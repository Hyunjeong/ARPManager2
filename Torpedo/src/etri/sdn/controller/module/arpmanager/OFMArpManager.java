package etri.sdn.controller.module.arpmanager;

import java.net.InetAddress;
import java.net.NetworkInterface;
import java.net.SocketException;
import java.net.UnknownHostException;
import java.nio.ByteBuffer;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.projectfloodlight.openflow.protocol.OFFactories;
import org.projectfloodlight.openflow.protocol.OFFactory;
import org.projectfloodlight.openflow.protocol.OFFlowMod;
import org.projectfloodlight.openflow.protocol.OFFlowModCommand;
import org.projectfloodlight.openflow.protocol.OFFlowModFlags;
import org.projectfloodlight.openflow.protocol.OFMessage;
import org.projectfloodlight.openflow.protocol.OFPacketIn;
import org.projectfloodlight.openflow.protocol.OFPacketOut;
import org.projectfloodlight.openflow.protocol.OFType;
import org.projectfloodlight.openflow.protocol.action.OFAction;
import org.projectfloodlight.openflow.protocol.action.OFActionOutput;
import org.projectfloodlight.openflow.protocol.instruction.OFInstruction;
import org.projectfloodlight.openflow.protocol.instruction.OFInstructionApplyActions;
import org.projectfloodlight.openflow.protocol.match.Match;
import org.projectfloodlight.openflow.protocol.match.MatchField;
import org.projectfloodlight.openflow.types.EthType;
import org.projectfloodlight.openflow.types.MacAddress;
import org.projectfloodlight.openflow.types.OFBufferId;
import org.projectfloodlight.openflow.types.OFPort;
import org.projectfloodlight.openflow.types.OFVlanVidMatch;
import org.projectfloodlight.openflow.types.TableId;
import org.projectfloodlight.openflow.types.U64;
import org.projectfloodlight.openflow.types.VlanVid;
import org.projectfloodlight.openflow.util.HexString;

import etri.sdn.controller.IService;
import etri.sdn.controller.MessageContext;
import etri.sdn.controller.OFMFilter;
import etri.sdn.controller.OFModel;
import etri.sdn.controller.OFModule;
import etri.sdn.controller.module.devicemanager.IDevice;
import etri.sdn.controller.module.devicemanager.IDeviceService;
import etri.sdn.controller.module.devicemanager.SwitchPort;
import etri.sdn.controller.module.linkdiscovery.NodePortTuple;
import etri.sdn.controller.module.routing.IRoutingService;
import etri.sdn.controller.module.routing.Route;
import etri.sdn.controller.module.topologymanager.ITopologyService;
import etri.sdn.controller.protocol.OFProtocol;
import etri.sdn.controller.protocol.SwitchInfo;
import etri.sdn.controller.protocol.io.Connection;
import etri.sdn.controller.protocol.io.IOFSwitch;
import etri.sdn.controller.protocol.packet.ARP;
import etri.sdn.controller.protocol.packet.IPv4;
import etri.sdn.controller.util.AppCookie;
import etri.sdn.controller.util.Logger;

public class OFMArpManager extends OFModule {

	public static Map<String, Object> arptable = new HashMap<String, Object>();

	public static short FLOWMOD_DEFAULT_IDLE_TIMEOUT = 5; 	// in seconds
	public static short FLOWMOD_DEFAULT_HARD_TIMEOUT = 0; 	// infinite
	public static short FLOWMOD_DEFAULT_PRIORITY = 10;

	// flow-mod - for use in the cookie
	public static final int ARP_MANAGER_APP = 21; // TODO: This must be managed
	// by a global APP_ID class
	private long appCookie = AppCookie.makeCookie(ARP_MANAGER_APP, 0);

	private static final int LEARNING_SWITCH_APP_ID = 1;
	private static final int APP_ID_BITS = 12;
	private static final int APP_ID_SHIFT = (64 - APP_ID_BITS);
	private static final long LEARNING_SWITCH_COOKIE = (long) (LEARNING_SWITCH_APP_ID & ((1 << APP_ID_BITS) - 1)) << APP_ID_SHIFT;

	private static final short IDLE_TIMEOUT_DEFAULT = 5;
	private static final short HARD_TIMEOUT_DEFAULT = 0;
	private static final short PRIORITY_DEFAULT = 100;
	// normally, setup reverse flow as well. 
	private static final boolean LEARNING_SWITCH_REVERSE_FLOW = true;
	private static final int MAX_MACS_PER_SWITCH  = 1000; 
	
	IDeviceService deviceManager = null;
	ITopologyService topology = null;
	IRoutingService routingEngine = null;

	private byte[] bcontrollerMac = null;
	byte[] bopcode = new byte[]{0x00, 0x02};

	public Comparator<SwitchPort> clusterIdComparator = new Comparator<SwitchPort>() {
		@Override
		public int compare(SwitchPort d1, SwitchPort d2) {
			Long d1ClusterId = topology.getL2DomainId(d1.getSwitchDPID());
			Long d2ClusterId = topology.getL2DomainId(d2.getSwitchDPID());
			return d1ClusterId.compareTo(d2ClusterId);
		}
	};

	private OFProtocol protocol;

	private void addToARPTable(String IP, String MAC) {
		arptable.put(IP, MAC);
	}

	private String lookupARPTable(String destinationIP) {
		if (arptable.containsKey(destinationIP)) {
			String destMAC = (String) arptable.get(destinationIP);
			return destMAC;
		} else
			return "";
	}

	@Override
	protected Collection<Class<? extends IService>> services() {
		return Collections.emptyList();
	}

	@Override
	protected void initialize() {
		protocol = getController().getProtocol();
		deviceManager = (IDeviceService) OFModule.getModule(IDeviceService.class);
		topology = (ITopologyService) OFModule.getModule(ITopologyService.class);
		routingEngine = (IRoutingService) OFModule.getModule(IRoutingService.class);
		//		assert ( deviceManager != null );

		registerFilter(OFType.PACKET_IN, new OFMFilter() {

			@Override
			public boolean filter(OFMessage m) {
				OFPacketIn pi = (OFPacketIn) m;

				byte[] packet = pi.getData();
				if ( packet[12] == 0x08 && packet[13] == 0x06 ) {
					// ARP! (ethertype)
					return true;
				}
				return false;
			}
		});


		InetAddress addr = null;
		try {
			addr = InetAddress.getLocalHost();
		} catch (UnknownHostException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

		NetworkInterface ni = null;

		try {
			ni = NetworkInterface.getByInetAddress(addr);
		} catch (SocketException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}
		try {
			this.bcontrollerMac = ni.getHardwareAddress();
		} catch (SocketException e1) {
			// TODO Auto-generated catch block
			e1.printStackTrace();
		}

	}

	@Override
	protected boolean handleHandshakedEvent(Connection conn,
			MessageContext context) {
		// TODO Auto-generated method stub
		return true;
	}

	protected IDevice findDestinationDevice(long macAddress, short vlan, Integer ipv4Address){
		//		Set<Long> swids = this.getController().getSwitchIdentifiers();
		Collection<IOFSwitch> switches = this.getController().getSwitches();
		IDevice ret = null;
		//		IOFSwitch sw ;
		//		sw.
		//		boolean replied = false;

		for (IOFSwitch sw : switches) {
			for(OFPort port : sw.getPortBroadcastHits().keySet()) {
				ret = deviceManager.findDevice(macAddress, vlan, ipv4Address, sw.getId(), port);
			}
		}
		//			if ( ret != null ) {
		//				// ....
		//				
		//				
		//				// if correctly replied ARP
		//				replied = true;
		//				break;
		//			}
		//			else
		//			{
		//				System.out.println("Device Manager가 없어 말이 됨?");
		//			}
		//		}
		return ret;
		//		return ! replied;
	}
	public boolean isGratuitous(byte[] senderProtocolAddress, byte[] targetProtocolAddress) {        
		assert(senderProtocolAddress.length == targetProtocolAddress.length);

		int indx = 0;
		while (indx < senderProtocolAddress.length) {
			if (senderProtocolAddress[indx] != targetProtocolAddress[indx]) {
				return false;
			}
			indx++;
		}

		return true;
	}
	private void writePacketOutForPacketIn(IOFSwitch sw, 
			OFPacketIn packetInMessage, 
			OFPort egressPort,
			OFPort getInputPort,
			List<OFMessage> out) {
		
		OFFactory fac = OFFactories.getFactory(packetInMessage.getVersion());
		OFPacketOut.Builder po = fac.buildPacketOut();
		
		List<OFAction> actions = new LinkedList<OFAction>();
		OFActionOutput.Builder action_output = fac.actions().buildOutput();
		actions.add( action_output.setPort(egressPort).setMaxLen(0xffff).build());
		
		po
		.setBufferId(packetInMessage.getBufferId())
		.setInPort(getInputPort)
		.setActions(actions);
		
//		if ( po.getBufferId() == OFBufferId.NO_BUFFER ) {
			po.setData( packetInMessage.getData() );
//		}

		// TODO: counter store support
		//		counterStore.updatePktOutFMCounterStore(sw, packetOutMessage);
		out.add(po.build());
	}
	private void writeFlowMod(IOFSwitch sw, OFFlowModCommand command, OFBufferId ofBufferId,
			Match match, OFPort outPort, List<OFMessage> out) {
		
		OFFactory fac = OFFactories.getFactory(sw.getVersion());

		OFFlowMod.Builder fm = null;
		switch ( command ){
		case ADD:
			fm = fac.buildFlowAdd();
			break;
		case DELETE:
			fm = fac.buildFlowDelete();
			break;
		case MODIFY:
			fm = fac.buildFlowModify();
			break;
		case DELETE_STRICT:
			fm = fac.buildFlowDeleteStrict();
			break;
		case MODIFY_STRICT:
			fm = fac.buildFlowModifyStrict();
			break;
		}
		
		List<OFAction> actions = new LinkedList<OFAction>();
		OFActionOutput.Builder action = fac.actions().buildOutput();
		action
		.setPort(outPort)
		.setMaxLen(0xffff);
		actions.add(action.build());
		
		try {
			fm
			.setCookie(U64.of(LEARNING_SWITCH_COOKIE))
			.setIdleTimeout(IDLE_TIMEOUT_DEFAULT)
			.setHardTimeout(HARD_TIMEOUT_DEFAULT)
			.setPriority(PRIORITY_DEFAULT)
			.setBufferId(ofBufferId)
			.setOutPort((command != OFFlowModCommand.DELETE)?outPort:OFPort.ANY /*for 1.0, this is NONE */)
			.setMatch(match)
			.setFlags((command != OFFlowModCommand.DELETE)?EnumSet.of(OFFlowModFlags.SEND_FLOW_REM):EnumSet.noneOf(OFFlowModFlags.class))
			.setActions(actions);
		} catch ( UnsupportedOperationException u ) {
			// probably from setActions() method
			List<OFInstruction> instructions = new LinkedList<OFInstruction>();
			OFInstructionApplyActions.Builder instruction = fac.instructions().buildApplyActions();
			instructions.add( instruction.setActions(actions).build() );
			
			fm
			.setInstructions( instructions )
			.setTableId(TableId.ZERO);
		}

		out.add(fm.build());
	}
	@Override
	protected boolean handleMessage(Connection conn, MessageContext context,
			OFMessage msg, List<OFMessage> outgoing) {
		// PACKET-IN for ARP has arrived.

		OFPacketIn pi = (OFPacketIn) msg;
		byte[] packetData = pi.getData();

		Match match = null;
		try { 
			match = pi.getMatch();
		} catch ( UnsupportedOperationException u ) {
			match = this.protocol.loadOFMatchFromPacket(conn.getSwitch(), pi.getData(), pi.getInPort(), true);
		}



		byte[] bsourceIP = Arrays.copyOfRange(packetData, 28, 32);
		byte[] bdestinationIP = Arrays.copyOfRange(packetData, 38, 42);
		byte[] bsourceMAC = Arrays.copyOfRange(packetData, 6, 12);
		byte[] bdestinationMAC = Arrays.copyOfRange(packetData, 0, 6);
		short opCode = ByteBuffer.wrap(packetData, 20, 2).getShort();

		String ssourceMAC = String.valueOf(HexString.toHexString(bsourceMAC));
		String sdestinationMAC = String.valueOf(HexString.toHexString(bdestinationMAC));

		String ssourceIP = IPv4.fromIPv4Address(IPv4.toIPv4Address(bsourceIP));
		String sdestinationIP = IPv4.fromIPv4Address(IPv4.toIPv4Address(bdestinationIP));

		if(!isGratuitous(bsourceIP, bdestinationIP)){
			addToARPTable(ssourceIP, ssourceMAC);
			//			System.out.println("add To table : " + ssourceIP + " " + ssourceMAC);
			if(opCode == ARP.OP_REQUEST) {
				String sfindedDestinationMAC = lookupARPTable(sdestinationIP);
				if(sfindedDestinationMAC != "" && sfindedDestinationMAC != null) {

					System.out.println("11111");
					//					System.out.println("findedDestinationMAC : " + sfindedDestinationMAC + " dIP : " + sdestinationIP + "\t");

					byte[] bfindedDestinationMAC = HexString.fromHexString(sfindedDestinationMAC);
					//
					//					ByteBuffer buffer = ByteBuffer.allocate(2);
					//					buffer.putShort(ARP.OP_REPLY);
					//					buffer.flip();
					//					byte[] opCodeForReply = buffer.array();
					//

					// arp reply 만들고
					System.arraycopy(bsourceMAC, 0, packetData, 0, bsourceMAC.length);
					System.arraycopy(bsourceMAC, 0, packetData, 32, bsourceMAC.length);
					System.arraycopy(bcontrollerMac, 0, packetData, 6, bcontrollerMac.length);
					System.arraycopy(bfindedDestinationMAC, 0, packetData, 22, bfindedDestinationMAC.length);
					System.arraycopy(bsourceIP, 0, packetData, 38, bsourceIP.length);
					System.arraycopy(bdestinationIP, 0, packetData, 28, bdestinationIP.length);
					System.arraycopy(bopcode, 0, packetData, 20, bopcode.length);

					
					OFPort inputPort = match.get(MatchField.IN_PORT);
					MacAddress sourceMac = match.get(MatchField.ETH_SRC);
					MacAddress destMac = match.get(MatchField.ETH_DST);
					EthType etherType = match.get(MatchField.ETH_TYPE);
					OFVlanVidMatch vm = match.get(MatchField.VLAN_VID);
					VlanVid vlan = (vm != null)?vm.getVlanVid():null;

					Match.Builder target = match.createBuilder();
					if ( inputPort != null ) {
						target.setExact(MatchField.IN_PORT, inputPort);
					}
					if ( etherType != null ) {
						target.setExact(MatchField.ETH_TYPE, etherType);
					}
					if ( vlan != null ) {
						target.setExact(MatchField.VLAN_VID, vm);
					}
					if ( sourceMac != null ) {
						target.setExact(MatchField.ETH_SRC, MacAddress.of(bfindedDestinationMAC));
					}
					if ( destMac != null ) {
						target.setExact(MatchField.ETH_DST, sourceMac);
					}

					match = target.build();
					
					// flow rule울 switch에 보내고
					OFPort outPort = inputPort;

					if (outPort == null) {
						// If we haven't learned the port for the dest MAC/VLAN, flood it
						// Don't flood broadcast packets if the broadcast is disabled.
						// XXX For LearningSwitch this doesn't do much. The sourceMac is removed
						//     from port map whenever a flow expires, so you would still see
						//     a lot of floods.
						this.writePacketOutForPacketIn(conn.getSwitch(), pi, OFPort.FLOOD, inputPort, outgoing);
					} else {
						// Add flow table entry matching source MAC, dest MAC, VLAN and input port
						// that sends to the port we previously learned for the dest MAC/VLAN.  Also
						// add a flow table entry with source and destination MACs reversed, and
						// input and output ports reversed.  When either entry expires due to idle
						// timeout, remove the other one.  This ensures that if a device moves to
						// a different port, a constant stream of packets headed to the device at
						// its former location does not keep the stale entry alive forever.
						// FIXME: current HP switches ignore DL_SRC and DL_DST fields, so we have to match on
						// NW_SRC and NW_DST as well
						
						this.writePacketOutForPacketIn(conn.getSwitch(), pi, outPort, inputPort, outgoing);

						// setting buffer id and do not write packet out cause some 
						// initial ping messages dropped for OF1.3 switches.
						this.writeFlowMod(conn.getSwitch(), OFFlowModCommand.ADD, 
								OFBufferId.NO_BUFFER/*pi.getBufferId()*/, match, outPort, outgoing);

					}
					return false;

				}
				else
				{
					//					System.out.println("===flooding===");
					doFlood(conn.getSwitch(), pi, context);
					return false;
				}
			}
			// ARP reply packet
			else {
//				long ldestinationMacOfReply = HexString.toLong(sdestinationMAC);
//				IDevice destinationDeviceOfReply = null;
//				try{
//					destinationDeviceOfReply = findDestinationDevice(ldestinationMacOfReply, vlan.getVlan(), IPv4.toIPv4Address(bsourceIP));
//				}catch(NullPointerException ex)
//				{
//					System.out.println(ldestinationMacOfReply + " / " + vlan.getVlan() + " / " + bsourceIP);
//				}
//				if(destinationDeviceOfReply == null){
//					doFlood(conn.getSwitch(), pi, context);
//					return false;
//				}
//				else{
//					SwitchPort[] destinationSwPortOfReply = destinationDeviceOfReply.getAttachmentPoints();
//					Short outPort = destinationSwPortOfReply[0].getPort().getShortPortNumber();
//					destinationSwPortOfReply[0].getSwitchDPID();
//					
//				}
			}
		}
		// GARP
		else{


		}
		return true;
	}

	protected OFPort getInputPort(OFPacketIn pi) {
		if ( pi == null ) {
			throw new AssertionError("pi cannot refer null");
		}
		try {
			return pi.getInPort();
		} catch ( UnsupportedOperationException e ) {
			try {
				return pi.getMatch().get(MatchField.IN_PORT);
			} catch ( NullPointerException nx ) {
				Logger.debug("Packet-in does not have oxm object for OFB_IN_PORT");
				throw new AssertionError("pi cannot refer null");
			}
		}
	}

	/**
	 * Creates a OFPacketOut with packetin that is flooded on all ports
	 * unless the port is blocked, in which case the packet will be dropped.
	 * 
	 * @param sw the switch that receives packetin
	 * @param pi packetin
	 * @param cntx the {@link MessageContext}
	 */
	protected void doFlood(IOFSwitch sw, OFPacketIn pi, MessageContext cntx) {
		OFPort inPort = getInputPort(pi);

		if (! topology.isIncomingBroadcastAllowed(sw.getId(), inPort) ) {
			return;
		}

		OFFactory fac = OFFactories.getFactory(pi.getVersion());

		// Set Action to flood
		OFPacketOut.Builder po = fac.buildPacketOut();

		po
		.setBufferId(pi.getBufferId())
		.setInPort(inPort);

		List<OFAction> actions = new ArrayList<OFAction>();
		OFActionOutput.Builder action_output = fac.actions().buildOutput();

		if (sw.hasAttribute(IOFSwitch.PROP_SUPPORTS_OFPP_FLOOD)) {
			action_output.setPort(OFPort.FLOOD);
		} else {
			action_output.setPort(OFPort.ALL);
		}
		action_output.setMaxLen((short)0xffff);

		actions.add(action_output.build());
		po.setActions(actions);

		// set buffer-id, in-port and packet-data based on packet-in
		if (pi.getBufferId() == OFBufferId.NO_BUFFER ) {
			po.setData( pi.getData() );
		}

		sw.getConnection().write(po.build());            

		return;
	}

	/**
	 * Pushes a packet-out to a switch. The assumption here is that the packet-in 
	 * was also generated from the same switch. Thus, if the input port of the
	 * packet-in and the outport are the same, the function will not push the packet-out.
	 * 
	 * @param conn the connection to the switch that generated the packet-in, and from which packet-out is sent
	 * @param match the {@link OFMatch}
	 * @param pi packetin
	 * @param outPort the output port
	 * @param cntx the {@link MessageContext}
	 */
	protected void pushPacket(Connection conn, Match match, OFPacketIn pi, 
			OFPort outPort, MessageContext cntx) {

		if (pi == null) {
			return;
		}
		OFPort inPort = getInputPort(pi);

		if ( outPort.equals(inPort) ){
			Logger.stdout("Packet out not sent as the outport matches inport. " + pi.toString());
			return;
		}

		// The assumption here is (sw) is the switch that generated the packet-in. 
		// If the input port is the same as output port, then the packet-out should be ignored.
		if ( inPort.equals(outPort) ) {
			return;
		}

		OFFactory fac = OFFactories.getFactory(pi.getVersion());

		// set actions
		OFActionOutput.Builder action_output = fac.actions().buildOutput();
		List<OFAction> actions = new ArrayList<OFAction>();

		action_output.setMaxLen((short)0xffff);
		action_output.setPort(outPort);
		actions.add(action_output.build());

		OFPacketOut.Builder po = fac.buildPacketOut().setActions(actions);

		// If the switch doens't support buffering set the buffer id to be none
		// otherwise it'll be the the buffer id of the PacketIn
		if ( protocol.getSwitchInformation(conn.getSwitch()).getBuffers() == 0 ) {
			po
			.setBufferId( OFBufferId.NO_BUFFER )
			.setData( pi.getData() );
		} else {
			po.setBufferId(pi.getBufferId());
		}

		po.setInPort(inPort);

		conn.write(po.build());
	}


	/**
	 * Pushes routes from back to front.
	 * 
	 * @param conn the connection to switch
	 * @param route a route to push
	 * @param match openFlow fields to match on
	 * @param pi packetin
	 * @param pinSwitch the switch of packetin
	 * @param cookie the cookie to set in each flow_mod
	 * @param cntx the {@link MessageContext}
	 * @param reqeustFlowRemovedNotifn true when the switch would send a flow mod 
	 *        removal notification when the flow mod expires
	 * @param doFlush true when the flow mod would be immediately written to the switch
	 * @param flowModCommand flow mod. command to use, e.g. OFFlowMod.OFPFC_ADD,
	 *        OFFlowMod.OFPFC_MODIFY etc.
	 * 
	 * @return true if the source switch is included in this route
	 */
	@SuppressWarnings("unchecked")
	public boolean pushRoute(
			Connection conn,
			Route route, 
			Match match, 
			OFPacketIn pi,
			long pinSwitch,
			long cookie, 
			MessageContext cntx,
			boolean reqeustFlowRemovedNotifn,
			boolean doFlush,
			OFFlowModCommand   flowModCommand) {

		boolean srcSwitchIncluded = false;

		OFFactory fac = OFFactories.getFactory(pi.getVersion());

		OFFlowMod.Builder fm = null;
		switch ( flowModCommand ){
		case ADD:
			fm = fac.buildFlowAdd();
			break;
		case DELETE:
			fm = fac.buildFlowDelete();
			break;
		case MODIFY:
			fm = fac.buildFlowModify();
			break;
		case DELETE_STRICT:
			fm = fac.buildFlowDeleteStrict();
			break;
		case MODIFY_STRICT:
			fm = fac.buildFlowModifyStrict();
			break;
		}

		fm.setIdleTimeout(FLOWMOD_DEFAULT_IDLE_TIMEOUT)
		.setHardTimeout(FLOWMOD_DEFAULT_HARD_TIMEOUT)
		//		.setBufferId(OFBufferId.NO_BUFFER)
		.setBufferId(pi.getBufferId())
		.setCookie(U64.of(cookie))
		.setMatch(match)
		.setPriority(FLOWMOD_DEFAULT_PRIORITY)
		.setFlags( EnumSet.noneOf(OFFlowModFlags.class) );

		try { 
			fm
			.setTableId(TableId.ZERO)
			.setCookieMask(U64.of(0xffffffffffffffffL));
		} catch ( UnsupportedOperationException u ) {
			// does nothing
		}

		List<NodePortTuple> switchPortList = route.getPath();

		for (int indx = switchPortList.size()-1; fm != null && indx > 0; indx -= 2) {

			// indx and indx-1 will always have the same switch dpid.
			long switchDPID = switchPortList.get(indx).getNodeId();
			IOFSwitch sw = controller.getSwitch(switchDPID);
			if (sw == null) {
				//				if (log.isWarnEnabled()) {
				//					log.warn("Unable to push route, switch at dpid {} " +
				//							"not available", switchDPID);
				//				}
				return srcSwitchIncluded;
			}

			// set buffer id if it is the source switch
			if (1 == indx) {
				// Set the flag to request flow-mod removal notifications only for the
				// source switch. The removal message is used to maintain the flow cache.
				// Don't set the flag for ARP messages - TODO generalize check
				if ( match.get(MatchField.ETH_TYPE) != EthType.ARP ) {
					fm.setFlags(EnumSet.of(OFFlowModFlags.SEND_FLOW_REM));
				}
			}

			OFPort outPort = switchPortList.get(indx).getPortId();
			OFPort inPort = switchPortList.get(indx-1).getPortId();

			Match.Builder fm_match = match.createBuilder();

			// copy construct the original match object.
			for ( @SuppressWarnings("rawtypes") MatchField mf : match.getMatchFields() ) {
				if ( match.isExact(mf) ) {
					fm_match.setExact(mf, match.get(mf));
				} else {
					fm_match.setMasked(mf, match.get(mf), match.getMasked(mf));
				}
			}

			fm_match.setExact(MatchField.IN_PORT, inPort);

			List<OFAction> actions = new ArrayList<OFAction>();
			OFActionOutput.Builder action_output = fac.actions().buildOutput(); 
			action_output.setMaxLen((short)0xffff).setPort(outPort);
			actions.add(action_output.build());

			try {	
				fm.setActions( actions );
			} catch ( UnsupportedOperationException u ) {
				List<OFInstruction> instructions = new ArrayList<OFInstruction>();
				OFInstructionApplyActions.Builder instruction = fac.instructions().buildApplyActions();
				instruction.setActions(actions);
				instructions.add(instruction.build());

				fm.setInstructions( instructions );
			}

			fm.setMatch(fm_match.build());

			fm.setBufferId(OFBufferId.NO_BUFFER); //?

					// write flow-mod object to switch.
			sw.getConnection().write(fm.build());

			// Push the packet out the source switch
			if (sw.getId() == pinSwitch) {
				// TODO: Instead of doing a packetOut here we could also 
				// send a flowMod with bufferId set.... 
				pushPacket(conn, match, pi, outPort, cntx);
				srcSwitchIncluded = true;
			}
		}

		return srcSwitchIncluded;
	}

	protected void doForwardFlow(IOFSwitch sw, OFPacketIn pi, 
			MessageContext cntx,
			boolean requestFlowRemovedNotifn) {    

		OFPort inPort = getInputPort(pi);

		Match match = protocol.loadOFMatchFromPacket(sw, pi.getData(), inPort, false);

		// Check if we have the location of the destination
		IDevice dstDevice = (IDevice) cntx.get(MessageContext.DST_DEVICE);

		if (dstDevice != null) {
			IDevice srcDevice = (IDevice) cntx.get(MessageContext.SRC_DEVICE);
			Long srcIsland = topology.getL2DomainId(sw.getId());

			if (srcDevice == null) {
				Logger.stderr("No device entry found for source device");
				return;
			}
			if (srcIsland == null) {
				Logger.stderr("No openflow island found for source {" + sw.getStringId() + "}/{" + inPort + "}");
				return;
			}

			// Validate that we have a destination known on the same island
			// Validate that the source and destination are not on the same switchport
			boolean on_same_island = false;
			boolean on_same_if = false;
			for (SwitchPort dstDap : dstDevice.getAttachmentPoints()) {
				long dstSwDpid = dstDap.getSwitchDPID();
				Long dstIsland = topology.getL2DomainId(dstSwDpid);
				if ((dstIsland != null) && dstIsland.equals(srcIsland)) {
					on_same_island = true;
					if ((sw.getId() == dstSwDpid) && (inPort == dstDap.getPort())) {
						on_same_if = true;
					}
					break;
				}
			}

			if (!on_same_island) {
				Logger.stdout("No first hop island found for destination device " + dstDevice + ", Action = flooding");
				// Flood since we don't know the dst device
				doFlood(sw, pi, cntx);
				return;
			}            

			if (on_same_if) {
				Logger.stdout("Both source and destination are on the same switch/port " + 
						sw.toString() + "/" + inPort + ", Action = NOP");
				return;
			}

			// Install all the routes where both src and dst have attachment points.
			// Since the lists are stored in sorted order we can traverse the attachment
			// points in O(m+n) time.
			SwitchPort[] srcDaps = srcDevice.getAttachmentPoints();
			Arrays.sort(srcDaps, clusterIdComparator);
			SwitchPort[] dstDaps = dstDevice.getAttachmentPoints();
			Arrays.sort(dstDaps, clusterIdComparator);

			int iSrcDaps = 0, iDstDaps = 0;

			while ((iSrcDaps < srcDaps.length) && (iDstDaps < dstDaps.length)) {
				SwitchPort srcDap = srcDaps[iSrcDaps];
				SwitchPort dstDap = dstDaps[iDstDaps];
				Long srcCluster = 
						topology.getL2DomainId(srcDap.getSwitchDPID());
				Long dstCluster = 
						topology.getL2DomainId(dstDap.getSwitchDPID());

				int srcVsDest = srcCluster.compareTo(dstCluster);
				if (srcVsDest == 0) {
					if (!srcDap.equals(dstDap) && 
							/* (srcCluster != null) && */		// --redundant null check.
							(dstCluster != null)) {
						Route route = 
								routingEngine.getRoute(srcDap.getSwitchDPID(),
										srcDap.getPort(),
										dstDap.getSwitchDPID(),
										dstDap.getPort());
						if (route != null) {
							//							if (log.isTraceEnabled()) {
							//								log.trace("pushRoute match={} route={} " + 
							//										"destination={}:{}",
							//										new Object[] {match, route, 
							//										dstDap.getSwitchDPID(),
							//										dstDap.getPort()});
							//							}

							pushRoute(sw.getConnection(), route, match, pi, sw.getId(), appCookie, 
									cntx, requestFlowRemovedNotifn, false,
									OFFlowModCommand.ADD);
						}
					}
					iSrcDaps++;
					iDstDaps++;
				} else if (srcVsDest < 0) {
					iSrcDaps++;
				} else {
					iDstDaps++;
				}
			}
		} else {
			// Flood since we don't know the dst device
			doFlood(sw, pi, cntx);
		}
	}

	@Override
	protected boolean handleDisconnect(Connection conn) {
		// TODO Auto-generated method stub
		return true;
	}

	@Override
	public OFModel[] getModels() {
		// TODO Auto-generated method stub
		return null;
	}

}
