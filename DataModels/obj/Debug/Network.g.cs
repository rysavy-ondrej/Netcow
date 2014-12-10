namespace DataModels
{
   using System;
   using System.Collections.Generic;
   using System.Diagnostics.Contracts;
   using System.Numerics;
   using System.Threading;
   using System.Threading.Tasks;
   using Microsoft.Formula.API;
   using Microsoft.Formula.API.Nodes;
   using Microsoft.Formula.API.Generators;
   using Microsoft.Formula.Common;
   using Microsoft.Formula.Common.Terms;

   public static partial class Network_Root
   {
      private static readonly Dictionary<string, Func<ICSharpTerm[], ICSharpTerm>> ConstructorMap = new Dictionary<string, Func<ICSharpTerm[], ICSharpTerm>>();
      static Network_Root()
      {
         ConstructorMap.Add("#AccessList", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList));
         ConstructorMap.Add("#AccessList[0]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_0));
         ConstructorMap.Add("#AccessList[1]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_1));
         ConstructorMap.Add("#AccessList[2]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_2));
         ConstructorMap.Add("#AccessList[3]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_3));
         ConstructorMap.Add("#AccessList[4]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_4));
         ConstructorMap.Add("#AccessList[5]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_5));
         ConstructorMap.Add("#AccessList[6]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_6));
         ConstructorMap.Add("#AccessList[7]", args => MkUserCnst(Network_Root.TypeCnstKind.AccessList_NDEX_7));
         ConstructorMap.Add("#AclAction", args => MkUserCnst(Network_Root.TypeCnstKind.AclAction));
         ConstructorMap.Add("#AclOptions", args => MkUserCnst(Network_Root.TypeCnstKind.AclOptions));
         ConstructorMap.Add("#AclProtocol", args => MkUserCnst(Network_Root.TypeCnstKind.AclProtocol));
         ConstructorMap.Add("#Boolean", args => MkUserCnst(Network_Root.TypeCnstKind.Boolean));
         ConstructorMap.Add("#Device", args => MkUserCnst(Network_Root.TypeCnstKind.Device));
         ConstructorMap.Add("#FlowDirection", args => MkUserCnst(Network_Root.TypeCnstKind.FlowDirection));
         ConstructorMap.Add("#FrameRelayPort", args => MkUserCnst(Network_Root.TypeCnstKind.FrameRelayPort));
         ConstructorMap.Add("#FrameRelayPort[0]", args => MkUserCnst(Network_Root.TypeCnstKind.FrameRelayPort_NDEX_0));
         ConstructorMap.Add("#FrameRelayPort[1]", args => MkUserCnst(Network_Root.TypeCnstKind.FrameRelayPort_NDEX_1));
         ConstructorMap.Add("#FrameRelaySwitch", args => MkUserCnst(Network_Root.TypeCnstKind.FrameRelaySwitch));
         ConstructorMap.Add("#FrameRelaySwitch[0]", args => MkUserCnst(Network_Root.TypeCnstKind.FrameRelaySwitch_NDEX_0));
         ConstructorMap.Add("#ID", args => MkUserCnst(Network_Root.TypeCnstKind.ID));
         ConstructorMap.Add("#IP", args => MkUserCnst(Network_Root.TypeCnstKind.IP));
         ConstructorMap.Add("#IP[0]", args => MkUserCnst(Network_Root.TypeCnstKind.IP_NDEX_0));
         ConstructorMap.Add("#IcmpOptions", args => MkUserCnst(Network_Root.TypeCnstKind.IcmpOptions));
         ConstructorMap.Add("#IgmpOptions", args => MkUserCnst(Network_Root.TypeCnstKind.IgmpOptions));
         ConstructorMap.Add("#IgmpOptions[0]", args => MkUserCnst(Network_Root.TypeCnstKind.IgmpOptions_NDEX_0));
         ConstructorMap.Add("#Integer", args => MkUserCnst(Network_Root.TypeCnstKind.Integer));
         ConstructorMap.Add("#Interface", args => MkUserCnst(Network_Root.TypeCnstKind.Interface));
         ConstructorMap.Add("#InterfaceIpAccessGroup", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAccessGroup));
         ConstructorMap.Add("#InterfaceIpAccessGroup[0]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAccessGroup_NDEX_0));
         ConstructorMap.Add("#InterfaceIpAccessGroup[1]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAccessGroup_NDEX_1));
         ConstructorMap.Add("#InterfaceIpAccessGroup[2]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAccessGroup_NDEX_2));
         ConstructorMap.Add("#InterfaceIpAddress", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAddress));
         ConstructorMap.Add("#InterfaceIpAddress[0]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAddress_NDEX_0));
         ConstructorMap.Add("#InterfaceIpAddress[1]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAddress_NDEX_1));
         ConstructorMap.Add("#InterfaceIpAddress[2]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpAddress_NDEX_2));
         ConstructorMap.Add("#InterfaceIpNat", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpNat));
         ConstructorMap.Add("#InterfaceIpNat[0]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpNat_NDEX_0));
         ConstructorMap.Add("#InterfaceIpNat[1]", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceIpNat_NDEX_1));
         ConstructorMap.Add("#InterfaceStatus", args => MkUserCnst(Network_Root.TypeCnstKind.InterfaceStatus));
         ConstructorMap.Add("#Interface[0]", args => MkUserCnst(Network_Root.TypeCnstKind.Interface_NDEX_0));
         ConstructorMap.Add("#Interface[1]", args => MkUserCnst(Network_Root.TypeCnstKind.Interface_NDEX_1));
         ConstructorMap.Add("#IpAccessList", args => MkUserCnst(Network_Root.TypeCnstKind.IpAccessList));
         ConstructorMap.Add("#IpAccessList[0]", args => MkUserCnst(Network_Root.TypeCnstKind.IpAccessList_NDEX_0));
         ConstructorMap.Add("#IpNatDynamic", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatDynamic));
         ConstructorMap.Add("#IpNatDynamic[0]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatDynamic_NDEX_0));
         ConstructorMap.Add("#IpNatDynamic[1]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatDynamic_NDEX_1));
         ConstructorMap.Add("#IpNatDynamic[2]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatDynamic_NDEX_2));
         ConstructorMap.Add("#IpNatDynamic[3]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatDynamic_NDEX_3));
         ConstructorMap.Add("#IpNatPool", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatPool));
         ConstructorMap.Add("#IpNatPool[0]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatPool_NDEX_0));
         ConstructorMap.Add("#IpNatPool[1]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatPool_NDEX_1));
         ConstructorMap.Add("#IpNatPool[2]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatPool_NDEX_2));
         ConstructorMap.Add("#IpNatPool[3]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatPool_NDEX_3));
         ConstructorMap.Add("#IpNatStatic", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatStatic));
         ConstructorMap.Add("#IpNatStatic[0]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatStatic_NDEX_0));
         ConstructorMap.Add("#IpNatStatic[1]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatStatic_NDEX_1));
         ConstructorMap.Add("#IpNatStatic[2]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatStatic_NDEX_2));
         ConstructorMap.Add("#IpNatStatic[3]", args => MkUserCnst(Network_Root.TypeCnstKind.IpNatStatic_NDEX_3));
         ConstructorMap.Add("#IpRoute", args => MkUserCnst(Network_Root.TypeCnstKind.IpRoute));
         ConstructorMap.Add("#IpRoute[0]", args => MkUserCnst(Network_Root.TypeCnstKind.IpRoute_NDEX_0));
         ConstructorMap.Add("#IpRoute[1]", args => MkUserCnst(Network_Root.TypeCnstKind.IpRoute_NDEX_1));
         ConstructorMap.Add("#IpRoute[2]", args => MkUserCnst(Network_Root.TypeCnstKind.IpRoute_NDEX_2));
         ConstructorMap.Add("#IpRoute[3]", args => MkUserCnst(Network_Root.TypeCnstKind.IpRoute_NDEX_3));
         ConstructorMap.Add("#Link", args => MkUserCnst(Network_Root.TypeCnstKind.Link));
         ConstructorMap.Add("#Link[0]", args => MkUserCnst(Network_Root.TypeCnstKind.Link_NDEX_0));
         ConstructorMap.Add("#Link[1]", args => MkUserCnst(Network_Root.TypeCnstKind.Link_NDEX_1));
         ConstructorMap.Add("#NatDirection", args => MkUserCnst(Network_Root.TypeCnstKind.NatDirection));
         ConstructorMap.Add("#NatOrigin", args => MkUserCnst(Network_Root.TypeCnstKind.NatOrigin));
         ConstructorMap.Add("#Natural", args => MkUserCnst(Network_Root.TypeCnstKind.Natural));
         ConstructorMap.Add("#NegInteger", args => MkUserCnst(Network_Root.TypeCnstKind.NegInteger));
         ConstructorMap.Add("#PN", args => MkUserCnst(Network_Root.TypeCnstKind.PN));
         ConstructorMap.Add("#PN[0]", args => MkUserCnst(Network_Root.TypeCnstKind.PN_NDEX_0));
         ConstructorMap.Add("#Port", args => MkUserCnst(Network_Root.TypeCnstKind.Port));
         ConstructorMap.Add("#PortList", args => MkUserCnst(Network_Root.TypeCnstKind.PortList));
         ConstructorMap.Add("#PortList[0]", args => MkUserCnst(Network_Root.TypeCnstKind.PortList_NDEX_0));
         ConstructorMap.Add("#PortList[1]", args => MkUserCnst(Network_Root.TypeCnstKind.PortList_NDEX_1));
         ConstructorMap.Add("#PosInteger", args => MkUserCnst(Network_Root.TypeCnstKind.PosInteger));
         ConstructorMap.Add("#Real", args => MkUserCnst(Network_Root.TypeCnstKind.Real));
         ConstructorMap.Add("#Router", args => MkUserCnst(Network_Root.TypeCnstKind.Router));
         ConstructorMap.Add("#RouterBgp", args => MkUserCnst(Network_Root.TypeCnstKind.RouterBgp));
         ConstructorMap.Add("#RouterBgp[0]", args => MkUserCnst(Network_Root.TypeCnstKind.RouterBgp_NDEX_0));
         ConstructorMap.Add("#RouterEigrp", args => MkUserCnst(Network_Root.TypeCnstKind.RouterEigrp));
         ConstructorMap.Add("#RouterEigrp[0]", args => MkUserCnst(Network_Root.TypeCnstKind.RouterEigrp_NDEX_0));
         ConstructorMap.Add("#RouterOsfp", args => MkUserCnst(Network_Root.TypeCnstKind.RouterOsfp));
         ConstructorMap.Add("#RouterOsfp[0]", args => MkUserCnst(Network_Root.TypeCnstKind.RouterOsfp_NDEX_0));
         ConstructorMap.Add("#RouterPort", args => MkUserCnst(Network_Root.TypeCnstKind.RouterPort));
         ConstructorMap.Add("#RouterPort[0]", args => MkUserCnst(Network_Root.TypeCnstKind.RouterPort_NDEX_0));
         ConstructorMap.Add("#RouterPort[1]", args => MkUserCnst(Network_Root.TypeCnstKind.RouterPort_NDEX_1));
         ConstructorMap.Add("#RouterRip", args => MkUserCnst(Network_Root.TypeCnstKind.RouterRip));
         ConstructorMap.Add("#RouterRip[0]", args => MkUserCnst(Network_Root.TypeCnstKind.RouterRip_NDEX_0));
         ConstructorMap.Add("#Router[0]", args => MkUserCnst(Network_Root.TypeCnstKind.Router_NDEX_0));
         ConstructorMap.Add("#String", args => MkUserCnst(Network_Root.TypeCnstKind.String));
         ConstructorMap.Add("#Switch", args => MkUserCnst(Network_Root.TypeCnstKind.Switch));
         ConstructorMap.Add("#SwitchInterface", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchInterface));
         ConstructorMap.Add("#SwitchInterface[0]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchInterface_NDEX_0));
         ConstructorMap.Add("#SwitchInterface[1]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchInterface_NDEX_1));
         ConstructorMap.Add("#SwitchPort", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPort));
         ConstructorMap.Add("#SwitchPortAccess", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortAccess));
         ConstructorMap.Add("#SwitchPortAccess[0]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortAccess_NDEX_0));
         ConstructorMap.Add("#SwitchPortMode", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortMode));
         ConstructorMap.Add("#SwitchPortMode[0]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortMode_NDEX_0));
         ConstructorMap.Add("#SwitchPortMode[1]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortMode_NDEX_1));
         ConstructorMap.Add("#SwitchPortTrunk", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortTrunk));
         ConstructorMap.Add("#SwitchPortTrunk[0]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortTrunk_NDEX_0));
         ConstructorMap.Add("#SwitchPortTrunk[1]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPortTrunk_NDEX_1));
         ConstructorMap.Add("#SwitchPort[0]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPort_NDEX_0));
         ConstructorMap.Add("#SwitchPort[1]", args => MkUserCnst(Network_Root.TypeCnstKind.SwitchPort_NDEX_1));
         ConstructorMap.Add("#Switch[0]", args => MkUserCnst(Network_Root.TypeCnstKind.Switch_NDEX_0));
         ConstructorMap.Add("#TcpOptions", args => MkUserCnst(Network_Root.TypeCnstKind.TcpOptions));
         ConstructorMap.Add("#TrunkEncapsulation", args => MkUserCnst(Network_Root.TypeCnstKind.TrunkEncapsulation));
         ConstructorMap.Add("#UI16", args => MkUserCnst(Network_Root.TypeCnstKind.UI16));
         ConstructorMap.Add("#UI16Range", args => MkUserCnst(Network_Root.TypeCnstKind.UI16Range));
         ConstructorMap.Add("#UI16Range[0]", args => MkUserCnst(Network_Root.TypeCnstKind.UI16Range_NDEX_0));
         ConstructorMap.Add("#UI16Range[1]", args => MkUserCnst(Network_Root.TypeCnstKind.UI16Range_NDEX_1));
         ConstructorMap.Add("#UI32", args => MkUserCnst(Network_Root.TypeCnstKind.UI32));
         ConstructorMap.Add("#UI32Range", args => MkUserCnst(Network_Root.TypeCnstKind.UI32Range));
         ConstructorMap.Add("#UI32Range[0]", args => MkUserCnst(Network_Root.TypeCnstKind.UI32Range_NDEX_0));
         ConstructorMap.Add("#UI32Range[1]", args => MkUserCnst(Network_Root.TypeCnstKind.UI32Range_NDEX_1));
         ConstructorMap.Add("#UI8", args => MkUserCnst(Network_Root.TypeCnstKind.UI8));
         ConstructorMap.Add("#device", args => MkUserCnst(Network_Root.TypeCnstKind.device));
         ConstructorMap.Add("#device[0]", args => MkUserCnst(Network_Root.TypeCnstKind.device_NDEX_0));
         ConstructorMap.Add("#device[1]", args => MkUserCnst(Network_Root.TypeCnstKind.device_NDEX_1));
         ConstructorMap.Add("#edge", args => MkUserCnst(Network_Root.TypeCnstKind.edge));
         ConstructorMap.Add("#edge[0]", args => MkUserCnst(Network_Root.TypeCnstKind.edge_NDEX_0));
         ConstructorMap.Add("#edge[1]", args => MkUserCnst(Network_Root.TypeCnstKind.edge_NDEX_1));
         ConstructorMap.Add("#path", args => MkUserCnst(Network_Root.TypeCnstKind.path));
         ConstructorMap.Add("#path[0]", args => MkUserCnst(Network_Root.TypeCnstKind.path_NDEX_0));
         ConstructorMap.Add("#path[1]", args => MkUserCnst(Network_Root.TypeCnstKind.path_NDEX_1));
         ConstructorMap.Add("#sameLan", args => MkUserCnst(Network_Root.TypeCnstKind.sameLan));
         ConstructorMap.Add("#sameLan[0]", args => MkUserCnst(Network_Root.TypeCnstKind.sameLan_NDEX_0));
         ConstructorMap.Add("#sameLan[1]", args => MkUserCnst(Network_Root.TypeCnstKind.sameLan_NDEX_1));
         ConstructorMap.Add("AccessList", args => Network_Root.MkAccessList((Network_Root.IArgType_AccessList__0)args[0], (Network_Root.IArgType_AccessList__1)args[1], (Network_Root.IArgType_AccessList__2)args[2], (Network_Root.IArgType_AccessList__3)args[3], (Network_Root.IArgType_AccessList__4)args[4], (Network_Root.IArgType_AccessList__5)args[5], (Network_Root.IArgType_AccessList__6)args[6], (Network_Root.IArgType_AccessList__7)args[7]));
         ConstructorMap.Add("DENY", args => MkUserCnst(Network_Root.UserCnstKind.DENY));
         ConstructorMap.Add("DESTINATION", args => MkUserCnst(Network_Root.UserCnstKind.DESTINATION));
         ConstructorMap.Add("DOT1Q", args => MkUserCnst(Network_Root.UserCnstKind.DOT1Q));
         ConstructorMap.Add("DOWN", args => MkUserCnst(Network_Root.UserCnstKind.DOWN));
         ConstructorMap.Add("ECHO", args => MkUserCnst(Network_Root.UserCnstKind.ECHO));
         ConstructorMap.Add("ECHO_REPLY", args => MkUserCnst(Network_Root.UserCnstKind.ECHO_REPLY));
         ConstructorMap.Add("ESTABLISHED", args => MkUserCnst(Network_Root.UserCnstKind.ESTABLISHED));
         ConstructorMap.Add("FALSE", args => MkUserCnst(Network_Root.UserCnstKind.FALSE));
         ConstructorMap.Add("FrameRelayPort", args => Network_Root.MkFrameRelayPort((Network_Root.IArgType_FrameRelayPort__0)args[0], (Network_Root.IArgType_FrameRelayPort__1)args[1]));
         ConstructorMap.Add("FrameRelaySwitch", args => Network_Root.MkFrameRelaySwitch((Network_Root.IArgType_FrameRelaySwitch__0)args[0]));
         ConstructorMap.Add("ICMP", args => MkUserCnst(Network_Root.UserCnstKind.ICMP));
         ConstructorMap.Add("IGMP", args => MkUserCnst(Network_Root.UserCnstKind.IGMP));
         ConstructorMap.Add("IN", args => MkUserCnst(Network_Root.UserCnstKind.IN));
         ConstructorMap.Add("INSIDE", args => MkUserCnst(Network_Root.UserCnstKind.INSIDE));
         ConstructorMap.Add("IP", args => Network_Root.MkIP((Network_Root.IArgType_IP__0)args[0]));
         ConstructorMap.Add("IPV4", args => MkUserCnst(Network_Root.UserCnstKind.IPV4));
         ConstructorMap.Add("ISL", args => MkUserCnst(Network_Root.UserCnstKind.ISL));
         ConstructorMap.Add("IgmpOptions", args => Network_Root.MkIgmpOptions((Network_Root.IArgType_IgmpOptions__0)args[0]));
         ConstructorMap.Add("Interface", args => Network_Root.MkInterface((Network_Root.IArgType_Interface__0)args[0], (Network_Root.IArgType_Interface__1)args[1]));
         ConstructorMap.Add("InterfaceIpAccessGroup", args => Network_Root.MkInterfaceIpAccessGroup((Network_Root.IArgType_InterfaceIpAccessGroup__0)args[0], (Network_Root.IArgType_InterfaceIpAccessGroup__1)args[1], (Network_Root.IArgType_InterfaceIpAccessGroup__2)args[2]));
         ConstructorMap.Add("InterfaceIpAddress", args => Network_Root.MkInterfaceIpAddress((Network_Root.IArgType_InterfaceIpAddress__0)args[0], (Network_Root.IArgType_InterfaceIpAddress__1)args[1], (Network_Root.IArgType_InterfaceIpAddress__2)args[2]));
         ConstructorMap.Add("InterfaceIpNat", args => Network_Root.MkInterfaceIpNat((Network_Root.IArgType_InterfaceIpNat__0)args[0], (Network_Root.IArgType_InterfaceIpNat__1)args[1]));
         ConstructorMap.Add("IpAccessList", args => Network_Root.MkIpAccessList((Network_Root.IArgType_IpAccessList__0)args[0]));
         ConstructorMap.Add("IpNatDynamic", args => Network_Root.MkIpNatDynamic((Network_Root.IArgType_IpNatDynamic__0)args[0], (Network_Root.IArgType_IpNatDynamic__1)args[1], (Network_Root.IArgType_IpNatDynamic__2)args[2], (Network_Root.IArgType_IpNatDynamic__3)args[3]));
         ConstructorMap.Add("IpNatPool", args => Network_Root.MkIpNatPool((Network_Root.IArgType_IpNatPool__0)args[0], (Network_Root.IArgType_IpNatPool__1)args[1], (Network_Root.IArgType_IpNatPool__2)args[2], (Network_Root.IArgType_IpNatPool__3)args[3]));
         ConstructorMap.Add("IpNatStatic", args => Network_Root.MkIpNatStatic((Network_Root.IArgType_IpNatStatic__0)args[0], (Network_Root.IArgType_IpNatStatic__1)args[1], (Network_Root.IArgType_IpNatStatic__2)args[2], (Network_Root.IArgType_IpNatStatic__3)args[3]));
         ConstructorMap.Add("IpRoute", args => Network_Root.MkIpRoute((Network_Root.IArgType_IpRoute__0)args[0], (Network_Root.IArgType_IpRoute__1)args[1], (Network_Root.IArgType_IpRoute__2)args[2], (Network_Root.IArgType_IpRoute__3)args[3]));
         ConstructorMap.Add("Link", args => Network_Root.MkLink((Network_Root.IArgType_Link__0)args[0], (Network_Root.IArgType_Link__1)args[1]));
         ConstructorMap.Add("NIL", args => MkUserCnst(Network_Root.UserCnstKind.NIL));
         ConstructorMap.Add("OUT", args => MkUserCnst(Network_Root.UserCnstKind.OUT));
         ConstructorMap.Add("OUTSIDE", args => MkUserCnst(Network_Root.UserCnstKind.OUTSIDE));
         ConstructorMap.Add("PERMIT", args => MkUserCnst(Network_Root.UserCnstKind.PERMIT));
         ConstructorMap.Add("PN", args => Network_Root.MkPN((Network_Root.IArgType_PN__0)args[0]));
         ConstructorMap.Add("PortList", args => Network_Root.MkPortList((Network_Root.IArgType_PortList__0)args[0], (Network_Root.IArgType_PortList__1)args[1]));
         ConstructorMap.Add("Router", args => Network_Root.MkRouter((Network_Root.IArgType_Router__0)args[0]));
         ConstructorMap.Add("RouterBgp", args => Network_Root.MkRouterBgp((Network_Root.IArgType_RouterBgp__0)args[0]));
         ConstructorMap.Add("RouterEigrp", args => Network_Root.MkRouterEigrp((Network_Root.IArgType_RouterEigrp__0)args[0]));
         ConstructorMap.Add("RouterOsfp", args => Network_Root.MkRouterOsfp((Network_Root.IArgType_RouterOsfp__0)args[0]));
         ConstructorMap.Add("RouterPort", args => Network_Root.MkRouterPort((Network_Root.IArgType_RouterPort__0)args[0], (Network_Root.IArgType_RouterPort__1)args[1]));
         ConstructorMap.Add("RouterRip", args => Network_Root.MkRouterRip((Network_Root.IArgType_RouterRip__0)args[0]));
         ConstructorMap.Add("SOURCE", args => MkUserCnst(Network_Root.UserCnstKind.SOURCE));
         ConstructorMap.Add("Switch", args => Network_Root.MkSwitch((Network_Root.IArgType_Switch__0)args[0]));
         ConstructorMap.Add("SwitchInterface", args => Network_Root.MkSwitchInterface((Network_Root.IArgType_SwitchInterface__0)args[0], (Network_Root.IArgType_SwitchInterface__1)args[1]));
         ConstructorMap.Add("SwitchPort", args => Network_Root.MkSwitchPort((Network_Root.IArgType_SwitchPort__0)args[0], (Network_Root.IArgType_SwitchPort__1)args[1]));
         ConstructorMap.Add("SwitchPortAccess", args => Network_Root.MkSwitchPortAccess((Network_Root.IArgType_SwitchPortAccess__0)args[0]));
         ConstructorMap.Add("SwitchPortMode", args => Network_Root.MkSwitchPortMode((Network_Root.IArgType_SwitchPortMode__0)args[0], (Network_Root.IArgType_SwitchPortMode__1)args[1]));
         ConstructorMap.Add("SwitchPortTrunk", args => Network_Root.MkSwitchPortTrunk((Network_Root.IArgType_SwitchPortTrunk__0)args[0], (Network_Root.IArgType_SwitchPortTrunk__1)args[1]));
         ConstructorMap.Add("TCP", args => MkUserCnst(Network_Root.UserCnstKind.TCP));
         ConstructorMap.Add("TRUE", args => MkUserCnst(Network_Root.UserCnstKind.TRUE));
         ConstructorMap.Add("UDP", args => MkUserCnst(Network_Root.UserCnstKind.UDP));
         ConstructorMap.Add("UI16Range", args => Network_Root.MkUI16Range((Network_Root.IArgType_UI16Range__0)args[0], (Network_Root.IArgType_UI16Range__1)args[1]));
         ConstructorMap.Add("UI32Range", args => Network_Root.MkUI32Range((Network_Root.IArgType_UI32Range__0)args[0], (Network_Root.IArgType_UI32Range__1)args[1]));
         ConstructorMap.Add("UP", args => MkUserCnst(Network_Root.UserCnstKind.UP));
         ConstructorMap.Add("device", args => Network_Root.Mkdevice((Network_Root.IArgType_device__0)args[0], (Network_Root.IArgType_device__1)args[1]));
         ConstructorMap.Add("edge", args => Network_Root.Mkedge((Network_Root.IArgType_edge__0)args[0], (Network_Root.IArgType_edge__1)args[1]));
         ConstructorMap.Add("path", args => Network_Root.Mkpath((Network_Root.IArgType_path__0)args[0], (Network_Root.IArgType_path__1)args[1]));
         ConstructorMap.Add("sameLan", args => Network_Root.MksameLan((Network_Root.IArgType_sameLan__0)args[0], (Network_Root.IArgType_sameLan__1)args[1]));
         ConstructorMap.Add("~rel~AccessList", args => Network_Root.Mk_CG_rel_CG_AccessList((Network_Root.IArgType__CG_rel_CG_AccessList__0)args[0]));
         ConstructorMap.Add("~rel~FrameRelayPort", args => Network_Root.Mk_CG_rel_CG_FrameRelayPort((Network_Root.IArgType__CG_rel_CG_FrameRelayPort__0)args[0]));
         ConstructorMap.Add("~rel~FrameRelaySwitch", args => Network_Root.Mk_CG_rel_CG_FrameRelaySwitch((Network_Root.IArgType__CG_rel_CG_FrameRelaySwitch__0)args[0]));
         ConstructorMap.Add("~rel~IgmpOptions", args => Network_Root.Mk_CG_rel_CG_IgmpOptions((Network_Root.IArgType__CG_rel_CG_IgmpOptions__0)args[0]));
         ConstructorMap.Add("~rel~Interface", args => Network_Root.Mk_CG_rel_CG_Interface((Network_Root.IArgType__CG_rel_CG_Interface__0)args[0]));
         ConstructorMap.Add("~rel~InterfaceIpAccessGroup", args => Network_Root.Mk_CG_rel_CG_InterfaceIpAccessGroup((Network_Root.IArgType__CG_rel_CG_InterfaceIpAccessGroup__0)args[0]));
         ConstructorMap.Add("~rel~InterfaceIpAddress", args => Network_Root.Mk_CG_rel_CG_InterfaceIpAddress((Network_Root.IArgType__CG_rel_CG_InterfaceIpAddress__0)args[0]));
         ConstructorMap.Add("~rel~IpAccessList", args => Network_Root.Mk_CG_rel_CG_IpAccessList((Network_Root.IArgType__CG_rel_CG_IpAccessList__0)args[0]));
         ConstructorMap.Add("~rel~IpNatDynamic", args => Network_Root.Mk_CG_rel_CG_IpNatDynamic((Network_Root.IArgType__CG_rel_CG_IpNatDynamic__0)args[0]));
         ConstructorMap.Add("~rel~IpNatPool", args => Network_Root.Mk_CG_rel_CG_IpNatPool((Network_Root.IArgType__CG_rel_CG_IpNatPool__0)args[0]));
         ConstructorMap.Add("~rel~IpNatStatic", args => Network_Root.Mk_CG_rel_CG_IpNatStatic((Network_Root.IArgType__CG_rel_CG_IpNatStatic__0)args[0]));
         ConstructorMap.Add("~rel~IpRoute", args => Network_Root.Mk_CG_rel_CG_IpRoute((Network_Root.IArgType__CG_rel_CG_IpRoute__0)args[0]));
         ConstructorMap.Add("~rel~Link", args => Network_Root.Mk_CG_rel_CG_Link((Network_Root.IArgType__CG_rel_CG_Link__0)args[0]));
         ConstructorMap.Add("~rel~PortList", args => Network_Root.Mk_CG_rel_CG_PortList((Network_Root.IArgType__CG_rel_CG_PortList__0)args[0]));
         ConstructorMap.Add("~rel~Router", args => Network_Root.Mk_CG_rel_CG_Router((Network_Root.IArgType__CG_rel_CG_Router__0)args[0]));
         ConstructorMap.Add("~rel~RouterBgp", args => Network_Root.Mk_CG_rel_CG_RouterBgp((Network_Root.IArgType__CG_rel_CG_RouterBgp__0)args[0]));
         ConstructorMap.Add("~rel~RouterEigrp", args => Network_Root.Mk_CG_rel_CG_RouterEigrp((Network_Root.IArgType__CG_rel_CG_RouterEigrp__0)args[0]));
         ConstructorMap.Add("~rel~RouterOsfp", args => Network_Root.Mk_CG_rel_CG_RouterOsfp((Network_Root.IArgType__CG_rel_CG_RouterOsfp__0)args[0]));
         ConstructorMap.Add("~rel~RouterPort", args => Network_Root.Mk_CG_rel_CG_RouterPort((Network_Root.IArgType__CG_rel_CG_RouterPort__0)args[0]));
         ConstructorMap.Add("~rel~RouterRip", args => Network_Root.Mk_CG_rel_CG_RouterRip((Network_Root.IArgType__CG_rel_CG_RouterRip__0)args[0]));
         ConstructorMap.Add("~rel~Switch", args => Network_Root.Mk_CG_rel_CG_Switch((Network_Root.IArgType__CG_rel_CG_Switch__0)args[0]));
         ConstructorMap.Add("~rel~SwitchInterface", args => Network_Root.Mk_CG_rel_CG_SwitchInterface((Network_Root.IArgType__CG_rel_CG_SwitchInterface__0)args[0]));
         ConstructorMap.Add("~rel~SwitchPort", args => Network_Root.Mk_CG_rel_CG_SwitchPort((Network_Root.IArgType__CG_rel_CG_SwitchPort__0)args[0]));
         ConstructorMap.Add("~rel~SwitchPortAccess", args => Network_Root.Mk_CG_rel_CG_SwitchPortAccess((Network_Root.IArgType__CG_rel_CG_SwitchPortAccess__0)args[0]));
         ConstructorMap.Add("~rel~SwitchPortMode", args => Network_Root.Mk_CG_rel_CG_SwitchPortMode((Network_Root.IArgType__CG_rel_CG_SwitchPortMode__0)args[0]));
         ConstructorMap.Add("~rel~SwitchPortTrunk", args => Network_Root.Mk_CG_rel_CG_SwitchPortTrunk((Network_Root.IArgType__CG_rel_CG_SwitchPortTrunk__0)args[0]));
         ConstructorMap.Add("~rel~UI16Range", args => Network_Root.Mk_CG_rel_CG_UI16Range((Network_Root.IArgType__CG_rel_CG_UI16Range__0)args[0]));
         ConstructorMap.Add("~rel~UI32Range", args => Network_Root.Mk_CG_rel_CG_UI32Range((Network_Root.IArgType__CG_rel_CG_UI32Range__0)args[0]));
         ConstructorMap.Add("Network.#Any", args => MkUserCnst(Network_Root.Network.TypeCnstKind.Any));
         ConstructorMap.Add("Network.#Constant", args => MkUserCnst(Network_Root.Network.TypeCnstKind.Constant));
         ConstructorMap.Add("Network.#Data", args => MkUserCnst(Network_Root.Network.TypeCnstKind.Data));
         ConstructorMap.Add("Network.conforms", args => MkUserCnst(Network_Root.Network.UserCnstKind.conforms));
         ConstructorMap.Add("Network.notFunctional", args => MkUserCnst(Network_Root.Network.UserCnstKind.notFunctional));
         ConstructorMap.Add("Network.notInjective", args => MkUserCnst(Network_Root.Network.UserCnstKind.notInjective));
         ConstructorMap.Add("Network.notInvTotal", args => MkUserCnst(Network_Root.Network.UserCnstKind.notInvTotal));
         ConstructorMap.Add("Network.notRelational", args => MkUserCnst(Network_Root.Network.UserCnstKind.notRelational));
         ConstructorMap.Add("Network.notTotal", args => MkUserCnst(Network_Root.Network.UserCnstKind.notTotal));
         ConstructorMap.Add("NetworkTopology.#Any", args => MkUserCnst(Network_Root.NetworkTopology.TypeCnstKind.Any));
         ConstructorMap.Add("NetworkTopology.#Constant", args => MkUserCnst(Network_Root.NetworkTopology.TypeCnstKind.Constant));
         ConstructorMap.Add("NetworkTopology.#Data", args => MkUserCnst(Network_Root.NetworkTopology.TypeCnstKind.Data));
         ConstructorMap.Add("NetworkTopology.conforms", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind.conforms));
         ConstructorMap.Add("NetworkTopology.notFunctional", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind.notFunctional));
         ConstructorMap.Add("NetworkTopology.notInjective", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind.notInjective));
         ConstructorMap.Add("NetworkTopology.notInvTotal", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind.notInvTotal));
         ConstructorMap.Add("NetworkTopology.notRelational", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind.notRelational));
         ConstructorMap.Add("NetworkTopology.notTotal", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind.notTotal));
         ConstructorMap.Add("NetworkTopology.unidirectional", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind.unidirectional));
         ConstructorMap.Add("NetworkTopology.~conforms0", args => MkUserCnst(Network_Root.NetworkTopology.UserCnstKind._CG_conforms0));
         ConstructorMap.Add("RouterConfiguration.#Any", args => MkUserCnst(Network_Root.RouterConfiguration.TypeCnstKind.Any));
         ConstructorMap.Add("RouterConfiguration.#Constant", args => MkUserCnst(Network_Root.RouterConfiguration.TypeCnstKind.Constant));
         ConstructorMap.Add("RouterConfiguration.#Data", args => MkUserCnst(Network_Root.RouterConfiguration.TypeCnstKind.Data));
         ConstructorMap.Add("RouterConfiguration.conforms", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.conforms));
         ConstructorMap.Add("RouterConfiguration.duplicateAddress", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.duplicateAddress));
         ConstructorMap.Add("RouterConfiguration.mismatchNetworkAddress", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.mismatchNetworkAddress));
         ConstructorMap.Add("RouterConfiguration.notFunctional", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.notFunctional));
         ConstructorMap.Add("RouterConfiguration.notInjective", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.notInjective));
         ConstructorMap.Add("RouterConfiguration.notInvTotal", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.notInvTotal));
         ConstructorMap.Add("RouterConfiguration.notRelational", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.notRelational));
         ConstructorMap.Add("RouterConfiguration.notTotal", args => MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind.notTotal));
         ConstructorMap.Add("SwitchConfiguration.#Any", args => MkUserCnst(Network_Root.SwitchConfiguration.TypeCnstKind.Any));
         ConstructorMap.Add("SwitchConfiguration.#Constant", args => MkUserCnst(Network_Root.SwitchConfiguration.TypeCnstKind.Constant));
         ConstructorMap.Add("SwitchConfiguration.#Data", args => MkUserCnst(Network_Root.SwitchConfiguration.TypeCnstKind.Data));
         ConstructorMap.Add("SwitchConfiguration.conforms", args => MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind.conforms));
         ConstructorMap.Add("SwitchConfiguration.mismatchPortMode", args => MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind.mismatchPortMode));
         ConstructorMap.Add("SwitchConfiguration.notFunctional", args => MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind.notFunctional));
         ConstructorMap.Add("SwitchConfiguration.notInjective", args => MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind.notInjective));
         ConstructorMap.Add("SwitchConfiguration.notInvTotal", args => MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind.notInvTotal));
         ConstructorMap.Add("SwitchConfiguration.notRelational", args => MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind.notRelational));
         ConstructorMap.Add("SwitchConfiguration.notTotal", args => MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind.notTotal));
         ConstructorMap.Add("Types.#Any", args => MkUserCnst(Network_Root.Types.TypeCnstKind.Any));
         ConstructorMap.Add("Types.#Constant", args => MkUserCnst(Network_Root.Types.TypeCnstKind.Constant));
         ConstructorMap.Add("Types.#Data", args => MkUserCnst(Network_Root.Types.TypeCnstKind.Data));
         ConstructorMap.Add("Types.conforms", args => MkUserCnst(Network_Root.Types.UserCnstKind.conforms));
         ConstructorMap.Add("Types.notFunctional", args => MkUserCnst(Network_Root.Types.UserCnstKind.notFunctional));
         ConstructorMap.Add("Types.notInjective", args => MkUserCnst(Network_Root.Types.UserCnstKind.notInjective));
         ConstructorMap.Add("Types.notInvTotal", args => MkUserCnst(Network_Root.Types.UserCnstKind.notInvTotal));
         ConstructorMap.Add("Types.notRelational", args => MkUserCnst(Network_Root.Types.UserCnstKind.notRelational));
         ConstructorMap.Add("Types.notTotal", args => MkUserCnst(Network_Root.Types.UserCnstKind.notTotal));
      }

      public enum UserCnstKind
      {
         DENY,
         DESTINATION,
         DOT1Q,
         DOWN,
         ECHO,
         ECHO_REPLY,
         ESTABLISHED,
         FALSE,
         ICMP,
         IGMP,
         IN,
         INSIDE,
         IPV4,
         ISL,
         NIL,
         OUT,
         OUTSIDE,
         PERMIT,
         SOURCE,
         TCP,
         TRUE,
         UDP,
         UP
      }

      public enum TypeCnstKind
      {
         AccessList,
         AccessList_NDEX_0,
         AccessList_NDEX_1,
         AccessList_NDEX_2,
         AccessList_NDEX_3,
         AccessList_NDEX_4,
         AccessList_NDEX_5,
         AccessList_NDEX_6,
         AccessList_NDEX_7,
         AclAction,
         AclOptions,
         AclProtocol,
         Boolean,
         Device,
         FlowDirection,
         FrameRelayPort,
         FrameRelayPort_NDEX_0,
         FrameRelayPort_NDEX_1,
         FrameRelaySwitch,
         FrameRelaySwitch_NDEX_0,
         ID,
         IP,
         IP_NDEX_0,
         IcmpOptions,
         IgmpOptions,
         IgmpOptions_NDEX_0,
         Integer,
         Interface,
         InterfaceIpAccessGroup,
         InterfaceIpAccessGroup_NDEX_0,
         InterfaceIpAccessGroup_NDEX_1,
         InterfaceIpAccessGroup_NDEX_2,
         InterfaceIpAddress,
         InterfaceIpAddress_NDEX_0,
         InterfaceIpAddress_NDEX_1,
         InterfaceIpAddress_NDEX_2,
         InterfaceIpNat,
         InterfaceIpNat_NDEX_0,
         InterfaceIpNat_NDEX_1,
         InterfaceStatus,
         Interface_NDEX_0,
         Interface_NDEX_1,
         IpAccessList,
         IpAccessList_NDEX_0,
         IpNatDynamic,
         IpNatDynamic_NDEX_0,
         IpNatDynamic_NDEX_1,
         IpNatDynamic_NDEX_2,
         IpNatDynamic_NDEX_3,
         IpNatPool,
         IpNatPool_NDEX_0,
         IpNatPool_NDEX_1,
         IpNatPool_NDEX_2,
         IpNatPool_NDEX_3,
         IpNatStatic,
         IpNatStatic_NDEX_0,
         IpNatStatic_NDEX_1,
         IpNatStatic_NDEX_2,
         IpNatStatic_NDEX_3,
         IpRoute,
         IpRoute_NDEX_0,
         IpRoute_NDEX_1,
         IpRoute_NDEX_2,
         IpRoute_NDEX_3,
         Link,
         Link_NDEX_0,
         Link_NDEX_1,
         NatDirection,
         NatOrigin,
         Natural,
         NegInteger,
         PN,
         PN_NDEX_0,
         Port,
         PortList,
         PortList_NDEX_0,
         PortList_NDEX_1,
         PosInteger,
         Real,
         Router,
         RouterBgp,
         RouterBgp_NDEX_0,
         RouterEigrp,
         RouterEigrp_NDEX_0,
         RouterOsfp,
         RouterOsfp_NDEX_0,
         RouterPort,
         RouterPort_NDEX_0,
         RouterPort_NDEX_1,
         RouterRip,
         RouterRip_NDEX_0,
         Router_NDEX_0,
         String,
         Switch,
         SwitchInterface,
         SwitchInterface_NDEX_0,
         SwitchInterface_NDEX_1,
         SwitchPort,
         SwitchPortAccess,
         SwitchPortAccess_NDEX_0,
         SwitchPortMode,
         SwitchPortMode_NDEX_0,
         SwitchPortMode_NDEX_1,
         SwitchPortTrunk,
         SwitchPortTrunk_NDEX_0,
         SwitchPortTrunk_NDEX_1,
         SwitchPort_NDEX_0,
         SwitchPort_NDEX_1,
         Switch_NDEX_0,
         TcpOptions,
         TrunkEncapsulation,
         UI16,
         UI16Range,
         UI16Range_NDEX_0,
         UI16Range_NDEX_1,
         UI32,
         UI32Range,
         UI32Range_NDEX_0,
         UI32Range_NDEX_1,
         UI8,
         device,
         device_NDEX_0,
         device_NDEX_1,
         edge,
         edge_NDEX_0,
         edge_NDEX_1,
         path,
         path_NDEX_0,
         path_NDEX_1,
         sameLan,
         sameLan_NDEX_0,
         sameLan_NDEX_1
      }

      public static readonly string[] UserCnstNames =
      {
         "DENY",
         "DESTINATION",
         "DOT1Q",
         "DOWN",
         "ECHO",
         "ECHO_REPLY",
         "ESTABLISHED",
         "FALSE",
         "ICMP",
         "IGMP",
         "IN",
         "INSIDE",
         "IPV4",
         "ISL",
         "NIL",
         "OUT",
         "OUTSIDE",
         "PERMIT",
         "SOURCE",
         "TCP",
         "TRUE",
         "UDP",
         "UP"
      };

      public static readonly string[] TypeCnstNames =
      {
         "#AccessList",
         "#AccessList[0]",
         "#AccessList[1]",
         "#AccessList[2]",
         "#AccessList[3]",
         "#AccessList[4]",
         "#AccessList[5]",
         "#AccessList[6]",
         "#AccessList[7]",
         "#AclAction",
         "#AclOptions",
         "#AclProtocol",
         "#Boolean",
         "#Device",
         "#FlowDirection",
         "#FrameRelayPort",
         "#FrameRelayPort[0]",
         "#FrameRelayPort[1]",
         "#FrameRelaySwitch",
         "#FrameRelaySwitch[0]",
         "#ID",
         "#IP",
         "#IP[0]",
         "#IcmpOptions",
         "#IgmpOptions",
         "#IgmpOptions[0]",
         "#Integer",
         "#Interface",
         "#InterfaceIpAccessGroup",
         "#InterfaceIpAccessGroup[0]",
         "#InterfaceIpAccessGroup[1]",
         "#InterfaceIpAccessGroup[2]",
         "#InterfaceIpAddress",
         "#InterfaceIpAddress[0]",
         "#InterfaceIpAddress[1]",
         "#InterfaceIpAddress[2]",
         "#InterfaceIpNat",
         "#InterfaceIpNat[0]",
         "#InterfaceIpNat[1]",
         "#InterfaceStatus",
         "#Interface[0]",
         "#Interface[1]",
         "#IpAccessList",
         "#IpAccessList[0]",
         "#IpNatDynamic",
         "#IpNatDynamic[0]",
         "#IpNatDynamic[1]",
         "#IpNatDynamic[2]",
         "#IpNatDynamic[3]",
         "#IpNatPool",
         "#IpNatPool[0]",
         "#IpNatPool[1]",
         "#IpNatPool[2]",
         "#IpNatPool[3]",
         "#IpNatStatic",
         "#IpNatStatic[0]",
         "#IpNatStatic[1]",
         "#IpNatStatic[2]",
         "#IpNatStatic[3]",
         "#IpRoute",
         "#IpRoute[0]",
         "#IpRoute[1]",
         "#IpRoute[2]",
         "#IpRoute[3]",
         "#Link",
         "#Link[0]",
         "#Link[1]",
         "#NatDirection",
         "#NatOrigin",
         "#Natural",
         "#NegInteger",
         "#PN",
         "#PN[0]",
         "#Port",
         "#PortList",
         "#PortList[0]",
         "#PortList[1]",
         "#PosInteger",
         "#Real",
         "#Router",
         "#RouterBgp",
         "#RouterBgp[0]",
         "#RouterEigrp",
         "#RouterEigrp[0]",
         "#RouterOsfp",
         "#RouterOsfp[0]",
         "#RouterPort",
         "#RouterPort[0]",
         "#RouterPort[1]",
         "#RouterRip",
         "#RouterRip[0]",
         "#Router[0]",
         "#String",
         "#Switch",
         "#SwitchInterface",
         "#SwitchInterface[0]",
         "#SwitchInterface[1]",
         "#SwitchPort",
         "#SwitchPortAccess",
         "#SwitchPortAccess[0]",
         "#SwitchPortMode",
         "#SwitchPortMode[0]",
         "#SwitchPortMode[1]",
         "#SwitchPortTrunk",
         "#SwitchPortTrunk[0]",
         "#SwitchPortTrunk[1]",
         "#SwitchPort[0]",
         "#SwitchPort[1]",
         "#Switch[0]",
         "#TcpOptions",
         "#TrunkEncapsulation",
         "#UI16",
         "#UI16Range",
         "#UI16Range[0]",
         "#UI16Range[1]",
         "#UI32",
         "#UI32Range",
         "#UI32Range[0]",
         "#UI32Range[1]",
         "#UI8",
         "#device",
         "#device[0]",
         "#device[1]",
         "#edge",
         "#edge[0]",
         "#edge[1]",
         "#path",
         "#path[0]",
         "#path[1]",
         "#sameLan",
         "#sameLan[0]",
         "#sameLan[1]"
      };

      public static string Namespace { get { return ""; } }

      public static bool CreateObjectGraph(Env env, ProgramName progName, string modelName, out Task<ObjectGraphResult> task)
      {
         Contract.Requires(env != null && progName != null && !string.IsNullOrEmpty(modelName));
         return env.CreateObjectGraph(progName, modelName, MkNumeric, MkString, ConstructorMap, out task);
      }

      public static RealCnst MkNumeric(int val)
      {
         var n = new RealCnst();
         n.Value = new Rational(val);
         return n;
      }

      public static RealCnst MkNumeric(double val)
      {
         var n = new RealCnst();
         n.Value = new Rational(val);
         return n;
      }

      public static RealCnst MkNumeric(Rational val)
      {
         var n = new RealCnst();
         n.Value = val;
         return n;
      }

      public static StringCnst MkString(string val = default(string))
      {
         var n = new StringCnst();
         n.Value = val;
         return n;
      }

      public static Quotation MkQuotation(string val = default(string))
      {
         var n = new Quotation();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.UserCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.TypeCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.Network.UserCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.Network.TypeCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.NetworkTopology.UserCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.NetworkTopology.TypeCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.RouterConfiguration.UserCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.RouterConfiguration.TypeCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.SwitchConfiguration.UserCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.SwitchConfiguration.TypeCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.Types.UserCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static UserCnst MkUserCnst(Network_Root.Types.TypeCnstKind val)
      {
         var n = new UserCnst();
         n.Value = val;
         return n;
      }

      public static Network_Root.AccessList MkAccessList(Network_Root.IArgType_AccessList__0 acl = null, Network_Root.IArgType_AccessList__1 action = null, Network_Root.IArgType_AccessList__2 pt = null, Network_Root.IArgType_AccessList__3 srcIp = null, Network_Root.IArgType_AccessList__4 srcPn = null, Network_Root.IArgType_AccessList__5 dstIp = null, Network_Root.IArgType_AccessList__6 dstPn = null, Network_Root.IArgType_AccessList__7 opts = null)
      {
         var _n_ = new Network_Root.AccessList();
         if (acl != null)
         {
            _n_.acl = acl;
         }

         if (action != null)
         {
            _n_.action = action;
         }

         if (pt != null)
         {
            _n_.pt = pt;
         }

         if (srcIp != null)
         {
            _n_.srcIp = srcIp;
         }

         if (srcPn != null)
         {
            _n_.srcPn = srcPn;
         }

         if (dstIp != null)
         {
            _n_.dstIp = dstIp;
         }

         if (dstPn != null)
         {
            _n_.dstPn = dstPn;
         }

         if (opts != null)
         {
            _n_.opts = opts;
         }

         return _n_;
      }

      public static Network_Root.FrameRelayPort MkFrameRelayPort(Network_Root.IArgType_FrameRelayPort__0 @switch = null, Network_Root.IArgType_FrameRelayPort__1 id = null)
      {
         var _n_ = new Network_Root.FrameRelayPort();
         if (@switch != null)
         {
            _n_.@switch = @switch;
         }

         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.FrameRelaySwitch MkFrameRelaySwitch(Network_Root.IArgType_FrameRelaySwitch__0 name = null)
      {
         var _n_ = new Network_Root.FrameRelaySwitch();
         if (name != null)
         {
            _n_.name = name;
         }

         return _n_;
      }

      public static Network_Root.IP MkIP(Network_Root.IArgType_IP__0 address = null)
      {
         var _n_ = new Network_Root.IP();
         if (address != null)
         {
            _n_.address = address;
         }

         return _n_;
      }

      public static Network_Root.IgmpOptions MkIgmpOptions(Network_Root.IArgType_IgmpOptions__0 msgtype = null)
      {
         var _n_ = new Network_Root.IgmpOptions();
         if (msgtype != null)
         {
            _n_.msgtype = msgtype;
         }

         return _n_;
      }

      public static Network_Root.Interface MkInterface(Network_Root.IArgType_Interface__0 id = null, Network_Root.IArgType_Interface__1 port = null)
      {
         var _n_ = new Network_Root.Interface();
         if (id != null)
         {
            _n_.id = id;
         }

         if (port != null)
         {
            _n_.port = port;
         }

         return _n_;
      }

      public static Network_Root.InterfaceIpAccessGroup MkInterfaceIpAccessGroup(Network_Root.IArgType_InterfaceIpAccessGroup__0 iface = null, Network_Root.IArgType_InterfaceIpAccessGroup__1 acl = null, Network_Root.IArgType_InterfaceIpAccessGroup__2 direction = null)
      {
         var _n_ = new Network_Root.InterfaceIpAccessGroup();
         if (iface != null)
         {
            _n_.iface = iface;
         }

         if (acl != null)
         {
            _n_.acl = acl;
         }

         if (direction != null)
         {
            _n_.direction = direction;
         }

         return _n_;
      }

      public static Network_Root.InterfaceIpAddress MkInterfaceIpAddress(Network_Root.IArgType_InterfaceIpAddress__0 iface = null, Network_Root.IArgType_InterfaceIpAddress__1 host = null, Network_Root.IArgType_InterfaceIpAddress__2 network = null)
      {
         var _n_ = new Network_Root.InterfaceIpAddress();
         if (iface != null)
         {
            _n_.iface = iface;
         }

         if (host != null)
         {
            _n_.host = host;
         }

         if (network != null)
         {
            _n_.network = network;
         }

         return _n_;
      }

      public static Network_Root.InterfaceIpNat MkInterfaceIpNat(Network_Root.IArgType_InterfaceIpNat__0 iface = null, Network_Root.IArgType_InterfaceIpNat__1 dir = null)
      {
         var _n_ = new Network_Root.InterfaceIpNat();
         if (iface != null)
         {
            _n_.iface = iface;
         }

         if (dir != null)
         {
            _n_.dir = dir;
         }

         return _n_;
      }

      public static Network_Root.IpAccessList MkIpAccessList(Network_Root.IArgType_IpAccessList__0 id = null)
      {
         var _n_ = new Network_Root.IpAccessList();
         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.IpNatDynamic MkIpNatDynamic(Network_Root.IArgType_IpNatDynamic__0 dir = null, Network_Root.IArgType_IpNatDynamic__1 orig = null, Network_Root.IArgType_IpNatDynamic__2 acl = null, Network_Root.IArgType_IpNatDynamic__3 pool = null)
      {
         var _n_ = new Network_Root.IpNatDynamic();
         if (dir != null)
         {
            _n_.dir = dir;
         }

         if (orig != null)
         {
            _n_.orig = orig;
         }

         if (acl != null)
         {
            _n_.acl = acl;
         }

         if (pool != null)
         {
            _n_.pool = pool;
         }

         return _n_;
      }

      public static Network_Root.IpNatPool MkIpNatPool(Network_Root.IArgType_IpNatPool__0 id = null, Network_Root.IArgType_IpNatPool__1 start = null, Network_Root.IArgType_IpNatPool__2 end = null, Network_Root.IArgType_IpNatPool__3 network = null)
      {
         var _n_ = new Network_Root.IpNatPool();
         if (id != null)
         {
            _n_.id = id;
         }

         if (start != null)
         {
            _n_.start = start;
         }

         if (end != null)
         {
            _n_.end = end;
         }

         if (network != null)
         {
            _n_.network = network;
         }

         return _n_;
      }

      public static Network_Root.IpNatStatic MkIpNatStatic(Network_Root.IArgType_IpNatStatic__0 dir = null, Network_Root.IArgType_IpNatStatic__1 orig = null, Network_Root.IArgType_IpNatStatic__2 local = null, Network_Root.IArgType_IpNatStatic__3 @global = null)
      {
         var _n_ = new Network_Root.IpNatStatic();
         if (dir != null)
         {
            _n_.dir = dir;
         }

         if (orig != null)
         {
            _n_.orig = orig;
         }

         if (local != null)
         {
            _n_.local = local;
         }

         if (@global != null)
         {
            _n_.@global = @global;
         }

         return _n_;
      }

      public static Network_Root.IpRoute MkIpRoute(Network_Root.IArgType_IpRoute__0 router = null, Network_Root.IArgType_IpRoute__1 network = null, Network_Root.IArgType_IpRoute__2 iface = null, Network_Root.IArgType_IpRoute__3 nexthop = null)
      {
         var _n_ = new Network_Root.IpRoute();
         if (router != null)
         {
            _n_.router = router;
         }

         if (network != null)
         {
            _n_.network = network;
         }

         if (iface != null)
         {
            _n_.iface = iface;
         }

         if (nexthop != null)
         {
            _n_.nexthop = nexthop;
         }

         return _n_;
      }

      public static Network_Root.Link MkLink(Network_Root.IArgType_Link__0 source = null, Network_Root.IArgType_Link__1 target = null)
      {
         var _n_ = new Network_Root.Link();
         if (source != null)
         {
            _n_.source = source;
         }

         if (target != null)
         {
            _n_.target = target;
         }

         return _n_;
      }

      public static Network_Root.PN MkPN(Network_Root.IArgType_PN__0 port = null)
      {
         var _n_ = new Network_Root.PN();
         if (port != null)
         {
            _n_.port = port;
         }

         return _n_;
      }

      public static Network_Root.PortList MkPortList(Network_Root.IArgType_PortList__0 arg_0 = null, Network_Root.IArgType_PortList__1 arg_1 = null)
      {
         var _n_ = new Network_Root.PortList();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         if (arg_1 != null)
         {
            _n_._1 = arg_1;
         }

         return _n_;
      }

      public static Network_Root.Router MkRouter(Network_Root.IArgType_Router__0 name = null)
      {
         var _n_ = new Network_Root.Router();
         if (name != null)
         {
            _n_.name = name;
         }

         return _n_;
      }

      public static Network_Root.RouterBgp MkRouterBgp(Network_Root.IArgType_RouterBgp__0 id = null)
      {
         var _n_ = new Network_Root.RouterBgp();
         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.RouterEigrp MkRouterEigrp(Network_Root.IArgType_RouterEigrp__0 id = null)
      {
         var _n_ = new Network_Root.RouterEigrp();
         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.RouterOsfp MkRouterOsfp(Network_Root.IArgType_RouterOsfp__0 id = null)
      {
         var _n_ = new Network_Root.RouterOsfp();
         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.RouterPort MkRouterPort(Network_Root.IArgType_RouterPort__0 router = null, Network_Root.IArgType_RouterPort__1 id = null)
      {
         var _n_ = new Network_Root.RouterPort();
         if (router != null)
         {
            _n_.router = router;
         }

         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.RouterRip MkRouterRip(Network_Root.IArgType_RouterRip__0 id = null)
      {
         var _n_ = new Network_Root.RouterRip();
         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.Switch MkSwitch(Network_Root.IArgType_Switch__0 name = null)
      {
         var _n_ = new Network_Root.Switch();
         if (name != null)
         {
            _n_.name = name;
         }

         return _n_;
      }

      public static Network_Root.SwitchInterface MkSwitchInterface(Network_Root.IArgType_SwitchInterface__0 id = null, Network_Root.IArgType_SwitchInterface__1 port = null)
      {
         var _n_ = new Network_Root.SwitchInterface();
         if (id != null)
         {
            _n_.id = id;
         }

         if (port != null)
         {
            _n_.port = port;
         }

         return _n_;
      }

      public static Network_Root.SwitchPort MkSwitchPort(Network_Root.IArgType_SwitchPort__0 @switch = null, Network_Root.IArgType_SwitchPort__1 id = null)
      {
         var _n_ = new Network_Root.SwitchPort();
         if (@switch != null)
         {
            _n_.@switch = @switch;
         }

         if (id != null)
         {
            _n_.id = id;
         }

         return _n_;
      }

      public static Network_Root.SwitchPortAccess MkSwitchPortAccess(Network_Root.IArgType_SwitchPortAccess__0 vlan = null)
      {
         var _n_ = new Network_Root.SwitchPortAccess();
         if (vlan != null)
         {
            _n_.vlan = vlan;
         }

         return _n_;
      }

      public static Network_Root.SwitchPortMode MkSwitchPortMode(Network_Root.IArgType_SwitchPortMode__0 iface = null, Network_Root.IArgType_SwitchPortMode__1 mode = null)
      {
         var _n_ = new Network_Root.SwitchPortMode();
         if (iface != null)
         {
            _n_.iface = iface;
         }

         if (mode != null)
         {
            _n_.mode = mode;
         }

         return _n_;
      }

      public static Network_Root.SwitchPortTrunk MkSwitchPortTrunk(Network_Root.IArgType_SwitchPortTrunk__0 encapsulation = null, Network_Root.IArgType_SwitchPortTrunk__1 native = null)
      {
         var _n_ = new Network_Root.SwitchPortTrunk();
         if (encapsulation != null)
         {
            _n_.encapsulation = encapsulation;
         }

         if (native != null)
         {
            _n_.native = native;
         }

         return _n_;
      }

      public static Network_Root.UI16Range MkUI16Range(Network_Root.IArgType_UI16Range__0 left = null, Network_Root.IArgType_UI16Range__1 right = null)
      {
         var _n_ = new Network_Root.UI16Range();
         if (left != null)
         {
            _n_.left = left;
         }

         if (right != null)
         {
            _n_.right = right;
         }

         return _n_;
      }

      public static Network_Root.UI32Range MkUI32Range(Network_Root.IArgType_UI32Range__0 left = null, Network_Root.IArgType_UI32Range__1 right = null)
      {
         var _n_ = new Network_Root.UI32Range();
         if (left != null)
         {
            _n_.left = left;
         }

         if (right != null)
         {
            _n_.right = right;
         }

         return _n_;
      }

      public static Network_Root.device Mkdevice(Network_Root.IArgType_device__0 port = null, Network_Root.IArgType_device__1 dev = null)
      {
         var _n_ = new Network_Root.device();
         if (port != null)
         {
            _n_.port = port;
         }

         if (dev != null)
         {
            _n_.dev = dev;
         }

         return _n_;
      }

      public static Network_Root.edge Mkedge(Network_Root.IArgType_edge__0 arg_0 = null, Network_Root.IArgType_edge__1 arg_1 = null)
      {
         var _n_ = new Network_Root.edge();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         if (arg_1 != null)
         {
            _n_._1 = arg_1;
         }

         return _n_;
      }

      public static Network_Root.path Mkpath(Network_Root.IArgType_path__0 source = null, Network_Root.IArgType_path__1 target = null)
      {
         var _n_ = new Network_Root.path();
         if (source != null)
         {
            _n_.source = source;
         }

         if (target != null)
         {
            _n_.target = target;
         }

         return _n_;
      }

      public static Network_Root.sameLan MksameLan(Network_Root.IArgType_sameLan__0 x = null, Network_Root.IArgType_sameLan__1 y = null)
      {
         var _n_ = new Network_Root.sameLan();
         if (x != null)
         {
            _n_.x = x;
         }

         if (y != null)
         {
            _n_.y = y;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_AccessList Mk_CG_rel_CG_AccessList(Network_Root.IArgType__CG_rel_CG_AccessList__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_AccessList();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_FrameRelayPort Mk_CG_rel_CG_FrameRelayPort(Network_Root.IArgType__CG_rel_CG_FrameRelayPort__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_FrameRelayPort();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_FrameRelaySwitch Mk_CG_rel_CG_FrameRelaySwitch(Network_Root.IArgType__CG_rel_CG_FrameRelaySwitch__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_FrameRelaySwitch();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_IgmpOptions Mk_CG_rel_CG_IgmpOptions(Network_Root.IArgType__CG_rel_CG_IgmpOptions__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_IgmpOptions();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_Interface Mk_CG_rel_CG_Interface(Network_Root.IArgType__CG_rel_CG_Interface__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_Interface();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_InterfaceIpAccessGroup Mk_CG_rel_CG_InterfaceIpAccessGroup(Network_Root.IArgType__CG_rel_CG_InterfaceIpAccessGroup__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_InterfaceIpAccessGroup();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_InterfaceIpAddress Mk_CG_rel_CG_InterfaceIpAddress(Network_Root.IArgType__CG_rel_CG_InterfaceIpAddress__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_InterfaceIpAddress();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_IpAccessList Mk_CG_rel_CG_IpAccessList(Network_Root.IArgType__CG_rel_CG_IpAccessList__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_IpAccessList();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_IpNatDynamic Mk_CG_rel_CG_IpNatDynamic(Network_Root.IArgType__CG_rel_CG_IpNatDynamic__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_IpNatDynamic();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_IpNatPool Mk_CG_rel_CG_IpNatPool(Network_Root.IArgType__CG_rel_CG_IpNatPool__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_IpNatPool();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_IpNatStatic Mk_CG_rel_CG_IpNatStatic(Network_Root.IArgType__CG_rel_CG_IpNatStatic__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_IpNatStatic();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_IpRoute Mk_CG_rel_CG_IpRoute(Network_Root.IArgType__CG_rel_CG_IpRoute__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_IpRoute();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_Link Mk_CG_rel_CG_Link(Network_Root.IArgType__CG_rel_CG_Link__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_Link();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_PortList Mk_CG_rel_CG_PortList(Network_Root.IArgType__CG_rel_CG_PortList__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_PortList();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_Router Mk_CG_rel_CG_Router(Network_Root.IArgType__CG_rel_CG_Router__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_Router();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_RouterBgp Mk_CG_rel_CG_RouterBgp(Network_Root.IArgType__CG_rel_CG_RouterBgp__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_RouterBgp();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_RouterEigrp Mk_CG_rel_CG_RouterEigrp(Network_Root.IArgType__CG_rel_CG_RouterEigrp__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_RouterEigrp();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_RouterOsfp Mk_CG_rel_CG_RouterOsfp(Network_Root.IArgType__CG_rel_CG_RouterOsfp__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_RouterOsfp();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_RouterPort Mk_CG_rel_CG_RouterPort(Network_Root.IArgType__CG_rel_CG_RouterPort__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_RouterPort();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_RouterRip Mk_CG_rel_CG_RouterRip(Network_Root.IArgType__CG_rel_CG_RouterRip__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_RouterRip();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_Switch Mk_CG_rel_CG_Switch(Network_Root.IArgType__CG_rel_CG_Switch__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_Switch();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_SwitchInterface Mk_CG_rel_CG_SwitchInterface(Network_Root.IArgType__CG_rel_CG_SwitchInterface__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_SwitchInterface();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_SwitchPort Mk_CG_rel_CG_SwitchPort(Network_Root.IArgType__CG_rel_CG_SwitchPort__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_SwitchPort();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_SwitchPortAccess Mk_CG_rel_CG_SwitchPortAccess(Network_Root.IArgType__CG_rel_CG_SwitchPortAccess__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_SwitchPortAccess();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_SwitchPortMode Mk_CG_rel_CG_SwitchPortMode(Network_Root.IArgType__CG_rel_CG_SwitchPortMode__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_SwitchPortMode();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_SwitchPortTrunk Mk_CG_rel_CG_SwitchPortTrunk(Network_Root.IArgType__CG_rel_CG_SwitchPortTrunk__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_SwitchPortTrunk();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_UI16Range Mk_CG_rel_CG_UI16Range(Network_Root.IArgType__CG_rel_CG_UI16Range__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_UI16Range();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public static Network_Root._CG_rel_CG_UI32Range Mk_CG_rel_CG_UI32Range(Network_Root.IArgType__CG_rel_CG_UI32Range__0 arg_0 = null)
      {
         var _n_ = new Network_Root._CG_rel_CG_UI32Range();
         if (arg_0 != null)
         {
            _n_._0 = arg_0;
         }

         return _n_;
      }

      public abstract partial class GroundTerm :
         ICSharpTerm
      {
         protected SpinLock rwLock = new SpinLock();
         Span span = default(Span);
         public Span Span { get { return Get<Span>(() => span); } set { Set(() => { span = value; }); } }
         public abstract int Arity { get; }
         public abstract object Symbol { get; }
         public abstract ICSharpTerm this[int index] { get; }
         protected T Get<T>(Func<T> getter)
         {
            bool gotLock = false;
            try
            {
               rwLock.Enter(ref gotLock);
               return getter();
            }
            finally
            {
               if (gotLock)
               {
                  rwLock.Exit();
               }
            }
         }

         protected void Set(System.Action setter)
         {
            bool gotLock = false;
            try
            {
               rwLock.Enter(ref gotLock);
               setter();
            }
            finally
            {
               if (gotLock)
               {
                  rwLock.Exit();
               }
            }
         }
      }

      public interface IArgType_AccessList__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_AccessList__1 :
         ICSharpTerm
      {
      }

      public interface IArgType_AccessList__2 :
         ICSharpTerm
      {
      }

      public interface IArgType_AccessList__3 :
         ICSharpTerm
      {
      }

      public interface IArgType_AccessList__4 :
         ICSharpTerm
      {
      }

      public interface IArgType_AccessList__5 :
         ICSharpTerm
      {
      }

      public interface IArgType_AccessList__6 :
         ICSharpTerm
      {
      }

      public interface IArgType_AccessList__7 :
         ICSharpTerm
      {
      }

      public partial class AccessList :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_AccessList__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_AccessList__0 _0_val = new Network_Root.IpAccessList();
         private Network_Root.IArgType_AccessList__1 _1_val = MkUserCnst(Network_Root.UserCnstKind.DENY);
         private Network_Root.IArgType_AccessList__2 _2_val = MkUserCnst(Network_Root.UserCnstKind.ICMP);
         private Network_Root.IArgType_AccessList__3 _3_val = new Network_Root.UI32Range();
         private Network_Root.IArgType_AccessList__4 _4_val = new Network_Root.UI16Range();
         private Network_Root.IArgType_AccessList__5 _5_val = new Network_Root.UI32Range();
         private Network_Root.IArgType_AccessList__6 _6_val = new Network_Root.UI16Range();
         private Network_Root.IArgType_AccessList__7 _7_val = MkUserCnst(Network_Root.UserCnstKind.NIL);

         public Network_Root.IArgType_AccessList__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_AccessList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_AccessList__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__2 _2
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_AccessList__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__3 _3
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_AccessList__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__4 _4
         {
            get
            {
               Contract.Ensures(_4_val != null);
               return Get<Network_Root.IArgType_AccessList__4>(() => _4_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _4_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__5 _5
         {
            get
            {
               Contract.Ensures(_5_val != null);
               return Get<Network_Root.IArgType_AccessList__5>(() => _5_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _5_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__6 _6
         {
            get
            {
               Contract.Ensures(_6_val != null);
               return Get<Network_Root.IArgType_AccessList__6>(() => _6_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _6_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__7 _7
         {
            get
            {
               Contract.Ensures(_7_val != null);
               return Get<Network_Root.IArgType_AccessList__7>(() => _7_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _7_val = value; });
            }
         }


         public Network_Root.IArgType_AccessList__0 acl
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_AccessList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__1 action
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_AccessList__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__2 pt
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_AccessList__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__3 srcIp
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_AccessList__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__4 srcPn
         {
            get
            {
               Contract.Ensures(_4_val != null);
               return Get<Network_Root.IArgType_AccessList__4>(() => _4_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _4_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__5 dstIp
         {
            get
            {
               Contract.Ensures(_5_val != null);
               return Get<Network_Root.IArgType_AccessList__5>(() => _5_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _5_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__6 dstPn
         {
            get
            {
               Contract.Ensures(_6_val != null);
               return Get<Network_Root.IArgType_AccessList__6>(() => _6_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _6_val = value; });
            }
         }

         public Network_Root.IArgType_AccessList__7 opts
         {
            get
            {
               Contract.Ensures(_7_val != null);
               return Get<Network_Root.IArgType_AccessList__7>(() => _7_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _7_val = value; });
            }
         }

         public override int Arity { get { return 8; } }
         public override object Symbol { get { return "AccessList"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        case 2:
                           return _2_val;
                        case 3:
                           return _3_val;
                        case 4:
                           return _4_val;
                        case 5:
                           return _5_val;
                        case 6:
                           return _6_val;
                        case 7:
                           return _7_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface AclAction :
         ICSharpTerm
      {
      }

      public interface AclOptions :
         ICSharpTerm
      {
      }

      public interface AclProtocol :
         ICSharpTerm
      {
      }

      public interface Boolean :
         ICSharpTerm
      {
      }

      public interface Device :
         ICSharpTerm
      {
      }

      public interface FlowDirection :
         ICSharpTerm
      {
      }

      public interface IArgType_FrameRelayPort__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_FrameRelayPort__1 :
         ICSharpTerm
      {
      }

      public partial class FrameRelayPort :
         GroundTerm,
         Network_Root.IArgType_Link__0,
         Network_Root.IArgType_Link__1,
         Network_Root.IArgType_PortList__0,
         Network_Root.IArgType__CG_rel_CG_FrameRelayPort__0,
         Network_Root.IArgType_device__0,
         Network_Root.IArgType_edge__0,
         Network_Root.IArgType_edge__1,
         Network_Root.IArgType_path__0,
         Network_Root.IArgType_path__1,
         Network_Root.IArgType_sameLan__0,
         Network_Root.IArgType_sameLan__1,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.Port,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_FrameRelayPort__0 _0_val = new Network_Root.FrameRelaySwitch();
         private Network_Root.IArgType_FrameRelayPort__1 _1_val = MkString("");

         public Network_Root.IArgType_FrameRelayPort__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_FrameRelayPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_FrameRelayPort__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_FrameRelayPort__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_FrameRelayPort__0 @switch
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_FrameRelayPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_FrameRelayPort__1 id
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_FrameRelayPort__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "FrameRelayPort"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_FrameRelaySwitch__0 :
         ICSharpTerm
      {
      }

      public partial class FrameRelaySwitch :
         GroundTerm,
         Network_Root.Device,
         Network_Root.IArgType_FrameRelayPort__0,
         Network_Root.IArgType__CG_rel_CG_FrameRelaySwitch__0,
         Network_Root.IArgType_device__1,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_FrameRelaySwitch__0 _0_val = MkString("");

         public Network_Root.IArgType_FrameRelaySwitch__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_FrameRelaySwitch__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_FrameRelaySwitch__0 name
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_FrameRelaySwitch__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "FrameRelaySwitch"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface ID :
         ICSharpTerm
      {
      }

      public interface IArgType_IP__0 :
         ICSharpTerm
      {
      }

      public partial class IP :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.Types.Any
      {
         private Network_Root.IArgType_IP__0 _0_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_IP__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IP__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_IP__0 address
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IP__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "IP"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IcmpOptions :
         ICSharpTerm
      {
      }

      public interface IArgType_IgmpOptions__0 :
         ICSharpTerm
      {
      }

      public partial class IgmpOptions :
         GroundTerm,
         Network_Root.AclOptions,
         Network_Root.IArgType_AccessList__7,
         Network_Root.IArgType__CG_rel_CG_IgmpOptions__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_IgmpOptions__0 _0_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_IgmpOptions__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IgmpOptions__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_IgmpOptions__0 msgtype
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IgmpOptions__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "IgmpOptions"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface Integer :
         ICSharpTerm
      {
      }

      public interface IArgType_Interface__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_Interface__1 :
         ICSharpTerm
      {
      }

      public partial class Interface :
         GroundTerm,
         Network_Root.IArgType_InterfaceIpAccessGroup__0,
         Network_Root.IArgType_InterfaceIpAddress__0,
         Network_Root.IArgType_InterfaceIpNat__0,
         Network_Root.IArgType__CG_rel_CG_Interface__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_Interface__0 _0_val = MkString("");
         private Network_Root.IArgType_Interface__1 _1_val = new Network_Root.RouterPort();

         public Network_Root.IArgType_Interface__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Interface__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_Interface__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_Interface__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_Interface__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Interface__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_Interface__1 port
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_Interface__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "Interface"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_InterfaceIpAccessGroup__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_InterfaceIpAccessGroup__1 :
         ICSharpTerm
      {
      }

      public interface IArgType_InterfaceIpAccessGroup__2 :
         ICSharpTerm
      {
      }

      public partial class InterfaceIpAccessGroup :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_InterfaceIpAccessGroup__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_InterfaceIpAccessGroup__0 _0_val = new Network_Root.Interface();
         private Network_Root.IArgType_InterfaceIpAccessGroup__1 _1_val = MkString("");
         private Network_Root.IArgType_InterfaceIpAccessGroup__2 _2_val = MkUserCnst(Network_Root.UserCnstKind.IN);

         public Network_Root.IArgType_InterfaceIpAccessGroup__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAccessGroup__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAccessGroup__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAccessGroup__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAccessGroup__2 _2
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAccessGroup__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }


         public Network_Root.IArgType_InterfaceIpAccessGroup__0 iface
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAccessGroup__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAccessGroup__1 acl
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAccessGroup__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAccessGroup__2 direction
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAccessGroup__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public override int Arity { get { return 3; } }
         public override object Symbol { get { return "InterfaceIpAccessGroup"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        case 2:
                           return _2_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_InterfaceIpAddress__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_InterfaceIpAddress__1 :
         ICSharpTerm
      {
      }

      public interface IArgType_InterfaceIpAddress__2 :
         ICSharpTerm
      {
      }

      public partial class InterfaceIpAddress :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_InterfaceIpAddress__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_InterfaceIpAddress__0 _0_val = new Network_Root.Interface();
         private Network_Root.IArgType_InterfaceIpAddress__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
         private Network_Root.IArgType_InterfaceIpAddress__2 _2_val = new Network_Root.UI32Range();

         public Network_Root.IArgType_InterfaceIpAddress__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAddress__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAddress__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAddress__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAddress__2 _2
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAddress__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }


         public Network_Root.IArgType_InterfaceIpAddress__0 iface
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAddress__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAddress__1 host
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAddress__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpAddress__2 network
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_InterfaceIpAddress__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public override int Arity { get { return 3; } }
         public override object Symbol { get { return "InterfaceIpAddress"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        case 2:
                           return _2_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_InterfaceIpNat__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_InterfaceIpNat__1 :
         ICSharpTerm
      {
      }

      public partial class InterfaceIpNat :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType_InterfaceIpNat__0 _0_val = new Network_Root.Interface();
         private Network_Root.IArgType_InterfaceIpNat__1 _1_val = MkUserCnst(Network_Root.UserCnstKind.INSIDE);

         public Network_Root.IArgType_InterfaceIpNat__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_InterfaceIpNat__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpNat__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_InterfaceIpNat__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_InterfaceIpNat__0 iface
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_InterfaceIpNat__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_InterfaceIpNat__1 dir
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_InterfaceIpNat__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "InterfaceIpNat"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface InterfaceStatus :
         ICSharpTerm
      {
      }

      public interface IArgType_IpAccessList__0 :
         ICSharpTerm
      {
      }

      public partial class IpAccessList :
         GroundTerm,
         Network_Root.IArgType_AccessList__0,
         Network_Root.IArgType_IpNatDynamic__2,
         Network_Root.IArgType__CG_rel_CG_IpAccessList__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_IpAccessList__0 _0_val = MkString("");

         public Network_Root.IArgType_IpAccessList__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpAccessList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_IpAccessList__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpAccessList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "IpAccessList"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_IpNatDynamic__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatDynamic__1 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatDynamic__2 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatDynamic__3 :
         ICSharpTerm
      {
      }

      public partial class IpNatDynamic :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_IpNatDynamic__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_IpNatDynamic__0 _0_val = MkUserCnst(Network_Root.UserCnstKind.INSIDE);
         private Network_Root.IArgType_IpNatDynamic__1 _1_val = MkUserCnst(Network_Root.UserCnstKind.DESTINATION);
         private Network_Root.IArgType_IpNatDynamic__2 _2_val = new Network_Root.IpAccessList();
         private Network_Root.IArgType_IpNatDynamic__3 _3_val = new Network_Root.IpNatPool();

         public Network_Root.IArgType_IpNatDynamic__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatDynamic__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatDynamic__2 _2
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatDynamic__3 _3
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }


         public Network_Root.IArgType_IpNatDynamic__0 dir
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatDynamic__1 orig
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatDynamic__2 acl
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatDynamic__3 pool
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpNatDynamic__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }

         public override int Arity { get { return 4; } }
         public override object Symbol { get { return "IpNatDynamic"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        case 2:
                           return _2_val;
                        case 3:
                           return _3_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_IpNatPool__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatPool__1 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatPool__2 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatPool__3 :
         ICSharpTerm
      {
      }

      public partial class IpNatPool :
         GroundTerm,
         Network_Root.IArgType_IpNatDynamic__3,
         Network_Root.IArgType__CG_rel_CG_IpNatPool__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_IpNatPool__0 _0_val = MkString("");
         private Network_Root.IArgType_IpNatPool__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
         private Network_Root.IArgType_IpNatPool__2 _2_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
         private Network_Root.IArgType_IpNatPool__3 _3_val = new Network_Root.UI32Range();

         public Network_Root.IArgType_IpNatPool__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpNatPool__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatPool__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpNatPool__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatPool__2 _2
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpNatPool__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatPool__3 _3
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpNatPool__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }


         public Network_Root.IArgType_IpNatPool__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpNatPool__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatPool__1 start
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpNatPool__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatPool__2 end
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpNatPool__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatPool__3 network
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpNatPool__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }

         public override int Arity { get { return 4; } }
         public override object Symbol { get { return "IpNatPool"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        case 2:
                           return _2_val;
                        case 3:
                           return _3_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_IpNatStatic__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatStatic__1 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatStatic__2 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpNatStatic__3 :
         ICSharpTerm
      {
      }

      public partial class IpNatStatic :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_IpNatStatic__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_IpNatStatic__0 _0_val = MkUserCnst(Network_Root.UserCnstKind.INSIDE);
         private Network_Root.IArgType_IpNatStatic__1 _1_val = MkUserCnst(Network_Root.UserCnstKind.DESTINATION);
         private Network_Root.IArgType_IpNatStatic__2 _2_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
         private Network_Root.IArgType_IpNatStatic__3 _3_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_IpNatStatic__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatStatic__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatStatic__2 _2
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatStatic__3 _3
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }


         public Network_Root.IArgType_IpNatStatic__0 dir
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatStatic__1 orig
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatStatic__2 local
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpNatStatic__3 @global
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpNatStatic__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }

         public override int Arity { get { return 4; } }
         public override object Symbol { get { return "IpNatStatic"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        case 2:
                           return _2_val;
                        case 3:
                           return _3_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_IpRoute__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpRoute__1 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpRoute__2 :
         ICSharpTerm
      {
      }

      public interface IArgType_IpRoute__3 :
         ICSharpTerm
      {
      }

      public partial class IpRoute :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_IpRoute__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_IpRoute__0 _0_val = new Network_Root.Router();
         private Network_Root.IArgType_IpRoute__1 _1_val = new Network_Root.UI32Range();
         private Network_Root.IArgType_IpRoute__2 _2_val = new Network_Root.RouterPort();
         private Network_Root.IArgType_IpRoute__3 _3_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_IpRoute__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpRoute__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpRoute__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpRoute__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpRoute__2 _2
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpRoute__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpRoute__3 _3
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpRoute__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }


         public Network_Root.IArgType_IpRoute__0 router
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_IpRoute__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_IpRoute__1 network
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_IpRoute__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public Network_Root.IArgType_IpRoute__2 iface
         {
            get
            {
               Contract.Ensures(_2_val != null);
               return Get<Network_Root.IArgType_IpRoute__2>(() => _2_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _2_val = value; });
            }
         }

         public Network_Root.IArgType_IpRoute__3 nexthop
         {
            get
            {
               Contract.Ensures(_3_val != null);
               return Get<Network_Root.IArgType_IpRoute__3>(() => _3_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _3_val = value; });
            }
         }

         public override int Arity { get { return 4; } }
         public override object Symbol { get { return "IpRoute"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        case 2:
                           return _2_val;
                        case 3:
                           return _3_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_Link__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_Link__1 :
         ICSharpTerm
      {
      }

      public partial class Link :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_Link__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_Link__0 _0_val = new Network_Root.FrameRelayPort();
         private Network_Root.IArgType_Link__1 _1_val = new Network_Root.FrameRelayPort();

         public Network_Root.IArgType_Link__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Link__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_Link__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_Link__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_Link__0 source
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Link__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_Link__1 target
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_Link__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "Link"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface NatDirection :
         ICSharpTerm
      {
      }

      public interface NatOrigin :
         ICSharpTerm
      {
      }

      public interface Natural :
         ICSharpTerm
      {
      }

      public interface NegInteger :
         ICSharpTerm
      {
      }

      public interface IArgType_PN__0 :
         ICSharpTerm
      {
      }

      public partial class PN :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.Types.Any
      {
         private Network_Root.IArgType_PN__0 _0_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_PN__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_PN__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_PN__0 port
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_PN__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "PN"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface Port :
         ICSharpTerm
      {
      }

      public interface IArgType_PortList__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_PortList__1 :
         ICSharpTerm
      {
      }

      public partial class PortList :
         GroundTerm,
         Network_Root.IArgType_PortList__1,
         Network_Root.IArgType__CG_rel_CG_PortList__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_PortList__0 _0_val = new Network_Root.FrameRelayPort();
         private Network_Root.IArgType_PortList__1 _1_val = MkUserCnst(Network_Root.UserCnstKind.NIL);

         public Network_Root.IArgType_PortList__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_PortList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_PortList__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_PortList__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "PortList"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface PosInteger :
         ICSharpTerm
      {
      }

      public interface Real :
         ICSharpTerm
      {
      }

      public interface IArgType_Router__0 :
         ICSharpTerm
      {
      }

      public partial class Router :
         GroundTerm,
         Network_Root.Device,
         Network_Root.IArgType_IpRoute__0,
         Network_Root.IArgType_RouterPort__0,
         Network_Root.IArgType__CG_rel_CG_Router__0,
         Network_Root.IArgType_device__1,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_Router__0 _0_val = MkString("");

         public Network_Root.IArgType_Router__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Router__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_Router__0 name
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Router__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "Router"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_RouterBgp__0 :
         ICSharpTerm
      {
      }

      public partial class RouterBgp :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_RouterBgp__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_RouterBgp__0 _0_val = MkString("");

         public Network_Root.IArgType_RouterBgp__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterBgp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_RouterBgp__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterBgp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "RouterBgp"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_RouterEigrp__0 :
         ICSharpTerm
      {
      }

      public partial class RouterEigrp :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_RouterEigrp__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_RouterEigrp__0 _0_val = MkString("");

         public Network_Root.IArgType_RouterEigrp__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterEigrp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_RouterEigrp__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterEigrp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "RouterEigrp"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_RouterOsfp__0 :
         ICSharpTerm
      {
      }

      public partial class RouterOsfp :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_RouterOsfp__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_RouterOsfp__0 _0_val = MkString("");

         public Network_Root.IArgType_RouterOsfp__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterOsfp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_RouterOsfp__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterOsfp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "RouterOsfp"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_RouterPort__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_RouterPort__1 :
         ICSharpTerm
      {
      }

      public partial class RouterPort :
         GroundTerm,
         Network_Root.IArgType_Interface__1,
         Network_Root.IArgType_IpRoute__2,
         Network_Root.IArgType_Link__0,
         Network_Root.IArgType_Link__1,
         Network_Root.IArgType_PortList__0,
         Network_Root.IArgType__CG_rel_CG_RouterPort__0,
         Network_Root.IArgType_device__0,
         Network_Root.IArgType_edge__0,
         Network_Root.IArgType_edge__1,
         Network_Root.IArgType_path__0,
         Network_Root.IArgType_path__1,
         Network_Root.IArgType_sameLan__0,
         Network_Root.IArgType_sameLan__1,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.Port,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_RouterPort__0 _0_val = new Network_Root.Router();
         private Network_Root.IArgType_RouterPort__1 _1_val = MkString("");

         public Network_Root.IArgType_RouterPort__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_RouterPort__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_RouterPort__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_RouterPort__0 router
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_RouterPort__1 id
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_RouterPort__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "RouterPort"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_RouterRip__0 :
         ICSharpTerm
      {
      }

      public partial class RouterRip :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_RouterRip__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data
      {
         private Network_Root.IArgType_RouterRip__0 _0_val = MkString("");

         public Network_Root.IArgType_RouterRip__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterRip__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_RouterRip__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_RouterRip__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "RouterRip"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface String :
         ICSharpTerm
      {
      }

      public interface IArgType_Switch__0 :
         ICSharpTerm
      {
      }

      public partial class Switch :
         GroundTerm,
         Network_Root.Device,
         Network_Root.IArgType_SwitchPort__0,
         Network_Root.IArgType__CG_rel_CG_Switch__0,
         Network_Root.IArgType_device__1,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_Switch__0 _0_val = MkString("");

         public Network_Root.IArgType_Switch__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Switch__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_Switch__0 name
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_Switch__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "Switch"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_SwitchInterface__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_SwitchInterface__1 :
         ICSharpTerm
      {
      }

      public partial class SwitchInterface :
         GroundTerm,
         Network_Root.IArgType_SwitchPortMode__0,
         Network_Root.IArgType__CG_rel_CG_SwitchInterface__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_SwitchInterface__0 _0_val = MkString("");
         private Network_Root.IArgType_SwitchInterface__1 _1_val = new Network_Root.SwitchPort();

         public Network_Root.IArgType_SwitchInterface__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchInterface__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchInterface__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchInterface__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_SwitchInterface__0 id
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchInterface__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchInterface__1 port
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchInterface__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "SwitchInterface"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_SwitchPort__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_SwitchPort__1 :
         ICSharpTerm
      {
      }

      public partial class SwitchPort :
         GroundTerm,
         Network_Root.IArgType_Link__0,
         Network_Root.IArgType_Link__1,
         Network_Root.IArgType_PortList__0,
         Network_Root.IArgType_SwitchInterface__1,
         Network_Root.IArgType__CG_rel_CG_SwitchPort__0,
         Network_Root.IArgType_device__0,
         Network_Root.IArgType_edge__0,
         Network_Root.IArgType_edge__1,
         Network_Root.IArgType_path__0,
         Network_Root.IArgType_path__1,
         Network_Root.IArgType_sameLan__0,
         Network_Root.IArgType_sameLan__1,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.Port,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_SwitchPort__0 _0_val = new Network_Root.Switch();
         private Network_Root.IArgType_SwitchPort__1 _1_val = MkString("");

         public Network_Root.IArgType_SwitchPort__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchPort__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchPort__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_SwitchPort__0 @switch
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchPort__1 id
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchPort__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "SwitchPort"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_SwitchPortAccess__0 :
         ICSharpTerm
      {
      }

      public partial class SwitchPortAccess :
         GroundTerm,
         Network_Root.IArgType_SwitchPortMode__1,
         Network_Root.IArgType__CG_rel_CG_SwitchPortAccess__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_SwitchPortAccess__0 _0_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_SwitchPortAccess__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPortAccess__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public Network_Root.IArgType_SwitchPortAccess__0 vlan
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPortAccess__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "SwitchPortAccess"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_SwitchPortMode__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_SwitchPortMode__1 :
         ICSharpTerm
      {
      }

      public partial class SwitchPortMode :
         GroundTerm,
         Network_Root.IArgType__CG_rel_CG_SwitchPortMode__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_SwitchPortMode__0 _0_val = new Network_Root.SwitchInterface();
         private Network_Root.IArgType_SwitchPortMode__1 _1_val = new Network_Root.SwitchPortAccess();

         public Network_Root.IArgType_SwitchPortMode__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPortMode__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchPortMode__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchPortMode__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_SwitchPortMode__0 iface
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPortMode__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchPortMode__1 mode
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchPortMode__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "SwitchPortMode"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_SwitchPortTrunk__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_SwitchPortTrunk__1 :
         ICSharpTerm
      {
      }

      public partial class SwitchPortTrunk :
         GroundTerm,
         Network_Root.IArgType_SwitchPortMode__1,
         Network_Root.IArgType__CG_rel_CG_SwitchPortTrunk__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data
      {
         private Network_Root.IArgType_SwitchPortTrunk__0 _0_val = MkUserCnst(Network_Root.UserCnstKind.DOT1Q);
         private Network_Root.IArgType_SwitchPortTrunk__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_SwitchPortTrunk__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPortTrunk__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchPortTrunk__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchPortTrunk__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_SwitchPortTrunk__0 encapsulation
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_SwitchPortTrunk__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_SwitchPortTrunk__1 native
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_SwitchPortTrunk__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "SwitchPortTrunk"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface TcpOptions :
         ICSharpTerm
      {
      }

      public interface TrunkEncapsulation :
         ICSharpTerm
      {
      }

      public interface UI16 :
         ICSharpTerm
      {
      }

      public interface IArgType_UI16Range__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_UI16Range__1 :
         ICSharpTerm
      {
      }

      public partial class UI16Range :
         GroundTerm,
         Network_Root.IArgType_AccessList__4,
         Network_Root.IArgType_AccessList__6,
         Network_Root.IArgType__CG_rel_CG_UI16Range__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data,
         Network_Root.Types.Any,
         Network_Root.Types.Data
      {
         private Network_Root.IArgType_UI16Range__0 _0_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
         private Network_Root.IArgType_UI16Range__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_UI16Range__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_UI16Range__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_UI16Range__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_UI16Range__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_UI16Range__0 left
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_UI16Range__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_UI16Range__1 right
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_UI16Range__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "UI16Range"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface UI32 :
         ICSharpTerm
      {
      }

      public interface IArgType_UI32Range__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_UI32Range__1 :
         ICSharpTerm
      {
      }

      public partial class UI32Range :
         GroundTerm,
         Network_Root.IArgType_AccessList__3,
         Network_Root.IArgType_AccessList__5,
         Network_Root.IArgType_InterfaceIpAddress__2,
         Network_Root.IArgType_IpNatPool__3,
         Network_Root.IArgType_IpRoute__1,
         Network_Root.IArgType__CG_rel_CG_UI32Range__0,
         Network_Root.Network.Any,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Data,
         Network_Root.Types.Any,
         Network_Root.Types.Data
      {
         private Network_Root.IArgType_UI32Range__0 _0_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
         private Network_Root.IArgType_UI32Range__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

         public Network_Root.IArgType_UI32Range__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_UI32Range__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_UI32Range__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_UI32Range__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_UI32Range__0 left
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_UI32Range__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_UI32Range__1 right
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_UI32Range__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "UI32Range"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface UI8 :
         ICSharpTerm
      {
      }

      public interface IArgType_device__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_device__1 :
         ICSharpTerm
      {
      }

      public partial class device :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType_device__0 _0_val = new Network_Root.FrameRelayPort();
         private Network_Root.IArgType_device__1 _1_val = new Network_Root.FrameRelaySwitch();

         public Network_Root.IArgType_device__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_device__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_device__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_device__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_device__0 port
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_device__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_device__1 dev
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_device__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "device"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_edge__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_edge__1 :
         ICSharpTerm
      {
      }

      public partial class edge :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType_edge__0 _0_val = new Network_Root.FrameRelayPort();
         private Network_Root.IArgType_edge__1 _1_val = new Network_Root.FrameRelayPort();

         public Network_Root.IArgType_edge__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_edge__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_edge__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_edge__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "edge"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_path__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_path__1 :
         ICSharpTerm
      {
      }

      public partial class path :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType_path__0 _0_val = new Network_Root.FrameRelayPort();
         private Network_Root.IArgType_path__1 _1_val = new Network_Root.FrameRelayPort();

         public Network_Root.IArgType_path__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_path__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_path__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_path__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_path__0 source
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_path__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_path__1 target
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_path__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "path"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType_sameLan__0 :
         ICSharpTerm
      {
      }

      public interface IArgType_sameLan__1 :
         ICSharpTerm
      {
      }

      public partial class sameLan :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType_sameLan__0 _0_val = new Network_Root.FrameRelayPort();
         private Network_Root.IArgType_sameLan__1 _1_val = new Network_Root.FrameRelayPort();

         public Network_Root.IArgType_sameLan__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_sameLan__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_sameLan__1 _1
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_sameLan__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }


         public Network_Root.IArgType_sameLan__0 x
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType_sameLan__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }

         public Network_Root.IArgType_sameLan__1 y
         {
            get
            {
               Contract.Ensures(_1_val != null);
               return Get<Network_Root.IArgType_sameLan__1>(() => _1_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _1_val = value; });
            }
         }

         public override int Arity { get { return 2; } }
         public override object Symbol { get { return "sameLan"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        case 1:
                           return _1_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_AccessList__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_AccessList :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_AccessList__0 _0_val = new Network_Root.AccessList();

         public Network_Root.IArgType__CG_rel_CG_AccessList__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_AccessList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~AccessList"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_FrameRelayPort__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_FrameRelayPort :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_FrameRelayPort__0 _0_val = new Network_Root.FrameRelayPort();

         public Network_Root.IArgType__CG_rel_CG_FrameRelayPort__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_FrameRelayPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~FrameRelayPort"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_FrameRelaySwitch__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_FrameRelaySwitch :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_FrameRelaySwitch__0 _0_val = new Network_Root.FrameRelaySwitch();

         public Network_Root.IArgType__CG_rel_CG_FrameRelaySwitch__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_FrameRelaySwitch__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~FrameRelaySwitch"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_IgmpOptions__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_IgmpOptions :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_IgmpOptions__0 _0_val = new Network_Root.IgmpOptions();

         public Network_Root.IArgType__CG_rel_CG_IgmpOptions__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_IgmpOptions__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~IgmpOptions"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_Interface__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_Interface :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_Interface__0 _0_val = new Network_Root.Interface();

         public Network_Root.IArgType__CG_rel_CG_Interface__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_Interface__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~Interface"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_InterfaceIpAccessGroup__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_InterfaceIpAccessGroup :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_InterfaceIpAccessGroup__0 _0_val = new Network_Root.InterfaceIpAccessGroup();

         public Network_Root.IArgType__CG_rel_CG_InterfaceIpAccessGroup__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_InterfaceIpAccessGroup__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~InterfaceIpAccessGroup"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_InterfaceIpAddress__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_InterfaceIpAddress :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_InterfaceIpAddress__0 _0_val = new Network_Root.InterfaceIpAddress();

         public Network_Root.IArgType__CG_rel_CG_InterfaceIpAddress__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_InterfaceIpAddress__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~InterfaceIpAddress"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_IpAccessList__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_IpAccessList :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_IpAccessList__0 _0_val = new Network_Root.IpAccessList();

         public Network_Root.IArgType__CG_rel_CG_IpAccessList__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_IpAccessList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~IpAccessList"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_IpNatDynamic__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_IpNatDynamic :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_IpNatDynamic__0 _0_val = new Network_Root.IpNatDynamic();

         public Network_Root.IArgType__CG_rel_CG_IpNatDynamic__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_IpNatDynamic__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~IpNatDynamic"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_IpNatPool__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_IpNatPool :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_IpNatPool__0 _0_val = new Network_Root.IpNatPool();

         public Network_Root.IArgType__CG_rel_CG_IpNatPool__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_IpNatPool__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~IpNatPool"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_IpNatStatic__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_IpNatStatic :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_IpNatStatic__0 _0_val = new Network_Root.IpNatStatic();

         public Network_Root.IArgType__CG_rel_CG_IpNatStatic__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_IpNatStatic__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~IpNatStatic"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_IpRoute__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_IpRoute :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_IpRoute__0 _0_val = new Network_Root.IpRoute();

         public Network_Root.IArgType__CG_rel_CG_IpRoute__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_IpRoute__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~IpRoute"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_Link__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_Link :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_Link__0 _0_val = new Network_Root.Link();

         public Network_Root.IArgType__CG_rel_CG_Link__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_Link__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~Link"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_PortList__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_PortList :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_PortList__0 _0_val = new Network_Root.PortList();

         public Network_Root.IArgType__CG_rel_CG_PortList__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_PortList__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~PortList"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_Router__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_Router :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_Router__0 _0_val = new Network_Root.Router();

         public Network_Root.IArgType__CG_rel_CG_Router__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_Router__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~Router"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_RouterBgp__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_RouterBgp :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_RouterBgp__0 _0_val = new Network_Root.RouterBgp();

         public Network_Root.IArgType__CG_rel_CG_RouterBgp__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_RouterBgp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~RouterBgp"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_RouterEigrp__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_RouterEigrp :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_RouterEigrp__0 _0_val = new Network_Root.RouterEigrp();

         public Network_Root.IArgType__CG_rel_CG_RouterEigrp__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_RouterEigrp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~RouterEigrp"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_RouterOsfp__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_RouterOsfp :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_RouterOsfp__0 _0_val = new Network_Root.RouterOsfp();

         public Network_Root.IArgType__CG_rel_CG_RouterOsfp__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_RouterOsfp__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~RouterOsfp"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_RouterPort__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_RouterPort :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_RouterPort__0 _0_val = new Network_Root.RouterPort();

         public Network_Root.IArgType__CG_rel_CG_RouterPort__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_RouterPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~RouterPort"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_RouterRip__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_RouterRip :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.RouterConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_RouterRip__0 _0_val = new Network_Root.RouterRip();

         public Network_Root.IArgType__CG_rel_CG_RouterRip__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_RouterRip__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~RouterRip"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_Switch__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_Switch :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_Switch__0 _0_val = new Network_Root.Switch();

         public Network_Root.IArgType__CG_rel_CG_Switch__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_Switch__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~Switch"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_SwitchInterface__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_SwitchInterface :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_SwitchInterface__0 _0_val = new Network_Root.SwitchInterface();

         public Network_Root.IArgType__CG_rel_CG_SwitchInterface__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_SwitchInterface__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~SwitchInterface"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_SwitchPort__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_SwitchPort :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_SwitchPort__0 _0_val = new Network_Root.SwitchPort();

         public Network_Root.IArgType__CG_rel_CG_SwitchPort__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_SwitchPort__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~SwitchPort"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_SwitchPortAccess__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_SwitchPortAccess :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_SwitchPortAccess__0 _0_val = new Network_Root.SwitchPortAccess();

         public Network_Root.IArgType__CG_rel_CG_SwitchPortAccess__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_SwitchPortAccess__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~SwitchPortAccess"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_SwitchPortMode__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_SwitchPortMode :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_SwitchPortMode__0 _0_val = new Network_Root.SwitchPortMode();

         public Network_Root.IArgType__CG_rel_CG_SwitchPortMode__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_SwitchPortMode__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~SwitchPortMode"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_SwitchPortTrunk__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_SwitchPortTrunk :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.SwitchConfiguration.Any
      {
         private Network_Root.IArgType__CG_rel_CG_SwitchPortTrunk__0 _0_val = new Network_Root.SwitchPortTrunk();

         public Network_Root.IArgType__CG_rel_CG_SwitchPortTrunk__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_SwitchPortTrunk__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~SwitchPortTrunk"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_UI16Range__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_UI16Range :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.Types.Any
      {
         private Network_Root.IArgType__CG_rel_CG_UI16Range__0 _0_val = new Network_Root.UI16Range();

         public Network_Root.IArgType__CG_rel_CG_UI16Range__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_UI16Range__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~UI16Range"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public interface IArgType__CG_rel_CG_UI32Range__0 :
         ICSharpTerm
      {
      }

      public partial class _CG_rel_CG_UI32Range :
         GroundTerm,
         Network_Root.Network.Any,
         Network_Root.NetworkTopology.Any,
         Network_Root.RouterConfiguration.Any,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.Types.Any
      {
         private Network_Root.IArgType__CG_rel_CG_UI32Range__0 _0_val = new Network_Root.UI32Range();

         public Network_Root.IArgType__CG_rel_CG_UI32Range__0 _0
         {
            get
            {
               Contract.Ensures(_0_val != null);
               return Get<Network_Root.IArgType__CG_rel_CG_UI32Range__0>(() => _0_val);
            }

            set
            {
               Contract.Requires(value != null);
               Set(() => { _0_val = value; });
            }
         }


         public override int Arity { get { return 1; } }
         public override object Symbol { get { return "~rel~UI32Range"; } }
         public override ICSharpTerm this[int index]
         {
            get
            {
               return Get<ICSharpTerm>(
                  () =>
                  {
                     switch (index)
                     {
                        case 0:
                           return _0_val;
                        default:
                           throw new InvalidOperationException();
                     }
                  }
               );
            }
         }
      }

      public partial class RealCnst :
         GroundTerm,
         Network_Root.IArgType_FrameRelayPort__1,
         Network_Root.IArgType_IP__0,
         Network_Root.IArgType_IgmpOptions__0,
         Network_Root.IArgType_InterfaceIpAccessGroup__1,
         Network_Root.IArgType_InterfaceIpAddress__1,
         Network_Root.IArgType_IpAccessList__0,
         Network_Root.IArgType_IpNatPool__0,
         Network_Root.IArgType_IpNatPool__1,
         Network_Root.IArgType_IpNatPool__2,
         Network_Root.IArgType_IpNatStatic__2,
         Network_Root.IArgType_IpNatStatic__3,
         Network_Root.IArgType_IpRoute__3,
         Network_Root.IArgType_PN__0,
         Network_Root.IArgType_RouterBgp__0,
         Network_Root.IArgType_RouterEigrp__0,
         Network_Root.IArgType_RouterOsfp__0,
         Network_Root.IArgType_RouterPort__1,
         Network_Root.IArgType_RouterRip__0,
         Network_Root.IArgType_SwitchInterface__0,
         Network_Root.IArgType_SwitchPortAccess__0,
         Network_Root.IArgType_SwitchPortTrunk__1,
         Network_Root.IArgType_SwitchPort__1,
         Network_Root.IArgType_UI16Range__0,
         Network_Root.IArgType_UI16Range__1,
         Network_Root.IArgType_UI32Range__0,
         Network_Root.IArgType_UI32Range__1,
         Network_Root.ID,
         Network_Root.Integer,
         Network_Root.Natural,
         Network_Root.NegInteger,
         Network_Root.Network.Any,
         Network_Root.Network.Constant,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Constant,
         Network_Root.NetworkTopology.Data,
         Network_Root.PosInteger,
         Network_Root.Real,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Constant,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Constant,
         Network_Root.SwitchConfiguration.Data,
         Network_Root.Types.Any,
         Network_Root.Types.Constant,
         Network_Root.Types.Data,
         Network_Root.UI16,
         Network_Root.UI32,
         Network_Root.UI8
      {
         Rational val = default(Rational);
         public override int Arity { get { return 0; } }
         public override object Symbol { get { return Get<Rational>(() => val); } }
         public override ICSharpTerm this[int index] { get { throw new InvalidOperationException(); } }
         public Rational Value { get { return Get<Rational>(() => val); } set { Set(() => { val = value; }); } }
      }

      public partial class StringCnst :
         GroundTerm,
         Network_Root.IArgType_FrameRelayPort__1,
         Network_Root.IArgType_FrameRelaySwitch__0,
         Network_Root.IArgType_InterfaceIpAccessGroup__1,
         Network_Root.IArgType_Interface__0,
         Network_Root.IArgType_IpAccessList__0,
         Network_Root.IArgType_IpNatPool__0,
         Network_Root.IArgType_RouterBgp__0,
         Network_Root.IArgType_RouterEigrp__0,
         Network_Root.IArgType_RouterOsfp__0,
         Network_Root.IArgType_RouterPort__1,
         Network_Root.IArgType_RouterRip__0,
         Network_Root.IArgType_Router__0,
         Network_Root.IArgType_SwitchInterface__0,
         Network_Root.IArgType_SwitchPort__1,
         Network_Root.IArgType_Switch__0,
         Network_Root.ID,
         Network_Root.Network.Any,
         Network_Root.Network.Constant,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Constant,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Constant,
         Network_Root.RouterConfiguration.Data,
         Network_Root.String,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Constant,
         Network_Root.SwitchConfiguration.Data,
         Network_Root.Types.Any,
         Network_Root.Types.Constant,
         Network_Root.Types.Data
      {
         string val = default(string);
         public override int Arity { get { return 0; } }
         public override object Symbol { get { return Get<string>(() => val); } }
         public override ICSharpTerm this[int index] { get { throw new InvalidOperationException(); } }
         public string Value { get { return Get<string>(() => val); } set { Set(() => { val = value; }); } }
      }

      public partial class Quotation :
         GroundTerm,
         Network_Root.AclAction,
         Network_Root.AclOptions,
         Network_Root.AclProtocol,
         Network_Root.Boolean,
         Network_Root.Device,
         Network_Root.FlowDirection,
         Network_Root.IArgType_AccessList__0,
         Network_Root.IArgType_AccessList__1,
         Network_Root.IArgType_AccessList__2,
         Network_Root.IArgType_AccessList__3,
         Network_Root.IArgType_AccessList__4,
         Network_Root.IArgType_AccessList__5,
         Network_Root.IArgType_AccessList__6,
         Network_Root.IArgType_AccessList__7,
         Network_Root.IArgType_FrameRelayPort__0,
         Network_Root.IArgType_FrameRelayPort__1,
         Network_Root.IArgType_FrameRelaySwitch__0,
         Network_Root.IArgType_IP__0,
         Network_Root.IArgType_IgmpOptions__0,
         Network_Root.IArgType_InterfaceIpAccessGroup__0,
         Network_Root.IArgType_InterfaceIpAccessGroup__1,
         Network_Root.IArgType_InterfaceIpAccessGroup__2,
         Network_Root.IArgType_InterfaceIpAddress__0,
         Network_Root.IArgType_InterfaceIpAddress__1,
         Network_Root.IArgType_InterfaceIpAddress__2,
         Network_Root.IArgType_InterfaceIpNat__0,
         Network_Root.IArgType_InterfaceIpNat__1,
         Network_Root.IArgType_Interface__0,
         Network_Root.IArgType_Interface__1,
         Network_Root.IArgType_IpAccessList__0,
         Network_Root.IArgType_IpNatDynamic__0,
         Network_Root.IArgType_IpNatDynamic__1,
         Network_Root.IArgType_IpNatDynamic__2,
         Network_Root.IArgType_IpNatDynamic__3,
         Network_Root.IArgType_IpNatPool__0,
         Network_Root.IArgType_IpNatPool__1,
         Network_Root.IArgType_IpNatPool__2,
         Network_Root.IArgType_IpNatPool__3,
         Network_Root.IArgType_IpNatStatic__0,
         Network_Root.IArgType_IpNatStatic__1,
         Network_Root.IArgType_IpNatStatic__2,
         Network_Root.IArgType_IpNatStatic__3,
         Network_Root.IArgType_IpRoute__0,
         Network_Root.IArgType_IpRoute__1,
         Network_Root.IArgType_IpRoute__2,
         Network_Root.IArgType_IpRoute__3,
         Network_Root.IArgType_Link__0,
         Network_Root.IArgType_Link__1,
         Network_Root.IArgType_PN__0,
         Network_Root.IArgType_PortList__0,
         Network_Root.IArgType_PortList__1,
         Network_Root.IArgType_RouterBgp__0,
         Network_Root.IArgType_RouterEigrp__0,
         Network_Root.IArgType_RouterOsfp__0,
         Network_Root.IArgType_RouterPort__0,
         Network_Root.IArgType_RouterPort__1,
         Network_Root.IArgType_RouterRip__0,
         Network_Root.IArgType_Router__0,
         Network_Root.IArgType_SwitchInterface__0,
         Network_Root.IArgType_SwitchInterface__1,
         Network_Root.IArgType_SwitchPortAccess__0,
         Network_Root.IArgType_SwitchPortMode__0,
         Network_Root.IArgType_SwitchPortMode__1,
         Network_Root.IArgType_SwitchPortTrunk__0,
         Network_Root.IArgType_SwitchPortTrunk__1,
         Network_Root.IArgType_SwitchPort__0,
         Network_Root.IArgType_SwitchPort__1,
         Network_Root.IArgType_Switch__0,
         Network_Root.IArgType_UI16Range__0,
         Network_Root.IArgType_UI16Range__1,
         Network_Root.IArgType_UI32Range__0,
         Network_Root.IArgType_UI32Range__1,
         Network_Root.IArgType__CG_rel_CG_AccessList__0,
         Network_Root.IArgType__CG_rel_CG_FrameRelayPort__0,
         Network_Root.IArgType__CG_rel_CG_FrameRelaySwitch__0,
         Network_Root.IArgType__CG_rel_CG_IgmpOptions__0,
         Network_Root.IArgType__CG_rel_CG_InterfaceIpAccessGroup__0,
         Network_Root.IArgType__CG_rel_CG_InterfaceIpAddress__0,
         Network_Root.IArgType__CG_rel_CG_Interface__0,
         Network_Root.IArgType__CG_rel_CG_IpAccessList__0,
         Network_Root.IArgType__CG_rel_CG_IpNatDynamic__0,
         Network_Root.IArgType__CG_rel_CG_IpNatPool__0,
         Network_Root.IArgType__CG_rel_CG_IpNatStatic__0,
         Network_Root.IArgType__CG_rel_CG_IpRoute__0,
         Network_Root.IArgType__CG_rel_CG_Link__0,
         Network_Root.IArgType__CG_rel_CG_PortList__0,
         Network_Root.IArgType__CG_rel_CG_RouterBgp__0,
         Network_Root.IArgType__CG_rel_CG_RouterEigrp__0,
         Network_Root.IArgType__CG_rel_CG_RouterOsfp__0,
         Network_Root.IArgType__CG_rel_CG_RouterPort__0,
         Network_Root.IArgType__CG_rel_CG_RouterRip__0,
         Network_Root.IArgType__CG_rel_CG_Router__0,
         Network_Root.IArgType__CG_rel_CG_SwitchInterface__0,
         Network_Root.IArgType__CG_rel_CG_SwitchPortAccess__0,
         Network_Root.IArgType__CG_rel_CG_SwitchPortMode__0,
         Network_Root.IArgType__CG_rel_CG_SwitchPortTrunk__0,
         Network_Root.IArgType__CG_rel_CG_SwitchPort__0,
         Network_Root.IArgType__CG_rel_CG_Switch__0,
         Network_Root.IArgType__CG_rel_CG_UI16Range__0,
         Network_Root.IArgType__CG_rel_CG_UI32Range__0,
         Network_Root.IArgType_device__0,
         Network_Root.IArgType_device__1,
         Network_Root.IArgType_edge__0,
         Network_Root.IArgType_edge__1,
         Network_Root.IArgType_path__0,
         Network_Root.IArgType_path__1,
         Network_Root.IArgType_sameLan__0,
         Network_Root.IArgType_sameLan__1,
         Network_Root.ID,
         Network_Root.IcmpOptions,
         Network_Root.Integer,
         Network_Root.InterfaceStatus,
         Network_Root.NatDirection,
         Network_Root.NatOrigin,
         Network_Root.Natural,
         Network_Root.NegInteger,
         Network_Root.Network.Any,
         Network_Root.Network.Constant,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Constant,
         Network_Root.NetworkTopology.Data,
         Network_Root.Port,
         Network_Root.PosInteger,
         Network_Root.Real,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Constant,
         Network_Root.RouterConfiguration.Data,
         Network_Root.String,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Constant,
         Network_Root.SwitchConfiguration.Data,
         Network_Root.TcpOptions,
         Network_Root.TrunkEncapsulation,
         Network_Root.Types.Any,
         Network_Root.Types.Constant,
         Network_Root.Types.Data,
         Network_Root.UI16,
         Network_Root.UI32,
         Network_Root.UI8
      {
         string val = string.Empty;
         public override int Arity { get { return 0; } }
         public override object Symbol { get { return Get<string>(() => string.Format("`{0}`", val)); } }
         public override ICSharpTerm this[int index] { get { throw new InvalidOperationException(); } }
         public string Value { get { return Get<string>(() => val); } set { Set(() => { val = value; }); } }
      }

      public partial class UserCnst :
         GroundTerm,
         Network_Root.AclAction,
         Network_Root.AclOptions,
         Network_Root.AclProtocol,
         Network_Root.Boolean,
         Network_Root.FlowDirection,
         Network_Root.IArgType_AccessList__1,
         Network_Root.IArgType_AccessList__2,
         Network_Root.IArgType_AccessList__7,
         Network_Root.IArgType_InterfaceIpAccessGroup__2,
         Network_Root.IArgType_InterfaceIpNat__1,
         Network_Root.IArgType_IpNatDynamic__0,
         Network_Root.IArgType_IpNatDynamic__1,
         Network_Root.IArgType_IpNatStatic__0,
         Network_Root.IArgType_IpNatStatic__1,
         Network_Root.IArgType_IpRoute__3,
         Network_Root.IArgType_PortList__1,
         Network_Root.IArgType_SwitchPortTrunk__0,
         Network_Root.IcmpOptions,
         Network_Root.InterfaceStatus,
         Network_Root.NatDirection,
         Network_Root.NatOrigin,
         Network_Root.Network.Any,
         Network_Root.Network.Constant,
         Network_Root.Network.Data,
         Network_Root.NetworkTopology.Any,
         Network_Root.NetworkTopology.Constant,
         Network_Root.NetworkTopology.Data,
         Network_Root.RouterConfiguration.Any,
         Network_Root.RouterConfiguration.Constant,
         Network_Root.RouterConfiguration.Data,
         Network_Root.SwitchConfiguration.Any,
         Network_Root.SwitchConfiguration.Constant,
         Network_Root.SwitchConfiguration.Data,
         Network_Root.TcpOptions,
         Network_Root.TrunkEncapsulation,
         Network_Root.Types.Any,
         Network_Root.Types.Constant,
         Network_Root.Types.Data
      {
         private object val = Network_Root.UserCnstKind.FALSE;
         public override int Arity { get { return 0; } }
         public override object Symbol { get { return Get<object>(() => ToSymbol(val)); } }
         public override ICSharpTerm this[int index] { get { throw new InvalidOperationException(); } }
         public object Value
         {
            get
            {
               return Get<object>(() => val);
            }

            set
            {
               if (!ValidateType(value))
               {
                  throw new InvalidOperationException();
               }

               Set(() => { val = value; });
            }
         }

         private static bool ValidateType(object o)
         {
            if (o == null)
            {
               return true;
            }
            else if (o is Network_Root.UserCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.TypeCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.Network.UserCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.Network.TypeCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.NetworkTopology.UserCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.NetworkTopology.TypeCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.RouterConfiguration.UserCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.RouterConfiguration.TypeCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.SwitchConfiguration.UserCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.SwitchConfiguration.TypeCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.Types.UserCnstKind)
            {
               return true;
            }
            else if (o is Network_Root.Types.TypeCnstKind)
            {
               return true;
            }
            else
            {
               return false;
            }
         }

         private static string ToSymbol(object o)
         {
            if (o == null)
            {
               return null;
            }
            else if (o is Network_Root.UserCnstKind)
            {
               return Network_Root.UserCnstNames[(int)o];
            }
            else if (o is Network_Root.TypeCnstKind)
            {
               return Network_Root.TypeCnstNames[(int)o];
            }
            else if (o is Network_Root.Network.UserCnstKind)
            {
               return Network_Root.Network.UserCnstNames[(int)o];
            }
            else if (o is Network_Root.Network.TypeCnstKind)
            {
               return Network_Root.Network.TypeCnstNames[(int)o];
            }
            else if (o is Network_Root.NetworkTopology.UserCnstKind)
            {
               return Network_Root.NetworkTopology.UserCnstNames[(int)o];
            }
            else if (o is Network_Root.NetworkTopology.TypeCnstKind)
            {
               return Network_Root.NetworkTopology.TypeCnstNames[(int)o];
            }
            else if (o is Network_Root.RouterConfiguration.UserCnstKind)
            {
               return Network_Root.RouterConfiguration.UserCnstNames[(int)o];
            }
            else if (o is Network_Root.RouterConfiguration.TypeCnstKind)
            {
               return Network_Root.RouterConfiguration.TypeCnstNames[(int)o];
            }
            else if (o is Network_Root.SwitchConfiguration.UserCnstKind)
            {
               return Network_Root.SwitchConfiguration.UserCnstNames[(int)o];
            }
            else if (o is Network_Root.SwitchConfiguration.TypeCnstKind)
            {
               return Network_Root.SwitchConfiguration.TypeCnstNames[(int)o];
            }
            else if (o is Network_Root.Types.UserCnstKind)
            {
               return Network_Root.Types.UserCnstNames[(int)o];
            }
            else if (o is Network_Root.Types.TypeCnstKind)
            {
               return Network_Root.Types.TypeCnstNames[(int)o];
            }
            else
            {
               throw new InvalidOperationException();
            }
         }
      }

      public static partial class Network
      {
         public enum UserCnstKind
         {
            conforms,
            notFunctional,
            notInjective,
            notInvTotal,
            notRelational,
            notTotal
         }

         public enum TypeCnstKind
         {
            Any,
            Constant,
            Data
         }

         public static readonly string[] UserCnstNames =
         {
            "Network.conforms",
            "Network.notFunctional",
            "Network.notInjective",
            "Network.notInvTotal",
            "Network.notRelational",
            "Network.notTotal"
         };

         public static readonly string[] TypeCnstNames =
         {
            "Network.#Any",
            "Network.#Constant",
            "Network.#Data"
         };

         public static string Namespace { get { return "Network"; } }
         public interface Any :
            ICSharpTerm
         {
         }

         public interface Constant :
            ICSharpTerm
         {
         }

         public interface Data :
            ICSharpTerm
         {
         }

      }

      public static partial class NetworkTopology
      {
         public enum UserCnstKind
         {
            conforms,
            notFunctional,
            notInjective,
            notInvTotal,
            notRelational,
            notTotal,
            unidirectional,
            _CG_conforms0
         }

         public enum TypeCnstKind
         {
            Any,
            Constant,
            Data
         }

         public static readonly string[] UserCnstNames =
         {
            "NetworkTopology.conforms",
            "NetworkTopology.notFunctional",
            "NetworkTopology.notInjective",
            "NetworkTopology.notInvTotal",
            "NetworkTopology.notRelational",
            "NetworkTopology.notTotal",
            "NetworkTopology.unidirectional",
            "NetworkTopology.~conforms0"
         };

         public static readonly string[] TypeCnstNames =
         {
            "NetworkTopology.#Any",
            "NetworkTopology.#Constant",
            "NetworkTopology.#Data"
         };

         public static string Namespace { get { return "NetworkTopology"; } }
         public interface Any :
            ICSharpTerm
         {
         }

         public interface Constant :
            ICSharpTerm
         {
         }

         public interface Data :
            ICSharpTerm
         {
         }

      }

      public static partial class RouterConfiguration
      {
         public enum UserCnstKind
         {
            conforms,
            duplicateAddress,
            mismatchNetworkAddress,
            notFunctional,
            notInjective,
            notInvTotal,
            notRelational,
            notTotal
         }

         public enum TypeCnstKind
         {
            Any,
            Constant,
            Data
         }

         public static readonly string[] UserCnstNames =
         {
            "RouterConfiguration.conforms",
            "RouterConfiguration.duplicateAddress",
            "RouterConfiguration.mismatchNetworkAddress",
            "RouterConfiguration.notFunctional",
            "RouterConfiguration.notInjective",
            "RouterConfiguration.notInvTotal",
            "RouterConfiguration.notRelational",
            "RouterConfiguration.notTotal"
         };

         public static readonly string[] TypeCnstNames =
         {
            "RouterConfiguration.#Any",
            "RouterConfiguration.#Constant",
            "RouterConfiguration.#Data"
         };

         public static string Namespace { get { return "RouterConfiguration"; } }
         public interface Any :
            ICSharpTerm
         {
         }

         public interface Constant :
            ICSharpTerm
         {
         }

         public interface Data :
            ICSharpTerm
         {
         }

      }

      public static partial class SwitchConfiguration
      {
         public enum UserCnstKind
         {
            conforms,
            mismatchPortMode,
            notFunctional,
            notInjective,
            notInvTotal,
            notRelational,
            notTotal
         }

         public enum TypeCnstKind
         {
            Any,
            Constant,
            Data
         }

         public static readonly string[] UserCnstNames =
         {
            "SwitchConfiguration.conforms",
            "SwitchConfiguration.mismatchPortMode",
            "SwitchConfiguration.notFunctional",
            "SwitchConfiguration.notInjective",
            "SwitchConfiguration.notInvTotal",
            "SwitchConfiguration.notRelational",
            "SwitchConfiguration.notTotal"
         };

         public static readonly string[] TypeCnstNames =
         {
            "SwitchConfiguration.#Any",
            "SwitchConfiguration.#Constant",
            "SwitchConfiguration.#Data"
         };

         public static string Namespace { get { return "SwitchConfiguration"; } }
         public interface Any :
            ICSharpTerm
         {
         }

         public interface Constant :
            ICSharpTerm
         {
         }

         public interface Data :
            ICSharpTerm
         {
         }

      }

      public static partial class Types
      {
         public enum UserCnstKind
         {
            conforms,
            notFunctional,
            notInjective,
            notInvTotal,
            notRelational,
            notTotal
         }

         public enum TypeCnstKind
         {
            Any,
            Constant,
            Data
         }

         public static readonly string[] UserCnstNames =
         {
            "Types.conforms",
            "Types.notFunctional",
            "Types.notInjective",
            "Types.notInvTotal",
            "Types.notRelational",
            "Types.notTotal"
         };

         public static readonly string[] TypeCnstNames =
         {
            "Types.#Any",
            "Types.#Constant",
            "Types.#Data"
         };

         public static string Namespace { get { return "Types"; } }
         public interface Any :
            ICSharpTerm
         {
         }

         public interface Constant :
            ICSharpTerm
         {
         }

         public interface Data :
            ICSharpTerm
         {
         }

      }

   }
}
