//
//  EmptyClass.cs
//
//  Author:
//       Ondrej Rysavy <rysavy@fit.vutbr.cz>
//
//  Copyright (c) 2014 (c) Brno University of Technology
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.

namespace Netifier.FilterConflictChecker
{
	using System;
	using System.IO;
	using System.Linq;
	using System.Collections.Generic;
	using System.Net;
	using System.Net.Sockets;


	using Xunit;
	using Netifier.ConfigurationObjects;
	using Netifier.Parsers;
	using Netifier.DataModels;
	using Netifier.Extensions;

	using Microsoft.FSharp.Core;
	using Microsoft.Formula.API;    
	using Microsoft.Formula.API.Generators;
	using Microsoft.Formula.API.Nodes;
	using Microsoft.Formula.Common.Terms;
	using Microsoft.Formula.Common;



	public class AccessGroup
	{
		public string GroupName { get; set; }
		public IEnumerable<AccessList> Rules { get; set; }
	}
	public class CheckerFactory
	{
		Checker checker;
		public static string theDomainFile = Path.Combine(Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location), "firewall.4ml");
		private CheckerFactory ()
		{
			checker = Checker.Create ("Firewall", theDomainFile);
		}

		public static Checker CreateAclModelChecker(string modelName, IEnumerable<AccessGroup> groups)
		{
			var factory = new CheckerFactory ();
			if (factory == null)
				return null;
			return factory.createAclModelChecker (modelName, groups);
		}
		
		Checker createAclModelChecker(string modelName, IEnumerable<AccessGroup> groups)
		{
			List<ICSharpTerm> facts = new List<ICSharpTerm> ();

			foreach (var group in groups) {
				var s = Firewall_Root.MkFilter (Firewall_Root.MkString (group.GroupName));
				facts.Add (s);
				int priority = 0;
				foreach (var r in group.Rules) {
					var t = Firewall_Root.MkRule (s, 
						       Firewall_Root.MkNumeric (++priority),
						       Firewall_Root.MkUserCnst (MapProtocol (r.Protocol, r.ProtocolOptions)), 
						       Firewall_Root.MkString (MapLoc (r.Source)),  	// srcIp
						       Firewall_Root.MkString (MapPort (r.SourcePort)), 	// srcPn
						       Firewall_Root.MkString (MapLoc (r.Destination)),	// dstIp
						       Firewall_Root.MkString (MapPort (r.DestinationPort)),	// dstPn
						       Firewall_Root.MkUserCnst (r.Action == AclAction.Permit ? Firewall_Root.UserCnstKind.ACCEPT : Firewall_Root.UserCnstKind.DENY));
					facts.Add (t);
				}
			}
			// generate address set:
			foreach (var loc in this.AddressSet) {
				var adrNum = loc.Address.ToUInt32();
				var wcNum = loc.Wildcard.ToUInt32();

				var x = Firewall_Root.MkIP (Firewall_Root.MkString (loc.ToString()),
					        Firewall_Root.MkNumeric (adrNum),
					        Firewall_Root.MkNumeric (adrNum | wcNum));
				facts.Add (x);
			}

			// generate port set:
			foreach (var port in this.PortSet) {
				switch (port.Tag) {
				case AclPortOperator.Tags.Any:
					var anyPn = Firewall_Root.MkPN (Firewall_Root.MkString (port.ToString ()),
						            Firewall_Root.MkNumeric (UInt16.MinValue),
						            Firewall_Root.MkNumeric (UInt16.MaxValue));
					facts.Add (anyPn);
					break;
				case AclPortOperator.Tags.Eq:
					var eq = port as AclPortOperator.Eq;
					var eqPn = Firewall_Root.MkPN (Firewall_Root.MkString (port.ToString ()),
						           Firewall_Root.MkNumeric (eq.Item),
						           Firewall_Root.MkNumeric (eq.Item));
					facts.Add (eqPn);
					break;

				case AclPortOperator.Tags.Neq:
					var neq = port as AclPortOperator.Neq;
					var neqPn1 = Firewall_Root.MkPN (Firewall_Root.MkString (port.ToString ()),
						Firewall_Root.MkNumeric (UInt16.MinValue),
						             Firewall_Root.MkNumeric (neq.Item-1));
					var neqPn2 = Firewall_Root.MkPN (Firewall_Root.MkString (port.ToString ()),
						Firewall_Root.MkNumeric (neq.Item+1),
						Firewall_Root.MkNumeric (UInt16.MaxValue));
					facts.Add (neqPn1);
					facts.Add (neqPn2);
					break;

				case AclPortOperator.Tags.Gt:
					var gt = port as AclPortOperator.Gt;
					var gtPn = Firewall_Root.MkPN (Firewall_Root.MkString (port.ToString ()),
						Firewall_Root.MkNumeric (gt.Item+1),
						Firewall_Root.MkNumeric (UInt16.MaxValue));
					facts.Add (gtPn);
					break;

				case AclPortOperator.Tags.Lt:
					var lt = port as AclPortOperator.Lt;
					var ltPn = Firewall_Root.MkPN (Firewall_Root.MkString (port.ToString ()),
						Firewall_Root.MkNumeric (UInt16.MinValue),
						Firewall_Root.MkNumeric (lt.Item-1));
					facts.Add (ltPn);
					break;

				case AclPortOperator.Tags.Range:
					var range = port as AclPortOperator.Range;
					var rangePn = Firewall_Root.MkPN (Firewall_Root.MkString (port.ToString ()),
						Firewall_Root.MkNumeric (range.Item1),
						Firewall_Root.MkNumeric (range.Item2));
					facts.Add (rangePn);
					break;	

				default:
					break;
				}
			}
				
			checker.CreateAndInstallModel (modelName, facts);
			return checker;
		}
		private Firewall_Root.UserCnstKind MapProtocol(ProtocolType pt,AclProtocolOptions options)
		{
			switch (pt) {
			case ProtocolType.IP:
				return Firewall_Root.UserCnstKind.IPV4;
			case ProtocolType.Icmp:
				return Firewall_Root.UserCnstKind.ICMP;
			case ProtocolType.Igmp:
				return Firewall_Root.UserCnstKind.IGMP;
			case ProtocolType.Tcp:
				if (options.Contains (AclTcpOptions.Established))
					return Firewall_Root.UserCnstKind.TCP_ESTABLISHED;
				else
					return Firewall_Root.UserCnstKind.TCP;
			case ProtocolType.Udp:
				return Firewall_Root.UserCnstKind.UDP;
			}
			return Firewall_Root.UserCnstKind.IPV4; 
		}

		private HashSet<AclLocation> AddressSet = new HashSet<AclLocation>();
		private HashSet<AclPortOperator> PortSet = new HashSet<AclPortOperator>();

		private string MapLoc(AclLocation loc)
		{
			AddressSet.Add (loc);
			return loc.ToString();
		}

		private string MapPort(AclPortOperator port)
		{
			PortSet.Add (port);
			return port.ToString ();
		}

	}



	public class Test
	{
		static string[] AclGroup1 = new string[] { 
			"access-list 199 permit tcp any any established",
			"access-list 199 deny   ip 206.191.241.40 0.0.0.7 any",
			"access-list 199 deny   ip host 206.191.194.42 host 206.191.194.42",
			"access-list 199 permit icmp any any echo",
			"access-list 199 permit icmp any any echo-reply",
			"access-list 199 permit tcp any 206.191.241.40 0.0.0.7 eq www",
			"access-list 199 permit tcp any 206.191.241.40 0.0.0.7 eq smtp",
			"access-list 199 permit tcp any 206.191.241.40 0.0.0.7 eq domain",
			"access-list 199 permit udp any 206.191.241.40 0.0.0.7 eq domain",
			"access-list 199 deny   tcp any 206.191.241.40 0.0.0.7 lt 1024",
			"access-list 199 deny   tcp any 206.191.241.40 0.0.0.7 gt 1023",
			"access-list 199 permit udp any 206.191.241.40 0.0.0.7 gt 1023",
			"access-list 199 deny   udp any 206.191.241.40 0.0.0.7 gt 50000",
			"access-list 199 deny   udp any 206.191.241.40 0.0.0.7 lt 1024"
		};

		public Test()
		{
		}

		[Fact]
		public void EvaluateAclGroup()
		{

			var accessLists = from c in AclGroup1
				select AccessListParser.TryParseString (c);

			var aclGroups = from item in accessLists.Where (x => x != null)
				group item.Value by item.Value.Id into g
				select new AccessGroup(){ GroupName = g.Key, Rules = g };

			var checker = CheckerFactory.CreateAclModelChecker ("test", aclGroups);

			var res = checker.Query ("test", "Ruleset(\"199\")");
			Assert.Equal (LiftedBool.True, res.Item1); 
			res = checker.Query ("test", "Ruleset(199)");
			Assert.Equal (LiftedBool.False, res.Item1); 
			res = checker.Query ("test", "Ruleset(x)");
			Assert.Equal (LiftedBool.True, res.Item1); 
		}
	}

}
