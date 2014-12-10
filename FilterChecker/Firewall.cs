
namespace Netifier.DataModels
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

	public static partial class Firewall_Root
	{
		private static readonly Dictionary<string, Func<ICSharpTerm[], ICSharpTerm>> ConstructorMap = new Dictionary<string, Func<ICSharpTerm[], ICSharpTerm>>();
		static Firewall_Root()
		{
			ConstructorMap.Add("#Action", args => MkUserCnst(Firewall_Root.TypeCnstKind.Action));
			ConstructorMap.Add("#Boolean", args => MkUserCnst(Firewall_Root.TypeCnstKind.Boolean));
			ConstructorMap.Add("#ConflictType", args => MkUserCnst(Firewall_Root.TypeCnstKind.ConflictType));
			ConstructorMap.Add("#D", args => MkUserCnst(Firewall_Root.TypeCnstKind.D));
			ConstructorMap.Add("#Filter", args => MkUserCnst(Firewall_Root.TypeCnstKind.Filter));
			ConstructorMap.Add("#Filter[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Filter_NDEX_0));
			ConstructorMap.Add("#IP", args => MkUserCnst(Firewall_Root.TypeCnstKind.IP));
			ConstructorMap.Add("#IP[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.IP_NDEX_0));
			ConstructorMap.Add("#IP[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.IP_NDEX_1));
			ConstructorMap.Add("#IP[2]", args => MkUserCnst(Firewall_Root.TypeCnstKind.IP_NDEX_2));
			ConstructorMap.Add("#Integer", args => MkUserCnst(Firewall_Root.TypeCnstKind.Integer));
			ConstructorMap.Add("#Natural", args => MkUserCnst(Firewall_Root.TypeCnstKind.Natural));
			ConstructorMap.Add("#NegInteger", args => MkUserCnst(Firewall_Root.TypeCnstKind.NegInteger));
			ConstructorMap.Add("#PN", args => MkUserCnst(Firewall_Root.TypeCnstKind.PN));
			ConstructorMap.Add("#PN[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.PN_NDEX_0));
			ConstructorMap.Add("#PN[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.PN_NDEX_1));
			ConstructorMap.Add("#PN[2]", args => MkUserCnst(Firewall_Root.TypeCnstKind.PN_NDEX_2));
			ConstructorMap.Add("#PT", args => MkUserCnst(Firewall_Root.TypeCnstKind.PT));
			ConstructorMap.Add("#PT[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.PT_NDEX_0));
			ConstructorMap.Add("#PT[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.PT_NDEX_1));
			ConstructorMap.Add("#PT[2]", args => MkUserCnst(Firewall_Root.TypeCnstKind.PT_NDEX_2));
			ConstructorMap.Add("#PosInteger", args => MkUserCnst(Firewall_Root.TypeCnstKind.PosInteger));
			ConstructorMap.Add("#Protocol", args => MkUserCnst(Firewall_Root.TypeCnstKind.Protocol));
			ConstructorMap.Add("#Real", args => MkUserCnst(Firewall_Root.TypeCnstKind.Real));
			ConstructorMap.Add("#Rule", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule));
			ConstructorMap.Add("#Rule[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_0));
			ConstructorMap.Add("#Rule[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_1));
			ConstructorMap.Add("#Rule[2]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_2));
			ConstructorMap.Add("#Rule[3]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_3));
			ConstructorMap.Add("#Rule[4]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_4));
			ConstructorMap.Add("#Rule[5]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_5));
			ConstructorMap.Add("#Rule[6]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_6));
			ConstructorMap.Add("#Rule[7]", args => MkUserCnst(Firewall_Root.TypeCnstKind.Rule_NDEX_7));
			ConstructorMap.Add("#String", args => MkUserCnst(Firewall_Root.TypeCnstKind.String));
			ConstructorMap.Add("#UInt16", args => MkUserCnst(Firewall_Root.TypeCnstKind.UInt16));
			ConstructorMap.Add("#UInt32", args => MkUserCnst(Firewall_Root.TypeCnstKind.UInt32));
			ConstructorMap.Add("#conflict", args => MkUserCnst(Firewall_Root.TypeCnstKind.conflict));
			ConstructorMap.Add("#conflict[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.conflict_NDEX_0));
			ConstructorMap.Add("#conflict[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.conflict_NDEX_1));
			ConstructorMap.Add("#conflict[2]", args => MkUserCnst(Firewall_Root.TypeCnstKind.conflict_NDEX_2));
			ConstructorMap.Add("#conflict[3]", args => MkUserCnst(Firewall_Root.TypeCnstKind.conflict_NDEX_3));
			ConstructorMap.Add("#contains", args => MkUserCnst(Firewall_Root.TypeCnstKind.contains));
			ConstructorMap.Add("#contains[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.contains_NDEX_0));
			ConstructorMap.Add("#contains[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.contains_NDEX_1));
			ConstructorMap.Add("#disjoint", args => MkUserCnst(Firewall_Root.TypeCnstKind.disjoint));
			ConstructorMap.Add("#disjoint[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.disjoint_NDEX_0));
			ConstructorMap.Add("#disjoint[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.disjoint_NDEX_1));
			ConstructorMap.Add("#exact", args => MkUserCnst(Firewall_Root.TypeCnstKind.exact));
			ConstructorMap.Add("#exact[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.exact_NDEX_0));
			ConstructorMap.Add("#exact[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.exact_NDEX_1));
			ConstructorMap.Add("#nodisjoint", args => MkUserCnst(Firewall_Root.TypeCnstKind.nodisjoint));
			ConstructorMap.Add("#nodisjoint[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.nodisjoint_NDEX_0));
			ConstructorMap.Add("#nodisjoint[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.nodisjoint_NDEX_1));
			ConstructorMap.Add("#olap", args => MkUserCnst(Firewall_Root.TypeCnstKind.olap));
			ConstructorMap.Add("#olap[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.olap_NDEX_0));
			ConstructorMap.Add("#olap[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.olap_NDEX_1));
			ConstructorMap.Add("#shadowing", args => MkUserCnst(Firewall_Root.TypeCnstKind.shadowing));
			ConstructorMap.Add("#shadowing[0]", args => MkUserCnst(Firewall_Root.TypeCnstKind.shadowing_NDEX_0));
			ConstructorMap.Add("#shadowing[1]", args => MkUserCnst(Firewall_Root.TypeCnstKind.shadowing_NDEX_1));
			ConstructorMap.Add("#shadowing[2]", args => MkUserCnst(Firewall_Root.TypeCnstKind.shadowing_NDEX_2));
			ConstructorMap.Add("ACCEPT", args => MkUserCnst(Firewall_Root.UserCnstKind.ACCEPT));
			ConstructorMap.Add("CORRELATION", args => MkUserCnst(Firewall_Root.UserCnstKind.CORRELATION));
			ConstructorMap.Add("DENY", args => MkUserCnst(Firewall_Root.UserCnstKind.DENY));
			ConstructorMap.Add("FALSE", args => MkUserCnst(Firewall_Root.UserCnstKind.FALSE));
			ConstructorMap.Add("Filter", args => Firewall_Root.MkFilter((Firewall_Root.IArgType_Filter__0)args[0]));
			ConstructorMap.Add("GENERALIZATION", args => MkUserCnst(Firewall_Root.UserCnstKind.GENERALIZATION));
			ConstructorMap.Add("ICMP", args => MkUserCnst(Firewall_Root.UserCnstKind.ICMP));
			ConstructorMap.Add("ICMP_ECHO", args => MkUserCnst(Firewall_Root.UserCnstKind.ICMP_ECHO));
			ConstructorMap.Add("ICMP_ECHOREPLY", args => MkUserCnst(Firewall_Root.UserCnstKind.ICMP_ECHOREPLY));
			ConstructorMap.Add("IGMP", args => MkUserCnst(Firewall_Root.UserCnstKind.IGMP));
			ConstructorMap.Add("IP", args => Firewall_Root.MkIP((Firewall_Root.IArgType_IP__0)args[0], (Firewall_Root.IArgType_IP__1)args[1], (Firewall_Root.IArgType_IP__2)args[2]));
			ConstructorMap.Add("IPV4", args => MkUserCnst(Firewall_Root.UserCnstKind.IPV4));
			ConstructorMap.Add("PN", args => Firewall_Root.MkPN((Firewall_Root.IArgType_PN__0)args[0], (Firewall_Root.IArgType_PN__1)args[1], (Firewall_Root.IArgType_PN__2)args[2]));
			ConstructorMap.Add("PT", args => Firewall_Root.MkPT((Firewall_Root.IArgType_PT__0)args[0], (Firewall_Root.IArgType_PT__1)args[1], (Firewall_Root.IArgType_PT__2)args[2]));
			ConstructorMap.Add("REDUNDANCY", args => MkUserCnst(Firewall_Root.UserCnstKind.REDUNDANCY));
			ConstructorMap.Add("Rule", args => Firewall_Root.MkRule((Firewall_Root.IArgType_Rule__0)args[0], (Firewall_Root.IArgType_Rule__1)args[1], (Firewall_Root.IArgType_Rule__2)args[2], (Firewall_Root.IArgType_Rule__3)args[3], (Firewall_Root.IArgType_Rule__4)args[4], (Firewall_Root.IArgType_Rule__5)args[5], (Firewall_Root.IArgType_Rule__6)args[6], (Firewall_Root.IArgType_Rule__7)args[7]));
			ConstructorMap.Add("SHADOWING", args => MkUserCnst(Firewall_Root.UserCnstKind.SHADOWING));
			ConstructorMap.Add("TCP", args => MkUserCnst(Firewall_Root.UserCnstKind.TCP));
			ConstructorMap.Add("TCP_ESTABLISHED", args => MkUserCnst(Firewall_Root.UserCnstKind.TCP_ESTABLISHED));
			ConstructorMap.Add("TRUE", args => MkUserCnst(Firewall_Root.UserCnstKind.TRUE));
			ConstructorMap.Add("UDP", args => MkUserCnst(Firewall_Root.UserCnstKind.UDP));
			ConstructorMap.Add("conflict", args => Firewall_Root.Mkconflict((Firewall_Root.IArgType_conflict__0)args[0], (Firewall_Root.IArgType_conflict__1)args[1], (Firewall_Root.IArgType_conflict__2)args[2], (Firewall_Root.IArgType_conflict__3)args[3]));
			ConstructorMap.Add("contains", args => Firewall_Root.Mkcontains((Firewall_Root.IArgType_contains__0)args[0], (Firewall_Root.IArgType_contains__1)args[1]));
			ConstructorMap.Add("disjoint", args => Firewall_Root.Mkdisjoint((Firewall_Root.IArgType_disjoint__0)args[0], (Firewall_Root.IArgType_disjoint__1)args[1]));
			ConstructorMap.Add("exact", args => Firewall_Root.Mkexact((Firewall_Root.IArgType_exact__0)args[0], (Firewall_Root.IArgType_exact__1)args[1]));
			ConstructorMap.Add("nodisjoint", args => Firewall_Root.Mknodisjoint((Firewall_Root.IArgType_nodisjoint__0)args[0], (Firewall_Root.IArgType_nodisjoint__1)args[1]));
			ConstructorMap.Add("olap", args => Firewall_Root.Mkolap((Firewall_Root.IArgType_olap__0)args[0], (Firewall_Root.IArgType_olap__1)args[1]));
			ConstructorMap.Add("shadowing", args => Firewall_Root.Mkshadowing((Firewall_Root.IArgType_shadowing__0)args[0], (Firewall_Root.IArgType_shadowing__1)args[1], (Firewall_Root.IArgType_shadowing__2)args[2]));
			ConstructorMap.Add("~rel~Filter", args => Firewall_Root.Mk_CG_rel_CG_Filter((Firewall_Root.IArgType__CG_rel_CG_Filter__0)args[0]));
			ConstructorMap.Add("~rel~IP", args => Firewall_Root.Mk_CG_rel_CG_IP((Firewall_Root.IArgType__CG_rel_CG_IP__0)args[0]));
			ConstructorMap.Add("~rel~PN", args => Firewall_Root.Mk_CG_rel_CG_PN((Firewall_Root.IArgType__CG_rel_CG_PN__0)args[0]));
			ConstructorMap.Add("~rel~PT", args => Firewall_Root.Mk_CG_rel_CG_PT((Firewall_Root.IArgType__CG_rel_CG_PT__0)args[0]));
			ConstructorMap.Add("~rel~Rule", args => Firewall_Root.Mk_CG_rel_CG_Rule((Firewall_Root.IArgType__CG_rel_CG_Rule__0)args[0]));
			ConstructorMap.Add("Firewall.#Any", args => MkUserCnst(Firewall_Root.Firewall.TypeCnstKind.Any));
			ConstructorMap.Add("Firewall.#Constant", args => MkUserCnst(Firewall_Root.Firewall.TypeCnstKind.Constant));
			ConstructorMap.Add("Firewall.#Data", args => MkUserCnst(Firewall_Root.Firewall.TypeCnstKind.Data));
			ConstructorMap.Add("Firewall.conforms", args => MkUserCnst(Firewall_Root.Firewall.UserCnstKind.conforms));
			ConstructorMap.Add("Firewall.notFunctional", args => MkUserCnst(Firewall_Root.Firewall.UserCnstKind.notFunctional));
			ConstructorMap.Add("Firewall.notInjective", args => MkUserCnst(Firewall_Root.Firewall.UserCnstKind.notInjective));
			ConstructorMap.Add("Firewall.notInvTotal", args => MkUserCnst(Firewall_Root.Firewall.UserCnstKind.notInvTotal));
			ConstructorMap.Add("Firewall.notRelational", args => MkUserCnst(Firewall_Root.Firewall.UserCnstKind.notRelational));
			ConstructorMap.Add("Firewall.notTotal", args => MkUserCnst(Firewall_Root.Firewall.UserCnstKind.notTotal));
		}

		public enum UserCnstKind
		{
			ACCEPT,
			CORRELATION,
			DENY,
			FALSE,
			GENERALIZATION,
			ICMP,
			ICMP_ECHO,
			ICMP_ECHOREPLY,
			IGMP,
			IPV4,
			REDUNDANCY,
			SHADOWING,
			TCP,
			TCP_ESTABLISHED,
			TRUE,
			UDP
		}

		public enum TypeCnstKind
		{
			Action,
			Boolean,
			ConflictType,
			D,
			Filter,
			Filter_NDEX_0,
			IP,
			IP_NDEX_0,
			IP_NDEX_1,
			IP_NDEX_2,
			Integer,
			Natural,
			NegInteger,
			PN,
			PN_NDEX_0,
			PN_NDEX_1,
			PN_NDEX_2,
			PT,
			PT_NDEX_0,
			PT_NDEX_1,
			PT_NDEX_2,
			PosInteger,
			Protocol,
			Real,
			Rule,
			Rule_NDEX_0,
			Rule_NDEX_1,
			Rule_NDEX_2,
			Rule_NDEX_3,
			Rule_NDEX_4,
			Rule_NDEX_5,
			Rule_NDEX_6,
			Rule_NDEX_7,
			String,
			UInt16,
			UInt32,
			conflict,
			conflict_NDEX_0,
			conflict_NDEX_1,
			conflict_NDEX_2,
			conflict_NDEX_3,
			contains,
			contains_NDEX_0,
			contains_NDEX_1,
			disjoint,
			disjoint_NDEX_0,
			disjoint_NDEX_1,
			exact,
			exact_NDEX_0,
			exact_NDEX_1,
			nodisjoint,
			nodisjoint_NDEX_0,
			nodisjoint_NDEX_1,
			olap,
			olap_NDEX_0,
			olap_NDEX_1,
			shadowing,
			shadowing_NDEX_0,
			shadowing_NDEX_1,
			shadowing_NDEX_2
		}

		public static readonly string[] UserCnstNames =
		{
			"ACCEPT",
			"CORRELATION",
			"DENY",
			"FALSE",
			"GENERALIZATION",
			"ICMP",
			"ICMP_ECHO",
			"ICMP_ECHOREPLY",
			"IGMP",
			"IPV4",
			"REDUNDANCY",
			"SHADOWING",
			"TCP",
			"TCP_ESTABLISHED",
			"TRUE",
			"UDP"
		};

		public static readonly string[] TypeCnstNames =
		{
			"#Action",
			"#Boolean",
			"#ConflictType",
			"#D",
			"#Filter",
			"#Filter[0]",
			"#IP",
			"#IP[0]",
			"#IP[1]",
			"#IP[2]",
			"#Integer",
			"#Natural",
			"#NegInteger",
			"#PN",
			"#PN[0]",
			"#PN[1]",
			"#PN[2]",
			"#PT",
			"#PT[0]",
			"#PT[1]",
			"#PT[2]",
			"#PosInteger",
			"#Protocol",
			"#Real",
			"#Rule",
			"#Rule[0]",
			"#Rule[1]",
			"#Rule[2]",
			"#Rule[3]",
			"#Rule[4]",
			"#Rule[5]",
			"#Rule[6]",
			"#Rule[7]",
			"#String",
			"#UInt16",
			"#UInt32",
			"#conflict",
			"#conflict[0]",
			"#conflict[1]",
			"#conflict[2]",
			"#conflict[3]",
			"#contains",
			"#contains[0]",
			"#contains[1]",
			"#disjoint",
			"#disjoint[0]",
			"#disjoint[1]",
			"#exact",
			"#exact[0]",
			"#exact[1]",
			"#nodisjoint",
			"#nodisjoint[0]",
			"#nodisjoint[1]",
			"#olap",
			"#olap[0]",
			"#olap[1]",
			"#shadowing",
			"#shadowing[0]",
			"#shadowing[1]",
			"#shadowing[2]"
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

		public static UserCnst MkUserCnst(Firewall_Root.UserCnstKind val)
		{
			var n = new UserCnst();
			n.Value = val;
			return n;
		}

		public static UserCnst MkUserCnst(Firewall_Root.TypeCnstKind val)
		{
			var n = new UserCnst();
			n.Value = val;
			return n;
		}

		public static UserCnst MkUserCnst(Firewall_Root.Firewall.UserCnstKind val)
		{
			var n = new UserCnst();
			n.Value = val;
			return n;
		}

		public static UserCnst MkUserCnst(Firewall_Root.Firewall.TypeCnstKind val)
		{
			var n = new UserCnst();
			n.Value = val;
			return n;
		}

		public static Firewall_Root.Filter MkFilter(Firewall_Root.IArgType_Filter__0 id = null)
		{
			var _n_ = new Firewall_Root.Filter();
			if (id != null)
			{
				_n_.id = id;
			}

			return _n_;
		}

		public static Firewall_Root.IP MkIP(Firewall_Root.IArgType_IP__0 ip = null, Firewall_Root.IArgType_IP__1 left = null, Firewall_Root.IArgType_IP__2 right = null)
		{
			var _n_ = new Firewall_Root.IP();
			if (ip != null)
			{
				_n_.ip = ip;
			}

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

		public static Firewall_Root.PN MkPN(Firewall_Root.IArgType_PN__0 pn = null, Firewall_Root.IArgType_PN__1 left = null, Firewall_Root.IArgType_PN__2 right = null)
		{
			var _n_ = new Firewall_Root.PN();
			if (pn != null)
			{
				_n_.pn = pn;
			}

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

		public static Firewall_Root.PT MkPT(Firewall_Root.IArgType_PT__0 pt = null, Firewall_Root.IArgType_PT__1 left = null, Firewall_Root.IArgType_PT__2 right = null)
		{
			var _n_ = new Firewall_Root.PT();
			if (pt != null)
			{
				_n_.pt = pt;
			}

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

		public static Firewall_Root.Rule MkRule(Firewall_Root.IArgType_Rule__0 filter = null, Firewall_Root.IArgType_Rule__1 priority = null, Firewall_Root.IArgType_Rule__2 proto = null, Firewall_Root.IArgType_Rule__3 srcIp = null, Firewall_Root.IArgType_Rule__4 srcPn = null, Firewall_Root.IArgType_Rule__5 dstIp = null, Firewall_Root.IArgType_Rule__6 dstPn = null, Firewall_Root.IArgType_Rule__7 action = null)
		{
			var _n_ = new Firewall_Root.Rule();
			if (filter != null)
			{
				_n_.filter = filter;
			}

			if (priority != null)
			{
				_n_.priority = priority;
			}

			if (proto != null)
			{
				_n_.proto = proto;
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

			if (action != null)
			{
				_n_.action = action;
			}

			return _n_;
		}

		public static Firewall_Root.conflict Mkconflict(Firewall_Root.IArgType_conflict__0 f = null, Firewall_Root.IArgType_conflict__1 i = null, Firewall_Root.IArgType_conflict__2 j = null, Firewall_Root.IArgType_conflict__3 t = null)
		{
			var _n_ = new Firewall_Root.conflict();
			if (f != null)
			{
				_n_.f = f;
			}

			if (i != null)
			{
				_n_.i = i;
			}

			if (j != null)
			{
				_n_.j = j;
			}

			if (t != null)
			{
				_n_.t = t;
			}

			return _n_;
		}

		public static Firewall_Root.contains Mkcontains(Firewall_Root.IArgType_contains__0 x = null, Firewall_Root.IArgType_contains__1 y = null)
		{
			var _n_ = new Firewall_Root.contains();
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

		public static Firewall_Root.disjoint Mkdisjoint(Firewall_Root.IArgType_disjoint__0 x = null, Firewall_Root.IArgType_disjoint__1 y = null)
		{
			var _n_ = new Firewall_Root.disjoint();
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

		public static Firewall_Root.exact Mkexact(Firewall_Root.IArgType_exact__0 x = null, Firewall_Root.IArgType_exact__1 y = null)
		{
			var _n_ = new Firewall_Root.exact();
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

		public static Firewall_Root.nodisjoint Mknodisjoint(Firewall_Root.IArgType_nodisjoint__0 x = null, Firewall_Root.IArgType_nodisjoint__1 y = null)
		{
			var _n_ = new Firewall_Root.nodisjoint();
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

		public static Firewall_Root.olap Mkolap(Firewall_Root.IArgType_olap__0 x = null, Firewall_Root.IArgType_olap__1 y = null)
		{
			var _n_ = new Firewall_Root.olap();
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

		public static Firewall_Root.shadowing Mkshadowing(Firewall_Root.IArgType_shadowing__0 f = null, Firewall_Root.IArgType_shadowing__1 p = null, Firewall_Root.IArgType_shadowing__2 q = null)
		{
			var _n_ = new Firewall_Root.shadowing();
			if (f != null)
			{
				_n_.f = f;
			}

			if (p != null)
			{
				_n_.p = p;
			}

			if (q != null)
			{
				_n_.q = q;
			}

			return _n_;
		}

		public static Firewall_Root._CG_rel_CG_Filter Mk_CG_rel_CG_Filter(Firewall_Root.IArgType__CG_rel_CG_Filter__0 arg_0 = null)
		{
			var _n_ = new Firewall_Root._CG_rel_CG_Filter();
			if (arg_0 != null)
			{
				_n_._0 = arg_0;
			}

			return _n_;
		}

		public static Firewall_Root._CG_rel_CG_IP Mk_CG_rel_CG_IP(Firewall_Root.IArgType__CG_rel_CG_IP__0 arg_0 = null)
		{
			var _n_ = new Firewall_Root._CG_rel_CG_IP();
			if (arg_0 != null)
			{
				_n_._0 = arg_0;
			}

			return _n_;
		}

		public static Firewall_Root._CG_rel_CG_PN Mk_CG_rel_CG_PN(Firewall_Root.IArgType__CG_rel_CG_PN__0 arg_0 = null)
		{
			var _n_ = new Firewall_Root._CG_rel_CG_PN();
			if (arg_0 != null)
			{
				_n_._0 = arg_0;
			}

			return _n_;
		}

		public static Firewall_Root._CG_rel_CG_PT Mk_CG_rel_CG_PT(Firewall_Root.IArgType__CG_rel_CG_PT__0 arg_0 = null)
		{
			var _n_ = new Firewall_Root._CG_rel_CG_PT();
			if (arg_0 != null)
			{
				_n_._0 = arg_0;
			}

			return _n_;
		}

		public static Firewall_Root._CG_rel_CG_Rule Mk_CG_rel_CG_Rule(Firewall_Root.IArgType__CG_rel_CG_Rule__0 arg_0 = null)
		{
			var _n_ = new Firewall_Root._CG_rel_CG_Rule();
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

		public interface Action :
		ICSharpTerm
		{
		}

		public interface Boolean :
		ICSharpTerm
		{
		}

		public interface ConflictType :
		ICSharpTerm
		{
		}

		public interface D :
		ICSharpTerm
		{
		}

		public interface IArgType_Filter__0 :
		ICSharpTerm
		{
		}

		public partial class Filter :
		GroundTerm,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType_Rule__0,
		Firewall_Root.IArgType__CG_rel_CG_Filter__0,
		Firewall_Root.IArgType_conflict__0,
		Firewall_Root.IArgType_shadowing__0
		{
			private Firewall_Root.IArgType_Filter__0 _0_val = MkString("");

			public Firewall_Root.IArgType_Filter__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_Filter__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}


			public Firewall_Root.IArgType_Filter__0 id
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_Filter__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public override int Arity { get { return 1; } }
			public override object Symbol { get { return "Filter"; } }
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

		public interface IArgType_IP__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_IP__1 :
		ICSharpTerm
		{
		}

		public interface IArgType_IP__2 :
		ICSharpTerm
		{
		}

		public partial class IP :
		GroundTerm,
		Firewall_Root.D,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType__CG_rel_CG_IP__0,
		Firewall_Root.IArgType_contains__0,
		Firewall_Root.IArgType_contains__1,
		Firewall_Root.IArgType_disjoint__0,
		Firewall_Root.IArgType_disjoint__1,
		Firewall_Root.IArgType_exact__0,
		Firewall_Root.IArgType_exact__1,
		Firewall_Root.IArgType_nodisjoint__0,
		Firewall_Root.IArgType_nodisjoint__1,
		Firewall_Root.IArgType_olap__0,
		Firewall_Root.IArgType_olap__1
		{
			private Firewall_Root.IArgType_IP__0 _0_val = MkString("");
			private Firewall_Root.IArgType_IP__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
			private Firewall_Root.IArgType_IP__2 _2_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

			public Firewall_Root.IArgType_IP__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_IP__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_IP__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_IP__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_IP__2 _2
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_IP__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}


			public Firewall_Root.IArgType_IP__0 ip
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_IP__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_IP__1 left
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_IP__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_IP__2 right
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_IP__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public override int Arity { get { return 3; } }
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

		public interface Integer :
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

		public interface IArgType_PN__1 :
		ICSharpTerm
		{
		}

		public interface IArgType_PN__2 :
		ICSharpTerm
		{
		}

		public partial class PN :
		GroundTerm,
		Firewall_Root.D,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType__CG_rel_CG_PN__0,
		Firewall_Root.IArgType_contains__0,
		Firewall_Root.IArgType_contains__1,
		Firewall_Root.IArgType_disjoint__0,
		Firewall_Root.IArgType_disjoint__1,
		Firewall_Root.IArgType_exact__0,
		Firewall_Root.IArgType_exact__1,
		Firewall_Root.IArgType_nodisjoint__0,
		Firewall_Root.IArgType_nodisjoint__1,
		Firewall_Root.IArgType_olap__0,
		Firewall_Root.IArgType_olap__1
		{
			private Firewall_Root.IArgType_PN__0 _0_val = MkString("");
			private Firewall_Root.IArgType_PN__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
			private Firewall_Root.IArgType_PN__2 _2_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

			public Firewall_Root.IArgType_PN__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_PN__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_PN__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_PN__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_PN__2 _2
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_PN__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}


			public Firewall_Root.IArgType_PN__0 pn
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_PN__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_PN__1 left
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_PN__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_PN__2 right
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_PN__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public override int Arity { get { return 3; } }
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

		public interface IArgType_PT__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_PT__1 :
		ICSharpTerm
		{
		}

		public interface IArgType_PT__2 :
		ICSharpTerm
		{
		}

		public partial class PT :
		GroundTerm,
		Firewall_Root.D,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType__CG_rel_CG_PT__0,
		Firewall_Root.IArgType_contains__0,
		Firewall_Root.IArgType_contains__1,
		Firewall_Root.IArgType_disjoint__0,
		Firewall_Root.IArgType_disjoint__1,
		Firewall_Root.IArgType_exact__0,
		Firewall_Root.IArgType_exact__1,
		Firewall_Root.IArgType_nodisjoint__0,
		Firewall_Root.IArgType_nodisjoint__1,
		Firewall_Root.IArgType_olap__0,
		Firewall_Root.IArgType_olap__1
		{
			private Firewall_Root.IArgType_PT__0 _0_val = MkUserCnst(Firewall_Root.UserCnstKind.IPV4);
			private Firewall_Root.IArgType_PT__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
			private Firewall_Root.IArgType_PT__2 _2_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));

			public Firewall_Root.IArgType_PT__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_PT__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_PT__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_PT__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_PT__2 _2
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_PT__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}


			public Firewall_Root.IArgType_PT__0 pt
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_PT__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_PT__1 left
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_PT__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_PT__2 right
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_PT__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public override int Arity { get { return 3; } }
			public override object Symbol { get { return "PT"; } }
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

		public interface PosInteger :
		ICSharpTerm
		{
		}

		public interface Protocol :
		ICSharpTerm
		{
		}

		public interface Real :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__1 :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__2 :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__3 :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__4 :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__5 :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__6 :
		ICSharpTerm
		{
		}

		public interface IArgType_Rule__7 :
		ICSharpTerm
		{
		}

		public partial class Rule :
		GroundTerm,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType__CG_rel_CG_Rule__0,
		Firewall_Root.IArgType_shadowing__1,
		Firewall_Root.IArgType_shadowing__2
		{
			private Firewall_Root.IArgType_Rule__0 _0_val = new Firewall_Root.Filter();
			private Firewall_Root.IArgType_Rule__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
			private Firewall_Root.IArgType_Rule__2 _2_val = MkUserCnst(Firewall_Root.UserCnstKind.IPV4);
			private Firewall_Root.IArgType_Rule__3 _3_val = MkString("");
			private Firewall_Root.IArgType_Rule__4 _4_val = MkString("");
			private Firewall_Root.IArgType_Rule__5 _5_val = MkString("");
			private Firewall_Root.IArgType_Rule__6 _6_val = MkString("");
			private Firewall_Root.IArgType_Rule__7 _7_val = MkUserCnst(Firewall_Root.UserCnstKind.ACCEPT);

			public Firewall_Root.IArgType_Rule__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_Rule__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_Rule__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__2 _2
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_Rule__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__3 _3
			{
				get
				{
					Contract.Ensures(_3_val != null);
					return Get<Firewall_Root.IArgType_Rule__3>(() => _3_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _3_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__4 _4
			{
				get
				{
					Contract.Ensures(_4_val != null);
					return Get<Firewall_Root.IArgType_Rule__4>(() => _4_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _4_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__5 _5
			{
				get
				{
					Contract.Ensures(_5_val != null);
					return Get<Firewall_Root.IArgType_Rule__5>(() => _5_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _5_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__6 _6
			{
				get
				{
					Contract.Ensures(_6_val != null);
					return Get<Firewall_Root.IArgType_Rule__6>(() => _6_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _6_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__7 _7
			{
				get
				{
					Contract.Ensures(_7_val != null);
					return Get<Firewall_Root.IArgType_Rule__7>(() => _7_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _7_val = value; });
				}
			}


			public Firewall_Root.IArgType_Rule__0 filter
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_Rule__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__1 priority
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_Rule__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__2 proto
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_Rule__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__3 srcIp
			{
				get
				{
					Contract.Ensures(_3_val != null);
					return Get<Firewall_Root.IArgType_Rule__3>(() => _3_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _3_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__4 srcPn
			{
				get
				{
					Contract.Ensures(_4_val != null);
					return Get<Firewall_Root.IArgType_Rule__4>(() => _4_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _4_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__5 dstIp
			{
				get
				{
					Contract.Ensures(_5_val != null);
					return Get<Firewall_Root.IArgType_Rule__5>(() => _5_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _5_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__6 dstPn
			{
				get
				{
					Contract.Ensures(_6_val != null);
					return Get<Firewall_Root.IArgType_Rule__6>(() => _6_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _6_val = value; });
				}
			}

			public Firewall_Root.IArgType_Rule__7 action
			{
				get
				{
					Contract.Ensures(_7_val != null);
					return Get<Firewall_Root.IArgType_Rule__7>(() => _7_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _7_val = value; });
				}
			}

			public override int Arity { get { return 8; } }
			public override object Symbol { get { return "Rule"; } }
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

		public interface String :
		ICSharpTerm
		{
		}

		public interface UInt16 :
		ICSharpTerm
		{
		}

		public interface UInt32 :
		ICSharpTerm
		{
		}

		public interface IArgType_conflict__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_conflict__1 :
		ICSharpTerm
		{
		}

		public interface IArgType_conflict__2 :
		ICSharpTerm
		{
		}

		public interface IArgType_conflict__3 :
		ICSharpTerm
		{
		}

		public partial class conflict :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType_conflict__0 _0_val = new Firewall_Root.Filter();
			private Firewall_Root.IArgType_conflict__1 _1_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
			private Firewall_Root.IArgType_conflict__2 _2_val = MkNumeric(new Rational(BigInteger.Parse("0"), BigInteger.Parse("1")));
			private Firewall_Root.IArgType_conflict__3 _3_val = MkUserCnst(Firewall_Root.UserCnstKind.SHADOWING);

			public Firewall_Root.IArgType_conflict__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_conflict__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_conflict__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_conflict__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_conflict__2 _2
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_conflict__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public Firewall_Root.IArgType_conflict__3 _3
			{
				get
				{
					Contract.Ensures(_3_val != null);
					return Get<Firewall_Root.IArgType_conflict__3>(() => _3_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _3_val = value; });
				}
			}


			public Firewall_Root.IArgType_conflict__0 f
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_conflict__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_conflict__1 i
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_conflict__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_conflict__2 j
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_conflict__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public Firewall_Root.IArgType_conflict__3 t
			{
				get
				{
					Contract.Ensures(_3_val != null);
					return Get<Firewall_Root.IArgType_conflict__3>(() => _3_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _3_val = value; });
				}
			}

			public override int Arity { get { return 4; } }
			public override object Symbol { get { return "conflict"; } }
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

		public interface IArgType_contains__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_contains__1 :
		ICSharpTerm
		{
		}

		public partial class contains :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType_contains__0 _0_val = new Firewall_Root.IP();
			private Firewall_Root.IArgType_contains__1 _1_val = new Firewall_Root.IP();

			public Firewall_Root.IArgType_contains__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_contains__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_contains__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_contains__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}


			public Firewall_Root.IArgType_contains__0 x
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_contains__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_contains__1 y
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_contains__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public override int Arity { get { return 2; } }
			public override object Symbol { get { return "contains"; } }
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

		public interface IArgType_disjoint__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_disjoint__1 :
		ICSharpTerm
		{
		}

		public partial class disjoint :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType_disjoint__0 _0_val = new Firewall_Root.IP();
			private Firewall_Root.IArgType_disjoint__1 _1_val = new Firewall_Root.IP();

			public Firewall_Root.IArgType_disjoint__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_disjoint__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_disjoint__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_disjoint__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}


			public Firewall_Root.IArgType_disjoint__0 x
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_disjoint__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_disjoint__1 y
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_disjoint__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public override int Arity { get { return 2; } }
			public override object Symbol { get { return "disjoint"; } }
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

		public interface IArgType_exact__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_exact__1 :
		ICSharpTerm
		{
		}

		public partial class exact :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType_exact__0 _0_val = new Firewall_Root.IP();
			private Firewall_Root.IArgType_exact__1 _1_val = new Firewall_Root.IP();

			public Firewall_Root.IArgType_exact__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_exact__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_exact__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_exact__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}


			public Firewall_Root.IArgType_exact__0 x
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_exact__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_exact__1 y
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_exact__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public override int Arity { get { return 2; } }
			public override object Symbol { get { return "exact"; } }
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

		public interface IArgType_nodisjoint__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_nodisjoint__1 :
		ICSharpTerm
		{
		}

		public partial class nodisjoint :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType_nodisjoint__0 _0_val = new Firewall_Root.IP();
			private Firewall_Root.IArgType_nodisjoint__1 _1_val = new Firewall_Root.IP();

			public Firewall_Root.IArgType_nodisjoint__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_nodisjoint__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_nodisjoint__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_nodisjoint__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}


			public Firewall_Root.IArgType_nodisjoint__0 x
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_nodisjoint__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_nodisjoint__1 y
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_nodisjoint__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public override int Arity { get { return 2; } }
			public override object Symbol { get { return "nodisjoint"; } }
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

		public interface IArgType_olap__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_olap__1 :
		ICSharpTerm
		{
		}

		public partial class olap :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType_olap__0 _0_val = new Firewall_Root.IP();
			private Firewall_Root.IArgType_olap__1 _1_val = new Firewall_Root.IP();

			public Firewall_Root.IArgType_olap__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_olap__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_olap__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_olap__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}


			public Firewall_Root.IArgType_olap__0 x
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_olap__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_olap__1 y
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_olap__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public override int Arity { get { return 2; } }
			public override object Symbol { get { return "olap"; } }
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

		public interface IArgType_shadowing__0 :
		ICSharpTerm
		{
		}

		public interface IArgType_shadowing__1 :
		ICSharpTerm
		{
		}

		public interface IArgType_shadowing__2 :
		ICSharpTerm
		{
		}

		public partial class shadowing :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType_shadowing__0 _0_val = new Firewall_Root.Filter();
			private Firewall_Root.IArgType_shadowing__1 _1_val = new Firewall_Root.Rule();
			private Firewall_Root.IArgType_shadowing__2 _2_val = new Firewall_Root.Rule();

			public Firewall_Root.IArgType_shadowing__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_shadowing__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_shadowing__1 _1
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_shadowing__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_shadowing__2 _2
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_shadowing__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}


			public Firewall_Root.IArgType_shadowing__0 f
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType_shadowing__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}

			public Firewall_Root.IArgType_shadowing__1 p
			{
				get
				{
					Contract.Ensures(_1_val != null);
					return Get<Firewall_Root.IArgType_shadowing__1>(() => _1_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _1_val = value; });
				}
			}

			public Firewall_Root.IArgType_shadowing__2 q
			{
				get
				{
					Contract.Ensures(_2_val != null);
					return Get<Firewall_Root.IArgType_shadowing__2>(() => _2_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _2_val = value; });
				}
			}

			public override int Arity { get { return 3; } }
			public override object Symbol { get { return "shadowing"; } }
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

		public interface IArgType__CG_rel_CG_Filter__0 :
		ICSharpTerm
		{
		}

		public partial class _CG_rel_CG_Filter :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType__CG_rel_CG_Filter__0 _0_val = new Firewall_Root.Filter();

			public Firewall_Root.IArgType__CG_rel_CG_Filter__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType__CG_rel_CG_Filter__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}


			public override int Arity { get { return 1; } }
			public override object Symbol { get { return "~rel~Filter"; } }
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

		public interface IArgType__CG_rel_CG_IP__0 :
		ICSharpTerm
		{
		}

		public partial class _CG_rel_CG_IP :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType__CG_rel_CG_IP__0 _0_val = new Firewall_Root.IP();

			public Firewall_Root.IArgType__CG_rel_CG_IP__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType__CG_rel_CG_IP__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}


			public override int Arity { get { return 1; } }
			public override object Symbol { get { return "~rel~IP"; } }
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

		public interface IArgType__CG_rel_CG_PN__0 :
		ICSharpTerm
		{
		}

		public partial class _CG_rel_CG_PN :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType__CG_rel_CG_PN__0 _0_val = new Firewall_Root.PN();

			public Firewall_Root.IArgType__CG_rel_CG_PN__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType__CG_rel_CG_PN__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}


			public override int Arity { get { return 1; } }
			public override object Symbol { get { return "~rel~PN"; } }
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

		public interface IArgType__CG_rel_CG_PT__0 :
		ICSharpTerm
		{
		}

		public partial class _CG_rel_CG_PT :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType__CG_rel_CG_PT__0 _0_val = new Firewall_Root.PT();

			public Firewall_Root.IArgType__CG_rel_CG_PT__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType__CG_rel_CG_PT__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}


			public override int Arity { get { return 1; } }
			public override object Symbol { get { return "~rel~PT"; } }
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

		public interface IArgType__CG_rel_CG_Rule__0 :
		ICSharpTerm
		{
		}

		public partial class _CG_rel_CG_Rule :
		GroundTerm,
		Firewall_Root.Firewall.Any
		{
			private Firewall_Root.IArgType__CG_rel_CG_Rule__0 _0_val = new Firewall_Root.Rule();

			public Firewall_Root.IArgType__CG_rel_CG_Rule__0 _0
			{
				get
				{
					Contract.Ensures(_0_val != null);
					return Get<Firewall_Root.IArgType__CG_rel_CG_Rule__0>(() => _0_val);
				}

				set
				{
					Contract.Requires(value != null);
					Set(() => { _0_val = value; });
				}
			}


			public override int Arity { get { return 1; } }
			public override object Symbol { get { return "~rel~Rule"; } }
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
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Constant,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType_Filter__0,
		Firewall_Root.IArgType_IP__1,
		Firewall_Root.IArgType_IP__2,
		Firewall_Root.IArgType_PN__1,
		Firewall_Root.IArgType_PN__2,
		Firewall_Root.IArgType_PT__1,
		Firewall_Root.IArgType_PT__2,
		Firewall_Root.IArgType_Rule__1,
		Firewall_Root.IArgType_conflict__1,
		Firewall_Root.IArgType_conflict__2,
		Firewall_Root.Integer,
		Firewall_Root.Natural,
		Firewall_Root.NegInteger,
		Firewall_Root.PosInteger,
		Firewall_Root.Real,
		Firewall_Root.UInt16,
		Firewall_Root.UInt32
		{
			Rational val = default(Rational);
			public override int Arity { get { return 0; } }
			public override object Symbol { get { return Get<Rational>(() => val); } }
			public override ICSharpTerm this[int index] { get { throw new InvalidOperationException(); } }
			public Rational Value { get { return Get<Rational>(() => val); } set { Set(() => { val = value; }); } }
		}

		public partial class StringCnst :
		GroundTerm,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Constant,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType_Filter__0,
		Firewall_Root.IArgType_IP__0,
		Firewall_Root.IArgType_PN__0,
		Firewall_Root.IArgType_Rule__3,
		Firewall_Root.IArgType_Rule__4,
		Firewall_Root.IArgType_Rule__5,
		Firewall_Root.IArgType_Rule__6,
		Firewall_Root.String
		{
			string val = default(string);
			public override int Arity { get { return 0; } }
			public override object Symbol { get { return Get<string>(() => val); } }
			public override ICSharpTerm this[int index] { get { throw new InvalidOperationException(); } }
			public string Value { get { return Get<string>(() => val); } set { Set(() => { val = value; }); } }
		}

		public partial class Quotation :
		GroundTerm,
		Firewall_Root.Action,
		Firewall_Root.Boolean,
		Firewall_Root.ConflictType,
		Firewall_Root.D,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Constant,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType_Filter__0,
		Firewall_Root.IArgType_IP__0,
		Firewall_Root.IArgType_IP__1,
		Firewall_Root.IArgType_IP__2,
		Firewall_Root.IArgType_PN__0,
		Firewall_Root.IArgType_PN__1,
		Firewall_Root.IArgType_PN__2,
		Firewall_Root.IArgType_PT__0,
		Firewall_Root.IArgType_PT__1,
		Firewall_Root.IArgType_PT__2,
		Firewall_Root.IArgType_Rule__0,
		Firewall_Root.IArgType_Rule__1,
		Firewall_Root.IArgType_Rule__2,
		Firewall_Root.IArgType_Rule__3,
		Firewall_Root.IArgType_Rule__4,
		Firewall_Root.IArgType_Rule__5,
		Firewall_Root.IArgType_Rule__6,
		Firewall_Root.IArgType_Rule__7,
		Firewall_Root.IArgType__CG_rel_CG_Filter__0,
		Firewall_Root.IArgType__CG_rel_CG_IP__0,
		Firewall_Root.IArgType__CG_rel_CG_PN__0,
		Firewall_Root.IArgType__CG_rel_CG_PT__0,
		Firewall_Root.IArgType__CG_rel_CG_Rule__0,
		Firewall_Root.IArgType_conflict__0,
		Firewall_Root.IArgType_conflict__1,
		Firewall_Root.IArgType_conflict__2,
		Firewall_Root.IArgType_conflict__3,
		Firewall_Root.IArgType_contains__0,
		Firewall_Root.IArgType_contains__1,
		Firewall_Root.IArgType_disjoint__0,
		Firewall_Root.IArgType_disjoint__1,
		Firewall_Root.IArgType_exact__0,
		Firewall_Root.IArgType_exact__1,
		Firewall_Root.IArgType_nodisjoint__0,
		Firewall_Root.IArgType_nodisjoint__1,
		Firewall_Root.IArgType_olap__0,
		Firewall_Root.IArgType_olap__1,
		Firewall_Root.IArgType_shadowing__0,
		Firewall_Root.IArgType_shadowing__1,
		Firewall_Root.IArgType_shadowing__2,
		Firewall_Root.Integer,
		Firewall_Root.Natural,
		Firewall_Root.NegInteger,
		Firewall_Root.PosInteger,
		Firewall_Root.Protocol,
		Firewall_Root.Real,
		Firewall_Root.String,
		Firewall_Root.UInt16,
		Firewall_Root.UInt32
		{
			string val = string.Empty;
			public override int Arity { get { return 0; } }
			public override object Symbol { get { return Get<string>(() => string.Format("`{0}`", val)); } }
			public override ICSharpTerm this[int index] { get { throw new InvalidOperationException(); } }
			public string Value { get { return Get<string>(() => val); } set { Set(() => { val = value; }); } }
		}

		public partial class UserCnst :
		GroundTerm,
		Firewall_Root.Action,
		Firewall_Root.Boolean,
		Firewall_Root.ConflictType,
		Firewall_Root.Firewall.Any,
		Firewall_Root.Firewall.Constant,
		Firewall_Root.Firewall.Data,
		Firewall_Root.IArgType_PT__0,
		Firewall_Root.IArgType_Rule__2,
		Firewall_Root.IArgType_Rule__7,
		Firewall_Root.IArgType_conflict__3,
		Firewall_Root.Protocol
		{
			private object val = Firewall_Root.UserCnstKind.FALSE;
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
				else if (o is Firewall_Root.UserCnstKind)
				{
					return true;
				}
				else if (o is Firewall_Root.TypeCnstKind)
				{
					return true;
				}
				else if (o is Firewall_Root.Firewall.UserCnstKind)
				{
					return true;
				}
				else if (o is Firewall_Root.Firewall.TypeCnstKind)
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
				else if (o is Firewall_Root.UserCnstKind)
				{
					return Firewall_Root.UserCnstNames[(int)o];
				}
				else if (o is Firewall_Root.TypeCnstKind)
				{
					return Firewall_Root.TypeCnstNames[(int)o];
				}
				else if (o is Firewall_Root.Firewall.UserCnstKind)
				{
					return Firewall_Root.Firewall.UserCnstNames[(int)o];
				}
				else if (o is Firewall_Root.Firewall.TypeCnstKind)
				{
					return Firewall_Root.Firewall.TypeCnstNames[(int)o];
				}
				else
				{
					throw new InvalidOperationException();
				}
			}
		}

		public static partial class Firewall
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
				"Firewall.conforms",
				"Firewall.notFunctional",
				"Firewall.notInjective",
				"Firewall.notInvTotal",
				"Firewall.notRelational",
				"Firewall.notTotal"
			};

			public static readonly string[] TypeCnstNames =
			{
				"Firewall.#Any",
				"Firewall.#Constant",
				"Firewall.#Data"
			};

			public static string Namespace { get { return "Firewall"; } }
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
 
