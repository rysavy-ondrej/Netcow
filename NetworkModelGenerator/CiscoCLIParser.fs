//
//  CiscoCLIParser.fs
//
//  Author:
//       Ondrej Rysavy <rysavy@fit.vutbr.cz>
//
//  Copyright (c) 2014 Ondrej Rysavy
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.

namespace Netcow.Parsers
open System
open System.Net
open FParsec
open FParsec.CharParsers
open DataModels


module internal _CliParsers =
    //-------------------------------------------------------------------------------------------------
    // HELPER PARSERS
    //-------------------------------------------------------------------------------------------------
    /// Consumes a line comment. Comments start with "!".
    let blocksep<'a> : Parser<string,'a> = 
        let parser = pstring "!" >>. restOfLine true
        in parser <?> "comment"


    let lspaces<'a> = 
        let lspace = anyOf [' '; '\t' ]
        many lspace

    /// Parses a string constant. 
    let pStringLiteral<'T> : Parser<string,'T> =
        let escape =  anyOf ['\'';'\"';'b';'f';'n';'r';'t';'0']
                      |>> function
                          | 'b' -> "\b"
                          | 'f' -> "\u000C"
                          | 'n' -> "\\n"
                          | 'r' -> "\\r"
                          | 't' -> "\\t"
                          | c   -> string c // every other char is mapped to itself
        let unicodeEscape =
            pstring "u" >>. pipe4 hex hex hex hex (fun h3 h2 h1 h0 ->
                let hex2int c = (int c &&& 15) + (int c >>> 6)*9 // hex char to int
                (hex2int h3)*4096 + (hex2int h2)*256 + (hex2int h1)*16 + hex2int h0
                |> char |> string
            )
        let str1 = between (pstring "\"") (pstring "\"")
                    (stringsSepBy (manySatisfy (fun c -> c <> '"' && c <> '\\'))
                              (pstring "\\" >>. (escape <|> unicodeEscape)))
        let str2 = between (pstring "\'") (pstring "\'")
                    (stringsSepBy (manySatisfy (fun c -> c <> '\'' && c <> '\\'))
                              (pstring "\\" >>. (escape <|> unicodeEscape)))
        in (str1 <|> str2) <?> "string literal in quotes"
       
    let pIdentifier<'T> : Parser<string,'T> = 
        let idStartChar c = Char.IsLetter c 
        let idContinueChar c = Char.IsLetterOrDigit c || c = '/' 
        identifier (new IdentifierOptions(isAsciiIdStart = idStartChar, isAsciiIdContinue=idContinueChar, label="identifier"))

    let argument<'T> = 
        let isValidChar c = not (Char.IsWhiteSpace c || Char.IsControl c) 
        identifier (new IdentifierOptions(isAsciiIdStart=isValidChar, isAsciiIdContinue=isValidChar, label="identifier"))

    /// List of known and supported commmands.
    let toplevelCommands = [ 
        "version",              [] ;
        "service",              [] ;
        "enable secret",        [] ;
        "hostname",             [] ;
        "interface",            ["ip address";"duplex";"speed";"shutdown";"serial";"encapsulation";"frame-relay";"clock rate"] ; 
        "ip route" ,            [] ;
        "ip name-server",       [] ; 
        "line",                 ["login";"logging synchronous"] ; 
        "ip classless",         [] ;

        "boot-start-marker",    [] ;
        "boot-end-marker",      [] ;
        "aaa new-model" ,       [] ;
        "memory-size" ,         [] ;
        "ip cef",               [] ;
        "ip http",              [] ;
        "ip domain",            [] ;
        "control-plane",        [] ;
        "ipv6 cef",             [] ;
        "spanning-tree",        [] ;
        "ip flow-export",       [] ;
        "access-list",          [] ;
    ]

    // access-list 101 deny icmp any 10.1.1.0 0.0.0.255 echo 
    // access-list 101 permit ip any 10.1.1.0 0.0.0.255

    let pCommandGroup<'T> = parse {
        let pTopLevelCmds = List.map (fun (s,r) -> pstring s |>> fun _ -> (s,r)) toplevelCommands
        let! no = opt (pstring "no") .>> lspaces
        let! cmd = choice pTopLevelCmds .>> lspaces
        let! args = manyTill (argument .>> lspaces) newline

        // SPACE [NO] COMMAND ARGS CRLF
        let pCommandItem = parse {
            let! _ = pstring " "
            let! no = opt (pstring "no") .>> lspaces
            let! subcmd = choice (List.map pstring (snd cmd)) .>> lspaces
            let! args = manyTill (argument .>> lspaces) newline
            return { CmdName = subcmd; No=no.IsSome; Args = Array.ofList args; Content= [||] }
        }
        let! content = many pCommandItem 
        return { CmdName = fst cmd; No=no.IsSome; Args = Array.ofList args; Content= Array.ofList content }
    }

    let pConfigFile<'T> = parse {
        let pend = pstring "end" .>> lspaces .>> newline
        let! cmds = parse {
            let! _ = (many blocksep)
            let! items = manyTill (pCommandGroup .>> (many blocksep)) pend
            let! _ = spaces
            return items
        }
        return Array.ofList cmds
    }

    let pIpv4Address<'T> = parse {
        let! oct1 = puint8
        let! _ = pstring "."
        let! oct2 = puint8
        let! _ = pstring "."    
        let! oct3 = puint8
        let! _ = pstring "."    
        let! oct4 = puint8
        return IPAddress([| oct1; oct2 ; oct3 ; oct4 |])
    }

    let pAddressAndWildcard<'T> = 
                   choice [ pstring "any" |>> fun _ -> {Address=IPAddress.Parse("0.0.0.0");Wildcard=IPAddress.Parse("255.255.255.255")}
                            parse { let! _ = pstring "host"
                                    let! _ = lspaces
                                    let! host = pIpv4Address
                                    return host } |>> fun h -> {Address=h; Wildcard =IPAddress.Parse("0.0.0.0")}
                            parse { let! addr = pIpv4Address 
                                    let! _ = lspaces 
                                    let! wcard = pIpv4Address
                                    return {Address=addr;Wildcard=wcard}}
                         ]  
    let portMapping = [
        // TCP Traffic
        "bgp",      "Border Gateway Protocol", (179)
        "chargen",  "Character generator", (19)
        "cmd",      "Remote commands", (514)
        "daytime",  "Daytime", (13)
        "discard",  "Discard", (9)
        "domain",   "Domain Name Service", (53)
        "echo",     "Echo", (7)
        "exec",     "Exec", (512)
        "finger",   "Finger", (79)
        "ftp",      "File Transfer Protocol", (21)
        "ftp-data", "FTP data connections", (20)
        "gopher",   "Gopher", (70)
        "hostname", "NIC host name server", (101)
        "ident",    "Ident Protocol", (113)
        "irc",      "Internet Relay Chat", (194)
        "klogin",   "Kerberos login", (543)
        "kshell",   "Kerberos shell", (544)
        "login",    "Login", (513)
        "lpd",      "Printer service", (515)
        "nntp",     "Network News Transport Protocol", (119)
        "pim-auto-rp", "PIM Auto-RP", (496)
        "pop2",     "Post Office Protocol v2", (109)
        "pop3",     "Post Office Protocol v3", (110)
        "smtp",     "Simple Mail Transport Protocol", (25)
        "sunrpc",   "Sun Remote Procedure Call", (111)
        "Syslog",   "Syslog", (514)
        "Tacacs",   "TAC Access Control System", (49)
        "Talk",     "Talk", (517)
        "telnet",   "Telnet", (23)
        "Time",     "Time", (37)
        "Uucp",     "UNIX-to-UNIX Copy Program", (540)
        "Whois",    "Nicname", (43)
        "www",      "World Wide Web", (80) 
        // UDP Traffic:
        "biff",     "Biff (mail notification, comsat)" , (512)
        "bootpc",   "Bootstrap Protocol (BOOTP) client", (68)
        "bootps",   "Bootstrap Protocol (BOOTP) server", (67)
        "discard",  "Discard", (9)
        "dnsix",    "DNSIX security protocol auditing", (195)
        "domain",   "Domain Name Service (DNS)", (53)
        "echo",     "Echo", (7)
        "isakmp",   "Internet Security Association and Key Management Protocol", (500)
        "mobile-ip",   "Mobile IP registration", (434)
        "nameserver",  "IEN116 name service (obsolete)", (42)
        "netbios-dgm", "NetBIOS datagram service", (138)
        "netbios-ns",  "NetBIOS name service", (137)
        "netbios-ss",  "NetBIOS session service", (139)
        "ntp",      "Network Time Protocol", (123)
        "pim-auto-rp",  "PIM Auto-RP", (496)
        "rip",      "Routing Information Protocol (router, in.routed)", (520)
        "snmp",     "Simple Network Management Protocol", (161)
        "snmptrap", "SNMP Traps", (162)
        "sunrpc",   "Sun Remote Procedure Call", (111)
        "syslog",   "System Logger", (514)
        "tacacs",   "TAC Access Control System", (49)
        "talk",     "Talk", (517)
        "tftp",     "Trivial File Transfer Protocol", (69)
        "time",     "Time", (37)
        "who",      "Who service (rwho)",(513)
        "xdmcp",    "X Display Manager Control Protocol", (177) ]


    // Possible operands include lt (less than), gt (greater than), eq (equal), neq (not equal), and range (inclusive range).
    let pPortValue<'T> =  
        let pp(s,_,v) = pstring s |>> fun _ -> uint16(v)
        puint16 <|> (choice (List.map pp portMapping))
    let pPortOperator<'T> = 
        choice [ pstring "lt" >>. lspaces >>. pPortValue |>> fun x -> AclPortOperator.Lt(x) 
                 pstring "gt" >>. lspaces >>. pPortValue |>> fun x -> AclPortOperator.Gt(x) 
                 pstring "eq" >>. lspaces >>. pPortValue |>> fun x -> AclPortOperator.Eq(x)  
                 pstring "neq" >>. lspaces >>. pPortValue |>> fun x -> AclPortOperator.Neq(x) 
                 pstring "range" >>. lspaces >>. (pPortValue .>> lspaces) .>>. pPortValue |>> fun (x,y) -> AclPortOperator.Range(x,y) 
               ]

    /// Specific parsers:

    // IP:   access-list access-list-number [dynamic dynamic-name [timeout minutes]] {deny | permit} protocol source source-wildcard destination destination-wildcard [precedence precedence] [tos tos] [log | log-input] [time-range time-range-name] [fragments]
    // ICMP: access-list access-list-number [dynamic dynamic-name [timeout minutes]] {deny | permit} icmp source source-wildcard destination destination-wildcard [icmp-type [icmp-code] | icmp-message] [precedence precedence] [tos tos] [log | log-input] [time-range time-range-name] [fragments]             
    // IGMP: access-list access-list-number [dynamic dynamic-name [timeout minutes]] {deny | permit} igmp source source-wildcard destination destination-wildcard [igmp-type] [precedence precedence] [tos tos] [log | log-input] [time-range time-range-name] [fragments]
    // TCP:  access-list access-list-number [dynamic dynamic-name [timeout minutes]] {deny | permit} tcp source source-wildcard [operator [port]] destination destination-wildcard [operator [port]] [established] [precedence precedence] [tos tos] [log | log-input] [time-range time-range-name] [fragments]
    // UDP:  access-list access-list-number [dynamic dynamic-name [timeout minutes]] {deny | permit} udp source source-wildcard [operator [port]] destination destination-wildcard [operator [port]] [precedence precedence] [tos tos] [log | log-input] [time-range time-range-name] [fragments]           
    let pAccessList<'T> = parse {
        let! _ = pstring "access-list" 

        let! _ = lspaces

        let! aclId = pint32 

        let! _ = lspaces

        let! dynamic = opt(parse { let! _ = pstring "dynamic"
                                   let! dynamicName = pIdentifier
                                   let! timeout = opt(parse { let! _ = pstring "timeout"
                                                              let! timeoutVal = puint32
                                                              return timeoutVal })
                                   return {Name=dynamicName; Timeout=timeout} })
        let! _ = lspaces

        let! action = (pstring "deny" |>> fun _ -> AclAction.Deny) <|> (pstring "permit" |>> fun _ -> AclAction.Permit )

        let! _ = lspaces
       
        let! protocol = 
            let protocolNames = List.map pstringCI (List.ofArray(Enum.GetNames(typeof<ProtocolType>)))
            (choice protocolNames |>> fun t -> (Enum.Parse(typeof<ProtocolType>,t,true)) :?> ProtocolType) <|> (puint8 |>> fun t -> Enum.ToObject(typeof<ProtocolType>,t) :?> ProtocolType) .>> lspaces

        let! _ = lspaces

        let! source = pAddressAndWildcard

        let! _ = lspaces 

        let! sourcePort = if protocol = ProtocolType.Tcp || protocol = ProtocolType.Udp 
                          then opt pPortOperator
                          else preturn None
        let! _ = lspaces               
        let! destination = pAddressAndWildcard

        let! _ = lspaces 

        let! destinationPort = if protocol = ProtocolType.Tcp || protocol = ProtocolType.Udp 
                               then opt pPortOperator
                               else preturn None
        let! _ = lspaces

        let pIcmpMessage = 
            let msgList = [
                             "administratively-prohibited" ;  "dod-host-prohibited" ; "echo-reply" ; "host-precedence-unreachable" ;
                             "host-tos-unreachable" ; "information-reply" ; "mask-request" ; "net-tos-redirect" ; "network-unknown" ;
                             "packet-too-big" ; "precedence-unreachable" ;  "redirect" ; "source-quench" ; "timestamp-reply" ; "ttl-exceeded" ;
                             "alternate-address"; "dod-net-prohibited"; "general-parameter-problem"; "host-redirect" ; "host-unknown"; 
                             "information-request" ; "mobile-redirect" ; "net-tos-unreachable" ; "no-room-for-option"; "parameter-problem";
                             "protocol-unreachable" ; "router-advertisement" ; "source-route-failed" ; "timestamp-request" ; "unreachable" ;
                             "conversion-error" ; "echo" ; "host-isolated" ; "host-tos-redirect" ; "host-unreachable" ; "mask-reply" ;
                             "net-redirect" ; "net-unreachable" ; "option-missing" ; "port-unreachable" ; "reassembly-timeout" ;
                             "router-solicitation" ; "time-exceeded" ; "traceroute"
                          ]
            choice (List.map pstring msgList)
        let! specific = match protocol with 
                        | ProtocolType.Icmp ->  opt( (puint8 |>> fun x -> AclIcmpOptions.IcmpType(x)) <|> (pIcmpMessage |>> fun x -> AclIcmpOptions.Parse(x)) )
                                                |>> fun t -> match t with 
                                                             | None -> AclProtocolOptions.NoOptions
                                                             | Some(icmpOpt) -> AclProtocolOptions.IcmpOptions(icmpOpt)
                        | ProtocolType.Igmp ->  preturn AclProtocolOptions.NoOptions
                        | ProtocolType.Tcp ->   opt(pstringCI "established" |>> fun _ -> AclTcpOptions.Established) 
                                                |>> fun t -> match t with 
                                                             | None -> AclProtocolOptions.NoOptions
                                                             | Some(tcpOpt) -> AclProtocolOptions.TcpOptions(tcpOpt)
                                    
                        | _ -> preturn AclProtocolOptions.NoOptions
        
        let! _ = lspaces

        let! precedence = opt(parse { let! _ = pstring "precedence"
                                      let! value = puint8
                                      return value })
        
        return { Id = aclId.ToString();
                 Dynamic = dynamic;
                 Action = action;
                 Protocol = protocol;
                 Source = source;
                 SourcePort = if sourcePort.IsSome then sourcePort.Value else AclPortOperator.Any;
                 Destination = destination;
                 DestinationPort = if destinationPort.IsSome then destinationPort.Value else AclPortOperator.Any;
                 ProtocolOptions = specific;
                 Precedence = precedence;
                 ToS = None;
                 TimeRange = None;
                 Fragments = None}
    }

type AccessListParser = class
    static member ParseString(input:String) =
        runParserOnString (_CliParsers.pAccessList .>> (_CliParsers.lspaces .>> eof)) null "AccessList" input 
    static member TryParseString(input:string, errorWriter : IO.TextWriter) = 
        match AccessListParser.ParseString(input) with
        | ParserResult.Success(res,_,_) -> Some(res)
        | ParserResult.Failure(err,_,_) -> 
            errorWriter.WriteLine(err);
            None
    static member TryParseString(input:string) =
        AccessListParser.TryParseString(input, IO.StreamWriter.Null)
end


type CliConfigParser = class
    static member ParseFile(path:String) = 
        runParserOnFile _CliParsers.pConfigFile null path Text.Encoding.Default 
    static member TryParseFile(path:string, errorWriter : IO.TextWriter) = 
        match CliConfigParser.ParseFile(path) with
        | ParserResult.Success(res,_,_) -> Some(res)
        | ParserResult.Failure(err,_,_) -> 
            errorWriter.WriteLine(err);
            None
    static member TryParseFile(path:string) = 
        CliConfigParser.TryParseFile(path, IO.StreamWriter.Null)

end

module _CliParsers_Tests = 
    open Xunit

    let aclGroup = [
        "access-list 199 permit tcp any any established"
        "access-list 199 deny   ip 206.191.241.40 0.0.0.7 any"
        "access-list 199 deny   ip host 206.191.194.42 host 206.191.194.42"
        "access-list 199 permit icmp any any echo"
        "access-list 199 permit icmp any any echo-reply"
        "access-list 199 permit tcp any 206.191.241.40 0.0.0.7 eq www"
        "access-list 199 permit tcp any 206.191.241.40 0.0.0.7 eq smtp"
        "access-list 199 permit tcp any 206.191.241.40 0.0.0.7 eq domain"
        "access-list 199 permit udp any 206.191.241.40 0.0.0.7 eq domain"
        "access-list 199 deny   tcp any 206.191.241.40 0.0.0.7 lt 1024"
        "access-list 199 deny   tcp any 206.191.241.40 0.0.0.7 gt 1023"
        "access-list 199 permit udp any 206.191.241.40 0.0.0.7 gt 1023"
        "access-list 199 deny   udp any 206.191.241.40 0.0.0.7 gt 50000"
        "access-list 199 deny   udp any 206.191.241.40 0.0.0.7 lt 1024"
    ]
    type AccessListTests() = class
        [<Fact>]
        member this.SimpleAcl () =
            let t = AccessListParser.ParseString("access-list 199 deny   ip 206.191.241.40 0.0.0.7 any")
            match t with
            | ParserResult.Success(acl, _,_) ->
                Assert.Equal(acl.Action, AclAction.Deny)
                Assert.Equal<string>("199", acl.Id)
                Assert.Equal(ProtocolType.IP, acl.Protocol)
                Assert.Equal(AclLocation.Create("206.191.241.40","0.0.0.7"),acl.Source)
                Assert.Equal(AclLocation.CreateAny(),acl.Destination)
            | ParserResult.Failure(err,_,_) ->
                Assert.True(false, "PARSER ERROR: " + err)
        [<Fact>]
        member this.AclGroup () =
            for l in aclGroup do
                let t = AccessListParser.ParseString(l)
                match t with
                | ParserResult.Failure(err, _,_) ->
                    Assert.True(false, "PARSER ERROR: " + err)
                | _ -> ()
    end

