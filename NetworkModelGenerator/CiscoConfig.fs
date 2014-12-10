//
//  CiscoConfig.fs
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
type UInt8 = Byte
type Int8 = SByte
type ProtocolType = System.Net.Sockets.ProtocolType 
/// This represent a command, arguments and subcommands.
type CliCommand = { CmdName : String; No: bool; Args: String[]; Content: CliCommand[] } 
with override this.ToString() =
        String.Format("{0}{1} {2}", (if this.No then "no " else ""), this.CmdName, String.concat " " this.Args)
     /// Gets the current command as a single string. 
     member this.Command = this.CmdName + " " + (String.concat " " this.Args)

[<AutoOpen>]
module ActivePatterns = 
    let (|CliArg1|_|) (input:Option<CliCommand>) = 
        if input.IsSome && input.Value.Args.Length >= 1 
        then Some(input.Value.Args.[0]) 
        else None
    let (|CliArg2|_|) (input:Option<CliCommand>) = 
        if input.IsSome && input.Value.Args.Length >= 2
        then Some(input.Value.Args.[0], input.Value.Args.[1]) 
        else None
    let (|CliArg3|_|) (input:Option<CliCommand>) = 
        if input.IsSome && input.Value.Args.Length >= 3
        then Some(input.Value.Args.[0], input.Value.Args.[1], input.Value.Args.[2]) 
        else None
    let (|CliArg4|_|) (input:Option<CliCommand>) = 
        if input.IsSome && input.Value.Args.Length >= 4
        then Some(input.Value.Args.[0], input.Value.Args.[1], input.Value.Args.[2], input.Value.Args.[3]) 
        else None
       
/// This type represents a device configuration.
type CliConfig(deviceId: String, commands:CliCommand[]) = 
    member this.DeviceId = deviceId
    member this.Commands = commands


type AclAction = Permit | Deny
type IPAddress = System.Net.IPAddress
// Possible operands include lt (less than), gt (greater than), eq (equal), neq (not equal), and range (inclusive range).
type AclPortOperator =
| Any 
| Lt of UInt16
| Gt of UInt16
| Eq of UInt16
| Neq of UInt16
| Range of UInt16 * UInt16
with 
    override this.ToString() = 
        match this with
        | Any -> "*"
        | Lt(p) -> "lt " + p.ToString()
        | Gt(p) -> "gt " + p.ToString()
        | Eq(p) -> "eq " + p.ToString()
        | Neq(p) -> "neq " + p.ToString()
        | Range(p,q) -> "range " + p.ToString() + " " + q.ToString()

type AclLocation = { Address : IPAddress; Wildcard : IPAddress } 
with 
    static member Create(adr:string,wc:string) =
        {Address = IPAddress.Parse(adr); Wildcard = IPAddress.Parse(wc)}
    static member CreateAny() = 
        {Address = IPAddress.Parse("0.0.0.0"); Wildcard = IPAddress.Parse("255.255.255.255")}
    static member CreateHost(adr:string) = 
        {Address = IPAddress.Parse(adr); Wildcard = IPAddress.Parse("0.0.0.0")}
    override this.ToString () = 
        this.Address.ToString() + "%" + this.Wildcard.ToString()
    static member Parse(input:string) = 
        if String.IsNullOrWhiteSpace(input) 
        then invalidArg "input" "null string provided or invalid input format, X.X.X.X Y.Y.Y.Y is expected."
        else let x = input.Trim().Split([|' ';'/';'%'|])
             match x with
             | [| adr; wc |] -> {Address = IPAddress.Parse(adr); Wildcard = IPAddress.Parse(wc)}
             | [| adr |] -> {Address = IPAddress.Parse(adr); Wildcard = IPAddress.Parse("0.0.0.0")}
             | _ -> invalidArg "input" "invalid input format, X.X.X.X/Y.Y.Y.Y is expected."

type AclDynamic = { Name : String; Timeout : option<UInt32> }

type AclIgmpOptions = 
| IgmpType of UInt16

type AclIcmpOptions = 
| IcmpType of UInt8
| IcmpTypeCode of UInt8 * UInt8
with
    override this.ToString() =
        match this with
        | IcmpType(x) -> x.ToString()
        | IcmpTypeCode(x,y) -> x.ToString() + " " + x.ToString()
    static member Parse(input:string) = 
        match input with
        | "echo" -> IcmpType(8uy)
        | "echo-reply" -> IcmpType(0uy)
        | _ -> IcmpType(0uy)
          
type AclTcpOptions =  
| Established
with 
    override this.ToString() = 
        match this with
        | Established -> "established"
type AclProtocolOptions =
| NoOptions 
| IgmpOptions of AclIgmpOptions
| IcmpOptions of AclIcmpOptions
| TcpOptions of AclTcpOptions
with
    override this.ToString() =
        match this with
        | NoOptions -> String.Empty
        | IgmpOptions o -> o.ToString()
        | IcmpOptions o -> o.ToString()
        | TcpOptions o -> o.ToString()
    member this.Contains(x:AclTcpOptions) =
        match this with 
        | TcpOptions o -> o = x
        | _ -> false
    member this.Contains(x:AclIgmpOptions) =
        match this with
        | IgmpOptions o -> o = x
        | _ -> false
    member this.Contains(x:AclIcmpOptions) =
        match this with
        | IcmpOptions o -> o = x
        | _ -> false
/// <summary>
/// Represents a single access-list rule.
/// </summary>
/// <remarks>
///   access-list {100-199 | 2000-2699} {permit | deny} protocol_type 
///   Source_address Source_address_wildcard Source_protocol
///   Destination_address destination_address_wildcard Destination_protocol
///  [protocol specific options] [precedence precedence][tos tos][log][established]
/// </remarks>
type AccessList = { Id : String; 
                    Dynamic: option<AclDynamic>;
                    Action : AclAction; 
                    Protocol: ProtocolType; 
                    Source : AclLocation; 
                    SourcePort: AclPortOperator;
                    Destination : AclLocation;
                    DestinationPort : AclPortOperator;
                    ProtocolOptions : AclProtocolOptions;
                    Precedence : Option<Byte>;
                    ToS : Option<String>;
                    TimeRange : Option<String>;
                    Fragments: Option<bool>}    
with 
    override this.ToString() =
        String.concat " " [ "access-list"
                            this.Id
                            this.Action.ToString().ToLower()
                            this.Protocol.ToString().ToLower()
                            this.Source.ToString().Replace('%',' ')
                            this.SourcePort.ToString()
                            this.Destination.ToString().Replace('%',' ')
                            this.DestinationPort.ToString()
                          ]


        
module Tests = 
    ///Example:
    /// interface Serial0/1
    ///   ip address 198.18.196.65 255.255.255.252

    let i = { CmdName="interface"; No=false; Args = [| "Serial0/1" |]; 
              Content=[|
                         { CmdName="ip address"; No=false; Args = [| "198.18.196.65";"255.255.255.252"|]; Content = [||] }
              |]
            }