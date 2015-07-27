//
//  Benchmarks.cs
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
module Netcow.Reachability.Tests
open System
open System.IO
open System.Text
open System.Diagnostics
open System.Diagnostics.Contracts
open System.Linq
open System.Linq.Expressions
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Linq.RuntimeHelpers
type IndentedTextWriter = System.CodeDom.Compiler.IndentedTextWriter

type FilterItem = {
    SourceAddress : UInt32*UInt32;
    DestinationAddress : UInt32*UInt32;
    SourcePort : UInt16*UInt16;
    DestinationPort : UInt16*UInt16;
    Protocol : Byte*Byte
}

let defineZ3Fun (id:int, f:FilterItem) : string =
    let sb = new StringBuilder()
    sb.AppendFormat("(define-fun f_{0} ((f Flow)) Bool", id).AppendLine()
      .AppendFormat("(and (>= (srcip f) {0}) (<= (srcip f) {1})", fst f.SourceAddress,snd f.SourceAddress).AppendLine()
      .AppendFormat("     (>= (dstip f) {0}) (<= (dstip f) {1})", fst f.DestinationAddress, snd f.DestinationAddress).AppendLine()
      .AppendFormat("     (>= (srcpn f) {0}) (<= (srcpn f) {1})", fst f.SourcePort, snd f.SourcePort).AppendLine()
      .AppendFormat("     (>= (dstpn f) {0}) (<= (dstpn f) {1})", fst f.DestinationPort, snd f.DestinationPort).AppendLine()
      .AppendFormat("     (>= (proto f) {0}) (<= (proto f) {1})", fst f.Protocol, snd f.Protocol).AppendLine()  
      .AppendFormat("))").AppendLine()                
      .ToString ()

let getFilter split = 
    let r32 = (UInt32.MaxValue / (uint32 split)) 
    let r16 = (UInt16.MaxValue / (uint16 split)) 
    let r8 =  (Byte.MaxValue / (byte split)) 
    seq {
        // compute cubes...
        for d1=(uint32 0) to (uint32 split)-(uint32 1) do
            for d2=(uint32 0) to (uint32 split)-(uint32 1) do     
                for d3=(uint16 0) to (uint16 split)-(uint16 1) do
                    for d4=(uint16 0) to (uint16 split)-(uint16 1) do
                        for d5=(byte 0) to (byte split)-(byte 1) do
                            yield ( ((int d1) * split * split * split * split) + ((int d2) * split * split * split) + ((int d3) * split * split) + ((int d4) * split) + (int d5 + 1),
                                    { 
                                        SourceAddress = (uint32 1)+(r32 * d1),(r32 * (d1 + (uint32 1)))
                                        DestinationAddress = (uint32 1)+(r32 * d2),(r32 * (d2 + (uint32 1)))
                                        SourcePort = (uint16 1)+(r16 * d3),(r16 * (d3 + (uint16 1)))
                                        DestinationPort = (uint16 1)+(r16 * d4),(r16 * (d4 + (uint16 1)))
                                        Protocol = (byte 1)+(r8 * d5),(r8 * (d5 + (byte 1)))
                                    })
        }

                                  
[<Netcow.Commands.Cmdlet("Get","RandomFilter","Generates a random filter of the specified size with non-overlapping rules.")>]
let GetRandomFilter(size:Int32) =
    // get number of intervals in each dimension
    let split = int <| Math.Ceiling(Math.Pow(float size, 0.2))
    if (split <= 16)
    then    
        let filter = getFilter split
        for f in filter do
            Console.WriteLine(defineZ3Fun(f))
    else ()

[<Netcow.Commands.Cmdlet("Test","Disjoint","Generates a random filter and random flow for testing disjoint query.")>]
let TestDisjoint(firewallSize:Int32,packetSize:Int32) =
    let split = int <| Math.Ceiling(Math.Pow(float (firewallSize + packetSize), 0.2))        
    let filter = getFilter split
    /// randomly pick rules for firewall and packet:
    let rnd = Random()
    let firewall = new System.Collections.Generic.List<int*FilterItem>()
    let packets = new System.Collections.Generic.List<int*FilterItem>()
    for f in filter do
        if rnd.NextDouble() <= (float firewallSize) / float (firewallSize + packetSize) 
        then firewall.Add f
        else packets.Add f
    // print preamble
    Console.WriteLine(Utils.GetResource("FirewallTest.smt"))
    // print flows    
    for f in filter do
        Console.WriteLine(defineZ3Fun(f))
    // define filter:
    Console.WriteLine("(define-fun f_filter ((f Flow)) Bool	(or	")
    for f in firewall do
        Console.WriteLine("  (f_{0} f)", fst f)        
    Console.WriteLine("))")
    // define packet:
    Console.WriteLine("(define-fun f_packet ((f Flow)) Bool	(or	")
    for f in packets do
        Console.WriteLine("  (f_{0} f)", fst f)        
    Console.WriteLine("))")
    // define assert:    

    Console.WriteLine("(declare-const flow Flow)")
    Console.WriteLine("(assert (assert_flow flow))")
    Console.WriteLine("(assert (Disjoint (f_filter flow)(f_packet flow)))")
    Console.WriteLine("(echo \"Evaluating disjoint assert...\")")
    Console.WriteLine("(check-sat)")
    //Console.WriteLine("(get-model)")
    Console.WriteLine("(get-info :all-statistics)")

let rd = Random()
let getTransformBodyFromFilters(filterCount : int, size : int) : string =
    let sb = StringBuilder()
    sb.Append("  (or ") |> ignore
    for i=1 to size do
        sb.AppendFormat("(and (f_{0} x) (f_{1} y))",rd.Next(filterCount)+1,rd.Next(filterCount)+1) |> ignore
    sb.AppendLine(")").ToString()    
 
let getFirewallBodyFromFilters(filterCount : int, size : int) : string =
    let sb = StringBuilder()
    sb.Append("  (or") |> ignore
    for i=1 to size do
        sb.AppendFormat("(f_{0} x)",rd.Next(filterCount)+1) |> ignore
    sb.AppendLine(")").ToString()      
        
[<Netcow.Commands.Cmdlet("Test","DisjointPath","Generates a random path for testing disjoint query.")>]
let TestNetworkDisjoint(networkLength:int, rbaseCount:int, transformSize:int, firewallSize:int, packetSize:int) =    
    let split = int <| Math.Ceiling(Math.Pow(float (rbaseCount), 0.2))        
    let filter = getFilter split
        
    Console.WriteLine(Utils.GetResource("FirewallTest.smt"))
    for f in filter do Console.WriteLine(defineZ3Fun(f))
    
    // generate T relations:
    for i = 1 to networkLength do        
        let body = getTransformBodyFromFilters(filter.Count(),transformSize)        
        Console.WriteLine("(define-fun T_{0} ((x Flow)(y Flow)) Bool\n{1})", i, body)
    // generate F relations:
    for i = 1 to networkLength do        
        let body = getFirewallBodyFromFilters(filter.Count(), firewallSize)
        Console.WriteLine("(define-fun F_{0} ((x Flow)) Bool\n{1})", i, body)
    // generate R relation:
    let zvars = seq { for i=1 to networkLength-1 do yield String.Format("(z{0} Flow)", i) } |> String.concat ""  
    let rbody = "(T_1 x z1) (F_1 z1) " + ( seq { for i = 2 to networkLength-1 do yield String.Format("(T_{0} z{1} z{0}) (F_{0} z{0})", i, i-1) } |> String.concat "" ) + String.Format("(T_{0} z{1} y)", networkLength,networkLength-1)
    Console.WriteLine("(define-fun R ((x Flow)(y Flow)) Bool (exists ({0}) (and {1})))", zvars, rbody)
    // define random P and Q
    Console.WriteLine("(define-fun P ((x Flow)) Bool\n{0})", getFirewallBodyFromFilters(filter.Count(), packetSize))
    Console.WriteLine("(define-fun Q ((x Flow)) Bool\n{0})", getFirewallBodyFromFilters(filter.Count(), packetSize))

    // P(x) is assumption on flow x, R(x,y) is end-to-end relation, and Q(y) is assert:
    Console.WriteLine("(assert (forall ((x Flow)) (exists ((y Flow)) (=> (P x) (Disjoint (R x y) (Q y)) ) ) ) )")
    Console.WriteLine("(check-sat)")
    Console.WriteLine("(get-info :all-statistics)")