//
//  ReachabilityProgram.cs
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
open System
open System.IO
open System.Diagnostics
open DataModels
open DataModels.PacketTracer
open ConsoleFx
open ConsoleFx.Programs.Simple
open ConsoleFx.Validators
open System.Linq.Expressions
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Linq.RuntimeHelpers
type IndentedTextWriter = System.CodeDom.Compiler.IndentedTextWriter

/// This is a helper function to convert parameterless lambda function to Func expression of LINQ.
let toLinqFunc (expr : Expr<unit -> 'b>) =
  let linq = LeafExpressionConverter.QuotationToExpression expr
  let call = linq :?> MethodCallExpression
  let lambda = call.Arguments.[0] :?> LambdaExpression
  Expression.Lambda<Func<'b>>(lambda.Body, []) 

/// Takes an arbitrary name and produces identifier from it by replacing
/// all characters that violate identifier specification. 
let mkIdentifier (name:String) : String =
    let idmap (c:Char) : String = if Char.IsLetterOrDigit c || c = '_' then c.ToString() else "_" 
    String.collect idmap name                              

let mutable inputFile = String.Empty

let programHandler () = 
    Trace.WriteLine ("Embedded domain files:", "INFO");
    for s in CheckerFactory.AvailableDomainFiles() do                                                             
        Trace.WriteLine(String.Format(" +-{0}",s),"INFO")
    let checker = CheckerFactory.Create("Reachability");

    Trace.WriteLine (String.Format("Processing input file '{0}'.", inputFile), "INFO");
    
    /// Load Network file and print out all devices...
    let network = PtNetwork(inputFile);
    let writer = new IndentedTextWriter(Console.Out)
    writer.WriteLine("model T of Reachability at \"Reachability.4ml\" {")
    writer.Indent <- writer.Indent + 1
    for device in Seq.filter (fun (d:PtDevice) -> d.DeviceLayer = PtDeviceLayer.InternetLayer || d.DeviceLayer = PtDeviceLayer.ApplicationLayer) network.Devices do
        let deviceType = device.DeviceType
       
        let deviceId = mkIdentifier(device.Name)
        writer.WriteLine("d_{0} is Device(\"{1}\", {2}).", deviceId, device.Name,deviceType.ToString().ToUpperInvariant())
        writer.Indent <- writer.Indent + 1
        
        for port in network.GetPortMap(device) do
            if port.IsPowered 
            then
                let portId = mkIdentifier(port.Name)
                writer.WriteLine("p_{0}_{1} is Port(\"{2}\",d_{3}).",deviceId,portId,port.Name,deviceId)
        
        // generate idge between pairs of ports of the same device:
        for srcPort in network.GetPortMap(device) do
            if srcPort.IsPowered 
            then for trgPort in network.GetPortMap(device) do
                 if trgPort.IsPowered && srcPort.Name<>trgPort.Name 
                 then let srcPortId = mkIdentifier(srcPort.Name)
                      let trgPortId = mkIdentifier(trgPort.Name)
                      writer.WriteLine("Idge(p_{0}_{1}, p_{0}_{2}).",deviceId,srcPortId,trgPortId)
                     
        writer.Indent <- writer.Indent - 1  
    
    let getLinkName(link:PtLink) : String =        
        let portNames = 
            match (link.SourcePort.Device.DeviceType, link.TargetPort.Device.DeviceType) with
            | (PtDeviceType.Router,PtDeviceType.Router) -> [link.SourcePort.Oid;link.TargetPort.Oid]
            | (PtDeviceType.Switch,_) -> [String.Format("{0}.{1}", link.SourcePort.Device.Name, "vlan1")]
            | (_,PtDeviceType.Switch) -> [String.Format("{0}.{1}", link.TargetPort.Device.Name, "vlan1")]
            | _ -> []
        List.sort( portNames ) |> String.concat "+"    
    
    let linkDict = new Collections.Generic.Dictionary<string,int>() 

    for device in Seq.filter (fun (d:PtDevice) -> d.DeviceType = PtDeviceType.Switch) network.Devices do
        let linkId = linkDict.Count
        let linkName = String.Format("{0}.{1}", device.Name, "vlan1")
        writer.WriteLine("l{0} is Link(\"{1}\").", linkId, linkName)
        linkDict.Add(linkName, linkId)
          
    for link in network.Links do
        match (link.SourcePort.Device.DeviceType, link.TargetPort.Device.DeviceType) with
        | (PtDeviceType.Router,PtDeviceType.Router) -> 
            let linkName = getLinkName link
            if not (linkDict.ContainsKey linkName) 
            then let linkId = linkDict.Count                 
                 writer.WriteLine("l{0} is Link(\"{1}\").", linkId, linkName)
                 linkDict.Add(linkName,linkId)  
        | _ -> ()

    // Out-Edges and In-Edges:
    for link in network.Links do
        match (link.SourcePort.Device.DeviceType, link.TargetPort.Device.DeviceType) with
        | (PtDeviceType.Router,_) ->
            let sourcePort = String.Format("p_{0}_{1}", mkIdentifier(link.SourcePort.Device.Name), mkIdentifier(link.SourcePort.Name))
            let targetLink = getLinkName link
            writer.WriteLine("EdgeO({0},l{1}).", sourcePort, linkDict.[targetLink])
        | _-> ()    
        match (link.SourcePort.Device.DeviceType, link.TargetPort.Device.DeviceType) with          
        | (_,PtDeviceType.Router) ->  
            let sourceLink = getLinkName link
            let targetPort = String.Format("p_{0}_{1}", mkIdentifier(link.TargetPort.Device.Name), mkIdentifier(link.TargetPort.Name))            
            writer.WriteLine("EdgeI(l{0},{1}).", linkDict.[sourceLink], targetPort)
        | _ -> ()
        
    writer.Indent <- writer.Indent - 1
    Console.WriteLine("}");

    0
    
[<EntryPoint>]
let main argv =    
    Trace.Listeners.Add(new TextWriterTraceListener(Console.Error)) |> ignore
    Trace.AutoFlush <- true

    let app = new Programs.Simple.ConsoleProgram(Programs.ExecuteHandler(programHandler),true,CommandGrouping.DoesNotMatter, true)
    in try
        app.AddArgument(false)
           .ValidateWith(new PathValidator(checkIfExists=true))
           .ValidateWith(new CustomValidator(fun arg -> Path.GetExtension(arg).Equals(".xml", StringComparison.OrdinalIgnoreCase)))  
           .AssignTo(<@ fun () -> inputFile @> |> toLinqFunc );

        app.SetUsageBuilder<Programs.Simple.SimpleResourceUsageBuilder>()
        app.Run()
       with ex -> app.HandleError(ex)