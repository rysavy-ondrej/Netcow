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
open ConsoleFx
open ConsoleFx.Programs.Simple
open ConsoleFx.Validators
open System.Linq.Expressions
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Linq.RuntimeHelpers

/// This is a helper function to convert parameterless lambda function to Func expression of LINQ.
let toLinqFunc (expr : Expr<unit -> 'b>) =
  let linq = LeafExpressionConverter.QuotationToExpression expr
  let call = linq :?> MethodCallExpression
  let lambda = call.Arguments.[0] :?> LambdaExpression
  Expression.Lambda<Func<'b>>(lambda.Body, []) 


let mutable inputFile = String.Empty

let programHandler () = 
    Console.WriteLine ("Available domain files");

    for s in CheckerFactory.AvailableDomainFiles() do
        Console.WriteLine(s)
    Console.WriteLine ("Processing {0}...", inputFile);
    let checker = CheckerFactory.Create("Reachability");

    /// Load Network file and print out all devices...
    let net = DataModels.PacketTracer.PtNetwork(inputFile);
    for dev in net.Devices do
        Console.WriteLine("{0}:{1}", dev.Name, dev.DeviceType)
        //Console.WriteLine(String.concat "\n" dev.RunningConfig)
        for prt in net.GetPortMap(dev) do
            Console.Write("  {0}", prt.Name)
            
            if prt.IsConnected 
            then 
                let oth = net.GetRemotePort(prt)
                Console.WriteLine(" -> {0}.{1}", oth.Device.Name,oth.Name) 
            else Console.WriteLine()
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