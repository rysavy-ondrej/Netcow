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
// Netcow.Reachability
open System
open System.IO
open System.Diagnostics
open DataModels
open DataModels.PacketTracer
open System.Linq.Expressions
open System.Reflection
open Netcow
open Netcow.Reachability


  

[<Commands.Cmdlet("Get","Help")>]
let Help() = 
    let usage = Utils.GetResource("Usage.txt")
    Console.WriteLine(usage)

[<EntryPoint>]
let main(args) =
   
    Commands.CmdletManager.Usage <- Utils.GetResource("Usage.txt")
    try
        let res = Commands.CmdletManager.Run(args)
        0
    with e -> 
        Console.Error.WriteLine("ERROR: {0}", e.Message)
        Console.Error.WriteLine("Type '{0} Get-Help' to get a list of available commands.", Assembly.GetExecutingAssembly().GetName().Name)
        0    
