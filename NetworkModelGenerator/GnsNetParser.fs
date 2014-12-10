//
//  GnsNetParser.fs
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
open Netcow.Utils
(*
autostart = False
[127.0.0.1:7200]
    workingdir = /tmp
    udp = 10000
    [[3640]]
        image = /Data/GNS3/IOS/C3640-JK.BIN
        idlepc = 0x603e26f0
        ghostios = True
        chassis = 3640
    [[ROUTER Cherry]]
        model = 3640
        console = 2015
        aux = 2100
        cnfg = configs/Cherry.cfg
        slot0 = NM-1FE-TX
        f0/0 = Alder f0/0
        slot1 = NM-1FE-TX
        f1/0 = Walnut f0/0
        x = -279.780266634
        y = -176.149278299
*)

type ConfigSection = { Label:String; Content:ConfigNode[] }
and ConfigKey = { Name : String; Value:String }
and ConfigNode =
| Section of ConfigSection
| Key of ConfigKey
with
    override this.ToString() = 
        match this with
        | Section s -> String.Format("[{0}]", s.Label)
        | Key k -> String.Format("{0} = {1}", k.Name, k.Value)
    static member fold (f:'State -> ConfigNode -> 'State) (state: 'State) (t:ConfigNode[]) : 'State = 
        let g (s:'State)(x:ConfigNode) = 
            let s' = f s x
            match x with
            | Section t -> ConfigNode.fold f s' t.Content
            | _ -> s'
        Array.fold g state t

    static member filter (pred:ConfigNode->bool)(items:ConfigNode[]) : ConfigNode[] = 
        let f (s:List<ConfigNode>) (x:ConfigNode) =
            if pred x then x::s else s
        ConfigNode.fold f [] items |> List.rev |> Array.ofList

    static member GetSections (regex:String,items:ConfigNode[]) : ConfigSection[] = 
        let pred (t:ConfigNode) = 
            match t with
            | Section {Label=CompiledMatch regex _;Content=_} -> true
            | _ -> false
        ConfigNode.filter pred items |> Array.map (fun t -> match t with Section s -> s | _ -> failwith "invalid operation")

    static member GetKeys (regex:String,items:ConfigNode[]) : ConfigKey[] = 
        let pred (t:ConfigNode) = 
            match t with
            | Key {Name=CompiledMatch regex _;Value=_} -> true
            | _ -> false
        ConfigNode.filter pred items |> Array.map (fun t -> match t with Key k -> k | _ -> failwith "invalid operation")
    /// Prints nodes to the standard output.  
    static member Print (nodes:ConfigNode[]) = 
        let rec printNode (level:int)(nodes:ConfigNode []) =  
            for n in nodes do
                System.Console.Write(String.replicate (level*2) " ")
                System.Console.WriteLine(n)
                match n with
                | Section s -> printNode (level+1) s.Content 
                | _ -> ()
        in printNode 0 nodes

module internal _GnsParsers = 
    /// Section starts with section header and ends before other section start.
    /// Section can have subsections.
    let pTopologyFile<'T> = parse {
        let getSectionHdrOpen (level:int)  = 
            (pstring (String.replicate level "[") .>> notFollowedByString "[")
        let getSectionHdrClose (level:int) = 
            (pstring (String.replicate level "]") .>> notFollowedByString "]")
        
        let pSectionHeader (level:int) = parse {
            let! _ = (getSectionHdrOpen level)
            let! label = charsTillString "]" false 128 
            let! _ = (getSectionHdrClose level)
            let! _ = skipRestOfLine true
            return label
        }

        let pSectionItem = parse {
            let! variable = charsTillString "=" false 128 |>> fun x -> x.Trim()
            let! _ = pchar '='
            let! value = restOfLine true |>> fun x -> x.Trim()
            return Key {Name=variable;Value=value}
        }

        let rec pSection(level:int) = parse {
            let! hdr = spaces >>. pSectionHeader level
            let item = spaces >>. choice [ followedBy (getSectionHdrOpen (level+1)) >>. pSection (level+1)
                                           notFollowedByString "[" >>. pSectionItem ]
            let! items = many (attempt item) 
            return Section {Label=hdr;Content= Array.ofSeq items}
        }

        let item = spaces >>. choice [ followedByString "[" >>. pSection 1 
                                       notFollowedByString "[" >>. pSectionItem ]
        let! items = many (attempt item)
        return Array.ofList items
    }
 type GnsTopologyParser = class
    static member ParseFile(path:string) = 
        runParserOnFile _GnsParsers.pTopologyFile null path Text.Encoding.Default
    static member TryParseFile(path:string) = 
        match GnsTopologyParser.ParseFile(path) with
        | ParserResult.Success(res,_,_) -> Some(res)
        | _ -> None
 end