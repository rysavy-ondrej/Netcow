module Netcow.Reachability.Utils
open System.IO
open System.Reflection


let GetResource(name:string) : string =
    use sr = new StreamReader(Assembly.GetExecutingAssembly().GetManifestResourceStream(name)) 
    in sr.ReadToEnd()
