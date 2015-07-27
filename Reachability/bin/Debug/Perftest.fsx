#r "System.dll"
// CSV has the following format
// filter_size, packet_size, added-egs, assert-lower, assert-upper, binary-propagations, conflicts,
// datatype-accessor, datatype-constructor, decisions, memory, minimized-lits, mk-clause, 
// propagations, restarts, time 
open System
open System.IO
open System.Threading
open System.Diagnostics

let execProces(exec,args) = 
    let start = new ProcessStartInfo(exec,args)
    start.UseShellExecute <- false
    start.RedirectStandardOutput <- true
    start.RedirectStandardInput <- true
    start

let parseZ3statistics (stats:string) = 
    let lines = stats.Split('\n')
    let kv = seq { 
                for l in lines do
                    if l.StartsWith("(:") || l.StartsWith(" :")
                    then let [|key;value|] = l.Trim('(',':',' ','\t')
                                              .Split([|' ';'\t'|], StringSplitOptions.RemoveEmptyEntries) 
                         yield (key.Trim(':','('),value.Trim().Trim(')'))
            }
    dict(kv)        


let runTests(fmax:int,gmax:int,timefile:string,memfile:string) =                                      
    let timeWriter = new StreamWriter(timefile) 
    let memWriter = new StreamWriter(memfile)
    for i = 1 to fmax do              
        for j = 1 to gmax do
            let f = Math.Pow(2.0, float i)
            let p = Math.Pow(2.0, float j)                                
            Console.WriteLine("Step {0}{1}", i,j)

            let ncProg = Path.Combine(DirectoryInfo(Directory.GetCurrentDirectory()).Parent.FullName, "Netcow.Reachability.exe") 
            let ncArgs = String.Format("Test-Disjoint -f {0} -p {1}", f,p)

            use ncPrc = Process.Start(execProces(ncProg,ncArgs)) in
                use reader = ncPrc.StandardOutput in
                    let buffer = reader.ReadToEnd();
                    use z3Prc = Process.Start(execProces("z3","-smt2 -in")) in
                    begin
                        z3Prc.StandardInput.Write(buffer)
                        z3Prc.StandardInput.Close()
                        let out = z3Prc.StandardOutput.ReadToEnd()
                        let stats = parseZ3statistics(out)
                        // CSV:
                        // Console.WriteLine("{0},{1},{2},{3},{4},{5}",i,j, stats.["time"], stats.["memory"], stats.["conflicts"], stats.["propagations"])
                        // Z:
                        timeWriter.WriteLine(String.Format("{0} {1} {2}", Math.Pow(2.0, float i), Math.Pow(2.0, float j), stats.["time"]))
                        memWriter.WriteLine(String.Format("{0} {1} {2}", Math.Pow(2.0, float i), Math.Pow(2.0, float j), stats.["memory"]))

                    end                 
    timeWriter.Flush()
    memWriter.Flush()

runTests(16,8,"perft.dat","perfm.dat")