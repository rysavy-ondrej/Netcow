using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Management.Automation;
namespace Netcow.Cli.CmdLets
{
    public class CliCommand
    {
        IEnumerable<CliCommand> GetAllCommands()
        {
            
            return null;
        }
    }
    [Cmdlet("Get","Help")]
    public class GetHelp : Cmdlet
    {
        protected override void ProcessRecord()
        {
            base.ProcessRecord();
        }
    }
}
