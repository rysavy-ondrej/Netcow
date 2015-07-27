using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Management.Automation;
namespace PerformanceTests
{
    public class FilterRule
    {
        public Range<UInt32> SourceAddress;
        public Range<UInt32> DestinationAddress;
        public Range<UInt16> SourcePort;
        public Range<UInt16> DestinationPort;
        public Range<UInt16> Protocol;
    }
    public enum GenerationMethod { Random };

    [Cmdlet(VerbsCommon.Get,"RandomFilter")]
    public class GetRandomFilter : Cmdlet
    {
        [Parameter(HelpMessage="Size of generated filter", Mandatory=true, ValueFromPipeline=false)]
        public int Size { get; set; }
        [Parameter(HelpMessage = "Ratio of overlaped rules in the generated filter", Mandatory = true, ValueFromPipeline = false)]
        public int OverlapRatio { get; set; }

        [Parameter(HelpMessage= "Method used for generating filter", Mandatory=true)]
        public GenerationMethod Method { get; set; }

        protected override void ProcessRecord()
        {
            if (this.Size <= 0 || this.Size > 100000) 
            {
                ErrorRecord er = new ErrorRecord(new ArgumentException("specified size is out of bounds", "Size"), "E001", ErrorCategory.InvalidArgument, this);
                this.WriteError(er); return; 
            }
            
            for (int i = 0; i < this.Size; i++ )
            {

                
            }
        }
    }
}
