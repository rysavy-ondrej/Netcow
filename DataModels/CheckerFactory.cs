using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.IO;
using System.Reflection;
using System.Diagnostics;
namespace DataModels
{
    public static class CheckerFactory
    {
        public static string[] AvailableDomainFiles()
        {
            var _assembly = Assembly.GetExecutingAssembly();
            return _assembly.GetManifestResourceNames();
        }
   		public static string GetDomainFilePath(string domain)
        {
            var _assembly = Assembly.GetExecutingAssembly();
            var resourceName = String.Format("Netcow.DataModels._4mlFiles.{0}.4ml", domain);
            Trace.WriteLine("Attempting to load domain content from resource file '" + resourceName + "'.");
            try
            {
                using (var _textStreamReader = new StreamReader(_assembly.GetManifestResourceStream(resourceName)))
                {
                    var tmpFileName = Path.GetTempFileName();
                    File.WriteAllText(tmpFileName, _textStreamReader.ReadToEnd());
                    Trace.WriteLine("Success, content wrote to '" + tmpFileName + "'.");
                    return tmpFileName;
                }
            }
            catch (Exception)
            {
                Trace.WriteLine("Failed - no such file in the assembly.");
                return null;
            }               
        }
        public static Checker Create(string domainName)
        {


            switch (domainName)
            {
                case "Reachability":
                    return Checker.Create("Reachability", GetDomainFilePath("Reachability"), Reachability_Root.CreateObjectGraph);
                case "Firewall":
                    return Checker.Create("Firewall",GetDomainFilePath("Firewall"), Firewall_Root.CreateObjectGraph);
                default:
                    throw new ArgumentException(String.Format("Domain '{0}' cannot be found.", domainName));

            }
        }
    }
}
