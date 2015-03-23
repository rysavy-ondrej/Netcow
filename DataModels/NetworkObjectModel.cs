using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml.Linq;
using System.Diagnostics;
namespace DataModels.PacketTracer
{
    public enum PtDeviceType
    {
        ACCESS_POINT,  
        ANALOG_PHONE,  
        BRIDGE,  
        CABLE_MODEM,  
        CLOUD,  
        CO_AXIAL_SPLITTER,  
        DSL_MODEM,  
        HOME_VOIP,  
        HUB,  
        IP_PHONE,  
        LAPTOP,  
        MULTI_LAYER_SWITCH,  
        MULTI_USER,  
        PC,  
        PDA,  
        PRINTER,  
        REMOTE_NETWORK,  
        REPEATER,  
        ROUTER,  
        SERVER,  
        SWITCH,  
        TABLET_PC,  
        TV,  
        WIRED_END_DEVICE,  
        WIRELESS_END_DEVICE,  
        WIRELESS_ROUTER  
    }
    public class PtDevice
    {
        XElement _xdata;
        internal PtDevice(XElement xdata)
        {
            this._xdata = xdata;
        }
        public String Name
        {
            get
            {
                return this._xdata.Element("ENGINE").Element("NAME").Value;
            }
        }
        public String DeviceType
        {
            get
            {
                return this._xdata.Element("ENGINE").Element("TYPE").Value;
            }
        }

        public string [] RunningConfig
        {
            get
            {
                var lines = from line in this._xdata.Element("ENGINE").Element("RUNNINGCONFIG").Elements("LINE")
                            select line.Value;
                return lines.ToArray<String>();
            }
        }
        public string[] StartupConfig
        {
            get
            {
                var lines = from line in this._xdata.Element("ENGINE").Element("STARTUPCONFIG").Elements("LINE")
                            select line.Value;
                return lines.ToArray<String>();
            }
        }
    }
    public class PtPort
    {
        internal XElement _xdata;
        internal PtDevice _device;

        internal PtPort(PtDevice device, XElement xdata)
        {
            _device = device;
            _xdata = xdata;
        }

        public PtDevice Device
        {
            get
            {
                return _device;
            }
        }

        public String Name
        {
            get
            {
                return this._xdata.Attribute("name").Value;
            }
        }

        public bool IsConnected
        {
            get
            {
                return this._xdata.Attribute("type") != null;
            }
        }
    }
    /// <summary>
    /// This class represents a network object model which is exported from PacketTracer.
    /// </summary>
    public class PtNetwork
    {
        XDocument _xdoc;

        public PtNetwork(string networkFilename)
        {
            try
            {
                this._xdoc = XDocument.Load(networkFilename);
            }
            catch(Exception e)
            {
                var errtext = String.Format("Error: Cannot load Network file '{0}'. {1}", networkFilename, e.Message);
                Trace.WriteLine(errtext);
            }
        }

        public IEnumerable<PtDevice> Devices
        {
            get
            {
                var xdev = from x in _xdoc.Descendants("DEVICE")
                           select new PtDevice(x);
                return xdev;
            }
        }
        public PtDevice GetDevice(String name)
        {
            return this.Devices.SingleOrDefault(x => x.Name.Equals(name));        
        }


        public PtPort[] GetPortMap(PtDevice device)
        {
            var xdev = _xdoc.Descendants("PORTMAP").SingleOrDefault(x => x.Attribute("device").Value.Equals(device.Name));
            return (from y in xdev.Descendants()
                    select new PtPort(device, y)).ToArray();
        }

        public PtPort GetRemotePort(PtPort localPort)
        {
            var otherDev = localPort._xdata.Attribute("other-dev");
            var otherPort = localPort._xdata.Attribute("other-port");

            var remoteDevice = this.GetDevice(otherDev.Value);
            return GetPortMap(remoteDevice).SingleOrDefault(x => x.Name.Equals(otherPort.Value));
        }
    }
}
