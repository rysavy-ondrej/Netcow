using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Xml.Linq;
using System.Diagnostics;
using System.Diagnostics.Contracts;
namespace DataModels.PacketTracer
{
    public enum PtDeviceLayer
    {
        LinkLayer,
        InternetLayer,
        TransportLayer, 
        ApplicationLayer
    }
    public enum PtDeviceType
    {
        AcessPoint,  
        AnalogPhone,  
        Bridge,  
        CableModem,  
        Cloud,  
        CoaxialSplitter,  
        DslModem,  
        HomeVoip,  
        Hub,  
        IpPhone,  
        Laptop,  
        MultiLayerSwitch,  
        MultiUser,  
        PC,  
        PDA,  
        Printer,  
        RemoteNetwork,  
        Repeater,  
        Router,  
        Server,  
        Switch,  
        TabletPC,  
        TV,  
        WiredEndDevice,  
        WirelessEndDevice,  
        WirelessRouter  
    }

    public enum PtConnectionType
    {
        Undefined = 0,
        _FirstType = 8100,
        EthernetStraight = _FirstType,
        EthernetCross,
        EthernetRoll,
        Fiber,
        Phone,
        Cable,
        Serial,
        Auto,
        Console,
        Wireless,
        Coaxial,
        _LastType = Console
    }

    public enum PtPortType
    {
        ACCESS_POINT_WIRELESS_A,  
        ACCESS_POINT_WIRELESS_G,  
        ACCESS_POINT_WIRELESS_N,  
        AUX,  
        COAXIAL7,  
        CONSOLE,  
        COPPER_COAXIAL,  
        COPPER_ETHERNET,  
        COPPER_FAST_ETHERNET, 
        COPPER_GIGABIT_ETHERNET,  
        FIBER_FAST_ETHERNET,  
        FIBER_GIGABIT_ETHERNET,  
        FRSUB_INTERFACE,  
        HOST_WIRELESS_A,  
        HOST_WIRELESS_G,  
        HOST_WIRELESS_N,  
        LOOPBACK,  
        MODEM,  
        NULL,  
        PORT_CHANNEL,  
        PT_CO_AXIAL_SPLITTER_MODULE,  
        RS232,  
        SERIAL,  
        SMART_SERIAL,  
        SUB_INTERFACE,  
        TUNNEL,  
        VIRTUAL_ACCESS,  
        VIRTUAL_LINK,  
        VIRTUAL_TEMPLATE,  
        VLAN  
    }

    public abstract class PtObject
    {
        abstract public string Oid { get; }
    }
    public class PtDevice : PtObject
    {
        internal XElement _xdata;
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
        public PtDeviceType DeviceType
        {
            get
            {
                var deviceTypeString = this._xdata.Element("ENGINE").Element("TYPE").Value;
                return (PtDeviceType)(Enum.Parse(typeof(PtDeviceType), deviceTypeString, true));
            }
        }
        public PtDeviceLayer DeviceLayer
        {
            get
            {
                switch (this.DeviceType)
                {
                    case PtDeviceType.AcessPoint: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.AnalogPhone: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.Bridge: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.CableModem: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.Cloud: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.CoaxialSplitter: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.DslModem: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.HomeVoip: return PtDeviceLayer.InternetLayer;
                    case PtDeviceType.Hub: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.IpPhone: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.Laptop: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.MultiLayerSwitch: return PtDeviceLayer.InternetLayer;
                    case PtDeviceType.PC: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.PDA: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.Printer: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.Repeater: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.Router: return PtDeviceLayer.InternetLayer;
                    case PtDeviceType.Server: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.Switch: return PtDeviceLayer.LinkLayer;
                    case PtDeviceType.TabletPC: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.TV: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.WiredEndDevice: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.WirelessEndDevice: return PtDeviceLayer.ApplicationLayer;
                    case PtDeviceType.WirelessRouter: return PtDeviceLayer.InternetLayer;
                }
                return PtDeviceLayer.LinkLayer;
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

        public override string Oid
        {
            get { return this.Name + ":" + this.DeviceType.ToString(); }
        }
    }
    public class PtPort : PtObject
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
                return this._xdata.Element("LINK") != null;
            }
        }

        public bool IsPowered
        {
            get
            {
                var power = this._xdata.Attribute("power");
                return power != null ? Boolean.Parse(power.Value) : false;
            }
        }
        public PtConnectionType ConnectionType
        {
            get
            {
                if (this.IsConnected)
                {
                    var x = this._xdata.Element("LINK").Attribute("type");
                    return x != null ? (PtConnectionType)Int32.Parse(x.Value) : PtConnectionType.Undefined;
                }
                else return PtConnectionType.Undefined;
            }
        }
        internal XElement getLinkElement()
        {
            return this._xdata.Element("LINK");
        }

        public override string Oid
        {
            get { return this.Device.Name + "." + this.Name; }
        }
    }

    public class PtLink : PtObject
    {
        private XElement _xdata;
        internal PtLink(XElement xdata)
        {
            this._xdata = xdata;
        }
        public PtPort SourcePort
        {
            get
            {
                var portNode = _xdata.Parent;
                var portMapNode = portNode.Parent;
                var deviceName = portMapNode.Attribute("device").Value;
                var device = PtNetwork.GetDevice(_xdata.Document, deviceName);
                return new PtPort(device, portNode); 
            }
        }
        public PtPort TargetPort
        {
            get
            {
                var deviceName = _xdata.Attribute("device").Value;
                var portName = _xdata.Attribute("port").Value;
                var device = PtNetwork.GetDevice(_xdata.Document, deviceName);
                var port = PtNetwork.GetPortMap(_xdata.Document, device).SingleOrDefault(x => x.Name.Equals(portName));
                return port;                
            }
        }


        public override string Oid
        {
            get 
            {
                return this.SourcePort.Oid + "->" + this.TargetPort.Oid;
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


        public static IEnumerable<PtDevice> GetDevices(XDocument xdoc)
        {
            var xdev = from x in xdoc.Descendants("DEVICE")
                       select new PtDevice(x);
            return xdev;
        }
        public IEnumerable<PtDevice> Devices
        {
            get
            {
                return PtNetwork.GetDevices(this._xdoc);
            }
        }

        public IEnumerable<PtLink> Links
        {
            get
            {
                var xlink = from x in _xdoc.Descendants("LINK")
                            select new PtLink(x);
                return xlink;
            }
        }
        public static PtDevice GetDevice(XDocument xdoc, String name)
        {
            return PtNetwork.GetDevices(xdoc).SingleOrDefault(x => x.Name.Equals(name));        
        }
        public PtDevice GetDevice(String name)
        {
            return PtNetwork.GetDevice(this._xdoc, name); 
        }

        public static PtPort[] GetPortMap(XDocument xdoc, PtDevice device)
        {
            var xdev = xdoc.Descendants("PORTMAP").SingleOrDefault(x => x.Attribute("device").Value.Equals(device.Name));
            return (from y in xdev.Descendants("PORT")
                    select new PtPort(device, y)).ToArray();
        }
        public PtPort[] GetPortMap(PtDevice device)
        {
            return PtNetwork.GetPortMap(this._xdoc, device);
        }

        public PtPort GetRemotePort(PtPort localPort)
        {
            var xlink = localPort.getLinkElement();
            if (xlink != null)
            {
                var otherDev = xlink.Attribute("device");
                var otherPort = xlink.Attribute("port");
                Contract.Requires(otherDev != null && otherPort != null);

                var remoteDevice = this.GetDevice(otherDev.Value);
                return GetPortMap(remoteDevice).SingleOrDefault(x => x.Name.Equals(otherPort.Value));
            }
            else return null;
        }



    }
}
