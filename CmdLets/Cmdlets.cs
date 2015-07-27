using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Reflection;
using Fclp;
namespace Netcow.Commands
{
    public class Command
    {
        public string Name { get; set; }
        public MethodInfo MethodInfo { get;  set; }
        public Command(string name, MethodInfo methodInfo)
        {
            this.Name = name;
            this.MethodInfo = methodInfo;
        }

        void Foo()
        {
            var p = new Fclp.FluentCommandLineParser();
            p.Setup<int>('s').Callback(x => x = x);
        }

        void setupArgument(FluentCommandLineParser parser, int id, char sname, string fname, Type type, bool isRequired, string description)
        {
            var parserType = parser.GetType();
            var optType1 = typeof(ICommandLineOptionFluent<object>).GetGenericTypeDefinition();
            
            var optType = optType1.MakeGenericType(new Type[] { type });

            var setupMethod = parserType.GetMethod("Setup", new Type[] { typeof(char), typeof(string) })
                                        .MakeGenericMethod(new Type[] { type });

            var optObj = setupMethod.Invoke(parser, new object[] { sname, fname });

            var callbackMethod = typeof(Fclp.ICommandLineOptionFluent<object>).GetGenericTypeDefinition().MakeGenericType(type).GetMethod("Callback");

            var setPar1 = typeof(Command).GetMethod("setParameter", BindingFlags.Instance | BindingFlags.NonPublic );
            var setPar = setPar1.MakeGenericMethod(new Type[] { type }).Invoke(this, new object[]{ id });

            callbackMethod.Invoke(optObj, new object[] { setPar });
            
            if (isRequired)
            {
                var requiredMethod = optType.GetMethod("Required");
                requiredMethod.Invoke(optObj, new object[] { });
            }
        }
        Action<T> setParameter<T>(int id)
        {
            return new Action<T>(x => parameters[id] = (object)x);
        }
        object[] parameters;
        public void ParseArguments(string []args)
        {
            parameters = new object[this.MethodInfo.GetParameters().Count()];
            for (int i = 0; i < parameters.Count(); i++)
                parameters[i] = Type.Missing;

            var parser = new FluentCommandLineParser();
            parser.IsCaseSensitive = false;
                        
            foreach (var p in this.MethodInfo.GetParameters())
            {
                var s = p.Name[0];
                setupArgument(parser, p.Position, s, p.Name, p.ParameterType, !p.IsOptional, String.Empty);                       
            }              
            var result = parser.Parse(args);
            if (result.HasErrors)
            {
                throw new ArgumentException(result.ErrorText);
            }
        }
        /// <summary>
        /// Executes command using parser arguments as its input.
        /// </summary>
        public object Execute()
        {
            return this.MethodInfo.Invoke(null, parameters);
        }
    }
    public class CmdletManager
    {

        public static string Usage { get; set; }

        public static IEnumerable<Command> GetAllCmdlets()
        {
            Assembly a = Assembly.GetEntryAssembly();
            Type[] types = a.GetTypes();

            foreach (Type t in types)
            {
                var cmdlets = from m in t.GetMethods()
                              where m.GetCustomAttribute<CmdletAttribute>() != null
                              select new { Method = m, Info = m.GetCustomAttribute<CmdletAttribute>() };
                foreach (var c in cmdlets)
                {
                    var name = String.Format("{0}-{1}", c.Info.VerbName, c.Info.NounName);
                    yield return new Command(name, c.Method);
                }
            }
        }

        public static void Run(string[] args)
        {
            if (args == null || args.Count() == 0)
            {
                throw new ArgumentException("Missing command.");
            }

            var cmd = GetAllCmdlets().FirstOrDefault(x => x.Name.Equals(args[0],StringComparison.InvariantCultureIgnoreCase));
            if (cmd != null)
            {
                var left = new string[args.Count() - 1];
                Array.ConstrainedCopy(args, 1, left, 0, args.Count() - 1);
                cmd.ParseArguments(left);
                cmd.Execute(); 
            }
            else
            {
                throw new ArgumentException("Invalid command.");
            }
        }
    }


    public class CmdargAttribute : Attribute
    {
        public string ShortName { set; get; }
        public string FullName { set; get; }
        public string Description { set; get; }
        public CmdargAttribute(string shortName, string fullName, string description = "")
        {
            this.ShortName = shortName;
            this.FullName = fullName;
            this.Description = description;
        }
    }

    public class CmdletAttribute : Attribute
    {
        public string VerbName { set; get; }
        public string NounName { set; get; }

        public string Description { set; get; }
        public CmdletAttribute(string verbName, string nounName, string description="")
        {
            this.VerbName = verbName;
            this.NounName = nounName;
            this.Description = description;
        }
    }
}
