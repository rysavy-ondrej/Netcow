
namespace Netcow.FilterChecker
{
	using System;
	using System.Collections.Generic;
	using System.IO;
	using System.Linq;
	using System.Text;
	using System.Threading.Tasks;
	using ConsoleFx;
	using ConsoleFx.Programs.Simple;
	using ConsoleFx.Validators;
	using Netcow.Parsers;
	using DataModels;
	using LiftedBool = Microsoft.Formula.Common.LiftedBool;
	class Program
	{
		/// <summary>
		/// This is main program method.
		/// </summary>
		private static int Handler()
		{
			Console.WriteLine ("Processing {0}...", configFilePath);
			var config = CliConfigParser.TryParseFile (configFilePath, Console.Error);
			if (config != null) {
				var accessLists = from c in config.Value
				                  where String.Equals (c.CmdName, "access-list", StringComparison.InvariantCultureIgnoreCase)
				                  select AccessListParser.TryParseString (c.Command);

				var accessGroups = from item in accessLists.Where (x => x != null)
				                   group item.Value by item.Value.Id into g
				                   select new AccessGroup{ GroupName = g.Key, Rules = g };

				var mdlName = Path.GetFileNameWithoutExtension (configFilePath);
				var checker = CheckerFactory.CreateAclModelChecker (mdlName, accessGroups); 
				var query = String.Empty;
				var pred = String.Empty;
				switch (conflictType) {
				case ConflictType.Shadowing:
					query = "shadowing(f,p,q)";
					pred = "shadowing";
					break;
				default:
					query = "conflict(f,i,j,c)";
					pred = "conflict";
					break;
				}
				var res = checker.Query (mdlName, query);
				if (res.Item1 == LiftedBool.False) {
					Console.WriteLine ("No conflicts found.");
				}
				foreach (var proofTree in res.Item2) {
					foreach (var term in checker.GetProofTerms(proofTree, pred)) {
						term.PrintTerm (Console.Out);
						Console.WriteLine ();
					}
				}
			} else {
				Console.Error.WriteLine ("Error when parsing input configuration file.");
			}
			return 0;
		}
		private static void ErrorHandler(Exception ex)
		{
			Console.Error.WriteLine (ex.Message);
		}

		public enum ConflictType { All, Shadowing, Correlation, Generalization, Redundancy };

		private static ConflictType conflictType = ConflictType.All;
		private static string configFilePath = null;

		public static int Main (string[] args)
		{
			var app = new ConsoleProgram(Handler,
				includeHelpSupport: true,
				commandGrouping: CommandGrouping.DoesNotMatter,
				displayUsageOnError: true);
			try
			{
				/// option
				app.AddOption("conflict", "c", expectedParameters:1)
					.ValidateWith(new EnumValidator<ConflictType> { ErrorMessage = "Invalid conflict type. Specify All or Errors" })
					.AssignTo(() => conflictType);
				/// filename 
				app.AddArgument(false)
					.ValidateWith(new PathValidator(checkIfExists: true))
					.ValidateWith(new CustomValidator(arg => Path.GetExtension(arg).Equals(".cfg", StringComparison.OrdinalIgnoreCase)))
					.AssignTo(() => configFilePath);

				app.SetUsageBuilder<SimpleResourceUsageBuilder>();
				return app.Run();
			}
			catch (Exception ex)
			{
				return app.HandleError(ex);
			}
		}
	}
}
