﻿//
//  Checker.cs
//
//  Author:
//       Ondrej Rysavy <rysavy@fit.vutbr.cz>
//
//  Copyright (c) 2014 (c) Brno University of Technology
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Lesser General Public License as published by
//  the Free Software Foundation, either version 3 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Lesser General Public License for more details.
//
//  You should have received a copy of the GNU Lesser General Public License
//  along with this program.  If not, see <http://www.gnu.org/licenses/>.


namespace Netifier.FilterConflictChecker
{
	using System;
	using System.Collections.Generic;
	using System.IO;
	using System.Linq;
	using System.Text;
	using System.Threading.Tasks;
	using Microsoft.Formula.API;    
	using Microsoft.Formula.API.Generators;
	using Microsoft.Formula.API.Nodes;
	using Microsoft.Formula.Common.Terms;
	using Microsoft.Formula.Common;
	using Netifier.DataModels;

	/// <summary>
	/// Helper class that enables to create and query Models for Domain associated with this class.
	/// </summary>
	public class Checker : IDisposable
	{
		Env _4mlEnvironment = new Env();

		string _domainName;
		ProgramName _domainProgramName;

		static string _dynamicObjectsDirectory = Directory.GetCurrentDirectory();
		/// <summary>
		/// Initializes a new instance of the <see cref="Netifier.FilterConflictChecker.Checker"/> class.
		/// </summary>
		/// <param name="path">Path of the program file containing domain module.</param>
		/// <param name="domainName">Domain module name.</param>
		private Checker (string domainName, string path)
		{
			this._domainProgramName = new ProgramName("file://"+ path);
			this._domainName = domainName;
		}

		#region IDisposable implementation

		public void Dispose ()
		{
			this._4mlEnvironment = null;
		}

		#endregion

		/// <summary>
		/// Create new instance of Checker class. If initialization failed null is returned.
		/// </summary>
		/// <param name="domainName">Domain name.</param>
		/// <param name="path">Path to program file containing specified Domain.</param>
		public static Checker Create(string domainName, string path)
		{
			var c = new Checker (domainName, path);
			var r = c.installDomainProgram ();
			if (r) {
				return c;
			} else {
				c.Dispose ();
				return null;
			}
		}

		/// <summary>
		/// Loads the domain definition. It creates a domain into which 
		/// model can be loaded and then analyzed.
		/// </summary>
		/// <returns><c>true</c>, if domain definition was loaded, <c>false</c> otherwise.</returns>
		/// <param name="objects">Objects.</param>
		private bool installDomainProgram()
		{
			InstallResult res;
			_4mlEnvironment.Install (this._domainProgramName.Uri.AbsolutePath, out res);
			if (res == null) { return false; }

			foreach (var f in res.Flags) {
				Console.WriteLine ("{0} ({1}, {2}) : {3} {4} : {5}",
					f.Item2.ProgramName,
					f.Item2.Span.StartLine,
					f.Item2.Span.StartCol,
					f.Item2.Severity,
					f.Item2.Code,
					f.Item2.Message);
			}
				
			if (res.Succeeded) {
				Console.WriteLine ("Program {0} installed.", _domainProgramName);
				return true;
			} else {
				Console.WriteLine ("Could not install file; exiting");
				return false;
			}
		}

		/// <summary>
		/// Loads the model form the specified file.
		/// </summary>
		/// <returns><c>true</c>, if model was loaded, <c>false</c> otherwise.</returns>
		/// <param name="filename">Filename that contains model definition.</param>
		/// <param name="modelName">Model name.</param>
		/// <param name="objects">Objects.</param>
		bool LoadModel(string filename, string modelName, out List<ICSharpTerm> objects)
		{
			objects = null;
			var modelProgramName = new ProgramName (filename);
			Task<ObjectGraphResult> createTask;
			if (!Netifier.DataModels.Firewall_Root.CreateObjectGraph(_4mlEnvironment, modelProgramName, modelName, out createTask))
			{
				Console.WriteLine("Could not start object graph creation");
				return false;
			}

			createTask.Wait();
			foreach (var f in createTask.Result.Flags)
			{
				Console.WriteLine("({0}, {1}) : {2} {3} : {4}",
					f.Span.StartLine,
					f.Span.StartCol,
					f.Severity,
					f.Code,
					f.Message);
			}

			if (!createTask.Result.Succeeded)
			{
				Console.WriteLine("Could not create object graph of the domain; exiting");
				return false;
			}

			objects = createTask.Result.Objects;

			return true;
		}

		/// <summary>
		/// Gets the term that comprise of a predicate of the given name.
		/// </summary>
		/// <returns>The term.</returns>
		/// <param name="pt">Point.</param>
		/// <param name="name">Name.</param>
		public IEnumerable<Term> GetProofTerms(ProofTree pt, string name, bool topMatchOnly = true)
		{
			bool match = false;
			var c = pt.Conclusion;
			if (String.Equals (name, c.Symbol.PrintableName)) {
				yield return c;
				match = true;
			}
			if (topMatchOnly && match) {
				yield break;
			} else {
				foreach (var p in pt.Premises) {
					foreach (var t in GetProofTerms (p.Value, name, topMatchOnly))
						yield return t;
				}
			}
		}

		/// <summary>
		/// Query goals in the specified model.
		/// </summary>
		/// <param name="modelName">Model name.</param>
		/// <param name="goals">Goals to be evaluated in the specified model.</param>
		public Tuple<LiftedBool,IEnumerable<ProofTree>> Query(string modelName, params string[] goals)
		{
			bool errorOccured = false;
			List<AST<Node>> parsedGoals = new List<AST<Node>> ();
			foreach (var goal in goals) {
				Microsoft.Formula.Common.ImmutableCollection<Flag> flags;
				var parsedGoal = Factory.Instance.ParseDataTerm (goal, out flags);
				if (parsedGoal == null) {
					Console.Error.WriteLine ("ERROR: Cannot parse query:");
					foreach (var f in flags) {
						Console.Error.WriteLine ("{0} ({1}, {2}) : {3} {4} : {5}",
							f.ProgramName,
							f.Span.StartLine,
							f.Span.StartCol,
							f.Severity,
							f.Code,
							f.Message);
					}
					errorOccured = true;
				}
				parsedGoals.Add (parsedGoal);
			}

			if (errorOccured)
				return null;

			var programName = this.GetModelProgramName (modelName);


			var body = Factory.Instance.MkBody ();
			foreach (var goal in parsedGoals) {
				body = Factory.Instance.AddConjunct (body, Factory.Instance.MkFind (null, goal));
			}

			var queryTerms = new AST<Body> [] { body };

			List<Flag> queryFlags;
			Task<QueryResult> queryTask;
			Microsoft.Formula.Common.Rules.ExecuterStatistics exeStats;
			var res = _4mlEnvironment.Query (programName, modelName, queryTerms, true, true, out queryFlags, out queryTask, out exeStats);
			if (!res || queryTask == null) {
				Console.Error.WriteLine ("ERROR: Cannot execute query:");
				foreach (var f in queryFlags)
				{
					Console.Error.WriteLine("{0} ({1}, {2}) : {3} {4} : {5}",
						f.ProgramName,
						f.Span.StartLine,
						f.Span.StartCol,
						f.Severity,
						f.Code,
						f.Message);
				}
				errorOccured = true;
			}

			if (errorOccured)
				return null;

			System.Diagnostics.Stopwatch swatch = new System.Diagnostics.Stopwatch ();
			Console.Write ("\rExecuting query...");
			swatch.Start ();
			queryTask.Start ();
			queryTask.Wait();
			swatch.Stop ();
			Console.WriteLine("\rExecuting query completed. Execution time was {0}ms.               ", swatch.ElapsedMilliseconds);

			var result = queryTask.Result;
			if (result != null) {
				var proofTrees = result.EnumerateProofs (string.Format("{0}.requires", result.Source.Node.Name), out queryFlags);
				return new Tuple<LiftedBool, IEnumerable<ProofTree>> (result.Conclusion, proofTrees);
			}
			return new Tuple<LiftedBool, IEnumerable<ProofTree>> (LiftedBool.Unknown, null);
		}

		/// <summary>
		/// Creates and installs the model as a dynamic program.
		/// </summary>
		/// <returns><c>true</c>, if model was installed, <c>false</c> otherwise.</returns>
		/// <param name="modelName">Model name.</param>
		/// <param name="facts">Facts.</param>
		public bool CreateAndInstallModel(string modelName, IEnumerable<ICSharpTerm> facts)
		{
			List<ICSharpTerm> gndTerms = new List<ICSharpTerm>();
			if (facts != null)
				gndTerms.AddRange (facts);
			AST<Model> modelNode;

			if (!Factory.Instance.MkModel (modelName, _domainName, gndTerms, out modelNode, null, _domainProgramName.Uri.AbsolutePath)) {
				Console.Error.WriteLine("Cannot create model from provided facts.");
				return false;
			}

			var modelProgramName = new ProgramName ("file://" + Path.Combine(_dynamicObjectsDirectory, modelName + ".4ml"), false);
			var program = Factory.Instance.AddModule (Factory.Instance.MkProgram(modelProgramName), modelNode);

			var modelfilepath = System.IO.Path.GetFullPath (modelProgramName.Uri.AbsolutePath);
				using (var file = new System.IO.StreamWriter (modelfilepath)) {
				program.Print (file);
			}

			InstallResult result;
			this._4mlEnvironment.Install(program, out result);

			if (result.Succeeded) {
				Console.WriteLine ("Sucessfully installed model program {0}.", modelName);
				this.installedPrograms.Add (modelName, modelProgramName);
				return true;
			} else {
				foreach (var f in result.Flags) {
					Console.Error.WriteLine ("{0} ({1}, {2}) : {3} {4} : {5}",
						f.Item2.ProgramName,
						f.Item2.Span.StartLine,
						f.Item2.Span.StartCol,
						f.Item2.Severity,
						f.Item2.Code,
						f.Item2.Message);
				}
				return false;
			}
		}

		/// <summary>
		/// The collection of installed programs.
		/// </summary>
		Dictionary<string,ProgramName> installedPrograms = new Dictionary<string, ProgramName> ();

		/// <summary>
		/// Gets the name of the model program.
		/// </summary>
		/// <returns>The model program name.</returns>
		/// <param name="modelName">Model name.</param>
		ProgramName GetModelProgramName(string modelName)
		{
			ProgramName programName = null;
			this.installedPrograms.TryGetValue (modelName, out programName);
			return programName;
		}
	}
}

