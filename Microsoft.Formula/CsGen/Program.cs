//
//  Program.cs
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

namespace Formula.CsGen
{
	using System;
	using System.IO;
	using System.Threading;
	using  Microsoft.Formula.API;
	using Microsoft.Formula.CommandLine;

	class MainClass
	{

		public class AutoChooser : IChooser
		{
			public bool GetChoice(out DigitChoiceKind choice)
			{
					choice = DigitChoiceKind.Zero;
					return true;
			}
		}

		public static void Main(string[] args)
		{
			if (args.Length != 2) {
				System.Console.Error.WriteLine ("Error: Incorrect or missing arguments.");
				System.Console.Error.WriteLine ("Usage: fornula.csgen <input-file.4ml> <output-file.cs>");
				Environment.Exit (-1);			
			}
			var inputfilepath = args [0];
			var outputfilepath = args [1];

			var mdlname = Path.GetFileNameWithoutExtension (inputfilepath);

			if (!File.Exists (inputfilepath)) {
				System.Console.Error.WriteLine ("Error: Specified input file '{0}' cannot be found.", inputfilepath);
				Environment.Exit (-1);
			}

			System.Console.WriteLine ("{0} -> {1}", inputfilepath, outputfilepath);

			var sink = new CommandLineProgram.ConsoleSink ();
			var chooser = new AutoChooser ();
			var envParams = new EnvParams ();
			using (var ci = new CommandInterface (sink, chooser, envParams)) {
				Console.CancelKeyPress += (x, y) => { 
					y.Cancel = true;
					ci.Cancel ();                 
				};
				
				var loadfile = String.Format ("load {0}", inputfilepath);
				var generate = String.Format ("generate {0}", mdlname);
				var result = ci.DoCommand (loadfile);

				if (!result) {
					System.Console.Error.WriteLine ("Error: Input file cannot be loaded.");
					Environment.Exit (-1);
				}
				// create file here:
				using (var tw = new StreamWriter (outputfilepath)) {
					sink.Writer = tw; 
					result = ci.DoCommand (generate);
					sink.Writer = Console.Out;
					if (!result) {
						System.Console.Error.WriteLine ("Error: Cannot generate csharp source code for the specified domain module.");
						Environment.Exit (-1);					
					}
				}
			}
		}
	}
}
