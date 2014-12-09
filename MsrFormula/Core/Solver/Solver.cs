﻿namespace Microsoft.Formula.Solver
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics.Contracts;
    using System.Numerics;
    using System.Threading;
    using System.Threading.Tasks;

    using API;
    using API.Nodes;
    using API.Plugins;
    using Compiler;
    using Common;
    using Common.Rules;
    using Common.Terms;
    using Common.Extras;

    //// Aliases for Z3 types to avoid clashes
    using Z3Context = Microsoft.Z3.Context;
    using Z3Solver = Microsoft.Z3.Solver;
    using Z3Sort = Microsoft.Z3.Sort;
    using Z3Expr = Microsoft.Z3.Expr;
    using Z3BoolExpr = Microsoft.Z3.BoolExpr;
    using Z3RealExpr = Microsoft.Z3.RealExpr;
    using Z3IntExpr = Microsoft.Z3.IntExpr;
    using Z3Symbol = Microsoft.Z3.Symbol;
    using Z3Model = Microsoft.Z3.Model;
    using Z3RatNum = Microsoft.Z3.RatNum;

    internal class Solver : ISolver, IDisposable
    {
        private CancellationToken cancel;
        private bool disposed = false;
        private List<Flag> solverFlags = new List<Flag>();

        public CardSystem Cardinalities
        {
            get;
            private set;
        }

        public Configuration Configuration
        {
            get { return (Configuration)Source.Config.CompilerData; }
        }

        public SymbolTable SymbolTable
        {
            get { return PartialModel.Index.SymbolTable; }
        }

        internal IEnumerable<Flag> Flags
        {
            get { return solverFlags; }
        }

        internal FactSet PartialModel
        {
            get;
            private set;
        }

        internal Model Source
        {
            get;
            private set;
        }

        internal Z3Context Context
        {
            get;
            private set;
        }

        internal Z3Solver Z3Solver
        {
            get;
            private set;
        }

        internal TypeEmbedder TypeEmbedder
        {
            get;
            private set;
        }

        internal TermIndex Index
        {
            get { return PartialModel.Index; }
        }

        /// <summary>
        /// The search strategy. Can be null if goal decided as Unsat prior to
        /// instantiation, or if Strategy.Begin(...) failed.
        /// </summary>
        private ISearchStrategy Strategy
        {
            get;
            set;
        }

        internal Solver(FactSet partialModel, Model source, CancellationToken cancel)
        {
            Contract.Requires(partialModel != null);
            Contract.Requires(source != null);
            this.cancel = cancel;

            Source = source;
            PartialModel = partialModel;

            //// Step 1. Create Z3 Context and Solver
            CreateContextAndSolver();

            //// Step 2. Create type embedder
            CreateTypeEmbedder();

            //// Step 3. Create cardinality system.
            Cardinalities = new CardSystem(partialModel);

            //// Step 4. Try to create the search strategy.
            if (!Cardinalities.IsUnsat)
            {
               Strategy = CreateStrategy(solverFlags);
            }

            var se = new SymExecuter(this);
        }

        public SearchState GetState(IEnumerable<KeyValuePair<UserSymbol, int>> dofs)
        {
            throw new NotImplementedException();
        }

        /// <summary>
        /// Returns false is no more models can be enumerated.
        /// </summary>
        internal bool GetModel()
        {
            if (Strategy == null)
            {
                return false;
            }

            return true;
        }

        public void Dispose()
        {
            Dispose(true);
            GC.SuppressFinalize(this);
        }

        private void CreateTypeEmbedder()
        {
            var conf = (Configuration)Source.Config.CompilerData;
            Cnst value;
            var costMap = new Map<BaseSortKind, uint>((x, y) => (int)x - (int)y);

            if (conf.TryGetSetting(Configuration.Solver_RealCostSetting, out value))
            {
                costMap[BaseSortKind.Real] = (uint)((Rational)value.Raw).Numerator;
            }
            else
            {
                costMap[BaseSortKind.Real] = 10;
            }

            if (conf.TryGetSetting(Configuration.Solver_StringCostSetting, out value))
            {
                costMap[BaseSortKind.String] = (uint)((Rational)value.Raw).Numerator;
            }
            else
            {
                costMap[BaseSortKind.String] = 10;
            }

            if (conf.TryGetSetting(Configuration.Solver_IntegerCostSetting, out value))
            {
                costMap[BaseSortKind.Integer] = (uint)((Rational)value.Raw).Numerator;
            }
            else
            {
                costMap[BaseSortKind.Integer] = 11;
            }

            if (conf.TryGetSetting(Configuration.Solver_NaturalCostSetting, out value))
            {
                costMap[BaseSortKind.Natural] = (uint)((Rational)value.Raw).Numerator;
            }
            else
            {
                costMap[BaseSortKind.Natural] = 12;
            }

            if (conf.TryGetSetting(Configuration.Solver_PosIntegerCostSetting, out value))
            {
                costMap[BaseSortKind.PosInteger] = (uint)((Rational)value.Raw).Numerator;
            }
            else
            {
                costMap[BaseSortKind.PosInteger] = 13;
            }

            if (conf.TryGetSetting(Configuration.Solver_NegIntegerCostSetting, out value))
            {
                costMap[BaseSortKind.NegInteger] = (uint)((Rational)value.Raw).Numerator;
            }
            else
            {
                costMap[BaseSortKind.NegInteger] = 13;
            }

            TypeEmbedder = new TypeEmbedder(PartialModel.Index, Context, costMap);
        }

        /// <summary>
        /// Create and set the solver. Will get more complicated as 
        /// params become clear.
        /// </summary>
        private void CreateContextAndSolver()
        {
            Context = new Z3Context();
            Z3Solver = Context.MkSolver();
        }

        /// <summary>
        /// Creates and sets the search strategy.
        /// </summary>
        private ISearchStrategy CreateStrategy(List<Flag> flags)
        {
            Contract.Requires(!Cardinalities.IsUnsat);

            var conf = (Configuration)Source.Config.CompilerData;
            ISearchStrategy strategy;
            Cnst activeStrategyName;
            if (conf.TryGetSetting(Configuration.Solver_ActiveStrategySetting, out activeStrategyName))
            {
                var result = conf.TryGetStrategyInstance((string)activeStrategyName.Raw, out strategy);
                Contract.Assert(result);
            }
            else
            {
                strategy = OATStrategy.TheFactoryInstance;
            }

            List<Flag> beginFlags;
            var inst = strategy.Begin(this, out beginFlags);
            if (beginFlags != null)
            {
                flags.AddRange(beginFlags);
            }

            return inst;
        }

        /// <summary>
        /// TODO: Need to recheck this dispose logic
        /// </summary>
        protected void Dispose(bool disposing)
        {
            if (!disposed)
            {
                if (disposing && Context != null)
                {
                    Context.Dispose();
                }

                if (disposing && Z3Solver != null)
                {
                    Z3Solver.Dispose();
                }
            }

            disposed = true;
        }
    }
}
