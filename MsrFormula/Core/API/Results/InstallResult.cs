﻿namespace Microsoft.Formula.API
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics.Contracts;
    using System.Linq;
    using System.Text;
    using System.Threading;
    using System.Threading.Tasks;

    using Common;
    using Nodes;

    public sealed class InstallResult
    {
        private Map<ProgramName, InstallStatus> touched = 
            new Map<ProgramName, InstallStatus>(ProgramName.Compare);

        /// <summary>
        /// Maintains the order in which files were touched.
        /// </summary>
        private LinkedList<InstallStatus> touchedOrder = new LinkedList<InstallStatus>();

        private List<Tuple<AST<Program>, Flag>> flags = new List<Tuple<AST<Program>, Flag>>();

        /// <summary>
        /// True if this install operation succeeded.
        /// </summary>
        public bool Succeeded
        {
            get;
            internal set;
        }

        /// <summary>
        /// A list of the programs that were touched during this install operation.
        /// </summary>
        public IEnumerable<InstallStatus> Touched
        {
            get
            {
                return touchedOrder;
            }
        }

        /// <summary>
        /// A list of flags produced during installation.
        /// </summary>
        public IEnumerable<Tuple<AST<Program>, Flag>> Flags
        {
            get;
            private set;
        }

        public bool TryGetStatus(ProgramName name, out InstallStatus status)
        {
            Contract.Requires(name != null);
            return touched.TryFindValue(name, out status);
        }

        internal InstallResult()
        {
            Flags = new ImmutableCollection<Tuple<AST<Program>, Flag>>(flags);
        }

        internal void AddTouched(AST<Program> p, InstallKind kind)
        {
            Contract.Requires(p != null);
            InstallStatus status;
            if (!touched.TryFindValue(p.Node.Name, out status))
            {
                var inst = new InstallStatus(p, kind);
                touched.Add(p.Node.Name, inst);
                touchedOrder.AddLast(inst);
            }
            else if (status.Status == InstallKind.Failed || kind == InstallKind.Failed)
            {
                status.Status = InstallKind.Failed;
            }
        }

        internal void Union(InstallResult res)
        {
            Contract.Requires(res != null);

            if (res == this)
            {
                return;
            }

            Succeeded = Succeeded && res.Succeeded;
            flags.AddRange(res.flags);

            foreach (var kv in res.touched)
            {
                AddTouched(kv.Value.Program, kv.Value.Status);
            }
        }

        internal void AddFlag(AST<Program> p, Flag flag)
        {
            Contract.Requires(p != null && flag != null);
            flags.Add(new Tuple<AST<Program>, Flag>(p, flag));
            if (flag.Severity == SeverityKind.Error)
            {
                if (p.Node.Name == ProgramName.ApiErrorName && 
                    !touched.ContainsKey(ProgramName.ApiErrorName))
                {
                    var inst = new InstallStatus(p, InstallKind.Failed);
                    touched.Add(ProgramName.ApiErrorName, inst);
                    touchedOrder.AddLast(inst);
                }

                touched[p.Node.Name].Status = InstallKind.Failed;
                Succeeded = false;
            }
        }

        internal void AddFlags(ParseResult pr)
        {
            Contract.Requires(pr != null);
            foreach (var f in pr.Flags)
            {
                AddFlag(pr.Program, f);
            }
        }

        internal void AddFlags(AST<Program> p, IEnumerable<Flag> flags)
        {
            Contract.Requires(p != null);
            if (flags == null)
            {
                return;
            }

            foreach (var f in flags)
            {
                AddFlag(p, f);
            }
        }
    }
}
