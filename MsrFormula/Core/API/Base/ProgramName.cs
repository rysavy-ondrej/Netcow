﻿namespace Microsoft.Formula.API
{
    using System;
    using System.Collections.Generic;
    using System.Diagnostics.Contracts;
    using System.Runtime.Serialization;
    using System.Linq;
    using System.Text;

    public sealed class ProgramName
    {
        internal static readonly char[] UriSeparators = new char[] { '\\', '/' };

        private static readonly Uri envScheme = new Uri("env://", UriKind.Absolute);

        private static readonly Uri fileScheme = new Uri("file://", UriKind.Absolute);

        private static readonly Uri apiErrorUri = new Uri("api://unknowncaller.4ml");

        private static readonly ProgramName apiErrorName = new ProgramName();

        private readonly Uri workingUri;

        public static Uri EnvironmentScheme
        {
            get { return envScheme; }
        }

        public static Uri FileScheme
        {
            get { return fileScheme; }
        }

        public Uri Uri
        {
            get;
            private set;
        }

        /// <summary>
        /// Provides a distinct program name for an unknown caller of the API.
        /// </summary>
        internal static ProgramName ApiErrorName
        {
            get { return apiErrorName; }
        }

        public bool IsFileProgramName
        {
            get { return Uri.Scheme == FileScheme.Scheme; }
        }

        public ProgramName(string uriString, bool relativeToWorkingDir = true)
        {
            Contract.Requires(uriString != null);
            uriString = uriString.Trim().ToLowerInvariant().Replace('\\', '/');
            workingUri = new Uri(string.Format("{0}/", Environment.CurrentDirectory.ToLowerInvariant().Replace('\\', '/')), UriKind.Absolute);
            Uri = new Uri(relativeToWorkingDir ? workingUri : envScheme, uriString);

            if (!Uri.AbsoluteUri.StartsWith(fileScheme.AbsoluteUri) &&                
                !Uri.AbsoluteUri.StartsWith(envScheme.AbsoluteUri))
            {
                throw new Exception("Invalid program name scheme; must be file or env.");
            }
        }

        public ProgramName(string uriString, ProgramName relativeToProgram)
        {
            Contract.Requires(uriString != null && relativeToProgram != null);
            uriString = uriString.Trim().ToLowerInvariant().Replace('\\', '/');
            workingUri = new Uri(string.Format("{0}/", Environment.CurrentDirectory.ToLowerInvariant().Replace('\\', '/')), UriKind.Absolute);
            Uri = new Uri(relativeToProgram.Uri, uriString);

            if (!Uri.AbsoluteUri.StartsWith(fileScheme.AbsoluteUri) &&
                !Uri.AbsoluteUri.StartsWith(envScheme.AbsoluteUri))
            {
                throw new Exception("Invalid program name scheme; must be file or env.");
            }
        }

        /// <summary>
        /// Used to construct a program name representing a caller of the API without any additional context.
        /// </summary>
        private ProgramName()
        {
            Uri = apiErrorUri;
        }

        public override string ToString()
        {
            return Uri.AbsoluteUri.ToLowerInvariant();
        }

        public string ToString(EnvParams envParams)
        {
            if (EnvParams.GetBoolParameter(envParams, EnvParamKind.Msgs_SuppressPaths))
            {
                var segs = Uri.Segments;
                return segs[segs.Length - 1].ToLowerInvariant();
            }
            else
            {
                return ToString();
            }
        }

        public override bool Equals(object obj)
        {
            return obj == this ||
                   (obj is ProgramName && 
                    string.CompareOrdinal(((ProgramName)obj).Uri.AbsoluteUri.ToLowerInvariant(), Uri.AbsoluteUri.ToLowerInvariant()) == 0);
        }

        public override int GetHashCode()
        {
            return Uri.AbsoluteUri.ToLowerInvariant().GetHashCode();
        }

        public static int Compare(ProgramName n1, ProgramName n2)
        {
            Contract.Requires(n1 != null && n2 != null);
            return n1 == n2 ? 0 : string.CompareOrdinal(n1.ToString(), n2.ToString());
        }
    }
}
