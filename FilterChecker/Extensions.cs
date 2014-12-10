//
//  Extensions.cs
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
using System;
using System.Net;
using System.Net.Sockets;
namespace Netcow.Extensions
{
	public static class Extensions {
		public static uint ToUInt32(this IPAddress ipa)
		{
			if (ipa.AddressFamily != AddressFamily.InterNetwork)
				throw new ArgumentException ("Cannot call this method on address other than InterNetwork (IPv4).","ipa");
			uint ip = (uint)IPAddress.NetworkToHostOrder(
				(int)System.BitConverter.ToUInt32(
					ipa.GetAddressBytes(), 0));
			return ip;
		}
	}
}

