// ----------------------------------------------------------------------------------------------
// Copyright 2016 Mårten Rånge
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// ----------------------------------------------------------------------------------------------

// Inspired by Clojure's Persistent Hash Map (https://github.com/clojure/clojure/blob/master/src/jvm/clojure/lang/PersistentHashMap.java)
//  and Phil Bagwell's Ideal Hash Trie (http://lampwww.epfl.ch/papers/idealhashtrees.pdf)
//  and http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel

namespace PHM.CS
{
  using System;
  using System.Collections;
  using System.Collections.Generic;
  using System.Diagnostics;
  using System.Globalization;
  using System.Runtime.CompilerServices;
  using System.Text;

  public partial interface IPersistentHashMap<K, V> : IEnumerable<KeyValuePair<K, V>>
    where K : IEquatable<K>
  {
#if TEST_BUILD
    bool                      CheckInvariant  ();
#endif
    bool                      IsEmpty         { get; }
    bool                      Visit           (Func<uint, K, V, bool> r);
    IPersistentHashMap<K, V>  Set             (K k, V v);
    bool                      TryFind         (K k, out V v);
    IPersistentHashMap<K, V>  Unset           (K k);
  }

  public static partial class PersistentHashMap
  {
    public static IPersistentHashMap<K, V> Empty<K, V> ()
      where K : IEquatable<K>
    {
      return BaseNode<K ,V>.EmptyNode;
    }

    internal const int TrieShift    = 4                 ;
    internal const int TrieMaxShift = 32                ;
    internal const int TrieMaxNodes = 1 << TrieShift    ;
    internal const int TrieMask     = TrieMaxNodes - 1  ;

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static uint LocalHash (uint h, int s)
    {
      return (h >> s) & TrieMask;
    }

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static uint Bit (uint h, int s)
    {
      return 1U << (int) LocalHash (h, s);
    }

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static uint PopCount (uint v)
    {
      // From: http://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetParallel
      //  many cpus support popcount natively but that isn't available in IL
      v -=  ((v >> 1) & 0x55555555);
      v =   (v & 0x33333333) + ((v >> 2) & 0x33333333);
      v =   ((v + (v >> 4) & 0xF0F0F0F) * 0x1010101) >> 24;
      return v;
    }

    internal static string FormatWith (this string format, params object[] args)
    {
      return string.Format (CultureInfo.InvariantCulture, format, args);
    }

    internal static StringBuilder IndentedLine (this StringBuilder sb, int indent, string line)
    {
      sb.Append (' ', indent);
      sb.AppendLine (line);
      return sb;
    }

    internal static StringBuilder FormatIndentedLine (this StringBuilder sb, int indent, string format, params object[] args)
    {
      return sb.IndentedLine (indent, format.FormatWith (args));
    }

    internal static bool CheckHash (uint h, uint ah, int s)
    {
      return (h & ((1 << s) - 1)) == ah;
    }

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static T[] CopyArray<T> (T[] vs)
    {
      var nvs = new T[vs.Length];
      for (var iter = 0; iter < vs.Length; ++iter)
      {
        nvs[iter] = vs[iter];
      }
      return nvs;
    }

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static T[] CopyArrayMakeHoleLast<T> (T[] vs)
    {
      var nvs = new T[vs.Length + 1];
      for (var iter = 0; iter < vs.Length; ++iter)
      {
        nvs[iter] = vs[iter];
      }
      return nvs;
    }

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static T[] CopyArrayMakeHole<T> (uint holebit, uint bitmap, T[] vs)
    {
      Debug.Assert ((holebit & bitmap) == 0);
      Debug.Assert (PopCount (bitmap) == vs.Length);

      var holemask  = holebit - 1;
      var nvs       = new T[vs.Length + 1];
      var iter      = 0;

      for (; (bitmap & holemask) != 0; ++iter)
      {
        bitmap &= bitmap - 1;
        nvs[iter] = vs[iter];
      }

      for (; iter < vs.Length; ++iter)
      {
        nvs[iter + 1] = vs[iter];
      }

      return nvs;
    }

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static T[] CopyArrayRemoveHole<T> (int at, T[] vs)
    {
      Debug.Assert (at < vs.Length);
      Debug.Assert (vs.Length > 1);

      var nvs = new T[vs.Length - 1];
      for (var iter = 0; iter < at; ++iter)
      {
        nvs[iter] = vs[iter];
      }

      for (var iter = at; iter < nvs.Length; ++iter)
      {
        nvs[at] = vs[at + 1];
      }

      return nvs;
    }

    [MethodImpl (MethodImplOptions.AggressiveInlining)]
    internal static T[] CopyArrayRemoveHole<T> (uint holebit, uint bitmap, T[] vs)
    {
      Debug.Assert ((holebit & bitmap) != 0);
      Debug.Assert (PopCount (bitmap) == vs.Length);
      Debug.Assert (vs.Length > 0);

      var holemask  = holebit - 1;
      var nvs       = new T[vs.Length - 1];
      var iter      = 0;

      for (; (bitmap & holemask) != 0; ++iter)
      {
        bitmap &= bitmap - 1;
        nvs[iter] = vs[iter];
      }

      for (; iter < nvs.Length; ++iter)
      {
        nvs[iter] = vs[iter + 1];
      }

      return nvs;
    }

    internal abstract partial class BaseNode<K, V> : IPersistentHashMap<K ,V>
      where K : IEquatable<K>
    {
      public static readonly EmptyNode<K, V> EmptyNode = new EmptyNode<K, V> ();

      bool IPersistentHashMap<K, V>.IsEmpty
      {
        get
        {
          return Empty ();
        }
      }

      bool IPersistentHashMap<K, V>.Visit (Func<uint, K, V, bool> r)
      {
        if (r != null)
        {
          return Receive (r);
        }
        else
        {
          return true;
        }
      }

      IPersistentHashMap<K, V> IPersistentHashMap<K ,V>.Set (K k, V v)
      {
        return Set (0, new KeyValueNode<K, V> ((uint)k.GetHashCode (), k, v));
      }

      bool IPersistentHashMap<K ,V>.TryFind (K k, out V v)
      {
        return TryFind ((uint)k.GetHashCode (), 0, k, out v);
      }

      public IPersistentHashMap<K, V> Unset (K k)
      {
        return Unset ((uint)k.GetHashCode (), 0, k) ?? EmptyNode;
      }

#if TEST_BUILD
      bool IPersistentHashMap<K ,V>.CheckInvariant ()
      {
        return CheckInvariant (0, 0);
      }
#endif

      public IEnumerator<KeyValuePair<K, V>> GetEnumerator ()
      {
        var vs = new List<KeyValuePair<K, V>> (16);

        Receive ((h,k,v) =>
          {
            var kv = new KeyValuePair<K, V> (k, v);
            vs.Add (kv);
            return true;
          });

        for (var iter = 0; iter < vs.Count; ++iter)
        {
          var v = vs[iter];
          yield return v;
        }
      }

      IEnumerator IEnumerable.GetEnumerator ()
      {
        return GetEnumerator ();
      }

      #if TEST_BUILD
      public override string ToString ()
      {
        var sb = new StringBuilder (16);
        Describe (sb, 0);
        return sb.ToString ();
      }
#endif

#if TEST_BUILD
      internal abstract bool            CheckInvariant  (uint h, int s);
      internal abstract void            Describe        (StringBuilder sb, int indent);
#endif
      internal virtual  bool            Empty           ()
      {
        return false;
      }
      internal abstract bool            Receive         (Func<uint, K, V, bool> r);
      internal abstract BaseNode<K, V>  Set             (int s, KeyValueNode<K, V> n);
      internal abstract bool            TryFind         (uint h, int s, K k, out V v);
      internal abstract BaseNode<K, V>  Unset           (uint h, int s, K k);
    }

    internal sealed partial class EmptyNode<K, V> : BaseNode<K, V>
      where K : IEquatable<K>
    {
#if TEST_BUILD
      internal override bool CheckInvariant (uint h, int s)
      {
        return true;
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        sb.IndentedLine (indent, "Empty");
      }
#endif
      internal override bool Empty ()
      {
        return true;
      }

      internal override bool Receive (Func<uint, K, V, bool> r)
      {
        return true;
      }

      internal sealed override BaseNode<K, V> Set (int s, KeyValueNode<K, V> n)
      {
        return n;
      }

      internal sealed override bool TryFind (uint h, int s, K k, out V v)
      {
        v = default (V);
        return false;
      }

      internal override BaseNode<K, V> Unset (uint h, int s, K k)
      {
        return null;
      }
    }

    internal sealed partial class KeyValueNode<K, V> : BaseNode<K, V>
      where K : IEquatable<K>
    {
      public readonly uint Hash  ;
      public readonly K    Key   ;
      public readonly V    Value ;

      [MethodImpl (MethodImplOptions.AggressiveInlining)]
      public KeyValueNode (uint h, K k, V v)
      {
        Hash  = h;
        Key   = k;
        Value = v;
      }

#if TEST_BUILD
      internal override bool CheckInvariant (uint h, int s)
      {
        return CheckHash (Hash, h, s) && (Hash == (uint)Key.GetHashCode ());
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        sb.FormatIndentedLine (indent, "KeyValue Hash:0x{0:X08}, Key:{1}, Value:{2}", Hash, Key, Value);
      }
#endif

      internal override bool Receive (Func<uint, K, V, bool> r)
      {
        return r (Hash, Key, Value);
      }

      internal sealed override BaseNode<K, V> Set (int s, KeyValueNode<K, V> n)
      {
        // TODO: Optimize if h,k and v are identical?

        // No need to check for reference equality as parent always creates new KeyValueNode
        var h = n.Hash;
        if (Hash == h && Key.Equals (n.Key))
        {
          // Replaces current node
          return n;
        }
        else if (Hash == h)
        {
          return HashCollisionNodeN<K ,V>.FromTwoNodes (h, this, n);
        }
        else
        {
          return BitmapNodeN<K ,V>.FromTwoNodes (s, Hash, this, h, n);
        }
      }

      internal sealed override bool TryFind (uint h, int s, K k, out V v)
      {
        if (Hash == h && Key.Equals (k))
        {
          v = Value;
          return true;
        }
        else
        {
          v = default (V);
          return false;
        }
      }

      internal override BaseNode<K, V> Unset (uint h, int s, K k)
      {
        if (Hash == h && Key.Equals (k))
        {
          return null;
        }
        else
        {
          return this;
        }
      }
    }

    internal sealed partial class BitmapNodeN<K, V> : BaseNode<K, V>
      where K : IEquatable<K>
    {
      public readonly uint              Bitmap  ;
      public readonly BaseNode<K, V>[]  Nodes   ;

      [MethodImpl (MethodImplOptions.AggressiveInlining)]
      public BitmapNodeN (uint b, BaseNode<K, V>[] ns)
      {
        Bitmap  = b ;
        Nodes   = ns;
      }

      [MethodImpl (MethodImplOptions.AggressiveInlining)]
      public static BitmapNodeN<K, V> FromNNodes (uint b, BaseNode<K, V>[] ns)
      {
        return new BitmapNodeN<K, V> (b, ns);
      }

      [MethodImpl (MethodImplOptions.AggressiveInlining)]
      public static BitmapNodeN<K, V> FromTwoNodes (int s, uint h1, BaseNode<K, V> n1, uint h2, BaseNode<K, V> n2)
      {
        // TODO: Does .Assert affect inlining?
        Debug.Assert (h1 != h2);
        Debug.Assert (s < TrieMaxShift);
        var b1 = Bit (h1, s);
        var b2 = Bit (h2, s);
        if (b1 == b2)
        {
          return new BitmapNodeN<K, V> (b1, new [] { FromTwoNodes (s + TrieShift, h1, n1, h2, n2) });
        }
        else
        {
          return b1 < b2
            ? new BitmapNodeN<K, V> (b1 | b2, new [] { n1, n2 })
            : new BitmapNodeN<K, V> (b2 | b1, new [] { n2, n1 })
            ;
        }
      }

#if TEST_BUILD
      internal override bool CheckInvariant (uint h, int s)
      {
        if (PopCount (Bitmap) != Nodes.Length)
        {
          return false;
        }

        var bitmap = Bitmap;

        var hash = -1;
        var iter = -1;

        while (bitmap != 0)
        {
          ++hash;

          var isSet = (bitmap & 0x1) != 0;
          bitmap >>= 1;

          if (!isSet)
          {
            continue;
          }

          ++iter;

          var n = Nodes[iter];
          if (n == null)
          {
            return false;
          }

          if (!n.CheckInvariant (h | (uint)(hash << s), s + TrieShift))
          {
            return false;
          }
        }

        return true;
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        var bits = Convert.ToString (Bitmap, 2);
        sb.FormatIndentedLine (indent, "Bitmap Bitmap:0b{0}, Nodes:{1}", new string ('0', 32 - bits.Length) + bits, Nodes.Length);
        for (var iter = 0; iter < Nodes.Length; ++iter)
        {
          var n = Nodes[iter];
          n.Describe (sb, indent + 2);
        }
      }
#endif

      internal override bool Receive (Func<uint, K, V, bool> r)
      {
        for (var iter = 0; iter < Nodes.Length; ++iter)
        {
          var n = Nodes[iter];
          if (!n.Receive (r))
          {
            return false;
          }
        }

        return true;
      }

      internal sealed override BaseNode<K, V> Set (int s, KeyValueNode<K, V> n)
      {
        var h = n.Hash;
        var bit = Bit (h, s);
        var localIdx = PopCount (Bitmap & (bit - 1));
        if ((bit & Bitmap) != 0)
        {
          var nvs = CopyArray (Nodes);
          nvs[localIdx] = Nodes[localIdx].Set (s + TrieShift, n);
          return new BitmapNodeN<K, V> (Bitmap, nvs);
        }
        else
        {
          var nvs = CopyArrayMakeHole (bit, Bitmap, Nodes);
          nvs[localIdx] = n;
          return new BitmapNodeN<K, V> (Bitmap | bit, nvs);
        }
      }

      internal sealed override bool TryFind (uint h, int s, K k, out V v)
      {
        var bit = Bit (h, s);
        if ((bit & Bitmap) != 0)
        {
          var localIdx = PopCount (Bitmap & (bit - 1));
          return Nodes[localIdx].TryFind (h, s + TrieShift, k, out v);
        }
        else
        {
          v = default (V);
          return false;
        }
      }

      internal sealed override BaseNode<K, V> Unset (uint h, int s, K k)
      {
        var bit = Bit (h, s);
        if ((bit & Bitmap) != 0)
        {
          var localIdx  = PopCount (Bitmap & (bit - 1));
          var updated   =  Nodes[localIdx].Unset (h, s + TrieShift, k);
          if (updated == Nodes[localIdx])
          {
            return this;
          }
          else if (updated != null)
          {
            var nvs = CopyArray (Nodes);
            nvs[localIdx] = updated;
            return new BitmapNodeN<K, V> (Bitmap, nvs);
          }
          else if (Nodes.Length > 1)
          {
            var nvs = CopyArrayRemoveHole (bit, Bitmap, Nodes);
            return new BitmapNodeN<K, V> (Bitmap & ~bit, nvs);
          }
          else
          {
            return null;
          }
        }
        else
        {
          return this;
        }
      }

    }

    internal sealed partial class HashCollisionNodeN<K, V> : BaseNode<K, V>
      where K : IEquatable<K>
    {
      public readonly uint                 Hash      ;
      public readonly KeyValueNode<K, V>[] KeyValues ;

      [MethodImpl (MethodImplOptions.AggressiveInlining)]
      public HashCollisionNodeN (uint h, KeyValueNode<K, V>[] kvs)
      {
        Hash      = h   ;
        KeyValues = kvs ;
      }

      [MethodImpl (MethodImplOptions.AggressiveInlining)]
      public static HashCollisionNodeN<K, V> FromTwoNodes (uint h, KeyValueNode<K, V> kv1, KeyValueNode<K, V> kv2)
      {
        return new HashCollisionNodeN<K, V> (h, new [] { kv1, kv2 });
      }

#if TEST_BUILD
      internal override bool CheckInvariant (uint h, int s)
      {
        for (var iter = 0; iter < KeyValues.Length; ++iter)
        {
          var kv = KeyValues[iter];
          var k = kv.Key;
          if ((uint)k.GetHashCode () != Hash)
          {
            return false;
          }
        }

        return CheckHash (Hash, h, s);
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        sb.FormatIndentedLine (indent, "HashCollison Hash:0x{0:X08}, KeyValues:{1}", Hash, KeyValues.Length);
        for (var iter = 0; iter < KeyValues.Length; ++iter)
        {
          var kv = KeyValues[iter];
          kv.Describe (sb, indent + 2);
        }
      }
#endif

      internal override bool Receive (Func<uint, K, V, bool> r)
      {
        for (var iter = 0; iter < KeyValues.Length; ++iter)
        {
          var kv = KeyValues[iter];
          if (!r (kv.Hash, kv.Key, kv.Value))
          {
            return false;
          }
        }

        return true;
      }

      internal sealed override BaseNode<K, V> Set (int s, KeyValueNode<K, V> n)
      {
        var h = n.Hash;
        if (Hash == h)
        {
          var k = n.Key;
          for (var iter = 0; iter < KeyValues.Length; ++iter)
          {
            var kv = KeyValues[iter];
            if (kv.Key.Equals (k))
            {
              var rvs = CopyArray (KeyValues);
              rvs[iter] = n;
              return new HashCollisionNodeN<K, V> (h, rvs);
            }
          }

          var avs = CopyArrayMakeHoleLast (KeyValues);
          avs[KeyValues.Length] = n;
          return new HashCollisionNodeN<K, V> (h, avs);
        }
        else
        {
          return BitmapNodeN<K, V>.FromTwoNodes (s, Hash, this, h, n);
        }
      }

      internal sealed override bool TryFind (uint h, int s, K k, out V v)
      {
        if (Hash == h)
        {
          for (var iter = 0; iter < KeyValues.Length; ++iter)
          {
            var kv = KeyValues[iter];
            if (kv.Key.Equals (k))
            {
              v = kv.Value;
              return true;
            }
          }

          v = default (V);
          return false;
        }
        else
        {
          v = default (V);
          return false;
        }
      }

      internal override BaseNode<K, V> Unset (uint h, int s, K k)
      {
        if (Hash == h)
        {
          for (var iter = 0; iter < KeyValues.Length; ++iter)
          {
            var kv = KeyValues[iter];
            if (kv.Key.Equals (k))
            {
              // TODO: Case for .Length == 2
              if (KeyValues.Length > 1)
              {
                var rvs = CopyArrayRemoveHole (iter, KeyValues);
                return new HashCollisionNodeN<K, V> (h, rvs);
              }
              else
              {
                return null;
              }
            }
          }

          return this;
        }
        else
        {
          return this;
        }
      }
    }
  }
}
