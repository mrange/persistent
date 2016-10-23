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
    bool IsEmpty                  { get; }
    bool Visit                    (Func<uint, K, V, bool> r);
    IPersistentHashMap<K, V> Set  (K k, V v);
    bool TryFind                  (K k, out V v);
  }

  public static partial class PersistentHashMap
  {
    public static IPersistentHashMap<K, V> Empty<K, V> ()
      where K : IEquatable<K>
    {
      return new EmptyNode<K ,V> ();
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

      var holemask  = holebit - 1;
      var nvs       = new T[vs.Length + 1];
      var iter      = 0;

      for (; (bitmap & holemask) != 0; ++iter)
      {
        bitmap &= bitmap - 1;
        nvs[iter] = vs[iter];
      }

      ++iter;

      for (; iter < nvs.Length; ++iter)
      {
        nvs[iter] = vs[iter - 1];
      }

      return nvs;
    }

    internal abstract partial class BaseNode<K, V> : IPersistentHashMap<K ,V>
      where K : IEquatable<K>
    {
      bool IPersistentHashMap<K, V>.IsEmpty
      {
        get
        {
          return Empty ();
        }
      }

      bool IPersistentHashMap<K, V>.Visit(Func<uint, K, V, bool> r)
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

      IPersistentHashMap<K, V> IPersistentHashMap<K ,V>.Set(K k, V v)
      {
        return Set (0, new KeyValueNode<K, V> ((uint)k.GetHashCode (), k, v));
      }

      bool IPersistentHashMap<K ,V>.TryFind(K k, out V v)
      {
        return TryFind ((uint)k.GetHashCode (), 0, k, out v);
      }

      public override string ToString()
      {
        var sb = new StringBuilder (16);
        Describe (sb, 0);
        return sb.ToString();
      }

      internal abstract bool CheckInvariant (uint h, int s);
      internal abstract void Describe       (StringBuilder sb, int indent);
      internal virtual  bool Empty          ()
      {
        return false;
      }

      internal abstract bool Receive        (Func<uint, K, V, bool> r);
      internal abstract BaseNode<K, V> Set  (int s, KeyValueNode<K, V> n);
      internal abstract bool TryFind        (uint h, int s, K k, out V v);

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
    }

    internal sealed partial class EmptyNode<K, V> : BaseNode<K, V>
      where K : IEquatable<K>
    {
      internal override bool CheckInvariant (uint h, int s)
      {
        return true;
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        sb.IndentedLine (indent, "Empty");
      }

      internal override bool Empty()
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

      internal override bool CheckInvariant (uint h, int s)
      {
        return CheckHash (Hash, h, s) && Hash == Key.GetHashCode ();
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        sb.FormatIndentedLine (indent, "KeyValue {0}, {1}, {2}", Hash, Key, Value);
      }

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
          return new HashCollisionNodeN<K ,V> (h, this, n);
        }
        else
        {
          return new BitmapNodeN<K ,V> (s, Hash, this, h, n);
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
      public BitmapNodeN (int s, uint h1, BaseNode<K, V> n1, uint h2, BaseNode<K, V> n2)
        : this (Bit (h1, s) | Bit (h2, s), new [] { n1, n2 })
      {
        // TODO: Does .Assert affect inlining?
        Debug.Assert (h1 != h2);
        Debug.Assert (s < TrieMaxShift);
      }

      internal override bool CheckInvariant (uint h, int s)
      {
        for (var iter = 0; iter < Nodes.Length; ++iter)
        {
          var n = Nodes[iter];
          if (n == null)
          {
            return false;
          }

          if (!n.CheckInvariant (h | (uint)(iter << s), s + TrieShift))
          {
            return false;
          }
        }

        // TODO: Check bitmap

        return true;
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        sb.FormatIndentedLine (indent, "Bitmap {0}, {1}", Bitmap, Nodes.Length);
        for (var iter = 0; iter < Nodes.Length; ++iter)
        {
          var n = Nodes[iter];
          n.Describe (sb, indent + 2);
        }
      }

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
          nvs[localIdx] = Nodes[localIdx].Set (s + TrieShift, n);
          return new BitmapNodeN<K, V> (Bitmap, nvs);
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
      public HashCollisionNodeN (uint h, KeyValueNode<K, V> kv1, KeyValueNode<K, V> kv2)
        :  this (h, new [] { kv1, kv2 })
      {
      }

      internal override bool CheckInvariant (uint h, int s)
      {
        for (var iter = 0; iter < KeyValues.Length; ++iter)
        {
          var kv = KeyValues[iter];
          var k = kv.Key;
          if (k.GetHashCode () != Hash)
          {
            return false;
          }
        }

        return CheckHash (Hash, h, s);
      }

      internal override void Describe (StringBuilder sb, int indent)
      {
        sb.FormatIndentedLine (indent, "HashCollison {0}, {1}", Hash, KeyValues.Length);
        for (var iter = 0; iter < KeyValues.Length; ++iter)
        {
          var kv = KeyValues[iter];
          kv.Describe (sb, indent + 2);
        }
      }

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

      internal sealed override BaseNode<K, V> Set(int s, KeyValueNode<K, V> n)
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
          return new BitmapNodeN<K, V> (s, Hash, this, h, n);
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
    }
  }
}
