include "mod.dfy"

module List {

    import Mod;

    function sorted(list: seq<nat>): bool {
        forall k : nat :: 1 <= k < |list| ==> list[k] > list[k-1]
    }

    function nonZero(list: seq<nat>): bool
    {
        forall l: nat :: 0 <= l < |list| ==> list[l] > 0
    }

    function unique(list: seq<nat>): bool {
        forall n,m : nat :: 0 <= n < m < |list| ==> list[n] != list[m]
    }

    function method cycle(list:seq<nat>,pos:nat): nat
        requires |list| > 0;
    {
        var result := Mod.mod(pos, |list|);
        assert result < |list|;

        result
    }

    function method cycleOld(list:seq<nat>, pos: nat): nat
        requires |list| > 0;
    decreases pos;
    {
        var result := if ( pos < |list| ) then list[pos] else
            list[pos % |list|];
        
        assert pos < |list| ==> list[pos] == result;
        assert pos >= |list| ==> result == list[ pos % |list| ];

        result
    }

    method cycleUntil(list:seq<nat>, size: nat, gap: nat) returns (result: seq<nat>) 
        requires |list| > 0;
        ensures |result| == size;
        ensures forall pos : nat :: 0 <= pos < |result| ==> result[pos] == list[Mod.mod(pos + gap,|list|)]
    {
        if (size == 0 ) {
            result := [];
            return;
        }
        var key := Mod.mod(gap,|list|);
        Mod.remainderShouldBeSmall(gap, |list|, key);
        var current := list[key];
        var others := cycleUntil(list, size - 1, gap + 1);
        result := [current] + others;
    }
//     method cycleUntil(list:seq<nat>, size: nat) returns (result: seq<nat>)
//         requires |list| > 0;
//         ensures |result| == size;
//         ensures forall pos : nat :: pos <  |list| ==> result[pos] == list[pos];
// //        ensures forall pos : nat :: |list| < pos < |result| ==> result[pos] == list[cycle(list,pos)];
//     {
//         var arr := new nat[size];
//         var k := 0;
//         var l := |list|;
//         var v := Mod.mod(k,|list|);
//         while (k < size)
//             decreases size - k;
//             invariant v < |list|;
//             invariant v == Mod.mod(k,|list|);
//             invariant 0 < k < size ==> arr[k] == list[v];
//             // invariant k < size ==> arr[k] == cycle(list,k);
//             // invariant forall n: nat :: 0 <= n < k ==> ( n <= arr.Length ==> arr[n] == list[n]);
//             // invariant k < size && k >= |list| ==> arr[k] == list[ Mod.mod(k, |list|) ];
//         {
//             v := Mod.mod(k,|list|);
//             Mod.remainderShouldBeSmall(k,|list|, v);
//             Mod.loopList(list,k);

//             assert k >= |list| ==> Mod.mod(k,|list|) == Mod.mod(k-|list|, |list|);
//             assert k <  |list| ==> Mod.mod(k,|list|) == v == k;
//             arr[k] := list[ v ];
//             assert k <  |list| ==> arr[k] == list[k];
//             assert k >= |list| ==> arr[k] == list[ Mod.mod(k,|list|) ];
//             k := k + 1;
//             v := Mod.mod(k,|list|);
//             Mod.remainderShouldBeSmall(k,|list|, v);
//             assert v <  |list|;
//         }
//         result := arr[..];
//     }

    function first(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[0]
    }

    function last(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[|list|-1]
    }

    function method sum(list: seq<nat>): nat
        decreases |list|;
    {
        if (|list| == 0 ) then 0 else
        list[0] + sum(list[1..])
    }

    lemma sumOfListWithVEqualsSumOfListPlusV(list: seq<nat>, v: nat, k: nat)
        requires 0 < k < |list|;
    {
        // var t := [1];
        // assert t[0] == 1;
        // assert t[1..] == [];
        // assert sum([]) == 0;

        assert sum([v] + list) == v + sum(list) == sum(list) + v;
        var acc := sum(list[..k]);
        var acc2 := list[k] + sum(list[..k]);
        assert acc2 == list[k] + acc;
    }

    method integral(list: seq<nat>, initial: nat ) returns (result: seq<nat>)
        ensures |list| == |result|;
        ensures forall v: nat :: 0 <= v < |list| ==> result[v] == sum(list[0..v+1]) + initial;
    {
        var distance := |list|;
        var arr := new nat[distance];
        var k := 0;
        var acc := initial;
        while (k < |list|)
            decreases |list| - k;
            invariant 0 <= k <= |list|;
            invariant forall v: nat :: 0 <= v < k ==> arr[v] == sum(list[..v+1]) + initial;
        {
            /* 
             * Could not make it work using acc, what would be fast.
             * This is not the fast strategy, but for sure is correct
             */
            arr[k] := sum(list[..k+1]) + initial;
            k := k + 1;
        }
        // array to seq
        result := arr[..];
    }

    method testIntegral(v:nat, list: seq<nat>, initial: nat)
    {
        var a := [1,2,3];
        assert a[..1] == [a[0]];
 
        var empty := integral([], initial);
        assert  empty == [];
 
        var single := [v];
        var singleIntegral := integral(single, initial);
        assert singleIntegral[0] == sum(single[..1]) + initial;

        var listIntegral := integral(list, initial);
        assert forall n: nat ::  0 < n < |list| ==> listIntegral[n] == sum(list[..n+1]) + initial;
        assert |listIntegral| == |list|;
    }

    method Main() {
    }
}