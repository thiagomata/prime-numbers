include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"

module Integral {

    import ModDiv
    import Cycle
    import List

    lemma modListSumUp(listA: seq<nat>, listB: seq<nat>, v: nat)
        requires  v > 0;
        ensures ModDiv.mod( List.sum( listA + listB ), v) == ModDiv.mod( ModDiv.mod( List.sum(listA), v) + ModDiv.mod( List.sum(listB),v), v)
    {
        List.distributiveSum(listA, listB);
        var sa := List.sum(listA);
        var sb := List.sum(listB);
        var sab := List.sum(listA + listB);
        assert sab == sa + sb;
        ModDiv.modAplusB(v, sa, sb);
        assert ModDiv.mod(sab, v) == ModDiv.mod( ModDiv.mod(sa, v) + ModDiv.mod(sb,v), v);
    }

    function isIntegral(list: seq<nat>, initial: nat, listIntegral: seq<nat>): bool
        requires |list| == |listIntegral|;
    {
        forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == List.sum(list[0..v+1]) + initial
    }


    lemma integralValuesRelative(list: seq<nat>, initial:nat, listIntegral: seq<nat>)
        requires |list| == |listIntegral|;
        requires isIntegral(list, initial, listIntegral);
        ensures |listIntegral| > 0 ==> listIntegral[0] == list[0] + initial;
        ensures forall v: nat    :: 0 <  v     < |listIntegral| ==> listIntegral[v] == listIntegral[v-1] + list[v];
        ensures forall k: nat    :: 0 <  k     < |listIntegral| ==> listIntegral[k] >= listIntegral[k-1];
        ensures forall v, p: nat :: 0 <= p < v < |listIntegral| ==> listIntegral[v] >= listIntegral[p];
    {
        assert forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == List.sum(list[0..v+1]) + initial;

        if |list| > 0 {
            assert listIntegral[0] == List.sum(list[..1]) + initial;
            assert List.sum(list[..1]) == List.sum([list[0]]) == list[0];
            assert listIntegral[0] == list[0] + initial;
        }

        var k := 0;
        while (k < |list|)
            decreases |list| - k;
            invariant 0 <= k <= |list|;
            invariant forall v: nat    :: 0 <= v < k     ==> listIntegral[v]   == List.sum(list[..v+1]) + initial;
            invariant forall v: nat    :: 0 <  v < k     ==> listIntegral[v]   == listIntegral[v-1] + list[v];
            invariant forall v: nat    :: 0 <  v < k     ==> listIntegral[v]   >= listIntegral[v-1];
            invariant forall v, p: nat :: 0 <= p < v < k ==> listIntegral[v]   >= listIntegral[p];
        {
            assert listIntegral[k] == List.sum(list[..k+1]) + initial;
            assert list[..k+1] == list[..k]+[list[k]];
            assert listIntegral[k] == List.sum(list[..k] + [list[k]]) + initial;
            List.sumListPlusValue(list[..k],list[k]);
            assert listIntegral[k] == List.sum(list[..k]) + list[k] + initial;
            if ( k > 0 ) {
                assert listIntegral[k]   == List.sum(list[..k]) + initial + list[k];
                assert listIntegral[k-1] == List.sum(list[..k]) + initial;
                assert listIntegral[k]   == listIntegral[k-1] + list[k];
                assert listIntegral[k]   >= listIntegral[k-1];
                assert forall v: nat :: 0 <  v < k < |listIntegral| ==> listIntegral[k-1] >= listIntegral[v];
            }
            assert forall p: nat :: 0 < p < k ==> listIntegral[k] >= listIntegral[p];
            k := k + 1;
        }
        assert forall v, p :: 0 <= p < v < |listIntegral| ==> listIntegral[v] >= listIntegral[p];
    }

    lemma integralValuesIncrease(list: seq<nat>, initial:nat, listIntegral: seq<nat>)
        requires |list| == |listIntegral|;
        requires isIntegral(list, initial, listIntegral);
        requires List.nonZero(list);
        ensures forall v: nat    :: 0 <  v     < |listIntegral| ==> listIntegral[v] == listIntegral[v-1] + list[v];
        ensures forall k: nat    :: 0 <  k     < |listIntegral| ==> listIntegral[k] >  listIntegral[k-1];
        ensures forall v, p: nat :: 0 <= p < v < |listIntegral| ==> listIntegral[v] >  listIntegral[p];
        ensures List.sorted(listIntegral)
    {
        integralValuesRelative(list, initial, listIntegral);

        var k := 0;
        while (k < |list|)
            decreases |list| - k;
            invariant 0 <= k <= |list|;
            invariant forall v: nat    :: 0 <= v < k     ==> listIntegral[v]   == List.sum(list[..v+1]) + initial;
            invariant forall v: nat    :: 0 <  v < k     ==> listIntegral[v]   == listIntegral[v-1] + list[v];
            invariant forall v: nat    :: 0 <  v < k     ==> listIntegral[v]   > listIntegral[v-1];
            invariant forall v, p: nat :: 0 <= p < v < k ==> listIntegral[v]   > listIntegral[p];
        {
            if ( k > 0 ) {
                assert listIntegral[k]   == listIntegral[k-1] + list[k];
                assert listIntegral[k]   >  listIntegral[k-1];
                assert forall v: nat :: 0 <  v < k < |listIntegral| ==> listIntegral[k] > listIntegral[v];
            }
            assert forall p: nat :: 0 < p < k ==> listIntegral[k] > listIntegral[p];
            k := k + 1;
        }
        assert forall v, p :: 0 <= p < v < |listIntegral| ==> listIntegral[v] > listIntegral[p];
    }

    function method integral(list: seq<nat>, initial: nat ): seq<nat>
        ensures |list| == |integral(list, initial)|;
        ensures forall k :: 0 < k < |list| ==> (integral(list, initial))[k] == (integral(list, initial))[k-1] + list[k];
        ensures isIntegral(list,initial,integral(list, initial));
        decreases list;
    {
        var head := if |list| == 0 then 0 else list[0] + initial;
        var prev := if |list| == 0 then [] else integral(list[1..],head);
        var result := if |list| == 0 then [] else [head] + prev;

        assert |result| > 0 ==> result[0] == list[0] + initial;
        assert forall k :: 0 < k < |list| ==> result[k] == result[k-1] + list[k];
        assert |list| == 0 ==> result == [];
        assert |list| == 1 ==> result == [list[0] + initial];
        assert |list| == 1 ==> result == [List.sum(list[..1]) + initial];
        assert |list| > 0 ==> (result)[1..] == integral(list[1..],list[0] + initial);
        assert |list| > 0 ==> (result)[1..] == integral(list[1..],result[0]);

        integralIsIntegral(result, list, initial);
        result
    }

    lemma integralIsIntegral(listIntegral:seq<nat>,list:seq<nat>,initial: nat) 
        requires |listIntegral| == |list|;
        requires |listIntegral| > 0 ==> listIntegral[0] == list[0] + initial;
        requires forall k :: 0 <  k < |list| ==> listIntegral[k] == listIntegral[k-1] + list[k];
        ensures  forall k :: 0 <= k < |list| ==> listIntegral[k] == List.sum(list[..k+1]) + initial;
        ensures isIntegral(list,initial,listIntegral);
        decreases |listIntegral|;
    {
        if ( |list| == 0 ) {
            assert |listIntegral| == 0;
            assert isIntegral(list, initial, listIntegral);
        } else {
            assert listIntegral[0] == list[0] + initial;
            assert List.sum([list[0]]) == list[0];
            assert [list[0]] == list[..1];
            assert List.sum([list[0]]) == List.sum(list[..1]);
            assert listIntegral[0] == List.sum(list[..1]) + initial;

            var k := 0;
            while ( k < |list| )
                decreases |list| - k;
                invariant k <= |list|;
                invariant k > 0 ==> listIntegral[k-1] == List.sum(list[..k]) + initial;
                invariant forall v :: 0 <= v < k ==> listIntegral[v] == List.sum(list[..v+1]) + initial;
            {
                if ( k == 0 )
                {
                    assert listIntegral[0] == List.sum(list[..1]) + initial;
                } else {
                    assert listIntegral[0] == List.sum(list[..1]) + initial;
                    assert listIntegral[k-1] == List.sum(list[..k]) + initial; 
                    assert listIntegral[k] == listIntegral[k-1] + list[k];
                    assert listIntegral[k] == List.sum(list[..k]) + initial + list[k];
                    assert listIntegral[k] == List.sum(list[..k]) + list[k] + initial;
                    List.sumListPlusValue(list[..k],list[k]);
                    assert List.sum(list[..k]+[list[k]]) == List.sum(list[..k]+[list[k]]);
                    assert list[..k]+[list[k]] == list[..k+1];
                    assert List.sum(list[..k]+[list[k]]) == List.sum(list[..k+1]);
                }
                assert listIntegral[k] == List.sum(list[..k+1]) + initial;
                k := k + 1;
            }
        }
        assert isIntegral(list, initial, listIntegral);
    }

    method testIntegral(v:nat, list: seq<nat>, initial: nat)
    {
        var a := [1,2,3];
        assert a[..1] == [a[0]];
 
        var empty := integral([], initial);
        assert  empty == [];
 
        var single := [v];
        var singleIntegral := integral(single, initial);
        assert singleIntegral[0] == List.sum(single[..1]) + initial;

        var listIntegral := integral(list, initial);
        assert forall n: nat ::  0 < n < |list| ==> listIntegral[n] == List.sum(list[..n+1]) + initial;
        assert |listIntegral| == |list|;
    }
}