include "integral.dfy"
include "list.dfy"
include "cycle.dfy"

module Derivative {

    import Integral
    import List
    import Cycle

    function isDerivative(list: seq<nat>, initial: nat, listDerivative: seq<nat>): bool
        requires |list| == |listDerivative|;
    {
        ( forall v: nat :: 0 < v < |list| ==> ( list[v] >= list[v-1] && listDerivative[v] == list[v] - list[v-1] ) )
        && 
        ( |list| > 0 ==> list[0] > initial )
        && 
        ( |list| > 0 ==> listDerivative[0] == list[0] - initial )
    }

    method derivative(list: seq<nat>, initial: nat) returns (listDerivative: seq<nat>)
        requires |list| > 0;
        requires List.sorted(list);
        requires list[0] > initial;
        ensures |list| == |listDerivative|;
        ensures isDerivative(list, initial, listDerivative);
    {
        var distance := |list|;
        var arr := new nat[distance];
        var k := 0;
        arr[0] := list[0] - initial;
        while (k < |list|)
            decreases |list| - k;
            invariant 0 <= k <= |list|;
            invariant forall v: nat :: 0 < v < k ==> arr[v] == list[v] - list[v-1];
            invariant arr[0] == list[0] - initial;
        {
            if ( k > 0 ) {
                arr[k] := list[k] - list[k-1];
            }
            k := k + 1;
        }
        listDerivative := arr[..];
    }

    /**
     * listIntegral = integral(list, initial)
     * listDerivative = derivative(listIntegral, initial)
     * listDerivative == list
     */
    lemma derivativeOfIntegral(list: seq<nat>, listIntegral: seq<nat>, listDerivative: seq<nat>, initial: nat)
        requires |list| == |listIntegral|;
        requires Integral.isIntegral(list, initial, listIntegral);
        requires |listIntegral| == |listDerivative|;
        requires isDerivative(listIntegral, initial, listDerivative);
        ensures list == listDerivative;
    {
        if list == [] {
            assert listIntegral == [];
            assert listDerivative == [];
            assert listDerivative == list;
        } else if |list| == 1 {
            var h := list[0];
            assert forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == List.sum(list[0..v+1]) + initial;
            assert listIntegral[0] == List.sum(list[0..1]) + initial;
            assert list[0..1] == [list[0]];
            assert listIntegral[0] == List.sum([list[0]]) + initial;
            assert List.sum([list[0]]) == list[0];
            assert listIntegral[0] == list[0] + initial == h + initial;
            assert listDerivative[0] == listIntegral[0] - initial;
            assert listDerivative[0] == h + initial - initial == h;
            assert listDerivative == list;
        } else {
            assert forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == List.sum(list[0..v+1]) + initial;
            forall k | 0 < k < |listIntegral|
                ensures listDerivative[k] == list[k];
            {
                assert listIntegral[k] >= listIntegral[k-1];
                assert listIntegral[k] == List.sum(list[0..k+1]) + initial;
                assert listIntegral[k-1] == List.sum(list[0..k]) + initial;
                assert list[0..k] + [list[k]] == list[0..k+1];
                List.distributiveSum(list[0..k],[list[k]]);
                assert List.sum(list[0..k+1]) == List.sum(list[0..k] + [list[k]]);
                assert List.sum(list[0..k+1]) == List.sum(list[0..k]) + List.sum([list[k]]);
                assert List.sum(list[0..k+1]) == List.sum(list[0..k]) + list[k];
                assert listDerivative[k] == listIntegral[k] - listIntegral[k-1];
                assert listDerivative[k] == (List.sum(list[0..k+1]) + initial) - (List.sum(list[0..k]) + initial);
                assert listDerivative[k] == List.sum(list[0..k+1]) + initial - List.sum(list[0..k]) - initial;
                assert listDerivative[k] == List.sum(list[0..k]) + list[k] + initial - List.sum(list[0..k]) - initial;
                assert listDerivative[k] == list[k] + List.sum(list[0..k]) - List.sum(list[0..k]) + initial - initial;
                assert listDerivative[k] == list[k];
            }
        }
    }

    /**
     * listDerivative = derivative(list, initial)
     * listIntegral = integral(listDerivative, initial)
     * listDerivative == list
     */
    lemma integralOfDerivative(list: seq<nat>, listDerivative: seq<nat>, listIntegral: seq<nat>, initial: nat)
        requires |list| == |listDerivative|;
        requires |listIntegral| == |list|;
        requires isDerivative(list, initial, listDerivative);
        requires Integral.isIntegral(listDerivative, initial, listIntegral);
        requires |listIntegral| == |listDerivative|;
        ensures list == listIntegral;
    {
        if list == [] {
            assert listIntegral == [];
            assert listDerivative == [];
            assert listDerivative == list;
        } else if |list| == 1 {
            var h := list[0];
            assert forall v: nat :: 0 <= v < |listDerivative| ==> listIntegral[v] == List.sum(listDerivative[0..v+1]) + initial;
            assert listIntegral[0] == List.sum(listDerivative[0..1]) + initial;
            assert listDerivative[0..1] == [listDerivative[0]];
            assert listIntegral[0] == List.sum([listDerivative[0]]) + initial;
            assert List.sum([listDerivative[0]]) == listDerivative[0];
            assert listIntegral[0] == listDerivative[0] + initial;
            assert listDerivative[0] == list[0] - initial;
            assert listIntegral[0] == list[0] - initial + initial;
            assert listIntegral[0] == list[0];
            assert listIntegral == list;
        } else {
            assert forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == List.sum(listDerivative[0..v+1]) + initial;
            var k := 0;
            while (k < |listIntegral|)
                decreases |listIntegral| - k;
                invariant 0 <= k <= |listIntegral|;
                invariant forall v: nat :: 0 <= v < k ==> listIntegral[v] == list[v];
            {
                if ( k == 0 ) {
                    assert listDerivative[0] == list[0] - initial;
                    assert listIntegral[0] == List.sum(listDerivative[0..1]) + initial;
                    assert listDerivative[0..1] == [listDerivative[0]];
                    assert listIntegral[0] == List.sum([listDerivative[0]]) + initial;
                    assert List.sum([listDerivative[0]]) == listDerivative[0];
                    assert listIntegral[0] == listDerivative[0] + initial;
                    assert listIntegral[0] == list[0] - initial + initial;
                    assert listIntegral[0] == list[0];
                } else {
                    assert listIntegral[k] == List.sum(listDerivative[..k+1]) + initial;
                    assert listDerivative[..k+1] == listDerivative[..k]+[listDerivative[k]];
                    assert listIntegral[k] == List.sum(listDerivative[..k]+[listDerivative[k]]) + initial;
                    List.distributiveSum(listDerivative[..k],[listDerivative[k]]);
                    assert listIntegral[k] == List.sum(listDerivative[..k]) + List.sum([listDerivative[k]]) + initial;
                    assert listIntegral[k] == List.sum(listDerivative[..k]) + initial + List.sum([listDerivative[k]]);
                    assert listIntegral[k-1] == List.sum(listDerivative[..k]) + initial;
                    assert listIntegral[k] == listIntegral[k-1] + List.sum([listDerivative[k]]);
                    assert List.sum([listDerivative[k]]) == listDerivative[k];
                    assert listIntegral[k] == listIntegral[k-1] + listDerivative[k];
                    assert listIntegral[k-1] == list[k-1];
                    assert listIntegral[k] == list[k-1] + list[k] - list[k-1];
                    assert listIntegral[k] == list[k] + list[k-1] - list[k-1];
                    assert listIntegral[k] == list[k];
                }
                k := k + 1;
            }
        }
    }

    lemma inverseOfIntegralIsDerivative(listDerivative: seq<nat>, initial: nat, listIntegral: seq<nat>)
        requires |listDerivative| == |listIntegral|;
        requires Integral.isIntegral(listDerivative, initial, listIntegral);
        requires |listIntegral| > 0 ==> listIntegral[0] > initial;
        ensures isDerivative(listIntegral, initial, listDerivative);
    {
        Integral.integralValuesRelative(listDerivative, initial, listIntegral);
        assert forall v: nat :: 0 < v < |listIntegral| ==> ( listIntegral[v] >= listIntegral[v-1] && listDerivative[v] == listIntegral[v] - listIntegral[v-1] );
        assert ( |listIntegral| > 0 ==> listIntegral[0] > initial );
        assert ( |listIntegral| > 0 ==> listDerivative[0] == listIntegral[0] - initial );
    }

    lemma derivativeOfSortedList(listDerivative: seq<nat>, initial: nat, listIntegral: seq<nat>)
        requires |listDerivative| == |listIntegral|;
        requires Integral.isIntegral(listDerivative, initial, listIntegral);
        requires |listIntegral| > 0 ==> listIntegral[0] > initial;
        requires List.sorted(listIntegral)
        ensures isDerivative(listIntegral, initial, listDerivative);
        ensures List.nonZero(listDerivative);
    {        
        inverseOfIntegralIsDerivative(listDerivative, initial, listIntegral);
        var k := 0;
        while ( k < |listIntegral| )
            decreases |listIntegral| - k;
            invariant k <= |listIntegral|; 
            invariant k < |listIntegral| ==> listDerivative[k] > 0;
            invariant forall p :: 0 <= p < k ==> listDerivative[p] > 0;
        {
             if ( k > 0 ) {
                assert listDerivative[k] == listIntegral[k] - listIntegral[k-1];
                assert listIntegral[k] > listIntegral[k-1];
                var currentValue := listIntegral[k] - listIntegral[k-1];
                assert currentValue > 0;
                assert listDerivative[k] == currentValue;
                assert listDerivative[k] > 0;
            } else {
                assert listIntegral[k] > initial;
                assert listDerivative[k] == listIntegral[k] - initial;
                assert listDerivative[k] > 0;
            }
            assert listDerivative[k] > 0;
            k := k + 1;
        }
        assert forall k :: 0 <= k < |listIntegral| ==> listDerivative[k] > 0;
    }

    lemma sumOfDerivativeEqualsLastElement(listIntegral: seq<nat>, listDerivative: seq<nat>, initial: nat)
        requires |listIntegral| > 0;
        requires |listDerivative| == |listIntegral|;
        requires Integral.isIntegral(listDerivative, initial, listIntegral);
        requires |listIntegral| == |listDerivative|;
        ensures List.last(listIntegral) == List.sum(listDerivative) + initial;
    {
        assert |listIntegral| == |listDerivative|;
        assert listIntegral[ |listIntegral| - 1 ] == List.sum(listDerivative[..|listIntegral|]) + initial;
        assert listIntegral[ |listIntegral| - 1 ] == List.sum(listDerivative[..|listDerivative|]) + initial;
        assert listDerivative[..|listDerivative|] == listDerivative;
        assert listIntegral[ |listIntegral| - 1 ] == List.sum(listDerivative) + initial;
        assert List.last(listIntegral) == listIntegral[ |listIntegral| - 1 ];
        assert List.last(listIntegral) == List.sum(listDerivative) + initial;
    }
}