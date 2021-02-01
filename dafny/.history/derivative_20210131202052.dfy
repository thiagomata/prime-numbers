include "list.dfy"
include "cycle.dfy"

module Integral {

    import Cycle
    import List

    function isDerivetive1list: seq<nat>, initial: nat, listDerivetive: seq<nat>): bool
        requires |list| == |listDerivetive|;
    {
        ( forall v: nat :: 0 < v < |list| ==> ( list[v] >= list[v-1] && listDerivetive[v] == list[v] - list[v-1] ) )
        && 
        ( |list| > 0 ==> list[0] > initial )
        && 
        ( |list| > 0 ==> listDerivetive[0] == list[0] - initial )
    }

    lemma isDerivetiveReverseIntegral(list: seq<nat>, listIntegral: seq<nat>, listDerivetive: seq<nat>, initial: nat)
        requires |list| == |listIntegral|;
        requires isIntegral(list, initial, listIntegral);
        requires |listIntegral| == |listDerivetive|;
        requires isDerivetive(listIntegral, initial, listDerivetive);
        ensures list == listDerivetive;
    {
        if list == [] {
            assert listIntegral == [];
            assert listDerivetive == [];
            assert listDerivetive == list;
        } else if |list| == 1 {
            var h := list[0];
            assert forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == List.sum(list[0..v+1]) + initial;
            assert listIntegral[0] == List.sum(list[0..1]) + initial;
            assert list[0..1] == [list[0]];
            assert listIntegral[0] == List.sum([list[0]]) + initial;
            assert List.sum([list[0]]) == list[0];
            assert listIntegral[0] == list[0] + initial == h + initial;
            assert listDerivetive[0] == listIntegral[0] - initial;
            assert listDerivetive[0] == h + initial - initial == h;
            assert listDerivetive == list;
        } else {
            assert forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == List.sum(list[0..v+1]) + initial;
            forall k | 0 < k < |listIntegral|
                ensures listDerivetive[k] == list[k];
            {
                assert listIntegral[k] >= listIntegral[k-1];
                assert listIntegral[k] == List.sum(list[0..k+1]) + initial;
                assert listIntegral[k-1] == List.sum(list[0..k]) + initial;
                assert list[0..k] + [list[k]] == list[0..k+1];
                List.distributiveSum(list[0..k],[list[k]]);
                assert List.sum(list[0..k+1]) == List.sum(list[0..k] + [list[k]]);
                assert List.sum(list[0..k+1]) == List.sum(list[0..k]) + List.sum([list[k]]);
                assert List.sum(list[0..k+1]) == List.sum(list[0..k]) + list[k];
                assert listDerivetive[k] == listIntegral[k] - listIntegral[k-1];
                assert listDerivetive[k] == (List.sum(list[0..k+1]) + initial) - (List.sum(list[0..k]) + initial);
                assert listDerivetive[k] == List.sum(list[0..k+1]) + initial - List.sum(list[0..k]) - initial;
                assert listDerivetive[k] == List.sum(list[0..k]) + list[k] + initial - List.sum(list[0..k]) - initial;
                assert listDerivetive[k] == list[k] + List.sum(list[0..k]) - List.sum(list[0..k]) + initial - initial;
                assert listDerivetive[k] == list[k];
            }
        }
    }
}