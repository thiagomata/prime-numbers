include "modDiv.dfy"

/**
 * Define the cycle function
 * Ensure some important properties into the cycle function
 * assert forall k: nat :: |source| <= k  < |dest|  ==> ModDiv.mod(k,|source|) < |source|;
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == source[ModDiv.mod(k,|source|)];
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == dest[k-|source|];
 */
module Cycle {

    import ModDiv

    function method isCycle(list: seq<nat>, listCycle: seq<nat>): bool
        requires |list| > 0;
//        requires |listCycle| >= |list|;
    {
        var limit := if |listCycle| > |list| then |list| else |listCycle|;
        var equalsFirst    := listCycle[..limit] == list;
        var equalsPrevious := forall k : nat :: |list| <= k < |listCycle| ==> listCycle[k] == listCycle[k - |list|];
        var equalsMod      := forall k : nat :: 0      <= k < |listCycle| ==> listCycle[k] == list[ k % |list| ];

        assert equalsFirst    ==> listCycle[..limit] == list[..limit];
        assert equalsPrevious ==> forall k : nat :: |list| <= k < |listCycle| ==> listCycle[k] == listCycle[k - |list|];
        assert equalsMod      ==> forall k : nat :: 0      <= k < |listCycle| ==> listCycle[k] == list[ k % |list| ];

        equalsFirst && equalsPrevious && equalsMod
    }

    method cycleUntil(list:seq<nat>, size: nat, gap: nat) returns (result: seq<nat>) 
        requires |list| > 0;
        requires size >= |list|;
        ensures |result| == size;
        ensures isCycle(list, result);
        decreases size;
    {
        var arr := new nat[size];
        var key := 0;
        var modKey := 0;
        while ( key < size )
            decreases size - key;
            invariant key <= size;
            invariant key > 0 ==> isCycle(list, arr[..key]);
        {
            var mod, div := ModDiv.modDiv(key,|list|);
            assert ModDiv.isModDiv(key,|list|,mod,div);
            if ( key < |list| ) {
                ModDiv.modSmallValues(key,|list|,mod,div);
                assert modKey < |list| ==> modKey == key;
            }
            arr[key] := list[modKey];
            assert key < |list| ==> arr[..key] == list[..key];
            if ( key >= |list| ) {
                ModDiv.isModDivMinus(key,|list|,mod,div);
            }
            assert forall k : nat :: |list| <= k < key ==> arr[k] == arr[k - |list|];
            assert forall k : nat :: 0      <= k < key ==> arr[k] == list[ k % |list| ];
            key := key + 1;
        }
        assert key == size;
        result := arr[..];

        // if (size == 0 ) {
        //     result := [];
        //     return;
        // } else {
        //     var key := ModDiv.mod(gap,|list|);
        //     assert key < |list|;
        //     var current := list[key];
        //     var others := cycleUntil(list, size - 1, gap + 1);
        //     result := [current] + others;
        // }
    }
    
    lemma modIscycle(list: seq<nat>, listCycle: seq<nat>)
        requires |list| > 0;
        requires forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[k % |list|];
        ensures isCycle(list, listCycle);
    {
        var limit := if |listCycle| > |list| then |list| else |listCycle|;
        assert forall k : nat :: 0      <= k < |listCycle| ==> ModDiv.isMod(k, |list|, k % |list|);
        // assert listCycle[..limit] == list[..limit];
        assert forall k : nat :: |list| <= k < |listCycle| ==> listCycle[k] == listCycle[k - |list|];
        assert forall k : nat :: 0      <= k < |listCycle| ==> listCycle[k] == list[ k % |list| ];

    }

    /**
     * Since the current definition of the cycle mod is alligned with the definition of the isModDiv
     * all the properties defined to the isModDiv can be applied to the cycle.
     */
    lemma cycleIsMod(list: seq<nat>, listCycle: seq<nat>)
        requires |list| > 0;
        requires |listCycle| >= |list|;
        requires isCycle(list, listCycle);
        ensures forall k : nat :: 0 <= k < |listCycle| ==> ModDiv.isModDiv(k, |list|, k / |list|, k % |list|);
    {
        assert forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[ k % |list| ];
        assert forall k : nat :: 0 <= k < |listCycle| ==> ModDiv.isModDiv(k, |list|, k / |list|, k % |list|);
    }

    lemma cycleShouldContainsList(list: seq<nat>, cycleList: seq<nat>)
        requires |list| > 0;
        requires |cycleList| >= |list|;
        requires isCycle(list, cycleList);
        ensures cycleList[0..|list|] == list;
    {
    }

    lemma cycleByConcat(list: seq<nat>, cycleList: seq<nat>, smallCycle: seq<nat>, m: nat)
        requires |list| > 0;
        requires |cycleList| > |list|;
        requires |smallCycle| > |list|;
        requires isCycle(list, cycleList);
        requires isCycle(list, smallCycle);
        requires |cycleList| == |list| * m;
        requires |smallCycle| == |cycleList| - |list|;
        requires |smallCycle| == |list| * ( m - 1 );
        requires m > 0;
        ensures cycleList == list + cycleList[|list|..];
        ensures cycleList == list + smallCycle;
    {
        assert cycleList[0..|list|] == list;
    }

//     method Main()
//     {
//         print("\ntesting cycle\n");
//         print(isCycle([1,2,3],[1,2,3,1,2,3,1,4]));
//         print("\n:D\n");
//     }
}