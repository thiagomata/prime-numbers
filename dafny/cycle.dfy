include "modDiv.dfy"
include "list.dfy"

/**
 * Define the cycle function
 * Ensure some important properties into the cycle function
 * assert forall k: nat :: |source| <= k  < |dest|  ==> ModDiv.mod(k,|source|) < |source|;
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == source[ModDiv.mod(k,|source|)];
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == dest[k-|source|];
 */
module Cycle {

    import List
    import ModDiv

    function method isCycle(list: seq<nat>, listCycle: seq<nat>): bool
        requires |list| > 0;
    {
        var upperLimit := if |list| < |listCycle| then |list| else |listCycle|;

        var equalFirst     := forall k : nat :: 0      <= k < upperLimit           ==> listCycle[k] == list[k];
        var equalsPrevious := forall k : nat :: |list| <= k < |listCycle|          ==> listCycle[k] == listCycle[k - |list|];
        var equalsNext     := forall k : nat :: 0      <= k < |listCycle| - |list| ==> listCycle[k] == listCycle[k + |list|];

        equalFirst && equalsPrevious && equalsNext
    }
 
    function method cyclePos(source: seq<nat>, pos: nat): nat
        requires |source| > 0;
        ensures pos < |source| ==> cyclePos(source,pos) == source[pos];
        ensures pos > |source| ==> cyclePos(source,pos) == cyclePos(source, pos - |source|);
        ensures cyclePos(source,pos) == if pos < |source| then source[pos] else cyclePos(source, pos - |source|)
        decreases pos;
    {
        var s := |source|;
        assert s > 0;
        assert s > 0 ==> pos - s < pos;

        var cyclePosResult := if pos < |source| then source[pos] else cyclePos(source, pos - |source|);

        var posPlusSource := pos + |source|;

        cyclePosResult
    }
 
    function method cycle(source: seq<nat>, size: nat): seq<nat>
        requires |source| > 0;
        ensures |cycle(source,size)| == size;
        ensures isCycle(source, cycle(source,size));
        decreases size;
    {
        var cycleList := if size == 0 then [] else
        cycle(source,size-1) + [cyclePos(source,size - 1)];

        assert |cycleList| == size;
        assert |cycleList| > 0 ==> cycleList[0] == cyclePos(source,0);
        
        assert forall k: nat {:induction k} :: 0 <= k < |cycleList| ==> cycleList[k] == cyclePos(source,k);

        cycleList
    }

    /**
     * Ensure that the ModList is Cycle
     */
    lemma modIsCycle(modList: seq<nat>, loopValue: nat)
        requires loopValue > 0;
        requires |modList| > 0;
        requires loopValue <= |modList|;
        requires ModDiv.isModList(loopValue, modList);
        ensures isCycle(modList[..loopValue], modList);
    {
        ModDiv.modListValuesRepeat(modList, loopValue);
        var smallList := modList[..loopValue];
    }

    lemma cycleShouldContainsList(list: seq<nat>, cycleList: seq<nat>)
        requires |list| > 0;
        requires |cycleList| >= |list|;
        requires isCycle(list, cycleList);
        ensures cycleList[0..|list|] == list;
    {
    }

    lemma cycleAlwaysRepeatTheSameValues(list: seq<nat>, listCycle: seq<nat>, m: nat)
        requires m > 1;
        requires |list| > 0;
        requires |listCycle| == |list| * m;        
        requires isCycle(list, listCycle);
    {
        // going up //
        var k := 0;
        while ( k < |list| )
            decreases |list| - k;
            invariant k <= |list|;
        {
            var smallListValue := list[k];
            var bigKey := k;
            var n := 0;
            while ( bigKey < |listCycle| )
                decreases |listCycle| - bigKey;
                invariant bigKey == k + n * |list|;
                invariant ModDiv.mod(k + n * |list|,|list|) == ModDiv.mod(k,|list|);
                invariant ModDiv.mod(k,|list|) == k;
                invariant ModDiv.mod(bigKey,|list|) == k;
                invariant list[k] == list[ModDiv.mod(bigKey,|list|)];
                invariant bigKey < |listCycle| ==> listCycle[bigKey] == list[k];
                invariant bigKey < |listCycle| ==> listCycle[bigKey] == list[ModDiv.mod(bigKey,|list|)];
            {
                assert smallListValue == listCycle[bigKey];
                assert bigKey == k + n * |list|;
                assert smallListValue == listCycle[bigKey];
                ModDiv.modSmallValues(k,|list|);
                assert k < |list|;
                assert ModDiv.mod(k,|list|) == k;
                ModDiv.modAOnBEqualsModAMoreMTimesB(k,|list|,n);
                assert ModDiv.mod(k + n * |list|,|list|) == ModDiv.mod(k,|list|);
                assert ModDiv.mod(bigKey,|list|) == ModDiv.mod(k,|list|);
                assert ModDiv.mod(bigKey,|list|) == k;
                if ( bigKey + |list| < |listCycle| )
                {
                    assert listCycle[bigKey] == listCycle[bigKey + |list|];
                }
                n := n + 1;
                bigKey := bigKey + |list|;
                ModDiv.modAOnBEqualsModAMoreMTimesB(k,|list|,n);
                assert ModDiv.mod(k + n * |list|,|list|) == ModDiv.mod(k,|list|);
                assert ModDiv.mod(bigKey,|list|) == ModDiv.mod(k,|list|);
            }
            k := k + 1;
        }
        
        assert forall k : nat :: k <= 0 < |listCycle| ==> listCycle[k] == list[ModDiv.mod(k,|list|)];
    }

    // sounds good, does not work
    //
    // lemma cycleAlwaysRepeatTheSameValues(list: seq<nat>, listCycle: seq<nat>, m: nat)
    //     requires m > 1;
    //     requires |list| > 0;
    //     requires |listCycle| == |list| * m;        
    //     requires isCycle(list, listCycle);
    //     ensures
    //         forall k : nat :: 0 <= k < |list|   ==> 
    //         forall n : nat :: 0 <= n < m        ==> 
    //         k + n * |list| < |listCycle|        ==> 
    //         listCycle[k + n * |list|] == list[k];
    // {
    //     assert forall k : nat :: 0      <= k < |list|      ==> listCycle[k] == list[k];
    //     assert forall k : nat :: |list| <= k < |listCycle| ==> listCycle[k] == listCycle[k - |list|];


    //     // going up //
    //     var k := 0;
    //     while ( k < |list| )
    //         decreases |list| - k;
    //         invariant k <= |list|;
    //     {
    //         var current := list[k];
    //         var next := k;
    //         var n := 0;
    //         assert next == k + n * |list|;
    //         while ( next < |listCycle| )
    //             decreases |listCycle| - next;
    //             invariant next < |listCycle| ==> current == listCycle[next];
    //             invariant next < |listCycle| ==> current == list[k];
    //             invariant next < |listCycle| ==> listCycle[next] == list[k];
    //             invariant next == k + n * |list|;
    //             invariant next < |listCycle| ==> listCycle[k + n * |list|] == list[k];
    //             invariant 
    //                 k + n * |list| < |listCycle|        ==> 
    //                 listCycle[k + n * |list|] == list[k];
    //         {
    //             assert current == listCycle[next];
    //             assert next == k + n * |list|;
    //             assert listCycle[k + n * |list|] == list[k];
    //             n := n + 1;
    //             next := next + |list|;
    //         }
    //         assert next >= |listCycle|;
    //         k := k + 1;
    //     }
    //     assert k == |list|;

    //     // going down //
    //     k := 0;
    //     while ( k < |listCycle| )
    //         decreases |listCycle| - k;
    //         invariant k <= |listCycle|;
    //     {
    //         var current := listCycle[k];
    //         var prev := k;
    //         var n := 0;
    //         assert prev == k - n * |list|;
    //         while ( prev > |list| )
    //             decreases prev;
    //             invariant prev >= 0 ==> current == listCycle[prev];
    //             invariant prev >= |list| ==> current == listCycle[prev - |list|];
    //             invariant prev == k - n * |list|;
    //             // invariant 
    //             //     k + n * |list| < |listCycle|        ==> 
    //             //     listCycle[k + n * |list|] == list[k];
    //         {
    //             assert current == listCycle[prev];
    //             assert listCycle[prev] == listCycle[prev - |list|];
    //             assert prev == k - n * |list|;
    //             assert listCycle[k - n * |list|] == listCycle[prev - |list|];
    //             n := n + 1;
    //             prev := prev - |list|;
    //         }
    //         assert prev <= |list|;
    //         k := k + 1;
    //     }

    //     assert
    //         forall k : nat :: 0 <= k < |list|   ==> 
    //         forall n : nat :: 0 <= n < m        ==> 
    //         k + n * |list| < |listCycle|        ==> 
    //         listCycle[k + n * |list|] == list[k];
    // }

    // lemma cycleByConcat(list: seq<nat>, cycleList: seq<nat>, smallCycle: seq<nat>, m: nat)
    //     requires |list| > 0;
    //     requires |cycleList| > |list|;
    //     requires |smallCycle| > |list|;
    //     requires isCycle(list, cycleList);
    //     requires isCycle(list, smallCycle);
    //     requires |cycleList| == |list| * m;
    //     requires |smallCycle| == |cycleList| - |list|;
    //     requires |smallCycle| == |list| * ( m - 1 );
    //     requires m > 0;
    //     ensures cycleList == list + cycleList[|list|..];
    //     ensures smallCycle == cycleList[..|smallCycle|];
    //     ensures cycleList == list + smallCycle;
    // {
    //     assert smallCycle[0..|list|] == list;
    //     assert cycleList[0..|list|] == list;
    //     assert forall k: nat 
    // }


//     lemma sumMultipleList(list: seq<nat>, cycleList: seq<nat>, m: nat)
//         requires m > 0;
//         requires |list| > 0;
//         requires |cycleList| > 0;
//         requires |cycleList| >= |list|;
//         requires isCycle(list, cycleList);
//         requires |cycleList| == |list| * m;
//         ensures List.sum(cycleList) == List.sum(list) * m;
//         decreases cycleList, m;
//     {
//         if m == 1 {
//             assert cycleList == list;
//         } else {
//             var smallCycle := cycleList[|list|..];
//             assert cycleList == list + smallCycle;
//             assert isCycle(list, smallCycle);
//             List.distributiveSum(list,smallCycle);
//             assert List.sum(cycleList) == List.sum(list) + List.sum(smallCycle);
//             sumMultipleList(list,smallCycle, m-1);
//         }
//     }

//     lemma cycleListIsListPlusSmallCycleList(list: seq<nat>, cycleList: seq<nat>, smallCycle: seq<nat>, m: nat)
//         requires |list| > 0;
//         requires |cycleList| >= |list|;
//         requires m > 0;
//         requires isCycle(list, cycleList);
//         requires |cycleList| == |list| * m;
//         requires smallCycle == cycleList[|list|..];
//         ensures cycleList == list + smallCycle;
//         ensures List.sum(cycleList) == List.sum(list) + List.sum(smallCycle);
//         ensures |smallCycle| > 0 ==> isCycle(list, smallCycle);
//         ensures |smallCycle| == |list| * (m - 1);
//     {
//         List.distributiveSum(list,smallCycle);
//         assert |cycleList| == |list| * m;
//         assert forall v : nat :: 0 <= v < |list| ==> cycleList[v] == list[v];
//         assert |cycleList| >= |list|;
//         assert cycleList == list + smallCycle;
//         assert |smallCycle| > 0 ==> isCycle(list,smallCycle);
//         assert |smallCycle| == |list| * (m - 1);
//     }
// //     method Main()
// //     {
// //         print("\ntesting cycle\n");
// //         print(isCycle([1,2,3],[1,2,3,1,2,3,1,4]));
// //         print("\n:D\n");
// //     }
}