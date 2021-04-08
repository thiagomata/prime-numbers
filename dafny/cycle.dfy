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
        requires ModDiv.isModListFromValue(loopValue, modList);
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

    /**
     * We can predict the values of the cycle list based in the original list
     * using mod function
     *
     * listCycle[k] == list[mod(k,|list|)]
     */
    lemma cycleAlwaysRepeatTheSameValues(list: seq<nat>, listCycle: seq<nat>)
        requires |list| > 0;
        requires isCycle(list, listCycle);
        ensures forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[ModDiv.mod(k,|list|)];
    {
        var k := 0;
        while ( k < |listCycle| )
            decreases |listCycle| - k;
            invariant k <= |listCycle|;
            invariant forall i : nat :: 0 <= i < k ==> listCycle[i] == list[ModDiv.mod(i, |list|)];
        {
            if ( k < |list| ) {
                assert ModDiv.mod(k, |list|) == k;
                assert listCycle[k] == list[k];
                assert listCycle[k] == list[ModDiv.mod(k, |list|)];
            } else {
                assert listCycle[k] == listCycle[k-|list|];
                assert listCycle[k-|list|] == list[ModDiv.mod(k - |list|, |list|)];
                ModDiv.modAOnBEqualsModAPlusBOnB(k - |list|, |list|);
                assert ModDiv.mod(k - |list|, |list|) == ModDiv.mod(k, |list|);
                assert listCycle[k] == list[ModDiv.mod(k, |list|)];
            }
            k := k + 1;
        }
        assert forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[ModDiv.mod(k,|list|)];
    }

    /**
     * Every cycle list can be replaced by the original list concatenated by
     * a smaller cycle list.
     *
     * cycleList == list + smallCycle
     */
    lemma cycleByConcat(list: seq<nat>, cycleList: seq<nat>, smallCycle: seq<nat>, m: nat)
        requires |list| > 0;
        requires |cycleList| > |list|;
        requires |smallCycle| >= |list|;
        requires isCycle(list, cycleList);
        requires isCycle(list, smallCycle);
        requires |cycleList| == |list| * m;
        requires |smallCycle| == |cycleList| - |list|;
        requires |smallCycle| == |list| * ( m - 1 );
        requires m > 0;
        ensures cycleList == list + cycleList[|list|..];
        ensures smallCycle == cycleList[..|smallCycle|];
        ensures cycleList == list + smallCycle;
    {

        cycleAlwaysRepeatTheSameValues( list, cycleList);
        cycleAlwaysRepeatTheSameValues( list, smallCycle);
    }

    /**
     * if cycleList is list n times then the sum of the cycle list
     * is the sum of the list times n.
     *
     * List.sum(cycleList) == List.sum(list) * m
     */
    lemma sumMultipleList(list: seq<nat>, cycleList: seq<nat>, m: nat)
        requires m > 0;
        requires |list| > 0;
        requires |cycleList| > 0;
        requires |cycleList| >= |list|;
        requires isCycle(list, cycleList);
        requires |cycleList| == |list| * m;
        ensures List.sum(cycleList) == List.sum(list) * m;
        decreases cycleList, m;
    {
        if m == 1 {
            assert cycleList == list;
        } else {
            var smallCycle := cycleList[|list|..];
            assert cycleList == list + smallCycle;
            assert isCycle(list, smallCycle);
            List.distributiveSum(list,smallCycle);
            assert List.sum(cycleList) == List.sum(list) + List.sum(smallCycle);
            sumMultipleList(list,smallCycle, m-1);
        }
    }

    /**
     * mod(sum(cycle(list,m)),m) == 0
     *
     * Any cycle list that is a repetition of the list m times
     * will have the sum a value that its module by m is zero
     */
    lemma cycleSameMod(list: seq<nat>, cycleList: seq<nat>, m: nat)
        requires m > 0;
        requires |list| > 0;
        requires |cycleList| > 0;
        requires |cycleList| >= |list|;
        requires isCycle(list, cycleList);
        requires |cycleList| == |list| * m;
        ensures List.sum(cycleList) == m * List.sum(list);
        ensures ModDiv.mod(List.sum(cycleList), m) == 0;
    {
        sumMultipleList(list,cycleList, m);
        var listSum := List.sum(list);
        var cycleListSum := List.sum(cycleList);
        assert listSum * m == cycleListSum;
        
        ModDiv.modBOfMTimesB(m, listSum);

    }

    lemma cycleMultipleMod(list: seq<nat>, cycleList: seq<nat>, m1: nat, m2: nat)
        requires m1 > 0;
        requires m2 > 0;
        requires |list| > 0;
        requires |cycleList| > 0;
        requires |cycleList| >= |list|;
        requires isCycle(list, cycleList);
        requires ModDiv.mod(List.sum(list), m1) == 0;
        requires |cycleList| == |list| * m2;
        ensures List.sum(cycleList) == m2 * List.sum(list);
        ensures ModDiv.mod(List.sum(cycleList), m1) == 0;
    {
        sumMultipleList(list,cycleList, m2);
        var listSum := List.sum(list);
        var cycleListSum := List.sum(cycleList);
        assert listSum * m2 == cycleListSum;
        
        ModDiv.modATimesNIsZero(m1, listSum, m2);

    }

    lemma cycleNonZero(list: seq<nat>, cycleList: seq<nat>, m: nat)
        requires m > 0;
        requires |list| > 0;
        requires |cycleList| > 0;
        requires |cycleList| >= |list|;
        requires isCycle(list, cycleList);
        requires |cycleList| == |list| * m;
        requires List.nonZero(list);
        ensures List.nonZero(cycleList);
    {
        cycleAlwaysRepeatTheSameValues(list,cycleList);
    }


    lemma cycleValueProportion(list: seq<nat>, cycleList: seq<nat>, m: nat, value: nat)
        requires m > 0;
        requires |list| > 0;
        requires |cycleList| > 0;
        requires |cycleList| >= |list|;
        requires isCycle(list, cycleList);
        requires |cycleList| == |list| * m;
        ensures List.countWithValue(list,value) * m == List.countWithValue(cycleList,value);
    {
        cycleAlwaysRepeatTheSameValues(list,cycleList);
        var countList := List.countWithValue(list,value);
        var countCycle := List.countWithValue(cycleList,value);
         if m == 1 {
            assert cycleList == list;
        } else {
            var smallCycle := cycleList[|list|..];
            assert cycleList == list + smallCycle;
            assert isCycle(list, smallCycle);
            List.distributiveCount(list,smallCycle,value);
            assert List.countWithValue(list,value) + List.countWithValue(smallCycle,value) == List.countWithValue(cycleList,value);
            var smallCount := List.countWithValue(smallCycle,value);
            cycleValueProportion(list,smallCycle,m - 1,value);
        }
   }

    lemma proportionOnPerfectCycle(list: seq<nat>, m: nat,searchValue: nat)
        requires m  > 0;
        requires |list| > 0;
        ensures List.countWithValue(cycle(list, |list| * m),searchValue) == List.countWithValue(list,searchValue) * m;
        decreases m;
    {
        var cycleList := cycle(list, ( m * |list| ) );
        if ( m == 1 ) {
            assert cycleList == list;
            assert List.countWithValue(cycleList,searchValue) == List.countWithValue(list,searchValue) * m;
        } else {
            assert m > 1;
            var smallCycle := cycle(list, (m - 1) * |list| );
            assert |smallCycle| == (m - 1 ) * |list|;
            assert |smallCycle| >= |list|;
            cycleByConcat(list, cycleList, smallCycle, m);
            assert cycleList == list + smallCycle;
            proportionOnPerfectCycle(list, m - 1, searchValue);
            
            assert list + smallCycle == cycleList; 
            List.distributiveCount(list,smallCycle,searchValue);
            assert List.countWithValue(cycleList,searchValue) ==
                List.countWithValue(list,searchValue) +
                List.countWithValue(smallCycle,searchValue);
            assert List.countWithValue(smallCycle, searchValue) == List.countWithValue(list,searchValue) * (m - 1);
            assert List.countWithValue(cycleList,searchValue) ==
                List.countWithValue(list,searchValue) +
                List.countWithValue(list,searchValue) * (m - 1);
            assert List.countWithValue(cycleList,searchValue) == List.countWithValue(list,searchValue) * m;
        }
        assert List.countWithValue(cycleList,searchValue) == List.countWithValue(list,searchValue) * m;
    }

    lemma shiftedCycleIsCycleShifted(list: seq<nat>, cycleList: seq<nat>, m: nat)
        requires m > 1;
        requires |list| > 1;
        requires |cycleList| > 0;
        requires |cycleList| == |list| * m;
        requires isCycle(list,cycleList);
        // ensures isCycle(List.shift(list),List.shift(cycleList));
        ensures List.shift(cycleList) == cycle(List.shift(list),|cycleList|);
    {
        var shifted := List.shift(list);
        assert |shifted| == |list|;
        var shiftedCycle := cycle(shifted,|cycleList|);
        var cycleShifted := List.shift(cycleList);
        assert |shiftedCycle| == |cycleList|;
        assert |cycleList| > |list|;
        // if( |list| == 1 ) {
        //     assert list == shifted;
        //     cycleAlwaysRepeatTheSameValues(list,cycleList);
        //     cycleAlwaysRepeatTheSameValues(shifted,shiftedCycle);
        //     var c := |shiftedCycle|;
        //     assert forall k : nat :: 0 <= k < c ==> shiftedCycle[k] == shifted[ModDiv.mod(k,1)];
        //     assert forall k : nat :: 0 <= k < c ==> ModDiv.mod(k,1) == 0;
        //     assert forall k : nat :: 0 <= k < c ==> shiftedCycle[k] == shifted[0];
        //     assert forall k : nat :: 0 <= k < c ==> cycleList[k] == list[0];
        //     assert shiftedCycle == cycleList;
        // } else {
            cycleAlwaysRepeatTheSameValues(list,cycleList);
            cycleAlwaysRepeatTheSameValues(shifted,shiftedCycle);
            assert forall k : nat :: 0 <= k < |cycleList| ==> cycleList[k] == list[ModDiv.mod(k,|list|)];
            assert forall k : nat :: 1 <= k < |cycleList| - 1 ==> 
                cycleShifted[k] == 
                cycleList[k + 1] == 
                list[ModDiv.mod(1 + k,|list|)];

            assert forall k : nat :: 0 <= k < |shiftedCycle| ==> shiftedCycle[k] == shifted[ModDiv.mod(k,|shifted|)];
            assert ModDiv.mod(1,|shifted|) == 1;
            assert forall v :: 0 <= v < |list| - 1 ==> shifted[v] == list[v+1] == cycleList[v+1];
            assert cycleList[|list|] == cycleList[|list| - |list|] == cycleList[0] == list[0];
            assert shifted[|list|-1] == list[0];
            assert shifted[|list|-1] == cycleList[|list|];
            assert forall v :: 0 <= v < |shifted| ==> shifted[v] == cycleList[v+1];
            forall k | 0 <= k < |shiftedCycle| - 1
                ensures cycleShifted[k] == shiftedCycle[k];
            {
                assert |shifted| == |list|;
                assert |shiftedCycle| == |cycleList|;
                var n := ModDiv.mod(k,|shifted|);
                assert n < |list|;
                assert n < |shifted|;
                assert shiftedCycle[k] == shifted[n];
                assert cycleList[1 + n] == list[ModDiv.mod(1+n,|list|)] == 
                    list[
                        ModDiv.mod(
                            1 + ModDiv.mod(k,|list|),
                            |list|
                        )
                    ];
                assert ModDiv.mod(
                            1 + ModDiv.mod(k,|list|),
                            |list|
                        ) == 
                        ModDiv.mod(
                            ModDiv.mod(1,|list|) + ModDiv.mod(k,|list|),
                            |list|
                        );
                ModDiv.modAplusB(|list|,1,k);
                assert ModDiv.mod(
                            ModDiv.mod(1,|list|) + ModDiv.mod(k,|list|),
                            |list|
                        ) == ModDiv.mod(1 + k,|list|);
                assert cycleList[1 + k] == list[ModDiv.mod(1 + k,|list|)];
                assert cycleList[1 + n] == cycleList[1 + k];
                assert shifted[n] == cycleList[1 + n] == cycleList[1 + k];
                assert shiftedCycle[k] == cycleList[1 + k] == cycleShifted[k];
            }
            assert forall k :: 0 <= k < |shiftedCycle| - 1 ==> cycleShifted[k] == shiftedCycle[k];
            assert cycleShifted[0] == shiftedCycle[0];

            assert List.last(shiftedCycle) == shifted[ModDiv.mod(|shiftedCycle| - 1,|shifted|)];
            ModDiv.isModDivMinusTimes(1,|shifted|,m);
            
            assert ModDiv.mod(|shiftedCycle| - 1,|shifted|) == ModDiv.mod(|shifted| - 1,|shifted|) == |shifted| - 1;
            assert List.last(shiftedCycle) == List.last(shifted) == list[0] == cycleList[0] == List.last(cycleShifted);
            assert List.last(cycleList)    == List.last(list)    == list[ModDiv.mod(|list| - 1, |list|)];
            
            assert ModDiv.mod(|cycleList| - 1,|cycleList|) == ModDiv.mod(|list| - 1,|list|) == |list| - 1;
            assert List.last(cycleList) == List.last(list) == shifted[0] == shiftedCycle[0] == cycleShifted[0];
            
            // assert forall k : nat :: 0      <= k < |list|                  ==> cycleShifted[k] == list[k];
            // assert forall k : nat :: |list| <= k < |cycleShifted|          ==> cycleShifted[k] == cycleShifted[k - |list|];
            // assert forall k : nat :: 0      <= k < |cycleShifted| - |list| ==> cycleShifted[k] == cycleShifted[k + |list|];

            assert shiftedCycle == cycleShifted;
        // }
    }
//     method Main()
//     {
//         print("\ntesting cycle\n");
//         print(isCycle([1,2,3],[1,2,3,1,2,3,1,4]));
//         print("\n:D\n");
//     }
}