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
        // requires |listCycle| == |list| * m;        
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
        requires |smallCycle| > |list|;
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

//     method Main()
//     {
//         print("\ntesting cycle\n");
//         print(isCycle([1,2,3],[1,2,3,1,2,3,1,4]));
//         print("\n:D\n");
//     }
}