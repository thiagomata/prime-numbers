include "modDiv.dfy"
include "list.dfy"

/**
 * Define the cycle function
 * Ensure some important properties into the cycle function
 * assert forall k: nat :: |source| <= k  < |dest|  ==> ModDiv.mod(k,|source|) < |source|;
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == source[ModDiv.mod(k,|source|)];
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == dest[k-|source|];
 */
module CycleFromMod {

    import ModDiv
    import List

    function method isCycle(list: seq<nat>, listCycle: seq<nat>): bool
        requires |list| > 0;
    {
        var equalsMod := forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[ ModDiv.mod(k, |list|) ];

        equalsMod
    }
    
    function method cyclePos(list: seq<nat>, pos: nat): nat
        requires |list| > 0;
        ensures cyclePos(list,pos) == list[ModDiv.mod(pos,|list|)];
    {
        var l := |list|;
        var k := ModDiv.mod(pos, l);
        assert k < l;
        var result := list[k];
        result
    }

    method cycle(source: seq<nat>, size: nat) returns (result: seq<nat>)
        requires |source| > 0;
        ensures forall k : nat :: 0 <= k < |result| ==> ModDiv.mod(k,|source|) < |source|;
        ensures forall k : nat :: 0 <= k < |result| ==> result[k] == source[ModDiv.mod(k,|source|)];
        ensures |result| == size;
    {
        result := [];   
        while( |result| < size ) 
            invariant forall k : nat :: 0 <= k < |result| ==> result[k] == source[ModDiv.mod(k,|source|)];
            invariant |result| <= size;
            decreases size - |result|;
        {
            var value := cyclePos(source, |result|);
            result := result + [value];
        }
        assert |result| == size;
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
    
    lemma cycleListIsListPlusSmallCycleList(list: seq<nat>, cycleList: seq<nat>, smallCycle: seq<nat>, m: nat)
        requires |list| > 0;
        requires |cycleList| >= |list|;
        requires m > 0;
        requires isCycle(list, cycleList);
        requires |cycleList| == |list| * m;
        requires  smallCycle == cycleList[|list|..];
        ensures cycleList == list + smallCycle;
        ensures List.sum(cycleList) == List.sum(list) + List.sum(smallCycle);
        ensures |smallCycle| > 0 ==> isCycle(list, smallCycle);
        ensures |smallCycle| == |list| * (m - 1);
    {
        List.distributiveSum(list,smallCycle);
        assert |cycleList| == |list| * m;
        assert forall v : nat :: 0 <= v < |list| ==> cycleList[v] == list[v];
        assert |cycleList| >= |list|;
        assert cycleList == list + smallCycle;
        assert |smallCycle| > 0 ==> isCycle(list,smallCycle);
        assert |smallCycle| == |list| * (m - 1);
    }

//     method Main()
//     {
//         print("\ntesting cycle\n");
//         print(isCycle([1,2,3],[1,2,3,1,2,3,1,4]));
//         print("\n:D\n");
//     }
}