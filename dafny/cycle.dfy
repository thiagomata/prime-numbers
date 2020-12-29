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
    {
        var equalsMod := forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[ ModDiv.mod(k, |list|) ];

        equalsMod
    }
    function method isCycleGap(list: seq<nat>, listCycle: seq<nat>, gap: nat): bool
        requires |list| > 0;
    {
        var equalsMod := forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[ ModDiv.mod(k + gap, |list|) ];

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

    /**
     * Since the current definition of the cycle mod is alligned with the definition of the isModDiv
     * all the properties defined to the isModDiv can be applied to the cycle.
     */
    lemma cycleIsMod(list: seq<nat>, listCycle: seq<nat>, m: nat)
        requires |list| > 0;
        requires |listCycle| == |list| * m;
        requires isCycle(list, listCycle);
        ensures forall k : nat :: 0 <= k < |listCycle| ==> ModDiv.isModDiv(k, |list|, m, ModDiv.mod(k, |list|));
    {
        assert forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[ ModDiv.mod(k, |list|) ];
        //  * assert division * b + remainder == a
        //  * assert remainder < b;
        //  * assert remainder <= a;
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