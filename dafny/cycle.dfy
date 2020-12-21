include "mod.dfy"

/**
 * Define the cycle function
 * Ensure some important properties into the cycle function
 * assert forall k: nat :: |source| <= k  < |dest|  ==> Mod.mod(k,|source|) < |source|;
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == source[Mod.mod(k,|source|)];
 * assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == dest[k-|source|];
 */
module Cycle {

    import Mod

    function method cyclePos(list: seq<nat>, pos: nat): nat
        requires |list| > 0;
    {
        var l := |list|;
        var k := Mod.mod(pos, l);
        Mod.remainderShouldBeSmall(pos,l,k);
        assert k < l;
        var result := list[k];
        result
    }

    lemma checkCyclePos(list: seq<nat>, pos: nat, key: nat, result: nat)
        requires |list| > 0;
        requires key == Mod.mod(pos,|list|);
        requires result == cyclePos(list, pos);
        ensures key < |list|;
        ensures result == list[key];
    {
        Mod.remainderShouldBeSmall(pos,|list|,key);
    }

    method cycle(source: seq<nat>, size: nat) returns (result: seq<nat>)
        requires |source| > 0;
        ensures forall k : nat :: 0 <= k < |result| ==> Mod.mod(k,|source|) < |source|;
        ensures forall k : nat :: 0 <= k < |result| ==> result[k] == source[Mod.mod(k,|source|)];
        ensures |result| == size;
    {
        result := [];   
        while( |result| < size ) 
            invariant forall k : nat :: 0 <= k < |result| ==> result[k] == source[Mod.mod(k,|source|)];
            invariant |result| <= size;
            decreases size - |result|;
        {
            var value := cyclePos(source, |result|);            
            result := result + [value];
        }
        assert |result| == size;
    }

    function isCycle(list: seq<nat>, listCycle: seq<nat>): bool
        requires |list| > 0;
        requires |listCycle| >= |list|;
    {
        assert forall k : nat :: |list| <= k < |listCycle| ==> Mod.mod(k,|list|) == Mod.mod(k - |list|,|list|);
        assert forall k : nat :: 0 <= k < |list| ==> Mod.mod(k,|list|) == k;
        forall k : nat :: 0 <= k < |listCycle| ==> listCycle[k] == list[Mod.mod(k,|list|)]
    }

    method checkCycle(source: seq<nat>, m: nat)
        requires |source| > 0;
        requires m > 0;
    {
        var dest := cycle( source, |source| * m);
        assert |dest| == |source| * m;
        assert forall k: nat :: 0 <= k < |source|  ==> dest[k] == source[k];
        assert forall k: nat :: |source| <= k  < |dest|  ==> Mod.mod(k,|source|) < |source|;
        assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == source[Mod.mod(k,|source|)];
        assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == dest[k-|source|];
    }

    method test()
    {
        var source := [1,2,3];
        checkCycle(source,2);
        var dest := cycle(source,7);
        assert |dest| == 7;
        assert forall k: nat :: |source| <= k  < |dest|  ==> Mod.mod(k,|source|) < |source|;
        assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == source[Mod.mod(k,|source|)];
        assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == dest[k-|source|];
        assert |source| == 3;
        assert dest[0] == dest[3] == dest[6] == source[0];
        assert dest[1] == dest[4] == source[1];
        assert dest[2] == dest[5] == source[2];
        assert source == [1,2,3];
        assert dest == [1,2,3,1,2,3,1];
        print("dest = ");
        print(dest);
    }

    // method Main()
    // {
    //     print("\ntesting cycle\n");
    //     test();
    //     print("\n:D\n");
    // }
}