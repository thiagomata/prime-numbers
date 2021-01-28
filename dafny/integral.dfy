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

    method integral(list: seq<nat>, initial: nat ) returns (result: seq<nat>)
        ensures |list| == |result|;
        ensures isIntegral(list,initial,result);
    {
        var distance := |list|;
        var arr := new nat[distance];
        var k := 0;
        var acc := initial;
        while (k < |list|)
            decreases |list| - k;
            invariant 0 <= k <= |list|;
            invariant forall v: nat :: 0 <= v < k ==> arr[v] == List.sum(list[..v+1]) + initial;
        {
            /* 
             * Could not make it work using acc, what would be fast.
             * This is not the fast strategy, but for sure is correct
             */
            arr[k] := List.sum(list[..k+1]) + initial;
            k := k + 1;
        }
        // array to seq
        result := arr[..];
    }

    function isDerivetive(list: seq<nat>, initial: nat, listDerivetive: seq<nat>): bool
        requires |list| == |listDerivetive|;
    {
        ( forall v: nat :: 0 < v < |list| ==> ( list[v] >= list[v-1] && listDerivetive[v] == list[v] - list[v-1] ) )
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

    function isListModList(list: seq<nat>, value: nat, modList: seq<nat>): bool
        requires |list| == |modList|;
        requires |list| > 0;
        requires value > 0;
    {
        forall v: nat :: 0 <= v < |list| ==> modList[v] == ModDiv.mod(list[v], value)
    }

    method modList(list: seq<nat>, value: nat ) returns (modList: seq<nat>)
        requires |list| > 0;
        requires value > 0;
        ensures |list| == |modList|;
        ensures isListModList(list,value,modList);
    {
        var distance := |list|;
        var arr := new nat[distance];
        var k := 0;
        while (k < |list|)
            decreases |list| - k;
            invariant 0 <= k <= |list|;
            invariant forall v: nat :: 0 <= v < k ==> arr[v] == ModDiv.mod(list[v], value);
        {
            arr[k] := ModDiv.mod(list[k], value);
            k := k + 1;
        }
        modList := arr[..];
        assert |list| == |modList|;
    }


    function isNotMultiple(list: seq<nat>, value: nat): bool
        requires value > 0;
        // requires |list| > 0;
    {
        forall v: nat :: 0 <= v < |list| ==> ModDiv.mod(list[v], value) != 0
    }

    method modOfIntegralIsCycle(
        list: seq<nat>,
        m: nat,
        v: nat,
        initial: nat
    )
        requires m > 0; // 2
        requires v > 0; // 3

        // list is non zero, non empty and the List.sum of the list is multiple of m
        requires |list| > 0; // 2
        requires List.nonZero(list); // [2,4]
        requires ModDiv.mod(List.sum(list), v) == 0; // 2 + 4 == 6; mod(6,3) == 0
    {
        var integralList := integral(list, initial);
        assert isIntegral(list, initial, integralList);

        var modIntegralList := modList(integralList, v);

        var cycleList := Cycle.cycle(list, |list| * m);
        assert Cycle.isCycle(list, cycleList);
        
        var integralCycle := integral(cycleList, initial);

        var modIntegralCycle := modList(integralCycle, v);

        modOfIntegralIsCycleFull(
            list, 
            initial, 
            integralList, 
            modIntegralList, 
            // m,
            v, 
            cycleList, 
            integralCycle,
            modIntegralCycle
        );

        assert Cycle.isCycle(modIntegralList, modIntegralCycle); // [1,2,1,2] == cycle([1,2],m)
        assert List.nonZero(modIntegralList) ==> List.nonZero(modIntegralCycle);

    }

    /**
     * If we have a list of steps such as 
     * the integral of the steps plus the initial value are not multiple of v in any moment, 
     * and the sum of the steps is multiple of the value v, 
     * we can keep adding the steps in cycle ensuring that they
     * will also not be multiple of v.
     */
    lemma modOfIntegralIsCycleFull(
        list: seq<nat>, 
        initial: nat, 
        integralList: seq<nat>, 
        modIntegralList: seq<nat>, 
        // m: nat,
        v: nat, 
        cycleList: seq<nat>, 
        integralCycle: seq<nat>,
        modIntegralCycle: seq<nat>
    )

    // m and v are bigger than zero
    // requires m > 0; // 2
    requires v > 0; // 3

    // list is non zero, non empty and the List.sum of the list is multiple of m
    requires |list| > 0; // 2
    requires List.nonZero(list); // [2,4]
    requires ModDiv.mod(List.sum(list), v) == 0; // 2 + 4 == 6; mod(6,3) == 0


    // integral list def
    requires |integralList| == |list|; // [7,11] // [2,4]
    requires isIntegral(list, initial, integralList); // [7 == 5 + 2, 11 == 5 + 2 + 4]
    
    // mod of integral list def
    requires |modIntegralList| == |integralList|; // [7, 11] // [7 % 3, 11 % 3 ] == [1, 2]
    requires isListModList(integralList, v, modIntegralList);

    // cylce list def
    // requires |cycleList| == |list| * m; // [2,4,2,4]
    requires |cycleList| >= |list|;
    requires Cycle.isCycle(list, cycleList)

    // integral cycle def
    requires |integralCycle| == |cycleList|; // [7, 11, 13, 17]
    requires isIntegral(cycleList, initial, integralCycle); // [5+2,5+2+4,5+2+4+2,5+2+4+2+4] ...
    
    // mod of integral cycle def
    requires |integralCycle| == |modIntegralCycle|; // [7 % 3, 11 %3, 13 % 3, 17 % 3]
    requires isListModList(integralCycle, v, modIntegralCycle); // [1, 2, 1, 2]

    // mod of integral should be cycle
    ensures Cycle.isCycle(modIntegralList, modIntegralCycle); // [1,2,1,2] == cycle([1,2],m)
    ensures List.nonZero(modIntegralList) ==> List.nonZero(modIntegralCycle);
    {
        // for the first elements integralCycle is equal to integralList
        // and mod integral cycle list equals mod integral list
        var k: nat;
        assert list == cycleList[..|list|];
        forall k | 0 <= k < |list|
            ensures integralCycle[k] == integralList[k];
            ensures modIntegralCycle[k] == modIntegralList[k];
        {
            assert cycleList[k] == list[k];
            
            assert integralList[k]   == List.sum(list[0..k+1])      + initial;

            assert integralCycle[k]  == List.sum(cycleList[0..k+1]) + initial;
            assert cycleList[k]      == list[k];
            assert cycleList[0..k+1] == list[0..k+1];
            
            assert List.sum(cycleList[0..k+1]) == List.sum(list[0..k+1]);
            
            assert integralCycle[k] == List.sum(list[0..k+1]) + initial;
            assert integralCycle[k] == integralList[k];
            
            assert modIntegralList[k]  == ModDiv.mod(integralList[k],  v);
            assert modIntegralCycle[k] == ModDiv.mod(integralCycle[k], v);
            assert modIntegralCycle[k] == ModDiv.mod(integralList[k],  v);
            assert modIntegralCycle[k] == modIntegralList[k];
        }

        assert integralList    == integralCycle[..|list|];
        assert modIntegralList == modIntegralCycle[..|list|];

        forall k | |list| <= k < |modIntegralCycle|
            ensures modIntegralCycle[k-|list|] == modIntegralCycle[k];
        {
            assert integralCycle[k] == List.sum(cycleList[0..k+1]) + initial;
            var c1 := cycleList[0..|list|];
            var c2 := cycleList[|list|..k+1];
            assert cycleList[0..k+1] == c1 + c2; 
            List.distributiveSum(c1,c2);
            assert List.sum(c1 + c2) == List.sum(c1) + List.sum(c2); 
            assert integralCycle[k] == List.sum(cycleList[0..|list|] + cycleList[|list|..k+1]) + initial;
            assert integralCycle[k] == List.sum(cycleList[0..|list|]) + List.sum(cycleList[|list|..k+1]) + initial;
            assert integralCycle[k] == List.sum(c1) + List.sum(c2) + initial;
            var listSum := List.sum(cycleList[0..|list|]);
            assert List.nonZero(list);
            assert listSum > 0;
            assert ModDiv.mod(listSum, v) == 0;
            assert integralCycle[k] == listSum + List.sum(c2) + initial;
            var otherValue := List.sum(cycleList[|list|..k+1]) + initial;
            assert integralCycle[k] == listSum + otherValue;
            ModDiv.modAplusB(v, listSum, otherValue);
            assert modIntegralCycle[k] == ModDiv.mod(integralCycle[k], v);
            assert modIntegralCycle[k] == ModDiv.mod(listSum + otherValue, v);
            assert modIntegralCycle[k] == ModDiv.mod(ModDiv.mod(listSum, v) + ModDiv.mod(otherValue, v), v);
            assert modIntegralCycle[k] == ModDiv.mod(0 + ModDiv.mod(otherValue, v), v);
            assert modIntegralCycle[k] == ModDiv.mod(ModDiv.mod(otherValue, v), v);
            assert modIntegralCycle[k] == ModDiv.mod(otherValue, v);
            assert cycleList[|list|..k+1] == cycleList[0..k+1-|list|];
            assert otherValue == List.sum(cycleList[0..k+1-|list|]) + initial;
            assert modIntegralCycle[k-|list|] == ModDiv.mod(integralCycle[k-|list|],v);
            assert integralCycle[k-|list|] == otherValue;
            assert modIntegralCycle[k-|list|] == ModDiv.mod(otherValue,v);
            assert modIntegralCycle[k-|list|] == modIntegralCycle[k];
        }

        Cycle.cycleAlwaysRepeatTheSameValues(modIntegralList, modIntegralCycle);
    }

    function isFilterMultiples(list: seq<nat>, v: nat, filtered: seq<nat>): bool
        requires v > 0;
    {
        if |list| == 0 then filtered == []
        else if |filtered| > |list| then false
        else if ModDiv.mod(list[0], v) == 0 then isFilterMultiples(list[1..], v, filtered)
        else    |list| > 0 && 
                |filtered| > 0 && 
                list[0] == filtered[0] && 
                isFilterMultiples(list[1..], v, filtered[1..])
    }

    lemma filteredMultiplesIsNotMultiple(list: seq<nat>, v: nat, filtered: seq<nat>)
        requires v > 0;
        requires isFilterMultiples(list, v,filtered);
        ensures isNotMultiple(filtered, v);
    {
        assert |list| >= |filtered|;
        if |list| == 0 {
            assert filtered == [];
            assert isNotMultiple(filtered, v);
        } else if |list| == 1 {
            var h := list[0];
            if ModDiv.mod(h, v) == 0 {
                assert filtered == [];
                assert isNotMultiple(filtered, v);
            } else {
                assert isNotMultiple(filtered, v);
            }
        } else {
            // dafny already get it
        }
    }

    lemma listContainsFiltered(list: seq<nat>, v: nat, filtered: seq<nat>)
        requires v > 0;
        requires isFilterMultiples(list, v,filtered);
        ensures forall v :: 0 <= v < |filtered| ==> filtered[v] in list;
    {
        // thanks Dafny
    }

    // method filterMultiples(list: seq<nat>, value: nat ) returns (filtered: seq<nat>)
    //     ensures |list| >= |filtered|;
    //     ensures isFilterMultiples(list, value, filtered);
    //     requires value > 0;
    // {
    //     var arr: seq<nat> := [];
    //     assert |arr| == 0;
    //     var k := 0;
    //     var yes := 0;
    //     var no  := 0;
    //     while (k < |list|)
    //         decreases |list| - k;
    //         invariant yes + no == k;
    //         invariant |arr| == yes;
    //         invariant 0 <= k <= |list|;
    //         invariant forall v: nat :: 0 <= v < |arr| ==> ModDiv.mod(arr[v], value) == 0;
    //     {
    //         if ( k < |list| ) {
    //             if ( ModDiv.mod(list[k], value) == 0 ) {
    //                 arr := arr + [list[k]];
    //                 yes := yes + 1;
    //             } else {
    //                 no := no + 1;
    //             }
    //         }
    //         assert forall v: nat :: 0 <= v < |arr| ==> ModDiv.mod(arr[v], value) == 0;
    //         k := k + 1;
    //         assert yes + no == k;
    //     }
    //     filtered := arr[..];
    //     assert forall v:nat :: 0 <= v < |filtered| ==> ModDiv.mod(filtered[v],value) == 0;
    // }

    lemma filteredStillNotMultiple(list: seq<nat>, v1: nat, v2: nat, filtered: seq<nat>)
        requires v1 > 0;
        requires v2 > 0;
        requires isNotMultiple(list, v1);
        requires isFilterMultiples(list, v2, filtered);
        ensures  isNotMultiple(filtered, v1);
    {
        // thanks
    }

    lemma shiftedStillNonMultiple(list: seq<nat>, integralList: seq<nat>, value: nat, initial: nat, shiftedIntegral: seq<nat>)
        requires value > 0;
        requires |list| > 0;
        requires |integralList| == |list|;
        requires isIntegral(list, initial, integralList);
        requires isNotMultiple(integralList, value);
        requires ModDiv.mod(List.sum(list), value) == 0;
        requires |integralList| == |shiftedIntegral|;
        requires isIntegral(List.shift(list), initial + list[0], shiftedIntegral);
        ensures  isNotMultiple(shiftedIntegral, value);
    {
        assert integralList[0] == List.sum(list[0..1]) + initial;
        assert List.sum(list[0..1]) == list[0];
        assert integralList[0] == initial + list[0];

        var shifted := List.shift(list);
        List.shiftedProperties(list, shifted);
        
        assert forall v: nat :: 0 <= v < |integralList| ==> ModDiv.mod(integralList[v], value) != 0;

        assert |shifted| == |list|;
        if |shifted| > 1 {
            forall k | 1 <= k < |list| - 1
                ensures shiftedIntegral[k] == List.sum(list[..k+2]) + initial;
                ensures shiftedIntegral[k] == integralList[k+1];
                ensures ModDiv.mod(integralList[k+1], value) != 0;           
                ensures ModDiv.mod(shiftedIntegral[k], value) != 0;           
            {
                assert k < |list|;
                assert k < |shifted|;
                assert shifted[..k+1] == shifted[..k] + [shifted[k]];
                assert List.sum(shifted[..k+1]) == List.sum(shifted[..k] + [shifted[k]]);
                List.sumListPlusValue(shifted[..k], shifted[k]);
                assert List.sum(shifted[..k+1]) == List.sum(shifted[..k]) + shifted[k];
                List.sumListPlusValue(shifted[1..k], shifted[0]);
                assert List.sum(shifted[..k+1]) == shifted[0] + List.sum(shifted[1..k]) + shifted[k];
                assert shiftedIntegral[k] == List.sum(shifted[..k+1]) + initial + list[0];
                assert shiftedIntegral[k] == List.sum(shifted[..k]) + shifted[k] + initial + list[0];
                assert shifted[k] == list[k+1];
                assert shifted[0] == list[1];
                assert list[1..k+1] == shifted[..k];
                assert shiftedIntegral[k] == List.sum(list[1..k+1]) + list[k+1] + initial + list[0];
                List.singleSum(list[k+1]);
                List.singleSum(list[0]);
                assert list[k+1] == List.sum([list[k+1]]);
                assert list[0] == List.sum([list[0]]);
                assert shiftedIntegral[k] == List.sum(list[1..k+1]) + list[k+1] + initial + list[0];
                assert shiftedIntegral[k] == list[0] + List.sum(list[1..k+1]) + list[k+1] + initial;
                assert shiftedIntegral[k] == List.sum([list[0]]) + List.sum(list[1..k+1]) + list[k+1] + initial;
                List.sumListPlusValue(list[1..k+1],list[0]);
                assert shiftedIntegral[k] == List.sum(list[..k+1]) + list[k+1] + initial;
                assert shiftedIntegral[k] == List.sum(list[..k+1]) + List.sum([list[k+1]]) + initial;
                List.sumListPlusValue(list[..k+1],list[k+1]);
                assert shiftedIntegral[k] == List.sum(list[..k+1]+[list[k+1]]) + initial;
                assert list[..k+1] + [list[k+1]] == list[..k+2];
                assert shiftedIntegral[k] == List.sum(list[..k+2]) + initial;
                assert shiftedIntegral[k] == integralList[k+1];
            }
        }

        assert shifted == list[1..] + [list[0]];
        assert List.sum(shifted) == List.sum(list[1..]+[list[0]]);
        List.sumListPlusValue(list[1..],list[0]);
        assert List.sum(shifted) == List.sum(list[1..])+List.sum([list[0]]);
        assert List.sum(shifted) == List.sum([list[0]])+List.sum(list[1..]);
        assert List.sum(shifted) == List.sum([list[0]]+list[1..]);
        assert List.sum(shifted) == List.sum(list);

        if ( |shifted| > 1 ) {
            assert shifted[0] == list[1];
            assert shiftedIntegral[0] == List.sum(shifted[..1]) + initial + list[0];
            assert shifted[..1] == [shifted[0]];
            List.singleSum(shifted[0]);
            assert List.sum(shifted[..1]) == shifted[0];
            assert shiftedIntegral[0] == shifted[0] + initial + list[0];
            assert shiftedIntegral[0] == list[1] + initial + list[0];
            assert shiftedIntegral[0] == list[0] + list[1] + initial;
            List.sumListPlusValue([list[0]],list[1]);
            List.singleSum(list[0]);
            assert shiftedIntegral[0] == List.sum([list[0]]) + list[1] + initial;
            assert shiftedIntegral[0] == List.sum([list[0]] + [list[1]]) + initial;
            assert [list[0]] + [list[1]] == list[..2];
            assert shiftedIntegral[0] == List.sum(list[..2]) + initial;
            assert integralList[1] == List.sum(list[..2]) + initial;
            assert integralList[1] == shiftedIntegral[0];
            assert ModDiv.mod(integralList[1], value) != 0;
            assert ModDiv.mod(shiftedIntegral[0], value) != 0;
        } 
        if ( |shifted| == 1 ) {
            assert shifted == list;
            assert List.sum(shifted) == List.sum(list);
            assert list == [list[0]];
            List.singleSum(list[0]);
            assert List.sum([list[0]]) == list[0];
            assert List.sum(list) == list[0];
            assert ModDiv.mod(List.sum(list), value) == 0;
            assert ModDiv.mod(list[0], value) == 0;
            assert shiftedIntegral[0] == List.sum(shifted[..1]) + initial + list[0];
            assert integralList[0] == List.sum(list[..1]) + initial;
            assert integralList[0] == List.sum(list) + initial;
            assert integralList[0] == list[0] + initial;
            assert shiftedIntegral[0] == List.sum(list[..1]) + initial + list[0];
            assert shiftedIntegral[0] == List.sum([list[0]]) + initial + list[0];
            assert shiftedIntegral[0] == list[0] + initial + list[0];
            var a := list[0];
            var b := initial + list[0];
            assert b == list[0] + initial;
            assert integralList[0] == b;
            assert ModDiv.mod(integralList[0], value) == 0;
            assert ModDiv.mod(b, value) == 0;
            ModDiv.modAplusB(value, a, b);
            assert ModDiv.mod(a + b, value) == ModDiv.mod(
                ModDiv.mod(a, value) +
                ModDiv.mod(b, value)
                ,
                value
            );
            assert ModDiv.mod(integralList[0], value) == ModDiv.mod(a, value);
            assert ModDiv.mod(integralList[0], value) != 0;
            assert ModDiv.mod(a + b, value) == ModDiv.mod(
                ModDiv.mod(initial + list[0], value)
                ,
                value
            );
            ModDiv.modMod(initial + list[0], value);
            assert ModDiv.mod(list[0] + initial + list[0], value) != 0;
            assert ModDiv.mod(shiftedIntegral[0], value) != 0;
            assert isNotMultiple(shiftedIntegral, value);
        }

        // last is not multiple
        var last := |list| - 1;
        assert |list| == |shifted|;
        assert shiftedIntegral[last] == List.sum(shifted[..last+1]) + initial + list[0];
        assert shiftedIntegral[last] == List.sum(shifted[..|list|]) + initial + list[0];
        assert shiftedIntegral[last] == List.sum(shifted[..|shifted|]) + initial + list[0];
        assert shifted[..|shifted|] == shifted;
        assert shiftedIntegral[last] == List.sum(shifted) + initial + list[0];
        assert shiftedIntegral[last] == List.sum(list) + initial + list[0];
        assert ModDiv.mod(integralList[0], value) != 0;
        assert integralList[0] == List.sum(list[..1]) + initial;
        assert integralList[0] == List.sum([list[0]]) + initial;
        List.singleSum(list[0]);
        assert integralList[0] == list[0] + initial;
        assert ModDiv.mod(list[0] + initial, value) != 0;
        var sumShifted := List.sum(shifted);
        var firstIntegral := list[0] + initial;
        ModDiv.modAplusB(value, firstIntegral, sumShifted);
        assert ModDiv.mod(firstIntegral + sumShifted, value) == ModDiv.mod(
            ModDiv.mod(firstIntegral, value) +
            ModDiv.mod(sumShifted, value)
            ,
            value
        );
        assert ModDiv.mod(sumShifted, value) == 0;
        assert ModDiv.mod(firstIntegral + sumShifted, value) == ModDiv.mod(
            ModDiv.mod(firstIntegral, value)
            ,
            value
        );
        ModDiv.modMod(firstIntegral, value);
        assert ModDiv.mod(firstIntegral + sumShifted, value) == ModDiv.mod(firstIntegral, value);

        assert shiftedIntegral[last] == List.sum(list) + initial + list[0];
        assert shiftedIntegral[last] == sumShifted + firstIntegral;
        assert ModDiv.mod(sumShifted + firstIntegral, value) == ModDiv.mod(firstIntegral, value);
        assert ModDiv.mod(shiftedIntegral[last], value) == ModDiv.mod(firstIntegral, value);
        assert ModDiv.mod(shiftedIntegral[last], value) != 0;
        assert isNotMultiple(shiftedIntegral, value);
    }

    // function method filterMultiples(list: seq<nat>, v: nat): seq<nat>
    //     requires v > 0;
    //     ensures filterMultiples([], v) == [];
    //     decreases |list|;
    //     ensures isFilterMultiples(list, v, filterMultiples(list, v))
    // {
    //     if |list| == 0 then []
    //     else if ( ModDiv.mod(list[0], v) != 0 ) then filterMultiples(list[1..], v)
    //     else [list[0]] + filterMultiples(list[1..], v)
    // }

    method filterMultiples(list: seq<nat>, v: nat) returns (filtered: seq<nat>)
        requires v > 0;
        decreases |list|;
        ensures |filtered| <= |list|;
        ensures isFilterMultiples(list, v, filtered);
    {        
        if ( |list| == 0 )
        { 
            filtered := [];
        }
        else
        {
            var previous := filterMultiples(list[1..], v);
            if ( ModDiv.mod(list[0], v) == 0 )
            {
                filtered := previous;
            }
            else
            {
                filtered := [list[0]] + previous;
            }
        }
 
   }

    function method stepsAvoidMultiple(steps: seq<nat>, v: nat): seq<nat>
    requires v > 0;
    {
        stepsAvoidMultipleLoop(steps, v, 0, 0)
    }

    function method stepsAvoidMultipleLoop(steps: seq<nat>, v: nat, current: nat, acc: nat): seq<nat>
        requires v > 0;
        decreases |steps|;
        ensures List.sum(steps) + current == List.sum(stepsAvoidMultipleLoop(steps,v,current,acc));
    {
        var result := if ( |steps| == 0 && current == 0 ) then []
        else if |steps| == 0 then [current]
        else if ( ModDiv.mod(steps[0] + acc + current, v) == 0 ) 
        then stepsAvoidMultipleLoop(steps[1..], v, steps[0] + current, acc)
        else [steps[0] + current] + 
        stepsAvoidMultipleLoop(steps[1..], v, 0, steps[0] + current + acc);

        result
    }

    /**
     * se temos uma lista de passos que nao nunca multipla de um valor
     * se multiplicamos ciclicamente essa lista por outro valor
     *
     */
    lemma makingAListNotMultipleOfNextValue(
        list: seq<nat>, 
        initial: nat,  // 5
        initialV2: nat, // 7
        integralList: seq<nat>, 
        cycleList: seq<nat>,
        modIntegralList: seq<nat>, 
        integralCycle: seq<nat>,
        modIntegralCycle: seq<nat>,
        filteredIntegralCycle: seq<nat>,
        v1: nat,
        v2: nat,
        listV2A: seq<nat>,
        listV2B: seq<nat>
    )
    // v1 and v2 are diff and bigger than zero
    requires v1 > 0; // 3
    requires v2 > 0; // 5
    requires v1 != v2;
    requires ModDiv.mod(initial, v1) != 0;
    requires ModDiv.mod(initial, v2) != 0;
    requires ModDiv.mod(v2, v1) != 0;
    requires ModDiv.mod(v1, v2) != 0;

    // list is non zero, non empty and the List.sum of the list is multiple of m
    requires |list| > 0; // 2
    requires List.nonZero(list); // [2,4]
    requires ModDiv.mod(List.sum(list), v1) == 0; // 2 + 4 == 6; mod(6,3) == 0

    // integral list def
    requires |integralList| == |list|; // [7,11] // [2,4]
    requires isIntegral(list, initial, integralList); // [7 == 5 + 2, 11 == 5 + 2 + 4]
    
    // mod of integral list def
    requires |modIntegralList| == |integralList|; // [7, 11] // [7 % 3, 11 % 3 ] == [1, 2]
    requires isListModList(integralList, v1, modIntegralList);

    requires isNotMultiple(integralList, v1);
    requires List.nonZero(modIntegralList);

    // cylce list def
    requires |cycleList| == |list| * v2 + 1; // [4,2,4,2,4,2,4,2,4,2,4,2]
    requires |cycleList| >= |list|;
    requires Cycle.isCycle(list, cycleList)

    // integral cycle def
    requires |integralCycle| == |cycleList|; // [7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37 ]
    requires isIntegral(cycleList, initial, integralCycle); // [5+2,5+2+4,5+2+4+2,5+2+4+2+4 ... ]
    
    // mod of integral cycle def
    requires |integralCycle| == |modIntegralCycle|; // [7 % 3, 11 %3, 13 % 3, 17 % 3 ...]
    requires isListModList(integralCycle, v1, modIntegralCycle); // [1, 2, 1, 2 ... ]

    // mod of integral should be cycle
    ensures Cycle.isCycle(modIntegralList, modIntegralCycle); // [1,2,1,2] == cycle([1,2],|list| * m + 1 )
    requires List.nonZero(modIntegralList);
    ensures isNotMultiple(integralCycle, v1);

    requires isFilterMultiples(integralCycle, v2, filteredIntegralCycle); // [7, 11, 13, 17, 19, 23, 29, 31, 37 ] - [25, 35]
    ensures isNotMultiple(filteredIntegralCycle, v1);
    ensures isNotMultiple(filteredIntegralCycle, v2);
    {
         modOfIntegralIsCycleFull(
            list, 
            initial, 
            integralList, 
            modIntegralList, 
            v1,
            cycleList, 
            integralCycle,
            modIntegralCycle
        );
        
        assert isNotMultiple(integralCycle, v1);
        listContainsFiltered(integralCycle, v2, filteredIntegralCycle);
        assert isNotMultiple(filteredIntegralCycle, v1);

        filteredMultiplesIsNotMultiple(integralCycle, v2, filteredIntegralCycle);
        
        assert forall v: nat :: 0 <= v < |cycleList| ==> integralCycle[v] == List.sum(cycleList[0..v+1]) + initial;
        assert integralCycle[|integralCycle|-1] == List.sum(cycleList[..|cycleList|]) + initial;
        assert cycleList[..|cycleList|] == cycleList;
        assert integralCycle[|integralCycle|-1] == List.sum(cycleList) + initial;
        // assert forall k :: 0 <= k < |integralCycle| ==> exists v :: integralCycle[k] == filteredIntegralCycle[v];  
   }

    // lemma bigProoff(
    //     initial: nat,  // 5
    //     prev: seq<nat>, // [ 2 3 ]
    //     list: seq<nat>, // [ 2 4 ]
    //     integralList: seq<nat>, // [ 7 11 ]
    //     modList: seq<nat>, // [2, 1]
    //     modIntegralList: seq<nat>, // [1, 2]
    //     m: nat, // 3
    //     cycleList: seq<nat>, // [ 2 4 2 4 2 4 ]
    //     integralCycle: seq<nat>, // [ 7 11 13 17 19 23 ]
    //     modIntegralCycle: seq<nat> // [ 1 2 1 2 1 2 ]
    // )
    //     requires m > 0;
    //     requires |list| > 0;
    //     requires nonZero(list);
    //     requires |cycleList| == |list| * m;
    //     requires |list| == |integralList|;

    //     requires |modList| == |list|;
    //     requires isModList(list, m, modList);
    //     requires nonZero(modList);

    //     requires isIntegral(list, initial, integralList);
    //     requires isCycle(list, cycleList);
    //     requires |integralCycle| == |cycleList|;
    //     requires isIntegral(cycleList, initial, integralCycle);

    //     // // if the list integral is not multiple of m
    //     requires isNotMultiple(integralList, m);
    //     requires |modIntegralList| == |integralList|;
    //     requires isModList(integralList, m, modIntegralList);
    //     requires nonZero(modIntegralList);

    //     requires |modIntegralCycle| == |integralCycle|;
    //     requires isModList(integralCycle, m, modIntegralCycle);

    //     requires ModDiv.mod(sum(list), m) == 0; // [2 4] ==> 2 + 4 == 6 ==> 6 % 3 == 0;
        
    //     // the next integral should also be not multiple of m
    //     ensures isNotMultiple(integralCycle, m);
    //     ensures nonZero(modIntegralCycle);
    // {
    // }

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

   method Main() {
       var l := [2,4,2,4,2,4,2,4,2,4];
       var i := stepsAvoidMultipleLoop(List.shift(l),5,0,7);
       print(i);
   }
}