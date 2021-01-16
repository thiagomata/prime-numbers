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

    function isListModList(list: seq<nat>, value: nat, modList: seq<nat>): bool
        requires |list| == |modList|;
        requires |list| > 0;
        requires value > 0;
    {
        forall v: nat :: 0 <= v < |list| ==> modList[v] == ModDiv.mod(list[v], value)
    }

    function isNotMultiple(list: seq<nat>, value: nat): bool
        requires value > 0;
        requires |list| > 0;
    {
        forall v: nat :: 0 <= v < |list| ==> ModDiv.mod(list[v], value) != 0
    }

    lemma modOfIntegral(
        list: seq<nat>, 
        initial: nat, 
        integralList: seq<nat>, 
        modIntegralList: seq<nat>, 
        m: nat,
        v: nat, 
        cycleList: seq<nat>, 
        integralCycle: seq<nat>,
        modIntegralCycle: seq<nat>
    )

    // m is bigger than zero
    requires m > 0; // 2
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
    requires |cycleList| == |list| * m; // [2,4,2,4]
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
            
            assert modIntegralList[k]  == ModDiv.mod(integralList[k], v);
            assert modIntegralCycle[k] == ModDiv.mod(integralCycle[k], v);
            assert modIntegralCycle[k] == ModDiv.mod(integralList[k], v);
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

        Cycle.cycleAlwaysRepeatTheSameValues(modIntegralList, modIntegralCycle, m);
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

//    method Main() {
//        var l := [1,2,3];
//        var i := List.sum(l[..3]);
//        print(i);
//    }
}