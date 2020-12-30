include "modDiv.dfy"
include "list.dfy"
include "cycleFromMod.dfy"

module Integral {

    import ModDiv

    function sorted(list: seq<nat>): bool {
        forall k : nat :: 1 <= k < |list| ==> list[k] > list[k-1]
    }

    function nonZero(list: seq<nat>): bool
    {
        forall l: nat :: 0 <= l < |list| ==> list[l] > 0
    }

    function unique(list: seq<nat>): bool {
        forall n,m : nat :: 0 <= n < m < |list| ==> list[n] != list[m]
    }

    function first(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[0]
    }

    function last(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[|list|-1]
    }

    function method sum(list: seq<nat>): nat
        decreases |list|;
    {
        if (|list| == 0 ) then 0 else
        list[0] + sum(list[1..])
    }


    ghost method distributiveSum(a: seq<nat>, b: seq<nat> )
        ensures sum(a + b) == sum(a) + sum(b); 
    {
        assert |a| == 0 && |b| == 0 ==> sum(a) + sum(b) == 0 == sum(a + b);
        assert |a|  > 0 && |b| == 0 ==> a + b == a;    
        assert |a|  > 0 && |b| == 0 ==> sum(a) + sum(b) == sum(a) + 0 == sum(a) == sum(a + b);
        assert |a| == 0 && |b|  > 0 ==> a + b == b;
        assert |a| == 0 && |b|  > 0 ==> sum(a) + sum(b) == sum(b) + 0 == sum(b) == sum( a + b);
        assert |a|  > 0 && |b|  > 0 ==> sum(a) + sum(b) == a[0] + sum(a[1..]) + b[0] + sum(b[1..]) == a[0] + b[0] + sum(a[1..]) + sum(b[1..]);
        assert |a|  > 0 && |b|  > 0 ==> a + b == [a[0]] + (a[1..] + b);
        assert |a|  > 0 && |b|  > 0 ==> sum(a + b) == sum([a[0]]) + sum(a[1..] + b);
    }

    lemma divSum(list: seq<nat>, n: nat)
        requires 0 <= n < |list|;
        ensures sum(list) == sum(list[0..n]) + sum(list[n..]); 
    {
        assert list[0..n] + list[n..] == list;
        var a := list[0..n];
        var b := list[n..];
        distributiveSum(a,b);
    }

    lemma sumListPlusValue(list: seq<nat>, value: nat)
        ensures sum(list) + value == sum([value] + list);
        ensures sum(list) + value == sum(list + [value]);
        ensures value + sum(list) == sum(list) + value;
    {
        assert sum(list) + value == sum([value] + list);
        var a := list;
        var b := [value];
        distributiveSum(a, b);
    }

    lemma cycleListIsListPlusSmallCycleList(list: seq<nat>, cycleList: seq<nat>, smallCycle: seq<nat>, m: nat)
        requires |list| > 0;
        requires |cycleList| >= |list|;
        requires m > 0;
        requires isCycle(list, cycleList);
        requires |cycleList| == |list| * m;
        requires  smallCycle == cycleList[|list|..];
        ensures cycleList == list + smallCycle;
        ensures sum(cycleList) == sum(list) + sum(smallCycle);
        ensures |smallCycle| > 0 ==> isCycle(list, smallCycle);
        ensures |smallCycle| == |list| * (m - 1);
    {
        distributiveSum(list,smallCycle);
        assert |cycleList| == |list| * m;
        assert forall v : nat :: 0 <= v < |list| ==> cycleList[v] == list[v];
        assert |cycleList| >= |list|;
        assert cycleList == list + smallCycle;
        assert |smallCycle| > 0 ==> isCycle(list,smallCycle);
        assert |smallCycle| == |list| * (m - 1);
    }

    function isIntegral(list: seq<nat>, initial: nat, listIntegral: seq<nat>): bool
        requires |list| == |listIntegral|;
    {
        forall v: nat :: 0 <= v < |list| ==> listIntegral[v] == sum(list[0..v+1]) + initial
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
            invariant forall v: nat :: 0 <= v < k ==> arr[v] == sum(list[..v+1]) + initial;
        {
            /* 
             * Could not make it work using acc, what would be fast.
             * This is not the fast strategy, but for sure is correct
             */
            arr[k] := sum(list[..k+1]) + initial;
            k := k + 1;
        }
        // array to seq
        result := arr[..];
    }

    function isModList(list: seq<nat>, value: nat, modList: seq<nat>): bool
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
        cycleList: seq<nat>, 
        integralCycle: seq<nat>,
        modIntegralCycle: seq<nat>
    )

    // m is bigger than zero
    requires m > 0;

    // list is non zero, non empty and the sum of the list is multiple of m
    requires |list| > 0;
    requires nonZero(list);
    requires ModDiv.mod(sum(list),m) == 0;


    // integral list def
    requires |integralList| == |list|;
    requires isIntegral(list, initial, integralList);
    
    // mod of integral list def
    requires |modIntegralList| == |integralList|;
    requires isModList(integralList, m, modIntegralList);

    // cylce list def
    requires |cycleList| == |list| * m;
    requires |cycleList| >= |list|;
    requires isCycle(list, cycleList)

    // integral cycle def
    requires |integralCycle| == |cycleList|;
    requires isIntegral(cycleList, initial, integralCycle);
    
    // mod of integral cycle def
    requires |modIntegralCycle| == |integralCycle|;
    requires isModList(integralCycle, m, modIntegralCycle);

    // mod of integral should be cycle
//    ensures isCycle(modIntegralList, modIntegralCycle);
    {
        if ( m == 1 ) {
            assert cycleList == list;
            assert integralCycle == integralList;
            assert modIntegralCycle == modIntegralList;
        } else {
            assert cycleList[0..|list|] == list;

            assert forall v: nat :: 0 <= v < |integralList| ==> integralList[v] == sum(list[..v+1]) + initial;
            var last := |list| - 1;
            assert integralList[last] == sum(list[..(last+1)]) + initial;
            assert list[..(last+1)] == list;
            assert sum(list[..(last+1)]) == sum(list);
            assert integralList[last] == sum(list) + initial;
            assert ModDiv.mod(sum(list),m) == 0;
            
        }
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
        assert singleIntegral[0] == sum(single[..1]) + initial;

        var listIntegral := integral(list, initial);
        assert forall n: nat ::  0 < n < |list| ==> listIntegral[n] == sum(list[..n+1]) + initial;
        assert |listIntegral| == |list|;
    }

    method Main() {
    }
}