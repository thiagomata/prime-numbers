include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"
include "integral.dfy"

module Multiple {

    import ModDiv
    import Cycle
    import List
    import Integral

    function isNotMultiple(list: seq<nat>, value: nat): bool
        requires value > 0;
        // requires |list| > 0;
    {
        forall v: nat :: 0 <= v < |list| ==> ModDiv.mod(list[v], value) != 0
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
        requires Integral.isIntegral(list, initial, integralList);
        requires isNotMultiple(integralList, value);
        requires ModDiv.mod(List.sum(list), value) == 0;
        requires |integralList| == |shiftedIntegral|;
        requires Integral.isIntegral(List.shift(list), initial + list[0], shiftedIntegral);
        ensures  isNotMultiple(shiftedIntegral, value);
    {
        assert integralList[0] == List.sum(list[0..1]) + initial;
        assert List.sum(list[0..1]) == list[0];
        assert integralList[0] == initial + list[0];

        var shifted := List.shift(list);
        List.shiftedProperties(list, shifted);
        
        assert forall v: nat :: 0 <= v < |integralList| ==> ModDiv.mod(integralList[v], value) != 0;

        assert |shifted| == |list|;
        
        if ( |shifted| == 0 ) {
            assert isNotMultiple(shiftedIntegral, value);
        } else if ( |shifted| == 1 ) {
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
            assert a == List.sum(list);
            assert ModDiv.mod(List.sum(list), value) == 0;
            assert ModDiv.mod(a, value) == 0;
            var b := initial + list[0];
            assert b == list[0] + initial;
            assert integralList[0] == b; 
            assert ModDiv.mod(integralList[0], value) != 0;
            assert ModDiv.mod(List.sum(list), value) == 0;
            assert ModDiv.mod(b, value) != 0;
            ModDiv.modAplusB(value, a, b);
            assert ModDiv.mod(a + b, value) == ModDiv.mod(
                ModDiv.mod(a, value) +
                ModDiv.mod(b, value)
                ,
                value
            );
            assert ModDiv.mod(integralList[0], value) == ModDiv.mod(b, value);
            assert ModDiv.mod(integralList[0], value) != 0;
            assert a + b == list[0] + initial + list[0];
            var c := a + b;
            assert c == list[0] + initial + list[0];
            assert c == shiftedIntegral[0];
            assert c == a + b;
            assert ModDiv.mod(a + b, value) == ModDiv.mod(
                ModDiv.mod(a, value)
                + 
                ModDiv.mod(b, value),
                value
            );
            assert ModDiv.mod(a + b, value) == ModDiv.mod(
                0
                +
                ModDiv.mod(b, value)
                ,
                value
            );            
            assert ModDiv.mod(a + b, value) == ModDiv.mod(
                ModDiv.mod(b, value)
                ,
                value
            );            
            ModDiv.modMod(b, value);
            assert ModDiv.mod( ModDiv.mod(b, value), value) == ModDiv.mod(b, value);
            assert ModDiv.mod(a + b, value) == ModDiv.mod(b, value);
            assert ModDiv.mod(b, value) != 0;
            assert a + b == c;
            assert ModDiv.mod(a + b, value) == ModDiv.mod(c, value);
            assert ModDiv.mod(c, value) != 0;
            assert ModDiv.mod(shiftedIntegral[0], value) != 0;
            assert isNotMultiple(shiftedIntegral, value);
        }
        if ( |shifted| > 1 ) {

            /**
             * First is fine
             */
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

            /**
             * For all elements except the first and the last
             */
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
                assert ModDiv.mod(integralList[k+1], value) != 0;
                assert ModDiv.mod(shiftedIntegral[k], value) != 0;
            }

            /*
             * Sum shifted equals sum list 
             */
            assert shifted == list[1..] + [list[0]];
            assert List.sum(shifted) == List.sum(list[1..]+[list[0]]);
            List.sumListPlusValue(list[1..],list[0]);
            assert List.sum(shifted) == List.sum(list[1..])+List.sum([list[0]]);
            assert List.sum(shifted) == List.sum([list[0]])+List.sum(list[1..]);
            assert List.sum(shifted) == List.sum([list[0]]+list[1..]);
            assert List.sum(shifted) == List.sum(list);

            /*
             * last is not multiple
             */
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
    }

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
    requires Integral.isIntegral(list, initial, integralList); // [7 == 5 + 2, 11 == 5 + 2 + 4]
    
    // mod of integral list def
    requires |modIntegralList| == |integralList|; // [7, 11] // [7 % 3, 11 % 3 ] == [1, 2]
    requires ModDiv.isModListFromList(integralList, v1, modIntegralList);

    requires isNotMultiple(integralList, v1);
    requires List.nonZero(modIntegralList);

    // cylce list def
    requires |cycleList| == |list| * v2 + 1; // [4,2,4,2,4,2,4,2,4,2,4,2]
    requires |cycleList| >= |list|;
    requires Cycle.isCycle(list, cycleList)

    // integral cycle def
    requires |integralCycle| == |cycleList|; // [7, 11, 13, 17, 19, 23, 25, 29, 31, 35, 37 ]
    requires Integral.isIntegral(cycleList, initial, integralCycle); // [5+2,5+2+4,5+2+4+2,5+2+4+2+4 ... ]
    
    // mod of integral cycle def
    requires |integralCycle| == |modIntegralCycle|; // [7 % 3, 11 %3, 13 % 3, 17 % 3 ...]
    requires ModDiv.isModListFromList(integralCycle, v1, modIntegralCycle); // [1, 2, 1, 2 ... ]

    // mod of integral should be cycle
    ensures Cycle.isCycle(modIntegralList, modIntegralCycle); // [1,2,1,2] == cycle([1,2],|list| * m + 1 )
    requires List.nonZero(modIntegralList);
    ensures isNotMultiple(integralCycle, v1);

    requires isFilterMultiples(integralCycle, v2, filteredIntegralCycle); // [7, 11, 13, 17, 19, 23, 29, 31, 37 ] - [25, 35]
    ensures isNotMultiple(filteredIntegralCycle, v1);
    ensures isNotMultiple(filteredIntegralCycle, v2);
    {
         Integral.modOfIntegralIsCycleFull(
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

    //     requires Integral.isIntegral(list, initial, integralList);
    //     requires isCycle(list, cycleList);
    //     requires |integralCycle| == |cycleList|;
    //     requires Integral.isIntegral(cycleList, initial, integralCycle);

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
   method Main() {
       var l := [2,4,2,4,2,4,2,4,2,4];
       var i := stepsAvoidMultipleLoop(List.shift(l),5,0,7);
       print(i);
   }    
}