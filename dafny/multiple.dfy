include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"
include "integral.dfy"
include "derivative.dfy"

module Multiple {

    import ModDiv
    import Cycle
    import List
    import Integral
    import Derivative
    function isNotMultiple(list: seq<nat>, value: nat): bool
        requires value > 0;
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

    lemma isFilterSingleSolution(list: seq<nat>, a: seq<nat>, b:seq<nat>, v: nat)
        requires v > 0;
        requires isFilterMultiples(list, v, a);
        requires isFilterMultiples(list, v, b);
        ensures a == b;
    {
        if ( |list| == 0 ) {
            assert a == [];
            assert b == [];
            assert a == b;
        } else {
            if ( ModDiv.mod(list[0],v) == 0 ) {
                assert isFilterMultiples(list[1..], v, a);
                assert isFilterMultiples(list[1..], v, b);
                isFilterSingleSolution(list[1..],a,b,v);
                assert a == b;
            } else {
                var top := list[0];
                assert a[0] == top;
                assert b[0] == top;           
                assert isFilterMultiples(list[1..], v, a[1..]);
                assert isFilterMultiples(list[1..], v, b[1..]);
                isFilterSingleSolution(list[1..],a[1..],b[1..],v);
                assert a[1..] == b[1..];
                assert [top] + a[1..] == [top] + b[1..];
                assert a == b;
            }
        }
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

    lemma keepFilteredFromList(list: seq<nat>, v: nat, filtered: seq<nat>)
        requires v > 0;
        requires isFilterMultiples(list, v,filtered);
        ensures forall k :: 0 <= k < |list| ==> ( ModDiv.mod(list[k],v) != 0 ==> list[k] in filtered );
        ensures forall k :: 0 <= k < |list| ==> ( ModDiv.mod(list[k],v) == 0 ==> list[k] !in filtered );
        ensures forall k :: 0 <= k < |filtered| ==> filtered[k] in list;
        ensures List.sorted(list) ==> List.sorted(filtered);
        // ensures |filtered| >= |list|;
        ensures List.sorted(list) ==> |filtered| > 0 ==> filtered[0] >= list[0];
        ensures List.sorted(list) ==> |filtered| > 0 ==> List.last(filtered) <= List.last(list);
    {
        if ( list == [] ) {
            assert filtered == [];
        } else if ( |list| > 0 ) {
            var head := list[0];
            if (List.sorted(list)) {
                List.propertySorted(list);
                assert head == list[0];
                assert forall k :: 0 < k < |list| ==> head < list[k];
            }
            if ( ModDiv.mod(head, v) == 0 ) {
                assert isFilterMultiples(list[1..], v, filtered);
                assert head !in filtered;
            } else {
                assert head in filtered;
                assert filtered[0] == head;
            }
        }
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
        ensures shiftedIntegral[|list|-1] == List.sum(list) + initial + list[0];
        ensures List.sum(List.shift(list)) == List.sum(list);
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
            // assert a + b == c;
            // assert ModDiv.mod(a + b, value) == ModDiv.mod(c, value);
            assert ModDiv.mod(a + b, value) != 0;
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

    lemma shiftedSumEquals(list: seq<nat>, shifted: seq<nat> )
      requires shifted == List.shift(list);
      ensures List.sum(shifted) == List.sum(list);
    {
        if ( |list| == 0 ) {
            assert shifted == [];
            assert List.sum(list) == 0;
            assert List.sum(shifted) == 0;
            assert List.sum(shifted) == List.sum(list);
        } else {
            assert list[1..] + [list[0]] == shifted;
            assert List.sum(shifted) == List.sum(list[1..] + [list[0]]);
            List.distributiveSum(list[1..],[list[0]]);
            assert List.sum(shifted) == List.sum(list[1..]) + List.sum([list[0]]);
            assert List.sum(shifted) == List.sum([list[0]]) + List.sum(list[1..]);
            assert List.sum(shifted) == List.sum(list);
        }
    }

    lemma distributiveFilter(listA: seq<nat>, listB: seq<nat>, filterA: seq<nat>, filterB: seq<nat>, filterAB: seq<nat>, value: nat)
        requires value > 0;
        requires isFilterMultiples(listA, value, filterA);
        requires isFilterMultiples(listB, value, filterB);
        requires isFilterMultiples(listA + listB, value, filterAB);
        ensures filterA + filterB == filterAB;
    {
        var listAB := listA + listB;
        if ( |listA| == 0 && |listB| == 0 ) {
            assert listA == [];
            assert listB == [];
            assert listA + listB == [];
            assert filterA == [];
            assert filterB == [];
            assert filterA + filterB == [];
            assert filterAB == [] == filterA + filterB;
        }
        if( |listA|  > 0 && |listB| == 0 ) {
            assert listA + listB == listA;
            assert listA == listAB;
            assert isFilterMultiples(listA, value, filterA);
            assert isFilterMultiples(listAB, value, filterAB);
            assert isFilterMultiples(listA + [], value, filterAB);
            assert isFilterMultiples(listA, value, filterAB);
            isFilterSingleSolution(listAB, filterAB, filterA, value);
            assert filterA == filterAB;
            assert [] + filterA == filterAB;
            assert filterA + filterB == filterAB;
        }    
        if (|listA|  == 0 && |listB| > 0) {
            assert listA + listB == listB;
            assert filterA == [];
            assert filterA + filterB == filterB;
            assert listAB == listB;
            assert isFilterMultiples(listB,  value, filterB);
            assert isFilterMultiples(listAB, value, filterAB);
            assert isFilterMultiples([] + listB, value, filterAB);
            assert isFilterMultiples(listB,  value, filterAB);
            isFilterSingleSolution(listB, filterAB, filterB, value);
            assert filterB == filterAB;
            assert [] + filterB == filterAB;
            assert filterA + filterB == filterAB;
        }
        if ( |listA| > 0 && |listB| > 0 ) {
            var topA := listA[0];
            assert listAB[0] == topA;
            if ( ModDiv.mod(topA,value) != 0 ) {

                assert filterA[0] == topA;
                assert filterAB[0] == topA;

                assert |listA| > 0;
                assert |listAB| > 0;
                assert |filterA| > 0;
                assert |filterAB| > 0;
                keepFilteredFromList(listA, value, filterA);
                keepFilteredFromList(listAB, value, filterAB);
                assert topA in filterA;
                assert topA in filterAB;
                assert isFilterMultiples(listA[1..], value, filterA[1..]);
                assert isFilterMultiples(listAB[1..], value, filterAB[1..]);
                assert listA[1..] + listB == listAB[1..];
                assert filterAB == [filterAB[0]] + filterAB[1..];
                distributiveFilter(listA[1..], listB, filterA[1..], filterB, filterAB[1..], value);
                assert filterA[1..] + filterB == filterAB[1..];
                assert [topA] + filterA[1..] == filterA;
                assert [topA] + filterAB[1..] == filterAB;
                assert [topA] + filterA[1..] + filterB == [topA] + filterAB[1..];
                assert filterA + filterB == filterAB;
            } else {                
                keepFilteredFromList(listA, value, filterA);
                keepFilteredFromList(listAB, value, filterAB);
                assert topA !in filterA;
                assert topA !in filterAB;
                assert isFilterMultiples(listA[1..], value, filterA);
                assert isFilterMultiples(listAB[1..], value, filterAB);
                assert listAB[1..] == listA[1..] + listB;
                distributiveFilter(listA[1..], listB, filterA, filterB, filterAB, value);
                assert filterA + filterB == filterAB;
            }
        }
    }

    lemma relatedFilteredAndCount(list: seq<nat>, value: nat, filtered: seq<nat>)
        requires value > 0;
        requires isFilterMultiples(list, value, filtered);
        // ensures List.countWithValue(list, value) == List.countWithValue(list,0) + |filtered|;
    {
        keepFilteredFromList(list, value,filtered);
        assert forall k :: 0 <= k < |list| ==> ( ModDiv.mod(list[k],value) == 0 ==> list[k] !in filtered );
        assert forall k :: 0 <= k < |list| ==> ( ModDiv.mod(list[k],value) != 0 ==> list[k]  in filtered );
        var countModZero := 0;
        var countModNonZero := 0;
        var partialFiltered := [];
        var partialFilteredOut := [];
        var k := 0;

        assert isFilterMultiples(list[..k], value, partialFiltered);

        while ( k < |list| )
            decreases |list| - k;
            invariant k == countModNonZero + countModZero;
            invariant |partialFiltered| == countModNonZero;
            invariant |partialFilteredOut| == countModZero;
            invariant isNotMultiple(partialFiltered, value);
            invariant k <= |list|;
            invariant forall c :: 0 <= c < |partialFilteredOut| ==> ModDiv.mod(partialFilteredOut[c],value) == 0;
            invariant forall c :: 0 <= c < |partialFiltered|    ==> ModDiv.mod(partialFiltered[c],value)    != 0;
            invariant forall c :: 0 <= c < k ==> ( ModDiv.mod(list[c],value) != 0 ==> list[c]  in partialFiltered );
            invariant forall c :: 0 <= c < k ==> ( ModDiv.mod(list[c],value) == 0 ==> list[c] !in partialFiltered );
            invariant forall c :: 0 <= c < k ==> ( ModDiv.mod(list[c],value) != 0 ==> list[c] !in partialFilteredOut );
            invariant forall c :: 0 <= c < k ==> ( ModDiv.mod(list[c],value) == 0 ==> list[c]  in partialFilteredOut );
            invariant forall c :: 0 <= c < |partialFilteredOut| ==> partialFilteredOut[c]  in list;
            invariant forall c :: 0 <= c < |partialFiltered|    ==> partialFiltered[c]     in list;
            // invariant List.countWithValue(list[..k],0) == countModZero; 
            // invariant isFilterMultiples(list[..k], value, partialFiltered);
        {
            if ( ModDiv.mod(list[k],value) == 0 ) {
                countModZero := countModZero + 1;
                assert list[k] !in filtered;
                partialFilteredOut := partialFilteredOut + [list[k]];
            } else {
                countModNonZero := countModNonZero + 1;
                assert list[k] in filtered;
                partialFiltered := partialFiltered + [list[k]];
            }
            k := k + 1;
            assert k == countModNonZero + countModZero;
        }
        assert k == |list|;
        assert forall c :: 0 <= c < k ==> ( ModDiv.mod(list[c],value) != 0 ==> list[c]  in partialFiltered );
        assert forall c :: 0 <= c < k ==> ( ModDiv.mod(list[c],value) == 0 ==> list[c] !in partialFiltered );
        assert forall c :: 0 <= c < |partialFiltered|    ==> partialFiltered[c]     in list;
        assert |partialFiltered| == countModNonZero;
        assert |partialFilteredOut| == countModZero;
        assert isFilterMultiples(list, value, filtered);
        // assert |filtered| == countModNonZero;
        // assert |filtered| + countModZero == |list|;
    }
}