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

    /**
     * Considering that we can create a sorted list that is never multiple of some primes
     * from an initial value and some steps that should be added in cycle sequence.
     * Let's call nextPrime is the first element of that list.
     * We are able to create a new list that is never multiple from all previous primes
     * and also is not multiple of next prime.
     */
    lemma makingAListNotMultipleOfNextValue(
        steps: seq<nat>,
        cycleSteps: seq<nat>,
        initial: nat, 
        nextInitial: nat,
        shifted: seq<nat>,
        primes: seq<nat>,
        nextPrime: nat,
        integral: seq<nat>, 
        shiftedIntegral: seq<nat>,
        filteredShiftedIntegral: seq<nat>,
        nextSteps: seq<nat>,
        integralNextSteps: seq<nat>
    )
    requires |steps| > 0;
    requires |primes| > 0;
    requires initial > 0;
    requires nextInitial == initial + steps[0];
    requires nextPrime == initial;
    requires List.nonZero(steps);
    requires List.nonZero(primes);
    requires Cycle.isCycle(steps, cycleSteps);
    requires |cycleSteps| == |steps| * nextPrime;
    requires |integral| == |cycleSteps|;
    requires Integral.isIntegral(cycleSteps, initial, integral);
    requires forall p :: 0 <= p < |primes| ==> isNotMultiple(integral, primes[p]);
    requires shifted == List.shift(cycleSteps);
    requires forall p :: 0 <= p < |primes| ==> ModDiv.mod(List.sum(steps), primes[p]) == 0;
    requires |integral| == |shiftedIntegral|;
    requires Integral.isIntegral(shifted, nextInitial, shiftedIntegral);
    requires isFilterMultiples(shiftedIntegral, nextPrime, filteredShiftedIntegral);
    requires |nextSteps| == |filteredShiftedIntegral|;
    requires Derivative.isDerivative(filteredShiftedIntegral, nextInitial, nextSteps);
    requires |integralNextSteps| == |nextSteps|;
    requires Integral.isIntegral(nextSteps, nextInitial, integralNextSteps);

    ensures forall p :: 0 <= p < |primes| ==> isNotMultiple(shiftedIntegral, primes[p]);
    ensures isNotMultiple(filteredShiftedIntegral, nextPrime);
    ensures forall p :: 0 <= p < |primes| ==> isNotMultiple(filteredShiftedIntegral, primes[p]);
    ensures forall p :: 0 <= p < |primes| ==> isNotMultiple(integralNextSteps, primes[p]);
    ensures isNotMultiple(integralNextSteps, nextPrime);
    ensures filteredShiftedIntegral == integralNextSteps;
    {
        shiftedSumEquals(cycleSteps, shifted);
        forall p | 0 <= p < |primes|
            ensures isNotMultiple(shiftedIntegral, primes[p])
            ensures isNotMultiple(filteredShiftedIntegral, primes[p])
        {
            assert ModDiv.mod(List.sum(steps), primes[p]) == 0;
            Cycle.sumMultipleList(steps, cycleSteps, nextPrime);
            assert List.sum(cycleSteps) == List.sum(steps) * nextPrime;
            shiftedStillNonMultiple(cycleSteps, integral, primes[p], initial, shiftedIntegral);
            assert isNotMultiple(shiftedIntegral, primes[p]);
            filteredStillNotMultiple(shiftedIntegral, primes[p], nextPrime, filteredShiftedIntegral);
            assert isNotMultiple(filteredShiftedIntegral, primes[p]);
        }
        filteredMultiplesIsNotMultiple(shiftedIntegral, nextPrime, filteredShiftedIntegral);
        assert isNotMultiple(filteredShiftedIntegral, nextPrime);

        assert Derivative.isDerivative(filteredShiftedIntegral, nextInitial, nextSteps);
        assert Integral.isIntegral(nextSteps, nextInitial, integralNextSteps);
        Derivative.integralOfDerivative(filteredShiftedIntegral, nextSteps, integralNextSteps, nextInitial);
        assert filteredShiftedIntegral == integralNextSteps;

        // assert ModDiv.mod(List.sum(nextSteps), v) == 0;

    }
}