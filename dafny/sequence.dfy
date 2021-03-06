include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"
include "integral.dfy"
include "derivative.dfy"
include "multiple.dfy"

module Sequence {

    import List
    import ModDiv
    import Cycle
    import Integral
    import Derivative
    import Multiple

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
        v: nat, 
        cycleList: seq<nat>, 
        integralCycle: seq<nat>,
        modIntegralCycle: seq<nat>
    )

    requires v > 0; // 3

    // list is non zero, non empty and the List.sum of the list is multiple of m
    requires |list| > 0; // 2
    requires List.nonZero(list); // [2,4]
    requires ModDiv.mod(List.sum(list), v) == 0; // 2 + 4 == 6; mod(6,3) == 0


    // integral list def
    requires |integralList| == |list|; // [7,11] // [2,4]
    requires Integral.isIntegral(list, initial, integralList); // [7 == 5 + 2, 11 == 5 + 2 + 4]
    
    // mod of integral list def
    requires |modIntegralList| == |integralList|; // [7, 11] // [7 % 3, 11 % 3 ] == [1, 2]
    requires ModDiv.isModListFromList(integralList, v, modIntegralList);

    // cylce list def
    // requires |cycleList| == |list| * m; // [2,4,2,4]
    requires |cycleList| >= |list|;
    requires Cycle.isCycle(list, cycleList)

    // integral cycle def
    requires |integralCycle| == |cycleList|; // [7, 11, 13, 17]
    requires Integral.isIntegral(cycleList, initial, integralCycle); // [5+2,5+2+4,5+2+4+2,5+2+4+2+4] ...
    
    // mod of integral cycle def
    requires |integralCycle| == |modIntegralCycle|; // [7 % 3, 11 %3, 13 % 3, 17 % 3]
    requires ModDiv.isModListFromList(integralCycle, v, modIntegralCycle); // [1, 2, 1, 2]

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

    lemma modOfIntegralIsCycle(
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
        var integralList := Integral.integral(list, initial);
        assert Integral.isIntegral(list, initial, integralList);

        var modIntegralList := ModDiv.modListFromList(integralList, v);

        var cycleList := Cycle.cycle(list, |list| * m);
        assert Cycle.isCycle(list, cycleList);
        
        var integralCycle := Integral.integral(cycleList, initial);

        var modIntegralCycle := ModDiv.modListFromList(integralCycle, v);

        modOfIntegralIsCycleFull(
            list, 
            initial, 
            integralList, 
            modIntegralList, 
            v, 
            cycleList, 
            integralCycle,
            modIntegralCycle
        );

        assert Cycle.isCycle(modIntegralList, modIntegralCycle); // [1,2,1,2] == cycle([1,2],m)
        assert List.nonZero(modIntegralList) ==> List.nonZero(modIntegralCycle);

    }

    /**
     * Considering that we can create a sorted list that is never multiple of some primes
     * from an initial value and some steps that should be added in cycle sequence.
     * Let's call nextPrime is the  first element of that list.
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
        integralNextSteps: seq<nat>,
        cycleMultipler: nat
    )
    requires |steps| > 0;
    requires |primes| > 0;
    requires initial > 0;
    requires cycleMultipler > 0;
    requires nextInitial == initial + steps[0];
    requires nextPrime == initial;
    requires ModDiv.mod(nextInitial, nextPrime ) != 0; // <================= hard to prove
    requires List.nonZero(steps);
    requires List.nonZero(primes);
    requires Cycle.isCycle(steps, cycleSteps);
    requires |cycleSteps| == |steps| * nextPrime;
    requires |integral| == |cycleSteps|;
    requires Integral.isIntegral(cycleSteps, initial, integral);
    requires shifted == List.shift(cycleSteps);
    requires forall p :: 0 <= p < |primes| ==> Multiple.isNotMultiple(integral, primes[p]);
    requires forall p :: 0 <= p < |primes| ==> ModDiv.mod(initial, primes[p]) == 0;
    requires forall p :: 0 <= p < |primes| ==> ModDiv.mod(List.sum(steps), primes[p]) == 0;
    requires |integral| == |shiftedIntegral|;
    requires Integral.isIntegral(shifted, nextInitial, shiftedIntegral);
    requires Multiple.isFilterMultiples(shiftedIntegral, nextPrime, filteredShiftedIntegral);
    requires |nextSteps| == |filteredShiftedIntegral|;
    requires Derivative.isDerivative(filteredShiftedIntegral, nextInitial, nextSteps);
    requires |integralNextSteps| == |nextSteps|;
    requires Integral.isIntegral(nextSteps, nextInitial, integralNextSteps);

    ensures forall p :: 0 <= p < |primes| ==> ModDiv.mod(nextInitial, primes[p]) != 0;
    ensures forall p :: 0 <= p < |primes| ==> Multiple.isNotMultiple(shiftedIntegral, primes[p]);
    ensures Multiple.isNotMultiple(filteredShiftedIntegral, nextPrime);
    ensures forall p :: 0 <= p < |primes| ==> Multiple.isNotMultiple(filteredShiftedIntegral, primes[p]);
    ensures forall p :: 0 <= p < |primes| ==> Multiple.isNotMultiple(integralNextSteps, primes[p]);
    ensures Multiple.isNotMultiple(integralNextSteps, nextPrime);
    ensures filteredShiftedIntegral == integralNextSteps;
    {
        Multiple.shiftedSumEquals(cycleSteps, shifted);

        /**
         * Proof that integral[0] == nextInitial;
         */
        assert nextInitial == initial + steps[0];
        assert integral[0] == initial + List.sum(cycleSteps[..1]);
        assert cycleSteps[..1] ==  [cycleSteps[0]];
        assert cycleSteps[0] == steps[0];
        assert List.sum(cycleSteps[..1]) == List.sum([cycleSteps[0]]);
        assert List.sum(cycleSteps[..1]) == List.sum([steps[0]]);
        assert List.sum([steps[0]]) == steps[0];
        assert integral[0] == initial + steps[0];
        assert integral[0] == nextInitial;

        /**
         * Proof that List.sum(cycleSteps) % nextPrime == 0
         */
        Cycle.cycleSameMod(steps, cycleSteps, nextPrime);
        assert ModDiv.mod(List.sum(cycleSteps), nextPrime) == 0;

        /**
         * Proof that shiftedIntegral is sorted
         */
        assert List.last(integral) == initial + List.sum(cycleSteps[..|integral|]);
        Cycle.cycleNonZero(steps, cycleSteps, nextPrime);
        Integral.integralValuesIncrease(shifted, nextInitial, shiftedIntegral);
        assert List.sorted(shiftedIntegral);

        /**
         * Proof that sum of shifted is equal to the sum of the cycle steps
         */        
        var lastShifedIntegral := List.last(shiftedIntegral); 
        var sumShifted := List.sum(shifted);
        Derivative.sumOfDerivativeEqualsLastElement(shiftedIntegral, shifted, nextInitial);
        assert lastShifedIntegral == sumShifted + nextInitial;
        assert shifted == List.shift(cycleSteps);
        assert List.sum(shifted) == List.sum(cycleSteps);
        assert sumShifted == List.sum(cycleSteps);

        /**
         * Sum of the shifted % nextPrime == 0
         * next Initial % next Prime != 0
         * last element in the shifted integral % next Prime != 0
         */
        assert ModDiv.mod(List.sum(cycleSteps),nextPrime) == 0;
        assert ModDiv.mod(sumShifted,nextPrime) == 0;
        assert ModDiv.mod(lastShifedIntegral,nextPrime) == ModDiv.mod(sumShifted + nextInitial,nextPrime);
        ModDiv.modAplusB(nextPrime,sumShifted,nextInitial);
        assert ModDiv.mod(lastShifedIntegral,nextPrime) == ModDiv.mod(nextInitial,nextPrime);
        assert ModDiv.mod(lastShifedIntegral,nextPrime) != 0;
        assert ModDiv.mod(nextInitial,nextPrime) != 0;
        assert ModDiv.mod(List.last(shiftedIntegral),nextPrime) != 0;


        Multiple.keepFilteredFromList(shiftedIntegral, nextPrime, filteredShiftedIntegral);
        assert List.sorted(filteredShiftedIntegral);
        List.propertySorted(filteredShiftedIntegral);
        assert forall k :: 0 <= k < |filteredShiftedIntegral| ==> List.last(filteredShiftedIntegral) >= filteredShiftedIntegral[k];

        assert List.last(filteredShiftedIntegral) == lastShifedIntegral;
        
        forall p | 0 <= p < |primes|
            ensures Multiple.isNotMultiple(shiftedIntegral, primes[p])
            ensures Multiple.isNotMultiple(filteredShiftedIntegral, primes[p])
            ensures ModDiv.mod(List.last(filteredShiftedIntegral) - nextInitial, primes[p]) == 0;
        {
            assert ModDiv.mod(List.sum(steps), primes[p]) == 0;
            Cycle.sumMultipleList(steps, cycleSteps, nextPrime);
            assert List.sum(cycleSteps) == List.sum(steps) * nextPrime;
            Cycle.cycleMultipleMod(steps, cycleSteps, primes[p], nextPrime);
            Multiple.shiftedStillNonMultiple(cycleSteps, integral, primes[p], initial, shiftedIntegral);
            assert Multiple.isNotMultiple(shiftedIntegral, primes[p]);
            
            
            Cycle.cycleMultipleMod(steps, cycleSteps, primes[p], nextPrime);
            
            assert ModDiv.mod(List.sum(cycleSteps),primes[p]) == 0;
            assert ModDiv.mod(sumShifted,primes[p]) == 0;
            assert ModDiv.mod(lastShifedIntegral,primes[p]) == ModDiv.mod(sumShifted + nextInitial,primes[p]);
            ModDiv.modAplusB(primes[p],sumShifted,nextInitial);
            assert ModDiv.mod(lastShifedIntegral,primes[p]) == ModDiv.mod(nextInitial, primes[p]);
            assert ModDiv.mod(lastShifedIntegral,primes[p]) != 0;

            Multiple.filteredStillNotMultiple(shiftedIntegral, primes[p], nextPrime, filteredShiftedIntegral);
            assert Multiple.isNotMultiple(filteredShiftedIntegral, primes[p]);

            assert primes[p] > 0; // 3
            // list is non zero, non empty and the List.sum of the list is multiple of m
            assert |filteredShiftedIntegral| > 0; // 2
            assert List.nonZero(filteredShiftedIntegral); // [2,4]
            assert ModDiv.mod(sumShifted,primes[p]) == 0;
            assert ModDiv.mod(List.last(filteredShiftedIntegral) - nextInitial, primes[p]) == 0;

        }
        Multiple.filteredMultiplesIsNotMultiple(shiftedIntegral, nextPrime, filteredShiftedIntegral);
        assert Multiple.isNotMultiple(filteredShiftedIntegral, nextPrime);

        assert Derivative.isDerivative(filteredShiftedIntegral, nextInitial, nextSteps);
        assert Integral.isIntegral(nextSteps, nextInitial, integralNextSteps);
        Derivative.integralOfDerivative(filteredShiftedIntegral, nextSteps, integralNextSteps, nextInitial);
        assert filteredShiftedIntegral == integralNextSteps;

        Derivative.sumOfDerivativeEqualsLastElement(filteredShiftedIntegral, nextSteps, nextInitial);

        assert List.sum(nextSteps) == List.last(filteredShiftedIntegral) - nextInitial;

        assert List.nonZero(shifted);
        Integral.integralValuesIncrease(shifted, nextInitial, shiftedIntegral);
        Integral.integralValuesRelative(shifted, nextInitial, shiftedIntegral);
        assert shiftedIntegral[0] == shifted[0] + nextInitial;
        assert forall v :: 0 < v < |shiftedIntegral| ==> shiftedIntegral[v] - shiftedIntegral[v-1] > 0;
        assert forall v :: 0 < v < |shiftedIntegral| ==> shiftedIntegral[v] > shiftedIntegral[v-1];
        Multiple.keepFilteredFromList(shiftedIntegral, nextPrime,  filteredShiftedIntegral);
        assert List.sorted(shiftedIntegral);
        assert List.sorted(filteredShiftedIntegral);
        assert forall v :: 0 < v < |filteredShiftedIntegral| ==> filteredShiftedIntegral[v] > filteredShiftedIntegral[v-1];
        assert forall v :: 0 < v < |filteredShiftedIntegral| ==> filteredShiftedIntegral[v] > shiftedIntegral[0];
        assert initial > 0;
        assert nextInitial == initial + steps[0];
        assert nextInitial > 0;
        assert Derivative.isDerivative(filteredShiftedIntegral, nextInitial, nextSteps);
        assert forall v :: 0 < v < |shiftedIntegral| ==> shiftedIntegral[v] > shifted[0] + nextInitial > nextInitial;
        assert shifted[0] > 0;
        assert filteredShiftedIntegral[0] >= shiftedIntegral[0];
        Derivative.derivativeOfSortedList(nextSteps,nextInitial,filteredShiftedIntegral);        
        assert List.nonZero(nextSteps);

        forall p | 0 <= p < |primes|
            ensures Multiple.isNotMultiple(shiftedIntegral, primes[p])
            ensures Multiple.isNotMultiple(filteredShiftedIntegral, primes[p])
            ensures ModDiv.mod(List.sum(nextSteps),primes[p]) == 0;
            ensures ModDiv.mod(List.sum(nextSteps) + nextInitial,primes[p]) != 0;
        {
            var sumNextSteps := List.sum(nextSteps);
            assert ModDiv.mod(List.last(filteredShiftedIntegral) - nextInitial, primes[p]) == 0;
            assert sumNextSteps == List.last(filteredShiftedIntegral) - nextInitial;
            assert ModDiv.mod(sumNextSteps,primes[p]) == 0;
            assert Multiple.isNotMultiple(filteredShiftedIntegral, nextPrime);
            assert ModDiv.mod(sumNextSteps + nextInitial,primes[p]) != 0;
            assert ModDiv.mod(List.sum(nextSteps) + nextInitial,primes[p]) != 0;
            ModDiv.modAplusB(primes[p],sumNextSteps,nextInitial);
            assert ModDiv.mod(sumNextSteps + nextInitial,primes[p]) == ModDiv.mod(nextInitial,primes[p]);
            assert ModDiv.mod(nextInitial,primes[p]) != 0;
            assert ModDiv.mod(sumNextSteps + nextInitial,primes[p]) != 0;

            var modIntegralList := ModDiv.modListFromList(filteredShiftedIntegral, primes[p]);
            var cycleList := Cycle.cycle(nextSteps, |nextSteps| * cycleMultipler);
            var integralCycle := Integral.integral(cycleList, nextInitial);
            assert Integral.isIntegral(cycleList, nextInitial, integralCycle);
            var modIntegralCycle := ModDiv.modListFromList(integralCycle, primes[p]);


            assert cycleMultipler > 0; // 2
            assert primes[p] > 0; // 3

            // list is non zero, non empty and the List.sum of the list is multiple of m
            assert |nextSteps| > 0; // 2
            assert List.nonZero(nextSteps); // [2,4]
            assert ModDiv.mod(List.sum(nextSteps), primes[p]) == 0; // 2 + 4 == 6; mod(6,3) == 0

            modOfIntegralIsCycle(
                nextSteps,
                cycleMultipler,
                primes[p],
                nextInitial
            );
        }
    }
}