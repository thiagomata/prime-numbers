include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"
include "multiple.dfy"

module Prime {

    import ModDiv
    import List

    function method isPrimeLoop(prime: nat, loopValue: nat): bool 
        requires loopValue > 0;
        decreases loopValue;
    {
        if loopValue == 1 then true 
        else if ModDiv.mod(prime, loopValue) == 0 then false
        else isPrimeLoop(prime,loopValue - 1)
    }

    function method isPrime(prime: nat): bool
    {
        if prime < 2 then false
        else isPrimeLoop(prime, prime - 1)
    }

    function method isPrimeSequence(list: seq<nat>): bool        
    {
        var allElementsArePrimes := forall k :: 0 <= k < |list| ==> isPrime(list[k]);
        var allPrimesAreInTheList := |list| > 0 ==> 
            forall v :: 2 <= v <= List.max(list) ==> ( 
                isPrime(v) ==> exists k  :: 0 <= k < |list| && list[k] == v
            );
        var isSorted := List.sorted(list);
        var isNonZero := List.nonZero(list);

        if !isSorted then false
        else if !isNonZero then false
        else if !allElementsArePrimes then false
        else if !allPrimesAreInTheList then false
        else true
    }

    function method getPrimeSequenceUntil(value: nat): seq<nat>
        ensures value < 2 ==> getPrimeSequenceUntil(value) == [];
        ensures value >= 2 && !isPrime(value) ==> getPrimeSequenceUntil(value) == getPrimeSequenceUntil(value - 1);
        ensures value >= 2 && isPrime(value) ==> |getPrimeSequenceUntil(value)| > 0;
        ensures value >= 2 && isPrime(value) ==> getPrimeSequenceUntil(value)[0] == value;
        decreases value;
    {
        var prev := if value < 2 then [] else getPrimeSequenceUntil(value - 1);
        var primeSequence := if value < 2 then []
        else if isPrime(value) then [value] + prev
        else prev;

        assert value < 2 ==> isPrime(value) == false;
        assert isPrime(value) ==> primeSequence[0] == value;
        assert value >= 2 && !isPrime(value) ==> primeSequence == getPrimeSequenceUntil(value - 1);
        assert value >= 2 && isPrime(value)  ==> primeSequence[0] == value;

        primeSequence
    }

    lemma getPrimeSequenceUntilValueIsPrimeSequence(value: nat, primeSequence: seq<nat>)
        requires primeSequence == getPrimeSequenceUntil(value);
        // ensures isPrimeSequence(primeSequence);
    {
        assert forall v :: 0 <= v < 2 ==> isPrime(v) == false;
        if (value < 2) {
            assert isPrimeSequence(primeSequence);
        } else {
            if (isPrime(value)) {
                assert primeSequence[0] == value;
                assert primeSequence[1..] == getPrimeSequenceUntil(value - 1);
            } else {
                assert primeSequence == getPrimeSequenceUntil(value - 1);
            }
            if (isPrime(value) && isPrime(value - 1))
            {
                assert primeSequence[0] == value;
                assert primeSequence[1] == value - 1;
                assert primeSequence[1] < primeSequence[0];
            }
            if (isPrime(value) && !isPrime(value - 1))
            {
                assert primeSequence[0] == value;
                assert primeSequence[1..] == getPrimeSequenceUntil(value - 2);
                getPrimeSequenceUntilValueIsPrimeSequence(value - 2, primeSequence[1..]);
            }
            if (!isPrime(value) && isPrime(value - 1))
            {
                assert primeSequence == getPrimeSequenceUntil(value - 1);
                getPrimeSequenceUntilValueIsPrimeSequence(value - 1, primeSequence);
            }
            if (!isPrime(value) && !isPrime(value - 1))
            {
                assert primeSequence == getPrimeSequenceUntil(value - 2);
                getPrimeSequenceUntilValueIsPrimeSequence(value - 2, primeSequence);
            }
            assert |primeSequence| > 1 ==> primeSequence[0] > primeSequence[1];
        }
    }

    lemma thereIsSomePrimeBetweenAPrimeAndItSquared(prime: nat)
    {

    }
}