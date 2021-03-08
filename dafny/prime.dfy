include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"
include "multiple.dfy"

module Prime {

    import ModDiv
    import List

    function method isPrime(value: nat): bool
    {
        value > 1 && forall v: nat :: 1 < v < value ==>
            ModDiv.mod(value, v) != 0
    }

    function method isPrimeList(list: seq<nat>): bool
        requires List.sorted(list);
        // all the values are prime
        ensures isPrimeList(list) ==> forall k: nat :: 0 < k < |list| ==> isPrime(list[k])
        // all the prime values are in the list
        ensures |list| > 0 && isPrimeList(list) ==> forall v: nat :: 2 <= v < list[|list|-1] ==> (isPrime(v)) ==> v in list
    {
        var onlyPrimes := forall k: nat :: 0 < k < |list| ==>
            isPrime(list[k]);

        var maxValue := if |list| > 0 then List.max(list) else 0;
        var allPrimes := forall v: nat :: 2 <= v < maxValue ==>
            (isPrime(v)) ==> v in list;

        onlyPrimes && allPrimes 
    }

    function method generatePrimeList(value:nat): seq<nat>
        ensures forall k :: 0 <= k < |generatePrimeList(value)| ==> isPrime(generatePrimeList(value)[k]);
        ensures isPrime(value) ==> |generatePrimeList(value)| > 0 && List.last(generatePrimeList(value)) == value;
    {
        var top := if (isPrime(value)) then [value] else [];
        var tail := if value > 1 then generatePrimeList(value - 1) else [];

        assert |top| > 0 ==> List.max(top) == value;
        assert forall k :: 0 <= k < |top| ==> isPrime(top[k]);
        assert forall k :: 0 <= k < |tail| ==> isPrime(tail[k]);
        tail + top
    }

    lemma generatePrimeListIsPrimeList(value:nat, list: seq<nat>)
        requires list == generatePrimeList(value);
        ensures |list| > 0 ==> List.max(list) <= value;
        ensures List.sorted(list);
        ensures forall v: nat :: 0 <= v < value ==> (isPrime(v)  ==> v  in list);
        ensures forall v: nat :: 0 <= v < value ==> (!isPrime(v) ==> v !in list);
        ensures isPrimeList(list);
        decreases value;
    {
        assert isPrime(1) == false;
        assert isPrime(0) == false;

        if ( |list| == 0 ) {
            assert List.sorted(list);
            assert isPrimeList(list);
        } else {
            var last := list[|list|-1];
            assert isPrime(last);
            if ( isPrime(value) ) {
                assert last == value;
            } else {
                assert list == generatePrimeList(value - 1);
            }
        }

        var tail := if value > 1 then generatePrimeList(value - 1) else [];
        var top := if isPrime(value) then [value] else [];
        if ( value > 0 ) {
            generatePrimeListIsPrimeList(value - 1, tail);
        }

        if ( isPrime(value) ) {
            assert value in list;
            assert |list| > 0;
            assert list == tail + top;
            assert |top| > 0;
            if (|tail| > 0 ) {
                List.maxSumList(tail,top);
                assert List.max(top) == value;
                assert List.max(tail) <= value - 1;
                assert List.max(list) == value;
            } else {
                assert list == top;
                assert List.max(top) == value;
                assert List.max(list) == value;
            }
            assert List.max(list) == value;
        } else if value > 1 {
            assert list == generatePrimeList(value - 1);
            assert value !in list;
            generatePrimeListIsPrimeList(value - 1, list);
            assert |list| > 0 ==> List.max(list) <= value - 1;
        } else {
            assert list == [];
        }

        assert isPrime(value) ==> top == [value];
        assert isPrime(value) ==> value in top;
        assert list == tail + top;
        assert  isPrime(value) ==> value  in list;
        assert !isPrime(value) ==> value !in list;

        assert forall k: nat :: 0 < k < |list| ==> isPrime(list[k]);

        var maxValueLemma := if |list| > 0 then List.max(list) else 0;
        assert forall v: nat :: 0 <= v < 2 ==> isPrime(v) == false;
        assert forall v: nat :: 0 <= v < value - 1 ==> (isPrime(v) ==> v in tail);
    }

    // lemma thereIsSomePrimeBetweenAPrimeAndItSquared(prime: nat)
    // {

    // }
}