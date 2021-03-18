include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"
include "multiple.dfy"

module Prime {

    import ModDiv
    import List
    import Multiple
    import Cycle

    function method isPrime(value: nat): bool
    {
        value > 1 && forall v: nat :: 1 < v < value ==>
            ModDiv.mod(value, v) != 0
    }

    function method isPrimeList(list: seq<nat>): bool
        // all the values are unique and sorted
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
        var current  := if (isPrime(value)) then [value] else [];
        var previous := if value > 1 then generatePrimeList(value - 1) else [];

        assert |current| > 0 ==> List.max(current) == value;
        assert forall k :: 0 <= k < |current|  ==> isPrime(current[k]);
        assert forall k :: 0 <= k < |previous| ==> isPrime(previous[k]);
        previous + current
    }

    lemma generatePrimeListIsPrimeList(value:nat, list: seq<nat>)
        requires list == generatePrimeList(value);
        // inside of the bound values
        ensures |list| > 0 ==> List.max(list) <= value;
        // sorted and unique
        ensures List.sorted(list);
        // all the prime until value
        ensures forall v: nat :: 0 <= v < value ==> (isPrime(v)  ==> v  in list);
        // only primes until the value
        ensures forall v: nat :: 0 <= v < value ==> (!isPrime(v) ==> v !in list);
        // check the prime list def
        ensures isPrimeList(list);
        decreases value;
    {
        assert isPrime(1) == false;
        assert isPrime(0) == false;
        // all values before 2 are not primes
        assert forall v: nat :: 0 <= v < 2 ==> isPrime(v) == false;

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

        // load previous definition
        var previous := if value > 1 then generatePrimeList(value - 1) else [];

        // load current definition
        var current := if isPrime(value) then [value] else [];

        // recursive call if allowed
        // assumes that the previous have the expected properties
        if ( value > 0 ) {
            generatePrimeListIsPrimeList(value - 1, previous);
        }

        // check if the new list will keep these properties
        if ( isPrime(value) ) {
            assert value in list;
            assert |list| > 0;
            assert list == previous + current;
            assert |current| > 0;
            if (|previous| > 0 ) {
                List.maxSumList(previous,current);
                assert List.max(current) == value;
                assert List.max(previous) <= value - 1;
                assert List.max(list) == value;
            } else {
                assert list == current;
                assert List.max(current) == value;
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

        assert isPrime(value) ==> current == [value];
        assert isPrime(value) ==> value in current;
        assert list == previous + current;

        // all values in the previous are prime
        assert forall k: nat :: 0 < k < |previous| ==> isPrime(previous[k]);
        // since the current value will be only in the list if prime
        assert  isPrime(value) ==> value  in list;
        assert !isPrime(value) ==> value !in list;
        // all values in the list are still prime
        assert forall k: nat :: 0 < k < |list| ==> isPrime(list[k]);

        // all prime values before value are in the previous list
        assert forall v: nat :: 0 <= v < value ==> (isPrime(v) ==> v in previous);
        // since the current value will be only in the list if prime
        // all prime values until value are in the list
        assert forall v: nat :: 0 <= v <= value ==> (isPrime(v) ==> v in list);
    }

    lemma evenNumbesBiggerThan2AreNotPrime()
        ensures forall v :: 1 < v ==> isPrime(v*2) == false;
    {
        forall v | 1 < v
            ensures ModDiv.mod(v*2,2) == 0;
            ensures isPrime(v*2) == false;
        {
            assert v > 1;
            assert v * 2 > 2;
            ModDiv.modBOfMTimesB(v,2);
            assert ModDiv.mod(v*2,2) == 0;
            assert isPrime(v*2) == false;
        }
        // mod(b * m, b) == 0
    }

    // lemma filterPrimes()
    // if we filter out all the multiples of any number of primes the number of multiples of other
    // primes should keep stable ( - 1 max )


    lemma numberOfMultiplesOfSomeValue( value: nat, start: nat, end: nat, list: seq<nat>, filtered: seq<nat>, modList: seq<nat>)
        requires value > 0;
        requires isPrime(value);
        requires end > start;
        requires end > 0;
        requires ModDiv.isModListFromValue(value, modList);
        requires |list| == end - start;
        requires forall k :: 0 <= k < |list| ==> list[k] == start + k;
        requires |modList| == end;
        requires |modList| > 0;
        requires |modList| > value;
        requires Multiple.isFilterMultiples(list,value,filtered);
//        // ensures |filtered| <= (|list| / value) - 1;
        // ensures |filtered| >= (|list| / value) + 1;
    {        
        // /* we are removing all and only the multiples of the value */
        Multiple.keepFilteredFromList(list,value,filtered);
        assert forall k :: 0 <= k < |list| ==> ( ModDiv.mod(list[k],value) == 0 ==> list[k] !in filtered );
        assert forall k :: 0 <= k < |list| ==> ( ModDiv.mod(list[k],value) != 0 ==> list[k]  in filtered );

        /* check that matches with the def of modList */
        assert forall k :: 0 <= k < |list| ==> list[k] == start + k;
        assert forall k :: 0 <= k < |modList| ==> modList[k] == ModDiv.mod(k,value);
        assert forall k :: 0 <= k < |modList| ==> ModDiv.mod(k,value) < value;
        // // assert List.max(modList) < value;   
    //    assert forall k :: 0 <= k < |list| ==> ModDiv.mod(list[k], value) == modList[start + k];
        assert forall k :: 0 <= k < |list| ==> ( modList[k + start] == 0 ==> list[k] !in filtered );
        assert forall k :: 0 <= k < |list| ==> ( modList[k + start] != 0 ==> list[k]  in filtered );
        assert List.countWithValue(modList[start..],0) == |list| - |filtered|;

        var smallModList := modList[..value]; 
        ModDiv.modListValuesRepeat(modList, value);
        Cycle.modIsCycle(modList, value);
        Cycle.cycleAlwaysRepeatTheSameValues(smallModList, modList);


        assert isPrime(value);
        assert value > 1;
        assert forall v: nat :: 1 < v < value ==> ModDiv.mod(value, v) != 0;
        assert forall v: nat :: 1 < v < value ==> ModDiv.mod(v, value) == v;
        assert ModDiv.mod(value,value) == 0;
        assert ModDiv.mod(0,value) == 0;
        assert smallModList[0] == 0;
        
        // all values in mod list are cycle around the first loop
        // in the first loop only one mod is
        assert forall k :: 0 <= k <  |modList| ==> modList[k] == modList[ModDiv.mod(k,value)];
        assert forall k :: 0 <= k <  |smallModList| ==> ModDiv.mod(k,value) == k;
        assert forall k :: 0 <= k <  |smallModList| ==> smallModList[k] == k;
        assert forall k :: 0 <= k < |smallModList[1..]| ==> smallModList[1..][k] != 0;
        List.notFoundShouldReturnZero(smallModList[1..], 0);
        assert List.countWithValue(smallModList[1..], 0) == 0;
        List.distributiveCount([smallModList[0]],smallModList[1..], 0);
        assert List.countWithValue([smallModList[0]],0) == 1;
        assert List.countWithValue(smallModList,0) == List.countWithValue([smallModList[0]],0) + List.countWithValue(smallModList[1..],0);
        assert List.countWithValue(smallModList,0) == 1;
   }

    // lemma thereIsSomePrimeBetweenAPrimeAndItSquared(prime: nat)
    // {
    // }
}