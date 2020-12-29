/**
 * Define our own modDiv function that defines how division and remainder should work.
 * assert division * b + remainder == a
 * assert remainder < b;
 * assert remainder <= a;
 *
 * Using the definition of isModDiv and not the implementation to create the
 * lemmas.
 *
 * Requires that the modDiv method implements that isModDiv definition.
 * Extracts the mod and div from the modDiv definition
 *
 * Ensure some important properties into the mod function
 *  mod(a,b) == mod(a,b) // there is only one single remainder value every a,b pair
 *  mod(n,n) == 0
 *  mod(a + b, b) == mod(a, b)
 *  div(a + b, b) == div(a, b) + 1
 *  if a < b then mod(a,b) == a
 *  mod(mod(a,b)) == mod(a,b)
 *  mod(a + m * b, b) == mod(a,b);
 *  div(a + m * b, b) == div(a,b) * m;
 *
 * This strategy of breaking the function and lemmas from the method implementation
 * seems more aligned with the expectations of the dafny language.
 */
module ModDiv {

    /**
     * Ensures that mod(a,b) == remainder and div(a,b) == div
     *
     * That is:
     * assert division * b + remainder == a
     * assert remainder < b;
     * assert remainder <= a;
     */
    function method isModDiv(a: nat, b: nat, division: nat, remainder: nat): bool
        requires b > 0;
//        requires a >= 0;
    {
        var validIsModDiv := if ! ( division * b + remainder == a ) then false
        else if ! ( remainder < b ) then false
        else if ! ( remainder <= a ) then false
        else true;

        assert validIsModDiv ==> division * b + remainder == a;
        assert validIsModDiv ==> a - remainder == division * b;
        assert validIsModDiv ==> remainder < b;
        assert validIsModDiv ==> remainder <= a;
        validIsModDiv
    }

    function method pairFirst(pair:(nat,nat)): nat
    {
        var (a, b) := pair;
        a
    }

    function method pairLast(pair:(nat,nat)): nat
    {
        var (a, b) := pair;
        b
    }

    /**
     * Starting from one valid input of a,b,div and remainder where
     * div * b + remainder == a, decreases the remainder and increases
     * the div until remainder < b;
     *
     * The input (a,b,0,a) is an valid input, since
     * 0 * b + a == a
     *
     * Using this input, we could get the mod and div ensuring the
     * required properties to assert that ModDiv IsModDiv
     */
    function method modDiv(a: nat, b:nat, div: nat, remainder: nat): (nat,nat)
        requires b > 0;
        requires div * b + remainder == a;
        ensures pairFirst(modDiv(a,b,div,remainder)) * b + pairLast(modDiv(a,b,div,remainder)) == a;
        ensures pairLast(modDiv(a,b,div,remainder)) <= remainder;
        ensures pairLast(modDiv(a,b,div,remainder)) < b;
        ensures isModDiv(a,b,pairFirst(modDiv(a,b,div,remainder)),pairLast(modDiv(a,b,div,remainder)));
        decreases remainder;
    {
        assert div * b + remainder == a;
        assert remainder >= b ==> div * b + b + remainder - b == a;
        assert remainder >= b ==> (div + 1 ) * b + (remainder - b) == a;

        var next_remainder := if remainder >= b then remainder - b else remainder;

        assert next_remainder <= remainder;

        var next_div := div + 1;
        var result := if remainder < b then (div, remainder) else modDiv(a, b, next_div, next_remainder);
        var new_div := pairFirst(result);
        var new_remainder := pairLast(result);

        /**
         * Induction proof that pairFirst(result) * b + pairLast(result) == a;
         */
        assert remainder >= b ==> pairFirst(modDiv(a,b,next_div,next_remainder )) * b + pairLast(modDiv(a,b,div + 1,next_remainder)) == a;
        assert remainder >= b ==> result == modDiv(a,b,next_div,next_remainder );
        assert remainder >= b ==> pairFirst(result) * b + pairLast(result) == a;
        assert remainder >= b ==> pairFirst(result) * b + pairLast(result) == a;
        assert remainder <  b ==> result == (div,remainder);
        assert pairFirst(result) * b + pairLast(result) == a;
        assert new_div * b + new_remainder == a;

        /**
         * Induction proof that remainder < b;
         */
        assert remainder >= b ==> new_remainder == pairLast( modDiv( a, b, div + 1, remainder - b ));
        assert remainder >= b ==> pairLast( modDiv( a, b, div + 1, remainder - b )) <= remainder - b;
        assert remainder >= b ==> new_remainder < remainder;
        assert remainder <  b ==> new_remainder == remainder;
        assert remainder <  b ==> new_remainder < b;

        assert isModDiv(a,b,new_div,new_remainder);
        result
    }

    lemma assertModDivIsModDiv(a: nat, b: nat, div: nat, remainder: nat)
        requires 0 * b + a == a;
        requires b > 0;
        requires div == pairFirst(modDiv(a,b,0,a));
        requires remainder == pairLast(modDiv(a,b,0,a));
        ensures div * b + remainder == a;
        ensures remainder < b;
        ensures isModDiv(a, b, div, remainder);
    {
        // thanks
    }

    function method mod(a: nat, b: nat): nat
       requires b > 0;
       ensures mod(a,b) < b;
    {
        assert 0 * b + a == a;
        var result := modDiv(a, b, 0, a);
        var div := pairFirst(result);
        var remainder := pairLast(result);
        assertModDivIsModDiv(a, b, div, remainder);
        assert isModDiv(a, b, div, remainder);
        assert remainder < b;
        assert remainder <= a;
        remainder
    }

    function method div(a: nat, b: nat): nat
       requires b > 0;       
    {
        assert 0 * b + a == a;
        var result := modDiv(a, b, 0, a);
        var div := pairFirst(result);
        var remainder := pairLast(result);
        assertModDivIsModDiv(a, b, div, remainder);
        assert isModDiv(a, b, div, remainder);
        div
    }

    /**
     *  mod(n,n) == 0;
     *  div(n,n) == 1;
     */
    lemma modNOnNIsZero(a: nat, b: nat, division: nat, remainder: nat)
        requires b > 0;
        // requires a >= 0;
        requires a == b;
        requires isModDiv(a, b, division, remainder)
        ensures remainder == 0;
        ensures division == 1;
    {
        assert division * b + remainder == a;
        assert a == b;
        assert division * b + remainder == b;
        assert b > 0;
        assert remainder < b;
        assert division * b - b == remainder;
        assert b * ( division - 1 ) == remainder;
        var diffB := division - 1;
        assert b * diffB == remainder;
        assert b * diffB < b;
        assert diffB > 0 ==> b * diffB >= b;
        assert diffB == 0;
        assert 0 == remainder;
        assert division - 1 == 0;
        assert division == 1;
    }

    /**
     * mod(a + b, b) == mod(a, b)
     * div(a + b, b) == div(a, b) + 1
     */
    lemma isModDivPlus(a: nat, b: nat, division: nat, remainder: nat)
        requires b > 0;
        // requires a >= 0;
        requires isModDiv(a, b, division, remainder)
        ensures isModDiv( a + b, b, division + 1, remainder)
    {
        assert ( division * b + remainder == a );
        assert ( ( division + 1 ) * b + remainder == a + b );
        assert ( remainder < b );
        assert remainder <= a;
        assert remainder <= a + b;
    }

    /**
     * a > b ==> mod(a, b) == mod(a - b, b)
     * a > b ==> div(a, b) == div(a - b, b) - 1
     */
    lemma isModDivMinus(a: nat, b: nat, division: nat, remainder: nat)
        requires b > 0;
        requires a >= b;
        requires isModDiv(a, b, division, remainder)
        ensures isModDiv( a - b, b, division - 1, remainder)
    {
        assert ( division * b + remainder == a );
        assert ( ( division - 1 ) * b + remainder == a - b );
        assert ( remainder < b );
        assert remainder <= a;
        assert remainder <= a - b;
    }

    /**
     * There is only one div value and remainder for each pair (a,b).
     * 
     * In other words,
     *  if r1 and div1 have values that isModDiv(a,b,div1,r1)
     * and r2 and div2 have values that isModDiv(a,b,div2,r2)
     * then r1 == r2 and div1 == div2
     */
    lemma modAB1equals2(a: nat, b: nat, r1: nat, r2: nat, div1: nat, div2: nat)
       requires b > 0;
       requires isModDiv(a, b, div1, r1);
       requires isModDiv(a, b, div2, r2);
       ensures r1 == r2;
       ensures div1 == div2;
    {
        assert isModDiv(a, b, div1, r1);
        assert isModDiv(a, b, div2, r2);
        assert div1 * b + r1 == a;
        assert div2 * b + r2 == a;
        assert div1 * b + r1 == div2 * b + r2;
        assert r1 <= a;
        assert r2 <= a;
        assert a == div1 * b + r1;
        assert a - r1 == b * div1;
        assert a - r2 == div2 * b;
        assert r1 < b;
        assert r2 < b;
        var diff: nat;
        if (r1 >= r2) {
            diff := r1 - r2;
            assert diff == r1 - r2;
            assert 0 <= diff < b;
            assert r1 == diff + r2;
            assert div1 * b + r1 == div2 * b + r2;
            assert div1 * b + diff + r2 == div2 * b + r2;
            assert div1 * b + diff == div2 * b;
            assert div2 * b - div1 * b == diff;
            assert b * ( div2 - div1 ) == diff;
            var diffDiv := div2 - div1;
            assert div2 < div1 ==> diffDiv < 0;
            assert diffDiv < 0 ==> diff < 0;  // impossible 
            assert div2 > div1 ==> diffDiv > 0;
            assert div2 > div1 ==> diffDiv >= 1;
            assert diffDiv > 0 ==> diff > b; // impossible
            assert div2 == div1;
            assert diff == 0;
        }
        if (r2 >= r1) {
            diff := r2 - r1;
            assert diff == r2 - r1;
            assert 0 <= diff < b;
            assert r2 == diff + r1;
            assert div2 * b + r2 == div1 * b + r1;
            assert div2 * b + diff + r1 == div1 * b + r1;
            assert div2 * b + diff == div1 * b;
            assert div1 * b - div2 * b == diff;
            assert b * ( div1 - div2 ) == diff;
            var diffDiv := div1 - div2;
            assert b * diffDiv == diff;
            assert div1 < div2 ==> diffDiv < 0;
            assert diffDiv < 0 ==> diff < 0;  // impossible 
            assert div1 > div2 ==> diffDiv > 0;
            assert div1 > div2 ==> diffDiv > 1;
            assert diffDiv > 0 ==> diff > b; // impossible
            assert diff == 0;
        }
        assert diff == 0;
        assert r2 == r1;
        assert div1 == div2;

    }

    /**
     * if a < b then mod(a,b) == a
     * Mod of small values are the values itself
     */
    lemma modSmallValuesFull(a: nat, b: nat, r1: nat, div1: nat)
       requires b > 0;
       requires a < b;
       requires isModDiv(a, b, div1, r1);
       ensures r1 == a;
    {
        assert isModDiv(a, b, div1, r1);
        assert div1 * b + r1 == a;
        assert r1 <= a;
        assert a < b;
        assert div1 * b + r1 < b;
        assert div1 >= 1 ==> div1 * b + r1 > b; // impossible
        assert div1 == 0;
        assert r1 == a;
    }

    lemma modSmallValues(a: nat, b: nat)
       requires b > 0;
       requires a < b;
    {
        assert 0 * b + a == a;
        assert isModDiv(a, b, 0, a);
        var result := modDiv(a,b,0,a);
        assert isModDiv(a,b,pairFirst(result),pairLast(result));
        modSmallValuesFull(a,b,pairLast(result),pairFirst(result));
    }

    /**
     * We can replay the mod function into the result of the function many times
     * that will not affect the result.
     *
     * mod(mod(a,b)) == mod(a,b)
     */
    lemma modReplay(a: nat, b: nat, r1: nat, r2: nat, div1: nat, div2: nat)
       requires b > 0;
       requires a - b > 0;
       requires isModDiv(a, b, div1, r1);
       requires isModDiv(r1, b, div2, r2);
       ensures r1 == r2;
       ensures div2 == 0;
    {
        assert r1 < b;
        modSmallValuesFull(r1,b,r2,div2);
    }

    /**
     * mod(a, b) == mod(a + b, b)
     */
    lemma modAOnBEqualsModAPlusBOnB(a: nat, b: nat, r1: nat, r2: nat, div1: nat, div2: nat)
       requires b > 0;
       requires a >= b;
       requires isModDiv(a, b, div1, r1);
       requires isModDiv(a + b, b, div2, r2);
       ensures r1 == r2;
       ensures div2 == div1 + 1;
    {
        assert isModDiv(a, b, div1, r1);
        assert isModDiv(a + b, b, div2, r2);
        assert div1 * b + r1 == a;
        assert div2 * b + r2 == a + b;
        assert r1 <= a;
        assert r2 <= a + b;
        assert 0 <= r1 < b;
        assert 0 <= r2 < b;
         var diff: nat;
        if (r1 >= r2) {
            diff := r1 - r2;
            assert diff == r1 - r2;
            assert diff < b;
            assert r1 == diff + r2;
            assert a == a;
            assert ( a ) + b == a + b;
            assert ( div1 * b + r1 ) + b == div2 * b + r2;
            assert div1 * b + diff + r2 + b == div2 * b + r2;
            assert div1 * b + diff + b == div2 * b;
            assert div2 * b - div1 * b - b == diff;
            assert b * ( div2 - div1 - 1 ) == diff;

            var diffDiv := ( div2 - div1 - 1 );
            
            assert b * diffDiv == diff;
            assert diff < b;
            assert b > 0;
            assert diffDiv >= 1 ==> diff >= b; // impossible
            assert diffDiv < 1;
            assert diffDiv == 0;
            assert 0 == div2 - div1 - 1;
            assert div1 == div2 - 1;
            assert div2 == div1 + 1;

        }
        if (r2 >= r1) {
            diff := r2 - r1;
            assert diff == r2 - r1;
            assert diff < b;
            assert r2 == diff + r1;
            assert a == a;
            assert ( a ) + b == a + b;
            assert div2 * b + r2 == ( div1 * b + r1 ) + b;
            assert div2 * b + diff + r1 == div1 * b + r1 + b;
            assert div2 * b + diff == div1 * b + b;
            assert div1 * b - div2 * b + b == diff;
            assert b * ( div1 - div2 + 1 ) == diff;
            
            var diffDiv := ( div1 - div2 + 1 );
            
            assert b * diffDiv == diff;
            assert diff < b;
            assert b > 0;
            assert diffDiv >= 1 ==> b * diffDiv >= b; // impossible
            assert diffDiv < 1;
            assert diffDiv == 0;
            assert 0 == div1 - div2 + 1;
            assert div1 == div2 - 1;
            assert div2 == div1 + 1;
        }
        assert diff == 0;
        assert r2 == r1;
        assert div1 == div2 - 1;
        assert div2 == div1 + 1;       
    }

    /**
     * mod(a + m * b, b) == mod(a,b);
     * div(a + m * b, b) == div(a,b) * m;
     */
    lemma modAOnBEqualsModAMoreMTimesB(a: nat, b: nat, r1: nat, r2: nat, div1: nat, div2: nat, m: nat)
       requires b > 0;
       requires a >= b;
       requires isModDiv(a, b, div1, r1);
       requires isModDiv(a + m * b, b, div2, r2);
       ensures r1 == r2;
       ensures div2 == div1 + m;
    {
        var mCurrent: nat := 0;
        assert isModDiv( a, b, div1, r1);
        assert isModDiv(a + b * mCurrent, b, div1 + mCurrent, r1);
        while (mCurrent < m)
            decreases m - mCurrent;
            invariant isModDiv( a + b * mCurrent, b, div1 + mCurrent, r1);
            invariant mCurrent <= m;
        {
            assert isModDiv(a + b * mCurrent, b, div1 + mCurrent, r1);
            isModDivPlus(   a + b * mCurrent, b, div1 + mCurrent, r1);
            assert isModDiv(a + b * mCurrent + b, b, div1 + mCurrent + 1, r1);
            mCurrent := mCurrent + 1;
            assert isModDiv(a + b * mCurrent, b, div1 + mCurrent, r1);
        }
        assert mCurrent == m;
        assert isModDiv(a + m * b, b, div2, r2);
        assert ( div2     ) * b + r2 == a + b * m;
        assert ( div1 + m ) * b + r1 == a + b * m;
        assert div2 * b + r2 == ( div1 + m ) * b + r1;
        assert div2 * b - ( div1 + m ) * b == r1 - r2;
        assert b * ( div2 - div1 - m ) == r1 - r2;
        assert r1 < b;
        assert r2 < b;
        if ( r1 >= r2 ) {
            assert r1 - r2 < b;
            assert b * ( div2 - div1 - m ) == r1 - r2;
            var divDiff := div2 - div1 - m;
            assert b * divDiff == r1 - r2;
            assert divDiff >= 1 ==> b * divDiff >= b; // impossible
            assert divDiff == 0;
            assert div2 - div1 - m == 0;
            assert div2 == div1 + m;
            assert b * 0 == r2 - r1;
            assert r2 == r1;
        }
        if ( r2 >= r1 ) {
            assert r2 - r1 < b;
            assert div2 * b + r2 == ( div1 + m ) * b + r1;
            assert r2 == ( div1 + m ) * b - div2 * b + r1;
            assert r2 - r1 == ( div1 + m ) * b - div2 * b;
            assert r2 - r1 == ( div1 + m - div2 ) * b;
            var divDiff := div1 + m - div2;
            assert b * divDiff == r2 - r1;
            assert divDiff >= 1 ==> b * divDiff >= b; // impossible
            assert divDiff == 0;
            assert div1 + m - div2 == 0;
            assert div2 == div1 + m;
            assert b * 0 == r2 - r1;
            assert r2 == r1;
        }
    }

    /**
     * assert mod(v1+v2,div) == mod(mod(v1,div)+mob(v2,x),div)
     *
     * assert rSum == rModSum
     * where rSum == mod(v1+V2)
     * and   vModSum = mod(v1,div) + mod(v2,div)
     * and   rModSum == mod(vModSum,div)
     */
    lemma modAplusB(
        div: nat, 
        v1: nat, v2: nat, vSum: nat, vModSum: nat,
        r1: nat, r2: nat, rSum: nat, rModSum: nat,
        div1: nat, div2: nat, divSum: nat, divModSum: nat
    )
       requires div > 0;
       requires vSum == v1 + v2;
       requires vModSum == r1 + r2;
       requires isModDiv(v1, div, div1, r1);
       requires isModDiv(v2, div, div2, r2);
       requires isModDiv(vSum, div, divSum, rSum);
       requires isModDiv(vModSum, div, divModSum, rModSum);
       ensures rModSum == rSum;
    {
        assert vSum == v1 + v2;
        assert isModDiv(v1, div, div1, r1);
        assert isModDiv(v2, div, div2, r2);
        assert v1 == div1 * div + r1;
        assert v2 == div2 * div + r2;
        assert vSum == div1 * div + r1 + div2 * div + r2;
        assert vSum == div * div1 + div * div2 + r1 + r2;
        assert vSum == div * (div1 + div2) + r1 + r2;
        assert r1 + r2 == vSum - div * (div1 + div2);

        assert vModSum == r1 + r2;
        assert isModDiv(vModSum, div, divModSum, rModSum);
        assert vModSum == divModSum * div + rModSum;
        assert r1 + r2 == divModSum * div + rModSum;

        assert isModDiv(vSum, div, divSum, rSum);
        assert vSum == divSum * div + rSum;

        assert r1 + r2 == r1 + r2;
        assert vSum - div * (div1 + div2) == divModSum * div + rModSum;
        assert ( divSum * div + rSum ) - div * (div1 + div2) == divModSum * div + rModSum;
        assert divSum * div + rSum - div * (div1 + div2) == divModSum * div + rModSum;
        assert divSum * div - div * (div1 + div2) + rSum == divModSum * div + rModSum;

        assert r1 < div;
        assert r2 < div;
        assert rModSum < div;
        assert rSum < div;
        assert div >= 1;

        if ( rModSum >= rSum ) {
            assert divSum * div - div * (div1 + div2) == divModSum * div + rModSum - rSum;
            assert divSum * div - div * (div1 + div2) - divModSum * div ==  rModSum - rSum;
            assert rModSum - rSum == divSum * div - div * div1 - div * div2 - divModSum * div;
            assert rModSum - rSum == div * ( divSum - div1 - div2 - divModSum );

            var diffR := rModSum - rSum;
            var divFactor := divSum - div1 - div2 - divModSum;

            assert rModSum - rSum == div * divFactor;

            assert diffR < div;
            assert div * divFactor ==  rModSum - rSum;
            assert divFactor > 1 ==> div * divFactor >= div; // impossible
            assert divFactor == 0;
            assert rModSum - rSum == div * divFactor;
            assert rSum - rModSum == div * 0;
            assert rSum - rModSum == 0;
            assert rSum == rModSum;
        }
        if (rModSum <= rSum ) {
            assert divSum * div - div * div1 - div * div2 + rSum == divModSum * div + rModSum;
            assert rSum == divModSum * div + rModSum - divSum * div + div * div1 + div * div2;
            assert rSum == rModSum + divModSum * div - divSum * div + div * div1 + div * div2;
            assert rSum - rModSum == divModSum * div - divSum * div + div * div1 + div * div2;
            assert rSum - rModSum == div * ( divModSum - divSum + div1 + div2 );

            var diffR := rSum - rModSum;
            var divFactor :=  divModSum - divSum + div1 + div2;
            
            assert rSum - rModSum == div * divFactor;

            assert diffR < div;
            assert div * divFactor ==  rSum - rModSum;
            assert divFactor > 1 ==> div * divFactor >= div; // impossible
            assert divFactor == 0;
            assert rSum - rModSum == div * 0;
            assert rSum - rModSum == 0;
            assert rSum == rModSum;
        }

        assert rSum == rModSum;
    }

    function isModList(size: nat, loop: nat, result: seq<nat>): bool
        requires loop > 0;
        // requires |result| == size;
    {
        forall v: nat :: 0 <= v < |result| ==> result[v] == mod(v, loop)
    }

    method modList(size: nat, loop: nat) returns (result: seq<nat>)
        requires loop > 0;
        ensures |result| == size;
        ensures isModList( size, loop, result );
    {
        var arr := new nat[size];
        var k := 0;
        while (k < size)
            decreases size - k;
            invariant 0 <= k <= size;
            invariant forall v: nat :: 0 <= v < k ==> arr[v] == mod(v, loop);
        {
            assert 0 * loop + k == k;
            var resultModDiv := modDiv(k, loop, 0, k);
            var div := pairFirst(resultModDiv);
            var remainder := pairLast(resultModDiv);
            assert div * loop + remainder == k;
            assert remainder < loop;
            assert isModDiv(k, loop, div, remainder);

            arr[k] := remainder;
            k := k + 1;
        }
        assert k == size;
        assert forall v: nat :: 0 <= v < k ==> arr[v] == mod(v, loop);
        // array to seq
        result := arr[..];
        assert |result| == size;
    }

    method Main() {
        print("hello from ModDiv \n");
        print("\n mod(5,2) \n");
        print(mod(5,2));
        print("\n mod(10,2) \n");
        print(mod(10,5));
        print("\n");
        var modList := modList(12,3);
        print(modList);
    }
}