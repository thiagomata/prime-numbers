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

    /**
     * The input (a,b,0,a) is an valid input, since
     * 0 * b + a == a
     *
     * Using this input, we could get the mod and div ensuring the
     * required properties to assert that ModDiv IsModDiv
     */
    function method getModDiv(a: nat, b: nat): (nat,nat)
        requires b > 0;
    {
        assert 0 * b + a == a;
        assert a <= a;
        modDiv(a, b, 0, a)
    }

    lemma assertModDivIsModDiv(a: nat, b: nat, div: nat, remainder: nat)
        requires 0 * b + a == a;
        requires b > 0;
        requires div == pairFirst(getModDiv(a,b));
        requires remainder == pairLast(getModDiv(a,b));
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
        var result := getModDiv(a, b);
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
        var result := getModDiv(a, b);
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
            assert b * diffDiv == diff;
            assert div2 < div1 ==> diffDiv < 0;

            if ( diffDiv < 0 ) // proof by contradiction
            {
                assert b >= 1;
                assert b * diffDiv == diff;
                assert diff < 0;  // impossible 
                assert false;
            }

            assert div2 > div1 ==> diffDiv > 0;
            assert div2 > div1 ==> diffDiv >= 1;
            
            if ( diffDiv > 0 ) // proof by contradiction  
            {
                assert b >= 1;
                assert b * diffDiv == diff;
                assert diff > b; // impossible
                assert false;
            }
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
            
            if (diffDiv < 0 ) { // proof by contradiction
                assert b * diffDiv == diff;
                assert diff < 0;  // impossible 
                assert false;
            }

            assert div1 > div2 ==> diffDiv > 0;
            assert div1 > div2 ==> diffDiv > 1;

            if (diffDiv > 0) { // proof by contradiction
                assert b >= 1;
                assert diffDiv >= 1;
                assert b * diffDiv == diff;
                assert b * diffDiv > b ==> diff > b; // impossible
                assert false;
            }
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

        if ( div1 >= 1 ) // proof by contradiction 
        {
            assert r1 >= 0;
            assert b > 0;
            assert div1 >= 1;
            assert div1 * b + r1 >= b; // impossible
            assert false;
        }

        assert div1 == 0;
        assert r1 == a;
    }

    lemma modSmallValues(a: nat, b: nat)
       requires b > 0;
       requires a < b;
    {
        assert 0 * b + a == a;
        assert isModDiv(a, b, 0, a);
        var result := getModDiv(a,b);
        assert isModDiv(a,b,pairFirst(result),pairLast(result));
        modSmallValuesFull(a,b,pairLast(result),pairFirst(result));
    }

    lemma modMod(a: nat, b:nat)
        requires b > 0;
        ensures mod(a,b) == mod(mod(a,b),b);
    {
        var result := getModDiv(a, b);
        var result2 := getModDiv(pairLast(result), b);
        modModFull(
            a, b,
            pairLast(result), pairLast(result2),
            pairFirst(result), pairFirst(result2)
        );        
    }
    /**
     * We can replay the mod function into the result of the function many times
     * that will not affect the result.
     *
     * mod(mod(a,b)) == mod(a,b)
     */
    lemma modModFull(a: nat, b: nat, r1: nat, r2: nat, div1: nat, div2: nat)
       requires b > 0;
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
    lemma modAOnBEqualsModAPlusBOnBFull(a: nat, b: nat, r1: nat, r2: nat, div1: nat, div2: nat)
       requires b > 0;
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

            if ( diffDiv >= 1 ) // proof by contradiction 
            {
                assert b >= 1;
                assert diffDiv >= 1;
                assert b * diffDiv == diff;
                assert diff >= b; // impossible
                assert false;
            }

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

            if ( diffDiv >= 1 ) // proof by contradiction
            { 
                assert b >= 1;
                assert diffDiv >= 1;
                assert b * diffDiv >= b; // impossible
                assert false;
            }
            
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

    lemma modAOnBEqualsModAPlusBOnB(a: nat, b: nat)
        requires b > 0;
        ensures mod(a,b) == mod(a + b, b);
    {
        var result := getModDiv(a, b);
        var result2 := getModDiv(a + b, b);
        modAOnBEqualsModAPlusBOnBFull(
            a, b,
            pairLast(result), pairLast(result2),
            pairFirst(result), pairFirst(result2)
        );
    }

    /**
     * mod(a + m * b, b) == mod(a,b);
     * div(a + m * b, b) == div(a,b) + m;
     */
    lemma modAOnBEqualsModAMoreMTimesBFull(a: nat, b: nat, r1: nat, r2: nat, div1: nat, div2: nat, m: nat)
       requires b > 0;
    //    requires a >= b;
       requires isModDiv(a, b, div1, r1);
       requires isModDiv(a + m * b, b, div2, r2);
       ensures r1 == r2;
       ensures div2 == div1 + m;
    {
        assert m > 1 ==> a + m * b > b;
        assert m == 0 ==> a + m * b == a;
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
            
            if( divDiff >= 1 ) // proof by contradiction 
            {
                assert r1 - r2 < b;
                assert b >= 1;
                assert b * divDiff == r1 - r2;
                assert b * divDiff >= b; // impossible
                assert false;
            }
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
            if ( divDiff  >= 1 ) // proof by contradiction 
            {
                assert r2 - r1 < b;
                assert b * divDiff == r2 - r1;
                assert b >= 1;
                assert divDiff >= 1;
                assert divDiff * b >= b; // impossible
                assert false;
            }
            assert divDiff == 0;
            assert div1 + m - div2 == 0;
            assert div2 == div1 + m;
            assert b * 0 == r2 - r1;
            assert r2 == r1;
        }
    }

    lemma modAOnBEqualsModAMoreMTimesB(a: nat, b: nat, m: nat)
       requires b > 0;
       ensures mod(a,b) == mod(a + m * b, b);
       ensures div(a + m * b, b) == div(a,b) + m;
    {
        var modDivAB := getModDiv(a,b);
        var modDivAMB := getModDiv(a + m * b, b);

        var div1 := pairFirst(modDivAB);
        var div2 := pairFirst(modDivAMB);

        var r1 := pairLast(modDivAB);
        var r2 := pairLast(modDivAMB);

        modAOnBEqualsModAMoreMTimesBFull(
            a, b, 
            r1, r2, 
            div1, div2,
            m
        );
        assert mod(a,b) == mod(a + m * b, b);
        assert div(a + m * b, b) == div(a,b) + m;
    }

    /**
     * assert mod(v1+v2,div) == mod(mod(v1,div)+mob(v2,x),div)
     *
     * assert rSum == rModSum
     * where rSum == mod(v1+V2)
     * and   vModSum = mod(v1,div) + mod(v2,div)
     * and   rModSum == mod(vModSum,div)
     */
    lemma modAplusBFull(
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
            assert div * divFactor ==  diffR;
            assert div * divFactor < div;
            
            if ( divFactor > 1 ) // proof by contradiction 
            {
                assert div >= 1;
                assert divFactor > 1;
                assert div * divFactor >= div; // impossible
                assert false;
            }
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
            assert div * divFactor ==  diffR;
            assert div * divFactor < div;

            if (divFactor > 1 ) // proof by contradiction 
            {
                assert div >= 1;
                assert divFactor > 1;
                // assert div * divFactor >= div; // impossible
                assert false;
            }

            assert divFactor == 0;
            assert rSum - rModSum == div * 0;
            assert rSum - rModSum == 0;
            assert rSum == rModSum;
        }

        assert rSum == rModSum;
    }

    /**
     * ensures mod(a+b,div) == mod( mod(a, div) + mod(b, div), div);
     *
     */
    lemma modAplusB(
        div: nat, v1: nat, v2: nat
    )
       requires div > 0;
       ensures mod(v1+v2,div) == mod( mod(v1, div) + mod(v2, div), div);
       ensures mod(v1, div) == 0 ==> mod(v1+v2,div) == mod(v2, div);
       ensures mod(v2, div) == 0 ==> mod(v1+v2,div) == mod(v1, div);
    {
       var vSum := v1 + v2;
       var v1ModDiv := getModDiv(v1, div);
       var div1 := pairFirst(v1ModDiv);
       var r1 := pairLast(v1ModDiv);
       var v2ModDiv := getModDiv(v2, div);
       var div2 := pairFirst(v2ModDiv);
       var r2 := pairLast(v2ModDiv);
       var vModSum := r1 + r2;
       var vSumModDiv := getModDiv(vSum, div);
       var divSum := pairFirst(vSumModDiv);
       var rSum := pairLast(vSumModDiv);
       var vModSumDiv := getModDiv(vModSum, div);
       var divModSum := pairFirst(vModSumDiv);
       var rModSum := pairLast(vModSumDiv);
        
        modAplusBFull(
            div, 
            v1, v2, vSum, vModSum,
            r1, r2, rSum, rModSum,
            div1, div2, divSum, divModSum
        );

        assert mod(v1+v2,div) == mod( mod(v1, div) + mod(v2, div), div);
        if ( mod(v1,div) == 0 ) {
            assert mod(v1+v2,div) == mod( 0 + mod(v2, div), div);
            assert mod(v1+v2,div) == mod( mod(v2, div), div);
            modMod(v2, div);
            assert mod(v1+v2,div) == mod(v2, div);
        }
        if ( mod(v2,div) == 0 ) {
            assert mod(v1+v2,div) == mod( mod(v1, div) + 0, div);
            assert mod(v1+v2,div) == mod( mod(v1, div), div);
            modMod(v1, div);
            assert mod(v1+v2,div) == mod(v1, div);
        }
    }

    /**
     * mod(b * m, b) == 0;
     */
    lemma modBOfMTimesB(
        b: nat, m: nat
    )
       requires b > 0;
       ensures mod(b * m, b) == 0;
       decreases m;
    {
        var a := b * m;
        if ( m == 0 ) {
            assert a == 0;
            assert mod(a, b) == mod(0, b);
            assert mod(a, b) == 0;
        } else {
            assert m > 0;
            assert a == b * m;
            assert a >= m;
            var smallA := a - b;
            assert smallA >= 0;
            modAOnBEqualsModAPlusBOnB(smallA, b);
            assert mod(a, b) == mod(smallA, b);
            assert a == b * m;
            assert a - b == b * m - b;
            assert b * m - b == b * ( m - 1 ); 
            assert a - b == b * ( m - 1 );
            modBOfMTimesB(b, m - 1);
        }
    }

    /**
     * mod(a, b) == 0 ==> mod(m * a, b) == 0;
     */
    lemma modATimesNIsZero(
        b: nat, a: nat, m: nat
    )
       requires b > 0;
       requires mod(a, b) == 0;
       ensures mod(a * m, b) == 0;
       decreases m;
    {
        if ( m == 0 ) {
            assert a * m == 0;
            assert mod(a * m, b) == mod(0 , b) == 0;
        } else {
            var n := m;
            while ( n > 0 )
                invariant n >= 0;
                invariant n <= m;
                invariant mod(a * m, b) == mod( a * n, b);
                decreases n;
            {
                var smallA := a * n - a;
                assert smallA >= 0;
                modAplusB(b,smallA, a);
                assert mod(a * n, b) == mod( mod(smallA, b) + mod(a,b), b);
                assert mod(a,b) == 0;
                assert mod(a * n, b) == mod( mod(smallA, b) + 0, b);
                assert mod(a * n, b) == mod( mod(smallA, b), b);
                modMod(smallA, b);
                assert mod(a * n, b) == mod(smallA, b);
                n := n - 1;
            }
            assert n == 0;
            assert mod(a * 0, b) == mod(a * m, b); 
            assert mod(0, b) == mod(a * m, b); 
            assert 0 == mod(a * m, b); 
        }
    }

    function isModListFromValue(loop: nat, result: seq<nat>): bool
        requires loop > 0;
    {
        forall v: nat :: 0 <= v < |result| ==> result[v] == mod(v, loop)
    }

    function isModListFromList(list: seq<nat>, value: nat, modList: seq<nat>): bool
        requires |list| == |modList|;
        // requires |list| > 0;
        requires value > 0;
    {
        forall v: nat :: 0 <= v < |list| ==> modList[v] == mod(list[v], value)
    }

    method getModDivFromValue(size: nat, loop: nat) returns (resultModList: seq<nat>, resultDivList: seq<nat>)
        requires loop > 0;
        ensures |resultModList| == size;
        ensures |resultDivList| == size;
        ensures isModListFromValue( loop, resultModList );
        ensures forall k : nat :: 0    <= k < |resultDivList| ==> isModDiv(k, loop, resultDivList[k], resultModList[k]);
        ensures forall k : nat :: 0    <= k < |resultModList| ==> resultModList[k] < loop;
        ensures forall k : nat :: loop <  k < |resultModList| ==> resultModList[k] == resultModList[k - loop];
    {
        var arrMod := new nat[size];
        var arrDiv := new nat[size];
        var k := 0;
        while (k < size)
            decreases size - k;
            invariant 0 <= k <= size;
            invariant forall v: nat :: 0 <= v < k ==> arrMod[v] == mod(v, loop);
            invariant forall v: nat :: 0 <= v < k ==> arrDiv[v] == div(v, loop);
            invariant forall v: nat :: 0 <= v < k ==> arrMod[v] == mod(v + loop, loop);
        {
            var resultModDiv := getModDiv(k, loop);
            var div := pairFirst(resultModDiv);
            var remainder := pairLast(resultModDiv);
            assert div * loop + remainder == k;
            assert remainder < loop;
            assert remainder == mod(k, loop);
            modAOnBEqualsModAPlusBOnB(k, loop);
            assert mod(k,loop) == mod(k + loop, loop);
            assert remainder == mod(k + loop, loop);
            assert isModDiv(k, loop, div, remainder);

            arrMod[k] := remainder;
            arrDiv[k] := div;
            k := k + 1;
        }
        assert k == size;
        assert forall v: nat :: 0 <= v < k ==> arrMod[v] == mod(v, loop);
        assert forall v: nat :: 0 <= v < k ==> arrDiv[v] == div(v, loop);
        assert forall v: nat :: 0 <= v < k ==> mod(v, loop) == mod( v + loop, loop);
        assert forall v: nat :: loop < v < k ==> arrMod[v - loop] == arrMod[v];
        // array to seq
        resultModList := arrMod[..];
        resultDivList := arrDiv[..];
        assert |resultModList| == size;
        assert |resultDivList| == size;
    }

    function method modListFromList(list: seq<nat>, value: nat ): seq<nat>
        requires value > 0;
        ensures |list| == |modListFromList(list, value)|;
        decreases list;
        ensures isModListFromList(list,value,modListFromList(list,value));
    {
        var modList := if (list == []) then [] 
        else [mod(list[0], value)] + modListFromList(list[1..], value);

        assert |modList| == |list|;
        assert list == [] ==> modList == [];
        assert |list| == 1 ==> modList == [mod(list[0],value)];
        assert |list| > 1 ==> modList == [mod(list[0],value)] + modListFromList(list[1..], value);
        assert isModListFromList(list,value, modList);

        modList
    }

    // method modListfromList(list: seq<nat>, value: nat ) returns (modList: seq<nat>)
    //     requires |list| > 0;
    //     requires value > 0;
    //     ensures |list| == |modList|;
    //     ensures isModListFromList(list,value,modList);
    // {
    //     var distance := |list|;
    //     var arr := new nat[distance];
    //     var k := 0;
    //     while (k < |list|)
    //         decreases |list| - k;
    //         invariant 0 <= k <= |list|;
    //         invariant forall v: nat :: 0 <= v < k ==> arr[v] == mod(list[v], value);
    //     {
    //         arr[k] := mod(list[k], value);
    //         k := k + 1;
    //     }
    //     modList := arr[..];
    //     assert |list| == |modList|;
    // }

    /**
     * Since is a modList modList[v] == modList[v + loopValue] == modList[v - loopValue]
     */
    lemma modListValuesRepeat(modList: seq<nat>, loopValue: nat)
        requires loopValue > 0;
        requires isModListFromValue(loopValue, modList);
        ensures forall v: nat :: loopValue < v < |modList| ==> modList[v - loopValue] == modList[v];
        ensures forall v: nat :: 0 < v < |modList| - loopValue ==> modList[v] == modList[v + loopValue];
    {
        assert forall v: nat :: 0 <= v < |modList| ==> modList[v] == mod(v, loopValue);
        var v := 0;
        while ( v < |modList| )
            decreases |modList| - v;
            invariant v <= |modList|;
            invariant forall k: nat :: 0 <= k < v ==> modList[k] == mod(k, loopValue);
            invariant forall k: nat :: 0 <= k < v ==> modList[k] == mod(k + loopValue, loopValue);
            invariant forall k: nat :: loopValue <= k < v ==> modList[k - loopValue] == mod(k, loopValue);
            invariant forall k: nat :: loopValue <= k < v ==> modList[k - loopValue] == modList[k];
            invariant forall k: nat :: 0 <= k < v - loopValue ==> modList[k] == modList[ k + loopValue ];
        {
            modAOnBEqualsModAPlusBOnB(v, loopValue);
            assert mod(v, loopValue) == mod(v + loopValue, loopValue);
            assert modList[v] == mod(v, loopValue);
            assert modList[v] == mod(v + loopValue, loopValue);
            v := v + 1;
        }
        assert v == |modList|;
    }

    function isNotMultiple(list: seq<nat>, value: nat): bool
        requires value > 0;
        requires |list| > 0;
    {
        forall v: nat :: 0 <= v < |list| ==> mod(list[v], value) != 0
    }

    // method Main() {
    //     print("hello from ModDiv \n");
    //     print("\n mod(5,2) \n");
    //     print(mod(5,2));
    //     print("\n mod(10,2) \n");
    //     print(mod(10,5));
    //     print("\n");
    //     var modList, divList := modList(12,3);
    //     print(modList);
    //     print(divList);
    // }
}