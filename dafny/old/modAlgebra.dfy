/**
 * Define our own mod function ( since I could not proof that mod(a,b) == a % b)
 *
 * Using the difference between the real div and the nat div to calculate mod
 *
 * Ensure some important properties into the mod function
 *  mod(n,n) == 0
 *  mod(m*n,n) == 0
 *  mod(a+m*n,n) == mod(a,n)
 *
 * I am giving up this strategy since I could not proof some important properties using it
 */
module ModAlgebra {

    function floor(r: real): int {
        var i: int := r.Floor as int;
        i
    }

    lemma floorOfInt(i: int)
    ensures floor(i as real) == i;
    {
        // qed.
        assert floor(i as real) == i;
    }

    function method mod(a: nat, b: nat): nat
       requires b > 0;
       requires a >= 0;
    {
        var ar: real := a as real;
        var br: real := b as real;
        var cr: real := ar / br;
        var c: nat := cr.Floor as nat;
        var r: nat := a - c * b;
        // by def
        assert r == a - c * b;
        // substitution
        assert r == a - cr.Floor * b;
        // substitution
        assert r == a - (ar / br).Floor * b;
        // substitution
        assert r == a - (a as real / b as real).Floor * b;
        // one line def

        //    assert r == a % b;
        r
    }

    lemma modAtoBshouldBeEqualToModAPlusBtimesMToB(a: nat, b: nat, m: nat)
       ensures mod(a, b) == mod(a + b * m, b);
       requires b > 0;
    {
        var ar: real := a as real;
        var br: real := b as real;
        var mr: real := m as real;
        var c1r: real := ar / br;
        var c2r: real := (ar + br * mr) / br;

        // proving that c2 == c1 + m
        // starting from the c2r def  .... trying to get the def of c1r plus something

        // by def
        assert c2r == (ar + br * mr) / br;

        // distributive 1 / b
        assert c2r == ar / br + br * mr / br;

        // commutative 
        assert c2r == ar / br + mr * br / br;

        // commutative
        assert c2r == ar / br + mr * (br / br);

        // definition of 1; v / v == 1
        assert br / br == 1.0;
        assert ar / br + mr * (br / br) ==
            ar / br + mr;

        // definition of 1; v * 1 == v
        assert c2r == ar / br + mr * 1.0 == ar / br + mr;

        // adding a integer to a number before floor should be equal
        // than adding the integer to the number after floor
        assert floor(ar / br) ==
            floor(ar / br + mr) - m;

        // use def of floor on  a / b + m
        assert floor(ar / br + mr) ==
            floor(ar / br) + m;

        // assert that floor of c1 real == c1
        var c1: nat := (ar / br).Floor as nat;
        assert c1 == c1r.Floor as nat;

        // assert that floor of c2 real == c2
        var c2: nat := floor(c2r) as nat;
        assert c2 == c2r.Floor as nat;
        assert c2 == c1 + m;
        // qed. c2 == c1 + m

        // now, we can go the the def of mod in both cases

        // assert that r1 matches the def of mod(a,b)
        var r1: nat := a - c1 * b;
        assert r1 == mod(a, b);

        // assert that r2 matches the def of mod(a + b * m, b)
        var r2: nat := (a + b * m) - c2 * b;

        // create new var x to reference a + b * m to reduce code
        var x: nat := a + b * m;
        var xr: real := x as real;
        assert xr == ar + br * mr;

        // by def 
        assert mod(x, b) == x - (xr / b as real).Floor * b;

        // substitute b as real to br 
        assert mod(x, b) == x - (xr / br).Floor * b;

        // floor is the same x / b and xr / br
        assert mod(x, b) == x - floor(x as real / br as real) * b;

        // substitute since c2 == c1 + m
        assert mod(x, b) == x - (c1 + m) * b;

        // distributive b
        assert mod(x, b) == x - (c1 * b + m * b);

        // distributive -1
        assert mod(x, b) == x - c1 * b - m * b;

        // since x == a + b * m
        assert mod(x, b) == a + b * m - c1 * b - b * m;

        // definition of zero; b * m - b * m == 0
        assert mod(x, b) == a - c1 * b + b * m - b * m == a - c1 * b;

        // substitute r2 by its def
        assert mod(x, b) == r2;

        // substitution; r2 == mod(a + b*m, b)
        assert mod(a + b * m, b) == mod(a, b);
        // qed.
    }

    ghost method testMod()
    {
        assert mod(4, 2) == 0;
        assert mod(5, 2) == 1;
        assert forall n: nat:: mod(n, 1) == 0;
        assert forall n: nat:: mod(2 * n, 2) == 0;
        assert forall n: nat:: mod(2 * n + 1, 2) == 1;
        assert forall n: nat:: mod(3 * n, 3) == 0;
        assert forall n: nat:: mod(3 * n + 1, 3) == 1;
        assert forall n: nat:: mod(3 * n + 2, 3) == 2;
    }

    lemma modIsAlwaysSmallThanListSize(a: nat, b: nat, m: nat, r: nat)
       requires b > 0;
       requires a == b * m + r;
       ensures mod(a, b) == mod(b * m + r, b);
       ensures mod(a, b) == r ==> r <= a;
    //    ensures mod(a, b) == r ==> r <= b;
    {
       var ar: real := a as real;
       var br: real := b as real;
       var cr: real := ar / br;
       var c: nat := cr.Floor as nat;
       // assert c as real >= cr;



       modAtoBshouldBeEqualToModAPlusBtimesMToB(r,b,m);
        // var ar: real := a as real;
        // var br: real := b as real;
        // var cr: real := ar / br;
        
        // var r: nat := a - c * b;
        // // by def
        // assert r == a - c * b;
    }

    lemma modNByNShouldBeZero(n: nat)
       requires n > 0;
       ensures mod(n, n) == 0;
    {
        var nr: real := n as real;

        // by definition
        assert mod(n, n) == n - (n as real / n as real).Floor * n;

        // substitutive; nr == n as real
        assert mod(n, n) == n - (nr / nr).Floor * n;

        // by definition of 1
        assert n / n == 1;
        assert nr / nr == 1 as real;
        assert(nr / nr).Floor == 1;

        // substitutive; sice nr / nr == 1.0;
        assert mod(n, n) == n - 1 * n;

        // definition of 1; 1 * n == n
        assert mod(n, n) == n - n;

        // defintion of zero n - n == 0;
        assert mod(n, n) == 0;
        // qed.
    }

    ghost method testmodNByNShouldBeZero(n: nat)
       requires n > 0;
    {
        modNByNShouldBeZero(n);
        assert mod(n, n) == 0;
    }

    lemma modNTimesMByNShouldBeZero(n: nat, m: nat)
       requires n > 0;
       ensures mod(n * m, n) == 0;
    {
        assert mod(0, n) == 0;
        modAtoBshouldBeEqualToModAPlusBtimesMToB(0, n, m);

        // qed
        assert mod(n * m, n) == 0;
    }

    ghost method testModNTimesMByNShouldBeZero(n: nat, m: nat)
        requires n > 0;
    {
        modNTimesMByNShouldBeZero(n, m);
        assert mod(n * m, n) == 0;
    }
}