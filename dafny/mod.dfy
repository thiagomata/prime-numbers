/**
 * Define our own mod function ( since I could not proof that mod(a,b) == a % b)
 * Ensure some important properties into the mod function
 *  mod(0,n) == 0
 *  mod(n,1) == 0
 *  mod(n,n) == 0
 *  mod(m*n,n) == 0
 *  mod(a+m*n,n) == mod(a,n)
 *  mod(a,b) <= a
 *  mod(a,b) <= b
 */
module Mod {

    function method mod(a: nat, b: nat): nat
       requires b > 0;
       requires a >= 0;
       decreases a;
       ensures mod(a,b) <= a;
       ensures mod(a,b) <  b;
       ensures a == 0 ==> mod(a,b) == 0;
    {
        var remainder := if a >= b then mod( a-b, b) else a;

        assert a == 0 ==> remainder == 0;

        assert a >= b ==> remainder == mod(a-b,b);
        assert a >= b ==> remainder == mod(a-b,b) ==> remainder <= a;
        assert a == b ==> remainder == 0;
        assert a == b ==> remainder <= a;
        assert a <  b ==> remainder == a;
        assert a <  b ==> remainder <= a;
        assert b >  0 ==> remainder <= (a - b) ==> remainder <= a;
        assert remainder <= a;
        remainder
    }

    lemma modBtoBShouldBeZero(b: nat)
       requires b > 0;
       ensures mod(b ,b) == 0;
    {
        assert mod(b,b) == if ( b >= b ) then mod(b-b, b) else b;
        assert b >= b;
        assert mod(b,b) == mod(b-b, b);
        assert mod(b,b) == mod(0,b) == 0;
    }

    lemma modBto1ShouldBeB(b: nat)
       ensures mod(b, 1) == 0
    {
        assert mod(b, 1) == if b >= 1 then mod( b-1, 1) else b;
    }

    lemma modAtoBshouldBeEqualToModAPlusBtimesMToB(a: nat, b: nat, m: nat)
       ensures mod(a, b) == mod(a + b * m, b);
       requires b > 0;
       decreases m; 
       decreases a;
    {
        assert mod(b,b) == 0;
        assert mod(0,b) == 0;
        assert a == 0 ==> mod(a,b) == 0;
        assert a == 0 ==> mod(a + b * m, b) == mod(b * m, b);
        assert m == 1 ==> mod(b * m, b ) == mod(b,b) == 0;
        assert m >  1 ==> mod(b * m, b ) == if b * m >= b then mod( b*m - b, b) else b;
        assert m >  1 ==> mod(b * m, b ) == mod( b * m - b, b) == mod(b * (m-1),b);

        var x := a + b * m;
        assert mod(x, b) == mod((a + b * m), b);
        assert mod(x, b) == if x >= b then mod(x-b, b) else x;
        assert x == ( a + b * m);
        assert x - b == (a + b * m ) - b == a + b * m - b == a + b * ( m - 1);
        assert mod(x, b) == if ( a + b * m ) >= b then mod(a + b * m - b, b) else a + b * m;
        assert m == 1 ==> mod(x,b) == if ( a + b ) >= b then mod(a + b - b, b) else a + b * m;
        assert m == 1 ==> mod(x,b) == if ( a + b ) >= b then mod(a, b) else a + b;
        
        assert a >  0 ==> ( a + b ) > b;
        assert m == 1 && a  > 0 ==> mod(x,b) == mod(a,b);

        assert m > 1  ==> a + b * m > b;
        assert m > 1  ==> mod(x,b) == mod(a + b * m - b, b) == mod(x-b,b);
        assert m > 1  ==> mod(a + b * m,b) == mod(a + b * (m - 1), b);
        assert m > 1  ==> mod(a + b * m,b) == mod(a, b);
        // qed.
    }

    lemma modAtoBShouldBeEqualModAplusBtoB(a: nat, b: nat)
        requires a > b;
        requires b > 0;
        ensures mod(a,b) == mod(a-b,b);
    {
        var v := a - b;
        assert v > 0;
        var m := 1;
        modAtoBshouldBeEqualToModAPlusBtimesMToB(v,b,1);
    }

    lemma modATimesBModBZero(a: nat, b: nat)
        requires b > 0;
        ensures mod(a*b, b) == 0;
        ensures mod(b*a, b) == 0;
    {
        modAtoBshouldBeEqualToModAPlusBtimesMToB(0, b, a);
        assert mod(a*b,b) == mod(b,b);
        modBtoBShouldBeZero(b);
        assert mod(b,b) == 0;
        assert mod(a*b,b) == 0;
    }


    lemma remainderShouldBeSmall (a: nat, b: nat, r: nat) 
        requires b > 0;
        requires r == mod(a,b);
        ensures mod(a,b) == r <= a;
        ensures mod(a,b) == r < b;
    {

    }

    function method cyclePos(list: seq<nat>, pos: nat): nat
        requires |list| > 0;
    {
        var l := |list|;
        var k := mod(pos, l);
        remainderShouldBeSmall(pos,l,k);
        assert k < l;
        var result := list[k];
        result
    }

    lemma checkCyclePos(list: seq<nat>, pos: nat, key: nat, result: nat)
        requires |list| > 0;
        requires key == mod(pos,|list|);
        requires result == cyclePos(list, pos);
        ensures key < |list|;
        ensures result == list[key];
    {
        remainderShouldBeSmall(pos,|list|,key);
    }

    method cycle(source: seq<nat>, size: nat) returns (result: seq<nat>)
        requires |source| > 0;
        ensures forall k : nat :: 0 <= k < |result| ==> mod(k,|source|) < |source|;
        ensures forall k : nat :: 0 <= k < |result| ==> result[k] == source[mod(k,|source|)];
        ensures |result| == size;
    {
        result := [];   
        while( |result| < size ) 
            invariant forall k : nat :: 0 <= k < |result| ==> result[k] == source[mod(k,|source|)];
            invariant |result| <= size;
            decreases size - |result|;
        {
            var value := cyclePos(source, |result|);            
            result := result + [value];
        }
        assert |result| == size;
    }

    method checkCycle(source: seq<nat>, m: nat)
        requires |source| > 0;
        requires m > 0;
    {
        var dest := cycle( source, |source| * m);
        assert |dest| == |source| * m;
        assert forall k: nat :: 0 <= k < |source|  ==> dest[k] == source[k];
        assert forall k: nat :: |source| <= k  < |dest|  ==> mod(k,|source|) < |source|;
        assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == source[mod(k,|source|)];
        assert forall k: nat :: |source| <= k  < |dest|  ==> dest[k] == dest[k-|source|];
    }

    ghost method testMod()
    {
        assert mod(4, 2) == 0;
        assert mod(5, 2) == 1;
    }

    ghost method testMod2(n: nat)
        ensures mod(2*n, 2) == 0;
        ensures mod(0, n + 1) == 0;
        ensures mod(n, 1) == 0;
        ensures mod(2*n, 2) == 0;
        ensures mod(2 * n + 1, 2) == mod(1,2);
        ensures mod(3 * n, 3) == 0;
        ensures mod(3 * n + 1, 3) == mod(1,3) == 1;
    {
        modBto1ShouldBeB(n);
        assert mod(n, 1) == 0;

        modATimesBModBZero(n,2);
        assert mod(2*n, 2) == 0;

        modAtoBshouldBeEqualToModAPlusBtimesMToB(1, 2, n);
        assert mod(2 * n + 1, 2) == mod(1,2);
        
        modATimesBModBZero(n, 3);
        assert mod(3 * n, 3) == 0;

        modAtoBshouldBeEqualToModAPlusBtimesMToB(1, 3, n);
        assert mod(3 * n + 1, 3) == mod(1,3) == 1;
    }

    method Main()
    {
        print("\ntesting mod\n");
        testMod();
        testMod2(123);
        print("\n:D\n");
    }
}