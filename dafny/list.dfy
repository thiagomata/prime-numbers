module List {

    function sorted(list: seq<nat>): bool {
        var prev   := forall k : nat :: 1 <= k < |list| ==> list[k] > list[k-1];
        prev
    }

    lemma propertySorted(list: seq<nat>)
        requires sorted(list);
        ensures |list| > 0 ==> sorted(list[1..]);
        ensures |list| > 0 ==> sorted(list[..|list|-1]);
        ensures forall k :: 0 < k < |list| ==> list[0] < list[k];
        ensures forall k :: 0 <= k < |list| - 1 ==> last(list) > list[k];
    {
        if (|list| < 2 ) {
            assert forall k :: 0 < k < |list| ==> list[0] < list[k];
        } else {
            var min := list[0];
            assert min < list[1];
            propertySorted(list[1..]);
            var max := last(list);
            assert max > list[|list|-2];
            propertySorted(list[..|list|-1]);
        }
    }

    function nonZero(list: seq<nat>): bool
    {
        forall l: nat :: 0 <= l < |list| ==> list[l] > 0
    }

    function unique(list: seq<nat>): bool {
        forall n,m : nat :: 0 <= n < m < |list| ==> list[n] != list[m]
    }

    function first(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[0]
    }

    function last(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[|list|-1]
    }

    function method sum(list: seq<nat>): nat
        decreases |list|;
    {
        if (|list| == 0 ) then 0 else
        list[0] + sum(list[1..])
    }

    function method shift(list: seq<nat>):seq<nat>
    {
        if |list| == 0 then [] else
        list[1..] + [list[0]]
    }

    lemma shiftedProperties(list: seq<nat>, shifted: seq<nat>)
        requires shifted == shift(list);
        ensures forall k :: 1 <= k < |list| - 1 ==> shifted[k-1] == list[k];
        ensures |shifted| > 0 ==> shifted[|list|-1] == list[0];
        ensures |list| == |shifted|;
    {
        assert list == [] ==> shifted == [];
        if |list| > 0 {
            assert forall k :: 1 <= k < |list| - 1 ==> shifted[k-1] == list[k];
            assert shifted[|list|-1] == list[0];
        }
    }

    lemma singleSum(value: nat)
        ensures sum([value]) == value;
    {
    }

    ghost method distributiveSum(a: seq<nat>, b: seq<nat> )
        ensures sum(a + b) == sum(a) + sum(b); 
    {
        assert |a| == 0 && |b| == 0 ==> sum(a) + sum(b) == 0 == sum(a + b);
        assert |a|  > 0 && |b| == 0 ==> a + b == a;    
        assert |a|  > 0 && |b| == 0 ==> sum(a) + sum(b) == sum(a) + 0 == sum(a) == sum(a + b);
        assert |a| == 0 && |b|  > 0 ==> a + b == b;
        assert |a| == 0 && |b|  > 0 ==> sum(a) + sum(b) == sum(b) + 0 == sum(b) == sum( a + b);
        assert |a|  > 0 && |b|  > 0 ==> sum(a) + sum(b) == a[0] + sum(a[1..]) + b[0] + sum(b[1..]) == a[0] + b[0] + sum(a[1..]) + sum(b[1..]);
        assert |a|  > 0 && |b|  > 0 ==> a + b == [a[0]] + (a[1..] + b);
        assert |a|  > 0 && |b|  > 0 ==> sum(a + b) == sum([a[0]]) + sum(a[1..] + b);
    }

    lemma divSum(list: seq<nat>, n: nat)
        requires 0 <= n < |list|;
        ensures sum(list) == sum(list[0..n]) + sum(list[n..]); 
    {
        assert list[0..n] + list[n..] == list;
        var a := list[0..n];
        var b := list[n..];
        distributiveSum(a,b);
    }

    lemma sumListPlusValue(list: seq<nat>, value: nat)
        ensures sum(list) + value == sum([value] + list);
        ensures sum(list) + value == sum(list + [value]);
        ensures value + sum(list) == sum(list) + value;
    {
        assert sum(list) + value == sum([value] + list);
        var a := list;
        var b := [value];
        distributiveSum(a, b);
    }

     lemma sumPopLast(list: seq<nat>)
         requires |list| > 0;
         ensures sum(list) == list[|list|-1] + sum(list[..|list|-1]);
    {
        var last := list[|list|-1];
        var body := list[..|list|-1];
        assert body + [last] == list;
        sumListPlusValue(body, last);
        assert sum(list) == last + sum(body);
    }

     lemma sumPopFirst(list: seq<nat>)
         requires |list| > 0;
         ensures sum(list) == list[0] + sum(list[1..]);
    {
        var first := list[0];
        var body := list[1..];
        assert [first] + body == list;
        sumListPlusValue(body, first);
        assert sum(list) == first + sum(body);
    }

//    method Main() {
//        var l := [1,2,3];
//     //    print(l[|l|-1]);
//        print(l[..|l|-1]);
//     }
}