module List {

    function sorted(list: seq<nat>): bool {
        forall k : nat :: 1 <= k < |list| ==> list[k] > list[k-1]
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

     lemma sumPop(list: seq<nat>)
         requires |list| > 0;
         ensures sum(list) == list[|list|-1] + sum(list[..|list|-1]);
    {
        var last := list[|list|-1];
        var body := list[..|list|-1];
        assert body + [last] == list;
        sumListPlusValue(body, last);
        assert sum(list) == last + sum(body);
    }

//    method Main() {
//        var l := [1,2,3];
//     //    print(l[|l|-1]);
//        print(l[..|l|-1]);
//     }
}