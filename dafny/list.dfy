module List {

    function method countWithValue(list: seq<nat>, value: nat): nat 
        decreases |list|;        
    {
        if |list| == 0 then 0 else
        if list[0] == value then 1 + countWithValue(list[1..],value) else
        countWithValue(list[1..],value)
    }

    lemma notFoundShouldReturnZero(list: seq<nat>, value: nat)
        requires forall k : nat :: 0 <= k < |list| ==> list[k] != value;
        ensures countWithValue(list, value) == 0;
    {
        if ( |list| == 0 ) {
            assert countWithValue(list,value) == 0;
        } else if |list| == 1 {
            assert list[0] != value;
            assert countWithValue(list, value) == 0;
        } else {
            var head := [list[0]];
            var tail := list[1..];
            assert forall k : nat :: 0 <= k < |tail| ==> tail[k] != value;
            distributiveCount(head,tail, value);
            assert list[0] != value;
            assert countWithValue(head,value) == 0;
            assert countWithValue(list,value) == countWithValue(head,value) + countWithValue(tail,value);
            notFoundShouldReturnZero(tail,value);
        }
    }

    lemma distributiveCount(listA: seq<nat>, listB: seq<nat>, value: nat)
        ensures countWithValue(listA, value) + countWithValue(listB, value) == countWithValue(listA + listB, value);
    {
        var a := listA;
        var b := listB;
        if ( |a| == 0 && |b| == 0 ) {
            assert a + b == [];
            assert countWithValue(a, value) + countWithValue(b, value) == 0;
            assert countWithValue(a + b, value) == 0;
            assert countWithValue(a, value) + countWithValue(b, value) == countWithValue(a + b, value);
        }
        if (|a|  > 0 && |b| == 0) {
            assert a + b == a;
            assert  countWithValue(a, value) + countWithValue(b, value) == 
                    countWithValue(a, value) + 0 == countWithValue(a, value) == 
                    countWithValue(a + b, value);
        }
        if (|a|  == 0 && |b| > 0) {
            assert a + b == b;
            assert  countWithValue(a, value) + countWithValue(b, value) == 
                    0 + countWithValue(b, value) == countWithValue(b, value) == 
                    countWithValue(a + b, value);
        }
        if ( |a| > 0 && |b| > 0 ) {
            var topA := 0;
            if ( a[0] == value ) {
                topA := 1;
            }
            assert 
                countWithValue(a, value) + countWithValue(b, value) == 
                topA + countWithValue(a[1..],value) + countWithValue(b,value);

            assert a + b == [a[0]] + (a[1..] + b);
            assert countWithValue(a + b, value) == countWithValue([a[0]], value) + countWithValue(a[1..] + b, value);
            if ( a[0] == value ) {
                assert countWithValue(a + b, value) == 1 + countWithValue(a[1..] + b, value);
            } else {
                assert countWithValue(a + b, value) == 0 + countWithValue(a[1..] + b, value);
                assert countWithValue(a + b, value) == countWithValue(a[1..] + b, value);
            }
            distributiveSum(a[1..],b);
        }
    }

    lemma appendCount(list: seq<nat>, value: nat, next: nat)
        ensures value == next ==> countWithValue([next] + list, value) == 1 + countWithValue(list, value);
        ensures value == next ==> countWithValue(list + [next], value) == countWithValue(list, value) + 1;
        ensures value != next ==> countWithValue([next] + list, value) == countWithValue(list, value);
        ensures value != next ==> countWithValue(list + [next], value) == countWithValue(list, value);
    {
        var resultNext: nat;
        if ( value == next ) {
            resultNext := 1;
        } else {
            resultNext := 0;
        }
        assert countWithValue([next],value) == resultNext;
        distributiveCount(list, [next], value);
        assert countWithValue(list + [next],value) == countWithValue(list,value) + countWithValue([next],value);
        assert countWithValue(list + [next],value) == countWithValue(list,value) + resultNext;
        distributiveCount([next], list, value);
        assert countWithValue([next] + list,value) == countWithValue([next],value) + countWithValue(list,value);
        assert countWithValue([next] + list,value) == resultNext + countWithValue(list,value);
    }

    function method sorted(list: seq<nat>): bool {
        var prev   := forall k : nat :: 1 <= k < |list| ==> list[k] > list[k-1];
        prev
    }

    function method sortedDesc(list: seq<nat>): bool {
        var prev   := forall k : nat :: 1 <= k < |list| ==> list[k] < list[k-1];
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

    function method nonZero(list: seq<nat>): bool
    {
        forall l: nat :: 0 <= l < |list| ==> list[l] > 0
    }

    function method unique(list: seq<nat>): bool {
        forall n,m : nat :: 0 <= n < m < |list| ==> list[n] != list[m]
    }

    function method first(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[0]
    }

    function method last(list: seq<nat>): nat 
        requires |list| > 0;
    {
        list[|list|-1]
    }

    function method max(list: seq<nat>): nat
        requires |list| > 0;
        ensures forall k :: 0 <= k < |list| ==> max(list) >= list[k];
        ensures max(list) in list;
    {
        var prev := if |list| == 1 then list[0] else max(list[1..]);

        if |list| == 1 then list[0]
        else if prev > list[0] then prev
        else list[0] 
    }

    lemma maxSumList(listA: seq<nat>, listB: seq<nat>)
        requires |listA| > 0;
        requires |listB| > 0; 
        ensures max(listA + listB) >= max(listA);
        ensures max(listA + listB) >= max(listB);
        ensures max(listA) > max(listB) ==> max(listA + listB) == max(listA);
        ensures max(listB) > max(listA) ==> max(listA + listB) == max(listB);
        ensures max(listA + listB) >= max(listB + listA);
    {
        var maxA := max(listA);
        var maxB := max(listB);
        var listAB := listA + listB;
        assert maxA in listA;
        assert maxB in listB;
        assert forall k :: 0 <= k < |listA| ==> listA[k] in listAB;
        assert forall k :: 0 <= k < |listB| ==> listB[k] in listAB;
        assert maxA > maxB ==> max(listAB) == maxA;
        assert maxB > maxA ==> max(listAB) == maxB;
    }

    function method min(list: seq<nat>): nat
        requires |list| > 0;
        ensures forall k :: 0 <= k < |list| ==> min(list) <= list[k]
    {
        var prev := if |list| == 1 then list[0] else min(list[1..]);

        if |list| == 1 then list[0]
        else if prev < list[0] then prev
        else list[0] 
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