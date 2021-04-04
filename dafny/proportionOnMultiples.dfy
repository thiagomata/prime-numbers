include "modDiv.dfy"
include "list.dfy"
include "cycle.dfy"
include "multiple.dfy"

module ProportionOnMultiples {

    import ModDiv
    import List
    import Multiple
    import Cycle

    lemma proportionOnCycleBottomLimit(list: seq<nat>, start: nat, end: nat, searchValue: nat)
        requires end  > 0;
        requires start < end;
        requires |list| > 0;
        // ensures List.countWithValue(Cycle.cycle(list, end)[start..],searchValue) <= List.countWithValue(list,searchValue) + 2;
        // ensures List.countWithValue(afterCycle[..start],searchValue) >=
        //         List.countWithValue(list,searchValue) * ( ModDi.div(start,|list|) - 1 );
        // ensures List.countWithValue(afterCycle[..start],searchValue) <=
        //         List.countWithValue(list,searchValue) * ( ModDi.div(start,|list|) - 1 );

    {
        var l := List.countWithValue(list,searchValue);

        /* define the after top, the min mulitple value just after the end */
        var afterEnd := |list|;
        var m := 1;
        while ( afterEnd < end ) 
            decreases end - afterEnd;
            invariant afterEnd == m * |list|;
            invariant afterEnd - |list| < end;
        {
            afterEnd := afterEnd + |list|;
            m := m + 1;
        }
        assert afterEnd == m * |list|;
        assert end <= afterEnd;
        assert afterEnd - |list| < end;
        assert m * |list| - |list| <= end <= m * |list|;
        assert ( m  - 1 ) * |list| <= end <= m * |list|;
        var beforeEnd := afterEnd - |list|;
        assert beforeEnd <= end;
        assert beforeEnd + |list| == afterEnd - |list| + |list|;
        assert beforeEnd + |list| == afterEnd;
        assert afterEnd >= end;
        assert beforeEnd + |list| >= end;
        assert afterEnd == m * |list|;
        assert beforeEnd == ( m - 1 ) * |list| <= end;
        var rEnd := end - beforeEnd;
        assert beforeEnd + rEnd == end;
        assert beforeEnd == ( m - 1 ) * |list|;
        if ( afterEnd == end ) {
            assert ModDiv.isModDiv(end, |list|, m, 0);
        } else {
            assert afterEnd > end;
            assert beforeEnd <= end;            
            assert ModDiv.isModDiv(end, |list|, m - 1, rEnd);
        }

        // /* define before top, the max multiple value before the end */
        // var beforeEnd := (m - 1) * |list|;
        // assert beforeEnd <= end <= afterEnd;

        /* define the after start, the min multiple value just after the end */
        var n := 0;
        var afterStart := 0;
        while ( afterStart <= start )
            decreases start - afterStart;
            invariant afterStart == n * |list|;
            invariant afterStart - |list| <= start;
            invariant afterStart - |list| < end;
        {
            afterStart := afterStart + |list|;
            n := n + 1;
        }
        assert afterStart > start;
        var beforeStart := afterStart - |list|;
        assert beforeStart <= start;
        /* define before start, the max multiple value before the start */
        assert beforeStart + |list| == afterStart - |list| + |list|;
        assert beforeStart + |list| == afterStart;
        assert beforeStart + |list| > start;
        assert afterStart == n * |list|;
        assert beforeStart == ( n - 1 ) * |list|;
        var rStart := start - beforeStart;
        assert ModDiv.isModDiv(start, |list|, n - 1, rStart);

        assert start < end;
        assert (n - 1) * |list| <= start < end <= m * |list|;
        assert (n - 1) * |list| < m * |list|;
        assert (n - 1) < m;
        assert n <= m;

        assert n * |list| <= m * |list|;
        assert afterStart <= afterEnd;
        assert n * |list| - |list| <= m * |list| - |list|;
        assert beforeStart <= beforeEnd;
        assert beforeStart <   afterStart <= afterEnd;
        assert beforeStart <=  beforeEnd  <  afterEnd;

        var afterCycle := Cycle.cycle(list, afterEnd);
        assert Cycle.isCycle(list, afterCycle);
        Cycle.cycleAlwaysRepeatTheSameValues(list,afterCycle);
        assert |afterCycle| == afterEnd;
        assert afterEnd - beforeEnd == |list|;
        assert beforeEnd < end;
        assert |afterCycle[end..]| < |list|;
        
        // /* we can define the proportion of the value in the perfect after cycle */
        Cycle.proportionOnPerfectCycle(list, m, searchValue);
        assert List.countWithValue(afterCycle,searchValue) == l * m;

        if ( n == 0 ) {
            assert start == 0; 
            assert |afterCycle[..start]| == 0;
            assert List.countWithValue(afterCycle[..start], searchValue) == 0;
            assert List.countWithValue(afterCycle[..start],searchValue) <= l * n;
        } 
        else if ( n == 1 ) {
            assert beforeStart == (n - 1) * |list| == 0;
            assert afterStart == n  * |list| == |list|;
            assert |afterCycle| == afterEnd;
            assert afterEnd >= afterStart;
            assert |afterCycle| >= afterStart;
            var afterStartCycle  := Cycle.cycle(list, afterStart);
            var beforeStartCycle := Cycle.cycle(list, beforeStart);
            Cycle.cycleAlwaysRepeatTheSameValues(list,afterStartCycle);
            Cycle.proportionOnPerfectCycle(list, n, searchValue);
            assert |beforeStartCycle| == 0;
            assert |afterStartCycle| == |list|;
            assert afterStartCycle == list;
            assert List.countWithValue(afterStartCycle,searchValue) == l;
            assert afterStartCycle[..afterStart] == afterStartCycle;
            assert afterStartCycle[..afterStart] == afterCycle[..afterStart];
            assert afterStart > start;
            assert afterCycle[..afterStart] == afterCycle[..start] + afterCycle[start..afterStart];
            List.countWithValueSum(afterCycle[..afterStart],start,searchValue);
            assert List.countWithValue(afterCycle[..afterStart], searchValue) == 
                List.countWithValue(afterCycle[..start], searchValue) +
                List.countWithValue(afterCycle[start..afterStart], searchValue);
            assert List.countWithValue(afterCycle[..afterStart], searchValue) == 
                List.countWithValue(afterStartCycle, searchValue);
            assert l == List.countWithValue(afterStartCycle, searchValue) == 
                List.countWithValue(afterCycle[..start], searchValue) +
                List.countWithValue(afterCycle[start..afterStart], searchValue);
            assert l == 
                List.countWithValue(afterCycle[..start], searchValue) +
                List.countWithValue(afterCycle[start..afterStart], searchValue);
            assert l - List.countWithValue( afterCycle[start..afterStart], searchValue) == 
                List.countWithValue(afterCycle[..start], searchValue);
            assert List.countWithValue(afterCycle[start..afterStart], searchValue) >= 0;
            assert List.countWithValue(afterCycle[..start], searchValue) <= l; 
            assert List.countWithValue(afterCycle[..start], searchValue) <= l * n;
        } 
        // else {
        //     assert n > 1;
        //     assert (n - 1) > 0;
        //     assert |list| > 0;
            
        //     assert afterStart  == (n) * |list|;
        //     assert beforeStart == (n - 1) * |list|;
        //     assert ( n - 1 ) > 0;
        //     assert |list| > 0;
        //     assert ( n - 1 ) * |list| > 0;
        //     assert beforeStart > 0;

        //     var afterStartCycle  := Cycle.cycle(list, afterStart);
        //     var beforeStartCycle := Cycle.cycle(list, beforeStart);
        //     assert Cycle.isCycle(list, afterStartCycle);
        //     assert Cycle.isCycle(list, beforeStartCycle);
        //     assert |afterStartCycle|  == afterStart;
        //     assert |beforeStartCycle| == beforeStart;
        //     assert |afterCycle| >= afterStart;
        //     assert afterCycle[..afterStart] == afterStartCycle;
        //     assert beforeStart < afterStart;
        //     assert afterStartCycle[..beforeStart] + afterStartCycle[beforeStart..] ==  afterStartCycle;
        //     assert beforeStartCycle == afterStartCycle[..beforeStart];

        //     /* we can define the proportion of the value in the perfect after cycle */
        //     Cycle.proportionOnPerfectCycle(list, n, searchValue);
        //     Cycle.proportionOnPerfectCycle(list, n - 1, searchValue);
        //     assert List.countWithValue(afterStartCycle,searchValue)  == l * n;
        //     assert List.countWithValue(beforeStartCycle,searchValue) == l * ( n - 1);

        //     /* count from before start until start */
        //     List.countWithValueSum(afterStartCycle[beforeStart..],start,searchValue);
        //     assert List.countWithValue( afterStartCycle[beforeStart..], searchValue) == 
        //         List.countWithValue(    afterStartCycle[beforeStart..start], searchValue) +
        //         List.countWithValue(    afterStartCycle[start..], searchValue);
        //     /* count in afterStartCycle[beforeStart..] is count on list times n */
        //     assert l == 
        //         List.countWithValue(afterStartCycle[beforeStart..start],searchValue) +
        //         List.countWithValue(afterStartCycle[start..],searchValue);
        //     assert List.countWithValue(afterStartCycle[beforeStart..start],searchValue) <= l;
        //     /* count from before start until after start */
        //     assert List.countWithValue(afterStartCycle[start..],searchValue) <= l;
        //     /* since afterCycle contains afterStartCycle */
        //     assert List.countWithValue(afterCycle[start..afterStart],searchValue) <= l;

        //     // IMPORTANT
        //     assert List.countWithValue(beforeStartCycle,searchValue) == l * ( n - 1);

        //     List.countWithValueSum(afterCycle[..start],beforeStart,searchValue);
        //     assert List.countWithValue(afterCycle[..start],searchValue) == 
        //         List.countWithValue(afterCycle[..beforeStart],searchValue) +
        //         List.countWithValue(afterCycle[beforeStart..start],searchValue);
        //     assert List.countWithValue(afterCycle[..start],searchValue) == 
        //         l * ( n - 1 ) +
        //         List.countWithValue(afterCycle[beforeStart..start],searchValue);
        //     assert List.countWithValue(afterCycle[..start],searchValue) >=
        //         l * ( n - 1 );
        //     assert List.countWithValue(afterCycle[..start],searchValue) <=
        //         l * n;
        // }
        // List.countWithValueSum(afterCycle[..end],start,searchValue);
        // assert List.countWithValue(afterCycle[..end],searchValue) == 
        //     List.countWithValue(afterCycle[..end],searchValue) +
        //     List.countWithValue(afterCycle[start..end],searchValue);

        // assert List.countWithValue(afterCycle[start..end],searchValue) ==
        //     List.countWithValue(afterCycle[..end],searchValue) -
        //     List.countWithValue(afterCycle[..start],searchValue);

    }


    // lemma proportionOnCycle(list: seq<nat>, start: nat, end: nat, searchValue: nat)
    //     requires end  > 0;
    //     requires start < end;
    //     requires |list| > 0;
    //     // ensures List.countWithValue(Cycle.cycle(list, end)[start..],searchValue) <= List.countWithValue(list,searchValue) + 2;
    // {
    //     var l := List.countWithValue(list,searchValue);
    //     /* define the after top, the min mulitple value just after the end */
    //     var afterEnd := |list|;
    //     var m := 1;
    //     while ( afterEnd < end ) 
    //         decreases end - afterEnd;
    //         invariant afterEnd == m * |list|;
    //         invariant afterEnd - |list| < end;
    //     {
    //         afterEnd := afterEnd + |list|;
    //         m := m + 1;
    //     }
    //     assert afterEnd == m * |list|;
    //     assert end <= afterEnd;
    //     assert afterEnd - |list| < end;
    //     assert m * |list| - |list| <= end <= m * |list|;
    //     assert ( m  - 1 ) * |list| <= end <= m * |list|;

    //     /* define before top, the max multiple value before the end */
    //     var beforeEnd := (m - 1) * |list|;
    //     assert beforeEnd <= end <= afterEnd;

    //     /* define the after start, the min multiple value just after the end */
    //     var n := 0;
    //     var afterStart := 0;
    //     while ( afterStart < start )
    //         decreases start - afterStart;
    //         invariant afterStart == n * |list|;
    //         invariant afterStart - |list| <= start;
    //         invariant afterStart - |list| < end;
    //     {
    //         afterStart := afterStart + |list|;
    //         n := n + 1;
    //     }
    //     assert afterStart == n * |list|;
    //     assert afterStart - |list| <= start;
    //     assert (n * |list|) - |list| <= start;
    //     assert (n - 1) * |list| <= start;
    //     assert start <= afterStart;
    //     assert (n - 1) * |list| <= start <= n * |list|;

    //     /* define before start, the max multiple value before the start */
    //     var beforeStart := (n - 1) * |list|;

    //     assert start < end;
    //     assert (n - 1) * |list| <= start < end <= m * |list|;
    //     assert (n - 1) * |list| < m * |list|;
    //     assert (n - 1) < m;
    //     assert n <= m;
    //     assert n * |list| <= m * |list|;
    //     assert afterStart <= afterEnd;
    //     assert n * |list| - |list| <= m * |list| - |list|;
    //     assert beforeStart <= beforeEnd;
    //     assert beforeStart <   afterStart <= afterEnd;
    //     assert beforeStart <=  beforeEnd  <  afterEnd;

    //     var afterCycle := Cycle.cycle(list, afterEnd);
    //     assert Cycle.isCycle(list, afterCycle);
    //     // Cycle.cycleAlwaysRepeatTheSameValues(list,afterCycle);
    //     assert |afterCycle| == afterEnd;
    //     assert afterEnd - beforeEnd == |list|;
    //     assert beforeEnd < end;
    //     assert |afterCycle[end..]| < |list|;
        
    //     /* we can define the proportion of the value in the perfect after cycle */
    //     Cycle.proportionOnPerfectCycle(list, m, searchValue);
    //     assert List.countWithValue(afterCycle,searchValue) == l * m;

    //     if ( n == 0 ) {
    //         assert start == 0; 
    //         assert |afterCycle[..start]| == 0;
    //         assert List.countWithValue( afterCycle[..start], searchValue) == 0;
    //     } else if ( n == 1 ) {
    //         assert afterStart == n * |list| == |list|;
    //         assert beforeStart == 0;
    //         assert List.countWithValue(afterCycle[..afterStart],searchValue)  == l;
    //         List.countWithValueSum(afterCycle[..afterStart],start,searchValue);
    //         assert List.countWithValue( afterCycle[..afterStart], searchValue) == 
    //             List.countWithValue(    afterCycle[..start], searchValue) +
    //             List.countWithValue(    afterCycle[start..afterStart], searchValue);
    //         assert l == 
    //             List.countWithValue(    afterCycle[..start], searchValue) +
    //             List.countWithValue(    afterCycle[start..afterStart], searchValue);
    //         assert List.countWithValue(    afterCycle[..start], searchValue) <= l;
    //     } else {
    //         assert n > 1;
    //         assert (n - 1) > 0;
    //         assert |list| > 0;
            
    //         assert afterStart  == (n) * |list|;
    //         assert beforeStart == (n - 1) * |list|;
    //         assert ( n - 1 ) > 0;
    //         assert |list| > 0;
    //         assert ( n - 1 ) * |list| > 0;
    //         assert beforeStart > 0;

    //         var afterStartCycle  := Cycle.cycle(list, afterStart);
    //         var beforeStartCycle := Cycle.cycle(list, beforeStart);
    //         assert Cycle.isCycle(list, afterStartCycle);
    //         assert Cycle.isCycle(list, beforeStartCycle);
    //         assert |afterStartCycle|  == afterStart;
    //         assert |beforeStartCycle| == beforeStart;
    //         assert |afterCycle| >= afterStart;
    //         assert afterCycle[..afterStart] == afterStartCycle;
    //         assert beforeStart < afterStart;
    //         assert afterStartCycle[..beforeStart] + afterStartCycle[beforeStart..] ==  afterStartCycle;
    //         assert beforeStartCycle == afterStartCycle[..beforeStart];

    //         /* we can define the proportion of the value in the perfect after cycle */
    //         Cycle.proportionOnPerfectCycle(list, n, searchValue);
    //         Cycle.proportionOnPerfectCycle(list, n - 1, searchValue);
    //         assert List.countWithValue(afterStartCycle,searchValue)  == l * n;
    //         assert List.countWithValue(beforeStartCycle,searchValue) == l * ( n - 1);

    //         /* count from before start until start */
    //         List.countWithValueSum(afterStartCycle[beforeStart..],start,searchValue);
    //         assert List.countWithValue( afterStartCycle[beforeStart..], searchValue) == 
    //             List.countWithValue(    afterStartCycle[beforeStart..start], searchValue) +
    //             List.countWithValue(    afterStartCycle[start..], searchValue);
    //         /* count in afterStartCycle[beforeStart..] is count on list times n */
    //         assert l == 
    //             List.countWithValue(afterStartCycle[beforeStart..start],searchValue) +
    //             List.countWithValue(afterStartCycle[start..],searchValue);
    //         assert List.countWithValue(afterStartCycle[beforeStart..start],searchValue) <= l;
    //         /* count from before start until after start */
    //         assert List.countWithValue(afterStartCycle[start..],searchValue) <= l;
    //         /* since afterCycle contains afterStartCycle */
    //         assert List.countWithValue(afterCycle[start..afterStart],searchValue) <= l;

    //         // IMPORTANT
    //         assert List.countWithValue(beforeStartCycle,searchValue) == l * ( n - 1);

    //         List.countWithValueSum(afterCycle[..start],beforeStart,searchValue);
    //         assert List.countWithValue(afterCycle[..start],searchValue) == 
    //             List.countWithValue(afterCycle[..beforeStart],searchValue) +
    //             List.countWithValue(afterCycle[beforeStart..start],searchValue);
    //         assert List.countWithValue(afterCycle[..start],searchValue) == 
    //             l * ( n - 1 ) +
    //             List.countWithValue(afterCycle[beforeStart..start],searchValue);
    //         assert List.countWithValue(afterCycle[..start],searchValue) >=
    //             l * ( n - 1 );
    //         assert List.countWithValue(afterCycle[..start],searchValue) <=
    //             l * n;
    //     }
    //     List.countWithValueSum(afterCycle[..end],start,searchValue);
    //     assert List.countWithValue(afterCycle[..end],searchValue) == 
    //         List.countWithValue(afterCycle[..end],searchValue) +
    //         List.countWithValue(afterCycle[start..end],searchValue);

    //     assert List.countWithValue(afterCycle[start..end],searchValue) ==
    //         List.countWithValue(afterCycle[..end],searchValue) -
    //         List.countWithValue(afterCycle[..start],searchValue);

    //     if ( m == 1 ) {
    //         assert end <= |list|;
    //         assert list[..end] + list[end..] == list;
    //         List.distributiveCount(list[..end],list[end..],searchValue);
    //         assert l ==
    //             List.countWithValue(list[..end],searchValue) +
    //             List.countWithValue(list[end..],searchValue);
    //         /* upper bound */
    //         assert List.countWithValue(list[..end],searchValue) <=
    //             l;
    //     } else {
    //         /* before cycle and after cycle are related */
    //         var afterStartCycle := Cycle.cycle(list, beforeEnd);
    //         assert Cycle.isCycle(list, afterStartCycle);
    //         assert Cycle.isCycle(list, afterCycle);
    //         Cycle.cycleByConcat(list, afterCycle, afterStartCycle, m);
    //         assert afterCycle[..beforeEnd] == afterStartCycle;

    //         // /* we can define the proportion of the value in the perfect before top cycle */
    //         Cycle.proportionOnPerfectCycle(list, m - 1, searchValue);
    //         assert List.countWithValue(afterStartCycle,searchValue) == l * ( m - 1 );

    //         /* we can break down the after cycle in before and after the beforeEnd */
    //         assert |afterCycle| > beforeEnd;
    //         assert afterCycle[..beforeEnd] + afterCycle[beforeEnd..] == afterCycle;
    //         List.distributiveCount(afterCycle[..beforeEnd],afterCycle[beforeEnd..],searchValue);
    //         assert List.countWithValue(afterCycle,searchValue) == 
    //             List.countWithValue(afterCycle[..beforeEnd],searchValue) +
    //             List.countWithValue(afterCycle[beforeEnd..],searchValue);

    //         /* we can break down the after cycle in before and after the end */
    //         assert |afterCycle| >= end;
    //         assert afterCycle[..end] + afterCycle[end..] == afterCycle;
    //         List.distributiveCount(afterCycle[..end],afterCycle[end..],searchValue);
    //         assert List.countWithValue(afterCycle,searchValue) == 
    //             List.countWithValue(afterCycle[..end],searchValue) +
    //             List.countWithValue(afterCycle[end..],searchValue);
            
    //         /* we can proof that in the last bite of the after cycle we have
    //          * the same count as in the list */
    //         assert l * m == 
    //             List.countWithValue(afterStartCycle,searchValue) +
    //             List.countWithValue(afterCycle[beforeEnd..],searchValue);
    //         assert l * m == 
    //             l * ( m - 1 ) +
    //             List.countWithValue(afterCycle[beforeEnd..],searchValue);
    //         assert l == List.countWithValue(afterCycle[beforeEnd..],searchValue);

    //         /* the last slice between beforeEnd and the end will have equal or less elements
    //          * than the list */
    //         assert afterCycle[beforeEnd..end] + afterCycle[end..] == afterCycle[beforeEnd..];
    //         List.distributiveCount(afterCycle[beforeEnd..end],afterCycle[end..],searchValue);
    //         assert List.countWithValue(afterCycle[beforeEnd..],searchValue) == 
    //             List.countWithValue(afterCycle[beforeEnd..end],searchValue) +
    //             List.countWithValue(afterCycle[end..],searchValue);
    //         assert l == 
    //             List.countWithValue(afterCycle[beforeEnd..end],searchValue) +
    //             List.countWithValue(afterCycle[end..],searchValue);

    //         /* partial slice after beforeEnd and before the end has size equal or less the count in the list */
    //         assert List.countWithValue(afterCycle[beforeEnd..end],searchValue) <= l;

    //         assert afterCycle[..beforeEnd] + afterCycle[beforeEnd..end] == afterCycle[..end];
    //         List.distributiveCount(afterCycle[..beforeEnd],afterCycle[beforeEnd..end],searchValue);
    //         assert List.countWithValue(afterCycle[..end],searchValue) == 
    //             List.countWithValue(afterCycle[..beforeEnd],searchValue) +
    //             List.countWithValue(afterCycle[beforeEnd..end],searchValue);

    //         assert List.countWithValue(afterCycle[..end],searchValue) == 
    //             l * ( m - 1 ) +
    //             List.countWithValue(afterCycle[beforeEnd..end],searchValue);

    //         /* upper bounder */
    //         assert List.countWithValue(afterCycle[..end],searchValue) >= 
    //             l * ( m - 1);

    //         assert List.countWithValue(afterCycle[..end],searchValue) <= 
    //             l * m;
    //     }

    //     assert List.countWithValue(afterCycle[..end],searchValue) <= 
    //         l * m;

    //     assert List.countWithValue(afterCycle[..start],searchValue) >=
    //         l * ( n - 1 );

    //     assert List.countWithValue(afterCycle[start..end],searchValue) >=
    //         l * ( m - 1) -
    //         l * ( n );
    // }

//     lemma numberOfMultiplesOfSomeValue( value: nat, start: nat, end: nat, list: seq<nat>, filtered: seq<nat>, modList: seq<nat>)
//         requires value > 0;
//         requires isPrime(value);
//         requires end > start;
//         requires end > 0;
//         requires ModDiv.isModListFromValue(value, modList);
//         requires |list| == end - start;
//         requires forall k :: 0 <= k < |list| ==> list[k] == start + k;
//         requires |modList| == end;
//         requires |modList| > 0;
//         requires |modList| > value;
//         requires Multiple.isFilterMultiples(list,value,filtered);
// //        // ensures |filtered| <= (|list| / value) - 1;
//         // ensures |filtered| >= (|list| / value) + 1;
//     {
//         // ensure that the proportion of multiples is the same from 0 .. last slice
//         // ensure that last slice is small than cycle
//         // ensure that the max of multiples in the last slice is 1, min 0
//         // ensure that the proportion of multiples is the same from 0 .. first slice
//         // ensure that firs slice is small than cycle
//         // ensure that the max of multiples in the first slice is 1, min  0
//         // proportion max is value - 0 + 1
//         // proportion min is value - 1 + 0
//         // [value - 1, value + 1]
//     }
}