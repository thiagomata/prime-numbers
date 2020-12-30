    // lemma bigProoff(
    //     initial: nat,  // 5
    //     prev: seq<nat>, // [ 2 3 ]
    //     list: seq<nat>, // [ 2 4 ]
    //     integralList: seq<nat>, // [ 7 11 ]
    //     modList: seq<nat>, // [2, 1]
    //     modIntegralList: seq<nat>, // [1, 2]
    //     m: nat, // 3
    //     cycleList: seq<nat>, // [ 2 4 2 4 2 4 ]
    //     integralCycle: seq<nat>, // [ 7 11 13 17 19 23 ]
    //     modIntegralCycle: seq<nat> // [ 1 2 1 2 1 2 ]
    // )
    //     requires m > 0;
    //     requires |list| > 0;
    //     requires nonZero(list);
    //     requires |cycleList| == |list| * m;
    //     requires |list| == |integralList|;

    //     requires |modList| == |list|;
    //     requires isModList(list, m, modList);
    //     requires nonZero(modList);

    //     requires isIntegral(list, initial, integralList);
    //     requires isCycle(list, cycleList);
    //     requires |integralCycle| == |cycleList|;
    //     requires isIntegral(cycleList, initial, integralCycle);

    //     // // if the list integral is not multiple of m
    //     requires isNotMultiple(integralList, m);
    //     requires |modIntegralList| == |integralList|;
    //     requires isModList(integralList, m, modIntegralList);
    //     requires nonZero(modIntegralList);

    //     requires |modIntegralCycle| == |integralCycle|;
    //     requires isModList(integralCycle, m, modIntegralCycle);

    //     requires ModDiv.mod(sum(list), m) == 0; // [2 4] ==> 2 + 4 == 6 ==> 6 % 3 == 0;
        
    //     // the next integral should also be not multiple of m
    //     ensures isNotMultiple(integralCycle, m);
    //     ensures nonZero(modIntegralCycle);
    // {
    // }

 