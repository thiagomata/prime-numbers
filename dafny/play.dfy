   method Main() {
       var l := [1,2,3];
       var j := [1,8];
       print(j[..1]);
       assert j[..1] == [j[0]];
      //  print(l[..|l|]);
      //  print(forall v :: 0 <= v < |j| ==> j[v] in l);
    }