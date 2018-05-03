method pick(max: int) returns (result: int)
  requires max>0
  ensures 0<=result<max
{
  assume false;
}

predicate inv(st: int, lfork: int, rfork: int)
{
  0<=st<=2 && 0<=lfork<=2 && 0<=rfork<=2 && !((st==2 && lfork==1 && rfork==1)||(st==2 && lfork==0 && rfork==1)||(st==2 && lfork==0 && rfork==0)||(st==2 && lfork==1 && rfork==0)||(st==2 && lfork==2 && rfork==1)||(st==2 && lfork==0 && rfork==2)||(st==2 && lfork==2 && rfork==2)||(st==2 && lfork==2 && rfork==0))
}

method Main(phil: array<int>, fork: array<int>) 
  requires forall i:: 0<=i<phil.Length ==> phil[i] == 0
  requires forall i:: 0<=i<fork.Length ==> fork[i] == 0
  requires phil.Length == fork.Length > 0
  modifies phil
  modifies fork
{
  var steps := pick(100);
  while (steps>0)//phil[i] has access to fork[i] and fork[i+1] mod n
    invariant forall i:: 0<=i<phil.Length ==> inv(phil[i], fork[i], fork[(i+1)%fork.Length])
  {
    steps := steps-1;
    var i := pick(phil.Length);
    assert inv(phil[i], fork[i], fork[(i+1)%fork.Length]);
    assert phil[i]==2 ==> fork[i]==1;
    assert phil[i]==2 ==> fork[(i+1)%fork.Length]==2;
    if(phil[i]==0)
    {
      //Thinking->Hungry
      phil[i] := 1;
      assert phil[i]==2 ==> fork[i]==1;101 albert street?
    }
    else if (phil[i]==1)
    {
      //Hungry
      if (fork[i]==1 && fork[(i+1) % fork.Length] ==2)
      {
        //Hungry->Eating
        phil[i] := 2;
        assert phil[i]==2 ==> fork[i]==1;
      }
      else
      {
        //Seek forks to pick up
        var temp := pick(2);//try to pick up fork 0 or 1
        if(temp==0)
        {
          //Try to pick up left fork
          if(fork[i]==0)
          {
            fork[i] := 1;
          }
        }
        else
        {
          //Try to pick up right fork
          if(fork[(i+1)%fork.Length]==0)
          {
            fork[(i+1)%fork.Length] := 2;
          }
        }//end fork pick-up selection
        assert phil[i]==2 ==> fork[i]==1;
      }//end hungry but not all forks
      assert phil[i]==2 ==> fork[i]==1;
    }//end hungry
    else
    {
      //Eating->Thinking
      fork[i] := 0;
      fork[(i+1)%fork.Length] := 0;
      phil[i] := 0;
      assert phil[i]==2 ==> fork[i]==1;
    }
    assert phil[i]==2 ==> fork[i]==1;
    assert phil[i]==2 ==> fork[(i+1)%fork.Length]==2;
  }
}