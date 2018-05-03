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

method step(phil: array<int>, fork: array<int>, n:int, i: int)
    requires phil.Length==fork.Length==n
    requires n>0
    requires forall j:: 0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n])
    requires 0<=i<n && inv(phil[i], fork[i], fork[(i+1)%n])
    ensures  0<=i<n && inv(phil[i], fork[i], fork[(i+1)%n])
    ensures forall j:: 0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n])
    modifies phil
    modifies fork
{
    if(phil[i]==0)
    {
      //Thinking->Hungry
      phil[i] := 1;
      assert phil[i]==2 ==> fork[i]==1;
    }
    else if (phil[i]==1)
    {
      //Hungry
      if (fork[i]==1 && fork[(i+1) % n] ==2)
      {
        //Hungry->Eating
        assert phil[i]==2 ==> fork[i]==1;
        assert (fork[i]==1);
        phil[i] := 2;
        assert (fork[i]==1);
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
          if(fork[(i+1)%n]==0)
          {
            fork[(i+1)%n] := 2;
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
      fork[(i+1)%n] := 0;
      phil[i] := 0;
      assert phil[i]==2 ==> fork[i]==1;
    }
    assert forall j:: 0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n]);
}

method Main(phil: array<int>, fork: array<int>, n: int) 
  requires forall i:: 0<=i<phil.Length ==> phil[i] == 0
  requires forall i:: 0<=i<fork.Length ==> fork[i] == 0
  requires phil.Length == fork.Length ==n
  requires n > 0
  modifies phil
  modifies fork
{
  var steps := pick(100);
  while (steps>0)//phil[i] has access to fork[i] and fork[i+1] mod n
    decreases steps
    invariant forall i:: 0<=i<n ==> inv(phil[i], fork[i], fork[(i+1)%n])
  {
    steps := steps-1;
    var i := pick(phil.Length);
    step(phil, fork, n, i);//move the i'th philosopher
    assert phil[i]==2 ==> fork[i]==1;
    assert phil[i]==2 ==> fork[(i+1)%n]==2;
  }
}