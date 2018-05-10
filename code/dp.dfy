method pick(max: int) returns (result: int)
  requires max>0
  ensures 0<=result<max
{
  return 0;
}
predicate inv_old(st: int, lfork: int, rfork: int)
{
  0<=st<=2 && 0<=lfork<=2 && 0<=rfork<=2 && !((st==2 && lfork==1 && rfork==1)||(st==2 && lfork==0 && rfork==1)||(st==2 && lfork==0 && rfork==0)||(st==2 && lfork==1 && rfork==0)||(st==2 && lfork==2 && rfork==1)||(st==2 && lfork==0 && rfork==2)||(st==2 && lfork==2 && rfork==2)||(st==2 && lfork==2 && rfork==0))
}

predicate inv(st: int, lfork: int, rfork: int)
{
  0<=st<=2 && 0<=lfork<=2 && 0<=rfork<=2 && (st==2 ==> lfork==1) && (st==2 ==> rfork==2)
}

lemma claim()
{
  assert forall i,j,k: int:: inv(i,j,k) <==> inv_old(i,j,k);
}

lemma notEqMod(i: int, n: int)
  requires 0<=i<n
  requires n>2
  ensures forall j {:trigger (j+1)%n}:: (0<=j<n && i!=j) ==> (i+1)%n != (j+1)%n;
{
  //assert forall j:: (0<=j<n && i!=j) ==> (i+1)%n!=(j+1)%n;
}

method step(phil: array<int>, fork: array<int>, n:int, i: int)
  requires phil.Length==fork.Length==n
  requires n > 2
  requires 0<=i<n
  requires fork!=phil
  requires forall j:: 0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n])
  ensures forall j:: 0<=j<n ==>  inv(phil[j], fork[j], fork[(j+1)%n])
  modifies phil
  modifies fork
{
  if(phil[i]==0)
  {
    //Thinking->Hungry
    phil[i] := 1;
  }
  else if (phil[i]==1)
  {
    //Hungry
    if (fork[i]==1 && fork[(i+1) % n] ==2)
    {
      //Hungry->Eating
      phil[i] := 2;
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
    }//end hungry but not all forks
  }//end hungry
  else
  {
    //Eating->Thinking
    assert forall j {:trigger phil[j]}:: 0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n]);
    notEqMod(i,n);
    fork[i] := 0;
    fork[(i+1)%n] := 0;
    phil[i] := 0;
  }//End internal state detection
}//end step() method

method Main(phil: array<int>, fork:array<int>, n:int)
  modifies phil
  modifies fork
  requires fork!=phil
  requires phil.Length==fork.Length==n
  requires n>2
  requires forall j:: 0<=j<n ==> phil[j] == 0
  requires forall j:: 0<=j<n ==> fork[j] == 0
{
  var steps := pick(1000);
  while(steps>0)
    decreases steps
    invariant forall j:: 0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n])
  {
    steps := steps - 1;
    var i := pick(n);
    step(phil, fork, n, i);
  }
}