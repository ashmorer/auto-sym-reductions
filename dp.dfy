method pick(max: int) returns (result: int)
  requires max>0
  ensures 0<=result<max
{
  assume false;
}
predicate inv2(st: int, lfork: int, rfork: int)
{
  0<=st<=2 && 0<=lfork<=2 && 0<=rfork<=2 && !((st==2 && lfork==1 && rfork==1)||(st==2 && lfork==0 && rfork==1)||(st==2 && lfork==0 && rfork==0)||(st==2 && lfork==1 && rfork==0)||(st==2 && lfork==2 && rfork==1)||(st==2 && lfork==0 && rfork==2)||(st==2 && lfork==2 && rfork==2)||(st==2 && lfork==2 && rfork==0))
}

predicate inv(st: int, lfork: int, rfork: int)
{
  0<=st<=2 && 0<=lfork<=2 && 0<=rfork<=2 && (st==2 ==> lfork==1) && (st==2 ==> rfork==2)
}

lemma claim()
{
  assert forall i,j,k: int:: inv(i,j,k) <==> inv2(i,j,k);
}

lemma mod1()
  ensures forall i,n: int:: 0<=i<n ==> (((i-1)%n)+1)%n == i
{
  assert forall i,n: int:: 0<=i<n ==> (((i-1)%n)+1)%n == i;
}

lemma mod2()
  ensures forall i,n: int:: 0<=i<n ==> (((i+1)%n)+1)%n == (i+2)%n;
{
  assert forall i,n: int:: 0<=i<n ==> (((i+1)%n)+1)%n == (i+2)%n;
}

lemma mod3()
  ensures forall n: int:: n>2 ==> (0+1)%n==1
{
  assert forall n: int:: n>2 ==> (0+1)%n==1;
}

lemma mod4()
  ensures forall i,n:: 1<i<n-1 ==> ((i+1)%n != 0 && (i+1)%n != 1)
{
  assert forall i,n:: 1<i<n-1 ==> (i+1)%n != 0;
  assert forall i,n:: 1<i<n-1 ==> (i+1)%n != 1;
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
    assert 0<=i<n;
    //Remind Dafny the invariant holds on nearby processes, which is very restricting
    assert forall j::0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n]);
    mod1();
    mod2();
    mod3();
    mod4();
    assert (((i+1)%n)+1)%n==(i+2)%n;
    assert (((i-1)%n)+1)%n==i;
    assert inv(phil[(i+1)%n], fork[(i+1)%n], fork[(i+2)%n]);
    assert inv(phil[(i-1)%n], fork[(i-1)%n], fork[i]);
    assert inv(phil[i], fork[i], fork[(i+1)%n]);
    assert forall j:: 0<=j<n ==> inv(phil[j], fork[j], fork[(j+1)%n]);
    assert forall k: int:: k>2 ==> (0+1)%k==1;
    assert (0+1)%n == 1;
    assert inv(phil[0], fork[0], fork[1]);
    assert forall j:: 1<=j<=i-1 ==> 0<=j<n;
    assert forall j:: 1<=j<=i-1 ==> inv(phil[j], fork[j], fork[(j+1)%n]);
    assert forall j:: 1<=j<=i-1 ==> (inv(phil[j], fork[j], fork[(j+1)%n]) ==> (phil[j]==2 ==> fork[j]==1));
    assert forall j,k,l:: inv(j,k,l) ==> 0<=j<=2;
    assert forall j,k,l:: inv(j,k,l) ==> 0<=k<=2;
    assert forall j,k,l:: inv(j,k,l) ==> 0<=l<=2;
    assert forall j:: 1<=j<=i-1 ==> (inv(phil[j], fork[j], fork[(j+1)%n] ==> 0<=phil[j]<=2);
    assert forall j:: 1<=j<=i-1 ==> 0<=phil[j]<=2;
    assert forall j:: 1<=j<=i-1 ==> 0<=fork[j]<=2;
    assert forall j:: 1<=j<=i-1 ==> 0<=fork[(j+1)%n]<=2;
    assert forall j:: 1<=j<=i-1 ==> (phil[j]==2 ==> fork[j]==1);
    assert forall j:: 1<=j<=i-1 ==> (phil[j]==2 ==> fork[(j+1)%n]==2);
    fork[i] := 0;
    fork[(i+1)%n] := 0;
    phil[i] := 0;
    assert 1<i<n-1 ==> old(phil[0])==phil[0];
    assert 1<i<n-1 ==> (i+1)%n != 0;
    assert 1<i<n-1 ==> (i+1)%n != 1;
    assert 1<i<n-1 ==> old(fork[0])==fork[0];
    assert 1<i<n-1 ==> old(fork[1])==fork[1];
    assert 1<i<n-1 ==> (phil[0]==2 ==> fork[0]==1);
    assert 1<i<n-1 ==> (phil[0]==2 ==> fork[1]==2);
    assert 1<i<n-1 ==> (0<=phil[0]<=2);
    assert 1<i<n-1 ==> (0<=fork[0]<=2);
    assert 1<i<n-1 ==> (0<=fork[1]<=2);
    assert 1<i<n-1 ==> inv(phil[0], fork[0], fork[1]);//if i isn't near P0 (i==n-1, 0, or 1), invariant stays
    assert inv(phil[0], fork[0], fork[1]);
    assert forall j:: 1<=j<=i-1 ==> (phil[j]==2 ==> fork[j]==1);
    assert forall j:: 1<=j<=i-1 ==> (phil[j]==2 ==> fork[(j+1)%n]==2);
    assert forall j:: 1<=j<=i-1 ==> inv(phil[j], fork[j], fork[(j+1)%n]);//should be non-interference
    assert inv(phil[i], fork[i], fork[(i+1)%n]);
    assert inv(phil[(i+1)%n], fork[(i+1)%n], fork[(i+2)%n]);
    assert forall j:: i+1<j<n-1 ==> inv(phil[j], fork[j], fork[(j+1)%n]);
    assert inv(phil[n-1], fork[n-1], fork[0]);
    assert forall j:: 0<=j<n ==> (j==0 || 1<=j<=i-1 || j==i || j==i+1 || i+1<j<n-1 || j==n-1);//prove the following by cases
    assert forall j:: 0<=j<n ==>  inv(phil[j], fork[j], fork[(j+1)%n]);
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