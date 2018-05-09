predicate p(i: int, j: int, k: int)
{
    q(i)
}

predicate q(i: int)
{
  i>0
}

method Main(phil: array<int>, a: array<int>, b: array<int>, i: int, n: int)
  requires phil.Length==a.Length==b.Length==n
  requires 0<=i<n
  requires n>2 
{
  assume forall j:: 0<=j<n-1 ==> p(phil[j], phil[j+1], phil[j]);
  //assert forall j:: 0<=j<n-1 ==> (inv(phil[j], a[j+1], a[j]) ==> inv2(phil[j]));
  assert forall j:: 0<=j<n-1 ==> q(phil[j]);
}

//Making inv() a binary predicate verifies
//Making inv() be in three distinct arrays verifies
//Making inv() refer to concrete values in the second/third components verifies
//Making inv() refer to the same values in second/third components verifies.

//Why as written does it not verify?