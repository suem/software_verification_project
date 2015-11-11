// Introduce a constant 'N' and postulate that it is non-negative
const N: int;
axiom 0 <= N;

// Declare a map from integers to integers.
// 'a' should be treated as an array of 'N' elements, indexed from 0 to N-1
var a: [int]int;

// Returns true iff the elements of 'arr' are small (i.e. values in the range -3N to +3N)
function has_small_elements(arr: [int]int): bool
{
  (forall i: int :: (0 <= i && i < N) ==> (-3 * N <= arr[i] && arr[i] <= 3 * N))
}

// Sorts 'a' using bucket sort or quick sort, as determined by has_small_elements(a)
procedure sort() returns (perm : [int]int)
  modifies a;
  // perm is a permutation
  ensures (forall i: int :: 0 <= i && i <= N-1 ==> 0 <= perm[i] && perm[i] <= N-1);
  ensures (forall k, l: int :: 0 <= k && k < l && l <= N-1 ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: 0 <= i && i <= N-1 ==> a[i] == old(a)[perm[i]]);
  // array is sorted
  ensures (forall k, l: int :: 0 <= k && k <= l && l <= N-1 ==> a[k] <= a[l]);
  
{
  
  if(N > 0) { // array not empty
    if (has_small_elements(a))
    {
        // sort 'a' using bucket sort
        call perm := bs(0,N-1);
    } else {
        // sort 'a' using quick sort
        call perm := qs(0,N-1);
    }     
  }
 
}



procedure qsPartition(lo : int, hi : int) returns (pivot_index: int, perm: [int]int) 
  modifies a;
  requires lo <= hi;
  ensures lo <= pivot_index && pivot_index <= hi;
  // array is correctly partitioned
  ensures (forall k: int :: lo <= k && k < pivot_index ==> a[k] <= a[pivot_index]);
  ensures (forall k: int :: pivot_index < k && k <= hi ==> a[k] > a[pivot_index]);
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall i, j: int :: lo <= i && i < j && j <= hi ==> perm[i] != perm[j]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lo <= i && i <= hi ==> a[i] == old(a)[perm[i]]);
  // only the indexes between lo and hi are modified, the rest of the array stays the same
  ensures (forall i: int :: i < lo || i > hi ==> a[i] == old(a)[i]);
{

  // local variables
  var i, j, pivot, tmp, n : int;

  // init permutation
  n := lo;
  while (n <= hi)
    invariant lo <= n && n <= hi+1;
    invariant (forall k: int :: lo <= k && k < n ==> perm[k] == k);
    invariant (forall k: int :: lo <= k && k < n ==> lo <= perm[k] && perm[k] <= hi);
    invariant (forall k, l: int :: lo <= k && k < l && l < n ==> perm[k] != perm[l]);
  {
    perm[n] := n;
    n := n + 1;
  }

  i := lo - 1;
  j := lo;
  
  
  pivot := a[hi];
  while(j < hi) 
    invariant pivot == a[hi];
    invariant lo - 1 <= i && i < j && j <= hi;
 
    // correct partition
    invariant (forall k: int :: lo <= k && k <= i ==> a[k] <= pivot);
    invariant (forall k: int :: i < k && k < j ==> a[k] > pivot);
    
    // correct permutation
    invariant (forall k: int :: lo <= k && k <= hi ==> lo <= perm[k] && perm[k] <= hi);
    invariant (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
    
    // final array is permutation of original
    invariant (forall k: int :: lo <= k && k <= hi ==> a[k] == old(a)[perm[k]]);
    
    // rest of the array is untouched
    invariant (forall k: int :: k < lo || k > hi ==> a[k] == old(a)[k]);
    
  {
    if(a[j] <= pivot) {
      i := i + 1;
      // swap a[i] with a[j]
      tmp := a[i]; a[i] := a[j]; a[j] := tmp;
      tmp := perm[i]; perm[i] := perm[j]; perm[j] := tmp;
    }
    j := j + 1;
  }
  
  //swap a[i+1] with a[hi], the pivot element
  tmp := a[i+1];  a[i+1] := a[hi];  a[hi] := tmp;
  tmp := perm[i+1]; perm[i+1] := perm[hi]; perm[hi] := tmp;
  
  pivot_index := i+1;

}


procedure qs(lo : int, hi : int) returns (perm: [int]int) 
  modifies a;
  requires lo <= hi;
  
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lo <= i && i <= hi ==> a[i] == old(a)[perm[i]]);
  
  // array is sorted
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> a[k] <= a[l]);
  
  // rest of the array is untouched
  ensures (forall k: int :: k < lo || k > hi ==> a[k] == old(a)[k]);
{
   // local variables
  var n, pivot_index: int;
  var perm_comb, perm_left, perm_right: [int]int;

  if(lo < hi) {
    call pivot_index, perm := qsPartition(lo,hi);
    
    // we have a non empty left part
    if(lo < pivot_index) {
      call perm_left := qs(lo, pivot_index - 1);
      n := lo;
      while(n < pivot_index) 
        invariant lo <= n && n <= pivot_index;
        invariant (forall i: int :: lo <= i && i < n ==> perm_comb[i] == perm_left[i]);
        invariant (forall i: int :: lo <= i && i < n ==> lo <= perm_comb[i] && perm_comb[i] < pivot_index);
        invariant (forall k, l: int :: lo <= k && k < l && l < n ==> perm_comb[k] != perm_comb[l]);
      { perm_comb[n] := perm_left[n]; }
     
    }     
    
    // we have a non empty right part
    if(pivot_index + 1 <= hi) {
      call perm_right := qs(pivot_index + 1, hi);
      n := pivot_index + 1;
      while(n <= hi) 
        invariant pivot_index + 1 <= n && n <= hi+1;
        invariant (forall i: int :: pivot_index + 1 <= i && i < n ==> perm_comb[i] == perm_right[i]);
        invariant (forall i: int :: pivot_index + 1 <= i && i < n ==> pivot_index + 1 <= perm_comb[i] && perm_comb[i] <= hi);
        invariant (forall k, l: int :: pivot_index + 1 <= k && k < l && l < n ==> perm_comb[k] != perm_comb[l]);
      { perm_comb[n] := perm_left[n]; }
    }
    
    perm_comb[pivot_index] := pivot_index;
    // perm_comb is now a permutation
    assert (forall i: int :: lo <= i && i <= hi ==> lo <= perm_comb[i] && perm_comb[i] <= hi);
    assert (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm_comb[k] != perm_comb[l]);
    
    // assert that perm combined with perm_comb is a permutation
    n := lo;
    while(n <= hi) 
      invariant lo <= n && n <= hi+1;
      invariant (forall i: int :: lo <= i && i < n ==> perm[i] == perm_comb[perm[i]]);
      invariant (forall i: int :: lo <= i && i < n ==> lo <= perm[i] && perm[i] <= hi);
      invariant (forall k, l: int :: lo <= k && k < l && l < n ==> perm[k] != perm[l]);
      invariant (forall i: int :: lo <= i && i < n ==> a[i] == old(a)[perm[i]]);
    { perm[n] := perm_comb[perm[n]]; }
    
  } else {
    perm[lo] := lo;
  }
    
}

procedure bs(lo : int, hi : int) returns (perm: [int]int)
  modifies a;
  requires lo <= hi;
  requires lo >= 0;
  
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lo <= i && i <= hi ==> a[i] == old(a)[perm[i]]);
  
  // array is sorted
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> a[k] <= a[l]);
  
  // rest of the array is untouched
  ensures (forall k: int :: k < lo || k > hi ==> a[k] == old(a)[k]);
{
  //assumption: all values are within the [-3N, 3N] range where N = length of `a'
  
  //we're using three buckets:
  var b0: [int]int; //bucket for values [-3N,-1N)
  var b1: [int]int; //bucket for values [-1N,1N)
  var b2: [int]int; //bucket for values [1N,3N]
  
  //buckets' start/end indices
  var b0_i:int;
  var b1_i:int;
  var b2_i:int;
  
  //buckets' upper bounds (exclusive)
  var bound_0:int;
  var bound_1:int;
  var bound_2:int;
  
  //iterator variables
  var i,k:int;
  
  b0_i := 0;
  b1_i := 0;
  b2_i := 0;
  bound_0 := -N;
  bound_1 := N;
  bound_2 := 3*N + 1;
  
  i := lo;
  while(i < hi)
    invariant (i >= lo && i <= hi);
    
    //all previous elements of a have been placed in a bucket
    invariant(forall e:int :: ((e >= lo && e <i) ==> (exists t:int :: (b0[t] == a[e] || b1[t] == a[e] || b2[t] == a[e]))) );
    
    //all buckets contain the correct kind of elements:
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] < -N));
    invariant(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] >= -N && b1[e] < N));
    invariant(forall e:int :: (e >= 0 && e < b2_i) ==> (b2[e] >= N && b2[e] < 3*N + 1));
    
    //TODO: more invariants
    
    {
      
    //add a[i] to correct bucket
    if(a[i] < bound_1){
      if(a[i] < bound_0){
        b0[b0_i] := a[i];
        b0_i := b0_i + 1;
      }
      else{
        b1[b1_i] := a[i];
        b1_i := b1_i + 1;
      }
    }
    else{
      b2[b2_i] := a[i];
      b2_i := b2_i + 1;
    }
    
    i := i + 1;
  }
  
  //debugging: check all elements have been inserted into a bucket
  assert(forall e:int :: ((e >= lo && e < hi) ==> (exists t:int :: (b0[t] == a[e] || b1[t] == a[e] || b2[t] == a[e]))));
  
  //sort the buckets
  //TODO (?): call QS to sort b0 for the range [0..(b0_i - 1)]
  //TODO (?): call QS to sort b1 for the range [0..(b1_i - 1)]
  //TODO (?): call QS to sort b2 for the range [0..(b2_i - 1)]
  assume(forall e:int :: ((e > 0 && e < b0_i) ==> (b0[e-1] <= b0[e])));
  assume(forall e:int :: ((e > 0 && e < b1_i) ==> (b1[e-1] <= b1[e])));
  assume(forall e:int :: ((e > 0 && e < b2_i) ==> (b2[e-1] <= b2[e])));
  
  //TODO (?): keep track of permutations
  
  i := lo;
  while(i < b0_i)
    //TODO: invariants
    {
    a[i] := b0[i];
    i := i + 1;
  }
  
  k := 0;
  while(k < b1_i)
    //TODO: invariants
    {
    a[i] := b1[k];
    i := i + 1;
    k := k + 1;
  }
  
  k := 0;
  while(k < b2_i)
    //TODO: invariants
    {
    a[i] := b2[k];
    i := i + 1;
    k := k + 1;
  }
}
