// Introduce a constant 'N' and postulate that it is non-negative
const N: int;
axiom 0 <= N;

// Declare a map from integers to integers.
// 'a' should be treated as an array of 'N' elements, indexed from 0 to N-1
var a, b0, b1, b2: [int]int;

// Returns true iff the elements of 'arr' are small (i.e. values in the range -3N to +3N)
function has_small_elements(arr: [int]int): bool
{
  (forall i: int :: (0 <= i && i < N) ==> (-3 * N <= arr[i] && arr[i] <= 3 * N))
}

// Sorts 'a' using bucket sort or quick sort, as determined by has_small_elements(a)
procedure sort() returns (perm : [int]int)
  modifies a,b0,b1,b2;
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

/*

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

*/


// dummy sort implementation for faster development times
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
 // perm is a permutation
  assume (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  assume (forall i: int :: lo <= i && i <= hi ==> a[i] == old(a)[perm[i]]);
  // array is sorted
  assume (forall k, l: int :: lo <= k && k <= l && l <= hi ==> a[k] <= a[l]);
  // rest of the array is untouched
  assume (forall k: int :: k < lo || k > hi ==> a[k] == old(a)[k]);  
}

// dummy sort implementation for faster development times
procedure qs_b0(lo : int, hi : int) returns (perm: [int]int) 
  modifies b0;
  requires lo <= hi;
  
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  ensures (forall i: int :: lo <= i && i <= hi ==> b0[i] == old(b0)[perm[i]]);
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> b0[k] <= b0[l]);
  ensures (forall k: int :: k < lo || k > hi ==> b0[k] == old(b0)[k]);
{
  assume (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  assume (forall i: int :: lo <= i && i <= hi ==> b0[i] == old(b0)[perm[i]]);
  assume (forall k, l: int :: lo <= k && k <= l && l <= hi ==> b0[k] <= b0[l]);
  assume (forall k: int :: k < lo || k > hi ==> b0[k] == old(b0)[k]);  
}
procedure qs_b1(lo : int, hi : int) returns (perm: [int]int) 
  modifies b1;
  requires lo <= hi;
  
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  ensures (forall i: int :: lo <= i && i <= hi ==> b1[i] == old(b1)[perm[i]]);
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> b1[k] <= b1[l]);
  ensures (forall k: int :: k < lo || k > hi ==> b1[k] == old(b1)[k]);
{
  assume (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  assume (forall i: int :: lo <= i && i <= hi ==> b1[i] == old(b1)[perm[i]]);
  assume (forall k, l: int :: lo <= k && k <= l && l <= hi ==> b1[k] <= b1[l]);
  assume (forall k: int :: k < lo || k > hi ==> b1[k] == old(b1)[k]);  
}
procedure qs_b2(lo : int, hi : int) returns (perm: [int]int) 
  modifies b2;
  requires lo <= hi;
  
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  ensures (forall i: int :: lo <= i && i <= hi ==> b2[i] == old(b2)[perm[i]]);
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> b2[k] <= b2[l]);
  ensures (forall k: int :: k < lo || k > hi ==> b2[k] == old(b2)[k]);
{
  assume (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  assume (forall i: int :: lo <= i && i <= hi ==> b2[i] == old(b2)[perm[i]]);
  assume (forall k, l: int :: lo <= k && k <= l && l <= hi ==> b2[k] <= b2[l]);
  assume (forall k: int :: k < lo || k > hi ==> b2[k] == old(b2)[k]);  
}

procedure bs(lo : int, hi : int) returns (perm: [int]int)
  modifies a, b0, b1, b2;
  requires lo <= hi;
  requires lo >= 0;
  // only use bucket sort when these conditions hols
  requires (forall i: int :: (0 <= i && i < N) ==> (-3 * N <= a[i] && a[i] <= 3 * N));
  
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
  
  //we're using three buckets: TODO at the moment we're using global arrays
  //var b0: [int]int; // bucket for values [-3N,-1N)
  //var b1: [int]int; //bucket for values [-1N,1N)
  //var b2: [int]int; //bucket for values [1N,3N]
  
  //buckets' start/end indices
  var b0_i:int;
  var b1_i:int;
  var b2_i:int;
  
  //buckets' upper bounds (exclusive)
  var bound_0:int;
  var bound_1:int;
  var bound_2:int;
  
  //bucket permutations
  var perm0, perm1, perm2 : [int]int;
  
  //iterator variables
  var i :int;
  
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
  
  
  //TODO (?): keep track of permutations
    
  //sort the buckets
  if(b0_i > 0) { // if bucket is non empty
      call perm0 := qs_b0(0, b0_i-1);
      i := 0;
      while(i < b0_i)
        invariant (forall k: int :: 0 <= k && k < i ==> a[lo + i] == b0[i]);
        invariant (forall k, l: int :: lo <= k && k <= l && l < lo + i ==> a[k] <= a[l]);
        //TODO: invariants
      {
        a[lo + i] := b0[i];
        i := i + 1;
      }
      //here the array from lo...lo+bo_i-1 is sorted
      assert (forall k, l: int :: lo <= k && k <= l && l < lo + b0_i ==> a[k] <= a[l]);
  }
  
  if(b1_i > 0) { // if bucket is non empty
      call perm1 := qs_b1(0, b1_i-1);
      i := 0;
      while(i < b1_i)
        invariant (forall k: int :: 0 <= k && k < i ==> a[b0_i + i] == b1[i]);
        invariant (forall k, l: int :: b0_i <= k && k <= l && l < b0_i + i ==> a[k] <= a[l]);
        //TODO: invariants
      {
        a[b0_i + i] := b1[i];
        i := i + 1;
      }
      //here the array from lo...lo+bo_i-1 is sorted
      assert (forall k, l: int :: b0_i <= k && k <= l && l < b0_i + b1_i ==> a[k] <= a[l]);
  }
 
   if(b2_i > 0) { // if bucket is non empty
      call perm2 := qs_b2(0, b2_i-1);
      i := 0;
      while(i < b2_i)
        invariant (forall k: int :: 0 <= k && k < i ==> a[b1_i + i] == b2[i]);
        invariant (forall k, l: int :: b1_i <= k && k <= l && l < b1_i + i ==> a[k] <= a[l]);
        //TODO: invariants
      {
        a[b1_i + i] := b2[i];
        i := i + 1;
      }
      //here the array from lo...lo+bo_i-1 is sorted
      assert (forall k, l: int :: b1_i <= k && k <= l && l < b1_i + b2_i ==> a[k] <= a[l]);
  }
  
}
