// Introduce a constant 'N' and postulate that it is non-negative
const N: int;
axiom 0 <= N;

// Declare a map from integers to integers.
// 'a' should be treated as an array of 'N' elements, indexed from 0 to N-1
var a: [int]int;
// internal variable that is used by quicksort implementation
var a_qs:  [int]int;

// Returns true iff the elements of 'arr' are small (i.e. values in the range -3N to +3N)
function has_small_elements(arr: [int]int): bool
{
  (forall i: int :: (0 <= i && i < N) ==> (-3 * N <= arr[i] && arr[i] <= 3 * N))
}

// Sorts 'a' using bucket sort or quick sort, as determined by has_small_elements(a)
procedure sort() returns (perm : [int]int)
  modifies a, a_qs;
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
        call perm := bucketSort(0,N-1);
    } else {
        // sort 'a' using quick sort
        call a, perm := quickSort(a,0,N-1);
    }     
  }
 
}


procedure qsPartition(lo : int, hi : int) returns (pivot_index: int, perm: [int]int) 
  modifies a_qs;
  requires lo <= hi;
  ensures lo <= pivot_index && pivot_index <= hi;
  // array is correctly partitioned
  ensures (forall k: int :: lo <= k && k < pivot_index ==> a_qs[k] <= a_qs[pivot_index]);
  ensures (forall k: int :: pivot_index < k && k <= hi ==> a_qs[k] > a_qs[pivot_index]);
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall i, j: int :: lo <= i && i < j && j <= hi ==> perm[i] != perm[j]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lo <= i && i <= hi ==> a_qs[i] == old(a_qs)[perm[i]]);
  // only the indexes between lo and hi are modified, the rest of the array stays the same
  ensures (forall i: int :: i < lo || i > hi ==> a_qs[i] == old(a_qs)[i]);
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
  
  
  pivot := a_qs[hi];
  while(j < hi) 
    invariant pivot == a_qs[hi];
    invariant lo - 1 <= i && i < j && j <= hi;
 
    // correct partition
    invariant (forall k: int :: lo <= k && k <= i ==> a_qs[k] <= pivot);
    invariant (forall k: int :: i < k && k < j ==> a_qs[k] > pivot);
    
    // correct permutation
    invariant (forall k: int :: lo <= k && k <= hi ==> lo <= perm[k] && perm[k] <= hi);
    invariant (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
    
    // final array is permutation of original
    invariant (forall k: int :: lo <= k && k <= hi ==> a_qs[k] == old(a_qs)[perm[k]]);
    
    // rest of the array is untouched
    invariant (forall k: int :: k < lo || k > hi ==> a_qs[k] == old(a_qs)[k]);
    
  {
    if(a_qs[j] <= pivot) {
      i := i + 1;
      // swap a_qs[i] with a_qs[j]
      tmp := a_qs[i]; a_qs[i] := a_qs[j]; a_qs[j] := tmp;
      tmp := perm[i]; perm[i] := perm[j]; perm[j] := tmp;
    }
    j := j + 1;
  }
  
  //swap a_qs[i+1] with a_qs[hi], the pivot element
  tmp := a_qs[i+1];  a_qs[i+1] := a_qs[hi];  a_qs[hi] := tmp;
  tmp := perm[i+1]; perm[i+1] := perm[hi]; perm[hi] := tmp;
  
  pivot_index := i+1;

}


procedure qs(lo : int, hi : int) returns (perm: [int]int) 
  modifies a_qs;
  requires lo <= hi;
  
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lo <= i && i <= hi ==> a_qs[i] == old(a_qs)[perm[i]]);
  
  // array is sorted
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> a_qs[k] <= a_qs[l]);
  
  // rest of the array is untouched
  ensures (forall k: int :: k < lo || k > hi ==> a_qs[k] == old(a_qs)[k]);
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

    // combine perm_comb with perm
    n := lo;
    while(n <= hi) 
      invariant lo <= n && n <= hi+1;
      invariant (forall i: int :: lo <= i && i < n ==> perm[i] == perm_comb[perm[i]]);
      invariant (forall i: int :: lo <= i && i < n ==> lo <= perm[i] && perm[i] <= hi);
      invariant (forall k, l: int :: lo <= k && k < l && l < n ==> perm[k] != perm[l]);
      invariant (forall i: int :: lo <= i && i < n ==> a_qs[i] == old(a_qs)[perm[i]]);
    { perm[n] := perm_comb[perm[n]]; }
    
  } else {
    perm[lo] := lo;
  }
    
}

// public interface for quicksort that can be used to sort arbitrary arrays
procedure quickSort(arr : [int]int, lo : int, hi : int) returns (arr_sorted : [int]int, perm: [int]int) 
  modifies a_qs;
  requires lo <= hi;
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lo <= i && i <= hi ==> arr_sorted[i] == arr[perm[i]]);
  // array is sorted
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> arr_sorted[k] <= arr_sorted[l]);
{
  // write input array into a_qs
  a_qs := arr;
  // let quicksort implementation sort a_qs
  call perm := qs(lo,hi);
  // write a_qs into output argument
  arr_sorted := a_qs;
}


procedure bucketSort(lo : int, hi : int) returns (perm: [int]int)
  modifies a,a_qs; //, b0, b1, b2;
  // only allow bucketsort to be called from [0..N-1]
  requires lo == 0;
  requires hi == N-1;
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lo <= i && i <= hi ==> a[i] == old(a)[perm[i]]);
  // array is sorted
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi  ==> a[k] <= a[l]);
{
  
  //buckets' end indices
  var b0_i:int;
  var b1_i:int;
  var b2_i:int;
  
  //buckets' upper bounds (exclusive)
  var bound_0:int;
  var bound_1:int;
  var bound_2:int;
  
  //bucket permutations
  var perm0, perm1, perm2 : [int]int;

  var b0, b0_sorted, b1, b1_sorted, b2, b2_sorted: [int]int;
  
  //iterator variables
  var i :int;
  
  b0_i := 0;
  b1_i := 0;
  b2_i := 0;
  bound_0 := -1*N;
  bound_1 := N;
  bound_2 := 3*N + 1;
  
  i := lo;
  while(i <= hi)
    invariant (i >= lo && i <= hi+1);
    // array 'a' is divided over b0,b1 and b2
    invariant b0_i+b1_i+b2_i == lo+i;

    //all buckets contain the correct kind of elements:
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] < -1*N));
    invariant(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] >= -1*N && b1[e] < N));
    invariant(forall e:int :: (e >= 0 && e < b2_i) ==> (b2[e] >= N));
        
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
  
  // sort first bucket if non-empty
  if(b0_i > 0) { call b0_sorted, perm0 := quickSort(b0, 0, b0_i-1); }
  // copy back elements from bucket to array
  i := 0;
  while(i < b0_i)
    // copied values are sorted
    invariant (forall k: int :: 0 <= k && k < i ==> a[k+lo] == b0_sorted[k]);
    invariant (forall k, l: int :: 0 <= k && k <= l && l < i ==> a[k+lo] <= a[l+lo]);
  {
    a[i+lo] := b0_sorted[i];
    i := i + 1;
  }
  
  // sort second bucket if non-empty
  if(b1_i > 0) { call b1_sorted, perm1 := quickSort(b1, 0, b1_i-1); }
  // copy back elements from bucket to array

  i := 0;
  while(i < b1_i)
    // preserve info. about first part of array
    invariant (forall k: int :: 0 <= k && k < b0_i ==> a[k+lo] == b0_sorted[k]);
    invariant (forall k, l: int :: 0 <= k && k <= l && l < b0_i ==> a[k+lo] <= a[l+lo]);
    
    // copied values are sorted
    invariant (forall k: int :: 0 <= k && k < i ==> a[k+lo+b0_i] == b1_sorted[k]);
    invariant (forall k, l: int :: 0 <= k && k <= l && l < i ==> a[k+lo+b0_i] <= a[l+lo+b0_i]);
      
  {
    a[i+lo+b0_i] := b1_sorted[i];   
  }
  

  // sort third bucket if non-empty
  if(b2_i > 0) { call b2_sorted, perm2 := quickSort(b2, 0, b2_i-1); }
  // copy back elements from bucket to array
  i := 0;
  while(i < b2_i)
    // preserve info. about first part of array
    invariant (forall k: int :: 0 <= k && k < b0_i ==> a[k+lo] == b0_sorted[k]);
    invariant (forall k, l: int :: 0 <= k && k <= l && l < b0_i ==> a[k+lo] <= a[l+lo]);
    
    // preserve info. about second part of array
    invariant (forall k: int :: 0 <= k && k < b1_i ==> a[k+lo+b0_i] == b1_sorted[k]);
    invariant (forall k, l: int :: 0 <= k && k <= l && l < b1_i ==> a[k+lo+b0_i] <= a[l+lo+b0_i]);
    
    // copied values are sorted
    invariant (forall k: int :: 0 <= k && k < i ==> a[k+lo+b0_i+b1_i] == b2_sorted[k]);
    invariant (forall k, l: int :: 0 <= k && k <= l && l < i ==> a[k+lo+b0_i+b1_i] <= a[l+lo+b0_i+b1_i]);
  {
    a[i+lo+b0_i+b1_i] := b2_sorted[i];   
  }
  
  //TODO prove that array is permutation of original
  assume (forall k: int :: lo <= k && k <= hi ==> lo <= perm[k] && perm[k] <= hi);
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  assume (forall k: int :: lo <= k && k <= hi ==> a[k] == old(a)[perm[k]]);

}

