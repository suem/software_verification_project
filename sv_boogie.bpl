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
  var perm_comb, perm_left, perm_right, perm_res: [int]int;
  
  if(lo < hi) {
    call pivot_index, perm := qsPartition(lo,hi);
    assert (forall i: int :: lo <= i && i <= hi ==> a_qs[i] == old(a_qs)[perm[i]]);

    // we have a non empty left part
    if(lo < pivot_index) {
      call perm_left := qs(lo, pivot_index - 1);

      n := lo;
      while(n < pivot_index) 
        invariant lo <= n && n <= pivot_index;
        invariant (forall i: int :: lo <= i && i < n ==> perm_comb[i] == perm_left[i]);
        invariant (forall i: int :: lo <= i && i < n ==> lo <= perm_comb[i] && perm_comb[i] <= hi);
        invariant (forall k, l: int :: lo <= k && k < l && l < n ==> perm_comb[k] != perm_comb[l]);
      { 
        perm_comb[n] := perm_left[n];
        n := n+1;
      }
    }     

    //assert (forall i: int :: lo <= i && i <= pivot_index-1 ==> a_qs[i] == old(a_qs)[perm[perm_comb[i]]]);
    //assert (forall i: int :: pivot_index + 1 <= i && i <= hi ==> a_qs[i] == old(a_qs)[perm[i]]);

    // we have a non empty right part
    if(pivot_index + 1 <= hi) {
      call perm_right := qs(pivot_index + 1, hi);

      n := pivot_index + 1;
      while(n <= hi)
        // maintain previous information about perm_comb
          invariant (forall i: int :: lo <= i && i < pivot_index ==> perm_comb[i] == perm_left[i]);
          invariant (forall i: int :: lo <= i && i < pivot_index ==> lo <= perm_comb[i] && perm_comb[i] <= hi);
          invariant (forall k, l: int :: lo <= k && k < l && l < pivot_index ==> perm_comb[k] != perm_comb[l]);
          invariant (forall i: int :: lo <= i && i <= pivot_index-1 ==> a_qs[i] == old(a_qs)[perm[perm_comb[i]]]);

          invariant pivot_index + 1 <= n && n <= hi+1;
          invariant (forall i: int :: pivot_index + 1 <= i && i < n ==> perm_comb[i] == perm_right[i]);
          invariant (forall i: int :: pivot_index + 1 <= i && i < n ==> pivot_index + 1 <= perm_comb[i] && perm_comb[i] <= hi);
          invariant (forall k, l: int :: pivot_index + 1 <= k && k < l && l < n ==> perm_comb[k] != perm_comb[l]);
      { 
        perm_comb[n] := perm_right[n]; 
        n := n+1;
      }
    }

    //assert (forall i: int :: pivot_index + 1 <= i && i <= hi ==> a_qs[i] == old(a_qs)[perm[perm_comb[i]]]);
    //assert (forall i: int :: lo <= i && i <= pivot_index-1 ==> a_qs[i] == old(a_qs)[perm[perm_comb[i]]]);

    perm_comb[pivot_index] := pivot_index;
    // perm_comb is now a permutation

    //assert (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
    //assert (forall i: int :: lo <= i && i <= hi ==> lo <= perm_comb[i] && perm_comb[i] <= hi);

    //IMPORTANT: without this assert the verify doesn't terminate
    assert (forall k, l: int :: lo <= k && k <= l && l <= hi  ==> a_qs[k] <= a_qs[l]);

    // combine perm_comb with perm
    n := lo;
    while(n <= hi) 
      invariant lo <= n && n <= hi+1;
      invariant (forall i: int :: lo <= i && i < n ==> perm_res[i] == perm[perm_comb[i]]);
      invariant (forall i: int :: lo <= i && i < n ==> lo <= perm_res[i] && perm_res[i] <= hi);
      invariant (forall k, l: int :: lo <= k && k < l && l < n ==> perm_res[k] != perm_res[l]);
      invariant (forall i: int :: lo <= i && i <= hi ==> a_qs[i] == old(a_qs)[perm[perm_comb[i]]]);
    { 
      perm_res[n] := perm[perm_comb[n]];
      n := n+1;  
    }

    // write updated permutation back to perm
    perm := perm_res;
    
  } else {
    perm[lo] := lo;
  }

  // IMPORTANT: this assert is crutial for boogie to terminate
  assert (forall i: int :: lo <= i && i <= hi ==> a_qs[i] == old(a_qs)[perm[i]]);
}


procedure bucketSort(lo : int, hi : int) returns (perm: [int]int)
  modifies a,a_qs; //, b0, b1, b2;
  // only allow bucketsort to be called from [0..N-1]
  requires 0 <= lo && lo <= hi;
  // perm is a permutation
  ensures (forall k: int :: lo <= k && k <= hi ==> lo <= perm[k] && perm[k] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  ensures (forall k: int :: lo <= k && k <= hi ==> a[k] == old(a)[perm[k]]);
  // array is sorted
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi  ==> a[k] <= a[l]);
{
  
  //buckets' end indices
  var b0_i, off_b0:int;
  var b1_i, off_b1:int;
  var b2_i, off_b2:int;
  
  //buckets' upper bounds (exclusive)
  var bound_0:int;
  var bound_1:int;
  var bound_2:int;
  
  //bucket permutations
  var perm0, perm1, perm2 : [int]int;
  var permAtoB0 : [int]int;
  var permAtoB1 : [int]int;
  var permAtoB2 : [int]int;
  var permA : [int]int;

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
    invariant i-lo == b0_i+b1_i+b2_i; 
    //all buckets contain the correct kind of elements:
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] < -1*N));
    invariant(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] >= -1*N && b1[e] < N));
    invariant(forall e:int :: (e >= 0 && e < b2_i) ==> (b2[e] >= N));
    
    //permAtoB holds the mapping of elements from A onto the buckets
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permAtoB0[e]]));
    invariant(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] == a[permAtoB1[e]]));
    invariant(forall e:int :: (e >= 0 && e < b2_i) ==> (b2[e] == a[permAtoB2[e]]));
    
    invariant (forall k: int :: 0 <= k && k < b0_i ==> lo <= permAtoB0[k] && permAtoB0[k] <= hi);
    invariant (forall k: int :: 0 <= k && k < b1_i ==> lo <= permAtoB1[k] && permAtoB1[k] <= hi);
    invariant (forall k: int :: 0 <= k && k < b2_i ==> lo <= permAtoB2[k] && permAtoB2[k] <= hi);
    
    //every element is permuted
    invariant (forall k: int :: 0 <= k && k < b0_i ==> permAtoB0[k] < i);
    invariant (forall k: int :: 0 <= k && k < b1_i ==> permAtoB1[k] < i);
    invariant (forall k: int :: 0 <= k && k < b2_i ==> permAtoB2[k] < i);
    
    invariant(forall e,f : int :: ((e >= 0 && e < b0_i && e != f && f >= 0 && f < b0_i) ==> (permAtoB0[e] != permAtoB0[f])));
    invariant(forall e,f : int :: ((e >= 0 && e < b1_i && e != f && f >= 0 && f < b1_i) ==> (permAtoB1[e] != permAtoB1[f])));
    invariant(forall e,f : int :: ((e >= 0 && e < b2_i && e != f && f >= 0 && f < b2_i) ==> (permAtoB2[e] != permAtoB2[f])));
    
    invariant(forall e,f : int :: ((e >= 0 && e < b0_i && f >=0 && f < b1_i) ==> (permAtoB0[e] != permAtoB1[f])));
    invariant(forall e,f : int :: ((e >= 0 && e < b0_i && f >=0 && f < b2_i) ==> (permAtoB0[e] != permAtoB2[f])));
    invariant(forall e,f : int :: ((e >= 0 && e < b1_i && f >=0 && f < b2_i) ==> (permAtoB1[e] != permAtoB2[f])));
  {
    //add a[i] to correct bucket
    if(a[i] < bound_1){
      if(a[i] < bound_0){
        b0[b0_i] := a[i];
        permAtoB0[b0_i] := i;
        
        b0_i := b0_i + 1;
      }
      else{
        b1[b1_i] := a[i];
        permAtoB1[b1_i] := i;
        
        b1_i := b1_i + 1;
      }
    }
    else{
      b2[b2_i] := a[i];
      permAtoB2[b2_i] := i;
        
      b2_i := b2_i + 1;
    }
    i := i + 1;
  }
  
  i := 0;
  while(i < b0_i)
    invariant (i >= 0 && i <= b0_i);
    invariant(forall e:int :: (e >= 0 && e < i) ==> (b0[e] == a[permA[e]]));
    invariant (forall k: int :: 0 <= k && k < i ==> lo <= permA[k] && permA[k] <= hi);
    
    invariant (forall e:int :: (e >=0 && e < i ==> permA[e] == permAtoB0[e]));
    invariant (forall e,f:int :: (e >= 0 && e < f && f < i ==> permA[e] != permA[f]));
  {
    permA[i] := permAtoB0[i];
    i := i + 1;
  }
  
  i := 0;
  while(i < b1_i)
    invariant(i >= 0 && i <= b1_i);
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
    invariant(forall e:int :: (e >= 0 && e < i) ==> (b1[e] == a[permA[e + b0_i]]));
    invariant (forall k: int :: 0 <= k && k < b0_i ==> lo <= permA[k] && permA[k] <= hi);
    invariant (forall k: int :: b0_i <= k && k < i+b0_i ==> lo <= permA[k] && permA[k] <= hi);
    
    invariant(forall f:int :: (f >= b0_i && f < b0_i + i ==> permA[f] == permAtoB1[f-b0_i]));

    invariant(forall e:int :: (e >= 0 && e < b0_i + i ==> (permA[e] == permAtoB0[e] || permA[e] == permAtoB1[e-b0_i])));
    invariant (forall e,f:int :: (e >= 0 && e < i+ b0_i && e != f && f >= 0 && f < i + b0_i ==> permA[e] != permA[f]));
  {
    permA[i+b0_i] := permAtoB1[i];
    i := i + 1;
  }
  
  i := 0;
  while(i < b2_i)
    invariant(i >= 0 && i <= b2_i);
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
    invariant(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] == a[permA[e + b0_i]]));
    invariant(forall e:int :: (e >= 0 && e < i) ==> (b2[e] == a[permA[e + b0_i + b1_i]]));
    invariant (forall k: int :: 0 <= k && k < b0_i ==> lo <= permA[k] && permA[k] <= hi);
    invariant (forall k: int :: b0_i <= k && k < b1_i+b0_i ==> lo <= permA[k] && permA[k] <= hi);
    invariant (forall k: int :: b0_i + b1_i <= k && k < b0_i + b1_i + i ==> lo <= permA[k] && permA[k] <= hi);
    
    invariant(forall f:int :: (f >= b0_i+b1_i && f < b0_i + b1_i + i ==> permA[f] == permAtoB2[f-b0_i-b1_i]));
    invariant(forall e:int :: (e >= 0 && e < b0_i + b1_i + i ==> (permA[e] == permAtoB0[e] || permA[e] == permAtoB1[e-b0_i] || permA[e] == permAtoB2[e-b1_i-b0_i])));
    
    invariant (forall e,f:int :: (e >= 0 && e < b1_i+ b0_i && e != f && f >= 0 && f < b1_i + b0_i ==> permA[e] != permA[f]));
    invariant (forall e,f:int :: (e >= 0 && e < i+ b1_i + b0_i && e != f && f >= 0 && f < i + b1_i + b0_i ==> permA[e] != permA[f]));
  {
    permA[i + b0_i + b1_i] := permAtoB2[i];
    i := i + 1;
  }
  
  // index mapping from bucket indexes to array indexes 
  off_b0 := lo + b0_i; // end index of bucket0 in a (exclusive)
  off_b1 := lo + b0_i + b1_i; // end index of bucket1 in a (exclusive)
  off_b2 := lo + b0_i + b1_i + b2_i; // end index of bucket2 in a (exclusive)
  
  // sort all buckets
  if(b0_i > 0) { call b0_sorted, perm0 := quickSort(b0, 0, b0_i-1); }
  if(b1_i > 0) { call b1_sorted, perm1 := quickSort(b1, 0, b1_i-1); }
  if(b2_i > 0) { call b2_sorted, perm2 := quickSort(b2, 0, b2_i-1); }

  i := lo;
  while(i < off_b0)
    // bucket values are copied to a
    invariant (forall k: int :: lo <= k && k < i ==> a[k] == b0_sorted[k-lo]);
    invariant (forall k: int :: lo <= k && k < i ==> a[k] == old(a[perm[k]]));
    invariant (forall k: int :: lo <= k && k < i ==> lo <= perm[k] && perm[k] <= hi);
    
    invariant(forall f:int ::(f >= lo && f < i ==> perm[f] == permA[perm0[f-lo]]));
    invariant(forall e,f:int :: (e >= lo && e < i && e != f && f >= lo && f < i ==> perm[e] != perm[f]));
  {
    a[i] := b0_sorted[i-lo];
    perm[i] := permA[perm0[i-lo]];
    i := i + 1;
  }

  // copy back elements from bucket to array
  i := off_b0;
  while(i < off_b1)
    // needed to ensure that only this part of array is modified
    invariant off_b0 <= i && i <= off_b1; 
    // previous knowledge about a is preserved
    invariant (forall k: int :: lo <= k && k < off_b0 ==> a[k] == b0_sorted[k-lo]);
    // bucket values are copied to a
    invariant (forall k: int :: off_b0 <= k && k < i ==> a[k] == b1_sorted[k-off_b0]);
    
    //permutation
    invariant (forall k: int :: lo <= k && k < off_b0 ==> a[k] == old(a[perm[k]]));
    invariant (forall k: int :: off_b0 <= k && k < i ==> a[k] == old(a[perm[k]]));
    invariant (forall k: int :: lo <= k && k < off_b0 ==> lo <= perm[k] && perm[k] <= hi);
    invariant (forall k: int :: off_b0 <= k && k < i ==> lo <= perm[k] && perm[k] <= hi);
    
    invariant(forall f:int ::(f >= off_b0 && f < i ==> perm[f] == permA[perm1[f-b0_i-lo] + b0_i]));
    invariant(forall e,f:int :: (e >= lo && e < i && e != f && f >= lo && f < i ==> perm[e] != perm[f]));
  {
    a[i] := b1_sorted[i-off_b0];
    perm[i] := permA[perm1[i-b0_i-lo] + b0_i];
    i := i + 1;
  }
  
  i := off_b1;
  while(i < off_b2)
    // needed to ensure that only this part of array is modified
    invariant off_b1 <= i && i <= off_b2; 
    // previous knowledge about a is preserved
    invariant (forall k: int :: lo <= k && k < off_b0 ==> a[k] == b0_sorted[k-lo]);
    invariant (forall k: int :: off_b0 <= k && k < off_b1 ==> a[k] == b1_sorted[k-off_b0]);
    // bucket values are copied to a
    invariant (forall k: int :: off_b1 <= k && k < i ==> a[k] == b2_sorted[k-off_b1]);
    
    //permutation
    invariant (forall k: int :: lo <= k && k < off_b0 ==> a[k] == old(a[perm[k]]));
    invariant (forall k: int :: off_b0 <= k && k < off_b1 ==> a[k] == old(a[perm[k]]));
    invariant (forall k: int :: off_b1 <= k && k < i ==> a[k] == old(a[perm[k]]));
    invariant (forall k: int :: lo <= k && k < off_b0 ==> lo <= perm[k] && perm[k] <= hi);
    invariant (forall k: int :: off_b0 <= k && k < off_b1 ==> lo <= perm[k] && perm[k] <= hi);
    invariant (forall k: int :: off_b1 <= k && k < i ==> lo <= perm[k] && perm[k] <= hi);
    
    invariant(forall f:int ::(f >= off_b1 && f < i ==> perm[f] == permA[perm2[f-b0_i-b1_i-lo] + b0_i + b1_i]));
    invariant(forall e,f:int :: (e >= lo && e < i && e != f && f >= lo && f < i ==> perm[e] != perm[f]));
  {
    a[i] := b2_sorted[i-off_b1];
    perm[i] := permA[perm2[i-b0_i-b1_i-lo] + b0_i + b1_i];
    i := i + 1;
  }
}

