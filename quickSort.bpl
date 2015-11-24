// Introduce a constant 'N' and postulate that it is non-negative
const N: int;
axiom 0 <= N;

// internal variable that is used by quicksort implementation
var a_qs:  [int]int;

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


