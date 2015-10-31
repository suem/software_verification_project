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
  var perm_rec: [int]int;

  if(lo < hi) {
    call pivot_index, perm := qsPartition(lo,hi);
    
    // we have a non empty left part
    if(lo < pivot_index-1) {
      call perm_rec := qs(lo, pivot_index - 1);
      // update permutation
      n := lo;
      while(n <= hi) 
        invariant (forall i: int :: lo <= i && i < n ==> lo <= perm[i] && perm[i] <= hi);
        invariant (forall i: int :: n <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
        // TODO add invariants
      { 
        if(perm[n] < pivot_index) {
          
          perm[n] := perm_rec[perm[n]];  
        }
        n := n+1;
      } 
    }     
    
    //assume pivot_index + 1 >= hi; // TODO for debugging 
    // we have a non empty right part
    if(pivot_index + 1 < hi) {
      call perm_rec := qs(pivot_index + 1, hi);
         
      n := lo;
      while(n <= hi) 
        invariant (forall i: int :: lo <= i && i < n ==> lo <= perm[i] && perm[i] <= hi);
        invariant (forall i: int :: n <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
        // TODO add invariants
      { 
        if(perm[n] > pivot_index) {
          perm[n] := perm_rec[perm[n]];  
        }
        n := n+1;
      } 
    }
    
  } else {
    perm[lo] := lo;
  }
  
  // TODO prove these
  
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  assume (forall i: int :: lo <= i && i <= hi ==> a[i] == old(a)[perm[i]]);
  
}

procedure bs(lo : int, hi : int) returns (perm: [int]int) 
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
  
  
}

