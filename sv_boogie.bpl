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
procedure sort() returns ()
  modifies a;
{
  if (has_small_elements(a))
  {
      // sort 'a' using bucket sort
  } else
  {
      // sort 'a' using quick sort
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


procedure test() 
  modifies a;
{
  var pp: [int]int;
  var x,a,b : int;
  assume a == b;
  call x, pp := qsPartition(a,b);
  assert x == a;
  assert pp[a] == a;
}


procedure qs(lo : int, hi : int) returns (perm: [int]int) 
  modifies a;
  requires lo <= hi;
 
  // perm is a permutation
  ensures (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  ensures (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  //ensures (forall i: int :: lo <= i && i <= hi ==> a[i] == old(a)[perm[i]]);
  
  // array is sorted
  ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> a[k] <= a[l]);

{
   // local variables
  var n, pivot_index, lo_l, hi_l, lo_r, hi_r : int;
  var perm_l, perm_r: [int]int;

  if(lo < hi) {
    call pivot_index, perm := qsPartition(lo,hi);
    lo_l := lo;
    hi_l := pivot_index - 1;
    lo_r := pivot_index + 1;
    hi_r := hi;
    

    assert (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
    
    // we have a non empty left part
    if(lo_l < hi_l) {
      call perm_l := qs(lo_l, hi_l);                
      n := lo_l;     
      while(n <= hi_l) 
        invariant hi_l < pivot_index;
        invariant lo <= pivot_index && pivot_index <= hi;
        invariant lo_l <= n && n <= hi_l+1;
        
        // preserve properties of perm_l 
        invariant (forall k: int :: lo <= k && k <= hi_l ==> lo <= perm_l[k] && perm_l[k] <= hi_l);
        invariant (forall k, l: int :: lo <= k && k < l && l < hi_l ==> perm_l[k] != perm_l[l]);
        
        // preserve properties of perm
        invariant (forall k: int :: lo <= k && k < n ==> lo <= perm[k] && perm[k] <= hi);
        invariant (forall k: int :: n <= k && k <= hi ==> lo <= perm[k] && perm[k] <= hi);
        
//        invariant (forall k, l: int :: lo <= k && k < l && l < n ==> perm[k] != perm[l]); // TODO fix this invariant
        invariant (forall k, l: int :: n <= k && k < l && l <= hi ==> perm[k] != perm[l]);
           
      {
        perm[n] := perm_l[n]; n := n+1;
      }
    }       
           
    // we have a non empty right part
    if(lo_r < hi_r) {
      call perm_r := qs(lo_r, hi_r);                
      n := lo_r;
      while(n <= hi_r) 
        // TODO add invariants for right side 
      {
        perm[n] := perm_r[n]; n := n+1;
      }
      
    }
    
  } else {
    perm[lo] := lo;
  }
  
}

S
