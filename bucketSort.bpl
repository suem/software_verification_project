const N: int;
axiom 0 <= N;

// Declare a map from integers to integers.
// 'a' should be treated as an array of 'N' elements, indexed from 0 to N-1
var a: [int]int;
// internal variable that is used by quicksort implementation
var a_qs:  [int]int;

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
  assume (forall i: int :: lo <= i && i <= hi ==> lo <= perm[i] && perm[i] <= hi);
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  // the final array is that permutation of the input array
  assume (forall i: int :: lo <= i && i <= hi ==> arr_sorted[i] == arr[perm[i]]);
  // array is sorted
  assume (forall k, l: int :: lo <= k && k <= l && l <= hi ==> arr_sorted[k] <= arr_sorted[l]);
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
  {
    a[i] := b0_sorted[i-lo];
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
  {
    a[i] := b1_sorted[i-off_b0];   
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
  {
    a[i] := b2_sorted[i-off_b1];   
    i := i + 1;
  }

  /*
  assert (forall k: int :: lo <= k && k < off_b0 ==> a[k] == b0_sorted[k-lo]);
  assert (forall k: int :: off_b0 <= k && k < off_b1 ==> a[k] == b1_sorted[k-off_b0]);
  assert (forall k: int :: off_b1 <= k && k < off_b2 ==> a[k] == b2_sorted[k-off_b1]);
  assert (forall k, l: int ::     lo <= k && k <= l && l < off_b0 ==> a[k] <= a[l]);
  assert (forall k, l: int :: off_b0 <= k && k <= l && l < off_b1 ==> a[k] <= a[l]);
  assert (forall k, l: int :: off_b1 <= k && k <= l && l < off_b2 ==> a[k] <= a[l]);
  */

  // now the array is sorted
  // assert (forall k, l: int ::     lo <= k && k <= l && l <= hi ==> a[k] <= a[l]);

  // TODO we still need to construct a permutation and prove these properties
  assume (forall k: int :: lo <= k && k <= hi ==> lo <= perm[k] && perm[k] <= hi);
  assume (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  assume (forall k: int :: lo <= k && k <= hi ==> a[k] == old(a)[perm[k]]);
}

