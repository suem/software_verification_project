const N: int;
axiom 0 <= N;

type Tuple t1 t1;

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
  
  assert(i == hi+1);
  assert(b0_i + b1_i + b2_i == hi-lo + 1);
  
  i := 0;
  while(i < b0_i)
    invariant (i >= 0 && i <= b0_i);
    invariant(forall e:int :: (e >= 0 && e < i) ==> (b0[e] == a[permA[e]]));
    invariant (forall k: int :: 0 <= k && k < i ==> lo <= permA[k] && permA[k] <= hi);
  {
    permA[i] := permAtoB0[i];
    i := i + 1;
  }
  
  assert(i == b0_i);
  assert(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
  
  i := 0;
  while(i < b1_i)
    invariant(i >= 0 && i <= b1_i);
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
    invariant(forall e:int :: (e >= 0 && e < i) ==> (b1[e] == a[permA[e + b0_i]]));
    invariant (forall k: int :: 0 <= k && k < b0_i ==> lo <= permA[k] && permA[k] <= hi);
    invariant (forall k: int :: b0_i <= k && k < i+b0_i ==> lo <= permA[k] && permA[k] <= hi);
  {
    permA[i+b0_i] := permAtoB1[i];
    i := i + 1;
  }
  
  assert (i == b1_i);
  assert(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
  assert(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] == a[permA[e + b0_i]]));
  
  i := 0;
  while(i < b2_i)
    invariant(i >= 0 && i <= b2_i);
    invariant(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
    invariant(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] == a[permA[e + b0_i]]));
    invariant(forall e:int :: (e >= 0 && e < i) ==> (b2[e] == a[permA[e + b0_i + b1_i]]));
    invariant (forall k: int :: 0 <= k && k < b0_i ==> lo <= permA[k] && permA[k] <= hi);
    invariant (forall k: int :: b0_i <= k && k < b1_i+b0_i ==> lo <= permA[k] && permA[k] <= hi);
    invariant (forall k: int :: b0_i + b1_i <= k && k < b0_i + b1_i + i ==> lo <= permA[k] && permA[k] <= hi);
  {
    permA[i + b0_i + b1_i] := permAtoB2[i];
    i := i + 1;
  }
  
  assert(i == b2_i);
  assert(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
  assert(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] == a[permA[e + b0_i]]));
  assert(forall e:int :: (e >= 0 && e < b2_i) ==> (b2[e] == a[permA[e + b0_i + b1_i]]));
  
  
  // index mapping from bucket indexes to array indexes 
  off_b0 := lo + b0_i; // end index of bucket0 in a (exclusive)
  off_b1 := lo + b0_i + b1_i; // end index of bucket1 in a (exclusive)
  off_b2 := lo + b0_i + b1_i + b2_i; // end index of bucket2 in a (exclusive)
  
  // sort all buckets
  if(b0_i > 0) { call b0_sorted, perm0 := quickSort(b0, 0, b0_i-1); }
  if(b1_i > 0) { call b1_sorted, perm1 := quickSort(b1, 0, b1_i-1); }
  if(b2_i > 0) { call b2_sorted, perm2 := quickSort(b2, 0, b2_i-1); }
  
  assert(forall e:int :: (e >= 0 && e < b0_i) ==> (b0[e] == a[permA[e]]));
  assert(forall e:int :: (e >= 0 && e < b1_i) ==> (b1[e] == a[permA[e + b0_i]]));
  assert(forall e:int :: (e >= 0 && e < b2_i) ==> (b2[e] == a[permA[e + b0_i + b1_i]]));
  
  assert(forall e:int :: (e >= 0 && e < b0_i) ==> (b0_sorted[e] == b0[perm0[e]]));
  assert(forall e:int :: (e >= 0 && e < b1_i) ==> (b1_sorted[e] == b1[perm1[e]]));
  assert(forall e:int :: (e >= 0 && e < b2_i) ==> (b2_sorted[e] == b2[perm2[e]]));
  
  assert(forall e:int :: (e >= 0 && e < b0_i) ==> (b0_sorted[e] == old(a[permA[perm0[e]]])));
  assert(forall e:int :: (e >= 0 && e < b1_i) ==> (b1_sorted[e] == old(a[permA[perm1[e] + b0_i]])));
  assert(forall e:int :: (e >= 0 && e < b2_i) ==> (b2_sorted[e] == old(a[permA[perm2[e] + b0_i + b1_i]])));
  
  assert(forall e:int :: (e >= lo && e < lo + b0_i) ==> (b0_sorted[e-lo] == old(a[permA[perm0[e-lo]]])));
  assert(forall e:int :: (e >= lo && e < lo + b1_i) ==> (b1_sorted[e-lo] == old(a[permA[perm1[e-lo] + b0_i]])));
  assert(forall e:int :: (e >= lo && e < lo + b2_i) ==> (b2_sorted[e-lo] == old(a[permA[perm2[e-lo] + b0_i + b1_i]])));
  
  assert(forall e:int :: (e >= lo && e <= hi) ==> (
    (e < b0_i ==> b0_sorted[e-lo] == old(a[permA[perm0[e-lo]]]))
    &&
    (e >= b0_i && e < b0_i + b1_i ==> (b1_sorted[e-b0_i] == old(a[permA[perm1[e-b0_i] + b0_i]])))
    &&
    (e >= b0_i + b1_i && e < b0_i + b1_i + b2_i ==> b2_sorted[e-b0_i-b1_i] == old(a[permA[perm2[e-b0_i-b1_i] + b0_i + b1_i]]))
    )
  );
  
   assert (forall k: int :: 0 <= k && k < b0_i ==> lo <= permA[k] && permA[k] <= hi);
    assert (forall k: int :: b0_i <= k && k < b1_i+b0_i ==> lo <= permA[k] && permA[k] <= hi);
    assert (forall k: int :: b0_i + b1_i <= k && k < b0_i + b1_i + b2_i ==> lo <= permA[k] && permA[k] <= hi);
   assert (forall k: int :: 0 <= k && k <= hi-lo ==> lo <= permA[k] && permA[k] <= hi);
  //assert(forall e:int :: (e >= lo && e <= hi) ==> ());

  i := lo;
  while(i < off_b0)
    // bucket values are copied to a
    invariant (forall k: int :: lo <= k && k < i ==> a[k] == b0_sorted[k-lo]);
    invariant (forall k: int :: lo <= k && k < i ==> a[k] == old(a[perm[k]]));
    invariant (forall k: int :: lo <= k && k < i ==> lo <= perm[k] && perm[k] <= hi);
  {
    a[i] := b0_sorted[i-lo];
    perm[i] := permA[perm0[i-lo]];
    i := i + 1;
  }

  assert(forall e:int :: (e >= lo && e <= hi) ==> (
      (e < off_b0 ==> a[e] == old(a[perm[e]]))
    )
  );

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
  {
    a[i] := b2_sorted[i-off_b1];
    perm[i] := permA[perm2[i-b0_i-b1_i-lo] + b0_i + b1_i];
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
  assert (forall k: int :: lo <= k && k <= hi ==> lo <= perm[k] && perm[k] <= hi);
  assert (forall k, l: int :: lo <= k && k < l && l <= hi ==> perm[k] != perm[l]);
  assert (forall k: int :: lo <= k && k <= hi ==> a[k] == old(a)[perm[k]]);
}

