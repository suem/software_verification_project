procedure lemma_absurde(a : [int]int, b:[int]int, off : int, n : int) 
    requires off >= 0;
    requires n >= 0;
    requires (forall k: int :: 0 <= k && k < n ==> a[k+off] == b[k]);
    requires (forall k, l: int :: 0 <= k && k <= l && l < n ==> b[k] <= b[l]);
    ensures (forall k, l: int :: 0 <= k && k <= l && l < n ==> a[k+off] <= a[l+off]);
{
    assume (forall k, l: int :: 0 <= k && k <= l && l < n ==> a[k+off] <= a[l+off]);
}

procedure lemma(a : [int]int, b:[int]int, lo : int, hi : int, n : int) 
    requires hi-lo+1==n;
    requires n >= 0;
    requires (forall k: int :: lo <= k && k <= hi ==> a[k] == b[k-lo]);
    requires (forall k, l: int :: 0 <= k && k <= l && l < n ==> b[k] <= b[l]);
    ensures (forall k, l: int :: lo <= k && k <= l && l <= hi ==> a[k] <= a[l]);
{ }


