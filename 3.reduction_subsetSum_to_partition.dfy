// This function calculates the sum of the elements in a sequence.
function sum_seq(s:seq<int>): int
{
	if |s| == 0 then 0
	else if |s| == 1 then s[0]
	else s[0] + sum_seq(s[1..])
}


// This function creates a sequence from a multiset.
ghost function seq_from_multiset(ms:multiset<int>): seq<int>
	ensures multiset(seq_from_multiset(ms)) == ms
	
{
	if ms == multiset{} then [] else 
		var i:| i in ms; 
		[i] + seq_from_multiset(ms - multiset{i})
}


// SubsetSum decision problem.
ghost predicate subsetSum(t:int, r:seq<int>)
{
	exists s:seq<int>:: multiset(s) <= multiset(r) && sum_seq(s) == t
}


// Partition decisionn problem.
ghost predicate partition(r:seq<int>)
{
	exists s:seq<int>:: multiset(s) <= multiset(r)  && sum_seq(r) == 2*sum_seq(s)
}


/**
The reduction: Subsetsum <=p Partition
**/


// Reduction function
function subSet2Partition(t:int, r:seq<int>): seq<int>
{
	r + [sum_seq(r) - 2*t]
}


//Reduction correctness
lemma reduction_Lemma  (t:int, r:seq<int>)
	ensures subsetSum(t, r) <==> partition(subSet2Partition(t, r)) 
{
	if subsetSum(t, r) 
	{
		forward_Lemma(t, r);
	}
	if partition(subSet2Partition(t, r))
	{
		backward_Lemma(t, r);
	}
}


lemma forward_Lemma (t:int, r:seq<int>)
	requires subsetSum(t, r) 
	ensures partition(subSet2Partition(t, r)) 

{	
	general_distributive_Lemma();
	var s: seq<int> :|  multiset(s) <= multiset(r) && sum_seq(s) == t;
	var ns: seq<int> := s + [sum_seq(r) - 2*t];
	assert 2*sum_seq(ns) == sum_seq(subSet2Partition(t, r));
}


lemma backward_Lemma (t:int, r:seq<int>)
	requires partition(subSet2Partition(t, r)) 
	ensures subsetSum(t, r)

{	
	general_distributive_Lemma();
	var i: int := sum_seq(r) - 2*t;
	var nr: seq<int> := subSet2Partition(t, r);
	var s: seq<int> :| multiset(s) <= multiset(nr)  && sum_seq(nr) == 2*sum_seq(s);	
	if i !in multiset(s)
	{
		var sm: seq<int> := seq_from_multiset(multiset(r) - multiset(s));
		same_sum_Lemma(sm + s, r); 
	}
	else
	{
		
		var sm: seq<int> := seq_from_multiset(multiset(s) - multiset{i}); 
		same_sum_Lemma(sm + [i], s);
		
	}
}


///// Auxiliar lemmas for sequences and multisets //////////////////////

lemma distributive_Lemma(s:seq<int>, r:seq<int>)
	ensures sum_seq(s + r) == sum_seq(s) + sum_seq(r)
{
	if s == [] 
	{ 
		assert s + r == r;
	}
	else
	{
		assert s + r == [s[0]] + (s[1..] + r);
	}
}

lemma general_distributive_Lemma()
	ensures forall s,r :: sum_seq(s + r) == sum_seq(s) + sum_seq(r)
{
	forall s:seq<int>, r:seq<int>
	{
		distributive_Lemma(s, r);
	}
}

lemma same_sum_Lemma(s:seq<int>, r:seq<int>)
	requires multiset(r) == multiset(s)
	ensures sum_seq(r) == sum_seq(s)
{
	general_distributive_Lemma();
	if r != []
	{
		assert r == [r[0]] + r[1..];
		assert r[0] in multiset(s);
		var j :| 0 <= j < |s| && s[j] == r[0];
		assert s == s[..j] + [r[0]] + s[j+1..];
		var ss := s[..j] + s[j+1..];								
		assert multiset(ss) == multiset(s) - multiset{r[0]};
		same_sum_Lemma(ss, r[1..]);		
	}
}
