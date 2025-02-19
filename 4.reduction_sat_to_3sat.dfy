/************************
INSTANCE TYPE DECLARATION
************************/
type clause = seq<int>
type Formula = seq<clause>
// Note: Each formula is in CNF.
// From now on V denotes a number of variables. Forall variable x: 1 <= x <= V.
// We assume that any CNF cannot contain empty clauses. 

/*************************
TYPE DEFINITION PREDICATES
*************************/

// Auxiliary function that calculates the absolute value of an integer.
function abs(i: int): int
{
    if i >= 0 then i
    else -i
}

// This predicate guarantees that a clause is nonempty and all its variables are in [1..V].
predicate valid_clause(V: nat, cla: clause)
{
    |cla| > 0 && (forall n:nat :: n < |cla| ==> 1 <= abs(cla[n]) <= V && cla[n] != 0)
}


// This predicate guarantees that all clauses in a CNF are valid.
// In addition, we assume that any CNF has at least one clause. 
predicate valid_formula(V: nat, f: Formula)
{    
    forall n: nat :: n < |f| ==> valid_clause(V, f[n])
}


// An assignment "assig" is a sequence of boolean values where 
// forall i in [1..V], the value of variable i is assig[i]. 
predicate valid_assignment(V: nat, assig: seq<bool>)   
{
    |assig| == V+1
}


// This predicate guarantees that each clause in a CNF has exactly three literal.
predicate is3CNF(V: nat, f: Formula)
    requires valid_formula(V, f)
{
    forall n:nat :: n < |f| ==> |f[n]| == 3
}


/******************
PROBLEM DEFINITIONS
*******************/

// This predicate guarantees that a literal in a clause makes the clause true.
predicate good_literal(V: nat, l: int, cla: clause, assig: seq<bool>)
    requires valid_clause(V, cla)
    requires valid_assignment(V, assig)
    
{
    l in cla && (assig[abs(l)] <==> l > 0)
}


// This predicate guarantees that an assignment is a model for a clause.
predicate model_clause(V: nat, cla: clause, assig: seq<bool>)
    requires valid_clause(V, cla)
    requires valid_assignment(V, assig)
{
    exists l: int :: l in cla && good_literal(V, l, cla, assig)
}


// This predicate guarantees that an assignment is a model for a CNF.
predicate model(V: nat, f: Formula, assig: seq<bool>)
    requires valid_formula(V, f)
    requires valid_assignment(V, assig)
{
    forall n:nat :: n < |f| ==> model_clause(V, f[n], assig)
}


lemma model_Lemma(V: nat, f: Formula, assig: seq<bool>)
    requires valid_formula(V, f)
    requires valid_assignment(V, assig)
    ensures |f| > 1 ==> (model(V, f, assig) ==> model(V, f[1..], assig))
{}



// This predicate guarantees that a CNF is satisfiable.
ghost predicate isSat(V:nat, f: Formula)
    requires valid_formula(V, f)
{
    exists assig: seq<bool>:: valid_assignment(V, assig) && model(V, f, assig) 
}



/***************
REDUCTION: INDEPENDENT-SET <=p VERTEX-COVER
****************/

//// REDUCTION FUNCTION ////

// Transforms a clause containing a single literal into an
// "equivalent" clause with exactly three literals. 
ghost function from1To3(V: nat, cla: clause): (int, Formula)
    requires |cla| == 1
    requires valid_clause(V, cla)
    ensures var (newV, newCNF):= from1To3(V, cla); 
    (
        valid_formula(newV, newCNF) &&
        is3CNF(newV, newCNF) &&
        newCNF[0] == cla + [V+1, V+2] &&
        newCNF[1] == cla + [V+1, -(V+2)] &&
        newCNF[2] == cla + [-(V+1), V+2] &&
        newCNF[3] == cla + [-(V+1), -(V+2)] &&
        newV > V
    )
{
    (V+2, 
            [cla + [V+1, V+2]] + 
            [cla + [V+1, -(V+2)]] + 
            [cla + [-(V+1), V+2]] +
            [cla + [-(V+1), -(V+2)]]
    )
}


// This function transforms a clause containing two literals into an
// "equivalent" clause with exactly three literals. 
ghost function from2To3(V: nat, cla: clause): (int, Formula)
    requires |cla| == 2
    requires valid_clause(V, cla)
    ensures var (newV, newCNF):= from2To3(V, cla); 
    (
        valid_formula(newV, newCNF) &&
        newV > V &&
        is3CNF(newV, newCNF) &&
        newCNF[0] == cla + [V+1] &&
        newCNF[1] == cla + [-(V+1)] 
    )
{
    (V+1, 
            [cla + [V+1]] + 
            [cla + [-(V+1)]]
        )
}


// This function transforms a clause containing a n > 3 literals into an
// "equivalent" clause with exactly three literals. 
ghost function fromNTo3(V: nat, cla: clause): (int, Formula)
    requires |cla| > 3
    requires valid_clause(V, cla)
    ensures var (newV, newCNF):= fromNTo3(V, cla); var n:= |cla|; 
    (
        valid_formula(newV, newCNF) && 
        is3CNF(newV, newCNF) &&
        newV == V+|cla|-3  &&
        |newCNF| == |cla|-2 && newV > V &&
        newCNF[0] == [cla[0], cla[1], V+1] &&
        newCNF[n-3] == [cla[n-2], cla[n-1], -newV] &&
        forall m: nat :: 1 <= m < n-3 ==> newCNF[m] == [cla[m+1], -(V+m), V+m+1] 
    )
{   
    var n:= |cla|;
    if n == 4 then (V+1, [cla[..2] + [V+1]] + [cla[n-2..] + [-(V+1)]])
    else var (newV, newF):= add_two_new_literals(V+1, cla[2..n-2]);
         (newV, [cla[..2] + [V+1]] + newF + [cla[n-2..] + [-newV]]) 
}


ghost function add_two_new_literals(V: nat, cla: clause): (int, Formula)
    requires |cla| > 0
    requires valid_clause(V, cla)
    decreases |cla|
    ensures var (newV, newCNF):= add_two_new_literals(V, cla);
    (       
        valid_formula(newV, newCNF) &&
        |newCNF| == |cla| && newV ==  V + |cla| && 
        is3CNF(newV, newCNF) && 
        forall i: nat :: 0 <= i < |newCNF| ==> newCNF[i] == [cla[i], -(V+i), V+i+1]
    )
{
    var x: int := V as int;
    if |cla| == 1 then (V+1, [[cla[0], -x,  V+1]])
    else var (newV, newF):= add_two_new_literals(V+1, cla[1..]);
        (newV, [[cla[0], -x, V+1]] + newF)

}


// Generalization of previous cases.
ghost function clauseTo3CNF(V: nat, cla: clause): (int, Formula)
    requires valid_clause(V, cla)
    ensures var (newV, newCNF):= clauseTo3CNF(V, cla); 
    (
        valid_formula(newV, newCNF) &&
        newV >= V &&
        is3CNF(newV, newCNF) &&
        |cla| == 1 ==> newV == V+2 && |newCNF| == 4 &&
        |cla| == 2 ==> newV == V+1 && |newCNF| == 2 &&
        |cla| == 3 ==> newV == V && |newCNF| == 1 &&
        |cla| > 3 ==> newV == V+|cla|-3 && |newCNF| == |cla|-2 
    )
{ 
    if |cla| == 1 then from1To3(V, cla)
    else if |cla| == 2 then from2To3(V, cla)
    else if |cla| == 3 then (V, [cla])
    else fromNTo3(V, cla)
}


// Final function.
ghost function sat_to_3sat(V: nat, f: Formula): (int, Formula)
    requires valid_formula(V, f)
    ensures var (newV, newF):= sat_to_3sat(V, f);
    ( 
        valid_formula(newV, newF) &&
        newV >= V &&
        is3CNF(newV, newF)
    )
    decreases |f|    
{
    if |f| == 0 then (V, [])
    else var (newV1, newCNF):= clauseTo3CNF(V, f[0]); 
         var (newV2, newF):= sat_to_3sat(newV1, f[1..]); 
         (newV2, newCNF + newF) 
}


//// REDUCTION CORRECTNESS ////

lemma reduction_Lemma(V: nat, f: Formula)
    requires valid_formula(V, f)
    ensures var (newV, newF):= sat_to_3sat(V, f); 
        isSat(V, f) <==>  isSat(newV, newF) 
{
    var newF:= sat_to_3sat(V, f); 
    if isSat(V, f)
    {
        forward_Lemma(V, f);
    }
    if isSat(newF.0, newF.1) 
    {
        backward_Lemma(V, f);
    }
}

// Reduction forward: isSat(F) ==> isSat(f(F))

lemma forward_Lemma(V: nat, f: Formula)
    requires valid_formula(V, f)
    requires isSat(V, f) 
    ensures var (newV, newF):= sat_to_3sat(V, f);  isSat(newV, newF) 
{
    var  assig: seq<bool>:| valid_assignment(V, assig) && model(V, f, assig);
    var  lassig: seq<bool>:= larger_good_assignment(V, f, assig);
}

// Reduction backward: isSat(f(F)) ==> isSat(F)

lemma backward_Lemma(V: nat, f: Formula)
    requires valid_formula(V, f)
    requires var (newV, newF):= sat_to_3sat(V, f); isSat(newV, newF) 
    ensures isSat(V, f) 
{
    var (newV, newF):= sat_to_3sat(V, f); 
    var lassig: seq<bool>:| valid_assignment(newV, lassig) && model(newV, newF, lassig);
    sat_to_3sat_Lemma(V, f, lassig); 
}


// Auxiliarys for forward_Lemma

/// This function increases 'assig' in such a way that forall x: nat::  first+1 <= x last+1  ==> assig[x] == value 
ghost function increase_assignment(first: nat, last: nat, assig: seq<bool>, value:bool) : seq<bool>
    requires first == |assig|-1
    requires first  <= last
    ensures var iassig:= increase_assignment(first, last, assig, value); 
        assig <= iassig && |iassig| == last+1
    ensures var iassig:= increase_assignment(first, last, assig, value);
        forall x: nat :: |assig| < x <= last ==> iassig[x] == value
    decreases last-first
{
    if first == last then assig
    else increase_assignment(first+1, last, assig + [value], value)
}


// This function constructs a larger assignment 'lassig' from 'assig' in such a way that 
// model_clause(V, cla, assig) <==> lassig is a model for the transformation fromNTo3(V, cla).
ghost function larger_good_assignment_clause(V: nat, cla: clause, assig: seq<bool>): seq<bool>
    requires |cla| > 3
    requires valid_assignment(V, assig)
    requires valid_clause(V, cla)
    requires model_clause(V, cla, assig)
    ensures var lassig:= larger_good_assignment_clause(V, cla, assig);
            var (newV, newCNF):= fromNTo3(V, cla);
                assig <= lassig && 
                valid_assignment(newV, lassig) &&
                model(newV, newCNF, lassig)
{
    var n:= |cla|-2;
    var (newV, newCNF):= fromNTo3(V, cla);
    var i:nat :| 0 <= i < |cla| && good_literal(V, cla[i], cla, assig);
    if i < 2 then
        var lassig:= increase_assignment(V, newV,  assig, false);
        assert forall m: nat :: 1 <= m < n ==> 
            (-(V+m) in newCNF[m] && good_literal(newV, -(V+m), newCNF[m], lassig));
        assert good_literal(newV, cla[i], newCNF[0], lassig);
        lassig
    
    else if i > n-1 then
        var lassig:= increase_assignment(V, newV, assig, true);
        assert forall m: nat :: 0 <= m < n-1 ==> 
            (V+m+1 in newCNF[m] && good_literal(newV, V+m+1, newCNF[m], lassig));
        assert good_literal(newV, cla[i], newCNF[n-1], lassig);
        lassig
    else
        var lassig_true:= increase_assignment(V, V+i-1,assig, true);
        var lassig:= increase_assignment(V+i-1, newV, lassig_true, false);
        // assert valid_assignment(newV, lassig) && assig <= lassig_true <= lassig;
        assert forall m: nat :: i <= m <= n-1 ==> 
            (-(V+m) in newCNF[m] && good_literal(V+n-1, -(V+m), newCNF[m], lassig));
        assert forall m: nat :: i <= m <= n-1 ==> model_clause(newV, newCNF[m], lassig);
        assert forall m: nat :: 0 <= m < i-1 ==> 
            (V+m+1 in newCNF[m] && good_literal(newV, V+m+1, newCNF[m], lassig));
        assert good_literal(newV, cla[i], newCNF[i-1], lassig);
        lassig
}


// This function constructs a larger assignment 'lassig' from 'assig' in such a way that 
// model(V, f, assig) <==> lassig is a model for the reduction sat_to_3sat(V, f).
ghost function larger_good_assignment(V: nat, f: Formula, assig: seq<bool>): seq<bool>
    requires valid_formula(V, f)
    requires valid_assignment(V, assig)
    requires model(V, f, assig)
    decreases |f|
    ensures var (newV, newF):= sat_to_3sat(V, f);
            var lassig:= larger_good_assignment(V, f, assig);
            assig <= lassig &&
            valid_assignment(newV, lassig) &&
            model(newV, newF, lassig) 
{
    if |f| == 0 then assig
    else if |f[0]| == 1 then 
        var iassig:= assig + [true, true];
        from1To3_Lemma(V, f[0], assig);
        larger_good_assignment(V+2, f[1..], iassig) 
    else if |f[0]| == 2 then 
        var iassig:= assig + [true];
        from2To3_Lemma(V, f[0], assig);
        larger_good_assignment(V+1, f[1..], iassig)
    else if |f[0]| == 3 then
        larger_good_assignment(V, f[1..], assig)
    else var iassig:= larger_good_assignment_clause(V, f[0], assig);
        var (newV, newCNF):= fromNTo3(V, f[0]); 
        larger_good_assignment(newV, f[1..], iassig)
             
}


// This lema proves that if a 1clause has a model, then the same model, plus 
// assigning the true value to the variables added by the transformation from1To3,
// is also a model for the 3CNF obtained by that tranformation. 
lemma from1To3_Lemma(V: nat, cla: clause, assig: seq<bool>)
    requires |cla| == 1
    requires valid_assignment(V, assig)
    requires valid_clause(V, cla)
    requires model_clause(V, cla, assig)
    ensures var (newV, newCNF):= from1To3(V, cla);
        valid_assignment(newV, assig + [true, true]) && 
        model(newV, newCNF, assig + [true, true])
{
    var l:|  l in cla && good_literal(V, l, cla, assig);
    var (newV, newCNF):= from1To3(V, cla); 
    assert forall i:: 0 <= i <= 3 ==> 
        good_literal(newV, l, newCNF[i],  assig + [true, true]);
}

// This lema proves that if a 1clause has a model, then the same model, plus 
// assigning the true value to the variable added by the transformation from2To3,
// is also a model for the 3CNF obtained by that tranformation. 
lemma from2To3_Lemma(V: nat, cla: clause, assig: seq<bool>)
    requires |cla| == 2
    requires valid_assignment(V, assig)
    requires valid_clause(V, cla)
    requires model_clause(V, cla, assig)
    ensures var (newV, newCNF):= from2To3(V, cla); 
        valid_assignment(newV, assig + [true]) && 
        model(newV, newCNF, assig + [true])
{
    var l:|  l in cla && good_literal(V, l, cla, assig);
    var (newV, newCNF):= from2To3(V, cla); 
    assert good_literal(newV, l, newCNF[0], assig + [true]);
    assert good_literal(newV, l, newCNF[1], assig + [true]);
}


// Auxiliary for backward_Lemma.

// This function looks for the first false of an assignment. 
// It is used in the next lemma. 
ghost function first_false(V: nat, W: nat, assig: seq<bool>): nat
    requires 1 <= V < W <= |assig|-1
    ensures first_false(V, W, assig) <= W
    ensures first_false(V, W, assig) == 0 || first_false(V, W, assig) >= V
    ensures first_false(V, W, assig) == 0  <==> 
        forall x: int :: V < x <= W ==> assig[x] == true 
    ensures first_false(V, W, assig) >= V ==>
        (forall x: int :: V < x < first_false(V, W,  assig) ==> assig[x] == true) &&
        assig[first_false(V, W, assig)] == false
    decreases W-V
     
{
    if assig[V+1] == false then V+1
    else if V+1 == W && assig[V+1] == true then 0
    else first_false(V+1, W,  assig)
}



// This lema proves that if the 3CNF obtained by the transformation fromNTo3
// applied to an n > 3 clause has a model 'lassig', then lassig[..V+1] is also a model for the original n > 3 clause.
// The proof is by contradiction.
lemma fromNTo3_Lemma(V: nat, cla: clause, lassig: seq<bool>)
    requires |cla| > 3
    requires valid_clause(V, cla)
    requires var (newV, newCNF):= fromNTo3(V, cla); valid_assignment(newV, lassig)
    requires var (newV, newCNF):= fromNTo3(V, cla); model(newV, newCNF, lassig)
    decreases |cla|
    ensures valid_assignment(V, lassig[..V+1]) && model_clause(V, cla, lassig[..V+1])
{
    var (newV, newCNF):= fromNTo3(V, cla);
    var n:= |cla|-2;
   
    if forall j:nat, i: nat  :: 
    ( (0 <= j < |cla| && 0 <= i < n  && cla[j] in newCNF[i])  ==> 
        !good_literal(newV, cla[j], newCNF[i], lassig)
    )
    {
        var x:= first_false(V, newV, lassig);
        if 1 <= x <= newV
        {
            var i:= x-V-1;
            assert newCNF[i] == [cla[i+1], -(V+i), V+i+1]; 
            assert false;
        }
    }
    else
    {
        var j, i :|
        ( 
            (0 <= j < |cla| && 0 <= i < n  && cla[j] in newCNF[i]) &&
            good_literal(newV, cla[j], newCNF[i], lassig)
        );
        assert cla[j] in cla && good_literal(V, cla[j], cla, lassig[..V+1]);
    }
}



// The sat_to_3sat_Lemma(V, f, lassig) proves that if the 3CNF obtained by the reduction 
// sat_to_3sat(V, f, lassig) has a model 'lassig', then the assignment lassig[..V+1] is a model for f.
lemma sat_to_3sat_Lemma(V: nat, f: Formula, lassig: seq<bool>)
    requires valid_formula(V, f)
    requires var (newV, newF):= sat_to_3sat(V, f); 
        valid_assignment(newV, lassig) && model(newV, newF, lassig)
    decreases |f|
    ensures valid_assignment(V, lassig[..V+1]) && model(V, f, lassig[..V+1])
{
    if |f| > 0
    {
            var (newV1, newCNF):= clauseTo3CNF(V, f[0]);
            var (newV2, newF):= sat_to_3sat(newV1, f[1..]);
            assert sat_to_3sat(V, f) ==  (newV2, newCNF + newF);
            assert newV2 >= newV1;
            assert |lassig| == newV2+1;
            model_Lemma(newV2, newF, lassig);
        if
        case |f[0]| == 1 =>
            assert newV1 == V+2;
            assert newCNF == (newCNF + newF)[..4];
            assert lassig[..V+3] <= lassig;
            assert model(newV1, newCNF, lassig[..V+3]);
            // sat_to_3sat_Lemma(newV1, f[1..], lassig);
            assert model(newV2, newF, lassig);
        case |f[0]| == 2 =>
            assert newV1 == V+1;
            assert newCNF == (newCNF + newF)[..2];
            assert lassig[..V+2] <= lassig;
            assert model(newV1, newCNF, lassig[..V+2]);
            // sat_to_3sat_Lemma(newV1, f[1..], lassig);
            assert model(newV2, newF, lassig);
        case |f[0]| == 3 =>
            assert newV1 == V;
            assert newCNF == (newCNF + newF)[..1] == [f[0]];
            assert lassig[..V+1] <= lassig;
            assert model(V, newCNF, lassig[..V+1]);
            assert valid_assignment(V, lassig[..V+1]);
            // sat_to_3sat_Lemma(V, f[1..], lassig);
            assert model(newV2, newF, lassig);
        case |f[0]| > 3 =>
            assert |f[0]| > 3;
            assert (newV1, newCNF) ==  clauseTo3CNF(V, f[0]) == fromNTo3(V, f[0]);
            assert newV1 == V+|f[0]|-3;
            assert newCNF == (newCNF + newF)[..|f[0]|-2];
            assert  lassig[.. V+|f[0]|-2] <= lassig;
            assert model(newV1, newCNF, lassig[..V+|f[0]|-2]);
            fromNTo3_Lemma(V, f[0], lassig[.. V + |f[0]|-2]);
            assert model_clause(V, f[0],  lassig[.. V + |f[0]|-2][..V+1]);
            assert lassig[..V + |f[0]|-2][..V+1] ==  lassig[..V+1];
            assert model_clause(V, f[0], lassig[..V+1]);
            //sat_to_3sat_Lemma(newV1, f[1..], lassig);
            assert model(newV2, newF, lassig);
    }
}

//310 code lines
