
/************************
INSTANCE TYPE DECLARATION
************************/

type node = (nat, int)
type edge = (node, node)
datatype Graph = G(V: set<node>, E: set<edge>)
// The nodes of the graph are pairs of natural numbers. The first number identifies
// a clause of the CNF and the second one indentifies a literal of the clause

type clause = seq<int>
type Formula = seq<clause>
// Note: Each formula is in CNF.
// From now on V denotes a number of variables. Forall variable x: 1 <= x <= V.
// We assume that any CNF cannot contain empty clauses. 

/*************************
TYPE DEFINITION PREDICATES
*************************/

predicate well_ordered_pair(u: node, v: node)
{
    (u.0 < v.0) || ((u.0 == v.0) && (u.1 < v.1))
}

// This predicate guarantees that the edges are ordered pairs of nodes in V.
ghost predicate valid_graph(g: Graph)
{
    forall u, v: node :: 
        (u, v) in g.E ==> u in g.V && v in g.V && well_ordered_pair(u, v)
}


/******************
PROBLEM DEFINITIONS
*******************/

//// CLIQUE ////
ghost predicate clique(g: Graph, k: nat)
    requires valid_graph(g)
    requires k <= |g.V|
{
    exists cl: set<node> :: |cl| == k && is_clique(g, cl)
}

ghost predicate is_clique(g: Graph, cl: set<node>)
    requires valid_graph(g)
    requires |cl| <= |g.V|
{
    cl <= g.V &&
    forall u, v: node :: 
        u in cl && v in cl && well_ordered_pair(u, v) ==> (u, v) in g.E 
}

//// 3SAT ////

// Auxiliary function that calculates the absolute value of an integer.
function abs(i: int): int
{
    if i >= 0 then i
    else -i
}

// This predicate guarantees that a clause is nonempty and all its variables are in [1..V].
predicate valid_3clause(V: nat, cla: clause)
{
    |cla| == 3 && 
    forall n: nat ::
         n < |cla| ==> 1 <= abs(cla[n]) <= V && cla[n] != 0
}


// This predicate guarantees that all clauses in a CNF are valid.
// In addition, we assume that any CNF has at least one clause. 
predicate valid_formula(V: nat, f: Formula)
{    
    forall n: nat :: n < |f| ==> valid_3clause(V, f[n])
}

    
// An assignment "assig" is a sequence of boolean values where 
// forall i in [1..V], the value of variable i is assig[i]. 
predicate valid_assignment(V: nat, assig: seq<bool>)   
{
    |assig| == V+1
}

// This predicate guarantees that a literal in a clause makes the clause true.
predicate good_literal(V: nat, l: int, cla: clause, assig: seq<bool>)
    requires valid_3clause(V, cla)
    requires valid_assignment(V, assig)    
{
    l in cla && (assig[abs(l)] <==> l > 0)
}



// This predicate guarantees that an assignment is a model for a clause.
predicate model_clause(V: nat, cla: clause, assig: seq<bool>)
    requires valid_3clause(V, cla)
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


// This predicate guarantees that a CNF is satisfiable.
ghost predicate isSat(V:nat, f: Formula)
    requires valid_formula(V, f)
{
    exists assig: seq<bool>:: valid_assignment(V, assig) && model(V, f, assig) 
}


/***************
REDUCTION: 3SAT <=p CLIQUE
****************/

///// REDUCTION FUNCTION /////

ghost function formula_to_graph(V: nat, f: Formula): Graph
    requires valid_formula(V, f)
    ensures valid_graph(formula_to_graph(V, f))
    ensures |f| <= |formula_to_graph(V, f).V| <= 3*|f|
    ensures forall n: nat, l: int ::  
        n < |f| && l in f[n] <==> (n, l) in formula_to_graph(V, f).V      
    ensures forall u: node, v: node :: 
        (u, v) in formula_to_graph(V, f).E <==>
        (
            u in set_of_nodes(V, f) && 
            v in set_of_nodes(V, f) && 
            u.0 < v.0 && u.1 != -(v.1)
        )
    
{
    if |f| == 0 then G({}, {})
    else G(set_of_nodes(V, f), set_of_edges(V, f))
}

ghost function set_of_nodes(V: nat, f: Formula): set<node>
    requires valid_formula(V, f)
    ensures |f| <= |set_of_nodes(V, f)| <= 3*|f|
    ensures forall n: nat, l: int ::  
        n < |f| && l in f[n] <==> (n, l) in set_of_nodes(V, f)      
{
    if |f| == 0 then {}
    else set_of_nodes_level(V, f, 0)
}


ghost function set_of_nodes_level(V: nat, f: Formula, level: nat): set<node>
    requires valid_formula(V, f)
    requires 0 <= level < |f|
    decreases |f| - level
    ensures (|f|-level) <= |set_of_nodes_level(V, f, level)| <= 3*(|f|-level)
    ensures forall n: nat, l: int ::  
        (level <= n < |f| && l in f[n]) <==> (n, l) in set_of_nodes_level(V, f, level)
{
    var l1: set<node>:= 
        {(level, f[level][0]), (level, f[level][1]), (level, f[level][2])};
    if |f| == 1 || level == |f|-1 then l1
    else var s1: set<node>:=  set_of_nodes_level(V, f, level+1);
         l1 + s1
}

ghost function set_of_edges(V: nat, f: Formula): set<edge>
    requires valid_formula(V, f)
    ensures forall u: node, v: node :: 
        (u, v) in set_of_edges(V, f) <==>
        (
            u in set_of_nodes(V, f) && 
            v in set_of_nodes(V, f) && 
            u.0 < v.0 && u.1 != -(v.1)
        )    
{
    if |f| == 0 then {}
    else set_of_edges_level(V, f, 0)
}

ghost function set_of_edges_level(V: nat, f: Formula, level: nat): set<edge>
    requires valid_formula(V, f)
    requires 0 <= level < |f|
{
   if |f| == 1 || level == |f|-1 then {}
   else var nodes: set<node>:= set_of_nodes_level(V, f, level);
        var edges: set<edge>:= set u: node, v: node | 
            u in nodes && v in nodes && 
            u.0 < v.0 && u.1 != -(v.1) :: (u, v);
        edges
}  


///// REDUCTION CORRECTNESS /////


lemma reduction_Lemma(V: nat, f: Formula)
    requires valid_formula(V, f)
    ensures isSat(V, f) <==> clique(formula_to_graph(V, f), |f|) 
{    
    if isSat(V, f)
    {
        forward_Lemma(V, f);
    }
    if  clique(formula_to_graph(V, f), |f|) 
    {
        backward_Lemma(V, f);
    }
}

//Forward reduction: isSat(V, F) ==> clique(f(V, F))

lemma forward_Lemma(V: nat, f: Formula)
    requires valid_formula(V, f)
    requires isSat(V, f)
    ensures clique(formula_to_graph(V, f), |f|) 
{
    if |f| > 0
    {
        var g: Graph:= formula_to_graph(V, f);
        var assig: seq<bool>:| valid_assignment(V, assig) && model(V, f, assig);
        var cl: set<node> := good_literals(V, f, assig);
        assert |cl| == |f|;
        good_literals_level_Lemma(V, f, assig, |f|-1);
        good_literals_edges_Lemma(V, f, assig, |f|-1);
        assert forall u, v: node :: 
            u in cl && v in cl && u != v ==> (u, v) in g.E || (v, u) in g.E;
        assert clique(formula_to_graph(V, f), |f|) ;
    }
} 

//Backward reduction: clique(f(V, F)) ==> isSat(V, F)

lemma backward_Lemma(V: nat, f: Formula)
    requires valid_formula(V, f)
    requires clique(formula_to_graph(V, f), |f|)
    ensures  isSat(V, f)
{
    if |f| == 0
    {
        assert model(V, f, false_assig(V));
    }
    else
    {
        var g: Graph:= formula_to_graph(V, f);
        var cl: set<node> :| |cl| == |f| && is_clique(g, cl);
        var nassig: seq<bool>:= assignment_from_clique (V, f, cl);
        assert forall n: nat, l: int :: (n, l) in cl ==> good_literal(V, l, f[n], nassig);
        var sn: set<nat>:= set n | 0 <= n < |f| :: n;
        set_of_nodes_level_Lemma(V, f, 0);
        assert  levels_in_set(g.V) == sn;    
        set_of_nodes_level_cardinal_Lemma(V, f, 0);
        assert |levels_in_set(g.V)| == |f|;
        clique_cardinal_Lemma(V, f, cl);
        assert |levels_in_set(cl)| == |f|;
        set_Lemma(levels_in_set(cl), levels_in_set(g.V));
        assert levels_in_set(g.V) == levels_in_set(cl);
        assert  forall n: nat :: n in levels_in_set(cl) ==> 
        exists l: int :: l in f[n] && (n, l) in cl;
        assert model(V, f, nassig);
    }
} 



/// Auxiliar functions and lemmas to prove forward_Lemma

ghost function good_literals(V: nat, f: Formula, assig: seq<bool>): set<node>
    requires valid_formula(V, f)
    requires valid_assignment(V, assig)
    requires model(V, f, assig)
    decreases |f|
    ensures |good_literals(V, f, assig)| == |f|
{ 
     if |f| == 0 then {}
     else good_literals_level(V, f, assig, |f|-1) 
}

ghost function good_literals_level(V: nat, f: Formula, assig: seq<bool>, level: nat): set<node>
    requires 0 <= level < |f|
    requires valid_formula(V, f)
    requires valid_assignment(V, assig)
    requires model(V, f, assig)
    decreases level
    ensures var gl:= good_literals_level(V, f, assig, level);
        forall u: node :: u in gl ==> 0 <= u.0 <= level
    ensures |good_literals_level(V, f, assig, level)| == level+1
{ 
     var l: int :| l in f[level] && good_literal(V, l, f[level], assig);
     if (|f| == 1 || level == 0) then {(level, l)}
     else {(level, l)} + good_literals_level(V, f, assig, level-1)
}


lemma good_literals_level_Lemma(V: nat, f: Formula, assig: seq<bool>, level: nat) 
    requires 0 <= level < |f|
    requires valid_formula(V, f)
    requires valid_assignment(V, assig)
    requires model(V, f, assig)
    ensures var g: Graph:= formula_to_graph(V, f);
            var gl:= good_literals_level(V, f, assig, level);
            forall u: node :: 
                u in gl ==> good_literal(V, u.1, f[u.0], assig)
    ensures var gl:= good_literals_level(V, f, assig, level);
        forall u: node, v: node :: u in gl && v in gl && u != v ==> u.0 != v.0
{}


lemma good_literals_edges_Lemma(V: nat, f: Formula, assig: seq<bool>, level: nat)
    requires 0 <= level < |f|
    requires valid_formula(V, f)
    requires valid_assignment(V, assig)
    requires model(V, f, assig)
    ensures var g: Graph:= formula_to_graph(V, f);
            var gl:=  good_literals_level(V, f, assig, level);
            forall u, v: node :: u in gl && v in gl && u.0 < v.0 ==> (u, v) in g.E 
{
    if |f| > 0
    {
        good_literals_level_Lemma(V, f, assig, level);
        var g: Graph:= formula_to_graph(V, f);
        var gl:=  good_literals_level(V, f, assig, level);
        if exists u: node, v: node :: u in gl && v in gl && u.0 < v.0 && (u, v) !in g.E
        {
            var u: node, v: node :| u in gl && v in gl && u.0 < v.0 && (u, v) !in g.E;
            assert u.1 == -v.1;
            assert u == (u.0, -v.1); 
            assert v == (v.0, v.1);
            assert assig[abs(-v.1)] <==> -v.1 > 0;
            assert assig[abs(v.1)] <==> v.1 > 0;
            assert false;       
        }
    }
}  

/// Auxiliar function and lemmas to prove backward_Lemma

lemma set_Lemma<T>(c1: set<T>, c2: set<T>)
    requires c1 <= c2
    ensures |c1| <= |c2|
    ensures c1 <= c2 && |c1| == |c2| ==> c2 == c1
{
    if c1 != {}
    {
        var u:T :| u in c1;
        set_Lemma(c1-{u}, c2-{u});
    }
}

ghost function levels_in_set(s: set<node>): set<nat>
    ensures forall u: node :: u in s ==> u.0 in levels_in_set(s)
    ensures forall n: nat :: 
        n in levels_in_set(s) ==> exists l: int :: (n, l) in s
    ensures |levels_in_set(s)| <= |s|
    decreases |s| 
{
    if s == {} then {}
    else var u: node :| u in s;
         var su: set<node>:= set v: node | v in s && v.0 == u.0; 
        {u.0} + levels_in_set(s-su)
}


lemma levels_in_set_Lemma(s1: set<node>, s2: set<node>) 
    ensures levels_in_set(s1 + s2) == levels_in_set(s1) + levels_in_set(s2)
    ensures s1 <= s2 ==> levels_in_set(s1) <= levels_in_set(s2)
 {}
 

lemma set_of_nodes_level_Lemma(V: nat, f: Formula, level: nat)
    requires valid_formula(V, f)
    requires 0 <= level < |f|
    ensures forall n: nat ::
        n in levels_in_set(set_of_nodes_level(V, f, level)) <==> level <= n < |f| 
    decreases |f| - level  
{ 
    var l1: set<node>:= 
        {(level, f[level][0]), (level, f[level][1]), (level, f[level][2])};
    assert forall n: nat :: (n in levels_in_set(l1) <==> n == level); 
    if |f| != 1 && level != |f|-1
    {   
        var s1: set<node>:=  set_of_nodes_level(V, f, level+1);
        levels_in_set_Lemma(l1, s1);
        assert levels_in_set(l1 + s1) == levels_in_set(l1) + levels_in_set(s1);
    }
}


lemma set_of_nodes_level_cardinal_Lemma(V: nat, f: Formula, level: nat)
    requires valid_formula(V, f)
    requires 0 <= level < |f|
    ensures |levels_in_set(set_of_nodes_level(V, f, level))| == |f| - level
    decreases |f| - level  
{ 
    var l1: set<node>:= 
        {(level, f[level][0]), (level, f[level][1]), (level, f[level][2])};
    assert levels_in_set(l1) == {level}; 
    assert |levels_in_set(l1)| == 1;
    if |f| != 1 && level != |f|-1
    {
        var s1: set<node>:=  set_of_nodes_level(V, f, level+1);
        levels_in_set_Lemma(l1, s1);
        assert levels_in_set(set_of_nodes_level(V, f, level)) == 
            levels_in_set(l1) + levels_in_set(s1); 
    }
}


lemma clique_node_Lemma(u: node, V: nat, f: Formula, cl: set<node>)
    requires valid_formula(V, f)
    requires |cl| <= |formula_to_graph(V, f).V| 
    requires is_clique(formula_to_graph(V, f), cl)
    requires u in cl
    ensures forall v: node :: v in cl && u != v ==> u.0 != v.0
{
    if exists v: node :: v in cl && u != v && u.0 == v.0
    {
        var v: node :| v in cl && u != v && u.0 == v.0;
        assert (u, v) !in set_of_edges(V, f);
         assert (v, u) !in set_of_edges(V, f);
    }
}


lemma clique_cardinal_Lemma(V: nat, f: Formula, cl: set<node>)
    requires valid_formula(V, f)
    requires |cl| <= |formula_to_graph(V, f).V| 
    requires is_clique(formula_to_graph(V, f), cl)
    ensures |levels_in_set(cl)| == |cl|  
{
    if cl > {}
    {
        var u: node :| u in cl;
        assert {u.0} + levels_in_set(cl-{u}) == levels_in_set(cl);
        assert forall u: node :: u in cl ==> u.0 in levels_in_set(cl);
        clique_node_Lemma(u, V, f, cl);
        assert forall v: node :: v in cl && u != v ==> u.0 != v.0;
        assert |levels_in_set(cl-{u})| == |cl-{u}|;  
    }
}

ghost function false_assig(V: nat): seq<bool>
    ensures |false_assig(V)| == V+1
    ensures valid_assignment(V, false_assig(V))
{
    if V == 0 then [false]
    else [false] + false_assig(V-1)
}


ghost function assignment_from_clique(V: nat, f: Formula, cl: set<node>): seq<bool>
    requires valid_formula(V, f)
    requires valid_graph(formula_to_graph(V, f))
    requires |cl| <= |formula_to_graph(V, f).V|
    requires is_clique(formula_to_graph(V, f), cl)
    decreases |cl|
    ensures |assignment_from_clique(V, f, cl)| == V+1
    ensures valid_assignment(V, assignment_from_clique(V, f, cl))
    ensures var nassig: seq<bool>:= assignment_from_clique(V, f, cl);
            forall n: nat, l: int :: 
                (n, l) in cl ==> (nassig[abs(l)] <==> l > 0)
{
    var nodes: set<node>:= formula_to_graph(V, f).V;
    if |f| == 0 || cl == {} then false_assig(V)
    else var u: node :| u in cl;
        assert (u.0, u.1) in cl;
        var nassig: seq<bool>:= assignment_from_clique(V, f, cl-{u});
        assert  nassig ==  nassig[..abs(u.1)] + [nassig[abs(u.1)]] +  nassig[abs(u.1)+1..]; 
        if u.1 > 0 then nassig[..abs(u.1)] + [true] +  nassig[abs(u.1)+1..]
        else nassig[..abs(u.1)] + [false] +  nassig[abs(u.1)+1..]    
}

// 280 code lines
