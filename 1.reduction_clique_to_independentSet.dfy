// Nodes in an undirected graph are natural numbers.
datatype Graph = G(V: set<nat>, E: set<(nat, nat)>)

// The undirected graph is valid
ghost predicate valid_graph(g: Graph)
{
    forall u: nat, v: nat :: (u, v) in g.E ==> u in g.V && v in g.V && u < v
}

// Clique decision problem.
predicate clique(g: Graph, k: nat)
    requires valid_graph(g) && k <= |g.V|
{
    exists cl: set<nat> :: |cl| == k && cl <= g.V && is_clique(g, cl)
}

predicate is_clique(g: Graph, cl: set<nat>)
    requires valid_graph(g)
    requires cl <= g.V
{
    forall u: nat, v:nat :: u in cl && v in cl && u < v ==> (u, v) in g.E 
}

// Independent-Set decision problem.
predicate indSet(g: Graph, k: nat)
    requires valid_graph(g) && k <= |g.V|
{
    exists ins: set<nat> :: |ins| == k && ins <= g.V &&
        is_indSet(g, ins)
}

predicate is_indSet(g: Graph, ins: set<nat>)
    requires valid_graph(g)
    requires ins <= g.V
{
    forall u: nat, v:nat :: u in ins && v in ins && u < v ==> (u, v) !in g.E 
}

/**
The reduction: Clique <=p Independent-Set
**/

// This function calculates the complement set of edges. 
function complement_edges(g: Graph): set<(nat, nat)>
    requires valid_graph(g)
{   
    set u: nat, v:nat | u in g.V && v in g.V && u < v  && (u,v) !in g.E :: (u, v)    
} 

// The reduction function only transforms the initial graph G(V,E) into G(V,E')
// where E' is the complement set of E.
function complement_graph(g: Graph): Graph
    requires valid_graph(g)
    ensures valid_graph(complement_graph(g))
    ensures g.V == complement_graph(g).V
    ensures forall u: nat, v: nat :: u in g.V && v in g.V && u < v ==> 
        ((u, v) in g.E <==> (u, v) !in complement_graph(g).E)
{
    G(g.V, complement_edges(g))
}

//Reduction correctness
lemma reduction_Lemma(g: Graph, k: nat)
    requires valid_graph(g) && k <= |g.V|
    ensures clique(g, k) <==> indSet(complement_graph(g), k)
{}

// 32 code lines
