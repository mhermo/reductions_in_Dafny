datatype Graph = G(V: set<nat>, E: set<(nat, nat)>)
// The nodes of the graph are natural numbers.

// This predicate guarantees that the edges are ordered pairs of nodes in V.
ghost predicate valid_graph(g: Graph)
{
    forall u: nat, v: nat :: (u, v) in g.E ==> u in g.V && v in g.V && u < v
}

// This predicate is the decision problem known as the Clique problem.
ghost predicate clique(g: Graph, k: nat)
    requires valid_graph(g)
    requires k <= |g.V|
{
    exists cl: set<nat> :: |cl| == k && cl <= g.V &&
        (forall u: nat, v: nat :: u in cl && v in cl && u < v ==> (u, v) in g.E)
}

// This predicate is the decision problem known as the Independent-Set problem.
ghost predicate indSet(g: Graph, k: nat)
    requires valid_graph(g)
    requires k <= |g.V|
{
    exists ins: set<nat> :: |ins| == k && ins <= g.V &&
        (forall u, v: nat :: u in ins && v in ins && u < v ==> (u, v) !in g.E)
}

/**
The reduction: Clique <=p Independent-Set
**/
// Reduction function

// This function calculates the complementary set of edges. 
// The cost is O(|g.V|^2).
function complement_edges(g: Graph): set<(nat, nat)>
    requires valid_graph(g)
{
   
    set u: nat, v:nat | u in g.V && v in g.V && u < v  && (u,v) !in g.E :: (u, v)    
} 

// The reduction function only transforms the initial graph G(V,E) into G(V,E')
// where E' is the complementary set of E. It has a quadratic cost.  
function complement_graph(g: Graph): Graph
    requires valid_graph(g)
    ensures valid_graph(complement_graph(g))
    ensures g.V == complement_graph(g).V
    ensures forall u: nat, v: nat :: u in g.V && v in g.V && u < v ==> 
        ((u, v) in g.E <==> (u, v) !in complement_graph(g).E)
{
    if |g.V| == 0 then g else G(g.V, complement_edges(g))
}

//Reduction correctness
lemma reduction_Lemma(g: Graph, k: nat)
    requires valid_graph(g)
    requires k <= |g.V|
    ensures clique(g, k) <==> indSet(complement_graph(g), k)
{}

// 27 code lines