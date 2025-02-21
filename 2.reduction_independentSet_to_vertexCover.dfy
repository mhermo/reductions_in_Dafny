
datatype Graph = G(V: set<nat>, E: set<(nat, nat)>)
// The nodes of the graph are natural numbers.

// This predicate guarantees that the edges are ordered pairs of nodes in V.
ghost predicate valid_graph(g: Graph)
{
    forall u: nat, v: nat :: (u, v) in g.E ==> u in g.V && v in g.V && u < v
}

// This predicate is the decision problem known as the Independent-Set problem.
ghost predicate indSet(g: Graph, k: nat)
    requires valid_graph(g)
    requires k <= |g.V|
{
    exists ins: set<nat> :: |ins| == k && is_indSet(g, ins)
}

ghost predicate is_indSet(g: Graph, ins: set<nat>)
    requires valid_graph(g)
    requires |ins| <= |g.V|
{
    ins <= g.V &&
    forall u: nat, v:nat :: u in ins && v in ins && u < v ==> (u, v) !in g.E 
}


// This predicate is the decision problem known as the Vertex-Cover problem.
ghost predicate vertexCover(g: Graph, k: nat)
    requires valid_graph(g)
    requires k <= |g.V|
{
    exists vc: set<nat> :: |vc| == k && is_vertexCover(g, vc)
}

ghost predicate is_vertexCover(g: Graph, vc: set<nat>)
    requires valid_graph(g)
    requires |vc| <= |g.V|
{
    vc <= g.V &&
    forall u: nat, v: nat :: (u, v) in g.E ==> (u in vc || v in vc) 
}

/**
The reduction: independentSet <=p vertexCover
**/

// Reduction function. This reduction is trivial.
function indSet_to_vertexCover(g: Graph, k: nat): nat
    requires valid_graph(g)
    requires k <= |g.V|
{
    |g.V|-k
} 

// Reduction correctness
lemma reduction_Lemma(g: Graph, k: nat)
    requires valid_graph(g)
    requires k <= |g.V|
    ensures indSet(g, k) <==> vertexCover(g, |g.V|-k)
{
    if indSet(g, k)
    {     
        var ins: set<nat> :| |ins| == k && is_indSet(g, ins);
        var vc:= set u | u in g.V && u !in ins;
        assert vc == g.V - ins;
        assert is_vertexCover(g, vc);
    }
    if vertexCover(g, |g.V|-k)
    {
        var vc: set<nat> :| |vc| == |g.V|-k &&  is_vertexCover(g, vc);
        var ins:=  set u | u in g.V && u !in vc;
        assert ins == g.V - vc;
        assert is_indSet(g, ins);
       
    }
}

// 40 code lines
