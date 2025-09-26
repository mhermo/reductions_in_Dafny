module First {

/************************
INSTANCE TYPE DECLARATION
************************/

// In a graph G(V,E), V is a natural meaning that the set of nodes is {0, 1,...V-1} 
datatype Graph = G(V: nat, E: set<(nat, nat)>)
type UndirectedGraph = Graph
type DirectedGraph = Graph

ghost predicate valid_DirectedGraph(g: DirectedGraph)
{
    forall u: nat, v: nat :: (u, v) in g.E ==> u < g.V && v < g.V && u != v
}

ghost predicate valid_UndirectedGraph(ug: UndirectedGraph)
{
    forall u: nat, v: nat :: (u, v) in ug.E ==> u < ug.V && v < ug.V && u < v
}

/////// DIRECTED/UNDIRECTED HAMILTONIAN CIRCUIT ///////

//Definition predicates:

ghost predicate directed_ham(g: DirectedGraph)
    requires valid_DirectedGraph(g)
{
    exists hc:seq<nat> :: is_directed_ham(g, hc)
}

ghost predicate is_directed_ham(g: DirectedGraph, hc: seq<nat>)
    requires valid_DirectedGraph(g)
{
    (g.V == 0 && |hc| == 0) ||
    (
        (|hc| == g.V) && 
        (forall u: nat :: (u < g.V <==> u in hc)) && 
        (forall i: nat :: i < |hc|-1 ==> (hc[i], hc[i+1]) in g.E) &&
        (hc[|hc|-1], hc[0])in g.E
    )
}


ghost predicate undirected_ham(ug: UndirectedGraph)
    requires valid_UndirectedGraph(ug)
{
    exists uhc:seq<nat> :: is_undirected_ham(ug, uhc)
}

ghost predicate is_undirected_ham(ug: UndirectedGraph, uhc: seq<nat>)
    requires valid_UndirectedGraph(ug)
{
    (ug.V == 0 && |uhc| == 0) ||
    (
        (|uhc| == ug.V) && 
        (forall u: nat :: (u < ug.V <==> u in uhc)) && 
        (
            forall i: nat :: i < |uhc|-1 ==> 
              (((uhc[i], uhc[i+1]) in ug.E) || ((uhc[i+1], uhc[i]) in ug.E))
        ) &&
        (((uhc[|uhc|-1], uhc[0]) in ug.E) || ((uhc[0], uhc[|uhc|-1]) in ug.E))
    )
}


/////// AUXILIAR PREDICATES, LEMMAS AND FUNCTIONS //////

function In2Mid(n: nat): set<(nat, nat)>
{
	set u: nat | n <= u < 2*n :: (u-n, u)
}


function Mid2Out(n: nat): set<(nat, nat)>
    ensures forall u: nat, v: nat :: n <= u < 2*n && 2*n < v < 3*n ==>
        ((u,v) in Mid2Out(n) <==> v == u + n)
{
	set u: nat | 2*n <= u < 3*n :: (u-n, u)
}


function In2Out(g: DirectedGraph): set<(nat, nat)>
    requires valid_DirectedGraph(g)    
{
	set u: nat, v: nat | 
        u < g.V && v < g.V && (u, v) in g.E :: (v, u+2*g.V)
}

function new_edges(g: DirectedGraph): set<(nat, nat)>
    requires valid_DirectedGraph(g)
{
    In2Mid(g.V) + Mid2Out(g.V) + In2Out(g)
}


// Reduction function.
function DirectedGraph_to_UndirectedGraph(g: DirectedGraph): UndirectedGraph
    requires valid_DirectedGraph(g)
{
    G(3*g.V, new_edges(g))
} 


// Reduction correctness
/////////////////////////////////////////////////////

/*
lemma reduction_Lemma(g: DirectedGraph)
    requires valid_DirectedGraph(g)
    ensures var ug: UndirectedGraph :=  DirectedGraph_to_UndirectedGraph(g); 
        directed_ham(g) <==> undirected_ham(ug)
{
    var ug: UndirectedGraph :=  DirectedGraph_to_UndirectedGraph(g);     
    if directed_ham(g)
    {
        forward_Lemma(g, ug);
    }
    if undirected_ham(ug)
    {
        backward_Lemma(g, ug);
    }
}
*/


/// Construction of an undirected hamiltonian circuit from a directed one 
function new_circuit(n: nat, hc: seq<nat>): seq<nat>
    requires n >= |hc|
    ensures |new_circuit(n, hc)| == 3*|hc|
    decreases |hc|
{
    if |hc| == 0 then []
    else if |hc| == 1 then var u: nat := hc[0];
        [u, u+n, u+(2*n)] 
    else var u: nat:= hc[0];
        [u, u+n, u+(2*n)] + new_circuit(n, hc[1..])
}

function directed_ham_to_undirected_ham(g: DirectedGraph, hc: seq<nat>): seq<nat>
    requires valid_DirectedGraph(g)
    requires is_directed_ham(g, hc)
{
    new_circuit(g.V, hc)
}


//////Lemmas to prove the forward_Lemma//////////////

lemma nodes_circuit_Lemma(u: nat, n: nat, hc: seq<nat>)
    requires n >= |hc|
    ensures var uhc: seq<nat> := new_circuit(n, hc);
        u in uhc <==>  u in hc || u-n in hc || u-2*n in hc
{}


lemma undirected_nodes_circuit_Lemma(u: nat, g: DirectedGraph, hc: seq<nat>)
    requires valid_DirectedGraph(g)
    requires is_directed_ham(g, hc)
    ensures var uhc: seq<nat> := directed_ham_to_undirected_ham(g, hc);
        u in uhc  <==> u < 3*|hc|
{
    nodes_circuit_Lemma(u, |hc|, hc);
}
////////////////////////////////////////////////////////////////////////


/// Properties of nodes in new_circuit(n, hc)
lemma new_circuit_Lemma1(i: nat, n: nat, hc: seq<nat>)
    requires n >= |hc|
    requires i < |hc|
    ensures var uhc: seq<nat> := new_circuit(n, hc);
        hc[i] == uhc[3*i]
{
    if i > 0
    {  
        new_circuit_Lemma1(i-1, n, hc[1..]);
    }
}

lemma new_circuit_Lemma2(i: nat, n: nat, hc: seq<nat>)
    requires n >= |hc|
    requires i < |hc|
    ensures var uhc: seq<nat> := new_circuit(n, hc);
        hc[i]+n == uhc[(3*i)+1]
{
    if i > 0
    {  
        new_circuit_Lemma2(i-1, n, hc[1..]);
    }
}

lemma new_circuit_Lemma3(i: nat, n: nat, hc: seq<nat>)
    requires n >= |hc|
    requires i < |hc|
    ensures var uhc: seq<nat> := new_circuit(n, hc);
        hc[i]+2*n == uhc[(3*i)+2]
{
    if i > 0
    {  
        new_circuit_Lemma3(i-1, n, hc[1..]);
    }
}

/// Properties of new_edges(g) and properties of edges in new_circuit(n, g)

lemma new_edges_circuit_Lemma1(i: nat, g: DirectedGraph, hc: seq<nat>)
    requires valid_DirectedGraph(g)
    requires is_directed_ham(g, hc)
    requires i < |hc|
    ensures var uhc: seq<nat> := new_circuit(|hc|, hc);
        (uhc[3*i], uhc[3*i+1]) in new_edges(g)
{
    var uhc: seq<nat> := new_circuit(|hc|, hc);
    assert hc[i] in hc;
    new_circuit_Lemma1(i, g.V, hc);
    assert uhc[3*i] == hc[i];
    new_circuit_Lemma2(i, g.V, hc);
    assert uhc[(3*i)+1] == hc[i]+g.V;
    assert (hc[i], hc[i]+g.V) in In2Mid(g.V);
    assert (uhc[3*i], uhc[(3*i)+1]) in new_edges(g);
}


lemma new_edges_circuit_Lemma2(i: nat, g: DirectedGraph, hc: seq<nat>)
    requires valid_DirectedGraph(g)
    requires is_directed_ham(g, hc)
    requires i < |hc|-1
    ensures var uhc: seq<nat> := new_circuit(|hc|, hc);
        (uhc[3*(i+1)], uhc[3*i+2]) in new_edges(g)
{
    var uhc: seq<nat> := new_circuit(|hc|, hc);
    new_circuit_Lemma3(i, g.V, hc);
    assert uhc[3*i+2] == hc[i]+2*g.V;
    new_circuit_Lemma1(i+1, g.V, hc);
    assert uhc[3*(i+1)] == hc[i+1];
    assert (hc[i], hc[i+1]) in g.E;
    assert (hc[i+1], hc[i]+2*g.V) in In2Out(g);
    assert (uhc[3*(i+1)], uhc[3*i+2]) in new_edges(g);
}

lemma new_edges_circuit_Lemma3(i: nat, g: DirectedGraph, hc: seq<nat>)
    requires valid_DirectedGraph(g)
    requires is_directed_ham(g, hc)
    requires i < |hc|
    ensures var uhc: seq<nat> := new_circuit(|hc|, hc);
        (uhc[3*i+1], uhc[3*i+2]) in new_edges(g)
{
    
    var uhc: seq<nat> := new_circuit(|hc|, hc);
    assert hc[i] in hc;
    new_circuit_Lemma2(i, g.V, hc);
    assert uhc[3*i+1] == hc[i]+g.V;
    new_circuit_Lemma3(i, g.V, hc);
    assert uhc[3*i+2] == hc[i]+2*g.V;  
    assert(hc[i]+g.V, hc[i]+2*g.V) in Mid2Out(g.V);
    assert (uhc[3*i+1], uhc[3*i+2]) in new_edges(g);
}


lemma edge_new_circuit_Lemma(g: DirectedGraph, i: nat, hc: seq<nat>)
    requires valid_DirectedGraph(g)
    requires is_directed_ham(g, hc)
    requires var uhc: seq<nat> := new_circuit(|hc|, hc);
         i < |uhc|-1
    ensures var uhc: seq<nat> := new_circuit(|hc|, hc);
        (uhc[i], uhc[i+1]) in new_edges(g) ||  (uhc[i+1], uhc[i]) in new_edges(g)
{
    var uhc: seq<nat> := new_circuit(|hc|, hc);
    if |hc| > 0
    {
        var r: nat := i/3;
        if
        case i%3 == 0 =>
            assert i == 3*r;
            new_edges_circuit_Lemma1(r, g, hc);
        case i%3 == 1 =>
            assert i == 3*r+1;
            new_edges_circuit_Lemma3(r, g, hc);            
        case i%3 == 2 =>
            assert i == 3*r+2;
            new_edges_circuit_Lemma2(r, g, hc);
    }
}


lemma forward_Lemma(g: DirectedGraph, ug: UndirectedGraph)     
    requires valid_DirectedGraph(g)
    requires ug == DirectedGraph_to_UndirectedGraph(g)     
    requires directed_ham(g)
    ensures undirected_ham(ug)
{
    var hc: seq<nat> :| is_directed_ham(g, hc);
    var uhc: seq<nat> := directed_ham_to_undirected_ham(g, hc);
    if ug.V == 0
    {
        assert is_undirected_ham(ug, uhc);
    }
    else
    { 
        forall u: nat ensures u < ug.V <==> u in uhc
        {
            undirected_nodes_circuit_Lemma(u, g, hc);
        }
        
        forall i: nat | i < |uhc|-1 ensures  
               (((uhc[i], uhc[i+1]) in ug.E) || ((uhc[i+1], uhc[i]) in ug.E))
        {
            edge_new_circuit_Lemma(g, i, hc);
        }

        var i: nat:= |hc|-1;
        assert hc[i]+2*|hc| == uhc[3*i+2]
            by {new_circuit_Lemma3(i, |hc|, hc);}
        assert (uhc[0], uhc[|uhc|-1]) in ug.E;

        assert is_undirected_ham(ug, uhc);

    }
}

}

/// 172 code lines

