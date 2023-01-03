import networkx as nx
import itertools
import matplotlib.pyplot as plt
from matplotlib.colors import Colormap
import copy
import netgraph


""" 
import pickle
with open('mincfs_graphs_up_to_10.pkl','rb') as mmyfile:
    mincfs=pickle.load(myfile)
# mincfs is a dict of dicts whose keys are representatives of each isomorphism type of minCFS graph with up to 10 vertices, and whose values are dicts of properties of the corresponding RACG.
"""


def draw(G,H=None,K=None,**kwargs):
    """
    Draw the graph G as an editable graph.
    By default edges of G are black.
    If a subgraph H is given then its edges are red.
    If a subgraph K is given its edges are blue.
    If both H and K are given then their common edges are purple.  
    Other kwargs passed to netgraph.
    """
    edge_color=dict()
    if H is None and K is None:
        for e in G.edges():
            edge_color[e]='black'
    elif K is None:
        for e in G.edges():
            if e in H.edges():
                edge_color[e]='red'
            else:
                edge_color[e]='black'
    elif H is None:
        for e in G.edges():
            if e in K.edges():
                edge_color[e]='blue'
            else:
                edge_color[e]='black'
    else:
        for e in G.edges():
            if e in K.edges() and e in H.edges():
                edge_color[e]='purple'
            elif e in H.edges():
                edge_color[e]='red'
            elif e in K.edges():
                edge_color[e]='blue'
            else:
                edge_color[e]='black'
    plot_instance = netgraph.EditableGraph(G,node_labels=True,node_label_fontdict=dict(size=11),edge_color=edge_color,**kwargs)
    plt.show(block=False)
    return plot_instance




def find_good_cycle_in_iterated_double(G,maxdoublingdepth,verbose=False):
    """
    Recursive bredth first search for good cycles in iterated doubles of G over vertices.
    """
    for doublingdepth in range(1+maxdoublingdepth):
        result= find_good_cycle_at_depth(G,doublingdepth,verbose=verbose)
        if result is not None:
            return result
    return None

def find_good_cycle_at_depth(G,doublingdepth,doublingsequence=[],verbose=False):
    if doublingdepth==0:
        if verbose:
            print("Searching for a good cycle in iterated double with doubling sequence: "+str(doublingsequence))
        c=get_good_cycle(G)
        if c is not None:
            return c,doublingsequence
        return None
    else:
        if doublingsequence:
            next_to_try=[v for v in G if v[-1]!=2] # we already did some doubling and some vertices have a symmetric partner
        else:
            next_to_try=[v for v in G]
        for v in next_to_try:
            newdoublingsequence=doublingsequence+[v,]
            result= find_good_cycle_at_depth(double_over_vertex(G,v),doublingdepth=doublingdepth-1,doublingsequence=newdoublingsequence,verbose=verbose)
            if result is not None:
                return result
    return None

    
def double_over_vertex(G,v):
    """
    Return the graph obtained from G by doubling over vertex v: contains two copies of G, identified on the link of v, with v deleted. 
    Vertices of the new graph are of the form (w,1) and (w,2) for vertices w of G that get doubled, and (w,0) for vertices in the link of v that are not doubled. 
    """
    def addon(x,y):
        if type(x) is tuple:
            return (*x,y)
        else:
            return (x,y)
    D=nx.Graph()
    for w,attributes in G.nodes(data=True):
        D.add_node(addon(w,1),**attributes)
        D.add_node(addon(w,2),**attributes)
    for (u,w) in G.edges():
        D.add_edge(addon(u,1),addon(w,1))
        D.add_edge(addon(u,2),addon(w,2))
    D.remove_node(addon(v,1))
    D.remove_node(addon(v,2))
    for w in link(G,v):
        D.add_node(addon(w,0),**G.nodes[w])
    for w in link(G,v):
        for u in set(G[v])&set(G[w]):
            D.add_edge(addon(u,0),addon(w,0))
        for u in set(G[w])&distance_two(G,v):
            D.add_edge(addon(u,1),addon(w,0))
            D.add_edge(addon(u,2),addon(w,0))
        D.remove_node(addon(w,1))
        D.remove_node(addon(w,2))
    return D






def is_induced_cycle(G,S):
    induced_subgraph=G.subgraph(S)
    return all(len(induced_subgraph[v])==2 for v in induced_subgraph) and nx.is_connected(induced_subgraph)
    
def is_good_cycle(G,S):
    return len(S)>4 and is_induced_cycle(G,S) and  is_square_complete(G,S)



def get_good_cycle(G,legalturns=None,precomputeddiagonals=None,forbidden=set()):
    """
    Returns a tuple of vertices representing an induced, square complete cycle in G of length at least 5. 
    Returns None if no such cycle exists. 
    """
    if legalturns is None:
        legalturns=get_legal_turns(G)
    if precomputeddiagonals is None:
        precomputeddiagonals=diagonals(G)
    newforbidden=forbidden | (set(G)-set(legalturns))
    refined=copy.copy(newforbidden)
    firsttime=True
    while firsttime or refined!=newforbidden:
        firsttime=False
        newforbidden=refined
        for v in set(G)-newforbidden:
            if all(v not in legalturns[w] for w in set(legalturns)-newforbidden):
                refined.add(v)
    for v in list(set(G)-newforbidden):
        c=get_good_cycle_at_vert(G,v,legalturns,prefix=tuple([]),precomputeddiagonals=precomputeddiagonals,forbidden=newforbidden)
        if c is not None:
            return c
        newforbidden.add(v) # no good cycles at v, so in continuing search do not consider paths through v.
    return None

def get_good_cycle_at_vert(G,v,legalturns,prefix=tuple([]),precomputeddiagonals=None,forbidden=set([])):
    if v in forbidden:
        assert(False)
    if precomputeddiagonals is None:
        precomputeddiagonals=diagonals(G)
    current=v
    newforbidden=forbidden | {(set(T)-set([current,])).pop() for T in (T for T in precomputeddiagonals if current in T)}
    if not prefix: # we are starting a good cycle at v, not continuing one already started
        if current not in legalturns:
            return None
        for nextvert in set(legalturns[current])-newforbidden:
            c=get_good_cycle_at_vert(G,nextvert,legalturns,prefix=(current,),precomputeddiagonals=precomputeddiagonals,forbidden=newforbidden)
            if c is not None:
                return c
        return None
    else: # prefix contains a prefix of a good cycle ending at v. Try to continue it. 
        previousvert=prefix[-1]
        if current not in legalturns[previousvert]:
            return None
        for nextvert in legalturns[previousvert][current]-newforbidden:
            if nextvert in prefix: # this would make a closed loop. Is it good?
                i=prefix.index(nextvert)
                if current in legalturns and nextvert in legalturns[current] and prefix[i+1] in legalturns[current][nextvert] and len(prefix)-i>3:
                    return prefix[i:]+(current,)
            else: # increment prefix with nextvert and try to continue from nextvert
                c=get_good_cycle_at_vert(G,nextvert,legalturns,prefix=prefix+(current,),precomputeddiagonals=precomputeddiagonals,forbidden=newforbidden)
                if c is not None:
                    return c
        return None
        
            
            
        
def get_legal_turns(G):
    legal=dict()
    for v in G:
        for w in G[v]:
            possible_next=distance_two(G,v) & set(G[w])
            for u in possible_next:
                if all(not is_a_square(G,{u,v,w,x}) for x in set(G[u])&set(G[v])):
                    if v not in legal:
                        legal[v]=dict()
                    legal[v].setdefault(w,set()).add(u)
    refined=copy.deepcopy(legal)
    firsttime=True
    while firsttime or refined!=legal:
        if not firsttime:
            legal=refined
            refined=copy.deepcopy(legal)
        else:
            firsttime=False
        for v in legal:
            for y in legal[v]:
                if y not in legal:
                    del refined[v][y]
                    if not refined[v]:
                        del refined[v]
                else:
                    for z in legal[v][y]:
                        if z not in legal[y]:
                            refined[v][y].remove(z)
                    if not refined[v][y]:
                        del refined[v][y]
                        if not refined[v]:
                            del refined[v]
    return refined
     

def is_square_complete(G,S):
    """
    G is nx.Graph, S is a collection of vertices, a collection of edges, or an nx.Subgraph of G. 
    Decide if the induced subgraph of G defined by S is square complete.
    """
    if len(S)<2:
        return True
    induced_subgraph=G.subgraph(S)
    vertlist=[x for x in inducedsubgraph]
    for i in range(len(vertlist)-1):
        for j in (j for j in range(i+1,len(vertlist)) if vertlist[j] in distance_two(G,vertlist[i])):
            v=vertlist[i]
            w=vertlist[j]
            common_neighbors=set(G[v]) & set(G[w])
            for u in common_neighbors-set(S):
                if any(x not in G[u] for x in (y for y in common_neighbors if y!=u)):
                    return False # x,v,u,w is an induced square of G with diagonal in S
    return True

def get_square_completion(G,S):
    """
    Given an nx.Graph G and S defining a subgraph return the smallest square complete subgraph of G containing S.
    """
    induced_graph=G.subgraph(S)
    if len(induced_graph)<2:
        return induced_graph
    SQ={sq for sq in induced_squares(G)}
    the_verts=set(induced_graph)
    changed=True
    while changed:
        for sq in SQ:
            verts_in=set(sq) & the_verts
            if len(verts_in)==3:
                the_verts|=set(sq)
                changed=True
                break
            elif len(verts_in)==2:
                a,b=verts_in
                if b not in G[a]:
                    the_verts|=set(sq)
                    changed=True
                    break
        else:
            changed=False
    return G.subgraph(the_verts)
            
            
        

def minsquare_subgraphs(G):
    """
    Generate the minsquare subgraphs of an nx.Graph G.
     minsquare = square complete, contains a square, and is minimal with respect to inclusion among such subgraphs. 
    """
    SQ=square_graph(G)
    for C in nx.connected_components(SQ):
        yield G.subgraph(support(C))

def is_minsquare(G,V=None):
    """
    Determine if induced subgraph H of G spanned by V is a minsquare subgraph of G; that is, H is square-complete, contains a square, and is minimal among subgraphs of G with these properties.
    If no H is given determine if G itself is minsquare.
    """
    if V is None:
        verts=set(G)
    else:
        verts=V
    return any(verts==set(H) for H in minsquare_subgraphs(G))

    
def is_CFS(G,precomputed_diagonal_graph=None):
    """
    True if G is a CFS graph, which means that, modulo deleting a join, the square graph of G contains a component with full support.
    """
    Gprime=G.subgraph([v for v in G if G.degree[v]<len(G)])
    if precomputed_diagonal_graph is None:
        dg=diagonal_graph(Gprime)
    else:
        dg=precomputed_diagonal_graph
    if not dg:
        return not bool(Gprime)
    theverts=set(Gprime)
    for C in nx.connected_components(dg):
        if support(C)==theverts:
            return True
    return False
        
                    
def is_minimal_CFS(G,max_edges_to_remove=1):
    """
    Default only checks that no spanning subgraph with one fewer edge is CFS. A priori it might be necesasry to remove several edges to verify nonminimality. Use max_edges_to_remove=float('inf') to check all possible subgraphs, but this can take a long time.
    """
    if not is_CFS(G):
        return False
    for E in range(max(len(G)--1,len(G.edges())-max_edges_to_remove),len(G.edges())):
        for edges in itertools.combinations(G.edges(),E):
            H=G.edge_subgraph(edges)
            if len(H)<len(G):
                continue
            if is_CFS(H):
                return False
    return True

def is_strongly_CFS(G):
    """
    Decide if the square graph of G is connected and has full support.
    """
    Gprime=G.subgraph([v for v in G if G.degree[v]<len(G)])
    sg=square_graph(Gprime)
    if not sg:
        return not bool(Gprime)
    if not nx.is_connected(sg):
        return False
    return support(sg)==set(Gprime)

def distillations(G,only_minCFS=False,non_cone=False):
    """
    Yield subgraphs A and B of G so that G splits as an amalgam A*_C B whose factors are CFS, such that C=A&B is not a clique.
    """
    for A in itertools.chain.from_iterable(itertools.combinations(G,n) for n in range(3,len(G))):
        if not is_CFS(G.subgraph(A)) or (only_minCFS and not is_minimal_CFS(G)):
            continue
        for C in itertools.chain.from_iterable(itertools.combinations(A,n) for n in range(2,len(A))):
            if is_clique(G,C):
                continue
            if non_cone and len(A)-len(C)==1:
                v=next(iter(set(A)-set(C)))
                if len(G.subgraph(A)[v])==len(C):
                    continue
            B=set(C)|(set(G)-set(A))
            if (not only_minCFS and is_CFS(G.subgraph(B))) or is_minimal_CFS(G.subgraph(B)):
                if non_cone and len(B)-len(C)==1:
                    v=next(iter(set(B)-set(C)))
                    if len(G.subgraph(B)[v])==len(C):
                        continue
                yield G.subgraph(A),G.subgraph(B)

def reductions(G):
    """
    Yield subgraphs of G with one vertex removed that are still CFS.
    """
    for v in G:
        H=G.subgraph(set(G)-set([v,]))
        if is_CFS(H):
            yield H
                                           

#------------- Dani Levcovitz conditions

def Dani_Levcovitz(Gamma,Lambda,verbose=False):
    """
    Given a triangle-free CFS graph Gamma and a subgraph Lambda of the complementary graph, check if Lambda defines a finite index RAAG system according to Dani-Levcovitz Theorem 4.8.
    """
    Gammaprime=Gamma.subgraph([v for v in Gamma if Gamma.degree[v]<len(Gamma)])
    if not set(Lambda)==set(Gammaprime):
        if verbose:
            print("Lambda does not have full support.")
        return False
    if not Dani_Levcovitz_RAAG_system(Gamma,Lambda,verbose):
        return False
    return  True 

def draw_Dani_Levcovitz_pair(Gamma,Lambda,**kwargs):
    Theta= Dani_Levcovitz_Theta_graph(Gamma,Lambda)
    edge_color=dict()
    cc=nx.connected_components(Lambda)
    comp1nodes=next(cc)
    for e in Theta.edges():
        if e in Gamma.edges():
            edge_color[e]='black'
        elif e[0] in comp1nodes and e[1] in comp1nodes:
            edge_color[e]='red'
        else: # Lambda has at most 2 connected components
            edge_color[e]='blue'
    plot_instance = netgraph.EditableGraph(Theta,node_labels=True,node_label_fontdict=dict(size=11),edge_color=edge_color,**kwargs)
    plt.show(block=False)
    return plot_instance


def find_Dani_Levcovitz_subgraph(Gamma,verbose=False,assume_triangle_free=False,assume_CFS=False):
    """
    Given a triangle-free CFS graph Gamma, find a subgraph Lambda of the complementary graph satisfying Dani-Levcovitz conditions. 
    Return None if no such graph exists.
    """
    # Lambda must have exactly 2 components. Dan-Levcovitz, Fig 3.10, show that more than 2 components implies Gamma contains a triangle. But Lambda can't contain only one component if it is induced and has full support unless Gamma is discrete, which it is not, since it is assumed to be CFS.
    # Lambda must be contained in the subgraph of the complement of G consisting of edges that are diagonals of induced squares, since any other edge would give an isolated vertex in the defining graph of the RAAG, but our W_Gamma is 1-ended, so the RAAG should not have isolated vertices.
    # enumerate non-spanning subtrees Lambda1 of the commuting complementary graph. This will be one component of prospective Lambda. Then enumerate spanning subtrees Lambda2 of commutingGcomp - Lambda1. Lambda2 must be spanning so that Lambda=Lambda1 U Lambda2 has full support.
    if not assume_triangle_free:
        if not is_triangle_free(Gamma):
            NotImplemented
    diagG=diagonal_graph(Gamma)
    if not is_CFS(Gamma,precomputed_diagonal_graph=diagG):
        raise ValueError("Gamma is not a CFS graph.")
    commutingGcomp=nx.Graph()
    commutingGcomp.add_edges_from(v for v in diagG) # We do not need the entire complement graph of Gamma. Only edges that are the diagonal of an induced square have a chance to commute with another edge. Allowing other edges would just give isolated vertices of Delta.
    try:
        A,B=bipartition(Gamma)
    except ValueError: # commutingGcomp is not bipartite
        return None
    Apart=commutingGcomp.subgraph(A)
    Bpart=commutingGcomp.subgraph(B)
    if not Apart.edges() or not Bpart.edges():
        return None
    for Lambda1 in nx.algorithms.tree.mst.SpanningTreeIterator(Apart):
        for Lambda2 in nx.algorithms.tree.mst.SpanningTreeIterator(Bpart):
            Lambda=nx.Graph()
            Lambda.add_edges_from(Lambda1.edges())
            Lambda.add_edges_from(Lambda2.edges())
            if Dani_Levcovitz(Gamma,Lambda): # check if Dani-Levcovitz conditions hold. 
                return Lambda
    return None

def old_find_Dani_Levcovitz_subgraph(Gamma,verbose=False):
    """
    Given a triangle-free CFS graph Gamma, find a subgraph Lambda of the complementary graph satisfying Dani-Levcovitz conditions. 
    Return None if no such graph exists.
    """
    diagG=diagonal_graph(Gamma)
    commutingGcomp=nx.Graph()
    commutingGcomp.add_edges_from(v for v in diagG) # We do not need the entire complement graph of Gamma. Only edges that are the diagonal of an induced square have a chance to commute with another edge. Allowing other edges would just give isolated vertices of Delta.

    # look at subgraphs of commutingGcomp with at most 2 components
    for E in range(len(commutingGcomp.edges()),len(Gamma)//2-1,-1):
        for edgeset in itertools.combinations(commutingGcomp.edges(),E):
            Lambda=commutingGcomp.edge_subgraph(edgeset)
            if Dani_Levcovitz(Gamma,Lambda): # check if Dani-Levcovitz conditions hold
                return Lambda
    return None


def Theta_induced_rooted_complementary_subtrees(Gamma, commutingGcomp, current_tree, current_buds):
    """
    Generate subtrees of commutingGcomp containing current_tree such that no two vertices are connected by an edge of Gamma.
    """
    if not current_buds:
       yield current_tree
    else:
        current_bud=min(current_buds)
        if len(current_tree)==1:
            outgoing_neighbors=set(commutingGcomp[current_bud])
        else:
            stem=next(iter(current_tree[current_bud]))
            outgoing_neighbors=set(commutingGcomp[current_bud])-set([stem,])
        for new_growth in itertools.chain.from_iterable(itertools.combinations(outgoing_neighbors,n) for n in range(len(outgoing_neighbors)+1)):
            Theta=Dani_Levcovitz_Theta_graph(Gamma,current_tree)
            if any(set(Theta[v]) & (set(new_growth) | set(current_tree)) for v in new_growth): #if  current_tree U newgrowth not Theta-induced
                continue
            new_tree=current_tree.copy()
            for v in new_growth:
                new_tree.add_edge(current_bud,v)
            next_buds=(set(new_growth) | current_buds)-set([current_bud,])
            for T in Theta_induced_rooted_complementary_subtrees(Gamma, commutingGcomp, new_tree, next_buds):
                yield T
        

        
        



def Dani_Levcovitz_Theta_graph(Gamma,Lambda):
    Theta=nx.Graph()
    for e in Gamma.edges():
        Theta.add_edge(*e)
    for e in Lambda.edges():
        Theta.add_edge(*e)
    return Theta

def Dani_Levcovitz_RAAG_system(Gamma,Lambda, verbose=False): 
    """
    Given a triangle free CFS graph Gamma and a subgraph Lambda of the complementary graph, check if Lambda defines a RAAG system of W_\Gamma, according to Dani-Levcovitz Theorem 3.18.
    """
    if len([x for x in nx.connected_components(Lambda)])>2:
        if verbose:
            print("Lambda has more than two components.")
        return False
    if not Dani_Levcovitz_R1(Gamma,Lambda,verbose):
        return False
    if not Dani_Levcovitz_R2(Gamma,Lambda,verbose):
        return False
    if not Dani_Levcovitz_R3(Gamma,Lambda,verbose):
        return False
    if not Dani_Levcovitz_R4(Gamma,Lambda,verbose):
        return False
    return True

def Dani_Levcovitz_R1(Gamma,Lambda,verbose=False):
    # R1: Lambda is a forest
    for C in nx.connected_components(Lambda):
        if not nx.is_tree(Lambda.subgraph(C)):
            if verbose:
                print("Condition R1 fails. Lambda component "+str(C)+" is not a tree.")
            return False
    return True

def Dani_Levcovitz_R2(Gamma,Lambda,verbose=False):
    # R2: Each component of Lambda is an induced subgraph of Theta
    Theta= Dani_Levcovitz_Theta_graph(Gamma,Lambda)
    for C in nx.connected_components(Lambda):
        if len(Theta.subgraph(C).edges())!=len(Lambda.subgraph(C).edges()):
            if verbose:
                print("Condition R2 fails. Lambda component "+str(C)+" is not induced.")
            return False
    return True
    
def Dani_Levcovitz_R3(Gamma,Lambda,verbose=False):
    # R3: Gamma contains the join of the Lambda-convex hulls of 2 component squares
    for S in two_component_cycles(Gamma,Lambda,4):
        Tc=convex_hull(Lambda,{S[0],S[2]})
        Td=convex_hull(Lambda,{S[1],S[3]})
        for x,y in itertools.product(Tc,Td):
            if (x,y) not in Gamma.edges():
                if verbose:
                    print("Condition R3 fails. For 2 component cycle "+str(S)+", edge "+str((x,y))+" of join of Lambda hulls is not in Gamma.")
                return False
    return True

def Dani_Levcovitz_R4(Gamma,Lambda,verbose=False):
    # R4: Every edge of a 2 component cycle is contained in a 2 component square of Theta with its vertices in the Lamdba-hulls of of the vertices of the original cycle
    C=[g for g in nx.connected_components(Lambda)]
    for i,j in itertools.combinations(range(len(C)),2):
        for cycle in bicycles(Gamma,C[i],C[j]): 
            cs={cycle[2*i] for i in range(len(cycle)//2)}
            ds={cycle[2*i+1] for i in range(len(cycle)//2)}
            Tc=convex_hull(Lambda,cs)
            Td=convex_hull(Lambda,ds)
            allowed_edges=set()
            for square in bicycles(Gamma,Tc,Td,4): # enumerate the 2 component squares with vertices in Tc and Td and take the collection of all their edges. These are the allowed edges. 
                for k in range(4):
                    allowed_edges.add((square[k],square[(k+1)%4]))
                    allowed_edges.add((square[(k+1)%4],square[k]))
            for k in range(len(cycle)): # check if all the edges of the cycle are in the set of allowed edges
                if (cycle[k],cycle[(k+1)%len(cycle)]) not in allowed_edges:
                    if verbose:
                        print("Condition R4 fails. For 2 component cycle "+str(cycle)+",  edge"+str((cycle[k],cycle[(k+1)%len(cycle)]))+" is not contained in 2 component square.")
                    return False
    return True
            
def two_component_cycles(Gamma,Lambda,n=None):
    """
    Generator of 2-component cycles. 
    """
    C=[c for c in nx.connected_components(Lambda)]
    for cycle in itertools.chain.from_iterable(bicycles(Gamma,C[i],C[j],n) for i,j in itertools.combinations(range(len(C)),2)):
        yield cycle

def bicycles(G,A,B,n=None):
    """
    Given a graph G and disjoint sets of vertices A and B and an even number n, inductively generate cycles of length n in G whose vertices alternate between A and B.
    If no n is given then generate cycles of all possible lengths. 
    We assume that vertices of G are comparable so that we can restrict to cycles that are lexicographically minimal among permutations by change of starting vertex and direction, subject to starting in set A. 
    """
    if n is None:
        for cycle in itertools.chain.from_iterable(bicycles(G,A,B,2*m) for m in range(2,1+min(len(A),len(B)))):
            yield cycle
    else:
        assert(n%2==0 and n>=4)
        for firstA in A:
            for firstB in set(B)&set(G[firstA]):
                for lastB in {b for b in B if b>firstB}&set(G[firstA]): # ensure that lastB is greater than the firstB so that resulting cycle is lex minimal up to reversal
                    remainingA={x for x in A if x>firstA} # ensure that all other A vertices are greater than firstA so that resulting cycle is lex minimal up to change of starting vertex in A.
                    remainingB={x for x in B if x not in {firstB,lastB}}
                    for cycle in extendbicycle(G,remainingB,remainingA,[lastB,firstA,firstB],n):
                        yield cycle[1:]+cycle[0:1] # cycle that we actually yield is of form [firstA,firstB,....,lastB]
                        
def extendbicycle(G, remaining_even_index_vertices, remaining_oddindex_vertices, currentcycle, n):
    if len(currentcycle)==n-1: #only need one more vertex to complete the cycle
        for final_vertex in remaining_oddindex_vertices & set(G[currentcycle[-1]]) & set(G[currentcycle[0]]): # a vertex that is in remaining_odd_index_vertices and is adjacent to previous vertex and to initial vertex so that we make a closed cycle
             yield currentcycle+[final_vertex,]
    elif len(currentcycle)%2: # current length is odd, so last index is even, so next index is odd 
        for b in remaining_oddindex_vertices & set(G[currentcycle[-1]]):
            for thecycle in extendbicycle(G,remaining_even_index_vertices,remaining_oddindex_vertices-set([b]),currentcycle+[b,],n):
                yield thecycle
    else: # next index is even
        for a in remaining_even_index_vertices & set(G[currentcycle[-1]]):
            for thecycle in extendbicycle(G,remaining_even_index_vertices-set([a]),remaining_oddindex_vertices,currentcycle+[a,],n):
                yield thecycle



#--------- Nguyen-Tran 

def maximal_suspension_subgraphs(G):
    """
    Generator that yields maximal suspension subsets of a graph G.
    """
    ordered_nodes=[v for v in G]
    for i in range(len(ordered_nodes)-1):
        for j in (j for j in range(i+1,len(ordered_nodes)) if ordered_nodes[j] not in G[ordered_nodes[i]]):
            a=ordered_nodes[i]
            b=ordered_nodes[j]
            common_neighbors=set(G[a])&set(G[b])
            if len(common_neighbors)<2:
                pass # a and b are not suspension points of a subgraph
            elif len(common_neighbors)>2:
                yield ((a,b),tuple(common_neighbors))
            else:
                c,d=common_neighbors
                assert(c not in G[d]) # G is triangle-free
                k=ordered_nodes.index(c)
                ell=ordered_nodes.index(d)
                if k>ell:
                    k,ell=ell,k
                    c,d=d,c
                if len(set(G[c])&set(G[d]))==2:
                    if i<k:
                        yield ((a,b),(c,d))
                    else:
                        pass # The square a,c,b,d is a max suspension subgraph, but we already yielded it because c comes before a in the ordered_nodes list. 
                else:
                    pass # The maximal suspension subgraph for which a,b are suspension points is contained in a larger suspension subgraph for which c,d are the suspension points. 
            

def Nguyen_Tran_tree(G):
    T=nx.Graph()
    for ms in maximal_suspension_subgraphs(G):
        T.add_node(ms)
    for v,w in itertools.combinations(T,2):
        if is_induced_square(G,{v[0][0],w[0][0],v[0][1],w[0][1]}):
            T.add_edge(v,w)
    return T

def Nguyen_Tran_condition(G):
    """
    If G is a triangle-free planar graph, decides whether or not W_G is quasiisometric to a RAAG.
    """
    Gprime=G.subgraph([v for v in G if G.degree[v]<len(G)])
    if is_join(Gprime):
        return True
    T=Nguyen_Tran_tree(Gprime)
    return all(len(T[v])<len(v[1]) for v in T)




# -------- Edletzberger
def is_cut_set(G,S):
    H=G.copy()
    for v in S:
        H.remove_node(v)
    return not nx.is_connected(H)

def cut_cliques(G):
    for C in nx.find_cliques(G):
        if is_cut_set(G,C):
            yield set(C)

def is_one_ended(G):
    if not nx.is_connected(G):
        return False
    if is_clique(G,G):
        return False
    CC=cut_cliques(G)
    try:
        next(CC)
    except StopIteration:
        return True
    return False

    
def cut_pairs(G):
    """
    Generates cut pairs of vertices in G.
    """
    for a,b in itertools.combinations(G,2):
        if is_cut_set(G,{a,b}):
            yield (a,b)

def cut_triples(G):
    """
    Assuming G is triangle free and one-ended, generates cut sets that are segments of length 2 whose endpoints are not a cut pair. 
    """
    for a,b in itertools.combinations(G,2):
        if is_cut_set(G,{a,b}):
            continue
        common_neighbors=set(G[a])&set(G[b])
        for c in common_neighbors:
            if is_cut_set(G,{a,b,c}):
                yield (a,b,c)
                
def is_separated_by(G,A,C):
    """
    Return True if some pair of points of A-C is in different components of G-C
    """
    H=G.copy()
    for v in C:
        H.remove_node(v)
    return any(not nx.has_path(H,a,b) for a,b in itertools.combinations(set(A)-set(C),2))

def are_separated_from(G,A,C):
    """
    Return set of vertices of G that are separated from all of A-C in G-C.
    """
    H=G.copy()
    for v in C:
        H.remove.node(v)
    return {v for v in set(G)-set(C) if not any(nx.has_path(H,a,v) for a in set(A)-set(C))}
    

def are_crossing_pairs(G,S,T):
    if len(set(S)|set(T))<4:
        return False
    return is_separated_by(G,S,T)
        
def are_crossing_triples(G,S,T):
    if S[2]!=T[2] or len(set(S)|set(T))!=5:
        return False
    return is_separated_by(G,S,T)

def subdivided_K4s(G):
    """
    Generator that yields subdivided K4 subgraphs of G.
    """
    for a,b,c, d in itertools.combinations(G,4):
        for pathab in nx.all_simple_paths(G,a,b):
            if c in pathab or d in pathab:
                continue
            Hab=G.subgraph(set(G)-(set(pathab)-{a,b}))
            for pathac in nx.all_simple_paths(Hab,a,c):
                if b in pathac or d in pathac:
                    continue
                Habc=Hab.subgraph(set(Hab)-(set(pathac)-{a,c}))
                for pathad in nx.all_simple_paths(Habc,a,d):
                    if b in pathad or c in pathad:
                        continue
                    Ha=Habc.subgraph(set(Habc)-(set(pathad)-{a,d}))
                    for pathbc in nx.all_simple_paths(Ha,b,c):
                        if a in pathbc or d in pathbc:
                            continue
                        Ha_bc=Ha.subgraph(set(Ha)-(set(pathbc)-{b,c}))
                        for pathbd in nx.all_simple_paths(Ha_bc,b,d):
                            if a in pathbd or c in pathbd:
                                continue
                            Ha_b=Ha_bc.subgraph(set(Ha_bc)-(set(pathbd)-{b,d}))
                            for pathcd in nx.all_simple_paths(Ha_b,c,d):
                                if a in pathcd or b in pathcd:
                                    continue
                                yield G.edge_subgraph([(p[i],p[i+1]) for p in [pathab,pathac,pathad,pathbc,pathbd,pathcd]  for i in range(len(p)-1)])
              
def branches(S):
    """
    If S is a subdivided K4, generate the six arc subgraphs.
    """
    essential_vertices={v for v in S if len(S[v])==3}
    for a,b in itertools.combinations(essential_vertices,2):
        for path in nx.all_simple_paths(S,a,b):
            if len(set(path)&essential_vertices)==2:
                yield S.edge_subgraph((path[i],path[i+1]) for i in range(len(path)-1))


def Edletzberger_A1(G,A):
    for a,b in itertools.combinations(A,2):
        if not (a in G[b] or is_cut_set(G,{a,b})):
            return False
    return True

def Edletzberger_A2(G,A,subdivided_K4s_of_G=None):
    if subdivided_K4s_of_G is None:
        K4s=[x for x in subdivided_K4s(G)]
    else:
        K4s=subdivided_K4s_of_G
    for K in K4s:
        if len(set(A)&set(K))>2:
            if not any(set(A)<=set(B) for B in branches(K)):
                return False
    return True

def Edletzberger_A1A2_extensions(G,A,B,subdivided_K4s_of_G=None):
    """
    Assuming G is a triangle-free graph with ordered vertices and A and B are disjoint subsets of vertices such that A satisfies A1 and A2, yields maximal extensions of A by elements of B that stulll satisfy A1 and A2.
    """
    if subdivided_K4s_of_G is None:
        K4s=[x for x in subdivided_K4s(G)]
    else:
        K4s=subdivided_K4s_of_G
    A_is_relatively_maximal=True
    for v in B:
        Aprime=A|set([v,])
        if Edletzberger_A1(G,Aprime) and Edletzberger_A2(G,Aprime,K4s):
            A_is_relatively_maximal=False
            for E in Edletzberger_A1A2_extensions(G,Aprime,{w for w in B if w>v},K4s):
                yield E
    if A_is_relatively_maximal: # there is no extnsion of A using only elements of B
        therest=set(G)-(set(A)|set(B))
        if not therest:
            yield A
        elif (not is_clique(G,A)) and (not any(Edletzberger_A1(G,A|set([v,])) and Edletzberger_A2(G,A|set([v,]),K4s) for v in therest)):
            # there is no extnesion of A satisfuing A1 and A2 by any element we didn't already consider, so A is really maximal
            yield A

def Edletzberger_A_sets(G,cut_pairs_of_G=None,subdivided_K4s_of_G=None):
    """
    Yield sets satsifying conditions (A1), (A2), (A3) of Proposition 3.16.
    """
    if subdivided_K4s_of_G is None:
        K4s=[x for x in subdivided_K4s(G)]
    else:
        K4s=subdivided_K4s_of_G
    if cut_pairs_of_G is None:
        cuts={C for C in cut_pairs(G)}
    else:
        cuts=cut_pairs_of_G
    for A in set(cuts)|set(G.edges()):
        B={v for v in set(G) if v>max(set(A))}
        for Aprime in Edletzberger_A1A2_extensions(G,set(A),B,K4s):
            if not is_clique(G,Aprime):
                yield Aprime

def Edletzberger_wheels(G,cut_triples_of_G=None):
    """
    Generator that yields "wheels" of either a single, uncrossed cut triple or a set of cut triples that form a hanging wheel.
    """
    if cut_triples_of_G is None:
        trips=cut_triples(G)
    else:
        trips=cut_triples_of_G
    hubs={T[2] for T in trips}
    for hub in hubs:
        wheels=[]
        for T in (T for T in trips if T[2]==hub):
            for wheel in wheels:
                if  any(are_crossing_triples(G,T,S) for S in wheel):
                    wheel.add(T)
                    break
            else:
                wheels.append(set([T,]))
        for wheel in wheels:
            yield wheel


def Edletzberger_B1(G,B,precomputed_two_ended_essential_special_subgroups=None):
    """
    Check if the set B of essential  vertices of G satisfies condition B1.
    """
    if precomputed_two_ended_essential_special_subgroups is None:
        EV={v for v in G if len(G[v])>=3}
        T=two_ended_special_subgroups(G,EV)
    else:
        T=precomputed_two_ended_essential_special_subgroups
    return all(not is_separated_by(G,B,C) for C in T)
   
 
                
def Edletzberger_B_sets(G):
    """
    Generate maximal sets of essential vertices of a 1--ended 2--dimensional RA Coxeter system defined by G that are not separated by any 2--ended special subgroup.
    """
    EV={v for v in G if len(G[v])>=3}
    if len(EV)<4: # condition B3 can't be satisfied
        return
    T=[C for C in two_ended_special_subgroups(G,EV)]
    # consruct the poset of subsets of EV of size at least 4 that satisfy B1. Then we'll find the maximal elements. 
    poset_of_B1_sets=nx.DiGraph()
    for B in itertools.combinations(EV,4): # start with sets of size 4
        if Edletzberger_B1(G,B,T):
            poset_of_B1_sets.add_node(B)
    newvertices={B for B in poset_of_B1_sets}
    while newvertices:
        B=newvertices.pop()
        for v in EV-set(B):
            superB=list(B)+[v,]
            if Edletzberger_B1(G,superB,T):
                superB.sort()
                superB=tuple(superB)
                if superB not in poset_of_B1_sets:
                    poset_of_B1_sets.add_node(superB)
                    newvertices.add(superB)
                    for C in poset_of_B1_sets:
                        if set(C)<set(superB):
                            poset_of_B1_sets.add_edge(C,superB)
                        elif set(superB)<set(C):
                            poset_of_B1_sets.add_edge(superB,B)
    # condition B2 is satisfied for the vertices of poset_of_B1_sets with no outgoing edges
    for B in (node for node, out_degree in poset_of_B1_sets.out_degree() if out_degree == 0):
        yield B

def graph_of_cylinders(G,subdivided_K4s_of_G=None,assume_triangle_free=False,assume_one_ended=False):
    """
    Returns the graph of cylinders for 2--ended splittings of a 1--ended 2--dimensional right angled Coxeter group.
    """
    if not assume_one_ended:
        if not is_one_ended(G):
            NotImplemented
    if not assume_triangle_free:
        if not is_triangle_free(G):
            NotImplemented
    if subdivided_K4s_of_G is None:
        K4s=[x for x in subdivided_K4s(G)]
    else:
        K4s=subdivided_K4s_of_G
    cuts=[C for C in cut_pairs(G)]
    trips=[T for T in cut_triples(G)]
    uncrossedcuts=[C for C in cuts if not any(are_crossing_pairs(G,C,D) for D in cuts)]
    uncrossedtrips=[]
    wheels=[]
    for W in Edletzberger_wheels(G,trips):
        if len(W)==1:
            uncrossedtrips.append(list(W)[0])
        else:
            wheels.append(tuple(set().union(w for w in W)))
    cylinders=[('C',(a,b),tuple(sorted(c for c in set(G[a])&set(G[b])))) for (a,b) in uncrossedcuts]+[('C',(a,b),tuple(sorted(d for d in set(G[a])&set(G[b])))) for (a,b,c) in uncrossedtrips]
    rigid=[('R',)+tuple(sorted(B)) for B in Edletzberger_B_sets(G)]
    hanging=[('H',)+tuple(sorted(set().union(*[set(x) for x in wheel]))) for wheel in wheels]+[('H',)+tuple(sorted(A)) for A in Edletzberger_A_sets(G,cuts,K4s) if not any(A<=support(C[1:]) for C in cylinders)]
    T=nx.Graph()
    T.add_nodes_from(cylinders+rigid+hanging)
    for C in cylinders:
        for NC in rigid+hanging:
            if set(C[1])<=set(NC[1:]):
                T.add_edge(C,NC)
    return T

def is_surface_type(G):
    return len(G)>=4 and nx.is_connected(G) and all(len(G[v])==2 for v in G)

def is_rigid(G,assume_triangle_free=False,assume_one_ended=False):
    if not assume_one_ended:
        if not is_one_ended(G):
            NotImplemented
    if not assume_triangle_free:
        if not is_triangle_free(G):
            NotImplemented
    cuts=itertools.chain.from_iterable([cut_pairs(G),cut_triples(G)])
    try:
        next(cuts)
        return False
    except StopIteration:
        return True
    
def has_cycle_of_cylinders(G,T=None,**kwargs):
    if T is None:
        T=graph_of_cylinders(G,kwargs)
    if len(T)==1:
        return False
    cylinder_incidence_graph=nx.Graph()
    for cylinder in (v for v in T if v[0]=='C'):
        pole=cylinder[1]
        cylinder_incidence_graph.add_edge(*pole)
    return not nx.is_forest(cylinder_incidence_graph)
        
    
    
    
                                
# ----------more CFS stuff
def get_CFS_spanning_subgraph(G,max_edges_to_remove=1):
    if not is_CFS(G):
        raise ValueError
    for E in range(max(len(G)-1,len(G.edges())-max_edges_to_remove),len(G.edges())):
        for edges in itertools.combinations(G.edges(),E):
            H=G.edge_subgraph(edges)
            if len(H)<len(G):
                continue
            if is_CFS(H):
                return H
    return None

def is_minCFS_hierarchy(G):
    return bool(get_minCFS_hierarchy(G))

def get_minCFS_hierarchy(G):
    T=get_iterated_construction(G,max_cone_size=2,only_minCFS=True)
    if is_induced_square(G,G):
        return [G,]
    if len(G)<=4:
        return list([])
    if not is_minimal_CFS(G):
        return list([])
    for v in G:
        if len(G[v])!=2:
            continue
        H=G.subgraph([w for w in G if w!=v])
        if not is_minimal_CFS(H):
            continue
        subhierarchy=get_minCFS_hierarchy(H)
        if subhierarchy:
            return [G,]+subhierarchy
    return list([])


def get_iterated_construction(G,max_cone_size=float('inf'),only_minCFS=False,only_cones=False):
    """
    Return a rooted directed tree T whose source vertex is the graph G and such that at each vertex H there are the following possibiliies:
    H is a square graph and T has no outgoing edges at H
    There is a CFS subgraph H' = H - {v}, and T has a single outgoing edge at H going to H'
    H splits as an amalgam of CFS subgraphs A and B, and T has 2 outgoing edges at H, going to A and B

    If only_cones=True only check for splittings as cone of a subgraph, not as amalgam.

    Return an empty tree if G is not CFS.
    """
    # search prefers coning over amalgams, so if it is possible to build G via a sequence of cones offs then the resulting T will be a line where each edge is a cone off. 
    T=nx.DiGraph()
    if is_induced_square(G,G):
        T.add_node(G)
        return T
    if not is_CFS(G):
        return T
    if only_minCFS and not is_minimal_CFS(G):
        return T
    for v in G:
        if len(G[v])>max_cone_size:
            continue
        H=G.subgraph([w for w in G if w!=v])
        if only_minCFS and not is_minimal_CFS(H):
            continue
        subtree=get_iterated_construction(H,max_cone_size,only_minCFS)
        if subtree:
            T.add_edges_from(subtree.edges())
            T.add_edge(G,H)
            return T
    if not only_cones:
        for A,B in distillations(G,only_minCFS=only_minCFS,non_cone=True):
            sgA=G.subgraph(A)
            sgB=G.subgraph(B)
            subtreeA=get_iterated_construction(sgA,max_cone_size,only_minCFS)
            subtreeB=get_iterated_construction(sgB,max_cone_size,only_minCFS)
            if subtreeA and subtreeB:
                T.add_edges_from(subtreeA.edges())
                T.add_edges_from(subtreeB.edges())
                T.add_edge(G,sgA)
                T.add_edge(G,sgB)
                return T
    return T


def square_graph(G):
    """"
    Graph with one vertex for each indced square in G and an egde between vertices if the corresponding squares contain a diagonal in their intersection. 
    """
    SG=nx.Graph()
    if len(G)<4:
        return SG
    for S in induced_squares(G):
        SG.add_node(tuple(sorted(S)))
    for (S,T) in itertools.combinations(SG,2):
        I=set(S)&set(T)
        if len(I)==3:
            SG.add_edge(S,T)
        elif len(I)==2:
            a,b=I
            if a not in G[b]:
                SG.add_edge(S,T)
    return SG

def diagonal_graph(G):
    DG=nx.Graph()
    if len(G)<4:
        return DG
    for S in induced_squares(G):
        DG.add_edge((S[0],S[2]),(S[1],S[3]))
    return DG


        
def support(C):
    """
    C is a collection of collections of vertices of a graph. Return the set of vertices of G that occur in C.
    """
    return set().union(*[set(x) for x in C])

#-------------- general graph structure
def bipartition(G):
    """
    Given a graph G, return two disjoint subset of vertices such that each set contains no adjacent vertices, and their union is all vertices of G. 
    Raise an error if G is not bipartite.
    """
    spheres=dict()
    radius=0
    spheres[-1]=set([])
    spheres[0]=set([min(C) for C in nx.connected_components(G)])
    while sum(len(spheres[r]) for r in spheres)<len(G):
        next_sphere=(set().union(*[set(G[v]) for v in spheres[radius]]))-(spheres[radius]|spheres[radius-1])
        if G.subgraph(next_sphere).edges():
            raise ValueError("Input graph is not bipartite")
        radius+=1
        spheres[radius]=next_sphere
    return set().union(*[spheres[r] for r in spheres if not r%2]),set().union(*[spheres[r] for r in spheres if  r%2])
    


def two_ended_special_subgroups(G,V=None):
    """
    Generator that yields vertices of G that generate a two-ended subgroup of the RACG.
    If V, a subset of vertices of G, is given, then only yield subsets of V.
    """
    if V is None:
        theverts=[v for v in G]
    else:
        theverts=[v for v in V]
    if len(theverts)<2:
        return
    theverts.sort()
    for i in range(len(theverts)-1):
        a=theverts[i]
        for j in range(i+1,len(theverts)):
            b=theverts[j]
            if b not in G[a]:
                yield (a,b)
                for c in set(G[a])&set(G[b]):
                    yield (a,c,b)


    

def triangles(G,V=None):
    """
    Generator that returns triangles of G.
    If V, a subset of vertices of G, is given then only yield triangles whose vertices all belong to V. 
    """
    if V is None:
        theverts=[v for v in G]
    else:
        theverts=[v for v in V]
    if len(theverts)<3:
        return
    else:
        theverts.sort()
        for i in range(len(theverts)-2):
            a=theverts[i]
            for b,c in itertools.combinations([v for v in set(G[a])&set(theverts) if v>a],2):
                if b in G[c]:
                    if b<c:
                        yield (a,b,c)
                    else:
                        yield (a,c,b)

def is_triangle_free(G,V=None):
    if len(G.edges())>len(G)**2/4:
        return False
    T=triangles(G,V)
    try:
        next(T)
    except StopIteration:
        return True
    return False

                
def induced_squares(G,V=None):
    """
    Generator that returns induced squares of G in the form (a,b,c,d) such that (a,c) and (b,d) are diagonals and (a,b,c,d) is lexicographically minimal amoung permutations of these four vertices.
    If V, a subset of vertices of G, is given then only yield squares whose vertices all belong to V. 
    """
    if V is None:
        theverts=set(G.nodes())
    else:
        theverts=set(V)
    for a in theverts:
        for b,d in itertools.combinations([v for v in set(G[a])&theverts if v>a],2):
            if b in G[d]:
                continue
            for c in (c for c in theverts&set(G[b])&set(G[d]) if a<c and a not in G[c]):
                if b<d:
                    yield (a,b,c,d)
                else:
                    yield (a,d,c,b)

def all_squares(G,V=None):
    """
    Generator that returns squares of G in the form (a,b,c,d) such that (a,c) and (b,d) are diagonals and (a,b,c,d) is lexicographically minimal amoung permutations of these four vertices.
    If V, a subset of vertices of G, is given then only yield squares whose vertices all belong to V. 
    """
    if V is None:
        theverts=set(G.nodes())
    else:
        theverts=set(V)
    for a in theverts:
        for b,d in itertools.combinations([v for v in set(G[a])&theverts if v>a],2):
            for c in (c for c in theverts&set(G[b])&set(G[d]) if a<c):
                if b<d:
                    yield (a,b,c,d)
                else:
                    yield (a,d,c,b)


def simple_cycles_undirected(G):
    simple_cycles=dict()
    cycle_list=[]
    for c in nx.simple_cycles(G.to_directed()):
        if len(c)>2:
            if not len(c) in simple_cycles:
                simple_cycles[len(c)]=set([tuple(c),])
            else:
                if any(set(c)==set(x) for x in simple_cycles[len(c)]):
                    pass
                else:
                    simple_cycles[len(c)].add(tuple(c))
    for L in (L for L in range(3,1+max(x for x in simple_cycles)) if L in simple_cycles):
        for c in simple_cycles[L]:
            cycle_list.append(c)
    return cycle_list

def is_join(G):
    v=[v for v in G][0]
    for B in itertools.chain.from_iterable(itertools.combinations(G[v],n) for n in range(1,1+len(G[v]))):
        A=set(G)-set(B)
        if all(a in G[b] for b in B for a in A):
            return True
    return False


def is_clique(G,C):
    return 2*len(G.subgraph(C).edges())==len(C)*(len(C)-1)

def is_induced_square(G,S):
    if len(set(S))!=4:
        return False
    inducedsubgraph=G.subgraph(S)
    return len(inducedsubgraph.edges())==4 and all(inducedsubgraph.degree(v)==2 for v in S)

def is_square(G,S):
    if len(set(S))!=4:
        return False
    a,b,c,d=S
    if b not in G[a]:
        a,b,c,d=a,c,b,d
        if b not in G[a]:
            return False
    if d not in G[a]:
        a,b,c,d=a,b,d,c
        if d not in G[a]:
            return False
    if c not in set(G[b])&set(G[d]):
        return False
    return True

        

def diagonal_pairs(G,S):
    a,b,c,d=tuple(S)
    if a in G[b]:
        if a in G[c]:
            return ((a,d),(b,c))
        else:
            return ((a,c),(b,d))
    else:
        return ((a,b),(c,d))

    

def is_triangle(G,S):
    if len(S)!=3:
        return False
    inducedsubgraph=G.subgraph(S)
    return len(inducedsubgraph.edges())==3


def convex_hull(G,S):
    firsthull=set(S)
    for  v,w in itertools.combinations(S,2):
        if nx.has_path(G,v,w):
            firsthull.update(*[P  for P in nx.all_shortest_paths(G,v,w)])
    if S==firsthull:
        return firsthull
    else:
        return convex_hull(G,firsthull)

def link(G,v):
    return set(G[v])

def star(G,v):
    return set([v,])|link(G,v)

def distance_two(G,v):
    """
    Return the set of vertices at distance 2 from v in graph G.
    """
    return (set().union(*[set(G[w]) for w in G[v]]))-star(G,v)



def color_verts(G):
    nodelist=list(G.nodes())
    for i in range(len(nodelist)):
        G.nodes[nodelist[i]]['color']=plt.cm.gist_rainbow(.1+i/(len(nodelist)+1))
        
# some example graphs

def Davis_Januskiewicz(Gamma):
    """
    Given a graph Gamma defining a right-angled Artin group G, return a graph defining a right-angled Coxeter group that is commensurable to G. This is the graph Gamma' of Davis-Januskiewicz 2000.
    """
    Gammaprime=nx.Graph()
    for v,w in Gamma.edges():
        Gammaprime.add_edge((v,1),(w,-1))
        Gammaprime.add_edge((v,-1),(w,1))
        Gammaprime.add_edge((v,1),(w,1))
        Gammaprime.add_edge((v,-1),(w,-1))
    return Gammaprime

def suspension(n):
    G=nx.graph()
    for i in range(1,n+1):
        G.add_edge(0,i)
        G.add_edge(1,i)
    return G

def Pallavi(height,vertex=(0,0)):
    G=nx.Graph()
    for level in range(1,1+height):
        for i in range(3):
            G.add_edge((i,level),(i,level-1))
        G.add_edge((2,level),(0,level-1))
    for level in range(0,1+height):
        G.add_edge((0,level),(1,level))
        G.add_edge((1,level),(2,level))
    G.add_edge((2,height),vertex)
    return G
        
def nested_suspension(n):
    G=nx.Graph()
    for i in range(1,1+n):
        if i%2:
            olda=((i+1)//2,0)
            oldb=(-(i+1)//2,0)
            newa=(0,(i+1)//2)
            newb=(0,-((i+1)//2))
        else:
            newa=((i+2)//2,0)
            newb=(-(i+2)//2,0)
            olda=(0,(i+1)//2)
            oldb=(0,-((i+1)//2))
        G.add_edge(olda,newa)
        G.add_edge(oldb,newa)
        G.add_edge(olda,newb)
        G.add_edge(oldb,newb)
    return G
          
def powerset(iterable,minsize=0,maxsize=float('inf')):
    aslist=list(iterable)
    return itertools.chain.from_iterable(itertools.combinations(aslist, r) for r in range(minsize,1+min(maxsize,len(aslist))))

def thenonconstructablemincfsexample(): # This is a triangle-free, minimal CFS graph that is not strongly CFS. 14 nodes. Smallest known so far.
    G=nx.Graph()
    G.add_edge('w','y')
    G.add_edge('x','y')
    G.add_edge('x','z')
    G.add_edge('z','w')
    G.add_edge('x','y2')
    G.add_edge('y2','w2')
    G.add_edge('w2','z')
    G.add_edge('w2','p1')
    G.add_edge('x','p1')
    G.add_edge('z','x1')
    G.add_edge('w','y1')
    G.add_edge('x1','y1')
    G.add_edge('w','p2')
    G.add_edge('x1','p2')
    G.add_edge('y','x2')
    G.add_edge('w','z2')
    G.add_edge('x2','z2')
    G.add_edge('w','p4')
    G.add_edge('x2','p4')
    G.add_edge('y','w1')
    G.add_edge('x','z1')
    G.add_edge('w1','z1')
    G.add_edge('e','z2')
    G.add_edge('e','y')
    G.add_edge('f','y')
    G.add_edge('f','z2')
    G.add_edge('a','x')
    G.add_edge('a','y2')
    G.add_edge('a','z')
    G.add_edge('a','y1')
    G.add_edge('a','w1')
    G.add_edge('a','e')
    G.add_edge('a','f')
    G.add_edge('b','x')
    G.add_edge('b','y2')
    G.add_edge('b','z')
    G.add_edge('b','y1')
    G.add_edge('b','w1')
    return G
