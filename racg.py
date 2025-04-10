import networkx as nx # Works with networkx 3.2.1. (Prior to 3.1, nx.simple_cycles only works for directed graphs.)
from networkx.algorithms import bipartite
import itertools
import math
import copy


# These are used by the drawing functions draw, draw_Dani_Levcovitz_pair, draw_Dani_Levcovitz_in_diagonal to draw interactive graphs, in which vertices can be repositioned and vertices and edges can be added or removed. Can be commented out if you don't want to draw graphs, or will draw them using some other graph drawing package. 
import matplotlib.pyplot as plt
from matplotlib.colors import Colormap
import netgraph



import cmath # This is only used in graph2tikz to export graph to tikz format for inclusion into latex. 





"""
All of these functions work with graphs represented by nx.Graph class. 

Most implementations are currently for triangle-free graphs. May give wrong answers if the graph has triangles!
"""










def draw(G,H=None,K=None,node_labels=True,**kwargs):
    """
    Draw the graph G as an interactive graph.
    By default edges of G are black.
    If a subgraph H is given then its edges are red.
    If a subgraph K is given its edges are blue.
    If both H and K are given then their common edges are purple.  
    Other kwargs passed to netgraph.
    """
    # Positioning nodes by argument is possible. At some point the syntax changed in netgraph, so the argument is either node_layout=pos or node_positions=pos, depending on your version of netgraph. In both cases pos is a dict with keys the vertices and values the coordinates of each vertex. 
    # If you just want to see the graph G and perhaps reposition vertices then you can call draw(G). If you want to add or remove vertices and edges using the interactive features of netgraph call pi=draw(G), edit in the popup window, and then then new graph will be available in the plot instance pi.
    # netgraph gives an error if you try to draw a graph with no edges.
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
    if node_labels:
        nodedict=dict() # avoid having the word "frozenset" printed in node labels
        for g in G:
            if type(g)==frozenset:
                if any(type(x)==frozenset for x in g):
                    nodedict[g]=tuple([x if type(x)!=frozenset else tuple(x) for x in g])
                else:
                    nodedict[g]=tuple(g)
            else:
                try:
                    if any(type(x)==frozenset for x in g):
                        nodedict[g]=tuple([x if type(x)!=frozenset else tuple(x) for x in g])
                    else:
                        nodedict[g]=tuple(g)
                except TypeError:
                    nodedict[g]=g
        plot_instance = netgraph.EditableGraph(G,node_labels=nodedict,node_label_fontdict=dict(size=11),edge_color=edge_color,**kwargs)
    else:
        plot_instance = netgraph.EditableGraph(G,node_labels=False,node_label_fontdict=dict(size=11),edge_color=edge_color,**kwargs)
    plt.show(block=False)
    return plot_instance






    
def is_CFS(G,precomputed_diagonal_graph=None):
    """
    True if G is a CFS graph, which means that, modulo deleting a join, the square graph of G contains a component with full support.

    >>> G=cycle_graph(4); is_CFS(G)
    True
    >>> G=cycle_graph(5); is_CFS(G)
    False
    >>> G=suspension(3); is_CFS(G)
    True
    """
    Gprime=G.subgraph([v for v in G if G.degree[v]<len(G)-1]) # Gprime is G minus cone vertices
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

def is_strongly_CFS(G):
    """
    Decide if the square graph of G is connected and has full support.

    >>> G=circulant(11,3); is_strongly_CFS(G)
    True
    >>> G.remove_node(10); is_strongly_CFS(G)
    False
    """
    Gprime=G.subgraph([v for v in G if G.degree[v]<len(G)-1])
    dg=diagonal_graph(Gprime)
    if not dg:
        return not bool(Gprime)
    if not nx.is_connected(dg):
        return False
    return support(dg)==set(Gprime)



def is_minsquare(G,V=None):
    """
    Determine if induced subgraph H of G spanned by V is a minsquare subgraph of G; that is, H is square-complete, contains a square, and is minimal among subgraphs of G with these properties.
    If V is None, determine if G itself is minsquare.

    >>> G=nx.Graph(); G.add_edges_from([(0,1),(0,3),(0,9),(1,2),(1,4),(2,3),(2,5),(3,4),(3,6),(4,5),(4,7),(5,6),(5,8),(6,7),(6,9),(7,8),(8,9)]); is_minsquare(G)
    False
    >>> is_minsquare(G,{0,3,6,9})
    True
    """
    if V is None:
        verts=set(G)
    else:
        verts=V
    return any(verts==set(H) for H in minsquare_subgraphs(G))

                    
def is_minimal_CFS(G,max_edges_to_remove=1):
    """
    Default only checks that no spanning subgraph with one fewer edge is CFS. A priori it might be necesasry to remove several edges to verify nonminimality. Use max_edges_to_remove=float('inf') to check all possible subgraphs, but this can take a long time.
    If G is triangle-free then it is not necessary to remove multiple edges, one is always enough. 
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








                
#---------   Graph doubles, Davis-Januskiewwicz, doubling over a vertex link or star.
def Davis_Januskiewicz(Gamma):
    """
    Given a graph Gamma defining a right-angled Artin group G, return a graph defining a right-angled Coxeter group that is commensurable to G. This is the graph Gamma' of Davis-Januszkiewicz 2000. Also called the 'graph double' of Gamma.
    """
    return double(Gamma)

def double(Gamma):
    """
    Return double of Gamma.
    """
    Gammaprime=nx.Graph()
    for v,w in Gamma.edges():
        Gammaprime.add_edge((v,1),(w,0))
        Gammaprime.add_edge((v,0),(w,1))
        Gammaprime.add_edge((v,1),(w,1))
        Gammaprime.add_edge((v,0),(w,0))
    return Gammaprime

def is_double(G):
    """
    Return bool(G is a double graph).
    >>> G=double(nx.path_graph(4)); is_double(G)
    True
    >>> G.add_edges_from([((0,2),(1,0)),((0,2),(1,1))]); is_double(G)
    False
    """
    #Characterization of double graphs: for each link that occurs in G, the set of vertices having that link has even order.
    Gemini=twin_module_graph(G)
    return not any(Gemini.nodes[M]['weight']%2 for M in Gemini)
    

def undouble(G):
    """
    Return a graph of which G is a double.
    >>> G=nx.path_graph(4); nx.is_isomorphic(G,undouble(double(G)))
    True
    """
    T=twin_module_graph(G)
    assert(not any(len(M)%2 for M in T)) # if not, this graph is not a double
    twinpartition=dict()
    for M in T:
        aslist=list(M)
        pairs=[]
        thehalf=len(M)//2
        for i in range(thehalf):
            pairs.append({aslist[i],aslist[i+thehalf]})
        twinpartition[M]=pairs
    U=nx.Graph()
    for M,N in T.edges():
        for p,q in itertools.product(twinpartition[M],twinpartition[N]):
            U.add_edge(frozenset(p),frozenset(q))
    return U
                            




def link_double(Gamma,vertex):
    """
    Return graph that is double of Gamma over link of vertex, removing vertex. For right-angled Coxter groups this defines an index 2 subgroup.
    >>> G=cycle_graph(4); H=link_double(G,0); nx.is_isomorphic(G,H)
    True
    """
    Gammaprime=nx.Graph()
    for v,w in Gamma.edges():
        if v==vertex or w==vertex:
            if w==vertex:
                v,w=w,v
            Gammaprime.add_node((w,0))
        elif v in Gamma[vertex] and w in Gamma[vertex]:
            Gammaprime.add_edge((v,0),(w,0))
        elif v in Gamma[vertex] or w in Gamma[vertex]:
            if w in Gamma[vertex]:
                v,w=w,v
            Gammaprime.add_edge((v,0),(w,0))
            Gammaprime.add_edge((v,0),(w,1))
        else:
            Gammaprime.add_edge((v,0),(w,0))
            Gammaprime.add_edge((v,1),(w,1))
    return Gammaprime

def involutions_without_fixed_edges(G):
    """
    Generate nontrivial involutions of G without edge inversions.
    """
    augmentedG=G.copy()
    maxdeg=max(G.degree(v) for v in G)
    for v in G:
        augmentedG.nodes[v]['number_of_neighbors_by_valence']=tuple([len([w for w in G[v] if G.degree(w)==d]) for d in range(1,maxdeg+1)])
    for A in nx.algorithms.isomorphism.vf2pp_all_isomorphisms(augmentedG,augmentedG,node_label='number_of_neighbors_by_valence'):
        if any(A[A[v]]!=v for v in G): # only want order 2
            continue
        if any((A[v],A[w]) in {(w,v),(v,w)} for v,w in G.edges): # don't want edges fixed. This also rules out identity, if the graph has any edges.
            continue
        yield A

def has_link_undoubling(G):
    the_gen=get_link_undoubling(G)
    try:
        next(the_gen)
        return True
    except StopIteration:
        return False

        
def get_link_undoubling(G,name_of_new_vertex=None,forbidden_link=None):
    if name_of_new_vertex is None:
        new_vertex=0
        while new_vertex in G:
            new_vertex+=1
    else:
        new_vertex=name_of_new_vertex
    for A in involutions_without_fixed_edges(G):
        fixed={v for v in G if A[v]==v}
        if forbidden_link is not None:
            if fixed==set(forbidden_link):
                continue
        if len(fixed)<2 or len(fixed)>=len(G)-2:
            continue
        comps=[C for C in nx.connected_components(G.subgraph(set(G)-fixed))]
        component_permutation=dict()
        for i in range(len(comps)):
            v=next(iter(comps[i]))
            for j in range(len(comps)):
                if A[v] in comps[j]:
                    component_permutation[i]=j
                    break
            else:
                raise ValueError
        if any(component_permutation[i]==i for i in component_permutation):
            continue
        available=set(x for x in component_permutation)
        domain=set()
        while available:
            i=available.pop()
            j=component_permutation[i]
            available.remove(j)
            domain.add(i)
        H=G.subgraph(fixed|set.union(*[comps[i] for i in domain])).copy()
        for v in fixed:
            H.add_edge(v,new_vertex)
        yield H
        
 
    
    
        
    
        
        

def find_in_iterated_double(thegraph,thefunction,maxdoublingdepth=3,verbose=False,return_depth_only=False,startingdepth=0):
    """
    Given an input graph and a function that evaluates on graphs to either None or a set of vertices, do a breadth first search on link doubles of the input graph until the function evaluates to not None.

    Stop after depth maxdoublingdepth. 

    If successfull, output the result of the input function and the doubling sequence used to find the graph with positive answer. Otherwise, return None.

    if return_depth_only=True then output only the depth at which a positive answer is found, or -1 if no answer is found.
    """
    nodes=[v for v in thegraph]
    G=nx.Graph() # make an isomorphic copy of thegraph whose nodes are integers
    for (v,w) in thegraph.edges():
        G.add_edge(nodes.index(v),nodes.index(w))
    def rewrite_tuple(t): # rewrites left nested tuple as one long tuple, with nodes as in input graph
        if type(t)==tuple:
            return (rewrite_tuple(t[0]),t[1])
        else:
            return nodes[t]
    if startingdepth==0:
        if verbose:
            print("Searching with doubling sequence: []")
        result=thefunction(G)
        if result is not None:
            if return_depth_only:
                return 0
            else:
                return result,[]
    currentdepth=1 
    doublingsequences=[[]]
    while currentdepth<=maxdoublingdepth:
        if verbose:
            print('Constructing doubling sequence of length '+str(currentdepth)+'.')
        previous_doublingsequences=doublingsequences
        doublingsequences=[]
        for ds in previous_doublingsequences:
            prevdouble=G
            lastlink=set()
            for v in ds:
                lastlink=link(prevdouble,v)
                prevdouble=link_double(prevdouble,v)
            EQ=vertex_equivalence_classes(prevdouble)
            EQreps=sorted([min(EQclass) for EQclass in EQ])
            for v in EQreps:
                if lastlink and v[0] in lastlink:
                    if v[0]<ds[-1]: # link doubling over adjacent vertices commutes. Skip this possibility because it is isomorphic to a graph already considered. 
                        continue
                new_ds=ds+[v,]
                thisdouble=link_double(prevdouble,v)
                doublingsequences.append(new_ds)
                if currentdepth>=startingdepth:
                    if verbose:
                        print("Searching with doubling sequence: "+str(new_ds))
                    result=thefunction(thisdouble)
                    if result is not None:
                        if return_depth_only:
                            return currentdepth
                        else:
                            return result,[rewrite_tuple(t) for t in new_ds]
        currentdepth+=1
    if return_depth_only:
        return -1
    else:
        return None

def star_double(Gamma,vertex):
    """
    Return graph that is double of Gamma over the star of vertex. For right-angled Artin groups this defines an index 2 subgroup.
    """
    Gammaprime=nx.Graph()
    for v,w in Gamma.edges():
        if v==vertex or w==vertex:
            Gammaprime.add_edge((v,0),(w,0))
        elif v in Gamma[vertex] and w in Gamma[vertex]:
            Gammaprime.add_edge((v,0),(w,0))
        elif v in Gamma[vertex] or w in Gamma[vertex]:
            if w in Gamma[vertex]:
                v,w=w,v
            Gammaprime.add_edge((v,0),(w,0))
            Gammaprime.add_edge((v,0),(w,1))
        else:
            Gammaprime.add_edge((v,0),(w,0))
            Gammaprime.add_edge((v,1),(w,1))
    return Gammaprime
    









#--------  stable cycles
# Functions for finding stable cycles in the graph.
# Stable cycle means a cycle that is incuded and square complete,  giving a stable virtual surface subgroup.

def has_stable_cycle(G):
    """
    >>> has_stable_cycle(Pallavi(4,2,(2,0),(2,4)))
    True
    >>> has_stable_cycle(nested_suspension(3))
    False
    """
    try:
        next(get_stable_cycles(G))
    except StopIteration:
        return False
    return True

def get_stable_cycles(G,legalturns=None,precomputeddiagonals=None,forbidden=set()):
    """
    Yield a tuples of vertices representing an induced, square complete cycle in G of length at least 5. 
    """
    if legalturns is None:
        legalturns=get_legal_turns(G)
    if precomputeddiagonals is None:
        thediagonals=diagonals(G)
    else:
        thediagonals=precomputeddiagonals
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
        c=get_stable_cycle_at_vert(G,v,legalturns,prefix=tuple([]),precomputeddiagonals=thediagonals,forbidden=newforbidden)
        if c is not None:
            yield c
        newforbidden.add(v) # no stable cycles at v, so in continuing search do not consider paths through v.
    
def get_stable_cycle(G,legalturns=None,precomputeddiagonals=None,forbidden=set()):
    """
    Return a tuple of vertices representing an induced, square complete cycle in G of length at least 5, if one exists, or None.
    """
    stable_cycle_generator=get_stable_cycles(G,legalturns=legalturns,precomputeddiagonals=precomputeddiagonals,forbidden=forbidden)
    try:
        the_cycle=next(stable_cycle_generator)
        return the_cycle
    except StopIteration:
        return None


    
def is_induced_cycle(G,S):
    """
    Check if the set S is the vertex set of an induced cycle subgraph of G.
    """
    induced_subgraph=G.subgraph(S)
    return all(len(induced_subgraph[v])==2 for v in induced_subgraph) and nx.is_connected(induced_subgraph)
    
def is_stable_cycle(G,S):
    """
    Check if S is the vertex set of an induced cycle subgraph of G that has length at least 5 and is square complete.
    """
    return len(S)>4 and is_induced_cycle(G,S) and  is_square_complete(G,S)

def get_stable_cycle_at_vert(G,v,legalturns,prefix=tuple([]),precomputeddiagonals=None,forbidden=set([])):
    if v in forbidden:
        assert(False)
    if precomputeddiagonals is None:
        thediagonals=diagonals(G)
    else:
        thediagonals=precomputeddiagonals
    current=v
    newforbidden=forbidden | {(set(T)-set([current,])).pop() for T in (T for T in thediagonals if current in T)}
    if not prefix: # we are starting a stable cycle at v, not continuing one already started
        if current not in legalturns:
            return None
        for nextvert in set(legalturns[current])-newforbidden:
            c=get_stable_cycle_at_vert(G,nextvert,legalturns,prefix=(current,),precomputeddiagonals=thediagonals,forbidden=newforbidden)
            if c is not None:
                return c
        return None
    else: # prefix contains a prefix of a stable cycle ending at v. Try to continue it. 
        previousvert=prefix[-1]
        if current not in legalturns[previousvert]:
            return None
        for nextvert in legalturns[previousvert][current]-newforbidden:
            if nextvert in prefix: # this would make a closed loop. Is it stable?
                i=prefix.index(nextvert)
                if current in legalturns and nextvert in legalturns[current] and prefix[i+1] in legalturns[current][nextvert] and len(prefix)-i>3:
                    return prefix[i:]+(current,)
            else: # increment prefix with nextvert and try to continue from nextvert
                c=get_stable_cycle_at_vert(G,nextvert,legalturns,prefix=prefix+(current,),precomputeddiagonals=thediagonals,forbidden=newforbidden)
                if c is not None:
                    return c
        return None
        
def get_legal_turns(G):
    legal=dict()
    for v in G:
        for w in G[v]:
            possible_next=distance_two(G,v) & set(G[w])
            for u in possible_next:
                if all(not is_square(G,{u,v,w,x}) for x in set(G[u])&set(G[v])):
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
#------------------------







#---------- square completion
def is_square_complete(G,S):
    """
    G is nx.Graph, S is a collection of vertices, a collection of edges, or an nx.Subgraph of G. 
    Decide if the induced subgraph of G defined by S is square complete. 
    Return True or False.
    >>> G=nx.Graph(); G.add_edges_from([(0,1),(1,2),(2,3),(0,4),(2,4),(0,5),(5,3),(0,6),(6,3),(0,7),(7,8),(8,3),(9,5),(9,6),(10,5),(10,6)]);
    >>> is_square_complete(G,{0,1,2,3}) 
    False
    >>> is_square_complete(G,{0,3,5,6,9,10})
    True
    >>> H=G.subgraph({4,0,7,8}); is_square_complete(G,H)
    True
    """
    if len(S)<2:
        return True
    induced_subgraph=G.subgraph(S)
    return set(induced_subgraph)==set(get_square_completion(G,S))

def get_square_completion(G,S):
    """
    Given an nx.Graph G and S defining a subgraph return the smallest square complete subgraph of G containing S.
    Return type is nx.SubGraph view.

    >>> G=nx.Graph(); G.add_edges_from([(0,1),(1,2),(2,3),(0,4),(2,4),(0,5),(5,3),(0,6),(6,3),(0,7),(7,8),(8,3),(9,5),(9,6),(10,5),(10,6)]);
    >>> set(get_square_completion(G,{0,1,2,3}))=={0,1,2,3,4,5,6,9,10}
    True
    """
    old_verts=set()
    check_verts=set()
    new_verts=set(G.subgraph(S))
    while new_verts:
        old_verts|=check_verts
        check_verts=new_verts
        new_verts=set()
        H=old_verts|check_verts
        for v in check_verts:
            for w in distance_two(G,v)&H:
                for a,b in itertools.combinations(set(G[v])&set(G[w]),2):
                    if b not in G[a]: # {a,b}*{v,w} is an induced square of G with diagonal {v,w} in H
                        if a not in H:
                            new_verts.add(a)
                        if b not in H:
                            new_verts.add(b)
    return G.subgraph(old_verts|check_verts)
                

def minsquare_subgraphs(G):
    """
    Generate the minsquare subgraphs of an nx.Graph G.
     minsquare = square complete, contains a square, and is minimal with respect to inclusion among such subgraphs. 
    """
    D=diagonal_graph(G)
    components=[tuple(sorted(C)) for C in nx.connected_components(D)]
    component_completion=nx.DiGraph()
    # component_completeion is a graph of components with an edge from A to B if the support of A contains a pair tha are a diagonal of a square appearing as a vertex of B
    for C in components:
        component_completion.add_node(C)
    for C in components:
        S=support(C)
        for x,y in itertools.combinations(S,2):
            if are_diagonal(G,x,y):
                diag=frozenset({x,y})
                for Cprime in components:
                    if diag in Cprime:
                        component_completion.add_edge(C,Cprime)
                        break
                else:
                    raise ValueError("Coulnd't find "+str(diag))
    for sink in minimal_sinks(component_completion):
        yield G.subgraph(set.union(*[support(C) for C in sink]))
    

def minimal_sinks(G):
    """
    Given a directed graph, yield minimal subgraphs with no outoing edges. 
    """
    for C in nx.strongly_connected_components(G):
        if all(w in C for v in C for w in G[v]):
            yield C



def distillations(G,only_minCFS=False,non_cone=False):
    """
    Yield subgraphs A and B of G so that G splits as an amalgam A*_C B whose factors are CFS, such that C=A&B is not a clique.
    """
    # We may assume |A|<=|B|, which implies |C|>=2|A|-|G|
    for A in itertools.chain.from_iterable(itertools.combinations(G,n) for n in range(3,len(G))):
        if not is_CFS(G.subgraph(A)) or (only_minCFS and not is_minimal_CFS(G)):
            continue
        for C in itertools.chain.from_iterable(itertools.combinations(A,n) for n in range(max(2,2*len(A)-len(G)),len(A))):
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

def distillations_over_thick_join(G):
    """
    Yield subgraphs A,B of triangle-free graph G such that G splits as an amalgam A*_C B whose factors are CFS and such that C=A&B is a thick join.
    """
    # C = E*F
    compG=nx.complement(G)
    for E in anticliques(G,minsize=2):
        Fprime=set(G).intersection(*[link(G,v) for v in E])
        if len(Fprime)<2:
            continue
        for F in itertools.chain.from_iterable(itertools.combinations(Fprime,n) for n in range(2,1+len(Fprime))):
            if not is_clique(compG,F):
                continue
            C=set(E)|set(F)
            complementary_components=[set(x) for x in nx.connected_components(G.subgraph(set(G)-C))]
            if len(complementary_components)!=2:
                continue
            A=C|complementary_components[0]
            B=C|complementary_components[1]
            if is_CFS(G.subgraph(A)) and is_CFS(G.subgraph(B)):
                yield G.subgraph(A),G.subgraph(B)
    

    
def reductions(G):
    """
    Yield subgraphs of G with one vertex removed that are still CFS.
    """
    for v in sorted([v for v in G], key=lambda v: len(G[v])):
        H=G.subgraph(set(G)-set([v,]))
        if is_CFS(H):
            yield H
                                           






            
#------------- Dani Levcovitz conditions

def Dani_Levcovitz(Gamma,Lambda,verbose=False):
    """
    Given a triangle-free graph Gamma defining a one-ended RACG and a subgraph Lambda of the complementary graph, check if Lambda defines a finite index RAAG system according to Dani-Levcovitz Theorem 4.8.
    """
    if not (is_triangle_free(Gamma) and is_one_ended(Gamma)):
        raise InputError("Input graph must be triangle-free, planar, without separating cliques.")
    if len([x for x in nx.connected_components(Lambda)])!=2: # Dani-Lavcovitz Corollary 4.9: If W_Gamma is one-ended and 2-dimensional then Lambda only defines a finite index RAAG system if it has exactly 2 components. 
        if verbose:
            print("Lambda has more than two components.")
        return False
    if not Dani_Levcovitz_F1(Gamma,Lambda,verbose):
        return False
    if not Dani_Levcovitz_RAAG_system(Gamma,Lambda,verbose):
        return False
    # Dani-Levcovitz Remark 4.3: If Gamma is conected, Lambda has 2 components, and R2 and F1 are satisfied then F2 is also satisfied, so does not need to be checked separately.
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

def draw_Dani_Levcovitz_in_diagonal(Gamma,Lambda):
    plot_instance=draw(diagonal_graph(Gamma),Dani_Levcovitz_Delta(Gamma,Lambda))
    return plot_instance

def Dani_Levcovitz_Delta(Gamma,Lambda):
    Delta=nx.Graph()
    for (a,b) in Lambda.edges():
        Delta.add_node(frozenset({a,b}))
    for (e,f) in itertools.combinations(Lambda.edges(),2):
        if is_induced_square(Gamma,e|f):
            Delta.add_edge(e,f)
    return Delta

def find_Dani_Levcovitz_subgraph(Gamma,verbose=False,assume_triangle_free=False,assume_CFS=False):
    """
    Given a triangle-free CFS graph Gamma, find a subgraph Lambda of the complementary graph satisfying Dani-Levcovitz conditions. 
    Return None if no such graph exists.


    >>> B=nx.Graph();B.add_edge(0,1);B.add_edge(2,1);B.add_edge(2,3);B.add_edge(3,0);
    >>> D=double(B);D.add_edge((0,0),(4,0));D.add_edge((0,1),(4,0)); D.add_edge((1,0),(5,0));D.add_edge((1,1),(5,0));
    >>> Lambda=find_Dani_Levcovitz_subgraph(D); Dani_Levcovitz(D,Lambda)
    True
    >>> D=double(cycle_graph(8));Lambda=find_Dani_Levcovitz_subgraph(D); Lambda is None
    True
    >>> G=cycle_graph(6); G.add_edge(1,6); G.add_edge(3,6); G.add_edge(5,6); G.add_edge(6,7);G.add_edge(7,0); G.add_edge(7,2);G.add_edge(7,4);Lambda=find_Dani_Levcovitz_subgraph(G); Dani_Levcovitz(G,Lambda)
    True
    """
    # Lambda must have exactly 2 components. Dan-Levcovitz, Fig 3.10, show that more than 2 components implies Gamma contains a triangle. But Lambda can't contain only one component if it is induced and has full support unless Gamma is discrete, which it is not, since it is assumed to be CFS.
    # Lambda must be contained in the subgraph of the complement of G consisting of edges that are diagonals of induced squares, since any other edge would give an isolated vertex in the defining graph of the RAAG, but our W_Gamma is 1-ended, so the RAAG should not have isolated vertices.
    # enumerate non-spanning subtrees Lambda1 of the commuting complementary graph. This will be one component of prospective Lambda. Then enumerate spanning subtrees Lambda2 of commutingGcomp - Lambda1. Lambda2 must be spanning so that Lambda=Lambda1 U Lambda2 has full support.
    if not assume_triangle_free:
        if not is_triangle_free(Gamma):
            raise InputError("Input graph must be triangle-free, planar, without separating cliques.")
    # know some ways to create or obstruct existence of Lambda
    if not is_strongly_CFS(Gamma):
        return None
    Twins=twin_module_graph(Gamma)
    if nx.is_tree(Twins):
        favorite_vertex_in_twin_link=dict()
        favorite_vertex_in_twin_module=dict()
        for M in Twins:
            favorite_vertex_in_twin_link[M]=next(iter(link(Twins,M)))
            favorite_vertex_in_twin_module[M]=next(iter(M))
        M0=next(iter(Twins))
        M1=next(iter(link(Twins,M0)))
        Lambda0_edges=set()
        Lambda1_edges=set()
        for M in Twins:
            if nx.shortest_path_length(Twins,M0,M)%2:
                for v in M:
                    Lambda1_edges.add((v,favorite_vertex_in_twin_module[M]))
                for L in link(Twins,M):
                    Lambda0_edges.add((favorite_vertex_in_twin_module[L],favorite_vertex_in_twin_module[favorite_vertex_in_twin_link[M]]))
            else:
                for v in M:
                    Lambda0_edges.add((v,favorite_vertex_in_twin_module[M]))
                for L in link(Twins,M):
                    Lambda1_edges.add((favorite_vertex_in_twin_module[L],favorite_vertex_in_twin_module[favorite_vertex_in_twin_link[M]]))
        Lambda=nx.Graph()
        for (a,b) in Lambda0_edges|Lambda1_edges:
            if a!=b:
                Lambda.add_edge(a,b)
        assert(Dani_Levcovitz(Gamma,Lambda))
        return Lambda
    else:
        for cycle in geodesic_simple_cycles(Twins):
            if len(cycle)%2 or len(cycle)>6:
                return None
            elif len(cycle)==6:
                for M in link(Twins,cycle[0]) & link(Twins,cycle[2]) & link(Twins,cycle[4]):
                    if link(Twins,M) & link(Twins,cycle[1]) & link(Twins,cycle[3]) & link(Twins,cycle[5]):
                        break
                else:
                    return None
            else:
                pass
    # shortcuts didn't work, start a brute force search
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
        raise InputError("Lambda has more than two components.") # Theorem 3.18 does not apply if Lambda has more than two components.
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

def Dani_Levcovitz_F1(Gamma,Lambda,verbose=False):
    Gammaprime=Gamma.subgraph([v for v in Gamma if Gamma.degree[v]<len(Gamma)])
    if not set(Lambda)==set(Gammaprime):
        if verbose:
            print("Lambda does not have full support.")
        return False
    return True

def Dani_Levcovitz_F2(Gamma,Lambda,verbose=False):
    if has_cone_vertex(Gamma) or not is_triangle_free(Gamma):
        raise InputError("Input graph should be cond-free and triangle-free.")
    # for every pair of distinct components Lambda_1 Lambda_2 of Lambda and vertices v_1 in Lambda_1 and v_2 in Lambda_2, there is a Lambda_1-Lambda_2 path from v_1 to v_2
    for A, B in itertools.combinations(nx.connected_components(Lambda),2):
        reachable=nx.Graph()
        reachable.add_nodes_from(A|B)
        for a in A:
            for b in set(Gamma[a])&B:
                reachable.add_edge(a,b)
        components=[C for C in nx.connected_components(reachable)]
        if len(components)>1:
            if verbose:
                for i in range(len(components)):
                    if len(components[i])==1:
                        print(str(components[i])+" is isolated vertex for Lambda components "+str(A)+" and "+str(B)+".")
                        break
                else:
                    a=next(iter(A&components[0]))
                    b=next(iter(B&components[1]))
                    print("No "+str(A)+"-"+str(B)+" path from "+str(a)+" to "+str(b)+".")
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



def is_satellite(G,v):
    """
    Decide if v is a satellite vertex of G.
    """
    return any(link(G,v)<=link(G,w) for w in distance_two(G,v))

def satellite_dismantling_sequences(G,assume_strong_CFS=False,assume_one_ended=False,assume_triangle_free=False):
    """
    Yield lists V such that V[0] is satellite of G, V[1] is satellite of G-V[:1], V[2] is a satellite of G-V[:2],... ending in a square, and such that each graph in the sequence is strongly CFS.
    """
    if not assume_triangle_free:
        if not is_triangle_free(G):
            raise InputError("Input graph must be triangle-free without separting cliques.")
    if not assume_one_ended:
        if not is_one_ended(G):
            raise InputError("Input graph must be triangle-free without separting cliques.")
    if not assume_strong_CFS:
        if not is_strongly_CFS(G):
            return
    V=list()
    if len(G)==4:
        yield V
    satellitechoices=list()
    satellitechoices.append({v for v in G if is_satellite(G,v)})
    currentindex=0
    while currentindex>=0:
        try:
            nextsatellite=satellitechoices[currentindex].pop()
        except KeyError:
            currentindex-=1
            continue
        V=V[:currentindex]+[nextsatellite,]
        satellitechoices=satellitechoices[:currentindex+1]
        H=G.subgraph(set(G)-set(V))
        if (not is_one_ended(H)) or (not is_strongly_CFS(H)):
            continue
        if len(H)==4:
            yield V
            continue
        satellitechoices.append({v for v in H if is_satellite(H,v)})
        currentindex+=1

def is_suitable_satellite_dismantling_sequence(G,satellite_list,required_Lambda_edges=[]):
    n=len(satellite_list)
    assert(len(G)==n+4)
    if len(G)==4 and len(satellite_list)==0:
        return True
    if any(tuple(edge) in G.edges() for edge in required_Lambda_edges):
        return False
    Gamma=[G.subgraph(set(G)-set(satellite_list[:i])) for i in range(n,-1,-1)]
    required_edges_not_in_base_square=[]
    for edge in required_Lambda_edges:
        p,q=edge
        if p in Gamma[0] and q in Gamma[0]:
            pass
        else:
            for i in range(n):
                if p in Gamma[i]:
                    required_edges_not_in_base_square.append((p,q))
                    break
                if q in Gamma[i]:
                    required_edges_not_in_base_square.append((q,p))
                    break
            else:
                raise ValueError('Did not find required edge')
    x=[None,]+list(reversed(satellite_list))
    N=[link(Gamma[i+1],x[i+1]) for i in range(n)]
    V=[{v for v in Gamma[i] if N[i]<=link(Gamma[i],v)} for i in range(n)]
    for i in range(n):
        Js={j for j in range(i+1,n) if x[i+1] in N[j] and N[j]&set(Gamma[i])}
        V[i]=V[i].intersection(*[N[j] for j in Js])
        if not V[i]:
            return False
        for edge in required_edges_not_in_base_square:
            if edge[1]==x[i+1]:
                V[i]=V[i]&{edge[0]}
                if not V[i]:
                    return False
    return True

def find_suitable_satellite_dismantling_sequence(G,required_edges=[]):
    for satellite_sequence in satellite_dismantling_sequences(G):
        if is_suitable_satellite_dismantling_sequence(G,satellite_sequence,required_edges):
            return satellite_sequence

def exists_DL_relative_to_GOC(G,GOC):
    if is_square(G,set(G)):
        return True
    if any(v[0]=='H' for v in GOC):
        return False
    required_Lambda_edges=[v[1] for v in GOC if v[0]=='C']
    for v in (v for v in GOC if v[0]=='R'):
        required_Lambda_edges_in_this_rigid=[e for e in required_Lambda_edges if set(e)<=set(v[1:])]
        relativesss=find_suitable_satellite_dismantling_sequence(G.subgraph(set(v[1:])),required_Lambda_edges_in_this_rigid)
        if relativesss is None:
            return False
    return True

def exists_DL(G):
    if is_square(G,set(G)):
        return True
    sss=find_suitable_satellite_dismantling_sequence(G)
    return not (sss is None)
                                                                    
    
    
        
        
        
    
    
    



#--------- Nguyen-Tran 

def Nguyen_Tran_tree(G):
    T=nx.Graph()
    for ms in maximal_one_ended_suspension_subgraphs(G):
        T.add_node(ms)
    for v,w in itertools.combinations(T,2):
        if is_induced_square(G,{v[0][0],w[0][0],v[0][1],w[0][1]}):
            T.add_edge(v,w)
    return T

def Nguyen_Tran_condition(G):
    """
    If G is a connected, triangle-free, planar graph with at least 5 vertices and no separating vertex or edge, decides whether or not W_G is quasiisometric to a RAAG using the main theorem of Nguyen-Tran.
    """
    if not (is_triangle_free(G) and is_one_ended(G) and nx.is_planar(G) and len(G)>=5):
        raise InputError("Input graph must be triangle-free, planar, without separating cliques.")
    if is_join(G):
        return True
    T=Nguyen_Tran_tree(G)
    return all(len(T[v])<len(v[1]) for v in T)

def maximal_one_ended_suspension_subgraphs(G):
    """
    Generator that yields maximal suspension subsets of a graph G as tuples ((a,b),(c_1,c_2,....)) such that a and b are the suspension vertices and c_1,c_2,.... are the common neighbors of a and b in G, with at least one pair c_i and c_j are non-adjacent. 
    """
    ordered_nodes=[v for v in G]
    for i in range(len(ordered_nodes)-1):
        for j in (j for j in range(i+1,len(ordered_nodes)) if ordered_nodes[j] not in G[ordered_nodes[i]]):
            a=ordered_nodes[i]
            b=ordered_nodes[j]
            common_neighbors=link(G,a)&link(G,b)
            if is_clique(G,common_neighbors):
                pass # a and b are not suspension points of a one-ended subgraph
            elif len(common_neighbors)>2:
                yield ((a,b),tuple(common_neighbors))
            else: # a and b are diagonal of a square, but the square may be in larger suspension using other diagonal
                c,d=common_neighbors
                k=ordered_nodes.index(c)
                ell=ordered_nodes.index(d)
                if k>ell:
                    k,ell=ell,k
                    c,d=d,c
                if len(link(G,c)&link(G,d))==2:
                    if i<k:
                        yield ((a,b),(c,d))
                    else:
                        pass # The square a,c,b,d is a max suspension subgraph, but we already yielded it because c comes before a in the ordered_nodes list. 
                else:
                    pass # The maximal suspension subgraph for which a,b are suspension points is contained in a larger suspension subgraph for which c,d are the suspension points. 








                
# -------- Edletzberger, construction of JSJ and JSJTOC over 2-ended splittings
def is_cut_set(G,S):
    return not nx.is_connected(G.subgraph(set(G)-set(S)))

def is_one_ended(G):
    if len(G)<4:
        return False
    if not nx.is_connected(G):
        return False
    if is_clique(G,G):
        return False
    maxcliques=[set(C) for C in nx.find_cliques(G)]
    for C in maxcliques:
        if not nx.is_connected(G.subgraph(set(G)-set(C))):
            return False
        if len(C)>1:
            for v in C:
                if link(G,v)<=C:
                    return False
    return True

def is_zero_ended(G):
    return is_clique(G,G)

def is_two_ended(G):
    orderednodes=[v for v in G]
    for i in range(len(orderednodes)-1):
        for j in range(i+1,len(orderednodes)):
            if orderednodes[j] not in G[orderednodes[i]]:
                commonneighbors=link(G,orderednodes[i])&link(G,orderednodes[j])
                if len(commonneighbors)==len(G)-2:
                    return is_clique(G,commonneighbors)
    return False

def is_infinite_ended(G):
    if is_zero_ended(G):
        return False
    if is_two_ended(G):
        return False
    if is_one_ended(G):
        return False
    return True


    
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

def cut_squares(G):
    """
    Generate induced squares in G with more than one complementary component.
    """
    for S in induced_squares(G):
        if not nx.is_connected(G.subgraph(set(G)-set(S))):
            yield S

def has_cut_squares(G):
    """
    Decide if G contains an induced square whose complement has more than one component. 
    """
    cs=cut_squares(G)
    try:
        next(cs)
    except StopIteration:
        return False
    return True

        
def has_two_ended_splitting(G):
    """
    If G is triangle-free and generates a one ended Coxeter group, check if it admits a spliting over a two ended subgroup.
    """
    try:
        next(cut_pairs(G))
        return True
    except StopIteration:
        try:
            next(cut_triples(G))
            return True
        except StopIteration:
            return False
                
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
        for pathab in nx.all_simple_paths(G.subgraph(set(G)-{c,d}),a,b):
            Hab=G.subgraph(set(G)-(set(pathab)-{a,b}))
            for pathac in nx.all_simple_paths(Hab.subgraph(set(Hab)-{b,d}),a,c):
                Habc=Hab.subgraph(set(Hab)-(set(pathac)-{a,c}))
                for pathad in nx.all_simple_paths(Habc.subgraph(set(Habc)-{b,c}),a,d):
                    Ha=Habc.subgraph(set(Habc)-(set(pathad)-{a,d}))
                    for pathbc in nx.all_simple_paths(Ha.subgraph(set(Ha)-{a,d}),b,c):
                        Ha_bc=Ha.subgraph(set(Ha)-(set(pathbc)-{b,c}))
                        for pathbd in nx.all_simple_paths(Ha_bc.subgraph(set(Ha_bc)-{a,c}),b,d):
                            Ha_b=Ha_bc.subgraph(set(Ha_bc)-(set(pathbd)-{b,d}))
                            for pathcd in nx.all_simple_paths(Ha_b.subgraph(set(Ha_b)-{a,b}),c,d):
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
            superB.sort()
            superB=tuple(superB)
            if superB not in poset_of_B1_sets:
                if Edletzberger_B1(G,superB,T):            
                    poset_of_B1_sets.add_node(superB)
                    newvertices.add(superB)
                    for C in [C for C in poset_of_B1_sets if len(C)+1==len(superB)]:
                        if set(C)<set(superB):
                            poset_of_B1_sets.add_edge(C,superB)
                    for C in [C for C in poset_of_B1_sets if len(C)==1+len(superB)]:
                        if set(superB)<set(C):
                            poset_of_B1_sets.add_edge(superB,B)
    # condition B2 is satisfied for the vertices of poset_of_B1_sets with no outgoing edges
    for B in (node for node, out_degree in poset_of_B1_sets.out_degree() if out_degree == 0):
        yield B

def graph_of_cylinders(G,subdivided_K4s_of_G=None,assume_triangle_free=False,assume_one_ended=False):
    """
    Returns the graph of cylinders for 2--ended splittings of a 1--ended 2--dimensional right angled Coxeter group.
    Object is nx.Graph() whose vertices are tuples whose first entry is 'C', 'R', 'H' if vertex if cylinder, rigid, or hanging. A cylinder vertex is of the form ('C',(a,b),(c,d,e...)) where a,b give a cut of G and c,d,e... are their common neighbors. Rigid vertex is of the form ('R',a,b,c....) where the vertex group is generated by a,b,c,.... of G. Similar for hanging. 
    """
    if not assume_one_ended:
        if not is_one_ended(G):
            raise InputError("Input graph must be triangle-free and without separating cliques.")
    if not assume_triangle_free:
        if not is_triangle_free(G):
            raise InputError("Input graph must be triangle-free and without separating cliques.")
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
            raise InputError("Input graph must be triangle-free, planar, without separating cliques.")
    if not assume_triangle_free:
        if not is_triangle_free(G):
            raise InputError("Input graph must be triangle-free, planar, without separating cliques.")
    cuts=itertools.chain.from_iterable([cut_pairs(G),cut_triples(G)])
    try:
        next(cuts)
        return False
    except StopIteration:
        return True
    
def has_cycle_of_cylinders(G,GOC=None,**kwargs):
    if GOC is None:
        GOC=graph_of_cylinders(G,kwargs)
    if len(GOC)==1:
        return False
    cylinder_incidence_graph=nx.Graph()
    for cylinder in (v for v in GOC if v[0]=='C'):
        pole=cylinder[1]
        cylinder_incidence_graph.add_edge(*pole)
    return not nx.is_forest(cylinder_incidence_graph)
        
    
def has_ZZ_RAAG_obstruction(G,GOC=None,**kwargs):
    """
    A RACG that is Qi to a RAAG cannot have in its graph of cylinders a virtual Z^2 edge incident to a rigid vertex that is not virtually Z^2. 
    """
    if GOC is None:
        GOC=graph_of_cylinders(G,kwargs)
    if len(GOC)==1:
        return False
    for (v,w) in GOC.edges():
        if v[0]=='C':
            v,w=w,v
        assert(v[0]=='R')
        rigid_support=set(v[1:])
        cylinder_support=set(w[1])|set(w[2])
        if is_induced_square(G, rigid_support & cylinder_support): # this edge has virtual Z^2 stabilzer
            if not rigid_support <= cylinder_support: # rigid stabilizer is strictly larger than incident edge, so not virtual Z^2
                return True
    return False

def has_iterated_splittings(G,GOC=None,**kwargs):
    """
    Decide if a rigid vertex of the graph of cyliders of a one-ended RACG defined by a triangle-free graph is not Z^2 and admits a splitting over a finite or 2-ended group. 
    """
    if GOC is None:
        GOC=graph_of_cylinders(G,kwargs)
    if len(GOC)==1:
        return False
    for rigid_vertex in {v for v in GOC if v[0]=='R'}:
        H=G.subgraph(rigid_vertex[1:])
        if is_induced_square(G,H):
            continue
        elif not is_one_ended(H):
            return True
        elif has_two_ended_splitting(H):
            return True
    return False



  


def compliant_subsets(G,required_vertices={},verbose=False):
    """
    Given a triangle-free graph G, return non-clique, proper compliant subsets of G as a set of frozensets of vertices of G.  
    Vertices can be used to specify a set of vertices; if Vertices is not None then only compliant sets containing Vertices are returned. 
    """
    old=set()
    new=set()
    V=set(required_vertices)
    for A,B in maximal_joins(G,required_vertices=V,only_thick=True):
        if len(A)>len(B):
            A,B=B,A
        S=A|B
        if verbose:
            print(str(set(A))+"*"+str(set(B))+" is a maximal thick join.")
        new.add(frozenset(S))
        if len(S)>4:
            if len(A)==2 and V<=A:
                new.add(frozenset(A))
                if verbose:
                    print(str(set(A))+" is the pole of "+str(S)+".")
            elif len(B)==2 and V<=B:
                new.add(frozenset(B))
                if verbose:
                    print(str(set(B))+" is the pole of "+str(S)+".")
    def potentialT(S):
        SS=set(S)
        orderednodes=list(S)+list(set(G)-SS)
        firstnonS=len(S)
        while firstnonS<len(G):
            t=orderednodes[firstnonS]
            if is_clique(G,link(G,t)&SS):
                firstnonS+=1
                continue
            orderedSlink=list(link(G,t)&SS)
            for firstL in range(len(orderedSlink)-1):
                for p in powerset([i for i in range(firstL+1,len(orderedSlink))],minsize=1):
                    Uind=[firstL,]+list(p)
                    U=set([orderedSlink[i] for i in Uind])
                    if is_clique(G,U):
                        continue
                    possibleadditionalT=[i for i in itertools.chain(range(len(S)),range(firstnonS,len(G))) if orderednodes[i] not in G[t] and U<=link(G,orderednodes[i])]
                    for A in anticliques(G.subgraph([orderednodes[i] for i in possibleadditionalT])):
                        yield set([t,])|set(A)
                firstL+=1
            firstnonS+=1
    while new:
        S=new.pop()
        for T in new|old: # check if there is some known compliant T such that U=S&T is not already known
            U=S&T
            if S<T or T<S or is_clique(G,U) or U in new|old:
                continue
            if len(U)==3 and nx.is_connected(G.subgraph(U)): # U is a 2--path.
                Upole=set(next(iter(anticliques(G.subgraph(U),minsize=2))))
                if V<=Upole:
                    Upole=frozenset(Upole)
                    if Upole not in new|old:
                        new.add(Upole)
                        if verbose:
                            print(str(set(Upole))+" is virtually the intersection of "+str(set(S))+" and "+str(set(T))+".")
                        continue
            new.add(U)
            if verbose:
                print(str(set(U))+" is the intersection of "+str(set(S))+" and "+str(set(T))+".")
            try: # if U is a suspension of at least 3 vertices, also add its pole
                Upole=get_suspension_pole(G,U)
                Upole=frozenset(Upole)
                if Upole not in new|old:
                    if V<=set(Upole):
                        new.add(Upole)
                        if verbose:
                            print(str(set(Upole))+" is the pole of "+str(set(U))+".")
            except RuntimeError:
                pass
        for T in potentialT(S): # check if some translate of Sigma_S with infinite projection to Sigma_S
            T=frozenset(T)
            U=S.intersection(*[frozenset(link(G,t)) for t in T])
            if U==S or is_clique(G,U) or U in new|old or not V<=U:
                continue
            if len(U)==3 and nx.is_connected(G.subgraph(U)): # U is a 2--path. Also add the 2--anticlique
                Upole=next(iter(anticliques(G.subgraph(U),minsize=2)))
                Upole=frozenset(Upole)
                if Upole not in old and V<=set(Upole):
                    new.add(Upole)
                    if verbose:
                        if len(T)==1:
                            print(str(set(Upole))+" is virtually the intersection of "+str(set(S))+" with link of "+str(set(T))+".")
                        else:
                            print(str(set(Upole))+" is virtually the intersection of "+str(set(S))+" with common link of "+str(set(T))+".")
                    continue
            new.add(U)
            if verbose:
                if len(T)==1:
                    print(str(set(U))+" is the intersection of "+str(set(S))+" with link of "+str(set(T))+".")
                else:
                    print(str(set(U))+" is the intersection of "+str(set(S))+" with common link of "+str(set(T))+".")
            try: # if U is a suspension of at least 3 vertices, also add its pole
                Upole=get_suspension_pole(G,U)
                Upole=frozenset(Upole)
                if Upole not in old and V<=set(Upole):
                    new.add(Upole)
                    if verbose:
                        print(str(set(Upole))+" is the pole of "+str(set(U))+".")
            except RuntimeError:
                pass
        old.add(S)
    return old

def get_suspension_pole(G,U):
    """
    If U is the set of vertices of a suspension subgraph of G that is a suspension of at least 3 vertices then return the pole. If not raise RuntimeError.
    """
    if len(U)<5:
        raise RuntimeError
    H=G.subgraph(U)
    pole=[v for v in H if len(H[v])>2]
    suspended=[v for v in H if len(H[v])==2]
    if len(pole)!=2 or len(suspended)<len(U)-2:
        raise RuntimeError
    a,b=pole
    if a in H[b]:
        raise RuntimeError
    if set(H[a])==suspended and set(H[b])==suspended:
        return {a,b}
    raise RuntimeError


          
                

def has_compliant_cycle(G):
    return compliant_cycle(G) is not None

def is_one_or_two_flat(G,S):
    if len(S)<2 or len(S)>4:
        return False
    H=G.subgraph(S)
    if len(S)==2 and len(H.edges())==0:
        return True
    if len(S)==3 and len(H.edges())==2:
        return True
    if len(S)==4 and is_induced_square(G,S):
        return True
    return False



def compliant_cycle(G,verbose=False,try_subordinate_joins=1,enforce_extra_S_condition=True):
    """
    Find a compliant set S and an induced path A satisfying theorem 8.14. Specifically, need that A intersects S only at its endpoints and for every interior vertex a in A, link(a)\cap S is a clique. We also need that there does not exist S' that is in the same QI orbit as S, intersects S in incomplete set, and contains some vertex of A. When S is hyperbolic or square the S' condition is automatic.  
    
    Option try_subordinate_joins restricts choices of S to make it easier to check for S'. 
    try_subordinate_joins:
    0: Only consider S that are square-free, square, or maximal thick join subgraphs.
    1: Consider all compliant sets S covered by case 0 or case 2. 
    2: Only consider S that are thick joins not covered in case 0.
    Option 0 is faster than 1. Option 2 is for if 0 already failed, so we don't repeat work by trying 1. 

    If enforce_extra_S_condition=False do not check for S' at all. This is for experimentation, output may not satisfy the conditions of the theorem. 
    """
    compliant_all=compliant_subsets(G)
    compliant_hyperbolic=set()
    compliant_square=set()
    compliant_max_join_suspension=set()
    compliant_max_join_non_suspension=set()
    compliant_non_max_join_suspension=set()
    compliant_non_max_join_non_suspension=set()
    compliant_other=set()
    RIC=MPRG_fundamental_domain(G)
    neighbor_types=MPRG_neighbor_types(G,RIC)
    for S in compliant_all: # sort the compliant sets
        if not has_induced_square(G,S):
            compliant_hyperbolic.add(S)
        elif is_square(G,S):
            compliant_square.add(S)
        else:
            J=get_join(G.subgraph(S),assume_triangle_free=True)
            if J is None:
                compliant_other.add(S)
            A,B=J
            if len(A)>len(B):
                A,B=B,A
            A=frozenset(A)
            B=frozenset(B)
            J=frozenset({A,B})
            ismax=(set(A)==set.intersection(*[link(G,b) for b in B])) and (set(B)==set.intersection(*[link(G,a) for a in A]))
            if len(A)==2:
                if ismax:
                    compliant_max_join_suspension.add(J)
                else:
                    compliant_non_max_join_suspension.add(J)
            else:
                if ismax:
                    compliant_max_join_non_suspension.add(J)
                else:
                    compliant_non_max_join_non_suspension.add(J)
    def get_path_avoiding_forbidden(S,forbidden):
        bridges=[T for T in compliant_all if is_clique(G,S&T)]
        for first,last in ((x,y) for x,y in itertools.combinations(S,2) if not is_clique(G,{x,y})):
            # case that first and last edges both bridges
            for A in [T for T in bridges if first in T]:
                for B in [T for T in bridges if last in T and T!=A]: # A!=B since otherwise we have only P is a 2-anticlique
                    for a in [a for a in A if a!=first and a not in forbidden]:
                        for b in [b for b in B if b!=last and b not in forbidden]:
                            auxgraph=(G.subgraph(set(G)-forbidden)).copy()
                            for T in [T for T in bridges if T!=A and T!=B]:
                                for c,d in itertools.combinations(set(T),2):
                                    if c in auxgraph and d in auxgraph:
                                        if (c,d) not in auxgraph.edges():
                                            auxgraph.add_edge(c,d,bridges=[T,])
                                        elif 'bridges' in auxgraph[c][d]:
                                            auxgraph[c][d]['bridges'].append(T)
                            try:
                                the_path=nx.shortest_path(auxgraph,a,b)
                                auxgraph.add_edge(first,a,bridges=[A,])
                                auxgraph.add_edge(b,last,bridges=[B,])
                                whole_path=[first,]+the_path+[last,] # whole_path contains at least two bridge edges
                                return whole_path,auxgraph
                            except nx.NetworkXNoPath:
                                continue
            # case that only first edge is a bridge
            for A in [T for T in bridges if first in T]:
                for a in [a for a in A if a!=first and a not in forbidden]:
                    auxgraph=(G.subgraph((set(G)-forbidden)|set([last,]))).copy()
                    for T in [T for T in bridges if T!=A]:
                        for c,d in itertools.combinations(set(T),2):
                            if c in auxgraph and d in auxgraph and c!=last and d!=last:
                                if (c,d) not in auxgraph.edges():
                                    auxgraph.add_edge(c,d,bridges=[T,])
                                elif 'bridges' in auxgraph[c][d]:
                                    auxgraph[c][d]['bridges'].append(T)
                    try:
                        the_path=nx.shortest_path(auxgraph,a,last) # by construction, the_path ends with a G edge
                        whole_path=[first,]+the_path # whole_path contains at least one bridge edge and at least on G edge
                        auxgraph.add_edge(first,a,bridges=[A,])
                        return whole_path,auxgraph
                    except nx.NetworkXNoPath:
                        continue
            # case that only last edge is a bridge
            for B in [T for T in bridges if last in T]:
                for b in [b for b in B if b!=last and b not in forbidden]:
                    auxgraph=(G.subgraph((set(G)-forbidden)|set([first,]))).copy()
                    for T in [T for T in bridges if T!=B]:
                        for c,d in itertools.combinations(set(T),2):
                            if c in auxgraph and d in auxgraph and c!=first and d!=first:
                                if (c,d) not in auxgraph.edges():
                                    auxgraph.add_edge(c,d,bridges=[T,])
                                elif 'bridges' in auxgraph[c][d]:
                                    auxgraph[c][d]['bridges'].append(T)
                    try:
                        the_path=nx.shortest_path(auxgraph,first,b)
                        whole_path=the_path+[last,]
                        auxgraph.add_edge(b,last,bridges=[B,])
                        return whole_path,auxgraph
                    except nx.NetworkXNoPath:
                        continue
            # case that first and last edges not bridges
            auxgraph=(G.subgraph((set(G)-forbidden)|{first,last})).copy()
            for T in bridges:
                for c,d in itertools.combinations(set(T),2):
                    if c in auxgraph and d in auxgraph and c!=first and d!=first and c!=last and d!=last:
                        if (c,d) not in auxgraph.edges():
                            auxgraph.add_edge(c,d,bridges=[T,])
                        elif 'bridges' in auxgraph[c][d]:
                            auxgraph[c][d]['bridges'].append(T)
            try:
                the_path=nx.shortest_path(auxgraph,first,last)
                assert(len(the_path)>3) # should not be possible for first and last to have common neighbor in auxgraph; such a vertex would have been forbidden for having link intersecting S_0 in a nonclique
                return the_path,auxgraph
            except nx.NetworkXNoPath:
                continue
        return None, None
    if try_subordinate_joins in {0,1}: # consider cases that S is square, hyperbolic, or max join
        for S in compliant_hyperbolic|compliant_square:
            forbidden=set(S)|{v for v in G if not is_clique(G,link(G,v)&S)}
            the_path,auxgraph=get_path_avoiding_forbidden(S,forbidden)
            if the_path is not None:
                return S,the_path,auxgraph
        for J in compliant_max_join_suspension|compliant_max_join_non_suspension:
            A,B=J
            if len(A)>len(B):
                A,B=B,A
            S=set(A)|set(B)
            Snbhd={v for v in G if (v not in S) and link(G,v)&S} 
            forbidden=set(S)|{v for v in G if not is_clique(G,link(G,v)&S)}
            if enforce_extra_S_condition:
                seed_generator=(K for K in RIC if K!=J)
                while True:
                    try:
                        K=next(seed_generator)
                    except StopIteration:
                        break
                    X,Y=K
                    if len(X)>len(Y):
                        X,Y=Y,X
                    Sprime=set(X)|set(Y)
                    if Sprime<=forbidden:
                        continue
                    if (len(A)==2 and len(X)==2) or (len(A)>2 and len(X)>2):
                        if neighbor_types[J]==neighbor_types[K] and not is_clique(G,S & Sprime):
                            forbidden|=Sprime
            the_path,auxgraph=get_path_avoiding_forbidden(S,forbidden)
            if the_path is not None:
                return S,the_path,auxgraph
    if try_subordinate_joins in {1,2}: # consider cases that S is a thick join but not maximal 
        for J in compliant_non_max_join_suspension|compliant_non_max_join_non_suspension:
            A,B=J
            if len(A)>len(B):
                A,B=B,A
            S=set(A)|set(B)
            Snbhd={v for v in G if (v not in S) and link(G,v)&S} 
            max_joins_containing_S={frozenset({X,Y}) for X,Y in RIC if S<=set(X)|set(Y)}
            S_is_suspension=bool(len(A)==2)
            forbidden=set(S)|{v for v in G if not is_clique(G,link(G,v)&S)}
            if enforce_extra_S_condition:
                # enumerate subgraphs that intersect S in a nonclique and could conceivably by in same QI orbit as S
                seed_generator=itertools.chain.from_iterable([itertools.combinations(A,2),itertools.combinations(B,2)])
                while True:
                    try:
                        nonclique_in_S_intersection=next(seed_generator)
                    except StopIteration:
                        break
                    x1,x2=nonclique_in_S_intersection
                    L=link(G,x1)&link(G,x2)
                    if not S_is_suspension:
                        possible_Y_factors=powerset(L,minsize=3)
                    else:
                        possible_Y_factors=powerset(L,minsize=2)
                    for Y in possible_Y_factors:
                        maximal_complementary_factor=set.intersection(*[link(G,y) for y in Y])
                        if not S_is_suspension:
                            possible_X_factors=powerset(maximal_complementary_factor-{x1,x2}, minsize=1)
                        else:
                            if len(Y)==2:
                                possible_X_factors=powerset(maximal_complementary_factor-{x1,x2}, minsize=1)
                            else:
                                possible_X_factors=[set(),]
                        for Xprime in possible_X_factors:
                            X=set(Xprime)|{x1,x2}
                            if len(X)>len(Y):
                                X,Y=Y,X
                            Sprime=set(X)|set(Y)
                            # Sprime is a thick join of the same type suspension/nonsuspension as S. Now further checks to exclude it if it cannot be in same QI orbit as S
                            biggerX=set.intersection(*[link(G,y) for y in Y])
                            biggerY=set.intersection(*[link(G,x) for x in X])
                            if X==biggerX and Y==biggerY: # this X*Y is a maximal join
                                continue
                            ###### consider if the set of maximal joins containing S is similar to the set of maximal joins containing Sprime
                            max_joins_containing_Sprime={frozenset({U,V}) for U,V in RIC if Sprime<=set(U)|set(V)}
                            if {neighbor_types[J] for J in max_joins_containing_S}=={neighbor_types[K] for K in max_joins_containing_Sprime}:
                                forbidden|=Sprime
            the_path,auxgraph=get_path_avoiding_forbidden(S,forbidden)
            if the_path is not None:
                return S,the_path,auxgraph
    #for S in compliant_other: # don't know what to do with these
    return None



         
        
        
            
        


#-------------------- Fioravanti-Karrer
def Fioravanti_Karrer_condition(G,assume_triangle_free=False,assume_one_ended=False,GOC=None,verbose=False):
    """
    Recursively find splittings of triangle-free graph G over either a clique or a subgraph of a thick join, until remaining pices are joins. Return value True means this process was sucessful and the RACG W_G has totally disconnected Morse boundary. Return value False means at some point no suitable splitting could be found. In this case the result is inconclusive about connectivity of the Morse boundary. 
    """
    if not assume_triangle_free and not is_triangle_free(G):
        raise InputError("Only implemented for triangle-free graphs.")
    if is_clique(G,G):# Morse boundary is empty
        if verbose:
            print("Graph "+str(G.nodes())+" is a clique.")
        return True
    if is_join(G):# defining graph is a join, so group is either finite, virtualy free, or thick join
        if has_cone_vertex(G):
            if verbose:
                print("Graph "+str(G.nodes())+" is cone on anticlique.")
        else:
            if verbose:
                print("Graph "+str(G.nodes())+" is thick join.")
        return True
    if not assume_one_ended:
        gsd=GSD(G,assume_triangle_free=True) # Grushko-Stallings-Dunwoody decomposition
        if len(gsd)>1: # exists spltting over finite subgroup, pass to vertex groups
            if verbose:
                print("Graph "+str(G.nodes())+" splits over a finite subgroup.")
                for v in gsd:
                    if Fioravanti_Karrer_condition(G.subgraph(v),assume_triangle_free=True,verbose=True) is False:
                        print("GSD factor "+str(v)+" of graph "+str(G.nodes())+" fails.")
                        return False
                return True
            else:
                return all(Fioravanti_Karrer_condition(G.subgraph(v),assume_triangle_free=True) for v in gsd) #pass to vertex groups, which are either finite or one-ended
    # one ended
    if is_surface_type(G):
        if verbose:
            print("Graph "+str(G.nodes())+" is surface type.")
        return False
    if GOC is None:
        pass
    else:
        goc=GOC
        if len(goc)>1 and all(len(v[2])>=2 for v in goc if v[0]=='C'):# pass to rigid vertices, since Morse boundaries of one-ended cylinders and hanging subgroups are empty/totally disconnected, respectively
            if verbose:
                print("Nontrivial JSJ decomposition with thick cylinders.")
                for rigid in (v for v in goc if v[0]=="R"):
                    print("Passing to rigid vertex "+str(rigid)+" of graph "+str(G.nodes())+".")
                    if Fioravanti_Karrer_condition(G.subgraph(rigid[1:]),assume_triangle_free=True,verbose=True) is False:
                        print("Rigid vertex "+str(rigid)+" of graph "+str(G.nodes())+" fails.")
                        return False
                return True
            else:
                return all(Fioravanti_Karrer_condition(G.subgraph(r[1:]),assume_triangle_free=True) for r in goc if r[0]=='R')
    if verbose:
        print("Looking for disconnecting sub-joins.")
    for A,B in maximal_joins(G,only_thick=True):
        for P in powerset(A|B):
            connected_components=[C for C in nx.connected_components(G.subgraph(set(G)-set(P)))]
            if len(connected_components)>1:
                if verbose:
                    print("Subset "+str(set(P))+" of thick join "+str(set(A))+"*"+str(set(B))+" separates the graph "+str(G.nodes())+".")
                    for component in connected_components:
                        if Fioravanti_Karrer_condition(G.subgraph(component|set(P)), assume_triangle_free=True,verbose=True) is False:
                            print("Component "+str(component)+" of graph "+str(G.nodes())+" fails.")
                            return False
                    return True
                else:
                    return all(Fioravanti_Karrer_condition(G.subgraph(C|set(P))) for C in connected_components)
    if verbose:
        print("Did not find any suitable decompositions of graph "+str(G.nodes())+".")
    return False
            
    

        

def GSD(G,assume_triangle_free=False):
    """
    Find the Grushko-Stallings-Dunwoody decomposition of a RACG defined by triangle-free graph G.
    Return type is nx.Graph() whose vertices are frozensets of vertices of G, such that subgraph induced by such a set is either spherical or not separated by a clique. Edge between two vertices when there is inclusion of their corresponding sets. 
    """
    if not assume_triangle_free and not is_triangle_free(G):
        raise InputError("Only implemented for triangle-free graphs.")
    gsd=nx.Graph()
    for v in zero_one_ended_components(G):
        gsd.add_node(frozenset(v))
    for v, w in itertools.permutations(gsd,2):
        if v<=w:
            gsd.add_edge(v,w)
    # it can happen that there are extraneous triangles coming from chaining inclusion of cut vertex into cut edge into rigid subgraph. In this case remove the vertex-rigid edge.
    for u, v, w in triangles(gsd):
        if u < v:
            if v<w:
                pass
            elif w<u:
                u,v,w=w,u,v
            else:
                u,v,w=u,w,v
        else:
            if w < v:
                u,v,w=w,v,u
            elif w<u:
                u,v,w=v,w,u
            else:
                u,v,w=v,u,w
        gsd.remove_edge(u,w)
    return gsd
        
def zero_one_ended_components(G):
    """
    Generator of subsets of vertices of G that are either a separating vertex or edge or cannot be disconnected by a vertex or edge. 
    """
    cliques_by_size=[set([]),]+[set([v,]) for v in G]+[{v,w} for v,w in G.edges()]
    for clique in cliques_by_size:
        complementary_components=[C for C in nx.connected_components(G.subgraph(set(G)-clique))]
        if len(complementary_components)>1:
            if clique:
                yield frozenset(clique)
            for C in complementary_components:
                for O in zero_one_ended_components(G.subgraph(C|clique)):
                    yield O
            break
    else:
        yield set(G)
        
                    
            
#--------------------   Camp-Mihalik
def has_locally_connected_boundary(G,assume_one_ended=False,assume_two_dimensional=False, verbose=False):
    """
    Check Camp-Mihalik conditions to see if W_G has locally connected visual boundary.

    >>> G=nx.Graph(); G.add_edges_from([(0,2),(0,3),(1,2),(1,3)]);
    >>> has_locally_connected_boundary(G)
    True
    >>> G.add_edges_from([(0,4),(1,4)]);
    >>> has_locally_connected_boundary(G)
    False
    >>> G=double(cycle_graph(5));
    >>> has_locally_connected_boundary(G)
    False
    >>> G.add_edges_from([((0,0),(5,0)),((0,1),(5,0)),((1,0),(5,0)),((4,1),(5,0)),((1,0),(6,0)),((1,1),(6,0)),((2,0),(6,0)),((0,1),(6,0)),((2,0),(7,0)),((2,1),(7,0)),((3,0),(7,0)),((1,1),(7,0)),((3,0),(8,0)),((3,1),(8,0)),((4,0),(8,0)),((2,1),(8,0)),((4,0),(9,0)),((4,1),(9,0)),((0,0),(9,0)),((3,1),(9,0))]);
    >>> has_locally_connected_boundary(G)
    True
    """
    if not assume_two_dimensional:
        for a,b,c,d in induced_squares(G):
            if not is_clique(G,link(G,a)&link(G,b)&link(G,c)&link(G,d)):
                raise InputError("Graph has an octahedron; Camp-Mihalik does not apply.")
    if not assume_one_ended and not is_one_ended(G):
        raise InputError("Graph does not give one-ended group; Camp-Mihalik does not apply.")
    # Step 1, check if G is suspension
    sus=get_suspension(G)
    if sus is not None:
        P,S=sus
        if is_infinite_ended(G.subgraph(S)):
            if verbose:
                print("Suspension "+str(P)+"*"+str(S))
            return False
        else:
            return True
    # Step 2, search for virtual factor separator
    vfs=find_virtual_factor_separator(G)
    if vfs is None:
        return True
    else:
        if verbose:
            print("Virtual factor separator "+str(vfs))
        return False

def find_virtual_factor_separator(G,assume_triangle_free=False,verbose=False):  
    H,nodes=integer_graph(G)
    if assume_triangle_free or is_triangle_free(H):
        graph_is_triangle_free=True
    else:
        graph_is_triangle_free=False
    for i in range(len(H)-1):
        for j in distance_two(H,i):
            if j<i:
                continue
        common_neighbors=link(H,i)&link(H,j)
        for D in powerset(common_neighbors,minsize=1):
            D=set(D)
            if graph_is_triangle_free:
                Cprime_generator=powerset(set.intersection(*[link(H,d) for d in D]),maxsize=1)
            else:
                Cprime_generator=powerset(set.intersection(*[link(H,d) for d in D]))
            for Cprime in Cprime_generator: # Cprime=C-D
                Cprime=set(Cprime)
                if not {i,j}<=Cprime and is_clique(H,Cprime):
                    C=Cprime|D
                    if not nx.is_connected(H.subgraph(set(H)-C)):
                        GC={nodes[k] for k in C}
                        GD={nodes[k] for k in D}
                        Gs=nodes[i]
                        Gt=nodes[j]
                        if verbose:
                            print("C="+str(GC)+", D="+str(GD)+", s="+str(Gs)+", t="+str(Gt))
                        return GC,GD,Gs,Gt
    return None
    



# --------- MPRG
def MPRG_fundamental_domain(G):
    """
    Given a triangle-free graph G, compute a fundamental domain in the maximal product region graph of the corresponding RACG.
    Vertices are maximal thick join subgraph of G, represented by frozenset of two frozensets of vertices. 
    Edge between two vertices if their intersection as subgraphs of G contains a square. 
    """
    F=nx.Graph()
    for J in maximal_joins(G,only_thick=True):
        F.add_node(J)
    for v,w in itertools.combinations(F,2):
        v1,v2=v
        w1,w2=w
        if ((not is_clique(G,v1&w1)) and (not is_clique(G,v2&w2))) or  ((not is_clique(G,v1&w2)) and (not is_clique(G,v2&w1))):
            F.add_edge(v,w)
    return F

def MPRG_neighbor_types(G,F):
    """
    Given a triangle-free graph G and its MPRG_fundamental_domain F, return a dict whose keys are vertices of F, and whose values are frozensets of tuples (neighbor,intersection), where neighbor in {'suspension','non-suspension'} and intersection in {'square','suspension','non-suspension'}, describing the types of neighbors of J in F and their intersection with J. 
    """
    result=dict()
    for J in F:
        result[J]=set()
        for K in F[J]:
            A,B=K
            if len(A)>len(B):
                A,B=B,A
            if len(A)==2:
                neighbortype='suspension'
            else:
                neighbortype='non-suspension'
            J1,J2=J
            X=set(J1)&set(A)
            if X:
                Y=set(J2)&set(B)
            else:
                X=set(J1)&set(B)
                Y=set(J2)&set(A)
            if len(X)>len(Y):
                X,Y=Y,X
            if len(Y)==2:
                intersectiontype='square'
            elif len(X)==2:
                intersectiontype='suspension'
            else:
                intersectiontype='non-suspension'
            result[J].add((neighbortype,intersectiontype))
    for J in result:
        result[J]=frozenset(result[J])
    return result

def MPRG_stab(F,v):
    """
    Given the fundamental domain F of the MPRG of a RACG as output by MPRG_fundamental_domain an a vertex v in F, return the set of vertices of the defining graph of the RACG  that make up the maximal thick join corresponding to v.
    """
    assert(v in F)
    A,B=v
    return set(A)|set(B)

def MPRG_support(F,Fset):
    return set.union(*[MPRG_stab(F,v) for v in Fset])

def MPRG_fixed(F,s):
    """
    Given F as output by MPRG_fundamental_domain and vertex s of the defining graph of the RACG, return the set of vertices in F that contain s.
    """
    return {J for J in F if s in MPRG_stab(F,J)}

def edges_not_in_any_thick_join(G,precomputed_MPRG_fundamtenal_domain=None):
    """
    Generators that yields edges of G that are not contained in any thick join subgraph.
    """
    if precomputed_MPRG_fundamtenal_domain is None:
        F=MPRG_fundamental_domain(G)
    else:
        F=precomputed_MPRG_fundamtenal_domain
    vertex_supports=[MPRG_support(F,[v,]) for v in F]
    for a,b in G.edges():
        if not any(a in S and b in S for S in vertex_supports):
            yield a,b
    

def get_MPRG_ladder(G,rs=None,ss=None,verbose=False,small_first=False, try_hard=False):
    """
    Search for triple r,s,Delta such that r and s are vertices of G and Delta is a subset of the fundamental domain of the MPRG of the RACG defined by G such that <r,s>.Delta is a thick ladder.

    If candidates for r are already known they can be given as an iterable rs. This will speed up search. 

    If tryhard=False then for candidate r and s we take corresponding sets R and S to be the entire fixed sets of r and s, and assume these should be contained in Delta. Otherwise, allow the possibility that only some subsets of the fixed sets occur in Delta. This requires iterating over the powersets of fix(r) and fix(s), and will be much slower. 
    """
    if is_join(G):
        return None
    F=MPRG_fundamental_domain(G)
    if not nx.is_connected(F):
        raise ValueError('MPRG fundamental domain is not connected.')
    if len(F)<5 or nx.is_tree(F):
        return None
    vertices_with_large_fixed_sets=[v for v in G if diameter_at_least_three(F,MPRG_fixed(F,v))]
    if not try_hard:
        vertices_with_large_fixed_set_not_star_separated=[v for v in vertices_with_large_fixed_sets if not badly_star_separated(F,MPRG_fixed(F,v))]
    if rs is None:
        assert(ss is None)
        if try_hard:
            orderedvertices=vertices_with_large_fixed_sets+[v for v in set(G)-set(vertices_with_large_fixed_sets)]
            possible_r_indices=[i for i in range(len(vertices_with_large_fixed_sets))]
            possible_s_indices=[i for i in range(len(vertices_with_large_fixed_sets))]
        else:
            orderedvertices=vertices_with_large_fixed_set_not_star_separated+[v for v in set(G)-set(vertices_with_large_fixed_set_not_star_separated)]
            possible_r_indices=[i for i in range(len(vertices_with_large_fixed_set_not_star_separated))]
            possible_s_indices=[i for i in range(len(vertices_with_large_fixed_set_not_star_separated))]
    else:
        if try_hard:
            allowed_r=list(set(vertices_with_large_fixed_sets)&set(rs))
            disallowed_r=list(set(vertices_with_large_fixed_sets)-set(rs))
            orderedvertices=allowed_r+disallowed_r+[v for v in set(G)-set(vertices_with_large_fixed_sets)]
            possible_r_indices=[i for i in range(len(allowed_r))]
            if ss is None:
                possible_s_indices=[i for i in range(len(vertices_with_large_fixed_sets))]
            else:
                possible_s_indices=[i for i in range(len(vertices_with_large_fixed_sets)) if vertices_with_large_fixed_sets[i] in ss]
        else:
            allowed_r=list(set(vertices_with_large_fixed_set_not_star_separated)&set(rs))
            disallowed_r=list(set(vertices_with_large_fixed_set_not_star_separated)-set(rs))
            orderedvertices=allowed_r+disallowed_r+[v for v in set(G)-set(vertices_with_large_fixed_set_not_star_separated)]
            possible_r_indices=[i for i in range(len(allowed_r))]
            if ss is None:
                possible_s_indices=[i for i in range(len(vertices_with_large_fixed_set_not_star_separated))]
            else:
                possible_s_indices=[i for i in range(len(vertices_with_large_fixed_set_not_star_separated)) if vertices_with_large_fixed_set_not_star_separated[i] in ss]
    for i in possible_r_indices:
        r=orderedvertices[i]
        Rfix=MPRG_fixed(F,r)
        for j in [j for j in possible_s_indices if j>i]:
            s=orderedvertices[j]
            if r in G[s]:
               continue
            Sfix=MPRG_fixed(F,s)
            if Sfix&Rfix: # if r and s are contained in a common join
                continue
            if verbose:
                print("Trying r="+str(r)+" and s="+str(s))
            if try_hard:
                Rs_to_try=powerset(Rfix,minsize=2,small_first=small_first)
            else:
                Rs_to_try=[Rfix,]
            for R in Rs_to_try:
                R=set(R)
                if try_hard and not diameter_at_least_three(F,R): # if try_hard=False already checked diameter for R=Rfix
                    continue
                if try_hard and badly_star_separated(F,R): # if try_hard=False already checked star separation for R=Rfix
                    continue
                if try_hard:
                    Ss_to_try=powerset(Sfix,minsize=2,small_first=small_first)
                else:
                    Ss_to_try=[Sfix,]
                for S in Ss_to_try:
                    S=set(S)
                    if try_hard and not diameter_at_least_three(F,S):
                        continue
                    if try_hard and not badly_star_separated(F,S):
                        continue
                    if verbose:
                        print("Trying fixed sets "+str(R)+" and "+str(S))
                    Delta=find_Delta_for_MPRG_ladder_subtractive(F,r,s,R,S,(Rfix-R)|(Sfix-S)|(set([])),verbose=(verbose==2))
                    if Delta is not None:
                        return r,s,Delta
    return None
    
def badly_star_separated(F,R,verbose=False):
    for v in F:
        possiblestars=[star(F,v),]
        for S in powerset(star(F,v)-set([v,]),minsize=1,small_first=False):
            S=set(S)
            if set.intersection(*[MPRG_support(F,[s,]) for s in S])-MPRG_support(F,[v,]):
                possiblestars.append(S)
        for S in possiblestars:
            components=nx.connected_components(F.subgraph(set(F)-S))
            Rcomponents=[set(C)&set(R) for C in components if set(C)&set(R)]
            assert(Rcomponents)# should have only used this function if diam(R)>=3
            if len(Rcomponents)==1:
                continue
            singletonRcomponents=[set(C) for C in Rcomponents if len(C)==1]
            if len(Rcomponents)-len(singletonRcomponents)>1:
                if verbose:
                    print("R set "+str(R)+" is separated into multiple nonsingleton components by subset "+str(S)+" of star of "+str(v)+".")
                return True
            if len(singletonRcomponents)>1 and diameter_at_least_three(F,set.union(*singletonRcomponents)):
                if verbose:
                    print("R set "+str(R)+" has widely separated singleton complementary components of subset "+str(S)+" of star of "+str(v)+".")
                return True
    return False
        
    
def all_in_one_component(thegraph,input_vertices):
    active_components=[C for C in nx.connected_components(thegraph) if set(C)&set(input_vertices)]
    return len(active_components)<=1

def diameter_at_least_three(thegraph,input_vertex_set):
    """
    Return True if input_vertex_set has diameter at least three in thegraph.
    Error if input_vertex_set is not contained in a single component of thegraph.

    >>> diameter_at_least_three(cycle_graph(5),{0,1,2,3,4})
    False
    >>> diameter_at_least_three(cycle_graph(6), {0,3})
    True
    """
    vertices=set(input_vertex_set)
    if not vertices:
        return False
    if not all_in_one_component(thegraph,vertices):
        raise ValueError('Input vertices not in common connected component.')
    for v in vertices:
        if vertices<=two_ball(thegraph,v):
            continue
        else:
            return True
    return False

    
def find_Delta_for_MPRG_ladder_subtractive(F,r,s,R,S,excluded,currentDelta=None,verbose=False):
    """
    Find a connected subgraph Delta of fundamental domain F of an MPRG such that the support of r in Delta is R, the support of s in Delta is S, such that Delta does not contain any vertices given by excluded, such that Delta minus the star of any vertex has exactly one non-singleton component, and such that the complement of the big component has diameter at most 2.

    Start with F-excluded. If all vertices of R and S are contained in one component, pass to that component, else fail. Then iterate through vertices v in F and remove its star. If there is only one nonsingleton component containing vertices of R and S then throw away any other nonsingleton components, else fail. If there are singleton components that are not in R or S and make the diameter of the complement of the big component at least 3 then throw them away too. 
    """
    if currentDelta is None:
        Delta=F.subgraph(set(F)-excluded) # largest subgraph whose intersection with Rfix is R and intersection with Sfix is S
    else:
        Delta=currentDelta
    components=[C for C in nx.connected_components(Delta)]
    if len(components)>1:
        activeindex=[i for i in range(len(components)) if (R|S)&components[i]]
        if len(activeindex)!=1:
            if verbose:
                print("R and S do not lie in a connected subset of F-excluded.")
            return None
        else:
            Delta=Delta.subgraph(components[activeindex[0]])
    modified=True
    while modified:
        modified=False
        possiblevertexstars=[]
        for v in F:
            possiblevertexstars.append((v,star(F,v)))
            for partialstar in powerset(star(F,v)-set([v,]),minsize=1,small_first=False):
                partialstar=set(partialstar)
                if set.intersection(*[MPRG_support(F,[x,]) for x in partialstar])-MPRG_support(F,[v,]):
                    possiblevertexstars.append((v,partialstar))
        for v,partialstar in possiblevertexstars:
            if verbose:
                print("Delta has size "+str(len(Delta))+". Checking intersection with partial star of "+str(v))
            dead=[]
            live=[]
            deadsingle=[]
            livesingle=[]
            for C in nx.connected_components(Delta.subgraph(set(Delta)-partialstar)):
                if len(C)==1:
                    if C&(R|S):
                        livesingle.append(C)
                    else:
                        deadsingle.append(C)
                elif C&(R|S):
                    live.append(C)
                else:
                    dead.append(C)
            if len(live)!=1:
                if verbose:
                    print("More than one live complementary component of star.")
                return None
            bigcomponent=live[0]
            if not ((bigcomponent&S) and (bigcomponent&R)):
                if verbose:
                    print("Big component misses one of the fixed sets.")
                return None
            if dead:
                Delta=Delta.subgraph(set(Delta)-set.union(*dead))
                modified=True
                components=[C for C in nx.connected_components(Delta)]
                if len(components)>1:
                    activeindex=[i for i in range(len(components)) if (R|S)&components[i]]
                    if len(activeindex)!=1:
                        if verbose:
                            print("Dead component disconnects.")
                        return None
                    else:
                        Delta=Delta.subgraph(components[activeindex[0]])
            deadleaves=[v for v in Delta if len(Delta[v])==1 and v not in R|S]
            while deadleaves:
                Delta=Delta.subgraph(set(Delta)-set(deadleaves))
                modified=True
                deadleaves=[v for v in Delta if len(Delta[v])==1 and v not in R|S]
            if diameter_at_least_three(Delta,set(Delta)-bigcomponent):
                if deadsingle:
                    optionalvertices=[next(iter(C)) for C in deadsingle]
                    for P in powerset(optionalvertices,minsize=1,small_first=False): # don't know which of these its ok to throw away
                        newDelta=Delta.subgraph(set(Delta)-set(P))
                        if diameter_at_least_three(Delta,set(newDelta)-bigcomponent):
                            continue
                        else:
                            recursionresult=find_Delta_for_MPRG_ladder_subtractive(F,r,s,R,S,excluded|set(P),currentDelta=newDelta)
                            if recursionresult is not None:
                                return recursionresult
                if verbose:
                    print("Complement of the big component has diameter greater than 2.")
                return None
    return Delta

def check_Delta_for_MPRG_ladder(F,r,s,R,S,excluded,Delta):
    components=[C for C in nx.connected_components(Delta)]
    if len(components)>1:
        activeindex=[i for i in range(len(components)) if (R|S)&components[i]]
        if len(activeindex)!=1:
            print("R and S do not lie in a connected subset of F-excluded.")
            return
    while True:
        possiblevertexstars=[]
        for v in F:
            possiblevertexstars.append((v,star(F,v)))
            for partialstar in powerset(star(F,v)-set([v,]),minsize=1,small_first=False):
                partialstar=set(partialstar)
                if set.intersection(*[MPRG_support(F,[x,]) for x in partialstar])-MPRG_support(F,[v,]):
                    possiblevertexstars.append((v,partialstar))
        for v,partialstar in possiblevertexstars:
            print("Checking intersection with subset "+str(partialstar)+" of star of "+str(v)+".")
            dead=[]
            live=[]
            deadsingle=[]
            livesingle=[]
            for C in nx.connected_components(Delta.subgraph(set(Delta)-partialstar)):
                if len(C)==1:
                    if C&(R|S):
                        livesingle.append(C)
                    else:
                        deadsingle.append(C)
                elif C&(R|S):
                    live.append(C)
                else:
                    dead.append(C)
            if len(live)!=1:
                print("More than one live complementary component of star.")
                return 
            bigcomponent=live[0]
            if not ((bigcomponent&S) and (bigcomponent&R)):
                print("Big component misses one of the fixed sets.")
                return 
            if dead:
                components=[C for C in nx.connected_components(Delta.subgraph(set(Delta)-set.union(*dead)))]
                if len(components)>1:
                    print("Dead component disconnects.")
                    return None
            deadleaves=[v for v in Delta if len(Delta[v])==1 and v not in R|S]
            if diameter_at_least_three(Delta,set(Delta)-bigcomponent):
                print("Complement of the big component has diameter greater than 2.")
                return
    print("Looks good.")


                                
# ----------more CFS stuff

def get_iterated_construction(G,max_cone_size=float('inf'),only_cones=True,prefer_large_cones=False,additional_condition=None):
    """
    Return a rooted directed tree T whose source vertex is the graph G and such that at each vertex H there are the following possibilities:
    H is a square graph and T has no outgoing edges at H.
    There is a subgraph H' = H - {v}, and T has a single outgoing edge at H going to H'.
    H splits as an amalgam of subgraphs A and B, and T has 2 outgoing edges at H, going to A and B.

    If only_cones=True only check for splittings as cone of a subgraph, not as amalgam.
    If max_cone_size is given then only search for cones over subgraph of at most the given size. 
    If prefer_large_cones=True search will first check highest valence vertices for cone splitting. 

    If additional_condition is not None it should be a boolean function on graphs. Require that all H, A, B in T evaluate to True.
    Return an empty tree if G is not square and admits no decomposition. 
    """
    # search prefers coning, so if it is possible to build G via a sequence of cones-offs without using any amalgams then the resulting T will be a line where each edge is a cone off.
    # CFS graphs can always be built only by coning. The amalgam parts of this algorithm should never be needed.
    T=nx.DiGraph()
    if is_induced_square(G,G):
        T.add_node(G)
        return T
    for v in sorted([v for v in G], key=lambda v: len(G[v]),reverse=prefer_large_cones): # check if G-{v} is CFS. If so, induct.
        if len(G[v])>max_cone_size:
            continue
        H=G.subgraph([w for w in G if w!=v])
        if additional_condition is not None:
            if not additional_condition(H):
                continue
        subtree=get_iterated_construction(H,max_cone_size,additional_condition=additional_condition)
        if subtree:
            T.add_edges_from(subtree.edges())
            T.add_edge(G,H)
            return T
    if not only_cones: # at this point the graph is not a square and there is no vertex v for which G-{v} is CFS. Look for splitting of the graph as an amalgam of CFS subgraphs. 
        for A,B in distillations(G,non_cone=True):
            sgA=G.subgraph(A)
            sgB=G.subgraph(B)
            # G is an amalgam of CFS graphs sgA and sgB over their intersection. Induct on each. 
            subtreeA=get_iterated_construction(sgA,max_cone_size)
            subtreeB=get_iterated_construction(sgB,max_cone_size)
            if subtreeA and subtreeB:
                T.add_edges_from(subtreeA.edges())
                T.add_edges_from(subtreeB.edges())
                T.add_edge(G,sgA)
                T.add_edge(G,sgB)
                return T
    return T

def get_cone_sequence(G,prefer_large_cones=True,additional_condition=None):
    """
    Given a CFS graph G, return a set of four vertices forming an initial square and a sequence of vertices added as cone-offs to build G.
    """
    T=get_iterated_construction(G,prefer_large_cones=prefer_large_cones,additional_condition=additional_condition)
    if len(T)==0:
        return None
    assert(len(T)==len(G)-3)
    cone_sequence=[]
    H=next(iter({K for K in T if len(K)==len(G)}))
    while len(H)>4:
        nextH=next(T.successors(H))
        cone_sequence.append((set(H)-set(nextH)).pop())
        H=nextH
    cone_sequence.reverse()
    return set(H),cone_sequence


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
    """
    Graph with one vertex for each diagonal pair of vertices that are the diagonal of an induced square of G, and an edge between pairs when they are the vertices of an induced square.
    Vertices are given as a frozenset({a,b}).
    """
    DG=nx.Graph()
    if len(G)<4:
        return DG
    for S in induced_squares(G):
        DG.add_edge(frozenset({S[0],S[2]}),frozenset({S[1],S[3]}))
    return DG

def diagonals(G):
    """
    Return the set of pairs frozenset({a,b}) of vertices of G such that {a,b} is a diagonal in some induced square.
    """
    DG=diagonal_graph(G)
    return {v for v in DG}
        
def support(C):
    """
    C is a collection of collections of vertices of a graph. Return the set of vertices of G that occur in C.
    """
    return set().union(*[set(x) for x in C])


def graph_from_diagonals(D):
    # reconstruct the smallest graph that has D as its diagonal graph. 
    G=nx.Graph()
    for A,B in D.edges():
        a=tuple(A)
        b=tuple(B)
        for i,j in itertools.combinations_with_replacement({0,1},2):
            G.add_edge(a[i],b[j])
    return G



#-------------- unfolding


def find_places_to_unfold(G):
    """
    Given a triangle-free graph G, yield (A,B,C,D,E,F) such that E*F is a maximal thick join that separates G, D is a union of its complementary components, and A, B, C is a partition of E such that vertices of A only have neighbors in D and F, vertices of B have no neighbors in D, and a singleton set of vertices C with neighbors in both D and D complement. 
    """
    for E,F in get_separating_maximal_thick_joins(G):
        therest=G.subgraph(set(G)-E-F)
        thefactors=[E,F]
        comps=[thecomps for thecomps in nx.connected_components(therest)]
        for union_of_components in powerset(comps,minsize=1,maxsize=len(comps)-1):
            D=set.union(*[comp for comp in union_of_components])
            for i in range(2):
                factor=thefactors[i]
                Aplus={v for v in factor if set(D)&set(G[v])}
                Bplus={v for v in factor if (set(therest)-set(D))&set(G[v])}
                C=Aplus&Bplus
                A=Aplus-C
                B=factor-A-C
                if len(C)==1 and A and B:
                    yield(frozenset(A),frozenset(B),frozenset(C),frozenset(D),frozenset(thefactors[i]),frozenset(thefactors[(i+1)%2]))

def has_unfoldings(G):
    """
    Given a triangle-free graph G, determine if it has any possible unfoldings according to Theorem....
    """
    pu=find_places_to_unfold(G)
    try:
        next(pu)
    except StopIteration:
        return False
    return True
                
def unfold_once(G,A,B,C,D,E,F):
    """
    Given a triangle-free graph G and the output of find_places_to_unfold, perform the unfolding, changing G into a graph G' with one additional vertex, with W(G) and W(G') quasiisometric.
    """
    U=G.copy()
    newvertex=0
    while newvertex in U:
        newvertex+=1
    U.add_node(newvertex)
    for f in F:
        U.add_edge(newvertex,f)
    assert(len(C)==1)
    c=next(iter(C))
    for d in D:
        if c in U[d]:
            U.remove_edge(c,d)
            U.add_edge(newvertex,d)
    return U

def maximal_unfolding(G):
    """
    Find places to unfold and then unfold, iteratively, until no more place to unfold are found.
    """
    # Don't know anything about what happens if different unfolding sequences are chosen.
    current_graph=G.copy()
    while True:
        places=find_places_to_unfold(current_graph)
        try:
            place=next(places)
            current_graph=unfold_once(current_graph,*place)
        except StopIteration:
            break
    return current_graph
            
def all_unfoldings(G):
    for p in find_places_to_unfold(G):
        H=unfold_once(G,*p)
        yield H
        for K in all_unfoldings(H):
            yield K




            

#-------------- general graph structure
def integer_graph(G):
    """
    Return a graph H isomorphic to G whose vertices are integers 0...len(G) and a list whose i entry is the vertex of G corresponding to vertex i of H. 
    """
    H=nx.Graph()
    nodes=[v for v in G]
    node_dict=dict()
    for v in G:
        node_dict[v]=nodes.index(v)
    for a,b in G.edges():
        H.add_edge(node_dict[a],node_dict[b])
    return H,nodes

def bipartition(G):
    """
    Given a graph G, return a partition of its vertices into two sets such that neither set contains a pair of adjacent vertices. 
    Error if graph is not bipartite or is not connected.
    """
    return bipartite.sets(G)
    spheres=dict()
    spheres[-1]=set([])
    spheres[0]={next(iter(C)) for C in nx.connected_components(G)} # set containing one vertex from each connected component of G
    radius=0
    while sum(len(spheres[r]) for r in spheres)<len(G):
        next_sphere=(set().union(*[set(G[v]) for v in spheres[radius]]))-(spheres[radius]|spheres[radius-1])
        if G.subgraph(next_sphere).edges():
            raise ValueError("Input graph is not bipartite")
        radius+=1
        spheres[radius]=next_sphere
    return set().union(*[spheres[r] for r in spheres if not r%2]),set().union(*[spheres[r] for r in spheres if  r%2])

def is_bipartite(G):
    return bipartite.is_bipartite(G)
    


def two_ended_special_subgroups(G,V=None):
    """
    Generator that yields vertices of G that generate a two-ended subgroup of the RACG.
    Output will be tuples (a,b) with a<b and a not adjacent to b and tuples (a,c,b) with a<b, a not adjacent to b, and c adjacent to both a and b.

    If V, a subset of vertices of G, is given, then only yield subsets of V.

    >>> G=nx.Graph(); G.add_edges_from([(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),(2,6),(6,3),(2,7),(7,4),(2,8),(8,5)]); T={S for S in two_ended_special_subgroups(G)}; T=={(0, 1),(0, 2, 1), (0, 2, 6), (0, 2, 7), (0, 2, 8), (0, 3, 1), (0, 3, 6), (0, 4, 1), (0, 4, 7), (0, 5, 1), (0, 5, 8), (0, 6), (0, 7), (0, 8), (1, 2, 6), (1, 2, 7), (1, 2, 8), (1, 3, 6), (1, 4, 7), (1, 5, 8), (1, 6), (1, 7), (1, 8), (2, 0, 3), (2, 0, 4), (2, 0, 5), (2, 1, 3), (2, 1, 4), (2, 1, 5), (2, 3), (2, 4),(2, 5), (2, 6, 3),(2, 7, 4),(2, 8, 5),(3, 0, 4),(3, 0, 5),(3, 1, 4),(3, 1, 5), (3, 4), (3, 5), (3, 7), (3, 8),(4, 0, 5),(4, 1, 5), (4, 5),(4, 6),(4, 8),(5, 6),(5, 7), (6, 2, 7),(6, 2, 8),(6, 7), (6, 8), (7, 2, 8),(7, 8)}
    True
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
    Generator that returns triangles of G. Triangles yielded as ordered triples of vertices.
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
    """
    Decide if graph G is triangle-free.
    
    If V a subset of vertices is given, decide if there are any triangles with all vertices in V.

    >>> G=double(nx.path_graph(3+1)); is_triangle_free(G)
    True
    >>> G.add_edge((0,0),(2,0)); is_triangle_free(G)
    False
    >>> is_triangle_free(G,{(0,0),(0,1),(1,0),(1,1),(2,1),(3,0),(3,1)})
    True
    >>> is_triangle_free(G,{(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)})
    False
    """
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
    Generator that returns induced squares of G in the form (a,b,c,d) such that (a,c) and (b,d) are diagonals and (a,b,c,d).
    If V, a subset of vertices of G, is given then only yield squares whose vertices all belong to V. 
    """
    orderednodes=list(G)
    auxG=nx.Graph() # copy of G where the nodes have been replaced by integers
    for a,b in G.edges():
        auxG.add_edge(orderednodes.index(a),orderednodes.index(b))
    if V is None:
        theverts=set(auxG.nodes())
    else:
        theverts={orderednodes.index(v) for v in V}
    for a in theverts:
        A=orderednodes[a]
        for b,d in itertools.combinations([v for v in set(auxG[a])&theverts if v>a],2):
            if b in auxG[d]:
                continue
            B=orderednodes[b]
            D=orderednodes[d]
            for c in (c for c in theverts&set(auxG[b])&set(auxG[d]) if a<c and a not in auxG[c]):
                C=orderednodes[c]
                if b<d:
                    yield (A,B,C,D)
                else:
                    yield (A,D,C,B)

def has_induced_square(G,V=None):
    thesquares=induced_squares(G,V)
    try:
        next(thesquares)
        return True
    except StopIteration:
        return False

def all_squares(G,V=None):
    """
    Generator that returns squares of G in the form (a,b,c,d) such that (a,c) and (b,d) are diagonals.
    Allows the possibility that the diagonal of a square is an edge in G.
    If V, a subset of vertices of G, is given then only yield squares whose vertices all belong to V. 
    """
    orderednodes=list(G)
    auxG=nx.Graph() # copy of G where the nodes have been replaced by integers
    for a,b in G.edges():
        auxG.add_edge(orderednodes.index(a),orderednodes.index(b))
    if V is None:
        theverts=set(auxG.nodes())
    else:
        theverts={orderednodes.index(v) for v in V}
    for a in theverts:
        A=orderednodes[a]
        for b,d in itertools.combinations([v for v in set(auxG[a])&theverts if v>a],2):
            B=orderednodes[b]
            D=orderednodes[d]
            for c in (c for c in theverts&set(auxG[b])&set(auxG[d]) if a<c):
                C=orderednodes[c]
                if b<d:
                    yield (A,B,C,D)
                else:
                    yield (A,D,C,B)


def is_induced_subgraph(G,H):
    """
    Decide if graph H whose vertex set is a subset of the vertex set of G is an induced subgraph of G.
    >>> G=nx.Graph(); G.add_edges_from([(0,1),(1,2),(2,0),(2,3),(3,0)]); H=nx.Graph(); H.add_edges_from([(0,1),(1,2),(2,3),(3,0)]);
    >>> is_induced_subgraph(G,H)
    False
    >>> G=nx.Graph(); G.add_edges_from([(0,1),(1,2),(2,4),(4,0),(2,3),(3,0)]); H=nx.Graph(); H.add_edges_from([(0,1),(1,2),(2,3),(3,0)]);
    >>> is_induced_subgraph(G,H)
    True
    """
    for v,w in itertools.combinations(H,2):
        if w in G[v] and w not in H[v]:
            return False
    return True

def has_no_two_chord(G,H):
    """
    Decide if graph H whose vertex set is a subset of the vertex set of G has a 2--chord in G.
    """
    for v,w in itertools.combinations(H,2):
        if v not in H[w]:
            if set(G[v])&set(G[w]) and not set(H[v])&set(H[w]):
                return False
    return True
            


def geodesic_simple_cycles(G):
    """
    Generator that yields isometrically embedded cycles in nx.Graph G.
    """
    # Current implementation iterates through all simple cycles and checks if they are isometrically embedded.
    for cycle in nx.simple_cycles(G):
        if all(nx.shortest_path_length(G,cycle[i],cycle[(i+j)%len(cycle)])==j for i,j in itertools.product(range(len(cycle)),range(1,1+len(cycle)//2))):
            yield cycle
            
def get_suspension(G):
    if len(G)<2:
        return None
    H,nodes=integer_graph(G)
    for i in range(len(H)-1):
        for j in distance_two(H,i):
            if j<i:
                continue
            common_neighbors=link(H,i)&link(H,j)
            if len(common_neighbors)==len(H)-2:
                return {nodes[i],nodes[j]},common_neighbors
    return None

def is_suspension(G):
    S=get_suspension(G)
    return not (S is None)

def is_join(G):
    """
    Decide if G is a join of two nonempty subsets. 
    >>> is_join(cycle_graph(4))
    True
    >>> is_join(cycle_graph(5))
    False
    """
    return get_join(G) is not None

def get_join(G,assume_triangle_free=False):
    """
    Return nonempty sets A and B of vertices of graph G such that G=A*B, or None.
    Returned sets satisfy len(A)<=len(B).
    """
    v=next(iter(G)) # pick some vertex v. If G=A*B with v in A then B is contained in link(v).
    if assume_triangle_free or is_triangle_free(G):
        possibleB=[link(G,v),]
    else:
        possibleB=powerset(link(G,v),minsize=1,small_first=False)
    for B in possibleB:
        B=set(B)
        if not B:
            continue
        A=(set.intersection(*[link(G,b) for b in B]))-B
        if not A:
            continue
        if len(A)+len(B)==len(G):
            if len(B)<len(A):
                A,B=B,A
            return A,B
    return None



def maximal_joins(G,required_vertices={},only_thick=False):
    """
    Generate maximal join subgraphs of G containing all required_vertices.
    Yields frozenset of two frozensets A, B with such that A*B is a maximal join subgraph of G.
    If only_thick=True only yield maximal joins A,B for which A and B are not cliques.
    """ 
    Gemini=twin_module_graph(G)
    V1=[] # twin modules containing a required vertex
    V2=[] # twin modules not contining a required vertex
    for v in Gemini:
        if set(v)&set(required_vertices):
            V1.append(v)
        else:
            V2.append(v)
    V=V1+V2
    if V1 and V2:
        possible_first_index=range(len(V1))
    else:
        possible_first_index=range(len(V)-1)
    for i in possible_first_index:
        upperlink=[j for j in range(i+1,len(V)) if V[j] in Gemini[V[i]]]
        for S in (sorted(list(P)) for P in powerset(upperlink,minsize=1)):
            T=[t for t in range(len(V)) if t not in S and all(V[t] in Gemini[V[s]] for s in S)] # T contains i, so is nonempty
            if min(T)<i:
                continue
            U=[u for u in range(len(V)) if u not in T and all(V[u] in Gemini[V[t]] for t in T)]
            if U!=S:
                continue
            if not set(range(len(V1)))<=set(S)|set(T):
                continue
            GS=frozenset.union(*[V[s] for s in S])
            GT=frozenset.union(*[V[t] for t in T])
            if only_thick and (is_clique(G,GS) or is_clique(G,GT)):
                continue
            yield frozenset({GS,GT})
          

def is_cone_vertex(G,v):
    """
    Decide if v is adjacent to every other vertex of G.
    """
    return len(G[v])==len(G)-1

def has_cone_vertex(G):
    """
    Decide if G contains a cone vertex.
    """
    return any(is_cone_vertex(G,v) for v in G)

def is_clique(G,C):
    """
    Return True if C forms a clique in G, including if C is empty or singleton.

    >>> G=suspension(3); is_clique(G,{})
    True
    >>> is_clique(G,{0})
    True
    >>> is_clique(G,{0,1})
    False
    >>> is_clique(G,{0,2})
    True
    >>>
    """
    return 2*len(G.subgraph(C).edges())==len(C)*(len(C)-1)

def cliques(G,minsize=0):
    """
    Generator that yields all cliques of G.
    Output as ordered tuple of vertices.
    """
    if minsize==0:
        yield ()
    for C in nx.enumerate_all_cliques(G):
        if len(C)>=minsize:
            yield(tuple(sorted(C)))

def anticliques(G,minsize=0):
    """
    Generator that yields all anticliques of G.
    Output as ordered tuple of vertices.
    """
    for C in cliques(nx.complement(G),minsize=minsize):
        yield C

def is_induced_square(G,S):
    """
    Decide if S is the vertex set of an induced square of G.

    >>> G=cycle_graph(4); is_induced_square(G,{0,1,2,3})
    True
    >>> G.add_edge(0,2); is_induced_square(G,{0,1,2,3})
    False
    >>> G=suspension(3); is_induced_square(G,{0,1,2,3})
    True
    >>> is_induced_square(G,{1,2,3,4})
    False
    """
    if len(set(S))!=4:
        return False
    inducedsubgraph=G.subgraph(S)
    return len(inducedsubgraph.edges())==4 and all(inducedsubgraph.degree(v)==2 for v in S)

def is_square(G,S):
    """
    Decide if S is the set of vertices of a square, not necessarily induced.

    >>> G=cycle_graph(4); is_square(G,{0,1,2,3})
    True
    >>> G.add_edge(0,2); is_square(G,{0,1,2,3})
    True
    >>> G=suspension(3); is_square(G,{0,1,2,3})
    True
    >>> is_square(G,{1,2,3,4})
    False
    """
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

    

def are_diagonal(G,v,w):
    """
    Determine if v and w are a diagonal pair in an induced square of G.
   
    >>> are_diagonal(cycle_graph(4),0,1)
    False
    >>> are_diagonal(cycle_graph(4),0,2)
    True
    >>> G=cycle_graph(4); G.add_edge(0,2); are_diagonal(G,0,2)
    False
    """
    if v in G[w]:
        return False
    common_neighbors=set(G[v])&set(G[w])
    if is_clique(G,common_neighbors):
        return False
    return True



def is_triangle(G,S):
    """
    Decide is S is the set of vertices of a triangle in G.
    """
    if len(S)!=3:
        return False
    inducedsubgraph=G.subgraph(S)
    return len(inducedsubgraph.edges())==3


def convex_hull(G,S):
    """
    Recursively compute the convex hull of the set S of vertices of nx.Graph G.

    >>> G=suspension(4); G.add_edge(4,6); G.add_edge(6,5); G.add_edge(6,7);
    >>> convex_hull(G,{2,3})=={0,1,2,3,4,5,6}
    True
    """
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


def twins(G,v):
    """
    Return the set of vertices that have the same link as v, including v.

    >>> G=double(nx.path_graph(4)); twins(G,(1,0))=={(1, 0), (1, 1)}
    True
    >>> G.add_node('a');G.add_node('b'); twins(G,'a')=={'a','b'}
    True
    """
    L=link(G,v)
    if L:
        return set([v])|{w for w in distance_two(G,v) if link(G,w)==L}
    else:
        return {w for w in G if link(G,w)==L}

def twin_module(G,L):
    """
    Return the set of vertices of G whose link is equal to set L.

    >>> G=double(nx.path_graph(4)); twin_module(G,{(0,0),(0,1),(2,0),(2,1)})
    {(1, 0), (1, 1)}
    """
    return {v for v in G if link(G,v)==set(L)}

def twin_module_link(G,M):
    """
    Given a twin module M of G, return the set of twin modules of G that are adjacent to M in the twin graph, which is the same as twin modules containing vertices adjacent to some/every element of M.
    """
    v=next(iter(M))
    return {frozenset(twins(G,w)) for w in G[v]}
    
def twin_module_graph(G):
    """
    Return the nx.Graph with one vertex for each twin module of G and an edge between vertices if and only if G contains the join of the two modules, which is true if any vertex of one modules is adjacent to any vertex of the other.
    Vertices of the returned graph are frozensets of vertices of the input graph. 
    Vertices have attribute 'weight' equal to the number of vertices of G in that twin module.
    """
    Gemini=nx.Graph()
    for (v,w) in G.edges():
        Gemini.add_edge(frozenset(twins(G,v)),frozenset(twins(G,w)))
    for M in Gemini:
        Gemini.nodes[M]['weight']=len(M)
    return Gemini

def distance_two(G,v):
    """
    Return the set of vertices at distance 2 from v in graph G.
    """
    return (set().union(*[set(G[w]) for w in G[v]]))-star(G,v)

def two_ball(G,v):
    """
    Return the set of vertices in the closed ball of radius 2 about v in G.
    """
    return star(G,v).union(*[set(G[w]) for w in G[v]])

def get_separating_maximal_thick_joins(G):
    """
    Generator that yields pairs A,B of frozensets of vertices of G such that A and B have size at least 2 and A*B is a maximal join subgraph of graph G that separates G.
    """
    for A,B in maximal_joins(G,only_thick=True):
        if len(A)+len(B)+2<=len(G) and not nx.is_connected(G.subgraph(set(G)-A-B)):
            if len(A)>len(B):
                A,B=B,A
            yield A,B

def has_separating_maximal_join(G):
    """
    Decide if G contains subsets A and B of size at least 2 such that A*B is a maximal join subgraph that separates G.

    >>> G=double(cycle_graph(6)); has_separating_maximal_join(G)
    False
    >>> G=cycle_graph(6); G.add_edges_from([(0,6),(6,3)]); has_separating_maximal_join(double(G))
    True
    """
    try:
        next(get_separating_maximal_thick_joins(G))
    except StopIteration:
        return False
    return True

def get_separating_stars(G):
    """
    Generator that yields separating vertex stars of G.
    """
    for v in G:
        S=star(G,v)
        if len(S)<=len(G)+2 and not nx.is_connected(G.subgraph(set(G)-S)):
            yield S

def has_separating_star(G):
    """
    Decide if G has separating stars.

    >>> G=cycle_graph(6); has_separating_star(G)
    False
    >>> G.add_edges_from([(0,6),(6,3)]); has_separating_star(G)
    True
    """
    try:
        next(get_separating_stars(G))
    except StopIteration:
        return False
    return True
        



def vertex_equivalence_classes(G):
    """
    Return sets of vertices that are in same Aut(G) orbit.
    """
    action_graph=nx.Graph()
    for v in G:
        action_graph.add_node(v)
    for A in nx.algorithms.isomorphism.vf2pp_all_isomorphisms(G,G):
        for v in G:
            action_graph.add_edge(v,A[v])
    return [C for C in nx.connected_components(action_graph)]

def vertex_equivalence_classes_stabilizing_set(G,V):
    """
    Return sets of vertices that are in same orbit under automorphisms of G that fix set V pointwise.
    """
    action_graph=nx.Graph()
    for w in G:
        action_graph.add_node(w)
    for A in nx.algorithms.isomorphism.vf2pp_all_isomorphisms(G,G):
        if all(A[v]==v for v in V):
            for w in G:
                action_graph.add_edge(w,A[w])
    return [C for C in nx.connected_components(action_graph)]






#----------- near doubles and coarse near doubles

def is_near_double(G,precomputed_twin_module_graph=None):
    """
    Decide if triangle-free G is a graph that can be turned into a double by taking link double once or twice. 

    >>> B=nx.Graph();B.add_edge(0,1);B.add_edge(2,1);B.add_edge(2,3);B.add_edge(3,4);
    >>> D=double(B);is_near_double(D)
    True
    >>> D.remove_node((2,1)); is_near_double(D)
    True
    >>> D.remove_node((3,1));is_near_double(D)
    True
    >>> D.remove_node((1,1));is_near_double(D)
    False
    >>> D=double(B); D.remove_node((3,1)); D.remove_node((0,1));is_near_double(D)
    True
    >>> D=double(B); D.remove_edge((2,1),(3,1));is_near_double(D)
    True
    >>> D.remove_edge((2,1),(3,0));is_near_double(D)
    True
    >>> D.add_edge((2,1),(3,0)); D.remove_edge((2,1),(1,0));is_near_double(D)
    False
    >>> D=double(B); D.add_edge((1,1),(4,1)); is_near_double(D)
    True
    >>> D=double(B); D.add_edge((1,1),(4,1)); D.add_edge((0,0),(3,0)); is_near_double(D)
    False
    >>> D=double(B); D.remove_node((1,1)); D.add_edge((1,0),(3,1)); is_near_double(D)
    True
    >>> I=nx.identified_nodes(D,(1,1),(3,1)); is_near_double(I)
    True
    >>> B=nx.Graph();B.add_edge(0,1);B.add_edge(2,1);B.add_edge(2,3);B.add_edge(3,4);B.add_edge(4,5);B.add_edge(5,6);
    >>> D=double(B);D.remove_node((0,1));D.remove_node((6,1)); is_near_double(D)
    False
    >>> B=nx.Graph(); B.add_edge(0,1); B.add_edge(1,2); B.add_edge(0,3); B.add_edge(3,4);B.add_edge(0,5);B.add_edge(5,6);D=double(B);
    >>> D.remove_node((1,1)); D.remove_node((3,1)); is_near_double(D)
    False
    """
    if precomputed_twin_module_graph is None:
        Twins=twin_module_graph(G)
    else:
        Twins=precomputed_twin_module_graph
    Odds={S for S in Twins if len(S)%2!=0}
    if len(Odds)<=1:
        return True
    elif len(Odds)==2:
        A,B=Odds
        if A in Twins[B]:
            return True
        if link(Twins,A)<=link(Twins,B) or link(Twins,B)<=link(Twins,A):
            return True
    def link_subordinates(S):
        return {T for T in distance_two(Twins,S) if link(Twins,T)<=link(Twins,S)}
    for A,C in Twins.edges():
        B=link_subordinates(A)
        D=link_subordinates(C)
        if Odds<={A,C}|B|D:
            return True
    return False

def Einzelkinder(G,precomputed_twin_module_graph=None):
    if precomputed_twin_module_graph is None:
        Twins=twin_module_graph(G)
    else:
        Twins=precomputed_twin_module_graph
    unclonable_singletons=set()
    for S in Twins:
        if len(S)==1:
            v=next(iter(S))
            if not vertex_is_clonable(G,v):
                unclonable_singletons.add(S)
    return unclonable_singletons

def is_coarse_near_double(G,precomputed_twin_module_graph=None):
    """
    Same as near_double except only considers unclonable singleton twin modules instead of all odd twin modules. All other modules can be turned into even modules by vertex cloning.
    """
    if precomputed_twin_module_graph is None:
        Twins=twin_module_graph(G)
    else:
        Twins=precomputed_twin_module_graph
    unclonable_singletons=Einzelkinder(G,Twins)
    if len(unclonable_singletons)<=1:
        return True
    elif len(unclonable_singletons)==2:
        A,B=unclonable_singletons
        if A in Twins[B]:
            return True
        if link(Twins,A)<=link(Twins,B) or link(Twins,B)<=link(Twins,A):
            return True
    def link_subordinates(S):
        return {T for T in distance_two(Twins,S) if link(Twins,T)<=link(Twins,S)}
    for A,C in Twins.edges():
        B=link_subordinates(A)
        D=link_subordinates(C)
        if unclonable_singletons<={A,C}|B|D:
            return True
    return False

def satellites(G,v):
    """
    Return set of satellites of v.
    """
    return {w for w in distance_two(G,v) if link(G,w)<=link(G,v)}

def vertices_of_which_satellite(G,v):
    """
    Return the set of vertices of G of which v is a satellite.
    """
    return {w for w in distance_two(G,v) if link(G,v)<=link(G,w)}
                        
def vertex_is_clonable(G,v):
    """
    Given a vertex v in a triangle-free graph G, decide if v is clonable. 
    """
    return len(vertices_of_which_satellite(G,v))>=2

def clonable_vertices(G,twin_free=False):
    """
    Generate clonable vertices of G.
    If twin_free=True yield at most one vertex from each twin module.
    """
    if twin_free:
        Gemini=twin_module_graph(G)
        for M in Gemini:
            v=next(iter(M))
            if len(M)>=3:
                yield v
            elif vertex_is_clonable(G,v):
                yield v
    else:
        for v in G:
            if vertex_is_clonable(G,v):
                yield v

def clone_vertex(G,v):
    new_vertex=0
    while new_vertex in G:
        new_vertex+=1
    H=G.copy()
    for w in G[v]:
        H.add_edge(new_vertex,w)
    return H

def canonical_blowup(G):
    """
    Replace G with a graph such that every twin module has 1, 2, or 4 vertices, by cloning and uncloning without changing QI type of RACG. 
    """
    return blowup(reweighted_twin_module_graph(G))

def reweighted_twin_module_graph(G):
    Gemini=twin_module_graph(G)
    auxgraph=nx.Graph()
    for M in (v for v in Gemini if Gemini.nodes[v]['weight']==1):
        v=next(iter(M))
        if vertex_is_clonable(G,v):
            auxgraph.add_node(M,weight=2)
        else:
            auxgraph.add_node(M,weight=1)
    for M in (v for v in Gemini if Gemini.nodes[v]['weight']==2):
        auxgraph.add_node(M,weight=2)
    for M in (v for v in Gemini if Gemini.nodes[v]['weight']>=4):
        auxgraph.add_node(M,weight=4)
    for M in (v for v in Gemini if Gemini.nodes[v]['weight']==3):
        v=next(iter(M))
        if len(vertices_of_which_satellite(G,v))>2:
            auxgraph.add_node(M,weight=2)
        else:
            auxgraph.add_node(M,weight=4)
    for A,B in Gemini.edges():
        auxgraph.add_edge(A,B)
    return auxgraph

#---------- isometrically embed an arbitrary graph into a strongly CFS graph
def embed_into_strongly_CFS(G):
    D=diagonal_graph(G)
    leg_length=max([3,math.ceil(nx.diameter(G)/2)])
    H=G.copy()
    supported_vertices=set().union(*[support(C) for C in nx.connected_components(D)])
    unsupported_vertices=set(G)-supported_vertices
    spider_zero=0
    while spider_zero in G:
        spider_zero+=1
    spider_one=spider_zero+1
    while spider_one in G:
        spider_one+=1
    H.add_node(spider_zero)
    H.add_node(spider_one)
    for v in [tuple([v,]) for v in unsupported_vertices]+[tuple(d) for d in D]:
        H.add_edges_from([(spider_zero,(v,1,0)),(spider_zero,(v,1,1)),(spider_one,(v,1,0)),(spider_one,(v,1,1))])
        for i in range(2,leg_length):
            H.add_edges_from([((v,i,0),(v,i-1,0)),((v,i,0),(v,i-1,1)),((v,i,1),(v,i-1,0)),((v,i,1),(v,i-1,1))])
    for v in [tuple([v,]) for v in unsupported_vertices]:
        H.add_edges_from([(v[0],(v,leg_length-1,0)),(v[0],(v,leg_length-1,1))])
    for v in [tuple(d) for d in D]:
        H.add_edges_from([(v[0],(v,leg_length-1,0)),(v[0],(v,leg_length-1,1))])
        H.add_edges_from([(v[1],(v,leg_length-1,0)),(v[1],(v,leg_length-1,1))])
    return H
        
        



#----------- some example graphs
def cycle_graph(n):
    """
    Cycle of length n>0 with vertices 0,...,n-1.
    """
    assert(n>2)
    G=nx.Graph()
    for i in range(n):
        G.add_edge(i,(i+1)%n)
    return(G)

    
def suspension(n):
    """
    Suspension of n vertices. Suspension points are 0,1.
    """
    G=nx.Graph()
    for i in range(2,n+2):
        G.add_edge(0,i)
        G.add_edge(1,i)
    return G

def circulant(n,m=3):
    """
    Return the circulant graph with n nodes and step sizes 1 and m. Same as the Cayley graph of Z/nZ with respect to generating set {1,m}.
    """
    # circulant(11,3) is the smallest example of a non-square, strongly CFS graph G for which there does not exist a vertex v such that G-{v} is strongly CFS.
    G=cycle_graph(n)
    for i in range(n):
        G.add_edge(i,(i+3)%n)
    return G

def Pallavi(height,width=3,vertex0=None,vertex1=None):
    # the example Pallavi showed that is a grid with diagonals spanning each side-to-side pair of squares, plus one additional edge between vertex0 and vertex1, which default to (0,height) and (width,0) if not specified.
    G=nx.Graph()
    for level in range(1,1+height):
        for i in range(width+1):
            G.add_edge((i,level),(i,level-1)) #vertical edges
        for i in range(2,width+1):
            G.add_edge((i,level),(i-2,level-1)) #diagonal edges
    for level in range(1+height):
        for i in range(1,width+1):
            G.add_edge((i,level),(i-1,level)) #horizontal edges
    if vertex0 and vertex1:
        G.add_edge(vertex0,vertex1)
    else:
        G.add_edge((0,height),(width,0))
    return G
        
def nested_suspension(n): #isomorphic to Davis_Januskiewicz(nx.path_graph(n+1))
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

def path_graph(n):
    """
    Path graph with n vertices.
    """
    G=nx.Graph()
    G.add_node(0)
    for i in range(1,n):
        G.add_edge(i,i-1)
    return G

def tree(valence,radius):
    """
    Finite radius tree such that all non-leaves have given valence.
    """
    G=nx.Graph()
    G.add_node(0)
    rad=0
    current_node=0
    spheres=dict()
    spheres[0]=set([0,])
    if radius>0:
        spheres[1]=set()
        for i in range(valence):
            current_node+=1
            G.add_edge(0,current_node)
            spheres[1].add(current_node)
    rad=1
    while rad<radius:
        rad+=1
        spheres[rad]=set()
        for v in spheres[rad-1]:
            for i in range(valence-1):
                current_node+=1
                G.add_edge(v,current_node)
                spheres[rad].add(current_node)
    return G
          
def blowup(weightedgraph):
    G=nx.Graph()
    for (v,w) in weightedgraph.edges():
        for i in range(weightedgraph.nodes[v]['weight']):
            for j in range(weightedgraph.nodes[w]['weight']):
                G.add_edge((v,i),(w,j))
    return G
    
    

def thenonconstructablemincfsexample(): # This is a minimal CFS graph that is not strongly CFS. 19 nodes. Smallest known so far. Not triangle-free.
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

def Genevois_minsquare_nonCFS_example():
    # genevois 19 QI rigid subgroups in RACG, Example 7.3(a)
    G=nx.Graph()
    G.add_edge(0,1)
    G.add_edge(0,3)
    G.add_edge(0,4)
    G.add_edge(0,5)
    G.add_edge(1,2)
    G.add_edge(1,6)
    G.add_edge(2,3)
    G.add_edge(2,4)
    G.add_edge(2,5)
    G.add_edge(3,10)
    G.add_edge(4,6)
    G.add_edge(4,8)
    G.add_edge(5,8)
    G.add_edge(5,10)
    G.add_edge(6,7)
    G.add_edge(6,11)
    G.add_edge(7,8)
    G.add_edge(7,9)
    G.add_edge(7,12)
    G.add_edge(8,9)
    G.add_edge(8,11)
    G.add_edge(8,12)
    G.add_edge(9,10)
    G.add_edge(9,11)
    G.add_edge(10,12)
    G.add_edge(11,12)
    return G
    
    
def minsquarebutnotcfsexample():
    G=nx.Graph()
    G.add_edge(0,1)
    G.add_edge(0,2)
    G.add_edge(0,3)
    G.add_edge(1,4)
    G.add_edge(1,5)
    G.add_edge(2,4)
    G.add_edge(2,5)
    G.add_edge(3,4)
    G.add_edge(3,7)
    G.add_edge(3,8)
    G.add_edge(4,6)
    G.add_edge(5,6)
    G.add_edge(5,9)
    G.add_edge(6,7)
    G.add_edge(6,8)
    G.add_edge(7,9)
    G.add_edge(8,9)
    return G



def accidentalsquare(): # 4-legged spider with toes identified to make a square
    G=nx.Graph()
    G.add_edge(0,1)
    G.add_edge(1,2)
    G.add_edge(2,3)
    G.add_edge(3,0)
    G.add_edge(3,4)
    G.add_edge(0,5)
    G.add_edge(0,6)
    G.add_edge(4,5)
    G.add_edge(4,6)
    G.add_edge(5,16)
    G.add_edge(5,17)
    G.add_edge(6,16)
    G.add_edge(6,17)
    G.add_edge(0,7)
    G.add_edge(1,8)
    G.add_edge(1,9)
    G.add_edge(7,8)
    G.add_edge(7,9)
    G.add_edge(8,16)
    G.add_edge(8,17)
    G.add_edge(9,16)
    G.add_edge(9,17)
    G.add_edge(1,10)
    G.add_edge(2,11)
    G.add_edge(2,12)
    G.add_edge(10,11)
    G.add_edge(10,12)
    G.add_edge(11,16)
    G.add_edge(11,17)
    G.add_edge(12,16)
    G.add_edge(12,17)
    G.add_edge(2,13)
    G.add_edge(13,14)
    G.add_edge(13,15)
    G.add_edge(3,14)
    G.add_edge(3,15)
    G.add_edge(14,16)
    G.add_edge(14,17)
    G.add_edge(15,16)
    G.add_edge(15,17)
    return G

def Clebsch():
    G=nx.Graph()
    G.add_edge((0,0,0,0),(0,0,0,1))
    G.add_edge((0,0,0,0),(0,0,1,0))
    G.add_edge((0,0,0,0),(0,1,0,0))
    G.add_edge((0,0,0,0),(1,0,0,0))
    G.add_edge((0,0,0,1),(0,0,1,1))
    G.add_edge((0,0,0,1),(0,1,0,1))
    G.add_edge((0,0,0,1),(1,0,0,1))
    G.add_edge((0,0,1,0),(0,0,1,1))
    G.add_edge((0,0,1,0),(0,1,1,0))
    G.add_edge((0,0,1,0),(1,0,1,0))
    G.add_edge((0,1,0,0),(0,1,0,1))
    G.add_edge((0,1,0,0),(0,1,1,0))
    G.add_edge((0,1,0,0),(1,1,0,0))
    G.add_edge((1,0,0,0),(1,0,0,1))
    G.add_edge((1,0,0,0),(1,0,1,0))
    G.add_edge((1,0,0,0),(1,1,0,0))
    G.add_edge((0,0,1,1),(0,1,1,1))
    G.add_edge((0,0,1,1),(1,0,1,1))
    G.add_edge((0,1,0,1),(0,1,1,1))
    G.add_edge((0,1,0,1),(1,1,0,1))
    G.add_edge((1,0,0,1),(1,0,1,1))
    G.add_edge((1,0,0,1),(1,1,0,1))
    G.add_edge((0,1,1,0),(0,1,1,1))
    G.add_edge((0,1,1,0),(1,1,1,0))
    G.add_edge((1,0,1,0),(1,0,1,1))
    G.add_edge((1,0,1,0),(1,1,1,0))
    G.add_edge((1,1,0,0),(1,1,0,1))
    G.add_edge((1,1,0,0),(1,1,1,0))
    G.add_edge((0,1,1,1),(1,1,1,1))
    G.add_edge((1,0,1,1),(1,1,1,1))
    G.add_edge((1,1,0,1),(1,1,1,1))
    G.add_edge((1,1,1,0),(1,1,1,1))
    G.add_edge((0,0,0,0),(1,1,1,1))
    G.add_edge((0,0,0,1),(1,1,1,0))
    G.add_edge((0,0,1,0),(1,1,0,1))
    G.add_edge((0,1,0,0),(1,0,1,1))
    G.add_edge((1,0,0,0),(0,1,1,1))
    G.add_edge((0,0,1,1),(1,1,0,0))
    G.add_edge((0,1,0,1),(1,0,1,0))
    G.add_edge((1,0,0,1),(0,1,1,0))
    return G

def Wagner():
    G=nx.Graph()
    G.add_edge(0,1)
    G.add_edge(1,2)
    G.add_edge(2,3)
    G.add_edge(3,4)
    G.add_edge(4,5)
    G.add_edge(5,6)
    G.add_edge(6,7)
    G.add_edge(7,0)
    G.add_edge(0,4)
    G.add_edge(1,5)
    G.add_edge(2,6)
    G.add_edge(3,7)
    return G

def Cordes_Levcovitz():
    G=double(nx.path_graph(6))
    G.add_edges_from([((0,2),(0,1)), ((0,2),(3,1)), ((1,2),(1,1)), ((1,2),(4,1)), ((2,2),(2,1)),((2,2),(5,1))])
    G.add_edges_from([((0,-1),(0,0)), ((0,-1),(3,0)), ((1,-1),(1,0)), ((1,-1),(4,0)), ((2,-1),(2,0)),((2,-1),(5,0))])
    return G

#--------------------------- for exporting graph 
def graph2tikz(netgraph_plot_instance):
    """
    Input a netgraph plot instance, output a string with tikz code for drawing the graph in tex. 
    Output includes node labels. We attempt to position them relative to the node to not cover the incident edges, but this will usually need manual adjustment in the tex file if the labels are long. 
    """
    tikzoutputstring='\\begin{tikzpicture}\\tiny\n'
    for i in range(len(netgraph_plot_instance.nodes)):
        thisnodepos=netgraph_plot_instance.node_positions[netgraph_plot_instance.nodes[i]][0]-.5+(netgraph_plot_instance.node_positions[netgraph_plot_instance.nodes[i]][1]-.5)*1j
        thisnodeangle=180.0*cmath.phase(thisnodepos)/cmath.pi
        tikzoutputstring+='\coordinate[label={[label distance=-1pt] '+"{:.2f}".format(thisnodeangle)+':$'+str(netgraph_plot_instance.nodes[i])+'$}] ('+str(i)+') at ('+"{:.2f}".format(thisnodepos.real)+','+"{:.2f}".format(thisnodepos.imag)+');\n'
    for initial,final in netgraph_plot_instance.edges:
        tikzoutputstring+='\\draw ('+str(netgraph_plot_instance.nodes.index(initial))+')--('+str(netgraph_plot_instance.nodes.index(final))+');\n'
    for i in range(len(netgraph_plot_instance.nodes)):
        tikzoutputstring+='\\filldraw ('+str(i)+') circle (.5pt);\n'
    tikzoutputstring+= '\\end{tikzpicture}'
    print(tikzoutputstring)


def color_verts(G):
    """
    Add an attribute 'color' to each vertex of the graph, assigning to each vertex a unique color.
    """
    nodelist=list(G.nodes())
    for i in range(len(nodelist)):
        G.nodes[nodelist[i]]['color']=plt.cm.gist_rainbow(.1+i/(len(nodelist)+1))


        
#----------------------------------

def powerset(iterable,minsize=0,maxsize=float('inf'),small_first=True):
    """
    Return a generator of all subsets of the input iteratble. 
    Limit the size of returned subsets with minsize and maxsize parameters. 
    Default is to yield subsets by increasing cardinality; use small_first=False to yield by decreasing cardinality.
    """
    aslist=list(iterable)
    themax=min(maxsize,len(aslist))
    if small_first:
        return itertools.chain.from_iterable(itertools.combinations(aslist, r) for r in range(minsize,1+themax))
    else:
        return itertools.chain.from_iterable(itertools.combinations(aslist, r) for r in range(themax,minsize-1,-1))







if __name__ == "__main__":
    import doctest
    doctest.testmod()
