#!/usr/bin/env python3
"""Independent check of two graph families relevant to Written on the Wall II conjecture 189.

Conjecture 189 (Graffiti.pc): if G is connected, n > 1, and every vertex v has distEven(v) <= 1 + sigma(G)
(distEven(v) = number of vertices at even distance from v, v included; sigma = second-smallest degree), then G has a
Hamiltonian path.

Neither family is a counterexample to #189 (every member checked has a Hamiltonian path). They refute two natural
lemmas a uniform proof might rely on. Requires networkx. Usage: python3 verify_families.py
"""
import itertools
import random
import networkx as nx


def blow_up(sizes, cliques, base_edges):
    G = nx.Graph()
    cls = {}
    for c, s in sizes.items():
        cls[c] = [f"{c}{i}" for i in range(s)]
        G.add_nodes_from(cls[c])
        if cliques.get(c, True):
            G.add_edges_from(itertools.combinations(cls[c], 2))
    for a, b in base_edges:
        G.add_edges_from((u, v) for u in cls[a] for v in cls[b])
    return G, cls


def family_F(L):
    """Branch A: clique blow-up of G?qtfo. A minimum cut with 3 components (refutes the 'two-sides' lemma)."""
    sizes = {"A": L - 12, "B": 4, "D": 2, "P": 6, "Q": 6, "x": 1, "y": 1, "Z": L - 4}
    E = [("A", "D"), ("A", "x"), ("A", "y"), ("A", "Z"), ("B", "D"), ("B", "Z"), ("D", "Z"),
         ("P", "x"), ("P", "y"), ("P", "Z"), ("Q", "x"), ("Q", "y"), ("Q", "Z")]
    G, cls = blow_up(sizes, {}, E)
    return G, cls, cls["x"] + cls["y"] + cls["Z"]


def family_E(m):
    """Branch E: C6 blow-up; both the closure and Chvatal-Erdos conditions fail (refutes 'closure or CE')."""
    names = ["V0", "V1", "V2", "V3", "V4", "V5"]
    sizes = dict(zip(names, [2, m, m, m, m - 1, m]))
    cliques = dict(zip(names, [False, True, False, True, True, True]))
    E = [(names[i], names[(i + 1) % 6]) for i in range(6)]
    G, cls = blow_up(sizes, cliques, E)
    return G, cls


def basics(G):
    n = G.number_of_nodes()
    sig = sorted(d for _, d in G.degree())[1]
    D = dict(nx.all_pairs_shortest_path_length(G))
    max_even = max(sum(1 for u in D[v] if D[v][u] % 2 == 0) for v in G)
    return n, sig, max_even


def ham_path(G, tries=4000, seed=1):
    """Randomised greedy with Posa rotations. Returns a verified Hamiltonian path or None (None proves nothing)."""
    rng = random.Random(seed)
    nodes = list(G)
    n = len(nodes)
    for _ in range(tries):
        p = [rng.choice(nodes)]
        used = {p[0]}
        stall = 0
        while len(p) < n and stall < 200:
            cand = [w for w in G[p[-1]] if w not in used]
            if cand:
                w = min(cand, key=lambda w: sum(1 for z in G[w] if z not in used) + rng.random())
                p.append(w)
                used.add(w)
                stall = 0
            else:
                ends = [i for i, w in enumerate(p[:-2]) if w in G[p[-1]]]
                if not ends:
                    break
                i = rng.choice(ends)
                p = p[:i + 1] + p[i + 1:][::-1]
                stall += 1
        if len(p) == n and all(G.has_edge(p[i], p[i + 1]) for i in range(n - 1)):
            return p
    return None


def main():
    print("Family F_L (refutes: 'every minimum cut in the open region leaves exactly 2 components')")
    for L in (16, 20, 24):
        G, cls, S = family_F(L)
        n, sig, me = basics(G)
        R = G.copy()
        R.remove_nodes_from(S)
        k = nx.node_connectivity(G)
        comps = sorted(len(c) for c in nx.connected_components(R))
        tri = sum(nx.triangles(G).values()) > 0
        hp = ham_path(G) is not None
        print(f"  L={L}: n={n} sigma={sig} maxEven={me} (H)={me <= sig + 1} n>=2s+4={n >= 2 * sig + 4} "
              f"diam={nx.diameter(G)} kappa={k}=|S|={len(S)} triangle={tri} components(G-S)={comps} "
              f"Hamiltonian path found={hp}")
    print("Family E_m (refutes: '(H) => (n-1)-closure complete OR kappa >= alpha - 1')")
    for m in (3, 4, 6):
        G, cls = family_E(m)
        n, sig, me = basics(G)
        k = nx.node_connectivity(G)
        alpha = len(max(nx.find_cliques(nx.complement(G)), key=len))
        deg = dict(G.degree())
        best = max(deg[u] + deg[v] for u, v in itertools.combinations(G, 2) if not G.has_edge(u, v))
        V0, V1, V2, V3, V4, V5 = (cls[c] for c in ["V0", "V1", "V2", "V3", "V4", "V5"])
        alt = [x for pair in zip(V3, V2) for x in pair]
        path = V4 + alt + V1 + [V0[0]] + V5 + [V0[1]]
        ok = len(set(path)) == n and all(G.has_edge(path[i], path[i + 1]) for i in range(n - 1))
        print(f"  m={m}: n={n} sigma={sig} maxEven={me} (H)={me <= sig + 1} n>=2s+4={n >= 2 * sig + 4} "
              f"diam={nx.diameter(G)} kappa={k} alpha={alpha} kappa>=alpha-1={k >= alpha - 1} "
              f"max nonadjacent degree sum={best} < n-1={n - 1}: closure stuck={best < n - 1} "
              f"explicit Hamiltonian path valid={ok}")


if __name__ == "__main__":
    main()
