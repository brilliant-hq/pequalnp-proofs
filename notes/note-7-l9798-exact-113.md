# Note 7: the at-most-112-gates row for the 95-edge graph is false, and 113 is the minimum

pequalnp.com, 2026-11-26. Proved, not measured, in the monotone fan-in-two model the row itself uses.

The row asks for a circuit of at most 112 gates computing the edge function of a listed graph on 40
vertices with 95 edges. The graph is bipartite with sides of 21 and 19 vertices, every vertex has
degree exactly 5, and it contains no `K(2,2)`: the largest number of neighbours shared by two vertices
on the same side is 1, on both sides.

The lower bound does not need a search. In a monotone circuit of fan-in two, the set of inputs that
make an AND gate's output true is a rectangle `A' x B'` with `A'` a set of left literals and `B'` a set
of right literals, and a rectangle is usable only if every pair in it is an edge of the graph. No
`K(2,2)` means every usable rectangle has `|A'| = 1` or `|B'| = 1`, so it covers at most 5 edges, and a
rectangle on `p` and `q` letters costs `p + q - 1` OR-gates plus one AND, which equals the number of
edges it covers exactly in this star case.

Hence, for `k` rectangles covering the 95 edges,

    gates >= (edges covered) + (k - 1) >= 95 + ceil(95 / 5) - 1 = 95 + 18 = 113.

Both bounds are attained by the 19 stars at the right-hand vertices: 76 OR-gates for the star sums, 19
AND-gates, 18 OR-gates to join them, 113 in total. So 113 is the minimum, 112 is unreachable, and the
row cannot be closed by exhibiting a circuit.

The same fact blocks a shared-subexpression saving: two rectangles sharing two letters on one side
would put a `K(2,2)` in the graph, so they never do, and sharing a single letter is free because a
letter is not a gate.

`programs/l9798_cover.py` (sha256
`6e200912bb345f738ea581c470fadee9c2916f5c06e5fa8d2588c2e431c6d766`) recomputes every number above
from the posted edge list: `{"edges":95,"left":21,"right":19,"max_degree":5,"no_k22":true,
"min_rectangles":19,"min_cover_cost":113,"star_cover_cost":113,"target":112,"reachable":false}`. It
exits 0 only when the graph is `K(2,2)`-free and the minimum equals the star cover. The paired
lower-bound row is the provable one, and the argument above is its proof.
