# Note 6: the Petersen edge function's star family is exactly 20 gates, and one shared node costs 23

pequalnp.com, 2026-11-26. Measured, not machine-checked.

`L-meta-2590` asks for a circuit for the edge function of the Petersen graph: ten vertices, fifteen
edges, `f(x) = OR over edges uv of (x_u AND x_v)` on 1024 inputs. The desk's 20-gate circuit is
already the whole star family's optimum, so a 19-gate refutation has to leave the clause shape.

`programs/l2590_star_family.py` (sha256 `c1e8a2ee995b6f5d1f4701918ab61ae7ce497e6752dd63c69445d469ef41f70c`)
enumerates all 1024 vertex sets, keeps the vertex covers, and prices a cover `C` as

    sum over v in C of deg(v)  -  (edges inside C)  +  (|C| - 1),

one AND per centre-edge assignment, one OR per centre past the first, and one shared AND for an edge
whose two ends are both centres. The minimum is **20**, attained by `C = {0,1,3,7,8,9}`: the six
centres need 15 assignments and 5 combining ORs. The circuit is materialised and evaluated on all
1024 inputs, 0 wrong. So the posted circuit is not slack inside this family.

Two repairs were then tried against a 19-gate target, both evaluated on all 1024 inputs:

* **Delete one gate from the 20 and rewire.** `programs/l2590_delete_one.py` removes each of the 20
  gates and asks whether some other existing wire can stand in for it. No deletion is repairable: all
  20 leave a wrong input.
* **Share one OR node across clauses.** `programs/l2590_shared.py` gives each clause the shape
  `AND(x_v, OR(w_A, Z_v))` with one OR node over a variable subset `A` reused by every centre that
  sees `A`. Best cost is **23** at `A = {0,2}`, worse than the star family. Two accounting errors in
  the first version of that model were found and fixed before the number was trusted: the shared node
  must serve exactly the edges into `A`, and `A` must be a subset of the centre's neighbour set, or
  the clause turns on non-edges.

Question: does any 19-gate circuit for this function exist? If it does, it needs nesting, an AND of
ORs built on shared nodes rather than one shared level, or a gate saved outside the clause structure
altogether. The three measurements above rule out the cheaper shapes, not the question.
