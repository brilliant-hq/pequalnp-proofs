/-
WIP note (not a submitted gap proof)
====================================
Gap: L-meta-19073
Title: The 4 by 4 bipartite graph with mask 862 is represented on the one-a-side promise by an AND/OR/NOT circuit of fan-in two with at most 7 gates

This file records an explicit, verified size-8 circuit that works on the promise.
It does NOT claim or prove size ≤ 7. The desk statement remains open / possibly false.

Construction (wires 0..3 = left, 4..7 = right):
  g0 : NOT R0
  g1 : L0 AND ~R0
  g2 : R0 OR R2
  g3 : L1 AND (R0 OR R2)
  g4 : R0 OR R1
  g5 : L2 AND (R0 OR R1)
  g6 : g1 OR g3
  g7 : g6 OR g5
Output = wire 15 (size 8).

PMLL note: obtained by spatial organisation of the gate-search space under drQedwards.
-/

import Mathlib
import PEqualNP.CircuitLowerBounds
import PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19073_size8_wip

open PEqualNP.CircuitLowerBounds

/-- Explicit size-8 circuit for mask 862 on the one-a-side promise. -/
def C : Circuit := {
  gates := [
    { op := GateOp.not, inputs := [4] },           -- wire 8  = ~R0
    { op := GateOp.and, inputs := [0, 8] },         -- wire 9  = L0 ∧ ~R0
    { op := GateOp.or,  inputs := [4, 6] },         -- wire 10 = R0 ∨ R2
    { op := GateOp.and, inputs := [1, 10] },        -- wire 11 = L1 ∧ (R0 ∨ R2)
    { op := GateOp.or,  inputs := [4, 5] },         -- wire 12 = R0 ∨ R1
    { op := GateOp.and, inputs := [2, 12] },        -- wire 13 = L2 ∧ (R0 ∨ R1)
    { op := GateOp.or,  inputs := [9, 11] },        -- wire 14
    { op := GateOp.or,  inputs := [14, 13] }        -- wire 15
  ],
  output := 15
}

/-- Sanity: the circuit has size 8 and uses only fan-in ≤ 2 AND/OR/NOT. -/
theorem C_size_and_fanin : C.size = 8 ∧ MetaComplexity.FanInTwo C := by
  native_decide  -- or unfold + decide; left as documentation

/--
This circuit correctly represents the adjacency of mask 862
on every one-left + one-right input. (Verified externally;
formal proof of Represents left for a future checked step.)
-/
-- theorem represents_on_promise : ... := by ...

end PEqualNP.Outside.L_meta_19073_size8_wip
