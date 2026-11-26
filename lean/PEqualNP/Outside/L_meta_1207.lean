import Mathlib
import PEqualNP.Defs

/-!
A monotone circuit of ten gates for the edge function of the graph

  (0,1) (0,2) (1,3) (2,4) (3,5) (4,5) (6,7)

The six-cycle part `0-1-3-5-4-2-0` has the vertex cover `{0, 3, 4}`, so the star
cover gives `6 + 3 - 1 = 8` gates for it, and the separate edge `(6,7)` costs one
AND and one OR.

Wires: `0..7` are the inputs, gate `j` writes wire `8 + j`.

  w8  = x1 OR  x2      (the two neighbours of 0)
  w9  = w8 AND x0      "edge (0,1) or edge (0,2) is on"
  w10 = x1 OR  x5      (the two neighbours of 3)
  w11 = w10 AND x3     "edge (1,3) or edge (3,5) is on"
  w12 = x2 OR  x5      (the two neighbours of 4)
  w13 = w12 AND x4     "edge (2,4) or edge (4,5) is on"
  w14 = x6 AND x7      "edge (6,7) is on"
  w15 = w9  OR w11
  w16 = w15 OR w13
  w17 = w16 OR w14     the answer

Ten gates, fan-in two, AND and OR only.
-/

open PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_1207 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 10 ∧
        ∀ x : Fin 8 → Bool,
          C.eval (List.ofFn x) =
            (fun x : Fin 8 → Bool =>
              (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) ||
              (x 3 && x 5) || (x 4 && x 5) || (x 6 && x 7)) x := by
  refine ⟨⟨[⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [8, 0]⟩,
            ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.and, [10, 3]⟩,
            ⟨GateOp.or, [2, 5]⟩, ⟨GateOp.and, [12, 4]⟩,
            ⟨GateOp.and, [6, 7]⟩,
            ⟨GateOp.or, [9, 11]⟩, ⟨GateOp.or, [15, 13]⟩, ⟨GateOp.or, [16, 14]⟩], 17⟩,
          ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp
  · decide +kernel
  · decide +kernel
