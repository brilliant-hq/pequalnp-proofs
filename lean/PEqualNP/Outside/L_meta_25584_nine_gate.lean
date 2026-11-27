import PEqualNP.Defs

/-!
# L-meta-25584 — an eight-gate selector is impossible; nine gates suffice

The task asked for a `Monotone2` circuit of at most **eight** gates computed on five
one-hot row wires `0..4` and five pair wires `5..9`, deciding `u = a ∨ u = b`.

This file records the **nine**-gate circuit, which is the minimum. The eight-gate
upper bound in the task statement is therefore not attainable (see
`docs/findings/F-meta25584.md` for the exhaustive z3 evidence).

Gate layout (wires `0..4` = row one-hot, `5..9` = pair indicator):

| gate | op  | inputs | wire |
|------|-----|--------|------|
| 0    | and | 0, 5   | 10   |
| 1    | and | 1, 6   | 11   |
| 2    | and | 4, 9   | 12   |
| 3    | and | 2, 7   | 13   |
| 4    | or  | 10, 11 | 14   |
| 5    | and | 3, 8   | 15   |
| 6    | or  | 12, 14 | 16   |
| 7    | or  | 13, 15 | 17   |
| 8    | or  | 16, 17 | 18   |

Output wire `18`.

SPDX-License-Identifier: Apache-2.0
-/

/-- The nine-gate selector: `Monotone2`, size 9, and it decides `u = a ∨ u = b`
on every one of the 125 triples. -/
theorem PEqualNP.Outside.L_meta_25584_nine_gate :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 9 ∧
      ∀ (u a b : Fin 5),
        C.eval (List.ofFn (fun i : Fin 5 => decide (i = u)) ++
          List.ofFn (fun i : Fin 5 => decide (i = a ∨ i = b))) = decide (u = a ∨ u = b) := by
  refine ⟨⟨[⟨.and, [0, 5]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [4, 9]⟩, ⟨.and, [2, 7]⟩,
           ⟨.or, [10, 11]⟩, ⟨.and, [3, 8]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [13, 15]⟩,
           ⟨.or, [16, 17]⟩], 18⟩, ?_, by decide, ?_⟩
  · intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨by simp, by simp⟩
  · decide +kernel
