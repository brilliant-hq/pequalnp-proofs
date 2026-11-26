import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18833

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def gateOk (g : Gate) : Bool :=
  (match g.op with
   | GateOp.and => true
   | GateOp.or => true
   | _ => false) && decide (g.inputs.length ≤ 2)

theorem mono_of_all (C : Circuit) (h : C.gates.all gateOk = true) : Monotone2 C := by
  intro g hg
  have hk := List.all_eq_true.mp h g hg
  simp only [gateOk, Bool.and_eq_true, decide_eq_true_eq] at hk
  obtain ⟨h1, h2⟩ := hk
  refine ⟨?_, h2⟩
  cases hop : g.op <;> simp_all

def witness : Circuit :=
  ⟨[⟨.or, [0, 21]⟩,
    ⟨.or, [1, 22]⟩,
    ⟨.or, [2, 23]⟩,
    ⟨.or, [3, 24]⟩,
    ⟨.or, [4, 25]⟩,
    ⟨.or, [5, 26]⟩,
    ⟨.or, [6, 27]⟩,
    ⟨.or, [14, 7]⟩,
    ⟨.or, [15, 8]⟩,
    ⟨.or, [16, 9]⟩,
    ⟨.or, [17, 10]⟩,
    ⟨.or, [18, 11]⟩,
    ⟨.or, [19, 12]⟩,
    ⟨.or, [20, 13]⟩,
    ⟨.or, [35, 36]⟩,
    ⟨.or, [42, 38]⟩,
    ⟨.and, [28, 43]⟩,
    ⟨.or, [36, 37]⟩,
    ⟨.or, [45, 39]⟩,
    ⟨.and, [29, 46]⟩,
    ⟨.or, [37, 38]⟩,
    ⟨.or, [48, 40]⟩,
    ⟨.and, [30, 49]⟩,
    ⟨.or, [38, 39]⟩,
    ⟨.or, [51, 41]⟩,
    ⟨.and, [31, 52]⟩,
    ⟨.or, [35, 39]⟩,
    ⟨.or, [54, 40]⟩,
    ⟨.and, [32, 55]⟩,
    ⟨.or, [36, 40]⟩,
    ⟨.or, [57, 41]⟩,
    ⟨.and, [33, 58]⟩,
    ⟨.or, [35, 37]⟩,
    ⟨.or, [60, 41]⟩,
    ⟨.and, [34, 61]⟩,
    ⟨.or, [44, 47]⟩,
    ⟨.or, [63, 50]⟩,
    ⟨.or, [64, 53]⟩,
    ⟨.or, [65, 56]⟩,
    ⟨.or, [66, 59]⟩,
    ⟨.or, [67, 62]⟩], 68⟩

theorem witness_mono : Monotone2 witness := mono_of_all witness (by decide)

theorem witness_size : witness.size ≤ 41 := by decide

end PEqualNP.Outside.L_meta_18833

theorem PEqualNP.Outside.L_meta_18833 : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 14 => decide ((u.val < 7 ∧ v.val < 7 ∧ (v.val + 7 - u.val) % 7 ∈ [0, 1, 3]) ∨ (7 ≤ u.val ∧ 7 ≤ v.val ∧ (u.val + 7 - v.val) % 7 ∈ [0, 1, 3]))) 41) := by
  refine ⟨PEqualNP.Outside.L_meta_18833.witness, PEqualNP.Outside.L_meta_18833.witness_mono, PEqualNP.Outside.L_meta_18833.witness_size, ?_⟩
  decide +kernel
