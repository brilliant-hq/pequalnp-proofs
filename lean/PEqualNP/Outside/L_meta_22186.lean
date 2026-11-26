import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22186_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [6, 7]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [1, 5]⟩, ⟨.or, [2, 13]⟩, ⟨.or, [9, 14]⟩, ⟨.and, [12, 15]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [17, 18]⟩, ⟨.or, [16, 19]⟩], 20⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : Monotone2 witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_22186_aux

theorem PEqualNP.Outside.L_meta_22186 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (841586 : ℕ).testBit (6 * u.val + v.val)) 12) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_22186_aux.witness, PEqualNP.Outside.L_meta_22186_aux.witnessFit, by decide, by decide +kernel⟩
