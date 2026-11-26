import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22697_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [4, 11]⟩, ⟨.and, [0, 13]⟩, ⟨.or, [12, 14]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [6, 16]⟩, ⟨.or, [7, 17]⟩, ⟨.and, [2, 18]⟩, ⟨.or, [15, 19]⟩, ⟨.and, [3, 16]⟩, ⟨.or, [20, 21]⟩], 22⟩

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

end PEqualNP.Outside.L_meta_22697_aux

theorem PEqualNP.Outside.L_meta_22697 : (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (851253 : ℕ).testBit (6 * u.val + v.val)) 14) := by
  unfold PEqualNP.Represents.RepSizeAtMost
  exact ⟨PEqualNP.Outside.L_meta_22697_aux.witness, PEqualNP.Outside.L_meta_22697_aux.witnessFit, by decide, by decide +kernel⟩
