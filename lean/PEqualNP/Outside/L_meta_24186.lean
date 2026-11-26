import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24186_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [1, 4]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [5, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 9]⟩, ⟨.or, [7, 11]⟩, ⟨.or, [10, 12]⟩, ⟨.or, [0, 14]⟩, ⟨.not, [15]⟩, ⟨.or, [13, 16]⟩], 17⟩

def acceptedOp (g : Gate) : Bool :=
  match g.op with
  | .and | .or | .not => true
  | _ => false

theorem acceptedOpSound (g : Gate) (ok : acceptedOp g = true) :
    g.op = .and ∨ g.op = .or ∨ g.op = .not := by
  cases h : g.op <;> simp [acceptedOp, h] at ok ⊢

theorem witnessFit : FanInTwo witness := by
  have legal : witness.gates.all (fun g => acceptedOp g && decide (g.inputs.length ≤ 2)) = true := by
    decide +kernel
  intro g hg
  have passed := List.all_eq_true.mp legal g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at passed
  exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using acceptedOpSound g passed.1,
    passed.2⟩

end PEqualNP.Outside.L_meta_24186_aux

theorem PEqualNP.Outside.L_meta_24186 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (266774 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_24186_aux.witness, PEqualNP.Outside.L_meta_24186_aux.witnessFit, by decide, by decide +kernel⟩
