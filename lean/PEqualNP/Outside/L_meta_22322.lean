import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22322_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.not, [10]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [7, 13]⟩, ⟨.not, [14]⟩, ⟨.or, [12, 15]⟩, ⟨.and, [16, 17]⟩], 18⟩

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

end PEqualNP.Outside.L_meta_22322_aux

theorem PEqualNP.Outside.L_meta_22322 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 13 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (18107 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22322_aux.witness, PEqualNP.Outside.L_meta_22322_aux.witnessFit, by decide, by decide +kernel⟩
