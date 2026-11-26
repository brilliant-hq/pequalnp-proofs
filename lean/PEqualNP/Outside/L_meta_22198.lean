import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22198_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [3, 5]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [3, 8]⟩, ⟨.or, [4, 7]⟩, ⟨.not, [10]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [0, 11]⟩, ⟨.not, [12]⟩, ⟨.and, [13, 14]⟩, ⟨.or, [1, 15]⟩, ⟨.and, [9, 16]⟩], 17⟩

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

end PEqualNP.Outside.L_meta_22198_aux

theorem PEqualNP.Outside.L_meta_22198 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (17210 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨PEqualNP.Outside.L_meta_22198_aux.witness, PEqualNP.Outside.L_meta_22198_aux.witnessFit, by decide, by decide +kernel⟩
