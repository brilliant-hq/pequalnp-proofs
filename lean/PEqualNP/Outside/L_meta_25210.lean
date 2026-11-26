import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25210

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [5, 0]⟩, ⟨.and, [6, 1]⟩, ⟨.or, [7, 3]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [2, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [12, 10]⟩, ⟨.or, [13, 12]⟩, ⟨.or, [11, 13]⟩], 15⟩

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

theorem main_proof : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33969 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  ⟨witness, witnessFit, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_25210

theorem PEqualNP.Outside.L_meta_25210 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (33969 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_25210.main_proof
