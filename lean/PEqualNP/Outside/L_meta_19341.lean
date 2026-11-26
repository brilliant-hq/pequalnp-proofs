import PEqualNP.Defs

-- Adapted from the accepted PEqualNP.Outside.L_meta_19040 (pull request 23922, Apache License 2.0); the circuit was found by an exact SAT search.

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_19341

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [1, 8]⟩, ⟨.not, [10]⟩, ⟨.or, [9, 12]⟩, ⟨.not, [14]⟩, ⟨.or, [11, 15]⟩, ⟨.and, [13, 16]⟩], 17⟩

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

end PEqualNP.Outside.L_meta_19341

open PEqualNP.Outside.L_meta_19341 in
theorem PEqualNP.Outside.L_meta_19341 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7576638 : ℕ).testBit (5 * u.val + v.val)) C := by
  exact ⟨witness, witnessFit, by decide, by decide +kernel⟩
