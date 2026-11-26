import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23431

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or, [4, 5]⟩,
    ⟨.not, [0]⟩,
    ⟨.and, [7, 6]⟩,
    ⟨.or, [2, 0]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.not, [11]⟩], 12⟩

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

theorem main_aux :
    ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
        (2114487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, witnessFit, by decide, by decide +kernel⟩

end PEqualNP.Outside.L_meta_23431

theorem PEqualNP.Outside.L_meta_23431 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2114487 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) :=
  PEqualNP.Outside.L_meta_23431.main_aux
