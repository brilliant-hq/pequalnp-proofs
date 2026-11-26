import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23020

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [1, 3]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.or, [8, 11]⟩], 12⟩

private def monotoneOp (op : GateOp) : Bool :=
  match op with
  | .and | .or => true
  | _ => false

private theorem witness_monotone : Monotone2 witness := by
  have check : witness.gates.all (fun g => monotoneOp g.op && decide (g.inputs.length ≤ 2)) =
      true := by decide +kernel
  intro g hg
  have shape := List.all_eq_true.mp check g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at shape
  refine ⟨?_, shape.2⟩
  cases op : g.op <;> simp [op, monotoneOp] at shape ⊢

end PEqualNP.Outside.L_meta_23020

open PEqualNP.Outside.L_meta_23020 in
theorem PEqualNP.Outside.L_meta_23020 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34078 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, witness_monotone, by decide, by decide +kernel⟩
