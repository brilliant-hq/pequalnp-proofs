import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23009
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit := ⟨[⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [2, 8]⟩, ⟨.or, [0, 6]⟩, ⟨.and, [9, 10]⟩], 11⟩

private def good (op : GateOp) : Bool :=
  match op with
  | .and | .or => true
  | _ => false

private theorem fit : Monotone2 witness := by
  have h : witness.gates.all (fun g => good g.op && decide (g.inputs.length ≤ 2)) =
      true := by decide +kernel
  intro g hg
  have leg := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at leg
  refine ⟨?_,leg.2⟩
  cases hop : g.op <;> simp [hop,good] at leg ⊢

end PEqualNP.Outside.L_meta_23009

open PEqualNP.Outside.L_meta_23009 in
theorem PEqualNP.Outside.L_meta_23009 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 7 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (99870 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
