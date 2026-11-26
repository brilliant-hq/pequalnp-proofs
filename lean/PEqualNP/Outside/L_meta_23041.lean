import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23041
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit := ⟨[⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [5, 6]⟩, ⟨.or, [8, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [0, 11]⟩], 12⟩

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

end PEqualNP.Outside.L_meta_23041

open PEqualNP.Outside.L_meta_23041 in
theorem PEqualNP.Outside.L_meta_23041 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (233279 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
