import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24897
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit := ⟨[⟨.or, [4, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.not, [7]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [1, 7]⟩, ⟨.and, [2, 6]⟩, ⟨.or, [10, 11]⟩, ⟨.or, [0, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

private def good (op : GateOp) : Bool :=
  match op with
  | .and | .or | .not => true
  | _ => false

private theorem fit : FanInTwo witness := by
  have h : witness.gates.all (fun g => good g.op && decide (g.inputs.length ≤ 2)) =
      true := by decide +kernel
  intro g hg
  have leg := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at leg
  refine ⟨?_,leg.2⟩
  cases hop : g.op <;> simp [hop,good] at leg ⊢

end PEqualNP.Outside.L_meta_24897

open PEqualNP.Outside.L_meta_24897 in
theorem PEqualNP.Outside.L_meta_24897 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (2297663 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
