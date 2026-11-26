import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23976
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit := ⟨[⟨.not, [3]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [4, 8]⟩, ⟨.not, [9]⟩, ⟨.and, [7, 10]⟩, ⟨.or, [6, 11]⟩], 12⟩

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

end PEqualNP.Outside.L_meta_23976

open PEqualNP.Outside.L_meta_23976 in
theorem PEqualNP.Outside.L_meta_23976 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12631 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
