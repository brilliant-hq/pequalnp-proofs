import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23950
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.not, [5]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [9, 10]⟩, ⟨.not, [11]⟩], 12⟩

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

end PEqualNP.Outside.L_meta_23950

open PEqualNP.Outside.L_meta_23950 in
theorem PEqualNP.Outside.L_meta_23950 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (4957 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
