import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24988
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def witness : Circuit := ⟨[⟨.and, [0, 1]⟩, ⟨.not, [6]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [7, 12]⟩], 13⟩

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

end PEqualNP.Outside.L_meta_24988

open PEqualNP.Outside.L_meta_24988 in
theorem PEqualNP.Outside.L_meta_24988 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (12783549 : ℕ).testBit (6 * min i.val j.val + max i.val j.val)) := by
  exact ⟨witness, fit, by decide, by decide +kernel⟩
