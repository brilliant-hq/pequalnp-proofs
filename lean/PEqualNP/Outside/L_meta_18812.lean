import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18812

open PEqualNP.CircuitLowerBounds

private def flow (n : ℕ) (C : Circuit) (seed : ℕ) (w : List Bool) (k : ℕ) : Bool :=
  if k < n then decide (k = seed) else
    match C.gates[k-n]? with
    | some g =>
      match g.inputs with
      | [a,b] =>
        if _valid : a < k ∧ b < k then
          if (match g.op with | .and => true | _ => false) then
            (w.getD a false && flow n C seed w b) || (flow n C seed w a && w.getD b false)
          else flow n C seed w a || flow n C seed w b
        else false
      | _ => false
    | none => false
termination_by k
decreasing_by all_goals first | exact _valid.1 | exact _valid.2

end PEqualNP.Outside.L_meta_18812

open PEqualNP.Outside.L_meta_18812 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_18812 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : ℕ) (x4 : List Bool), PEqualNP.TopForm.IsAO2 x1 x2 → ∃ (x6 : ℕ → Bool), (∀ x7 < x1, x6 x7 = Decidable.decide (x7 = x3)) ∧ ∀ (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) (x9 x10 : ℕ), x2.gates[x7]? = Option.some x8 → x8.inputs = [x9, x10] → (x8.op = PEqualNP.CircuitLowerBounds.GateOp.and → x6 (x1 + x7) = ((x2.wires x4).getD x9 Bool.false && x6 x10 || x6 x9 && (x2.wires x4).getD x10 Bool.false)) ∧ (x8.op = PEqualNP.CircuitLowerBounds.GateOp.or → x6 (x1 + x7) = (x6 x9 || x6 x10)) := by
  intro n C seed w fit
  let d := flow n C seed (C.wires w)
  refine ⟨d, ?_, ?_⟩
  · intro i hi
    change flow n C seed (C.wires w) i = _
    rw [flow, ite_eq_left hi]
  · intro j g a b someGate pair
    have jLt : j < C.gates.length := (List.getElem?_eq_some_iff.mp someGate).choose
    have atGate : gateAt C j = g := by
      simp [gateAt, List.getD_eq_getElem?_getD, someGate]
    have hread := fit.2.1 j jLt
    rw [atGate, pair] at hread
    have earlier : a < n+j ∧ b < n+j := ⟨hread a (by simp),hread b (by simp)⟩
    have outside : ¬ n+j < n := by omega
    have idx : n+j-n = j := by omega
    constructor <;> intro op
    · change flow n C seed (C.wires w) (n+j) = _
      rw [flow]
      simp only [outside, idx, someGate, pair, earlier, op, ite_true]
      rfl
    · change flow n C seed (C.wires w) (n+j) = _
      rw [flow]
      simp only [outside, idx, someGate, pair, earlier,
        op, Bool.false_eq_true, ite_false]
      rfl

