import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18917

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

end PEqualNP.Outside.L_meta_18917

open PEqualNP.Outside.L_meta_18917 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_18917 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 : ℕ) (x7 : Fin x1 → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     x2.output = x1 + x3 →       x3 + (1 : ℕ) = x2.size →         x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →           have x12 : ℕ → Bool := fun (x12 : ℕ) => (x2.wires (List.ofFn x7)).getD x12 Bool.false;           x12 x4 = Bool.false → x12 x5 = Bool.false → ∃ (x15 : ℕ → Bool), (∀ x16 < x1, x15 x16 = Decidable.decide (x16 = x6)) ∧ (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) (x18 x19 : ℕ), x2.gates[x16]? = Option.some x17 → x17.inputs = [x18, x19] → (x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x15 (x1 + x16) = (x12 x18 && x15 x19 || x15 x18 && x12 x19)) ∧ (x17.op = PEqualNP.CircuitLowerBounds.GateOp.or → x15 (x1 + x16) = (x15 x18 || x15 x19))) ∧ x15 x2.output = Bool.false := by
  intro n C idx a b seed x fit out _ hGate
  dsimp only
  intro ha hb
  let w := C.wires (List.ofFn x)
  let d := flow n C seed w
  have recStep (j : ℕ) (g : Gate) (a b : ℕ)
      (someGate : C.gates[j]? = some g) (pair : g.inputs = [a,b]) :
      (g.op = .and → d (n+j) = (w.getD a false && d b || d a && w.getD b false)) ∧
      (g.op = .or → d (n+j) = (d a || d b)) := by
      have jLt : j < C.gates.length := (List.getElem?_eq_some_iff.mp someGate).choose
      have atGate : gateAt C j = g := by
        simp [gateAt, List.getD_eq_getElem?_getD, someGate]
      have hread := fit.2.1 j jLt
      rw [atGate, pair] at hread
      have earlier : a < n+j ∧ b < n+j := ⟨hread a (by simp),hread b (by simp)⟩
      have outside : ¬ n+j < n := by omega
      have idx : n+j-n = j := by omega
      constructor <;> intro op
      · change flow n C seed w (n+j) = _
        rw [flow]
        simp only [outside, idx, someGate, pair, earlier, op, ite_true]
        rfl
      · change flow n C seed w (n+j) = _
        rw [flow]
        simp only [outside, idx, someGate, pair, earlier,
          op, Bool.false_eq_true, ite_false]
        rfl
  refine ⟨d, ?_, recStep, ?_⟩
  · intro i hi
    change flow n C seed w i = _
    rw [flow, ite_eq_left hi]
  · rw [out, (recStep idx ⟨.and,[a,b]⟩ a b hGate rfl).1 rfl]
    have ha' : w.getD a false = false := ha
    have hb' : w.getD b false = false := hb
    simp [ha', hb', -List.getD_eq_getElem?_getD]
