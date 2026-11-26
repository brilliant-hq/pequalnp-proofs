import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm in
theorem PEqualNP.Outside.L_meta_18681 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x6 ∈ x2.gates, x6.inputs.Nodup) → x3 < x1 + x2.size → x4 < x1 + x2.size → x3 ≠ x4 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), x10.size = x2.size + (1 : ℕ) ∧ PEqualNP.TopForm.IsAO2 x1 x10 ∧ (∀ x11 ∈ x10.gates, x11.inputs.Nodup) ∧ ∀ (x11 : Fin x1 → Bool), (∀ x12 < x1 + x2.size, PEqualNP.BlindGate.wireValue x10 x1 x11 x12 = PEqualNP.BlindGate.wireValue x2 x1 x11 x12) ∧ PEqualNP.BlindGate.wireValue x10 x1 x11 (x1 + x2.size) = (PEqualNP.BlindGate.wireValue x2 x1 x11 x3 || PEqualNP.BlindGate.wireValue x2 x1 x11 x4) := by
  intro n C a b ao distinct ha hb neq
  let g : Gate := ⟨.or, [a,b]⟩
  let D : Circuit := ⟨C.gates ++ [g], C.output⟩
  have size : D.size = C.size + 1 := by simp [D, Circuit.size]
  have inD (h : Gate) (hh : h ∈ D.gates) : h ∈ C.gates ∨ h = g := by
    simpa [D] using hh
  have nd : ∀ h ∈ D.gates, h.inputs.Nodup := by
    intro h hh
    rcases inD h hh with hm | rfl
    · exact distinct h hm
    · simp [g, neq]
  refine ⟨D, size, ⟨?_, ?_, ?_⟩, nd, ?_⟩
  · intro h hh
    rcases inD h hh with hm | rfl
    · exact ao.1 h hm
    · exact Or.inr rfl
  · intro j hj i hi
    by_cases old : j < C.gates.length
    · change i ∈ ((C.gates ++ [g]).getD j ⟨.or, []⟩).inputs at hi
      rw [List.getD_append _ _ _ _ old] at hi
      exact ao.2.1 j old i hi
    · have last : j = C.gates.length := by
        change j < (C.gates ++ [g]).length at hj
        simp at hj
        omega
      subst j
      change i ∈ ((C.gates ++ [g]).getD C.gates.length ⟨.or, []⟩).inputs at hi
      have read : (C.gates ++ [g]).getD C.gates.length ⟨.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [read] at hi
      rcases (by simpa [g] using hi : i = a ∨ i = b) with rfl | rfl
      · exact ha
      · exact hb
  · intro h hh
    rcases inD h hh with hm | rfl
    · exact ao.2.2 h hm
    · rfl
  · intro x
    let w := C.wires (List.ofFn x)
    have stepLength (gs : List Gate) (ws : List Bool) :
        (gs.foldl (fun v h => v ++ [h.op.eval (h.inputs.map fun i => v.getD i false)]) ws).length
          = ws.length + gs.length := by
      induction gs generalizing ws with
      | nil => simp
      | cons h rest ih =>
        rw [List.foldl_cons, ih]
        simp
        omega
    have length : w.length = n + C.size := by
      simpa [w, Circuit.wires, Circuit.size] using stepLength C.gates (List.ofFn x)
    have readings : D.wires (List.ofFn x) = w ++ [w.getD a false || w.getD b false] := by
      simp [D, w, g, Circuit.wires, List.foldl_append, GateOp.eval]
    constructor
    · intro k hk
      rw [PEqualNP.BlindGate.wireValue, readings, List.getD_append _ _ _ _ (length.symm ▸ hk)]
      rfl
    · rw [PEqualNP.BlindGate.wireValue, readings, ← length]
      simp [List.getD_eq_getElem?_getD, PEqualNP.BlindGate.wireValue, w]

