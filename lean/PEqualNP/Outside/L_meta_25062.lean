import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_25062 : (∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ v.val ≠ 0) ∨ (u.val = 1 ∧ v.val ≠ 1) ∨ (2 ≤ u.val ∧ v.val = 0))) C) := by
  intro n hn
  let base := n + n
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [1, n]⟩, ⟨.or, [n + 1, 0]⟩,
      ⟨.and, [base, base + 1]⟩, ⟨.not, [base + 2]⟩,
      ⟨.or, [0, base]⟩, ⟨.and, [base + 3, base + 4]⟩], base + 5⟩
  refine ⟨circuit, ?_, by simp [circuit, PEqualNP.CircuitLowerBounds.Circuit.size], ?_⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · intro u v
    let inputs := PEqualNP.Represents.oneEach u v
    have inputLength : inputs.length = base := by
      simp [inputs, PEqualNP.Represents.oneEach, base]
    have readLeft (i : ℕ) (hi : i < n) : inputs.getD i false = decide (u.val = i) := by
      unfold inputs PEqualNP.Represents.oneEach
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simp [Fin.ext_iff, eq_comm]
    have readRight (i : ℕ) (hi : i < n) : inputs.getD (n + i) false = decide (v.val = i) := by
      unfold inputs PEqualNP.Represents.oneEach
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_ofFn, Nat.add_sub_cancel_left]
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp [Fin.ext_iff, eq_comm]
    have leftZero := readLeft 0 (by omega)
    have leftOne := readLeft 1 (by omega)
    have rightZero : inputs.getD n false = decide (v.val = 0) := by
      simpa using readRight 0 (by omega)
    have rightOne := readRight 1 (by omega)
    have readInput (more : List Bool) (i : ℕ) (hi : i < base) :
        (inputs ++ more).getD i false = inputs.getD i false := by
      rw [List.getD_append _ _ _ _ (by omega)]
    have readGate (more : List Bool) (i : ℕ) :
        (inputs ++ more).getD (base + i) false = more.getD i false := by
      rw [List.getD_append_right _ _ _ _ (by omega), inputLength, Nat.add_sub_cancel_left]
    have readGateZero (more : List Bool) :
        (inputs ++ more).getD base false = more.getD 0 false := by
      simpa only [Nat.add_zero] using readGate more 0
    change circuit.eval inputs = _
    have evaluation : circuit.eval inputs =
        ((!((decide (u.val = 1) || decide (v.val = 0)) &&
          (decide (v.val = 1) || decide (u.val = 0)))) &&
          (decide (u.val = 0) || (decide (u.val = 1) || decide (v.val = 0)))) := by
      simp (disch := omega) only [circuit, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
        List.any_cons, List.any_nil, List.all_cons, List.all_nil, List.headD_cons,
        List.append_assoc, List.cons_append, List.nil_append,
        readInput, readGate, readGateZero, List.getD_cons_zero, List.getD_cons_succ,
        leftZero, leftOne, rightZero, rightOne, id_eq, Bool.or_false, Bool.and_true]
    rw [evaluation]
    by_cases huZero : u.val = 0
    · simp [huZero]
    by_cases huOne : u.val = 1
    · simp [huOne]
    have huOther : 2 ≤ u.val := by omega
    by_cases hvZero : v.val = 0 <;> simp [huZero, huOne, huOther, hvZero]
