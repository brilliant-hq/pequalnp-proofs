import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_8277_2
    (hCover :
    let a : List Nat := [29, 225, 1793, 294, 586, 1170]
    let b : List Nat := [3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092]
    let t : List Nat := [290491182601031952, 77704707237741441, 76583205372905601, 17829957, 72622755967141937, 1099511632424, 281474977890344, 20, 19963012711297, 68720656419, 1116708405768, 65536, 1099529719813, 4294967312, 4295032836, 1, 5066721379698817, 281492173488648, 68719481379, 256, 281474994541573, 4294967556, 4294967312, 1, 85917175877, 4295032832, 4294967552, 1]
    let bit : Nat → Nat → Bool := Nat.testBit
    ∀ r c : Nat, r &&& 7 ≠ 7 → r &&& 56 ≠ 56 →
      (∀ m ∈ a ++ b, ((List.range 11).filter (c &&& m).testBit).length ≤ 2) →
      (∀ i : Fin 6, r.testBit i.val = true → c &&& a.getD i.val 0 = 0) →
      ∃ d : Fin 2048, (t.getD (d.val / 64) 0).testBit (d.val % 64) = true ∧
        (∀ i : Fin 6, r.testBit i.val = true → d.val &&& a.getD i.val 0 = 0) ∧
        ∀ j < 11, c.testBit j = true → bit d.val j = true)
    (hWitness :
    let a : List Nat := [29, 225, 1793, 294, 586, 1170]
    let b : List Nat := [3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092]
    let t : List Nat := [290491182601031952, 77704707237741441, 76583205372905601, 17829957, 72622755967141937, 1099511632424, 281474977890344, 20, 19963012711297, 68720656419, 1116708405768, 65536, 1099529719813, 4294967312, 4295032836, 1, 5066721379698817, 281492173488648, 68719481379, 256, 281474994541573, 4294967556, 4294967312, 1, 85917175877, 4295032832, 4294967552, 1]
    let input := fun (f : Nat → Bool) (c : Nat) => (List.range 6).map f ++
      (List.range 11).map c.testBit ++ b.map (fun m => decide (c &&& m ≠ 0))
    let pow2 := fun k : Nat => 2^k
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 30 C ∧ C.size = 28 ∧ C.output = 57 ∧
      (∀ (i : Fin 6) (j : Fin 11), (a.getD i.val 0).testBit j.val = true →
        C.eval (input (pow2 i.val).testBit (pow2 j.val)) = true) ∧
      ∀ d : Fin 2048, (t.getD (d.val / 64) 0).testBit (d.val % 64) = true →
        C.eval (input (fun i => decide (d.val &&& a.getD i 0 = 0)) d.val) = false) :
have x1 : List ℕ := [(29 : ℕ), (225 : ℕ), (1793 : ℕ), (294 : ℕ), (586 : ℕ), (1170 : ℕ)]; have x2 : List ℕ := [(3 : ℕ), (40 : ℕ), (1064 : ℕ), (272 : ℕ), (336 : ℕ), (516 : ℕ), (644 : ℕ), (48 : ℕ), (560 : ℕ), (264 : ℕ), (392 : ℕ), (68 : ℕ), (1092 : ℕ)]; have x3 : ℕ → ℕ → List Bool := fun (x3 x4 : ℕ) => List.map x3.testBit (List.range (6 : ℕ)) ++ List.map x4.testBit (List.range (11 : ℕ)) ++ List.map (fun (x5 : ℕ) => Decidable.decide (x4 &&& x5 ≠ (0 : ℕ))) x2; have x4 : ℕ → ℕ := fun (x4 : ℕ) => (2 : ℕ) ^ x4; ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (30 : ℕ) x5 ∧ x5.size = (28 : ℕ) ∧ x5.output = (57 : ℕ) ∧ (∀ (x6 : Fin (6 : ℕ)) (x7 : Fin (11 : ℕ)), (x1.getD ↑x6 (0 : ℕ)).testBit ↑x7 = Bool.true → x5.eval (x3 (x4 ↑x6) (x4 ↑x7)) = Bool.true) ∧ ∀ (x6 x7 : ℕ), x6 &&& (7 : ℕ) ≠ (7 : ℕ) → x6 &&& (56 : ℕ) ≠ (56 : ℕ) → (∀ x10 ∈ x1 ++ x2, (List.filter (x7 &&& x10).testBit (List.range (11 : ℕ))).length ≤ (2 : ℕ)) → (∀ (x11 : Fin (6 : ℕ)), x6.testBit ↑x11 = Bool.true → x7 &&& x1.getD ↑x11 (0 : ℕ) = (0 : ℕ)) → x5.eval (x3 x6 x7) = Bool.false := by
  have evalMono {n : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
      {xs ys : List Bool} (hlen : xs.length = ys.length)
      (hle : ∀ i, xs.getD i false = true → ys.getD i false = true) :
      C.eval xs = true → C.eval ys = true := by
    let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
      w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have hfold (gs : List PEqualNP.CircuitLowerBounds.Gate)
        (hg : ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or)
        (x y : List Bool) (hl : x.length = y.length)
        (le : ∀ i, x.getD i false = true → y.getD i false = true) :
        ∀ i, (gs.foldl step x).getD i false = true → (gs.foldl step y).getD i false = true := by
      induction gs generalizing x y with
      | nil => exact le
      | cons g gs ih =>
        apply ih (fun g' h => hg g' (List.mem_cons_of_mem _ h))
        · simp [step, hl]
        · have hv :
              g.op.eval (g.inputs.map (fun i => x.getD i false)) = true →
                g.op.eval (g.inputs.map (fun i => y.getD i false)) = true := by
            rcases hg g (by simp) with hop | hop
            · rw [hop]
              change (g.inputs.map (fun i => x.getD i false)).all id = true →
                (g.inputs.map (fun i => y.getD i false)).all id = true
              simp only [List.all_eq_true, List.mem_map, id_eq]
              intro h b hb
              obtain ⟨i, hi, rfl⟩ := hb
              exact le i (h _ ⟨i,hi,rfl⟩)
            · rw [hop]
              change (g.inputs.map (fun i => x.getD i false)).any id = true →
                (g.inputs.map (fun i => y.getD i false)).any id = true
              simp only [List.any_eq_true, List.mem_map, id_eq]
              rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
              exact ⟨_, ⟨i,hi,rfl⟩, le i hb⟩
          intro i
          change (x ++ [_]).getD i false = true → (y ++ [_]).getD i false = true
          by_cases hi : i < x.length
          · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
            exact le i
          · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ← hl]
            cases i - x.length with
            | zero => exact hv
            | succ k => simp
    exact hfold C.gates hC.1 xs ys hlen hle C.output
  let a : List Nat := [29, 225, 1793, 294, 586, 1170]
  let b : List Nat := [3, 40, 1064, 272, 336, 516, 644, 48, 560, 264, 392, 68, 1092]
  let input := fun (f : Nat → Bool) (c : Nat) => (List.range 6).map f ++
    (List.range 11).map c.testBit ++ b.map (fun m => decide (c &&& m ≠ 0))
  obtain ⟨C, ao, cost, output, pos, neg⟩ := hWitness
  refine ⟨C, ao, cost, output, pos, ?_⟩
  intro r c hr1 hr2 hc hdis
  obtain ⟨d,hd,hrow,hcol⟩ := hCover r c hr1 hr2 hc hdis
  let f := fun i : Nat => decide (d.val &&& a.getD i 0 = 0)
  change C.eval (input r.testBit c) = false
  have nd : C.eval (input f d.val) = false := neg d hd
  have auxSmall : ∀ m ∈ b, m < 2^11 := by decide
  have auxMono (m : Nat) (hm : m ∈ b) (nonzero : c &&& m ≠ 0) : d.val &&& m ≠ 0 := by
    intro zero
    apply nonzero
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases small : j < 11
    · have h := congrArg (fun n : Nat => n.testBit j) zero
      simp only [Nat.testBit_and, Nat.zero_testBit] at h ⊢
      by_cases bit : c.testBit j = true
      · have db := hcol j small bit
        simpa only [bit, db, Bool.true_and] using h
      · have fb := Bool.eq_false_iff.mpr bit
        simp only [fb, Bool.false_and]
    · have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 11 ≤ j)
      have hmj := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (auxSmall m hm) hpow)
      simp [Nat.testBit_and, hmj]
  let implies := fun x y : Bool => x = true → y = true
  have mapLe (ns : List Nat) (f g : Nat → Bool)
      (h : ∀ j ∈ ns, f j = true → g j = true) : List.Forall₂ implies (ns.map f) (ns.map g) := by
    induction ns with
    | nil => exact .nil
    | cons n ns ih =>
      exact .cons (h n (by simp)) (ih (fun k hk => h k (by simp [hk])))
  have rel : List.Forall₂ implies (input r.testBit c) (input f d.val) := by
    apply List.rel_append
    · apply List.rel_append
      · apply mapLe
        intro i hi h
        exact decide_eq_true (hrow ⟨i,List.mem_range.mp hi⟩ h)
      · exact mapLe _ _ _ (fun j hj => hcol j (List.mem_range.mp hj))
    · apply mapLe
      intro m hm h
      exact decide_eq_true (auxMono m hm (of_decide_eq_true h))
  have getLe {x y : List Bool} (p : List.Forall₂ implies x y) (i : Nat) :
      x.getD i false = true → y.getD i false = true := by
    induction p generalizing i with
    | nil => simp
    | cons h _ ih =>
      cases i with
      | zero => exact h
      | succ i => exact ih i
  cases e : C.eval (input r.testBit c) with
  | false => rfl
  | true =>
    have ht := evalMono C ao rel.length_eq (getLe rel) e
    simp [nd] at ht
