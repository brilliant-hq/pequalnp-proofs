import PEqualNP.Defs

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_8229_36 :
    (∃ (gs : List (Bool × Fin 32 × Fin 32)) (terms : List (Fin 32 × Fin 32)),
      let ws := gs.foldl (fun (w : List ℕ) g => w ++ [if g.1 = true then
          w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0 else
          w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0])
        [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
         26322415680, 344922804352, 414195942664, 581968119809, 1065151898146, 685262031889, 685297815317, 1067030980394, 652835063552, 663661938444, 435849692940]
      let out := fun (p : Fin 32 × Fin 32) => ws.getD p.1.val 0 &&& ws.getD p.2.val 0
      gs.length + 2 * terms.length ≤ 14 ∧
        (∀ i : Fin gs.length, (gs.get i).2.1.val < 17 + i.val ∧ (gs.get i).2.2.val < 17 + i.val) ∧
        (gs.filter (·.1)).length = 1 ∧
        (∀ i : Fin gs.length, (gs.get i).1 = true →
          ws.getD (17 + i.val) 0 &&& 1099511562240 ≠ 0) ∧
        (∀ p ∈ terms, p.1.val < 17 + gs.length ∧ p.2.val < 17 + gs.length ∧
          out p &&& 1099511562240 = 0) ∧
        terms.foldl (fun n p => n ||| out p) 34572 = 65535) →
    (∀ (z : List ℕ) (A : List (Bool × Fin 32 × Fin 32)) (T : List (Fin 32 × Fin 32)),
      let step := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]
      let V := A.foldl step z
      z.length = 11 → A.length + 2 * T.length ≤ 22 → T ≠ [] →
      (∀ j : Fin A.length, (A.get j).2.1.val < 11 + j.val ∧
        (A.get j).2.2.val < 11 + j.val) →
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length) →
      ∃ (R : List (Bool × Fin 32 × Fin 32)) (B : Fin 21 → Bool × Fin 32 × Fin 32),
      List.ofFn B = A ++ T.map (fun p => (true, p)) ++ R ∧ (∀ g ∈ R, g.1 = false) ∧
      (∀ j : Fin 21, (B j).2.1.val < 11 + j.val ∧ (B j).2.2.val < 11 + j.val) ∧
      ((List.ofFn B).foldl step z).getD 31 0 =
        T.foldl (fun b p => b ||| (V.getD p.1 0 &&& V.getD p.2 0)) 0) →
    (∀ (z : List ℕ) (m : ℕ) (A R : List (Bool × Fin 32 × Fin 32))
        (T : List (Fin 32 × Fin 32)) (B : Fin 21 → Bool × Fin 32 × Fin 32),
      let step := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]
      let V := A.foldl step z
      let W := (List.ofFn B).foldl step z
      z.length = 11 → List.ofFn B = A ++ T.map (fun p => (true, p)) ++ R → (∀ g ∈ R, g.1 = false) →
      (∀ j : Fin A.length, (A.get j).1 = true → V.getD (11 + j.val) 0 &&& m ≠ 0) →
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length ∧
        (V.getD p.1 0 &&& V.getD p.2 0) &&& m = 0) →
      (List.ofFn (fun j : Fin 21 => decide ((B j).1 = true ∧
        W.getD (11 + j.val) 0 &&& m ≠ 0))).count true = (A.filter (·.1)).length ∧
      ∀ i : Fin 21, (B i).1 = true → W.getD (11 + i.val) 0 &&& m = 0 →
        A.length ≤ i.val) →
    (∀ (A R : List (Bool × Fin 32 × Fin 32)) (T : List (Fin 32 × Fin 32))
        (B : Fin 21 → Bool × Fin 32 × Fin 32),
      List.ofFn B = A ++ T.map (fun p => (true, p)) ++ R → (∀ g ∈ R, g.1 = false) →
      (∀ j : Fin 21, (B j).2.1.val < 11 + j.val ∧ (B j).2.2.val < 11 + j.val) →
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length) →
      let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨(List.ofFn B).map (fun g =>
        ⟨if g.1 = true then .and else .or, [g.2.1.val, g.2.2.val]⟩), 31⟩
      ∀ i j : Fin 21, A.length ≤ i.val → (B j).1 = true → ¬ PEqualNP.EdgeOwnership.InCone 11 C i.val j.val) →
    ∃ (x1 : Fin (21 : ℕ) → Bool × Fin (32 : ℕ) × Fin (32 : ℕ)),   (∀ (x2 : Fin (21 : ℕ)), ↑(x1 x2).2.1 < (11 : ℕ) + ↑x2 ∧ ↑(x1 x2).2.2 < (11 : ℕ) + ↑x2) ∧     have x2 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.map (fun (x2 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => { op := if x2.1 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [↑x2.2.1, ↑x2.2.2] : PEqualNP.CircuitLowerBounds.Gate }) (List.ofFn x1), output := (31 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit };     have x3 : List ℕ := List.foldl (fun (x3 : List ℕ) (x4 : Bool × Fin (32 : ℕ) × Fin (32 : ℕ)) => x3 ++ [if x4.1 = Bool.true then x3.getD ↑x4.2.1 (0 : ℕ) &&& x3.getD ↑x4.2.2 (0 : ℕ) else x3.getD ↑x4.2.1 (0 : ℕ) ||| x3.getD ↑x4.2.2 (0 : ℕ)]) [(2147418115 : ℕ), (663661903884 : ℕ), (34144976944 : ℕ), (728266375360 : ℕ), (21653750532 : ℕ), (103293914128 : ℕ), (26322415680 : ℕ), (344922804352 : ℕ), (414195942664 : ℕ), (581968119809 : ℕ), (1065151898146 : ℕ)] (List.ofFn x1);     x3.getD (31 : ℕ) (0 : ℕ) = (65535 : ℕ) ∧ List.count Bool.true (List.ofFn fun (x4 : Fin (21 : ℕ)) => Decidable.decide ((x1 x4).1 = Bool.true ∧ x3.getD ((11 : ℕ) + ↑x4) (0 : ℕ) &&& (1099511562240 : ℕ) ≠ (0 : ℕ))) = (2 : ℕ) ∧ ∀ (x4 x5 : Fin (21 : ℕ)), (x1 x4).1 = Bool.true → x3.getD ((11 : ℕ) + ↑x4) (0 : ℕ) &&& (1099511562240 : ℕ) = (0 : ℕ) → (x1 x5).1 = Bool.true → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x2 ↑x4 ↑x5 := by
  intro remaining assemble flags cones
  have core : ∃ (A : List (Bool × Fin 32 × Fin 32)) (T : List (Fin 32 × Fin 32)),
      let V := A.foldl (fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
        w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0
          else w.getD g.2.1 0 ||| w.getD g.2.2 0]) [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
       26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]
      let term := fun p : Fin 32 × Fin 32 => V.getD p.1 0 &&& V.getD p.2 0
      A.length + 2 * T.length ≤ 22 ∧ T ≠ [] ∧
      (∀ j : Fin A.length, (A.get j).2.1.val < 11 + j.val ∧
        (A.get j).2.2.val < 11 + j.val) ∧
      (A.filter (·.1)).length = 2 ∧
      (∀ j : Fin A.length, (A.get j).1 = true →
        V.getD (11 + j.val) 0 &&& 1099511562240 ≠ 0) ∧
      (∀ p ∈ T, p.1.val < 11 + A.length ∧ p.2.val < 11 + A.length ∧
        term p &&& 1099511562240 = 0) ∧
      T.foldl (fun b p => b ||| term p) 0 = 65535 := by
    let roots : List ℕ := [2147418115, 663661903884, 34144976944, 728266375360, 21653750532,
       103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146]
    let head : List (Bool × Fin 32 × Fin 32) :=
      [(false, 5, 9), (false, 4, 11), (false, 8, 10), (true, 12, 13), (false, 1, 14), (false, 4, 8)]
    let value := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) =>
      if g.1 = true then w.getD g.2.1.val 0 &&& w.getD g.2.2.val 0
      else w.getD g.2.1.val 0 ||| w.getD g.2.2.val 0
    let step := fun (w : List ℕ) (g : Bool × Fin 32 × Fin 32) => w ++ [value w g]
    let seed : List ℕ := head.foldl step roots
    let emit := fun (w : List ℕ) (p : Fin 32 × Fin 32) => w.getD p.1.val 0 &&& w.getD p.2.val 0
    let first : Fin 32 × Fin 32 := (15, 16)
    obtain ⟨gs, ts, h⟩ := remaining
    have seedVal : seed = [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128, 26322415680, 344922804352, 414195942664, 581968119809, 1065151898146, 685262031889, 685297815317, 1067030980394, 652835063552, 663661938444, 435849692940] := by decide +kernel
    rw [← seedVal] at h
    let bank := gs.foldl step seed
    change gs.length + 2 * ts.length ≤ 14 ∧
      (∀ i : Fin gs.length, (gs.get i).2.1.val < 17 + i.val ∧ (gs.get i).2.2.val < 17 + i.val) ∧
      (gs.filter (·.1)).length = 1 ∧
      (∀ i : Fin gs.length, (gs.get i).1 = true → bank.getD (17+i.val) 0 &&& 1099511562240 ≠ 0) ∧
      (∀ p ∈ ts, p.1.val < 17+gs.length ∧ p.2.val < 17+gs.length ∧ emit bank p &&& 1099511562240 = 0) ∧
      ts.foldl (fun n p => n ||| emit bank p) 34572 = 65535 at h
    obtain ⟨budget, inputs, dirtyCount, dirty, clean, covers⟩ := h
    have same : (head ++ gs).foldl step roots = bank := by rw [List.foldl_append]
    have preserve (xs : List (Bool × Fin 32 × Fin 32)) (base : List ℕ) (i : ℕ) (hi : i < base.length) :
        (xs.foldl step base).getD i 0 = base.getD i 0 := by
      induction xs generalizing base with
      | nil => rfl
      | cons x tail ih =>
        rw [List.foldl_cons, ih (step base x) (by simp [step]; omega)]
        simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
    have keep (i : ℕ) (hi : i < 17) : bank.getD i 0 = seed.getD i 0 :=
      preserve gs seed i hi
    have fixed : emit bank first = 34572 := by
      change bank.getD 15 0 &&& bank.getD 16 0 = 34572
      rw [keep 15 (by decide), keep 16 (by decide), seedVal]
      decide +kernel
    have countHead : (head.filter (·.1)).length = 1 := rfl
    have headInputs : ∀ j : Fin head.length,
        (head.get j).2.1.val < 11 + j.val ∧ (head.get j).2.2.val < 11+j.val := by decide
    have headDirty : ∀ j : Fin head.length, (head.get j).1 = true →
        seed.getD (11+j.val) 0 &&& 1099511562240 ≠ 0 := by decide
    have hlen : head.length = 6 := rfl
    have glen : (head ++ gs).length = 6 + gs.length := by rw [List.length_append, hlen]
    have getHead (i : Fin (head ++ gs).length) (hi : i.val < 6) :
        (head ++ gs).get i = head.get ⟨i.val,hi⟩ := by
      exact List.getElem_append_left (as := head) (bs := gs) hi
    have getRest (i : Fin (head ++ gs).length) (hi : 6 ≤ i.val) :
        (head ++ gs).get i = gs.get ⟨i.val-6,by have := i.isLt; omega⟩ := by
      exact List.getElem_append_right (as := head) (bs := gs) hi
    refine ⟨head ++ gs, first :: ts, ?_⟩
    change (head ++ gs).length + 2 * (first :: ts).length ≤ 22 ∧ first :: ts ≠ [] ∧
      (∀ i : Fin (head ++ gs).length, ((head ++ gs).get i).2.1.val < 11+i.val ∧
        ((head ++ gs).get i).2.2.val < 11+i.val) ∧
      ((head ++ gs).filter (·.1)).length = 2 ∧
      (∀ i : Fin (head ++ gs).length, ((head ++ gs).get i).1 = true →
        ((head ++ gs).foldl step roots).getD (11+i.val) 0 &&& 1099511562240 ≠ 0) ∧
      (∀ p ∈ first :: ts, p.1.val < 11+(head++gs).length ∧ p.2.val < 11+(head++gs).length ∧
        emit ((head ++ gs).foldl step roots) p &&& 1099511562240 = 0) ∧
      (first :: ts).foldl (fun n p => n ||| emit ((head ++ gs).foldl step roots) p) 0 = 65535
    rw [same]
    refine ⟨?_, List.cons_ne_nil _ _, ?_, ?_, ?_, ?_, ?_⟩
    · rw [glen, List.length_cons]
      omega
    · intro i
      by_cases hi : i.val < 6
      · rw [getHead i hi]
        exact headInputs ⟨i.val,hi⟩
      · have hj : i.val-6 < gs.length := by have := i.isLt; omega
        rw [getRest i (by omega)]
        simpa only [show 11+i.val = 17+(i.val-6) by omega] using inputs ⟨i.val-6,hj⟩
    · rw [List.filter_append, List.length_append, countHead, dirtyCount]
    · intro i
      by_cases hi : i.val < 6
      · rw [getHead i hi, keep (11+i.val) (by omega)]
        exact headDirty ⟨i.val,hi⟩
      · have hj : i.val-6 < gs.length := by have := i.isLt; omega
        rw [getRest i (by omega), show 11+i.val = 17+(i.val-6) by omega]
        exact dirty ⟨i.val-6,hj⟩
    · intro p hp
      rw [List.mem_cons] at hp
      rw [glen, show 11 + (6 + gs.length) = 17 + gs.length by omega]
      rcases hp with rfl | hp
      · refine ⟨?_, ?_, ?_⟩
        · change 15 < 17+gs.length
          omega
        · change 16 < 17+gs.length
          omega
        · rw [fixed]
          decide
      · exact clean p hp
    · simpa only [List.foldl_cons, fixed, Nat.zero_or] using covers
  obtain ⟨A, T, budget, hasTop, read, count, dirty, clean, output⟩ := core
  have topRead (p : Fin 32 × Fin 32) (hp : p ∈ T) :=
    And.intro (clean p hp).1 (clean p hp).2.1
  obtain ⟨R, B, layout, onlyOr, back, value⟩ :=
    assemble [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
       26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] A T rfl budget hasTop read topRead
  obtain ⟨countB, partition⟩ :=
    flags [2147418115, 663661903884, 34144976944, 728266375360, 21653750532, 103293914128,
       26322415680, 344922804352, 414195942664, 581968119809, 1065151898146] 1099511562240 A R T B rfl layout onlyOr dirty clean
  refine ⟨B, back, value.trans output, countB.trans count, ?_⟩
  intro i j andI cleanI andJ
  exact cones A R T B layout onlyOr back topRead i j (partition i andI cleanI) andJ
