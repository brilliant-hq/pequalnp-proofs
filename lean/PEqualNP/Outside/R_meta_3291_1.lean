import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3291_1
    (lineBound : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p' l ∧ I p l' ∧ I p' l')) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ 1 →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = true}
        ≤ 10 * C.size)
    (pointBound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = false) →
      Fintype.card {e : Fin N × Fin N // I e.1 e.2 ∧
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = true}
        ≤ 10 * C.size)
    (rereadCore : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
        (C : PEqualNP.CircuitLowerBounds.Circuit) (E F : Finset (Fin N × Fin N)) (j a b : ℕ),
      let wv := PEqualNP.CleanedNonEdge.wireVal (N + N) C;
      let U : Fin N × Fin N → Fin (N + N) → Bool := fun e k =>
        decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2);
      let V1 : Fin N → Fin (N + N) → Bool := fun l =>
        Fin.addCases (fun p => decide (¬ I p l)) (fun k => decide (k = l));
      87 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        Fintype.card {l : Fin N // z (Fin.natAdd N l) = true} ≤ q →
        (¬ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        wv C.output z = false) →
      (∀ e ∈ E, I e.1 e.2 ∧ wv C.output (U e) = true ∧
        ∀ d : Bool, PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N) == d) e.1.val (N + e.2.val) = false) →
      (4513 ≤ C.size ∧ 24 * C.size < E.card ∧ F ⊆ E ∧ j < C.size ∧ 24 < F.card ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.Perm [a, b] ∧
        wv a (fun i => decide (i.val < N)) = false ∧ wv b (fun i => decide (i.val < N)) = true) →
      ∃ e ∈ F, ¬ (wv a (U e) = true ∧ wv b (U e) = true ∧ wv a (V1 e.2) = true ∧ wv b (V1 e.2) = false)) :
    (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (131 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.TopForm.IsAO2 (x2 + x2) x5 → (∀ (x11 : Fin (x2 + x2) → Bool), Fintype.card { x12 : Fin x2 // x11 (Fin.natAdd x2 x12) = Bool.true } ≤ x1 → (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x11 (Fin.castAdd x2 x13) = Bool.true ∧ x11 (Fin.natAdd x2 x14) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x11 = Bool.false) → Fintype.card { x12 : Fin x2 × Fin x2 // x3 x12.1 x12.2 ∧ (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x13 : Fin (x2 + x2)) => Decidable.decide (x13 = Fin.castAdd x2 x12.1 ∨ x13 = Fin.natAdd x2 x12.2)) = Bool.true } ≤ (44 : ℕ) * x5.size) := by
  classical
  intro q N I instI C hq hN hcol huniq hAO hsound
  have noRectangle : ∀ p r l m : Fin N, p ≠ r → l ≠ m →
      ¬ (I p l ∧ I r l ∧ I p m ∧ I r m) := by
    rintro p r l m hpr hlm ⟨hpl, hrl, hpm, hrm⟩
    obtain ⟨_, _, uniqueLine⟩ := huniq p r hpr
    exact hlm ((uniqueLine l ⟨hpl, hrl⟩).trans (uniqueLine m ⟨hpm, hrm⟩).symm)
  have hL := lineBound N I C noRectangle hAO (fun z hz => hsound z (hz.trans (by omega)))
  have hP := pointBound q N I C (by omega) hN hcol huniq hAO hsound
  let U : Fin N × Fin N → Fin (N + N) → Bool :=
    fun e k => decide (k = Fin.castAdd N e.1 ∨ k = Fin.natAdd N e.2)
  let readLine (e : Fin N × Fin N) :=
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val)
  let readPoint (e : Fin N × Fin N) :=
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val)
  let hits := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (U e) = true
  let lines := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ readLine e = true
  let points := Finset.univ.filter fun e : Fin N × Fin N => I e.1 e.2 ∧ readPoint e = true
  let E := Finset.univ.filter fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (U e) = true ∧
    readLine e = false ∧ readPoint e = false
  have hEcard : E.card ≤ 24 * C.size := by
    by_contra hbig
    have hgt : 24 * C.size < E.card := Nat.lt_of_not_ge hbig
    have hEne : E.Nonempty := Finset.card_pos.mp (by omega)
    have hEmem : ∀ e ∈ E, I e.1 e.2 ∧
        PEqualNP.MetaComplexity.circuitFun (N + N) C (U e) = true ∧
        readLine e = false ∧ readPoint e = false := fun e he => (Finset.mem_filter.mp he).2
    have hApart (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have hSingleOff (v : Fin (N + N)) :
        PEqualNP.MetaComplexity.circuitFun (N + N) C (fun i => decide (i = v)) = false := by
      apply hsound
      · rw [Fintype.card_subtype]
        have hle1 : (Finset.univ.filter fun l : Fin N => decide (Fin.natAdd N l = v) = true).card ≤ 1 :=
          Finset.card_le_one.mpr fun a ha b hb => by
            have ha' : Fin.natAdd N a = v := of_decide_eq_true (Finset.mem_filter.mp ha).2
            have hb' : Fin.natAdd N b = v := of_decide_eq_true (Finset.mem_filter.mp hb).2
            exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val (ha'.trans hb'.symm)))
        omega
      · rintro ⟨p, l, _, hp, hl⟩
        exact hApart p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)

    let stepW : List Bool → PEqualNP.CircuitLowerBounds.Gate → Bool :=
      fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)
    let runW : List PEqualNP.CircuitLowerBounds.Gate → List Bool → List Bool :=
      fun gs init => gs.foldl (fun w g => w ++ [stepW w g]) init
    have hrunLen : ∀ gs init, (runW gs init).length = init.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro init; simp [runW]
      | cons g rest ih =>
        intro init
        change (runW rest (init ++ [stepW init g])).length = _
        rw [ih, List.length_append, List.length_singleton, List.length_cons]
        omega
    have hrunPrefix : ∀ gs init i, i < init.length →
        (runW gs init).getD i false = init.getD i false := by
      intro gs
      induction gs with
      | nil => intro init i _; rfl
      | cons g rest ih =>
        intro init i hi
        change (runW rest (init ++ [stepW init g])).getD i false = _
        rw [ih _ i (by simp; omega), List.getD_append _ _ _ _ hi]
    have hwireLt : ∀ (x : Fin (N + N) → Bool) (i : Fin (N + N)),
        PEqualNP.CleanedNonEdge.wireVal (N + N) C i.val x = x i := by
      intro x i
      change (runW C.gates (List.ofFn x)).getD i.val false = x i
      rw [hrunPrefix C.gates (List.ofFn x) i.val (by simp), List.getD_eq_getElem?_getD,
        List.getElem?_ofFn]
      simp [i.isLt]
    have hwireGe : ∀ (x : Fin (N + N) → Bool) (w : ℕ), N + N + C.size ≤ w →
        PEqualNP.CleanedNonEdge.wireVal (N + N) C w x = false := by
      intro x w hw
      change (runW C.gates (List.ofFn x)).getD w false = false
      apply List.getD_eq_default
      rw [hrunLen, List.length_ofFn]
      exact hw
    have hgateProps : ∀ j < C.size,
        ((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs =
          [PEqualNP.TopForm.opnd C j 0, PEqualNP.TopForm.opnd C j 1] ∧
        PEqualNP.TopForm.opnd C j 0 < N + N + j ∧
        PEqualNP.TopForm.opnd C j 1 < N + N + j := by
      intro j hj
      have hj' : j < C.gates.length := hj
      have hgateEq : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
        rw [List.getD_eq_getElem _ _ hj']
      have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj'
      have hop := hAO.1 C.gates[j] hmem
      have hlen : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2 := by
        rw [hgateEq]; exact hAO.2.2 C.gates[j] hmem
      obtain ⟨ia, ib, hiab⟩ := List.length_eq_two.mp hlen
      have ha0 : PEqualNP.TopForm.opnd C j 0 = ia := by
        change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0 = ia
        rw [hiab]; rfl
      have hb1 : PEqualNP.TopForm.opnd C j 1 = ib := by
        change (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0 = ib
        rw [hiab]; rfl
      have hback0 : PEqualNP.TopForm.opnd C j 0 < N + N + j := by
        rw [ha0]
        exact hAO.2.1 j hj' ia (by rw [hiab]; simp)
      have hback1 : PEqualNP.TopForm.opnd C j 1 < N + N + j := by
        rw [hb1]
        exact hAO.2.1 j hj' ib (by rw [hiab]; simp)
      have hinpEq : (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs =
          [PEqualNP.TopForm.opnd C j 0, PEqualNP.TopForm.opnd C j 1] := by
        rw [hiab, ha0, hb1]
      refine ⟨?_, hinpEq, hback0, hback1⟩
      rw [hgateEq]; exact hop
    have hwireGate : ∀ (x : Fin (N + N) → Bool) (j : ℕ) (hj : j < C.size),
        PEqualNP.CleanedNonEdge.wireVal (N + N) C (N + N + j) x =
          (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op.eval
            [PEqualNP.CleanedNonEdge.wireVal (N + N) C (PEqualNP.TopForm.opnd C j 0) x,
             PEqualNP.CleanedNonEdge.wireVal (N + N) C (PEqualNP.TopForm.opnd C j 1) x] := by
      intro x j hj
      have hj' : j < C.gates.length := hj
      have hgateEq : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
        rw [List.getD_eq_getElem _ _ hj']
      have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
        rw [List.cons_getElem_drop_succ (l := C.gates) (n := j) (h := hj'), List.take_append_drop]
      let pre := runW (C.gates.take j) (List.ofFn x)
      have hpreLen : pre.length = N + N + j := by
        rw [hrunLen, List.length_ofFn, List.length_take, Nat.min_eq_left hj'.le]
      have hrunSplit : runW C.gates (List.ofFn x) =
          runW (C.gates.drop (j + 1)) (pre ++ [stepW pre C.gates[j]]) := by
        change C.gates.foldl _ (List.ofFn x) = _
        conv_lhs => rw [hsplit]
        rw [List.foldl_append]
        rfl
      have hpreEq : ∀ i < N + N + j,
          (runW C.gates (List.ofFn x)).getD i false = pre.getD i false := by
        intro i hi
        rw [hrunSplit, hrunPrefix _ _ i (by simp [hpreLen]; omega),
          List.getD_append _ _ _ _ (by omega)]
      have htop : PEqualNP.CleanedNonEdge.wireVal (N + N) C (N + N + j) x = stepW pre C.gates[j] := by
        change (runW C.gates (List.ofFn x)).getD (N + N + j) false = _
        rw [hrunSplit, hrunPrefix _ _ (N + N + j) (by simp [hpreLen]),
          List.getD_append_right _ _ _ _ (by omega)]
        have hsub : N + N + j - pre.length = 0 := by omega
        rw [hsub]; rfl
      rw [htop]
      obtain ⟨_, hinpEq, hb0, hb1⟩ := hgateProps j hj
      dsimp only [stepW]
      rw [← hgateEq, hinpEq]
      simp only [List.map_cons, List.map_nil]
      rw [← hpreEq _ hb0, ← hpreEq _ hb1]
      rfl

    let P := E.image Prod.fst
    let L := E.image Prod.snd
    have houtLt : C.output < N + N + C.size := by
      by_contra hge
      obtain ⟨e, he⟩ := hEne
      have hacc := (hEmem e he).2.1
      have hff := hwireGe (U e) C.output (Nat.le_of_not_lt hge)
      change PEqualNP.MetaComplexity.circuitFun (N + N) C (U e) = false at hff
      rw [hacc] at hff
      exact Bool.false_ne_true hff.symm
    have hsupport : P.card + L.card ≤ C.size + 1 := by
      let S : Finset (Fin (N + N)) := P.image (Fin.castAdd N) ∪ L.image (Fin.natAdd N)
      have hScard : S.card = P.card + L.card := by
        rw [Finset.card_union_of_disjoint,
          Finset.card_image_of_injective _ (Fin.castAdd_injective N N),
          Finset.card_image_of_injective _ (Fin.natAdd_injective N N)]
        rw [Finset.disjoint_left]
        intro v hp hl
        obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hl
        exact hApart p l hl.symm

      let reachStep : List (Finset (Fin (N + N)) × Finset ℕ) → PEqualNP.CircuitLowerBounds.Gate →
          List (Finset (Fin (N + N)) × Finset ℕ) :=
        fun acc g =>
          let j := acc.length - (N + N)
          let a := g.inputs.getD 0 0
          let b := g.inputs.getD 1 0
          let pa := acc.getD a (∅, ∅)
          let pb := acc.getD b (∅, ∅)
          acc ++ [(pa.1 ∪ pb.1, insert j (pa.2 ∪ pb.2))]
      let initReach : List (Finset (Fin (N + N)) × Finset ℕ) :=
        (List.finRange (N + N)).map fun i => ({i}, ∅)
      let allReach : List (Finset (Fin (N + N)) × Finset ℕ) := C.gates.foldl reachStep initReach
      have hrLen : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
          (init : List (Finset (Fin (N + N)) × Finset ℕ)),
          (gs.foldl reachStep init).length = init.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro init; simp
        | cons g rest ih =>
          intro init
          rw [List.foldl_cons, ih, List.length_append, List.length_singleton, List.length_cons]
          omega
      have hrPrefix : ∀ (gs : List PEqualNP.CircuitLowerBounds.Gate)
          (init : List (Finset (Fin (N + N)) × Finset ℕ)) w,
          w < init.length → (gs.foldl reachStep init).getD w (∅, ∅) = init.getD w (∅, ∅) := by
        intro gs
        induction gs with
        | nil => intro init w _; rfl
        | cons g rest ih =>
          intro init w hw
          rw [List.foldl_cons, ih _ w (by rw [List.length_append, List.length_singleton]; omega),
            List.getD_append _ _ _ _ hw]
      have hallLen : allReach.length = N + N + C.size := by
        change (C.gates.foldl reachStep initReach).length = _
        rw [hrLen, List.length_map, List.length_finRange]; rfl
      have hreachIn : ∀ (i : Fin (N + N)),
          allReach.getD i.val (∅, ∅) = ({i}, ∅) := by
        intro i
        change (C.gates.foldl reachStep initReach).getD i.val (∅, ∅) = ({i}, ∅)
        rw [hrPrefix _ _ i.val (by simp [initReach])]
        simp [initReach, List.getD_eq_getElem?_getD, i.isLt]
      have hreachGate : ∀ j < C.size,
          let a := PEqualNP.TopForm.opnd C j 0
          let b := PEqualNP.TopForm.opnd C j 1
          let pa := allReach.getD a (∅, ∅)
          let pb := allReach.getD b (∅, ∅)
          allReach.getD (N + N + j) (∅, ∅) = (pa.1 ∪ pb.1, insert j (pa.2 ∪ pb.2)) := by
        intro j hj
        have hj' : j < C.gates.length := hj
        have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
          rw [List.cons_getElem_drop_succ (l := C.gates) (n := j) (h := hj'), List.take_append_drop]
        let pre := (C.gates.take j).foldl reachStep initReach
        have hpreLen : pre.length = N + N + j := by
          rw [hrLen, List.length_map, List.length_finRange, List.length_take, Nat.min_eq_left hj'.le]
        have hallSplit : allReach = (C.gates.drop (j + 1)).foldl reachStep
            (reachStep pre C.gates[j]) := by
          change C.gates.foldl reachStep initReach = _
          conv_lhs => rw [hsplit]
          rw [List.foldl_append]; rfl
        have hpreEq : ∀ w < N + N + j, allReach.getD w (∅, ∅) = pre.getD w (∅, ∅) := by
          intro w hw
          rw [hallSplit, hrPrefix _ _ w (by simp [reachStep, hpreLen]; omega),
            List.getD_append _ _ _ _ (by omega)]
        have htop : allReach.getD (N + N + j) (∅, ∅) =
            ((pre.getD (C.gates[j].inputs.getD 0 0) (∅, ∅)).1 ∪
              (pre.getD (C.gates[j].inputs.getD 1 0) (∅, ∅)).1,
             insert j ((pre.getD (C.gates[j].inputs.getD 0 0) (∅, ∅)).2 ∪
              (pre.getD (C.gates[j].inputs.getD 1 0) (∅, ∅)).2)) := by
          rw [hallSplit, hrPrefix _ _ (N + N + j) (by simp [reachStep, hpreLen]),
            List.getD_append_right _ _ _ _ (by omega)]
          have hsub : N + N + j - pre.length = 0 := by omega
          have hsubj : pre.length - (N + N) = j := by omega
          simp only [hsub, hsubj]
          rfl
        obtain ⟨_, hinpEq, hb0, hb1⟩ := hgateProps j hj
        have hgateEq : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
          change C.gates.getD j ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩ = C.gates[j]
          rw [List.getD_eq_getElem _ _ hj']
        rw [htop]
        have haEq : C.gates[j].inputs.getD 0 0 = PEqualNP.TopForm.opnd C j 0 := by
          change C.gates[j].inputs.getD 0 0 = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 0 0
          rw [hgateEq]
        have hbEq : C.gates[j].inputs.getD 1 0 = PEqualNP.TopForm.opnd C j 1 := by
          change C.gates[j].inputs.getD 1 0 = (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.getD 1 0
          rw [hgateEq]
        rw [haEq, hbEq, ← hpreEq _ hb0, ← hpreEq _ hb1]
      have hagree : ∀ (w : ℕ), w < N + N + C.size → ∀ (x y : Fin (N + N) → Bool),
          (∀ v ∈ (allReach.getD w (∅, ∅)).1, x v = y v) →
          PEqualNP.CleanedNonEdge.wireVal (N + N) C w x =
            PEqualNP.CleanedNonEdge.wireVal (N + N) C w y := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hw x y hxy
          by_cases hwn : w < N + N
          · let i : Fin (N + N) := ⟨w, hwn⟩
            rw [show w = i.val from rfl, hwireLt x i, hwireLt y i]
            apply hxy
            rw [hreachIn i]
            exact Finset.mem_singleton_self i
          · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
            have hj : j < C.size := by omega
            obtain ⟨_, _, hb0, hb1⟩ := hgateProps j hj
            have hrg := hreachGate j hj
            dsimp only at hrg
            rw [hrg] at hxy
            rw [hwireGate x j hj, hwireGate y j hj]
            have h0 := ih _ hb0 (by omega) x y (fun v hv => hxy v (Finset.mem_union_left _ hv))
            have h1 := ih _ hb1 (by omega) x y (fun v hv => hxy v (Finset.mem_union_right _ hv))
            rw [h0, h1]
      have hclosed : ∀ (w : ℕ), w < N + N + C.size →
          (∀ g ∈ (allReach.getD w (∅, ∅)).2, g < C.size ∧ N + N + g ≤ w) ∧
          (∀ v ∈ (allReach.getD w (∅, ∅)).1,
            v.val = w ∨ ∃ g ∈ (allReach.getD w (∅, ∅)).2,
              v.val = PEqualNP.TopForm.opnd C g 0 ∨ v.val = PEqualNP.TopForm.opnd C g 1) ∧
          (∀ g ∈ (allReach.getD w (∅, ∅)).2,
            N + N + g = w ∨ ∃ g' ∈ (allReach.getD w (∅, ∅)).2,
              N + N + g = PEqualNP.TopForm.opnd C g' 0 ∨ N + N + g = PEqualNP.TopForm.opnd C g' 1) := by
        intro w
        induction w using Nat.strong_induction_on with
        | _ w ih =>
          intro hw
          by_cases hwn : w < N + N
          · let i : Fin (N + N) := ⟨w, hwn⟩
            rw [show w = i.val from rfl, hreachIn i]
            refine ⟨fun g hg => (Finset.notMem_empty g hg).elim, ?_, fun g hg => (Finset.notMem_empty g hg).elim⟩
            intro v hv
            rw [Finset.mem_singleton.mp hv]
            exact Or.inl rfl
          · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
            have hj : j < C.size := by omega
            obtain ⟨_, _, hb0, hb1⟩ := hgateProps j hj
            have hrg := hreachGate j hj
            dsimp only at hrg
            obtain ⟨iha1, iha2, iha3⟩ := ih _ hb0 (by omega)
            obtain ⟨ihb1, ihb2, ihb3⟩ := ih _ hb1 (by omega)
            rw [hrg]
            refine ⟨?_, ?_, ?_⟩
            · intro g hg
              rcases Finset.mem_insert.mp hg with rfl | hg'
              · exact ⟨hj, le_refl _⟩
              · rcases Finset.mem_union.mp hg' with ha | hb
                · obtain ⟨h1, h2⟩ := iha1 g ha; exact ⟨h1, by omega⟩
                · obtain ⟨h1, h2⟩ := ihb1 g hb; exact ⟨h1, by omega⟩
            · intro v hv
              rcases Finset.mem_union.mp hv with ha | hb
              · rcases iha2 v ha with heq | ⟨g, hg, hread⟩
                · exact Or.inr ⟨j, Finset.mem_insert_self j _, Or.inl heq⟩
                · exact Or.inr ⟨g, Finset.mem_insert_of_mem (Finset.mem_union_left _ hg), hread⟩
              · rcases ihb2 v hb with heq | ⟨g, hg, hread⟩
                · exact Or.inr ⟨j, Finset.mem_insert_self j _, Or.inr heq⟩
                · exact Or.inr ⟨g, Finset.mem_insert_of_mem (Finset.mem_union_right _ hg), hread⟩
            · intro g hg
              rcases Finset.mem_insert.mp hg with rfl | hg'
              · exact Or.inl rfl
              · rcases Finset.mem_union.mp hg' with ha | hb
                · rcases iha3 g ha with heq | ⟨g', hg', hread⟩
                  · exact Or.inr ⟨j, Finset.mem_insert_self j _, Or.inl heq⟩
                  · exact Or.inr ⟨g', Finset.mem_insert_of_mem (Finset.mem_union_left _ hg'), hread⟩
                · rcases ihb3 g hb with heq | ⟨g', hg', hread⟩
                  · exact Or.inr ⟨j, Finset.mem_insert_self j _, Or.inr heq⟩
                  · exact Or.inr ⟨g', Finset.mem_insert_of_mem (Finset.mem_union_right _ hg'), hread⟩
      have hreachCard : ∀ w < N + N + C.size,
          (allReach.getD w (∅, ∅)).1.card ≤ (allReach.getD w (∅, ∅)).2.card + 1 := by
        intro w hw
        by_cases hwn : w < N + N
        · let i : Fin (N + N) := ⟨w, hwn⟩
          rw [show w = i.val from rfl, hreachIn i]
          simp
        · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
          have hj : j < C.size := by omega
          have hrg := hreachGate j hj
          dsimp only at hrg
          have hjmem : j ∈ (allReach.getD (N + N + j) (∅, ∅)).2 := by
            rw [hrg]; exact Finset.mem_insert_self j _
          obtain ⟨hsub, hvin, hgin⟩ := hclosed (N + N + j) hw
          let R := (allReach.getD (N + N + j) (∅, ∅)).1
          let G := (allReach.getD (N + N + j) (∅, ∅)).2
          change R.card ≤ G.card + 1
          let W := R.image Fin.val ∪ (G.erase j).image (fun g => N + N + g)
          have hdisj : Disjoint (R.image Fin.val) ((G.erase j).image (fun g => N + N + g)) := by
            rw [Finset.disjoint_left]
            intro x hx hg
            obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
            obtain ⟨g, _, hgv⟩ := Finset.mem_image.mp hg
            omega
          have hGpos : 0 < G.card := Finset.card_pos.mpr ⟨j, hjmem⟩
          have hWcard : W.card = R.card + (G.card - 1) := by
            rw [Finset.card_union_of_disjoint hdisj,
              Finset.card_image_of_injective _ Fin.val_injective,
              Finset.card_image_of_injective _ (fun _ _ h => Nat.add_left_cancel h),
              Finset.card_erase_of_mem hjmem]
          let slots : Finset ℕ := (G ×ˢ ({0, 1} : Finset (Fin 2))).image
            (fun p => PEqualNP.TopForm.opnd C p.1 p.2)
          have hWsub : W ⊆ slots := by
            intro x hx
            rcases Finset.mem_union.mp hx with hv | hg
            · obtain ⟨v, hvR, rfl⟩ := Finset.mem_image.mp hv
              rcases hvin v hvR with heq | ⟨g, hgG, h0 | h1⟩
              · omega
              · exact Finset.mem_image.mpr ⟨(g, 0), Finset.mem_product.mpr ⟨hgG, by simp⟩, h0.symm⟩
              · exact Finset.mem_image.mpr ⟨(g, 1), Finset.mem_product.mpr ⟨hgG, by simp⟩, h1.symm⟩
            · obtain ⟨g, hgEr, rfl⟩ := Finset.mem_image.mp hg
              obtain ⟨hne, hgG⟩ := Finset.mem_erase.mp hgEr
              rcases hgin g hgG with heq | ⟨g', hg'G, h0 | h1⟩
              · exact (hne (Nat.add_left_cancel heq)).elim
              · exact Finset.mem_image.mpr ⟨(g', 0), Finset.mem_product.mpr ⟨hg'G, by simp⟩, h0.symm⟩
              · exact Finset.mem_image.mpr ⟨(g', 1), Finset.mem_product.mpr ⟨hg'G, by simp⟩, h1.symm⟩
          have hslotsCard : slots.card ≤ 2 * G.card := by
            calc slots.card
                ≤ (G ×ˢ ({0, 1} : Finset (Fin 2))).card := Finset.card_image_le
              _ = G.card * 2 := by rw [Finset.card_product]; simp
              _ = 2 * G.card := mul_comm _ _
          have hWle := (Finset.card_le_card hWsub).trans hslotsCard
          omega
      have hSsub : S ⊆ (allReach.getD C.output (∅, ∅)).1 := by
        intro v hv
        have hdiff : ∃ u : Fin (N + N),
            PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = u ∨ k = v)) = true ∧
            PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = u)) = false := by
          rcases Finset.mem_union.mp hv with hp | hl
          · obtain ⟨p, hpP, rfl⟩ := Finset.mem_image.mp hp
            obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp hpP
            refine ⟨Fin.natAdd N e.2, ?_, hSingleOff _⟩
            simpa only [U, or_comm] using (hEmem e heE).2.1
          · obtain ⟨l, hlL, rfl⟩ := Finset.mem_image.mp hl
            obtain ⟨e, heE, rfl⟩ := Finset.mem_image.mp hlL
            exact ⟨Fin.castAdd N e.1, (hEmem e heE).2.1, hSingleOff _⟩
        obtain ⟨u, htrue, hfalse⟩ := hdiff
        by_contra hnot
        have hEq := hagree C.output houtLt
          (fun k => decide (k = u ∨ k = v)) (fun k => decide (k = u))
          (fun w hw => by
            have hne : w ≠ v := fun hwe => hnot (hwe ▸ hw)
            simp [hne])
        change PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = u ∨ k = v)) =
          PEqualNP.MetaComplexity.circuitFun (N + N) C (fun k => decide (k = u)) at hEq
        rw [htrue, hfalse] at hEq
        exact Bool.false_ne_true hEq.symm
      have hGsub : (allReach.getD C.output (∅, ∅)).2 ⊆ Finset.range C.size := by
        intro g hg
        exact Finset.mem_range.mpr ((hclosed C.output houtLt).1 g hg).1
      have h1 := Finset.card_le_card hSsub
      have h2 := hreachCard C.output houtLt
      have h3 := (Finset.card_le_card hGsub).trans (by rw [Finset.card_range])
      omega

    have hsmall : min P.card L.card ≤ 2256 → E.card ≤ 24 * C.size := by
      intro hmin
      have hquad : ∀ d : ℕ, 94 * d ≤ 2256 + (d * d - d) := by
        intro d
        have hd : d ≤ d * d := Nat.le_mul_self d
        zify [hd]
        rcases (show (d : ℤ) ≤ 47 ∨ 48 ≤ (d : ℤ) by omega) with h | h
        · nlinarith [mul_nonneg (show (0 : ℤ) ≤ 47 - d by omega) (show (0 : ℤ) ≤ 48 - d by omega)]
        · nlinarith [mul_nonneg (show (0 : ℤ) ≤ d - 47 by omega) (show (0 : ℤ) ≤ d - 48 by omega)]
      have hweighted : ∀ (A B : Type) [Fintype A] [Fintype B] (J : A → B → Prop) [DecidableRel J],
          (∀ a a' b b', a ≠ a' → J a b → J a' b → J a b' → J a' b' → b = b') →
          94 * Fintype.card {e : A × B // J e.1 e.2} ≤
            2256 * Fintype.card B + Fintype.card A * (Fintype.card A - 1) := by
        intro A B _ _ J _ hJuniq
        let nbr (b : B) : Finset A := Finset.univ.filter fun a => J a b
        have hedge : Fintype.card {e : A × B // J e.1 e.2} = ∑ b : B, (nbr b).card := by
          rw [Fintype.card_subtype]
          have hpart : (Finset.univ : Finset (A × B)).filter (fun e => J e.1 e.2) =
              Finset.univ.biUnion (fun b : B => (nbr b).map ⟨fun a => (a, b),
                fun _ _ h => congrArg Prod.fst h⟩) := by
            ext e
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
              Finset.mem_map, nbr]
            constructor
            · intro h; exact ⟨e.2, e.1, h, rfl⟩
            · rintro ⟨b, a, ha, rfl⟩; exact ha
          rw [hpart, Finset.card_biUnion]
          · simp [Finset.card_map]
          · intro b _ b' _ hne
            apply Finset.disjoint_left.mpr
            intro e hb hb'
            obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hb
            obtain ⟨a', _, heq⟩ := Finset.mem_map.mp hb'
            exact hne (congrArg Prod.snd heq).symm
        have hpairDisj : ((Finset.univ : Finset B) : Set B).PairwiseDisjoint
            (fun b => (nbr b).offDiag) := by
          intro b _ b' _ hne
          apply Finset.disjoint_left.mpr
          intro p hp hp'
          obtain ⟨ha, ha', hnea⟩ := Finset.mem_offDiag.mp hp
          obtain ⟨hb, hb', _⟩ := Finset.mem_offDiag.mp hp'
          exact hne (hJuniq _ _ b b' hnea
            (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp ha').2
            (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hb').2)
        have hpairSum : (∑ b : B, (nbr b).offDiag.card) ≤
            Fintype.card A * Fintype.card A - Fintype.card A := by
          have hsub : Finset.univ.biUnion (fun b : B => (nbr b).offDiag) ⊆
              (Finset.univ : Finset A).offDiag := by
            intro p hp
            obtain ⟨b, _, hb⟩ := Finset.mem_biUnion.mp hp
            exact Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _,
              (Finset.mem_offDiag.mp hb).2.2⟩
          have hle := Finset.card_le_card hsub
          simpa only [Finset.card_biUnion hpairDisj, Finset.offDiag_card, Finset.card_univ] using hle
        have hsum : (∑ b : B, 94 * (nbr b).card) ≤ ∑ b : B, (2256 + (nbr b).offDiag.card) := by
          refine Finset.sum_le_sum fun b _ => ?_
          rw [Finset.offDiag_card]
          exact hquad (nbr b).card
        simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, Nat.cast_id] at hsum
        rw [hedge, Nat.mul_sub_left_distrib, Nat.mul_one]
        omega
      have hPpos : 0 < P.card := by
        obtain ⟨e, he⟩ := hEne
        exact Finset.card_pos.mpr ⟨e.1, Finset.mem_image_of_mem _ he⟩
      have hLpos : 0 < L.card := by
        obtain ⟨e, he⟩ := hEne
        exact Finset.card_pos.mpr ⟨e.2, Finset.mem_image_of_mem _ he⟩
      rcases min_le_iff.mp hmin with hP2256 | hL2256
      · have hw := hweighted P L (fun p l => (p.val, l.val) ∈ E) (by
          intro p p' l l' hne h1 h2 h3 h4
          apply Subtype.ext
          by_contra hlne
          exact noRectangle p.val p'.val l.val l'.val (fun h => hne (Subtype.ext h)) hlne
            ⟨(hEmem _ h1).1, (hEmem _ h2).1, (hEmem _ h3).1, (hEmem _ h4).1⟩)
        have hbij : E.card ≤ Fintype.card {e : P × L // (e.1.val, e.2.val) ∈ E} := by
          rw [← Fintype.card_coe E]
          refine Fintype.card_le_of_injective
            (fun e => ⟨(⟨e.val.1, Finset.mem_image_of_mem _ e.property⟩,
              ⟨e.val.2, Finset.mem_image_of_mem _ e.property⟩), e.property⟩) ?_
          intro a b hab
          exact Subtype.ext (Prod.ext (congrArg (fun x => x.val.1.val) hab)
            (congrArg (fun x => x.val.2.val) hab))
        simp only [Fintype.card_coe] at hw
        have hmul : P.card * (P.card - 1) ≤ 2256 * (P.card - 1) :=
          Nat.mul_le_mul_right _ hP2256
        omega
      · have hw := hweighted L P (fun l p => (p.val, l.val) ∈ E) (by
          intro l l' p p' hne h1 h2 h3 h4
          apply Subtype.ext
          by_contra hpne
          exact noRectangle p.val p'.val l.val l'.val hpne (fun h => hne (Subtype.ext h))
            ⟨(hEmem _ h1).1, (hEmem _ h3).1, (hEmem _ h2).1, (hEmem _ h4).1⟩)
        have hbij : E.card ≤ Fintype.card {e : L × P // (e.2.val, e.1.val) ∈ E} := by
          rw [← Fintype.card_coe E]
          refine Fintype.card_le_of_injective
            (fun e => ⟨(⟨e.val.2, Finset.mem_image_of_mem _ e.property⟩,
              ⟨e.val.1, Finset.mem_image_of_mem _ e.property⟩), e.property⟩) ?_
          intro a b hab
          exact Subtype.ext (Prod.ext (congrArg (fun x => x.val.2.val) hab)
            (congrArg (fun x => x.val.1.val) hab))
        simp only [Fintype.card_coe] at hw
        have hmul : L.card * (L.card - 1) ≤ 2256 * (L.card - 1) :=
          Nat.mul_le_mul_right _ hL2256
        omega
    have hPbig : 2256 < P.card := by
      by_contra hle
      exact hbig (hsmall (le_trans (min_le_left _ _) (Nat.le_of_not_lt hle)))
    have hLbig : 2256 < L.card := by
      by_contra hle
      exact hbig (hsmall (le_trans (min_le_right _ _) (Nat.le_of_not_lt hle)))
    have hSizeBig : 4513 ≤ C.size := by omega
    have hLineDeg : 24 * C.size < L.card * (q + 1) := by
      have hle : E.card ≤ L.card * (q + 1) := by
        calc E.card
            = Fintype.card {e : Fin N × Fin N // e ∈ E} := (Fintype.card_coe E).symm
          _ ≤ Fintype.card (Σ l : L, {p : Fin N // I p l.val}) := by
              refine Fintype.card_le_of_injective
                (fun e => ⟨⟨e.val.2, Finset.mem_image_of_mem _ e.property⟩,
                  ⟨e.val.1, (hEmem _ e.property).1⟩⟩) ?_
              intro a b hab
              exact Subtype.ext (Prod.ext (congrArg (fun x => x.2.val) hab)
                (congrArg (fun x => x.1.val) hab))
          _ = L.card * (q + 1) := by simp [Fintype.card_sigma, hcol]
      omega

    let wv := PEqualNP.CleanedNonEdge.wireVal (N + N) C
    let V : Finset (Fin N) → Fin (N + N) → Bool := fun S => Fin.addCases
      (fun p => decide (∀ l ∈ S, ¬ I p l)) (fun l => decide (l ∈ S))
    have hVfalse : ∀ S : Finset (Fin N), S.card ≤ q →
        PEqualNP.MetaComplexity.circuitFun (N + N) C (V S) = false := by
      intro S hS
      apply hsound (V S)
      · rw [Fintype.card_subtype]
        simpa only [V, Fin.addCases_right, decide_eq_true_eq, Finset.filter_mem_eq_inter,
          Finset.univ_inter] using hS
      · rintro ⟨p, l, hpl, hp, hl⟩
        simp only [V, Fin.addCases_left, Fin.addCases_right, decide_eq_true_eq] at hp hl
        exact hp l hl hpl
    have hV0 : wv C.output (V ∅) = false := hVfalse ∅ (by simp)
    have hVs : ∀ l : Fin N, wv C.output (V {l}) = false := fun l =>
      hVfalse {l} (by simp; omega)
    let both : ℕ → Fin N × Fin N → Prop := fun k e =>
      wv k (U e) = true ∧ wv k (V ∅) = false ∧ wv k (V {e.2}) = false
    have hbothOut : ∀ e ∈ E, both C.output e := fun e he =>
      ⟨(hEmem e he).2.1, hV0, hVs e.2⟩
    have hnoLeaf : ∀ k < N + N, ∀ e ∈ E, ¬ both k e := by
      intro k hk e _ hboth
      obtain ⟨hU, h0, h1⟩ := hboth
      let i : Fin (N + N) := ⟨k, hk⟩
      change PEqualNP.CleanedNonEdge.wireVal (N + N) C i.val (U e) = true at hU
      change PEqualNP.CleanedNonEdge.wireVal (N + N) C i.val (V ∅) = false at h0
      change PEqualNP.CleanedNonEdge.wireVal (N + N) C i.val (V {e.2}) = false at h1
      rw [hwireLt] at hU
      rw [hwireLt] at h0
      rw [hwireLt] at h1
      by_cases hkn : k < N
      · let p : Fin N := ⟨k, hkn⟩
        have hi : i = Fin.castAdd N p := Fin.ext rfl
        rw [hi] at h0
        simp only [V, Fin.addCases_left, Finset.notMem_empty, IsEmpty.forall_iff,
          implies_true, decide_true] at h0
        exact Bool.noConfusion h0
      · let l : Fin N := ⟨k - N, by omega⟩
        have hi : i = Fin.natAdd N l := Fin.ext (by simp [i, l]; omega)
        rw [hi] at hU h1
        have hU1 : Fin.natAdd N l ≠ Fin.castAdd N e.1 := (hApart e.1 l).symm
        have hU2 : (Fin.natAdd N l = Fin.natAdd N e.2) ↔ l = e.2 :=
          ⟨fun h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h)), congrArg (Fin.natAdd N)⟩
        have hUl : U e (Fin.natAdd N l) = decide (l = e.2) := by
          simp only [U, hU1, hU2, false_or]
        rw [hUl, decide_eq_true_eq] at hU
        rw [hU] at h1
        simp only [V, Fin.addCases_right, Finset.mem_singleton_self, decide_true] at h1
        exact Bool.noConfusion h1
    have hexGate : ∀ e ∈ E, ∃ j : Fin C.size,
        both (N + N + j.val) e ∧ ∀ k < N + N + j.val, ¬ both k e := by
      intro e he
      have hex : ∃ k, both k e := ⟨C.output, hbothOut e he⟩
      let k0 := Nat.find hex
      have hk0 : both k0 e := Nat.find_spec hex
      have hmin : ∀ k < k0, ¬ both k e := fun k hk => Nat.find_min hex hk
      have hk0le : k0 ≤ C.output := Nat.find_min' hex (hbothOut e he)
      have hk0ge : N + N ≤ k0 := by
        by_contra hlt
        exact hnoLeaf k0 (Nat.lt_of_not_le hlt) e he hk0
      refine ⟨⟨k0 - (N + N), by omega⟩, ?_, ?_⟩
      · simpa only [Nat.add_sub_cancel' hk0ge] using hk0
      · intro k hk
        dsimp only at hk
        exact hmin k (by omega)
    let firstGate : Fin N × Fin N → Fin C.size := fun e =>
      if he : e ∈ E then Classical.choose (hexGate e he) else ⟨0, by omega⟩
    have hsumE : E.card = ∑ j : Fin C.size, (E.filter fun e => firstGate e = j).card := by
      have hpart : E = Finset.univ.biUnion (fun j : Fin C.size => E.filter fun e => firstGate e = j) := by
        ext e
        simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
        constructor
        · intro he; exact ⟨firstGate e, he, rfl⟩
        · rintro ⟨_, he, _⟩; exact he
      conv_lhs => rw [hpart]
      rw [Finset.card_biUnion]
      intro j _ j' _ hne
      apply Finset.disjoint_left.mpr
      intro e hj hj'
      exact hne ((Finset.mem_filter.mp hj).2.symm.trans (Finset.mem_filter.mp hj').2)
    have hpigeon : ∃ j : Fin C.size, 24 < (E.filter fun e => firstGate e = j).card := by
      by_contra hnone
      push Not at hnone
      have hle : E.card ≤ 24 * C.size := by
        rw [hsumE]
        calc (∑ j : Fin C.size, (E.filter fun e => firstGate e = j).card)
            ≤ ∑ _ : Fin C.size, 24 := Finset.sum_le_sum fun j _ => hnone j
          _ = 24 * C.size := by simp [Finset.sum_const, mul_comm]
      omega
    obtain ⟨j, hj24⟩ := hpigeon
    let F := E.filter fun e => firstGate e = j
    have hFsub : F ⊆ E := Finset.filter_subset _ _
    have hFne : F.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hj24)
    have hFspec : ∀ e ∈ F, both (N + N + j.val) e ∧ ∀ k < N + N + j.val, ¬ both k e := by
      intro e he
      have heE : e ∈ E := hFsub he
      have hfg : firstGate e = j := (Finset.mem_filter.mp he).2
      have hspec := Classical.choose_spec (hexGate e heE)
      have hch : Classical.choose (hexGate e heE) = j := by
        simp only [firstGate, heE, ↓reduceDIte] at hfg
        exact hfg
      simpa only [hch] using hspec
    obtain ⟨hop, hinpEq, hb0, hb1⟩ := hgateProps j.val j.isLt
    let a0 := PEqualNP.TopForm.opnd C j.val 0
    let b0 := PEqualNP.TopForm.opnd C j.val 1
    have hevalAnd : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.and.eval [a, b] = (a && b) :=
      fun a b => by cases a <;> cases b <;> rfl
    have hevalOr : ∀ a b : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [a, b] = (a || b) :=
      fun a b => by cases a <;> cases b <;> rfl
    have hnotOr : (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).op ≠
        PEqualNP.CircuitLowerBounds.GateOp.or := by
      intro hor
      obtain ⟨e, he⟩ := hFne
      obtain ⟨⟨hU, h0, h1⟩, hmin⟩ := hFspec e he
      dsimp only [wv] at hU h0 h1
      rw [hwireGate (U e) j.val j.isLt, hor, hevalOr, Bool.or_eq_true] at hU
      rw [hwireGate (V ∅) j.val j.isLt, hor, hevalOr, Bool.or_eq_false_iff] at h0
      rw [hwireGate (V {e.2}) j.val j.isLt, hor, hevalOr, Bool.or_eq_false_iff] at h1
      rcases hU with haU | hbU
      · exact hmin a0 hb0 ⟨haU, h0.1, h1.1⟩
      · exact hmin b0 hb1 ⟨hbU, h0.2, h1.2⟩
    have hand : (PEqualNP.MetaComplexity.NestedCover.gateAt C j.val).op =
        PEqualNP.CircuitLowerBounds.GateOp.and := hop.resolve_right hnotOr
    have hbothChildU : ∀ e ∈ F, wv a0 (U e) = true ∧ wv b0 (U e) = true := by
      intro e he
      have hU := (hFspec e he).1.1
      dsimp only [wv] at hU
      rw [hwireGate (U e) j.val j.isLt, hand, hevalAnd, Bool.and_eq_true] at hU
      exact hU
    have hnotBoth0 : ¬ (wv a0 (V ∅) = false ∧ wv b0 (V ∅) = false) := by
      rintro ⟨ha0, hb0'⟩
      obtain ⟨e, he⟩ := hFne
      obtain ⟨⟨_, _, h1⟩, hmin⟩ := hFspec e he
      dsimp only [wv] at h1
      rw [hwireGate (V {e.2}) j.val j.isLt, hand, hevalAnd, Bool.and_eq_false_iff] at h1
      rcases h1 with ha1 | hb1'
      · exact hmin a0 hb0 ⟨(hbothChildU e he).1, ha0, ha1⟩
      · exact hmin b0 hb1 ⟨(hbothChildU e he).2, hb0', hb1'⟩
    have hor0 : wv a0 (V ∅) = false ∨ wv b0 (V ∅) = false := by
      obtain ⟨e, he⟩ := hFne
      have h0 := (hFspec e he).1.2.1
      dsimp only [wv] at h0
      rw [hwireGate (V ∅) j.val j.isLt, hand, hevalAnd, Bool.and_eq_false_iff] at h0
      exact h0
    have hEmemB : ∀ e ∈ E, I e.1 e.2 ∧ PEqualNP.MetaComplexity.circuitFun (N + N) C (U e) = true ∧
        ∀ b : Bool, PEqualNP.ReadK.lineSingle C (N + N) (fun i => decide (i < N) == b)
          e.1.val (N + e.2.val) = false := by
      intro e he
      obtain ⟨hi, ha, hl, hp⟩ := hEmem e he
      refine ⟨hi, ha, fun b => ?_⟩
      cases b with
      | false =>
        have hfn : (fun i : ℕ => decide (i < N) == false) = (fun i : ℕ => decide (N ≤ i)) := by
          funext i
          by_cases h : i < N
          · simp [h, Nat.not_le_of_gt h]
          · simp [h, Nat.le_of_not_gt h]
        rw [hfn]; exact hl
      | true =>
        have hfn : (fun i : ℕ => decide (i < N) == true) = (fun i : ℕ => decide (i < N)) := by
          funext i
          by_cases h : i < N <;> simp [h]
        rw [hfn]; exact hp
    have hV0eq : V ∅ = fun i : Fin (N + N) => decide (i.val < N) := by
      funext i
      by_cases hi : i.val < N
      · have h : i = Fin.castAdd N ⟨i.val, hi⟩ := Fin.ext rfl
        rw [h]; dsimp only [V]; rw [Fin.addCases_left]; simp [hi]
      · have h : i = Fin.natAdd N ⟨i.val - N, by omega⟩ := Fin.ext (by simp; omega)
        rw [h]; dsimp only [V]; rw [Fin.addCases_right]; simp
    have hV1eq : ∀ e : Fin N × Fin N,
        V {e.2} = Fin.addCases (fun p => decide (¬ I p e.2)) (fun l => decide (l = e.2)) := by
      intro e
      funext i
      by_cases hi : i.val < N
      · have h : i = Fin.castAdd N ⟨i.val, hi⟩ := Fin.ext rfl
        rw [h]; dsimp only [V]; rw [Fin.addCases_left, Fin.addCases_left]; simp
      · have h : i = Fin.natAdd N ⟨i.val - N, by omega⟩ := Fin.ext (by simp; omega)
        rw [h]; dsimp only [V]; rw [Fin.addCases_right, Fin.addCases_right]; simp
    rcases hor0 with ha0 | hb0'
    · have hb0t : wv b0 (V ∅) = true := by
        cases h : wv b0 (V ∅)
        · exact (hnotBoth0 ⟨ha0, h⟩).elim
        · rfl
      have hbad := rereadCore q N I C E F j.val a0 b0 (by omega) hN hcol huniq hAO hsound hEmemB
        ⟨hSizeBig, hgt, hFsub, j.isLt, hj24, hand, by rw [hinpEq],
          by rw [← hV0eq]; exact ha0, by rw [← hV0eq]; exact hb0t⟩
      rcases hbad with ⟨e, he, hfail⟩
      obtain ⟨hUa, hUb⟩ := hbothChildU e he
      have ha1 : wv a0 (V {e.2}) = true := by
        cases h : wv a0 (V {e.2})
        · exact ((hFspec e he).2 a0 hb0 ⟨hUa, ha0, h⟩).elim
        · rfl
      have hb1f : wv b0 (V {e.2}) = false := by
        have h1 := (hFspec e he).1.2.2
        dsimp only [wv] at h1
        rw [hwireGate (V {e.2}) j.val j.isLt, hand, hevalAnd, Bool.and_eq_false_iff] at h1
        rcases h1 with ha1f | hb1f
        · dsimp only [wv, a0] at ha1; rw [ha1] at ha1f; exact Bool.noConfusion ha1f
        · exact hb1f
      exact hfail ⟨hUa, hUb, by dsimp only; rw [← hV1eq e]; exact ha1,
        by dsimp only; rw [← hV1eq e]; exact hb1f⟩
    · have ha0t : wv a0 (V ∅) = true := by
        cases h : wv a0 (V ∅)
        · exact (hnotBoth0 ⟨h, hb0'⟩).elim
        · rfl
      have hbad := rereadCore q N I C E F j.val b0 a0 (by omega) hN hcol huniq hAO hsound hEmemB
        ⟨hSizeBig, hgt, hFsub, j.isLt, hj24, hand, by rw [hinpEq]; exact List.Perm.swap _ _ [],
          by rw [← hV0eq]; exact hb0', by rw [← hV0eq]; exact ha0t⟩
      rcases hbad with ⟨e, he, hfail⟩
      obtain ⟨hUa, hUb⟩ := hbothChildU e he
      have hb1t : wv b0 (V {e.2}) = true := by
        cases h : wv b0 (V {e.2})
        · exact ((hFspec e he).2 b0 hb1 ⟨hUb, hb0', h⟩).elim
        · rfl
      have ha1f : wv a0 (V {e.2}) = false := by
        have h1 := (hFspec e he).1.2.2
        dsimp only [wv] at h1
        rw [hwireGate (V {e.2}) j.val j.isLt, hand, hevalAnd, Bool.and_eq_false_iff] at h1
        rcases h1 with ha1f | hb1f
        · exact ha1f
        · dsimp only [wv, b0] at hb1t; rw [hb1t] at hb1f; exact Bool.noConfusion hb1f
      exact hfail ⟨hUb, hUa, by dsimp only; rw [← hV1eq e]; exact hb1t,
        by dsimp only; rw [← hV1eq e]; exact ha1f⟩
  have hcover : hits ⊆ (lines ∪ points) ∪ E := by
    intro e he
    obtain ⟨hi, ha⟩ := (Finset.mem_filter.mp he).2
    simp only [lines, points, E, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    cases readLine e <;> cases readPoint e <;> simp [hi, ha]
  rw [Fintype.card_subtype] at hL hP ⊢
  change lines.card ≤ 10 * C.size at hL
  change points.card ≤ 10 * C.size at hP
  change hits.card ≤ 44 * C.size
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le lines points
  have h3 := Finset.card_union_le (lines ∪ points) E
  omega
