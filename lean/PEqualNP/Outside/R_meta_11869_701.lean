import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

set_option maxHeartbeats 6000000 in
theorem PEqualNP.Outside.R_meta_11869_701
    (lowAnd :
      let ins16 : List (BitVec 64) :=
        [0, 1, 2, 3, 4, 5, 6, 7].map (fun u => BitVec.ofNat 64 (255 * 2 ^ (8 * u))) ++
        [0, 1, 2, 3, 4, 5, 6, 7].map (fun v => BitVec.ofNat 64 (72340172838076673 * 2 ^ v))
      let stepBV : List (BitVec 64) → Bool × ℕ × ℕ → List (BitVec 64) :=
        fun ws g => ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]
      let evalBV : List (Bool × ℕ × ℕ) → List (BitVec 64) := fun gs => gs.foldl stepBV ins16
      let target : BitVec 64 := BitVec.ofNat 64 7583035862004050432
      ∀ gs : List (Bool × ℕ × ℕ),
        1 ≤ gs.length → gs.length ≤ 20 →
        1 ≤ (gs.filter (fun g => !g.1)).length →
        (gs.filter (fun g => !g.1)).length ≤ 7 →
        3 ≤ (gs.filter (fun g => g.1)).length →
        (∀ k (hk : k < gs.length),
          let g := gs[k]
          let ws := evalBV (gs.take k)
          let z := if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0
          g.2.1 < g.2.2 ∧ g.2.2 < 16 + k ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 64 ∧ z ∉ ws) →
        (evalBV gs).getD (16 + (gs.length - 1)) 0 = target → False)
    (midAnd :
      let ins16 : List (BitVec 64) :=
        [0, 1, 2, 3, 4, 5, 6, 7].map (fun u => BitVec.ofNat 64 (255 * 2 ^ (8 * u))) ++
        [0, 1, 2, 3, 4, 5, 6, 7].map (fun v => BitVec.ofNat 64 (72340172838076673 * 2 ^ v))
      let stepBV : List (BitVec 64) → Bool × ℕ × ℕ → List (BitVec 64) :=
        fun ws g => ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]
      let evalBV : List (Bool × ℕ × ℕ) → List (BitVec 64) := fun gs => gs.foldl stepBV ins16
      let target : BitVec 64 := BitVec.ofNat 64 7583035862004050432
      ∀ gs : List (Bool × ℕ × ℕ),
        1 ≤ gs.length → gs.length ≤ 20 →
        8 ≤ (gs.filter (fun g => !g.1)).length →
        (gs.filter (fun g => !g.1)).length ≤ 11 →
        3 ≤ (gs.filter (fun g => g.1)).length →
        (∀ k (hk : k < gs.length),
          let g := gs[k]
          let ws := evalBV (gs.take k)
          let z := if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0
          g.2.1 < g.2.2 ∧ g.2.2 < 16 + k ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 64 ∧ z ∉ ws) →
        (evalBV gs).getD (16 + (gs.length - 1)) 0 = target → False)
    (highAnd :
      let ins16 : List (BitVec 64) :=
        [0, 1, 2, 3, 4, 5, 6, 7].map (fun u => BitVec.ofNat 64 (255 * 2 ^ (8 * u))) ++
        [0, 1, 2, 3, 4, 5, 6, 7].map (fun v => BitVec.ofNat 64 (72340172838076673 * 2 ^ v))
      let stepBV : List (BitVec 64) → Bool × ℕ × ℕ → List (BitVec 64) :=
        fun ws g => ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]
      let evalBV : List (Bool × ℕ × ℕ) → List (BitVec 64) := fun gs => gs.foldl stepBV ins16
      let target : BitVec 64 := BitVec.ofNat 64 7583035862004050432
      ∀ gs : List (Bool × ℕ × ℕ),
        1 ≤ gs.length → gs.length ≤ 20 →
        12 ≤ (gs.filter (fun g => !g.1)).length →
        (gs.filter (fun g => !g.1)).length ≤ 17 →
        3 ≤ (gs.filter (fun g => g.1)).length →
        (∀ k (hk : k < gs.length),
          let g := gs[k]
          let ws := evalBV (gs.take k)
          let z := if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0
          g.2.1 < g.2.2 ∧ g.2.2 < 16 + k ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 64 ∧ z ∉ ws) →
        (evalBV gs).getD (16 + (gs.length - 1)) 0 = target → False) :
    ¬ (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (7583035862004050432 : ℕ).testBit (8 * u.val + v.val)) 20) := by
  dsimp only at lowAnd midAnd highAnd
  let ins16 : List (BitVec 64) :=
    [0, 1, 2, 3, 4, 5, 6, 7].map (fun u => BitVec.ofNat 64 (255 * 2 ^ (8 * u))) ++
    [0, 1, 2, 3, 4, 5, 6, 7].map (fun v => BitVec.ofNat 64 (72340172838076673 * 2 ^ v))
  let stepBV : List (BitVec 64) → Bool × ℕ × ℕ → List (BitVec 64) :=
    fun ws g => ws ++ [if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0]
  let evalBV : List (Bool × ℕ × ℕ) → List (BitVec 64) := fun gs => gs.foldl stepBV ins16
  let target : BitVec 64 := BitVec.ofNat 64 7583035862004050432
  -- GMP-fast bit-test conversion (avoids Nat.shiftRight/Nat.shiftLeft in kernel; <0.15s total!)
  have hTB : ∀ (n k : ℕ), n.testBit k = decide ((n / 2 ^ k) % 2 = 1) := by
    intro n k
    rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.and_comm, Nat.and_one_is_mod]
    cases h : (n / 2 ^ k) % 2
    · rfl
    · rename_i m
      have : (n / 2 ^ k) % 2 < 2 := Nat.mod_lt _ (by omega)
      have hm : m = 0 := by omega
      subst hm; rfl
  have hBVBit : ∀ (w : BitVec 64) (k : ℕ), w.getLsbD k = decide ((w.toNat / 2 ^ k) % 2 = 1) := by
    intro w k
    rw [BitVec.getLsbD, hTB]
  have hAObitF : ∀ k : Fin 64, decide (((BitVec.allOnes 64).toNat / 2 ^ k.val) % 2 = 1) = true := by decide
  have hAObit : ∀ k < 64, (BitVec.allOnes 64).getLsbD k = true := fun k hk => by
    rw [hBVBit]; exact hAObitF ⟨k, hk⟩
  let tW (w : BitVec 64) : ℕ := (List.range 64).countP (fun k => w.getLsbD k && target.getLsbD k)
  have h255 : ∀ k : Fin 64, (255 : ℕ).testBit k.val = decide (k.val < 8) := by
    intro k; rw [hTB]
    revert k; decide
  have hCol0 : ∀ k : Fin 64, (72340172838076673 : ℕ).testBit k.val = decide (k.val % 8 = 0) := by
    intro k; rw [hTB]
    revert k; decide
  have hInsRow : ∀ i : Fin 8, ins16.getD i.val 0 = BitVec.ofNat 64 (255 * 2 ^ (8 * i.val)) := by decide
  have hInsCol : ∀ j : Fin 8, ins16.getD (8 + j.val) 0 = BitVec.ofNat 64 (72340172838076673 * 2 ^ j.val) := by decide
  have hInsInit : ∀ (u v : Fin 8) (i : Fin 16),
      (oneEach u v).getD i.val false = (ins16.getD i.val 0).getLsbD (8 * u.val + v.val) := by
    intro u v i
    have hlt64 : 8 * u.val + v.val < 64 := by omega
    by_cases hi : i.val < 8
    · have h1 : (oneEach u v).getD i.val false = decide (i.val = u.val) := by
        change (List.ofFn (fun x : Fin 8 => decide (x = u)) ++ List.ofFn (fun y : Fin 8 => decide (y = v))).getD i.val false = _
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_left (by simp; exact hi), List.getElem_ofFn]
        simp [Fin.ext_iff]
      rw [h1, hInsRow ⟨i.val, hi⟩, BitVec.getLsbD_ofNat, ← Nat.shiftLeft_eq]
      simp only [hlt64, decide_true, Bool.true_and, Nat.testBit_shiftLeft]
      by_cases hge : 8 * i.val ≤ 8 * u.val + v.val
      · simp only [hge, decide_true, Bool.true_and]
        have hd : 8 * u.val + v.val - 8 * i.val < 64 := by omega
        rw [h255 ⟨8 * u.val + v.val - 8 * i.val, hd⟩]
        simp only [decide_eq_decide]
        omega
      · simp only [hge, decide_false, Bool.false_and, decide_eq_false_iff_not]
        omega
    · have hj : i.val - 8 < 8 := by omega
      have h1 : (oneEach u v).getD i.val false = decide (i.val - 8 = v.val) := by
        change (List.ofFn (fun x : Fin 8 => decide (x = u)) ++ List.ofFn (fun y : Fin 8 => decide (y = v))).getD i.val false = _
        rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp; omega)]
        simp only [List.length_ofFn, List.getElem_ofFn, Fin.ext_iff]
      have hieq : i.val = 8 + (i.val - 8) := by omega
      rw [h1, hieq, hInsCol ⟨i.val - 8, hj⟩, BitVec.getLsbD_ofNat, ← Nat.shiftLeft_eq]
      simp only [hlt64, decide_true, Bool.true_and, Nat.testBit_shiftLeft]
      by_cases hge : i.val - 8 ≤ 8 * u.val + v.val
      · simp only [hge, decide_true, Bool.true_and]
        have hd : 8 * u.val + v.val - (i.val - 8) < 64 := by omega
        rw [hCol0 ⟨8 * u.val + v.val - (i.val - 8), hd⟩]
        simp only [decide_eq_decide]
        omega
      · simp only [hge, decide_false, Bool.false_and, decide_eq_false_iff_not]
        omega
  have hTargetNotIns : target ∉ ins16 := by decide
  have hTargetNeZero : target ≠ 0 := by decide
  have hTargetNeOnes : target ≠ BitVec.allOnes 64 := by decide
  have hInsDirty : ∀ w ∈ ins16, ∃ k : Fin 64, w.getLsbD k.val = true ∧ target.getLsbD k.val = false := by
    have hfast : ins16.all (fun w =>
        (List.range 64).any (fun k => decide ((w.toNat / 2 ^ k) % 2 = 1) && !decide ((target.toNat / 2 ^ k) % 2 = 1))) = true := by
      decide
    intro w hw
    have h1 := List.all_eq_true.mp hfast w hw
    obtain ⟨k, hk_mem, hk_ok⟩ := List.any_eq_true.mp h1
    have hk_lt : k < 64 := List.mem_range.mp hk_mem
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hk_ok
    refine ⟨⟨k, hk_lt⟩, ?_, ?_⟩
    · rw [hBVBit]; exact hk_ok.1
    · rw [hBVBit]; exact hk_ok.2
  have hInsWeight : ∀ w ∈ ins16, tW w ≤ 6 := by
    have hfast : ins16.all (fun w =>
        decide ((List.range 64).countP (fun k => decide ((w.toNat / 2 ^ k) % 2 = 1) && decide ((target.toNat / 2 ^ k) % 2 = 1)) ≤ 6)) = true := by
      decide
    intro w hw
    have h1 : (List.range 64).countP (fun k => decide ((w.toNat / 2 ^ k) % 2 = 1) && decide ((target.toNat / 2 ^ k) % 2 = 1)) ≤ 6 :=
      of_decide_eq_true (List.all_eq_true.mp hfast w hw)
    simpa only [tW, hBVBit] using h1
  have hTargetWeight : tW target = 28 := by
    have hfast : (List.range 64).countP (fun k => decide ((target.toNat / 2 ^ k) % 2 = 1) && decide ((target.toNat / 2 ^ k) % 2 = 1)) = 28 := by
      decide
    simpa only [tW, hBVBit] using hfast
  classical
  rintro ⟨C, hMono, hSize, hRep⟩
  -- Helper: evalBV length and append properties
  have hEvalLen : ∀ gs : List (Bool × ℕ × ℕ), (evalBV gs).length = 16 + gs.length := by
    have haux : ∀ (gs : List (Bool × ℕ × ℕ)) (ws : List (BitVec 64)),
        (gs.foldl stepBV ws).length = ws.length + gs.length := by
      intro gs
      induction gs with
      | nil => intro ws; simp
      | cons g rest ih => intro ws; rw [List.foldl_cons, ih]; simp [stepBV]; omega
    intro gs
    change (gs.foldl stepBV ins16).length = 16 + gs.length
    rw [haux]; rfl
  have hEvalAppend : ∀ (gs : List (Bool × ℕ × ℕ)) (g : Bool × ℕ × ℕ),
      evalBV (gs ++ [g]) = stepBV (evalBV gs) g := by
    intro gs g
    change ((gs ++ [g]).foldl stepBV ins16) = stepBV (gs.foldl stepBV ins16) g
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hEvalPrefix : ∀ (gs1 gs2 : List (Bool × ℕ × ℕ)),
      ∀ w ∈ evalBV gs1, w ∈ evalBV (gs1 ++ gs2) := by
    intro gs1 gs2
    have haux : ∀ (gs : List (Bool × ℕ × ℕ)) (ws : List (BitVec 64)) (w : BitVec 64),
        w ∈ ws → w ∈ gs.foldl stepBV ws := by
      intro gs
      induction gs with
      | nil => intro ws w hw; exact hw
      | cons g rest ih =>
        intro ws w hw
        rw [List.foldl_cons]
        exact ih _ w (List.mem_append_left _ hw)
    intro w hw
    change w ∈ (gs1 ++ gs2).foldl stepBV ins16
    rw [List.foldl_append]
    exact haux gs2 (evalBV gs1) w hw
  have hEvalPrefixGetD : ∀ (gs1 gs2 : List (Bool × ℕ × ℕ)) (k : ℕ),
      k < 16 + gs1.length → (evalBV (gs1 ++ gs2)).getD k 0 = (evalBV gs1).getD k 0 := by
    have haux : ∀ (gs : List (Bool × ℕ × ℕ)) (ws : List (BitVec 64)) (k : ℕ),
        k < ws.length → (gs.foldl stepBV ws).getD k 0 = ws.getD k 0 := by
      intro gs
      induction gs with
      | nil => intro ws k _; rfl
      | cons g rest ih =>
        intro ws k hk
        rw [List.foldl_cons, ih _ k (by simp [stepBV]; omega)]
        rw [List.getD_eq_getElem _ _ (by simp [stepBV]; omega), List.getElem_append_left hk,
          ← List.getD_eq_getElem _ _ hk]
    intro gs1 gs2 k hk
    change ((gs1 ++ gs2).foldl stepBV ins16).getD k 0 = (evalBV gs1).getD k 0
    rw [List.foldl_append]
    exact haux gs2 (evalBV gs1) k (by rw [hEvalLen]; exact hk)
  -- Cleanliness predicate for a BitVec 64 DAG
  let IsClean (gs : List (Bool × ℕ × ℕ)) : Prop :=
    ∀ k (hk : k < gs.length),
      let g := gs[k]
      let ws := evalBV (gs.take k)
      let z := if g.1 then ws.getD g.2.1 0 ||| ws.getD g.2.2 0 else ws.getD g.2.1 0 &&& ws.getD g.2.2 0
      g.2.1 < g.2.2 ∧ g.2.2 < 16 + k ∧ z ≠ 0 ∧ z ≠ BitVec.allOnes 64 ∧ z ∉ ws
  -- Step 1: Simulate C.gates in BitVec 64 and compress into a clean DAG gs of length <= C.gates.length
  have hSimNorm : ∀ (cgs : List Gate) (cw : List (BitVec 64)) (gs : List (Bool × ℕ × ℕ)),
      (∀ g ∈ cgs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ (u v : Fin 8) (ws : List Bool),
        ws.length = cw.length →
        (∀ k, ws.getD k false = (cw.getD k 0).getLsbD (8 * u.val + v.val)) →
        True) →
      (∀ w ∈ cw, w = 0 ∨ w = BitVec.allOnes 64 ∨ w ∈ evalBV gs) →
      IsClean gs →
      ∃ (cw' : List (BitVec 64)) (gs' : List (Bool × ℕ × ℕ)),
        cw'.length = cw.length + cgs.length ∧
        gs'.length ≤ gs.length + cgs.length ∧
        (∀ (u v : Fin 8) (ws : List Bool),
          ws.length = cw.length →
          (∀ k, ws.getD k false = (cw.getD k 0).getLsbD (8 * u.val + v.val)) →
          ∀ k, (cgs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).getD k false =
            (cw'.getD k 0).getLsbD (8 * u.val + v.val)) ∧
        (∀ w ∈ cw', w = 0 ∨ w = BitVec.allOnes 64 ∨ w ∈ evalBV gs') ∧
        IsClean gs' := by
    intro cgs
    induction cgs with
    | nil =>
      intro cw gs _ _ hcov hcl
      exact ⟨cw, gs, by simp, by simp, fun u v ws _ hws k => hws k, hcov, hcl⟩
    | cons g rest ih =>
      intro cw gs hcgs _ hcov hcl
      have hg := hcgs g List.mem_cons_self
      let bvGate : BitVec 64 :=
        if g.op = GateOp.or then
          g.inputs.foldr (fun i acc => cw.getD i 0 ||| acc) 0
        else
          g.inputs.foldr (fun i acc => cw.getD i 0 &&& acc) (BitVec.allOnes 64)
      have hbvGate_bit : ∀ (u v : Fin 8) (ws : List Bool),
          (∀ k, ws.getD k false = (cw.getD k 0).getLsbD (8 * u.val + v.val)) →
          g.op.eval (g.inputs.map fun i => ws.getD i false) = bvGate.getLsbD (8 * u.val + v.val) := by
        intro u v ws hws
        rcases hg.1 with hand | hor
        · have hne : g.op ≠ GateOp.or := by rw [hand]; intro h; cases h
          simp only [bvGate, hne, ite_false]
          rw [hand]
          change (g.inputs.map fun i => ws.getD i false).all id = _
          have hfold_and : ∀ l : List ℕ,
              (l.map fun i => ws.getD i false).all id =
              (l.foldr (fun i acc => cw.getD i 0 &&& acc) (BitVec.allOnes 64)).getLsbD (8 * u.val + v.val) := by
            intro l
            induction l with
            | nil =>
              have hlt64 : 8 * u.val + v.val < 64 := by omega
              exact (hAObit _ hlt64).symm
            | cons i tl ihl =>
              simp only [List.map_cons, List.all_cons, id_eq, List.foldr_cons, BitVec.getLsbD_and, hws i, ihl]
          exact hfold_and g.inputs
        · simp only [bvGate, hor, ite_true]
          change (g.inputs.map fun i => ws.getD i false).any id = _
          have hfold_or : ∀ l : List ℕ,
              (l.map fun i => ws.getD i false).any id =
              (l.foldr (fun i acc => cw.getD i 0 ||| acc) 0).getLsbD (8 * u.val + v.val) := by
            intro l
            induction l with
            | nil => simp
            | cons i tl ihl =>
              simp only [List.map_cons, List.any_cons, id_eq, List.foldr_cons, BitVec.getLsbD_or, hws i, ihl]
          exact hfold_or g.inputs
      -- BitVec 64 absorption/identity helpers
      have h_or_zero : ∀ a : BitVec 64, a ||| 0 = a := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
      have h_zero_or : ∀ a : BitVec 64, 0 ||| a = a := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
      have h_and_zero : ∀ a : BitVec 64, a &&& 0 = 0 := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
      have h_zero_and : ∀ a : BitVec 64, 0 &&& a = 0 := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
      have h_and_ones : ∀ a : BitVec 64, a &&& BitVec.allOnes 64 = a := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; rw [BitVec.getLsbD_and, hAObit k hk, Bool.and_true]
      have h_ones_and : ∀ a : BitVec 64, BitVec.allOnes 64 &&& a = a := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; rw [BitVec.getLsbD_and, hAObit k hk, Bool.true_and]
      have h_or_ones : ∀ a : BitVec 64, a ||| BitVec.allOnes 64 = BitVec.allOnes 64 := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; rw [BitVec.getLsbD_or, hAObit k hk, Bool.or_true]
      have h_ones_or : ∀ a : BitVec 64, BitVec.allOnes 64 ||| a = BitVec.allOnes 64 := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; rw [BitVec.getLsbD_or, hAObit k hk, Bool.true_or]
      have h_or_self : ∀ a : BitVec 64, a ||| a = a := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
      have h_and_self : ∀ a : BitVec 64, a &&& a = a := fun a => by apply BitVec.eq_of_getLsbD_eq; intro k hk; simp
      -- Show bvGate is either already covered or can be added via 1 clean binary gate
      have hStep : ∃ gs1 : List (Bool × ℕ × ℕ),
          gs1.length ≤ gs.length + 1 ∧
          (∀ w ∈ evalBV gs, w ∈ evalBV gs1) ∧
          (bvGate = 0 ∨ bvGate = BitVec.allOnes 64 ∨ bvGate ∈ evalBV gs1) ∧
          IsClean gs1 := by
        by_cases hcovz : bvGate = 0 ∨ bvGate = BitVec.allOnes 64 ∨ bvGate ∈ evalBV gs
        · exact ⟨gs, by omega, fun _ hw => hw, hcovz, hcl⟩
        · push Not at hcovz
          obtain ⟨hz0, hz1, hzmem⟩ := hcovz
          have hlen2 : ∃ i j : ℕ, g.inputs = [i, j] := by
            cases hin : g.inputs with
            | nil =>
              exfalso
              rcases hg.1 with hand | hor
              · have hne : g.op ≠ GateOp.or := by rw [hand]; intro h; cases h
                simp only [bvGate, hne, ite_false, hin, List.foldr_nil] at hz1
                exact hz1 rfl
              · simp only [bvGate, hor, ite_true, hin, List.foldr_nil] at hz0
                exact hz0 rfl
            | cons i tl =>
              cases tl with
              | nil =>
                exfalso
                have hci : cw.getD i 0 = 0 ∨ cw.getD i 0 = BitVec.allOnes 64 ∨ cw.getD i 0 ∈ evalBV gs := by
                  by_cases hi : i < cw.length
                  · rw [List.getD_eq_getElem _ _ hi]; exact hcov _ (List.getElem_mem hi)
                  · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl rfl
                have hbeq : bvGate = cw.getD i 0 := by
                  rcases hg.1 with hand | hor
                  · have hne : g.op ≠ GateOp.or := by rw [hand]; intro h; cases h
                    simp only [bvGate, hne, ite_false, hin, List.foldr_cons, List.foldr_nil, h_and_ones]
                  · simp only [bvGate, hor, ite_true, hin, List.foldr_cons, List.foldr_nil, h_or_zero]
                rw [hbeq] at hz0 hz1 hzmem
                rcases hci with h0 | h1 | hm
                · exact hz0 h0
                · exact hz1 h1
                · exact hzmem hm
              | cons j tl2 =>
                cases tl2 with
                | nil => exact ⟨i, j, rfl⟩
                | cons _ _ =>
                  have := hg.2
                  rw [hin] at this
                  simp at this
          obtain ⟨i, j, hij⟩ := hlen2
          let x : BitVec 64 := cw.getD i 0
          let y : BitVec 64 := cw.getD j 0
          have hx_cov : x = 0 ∨ x = BitVec.allOnes 64 ∨ x ∈ evalBV gs := by
            dsimp only [x]
            by_cases hi : i < cw.length
            · rw [List.getD_eq_getElem _ _ hi]; exact hcov _ (List.getElem_mem hi)
            · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl rfl
          have hy_cov : y = 0 ∨ y = BitVec.allOnes 64 ∨ y ∈ evalBV gs := by
            dsimp only [y]
            by_cases hj : j < cw.length
            · rw [List.getD_eq_getElem _ _ hj]; exact hcov _ (List.getElem_mem hj)
            · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl rfl
          have hbv_xy : bvGate = if g.op = GateOp.or then x ||| y else x &&& y := by
            by_cases hor : g.op = GateOp.or
            · simp only [bvGate, hor, ite_true, hij, List.foldr_cons, List.foldr_nil, h_or_zero, x, y]
            · simp only [bvGate, hor, ite_false, hij, List.foldr_cons, List.foldr_nil, h_and_ones, x, y]
          have hx_in : x ∈ evalBV gs := by
            rcases hx_cov with hx0 | hx1 | hxm
            · exfalso
              rw [hbv_xy, hx0] at hz0 hz1 hzmem
              by_cases hor : g.op = GateOp.or
              · simp only [hor, ite_true, h_zero_or] at hz0 hz1 hzmem
                rcases hy_cov with hy0 | hy1 | hym
                · exact hz0 hy0
                · exact hz1 hy1
                · exact hzmem hym
              · simp only [hor, ite_false, h_zero_and] at hz0
                exact hz0 rfl
            · exfalso
              rw [hbv_xy, hx1] at hz0 hz1 hzmem
              by_cases hor : g.op = GateOp.or
              · simp only [hor, ite_true, h_ones_or] at hz1
                exact hz1 rfl
              · simp only [hor, ite_false, h_ones_and] at hz0 hz1 hzmem
                rcases hy_cov with hy0 | hy1 | hym
                · exact hz0 hy0
                · exact hz1 hy1
                · exact hzmem hym
            · exact hxm
          have hy_in : y ∈ evalBV gs := by
            rcases hy_cov with hy0 | hy1 | hym
            · exfalso
              rw [hbv_xy, hy0] at hz0 hz1 hzmem
              by_cases hor : g.op = GateOp.or
              · simp only [hor, ite_true, h_or_zero] at hzmem
                exact hzmem hx_in
              · simp only [hor, ite_false, h_and_zero] at hz0
                exact hz0 rfl
            · exfalso
              rw [hbv_xy, hy1] at hz0 hz1 hzmem
              by_cases hor : g.op = GateOp.or
              · simp only [hor, ite_true, h_or_ones] at hz1
                exact hz1 rfl
              · simp only [hor, ite_false, h_and_ones] at hzmem
                exact hzmem hx_in
            · exact hym
          have hxy_ne : x ≠ y := by
            intro hxy
            rw [hbv_xy, hxy] at hzmem
            by_cases hor : g.op = GateOp.or
            · simp only [hor, ite_true, h_or_self] at hzmem
              exact hzmem hy_in
            · simp only [hor, ite_false, h_and_self] at hzmem
              exact hzmem hy_in
          obtain ⟨a, ha_lt, ha_eq⟩ := List.getElem_of_mem hx_in
          obtain ⟨b, hb_lt, hb_eq⟩ := List.getElem_of_mem hy_in
          have hab_ne : a ≠ b := fun h => hxy_ne (by subst h; exact ha_eq.symm.trans hb_eq)
          let p : ℕ := min a b
          let q : ℕ := max a b
          have hpq_lt : p < q := by omega
          have hq_lt : q < 16 + gs.length := by rw [← hEvalLen gs]; omega
          let opB : Bool := decide (g.op = GateOp.or)
          let newG : Bool × ℕ × ℕ := (opB, p, q)
          have hnew_val : (if newG.1 then (evalBV gs).getD newG.2.1 0 ||| (evalBV gs).getD newG.2.2 0
              else (evalBV gs).getD newG.2.1 0 &&& (evalBV gs).getD newG.2.2 0) = bvGate := by
            have hp_get : (evalBV gs).getD p 0 = if a ≤ b then x else y := by
              by_cases hab : a ≤ b
              · have hp : p = a := Nat.min_eq_left hab
                simp only [hab, ite_true, hp, List.getD_eq_getElem _ _ ha_lt, ha_eq]
              · have hp : p = b := Nat.min_eq_right (by omega)
                simp only [hab, ite_false, hp, List.getD_eq_getElem _ _ hb_lt, hb_eq]
            have hq_get : (evalBV gs).getD q 0 = if a ≤ b then y else x := by
              by_cases hab : a ≤ b
              · have hq : q = b := Nat.max_eq_right hab
                simp only [hab, ite_true, hq, List.getD_eq_getElem _ _ hb_lt, hb_eq]
              · have hq : q = a := Nat.max_eq_left (by omega)
                simp only [hab, ite_false, hq, List.getD_eq_getElem _ _ ha_lt, ha_eq]
            simp only [newG, opB, hp_get, hq_get, hbv_xy]
            by_cases hor : g.op = GateOp.or <;> by_cases hab : a ≤ b <;>
              simp [hor, hab, BitVec.or_comm, BitVec.and_comm]
          refine ⟨gs ++ [newG], by simp, hEvalPrefix gs [newG], Or.inr (Or.inr ?_), ?_⟩
          · rw [hEvalAppend]
            simp only [stepBV, List.mem_append, List.mem_singleton]
            rw [hnew_val]
            exact Or.inr rfl
          · intro k hk
            by_cases hlt : k < gs.length
            · have htake : (gs ++ [newG]).take k = gs.take k := by
                rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
              have hget : (gs ++ [newG])[k] = gs[k] := List.getElem_append_left hlt
              simpa only [htake, hget] using hcl k hlt
            · have hk_eq : k = gs.length := by simp at hk; omega
              subst hk_eq
              have htake : (gs ++ [newG]).take gs.length = gs := by simp
              have hget : (gs ++ [newG])[gs.length] = newG := by simp
              simp only [htake, hget, hnew_val]
              exact ⟨hpq_lt, hq_lt, hz0, hz1, hzmem⟩
      obtain ⟨gs1, hgs1_len, hgs1_sub, hbv_cov, hgs1_clean⟩ := hStep
      have hcov' : ∀ w ∈ cw ++ [bvGate], w = 0 ∨ w = BitVec.allOnes 64 ∨ w ∈ evalBV gs1 := by
        intro w hw
        rcases List.mem_append.mp hw with hw1 | hw2
        · rcases hcov w hw1 with h0 | h1 | hm
          · exact Or.inl h0
          · exact Or.inr (Or.inl h1)
          · exact Or.inr (Or.inr (hgs1_sub w hm))
        · rw [List.mem_singleton.mp hw2]
          exact hbv_cov
      obtain ⟨cw', gs', hcw'_len, hgs'_len, hcw'_bits, hcov_final, hcl_final⟩ :=
        ih (cw ++ [bvGate]) gs1 (fun g' hg' => hcgs g' (List.mem_cons_of_mem g hg'))
          (fun _ _ _ _ _ => trivial) hcov' hgs1_clean
      refine ⟨cw', gs', by simp only [List.length_append, List.length_cons, List.length_nil] at hcw'_len ⊢; omega, by simp only [List.length_cons]; omega, ?_, hcov_final, hcl_final⟩
      intro u v ws hlen hws k
      rw [List.foldl_cons]
      apply hcw'_bits u v (ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]) (by simp [hlen])
      intro m
      by_cases hm : m < ws.length
      · have hmc : m < cw.length := hlen ▸ hm
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hm, ← List.getD_eq_getElem _ _ hm]
        conv_rhs => rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hmc, ← List.getD_eq_getElem cw 0 hmc]
        exact hws m
      · by_cases hmeq : m = ws.length
        · subst hmeq
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
          conv_rhs => rw [hlen, List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
          simp only [Nat.sub_self, List.getElem_cons_zero]
          exact hbvGate_bit u v ws hws
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)]
          simp
  obtain ⟨cw, gs0, hcw_len, hgs0_len, hcw_bits, hcw_cov, hgs0_clean⟩ :=
    hSimNorm C.gates ins16 [] hMono (fun _ _ _ _ _ => trivial)
      (fun w hw => Or.inr (Or.inr hw)) (fun k hk => by simp at hk)
  -- Show cw.getD C.output 0 = target
  have hOutTarget : cw.getD C.output 0 = target := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let u : Fin 8 := ⟨i / 8, by omega⟩
    let v : Fin 8 := ⟨i % 8, by omega⟩
    have huv : 8 * u.val + v.val = i := by simp [u, v]; omega
    rw [← huv]
    have honeLen : (oneEach u v).length = 16 := by
      change (List.ofFn (fun x : Fin 8 => decide (x = u)) ++ List.ofFn (fun y : Fin 8 => decide (y = v))).length = 16
      simp
    have h1 := hcw_bits u v (oneEach u v) (by rw [honeLen]; rfl) (fun k => by
      by_cases hk : k < 16
      · exact hInsInit u v ⟨k, hk⟩
      · rw [List.getD_eq_default _ _ (by omega),
          List.getD_eq_default _ _ (by simp [ins16]; omega)]
        simp) C.output
    have h2 : C.eval (oneEach u v) = (7583035862004050432 : ℕ).testBit (8 * u.val + v.val) := hRep u v
    have h3 : C.eval (oneEach u v) = (cw.getD C.output 0).getLsbD (8 * u.val + v.val) := h1
    rw [← h3, h2]
    have hlt64 : 8 * u.val + v.val < 64 := by omega
    dsimp only [target]
    rw [BitVec.getLsbD_ofNat]
    simp [hlt64]
  have hTargetMem : target ∈ evalBV gs0 := by
    have hc : cw.getD C.output 0 = 0 ∨ cw.getD C.output 0 = BitVec.allOnes 64 ∨ cw.getD C.output 0 ∈ evalBV gs0 := by
      by_cases ho : C.output < cw.length
      · rw [List.getD_eq_getElem _ _ ho]; exact hcw_cov _ (List.getElem_mem ho)
      · rw [List.getD_eq_default _ _ (by omega)]; exact Or.inl rfl
    rw [hOutTarget] at hc
    rcases hc with h0 | h1 | hm
    · exact (hTargetNeZero h0).elim
    · exact (hTargetNeOnes h1).elim
    · exact hm
  -- Truncate gs0 so that the last wire equals target
  obtain ⟨pos, hpos_lt, hpos_eq⟩ := List.getElem_of_mem hTargetMem
  have hpos_ge16 : 16 ≤ pos := by
    by_contra hlt16
    push Not at hlt16
    have h1 : (evalBV gs0).getD pos 0 = (evalBV []).getD pos 0 := by
      simpa using hEvalPrefixGetD [] gs0 pos (by omega)
    rw [List.getD_eq_getElem _ _ hpos_lt, hpos_eq] at h1
    have h2 : target ∈ ins16 := by
      have hlen16 : ins16.length = 16 := rfl
      have hlti : pos < ins16.length := by omega
      change target = ins16.getD pos 0 at h1
      rw [List.getD_eq_getElem _ _ hlti] at h1
      rw [h1]
      exact List.getElem_mem hlti
    exact hTargetNotIns h2
  let idx : ℕ := pos - 16
  have hidx_lt : idx < gs0.length := by rw [hEvalLen] at hpos_lt; omega
  let gs : List (Bool × ℕ × ℕ) := gs0.take (idx + 1)
  have hgs_len_eq : gs.length = idx + 1 := by simp [gs, Nat.min_eq_left (Nat.succ_le_of_lt hidx_lt)]
  have hgs_ge1 : 1 ≤ gs.length := by omega
  have hgs_le20 : gs.length ≤ 20 := by
    change gs.length ≤ 20
    have : C.gates.length ≤ 20 := hSize
    simp at hgs0_len
    omega
  have hgs_clean : IsClean gs := by
    intro k hk
    have hk0 : k < gs0.length := by omega
    have htake : gs.take k = gs0.take k := by
      simp only [gs, List.take_take, Nat.min_eq_left (by omega : k ≤ idx + 1)]
    have hget : gs[k] = gs0[k] := by
      simp only [gs, List.getElem_take]
    simpa only [htake, hget] using hgs0_clean k hk0
  have hgs_last : (evalBV gs).getD (16 + (gs.length - 1)) 0 = target := by
    have hsplit : gs0 = gs ++ gs0.drop (idx + 1) := (List.take_append_drop (idx + 1) gs0).symm
    have hpre := hEvalPrefixGetD gs (gs0.drop (idx + 1)) pos (by omega)
    rw [← hsplit, List.getD_eq_getElem _ _ hpos_lt, hpos_eq] at hpre
    have heq : 16 + (gs.length - 1) = pos := by omega
    rw [heq, ← hpre]
  have hTargetInGs : target ∈ evalBV gs := by
    rw [← hgs_last]
    have hlt : 16 + (gs.length - 1) < (evalBV gs).length := by rw [hEvalLen]; omega
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  -- Step 2: Prove 1 <= andCount gs (pure OR gates keep ∃ k < 64, w[k]=true ∧ target[k]=false)
  have hAndGe1 : 1 ≤ (gs.filter (fun g => !g.1)).length := by
    by_contra h0
    have hAllOr : ∀ g ∈ gs, g.1 = true := by
      intro g hg
      cases hgb : g.1
      · exfalso
        have hmem : g ∈ gs.filter (fun g => !g.1) := List.mem_filter.mpr ⟨hg, by simp [hgb]⟩
        have hpos : 0 < (gs.filter (fun g => !g.1)).length := List.length_pos_of_mem hmem
        omega
      · rfl
    have hInvDirty : ∀ (l : List (Bool × ℕ × ℕ)) (ws : List (BitVec 64)),
        (∀ g ∈ l, g.1 = true) →
        (∀ k (hk : k < l.length), l[k].2.1 < ws.length + k) →
        (∀ w ∈ ws, ∃ k : Fin 64, w.getLsbD k.val = true ∧ target.getLsbD k.val = false) →
        ∀ w ∈ l.foldl stepBV ws, ∃ k : Fin 64, w.getLsbD k.val = true ∧ target.getLsbD k.val = false := by
      intro l
      induction l with
      | nil => intro ws _ _ hws w hw; exact hws w hw
      | cons g rest ih =>
        intro ws hor hidx hws
        rw [List.foldl_cons]
        have hg1 : g.1 = true := hor g List.mem_cons_self
        have hg_lt : g.2.1 < ws.length := by
          have h0 := hidx 0 (by simp)
          simpa using h0
        apply ih (stepBV ws g) (fun g' hg' => hor g' (List.mem_cons_of_mem g hg'))
        · intro k hk
          have := hidx (k + 1) (by simp; omega)
          simp only [stepBV, List.length_append, List.length_singleton]
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this
        · intro w hw
          rcases List.mem_append.mp hw with hw1 | hw2
          · exact hws w hw1
          · simp only [List.mem_singleton.mp hw2, hg1, ite_true]
            have hx_ne : ∃ k : Fin 64, (ws.getD g.2.1 0).getLsbD k.val = true ∧ target.getLsbD k.val = false := by
              rw [List.getD_eq_getElem _ _ hg_lt]
              exact hws _ (List.getElem_mem hg_lt)
            obtain ⟨k, hkx, hkt⟩ := hx_ne
            refine ⟨k, ?_, hkt⟩
            rw [BitVec.getLsbD_or, hkx]
            rfl
    have hCleanIdx : ∀ k (hk : k < gs.length), gs[k].2.1 < ins16.length + k := by
      intro k hk
      have hc := hgs_clean k hk
      have hlen16 : ins16.length = 16 := rfl
      omega
    obtain ⟨k, hk1, hk2⟩ := hInvDirty gs ins16 hAllOr hCleanIdx hInsDirty target hTargetInGs
    rw [hk1] at hk2
    cases hk2
  -- Step 3: Prove 3 <= orCount gs (tW <= 6 * 2^(orCount), and 6 * 2^2 = 24 < 28)
  have hCountP_mono : ∀ (p q : ℕ → Bool) (xs : List ℕ),
      (∀ k, p k = true → q k = true) → xs.countP p ≤ xs.countP q := by
    intro p q xs hpq
    induction xs with
    | nil => simp
    | cons a tl ih =>
      simp only [List.countP_cons]
      cases hp : p a
      · simp; omega
      · simp [hpq a hp]; omega
  have hCountP_or : ∀ (p q r : ℕ → Bool) (xs : List ℕ),
      (∀ k, r k = true → p k = true ∨ q k = true) → xs.countP r ≤ xs.countP p + xs.countP q := by
    intro p q r xs h
    induction xs with
    | nil => simp
    | cons a tl ih =>
      simp only [List.countP_cons]
      cases hr : r a
      · simp; omega
      · rcases h a hr with hp | hq
        · simp [hp]; omega
        · simp [hq]; omega
  have hOrGe3 : 3 ≤ (gs.filter (fun g => g.1)).length := by
    have hInvW : ∀ (l : List (Bool × ℕ × ℕ)) (ws : List (BitVec 64)) (M : ℕ),
        (∀ w ∈ ws, tW w ≤ M) →
        ∀ w ∈ l.foldl stepBV ws, tW w ≤ M * 2 ^ (l.filter (fun g => g.1)).length := by
      intro l
      induction l with
      | nil => intro ws M hM w hw; simpa using hM w hw
      | cons g rest ih =>
        intro ws M hM
        rw [List.foldl_cons]
        have hgetW : ∀ idx : ℕ, tW (ws.getD idx 0) ≤ M := by
          intro idx
          by_cases h : idx < ws.length
          · rw [List.getD_eq_getElem _ _ h]; exact hM _ (List.getElem_mem h)
          · rw [List.getD_eq_default _ _ (by omega)]
            have h0 : tW 0 = 0 := by simp [tW]
            omega
        cases hg1 : g.1
        · have hfilt : ((g :: rest).filter (fun g => g.1)).length = (rest.filter (fun g => g.1)).length := by
            simp [hg1]
          rw [hfilt]
          apply ih (stepBV ws g) M
          intro w hw
          rcases List.mem_append.mp hw with hw1 | hw2
          · exact hM w hw1
          · simp only [List.mem_singleton.mp hw2, hg1, ite_false]
            have hle : tW (ws.getD g.2.1 0 &&& ws.getD g.2.2 0) ≤ tW (ws.getD g.2.1 0) := by
              apply hCountP_mono
              intro k hk
              simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hk ⊢
              exact ⟨hk.1.1, hk.2⟩
            exact hle.trans (hgetW g.2.1)
        · have hfilt : ((g :: rest).filter (fun g => g.1)).length = (rest.filter (fun g => g.1)).length + 1 := by
            simp [hg1]
          rw [hfilt, Nat.pow_succ, Nat.mul_comm (2 ^ _) 2, ← Nat.mul_assoc]
          apply ih (stepBV ws g) (M * 2)
          intro w hw
          rcases List.mem_append.mp hw with hw1 | hw2
          · exact (hM w hw1).trans (by omega)
          · simp only [List.mem_singleton.mp hw2, hg1, ite_true]
            have hle : tW (ws.getD g.2.1 0 ||| ws.getD g.2.2 0) ≤ tW (ws.getD g.2.1 0) + tW (ws.getD g.2.2 0) := by
              apply hCountP_or
              intro k hk
              simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, Bool.and_eq_true, Bool.or_eq_true] at hk ⊢
              rcases hk.1 with h1 | h2
              · exact Or.inl ⟨h1, hk.2⟩
              · exact Or.inr ⟨h2, hk.2⟩
            have h1 := hgetW g.2.1
            have h2 := hgetW g.2.2
            omega
    have h28 : tW target ≤ 6 * 2 ^ (gs.filter (fun g => g.1)).length :=
      hInvW gs ins16 6 hInsWeight target hTargetInGs
    have ht28 : tW target = 28 := hTargetWeight
    by_contra hlt3
    have hle2 : (gs.filter (fun g => g.1)).length ≤ 2 := by omega
    have hpow : 2 ^ (gs.filter (fun g => g.1)).length ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) hle2
    omega
  -- Sum of AND count and OR count equals gs.length <= 20, so andCount <= 17
  have hCountSum : (gs.filter (fun g => !g.1)).length + (gs.filter (fun g => g.1)).length = gs.length := by
    have haux : ∀ l : List (Bool × ℕ × ℕ),
        (l.filter (fun g => !g.1)).length + (l.filter (fun g => g.1)).length = l.length := by
      intro l
      induction l with
      | nil => simp
      | cons g rest ih =>
        cases hb : g.1 <;> simp [hb] <;> omega
    exact haux gs
  have hAndLe17 : (gs.filter (fun g => !g.1)).length ≤ 17 := by omega
  -- Dispatch to the 3 sharp AND-count regimes
  by_cases h1 : (gs.filter (fun g => !g.1)).length ≤ 7
  · exact lowAnd gs hgs_ge1 hgs_le20 hAndGe1 h1 hOrGe3 hgs_clean hgs_last
  · by_cases h2 : (gs.filter (fun g => !g.1)).length ≤ 11
    · exact midAnd gs hgs_ge1 hgs_le20 (by omega) h2 hOrGe3 hgs_clean hgs_last
    · exact highAnd gs hgs_ge1 hgs_le20 (by omega) hAndLe17 hOrGe3 hgs_clean hgs_last
