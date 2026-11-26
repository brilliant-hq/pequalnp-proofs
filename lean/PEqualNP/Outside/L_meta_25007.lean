import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25007_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def pack6 (b0 b1 b2 b3 b4 b5 : Bool) : BitVec 6 :=
  BitVec.ofNat 6
    ((if b0 then 1 else 0) + (if b1 then 2 else 0) + (if b2 then 4 else 0) +
     (if b3 then 8 else 0) + (if b4 then 16 else 0) + (if b5 then 32 else 0))

lemma pack6_getElem (b0 b1 b2 b3 b4 b5 : Bool) (i : Fin 6) :
    (pack6 b0 b1 b2 b3 b4 b5)[i.val] =
      match i.val with
      | 0 => b0
      | 1 => b1
      | 2 => b2
      | 3 => b3
      | 4 => b4
      | _ => b5 := by
  revert b0 b1 b2 b3 b4 b5 i
  decide +kernel

lemma pack6_and (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    pack6 (a0 && b0) (a1 && b1) (a2 && b2) (a3 && b3) (a4 && b4) (a5 && b5) =
      pack6 a0 a1 a2 a3 a4 a5 &&& pack6 b0 b1 b2 b3 b4 b5 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_and, pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩,
      pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩, pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩]
  interval_cases i <;> rfl

lemma pack6_or (a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool) :
    pack6 (a0 || b0) (a1 || b1) (a2 || b2) (a3 || b3) (a4 || b4) (a5 || b5) =
      pack6 a0 a1 a2 a3 a4 a5 ||| pack6 b0 b1 b2 b3 b4 b5 := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_or, pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩,
      pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩, pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩]
  interval_cases i <;> rfl

lemma pack6_not (a0 a1 a2 a3 a4 a5 : Bool) :
    pack6 (!a0) (!a1) (!a2) (!a3) (!a4) (!a5) = ~~~(pack6 a0 a1 a2 a3 a4 a5) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [BitVec.getElem_not, pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩, pack6_getElem _ _ _ _ _ _ ⟨i, hi⟩]
  interval_cases i <;> rfl

def canStep (S : List (BitVec 6)) (v : BitVec 6) : Bool :=
  (v == 0) || (v == 63) ||
  S.any (fun a => (v == a) || (v == ~~~a)) ||
  S.any (fun a => S.any (fun b => (v == (a &&& b)) || (v == (a ||| b))))

def allVals : List (BitVec 6) :=
  (List.range 64).map (BitVec.ofNat 6)

lemma mem_allVals (v : BitVec 6) : v ∈ allVals := by
  refine List.mem_map.mpr ⟨v.toNat, List.mem_range.mpr v.isLt, ?_⟩
  simp [BitVec.ofNat_toNat]

def reach : ℕ → List (BitVec 6) → Bool
  | 0, S => S.contains 35
  | k + 1, S =>
      reach k S ||
      (allVals.filter (fun v => !(S.contains v) && canStep S v)).any (fun v => reach k (v :: S))

lemma reach_mono {k m : ℕ} (hkm : k ≤ m) (S : List (BitVec 6)) (h : reach k S = true) :
    reach m S = true := by
  induction hkm with
  | refl => exact h
  | step _ ih =>
    simp only [reach, ih, Bool.true_or]

lemma reach_step {k : ℕ} {S : List (BitVec 6)} {v : BitVec 6}
    (hv : canStep S v = true) (hr : reach k (v :: S) = true) :
    reach (k + 1) S = true := by
  by_cases hmem : S.contains v = true
  · have hsub : ∀ m (A B : List (BitVec 6)), (∀ x, x ∈ A → x ∈ B) → reach m A = true → reach m B = true := by
      intro m
      induction m with
      | zero =>
        intro A B hAB hA
        simp only [reach, List.contains_iff_mem] at hA ⊢
        exact hAB 35 hA
      | succ m ihm =>
        intro A B hAB hA
        have hstep_mono : ∀ x, canStep A x = true → canStep B x = true := by
          intro x hx
          simp only [canStep, Bool.or_eq_true, List.any_eq_true, beq_iff_eq] at hx ⊢
          rcases hx with ((h0 | h63) | ⟨a, ha, hae⟩) | ⟨a, ha, b, hb, hab⟩
          · exact Or.inl (Or.inl (Or.inl h0))
          · exact Or.inl (Or.inl (Or.inr h63))
          · exact Or.inl (Or.inr ⟨a, hAB a ha, hae⟩)
          · exact Or.inr ⟨a, hAB a ha, b, hAB b hb, hab⟩
        simp only [reach, Bool.or_eq_true] at hA ⊢
        rcases hA with h1 | h2
        · exact Or.inl (ihm A B hAB h1)
        · rw [List.any_eq_true] at h2
          obtain ⟨w, hw, hrw⟩ := h2
          simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hw
          by_cases hBw : B.contains w = true
          · refine Or.inl (ihm (w :: A) B ?_ hrw)
            intro y hy
            rcases List.mem_cons.mp hy with rfl | hyA
            · exact List.contains_iff_mem.mp hBw
            · exact hAB y hyA
          · right
            rw [List.any_eq_true]
            refine ⟨w, ?_, ihm (w :: A) (w :: B) ?_ hrw⟩
            · simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
              exact ⟨mem_allVals w, Bool.eq_false_iff.mpr hBw, hstep_mono w hw.2.2⟩
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hyA
              · exact List.mem_cons_self
              · exact List.mem_cons_of_mem _ (hAB y hyA)
    have hrS : reach k S = true := hsub k (v :: S) S (fun x hx => by
      rcases List.mem_cons.mp hx with rfl | hxS
      · exact List.contains_iff_mem.mp hmem
      · exact hxS) hr
    simp only [reach, hrS, Bool.true_or]
  · simp only [reach, Bool.or_eq_true]
    right
    rw [List.any_eq_true]
    refine ⟨v, ?_, hr⟩
    simp only [List.mem_filter, Bool.and_eq_true, Bool.not_eq_true']
    exact ⟨mem_allVals v, Bool.eq_false_iff.mpr hmem, hv⟩

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def val6 (w0 w1 w2 w3 w4 w5 : List Bool) (i : ℕ) : BitVec 6 :=
  pack6 (w0.getD i false) (w1.getD i false) (w2.getD i false)
        (w3.getD i false) (w4.getD i false) (w5.getD i false)

lemma stepW_getD (w : List Bool) (g : Gate) (i : ℕ) :
    (stepW w g).getD i false =
      if i < w.length then w.getD i false
      else if i = w.length then g.op.eval (g.inputs.map fun k => w.getD k false)
      else false := by
  unfold stepW
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; rfl

lemma gate_canStep (S : List (BitVec 6)) (w0 w1 w2 w3 w4 w5 : List Bool)
    (hS : ∀ i : ℕ, val6 w0 w1 w2 w3 w4 w5 i ∈ S)
    (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    canStep S (pack6
      (g.op.eval (g.inputs.map fun i => w0.getD i false))
      (g.op.eval (g.inputs.map fun i => w1.getD i false))
      (g.op.eval (g.inputs.map fun i => w2.getD i false))
      (g.op.eval (g.inputs.map fun i => w3.getD i false))
      (g.op.eval (g.inputs.map fun i => w4.getD i false))
      (g.op.eval (g.inputs.map fun i => w5.getD i false))) = true := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change ins.length ≤ 2 at hlen
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨k, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;>
      simp [GateOp.eval, pack6, canStep]
  · rcases hop with rfl | rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
      have hi := hS i
      simp only [canStep, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl (Or.inr ⟨val6 w0 w1 w2 w3 w4 w5 i, hi, Or.inl rfl⟩)
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      have hi := hS i
      simp only [canStep, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl (Or.inr ⟨val6 w0 w1 w2 w3 w4 w5 i, hi, Or.inl rfl⟩)
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
      rw [pack6_not]
      have hi := hS i
      simp only [canStep, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl (Or.inr ⟨val6 w0 w1 w2 w3 w4 w5 i, hi, Or.inr rfl⟩)
  · rcases hop with rfl | rfl | rfl
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
      rw [pack6_and]
      have hi := hS i
      have hj := hS j
      simp only [canStep, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inr ⟨val6 w0 w1 w2 w3 w4 w5 i, hi, val6 w0 w1 w2 w3 w4 w5 j, hj, Or.inl rfl⟩
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq]
      rw [pack6_or]
      have hi := hS i
      have hj := hS j
      simp only [canStep, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inr ⟨val6 w0 w1 w2 w3 w4 w5 i, hi, val6 w0 w1 w2 w3 w4 w5 j, hj, Or.inr rfl⟩
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
      rw [pack6_not]
      have hi := hS i
      simp only [canStep, Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact Or.inl (Or.inr ⟨val6 w0 w1 w2 w3 w4 w5 i, hi, Or.inr rfl⟩)
  · simp at hlen

lemma foldl_reach (gs : List Gate) (out : ℕ)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (L : ℕ) (w0 w1 w2 w3 w4 w5 : List Bool) (S : List (BitVec 6)),
      w0.length = L → w1.length = L → w2.length = L →
      w3.length = L → w4.length = L → w5.length = L →
      (0 : BitVec 6) ∈ S →
      (∀ i : ℕ, val6 w0 w1 w2 w3 w4 w5 i ∈ S) →
      val6 (gs.foldl stepW w0) (gs.foldl stepW w1) (gs.foldl stepW w2)
           (gs.foldl stepW w3) (gs.foldl stepW w4) (gs.foldl stepW w5) out = 35 →
      reach gs.length S = true := by
  induction gs with
  | nil =>
    intro L w0 w1 w2 w3 w4 w5 S _ _ _ _ _ _ _ hS hout
    simp only [List.length_nil, reach, List.contains_iff_mem]
    rw [← hout]
    exact hS out
  | cons g gs ih =>
    intro L w0 w1 w2 w3 w4 w5 S h0 h1 h2 h3 h4 h5 hzero hS hout
    have hg := hfan g List.mem_cons_self
    have hgs : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')
    let z := pack6
      (g.op.eval (g.inputs.map fun i => w0.getD i false))
      (g.op.eval (g.inputs.map fun i => w1.getD i false))
      (g.op.eval (g.inputs.map fun i => w2.getD i false))
      (g.op.eval (g.inputs.map fun i => w3.getD i false))
      (g.op.eval (g.inputs.map fun i => w4.getD i false))
      (g.op.eval (g.inputs.map fun i => w5.getD i false))
    have hz : canStep S z = true := gate_canStep S w0 w1 w2 w3 w4 w5 hS g hg
    have hS' : ∀ i : ℕ, val6 (stepW w0 g) (stepW w1 g) (stepW w2 g) (stepW w3 g) (stepW w4 g) (stepW w5 g) i ∈ z :: S := by
      intro i
      unfold val6
      rw [stepW_getD, stepW_getD, stepW_getD, stepW_getD, stepW_getD, stepW_getD,
          h0, h1, h2, h3, h4, h5]
      split_ifs with hlt heq
      · exact List.mem_cons_of_mem _ (hS i)
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ hzero
    have hrec := ih hgs (L + 1) (stepW w0 g) (stepW w1 g) (stepW w2 g) (stepW w3 g) (stepW w4 g) (stepW w5 g) (z :: S)
      (by simp [stepW, h0]) (by simp [stepW, h1]) (by simp [stepW, h2])
      (by simp [stepW, h3]) (by simp [stepW, h4]) (by simp [stepW, h5])
      (List.mem_cons_of_mem _ hzero) hS' hout
    simpa only [List.length_cons] using reach_step hz hrec

def initS : List (BitVec 6) := [0, 7, 56, 9, 18, 36]

set_option maxHeartbeats 0 in
lemma no_reach3 : reach 3 initS = false := by
  decide +kernel

lemma oneEach_getD_val {n : ℕ} (u v : Fin n) (i : ℕ) :
    (oneEach u v).getD i false =
      if i < n then decide (u.val = i)
      else if i < n + n then decide (v.val = i - n)
      else false := by
  unfold oneEach
  simp only [List.getD_eq_getElem?_getD]
  by_cases h1 : i < n
  · rw [if_pos h1, List.getElem?_append_left (by simp; exact h1)]
    rw [List.getElem?_eq_getElem (by simp; exact h1)]
    simp [Fin.ext_iff, eq_comm]
  · rw [if_neg h1]
    by_cases h2 : i < n + n
    · rw [if_pos h2, List.getElem?_append_right (by simp; omega)]
      rw [List.getElem?_eq_getElem (by simp; omega)]
      simp [Fin.ext_iff, eq_comm]
    · rw [if_neg h2, List.getElem?_eq_none (by simp; omega)]
      rfl

lemma init_mem {n : ℕ} {a0 a1 b0 b1 b2 : Fin n}
    (ha : a0 ≠ a1) (hb01 : b0 ≠ b1) (hb02 : b0 ≠ b2) (hb12 : b1 ≠ b2) (i : ℕ) :
    val6 (oneEach a0 b0) (oneEach a0 b1) (oneEach a0 b2)
         (oneEach a1 b0) (oneEach a1 b1) (oneEach a1 b2) i ∈ initS := by
  unfold val6
  rw [oneEach_getD_val, oneEach_getD_val, oneEach_getD_val,
      oneEach_getD_val, oneEach_getD_val, oneEach_getD_val]
  by_cases h1 : i < n
  · simp only [if_pos h1]
    by_cases ea0 : a0.val = i
    · have ea1 : a1.val ≠ i := fun h => ha (Fin.ext (ea0.trans h.symm))
      simp [ea0, ea1, pack6, initS]
    · by_cases ea1 : a1.val = i
      · simp [ea0, ea1, pack6, initS]
      · simp [ea0, ea1, pack6, initS]
  · simp only [if_neg h1]
    by_cases h2 : i < n + n
    · simp only [if_pos h2]
      by_cases eb0 : b0.val = i - n
      · have eb1 : b1.val ≠ i - n := fun h => hb01 (Fin.ext (eb0.trans h.symm))
        have eb2 : b2.val ≠ i - n := fun h => hb02 (Fin.ext (eb0.trans h.symm))
        simp [eb0, eb1, eb2, pack6, initS]
      · by_cases eb1 : b1.val = i - n
        · have eb2 : b2.val ≠ i - n := fun h => hb12 (Fin.ext (eb1.trans h.symm))
          simp [eb0, eb1, eb2, pack6, initS]
        · by_cases eb2 : b2.val = i - n
          · simp [eb0, eb1, eb2, pack6, initS]
          · simp [eb0, eb1, eb2, pack6, initS]
    · simp [if_neg h2, pack6, initS]

lemma no_two_by_three {n : ℕ} (A : Fin n → Fin n → Bool) (a0 a1 b0 b1 b2 : Fin n)
    (ha : a0 ≠ a1) (hb01 : b0 ≠ b1) (hb02 : b0 ≠ b2) (hb12 : b1 ≠ b2)
    (h00 : A a0 b0 = true) (h01 : A a0 b1 = true) (h02 : A a0 b2 = false)
    (h10 : A a1 b0 = false) (h11 : A a1 b1 = false) (h12 : A a1 b2 = true)
    (C : Circuit) (hfan : FanInTwo C) (hsz : C.size ≤ 3) (hrep : Represents A C) : False := by
  have hout : val6 (C.gates.foldl stepW (oneEach a0 b0))
                   (C.gates.foldl stepW (oneEach a0 b1))
                   (C.gates.foldl stepW (oneEach a0 b2))
                   (C.gates.foldl stepW (oneEach a1 b0))
                   (C.gates.foldl stepW (oneEach a1 b1))
                   (C.gates.foldl stepW (oneEach a1 b2)) C.output = 35 := by
    unfold val6
    change pack6 (C.eval (oneEach a0 b0)) (C.eval (oneEach a0 b1)) (C.eval (oneEach a0 b2))
                 (C.eval (oneEach a1 b0)) (C.eval (oneEach a1 b1)) (C.eval (oneEach a1 b2)) = 35
    rw [hrep a0 b0, hrep a0 b1, hrep a0 b2, hrep a1 b0, hrep a1 b1, hrep a1 b2,
        h00, h01, h02, h10, h11, h12]
    decide
  have hlen : ∀ u v : Fin n, (oneEach u v).length = n + n := fun u v => by simp [oneEach]
  have hr := foldl_reach C.gates C.output hfan (n + n)
    (oneEach a0 b0) (oneEach a0 b1) (oneEach a0 b2)
    (oneEach a1 b0) (oneEach a1 b1) (oneEach a1 b2) initS
    (hlen a0 b0) (hlen a0 b1) (hlen a0 b2) (hlen a1 b0) (hlen a1 b1) (hlen a1 b2)
    (by simp [initS]) (init_mem ha hb01 hb02 hb12) hout
  have hr3 := reach_mono hsz initS hr
  rw [no_reach3] at hr3
  exact Bool.noConfusion hr3

end PEqualNP.Outside.L_meta_25007_aux

theorem PEqualNP.Outside.L_meta_25007 : ∀ (n : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → ¬ ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 3 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) C := by
  intro n S T hn hS hSc hT hTc ⟨C, hfan, hsz, hrep⟩
  obtain ⟨u1, hu1⟩ := hS
  obtain ⟨u2, hu2⟩ := hSc
  rw [Finset.mem_compl] at hu2
  have hu12 : u1 ≠ u2 := fun h => hu2 (h ▸ hu1)
  have hcard : T.card + Tᶜ.card = n := by
    have := Finset.card_add_card_compl T
    simpa [Fintype.card_fin] using this
  by_cases hT2 : 2 ≤ T.card
  · obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
    obtain ⟨v3, hv3⟩ := hTc
    rw [Finset.mem_compl] at hv3
    have hv13 : v1 ≠ v3 := fun h => hv3 (h ▸ hv1)
    have hv23 : v2 ≠ v3 := fun h => hv3 (h ▸ hv2)
    exact PEqualNP.Outside.L_meta_25007_aux.no_two_by_three _ u1 u2 v1 v2 v3
      hu12 hv12 hv13 hv23
      (by simp [hu1, hv1]) (by simp [hu1, hv2]) (by simp [hu1, hv3])
      (by simp [hu2, hv1]) (by simp [hu2, hv2]) (by simp [hu2, hv3])
      C hfan hsz hrep
  · have hTc2 : 2 ≤ Tᶜ.card := by omega
    obtain ⟨v1, hv1, v2, hv2, hv12⟩ := Finset.one_lt_card.mp (by omega : 1 < Tᶜ.card)
    rw [Finset.mem_compl] at hv1 hv2
    obtain ⟨v3, hv3⟩ := hT
    have hv13 : v1 ≠ v3 := fun h => hv1 (h ▸ hv3)
    have hv23 : v2 ≠ v3 := fun h => hv2 (h ▸ hv3)
    exact PEqualNP.Outside.L_meta_25007_aux.no_two_by_three _ u2 u1 v1 v2 v3
      hu12.symm hv12 hv13 hv23
      (by simp [hu2, hv1]) (by simp [hu2, hv2]) (by simp [hu2, hv3])
      (by simp [hu1, hv1]) (by simp [hu1, hv2]) (by simp [hu1, hv3])
      C hfan hsz hrep
