import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_573

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepf (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepf x := rfl

theorem stepf_len (w : List Bool) (g : Gate) : (stepf w g).length = w.length + 1 := by
  simp [stepf]

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepf w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih, stepf_len, List.length_cons]; omega

theorem fold_pre (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepf w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (stepf w g) (by rw [stepf_len]; omega), stepf,
      List.getD_append _ _ _ _ hi]

theorem fold_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hrb : ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < w.length + j) :
    (gs.foldl stepf w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map
        fun i => (gs.foldl stepf w).getD i false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have h0 : ∀ i ∈ g.inputs, i < w.length := fun i hi => by simpa using hrb 0 (by simp) i hi
      rw [List.foldl_cons, fold_pre gs (stepf w g) _ (by rw [stepf_len]; omega)]
      simp only [List.getD_cons_zero, Nat.add_zero]
      rw [stepf, List.getD_append_right _ _ _ _ le_rfl]
      simp only [Nat.sub_self, List.getD_cons_zero]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [fold_pre gs _ i (by simp; have := h0 i hi; omega), List.getD_append _ _ _ _ (h0 i hi)]
    | succ j =>
      have hl : (stepf w g).length = w.length + 1 := stepf_len w g
      rw [List.foldl_cons, show w.length + (j + 1) = (stepf w g).length + j by omega]
      simp only [List.getD_cons_succ]
      apply ih (stepf w g) j (by simpa using hj)
      intro j' hj' i hi
      have := hrb (j' + 1) (by simpa using hj') i (by simpa using hi)
      omega

def WW (N : ℕ) (C : Circuit) (w : ℕ) (x : Fin N → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

theorem WW_in {N : ℕ} (C : Circuit) (w : ℕ) (hw : w < N) (x : Fin N → Bool) :
    WW N C w x = x ⟨w, hw⟩ := by
  unfold WW
  rw [wires_eq, fold_pre _ _ _ (by simpa using hw), List.getD_eq_getElem _ _ (by simpa using hw),
    List.getElem_ofFn]

theorem WW_out {N : ℕ} (C : Circuit) (w : ℕ) (hw : N + C.gates.length ≤ w) (x : Fin N → Bool) :
    WW N C w x = false := by
  unfold WW
  rw [wires_eq]
  apply List.getD_eq_default
  rw [fold_len]; simpa using hw

theorem WW_gate {N : ℕ} (C : Circuit) (hrb : ReadsBack N C) (j : ℕ) (hj : j < C.gates.length)
    (x : Fin N → Bool) :
    WW N C (N + j) x = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => WW N C i x) := by
  unfold WW
  rw [wires_eq]
  have := fold_gate C.gates (List.ofFn x) j hj
    (fun j hj i hi => by rw [List.length_ofFn]; exact hrb j hj i hi)
  rw [List.length_ofFn] at this
  exact this

theorem gateAt_mem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  unfold gateAt
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem hj


abbrev VV (n : ℕ) := Fin n → ZMod 2
abbrev PP (n : ℕ) := VV n × Submodule (ZMod 2) (VV n)

theorem zc (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

def kerS {n : ℕ} (w : VV n) : Submodule (ZMod 2) (VV n) where
  carrier := {d | dotProduct w d = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [dotProduct_add, ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at *
    rw [dotProduct_smul, ha, smul_zero]

theorem mem_kerS {n : ℕ} (w d : VV n) : d ∈ kerS w ↔ dotProduct w d = 0 := Iff.rfl

def inP {n : ℕ} (Q : PP n) (x : VV n) : Prop := x - Q.1 ∈ Q.2

theorem inP_trans {n : ℕ} {P Q : PP n} {x : VV n} (h1 : Q.2 ≤ P.2) (h2 : Q.1 - P.1 ∈ P.2)
    (h : inP Q x) : inP P x := by
  unfold inP at *
  have : x - P.1 = (x - Q.1) + (Q.1 - P.1) := by abel
  rw [this]
  exact P.2.add_mem (h1 h) h2

theorem refine {n : ℕ} (P : PP n) (w : VV n) :
    ∃ T : Finset (PP n), T.card ≤ 2 ∧
      (∀ Q ∈ T, Q.1 - P.1 ∈ P.2 ∧ Q.2 ≤ P.2 ∧
        Module.finrank (ZMod 2) P.2 ≤ Module.finrank (ZMod 2) Q.2 + 1 ∧
        ∀ x, inP Q x → dotProduct w x = dotProduct w Q.1) ∧
      (∀ x, inP P x → ∃! Q, Q ∈ T ∧ inP Q x) := by
  classical
  by_cases h : ∀ d ∈ P.2, dotProduct w d = 0
  · refine ⟨{P}, by simp, ?_, ?_⟩
    · intro Q hQ
      rw [Finset.mem_singleton] at hQ
      subst hQ
      refine ⟨by simp, le_rfl, by omega, ?_⟩
      intro x hx
      have := h _ hx
      rw [dotProduct_sub, sub_eq_zero] at this
      exact this
    · intro x hx
      refine ⟨P, ⟨Finset.mem_singleton_self _, hx⟩, ?_⟩
      rintro Q ⟨hQ, -⟩
      exact Finset.mem_singleton.mp hQ
  · push_neg at h
    obtain ⟨d0, hd0, hw⟩ := h
    have hw1 : dotProduct w d0 = 1 := by
      rcases zc (dotProduct w d0) with h | h
      · exact absurd h hw
      · exact h
    have hne : d0 ≠ 0 := by
      rintro rfl
      simp at hw1
    let D' : Submodule (ZMod 2) (VV n) := P.2 ⊓ kerS w
    let Q1 : PP n := (P.1, D')
    let Q2 : PP n := (P.1 + d0, D')
    have hrank : Module.finrank (ZMod 2) P.2 ≤ Module.finrank (ZMod 2) D' + 1 := by
      have hle : P.2 ≤ D' ⊔ (ZMod 2 ∙ d0) := by
        intro d hd
        rcases zc (dotProduct w d) with h0 | h1
        · exact Submodule.mem_sup_left (Submodule.mem_inf.mpr ⟨hd, h0⟩)
        · rw [Submodule.mem_sup]
          refine ⟨d - d0, Submodule.mem_inf.mpr ⟨P.2.sub_mem hd hd0, ?_⟩, d0,
            Submodule.mem_span_singleton_self d0, by abel⟩
          rw [mem_kerS, dotProduct_sub, h1, hw1, sub_self]
      calc Module.finrank (ZMod 2) P.2 ≤ Module.finrank (ZMod 2) ↥(D' ⊔ (ZMod 2 ∙ d0)) :=
            Submodule.finrank_mono hle
        _ ≤ Module.finrank (ZMod 2) D' + Module.finrank (ZMod 2) ↥(ZMod 2 ∙ d0) :=
            Submodule.finrank_add_le_finrank_add_finrank _ _
        _ = Module.finrank (ZMod 2) D' + 1 := by rw [finrank_span_singleton hne]
    have hq1 : ∀ x, inP Q1 x ↔ inP P x ∧ dotProduct w (x - P.1) = 0 := by
      intro x
      show x - P.1 ∈ P.2 ⊓ kerS w ↔ _
      rw [Submodule.mem_inf, mem_kerS]
      rfl
    have hq2 : ∀ x, inP Q2 x → dotProduct w (x - P.1) = 1 := by
      intro x hx
      have hx' : x - (P.1 + d0) ∈ P.2 ⊓ kerS w := hx
      rw [Submodule.mem_inf, mem_kerS] at hx'
      have : x - P.1 = (x - (P.1 + d0)) + d0 := by abel
      rw [this, dotProduct_add, hx'.2, hw1, zero_add]
    refine ⟨{Q1, Q2}, ?_, ?_, ?_⟩
    · exact (Finset.card_insert_le _ _).trans (by simp)
    · intro Q hQ
      rw [Finset.mem_insert, Finset.mem_singleton] at hQ
      rcases hQ with rfl | rfl
      · refine ⟨show P.1 - P.1 ∈ P.2 by simp, inf_le_left, hrank, ?_⟩
        intro x hx
        have := ((hq1 x).mp hx).2
        rw [dotProduct_sub, sub_eq_zero] at this
        exact this
      · refine ⟨show P.1 + d0 - P.1 ∈ P.2 by simpa using hd0, inf_le_left, hrank, ?_⟩
        intro x hx
        have hx' : x - (P.1 + d0) ∈ P.2 ⊓ kerS w := hx
        rw [Submodule.mem_inf, mem_kerS, dotProduct_sub, sub_eq_zero] at hx'
        exact hx'.2
    · intro x hx
      rcases zc (dotProduct w (x - P.1)) with h0 | h1
      · refine ⟨Q1, ⟨by simp, (hq1 x).mpr ⟨hx, h0⟩⟩, ?_⟩
        rintro Q ⟨hQ, hQx⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with rfl | rfl
        · rfl
        · have := hq2 x hQx
          rw [h0] at this
          exact absurd this (by decide)
      · have hx2 : inP Q2 x := by
          show x - (P.1 + d0) ∈ P.2 ⊓ kerS w
          rw [Submodule.mem_inf, mem_kerS]
          have : x - (P.1 + d0) = (x - P.1) - d0 := by abel
          rw [this, dotProduct_sub, h1, hw1, sub_self]
          exact ⟨P.2.sub_mem hx hd0, rfl⟩
        refine ⟨Q2, ⟨by simp, hx2⟩, ?_⟩
        rintro Q ⟨hQ, hQx⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hQ
        rcases hQ with rfl | rfl
        · have := ((hq1 x).mp hQx).2
          rw [h1] at this
          exact absurd this (by decide)
        · rfl

noncomputable def charged (g : Gate) : Bool := @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _)

noncomputable def costK (C : Circuit) (k : ℕ) : ℕ := (C.gates.take k).countP charged

def val (n : ℕ) (C : Circuit) (w : ℕ) (pt : VV n) : Bool :=
  (C.wires (List.ofFn (fun i : Fin n => decide (pt i = 1)))).getD w false

theorem val_eq (n : ℕ) (C : Circuit) (w : ℕ) (pt : VV n) :
    val n C w pt = WW n C w (fun i => decide (pt i = 1)) := rfl

def Aff {n : ℕ} (f : VV n → Bool) (Q : PP n) : Prop :=
  ∃ (weight : VV n) (offset : ZMod 2), ∀ pt, inP Q pt → f pt = decide (dotProduct weight pt + offset = 1)

theorem costK_succ (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    costK C (k + 1) = costK C k + (if charged (gateAt C k) then 1 else 0) := by
  unfold costK
  rw [List.take_succ, List.getElem?_eq_getElem hk, List.countP_append]
  have : gateAt C k = C.gates[k] := by unfold gateAt; rw [List.getD_eq_getElem _ _ hk]
  rw [this]
  cases h : charged C.gates[k] <;> simp [h]

theorem b1 (q : ZMod 2) : (!decide (q = 1)) = decide (q + 1 = 1) := by revert q; decide
theorem b1m (q : ZMod 2) : decide ([decide (q = 1)].count true % 2 = 0) = decide (q + 1 = 1) := by
  revert q; decide
theorem b2m (q r : ZMod 2) :
    decide ([decide (q = 1), decide (r = 1)].count true % 2 = 0) = decide (q + r + 1 = 1) := by
  revert q r; decide

theorem main_ind (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (hg : ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (U : Submodule (ZMod 2) (VV n)) (p : VV n) :
    ∀ k ≤ C.gates.length, ∃ S : Finset (PP n), S.card ≤ 2 ^ (costK C k) ∧
      (∀ Q ∈ S, Q.1 - p ∈ U ∧ Q.2 ≤ U ∧
        Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) Q.2 + costK C k) ∧
      (∀ x, x - p ∈ U → ∃! Q, Q ∈ S ∧ inP Q x) ∧
      (∀ Q ∈ S, ∀ w < n + k, Aff (val n C w) Q) := by
  classical
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨{(p, U)}, by simp [costK], ?_, ?_, ?_⟩
    · intro Q hQ
      rw [Finset.mem_singleton] at hQ
      subst hQ
      simp [costK]
    · intro x hx
      refine ⟨(p, U), ⟨Finset.mem_singleton_self _, hx⟩, ?_⟩
      rintro Q ⟨hQ, -⟩
      exact Finset.mem_singleton.mp hQ
    · intro Q _ w hw
      refine ⟨Pi.single ⟨w, by omega⟩ 1, 0, ?_⟩
      intro pt _
      rw [val_eq, WW_in C w (by omega), single_dotProduct, one_mul, add_zero]
  | succ k ih =>
    intro hk
    obtain ⟨S, hcard, hprop, hpart, haff⟩ := ih (by omega)
    have hkl : k < C.gates.length := by omega
    have hmem := gateAt_mem C k hkl
    have hrd := hrb k hkl
    have hval : ∀ pt, val n C (n + k) pt =
        (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => val n C i pt) := by
      intro pt
      rw [val_eq, WW_gate C hrb k hkl]
      rfl
    rcases hg _ hmem with ⟨hop, hlen⟩ | hrest
    · -- charged gate
      have hch : charged (gateAt C k) = true := by
        unfold charged; exact @decide_eq_true _ (Classical.propDecidable _) hop
      rw [costK_succ C k hkl, hch, if_pos rfl]
      obtain ⟨i1, i2, hin⟩ : ∃ i1 i2, (gateAt C k).inputs = [i1, i2] := by
        match h : (gateAt C k).inputs, hlen with
        | [a, b], _ => exact ⟨a, b, rfl⟩
      have hi1 : i1 < n + k := hrd i1 (by rw [hin]; simp)
      have hi2 : i2 < n + k := hrd i2 (by rw [hin]; simp)
      have hA : ∀ Q : PP n, ∃ (w1 : VV n) (c1 : ZMod 2), Q ∈ S → ∀ pt, inP Q pt →
          val n C i1 pt = decide (dotProduct w1 pt + c1 = 1) := by
        intro Q
        by_cases hQ : Q ∈ S
        · obtain ⟨w1, c1, h⟩ := haff Q hQ i1 hi1
          exact ⟨w1, c1, fun _ => h⟩
        · exact ⟨0, 0, fun h => absurd h hQ⟩
      choose W1 C1 hW using hA
      choose T hTc hTp hTu using fun Q : PP n => refine Q (W1 Q)
      refine ⟨S.biUnion T, ?_, ?_, ?_, ?_⟩
      · calc (S.biUnion T).card ≤ ∑ Q ∈ S, (T Q).card := Finset.card_biUnion_le
          _ ≤ ∑ _Q ∈ S, 2 := Finset.sum_le_sum (fun Q _ => hTc Q)
          _ = 2 * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
          _ ≤ 2 * 2 ^ costK C k := by omega
          _ = 2 ^ (costK C k + 1) := by rw [pow_succ]; ring
      · intro Q' hQ'
        obtain ⟨Q, hQ, hQ'T⟩ := Finset.mem_biUnion.mp hQ'
        obtain ⟨h1, h2, h3, -⟩ := hTp Q Q' hQ'T
        obtain ⟨g1, g2, g3⟩ := hprop Q hQ
        refine ⟨?_, h2.trans g2, by omega⟩
        have : Q'.1 - p = (Q'.1 - Q.1) + (Q.1 - p) := by abel
        rw [this]
        exact U.add_mem (g2 h1) g1
      · intro x hx
        obtain ⟨Q, ⟨hQ, hxQ⟩, hQu⟩ := hpart x hx
        obtain ⟨Q', ⟨hQ'T, hxQ'⟩, hQ'u⟩ := hTu Q x hxQ
        refine ⟨Q', ⟨Finset.mem_biUnion.mpr ⟨Q, hQ, hQ'T⟩, hxQ'⟩, ?_⟩
        rintro R ⟨hR, hxR⟩
        obtain ⟨P, hP, hRT⟩ := Finset.mem_biUnion.mp hR
        obtain ⟨r1, r2, -, -⟩ := hTp P R hRT
        have hPQ : P = Q := hQu P ⟨hP, inP_trans r2 r1 hxR⟩
        subst hPQ
        exact hQ'u R ⟨hRT, hxR⟩
      · intro Q' hQ' w hw
        obtain ⟨Q, hQ, hQ'T⟩ := Finset.mem_biUnion.mp hQ'
        obtain ⟨h1, h2, -, h4⟩ := hTp Q Q' hQ'T
        have hsub : ∀ pt, inP Q' pt → inP Q pt := fun pt h => inP_trans h2 h1 h
        by_cases hwk : w < n + k
        · obtain ⟨a, b, hab⟩ := haff Q hQ w hwk
          exact ⟨a, b, fun pt h => hab pt (hsub pt h)⟩
        · have hw' : w = n + k := by omega
          subst hw'
          obtain ⟨w2, c2, h2a⟩ := haff Q hQ i2 hi2
          have hc : ∀ pt, inP Q' pt → val n C i1 pt =
              decide (dotProduct (W1 Q) Q'.1 + C1 Q = 1) := by
            intro pt hpt
            rw [hW Q hQ pt (hsub pt hpt), h4 pt hpt]
          rcases hop with hand | hor
          · rcases zc (dotProduct (W1 Q) Q'.1 + C1 Q) with e | e
            · refine ⟨0, 0, fun pt hpt => ?_⟩
              rw [hval, hin, hand]
              simp only [List.map_cons, List.map_nil]
              rw [hc pt hpt, e]
              simp [GateOp.eval]
            · refine ⟨w2, c2, fun pt hpt => ?_⟩
              rw [hval, hin, hand]
              simp only [List.map_cons, List.map_nil]
              rw [hc pt hpt, e, ← h2a pt (hsub pt hpt)]
              simp [GateOp.eval]
          · rcases zc (dotProduct (W1 Q) Q'.1 + C1 Q) with e | e
            · refine ⟨w2, c2, fun pt hpt => ?_⟩
              rw [hval, hin, hor]
              simp only [List.map_cons, List.map_nil]
              rw [hc pt hpt, e, ← h2a pt (hsub pt hpt)]
              simp [GateOp.eval]
            · refine ⟨0, 1, fun pt hpt => ?_⟩
              rw [hval, hin, hor]
              simp only [List.map_cons, List.map_nil]
              rw [hc pt hpt, e]
              simp [GateOp.eval]
    · -- affine gate
      have hch : charged (gateAt C k) = false := by
        unfold charged
        rcases hrest with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp
      rw [costK_succ C k hkl, hch]
      simp only [Bool.false_eq_true, if_false, add_zero]
      refine ⟨S, hcard, hprop, hpart, ?_⟩
      intro Q hQ w hw
      by_cases hwk : w < n + k
      · exact haff Q hQ w hwk
      · have hw' : w = n + k := by omega
        subst hw'
        rcases hrest with ⟨hop, hlen⟩ | ⟨hop, hlen⟩
        · match h : (gateAt C k).inputs, hlen with
          | [], _ =>
            refine ⟨0, 1, fun pt _ => ?_⟩
            rw [hval, h, hop]
            simp [GateOp.eval]
          | [a], _ =>
            have ha : a < n + k := hrd a (by rw [h]; simp)
            obtain ⟨wa, ca, hA⟩ := haff Q hQ a ha
            refine ⟨wa, ca + 1, fun pt hpt => ?_⟩
            rw [hval, h, hop]
            simp only [List.map_cons, List.map_nil, GateOp.eval]
            rw [hA pt hpt, b1m, add_assoc]
          | [a, b], _ =>
            have ha : a < n + k := hrd a (by rw [h]; simp)
            have hb : b < n + k := hrd b (by rw [h]; simp)
            obtain ⟨wa, ca, hA⟩ := haff Q hQ a ha
            obtain ⟨wb, cb, hB⟩ := haff Q hQ b hb
            refine ⟨wa + wb, ca + cb + 1, fun pt hpt => ?_⟩
            rw [hval, h, hop]
            simp only [List.map_cons, List.map_nil, GateOp.eval]
            rw [hA pt hpt, hB pt hpt, b2m, add_dotProduct]
            congr 2
            ring
        · match h : (gateAt C k).inputs, hlen with
          | [a], _ =>
            have ha : a < n + k := hrd a (by rw [h]; simp)
            obtain ⟨wa, ca, hA⟩ := haff Q hQ a ha
            refine ⟨wa, ca + 1, fun pt hpt => ?_⟩
            rw [hval, h, hop]
            simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
            rw [hA pt hpt, b1, add_assoc]

theorem final (n : ℕ) (C : Circuit) (hrb : ReadsBack n C)
    (hg : ∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
      (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1))
    (U : Submodule (ZMod 2) (VV n)) (p : VV n) :
    ∃ (m : ℕ) (base : Fin m → VV n) (dir : Fin m → Submodule (ZMod 2) (VV n)),
      m ≤ 2 ^ (C.gates.countP charged) ∧ (∀ j, base j - p ∈ U ∧ dir j ≤ U ∧
        Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) (dir j) + C.gates.countP charged) ∧
      (∀ x : VV n, x - p ∈ U → ∃! j : Fin m, x - base j ∈ dir j) ∧
      ∀ (part : Fin m) (wire : ℕ), ∃ (weight : VV n) (offset : ZMod 2),
        ∀ point : VV n, point - base part ∈ dir part →
          val n C wire point = decide (dotProduct weight point + offset = 1) := by
  classical
  obtain ⟨S, hcard, hprop, hpart, haff⟩ := main_ind n C hrb hg U p C.gates.length le_rfl
  have hc : costK C C.gates.length = C.gates.countP charged := by
    unfold costK; rw [List.take_of_length_le le_rfl]
  rw [hc] at hcard hprop
  let e : Fin S.card ≃ {x // x ∈ S} := S.equivFin.symm
  refine ⟨S.card, fun j => (e j).1.1, fun j => (e j).1.2, hcard, ?_, ?_, ?_⟩
  · intro j
    exact hprop _ (e j).2
  · intro x hx
    obtain ⟨Q, ⟨hQ, hxQ⟩, hQu⟩ := hpart x hx
    refine ⟨e.symm ⟨Q, hQ⟩, ?_, ?_⟩
    · show inP (e (e.symm ⟨Q, hQ⟩)).1 x
      rw [Equiv.apply_symm_apply]
      exact hxQ
    · intro j hj
      have := hQu (e j).1 ⟨(e j).2, hj⟩
      rw [← Equiv.symm_apply_apply e j]
      congr 1
      exact Subtype.ext this
  · intro part wire
    by_cases hw : wire < n + C.gates.length
    · exact haff _ (e part).2 wire hw
    · refine ⟨0, 0, fun pt _ => ?_⟩
      rw [val_eq, WW_out C wire (by omega)]
      simp

end PEqualNP.Outside.L_lib_573

open PEqualNP.Outside.L_lib_573 in
theorem PEqualNP.Outside.L_lib_573 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let K := ZMod 2
  let X := Fin n → K
  let input := fun x : X => List.ofFn (fun i : Fin n => decide (x i = 1))
  let cost := C.gates.countP (fun g => @decide (g.op = .and ∨ g.op = .or) (Classical.propDecidable _))
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  (∀ g ∈ C.gates, ((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨ (g.op = .not ∧ g.inputs.length = 1)) →
  ∀ (U : Submodule K X) (p : X), ∃ (m : ℕ) (base : Fin m → X) (dir : Fin m → Submodule K X),
    m ≤ 2^cost ∧ (∀ j, base j - p ∈ U ∧ dir j ≤ U ∧
      Module.finrank K U ≤ Module.finrank K (dir j) + cost) ∧
    (∀ x : X, x-p ∈ U → ∃! j : Fin m, x-base j ∈ dir j) ∧
    ∀ (part : Fin m) (wire : ℕ), ∃ (weight : X) (offset : K),
      ∀ point : X, point-base part ∈ dir part →
        (C.wires (input point)).getD wire false = decide (dotProduct weight point + offset = 1) := by
  intro n C K X input cost hrb hg U p
  exact final n C hrb hg U p
