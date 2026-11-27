import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29726

open Finset

def z (b : Bool) : ZMod 2 := if b then 1 else 0

theorem z_true : z true = 1 := rfl
theorem z_false : z false = 0 := rfl

theorem z_xor (a b : Bool) : z (xor a b) = z a + z b := by
  cases a <;> cases b <;> decide

theorem z_dec (q : ZMod 2) : z (decide (q = 1)) = q := by
  revert q; decide

theorem z_inj {a b : Bool} (h : z a = z b) : a = b := by
  revert h; cases a <;> cases b <;> decide

def sg (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  revert a b; decide

theorem sg_zero : sg 0 = 1 := rfl

theorem sg_sum {ι : Type} (S : Finset ι) (f : ι → ZMod 2) :
    sg (∑ i ∈ S, f i) = ∏ i ∈ S, sg (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [sg_zero]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sg_add, ih]

def dot {s : ℕ} (u v : Fin s → ZMod 2) : ZMod 2 := ∑ i, u i * v i

theorem dot_add_right {s : ℕ} (u v w : Fin s → ZMod 2) :
    dot u (v + w) = dot u v + dot u w := by
  simp [dot, mul_add, Finset.sum_add_distrib]

theorem univ_zmod2 : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide

theorem sum_zmod2 (f : ZMod 2 → ℤ) : ∑ a, f a = f 0 + f 1 := by
  rw [univ_zmod2, Finset.sum_pair (by decide)]

theorem charsum {s : ℕ} (u : Fin s → ZMod 2) :
    ∑ p : Fin s → ZMod 2, sg (dot p u) = if u = 0 then 2 ^ s else 0 := by
  have h1 : ∀ p : Fin s → ZMod 2, sg (dot p u) = ∏ i, sg (p i * u i) := fun p => sg_sum _ _
  simp_rw [h1]
  have h3 := Finset.prod_univ_sum (fun _ : Fin s => (Finset.univ : Finset (ZMod 2)))
    (fun i a => sg (a * u i))
  rw [Fintype.piFinset_univ] at h3
  rw [← h3]
  have h2 : ∀ i, ∑ a : ZMod 2, sg (a * u i) = if u i = 0 then 2 else 0 := by
    intro i; rw [sum_zmod2]; generalize u i = q; revert q; decide
  simp_rw [h2]
  split_ifs with hu
  · subst hu; simp
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
      by_contra h; push Not at h; exact hu (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem add_eq_zero_iff2 {s : ℕ} (x w : Fin s → ZMod 2) : x + w = 0 ↔ x = w := by
  have h : ∀ a b : ZMod 2, a + b = 0 ↔ a = b := by decide
  simp only [funext_iff, Pi.add_apply, Pi.zero_apply, h]

theorem inversion {s : ℕ} (F : (Fin s → ZMod 2) → (Fin s → ZMod 2) → ZMod 2)
    (w1 w2 : Fin s → ZMod 2) :
    ∑ p, ∑ q, (∑ x, ∑ y, sg (F x y + dot p x + dot q y)) * sg (dot p w1 + dot q w2) =
      4 ^ s * sg (F w1 w2) := by
  have key : ∀ p q x y, sg (F x y + dot p x + dot q y) * sg (dot p w1 + dot q w2) =
      sg (F x y) * (sg (dot p (x + w1)) * sg (dot q (y + w2))) := by
    intros; simp only [dot_add_right, sg_add]; ring
  calc _ = ∑ p, ∑ q, ∑ x, ∑ y, sg (F x y) * (sg (dot p (x + w1)) * sg (dot q (y + w2))) := by
        simp_rw [Finset.sum_mul, key]
    _ = ∑ pq : (Fin s → ZMod 2) × (Fin s → ZMod 2), ∑ xy : (Fin s → ZMod 2) × (Fin s → ZMod 2),
          sg (F xy.1 xy.2) * (sg (dot pq.1 (xy.1 + w1)) * sg (dot pq.2 (xy.2 + w2))) := by
        simp only [Fintype.sum_prod_type]
    _ = ∑ xy : (Fin s → ZMod 2) × (Fin s → ZMod 2), ∑ pq : (Fin s → ZMod 2) × (Fin s → ZMod 2),
          sg (F xy.1 xy.2) * (sg (dot pq.1 (xy.1 + w1)) * sg (dot pq.2 (xy.2 + w2))) :=
        Finset.sum_comm
    _ = ∑ x, ∑ y, sg (F x y) * ((∑ p, sg (dot p (x + w1))) * (∑ q, sg (dot q (y + w2)))) := by
        simp only [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        simp only [Finset.mul_sum]
    _ = ∑ x, ∑ y, sg (F x y) * ((if x = w1 then 2 ^ s else 0) * (if y = w2 then 2 ^ s else 0)) := by
        simp only [charsum, add_eq_zero_iff2]
    _ = 4 ^ s * sg (F w1 w2) := by
        simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
        rw [show (4 : ℤ) ^ s = 2 ^ s * 2 ^ s by rw [← mul_pow]; norm_num]; ring

def zr {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (x y : Fin s → ZMod 2) (i : Fin s) : ZMod 2 :=
  (x i + ∑ j ∈ (Finset.Iio i).attach, A i j.1 * zr A B x y j.1) *
    (y i + ∑ j ∈ (Finset.Iio i).attach, B i j.1 * zr A B x y j.1)
termination_by i.val
decreasing_by all_goals (have h := Finset.mem_Iio.mp j.2; exact h)

theorem zr_eq {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (x y : Fin s → ZMod 2) (i : Fin s) :
    zr A B x y i = (x i + ∑ j ∈ Finset.Iio i, A i j * zr A B x y j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * zr A B x y j) := by
  rw [zr, Finset.sum_attach (Finset.Iio i) (fun j => A i j * zr A B x y j),
    Finset.sum_attach (Finset.Iio i) (fun j => B i j * zr A B x y j)]

theorem zr_unique {s : ℕ} (A B : Fin s → Fin s → ZMod 2) (x y : Fin s → ZMod 2)
    (G : Fin s → ZMod 2)
    (hG : ∀ i, G i = (x i + ∑ j ∈ Finset.Iio i, A i j * G j) *
      (y i + ∑ j ∈ Finset.Iio i, B i j * G j)) :
    ∀ k, ∀ i : Fin s, i.val = k → G i = zr A B x y i := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro i hi
    rw [hG i, zr_eq]
    have hs : ∀ j ∈ Finset.Iio i, G j = zr A B x y j := fun j hj =>
      ih j.val (by have h := Finset.mem_Iio.mp hj; rw [← hi]; exact h) j rfl
    congr 1 <;> congr 1 <;> exact Finset.sum_congr rfl (fun j hj => by rw [hs j hj])

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

def nl (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
      (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

def SS (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (fun j => nl (gateAt C j) = true)

def pos (C : Circuit) (k : Fin (SS C).card) : ℕ := (SS C).orderEmbOfFin rfl k

theorem pos_mem (C : Circuit) (k : Fin (SS C).card) : pos C k ∈ SS C :=
  Finset.orderEmbOfFin_mem _ _ _

theorem pos_lt_iff (C : Circuit) (k k' : Fin (SS C).card) : pos C k < pos C k' ↔ k < k' :=
  ((SS C).orderEmbOfFin rfl).lt_iff_lt

theorem pos_surj (C : Circuit) (j : ℕ) (hj : j ∈ SS C) : ∃ k, pos C k = j := by
  have : j ∈ Set.range ((SS C).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]; exact hj
  obtain ⟨k, hk⟩ := this
  exact ⟨k, hk⟩

theorem card_SS (C : Circuit) : (SS C).card = C.gates.countP nl := by
  unfold SS gateAt
  generalize C.gates = l
  induction l with
  | nil => simp
  | cons g l ih =>
    simp only [Finset.card_filter] at ih ⊢
    rw [List.length_cons, Finset.sum_range_succ', List.countP_cons, ← ih]
    simp [List.getD_cons_succ, List.getD_cons_zero]

theorem exp2 (f : List Bool → Bool) (a b : Bool) :
    z (f [a, b]) = z (f [false, false]) + (z (f [true, false]) + z (f [false, false])) * z a +
      (z (f [false, true]) + z (f [false, false])) * z b +
      (z (f [false, false]) + z (f [false, true]) + z (f [true, false]) + z (f [true, true])) *
        (z a * z b) := by
  cases h1 : f [false, false] <;> cases h2 : f [false, true] <;> cases h3 : f [true, false] <;>
    cases h4 : f [true, true] <;> cases a <;> cases b <;> simp only [h1, h2, h3, h4] <;> decide

theorem exp1 (f : List Bool → Bool) (a : Bool) :
    z (f [a]) = z (f [false]) + (z (f [true]) + z (f [false])) * z a := by
  cases h1 : f [false] <;> cases h2 : f [true] <;> cases a <;> simp only [h1, h2] <;> decide

theorem coef_nl (g : Gate) (h : nl g = true) :
    z (g.op.eval [false,false]) + z (g.op.eval [false,true]) + z (g.op.eval [true,false]) +
      z (g.op.eval [true,true]) = 1 := by
  unfold nl at h
  rw [Bool.and_eq_true] at h
  have h2 := congrArg z h.2
  rw [z_xor, z_xor, z_xor, z_true] at h2
  rw [← h2]; ring

theorem coef_lin (g : Gate) (h : nl g = false) (hl : g.inputs.length = 2) :
    z (g.op.eval [false,false]) + z (g.op.eval [false,true]) + z (g.op.eval [true,false]) +
      z (g.op.eval [true,true]) = 0 := by
  unfold nl at h
  rw [show (g.inputs.length == 2) = true by simp [hl], Bool.true_and] at h
  have h2 := congrArg z h
  rw [z_xor, z_xor, z_xor, z_false] at h2
  rw [← h2]; ring

def i1 (C : Circuit) (k : Fin (SS C).card) : ℕ := (gateAt C (pos C k)).inputs.getD 0 0
def i2 (C : Circuit) (k : Fin (SS C).card) : ℕ := (gateAt C (pos C k)).inputs.getD 1 0
def ev (C : Circuit) (k : Fin (SS C).card) (a b : Bool) : ZMod 2 :=
  z ((gateAt C (pos C k)).op.eval [a, b])
def bet (C : Circuit) (k : Fin (SS C).card) : ZMod 2 := ev C k false true + ev C k false false
def alp (C : Circuit) (k : Fin (SS C).card) : ZMod 2 := ev C k true false + ev C k false false
def GG (N : ℕ) (C : Circuit) (k : Fin (SS C).card) (x : Fin N → Bool) : ZMod 2 :=
  (z (WW N C (i1 C k) x) + bet C k) * (z (WW N C (i2 C k) x) + alp C k)

theorem nl_pos (C : Circuit) (k : Fin (SS C).card) : nl (gateAt C (pos C k)) = true := by
  have := pos_mem C k
  simp only [SS, Finset.mem_filter] at this
  exact this.2

theorem pos_lt_len (C : Circuit) (k : Fin (SS C).card) : pos C k < C.gates.length := by
  have := pos_mem C k
  simp only [SS, Finset.mem_filter, Finset.mem_range] at this
  exact this.1

theorem inputs_eq (C : Circuit) (k : Fin (SS C).card) :
    (gateAt C (pos C k)).inputs = [i1 C k, i2 C k] := by
  have h := nl_pos C k
  unfold nl at h
  rw [Bool.and_eq_true] at h
  have hl : (gateAt C (pos C k)).inputs.length = 2 := by simpa using h.1
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hl
  simp only [i1, i2, hab, List.getD_cons_zero, List.getD_cons_succ]

theorem comb {N s : ℕ} (c1 c2 e α β : ZMod 2) (l1 l2 : Fin N → ZMod 2) (μ1 μ2 : Fin s → ZMod 2)
    (G : Fin s → (Fin N → Bool) → ZMod 2) (Wp Wq Ww : (Fin N → Bool) → ZMod 2)
    (h1 : ∀ x, Wp x = c1 + ∑ r, l1 r * z (x r) + ∑ k, μ1 k * G k x)
    (h2 : ∀ x, Wq x = c2 + ∑ r, l2 r * z (x r) + ∑ k, μ2 k * G k x)
    (h : ∀ x, Ww x = e + α * Wp x + β * Wq x) :
    ∀ x, Ww x = (e + α * c1 + β * c2) + ∑ r, (α * l1 r + β * l2 r) * z (x r) +
      ∑ k, (α * μ1 k + β * μ2 k) * G k x := by
  intro x
  rw [h, h1, h2]
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem form_exists (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) :
    ∀ w, ∃ (c : ZMod 2) (l : Fin N → ZMod 2) (μ : Fin (SS C).card → ZMod 2),
      (∀ x, z (WW N C w x) = c + ∑ r, l r * z (x r) + ∑ k, μ k * GG N C k x) ∧
      ∀ k, μ k ≠ 0 → N + pos C k ≤ w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
  by_cases hw : w < N
  · refine ⟨0, fun r => if r = ⟨w, hw⟩ then 1 else 0, 0, fun x => ?_, fun k hk => absurd rfl hk⟩
    rw [WW_in C w hw]
    simp [Finset.sum_ite_eq']
  by_cases hw2 : w < N + C.gates.length
  · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
    have hj : j < C.gates.length := by omega
    have hg := WW_gate C hrb j hj
    have hlen := hfan _ (gateAt_mem C j hj)
    have hrj : ∀ i ∈ (gateAt C j).inputs, i < N + j := hrb j hj
    by_cases hnl : nl (gateAt C j) = true
    · obtain ⟨k, hk⟩ := pos_surj C j (by simp [SS, hj, hnl])
      subst hk
      have hin := inputs_eq C k
      refine ⟨ev C k false false + bet C k * alp C k, 0, Pi.single k 1, fun x => ?_,
        fun k' hk' => ?_⟩
      · rw [hg, hin]
        simp only [List.map_cons, List.map_nil]
        rw [exp2 (gateAt C (pos C k)).op.eval, coef_nl _ hnl]
        simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, Pi.single_apply,
          ite_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        unfold GG bet alp ev
        generalize z (WW N C (i1 C k) x) = a
        generalize z (WW N C (i2 C k) x) = b
        generalize z ((gateAt C (pos C k)).op.eval [false, false]) = p
        generalize z ((gateAt C (pos C k)).op.eval [false, true]) = q
        generalize z ((gateAt C (pos C k)).op.eval [true, false]) = r
        revert a b p q r; decide
      · have : k' = k := by
          by_contra hne; exact hk' (by simp [Pi.single_apply, hne])
        subst this; exact le_rfl
    · have hnl' : nl (gateAt C j) = false := by simpa using hnl
      rcases hL : (gateAt C j).inputs with _ | ⟨p, _ | ⟨q, _ | ⟨r, rest⟩⟩⟩
      · refine ⟨z ((gateAt C j).op.eval []), 0, 0, fun x => ?_, fun k hk => absurd rfl hk⟩
        rw [hg, hL]; simp
      · have hp : p < N + j := hrj p (by simp [hL])
        obtain ⟨c1, l1, μ1, h1, s1⟩ := ih p hp
        have hh : ∀ x, z (WW N C (N + j) x) = z ((gateAt C j).op.eval [false]) +
            (z ((gateAt C j).op.eval [true]) + z ((gateAt C j).op.eval [false])) *
              z (WW N C p x) + 0 * z (WW N C p x) := by
          intro x; rw [hg, hL]; simp only [List.map_cons, List.map_nil]
          rw [exp1 (gateAt C j).op.eval]; ring
        refine ⟨_, _, _, comb c1 c1 _ _ 0 l1 l1 μ1 μ1 (GG N C) (fun x => z (WW N C p x))
          (fun x => z (WW N C p x)) (fun x => z (WW N C (N + j) x)) h1 h1 hh, fun k hk => ?_⟩
        have : μ1 k ≠ 0 := by
          intro h0; apply hk; simp [h0]
        have := s1 k this; omega
      · have hp : p < N + j := hrj p (by simp [hL])
        have hq : q < N + j := hrj q (by simp [hL])
        obtain ⟨c1, l1, μ1, h1, s1⟩ := ih p hp
        obtain ⟨c2, l2, μ2, h2, s2⟩ := ih q hq
        have h0 := coef_lin _ hnl' (by simp [hL])
        have hh : ∀ x, z (WW N C (N + j) x) = z ((gateAt C j).op.eval [false, false]) +
            (z ((gateAt C j).op.eval [true, false]) + z ((gateAt C j).op.eval [false, false])) *
              z (WW N C p x) +
            (z ((gateAt C j).op.eval [false, true]) + z ((gateAt C j).op.eval [false, false])) *
              z (WW N C q x) := by
          intro x; rw [hg, hL]; simp only [List.map_cons, List.map_nil]
          rw [exp2 (gateAt C j).op.eval, h0]; ring
        refine ⟨_, _, _, comb c1 c2 _ _ _ l1 l2 μ1 μ2 (GG N C) (fun x => z (WW N C p x))
          (fun x => z (WW N C q x)) (fun x => z (WW N C (N + j) x)) h1 h2 hh, fun k hk => ?_⟩
        by_cases hk1 : μ1 k = 0
        · have : μ2 k ≠ 0 := by
            intro h0; apply hk; simp [h0, hk1]
          have := s2 k this; omega
        · have := s1 k hk1; omega
      · exfalso; rw [hL] at hlen; simp at hlen
  · refine ⟨0, 0, 0, fun x => ?_, fun k hk => absurd rfl hk⟩
    rw [WW_out C w (by omega)]; simp [z]


theorem sg_one : sg 1 = -1 := rfl

theorem sg_dbl (a : ZMod 2) : sg (a + a) = 1 := by revert a; decide

theorem dot_eq_dp {s : ℕ} (u v : Fin s → ZMod 2) : dot u v = u ⬝ᵥ v := rfl

theorem sg_mul_le (q : ZMod 2) (y : ℤ) : sg q * y ≤ |y| := by
  unfold sg; split_ifs
  · simpa using le_abs_self y
  · simpa using neg_le_abs y

theorem cardV (N : ℕ) : Fintype.card (Fin N → ZMod 2) = 2 ^ N := by
  simp [Fintype.card_fun, ZMod.card]

def xb {N : ℕ} (x : Fin N → ZMod 2) : Fin N → Bool := fun i => decide (x i = 1)

def Wz (N : ℕ) (C : Circuit) (w : ℕ) (x : Fin N → ZMod 2) : ZMod 2 := z (WW N C w (xb x))

def GZ (N : ℕ) (C : Circuit) (k : Fin (SS C).card) (x : Fin N → ZMod 2) : ZMod 2 :=
  (Wz N C (i1 C k) x + bet C k) * (Wz N C (i2 C k) x + alp C k)

theorem form_z (N : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (w : ℕ) :
    ∃ (c : ZMod 2) (l : Fin N → ZMod 2) (μ : Fin (SS C).card → ZMod 2),
      (∀ x, Wz N C w x = c + l ⬝ᵥ x + ∑ k, μ k * GZ N C k x) ∧
      ∀ k, μ k ≠ 0 → N + pos C k ≤ w := by
  obtain ⟨c, l, μ, h, hs⟩ := form_exists N C hrb hfan w
  refine ⟨c, l, μ, fun x => ?_, hs⟩
  have h2 := h (xb x)
  have hz : ∀ r, z (xb x r) = x r := fun r => z_dec _
  simp only [hz] at h2
  exact h2

theorem i1_lt (N : ℕ) (C : Circuit) (hrb : ReadsBack N C) (k : Fin (SS C).card) :
    i1 C k < N + pos C k :=
  hrb (pos C k) (pos_lt_len C k) (i1 C k) (by rw [inputs_eq]; simp)

theorem i2_lt (N : ℕ) (C : Circuit) (hrb : ReadsBack N C) (k : Fin (SS C).card) :
    i2 C k < N + pos C k :=
  hrb (pos C k) (pos_lt_len C k) (i2 C k) (by rw [inputs_eq]; simp)

theorem shift_inv (N : ℕ) (C : Circuit) (hrb : ReadsBack N C) (cF : ℕ → ZMod 2)
    (lF : ℕ → Fin N → ZMod 2) (μF : ℕ → Fin (SS C).card → ZMod 2)
    (hF : ∀ w x, Wz N C w x = cF w + lF w ⬝ᵥ x + ∑ k, μF w k * GZ N C k x)
    (hS : ∀ w k, μF w k ≠ 0 → N + pos C k ≤ w) (y : Fin N → ZMod 2)
    (hy : ∀ k, lF (i1 C k) ⬝ᵥ y = 0 ∧ lF (i2 C k) ⬝ᵥ y = 0) :
    ∀ w x, Wz N C w (x + y) = Wz N C w x + lF w ⬝ᵥ y := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro x
    have hs : ∑ k, μF w k * GZ N C k (x + y) = ∑ k, μF w k * GZ N C k x := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hμ : μF w k = 0
      · rw [hμ, zero_mul, zero_mul]
      · have hw := hS w k hμ
        unfold GZ
        rw [ih (i1 C k) (by have := i1_lt N C hrb k; omega) x,
          ih (i2 C k) (by have := i2_lt N C hrb k; omega) x, (hy k).1, (hy k).2, add_zero,
          add_zero]
    rw [hF w (x + y), hF w x, hs, dotProduct_add]
    ring

def fo {N : ℕ} (g : (Fin N → ZMod 2) → ZMod 2) (u : Fin N → ZMod 2) : ℤ :=
  ∑ x, sg (g x + u ⬝ᵥ x)

theorem fo_zero {N : ℕ} (g : (Fin N → ZMod 2) → ZMod 2) (l y u : Fin N → ZMod 2)
    (hg : ∀ x, g (x + y) = g x + l ⬝ᵥ y) (h1 : (l + u) ⬝ᵥ y = 1) : fo g u = 0 := by
  have e : fo g u = ∑ x, sg (g (x + y) + u ⬝ᵥ (x + y)) := by
    rw [fo]
    exact (Fintype.sum_equiv (Equiv.addRight y) (fun x => sg (g (x + y) + u ⬝ᵥ (x + y)))
      (fun x => sg (g x + u ⬝ᵥ x)) (fun x => rfl)).symm
  have e2 : ∀ x, sg (g (x + y) + u ⬝ᵥ (x + y)) = - sg (g x + u ⬝ᵥ x) := by
    intro x
    have : g (x + y) + u ⬝ᵥ (x + y) = (g x + u ⬝ᵥ x) + 1 := by
      rw [hg, dotProduct_add, ← h1, add_dotProduct]; ring
    rw [this, sg_add, sg_one]; ring
  have h3 : fo g u = - fo g u := by
    conv_lhs => rw [e]
    simp only [e2, Finset.sum_neg_distrib]
    rfl
  linarith

theorem parseval {N : ℕ} (g : (Fin N → ZMod 2) → ZMod 2) :
    ∑ u, fo g u ^ 2 = ((2 : ℤ) ^ N) ^ 2 := by
  have h1 : ∀ u, fo g u ^ 2 = ∑ x, ∑ x', sg (g x + g x') * sg (dot u (x + x')) := by
    intro u
    rw [fo, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
    rw [← sg_add, ← sg_add, dot_eq_dp, dotProduct_add]
    congr 1
    ring
  simp_rw [h1]
  calc _ = ∑ x : Fin N → ZMod 2, ∑ x' : Fin N → ZMod 2, ∑ u : Fin N → ZMod 2,
        sg (g x + g x') * sg (dot u (x + x')) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun x _ => Finset.sum_comm)
    _ = ∑ x : Fin N → ZMod 2, ∑ x' : Fin N → ZMod 2,
        sg (g x + g x') * (if x = x' then 2 ^ N else 0) := by
        simp only [← Finset.mul_sum, charsum, add_eq_zero_iff2]
    _ = ∑ x : Fin N → ZMod 2, (2 : ℤ) ^ N := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, sg_dbl,
          one_mul]
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, cardV]
        simp only [nsmul_eq_mul]
        push_cast
        ring

theorem nl_and (g : Gate)
    (hg : (g.op = .and ∧ g.inputs.length = 2) ∨ (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
      (g.op = .not ∧ g.inputs.length = 1)) (h : nl g = true) : g.op = .and := by
  rcases hg with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
  · exact h1
  · exfalso
    unfold nl at h
    rw [h1] at h
    have e : xor (xor ((GateOp.mod 2).eval [false,false]) ((GateOp.mod 2).eval [false,true]))
        (xor ((GateOp.mod 2).eval [true,false]) ((GateOp.mod 2).eval [true,true])) = false := by
      decide
    rw [e, Bool.and_false] at h
    exact Bool.false_ne_true h
  · exfalso
    unfold nl at h
    rw [h2] at h
    exact Bool.false_ne_true h

theorem zm_one (q : ZMod 2) (h : q ≠ 0) : q = 1 := by revert q h; decide

theorem sg_lin (q : ZMod 2) : sg q = 1 - 2 * (if q = 1 then 1 else 0) := by revert q; decide

theorem rank_ker {N r h : ℕ} (P : Fin r → Fin N → ZMod 2) (hr : r + h ≤ N) :
    h ≤ Module.finrank (ZMod 2) (LinearMap.ker (Matrix.mulVecLin (Matrix.of P))) := by
  have e1 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin (Matrix.of P))
  have e2 := Submodule.finrank_le (LinearMap.range (Matrix.mulVecLin (Matrix.of P)))
  rw [Module.finrank_fin_fun] at e1 e2
  omega

theorem indep_sub {N : ℕ} (S : Submodule (ZMod 2) (Fin N → ZMod 2)) (h : ℕ)
    (hdim : h ≤ Module.finrank (ZMod 2) S) :
    ∃ yv : Fin h → (Fin N → ZMod 2), LinearIndependent (ZMod 2) yv ∧ ∀ i, yv i ∈ S := by
  let bs := Module.finBasis (ZMod 2) S
  have hl : LinearIndependent (ZMod 2) (S.subtype ∘ (bs ∘ Fin.castLE hdim)) :=
    (bs.linearIndependent.comp (Fin.castLE hdim) (Fin.castLE_injective hdim)).map'
      S.subtype (Submodule.ker_subtype S)
  exact ⟨S.subtype ∘ (bs ∘ Fin.castLE hdim), hl, fun i => (bs (Fin.castLE hdim i)).2⟩

theorem indep_ker {N r h : ℕ} (P : Fin r → Fin N → ZMod 2) (hr : r + h ≤ N) :
    ∃ yv : Fin h → (Fin N → ZMod 2), LinearIndependent (ZMod 2) yv ∧ ∀ i k, P k ⬝ᵥ yv i = 0 := by
  obtain ⟨yv, hl, hm⟩ := indep_sub _ h (rank_ker P hr)
  refine ⟨yv, hl, fun i k => ?_⟩
  have hy := hm i
  rw [LinearMap.mem_ker] at hy
  have := congrFun hy k
  simpa [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.of_apply] using this

theorem lin_part (N h : ℕ) (C : Circuit) (hrb : ReadsBack N C)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hS : 2 * (SS C).card + h ≤ N) :
    ∃ (lo : Fin N → ZMod 2) (yv : Fin h → (Fin N → ZMod 2)), LinearIndependent (ZMod 2) yv ∧
      ∀ i x, Wz N C C.output (x + yv i) = Wz N C C.output x + lo ⬝ᵥ yv i := by
  choose cF lF μF hF hSF using form_z N C hrb hfan
  obtain ⟨yv, hl, hz⟩ := indep_ker (Fin.append (fun k => lF (i1 C k)) (fun k => lF (i2 C k)))
    (by omega : (SS C).card + (SS C).card + h ≤ N)
  refine ⟨lF C.output, yv, hl, fun i x =>
    shift_inv N C hrb cF lF μF hF hSF _ (fun k => ⟨?_, ?_⟩) C.output x⟩
  · have := hz i (Fin.castAdd _ k); rwa [Fin.append_left] at this
  · have := hz i (Fin.natAdd _ k); rwa [Fin.append_right] at this

theorem sum_sg_v {N m : ℕ} (v : Fin m → (Fin N → ZMod 2)) (y : Fin N → ZMod 2) :
    ∑ j, sg (v j ⬝ᵥ y) =
      (m : ℤ) - 2 * (((Finset.univ : Finset (Fin m)).filter (fun j => v j ⬝ᵥ y = 1)).card : ℤ) := by
  simp only [sg_lin, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp

theorem count_J (N m h D E : ℕ) (v : Fin m → (Fin N → ZMod 2))
    (hbias : ∀ x : Fin N → ZMod 2, x ≠ 0 →
      D * ((m : ℤ) - 2 * (((Finset.univ : Finset (Fin m)).filter
        (fun j => v j ⬝ᵥ x = 1)).card : ℤ)).natAbs ≤ E * m)
    (lo : Fin N → ZMod 2) (yv : Fin h → (Fin N → ZMod 2)) (hli : LinearIndependent (ZMod 2) yv) :
    (D : ℤ) * 2 ^ h * ((Finset.univ : Finset (Fin m)).filter
      (fun j => (fun i => (lo + v j) ⬝ᵥ yv i) = 0)).card ≤ D * m + (2 ^ h - 1) * E * m := by
  classical
  let a : Fin m → Fin h → ZMod 2 := fun j i => (lo + v j) ⬝ᵥ yv i
  let Yt : (Fin h → ZMod 2) → (Fin N → ZMod 2) := fun t => ∑ i, t i • yv i
  have hY0 : ∀ t, t ≠ 0 → Yt t ≠ 0 := by
    intro t ht hz
    apply ht; funext i
    exact Fintype.linearIndependent_iff.mp hli t hz i
  have hc1 : ∀ j, ∑ t : Fin h → ZMod 2, sg (dot t (a j)) =
      (2 ^ h : ℤ) * (if a j = 0 then 1 else 0) := by
    intro j; rw [charsum]; split_ifs <;> simp
  have hsum : (2 ^ h : ℤ) * ((Finset.univ : Finset (Fin m)).filter (fun j => a j = 0)).card =
      ∑ j, ∑ t : Fin h → ZMod 2, sg (dot t (a j)) := by
    simp only [hc1, ← Finset.mul_sum, Finset.sum_boole]
  have hdot : ∀ j t, dot t (a j) = lo ⬝ᵥ Yt t + v j ⬝ᵥ Yt t := by
    intro j t
    show ∑ i, t i * ((lo + v j) ⬝ᵥ yv i) = _
    rw [← add_dotProduct, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
  have hsw : ∑ j, ∑ t : Fin h → ZMod 2, sg (dot t (a j)) =
      ∑ t : Fin h → ZMod 2, sg (lo ⬝ᵥ Yt t) * ∑ j, sg (v j ⬝ᵥ Yt t) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hdot, sg_add]
  have hle1 : ∑ t : Fin h → ZMod 2, sg (lo ⬝ᵥ Yt t) * ∑ j, sg (v j ⬝ᵥ Yt t) ≤
      ∑ t : Fin h → ZMod 2, |∑ j, sg (v j ⬝ᵥ Yt t)| :=
    Finset.sum_le_sum (fun t _ => sg_mul_le _ _)
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin h → ZMod 2))
    (fun t => |∑ j, sg (v j ⬝ᵥ Yt t)|) (Finset.mem_univ 0)
  have h0 : |∑ j, sg (v j ⬝ᵥ Yt 0)| = m := by
    have : Yt 0 = 0 := by simp [Yt]
    rw [this]
    simp [dotProduct_zero, sg_zero]
  have hrest : ∑ t ∈ (Finset.univ : Finset (Fin h → ZMod 2)).erase 0,
      (D : ℤ) * |∑ j, sg (v j ⬝ᵥ Yt t)| ≤
      ∑ t ∈ (Finset.univ : Finset (Fin h → ZMod 2)).erase 0, (E : ℤ) * m := by
    refine Finset.sum_le_sum (fun t ht => ?_)
    have ht0 : t ≠ 0 := Finset.ne_of_mem_erase ht
    have hb := hbias (Yt t) (hY0 t ht0)
    have hb' : ((D * ((m : ℤ) - 2 * (((Finset.univ : Finset (Fin m)).filter
        (fun j => v j ⬝ᵥ Yt t = 1)).card : ℤ)).natAbs : ℕ) : ℤ) ≤ ((E * m : ℕ) : ℤ) :=
      Nat.cast_le.mpr hb
    push_cast [Int.natCast_natAbs] at hb'
    rw [sum_sg_v]
    exact hb'
  have hcard : (((Finset.univ : Finset (Fin h → ZMod 2)).erase 0).card : ℤ) = 2 ^ h - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, cardV,
      Nat.cast_sub Nat.one_le_two_pow]
    push_cast; ring
  rw [Finset.sum_const, nsmul_eq_mul, hcard] at hrest
  have hD0 : (0 : ℤ) ≤ D := by positivity
  calc (D : ℤ) * 2 ^ h * ((Finset.univ : Finset (Fin m)).filter (fun j => a j = 0)).card
        = D * ((2 ^ h : ℤ) * ((Finset.univ : Finset (Fin m)).filter (fun j => a j = 0)).card) := by
        ring
    _ ≤ D * ∑ t : Fin h → ZMod 2, |∑ j, sg (v j ⬝ᵥ Yt t)| := by
        rw [hsum, hsw]; exact mul_le_mul_of_nonneg_left hle1 hD0
    _ = D * m + ∑ t ∈ (Finset.univ : Finset (Fin h → ZMod 2)).erase 0,
        (D : ℤ) * |∑ j, sg (v j ⬝ᵥ Yt t)| := by
        rw [← hsplit, mul_add, Finset.mul_sum]
        simp only [h0]
    _ ≤ D * m + (2 ^ h - 1) * (E * m) := by linarith
    _ = _ := by ring

theorem dec_lin (d : Bool → ZMod 2) (b : Bool) : d b = d false + (d true + d false) * z b := by
  cases b
  · simp [z]
  · rw [z_true, mul_one]; generalize d true = p; generalize d false = q; revert p q; decide

theorem zm_cases (q : ZMod 2) : q = 0 ∨ q = 1 := by revert q; decide

theorem sg_eq (a b : ZMod 2) : sg (a + b) = 2 * (if a = b then 1 else 0) - 1 := by
  revert a b; decide

theorem term_le {N : ℕ} (g : (Fin N → ZMod 2) → ZMod 2) (bit : (Fin N → ZMod 2) → Bool)
    (hg : ∀ x, g x = z (bit x)) (d : Bool → ZMod 2) (u : Fin N → ZMod 2) (hu : u ≠ 0) :
    ∑ x, sg (d (bit x) + u ⬝ᵥ x) ≤ |fo g u| := by
  have hd : ∀ x, d (bit x) + u ⬝ᵥ x = d false + ((d true + d false) * g x + u ⬝ᵥ x) := by
    intro x; rw [dec_lin d (bit x), hg]; ring
  simp only [hd, sg_add (d false)]
  rw [← Finset.mul_sum]
  rcases zm_cases (d true + d false) with h0 | h1
  · rw [h0]
    simp only [zero_mul, zero_add]
    have : ∑ x : Fin N → ZMod 2, sg (u ⬝ᵥ x) = ∑ x : Fin N → ZMod 2, sg (dot x u) := by
      refine Finset.sum_congr rfl (fun x _ => ?_); rw [dot_eq_dp, dotProduct_comm]
    rw [this, charsum, if_neg hu, mul_zero]; exact abs_nonneg _
  · rw [h1]
    simp only [one_mul]
    exact sg_mul_le _ (fo g u)

theorem gain_eq (N m : ℕ) (K : Finset (Fin m)) (P : (Fin N → ZMod 2) → Fin m → ZMod 2)
    (Q : (Fin N → ZMod 2) → Fin m → ZMod 2) :
    (2 * ((∑ x : Fin N → ZMod 2, (K.filter (fun j => P x j = Q x j)).card : ℕ) : ℤ) -
      2 ^ N * K.card) = ∑ j ∈ K, ∑ x, sg (P x j + Q x j) := by
  simp only [sg_eq]
  rw [Finset.sum_comm]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, cardV, ← Finset.mul_sum,
    Finset.sum_boole, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem cs_bound {N m : ℕ} (g : (Fin N → ZMod 2) → ZMod 2) (v : Fin m ↪ (Fin N → ZMod 2))
    (K J : Finset (Fin m)) (hJ : ∀ j, j ∉ J → fo g (v j) = 0) :
    (∑ j ∈ K, |fo g (v j)|) ^ 2 ≤ (J.card : ℤ) * ((2 : ℤ) ^ N) ^ 2 := by
  classical
  have e1 : ∑ j ∈ K, |fo g (v j)| = ∑ j ∈ K.filter (· ∈ J), |fo g (v j)| := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs with hj
    · rfl
    · rw [hJ j hj, abs_zero]
  rw [e1, ← parseval g]
  calc _ ≤ ((K.filter (· ∈ J)).card : ℤ) * ∑ j ∈ K.filter (· ∈ J), |fo g (v j)| ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (J.card : ℤ) * ∑ u, fo g u ^ 2 := by
        apply mul_le_mul
        · exact_mod_cast Finset.card_le_card (fun j hj => (Finset.mem_filter.mp hj).2)
        · calc _ ≤ ∑ j, |fo g (v j)| ^ 2 :=
                Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
            _ = ∑ u ∈ Finset.univ.map v, fo g u ^ 2 := by rw [Finset.sum_map]; simp [sq_abs]
            _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
        · exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        · positivity

theorem main_bound (N m h D E : ℕ) (v : Fin m ↪ (Fin N → ZMod 2)) (hv0 : ∀ j, v j ≠ 0)
    (hbias : ∀ x : Fin N → ZMod 2, x ≠ 0 →
      D * ((m : ℤ) - 2 * (((Finset.univ : Finset (Fin m)).filter
        (fun j => v j ⬝ᵥ x = 1)).card : ℤ)).natAbs ≤ E * m)
    (C : Circuit) (hrb : ReadsBack N C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hS : 2 * (SS C).card + h ≤ N) (K : Finset (Fin m)) (dec : Bool → Fin m → ZMod 2) :
    2 ^ h * D * (2 * (∑ x : Fin N → ZMod 2,
      (K.filter (fun j => dec (WW N C C.output (xb x)) j = v j ⬝ᵥ x)).card) -
        2 ^ N * K.card) ^ 2 ≤ (D + (2 ^ h - 1) * E) * m * (2 ^ N) ^ 2 := by
  classical
  obtain ⟨lo, yv, hli, hinv⟩ := lin_part N h C hrb hfan hS
  let g : (Fin N → ZMod 2) → ZMod 2 := fun x => Wz N C C.output x
  let J := (Finset.univ : Finset (Fin m)).filter (fun j => (fun i => (lo + v j) ⬝ᵥ yv i) = 0)
  have hJ : ∀ j, j ∉ J → fo g (v j) = 0 := by
    intro j hj
    have hex : ∃ i, (lo + v j) ⬝ᵥ yv i ≠ 0 := by
      by_contra hc
      simp only [not_exists, ne_eq, not_not] at hc
      exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, funext hc⟩)
    obtain ⟨i, hi⟩ := hex
    exact fo_zero g lo (yv i) (v j) (hinv i) (zm_one _ hi)
  have hcount := count_J N m h D E v hbias lo yv hli
  have hGR : (2 * ((∑ x : Fin N → ZMod 2,
      (K.filter (fun j => dec (WW N C C.output (xb x)) j = v j ⬝ᵥ x)).card : ℕ) : ℤ)) -
        2 ^ N * K.card ≤ ∑ j ∈ K, |fo g (v j)| := by
    rw [gain_eq N m K (fun x j => dec (WW N C C.output (xb x)) j) (fun x j => v j ⬝ᵥ x)]
    exact Finset.sum_le_sum (fun j _ => term_le g (fun x => WW N C C.output (xb x))
      (fun x => rfl) (fun b => dec b j) (v j) (hv0 j))
  have hR0 : 0 ≤ ∑ j ∈ K, |fo g (v j)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hR2 := cs_bound g v K J hJ
  generalize hA : (∑ x : Fin N → ZMod 2,
      (K.filter (fun j => dec (WW N C C.output (xb x)) j = v j ⬝ᵥ x)).card) = A at hGR ⊢
  generalize ∑ j ∈ K, |fo g (v j)| = R at hGR hR0 hR2
  have hG : ((2 * A - 2 ^ N * K.card : ℕ) : ℤ) ≤ R := by
    rcases le_or_gt (2 ^ N * K.card) (2 * A) with hle | hlt
    · rw [Nat.cast_sub hle]; push_cast; exact hGR
    · rw [Nat.sub_eq_zero_of_le hlt.le]; simpa using hR0
  generalize 2 * A - 2 ^ N * K.card = G at hG ⊢
  have hG0 : (0 : ℤ) ≤ (G : ℤ) := by positivity
  have hsq : ((G : ℤ)) ^ 2 ≤ (J.card : ℤ) * ((2 : ℤ) ^ N) ^ 2 :=
    le_trans (pow_le_pow_left₀ hG0 hG 2) hR2
  have key : ((2 ^ h * D * G ^ 2 : ℕ) : ℤ) ≤
      (((D + (2 ^ h - 1) * E) * m * (2 ^ N) ^ 2 : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub Nat.one_le_two_pow]
    have hP : (0 : ℤ) ≤ ((2 : ℤ) ^ N) ^ 2 := by positivity
    calc (2 : ℤ) ^ h * D * (G : ℤ) ^ 2 ≤ 2 ^ h * D * ((J.card : ℤ) * ((2 : ℤ) ^ N) ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = ((D : ℤ) * 2 ^ h * J.card) * ((2 : ℤ) ^ N) ^ 2 := by ring
      _ ≤ (D * m + (2 ^ h - 1) * E * m) * ((2 : ℤ) ^ N) ^ 2 :=
          mul_le_mul_of_nonneg_right hcount hP
      _ = _ := by ring
  exact_mod_cast key

end PEqualNP.Outside.L_meta_29726

open PEqualNP.Outside.L_meta_29726 in
theorem PEqualNP.Outside.L_meta_29726 :
∀ (k m h D E : ℕ), 0 < D →
  let F := ZMod 2
  let V := Fin k → F
  ∀ v : Fin m ↪ V, (∀ j, v j ≠ 0) →
    (∀ x : V, x ≠ 0 →
      let n := ((Finset.univ : Finset (Fin m)).filter (fun j => dotProduct (v j) x = 1)).card
      D*((m : ℤ)-2*(n : ℤ)).natAbs ≤ E*m) →
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.NestedCover.ReadsBack k C →
      (∀ g ∈ C.gates, (g.op = .and ∧ g.inputs.length = 2) ∨
        (g.op = .mod 2 ∧ g.inputs.length ≤ 2) ∨
        (g.op = .not ∧ g.inputs.length = 1)) →
      let s := C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _))
      2*s+h ≤ k → ∀ (K : Finset (Fin m)) (dec : Bool → Fin m → F),
        let bit := fun x : V => C.eval (List.ofFn (fun i : Fin k => decide (x i = 1)))
        let G := 2*(∑ x : V, (K.filter (fun j => dec (bit x) j = dotProduct (v j) x)).card) -
          2^k*K.card
        2^h*D*G^2 ≤ (D+(2^h-1)*E)*m*(2^k)^2 := by
  intro k m h D E hD
  dsimp only
  intro v hv0 hbias C hrb hgates hsk K dec
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := by
    intro g hg
    rcases hgates g hg with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ <;> omega
  have hSs : (SS C).card ≤
      C.gates.countP (fun g => @decide (g.op = .and) (Classical.propDecidable _)) := by
    rw [card_SS]
    exact List.countP_mono_left (fun g hg hnl => @decide_eq_true _ (Classical.propDecidable _) (nl_and g (hgates g hg) hnl))
  exact main_bound k m h D E v hv0 hbias C hrb hfan (by omega) K dec
