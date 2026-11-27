import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_592

open Finset

noncomputable section

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl


abbrev VV (n : ℕ) := Fin n → ZMod 2

/- generic fold helpers -/

theorem fold_congr {S : Type} {t : ℕ} (l : List (Fin t)) (g g' : Fin t → S → S)
    (h : ∀ x ∈ l, g x = g' x) (init : S) :
    l.foldl (fun cur st => g st cur) init = l.foldl (fun cur st => g' st cur) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih (fun y hy => h y (by simp [hy])) _

theorem fold_lin {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {t : ℕ}
    (l : List (Fin t)) (f : Fin t → V →ₗ[K] V) :
    ∃ L : V →ₗ[K] V, ∀ v, l.foldl (fun cur st => f st cur) v = L v := by
  induction l with
  | nil => exact ⟨LinearMap.id, fun v => rfl⟩
  | cons x l ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L ∘ₗ f x, fun v => by simp only [List.foldl_cons]; rw [hL]; rfl⟩

theorem mem_take_lt {t i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).take i) : x.val < i := by
  obtain ⟨n, hn, hx⟩ := List.mem_take_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show n < i
  omega

theorem mem_drop_ge {t i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).drop i) : i ≤ x.val := by
  obtain ⟨n, hn, hx⟩ := List.mem_drop_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show i ≤ i + n
  omega

theorem fold_eq {X : Type} (f : ℕ → X → X) (g : ℕ → X) (hs : ∀ t, g (t + 1) = f t (g t))
    (n : ℕ) : (List.finRange n).foldl (fun v i => f i.val v) (g 0) = g n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
    simp only [Fin.coe_castSucc, ih, List.foldl_cons, List.foldl_nil, Fin.val_last, hs]

/- step matrices -/

abbrev Ctl (b : ℕ) := (Fin b → ZMod 2) × ZMod 2

def ev {b : ℕ} (i : Fin (b + 1)) : VV (b + 1) := fun j => if i = j then 1 else 0

def ee (b t : ℕ) : VV (b + 1) := if h : t < b + 1 then ev ⟨t, h⟩ else 0

def Sh (b : ℕ) (lam : Fin (b + 1) → ZMod 2) : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
  Matrix.of fun k l => if k.val < b then (if l.val = k.val + 1 then 1 else 0) else lam l

def Am (b : ℕ) (c : Fin b → ZMod 2) : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
  Sh b (Fin.cons 1 c)

theorem sh_mul {b : ℕ} (lam : Fin (b + 1) → ZMod 2)
    (W : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k j : Fin (b + 1)) :
    (Sh b lam * W) k j =
      if h : k.val < b then W ⟨k.val + 1, by omega⟩ j else ∑ l, lam l * W l j := by
  rw [Matrix.mul_apply]
  simp only [Sh, Matrix.of_apply]
  by_cases h : k.val < b
  · rw [dif_pos h]
    simp only [h, ↓reduceIte, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single ⟨k.val + 1, by omega⟩]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h'
      exact hl (Fin.ext h')
    · simp
  · rw [dif_neg h]
    simp only [h, ↓reduceIte]

theorem sh_mulVec {b : ℕ} (lam : Fin (b + 1) → ZMod 2) (s : VV (b + 1)) (k : Fin (b + 1)) :
    (Sh b lam).mulVec s k =
      if h : k.val < b then s ⟨k.val + 1, by omega⟩ else ∑ l, lam l * s l := by
  simp only [Matrix.mulVec, dotProduct, Sh, Matrix.of_apply]
  by_cases h : k.val < b
  · rw [dif_pos h]
    simp only [h, ↓reduceIte, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single ⟨k.val + 1, by omega⟩]
    · simp
    · intro l _ hl
      rw [if_neg]
      intro h'
      exact hl (Fin.ext h')
    · simp
  · rw [dif_neg h]
    simp only [h, ↓reduceIte]

def bias (b : ℕ) (e : ZMod 2) : VV (b + 1) := fun k => if k.val < b then 0 else e

def tf (b : ℕ) (C : Ctl b) (s : VV (b + 1)) : VV (b + 1) := (Am b C.1).mulVec s + bias b C.2

theorem tf_lt {b : ℕ} (C : Ctl b) (s : VV (b + 1)) (k : Fin (b + 1)) (h : k.val < b) :
    tf b C s k = s ⟨k.val + 1, by omega⟩ := by
  simp only [tf, Pi.add_apply, Am, sh_mulVec, bias, h, ↓reduceIte, ↓reduceDIte, add_zero]

theorem tf_last {b : ℕ} (C : Ctl b) (s : VV (b + 1)) :
    tf b C s (Fin.last b) = s 0 + C.2 + ∑ j : Fin b, C.1 j * s j.succ := by
  have h : ¬ (Fin.last b).val < b := by simp
  simp only [tf, Pi.add_apply, Am, sh_mulVec, bias, h, ↓reduceIte, ↓reduceDIte]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, one_mul]
  ring

theorem det_am {b : ℕ} (c : Fin b → ZMod 2) : (Am b c).det = 1 := by
  refine (zmod2_cases _).resolve_left ?_
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  have h1 : ∀ k : Fin (b + 1), 0 < k.val → v k = 0 := by
    intro k hk
    have := congrFun hv ⟨k.val - 1, by omega⟩
    rw [Am, sh_mulVec, dif_pos (show k.val - 1 < b by omega)] at this
    have e : ∀ y : Fin (b + 1), y.val = k.val → v y = v k := fun y hy => by rw [Fin.ext hy]
    rw [e _ (by simp only; omega)] at this
    exact this
  have h0 : v 0 = 0 := by
    have := congrFun hv (Fin.last b)
    rw [Am, sh_mulVec, dif_neg (by simp), Fin.sum_univ_succ] at this
    simp only [Fin.cons_zero, one_mul, Pi.zero_apply] at this
    rwa [Finset.sum_eq_zero (fun j _ => by rw [h1 j.succ (by simp), mul_zero]), add_zero] at this
  apply hv0
  funext k
  by_cases hk : k.val = 0
  · rw [show k = 0 from Fin.ext hk]
    exact h0
  · exact h1 k (Nat.pos_of_ne_zero hk)

def Lp (b : ℕ) (F : ℕ → Fin b → ZMod 2) : ℕ → Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)
  | 0 => 1
  | t + 1 => Am b (F t) * Lp b F t

theorem det_lp (b : ℕ) (F : ℕ → Fin b → ZMod 2) (t : ℕ) : (Lp b F t).det = 1 := by
  induction t with
  | zero => exact Matrix.det_one
  | succ t ih =>
    show (Am b (F t) * Lp b F t).det = 1
    rw [Matrix.det_mul, det_am, ih, one_mul]

theorem lp_congr (b : ℕ) (F G : ℕ → Fin b → ZMod 2) (p : ℕ) (h : ∀ t < p, F t = G t) :
    Lp b F p = Lp b G p := by
  induction p with
  | zero => rfl
  | succ p ih =>
    show Am b (F p) * Lp b F p = Am b (G p) * Lp b G p
    rw [h p (by omega), ih (fun t ht => h t (by omega))]

theorem lp_add (b : ℕ) (F : ℕ → Fin b → ZMod 2) (p q : ℕ) :
    Lp b F (p + q) = Lp b (fun t => F (p + t)) q * Lp b F p := by
  induction q with
  | zero =>
    show Lp b F p = 1 * Lp b F p
    rw [one_mul]
  | succ q ih =>
    show Am b (F (p + q)) * Lp b F (p + q) = (Am b (F (p + q)) * Lp b (fun t => F (p + t)) q) * Lp b F p
    rw [ih, Matrix.mul_assoc]

/- orbits and the count -/
/- every invertible matrix is a product of step matrices -/

def Dsp (b k : ℕ) : Submodule (ZMod 2) (VV (b + 1)) :=
  Submodule.span (ZMod 2) {v | ∃ i, (i + 1 < k ∨ i = b) ∧ v = ee b i}

def valid (b k : ℕ) (v : VV (b + 1)) : Prop := ∃ y ∈ Dsp b k, v = ee b (k - 1) + y

theorem allE {b : ℕ} (X : Submodule (ZMod 2) (VV (b + 1))) (z : ℕ → VV (b + 1))
    (htop : ee b b ∈ X)
    (h : ∀ i, i < b → ee b i ∈ X ∨ (z (i + 1) ∈ X ∧ valid b (i + 1) (z (i + 1)))) :
    ∀ i, ee b i ∈ X := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases hib : i < b
    · rcases h i hib with h1 | ⟨h1, y, hy, hz⟩
      · exact h1
      · have hD : Dsp b (i + 1) ≤ X := by
          refine Submodule.span_le.2 ?_
          rintro _ ⟨j, hj, rfl⟩
          rcases hj with hj | hj
          · exact ih j (by omega)
          · rw [hj]
            exact htop
        have e : ee b i = z (i + 1) - y := by
          rw [hz, Nat.add_sub_cancel]
          abel
        rw [e]
        exact X.sub_mem h1 (hD hy)
    · by_cases hib' : i = b
      · rw [hib']
        exact htop
      · have e : ee b i = 0 := by
          simp only [ee]
          rw [dif_neg (by omega)]
        rw [e]
        exact X.zero_mem

theorem det_ne_of_span {n : ℕ} (W : Matrix (Fin n) (Fin n) (ZMod 2))
    (h : ⊤ ≤ Submodule.span (ZMod 2) (Set.range fun k => W k)) : W.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
  apply hv0
  let φ : VV n →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => x ⬝ᵥ v
      map_add' := fun x y => add_dotProduct x y v
      map_smul' := fun r x => smul_dotProduct r x v }
  have hle : Submodule.span (ZMod 2) (Set.range fun k => W k) ≤ LinearMap.ker φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, rfl⟩
    show W k ⬝ᵥ v = 0
    exact congrFun hv k
  funext i
  have := hle (h (Submodule.mem_top (x := Pi.single i 1)))
  rw [LinearMap.mem_ker] at this
  simpa [φ] using this

theorem top_of_ev {b : ℕ} (X : Submodule (ZMod 2) (VV (b + 1))) (h : ∀ i, ee b i ∈ X) :
    ⊤ ≤ X := by
  intro x _
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
  have := h i.val
  simp only [ee, i.isLt, ↓reduceDIte, Fin.eta] at this
  exact this

theorem span_rows {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0)
    (i : ℕ) : ee b i ∈ Submodule.span (ZMod 2) (Set.range fun k => M k) := by
  by_cases hi : i < b + 1
  · have hu : IsUnit M.det := isUnit_iff_ne_zero.2 hM
    have e : ee b i = ∑ l, M⁻¹ ⟨i, hi⟩ l • M l := by
      funext j
      have := congrFun (congrFun (Matrix.nonsing_inv_mul M hu) ⟨i, hi⟩) j
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      simp only [ee, hi, ↓reduceDIte, ev, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
    rw [e]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  · have e : ee b i = 0 := by
      simp only [ee]
      rw [dif_neg hi]
    rw [e]
    exact Submodule.zero_mem _

theorem step_exists {b : ℕ} (W W' : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hW : W.det ≠ 0)
    (hW' : W'.det ≠ 0)
    (hsh : ∀ k : Fin (b + 1), (hk : k.val < b) → W' k = W ⟨k.val + 1, by omega⟩) :
    ∃ c, Am b c * W = W' := by
  have hu : IsUnit W.det := isUnit_iff_ne_zero.2 hW
  set lam := Matrix.vecMul (W' (Fin.last b)) W⁻¹ with hlam
  have hl : Matrix.vecMul lam W = W' (Fin.last b) := by
    rw [hlam, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  have hN : Sh b lam * W = W' := by
    ext k j
    rw [sh_mul]
    split_ifs with hk
    · rw [hsh k hk]
    · have e : k = Fin.last b := Fin.ext (by simp; omega)
      rw [e, ← hl]
      rfl
  have h0 : lam 0 ≠ 0 := by
    intro h0
    have hd : (Sh b lam).det = 0 := by
      refine Matrix.det_eq_zero_of_column_eq_zero 0 (fun k => ?_)
      simp only [Sh, Matrix.of_apply]
      split_ifs with h1 h2
      · simp at h2
      · rfl
      · exact h0
    apply hW'
    rw [← hN, Matrix.det_mul, hd, zero_mul]
  have h1 : lam 0 = 1 := (zmod2_cases _).resolve_left h0
  refine ⟨fun j => lam j.succ, ?_⟩
  have e : (Fin.cons 1 (fun j => lam j.succ) : Fin (b + 1) → ZMod 2) = lam := by
    funext l
    refine Fin.cases ?_ (fun j => ?_) l
    · rw [Fin.cons_zero, h1]
    · rw [Fin.cons_succ]
  rw [Am, e, hN]

def gM (b : ℕ) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (j : ℕ) : VV (b + 1) :=
  if h : j < b + 1 then M ⟨j, h⟩ else 0

def Sk (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ) :
    Set (VV (b + 1)) :=
  {v | (∃ j, k ≤ j ∧ j ≤ b ∧ v = z j) ∨ (∃ j, j < k ∧ v = gM b M j)}

def SS (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ) :
    Set (VV (b + 1)) :=
  {v | (∃ j, k + 1 ≤ j ∧ j ≤ b ∧ v = z j) ∨ (∃ j, j < k ∧ v = gM b M j)}

def Good (b : ℕ) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ) (z : ℕ → VV (b + 1)) :
    Prop :=
  (∀ j, k ≤ j → j ≤ b → valid b j (z j)) ∧
    ∀ k', k ≤ k' → k' ≤ b + 1 → ⊤ ≤ Submodule.span (ZMod 2) (Sk b z M k')

theorem good_base {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0) :
    Good b M (b + 1) (fun _ => 0) := by
  refine ⟨fun j h1 h2 => absurd h1 (by omega), fun k' h1 h2 => ?_⟩
  have hk : k' = b + 1 := by omega
  rw [hk]
  refine top_of_ev _ (fun i => ?_)
  refine Submodule.span_mono ?_ (span_rows M hM i)
  rintro _ ⟨k, rfl⟩
  refine Or.inr ⟨k.val, k.isLt, ?_⟩
  simp only [gM, k.isLt, ↓reduceDIte, Fin.eta]

theorem good_step {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (k : ℕ)
    (hk1 : 1 ≤ k) (hkb : k ≤ b) (z : ℕ → VV (b + 1)) (hz : Good b M (k + 1) z) :
    ∃ z', Good b M k z' := by
  obtain ⟨hv, hs⟩ := hz
  have hSk : ⊤ ≤ Submodule.span (ZMod 2) (insert (gM b M k) (SS b z M k)) := by
    refine (hs (k + 1) le_rfl (by omega)).trans (Submodule.span_mono ?_)
    rintro v (⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl ⟨j, hj1, hj2, rfl⟩)
    · by_cases hjk : j = k
      · rw [hjk]
        exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨j, by omega, rfl⟩)
  have hchoose : ∃ x, valid b k x ∧ ⊤ ≤ Submodule.span (ZMod 2) (insert x (SS b z M k)) := by
    by_cases hA : ∃ y ∈ Dsp b k, ee b (k - 1) + y ∉ Submodule.span (ZMod 2) (SS b z M k)
    · obtain ⟨y, hy, hny⟩ := hA
      refine ⟨ee b (k - 1) + y, ⟨y, hy, rfl⟩, ?_⟩
      have hx : ee b (k - 1) + y ∈ Submodule.span (ZMod 2) (insert (gM b M k) (SS b z M k)) :=
        hSk Submodule.mem_top
      have hg := mem_span_insert_exchange hx hny
      refine hSk.trans (Submodule.span_le.2 ?_)
      rintro v (rfl | hv)
      · exact hg
      · exact Submodule.subset_span (Set.mem_insert_of_mem _ hv)
    · push Not at hA
      refine ⟨ee b (k - 1), ⟨0, Submodule.zero_mem _, by rw [add_zero]⟩, ?_⟩
      have h0 : ee b (k - 1) ∈ Submodule.span (ZMod 2) (SS b z M k) := by
        simpa using hA 0 (Submodule.zero_mem _)
      have hD : ∀ i, (i + 1 < k ∨ i = b) → ee b i ∈ Submodule.span (ZMod 2) (SS b z M k) := by
        intro i hi
        have h2 := hA (ee b i) (Submodule.subset_span ⟨i, hi, rfl⟩)
        have e2 : ee b i = (ee b (k - 1) + ee b i) - ee b (k - 1) := by abel
        rw [e2]
        exact Submodule.sub_mem _ h2 h0
      have hall := allE (Submodule.span (ZMod 2) (SS b z M k)) z (hD b (Or.inr rfl)) (by
        intro i hi
        by_cases hik : i + 1 < k
        · exact Or.inl (hD i (Or.inl hik))
        · by_cases hik' : i + 1 = k
          · left
            rw [show i = k - 1 by omega]
            exact h0
          · right
            exact ⟨Submodule.subset_span (Or.inl ⟨i + 1, by omega, by omega, rfl⟩),
              hv (i + 1) (by omega) (by omega)⟩)
      exact (top_of_ev _ hall).trans (Submodule.span_mono (Set.subset_insert _ _))
  obtain ⟨x, hxv, hxs⟩ := hchoose
  refine ⟨Function.update z k x, ?_, ?_⟩
  · intro j hj1 hj2
    by_cases hjk : j = k
    · rw [hjk, Function.update_self]
      exact hxv
    · rw [Function.update_of_ne hjk]
      exact hv j (by omega) hj2
  · intro k' hk' hk'b
    by_cases hkk : k' = k
    · rw [hkk]
      refine hxs.trans (Submodule.span_mono ?_)
      rintro v (rfl | ⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact Or.inl ⟨k, le_rfl, hkb, by rw [Function.update_self]⟩
      · exact Or.inl ⟨j, by omega, hj2, by rw [Function.update_of_ne (by omega)]⟩
      · exact Or.inr ⟨j, hj, rfl⟩
    · refine (hs k' (by omega) hk'b).trans (Submodule.span_mono ?_)
      rintro v (⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact Or.inl ⟨j, hj1, hj2, by rw [Function.update_of_ne (by omega)]⟩
      · exact Or.inr ⟨j, hj, rfl⟩

theorem good_one {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0) :
    ∃ z, Good b M 1 z := by
  have h : ∀ r, r ≤ b → ∃ z, Good b M (b + 1 - r) z := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨fun _ => 0, good_base M hM⟩
    | succ r ih =>
      intro hr
      obtain ⟨z, hz⟩ := ih (by omega)
      rw [show b + 1 - r = (b - r) + 1 by omega] at hz
      rw [show b + 1 - (r + 1) = b - r by omega]
      exact good_step M (b - r) (by omega) (by omega) z hz
  obtain ⟨z, hz⟩ := h b le_rfl
  rw [show b + 1 - b = 1 by omega] at hz
  exact ⟨z, hz⟩

def seqf (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (t : ℕ) :
    VV (b + 1) :=
  if t < b + 1 then ee b t else if t < 2 * b + 1 then z (t - b) else gM b M (t - (2 * b + 1))

def Wn (b : ℕ) (z : ℕ → VV (b + 1)) (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (t : ℕ) :
    Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
  Matrix.of fun k l => seqf b z M (t + k.val) l

theorem surj_exact {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0) :
    ∃ D : ℕ → Fin b → ZMod 2, Lp b D (2 * b + 1) = M := by
  obtain ⟨z, hv, hs⟩ := good_one M hM
  have hspan : ∀ t, t ≤ 2 * b + 1 →
      ⊤ ≤ Submodule.span (ZMod 2) (Set.range fun k => Wn b z M t k) := by
    intro t ht
    by_cases htb : t ≤ b
    · apply top_of_ev
      apply allE _ z
      · refine Submodule.subset_span ⟨⟨b - t, by omega⟩, ?_⟩
        show seqf b z M (t + (b - t)) = ee b b
        rw [show t + (b - t) = b by omega, seqf, if_pos (by omega)]
      · intro i hi
        by_cases hit : t ≤ i
        · left
          refine Submodule.subset_span ⟨⟨i - t, by omega⟩, ?_⟩
          show seqf b z M (t + (i - t)) = ee b i
          rw [show t + (i - t) = i by omega, seqf, if_pos (by omega)]
        · right
          refine ⟨Submodule.subset_span ⟨⟨i + 1 + b - t, by omega⟩, ?_⟩,
            hv (i + 1) (by omega) (by omega)⟩
          show seqf b z M (t + (i + 1 + b - t)) = z (i + 1)
          rw [seqf, if_neg (by omega), if_pos (by omega)]
          congr 1
          omega
    · have hk := hs (t - b) (by omega) (by omega)
      refine hk.trans (Submodule.span_mono ?_)
      rintro v (⟨j, hj1, hj2, rfl⟩ | ⟨j, hj, rfl⟩)
      · refine ⟨⟨j - (t - b), by omega⟩, ?_⟩
        show seqf b z M (t + (j - (t - b))) = z j
        rw [seqf, if_neg (by omega), if_pos (by omega)]
        congr 1
        omega
      · refine ⟨⟨j + 2 * b + 1 - t, by omega⟩, ?_⟩
        show seqf b z M (t + (j + 2 * b + 1 - t)) = gM b M j
        rw [seqf, if_neg (by omega), if_neg (by omega)]
        congr 1
        omega
  have hW0 : Wn b z M 0 = 1 := by
    ext k l
    rw [Wn, Matrix.of_apply, seqf, if_pos (by omega), Matrix.one_apply]
    simp only [ee, Nat.zero_add, k.isLt, ↓reduceDIte, Fin.eta, ev]
  have hWL : Wn b z M (2 * b + 1) = M := by
    ext k l
    rw [Wn, Matrix.of_apply, seqf, if_neg (by omega), if_neg (by omega), gM,
      dif_pos (by omega)]
    have e : ∀ y : Fin (b + 1), y.val = k.val → M y l = M k l := fun y hy => by rw [Fin.ext hy]
    exact e _ (by simp only; omega)
  have hshift : ∀ t (k : Fin (b + 1)) (hk : k.val < b),
      Wn b z M (t + 1) k = Wn b z M t ⟨k.val + 1, by omega⟩ := by
    intro t k hk
    funext l
    show seqf b z M (t + 1 + k.val) l = seqf b z M (t + (k.val + 1)) l
    rw [show t + 1 + k.val = t + (k.val + 1) by omega]
  have hex : ∀ t, ∃ c : Fin b → ZMod 2, t < 2 * b + 1 → Am b c * Wn b z M t = Wn b z M (t + 1) := by
    intro t
    by_cases ht : t < 2 * b + 1
    · obtain ⟨c, hc⟩ := step_exists (Wn b z M t) (Wn b z M (t + 1))
        (det_ne_of_span _ (hspan t (by omega))) (det_ne_of_span _ (hspan (t + 1) (by omega)))
        (fun k hk => hshift t k hk)
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose D hD using hex
  refine ⟨D, ?_⟩
  have h : ∀ t, t ≤ 2 * b + 1 → Lp b D t = Wn b z M t := by
    intro t
    induction t with
    | zero =>
      intro _
      rw [hW0]
      rfl
    | succ t ih =>
      intro ht
      show Am b (D t) * Lp b D t = _
      rw [ih (by omega), hD t (by omega)]
  rw [h _ le_rfl, hWL]

theorem surj {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0)
    (L : ℕ) (hL : 2 * b + 1 ≤ L) : ∃ D : ℕ → Fin b → ZMod 2, Lp b D L = M := by
  induction L, hL using Nat.le_induction generalizing M with
  | base => exact surj_exact M hM
  | succ L hL ih =>
    have hA : IsUnit (Am b 0).det := by
      rw [det_am]
      exact isUnit_one
    obtain ⟨D, hD⟩ := ih ((Am b 0)⁻¹ * M) (by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, det_am, Ring.inverse_one, one_mul]
      exact hM)
    refine ⟨fun t => if t = L then 0 else D t, ?_⟩
    show Am b (if L = L then 0 else D L) * Lp b (fun t => if t = L then 0 else D t) L = M
    rw [if_pos rfl, lp_congr b _ D L (fun t ht => if_neg (by omega)), hD, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]

/- seeds, rows and orbits -/

abbrev Sd (b : ℕ) := Fin (b + 1) → Bool

abbrev Ct (b : ℕ) := (Fin b → Bool) → Bool

def wm {b : ℕ} (c : Ct b) (s : Sd b) : Sd b :=
  fun k => if h : k.val < b then s ⟨k.val + 1, by omega⟩ else xor (s 0) (c (fun j => s j.succ))

theorem wm_lt {b : ℕ} (c : Ct b) (s : Sd b) (k : Fin (b + 1)) (h : k.val < b) :
    wm c s k = s ⟨k.val + 1, by omega⟩ := by
  simp only [wm, h, ↓reduceDIte]

theorem wm_last {b : ℕ} (c : Ct b) (s : Sd b) :
    wm c s (Fin.last b) = xor (s 0) (c (fun j => s j.succ)) := by
  have h : ¬ (Fin.last b).val < b := by simp
  simp only [wm, h, ↓reduceDIte]

theorem xor_cancel {p q r : Bool} (h : xor p r = xor q r) : p = q := by
  revert h
  cases p <;> cases q <;> cases r <;> decide

theorem wm_inj {b : ℕ} (c : Ct b) : Function.Injective (wm c) := by
  intro s s' h
  have hr : ∀ j : Fin b, s j.succ = s' j.succ := by
    intro j
    have := congrFun h j.castSucc
    rw [wm_lt _ _ _ (by simp), wm_lt _ _ _ (by simp)] at this
    have e : ∀ (t : Sd b) (y : Fin (b + 1)), y.val = j.val + 1 → t y = t j.succ :=
      fun t y hy => by rw [show y = j.succ from Fin.ext (by simp [hy])]
    rw [e s _ (by simp), e s' _ (by simp)] at this
    exact this
  have hl := congrFun h (Fin.last b)
  rw [wm_last, wm_last] at hl
  have hrest : (fun j : Fin b => s j.succ) = (fun j : Fin b => s' j.succ) := funext hr
  rw [hrest] at hl
  have h0 := xor_cancel hl
  funext k
  refine Fin.cases ?_ (fun j => ?_) k
  · exact h0
  · exact hr j

def orb {b : ℕ} (F : ℕ → Ct b) (s : Sd b) : ℕ → Sd b
  | 0 => s
  | t + 1 => wm (F t) (orb F s t)

def pr {b : ℕ} (F : ℕ → Ct b) (t : ℕ) : Sd b → Sd b := fun s => orb F s t

theorem orb_add {b : ℕ} (F : ℕ → Ct b) (s : Sd b) (p q : ℕ) :
    orb F s (p + q) = orb (fun t => F (p + t)) (orb F s p) q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    show wm (F (p + q)) (orb F s (p + q)) = wm (F (p + q)) (orb (fun t => F (p + t)) (orb F s p) q)
    rw [ih]

theorem orb_congr {b : ℕ} (F G : ℕ → Ct b) (s : Sd b) (L : ℕ) (h : ∀ t < L, F t = G t) :
    orb F s L = orb G s L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    show wm (F L) (orb F s L) = wm (G L) (orb G s L)
    rw [h L (by omega), ih (fun t ht => h t (by omega))]

theorem pr_bij {b : ℕ} (F : ℕ → Ct b) (t : ℕ) : Function.Bijective (pr F t) := by
  induction t with
  | zero => exact Function.bijective_id
  | succ t ih =>
    show Function.Bijective (wm (F t) ∘ pr F t)
    exact (Finite.injective_iff_bijective.1 (wm_inj _)).comp ih

/- the count is a fixed-point count -/

abbrev site (a t : ℕ) : Fin (a + 1) := Fin.ofNat (a + 1) t

theorem site_val (a t : ℕ) : (site a t).val = t % (a + 1) := Fin.val_ofNat _ _

theorem site_eq {a p q : ℕ} (h : p % (a + 1) = q % (a + 1)) : site a p = site a q :=
  Fin.ext (by rw [site_val, site_val, h])

theorem site_fin (a : ℕ) (i : Fin (a + 1)) : site a i.val = i := Fin.ofNat_val_eq_self i

abbrev cst (a b : ℕ) (C : Fin (a + 1) → Ct b) (x : Fin (a + 1) → Bool) (i : Fin (a + 1)) :
    Prop :=
  x (Fin.ofNat (a + 1) (i.val + (b + 1))) =
    xor (x i) (C i (fun j => x (Fin.ofNat (a + 1) (i.val + 1 + j.val))))

def cnt (a b : ℕ) (C : Fin (a + 1) → Ct b) : ℕ :=
  ((Finset.univ : Finset (Fin (a + 1) → Bool)).filter (fun x =>
    ∀ i : Fin (a + 1), x (Fin.ofNat (a + 1) (i.val + (b + 1))) =
      xor (x i) (C i (fun j => x (Fin.ofNat (a + 1) (i.val + 1 + j.val)))))).card

def win (a b : ℕ) (x : Fin (a + 1) → Bool) (t : ℕ) : Sd b :=
  fun k => x (site a (t + k.val))

theorem win_mod (a b : ℕ) (x : Fin (a + 1) → Bool) (p q : ℕ) (h : p % (a + 1) = q % (a + 1)) :
    win a b x p = win a b x q := by
  funext k
  simp only [win]
  rw [site_eq (a := a) (p := p + k.val) (q := q + k.val)]
  rw [Nat.add_mod, h, ← Nat.add_mod]

theorem win_step (a b : ℕ) (C : Fin (a + 1) → Ct b) (x : Fin (a + 1) → Bool)
    (i : Fin (a + 1)) :
    cst a b C x i ↔ win a b x (i.val + 1) = wm (C i) (win a b x i.val) := by
  have hlow : ∀ k : Fin (b + 1), k.val < b →
      win a b x (i.val + 1) k = wm (C i) (win a b x i.val) k := by
    intro k hk
    rw [wm_lt _ _ _ hk]
    simp only [win]
    rw [show i.val + 1 + k.val = i.val + (k.val + 1) by omega]
  have hl1 : win a b x (i.val + 1) (Fin.last b) = x (Fin.ofNat (a + 1) (i.val + (b + 1))) := by
    simp only [win, Fin.val_last]
    rw [show i.val + 1 + b = i.val + (b + 1) by omega]
  have hl2 : wm (C i) (win a b x i.val) (Fin.last b) =
      xor (x i) (C i (fun j => x (Fin.ofNat (a + 1) (i.val + 1 + j.val)))) := by
    rw [wm_last]
    simp only [win, Fin.val_zero, Nat.add_zero, Fin.val_succ]
    rw [site_fin]
    congr 2
    funext j
    rw [show i.val + (j.val + 1) = i.val + 1 + j.val by omega]
  constructor
  · intro h
    funext k
    by_cases hk : k.val < b
    · exact hlow k hk
    · rw [show k = Fin.last b from Fin.ext (by simp; omega), hl1, hl2]
      exact h
  · intro h
    have := congrFun h (Fin.last b)
    rw [hl1, hl2] at this
    exact this

def Cn (a b : ℕ) (C : Fin (a + 1) → Ct b) (t : ℕ) : Ct b := C (site a t)

theorem sol_step (a b : ℕ) (C : Fin (a + 1) → Ct b) (x : Fin (a + 1) → Bool)
    (hx : ∀ i, cst a b C x i) (t : ℕ) :
    win a b x (t + 1) = wm (Cn a b C t) (win a b x t) := by
  have h := (win_step a b C x (site a t)).1 (hx _)
  rw [win_mod a b x (t + 1) ((site a t).val + 1), win_mod a b x t (site a t).val]
  · exact h
  · rw [site_val]
    exact (Nat.mod_mod t (a + 1)).symm
  · rw [site_val]
    exact (Nat.mod_add_mod t (a + 1) 1).symm

theorem orb_win (a b : ℕ) (C : Fin (a + 1) → Ct b) (x : Fin (a + 1) → Bool)
    (hx : ∀ i, cst a b C x i) (t : ℕ) : orb (Cn a b C) (win a b x 0) t = win a b x t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show wm (Cn a b C t) (orb (Cn a b C) (win a b x 0) t) = _
    rw [ih, sol_step a b C x hx]

theorem cn_per (a b : ℕ) (C : Fin (a + 1) → Ct b) (t : ℕ) :
    Cn a b C (t + (a + 1)) = Cn a b C t := by
  simp only [Cn]
  rw [site_eq (a := a) (Nat.add_mod_right t (a + 1))]

theorem orb_per (a b : ℕ) (C : Fin (a + 1) → Ct b) (s : Sd b)
    (hs : orb (Cn a b C) s (a + 1) = s) (t : ℕ) :
    orb (Cn a b C) s (t + (a + 1)) = orb (Cn a b C) s t := by
  induction t with
  | zero => rw [Nat.zero_add, hs]; rfl
  | succ t ih =>
    rw [show t + 1 + (a + 1) = (t + (a + 1)) + 1 by omega]
    show wm (Cn a b C (t + (a + 1))) (orb (Cn a b C) s (t + (a + 1))) =
      wm (Cn a b C t) (orb (Cn a b C) s t)
    rw [ih, cn_per]

theorem orb_shift {b : ℕ} (F : ℕ → Ct b) (s : Sd b) (t k : ℕ) (hk : k < b) :
    orb F s (t + 1) ⟨k, by omega⟩ = orb F s t ⟨k + 1, by omega⟩ := by
  show wm (F t) (orb F s t) ⟨k, by omega⟩ = _
  rw [wm_lt _ _ _ hk]

theorem orb_col {b : ℕ} (F : ℕ → Ct b) (s : Sd b) :
    ∀ k (hk : k < b + 1) t, orb F s t ⟨k, hk⟩ = orb F s (t + k) 0 := by
  intro k
  induction k with
  | zero =>
    intro hk t
    rfl
  | succ k ih =>
    intro hk t
    rw [← orb_shift F s t k (by omega), ih (by omega) (t + 1)]
    rw [show t + 1 + k = t + (k + 1) by omega]

theorem z_mod (a b : ℕ) (C : Fin (a + 1) → Ct b) (s : Sd b)
    (hs : orb (Cn a b C) s (a + 1) = s) (t : ℕ) :
    orb (Cn a b C) s t 0 = orb (Cn a b C) s (t % (a + 1)) 0 := by
  have h : ∀ q r, orb (Cn a b C) s (r + (a + 1) * q) = orb (Cn a b C) s r := by
    intro q
    induction q with
    | zero => intro r; rfl
    | succ q ih =>
      intro r
      rw [show r + (a + 1) * (q + 1) = (r + (a + 1) * q) + (a + 1) by ring, orb_per a b C s hs, ih]
  conv_lhs => rw [← Nat.mod_add_div t (a + 1)]
  rw [h]

def psi (a b : ℕ) (C : Fin (a + 1) → Ct b) (s : Sd b) : Fin (a + 1) → Bool :=
  fun i => orb (Cn a b C) s i.val 0

theorem win_psi (a b : ℕ) (C : Fin (a + 1) → Ct b) (s : Sd b)
    (hs : orb (Cn a b C) s (a + 1) = s) (t : ℕ) :
    win a b (psi a b C s) t = orb (Cn a b C) s t := by
  funext k
  show orb (Cn a b C) s (site a (t + k.val)).val 0 = _
  rw [site_val, ← z_mod a b C s hs, ← orb_col _ s k.val k.isLt t]

theorem cnt_eq (a b : ℕ) (C : Fin (a + 1) → Ct b) :
    cnt a b C = ((Finset.univ : Finset (Sd b)).filter
      (fun s => orb (Cn a b C) s (a + 1) = s)).card := by
  refine Finset.card_nbij' (fun x => win a b x 0) (fun s => psi a b C s) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hx ⊢
    rw [orb_win a b C x hx]
    exact win_mod a b x _ _ (by simp)
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hs ⊢
    intro i
    refine (win_step a b C (psi a b C s) i).2 ?_
    rw [win_psi a b C s hs, win_psi a b C s hs]
    show wm (Cn a b C i.val) _ = wm (C i) _
    rw [Cn, site_fin]
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hx
    funext i
    show orb (Cn a b C) (win a b x 0) i.val 0 = x i
    rw [orb_win a b C x hx]
    show x (site a (i.val + 0)) = x i
    rw [Nat.add_zero, site_fin]
  · intro s hs
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq] at hs
    show win a b (psi a b C s) 0 = s
    rw [win_psi a b C s hs]
    rfl

/- function matrices -/

def Fm (K : Type) [Field K] {b : ℕ} (f : Sd b → Sd b) : Matrix (Sd b) (Sd b) K :=
  Matrix.of fun x y => if x = f y then 1 else 0

theorem Fm_mul (K : Type) [Field K] {b : ℕ} (f g : Sd b → Sd b) :
    Fm K f * Fm K g = Fm K (f ∘ g) := by
  ext x y
  simp [Fm, Matrix.mul_apply]

theorem Fm_id (K : Type) [Field K] {b : ℕ} : Fm K (fun s : Sd b => s) = 1 := by
  ext x y
  simp [Fm, Matrix.one_apply]

theorem trace_Fm (K : Type) [Field K] {b : ℕ} (f : Sd b → Sd b) :
    (Fm K f).trace = (((Finset.univ : Finset (Sd b)).filter (fun s => f s = s)).card : K) := by
  simp only [Matrix.trace, Matrix.diag, Fm, Matrix.of_apply]
  rw [Finset.sum_boole]
  congr 2
  ext s
  simp [eq_comm]

theorem cnt_trace (K : Type) [Field K] (a b : ℕ) (C : Fin (a + 1) → Ct b) :
    (cnt a b C : K) = (Fm K (pr (Cn a b C) (a + 1))).trace := by
  rw [trace_Fm, cnt_eq]
  rfl

theorem perm_apply (K : Type) [Field K] {b : ℕ} (f : Sd b → Sd b) (hf : Function.Bijective f)
    (B : Matrix (Sd b) (Sd b) K) (x j : Sd b) :
    (Fm K f * B) x j = B ((Equiv.ofBijective f hf).symm x) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single ((Equiv.ofBijective f hf).symm x)]
  · simp only [Fm, Matrix.of_apply, Equiv.ofBijective_apply_symm_apply, ↓reduceIte, one_mul]
  · intro z _ hz
    simp only [Fm, Matrix.of_apply]
    rw [if_neg, zero_mul]
    intro hx
    apply hz
    rw [hx, Equiv.ofBijective_symm_apply_apply]
  · simp

/- the invariant subspaces -/

def W (K : Type) [Field K] (b : ℕ) : Submodule K (Matrix (Sd b) (Sd b) K) where
  carrier := {B | ∀ x y, ∑ j, B x j = ∑ i, B i y}
  add_mem' := by
    intro A B hA hB x y
    show ∑ j, (A x j + B x j) = ∑ i, (A i y + B i y)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hA x y, hB x y]
  zero_mem' := by
    intro x y
    simp
  smul_mem' := by
    intro c A hA x y
    show ∑ j, c * A x j = ∑ i, c * A i y
    rw [← Finset.mul_sum, ← Finset.mul_sum, hA x y]

theorem mem_W {K : Type} [Field K] {b : ℕ} (B : Matrix (Sd b) (Sd b) K) :
    B ∈ W K b ↔ ∀ x y, ∑ j, B x j = ∑ i, B i y := Iff.rfl

theorem W_inv (K : Type) [Field K] {b : ℕ} (f : Sd b → Sd b) (hf : Function.Bijective f)
    (B : Matrix (Sd b) (Sd b) K) (hB : B ∈ W K b) : Fm K f * B ∈ W K b := by
  intro x y
  show ∑ j, (Fm K f * B) x j = ∑ i, (Fm K f * B) i y
  simp only [perm_apply K f hf]
  rw [hB _ y]
  exact (Equiv.sum_comp (Equiv.ofBijective f hf).symm (fun i => B i y)).symm

theorem one_W (K : Type) [Field K] (b : ℕ) : (1 : Matrix (Sd b) (Sd b) K) ∈ W K b := by
  intro x y
  simp [Matrix.one_apply]

theorem Fm_W (K : Type) [Field K] {b : ℕ} (f : Sd b → Sd b) (hf : Function.Bijective f) :
    Fm K f ∈ W K b := by
  have h := W_inv K f hf 1 (one_W K b)
  rwa [Matrix.mul_one] at h

def Rs (K : Type) [Field K] (b : ℕ) : Submodule K (Matrix (Sd b) (Sd b) K) where
  carrier := {B | ∃ u v : Sd b → K,
    B = Matrix.vecMulVec u (fun _ => 1) + Matrix.vecMulVec (fun _ => 1) v ∧ ∑ x, u x = ∑ x, v x}
  add_mem' := by
    rintro A B ⟨u, v, rfl, huv⟩ ⟨u', v', rfl, huv'⟩
    refine ⟨u + u', v + v', ?_, ?_⟩
    · ext x y
      simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply]
      ring
    · simp only [Pi.add_apply, Finset.sum_add_distrib, huv, huv']
  zero_mem' := ⟨0, 0, by ext x y; simp [Matrix.vecMulVec_apply], by simp⟩
  smul_mem' := by
    rintro c A ⟨u, v, rfl, huv⟩
    refine ⟨c • u, c • v, ?_, ?_⟩
    · ext x y
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, huv]

theorem card_Sd (b : ℕ) : Fintype.card (Sd b) = 2 ^ (b + 1) := by
  simp [Sd]

theorem cardK_two (K : Type) [Field K] [CharP K 2] (b : ℕ) : (Fintype.card (Sd b) : K) = 0 := by
  rw [card_Sd, Nat.cast_pow, Nat.cast_ofNat, CharTwo.two_eq_zero, zero_pow (by omega)]

theorem Rs_W (K : Type) [Field K] [CharP K 2] (b : ℕ) : Rs K b ≤ W K b := by
  rintro B ⟨u, v, rfl, huv⟩ x y
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, mul_one, one_mul, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, cardK_two, zero_mul, zero_add, add_zero]
  exact huv.symm

theorem Rs_inv (K : Type) [Field K] {b : ℕ} (f : Sd b → Sd b) (hf : Function.Bijective f)
    (B : Matrix (Sd b) (Sd b) K) (hB : B ∈ Rs K b) : Fm K f * B ∈ Rs K b := by
  obtain ⟨u, v, rfl, huv⟩ := hB
  refine ⟨fun x => u ((Equiv.ofBijective f hf).symm x), v, ?_, ?_⟩
  · ext x y
    rw [perm_apply K f hf]
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply]
  · rw [← huv]
    exact Equiv.sum_comp (Equiv.ofBijective f hf).symm u

theorem Rs_trace (K : Type) [Field K] [CharP K 2] {b : ℕ} (B : Matrix (Sd b) (Sd b) K)
    (hB : B ∈ Rs K b) : B.trace = 0 := by
  obtain ⟨u, v, rfl, huv⟩ := hB
  simp only [Matrix.trace, Matrix.diag, Matrix.add_apply, Matrix.vecMulVec_apply, mul_one,
    one_mul, Finset.sum_add_distrib, huv]
  rw [← two_mul, CharTwo.two_eq_zero, zero_mul]

/- dimensions -/

def z0 (b : ℕ) : Sd b := fun _ => false

abbrev S0 (b : ℕ) := {x : Sd b // x ≠ z0 b}

theorem card_S0 (b : ℕ) : Fintype.card (S0 b) = 2 ^ (b + 1) - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_Sd]

def coW (K : Type) [Field K] (b : ℕ) : W K b →ₗ[K] ((S0 b × S0 b → K) × K) where
  toFun B := (fun p => B.1 p.1.1 p.2.1, ∑ j, B.1 (z0 b) j)
  map_add' B B' := by
    simp only [Submodule.coe_add, Matrix.add_apply, Finset.sum_add_distrib, Prod.mk_add_mk]
    rfl
  map_smul' c B := by
    simp only [Submodule.coe_smul, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum,
      RingHom.id_apply, Prod.smul_mk]
    rfl

theorem coW_inj (K : Type) [Field K] (b : ℕ) : Function.Injective (coW K b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro B hB0
  have hz : ∀ i j, i ≠ z0 b → j ≠ z0 b → B.1 i j = 0 := fun i j hi hj =>
    congrFun (congrArg Prod.fst hB0) (⟨i, hi⟩, ⟨j, hj⟩)
  have hs : ∑ j, B.1 (z0 b) j = 0 := congrArg Prod.snd hB0
  have hW : ∀ x y, ∑ j, B.1 x j = ∑ i, B.1 i y := B.2
  have hrow : ∀ x, ∑ j, B.1 x j = 0 := fun x => by rw [hW x (z0 b), ← hW (z0 b) (z0 b), hs]
  have hcol : ∀ y, ∑ i, B.1 i y = 0 := fun y => by rw [← hW (z0 b) y, hs]
  have h1 : ∀ i, i ≠ z0 b → B.1 i (z0 b) = 0 := by
    intro i hi
    have := hrow i
    rwa [Finset.sum_eq_single (z0 b) (fun j _ hj => hz i j hi hj) (by simp)] at this
  have h2 : ∀ j, j ≠ z0 b → B.1 (z0 b) j = 0 := by
    intro j hj
    have := hcol j
    rwa [Finset.sum_eq_single (z0 b) (fun i _ hi => hz i j hi hj) (by simp)] at this
  have h3 : B.1 (z0 b) (z0 b) = 0 := by
    have := hrow (z0 b)
    rwa [Finset.sum_eq_single (z0 b) (fun j _ hj => h2 j hj) (by simp)] at this
  apply Subtype.ext
  ext i j
  show B.1 i j = 0
  by_cases hi : i = z0 b
  · subst hi
    by_cases hj : j = z0 b
    · subst hj
      exact h3
    · exact h2 j hj
  · by_cases hj : j = z0 b
    · subst hj
      exact h1 i hi
    · exact hz i j hi hj

theorem finrank_W (K : Type) [Field K] (b : ℕ) :
    Module.finrank K (W K b) ≤ (2 ^ (b + 1) - 1) ^ 2 + 1 := by
  have h := LinearMap.finrank_le_finrank_of_injective (coW_inj K b)
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Module.finrank_self,
    Fintype.card_prod, card_S0] at h
  rw [sq]
  exact h

def uf (K : Type) [Field K] {b : ℕ} (α β : S0 b → K) : Sd b → K :=
  fun x => if h : x = z0 b then (∑ y, β y - ∑ y, α y) else α ⟨x, h⟩

def vf (K : Type) [Field K] {b : ℕ} (β : S0 b → K) : Sd b → K :=
  fun x => if h : x = z0 b then 0 else β ⟨x, h⟩

theorem sum_dz (K : Type) [Field K] {b : ℕ} (c : K) (α : S0 b → K) :
    ∑ x : Sd b, (if h : x = z0 b then c else α ⟨x, h⟩) = c + ∑ y, α y := by
  rw [← (Equiv.optionSubtypeNe (z0 b)).sum_comp, Fintype.sum_option]
  congr 1
  · simp
  · refine Finset.sum_congr rfl (fun y _ => ?_)
    simp [y.2]

def Phi (K : Type) [Field K] (b : ℕ) :
    ((S0 b → K) × (S0 b → K)) →ₗ[K] Matrix (Sd b) (Sd b) K where
  toFun p := Matrix.vecMulVec (uf K p.1 p.2) (fun _ => 1) + Matrix.vecMulVec (fun _ => 1) (vf K p.2)
  map_add' p q := by
    ext x y
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, uf, vf, Prod.fst_add, Prod.snd_add,
      Pi.add_apply, Finset.sum_add_distrib]
    split_ifs <;> ring
  map_smul' c p := by
    ext x y
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, uf, vf, Prod.smul_fst,
      Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    split_ifs <;> ring

theorem Phi_inj (K : Type) [Field K] (b : ℕ) : Function.Injective (Phi K b) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨α, β⟩ h
  have he : ∀ x y, uf K α β x + vf K β y = 0 := by
    intro x y
    have := congrFun (congrFun h x) y
    simpa [Phi, Matrix.vecMulVec_apply] using this
  have hu : ∀ x, uf K α β x = 0 := fun x => by
    have := he x (z0 b)
    simpa [vf] using this
  have hv : ∀ y, vf K β y = 0 := fun y => by
    have := he (z0 b) y
    rwa [hu, zero_add] at this
  ext y
  · have := hu y.1
    simpa [uf, y.2] using this
  · have := hv y.1
    simpa [vf, y.2] using this

theorem Phi_R (K : Type) [Field K] (b : ℕ) : LinearMap.range (Phi K b) ≤ Rs K b := by
  rintro _ ⟨⟨α, β⟩, rfl⟩
  refine ⟨uf K α β, vf K β, rfl, ?_⟩
  simp only [uf, vf]
  rw [sum_dz, sum_dz]
  ring

theorem finrank_R (K : Type) [Field K] (b : ℕ) :
    2 * (2 ^ (b + 1) - 1) ≤ Module.finrank K (Rs K b) := by
  have h1 := LinearMap.finrank_range_of_inj (Phi_inj K b)
  have h2 := Submodule.finrank_mono (Phi_R K b)
  rw [h1, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, card_S0] at h2
  omega

/- realizing a scan on a finite-dimensional space -/

theorem embed (K : Type) [Field K] (d m : ℕ) (hd : d ≤ m) :
    ∃ (inj : (Fin d → K) →ₗ[K] (Fin m → K)) (proj : (Fin m → K) →ₗ[K] (Fin d → K)),
      ∀ v, proj (inj v) = v := by
  refine ⟨{ toFun := fun v j => if h : j.val < d then v ⟨j.val, h⟩ else 0
            map_add' := fun v w => by
              funext j
              simp only [Pi.add_apply]
              split_ifs <;> simp
            map_smul' := fun r v => by
              funext j
              simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
              split_ifs <;> simp },
    LinearMap.funLeft K K (Fin.castLE hd), fun v => ?_⟩
  funext i
  simp [LinearMap.funLeft]

theorem realize {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {X Q : Type} (n m : ℕ) (hm : Module.finrank K V ≤ m) (rep : X → V)
    (x0 : X) (T : Q → X → X) (g : X → K) (step : Q → V →ₗ[K] V) (out : V →ₗ[K] K)
    (hstep : ∀ c x, step c (rep x) = rep (T c x)) (hout : ∀ x, out (rep x) = g x) :
    ∃ (s : Fin m → K) (step' : Fin n → Q → (Fin m → K) →ₗ[K] (Fin m → K))
      (out' : (Fin m → K) →ₗ[K] K),
      ∀ C : Fin n → Q, out' ((List.finRange n).foldl (fun v i => step' i (C i) v) s) =
        g ((List.finRange n).foldl (fun x i => T (C i) x) x0) := by
  obtain ⟨inj, proj, hpi⟩ := embed K _ m hm
  let e := (Module.finBasis K V).equivFun
  let ι : V →ₗ[K] (Fin m → K) := inj ∘ₗ e.toLinearMap
  let π : (Fin m → K) →ₗ[K] V := e.symm.toLinearMap ∘ₗ proj
  have hπι : ∀ v, π (ι v) = v := by
    intro v
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_coe, hpi, LinearEquiv.symm_apply_apply]
  refine ⟨ι (rep x0), fun _ c => ι ∘ₗ step c ∘ₗ π, out ∘ₗ π, fun C => ?_⟩
  have hfold : ∀ (l : List (Fin n)) (x : X),
      π (l.foldl (fun v i => (ι ∘ₗ step (C i) ∘ₗ π) v) (ι (rep x))) =
        rep (l.foldl (fun x i => T (C i) x) x) := by
    intro l
    induction l with
    | nil => intro x; exact hπι _
    | cons i l ih =>
      intro x
      simp only [List.foldl_cons, LinearMap.coe_comp, Function.comp_apply, hπι, hstep]
      exact ih _
  rw [LinearMap.comp_apply, hfold, hout]

/- the upper bound -/

def Lc (K : Type) [Field K] {b : ℕ} (c : Ct b) : W K b →ₗ[K] W K b where
  toFun B := ⟨Fm K (wm c) * B.1,
    W_inv K _ (Finite.injective_iff_bijective.1 (wm_inj c)) B.1 B.2⟩
  map_add' B B' := Subtype.ext (Matrix.mul_add _ _ _)
  map_smul' r B := Subtype.ext (Matrix.mul_smul _ r _)

def trW (K : Type) [Field K] (b : ℕ) : W K b →ₗ[K] K :=
  (Matrix.traceLinearMap (Sd b) K K) ∘ₗ (W K b).subtype

def st0 (K : Type) [Field K] (b : ℕ) (F : ℕ → Ct b) (t : ℕ) : W K b :=
  ⟨Fm K (pr F t), Fm_W K _ (pr_bij F t)⟩

theorem fold_W (K : Type) [Field K] (a b : ℕ) (C : Fin (a + 1) → Ct b) :
    ((List.finRange (a + 1)).foldl (fun x i => Lc K (C i) x) (st0 K b (Cn a b C) 0)) =
      st0 K b (Cn a b C) (a + 1) := by
  have e1 : (fun x (i : Fin (a + 1)) => Lc K (C i) x) =
      fun x i => Lc K (Cn a b C i.val) x := by
    funext x i
    rw [Cn, site_fin]
  rw [e1]
  exact fold_eq (fun t x => Lc K (Cn a b C t) x) (st0 K b (Cn a b C))
    (fun t => Subtype.ext (by
      show Fm K (pr (Cn a b C) (t + 1)) = Fm K (wm (Cn a b C t)) * Fm K (pr (Cn a b C) t)
      rw [Fm_mul]
      rfl)) (a + 1)

theorem upper (K : Type) [Field K] (a b m : ℕ)
    (hm : (if ringChar K = 2 then (2 ^ (b + 1) - 2) ^ 2 else (2 ^ (b + 1) - 1) ^ 2 + 1) ≤ m) :
    ∃ (s : Fin m → K) (step : Fin (a + 1) → Ct b → (Fin m → K) →ₗ[K] (Fin m → K))
      (out : (Fin m → K) →ₗ[K] K),
      ∀ C : Fin (a + 1) → Ct b,
        out ((List.finRange (a + 1)).foldl (fun v i => step i (C i) v) s) = (cnt a b C : K) := by
  have hfin : ∀ C : Fin (a + 1) → Ct b, (cnt a b C : K) = trW K b
      ((List.finRange (a + 1)).foldl (fun x i => Lc K (C i) x) (st0 K b (fun _ _ => false) 0)) := by
    intro C
    rw [show st0 K b (fun _ _ => false) 0 = st0 K b (Cn a b C) 0 from rfl, fold_W, cnt_trace]
    rfl
  have hD : 1 ≤ 2 ^ (b + 1) - 1 := by
    have : 2 ≤ 2 ^ (b + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  by_cases hK : ringChar K = 2
  · rw [if_pos hK] at hm
    haveI : CharP K 2 := ringChar.of_eq hK
    let Z : Submodule K (W K b) := (Rs K b).comap (W K b).subtype
    have hZ : Module.finrank K Z = Module.finrank K (Rs K b) :=
      (Submodule.comapSubtypeEquivOfLe (Rs_W K b)).finrank_eq
    have hq := Submodule.finrank_quotient_add_finrank Z
    have hW := finrank_W K b
    have hR := finrank_R K b
    have hdim : Module.finrank K (W K b ⧸ Z) ≤ m := by
      refine le_trans ?_ hm
      obtain ⟨E, hE⟩ : ∃ E, 2 ^ (b + 1) - 1 = E + 1 := ⟨2 ^ (b + 1) - 2, by omega⟩
      rw [show 2 ^ (b + 1) - 2 = E by omega]
      rw [hE] at hW hR
      nlinarith
    have hinv : ∀ c : Ct b, Z ≤ Z.comap (Lc K c) := by
      intro c B hB
      exact Rs_inv K _ (Finite.injective_iff_bijective.1 (wm_inj c)) B.1 hB
    have hker : Z ≤ LinearMap.ker (trW K b) := by
      intro B hB
      exact Rs_trace K B.1 hB
    obtain ⟨s, step, out, h⟩ := realize (a + 1) m hdim Z.mkQ (st0 K b (fun _ _ => false) 0)
      (fun c x => Lc K c x) (fun x => trW K b x)
      (fun c => Z.mapQ Z (Lc K c) (hinv c)) (Z.liftQ (trW K b) hker)
      (fun c x => Submodule.mapQ_apply _ _ _ _) (fun x => Submodule.liftQ_apply _ _ _)
    exact ⟨s, fun i c => step i c, out, fun C => by rw [h C, hfin C]⟩
  · rw [if_neg hK] at hm
    obtain ⟨s, step, out, h⟩ := realize (a + 1) m ((finrank_W K b).trans hm) (fun x => x)
      (st0 K b (fun _ _ => false) 0) (fun c x => Lc K c x) (fun x => trW K b x)
      (fun c => Lc K c) (trW K b) (fun c x => rfl) (fun x => rfl)
    exact ⟨s, fun i c => step i c, out, fun C => by rw [h C, hfin C]⟩

/- bits and linear rows -/

def tz {b : ℕ} (s : Sd b) : VV (b + 1) := fun k => if s k then 1 else 0

def fz {b : ℕ} (v : VV (b + 1)) : Sd b := fun k => decide (v k = 1)

theorem tz_fz {b : ℕ} (v : VV (b + 1)) : tz (fz v) = v := by
  funext k
  simp only [tz, fz]
  rcases zmod2_cases (v k) with h | h <;> simp [h]

theorem fz_tz {b : ℕ} (s : Sd b) : fz (tz s) = s := by
  funext k
  simp only [tz, fz]
  by_cases h : s k <;> simp [h]

theorem tz_inj {b : ℕ} : Function.Injective (tz (b := b)) := fun s s' h => by
  rw [← fz_tz s, h, fz_tz]

theorem tz_z0 (b : ℕ) : tz (z0 b) = 0 := by
  funext k
  simp [tz, z0]

def lin {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (s : Sd b) : Sd b :=
  fz (M.mulVec (tz s))

theorem lin_mul {b : ℕ} (M N : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (s : Sd b) :
    lin (M * N) s = lin M (lin N s) := by
  simp only [lin, tz_fz, Matrix.mulVec_mulVec]

theorem lin_one {b : ℕ} (s : Sd b) : lin 1 s = s := by
  simp [lin, fz_tz]

theorem lin_z0 {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) : lin M (z0 b) = z0 b := by
  rw [lin, tz_z0, Matrix.mulVec_zero, ← tz_z0 b, fz_tz]

theorem lin_inv {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0)
    (s : Sd b) : lin M⁻¹ (lin M s) = s := by
  rw [← lin_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), lin_one]

theorem lin_inj {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0) :
    Function.Injective (lin M) := fun s s' h => by
  rw [← lin_inv M hM s, h, lin_inv M hM s']

def lc {b : ℕ} (c : Fin b → ZMod 2) : Ct b :=
  fun r => decide (∑ j, c j * (if r j then 1 else 0) = 1)

theorem tz_xor (p q : Bool) :
    (if xor p q then (1 : ZMod 2) else 0) = (if p then 1 else 0) + (if q then 1 else 0) := by
  cases p <;> cases q <;> decide

theorem ite_dec (x : ZMod 2) : (if decide (x = 1) = true then (1 : ZMod 2) else 0) = x := by
  rcases zmod2_cases x with h | h <;> simp [h]

theorem wm_lc {b : ℕ} (c : Fin b → ZMod 2) (s : Sd b) : wm (lc c) s = lin (Am b c) s := by
  apply tz_inj
  rw [lin, tz_fz]
  funext k
  rw [Am, sh_mulVec]
  by_cases h : k.val < b
  · rw [dif_pos h]
    simp only [tz]
    rw [wm_lt _ _ _ h]
  · rw [dif_neg h]
    have hk : k = Fin.last b := Fin.ext (by simp; omega)
    subst hk
    simp only [tz]
    rw [wm_last, tz_xor, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, one_mul, lc, ite_dec]

theorem lc_zero (b : ℕ) : lc (0 : Fin b → ZMod 2) = fun _ => false := by
  funext r
  simp [lc]

theorem real_lin {b : ℕ} (M : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (hM : M.det ≠ 0)
    (L : ℕ) (hL : 2 * b + 1 ≤ L) : ∃ F : ℕ → Ct b, pr F L = lin M := by
  obtain ⟨D, hD⟩ := surj M hM L hL
  refine ⟨fun t => lc (D t), ?_⟩
  rw [← hD]
  have : ∀ t, pr (fun t => lc (D t)) t = lin (Lp b D t) := by
    intro t
    induction t with
    | zero =>
      funext s
      exact (lin_one s).symm
    | succ t ih =>
      funext s
      show wm (lc (D t)) (pr (fun t => lc (D t)) t s) = lin (Am b (D t) * Lp b D t) s
      rw [ih, lin_mul, wm_lc]
  exact this L

theorem real_cat {b : ℕ} (F1 F2 : ℕ → Ct b) (c : Ct b) (L1 L2 : ℕ) :
    ∃ F : ℕ → Ct b, pr F (L1 + 1 + L2) = pr F2 L2 ∘ wm c ∘ pr F1 L1 := by
  refine ⟨fun t => if t < L1 then F1 t else if t = L1 then c else F2 (t - (L1 + 1)), ?_⟩
  funext s
  simp only [pr, Function.comp_apply]
  rw [orb_add]
  have h1 : orb (fun t => if t < L1 then F1 t else if t = L1 then c else F2 (t - (L1 + 1))) s
      (L1 + 1) = wm c (orb F1 s L1) := by
    show wm (if L1 < L1 then F1 L1 else if L1 = L1 then c else F2 (L1 - (L1 + 1)))
      (orb (fun t => if t < L1 then F1 t else if t = L1 then c else F2 (t - (L1 + 1))) s L1) = _
    rw [if_neg (lt_irrefl _), if_pos rfl]
    rw [orb_congr _ F1 s L1 (fun t ht => if_pos ht)]
  rw [h1]
  refine orb_congr _ _ _ _ (fun t _ => ?_)
  rw [if_neg (by omega), if_neg (by omega)]
  congr 1
  omega

/- the nonlinear row -/

def e0 (b : ℕ) : Sd b := fun k => decide (k.val = 0)

def dl (b : ℕ) : Ct b := fun r => decide (∀ j, r j = false)

theorem e0_ne (b : ℕ) : e0 b ≠ z0 b := by
  intro h
  have := congrFun h 0
  simp [e0, z0] at this

theorem dl_eq (b : ℕ) (s : Sd b) :
    wm (dl b) s = wm (fun _ => false) (Equiv.swap (z0 b) (e0 b) s) := by
  have hne : ∀ k : Fin (b + 1), k.val ≠ 0 → Equiv.swap (z0 b) (e0 b) s k = s k := by
    intro k hk
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1
      simp [z0, e0, hk]
    · subst h2
      simp [z0, e0, hk]
    · rfl
  funext k
  by_cases h : k.val < b
  · rw [wm_lt _ _ _ h, wm_lt _ _ _ h, hne _ (by simp)]
  · have hk : k = Fin.last b := Fin.ext (by simp; omega)
    subst hk
    rw [wm_last, wm_last, Bool.xor_false]
    rw [Equiv.swap_apply_def]
    split_ifs with h1 h2
    · subst h1
      simp [dl, z0, e0]
    · subst h2
      simp [dl, z0, e0]
    · have hd : dl b (fun j => s j.succ) = false := by
        simp only [dl, decide_eq_false_iff_not]
        intro hall
        cases h0 : s 0
        · apply h1
          funext k
          refine Fin.cases ?_ (fun j => ?_) k
          · simp [z0, h0]
          · simp [z0, hall j]
        · apply h2
          funext k
          refine Fin.cases ?_ (fun j => ?_) k
          · simp [e0, h0]
          · simp [e0, hall j]
      rw [hd, Bool.xor_false]

theorem wm_false (b : ℕ) (s : Sd b) : wm (fun _ => false) s = lin (Am b 0) s := by
  rw [← wm_lc, lc_zero]

/- moving a nonzero vector to the first unit vector -/

theorem zz_self (x : ZMod 2) : x + x = 0 := by
  rcases zmod2_cases x with h | h <;> rw [h] <;> decide

theorem exA {b : ℕ} (v : VV (b + 1)) (hv : v ≠ 0) :
    ∃ A : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2), A.det ≠ 0 ∧ A.mulVec v = tz (e0 b) := by
  obtain ⟨k, hk⟩ : ∃ k, v k = 1 := by
    by_contra hc
    push_neg at hc
    apply hv
    funext k
    exact (zmod2_cases (v k)).resolve_right (hc k)
  let P : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
    Matrix.of fun i j => if j = Equiv.swap 0 k i then 1 else 0
  have hPv : ∀ u, P.mulVec u = fun i => u (Equiv.swap 0 k i) := by
    intro u
    funext i
    simp [P, Matrix.mulVec, dotProduct]
  have hPP : P * P = 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (Equiv.swap 0 k i)]
    · simp [P, Matrix.one_apply, eq_comm]
    · intro l _ hl
      simp [P, hl]
    · simp
  have hP : P.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hPP
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  set u := P.mulVec v with hu
  have hu0 : u 0 = 1 := by
    rw [hu, hPv]
    simp [hk]
  let N : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2) :=
    Matrix.of fun i j => if j = 0 ∧ i ≠ 0 then u i else 0
  have hN : ∀ i, N.mulVec u i = if i ≠ 0 then u i else 0 := by
    intro i
    simp only [N, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_eq_single 0]
    · by_cases hi : i = 0
      · simp [hi]
      · simp [hi, hu0]
    · intro j _ hj
      simp [hj]
    · simp
  have hE : (1 + N).det ≠ 0 := by
    have ht : (1 + N).IsLowerTriangular := by
      intro i j hij
      have hij' : i < j := hij
      have h1 : i ≠ j := ne_of_lt hij'
      have h2 : j ≠ 0 := by
        intro h
        rw [h] at hij'
        exact absurd hij' (Fin.not_lt_zero _)
      simp [N, Matrix.one_apply, h1, h2]
    rw [Matrix.det_of_isLowerTriangular _ ht]
    have : ∀ i, (1 + N) i i = 1 := by
      intro i
      simp [N]
    simp [this]
  refine ⟨(1 + N) * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    exact mul_ne_zero hE hP
  · rw [← Matrix.mulVec_mulVec, ← hu, Matrix.add_mulVec, Matrix.one_mulVec]
    funext i
    rw [Pi.add_apply, hN]
    by_cases hi : i = 0
    · subst hi
      simp [tz, e0, hu0]
    · have hv : i.val ≠ 0 := fun h => hi (Fin.ext h)
      rw [if_pos hi, zz_self]
      simp [tz, e0, hv]

/- the realizable span -/

def SP (K : Type) [Field K] (b L : ℕ) : Submodule K (Matrix (Sd b) (Sd b) K) :=
  Submodule.span K (Set.range fun F : ℕ → Ct b => Fm K (pr F L))

def fv (K : Type) [Field K] {b : ℕ} (x : Sd b) : Sd b → K := Pi.single x 1 - Pi.single (z0 b) 1

theorem Fm_diff (K : Type) [Field K] {b : ℕ} (σ : Sd b → Sd b) (h0 : σ (z0 b) = z0 b)
    (r : Sd b) (hr : r ≠ z0 b) :
    Fm K σ - Fm K (σ ∘ Equiv.swap r (z0 b)) = Matrix.vecMulVec (fv K (σ r)) (fv K r) := by
  ext x y
  simp only [Matrix.sub_apply, Fm, Matrix.of_apply, Matrix.vecMulVec_apply, fv, Pi.sub_apply,
    Pi.single_apply, Function.comp_apply]
  by_cases hy1 : y = r
  · subst hy1
    simp [h0, hr]
  · by_cases hy2 : y = z0 b
    · subst hy2
      simp [h0, Ne.symm hr]
      try ring
    · simp [Equiv.swap_apply_of_ne_of_ne hy1 hy2, hy1, hy2]

theorem op_mem (K : Type) [Field K] {b L : ℕ} (hL : 4 * b + 3 ≤ L) (r s : Sd b)
    (hr : r ≠ z0 b) (hs : s ≠ z0 b) : Matrix.vecMulVec (fv K s) (fv K r) ∈ SP K b L := by
  have hz : ∀ x : Sd b, x ≠ z0 b → tz x ≠ 0 := fun x hx h => hx (tz_inj (h.trans (tz_z0 b).symm))
  obtain ⟨Ar, hAr, hAr'⟩ := exA (tz r) (hz r hr)
  obtain ⟨As, hAs, hAs'⟩ := exA (tz s) (hz s hs)
  have hlr : lin Ar r = e0 b := by rw [lin, hAr', fz_tz]
  have hls : lin As s = e0 b := by rw [lin, hAs', fz_tz]
  have hdi : ∀ A : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2), A.det ≠ 0 → A⁻¹.det ≠ 0 := by
    intro A hA h
    have := Matrix.det_nonsing_inv_mul_det A (isUnit_iff_ne_zero.2 hA)
    rw [h, zero_mul] at this
    exact zero_ne_one this
  set B := As⁻¹ * Ar with hB
  have hBd : B.det ≠ 0 := by
    rw [hB, Matrix.det_mul]
    exact mul_ne_zero (hdi As hAs) hAr
  have hBr : lin B r = s := by
    rw [hB, lin_mul, hlr, ← hls, lin_inv As hAs]
  have hσ : Fm K (lin B) ∈ SP K b L := by
    obtain ⟨F, hF⟩ := real_lin B hBd L (by omega)
    rw [← hF]
    exact Submodule.subset_span ⟨F, rfl⟩
  have hA0 : (Am b 0).det ≠ 0 := by
    rw [det_am]
    exact one_ne_zero
  set G := B * Ar⁻¹ * (Am b 0)⁻¹ with hG
  have hGd : G.det ≠ 0 := by
    rw [hG, Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero hBd (hdi Ar hAr)) (hdi _ hA0)
  have hτ : Fm K (lin B ∘ Equiv.swap r (z0 b)) ∈ SP K b L := by
    obtain ⟨F1, hF1⟩ := real_lin Ar hAr (2 * b + 1) le_rfl
    obtain ⟨F2, hF2⟩ := real_lin G hGd (L - (2 * b + 2)) (by omega)
    obtain ⟨F, hF⟩ := real_cat F1 F2 (dl b) (2 * b + 1) (L - (2 * b + 2))
    have hL' : 2 * b + 1 + 1 + (L - (2 * b + 2)) = L := by omega
    rw [hL', hF1, hF2] at hF
    have he : lin G ∘ wm (dl b) ∘ lin Ar = lin B ∘ Equiv.swap r (z0 b) := by
      funext x
      simp only [Function.comp_apply]
      rw [dl_eq, wm_false, ← lin_mul, hG, Matrix.mul_assoc, Matrix.nonsing_inv_mul _
        (isUnit_iff_ne_zero.2 hA0), Matrix.mul_one, lin_mul]
      have hsw : Equiv.swap (z0 b) (e0 b) (lin Ar x) = lin Ar (Equiv.swap (z0 b) r x) := by
        have := (lin_inj Ar hAr).swap_apply (z0 b) r x
        rwa [lin_z0, hlr] at this
      rw [hsw, lin_inv Ar hAr, Equiv.swap_comm]
    rw [← he, ← hF]
    exact Submodule.subset_span ⟨F, rfl⟩
  have h := Submodule.sub_mem _ hσ hτ
  rwa [Fm_diff K (lin B) (lin_z0 B) r hr, hBr] at h

theorem one_SP (K : Type) [Field K] {b L : ℕ} (hL : 2 * b + 1 ≤ L) :
    (1 : Matrix (Sd b) (Sd b) K) ∈ SP K b L := by
  obtain ⟨F, hF⟩ := real_lin (1 : Matrix (Fin (b + 1)) (Fin (b + 1)) (ZMod 2)) (by simp) L hL
  have : Fm K (pr F L) = 1 := by
    rw [hF]
    ext x y
    simp [Fm, lin_one, Matrix.one_apply]
  rw [← this]
  exact Submodule.subset_span ⟨F, rfl⟩

theorem fv_z0 (K : Type) [Field K] (b : ℕ) : fv K (z0 b) = 0 := sub_self _

theorem decomp (K : Type) [Field K] {b : ℕ} (M : Matrix (Sd b) (Sd b) K)
    (hrow : ∀ x, ∑ j, M x j = 0) (hcol : ∀ y, ∑ i, M i y = 0) :
    M = ∑ s, ∑ r, M s r • Matrix.vecMulVec (fv K s) (fv K r) := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, fv, Pi.sub_apply,
    Pi.single_apply, smul_eq_mul]
  have inner : ∀ s, ∑ r, M s r * (((if x = s then 1 else 0) - (if x = z0 b then 1 else 0)) *
      ((if y = r then 1 else 0) - (if y = z0 b then 1 else 0))) =
      ((if x = s then 1 else 0) - (if x = z0 b then 1 else 0)) * M s y := by
    intro s
    have e : ∀ r, M s r * (((if x = s then (1 : K) else 0) - (if x = z0 b then 1 else 0)) *
        ((if y = r then 1 else 0) - (if y = z0 b then 1 else 0))) =
        ((if x = s then (1 : K) else 0) - (if x = z0 b then 1 else 0)) *
          ((if y = r then M s r else 0) - (if y = z0 b then M s r else 0)) := by
      intro r
      split_ifs <;> ring
    simp only [e, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    by_cases hy : y = z0 b
    · simp only [hy, if_true, hrow, sub_zero]
    · simp only [hy, if_false, Finset.sum_const_zero, sub_zero]
  simp only [inner]
  have e2 : ∀ s, ((if x = s then (1 : K) else 0) - (if x = z0 b then 1 else 0)) * M s y =
      (if x = s then M s y else 0) - (if x = z0 b then M s y else 0) := by
    intro s
    split_ifs <;> ring
  simp only [e2, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hx : x = z0 b
  · simp only [hx, if_true, hcol, sub_zero]
  · simp only [hx, if_false, Finset.sum_const_zero, sub_zero]

theorem spanW (K : Type) [Field K] {b L : ℕ} (hL : 4 * b + 3 ≤ L) (Y : Matrix (Sd b) (Sd b) K)
    (hY : Y ∈ W K b) : Y ∈ SP K b L := by
  set lam := ∑ j, Y (z0 b) j with hlam
  set M := Y - lam • (1 : Matrix (Sd b) (Sd b) K) with hM
  have hY' : ∀ x y, ∑ j, Y x j = ∑ i, Y i y := hY
  have hrow : ∀ x, ∑ j, M x j = 0 := by
    intro x
    simp only [hM, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    rw [hY' x (z0 b), ← hY' (z0 b) (z0 b), hlam, sub_self]
  have hcol : ∀ y, ∑ i, M i y = 0 := by
    intro y
    simp only [hM, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [← hY' (z0 b) y, hlam, sub_self]
  have e : Y = lam • 1 + M := by
    rw [hM]
    abel
  rw [e, decomp K M hrow hcol]
  refine Submodule.add_mem _ (Submodule.smul_mem _ _ (one_SP K (by omega)))
    (Submodule.sum_mem _ fun s _ => Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_)
  by_cases hs : s = z0 b
  · rw [hs, fv_z0]
    have : Matrix.vecMulVec (0 : Sd b → K) (fv K r) = 0 := by
      ext x y
      simp [Matrix.vecMulVec_apply]
    rw [this]
    exact Submodule.zero_mem _
  · by_cases hr : r = z0 b
    · rw [hr, fv_z0]
      have : Matrix.vecMulVec (fv K s) (0 : Sd b → K) = 0 := by
        ext x y
        simp [Matrix.vecMulVec_apply]
      rw [this]
      exact Submodule.zero_mem _
    · exact op_mem K hL r s hr hs

/- the rank argument -/

theorem rank_bound {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (A : Matrix ι (Fin d) K) (B : Matrix (Fin d) ι K) (h : A * B = 1) : Fintype.card ι ≤ d := by
  have h1 := Matrix.rank_mul_le_left A B
  have h2 := Matrix.rank_le_card_width A
  rw [h, Matrix.rank_one] at h1
  simpa using h1.trans h2

theorem dual_bound {K : Type} [Field K] {X Y N ι : Type} [Fintype X] [Fintype Y] [Fintype N]
    [DecidableEq N] [Fintype ι] [DecidableEq ι] (m : ℕ)
    (P : X → Matrix N N K) (Q : Y → Matrix N N K) (u : X → Fin m → K) (v : Y → Fin m → K)
    (hf : ∀ x y, (Q y * P x).trace = ∑ j, u x j * v y j)
    (A B : ι → Matrix N N K) (hA : ∀ k, A k ∈ Submodule.span K (Set.range P))
    (hB : ∀ k, B k ∈ Submodule.span K (Set.range Q))
    (hd : ∀ k l, (B l * A k).trace = if k = l then 1 else 0) : Fintype.card ι ≤ m := by
  choose c hc using fun k => (Submodule.mem_span_range_iff_exists_fun K).1 (hA k)
  choose e he using fun k => (Submodule.mem_span_range_iff_exists_fun K).1 (hB k)
  have h3 : ∀ T : X → Y → Fin m → K, ∑ j, ∑ y, ∑ x, T x y j = ∑ x, ∑ y, ∑ j, T x y j := by
    intro T
    calc ∑ j, ∑ y, ∑ x, T x y j = ∑ y, ∑ j, ∑ x, T x y j := Finset.sum_comm
      _ = ∑ y, ∑ x, ∑ j, T x y j := Finset.sum_congr rfl (fun y _ => Finset.sum_comm)
      _ = ∑ x, ∑ y, ∑ j, T x y j := Finset.sum_comm
  have hM : (Matrix.of fun (k : ι) (j : Fin m) => ∑ x, c k x * u x j) *
      (Matrix.of fun (j : Fin m) (l : ι) => ∑ y, e l y * v y j) = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply, ← hd k l, ← hc k, ← he l]
    simp only [Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, hf]
    refine (h3 (fun x y j => c k x * u x j * (e l y * v y j))).trans ?_
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ =>
      Finset.sum_congr rfl (fun j _ => by beta_reduce; ring)))
  exact rank_bound m _ _ hM

/- the lower bound -/

theorem lower (K : Type) [Field K] (a b m : ℕ) (hn : 8 * (b + 1) ≤ a + 1)
    (s : Fin m → K) (step : Fin (a + 1) → Ct b → (Fin m → K) →ₗ[K] (Fin m → K))
    (out : (Fin m → K) →ₗ[K] K)
    (hsc : ∀ C : Fin (a + 1) → Ct b,
        out ((List.finRange (a + 1)).foldl (fun v i => step i (C i) v) s) = (cnt a b C : K))
    {ι : Type} [Fintype ι] [DecidableEq ι] (A B : ι → Matrix (Sd b) (Sd b) K)
    (hA : ∀ k, A k ∈ W K b) (hB : ∀ k, B k ∈ W K b)
    (hd : ∀ k l, (B l * A k).trace = if k = l then 1 else 0) : Fintype.card ι ≤ m := by
  set i0 := 4 * (b + 1) with hi0
  let mix : (Fin (a + 1) → Ct b) → (Fin (a + 1) → Ct b) → (Fin (a + 1) → Ct b) :=
    fun τ σ j => if j.val < i0 then τ j else σ j
  let u : (Fin (a + 1) → Ct b) → Fin m → K := fun τ =>
    ((List.finRange (a + 1)).take i0).foldl (fun v j => step j (τ j) v) s
  have hL : ∀ σ : Fin (a + 1) → Ct b, ∃ L : (Fin m → K) →ₗ[K] (Fin m → K), ∀ v,
      ((List.finRange (a + 1)).drop i0).foldl (fun v j => step j (σ j) v) v = L v :=
    fun σ => fold_lin _ (fun j => step j (σ j))
  choose L hL using hL
  have key : ∀ τ σ, out (L σ (u τ)) = (cnt a b (mix τ σ) : K) := by
    intro τ σ
    have e1 : ((List.finRange (a + 1)).take i0).foldl
        (fun v j => step j (mix τ σ j) v) s = u τ :=
      fold_congr _ (fun j => ⇑(step j (mix τ σ j))) (fun j => ⇑(step j (τ j)))
        (fun x hx => by simp only [mix, if_pos (mem_take_lt hx)]) s
    have e2 : ∀ v, ((List.finRange (a + 1)).drop i0).foldl
        (fun v j => step j (mix τ σ j) v) v =
        ((List.finRange (a + 1)).drop i0).foldl (fun v j => step j (σ j) v) v :=
      fun v => fold_congr _ (fun j => ⇑(step j (mix τ σ j))) (fun j => ⇑(step j (σ j)))
        (fun x hx => by simp only [mix, if_neg (not_lt.2 (mem_drop_ge hx))]) v
    rw [← hsc, ← hL σ, ← e1, ← e2, ← List.foldl_append, List.take_append_drop]
  let Bv : (Fin (a + 1) → Ct b) → Fin m → K :=
    fun σ j => out (L σ (fun j' => if j = j' then 1 else 0))
  have hfac : ∀ τ σ, (cnt a b (mix τ σ) : K) = ∑ j, u τ j * Bv σ j := by
    intro τ σ
    rw [← key]
    conv_lhs => rw [pi_eq_sum_univ (u τ)]
    simp only [map_sum, map_smul, smul_eq_mul, Bv]
  let Pp : (Fin (a + 1) → Ct b) → Matrix (Sd b) (Sd b) K :=
    fun τ => Fm K (pr (fun t => τ (site a t)) i0)
  let Qq : (Fin (a + 1) → Ct b) → Matrix (Sd b) (Sd b) K :=
    fun σ => Fm K (pr (fun t => σ (site a (i0 + t))) (a + 1 - i0))
  have hfix : ∀ τ σ, (Qq σ * Pp τ).trace = ∑ j, u τ j * Bv σ j := by
    intro τ σ
    rw [← hfac, cnt_trace]
    show (Fm K _ * Fm K _).trace = _
    rw [Fm_mul]
    congr 2
    funext x
    simp only [pr, Function.comp_apply]
    rw [show a + 1 = i0 + (a + 1 - i0) by omega, orb_add]
    rw [show i0 + (a + 1 - i0) - i0 = a + 1 - i0 by omega]
    rw [orb_congr (Cn a b (mix τ σ)) (fun t => τ (site a t)) x i0 (fun t ht => by
      show mix τ σ (site a t) = τ (site a t)
      have hv : (site a t).val < i0 := by
        rw [site_val, Nat.mod_eq_of_lt (by omega)]
        exact ht
      simp only [mix, hv, ↓reduceIte])]
    refine orb_congr _ _ _ _ (fun t ht => ?_)
    show σ (site a (i0 + t)) = mix τ σ (site a (i0 + t))
    have hv : ¬ (site a (i0 + t)).val < i0 := by
      rw [site_val, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [mix, hv, ↓reduceIte]
  have hP : ∀ k, A k ∈ Submodule.span K (Set.range Pp) := by
    intro k
    refine Submodule.span_mono ?_ (spanW K (L := i0) (by omega) (A k) (hA k))
    rintro _ ⟨F, rfl⟩
    refine ⟨fun j => F j.val, ?_⟩
    show Fm K _ = Fm K _
    congr 1
    funext x
    refine orb_congr _ _ _ _ (fun t ht => ?_)
    show F (site a t).val = F t
    rw [site_val, Nat.mod_eq_of_lt (by omega)]
  have hQ : ∀ k, B k ∈ Submodule.span K (Set.range Qq) := by
    intro k
    refine Submodule.span_mono ?_ (spanW K (L := a + 1 - i0) (by omega) (B k) (hB k))
    rintro _ ⟨F, rfl⟩
    refine ⟨fun j => F (j.val - i0), ?_⟩
    show Fm K _ = Fm K _
    congr 1
    funext x
    refine orb_congr _ _ _ _ (fun t ht => ?_)
    show F ((site a (i0 + t)).val - i0) = F t
    rw [site_val, Nat.mod_eq_of_lt (by omega), Nat.add_sub_cancel_left]
  exact dual_bound m Pp Qq u Bv hfix A B hP hQ hd

/- dual systems -/

theorem tr_op {K : Type} [Field K] {N : Type} [Fintype N] (p q p' q' : N → K) :
    (Matrix.vecMulVec p q * Matrix.vecMulVec p' q').trace = (q ⬝ᵥ p') * (q' ⬝ᵥ p) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct,
    Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem op_W {K : Type} [Field K] {b : ℕ} (p q : Sd b → K) (hp : ∑ x, p x = 0)
    (hq : ∑ x, q x = 0) : Matrix.vecMulVec p q ∈ W K b := by
  intro x y
  simp only [Matrix.vecMulVec_apply, ← Finset.mul_sum, ← Finset.sum_mul, hp, hq, mul_zero,
    zero_mul]

theorem sum_single_sub {K : Type} [Field K] {b : ℕ} (x z : Sd b) :
    ∑ y, (Pi.single x (1 : K) - Pi.single z 1 : Sd b → K) y = 0 := by
  simp [Finset.sum_sub_distrib]

theorem dot_ss {K : Type} [Field K] {b : ℕ} (i c i' c' : Sd b) :
    (Pi.single i (1 : K) - Pi.single c 1 : Sd b → K) ⬝ᵥ (Pi.single i' 1 - Pi.single c' 1) =
      (if i = i' then 1 else 0) - (if i = c' then 1 else 0) - (if c = i' then 1 else 0) +
        (if c = c' then 1 else 0) := by
  simp only [sub_dotProduct, dotProduct_sub, single_dotProduct, Pi.single_apply, one_mul]
  split_ifs <;> simp_all <;> ring

abbrev T2 (b : ℕ) := {x : Sd b // ¬ (x = z0 b ∨ x = e0 b)}

theorem card_T2 (b : ℕ) : Fintype.card (T2 b) = 2 ^ (b + 1) - 2 := by
  rw [Fintype.card_subtype_compl, card_Sd, Fintype.card_subtype]
  congr 1
  have : (Finset.univ.filter fun x : Sd b => x = z0 b ∨ x = e0 b) = {z0 b, e0 b} := by
    ext x
    simp
  rw [this, Finset.card_pair (e0_ne b).symm]

def hv (K : Type) [Field K] {b : ℕ} (x : Sd b) : Sd b → K := Pi.single x 1 - Pi.single (e0 b) 1

theorem dual_two (K : Type) [Field K] (b : ℕ) :
    ∃ (A B : T2 b × T2 b → Matrix (Sd b) (Sd b) K), (∀ k, A k ∈ W K b) ∧ (∀ k, B k ∈ W K b) ∧
      ∀ k l, (B l * A k).trace = if k = l then 1 else 0 := by
  refine ⟨fun k => Matrix.vecMulVec (fv K k.1.1) (fv K k.2.1),
    fun l => Matrix.vecMulVec (hv K l.2.1) (hv K l.1.1), fun k => ?_, fun k => ?_, ?_⟩
  · exact op_W _ _ (sum_single_sub _ _) (sum_single_sub _ _)
  · exact op_W _ _ (sum_single_sub _ _) (sum_single_sub _ _)
  · rintro ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
    rw [tr_op]
    simp only [hv, fv, dot_ss]
    push_neg at hk1 hk2 hl1 hl2
    have he := e0_ne b
    simp only [hk1.1, hk1.2, hk2.1, hk2.2, hl1.1, hl1.2, hl2.1, hl2.2, he, Ne.symm hk1.1,
      Ne.symm hk1.2, Ne.symm hk2.1, Ne.symm hk2.2, Ne.symm hl1.1, Ne.symm hl1.2, Ne.symm hl2.1,
      Ne.symm hl2.2, Ne.symm he, if_false, sub_zero, add_zero, Prod.mk.injEq, Subtype.mk.injEq]
    by_cases h1 : l1 = k1
    · subst h1
      by_cases h2 : k2 = l2
      · subst h2
        simp
      · simp [h2]
    · simp [h1, Ne.symm h1]

theorem dual_odd (K : Type) [Field K] (b : ℕ) (hK : ringChar K ≠ 2) :
    ∃ (A B : Option (S0 b × S0 b) → Matrix (Sd b) (Sd b) K), (∀ k, A k ∈ W K b) ∧
      (∀ k, B k ∈ W K b) ∧ ∀ k l, (B l * A k).trace = if k = l then 1 else 0 := by
  have hN : (Fintype.card (Sd b) : K) ≠ 0 := by
    rw [card_Sd, Nat.cast_pow, Nat.cast_ofNat]
    exact pow_ne_zero _ (Ring.two_ne_zero hK)
  set c := (Fintype.card (Sd b) : K)⁻¹ with hc
  have hcN : (Fintype.card (Sd b) : K) * c = 1 := mul_inv_cancel₀ hN
  let gv : Sd b → Sd b → K := fun x => Pi.single x 1 - fun _ => c
  have hsg : ∀ x, ∑ y, gv x y = 0 := by
    intro x
    simp only [gv, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ,
      if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcN, sub_self]
  have hcc : (fun _ : Sd b => (1 : K)) ⬝ᵥ (fun _ => c) = 1 := by
    simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcN]
  have h1f : ∀ x, (fun _ : Sd b => (1 : K)) ⬝ᵥ fv K x = 0 := by
    intro x
    simp only [dotProduct, one_mul]
    exact sum_single_sub _ _
  have h1g : ∀ x, (fun _ : Sd b => (1 : K)) ⬝ᵥ gv x = 0 := by
    intro x
    simp only [dotProduct, one_mul]
    exact hsg x
  have hfc : ∀ x, fv K x ⬝ᵥ (fun _ : Sd b => c) = 0 := by
    intro x
    simp only [dotProduct, ← Finset.sum_mul]
    rw [show ∑ i, fv K x i = 0 from sum_single_sub _ _, zero_mul]
  have hgc : ∀ x, gv x ⬝ᵥ (fun _ : Sd b => c) = 0 := by
    intro x
    simp only [dotProduct, ← Finset.sum_mul]
    rw [hsg, zero_mul]
  have hgf : ∀ r p : Sd b, r ≠ z0 b → gv r ⬝ᵥ fv K p = if r = p then 1 else 0 := by
    intro r p hr
    rw [show gv r = Pi.single r 1 - (fun _ => c) from rfl, sub_dotProduct, single_dotProduct,
      one_mul, dotProduct_comm (fun _ => c), hfc p, sub_zero]
    simp [fv, Pi.single_apply, hr]
  have hfg : ∀ q s : Sd b, s ≠ z0 b → fv K q ⬝ᵥ gv s = if q = s then 1 else 0 := by
    intro q s hs
    rw [show gv s = Pi.single s 1 - (fun _ => c) from rfl, dotProduct_sub, dotProduct_single,
      mul_one, hfc q, sub_zero]
    simp [fv, Pi.single_apply, hs, eq_comm]
  let A : Option (S0 b × S0 b) → Matrix (Sd b) (Sd b) K := fun k => match k with
    | none => Matrix.vecMulVec (fun _ => c) (fun _ => 1)
    | some p => Matrix.vecMulVec (fv K p.1.1) (fv K p.2.1)
  let B : Option (S0 b × S0 b) → Matrix (Sd b) (Sd b) K := fun k => match k with
    | none => Matrix.vecMulVec (fun _ => c) (fun _ => 1)
    | some p => Matrix.vecMulVec (gv p.2.1) (gv p.1.1)
  have hJ : Matrix.vecMulVec (fun _ : Sd b => c) (fun _ => (1 : K)) ∈ W K b := by
    intro x y
    simp [Matrix.vecMulVec_apply, Finset.sum_const, mul_comm]
  refine ⟨A, B, ?_, ?_, ?_⟩
  · rintro (_ | p)
    · exact hJ
    · exact op_W _ _ (sum_single_sub _ _) (sum_single_sub _ _)
  · rintro (_ | p)
    · exact hJ
    · exact op_W _ _ (hsg _) (hsg _)
  · rintro (_ | ⟨⟨p, hp⟩, ⟨q, hq⟩⟩) (_ | ⟨⟨r, hr⟩, ⟨s, hs⟩⟩)
    · show Matrix.trace (Matrix.vecMulVec _ _ * Matrix.vecMulVec _ _) = _
      rw [tr_op, hcc]
      simp
    · show Matrix.trace (Matrix.vecMulVec _ _ * Matrix.vecMulVec _ _) = _
      rw [tr_op, h1g, mul_zero]
      simp
    · show Matrix.trace (Matrix.vecMulVec _ _ * Matrix.vecMulVec _ _) = _
      rw [tr_op, h1f, zero_mul]
      simp
    · show Matrix.trace (Matrix.vecMulVec _ _ * Matrix.vecMulVec _ _) = _
      rw [tr_op, hgf r p hr, hfg q s hs]
      by_cases h1 : r = p
      · subst h1
        by_cases h2 : q = s
        · subst h2
          simp
        · simp [h2]
      · simp [h1, Ne.symm h1]

end

end PEqualNP.Outside.L_lib_592

open PEqualNP.Outside.L_lib_592 in
theorem PEqualNP.Outside.L_lib_592 : ∀ (K : Type) [Field K] (b : ℕ),
  let w := b + 1
  let D := 2 ^ w
  let threshold := if ringChar K = 2 then (D - 2) ^ 2 else (D - 1) ^ 2 + 1
  let Control := (Fin b → Bool) → Bool
  ∀ (a m : ℕ),
    let n := a + 1
    let count := fun (C : Fin n → Control) =>
      ((Finset.univ : Finset (Fin n → Bool)).filter (fun x =>
        ∀ i : Fin n,
          x (Fin.ofNat (a + 1) (i.val + w)) =
            xor (x i) (C i (fun j => x (Fin.ofNat (a + 1) (i.val + 1 + j.val)))))).card
    let admits :=
      ∃ (s : Fin m → K)
        (step : Fin n → Control → (Fin m → K) →ₗ[K] (Fin m → K))
        (out : (Fin m → K) →ₗ[K] K),
        ∀ C : Fin n → Control,
          out ((List.finRange n).foldl (fun v i => step i (C i) v) s) = (count C : K)
    (threshold ≤ m → admits) ∧ (8 * w ≤ n → admits → threshold ≤ m) := by
  intro K _ b
  dsimp only
  intro a m
  refine ⟨fun hm => upper K a b m hm, fun hn h => ?_⟩
  obtain ⟨s, step, out, hc⟩ := h
  by_cases hK : ringChar K = 2
  · rw [if_pos hK]
    obtain ⟨A, B, hA, hB, hd⟩ := dual_two K b
    have := lower K a b m hn s step out hc A B hA hB hd
    rwa [Fintype.card_prod, card_T2, ← sq] at this
  · rw [if_neg hK]
    obtain ⟨A, B, hA, hB, hd⟩ := dual_odd K b hK
    have := lower K a b m hn s step out hc A B hA hB hd
    rwa [Fintype.card_option, Fintype.card_prod, card_S0, ← sq] at this
