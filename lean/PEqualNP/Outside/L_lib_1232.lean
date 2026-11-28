import PEqualNP.Defs
import Mathlib

namespace PEqualNP.Outside.L_lib_1232_aux

open Finset

theorem decide_iff' {p q : Prop} {dp : Decidable p} {dq : Decidable q} (h : p ↔ q) :
    @decide p dp = @decide q dq := by
  cases dp with
  | isFalse hp =>
    cases dq with
    | isFalse hq => rfl
    | isTrue hq => exact absurd (h.mpr hq) hp
  | isTrue hp =>
    cases dq with
    | isFalse hq => exact absurd (h.mp hp) hq
    | isTrue hq => rfl

/-! ### generic helpers about decidability instances -/

theorem ite_iff {α : Type} {P Q : Prop} {dP : Decidable P} {dQ : Decidable Q} (h : P ↔ Q)
    (a b : α) : @ite α P dP a b = @ite α Q dQ a b := by
  by_cases hp : P
  · rw [if_pos hp, if_pos (h.mp hp)]
  · rw [if_neg hp, if_neg (fun hq => hp (h.mpr hq))]

theorem natCast_card_filter' {α : Type} [Fintype α] (P : α → Prop) {iP : DecidablePred P} :
    (((@Finset.filter α P iP univ).card : ℕ) : ZMod 2) = ∑ a, @ite _ (P a) (iP a) 1 0 := by
  rw [Finset.natCast_card_filter]

theorem mod2_iff {a b : ℕ} (h : (a : ZMod 2) = (b : ZMod 2)) : a % 2 = 1 ↔ b % 2 = 1 := by
  rw [ZMod.natCast_eq_natCast_iff'] at h; rw [h]

theorem decide_card_congr2 {α : Type} [Fintype α] (P Q : α → Prop) {iP : DecidablePred P}
    {iQ : DecidablePred Q} {d1 : Decidable ((@Finset.filter α P iP univ).card % 2 = 1)}
    {d2 : Decidable ((@Finset.filter α Q iQ univ).card % 2 = 1)}
    (h : ∀ x, P x ↔ Q x) : @decide _ d1 = @decide _ d2 := by
  have : @Finset.filter α P iP univ = @Finset.filter α Q iQ univ := by
    ext x; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h x
  apply decide_iff'
  rw [this]

/-! ### small gadget factors -/

def e4 : (Fin 4 → Bool) ≃ Bool × Bool × Bool × Bool where
  toFun Y := (Y 0, Y 1, Y 2, Y 3)
  invFun b := ![b.1, b.2.1, b.2.2.1, b.2.2.2]
  left_inv Y := by funext k; fin_cases k <;> rfl
  right_inv b := rfl

def e6 : (Fin 6 → Bool) ≃ Bool × Bool × Bool × Bool × Bool × Bool where
  toFun Y := (Y 0, Y 1, Y 2, Y 3, Y 4, Y 5)
  invFun b := ![b.1, b.2.1, b.2.2.1, b.2.2.2.1, b.2.2.2.2.1, b.2.2.2.2.2]
  left_inv Y := by funext k; fin_cases k <;> rfl
  right_inv b := rfl

def portOK (a b : Bool) (w : Fin 4 → Bool) : Bool :=
  !(a && w 0) && !(w 0 && w 1) && !(w 1 && w 2) && !(w 2 && b) && !(a && w 3) && !(w 3 && b)

def hubOK (t : Bool) (Y : Fin 6 → Bool) : Bool :=
  !(Y 0 && Y 1) && !(Y 1 && Y 2) && !(Y 1 && Y 3) && !(Y 3 && Y 4) && !(Y 4 && Y 5) &&
  !(Y 2 && t) && !(Y 5 && t)

theorem portFactor (a b : Bool) :
    (∑ w : Fin 4 → Bool, if portOK a b w = true then (1 : ZMod 2) else 0) =
      if b = !a then 1 else 0 := by
  rw [← e4.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases a <;> cases b <;> decide

theorem hubFactor0 (t c : Bool) :
    (∑ Y : Fin 6 → Bool, if hubOK t Y = true ∧ (Y 0 = true → c = true) then (1 : ZMod 2) else 0) =
      if t = true ∧ c = true then 0 else 1 := by
  rw [← e6.symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  cases t <;> cases c <;> decide

theorem hubFactor (t : Bool) (c : Prop) [Decidable c] :
    (∑ Y : Fin 6 → Bool, if hubOK t Y = true ∧ (Y 0 = true → c) then (1 : ZMod 2) else 0) =
      if t = true ∧ c then 0 else 1 := by
  by_cases hc : c
  · have := hubFactor0 t true
    simpa [hc] using this
  · have := hubFactor0 t false
    simpa [hc] using this

/-! ### the half graph -/

abbrev HV (m : ℕ) (K : Type) := Fin m ⊕ (Fin m ⊕ ((Fin m × Fin 4) ⊕ (Unit ⊕ (K × Fin 6))))

instance instDecEqHV {m : ℕ} {K : Type} [DecidableEq K] : DecidableEq (HV m K) :=
  letI : DecidableEq (Fin m ⊕ ((Fin m × Fin 4) ⊕ (Unit ⊕ (K × Fin 6)))) := inferInstance
  inferInstanceAs (DecidableEq (Fin m ⊕ (Fin m ⊕ ((Fin m × Fin 4) ⊕ (Unit ⊕ (K × Fin 6))))))

def hubE (k k' : Fin 6) : Bool :=
  (decide (k = 0) && decide (k' = 1)) || (decide (k = 1) && decide (k' = 2)) ||
  (decide (k = 1) && decide (k' = 3)) || (decide (k = 3) && decide (k' = 4)) ||
  (decide (k = 4) && decide (k' = 5))

section half
variable {K : Type} [DecidableEq K]

def eH {m : ℕ} (S : K → Finset (Fin m)) : HV m K → HV m K → Bool
  | .inl i, .inr (.inr (.inl (i', k))) => decide (i = i') && (decide (k = 0) || decide (k = 3))
  | .inr (.inr (.inl (i, k))), .inr (.inr (.inl (i', k'))) =>
      decide (i = i') && ((decide (k = 0) && decide (k' = 1)) || (decide (k = 1) && decide (k' = 2)))
  | .inr (.inr (.inl (i, k))), .inr (.inl i') => decide (i = i') && (decide (k = 2) || decide (k = 3))
  | .inr (.inr (.inr (.inr (U, k)))), .inr (.inr (.inr (.inr (U', k')))) =>
      decide (U = U') && hubE k k'
  | .inr (.inr (.inr (.inr (_, k)))), .inr (.inr (.inr (.inl _))) => decide (k = 0)
  | .inr (.inr (.inr (.inr (U, k)))), .inl i => decide (k = 0) && !(decide (i ∈ S U))
  | .inr (.inr (.inr (.inr (U, k)))), .inr (.inl i) => decide (k = 0) && decide (i ∈ S U)
  | _, _ => false

def liveH {m : ℕ} (t : K → Bool) : HV m K → Bool
  | .inr (.inr (.inr (.inr (U, k)))) => !(t U && (decide (k = 2) || decide (k = 5)))
  | _ => true

abbrev Rest (m : ℕ) (K : Type) :=
  (Fin m → Bool) × ((Fin m → Fin 4 → Bool) × (Bool × (K → Fin 6 → Bool)))
abbrev Tup (m : ℕ) (K : Type) := (Fin m → Bool) × Rest m K

def toT {m : ℕ} (y : HV m K → Bool) : Tup m K :=
  (fun i => y (.inl i), fun i => y (.inr (.inl i)), fun i k => y (.inr (.inr (.inl (i, k)))),
   y (.inr (.inr (.inr (.inl ())))), fun U k => y (.inr (.inr (.inr (.inr (U, k))))))

def fromT {m : ℕ} (τ : Tup m K) : HV m K → Bool
  | .inl i => τ.1 i
  | .inr (.inl i) => τ.2.1 i
  | .inr (.inr (.inl (i, k))) => τ.2.2.1 i k
  | .inr (.inr (.inr (.inl _))) => τ.2.2.2.1
  | .inr (.inr (.inr (.inr (U, k)))) => τ.2.2.2.2 U k

def tEquiv (m : ℕ) (K : Type) : (HV m K → Bool) ≃ Tup m K where
  toFun := toT
  invFun := fromT
  left_inv y := by funext v; rcases v with i | i | ⟨i, k⟩ | ⟨⟩ | ⟨U, k⟩ <;> rfl
  right_inv τ := rfl

def halfValid {m : ℕ} (S : K → Finset (Fin m)) (t : K → Bool) (y : HV m K → Bool) : Prop :=
  (∀ v, y v = true → liveH t v = true) ∧ ∀ u v, eH S u v = true → ¬(y u = true ∧ y v = true)

def tValid {m : ℕ} (S : K → Finset (Fin m)) (t : K → Bool) (τ : Tup m K) : Prop :=
  (∀ i, portOK (τ.1 i) (τ.2.1 i) (τ.2.2.1 i) = true) ∧ (∀ U, hubOK (t U) (τ.2.2.2.2 U) = true) ∧
  ∀ U, τ.2.2.2.2 U 0 = true → τ.2.2.2.1 = false ∧
    ∀ i, (i ∈ S U → τ.2.1 i = false) ∧ (i ∉ S U → τ.1 i = false)

theorem halfValid_iff {m : ℕ} (S : K → Finset (Fin m)) (t : K → Bool) (y : HV m K → Bool) :
    halfValid S t y ↔ tValid S t (toT y) := by
  constructor
  · rintro ⟨hl, he⟩
    refine ⟨fun i => ?_, fun U => ?_, fun U hU => ⟨?_, fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩⟩
    · have h1 := he (.inl i) (.inr (.inr (.inl (i, 0)))) (by simp [eH])
      have h2 := he (.inr (.inr (.inl (i, 0)))) (.inr (.inr (.inl (i, 1)))) (by simp [eH])
      have h3 := he (.inr (.inr (.inl (i, 1)))) (.inr (.inr (.inl (i, 2)))) (by simp [eH])
      have h4 := he (.inr (.inr (.inl (i, 2)))) (.inr (.inl i)) (by simp [eH])
      have h5 := he (.inl i) (.inr (.inr (.inl (i, 3)))) (by simp [eH])
      have h6 := he (.inr (.inr (.inl (i, 3)))) (.inr (.inl i)) (by simp [eH])
      simp only [toT, portOK]
      revert h1 h2 h3 h4 h5 h6
      generalize y (.inl i) = a
      generalize y (.inr (.inl i)) = b
      generalize y (.inr (.inr (.inl (i, 0)))) = w0
      generalize y (.inr (.inr (.inl (i, 1)))) = w1
      generalize y (.inr (.inr (.inl (i, 2)))) = w2
      generalize y (.inr (.inr (.inl (i, 3)))) = w3
      revert a b w0 w1 w2 w3
      decide
    · have h1 := he (.inr (.inr (.inr (.inr (U, 0))))) (.inr (.inr (.inr (.inr (U, 1))))) (by simp [eH, hubE])
      have h2 := he (.inr (.inr (.inr (.inr (U, 1))))) (.inr (.inr (.inr (.inr (U, 2))))) (by simp [eH, hubE])
      have h3 := he (.inr (.inr (.inr (.inr (U, 1))))) (.inr (.inr (.inr (.inr (U, 3))))) (by simp [eH, hubE])
      have h4 := he (.inr (.inr (.inr (.inr (U, 3))))) (.inr (.inr (.inr (.inr (U, 4))))) (by simp [eH, hubE])
      have h5 := he (.inr (.inr (.inr (.inr (U, 4))))) (.inr (.inr (.inr (.inr (U, 5))))) (by simp [eH, hubE])
      have l2 := hl (.inr (.inr (.inr (.inr (U, 2)))))
      have l5 := hl (.inr (.inr (.inr (.inr (U, 5)))))
      simp only [liveH] at l2 l5
      simp only [toT, hubOK]
      revert h1 h2 h3 h4 h5 l2 l5
      generalize t U = c
      generalize y (.inr (.inr (.inr (.inr (U, 0))))) = y0
      generalize y (.inr (.inr (.inr (.inr (U, 1))))) = y1
      generalize y (.inr (.inr (.inr (.inr (U, 2))))) = y2
      generalize y (.inr (.inr (.inr (.inr (U, 3))))) = y3
      generalize y (.inr (.inr (.inr (.inr (U, 4))))) = y4
      generalize y (.inr (.inr (.inr (.inr (U, 5))))) = y5
      revert c y0 y1 y2 y3 y4 y5
      decide
    · have h := he (.inr (.inr (.inr (.inr (U, 0))))) (.inr (.inr (.inr (.inl ())))) (by simp [eH])
      simp only [toT] at hU ⊢
      simpa [hU] using h
    · have h := he (.inr (.inr (.inr (.inr (U, 0))))) (.inr (.inl i)) (by simp [eH, hi])
      simp only [toT] at hU ⊢
      simpa [hU] using h
    · have h := he (.inr (.inr (.inr (.inr (U, 0))))) (.inl i) (by simp [eH, hi])
      simp only [toT] at hU ⊢
      simpa [hU] using h
  · rintro ⟨hp, hh, hc⟩
    refine ⟨?_, ?_⟩
    · rintro (i | i | ⟨i, k⟩ | ⟨⟩ | ⟨U, k⟩) hv
      · rfl
      · rfl
      · rfl
      · rfl
      · have h := hh U
        simp only [toT, hubOK, Bool.and_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff] at h
        fin_cases k <;> simp_all [liveH]
    · rintro (i | i | ⟨i, k⟩ | ⟨⟩ | ⟨U, k⟩) (i' | i' | ⟨i', k'⟩ | ⟨⟩ | ⟨U', k'⟩) he hxy <;>
        simp [eH] at he
      · obtain ⟨rfl, hk⟩ := he
        have h := hp i
        simp only [toT, portOK] at h
        rcases hk with rfl | rfl <;> simp [hxy.1, hxy.2] at h
      · obtain ⟨rfl, hk⟩ := he
        have h := hp i
        simp only [toT, portOK] at h
        rcases hk with rfl | rfl <;> simp [hxy.1, hxy.2] at h
      · obtain ⟨rfl, hk⟩ := he
        have h := hp i
        simp only [toT, portOK] at h
        rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hxy.1, hxy.2] at h
      · obtain ⟨rfl, hi⟩ := he
        have h := ((hc U (by simpa [toT] using hxy.1)).2 i').2 hi
        simp only [toT] at h
        rw [h] at hxy
        simp at hxy
      · obtain ⟨rfl, hi⟩ := he
        have h := ((hc U (by simpa [toT] using hxy.1)).2 i').1 hi
        simp only [toT] at h
        rw [h] at hxy
        simp at hxy
      · subst he
        have h := (hc U (by simpa [toT] using hxy.1)).1
        simp only [toT] at h
        exact (Bool.eq_false_iff.mp h) hxy.2
      · obtain ⟨rfl, hk⟩ := he
        have h := hh U
        simp only [toT, hubOK] at h
        fin_cases k <;> fin_cases k' <;> simp [hubE] at hk <;> simp_all

end half

/-! ### the full graph and its count -/

section full
variable {K : Type} [DecidableEq K]

abbrev FV (l r : ℕ) (K : Type) := HV l K ⊕ HV r K

def eV {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r)) (cr : Fin l → Fin r → Bool) :
    FV l r K → FV l r K → Bool
  | .inl a, .inl b => eH SL a b
  | .inr a, .inr b => eH SR a b
  | .inl (.inl i), .inr (.inl j) => cr i j
  | _, _ => false

def adjV {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (u v : FV l r K) : Bool :=
  eV SL SR cr u v || eV SL SR cr v u

def liveV {l r : ℕ} (f g : K → Bool) : FV l r K → Bool
  | .inl a => liveH f a
  | .inr a => liveH g a

def validGen {V : Type} (adj : V → V → Bool) (live : V → Bool) (x : V → Bool) : Prop :=
  (∀ v, x v = true → live v = true) ∧ ∀ u v, adj u v = true → x u = true → x v = false

instance {V : Type} [Fintype V] (adj : V → V → Bool) (live : V → Bool) (x : V → Bool) :
    Decidable (validGen adj live x) := by unfold validGen; infer_instance

theorem full_valid_iff {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (f g : K → Bool) (x : FV l r K → Bool) :
    validGen (adjV SL SR cr) (liveV f g) x ↔
      halfValid SL f (fun a => x (.inl a)) ∧ halfValid SR g (fun a => x (.inr a)) ∧
      ∀ i j, cr i j = true → ¬(x (.inl (.inl i)) = true ∧ x (.inr (.inl j)) = true) := by
  have hsym : (∀ u v, adjV SL SR cr u v = true → x u = true → x v = false) ↔
      ∀ u v, eV SL SR cr u v = true → ¬(x u = true ∧ x v = true) := by
    constructor
    · intro h u v he ⟨hu, hv⟩
      have := h u v (by simp [adjV, he]) hu
      rw [this] at hv; exact Bool.false_ne_true hv
    · intro h u v ha hu
      simp only [adjV, Bool.or_eq_true] at ha
      rcases ha with ha | ha
      · cases hv : x v
        · rfl
        · exact absurd ⟨hu, hv⟩ (h u v ha)
      · cases hv : x v
        · rfl
        · exact absurd ⟨hv, hu⟩ (h v u ha)
  unfold validGen halfValid
  rw [hsym]
  constructor
  · rintro ⟨hl, he⟩
    exact ⟨⟨fun v hv => hl (.inl v) hv, fun u v h => he (.inl u) (.inl v) h⟩,
      ⟨fun v hv => hl (.inr v) hv, fun u v h => he (.inr u) (.inr v) h⟩,
      fun i j h => he (.inl (.inl i)) (.inr (.inl j)) h⟩
  · rintro ⟨⟨hl1, he1⟩, ⟨hl2, he2⟩, hc⟩
    refine ⟨?_, ?_⟩
    · rintro (v | v) hv
      · exact hl1 v hv
      · exact hl2 v hv
    · rintro (u | u) (v | v) h
      · exact he1 u v h
      · rcases u with i | u <;> rcases v with j | v
        · exact hc i j h
        · simp [eV] at h
        · simp [eV] at h
        · simp [eV] at h
      · simp [eV] at h
      · exact he2 u v h

def fEquiv (l r : ℕ) (K : Type) : (FV l r K → Bool) ≃ Tup l K × Tup r K :=
  (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr (tEquiv l K) (tEquiv r K))

def crossP {l r : ℕ} (cr : Fin l → Fin r → Bool) (P : Fin l → Bool) (Q : Fin r → Bool) : Prop :=
  ∀ i j, cr i j = true → ¬(P i = true ∧ Q j = true)

instance {l r : ℕ} (cr : Fin l → Fin r → Bool) (P : Fin l → Bool) (Q : Fin r → Bool) :
    Decidable (crossP cr P Q) := by unfold crossP; infer_instance

instance {m : ℕ} [Fintype K] (S : K → Finset (Fin m)) (t : K → Bool) (τ : Tup m K) :
    Decidable (tValid S t τ) := by unfold tValid; infer_instance

theorem valid_tup {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (f g : K → Bool) (τL : Tup l K) (τR : Tup r K) :
    validGen (adjV SL SR cr) (liveV f g) ((fEquiv l r K).symm (τL, τR)) ↔
      tValid SL f τL ∧ tValid SR g τR ∧ crossP cr τL.1 τR.1 := by
  rw [full_valid_iff, halfValid_iff, halfValid_iff]
  exact Iff.rfl

def con {m : ℕ} (S : K → Finset (Fin m)) (P Pb : Fin m → Bool) (U : K) : Prop :=
  ∀ i, (i ∈ S U → Pb i = false) ∧ (i ∉ S U → P i = false)

instance {m : ℕ} (S : K → Finset (Fin m)) (P Pb : Fin m → Bool) (U : K) :
    Decidable (con S P Pb U) := by unfold con; infer_instance

theorem halfCount {m : ℕ} [Fintype K] (S : K → Finset (Fin m)) (t : K → Bool) (P : Fin m → Bool) :
    (∑ ρ : Rest m K, if tValid S t (P, ρ) then (1 : ZMod 2) else 0) =
      if ∃ U, t U = true ∧ ∀ i, P i = decide (i ∈ S U) then 1 else 0 := by
  have hHb : ∀ (Pb : Fin m → Bool) (W : Fin m → Fin 4 → Bool) (z : Bool),
      (∑ Hb : K → Fin 6 → Bool, if tValid S t (P, Pb, W, z, Hb) then (1 : ZMod 2) else 0) =
      (if ∀ i, portOK (P i) (Pb i) (W i) = true then 1 else 0) *
      (if ∃ U, t U = true ∧ (z = false ∧ con S P Pb U) then 0 else 1) := by
    intro Pb W z
    have h1 : ∀ Hb : K → Fin 6 → Bool, (if tValid S t (P, Pb, W, z, Hb) then (1 : ZMod 2) else 0) =
        (if ∀ i, portOK (P i) (Pb i) (W i) = true then 1 else 0) *
        ∏ U, (if hubOK (t U) (Hb U) = true ∧ (Hb U 0 = true → z = false ∧ con S P Pb U)
          then (1 : ZMod 2) else 0) := by
      intro Hb
      rw [Fintype.prod_boole, ite_zero_mul_ite_zero, one_mul]
      apply if_congr _ rfl rfl
      simp only [tValid, con, forall_and]
    rw [Finset.sum_congr rfl (fun Hb _ => h1 Hb), ← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun U (Y : Fin 6 → Bool) =>
      if hubOK (t U) Y = true ∧ (Y 0 = true → z = false ∧ con S P Pb U) then (1 : ZMod 2) else 0)]
    simp only [hubFactor]
    have e2 : ∀ U, (if t U = true ∧ (z = false ∧ con S P Pb U) then (0 : ZMod 2) else 1) =
        if ¬(t U = true ∧ (z = false ∧ con S P Pb U)) then 1 else 0 := by
      intro U; split_ifs <;> simp_all
    simp only [e2]
    rw [Fintype.prod_boole]
    by_cases h : ∃ U, t U = true ∧ (z = false ∧ con S P Pb U)
    · have h' : ¬ ∀ U, ¬(t U = true ∧ (z = false ∧ con S P Pb U)) := fun hh =>
        let ⟨U, hU⟩ := h; hh U hU
      rw [if_pos h, if_neg h']
    · have h' : ∀ U, ¬(t U = true ∧ (z = false ∧ con S P Pb U)) := fun U hU => h ⟨U, hU⟩
      rw [if_neg h, if_pos h']
  have hz : ∀ Pb : Fin m → Bool,
      (∑ z : Bool, if ∃ U, t U = true ∧ (z = false ∧ con S P Pb U) then (0 : ZMod 2) else 1) =
        if ∃ U, t U = true ∧ con S P Pb U then 1 else 0 := by
    intro Pb
    rw [Fintype.sum_bool]
    have e1 : ¬ ∃ U, t U = true ∧ (true = false ∧ con S P Pb U) := by simp
    rw [if_neg e1]
    by_cases h : ∃ U, t U = true ∧ con S P Pb U
    · rw [if_pos (by simpa using h), if_pos h]; decide
    · rw [if_neg (by simpa using h), if_neg h]; decide
  have hW : ∀ Pb : Fin m → Bool,
      (∑ W : Fin m → Fin 4 → Bool, if ∀ i, portOK (P i) (Pb i) (W i) = true then (1 : ZMod 2) else 0) =
        if Pb = (fun i => !P i) then 1 else 0 := by
    intro Pb
    have eW : ∀ W : Fin m → Fin 4 → Bool,
        (if ∀ i, portOK (P i) (Pb i) (W i) = true then (1 : ZMod 2) else 0) =
        ∏ i, (if portOK (P i) (Pb i) (W i) = true then (1 : ZMod 2) else 0) := by
      intro W
      rw [Fintype.prod_boole]
      exact congrArg (fun d => @ite (ZMod 2) (∀ i, portOK (P i) (Pb i) (W i) = true) d 1 0)
        (Subsingleton.elim _ _)
    rw [Finset.sum_congr rfl (fun W _ => eW W)]
    rw [← Fintype.prod_sum (fun i (w : Fin 4 → Bool) =>
      if portOK (P i) (Pb i) w = true then (1 : ZMod 2) else 0)]
    simp only [portFactor]
    rw [Fintype.prod_boole]
    exact ite_iff ⟨fun h => funext h, fun h i => congrFun h i⟩ _ _
  simp only [Fintype.sum_prod_type]
  simp only [hHb]
  simp only [← Finset.mul_sum]
  simp only [hz]
  simp only [← Finset.sum_mul]
  simp only [hW]
  simp only [boole_mul]
  rw [Fintype.sum_ite_eq']
  apply if_congr _ rfl rfl
  apply exists_congr
  intro U
  apply and_congr Iff.rfl
  simp only [con]
  apply forall_congr'
  intro i
  by_cases hi : i ∈ S U <;> cases P i <;> simp [hi]

theorem reindex {m : ℕ} [Fintype K] (S : K → Finset (Fin m))
    (hS : Function.Injective (fun U i => decide (i ∈ S U))) (t : K → Bool)
    (F : (Fin m → Bool) → ZMod 2) :
    (∑ P, (if ∃ U, t U = true ∧ ∀ i, P i = decide (i ∈ S U) then (1 : ZMod 2) else 0) * F P) =
      ∑ U, if t U = true then F (fun i => decide (i ∈ S U)) else 0 := by
  have e : ∀ P : Fin m → Bool, (∃ U, t U = true ∧ ∀ i, P i = decide (i ∈ S U)) ↔
      P ∈ (univ.filter (fun U => t U = true)).image (fun U i => decide (i ∈ S U)) := by
    intro P
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨U, h1, h2⟩; exact ⟨U, h1, (funext h2).symm⟩
    · rintro ⟨U, h1, rfl⟩; exact ⟨U, h1, fun i => rfl⟩
  have e' : ∀ P : Fin m → Bool,
      (if ∃ U, t U = true ∧ ∀ i, P i = decide (i ∈ S U) then (1 : ZMod 2) else 0) * F P =
      if P ∈ (univ.filter (fun U => t U = true)).image (fun U i => decide (i ∈ S U)) then F P else 0 := by
    intro P; rw [boole_mul]; exact if_congr (e P) rfl rfl
  rw [Finset.sum_congr rfl (fun P _ => e' P), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_image (fun x _ y _ h => hS h), Finset.sum_filter]

theorem split_sum {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (a : A × B → ZMod 2) (b : C × D → ZMod 2) (c : A → C → ZMod 2) :
    (∑ x : A × B, ∑ y : C × D, c x.1 y.1 * (a x * b y)) =
      ∑ p, ∑ q, c p q * ((∑ u, a (p, u)) * (∑ v, b (q, v))) := by
  simp only [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_comm]

theorem count_formula {l r : ℕ} [Fintype K] (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool)
    (hL : Function.Injective (fun U i => decide (i ∈ SL U)))
    (hR : Function.Injective (fun U j => decide (j ∈ SR U)))
    (f g : K → Bool) :
    (∑ x : FV l r K → Bool, if validGen (adjV SL SR cr) (liveV f g) x then (1 : ZMod 2) else 0) =
    ∑ U, ∑ V, if f U = true ∧ g V = true ∧ (∀ i j, cr i j = true → ¬(i ∈ SL U ∧ j ∈ SR V))
      then 1 else 0 := by
  rw [← (fEquiv l r K).symm.sum_comp, Fintype.sum_prod_type]
  simp only [valid_tup]
  have step : ∀ (τL : Tup l K) (τR : Tup r K),
      (if tValid SL f τL ∧ tValid SR g τR ∧ crossP cr τL.1 τR.1 then (1 : ZMod 2) else 0) =
      (fun P Q => if crossP cr P Q then (1 : ZMod 2) else 0) τL.1 τR.1 *
        ((fun τ => if tValid SL f τ then (1 : ZMod 2) else 0) τL *
         (fun τ => if tValid SR g τ then (1 : ZMod 2) else 0) τR) := by
    intro τL τR
    simp only
    rw [ite_zero_mul_ite_zero, ite_zero_mul_ite_zero]; simp only [mul_one]
    exact if_congr (by tauto) rfl rfl
  simp only [step]
  rw [split_sum (fun τ => if tValid SL f τ then (1 : ZMod 2) else 0)
    (fun τ => if tValid SR g τ then (1 : ZMod 2) else 0)
    (fun P Q => if crossP cr P Q then (1 : ZMod 2) else 0)]
  simp only [halfCount]
  have step2 : ∀ (P : Fin l → Bool) (Q : Fin r → Bool),
      (if crossP cr P Q then (1 : ZMod 2) else 0) *
        ((if ∃ U, f U = true ∧ ∀ i, P i = decide (i ∈ SL U) then (1 : ZMod 2) else 0) *
         (if ∃ U, g U = true ∧ ∀ j, Q j = decide (j ∈ SR U) then (1 : ZMod 2) else 0)) =
      (if ∃ U, f U = true ∧ ∀ i, P i = decide (i ∈ SL U) then (1 : ZMod 2) else 0) *
        ((if ∃ U, g U = true ∧ ∀ j, Q j = decide (j ∈ SR U) then (1 : ZMod 2) else 0) *
          (if crossP cr P Q then (1 : ZMod 2) else 0)) := by
    intro P Q; ring
  simp only [step2]
  simp only [← Finset.mul_sum]
  rw [reindex SL hL f]
  simp only [reindex SR hR g]
  apply Finset.sum_congr rfl
  intro U _
  by_cases hf : f U = true
  · rw [if_pos hf]
    apply Finset.sum_congr rfl
    intro V _
    by_cases hg : g V = true
    · rw [if_pos hg]
      apply if_congr _ rfl rfl
      simp [crossP, hf, hg]
    · rw [if_neg hg, if_neg (by tauto)]
  · rw [if_neg hf]
    symm
    apply Finset.sum_eq_zero
    intro V _
    rw [if_neg (by tauto)]

end full


/-! ### rectangle bound -/

def sg (b : Bool) : ℤ := if b then -1 else 1

theorem sg_mul_sg (x y : Bool) : sg x * sg y = if x = y then 1 else -1 := by
  cases x <;> cases y <;> simp [sg]

theorem sg_mul_le_abs (x : Bool) (a : ℤ) : sg x * a ≤ |a| := by
  cases x
  · simp [sg, le_abs_self]
  · simp [sg, neg_le_abs]

theorem rect_bound {T : Type} {fT : Fintype T} (res res' : T → T → Bool)
    (hres : ∀ f g, res' f g = res f g) (D : ℕ) (hD : Fintype.card T = D) {dT : DecidableEq T}
    (horth : ∀ f f', ∑ g, sg (res f g) * sg (res f' g) = if f = f' then (D : ℤ) else 0)
    (K : ℕ) (rows cols : Fin K → Finset T) (guess : Fin K → T → Bool)
    (hpart : ∀ f g : T, ∃! i, f ∈ rows i ∧ g ∈ cols i)
    {inst : DecidablePred (fun a : T × T =>
      ∃ i, a.1 ∈ rows i ∧ a.2 ∈ cols i ∧ guess i a.2 = res' a.1 a.2)} :
    (2 * (@Finset.filter _ (fun a : T × T =>
      ∃ i, a.1 ∈ rows i ∧ a.2 ∈ cols i ∧ guess i a.2 = res' a.1 a.2) inst univ).card
        - D ^ 2) ^ 2 ≤ K * D ^ 3 := by
  classical
  choose idx hidx huniq using hpart
  set c := (@Finset.filter _ (fun a : T × T =>
      ∃ i, a.1 ∈ rows i ∧ a.2 ∈ cols i ∧ guess i a.2 = res' a.1 a.2) inst univ).card with hc
  have hmem : ∀ (i : Fin K) (a : T × T), a ∈ rows i ×ˢ cols i ↔ idx a.1 a.2 = i := by
    intro i a
    rw [Finset.mem_product]
    constructor
    · intro h; exact (huniq a.1 a.2 i h).symm
    · rintro rfl; exact hidx a.1 a.2
  have hpred : ∀ a : T × T, (∃ i, a.1 ∈ rows i ∧ a.2 ∈ cols i ∧ guess i a.2 = res' a.1 a.2) ↔
      guess (idx a.1 a.2) a.2 = res a.1 a.2 := by
    intro a
    constructor
    · rintro ⟨i, h1, h2, h3⟩
      have := huniq a.1 a.2 i ⟨h1, h2⟩
      rw [← this, ← hres]; exact h3
    · intro h
      exact ⟨idx a.1 a.2, (hidx a.1 a.2).1, (hidx a.1 a.2).2, by rw [hres]; exact h⟩
  have hcard : (c : ℤ) = ∑ a : T × T, if guess (idx a.1 a.2) a.2 = res a.1 a.2 then (1 : ℤ) else 0 := by
    rw [hc, Finset.natCast_card_filter]
    apply Finset.sum_congr rfl
    intro a _
    exact if_congr (hpred a) rfl rfl
  set S : Fin K → T → ℤ := fun i g => ∑ f ∈ rows i, sg (res f g) with hS
  have hX : (2 * (c : ℤ) - (D : ℤ) ^ 2) = ∑ i, ∑ g ∈ cols i, sg (guess i g) * S i g := by
    have h1 : (2 * (c : ℤ) - (D : ℤ) ^ 2) =
        ∑ a : T × T, sg (guess (idx a.1 a.2) a.2) * sg (res a.1 a.2) := by
      have e1 : ∀ a : T × T, sg (guess (idx a.1 a.2) a.2) * sg (res a.1 a.2) =
          2 * (if guess (idx a.1 a.2) a.2 = res a.1 a.2 then (1 : ℤ) else 0) - 1 := by
        intro a
        rw [sg_mul_sg]
        split_ifs <;> norm_num
      rw [Finset.sum_congr rfl (fun a _ => e1 a), Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← hcard]
      simp [Fintype.card_prod, hD, sq]
    rw [h1, ← Finset.sum_fiberwise (univ : Finset (T × T)) (fun a => idx a.1 a.2)]
    apply Finset.sum_congr rfl
    intro i _
    have hset : (univ.filter (fun a : T × T => idx a.1 a.2 = i)) = rows i ×ˢ cols i := by
      ext a; simp [hmem]
    rw [hset, Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro g hg
    rw [hS, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f hf
    have : idx f g = i := (hmem i (f, g)).mp (Finset.mem_product.mpr ⟨hf, hg⟩)
    rw [this]
  set Y : Fin K → ℤ := fun i => ∑ g ∈ cols i, |S i g| with hY
  have hle : (2 * (c : ℤ) - (D : ℤ) ^ 2) ≤ ∑ i, Y i := by
    rw [hX]
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro g _
    exact sg_mul_le_abs _ _
  have hY0 : 0 ≤ ∑ i, Y i :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun g _ => abs_nonneg _))
  have hSq : ∀ i, ∑ g, (S i g) ^ 2 = (D : ℤ) * (rows i).card := by
    intro i
    have h1 : ∀ g, (S i g) ^ 2 = ∑ f ∈ rows i, ∑ f' ∈ rows i, sg (res f g) * sg (res f' g) := by
      intro g; rw [hS, sq, Finset.sum_mul_sum]
    calc ∑ g, (S i g) ^ 2
        = ∑ g, ∑ f ∈ rows i, ∑ f' ∈ rows i, sg (res f g) * sg (res f' g) :=
          Finset.sum_congr rfl (fun g _ => h1 g)
      _ = ∑ f ∈ rows i, ∑ g, ∑ f' ∈ rows i, sg (res f g) * sg (res f' g) := Finset.sum_comm
      _ = ∑ f ∈ rows i, ∑ f' ∈ rows i, ∑ g, sg (res f g) * sg (res f' g) :=
          Finset.sum_congr rfl (fun f _ => Finset.sum_comm)
      _ = ∑ f ∈ rows i, ∑ f' ∈ rows i, (if f = f' then (D : ℤ) else 0) := by
          simp only [horth]
      _ = ∑ f ∈ rows i, (D : ℤ) :=
          Finset.sum_congr rfl (fun f hf => by rw [Finset.sum_ite_eq]; simp [hf])
      _ = (D : ℤ) * (rows i).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hYi : ∀ i, (Y i) ^ 2 ≤ ((cols i).card : ℤ) * ((D : ℤ) * (rows i).card) := by
    intro i
    calc (Y i) ^ 2 = (∑ g ∈ cols i, |S i g|) ^ 2 := rfl
      _ ≤ ((cols i).card : ℤ) * ∑ g ∈ cols i, |S i g| ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ ((cols i).card : ℤ) * ∑ g, (S i g) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          simp only [sq_abs]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun g _ _ => sq_nonneg _)
      _ = _ := by rw [hSq]
  have hRC : ∑ i, ((rows i).card : ℤ) * (cols i).card = (D : ℤ) ^ 2 := by
    have h := Finset.card_eq_sum_card_fiberwise (f := fun a : T × T => idx a.1 a.2)
      (s := univ) (t := univ) (fun _ _ => mem_univ _)
    have e : ∀ i, (univ.filter (fun a : T × T => idx a.1 a.2 = i)).card =
        (rows i).card * (cols i).card := by
      intro i; rw [← Finset.card_product]; congr 1; ext a; simp [hmem]
    simp only [e] at h
    rw [Finset.card_univ, Fintype.card_prod, hD] at h
    have h' : ((D * D : ℕ) : ℤ) = ((∑ i, (rows i).card * (cols i).card : ℕ) : ℤ) := by rw [h]
    push_cast at h'
    rw [← h']; ring
  have hfin : (∑ i, Y i) ^ 2 ≤ (K : ℤ) * (D : ℤ) ^ 3 := by
    calc (∑ i, Y i) ^ 2 ≤ (K : ℤ) * ∑ i, (Y i) ^ 2 := by
          have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin K))) (f := Y)
          simpa using this
      _ ≤ (K : ℤ) * ∑ i, ((cols i).card : ℤ) * ((D : ℤ) * (rows i).card) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum (fun i _ => hYi i)
      _ = (K : ℤ) * ((D : ℤ) * ∑ i, ((rows i).card : ℤ) * (cols i).card) := by
          congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = (K : ℤ) * (D : ℤ) ^ 3 := by rw [hRC]; ring
  by_cases h : 2 * c ≤ D ^ 2
  · rw [Nat.sub_eq_zero_of_le h]; simp
  · push_neg at h
    have hcast : ((2 * c - D ^ 2 : ℕ) : ℤ) = 2 * (c : ℤ) - (D : ℤ) ^ 2 := by
      rw [Nat.cast_sub h.le]; push_cast; ring
    have hX0 : 0 ≤ 2 * (c : ℤ) - (D : ℤ) ^ 2 := by rw [← hcast]; positivity
    have h2 : (2 * (c : ℤ) - (D : ℤ) ^ 2) ^ 2 ≤ (K : ℤ) * (D : ℤ) ^ 3 := by
      have : (2 * (c : ℤ) - (D : ℤ) ^ 2) ^ 2 ≤ (∑ i, Y i) ^ 2 := by nlinarith
      exact le_trans this hfin
    have key : ((2 * c - D ^ 2 : ℕ) : ℤ) ^ 2 ≤ (K : ℤ) * (D : ℤ) ^ 3 := by rw [hcast]; exact h2
    exact_mod_cast key

/-! ### orthogonality of the containment sign matrix -/

theorem neg_one_pow_card_filter {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] :
    ((-1 : ℤ)) ^ (univ.filter P).card = ∏ a, if P a then (-1 : ℤ) else 1 := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

theorem orth {K : Type} {fK : Fintype K} {dK : DecidableEq K} {dT : DecidableEq (K → Bool)}
    (le : K → K → Prop)
    [DecidableRel le] (rk : K → ℕ) (hrefl : ∀ U, le U U)
    (hrk : ∀ U V, le U V → U ≠ V → rk U < rk V) (res : (K → Bool) → (K → Bool) → Bool)
    (hres : ∀ f g, res f g = decide ((univ.filter (fun pr : K × K =>
      f pr.1 = true ∧ g pr.2 = true ∧ le pr.1 pr.2)).card % 2 = 1))
    (f f' : K → Bool) :
    ∑ g, sg (res f g) * sg (res f' g) = if f = f' then ((2 ^ Fintype.card K : ℕ) : ℤ) else 0 := by
  have hsg : ∀ n : ℕ, sg (decide (n % 2 = 1)) = (-1) ^ n := by
    intro n
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_one_pow]; have : n % 2 = 0 := Nat.even_iff.mp h; simp [sg, this]
    · rw [h.neg_one_pow]; have : n % 2 = 1 := Nat.odd_iff.mp h; simp [sg, this]
  have hone : ∀ (h g : K → Bool), sg (res h g) =
      ∏ V, ∏ U, (if h U = true ∧ g V = true ∧ le U V then (-1 : ℤ) else 1) := by
    intro h g
    rw [hres, hsg, neg_one_pow_card_filter, Fintype.prod_prod_type, Finset.prod_comm]
  have hprod : ∀ g : K → Bool, sg (res f g) * sg (res f' g) =
      ∏ V, ∏ U, ((if f U = true ∧ g V = true ∧ le U V then (-1 : ℤ) else 1) *
        (if f' U = true ∧ g V = true ∧ le U V then (-1 : ℤ) else 1)) := by
    intro g
    rw [hone, hone, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro V _
    rw [← Finset.prod_mul_distrib]
  let φ : K → Bool → ℤ := fun V b => ∏ U, ((if f U = true ∧ b = true ∧ le U V then (-1 : ℤ) else 1) *
        (if f' U = true ∧ b = true ∧ le U V then (-1 : ℤ) else 1))
  let ψ : K → ℤ := fun V => ∏ U, ((if f U = true ∧ le U V then (-1 : ℤ) else 1) *
        (if f' U = true ∧ le U V then (-1 : ℤ) else 1))
  have hφ : ∀ V, ∑ b, φ V b = ψ V + 1 := by
    intro V
    rw [Fintype.sum_bool]
    congr 1
    · apply Finset.prod_congr rfl; intro U _; simp
    · apply Finset.prod_eq_one; intro U _; simp
  calc ∑ g, sg (res f g) * sg (res f' g) = ∑ g : K → Bool, ∏ V, φ V (g V) :=
        Finset.sum_congr rfl (fun g _ => hprod g)
    _ = ∏ V, ∑ b, φ V b := (Fintype.prod_sum φ).symm
    _ = ∏ V, (ψ V + 1) := Finset.prod_congr rfl (fun V _ => hφ V)
    _ = if f = f' then ((2 ^ Fintype.card K : ℕ) : ℤ) else 0 := by
      split_ifs with hff
      · subst hff
        have htrue : ∀ V, ψ V = 1 := by
          intro V; apply Finset.prod_eq_one; intro U _; split_ifs <;> norm_num
        simp only [htrue]
        rw [Finset.prod_const, Finset.card_univ]; push_cast; norm_num
      · obtain ⟨U0, hU0, hmin⟩ := Finset.exists_min_image (univ.filter (fun U => f U ≠ f' U)) rk (by
          by_contra hne
          apply hff; funext U; by_contra hU
          exact hne ⟨U, by simp [hU]⟩)
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU0 hmin
        apply Finset.prod_eq_zero (Finset.mem_univ U0)
        have : ψ U0 = -1 := by
          show (∏ U, ((if f U = true ∧ le U U0 then (-1 : ℤ) else 1) *
            (if f' U = true ∧ le U U0 then (-1 : ℤ) else 1))) = -1
          rw [Finset.prod_eq_single U0]
          · simp only [hrefl, and_true]
            cases h1 : f U0 <;> cases h2 : f' U0 <;> simp_all
          · intro U _ hU
            by_cases hle : le U U0
            · have hlt := hrk U U0 hle hU
              have heq : f U = f' U := by
                by_contra hne; exact absurd (hmin U hne) (not_le.mpr hlt)
              rw [heq]; split_ifs <;> norm_num
            · simp [hle]
          · intro h; exact absurd (Finset.mem_univ U0) h
        rw [this]; norm_num

/-! ### transport between `Fin N` and a labelled vertex type -/

theorem transport {N : ℕ} {V : Type} [Fintype V] [DecidableEq V] (e : V ≃ Fin N)
    (adj : V → V → Bool) (live : V → Bool) (G : Fin N → Finset (Fin N)) (liveF : Fin N → Bool)
    (hG : ∀ a b, e b ∈ G (e a) ↔ adj a b = true) (hl : ∀ a, liveF (e a) = live a)
    {inst : DecidablePred (fun I : Finset (Fin N) =>
      (∀ v ∈ I, liveF v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)} :
    (@Finset.filter _ (fun I : Finset (Fin N) =>
      (∀ v ∈ I, liveF v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I) inst univ).card =
    (univ.filter (fun x : V → Bool => validGen adj live x)).card := by
  apply Finset.card_nbij' (fun I a => decide (e a ∈ I)) (fun x => univ.filter (fun u => x (e.symm u) = true))
  · intro I hI
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hI ⊢
    obtain ⟨hl1, hi1⟩ := hI
    refine ⟨fun a ha => ?_, fun a b hab ha => ?_⟩
    · rw [← hl]; exact hl1 _ (by simpa using ha)
    · have hb : e b ∈ G (e a) := (hG a b).mpr hab
      have := hi1 (e a) (by simpa using ha) (e b) hb
      simpa using this
  · intro x hx
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx ⊢
    obtain ⟨hl1, hi1⟩ := hx
    refine ⟨fun v hv => ?_, fun u hu v hv hv' => ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have := hl1 _ hv
      rw [← hl, Equiv.apply_symm_apply] at this; exact this
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hv'
      have h1 : adj (e.symm u) (e.symm v) = true := by
        rw [← hG]; simpa using hv
      have := hi1 _ _ h1 hu
      rw [this] at hv'; exact Bool.false_ne_true hv'
  · intro I _
    ext u; simp
  · intro x _
    funext a; simp


/-! ### properties of the labelled graph -/

section props
variable {K : Type} [DecidableEq K]

def sideV {l r : ℕ} : FV l r K → Bool
  | .inl _ => false
  | .inr _ => true

def shoreH {m : ℕ} : HV m K → Bool
  | .inl _ => false
  | .inr (.inl _) => false
  | .inr (.inr (.inl (_, k))) => decide (k ≠ 1)
  | .inr (.inr (.inr (.inl _))) => false
  | .inr (.inr (.inr (.inr (_, k)))) => decide (k = 0 ∨ k = 2 ∨ k = 3 ∨ k = 5)

def shoreV {l r : ℕ} : FV l r K → Bool
  | .inl a => shoreH a
  | .inr a => !shoreH a

def tagH {m : ℕ} : HV m K → Option K
  | .inr (.inr (.inr (.inr (U, k)))) => if k = 2 ∨ k = 5 then some U else none
  | _ => none

def tagV {l r : ℕ} : FV l r K → Option K
  | .inl a => tagH a
  | .inr a => tagH a

theorem eH_irrefl {m : ℕ} (S : K → Finset (Fin m)) (a : HV m K) : eH S a a = false := by
  rcases a with i | i | ⟨i, k⟩ | u | ⟨U, k⟩ <;> simp [eH] <;> revert k <;> decide

theorem adjV_irrefl {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (a : FV l r K) : adjV SL SR cr a a = false := by
  rcases a with a | a <;> simp [adjV, eV, eH_irrefl]

theorem adjV_symm {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (a b : FV l r K) : adjV SL SR cr a b = adjV SL SR cr b a := by
  simp only [adjV, Bool.or_comm]

theorem adjV_cross {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (a : HV l K) (b : HV r K) :
    adjV SL SR cr (.inl a) (.inr b) = true ↔ ∃ i j, a = .inl i ∧ b = .inl j ∧ cr i j = true := by
  rcases a with i | a <;> rcases b with j | b <;> simp [adjV, eV]

theorem eH_shore {m : ℕ} (S : K → Finset (Fin m)) (a b : HV m K) (h : eH S a b = true) :
    shoreH a ≠ shoreH b := by
  rcases a with i | i | ⟨i, k⟩ | u | ⟨U, k⟩ <;> rcases b with i' | i' | ⟨i', k'⟩ | u' | ⟨U', k'⟩ <;>
    simp [eH] at h
  all_goals first
    | (rcases h with ⟨-, rfl | rfl⟩ <;> simp [shoreH])
    | (rcases h with ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ <;> simp [shoreH])
    | (obtain ⟨-, hk⟩ := h; fin_cases k <;> fin_cases k' <;> simp [hubE] at hk <;> simp [shoreH])
    | (obtain ⟨rfl, -⟩ := h; simp [shoreH])
    | (subst h; simp [shoreH])

theorem adjV_shore {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (a b : FV l r K) (h : adjV SL SR cr a b = true) :
    shoreV a ≠ shoreV b := by
  have key : ∀ a b, eV SL SR cr a b = true → shoreV a ≠ shoreV b := by
    rintro (a | a) (b | b) h
    · exact eH_shore SL a b h
    · rcases a with i | a <;> rcases b with j | b <;> simp [eV] at h
      simp [shoreV, shoreH]
    · simp [eV] at h
    · intro hs
      apply eH_shore SR a b h
      simpa [shoreV] using hs
  simp only [adjV, Bool.or_eq_true] at h
  rcases h with h | h
  · exact key a b h
  · exact (key b a h).symm

theorem eH_tag {m : ℕ} (S : K → Finset (Fin m)) (U : K) (k : Fin 6) (hk : k = 2 ∨ k = 5)
    (b : HV m K) :
    (eH S (.inr (.inr (.inr (.inr (U, k))))) b || eH S b (.inr (.inr (.inr (.inr (U, k)))))) = true ↔
    b = .inr (.inr (.inr (.inr (U, if k = 2 then 1 else 4)))) := by
  rcases hk with rfl | rfl <;> rcases b with i' | i' | ⟨i', k'⟩ | u' | ⟨U', k'⟩ <;>
    simp [eH, hubE] <;> fin_cases k' <;> simp [eq_comm]

theorem tag_nbr {l r : ℕ} (SL : K → Finset (Fin l)) (SR : K → Finset (Fin r))
    (cr : Fin l → Fin r → Bool) (a : FV l r K) (h : (tagV a).isSome = true) :
    ∃ c, ∀ b, adjV SL SR cr a b = true ↔ b = c := by
  rcases a with a | a
  · rcases a with i | i | ⟨i, k⟩ | u | ⟨U, k⟩ <;> simp [tagV, tagH] at h
    refine ⟨.inl (.inr (.inr (.inr (.inr (U, if k = 2 then 1 else 4))))), ?_⟩
    rintro (b | b)
    · simp only [Sum.inl.injEq]
      exact eH_tag SL U k h b
    · simp [adjV, eV]
  · rcases a with i | i | ⟨i, k⟩ | u | ⟨U, k⟩ <;> simp [tagV, tagH] at h
    refine ⟨.inr (.inr (.inr (.inr (.inr (U, if k = 2 then 1 else 4))))), ?_⟩
    rintro (b | b)
    · simp [adjV, eV]
    · simp only [Sum.inr.injEq]
      exact eH_tag SR U k h b

theorem live_tag {l r : ℕ} (f g : K → Bool) (a : FV l r K) {d : Decidable (sideV a = true)} :
    (tagV a).elim true (fun U => !((@ite _ (sideV a = true) d g f) U)) = liveV f g a := by
  rcases a with a | a <;> rcases a with i | i | ⟨i, k⟩ | u | ⟨U, k⟩ <;>
    simp [tagV, tagH, liveV, liveH, sideV] <;> fin_cases k <;> simp

theorem card_FV (l r : ℕ) (K : Type) [Fintype K] [DecidableEq K] :
    Fintype.card (FV l r K) = 6 * l + 6 * r + 12 * Fintype.card K + 2 := by
  simp only [FV, HV, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  ring

end props

/-! ### the protocol (any fitting graph) -/

theorem part1_core {N l r : ℕ} (C : Fin l → Finset (Fin r)) (G : Fin N → Finset (Fin N))
    (side : Fin N → Bool) (p : Fin l → Fin N) (s : Fin r → Fin N)
    (hp : ∀ i, side (p i) = false) (hs : ∀ j, side (s j) = true)
    (hsym : ∀ u v, v ∈ G u ↔ u ∈ G v)
    (hcross : ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i))
    {Key : Type} [Fintype Key] [DecidableEq Key] (κ : Finset (Fin l) → Key)
    (avoid : Key → Finset (Fin N) → Prop)
    (havoid : ∀ T B, avoid (κ T) B ↔ ∀ i ∈ T, ∀ j ∈ C i, s j ∉ B) :
    ∃ (send : (Fin N → Bool) → Key → Bool) (recv : (Key → Bool) → (Fin N → Bool) → Bool),
      ∀ a b, recv (send a) b = decide ((univ.filter (fun I : Finset (Fin N) =>
        (∀ v ∈ I, (if side v = true then b v else a v) = true) ∧
          ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card % 2 = 1) := by
  classical
  let TA : Finset (Fin N) → Finset (Fin l) := fun A => univ.filter (fun i => p i ∈ A)
  let vL : (Fin N → Bool) → Finset (Fin N) → Prop := fun a A =>
    (∀ v ∈ A, side v = false) ∧ (∀ v ∈ A, a v = true) ∧ ∀ u ∈ A, ∀ v ∈ G u, v ∉ A
  let vR : (Fin N → Bool) → Finset (Fin N) → Prop := fun b B =>
    (∀ v ∈ B, side v = true) ∧ (∀ v ∈ B, b v = true) ∧ ∀ u ∈ B, ∀ v ∈ G u, v ∉ B
  let nL : (Fin N → Bool) → Key → ℕ := fun a U =>
    (univ.filter (fun A => vL a A ∧ κ (TA A) = U)).card
  let nR : (Fin N → Bool) → Key → ℕ := fun b U =>
    (univ.filter (fun B => vR b B ∧ avoid U B)).card
  refine ⟨fun a U => decide (nL a U % 2 = 1),
    fun h b => decide ((∑ U, if h U = true then nR b U else 0) % 2 = 1), fun a b => ?_⟩
  have hvalid : ∀ A B, (∀ v ∈ A, side v = false) → (∀ v ∈ B, side v = true) →
      (((∀ v ∈ A ∪ B, (if side v = true then b v else a v) = true) ∧
          ∀ u ∈ A ∪ B, ∀ v ∈ G u, v ∉ A ∪ B) ↔
        vL a A ∧ vR b B ∧ avoid (κ (TA A)) B) := by
    intro A B sA sB
    have cross : ∀ u ∈ A, ∀ v ∈ B, v ∈ G u → ¬ avoid (κ (TA A)) B := by
      intro u hu v hv hG hav
      obtain ⟨i, j, rfl, rfl, hj⟩ := (hcross u v (sA u hu) (sB v hv)).mp hG
      exact (havoid _ _).mp hav i (by simp [TA, hu]) j hj hv
    constructor
    · rintro ⟨hl, hi⟩
      refine ⟨⟨sA, fun v hv => ?_, fun u hu v hvG hv => ?_⟩,
        ⟨sB, fun v hv => ?_, fun u hu v hvG hv => ?_⟩, ?_⟩
      · have := hl v (Finset.mem_union_left _ hv); simpa [sA v hv] using this
      · exact hi u (Finset.mem_union_left _ hu) v hvG (Finset.mem_union_left _ hv)
      · have := hl v (Finset.mem_union_right _ hv); simpa [sB v hv] using this
      · exact hi u (Finset.mem_union_right _ hu) v hvG (Finset.mem_union_right _ hv)
      · rw [havoid]
        intro i hi' j hj hsj
        have hpA : p i ∈ A := by simpa [TA] using hi'
        have hG : s j ∈ G (p i) := (hcross (p i) (s j) (hp i) (hs j)).mpr ⟨i, j, rfl, rfl, hj⟩
        exact hi (p i) (Finset.mem_union_left _ hpA) (s j) hG (Finset.mem_union_right _ hsj)
    · rintro ⟨⟨-, hla, hia⟩, ⟨-, hlb, hib⟩, hav⟩
      refine ⟨fun v hv => ?_, fun u hu v hvG hv => ?_⟩
      · rcases Finset.mem_union.mp hv with hv | hv
        · simp [sA v hv, hla v hv]
        · simp [sB v hv, hlb v hv]
      · rcases Finset.mem_union.mp hu with hu | hu <;> rcases Finset.mem_union.mp hv with hv | hv
        · exact hia u hu v hvG hv
        · exact cross u hu v hv hvG hav
        · exact cross v hv u hu ((hsym u v).mp hvG) hav
        · exact hib u hu v hvG hv
  have hsplit : ∀ I : Finset (Fin N),
      I = I.filter (fun v => side v = false) ∪ I.filter (fun v => side v = true) := by
    intro I; ext v; simp only [Finset.mem_union, Finset.mem_filter]; cases side v <;> simp
  have hdec : (univ.filter (fun I : Finset (Fin N) =>
      (∀ v ∈ I, (if side v = true then b v else a v) = true) ∧
        ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card = ∑ U, nL a U * nR b U := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I => I.filter (fun v => side v = false))
      (t := univ.filter (fun A => vL a A))]
    · have hfib : ∀ A ∈ univ.filter (fun A => vL a A),
          ((univ.filter (fun I : Finset (Fin N) =>
            (∀ v ∈ I, (if side v = true then b v else a v) = true) ∧
              ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).filter
            (fun I => I.filter (fun v => side v = false) = A)).card = nR b (κ (TA A)) := by
        intro A hA
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
        apply Finset.card_nbij' (fun I => I.filter (fun v => side v = true)) (fun B => A ∪ B)
        · intro I hI
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hI ⊢
          obtain ⟨hv, hIA⟩ := hI
          rw [hsplit I, hIA] at hv
          have := (hvalid A (I.filter (fun v => side v = true)) hA.1
            (fun v hv => (Finset.mem_filter.mp hv).2)).mp hv
          exact ⟨this.2.1, this.2.2⟩
        · intro B hB
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hB ⊢
          refine ⟨(hvalid A B hA.1 hB.1.1).mpr ⟨hA, hB.1, hB.2⟩, ?_⟩
          ext v; simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hv | hv, hs'⟩
            · exact hv
            · rw [hB.1.1 v hv] at hs'; exact absurd hs' (by simp)
          · intro hv; exact ⟨Or.inl hv, hA.1 v hv⟩
        · intro I hI
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hI
          rw [← hI.2]
          exact (hsplit I).symm
        · intro B hB
          simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hB
          ext v; simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hv | hv, hs'⟩
            · rw [hA.1 v hv] at hs'; exact absurd hs' (by simp)
            · exact hv
          · intro hv; exact ⟨Or.inr hv, hB.1.1 v hv⟩
      rw [Finset.sum_congr rfl hfib]
      rw [← Finset.sum_fiberwise (univ.filter (fun A => vL a A)) (fun A => κ (TA A))]
      apply Finset.sum_congr rfl
      intro U _
      rw [Finset.sum_congr rfl (fun A hA => by rw [(Finset.mem_filter.mp hA).2])]
      rw [Finset.sum_const, smul_eq_mul, Finset.filter_filter]
    · intro I hI
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hI ⊢
      rw [hsplit I] at hI
      exact ((hvalid _ _ (fun v hv => (Finset.mem_filter.mp hv).2)
        (fun v hv => (Finset.mem_filter.mp hv).2)).mp hI).1
  rw [hdec]
  apply decide_eq_decide.mpr
  have hmod : (∑ U, nL a U * nR b U) % 2 =
      (∑ U, if decide (nL a U % 2 = 1) = true then nR b U else 0) % 2 := by
    rw [Finset.sum_nat_mod, Finset.sum_nat_mod (s := univ)
      (f := fun U => if decide (nL a U % 2 = 1) = true then nR b U else 0)]
    congr 1
    apply Finset.sum_congr rfl
    intro U _
    rcases Nat.mod_two_eq_zero_or_one (nL a U) with h | h
    · rw [Nat.mul_mod, h]; simp [h]
    · rw [Nat.mul_mod, h]; simp [h]
  rw [hmod]

/-! ### the concrete instance -/

def SLf {l r : ℕ} (C : Fin l → Finset (Fin r)) (unions : Finset (Finset (Fin r))) :
    ↥unions → Finset (Fin l) := fun U => univ.filter (fun i => C i ⊆ U.val)

def SRf {r : ℕ} (unions : Finset (Finset (Fin r))) : ↥unions → Finset (Fin r) :=
  fun U => univ.filter (fun j => j ∉ U.val)

def crf {l r : ℕ} (C : Fin l → Finset (Fin r)) : Fin l → Fin r → Bool :=
  fun i j => decide (j ∈ C i)

theorem part1_main : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ (l r : Nat) (C : Fin l → Finset (Fin r)) (unions : Finset (Finset (Fin r))),
  (∀ S : Finset (Fin l), ∃ U ∈ unions, ∀ j, j ∈ U ↔ ∃ i ∈ S, j ∈ C i) →
  let Key := ↥unions
  let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N) =>
    Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
    (∀ j, side (s j) = true) ∧ (∀ u, u ∉ G u) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
    ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
  let odd := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
    decide (((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card % 2 = 1)
  (∀ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N), fits N G side p s →
    ∃ (send : (Fin N → Bool) → Key → Bool) (recv : (Key → Bool) → (Fin N → Bool) → Bool),
      ∀ a b, recv (send a) b = odd N G (fun v => if side v then b v else a v)) := by
  intro l r C unions hun2 Key fits odd N G side p s hfits
  obtain ⟨-, -, hp, hs, -, hsym, hcross⟩ := hfits
  choose κv hκmem hκ using hun2
  obtain ⟨send, recv, h⟩ := part1_core C G side p s hp hs hsym hcross
    (Key := ↥unions) (fun T => ⟨κv T, hκmem T⟩) (fun U B => ∀ j ∈ U.val, s j ∉ B)
    (fun T B => by
      simp only [hκ]
      constructor
      · intro hB i hi j hj; exact hB j ⟨i, hi, hj⟩
      · rintro hB j ⟨i, hi, hj⟩; exact hB i hi j hj)
  refine ⟨send, recv, fun a b => ?_⟩
  rw [h a b]
  exact decide_card_congr2 _ _ (fun I => by
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, h2⟩
      have := h1 v hv
      cases hsv : side v <;> simpa [hsv] using this
    · rintro ⟨h1, h2⟩
      refine ⟨fun v hv => ?_, h2⟩
      have := h1 v hv
      cases hsv : side v <;> simpa [hsv] using this)

theorem part2_main : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  ∀ (l r : Nat) (C : Fin l → Finset (Fin r)) (unions : Finset (Finset (Fin r))),
  (∀ U ∈ unions, ∃ S : Finset (Fin l), ∀ j, j ∈ U ↔ ∃ i ∈ S, j ∈ C i) →
  let Key := ↥unions
  let q := unions.card
  let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N) =>
    Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
    (∀ j, side (s j) = true) ∧ (∀ u, u ∉ G u) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
    ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
  let odd := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
    decide (((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card % 2 = 1)
  ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side shore : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N) (tag : Fin N → Option Key),
    fits N G side p s ∧ N ≤ 6*(l+r)+(l+r+14)*q+2 ∧
    (∀ u, ∀ v ∈ G u, shore v ≠ shore u) ∧
    (∀ i, tag (p i) = none) ∧ (∀ j, tag (s j) = none) ∧
    (∀ u, (tag u).isSome = true → (G u).card = 1) ∧
    let Table := Key → Bool
    let result := fun (f g : Table) => odd N G (fun v =>
      (tag v).elim true (fun U => !((if side v then g else f) U)))
    (∀ f g, result f g = decide (((Finset.univ : Finset (Key × Key)).filter (fun pair =>
      f pair.1 = true ∧ g pair.2 = true ∧ pair.1.val ⊆ pair.2.val)).card % 2 = 1)) ∧
    ∀ (K : Nat) (rows cols : Fin K → Finset Table) (guess : Fin K → Table → Bool),
      (∀ f g : Table, ∃! i, f ∈ rows i ∧ g ∈ cols i) →
      let D := 2^q
      let correct := ((Finset.univ : Finset (Table × Table)).filter (fun a =>
        ∃ i, a.1 ∈ rows i ∧ a.2 ∈ cols i ∧ guess i a.2 = result a.1 a.2)).card
      (2*correct-D^2)^2 ≤ K*D^3 := by
  intro l r C unions hun1 Key q fits odd
  have hbu : ∀ U : ↥unions, ∀ j, j ∈ U.val ↔ ∃ i, C i ⊆ U.val ∧ j ∈ C i := by
    intro U j
    obtain ⟨S, hS⟩ := hun1 U.val U.2
    constructor
    · intro hj
      obtain ⟨i, hi, hji⟩ := (hS j).mp hj
      exact ⟨i, fun j' hj' => (hS j').mpr ⟨i, hi, hj'⟩, hji⟩
    · rintro ⟨i, hi, hji⟩; exact hi hji
  have hSLinj : Function.Injective (fun U i => decide (i ∈ SLf C unions U)) := by
    intro U V h
    have h' : ∀ i, (C i ⊆ U.val ↔ C i ⊆ V.val) := by
      intro i
      have := congrFun h i
      simpa [SLf] using this
    apply Subtype.ext
    ext j
    rw [hbu U j, hbu V j]
    simp only [h']
  have hSRinj : Function.Injective (fun U j => decide (j ∈ SRf unions U)) := by
    intro U V h
    apply Subtype.ext
    ext j
    have := congrFun h j
    simpa [SRf] using this
  have hcrossK : ∀ U V : ↥unions,
      (∀ i j, crf C i j = true → ¬(i ∈ SLf C unions U ∧ j ∈ SRf unions V)) ↔ U.val ⊆ V.val := by
    intro U V
    simp only [crf, SLf, SRf, decide_eq_true_eq, Finset.mem_filter, Finset.mem_univ, true_and,
      not_and, not_not]
    constructor
    · intro h j hj
      obtain ⟨i, hi, hji⟩ := (hbu U j).mp hj
      exact h i j hji hi
    · intro h i j hji hi
      exact h (hi hji)
  set e := Fintype.equivFin (FV l r ↥unions) with he
  refine ⟨Fintype.card (FV l r ↥unions),
    fun u => univ.filter (fun w => adjV (SLf C unions) (SRf unions) (crf C) (e.symm u) (e.symm w) = true),
    fun u => sideV (e.symm u), fun u => shoreV (e.symm u),
    fun i => e (Sum.inl (Sum.inl i)), fun j => e (Sum.inr (Sum.inl j)),
    fun u => tagV (e.symm u), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i i' h; simpa using h
  · intro j j' h; simpa using h
  · intro i; simp [sideV]
  · intro j; simp [sideV]
  · intro u; simp [adjV_irrefl]
  · intro u v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [adjV_symm]
  · intro u v hu hv
    obtain ⟨a, rfl⟩ := e.surjective u
    obtain ⟨b, rfl⟩ := e.surjective v
    simp only [Equiv.symm_apply_apply] at hu hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
    rcases a with a | a <;> rcases b with b | b <;> simp [sideV] at hu hv
    rw [adjV_cross]
    constructor
    · rintro ⟨i, j, rfl, rfl, h⟩; exact ⟨i, j, rfl, rfl, by simpa [crf] using h⟩
    · rintro ⟨i, j, h1, h2, h3⟩
      refine ⟨i, j, ?_, ?_, by simpa [crf] using h3⟩
      · simpa using h1
      · simpa using h2
  · have h12 : 12 * unions.card ≤ (l + r + 14) * unions.card := Nat.mul_le_mul_right _ (by omega)
    show Fintype.card (FV l r ↥unions) ≤ 6*(l+r)+(l+r+14)*unions.card+2
    rw [card_FV, Fintype.card_coe]
    nlinarith [h12]
  · intro u v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    exact (adjV_shore _ _ _ _ _ hv).symm
  · intro i; simp [tagV, tagH]
  · intro j; simp [tagV, tagH]
  · intro u hu
    obtain ⟨c, hc⟩ := tag_nbr (SLf C unions) (SRf unions) (crf C) (e.symm u) hu
    rw [Finset.card_eq_one]
    refine ⟨e c, ?_⟩
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hc, Equiv.symm_apply_eq]
  · intro Table result
    let resT : (↥unions → Bool) → (↥unions → Bool) → Bool := fun f g =>
      decide ((univ.filter (fun pair : ↥unions × ↥unions =>
        f pair.1 = true ∧ g pair.2 = true ∧ pair.1.val ⊆ pair.2.val)).card % 2 = 1)
    have hres : ∀ f g, result f g = resT f g := by
      intro f g
      apply decide_iff'
      apply mod2_iff
      rw [transport e (adjV (SLf C unions) (SRf unions) (crf C)) (liveV f g) _ _ ?hG ?hl]
      · rw [Finset.natCast_card_filter, count_formula (SLf C unions) (SRf unions) (crf C)
          hSLinj hSRinj f g, Finset.natCast_card_filter, Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro U _
        apply Finset.sum_congr rfl
        intro V _
        apply ite_iff
        rw [hcrossK]
      · intro a b
        simp
      · intro a
        simp only [Equiv.symm_apply_apply]
        exact live_tag f g a
    refine ⟨fun f g => (hres f g).trans (decide_card_congr2 _ _ (fun x => Iff.rfl)),
      fun K rows cols guess hpart => ?_⟩
    exact rect_bound resT result hres (2 ^ unions.card)
      (by simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe])
      (fun f f' => by
        rw [orth (fun U V : ↥unions => U.val ⊆ V.val) (fun U => U.val.card)
          (fun U => Finset.Subset.refl _)
          (fun U V h hne => Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨h, fun h' => hne (Subtype.ext h')⟩)) resT (fun f g => rfl) f f', Fintype.card_coe])
      K rows cols guess hpart

end PEqualNP.Outside.L_lib_1232_aux

theorem PEqualNP.Outside.L_lib_1232 : letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (l r : Nat) (C : Fin l → Finset (Fin r)),
  let unions := (Finset.univ : Finset (Finset (Fin l))).image (fun S => S.biUnion C)
  let Key := ↥unions
  let q := unions.card
  let fits := fun (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N) =>
    Function.Injective p ∧ Function.Injective s ∧ (∀ i, side (p i) = false) ∧
    (∀ j, side (s j) = true) ∧ (∀ u, u ∉ G u) ∧ (∀ u v, v ∈ G u ↔ u ∈ G v) ∧
    ∀ u v, side u = false → side v = true →
      (v ∈ G u ↔ ∃ i j, u = p i ∧ v = s j ∧ j ∈ C i)
  let odd := fun (N : Nat) (G : Fin N → Finset (Fin N)) (live : Fin N → Bool) =>
    decide (((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, live v = true) ∧ ∀ u ∈ I, ∀ v ∈ G u, v ∉ I)).card % 2 = 1)
  (∀ (N : Nat) (G : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N), fits N G side p s →
    ∃ (send : (Fin N → Bool) → Key → Bool) (recv : (Key → Bool) → (Fin N → Bool) → Bool),
      ∀ a b, recv (send a) b = odd N G (fun v => if side v then b v else a v)) ∧
  ∃ (N : Nat) (G : Fin N → Finset (Fin N)) (side shore : Fin N → Bool)
    (p : Fin l → Fin N) (s : Fin r → Fin N) (tag : Fin N → Option Key),
    fits N G side p s ∧ N ≤ 6*(l+r)+(l+r+14)*q+2 ∧
    (∀ u, ∀ v ∈ G u, shore v ≠ shore u) ∧
    (∀ i, tag (p i) = none) ∧ (∀ j, tag (s j) = none) ∧
    (∀ u, (tag u).isSome = true → (G u).card = 1) ∧
    let Table := Key → Bool
    let result := fun (f g : Table) => odd N G (fun v =>
      (tag v).elim true (fun U => !((if side v then g else f) U)))
    (∀ f g, result f g = decide (((Finset.univ : Finset (Key × Key)).filter (fun pair =>
      f pair.1 = true ∧ g pair.2 = true ∧ pair.1.val ⊆ pair.2.val)).card % 2 = 1)) ∧
    ∀ (K : Nat) (rows cols : Fin K → Finset Table) (guess : Fin K → Table → Bool),
      (∀ f g : Table, ∃! i, f ∈ rows i ∧ g ∈ cols i) →
      let D := 2^q
      let correct := ((Finset.univ : Finset (Table × Table)).filter (fun a =>
        ∃ i, a.1 ∈ rows i ∧ a.2 ∈ cols i ∧ guess i a.2 = result a.1 a.2)).card
      (2*correct-D^2)^2 ≤ K*D^3 := by
  intro l r C
  refine ⟨PEqualNP.Outside.L_lib_1232_aux.part1_main l r C _ ?_,
    PEqualNP.Outside.L_lib_1232_aux.part2_main l r C _ ?_⟩
  · intro S
    simp only [Finset.mem_image, Finset.mem_univ, true_and, exists_exists_eq_and]
    exact ⟨S, fun j => by simp [Finset.mem_biUnion]⟩
  · intro U hU
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hU
    obtain ⟨S, rfl⟩ := hU
    exact ⟨S, fun j => by simp [Finset.mem_biUnion]⟩
