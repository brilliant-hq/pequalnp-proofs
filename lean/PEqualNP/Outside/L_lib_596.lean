import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_596

open Finset

theorem rank_bound {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (A : Matrix ι (Fin d) K) (B : Matrix (Fin d) ι K) (h : A * B = 1) : Fintype.card ι ≤ d := by
  have h1 := Matrix.rank_mul_le_left A B
  have h2 := Matrix.rank_le_card_width A
  rw [h, Matrix.rank_one] at h1
  simpa using h1.trans h2

section Generic

variable {F : Type} [Field F] {t : ℕ} {T : Fin t → Type}

def mix (i : ℕ) (τ σ : (j : Fin t) → T j) : (j : Fin t) → T j :=
  fun j => if j.val < i then τ j else σ j

theorem fold_congr {S : Type} (l : List (Fin t)) (g g' : Fin t → S → S)
    (h : ∀ x ∈ l, g x = g' x) (init : S) :
    l.foldl (fun cur st => g st cur) init = l.foldl (fun cur st => g' st cur) init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih (fun y hy => h y (by simp [hy])) _

theorem fold_lin {V : Type} [AddCommGroup V] [Module F V] (l : List (Fin t))
    (f : Fin t → V →ₗ[F] V) :
    ∃ L : V →ₗ[F] V, ∀ v, l.foldl (fun cur st => f st cur) v = L v := by
  induction l with
  | nil => exact ⟨LinearMap.id, fun v => rfl⟩
  | cons x l ih =>
    obtain ⟨L, hL⟩ := ih
    exact ⟨L ∘ₗ f x, fun v => by simp only [List.foldl_cons]; rw [hL]; rfl⟩

theorem mem_take_lt {i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).take i) : x.val < i := by
  obtain ⟨n, hn, hx⟩ := List.mem_take_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show n < i
  omega

theorem mem_drop_ge {i : ℕ} {x : Fin t} (h : x ∈ (List.finRange t).drop i) : i ≤ x.val := by
  obtain ⟨n, hn, hx⟩ := List.mem_drop_iff_getElem.1 h
  rw [← hx, List.getElem_finRange]
  show i ≤ i + n
  omega

theorem lower {d : ℕ} (c : ((j : Fin t) → T j) → F) (s : Fin d → F)
    (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
    (out : (Fin d → F) →ₗ[F] F)
    (hc : ∀ tests : (j : Fin t) → T j,
      out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) = c tests)
    (i : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (τ σ : ι → (j : Fin t) → T j)
    (hδ : ∀ a b, c (mix i (τ a) (σ b)) = if a = b then 1 else 0) : Fintype.card ι ≤ d := by
  let u : ι → Fin d → F := fun a =>
    ((List.finRange t).take i).foldl (fun cur stage => step stage (τ a stage) cur) s
  have hL : ∀ b, ∃ L : (Fin d → F) →ₗ[F] (Fin d → F), ∀ v,
      ((List.finRange t).drop i).foldl (fun cur stage => step stage (σ b stage) cur) v = L v :=
    fun b => fold_lin _ (fun st => step st (σ b st))
  choose L hL using hL
  have key : ∀ a b, out (L b (u a)) = if a = b then 1 else 0 := by
    intro a b
    have e1 : ((List.finRange t).take i).foldl
        (fun cur stage => step stage (mix i (τ a) (σ b) stage) cur) s = u a :=
      fold_congr _ (fun st => ⇑(step st (mix i (τ a) (σ b) st))) (fun st => ⇑(step st (τ a st)))
        (fun x hx => by simp only [mix, if_pos (mem_take_lt hx)]) s
    have e2 : ∀ v, ((List.finRange t).drop i).foldl
        (fun cur stage => step stage (mix i (τ a) (σ b) stage) cur) v =
        ((List.finRange t).drop i).foldl (fun cur stage => step stage (σ b stage) cur) v :=
      fun v => fold_congr _ (fun st => ⇑(step st (mix i (τ a) (σ b) st)))
        (fun st => ⇑(step st (σ b st)))
        (fun x hx => by simp only [mix, if_neg (not_lt.2 (mem_drop_ge hx))]) v
    rw [← hδ a b, ← hc, ← hL b, ← e1, ← e2, ← List.foldl_append, List.take_append_drop]
  have hM : (Matrix.of fun (a : ι) (j : Fin d) => u a j) *
      (Matrix.of fun (j : Fin d) (b : ι) => out (L b (fun j' => if j = j' then 1 else 0))) = 1 := by
    ext a b
    have := LinearMap.pi_apply_eq_sum_univ (out ∘ₗ L b) (u a)
    simp only [LinearMap.comp_apply] at this
    rw [Matrix.mul_apply, Matrix.one_apply, ← key a b, this]
    simp only [Matrix.of_apply, smul_eq_mul]
  exact rank_bound d _ _ hM

def row (c : ((j : Fin t) → T j) → F) (i : ℕ) (τ : (j : Fin t) → T j) :
    ((j : Fin t) → T j) → F :=
  fun σ => c (mix i τ σ)

def RS (c : ((j : Fin t) → T j) → F) (i : ℕ) : Submodule F (((j : Fin t) → T j) → F) :=
  Submodule.span F (Set.range (row c i))

theorem row_mem (c : ((j : Fin t) → T j) → F) (i : ℕ) (τ : (j : Fin t) → T j) :
    row c i τ ∈ RS c i :=
  Submodule.subset_span ⟨τ, rfl⟩

def shiftL (j : Fin t) (x : T j) :
    (((j : Fin t) → T j) → F) →ₗ[F] (((j : Fin t) → T j) → F) :=
  LinearMap.funLeft F F (fun σ => Function.update σ j x)

theorem mix_update (i : Fin t) (x : T i) (τ σ : (j : Fin t) → T j) :
    mix i.val τ (Function.update σ i x) = mix (i.val + 1) (Function.update τ i x) σ := by
  funext l
  by_cases hl : l = i
  · subst hl
    simp [mix]
  · have hne : l.val ≠ i.val := fun h => hl (Fin.ext h)
    simp only [mix, Function.update_of_ne hl]
    by_cases h1 : l.val < i.val
    · rw [if_pos h1, if_pos (by omega)]
    · rw [if_neg h1, if_neg (by omega)]

theorem shift_row (c : ((j : Fin t) → T j) → F) (j : Fin t) (x : T j) (τ : (j : Fin t) → T j) :
    shiftL j x (row c j.val τ) = row c (j.val + 1) (Function.update τ j x) := by
  funext σ
  simp only [shiftL, LinearMap.funLeft_apply, row]
  rw [mix_update]

theorem shift_maps (c : ((j : Fin t) → T j) → F) (j : Fin t) (x : T j) :
    ∀ r ∈ RS c j.val, shiftL j x r ∈ RS c (j.val + 1) := by
  intro r hr
  have hle : RS c j.val ≤ (RS c (j.val + 1)).comap (shiftL j x) := by
    rw [RS, Submodule.span_le]
    rintro _ ⟨τ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap]
    rw [shift_row]
    exact row_mem _ _ _
  exact hle hr

theorem embed {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V] (d : ℕ)
    (h : Module.finrank F V ≤ d) :
    ∃ (e : V →ₗ[F] (Fin d → F)) (p : (Fin d → F) →ₗ[F] V), ∀ v, p (e v) = v := by
  let b := Module.finBasis F V
  let ins : (Fin (Module.finrank F V) → F) →ₗ[F] (Fin d → F) :=
    { toFun := fun v j => if hj : j.val < Module.finrank F V then v ⟨j.val, hj⟩ else 0
      map_add' := fun v w => by
        funext j
        by_cases hj : j.val < Module.finrank F V <;> simp [hj]
      map_smul' := fun a v => by
        funext j
        by_cases hj : j.val < Module.finrank F V <;> simp [hj] }
  let pr : (Fin d → F) →ₗ[F] (Fin (Module.finrank F V) → F) :=
    LinearMap.funLeft F F (Fin.castLE h)
  refine ⟨ins ∘ₗ b.equivFun.toLinearMap, b.equivFun.symm.toLinearMap ∘ₗ pr, fun v => ?_⟩
  have hpi : ∀ w, pr (ins w) = w := by
    intro w
    funext j
    simp [pr, ins, LinearMap.funLeft_apply, j.isLt]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hpi, LinearEquiv.symm_apply_apply]

theorem upper {d : ℕ} [∀ j, Fintype (T j)] [∀ j, DecidableEq (T j)]
    (c : ((j : Fin t) → T j) → F) (τ0 : (j : Fin t) → T j)
    (hR : ∀ i, i ≤ t → Module.finrank F (RS c i) ≤ d) :
    ∃ (s : Fin d → F) (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
      (out : (Fin d → F) →ₗ[F] F), ∀ tests : (j : Fin t) → T j,
      out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
        c tests := by
  have hE : ∀ i, i ≤ t → ∃ (e : RS c i →ₗ[F] (Fin d → F)) (p : (Fin d → F) →ₗ[F] RS c i),
      ∀ v, p (e v) = v := fun i hi => embed d (hR i hi)
  choose e p hep using hE
  let st : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)) := fun j x =>
    e (j.val + 1) j.isLt ∘ₗ ((shiftL j x).restrict (shift_maps c j x)) ∘ₗ p j.val j.isLt.le
  let ev : (((j : Fin t) → T j) → F) →ₗ[F] F := LinearMap.proj τ0
  refine ⟨e 0 (Nat.zero_le _) ⟨row c 0 τ0, row_mem c 0 τ0⟩, st,
    ev ∘ₗ (RS c t).subtype ∘ₗ p t le_rfl, fun tests => ?_⟩
  have inv : ∀ i (hi : i ≤ t), ((List.finRange t).take i).foldl
      (fun cur stage => st stage (tests stage) cur)
      (e 0 (Nat.zero_le _) ⟨row c 0 τ0, row_mem c 0 τ0⟩) =
        e i hi ⟨row c i tests, row_mem c i tests⟩ := by
    intro i
    induction i with
    | zero =>
      intro hi
      simp only [List.take_zero, List.foldl_nil]
      congr 2
    | succ i ih =>
      intro hi
      have hget : (List.finRange t)[i]? = some ⟨i, by omega⟩ := by
        rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_finRange]
        rfl
      rw [List.take_add_one, List.foldl_append, ih (by omega), hget]
      simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
      simp only [st, LinearMap.comp_apply, hep]
      congr 1
      apply Subtype.ext
      rw [LinearMap.restrict_apply]
      show shiftL _ _ (row c i tests) = row c (i + 1) tests
      rw [shift_row]
      simp
  have h2 := inv t le_rfl
  rw [List.take_of_length_le (by simp)] at h2
  rw [h2]
  simp only [LinearMap.comp_apply, hep, ev, LinearMap.proj_apply, Submodule.subtype_apply, row]
  congr 1
  funext j
  simp [mix, j.isLt]

end Generic

theorem decomp {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (KP KQ : Submodule (ZMod 2) V) [Fintype KP] [Fintype KQ] [Fintype (V ⧸ (KP ⊔ KQ))]
    (hbot : KP ⊓ KQ = ⊥)
    (rep : V ⧸ (KP ⊔ KQ) → V) (hrep : ∀ κ, Submodule.Quotient.mk (rep κ) = κ)
    (p f : V → F) (hp : ∀ v, ∀ a ∈ KP, p (v + a) = p v) (hf : ∀ v, ∀ b ∈ KQ, f (v + b) = f v) :
    ∑ v, p v * f v = ∑ κ, (∑ b : KQ, p (rep κ + b)) * (∑ a : KP, f (rep κ + a)) := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ
    (fun v => (Submodule.Quotient.mk v : V ⧸ (KP ⊔ KQ))) (fun v => p v * f v)]
  refine Finset.sum_congr rfl (fun κ _ => ?_)
  have hbij : ∑ x : KP × KQ, p (rep κ + x.2) * f (rep κ + x.1) =
      ∑ v ∈ Finset.univ.filter (fun v => (Submodule.Quotient.mk v : V ⧸ (KP ⊔ KQ)) = κ),
        p v * f v := by
    refine Finset.sum_bij (fun x _ => rep κ + x.1 + x.2) ?_ ?_ ?_ ?_
    · intro x _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hk : (Submodule.Quotient.mk (rep κ + x.1 + x.2) : V ⧸ (KP ⊔ KQ)) =
          Submodule.Quotient.mk (rep κ) := by
        apply (Submodule.Quotient.eq _).2
        have e : rep κ + (x.1 : V) + x.2 - rep κ = (x.1 : V) + x.2 := by abel
        rw [e]
        exact Submodule.add_mem_sup x.1.2 x.2.2
      rw [hk, hrep]
    · intro x _ y _ hxy
      have h12 : (x.1 : V) + x.2 = y.1 + y.2 := by
        have := hxy
        simp only [add_assoc] at this
        exact add_left_cancel this
      have hsub : (x.1 : V) - y.1 = y.2 - x.2 := by
        rw [sub_eq_sub_iff_add_eq_add, h12, add_comm]
      have hmem : (x.1 : V) - y.1 ∈ KP ⊓ KQ :=
        Submodule.mem_inf.2 ⟨KP.sub_mem x.1.2 y.1.2, hsub ▸ KQ.sub_mem y.2.2 x.2.2⟩
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
      have h2 : (x.2 : V) = y.2 := by
        rw [hmem] at h12
        exact add_left_cancel h12
      exact Prod.ext (Subtype.ext hmem) (Subtype.ext h2)
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      have hv2 : (Submodule.Quotient.mk v : V ⧸ (KP ⊔ KQ)) = Submodule.Quotient.mk (rep κ) := by
        rw [hv, hrep]
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 ((Submodule.Quotient.eq _).1 hv2)
      refine ⟨(⟨y, hy⟩, ⟨z, hz⟩), Finset.mem_univ _, ?_⟩
      show rep κ + y + z = v
      rw [add_assoc, hyz]
      abel
    · intro x _
      have e1 : p (rep κ + x.1 + x.2) = p (rep κ + x.2) := by
        rw [show rep κ + (x.1 : V) + x.2 = (rep κ + x.2) + x.1 by abel]
        exact hp _ _ x.1.2
      have e2 : f (rep κ + x.1 + x.2) = f (rep κ + x.1) := hf _ _ x.2.2
      rw [e1, e2]
  rw [← hbij, Finset.sum_mul_sum, Finset.sum_comm]
  exact Fintype.sum_prod_type' (fun (a : KP) (b : KQ) => p (rep κ + b) * f (rep κ + a))

theorem delta_sum {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] [DecidableEq V]
    (KP KQ : Submodule (ZMod 2) V) [DecidablePred (· ∈ KP)] [DecidablePred (· ∈ KQ)]
    (hbot : KP ⊓ KQ = ⊥)
    (rep : V ⧸ (KP ⊔ KQ) → V) (hrep : ∀ κ, Submodule.Quotient.mk (rep κ) = κ)
    [DecidableEq (V ⧸ (KP ⊔ KQ))] (α β : V ⧸ (KP ⊔ KQ)) :
    ∑ v, (if v - rep α ∈ KP then (1 : F) else 0) * (if v - rep β ∈ KQ then (1 : F) else 0) =
      if α = β then 1 else 0 := by
  by_cases hab : α = β
  · subst hab
    rw [if_pos rfl, Finset.sum_eq_single (rep α)]
    · simp [sub_self, KP.zero_mem, KQ.zero_mem]
    · intro v _ hv
      by_cases h1 : v - rep α ∈ KP
      · by_cases h2 : v - rep α ∈ KQ
        · exfalso
          have hmem : v - rep α ∈ KP ⊓ KQ := Submodule.mem_inf.2 ⟨h1, h2⟩
          rw [hbot, Submodule.mem_bot, sub_eq_zero] at hmem
          exact hv hmem
        · simp [h2]
      · simp [h1]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hab]
    apply Finset.sum_eq_zero
    intro v _
    by_cases h1 : v - rep α ∈ KP
    · by_cases h2 : v - rep β ∈ KQ
      · exfalso
        apply hab
        rw [← hrep α, ← hrep β]
        apply (Submodule.Quotient.eq _).2
        have e : rep α - rep β = (v - rep β) - (v - rep α) := by abel
        rw [e]
        exact Submodule.sub_mem _ (Submodule.mem_sup_right h2) (Submodule.mem_sup_left h1)
      · simp [h2]
    · simp [h1]

section Spec

variable {k m t : ℕ}

noncomputable def Gm (gen : Fin m → (Fin k → ZMod 2)) :
    (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin k → ZMod 2) where
  toFun a := ∑ h, a h • gen h
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, mul_smul]

noncomputable def piS (S : Finset (Fin k)) : (Fin k → ZMod 2) →ₗ[ZMod 2] (S → ZMod 2) :=
  LinearMap.funLeft _ _ Subtype.val

noncomputable def KS (gen : Fin m → (Fin k → ZMod 2)) (S : Finset (Fin k)) :
    Submodule (ZMod 2) (LinearMap.range (Gm gen)) :=
  LinearMap.ker (piS S ∘ₗ (LinearMap.range (Gm gen)).subtype)

theorem mem_KS (gen : Fin m → (Fin k → ZMod 2)) (S : Finset (Fin k))
    (v : LinearMap.range (Gm gen)) :
    v ∈ KS gen S ↔ ∀ x ∈ S, (v : Fin k → ZMod 2) x = 0 := by
  simp [KS, piS, funext_iff, LinearMap.funLeft_apply]

theorem rk_eq (gen : Fin m → (Fin k → ZMod 2)) (S : Finset (Fin k)) :
    Matrix.rank (fun row (coord : S) => gen row coord.val : Matrix (Fin m) S (ZMod 2)) =
      Module.finrank (ZMod 2)
        (LinearMap.range (piS S ∘ₗ (LinearMap.range (Gm gen)).subtype)) := by
  refine (Matrix.rank_transpose _).symm.trans ?_
  have h : (Matrix.transpose
      (fun row (coord : S) => gen row coord.val : Matrix (Fin m) S (ZMod 2))).mulVecLin =
      piS S ∘ₗ Gm gen := by
    apply LinearMap.ext
    intro a
    funext coord
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, piS, Gm, LinearMap.comp_apply,
      LinearMap.funLeft_apply, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  unfold Matrix.rank
  rw [h, LinearMap.range_comp, LinearMap.range_comp, Submodule.range_subtype]

def PS (scope : Fin t → Finset (Fin k)) (i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)

def QS (scope : Fin t → Finset (Fin k)) (i : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)

theorem mem_PS (scope : Fin t → Finset (Fin k)) (i : ℕ) (x : Fin k) :
    x ∈ PS scope i ↔ ∃ before : Fin t, before.val < i ∧ x ∈ scope before := by
  simp [PS]

theorem mem_QS (scope : Fin t → Finset (Fin k)) (i : ℕ) (x : Fin k) :
    x ∈ QS scope i ↔ ∃ after : Fin t, i ≤ after.val ∧ x ∈ scope after := by
  simp [QS]

theorem cover_PQ (scope : Fin t → Finset (Fin k)) (hc : ∀ v : Fin k, ∃ j : Fin t, v ∈ scope j)
    (i : ℕ) (x : Fin k) : x ∈ PS scope i ∨ x ∈ QS scope i := by
  obtain ⟨j, hj⟩ := hc x
  by_cases h : j.val < i
  · exact Or.inl ((mem_PS scope i x).2 ⟨j, h, hj⟩)
  · exact Or.inr ((mem_QS scope i x).2 ⟨j, not_lt.1 h, hj⟩)

theorem bot_PQ (gen : Fin m → (Fin k → ZMod 2)) (scope : Fin t → Finset (Fin k))
    (hc : ∀ v : Fin k, ∃ j : Fin t, v ∈ scope j) (i : ℕ) :
    KS gen (PS scope i) ⊓ KS gen (QS scope i) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, mem_KS, mem_KS] at hv
  rw [Submodule.mem_bot]
  apply Subtype.ext
  funext x
  rcases cover_PQ scope hc i x with h | h
  · simpa using hv.1 x h
  · simpa using hv.2 x h

theorem bot_univ (gen : Fin m → (Fin k → ZMod 2)) :
    KS gen (Finset.univ : Finset (Fin k)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [mem_KS] at hv
  rw [Submodule.mem_bot]
  apply Subtype.ext
  funext x
  simpa using hv x (Finset.mem_univ x)

abbrev Qt (gen : Fin m → (Fin k → ZMod 2)) (scope : Fin t → Finset (Fin k)) (i : ℕ) :=
  (LinearMap.range (Gm gen)) ⧸ (KS gen (PS scope i) ⊔ KS gen (QS scope i))

theorem card_Qt (gen : Fin m → (Fin k → ZMod 2)) (scope : Fin t → Finset (Fin k))
    (hc : ∀ v : Fin k, ∃ j : Fin t, v ∈ scope j) (i : ℕ) :
    Nat.card (Qt gen scope i) =
      2 ^ (Matrix.rank (fun row (coord : PS scope i) => gen row coord.val :
              Matrix (Fin m) (PS scope i) (ZMod 2)) +
            Matrix.rank (fun row (coord : QS scope i) => gen row coord.val :
              Matrix (Fin m) (QS scope i) (ZMod 2)) -
            Matrix.rank (fun row (coord : (Finset.univ : Finset (Fin k))) => gen row coord.val :
              Matrix (Fin m) (Finset.univ : Finset (Fin k)) (ZMod 2))) := by
  classical
  rw [rk_eq, rk_eq, rk_eq]
  have h1 : Module.finrank (ZMod 2) (Qt gen scope i) +
      Module.finrank (ZMod 2) ↥(KS gen (PS scope i) ⊔ KS gen (QS scope i)) =
      Module.finrank (ZMod 2) (LinearMap.range (Gm gen)) :=
    Submodule.finrank_quotient_add_finrank _
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq (KS gen (PS scope i)) (KS gen (QS scope i))
  rw [bot_PQ gen scope hc i, finrank_bot] at h2
  have h3 : Module.finrank (ZMod 2)
      (LinearMap.range (piS (PS scope i) ∘ₗ (LinearMap.range (Gm gen)).subtype)) +
      Module.finrank (ZMod 2) (KS gen (PS scope i)) =
      Module.finrank (ZMod 2) (LinearMap.range (Gm gen)) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h4 : Module.finrank (ZMod 2)
      (LinearMap.range (piS (QS scope i) ∘ₗ (LinearMap.range (Gm gen)).subtype)) +
      Module.finrank (ZMod 2) (KS gen (QS scope i)) =
      Module.finrank (ZMod 2) (LinearMap.range (Gm gen)) :=
    LinearMap.finrank_range_add_finrank_ker _
  have h5 : Module.finrank (ZMod 2)
      (LinearMap.range (piS (Finset.univ : Finset (Fin k)) ∘ₗ
        (LinearMap.range (Gm gen)).subtype)) +
      Module.finrank (ZMod 2) (KS gen (Finset.univ : Finset (Fin k))) =
      Module.finrank (ZMod 2) (LinearMap.range (Gm gen)) :=
    LinearMap.finrank_range_add_finrank_ker _
  rw [bot_univ, finrank_bot] at h5
  haveI : Finite (Qt gen scope i) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI := Fintype.ofFinite (Qt gen scope i)
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  congr 1
  apply Nat.eq_sub_of_add_eq
  omega

noncomputable def cnt (F : Type) [Field F] (base : Fin k → ZMod 2) (gen : Fin m → (Fin k → ZMod 2))
    (scope : Fin t → Finset (Fin k)) (tests : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool) : F :=
  ((Nat.card {w : Fin k → ZMod 2 //
    w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧
      ∀ j, tests j (fun tested => w tested.val) = true} : ℕ) : F)

theorem count_eq (F : Type) [Field F] (base : Fin k → ZMod 2) (gen : Fin m → (Fin k → ZMod 2))
    (Acc : (Fin k → ZMod 2) → Prop) [Fintype (LinearMap.range (Gm gen))] [DecidablePred Acc] :
    ((Nat.card {w : Fin k → ZMod 2 //
      w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧ Acc w} : ℕ) : F) =
      ∑ v : LinearMap.range (Gm gen), if Acc (base + v) then 1 else 0 := by
  classical
  have e : {v : LinearMap.range (Gm gen) // Acc (base + v)} ≃
      {w : Fin k → ZMod 2 //
        w ∈ Set.range (fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h) ∧ Acc w} :=
    { toFun := fun x => ⟨base + x.1, by
          obtain ⟨a, ha⟩ := x.1.2
          exact ⟨a, by rw [← ha]; rfl⟩, x.2⟩
      invFun := fun y => ⟨⟨y.1 - base, by
          obtain ⟨a, ha⟩ := y.2.1
          exact ⟨a, by rw [← ha]; simp [Gm]⟩⟩, by simpa using y.2.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        apply Subtype.ext
        simp
      right_inv := fun y => by
        apply Subtype.ext
        simp }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.natCast_card_filter]

def pacc (scope : Fin t → Finset (Fin k)) (i : ℕ)
    (τ : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool) (w : Fin k → ZMod 2) : Prop :=
  ∀ j : Fin t, j.val < i → τ j (fun tested => w tested.val) = true

def facc (scope : Fin t → Finset (Fin k)) (i : ℕ)
    (σ : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool) (w : Fin k → ZMod 2) : Prop :=
  ∀ j : Fin t, i ≤ j.val → σ j (fun tested => w tested.val) = true

theorem acc_mix (scope : Fin t → Finset (Fin k)) (i : ℕ)
    (τ σ : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool) (w : Fin k → ZMod 2) :
    (∀ j, mix i τ σ j (fun tested => w tested.val) = true) ↔
      pacc scope i τ w ∧ facc scope i σ w := by
  constructor
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have := h j
      simp only [mix, if_pos hj] at this
      exact this
    · have := h j
      simp only [mix, if_neg (not_lt.2 hj)] at this
      exact this
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j.val < i
    · simp only [mix, if_pos hj]
      exact h1 j hj
    · simp only [mix, if_neg hj]
      exact h2 j (not_lt.1 hj)

theorem pacc_add (scope : Fin t → Finset (Fin k)) (i : ℕ)
    (τ : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool) (w v : Fin k → ZMod 2)
    (hv : ∀ x ∈ PS scope i, v x = 0) : pacc scope i τ (w + v) ↔ pacc scope i τ w := by
  have e : ∀ j : Fin t, j.val < i →
      (fun tested : ↥(scope j) => (w + v) tested.val) = (fun tested => w tested.val) := by
    intro j hj
    funext tested
    have hx : tested.val ∈ PS scope i := (mem_PS scope i _).2 ⟨j, hj, tested.2⟩
    simp [hv _ hx]
  unfold pacc
  constructor
  · intro h j hj
    rw [← e j hj]
    exact h j hj
  · intro h j hj
    rw [e j hj]
    exact h j hj

theorem facc_add (scope : Fin t → Finset (Fin k)) (i : ℕ)
    (σ : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool) (w v : Fin k → ZMod 2)
    (hv : ∀ x ∈ QS scope i, v x = 0) : facc scope i σ (w + v) ↔ facc scope i σ w := by
  have e : ∀ j : Fin t, i ≤ j.val →
      (fun tested : ↥(scope j) => (w + v) tested.val) = (fun tested => w tested.val) := by
    intro j hj
    funext tested
    have hx : tested.val ∈ QS scope i := (mem_QS scope i _).2 ⟨j, hj, tested.2⟩
    simp [hv _ hx]
  unfold facc
  constructor
  · intro h j hj
    rw [← e j hj]
    exact h j hj
  · intro h j hj
    rw [e j hj]
    exact h j hj

theorem count_split (F : Type) [Field F] (base : Fin k → ZMod 2) (gen : Fin m → (Fin k → ZMod 2))
    (scope : Fin t → Finset (Fin k)) (i : ℕ)
    (τ σ : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool)
    [Fintype (LinearMap.range (Gm gen))]
    [DecidablePred (pacc scope i τ)] [DecidablePred (facc scope i σ)] :
    cnt F base gen scope (mix i τ σ) =
      ∑ v : LinearMap.range (Gm gen), (if pacc scope i τ (base + v) then (1 : F) else 0) *
        (if facc scope i σ (base + v) then (1 : F) else 0) := by
  classical
  unfold cnt
  rw [count_eq F base gen _]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [ite_zero_mul_ite_zero, one_mul]
  exact if_congr (acc_mix scope i τ σ _) rfl rfl

def pin (scope : Fin t → Finset (Fin k)) (u : Fin k → ZMod 2) :
    (j : Fin t) → (↥(scope j) → ZMod 2) → Bool :=
  fun j z => decide (z = fun tested => u tested.val)

theorem pacc_pin (scope : Fin t → Finset (Fin k)) (i : ℕ) (u w : Fin k → ZMod 2) :
    pacc scope i (pin scope u) w ↔ ∀ x ∈ PS scope i, w x = u x := by
  unfold pacc pin
  simp only [decide_eq_true_eq]
  constructor
  · intro h x hx
    obtain ⟨j, hj, hxj⟩ := (mem_PS scope i x).1 hx
    exact congrFun (h j hj) ⟨x, hxj⟩
  · intro h j hj
    funext tested
    exact h _ ((mem_PS scope i _).2 ⟨j, hj, tested.2⟩)

theorem facc_pin (scope : Fin t → Finset (Fin k)) (i : ℕ) (u w : Fin k → ZMod 2) :
    facc scope i (pin scope u) w ↔ ∀ x ∈ QS scope i, w x = u x := by
  unfold facc pin
  simp only [decide_eq_true_eq]
  constructor
  · intro h x hx
    obtain ⟨j, hj, hxj⟩ := (mem_QS scope i x).1 hx
    exact congrFun (h j hj) ⟨x, hxj⟩
  · intro h j hj
    funext tested
    exact h _ ((mem_QS scope i _).2 ⟨j, hj, tested.2⟩)

theorem low_spec (F : Type) [Field F] (d : ℕ) (base : Fin k → ZMod 2)
    (gen : Fin m → (Fin k → ZMod 2)) (scope : Fin t → Finset (Fin k))
    (hc : ∀ v : Fin k, ∃ j : Fin t, v ∈ scope j) (i : ℕ) (s : Fin d → F)
    (step : (j : Fin t) → ((↥(scope j) → ZMod 2) → Bool) → ((Fin d → F) →ₗ[F] (Fin d → F)))
    (out : (Fin d → F) →ₗ[F] F)
    (h : ∀ tests : (j : Fin t) → (↥(scope j) → ZMod 2) → Bool,
      out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
        cnt F base gen scope tests) :
    Nat.card (Qt gen scope i) ≤ d := by
  classical
  haveI : Finite (Qt gen scope i) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI := Fintype.ofFinite (Qt gen scope i)
  choose rep hrep using Submodule.Quotient.mk_surjective
    (KS gen (PS scope i) ⊔ KS gen (QS scope i))
  rw [Nat.card_eq_fintype_card]
  refine lower (cnt F base gen scope) s step out h i
    (fun α => pin scope (base + (rep α : Fin k → ZMod 2)))
    (fun α => pin scope (base + (rep α : Fin k → ZMod 2))) (fun α β => ?_)
  rw [count_split]
  have hP : ∀ v : LinearMap.range (Gm gen),
      pacc scope i (pin scope (base + (rep α : Fin k → ZMod 2))) (base + v) ↔
        v - rep α ∈ KS gen (PS scope i) := by
    intro v
    rw [pacc_pin, mem_KS]
    simp [sub_eq_zero]
  have hQ : ∀ v : LinearMap.range (Gm gen),
      facc scope i (pin scope (base + (rep β : Fin k → ZMod 2))) (base + v) ↔
        v - rep β ∈ KS gen (QS scope i) := by
    intro v
    rw [facc_pin, mem_KS]
    simp [sub_eq_zero]
  simp only [hP, hQ]
  exact delta_sum _ _ (bot_PQ gen scope hc i) rep hrep α β

theorem up_spec (F : Type) [Field F] (base : Fin k → ZMod 2)
    (gen : Fin m → (Fin k → ZMod 2)) (scope : Fin t → Finset (Fin k))
    (hc : ∀ v : Fin k, ∃ j : Fin t, v ∈ scope j) (i : ℕ) :
    Module.finrank F (RS (cnt F base gen scope) i) ≤ Nat.card (Qt gen scope i) := by
  classical
  haveI : Finite (Qt gen scope i) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  letI := Fintype.ofFinite (Qt gen scope i)
  choose rep hrep using Submodule.Quotient.mk_surjective
    (KS gen (PS scope i) ⊔ KS gen (QS scope i))
  let B : Qt gen scope i → ((j : Fin t) → (↥(scope j) → ZMod 2) → Bool) → F := fun κ σ =>
    ∑ a : KS gen (PS scope i),
      if facc scope i σ (base + ((rep κ + a : LinearMap.range (Gm gen)) : Fin k → ZMod 2))
      then (1 : F) else 0
  have hrow : ∀ τ, row (cnt F base gen scope) i τ =
      ∑ κ, (∑ b : KS gen (QS scope i),
        if pacc scope i τ (base + ((rep κ + b : LinearMap.range (Gm gen)) : Fin k → ZMod 2))
        then (1 : F) else 0) • B κ := by
    intro τ
    funext σ
    simp only [row, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [count_split]
    rw [decomp (KS gen (PS scope i)) (KS gen (QS scope i)) (bot_PQ gen scope hc i) rep hrep
      (fun v => if pacc scope i τ (base + v) then (1 : F) else 0)
      (fun v => if facc scope i σ (base + v) then (1 : F) else 0)]
    · intro v a ha
      have := pacc_add scope i τ (base + (v : Fin k → ZMod 2)) (a : Fin k → ZMod 2)
        ((mem_KS gen _ a).1 ha)
      simp only [Submodule.coe_add, ← add_assoc, this]
    · intro v b hb
      have := facc_add scope i σ (base + (v : Fin k → ZMod 2)) (b : Fin k → ZMod 2)
        ((mem_KS gen _ b).1 hb)
      simp only [Submodule.coe_add, ← add_assoc, this]
  have hle : RS (cnt F base gen scope) i ≤ Submodule.span F (Set.range B) := by
    rw [RS, Submodule.span_le]
    rintro _ ⟨τ, rfl⟩
    rw [hrow]
    exact Submodule.sum_mem _ (fun κ _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨κ, rfl⟩))
  calc Module.finrank F (RS (cnt F base gen scope) i)
      ≤ Module.finrank F (Submodule.span F (Set.range B)) := Submodule.finrank_mono hle
    _ ≤ Fintype.card (Qt gen scope i) := finrank_range_le_card B
    _ = Nat.card (Qt gen scope i) := Nat.card_eq_fintype_card.symm

end Spec

end PEqualNP.Outside.L_lib_596

open PEqualNP.Outside.L_lib_596 in
theorem PEqualNP.Outside.L_lib_596 : ∀ (F : Type) [Field F] (k m t d : ℕ),
  let W := Fin k → ZMod 2
  ∀ (base : W) (gen : Fin m → W) (scope : Fin t → Finset (Fin k)),
    (∀ v : Fin k, ∃ j : Fin t, v ∈ scope j) →
    let key := fun a : Fin m → ZMod 2 => base + ∑ h : Fin m, a h • gen h
    let rk := fun S : Finset (Fin k) =>
      let M : Matrix (Fin m) S (ZMod 2) := fun row coord => gen row coord.val
      M.rank
    let need := (Finset.range (t+1)).sup (fun i =>
      let P := Finset.univ.filter (fun seen : Fin k => ∃ before : Fin t, before.val < i ∧ seen ∈ scope before)
      let Q := Finset.univ.filter (fun future : Fin k => ∃ after : Fin t, i ≤ after.val ∧ future ∈ scope after)
      2^(rk P + rk Q - rk Finset.univ))
    let T := fun idx : Fin t => (↥(scope idx) → ZMod 2) → Bool
    let count := fun tests : (j : Fin t) → T j =>
      Nat.card {w : W // w ∈ Set.range key ∧ ∀ j, tests j (fun tested => w tested.val) = true}
    (∃ (s : Fin d → F)
       (step : (j : Fin t) → T j → ((Fin d → F) →ₗ[F] (Fin d → F)))
       (out : (Fin d → F) →ₗ[F] F),
      ∀ tests : (j : Fin t) → T j,
        out ((List.finRange t).foldl (fun cur stage => step stage (tests stage) cur) s) =
          (count tests : F)) ↔ need ≤ d := by
  intro F _ k m t d
  dsimp only
  intro base gen scope hcover
  constructor
  · rintro ⟨s, step, out, h⟩
    rw [Finset.sup_le_iff]
    intro i _
    exact (card_Qt gen scope hcover i).symm.trans_le
      (low_spec F d base gen scope hcover i s step out h)
  · intro hd
    rw [Finset.sup_le_iff] at hd
    exact upper (cnt F base gen scope) (fun _ _ => true) (fun i hi =>
      (up_spec F base gen scope hcover i).trans ((card_Qt gen scope hcover i).trans_le
        (hd i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))))
