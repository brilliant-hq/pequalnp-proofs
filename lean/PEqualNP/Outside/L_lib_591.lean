import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_591

open Finset Equiv

theorem rank_bound {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (A : Matrix ι (Fin d) K) (B : Matrix (Fin d) ι K) (h : A * B = 1) : Fintype.card ι ≤ d := by
  have h1 := Matrix.rank_mul_le_left A B
  have h2 := Matrix.rank_le_card_width A
  rw [h, Matrix.rank_one] at h1
  simpa using h1.trans h2

theorem pad {K : Type} [Field K] {ι : Type} [Fintype ι] {α β : Type} (d : ℕ)
    (hd : Fintype.card ι ≤ d) (a : α → ι → K) (b : β → ι → K) :
    ∃ (A : α → Fin d → K) (B : β → Fin d → K),
      ∀ p q, ∑ σ, a p σ * b q σ = ∑ j : Fin d, A p j * B q j := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin d) (by simpa using hd)
  refine ⟨fun p => Function.extend e (a p) 0, fun q => Function.extend e (b q) 0, fun p q => ?_⟩
  apply Fintype.sum_of_injective e e.injective
  · intro j hj
    have hj' : ¬∃ x, e x = j := by simpa [Set.mem_range] using hj
    dsimp only
    rw [Function.extend_apply' _ _ _ hj']
    simp
  · intro σ
    simp [e.injective.extend_apply]

theorem exists_perm {n : ℕ} (i j k l : Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ p : Perm (Fin n), p i = k ∧ p j = l := by
  refine ⟨swap (swap i k j) l * swap i k, ?_, ?_⟩
  · have h1 : swap i k j ≠ k := by
      intro h
      have : j = i := by
        have := congrArg (swap i k) h
        simpa using this
      exact hij this.symm
    simp only [Perm.mul_apply, swap_apply_left]
    exact swap_apply_of_ne_of_ne h1.symm hkl
  · simp only [Perm.mul_apply, swap_apply_left]

theorem frame {K : Type} [Field K] {n : ℕ} {T : Type} [Fintype T] (φ ψ : T → Fin n → K)
    (h : ∀ x y : Fin n, (if x = y then (1 : K) else 0) = ∑ s, φ s x * ψ s y)
    (p r : Perm (Fin n)) :
    ((((Finset.univ : Finset (Fin n)).filter (fun i => r (p i) = i)).card : ℕ) : K) =
      ∑ s, ∑ t, (∑ i, φ s (p i) * ψ t i) * (∑ j, ψ s j * φ t (r j)) := by
  rw [Finset.natCast_card_filter]
  have e1 : ∀ i, (if r (p i) = i then (1 : K) else 0) =
      ∑ j, (if p i = j then (1 : K) else 0) * (if r j = i then (1 : K) else 0) := by
    intro i
    rw [Finset.sum_eq_single (p i)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  rw [Finset.sum_congr rfl (fun i _ => e1 i)]
  simp_rw [h, Finset.sum_mul_sum]
  calc ∑ i, ∑ j, ∑ s, ∑ t, φ s (p i) * ψ s j * (φ t (r j) * ψ t i)
      = ∑ i, ∑ s, ∑ j, ∑ t, φ s (p i) * ψ s j * (φ t (r j) * ψ t i) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ s, ∑ i, ∑ j, ∑ t, φ s (p i) * ψ s j * (φ t (r j) * ψ t i) := Finset.sum_comm
    _ = ∑ s, ∑ i, ∑ t, ∑ j, φ s (p i) * ψ s j * (φ t (r j) * ψ t i) :=
        Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
    _ = ∑ s, ∑ t, ∑ i, ∑ j, φ s (p i) * ψ s j * (φ t (r j) * ψ t i) :=
        Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
    _ = _ := by
        refine Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => ?_))
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        ring

theorem main_iff {K : Type} [Field K] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ)
    (u w : Perm (Fin n) → ι → K)
    (hfix : ∀ p r : Perm (Fin n),
      ((((Finset.univ : Finset (Fin n)).filter (fun i => r (p i) = i)).card : ℕ) : K) =
        ∑ a, u p a * w r a)
    (hu : ∀ a, ∃ c : Perm (Fin n) → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0)
    (hw : ∀ a, ∃ c : Perm (Fin n) → K, ∀ β, ∑ p, c p * w p β = if β = a then 1 else 0) :
    (∃ (A B : Perm (Fin n) → Fin d → K), ∀ p r,
      ((((Finset.univ : Finset (Fin n)).filter (fun i => r (p i) = i)).card : ℕ) : K) =
        ∑ j : Fin d, A p j * B r j) ↔ Fintype.card ι ≤ d := by
  constructor
  · rintro ⟨A, B, h⟩
    choose c hc using hu
    choose e he using hw
    have hM : (Matrix.of fun (a : ι) (j : Fin d) => ∑ p, c a p * A p j) *
        (Matrix.of fun (j : Fin d) (β : ι) => ∑ r, e β r * B r j) = 1 := by
      ext a β
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [Matrix.of_apply]
      calc ∑ j, (∑ p, c a p * A p j) * (∑ r, e β r * B r j)
          = ∑ p, ∑ r, c a p * e β r * ∑ j, A p j * B r j := by
            simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun p _ => ?_)
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => ?_))
            ring
        _ = ∑ p, ∑ r, c a p * e β r * ∑ g, u p g * w r g := by
            simp_rw [← h, hfix]
        _ = ∑ g, (∑ p, c a p * u p g) * (∑ r, e β r * w r g) := by
            simp_rw [Finset.sum_mul_sum, Finset.mul_sum]
            calc ∑ p, ∑ r, ∑ g, c a p * e β r * (u p g * w r g)
                = ∑ p, ∑ g, ∑ r, c a p * e β r * (u p g * w r g) :=
                  Finset.sum_congr rfl (fun p _ => Finset.sum_comm)
              _ = ∑ g, ∑ p, ∑ r, c a p * e β r * (u p g * w r g) := Finset.sum_comm
              _ = _ := by
                  refine Finset.sum_congr rfl (fun g _ => Finset.sum_congr rfl (fun p _ =>
                    Finset.sum_congr rfl (fun r _ => ?_)))
                  ring
        _ = if a = β then 1 else 0 := by
            simp_rw [hc, he]
            simp [eq_comm]
    exact rank_bound d _ _ hM
  · intro hd
    obtain ⟨A, B, hAB⟩ := pad (K := K) d hd u w
    exact ⟨A, B, fun p r => by rw [hfix, hAB]⟩


theorem toFun {K : Type} [Field K] {P ι : Type} [Fintype P] [DecidableEq ι] (u : P → ι → K) (a : ι)
    (h : (Pi.single a 1 : ι → K) ∈ Submodule.span K (Set.range u)) :
    ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0 := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 h
  refine ⟨c, fun β => ?_⟩
  have := congrFun hc β
  simpa [Finset.sum_apply, Pi.single_apply] using this

theorem transfer {K : Type} [Field K] {P ι : Type} [Fintype P] [DecidableEq ι] (u : P → ι → K)
    (σ : ι ≃ ι) (h : ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p β = if β = a then 1 else 0) :
    ∀ a, ∃ c : P → K, ∀ β, ∑ p, c p * u p (σ β) = if β = a then 1 else 0 := by
  intro a
  obtain ⟨c, hc⟩ := h (σ a)
  exact ⟨c, fun β => by rw [hc]; simp [σ.injective.eq_iff]⟩

def optE (K : Type) [Field K] (X : Type) : (X → K) →ₗ[K] (Option X → K) where
  toFun f o := o.elim 0 f
  map_add' f g := by funext o; cases o <;> simp
  map_smul' c f := by funext o; cases o <;> simp

theorem optE_single {K : Type} [Field K] {X : Type} [DecidableEq X] (x : X) :
    optE K X (Pi.single x 1) = Pi.single (some x) 1 := by
  funext o
  cases o <;> simp [optE, Pi.single_apply]

theorem opt_span {K : Type} [Field K] {X : Type} [Fintype X] [DecidableEq X]
    (Sp : Submodule K (Option X → K)) (h : ∀ x, (Pi.single (some x) 1 : Option X → K) ∈ Sp)
    (v : Option X → K) (hv : v ∈ Sp) (hk : v none ≠ 0) :
    ∀ a, (Pi.single a 1 : Option X → K) ∈ Sp := by
  intro a
  cases a with
  | some x => exact h x
  | none =>
    have e : (Pi.single none 1 : Option X → K) =
        (v none)⁻¹ • (v - ∑ x, v (some x) • (Pi.single (some x) 1 : Option X → K)) := by
      funext o
      cases o with
      | none => simp [Finset.sum_apply, Pi.single_apply, hk]
      | some y => simp [Finset.sum_apply, Pi.single_apply]
    rw [e]
    exact Sp.smul_mem _ (Sp.sub_mem hv (Sp.sum_mem fun x _ => Sp.smul_mem _ (h x)))

/- case one: the characteristic does not divide q -/

def φ1 (K : Type) [Field K] (b : ℕ) (s : Fin (b + 1)) (x : Fin (b + 2)) : K :=
  (if x = s.castSucc then 1 else 0) - (if x = Fin.last (b + 1) then 1 else 0)

def ψ1 (K : Type) [Field K] (b : ℕ) (s : Fin (b + 1)) (y : Fin (b + 2)) : K :=
  if y = s.castSucc then 1 else 0

def α1 (K : Type) [Field K] (b : ℕ) (x : Fin (b + 2)) : K :=
  if x = Fin.last (b + 1) then 1 else 0

def Φ1 (K : Type) [Field K] (b : ℕ) (o : Option (Fin (b + 1))) : Fin (b + 2) → K :=
  o.elim (α1 K b) (φ1 K b)

def Ψ1 (K : Type) [Field K] (b : ℕ) (o : Option (Fin (b + 1))) : Fin (b + 2) → K :=
  o.elim (fun _ => 1) (ψ1 K b)

theorem hδ1 (K : Type) [Field K] (b : ℕ) (x y : Fin (b + 2)) :
    (if x = y then (1 : K) else 0) = ∑ o, Φ1 K b o x * Ψ1 K b o y := by
  rw [Fintype.sum_option]
  simp only [Φ1, Ψ1, Option.elim, φ1, ψ1, α1]
  rcases Fin.eq_castSucc_or_eq_last x with ⟨i, rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last y with ⟨j, rfl⟩ | rfl <;>
    simp [Fin.castSucc_inj, eq_comm]


def Vc1 (K : Type) [Field K] (b : ℕ) (p : Perm (Fin (b + 2))) (z : Fin (b + 1) × Fin (b + 1)) : K :=
  ∑ i, φ1 K b z.1 (p i) * ψ1 K b z.2 i

theorem Vc1_eq (K : Type) [Field K] (b : ℕ) (p : Perm (Fin (b + 2))) (s t : Fin (b + 1)) :
    Vc1 K b p (s, t) = φ1 K b s (p t.castSucc) := by
  simp [Vc1, ψ1]

theorem sumφ1 (K : Type) [Field K] (b : ℕ) (s : Fin (b + 1)) : ∑ x, φ1 K b s x = 0 := by
  simp [φ1, Finset.sum_sub_distrib]

theorem sumφ1p (K : Type) [Field K] (b : ℕ) (s : Fin (b + 1)) (p : Perm (Fin (b + 2))) :
    ∑ i, φ1 K b s (p i) = 0 := by
  rw [Equiv.sum_comp p (φ1 K b s)]
  exact sumφ1 K b s

theorem sumα1p (K : Type) [Field K] (b : ℕ) (p : Perm (Fin (b + 2))) :
    ∑ i, α1 K b (p i) = 1 := by
  rw [Equiv.sum_comp p (α1 K b)]
  simp [α1]

theorem fix1 (K : Type) [Field K] (b : ℕ) (p r : Perm (Fin (b + 2))) :
    ((((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : ℕ) : K) =
      1 + ∑ s, ∑ t, Vc1 K b p (s, t) * Vc1 K b r (t, s) := by
  rw [frame (Φ1 K b) (Ψ1 K b) (hδ1 K b) p r]
  simp only [Fintype.sum_option]
  have b00 : (∑ i, Φ1 K b none (p i) * Ψ1 K b none i) * (∑ j, Ψ1 K b none j * Φ1 K b none (r j))
      = 1 := by
    simp only [Φ1, Ψ1, Option.elim, mul_one, one_mul, sumα1p]
  have b0t : ∀ t, (∑ i, Φ1 K b none (p i) * Ψ1 K b (some t) i) *
      (∑ j, Ψ1 K b none j * Φ1 K b (some t) (r j)) = 0 := by
    intro t
    simp only [Φ1, Ψ1, Option.elim, one_mul, sumφ1p, mul_zero]
  have bs0 : ∀ s, (∑ i, Φ1 K b (some s) (p i) * Ψ1 K b none i) *
      (∑ j, Ψ1 K b (some s) j * Φ1 K b none (r j)) = 0 := by
    intro s
    simp only [Φ1, Ψ1, Option.elim, mul_one, sumφ1p, zero_mul]
  have bst : ∀ s t, (∑ i, Φ1 K b (some s) (p i) * Ψ1 K b (some t) i) *
      (∑ j, Ψ1 K b (some s) j * Φ1 K b (some t) (r j)) = Vc1 K b p (s, t) * Vc1 K b r (t, s) := by
    intro s t
    simp only [Φ1, Ψ1, Option.elim, Vc1]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  simp only [b00, b0t, bs0, bst, Finset.sum_const_zero, add_zero, zero_add]

theorem diff1 (K : Type) [Field K] (b : ℕ) (p : Perm (Fin (b + 2))) (t s' t' : Fin (b + 1)) :
    Vc1 K b p (s', t') - Vc1 K b (p * swap t.castSucc (Fin.last (b + 1))) (s', t') =
      if t' = t then φ1 K b s' (p t.castSucc) - φ1 K b s' (p (Fin.last (b + 1))) else 0 := by
  rw [Vc1_eq, Vc1_eq, Perm.mul_apply]
  by_cases h : t' = t
  · subst h
    simp
  · rw [if_neg h, swap_apply_of_ne_of_ne (by simpa [Fin.castSucc_inj] using h)
      (Fin.castSucc_ne_last t'), sub_self]

theorem core1 (K : Type) [Field K] (b : ℕ) (hn : ((b + 2 : ℕ) : K) ≠ 0) {ι' : Type}
    (F : (Fin (b + 1) × Fin (b + 1) → K) →ₗ[K] (ι' → K)) (u' : Perm (Fin (b + 2)) → ι' → K)
    (hF : ∀ p p', u' p - u' p' = F (fun z => Vc1 K b p z - Vc1 K b p' z))
    (x : Fin (b + 1) × Fin (b + 1)) :
    F (Pi.single x 1) ∈ Submodule.span K (Set.range u') := by
  obtain ⟨s, t⟩ := x
  let g : Fin (b + 2) → (Fin (b + 1) × Fin (b + 1) → K) := fun y z =>
    if z.2 = t then φ1 K b z.1 s.castSucc - φ1 K b z.1 y else 0
  have hg : ∀ y, F (g y) ∈ Submodule.span K (Set.range u') := by
    intro y
    by_cases hy : y = s.castSucc
    · have : g y = 0 := by
        funext z
        simp [g, hy]
      rw [this, map_zero]
      exact Submodule.zero_mem _
    · obtain ⟨p, hp1, hp2⟩ := exists_perm t.castSucc (Fin.last (b + 1)) s.castSucc y
        (Fin.castSucc_ne_last t) (Ne.symm hy)
      have : g y = fun z => Vc1 K b p z - Vc1 K b (p * swap t.castSucc (Fin.last (b + 1))) z := by
        funext z
        obtain ⟨s', t'⟩ := z
        rw [diff1, hp1, hp2]
      rw [this, ← hF]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨p, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hsum : ∑ y, g y = ((b + 2 : ℕ) : K) • (Pi.single (s, t) 1 : Fin (b + 1) × Fin (b + 1) → K) := by
    funext z
    obtain ⟨s', t'⟩ := z
    rw [Finset.sum_apply]
    by_cases ht : t' = t
    · subst ht
      simp only [g, if_pos rfl]
      rw [Finset.sum_sub_distrib, sumφ1, sub_zero, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      by_cases hs : s' = s
      · subst hs
        simp [φ1, Pi.single_apply]
      · have : s.castSucc ≠ s'.castSucc := by simpa [Fin.castSucc_inj] using Ne.symm hs
        simp [φ1, Pi.single_apply, hs, this]
    · simp [g, ht, Pi.single_apply]
  have e : F (Pi.single (s, t) 1) = (((b + 2 : ℕ) : K))⁻¹ • ∑ y, F (g y) := by
    rw [← map_sum, hsum, map_smul, smul_smul, inv_mul_cancel₀ hn, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun y _ => hg y)


/- case two: the characteristic divides q -/

def e2 (b : ℕ) (s : Fin b) : Fin (b + 2) := s.castSucc.castSucc

def A2 (b : ℕ) : Fin (b + 2) := (Fin.last b).castSucc

def φ2 (K : Type) [Field K] (b : ℕ) (s : Fin b) (x : Fin (b + 2)) : K :=
  (if x = e2 b s then 1 else 0) - (if x = Fin.last (b + 1) then 1 else 0)

def ψ2 (K : Type) [Field K] (b : ℕ) (s : Fin b) (y : Fin (b + 2)) : K :=
  (if y = e2 b s then 1 else 0) - (if y = A2 b then 1 else 0)

def α2 (K : Type) [Field K] (b : ℕ) (x : Fin (b + 2)) : K :=
  if x = Fin.last (b + 1) then 1 else 0

def γ2 (K : Type) [Field K] (b : ℕ) (y : Fin (b + 2)) : K :=
  if y = A2 b then 1 else 0

def Φ2 (K : Type) [Field K] (b : ℕ) (o : Option (Option (Fin b))) : Fin (b + 2) → K :=
  o.elim (fun _ => 1) (fun o' => o'.elim (α2 K b) (φ2 K b))

def Ψ2 (K : Type) [Field K] (b : ℕ) (o : Option (Option (Fin b))) : Fin (b + 2) → K :=
  o.elim (γ2 K b) (fun o' => o'.elim (fun _ => 1) (ψ2 K b))

theorem hδ2 (K : Type) [Field K] (b : ℕ) (hn0 : ((b + 2 : ℕ) : K) = 0) (x y : Fin (b + 2)) :
    (if x = y then (1 : K) else 0) = ∑ o, Φ2 K b o x * Ψ2 K b o y := by
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only [Φ2, Ψ2, Option.elim, φ2, ψ2, α2, γ2, e2, A2]
  have l1 : ∀ z : Fin (b + 1), ¬ (Fin.last (b + 1) = z.castSucc) :=
    fun z h => Fin.castSucc_ne_last z h.symm
  have l2 : ∀ z : Fin b, ¬ (Fin.last b = z.castSucc) := fun z h => Fin.castSucc_ne_last z h.symm
  rcases Fin.eq_castSucc_or_eq_last x with ⟨x', rfl⟩ | rfl <;>
    rcases Fin.eq_castSucc_or_eq_last y with ⟨y', rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last x' with ⟨i, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last y' with ⟨j, rfl⟩ | rfl <;>
      simp [Fin.castSucc_inj, eq_comm, l1, l2]
  · rcases Fin.eq_castSucc_or_eq_last x' with ⟨i, rfl⟩ | rfl <;> simp [l1, l2]
  · rcases Fin.eq_castSucc_or_eq_last y' with ⟨j, rfl⟩ | rfl
    · simp [l1, l2]
    · simp [l1, l2]
      push_cast at hn0
      linear_combination (-1 : K) * hn0
  · simp [l1, l2]


theorem e2_inj (b : ℕ) (s t : Fin b) : e2 b s = e2 b t ↔ s = t := by
  simp [e2, Fin.castSucc_inj]

theorem e2_ne_last (b : ℕ) (s : Fin b) : ¬ (e2 b s = Fin.last (b + 1)) := Fin.castSucc_ne_last _

theorem A2_ne_last (b : ℕ) : ¬ (A2 b = Fin.last (b + 1)) := Fin.castSucc_ne_last _

theorem A2_ne_e2 (b : ℕ) (s : Fin b) : ¬ (A2 b = e2 b s) := by
  intro h
  simp only [A2, e2, Fin.castSucc_inj] at h
  exact Fin.castSucc_ne_last s h.symm

def Vc2 (K : Type) [Field K] (b : ℕ) (p : Perm (Fin (b + 2))) (z : Fin b × Fin b) : K :=
  ∑ i, φ2 K b z.1 (p i) * ψ2 K b z.2 i

theorem Vc2_eq (K : Type) [Field K] (b : ℕ) (p : Perm (Fin (b + 2))) (s t : Fin b) :
    Vc2 K b p (s, t) = φ2 K b s (p (e2 b t)) - φ2 K b s (p (A2 b)) := by
  simp [Vc2, ψ2, mul_sub, Finset.sum_sub_distrib]

theorem sumφ2p (K : Type) [Field K] (b : ℕ) (s : Fin b) (p : Perm (Fin (b + 2))) :
    ∑ i, φ2 K b s (p i) = 0 := by
  rw [Equiv.sum_comp p (φ2 K b s)]
  simp [φ2, Finset.sum_sub_distrib]

theorem sumψ2 (K : Type) [Field K] (b : ℕ) (s : Fin b) : ∑ i, ψ2 K b s i = 0 := by
  simp [ψ2, Finset.sum_sub_distrib]

theorem fix2 (K : Type) [Field K] (b : ℕ) (hn0 : ((b + 2 : ℕ) : K) = 0) (p r : Perm (Fin (b + 2))) :
    ((((Finset.univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : ℕ) : K) =
      2 + ∑ s, ∑ t, Vc2 K b p (s, t) * Vc2 K b r (t, s) := by
  rw [frame (Φ2 K b) (Ψ2 K b) (hδ2 K b hn0) p r]
  simp only [Fintype.sum_option]
  have hN : ∑ _i : Fin (b + 2), (1 : K) * 1 = 0 := by simpa using hn0
  have hγ : ∑ i, γ2 K b i = 1 := by simp [γ2]
  have hα : ∀ q : Perm (Fin (b + 2)), ∑ i, α2 K b (q i) = 1 := by
    intro q
    rw [Equiv.sum_comp q (α2 K b)]
    simp [α2]
  have bcc : (∑ i, Φ2 K b none (p i) * Ψ2 K b none i) * (∑ j, Ψ2 K b none j * Φ2 K b none (r j))
      = 1 := by
    simp only [Φ2, Ψ2, Option.elim, one_mul, mul_one, hγ]
  have bca : (∑ i, Φ2 K b none (p i) * Ψ2 K b (some none) i) *
      (∑ j, Ψ2 K b none j * Φ2 K b (some none) (r j)) = 0 := by
    simp only [Φ2, Ψ2, Option.elim, hN, zero_mul]
  have bct : ∀ t, (∑ i, Φ2 K b none (p i) * Ψ2 K b (some (some t)) i) *
      (∑ j, Ψ2 K b none j * Φ2 K b (some (some t)) (r j)) = 0 := by
    intro t
    simp only [Φ2, Ψ2, Option.elim, one_mul, sumψ2, zero_mul]
  have bac : (∑ i, Φ2 K b (some none) (p i) * Ψ2 K b none i) *
      (∑ j, Ψ2 K b (some none) j * Φ2 K b none (r j)) = 0 := by
    simp only [Φ2, Ψ2, Option.elim, hN, mul_zero]
  have baa : (∑ i, Φ2 K b (some none) (p i) * Ψ2 K b (some none) i) *
      (∑ j, Ψ2 K b (some none) j * Φ2 K b (some none) (r j)) = 1 := by
    simp only [Φ2, Ψ2, Option.elim, one_mul, mul_one, hα]
  have bat : ∀ t, (∑ i, Φ2 K b (some none) (p i) * Ψ2 K b (some (some t)) i) *
      (∑ j, Ψ2 K b (some none) j * Φ2 K b (some (some t)) (r j)) = 0 := by
    intro t
    simp only [Φ2, Ψ2, Option.elim, one_mul, sumφ2p, mul_zero]
  have bsc : ∀ s, (∑ i, Φ2 K b (some (some s)) (p i) * Ψ2 K b none i) *
      (∑ j, Ψ2 K b (some (some s)) j * Φ2 K b none (r j)) = 0 := by
    intro s
    simp only [Φ2, Ψ2, Option.elim, mul_one, sumψ2, mul_zero]
  have bsa : ∀ s, (∑ i, Φ2 K b (some (some s)) (p i) * Ψ2 K b (some none) i) *
      (∑ j, Ψ2 K b (some (some s)) j * Φ2 K b (some none) (r j)) = 0 := by
    intro s
    simp only [Φ2, Ψ2, Option.elim, mul_one, sumφ2p, zero_mul]
  have bst : ∀ s t, (∑ i, Φ2 K b (some (some s)) (p i) * Ψ2 K b (some (some t)) i) *
      (∑ j, Ψ2 K b (some (some s)) j * Φ2 K b (some (some t)) (r j)) =
        Vc2 K b p (s, t) * Vc2 K b r (t, s) := by
    intro s t
    simp only [Φ2, Ψ2, Option.elim, Vc2]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  simp only [bcc, bca, bct, bac, baa, bat, bsc, bsa, bst, Finset.sum_const_zero, add_zero,
    zero_add]
  ring

theorem diff2 (K : Type) [Field K] (b : ℕ) (p : Perm (Fin (b + 2))) (t s' t' : Fin b) :
    Vc2 K b p (s', t') - Vc2 K b (p * swap (e2 b t) (Fin.last (b + 1))) (s', t') =
      if t' = t then φ2 K b s' (p (e2 b t)) - φ2 K b s' (p (Fin.last (b + 1))) else 0 := by
  rw [Vc2_eq, Vc2_eq, Perm.mul_apply, Perm.mul_apply,
    swap_apply_of_ne_of_ne (A2_ne_e2 b t) (A2_ne_last b)]
  by_cases h : t' = t
  · subst h
    simp
  · rw [if_neg h, swap_apply_of_ne_of_ne (by simpa [e2_inj] using h) (e2_ne_last b t')]
    ring

theorem core2 (K : Type) [Field K] (b : ℕ) {ι' : Type}
    (F : (Fin b × Fin b → K) →ₗ[K] (ι' → K)) (u' : Perm (Fin (b + 2)) → ι' → K)
    (hF : ∀ p p', u' p - u' p' = F (fun z => Vc2 K b p z - Vc2 K b p' z))
    (x : Fin b × Fin b) :
    F (Pi.single x 1) ∈ Submodule.span K (Set.range u') := by
  obtain ⟨s, t⟩ := x
  obtain ⟨p, hp1, hp2⟩ := exists_perm (e2 b t) (Fin.last (b + 1)) (e2 b s) (A2 b)
    (e2_ne_last b t) (fun h => A2_ne_e2 b s h.symm)
  have : (Pi.single (s, t) 1 : Fin b × Fin b → K) =
      fun z => Vc2 K b p z - Vc2 K b (p * swap (e2 b t) (Fin.last (b + 1))) z := by
    funext z
    obtain ⟨s', t'⟩ := z
    rw [diff2, hp1, hp2]
    by_cases ht : t' = t
    · subst ht
      by_cases hs : s' = s
      · subst hs
        simp [φ2, e2_ne_last, A2_ne_e2, A2_ne_last]
      · have : ¬ (e2 b s = e2 b s') := by simpa [e2_inj] using Ne.symm hs
        simp [φ2, hs, this, e2_ne_last, A2_ne_e2, A2_ne_last]
    · simp [ht]
  rw [this, ← hF]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨p, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)


theorem finishOpt {K : Type} [Field K] {n : ℕ} {X : Type} [Fintype X] [DecidableEq X] (d : ℕ)
    (Vc : Perm (Fin n) → X → K) (τ : X ≃ X) (κ1 κ2 : K) (h1 : κ1 ≠ 0) (h2 : κ2 ≠ 0)
    (hfix : ∀ p r : Perm (Fin n),
      ((((Finset.univ : Finset (Fin n)).filter (fun i => r (p i) = i)).card : ℕ) : K) =
        κ1 * κ2 + ∑ x, Vc p x * Vc r (τ x))
    (hcore : ∀ u' : Perm (Fin n) → Option X → K,
      (∀ p p', u' p - u' p' = optE K X (fun z => Vc p z - Vc p' z)) →
        ∀ x, optE K X (Pi.single x 1) ∈ Submodule.span K (Set.range u')) :
    (∃ (A B : Perm (Fin n) → Fin d → K), ∀ p r,
      ((((Finset.univ : Finset (Fin n)).filter (fun i => r (p i) = i)).card : ℕ) : K) =
        ∑ j : Fin d, A p j * B r j) ↔ Fintype.card X + 1 ≤ d := by
  let U : K → Perm (Fin n) → Option X → K := fun κ p o => o.elim κ (Vc p)
  let σ : Option X ≃ Option X := Equiv.optionCongr τ
  have hdiff : ∀ κ p p', U κ p - U κ p' = optE K X (fun z => Vc p z - Vc p' z) := by
    intro κ p p'
    funext o
    cases o <;> simp [U, optE]
  have hspan : ∀ κ, κ ≠ 0 → ∀ a, ∃ c : Perm (Fin n) → K, ∀ β,
      ∑ p, c p * U κ p β = if β = a then 1 else 0 := by
    intro κ hκ a
    apply toFun
    refine opt_span (Submodule.span K (Set.range (U κ))) (fun x => ?_) (U κ 1)
      (Submodule.subset_span (Set.mem_range_self 1)) hκ a
    rw [← optE_single]
    exact hcore (U κ) (hdiff κ) x
  have key := main_iff d (U κ1) (fun r o => U κ2 r (σ o)) (fun p r => by
      rw [hfix, Fintype.sum_option]
      simp [U, σ]) (hspan κ1 h1) (transfer (U κ2) σ (hspan κ2 h2))
  rw [key, Fintype.card_option]

theorem finishPlain {K : Type} [Field K] {n : ℕ} {X : Type} [Fintype X] [DecidableEq X] (d : ℕ)
    (Vc : Perm (Fin n) → X → K) (τ : X ≃ X)
    (hfix : ∀ p r : Perm (Fin n),
      ((((Finset.univ : Finset (Fin n)).filter (fun i => r (p i) = i)).card : ℕ) : K) =
        ∑ x, Vc p x * Vc r (τ x))
    (hcore : ∀ x, (Pi.single x 1 : X → K) ∈ Submodule.span K (Set.range Vc)) :
    (∃ (A B : Perm (Fin n) → Fin d → K), ∀ p r,
      ((((Finset.univ : Finset (Fin n)).filter (fun i => r (p i) = i)).card : ℕ) : K) =
        ∑ j : Fin d, A p j * B r j) ↔ Fintype.card X ≤ d :=
  main_iff d Vc (fun r x => Vc r (τ x)) hfix (fun a => toFun Vc a (hcore a))
    (transfer Vc τ (fun a => toFun Vc a (hcore a)))

end PEqualNP.Outside.L_lib_591

open PEqualNP.Outside.L_lib_591 in
theorem PEqualNP.Outside.L_lib_591 : ∀ (K : Type) [Field K] (b d : ℕ),
  let q := b + 2
  let P := Equiv.Perm (Fin q)
  let fixed := fun (p r : P) =>
    ((Finset.univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card
  let threshold := if ringChar K ∣ q then
      (q - 2) ^ 2 + (if ringChar K = 2 then 0 else 1)
    else (q - 1) ^ 2 + 1
  (∃ (A B : P → Fin d → K),
    ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
    threshold ≤ d := by
  intro K _ b d
  dsimp only
  by_cases hdiv : ringChar K ∣ b + 2
  · have hn0 : ((b + 2 : ℕ) : K) = 0 := (CharP.cast_eq_zero_iff K (ringChar K) (b + 2)).2 hdiv
    rw [if_pos hdiv, Nat.add_sub_cancel]
    by_cases h2 : ringChar K = 2
    · have h20 : (2 : K) = 0 := (CharP.cast_eq_zero_iff K (ringChar K) 2).2 (by rw [h2])
      rw [if_pos h2, add_zero]
      have key := finishPlain d (Vc2 K b) (Equiv.prodComm (Fin b) (Fin b))
        (fun p r => by
          rw [fix2 K b hn0, h20, zero_add, Fintype.sum_prod_type]
          rfl)
        (fun x => by
          have := core2 K b LinearMap.id (Vc2 K b) (fun p p' => rfl) x
          simpa using this)
      rw [key, Fintype.card_prod, Fintype.card_fin, sq]
    · rw [if_neg h2]
      have key := finishOpt d (Vc2 K b) (Equiv.prodComm (Fin b) (Fin b)) 1 2 one_ne_zero
        (Ring.two_ne_zero h2)
        (fun p r => by
          rw [fix2 K b hn0, one_mul, Fintype.sum_prod_type]
          rfl)
        (fun u' hu' x => core2 K b (optE K _) u' hu' x)
      rw [key, Fintype.card_prod, Fintype.card_fin, sq]
  · have hn : ((b + 2 : ℕ) : K) ≠ 0 := fun h =>
      hdiv ((CharP.cast_eq_zero_iff K (ringChar K) (b + 2)).1 h)
    rw [if_neg hdiv, show b + 2 - 1 = b + 1 by omega]
    have key := finishOpt d (Vc1 K b) (Equiv.prodComm (Fin (b + 1)) (Fin (b + 1))) 1 1
      one_ne_zero one_ne_zero
      (fun p r => by
        rw [fix1 K b, one_mul, Fintype.sum_prod_type]
        rfl)
      (fun u' hu' x => core1 K b hn (optE K _) u' hu' x)
    rw [key, Fintype.card_prod, Fintype.card_fin, sq]
