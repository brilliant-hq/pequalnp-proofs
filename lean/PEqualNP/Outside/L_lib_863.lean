import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_863_aux

open scoped BigOperators

abbrev F := ZMod 2

private lemma zmod2_cases (a : F) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> decide

private lemma zmod2_vec_add_self {n : ℕ} (v : Fin n → F) : v + v = 0 := by
  funext i
  exact zmod2_add_self (v i)

private lemma zmod2_add_cancel_left (a b : F) : a + (a + b) = b := by
  rw [← add_assoc, zmod2_add_self, zero_add]

private def chi (a : F) : ℤ := if a = 0 then 1 else -1

private lemma chi_zero : chi 0 = 1 := rfl

private lemma chi_one : chi 1 = -1 := rfl

private lemma chi_add (a b : F) : chi (a + b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> decide

private lemma chi_eq_ite (a b : F) : (if a = b then (1 : ℤ) else -1) = chi (a + b) := by
  fin_cases a <;> fin_cases b <;> decide

private lemma chi_le_one (a : F) : chi a ≤ 1 := by
  fin_cases a <;> decide

private lemma chi_sum_pair : ∑ x : F, ∑ y : F, chi (x * y) = 2 := by
  decide

private lemma sum_chi_dot {n : ℕ} (z : Fin n → F) :
    (∑ u : Fin n → F, chi (dotProduct u z)) = if z = 0 then (2 : ℤ) ^ n else 0 := by
  by_cases hz : z = 0
  · subst hz
    simp only [↓reduceIte, dotProduct_zero, chi_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_pi, Fintype.card_fin, ZMod.card, Finset.prod_const, nsmul_eq_mul, mul_one]
    norm_cast
  · simp only [hz, ↓reduceIte]
    have hex : ∃ i : Fin n, z i ≠ 0 := by
      by_contra h
      push Not at h
      exact hz (funext h)
    obtain ⟨i, hi⟩ := hex
    have hzi : z i = 1 := by
      rcases zmod2_cases (z i) with h0 | h1
      · exact absurd h0 hi
      · exact h1
    let e : Fin n → F := Pi.single i (1 : F)
    have hdez : dotProduct e z = 1 := by
      simp [e, dotProduct, Pi.single_apply, hzi]
    have hS : (∑ u : Fin n → F, chi (dotProduct u z)) =
        -(∑ u : Fin n → F, chi (dotProduct u z)) := by
      have hbij : (∑ u : Fin n → F, chi (dotProduct u z)) =
          ∑ u : Fin n → F, chi (dotProduct (u + e) z) :=
        (Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)).symm
      conv_lhs => rw [hbij]
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [add_dotProduct, hdez, chi_add, chi_one, mul_neg_one]
    omega

private def IsQuad {n : ℕ} (q : (Fin n → F) → F) : Prop :=
  ∃ (b : F) (a : Fin n → F) (M : Fin n → Fin n → F), ∀ v,
    q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j

private lemma isQuad_zero {n : ℕ} : IsQuad (fun _ : Fin n → F => (0 : F)) := by
  refine ⟨0, 0, fun _ _ => 0, fun v => ?_⟩
  simp

private lemma isQuad_add {n : ℕ} {q₁ q₂ : (Fin n → F) → F} (h₁ : IsQuad q₁) (h₂ : IsQuad q₂) :
    IsQuad (fun v => q₁ v + q₂ v) := by
  obtain ⟨b₁, a₁, M₁, hq₁⟩ := h₁
  obtain ⟨b₂, a₂, M₂, hq₂⟩ := h₂
  refine ⟨b₁ + b₂, a₁ + a₂, fun i j => M₁ i j + M₂ i j, fun v => ?_⟩
  dsimp only
  rw [hq₁ v, hq₂ v, add_dotProduct]
  have hsum : (∑ i : Fin n, ∑ j : Fin n, (M₁ i j + M₂ i j) * v i * v j) =
      (∑ i : Fin n, ∑ j : Fin n, M₁ i j * v i * v j) +
      (∑ i : Fin n, ∑ j : Fin n, M₂ i j * v i * v j) := by
    simp only [add_mul, Finset.sum_add_distrib]
  rw [hsum]
  ring

private lemma isQuad_affine {n : ℕ} (a : Fin n → F) (b : F) :
    IsQuad (fun v : Fin n → F => dotProduct a v + b) := by
  refine ⟨b, a, fun _ _ => 0, fun v => ?_⟩
  simp [add_comm]

private lemma isQuad_mul_dot {n : ℕ} (α β : Fin n → F) :
    IsQuad (fun v : Fin n → F => dotProduct α v * dotProduct β v) := by
  refine ⟨0, 0, fun i j => α i * β j, fun v => ?_⟩
  dsimp only
  rw [zero_dotProduct, zero_add, zero_add]
  simp only [dotProduct]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma isQuad_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → (Fin n → F) → F) (hf : ∀ t ∈ s, IsQuad (f t)) :
    IsQuad (fun v => ∑ t ∈ s, f t v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using isQuad_zero (n := n)
  | insert a s ha ih =>
    have h1 : IsQuad (f a) := hf a (Finset.mem_insert_self a s)
    have h2 : IsQuad (fun v => ∑ t ∈ s, f t v) :=
      ih (fun t ht => hf t (Finset.mem_insert_of_mem ht))
    simpa [Finset.sum_insert ha] using isQuad_add h1 h2

private def IsAlt {n : ℕ} (P : Matrix (Fin n) (Fin n) F) : Prop :=
  (∀ i, P i i = 0) ∧ (∀ i j, P i j = P j i)

private lemma exists_polar_of_isQuad {n : ℕ} {q : (Fin n → F) → F} (hq : IsQuad q) :
    ∃ P : Matrix (Fin n) (Fin n) F, IsAlt P ∧
      ∀ u v, q (u + v) + q u + q v + q 0 = dotProduct u (P.mulVec v) := by
  obtain ⟨b, a, A, hq⟩ := hq
  refine ⟨Matrix.of (fun i j => A i j + A j i), ⟨?_, ?_⟩, ?_⟩
  · intro i
    exact zmod2_add_self (A i i)
  · intro i j
    simp [Matrix.of_apply, add_comm]
  · intro u v
    rw [hq (u + v), hq u, hq v, hq 0]
    simp only [Pi.zero_apply, Pi.add_apply, dotProduct_zero, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [dotProduct_add]
    have hlin : (b + (dotProduct a u + dotProduct a v) +
        ∑ i, ∑ j, A i j * (u i + v i) * (u j + v j)) +
        (b + dotProduct a u + ∑ i, ∑ j, A i j * u i * u j) +
        (b + dotProduct a v + ∑ i, ∑ j, A i j * v i * v j) + b =
        (∑ i, ∑ j, A i j * (u i + v i) * (u j + v j)) +
        (∑ i, ∑ j, A i j * u i * u j) +
        (∑ i, ∑ j, A i j * v i * v j) := by
      have hb : b + b = 0 := zmod2_add_self b
      have hu : dotProduct a u + dotProduct a u = 0 := zmod2_add_self _
      have hv : dotProduct a v + dotProduct a v = 0 := zmod2_add_self _
      calc _ = (b + b) + (b + b) + (dotProduct a u + dotProduct a u) +
               (dotProduct a v + dotProduct a v) +
               ((∑ i, ∑ j, A i j * (u i + v i) * (u j + v j)) +
                (∑ i, ∑ j, A i j * u i * u j) +
                (∑ i, ∑ j, A i j * v i * v j)) := by ring
        _ = _ := by rw [hb, hu, hv]; simp
    rw [hlin]
    have hquad : (∑ i, ∑ j, A i j * (u i + v i) * (u j + v j)) +
        (∑ i, ∑ j, A i j * u i * u j) +
        (∑ i, ∑ j, A i j * v i * v j) =
        ∑ i, ∑ j, (A i j * u i * v j + A i j * v i * u j) := by
      simp only [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      have h1 : A i j * u i * u j + A i j * u i * u j = 0 := zmod2_add_self _
      have h2 : A i j * v i * v j + A i j * v i * v j = 0 := zmod2_add_self _
      calc A i j * (u i + v i) * (u j + v j) + A i j * u i * u j + A i j * v i * v j
          = (A i j * u i * u j + A i j * u i * u j) +
            (A i j * v i * v j + A i j * v i * v j) +
            (A i j * u i * v j + A i j * v i * u j) := by ring
        _ = A i j * u i * v j + A i j * v i * u j := by rw [h1, h2]; simp
    rw [hquad]
    simp only [Finset.sum_add_distrib]
    have hswap : (∑ i : Fin n, ∑ j : Fin n, A i j * v i * u j) =
        ∑ i : Fin n, ∑ j : Fin n, A j i * u i * v j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hswap, ← Finset.sum_add_distrib]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

private lemma dot_single_mulVec_single {n : ℕ} (P : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    dotProduct (Pi.single i (1 : F)) (P.mulVec (Pi.single j (1 : F))) = P i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

private lemma matrix_eq_of_dot_mulVec {n : ℕ} {P₁ P₂ : Matrix (Fin n) (Fin n) F}
    (h : ∀ u v, dotProduct u (P₁.mulVec v) = dotProduct u (P₂.mulVec v)) : P₁ = P₂ := by
  ext i j
  have h' := h (Pi.single i (1 : F)) (Pi.single j (1 : F))
  simpa [dot_single_mulVec_single] using h'

private lemma isAlt_of_polar {n : ℕ} {d : (Fin n → F) → F} {M : Matrix (Fin n) (Fin n) F}
    (hM : ∀ u v, d (u + v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) : IsAlt M := by
  refine ⟨?_, ?_⟩
  · intro i
    let ei : Fin n → F := Pi.single i (1 : F)
    have h := hM ei ei
    rw [dot_single_mulVec_single, zmod2_vec_add_self] at h
    rw [← h]
    have h1 := zmod2_add_self (d 0)
    have h2 := zmod2_add_self (d ei)
    calc d 0 + d ei + d ei + d 0
        = (d 0 + d 0) + (d ei + d ei) := by ring
      _ = 0 := by rw [h1, h2]; simp
  · intro i j
    let ei : Fin n → F := Pi.single i (1 : F)
    let ej : Fin n → F := Pi.single j (1 : F)
    have h1 := hM ei ej
    have h2 := hM ej ei
    rw [dot_single_mulVec_single] at h1 h2
    rw [← h1, ← h2, add_comm ei ej]
    ring

private lemma bilinear_symm {n : ℕ} {P : Matrix (Fin n) (Fin n) F} (hP : IsAlt P)
    (u v : Fin n → F) :
    dotProduct u (P.mulVec v) = dotProduct v (P.mulVec u) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hP.2 j i]
  ring

private lemma bilinear_alt_self {n : ℕ} {P : Matrix (Fin n) (Fin n) F} (hP : IsAlt P)
    (u : Fin n → F) :
    dotProduct u (P.mulVec u) = 0 := by
  have hgen : ∀ s : Finset (Fin n), ∑ i ∈ s, ∑ j ∈ s, u i * (P i j * u j) = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      have hdiag : u a * (P a a * u a) = 0 := by rw [hP.1 a]; simp
      have hpair : (∑ j ∈ s, u a * (P a j * u j)) + (∑ i ∈ s, u i * (P i a * u a)) = 0 := by
        have heq : (∑ i ∈ s, u i * (P i a * u a)) = ∑ j ∈ s, u a * (P a j * u j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hP.2 j a]
          ring
        rw [heq]
        exact zmod2_add_self _
      calc u a * (P a a * u a) + (∑ j ∈ s, u a * (P a j * u j)) +
            ∑ i ∈ s, (u i * (P i a * u a) + ∑ j ∈ s, u i * (P i j * u j))
          = u a * (P a a * u a) +
            ((∑ j ∈ s, u a * (P a j * u j)) + (∑ i ∈ s, u i * (P i a * u a))) +
            ∑ i ∈ s, ∑ j ∈ s, u i * (P i j * u j) := by
              rw [Finset.sum_add_distrib]; ring
        _ = 0 := by rw [hdiag, hpair, ih]; simp
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum] using hgen Finset.univ

private lemma sum_dotProduct_aux {n : ℕ} {ι : Type*} (s : Finset ι)
    (g : ι → (Fin n → F)) (v : Fin n → F) :
    dotProduct (∑ t ∈ s, g t) v = ∑ t ∈ s, dotProduct (g t) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_dotProduct, ih]

private lemma rank_add_le_aux {n : ℕ} (P₀ P₁ : Matrix (Fin n) (Fin n) F) :
    (P₀ + P₁).rank ≤ P₀.rank + P₁.rank := by
  unfold Matrix.rank
  have hsub : LinearMap.range (P₀ + P₁).mulVecLin ≤
      LinearMap.range P₀.mulVecLin ⊔ LinearMap.range P₁.mulVecLin := by
    rintro _ ⟨v, rfl⟩
    have hadd : (P₀ + P₁).mulVecLin v = P₀.mulVecLin v + P₁.mulVecLin v :=
      Matrix.add_mulVec P₀ P₁ v
    rw [hadd]
    exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
  calc Module.finrank F (LinearMap.range (P₀ + P₁).mulVecLin)
      ≤ Module.finrank F (LinearMap.range P₀.mulVecLin ⊔ LinearMap.range P₁.mulVecLin :
          Submodule F (Fin n → F)) := Submodule.finrank_mono hsub
    _ ≤ Module.finrank F (LinearMap.range P₀.mulVecLin) +
        Module.finrank F (LinearMap.range P₁.mulVecLin) := by
          have h := Submodule.finrank_sup_add_finrank_inf_eq
            (LinearMap.range P₀.mulVecLin) (LinearMap.range P₁.mulVecLin)
          omega

open Classical in
private lemma card_submodule_zmod2 {n : ℕ} (W : Submodule F (Fin n → F)) :
    Fintype.card W = 2 ^ Module.finrank F W := by
  have h := Module.card_eq_pow_finrank (K := F) (V := W)
  simpa [ZMod.card] using h

open Classical in
private lemma card_ker_mulVecLin {n : ℕ} (P : Matrix (Fin n) (Fin n) F) :
    Fintype.card (LinearMap.ker P.mulVecLin) = 2 ^ (n - P.rank) ∧ P.rank ≤ n := by
  have hrn := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  have hdim : Module.finrank F (Fin n → F) = n := by simp
  rw [hdim] at hrn
  have hrle : P.rank ≤ n := by
    unfold Matrix.rank
    omega
  have hker : Module.finrank F (LinearMap.ker P.mulVecLin) = n - P.rank := by
    unfold Matrix.rank at hrle ⊢
    omega
  refine ⟨?_, hrle⟩
  rw [card_submodule_zmod2, hker]

private lemma walsh_sq_bound {n : ℕ} (f : (Fin n → F) → F) (P : Matrix (Fin n) (Fin n) F)
    (hf : ∀ u v, f (u + v) + f u + f v + f 0 = dotProduct u (P.mulVec v)) :
    2 ^ P.rank * (∑ u : Fin n → F, chi (f u)).natAbs ^ 2 ≤ (2 ^ n) ^ 2 := by
  classical
  let S : ℤ := ∑ u : Fin n → F, chi (f u)
  have hS2 : S * S = (2 : ℤ) ^ n *
      ∑ v ∈ (Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0),
        chi (f v + f 0) := by
    calc S * S
        = ∑ u : Fin n → F, ∑ w : Fin n → F, chi (f w) * chi (f u) := by
            simp only [S, Finset.sum_mul, Finset.mul_sum]
      _ = ∑ u : Fin n → F, ∑ v : Fin n → F, chi (f (u + v) + f u) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            exact (Fintype.sum_equiv (Equiv.addLeft u)
              (fun v => chi (f (u + v) + f u)) (fun w => chi (f w) * chi (f u))
              (fun v => by simp [chi_add])).symm
      _ = ∑ v : Fin n → F, ∑ u : Fin n → F, chi (f (u + v) + f u) := Finset.sum_comm
      _ = ∑ v : Fin n → F, chi (f v + f 0) * ∑ u : Fin n → F, chi (dotProduct u (P.mulVec v)) := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun u _ => ?_
            have hrel : f (u + v) + f u = (f v + f 0) + dotProduct u (P.mulVec v) := by
              rw [← hf u v]
              have h1 := zmod2_add_self (f v)
              have h2 := zmod2_add_self (f 0)
              calc f (u + v) + f u
                  = f (u + v) + f u + (f v + f v) + (f 0 + f 0) := by rw [h1, h2]; simp
                _ = f v + f 0 + (f (u + v) + f u + f v + f 0) := by ring
            rw [hrel, chi_add]
      _ = ∑ v : Fin n → F,
            if P.mulVec v = 0 then (2 : ℤ) ^ n * chi (f v + f 0) else 0 := by
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [sum_chi_dot]
            split_ifs <;> ring
      _ = (2 : ℤ) ^ n *
            ∑ v ∈ (Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0),
              chi (f v + f 0) := by
            rw [Finset.mul_sum, Finset.sum_filter]
  have hsum_le : (∑ v ∈ (Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0),
      chi (f v + f 0)) ≤
      (((Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0)).card : ℤ) := by
    calc _ ≤ ∑ _v ∈ (Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0), (1 : ℤ) :=
          Finset.sum_le_sum fun v _ => chi_le_one _
      _ = _ := by simp
  have hcard_eq : ((Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0)).card =
      Fintype.card (LinearMap.ker P.mulVecLin) := by
    rw [Fintype.card_subtype]
    congr 1
    ext v
    simp [LinearMap.mem_ker]
  obtain ⟨hker_card, hrle⟩ := card_ker_mulVecLin P
  have hS2_le_int : (S.natAbs : ℤ) ^ 2 ≤ (2 : ℤ) ^ n * (2 : ℤ) ^ (n - P.rank) := by
    have hsq : (S.natAbs : ℤ) ^ 2 = S * S := by
      rw [sq, ← Nat.cast_mul, Int.natAbs_mul_self]
    rw [hsq, hS2]
    have h2pos : (0 : ℤ) ≤ (2 : ℤ) ^ n := by positivity
    calc (2 : ℤ) ^ n * ∑ v ∈ (Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0),
          chi (f v + f 0)
        ≤ (2 : ℤ) ^ n *
          (((Finset.univ : Finset (Fin n → F)).filter (fun v => P.mulVec v = 0)).card : ℤ) :=
            mul_le_mul_of_nonneg_left hsum_le h2pos
      _ = (2 : ℤ) ^ n * (2 : ℤ) ^ (n - P.rank) := by
            rw [hcard_eq, hker_card]
            push_cast
            rfl
  have hS2_le : S.natAbs ^ 2 ≤ 2 ^ n * 2 ^ (n - P.rank) := by
    exact_mod_cast hS2_le_int
  calc 2 ^ P.rank * S.natAbs ^ 2
      ≤ 2 ^ P.rank * (2 ^ n * 2 ^ (n - P.rank)) := Nat.mul_le_mul_left _ hS2_le
    _ = 2 ^ n * (2 ^ P.rank * 2 ^ (n - P.rank)) := by ring
    _ = 2 ^ n * 2 ^ n := by rw [← pow_add, Nat.add_sub_of_le hrle]
    _ = (2 ^ n) ^ 2 := by ring

private def rad {n : ℕ} (P : Matrix (Fin n) (Fin n) F) (W : Submodule F (Fin n → F)) :
    Submodule F (Fin n → F) :=
  { carrier := {w | w ∈ W ∧ ∀ y ∈ W, dotProduct w (P.mulVec y) = 0}
    zero_mem' := ⟨W.zero_mem, fun y _ => by simp⟩, add_mem' := by
      rintro a b ⟨haW, ha⟩ ⟨hbW, hb⟩
      refine ⟨W.add_mem haW hbW, fun y hy => ?_⟩
      rw [add_dotProduct, ha y hy, hb y hy, add_zero]
    smul_mem' := by
      rintro c a ⟨haW, ha⟩
      refine ⟨W.smul_mem c haW, fun y hy => ?_⟩
      rw [smul_dotProduct, ha y hy, smul_zero] }

private lemma exists_symplectic_on {n : ℕ} (P : Matrix (Fin n) (Fin n) F) (hP : IsAlt P) :
    ∀ (d : ℕ) (W : Submodule F (Fin n → F)), Module.finrank F W = d →
      ∃ (k : ℕ) (e f : Fin k → (Fin n → F)),
        Module.finrank F W = 2 * k + Module.finrank F (rad P W) ∧
        (∀ t, e t ∈ W ∧ f t ∈ W) ∧
        (∀ s t, dotProduct (e s) (P.mulVec (e t)) = 0) ∧
        (∀ s t, dotProduct (f s) (P.mulVec (f t)) = 0) ∧
        (∀ s t, dotProduct (e s) (P.mulVec (f t)) = if s = t then 1 else 0) ∧
        (∀ u ∈ W, u + ∑ t : Fin k, (dotProduct u (P.mulVec (f t)) • e t +
                                    dotProduct u (P.mulVec (e t)) • f t) ∈ rad P W) := by
  intro d
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro W hdim
    by_cases hall : ∀ x ∈ W, ∀ y ∈ W, dotProduct x (P.mulVec y) = 0
    · refine ⟨0, Fin.elim0, Fin.elim0, ?_, fun t => t.elim0, fun s => s.elim0,
        fun s => s.elim0, fun s => s.elim0, ?_⟩
      · have hradW : rad P W = W := by
          ext w
          simp only [rad, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
            Set.mem_ofPred_eq]
          exact ⟨fun h => h.1, fun hw => ⟨hw, hall w hw⟩⟩
        rw [hradW]
        simp
      · intro u hu
        simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
        exact ⟨hu, hall u hu⟩
    · push Not at hall
      obtain ⟨x, hxW, y, hyW, hxy_ne⟩ := hall
      have hxy : dotProduct x (P.mulVec y) = 1 := by
        rcases zmod2_cases (dotProduct x (P.mulVec y)) with h0 | h1
        · exact absurd h0 hxy_ne
        · exact h1
      have hyx : dotProduct y (P.mulVec x) = 1 := by
        rw [bilinear_symm hP, hxy]
      have hxx : dotProduct x (P.mulVec x) = 0 := bilinear_alt_self hP x
      have hyy : dotProduct y (P.mulVec y) = 0 := bilinear_alt_self hP y
      let W' : Submodule F (Fin n → F) :=
        { carrier := {w | w ∈ W ∧ dotProduct x (P.mulVec w) = 0 ∧ dotProduct y (P.mulVec w) = 0}
          zero_mem' := ⟨W.zero_mem, by simp, by simp⟩, add_mem' := by
            rintro a b ⟨haW, hxa, hya⟩ ⟨hbW, hxb, hyb⟩
            refine ⟨W.add_mem haW hbW, ?_, ?_⟩
            · rw [Matrix.mulVec_add, dotProduct_add, hxa, hxb, add_zero]
            · rw [Matrix.mulVec_add, dotProduct_add, hya, hyb, add_zero]
          smul_mem' := by
            rintro c a ⟨haW, hxa, hya⟩
            refine ⟨W.smul_mem c haW, ?_, ?_⟩
            · rw [Matrix.mulVec_smul, dotProduct_smul, hxa, smul_zero]
            · rw [Matrix.mulVec_smul, dotProduct_smul, hya, smul_zero] }
      have hproj_mem : ∀ u ∈ W,
          u + dotProduct y (P.mulVec u) • x + dotProduct x (P.mulVec u) • y ∈ W' := by
        intro u hu
        refine ⟨W.add_mem (W.add_mem hu (W.smul_mem _ hxW)) (W.smul_mem _ hyW), ?_, ?_⟩
        · rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
            dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hxx, hxy,
            smul_zero, add_zero, smul_eq_mul, mul_one]
          exact zmod2_add_self _
        · rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
            dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, hyx, hyy,
            smul_zero, add_zero, smul_eq_mul, mul_one]
          exact zmod2_add_self _
      have hrad_eq : rad P W' = rad P W := by
        ext w
        simp only [rad, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
          Set.mem_ofPred_eq]
        constructor
        · rintro ⟨⟨hwW, hxw, hyw⟩, hw'⟩
          refine ⟨hwW, fun u hu => ?_⟩
          have hu' := hproj_mem u hu
          have h0 := hw' _ hu'
          rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
            dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul,
            bilinear_symm hP w x, hxw, bilinear_symm hP w y, hyw,
            smul_zero, smul_zero, add_zero, add_zero] at h0
          exact h0
        · rintro ⟨hwW, hw⟩
          refine ⟨⟨hwW, ?_, ?_⟩, fun u hu => hw u hu.1⟩
          · rw [bilinear_symm hP]; exact hw x hxW
          · rw [bilinear_symm hP]; exact hw y hyW
      let φ : W →ₗ[F] (F × F) :=
        { toFun := fun w => (dotProduct x (P.mulVec w.1), dotProduct y (P.mulVec w.1))
          map_add' := fun a b => by
            ext <;> simp [Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun c a => by
            ext <;> simp [Matrix.mulVec_smul, dotProduct_smul] }
      have hφ_surj : LinearMap.range φ = ⊤ := by
        rw [Submodule.eq_top_iff']
        rintro ⟨c₁, c₂⟩
        refine ⟨⟨c₁ • y + c₂ • x, W.add_mem (W.smul_mem c₁ hyW) (W.smul_mem c₂ hxW)⟩, ?_⟩
        ext
        · simp [φ, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
            hxy, hxx]
        · simp [φ, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
            hyy, hyx]
      let eKer : LinearMap.ker φ ≃ₗ[F] W' :=
        { toFun := fun w => ⟨w.1.1, w.1.2,
            congrArg Prod.fst w.2, congrArg Prod.snd w.2⟩
          invFun := fun w => ⟨⟨w.1, w.2.1⟩, Prod.ext w.2.2.1 w.2.2.2⟩
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      have hrn := LinearMap.finrank_range_add_finrank_ker φ
      rw [hφ_surj, finrank_top, Module.finrank_prod, Module.finrank_self,
        eKer.finrank_eq] at hrn
      have hdim' : Module.finrank F W' < d := by omega
      obtain ⟨k', e', f', hdim_eq', hmem', hee', hff', hef', hrad'⟩ :=
        ih (Module.finrank F W') hdim' W' rfl
      refine ⟨k' + 1, Fin.cons x e', Fin.cons y f', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hrad_eq]
        omega
      · intro t
        refine Fin.cases ?_ ?_ t
        · exact ⟨hxW, hyW⟩
        · intro t'
          exact ⟨(hmem' t').1.1, (hmem' t').2.1⟩
      · intro s t
        refine Fin.cases ?_ (fun s' => ?_) s
        · refine Fin.cases ?_ (fun t' => ?_) t
          · exact hxx
          · exact (hmem' t').1.2.1
        · refine Fin.cases ?_ (fun t' => ?_) t
          · rw [bilinear_symm hP]; exact (hmem' s').1.2.1
          · exact hee' s' t'
      · intro s t
        refine Fin.cases ?_ (fun s' => ?_) s
        · refine Fin.cases ?_ (fun t' => ?_) t
          · exact hyy
          · exact (hmem' t').2.2.2
        · refine Fin.cases ?_ (fun t' => ?_) t
          · rw [bilinear_symm hP]; exact (hmem' s').2.2.2
          · exact hff' s' t'
      · intro s t
        refine Fin.cases ?_ (fun s' => ?_) s
        · refine Fin.cases ?_ (fun t' => ?_) t
          · simp [hxy]
          · simp [Ne.symm (Fin.succ_ne_zero t'), (hmem' t').2.2.1]
        · refine Fin.cases ?_ (fun t' => ?_) t
          · simp [bilinear_symm hP (e' s') y, (hmem' s').1.2.2]
          · simp only [Fin.cons_succ, Fin.succ_inj]
            exact hef' s' t'
      · intro u hu
        let u' := u + dotProduct y (P.mulVec u) • x + dotProduct x (P.mulVec u) • y
        have hu' : u' ∈ W' := hproj_mem u hu
        have hsum_eq : u + ∑ t : Fin (k' + 1),
            (dotProduct u (P.mulVec (Fin.cons (α := fun _ => Fin n → F) y f' t)) •
               Fin.cons (α := fun _ => Fin n → F) x e' t +
             dotProduct u (P.mulVec (Fin.cons (α := fun _ => Fin n → F) x e' t)) •
               Fin.cons (α := fun _ => Fin n → F) y f' t) =
            u' + ∑ t : Fin k',
              (dotProduct u' (P.mulVec (f' t)) • e' t +
               dotProduct u' (P.mulVec (e' t)) • f' t) := by
          rw [Fin.sum_univ_succ]
          simp only [Fin.cons_zero, Fin.cons_succ]
          have hfirst : u + (dotProduct u (P.mulVec y) • x + dotProduct u (P.mulVec x) • y) = u' := by
            simp only [u', bilinear_symm hP y u, bilinear_symm hP x u, add_assoc]
          rw [← add_assoc, hfirst]
          congr 1
          refine Finset.sum_congr rfl fun t _ => ?_
          have huf : dotProduct u' (P.mulVec (f' t)) = dotProduct u (P.mulVec (f' t)) := by
            simp only [u', add_dotProduct, smul_dotProduct, (hmem' t).2.2.1,
              (hmem' t).2.2.2, smul_zero, add_zero]
          have hue : dotProduct u' (P.mulVec (e' t)) = dotProduct u (P.mulVec (e' t)) := by
            simp only [u', add_dotProduct, smul_dotProduct, (hmem' t).1.2.1,
              (hmem' t).1.2.2, smul_zero, add_zero]
          rw [huf, hue]
        rw [hsum_eq, ← hrad_eq]
        exact hrad' u' hu'

private lemma rad_top_eq_ker {n : ℕ} (P : Matrix (Fin n) (Fin n) F) (hP : IsAlt P) :
    rad P ⊤ = LinearMap.ker P.mulVecLin := by
  ext w
  simp only [rad, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_ofPred_eq, Submodule.mem_top, true_and, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hw
    funext i
    have hi := hw (Pi.single i (1 : F)) trivial
    rw [bilinear_symm hP] at hi
    simpa [dotProduct, Pi.single_apply] using hi
  · intro hw y _
    rw [bilinear_symm hP, hw, dotProduct_zero]

private lemma rank_even_of_isAlt {n : ℕ} (P : Matrix (Fin n) (Fin n) F) (hP : IsAlt P) :
    ∃ k, P.rank = 2 * k := by
  have hdim_top : Module.finrank F (⊤ : Submodule F (Fin n → F)) = n := by simp
  obtain ⟨k, _, _, hdim, _, _, _, _, _⟩ := exists_symplectic_on P hP n ⊤ hdim_top
  rw [hdim_top, rad_top_eq_ker P hP] at hdim
  have hrn := LinearMap.finrank_range_add_finrank_ker P.mulVecLin
  have hdimV : Module.finrank F (Fin n → F) = n := by simp
  rw [hdimV] at hrn
  refine ⟨k, ?_⟩
  unfold Matrix.rank
  omega

private lemma additive_eq_dotProduct {n : ℕ} (ℓ : (Fin n → F) → F)
    (hadd : ∀ u v, ℓ (u + v) = ℓ u + ℓ v) :
    ∃ a : Fin n → F, ∀ u, ℓ u = dotProduct a u := by
  have hzero : ℓ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    have h2 := congrArg (· + ℓ 0) h
    have h3 : 0 = ℓ 0 := by simpa [add_assoc, zmod2_add_self] using h2
    exact h3.symm
  have hsmul : ∀ (c : F) (v : Fin n → F), ℓ (c • v) = c * ℓ v := by
    intro c v
    rcases zmod2_cases c with rfl | rfl
    · simp [hzero]
    · simp
  have hsum : ∀ (s : Finset (Fin n)) (g : Fin n → (Fin n → F)),
      ℓ (∑ i ∈ s, g i) = ∑ i ∈ s, ℓ (g i) := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  refine ⟨fun i => ℓ (Pi.single i (1 : F)), fun u => ?_⟩
  have hu : u = ∑ i : Fin n, u i • Pi.single i (1 : F) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hu]
  rw [hsum]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsmul, mul_comm]

open Classical in
private lemma sum_chi_symplectic_subset {n r : ℕ} (M : Matrix (Fin n) (Fin n) F) (hM : IsAlt M)
    (e f : Fin r → (Fin n → F))
    (hee : ∀ s t, dotProduct (e s) (M.mulVec (e t)) = 0)
    (hff : ∀ s t, dotProduct (f s) (M.mulVec (f t)) = 0)
    (hef : ∀ s t, dotProduct (e s) (M.mulVec (f t)) = if s = t then 1 else 0)
    (S : Finset (Fin r)) :
    ∀ (W : Submodule F (Fin n → F)), (∀ t ∈ S, e t ∈ W ∧ f t ∈ W) →
      (2 : ℤ) ^ S.card *
        (∑ u : W, chi (∑ t ∈ S, dotProduct u.1 (M.mulVec (f t)) *
                                 dotProduct u.1 (M.mulVec (e t)))) =
        (Fintype.card W : ℤ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro W _
    simp [chi_zero]
  | insert t₀ S' ht₀ ih =>
    intro W hmem
    have he0 : e t₀ ∈ W := (hmem t₀ (Finset.mem_insert_self t₀ S')).1
    have hf0 : f t₀ ∈ W := (hmem t₀ (Finset.mem_insert_self t₀ S')).2
    let W' : Submodule F (Fin n → F) :=
      { carrier := {w | w ∈ W ∧ dotProduct w (M.mulVec (f t₀)) = 0 ∧
                                 dotProduct w (M.mulVec (e t₀)) = 0}
        zero_mem' := ⟨W.zero_mem, by simp, by simp⟩, add_mem' := by
          rintro a b ⟨haW, haf, hae⟩ ⟨hbW, hbf, hbe⟩
          refine ⟨W.add_mem haW hbW, ?_, ?_⟩
          · rw [add_dotProduct, haf, hbf, add_zero]
          · rw [add_dotProduct, hae, hbe, add_zero]
        smul_mem' := by
          rintro c a ⟨haW, haf, hae⟩
          refine ⟨W.smul_mem c haW, ?_, ?_⟩
          · rw [smul_dotProduct, haf, smul_zero]
          · rw [smul_dotProduct, hae, smul_zero] }
    have hmem' : ∀ t ∈ S', e t ∈ W' ∧ f t ∈ W' := by
      intro t ht
      have hne : t ≠ t₀ := fun h => ht₀ (h ▸ ht)
      have hW := hmem t (Finset.mem_insert_of_mem ht)
      refine ⟨⟨hW.1, ?_, ?_⟩, ⟨hW.2, ?_, ?_⟩⟩
      · simp [hef t t₀, hne]
      · exact hee t t₀
      · exact hff t t₀
      · rw [bilinear_symm hM, hef t₀ t]
        simp [hne.symm]
    have hB_shift : ∀ (x y : F) (w : W') (t : Fin r),
        dotProduct (w.1 + x • e t₀ + y • f t₀) (M.mulVec (f t)) =
          dotProduct w.1 (M.mulVec (f t)) + x * (if t₀ = t then 1 else 0) ∧
        dotProduct (w.1 + x • e t₀ + y • f t₀) (M.mulVec (e t)) =
          dotProduct w.1 (M.mulVec (e t)) + y * (if t = t₀ then 1 else 0) := by
      intro x y w t
      constructor
      · rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          hef t₀ t, hff t₀ t, smul_zero, add_zero, smul_eq_mul]
      · rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          hee t₀ t, bilinear_symm hM (f t₀) (e t), hef t t₀,
          smul_zero, add_zero, smul_eq_mul]
    let Φ : (F × F × W') ≃ W :=
      { toFun := fun p => ⟨p.2.2.1 + p.1 • e t₀ + p.2.1 • f t₀,
          W.add_mem (W.add_mem p.2.2.2.1 (W.smul_mem p.1 he0)) (W.smul_mem p.2.1 hf0)⟩
        invFun := fun u =>
          (dotProduct u.1 (M.mulVec (f t₀)),
           dotProduct u.1 (M.mulVec (e t₀)),
           ⟨u.1 + dotProduct u.1 (M.mulVec (f t₀)) • e t₀ +
                  dotProduct u.1 (M.mulVec (e t₀)) • f t₀,
            ⟨W.add_mem (W.add_mem u.2 (W.smul_mem _ he0)) (W.smul_mem _ hf0),
             by
               rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
                 hef t₀ t₀, hff t₀ t₀]
               simp only [↓reduceIte, smul_eq_mul, mul_one, mul_zero, add_zero]
               exact zmod2_add_self _,
             by
               rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
                 hee t₀ t₀, bilinear_symm hM (f t₀) (e t₀), hef t₀ t₀]
               simp only [↓reduceIte, smul_eq_mul, mul_one, mul_zero, add_zero]
               exact zmod2_add_self _⟩⟩)
        left_inv := by
          rintro ⟨x, y, w⟩
          have h0 := hB_shift x y w t₀
          simp only [↓reduceIte, mul_one, w.2.2.1, w.2.2.2, zero_add] at h0
          refine Prod.ext h0.1 (Prod.ext h0.2 ?_)
          apply Subtype.ext
          dsimp only
          rw [h0.1, h0.2]
          have h1 : x • e t₀ + x • e t₀ = 0 := zmod2_vec_add_self _
          have h2 : y • f t₀ + y • f t₀ = 0 := zmod2_vec_add_self _
          calc w.1 + x • e t₀ + y • f t₀ + x • e t₀ + y • f t₀
              = w.1 + (x • e t₀ + x • e t₀) + (y • f t₀ + y • f t₀) := by abel
            _ = w.1 := by rw [h1, h2]; simp
        right_inv := by
          rintro ⟨u, hu⟩
          apply Subtype.ext
          dsimp only
          have h1 : dotProduct u (M.mulVec (f t₀)) • e t₀ +
              dotProduct u (M.mulVec (f t₀)) • e t₀ = 0 := zmod2_vec_add_self _
          have h2 : dotProduct u (M.mulVec (e t₀)) • f t₀ +
              dotProduct u (M.mulVec (e t₀)) • f t₀ = 0 := zmod2_vec_add_self _
          calc u + dotProduct u (M.mulVec (f t₀)) • e t₀ +
                dotProduct u (M.mulVec (e t₀)) • f t₀ +
                dotProduct u (M.mulVec (f t₀)) • e t₀ +
                dotProduct u (M.mulVec (e t₀)) • f t₀
              = u + (dotProduct u (M.mulVec (f t₀)) • e t₀ +
                     dotProduct u (M.mulVec (f t₀)) • e t₀) +
                    (dotProduct u (M.mulVec (e t₀)) • f t₀ +
                     dotProduct u (M.mulVec (e t₀)) • f t₀) := by abel
            _ = u := by rw [h1, h2]; simp }
    have hcardW : (Fintype.card W : ℤ) = 4 * (Fintype.card W' : ℤ) := by
      have hc : Fintype.card W = Fintype.card (F × F × W') := Fintype.card_congr Φ.symm
      rw [hc, Fintype.card_prod, Fintype.card_prod, ZMod.card]
      push_cast
      ring
    have hsum : (∑ u : W, chi (∑ t ∈ insert t₀ S',
        dotProduct u.1 (M.mulVec (f t)) * dotProduct u.1 (M.mulVec (e t)))) =
        2 * (∑ w : W', chi (∑ t ∈ S',
          dotProduct w.1 (M.mulVec (f t)) * dotProduct w.1 (M.mulVec (e t)))) := by
      rw [← Fintype.sum_equiv Φ
        (fun p : F × F × W' => chi (∑ t ∈ insert t₀ S',
          dotProduct (Φ p).1 (M.mulVec (f t)) * dotProduct (Φ p).1 (M.mulVec (e t))))
        (fun u : W => chi (∑ t ∈ insert t₀ S',
          dotProduct u.1 (M.mulVec (f t)) * dotProduct u.1 (M.mulVec (e t))))
        (fun _ => rfl)]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      have hterm : ∀ (x y : F) (w : W'),
          chi (∑ t ∈ insert t₀ S',
            dotProduct (Φ (x, y, w)).1 (M.mulVec (f t)) *
            dotProduct (Φ (x, y, w)).1 (M.mulVec (e t))) =
          chi (x * y) * chi (∑ t ∈ S',
            dotProduct w.1 (M.mulVec (f t)) * dotProduct w.1 (M.mulVec (e t))) := by
        intro x y w
        have hΦ : (Φ (x, y, w)).1 = w.1 + x • e t₀ + y • f t₀ := rfl
        rw [Finset.sum_insert ht₀, chi_add]
        congr 1
        · have h0 := hB_shift x y w t₀
          simp only [↓reduceIte, mul_one, w.2.2.1, w.2.2.2, zero_add] at h0
          rw [hΦ, h0.1, h0.2]
        · congr 1
          refine Finset.sum_congr rfl fun t ht => ?_
          have hne : t ≠ t₀ := fun h => ht₀ (h ▸ ht)
          have ht_shift := hB_shift x y w t
          simp only [hne, hne.symm, ↓reduceIte, mul_zero, add_zero] at ht_shift
          rw [hΦ, ht_shift.1, ht_shift.2]
      simp_rw [hterm, ← Finset.mul_sum, ← Finset.sum_mul, chi_sum_pair]
    rw [Finset.card_insert_of_notMem ht₀, hsum, hcardW]
    have hih := ih W' hmem'
    calc (2 : ℤ) ^ (S'.card + 1) * (2 * ∑ w : W',
            chi (∑ t ∈ S', dotProduct w.1 (M.mulVec (f t)) * dotProduct w.1 (M.mulVec (e t))))
        = 4 * ((2 : ℤ) ^ S'.card * ∑ w : W',
            chi (∑ t ∈ S', dotProduct w.1 (M.mulVec (f t)) * dotProduct w.1 (M.mulVec (e t)))) := by
          rw [pow_succ]; ring
      _ = 4 * (Fintype.card W' : ℤ) := by rw [hih]

open Classical in
private lemma sum_chi_symplectic_univ {n r : ℕ} (M : Matrix (Fin n) (Fin n) F) (hM : IsAlt M)
    (e f : Fin r → (Fin n → F))
    (hee : ∀ s t, dotProduct (e s) (M.mulVec (e t)) = 0)
    (hff : ∀ s t, dotProduct (f s) (M.mulVec (f t)) = 0)
    (hef : ∀ s t, dotProduct (e s) (M.mulVec (f t)) = if s = t then 1 else 0)
    (S : Finset (Fin r)) :
    (2 : ℤ) ^ S.card *
      (∑ u : Fin n → F, chi (∑ t ∈ S, dotProduct u (M.mulVec (f t)) *
                                       dotProduct u (M.mulVec (e t)))) = (2 : ℤ) ^ n := by
  have h := sum_chi_symplectic_subset M hM e f hee hff hef S ⊤ (fun _ _ => ⟨trivial, trivial⟩)
  let eTop : (⊤ : Submodule F (Fin n → F)) ≃ (Fin n → F) :=
    { toFun := Subtype.val
      invFun := fun u => ⟨u, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hsum : (∑ u : (⊤ : Submodule F (Fin n → F)),
      chi (∑ t ∈ S, dotProduct u.1 (M.mulVec (f t)) * dotProduct u.1 (M.mulVec (e t)))) =
      ∑ u : Fin n → F,
        chi (∑ t ∈ S, dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t))) :=
    Fintype.sum_equiv eTop _ _ (fun _ => rfl)
  have hcard : Fintype.card (⊤ : Submodule F (Fin n → F)) = 2 ^ n := by
    rw [Fintype.card_congr eTop, Fintype.card_pi]
    simp [ZMod.card]
  rw [hsum, hcard] at h
  exact_mod_cast h

private lemma card_filter_lt_fin {r j : ℕ} (hj : j ≤ r) :
    ((Finset.univ : Finset (Fin r)).filter (fun t : Fin r => t.val < j)).card = j := by
  have hbij : ((Finset.univ : Finset (Fin r)).filter (fun t : Fin r => t.val < j)).card =
      (Finset.univ : Finset (Fin j)).card := by
    refine Finset.card_bij (fun t ht => (⟨t.val, (Finset.mem_filter.mp ht).2⟩ : Fin j))
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro a _ b _ hEq
      exact Fin.ext (Fin.mk.inj hEq)
    · intro k _
      refine ⟨⟨k.val, by omega⟩, ?_, Fin.ext rfl⟩
      simp
  rw [hbij, Finset.card_univ, Fintype.card_fin]

private lemma card_filter_ge_fin {r j : ℕ} (hj : j ≤ r) :
    ((Finset.univ : Finset (Fin r)).filter (fun t : Fin r => j ≤ t.val)).card = r - j := by
  have hbij : ((Finset.univ : Finset (Fin r)).filter (fun t : Fin r => j ≤ t.val)).card =
      (Finset.univ : Finset (Fin (r - j))).card := by
    refine Finset.card_bij (fun t ht => (⟨t.val - j, by
        have h := (Finset.mem_filter.mp ht).2
        omega⟩ : Fin (r - j)))
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · intro a ha b hb hEq
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hval := Fin.mk.inj hEq
      exact Fin.ext (by omega)
    · intro k _
      refine ⟨⟨j + k.val, by omega⟩, ?_, Fin.ext (by simp)⟩
      simp
  rw [hbij, Finset.card_univ, Fintype.card_fin]

private theorem prove_863 (n r : ℕ)
    (Q : Bool → (Fin n → F) → F) (M : Matrix (Fin n) (Fin n) F)
    (hQ : ∀ t, IsQuad (Q t))
    (hMrank : M.rank = 2 * r)
    (hMpolar : ∀ u v, (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
      (Q false v + Q true v) + (Q false 0 + Q true 0) = dotProduct u (M.mulVec v)) :
    let agree := fun (q : (Fin n → F) → F) (a : Fin n → F) (b : F) (t : Bool) =>
      ∑ u : Fin n → F, if Q t u = q u + (if t then dotProduct a u + b else 0) then (1 : ℤ) else -1
    (∀ (q : (Fin n → F) → F) (a : Fin n → F) (b : F), IsQuad q →
      ∃ j ≤ r, 2 ^ j * (agree q a b false).natAbs ≤ 2 ^ n ∧
        2 ^ (r - j) * (agree q a b true).natAbs ≤ 2 ^ n) ∧
    ∀ j ≤ r, ∃ (q : (Fin n → F) → F) (a : Fin n → F) (b : F), IsQuad q ∧
      (2 : ℤ) ^ j * agree q a b false = 2 ^ n ∧
      (2 : ℤ) ^ (r - j) * agree q a b true = 2 ^ n := by
  intro agree
  constructor
  · intro q a b hq
    let e₀ : (Fin n → F) → F := fun u => Q false u + q u
    let e₁ : (Fin n → F) → F := fun u => Q true u + (q u + (dotProduct a u + b))
    have he₀ : IsQuad e₀ := isQuad_add (hQ false) hq
    have he₁ : IsQuad e₁ := isQuad_add (hQ true) (isQuad_add hq (isQuad_affine a b))
    obtain ⟨P₀, hP₀_alt, hP₀⟩ := exists_polar_of_isQuad he₀
    obtain ⟨P₁, hP₁_alt, hP₁⟩ := exists_polar_of_isQuad he₁
    have hPsum : P₀ + P₁ = M := by
      apply matrix_eq_of_dot_mulVec
      intro u v
      rw [Matrix.add_mulVec, dotProduct_add, ← hP₀ u v, ← hP₁ u v, ← hMpolar u v]
      simp only [e₀, e₁, dotProduct_add, dotProduct_zero, zero_add]
      have hq1 := zmod2_add_self (q (u + v))
      have hq2 := zmod2_add_self (q u)
      have hq3 := zmod2_add_self (q v)
      have hq4 := zmod2_add_self (q 0)
      have ha1 := zmod2_add_self (dotProduct a u)
      have ha2 := zmod2_add_self (dotProduct a v)
      have hb := zmod2_add_self b
      calc (Q false (u + v) + q (u + v)) + (Q false u + q u) + (Q false v + q v) +
            (Q false 0 + q 0) +
            ((Q true (u + v) + (q (u + v) + (dotProduct a u + dotProduct a v + b))) +
             (Q true u + (q u + (dotProduct a u + b))) +
             (Q true v + (q v + (dotProduct a v + b))) +
             (Q true 0 + (q 0 + b)))
          = (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
            (Q false v + Q true v) + (Q false 0 + Q true 0) +
            (q (u + v) + q (u + v)) + (q u + q u) + (q v + q v) + (q 0 + q 0) +
            (dotProduct a u + dotProduct a u) + (dotProduct a v + dotProduct a v) +
            (b + b) + (b + b) := by ring
        _ = (Q false (u + v) + Q true (u + v)) + (Q false u + Q true u) +
            (Q false v + Q true v) + (Q false 0 + Q true 0) := by
              rw [hq1, hq2, hq3, hq4, ha1, ha2, hb]; simp
    obtain ⟨a₀, ha₀⟩ := rank_even_of_isAlt P₀ hP₀_alt
    obtain ⟨b₁, hb₁⟩ := rank_even_of_isAlt P₁ hP₁_alt
    have hrank_le : r ≤ a₀ + b₁ := by
      have h := rank_add_le_aux P₀ P₁
      rw [hPsum, hMrank, ha₀, hb₁] at h
      omega
    refine ⟨min a₀ r, Nat.min_le_right a₀ r, ?_, ?_⟩
    · have hja : min a₀ r ≤ a₀ := Nat.min_le_left a₀ r
      have hagree0 : agree q a b false = ∑ u : Fin n → F, chi (e₀ u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp [e₀, chi_eq_ite]
      rw [hagree0]
      have hw := walsh_sq_bound e₀ P₀ hP₀
      rw [ha₀] at hw
      have hpow : 2 ^ (2 * min a₀ r) ≤ 2 ^ (2 * a₀) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hsq : (2 ^ min a₀ r * (∑ u : Fin n → F, chi (e₀ u)).natAbs) ^ 2 ≤ (2 ^ n) ^ 2 := by
        calc (2 ^ min a₀ r * (∑ u : Fin n → F, chi (e₀ u)).natAbs) ^ 2
            = 2 ^ (2 * min a₀ r) * (∑ u : Fin n → F, chi (e₀ u)).natAbs ^ 2 := by
                rw [mul_pow, ← pow_mul, mul_comm (min a₀ r) 2]
          _ ≤ 2 ^ (2 * a₀) * (∑ u : Fin n → F, chi (e₀ u)).natAbs ^ 2 :=
                Nat.mul_le_mul_right _ hpow
          _ ≤ (2 ^ n) ^ 2 := hw
      by_contra hlt
      push Not at hlt
      have hgt := Nat.mul_lt_mul'' hlt hlt
      simp only [sq] at hsq
      omega
    · have hrjb : r - min a₀ r ≤ b₁ := by omega
      have hagree1 : agree q a b true = ∑ u : Fin n → F, chi (e₁ u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp [e₁, chi_eq_ite]
      rw [hagree1]
      have hw := walsh_sq_bound e₁ P₁ hP₁
      rw [hb₁] at hw
      have hpow : 2 ^ (2 * (r - min a₀ r)) ≤ 2 ^ (2 * b₁) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hsq : (2 ^ (r - min a₀ r) * (∑ u : Fin n → F, chi (e₁ u)).natAbs) ^ 2 ≤ (2 ^ n) ^ 2 := by
        calc (2 ^ (r - min a₀ r) * (∑ u : Fin n → F, chi (e₁ u)).natAbs) ^ 2
            = 2 ^ (2 * (r - min a₀ r)) * (∑ u : Fin n → F, chi (e₁ u)).natAbs ^ 2 := by
                rw [mul_pow, ← pow_mul, mul_comm (r - min a₀ r) 2]
          _ ≤ 2 ^ (2 * b₁) * (∑ u : Fin n → F, chi (e₁ u)).natAbs ^ 2 :=
                Nat.mul_le_mul_right _ hpow
          _ ≤ (2 ^ n) ^ 2 := hw
      by_contra hlt
      push Not at hlt
      have hgt := Nat.mul_lt_mul'' hlt hlt
      simp only [sq] at hsq
      omega
  · intro j hj
    let d : (Fin n → F) → F := fun u => Q false u + Q true u
    have hM_alt : IsAlt M := isAlt_of_polar (d := d) hMpolar
    have hdim_top : Module.finrank F (⊤ : Submodule F (Fin n → F)) = n := by simp
    obtain ⟨k, e, f, hdim_k, _, hee, hff, hef, hdecomp⟩ :=
      exists_symplectic_on M hM_alt n ⊤ hdim_top
    have hkr : k = r := by
      rw [hdim_top, rad_top_eq_ker M hM_alt] at hdim_k
      have hrn := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
      have hdimV : Module.finrank F (Fin n → F) = n := by simp
      rw [hdimV] at hrn
      have hMr : Module.finrank F (LinearMap.range M.mulVecLin) = 2 * r := hMrank
      omega
    subst hkr
    let g : (Fin n → F) → F :=
      fun u => ∑ t : Fin k, dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t))
    have hg_polar : ∀ u v, g (u + v) + g u + g v + g 0 = dotProduct u (M.mulVec v) := by
      intro u v
      have hLHS : g (u + v) + g u + g v + g 0 =
          ∑ t : Fin k, (dotProduct u (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)) +
                        dotProduct u (M.mulVec (e t)) * dotProduct v (M.mulVec (f t))) := by
        simp only [g, zero_dotProduct, mul_zero, Finset.sum_const_zero, add_zero,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        simp only [add_dotProduct]
        have h1 := zmod2_add_self (dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t)))
        have h2 := zmod2_add_self (dotProduct v (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)))
        calc (dotProduct u (M.mulVec (f t)) + dotProduct v (M.mulVec (f t))) *
              (dotProduct u (M.mulVec (e t)) + dotProduct v (M.mulVec (e t))) +
              dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t)) +
              dotProduct v (M.mulVec (f t)) * dotProduct v (M.mulVec (e t))
            = (dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t)) +
               dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t))) +
              (dotProduct v (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)) +
               dotProduct v (M.mulVec (f t)) * dotProduct v (M.mulVec (e t))) +
              (dotProduct u (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)) +
               dotProduct u (M.mulVec (e t)) * dotProduct v (M.mulVec (f t))) := by ring
          _ = _ := by rw [h1, h2]; simp
      rw [hLHS]
      have hrad_u := (hdecomp u trivial).2 v trivial
      rw [add_dotProduct, sum_dotProduct_aux] at hrad_u
      have hsum_eq : (∑ t : Fin k, dotProduct (dotProduct u (M.mulVec (f t)) • e t +
            dotProduct u (M.mulVec (e t)) • f t) (M.mulVec v)) =
          ∑ t : Fin k, (dotProduct u (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)) +
                        dotProduct u (M.mulVec (e t)) * dotProduct v (M.mulVec (f t))) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul,
          bilinear_symm hM_alt (e t) v, bilinear_symm hM_alt (f t) v]
      rw [hsum_eq] at hrad_u
      have hadd := congrArg (· + dotProduct u (M.mulVec v)) hrad_u
      have hself := zmod2_add_self (dotProduct u (M.mulVec v))
      calc (∑ t : Fin k, (dotProduct u (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)) +
              dotProduct u (M.mulVec (e t)) * dotProduct v (M.mulVec (f t))))
          = (dotProduct u (M.mulVec v) + dotProduct u (M.mulVec v)) +
            (∑ t : Fin k, (dotProduct u (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)) +
              dotProduct u (M.mulVec (e t)) * dotProduct v (M.mulVec (f t)))) := by
              rw [hself, zero_add]
        _ = (dotProduct u (M.mulVec v) +
            (∑ t : Fin k, (dotProduct u (M.mulVec (f t)) * dotProduct v (M.mulVec (e t)) +
              dotProduct u (M.mulVec (e t)) * dotProduct v (M.mulVec (f t))))) +
            dotProduct u (M.mulVec v) := by ring
        _ = 0 + dotProduct u (M.mulVec v) := hadd
        _ = dotProduct u (M.mulVec v) := zero_add _
    let ℓ : (Fin n → F) → F := fun u => d u + g u + d 0
    have hℓ_add : ∀ u v, ℓ (u + v) = ℓ u + ℓ v := by
      intro u v
      have hd_g : (d (u + v) + d u + d v + d 0) + (g (u + v) + g u + g v + g 0) = 0 := by
        rw [hMpolar u v, hg_polar u v, zmod2_add_self]
      have hg0 : g 0 = 0 := by simp [g]
      rw [hg0, add_zero] at hd_g
      have hsum0 : ℓ (u + v) + (ℓ u + ℓ v) = 0 := by
        have hd0 := zmod2_add_self (d 0)
        calc ℓ (u + v) + (ℓ u + ℓ v)
            = ((d (u + v) + d u + d v + d 0) + (g (u + v) + g u + g v)) + (d 0 + d 0) := by
                dsimp only [ℓ]; ring
          _ = 0 := by rw [hd_g, hd0, add_zero]
      have hself := zmod2_add_self (ℓ u + ℓ v)
      calc ℓ (u + v)
          = ℓ (u + v) + ((ℓ u + ℓ v) + (ℓ u + ℓ v)) := by rw [hself, add_zero]
        _ = (ℓ (u + v) + (ℓ u + ℓ v)) + (ℓ u + ℓ v) := by ring
        _ = ℓ u + ℓ v := by rw [hsum0, zero_add]
    obtain ⟨a_d, ha_d⟩ := additive_eq_dotProduct ℓ hℓ_add
    have hd_eq : ∀ u, d u = g u + dotProduct a_d u + d 0 := by
      intro u
      have h := ha_d u
      dsimp only [ℓ] at h
      have hgu := zmod2_add_self (g u)
      have hd0 := zmod2_add_self (d 0)
      calc d u = d u + (g u + g u) + (d 0 + d 0) := by rw [hgu, hd0]; simp
        _ = (d u + g u + d 0) + g u + d 0 := by ring
        _ = dotProduct a_d u + g u + d 0 := by rw [h]
        _ = g u + dotProduct a_d u + d 0 := by ring
    let S_L : Finset (Fin k) := Finset.univ.filter (fun t : Fin k => t.val < j)
    let S_R : Finset (Fin k) := Finset.univ.filter (fun t : Fin k => j ≤ t.val)
    have hSL_card : S_L.card = j := card_filter_lt_fin hj
    have hSR_card : S_R.card = k - j := card_filter_ge_fin hj
    let gL : (Fin n → F) → F :=
      fun u => ∑ t ∈ S_L, dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t))
    let gR : (Fin n → F) → F :=
      fun u => ∑ t ∈ S_R, dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t))
    have hg_split : ∀ u, g u = gL u + gR u := by
      intro u
      have hdisj : Disjoint S_L S_R := by
        rw [Finset.disjoint_left]
        intro t h1 h2
        simp only [S_L, S_R, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        omega
      have hunion : S_L ∪ S_R = Finset.univ := by
        ext t
        simp only [S_L, S_R, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
          iff_true]
        omega
      simpa only [g, gL, gR, hunion] using
        Finset.sum_union hdisj (f := fun t => dotProduct u (M.mulVec (f t)) *
          dotProduct u (M.mulVec (e t)))
    let q : (Fin n → F) → F := fun u => Q false u + gL u
    have hq_quad : IsQuad q := by
      apply isQuad_add (hQ false)
      apply isQuad_finset_sum S_L
      intro t _
      have hrewrite : (fun u : Fin n → F =>
          dotProduct u (M.mulVec (f t)) * dotProduct u (M.mulVec (e t))) =
          fun u => dotProduct (M.mulVec (f t)) u * dotProduct (M.mulVec (e t)) u := by
        funext u
        rw [dotProduct_comm u (M.mulVec (f t)), dotProduct_comm u (M.mulVec (e t))]
      rw [hrewrite]
      exact isQuad_mul_dot (M.mulVec (f t)) (M.mulVec (e t))
    refine ⟨q, a_d, d 0, hq_quad, ?_, ?_⟩
    · have hagree0 : agree q a_d (d 0) false = ∑ u : Fin n → F, chi (gL u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [Bool.false_eq_true, ↓reduceIte, add_zero, chi_eq_ite, q]
        rw [zmod2_add_cancel_left]
      rw [hagree0, ← hSL_card]
      exact sum_chi_symplectic_univ M hM_alt e f hee hff hef S_L
    · have hagree1 : agree q a_d (d 0) true = ∑ u : Fin n → F, chi (gR u) := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [↓reduceIte, chi_eq_ite, q]
        have harg : Q true u + (Q false u + gL u + (dotProduct a_d u + d 0)) = gR u := by
          have hd' := hd_eq u
          rw [hg_split u] at hd'
          have h1 : Q true u + Q false u = d u := add_comm _ _
          have hgl := zmod2_add_self (gL u)
          have ha := zmod2_add_self (dotProduct a_d u)
          have hd0 := zmod2_add_self (d 0)
          calc Q true u + (Q false u + gL u + (dotProduct a_d u + d 0))
              = (Q true u + Q false u) + gL u + dotProduct a_d u + d 0 := by ring
            _ = (gL u + gR u + dotProduct a_d u + d 0) + gL u + dotProduct a_d u + d 0 := by
                  rw [h1, hd']
            _ = gR u + (gL u + gL u) + (dotProduct a_d u + dotProduct a_d u) + (d 0 + d 0) := by
                  ring
            _ = gR u := by rw [hgl, ha, hd0]; simp
        rw [harg]
      rw [hagree1, ← hSR_card]
      exact sum_chi_symplectic_univ M hM_alt e f hee hff hef S_R

end PEqualNP.Outside.L_lib_863_aux

theorem PEqualNP.Outside.L_lib_863 : (∀ (n r : ℕ),
  let F := ZMod 2
  let V := Fin n → F
  let quad := fun (q : V → F) =>
    ∃ (b : F) (a : V) (M : Fin n → Fin n → F), ∀ v,
      q v = b + dotProduct a v + ∑ i, ∑ j, M i j * v i * v j
  ∀ (Q : Bool → V → F) (M : Matrix (Fin n) (Fin n) F), (∀ t, quad (Q t)) →
    let d := fun u : V => Q false u + Q true u
    M.rank = 2*r → (∀ u v, d (u+v) + d u + d v + d 0 = dotProduct u (M.mulVec v)) →
    let agree := fun (q : V → F) (a : V) (b : F) (t : Bool) =>
      ∑ u : V, if Q t u = q u + (if t then dotProduct a u + b else 0) then (1 : ℤ) else -1
    (∀ (q : V → F) (a : V) (b : F), quad q →
      ∃ j ≤ r, 2^j * (agree q a b false).natAbs ≤ 2^n ∧
        2^(r-j) * (agree q a b true).natAbs ≤ 2^n) ∧
    ∀ j ≤ r, ∃ (q : V → F) (a : V) (b : F), quad q ∧
      (2 : ℤ)^j * agree q a b false = 2^n ∧
      (2 : ℤ)^(r-j) * agree q a b true = 2^n) := by
  intro n r F V quad Q M hQ d hMrank hMpolar agree
  exact PEqualNP.Outside.L_lib_863_aux.prove_863 n r Q M hQ hMrank hMpolar
