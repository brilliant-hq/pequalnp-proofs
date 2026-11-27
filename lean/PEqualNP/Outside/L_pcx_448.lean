import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_448_aux

abbrev K := ZMod 2

lemma k_cases (x : K) : x = 0 ∨ x = 1 := by
  match x with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

lemma k_add_self (x : K) : x + x = 0 := by
  rcases k_cases x with rfl | rfl <;> decide

lemma poly_add_self {σ : Type*} (p : MvPolynomial σ K) : p + p = 0 := by
  calc p + p = (1 + 1 : K) • p := by rw [add_smul, one_smul]
    _ = (0 : K) • p := by rw [k_add_self]
    _ = 0 := zero_smul _ _

noncomputable def ev0 {n : ℕ} : MvPolynomial (Fin n ⊕ Unit) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun _ => (0 : MvPolynomial (Fin n) K)))

noncomputable def ev1 {n : ℕ} : MvPolynomial (Fin n ⊕ Unit) K →ₐ[K] MvPolynomial (Fin n) K :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X (fun _ => (1 : MvPolynomial (Fin n) K)))

lemma eval_ev0 {n : ℕ} (x : Fin n → K) (p : MvPolynomial (Fin n ⊕ Unit) K) :
    MvPolynomial.eval x (ev0 p) = MvPolynomial.eval (Sum.elim x (fun _ => 0)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ev0]
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | mul_X p v ihp =>
    rw [map_mul, map_mul, map_mul, ihp]
    cases v <;> simp [ev0]

lemma eval_ev1 {n : ℕ} (x : Fin n → K) (p : MvPolynomial (Fin n ⊕ Unit) K) :
    MvPolynomial.eval x (ev1 p) = MvPolynomial.eval (Sum.elim x (fun _ => 1)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ev1]
  | add p q ihp ihq => simp [map_add, ihp, ihq]
  | mul_X p v ihp =>
    rw [map_mul, map_mul, map_mul, ihp]
    cases v <;> simp [ev1]

noncomputable def partA {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) K) : MvPolynomial (Fin n) K :=
  ev0 p

noncomputable def partB {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) K) : MvPolynomial (Fin n) K :=
  ev1 p + ev0 p

lemma eval_decomp {n : ℕ} (x : Fin n → K) (u : K) (p : MvPolynomial (Fin n ⊕ Unit) K) :
    MvPolynomial.eval (Sum.elim x (fun _ => u)) p =
      MvPolynomial.eval x (partA p) + u * MvPolynomial.eval x (partB p) := by
  rcases k_cases u with rfl | rfl
  · simp [partA, eval_ev0]
  · simp only [partA, partB, map_add, one_mul, eval_ev0, eval_ev1]
    have h := k_add_self (MvPolynomial.eval (Sum.elim x (fun _ => 0)) p)
    calc MvPolynomial.eval (Sum.elim x (fun _ => 1)) p
        = MvPolynomial.eval (Sum.elim x (fun _ => 1)) p + 0 := (add_zero _).symm
      _ = MvPolynomial.eval (Sum.elim x (fun _ => 1)) p +
          (MvPolynomial.eval (Sum.elim x (fun _ => 0)) p + MvPolynomial.eval (Sum.elim x (fun _ => 0)) p) := by rw [h]
      _ = MvPolynomial.eval (Sum.elim x (fun _ => 0)) p +
          (MvPolynomial.eval (Sum.elim x (fun _ => 1)) p + MvPolynomial.eval (Sum.elim x (fun _ => 0)) p) := by
        rw [add_left_comm]

lemma monomial_left_deg {n : ℕ} (s : (Fin n ⊕ Unit) →₀ ℕ) (c : K) :
    (MvPolynomial.C c * ∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K) ^ s (Sum.inl i)).totalDegree ≤
      ∑ i : Fin n, s (Sum.inl i) := by
  calc (MvPolynomial.C c * ∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K) ^ s (Sum.inl i)).totalDegree
      ≤ (MvPolynomial.C c : MvPolynomial (Fin n) K).totalDegree +
        (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K) ^ s (Sum.inl i)).totalDegree :=
          MvPolynomial.totalDegree_mul _ _
    _ = (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K) ^ s (Sum.inl i)).totalDegree := by
          rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ ∑ i : Fin n, ((MvPolynomial.X i : MvPolynomial (Fin n) K) ^ s (Sum.inl i)).totalDegree :=
          MvPolynomial.totalDegree_finsetProd _ _
    _ = ∑ i : Fin n, s (Sum.inl i) := by
          apply Finset.sum_congr rfl; intro i _
          exact MvPolynomial.totalDegree_X_pow i (s (Sum.inl i))

lemma ev0_monomial {n : ℕ} (s : (Fin n ⊕ Unit) →₀ ℕ) (c : K) :
    ev0 (MvPolynomial.monomial s c) =
      MvPolynomial.C c * ((∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K) ^ s (Sum.inl i)) *
        (0 : MvPolynomial (Fin n) K) ^ s (Sum.inr ())) := by
  simp only [ev0, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hu : (∏ u : Unit, (0 : MvPolynomial (Fin n) K) ^ s (Sum.inr u)) =
      (0 : MvPolynomial (Fin n) K) ^ s (Sum.inr ()) := Fintype.prod_unique _
  rw [hu]

lemma ev1_monomial {n : ℕ} (s : (Fin n ⊕ Unit) →₀ ℕ) (c : K) :
    ev1 (MvPolynomial.monomial s c) =
      MvPolynomial.C c * ∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K) ^ s (Sum.inl i) := by
  simp only [ev1, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, one_pow]
  have hu : (∏ _u : Unit, (1 : MvPolynomial (Fin n) K)) = 1 := Fintype.prod_unique _
  rw [hu, mul_one]

lemma sum_finsupp_split {n : ℕ} (s : (Fin n ⊕ Unit) →₀ ℕ) :
    s.sum (fun _ e => e) = (∑ i : Fin n, s (Sum.inl i)) + s (Sum.inr ()) := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_sum_type]
  have hu : (∑ u : Unit, s (Sum.inr u)) = s (Sum.inr ()) := Fintype.sum_unique _
  rw [hu]

lemma totalDegree_partA_le {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) K) :
    (partA p).totalDegree ≤ p.totalDegree := by
  unfold partA
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [ev0_monomial]
  by_cases h0 : s (Sum.inr ()) = 0
  · rw [h0, pow_zero, mul_one]
    have hle : s.sum (fun _ e => e) ≤ p.totalDegree :=
      Finset.le_sup (f := fun s : (Fin n ⊕ Unit) →₀ ℕ => s.sum fun _ e => e) hs
    rw [sum_finsupp_split] at hle
    exact (monomial_left_deg s (p.coeff s)).trans (by omega)
  · rw [zero_pow h0, mul_zero, mul_zero, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _

lemma totalDegree_partB_le {n : ℕ} (p : MvPolynomial (Fin n ⊕ Unit) K) :
    (partB p).totalDegree ≤ p.totalDegree - 1 := by
  unfold partB
  conv_lhs => rw [p.as_sum]
  rw [map_sum, map_sum, ← Finset.sum_add_distrib]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  rw [ev1_monomial, ev0_monomial]
  by_cases h0 : s (Sum.inr ()) = 0
  · rw [h0, pow_zero, mul_one, poly_add_self, MvPolynomial.totalDegree_zero]
    exact Nat.zero_le _
  · rw [zero_pow h0, mul_zero, mul_zero, add_zero]
    have hle : s.sum (fun _ e => e) ≤ p.totalDegree :=
      Finset.le_sup (f := fun s : (Fin n ⊕ Unit) →₀ ℕ => s.sum fun _ e => e) hs
    rw [sum_finsupp_split] at hle
    exact (monomial_left_deg s (p.coeff s)).trans (by omega)

lemma two_mul_choose_two_add (m : ℕ) : 2 * m.choose 2 + m = m * m := by
  induction m with
  | zero => decide
  | succ k ih =>
    have hch : (k + 1).choose 2 = k.choose 2 + k := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      exact Nat.add_comm k (k.choose 2)
    have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
      simp only [Nat.add_mul, Nat.mul_add, one_mul, mul_one]; omega
    omega

lemma card_lt_pairs (m : ℕ) :
    (((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))).filter
      (fun ij => ij.1 < ij.2)).card = m.choose 2 := by
  let U := (Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))
  let L := U.filter (fun ij => ij.1 < ij.2)
  let R := U.filter (fun ij => ij.2 < ij.1)
  let D := U.filter (fun ij => ij.1 = ij.2)
  have hLR : L.card = R.card := by
    apply Finset.card_bij (fun ij _ => (ij.2, ij.1))
    · intro ij hij
      have hlt : ij.1 < ij.2 := (Finset.mem_filter.mp hij).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hlt⟩
    · intro ij1 _ ij2 _ h
      exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
    · intro ij hij
      have hlt : ij.2 < ij.1 := (Finset.mem_filter.mp hij).2
      exact ⟨(ij.2, ij.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, hlt⟩, rfl⟩
  have hD : D.card = m := by
    have hbij : D.card = (Finset.univ : Finset (Fin m)).card := by
      apply Finset.card_bij (fun ij _ => ij.1)
      · intro _ _; exact Finset.mem_univ _
      · intro ij1 h1 ij2 h2 heq
        have e1 : ij1.1 = ij1.2 := (Finset.mem_filter.mp h1).2
        have e2 : ij2.1 = ij2.2 := (Finset.mem_filter.mp h2).2
        exact Prod.ext heq (e1.symm.trans (heq.trans e2))
      · intro i _
        exact ⟨(i, i), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩, rfl⟩
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  have hdLR : Disjoint L R := by
    rw [Finset.disjoint_filter]; intro ij _ h1 h2; exact lt_asymm h1 h2
  have hdLD : Disjoint L D := by
    rw [Finset.disjoint_filter]; intro ij _ h1 h2; exact ne_of_lt h1 h2
  have hdRD : Disjoint R D := by
    rw [Finset.disjoint_filter]; intro ij _ h1 h2; exact ne_of_gt h1 h2
  have hunion : L ∪ R ∪ D = U := by
    ext ij
    simp only [L, R, D, U, Finset.mem_union, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, iff_true]
    rcases lt_trichotomy ij.1 ij.2 with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
    · exact Or.inl (Or.inr h)
  have hcardU : U.card = m * m := by
    simp [U, Fintype.card_fin]
  have hsum : (L ∪ R ∪ D).card = L.card + R.card + D.card := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hdLD, hdRD⟩),
      Finset.card_union_of_disjoint hdLR]
  rw [hunion, hcardU] at hsum
  have hc := two_mul_choose_two_add m
  change L.card = m.choose 2
  omega

lemma part1_alg {m : ℕ} (α β : Fin m → K) :
    (∃ u : K, ∀ i, α i + u * β i = 0) ↔
      (∀ i, α i * (1 + β i) = 0) ∧ (∀ i j, i < j → α i * β j + α j * β i = 0) := by
  constructor
  · rintro ⟨u, hu⟩
    have hα : ∀ i, α i = u * β i := by
      intro i
      have h1 := congrArg (· + u * β i) (hu i)
      simp only [add_assoc, k_add_self, add_zero, zero_add] at h1
      exact h1
    refine ⟨fun i => ?_, fun i j _ => ?_⟩
    · rcases k_cases (β i) with hbi | hbi
      · rw [hα i, hbi, mul_zero, zero_mul]
      · rw [hbi, k_add_self 1, mul_zero]
    · rw [hα i, hα j]
      have hmul : u * β i * β j = u * β j * β i := by
        rw [mul_assoc, mul_comm (β i) (β j), ← mul_assoc]
      rw [hmul, k_add_self]
  · rintro ⟨hG1, hG2lt⟩
    have hG2 : ∀ i j, α i * β j + α j * β i = 0 := by
      intro i j
      rcases lt_trichotomy i j with hij | rfl | hji
      · exact hG2lt i j hij
      · exact k_add_self _
      · rw [add_comm]; exact hG2lt j i hji
    by_cases hβ : ∀ i, β i = 0
    · refine ⟨0, fun i => ?_⟩
      rw [hβ i, mul_zero, add_zero]
      have h0 := hG1 i
      rw [hβ i, add_zero, mul_one] at h0
      exact h0
    · have hex : ∃ i0, β i0 ≠ 0 := by
        by_contra hnone
        exact hβ (fun i => by by_contra hne; exact hnone ⟨i, hne⟩)
      rcases hex with ⟨i0, hi0⟩
      have hbi0 : β i0 = 1 := by
        rcases k_cases (β i0) with h | h
        · exact (hi0 h).elim
        · exact h
      refine ⟨α i0, fun j => ?_⟩
      have h0 := hG2 j i0
      rw [hbi0, mul_one] at h0
      exact h0

lemma part1 (d n m : ℕ) :
    let P := MvPolynomial (Fin n ⊕ Unit) K
    let S := MvPolynomial (Fin n) K
    ∀ F : Fin m → P, (∀ i, (F i).totalDegree ≤ d + 1) →
      ∃ G : Finset S, G.card ≤ m + m.choose 2 ∧
        (∀ p ∈ G, p.totalDegree ≤ 2 * d + 1) ∧
        ∀ x : Fin n → K,
          (∃ u : K, ∀ i, MvPolynomial.eval (Sum.elim x (fun _ => u)) (F i) = 0) ↔
          ∀ p ∈ G, MvPolynomial.eval x p = 0 := by
  classical
  intro P S F hdeg
  let a : Fin m → S := fun i => partA (F i)
  let b : Fin m → S := fun i => partB (F i)
  have ha_deg : ∀ i, (a i).totalDegree ≤ d + 1 := fun i =>
    (totalDegree_partA_le (F i)).trans (hdeg i)
  have hb_deg : ∀ i, (b i).totalDegree ≤ d := fun i => by
    have h1 : (b i).totalDegree ≤ (F i).totalDegree - 1 := totalDegree_partB_le (F i)
    have h2 := hdeg i
    omega
  let g1 : Fin m → S := fun i => a i * (1 + b i)
  let g2 : Fin m × Fin m → S := fun ij => a ij.1 * b ij.2 + a ij.2 * b ij.1
  let G1 : Finset S := (Finset.univ : Finset (Fin m)).image g1
  let pairs := ((Finset.univ : Finset (Fin m)) ×ˢ (Finset.univ : Finset (Fin m))).filter (fun ij => ij.1 < ij.2)
  let G2 : Finset S := pairs.image g2
  refine ⟨G1 ∪ G2, ?_, ?_, ?_⟩
  · have h1 : G1.card ≤ m := by
      calc G1.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_image_le
        _ = m := by rw [Finset.card_univ, Fintype.card_fin]
    have h2 : G2.card ≤ m.choose 2 := by
      calc G2.card ≤ pairs.card := Finset.card_image_le
        _ = m.choose 2 := card_lt_pairs m
    have h3 : (G1 ∪ G2).card ≤ G1.card + G2.card := Finset.card_union_le G1 G2
    omega
  · intro p hp
    rcases Finset.mem_union.mp hp with hp1 | hp2
    · rcases Finset.mem_image.mp hp1 with ⟨i, _, rfl⟩
      dsimp only [g1]
      have hm := MvPolynomial.totalDegree_mul (a i) (1 + b i)
      have ha1 := MvPolynomial.totalDegree_add (1 : S) (b i)
      rw [MvPolynomial.totalDegree_one] at ha1
      have hda := ha_deg i
      have hdb := hb_deg i
      omega
    · rcases Finset.mem_image.mp hp2 with ⟨⟨i, j⟩, _, rfl⟩
      dsimp only [g2]
      have hadd := MvPolynomial.totalDegree_add (a i * b j) (a j * b i)
      have hm1 := MvPolynomial.totalDegree_mul (a i) (b j)
      have hm2 := MvPolynomial.totalDegree_mul (a j) (b i)
      have hda1 := ha_deg i; have hdb2 := hb_deg j
      have hda2 := ha_deg j; have hdb1 := hb_deg i
      omega
  · intro x
    let α : Fin m → K := fun i => MvPolynomial.eval x (a i)
    let β : Fin m → K := fun i => MvPolynomial.eval x (b i)
    have hstep1 : (∃ u : K, ∀ i, MvPolynomial.eval (Sum.elim x (fun _ => u)) (F i) = 0) ↔
        (∃ u : K, ∀ i, α i + u * β i = 0) := by
      constructor
      · rintro ⟨u, hu⟩; exact ⟨u, fun i => by rw [← eval_decomp x u (F i)]; exact hu i⟩
      · rintro ⟨u, hu⟩; exact ⟨u, fun i => by rw [eval_decomp x u (F i)]; exact hu i⟩
    rw [hstep1, part1_alg α β]
    constructor
    · rintro ⟨h1, h2⟩ p hp
      rcases Finset.mem_union.mp hp with hp1 | hp2
      · rcases Finset.mem_image.mp hp1 with ⟨i, _, rfl⟩
        dsimp only [g1]
        rw [map_mul, map_add, map_one]
        exact h1 i
      · rcases Finset.mem_image.mp hp2 with ⟨⟨i, j⟩, hij, rfl⟩
        dsimp only [g2]
        rw [map_add, map_mul, map_mul]
        exact h2 i j (Finset.mem_filter.mp hij).2
    · intro hG
      refine ⟨fun i => ?_, fun i j hij => ?_⟩
      · have hp : g1 i ∈ G1 ∪ G2 := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        have h0 := hG (g1 i) hp
        dsimp only [g1] at h0
        rw [map_mul, map_add, map_one] at h0
        exact h0
      · have hij_mem : (i, j) ∈ pairs :=
          Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ i, Finset.mem_univ j⟩, hij⟩
        have hp : g2 (i, j) ∈ G1 ∪ G2 := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), hij_mem, rfl⟩)
        have h0 := hG (g2 (i, j)) hp
        dsimp only [g2] at h0
        rw [map_add, map_mul, map_mul] at h0
        exact h0

lemma sum_eval_monomial_eq_zero {N : ℕ} (s : Fin N →₀ ℕ) (c : K) (hdeg : s.sum (fun _ e => e) < N) :
    ∑ x : Fin N → K, MvPolynomial.eval x (MvPolynomial.monomial s c) = 0 := by
  have hex0 : ∃ i0 : Fin N, s i0 = 0 := by
    by_contra hnone
    have hge : ∀ i : Fin N, 1 ≤ s i := fun i => by
      have hne : s i ≠ 0 := fun h => hnone ⟨i, h⟩
      omega
    have hsum : N ≤ ∑ i : Fin N, s i := by
      calc N = ∑ _i : Fin N, 1 := by simp
        _ ≤ ∑ i : Fin N, s i := Finset.sum_le_sum (fun i _ => hge i)
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hdeg
    omega
  rcases hex0 with ⟨i0, hi0⟩
  have hev : ∀ x : Fin N → K, MvPolynomial.eval x (MvPolynomial.monomial s c) =
      c * ∏ i : Fin N, (x i) ^ (s i) := by
    intro x
    rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp_rw [hev, ← Finset.mul_sum]
  have hprod : ∑ x : Fin N → K, ∏ i : Fin N, (x i) ^ (s i) = ∏ i : Fin N, ∑ v : K, v ^ (s i) := by
    have h := Finset.sum_prod_piFinset (ι := Fin N) (Finset.univ : Finset K) (fun i v => v ^ (s i))
    rw [Fintype.piFinset_univ] at h
    exact h
  rw [hprod]
  have hzero : ∑ v : K, v ^ (s i0) = 0 := by
    rw [hi0]
    decide
  rw [Finset.prod_eq_zero (Finset.mem_univ i0) hzero, mul_zero]

lemma full_degree_of_point_support {N : ℕ} (p : MvPolynomial (Fin N) K)
    (h1 : MvPolynomial.eval (fun _ => 1) p ≠ 0)
    (h0 : ∀ x : Fin N → K, (∃ i, x i = 0) → MvPolynomial.eval x p = 0) :
    N ≤ p.totalDegree := by
  by_contra hlt
  have hlt' : p.totalDegree < N := by omega
  have hsum_eq : ∑ x : Fin N → K, MvPolynomial.eval x p = MvPolynomial.eval (fun _ => 1) p := by
    rw [Finset.sum_eq_single (fun _ => 1)]
    · intro x _ hne
      apply h0 x
      by_contra hno0
      apply hne
      funext i
      rcases k_cases (x i) with h | h
      · exact (hno0 ⟨i, h⟩).elim
      · exact h
    · intro hni; exact (hni (Finset.mem_univ _)).elim
  have hsum_zero : ∑ x : Fin N → K, MvPolynomial.eval x p = 0 := by
    conv_lhs => arg 2; ext x; rw [p.as_sum, map_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro s hs
    have hle : s.sum (fun _ e => e) ≤ p.totalDegree :=
      Finset.le_sup (f := fun s : Fin N →₀ ℕ => s.sum fun _ e => e) hs
    exact sum_eval_monomial_eq_zero s (p.coeff s) (lt_of_le_of_lt hle hlt')
  exact h1 (hsum_eq.symm.trans hsum_zero)

lemma part2 (d : ℕ) :
    let bound := 2 * d + 1
    ∃ f : MvPolynomial (Fin bound ⊕ Unit) K, f.totalDegree ≤ d + 1 ∧
      (∀ x : Fin bound → K,
        (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔ ∃ i, x i = 0) ∧
      ∀ G : Finset (MvPolynomial (Fin bound) K),
        (∀ x : Fin bound → K,
          (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔
          ∀ p ∈ G, MvPolynomial.eval x p = 0) →
        ∃ p ∈ G, bound ≤ p.totalDegree := by
  intro bound
  let I1 : Finset (Fin bound) := Finset.univ.filter (fun i => i.val < d + 1)
  let I2 : Finset (Fin bound) := Finset.univ.filter (fun i => d + 1 ≤ i.val)
  have hI1_card : I1.card = d + 1 := by
    have hbij : I1.card = (Finset.univ : Finset (Fin (d + 1))).card := by
      apply Finset.card_bij (fun i hi => ⟨i.val, (Finset.mem_filter.mp hi).2⟩)
      · intro _ _; exact Finset.mem_univ _
      · intro i1 _ i2 _ heq
        exact Fin.ext (congrArg (fun k : Fin (d + 1) => k.val) heq)
      · intro k _
        exact ⟨⟨k.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩
    rw [hbij, Finset.card_univ, Fintype.card_fin]
  have hI2_card : I2.card = d := by
    have hdisj : Disjoint I1 I2 := by
      rw [Finset.disjoint_filter]; intro i _ h1 h2; omega
    have hunion : I1 ∪ I2 = Finset.univ := by
      ext i
      simp only [I1, I2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      omega
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin, hI1_card] at hc
    omega
  let A : MvPolynomial (Fin bound ⊕ Unit) K := ∏ i ∈ I1, MvPolynomial.X (Sum.inl i)
  let B : MvPolynomial (Fin bound ⊕ Unit) K := ∏ i ∈ I2, MvPolynomial.X (Sum.inl i)
  let U : MvPolynomial (Fin bound ⊕ Unit) K := MvPolynomial.X (Sum.inr ())
  let f : MvPolynomial (Fin bound ⊕ Unit) K := A + U * (1 + B)
  have hf_deg : f.totalDegree ≤ d + 1 := by
    have hA : A.totalDegree ≤ d + 1 := by
      calc A.totalDegree ≤ ∑ i ∈ I1, (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin bound ⊕ Unit) K).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ = ∑ _i ∈ I1, 1 := Finset.sum_congr rfl (fun i _ => MvPolynomial.totalDegree_X _)
        _ = I1.card := by simp
        _ = d + 1 := hI1_card
    have hB : B.totalDegree ≤ d := by
      calc B.totalDegree ≤ ∑ i ∈ I2, (MvPolynomial.X (Sum.inl i) : MvPolynomial (Fin bound ⊕ Unit) K).totalDegree :=
            MvPolynomial.totalDegree_finsetProd _ _
        _ = ∑ _i ∈ I2, 1 := Finset.sum_congr rfl (fun i _ => MvPolynomial.totalDegree_X _)
        _ = I2.card := by simp
        _ = d := hI2_card
    have hU : U.totalDegree = 1 := MvPolynomial.totalDegree_X _
    have h1B := MvPolynomial.totalDegree_add (1 : MvPolynomial (Fin bound ⊕ Unit) K) B
    rw [MvPolynomial.totalDegree_one] at h1B
    have hmul := MvPolynomial.totalDegree_mul U (1 + B)
    have hadd := MvPolynomial.totalDegree_add A (U * (1 + B))
    change (A + U * (1 + B)).totalDegree ≤ d + 1
    omega
  have hf_sol : ∀ x : Fin bound → K,
      (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔ ∃ i, x i = 0 := by
    intro x
    have hev : ∀ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f =
        (∏ i ∈ I1, x i) + u * (1 + ∏ i ∈ I2, x i) := by
      intro u
      simp only [f, A, B, U, map_add, map_mul, map_one, map_prod, MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr]
    constructor
    · rintro ⟨u, hu⟩
      by_contra hno0
      have hx1 : ∀ i, x i = 1 := fun i => by
        rcases k_cases (x i) with h | h
        · exact (hno0 ⟨i, h⟩).elim
        · exact h
      rw [hev u] at hu
      have hp1 : ∏ i ∈ I1, x i = 1 := Finset.prod_eq_one (fun i _ => hx1 i)
      have hp2 : ∏ i ∈ I2, x i = 1 := Finset.prod_eq_one (fun i _ => hx1 i)
      rw [hp1, hp2, k_add_self 1, mul_zero, add_zero] at hu
      exact (by decide : (1 : K) ≠ 0) hu
    · rintro ⟨i0, hi0⟩
      by_cases h1 : i0.val < d + 1
      · refine ⟨0, ?_⟩
        rw [hev 0, zero_mul, add_zero]
        exact Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩) hi0
      · refine ⟨∏ i ∈ I1, x i, ?_⟩
        rw [hev (∏ i ∈ I1, x i)]
        have hp2 : ∏ i ∈ I2, x i = 0 :=
          Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩) hi0
        rw [hp2, add_zero, mul_one, k_add_self]
  refine ⟨f, hf_deg, hf_sol, ?_⟩
  intro G hG
  have h1_not : ¬ (∀ p ∈ G, MvPolynomial.eval (fun _ => 1) p = 0) := by
    intro hall
    have hsol := (hG (fun _ => 1)).mpr hall
    rcases (hf_sol (fun _ => 1)).mp hsol with ⟨i, hi⟩
    exact (by decide : (1 : K) ≠ 0) hi
  have hexp : ∃ p ∈ G, MvPolynomial.eval (fun _ => 1) p ≠ 0 := by
    by_contra hnone
    apply h1_not
    intro p hp
    by_contra hne
    exact hnone ⟨p, hp, hne⟩
  rcases hexp with ⟨p, hpG, hp1⟩
  refine ⟨p, hpG, full_degree_of_point_support p hp1 ?_⟩
  intro x hx0
  exact (hG x).mp ((hf_sol x).mpr hx0) p hpG

lemma main_proof : ∀ d : ℕ,
  let K := ZMod 2
  let bound := 2*d+1
  (∀ n m : ℕ,
    let P := MvPolynomial (Fin n ⊕ Unit) K
    let S := MvPolynomial (Fin n) K
    ∀ F : Fin m → P, (∀ i, (F i).totalDegree ≤ d+1) →
      ∃ G : Finset S, G.card ≤ m + m.choose 2 ∧
        (∀ p ∈ G, p.totalDegree ≤ bound) ∧
        ∀ x : Fin n → K,
          (∃ u : K, ∀ i, MvPolynomial.eval (Sum.elim x (fun _ => u)) (F i) = 0) ↔
          ∀ p ∈ G, MvPolynomial.eval x p = 0) ∧
  ∃ f : MvPolynomial (Fin bound ⊕ Unit) K, f.totalDegree ≤ d+1 ∧
    (∀ x : Fin bound → K,
      (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔ ∃ i, x i = 0) ∧
    ∀ G : Finset (MvPolynomial (Fin bound) K),
      (∀ x : Fin bound → K,
        (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔
        ∀ p ∈ G, MvPolynomial.eval x p = 0) →
      ∃ p ∈ G, bound ≤ p.totalDegree :=
  fun d => ⟨fun n m => part1 d n m, part2 d⟩

end PEqualNP.Outside.L_pcx_448_aux

theorem PEqualNP.Outside.L_pcx_448 : (∀ d : ℕ,
  let K := ZMod 2
  let bound := 2*d+1
  (∀ n m : ℕ,
    let P := MvPolynomial (Fin n ⊕ Unit) K
    let S := MvPolynomial (Fin n) K
    ∀ F : Fin m → P, (∀ i, (F i).totalDegree ≤ d+1) →
      ∃ G : Finset S, G.card ≤ m + m.choose 2 ∧
        (∀ p ∈ G, p.totalDegree ≤ bound) ∧
        ∀ x : Fin n → K,
          (∃ u : K, ∀ i, MvPolynomial.eval (Sum.elim x (fun _ => u)) (F i) = 0) ↔
          ∀ p ∈ G, MvPolynomial.eval x p = 0) ∧
  ∃ f : MvPolynomial (Fin bound ⊕ Unit) K, f.totalDegree ≤ d+1 ∧
    (∀ x : Fin bound → K,
      (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔ ∃ i, x i = 0) ∧
    ∀ G : Finset (MvPolynomial (Fin bound) K),
      (∀ x : Fin bound → K,
        (∃ u : K, MvPolynomial.eval (Sum.elim x (fun _ => u)) f = 0) ↔
        ∀ p ∈ G, MvPolynomial.eval x p = 0) →
      ∃ p ∈ G, bound ≤ p.totalDegree) :=
  PEqualNP.Outside.L_pcx_448_aux.main_proof
