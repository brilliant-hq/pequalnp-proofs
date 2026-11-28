import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1236_aux

section MultiIndex

def multiIdx (q d : ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset (fun _ : Fin q => Finset.range (d + 1))).filter (fun α => ∑ i : Fin q, α i ≤ d)

lemma mem_multiIdx {q d : ℕ} {α : Fin q → ℕ} :
    α ∈ multiIdx q d ↔ ∑ i : Fin q, α i ≤ d := by
  simp only [multiIdx, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hsum
    refine ⟨fun i => ?_, hsum⟩
    have hi : α i ≤ ∑ j : Fin q, α j :=
      Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

lemma card_multiIdx : ∀ (q d : ℕ), (multiIdx q d).card = Nat.choose (q + d) d
  | 0, d => by
    have h1 : multiIdx 0 d = {Fin.elim0} := by
      ext α
      rw [mem_multiIdx, Finset.mem_singleton]
      constructor
      · intro _; funext i; exact Fin.elim0 i
      · intro _; simp
    rw [h1, Finset.card_singleton, zero_add, Nat.choose_self]
  | q + 1, 0 => by
    have h1 : multiIdx (q + 1) 0 = {fun _ => 0} := by
      ext α
      simp only [mem_multiIdx, Finset.mem_singleton]
      constructor
      · intro hsum
        funext i
        have hi : α i ≤ ∑ j : Fin (q + 1), α j :=
          Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        omega
      · intro h; subst h; simp
    rw [h1, Finset.card_singleton, add_zero, Nat.choose_zero_right]
  | q + 1, d + 1 => by
    let S0 := (multiIdx (q + 1) (d + 1)).filter (fun α => α 0 = 0)
    let S1 := (multiIdx (q + 1) (d + 1)).filter (fun α => ¬ α 0 = 0)
    have hsplit : (multiIdx (q + 1) (d + 1)).card = S0.card + S1.card := by
      have hdisj : Disjoint S0 S1 :=
        Finset.disjoint_filter.mpr (fun _ _ h1 h2 => h2 h1)
      rw [← Finset.card_union_of_disjoint hdisj]
      congr 1
      ext α
      simp only [S0, S1, Finset.mem_union, Finset.mem_filter]
      tauto
    have hS0 : S0.card = (multiIdx q (d + 1)).card := by
      refine Finset.card_bij (fun α _ => Fin.tail α) ?_ ?_ ?_
      · intro α hα
        simp only [S0, Finset.mem_filter, mem_multiIdx] at hα ⊢
        have hsum := hα.1
        rw [Fin.sum_univ_succ, hα.2, zero_add] at hsum
        exact hsum
      · intro α1 h1 α2 h2 heq
        simp only [S0, Finset.mem_filter] at h1 h2
        funext i
        refine Fin.cases ?_ ?_ i
        · rw [h1.2, h2.2]
        · intro j; exact congrFun heq j
      · intro β hβ
        rw [mem_multiIdx] at hβ
        refine ⟨Fin.cons 0 β, ?_, by funext j; simp⟩
        simp only [S0, Finset.mem_filter, mem_multiIdx, Fin.cons_zero]
        refine ⟨?_, trivial⟩
        rw [Fin.sum_univ_succ, Fin.cons_zero, zero_add]
        simpa using hβ
    have hS1 : S1.card = (multiIdx (q + 1) d).card := by
      let dec0 : (Fin (q + 1) → ℕ) → (Fin (q + 1) → ℕ) :=
        fun α i => if i = 0 then α 0 - 1 else α i
      let inc0 : (Fin (q + 1) → ℕ) → (Fin (q + 1) → ℕ) :=
        fun β i => if i = 0 then β 0 + 1 else β i
      refine Finset.card_bij (fun α _ => dec0 α) ?_ ?_ ?_
      · intro α hα
        simp only [S1, Finset.mem_filter, mem_multiIdx] at hα ⊢
        have hsum := hα.1
        rw [Fin.sum_univ_succ] at hsum ⊢
        have htail : (∑ x : Fin q, dec0 α x.succ) = ∑ x : Fin q, α x.succ := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp [dec0, Fin.succ_ne_zero]
        rw [htail]
        simp only [dec0, ↓reduceIte]
        have hpos : 0 < α 0 := Nat.pos_of_ne_zero hα.2
        omega
      · intro α1 h1 α2 h2 heq
        simp only [S1, Finset.mem_filter] at h1 h2
        funext i
        by_cases hi : i = 0
        · subst hi
          have h0 := congrFun heq 0
          simp only [dec0, ↓reduceIte] at h0
          have hp1 : 0 < α1 0 := Nat.pos_of_ne_zero h1.2
          have hp2 : 0 < α2 0 := Nat.pos_of_ne_zero h2.2
          omega
        · have h0 := congrFun heq i
          simp only [dec0, hi, ↓reduceIte] at h0
          exact h0
      · intro β hβ
        rw [mem_multiIdx] at hβ
        refine ⟨inc0 β, ?_, ?_⟩
        · simp only [S1, Finset.mem_filter, mem_multiIdx]
          refine ⟨?_, by simp [inc0]⟩
          rw [Fin.sum_univ_succ] at hβ ⊢
          have htail : (∑ x : Fin q, inc0 β x.succ) = ∑ x : Fin q, β x.succ := by
            refine Finset.sum_congr rfl fun x _ => ?_
            simp [inc0, Fin.succ_ne_zero]
          rw [htail]
          simp only [inc0, ↓reduceIte]
          omega
        · funext i
          by_cases hi : i = 0
          · subst hi; simp [dec0, inc0]
          · simp [dec0, inc0, hi]
    rw [hsplit, hS0, hS1, card_multiIdx q (d + 1), card_multiIdx (q + 1) d]
    have h1 : q + 1 + (d + 1) = (q + d + 1) + 1 := by omega
    have h2 : q + (d + 1) = q + d + 1 := by omega
    have h3 : q + 1 + d = q + d + 1 := by omega
    rw [h1, h2, h3]
    rw [Nat.choose_succ_succ (q + d + 1) d, add_comm]

lemma sum_pow_eq_sum_pi {q : ℕ} (f : Fin q → ℚ) :
    ∀ k : ℕ, (∑ u : Fin q, f u) ^ k = ∑ s : Fin k → Fin q, ∏ j : Fin k, f (s j)
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ', sum_pow_eq_sum_pi f k, Finset.sum_mul_sum]
    have heq : (∑ x : Fin q, ∑ y : Fin k → Fin q, f x * ∏ j : Fin k, f (y j)) =
        ∑ p : Fin q × (Fin k → Fin q), f p.1 * ∏ j : Fin k, f (p.2 j) :=
      (Fintype.sum_prod_type (fun p : Fin q × (Fin k → Fin q) => f p.1 * ∏ j : Fin k, f (p.2 j))).symm
    rw [heq]
    let e : (Fin q × (Fin k → Fin q)) ≃ (Fin (k + 1) → Fin q) :=
      { toFun := fun p => Fin.cons p.1 p.2
        invFun := fun s => (s 0, Fin.tail s)
        left_inv := fun ⟨a, g⟩ => Prod.ext rfl (by funext j; simp)
        right_inv := fun s => by funext i; refine Fin.cases rfl (fun j => rfl) i }
    refine Fintype.sum_equiv e _ _ (fun ⟨a, g⟩ => ?_)
    simp only [e, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

def freq {k q : ℕ} (s : Fin k → Fin q) : Fin q → ℕ :=
  fun u => (Finset.univ.filter (fun j : Fin k => s j = u)).card

def multiCount (k q : ℕ) (α : Fin q → ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Fin k → Fin q => freq s = α)).card

lemma sum_freq {k q : ℕ} (s : Fin k → Fin q) : ∑ u : Fin q, freq s u = k := by
  simp only [freq, Finset.card_filter]
  rw [Finset.sum_comm]
  simp

lemma prod_comp_eq_prod_pow_freq {k q : ℕ} (s : Fin k → Fin q) (g : Fin q → ℚ) :
    ∏ j : Fin k, g (s j) = ∏ u : Fin q, g u ^ freq s u := by
  have hfib := (Finset.prod_fiberwise_of_maps_to (s := (Finset.univ : Finset (Fin k)))
    (t := (Finset.univ : Finset (Fin q))) (g := s) (f := fun j => g (s j))
    (fun _ _ => Finset.mem_univ _)).symm
  rw [hfib]
  refine Finset.prod_congr rfl fun u _ => ?_
  have hcongr : (∏ j ∈ Finset.univ.filter (fun j : Fin k => s j = u), g (s j)) =
      ∏ _j ∈ Finset.univ.filter (fun j : Fin k => s j = u), g u :=
    Finset.prod_congr rfl (fun j hj => by rw [(Finset.mem_filter.mp hj).2])
  rw [hcongr, Finset.prod_const]
  rfl

lemma sum_mul_pow_expand {q d k : ℕ} (hk : k ≤ d) (a b : Fin q → ℚ) :
    (∑ u : Fin q, a u * b u) ^ k =
      ∑ α ∈ multiIdx q d,
        (multiCount k q α : ℚ) *
          (∏ u : Fin q, a u ^ α u) * (∏ u : Fin q, b u ^ α u) := by
  rw [sum_pow_eq_sum_pi]
  have hmap : ∀ s ∈ (Finset.univ : Finset (Fin k → Fin q)), freq s ∈ multiIdx q d := by
    intro s _
    rw [mem_multiIdx, sum_freq]
    exact hk
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hterm : ∀ s ∈ Finset.univ.filter (fun s : Fin k → Fin q => freq s = α),
      (∏ j : Fin k, (a (s j) * b (s j))) =
        (∏ u : Fin q, a u ^ α u) * (∏ u : Fin q, b u ^ α u) := by
    intro s hs
    have hfs : freq s = α := (Finset.mem_filter.mp hs).2
    rw [Finset.prod_mul_distrib, prod_comp_eq_prod_pow_freq, prod_comp_eq_prod_pow_freq, hfs]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_assoc]
  rfl

end MultiIndex

section HadamardRank

def ip {m : ℕ} (x y : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin m => x i && y i)).card

def had {m : ℕ} (x y : Fin m → Bool) : ℚ :=
  (-1 : ℚ) ^ ip x y

lemma had_eq_prod {m : ℕ} (x y : Fin m → Bool) :
    had x y = ∏ i : Fin m, (if x i && y i then (-1 : ℚ) else 1) := by
  dsimp only [had, ip]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

lemma had_ortho {m : ℕ} (x y : Fin m → Bool) :
    ∑ g : Fin m → Bool, had x g * had y g = if x = y then (2 : ℚ) ^ m else 0 := by
  have h1 : ∀ g : Fin m → Bool, had x g * had y g =
      ∏ i : Fin m, ((if x i && g i then (-1 : ℚ) else 1) * (if y i && g i then (-1 : ℚ) else 1)) := by
    intro g
    rw [had_eq_prod, had_eq_prod, Finset.prod_mul_distrib]
  simp_rw [h1]
  have hps := (Fintype.prod_sum (fun (i : Fin m) (b : Bool) =>
    (if x i && b then (-1 : ℚ) else 1) * (if y i && b then (-1 : ℚ) else 1))).symm
  rw [hps]
  have hcoord : ∀ i : Fin m,
      (∑ b : Bool, (if x i && b then (-1 : ℚ) else 1) * (if y i && b then (-1 : ℚ) else 1)) =
        if x i = y i then (2 : ℚ) else 0 := by
    intro i
    rw [Fintype.sum_bool]
    cases x i <;> cases y i <;> norm_num
  simp_rw [hcoord]
  by_cases hxy : x = y
  · subst hxy
    simp
  · rw [if_neg hxy]
    have hex : ∃ i : Fin m, x i ≠ y i := by
      by_contra hall
      push Not at hall
      exact hxy (funext hall)
    rcases hex with ⟨i, hi⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma rank_bound_from_had_factor {m : ℕ} {ι : Type*} [Fintype ι]
    (e : (Fin m → Bool) ≃ (Fin m → Bool))
    (F G : ι → (Fin m → Bool) → ℚ)
    (hfac : ∀ f g, had (e f) g = ∑ α : ι, F α f * G α g) :
    2 ^ m ≤ Fintype.card ι := by
  let W := Fin m → Bool
  let Φ : (W → ℚ) →ₗ[ℚ] (ι → ℚ) :=
    { toFun := fun v α => ∑ f : W, v f * F α f
      map_add' := fun v1 v2 => by
        funext α
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        funext α
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum] }
  have hInj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have hPsi : ∀ g : W, ∑ f : W, v f * had (e f) g = 0 := by
      intro g
      calc ∑ f : W, v f * had (e f) g
          = ∑ f : W, v f * ∑ α : ι, F α f * G α g := by simp_rw [hfac]
        _ = ∑ f : W, ∑ α : ι, (v f * F α f) * G α g := by
            refine Finset.sum_congr rfl fun f _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun α _ => by ring
        _ = ∑ α : ι, (∑ f : W, v f * F α f) * G α g := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun α _ => by rw [Finset.sum_mul]
        _ = ∑ α : ι, Φ v α * G α g := rfl
        _ = 0 := by simp [hv]
    funext f0
    have h0 : ∑ g : W, had (e f0) g * ∑ f : W, v f * had (e f) g = 0 := by
      simp [hPsi]
    have h1 : ∑ g : W, had (e f0) g * ∑ f : W, v f * had (e f) g = (2 : ℚ) ^ m * v f0 := by
      calc ∑ g : W, had (e f0) g * ∑ f : W, v f * had (e f) g
          = ∑ g : W, ∑ f : W, v f * (had (e f0) g * had (e f) g) := by
            refine Finset.sum_congr rfl fun g _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun f _ => by ring
        _ = ∑ f : W, v f * ∑ g : W, had (e f0) g * had (e f) g := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun f _ => by rw [Finset.mul_sum]
        _ = ∑ f : W, v f * (if e f0 = e f then (2 : ℚ) ^ m else 0) := by
            refine Finset.sum_congr rfl fun f _ => by rw [had_ortho]
        _ = ∑ f : W, if f = f0 then v f * (2 : ℚ) ^ m else 0 := by
            refine Finset.sum_congr rfl fun f _ => ?_
            by_cases hf : f = f0
            · subst hf; simp
            · have hne : e f0 ≠ e f := fun h => hf (e.injective h).symm
              simp [hf, hne]
        _ = (2 : ℚ) ^ m * v f0 := by
            rw [Finset.sum_ite_eq' Finset.univ f0]
            simp [mul_comm]
    rw [h1] at h0
    have hpow : (2 : ℚ) ^ m ≠ 0 := by positivity
    exact (mul_eq_zero.mp h0).resolve_left hpow
  have hle := LinearMap.finrank_le_finrank_of_injective hInj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hle
  have hcardW : Fintype.card W = 2 ^ m := by
    simp [W]
  omega

end HadamardRank

section ArithBound

lemma degree_quarter_bound (m d : ℕ) (hm : 1 ≤ m) (hch : 2 ^ m ≤ Nat.choose (m + d) d) :
    m < 4 * d := by
  by_contra hle
  push Not at hle
  have hbinom : 4 ^ m * Nat.choose (m + d) m ≤ 5 ^ (m + d) := by
    have hpow : (4 + 1 : ℕ) ^ (m + d) =
        ∑ k ∈ Finset.range (m + d + 1), 4 ^ k * 1 ^ (m + d - k) * Nat.choose (m + d) k := by
      exact add_pow 4 1 (m + d)
    have hterm : 4 ^ m * 1 ^ (m + d - m) * Nat.choose (m + d) m ≤
        ∑ k ∈ Finset.range (m + d + 1), 4 ^ k * 1 ^ (m + d - k) * Nat.choose (m + d) k :=
      Finset.single_le_sum (f := fun k => 4 ^ k * 1 ^ (m + d - k) * Nat.choose (m + d) k)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
    simp only [one_pow, mul_one] at hterm hpow
    change 4 ^ m * (m + d).choose m ≤ (4 + 1) ^ (m + d)
    rw [hpow]
    exact hterm
  have hsymm : Nat.choose (m + d) m = Nat.choose (m + d) d := Nat.choose_symm_add
  rw [hsymm] at hbinom
  have h8 : 8 ^ m ≤ 5 ^ (m + d) := by
    calc 8 ^ m = (4 * 2) ^ m := by norm_num
      _ = 4 ^ m * 2 ^ m := Nat.mul_pow 4 2 m
      _ ≤ 4 ^ m * Nat.choose (m + d) d := Nat.mul_le_mul_left _ hch
      _ ≤ 5 ^ (m + d) := hbinom
  have h4096 : 4096 ^ m ≤ 3125 ^ m := by
    calc 4096 ^ m = (8 ^ 4) ^ m := by norm_num
      _ = (8 ^ m) ^ 4 := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ (5 ^ (m + d)) ^ 4 := Nat.pow_le_pow_left h8 4
      _ = 5 ^ (4 * m + 4 * d) := by rw [← pow_mul]; congr 1; ring
      _ ≤ 5 ^ (5 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = (5 ^ 5) ^ m := by rw [pow_mul]
      _ = 3125 ^ m := by norm_num
  have hlt : 3125 ^ m < 4096 ^ m := Nat.pow_lt_pow_left (by norm_num) (by omega)
  omega

end ArithBound

section MainProof

theorem main :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m N : Nat) (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
  (left right : (Fin m → Bool) → Fin N → Bool),
  (∀ u, u ∉ H u) → (∀ u v, v ∈ H u ↔ u ∈ H v) →
  let lhs := (Finset.univ : Finset (Fin N)).filter (fun v => side v = false)
  let unions := lhs.powerset.image (fun S => S.biUnion
    (fun v => (H v).filter (fun w => side w = true)))
  let q := unions.card
  let total := fun (f g : Fin m → Bool) =>
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
      ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
  (∃ A B : (Fin m → Bool) → ↥unions → Nat,
    ∀ f g, total f g = ∑ U, A f U * B g U) ∧
  ∀ (P : Polynomial ℚ) (e : (Fin m → Bool) ≃ (Fin m → Bool)),
    (∀ f g, P.eval (total f g : ℚ) =
      (if ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card % 2 = 1
       then (1 : ℚ) else 0)) →
    2^m ≤ Nat.choose (q + P.natDegree) P.natDegree ∧
    (q ≤ m → m < 4*P.natDegree) := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro m N H side left right _hIrr hSym
  dsimp only
  let lhs : Finset (Fin N) := (Finset.univ : Finset (Fin N)).filter (fun v => side v = false)
  let rhs : Finset (Fin N) := (Finset.univ : Finset (Fin N)).filter (fun v => side v = true)
  let crossNb : Finset (Fin N) → Finset (Fin N) :=
    fun S => S.biUnion (fun v => (H v).filter (fun w => side w = true))
  let unions : Finset (Finset (Fin N)) := lhs.powerset.image crossNb
  let q := unions.card
  let total : (Fin m → Bool) → (Fin m → Bool) → ℕ := fun f g =>
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
      ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
  let Aset : (Fin m → Bool) → ↥unions → Finset (Finset (Fin N)) := fun f U =>
    lhs.powerset.filter (fun S =>
      crossNb S = U.val ∧ (∀ v ∈ S, left f v = true) ∧ ∀ u ∈ S, ∀ v ∈ H u, v ∉ S)
  let Bset : (Fin m → Bool) → ↥unions → Finset (Finset (Fin N)) := fun g U =>
    rhs.powerset.filter (fun T =>
      (∀ w ∈ T, right g w = true) ∧ (∀ u ∈ T, ∀ v ∈ H u, v ∉ T) ∧ ∀ w ∈ T, w ∉ U.val)
  let A : (Fin m → Bool) → ↥unions → ℕ := fun f U => (Aset f U).card
  let B : (Fin m → Bool) → ↥unions → ℕ := fun g U => (Bset g U).card
  have hFactor : ∀ f g, total f g = ∑ U : ↥unions, A f U * B g U := by
    intro f g
    dsimp only [total, A, B]
    have hsum_card : (∑ U : ↥unions, (Aset f U).card * (Bset g U).card) =
        ((Finset.univ : Finset ↥unions).sigma (fun U => Aset f U ×ˢ Bset g U)).card := by
      rw [Finset.card_sigma]
      refine Finset.sum_congr rfl fun U _ => (Finset.card_product _ _).symm
    rw [hsum_card]
    refine Finset.card_bij
      (fun I _ =>
        let S := I.filter (fun v => side v = false)
        let T := I.filter (fun v => side v = true)
        have hSsub : S ⊆ lhs := by
          intro v hv
          simp only [S, lhs, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          exact hv.2
        have hUmem : crossNb S ∈ unions := Finset.mem_image.mpr ⟨S, Finset.mem_powerset.mpr hSsub, rfl⟩
        ⟨⟨crossNb S, hUmem⟩, (S, T)⟩) ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
      rcases hI with ⟨hLive, hInd⟩
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_univ _, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
      · rw [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, rfl, ?_, ?_⟩
        · intro v hv
          simp only [lhs, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
          exact hv.2
        · intro v hv
          simp only [Finset.mem_filter] at hv
          have hl := hLive v hv.1
          simpa [hv.2] using hl
        · intro u hu v hv
          simp only [Finset.mem_filter] at hu ⊢
          intro hvin
          exact hInd u hu.1 v hv hvin.1
      · rw [Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro w hw
          simp only [rhs, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
          exact hw.2
        · intro w hw
          simp only [Finset.mem_filter] at hw
          have hl := hLive w hw.1
          simpa [hw.2] using hl
        · intro u hu v hv
          simp only [Finset.mem_filter] at hu ⊢
          intro hvin
          exact hInd u hu.1 v hv hvin.1
        · intro w hw hwc
          simp only [Finset.mem_filter] at hw
          simp only [crossNb, Finset.mem_biUnion, Finset.mem_filter] at hwc
          rcases hwc with ⟨u, ⟨huI, _⟩, huv, _⟩
          exact hInd u huI w huv hw.1
    · intro I1 _ I2 _ hEq
      have hST : (I1.filter (fun v => side v = false), I1.filter (fun v => side v = true)) =
          (I2.filter (fun v => side v = false), I2.filter (fun v => side v = true)) :=
        eq_of_heq (Sigma.mk.inj_iff.mp hEq).2
      have hS := congrArg Prod.fst hST
      have hT := congrArg Prod.snd hST
      ext v
      cases hv : side v
      · have := Finset.ext_iff.mp hS v
        simpa [hv] using this
      · have := Finset.ext_iff.mp hT v
        simpa [hv] using this
    · rintro ⟨U, ⟨S, T⟩⟩ hST
      simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_product,
        Aset, Bset, Finset.mem_filter, Finset.mem_powerset] at hST
      rcases hST with ⟨⟨hSsub, hScross, hSlive, hSind⟩, ⟨hTsub, hTlive, hTind, hTdisj⟩⟩
      have hSside : ∀ v ∈ S, side v = false := fun v hv => (Finset.mem_filter.mp (hSsub hv)).2
      have hTside : ∀ w ∈ T, side w = true := fun w hw => (Finset.mem_filter.mp (hTsub hw)).2
      refine ⟨S ∪ T, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · intro v hv
          rcases Finset.mem_union.mp hv with hvS | hvT
          · rw [hSside v hvS]; simpa using hSlive v hvS
          · rw [hTside v hvT]; simpa using hTlive v hvT
        · intro u hu v huv hvin
          rcases Finset.mem_union.mp hu with huS | huT
          · rcases Finset.mem_union.mp hvin with hvS | hvT
            · exact hSind u huS v huv hvS
            · have hvU : v ∈ U.val := by
                rw [← hScross]
                exact Finset.mem_biUnion.mpr ⟨u, huS, Finset.mem_filter.mpr ⟨huv, hTside v hvT⟩⟩
              exact hTdisj v hvT hvU
          · rcases Finset.mem_union.mp hvin with hvS | hvT
            · have huU : u ∈ U.val := by
                rw [← hScross]
                exact Finset.mem_biUnion.mpr ⟨v, hvS, Finset.mem_filter.mpr ⟨(hSym u v).mp huv, hTside u huT⟩⟩
              exact hTdisj u huT huU
            · exact hTind u huT v huv hvT
      · have hfS : (S ∪ T).filter (fun v => side v = false) = S := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hvS | hvT, hsf⟩
            · exact hvS
            · rw [hTside v hvT] at hsf; cases hsf
          · intro hvS; exact ⟨Or.inl hvS, hSside v hvS⟩
        have hfT : (S ∪ T).filter (fun v => side v = true) = T := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_union]
          constructor
          · rintro ⟨hvS | hvT, hst⟩
            · rw [hSside v hvS] at hst; cases hst
            · exact hvT
          · intro hvT; exact ⟨Or.inr hvT, hTside v hvT⟩
        apply Sigma.ext
        · apply Subtype.ext
          dsimp only
          rw [hfS, hScross]
        · refine heq_of_eq (Prod.ext hfS hfT)
  refine ⟨⟨A, B, hFactor⟩, ?_⟩
  intro P e hP
  set d := P.natDegree
  have hchoose_bound : 2 ^ m ≤ Nat.choose (q + d) d := by
    let eU : ↥unions ≃ Fin q := Fintype.equivFinOfCardEq (Fintype.card_coe unions)
    let aQ : (Fin m → Bool) → Fin q → ℚ := fun f u => (A f (eU.symm u) : ℚ)
    let bQ : (Fin m → Bool) → Fin q → ℚ := fun g u => (B g (eU.symm u) : ℚ)
    have htotQ : ∀ f g, (total f g : ℚ) = ∑ u : Fin q, aQ f u * bQ g u := by
      intro f g
      rw [hFactor f g]
      push_cast
      exact Fintype.sum_equiv eU _ _ (fun U => by simp [aQ, bQ])
    let Q : Polynomial ℚ := Polynomial.C 1 - Polynomial.C 2 * P
    have hQdeg : Q.natDegree ≤ d := by
      refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
      rw [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)]
      exact Polynomial.natDegree_C_mul_le 2 P
    have hQeval : ∀ f g, Q.eval (total f g : ℚ) = had (e f) g := by
      intro f g
      dsimp only [Q, total]
      rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_C, hP f g]
      have hip_eq : ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card = ip (e f) g := by
        dsimp only [ip]
        congr 1; ext i; simp
      rw [hip_eq]
      dsimp only [had]
      have hmod : ip (e f) g % 2 = 0 ∨ ip (e f) g % 2 = 1 := Nat.mod_two_eq_zero_or_one _
      rcases hmod with h0 | h1
      · rw [h0]
        rw [if_neg Nat.zero_ne_one, mul_zero, sub_zero]
        have heven : Even (ip (e f) g) := Nat.even_iff.mpr h0
        rw [heven.neg_one_pow]
      · rw [h1]
        simp only [↓reduceIte, mul_one]
        have hodd : Odd (ip (e f) g) := Nat.odd_iff.mpr h1
        rw [hodd.neg_one_pow]
        norm_num
    let F : ↥(multiIdx q d) → (Fin m → Bool) → ℚ := fun α f =>
      (∑ k ∈ Finset.range (d + 1),
        Q.coeff k * (multiCount k q α.val : ℚ)) *
      (∏ u : Fin q, aQ f u ^ α.val u)
    let G : ↥(multiIdx q d) → (Fin m → Bool) → ℚ := fun α g =>
      ∏ u : Fin q, bQ g u ^ α.val u
    have hfac : ∀ f g, had (e f) g = ∑ α : ↥(multiIdx q d), F α f * G α g := by
      intro f g
      rw [← hQeval f g, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hQdeg)]
      simp_rw [htotQ f g]
      have hstep : (∑ k ∈ Finset.range (d + 1), Q.coeff k * (∑ u : Fin q, aQ f u * bQ g u) ^ k) =
          ∑ k ∈ Finset.range (d + 1), ∑ α ∈ multiIdx q d,
            (Q.coeff k * (multiCount k q α : ℚ)) *
              ((∏ u : Fin q, aQ f u ^ α u) * (∏ u : Fin q, bQ g u ^ α u)) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [sum_mul_pow_expand hk' (aQ f) (bQ g), Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => by ring
      rw [hstep, Finset.sum_comm, ← Finset.sum_attach (multiIdx q d)]
      refine Finset.sum_congr rfl fun α _ => ?_
      dsimp only [F, G]
      rw [← Finset.sum_mul, mul_assoc]
    have hrb := rank_bound_from_had_factor e F G hfac
    rw [Fintype.card_coe, card_multiIdx] at hrb
    exact hrb
  refine ⟨hchoose_bound, ?_⟩
  intro hqm
  have hq_pos : 1 ≤ q := by
    have hmem : crossNb ∅ ∈ unions :=
      Finset.mem_image.mpr ⟨∅, Finset.mem_powerset.mpr (Finset.empty_subset _), rfl⟩
    exact Finset.card_pos.mpr ⟨crossNb ∅, hmem⟩
  have hqm' : q ≤ m := hqm
  have hch_m : 2 ^ m ≤ Nat.choose (m + d) d :=
    le_trans hchoose_bound (Nat.choose_le_choose d (Nat.add_le_add_right hqm' d))
  exact degree_quarter_bound m d (le_trans hq_pos hqm') hch_m

end MainProof

end PEqualNP.Outside.L_lib_1236_aux

theorem PEqualNP.Outside.L_lib_1236 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m N : Nat) (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
  (left right : (Fin m → Bool) → Fin N → Bool),
  (∀ u, u ∉ H u) → (∀ u v, v ∈ H u ↔ u ∈ H v) →
  let lhs := (Finset.univ : Finset (Fin N)).filter (fun v => side v = false)
  let unions := lhs.powerset.image (fun S => S.biUnion
    (fun v => (H v).filter (fun w => side w = true)))
  let q := unions.card
  let total := fun (f g : Fin m → Bool) =>
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
      ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
  (∃ A B : (Fin m → Bool) → ↥unions → Nat,
    ∀ f g, total f g = ∑ U, A f U * B g U) ∧
  ∀ (P : Polynomial ℚ) (e : (Fin m → Bool) ≃ (Fin m → Bool)),
    (∀ f g, P.eval (total f g : ℚ) =
      (if ((Finset.univ : Finset (Fin m)).filter (fun i => e f i && g i)).card % 2 = 1
       then (1 : ℚ) else 0)) →
    2^m ≤ Nat.choose (q + P.natDegree) P.natDegree ∧
    (q ≤ m → m < 4*P.natDegree) :=
  PEqualNP.Outside.L_lib_1236_aux.main
