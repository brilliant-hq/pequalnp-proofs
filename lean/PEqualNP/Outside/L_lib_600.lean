import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_600

def sat {n : ℕ} (C : Finset ((Fin n × Bool) × (Fin n × Bool))) (w : Fin n → Bool) : Bool :=
  decide (∀ c ∈ C, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)

def satSet {n : ℕ} (C : Finset ((Fin n × Bool) × (Fin n × Bool))) : Finset (Fin n → Bool) :=
  Finset.univ.filter (fun z => sat C z = true)

def hasCert {n : ℕ} (S : Finset (Fin n → Bool)) (k : ℕ) : Prop :=
  ∀ x ∈ S, ∃ T : Finset (Fin n), T.card ≤ k ∧
    ∀ y : Fin n → Bool, (∀ i ∈ T, y i = x i) → y ∈ S

def hasHalf {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∃ (j : Fin n) (v : Bool), ∀ p : Fin n → Bool, p j = v → p ∈ S

def hasShape {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  ∃ (sites : Fin 5 → Fin n) (signs : Fin 5 → Bool),
    Function.Injective sites ∧ ∀ word : Fin n → Bool,
      let mark := fun k : Fin 5 => word (sites k) = signs k
      (word ∈ S) ↔ (¬(mark 0 ∧ (mark 1 ∨ mark 2)) ∧ ¬(mark 3 ∧ mark 4))

def mainGoal {n : ℕ} (S : Finset (Fin n → Bool)) : Prop :=
  (2 ^ n ≤ 2 * S.card → hasHalf S ∨ hasCert S 2) ∧
  (2 * S.card = 2 ^ n → hasCert S 2) ∧
  (7 * 2 ^ n < 16 * S.card ∧ 2 * S.card < 2 ^ n → hasShape S)

lemma mem_satSet_eq {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))} {w : Fin n → Bool} :
    w ∈ satSet A ↔ sat A w = true := by
  unfold satSet
  rw [Finset.mem_filter]
  simp

lemma mem_satSet {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))} {w : Fin n → Bool} :
    w ∈ satSet A ↔ ∀ c ∈ A, w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2 := by
  rw [mem_satSet_eq]
  unfold sat
  exact decide_eq_true_iff

lemma bool_beq_invol (a b : Bool) : ((a == b) == b) = a := by
  cases a <;> cases b <;> rfl

lemma card_agree_on {n : ℕ} (U : Finset (Fin n)) (w0 : Fin n → Bool) :
    (Finset.univ.filter (fun y : Fin n → Bool => ∀ i ∈ U, y i = w0 i)).card =
      2 ^ (n - U.card) := by
  let e : {y : Fin n → Bool // ∀ i ∈ U, y i = w0 i} ≃ ({i : Fin n // i ∉ U} → Bool) :=
    { toFun := fun y i => y.1 i.1
      invFun := fun f =>
        ⟨fun i => if h : i ∈ U then w0 i else f ⟨i, h⟩,
          fun i hi => by simp [hi]⟩
      left_inv := fun y => by
        ext i
        by_cases h : i ∈ U
        · simp [h, y.2 i h]
        · simp [h]
      right_inv := fun f => by
        ext i
        simp [i.2] }
  have h1 : (Finset.univ.filter (fun y : Fin n → Bool => ∀ i ∈ U, y i = w0 i)).card =
      Fintype.card {y : Fin n → Bool // ∀ i ∈ U, y i = w0 i} := by
    rw [Fintype.card_subtype]
  rw [h1, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
  have h2 : Fintype.card {i : Fin n // i ∉ U} = n - U.card := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  rw [h2]

lemma cert_cut_loss {n k : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    {H : Finset (Fin n → Bool)} (hsub : satSet A ⊆ H) (hcert : hasCert H k)
    (hstrict : ∃ w0 ∈ H, w0 ∉ satSet A) :
    2 ^ n + 2 ^ (k + 2) * (satSet A).card ≤ 2 ^ (k + 2) * H.card := by
  rcases hstrict with ⟨w0, hw0H, hw0A⟩
  rcases hcert w0 hw0H with ⟨T, hTcard, hTcert⟩
  rw [mem_satSet] at hw0A
  push Not at hw0A
  rcases hw0A with ⟨c, hcA, hc1, hc2⟩
  let U : Finset (Fin n) := T ∪ {c.1.1, c.2.1}
  let B : Finset (Fin n → Bool) := Finset.univ.filter (fun y : Fin n → Bool => ∀ i ∈ U, y i = w0 i)
  have hBU : B.card = 2 ^ (n - U.card) := card_agree_on U w0
  have hBsub : B ⊆ H \ satSet A := by
    intro y hy
    have hy' : ∀ i ∈ U, y i = w0 i := (Finset.mem_filter.mp hy).2
    rw [Finset.mem_sdiff]
    refine ⟨hTcert y (fun i hi => hy' i (Finset.mem_union_left _ hi)), ?_⟩
    rw [mem_satSet]
    push Not
    refine ⟨c, hcA, ?_, ?_⟩
    · rw [hy' c.1.1 (Finset.mem_union_right _ (by simp)), hc1]
    · rw [hy' c.2.1 (Finset.mem_union_right _ (by simp)), hc2]
  have hUcard : U.card ≤ k + 2 := by
    calc U.card ≤ T.card + ({c.1.1, c.2.1} : Finset (Fin n)).card := Finset.card_union_le _ _
      _ ≤ k + 2 := Nat.add_le_add hTcard Finset.card_le_two
  have hUn : U.card ≤ n := by
    simpa using Finset.card_le_univ U
  have hpow : 2 ^ n ≤ 2 ^ (k + 2) * B.card := by
    rw [hBU, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hdiff : B.card ≤ H.card - (satSet A).card := by
    have := Finset.card_le_card hBsub
    rwa [Finset.card_sdiff_of_subset hsub] at this
  have hle : (satSet A).card ≤ H.card := Finset.card_le_card hsub
  have hmul : 2 ^ (k + 2) * B.card ≤ 2 ^ (k + 2) * (H.card - (satSet A).card) :=
    Nat.mul_le_mul_left _ hdiff
  rw [Nat.mul_sub_left_distrib] at hmul
  have hmul_le : 2 ^ (k + 2) * (satSet A).card ≤ 2 ^ (k + 2) * H.card :=
    Nat.mul_le_mul_left _ hle
  omega

lemma half_core_concl {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    {H : Finset (Fin n → Bool)} (hsub : satSet A ⊆ H)
    (hcard : 2 * H.card = 2 ^ n) (hcert : hasCert H 2) :
    mainGoal (satSet A) := by
  have hle : (satSet A).card ≤ H.card := Finset.card_le_card hsub
  refine ⟨?_, ?_, ?_⟩
  · intro hge
    have heq : satSet A = H := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [heq]
    exact Or.inr hcert
  · intro heq2
    have heq : satSet A = H := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [heq]
    exact hcert
  · intro ⟨hgt, hlt⟩
    exfalso
    have hstrict : ∃ w0 ∈ H, w0 ∉ satSet A := by
      by_contra h
      push Not at h
      have : H ⊆ satSet A := h
      have := Finset.card_le_card this
      omega
    have hloss := cert_cut_loss hsub hcert hstrict
    norm_num at hloss
    omega

lemma card_filter_proj_signed {n k : ℕ} (s : Fin k → Fin n) (hs : Function.Injective s)
    (t : Fin k → Bool) (P : (Fin k → Bool) → Bool) :
    2 ^ k * (Finset.univ.filter (fun w : Fin n → Bool =>
        P (fun j => (w (s j) == t j)) = true)).card =
      (Finset.univ.filter (fun b : Fin k → Bool => P b = true)).card * 2 ^ n := by
  let R : Finset (Fin n) := Finset.univ.image s
  have hRcard : R.card = k := by
    rw [Finset.card_image_of_injective _ hs, Finset.card_fin]
  have hkn : k ≤ n := by
    simpa [hRcard] using Finset.card_le_univ R
  let e1 : (Fin n → Bool) ≃ (Fin k → Bool) × ({i : Fin n // i ∉ R} → Bool) :=
    { toFun := fun w => (fun j => (w (s j) == t j), fun i => w i.1)
      invFun := fun p i =>
        if h : i ∈ R then
          let j := Classical.choose (Finset.mem_image.mp h)
          (p.1 j == t j)
        else p.2 ⟨i, h⟩
      left_inv := fun w => by
        ext i
        by_cases h : i ∈ R
        · dsimp only
          rw [dif_pos h]
          have hj := (Classical.choose_spec (Finset.mem_image.mp h)).2
          rw [hj, bool_beq_invol]
        · dsimp only
          rw [dif_neg h]
      right_inv := fun p => by
        ext j
        · dsimp only
          have hmem : s j ∈ R := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
          rw [dif_pos hmem]
          have hj := (Classical.choose_spec (Finset.mem_image.mp hmem)).2
          have hjeq : Classical.choose (Finset.mem_image.mp hmem) = j := hs hj
          rw [hjeq, bool_beq_invol]
        · dsimp only
          rw [dif_neg j.2] }
  let S1 : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun w : Fin n → Bool => P (fun j => (w (s j) == t j)) = true)
  let S2 : Finset ((Fin k → Bool) × ({i : Fin n // i ∉ R} → Bool)) :=
    (Finset.univ.filter (fun b : Fin k → Bool => P b = true)) ×ˢ Finset.univ
  have hcard_eq : S1.card = S2.card := by
    refine Finset.card_bij (fun w _ => e1 w) ?_ ?_ ?_
    · intro w hw
      have hw' : P (fun j => (w (s j) == t j)) = true := (Finset.mem_filter.mp hw).2
      exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'⟩, Finset.mem_univ _⟩
    · intro w1 _ w2 _ h
      exact e1.injective h
    · intro p hp
      have hp' : P p.1 = true := (Finset.mem_filter.mp (Finset.mem_product.mp hp).1).2
      refine ⟨e1.symm p, ?_, e1.apply_symm_apply p⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have hfst : (fun j => (e1.symm p (s j) == t j)) = p.1 :=
        congrArg Prod.fst (e1.apply_symm_apply p)
      rw [hfst]
      exact hp'
  rw [hcard_eq, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_bool]
  have hcomp : Fintype.card {i : Fin n // i ∉ R} = n - k := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe, hRcard]
  rw [hcomp]
  calc 2 ^ k * ((Finset.univ.filter (fun b : Fin k → Bool => P b = true)).card * 2 ^ (n - k))
      = (Finset.univ.filter (fun b : Fin k → Bool => P b = true)).card * (2 ^ k * 2 ^ (n - k)) := by ring
    _ = (Finset.univ.filter (fun b : Fin k → Bool => P b = true)).card * 2 ^ n := by
        rw [← pow_add, Nat.add_sub_of_le hkn]

lemma card_shape_eq {n : ℕ} {S : Finset (Fin n → Bool)} (h : hasShape S) :
    32 * S.card = 15 * 2 ^ n := by
  rcases h with ⟨sites, signs, hinj, hiff⟩
  let P : (Fin 5 → Bool) → Bool := fun b =>
    decide (¬(b 0 = true ∧ (b 1 = true ∨ b 2 = true)) ∧ ¬(b 3 = true ∧ b 4 = true))
  have hS : S = Finset.univ.filter (fun w : Fin n → Bool =>
      P (fun j => (w (sites j) == signs j)) = true) := by
    ext w
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, decide_eq_true_eq, beq_iff_eq]
    exact hiff w
  have hP : (Finset.univ.filter (fun b : Fin 5 → Bool => P b = true)).card = 15 := by decide
  have hproj := card_filter_proj_signed sites hinj signs P
  rw [← hS, hP] at hproj
  norm_num at hproj
  exact hproj

lemma case_unary {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (j : Fin n) (a : Bool) (h : ∀ w ∈ satSet A, w j ≠ a) :
    mainGoal (satSet A) := by
  let s : Fin 1 → Fin n := fun _ => j
  have hs : Function.Injective s := fun x y _ => Subsingleton.elim x y
  let t : Fin 1 → Bool := fun _ => a
  let P : (Fin 1 → Bool) → Bool := fun b => !(b 0)
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun w : Fin n → Bool => P (fun i => (w (s i) == t i)) = true)
  have hmemH : ∀ w : Fin n → Bool, w ∈ H ↔ w j ≠ a := by
    intro w
    rw [Finset.mem_filter]
    simp [P, s, t, beq_eq_false_iff_ne]
  have hsub : satSet A ⊆ H := fun w hw => (hmemH w).mpr (h w hw)
  have hP : (Finset.univ.filter (fun b : Fin 1 → Bool => P b = true)).card = 1 := by decide
  have hcard : 2 * H.card = 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    rw [hP] at hproj
    norm_num at hproj
    exact hproj
  have hcert : hasCert H 2 := by
    intro x hx
    refine ⟨{j}, by simp, fun y hy => ?_⟩
    rw [hmemH] at hx ⊢
    rwa [hy j (by simp)]
  exact half_core_concl hsub hcard hcert

lemma case_conflict_same_opp {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (i j : Fin n) (hij : i ≠ j) (a : Bool)
    (h : ∀ w ∈ satSet A, ¬(w i = true ∧ w j = a) ∧ ¬(w i = false ∧ w j = !a)) :
    mainGoal (satSet A) := by
  let s : Fin 2 → Fin n := ![i, j]
  have hs : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [s]
  let t : Fin 2 → Bool := ![true, a]
  let P : (Fin 2 → Bool) → Bool := fun b =>
    decide (¬(b 0 = true ∧ b 1 = true) ∧ ¬(b 0 = false ∧ b 1 = false))
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun w : Fin n → Bool => P (fun k => (w (s k) == t k)) = true)
  have hmemH : ∀ w : Fin n → Bool, w ∈ H ↔
      ¬(w i = true ∧ w j = a) ∧ ¬(w i = false ∧ w j = !a) := by
    intro w
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, s, t, decide_eq_true_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      beq_iff_eq, beq_eq_false_iff_ne]
    cases w i <;> cases w j <;> cases a <;> decide
  have hsub : satSet A ⊆ H := fun w hw => (hmemH w).mpr (h w hw)
  have hP : (Finset.univ.filter (fun b : Fin 2 → Bool => P b = true)).card = 2 := by decide
  have hcard : 2 * H.card = 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    change 2 ^ 2 * H.card = _ at hproj
    rw [hP] at hproj
    norm_num at hproj
    omega
  have hcert : hasCert H 2 := by
    intro x hx
    refine ⟨{i, j}, Finset.card_le_two, fun y hy => ?_⟩
    rw [hmemH] at hx ⊢
    rw [hy i (by simp), hy j (by simp)]
    exact hx
  exact half_core_concl hsub hcard hcert

lemma case_conflict_diff {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : Bool)
    (h : ∀ w ∈ satSet A, ¬(w i = true ∧ w j = a) ∧ ¬(w i = false ∧ w k = b)) :
    mainGoal (satSet A) := by
  let s : Fin 3 → Fin n := ![i, j, k]
  have hs : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [s]
  let t : Fin 3 → Bool := ![true, a, b]
  let P : (Fin 3 → Bool) → Bool := fun v =>
    decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 0 = false ∧ v 2 = true))
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun w : Fin n → Bool => P (fun r => (w (s r) == t r)) = true)
  have hmemH : ∀ w : Fin n → Bool, w ∈ H ↔
      ¬(w i = true ∧ w j = a) ∧ ¬(w i = false ∧ w k = b) := by
    intro w
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, s, t, decide_eq_true_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, beq_iff_eq, beq_eq_false_iff_ne]
    cases w i <;> cases w j <;> cases w k <;> cases a <;> cases b <;> decide
  have hsub : satSet A ⊆ H := fun w hw => (hmemH w).mpr (h w hw)
  have hP : (Finset.univ.filter (fun v : Fin 3 → Bool => P v = true)).card = 4 := by decide
  have hcard : 2 * H.card = 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    change 2 ^ 3 * H.card = _ at hproj
    rw [hP] at hproj
    norm_num at hproj
    omega
  have hcert : hasCert H 2 := by
    intro x hx
    rw [hmemH] at hx
    by_cases hxi : x i = true
    · refine ⟨{i, j}, Finset.card_le_two, fun y hy => ?_⟩
      rw [hmemH, hy i (by simp), hy j (by simp)]
      exact ⟨hx.1, fun hc => by simp [hxi] at hc⟩
    · refine ⟨{i, k}, Finset.card_le_two, fun y hy => ?_⟩
      rw [hmemH, hy i (by simp), hy k (by simp)]
      exact ⟨fun hc => hxi hc.1, hx.2⟩
  exact half_core_concl hsub hcard hcert

lemma case_triangle {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool) (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hsub_tri : ∀ z ∈ satSet A,
      ¬(z u = signs u ∧ z v = signs v) ∧
      ¬(z v = signs v ∧ z w = signs w) ∧
      ¬(z u = signs u ∧ z w = signs w)) :
    mainGoal (satSet A) := by
  let s : Fin 3 → Fin n := ![u, v, w]
  have hs : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [s]
  let t : Fin 3 → Bool := ![signs u, signs v, signs w]
  let P : (Fin 3 → Bool) → Bool := fun b =>
    decide (¬(b 0 = true ∧ b 1 = true) ∧ ¬(b 1 = true ∧ b 2 = true) ∧ ¬(b 0 = true ∧ b 2 = true))
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun z : Fin n → Bool => P (fun r => (z (s r) == t r)) = true)
  have hmemH : ∀ z : Fin n → Bool, z ∈ H ↔
      ¬(z u = signs u ∧ z v = signs v) ∧
      ¬(z v = signs v ∧ z w = signs w) ∧
      ¬(z u = signs u ∧ z w = signs w) := by
    intro z
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, s, t, decide_eq_true_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, beq_iff_eq]
  have hsub : satSet A ⊆ H := fun z hz => (hmemH z).mpr (hsub_tri z hz)
  have hP : (Finset.univ.filter (fun b : Fin 3 → Bool => P b = true)).card = 4 := by decide
  have hcard : 2 * H.card = 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    change 2 ^ 3 * H.card = _ at hproj
    rw [hP] at hproj
    norm_num at hproj
    omega
  have hcert : hasCert H 2 := by
    intro x hx
    rw [hmemH] at hx
    by_cases hxu : x u = signs u
    · refine ⟨{v, w}, Finset.card_le_two, fun y hy => ?_⟩
      rw [hmemH, hy v (by simp), hy w (by simp)]
      have hxv : x v ≠ signs v := fun h => hx.1 ⟨hxu, h⟩
      have hxw : x w ≠ signs w := fun h => hx.2.2 ⟨hxu, h⟩
      exact ⟨fun h => hxv h.2, fun h => hxv h.1, fun h => hxw h.2⟩
    · by_cases hxv : x v = signs v
      · refine ⟨{u, w}, Finset.card_le_two, fun y hy => ?_⟩
        rw [hmemH, hy u (by simp), hy w (by simp)]
        have hxw : x w ≠ signs w := fun h => hx.2.1 ⟨hxv, h⟩
        exact ⟨fun h => hxu h.1, fun h => hxw h.2, fun h => hxu h.1⟩
      · refine ⟨{u, v}, Finset.card_le_two, fun y hy => ?_⟩
        rw [hmemH, hy u (by simp), hy v (by simp)]
        exact ⟨fun h => hxu h.1, fun h => hxv h.1, fun h => hxu h.1⟩
  exact half_core_concl hsub hcard hcert

lemma case_path4 {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool) (a b c d : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hsub_p4 : ∀ z ∈ satSet A,
      ¬(z a = signs a ∧ z b = signs b) ∧
      ¬(z b = signs b ∧ z c = signs c) ∧
      ¬(z c = signs c ∧ z d = signs d)) :
    mainGoal (satSet A) := by
  let s : Fin 4 → Fin n := ![a, b, c, d]
  have hs : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [s]
  let t : Fin 4 → Bool := ![signs a, signs b, signs c, signs d]
  let P : (Fin 4 → Bool) → Bool := fun v =>
    decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 1 = true ∧ v 2 = true) ∧ ¬(v 2 = true ∧ v 3 = true))
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun z : Fin n → Bool => P (fun r => (z (s r) == t r)) = true)
  have hmemH : ∀ z : Fin n → Bool, z ∈ H ↔
      ¬(z a = signs a ∧ z b = signs b) ∧
      ¬(z b = signs b ∧ z c = signs c) ∧
      ¬(z c = signs c ∧ z d = signs d) := by
    intro z
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, s, t, decide_eq_true_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, beq_iff_eq]
  have hsub : satSet A ⊆ H := fun z hz => (hmemH z).mpr (hsub_p4 z hz)
  have hP : (Finset.univ.filter (fun v : Fin 4 → Bool => P v = true)).card = 8 := by decide
  have hcard : 2 * H.card = 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    change 2 ^ 4 * H.card = _ at hproj
    rw [hP] at hproj
    norm_num at hproj
    omega
  have hcert : hasCert H 2 := by
    intro x hx
    rw [hmemH] at hx
    by_cases hxb : x b = signs b
    · refine ⟨{a, c}, Finset.card_le_two, fun y hy => ?_⟩
      rw [hmemH, hy a (by simp), hy c (by simp)]
      have hxa : x a ≠ signs a := fun h => hx.1 ⟨h, hxb⟩
      have hxc : x c ≠ signs c := fun h => hx.2.1 ⟨hxb, h⟩
      exact ⟨fun h => hxa h.1, fun h => hxc h.2, fun h => hxc h.1⟩
    · by_cases hxc : x c = signs c
      · refine ⟨{b, d}, Finset.card_le_two, fun y hy => ?_⟩
        rw [hmemH, hy b (by simp), hy d (by simp)]
        have hxd : x d ≠ signs d := fun h => hx.2.2 ⟨hxc, h⟩
        exact ⟨fun h => hxb h.2, fun h => hxb h.1, fun h => hxd h.2⟩
      · refine ⟨{b, c}, Finset.card_le_two, fun y hy => ?_⟩
        rw [hmemH, hy b (by simp), hy c (by simp)]
        exact ⟨fun h => hxb h.2, fun h => hxb h.1, fun h => hxc h.1⟩
  exact half_core_concl hsub hcard hcert

lemma case_three_disjoint {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool) (a b c d e f : Fin n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (haf : a ≠ f)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f)
    (hcd : c ≠ d) (hce : c ≠ e) (hcf : c ≠ f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f)
    (hsub3 : ∀ z ∈ satSet A,
      ¬(z a = signs a ∧ z b = signs b) ∧
      ¬(z c = signs c ∧ z d = signs d) ∧
      ¬(z e = signs e ∧ z f = signs f)) :
    mainGoal (satSet A) := by
  let s : Fin 6 → Fin n := ![a, b, c, d, e, f]
  have hs : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [s]
  let t : Fin 6 → Bool := ![signs a, signs b, signs c, signs d, signs e, signs f]
  let P : (Fin 6 → Bool) → Bool := fun v =>
    decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 2 = true ∧ v 3 = true) ∧ ¬(v 4 = true ∧ v 5 = true))
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun z : Fin n → Bool => P (fun r => (z (s r) == t r)) = true)
  have hsub : satSet A ⊆ H := by
    intro z hz
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, s, t, decide_eq_true_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.cons_val, beq_iff_eq]
    exact hsub3 z hz
  have hP : (Finset.univ.filter (fun v : Fin 6 → Bool => P v = true)).card = 27 := by decide
  have hcard : 64 * H.card = 27 * 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    rw [hP] at hproj
    norm_num at hproj
    exact hproj
  have hle : (satSet A).card ≤ H.card := Finset.card_le_card hsub
  have hpos : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  exact ⟨fun h => by omega, fun h => by omega, fun h => by omega⟩

lemma case_p3_k2 {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool) (a b e c d : Fin n)
    (hab : a ≠ b) (hae : a ≠ e) (hac : a ≠ c) (had : a ≠ d)
    (hbe : b ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hec : e ≠ c) (hed : e ≠ d) (hcd : c ≠ d)
    (hsub5 : ∀ z ∈ satSet A,
      ¬(z a = signs a ∧ z b = signs b) ∧
      ¬(z a = signs a ∧ z e = signs e) ∧
      ¬(z c = signs c ∧ z d = signs d)) :
    mainGoal (satSet A) := by
  let s : Fin 5 → Fin n := ![a, b, e, c, d]
  have hs : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [s]
  let t : Fin 5 → Bool := ![signs a, signs b, signs e, signs c, signs d]
  let P : (Fin 5 → Bool) → Bool := fun v =>
    decide (¬(v 0 = true ∧ (v 1 = true ∨ v 2 = true)) ∧ ¬(v 3 = true ∧ v 4 = true))
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun z : Fin n → Bool => P (fun r => (z (s r) == t r)) = true)
  have hmemH : ∀ z : Fin n → Bool, z ∈ H ↔
      ¬(z a = signs a ∧ (z b = signs b ∨ z e = signs e)) ∧
      ¬(z c = signs c ∧ z d = signs d) := by
    intro z
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, s, t, decide_eq_true_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, beq_iff_eq]
  have hsub : satSet A ⊆ H := by
    intro z hz
    rcases hsub5 z hz with ⟨h1, h2, h3⟩
    rw [hmemH]
    refine ⟨?_, h3⟩
    rintro ⟨ha, hb | he⟩
    · exact h1 ⟨ha, hb⟩
    · exact h2 ⟨ha, he⟩
  have hP : (Finset.univ.filter (fun v : Fin 5 → Bool => P v = true)).card = 15 := by decide
  have hcard : 32 * H.card = 15 * 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    rw [hP] at hproj
    norm_num at hproj
    exact hproj
  have hcert : hasCert H 3 := by
    intro x hx
    rw [hmemH] at hx
    have h2 : ∃ u ∈ ({c, d} : Finset (Fin n)), x u ≠ signs u := by
      by_cases hxc : x c = signs c
      · exact ⟨d, by simp, fun hxd => hx.2 ⟨hxc, hxd⟩⟩
      · exact ⟨c, by simp, hxc⟩
    rcases h2 with ⟨u, hu, hxu⟩
    by_cases hxa : x a = signs a
    · refine ⟨insert u {b, e}, ?_, fun y hy => ?_⟩
      · exact le_trans (Finset.card_insert_le u {b, e}) (Nat.add_le_add_right Finset.card_le_two 1)
      · rw [hmemH]
        have hxb : x b ≠ signs b := fun h => hx.1 ⟨hxa, Or.inl h⟩
        have hxe : x e ≠ signs e := fun h => hx.1 ⟨hxa, Or.inr h⟩
        refine ⟨?_, ?_⟩
        · rintro ⟨_, hyb | hye⟩
          · exact hxb ((hy b (by simp)).symm.trans hyb)
          · exact hxe ((hy e (by simp)).symm.trans hye)
        · rintro ⟨hyc, hyd⟩
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl
          · exact hxu ((hy u (by simp)).symm.trans hyc)
          · exact hxu ((hy u (by simp)).symm.trans hyd)
    · refine ⟨{a, u}, le_trans Finset.card_le_two (by norm_num), fun y hy => ?_⟩
      rw [hmemH]
      refine ⟨fun h => hxa ((hy a (by simp)).symm.trans h.1), ?_⟩
      rintro ⟨hyc, hyd⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl
      · exact hxu ((hy u (by simp)).symm.trans hyc)
      · exact hxu ((hy u (by simp)).symm.trans hyd)
  have hle : (satSet A).card ≤ H.card := Finset.card_le_card hsub
  have hpos : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  refine ⟨fun h => by omega, fun h => by omega, ?_⟩
  intro ⟨hgt, _⟩
  have heq : satSet A = H := by
    by_contra hne
    have hstrict : ∃ w0 ∈ H, w0 ∉ satSet A := by
      by_contra hno
      push Not at hno
      exact hne (Finset.Subset.antisymm hsub hno)
    have hloss := cert_cut_loss hsub hcert hstrict
    norm_num at hloss
    omega
  refine ⟨s, t, hs, fun word => ?_⟩
  rw [heq, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, P, decide_eq_true_eq, beq_iff_eq]

lemma case_star {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool) (edge : Fin n → Fin n → Prop)
    (hedge_ne : ∀ {x y}, edge x y → x ≠ y)
    (hsat_iff : ∀ w : Fin n → Bool,
      w ∈ satSet A ↔ ∀ u v, edge u v → ¬(w u = signs u ∧ w v = signs v))
    (u0 : Fin n) (hstar : ∀ x y, edge x y → x = u0 ∨ y = u0) :
    mainGoal (satSet A) := by
  have hhalf : hasHalf (satSet A) := by
    refine ⟨u0, !signs u0, fun p hp => ?_⟩
    rw [hsat_iff]
    intro x y hxy ⟨hx, hy⟩
    rcases hstar x y hxy with hx0 | hy0
    · rw [hx0, hp] at hx
      cases hsu : signs u0 <;> simp_all
    · rw [hy0, hp] at hy
      cases hsu : signs u0 <;> simp_all
  let s : Fin 1 → Fin n := fun _ => u0
  have hs : Function.Injective s := fun x y _ => Subsingleton.elim x y
  let t : Fin 1 → Bool := fun _ => signs u0
  let P : (Fin 1 → Bool) → Bool := fun b => !(b 0)
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun z : Fin n → Bool => P (fun r => (z (s r) == t r)) = true)
  have hmemH : ∀ z : Fin n → Bool, z ∈ H ↔ z u0 ≠ signs u0 := by
    intro z
    rw [Finset.mem_filter]
    simp [P, s, t, beq_eq_false_iff_ne]
  have hP : (Finset.univ.filter (fun b : Fin 1 → Bool => P b = true)).card = 1 := by decide
  have hHcard : 2 * H.card = 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    rw [hP] at hproj
    norm_num at hproj
    exact hproj
  have hHsub : H ⊆ satSet A := by
    intro p hp
    rw [hmemH] at hp
    rw [hsat_iff]
    intro x y hxy ⟨hx, hy⟩
    rcases hstar x y hxy with rfl | rfl
    · exact hp hx
    · exact hp hy
  let wstar : Fin n → Bool := fun i => if i = u0 then signs u0 else !signs i
  have hwstar_mem : wstar ∈ satSet A := by
    rw [hsat_iff]
    intro x y hxy ⟨hx, hy⟩
    have hne : x ≠ y := hedge_ne hxy
    rcases hstar x y hxy with rfl | rfl
    · have : wstar y = !signs y := if_neg hne.symm
      rw [this] at hy
      cases hsy : signs y <;> simp_all
    · have : wstar x = !signs x := if_neg hne
      rw [this] at hx
      cases hsx : signs x <;> simp_all
  have hwstar_not : wstar ∉ H := by
    rw [hmemH]
    simp [wstar]
  have hgt : H.card < (satSet A).card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hHsub, fun h => hwstar_not (h ▸ hwstar_mem)⟩)
  exact ⟨fun _ => Or.inl hhalf, fun h => by omega, fun h => by omega⟩

lemma case_two_disjoint_only {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool) (edge : Fin n → Fin n → Prop)
    (hsat_iff : ∀ w : Fin n → Bool,
      w ∈ satSet A ↔ ∀ u v, edge u v → ¬(w u = signs u ∧ w v = signs v))
    (a b c d : Fin n) (hab_e : edge a b) (hcd_e : edge c d)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (honly : ∀ x y, edge x y →
      (x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (x = c ∧ y = d) ∨ (x = d ∧ y = c)) :
    mainGoal (satSet A) := by
  let s : Fin 4 → Fin n := ![a, b, c, d]
  have hs : Function.Injective s := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [s]
  let t : Fin 4 → Bool := ![signs a, signs b, signs c, signs d]
  let P : (Fin 4 → Bool) → Bool := fun v =>
    decide (¬(v 0 = true ∧ v 1 = true) ∧ ¬(v 2 = true ∧ v 3 = true))
  let H : Finset (Fin n → Bool) :=
    Finset.univ.filter (fun z : Fin n → Bool => P (fun r => (z (s r) == t r)) = true)
  have hmemH : ∀ z : Fin n → Bool, z ∈ H ↔
      ¬(z a = signs a ∧ z b = signs b) ∧ ¬(z c = signs c ∧ z d = signs d) := by
    intro z
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, P, s, t, decide_eq_true_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, beq_iff_eq]
  have heq : satSet A = H := by
    ext z
    rw [hsat_iff, hmemH]
    constructor
    · intro h
      exact ⟨h a b hab_e, h c d hcd_e⟩
    · intro ⟨h1, h2⟩ x y hxy
      rcases honly x y hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1
      · exact fun h => h1 ⟨h.2, h.1⟩
      · exact h2
      · exact fun h => h2 ⟨h.2, h.1⟩
  have hP : (Finset.univ.filter (fun v : Fin 4 → Bool => P v = true)).card = 9 := by decide
  have hcard : 16 * (satSet A).card = 9 * 2 ^ n := by
    have hproj := card_filter_proj_signed s hs t P
    change 2 ^ 4 * H.card = _ at hproj
    rw [← heq, hP] at hproj
    norm_num at hproj
    exact hproj
  have hpos : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
  refine ⟨fun _ => Or.inr ?_, fun h => by omega, fun h => by omega⟩
  intro x hx
  rw [heq, hmemH] at hx
  have h1 : ∃ u ∈ ({a, b} : Finset (Fin n)), x u ≠ signs u := by
    by_cases hxa : x a = signs a
    · exact ⟨b, by simp, fun hxb => hx.1 ⟨hxa, hxb⟩⟩
    · exact ⟨a, by simp, hxa⟩
  have h2 : ∃ v ∈ ({c, d} : Finset (Fin n)), x v ≠ signs v := by
    by_cases hxc : x c = signs c
    · exact ⟨d, by simp, fun hxd => hx.2 ⟨hxc, hxd⟩⟩
    · exact ⟨c, by simp, hxc⟩
  rcases h1 with ⟨u, hu, hxu⟩
  rcases h2 with ⟨v, hv, hxv⟩
  refine ⟨{u, v}, Finset.card_le_two, fun y hy => ?_⟩
  rw [heq, hmemH]
  refine ⟨?_, ?_⟩
  · rintro ⟨hya, hyb⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hxu ((hy u (by simp)).symm.trans hya)
    · exact hxu ((hy u (by simp)).symm.trans hyb)
  · rintro ⟨hyc, hyd⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hxv ((hy v (by simp)).symm.trans hyc)
    · exact hxv ((hy v (by simp)).symm.trans hyd)

lemma case_match2_third {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool) (edge : Fin n → Fin n → Prop)
    (hedge_symm : ∀ {u v}, edge u v → edge v u)
    (hsat_e : ∀ {p q}, edge p q → ∀ z ∈ satSet A, ¬(z p = signs p ∧ z q = signs q))
    (a b c d x y : Fin n) (hab_e : edge a b) (hcd_e : edge c d) (hxy_e : edge x y)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hxy : x ≠ y)
    (hnot_old : ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (x = c ∧ y = d) ∨ (x = d ∧ y = c))) :
    mainGoal (satSet A) := by
  by_cases hx : a = x ∨ b = x ∨ c = x ∨ d = x
  · by_cases hy : a = y ∨ b = y ∨ c = y ∨ d = y
    · rcases hx with rfl | rfl | rfl | rfl
      · rcases hy with hy | hy | hy | hy
        · exact (hxy hy).elim
        · exact (hnot_old (Or.inl ⟨rfl, hy.symm⟩)).elim
        · subst hy
          exact case_path4 signs b a c d hab.symm hbc hbd hac had hcd (fun z hz =>
            ⟨hsat_e (hedge_symm hab_e) z hz, hsat_e hxy_e z hz, hsat_e hcd_e z hz⟩)
        · subst hy
          exact case_path4 signs b a d c hab.symm hbd hbc had hac hcd.symm (fun z hz =>
            ⟨hsat_e (hedge_symm hab_e) z hz, hsat_e hxy_e z hz, hsat_e (hedge_symm hcd_e) z hz⟩)
      · rcases hy with hy | hy | hy | hy
        · exact (hnot_old (Or.inr (Or.inl ⟨rfl, hy.symm⟩))).elim
        · exact (hxy hy).elim
        · subst hy
          exact case_path4 signs a b c d hab hac had hbc hbd hcd (fun z hz =>
            ⟨hsat_e hab_e z hz, hsat_e hxy_e z hz, hsat_e hcd_e z hz⟩)
        · subst hy
          exact case_path4 signs a b d c hab had hac hbd hbc hcd.symm (fun z hz =>
            ⟨hsat_e hab_e z hz, hsat_e hxy_e z hz, hsat_e (hedge_symm hcd_e) z hz⟩)
      · rcases hy with hy | hy | hy | hy
        · subst hy
          exact case_path4 signs b a c d hab.symm hbc hbd hac had hcd (fun z hz =>
            ⟨hsat_e (hedge_symm hab_e) z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e hcd_e z hz⟩)
        · subst hy
          exact case_path4 signs a b c d hab hac had hbc hbd hcd (fun z hz =>
            ⟨hsat_e hab_e z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e hcd_e z hz⟩)
        · exact (hxy hy).elim
        · exact (hnot_old (Or.inr (Or.inr (Or.inl ⟨rfl, hy.symm⟩)))).elim
      · rcases hy with hy | hy | hy | hy
        · subst hy
          exact case_path4 signs b a d c hab.symm hbd hbc had hac hcd.symm (fun z hz =>
            ⟨hsat_e (hedge_symm hab_e) z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e (hedge_symm hcd_e) z hz⟩)
        · subst hy
          exact case_path4 signs a b d c hab had hac hbd hbc hcd.symm (fun z hz =>
            ⟨hsat_e hab_e z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e (hedge_symm hcd_e) z hz⟩)
        · exact (hnot_old (Or.inr (Or.inr (Or.inr ⟨rfl, hy.symm⟩)))).elim
        · exact (hxy hy).elim
    · push Not at hy
      rcases hy with ⟨hay, hby, hcy, hdy⟩
      rcases hx with rfl | rfl | rfl | rfl
      · exact case_p3_k2 signs a b y c d hab hay hac had hby hbc hbd hcy.symm hdy.symm hcd
          (fun z hz => ⟨hsat_e hab_e z hz, hsat_e hxy_e z hz, hsat_e hcd_e z hz⟩)
      · exact case_p3_k2 signs b a y c d hab.symm hby hbc hbd hay hac had hcy.symm hdy.symm hcd
          (fun z hz => ⟨hsat_e (hedge_symm hab_e) z hz, hsat_e hxy_e z hz, hsat_e hcd_e z hz⟩)
      · exact case_p3_k2 signs c d y a b hcd hcy hac.symm hbc.symm hdy had.symm hbd.symm hay.symm hby.symm hab
          (fun z hz => ⟨hsat_e hcd_e z hz, hsat_e hxy_e z hz, hsat_e hab_e z hz⟩)
      · exact case_p3_k2 signs d c y a b hcd.symm hdy had.symm hbd.symm hcy hac.symm hbc.symm hay.symm hby.symm hab
          (fun z hz => ⟨hsat_e (hedge_symm hcd_e) z hz, hsat_e hxy_e z hz, hsat_e hab_e z hz⟩)
  · push Not at hx
    rcases hx with ⟨hax, hbx, hcx, hdx⟩
    by_cases hy : a = y ∨ b = y ∨ c = y ∨ d = y
    · rcases hy with rfl | rfl | rfl | rfl
      · exact case_p3_k2 signs a b x c d hab hax hac had hbx hbc hbd hcx.symm hdx.symm hcd
          (fun z hz => ⟨hsat_e hab_e z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e hcd_e z hz⟩)
      · exact case_p3_k2 signs b a x c d hab.symm hbx hbc hbd hax hac had hcx.symm hdx.symm hcd
          (fun z hz => ⟨hsat_e (hedge_symm hab_e) z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e hcd_e z hz⟩)
      · exact case_p3_k2 signs c d x a b hcd hcx hac.symm hbc.symm hdx had.symm hbd.symm hax.symm hbx.symm hab
          (fun z hz => ⟨hsat_e hcd_e z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e hab_e z hz⟩)
      · exact case_p3_k2 signs d c x a b hcd.symm hdx had.symm hbd.symm hcx hac.symm hbc.symm hax.symm hbx.symm hab
          (fun z hz => ⟨hsat_e (hedge_symm hcd_e) z hz, hsat_e (hedge_symm hxy_e) z hz, hsat_e hab_e z hz⟩)
    · push Not at hy
      rcases hy with ⟨hay, hby, hcy, hdy⟩
      exact case_three_disjoint signs a b c d x y hab hac had hax hay
        hbc hbd hbx hby hcd hcx hcy hdx hdy hxy
        (fun z hz => ⟨hsat_e hab_e z hz, hsat_e hcd_e z hz, hsat_e hxy_e z hz⟩)

lemma case_oriented {n : ℕ} {A : Finset ((Fin n × Bool) × (Fin n × Bool))}
    (signs : Fin n → Bool)
    (hno_unary : ∀ c ∈ A, c.1 ≠ c.2)
    (hsign : ∀ c ∈ A, c.1.1 ≠ c.2.1 → c.1.2 = signs c.1.1 ∧ c.2.2 = signs c.2.1) :
    mainGoal (satSet A) := by
  let edge : Fin n → Fin n → Prop := fun u v =>
    u ≠ v ∧ ∃ c ∈ A, (c.1.1 = u ∧ c.2.1 = v) ∨ (c.1.1 = v ∧ c.2.1 = u)
  have hedge_symm : ∀ {u v}, edge u v → edge v u := by
    intro u v ⟨hne, c, hc, hor⟩
    exact ⟨hne.symm, c, hc, hor.symm⟩
  have hsat_iff : ∀ w : Fin n → Bool,
      w ∈ satSet A ↔ ∀ u v, edge u v → ¬(w u = signs u ∧ w v = signs v) := by
    intro w
    rw [mem_satSet]
    constructor
    · intro hw u v ⟨hne, c, hc, hor⟩ ⟨hwu, hwv⟩
      have hcs := hsign c hc (by rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exact hne; exact hne.symm)
      rcases hw c hc with h1 | h2
      · rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h1 (hwu.trans hcs.1.symm)
        · exact h1 (hwv.trans hcs.1.symm)
      · rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact h2 (hwv.trans hcs.2.symm)
        · exact h2 (hwu.trans hcs.2.symm)
    · intro hedge c hc
      by_cases heq : c.1.1 = c.2.1
      · have hne2 : c.1.2 ≠ c.2.2 := by
          intro h
          exact hno_unary c hc (Prod.ext heq h)
        rw [heq]
        cases h1 : w c.2.1 <;> cases h2 : c.1.2 <;> cases h3 : c.2.2 <;> simp_all
      · have hcs := hsign c hc heq
        have he : edge c.1.1 c.2.1 := ⟨heq, c, hc, Or.inl ⟨rfl, rfl⟩⟩
        have hnot := hedge c.1.1 c.2.1 he
        rw [hcs.1, hcs.2]
        by_contra h
        push Not at h
        exact hnot h
  by_cases hno_edge : ∀ u v, ¬edge u v
  · have hall : satSet A = Finset.univ := by
      ext w
      simp only [Finset.mem_univ, iff_true, hsat_iff]
      intro u v he
      exact (hno_edge u v he).elim
    have hcard : (satSet A).card = 2 ^ n := by
      rw [hall, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hpos : 0 < 2 ^ n := Nat.pow_pos (by norm_num)
    refine ⟨fun _ => Or.inr ?_, fun h => by omega, fun h => by omega⟩
    intro x _
    exact ⟨∅, by simp, fun y _ => by rw [hall]; exact Finset.mem_univ y⟩
  · push Not at hno_edge
    rcases hno_edge with ⟨u0, v0, he0⟩
    by_cases hmatch2 : ∃ a b c d : Fin n,
        edge a b ∧ edge c d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d
    · rcases hmatch2 with ⟨a, b, c, d, hab_e, hcd_e, hac, had, hbc, hbd⟩
      by_cases hthird : ∃ x y : Fin n, edge x y ∧
          ¬((x = a ∧ y = b) ∨ (x = b ∧ y = a) ∨ (x = c ∧ y = d) ∨ (x = d ∧ y = c))
      · rcases hthird with ⟨x, y, hxy_e, hnot_old⟩
        exact case_match2_third signs edge hedge_symm
          (fun hpq z hz => (hsat_iff z).mp hz _ _ hpq)
          a b c d x y hab_e hcd_e hxy_e hab_e.1 hac had hbc hbd hcd_e.1 hxy_e.1 hnot_old
      · push Not at hthird
        exact case_two_disjoint_only signs edge hsat_iff a b c d hab_e hcd_e
          hab_e.1 hac had hbc hbd hcd_e.1 hthird
    · push Not at hmatch2
      by_cases hstar_u : ∀ x y, edge x y → x = u0 ∨ y = u0
      · exact case_star signs edge (fun h => h.1) hsat_iff u0 hstar_u
      · by_cases hstar_v : ∀ x y, edge x y → x = v0 ∨ y = v0
        · exact case_star signs edge (fun h => h.1) hsat_iff v0 hstar_v
        · push Not at hstar_u hstar_v
          rcases hstar_u with ⟨x1, y1, he1, hx1u, hy1u⟩
          rcases hstar_v with ⟨x2, y2, he2, hx2v, hy2v⟩
          have h1v : x1 = v0 ∨ y1 = v0 := by
            by_contra h
            push Not at h
            exact h.2.symm (hmatch2 u0 v0 x1 y1 he0 he1 hx1u.symm hy1u.symm h.1.symm)
          have h2u : x2 = u0 ∨ y2 = u0 := by
            by_contra h
            push Not at h
            exact hy2v.symm (hmatch2 u0 v0 x2 y2 he0 he2 h.1.symm h.2.symm hx2v.symm)
          have ⟨w1, he1', hw1u, hw1v⟩ : ∃ w1, edge v0 w1 ∧ w1 ≠ u0 ∧ w1 ≠ v0 := by
            rcases h1v with rfl | rfl
            · exact ⟨y1, he1, hy1u, he1.1.symm⟩
            · exact ⟨x1, hedge_symm he1, hx1u, he1.1⟩
          have ⟨w2, he2', hw2u, hw2v⟩ : ∃ w2, edge u0 w2 ∧ w2 ≠ u0 ∧ w2 ≠ v0 := by
            rcases h2u with rfl | rfl
            · exact ⟨y2, he2, he2.1.symm, hy2v⟩
            · exact ⟨x2, hedge_symm he2, he2.1, hx2v⟩
          have hw12 : w1 = w2 := by
            by_contra hne
            exact hne (hmatch2 v0 w1 u0 w2 he1' he2' he0.1.symm hw2v.symm hw1u)
          rw [← hw12] at he2'
          exact case_triangle signs u0 v0 w1 he0.1 hw1u.symm hw1v.symm (fun z hz =>
            ⟨(hsat_iff z).mp hz _ _ he0, (hsat_iff z).mp hz _ _ he1', (hsat_iff z).mp hz _ _ he2'⟩)

lemma solve_main {n : ℕ} (A : Finset ((Fin n × Bool) × (Fin n × Bool))) :
    mainGoal (satSet A) := by
  by_cases hunary : ∃ c ∈ A, c.1 = c.2
  · rcases hunary with ⟨c, hcA, hceq⟩
    refine case_unary c.1.1 c.1.2 (fun w hw => ?_)
    have := (mem_satSet.mp hw) c hcA
    rw [← hceq] at this
    rcases this with h | h <;> exact h
  · push Not at hunary
    let appears : Fin n → Bool → Prop := fun i b =>
      ∃ c ∈ A, c.1.1 ≠ c.2.1 ∧ ((c.1.1 = i ∧ c.1.2 = b) ∨ (c.2.1 = i ∧ c.2.2 = b))
    by_cases hconf : ∃ i : Fin n, appears i true ∧ appears i false
    · rcases hconf with ⟨i, ⟨c1, hc1A, hc1ne, hc1⟩, ⟨c2, hc2A, hc2ne, hc2⟩⟩
      have ⟨j, a, hij, hj⟩ : ∃ (j : Fin n) (a : Bool), i ≠ j ∧
          ∀ w ∈ satSet A, ¬(w i = true ∧ w j = a) := by
        rcases hc1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨c1.2.1, c1.2.2, by rw [← h1]; exact hc1ne, fun w hw ⟨hwi, hwj⟩ => ?_⟩
          rcases (mem_satSet.mp hw) c1 hc1A with h | h
          · exact h (by rw [h1, h2]; exact hwi)
          · exact h hwj
        · refine ⟨c1.1.1, c1.1.2, by rw [← h1]; exact hc1ne.symm, fun w hw ⟨hwi, hwj⟩ => ?_⟩
          rcases (mem_satSet.mp hw) c1 hc1A with h | h
          · exact h hwj
          · exact h (by rw [h1, h2]; exact hwi)
      have ⟨k, b, hik, hk⟩ : ∃ (k : Fin n) (b : Bool), i ≠ k ∧
          ∀ w ∈ satSet A, ¬(w i = false ∧ w k = b) := by
        rcases hc2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · refine ⟨c2.2.1, c2.2.2, by rw [← h1]; exact hc2ne, fun w hw ⟨hwi, hwk⟩ => ?_⟩
          rcases (mem_satSet.mp hw) c2 hc2A with h | h
          · exact h (by rw [h1, h2]; exact hwi)
          · exact h hwk
        · refine ⟨c2.1.1, c2.1.2, by rw [← h1]; exact hc2ne.symm, fun w hw ⟨hwi, hwk⟩ => ?_⟩
          rcases (mem_satSet.mp hw) c2 hc2A with h | h
          · exact h hwk
          · exact h (by rw [h1, h2]; exact hwi)
      by_cases hjk : j = k
      · subst hjk
        by_cases hab : a = b
        · subst hab
          refine case_unary j a (fun w hw hwj => ?_)
          cases hwi : w i
          · exact hk w hw ⟨hwi, hwj⟩
          · exact hj w hw ⟨hwi, hwj⟩
        · have hb : b = !a := by cases a <;> cases b <;> simp_all
          subst hb
          exact case_conflict_same_opp i j hij a (fun w hw => ⟨hj w hw, hk w hw⟩)
      · exact case_conflict_diff i j k hij hik hjk a b (fun w hw => ⟨hj w hw, hk w hw⟩)
    · push Not at hconf
      let signs : Fin n → Bool := fun i =>
        @decide (appears i true) (Classical.propDecidable _)
      refine case_oriented signs hunary (fun c hc hne => ?_)
      have h1 : c.1.2 = signs c.1.1 := by
        cases h : c.1.2
        · have hfalse : appears c.1.1 false := ⟨c, hc, hne, Or.inl ⟨rfl, h⟩⟩
          have hnottrue : ¬appears c.1.1 true := fun ht => hconf c.1.1 ht hfalse
          simp [signs, hnottrue]
        · have htrue : appears c.1.1 true := ⟨c, hc, hne, Or.inl ⟨rfl, h⟩⟩
          simp [signs, htrue]
      have h2 : c.2.2 = signs c.2.1 := by
        cases h : c.2.2
        · have hfalse : appears c.2.1 false := ⟨c, hc, hne, Or.inr ⟨rfl, h⟩⟩
          have hnottrue : ¬appears c.2.1 true := fun ht => hconf c.2.1 ht hfalse
          simp [signs, hnottrue]
        · have htrue : appears c.2.1 true := ⟨c, hc, hne, Or.inr ⟨rfl, h⟩⟩
          simp [signs, htrue]
      exact ⟨h1, h2⟩

end PEqualNP.Outside.L_lib_600

theorem PEqualNP.Outside.L_lib_600 : (∀ n : ℕ,
  let W := Fin n → Bool
  let Lit := Fin n × Bool
  let F := Finset (Lit × Lit)
  let sat := fun (C : F) (w : W) => decide (∀ c ∈ C,
    w c.1.1 ≠ c.1.2 ∨ w c.2.1 ≠ c.2.2)
  let Q := 2 ^ n
  ∀ A : F,
    let N := (Finset.univ.filter (fun z => sat A z = true)).card
    let cert := ∀ x : W, sat A x = true →
      ∃ T : Finset (Fin n), T.card ≤ 2 ∧
        ∀ y : W, (∀ i ∈ T, y i = x i) → sat A y = true
    let half := ∃ (j : Fin n) (v : Bool), ∀ p : W, p j = v → sat A p = true
    let shape := ∃ (sites : Fin 5 → Fin n) (signs : Fin 5 → Bool),
      Function.Injective sites ∧ ∀ word : W,
        let mark := fun k : Fin 5 => word (sites k) = signs k
        sat A word = decide (¬(mark 0 ∧ (mark 1 ∨ mark 2)) ∧ ¬(mark 3 ∧ mark 4))
    (Q ≤ 2 * N → half ∨ cert) ∧ (2 * N = Q → cert) ∧
      ((7 * Q < 16 * N ∧ 2 * N < Q) ↔ shape) ∧
      (shape → 32 * N = 15 * Q)) := by
  intro n W Lit F sat Q A N cert half shape
  have hmain := PEqualNP.Outside.L_lib_600.solve_main A
  have hmem : ∀ w : W, w ∈ PEqualNP.Outside.L_lib_600.satSet A ↔ sat A w = true :=
    fun w => PEqualNP.Outside.L_lib_600.mem_satSet_eq
  have hcert_iff : PEqualNP.Outside.L_lib_600.hasCert (PEqualNP.Outside.L_lib_600.satSet A) 2 ↔ cert := by
    constructor
    · intro h x hx
      rcases h x ((hmem x).mpr hx) with ⟨T, hT, hTy⟩
      exact ⟨T, hT, fun y hy => (hmem y).mp (hTy y hy)⟩
    · intro h x hx
      rcases h x ((hmem x).mp hx) with ⟨T, hT, hTy⟩
      exact ⟨T, hT, fun y hy => (hmem y).mpr (hTy y hy)⟩
  have hhalf_iff : PEqualNP.Outside.L_lib_600.hasHalf (PEqualNP.Outside.L_lib_600.satSet A) ↔ half := by
    constructor
    · rintro ⟨j, v, hp⟩
      exact ⟨j, v, fun p h => (hmem p).mp (hp p h)⟩
    · rintro ⟨j, v, hp⟩
      exact ⟨j, v, fun p h => (hmem p).mpr (hp p h)⟩
  have hshape_iff : PEqualNP.Outside.L_lib_600.hasShape (PEqualNP.Outside.L_lib_600.satSet A) ↔ shape := by
    constructor
    · rintro ⟨sites, signs, hinj, hiff⟩
      refine ⟨sites, signs, hinj, fun word => ?_⟩
      dsimp only
      have hw : sat A word = true ↔ _ := (hmem word).symm.trans (hiff word)
      cases h : sat A word
      · symm
        rw [decide_eq_false_iff_not]
        intro hc
        have ht : sat A word = true := hw.mpr hc
        rw [h] at ht
        exact Bool.false_ne_true ht
      · symm
        rw [decide_eq_true_eq]
        exact hw.mp h
    · rintro ⟨sites, signs, hinj, heq⟩
      refine ⟨sites, signs, hinj, fun word => ?_⟩
      dsimp only
      rw [hmem word, heq word, decide_eq_true_eq]
  have hN : (PEqualNP.Outside.L_lib_600.satSet A).card = N := rfl
  have hshape_card : shape → 32 * N = 15 * Q := by
    intro hs
    have := PEqualNP.Outside.L_lib_600.card_shape_eq (hshape_iff.mpr hs)
    simpa [hN, Q] using this
  refine ⟨?_, ?_, ?_, hshape_card⟩
  · intro h
    rcases hmain.1 (by simpa [hN, Q] using h) with h1 | h2
    · exact Or.inl (hhalf_iff.mp h1)
    · exact Or.inr (hcert_iff.mp h2)
  · intro h
    exact hcert_iff.mp (hmain.2.1 (by simpa [hN, Q] using h))
  · constructor
    · intro h
      exact hshape_iff.mp (hmain.2.2 (by simpa [hN, Q] using h))
    · intro hs
      have h32 := hshape_card hs
      have hpos : 0 < Q := Nat.pow_pos (by norm_num)
      omega
