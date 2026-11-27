import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25754_aux

open scoped BigOperators

abbrev B := ZMod 2

def signZ (t : B) : ℤ := if t = 0 then 1 else -1

lemma signZ_zero : signZ 0 = 1 := rfl

lemma signZ_one : signZ 1 = -1 := by decide

lemma signZ_add (a b : B) : signZ (a + b) = signZ a * signZ b := by
  fin_cases a <;> fin_cases b <;> decide

lemma signZ_sum {α : Type*} (s : Finset α) (f : α → B) :
    signZ (∑ x ∈ s, f x) = ∏ x ∈ s, signZ (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [signZ_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, signZ_add, ih]

lemma zmod2_add_self (a : B) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_add_eq_zero_iff (a b : B) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congr_arg (· + b) h
    rwa [add_assoc, zmod2_add_self, add_zero, zero_add] at this
  · rintro rfl
    exact zmod2_add_self a

lemma zmod2_ne_zero_eq_one {a : B} (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl

lemma supported_card {k : ℕ} [NeZero k] (S : Finset (ZMod k)) :
    (Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0)).card =
      2 ^ S.card := by
  classical
  let T := Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0)
  have heq : T.card = Fintype.card {a : ZMod k → B // a ∈ T} := (Fintype.card_coe T).symm
  let e : {a : ZMod k → B // a ∈ T} ≃ (S → B) :=
    { toFun := fun a i => a.1 i.1
      invFun := fun g => ⟨fun i => if hi : i ∈ S then g ⟨i, hi⟩ else 0, by
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        simp [hi]⟩
      left_inv := fun a => by
        apply Subtype.ext
        funext i
        by_cases hi : i ∈ S
        · simp [hi]
        · simp only [hi, ↓reduceDIte]
          have ha := (Finset.mem_filter.mp a.2).2 i hi
          exact ha.symm
      right_inv := fun g => by
        funext ⟨i, hi⟩
        simp [hi] }
  rw [heq, Fintype.card_congr e, Fintype.card_fun, ZMod.card, Fintype.card_coe]

lemma sum_supported_sign {k : ℕ} [NeZero k] (S : Finset (ZMod k)) (u : ZMod k → B) :
    ∑ a ∈ Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0),
      signZ (dotProduct a u) =
      if ∀ i ∈ S, u i = 0 then (2 : ℤ) ^ S.card else 0 := by
  classical
  set T := Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0)
  by_cases hu : ∀ i ∈ S, u i = 0
  · rw [if_pos hu]
    have h1 : ∀ a ∈ T, signZ (dotProduct a u) = 1 := by
      intro a ha
      have hdot : dotProduct a u = 0 := by
        unfold dotProduct
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : i ∈ S
        · rw [hu i hi, mul_zero]
        · rw [(Finset.mem_filter.mp ha).2 i hi, zero_mul]
      rw [hdot, signZ_zero]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul, mul_one, supported_card S]
    norm_cast
  · rw [if_neg hu]
    push Not at hu
    rcases hu with ⟨i₀, hi₀S, hui₀⟩
    have hui₀1 : u i₀ = 1 := zmod2_ne_zero_eq_one hui₀
    let flip : (ZMod k → B) → (ZMod k → B) := fun a => Function.update a i₀ (a i₀ + 1)
    have hflip_mem : ∀ a ∈ T, flip a ∈ T := by
      intro a ha
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      intro i hi
      have hne : i ≠ i₀ := fun heq => hi (heq ▸ hi₀S)
      simp [flip, Function.update_of_ne hne, ha i hi]
    have hflip_inv : ∀ a, flip (flip a) = a := by
      intro a
      funext i
      by_cases hi : i = i₀
      · subst hi
        simp [flip, add_assoc, zmod2_add_self]
      · simp [flip, Function.update_of_ne hi]
    have hflip_sign : ∀ a, signZ (dotProduct (flip a) u) = -signZ (dotProduct a u) := by
      intro a
      have hdot : dotProduct (flip a) u = dotProduct a u + 1 := by
        unfold dotProduct
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
            ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
        have hrest : ∑ i ∈ Finset.univ.erase i₀, flip a i * u i =
            ∑ i ∈ Finset.univ.erase i₀, a i * u i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp [flip, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
        rw [hrest]
        simp only [flip, Function.update_self, hui₀1, mul_one]
        ring
      rw [hdot, signZ_add, signZ_one]
      ring
    have hsum_eq : ∑ a ∈ T, signZ (dotProduct (flip a) u) = ∑ a ∈ T, signZ (dotProduct a u) := by
      refine Finset.sum_bij (fun a _ => flip a) hflip_mem ?_ ?_ (fun _ _ => rfl)
      · intro a₁ _ a₂ _ heq
        have := congr_arg flip heq
        rwa [hflip_inv, hflip_inv] at this
      · intro b hb
        exact ⟨flip b, hflip_mem b hb, hflip_inv b⟩
    have hneg : ∑ a ∈ T, signZ (dotProduct (flip a) u) = - ∑ a ∈ T, signZ (dotProduct a u) := by
      simp_rw [hflip_sign, Finset.sum_neg_distrib]
    linarith

lemma sum_univ_sign {k : ℕ} [NeZero k] (u : ZMod k → B) :
    ∑ a : ZMod k → B, signZ (dotProduct a u) = if u = 0 then (2 : ℤ) ^ k else 0 := by
  have h := sum_supported_sign (k := k) (Finset.univ : Finset (ZMod k)) u
  have hfilt : Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ (Finset.univ : Finset (ZMod k)) → mask i = 0) =
      Finset.univ := by
    ext a; simp
  rw [hfilt, Finset.card_univ, ZMod.card] at h
  simp only [Finset.mem_univ, true_implies] at h
  have hiff : (∀ i : ZMod k, u i = 0) ↔ u = 0 := ⟨fun ha => funext ha, fun hu i => by simp [hu]⟩
  rwa [if_congr hiff rfl rfl] at h

def snocB {m : ℕ} (y : Fin (m + 1) → B) (c : B) : Fin (m + 2) → B :=
  fun i => Fin.lastCases c y i

lemma snocB_last {m : ℕ} (y : Fin (m + 1) → B) (c : B) : snocB y c (Fin.last (m + 1)) = c := by
  simp [snocB]

lemma snocB_castSucc {m : ℕ} (y : Fin (m + 1) → B) (c : B) (j : Fin (m + 1)) :
    snocB y c j.castSucc = y j := by
  simp [snocB]

lemma list_prod_range_apply (f : ℕ → Matrix B B ℤ) :
    ∀ (m : ℕ) (c₀ c₁ : B),
      (((List.range m).map f).prod) c₀ c₁ =
        ∑ y ∈ Finset.univ.filter (fun y : Fin (m + 1) → B => y 0 = c₀ ∧ y (Fin.last m) = c₁),
          ∏ j : Fin m, f j.val (y j.castSucc) (y j.succ) := by
  intro m
  induction m with
  | zero =>
      intro c₀ c₁
      simp only [List.range_zero, List.map_nil, List.prod_nil, Matrix.one_apply,
        Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_const, nsmul_eq_mul, mul_one]
      by_cases h : c₀ = c₁
      · subst h
        rw [if_pos rfl]
        have hcard : (Finset.univ.filter (fun y : Fin 1 → B => y 0 = c₀ ∧ y (Fin.last 0) = c₀)).card = 1 := by
          have heq : Finset.univ.filter (fun y : Fin 1 → B => y 0 = c₀ ∧ y (Fin.last 0) = c₀) =
              {fun _ => c₀} := by
            ext y
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · rintro ⟨h0, _⟩; funext i; rw [Fin.eq_zero i]; exact h0
            · rintro rfl; simp
          rw [heq, Finset.card_singleton]
        rw [hcard]; norm_num
      · rw [if_neg h]
        have hcard : (Finset.univ.filter (fun y : Fin 1 → B => y 0 = c₀ ∧ y (Fin.last 0) = c₁)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro y _
          rintro ⟨h0, h1⟩
          exact h (h0.symm.trans h1)
        rw [hcard]; norm_num
  | succ m ih =>
      intro c₀ c₁
      rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton,
        Matrix.mul_apply]
      simp_rw [ih c₀]
      simp_rw [Finset.sum_mul]
      let P : Finset (Fin (m + 2) → B) :=
        Finset.univ.filter (fun y : Fin (m + 2) → B => y 0 = c₀ ∧ y (Fin.last (m + 1)) = c₁)
      let Q : Finset (Σ c : B, Fin (m + 1) → B) :=
        Finset.univ.sigma (fun c : B =>
          Finset.univ.filter (fun y : Fin (m + 1) → B => y 0 = c₀ ∧ y (Fin.last m) = c))
      have hsig : ∑ x : B, ∑ i ∈ Finset.univ.filter (fun y : Fin (m + 1) → B => y 0 = c₀ ∧ y (Fin.last m) = x),
            (∏ j : Fin m, f j.val (i j.castSucc) (i j.succ)) * f m x c₁ =
          ∑ p ∈ Q, (∏ j : Fin m, f j.val (p.2 j.castSucc) (p.2 j.succ)) * f m p.1 c₁ := by
        rw [Finset.sum_sigma']
      rw [hsig]
      refine Finset.sum_bij
        (fun p _ => snocB p.2 c₁)
        ?_ ?_ ?_ ?_
      · intro ⟨c, y⟩ hp
        simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, snocB_last y c₁⟩
        have h0 : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
        rw [h0, snocB_castSucc]
        exact hp.1
      · intro ⟨c, y⟩ hp ⟨c', y'⟩ hp' heq
        simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp hp'
        have hy : y = y' := by
          funext i
          have := congr_fun heq i.castSucc
          simpa [snocB_castSucc] using this
        subst hy
        have hc : c = c' := hp.2.symm.trans hp'.2
        subst hc
        rfl
      · intro z hz
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hz
        let c : B := z (Fin.last m).castSucc
        let y : Fin (m + 1) → B := fun i => z i.castSucc
        refine ⟨⟨c, y⟩, ?_, ?_⟩
        · simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, c, y]
          exact ⟨hz.1, trivial⟩
        · funext i
          refine Fin.lastCases ?_ ?_ i
          · simp [snocB_last, hz.2]
          · intro j
            simp [snocB_castSucc, y]
      · intro ⟨c, y⟩ hp
        simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp
        rw [Fin.prod_univ_castSucc]
        congr 1
        · apply Finset.prod_congr rfl
          intro j _
          have h1 : (j.castSucc : Fin (m + 1)).castSucc = j.castSucc.castSucc := rfl
          have h2 : (j.castSucc : Fin (m + 1)).succ = j.succ.castSucc := rfl
          rw [h1, h2, snocB_castSucc, snocB_castSucc]
          rfl
        · have h2 : (Fin.last m : Fin (m + 1)).succ = Fin.last (m + 1) := rfl
          rw [h2, snocB_castSucc, snocB_last]
          dsimp only
          rw [Fin.val_last, hp.2]

lemma trace_list_prod_range {k : ℕ} [NeZero k] (f : ZMod k → Matrix B B ℤ) :
    Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j : ℕ => f (j : ZMod k)))) =
      ∑ y : ZMod k → B, ∏ j : ZMod k, f j (y j) (y (j + 1)) := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  have h1 : ∀ c : B,
      (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j : ℕ => f (j : ZMod k)))) c c =
        ∑ y ∈ Finset.univ.filter (fun y : Fin (k + 1) → B => y 0 = c ∧ y (Fin.last k) = c),
          ∏ j : Fin k, f (j.val : ZMod k) (y j.castSucc) (y j.succ) :=
    fun c => list_prod_range_apply (fun j : ℕ => f (j : ZMod k)) k c c
  rw [Finset.sum_congr rfl (fun c _ => h1 c)]
  let Q : Finset (Σ c : B, Fin (k + 1) → B) :=
    Finset.univ.sigma (fun c : B =>
      Finset.univ.filter (fun y : Fin (k + 1) → B => y 0 = c ∧ y (Fin.last k) = c))
  have hsig : ∑ c : B, ∑ y ∈ Finset.univ.filter (fun y : Fin (k + 1) → B => y 0 = c ∧ y (Fin.last k) = c),
        ∏ j : Fin k, f (j.val : ZMod k) (y j.castSucc) (y j.succ) =
      ∑ p ∈ Q, ∏ j : Fin k, f (j.val : ZMod k) (p.2 j.castSucc) (p.2 j.succ) := by
    rw [Finset.sum_sigma']
  rw [hsig]
  have hkpos : 0 < k := NeZero.pos k
  refine Finset.sum_bij
    (fun p _ => fun i : ZMod k => p.2 ⟨i.val, Nat.lt_succ_of_lt (ZMod.val_lt i)⟩)
    (fun _ _ => Finset.mem_univ _)
    ?_ ?_ ?_
  · intro ⟨c₁, y₁⟩ hp₁ ⟨c₂, y₂⟩ hp₂ heq
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp₁ hp₂
    have hy : y₁ = y₂ := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · rw [hp₁.2, hp₂.2, ← hp₁.1, ← hp₂.1]
        have := congr_fun heq 0
        simpa [ZMod.val_zero] using this
      · intro j
        have := congr_fun heq (j.val : ZMod k)
        dsimp only at this
        have hval : ((j.val : ZMod k)).val = j.val := ZMod.val_natCast_of_lt j.isLt
        have harg : (⟨((j.val : ZMod k)).val, Nat.lt_succ_of_lt (ZMod.val_lt _)⟩ : Fin (k + 1)) = j.castSucc :=
          Fin.ext (by simpa using hval)
        rw [harg] at this
        exact this
    subst hy
    have hc : c₁ = c₂ := hp₁.1.symm.trans hp₂.1
    subst hc
    rfl
  · intro z _
    let y : Fin (k + 1) → B := fun i => z (i.val : ZMod k)
    refine ⟨⟨z 0, y⟩, ?_, ?_⟩
    · simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and, y]
      exact ⟨by simp, by simp [ZMod.natCast_self]⟩
    · funext i
      simp only [y, ZMod.natCast_zmod_val]
  · intro ⟨c, y⟩ hp
    simp only [Q, Finset.mem_sigma, Finset.mem_univ, Finset.mem_filter, true_and] at hp
    let e : Fin k ≃ ZMod k :=
      { toFun := fun j => (j.val : ZMod k)
        invFun := fun i => ⟨i.val, ZMod.val_lt i⟩
        left_inv := fun j => Fin.ext (ZMod.val_natCast_of_lt j.isLt)
        right_inv := fun i => ZMod.natCast_zmod_val i }
    refine Fintype.prod_equiv e _ _ (fun j => ?_)
    dsimp only [e, Equiv.coe_fn_mk]
    have hval1 : ((j.val : ZMod k)).val = j.val := ZMod.val_natCast_of_lt j.isLt
    have harg1 : (⟨((j.val : ZMod k)).val, Nat.lt_succ_of_lt (ZMod.val_lt _)⟩ : Fin (k + 1)) = j.castSucc := by
      apply Fin.ext; simpa using hval1
    rw [harg1]
    congr 1
    by_cases hlt : j.val + 1 < k
    · have hval2 : ((j.val : ZMod k) + 1).val = j.val + 1 := by
        rw [show (j.val : ZMod k) + 1 = ((j.val + 1 : ℕ) : ZMod k) by push_cast; rfl]
        exact ZMod.val_natCast_of_lt hlt
      have harg2 : (⟨((j.val : ZMod k) + 1).val, Nat.lt_succ_of_lt (ZMod.val_lt _)⟩ : Fin (k + 1)) = j.succ := by
        apply Fin.ext; simpa using hval2
      rw [harg2]
    · have heqk : j.val + 1 = k := by omega
      have hzero : (j.val : ZMod k) + 1 = 0 := by
        rw [show (j.val : ZMod k) + 1 = ((j.val + 1 : ℕ) : ZMod k) by push_cast; rfl, heqk, ZMod.natCast_self]
      have hlast : j.succ = Fin.last k := by apply Fin.ext; simpa using heqk
      rw [hzero, hlast, hp.2, ← hp.1]
      congr 1
      apply Fin.ext
      simp [ZMod.val_zero]

def rot {k : ℕ} (s : ℕ) (word : ZMod k → B) (i : ZMod k) : B := word (i - (s : ZMod k))
def back {k : ℕ} (s : ℕ) (b : ZMod k → B) (i : ZMod k) : B := b (i + (s : ZMod k))
def mix {k : ℕ} (d : ℕ) (x : ZMod k → B) (i : ZMod k) : B := x (i - (d : ZMod k)) + x i + x (i + (d : ZMod k))
def nl {k : ℕ} (y : ZMod k → B) (j : ZMod k) : B := y j + (1 + y (j + 1)) * y (j + 2)

def kernel {k : ℕ} [NeZero k] (d : ℕ) (a b : ZMod k → B) : ℤ :=
  ∑ u ∈ Finset.univ.filter (fun v : ZMod k → B => mix d v = a),
    Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
      let i := (j : ZMod k)
      (fun (l h : B) => signZ ((u i + b i + b (i - 2)) * l + b (i - 1) * l * h) : Matrix B B ℤ))))

lemma dotProduct_rot_eq_back {k : ℕ} [NeZero k] (s : ℕ) (a w : ZMod k → B) :
    dotProduct a (rot s w) = dotProduct (back s a) w := by
  unfold dotProduct rot back
  exact Fintype.sum_equiv (Equiv.subRight (s : ZMod k)) _ _ (fun i => by simp)

lemma dotProduct_mix_self_adj {k : ℕ} [NeZero k] (d : ℕ) (u x : ZMod k → B) :
    dotProduct (mix d u) x = dotProduct u (mix d x) := by
  unfold dotProduct mix
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  have h1 : ∑ i : ZMod k, u (i - (d : ZMod k)) * x i = ∑ i : ZMod k, u i * x (i + (d : ZMod k)) :=
    Fintype.sum_equiv (Equiv.subRight (d : ZMod k)) _ _ (fun i => by simp)
  have h2 : ∑ i : ZMod k, u (i + (d : ZMod k)) * x i = ∑ i : ZMod k, u i * x (i - (d : ZMod k)) :=
    Fintype.sum_equiv (Equiv.addRight (d : ZMod k)) _ _ (fun i => by simp)
  rw [h1, h2]
  ring

lemma list_map_natCast_eq {k : ℕ} {α : Type*} (f : ZMod k → α) :
    ∀ l : List ℕ, (l.map (fun j => f (j : ZMod k))) = l.map (fun j : ℕ => f (j : ZMod k)) := by
  intro l
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp only [Bind.bind, Pure.pure, List.flatMap_cons, List.singleton_append, List.map_cons] at ih ⊢
      rw [ih]

lemma trace_kernel_eq {k : ℕ} [NeZero k] (u b : ZMod k → B) :
    Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
      let i := (j : ZMod k)
      (fun (l h : B) => signZ ((u i + b i + b (i - 2)) * l + b (i - 1) * l * h) : Matrix B B ℤ)))) =
    ∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nl y)) := by
  let f : ZMod k → Matrix B B ℤ := fun i =>
    (fun (l h : B) => signZ ((u i + b i + b (i - 2)) * l + b (i - 1) * l * h) : Matrix B B ℤ)
  change Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j => f (j : ZMod k)))) = _
  rw [list_map_natCast_eq f (List.range k)]
  rw [trace_list_prod_range f]
  apply Finset.sum_congr rfl
  intro y _
  rw [← signZ_sum]
  congr 1
  unfold dotProduct nl
  have hexp : ∑ i : ZMod k, ((u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1)) =
      (∑ i : ZMod k, u i * y i) + (∑ i : ZMod k, b i * y i) +
      (∑ i : ZMod k, b (i - 2) * y i) + (∑ i : ZMod k, b (i - 1) * y i * y (i + 1)) := by
    have h1 : ∀ i : ZMod k, ((u i + b i + b (i - 2)) * y i + b (i - 1) * y i * y (i + 1)) =
        u i * y i + b i * y i + b (i - 2) * y i + b (i - 1) * y i * y (i + 1) := fun i => by ring
    simp_rw [h1, Finset.sum_add_distrib]
  have hshift2 : ∑ i : ZMod k, b (i - 2) * y i = ∑ i : ZMod k, b i * y (i + 2) :=
    Fintype.sum_equiv (Equiv.subRight (2 : ZMod k)) _ _ (fun i => by simp)
  have hshift1 : ∑ i : ZMod k, b (i - 1) * y i * y (i + 1) =
      ∑ i : ZMod k, b i * (y (i + 1) * y (i + 2)) :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod k)) _ _ (fun i => by
      simp only [Equiv.subRight_apply, sub_add_cancel]
      have : i - 1 + 2 = i + 1 := by ring
      rw [this]; ring)
  rw [hexp, hshift2, hshift1]
  have hnl : ∑ i : ZMod k, b i * (y i + (1 + y (i + 1)) * y (i + 2)) =
      (∑ i : ZMod k, b i * y i) + (∑ i : ZMod k, b i * y (i + 2)) +
      (∑ i : ZMod k, b i * (y (i + 1) * y (i + 2))) := by
    have h1 : ∀ i : ZMod k, b i * (y i + (1 + y (i + 1)) * y (i + 2)) =
        b i * y i + b i * y (i + 2) + b i * (y (i + 1) * y (i + 2)) := fun i => by ring
    simp_rw [h1, Finset.sum_add_distrib]
  rw [hnl]
  ring

lemma single_round_transfer {k : ℕ} [NeZero k] (d : ℕ) (b x : ZMod k → B) :
    ∑ a : ZMod k → B, kernel d a b * signZ (dotProduct a x) =
      (2 : ℤ) ^ k * signZ (dotProduct b (nl (mix d x))) := by
  classical
  have h1 : ∑ a : ZMod k → B, kernel d a b * signZ (dotProduct a x) =
      ∑ a : ZMod k → B, ∑ u ∈ Finset.univ.filter (fun v : ZMod k → B => mix d v = a),
        (∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nl y))) * signZ (dotProduct a x) := by
    apply Finset.sum_congr rfl
    intro a _
    unfold kernel
    simp_rw [trace_kernel_eq, Finset.sum_mul]
  rw [h1]
  have h2 : ∑ a : ZMod k → B, ∑ u ∈ Finset.univ.filter (fun v : ZMod k → B => mix d v = a),
      (∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nl y))) * signZ (dotProduct a x) =
      ∑ u : ZMod k → B, (∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nl y))) *
        signZ (dotProduct (mix d u) x) := by
    have hfib := Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (ZMod k → B))) (t := (Finset.univ : Finset (ZMod k → B)))
      (g := mix d) (fun _ _ => Finset.mem_univ _)
      (f := fun u => (∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nl y))) *
        signZ (dotProduct (mix d u) x))
    rw [← hfib]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro u hu
    rw [(Finset.mem_filter.mp hu).2]
  rw [h2]
  have h3 : ∀ u : ZMod k → B,
      (∑ y : ZMod k → B, signZ (dotProduct u y + dotProduct b (nl y))) * signZ (dotProduct (mix d u) x) =
      ∑ y : ZMod k → B, signZ (dotProduct b (nl y)) * signZ (dotProduct u (y + mix d x)) := by
    intro u
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [dotProduct_mix_self_adj, ← signZ_add, ← signZ_add]
    congr 1
    rw [dotProduct_add]
    ring
  simp_rw [h3]
  rw [Finset.sum_comm]
  have h4 : ∀ y : ZMod k → B,
      ∑ u : ZMod k → B, signZ (dotProduct b (nl y)) * signZ (dotProduct u (y + mix d x)) =
      if y = mix d x then (2 : ℤ) ^ k * signZ (dotProduct b (nl (mix d x))) else 0 := by
    intro y
    rw [← Finset.mul_sum, sum_univ_sign]
    have hiff : y + mix d x = 0 ↔ y = mix d x := by
      constructor
      · intro hz; funext i; exact (zmod2_add_eq_zero_iff _ _).mp (congr_fun hz i)
      · intro heq; subst heq; funext i; exact zmod2_add_self _
    by_cases hy : y = mix d x
    · rw [if_pos (hiff.mpr hy), if_pos hy, hy]; ring
    · rw [if_neg (mt hiff.mp hy), if_neg hy, mul_zero]
  simp_rw [h4]
  simp

def orbitGen {k : ℕ} (r : ℕ) (row col : ZMod k → B) (C1 C2 : ℕ → ZMod k → B)
    (key : ZMod k → B) : (ZMod k → B) × (ZMod k → B) :=
  (List.range r).foldl (fun (st : (ZMod k → B) × (ZMod k → B)) tick =>
    (nl (mix 1 st.1) + rot (2 * tick) key + C1 (tick + 1),
     nl (mix 2 st.2) + rot (3 * (tick + 1) + 1) key + C2 (tick + 1)))
    (rot 1 key + row, rot 3 key + col)

def initialGen {k : ℕ} [NeZero k] (row col : ZMod k → B) (a b q : ZMod k → B) : ℤ :=
  if q + back 1 a + back 3 b = 0 then (2 : ℤ) ^ k * signZ (dotProduct a row + dotProduct b col) else 0

def HGen {k : ℕ} [NeZero k] (r : ℕ) (row col : ZMod k → B) (C1 C2 : ℕ → ZMod k → B) :
    (ZMod k → B) → (ZMod k → B) → (ZMod k → B) → ℤ :=
  (List.range r).foldl (fun (old : (ZMod k → B) → (ZMod k → B) → (ZMod k → B) → ℤ) roundIndex p s t =>
    signZ (dotProduct p (C1 (roundIndex + 1)) + dotProduct s (C2 (roundIndex + 1))) *
      ∑ a : ZMod k → B, ∑ b : ZMod k → B, kernel 1 a p * kernel 2 b s *
        old a b (t + back (2 * roundIndex) p + back (3 * (roundIndex + 1) + 1) s))
    (initialGen row col)

lemma HGen_eq {k : ℕ} [NeZero k] (r : ℕ) (row col : ZMod k → B) (C1 C2 : ℕ → ZMod k → B) :
    ∀ a b q : ZMod k → B,
      HGen r row col C1 C2 a b q =
        ((2 : ℤ) ^ k) ^ (2 * r) *
          ∑ w : ZMod k → B, signZ (dotProduct a (orbitGen r row col C1 C2 w).1 +
            dotProduct b (orbitGen r row col C1 C2 w).2 + dotProduct q w) := by
  induction r with
  | zero =>
      intro a b q
      simp only [HGen, orbitGen, initialGen, List.range_zero, List.foldl_nil, mul_zero, pow_zero, one_mul]
      have hterm : ∀ w : ZMod k → B,
          signZ (dotProduct a (rot 1 w + row) + dotProduct b (rot 3 w + col) + dotProduct q w) =
          signZ (dotProduct a row + dotProduct b col) *
            signZ (dotProduct (q + back 1 a + back 3 b) w) := by
        intro w
        rw [← signZ_add]
        congr 1
        rw [dotProduct_add, dotProduct_add, dotProduct_rot_eq_back, dotProduct_rot_eq_back, add_dotProduct, add_dotProduct]
        ring
      simp_rw [hterm, ← Finset.mul_sum]
      have hsym : ∑ w : ZMod k → B, signZ (dotProduct (q + back 1 a + back 3 b) w) =
          ∑ w : ZMod k → B, signZ (dotProduct w (q + back 1 a + back 3 b)) := by
        apply Finset.sum_congr rfl; intro w _; rw [dotProduct_comm]
      rw [hsym, sum_univ_sign]
      split_ifs <;> ring
  | succ m ih =>
      intro p s t
      have hHstep : HGen (m + 1) row col C1 C2 p s t =
          signZ (dotProduct p (C1 (m + 1)) + dotProduct s (C2 (m + 1))) *
            ∑ a : ZMod k → B, ∑ b : ZMod k → B, kernel 1 a p * kernel 2 b s *
              HGen m row col C1 C2 a b (t + back (2 * m) p + back (3 * (m + 1) + 1) s) := by
        simp only [HGen, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have horbstep : ∀ w : ZMod k → B,
          orbitGen (m + 1) row col C1 C2 w =
            (nl (mix 1 (orbitGen m row col C1 C2 w).1) + rot (2 * m) w + C1 (m + 1),
             nl (mix 2 (orbitGen m row col C1 C2 w).2) + rot (3 * (m + 1) + 1) w + C2 (m + 1)) := by
        intro w
        simp only [orbitGen, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [hHstep]
      set q' := t + back (2 * m) p + back (3 * (m + 1) + 1) s
      simp_rw [ih _ _ q']
      have hpull : ∑ a : ZMod k → B, ∑ b : ZMod k → B,
          kernel 1 a p * kernel 2 b s *
            (((2 : ℤ) ^ k) ^ (2 * m) *
              ∑ w : ZMod k → B, signZ (dotProduct a (orbitGen m row col C1 C2 w).1 +
                dotProduct b (orbitGen m row col C1 C2 w).2 + dotProduct q' w)) =
          ((2 : ℤ) ^ k) ^ (2 * m) *
            ∑ w : ZMod k → B, signZ (dotProduct q' w) *
              (∑ a : ZMod k → B, kernel 1 a p * signZ (dotProduct a (orbitGen m row col C1 C2 w).1)) *
              (∑ b : ZMod k → B, kernel 2 b s * signZ (dotProduct b (orbitGen m row col C1 C2 w).2)) := by
        have hinner : ∀ a b : ZMod k → B,
            kernel 1 a p * kernel 2 b s *
              (((2 : ℤ) ^ k) ^ (2 * m) *
                ∑ w : ZMod k → B, signZ (dotProduct a (orbitGen m row col C1 C2 w).1 +
                  dotProduct b (orbitGen m row col C1 C2 w).2 + dotProduct q' w)) =
            ((2 : ℤ) ^ k) ^ (2 * m) *
              ∑ w : ZMod k → B, signZ (dotProduct q' w) *
                (kernel 1 a p * signZ (dotProduct a (orbitGen m row col C1 C2 w).1)) *
                (kernel 2 b s * signZ (dotProduct b (orbitGen m row col C1 C2 w).2)) := by
          intro a b
          rw [← mul_assoc, mul_comm (kernel 1 a p * kernel 2 b s), mul_assoc, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro w _
          rw [signZ_add, signZ_add]
          ring
        simp_rw [hinner, ← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        have hswap : ∀ b : ZMod k → B,
            ∑ a : ZMod k → B, ∑ w : ZMod k → B,
              signZ (dotProduct q' w) *
                (kernel 1 a p * signZ (dotProduct a (orbitGen m row col C1 C2 w).1)) *
                (kernel 2 b s * signZ (dotProduct b (orbitGen m row col C1 C2 w).2)) =
            ∑ w : ZMod k → B, ∑ a : ZMod k → B,
              signZ (dotProduct q' w) *
                (kernel 1 a p * signZ (dotProduct a (orbitGen m row col C1 C2 w).1)) *
                (kernel 2 b s * signZ (dotProduct b (orbitGen m row col C1 C2 w).2)) :=
          fun _ => Finset.sum_comm
        simp_rw [hswap]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro w _
        have hfact : ∑ b : ZMod k → B, ∑ a : ZMod k → B,
            signZ (dotProduct q' w) *
              (kernel 1 a p * signZ (dotProduct a (orbitGen m row col C1 C2 w).1)) *
              (kernel 2 b s * signZ (dotProduct b (orbitGen m row col C1 C2 w).2)) =
            (∑ a : ZMod k → B, signZ (dotProduct q' w) *
              (kernel 1 a p * signZ (dotProduct a (orbitGen m row col C1 C2 w).1))) *
            (∑ b : ZMod k → B, kernel 2 b s * signZ (dotProduct b (orbitGen m row col C1 C2 w).2)) := by
          rw [Finset.sum_mul_sum, Finset.sum_comm]
        rw [hfact, ← Finset.mul_sum]
      rw [hpull]
      simp_rw [single_round_transfer]
      have hcomb : signZ (dotProduct p (C1 (m + 1)) + dotProduct s (C2 (m + 1))) *
          (((2 : ℤ) ^ k) ^ (2 * m) *
            ∑ w : ZMod k → B, signZ (dotProduct q' w) *
              ((2 : ℤ) ^ k * signZ (dotProduct p (nl (mix 1 (orbitGen m row col C1 C2 w).1)))) *
              ((2 : ℤ) ^ k * signZ (dotProduct s (nl (mix 2 (orbitGen m row col C1 C2 w).2))))) =
          ((2 : ℤ) ^ k) ^ (2 * (m + 1)) *
            ∑ w : ZMod k → B, signZ (dotProduct p (orbitGen (m + 1) row col C1 C2 w).1 +
              dotProduct s (orbitGen (m + 1) row col C1 C2 w).2 + dotProduct t w) := by
        have hpow : ((2 : ℤ) ^ k) ^ (2 * (m + 1)) = ((2 : ℤ) ^ k) ^ (2 * m) * ((2 : ℤ) ^ k * (2 : ℤ) ^ k) := by
          rw [mul_add, pow_add, pow_mul]; ring
        have hrew : signZ (dotProduct p (C1 (m + 1)) + dotProduct s (C2 (m + 1))) *
            (((2 : ℤ) ^ k) ^ (2 * m) *
              ∑ w : ZMod k → B, signZ (dotProduct q' w) *
                ((2 : ℤ) ^ k * signZ (dotProduct p (nl (mix 1 (orbitGen m row col C1 C2 w).1)))) *
                ((2 : ℤ) ^ k * signZ (dotProduct s (nl (mix 2 (orbitGen m row col C1 C2 w).2))))) =
            ∑ w : ZMod k → B, ((2 : ℤ) ^ k) ^ (2 * m) * ((2 : ℤ) ^ k * (2 : ℤ) ^ k) *
              (signZ (dotProduct p (C1 (m + 1)) + dotProduct s (C2 (m + 1))) *
                signZ (dotProduct q' w) *
                signZ (dotProduct p (nl (mix 1 (orbitGen m row col C1 C2 w).1))) *
                signZ (dotProduct s (nl (mix 2 (orbitGen m row col C1 C2 w).2)))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro w _; ring
        rw [hrew, hpow, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w _
        congr 1
        rw [← signZ_add, ← signZ_add, ← signZ_add, horbstep w]
        congr 1
        simp only [q', dotProduct_add, add_dotProduct]
        rw [← dotProduct_rot_eq_back (2 * m) p w, ← dotProduct_rot_eq_back (3 * (m + 1) + 1) s w]
        ring
      exact hcomb

lemma key_count_eq {k : ℕ} [NeZero k] (r : ℕ) (row col : ZMod k → B) (C1 C2 : ℕ → ZMod k → B)
    (S T : Finset (ZMod k)) (y z : ZMod k → B) :
    (∑ a ∈ Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0),
      ∑ b ∈ Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ T → mask i = 0),
        signZ (dotProduct a y + dotProduct b z) * HGen r row col C1 C2 a b 0) =
      ((2 : ℤ) ^ k) ^ (2 * r) * (2 : ℤ) ^ (S.card + T.card) *
        ((Finset.univ.filter (fun w : ZMod k → B =>
          (∀ i ∈ S, (orbitGen r row col C1 C2 w).1 i = y i) ∧
          (∀ j ∈ T, (orbitGen r row col C1 C2 w).2 j = z j))).card : ℤ) := by
  classical
  set supS := Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ S → mask i = 0)
  set supT := Finset.univ.filter (fun mask : ZMod k → B => ∀ i : ZMod k, i ∉ T → mask i = 0)
  simp_rw [HGen_eq r row col C1 C2 _ _ 0, zero_dotProduct, add_zero]
  have h1 : ∀ a b : ZMod k → B,
      signZ (dotProduct a y + dotProduct b z) *
        (((2 : ℤ) ^ k) ^ (2 * r) *
          ∑ w : ZMod k → B, signZ (dotProduct a (orbitGen r row col C1 C2 w).1 +
            dotProduct b (orbitGen r row col C1 C2 w).2)) =
      ((2 : ℤ) ^ k) ^ (2 * r) *
        ∑ w : ZMod k → B,
          signZ (dotProduct a ((orbitGen r row col C1 C2 w).1 + y)) *
          signZ (dotProduct b ((orbitGen r row col C1 C2 w).2 + z)) := by
    intro a b
    rw [mul_left_comm, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    rw [← signZ_add, ← signZ_add]
    congr 1
    rw [dotProduct_add, dotProduct_add]
    ring
  simp_rw [h1, ← Finset.mul_sum]
  rw [mul_assoc]
  congr 1
  have hswap : ∑ a ∈ supS, ∑ b ∈ supT, ∑ w : ZMod k → B,
        signZ (dotProduct a ((orbitGen r row col C1 C2 w).1 + y)) *
        signZ (dotProduct b ((orbitGen r row col C1 C2 w).2 + z)) =
      ∑ w : ZMod k → B,
        (∑ a ∈ supS, signZ (dotProduct a ((orbitGen r row col C1 C2 w).1 + y))) *
        (∑ b ∈ supT, signZ (dotProduct b ((orbitGen r row col C1 C2 w).2 + z))) := by
    have hinner : ∀ a ∈ supS,
        ∑ b ∈ supT, ∑ w : ZMod k → B,
          signZ (dotProduct a ((orbitGen r row col C1 C2 w).1 + y)) *
          signZ (dotProduct b ((orbitGen r row col C1 C2 w).2 + z)) =
        ∑ w : ZMod k → B, ∑ b ∈ supT,
          signZ (dotProduct a ((orbitGen r row col C1 C2 w).1 + y)) *
          signZ (dotProduct b ((orbitGen r row col C1 C2 w).2 + z)) :=
      fun _ _ => Finset.sum_comm
    rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.sum_mul_sum]
  rw [hswap]
  simp_rw [supS, supT, sum_supported_sign]
  have hterm : ∀ w : ZMod k → B,
      (if ∀ i ∈ S, ((orbitGen r row col C1 C2 w).1 + y) i = 0 then (2 : ℤ) ^ S.card else 0) *
      (if ∀ j ∈ T, ((orbitGen r row col C1 C2 w).2 + z) j = 0 then (2 : ℤ) ^ T.card else 0) =
      if (∀ i ∈ S, (orbitGen r row col C1 C2 w).1 i = y i) ∧
         (∀ j ∈ T, (orbitGen r row col C1 C2 w).2 j = z j) then (2 : ℤ) ^ (S.card + T.card) else 0 := by
    intro w
    have hS : (∀ i ∈ S, ((orbitGen r row col C1 C2 w).1 + y) i = 0) ↔
        (∀ i ∈ S, (orbitGen r row col C1 C2 w).1 i = y i) := by
      constructor <;> intro h i hi
      · exact (zmod2_add_eq_zero_iff _ _).mp (h i hi)
      · exact (zmod2_add_eq_zero_iff _ _).mpr (h i hi)
    have hT : (∀ j ∈ T, ((orbitGen r row col C1 C2 w).2 + z) j = 0) ↔
        (∀ j ∈ T, (orbitGen r row col C1 C2 w).2 j = z j) := by
      constructor <;> intro h j hj
      · exact (zmod2_add_eq_zero_iff _ _).mp (h j hj)
      · exact (zmod2_add_eq_zero_iff _ _).mpr (h j hj)
    by_cases hp1 : ∀ i ∈ S, (orbitGen r row col C1 C2 w).1 i = y i
    · by_cases hp2 : ∀ j ∈ T, (orbitGen r row col C1 C2 w).2 j = z j
      · rw [if_pos (hS.mpr hp1), if_pos (hT.mpr hp2), if_pos ⟨hp1, hp2⟩, pow_add]
      · rw [if_pos (hS.mpr hp1), if_neg (mt hT.mp hp2), if_neg (fun h => hp2 h.2), mul_zero]
    · rw [if_neg (mt hS.mp hp1), zero_mul, if_neg (fun h => hp1 h.1)]
  simp_rw [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

end PEqualNP.Outside.L_meta_25754_aux

theorem PEqualNP.Outside.L_meta_25754 : (∀ (k : ℕ) [NeZero k] (r : ℕ),
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let N := (2:ℤ)^k
  let sign := fun (t : B) => if t = 0 then (1 : ℤ) else -1
  let rot := fun (s : ℕ) (word : V) (i : I) => word (i-(s : I))
  let back := fun (s : ℕ) (b : V) (i : I) => b (i+(s : I))
  let mix := fun (d : ℕ) (x : V) (i : I) => x (i-(d : I)) + x i + x (i+(d : I))
  let nl := fun (y : V) (j : I) => y j + (1+y (j+1))*y (j+2)
  let kernel := fun (d : ℕ) (a b : V) =>
    ∑ u ∈ Finset.univ.filter (fun v : V => mix d v = a),
      Matrix.trace (List.prod (α := Matrix B B ℤ) ((List.range k).map (fun j =>
        let i := (j : I)
        (fun (l h : B) => sign ((u i+b i+b (i-2))*l+b (i-1)*l*h) : Matrix B B ℤ))))
  ∀ (row col : V) (C : ℕ → V),
    let orbit := fun (key : V) =>
      (List.range r).foldl (fun (st : V × V) tick =>
        (nl (mix 1 st.1) + rot (2*tick) key + C (tick+1),
         nl (mix 2 st.2) + rot (3*(tick+1)+1) key + C (r+tick+1)))
        (rot 1 key + row, rot 3 key + col)
    let initial := fun (a b q : V) =>
      if q + back 1 a + back 3 b = 0 then N*sign (dotProduct a row + dotProduct b col) else 0
    let H := (List.range r).foldl (fun (old : V → V → V → ℤ) roundIndex p s t =>
      sign (dotProduct p (C (roundIndex+1)) + dotProduct s (C (r+roundIndex+1))) *
        ∑ a : V, ∑ b : V, kernel 1 a p * kernel 2 b s *
          old a b (t + back (2*roundIndex) p + back (3*(roundIndex+1)+1) s)) initial
    (∀ a b q : V, H a b q = N^(2*r) *
      ∑ w : V, sign (dotProduct a (orbit w).1 + dotProduct b (orbit w).2 + dotProduct q w)) ∧
    ∀ (S T : Finset I) (y z : V),
      let supported := fun (sites : Finset I) => Finset.univ.filter (fun mask : V =>
        ∀ i : I, i ∉ sites → mask i = 0)
      let passing := Finset.univ.filter (fun w : V =>
        (∀ i ∈ S, (orbit w).1 i = y i) ∧ (∀ j ∈ T, (orbit w).2 j = z j))
      (∑ a ∈ supported S, ∑ b ∈ supported T,
        sign (dotProduct a y + dotProduct b z) * H a b 0) =
        N^(2*r) * (2:ℤ)^(S.card+T.card) * (passing.card : ℤ)) := by
  intro k _ r I B V N sign rot back mix nl kernel row col C orbit initial H
  let C2 : ℕ → V := fun n => C (r + n)
  constructor
  · intro a b q
    exact PEqualNP.Outside.L_meta_25754_aux.HGen_eq r row col C C2 a b q
  · intro S T y z supported passing
    exact PEqualNP.Outside.L_meta_25754_aux.key_count_eq r row col C C2 S T y z
