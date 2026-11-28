import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38526

open Finset

abbrev F2 := ZMod 2

def dot2 (x y : Fin 2 → F2) : F2 := x 0 * y 0 + x 1 * y 1

def nondeg (M : Fin 2 → Fin 2 → F2) : Prop :=
  ∀ w : Fin 2 → F2, (∀ b, w 0 * M 0 b + w 1 * M 1 b = 0) → w = 0

theorem perp_exists : ∀ β : Fin 2 → F2, ∃ w, w ≠ 0 ∧ dot2 w β = 0 := by
  unfold dot2; decide

theorem perp_unique : ∀ β w w' : Fin 2 → F2, β ≠ 0 → w ≠ 0 → w' ≠ 0 →
    dot2 w β = 0 → dot2 w' β = 0 → ∀ i, w i = w' i := by
  unfold dot2; decide

theorem dual2 : ∀ β1 β2 : Fin 2 → F2, (∀ w, dot2 w β1 = 0 → dot2 w β2 = 0 → w = 0) →
    ∃ γ1 γ2 : Fin 2 → F2, dot2 γ1 β1 = 1 ∧ dot2 γ2 β1 = 0 ∧ dot2 γ1 β2 = 0 ∧ dot2 γ2 β2 = 1 := by
  unfold dot2; decide

theorem two_eq : ∀ x : F2, x + x = 0 := by decide

theorem zero_or_one : ∀ x : F2, x = 0 ∨ x = 1 := by decide

theorem pick_eq (p : Fin 3 → Fin 3 → Fin 3) (hp : ∀ x y, p x y ≠ x ∧ p x y ≠ y) :
    ∀ x y, x ≠ y → p x y = -(x + y) := by
  intro x y hxy
  have h := hp x y
  generalize p x y = r at h
  fin_cases x <;> fin_cases y <;> fin_cases r <;> simp_all <;> decide

def ind (p : Fin 3 → Fin 3 → Fin 3) (k : Fin 2) (x y : Fin 3) : F2 :=
  if p x y = k.succ then 1 else 0

def Nf (p : Fin 3 → Fin 3 → Fin 3) (k a b : Fin 2) : F2 :=
  ind p k a.succ b.succ - ind p k a.succ 0 - ind p k 0 b.succ + ind p k 0 0

def Aof (p : Fin 3 → Fin 3 → Fin 3) (α : Fin 2 → F2) : Fin 2 → Fin 2 → F2 :=
  fun a b => α 0 * Nf p 0 a b + α 1 * Nf p 1 a b

def good (p : Fin 3 → Fin 3 → Fin 3) : Prop :=
  ∃ α β : Fin 2 → F2, Aof p α ≠ 0 ∧ nondeg (Aof p β) ∧ nondeg (Aof p β + Aof p α)

theorem good_q : ∀ q : Fin 3 → Fin 3, (∀ c, q c ≠ c) →
    good (fun x y => if x = y then q x else -(x + y)) := by
  unfold good nondeg
  decide

theorem good_of (p : Fin 3 → Fin 3 → Fin 3) (hp : ∀ x y, p x y ≠ x ∧ p x y ≠ y) : good p := by
  have e : p = fun x y => if x = y then p x x else -(x + y) := by
    funext x y
    split_ifs with h
    · subst h; rfl
    · exact pick_eq p hp x y h
  rw [e]
  exact good_q (fun c => p c c) (fun c => (hp c c).1)


section Abs

variable {ι : Type} [DecidableEq ι]

abbrev V (ι : Type) := ι × Fin 2 → F2

def rhs (M : Fin 2 → Fin 2 → F2) (j : ι) (z z' : V ι) : F2 :=
  ∑ a, ∑ b, M a b * z (j, a) * z' (j, b)

def zo (j0 : ι) : V ι →ₗ[F2] V ι where
  toFun z := fun p => if p.1 = j0 then 0 else z p
  map_add' x y := by
    funext p
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

def ins (j0 : ι) : (Fin 2 → F2) →ₗ[F2] V ι where
  toFun w := fun p => if p.1 = j0 then w p.2 else 0
  map_add' x y := by
    funext p
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' c x := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> simp

theorem f_two (f : (Fin 2 → F2) →ₗ[F2] F2) (w : Fin 2 → F2) :
    f w = dot2 w (fun b => f (Pi.single b 1)) := by
  have e : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  conv_lhs => rw [e]
  simp [dot2]

theorem rhs_single (M : Fin 2 → Fin 2 → F2) (j : ι) (a b : Fin 2) :
    rhs M j (Pi.single (j, a) 1) (Pi.single (j, b) 1) = M a b := by
  unfold rhs
  fin_cases a <;> fin_cases b <;> simp [Pi.single_apply]

theorem rhs_ins_single (M : Fin 2 → Fin 2 → F2) (j : ι) (w : Fin 2 → F2) (b : Fin 2) :
    rhs M j (ins j w) (Pi.single (j, b) 1) = w 0 * M 0 b + w 1 * M 1 b := by
  unfold rhs
  fin_cases b <;> simp [Fin.sum_univ_two, Pi.single_apply, ins] <;> ring

omit [DecidableEq ι] in
theorem rhs_add (M M' : Fin 2 → Fin 2 → F2) (j : ι) (z z' : V ι) :
    rhs (M + M') j z z' = rhs M j z z' + rhs M' j z z' := by
  unfold rhs
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem rhs_zo (M : Fin 2 → Fin 2 → F2) (j0 : ι) (z z' : V ι) :
    rhs M j0 z (zo j0 z') = 0 := by
  unfold rhs
  simp [zo]

theorem subst_sum {T : Type} [DecidableEq T] (S : Finset T) (i0 : T) (hi0 : i0 ∈ S)
    (c c0 P : T → F2) (h1 : c0 i0 = 1) :
    ∑ i ∈ S.erase i0, (c i + c i0 * c0 i) * P i =
      ∑ i ∈ S, c i * P i + c i0 * ∑ i ∈ S, c0 i * P i := by
  rw [← Finset.add_sum_erase S (fun i => c i * P i) hi0,
    ← Finset.add_sum_erase S (fun i => c0 i * P i) hi0, h1]
  simp only [add_mul, Finset.sum_add_distrib]
  have h2 := two_eq (c i0 * P i0)
  have hs : ∑ x ∈ S.erase i0, c i0 * c0 x * P x = c i0 * ∑ x ∈ S.erase i0, c0 x * P x := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  linear_combination hs - h2

theorem main_abs {T : Type} [DecidableEq T] (A B : ι → Fin 2 → Fin 2 → F2)
    (hA : ∀ j, A j ≠ 0) (hB : ∀ j, nondeg (B j)) (hAB : ∀ j, nondeg (B j + A j)) :
    ∀ (J : Finset ι) (S : Finset T) (u v : T → V ι →ₗ[F2] F2) (cA cB : ι → T → F2),
      (∀ j ∈ J, ∀ z z', ∑ i ∈ S, cA j i * (u i z * v i z') = rhs (A j) j z z') →
      (∀ j ∈ J, ∀ z z', ∑ i ∈ S, cB j i * (u i z * v i z') = rhs (B j) j z z') →
      3 * J.card ≤ S.card := by
  intro J
  induction J using Finset.induction_on with
  | empty => intros; simp
  | insert j0 J hj0 ih =>
    intro S u v cA cB hAid hBid
    have hj0m : j0 ∈ insert j0 J := Finset.mem_insert_self _ _
    obtain ⟨i0, hi0S, hi0⟩ : ∃ i0 ∈ S, cA j0 i0 = 1 := by
      by_contra hne
      push Not at hne
      have h0 : ∀ i ∈ S, cA j0 i = 0 := fun i hi =>
        (zero_or_one _).resolve_right (hne i hi)
      apply hA j0
      funext a b
      have := hAid j0 hj0m (Pi.single (j0, a) 1) (Pi.single (j0, b) 1)
      rw [rhs_single, Finset.sum_eq_zero (fun i hi => by rw [h0 i hi, zero_mul])] at this
      simp [← this]
    set S1 := S.erase i0 with hS1
    have hsub : ∀ (c : ι → T → F2) (M : ι → Fin 2 → Fin 2 → F2),
        (∀ j ∈ insert j0 J, ∀ z z', ∑ i ∈ S, c j i * (u i z * v i z') = rhs (M j) j z z') →
        ∀ j ∈ insert j0 J, ∀ z z', ∑ i ∈ S1, (c j i + c j i0 * cA j0 i) * (u i z * v i z') =
          rhs (M j) j z z' + c j i0 * rhs (A j0) j0 z z' := by
      intro c M hc j hj z z'
      rw [hS1, subst_sum S i0 hi0S (c j) (cA j0) (fun i => u i z * v i z') hi0, hc j hj,
        hAid j0 hj0m]
    -- the slice B' at j0
    obtain ⟨M, hM, hMid⟩ : ∃ M, nondeg M ∧ ∀ z z',
        ∑ i ∈ S1, (cB j0 i + cB j0 i0 * cA j0 i) * (u i z * v i z') = rhs M j0 z z' := by
      rcases zero_or_one (cB j0 i0) with h | h
      · refine ⟨B j0, hB j0, fun z z' => ?_⟩
        rw [hsub cB B hBid j0 hj0m, h]
        ring
      · refine ⟨B j0 + A j0, hAB j0, fun z z' => ?_⟩
        rw [hsub cB B hBid j0 hj0m, h, rhs_add]
        ring
    let β : T → Fin 2 → F2 := fun l b => u l (ins j0 (Pi.single b 1))
    have huins : ∀ l w, u l (ins j0 w) = dot2 w (β l) := fun l w => f_two ((u l).comp (ins j0)) w
    obtain ⟨l1, hl1, l2, hl2, hind⟩ : ∃ l1 ∈ S1, ∃ l2 ∈ S1,
        ∀ w, dot2 w (β l1) = 0 → dot2 w (β l2) = 0 → w = 0 := by
      by_contra hne
      push Not at hne
      obtain ⟨w, hw0, hw⟩ : ∃ w : Fin 2 → F2, w ≠ 0 ∧ ∀ l ∈ S1, dot2 w (β l) = 0 := by
        by_cases hall : ∀ l ∈ S1, β l = 0
        · obtain ⟨w, hw, _⟩ := perp_exists 0
          exact ⟨w, hw, fun l hl => by rw [hall l hl]; simp [dot2]⟩
        · push Not at hall
          obtain ⟨l0, hl0, hne0⟩ := hall
          obtain ⟨w, hw1, -, hwn⟩ := hne l0 hl0 l0 hl0
          refine ⟨w, hwn, fun l hl => ?_⟩
          obtain ⟨w', hw'1, hw'2, hw'n⟩ := hne l0 hl0 l hl
          have e : w = w' := funext (perp_unique _ _ _ hne0 hwn hw'n hw1 hw'1)
          rw [e]
          exact hw'2
      apply hw0
      apply hM w
      intro b
      have := hMid (ins j0 w) (Pi.single (j0, b) 1)
      rw [rhs_ins_single, Finset.sum_eq_zero (fun i hi => by rw [huins, hw i hi]; ring)] at this
      exact this.symm
    have hl12 : l1 ≠ l2 := by
      intro h
      subst h
      obtain ⟨w, hw, hw1⟩ := perp_exists (β l1)
      exact hw (hind w hw1 hw1)
    obtain ⟨γ1, γ2, h11, h21, h12, h22⟩ := dual2 (β l1) (β l2) hind
    let r : V ι →ₗ[F2] (Fin 2 → F2) :=
      ((u l1).comp (zo j0)).smulRight γ1 + ((u l2).comp (zo j0)).smulRight γ2
    let e : V ι →ₗ[F2] V ι := zo j0 + (ins j0).comp r
    have hdot : ∀ (x y : F2) (β' : Fin 2 → F2),
        dot2 (x • γ1 + y • γ2) β' = x * dot2 γ1 β' + y * dot2 γ2 β' := by
      intro x y β'
      simp only [dot2, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hue : ∀ l z, u l (e z) = u l (zo j0 z) + dot2 (r z) (β l) := by
      intro l z
      simp only [e, LinearMap.add_apply, LinearMap.comp_apply, map_add, huins]
    have hrz : ∀ z, r z = u l1 (zo j0 z) • γ1 + u l2 (zo j0 z) • γ2 := by
      intro z
      simp [r]
    have hk1 : ∀ z, u l1 (e z) = 0 := by
      intro z
      rw [hue, hrz, hdot, h11, h21, mul_one, mul_zero, add_zero]
      exact two_eq _
    have hk2 : ∀ z, u l2 (e z) = 0 := by
      intro z
      rw [hue, hrz, hdot, h12, h22, mul_one, mul_zero, zero_add]
      exact two_eq _
    have hez : ∀ z j a, j ≠ j0 → e z (j, a) = z (j, a) := by
      intro z j a hj
      simp [e, zo, ins, hj]
    have hzo : ∀ z' j b, j ≠ j0 → zo j0 z' (j, b) = z' (j, b) := by
      intro z' j b hj
      simp [zo, hj]
    set S2 := (S1.erase l1).erase l2 with hS2
    have hl2' : l2 ∈ S1.erase l1 := Finset.mem_erase.mpr ⟨hl12.symm, hl2⟩
    have hS2sub : S2 ⊆ S1 := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
    have hnew : ∀ (c : ι → T → F2) (M : ι → Fin 2 → Fin 2 → F2),
        (∀ j ∈ insert j0 J, ∀ z z', ∑ i ∈ S, c j i * (u i z * v i z') = rhs (M j) j z z') →
        ∀ j ∈ J, ∀ z z', ∑ i ∈ S2, (c j i + c j i0 * cA j0 i) *
          (((u i).comp e) z * ((v i).comp (zo j0)) z') = rhs (M j) j z z' := by
      intro c M hc j hj z z'
      have hjj : j ≠ j0 := fun h => hj0 (h ▸ hj)
      simp only [LinearMap.comp_apply]
      rw [Finset.sum_subset hS2sub, hsub c M hc j (Finset.mem_insert_of_mem hj), rhs_zo,
        mul_zero, add_zero]
      · unfold rhs
        refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
        rw [hez z j a hjj, hzo z' j b hjj]
      · intro i hi hi2
        have : i = l1 ∨ i = l2 := by
          by_contra hc'
          push Not at hc'
          exact hi2 (Finset.mem_erase.mpr ⟨hc'.2, Finset.mem_erase.mpr ⟨hc'.1, hi⟩⟩)
        rcases this with h | h <;> subst h <;> simp [hk1, hk2]
    have key := ih S2 (fun i => (u i).comp e) (fun i => (v i).comp (zo j0))
      (fun j i => cA j i + cA j i0 * cA j0 i) (fun j i => cB j i + cB j i0 * cA j0 i)
      (hnew cA A hAid) (hnew cB B hBid)
    have c1 := Finset.card_erase_of_mem hi0S
    have c2 := Finset.card_erase_of_mem hl1
    have c3 := Finset.card_erase_of_mem hl2'
    have c4 := Finset.card_pos.mpr ⟨i0, hi0S⟩
    rw [Finset.card_insert_of_notMem hj0]
    rw [← hS1] at c1
    rw [← hS2] at c3
    have c5 := Finset.card_pos.mpr ⟨l1, hl1⟩
    have c6 := Finset.card_pos.mpr ⟨l2, hl2'⟩
    omega

end Abs


def lin {P : Type} [Fintype P] (g : P → F2) : (P → F2) →ₗ[F2] F2 where
  toFun z := ∑ p, z p * g p
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc]

theorem lower (n t : ℕ) (pick : Fin n → Fin 3 → Fin 3 → Fin 3)
    (hpick : ∀ j x y, pick j x y ≠ x ∧ pick j x y ≠ y)
    (u v : Fin t → (Fin n → Fin 3) → F2) (a b : Fin n → Fin 2 → (Fin n → Fin 3) → F2)
    (coeff : Fin n → Fin 2 → Fin t → F2)
    (h : ∀ (x y : Fin n → Fin 3) (j : Fin n) (k : Fin 2),
      (if pick j (x j) (y j) = k.succ then (1 : F2) else 0) =
      a j k x + b j k y + ∑ i, coeff j k i * u i x * v i y) : 3 * n ≤ t := by
  let x0 : Fin n → Fin 3 := fun _ => 0
  let w : Fin n × Fin 2 → (Fin n → Fin 3) := fun p => Function.update x0 p.1 p.2.succ
  have hw : ∀ p j, w p j = if j = p.1 then p.2.succ else 0 := by
    intro p j
    simp only [w, Function.update_apply, x0]
  let U : Fin t → Fin n × Fin 2 → F2 := fun i p => u i (w p) - u i x0
  let Vv : Fin t → Fin n × Fin 2 → F2 := fun i p => v i (w p) - v i x0
  have hD : ∀ j k p q, ∑ i, coeff j k i * (U i p * Vv i q) =
      if p.1 = j ∧ q.1 = j then Nf (pick j) k p.2 q.2 else 0 := by
    intro j k p q
    have key : ∑ i, coeff j k i * (U i p * Vv i q) =
        (∑ i, coeff j k i * u i (w p) * v i (w q)) - (∑ i, coeff j k i * u i (w p) * v i x0)
        - (∑ i, coeff j k i * u i x0 * v i (w q)) + ∑ i, coeff j k i * u i x0 * v i x0 := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by simp only [U, Vv]; ring)
    rw [key]
    have h1 := h (w p) (w q) j k
    have h2 := h (w p) x0 j k
    have h3 := h x0 (w q) j k
    have h4 := h x0 x0 j k
    have e : ((if pick j (w p j) (w q j) = k.succ then (1 : F2) else 0)
        - (if pick j (w p j) (x0 j) = k.succ then (1 : F2) else 0)
        - (if pick j (x0 j) (w q j) = k.succ then (1 : F2) else 0)
        + (if pick j (x0 j) (x0 j) = k.succ then (1 : F2) else 0)) =
        if p.1 = j ∧ q.1 = j then Nf (pick j) k p.2 q.2 else 0 := by
      obtain ⟨pj, pa⟩ := p
      obtain ⟨qj, qa⟩ := q
      simp only [hw]
      rcases eq_or_ne pj j with hp | hp <;> rcases eq_or_ne qj j with hq | hq
      · subst hp; subst hq; simp [Nf, ind, x0]
      · subst hp
        rw [if_neg (show ¬(pj = qj) from fun h => hq h.symm),
          if_neg (show ¬(pj = pj ∧ qj = pj) from fun h => hq h.2)]
        ring
      · subst hq
        rw [if_neg (show ¬(qj = pj) from fun h => hp h.symm),
          if_neg (show ¬(pj = qj ∧ qj = qj) from fun h => hp h.1)]
        ring
      · rw [if_neg (show ¬(j = pj) from fun h => hp h.symm),
          if_neg (show ¬(j = qj) from fun h => hq h.symm),
          if_neg (show ¬(pj = j ∧ qj = j) from fun h => hp h.1)]
        ring
    linear_combination e - h1 + h2 + h3 - h4
  have hexp : ∀ (j : Fin n) (γ : Fin 2 → F2) (z z' : V (Fin n)),
      ∑ i, (γ 0 * coeff j 0 i + γ 1 * coeff j 1 i) * (lin (U i) z * lin (Vv i) z') =
        rhs (Aof (pick j) γ) j z z' := by
    intro j γ z z'
    have s1 : ∑ i, (γ 0 * coeff j 0 i + γ 1 * coeff j 1 i) * (lin (U i) z * lin (Vv i) z') =
        ∑ p, ∑ q, z p * z' q * (γ 0 * ∑ i, coeff j 0 i * (U i p * Vv i q) +
          γ 1 * ∑ i, coeff j 1 i * (U i p * Vv i q)) := by
      have t1 : ∀ i, (γ 0 * coeff j 0 i + γ 1 * coeff j 1 i) * (lin (U i) z * lin (Vv i) z') =
          ∑ p, ∑ q, z p * z' q * ((γ 0 * coeff j 0 i + γ 1 * coeff j 1 i) * (U i p * Vv i q)) := by
        intro i
        simp only [lin, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun q _ => by ring)
      rw [Finset.sum_congr rfl (fun i _ => t1 i), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun q _ => ?_)
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [s1]
    simp only [hD]
    have s2 : ∀ p q : Fin n × Fin 2, z p * z' q *
        (γ 0 * (if p.1 = j ∧ q.1 = j then Nf (pick j) 0 p.2 q.2 else 0) +
          γ 1 * (if p.1 = j ∧ q.1 = j then Nf (pick j) 1 p.2 q.2 else 0)) =
        if p.1 = j then (if q.1 = j then Aof (pick j) γ p.2 q.2 * z p * z' q else 0) else 0 := by
      intro p q
      by_cases hp : p.1 = j <;> by_cases hq : q.1 = j <;> simp [hp, hq, Aof] <;> ring
    simp only [s2, Fintype.sum_prod_type, rhs]
    simp
  obtain ⟨α, β, hα, hβ, hαβ⟩ : ∃ α β : Fin n → Fin 2 → F2,
      (∀ j, Aof (pick j) (α j) ≠ 0) ∧ (∀ j, nondeg (Aof (pick j) (β j))) ∧
        (∀ j, nondeg (Aof (pick j) (β j) + Aof (pick j) (α j))) := by
    choose α β h1 h2 h3 using fun j => good_of (pick j) (hpick j)
    exact ⟨α, β, h1, h2, h3⟩
  have := main_abs (fun j => Aof (pick j) (α j)) (fun j => Aof (pick j) (β j)) hα hβ hαβ
    Finset.univ Finset.univ (fun i => lin (U i)) (fun i => lin (Vv i))
    (fun j i => α j 0 * coeff j 0 i + α j 1 * coeff j 1 i)
    (fun j i => β j 0 * coeff j 0 i + β j 1 * coeff j 1 i)
    (fun j _ z z' => hexp j (α j) z z') (fun j _ z z' => hexp j (β j) z z')
  simpa using this


theorem local_id (p : Fin 3 → Fin 3 → Fin 3) (hp : ∀ x y, p x y ≠ x ∧ p x y ≠ y) (k : Fin 2)
    (X Y : Fin 3) :
    (if p X Y = k.succ then (1 : F2) else 0) =
      (if X = k.succ then 0 else 1) + (if Y = k.succ then 1 else 0) +
        (if X = Y then (if p X X = k.succ then 0 else 1) else 0) := by
  by_cases hXY : X = Y
  · subst hXY
    rw [if_pos rfl]
    generalize p X X = r
    by_cases h : r = k.succ <;> by_cases h' : X = k.succ <;>
      simp only [h, h', if_true, if_false] <;> decide
  · rw [pick_eq p hp X Y hXY, if_neg hXY]
    fin_cases X <;> fin_cases Y <;> fin_cases k <;> simp_all <;> decide

theorem upper (n t : ℕ) (pick : Fin n → Fin 3 → Fin 3 → Fin 3)
    (hpick : ∀ j x y, pick j x y ≠ x ∧ pick j x y ≠ y) (ht : 3 * n ≤ t) :
    ∃ (u v : Fin t → (Fin n → Fin 3) → F2) (a b : Fin n → Fin 2 → (Fin n → Fin 3) → F2)
      (coeff : Fin n → Fin 2 → Fin t → F2),
      ∀ (x y : Fin n → Fin 3) (j : Fin n) (k : Fin 2),
        (if pick j (x j) (y j) = k.succ then (1 : F2) else 0) =
        a j k x + b j k y + ∑ i, coeff j k i * u i x * v i y := by
  let u : Fin t → (Fin n → Fin 3) → F2 := fun i x =>
    ∑ j : Fin n, if i.val = 3 * j.val + (x j).val then 1 else 0
  have hu : ∀ (x : Fin n → Fin 3) (j : Fin n) (c : Fin 3) (h : 3 * j.val + c.val < t),
      u ⟨3 * j.val + c.val, h⟩ x = if x j = c then 1 else 0 := by
    intro x j c h
    simp only [u]
    rw [Finset.sum_eq_single j]
    · by_cases hx : x j = c
      · simp [hx]
      · rw [if_neg, if_neg hx]
        intro h'
        apply hx
        ext
        simp at h'
        omega
    · intro j' _ hj'
      rw [if_neg]
      intro h'
      apply hj'
      have := (x j').isLt
      have := c.isLt
      ext
      try simp at h'
      omega
    · simp
  refine ⟨u, u, fun j k x => if x j = k.succ then 0 else 1, fun j k y => if y j = k.succ then 1 else 0,
    fun j k i => ∑ c : Fin 3, if i.val = 3 * j.val + c.val then
      (if pick j c c = k.succ then 0 else 1) else 0, ?_⟩
  intro x y j k
  have hlt : ∀ c : Fin 3, 3 * j.val + c.val < t := by
    intro c
    have := c.isLt
    have := j.isLt
    omega
  have hs : ∑ i : Fin t, (∑ c : Fin 3, if i.val = 3 * j.val + c.val then
      (if pick j c c = k.succ then (0 : F2) else 1) else 0) * u i x * u i y =
      if x j = y j then (if pick j (x j) (x j) = k.succ then 0 else 1) else 0 := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have e : ∀ c : Fin 3, (∑ i : Fin t, (if i.val = 3 * j.val + c.val then
        (if pick j c c = k.succ then (0 : F2) else 1) else 0) * u i x * u i y) =
        (if pick j c c = k.succ then (0 : F2) else 1) * (if x j = c then 1 else 0) *
          (if y j = c then 1 else 0) := by
      intro c
      rw [Finset.sum_eq_single ⟨3 * j.val + c.val, hlt c⟩]
      · rw [hu x j c (hlt c), hu y j c (hlt c), if_pos rfl]
      · intro i _ hi
        rw [if_neg, zero_mul, zero_mul]
        intro h'
        apply hi
        ext
        exact h'
      · simp
    rw [Finset.sum_congr rfl (fun c _ => e c)]
    rw [Finset.sum_eq_single (x j)]
    · by_cases h : x j = y j
      · simp [h]
      · simp [h, Ne.symm h]
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  rw [hs]
  exact local_id (pick j) (hpick j) k (x j) (y j)

end PEqualNP.Outside.L_meta_38526

open PEqualNP.Outside.L_meta_38526 in
theorem PEqualNP.Outside.L_meta_38526 : ∀ (n t : Nat) (pick : Fin n → Fin 3 → Fin 3 → Fin 3),
  (∀ j x y, pick j x y ≠ x ∧ pick j x y ≠ y) →
  let W := Fin n → Fin 3
  let F := ZMod 2
  (∃ (u v : Fin t → W → F) (a b : Fin n → Fin 2 → W → F)
     (coeff : Fin n → Fin 2 → Fin t → F),
    ∀ (x y : W) (j : Fin n) (k : Fin 2),
      (if pick j (x j) (y j) = k.succ then (1 : F) else 0) =
      a j k x + b j k y + ∑ i, coeff j k i * u i x * v i y) ↔ 3*n ≤ t := by
  intro n t pick hpick W F
  constructor
  · rintro ⟨u, v, a, b, coeff, h⟩
    exact lower n t pick hpick u v a b coeff h
  · intro ht
    exact upper n t pick hpick ht
