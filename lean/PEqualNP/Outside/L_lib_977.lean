import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_977_aux

theorem s_add (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (b c : ZMod 2) :
    s (b + c) = s b * s c := by
  rw [hs, hs, hs]
  fin_cases b <;> fin_cases c <;> decide

theorem char_sum (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (n : ℕ)
    (z : Fin n → ZMod 2) :
    ∑ a : Fin n → ZMod 2, s (dotProduct a z) = if z = 0 then (2 : ℤ) ^ n else 0 := by
  split_ifs with hz
  · subst hz
    simp only [dotProduct_zero, hs, ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
      ZMod.card, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  · obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hz (funext h)
    have hzi : z i = 1 := by
      have h2 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
      exact h2 _ hi
    let e : Fin n → ZMod 2 := Pi.single i 1
    have hez : dotProduct e z = 1 := by
      simp only [e, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, hzi]
    have key : ∀ a : Fin n → ZMod 2, s (dotProduct (a + e) z) = - s (dotProduct a z) := by
      intro a
      rw [add_dotProduct, s_add s hs, hez, hs 1]
      simp
    have h := Fintype.sum_equiv (Equiv.addRight e) (fun a => s (dotProduct (a + e) z))
      (fun a => s (dotProduct a z)) (fun a => rfl)
    simp only [key, Finset.sum_neg_distrib] at h
    linarith

theorem ortho (s : ZMod 2 → ℤ) (hs : ∀ b, s b = if b = 0 then 1 else -1) (n : ℕ)
    (x y : Fin n → ZMod 2) :
    ∑ a : Fin n → ZMod 2, s (dotProduct a x) * s (dotProduct a y) =
      if x = y then (2 : ℤ) ^ n else 0 := by
  have h1 : ∀ a : Fin n → ZMod 2, s (dotProduct a x) * s (dotProduct a y) = s (dotProduct a (x + y)) := by
    intro a
    rw [dotProduct_add, s_add s hs]
  simp only [h1]
  rw [char_sum s hs n (x + y)]
  have h2 : ∀ t u : ZMod 2, t + u = 0 ↔ t = u := by decide
  have h3 : (x + y = 0) ↔ (x = y) := by
    simp only [funext_iff, Pi.add_apply, Pi.zero_apply, h2]
  simp only [h3]

end PEqualNP.Outside.L_lib_977_aux

open PEqualNP.Outside.L_lib_977_aux in
theorem PEqualNP.Outside.L_lib_977 : (∀ (d : ℕ) (_ : 0 < d),
  let V := Fin d → ZMod 2
  let ones : V := fun _ => 1
  let parity := fun x : V => dotProduct ones x
  let W := fun (H : V → ℕ) (a : V) =>
    ∑ x : V, (H x : ℤ) * (if dotProduct a x = 0 then (1 : ℤ) else -1)
  let full := fun (H : V → ℕ) => ∀ a : V, a ≠ 0 →
    ∃ x y : V, 0 < H x ∧ 0 < H y ∧ dotProduct a x ≠ dotProduct a y
  ∀ A B : V → ℕ,
    ((∀ a, a ≠ ones → W A a = W B a) ∧ (¬ full A) ∧ full B) ↔
    ∃ (e : ZMod 2) (k : ℕ) (H : V → ℕ),
      0 < k ∧ (∃ x, 0 < H x) ∧ (∀ x, parity x ≠ e → H x = 0) ∧
      ∀ x, A x = H x + (if parity x = e then k else 0) ∧
        B x = H x + (if parity x = e then 0 else k)) := by
  intro d hd V ones parity W full A B
  let s : ZMod 2 → ℤ := fun b => if b = 0 then 1 else -1
  have hs : ∀ b, s b = if b = 0 then 1 else -1 := fun _ => rfl
  have z2 : ∀ t e : ZMod 2, t ≠ e ↔ t = e + 1 := by decide
  have hones : ones ≠ 0 := by
    intro h
    have := congrFun h ⟨0, hd⟩
    exact one_ne_zero this
  have base : ∀ c : ZMod 2, ∃ y : V, parity y = c := by
    intro c
    fin_cases c
    · refine ⟨0, ?_⟩
      show dotProduct ones 0 = _
      rw [dotProduct_zero]
      rfl
    · refine ⟨Pi.single ⟨0, hd⟩ 1, ?_⟩
      show dotProduct ones (Pi.single ⟨0, hd⟩ 1) = 1
      rw [dotProduct_single, mul_one]
  have full_of : ∀ (H : V → ℕ) (c : ZMod 2), (∀ x, parity x = c → 0 < H x) →
      (∃ x0, parity x0 ≠ c ∧ 0 < H x0) → full H := by
    intro H c hall hx0 a ha
    obtain ⟨y0, hy0⟩ := base c
    by_cases hao : a = ones
    · obtain ⟨x0, hx0c, hx0pos⟩ := hx0
      refine ⟨x0, y0, hx0pos, hall y0 hy0, ?_⟩
      rw [hao]
      show parity x0 ≠ parity y0
      rw [hy0]
      exact hx0c
    · have hi : ∃ i, a i = 1 := by
        by_contra h
        push_neg at h
        apply ha
        funext i
        have h1 : ∀ t : ZMod 2, t ≠ 1 → t = 0 := by decide
        exact h1 _ (h i)
      have hj : ∃ j, a j = 0 := by
        by_contra h
        push_neg at h
        apply hao
        funext j
        have h1 : ∀ t : ZMod 2, t ≠ 0 → t = 1 := by decide
        exact h1 _ (h j)
      obtain ⟨i, hi⟩ := hi
      obtain ⟨j, hj⟩ := hj
      let x : V := y0 + Pi.single i 1 + Pi.single j 1
      have hpx : parity x = c := by
        show dotProduct ones (y0 + Pi.single i 1 + Pi.single j 1) = c
        rw [dotProduct_add, dotProduct_add, dotProduct_single, dotProduct_single]
        show parity y0 + 1 * 1 + 1 * 1 = c
        rw [hy0]
        have h2 : ∀ t : ZMod 2, t + 1 * 1 + 1 * 1 = t := by decide
        exact h2 c
      refine ⟨x, y0, hall x hpx, hall y0 hy0, ?_⟩
      show dotProduct a (y0 + Pi.single i 1 + Pi.single j 1) ≠ dotProduct a y0
      rw [dotProduct_add, dotProduct_add, dotProduct_single, dotProduct_single, hi, hj]
      have h3 : ∀ t : ZMod 2, t + 1 * 1 + 0 * 1 ≠ t := by decide
      exact h3 _
  have not_full_of : ∀ (H : V → ℕ) (c : ZMod 2), (∀ x, 0 < H x → parity x = c) → ¬ full H := by
    intro H c hc hfull
    obtain ⟨x, y, hx, hy, hne⟩ := hfull ones hones
    exact hne ((hc x hx).trans (hc y hy).symm)
  have inv : ∀ (f : V → ℤ) (y : V),
      ∑ a : V, (∑ x : V, f x * s (dotProduct a x)) * s (dotProduct y a) = 2 ^ d * f y := by
    intro f y
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have inner : ∀ x : V, ∑ a : V, f x * s (dotProduct a x) * s (dotProduct y a) =
        f x * (if x = y then (2:ℤ) ^ d else 0) := by
      intro x
      rw [← ortho s hs d x y, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [dotProduct_comm y a]
      ring
    simp only [inner, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  have hW : ∀ (H : V → ℕ) (a : V), W H a = ∑ x : V, (H x : ℤ) * s (dotProduct a x) := fun _ _ => rfl
  constructor
  · rintro ⟨hWeq, hA, hB⟩
    let D : V → ℤ := fun x => (A x : ℤ) - B x
    have hWD : ∀ a, ∑ x : V, D x * s (dotProduct a x) = W A a - W B a := by
      intro a
      rw [hW, hW, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      simp only [D]
      ring
    have key : ∀ y, 2 ^ d * D y = (W A ones - W B ones) * s (dotProduct y ones) := by
      intro y
      rw [← inv D y]
      simp only [hWD]
      rw [Finset.sum_eq_single ones]
      · intro a _ ha
        rw [hWeq a ha, sub_self, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    have hDy : ∀ y, D y = D 0 * s (parity y) := by
      intro y
      have h1 := key y
      have h0 := key 0
      have hp : dotProduct y ones = parity y := dotProduct_comm y ones
      rw [hp] at h1
      rw [zero_dotProduct, hs 0, if_pos rfl, mul_one] at h0
      rw [← h0] at h1
      have h2 : (2 : ℤ) ^ d ≠ 0 := pow_ne_zero _ (by norm_num)
      apply mul_left_cancel₀ h2
      rw [h1]
      ring
    have finish : ∀ (e : ZMod 2) (k : ℕ), 0 < k →
        (∀ x, D x = if parity x = e then (k : ℤ) else -k) →
        ∃ (e : ZMod 2) (k : ℕ) (H : V → ℕ),
          0 < k ∧ (∃ x, 0 < H x) ∧ (∀ x, parity x ≠ e → H x = 0) ∧
          ∀ x, A x = H x + (if parity x = e then k else 0) ∧
            B x = H x + (if parity x = e then 0 else k) := by
      intro e k hk hD
      have hAB : ∀ x, (parity x = e → A x = B x + k) ∧ (parity x ≠ e → B x = A x + k) := by
        intro x
        have h := hD x
        simp only [D] at h
        constructor
        · intro hx
          rw [if_pos hx] at h
          omega
        · intro hx
          rw [if_neg hx] at h
          omega
      refine ⟨e, k, fun x => if parity x = e then B x else A x, hk, ?_, ?_, ?_⟩
      · by_contra hnone
        push_neg at hnone
        apply not_full_of B (e + 1) _ hB
        intro x hx
        by_cases he : parity x = e
        · have := hnone x
          simp only [he, ite_true] at this
          omega
        · exact (z2 _ _).1 he
      · intro x hx
        simp only [hx, ite_false]
        by_contra hpos
        apply hA
        apply full_of A e
        · intro y hy
          have := (hAB y).1 hy
          omega
        · exact ⟨x, hx, Nat.pos_of_ne_zero hpos⟩
      · intro x
        by_cases hx : parity x = e
        · simp only [hx, ite_true, add_zero]
          exact ⟨(hAB x).1 hx, trivial⟩
        · simp only [hx, ite_false, add_zero]
          exact ⟨trivial, (hAB x).2 hx⟩
    rcases lt_trichotomy (D 0) 0 with hneg | hzero | hpos
    · apply finish 1 (-D 0).toNat (by omega)
      intro x
      rw [hDy x, hs]
      have hz : ∀ t : ZMod 2, t = 0 ↔ ¬ t = 1 := by decide
      by_cases hx : parity x = 1
      · rw [if_pos hx, if_neg ((hz _).not.mpr (not_not.mpr hx))]
        omega
      · rw [if_neg hx, if_pos ((hz _).mpr hx)]
        omega
    · exfalso
      have hAB : A = B := by
        funext x
        have := hDy x
        rw [hzero, zero_mul] at this
        simp only [D] at this
        omega
      rw [hAB] at hA
      exact hA hB
    · apply finish 0 (D 0).toNat (by omega)
      intro x
      rw [hDy x, hs]
      by_cases hx : parity x = 0
      · rw [if_pos hx, if_pos hx]
        omega
      · rw [if_neg hx, if_neg hx]
        omega
  · rintro ⟨e, k, H, hk, ⟨x0, hx0⟩, hHsupp, hAB⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      rw [← sub_eq_zero, hW, hW, ← Finset.sum_sub_distrib]
      have hss : ∀ t : ZMod 2, s t * s t = 1 := by
        intro t
        rw [hs]
        split_ifs <;> norm_num
      have hsn : ∀ t : ZMod 2, s (t + 1) = - s t := by
        intro t
        fin_cases t <;> decide
      have hdiff : ∀ x : V, (A x : ℤ) - B x = (k : ℤ) * s e * s (parity x) := by
        intro x
        by_cases hx : parity x = e
        · have h1 := (hAB x).1
          have h2 := (hAB x).2
          rw [if_pos hx] at h1 h2
          rw [hx, mul_assoc, hss e, h1, h2]
          push_cast
          ring
        · have h1 := (hAB x).1
          have h2 := (hAB x).2
          rw [if_neg hx] at h1 h2
          rw [(z2 _ _).1 hx, hsn e, h1, h2]
          push_cast
          linear_combination (k : ℤ) * hss e
      have hterm : ∀ x : V, (A x : ℤ) * s (dotProduct a x) - (B x : ℤ) * s (dotProduct a x) =
          (k : ℤ) * s e * (s (dotProduct x ones) * s (dotProduct x a)) := by
        intro x
        have hp : dotProduct x ones = parity x := dotProduct_comm x ones
        rw [hp, dotProduct_comm x a, ← sub_mul, hdiff x]
        ring
      simp only [hterm]
      rw [← Finset.mul_sum, ortho s hs d ones a, if_neg (Ne.symm ha), mul_zero]
    · apply not_full_of A e
      intro x hx
      by_contra hne
      have h0 := hHsupp x hne
      have := (hAB x).1
      rw [h0, if_neg hne] at this
      omega
    · apply full_of B (e + 1)
      · intro x hx
        have hne : parity x ≠ e := by
          rw [hx]
          have : ∀ t : ZMod 2, t + 1 ≠ t := by decide
          exact this e
        have := (hAB x).2
        rw [if_neg hne] at this
        omega
      · refine ⟨x0, ?_, ?_⟩
        · have hpe : parity x0 = e := by
            by_contra hne
            have := hHsupp x0 hne
            omega
          rw [hpe]
          have : ∀ t : ZMod 2, t ≠ t + 1 := by decide
          exact this e
        · have := (hAB x0).2
          omega
