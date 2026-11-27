import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_751

theorem left_of {n m : Nat} (X A : Fin n → Fin m → Bool) (S : Finset (Fin n)) (J : Finset (Fin m))
    (f g : Bool → Bool)
    (hA : ∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j)))
    (hf : f false = true → f true = true) (hg : g false = true → g true = true) :
    ∀ j ∈ J, ∀ l ∈ J, (∀ i, X i j = true → X i l = true) → (∀ i, A i j = true → A i l = true) := by
  intro j hj l hl hX i hij
  rw [hA i j hj] at hij
  rw [hA i l hl]
  have hX' := hX i
  by_cases hi : i ∈ S
  · simp only [hi, ite_true] at hij ⊢
    cases hxj : X i j <;> cases hxl : X i l <;> simp_all
  · simp only [hi, ite_false] at hij ⊢
    cases hxj : X i j <;> cases hxl : X i l <;> simp_all

theorem right_of {n m : Nat} (X A : Fin n → Fin m → Bool) (S : Finset (Fin n)) (J : Finset (Fin m))
    (f g : Bool → Bool)
    (hA : ∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j)))
    (hf : f true = true → f false = true) (hg : g true = true → g false = true) :
    ∀ j ∈ J, ∀ l ∈ J, (∀ i, X i j = true → X i l = true) → (∀ i, A i l = true → A i j = true) := by
  intro j hj l hl hX i hil
  rw [hA i l hl] at hil
  rw [hA i j hj]
  have hX' := hX i
  by_cases hi : i ∈ S
  · simp only [hi, ite_true] at hil ⊢
    cases hxj : X i j <;> cases hxl : X i l <;> simp_all
  · simp only [hi, ite_false] at hil ⊢
    cases hxj : X i j <;> cases hxl : X i l <;> simp_all

/-- When the marked readout is the opposite of the ordinary one, every marked row is constant on J. -/
theorem marked_const {n m : Nat} (X A : Fin n → Fin m → Bool) (S : Finset (Fin n)) (J : Finset (Fin m))
    (f g : Bool → Bool)
    (hA : ∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j)))
    (hfg : ∀ b, g b = !f b)
    (hS : ∀ i ∈ S, ∃ k ∉ S, (∀ j ∈ J, X i j = X k j) ∧
      ((∀ j ∈ J, A i j = true → A k j = true) ∨ (∀ j ∈ J, A k j = true → A i j = true))) :
    ∀ i ∈ S, ∀ j ∈ J, ∀ l ∈ J, A i j = A i l := by
  intro i hi j hj l hl
  obtain ⟨k, hk, hXk, hc⟩ := hS i hi
  have ai : ∀ t ∈ J, A i t = !f (X i t) := fun t ht => by rw [hA i t ht, if_pos hi, hfg]
  have ak : ∀ t ∈ J, A k t = f (X i t) := fun t ht => by rw [hA k t ht, if_neg hk, hXk t ht]
  rcases hc with h | h
  · have c : ∀ t ∈ J, A i t = false := by
      intro t ht
      have := h t ht
      rw [ai t ht, ak t ht] at this
      rw [ai t ht]
      cases hv : f (X i t) <;> simp_all
    rw [c j hj, c l hl]
  · have c : ∀ t ∈ J, A i t = true := by
      intro t ht
      have := h t ht
      rw [ai t ht, ak t ht] at this
      rw [ai t ht]
      cases hv : f (X i t) <;> simp_all
    rw [c j hj, c l hl]

theorem const_left {n m : Nat} (X A : Fin n → Fin m → Bool) (S : Finset (Fin n)) (J : Finset (Fin m))
    (f g : Bool → Bool)
    (hA : ∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j)))
    (hc : ∀ i ∈ S, ∀ j ∈ J, ∀ l ∈ J, A i j = A i l) (hf : f false = true → f true = true) :
    ∀ j ∈ J, ∀ l ∈ J, (∀ i, X i j = true → X i l = true) → (∀ i, A i j = true → A i l = true) := by
  intro j hj l hl hX i hij
  by_cases hi : i ∈ S
  · rw [← hc i hi j hj l hl]; exact hij
  · rw [hA i j hj, if_neg hi] at hij
    rw [hA i l hl, if_neg hi]
    have hX' := hX i
    cases hxj : X i j <;> cases hxl : X i l <;> simp_all

theorem const_right {n m : Nat} (X A : Fin n → Fin m → Bool) (S : Finset (Fin n)) (J : Finset (Fin m))
    (f g : Bool → Bool)
    (hA : ∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j)))
    (hc : ∀ i ∈ S, ∀ j ∈ J, ∀ l ∈ J, A i j = A i l) (hf : f true = true → f false = true) :
    ∀ j ∈ J, ∀ l ∈ J, (∀ i, X i j = true → X i l = true) → (∀ i, A i l = true → A i j = true) := by
  intro j hj l hl hX i hil
  by_cases hi : i ∈ S
  · rw [hc i hi j hj l hl]; exact hil
  · rw [hA i l hl, if_neg hi] at hil
    rw [hA i j hj, if_neg hi]
    have hX' := hX i
    cases hxj : X i j <;> cases hxl : X i l <;> simp_all

end PEqualNP.Outside.L_lib_751

open PEqualNP.Outside.L_lib_751 in
theorem PEqualNP.Outside.L_lib_751 : ∀ (n m : Nat) (X A : Fin n → Fin m → Bool)
    (S : Finset (Fin n)) (J : Finset (Fin m)) (f g : Bool → Bool),
  let rowLE := fun i k : Fin n => ∀ j ∈ J, A i j = true → A k j = true
  let colLE := fun (T : Fin n → Fin m → Bool) (j l : Fin m) =>
    ∀ i, T i j = true → T i l = true
  (∀ i j, j ∈ J → A i j = (if i ∈ S then g (X i j) else f (X i j))) →
  (∀ i ∈ S, ∃ k ∉ S, (∀ j ∈ J, X i j = X k j) ∧ (rowLE i k ∨ rowLE k i)) →
  (∀ j ∈ J, ∀ l ∈ J, colLE X j l → colLE A j l) ∨
  (∀ j ∈ J, ∀ l ∈ J, colLE X j l → colLE A l j) := by
  intro n m X A S J f g rowLE colLE hA hS
  simp only [rowLE, colLE] at hS ⊢
  rcases hf0 : f false <;> rcases hf1 : f true <;> rcases hg0 : g false <;> rcases hg1 : g true
  all_goals first
    | (apply Or.inl; apply left_of X A S J f g hA <;> simp [hf0, hf1, hg0, hg1]
       done)
    | (apply Or.inr; apply right_of X A S J f g hA <;> simp [hf0, hf1, hg0, hg1]
       done)
    | (apply Or.inl
       apply const_left X A S J f g hA (marked_const X A S J f g hA _ hS)
       · simp [hf0, hf1]
       · intro b; cases b <;> simp [hf0, hf1, hg0, hg1]
       done)
    | (apply Or.inr
       apply const_right X A S J f g hA (marked_const X A S J f g hA _ hS)
       · simp [hf0, hf1]
       · intro b; cases b <;> simp [hf0, hf1, hg0, hg1]
       done)
