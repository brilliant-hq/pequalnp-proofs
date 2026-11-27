import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_194

private def insertPick {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    Fin (n + 1) ↪ Fin (m + 1) :=
  Fin.Embedding.cons (f.trans (finSuccAboveEquiv p).asEmbedding) (a := p) (by
    rintro ⟨i, hi⟩
    exact ((finSuccAboveEquiv p) (f i)).property hi)

private theorem insertPick_zero {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m) :
    insertPick p f 0 = p := rfl

private theorem insertPick_succ {n m : ℕ} (p : Fin (m + 1)) (f : Fin n ↪ Fin m)
    (i : Fin n) : insertPick p f i.succ = p.succAbove (f i) := rfl

private noncomputable def pickEquiv (n m : ℕ) :
    Fin (m + 1) × (Fin n ↪ Fin m) ≃ (Fin (n + 1) ↪ Fin (m + 1)) :=
  Equiv.ofBijective (fun pf => insertPick pf.1 pf.2) (by
    constructor
    · rintro ⟨p, f⟩ ⟨q, g⟩ h
      have hpq : p = q := congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e 0) h
      subst q
      congr 1
      apply Function.Embedding.ext
      intro i
      apply Fin.succAbove_right_injective
      exact congrArg (fun e : Fin (n + 1) ↪ Fin (m + 1) => e i.succ) h
    · intro e
      let p := e 0
      let f : Fin n ↪ Fin m :=
        ((Fin.Embedding.tail e).codRestrict {j : Fin (m + 1) | j ≠ p} (fun i hi =>
          Fin.succ_ne_zero i (e.injective hi))).trans (finSuccAboveEquiv p).symm.toEmbedding
      refine ⟨(p, f), ?_⟩
      apply Function.Embedding.ext
      intro i
      change insertPick p f i = e i
      refine Fin.cases rfl (fun j => ?_) i
      rw [insertPick_succ]
      exact congrArg Subtype.val ((finSuccAboveEquiv p).apply_symm_apply
        ⟨e j.succ, fun h => Fin.succ_ne_zero j (e.injective h)⟩))

private theorem sumPick {n m : ℕ} (g : (Fin (n + 1) ↪ Fin (m + 1)) → ℂ) :
    (∑ f, g f) = ∑ j : Fin (m + 1), ∑ f : Fin n ↪ Fin m, g (insertPick j f) := by
  rw [← (pickEquiv n m).sum_comp g, Fintype.sum_prod_type]
  rfl

private def entry (c d : ℂ) (j : Fin 4) (s : ℕ) : ℂ :=
  1 + (if s = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0)
    else c * (if j.val = s then (1 : ℂ) else if j.val = (s + 1) % 4 then Complex.I
      else if j.val = (s + 2) % 4 then -Complex.I else -1))

private def fiber (c d : ℂ) (p0 : Fin 5) : ℂ :=
  ∑ f : Fin 3 ↪ Fin 4, ∏ j : Fin 4, entry c d j (insertPick p0 f j).val

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem fiber_0 (c d : ℂ) :
    fiber c d 0 = 24 - 6 * d + 30 * c - 8 * c * d - 2 * c * d * Complex.I + 10 * c ^ 2 -
      2 * c ^ 2 * d - 2 * c ^ 2 * d * Complex.I + 4 * c ^ 3 - 2 * c ^ 3 * Complex.I -
      2 * c ^ 4 * Complex.I := by
  unfold fiber
  simp only [sumPick (n := 2) (m := 3), sumPick (n := 1) (m := 2), sumPick (n := 0) (m := 1)]
  simp only [Fintype.sum_unique, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  simp +decide [entry, Fin.succAbove]
  linear_combination (-c ^ 2 * d + c ^ 3 - c ^ 3 * Complex.I - c ^ 3 * d + c ^ 4 - c ^ 4 * Complex.I) * Complex.I_sq

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem fiber_1 (c d : ℂ) :
    fiber c d 1 = 24 - 6 * d - 30 * c + 6 * c * d + 10 * c ^ 2 - 2 * c ^ 2 * d +
      2 * c ^ 2 * d * Complex.I - 4 * c ^ 3 + 2 * c ^ 3 * Complex.I + 2 * c ^ 3 * d -
      2 * c ^ 3 * d * Complex.I - 2 * c ^ 4 * Complex.I := by
  unfold fiber
  simp only [sumPick (n := 2) (m := 3), sumPick (n := 1) (m := 2), sumPick (n := 0) (m := 1)]
  simp only [Fintype.sum_unique, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  simp +decide [entry, Fin.succAbove]
  linear_combination (c ^ 2 * d - c ^ 3 + c ^ 3 * Complex.I - c ^ 3 * d + c ^ 4 - c ^ 4 * Complex.I) * Complex.I_sq

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem fiber_2 (c d : ℂ) :
    fiber c d 2 = 24 - 6 * d - 30 * c * Complex.I + 2 * c * d + 8 * c * d * Complex.I -
      10 * c ^ 2 + 2 * c ^ 2 * d - 2 * c ^ 2 * d * Complex.I - 2 * c ^ 3 +
      4 * c ^ 3 * Complex.I + 2 * c ^ 4 * Complex.I := by
  unfold fiber
  simp only [sumPick (n := 2) (m := 3), sumPick (n := 1) (m := 2), sumPick (n := 0) (m := 1)]
  simp only [Fintype.sum_unique, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  simp +decide [entry, Fin.succAbove]
  linear_combination (10 * c ^ 2 - 3 * c ^ 2 * d + 3 * c ^ 3 - 5 * c ^ 3 * Complex.I + c ^ 3 * d * Complex.I - 3 * c ^ 4 * Complex.I + c ^ 4 * Complex.I ^ 2) * Complex.I_sq

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem fiber_3 (c d : ℂ) :
    fiber c d 3 = 24 - 6 * d + 30 * c * Complex.I - 6 * c * d * Complex.I - 10 * c ^ 2 +
      2 * c ^ 2 * d + 2 * c ^ 2 * d * Complex.I + 2 * c ^ 3 - 4 * c ^ 3 * Complex.I -
      2 * c ^ 3 * d + 2 * c ^ 3 * d * Complex.I + 2 * c ^ 4 * Complex.I := by
  unfold fiber
  simp only [sumPick (n := 2) (m := 3), sumPick (n := 1) (m := 2), sumPick (n := 0) (m := 1)]
  simp only [Fintype.sum_unique, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  simp +decide [entry, Fin.succAbove]
  linear_combination (10 * c ^ 2 - c ^ 2 * d - 3 * c ^ 3 + 5 * c ^ 3 * Complex.I + 2 * c ^ 3 * d - c ^ 3 * d * Complex.I - 3 * c ^ 4 * Complex.I + c ^ 4 * Complex.I ^ 2) * Complex.I_sq

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem fiber_4 (c d : ℂ) :
    fiber c d 4 = 24 + 24 * d := by
  unfold fiber
  simp only [sumPick (n := 2) (m := 3), sumPick (n := 1) (m := 2), sumPick (n := 0) (m := 1)]
  simp only [Fintype.sum_unique, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Fin.prod_univ_succ, Fin.prod_univ_zero, insertPick_zero, insertPick_succ, mul_one]
  simp +decide [entry, Fin.succAbove]
  linear_combination (4 * c ^ 2 + 4 * c ^ 2 * d) * Complex.I_sq

end PEqualNP.Outside.L_gct_194

open PEqualNP.Outside.L_gct_194 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  change (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, entry c d j (f j).val) = 120
  rw [sumPick (n := 3) (m := 4)]
  change (∑ p0 : Fin 5, fiber c d p0) = 120
  rw [Fin.sum_univ_five, fiber_0, fiber_1, fiber_2, fiber_3, fiber_4]
  ring
