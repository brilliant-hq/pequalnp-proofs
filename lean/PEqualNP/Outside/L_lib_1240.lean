import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1240

/-! ### Part 1: Binary expansion identity -/

private lemma sum_testBit_two_pow : ∀ (m d : Nat), d < 2 ^ m →
    (∑ j : Fin m, if d.testBit j.val = true then (2 : ℤ) ^ j.val else 0) = (d : ℤ) := by
  intro m
  induction m with
  | zero =>
    intro d hd
    have hd0 : d = 0 := by omega
    subst hd0; simp
  | succ m ih =>
    intro d hd
    rw [Fin.sum_univ_succ]
    have hd2 : d / 2 < 2 ^ m := by
      have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    have hrest : (∑ j : Fin m, if d.testBit (j.val + 1) = true then (2 : ℤ) ^ (j.val + 1) else 0) =
        2 * ∑ j : Fin m, if (d / 2).testBit j.val = true then (2 : ℤ) ^ j.val else 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Nat.testBit_succ]
      split_ifs
      · ring
      · ring
    have h0 : (if d.testBit (0 : Fin (m + 1)).val = true then (2 : ℤ) ^ (0 : Fin (m + 1)).val else 0) =
        ((d % 2 : Nat) : ℤ) := by
      simp only [Fin.val_zero, Nat.testBit_zero]
      have hm : d % 2 = 0 ∨ d % 2 = 1 := by omega
      rcases hm with h | h <;> simp [h]
    have hrec := ih (d / 2) hd2
    have hEq : (∑ j : Fin m, if d.testBit j.succ.val = true then (2 : ℤ) ^ j.succ.val else 0) =
        2 * ((d / 2 : Nat) : ℤ) := by
      simpa only [Fin.val_succ] using hrest.trans (congrArg (2 * ·) hrec)
    rw [h0, hEq]
    omega

/-! ### Part 2: Single torsion block for `d ≥ 2` -/

private abbrev BlkIdx (L : Nat) := Fin (3 * L) ⊕ Unit

private def blkAdj (d : Nat) : BlkIdx (Nat.log2 d) → BlkIdx (Nat.log2 d) → Bool :=
  let L := Nat.log2 d
  fun r c =>
    match r with
    | Sum.inl rv =>
      let j := rv.val / 3
      let rem := rv.val % 3
      let prevCol : BlkIdx L :=
        if hj : j = 0 then Sum.inr () else Sum.inl ⟨3 * j - 1, by have := rv.isLt; omega⟩
      if rem = 0 then
        decide (c = Sum.inl rv ∨ c = prevCol)
      else if rem = 1 then
        decide (c = Sum.inl rv ∨ c = prevCol)
      else
        decide (c = Sum.inl ⟨3 * j, by have := rv.isLt; omega⟩ ∨
                c = Sum.inl ⟨3 * j + 1, by have := rv.isLt; omega⟩ ∨
                c = Sum.inl rv)
    | Sum.inr () =>
      match c with
      | Sum.inr () => d.testBit 0
      | Sum.inl cv => decide (cv.val % 3 = 2) && d.testBit (cv.val / 3 + 1)

private def blkMat (d : Nat) : Matrix (BlkIdx (Nat.log2 d)) (BlkIdx (Nat.log2 d)) ℤ :=
  fun r c => if blkAdj d r c = true then 1 else 0

private def blkL (d : Nat) : Matrix (Fin (3 * Nat.log2 d)) (Fin (3 * Nat.log2 d)) ℤ :=
  fun r c => blkMat d (Sum.inl r) (Sum.inl c)

private def blkUvec (d : Nat) : Fin (3 * Nat.log2 d) → ℤ :=
  fun r => blkMat d (Sum.inl r) (Sum.inr ())

private def blkWvec (d : Nat) : Fin (3 * Nat.log2 d) → ℤ :=
  fun c => blkMat d (Sum.inr ()) (Sum.inl c)

private def blkB0 (d : Nat) : ℤ :=
  blkMat d (Sum.inr ()) (Sum.inr ())

private def blkLinv (d : Nat) : Matrix (Fin (3 * Nat.log2 d)) (Fin (3 * Nat.log2 d)) ℤ :=
  fun r c =>
    let jr := r.val / 3
    let rr := r.val % 3
    let jc := c.val / 3
    let rc := c.val % 3
    if jr < jc then 0
    else if jr = jc then
      if rr = 0 then (if rc = 0 then 1 else 0)
      else if rr = 1 then (if rc = 1 then 1 else 0)
      else (if rc = 2 then 1 else -1)
    else
      let sgn : ℤ := if rc = 2 then 1 else -1
      if rr = 2 then (2 : ℤ) ^ (jr - jc) * sgn
      else -((2 : ℤ) ^ (jr - 1 - jc)) * sgn

private def blkX0 (d : Nat) : Fin (3 * Nat.log2 d) → ℤ :=
  fun r =>
    let j := r.val / 3
    if r.val % 3 = 2 then (2 : ℤ) ^ (j + 1) else -((2 : ℤ) ^ j)

private lemma blkLinv_lt {d : Nat} (x c : Fin (3 * Nat.log2 d)) (h : x.val / 3 < c.val / 3) :
    blkLinv d x c = 0 := by
  unfold blkLinv; simp only [h, ↓reduceIte]

private lemma blkLinv_eq_j {d : Nat} (x c : Fin (3 * Nat.log2 d)) (h : x.val / 3 = c.val / 3) :
    blkLinv d x c =
      if x.val % 3 = 0 then (if c.val % 3 = 0 then 1 else 0)
      else if x.val % 3 = 1 then (if c.val % 3 = 1 then 1 else 0)
      else (if c.val % 3 = 2 then 1 else -1) := by
  unfold blkLinv
  rw [ite_eq_right (by omega), ite_eq_left h]

private lemma blkLinv_gt {d : Nat} (x c : Fin (3 * Nat.log2 d)) (h : c.val / 3 < x.val / 3) :
    blkLinv d x c =
      let sgn : ℤ := if c.val % 3 = 2 then 1 else -1
      if x.val % 3 = 2 then (2 : ℤ) ^ (x.val / 3 - c.val / 3) * sgn
      else -((2 : ℤ) ^ (x.val / 3 - 1 - c.val / 3)) * sgn := by
  unfold blkLinv
  simp only [show ¬ x.val / 3 < c.val / 3 by omega, show ¬ x.val / 3 = c.val / 3 by omega, ↓reduceIte]

private lemma blkL_mul_blkLinv (d : Nat) : blkL d * blkLinv d = 1 := by
  ext r c
  rw [Matrix.mul_apply, Matrix.one_apply]
  let L := Nat.log2 d
  set jr := r.val / 3
  set rr := r.val % 3
  set jc := c.val / 3
  set rc := c.val % 3
  have hrj : r.val / 3 = jr := rfl
  have hrr' : r.val % 3 = rr := rfl
  have hcj : c.val / 3 = jc := rfl
  have hcr' : c.val % 3 = rc := rfl
  have hr_eq : r.val = 3 * jr + rr := by omega
  have hrr : rr = 0 ∨ rr = 1 ∨ rr = 2 := by omega
  have hrc : rc = 0 ∨ rc = 1 ∨ rc = 2 := by omega
  rcases hrr with hrr0 | hrr1 | hrr2
  · -- rem = 0: support is {r} (if jr = 0) or {r, prev} (if jr > 0)
    by_cases hj0 : jr = 0
    · have hsupp : ∀ t : Fin (3 * L), t ≠ r → blkL d r t * blkLinv d t c = 0 := by
        intro t ht
        have hzero : blkL d r t = 0 := by
          unfold blkL blkMat
          rw [ite_eq_right]
          unfold blkAdj
          simp only [hrj, hrr', hrr0, ↓reduceIte, dite_eq_left hj0, decide_eq_true_eq,
            Sum.inl.injEq, reduceCtorEq, or_false]
          exact ht
        rw [hzero, zero_mul]
      rw [Finset.sum_eq_single r (fun t _ ht => hsupp t ht) (fun h => absurd (Finset.mem_univ r) h)]
      have hdiag : blkL d r r = 1 := by
        unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr0, hj0]
      rw [hdiag, one_mul]
      dsimp only [blkLinv]; simp only [hrj, hrr', hcj, hcr']
      by_cases hrc_eq : r = c
      · subst hrc_eq
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left hrr0, ite_eq_left hrr0]
      · rw [ite_eq_right hrc_eq]
        by_cases hjc0 : jc = 0
        · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left hrr0]
          have hrc_ne : rc ≠ 0 := by
            intro h; apply hrc_eq; apply Fin.ext; omega
          rw [ite_eq_right hrc_ne]
        · rw [ite_eq_left (by omega)]
    · let prev : Fin (3 * L) := ⟨3 * jr - 1, by have := r.isLt; omega⟩
      have hprev_ne : prev ≠ r := by
        intro h; have := congrArg Fin.val h; dsimp only [prev] at this; omega
      have hsupp : ∀ t : Fin (3 * L), t ∉ ({r, prev} : Finset (Fin (3 * L))) →
          blkL d r t * blkLinv d t c = 0 := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
        have hzero : blkL d r t = 0 := by
          unfold blkL blkMat
          rw [ite_eq_right]
          unfold blkAdj
          simp only [hrj, hrr', hrr0, ↓reduceIte, dite_eq_right hj0, decide_eq_true_eq, Sum.inl.injEq]
          rintro (h1 | h2)
          · exact ht.1 h1
          · exact ht.2 (Fin.ext (congrArg Fin.val h2))
        rw [hzero, zero_mul]
      have hsum2 : ∑ t : Fin (3 * L), blkL d r t * blkLinv d t c =
          blkL d r r * blkLinv d r c + blkL d r prev * blkLinv d prev c := by
        rw [← Finset.sum_subset (Finset.subset_univ ({r, prev} : Finset (Fin (3 * L))))
          (fun t _ ht => hsupp t ht)]
        rw [Finset.sum_pair hprev_ne.symm]
      rw [hsum2]
      have hL1 : blkL d r r = 1 := by
        unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr0, hj0]
      have hL2 : blkL d r prev = 1 := by
        unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr0, hj0, prev]
      rw [hL1, hL2, one_mul, one_mul]
      have hpj : prev.val / 3 = jr - 1 := by dsimp only [prev]; omega
      have hpr : prev.val % 3 = 2 := by dsimp only [prev]; omega
      by_cases hlt : jr < jc
      · have hne : r ≠ c := by intro h; subst h; omega
        rw [ite_eq_right hne, blkLinv_lt r c (by omega), blkLinv_lt prev c (by omega), add_zero]
      · by_cases heq : jr = jc
        · rw [blkLinv_eq_j r c (by omega), blkLinv_lt prev c (by omega), add_zero]
          rw [hrr', hrr0, hcr']
          simp only [↓reduceIte]
          by_cases hrc0 : rc = 0
          · have hreq : r = c := Fin.ext (by omega)
            rw [ite_eq_left hreq, ite_eq_left hrc0]
          · have hne : r ≠ c := by intro h; subst h; omega
            rw [ite_eq_right hne, ite_eq_right hrc0]
        · have hne : r ≠ c := by intro h; subst h; omega
          rw [ite_eq_right hne, blkLinv_gt r c (by omega), hrj, hrr', hcj, hcr', hrr0]
          simp only [(by decide : (0 : Nat) ≠ 2), ↓reduceIte]
          by_cases hpeq : jr - 1 = jc
          · rw [blkLinv_eq_j prev c (by omega), hpr, hcr']
            simp only [(by decide : (2 : Nat) ≠ 0), (by decide : (2 : Nat) ≠ 1), ↓reduceIte]
            have hz : jr - 1 - jc = 0 := by omega
            rw [hz, pow_zero]; split_ifs <;> ring
          · rw [blkLinv_gt prev c (by omega), hpj, hpr, hcj, hcr']
            simp only [↓reduceIte]; ring
  · -- rem = 1: identical to rem = 0 with rr = 1
    by_cases hj0 : jr = 0
    · have hsupp : ∀ t : Fin (3 * L), t ≠ r → blkL d r t * blkLinv d t c = 0 := by
        intro t ht
        have hzero : blkL d r t = 0 := by
          unfold blkL blkMat
          rw [ite_eq_right]
          unfold blkAdj
          simp only [hrj, hrr', hrr1, (by decide : (1 : Nat) ≠ 0), ↓reduceIte, dite_eq_left hj0,
            decide_eq_true_eq, Sum.inl.injEq, reduceCtorEq, or_false]
          exact ht
        rw [hzero, zero_mul]
      rw [Finset.sum_eq_single r (fun t _ ht => hsupp t ht) (fun h => absurd (Finset.mem_univ r) h)]
      have hdiag : blkL d r r = 1 := by
        unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr1, hj0]
      rw [hdiag, one_mul]
      dsimp only [blkLinv]; simp only [hrj, hrr', hcj, hcr']
      by_cases hrc_eq : r = c
      · subst hrc_eq
        rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left rfl,
          ite_eq_right (by omega), ite_eq_left hrr1, ite_eq_left hrr1]
      · rw [ite_eq_right hrc_eq]
        by_cases hjc0 : jc = 0
        · rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left hrr1]
          have hrc_ne : rc ≠ 1 := by
            intro h; apply hrc_eq; apply Fin.ext; omega
          rw [ite_eq_right hrc_ne]
        · rw [ite_eq_left (by omega)]
    · let prev : Fin (3 * L) := ⟨3 * jr - 1, by have := r.isLt; omega⟩
      have hprev_ne : prev ≠ r := by
        intro h; have := congrArg Fin.val h; dsimp only [prev] at this; omega
      have hsupp : ∀ t : Fin (3 * L), t ∉ ({r, prev} : Finset (Fin (3 * L))) →
          blkL d r t * blkLinv d t c = 0 := by
        intro t ht
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
        have hzero : blkL d r t = 0 := by
          unfold blkL blkMat
          rw [ite_eq_right]
          unfold blkAdj
          simp only [hrj, hrr', hrr1, (by decide : (1 : Nat) ≠ 0), ↓reduceIte, dite_eq_right hj0,
            decide_eq_true_eq, Sum.inl.injEq]
          rintro (h1 | h2)
          · exact ht.1 h1
          · exact ht.2 (Fin.ext (congrArg Fin.val h2))
        rw [hzero, zero_mul]
      have hsum2 : ∑ t : Fin (3 * L), blkL d r t * blkLinv d t c =
          blkL d r r * blkLinv d r c + blkL d r prev * blkLinv d prev c := by
        rw [← Finset.sum_subset (Finset.subset_univ ({r, prev} : Finset (Fin (3 * L))))
          (fun t _ ht => hsupp t ht)]
        rw [Finset.sum_pair hprev_ne.symm]
      rw [hsum2]
      have hL1 : blkL d r r = 1 := by
        unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr1, hj0]
      have hL2 : blkL d r prev = 1 := by
        unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr1, hj0, prev]
      rw [hL1, hL2, one_mul, one_mul]
      have hpj : prev.val / 3 = jr - 1 := by dsimp only [prev]; omega
      have hpr : prev.val % 3 = 2 := by dsimp only [prev]; omega
      by_cases hlt : jr < jc
      · have hne : r ≠ c := by intro h; subst h; omega
        rw [ite_eq_right hne, blkLinv_lt r c (by omega), blkLinv_lt prev c (by omega), add_zero]
      · by_cases heq : jr = jc
        · rw [blkLinv_eq_j r c (by omega), blkLinv_lt prev c (by omega), add_zero]
          rw [hrr', hrr1, hcr']
          simp only [(by decide : (1 : Nat) ≠ 0), ↓reduceIte]
          by_cases hrc1 : rc = 1
          · have hreq : r = c := Fin.ext (by omega)
            rw [ite_eq_left hreq, ite_eq_left hrc1]
          · have hne : r ≠ c := by intro h; subst h; omega
            rw [ite_eq_right hne, ite_eq_right hrc1]
        · have hne : r ≠ c := by intro h; subst h; omega
          rw [ite_eq_right hne, blkLinv_gt r c (by omega), hrj, hrr', hcj, hcr', hrr1]
          simp only [(by decide : (1 : Nat) ≠ 2), ↓reduceIte]
          by_cases hpeq : jr - 1 = jc
          · rw [blkLinv_eq_j prev c (by omega), hpr, hcr']
            simp only [(by decide : (2 : Nat) ≠ 0), (by decide : (2 : Nat) ≠ 1), ↓reduceIte]
            have hz : jr - 1 - jc = 0 := by omega
            rw [hz, pow_zero]; split_ifs <;> ring
          · rw [blkLinv_gt prev c (by omega), hpj, hpr, hcj, hcr']
            simp only [↓reduceIte]; ring
  · -- rem = 2: support is {t0, t1, r}
    let t0 : Fin (3 * L) := ⟨3 * jr, by have := r.isLt; omega⟩
    let t1 : Fin (3 * L) := ⟨3 * jr + 1, by have := r.isLt; omega⟩
    have hne01 : t0 ≠ t1 := by intro h; have := congrArg Fin.val h; dsimp only [t0, t1] at this; omega
    have hne0r : t0 ≠ r := by intro h; have := congrArg Fin.val h; dsimp only [t0] at this; omega
    have hne1r : t1 ≠ r := by intro h; have := congrArg Fin.val h; dsimp only [t1] at this; omega
    have hsupp : ∀ t : Fin (3 * L), t ∉ ({t0, t1, r} : Finset (Fin (3 * L))) →
        blkL d r t * blkLinv d t c = 0 := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
      have hzero : blkL d r t = 0 := by
        unfold blkL blkMat
        rw [ite_eq_right]
        unfold blkAdj
        simp only [hrj, hrr', hrr2, (by decide : (2 : Nat) ≠ 0), (by decide : (2 : Nat) ≠ 1), ↓reduceIte,
          decide_eq_true_eq, Sum.inl.injEq]
        rintro (h1 | h2 | h3)
        · exact ht.1 (Fin.ext (congrArg Fin.val h1))
        · exact ht.2.1 (Fin.ext (congrArg Fin.val h2))
        · exact ht.2.2 h3
      rw [hzero, zero_mul]
    have hsum3 : ∑ t : Fin (3 * L), blkL d r t * blkLinv d t c =
        blkL d r t0 * blkLinv d t0 c + (blkL d r t1 * blkLinv d t1 c + blkL d r r * blkLinv d r c) := by
      rw [← Finset.sum_subset (Finset.subset_univ ({t0, t1, r} : Finset (Fin (3 * L))))
        (fun t _ ht => hsupp t ht)]
      rw [Finset.sum_insert (by simp [hne01, hne0r]), Finset.sum_pair hne1r]
    rw [hsum3]
    have hL0 : blkL d r t0 = 1 := by
      unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr2, t0]
    have hL1 : blkL d r t1 = 1 := by
      unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr2, t1]
    have hL2 : blkL d r r = 1 := by
      unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr2]
    rw [hL0, hL1, hL2, one_mul, one_mul, one_mul]
    have ht0j : t0.val / 3 = jr := by dsimp only [t0]; omega
    have ht0r : t0.val % 3 = 0 := by dsimp only [t0]; omega
    have ht1j : t1.val / 3 = jr := by dsimp only [t1]; omega
    have ht1r : t1.val % 3 = 1 := by dsimp only [t1]; omega
    by_cases hlt : jr < jc
    · have hne : r ≠ c := by intro h; subst h; omega
      rw [ite_eq_right hne, blkLinv_lt t0 c (by omega), blkLinv_lt t1 c (by omega), blkLinv_lt r c (by omega)]
      ring
    · by_cases heq : jr = jc
      · rw [blkLinv_eq_j t0 c (by omega), blkLinv_eq_j t1 c (by omega), blkLinv_eq_j r c (by omega)]
        rw [ht0r, ht1r, hrr', hrr2, hcr']
        rcases hrc with hrc0 | hrc1 | hrc2
        · have hne : r ≠ c := by intro h; subst h; omega
          rw [ite_eq_right hne, hrc0]; norm_num
        · have hne : r ≠ c := by intro h; subst h; omega
          rw [ite_eq_right hne, hrc1]; norm_num
        · have hreq : r = c := Fin.ext (by omega)
          rw [ite_eq_left hreq, hrc2]; norm_num
      · have hne : r ≠ c := by intro h; subst h; omega
        rw [ite_eq_right hne, blkLinv_gt t0 c (by omega), blkLinv_gt t1 c (by omega), blkLinv_gt r c (by omega)]
        rw [ht0j, ht0r, ht1j, ht1r, hrj, hrr', hrr2, hcj, hcr']
        simp only [(by decide : (0 : Nat) ≠ 2), (by decide : (1 : Nat) ≠ 2), ↓reduceIte]
        have hpow : (2 : ℤ) ^ (jr - jc) = 2 * (2 : ℤ) ^ (jr - 1 - jc) := by
          have hexp : jr - jc = (jr - 1 - jc) + 1 := by omega
          rw [hexp, pow_succ]; ring
        rw [hpow]; ring

private lemma blkLinv_mul_blkL (d : Nat) : blkLinv d * blkL d = 1 := by
  have hdet : IsUnit (blkL d).det := by
    have h1 : (blkL d * blkLinv d).det = 1 := by rw [blkL_mul_blkLinv, Matrix.det_one]
    rw [Matrix.det_mul] at h1
    exact ⟨⟨(blkL d).det, (blkLinv d).det, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hinv : blkLinv d = (blkL d)⁻¹ := by
    calc blkLinv d = 1 * blkLinv d := (Matrix.one_mul _).symm
      _ = ((blkL d)⁻¹ * blkL d) * blkLinv d := by rw [Matrix.nonsing_inv_mul _ hdet]
      _ = (blkL d)⁻¹ * (blkL d * blkLinv d) := Matrix.mul_assoc _ _ _
      _ = (blkL d)⁻¹ * 1 := by rw [blkL_mul_blkLinv]
      _ = (blkL d)⁻¹ := Matrix.mul_one _
  rw [hinv, Matrix.nonsing_inv_mul _ hdet]

private lemma blkL_mulVec_x0 (d : Nat) (r : Fin (3 * Nat.log2 d)) :
    (∑ c : Fin (3 * Nat.log2 d), blkL d r c * blkX0 d c) + blkUvec d r = 0 := by
  let L := Nat.log2 d
  set jr := r.val / 3
  set rr := r.val % 3
  have hrj : r.val / 3 = jr := rfl
  have hrr' : r.val % 3 = rr := rfl
  have hrr : rr = 0 ∨ rr = 1 ∨ rr = 2 := by omega
  rcases hrr with hrr0 | hrr1 | hrr2
  · by_cases hj0 : jr = 0
    · have hsupp : ∀ c : Fin (3 * L), c ≠ r → blkL d r c * blkX0 d c = 0 := by
        intro c hc
        have hz : blkL d r c = 0 := by
          unfold blkL blkMat; rw [ite_eq_right]; unfold blkAdj
          simp only [hrj, hrr', hrr0, ↓reduceIte, dite_eq_left hj0, decide_eq_true_eq,
            Sum.inl.injEq, reduceCtorEq, or_false]
          exact hc
        rw [hz, zero_mul]
      rw [Finset.sum_eq_single r (fun c _ hc => hsupp c hc) (fun h => absurd (Finset.mem_univ r) h)]
      have hL1 : blkL d r r = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hj0, hrr0]
      have hU1 : blkUvec d r = 1 := by unfold blkUvec blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hj0, hrr0]
      have hX : blkX0 d r = -1 := by dsimp only [blkX0]; rw [hrj, hrr', hj0, hrr0]; rfl
      rw [hL1, hU1, hX]; ring
    · let prev : Fin (3 * L) := ⟨3 * jr - 1, by have := r.isLt; omega⟩
      have hprev_ne : prev ≠ r := by intro h; have := congrArg Fin.val h; dsimp only [prev] at this; omega
      have hsupp : ∀ c : Fin (3 * L), c ∉ ({r, prev} : Finset (Fin (3 * L))) →
          blkL d r c * blkX0 d c = 0 := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
        have hz : blkL d r c = 0 := by
          unfold blkL blkMat; rw [ite_eq_right]; unfold blkAdj
          simp only [hrj, hrr', hrr0, ↓reduceIte, dite_eq_right hj0, decide_eq_true_eq, Sum.inl.injEq]
          rintro (h1 | h2)
          · exact hc.1 h1
          · exact hc.2 (Fin.ext (congrArg Fin.val h2))
        rw [hz, zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ ({r, prev} : Finset (Fin (3 * L))))
        (fun c _ hc => hsupp c hc), Finset.sum_pair hprev_ne.symm]
      have hL1 : blkL d r r = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr0, hj0]
      have hL2 : blkL d r prev = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr0, hj0, prev]
      have hU0 : blkUvec d r = 0 := by unfold blkUvec blkMat; rw [ite_eq_right]; unfold blkAdj; simp [hrj, hrr', hrr0, hj0]
      have hXr : blkX0 d r = -((2 : ℤ) ^ jr) := by dsimp only [blkX0]; rw [hrj, hrr', hrr0]; simp
      have hXp : blkX0 d prev = (2 : ℤ) ^ jr := by
        dsimp only [blkX0]
        have hpj : prev.val / 3 = jr - 1 := by dsimp only [prev]; omega
        have hpr : prev.val % 3 = 2 := by dsimp only [prev]; omega
        rw [hpj, hpr, ite_eq_left rfl, Nat.sub_add_cancel (by omega)]
      rw [hL1, hL2, hU0, hXr, hXp]; ring
  · by_cases hj0 : jr = 0
    · have hsupp : ∀ c : Fin (3 * L), c ≠ r → blkL d r c * blkX0 d c = 0 := by
        intro c hc
        have hz : blkL d r c = 0 := by
          unfold blkL blkMat; rw [ite_eq_right]; unfold blkAdj
          simp only [hrj, hrr', hrr1, (by decide : (1 : Nat) ≠ 0), ↓reduceIte, dite_eq_left hj0,
            decide_eq_true_eq, Sum.inl.injEq, reduceCtorEq, or_false]
          exact hc
        rw [hz, zero_mul]
      rw [Finset.sum_eq_single r (fun c _ hc => hsupp c hc) (fun h => absurd (Finset.mem_univ r) h)]
      have hL1 : blkL d r r = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hj0, hrr1]
      have hU1 : blkUvec d r = 1 := by unfold blkUvec blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hj0, hrr1]
      have hX : blkX0 d r = -1 := by dsimp only [blkX0]; rw [hrj, hrr', hj0, hrr1]; rfl
      rw [hL1, hU1, hX]; ring
    · let prev : Fin (3 * L) := ⟨3 * jr - 1, by have := r.isLt; omega⟩
      have hprev_ne : prev ≠ r := by intro h; have := congrArg Fin.val h; dsimp only [prev] at this; omega
      have hsupp : ∀ c : Fin (3 * L), c ∉ ({r, prev} : Finset (Fin (3 * L))) →
          blkL d r c * blkX0 d c = 0 := by
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
        have hz : blkL d r c = 0 := by
          unfold blkL blkMat; rw [ite_eq_right]; unfold blkAdj
          simp only [hrj, hrr', hrr1, (by decide : (1 : Nat) ≠ 0), ↓reduceIte, dite_eq_right hj0,
            decide_eq_true_eq, Sum.inl.injEq]
          rintro (h1 | h2)
          · exact hc.1 h1
          · exact hc.2 (Fin.ext (congrArg Fin.val h2))
        rw [hz, zero_mul]
      rw [← Finset.sum_subset (Finset.subset_univ ({r, prev} : Finset (Fin (3 * L))))
        (fun c _ hc => hsupp c hc), Finset.sum_pair hprev_ne.symm]
      have hL1 : blkL d r r = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr1, hj0]
      have hL2 : blkL d r prev = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr1, hj0, prev]
      have hU0 : blkUvec d r = 0 := by unfold blkUvec blkMat; rw [ite_eq_right]; unfold blkAdj; simp [hrj, hrr', hrr1, hj0]
      have hXr : blkX0 d r = -((2 : ℤ) ^ jr) := by dsimp only [blkX0]; rw [hrj, hrr', hrr1]; simp
      have hXp : blkX0 d prev = (2 : ℤ) ^ jr := by
        dsimp only [blkX0]
        have hpj : prev.val / 3 = jr - 1 := by dsimp only [prev]; omega
        have hpr : prev.val % 3 = 2 := by dsimp only [prev]; omega
        rw [hpj, hpr, ite_eq_left rfl, Nat.sub_add_cancel (by omega)]
      rw [hL1, hL2, hU0, hXr, hXp]; ring
  · let t0 : Fin (3 * L) := ⟨3 * jr, by have := r.isLt; omega⟩
    let t1 : Fin (3 * L) := ⟨3 * jr + 1, by have := r.isLt; omega⟩
    have hne01 : t0 ≠ t1 := by intro h; have := congrArg Fin.val h; dsimp only [t0, t1] at this; omega
    have hne0r : t0 ≠ r := by intro h; have := congrArg Fin.val h; dsimp only [t0] at this; omega
    have hne1r : t1 ≠ r := by intro h; have := congrArg Fin.val h; dsimp only [t1] at this; omega
    have hsupp : ∀ c : Fin (3 * L), c ∉ ({t0, t1, r} : Finset (Fin (3 * L))) →
        blkL d r c * blkX0 d c = 0 := by
      intro c hc
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
      have hz : blkL d r c = 0 := by
        unfold blkL blkMat; rw [ite_eq_right]; unfold blkAdj
        simp only [hrj, hrr', hrr2, (by decide : (2 : Nat) ≠ 0), (by decide : (2 : Nat) ≠ 1), ↓reduceIte,
          decide_eq_true_eq, Sum.inl.injEq]
        rintro (h1 | h2 | h3)
        · exact hc.1 (Fin.ext (congrArg Fin.val h1))
        · exact hc.2.1 (Fin.ext (congrArg Fin.val h2))
        · exact hc.2.2 h3
      rw [hz, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ ({t0, t1, r} : Finset (Fin (3 * L))))
      (fun c _ hc => hsupp c hc), Finset.sum_insert (by simp [hne01, hne0r]), Finset.sum_pair hne1r]
    have hL0 : blkL d r t0 = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr2, t0]
    have hL1 : blkL d r t1 = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr2, t1]
    have hL2 : blkL d r r = 1 := by unfold blkL blkMat; rw [ite_eq_left]; unfold blkAdj; simp [hrj, hrr', hrr2]
    have hU0 : blkUvec d r = 0 := by unfold blkUvec blkMat; rw [ite_eq_right]; unfold blkAdj; simp [hrj, hrr', hrr2]
    have hX0 : blkX0 d t0 = -((2 : ℤ) ^ jr) := by
      dsimp only [blkX0]; have h1 : t0.val / 3 = jr := by dsimp only [t0]; omega
      have h2 : t0.val % 3 = 0 := by dsimp only [t0]; omega
      rw [h1, h2]; simp
    have hX1 : blkX0 d t1 = -((2 : ℤ) ^ jr) := by
      dsimp only [blkX0]; have h1 : t1.val / 3 = jr := by dsimp only [t1]; omega
      have h2 : t1.val % 3 = 1 := by dsimp only [t1]; omega
      rw [h1, h2]; simp
    have hX2 : blkX0 d r = (2 : ℤ) ^ (jr + 1) := by dsimp only [blkX0]; rw [ite_eq_left hrr2]
    rw [hL0, hL1, hL2, hU0, hX0, hX1, hX2, pow_succ]; ring

private lemma blkW_dot_x0 (d : Nat) (hd : 2 ≤ d) :
    blkB0 d + ∑ c : Fin (3 * Nat.log2 d), blkWvec d c * blkX0 d c = (d : ℤ) := by
  let L := Nat.log2 d
  have hlt : d < 2 ^ (L + 1) := (Nat.log2_lt (by omega : d ≠ 0)).mp (Nat.lt_succ_self (Nat.log2 d))
  have hbin := sum_testBit_two_pow (L + 1) d hlt
  rw [Fin.sum_univ_succ] at hbin
  simp only [Fin.val_zero, Fin.val_succ, pow_zero] at hbin
  have hb0 : blkB0 d = if d.testBit 0 = true then 1 else 0 := rfl
  have hsum_eq : (∑ c : Fin (3 * L), blkWvec d c * blkX0 d c) =
      ∑ j : Fin L, if d.testBit (j.val + 1) = true then (2 : ℤ) ^ (j.val + 1) else 0 := by
    let f : Fin L → Fin (3 * L) := fun j => ⟨3 * j.val + 2, by have := j.isLt; omega⟩
    have hfinj : Function.Injective f := fun j1 j2 h =>
      Fin.ext (by have := congrArg Fin.val h; dsimp only [f] at this; omega)
    have hsupp : ∀ c : Fin (3 * L), c ∉ Finset.univ.image f → blkWvec d c * blkX0 d c = 0 := by
      intro c hc
      have hne2 : c.val % 3 ≠ 2 := by
        intro h2
        apply hc
        refine Finset.mem_image.mpr ⟨⟨c.val / 3, by have := c.isLt; omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
        dsimp only [f]; omega
      have hz : blkWvec d c = 0 := by
        dsimp only [blkWvec, blkMat, blkAdj]; simp [hne2]
      rw [hz, zero_mul]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image f)) (fun c _ hc => hsupp c hc),
      Finset.sum_image (fun a _ b _ h => hfinj h)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hjdiv : (f j).val / 3 = j.val := by dsimp only [f]; omega
    have hjmod : (f j).val % 3 = 2 := by dsimp only [f]; omega
    simp only [blkWvec, blkMat, blkAdj, blkX0, hjdiv, hjmod, decide_true, Bool.true_and, ↓reduceIte]
    split_ifs <;> ring
  rw [hb0, hsum_eq, hbin]

private def blkDiag (d : Nat) : Matrix (BlkIdx (Nat.log2 d)) (BlkIdx (Nat.log2 d)) ℤ :=
  Matrix.diagonal (Sum.elim (fun _ => (1 : ℤ)) (fun _ => (d : ℤ)))

private def blkWLinv (d : Nat) : Fin (3 * Nat.log2 d) → ℤ :=
  fun c => ∑ r : Fin (3 * Nat.log2 d), blkWvec d r * blkLinv d r c

private def blkULeft (d : Nat) : Matrix (BlkIdx (Nat.log2 d)) (BlkIdx (Nat.log2 d)) ℤ :=
  fun r c =>
    match r, c with
    | Sum.inl rv, Sum.inl cv => if rv = cv then 1 else 0
    | Sum.inl _, Sum.inr () => 0
    | Sum.inr (), Sum.inl cv => blkWLinv d cv
    | Sum.inr (), Sum.inr () => 1

private def blkULeftInv (d : Nat) : Matrix (BlkIdx (Nat.log2 d)) (BlkIdx (Nat.log2 d)) ℤ :=
  fun r c =>
    match r, c with
    | Sum.inl rv, Sum.inl cv => if rv = cv then 1 else 0
    | Sum.inl _, Sum.inr () => 0
    | Sum.inr (), Sum.inl cv => -(blkWLinv d cv)
    | Sum.inr (), Sum.inr () => 1

private def blkVRight (d : Nat) : Matrix (BlkIdx (Nat.log2 d)) (BlkIdx (Nat.log2 d)) ℤ :=
  fun r c =>
    match r, c with
    | Sum.inl rv, Sum.inl cv => blkL d rv cv
    | Sum.inl rv, Sum.inr () => blkUvec d rv
    | Sum.inr (), Sum.inl _ => 0
    | Sum.inr (), Sum.inr () => 1

private def blkVRightInv (d : Nat) : Matrix (BlkIdx (Nat.log2 d)) (BlkIdx (Nat.log2 d)) ℤ :=
  fun r c =>
    match r, c with
    | Sum.inl rv, Sum.inl cv => blkLinv d rv cv
    | Sum.inl rv, Sum.inr () => blkX0 d rv
    | Sum.inr (), Sum.inl _ => 0
    | Sum.inr (), Sum.inr () => 1

private lemma blkULeftInv_mul_blkULeft (d : Nat) : blkULeftInv d * blkULeft d = 1 := by
  ext r c
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  cases r with
  | inl rv =>
    cases c with
    | inl cv =>
      simp only [blkULeftInv, blkULeft, Fintype.sum_unique, mul_zero, add_zero, Sum.inl.injEq]
      rw [Finset.sum_eq_single rv]
      · simp
      · intro t _ ht; simp [ht.symm]
      · intro h; exact absurd (Finset.mem_univ rv) h
    | inr u =>
      cases u
      simp [blkULeftInv, blkULeft]
  | inr u =>
    cases u
    cases c with
    | inl cv =>
      simp only [blkULeftInv, blkULeft, Fintype.sum_unique, one_mul, reduceCtorEq, ↓reduceIte]
      rw [Finset.sum_eq_single cv]
      · simp
      · intro t _ ht; simp [ht]
      · intro h; exact absurd (Finset.mem_univ cv) h
    | inr u' =>
      cases u'
      simp [blkULeftInv, blkULeft]

private lemma blkVRight_mul_blkVRightInv (d : Nat) : blkVRight d * blkVRightInv d = 1 := by
  ext r c
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  cases r with
  | inl rv =>
    cases c with
    | inl cv =>
      simp only [blkVRight, blkVRightInv, Fintype.sum_unique, mul_zero, add_zero, Sum.inl.injEq]
      have h := congrFun (congrFun (blkL_mul_blkLinv d) rv) cv
      simpa [Matrix.mul_apply, Matrix.one_apply] using h
    | inr u =>
      cases u
      simp only [blkVRight, blkVRightInv, Fintype.sum_unique, mul_one, reduceCtorEq, ↓reduceIte]
      exact blkL_mulVec_x0 d rv
  | inr u =>
    cases u
    cases c with
    | inl cv => simp [blkVRight, blkVRightInv]
    | inr u' => cases u'; simp [blkVRight, blkVRightInv]

private lemma blk_factor (d : Nat) (hd : 2 ≤ d) :
    blkULeft d * blkDiag d * blkVRight d = blkMat d := by
  ext r c
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]
  cases r with
  | inl rv =>
    have hsum1 : ∑ x : Fin (3 * Nat.log2 d),
        blkULeft d (Sum.inl rv) (Sum.inl x) * (blkDiag d * blkVRight d) (Sum.inl x) c =
        (blkDiag d * blkVRight d) (Sum.inl rv) c := by
      rw [Finset.sum_eq_single rv]
      · simp [blkULeft]
      · intro x _ hx; simp [blkULeft, hx.symm]
      · intro h; exact absurd (Finset.mem_univ rv) h
    rw [hsum1]
    simp only [blkULeft, Fintype.sum_unique, zero_mul, add_zero]
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    have hdiag : ∑ x : Fin (3 * Nat.log2 d),
        blkDiag d (Sum.inl rv) (Sum.inl x) * blkVRight d (Sum.inl x) c =
        blkVRight d (Sum.inl rv) c := by
      rw [Finset.sum_eq_single rv]
      · simp [blkDiag]
      · intro x _ hx; simp [blkDiag, hx.symm]
      · intro h; exact absurd (Finset.mem_univ rv) h
    rw [hdiag]
    simp only [blkDiag, Matrix.diagonal_apply_ne _ (by simp : Sum.inl rv ≠ Sum.inr ()),
      Fintype.sum_unique, zero_mul, add_zero]
    cases c with
    | inl cv => rfl
    | inr u => cases u; rfl
  | inr u =>
    cases u
    simp only [blkULeft, Fintype.sum_unique, one_mul]
    have hDVR_inl : ∀ x : Fin (3 * Nat.log2 d),
        (blkDiag d * blkVRight d) (Sum.inl x) c = blkVRight d (Sum.inl x) c := by
      intro x
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      rw [Finset.sum_eq_single x]
      · simp [blkDiag]
      · intro t _ ht; simp [blkDiag, ht.symm]
      · intro h; exact absurd (Finset.mem_univ x) h
    have hDVR_inr : (blkDiag d * blkVRight d) (Sum.inr ()) c = (d : ℤ) * blkVRight d (Sum.inr ()) c := by
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      have hz : ∑ x : Fin (3 * Nat.log2 d),
          blkDiag d (Sum.inr ()) (Sum.inl x) * blkVRight d (Sum.inl x) c = 0 := by
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [blkDiag]
      rw [hz, zero_add, Fintype.sum_unique]
      simp [blkDiag]
    simp_rw [hDVR_inl, hDVR_inr]
    cases c with
    | inl cv =>
      simp only [blkVRight, mul_zero, add_zero]
      have hcalc : ∑ x : Fin (3 * Nat.log2 d), blkWLinv d x * blkL d x cv = blkWvec d cv := by
        simp_rw [blkWLinv, Finset.sum_mul]
        rw [Finset.sum_comm]
        have hinner : ∀ t : Fin (3 * Nat.log2 d),
            ∑ x : Fin (3 * Nat.log2 d), blkWvec d t * blkLinv d t x * blkL d x cv =
              blkWvec d t * (if t = cv then 1 else 0) := by
          intro t
          have hmul : ∀ x, blkWvec d t * blkLinv d t x * blkL d x cv =
              blkWvec d t * (blkLinv d t x * blkL d x cv) := fun _ => mul_assoc _ _ _
          simp_rw [hmul, ← Finset.mul_sum]
          have h1 := congrFun (congrFun (blkLinv_mul_blkL d) t) cv
          rw [Matrix.mul_apply, Matrix.one_apply] at h1
          rw [h1]
        simp_rw [hinner]
        rw [Finset.sum_eq_single cv]
        · simp
        · intro t _ ht; simp [ht]
        · intro h; exact absurd (Finset.mem_univ cv) h
      exact hcalc
    | inr u' =>
      cases u'
      simp only [blkVRight, mul_one]
      have hwu : ∑ x : Fin (3 * Nat.log2 d), blkWLinv d x * blkUvec d x =
          -(∑ t : Fin (3 * Nat.log2 d), blkWvec d t * blkX0 d t) := by
        have hu_eq : ∀ x : Fin (3 * Nat.log2 d),
            blkUvec d x = -(∑ c' : Fin (3 * Nat.log2 d), blkL d x c' * blkX0 d c') := by
          intro x; have := blkL_mulVec_x0 d x; linarith
        simp_rw [hu_eq, mul_neg, Finset.sum_neg_distrib]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c' _ => ?_
        have hstep : ∑ x : Fin (3 * Nat.log2 d), blkWLinv d x * (blkL d x c' * blkX0 d c') =
            (∑ x : Fin (3 * Nat.log2 d), blkWLinv d x * blkL d x c') * blkX0 d c' := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm
        rw [hstep]
        congr 1
        simp_rw [blkWLinv, Finset.sum_mul]
        rw [Finset.sum_comm]
        have hinner : ∀ t : Fin (3 * Nat.log2 d),
            ∑ x : Fin (3 * Nat.log2 d), blkWvec d t * blkLinv d t x * blkL d x c' =
              blkWvec d t * (if t = c' then 1 else 0) := by
          intro t
          have hmul : ∀ x, blkWvec d t * blkLinv d t x * blkL d x c' =
              blkWvec d t * (blkLinv d t x * blkL d x c') := fun _ => mul_assoc _ _ _
          simp_rw [hmul, ← Finset.mul_sum]
          have h1 := congrFun (congrFun (blkLinv_mul_blkL d) t) c'
          rw [Matrix.mul_apply, Matrix.one_apply] at h1
          rw [h1]
        simp_rw [hinner]
        rw [Finset.sum_eq_single c']
        · simp
        · intro t _ ht; simp [ht]
        · intro h; exact absurd (Finset.mem_univ c') h
      rw [hwu]
      have hdot := blkW_dot_x0 d hd
      change -(∑ t, blkWvec d t * blkX0 d t) + (d : ℤ) = blkB0 d
      linarith

private lemma blkAdj_ones_le (d : Nat) :
    ((Finset.univ : Finset (BlkIdx (Nat.log2 d))).sum fun r =>
      ((Finset.univ : Finset (BlkIdx (Nat.log2 d))).filter (fun c => blkAdj d r c = true)).card) ≤
    3 + 10 * Nat.log2 d := by
  let L := Nat.log2 d
  rw [Fintype.sum_sum_type]
  have hu : (∑ u : Unit, ((Finset.univ : Finset (BlkIdx L)).filter (fun c => blkAdj d (Sum.inr u) c = true)).card) =
      ((Finset.univ : Finset (BlkIdx L)).filter (fun c => blkAdj d (Sum.inr ()) c = true)).card :=
    Fintype.sum_unique _
  rw [hu]
  have hrow_inl : ∀ rv : Fin (3 * L),
      ((Finset.univ : Finset (BlkIdx L)).filter (fun c => blkAdj d (Sum.inl rv) c = true)).card ≤ 3 := by
    intro rv
    let j := rv.val / 3
    let prevCol : BlkIdx L :=
      if hj : j = 0 then Sum.inr () else Sum.inl ⟨3 * j - 1, by have := rv.isLt; omega⟩
    have hrr : rv.val % 3 = 0 ∨ rv.val % 3 = 1 ∨ rv.val % 3 = 2 := by omega
    rcases hrr with h0 | h1 | h2
    · have hsub : (Finset.univ.filter (fun c => blkAdj d (Sum.inl rv) c = true)) ⊆
          ({Sum.inl rv, prevCol} : Finset (BlkIdx L)) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blkAdj, h0, ↓reduceIte,
          decide_eq_true_eq] at hc
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hc
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two.trans (by omega))
    · have hsub : (Finset.univ.filter (fun c => blkAdj d (Sum.inl rv) c = true)) ⊆
          ({Sum.inl rv, prevCol} : Finset (BlkIdx L)) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blkAdj, h1,
          (by decide : (1 : Nat) ≠ 0), ↓reduceIte, decide_eq_true_eq] at hc
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hc
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two.trans (by omega))
    · let t0 : BlkIdx L := Sum.inl ⟨3 * j, by have := rv.isLt; omega⟩
      let t1 : BlkIdx L := Sum.inl ⟨3 * j + 1, by have := rv.isLt; omega⟩
      have hsub : (Finset.univ.filter (fun c => blkAdj d (Sum.inl rv) c = true)) ⊆
          ({t0, t1, Sum.inl rv} : Finset (BlkIdx L)) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, blkAdj, h2,
          (by decide : (2 : Nat) ≠ 0), (by decide : (2 : Nat) ≠ 1), ↓reduceIte,
          decide_eq_true_eq] at hc
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact hc
      exact (Finset.card_le_card hsub).trans (Finset.card_le_three)
  have hsum_inl : (∑ rv : Fin (3 * L),
      ((Finset.univ : Finset (BlkIdx L)).filter (fun c => blkAdj d (Sum.inl rv) c = true)).card) ≤
      9 * L := by
    calc
      _ ≤ ∑ _rv : Fin (3 * L), 3 := Finset.sum_le_sum fun rv _ => hrow_inl rv
      _ = 9 * L := by simp [Finset.sum_const, mul_comm]; ring
  have hrow_inr : ((Finset.univ : Finset (BlkIdx L)).filter
      (fun c => blkAdj d (Sum.inr ()) c = true)).card ≤ L + 1 := by
    let S : Finset (BlkIdx L) :=
      insert (Sum.inr ()) (Finset.univ.image (fun j : Fin L =>
        Sum.inl ⟨3 * j.val + 2, by have := j.isLt; omega⟩))
    have hsub : (Finset.univ.filter (fun c => blkAdj d (Sum.inr ()) c = true)) ⊆ S := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
      cases c with
      | inr u => cases u; exact Finset.mem_insert_self _ _
      | inl cv =>
        simp only [blkAdj, Bool.and_eq_true, decide_eq_true_eq] at hc
        refine Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨⟨cv.val / 3, by have := cv.isLt; omega⟩, Finset.mem_univ _, ?_⟩)
        congr 1; apply Fin.ext; dsimp only; omega
    calc
      _ ≤ S.card := Finset.card_le_card hsub
      _ ≤ (Finset.univ.image (fun j : Fin L =>
            (Sum.inl ⟨3 * j.val + 2, by have := j.isLt; omega⟩ : BlkIdx L))).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (Finset.univ : Finset (Fin L)).card + 1 := Nat.add_le_add_right Finset.card_image_le 1
      _ = L + 1 := by simp
  exact (Nat.add_le_add hsum_inl hrow_inr).trans (by omega)

/-! ### Part 3: Full block-diagonal assembly + rank-`(n+1)` factorization of `raw` -/

private lemma card_mul_image_zmod (M d : Nat) [NeZero M] :
    ((Finset.univ : Finset (ZMod M)).image (fun y : ZMod M => y * (d : ZMod M))).card =
      M / Nat.gcd M d := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  set g := Nat.gcd M d
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d hM
  have hgM : g ∣ M := Nat.gcd_dvd_left M d
  have hgd : g ∣ d := Nat.gcd_dvd_right M d
  set img := (Finset.univ : Finset (ZMod M)).image (fun y : ZMod M => y * (d : ZMod M))
  have hmem : ∀ z : ZMod M, z ∈ img ↔ g ∣ z.val := by
    intro z
    constructor
    · intro hz
      rcases Finset.mem_image.mp hz with ⟨y, _, rfl⟩
      have hval : (y * (d : ZMod M)).val = (y.val * d) % M := by
        rw [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod_mod]
      rw [hval]
      exact (Nat.dvd_mod_iff hgM).mpr (dvd_mul_of_dvd_right hgd y.val)
    · intro hgz
      rcases hgz with ⟨t, ht⟩
      have hbez : (g : ℤ) = (M : ℤ) * Nat.gcdA M d + (d : ℤ) * Nat.gcdB M d := Nat.gcd_eq_gcd_ab M d
      have hbezM : (g : ZMod M) = (Nat.gcdB M d : ZMod M) * (d : ZMod M) := by
        have hcast := congrArg (Int.cast : ℤ → ZMod M) hbez
        push_cast at hcast
        rw [ZMod.natCast_self, zero_mul, zero_add, mul_comm] at hcast
        exact hcast
      refine Finset.mem_image.mpr ⟨(t : ZMod M) * (Nat.gcdB M d : ZMod M), Finset.mem_univ _, ?_⟩
      calc
        ((t : ZMod M) * (Nat.gcdB M d : ZMod M)) * (d : ZMod M)
            = (t : ZMod M) * ((Nat.gcdB M d : ZMod M) * (d : ZMod M)) := mul_assoc _ _ _
        _ = (t : ZMod M) * (g : ZMod M) := by rw [← hbezM]
        _ = ((g * t : Nat) : ZMod M) := by push_cast; ring
        _ = ((z.val : Nat) : ZMod M) := by rw [← ht]
        _ = z := ZMod.natCast_zmod_val z
  have hbij : img.card = (Finset.univ : Finset (Fin (M / g))).card := by
    symm
    refine Finset.card_bij (fun t _ => ((g * t.val : Nat) : ZMod M)) ?_ ?_ ?_
    · intro t _
      rw [hmem]
      have hlt : g * t.val < M := by
        calc g * t.val < g * (M / g) := Nat.mul_lt_mul_of_pos_left t.isLt hg_pos
        _ = M := Nat.mul_div_cancel' hgM
      rw [ZMod.val_natCast_of_lt hlt]
      exact dvd_mul_right g t.val
    · intro t1 _ t2 _ heq
      have hlt1 : g * t1.val < M := by
        calc g * t1.val < g * (M / g) := Nat.mul_lt_mul_of_pos_left t1.isLt hg_pos
        _ = M := Nat.mul_div_cancel' hgM
      have hlt2 : g * t2.val < M := by
        calc g * t2.val < g * (M / g) := Nat.mul_lt_mul_of_pos_left t2.isLt hg_pos
        _ = M := Nat.mul_div_cancel' hgM
      have hval := congrArg ZMod.val heq
      rw [ZMod.val_natCast_of_lt hlt1, ZMod.val_natCast_of_lt hlt2] at hval
      exact Fin.ext (Nat.eq_of_mul_eq_mul_left hg_pos hval)
    · intro z hz
      rcases (hmem z).mp hz with ⟨t, ht⟩
      have ht_lt : t < M / g := by
        have hzlt : z.val < M := z.val_lt
        rw [ht] at hzlt
        have hmul : g * (M / g) = M := Nat.mul_div_cancel' hgM
        rw [← hmul] at hzlt
        exact Nat.lt_of_mul_lt_mul_left hzlt
      refine ⟨⟨t, ht_lt⟩, Finset.mem_univ _, ?_⟩
      dsimp only; rw [← ht, ZMod.natCast_zmod_val]
  rw [hbij, Finset.card_univ, Fintype.card_fin]

private lemma image_combine_card {n k h base : Nat}
    (d : Fin h → Nat)
    (raw : Matrix (Finset (Fin n)) (Finset (Fin n)) ℤ)
    (A : Matrix (Finset (Fin n)) (Fin (k + 1) ⊕ Fin h) ℤ)
    (B : Matrix (Fin (k + 1) ⊕ Fin h) (Finset (Fin n)) ℤ)
    (U : Matrix (Fin (k + 1) ⊕ Fin h) (Finset (Fin n)) ℤ)
    (V : Matrix (Finset (Fin n)) (Fin (k + 1) ⊕ Fin h) ℤ)
    (hfac : A * Matrix.diagonal (Sum.elim (fun _ : Fin (k + 1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ))) * B = raw)
    (hUA : U * A = 1) (hBV : B * V = 1) :
    let Mask := Finset (Fin n)
    let M := base + 2
    let combine := fun (f : Mask → ZMod (base + 2)) (b : Mask) =>
      (Finset.univ : Finset Mask).sum (fun a => f a * (raw a b : ZMod (base + 2)))
    ((Finset.univ : Finset (Mask → ZMod (base + 2))).image combine).card =
      M ^ (k + 1) * (Finset.univ : Finset (Fin h)).prod (fun i => M / Nat.gcd M (d i)) := by
  classical
  intro Mask M combine
  haveI : NeZero M := ⟨by dsimp [M]; omega⟩
  let D := Fin (k + 1) ⊕ Fin h
  let φ : ℤ →+* ZMod M := Int.castRingHom (ZMod M)
  let AM : Matrix Mask D (ZMod M) := A.map φ
  let BM : Matrix D Mask (ZMod M) := B.map φ
  let UM : Matrix D Mask (ZMod M) := U.map φ
  let VM : Matrix Mask D (ZMod M) := V.map φ
  let rawM : Matrix Mask Mask (ZMod M) := raw.map φ
  let diagVec : D → ℤ := Sum.elim (fun _ : Fin (k + 1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ))
  let diagM : Matrix D D (ZMod M) := (Matrix.diagonal diagVec).map φ
  have hfacM : AM * diagM * BM = rawM := by
    have h1 := congrArg (Matrix.map · φ) hfac
    simpa [AM, BM, diagM, rawM, Matrix.map_mul] using h1
  have hUAM : UM * AM = 1 := by
    have h1 := congrArg (Matrix.map · φ) hUA
    simpa [UM, AM, Matrix.map_mul, Matrix.map_one] using h1
  have hBVM : BM * VM = 1 := by
    have h1 := congrArg (Matrix.map · φ) hBV
    simpa [BM, VM, Matrix.map_mul, Matrix.map_one] using h1
  have hcomb_eq : ∀ f : Mask → ZMod M, combine f = Matrix.vecMul (Matrix.vecMul (Matrix.vecMul f AM) diagM) BM := by
    intro f
    rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hfacM]
    funext b; simp [combine, Matrix.vecMul, dotProduct, rawM, φ]
  let S : Finset (D → ZMod M) := Finset.univ.image (fun g : D → ZMod M => Matrix.vecMul g diagM)
  have himg_eq : (Finset.univ : Finset (Mask → ZMod M)).image combine =
      S.image (fun w => Matrix.vecMul w BM) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_univ, true_and, S]
    constructor
    · rintro ⟨f, rfl⟩
      exact ⟨Matrix.vecMul (Matrix.vecMul f AM) diagM, ⟨Matrix.vecMul f AM, rfl⟩, (hcomb_eq f).symm⟩
    · rintro ⟨w, ⟨g, rfl⟩, rfl⟩
      refine ⟨Matrix.vecMul g UM, ?_⟩
      have h1 : Matrix.vecMul (Matrix.vecMul g UM) AM = g := by
        rw [Matrix.vecMul_vecMul, hUAM, Matrix.vecMul_one]
      rw [hcomb_eq, h1]
  have hBM_inj : Function.Injective (fun w : D → ZMod M => Matrix.vecMul w BM) := by
    intro w1 w2 h
    have h1 := congrArg (fun v => Matrix.vecMul v VM) h
    simp only [Matrix.vecMul_vecMul, hBVM, Matrix.vecMul_one] at h1
    exact h1
  rw [himg_eq, Finset.card_image_of_injective _ hBM_inj]
  have hdiag_apply : ∀ (g : D → ZMod M) (x : D), Matrix.vecMul g diagM x = g x * (diagVec x : ZMod M) := by
    intro g x
    simp only [Matrix.vecMul, dotProduct, diagM, Matrix.map_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single x]
    · simp [φ]
    · intro t _ ht; simp [ht]
    · intro h; exact absurd (Finset.mem_univ x) h
  let coordImg : D → Finset (ZMod M) := fun x =>
    (Finset.univ : Finset (ZMod M)).image (fun y => y * (diagVec x : ZMod M))
  have hS_pi : S = Fintype.piFinset coordImg := by
    ext w
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and, Fintype.mem_piFinset, coordImg]
    constructor
    · rintro ⟨g, rfl⟩ x
      exact ⟨g x, (hdiag_apply g x).symm⟩
    · intro hw
      choose g hg using hw
      refine ⟨g, funext fun x => ?_⟩
      rw [hdiag_apply g x, hg x]
  rw [hS_pi, Fintype.card_piFinset, Fintype.prod_sum_type]
  have hleft : (∏ _j : Fin (k + 1), (coordImg (Sum.inl _j)).card) = M ^ (k + 1) := by
    have heach : ∀ j : Fin (k + 1), (coordImg (Sum.inl j)).card = M := by
      intro j
      have heq : coordImg (Sum.inl j) = Finset.univ := by
        ext z; simp only [coordImg, diagVec, Sum.elim_inl, Int.cast_one, mul_one,
          Finset.mem_image, Finset.mem_univ, true_and, iff_true]
        exact ⟨z, rfl⟩
      rw [heq, Finset.card_univ, ZMod.card]
    simp_rw [heach]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hright : (∏ i : Fin h, (coordImg (Sum.inr i)).card) =
      ∏ i : Fin h, M / Nat.gcd M (d i) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have hci : coordImg (Sum.inr i) =
        (Finset.univ : Finset (ZMod M)).image (fun y : ZMod M => y * (d i : ZMod M)) := by
      ext z; simp [coordImg, diagVec]
    rw [hci]
    exact card_mul_image_zmod M (d i)
  rw [hleft, hright]

private lemma main_construction (h : Nat) (d : Fin h → Nat) (hd : ∀ i, 2 ≤ d i) :
    ∃ k : Nat,
      let n := k + h
      let Mask := Finset (Fin n)
      let D := Fin (k + 1) ⊕ Fin h
      ∃ C : Fin n → Finset (Fin n),
        n ≤ (Finset.univ : Finset (Fin h)).sum (fun i => 2 + 4 * Nat.log2 (d i)) ∧
        (Finset.univ : Finset (Fin n)).sum (fun i => (C i).card) ≤
          (Finset.univ : Finset (Fin h)).sum (fun i => 3 + 10 * Nat.log2 (d i)) ∧
        let raw : Matrix Mask Mask ℤ := fun a b =>
          ((1 + a.card + b.card + ((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)).card : Nat) : ℤ)
        let diagonal : Matrix D D ℤ := Matrix.diagonal
          (Sum.elim (fun _ : Fin (k + 1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ)))
        (∃ (A : Matrix Mask D ℤ) (B : Matrix D Mask ℤ)
          (U : Matrix D Mask ℤ) (V : Matrix Mask D ℤ),
          A * diagonal * B = raw ∧ U * A = 1 ∧ B * V = 1) := by
  classical
  let k : Nat := ∑ i : Fin h, 3 * Nat.log2 (d i)
  refine ⟨k, ?_⟩
  let n := k + h
  let Mask := Finset (Fin n)
  let D := Fin (k + 1) ⊕ Fin h
  let Aux := Σ i : Fin h, Fin (3 * Nat.log2 (d i))
  have hAux_card : Fintype.card Aux = k := by
    simp [Aux, k, Fintype.card_sigma, Fintype.card_fin]
  let eAux : Aux ≃ Fin k := Fintype.equivFinOfCardEq hAux_card
  let NIdx := Aux ⊕ Fin h
  let eN : NIdx ≃ Fin n := (eAux.sumCongr (Equiv.refl (Fin h))).trans finSumFinEquiv
  let MIdx := Unit ⊕ NIdx
  let eK1 : Unit ⊕ Fin k ≃ Fin (k + 1) :=
    { toFun := Sum.elim (fun _ => 0) Fin.succ
      invFun := fun x => if hx : x = 0 then Sum.inl () else Sum.inr (x.pred hx)
      left_inv := by
        rintro (u | x)
        · cases u; simp
        · simp [Fin.succ_ne_zero]
      right_inv := by
        intro x
        by_cases hx : x = 0
        · subst hx; simp
        · simp [hx] }
  let eD : MIdx ≃ D :=
    { toFun := fun x => match x with
        | Sum.inl () => Sum.inl (eK1 (Sum.inl ()))
        | Sum.inr (Sum.inl a) => Sum.inl (eK1 (Sum.inr (eAux a)))
        | Sum.inr (Sum.inr i) => Sum.inr i
      invFun := fun y => match y with
        | Sum.inl j => match eK1.symm j with
            | Sum.inl () => Sum.inl ()
            | Sum.inr t => Sum.inr (Sum.inl (eAux.symm t))
        | Sum.inr i => Sum.inr (Sum.inr i)
      left_inv := by
        rintro (u | (a | i))
        · cases u; simp
        · simp
        · simp
      right_inv := by
        rintro (j | i)
        · dsimp only
          cases hkj : eK1.symm j with
          | inl u => cases u; dsimp only; rw [← hkj, Equiv.apply_symm_apply]
          | inr t => dsimp only; rw [Equiv.apply_symm_apply, ← hkj, Equiv.apply_symm_apply]
        · rfl }
  -- Map NIdx ↔ Σ i : Fin h, BlkIdx (Nat.log2 (d i))
  let BSum := Σ i : Fin h, BlkIdx (Nat.log2 (d i))
  let eB : NIdx ≃ BSum :=
    { toFun := fun x => match x with
        | Sum.inl ⟨i, rv⟩ => ⟨i, Sum.inl rv⟩
        | Sum.inr i => ⟨i, Sum.inr ()⟩
      invFun := fun y => match y with
        | ⟨i, Sum.inl rv⟩ => Sum.inl ⟨i, rv⟩
        | ⟨i, Sum.inr ()⟩ => Sum.inr i
      left_inv := by rintro (⟨i, rv⟩ | i) <;> rfl
      right_inv := by rintro ⟨i, rv | u⟩ <;> [rfl; (cases u; rfl)] }
  -- Define block-diagonal adjacency on BSum, hence C on Fin n
  let adjB : BSum → BSum → Bool := fun x y =>
    if hEq : x.1 = y.1 then blkAdj (d x.1) x.2 (hEq ▸ y.2) else false
  let C : Fin n → Finset (Fin n) := fun u =>
    Finset.univ.filter (fun v => adjB (eB (eN.symm u)) (eB (eN.symm v)) = true)
  have hn_le : n ≤ ∑ i : Fin h, (2 + 4 * Nat.log2 (d i)) := by
    have hsum : n = ∑ i : Fin h, (3 * Nat.log2 (d i) + 1) := by
      dsimp only [n, k]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
    rw [hsum]
    refine Finset.sum_le_sum fun i _ => by omega
  have hC_le : ∑ u : Fin n, (C u).card ≤ ∑ i : Fin h, (3 + 10 * Nat.log2 (d i)) := by
    have hrew1 : ∑ u : Fin n, (C u).card =
        ∑ x : BSum, ((Finset.univ : Finset BSum).filter (fun y => adjB x y = true)).card := by
      let eNB : Fin n ≃ BSum := eN.symm.trans eB
      rw [← Equiv.sum_comp eNB (fun x => ((Finset.univ : Finset BSum).filter (fun y => adjB x y = true)).card)]
      refine Finset.sum_congr rfl fun u _ => ?_
      dsimp only [C, eNB, Equiv.trans_apply]
      refine Finset.card_bij (fun v _ => eB (eN.symm v)) ?_ ?_ ?_
      · intro v hv; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
      · intro v1 _ v2 _ heq; exact eN.symm.injective (eB.injective heq)
      · intro y hy; refine ⟨eN (eB.symm y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hy).2⟩, by simp⟩
    rw [hrew1, Fintype.sum_sigma]
    refine Finset.sum_le_sum fun i _ => ?_
    have hblk_eq : ∑ r : BlkIdx (Nat.log2 (d i)),
        ((Finset.univ : Finset BSum).filter (fun y => adjB ⟨i, r⟩ y = true)).card =
        ∑ r : BlkIdx (Nat.log2 (d i)),
        ((Finset.univ : Finset (BlkIdx (Nat.log2 (d i)))).filter (fun c => blkAdj (d i) r c = true)).card := by
      refine Finset.sum_congr rfl fun r _ => ?_
      refine Finset.card_bij (fun y hy => ?_) ?_ ?_ ?_
      · have hmem := (Finset.mem_filter.mp hy).2
        have hi : i = y.1 := by
          dsimp only [adjB] at hmem; split_ifs at hmem with hEq; exact hEq
        exact hi ▸ y.2
      · intro y hy
        have hmem := (Finset.mem_filter.mp hy).2
        dsimp only [adjB] at hmem
        split_ifs at hmem with hEq
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      · intro y1 hy1 y2 hy2 heq
        have h1 := (Finset.mem_filter.mp hy1).2
        have h2 := (Finset.mem_filter.mp hy2).2
        dsimp only [adjB] at h1 h2
        split_ifs at h1 with hi1
        split_ifs at h2 with hi2
        cases y1 with | mk i1 c1 =>
        cases y2 with | mk i2 c2 =>
        dsimp only at hi1 hi2 heq
        subst hi1; subst hi2; exact congrArg (Sigma.mk i) heq
      · intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
        refine ⟨⟨i, c⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [adjB, hc]⟩, rfl⟩
    rw [hblk_eq]
    exact blkAdj_ones_le (d i)
  -- Block-diagonal matrices on BSum (factoring -E_B)
  let EB : Matrix BSum BSum ℤ := fun x y => if adjB x y = true then 1 else 0
  let diagB : Matrix BSum BSum ℤ := Matrix.diagonal (fun x : BSum =>
    match x.2 with | Sum.inl _ => (1 : ℤ) | Sum.inr () => (d x.1 : ℤ))
  let ULB : Matrix BSum BSum ℤ := fun x y =>
    if hEq : x.1 = y.1 then -(blkULeft (d x.1) x.2 (hEq ▸ y.2)) else 0
  let ULBInv : Matrix BSum BSum ℤ := fun x y =>
    if hEq : x.1 = y.1 then -(blkULeftInv (d x.1) x.2 (hEq ▸ y.2)) else 0
  let VRB : Matrix BSum BSum ℤ := fun x y =>
    if hEq : x.1 = y.1 then blkVRight (d x.1) x.2 (hEq ▸ y.2) else 0
  let VRBInv : Matrix BSum BSum ℤ := fun x y =>
    if hEq : x.1 = y.1 then blkVRightInv (d x.1) x.2 (hEq ▸ y.2) else 0
  have hULB_inv : ULBInv * ULB = 1 := by
    ext ⟨i, r⟩ ⟨j, c⟩
    rw [Matrix.mul_apply, Fintype.sum_sigma, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single i]
      · simp only [ULBInv, ULB, ↓reduceDIte, neg_mul_neg]
        have h1 := congrFun (congrFun (blkULeftInv_mul_blkULeft (d i)) r) c
        rw [Matrix.mul_apply, Matrix.one_apply] at h1
        rw [h1]
        by_cases hrc : r = c <;> simp [hrc]
      · intro t _ ht; refine Finset.sum_eq_zero fun s _ => by simp [ULBInv, ht.symm]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [ite_eq_right (by intro h; exact hij (congrArg Sigma.fst h))]
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ => ?_
      by_cases hit : i = t
      · subst hit; simp [ULB, hij]
      · simp [ULBInv, hit]
  have hVRB_inv : VRB * VRBInv = 1 := by
    ext ⟨i, r⟩ ⟨j, c⟩
    rw [Matrix.mul_apply, Fintype.sum_sigma, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      rw [Finset.sum_eq_single i]
      · simp only [VRB, VRBInv, ↓reduceDIte]
        have h1 := congrFun (congrFun (blkVRight_mul_blkVRightInv (d i)) r) c
        rw [Matrix.mul_apply, Matrix.one_apply] at h1
        rw [h1]
        by_cases hrc : r = c <;> simp [hrc]
      · intro t _ ht; refine Finset.sum_eq_zero fun s _ => by simp [VRB, ht.symm]
      · intro h; exact absurd (Finset.mem_univ i) h
    · rw [ite_eq_right (by intro h; exact hij (congrArg Sigma.fst h))]
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ => ?_
      by_cases hit : i = t
      · subst hit; simp [VRBInv, hij]
      · simp [VRB, hit]
  have hB_fac : ULB * diagB * VRB = -EB := by
    ext ⟨i, r⟩ ⟨j, c⟩
    rw [Matrix.mul_apply, Matrix.neg_apply, Fintype.sum_sigma]
    by_cases hij : i = j
    · subst hij
      have hterm_zero : ∀ t : Fin h, t ≠ i →
          ∑ s : BlkIdx (Nat.log2 (d t)), (ULB * diagB) ⟨i, r⟩ ⟨t, s⟩ * VRB ⟨t, s⟩ ⟨i, c⟩ = 0 := by
        intro t ht; refine Finset.sum_eq_zero fun s _ => by simp [VRB, ht]
      rw [Finset.sum_eq_single i (fun t _ ht => hterm_zero t ht) (fun h => absurd (Finset.mem_univ i) h)]
      have hULB_diag : ∀ s : BlkIdx (Nat.log2 (d i)),
          (ULB * diagB) ⟨i, r⟩ ⟨i, s⟩ = -((blkULeft (d i) * blkDiag (d i)) r s) := by
        intro s
        rw [Matrix.mul_apply, Fintype.sum_sigma]
        rw [Finset.sum_eq_single i]
        · simp only [ULB, ↓reduceDIte, neg_mul, Finset.sum_neg_distrib]
          congr 1
          rw [Matrix.mul_apply]
          refine Finset.sum_congr rfl fun t _ => ?_
          congr 1
          dsimp only [diagB, blkDiag]
          by_cases hts : t = s
          · subst hts; cases t <;> simp
          · have hne : (⟨i, t⟩ : BSum) ≠ ⟨i, s⟩ := by intro h; exact hts (eq_of_heq (Sigma.mk.inj h).2)
            rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hts]
        · intro t _ ht; refine Finset.sum_eq_zero fun u _ => by simp [ULB, ht.symm]
        · intro h; exact absurd (Finset.mem_univ i) h
      simp_rw [hULB_diag]
      simp only [VRB, ↓reduceDIte, neg_mul, Finset.sum_neg_distrib]
      have h1 := congrFun (congrFun (blk_factor (d i) (hd i)) r) c
      rw [Matrix.mul_apply] at h1
      rw [h1]
      dsimp only [EB, adjB, blkMat]; simp
    · have hEB0 : EB ⟨i, r⟩ ⟨j, c⟩ = 0 := by dsimp only [EB, adjB]; simp [hij]
      rw [hEB0, neg_zero]
      refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ => ?_
      by_cases htj : t = j
      · subst htj
        have hzero : (ULB * diagB) ⟨i, r⟩ ⟨t, s⟩ = 0 := by
          rw [Matrix.mul_apply, Fintype.sum_sigma]
          refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
          by_cases hia : i = a
          · subst hia
            have hne : (⟨i, b⟩ : BSum) ≠ ⟨t, s⟩ := fun h => hij (congrArg Sigma.fst h)
            simp [diagB, Matrix.diagonal_apply_ne _ hne]
          · simp [ULB, hia]
        rw [hzero, zero_mul]
      · simp [VRB, htj]
  -- Lift block-diagonal matrices to MIdx = Unit ⊕ NIdx via eB
  let ULM : Matrix MIdx MIdx ℤ := fun x y => match x, y with
    | Sum.inl (), Sum.inl () => 1
    | Sum.inr a, Sum.inr b => ULB (eB a) (eB b)
    | _, _ => 0
  let ULMInv : Matrix MIdx MIdx ℤ := fun x y => match x, y with
    | Sum.inl (), Sum.inl () => 1
    | Sum.inr a, Sum.inr b => ULBInv (eB a) (eB b)
    | _, _ => 0
  let VRM : Matrix MIdx MIdx ℤ := fun x y => match x, y with
    | Sum.inl (), Sum.inl () => 1
    | Sum.inr a, Sum.inr b => VRB (eB a) (eB b)
    | _, _ => 0
  let VRMInv : Matrix MIdx MIdx ℤ := fun x y => match x, y with
    | Sum.inl (), Sum.inl () => 1
    | Sum.inr a, Sum.inr b => VRBInv (eB a) (eB b)
    | _, _ => 0
  let diagM : Matrix MIdx MIdx ℤ := Matrix.diagonal (fun x : MIdx => match x with
    | Sum.inl () => (1 : ℤ)
    | Sum.inr (Sum.inl _) => (1 : ℤ)
    | Sum.inr (Sum.inr i) => (d i : ℤ))
  let midM : Matrix MIdx MIdx ℤ := fun x y => match x, y with
    | Sum.inl (), Sum.inl () => 1
    | Sum.inr a, Sum.inr b => -(EB (eB a) (eB b))
    | _, _ => 0
  have hULM_inv : ULMInv * ULM = 1 := by
    ext x y; rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    cases x with
    | inl u => cases u; cases y with
      | inl u' => cases u'; simp [ULMInv, ULM]
      | inr b => simp [ULMInv, ULM]
    | inr a => cases y with
      | inl u => cases u; simp [ULMInv, ULM]
      | inr b =>
        simp only [ULMInv, ULM, Fintype.sum_unique, mul_zero, zero_add]
        rw [Equiv.sum_comp eB (fun t => ULBInv (eB a) t * ULB t (eB b))]
        have h1 := congrFun (congrFun hULB_inv (eB a)) (eB b)
        rw [Matrix.mul_apply, Matrix.one_apply] at h1
        rw [h1]; by_cases hab : a = b
        · subst hab; simp
        · rw [ite_eq_right (fun h => hab (eB.injective h)), ite_eq_right (fun h => hab (Sum.inr.inj h))]
  have hVRM_inv : VRM * VRMInv = 1 := by
    ext x y; rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    cases x with
    | inl u => cases u; cases y with
      | inl u' => cases u'; simp [VRM, VRMInv]
      | inr b => simp [VRM, VRMInv]
    | inr a => cases y with
      | inl u => cases u; simp [VRM, VRMInv]
      | inr b =>
        simp only [VRM, VRMInv, Fintype.sum_unique, mul_zero, zero_add]
        rw [Equiv.sum_comp eB (fun t => VRB (eB a) t * VRBInv t (eB b))]
        have h1 := congrFun (congrFun hVRB_inv (eB a)) (eB b)
        rw [Matrix.mul_apply, Matrix.one_apply] at h1
        rw [h1]; by_cases hab : a = b
        · subst hab; simp
        · rw [ite_eq_right (fun h => hab (eB.injective h)), ite_eq_right (fun h => hab (Sum.inr.inj h))]
  have hM_fac : ULM * diagM * VRM = midM := by
    ext x y
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    have hUD : ∀ (p q : MIdx), (ULM * diagM) p q = match p, q with
        | Sum.inl (), Sum.inl () => 1
        | Sum.inr a, Sum.inr b => (ULB * diagB) (eB a) (eB b)
        | _, _ => 0 := by
      intro p q
      rw [Matrix.mul_apply, Fintype.sum_sum_type]
      cases p with
      | inl u => cases u; cases q with
        | inl u' => cases u'; simp [ULM, diagM]
        | inr b => simp [ULM, diagM]
      | inr a => cases q with
        | inl u => cases u; simp [ULM, diagM]
        | inr b =>
          simp only [ULM, Fintype.sum_unique, zero_mul, zero_add]
          rw [Matrix.mul_apply, ← Equiv.sum_comp eB (fun t => ULB (eB a) t * diagB t (eB b))]
          refine Finset.sum_congr rfl fun t _ => ?_
          congr 1
          dsimp only [diagM, diagB]
          by_cases htb : t = b
          · subst htb
            rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
            cases t with
            | inl p => cases p; rfl
            | inr i => rfl
          · have hne1 : (Sum.inr t : MIdx) ≠ Sum.inr b := fun h => htb (Sum.inr.inj h)
            have hne2 : eB t ≠ eB b := fun h => htb (eB.injective h)
            rw [Matrix.diagonal_apply_ne _ hne1, Matrix.diagonal_apply_ne _ hne2]
    simp_rw [hUD]
    cases x with
    | inl u => cases u; cases y with
      | inl u' => cases u'; simp [VRM, midM]
      | inr b => simp [VRM, midM]
    | inr a => cases y with
      | inl u => cases u; simp [VRM, midM]
      | inr b =>
        simp only [VRM, midM, Fintype.sum_unique, zero_mul, zero_add]
        rw [Equiv.sum_comp eB (fun t => (ULB * diagB) (eB a) t * VRB t (eB b))]
        have h1 := congrFun (congrFun hB_fac (eB a)) (eB b)
        simpa [Matrix.mul_apply] using h1
  -- Rank-(n+1) factor P and left-inverse Q over ℤ
  let P : Matrix Mask MIdx ℤ := fun a x => match x with
    | Sum.inl () => (1 + a.card : ℤ)
    | Sum.inr z => if eN z ∈ a then 1 else 0
  let Q : Matrix MIdx Mask ℤ := fun x a => match x with
    | Sum.inl () => if a = ∅ then 1 else 0
    | Sum.inr z => if a = {eN z} then 1 else if a = ∅ then -2 else 0
  have hQP : Q * P = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    cases x with
    | inl u =>
      cases u
      rw [Finset.sum_eq_single (∅ : Mask)]
      · cases y with
        | inl u' => cases u'; simp [Q, P]
        | inr z =>
          dsimp only [Q, P]
          rw [ite_eq_left rfl, ite_eq_right (Finset.notMem_empty _), ite_eq_right (by simp)]
          norm_num
      · intro a _ ha; simp [Q, ha]
      · intro h; exact absurd (Finset.mem_univ _) h
    | inr z =>
      have hne : ({eN z} : Mask) ≠ ∅ := Finset.singleton_ne_empty _
      have hsupp : ∀ a : Mask, a ∉ ({({eN z} : Mask), (∅ : Mask)} : Finset Mask) → Q (Sum.inr z) a * P a y = 0 := by
        intro a ha
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
        simp [Q, ha.1, ha.2]
      rw [← Finset.sum_subset (Finset.subset_univ _) (fun a _ ha => hsupp a ha), Finset.sum_pair hne]
      cases y with
      | inl u =>
        cases u
        dsimp only [Q, P]
        rw [ite_eq_left rfl, ite_eq_right hne.symm, ite_eq_left rfl, ite_eq_right (by simp),
          Finset.card_singleton, Finset.card_empty]
        norm_num
      | inr w =>
        dsimp only [Q, P]
        rw [ite_eq_left rfl, ite_eq_right hne.symm, ite_eq_left rfl, ite_eq_right (Finset.notMem_empty _)]
        by_cases hzw : z = w
        · subst hzw
          rw [ite_eq_left (Finset.mem_singleton_self _), ite_eq_left rfl]; norm_num
        · have hneN : eN w ∉ ({eN z} : Mask) := by
            intro hmem; rw [Finset.mem_singleton] at hmem; exact hzw (eN.injective hmem).symm
          have hneS : (Sum.inr z : MIdx) ≠ Sum.inr w := fun h => hzw (Sum.inr.inj h)
          rw [ite_eq_right hneN, ite_eq_right hneS]; norm_num
  have hPTQT : P.transpose * Q.transpose = 1 := by
    rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
  let raw : Matrix Mask Mask ℤ := fun a b =>
    ((1 + a.card + b.card + ((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)).card : Nat) : ℤ)
  have hPmidPT : P * midM * P.transpose = raw := by
    ext a b
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    have hPM_inl : (P * midM) a (Sum.inl ()) = (1 + a.card : ℤ) := by
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique]
      simp [P, midM]
    have hPM_inr : ∀ z : NIdx, (P * midM) a (Sum.inr z) =
        -(∑ w : NIdx, (if eN w ∈ a then (1 : ℤ) else 0) * EB (eB w) (eB z)) := by
      intro z
      rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_unique]
      simp [P, midM, mul_neg, Finset.sum_neg_distrib]
    simp only [Fintype.sum_unique, hPM_inl, hPM_inr, Matrix.transpose_apply]
    simp only [P, neg_mul, Finset.sum_neg_distrib]
    have hcross_sum : (∑ z : NIdx, (∑ w : NIdx, (if eN w ∈ a then (1 : ℤ) else 0) * EB (eB w) (eB z)) *
        (if eN z ∈ b then (1 : ℤ) else 0)) =
        (((a ×ˢ b).filter (fun pair => pair.2 ∈ C pair.1)).card : ℤ) := by
      have h1 : (∑ z : NIdx, (∑ w : NIdx, (if eN w ∈ a then (1 : ℤ) else 0) * EB (eB w) (eB z)) *
          (if eN z ∈ b then (1 : ℤ) else 0)) =
          ∑ w : NIdx, ∑ z : NIdx, if eN w ∈ a ∧ eN z ∈ b ∧ eN z ∈ C (eN w) then (1 : ℤ) else 0 := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun z _ => ?_
        have hmemC : eN z ∈ C (eN w) ↔ adjB (eB w) (eB z) = true := by
          simp [C]
        dsimp only [EB]
        by_cases hw : eN w ∈ a <;> by_cases hz : eN z ∈ b <;> by_cases hc : adjB (eB w) (eB z) = true <;>
          simp [hw, hz, hc, hmemC]
      rw [h1]
      rw [Equiv.sum_comp eN (fun u => ∑ z : NIdx, if u ∈ a ∧ eN z ∈ b ∧ eN z ∈ C u then (1 : ℤ) else 0)]
      have h2 : ∀ u : Fin n, (∑ z : NIdx, if u ∈ a ∧ eN z ∈ b ∧ eN z ∈ C u then (1 : ℤ) else 0) =
          ∑ v : Fin n, if u ∈ a ∧ v ∈ b ∧ v ∈ C u then (1 : ℤ) else 0 := fun u =>
        Equiv.sum_comp eN (fun v => if u ∈ a ∧ v ∈ b ∧ v ∈ C u then (1 : ℤ) else 0)
      simp_rw [h2]
      rw [← Fintype.sum_prod_type (f := fun p : Fin n × Fin n => if p.1 ∈ a ∧ p.2 ∈ b ∧ p.2 ∈ C p.1 then (1 : ℤ) else 0),
        Finset.sum_boole]
      congr 1
      apply congrArg Finset.card
      ext ⟨u, v⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Finset.mem_product]
      tauto
    rw [hcross_sum]
    have hsplit : ((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)).card +
        ((a ×ˢ b).filter (fun z => z.2 ∈ C z.1)).card = a.card * b.card := by
      have hdisj : Disjoint ((a ×ˢ b).filter (fun z => z.2 ∉ C z.1))
          ((a ×ˢ b).filter (fun z => z.2 ∈ C z.1)) := by
        rw [Finset.disjoint_left]
        intro z hz1 hz2
        simp only [Finset.mem_filter] at hz1 hz2
        exact hz1.2 hz2.2
      have hun : ((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)) ∪
          ((a ×ˢ b).filter (fun z => z.2 ∈ C z.1)) = a ×ˢ b := by
        ext z; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      rw [← Finset.card_union_of_disjoint hdisj, hun, Finset.card_product]
    dsimp only [raw]
    have hsplitZ : (((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)).card : ℤ) +
        (((a ×ˢ b).filter (fun z => z.2 ∈ C z.1)).card : ℤ) = (a.card : ℤ) * (b.card : ℤ) := by
      exact_mod_cast hsplit
    push_cast
    linarith
  -- Reindex from MIdx to D via eD
  let A : Matrix Mask D ℤ := fun a x => (P * ULM) a (eD.symm x)
  let U : Matrix D Mask ℤ := fun x a => (ULMInv * Q) (eD.symm x) a
  let B : Matrix D Mask ℤ := fun x b => (VRM * P.transpose) (eD.symm x) b
  let V : Matrix Mask D ℤ := fun b x => (Q.transpose * VRMInv) b (eD.symm x)
  let diagonal : Matrix D D ℤ := Matrix.diagonal
    (Sum.elim (fun _ : Fin (k + 1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ)))
  have hdiag_eD : ∀ x y : MIdx, diagonal (eD x) (eD y) = diagM x y := by
    intro x y
    dsimp only [diagonal, diagM]
    by_cases hxy : x = y
    · subst hxy
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
      cases x with
      | inl u => cases u; simp [eD]
      | inr z => cases z <;> simp [eD]
    · have hne : eD x ≠ eD y := fun h => hxy (eD.injective h)
      rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hxy]
  have hUA : U * A = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hcalc : (∑ a : Mask, U x a * A a y) = ((ULMInv * Q) * (P * ULM)) (eD.symm x) (eD.symm y) := by
      rw [Matrix.mul_apply]
    rw [hcalc, Matrix.mul_assoc, ← Matrix.mul_assoc Q P ULM, hQP, Matrix.one_mul, hULM_inv, Matrix.one_apply]
    simp [eD.symm.injective.eq_iff]
  have hBV : B * V = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    have hcalc : (∑ b : Mask, B x b * V b y) = ((VRM * P.transpose) * (Q.transpose * VRMInv)) (eD.symm x) (eD.symm y) := by
      rw [Matrix.mul_apply]
    rw [hcalc, Matrix.mul_assoc, ← Matrix.mul_assoc P.transpose Q.transpose VRMInv, hPTQT,
      Matrix.one_mul, hVRM_inv, Matrix.one_apply]
    simp [eD.symm.injective.eq_iff]
  have hADB : A * diagonal * B = raw := by
    ext a b
    have hAD : ∀ y : D, (A * diagonal) a y = ((P * ULM) * diagM) a (eD.symm y) := by
      intro y
      rw [Matrix.mul_apply, Matrix.mul_apply, ← Equiv.sum_comp eD (fun x => A a x * diagonal x y)]
      refine Finset.sum_congr rfl fun t _ => ?_
      dsimp only [A]
      rw [Equiv.symm_apply_apply]
      have hde := hdiag_eD t (eD.symm y)
      rw [Equiv.apply_symm_apply] at hde
      rw [hde]
    rw [Matrix.mul_apply]
    simp_rw [hAD]
    rw [← Equiv.sum_comp eD (fun y => ((P * ULM) * diagM) a (eD.symm y) * B y b)]
    have hstep : ∑ t : MIdx, ((P * ULM) * diagM) a (eD.symm (eD t)) * B (eD t) b =
        (((P * ULM) * diagM) * (VRM * P.transpose)) a b := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun t _ => by dsimp only [B]; simp
    rw [hstep]
    have hassoc : ((P * ULM) * diagM) * (VRM * P.transpose) = P * (ULM * diagM * VRM) * P.transpose := by
      simp [Matrix.mul_assoc]
    rw [hassoc, hM_fac, hPmidPT]
  exact ⟨C, hn_le, hC_le, ⟨A, B, U, V, hADB, hUA, hBV⟩⟩

private lemma mat_one_eq_of_dec {α : Type*} (d1 d2 : DecidableEq α) :
    @OfNat.ofNat (Matrix α α ℤ) 1 (@One.toOfNat1 _ (@Matrix.one α ℤ d1 _ _)) =
    @OfNat.ofNat (Matrix α α ℤ) 1 (@One.toOfNat1 _ (@Matrix.one α ℤ d2 _ _)) := by
  ext x y
  by_cases hxy : x = y
  · subst hxy
    rw [@Matrix.one_apply_eq α ℤ d1 _ _ x, @Matrix.one_apply_eq α ℤ d2 _ _ x]
  · rw [@Matrix.one_apply_ne α ℤ d1 _ _ x y hxy, @Matrix.one_apply_ne α ℤ d2 _ _ x y hxy]

private lemma mat_diag_eq_of_dec {α : Type*} (d1 d2 : DecidableEq α) (v : α → ℤ) :
    @Matrix.diagonal α ℤ d1 _ v = @Matrix.diagonal α ℤ d2 _ v := by
  ext x y
  unfold Matrix.diagonal
  by_cases hxy : x = y <;> simp [hxy]

private lemma raw_entry_eq_of_dec {n : Nat} (C : Fin n → Finset (Fin n)) (a b : Finset (Fin n))
    (p1 p2 : DecidablePred (fun z : Fin n × Fin n => z.2 ∉ C z.1)) :
    ((1 + a.card + b.card + (@Finset.filter _ _ p1 (a ×ˢ b)).card : Nat) : ℤ) =
    ((1 + a.card + b.card + (@Finset.filter _ _ p2 (a ×ˢ b)).card : Nat) : ℤ) := by
  apply congrArg (fun m : Nat => ((1 + a.card + b.card + m : Nat) : ℤ))
  apply congrArg Finset.card
  ext z
  simp only [Finset.mem_filter]

theorem main_proof :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (h : Nat) (d : Fin h → Nat), (∀ i, 2 ≤ d i) →
      ∃ k : Nat,
        let n := k+h
        let Mask := Finset (Fin n)
        let D := Fin (k+1) ⊕ Fin h
        ∃ C : Fin n → Finset (Fin n),
          n ≤ (Finset.univ : Finset (Fin h)).sum (fun i => 2+4*Nat.log2 (d i)) ∧
          (Finset.univ : Finset (Fin n)).sum (fun i => (C i).card) ≤
            (Finset.univ : Finset (Fin h)).sum (fun i => 3+10*Nat.log2 (d i)) ∧
          let raw : Matrix Mask Mask ℤ := fun a b =>
            ((1+a.card+b.card+((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)).card : Nat) : ℤ)
          let diagonal : Matrix D D ℤ := Matrix.diagonal
            (Sum.elim (fun _ : Fin (k+1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ)))
          (∃ (A : Matrix Mask D ℤ) (B : Matrix D Mask ℤ)
            (U : Matrix D Mask ℤ) (V : Matrix Mask D ℤ),
            A * diagonal * B = raw ∧ U * A = 1 ∧ B * V = 1) ∧
          ∀ base : Nat,
            let M := base+2
            let combine := fun (f : Mask → ZMod (base+2)) (b : Mask) =>
              (Finset.univ : Finset Mask).sum (fun a => f a * (raw a b : ZMod (base+2)))
            ((Finset.univ : Finset (Mask → ZMod (base+2))).image combine).card =
              M^(k+1) * (Finset.univ : Finset (Fin h)).prod (fun i => M / Nat.gcd M (d i)) := by
  let _ : ∀ P : Prop, Decidable P := Classical.propDecidable
  intro h d hd
  rcases main_construction h d hd with ⟨k, C, hn_le, hC_le, A, B, U, V, hfac, hUA, hBV⟩
  have hUA' : U * A = 1 := hUA.trans (mat_one_eq_of_dec _ _)
  have hBV' : B * V = 1 := hBV.trans (mat_one_eq_of_dec _ _)
  have hfac' : A * Matrix.diagonal (Sum.elim (fun _ : Fin (k + 1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ))) * B =
      fun a b => ((1 + a.card + b.card + ((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)).card : Nat) : ℤ) := by
    ext a b
    exact (congrFun (congrFun (congrArg (fun M => A * M * B)
        (mat_diag_eq_of_dec _ _
          (Sum.elim (fun _ : Fin (k + 1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ))))) a) b).trans
      ((congrFun (congrFun hfac a) b).trans (raw_entry_eq_of_dec C a b _ _))
  refine ⟨k, C, hn_le, hC_le, ⟨A, B, U, V, hfac', hUA', hBV'⟩, ?_⟩
  intro base
  have hcard := image_combine_card (n := k + h) (k := k) (h := h) (base := base) d _ A B U V hfac hUA hBV
  dsimp only at hcard ⊢
  rw [← hcard]
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨f, rfl⟩ <;> refine ⟨f, funext fun b => Finset.sum_congr rfl fun a _ => ?_⟩
  · exact congrArg (fun z : ℤ => f a * (z : ZMod (base + 2))) (raw_entry_eq_of_dec C a b _ _)
  · exact congrArg (fun z : ℤ => f a * (z : ZMod (base + 2))) (raw_entry_eq_of_dec C a b _ _)

end PEqualNP.Outside.L_lib_1240

theorem PEqualNP.Outside.L_lib_1240 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (h : Nat) (d : Fin h → Nat), (∀ i, 2 ≤ d i) →
  ∃ k : Nat,
    let n := k+h
    let Mask := Finset (Fin n)
    let D := Fin (k+1) ⊕ Fin h
    ∃ C : Fin n → Finset (Fin n),
      n ≤ (Finset.univ : Finset (Fin h)).sum (fun i => 2+4*Nat.log2 (d i)) ∧
      (Finset.univ : Finset (Fin n)).sum (fun i => (C i).card) ≤
        (Finset.univ : Finset (Fin h)).sum (fun i => 3+10*Nat.log2 (d i)) ∧
      let raw : Matrix Mask Mask ℤ := fun a b =>
        ((1+a.card+b.card+((a ×ˢ b).filter (fun z => z.2 ∉ C z.1)).card : Nat) : ℤ)
      let diagonal : Matrix D D ℤ := Matrix.diagonal
        (Sum.elim (fun _ : Fin (k+1) => (1 : ℤ)) (fun i : Fin h => (d i : ℤ)))
      (∃ (A : Matrix Mask D ℤ) (B : Matrix D Mask ℤ)
        (U : Matrix D Mask ℤ) (V : Matrix Mask D ℤ),
        A * diagonal * B = raw ∧ U * A = 1 ∧ B * V = 1) ∧
      ∀ base : Nat,
        let M := base+2
        let combine := fun (f : Mask → ZMod (base+2)) (b : Mask) =>
          (Finset.univ : Finset Mask).sum (fun a => f a * (raw a b : ZMod (base+2)))
        ((Finset.univ : Finset (Mask → ZMod (base+2))).image combine).card =
          M^(k+1) * (Finset.univ : Finset (Fin h)).prod (fun i => M / Nat.gcd M (d i)) :=
  PEqualNP.Outside.L_lib_1240.main_proof
