import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38164

private def ofBits (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => ofBits f k + if f k then 2 ^ k else 0

private lemma ofBits_lt (f : Nat → Bool) : ∀ n, ofBits f n < 2 ^ n
  | 0 => by simp [ofBits]
  | k + 1 => by
    have ih := ofBits_lt f k
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    simp only [ofBits]
    cases f k <;> simp <;> omega

private lemma testBit_add_two_pow {a k i : Nat} (ha : a < 2 ^ k) :
    (a + 2 ^ k).testBit i = if i = k then true else a.testBit i := by
  by_cases hik : i = k
  · subst hik
    simp only [↓reduceIte, Nat.testBit_eq_decide_div_mod_eq]
    have hdiv : (a + 2 ^ i) / 2 ^ i = 1 := by
      have hpos : 0 < 2 ^ i := Nat.pow_pos (by decide)
      rw [Nat.add_div_right _ hpos, Nat.div_eq_of_lt ha]
    rw [hdiv]
    decide
  · simp only [hik, ↓reduceIte]
    by_cases hlt : i < k
    · simp only [Nat.testBit_eq_decide_div_mod_eq]
      have hpos : 0 < 2 ^ i := Nat.pow_pos (by decide)
      have hpow : 2 ^ k = 2 ^ (k - i) * 2 ^ i := by
        rw [← Nat.pow_add, Nat.sub_add_cancel (Nat.le_of_lt hlt)]
      have hdiv : (a + 2 ^ k) / 2 ^ i = a / 2 ^ i + 2 ^ (k - i) := by
        rw [hpow, Nat.add_mul_div_right _ _ hpos]
      have heven : 2 ^ (k - i) % 2 = 0 := by
        have h1 : 1 ≤ k - i := by omega
        obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' h1
        rw [hm, pow_succ]
        omega
      rw [hdiv]
      have hmod : (a / 2 ^ i + 2 ^ (k - i)) % 2 = (a / 2 ^ i) % 2 := by omega
      rw [hmod]
    · have hgt : k + 1 ≤ i := by omega
      have hle : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
      have h1 : a + 2 ^ k < 2 ^ i := by
        have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
        omega
      have h2 : a < 2 ^ i := by omega
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]

private lemma ofBits_testBit (f : Nat → Bool) :
    ∀ n i, (ofBits f n).testBit i = (decide (i < n) && f i)
  | 0, i => by simp [ofBits]
  | k + 1, i => by
    have ih := ofBits_testBit f k i
    simp only [ofBits]
    cases hfk : f k
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, ih]
      by_cases hi : i < k
      · have hi' : i < k + 1 := by omega
        simp [hi, hi']
      · by_cases heq : i = k
        · subst heq
          simp [hfk]
        · have hi' : ¬ i < k + 1 := by omega
          simp [hi, hi']
    · simp only [↓reduceIte, testBit_add_two_pow (ofBits_lt f k), ih]
      by_cases heq : i = k
      · subst heq
        simp [hfk]
      · simp only [heq, ↓reduceIte]
        have hiff : i < k ↔ i < k + 1 := by omega
        simp [hiff]

private lemma nat_eq_of_testBit_lt {a b n : Nat} (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h : ∀ i < n, a.testBit i = b.testBit i) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h i hi
  · have hle : 2 ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hle),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hle)]

private def solveBitAux (N d : Nat) (hd : 0 < d) (target : Nat → Bool) : Nat → Bool
  | 0 => false
  | rem + 1 =>
    let i := N - (rem + 1)
    let b1 := if h1 : d < rem + 1 then solveBitAux N d hd target (rem + 1 - d) else false
    let b2 := if h2 : 2 * d < rem + 1 then solveBitAux N d hd target (rem + 1 - 2 * d) else false
    xor (target i) (xor b1 b2)
termination_by rem => rem

private lemma exists_mix (N d : Nat) (hd : 0 < d) (target : Nat → Bool) :
    ∃ x < 2 ^ (N + 2 * d), ∀ i < N,
      xor (x.testBit i) (xor (x.testBit (i + d)) (x.testBit (i + 2 * d))) = target i := by
  let f : Nat → Bool := fun i => if i < N then solveBitAux N d hd target (N - i) else false
  let x : Nat := ofBits f N
  have hx_lt : x < 2 ^ (N + 2 * d) :=
    lt_of_lt_of_le (ofBits_lt f N) (Nat.pow_le_pow_right (by decide) (Nat.le_add_right N (2 * d)))
  have hx_bit : ∀ j, x.testBit j = f j := by
    intro j
    rw [ofBits_testBit]
    by_cases hj : j < N
    · simp [f, hj]
    · simp [f, hj]
  refine ⟨x, hx_lt, ?_⟩
  intro i hi
  rw [hx_bit i, hx_bit (i + d), hx_bit (i + 2 * d)]
  have hsub : N - i = (N - i - 1) + 1 := by omega
  have hfi : f i = xor (target i) (xor (f (i + d)) (f (i + 2 * d))) := by
    simp only [f, hi, ↓reduceIte]
    conv_lhs => rw [hsub]
    rw [solveBitAux]
    have hidx : N - (N - i - 1 + 1) = i := by omega
    have h1iff : d < N - i - 1 + 1 ↔ i + d < N := by omega
    have h2iff : 2 * d < N - i - 1 + 1 ↔ i + 2 * d < N := by omega
    have h1sub : N - i - 1 + 1 - d = N - (i + d) := by omega
    have h2sub : N - i - 1 + 1 - 2 * d = N - (i + 2 * d) := by omega
    simp only [hidx]
    congr 1
    congr 1
    · by_cases h1 : i + d < N
      · have h1' : d < N - i - 1 + 1 := h1iff.mpr h1
        simp only [h1, h1', ↓reduceDIte, ↓reduceIte, h1sub]
      · have h1' : ¬ d < N - i - 1 + 1 := fun c => h1 (h1iff.mp c)
        simp only [h1, h1', ↓reduceDIte, ↓reduceIte]
    · by_cases h2 : i + 2 * d < N
      · have h2' : 2 * d < N - i - 1 + 1 := h2iff.mpr h2
        simp only [h2, h2', ↓reduceDIte, ↓reduceIte, h2sub]
      · have h2' : ¬ 2 * d < N - i - 1 + 1 := fun c => h2 (h2iff.mp c)
        simp only [h2, h2', ↓reduceDIte, ↓reduceIte]
  rw [hfi]
  cases target i <;> cases f (i + d) <;> cases f (i + 2 * d) <;> rfl

private def chiFn (bits : Nat → Bool) (j : Nat) : Bool :=
  xor (bits j) (!(bits (j + 1)) && bits (j + 2))

private def invChiAux (h : Nat) (z : Finset Nat) (a b : Bool) : Nat → Bool
  | 0 => b
  | 1 => a
  | k + 2 =>
    xor (decide (h - 1 - k ∈ z)) (!(invChiAux h z a b (k + 1)) && invChiAux h z a b k)

private def invChi (h : Nat) (z : Finset Nat) (a b : Bool) (i : Nat) : Bool :=
  if i < h + 2 then invChiAux h z a b (h + 1 - i) else false

private def stripOf (h : Nat) (z : Finset Nat) (a b : Bool) : Nat :=
  ofBits (invChi h z a b) (h + 2)

private lemma stripOf_lt (h : Nat) (z : Finset Nat) (a b : Bool) :
    stripOf h z a b < 2 ^ (h + 2) :=
  ofBits_lt _ _

private lemma stripOf_testBit (h : Nat) (z : Finset Nat) (a b : Bool) (i : Nat) :
    (stripOf h z a b).testBit i = invChi h z a b i := by
  rw [stripOf, ofBits_testBit]
  by_cases hi : i < h + 2
  · simp [invChi, hi]
  · simp [invChi, hi]

private lemma stripOf_chi (h : Nat) (z : Finset Nat) (a b : Bool) (j : Nat) (hj : j < h) :
    chiFn (fun i => (stripOf h z a b).testBit i) j = decide (j ∈ z) := by
  simp only [chiFn, stripOf_testBit, invChi]
  have h0 : j < h + 2 := by omega
  have h1 : j + 1 < h + 2 := by omega
  have h2 : j + 2 < h + 2 := by omega
  simp only [h0, h1, h2, ↓reduceIte]
  have hk0 : h + 1 - j = (h - 1 - j) + 2 := by omega
  have hk1 : h + 1 - (j + 1) = (h - 1 - j) + 1 := by omega
  have hk2 : h + 1 - (j + 2) = h - 1 - j := by omega
  have hjback : h - 1 - (h - 1 - j) = j := by omega
  rw [hk0, hk1, hk2, invChiAux, hjback]
  cases decide (j ∈ z) <;>
    cases invChiAux h z a b (h - 1 - j + 1) <;>
    cases invChiAux h z a b (h - 1 - j) <;> rfl

private lemma stripOf_first (h : Nat) (z : Finset Nat) (hz : z ⊆ Finset.range h) (a b : Bool) :
    (Finset.range h).filter (fun j => chiFn (fun i => (stripOf h z a b).testBit i) j) = z := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, hchi⟩
    rw [stripOf_chi h z a b j hj] at hchi
    exact of_decide_eq_true hchi
  · intro hjz
    have hj : j < h := Finset.mem_range.mp (hz hjz)
    refine ⟨hj, ?_⟩
    rw [stripOf_chi h z a b j hj]
    exact decide_eq_true hjz

private lemma eq_stripOf (h u : Nat) (hu : u < 2 ^ (h + 2)) :
    u = stripOf h
      ((Finset.range h).filter (fun j => chiFn (fun i => u.testBit i) j))
      (u.testBit h) (u.testBit (h + 1)) := by
  set z := (Finset.range h).filter (fun j => chiFn (fun i => u.testBit i) j)
  apply nat_eq_of_testBit_lt hu (stripOf_lt h z _ _)
  have hstep : ∀ k ≤ h + 1,
      u.testBit (h + 1 - k) = invChiAux h z (u.testBit h) (u.testBit (h + 1)) k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hk
      match k with
      | 0 => simp [invChiAux]
      | 1 => simp [invChiAux]
      | m + 2 =>
        have hm1 : m + 1 ≤ h + 1 := by omega
        have hm0 : m ≤ h + 1 := by omega
        have ih1 := ih (m + 1) (by omega) hm1
        have ih0 := ih m (by omega) hm0
        rw [invChiAux]
        have hj : h - 1 - m < h := by omega
        have hidx0 : h + 1 - (m + 2) = h - 1 - m := by omega
        have hidx1 : h + 1 - (m + 1) = (h - 1 - m) + 1 := by omega
        have hidx2 : h + 1 - m = (h - 1 - m) + 2 := by omega
        rw [hidx0]
        rw [hidx1] at ih1
        rw [hidx2] at ih0
        rw [← ih1, ← ih0]
        have hmem : decide (h - 1 - m ∈ z) = chiFn (fun i => u.testBit i) (h - 1 - m) := by
          simp only [z, Finset.mem_filter, Finset.mem_range, hj, true_and, decide_eq_true_eq]
          cases chiFn (fun i => u.testBit i) (h - 1 - m) <;> simp
        rw [hmem, chiFn]
        cases u.testBit (h - 1 - m) <;>
          cases u.testBit (h - 1 - m + 1) <;>
          cases u.testBit (h - 1 - m + 2) <;> rfl
  intro i hi
  rw [stripOf_testBit, invChi]
  simp only [hi, ↓reduceIte]
  have h1 := hstep (h + 1 - i) (by omega)
  have hback : h + 1 - (h + 1 - i) = i := by omega
  rw [hback] at h1
  exact h1

private lemma invChiAux_const_of_top2 (h : Nat) (hh : 4 ≤ h) (z : Finset Nat)
    (h2 : h - 2 ∈ z) (h1 : h - 1 ∈ z) (a b : Bool) :
    ∀ k ≥ 3, invChiAux h z a b k = invChiAux h z false false k := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    match k with
    | 0 | 1 | 2 => omega
    | 3 =>
      simp only [invChiAux, Nat.sub_zero]
      have hm1 : h - 1 - 1 = h - 2 := by omega
      rw [hm1, decide_eq_true h2, decide_eq_true h1]
      cases a <;> cases b <;> rfl
    | 4 =>
      have h3ab : invChiAux h z a b 3 = true := by
        simp only [invChiAux, Nat.sub_zero]
        have hm1 : h - 1 - 1 = h - 2 := by omega
        rw [hm1, decide_eq_true h2, decide_eq_true h1]
        cases a <;> cases b <;> rfl
      have h3ff : invChiAux h z false false 3 = true := by
        simp only [invChiAux, Nat.sub_zero]
        have hm1 : h - 1 - 1 = h - 2 := by omega
        rw [hm1, decide_eq_true h2, decide_eq_true h1]
        rfl
      change xor (decide (h - 1 - 2 ∈ z)) (!(invChiAux h z a b 3) && invChiAux h z a b 2) =
        xor (decide (h - 1 - 2 ∈ z)) (!(invChiAux h z false false 3) && invChiAux h z false false 2)
      rw [h3ab, h3ff]
      rfl
    | m + 5 =>
      have ih1 := ih (m + 4) (by omega) (by omega)
      have ih0 := ih (m + 3) (by omega) (by omega)
      change xor (decide (h - 1 - (m + 3) ∈ z))
          (!(invChiAux h z a b (m + 4)) && invChiAux h z a b (m + 3)) =
        xor (decide (h - 1 - (m + 3) ∈ z))
          (!(invChiAux h z false false (m + 4)) && invChiAux h z false false (m + 3))
      rw [ih1, ih0]

private def topBit (z1 z0 a b : Bool) : Fin 5 → Bool
  | 0 => false
  | 1 => true
  | 2 => xor z0 (!a && b)
  | 3 => a
  | 4 => b

private lemma top2_collision_decide (u3 m3 m2 m1 m0 mh mhp1 : Bool) (miss3 : Bool) :
    ∃ p₁ p₂ : Bool × Bool, p₁ ≠ p₂ ∧
      let eval := fun (p : Bool × Bool) =>
        let b3 := xor u3 m3
        let b2 := xor true m2
        let b1 := xor (xor true (!p.1 && p.2)) m1
        let b0 := xor p.1 m0
        let b_h := xor p.2 mh
        let c3 := xor b3 (!b2 && b1)
        let c2 := xor b2 (!b1 && b0)
        let c1 := xor b1 (!b0 && b_h)
        if miss3 then (c2, c1) else (c3, c1)
      eval p₁ = eval p₂ := by
  revert u3 m3 m2 m1 m0 mh mhp1 miss3
  decide

private def sliceOut (z3 z2 z1 z0 a b : Bool) : Bool × Bool × Bool :=
  let u5 := b
  let u4 := a
  let u3 := xor z0 (!u4 && u5)
  let u2 := xor z1 (!u3 && u4)
  let u1 := xor z2 (!u2 && u3)
  let u0 := xor z3 (!u1 && u2)
  let m0 := false
  let m1 := !z0
  let m2 := z0
  let m3 := z0
  let m4 := true
  let m5 := false
  let b0 := xor u0 m0
  let b1 := xor u1 m1
  let b2 := xor u2 m2
  let b3 := xor u3 m3
  let b4 := xor u4 m4
  let b5 := xor u5 m5
  let c0 := xor b0 (!b1 && b2)
  let c2 := xor b2 (!b3 && b4)
  let c3 := xor b3 (!b4 && b5)
  (c0, c2, c3)

private lemma sliceOut_card (z3 z2 z1 z0 : Bool) :
    ((Finset.univ : Finset (Bool × Bool)).image (fun p => sliceOut z3 z2 z1 z0 p.1 p.2)).card =
      if z1 && z0 then 3 else 4 := by
  revert z3 z2 z1 z0
  decide

private lemma powerset_split_cards (h : Nat) (hh : 4 ≤ h) :
    let P := (Finset.range h).powerset
    let bad := P.filter (fun z => h - 2 ∈ z ∧ h - 1 ∈ z)
    let good := P.filter (fun z => ¬(h - 2 ∈ z ∧ h - 1 ∈ z))
    bad.card = 2 ^ (h - 2) ∧ good.card = 3 * 2 ^ (h - 2) := by
  intro P bad good
  have hbad : bad = ((Finset.range (h - 2)).powerset).image (fun s => insert (h - 2) (insert (h - 1) s)) := by
    ext z
    simp only [bad, P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hz, h2, h1⟩
      refine ⟨z.erase (h - 1) |>.erase (h - 2), ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_erase] at hk
        have hk' := Finset.mem_range.mp (hz hk.2.2)
        exact Finset.mem_range.mpr (by omega)
      · ext k
        simp only [Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro (rfl | rfl | ⟨_, _, hkz⟩)
          · exact h2
          · exact h1
          · exact hkz
        · intro hkz
          by_cases hk2 : k = h - 2
          · exact Or.inl hk2
          · by_cases hk1 : k = h - 1
            · exact Or.inr (Or.inl hk1)
            · exact Or.inr (Or.inr ⟨hk2, hk1, hkz⟩)
    · rintro ⟨s, hs, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro k hk
        simp only [Finset.mem_insert] at hk
        rcases hk with rfl | rfl | hks
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by omega)
        · exact Finset.mem_range.mpr (by have := Finset.mem_range.mp (hs hks); omega)
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hinj : Set.InjOn (fun s : Finset Nat => insert (h - 2) (insert (h - 1) s))
      (↑(Finset.range (h - 2)).powerset) := by
    intro s₁ hs₁ s₂ hs₂ heq
    simp only [Finset.mem_coe, Finset.mem_powerset] at hs₁ hs₂
    ext k
    have hk := congrArg (fun t => k ∈ t) heq
    simp only [Finset.mem_insert] at hk
    constructor
    · intro hk1
      have hlt := Finset.mem_range.mp (hs₁ hk1)
      have hmem : k = h - 2 ∨ k = h - 1 ∨ k ∈ s₂ := hk.mp (Or.inr (Or.inr hk1))
      rcases hmem with rfl | rfl | hk2
      · omega
      · omega
      · exact hk2
    · intro hk2
      have hlt := Finset.mem_range.mp (hs₂ hk2)
      have hmem : k = h - 2 ∨ k = h - 1 ∨ k ∈ s₁ := hk.mpr (Or.inr (Or.inr hk2))
      rcases hmem with rfl | rfl | hk1
      · omega
      · omega
      · exact hk1
  have hbad_card : bad.card = 2 ^ (h - 2) := by
    rw [hbad, Finset.card_image_of_injOn hinj, Finset.card_powerset, Finset.card_range]
  have htot : bad.card + good.card = P.card := by
    have hs := Finset.sum_filter_add_sum_filter_not P (fun z => h - 2 ∈ z ∧ h - 1 ∈ z) (fun _ => 1)
    simpa [bad, good] using hs
  have hP : P.card = 2 ^ h := by simp [P]
  have hpow : 2 ^ h = 4 * 2 ^ (h - 2) := by
    have hh2 : h = (h - 2) + 2 := by omega
    conv_lhs => rw [hh2]
    ring
  refine ⟨hbad_card, ?_⟩
  omega

theorem main_proof :
    ∀ (h d : Nat), 4 ≤ h → 0 < d →
      let strips := Finset.range (2^(h+2))
      let limit := 2^(h+2+2*d)
      let mix := fun (x i : Nat) =>
        xor (x.testBit i) (xor (x.testBit (i+d)) (x.testBit (i+2*d)))
      let chi := fun (bits : Nat → Bool) (j : Nat) =>
        xor (bits j) (!(bits (j+1)) && bits (j+2))
      let first := fun u : Nat =>
        (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
      let count := fun (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat) =>
        (strips.image (fun u =>
          let z := first u
          let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
          (z, (mask z).filter (fun j => chi bits j)))).card
      (∃ x y : Nat, x < limit ∧ y < limit ∧
        count (fun z => if h-1 ∈ z then y else x)
          (fun _ => {h-4,h-2,h-1}) = 15 * 2^(h-2)) ∧
      ∀ (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat),
        (∀ z ∈ strips.image first, pick z < limit ∧ mask z ⊆ Finset.range h ∧
          (h-3 ∉ mask z ∨ h-2 ∉ mask z)) →
        count pick mask ≤ 15 * 2^(h-2) := by
  intro h d hh hd
  dsimp only
  let strips := Finset.range (2 ^ (h + 2))
  let limit := 2 ^ (h + 2 + 2 * d)
  let mix := fun (x i : Nat) =>
    xor (x.testBit i) (xor (x.testBit (i + d)) (x.testBit (i + 2 * d)))
  let first := fun u : Nat =>
    (Finset.range h).filter (fun j => chiFn (fun i => u.testBit i) j)
  have hcount_sum : ∀ (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat),
      (strips.image (fun u =>
        let z := first u
        let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
        (z, (mask z).filter (fun j => chiFn bits j)))).card =
      ∑ z ∈ (Finset.range h).powerset,
        ((Finset.univ : Finset (Bool × Bool)).image (fun p =>
          let u := stripOf h z p.1 p.2
          let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
          (mask z).filter (fun j => chiFn bits j))).card := by
    intro pick mask
    let f : Nat → Finset Nat × Finset Nat := fun u =>
      let z := first u
      let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
      (z, (mask z).filter (fun j => chiFn bits j))
    let G : Finset Nat → Finset (Finset Nat × Finset Nat) := fun z =>
      (Finset.univ : Finset (Bool × Bool)).image (fun p =>
        let u := stripOf h z p.1 p.2
        let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
        (z, (mask z).filter (fun j => chiFn bits j)))
    have hEq : strips.image f = (Finset.range h).powerset.biUnion G := by
      ext q
      simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_powerset]
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hu' : u < 2 ^ (h + 2) := Finset.mem_range.mp hu
        refine ⟨first u, Finset.filter_subset _ _, ?_⟩
        refine Finset.mem_image.mpr ⟨(u.testBit h, u.testBit (h + 1)), Finset.mem_univ _, ?_⟩
        have hueq : u = stripOf h (first u) (u.testBit h) (u.testBit (h + 1)) := eq_stripOf h u hu'
        simp only [f]
        rw [← hueq]
      · rintro ⟨z, hz, hq⟩
        rcases Finset.mem_image.mp hq with ⟨⟨a, b⟩, _, rfl⟩
        refine ⟨stripOf h z a b, Finset.mem_range.mpr (stripOf_lt h z a b), ?_⟩
        have hf : first (stripOf h z a b) = z := stripOf_first h z hz a b
        simp only [f, hf]
    have hDisj : Set.PairwiseDisjoint (↑(Finset.range h).powerset : Set (Finset Nat)) G := by
      intro z₁ _ z₂ _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro q hq1 hq2
      rcases Finset.mem_image.mp hq1 with ⟨_, _, rfl⟩
      rcases Finset.mem_image.mp hq2 with ⟨_, _, h2⟩
      exact hne (congrArg Prod.fst h2).symm
    rw [hEq, Finset.card_biUnion hDisj]
    refine Finset.sum_congr rfl ?_
    intro z _
    let hpair : Finset Nat → Finset Nat × Finset Nat := fun s => (z, s)
    have hG : G z = ((Finset.univ : Finset (Bool × Bool)).image (fun p =>
        let u := stripOf h z p.1 p.2
        let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
        (mask z).filter (fun j => chiFn bits j))).image hpair := by
      rw [Finset.image_image]
      rfl
    rw [hG, Finset.card_image_of_injective]
    intro s₁ s₂ hs
    exact congrArg Prod.snd hs
  have hcards := powerset_split_cards h hh
  dsimp only at hcards
  constructor
  · let tx : Nat → Bool := fun i => decide (i = h - 3) || decide (i = h)
    let ty : Nat → Bool := fun i => decide (i = h - 2) || decide (i = h - 1) || decide (i = h)
    rcases exists_mix (h + 2) d hd tx with ⟨x, hx_lt, hx_mix⟩
    rcases exists_mix (h + 2) d hd ty with ⟨y, hy_lt, hy_mix⟩
    refine ⟨x, y, hx_lt, hy_lt, ?_⟩
    change (strips.image (fun u =>
      let z := first u
      let bits := fun i : Nat => xor (u.testBit i) (mix (if h - 1 ∈ z then y else x) i)
      (z, ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j => chiFn bits j)))).card =
      15 * 2 ^ (h - 2)
    rw [hcount_sum (fun z => if h - 1 ∈ z then y else x) (fun _ => {h - 4, h - 2, h - 1})]
    have hfiber : ∀ z ∈ (Finset.range h).powerset,
        ((Finset.univ : Finset (Bool × Bool)).image (fun p =>
          let u := stripOf h z p.1 p.2
          let bits := fun i : Nat => xor (u.testBit i) (mix (if h - 1 ∈ z then y else x) i)
          ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j => chiFn bits j))).card =
        if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4 := by
      intro z _
      let z3 := decide (h - 4 ∈ z)
      let z2 := decide (h - 3 ∈ z)
      let z1 := decide (h - 2 ∈ z)
      let z0 := decide (h - 1 ∈ z)
      let enc : Finset Nat → Bool × Bool × Bool := fun S =>
        (decide (h - 4 ∈ S), decide (h - 2 ∈ S), decide (h - 1 ∈ S))
      have henc_inj : Set.InjOn enc
          (↑((Finset.univ : Finset (Bool × Bool)).image (fun p =>
            let u := stripOf h z p.1 p.2
            let bits := fun i : Nat => xor (u.testBit i) (mix (if h - 1 ∈ z then y else x) i)
            ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j => chiFn bits j)))) := by
        intro S₁ hS₁ S₂ hS₂ heq
        simp only [Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hS₁ hS₂
        have hsub1 : S₁ ⊆ {h - 4, h - 2, h - 1} := by
          rcases hS₁ with ⟨_, rfl⟩; exact Finset.filter_subset _ _
        have hsub2 : S₂ ⊆ {h - 4, h - 2, h - 1} := by
          rcases hS₂ with ⟨_, rfl⟩; exact Finset.filter_subset _ _
        have he0 : h - 4 ∈ S₁ ↔ h - 4 ∈ S₂ := decide_eq_decide.mp (congrArg Prod.fst heq)
        have he1 : h - 2 ∈ S₁ ↔ h - 2 ∈ S₂ := decide_eq_decide.mp (congrArg (fun q => q.2.1) heq)
        have he2 : h - 1 ∈ S₁ ↔ h - 1 ∈ S₂ := decide_eq_decide.mp (congrArg (fun q => q.2.2) heq)
        ext j
        constructor
        · intro hj
          have hmem := hsub1 hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl
          · exact he0.mp hj
          · exact he1.mp hj
          · exact he2.mp hj
        · intro hj
          have hmem := hsub2 hj
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          rcases hmem with rfl | rfl | rfl
          · exact he0.mpr hj
          · exact he1.mpr hj
          · exact he2.mpr hj
      rw [← Finset.card_image_of_injOn henc_inj, Finset.image_image]
      have hcomp : (enc ∘ fun p : Bool × Bool =>
          let u := stripOf h z p.1 p.2
          let bits := fun i : Nat => xor (u.testBit i) (mix (if h - 1 ∈ z then y else x) i)
          ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j => chiFn bits j)) =
          fun p => sliceOut z3 z2 z1 z0 p.1 p.2 := by
        funext ⟨a, b⟩
        have hm : ∀ i < h + 2,
            mix (if h - 1 ∈ z then y else x) i =
              if h - 1 ∈ z then ty i else tx i := by
          intro i hi
          by_cases hz0 : h - 1 ∈ z
          · simp only [hz0, ↓reduceIte]; exact hy_mix i hi
          · simp only [hz0, ↓reduceIte]; exact hx_mix i hi
        have hu5 : (stripOf h z a b).testBit (h + 1) = b := by
          rw [stripOf_testBit, invChi]
          have hlt : h + 1 < h + 2 := by omega
          have hsub : h + 1 - (h + 1) = 0 := by omega
          simp [hlt, hsub, invChiAux]
        have hu4 : (stripOf h z a b).testBit h = a := by
          rw [stripOf_testBit, invChi]
          have hlt : h < h + 2 := by omega
          have hsub : h + 1 - h = 1 := by omega
          simp [hlt, hsub, invChiAux]
        have hu3 : (stripOf h z a b).testBit (h - 1) = xor z0 (!a && b) := by
          rw [stripOf_testBit, invChi]
          have hlt : h - 1 < h + 2 := by omega
          have hsub : h + 1 - (h - 1) = 2 := by omega
          simp [hlt, hsub, invChiAux, z0]
        have hu2 : (stripOf h z a b).testBit (h - 2) = xor z1 (!(xor z0 (!a && b)) && a) := by
          rw [stripOf_testBit, invChi]
          have hlt : h - 2 < h + 2 := by omega
          have hsub : h + 1 - (h - 2) = 3 := by omega
          have hk : h - 1 - 1 = h - 2 := by omega
          simp [hlt, hsub, invChiAux, hk, z1, z0]
        have hu1 : (stripOf h z a b).testBit (h - 3) =
            xor z2 (!(xor z1 (!(xor z0 (!a && b)) && a)) && xor z0 (!a && b)) := by
          rw [stripOf_testBit, invChi]
          have hlt : h - 3 < h + 2 := by omega
          have hsub : h + 1 - (h - 3) = 4 := by omega
          have hk1 : h - 1 - 2 = h - 3 := by omega
          have hk2 : h - 1 - 1 = h - 2 := by omega
          simp [hlt, hsub, invChiAux, hk1, hk2, z2, z1, z0]
        have hu0 : (stripOf h z a b).testBit (h - 4) =
            xor z3 (!(xor z2 (!(xor z1 (!(xor z0 (!a && b)) && a)) && xor z0 (!a && b))) &&
              xor z1 (!(xor z0 (!a && b)) && a)) := by
          rw [stripOf_testBit, invChi]
          have hlt : h - 4 < h + 2 := by omega
          have hsub : h + 1 - (h - 4) = 5 := by omega
          have hk0 : h - 1 - 3 = h - 4 := by omega
          have hk1 : h - 1 - 2 = h - 3 := by omega
          have hk2 : h - 1 - 1 = h - 2 := by omega
          simp [hlt, hsub, invChiAux, hk0, hk1, hk2, z3, z2, z1, z0]
        have hm0 : mix (if h - 1 ∈ z then y else x) (h - 4) = false := by
          rw [hm (h - 4) (by omega)]
          have : h - 4 ≠ h - 3 ∧ h - 4 ≠ h - 2 ∧ h - 4 ≠ h - 1 ∧ h - 4 ≠ h := by omega
          by_cases hz0 : h - 1 ∈ z <;> simp [hz0, tx, ty, this.1, this.2.1, this.2.2.1, this.2.2.2]
        have hm1 : mix (if h - 1 ∈ z then y else x) (h - 3) = !z0 := by
          rw [hm (h - 3) (by omega)]
          have : h - 3 ≠ h - 2 ∧ h - 3 ≠ h - 1 ∧ h - 3 ≠ h := by omega
          by_cases hz0 : h - 1 ∈ z <;> simp [hz0, tx, ty, z0, this.1, this.2.1, this.2.2]
        have hm2 : mix (if h - 1 ∈ z then y else x) (h - 2) = z0 := by
          rw [hm (h - 2) (by omega)]
          have : h - 2 ≠ h - 3 ∧ h - 2 ≠ h := by omega
          by_cases hz0 : h - 1 ∈ z <;> simp [hz0, tx, ty, z0, this.1, this.2]
        have hm3 : mix (if h - 1 ∈ z then y else x) (h - 1) = z0 := by
          rw [hm (h - 1) (by omega)]
          have : h - 1 ≠ h - 3 ∧ h - 1 ≠ h := by omega
          by_cases hz0 : h - 1 ∈ z <;> simp [hz0, tx, ty, z0, this.1, this.2]
        have hm4 : mix (if h - 1 ∈ z then y else x) h = true := by
          rw [hm h (by omega)]
          by_cases hz0 : h - 1 ∈ z <;> simp [hz0, tx, ty]
        have hm5 : mix (if h - 1 ∈ z then y else x) (h + 1) = false := by
          rw [hm (h + 1) (by omega)]
          have : h + 1 ≠ h - 3 ∧ h + 1 ≠ h - 2 ∧ h + 1 ≠ h - 1 ∧ h + 1 ≠ h := by omega
          by_cases hz0 : h - 1 ∈ z <;> simp [hz0, tx, ty, this.1, this.2.1, this.2.2.1, this.2.2.2]
        have ha1 : h - 4 + 1 = h - 3 := by omega
        have ha2 : h - 4 + 2 = h - 2 := by omega
        have hb1 : h - 2 + 1 = h - 1 := by omega
        have hb2 : h - 2 + 2 = h := by omega
        have hc1 : h - 1 + 1 = h := by omega
        have hc2 : h - 1 + 2 = h + 1 := by omega
        have hdec_filt : ∀ (k : Nat) (hk : k ∈ ({h - 4, h - 2, h - 1} : Finset Nat)) (P : Nat → Bool),
            decide (k ∈ ({h - 4, h - 2, h - 1} : Finset Nat).filter (fun j => P j = true)) = P k := by
          intro k hk P
          by_cases hP : P k = true
          · rw [hP, decide_eq_true_iff]
            exact Finset.mem_filter.mpr ⟨hk, hP⟩
          · have hPf : P k = false := by cases hpk : P k <;> simp_all
            rw [hPf, decide_eq_false_iff_not]
            intro hmem
            exact hP (Finset.mem_filter.mp hmem).2
        dsimp only [Function.comp_apply, enc, sliceOut]
        rw [hdec_filt (h - 4) (by simp), hdec_filt (h - 2) (by simp), hdec_filt (h - 1) (by simp)]
        simp only [chiFn, ha1, ha2, hb1, hb2, hc1, hc2,
          hu0, hu1, hu2, hu3, hu4, hu5, hm0, hm1, hm2, hm3, hm4, hm5]
      rw [hcomp, sliceOut_card]
      by_cases h2 : h - 2 ∈ z <;> by_cases h1 : h - 1 ∈ z <;> simp [z1, z0, h2, h1]
    rw [Finset.sum_congr rfl hfiber]
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range h).powerset)
      (fun z => h - 2 ∈ z ∧ h - 1 ∈ z)]
    have hs1 : ∑ z ∈ (Finset.range h).powerset.filter (fun z => h - 2 ∈ z ∧ h - 1 ∈ z),
        (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 3 * 2 ^ (h - 2) := by
      have hc : ∀ z ∈ (Finset.range h).powerset.filter (fun z => h - 2 ∈ z ∧ h - 1 ∈ z),
          (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 3 := by
        intro z hz
        simp only [Finset.mem_filter] at hz
        simp [hz.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hcards.1, Nat.mul_comm]
    have hs2 : ∑ z ∈ (Finset.range h).powerset.filter (fun z => ¬(h - 2 ∈ z ∧ h - 1 ∈ z)),
        (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 4 * (3 * 2 ^ (h - 2)) := by
      have hc : ∀ z ∈ (Finset.range h).powerset.filter (fun z => ¬(h - 2 ∈ z ∧ h - 1 ∈ z)),
          (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 4 := by
        intro z hz
        simp only [Finset.mem_filter] at hz
        simp [hz.2]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hcards.2, Nat.mul_comm]
    rw [hs1, hs2]
    ring
  · intro pick mask hcond
    change (strips.image (fun u =>
      let z := first u
      let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
      (z, (mask z).filter (fun j => chiFn bits j)))).card ≤ 15 * 2 ^ (h - 2)
    rw [hcount_sum]
    have hbound : ∀ z ∈ (Finset.range h).powerset,
        ((Finset.univ : Finset (Bool × Bool)).image (fun p =>
          let u := stripOf h z p.1 p.2
          let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
          (mask z).filter (fun j => chiFn bits j))).card ≤
        if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4 := by
      intro z hz
      have hz_sub : z ⊆ Finset.range h := Finset.mem_powerset.mp hz
      have hz_img : z ∈ strips.image first := by
        exact Finset.mem_image.mpr
          ⟨stripOf h z false false, Finset.mem_range.mpr (stripOf_lt h z false false),
           stripOf_first h z hz_sub false false⟩
      by_cases htop : h - 2 ∈ z ∧ h - 1 ∈ z
      · simp only [htop, ↓reduceIte]
        rcases hcond z hz_img with ⟨_, hmask_sub, hmiss⟩
        let g : Bool × Bool → Finset Nat := fun p =>
          let u := stripOf h z p.1 p.2
          let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
          (mask z).filter (fun j => chiFn bits j)
        let u3 := (stripOf h z false false).testBit (h - 3)
        let m3 := mix (pick z) (h - 3)
        let m2 := mix (pick z) (h - 2)
        let m1 := mix (pick z) (h - 1)
        let m0 := mix (pick z) h
        let mh := mix (pick z) (h + 1)
        let miss3 : Bool := decide (h - 3 ∉ mask z)
        rcases top2_collision_decide u3 m3 m2 m1 m0 mh false miss3 with ⟨p₁, p₂, hne, hcoll⟩
        have hchi_eq : ∀ j ∈ mask z,
            chiFn (fun i => xor ((stripOf h z p₁.1 p₁.2).testBit i) (mix (pick z) i)) j =
            chiFn (fun i => xor ((stripOf h z p₂.1 p₂.2).testBit i) (mix (pick z) i)) j := by
          intro j hj
          have hjlt : j < h := Finset.mem_range.mp (hmask_sub hj)
          have hsame_low : ∀ i ≤ h - 2,
              (stripOf h z p₁.1 p₁.2).testBit i = (stripOf h z p₂.1 p₂.2).testBit i := by
            intro i hi
            rw [stripOf_testBit, stripOf_testBit, invChi, invChi]
            have hlt : i < h + 2 := by omega
            simp only [hlt, ↓reduceIte]
            rw [invChiAux_const_of_top2 h hh z htop.1 htop.2 p₁.1 p₁.2 (h + 1 - i) (by omega),
              invChiAux_const_of_top2 h hh z htop.1 htop.2 p₂.1 p₂.2 (h + 1 - i) (by omega)]
          have hu2_val : ∀ p : Bool × Bool, (stripOf h z p.1 p.2).testBit (h - 2) = true := by
            intro p
            rw [stripOf_testBit, invChi]
            have hlt : h - 2 < h + 2 := by omega
            have hsub : h + 1 - (h - 2) = 3 := by omega
            have hk : h - 1 - 1 = h - 2 := by omega
            simp only [hlt, ↓reduceIte, hsub, invChiAux, Nat.sub_zero, hk,
              decide_eq_true htop.1, decide_eq_true htop.2]
            cases p.1 <;> cases p.2 <;> rfl
          have hu1_val : ∀ p : Bool × Bool,
              (stripOf h z p.1 p.2).testBit (h - 1) = xor true (!p.1 && p.2) := by
            intro p
            rw [stripOf_testBit, invChi]
            have hlt : h - 1 < h + 2 := by omega
            have hsub : h + 1 - (h - 1) = 2 := by omega
            simp only [hlt, ↓reduceIte, hsub, invChiAux, Nat.sub_zero,
              decide_eq_true htop.2]
          have hu0_val : ∀ p : Bool × Bool, (stripOf h z p.1 p.2).testBit h = p.1 := by
            intro p
            rw [stripOf_testBit, invChi]
            have hlt : h < h + 2 := by omega
            have hsub : h + 1 - h = 1 := by omega
            simp [hlt, hsub, invChiAux]
          have huh_val : ∀ p : Bool × Bool, (stripOf h z p.1 p.2).testBit (h + 1) = p.2 := by
            intro p
            rw [stripOf_testBit, invChi]
            have hlt : h + 1 < h + 2 := by omega
            have hsub : h + 1 - (h + 1) = 0 := by omega
            simp [hlt, hsub, invChiAux]
          have hu3_val : ∀ p : Bool × Bool, (stripOf h z p.1 p.2).testBit (h - 3) = u3 := by
            intro p
            rw [stripOf_testBit, invChi]
            have hlt : h - 3 < h + 2 := by omega
            simp only [hlt, ↓reduceIte]
            rw [invChiAux_const_of_top2 h hh z htop.1 htop.2 p.1 p.2 (h + 1 - (h - 3)) (by omega)]
            simp [u3, stripOf_testBit, invChi, hlt]
          by_cases hj4 : j ≤ h - 4
          · have h0 := hsame_low j (by omega)
            have h1 := hsame_low (j + 1) (by omega)
            have h2 := hsame_low (j + 2) (by omega)
            simp only [chiFn, h0, h1, h2]
          · have hcases : j = h - 3 ∨ j = h - 2 ∨ j = h - 1 := by omega
            rcases hcases with rfl | rfl | rfl
            · have hm3_false : miss3 = false := by
                simp only [miss3, decide_eq_false_iff_not, not_not]; exact hj
              simp only [hm3_false, Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hcoll
              have ha1 : h - 3 + 1 = h - 2 := by omega
              have ha2 : h - 3 + 2 = h - 1 := by omega
              simp only [chiFn, ha1, ha2, hu3_val, hu2_val, hu1_val]
              exact hcoll.1
            · have hm3_true : miss3 = true := by
                rcases hmiss with hm3 | hm2
                · simp [miss3, hm3]
                · exact absurd hj hm2
              simp only [hm3_true, ↓reduceIte, Prod.mk.injEq] at hcoll
              have hb1 : h - 2 + 1 = h - 1 := by omega
              have hb2 : h - 2 + 2 = h := by omega
              simp only [chiFn, hb1, hb2, hu2_val, hu1_val, hu0_val]
              exact hcoll.1
            · have hc1 : h - 1 + 1 = h := by omega
              have hc2 : h - 1 + 2 = h + 1 := by omega
              simp only [chiFn, hc1, hc2, hu1_val, hu0_val, huh_val]
              cases hm3 : miss3 <;> simp only [hm3, Bool.false_eq_true, ↓reduceIte,
                Prod.mk.injEq] at hcoll
              · exact hcoll.2
              · exact hcoll.2
        have hg_eq : g p₁ = g p₂ := by
          ext j
          simp only [g, Finset.mem_filter]
          constructor
          · rintro ⟨hj, hc⟩; exact ⟨hj, (hchi_eq j hj).symm.trans hc⟩
          · rintro ⟨hj, hc⟩; exact ⟨hj, (hchi_eq j hj).trans hc⟩
        have hsub_img :
            (Finset.univ : Finset (Bool × Bool)).image g ⊆
              ((Finset.univ : Finset (Bool × Bool)).erase p₂).image g := by
          intro S hS
          rcases Finset.mem_image.mp hS with ⟨p, _, rfl⟩
          by_cases hp : p = p₂
          · subst hp
            exact Finset.mem_image.mpr ⟨p₁, Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩, hg_eq⟩
          · exact Finset.mem_image.mpr ⟨p, Finset.mem_erase.mpr ⟨hp, Finset.mem_univ _⟩, rfl⟩
        calc ((Finset.univ : Finset (Bool × Bool)).image g).card
            ≤ (((Finset.univ : Finset (Bool × Bool)).erase p₂).image g).card :=
              Finset.card_le_card hsub_img
          _ ≤ ((Finset.univ : Finset (Bool × Bool)).erase p₂).card := Finset.card_image_le
          _ = 3 := by simp [Finset.card_erase_of_mem (Finset.mem_univ p₂)]
      · simp only [htop, ↓reduceIte]
        exact Finset.card_image_le.trans (by decide)
    have hle := Finset.sum_le_sum hbound
    have hrhs : ∑ z ∈ (Finset.range h).powerset, (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) =
        15 * 2 ^ (h - 2) := by
      rw [← Finset.sum_filter_add_sum_filter_not ((Finset.range h).powerset)
        (fun z => h - 2 ∈ z ∧ h - 1 ∈ z)]
      have hs1 : ∑ z ∈ (Finset.range h).powerset.filter (fun z => h - 2 ∈ z ∧ h - 1 ∈ z),
          (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 3 * 2 ^ (h - 2) := by
        have hc : ∀ z ∈ (Finset.range h).powerset.filter (fun z => h - 2 ∈ z ∧ h - 1 ∈ z),
            (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 3 := by
          intro z hz
          simp only [Finset.mem_filter] at hz
          simp [hz.2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hcards.1, Nat.mul_comm]
      have hs2 : ∑ z ∈ (Finset.range h).powerset.filter (fun z => ¬(h - 2 ∈ z ∧ h - 1 ∈ z)),
          (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 4 * (3 * 2 ^ (h - 2)) := by
        have hc : ∀ z ∈ (Finset.range h).powerset.filter (fun z => ¬(h - 2 ∈ z ∧ h - 1 ∈ z)),
            (if h - 2 ∈ z ∧ h - 1 ∈ z then 3 else 4) = 4 := by
          intro z hz
          simp only [Finset.mem_filter] at hz
          simp [hz.2]
        rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, hcards.2, Nat.mul_comm]
      rw [hs1, hs2]
      ring
    exact hle.trans_eq hrhs

end PEqualNP.Outside.L_meta_38164

theorem PEqualNP.Outside.L_meta_38164 :
∀ (h d : Nat), 4 ≤ h → 0 < d →
  let strips := Finset.range (2^(h+2))
  let limit := 2^(h+2+2*d)
  let mix := fun (x i : Nat) =>
    xor (x.testBit i) (xor (x.testBit (i+d)) (x.testBit (i+2*d)))
  let chi := fun (bits : Nat → Bool) (j : Nat) =>
    xor (bits j) (!(bits (j+1)) && bits (j+2))
  let first := fun u : Nat =>
    (Finset.range h).filter (fun j => chi (fun i => u.testBit i) j)
  let count := fun (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat) =>
    (strips.image (fun u =>
      let z := first u
      let bits := fun i : Nat => xor (u.testBit i) (mix (pick z) i)
      (z, (mask z).filter (fun j => chi bits j)))).card
  (∃ x y : Nat, x < limit ∧ y < limit ∧
    count (fun z => if h-1 ∈ z then y else x)
      (fun _ => {h-4,h-2,h-1}) = 15 * 2^(h-2)) ∧
  ∀ (pick : Finset Nat → Nat) (mask : Finset Nat → Finset Nat),
    (∀ z ∈ strips.image first, pick z < limit ∧ mask z ⊆ Finset.range h ∧
      (h-3 ∉ mask z ∨ h-2 ∉ mask z)) →
    count pick mask ≤ 15 * 2^(h-2) :=
  PEqualNP.Outside.L_meta_38164.main_proof
