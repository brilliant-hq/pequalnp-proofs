import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25717_aux

def rot {k : ℕ} (s : ℕ) (w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  w (i - (s : ZMod k))

def mix {k : ℕ} (d : ℕ) (w : ZMod k → ZMod 2) (i : ZMod k) : ZMod 2 :=
  w (i - (d : ZMod k)) + w i + w (i + (d : ZMod k))

def out {k : ℕ} (d u v : ℕ) (name c x : ZMod k → ZMod 2) (j : ZMod k) : ZMod 2 :=
  let y := mix d (rot u x + name)
  y j + (1 + y (j + 1)) * y (j + 2) + rot v x j + c j

def patch {k : ℕ} (starts : Finset (ZMod k)) (left len : ℕ) : Finset (ZMod k) :=
  starts.biUnion (fun p => (Finset.range len).image (fun t : ℕ => p - (left : ZMod k) + (t : ZMod k)))

lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

lemma zmod2_mul_one_add_self (a : ZMod 2) : (1 + a) * a = 0 := by
  fin_cases a <;> decide

lemma zmod2_two_eq_zero : (2 : ZMod 2) = 0 := by
  decide

lemma zmod2_sub_eq_add (a b : ZMod 2) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> decide

lemma out_diff {k : ℕ} (d u v : ℕ) (name c x z : ZMod k → ZMod 2) (j : ZMod k) :
    out d u v name c (x + z) j + out d u v name c x j =
      let a := mix d (rot u z)
      let y := mix d (rot u x + name)
      a j + a (j + 2) + a (j + 1) * a (j + 2) + rot v z j +
        a (j + 2) * y (j + 1) + a (j + 1) * y (j + 2) := by
  dsimp only [out]
  have hy : ∀ r, mix d (rot u (x + z) + name) r = mix d (rot u x + name) r + mix d (rot u z) r := by
    intro r
    simp only [mix, rot, Pi.add_apply]
    ring
  have hv : rot v (x + z) j = rot v x j + rot v z j := rfl
  rw [hy j, hy (j + 1), hy (j + 2), hv]
  have h2 : ∀ t : ZMod 2, t + t = 0 := zmod2_add_self
  generalize mix d (rot u x + name) j = y0
  generalize mix d (rot u x + name) (j + 1) = y1
  generalize mix d (rot u x + name) (j + 2) = y2
  generalize mix d (rot u z) j = a0
  generalize mix d (rot u z) (j + 1) = a1
  generalize mix d (rot u z) (j + 2) = a2
  generalize rot v x j = vx
  generalize rot v z j = vz
  generalize c j = cj
  have hring :
      (y0 + a0 + (1 + (y1 + a1)) * (y2 + a2) + (vx + vz) + cj) +
        (y0 + (1 + y1) * y2 + vx + cj) =
      (a0 + a2 + a1 * a2 + vz + a2 * y1 + a1 * y2) +
        2 * (y0 + y2 + y1 * y2 + vx + cj) := by
    ring
  rw [hring, zmod2_two_eq_zero, zero_mul, add_zero]

lemma out_inv_linear {k : ℕ} (d u v : ℕ) (name c z : ZMod k → ZMod 2) (j : ZMod k)
    (hinv : ∀ x, out d u v name c (x + z) j = out d u v name c x j) :
    (∀ w : ZMod k → ZMod 2,
      mix d (rot u z) (j + 2) * mix d w (j + 1) +
        mix d (rot u z) (j + 1) * mix d w (j + 2) = 0) ∧
    (mix d (rot u z) (j + 1) = 0 → mix d (rot u z) (j + 2) = 0 →
      mix d (rot u z) j + rot v z j = 0) := by
  have hzero : ∀ x,
      mix d (rot u z) j + mix d (rot u z) (j + 2) +
        mix d (rot u z) (j + 1) * mix d (rot u z) (j + 2) + rot v z j +
        mix d (rot u z) (j + 2) * mix d (rot u x + name) (j + 1) +
        mix d (rot u z) (j + 1) * mix d (rot u x + name) (j + 2) = 0 := by
    intro x
    have h := out_diff d u v name c x z j
    rw [hinv x, zmod2_add_self] at h
    exact h.symm
  constructor
  · intro w
    let x1 : ZMod k → ZMod 2 := fun i => w (i + (u : ZMod k))
    have hrot : rot u x1 = w := by
      funext i
      simp only [rot, x1, sub_add_cancel]
    have h0 := hzero 0
    have h1 := hzero x1
    have hadd : ∀ r, mix d (rot u x1 + name) r = mix d w r + mix d (rot u 0 + name) r := by
      intro r
      rw [hrot]
      have h0r : rot u (0 : ZMod k → ZMod 2) = 0 := rfl
      rw [h0r, zero_add]
      simp only [mix, Pi.add_apply]
      ring
    rw [hadd (j + 1), hadd (j + 2)] at h1
    have hsum :
        (mix d (rot u z) j + mix d (rot u z) (j + 2) +
          mix d (rot u z) (j + 1) * mix d (rot u z) (j + 2) + rot v z j +
          mix d (rot u z) (j + 2) * (mix d w (j + 1) + mix d (rot u 0 + name) (j + 1)) +
          mix d (rot u z) (j + 1) * (mix d w (j + 2) + mix d (rot u 0 + name) (j + 2))) +
        (mix d (rot u z) j + mix d (rot u z) (j + 2) +
          mix d (rot u z) (j + 1) * mix d (rot u z) (j + 2) + rot v z j +
          mix d (rot u z) (j + 2) * mix d (rot u 0 + name) (j + 1) +
          mix d (rot u z) (j + 1) * mix d (rot u 0 + name) (j + 2)) = 0 := by
      rw [h1, h0, add_zero]
    have hring :
        (mix d (rot u z) j + mix d (rot u z) (j + 2) +
          mix d (rot u z) (j + 1) * mix d (rot u z) (j + 2) + rot v z j +
          mix d (rot u z) (j + 2) * (mix d w (j + 1) + mix d (rot u 0 + name) (j + 1)) +
          mix d (rot u z) (j + 1) * (mix d w (j + 2) + mix d (rot u 0 + name) (j + 2))) +
        (mix d (rot u z) j + mix d (rot u z) (j + 2) +
          mix d (rot u z) (j + 1) * mix d (rot u z) (j + 2) + rot v z j +
          mix d (rot u z) (j + 2) * mix d (rot u 0 + name) (j + 1) +
          mix d (rot u z) (j + 1) * mix d (rot u 0 + name) (j + 2)) =
        (mix d (rot u z) (j + 2) * mix d w (j + 1) +
          mix d (rot u z) (j + 1) * mix d w (j + 2)) +
        2 * (mix d (rot u z) j + mix d (rot u z) (j + 2) +
          mix d (rot u z) (j + 1) * mix d (rot u z) (j + 2) + rot v z j +
          mix d (rot u z) (j + 2) * mix d (rot u 0 + name) (j + 1) +
          mix d (rot u z) (j + 1) * mix d (rot u 0 + name) (j + 2)) := by
      ring
    rw [hring, zmod2_two_eq_zero, zero_mul, add_zero] at hsum
    exact hsum
  · intro ha1 ha2
    have h0 := hzero 0
    rw [ha1, ha2] at h0
    simpa using h0

lemma natCast_ne_zero_of_lt {k m : ℕ} [NeZero k] (hnd : ¬ k ∣ m) :
    (m : ZMod k) ≠ 0 := by
  intro h
  exact hnd ((ZMod.natCast_eq_zero_iff m k).mp h)

lemma row_single_eqs {k : ℕ} [NeZero k] (hk1 : k ≠ 1) (hk3 : k ≠ 3)
    (row cr z : ZMod k → ZMod 2) (j : ZMod k)
    (hinv : ∀ x, out 1 1 0 row cr (x + z) j = out 1 1 0 row cr x j) :
    mix 1 (rot 1 z) (j + 1) = 0 ∧
    mix 1 (rot 1 z) (j + 2) = 0 ∧
    z (j - 2) = z (j - 1) := by
  have hk0 : k ≠ 0 := NeZero.ne k
  obtain ⟨hlin, hconst⟩ := out_inv_linear 1 1 0 row cr z j hinv
  have h1ne : (1 : ZMod k) ≠ 0 := by
    have h := natCast_ne_zero_of_lt (k := k) (m := 1) (fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      omega)
    simpa using h
  have h3ne : (3 : ZMod k) ≠ 0 := by
    have h := natCast_ne_zero_of_lt (k := k) (m := 3) (fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have : k = 2 := by omega
      subst this
      omega)
    simpa using h
  have ha12 : mix 1 (rot 1 z) (j + 1) = 0 ∧ mix 1 (rot 1 z) (j + 2) = 0 := by
    by_cases hk2 : k = 2
    · subst hk2
      have he1 := hlin (Pi.single (j + 1) 1)
      have he0 := hlin (Pi.single j 1)
      have hm1 : mix 1 (Pi.single (j + 1) 1 : ZMod 2 → ZMod 2) (j + 1) = 1 :=
        (show ∀ x : ZMod 2, mix 1 (Pi.single (x + 1) 1 : ZMod 2 → ZMod 2) (x + 1) = 1 by decide) j
      have hm2 : mix 1 (Pi.single (j + 1) 1 : ZMod 2 → ZMod 2) (j + 2) = 0 :=
        (show ∀ x : ZMod 2, mix 1 (Pi.single (x + 1) 1 : ZMod 2 → ZMod 2) (x + 2) = 0 by decide) j
      have hm3 : mix 1 (Pi.single j 1 : ZMod 2 → ZMod 2) (j + 1) = 0 :=
        (show ∀ x : ZMod 2, mix 1 (Pi.single x 1 : ZMod 2 → ZMod 2) (x + 1) = 0 by decide) j
      have hm4 : mix 1 (Pi.single j 1 : ZMod 2 → ZMod 2) (j + 2) = 1 :=
        (show ∀ x : ZMod 2, mix 1 (Pi.single x 1 : ZMod 2 → ZMod 2) (x + 2) = 1 by decide) j
      rw [hm1, hm2, mul_one, mul_zero, add_zero] at he1
      rw [hm3, hm4, mul_zero, mul_one, zero_add] at he0
      exact ⟨he0, he1⟩
    · have h2ne : (2 : ZMod k) ≠ 0 := by
        have h := natCast_ne_zero_of_lt (k := k) (m := 2) (fun hd => by
          have hle := Nat.le_of_dvd (by omega) hd
          omega)
        simpa using h
      have hne01 : j + 1 ≠ j := fun h => h1ne (by linear_combination h)
      have hne02 : j + 2 ≠ j := fun h => h2ne (by linear_combination h)
      have hne03 : j + 3 ≠ j := fun h => h3ne (by linear_combination h)
      have hne13 : j + 1 ≠ j + 3 := fun h => h2ne (by linear_combination -h)
      have hne23 : j + 2 ≠ j + 3 := fun h => h1ne (by linear_combination -h)
      have he0 := hlin (Pi.single j 1)
      have he3 := hlin (Pi.single (j + 3) 1)
      have hm1 : mix 1 (Pi.single j 1 : ZMod k → ZMod 2) (j + 1) = 1 := by
        simp only [mix, Nat.cast_one]
        have s1 : j + 1 - 1 = j := by ring
        have s2 : j + 1 + 1 = j + 2 := by ring
        rw [s1, s2, Pi.single_eq_same, Pi.single_eq_of_ne hne01, Pi.single_eq_of_ne hne02]
        ring
      have hm2 : mix 1 (Pi.single j 1 : ZMod k → ZMod 2) (j + 2) = 0 := by
        simp only [mix, Nat.cast_one]
        have s1 : j + 2 - 1 = j + 1 := by ring
        have s2 : j + 2 + 1 = j + 3 := by ring
        rw [s1, s2, Pi.single_eq_of_ne hne01, Pi.single_eq_of_ne hne02, Pi.single_eq_of_ne hne03]
        ring
      have hm3 : mix 1 (Pi.single (j + 3) 1 : ZMod k → ZMod 2) (j + 1) = 0 := by
        simp only [mix, Nat.cast_one]
        have s1 : j + 1 - 1 = j := by ring
        have s2 : j + 1 + 1 = j + 2 := by ring
        rw [s1, s2, Pi.single_eq_of_ne hne03.symm, Pi.single_eq_of_ne hne13, Pi.single_eq_of_ne hne23]
        ring
      have hm4 : mix 1 (Pi.single (j + 3) 1 : ZMod k → ZMod 2) (j + 2) = 1 := by
        simp only [mix, Nat.cast_one]
        have s1 : j + 2 - 1 = j + 1 := by ring
        have s2 : j + 2 + 1 = j + 3 := by ring
        rw [s1, s2, Pi.single_eq_of_ne hne13, Pi.single_eq_of_ne hne23, Pi.single_eq_same]
        ring
      rw [hm1, hm2, mul_one, mul_zero, add_zero] at he0
      rw [hm3, hm4, mul_zero, mul_one, zero_add] at he3
      exact ⟨he3, he0⟩
  refine ⟨ha12.1, ha12.2, ?_⟩
  have hc := hconst ha12.1 ha12.2
  simp only [mix, rot, Nat.cast_one, Nat.cast_zero, sub_zero] at hc
  have s1 : j - 1 - 1 = j - 2 := by ring
  have s2 : j + 1 - 1 = j := by ring
  rw [s1, s2] at hc
  have hring : z (j - 2) + z (j - 1) + z j + z j = z (j - 2) + z (j - 1) + (z j + z j) := by ring
  rw [hring, zmod2_add_self, add_zero] at hc
  calc z (j - 2) = z (j - 2) + (z (j - 1) + z (j - 1)) := by rw [zmod2_add_self, add_zero]
    _ = (z (j - 2) + z (j - 1)) + z (j - 1) := by ring
    _ = 0 + z (j - 1) := by rw [hc]
    _ = z (j - 1) := zero_add _

lemma col_single_eqs {k : ℕ} [NeZero k] (hk1 : k ≠ 1) (hk3 : k ≠ 3)
    (col cc z : ZMod k → ZMod 2) (j : ZMod k)
    (hinv : ∀ x, out 2 3 4 col cc (x + z) j = out 2 3 4 col cc x j) :
    mix 2 (rot 3 z) (j + 1) = 0 ∧
    mix 2 (rot 3 z) (j + 2) = 0 ∧
    mix 2 (rot 3 z) j = z (j - 4) := by
  have hk0 : k ≠ 0 := NeZero.ne k
  obtain ⟨hlin, hconst⟩ := out_inv_linear 2 3 4 col cc z j hinv
  have h1ne : (1 : ZMod k) ≠ 0 := by
    have h := natCast_ne_zero_of_lt (k := k) (m := 1) (fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      omega)
    simpa using h
  have h3ne : (3 : ZMod k) ≠ 0 := by
    have h := natCast_ne_zero_of_lt (k := k) (m := 3) (fun hd => by
      have hle := Nat.le_of_dvd (by omega) hd
      have : k = 2 := by omega
      subst this
      omega)
    simpa using h
  have he1 := hlin (Pi.single (j + 1) 1)
  have he2 := hlin (Pi.single (j + 2) 1)
  have hpair_same : ∀ r : ZMod k,
      (Pi.single r (1 : ZMod 2) : ZMod k → ZMod 2) (r - 2) +
        (Pi.single r (1 : ZMod 2) : ZMod k → ZMod 2) (r + 2) = 0 := by
    intro r
    have hiff : r - 2 = r ↔ r + 2 = r := by
      constructor <;> intro h
      · linear_combination -h
      · linear_combination -h
    by_cases h : r - 2 = r
    · rw [h, hiff.mp h, Pi.single_eq_same]
      exact zmod2_add_self 1
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (mt hiff.mpr h), add_zero]
  have hm1 : mix 2 (Pi.single (j + 1) 1 : ZMod k → ZMod 2) (j + 1) = 1 := by
    simp only [mix, Nat.cast_ofNat]
    have hre : (Pi.single (j + 1) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 1 - 2) +
        (Pi.single (j + 1) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 1) +
        (Pi.single (j + 1) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 1 + 2) =
        ((Pi.single (j + 1) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 1 - 2) +
        (Pi.single (j + 1) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 1 + 2)) +
        (Pi.single (j + 1) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 1) := by ring
    rw [hre, hpair_same (j + 1), zero_add, Pi.single_eq_same]
  have hm2 : mix 2 (Pi.single (j + 1) 1 : ZMod k → ZMod 2) (j + 2) = 0 := by
    simp only [mix, Nat.cast_ofNat]
    have s1 : j + 2 - 2 ≠ j + 1 := fun h => h1ne (by linear_combination -h)
    have s2 : j + 2 ≠ j + 1 := fun h => h1ne (by linear_combination h)
    have s3 : j + 2 + 2 ≠ j + 1 := fun h => h3ne (by linear_combination h)
    rw [Pi.single_eq_of_ne s1, Pi.single_eq_of_ne s2, Pi.single_eq_of_ne s3]
    ring
  have hm3 : mix 2 (Pi.single (j + 2) 1 : ZMod k → ZMod 2) (j + 1) = 0 := by
    simp only [mix, Nat.cast_ofNat]
    have s1 : j + 1 - 2 ≠ j + 2 := fun h => h3ne (by linear_combination -h)
    have s2 : j + 1 ≠ j + 2 := fun h => h1ne (by linear_combination -h)
    have s3 : j + 1 + 2 ≠ j + 2 := fun h => h1ne (by linear_combination h)
    rw [Pi.single_eq_of_ne s1, Pi.single_eq_of_ne s2, Pi.single_eq_of_ne s3]
    ring
  have hm4 : mix 2 (Pi.single (j + 2) 1 : ZMod k → ZMod 2) (j + 2) = 1 := by
    simp only [mix, Nat.cast_ofNat]
    have hre : (Pi.single (j + 2) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 2 - 2) +
        (Pi.single (j + 2) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 2) +
        (Pi.single (j + 2) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 2 + 2) =
        ((Pi.single (j + 2) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 2 - 2) +
        (Pi.single (j + 2) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 2 + 2)) +
        (Pi.single (j + 2) (1 : ZMod 2) : ZMod k → ZMod 2) (j + 2) := by ring
    rw [hre, hpair_same (j + 2), zero_add, Pi.single_eq_same]
  rw [hm1, hm2, mul_one, mul_zero, add_zero] at he1
  rw [hm3, hm4, mul_zero, mul_one, zero_add] at he2
  refine ⟨he2, he1, ?_⟩
  have hc := hconst he2 he1
  simp only [rot, Nat.cast_ofNat] at hc
  calc mix 2 (rot 3 z) j
      = mix 2 (rot 3 z) j + (z (j - 4) + z (j - 4)) := by rw [zmod2_add_self, add_zero]
    _ = (mix 2 (rot 3 z) j + z (j - 4)) + z (j - 4) := by ring
    _ = 0 + z (j - 4) := by rw [hc]
    _ = z (j - 4) := zero_add _

lemma row_block_zero {k : ℕ} [NeZero k] (hk1 : k ≠ 1) (hk3 : k ≠ 3)
    (row cr z : ZMod k → ZMod 2) (p : ZMod k)
    (hinv : ∀ t ∈ Finset.range 3, ∀ x,
      out 1 1 0 row cr (x + z) (p - (0 : ℕ) + (t : ℕ)) =
      out 1 1 0 row cr x (p - (0 : ℕ) + (t : ℕ))) :
    ∀ t ∈ Finset.range 7, z (p - (2 : ℕ) + (t : ℕ)) = 0 := by
  have h0 : ∀ x, out 1 1 0 row cr (x + z) p = out 1 1 0 row cr x p := by
    intro x
    have := hinv 0 (by decide) x
    simpa using this
  have h1 : ∀ x, out 1 1 0 row cr (x + z) (p + 1) = out 1 1 0 row cr x (p + 1) := by
    intro x
    have := hinv 1 (by decide) x
    simpa using this
  have h2 : ∀ x, out 1 1 0 row cr (x + z) (p + 2) = out 1 1 0 row cr x (p + 2) := by
    intro x
    have := hinv 2 (by decide) x
    simpa using this
  obtain ⟨ha1, ha2, heq0⟩ := row_single_eqs hk1 hk3 row cr z p h0
  obtain ⟨_, ha3, heq1⟩ := row_single_eqs hk1 hk3 row cr z (p + 1) h1
  obtain ⟨_, ha4, heq2⟩ := row_single_eqs hk1 hk3 row cr z (p + 2) h2
  have ha_eval : ∀ r : ZMod k, mix 1 (rot 1 z) r = z (r - 2) + z (r - 1) + z r := by
    intro r
    simp only [mix, rot, Nat.cast_one]
    have s1 : r - 1 - 1 = r - 2 := by ring
    have s2 : r + 1 - 1 = r := by ring
    rw [s1, s2]
  have e0 : z (p - 2) = z (p - 1) := heq0
  have e1 : z (p - 1) = z p := by
    have s1 : p + 1 - 2 = p - 1 := by ring
    have s2 : p + 1 - 1 = p := by ring
    rw [s1, s2] at heq1
    exact heq1
  have e2 : z p = z (p + 1) := by
    have s1 : p + 2 - 2 = p := by ring
    have s2 : p + 2 - 1 = p + 1 := by ring
    rw [s1, s2] at heq2
    exact heq2
  have zp : z p = 0 := by
    rw [ha_eval] at ha1
    have s1 : p + 1 - 2 = p - 1 := by ring
    have s2 : p + 1 - 1 = p := by ring
    rw [s1, s2, e1, ← e2] at ha1
    have h3 : z p + z p + z p = z p := by
      rw [zmod2_add_self, zero_add]
    rw [h3] at ha1
    exact ha1
  have zm1 : z (p - 1) = 0 := e1.trans zp
  have zm2 : z (p - 2) = 0 := e0.trans zm1
  have zp1 : z (p + 1) = 0 := e2.symm.trans zp
  have zp2 : z (p + 2) = 0 := by
    rw [ha_eval] at ha2
    have s1 : p + 2 - 2 = p := by ring
    have s2 : p + 2 - 1 = p + 1 := by ring
    rw [s1, s2, zp, zp1, zero_add, zero_add] at ha2
    exact ha2
  have zp3 : z (p + 3) = 0 := by
    have h := ha3
    have s0 : p + 1 + 2 = p + 3 := by ring
    rw [s0, ha_eval] at h
    have s1 : p + 3 - 2 = p + 1 := by ring
    have s2 : p + 3 - 1 = p + 2 := by ring
    rw [s1, s2, zp1, zp2, zero_add, zero_add] at h
    exact h
  have zp4 : z (p + 4) = 0 := by
    have h := ha4
    have s0 : p + 2 + 2 = p + 4 := by ring
    rw [s0, ha_eval] at h
    have s1 : p + 4 - 2 = p + 2 := by ring
    have s2 : p + 4 - 1 = p + 3 := by ring
    rw [s1, s2, zp2, zp3, zero_add, zero_add] at h
    exact h
  intro t ht
  rw [Finset.mem_range] at ht
  interval_cases t
  · simpa using zm2
  · have : p - (2 : ℕ) + (1 : ℕ) = p - 1 := by push_cast; ring
    rw [this]; exact zm1
  · have : p - (2 : ℕ) + (2 : ℕ) = p := by push_cast; ring
    rw [this]; exact zp
  · have : p - (2 : ℕ) + (3 : ℕ) = p + 1 := by push_cast; ring
    rw [this]; exact zp1
  · have : p - (2 : ℕ) + (4 : ℕ) = p + 2 := by push_cast; ring
    rw [this]; exact zp2
  · have : p - (2 : ℕ) + (5 : ℕ) = p + 3 := by push_cast; ring
    rw [this]; exact zp3
  · have : p - (2 : ℕ) + (6 : ℕ) = p + 4 := by push_cast; ring
    rw [this]; exact zp4

lemma col_block_zero {k : ℕ} [NeZero k] (hk1 : k ≠ 1) (hk3 : k ≠ 3)
    (col cc z : ZMod k → ZMod 2) (p : ZMod k)
    (hinv : ∀ t ∈ Finset.range 5, ∀ x,
      out 2 3 4 col cc (x + z) (p - (0 : ℕ) + (t : ℕ)) =
      out 2 3 4 col cc x (p - (0 : ℕ) + (t : ℕ))) :
    ∀ t ∈ Finset.range 11, z (p - (5 : ℕ) + (t : ℕ)) = 0 := by
  have h0 : ∀ x, out 2 3 4 col cc (x + z) p = out 2 3 4 col cc x p := by
    intro x; simpa using hinv 0 (by decide) x
  have h1 : ∀ x, out 2 3 4 col cc (x + z) (p + 1) = out 2 3 4 col cc x (p + 1) := by
    intro x; simpa using hinv 1 (by decide) x
  have h2 : ∀ x, out 2 3 4 col cc (x + z) (p + 2) = out 2 3 4 col cc x (p + 2) := by
    intro x; simpa using hinv 2 (by decide) x
  have h3 : ∀ x, out 2 3 4 col cc (x + z) (p + 3) = out 2 3 4 col cc x (p + 3) := by
    intro x; simpa using hinv 3 (by decide) x
  have h4 : ∀ x, out 2 3 4 col cc (x + z) (p + 4) = out 2 3 4 col cc x (p + 4) := by
    intro x; simpa using hinv 4 (by decide) x
  obtain ⟨ha1, ha2, heq0⟩ := col_single_eqs hk1 hk3 col cc z p h0
  obtain ⟨_, ha3, heq1⟩ := col_single_eqs hk1 hk3 col cc z (p + 1) h1
  obtain ⟨_, ha4, heq2⟩ := col_single_eqs hk1 hk3 col cc z (p + 2) h2
  obtain ⟨_, ha5, heq3⟩ := col_single_eqs hk1 hk3 col cc z (p + 3) h3
  obtain ⟨_, ha6, heq4⟩ := col_single_eqs hk1 hk3 col cc z (p + 4) h4
  have ha3' : mix 2 (rot 3 z) (p + 3) = 0 := by
    have s : p + 1 + 2 = p + 3 := by ring
    rwa [s] at ha3
  have ha4' : mix 2 (rot 3 z) (p + 4) = 0 := by
    have s : p + 2 + 2 = p + 4 := by ring
    rwa [s] at ha4
  have ha5' : mix 2 (rot 3 z) (p + 5) = 0 := by
    have s : p + 3 + 2 = p + 5 := by ring
    rwa [s] at ha5
  have ha6' : mix 2 (rot 3 z) (p + 6) = 0 := by
    have s : p + 4 + 2 = p + 6 := by ring
    rwa [s] at ha6
  have ha_eval : ∀ r : ZMod k, mix 2 (rot 3 z) r = z (r - 5) + z (r - 3) + z (r - 1) := by
    intro r
    simp only [mix, rot, Nat.cast_ofNat]
    have s1 : r - 2 - 3 = r - 5 := by ring
    have s2 : r + 2 - 3 = r - 1 := by ring
    rw [s1, s2]
  have zm3 : z (p - 3) = 0 := by
    have s : p + 1 - 4 = p - 3 := by ring
    rw [ha1, s] at heq1
    exact heq1.symm
  have zm2 : z (p - 2) = 0 := by
    have s : p + 2 - 4 = p - 2 := by ring
    rw [ha2, s] at heq2
    exact heq2.symm
  have zm1 : z (p - 1) = 0 := by
    have s : p + 3 - 4 = p - 1 := by ring
    rw [ha3', s] at heq3
    exact heq3.symm
  have zp : z p = 0 := by
    have s : p + 4 - 4 = p := by ring
    rw [ha4', s] at heq4
    exact heq4.symm
  have zm4 : z (p - 4) = 0 := by
    rw [ha_eval] at ha1
    have s1 : p + 1 - 5 = p - 4 := by ring
    have s2 : p + 1 - 3 = p - 2 := by ring
    have s3 : p + 1 - 1 = p := by ring
    rw [s1, s2, s3, zm2, zp, add_zero, add_zero] at ha1
    exact ha1
  have zm5 : z (p - 5) = 0 := by
    rw [ha_eval] at heq0
    rw [zm3, zm1, zm4, add_zero, add_zero] at heq0
    exact heq0
  have zp1 : z (p + 1) = 0 := by
    rw [ha_eval] at ha2
    have s1 : p + 2 - 5 = p - 3 := by ring
    have s2 : p + 2 - 3 = p - 1 := by ring
    have s3 : p + 2 - 1 = p + 1 := by ring
    rw [s1, s2, s3, zm3, zm1, zero_add, zero_add] at ha2
    exact ha2
  have zp2 : z (p + 2) = 0 := by
    rw [ha_eval] at ha3'
    have s1 : p + 3 - 5 = p - 2 := by ring
    have s2 : p + 3 - 3 = p := by ring
    have s3 : p + 3 - 1 = p + 2 := by ring
    rw [s1, s2, s3, zm2, zp, zero_add, zero_add] at ha3'
    exact ha3'
  have zp3 : z (p + 3) = 0 := by
    rw [ha_eval] at ha4'
    have s1 : p + 4 - 5 = p - 1 := by ring
    have s2 : p + 4 - 3 = p + 1 := by ring
    have s3 : p + 4 - 1 = p + 3 := by ring
    rw [s1, s2, s3, zm1, zp1, zero_add, zero_add] at ha4'
    exact ha4'
  have zp4 : z (p + 4) = 0 := by
    rw [ha_eval] at ha5'
    have s1 : p + 5 - 5 = p := by ring
    have s2 : p + 5 - 3 = p + 2 := by ring
    have s3 : p + 5 - 1 = p + 4 := by ring
    rw [s1, s2, s3, zp, zp2, zero_add, zero_add] at ha5'
    exact ha5'
  have zp5 : z (p + 5) = 0 := by
    rw [ha_eval] at ha6'
    have s1 : p + 6 - 5 = p + 1 := by ring
    have s2 : p + 6 - 3 = p + 3 := by ring
    have s3 : p + 6 - 1 = p + 5 := by ring
    rw [s1, s2, s3, zp1, zp3, zero_add, zero_add] at ha6'
    exact ha6'
  intro t ht
  rw [Finset.mem_range] at ht
  interval_cases t
  · simpa using zm5
  · have : p - (5 : ℕ) + (1 : ℕ) = p - 4 := by push_cast; ring
    rw [this]; exact zm4
  · have : p - (5 : ℕ) + (2 : ℕ) = p - 3 := by push_cast; ring
    rw [this]; exact zm3
  · have : p - (5 : ℕ) + (3 : ℕ) = p - 2 := by push_cast; ring
    rw [this]; exact zm2
  · have : p - (5 : ℕ) + (4 : ℕ) = p - 1 := by push_cast; ring
    rw [this]; exact zm1
  · have : p - (5 : ℕ) + (5 : ℕ) = p := by push_cast; ring
    rw [this]; exact zp
  · have : p - (5 : ℕ) + (6 : ℕ) = p + 1 := by push_cast; ring
    rw [this]; exact zp1
  · have : p - (5 : ℕ) + (7 : ℕ) = p + 2 := by push_cast; ring
    rw [this]; exact zp2
  · have : p - (5 : ℕ) + (8 : ℕ) = p + 3 := by push_cast; ring
    rw [this]; exact zp3
  · have : p - (5 : ℕ) + (9 : ℕ) = p + 4 := by push_cast; ring
    rw [this]; exact zp4
  · have : p - (5 : ℕ) + (10 : ℕ) = p + 5 := by push_cast; ring
    rw [this]; exact zp5

lemma row_depends_on_patch {k : ℕ} (row cr x x' : ZMod k → ZMod 2) (R : Finset (ZMod k))
    (hagree : ∀ s ∈ patch R 2 7, x' s = x s) :
    ∀ j ∈ patch R 0 3, out 1 1 0 row cr x' j = out 1 1 0 row cr x j := by
  intro j hj
  simp only [patch, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hj
  obtain ⟨p, hpR, t, ht, rfl⟩ := hj
  have hmem : ∀ m : ℕ, m < 7 → x' (p - (2 : ℕ) + (m : ℕ)) = x (p - (2 : ℕ) + (m : ℕ)) := by
    intro m hm
    exact hagree _ (Finset.mem_biUnion.mpr ⟨p, hpR, Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩⟩)
  have heq : ∀ off : ℕ, off ≤ 4 →
      x' (p - (0 : ℕ) + (t : ℕ) - (2 : ℕ) + (off : ℕ)) =
      x (p - (0 : ℕ) + (t : ℕ) - (2 : ℕ) + (off : ℕ)) := by
    intro off hoff
    have hcast : p - (0 : ℕ) + (t : ℕ) - (2 : ℕ) + (off : ℕ) = p - (2 : ℕ) + ((t + off : ℕ) : ZMod k) := by
      push_cast; ring
    rw [hcast]
    exact hmem (t + off) (by omega)
  have hmix : ∀ s : ℕ, s ≤ 2 →
      mix 1 (rot 1 x' + row) (p - (0 : ℕ) + (t : ℕ) + (s : ℕ)) =
      mix 1 (rot 1 x + row) (p - (0 : ℕ) + (t : ℕ) + (s : ℕ)) := by
    intro s hs
    simp only [mix, rot, Pi.add_apply, Nat.cast_one]
    have e1 : p - (0 : ℕ) + (t : ℕ) + (s : ℕ) - 1 - 1 = p - (0 : ℕ) + (t : ℕ) - (2 : ℕ) + (s : ℕ) := by
      push_cast; ring
    have e2 : p - (0 : ℕ) + (t : ℕ) + (s : ℕ) - 1 = p - (0 : ℕ) + (t : ℕ) - (2 : ℕ) + ((s + 1 : ℕ) : ZMod k) := by
      push_cast; ring
    have e3 : p - (0 : ℕ) + (t : ℕ) + (s : ℕ) + 1 - 1 = p - (0 : ℕ) + (t : ℕ) - (2 : ℕ) + ((s + 2 : ℕ) : ZMod k) := by
      push_cast; ring
    rw [e1, e2, e3, heq s (by omega), heq (s + 1) (by omega), heq (s + 2) (by omega)]
  have hrot0 : rot 0 x' (p - (0 : ℕ) + (t : ℕ)) = rot 0 x (p - (0 : ℕ) + (t : ℕ)) := by
    simp only [rot, Nat.cast_zero, sub_zero]
    have e0 : p + (t : ℕ) = p - (0 : ℕ) + (t : ℕ) - (2 : ℕ) + (2 : ℕ) := by push_cast; ring
    rw [e0]
    exact heq 2 (by omega)
  dsimp only [out]
  have hm0 := hmix 0 (by omega)
  have hm1 := hmix 1 (by omega)
  have hm2 := hmix 2 (by omega)
  simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at hm0 hm1 hm2 ⊢
  rw [hm0, hm1, hm2]
  simp only [Nat.cast_zero] at hrot0
  rw [hrot0]

lemma col_depends_on_patch {k : ℕ} (col cc x x' : ZMod k → ZMod 2) (C : Finset (ZMod k))
    (hagree : ∀ s ∈ patch C 5 11, x' s = x s) :
    ∀ i ∈ patch C 0 5, out 2 3 4 col cc x' i = out 2 3 4 col cc x i := by
  intro i hi
  simp only [patch, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range] at hi
  obtain ⟨p, hpC, t, ht, rfl⟩ := hi
  have hmem : ∀ m : ℕ, m < 11 → x' (p - (5 : ℕ) + (m : ℕ)) = x (p - (5 : ℕ) + (m : ℕ)) := by
    intro m hm
    exact hagree _ (Finset.mem_biUnion.mpr ⟨p, hpC, Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, rfl⟩⟩)
  have heq : ∀ off : ℕ, off ≤ 6 →
      x' (p - (0 : ℕ) + (t : ℕ) - (5 : ℕ) + (off : ℕ)) =
      x (p - (0 : ℕ) + (t : ℕ) - (5 : ℕ) + (off : ℕ)) := by
    intro off hoff
    have hcast : p - (0 : ℕ) + (t : ℕ) - (5 : ℕ) + (off : ℕ) = p - (5 : ℕ) + ((t + off : ℕ) : ZMod k) := by
      push_cast; ring
    rw [hcast]
    exact hmem (t + off) (by omega)
  have hmix : ∀ s : ℕ, s ≤ 2 →
      mix 2 (rot 3 x' + col) (p - (0 : ℕ) + (t : ℕ) + (s : ℕ)) =
      mix 2 (rot 3 x + col) (p - (0 : ℕ) + (t : ℕ) + (s : ℕ)) := by
    intro s hs
    simp only [mix, rot, Pi.add_apply, Nat.cast_ofNat]
    have e1 : p - (0 : ℕ) + (t : ℕ) + (s : ℕ) - 2 - 3 = p - (0 : ℕ) + (t : ℕ) - (5 : ℕ) + (s : ℕ) := by
      push_cast; ring
    have e2 : p - (0 : ℕ) + (t : ℕ) + (s : ℕ) - 3 = p - (0 : ℕ) + (t : ℕ) - (5 : ℕ) + ((s + 2 : ℕ) : ZMod k) := by
      push_cast; ring
    have e3 : p - (0 : ℕ) + (t : ℕ) + (s : ℕ) + 2 - 3 = p - (0 : ℕ) + (t : ℕ) - (5 : ℕ) + ((s + 4 : ℕ) : ZMod k) := by
      push_cast; ring
    rw [e1, e2, e3, heq s (by omega), heq (s + 2) (by omega), heq (s + 4) (by omega)]
  have hrot4 : rot 4 x' (p - (0 : ℕ) + (t : ℕ)) = rot 4 x (p - (0 : ℕ) + (t : ℕ)) := by
    simp only [rot, Nat.cast_ofNat]
    have e0 : p - (0 : ℕ) + (t : ℕ) - 4 = p - (0 : ℕ) + (t : ℕ) - (5 : ℕ) + (1 : ℕ) := by push_cast; ring
    rw [e0]
    exact heq 1 (by omega)
  dsimp only [out]
  have hm0 := hmix 0 (by omega)
  have hm1 := hmix 1 (by omega)
  have hm2 := hmix 2 (by omega)
  simp only [Nat.cast_zero, add_zero, Nat.cast_one, Nat.cast_ofNat] at hm0 hm1 hm2 ⊢
  rw [hm0, hm1, hm2]
  simp only [Nat.cast_zero] at hrot4
  rw [hrot4]

lemma card_le_mul_ker {k q : ℕ} [NeZero k] (forms : Fin q → (ZMod k → ZMod 2))
    (P : Finset (ZMod k → ZMod 2))
    (hker : ∀ z : ZMod k → ZMod 2, (∀ t : Fin q, dotProduct (forms t) z = 0) → z ∈ P) :
    2 ^ k ≤ 2 ^ q * P.card := by
  let L : (ZMod k → ZMod 2) → (Fin q → ZMod 2) := fun x t => dotProduct (forms t) x
  have hpart :
      (Finset.univ : Finset (ZMod k → ZMod 2)).card =
        ∑ y : Fin q → ZMod 2,
          ((Finset.univ : Finset (ZMod k → ZMod 2)).filter (fun x => L x = y)).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp
    · intro y1 _ y2 _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_filter] at hx1 hx2
      exact hne (hx1.2.symm.trans hx2.2)
  have hfib : ∀ y : Fin q → ZMod 2,
      ((Finset.univ : Finset (ZMod k → ZMod 2)).filter (fun x => L x = y)).card ≤ P.card := by
    intro y
    by_cases hemp : ((Finset.univ : Finset (ZMod k → ZMod 2)).filter (fun x => L x = y)) = ∅
    · rw [hemp, Finset.card_empty]
      exact Nat.zero_le _
    · obtain ⟨x0, hx0⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
      have hx0L : L x0 = y := (Finset.mem_filter.mp hx0).2
      refine Finset.card_le_card_of_injOn (fun x => x + x0) ?_ ?_
      · intro x hx
        have hxL : L x = y := (Finset.mem_filter.mp hx).2
        apply hker
        intro t
        have hadd : dotProduct (forms t) (x + x0) = dotProduct (forms t) x + dotProduct (forms t) x0 :=
          dotProduct_add _ _ _
        rw [hadd]
        have h1 : dotProduct (forms t) x = y t := congrFun hxL t
        have h2 : dotProduct (forms t) x0 = y t := congrFun hx0L t
        rw [h1, h2]
        exact zmod2_add_self _
      · intro x1 _ x2 _ heq
        funext i
        have hi : x1 i + x0 i = x2 i + x0 i := congrFun heq i
        calc x1 i = x1 i + (x0 i + x0 i) := by rw [zmod2_add_self, add_zero]
          _ = (x1 i + x0 i) + x0 i := by ring
          _ = (x2 i + x0 i) + x0 i := by rw [hi]
          _ = x2 i + (x0 i + x0 i) := by ring
          _ = x2 i := by rw [zmod2_add_self, add_zero]
  have htot : (Finset.univ : Finset (ZMod k → ZMod 2)).card = 2 ^ k := by
    rw [Finset.card_univ, Fintype.card_fun, ZMod.card, ZMod.card]
  calc 2 ^ k = (Finset.univ : Finset (ZMod k → ZMod 2)).card := htot.symm
    _ = ∑ y : Fin q → ZMod 2,
          ((Finset.univ : Finset (ZMod k → ZMod 2)).filter (fun x => L x = y)).card := hpart
    _ ≤ ∑ _y : Fin q → ZMod 2, P.card := Finset.sum_le_sum (fun y _ => hfib y)
    _ = (Finset.univ : Finset (Fin q → ZMod 2)).card * P.card := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = 2 ^ q * P.card := by
          rw [Finset.card_univ, Fintype.card_fun, ZMod.card, Fintype.card_fin]

lemma card_vanishing_on_sites {k : ℕ} [NeZero k] (sites : Finset (ZMod k)) :
    ((Finset.univ : Finset (ZMod k → ZMod 2)).filter (fun z => ∀ s ∈ sites, z s = 0)).card *
      2 ^ sites.card = 2 ^ k := by
  let P : Finset (ZMod k → ZMod 2) := Finset.univ.filter (fun z => ∀ s ∈ sites, z s = 0)
  let e : (ZMod k → ZMod 2) ≃
      ({ i : ZMod k // i ∉ sites } → ZMod 2) × ({ i : ZMod k // i ∈ sites } → ZMod 2) :=
    { toFun := fun z => (fun i => z i.1, fun i => z i.1)
      invFun := fun p i => if h : i ∈ sites then p.2 ⟨i, h⟩ else p.1 ⟨i, h⟩
      left_inv := fun z => by
        funext i
        by_cases h : i ∈ sites <;> simp [h]
      right_inv := fun p => by
        refine Prod.ext ?_ ?_
        · funext i; simp [i.2]
        · funext i; simp [i.2] }
  have hP : P.card = Fintype.card ({ i : ZMod k // i ∉ sites } → ZMod 2) := by
    trans (Finset.univ : Finset ({ i : ZMod k // i ∉ sites } → ZMod 2)).card
    · refine Finset.card_bij (t := (Finset.univ : Finset ({ i : ZMod k // i ∉ sites } → ZMod 2)))
        (fun z _ => (e z).1) (fun _ _ => Finset.mem_univ _) ?_ ?_
      · intro z1 hz1 z2 hz2 heq
        have h1 : (e z1).2 = 0 := by
          funext i
          exact (Finset.mem_filter.mp hz1).2 i.1 i.2
        have h2 : (e z2).2 = 0 := by
          funext i
          exact (Finset.mem_filter.mp hz2).2 i.1 i.2
        exact e.injective (Prod.ext heq (h1.trans h2.symm))
      · intro g _
        refine ⟨e.symm (g, 0), ?_, ?_⟩
        · simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
          intro s hs
          have h := congrFun (congrArg Prod.snd (e.apply_symm_apply (g, 0))) ⟨s, hs⟩
          exact h
        · exact congrArg Prod.fst (e.apply_symm_apply (g, 0))
    · simp
  have htot := Fintype.card_congr e
  rw [Fintype.card_fun, ZMod.card, ZMod.card, Fintype.card_prod, Fintype.card_fun, ZMod.card,
    Fintype.card_fun, ZMod.card, Fintype.card_coe] at htot
  rw [hP, Fintype.card_fun, ZMod.card]
  exact htot.symm

lemma zmod3_cases (j : ZMod 3) : j = 0 ∨ j = 1 ∨ j = 2 := by
  revert j; decide

lemma k3_mix1 (w : ZMod 3 → ZMod 2) (j : ZMod 3) :
    mix 1 w j = w 0 + w 1 + w 2 := by
  simp only [mix, Nat.cast_one]
  rcases zmod3_cases j with rfl | rfl | rfl
  · rw [show (0 : ZMod 3) - 1 = 2 by decide, show (0 : ZMod 3) + 1 = 1 by decide]; ring
  · rw [show (1 : ZMod 3) - 1 = 0 by decide, show (1 : ZMod 3) + 1 = 2 by decide]
  · rw [show (2 : ZMod 3) - 1 = 1 by decide, show (2 : ZMod 3) + 1 = 0 by decide]; ring

lemma k3_mix2 (w : ZMod 3 → ZMod 2) (j : ZMod 3) :
    mix 2 w j = w 0 + w 1 + w 2 := by
  simp only [mix, Nat.cast_ofNat]
  rcases zmod3_cases j with rfl | rfl | rfl
  · rw [show (0 : ZMod 3) - 2 = 1 by decide, show (0 : ZMod 3) + 2 = 2 by decide]; ring
  · rw [show (1 : ZMod 3) - 2 = 2 by decide, show (1 : ZMod 3) + 2 = 0 by decide]; ring
  · rw [show (2 : ZMod 3) - 2 = 0 by decide, show (2 : ZMod 3) + 2 = 1 by decide]; ring

lemma k3_sum_rot (u : ℕ) (w : ZMod 3 → ZMod 2) :
    rot u w 0 + rot u w 1 + rot u w 2 = w 0 + w 1 + w 2 := by
  have h : ∀ s : ZMod 3, w (0 - s) + w (1 - s) + w (2 - s) = w 0 + w 1 + w 2 := by
    intro s
    rcases zmod3_cases s with rfl | rfl | rfl
    · rw [show (0 : ZMod 3) - 0 = 0 by decide, show (1 : ZMod 3) - 0 = 1 by decide,
          show (2 : ZMod 3) - 0 = 2 by decide]
    · rw [show (0 : ZMod 3) - 1 = 2 by decide, show (1 : ZMod 3) - 1 = 0 by decide,
          show (2 : ZMod 3) - 1 = 1 by decide]; ring
    · rw [show (0 : ZMod 3) - 2 = 1 by decide, show (1 : ZMod 3) - 2 = 2 by decide,
          show (2 : ZMod 3) - 2 = 0 by decide]; ring
  exact h (u : ZMod 3)

lemma k3_out_row (row cr x : ZMod 3 → ZMod 2) (j : ZMod 3) :
    out 1 1 0 row cr x j = (x 0 + x 1 + x 2) + (row 0 + row 1 + row 2) + x j + cr j := by
  dsimp only [out]
  rw [k3_mix1, k3_mix1, k3_mix1, zmod2_mul_one_add_self, add_zero]
  simp only [rot, Pi.add_apply, Nat.cast_zero, sub_zero]
  have hr := k3_sum_rot 1 x
  simp only [rot] at hr
  calc (x (0 - (1 : ℕ)) + row 0 + (x (1 - (1 : ℕ)) + row 1) + (x (2 - (1 : ℕ)) + row 2)) + x j + cr j
      = (x (0 - (1 : ℕ)) + x (1 - (1 : ℕ)) + x (2 - (1 : ℕ))) + (row 0 + row 1 + row 2) + x j + cr j := by ring
    _ = (x 0 + x 1 + x 2) + (row 0 + row 1 + row 2) + x j + cr j := by rw [hr]

lemma k3_out_col (col cc x : ZMod 3 → ZMod 2) (j : ZMod 3) :
    out 2 3 4 col cc x j = (x 0 + x 1 + x 2) + (col 0 + col 1 + col 2) + x (j - (4 : ℕ)) + cc j := by
  dsimp only [out]
  rw [k3_mix2, k3_mix2, k3_mix2, zmod2_mul_one_add_self, add_zero]
  simp only [rot, Pi.add_apply]
  have hr := k3_sum_rot 3 x
  simp only [rot] at hr
  calc (x (0 - (3 : ℕ)) + col 0 + (x (1 - (3 : ℕ)) + col 1) + (x (2 - (3 : ℕ)) + col 2)) + x (j - (4 : ℕ)) + cc j
      = (x (0 - (3 : ℕ)) + x (1 - (3 : ℕ)) + x (2 - (3 : ℕ))) + (col 0 + col 1 + col 2) + x (j - (4 : ℕ)) + cc j := by ring
    _ = (x 0 + x 1 + x 2) + (col 0 + col 1 + col 2) + x (j - (4 : ℕ)) + cc j := by rw [hr]

lemma k1_out_const (d u v : ℕ) (name c x : ZMod 1 → ZMod 2) (j : ZMod 1) :
    out d u v name c x j = out d u v name c 0 j := by
  dsimp only [out, mix, rot, Pi.add_apply]
  have h0 : ∀ a : ZMod 1, a = 0 := fun a => Subsingleton.elim a 0
  simp only [h0, Pi.zero_apply, zero_add]
  rw [zmod2_mul_one_add_self, zmod2_mul_one_add_self, add_zero, add_zero]
  have hring :
      (x 0 + name 0 + (x 0 + name 0) + (x 0 + name 0) + x 0 + c 0) =
      (name 0 + name 0 + name 0 + c 0) + 2 * (2 * x 0) := by ring
  rw [hring, zmod2_two_eq_zero, zero_mul, add_zero, add_zero]

lemma dot_zmod3 (u v : ZMod 3 → ZMod 2) :
    dotProduct u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp only [dotProduct]
  rw [show (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

end PEqualNP.Outside.L_meta_25717_aux

theorem PEqualNP.Outside.L_meta_25717 : (∀ (k : ℕ) [NeZero k],
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let rot := fun (s : ℕ) (w : V) (i : I) => w (i-(s : I))
  let mix := fun (d : ℕ) (w : V) (i : I) => w (i-(d : I))+w i+w (i+(d : I))
  let out := fun (d u v : ℕ) (name c x : V) (j : I) =>
    let y := mix d (rot u x + name)
    y j + (1+y (j+1))*y (j+2) + rot v x j + c j
  let patch := fun (starts : Finset I) (left len : ℕ) =>
    starts.biUnion (fun p => (Finset.range len).image (fun t : ℕ => p-(left : I)+(t : I)))
  ∀ (row col cr cc : V) (R C : Finset I),
    let S := patch R 0 3
    let T := patch C 0 5
    let sites := patch R 2 7 ∪ patch C 5 11
    let need := if sites = ∅ ∨ k = 1 then 0 else if k = 3 then 2 else sites.card
    ∀ q : ℕ,
      (∃ (forms : Fin q → V) (decode : (Fin q → B) → V × V),
        ∀ key : V,
          let ans := decode (fun t => dotProduct (forms t) key)
          (∀ j ∈ S, ans.1 j = out 1 1 0 row cr key j) ∧
          (∀ i ∈ T, ans.2 i = out 2 3 4 col cc key i)) ↔ need ≤ q) := by
  intro k _
  dsimp only
  intro row col cr cc R C q
  let I := ZMod k
  let B := ZMod 2
  let V := I → B
  let S := PEqualNP.Outside.L_meta_25717_aux.patch R 0 3
  let T := PEqualNP.Outside.L_meta_25717_aux.patch C 0 5
  let sites := PEqualNP.Outside.L_meta_25717_aux.patch R 2 7 ∪ PEqualNP.Outside.L_meta_25717_aux.patch C 5 11
  change (∃ (forms : Fin q → V) (decode : (Fin q → B) → V × V),
      ∀ key : V,
        let ans := decode (fun t => dotProduct (forms t) key)
        (∀ j ∈ S, ans.1 j = PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr key j) ∧
        (∀ i ∈ T, ans.2 i = PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc key i)) ↔
      (if sites = ∅ ∨ k = 1 then 0 else if k = 3 then 2 else sites.card) ≤ q
  by_cases htriv : sites = ∅ ∨ k = 1
  · simp only [htriv, ↓reduceIte]
    constructor
    · intro _; exact Nat.zero_le _
    · intro _
      rcases htriv with hemp | hk1
      · refine ⟨fun _ _ => 0, fun _ => (0, 0), fun key => ⟨?_, ?_⟩⟩
        · intro j hj
          have hR : R = ∅ := by
            by_contra hne
            obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            have hmem : p - (2 : ℕ) + (0 : ℕ) ∈ sites :=
              Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨0, by decide, rfl⟩⟩)
            rw [hemp] at hmem
            exact Finset.notMem_empty _ hmem
          simp only [S, PEqualNP.Outside.L_meta_25717_aux.patch, hR, Finset.biUnion_empty] at hj
          exact absurd hj (Finset.notMem_empty _)
        · intro i hi
          have hC : C = ∅ := by
            by_contra hne
            obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            have hmem : p - (5 : ℕ) + (0 : ℕ) ∈ sites :=
              Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨0, by decide, rfl⟩⟩)
            rw [hemp] at hmem
            exact Finset.notMem_empty _ hmem
          simp only [T, PEqualNP.Outside.L_meta_25717_aux.patch, hC, Finset.biUnion_empty] at hi
          exact absurd hi (Finset.notMem_empty _)
      · subst hk1
        refine ⟨fun _ _ => 0, fun _ => (PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr 0,
          PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc 0), fun key => ⟨?_, ?_⟩⟩
        · intro j _
          exact (PEqualNP.Outside.L_meta_25717_aux.k1_out_const 1 1 0 row cr key j).symm
        · intro i _
          exact (PEqualNP.Outside.L_meta_25717_aux.k1_out_const 2 3 4 col cc key i).symm
  · simp only [htriv, ↓reduceIte]
    push Not at htriv
    obtain ⟨hne_sites, hk1⟩ := htriv
    by_cases hk3 : k = 3
    · simp only [hk3, ↓reduceIte]
      subst hk3
      constructor
      · rintro ⟨forms, decode, hdec⟩
        have hker : ∀ z : ZMod 3 → ZMod 2,
            (∀ t : Fin q, dotProduct (forms t) z = 0) →
            z ∈ ({(fun _ => 0), (fun _ => 1)} : Finset (ZMod 3 → ZMod 2)) := by
          intro z hz
          have hsame : ∀ x : ZMod 3 → ZMod 2,
              (∀ j ∈ S, PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr (x + z) j =
                PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr x j) ∧
              (∀ i ∈ T, PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc (x + z) i =
                PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc x i) := by
            intro x
            have hdot : (fun t => dotProduct (forms t) (x + z)) = (fun t => dotProduct (forms t) x) := by
              funext t
              rw [dotProduct_add, hz t, add_zero]
            have hx := hdec x
            have hxz := hdec (x + z)
            rw [hdot] at hxz
            exact ⟨fun j hj => (hxz.1 j hj).symm.trans (hx.1 j hj),
                   fun i hi => (hxz.2 i hi).symm.trans (hx.2 i hi)⟩
          have hall_eq : ∀ j : ZMod 3, z j = z 0 + z 1 + z 2 := by
            have hRC : R.Nonempty ∨ C.Nonempty := by
              by_contra h
              push Not at h
              obtain ⟨x, hx⟩ := hne_sites
              simp [sites, PEqualNP.Outside.L_meta_25717_aux.patch, h.1, h.2] at hx
            rcases hRC with ⟨p, hp⟩ | ⟨p, hp⟩
            · have hSall : ∀ j : ZMod 3, j ∈ S := by
                intro j
                have hsub : ∃ t : ℕ, t < 3 ∧ p - (0 : ℕ) + (t : ℕ) = j := by
                  rcases PEqualNP.Outside.L_meta_25717_aux.zmod3_cases p with rfl | rfl | rfl <;>
                    rcases PEqualNP.Outside.L_meta_25717_aux.zmod3_cases j with rfl | rfl | rfl
                  · exact ⟨0, by omega, by decide⟩
                  · exact ⟨1, by omega, by decide⟩
                  · exact ⟨2, by omega, by decide⟩
                  · exact ⟨2, by omega, by decide⟩
                  · exact ⟨0, by omega, by decide⟩
                  · exact ⟨1, by omega, by decide⟩
                  · exact ⟨1, by omega, by decide⟩
                  · exact ⟨2, by omega, by decide⟩
                  · exact ⟨0, by omega, by decide⟩
                obtain ⟨t, ht, htj⟩ := hsub
                exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, htj⟩⟩
              intro j
              have hj := (hsame 0).1 j (hSall j)
              rw [zero_add, PEqualNP.Outside.L_meta_25717_aux.k3_out_row,
                  PEqualNP.Outside.L_meta_25717_aux.k3_out_row] at hj
              simp only [Pi.zero_apply, add_zero, zero_add] at hj
              have hcancel : (z 0 + z 1 + z 2) + z j = 0 := by
                have hadd := congrArg (fun a => a + ((row 0 + row 1 + row 2) + cr j)) hj
                have hl : (z 0 + z 1 + z 2) + (row 0 + row 1 + row 2) + z j + cr j +
                    (row 0 + row 1 + row 2 + cr j) =
                    (z 0 + z 1 + z 2) + z j + 2 * (row 0 + row 1 + row 2 + cr j) := by ring
                have hr : row 0 + row 1 + row 2 + cr j + (row 0 + row 1 + row 2 + cr j) =
                    2 * (row 0 + row 1 + row 2 + cr j) := by ring
                rw [hl, hr, PEqualNP.Outside.L_meta_25717_aux.zmod2_two_eq_zero, zero_mul, add_zero] at hadd
                exact hadd
              calc z j = ((z 0 + z 1 + z 2) + z j) + (z 0 + z 1 + z 2) := by
                    have : ((z 0 + z 1 + z 2) + z j) + (z 0 + z 1 + z 2) =
                        z j + 2 * (z 0 + z 1 + z 2) := by ring
                    rw [this, PEqualNP.Outside.L_meta_25717_aux.zmod2_two_eq_zero, zero_mul, add_zero]
                _ = 0 + (z 0 + z 1 + z 2) := by rw [hcancel]
                _ = z 0 + z 1 + z 2 := zero_add _
            · have hTall : ∀ j : ZMod 3, j ∈ T := by
                intro j
                have hsub : ∃ t : ℕ, t < 5 ∧ p - (0 : ℕ) + (t : ℕ) = j := by
                  rcases PEqualNP.Outside.L_meta_25717_aux.zmod3_cases p with rfl | rfl | rfl <;>
                    rcases PEqualNP.Outside.L_meta_25717_aux.zmod3_cases j with rfl | rfl | rfl
                  · exact ⟨0, by omega, by decide⟩
                  · exact ⟨1, by omega, by decide⟩
                  · exact ⟨2, by omega, by decide⟩
                  · exact ⟨2, by omega, by decide⟩
                  · exact ⟨0, by omega, by decide⟩
                  · exact ⟨1, by omega, by decide⟩
                  · exact ⟨1, by omega, by decide⟩
                  · exact ⟨2, by omega, by decide⟩
                  · exact ⟨0, by omega, by decide⟩
                obtain ⟨t, ht, htj⟩ := hsub
                exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_image.mpr ⟨t, Finset.mem_range.mpr ht, htj⟩⟩
              intro j
              have hj := (hsame 0).2 (j + (4 : ℕ)) (hTall (j + (4 : ℕ)))
              rw [zero_add, PEqualNP.Outside.L_meta_25717_aux.k3_out_col,
                  PEqualNP.Outside.L_meta_25717_aux.k3_out_col, add_sub_cancel_right] at hj
              simp only [Pi.zero_apply, add_zero, zero_add] at hj
              have hcancel : (z 0 + z 1 + z 2) + z j = 0 := by
                have hadd := congrArg (fun a => a + ((col 0 + col 1 + col 2) + cc (j + (4 : ℕ)))) hj
                have hl : (z 0 + z 1 + z 2) + (col 0 + col 1 + col 2) + z j + cc (j + (4 : ℕ)) +
                    (col 0 + col 1 + col 2 + cc (j + (4 : ℕ))) =
                    (z 0 + z 1 + z 2) + z j + 2 * (col 0 + col 1 + col 2 + cc (j + (4 : ℕ))) := by ring
                have hr : col 0 + col 1 + col 2 + cc (j + (4 : ℕ)) +
                    (col 0 + col 1 + col 2 + cc (j + (4 : ℕ))) =
                    2 * (col 0 + col 1 + col 2 + cc (j + (4 : ℕ))) := by ring
                rw [hl, hr, PEqualNP.Outside.L_meta_25717_aux.zmod2_two_eq_zero, zero_mul, add_zero] at hadd
                exact hadd
              calc z j = ((z 0 + z 1 + z 2) + z j) + (z 0 + z 1 + z 2) := by
                    have : ((z 0 + z 1 + z 2) + z j) + (z 0 + z 1 + z 2) =
                        z j + 2 * (z 0 + z 1 + z 2) := by ring
                    rw [this, PEqualNP.Outside.L_meta_25717_aux.zmod2_two_eq_zero, zero_mul, add_zero]
                _ = 0 + (z 0 + z 1 + z 2) := by rw [hcancel]
                _ = z 0 + z 1 + z 2 := zero_add _
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 by decide) (z 0 + z 1 + z 2) with hb | hb
          · left; funext j; rw [hall_eq j, hb]
          · right; funext j; rw [hall_eq j, hb]
        have hcard := PEqualNP.Outside.L_meta_25717_aux.card_le_mul_ker forms
          ({(fun _ => 0), (fun _ => 1)} : Finset (ZMod 3 → ZMod 2)) hker
        have hP2 : ({(fun _ => 0), (fun _ => 1)} : Finset (ZMod 3 → ZMod 2)).card ≤ 2 :=
          Finset.card_le_two
        have hpow : 2 ^ 3 ≤ 2 ^ (q + 1) := by
          calc 2 ^ 3 ≤ 2 ^ q * ({(fun _ => 0), (fun _ => 1)} : Finset (ZMod 3 → ZMod 2)).card := hcard
            _ ≤ 2 ^ q * 2 := Nat.mul_le_mul_left _ hP2
            _ = 2 ^ (q + 1) := (pow_succ _ _).symm
        have hle : 3 ≤ q + 1 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
        omega
      · intro hq
        let f0 : ZMod 3 → ZMod 2 := fun i => if i = 0 ∨ i = 1 then 1 else 0
        let f1 : ZMod 3 → ZMod 2 := fun i => if i = 0 ∨ i = 2 then 1 else 0
        let forms : Fin q → (ZMod 3 → ZMod 2) := fun t =>
          if t.1 = 0 then f0 else if t.1 = 1 then f1 else 0
        let recKey : (Fin q → ZMod 2) → (ZMod 3 → ZMod 2) := fun y i =>
          if i = 0 then 0 else if i = 1 then y ⟨0, by omega⟩ else y ⟨1, by omega⟩
        let decode : (Fin q → ZMod 2) → (ZMod 3 → ZMod 2) × (ZMod 3 → ZMod 2) := fun y =>
          (PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr (recKey y),
           PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc (recKey y))
        refine ⟨forms, decode, fun key => ?_⟩
        have hrec : ∀ i : ZMod 3, recKey (fun t => dotProduct (forms t) key) i = key i + key 0 := by
          intro i
          have hd0 : dotProduct (forms ⟨0, by omega⟩) key = key 0 + key 1 := by
            simp only [forms, ↓reduceIte, PEqualNP.Outside.L_meta_25717_aux.dot_zmod3, f0]
            have h20 : (2 : ZMod 3) ≠ 0 := by decide
            have h21 : (2 : ZMod 3) ≠ 1 := by decide
            simp [h20, h21]
          have hd1 : dotProduct (forms ⟨1, by omega⟩) key = key 0 + key 2 := by
            simp only [forms, PEqualNP.Outside.L_meta_25717_aux.dot_zmod3, f1]
            have h10 : (1 : ZMod 3) ≠ 0 := by decide
            have h12 : (1 : ZMod 3) ≠ 2 := by decide
            simp [h10, h12]
          rcases PEqualNP.Outside.L_meta_25717_aux.zmod3_cases i with rfl | rfl | rfl
          · simp only [recKey, ↓reduceIte]
            exact (PEqualNP.Outside.L_meta_25717_aux.zmod2_add_self (key 0)).symm
          · simp only [recKey, show (1 : ZMod 3) ≠ 0 by decide, ↓reduceIte, hd0]
            ring
          · simp only [recKey, show (2 : ZMod 3) ≠ 0 by decide, show (2 : ZMod 3) ≠ 1 by decide,
              ↓reduceIte, hd1]
            ring
        constructor
        · intro j _
          dsimp only [decode]
          rw [PEqualNP.Outside.L_meta_25717_aux.k3_out_row, PEqualNP.Outside.L_meta_25717_aux.k3_out_row,
              hrec 0, hrec 1, hrec 2, hrec j]
          have hring :
              (key 0 + key 0 + (key 1 + key 0) + (key 2 + key 0)) + (row 0 + row 1 + row 2) +
                (key j + key 0) + cr j =
              (key 0 + key 1 + key 2) + (row 0 + row 1 + row 2) + key j + cr j +
                2 * (2 * key 0) := by ring
          rw [hring, PEqualNP.Outside.L_meta_25717_aux.zmod2_two_eq_zero, zero_mul, add_zero]
        · intro i _
          dsimp only [decode]
          rw [PEqualNP.Outside.L_meta_25717_aux.k3_out_col, PEqualNP.Outside.L_meta_25717_aux.k3_out_col,
              hrec 0, hrec 1, hrec 2, hrec (i - (4 : ℕ))]
          have hring :
              (key 0 + key 0 + (key 1 + key 0) + (key 2 + key 0)) + (col 0 + col 1 + col 2) +
                (key (i - (4 : ℕ)) + key 0) + cc i =
              (key 0 + key 1 + key 2) + (col 0 + col 1 + col 2) + key (i - (4 : ℕ)) + cc i +
                2 * (2 * key 0) := by ring
          rw [hring, PEqualNP.Outside.L_meta_25717_aux.zmod2_two_eq_zero, zero_mul, add_zero]
    · simp only [hk3, ↓reduceIte]
      constructor
      · rintro ⟨forms, decode, hdec⟩
        let P : Finset V := Finset.univ.filter (fun z => ∀ s ∈ sites, z s = 0)
        have hker : ∀ z : V, (∀ t : Fin q, dotProduct (forms t) z = 0) → z ∈ P := by
          intro z hz
          simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
          have hsame : ∀ x : V,
              (∀ j ∈ S, PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr (x + z) j =
                PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr x j) ∧
              (∀ i ∈ T, PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc (x + z) i =
                PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc x i) := by
            intro x
            have hdot : (fun t => dotProduct (forms t) (x + z)) = (fun t => dotProduct (forms t) x) := by
              funext t
              rw [dotProduct_add, hz t, add_zero]
            have hx := hdec x
            have hxz := hdec (x + z)
            rw [hdot] at hxz
            exact ⟨fun j hj => (hxz.1 j hj).symm.trans (hx.1 j hj),
                   fun i hi => (hxz.2 i hi).symm.trans (hx.2 i hi)⟩
          intro s hs
          rcases Finset.mem_union.mp hs with hsR | hsC
          · simp only [PEqualNP.Outside.L_meta_25717_aux.patch, Finset.mem_biUnion, Finset.mem_image] at hsR
            obtain ⟨p, hpR, t, ht, rfl⟩ := hsR
            refine PEqualNP.Outside.L_meta_25717_aux.row_block_zero hk1 hk3 row cr z p ?_ t ht
            intro u hu x
            exact (hsame x).1 _ (Finset.mem_biUnion.mpr ⟨p, hpR, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩)
          · simp only [PEqualNP.Outside.L_meta_25717_aux.patch, Finset.mem_biUnion, Finset.mem_image] at hsC
            obtain ⟨p, hpC, t, ht, rfl⟩ := hsC
            refine PEqualNP.Outside.L_meta_25717_aux.col_block_zero hk1 hk3 col cc z p ?_ t ht
            intro u hu x
            exact (hsame x).2 _ (Finset.mem_biUnion.mpr ⟨p, hpC, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩)
        have hcard := PEqualNP.Outside.L_meta_25717_aux.card_le_mul_ker forms P hker
        have hPcard := PEqualNP.Outside.L_meta_25717_aux.card_vanishing_on_sites sites
        have hmul : 2 ^ k * 2 ^ sites.card ≤ 2 ^ q * 2 ^ k := by
          calc 2 ^ k * 2 ^ sites.card
              ≤ (2 ^ q * P.card) * 2 ^ sites.card := Nat.mul_le_mul_right _ hcard
            _ = 2 ^ q * (P.card * 2 ^ sites.card) := mul_assoc _ _ _
            _ = 2 ^ q * 2 ^ k := by rw [hPcard]
        have hpow : 2 ^ sites.card ≤ 2 ^ q := by
          have hmul' : 2 ^ sites.card * 2 ^ k ≤ 2 ^ q * 2 ^ k := by
            rw [mul_comm] at hmul
            exact hmul
          exact Nat.le_of_mul_le_mul_right hmul' (by positivity)
        exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow
      · intro hq
        have e : Fin sites.card ≃ { i : I // i ∈ sites } :=
          (Fintype.equivFinOfCardEq (Fintype.card_coe sites)).symm
        let forms : Fin q → V := fun t =>
          if h : t.1 < sites.card then Pi.single (e ⟨t.1, h⟩).1 1 else 0
        let recKey : (Fin q → B) → V := fun y i =>
          if h : i ∈ sites then y ⟨(e.symm ⟨i, h⟩).1, by
            have := (e.symm ⟨i, h⟩).2
            omega⟩ else 0
        let decode : (Fin q → B) → V × V := fun y =>
          (PEqualNP.Outside.L_meta_25717_aux.out 1 1 0 row cr (recKey y),
           PEqualNP.Outside.L_meta_25717_aux.out 2 3 4 col cc (recKey y))
        refine ⟨forms, decode, fun key => ?_⟩
        have hagree : ∀ s ∈ sites, recKey (fun t => dotProduct (forms t) key) s = key s := by
          intro s hs
          simp only [recKey, hs, ↓reduceDIte]
          have hlt : (e.symm ⟨s, hs⟩).1 < sites.card := (e.symm ⟨s, hs⟩).2
          simp only [forms, hlt, ↓reduceDIte]
          have heq : e ⟨(e.symm ⟨s, hs⟩).1, hlt⟩ = ⟨s, hs⟩ := e.apply_symm_apply ⟨s, hs⟩
          rw [heq]
          simp only [single_dotProduct, one_mul]
        constructor
        · intro j hj
          exact PEqualNP.Outside.L_meta_25717_aux.row_depends_on_patch row cr key
            (recKey (fun t => dotProduct (forms t) key)) R
            (fun s hs => hagree s (Finset.mem_union_left _ hs)) j hj
        · intro i hi
          exact PEqualNP.Outside.L_meta_25717_aux.col_depends_on_patch col cc key
            (recKey (fun t => dotProduct (forms t) key)) C
            (fun s hs => hagree s (Finset.mem_union_right _ hs)) i hi
