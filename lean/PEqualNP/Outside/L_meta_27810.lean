import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27810

theorem cast_eq_iff {k a b : ℕ} : ((a : ZMod k) = (b : ZMod k)) ↔ a % k = b % k :=
  ZMod.natCast_eq_natCast_iff' a b k

theorem eq_of_cast {k a b : ℕ} (ha : a < k) (hb : b < k) (h : (a : ZMod k) = (b : ZMod k)) :
    a = b := by
  rw [cast_eq_iff, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  exact h

theorem reach (k : ℕ) (hk : 0 < k) (h2 : 2 ≤ k) (back : Finset (Fin k) → Finset (Fin k))
    (hb : ∀ S (i : Fin k), i ∈ S → ∀ t : ℕ, t < 7 → ∀ p : Fin k,
       p.val = (i.val + k - 2 + t) % k → p ∈ back S)
    (out : Fin k) : ∀ h q : ℕ, q ≤ 6*h → ∀ p : Fin k,
      ((p.val : ZMod k) + 2*(h : ZMod k) = (out.val : ZMod k) + (q : ZMod k)) →
      p ∈ (List.range h).foldl (fun S _ => back S) {out} := by
  intro h
  induction h with
  | zero =>
    intro q hq p hp
    have hq0 : q = 0 := by omega
    subst hq0
    simp only [Nat.cast_zero, mul_zero, add_zero] at hp
    have := eq_of_cast p.isLt out.isLt hp
    simp [Fin.ext_iff, this]
  | succ h ih =>
    intro q hq p hp
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    obtain ⟨t, q', ht, hq', hqq⟩ : ∃ t q', t < 7 ∧ q' ≤ 6*h ∧ q = q' + t :=
      ⟨min q 6, q - min q 6, by omega, by omega, by omega⟩
    let i : Fin k := ⟨(out.val + q' + 2*h*(k-1)) % k, Nat.mod_lt _ hk⟩
    have hi : (i.val : ZMod k) = out.val + q' - 2*h := by
      simp only [i, ZMod.natCast_mod]
      push_cast [Nat.cast_sub (by omega : 1 ≤ k)]
      rw [ZMod.natCast_self]; ring
    have hqc : (q : ZMod k) = q' + t := by rw [hqq]; push_cast; ring
    apply hb _ i _ t ht p
    · have hlt : (i.val + k - 2 + t) % k < k := Nat.mod_lt _ hk
      apply eq_of_cast p.isLt hlt
      rw [ZMod.natCast_mod]
      push_cast [Nat.cast_sub (by omega : 2 ≤ i.val + k)]
      rw [ZMod.natCast_self, hi]
      push_cast at hp
      linear_combination hp + hqc
    · apply ih q' hq' i
      linear_combination hi

theorem all_mem (k : ℕ) (hk : 0 < k) (h2 : 2 ≤ k) (back : Finset (Fin k) → Finset (Fin k))
    (hb : ∀ S (i : Fin k), i ∈ S → ∀ t : ℕ, t < 7 → ∀ p : Fin k,
       p.val = (i.val + k - 2 + t) % k → p ∈ back S)
    (out : Fin k) (h : ℕ) (hh : k ≤ 6*h+1) (p : Fin k) :
      p ∈ (List.range h).foldl (fun S _ => back S) {out} := by
  have hq : (p.val + 2*h + (k - out.val)) % k < k := Nat.mod_lt _ hk
  apply reach k hk h2 back hb out h ((p.val + 2*h + (k - out.val)) % k) (by omega) p
  rw [ZMod.natCast_mod]
  push_cast [Nat.cast_sub (le_of_lt out.isLt)]
  rw [ZMod.natCast_self]; ring

theorem arc (k : ℕ) (hk : 0 < k) (x s L : ℕ) (hL : 3 ≤ L) :
    ∃ a e : ℕ, a < (k+2)/3 ∧ e < L ∧
      ((x + 3*a + 4 : ℕ) : ZMod k) = ((s + e : ℕ) : ZMod k) := by
  have hd : (s + (k - (x+4) % k)) % k < k := Nat.mod_lt _ hk
  have hm : (x+4) % k < k := Nat.mod_lt _ hk
  set d := (s + (k - (x+4) % k)) % k with hdd
  have hdc : (d : ZMod k) = s - (x + 4) := by
    rw [hdd, ZMod.natCast_mod]
    push_cast [Nat.cast_sub (le_of_lt hm)]
    rw [ZMod.natCast_mod, ZMod.natCast_self]; push_cast; ring
  by_cases hc : d ≤ 3*((k+2)/3 - 1)
  · refine ⟨(d+2)/3, 3*((d+2)/3) - d, by omega, by omega, ?_⟩
    push_cast [Nat.cast_sub (by omega : d ≤ 3*((d+2)/3))]
    linear_combination hdc
  · refine ⟨0, k - d, by omega, by omega, ?_⟩
    push_cast [Nat.cast_sub (le_of_lt hd)]
    rw [ZMod.natCast_self]
    linear_combination hdc

end PEqualNP.Outside.L_meta_27810

open PEqualNP.Outside.L_meta_27810 in
theorem PEqualNP.Outside.L_meta_27810 : ∀ (k r : ℕ) (hk : 0 < k),
  let m := (k+2)/3
  m ≤ r → k ≤ 6*(r-m)+1 →
  let ix := fun j : ℕ => (⟨j % k, Nat.mod_lt _ hk⟩ : Fin k)
  let back := fun (S : Finset (Fin k)) => Finset.univ.filter (fun p : Fin k =>
    ∃ i ∈ S, ∃ t : Fin 7, p = ix (i.val + k - 2 % k + t.val))
  ∀ (out start : Fin k) (len : ℕ), 3 ≤ len → len+3 ≤ k →
    let side := (Finset.range len).image (fun a => ix (start.val+a))
    let kept := fun j : Fin r =>
      (List.range (r-(j.val+1))).foldl (fun S _ => back S) {out}
    ∀ key : Fin k,
      let site := fun j : Fin r => ix (key.val+3*(j.val+1)+1)
      (∃ j : Fin r, j.val+1 ≤ m ∧ site j ∈ kept j ∧ site j ∈ side) ∧
      (∃ j : Fin r, j.val+1 ≤ m ∧ site j ∈ kept j ∧ site j ∉ side) := by
  intro k r hk m hmr hkr ix back out start len h3 hlen side kept key site
  have hmd : m = (k+2)/3 := rfl
  have h2 : 2 % k = 2 := Nat.mod_eq_of_lt (by omega)
  have hb : ∀ S (i : Fin k), i ∈ S → ∀ t : ℕ, t < 7 → ∀ p : Fin k,
      p.val = (i.val + k - 2 + t) % k → p ∈ back S := by
    intro S i hi t ht p hp
    simp only [back, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨i, hi, ⟨t, ht⟩, Fin.ext ?_⟩
    show p.val = (i.val + k - 2 % k + t) % k
    rw [h2]; exact hp
  have hkept : ∀ j : Fin r, j.val + 1 ≤ m → ∀ p, p ∈ kept j := by
    intro j hj p
    exact all_mem k hk (by omega) back hb out _ (by omega) p
  have hsite : ∀ j : Fin r, ((site j).val : ZMod k) = ((key.val + 3*j.val + 4 : ℕ) : ZMod k) := by
    intro j
    show (((key.val + 3*(j.val+1)+1) % k : ℕ) : ZMod k) = _
    rw [ZMod.natCast_mod]; push_cast; ring
  constructor
  · obtain ⟨a, e, ha, he, hc⟩ := arc k hk key.val start.val len h3
    refine ⟨⟨a, by omega⟩, by simp only []; omega, hkept _ (by simp only []; omega) _, ?_⟩
    simp only [side, Finset.mem_image, Finset.mem_range]
    refine ⟨e, he, ?_⟩
    apply Fin.ext
    apply eq_of_cast (Nat.mod_lt _ hk) (site _).isLt
    rw [hsite, ZMod.natCast_mod, hc]
  · obtain ⟨a, e, ha, he, hc⟩ := arc k hk key.val (start.val + len) (k - len) (by omega)
    refine ⟨⟨a, by omega⟩, by simp only []; omega, hkept _ (by simp only []; omega) _, ?_⟩
    simp only [side, Finset.mem_image, Finset.mem_range, not_exists, not_and]
    intro a' ha' heq
    have h1 : ((start.val + a' : ℕ) : ZMod k) = ((key.val + 3*a + 4 : ℕ) : ZMod k) := by
      rw [← ZMod.natCast_mod, ← hsite ⟨a, by omega⟩]
      exact congrArg (fun z : Fin k => (z.val : ZMod k)) heq
    have h3' : ((a' : ℕ) : ZMod k) = ((len + e : ℕ) : ZMod k) := by
      push_cast at h1 hc ⊢
      linear_combination h1 + hc
    have := eq_of_cast (by omega) (by omega) h3'
    omega
