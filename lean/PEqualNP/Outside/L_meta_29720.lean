import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29720

def mix (x : ℤ → Bool) (z : ℤ) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def evolve (x : ℤ → Bool) (z : ℤ) : Bool :=
  xor (mix x z) (!(mix x (z+1)) && mix x (z+2))

def edgeAt (family : Set (ℤ → Bool)) (edge : ℤ) : Prop :=
  (∀ x ∈ family, ∀ z ≤ edge, x z = false) ∧
  ∃ x ∈ family, x (edge+1) = true

theorem evolve_low (x : ℤ → Bool) (e : ℤ) (h : ∀ z ≤ e, x z = false) (z : ℤ)
    (hz : z ≤ e - 3) : evolve x z = false := by
  have a1 : z + 1 - 1 = z := by ring
  have a2 : z + 1 + 1 = z + 2 := by ring
  have a3 : z + 2 - 1 = z + 1 := by ring
  have a4 : z + 2 + 1 = z + 3 := by ring
  unfold evolve mix
  rw [a1, a2, a3, a4, h (z-1) (by omega), h z (by omega), h (z+1) (by omega),
    h (z+2) (by omega), h (z+3) (by omega)]
  rfl

theorem evolve_wit (x : ℤ → Bool) (e : ℤ) (h : ∀ z ≤ e, x z = false)
    (hx : x (e+1) = true) : evolve x (e - 2) = true := by
  have a0 : e - 2 - 1 = e - 3 := by ring
  have a1 : e - 2 + 1 - 1 = e - 2 := by ring
  have a2 : e - 2 + 1 + 1 = e := by ring
  have a3 : e - 2 + 2 - 1 = e - 1 := by ring
  have a4 : e - 2 + 2 + 1 = e + 1 := by ring
  have a5 : e - 2 + 1 = e - 1 := by ring
  have a6 : e - 2 + 2 = e := by ring
  unfold evolve mix
  rw [a1, a2, a3, a4, a5, a6, a0, h (e-3) (by omega), h (e-2) (by omega), h (e-1) (by omega),
    h e (by omega), hx]
  rfl

theorem orbit_step (F : Set (ℤ → Bool)) (e : ℤ) (h : edgeAt F e) :
    edgeAt (Set.image evolve F) (e - 3) := by
  obtain ⟨h1, x, hxF, hx⟩ := h
  refine ⟨?_, evolve x, ⟨x, hxF, rfl⟩, ?_⟩
  · rintro y ⟨w, hw, rfl⟩ z hz
    exact evolve_low w e (h1 w hw) z hz
  · have a : e - 3 + 1 = e - 2 := by ring
    rw [a]
    exact evolve_wit x e (h1 x hxF) hx

theorem scan_step (F : Set (ℤ → Bool)) (e c : ℤ) (h : edgeAt F e) :
    edgeAt {y | ∃ x ∈ F, ∀ site ≤ c, y site = evolve x site} (min (e - 3) c) := by
  obtain ⟨h1, x, hxF, hx⟩ := h
  refine ⟨?_, ?_⟩
  · rintro y ⟨w, hw, hy⟩ z hz
    rw [hy z (le_trans hz (min_le_right _ _))]
    exact evolve_low w e (h1 w hw) z (le_trans hz (min_le_left _ _))
  · by_cases hc : e - 2 ≤ c
    · refine ⟨evolve x, ⟨x, hxF, fun _ _ => rfl⟩, ?_⟩
      have a : min (e - 3) c + 1 = e - 2 := by
        rw [min_eq_left (by omega)]; ring
      rw [a]
      exact evolve_wit x e (h1 x hxF) hx
    · refine ⟨fun s => if s ≤ c then evolve x s else true, ⟨x, hxF, ?_⟩, ?_⟩
      · intro site hs
        simp [hs]
      · have a : min (e - 3) c = c := min_eq_right (by omega)
        rw [a]
        have b : ¬ (c + 1 ≤ c) := by omega
        simp [b]

theorem orbit_main (S : Set (ℤ → Bool)) (E : ℤ) (h : edgeAt S E) (n : ℕ) :
    edgeAt ((List.range n).foldl (fun (family : Set (ℤ → Bool)) _ => Set.image evolve family) S)
      (E - 3*(n : ℤ)) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    have a : E - 3 * ((n + 1 : ℕ) : ℤ) = E - 3 * (n : ℤ) - 3 := by push_cast; ring
    rw [a]
    exact orbit_step _ _ ih

theorem fold_shift (E : ℤ) (cut : ℕ → ℤ) (n k : ℕ) (hk : k ≤ n) :
    (List.range k).foldl (fun current idx =>
      min current (cut (idx+1) - 3*((n+1-1-idx : ℕ) : ℤ))) (E - 3*((n+1 : ℕ) : ℤ))
    = (List.range k).foldl (fun current idx =>
      min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) (E - 3*(n : ℤ)) - 3 := by
  induction k with
  | zero => simp only [List.range_zero, List.foldl_nil]; push_cast; ring
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append, ih (by omega)]
    simp only [List.foldl_cons, List.foldl_nil]
    have a : ((n + 1 - 1 - k : ℕ) : ℤ) = ((n - 1 - k : ℕ) : ℤ) + 1 := by
      have : n + 1 - 1 - k = (n - 1 - k) + 1 := by omega
      rw [this]; push_cast; ring
    rw [a, ← min_sub_sub_right]
    congr 1
    ring

theorem fold_succ (E : ℤ) (cut : ℕ → ℤ) (n : ℕ) :
    (List.range (n+1)).foldl (fun current idx =>
      min current (cut (idx+1) - 3*((n+1-1-idx : ℕ) : ℤ))) (E - 3*((n+1 : ℕ) : ℤ))
    = min ((List.range n).foldl (fun current idx =>
      min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) (E - 3*(n : ℤ)) - 3) (cut (n+1)) := by
  rw [List.range_succ, List.foldl_append, fold_shift E cut n n le_rfl]
  simp

theorem scan_main (S : Set (ℤ → Bool)) (E : ℤ) (cut : ℕ → ℤ) (h : edgeAt S E) (n : ℕ) :
    edgeAt ((List.range n).foldl (fun (old : Set (ℤ → Bool)) tick =>
      {y | ∃ x ∈ old, ∀ site ≤ cut (tick+1), y site = evolve x site}) S)
      ((List.range n).foldl (fun current idx =>
        min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) (E - 3*(n : ℤ))) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [fold_succ, List.range_succ, List.foldl_append]
    exact scan_step _ _ _ ih

end PEqualNP.Outside.L_meta_29720

theorem PEqualNP.Outside.L_meta_29720 : (let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x : ℤ → Bool) (z : ℤ) =>
  xor (mix x z) (!(mix x (z+1)) && mix x (z+2))
let edgeAt := fun (family : Set (ℤ → Bool)) (edge : ℤ) =>
  (∀ x ∈ family, ∀ z ≤ edge, x z = false) ∧
  ∃ x ∈ family, x (edge+1) = true
∀ (S : Set (ℤ → Bool)) (E : ℤ) (cut : ℕ → ℤ) (n : ℕ), edgeAt S E →
  let orbit := (List.range n).foldl (fun (family : Set (ℤ → Bool)) _ => Set.image evolve family) S
  let scan := (List.range n).foldl (fun (old : Set (ℤ → Bool)) tick =>
    {y | ∃ x ∈ old, ∀ site ≤ cut (tick+1), y site = evolve x site}) S
  let trueEdge := E - 3*(n : ℤ)
  let finalEdge := (List.range n).foldl (fun current idx =>
    min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) trueEdge
  edgeAt orbit trueEdge ∧ edgeAt scan finalEdge) := by
  intro mix evolve edgeAt S E cut n h
  exact ⟨PEqualNP.Outside.L_meta_29720.orbit_main S E h n,
    PEqualNP.Outside.L_meta_29720.scan_main S E cut h n⟩
