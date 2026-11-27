import Mathlib.Data.Set.Image
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25625_aux

def mix (x : ℤ → Bool) (z : ℤ) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))
def evolve (x : ℤ → Bool) (z : ℤ) : Bool :=
  xor (mix x z) (!(mix x (z+1)) && mix x (z+2))
def edgeAt (family : Set (ℤ → Bool)) (edge : ℤ) : Prop :=
  (∀ x ∈ family, ∀ z ≤ edge, x z = false) ∧ ∃ x ∈ family, x (edge+1) = true

theorem mix_zero (x : ℤ → Bool) (E : ℤ) (h : ∀ z ≤ E, x z = false) (w : ℤ) (hw : w + 1 ≤ E) :
    mix x w = false := by
  unfold mix
  rw [h (w-1) (by omega), h w (by omega), h (w+1) (by omega)]
  rfl

theorem evolve_zero (x : ℤ → Bool) (E : ℤ) (h : ∀ z ≤ E, x z = false) (z : ℤ) (hz : z ≤ E - 3) :
    evolve x z = false := by
  unfold evolve
  rw [mix_zero x E h z (by omega), mix_zero x E h (z+1) (by omega),
    mix_zero x E h (z+2) (by omega)]
  rfl

theorem evolve_one (x : ℤ → Bool) (E : ℤ) (h : ∀ z ≤ E, x z = false) (hx : x (E+1) = true) :
    evolve x (E - 3 + 1) = true := by
  unfold evolve
  rw [mix_zero x E h (E-3+1) (by omega), mix_zero x E h (E-3+1+1) (by omega)]
  have e1 : E - 3 + 1 + 2 = E := by ring
  rw [e1]
  unfold mix
  rw [h (E-1) (by omega), h E le_rfl, hx]
  rfl

theorem orbit_step (S : Set (ℤ → Bool)) (E : ℤ) (h : edgeAt S E) :
    edgeAt (evolve '' S) (E - 3) := by
  obtain ⟨h1, x0, hx0, hw⟩ := h
  refine ⟨?_, evolve x0, ⟨x0, hx0, rfl⟩, evolve_one x0 E (h1 x0 hx0) hw⟩
  rintro y ⟨x, hx, rfl⟩ z hz
  exact evolve_zero x E (h1 x hx) z hz

theorem scan_step (S : Set (ℤ → Bool)) (E c : ℤ) (h : edgeAt S E) :
    edgeAt {y | ∃ x ∈ S, ∀ site ≤ c, y site = evolve x site} (min (E - 3) c) := by
  obtain ⟨h1, x0, hx0, hw⟩ := h
  refine ⟨?_, ?_⟩
  · rintro y ⟨x, hx, hy⟩ z hz
    have a : z ≤ E - 3 := le_trans hz (min_le_left _ _)
    have b : z ≤ c := le_trans hz (min_le_right _ _)
    rw [hy z b]
    exact evolve_zero x E (h1 x hx) z a
  · by_cases hc : E - 3 ≤ c
    · refine ⟨evolve x0, ⟨x0, hx0, fun _ _ => rfl⟩, ?_⟩
      rw [min_eq_left hc]
      exact evolve_one x0 E (h1 x0 hx0) hw
    · refine ⟨fun s => if s ≤ c then evolve x0 s else true, ⟨x0, hx0, ?_⟩, ?_⟩
      · intro site hs
        simp [hs]
      · rw [min_eq_right (by omega)]
        simp

theorem orbit_edge (S : Set (ℤ → Bool)) (E : ℤ) (h : edgeAt S E) (n : ℕ) :
    edgeAt ((List.range n).foldl (fun (family : Set (ℤ → Bool)) _ => evolve '' family) S)
      (E - 3 * (n : ℤ)) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    have := orbit_step _ _ ih
    have e : E - 3 * ((n+1 : ℕ) : ℤ) = E - 3 * (n : ℤ) - 3 := by push_cast; ring
    rw [e]
    exact this

theorem shift (l : List ℕ) (f g : ℕ → ℤ) (hfg : ∀ i ∈ l, f i = g i - 3) (init : ℤ) :
    l.foldl (fun c i => min c (f i)) (init - 3) = l.foldl (fun c i => min c (g i)) init - 3 := by
  induction l generalizing init with
  | nil => rfl
  | cons a t ih =>
    simp only [List.foldl_cons]
    have ha : f a = g a - 3 := hfg a (by simp)
    rw [ha, min_sub_sub_right, ih (fun i hi => hfg i (by simp [hi]))]

theorem scan_edge (S : Set (ℤ → Bool)) (E : ℤ) (cut : ℕ → ℤ) (h : edgeAt S E) (n : ℕ) :
    edgeAt ((List.range n).foldl (fun (old : Set (ℤ → Bool)) tick =>
      {y | ∃ x ∈ old, ∀ site ≤ cut (tick+1), y site = evolve x site}) S)
      ((List.range n).foldl (fun current idx =>
        min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) (E - 3*(n : ℤ))) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    have key := shift (List.range n) (fun idx => cut (idx+1) - 3*((n+1-1-idx : ℕ) : ℤ))
      (fun idx => cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ)) (by
        intro i hi
        have hi' : i < n := List.mem_range.mp hi
        have e : n+1-1-i = (n-1-i)+1 := by omega
        simp only [e]
        push_cast
        ring) (E - 3*(n : ℤ))
    have e2 : E - 3 * ((n+1 : ℕ) : ℤ) = E - 3 * (n : ℤ) - 3 := by push_cast; ring
    have e3 : ((n+1-1-n : ℕ) : ℤ) = 0 := by
      have : n+1-1-n = 0 := by omega
      rw [this]; rfl
    rw [e2, key, e3, mul_zero, sub_zero]
    exact scan_step _ _ _ ih

end PEqualNP.Outside.L_meta_25625_aux

open PEqualNP.Outside.L_meta_25625_aux in
theorem PEqualNP.Outside.L_meta_25625 : let mix := fun (x : ℤ → Bool) (z : ℤ) => xor (xor (x (z-1)) (x z)) (x (z+1))
let evolve := fun (x : ℤ → Bool) (z : ℤ) =>
  xor (mix x z) (!(mix x (z+1)) && mix x (z+2))
let edgeAt := fun (family : Set (ℤ → Bool)) (edge : ℤ) =>
  (∀ x ∈ family, ∀ z ≤ edge, x z = false) ∧
  ∃ x ∈ family, x (edge+1) = true
∀ (S : Set (ℤ → Bool)) (E : ℤ) (cut : ℕ → ℤ) (n : ℕ), edgeAt S E →
  let orbit := (List.range n).foldl (fun (family : Set (ℤ → Bool)) _ => evolve '' family) S
  let scan := (List.range n).foldl (fun (old : Set (ℤ → Bool)) tick =>
    {y | ∃ x ∈ old, ∀ site ≤ cut (tick+1), y site = evolve x site}) S
  let trueEdge := E - 3*(n : ℤ)
  let finalEdge := (List.range n).foldl (fun current idx =>
    min current (cut (idx+1) - 3*((n-1-idx : ℕ) : ℤ))) trueEdge
  edgeAt orbit trueEdge ∧ edgeAt scan finalEdge := by
  intro mix' evolve' edgeAt' S E cut n h
  exact ⟨orbit_edge S E h n, scan_edge S E cut h n⟩
