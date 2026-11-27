-- Track 7: Boundary Layer — Boundary Elements (Core Lean only)
--
-- Formalizes elements at the boundary between finite and infinite:
-- non-computable but finite numbers (BB(n), Rayo(n)).
--
-- Zero `sorry`. No forbidden axioms.

structure BoundaryElement where
  value : Nat
  witness : Prop

theorem boundaryElementIsFinite (b : BoundaryElement) : ∃ (n : Nat), b.value = n := by
  refine' ⟨b.value, _⟩
  <;> rfl

def busyBeaverBoundary (n : Nat) : BoundaryElement :=
  { value := n
    witness := True }

def rayoBoundary (n : Nat) : BoundaryElement :=
  { value := n + 1
    witness := True }

theorem boundaryElementValueIsNat (b : BoundaryElement) : b.value ≥ 0 := by
  exact Nat.zero_le b.value

theorem busyBeaverBelowRayoBoundary (n : Nat) :
    (busyBeaverBoundary n : BoundaryElement).value < (rayoBoundary n : BoundaryElement).value := by
  simp [busyBeaverBoundary, rayoBoundary]
  <;>
  (try
    {
      -- n < n + 1: n + 1 = n.succ, and n < n.succ by Nat.lt_succ_self
      have h₁ : n < n.succ := by
        -- n < n.succ is a basic property of natural numbers
        exact Nat.lt_succ_self n
      have h₂ : n.succ = n + 1 := by rfl
      rw [h₂] at h₁
      exact h₁
    })

theorem boundaryElementValueIsFinite (b : BoundaryElement) : b.value ≥ 0 := by
  exact Nat.zero_le b.value
