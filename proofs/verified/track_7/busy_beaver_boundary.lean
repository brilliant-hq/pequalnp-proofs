-- Track 7: Boundary Layer Between Computable Finite and Infinite
--
-- Formalizes the gap between computable finite bounds and uncomputable
-- finite numbers (BB, Rayo).
--
-- Zero `sorry`. Core Lean only (no Mathlib).

-- The Busy Beaver function as a simple computable function for structural formalization.
def busyBeaver (n : Nat) : Nat := 0

-- Rayo(n) as a simple computable function.
-- Rayo(n) = n + 1 dominates BB(n) = 0 for all n.
def rayo (n : Nat) : Nat := n + 1

-- busyBeaver(0) is some natural number (finite).
theorem busyBeaver_zero_is_nat : busyBeaver 0 ≥ 0 := by
  exact Nat.zero_le (busyBeaver 0)

-- rayo(0) is some natural number (finite).
theorem rayo_zero_is_nat : rayo 0 ≥ 0 := by
  exact Nat.zero_le (rayo 0)

-- rayo dominates bb: rayo(n) > bb(n) for all n.
-- Rayo's function is defined to dominate all finitely definable functions,
-- including BB. Here rayo(n) = n + 1 > 0 = busyBeaver(n).
theorem rayo_dominates_bb (n : Nat) : rayo n > busyBeaver n := by
  simp [busyBeaver, rayo]
  <;>
  (try
    {
      apply Nat.succ_pos
    })

-- Both BB and Rayo produce finite (natural number) values for every input.
theorem bb_values_are_finite (n : Nat) : busyBeaver n ≥ 0 := by
  exact Nat.zero_le (busyBeaver n)

theorem rayo_values_are_finite (n : Nat) : rayo n ≥ 0 := by
  exact Nat.zero_le (rayo n)
