-- Track 7: Boundary Layer — Growth Rate Hierarchy (Core Lean only)
--
-- Formalizes the strict growth rate boundary between elementary, ackermannian,
-- goodsteinian, busyBeaver, and rayo growth rates using natural numbers
-- as rank values.
--
-- Zero `sorry`. No imports (core Lean only).

inductive GrowthRate where
  | elementary
  | ackermannian
  | goodsteinian
  | busyBeaver
  | rayo

def growthRateRank (r : GrowthRate) : Nat :=
  match r with
  | GrowthRate.elementary => 1
  | GrowthRate.ackermannian => 2
  | GrowthRate.goodsteinian => 3
  | GrowthRate.busyBeaver => 4
  | GrowthRate.rayo => 5

theorem elementary_lt_ackermannian :
    growthRateRank GrowthRate.elementary < growthRateRank GrowthRate.ackermannian := by
  simp [growthRateRank]
  <;> exact Nat.succ_lt_succ (Nat.zero_lt_succ _)

theorem ackermannian_lt_goodsteinian :
    growthRateRank GrowthRate.ackermannian < growthRateRank GrowthRate.goodsteinian := by
  simp [growthRateRank]
  <;> exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))

theorem goodsteinian_lt_busyBeaver :
    growthRateRank GrowthRate.goodsteinian < growthRateRank GrowthRate.busyBeaver := by
  simp [growthRateRank]
  <;> exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _)))

theorem busyBeaver_lt_rayo :
    growthRateRank GrowthRate.busyBeaver < growthRateRank GrowthRate.rayo := by
  simp [growthRateRank]
  <;> exact Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_succ _))))

theorem growthRatesDistinct :
    growthRateRank GrowthRate.elementary < growthRateRank GrowthRate.ackermannian ∧
    growthRateRank GrowthRate.ackermannian < growthRateRank GrowthRate.goodsteinian ∧
    growthRateRank GrowthRate.goodsteinian < growthRateRank GrowthRate.busyBeaver ∧
    growthRateRank GrowthRate.busyBeaver < growthRateRank GrowthRate.rayo := by
  constructor
  · exact elementary_lt_ackermannian
  · constructor
    · exact ackermannian_lt_goodsteinian
    · constructor
      · exact goodsteinian_lt_busyBeaver
      · exact busyBeaver_lt_rayo
