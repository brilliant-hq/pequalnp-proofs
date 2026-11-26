import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_145_aux

theorem term_le {m k w : ℕ} (h2k : 2 * k ≤ m) (hw : w ≤ k) :
    k ^ k * (m - k) ^ (m - k) ≤ k ^ w * (m - k) ^ (m - w) := by
  have hk_le : k ≤ m - k := by omega
  have h1 : k ^ k = k ^ w * k ^ (k - w) := by
    rw [← Nat.pow_add, Nat.add_sub_cancel' hw]
  have h2 : (m - k) ^ (m - w) = (m - k) ^ (k - w) * (m - k) ^ (m - k) := by
    rw [← Nat.pow_add]
    congr 1; omega
  rw [h1, h2]
  have hp : k ^ (k - w) ≤ (m - k) ^ (k - w) := Nat.pow_le_pow_left hk_le (k - w)
  calc k ^ w * k ^ (k - w) * (m - k) ^ (m - k)
      = k ^ w * (k ^ (k - w) * (m - k) ^ (m - k)) := by ring
    _ ≤ k ^ w * ((m - k) ^ (k - w) * (m - k) ^ (m - k)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hp)

end PEqualNP.Outside.L_gct_145_aux

open PEqualNP.Outside.L_gct_145_aux in
theorem PEqualNP.Outside.L_gct_145 : ∀ m k : ℕ, 2 * k ≤ m → (∑ w ∈ Finset.range (k + 1), m.choose w) * (k ^ k * (m - k) ^ (m - k)) ≤ m ^ m := by
  intro m k h2k
  rw [Finset.sum_mul]
  have hstep : ∑ w ∈ Finset.range (k + 1), m.choose w * (k ^ k * (m - k) ^ (m - k)) ≤
      ∑ w ∈ Finset.range (k + 1), m.choose w * (k ^ w * (m - k) ^ (m - w)) := by
    apply Finset.sum_le_sum
    intro w hw
    have hwk : w ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hw)
    exact Nat.mul_le_mul_left _ (term_le h2k hwk)
  have hsub : Finset.range (k + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_mono (by omega)
  have hle_all : ∑ w ∈ Finset.range (k + 1), m.choose w * (k ^ w * (m - k) ^ (m - w)) ≤
      ∑ w ∈ Finset.range (m + 1), m.choose w * (k ^ w * (m - k) ^ (m - w)) :=
    Finset.sum_le_sum_of_subset hsub
  have hbin : ∑ w ∈ Finset.range (m + 1), m.choose w * (k ^ w * (m - k) ^ (m - w)) = m ^ m := by
    have h := add_pow k (m - k) m
    rw [show k + (m - k) = m by omega] at h
    rw [h]
    apply Finset.sum_congr rfl
    intro w _
    simp only [Nat.cast_id]
    ring
  exact hstep.trans (hle_all.trans hbin.le)
