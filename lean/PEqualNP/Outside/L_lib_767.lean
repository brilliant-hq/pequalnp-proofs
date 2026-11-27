import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_767_aux

theorem sub_one : ∀ a b : ZMod 2, a ≠ b → a - b = 1 := by decide

theorem add_zero_eq : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide

end PEqualNP.Outside.L_lib_767_aux

theorem PEqualNP.Outside.L_lib_767 : ∀ (r n : ℕ) (h : Fin n → Fin r → ZMod 2), Function.Injective h → (∀ j, h j ≠ 0) →
  ∀ x y : Fin n → ZMod 2, x ≠ y →
    (Finset.univ.filter (fun j => x j ≠ y j)).card ≤ 2 →
    (∑ j, x j • h j) ≠ (∑ j, y j • h j) := by
  intro r n h hinj hnz x y hxy hcard heq
  set D := Finset.univ.filter (fun j => x j ≠ y j) with hD
  have h0 : ∑ j, (x j - y j) • h j = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  have h1 : ∑ j, (x j - y j) • h j = ∑ j ∈ D, h j := by
    rw [← Finset.sum_subset (Finset.subset_univ D)]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hD, Finset.mem_filter] at hj
      rw [PEqualNP.Outside.L_lib_767_aux.sub_one _ _ hj.2, one_smul]
    · intro j _ hj
      rw [hD, Finset.mem_filter] at hj
      have : x j = y j := by
        by_contra hc
        exact hj ⟨Finset.mem_univ _, hc⟩
      rw [this, sub_self, zero_smul]
  rw [h1] at h0
  have hne : D.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    apply hxy
    funext j
    by_contra hj
    have : j ∈ D := by rw [hD, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj⟩
    rw [hc] at this
    simp at this
  have hpos := hne.card_pos
  rcases (by omega : D.card = 1 ∨ D.card = 2) with h2 | h2
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h2
    rw [ha, Finset.sum_singleton] at h0
    exact hnz a h0
  · obtain ⟨a, b, hab, ha⟩ := Finset.card_eq_two.mp h2
    rw [ha, Finset.sum_pair hab] at h0
    apply hab
    apply hinj
    funext i
    exact PEqualNP.Outside.L_lib_767_aux.add_zero_eq _ _ (by simpa using congrFun h0 i)
