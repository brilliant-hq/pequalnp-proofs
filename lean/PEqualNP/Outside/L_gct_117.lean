import PEqualNP.Defs
import Mathlib.Combinatorics.Additive.CauchyDavenport

open scoped Pointwise

namespace PEqualNP.Outside.L_gct_117_aux

def iterSum {p : ℕ} (S : Finset (ZMod p)) : ℕ → Finset (ZMod p)
  | 0 => S
  | k + 1 => iterSum S k + insert 0 S

lemma iterSum_spec {p : ℕ} (S : Finset (ZMod p)) :
    ∀ k z, z ∈ iterSum S k →
      ∃ m : Multiset (ZMod p), (∀ x ∈ m, x ∈ S) ∧ 0 < Multiset.card m ∧ Multiset.card m ≤ k + 1 ∧ m.sum = z := by
  intro k
  induction k with
  | zero =>
    intro z hz
    refine ⟨{z}, ?_, by simp, by simp, by simp⟩
    intro x hx
    rw [Multiset.mem_singleton.mp hx]
    exact hz
  | succ k ih =>
    intro z hz
    rcases Finset.mem_add.mp hz with ⟨a, ha, b, hb, rfl⟩
    obtain ⟨m, hmS, hmpos, hmle, hmsum⟩ := ih a ha
    rcases Finset.mem_insert.mp hb with rfl | hbS
    · exact ⟨m, hmS, hmpos, by omega, by simp [hmsum]⟩
    · refine ⟨b ::ₘ m, ?_, by simp, by simp; omega, by simp [hmsum, add_comm]⟩
      intro x hx
      rcases Multiset.mem_cons.mp hx with rfl | hxm
      · exact hbS
      · exact hmS x hxm

lemma iterSum_nonempty {p : ℕ} {S : Finset (ZMod p)} (hS : S.Nonempty) :
    ∀ k, (iterSum S k).Nonempty
  | 0 => hS
  | k + 1 => (iterSum_nonempty hS k).add (Finset.insert_nonempty 0 S)

lemma iterSum_card_ge {p : ℕ} (hp : Nat.Prime p) {S : Finset (ZMod p)} (hS : S.Nonempty) (h0 : (0 : ZMod p) ∉ S) :
    ∀ k, min p ((k + 1) * S.card) ≤ (iterSum S k).card := by
  intro k
  induction k with
  | zero =>
    simp [iterSum]
  | succ k ih =>
    have hcd := ZMod.cauchy_davenport hp (iterSum_nonempty hS k) (Finset.insert_nonempty 0 S)
    have hins : (insert (0 : ZMod p) S).card = S.card + 1 := Finset.card_insert_of_notMem h0
    rw [hins] at hcd
    have hstep : min p ((k + 2) * S.card) ≤ min p ((iterSum S k).card + (S.card + 1) - 1) := by
      have : (k + 2) * S.card = (k + 1) * S.card + S.card := by ring
      omega
    exact le_trans hstep hcd

end PEqualNP.Outside.L_gct_117_aux

theorem PEqualNP.Outside.L_gct_117 : ∀ (p g : ℕ) (S : Finset (ZMod p)), Nat.Prime p → 1 ≤ g → (0 : ZMod p) ∉ S → (∀ m : Multiset (ZMod p), (∀ x ∈ m, x ∈ S) → 0 < Multiset.card m → Multiset.card m ≤ g → m.sum ≠ 0) → g * S.card + 1 ≤ p := by
  intro p g S hp hg h0 hfree
  haveI : NeZero p := ⟨hp.ne_zero⟩
  by_cases hS : S.Nonempty
  · have hge := PEqualNP.Outside.L_gct_117_aux.iterSum_card_ge hp hS h0 (g - 1)
    have hg1 : g - 1 + 1 = g := by omega
    rw [hg1] at hge
    have h0not : (0 : ZMod p) ∉ PEqualNP.Outside.L_gct_117_aux.iterSum S (g - 1) := by
      intro hmem
      obtain ⟨m, hmS, hmpos, hmle, hmsum⟩ := PEqualNP.Outside.L_gct_117_aux.iterSum_spec S (g - 1) 0 hmem
      exact hfree m hmS hmpos (by omega) hmsum
    have hsub : PEqualNP.Outside.L_gct_117_aux.iterSum S (g - 1) ⊆ Finset.univ.erase (0 : ZMod p) := by
      intro z hz
      exact Finset.mem_erase.mpr ⟨fun h => h0not (h ▸ hz), Finset.mem_univ z⟩
    have hle : (PEqualNP.Outside.L_gct_117_aux.iterSum S (g - 1)).card ≤ p - 1 := by
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card] at hcard
      exact hcard
    have hppos : 1 ≤ p := hp.one_lt.le
    omega
  · have hScard : S.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hS)
    rw [hScard, mul_zero, zero_add]
    exact hp.one_lt.le
