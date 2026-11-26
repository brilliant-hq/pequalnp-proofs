import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18884_aux

def g (v : Fin 26) : Fin 13 :=
  ⟨if v.val < 13 then v.val else (26 - v.val) % 13, by split <;> omega⟩

def pa (i : Fin 13) : Fin 26 := ⟨i.val, by omega⟩

def pb (i : Fin 13) : Fin 26 := ⟨13 + (13 - i.val) % 13, by omega⟩

theorem k1 : ∀ i : Fin 13, pa i ≠ pb i ∧ (pa i).val < 13 ∧ 13 ≤ (pb i).val ∧
    ((pa i).val + (pb i).val) % 13 ∈ [0, 1, 3, 9] := by decide

theorem k2 : ∀ i : Fin 13, g (pa i) = i ∧ g (pb i) = i := by decide

end PEqualNP.Outside.L_meta_18884_aux

open PEqualNP.Outside.L_meta_18884_aux in
theorem PEqualNP.Outside.L_meta_18884 : ∀ (x1 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (SimpleGraph.fromRel fun (x2 x3 : Fin (26 : ℕ)) => ↑x2 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x3 ∧ (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) x1 → (13 : ℕ) ≤ x1.card := by
  intro S hS
  have hu : S.image g = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    obtain ⟨hne, h1, h2, h3⟩ := k1 i
    obtain ⟨e1, e2⟩ := k2 i
    have hadj := hS (pa i) (pb i) (by
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl ⟨h1, h2, h3⟩⟩)
    rw [Finset.mem_image]
    rcases hadj with h | h
    · exact ⟨_, h, e1⟩
    · exact ⟨_, h, e2⟩
  have := Finset.card_image_le (s := S) (f := g)
  rw [hu] at this
  simpa using this
