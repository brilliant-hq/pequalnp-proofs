import Mathlib

namespace PEqualNP.Outside.L_gct_194

theorem peel {α : Type} [Fintype α] {n : ℕ} (g : (Fin (n+1) → α) → ℂ) :
    (∑ f : Fin (n+1) → α, g f) = ∑ a : α, ∑ f : Fin n → α, g (Fin.cons a f) := by
  rw [← (Fin.consEquiv fun _ => α).sum_comp, Fintype.sum_prod_type]
  rfl

theorem I_cube : Complex.I ^ 3 = -Complex.I := by
  rw [pow_succ, Complex.I_sq]
  ring

end PEqualNP.Outside.L_gct_194

set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_gct_194 : ∀ c d : ℂ, (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, (1 + (if (f j).val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = (f j).val then (1 : ℂ) else if j.val = ((f j).val + 1) % 4 then Complex.I else if j.val = ((f j).val + 2) % 4 then -Complex.I else -1)))) = 120 := by
  intro c d
  set E : Fin 4 → Fin 5 → ℂ := fun j k => 1 + (if k.val = 4 then d * (if j.val = 0 then (1 : ℂ) else if j.val = 1 then -1 else 0) else c * (if j.val = k.val then (1 : ℂ) else if j.val = (k.val + 1) % 4 then Complex.I else if j.val = (k.val + 2) % 4 then -Complex.I else -1)) with hE
  have hsum : (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, E j (f j)) =
      ∑ f : Fin 4 → Fin 5, if Function.Injective f then ∏ j : Fin 4, E j (f j) else 0 := by
    rw [← Finset.sum_filter]
    exact (Finset.sum_bij (fun f _ => (f : Fin 4 → Fin 5))
      (by intro f _; simpa using f.injective)
      (by intro a _ b _ h; exact DFunLike.coe_injective h)
      (by intro f hf; simp at hf; exact ⟨⟨f, hf⟩, by simp, rfl⟩)
      (by intro f _; rfl))
  show (∑ f : Fin 4 ↪ Fin 5, ∏ j : Fin 4, E j (f j)) = 120
  rw [hsum]
  simp only [PEqualNP.Outside.L_gct_194.peel, Fintype.sum_unique, Fin.sum_univ_five]
  simp (config := {decide := true}) only [Fin.prod_univ_four, hE]
  simp only [↓reduceIte]
  ring_nf
  simp only [Complex.I_sq, Complex.I_pow_four, PEqualNP.Outside.L_gct_194.I_cube]
  ring
