import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18904_aux

open PEqualNP.CircuitLowerBounds

def f (x9 : List ℕ) (x10 : Gate) : List ℕ := x9 ++ [if x10.op.eval [Bool.false, Bool.true] = Bool.true then x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) ||| x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ) else x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) &&& x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)]

def P (x1 : List ℕ) (x3 : ℕ → ℕ) (k : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ (∀ i ∈ g.inputs, i < x1.length + k) ∧
    x3 (x1.length + k) = (if g.op.eval [Bool.false, Bool.true] = Bool.true then x3 (g.inputs.getD 0 0) ||| x3 (g.inputs.getD 1 0) else x3 (g.inputs.getD 0 0) &&& x3 (g.inputs.getD 1 0))

theorem exG (x1 : List ℕ) (x2 : ℕ) (x3 : ℕ → ℕ)
    (h2 : ∀ x5 < x2, ∃ x7 < x1.length + x5, ∃ x8 < x1.length + x5, x3 (x1.length + x5) = x3 x7 ||| x3 x8 ∨ x3 (x1.length + x5) = x3 x7 &&& x3 x8) :
    ∀ k, ∃ g : Gate, k < x2 → P x1 x3 k g := by
  intro k
  by_cases hk : k < x2
  · obtain ⟨a, ha, b, hb, h | h⟩ := h2 k hk
    · refine ⟨⟨GateOp.or, [a, b]⟩, fun _ => ⟨Or.inr rfl, rfl, ?_, ?_⟩⟩
      · intro i hi
        simp at hi
        omega
      · simpa [GateOp.eval] using h
    · refine ⟨⟨GateOp.and, [a, b]⟩, fun _ => ⟨Or.inl rfl, rfl, ?_, ?_⟩⟩
      · intro i hi
        simp at hi
        omega
      · simpa [GateOp.eval] using h
  · exact ⟨⟨GateOp.or, []⟩, fun h => absurd h hk⟩

theorem fold (x1 : List ℕ) (x2 : ℕ) (x3 : ℕ → ℕ) (h1 : ∀ x4 < x1.length, x3 x4 = x1.getD x4 (0 : ℕ))
    (G : ℕ → Gate) (hG : ∀ k, k < x2 → P x1 x3 k (G k)) :
    ∀ m ≤ x2, List.foldl f x1 ((List.range m).map G) = (List.range (x1.length + m)).map x3 := by
  intro m
  induction m with
  | zero =>
    intro _
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      have hi3 : i < x1.length := by simpa using hi2
      simp [h1 i hi3, hi3]
  | succ m ih =>
    intro hm
    have hgd : ∀ i < x1.length + m, ((List.range (x1.length + m)).map x3).getD i 0 = x3 i := by
      intro i hi
      simp [hi]
    obtain ⟨_, hl, hin, hv⟩ := hG m (by omega)
    have h0 : (G m).inputs.getD 0 0 < x1.length + m := by
      apply hin
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    have h1' : (G m).inputs.getD 1 0 < x1.length + m := by
      apply hin
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact List.getElem_mem _
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega), ← Nat.add_assoc, List.range_succ, List.map_append]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, f]
    rw [hgd _ h0, hgd _ h1', hv]

end PEqualNP.Outside.L_meta_18904_aux

theorem PEqualNP.Outside.L_meta_18904 : ∀ (x1 : List ℕ) (x2 : ℕ) (x3 : ℕ → ℕ), (∀ x4 < x1.length, x3 x4 = x1.getD x4 (0 : ℕ)) → (∀ x5 < x2, ∃ x7 < x1.length + x5, ∃ x8 < x1.length + x5, x3 (x1.length + x5) = x3 x7 ||| x3 x8 ∨ x3 (x1.length + x5) = x3 x7 &&& x3 x8) → ∀ x6 < x1.length + x2, ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size ≤ x2 ∧ PEqualNP.TopForm.IsAO2 x1.length x8 ∧ (List.foldl (fun (x9 : List ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) => x9 ++ [if x10.op.eval [Bool.false, Bool.true] = Bool.true then x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) ||| x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ) else x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) &&& x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)]) x1 x8.gates).getD x8.output (0 : ℕ) = x3 x6 := by
  intro x1 x2 x3 h1 h2 x6 h6
  choose G hG using PEqualNP.Outside.L_meta_18904_aux.exG x1 x2 x3 h2
  have hmem : ∀ g ∈ (List.range x2).map G, ∃ k < x2, G k = g := by
    intro g hg
    simpa using hg
  refine ⟨⟨(List.range x2).map G, x6⟩, by simp [PEqualNP.CircuitLowerBounds.Circuit.size], ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := hmem g hg
    exact (hG k hk).1
  · intro j hj i hi
    have hj' : j < x2 := by simpa using hj
    have : PEqualNP.MetaComplexity.NestedCover.gateAt ⟨(List.range x2).map G, x6⟩ j = G j := by
      simp [PEqualNP.MetaComplexity.NestedCover.gateAt, hj']
    rw [this] at hi
    exact (hG j hj').2.2.1 i hi
  · intro g hg
    obtain ⟨k, hk, rfl⟩ := hmem g hg
    exact (hG k hk).2.1
  · have := PEqualNP.Outside.L_meta_18904_aux.fold x1 x2 x3 h1 G hG x2 (le_refl _)
    unfold PEqualNP.Outside.L_meta_18904_aux.f at this
    rw [this]
    simp [h6]
