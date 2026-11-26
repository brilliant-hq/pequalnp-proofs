import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18502_aux

open PEqualNP.CircuitLowerBounds

def mk (t : Bool × ℕ × ℕ) : Gate :=
  { op := if t.1 then GateOp.and else GateOp.or, inputs := [t.2.1, t.2.2] }

theorem step {X : Type} (p : X) (g : List (Bool × ℕ × ℕ)) (W : List Bool) (S : List (Set X))
    (hl : W.length = S.length) (h : ∀ k, W.getD k false = true ↔ p ∈ S.getD k ∅) :
    ((g.map mk).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).length =
      (g.foldl (fun (L : List (Set X)) (t : Bool × ℕ × ℕ) => L.concat (if t.1 = true then L.getD t.2.1 ∅ ∩ L.getD t.2.2 ∅ else L.getD t.2.1 ∅ ∪ L.getD t.2.2 ∅)) S).length ∧
    ∀ k, ((g.map mk).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W).getD k false = true ↔
      p ∈ (g.foldl (fun (L : List (Set X)) (t : Bool × ℕ × ℕ) => L.concat (if t.1 = true then L.getD t.2.1 ∅ ∩ L.getD t.2.2 ∅ else L.getD t.2.1 ∅ ∪ L.getD t.2.2 ∅)) S).getD k ∅ := by
  induction g generalizing W S with
  | nil => exact ⟨hl, h⟩
  | cons t g ih =>
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    · simp [hl]
    · intro k
      rcases t with ⟨b, i, j⟩
      have hi := h i
      have hj := h j
      rcases lt_trichotomy k W.length with hk | hk | hk
      · have hk' : k < S.length := hl ▸ hk
        have := h k
        simp only [List.getD_eq_getElem?_getD] at this ⊢
        rw [List.getElem?_append_left hk, List.concat_eq_append, List.getElem?_append_left hk']
        exact this
      · subst hk
        simp only [List.getD_eq_getElem?_getD, List.concat_eq_append] at hi hj ⊢
        rw [List.getElem?_append_right le_rfl, hl, List.getElem?_append_right le_rfl]
        cases b <;> simp [mk, GateOp.eval, hi, hj]
      · have h1 : (W ++ [(mk (b, i, j)).op.eval ((mk (b, i, j)).inputs.map fun i => W.getD i false)]).length ≤ k := by simp; omega
        have h2 : ((S.concat (if (b, i, j).1 = true then S.getD (b, i, j).2.1 ∅ ∩ S.getD (b, i, j).2.2 ∅ else S.getD (b, i, j).2.1 ∅ ∪ S.getD (b, i, j).2.2 ∅))).length ≤ k := by simp; omega
        rw [List.getD_eq_default _ _ h1, List.getD_eq_default _ _ h2]
        simp

end PEqualNP.Outside.L_meta_18502_aux

open PEqualNP.Outside.L_meta_18502_aux in
theorem PEqualNP.Outside.L_meta_18502 : have x1 : Type := Finset (Fin (13 : ℕ)) × Finset (Fin (13 : ℕ)); ∀ (x2 : Fin (25 : ℕ) → Set x1) (x3 : List (Bool × ℕ × ℕ)) (x4 : ℕ), ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 ∧ x5.size = x3.length ∧ x5.output = x4 ∧ ∀ (x6 : x1) (x7 : Fin (25 : ℕ) → Bool), (∀ (x8 : Fin (25 : ℕ)), x7 x8 = Bool.true ↔ x6 ∈ x2 x8) → ∀ (x9 : ℕ), (x5.wires (List.ofFn x7)).getD x9 Bool.false = Bool.true ↔ x6 ∈ (List.foldl (fun (x10 : List (Set x1)) (x11 : Bool × ℕ × ℕ) => x10.concat (if x11.1 = Bool.true then x10.getD x11.2.1 ∅ ∩ x10.getD x11.2.2 ∅ else x10.getD x11.2.1 ∅ ∪ x10.getD x11.2.2 ∅)) (List.ofFn x2) x3).getD x9 ∅ := by
  intro X A g o
  refine ⟨{ gates := g.map mk, output := o }, ?_, ?_, rfl, ?_⟩
  · intro gt hgt
    simp only [List.mem_map] at hgt
    obtain ⟨t, _, rfl⟩ := hgt
    by_cases h : t.1 <;> simp [mk, h]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro p x hx k
    refine (step p g (List.ofFn x) (List.ofFn A) (by simp) ?_).2 k
    intro k
    by_cases hk : k < 25
    · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn, List.getElem_ofFn]
      exact hx ⟨k, hk⟩
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      simp
