import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18806_aux

open PEqualNP.CircuitLowerBounds

theorem getD_app {α : Type} (w : List α) (a a0 : α) (m : ℕ) :
    (w ++ [a]).getD m a0 = if m < w.length then w.getD m a0 else if m = w.length then a else a0 := by
  simp only [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy m w.length with h | h | h
  · simp [h, List.getElem?_append_left h]
  · subst h; simp
  · rw [if_neg (by omega), if_neg (by omega), List.getElem?_eq_none (by simp; omega)]
    rfl

theorem fold_inv {α : Type} (a0 : α) (F : GateOp → List α → α) (r : ℕ → ℕ) (n : ℕ)
    (hr1 : ∀ m, n ≤ m → r m = m) (hr2 : ∀ m, m < n → r m < n)
    (gs : List Gate) : ∀ (wD wC : List α), wD.length = wC.length → n ≤ wC.length →
    (∀ m, wD.getD (r m) a0 = wC.getD m a0) →
    (∀ m, ((gs.map (fun g => (⟨g.op, g.inputs.map r⟩ : Gate))).foldl
      (fun w g => w ++ [F g.op (g.inputs.map fun i => w.getD i a0)]) wD).getD (r m) a0 =
      (gs.foldl (fun w g => w ++ [F g.op (g.inputs.map fun i => w.getD i a0)]) wC).getD m a0) := by
  induction gs with
  | nil => intro wD wC _ _ h; simpa using h
  | cons g gs ih =>
    intro wD wC hl hn h
    simp only [List.map_cons, List.foldl_cons]
    have he : (g.inputs.map r).map (fun i => wD.getD i a0) = g.inputs.map (fun i => wC.getD i a0) := by
      rw [List.map_map]
      exact List.map_congr_left (fun i _ => h i)
    apply ih
    · simp [hl]
    · simp; omega
    · intro m
      rw [he, getD_app, getD_app]
      by_cases hm : m < n
      · have := hr2 m hm
        rw [if_pos (by omega), if_pos (by omega)]
        exact h m
      · rw [hr1 m (by omega)]
        have := h m
        rw [hr1 m (by omega)] at this
        rw [hl]
        split_ifs <;> simp_all

end PEqualNP.Outside.L_meta_18806_aux

open PEqualNP.Outside.L_meta_18806_aux PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18806 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x1)), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ x5 ∈ x2.gates, x5.inputs.Nodup) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2.size ∧ PEqualNP.TopForm.IsAO2 x1 x6 ∧ (∀ x7 ∈ x6.gates, x7.inputs.Nodup) ∧ (∀ (x7 : Fin x1 → Bool), x6.eval (List.ofFn x7) = x2.eval (List.ofFn (x7 ∘ ⇑x3))) ∧ ∀ (x7 : Fin x1), x6.lineDeg x1 {↑(x3 x7)} = x2.lineDeg x1 {↑x7} := by
  intro n C σ hC hN
  let r : ℕ → ℕ := fun i => if h : i < n then (σ ⟨i, h⟩ : ℕ) else i
  have hr1 : ∀ m, n ≤ m → r m = m := fun m hm => by simp [r, dif_neg (show ¬ m < n by omega)]
  have hr2 : ∀ m, m < n → r m < n := fun m hm => by simp [r, dif_pos hm]
  have hinj : Function.Injective r := by
    intro a b hab
    by_cases ha : a < n <;> by_cases hb : b < n
    · simp only [r, dif_pos ha, dif_pos hb] at hab
      have := σ.injective (Fin.ext hab)
      simpa using this
    · have := hr2 a ha; rw [hr1 b (by omega)] at hab; omega
    · have := hr2 b hb; rw [hr1 a (by omega)] at hab; omega
    · rw [hr1 a (by omega), hr1 b (by omega)] at hab; exact hab
  refine ⟨⟨C.gates.map (fun g => (⟨g.op, g.inputs.map r⟩ : PEqualNP.CircuitLowerBounds.Gate)), r C.output⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · obtain ⟨h1, h2, h3⟩ := hC
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      exact h1 g0 hg0
    · intro j hj i hi
      simp only [List.length_map] at hj
      have hgj := h2 j hj
      simp only [PEqualNP.MetaComplexity.NestedCover.gateAt, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_eq_getElem hj, Option.map_some, Option.getD_some] at hi hgj
      simp only [List.mem_map] at hi
      obtain ⟨i0, hi0, rfl⟩ := hi
      have := hgj i0 hi0
      by_cases h0 : i0 < n
      · have := hr2 i0 h0; omega
      · rw [hr1 i0 (by omega)]; exact this
    · intro g hg
      simp only [List.mem_map] at hg
      obtain ⟨g0, hg0, rfl⟩ := hg
      simpa using h3 g0 hg0
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    exact (hN g0 hg0).map hinj
  · intro x
    have key := fold_inv false (fun op l => op.eval l) r n hr1 hr2 C.gates (List.ofFn x) (List.ofFn (x ∘ σ)) (by simp) (by simp) (by
      intro m
      by_cases hm : m < n
      · have h2 := hr2 m hm
        simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
        simp [r, hm, List.ofFnNthVal, Function.comp]
      · rw [hr1 m (by omega)]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])
    exact key C.output
  · intro k
    let F : GateOp → List ℕ → ℕ := fun op l => Gate.lineDegree ⟨op, List.range l.length⟩ l
    have hF : ∀ (g : Gate) (d : List ℕ), g.lineDegree d = F g.op (g.inputs.map fun i => d.getD i 0) := by
      intro g d
      simp only [F, Gate.lineDegree, List.length_map]
      split_ifs
      · congr 1
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp at h1; simp [List.getElem?_eq_getElem h1]
      · congr 1
        apply List.ext_getElem (by simp)
        intro i h1 h2
        simp at h1; simp [List.getElem?_eq_getElem h1]
    have key := fold_inv 0 F r n hr1 hr2 C.gates
      ((List.range n).map fun i => if i ∈ ({(σ k : ℕ)} : Finset ℕ) then 1 else 0)
      ((List.range n).map fun i => if i ∈ ({(k : ℕ)} : Finset ℕ) then 1 else 0) (by simp) (by simp) (by
      intro m
      by_cases hm : m < n
      · have h2 := hr2 m hm
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h2,
          List.getElem?_range hm, Option.map_some, Option.getD_some, Finset.mem_singleton]
        simp only [r, dif_pos hm]
        have : ((σ ⟨m, hm⟩ : ℕ) = (σ k : ℕ)) ↔ m = (k : ℕ) := by
          rw [Fin.val_inj, σ.injective.eq_iff, Fin.ext_iff]
        by_cases hk : m = (k : ℕ)
        · rw [if_pos (this.mpr hk), if_pos hk]
        · rw [if_neg (fun h => hk (this.mp h)), if_neg hk]
      · rw [hr1 m (by omega)]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)])
    have e1 : ∀ (gs : List Gate) (d : List ℕ), gs.foldl (fun d g => d ++ [g.lineDegree d]) d =
        gs.foldl (fun w g => w ++ [F g.op (g.inputs.map fun i => w.getD i 0)]) d := by
      intro gs d
      congr 1
      funext w g
      rw [hF]
    have k2 := key C.output
    simp only [Circuit.lineDeg, Circuit.lineDegrees]
    rw [e1, e1]
    exact k2
