import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19024_aux

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

end PEqualNP.Outside.L_meta_19024_aux

open PEqualNP.Outside.L_meta_19024_aux PEqualNP.CircuitLowerBounds Pointwise in
theorem PEqualNP.Outside.L_meta_19024 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x3 ∧ x3.size = x1.size ∧ x3.lineDeg (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) = x1.lineDeg (26 : ℕ) (Finset.range (13 : ℕ)) ∧ ∀ (x4 x5 : Finset (Fin (13 : ℕ))), x3.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = x1.eval (PEqualNP.GenericRejection.incidenceInput (Finset.image (fun (x6 : Fin (13 : ℕ)) => -x6) x5) (Finset.image (fun (x6 : Fin (13 : ℕ)) => -x6) x4)) := by
  intro C hC
  let r : ℕ → ℕ := fun i => if i < 13 then 13 + (13 - i) % 13 else if i < 26 then (13 - (i - 13)) % 13 else i
  have hr1 : ∀ m, 26 ≤ m → r m = m := fun m hm => by simp only [r]; split_ifs <;> omega
  have hr2 : ∀ m, m < 26 → r m < 26 := fun m hm => by simp only [r]; split_ifs <;> omega
  refine ⟨⟨C.gates.map (fun g => (⟨g.op, g.inputs.map r⟩ : PEqualNP.CircuitLowerBounds.Gate)), r C.output⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    simpa using hC g0 hg0
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · let F : GateOp → List ℕ → ℕ := fun op l => Gate.lineDegree ⟨op, List.range l.length⟩ l
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
    have key := fold_inv 0 F r 26 hr1 hr2 C.gates
      ((List.range 26).map fun i => if i ∈ Finset.Ico 13 26 then 1 else 0)
      ((List.range 26).map fun i => if i ∈ Finset.range 13 then 1 else 0) (by simp) (by simp) (by
      intro m
      by_cases hm : m < 26
      · have h2 := hr2 m hm
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h2,
          List.getElem?_range hm, Option.map_some, Option.getD_some]
        interval_cases m <;> decide
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
  · intro X Y
    have key := fold_inv false (fun op l => op.eval l) r 26 hr1 hr2 C.gates
      (PEqualNP.GenericRejection.incidenceInput X Y)
      (PEqualNP.GenericRejection.incidenceInput (Finset.image (fun (x6 : Fin 13) => -x6) Y) (Finset.image (fun (x6 : Fin 13) => -x6) X))
      (by simp [PEqualNP.GenericRejection.incidenceInput]) (by simp [PEqualNP.GenericRejection.incidenceInput]) (by
      intro m
      by_cases hm : m < 26
      · simp only [Finset.image_neg_eq_neg]
        simp only [PEqualNP.GenericRejection.incidenceInput, List.getD_eq_getElem?_getD]
        interval_cases m <;> simp [r, List.getElem?_append_left, List.getElem?_append_right, Finset.mem_neg] <;> rfl
      · rw [hr1 m (by omega)]
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp [PEqualNP.GenericRejection.incidenceInput]; omega), List.getElem?_eq_none (by simp [PEqualNP.GenericRejection.incidenceInput]; omega)])
    exact key C.output
