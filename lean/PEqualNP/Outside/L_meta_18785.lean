import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18785_aux

open PEqualNP.CircuitLowerBounds

def fm (σ : Fin 26 → Option (Fin 25)) (F : ℕ) (i : ℕ) : ℕ :=
  if h : i < 26 then ((σ ⟨i, h⟩).map Fin.val).getD F else i - 1

theorem fm_lt (σ : Fin 26 → Option (Fin 25)) (F i : ℕ) (h : i < 26) :
    fm σ F i < 25 ∨ fm σ F i = F := by
  unfold fm
  rw [dif_pos h]
  cases σ ⟨i, h⟩ with
  | none => simp
  | some j => left; simp

theorem fm_ge (σ : Fin 26 → Option (Fin 25)) (F i : ℕ) (h : ¬ i < 26) :
    fm σ F i = i - 1 := by
  unfold fm
  rw [dif_neg h]

theorem getD_app (l : List Bool) (v : Bool) (i : ℕ) :
    (l ++ [v]).getD i false = if i < l.length then l.getD i false
      else if i = l.length then v else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append]
  split_ifs with h1 h2
  · rfl
  · subst h2; simp
  · have : i - l.length ≠ 0 := by omega
    simp [List.getElem?_cons, this]

theorem getD_big (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem main_fold (σ : Fin 26 → Option (Fin 25)) (F : ℕ) :
    ∀ (gs : List Gate) (wD wC : List Bool), wC.length = wD.length + 1 → 25 ≤ wD.length →
      wD.length + gs.length ≤ F →
      (∀ i, wD.getD (fm σ F i) false = wC.getD i false) →
      ∀ i, (List.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        wD (gs.map fun g => { g with inputs := g.inputs.map (fm σ F) })).getD (fm σ F i) false =
      (List.foldl (fun w (g : Gate) => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        wC gs).getD i false := by
  intro gs
  induction gs with
  | nil => intro wD wC _ _ _ h i; simpa using h i
  | cons g gs ih =>
    intro wD wC hl h25 hF h
    simp only [List.map_cons, List.foldl_cons]
    have hv : (g.inputs.map (fm σ F)).map (fun i => wD.getD i false) =
        g.inputs.map (fun i => wC.getD i false) := by
      simp only [List.map_map]
      exact List.map_congr_left (fun i _ => h i)
    apply ih
    · simp [hl]
    · simp; omega
    · simp at hF ⊢; omega
    · intro i
      rw [hv, getD_app, getD_app]
      have hi := h i
      by_cases h26 : i < 26
      · rcases fm_lt σ F i h26 with h1 | h1
        · rw [if_pos (by omega), if_pos (by omega)]
          exact hi
        · rw [h1] at hi ⊢
          simp at hF
          rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), ← hi,
            getD_big _ _ (by omega)]
      · rw [fm_ge σ F i h26] at hi ⊢
        by_cases ha : i < wC.length
        · rw [if_pos (by omega), if_pos ha]; exact hi
        · by_cases hb : i = wC.length
          · rw [if_neg (by omega), if_pos (by omega), if_neg ha, if_pos hb]
          · rw [if_neg (by omega), if_neg (by omega), if_neg ha, if_neg hb]

end PEqualNP.Outside.L_meta_18785_aux

open PEqualNP.Outside.L_meta_18785_aux in
theorem PEqualNP.Outside.L_meta_18785 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Option (Fin (25 : ℕ))), PEqualNP.MetaComplexity.Monotone2 x1 → ∃ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 ∧ x4.size = x1.size ∧ ∀ (x5 : Fin (25 : ℕ) → Bool), x4.eval (List.ofFn x5) = x1.eval (List.ofFn fun (x6 : Fin (26 : ℕ)) => (x2 x6).elim Bool.false x5) := by
  intro C σ hC
  refine ⟨⟨C.gates.map fun g => { g with inputs := g.inputs.map (fm σ (25 + C.gates.length)) },
    fm σ (25 + C.gates.length) C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_map] at hg
    obtain ⟨g0, hg0, rfl⟩ := hg
    have := hC g0 hg0
    simpa using this
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro x
    unfold PEqualNP.CircuitLowerBounds.Circuit.eval PEqualNP.CircuitLowerBounds.Circuit.wires
    apply main_fold
    · simp
    · simp
    · simp
    · intro i
      by_cases h26 : i < 26
      · unfold fm
        rw [dif_pos h26]
        have e : (List.ofFn fun x6 : Fin 26 => (σ x6).elim false x).getD i false =
            (σ ⟨i, h26⟩).elim false x := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
          simp only [List.length_ofFn, h26, Option.getD, dite_true]
        rw [e]
        cases σ ⟨i, h26⟩ with
        | none => simp [List.getD_eq_getElem?_getD]
        | some j =>
          rw [List.getD_eq_getElem?_getD, Option.map_some, Option.getD_some,
            List.getElem?_ofFn]
          simp only [List.length_ofFn, j.isLt, Option.getD, dite_true, Option.elim]
      · rw [fm_ge σ _ i h26, getD_big _ _ (by simp; omega), getD_big _ _ (by simp; omega)]

