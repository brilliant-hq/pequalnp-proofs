import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18828_aux

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


theorem relabel (n : ℕ) (C : Circuit) (σ : Equiv.Perm (Fin n)) (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (x ∘ σ)) := by
  let r : ℕ → ℕ := fun i => if h : i < n then (σ ⟨i, h⟩ : ℕ) else i
  have hr1 : ∀ m, n ≤ m → r m = m := fun m hm => by simp [r, dif_neg (show ¬ m < n by omega)]
  have hr2 : ∀ m, m < n → r m < n := fun m hm => by simp [r, dif_pos hm]
  refine ⟨⟨C.gates.map (fun g => (⟨g.op, g.inputs.map r⟩ : Gate)), r C.output⟩, ?_, ?_, ?_⟩
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
  · simp [Circuit.size]
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

def S (i j : Fin 26) : Bool :=
  (decide (i.val < 13) && decide (13 ≤ j.val) && decide ((i.val + 26 - j.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ))) ||
  (decide (j.val < 13) && decide (13 ≤ i.val) && decide ((j.val + 26 - i.val) % 13 ∈ ({0, 1, 3, 9} : Finset ℕ)))

def pi (v i : Fin 26) : Fin 26 :=
  if v.val < 13 then
    (if i.val < 13 then ⟨(i.val + 13 - v.val) % 13, by omega⟩ else ⟨13 + (i.val - v.val) % 13, by omega⟩)
  else
    (if i.val < 13 then ⟨13 + (v.val - i.val) % 13, by omega⟩ else ⟨(v.val + 13 - i.val) % 13, by omega⟩)

theorem pi_bij : ∀ v, Function.Bijective (pi v) := by decide +kernel

theorem pi_v : ∀ v, pi v v = 0 := by decide +kernel

theorem pi_S : ∀ v i j, S (pi v i) (pi v j) = S i j := by decide +kernel

theorem S_cc : ∀ p q : Fin 13, S (Fin.castAdd 13 p) (Fin.castAdd 13 q) = false := by decide +kernel
theorem S_nn : ∀ p q : Fin 13, S (Fin.natAdd 13 p) (Fin.natAdd 13 q) = false := by decide +kernel
theorem S_cn : ∀ p l : Fin 13, S (Fin.castAdd 13 p) (Fin.natAdd 13 l) = true ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l := by decide +kernel
theorem S_nc : ∀ p l : Fin 13, S (Fin.natAdd 13 l) (Fin.castAdd 13 p) = true ↔ p ∈ PEqualNP.HeptadCover.singerLines3 l := by decide +kernel

theorem inc_iff (x : Fin 26 → Bool) :
    (∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) ↔
    ∃ i j, S i j = true ∧ x i = true ∧ x j = true := by
  constructor
  · rintro ⟨p, l, h, h1, h2⟩
    exact ⟨_, _, (S_cn p l).mpr h, h1, h2⟩
  · rintro ⟨i, j, h, h1, h2⟩
    have key : ∀ i j : Fin (13 + 13), S i j = true → x i = true → x j = true →
        ∃ (p l : Fin 13), p ∈ PEqualNP.HeptadCover.singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
      intro i j h h1 h2
      induction i using Fin.addCases with
      | left p =>
        induction j using Fin.addCases with
        | left q => exact absurd ((S_cc p q).symm.trans h) Bool.false_ne_true
        | right l => exact ⟨p, l, (S_cn p l).mp h, h1, h2⟩
      | right l =>
        induction j using Fin.addCases with
        | left p => exact ⟨p, l, (S_nc p l).mp h, h2, h1⟩
        | right q => exact absurd ((S_nn l q).symm.trans h) Bool.false_ne_true
    exact key i j h h1 h2

end PEqualNP.Outside.L_meta_18828_aux

open PEqualNP.Outside.L_meta_18828_aux in
theorem PEqualNP.Outside.L_meta_18828 : have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), x2 ∈ PEqualNP.HeptadCover.singerLines3 x3 ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; ∀ (x2 : Fin (26 : ℕ)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 → ∃ (x5 : Fin (26 : ℕ) → Fin (26 : ℕ)) (x6 : PEqualNP.CircuitLowerBounds.Circuit), Function.Bijective x5 ∧ x5 x2 = (0 : Fin (26 : ℕ)) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x6 ∧ x6.size = x3.size ∧ (∀ (x7 : Fin (26 : ℕ) → Bool), x6.eval (List.ofFn x7) = x3.eval (List.ofFn (x7 ∘ x5))) ∧ ∀ (x7 : Fin (26 : ℕ) → Bool), x1 (x7 ∘ x5) ↔ x1 x7 := by
  intro x1 v C hC
  obtain ⟨D, hD1, hD2, hD3⟩ := relabel 26 C (Equiv.ofBijective _ (pi_bij v)) hC
  refine ⟨pi v, D, pi_bij v, pi_v v, hD1, hD2, hD3, ?_⟩
  intro x
  simp only [x1]
  rw [inc_iff, inc_iff]
  constructor
  · rintro ⟨i, j, h, h1, h2⟩
    exact ⟨pi v i, pi v j, by rw [pi_S]; exact h, h1, h2⟩
  · rintro ⟨i, j, h, h1, h2⟩
    obtain ⟨i', rfl⟩ := (pi_bij v).2 i
    obtain ⟨j', rfl⟩ := (pi_bij v).2 j
    exact ⟨i', j', by rw [← pi_S v]; exact h, h1, h2⟩
