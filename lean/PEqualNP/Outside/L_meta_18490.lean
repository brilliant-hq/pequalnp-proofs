import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18490
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.GenericRejection

def step (v : List Bool) (g : Gate) := v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

def Splits (a b c : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true ∨ c.getD i false = true

lemma appended (a : List Bool) (v : Bool) (i : ℕ) :
    (a ++ [v]).getD i false = if i = a.length then v else a.getD i false := by
  by_cases h : i < a.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append, h, Nat.ne_of_lt h]
  · by_cases he : i = a.length
    · subst i
      simp [List.getD_eq_getElem?_getD, List.getElem?_append]
    · have hp : 0 < i - a.length := by omega
      simp [List.getD_eq_getElem?_getD, List.getElem?_append, h, he, List.getElem?_eq_none_iff.mpr (by omega : a.length ≤ i), List.getElem?_eq_none_iff.mpr (by change 1 ≤ i - a.length; omega : [v].length ≤ i - a.length)]

lemma propagate (gs : List Gate) (only : ∀ g ∈ gs, g.op = GateOp.or)
    (a b c : List Bool) (hb : a.length = b.length) (hc : a.length = c.length) (hs : Splits a b c) :
    Splits (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact hs
  | cons g tail ih =>
    apply ih (fun q hq => only q (by simp [hq]))
    · simpa [step] using hb
    · simpa [step] using hc
    · intro i hi
      simp only [step, appended, ← hb, ← hc] at hi ⊢
      split at hi
      next h =>
        simp only [h, if_pos, only g (by simp), GateOp.eval, List.any_map, List.any_eq_true] at hi ⊢
        obtain ⟨j,hj,hv⟩ := hi
        rcases hs j hv with hjb | hjc
        · exact Or.inl ⟨j,hj,hjb⟩
        · exact Or.inr ⟨j,hj,hjc⟩
      next h => simpa [h] using hs i hi

lemma ofFnSplits {n : ℕ} (b c : Fin n → Bool) :
    Splits (List.ofFn fun i => b i || c i) (List.ofFn b) (List.ofFn c) := by
  intro i
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h]
end PEqualNP.Outside.L_meta_18490

open PEqualNP.Outside.L_meta_18490 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.L_meta_18490 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (∀ (x4 : Fin (42 : ℕ) → Bool), x1.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (42 : ℕ)) (x6 : Fin (42 : ℕ)), (↑x5 < (21 : ℕ) ∧ (21 : ℕ) ≤ ↑x6 ∧ (↑x6 + (21 : ℕ) - ↑x5) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ x4 x5 = Bool.true ∧ x4 x6 = Bool.true) → ∃ (x5 : Finset (Finset (Fin (21 : ℕ)) × Finset (Fin (21 : ℕ)))), (∀ x6 ∈ x5, x6.1.Nonempty ∧ x6.2.Nonempty ∧ ∀ x8 ∈ x6.1, ∀ x10 ∈ x6.2, (↑x10 + (21 : ℕ) - ↑x8) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)]) ∧ (∀ (x6 x7 : Fin (21 : ℕ)), (↑x7 + (21 : ℕ) - ↑x6) % (21 : ℕ) ∈ [(0 : ℕ), (5 : ℕ), (7 : ℕ), (17 : ℕ), (20 : ℕ)] → ∃ x9 ∈ x5, x6 ∈ x9.1 ∧ x7 ∈ x9.2) ∧ ∑ x6 ∈ x5, (x6.1.card + x6.2.card - (1 : ℕ)) ≤ List.countP (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => PEqualNP.CircuitLowerBounds.GateOp.casesOn x6.op Bool.false Bool.true Bool.false (fun (x7 : ℕ) => Bool.false) Bool.false) x1.gates + (1 : ℕ)) := by
  intro C hm hn hi
  exfalso
  have only (g : Gate) (hg : g ∈ C.gates) : g.op = GateOp.or := by
    have hop : g.op = GateOp.and ∨ g.op = GateOp.or := (hm g hg).1
    rcases hop with ha | ho
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
      exact False.elim (hn ⟨j, hj.symm ▸ ha⟩)
    · exact ho
  let b : Fin 42 → Bool := fun j => decide (j = 0)
  let c : Fin 42 → Bool := fun j => decide (j = 21)
  have sp := propagate C.gates only _ _ _ (by simp) (by simp) (ofFnSplits b c) C.output
  change C.eval _ = true → C.eval _ = true ∨ C.eval _ = true at sp
  have both : C.eval (List.ofFn fun i => b i || c i) = true := (hi _).2 (by decide +kernel)
  rcases sp both with hb | hc
  · have w := (hi b).1 hb
    revert w
    decide +kernel
  · have w := (hi c).1 hc
    revert w
    decide +kernel
