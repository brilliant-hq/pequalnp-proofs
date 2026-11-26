import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18453
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

abbrev inp (X Y : Finset (Fin 13)) := incidenceInput X Y
lemma splitInputs : Splits (inp {0} {0}) (inp {0} ∅) (inp ∅ {0}) := by
  intro i
  by_cases h : i < 26
  · interval_cases i <;> decide
  · have bound : (inp {0} {0}).length ≤ i := by change 26 ≤ i; omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr bound]
    simp

lemma contradiction (C : Circuit) (hm : Monotone2 C)
    (hn : ¬ ∃ j : Fin C.gates.length, (C.gates.get j).op = GateOp.and)
    (hi : ComputesIncidence PEqualNP.HeptadCover.singerLines3 C) : False := by
  have only (g : Gate) (hg : g ∈ C.gates) : g.op = GateOp.or := by
    rcases (hm g hg).1 with ha | ho
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hg
      exact False.elim (hn ⟨j, hj.symm ▸ ha⟩)
    · exact ho
  have s := propagate C.gates only _ _ _ (by decide) (by decide) splitInputs C.output
  change C.eval _ = true → C.eval _ = true ∨ C.eval _ = true at s
  have hboth := hi {0} {0}
  have ha := hi {0} ∅
  have hb := hi ∅ {0}
  have h1 : incidenceFun PEqualNP.HeptadCover.singerLines3 {0} {0} = true := by decide
  have h2 : incidenceFun PEqualNP.HeptadCover.singerLines3 {0} ∅ = false := by decide
  have h3 : incidenceFun PEqualNP.HeptadCover.singerLines3 ∅ {0} = false := by decide
  rcases s (hboth.trans h1) with hl | hr
  · exact Bool.noConfusion ((ha.trans h2).symm.trans hl)
  · exact Bool.noConfusion ((hb.trans h3).symm.trans hr)
end PEqualNP.Outside.L_meta_18453

theorem PEqualNP.Outside.L_meta_18453 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (64 : ℕ) ≤ x1.size) := by
  intro C hm hn hi _ _
  exact (PEqualNP.Outside.L_meta_18453.contradiction C hm hn hi).elim
