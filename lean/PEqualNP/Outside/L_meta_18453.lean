import Mathlib.Data.List.GetD
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18453

open PEqualNP.CircuitLowerBounds

private def Joined (a b c : List Bool) : Prop :=
  b.length = a.length ∧ c.length = a.length ∧
    ∀ i, c.getD i false = (a.getD i false || b.getD i false)

private theorem joinedInputs {n : ℕ} (a b : Fin n → Bool) :
    Joined (List.ofFn a) (List.ofFn b) (List.ofFn fun i => a i || b i) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  by_cases h : i < n
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

private theorem anyJoined {a b c : List Bool} (h : Joined a b c) (inputs : List ℕ) :
    (inputs.map (fun i => c.getD i false)).any id =
    ((inputs.map (fun i => a.getD i false)).any id ||
     (inputs.map (fun i => b.getD i false)).any id) := by
  induction inputs with
  | nil => rfl
  | cons i rest ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    rw [h.2.2 i, ih]
    ac_rfl

private theorem joinedAppend {a b c : List Bool} (h : Joined a b c) (x y : Bool) :
    Joined (a ++ [x]) (b ++ [y]) (c ++ [x || y]) := by
  rcases h with ⟨hb, hc, hw⟩
  refine ⟨by simp [hb], by simp [hc], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ (by simpa [hc] using hi),
        List.getD_append _ _ _ _ hi,
        List.getD_append _ _ _ _ (by simpa [hb] using hi)]
    exact hw i
  · have hn := Nat.le_of_not_lt hi
    rw [List.getD_append_right _ _ _ _ (by simpa [hc] using hn),
        List.getD_append_right _ _ _ _ hn,
        List.getD_append_right _ _ _ _ (by simpa [hb] using hn), hc, hb]
    cases i - a.length <;> simp

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem foldJoined (gates : List Gate) (hor : ∀ g ∈ gates, g.op = .or)
    {a b c : List Bool} (h : Joined a b c) :
    Joined (gates.foldl step a) (gates.foldl step b) (gates.foldl step c) := by
  induction gates generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hor q (List.mem_cons_of_mem g hq))
    simp only [step, hor g (List.mem_cons_self), GateOp.eval, anyJoined h]
    exact joinedAppend h _ _

private theorem outputJoined {n : ℕ} (C : Circuit) (hor : ∀ g ∈ C.gates, g.op = .or)
    (a b : Fin n → Bool) :
    C.eval (List.ofFn fun i => a i || b i) =
      (C.eval (List.ofFn a) || C.eval (List.ofFn b)) :=
  (foldJoined C.gates hor (joinedInputs a b)).2.2 C.output

end PEqualNP.Outside.L_meta_18453

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.HeptadCover PEqualNP.Outside.L_meta_18453 in
theorem PEqualNP.Outside.L_meta_18453 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → (¬∃ (x3 : Fin x1.gates.length), (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and) → PEqualNP.GenericRejection.ComputesIncidence PEqualNP.HeptadCover.singerLines3 x1 → PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.Ico (13 : ℕ) (26 : ℕ)) x1 (2 : ℕ) ∨ PEqualNP.CircuitLowerBounds.HasLineDegree (26 : ℕ) (Finset.range (13 : ℕ)) x1 (2 : ℕ) → (PEqualNP.MetaComplexity.NestedCover.gateAt x1 (x1.size - (1 : ℕ))).op = PEqualNP.CircuitLowerBounds.GateOp.or → (64 : ℕ) ≤ x1.size := by
  intro C hC noAnd correct _ _
  exfalso
  have hOr : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    have h := (hC g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
      exact (noAnd ⟨i, (congrArg Gate.op hi).trans h⟩).elim
    · exact h
  let a : Fin 26 → Bool := fun i => decide (i = 0)
  let b : Fin 26 → Bool := fun i => decide (i = 13)
  have ha : C.eval (List.ofFn a) = false := calc
    _ = C.eval (incidenceInput ({0} : Finset (Fin 13)) (∅ : Finset (Fin 13))) := by congr 1
    _ = false := (correct {0} ∅).trans (by decide +kernel)
  have hb : C.eval (List.ofFn b) = false := calc
    _ = C.eval (incidenceInput (∅ : Finset (Fin 13)) ({0} : Finset (Fin 13))) := by congr 1
    _ = false := (correct ∅ {0}).trans (by decide +kernel)
  have hab : C.eval (List.ofFn fun i => a i || b i) = true := calc
    _ = C.eval (incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13))) := by congr 1
    _ = true := (correct {0} {0}).trans (by decide +kernel)
  have h := outputJoined C hOr a b
  rw [ha, hb, hab] at h
  contradiction
