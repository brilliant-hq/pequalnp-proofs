import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18771

open PEqualNP.CircuitLowerBounds

private theorem inputRead (gates : List Gate) (w : List Bool) (i : ℕ)
    (h : i < w.length) :
    (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) w).getD i false
      = w.getD i false := by
  induction gates generalizing w with
  | nil => rfl
  | cons g tail ih =>
    rw [List.foldl_cons, ih, List.getD_append _ _ _ _ h]
    simp
    omega

end PEqualNP.Outside.L_meta_18771

open PEqualNP.Outside.L_meta_18771 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_18771 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.output < (10 : ℕ) → PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (19 : ℕ) → (∃ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x6) ≠ [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => x6 (Fin.ofNat (10 : ℕ) (x7 / (10 : ℕ))) && x6 (Fin.ofNat (10 : ℕ) (x7 % (10 : ℕ))) := by
  intro C ho _ _ _
  let j : Fin 10 := ⟨C.output,ho⟩
  let x : Fin 10 → Bool := fun k => decide (k = j)
  have good : C.eval (List.ofFn x) = true := by
    change (List.foldl _ (List.ofFn x) C.gates).getD C.output false = true
    have ok : C.output < (List.ofFn x).length := by simpa using ho
    rw [inputRead _ _ _ ok, List.getD_eq_getElem _ _ ok, List.getElem_ofFn]
    exact decide_eq_true rfl
  refine ⟨x, ?_⟩
  have empty : ∀ i : Fin 10, ([(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (49 : ℕ), (57 : ℕ), (79 : ℕ), (96 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x7 : ℕ) => (fun k => decide (k = i)) (Fin.ofNat (10 : ℕ) (x7 / (10 : ℕ))) && (fun k => decide (k = i)) (Fin.ofNat (10 : ℕ) (x7 % (10 : ℕ)))) = false := by decide +kernel
  rw [good, empty j]
  decide

