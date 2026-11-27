import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29868_aux

open PEqualNP.CircuitLowerBounds

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private theorem old_wire (w : List Bool) (b : Bool) (i : Nat) (hi : i < w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem fold_keeps_inputs (gs : List Gate) (w : List Bool) (i : Nat)
    (hi : i < w.length) : (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have next : i < (step w g).length := by simp [step]; omega
    exact (ih (step w g) next).trans (old_wire w _ i hi)

private theorem or_masked (w : List Bool) (g : Gate) (mask : Nat)
    (op : g.op = .or) (pin : mask ∈ g.inputs) (bit : w.getD mask false = true) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) = true := by
  rw [op]
  apply List.any_eq_true.mpr
  exact ⟨true, List.mem_map.mpr ⟨mask,pin,bit⟩,rfl⟩

private theorem masked_fold (gs : List Gate) (w v : List Bool) (mask : Nat)
    (legal : ∀g ∈ gs, 0 ∈ g.inputs → g.op = .or ∧ mask ∈ g.inputs)
    (lengths : w.length = v.length) (bound : mask < w.length)
    (leftMask : w.getD mask false = true) (rightMask : v.getD mask false = true)
    (same : ∀i, i ≠ 0 → w.getD i false = v.getD i false) :
    ∀i, i ≠ 0 → (gs.foldl step w).getD i false = (gs.foldl step v).getD i false := by
  induction gs generalizing w v with
  | nil => exact same
  | cons g gs ih =>
    let bit := g.op.eval (g.inputs.map (fun i => w.getD i false))
    have equalBit : bit = g.op.eval (g.inputs.map (fun i => v.getD i false)) := by
      by_cases usesZero : 0 ∈ g.inputs
      · obtain ⟨isOr,hasMask⟩ := legal g (by simp) usesZero
        exact (or_masked w g mask isOr hasMask leftMask).trans (or_masked v g mask isOr hasMask rightMask).symm
      · dsimp [bit]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact same i (fun zero => usesZero (zero ▸ hi))
    have left : step w g = w ++ [bit] := rfl
    have right : step v g = v ++ [bit] := by simp only [step, equalBit]
    have equalWires (i : Nat) (nonzero : i ≠ 0) :
        (w ++ [bit]).getD i false = (v ++ [bit]).getD i false := by
      by_cases inside : i < w.length
      · rw [old_wire w bit i inside, old_wire v bit i (by omega)]
        exact same i nonzero
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega), lengths]
    change ∀i, i ≠ 0 → (gs.foldl step (step w g)).getD i false = (gs.foldl step (step v g)).getD i false
    rw [left,right]
    exact ih (w ++ [bit]) (v ++ [bit]) (fun h hm => legal h (List.mem_cons_of_mem _ hm))
      (by simp [lengths]) (by simp; omega)
      ((old_wire w bit mask bound).trans leftMask)
      ((old_wire v bit mask (by omega)).trans rightMask) equalWires

end PEqualNP.Outside.L_meta_29868_aux

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_29868_aux in
theorem PEqualNP.Outside.L_meta_29868 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 6 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 5 ∈ (C.gates.get i).inputs ∧ 5 ≠ 0 ∧ 5 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 5 false = true)) := by
  rintro ⟨C,i,k,_,_,_,correct,_,onlyZero,isOr,_,_,_,hasFive,_,_,_⟩
  let x : Fin 7 → Bool := fun j => decide (j = 1 ∨ j = 5)
  let y : Fin 7 → Bool := fun j => decide (j = 0 ∨ j = 1 ∨ j = 5)
  let z : Fin 7 → Bool := fun j => decide (j = 1 ∨ j = 2)
  have xList : List.ofFn x = [false,true,false,false,false,true,false] := by decide +kernel
  have yList : List.ofFn y = [true,true,false,false,false,true,false] := by decide +kernel
  have xResult : C.eval (List.ofFn x) = false := by simpa [x] using correct x
  have yResult : C.eval (List.ofFn y) = true := by simpa [y] using correct y
  have outputNonzero : C.output ≠ 0 := by
    intro zero
    have zExpected : C.eval (List.ofFn z) = true := by simpa [z] using correct z
    have zZero : (List.ofFn z).getD 0 false = false := by decide +kernel
    have stays := fold_keeps_inputs C.gates (List.ofFn z) 0 (by simp)
    change (C.gates.foldl step (List.ofFn z)).getD C.output false = true at zExpected
    rw [zero, stays, zZero] at zExpected
    cases zExpected
  have gateMask (g : Gate) (member : g ∈ C.gates) (usesZero : 0 ∈ g.inputs) :
      g.op = .or ∧ 5 ∈ g.inputs := by
    obtain ⟨j,rfl⟩ := List.mem_iff_get.mp member
    have ji := onlyZero j usesZero
    subst j
    exact ⟨isOr,hasFive⟩
  have inputAgreement : ∀j,j ≠ 0 → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
    intro j nonzero
    rw [xList,yList]
    cases j with
    | zero => exact False.elim (nonzero rfl)
    | succ j => rfl
  have sameEval : C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
    exact masked_fold C.gates (List.ofFn x) (List.ofFn y) 5 gateMask
      (by simp) (by simp) (by rw [xList]; rfl) (by rw [yList]; rfl) inputAgreement C.output outputNonzero
  rw [xResult,yResult] at sameEval
  cases sameEval
