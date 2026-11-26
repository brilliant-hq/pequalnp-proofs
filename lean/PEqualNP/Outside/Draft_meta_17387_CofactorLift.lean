import PEqualNP.Defs
namespace PEqualNP.Outside.Draft_meta_17387_CofactorLift
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def shift (g : Gate) : Gate := ⟨g.op, g.inputs.map Nat.succ⟩

theorem shiftStep (v : Bool) (xs : List Bool) (g : Gate) :
    step (v :: xs) (shift g) = v :: step xs g := by
  simp [step,shift,List.map_map,Function.comp_def,List.getD]

theorem shiftRun (v : Bool) (gs : List Gate) (xs : List Bool) :
    (gs.map shift).foldl step (v :: xs) = v :: gs.foldl step xs := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih => simpa only [List.map_cons,List.foldl_cons,shiftStep] using ih (step xs g)

theorem runLength (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simpa [step,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (step xs g)

theorem readSnoc (w : List Bool) (v : Bool) (i : Nat) :
    (w ++ [v]).getD i false = if i = w.length then v else w.getD i false := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons a w ih => cases i with
    | zero => simp [List.getD]
    | succ i => simpa [List.getD,List.getElem?_cons_succ] using ih i

def wrap (n : Nat) (C : Circuit) (p : Nat) : Circuit :=
  ⟨C.gates.map shift ++ [⟨.and,[0,p+1]⟩, ⟨.or,[n+C.size+1,C.output+1]⟩], n+C.size+2⟩

theorem shape (n : Nat) (C : Circuit) (p : Nat) (hC : FanInTwo C) :
    FanInTwo (wrap n C p) ∧ (wrap n C p).size = C.size+2 := by
  constructor
  · intro g hg
    simp only [wrap,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with ⟨g0,hm,rfl⟩ | rfl | rfl
    · exact ⟨(hC g0 hm).1, by simpa [shift] using (hC g0 hm).2⟩
    · simp
    · simp
  · simp [wrap,Circuit.size]

theorem value (n : Nat) (C : Circuit) (p : Nat) (out : C.output < n+C.size)
    (v : Bool) (xs : List Bool) (hlen : xs.length = n) :
    (wrap n C p).eval (v::xs) =
      ((v && (Circuit.mk C.gates p).eval xs) || C.eval xs) := by
  let w := C.gates.foldl step xs
  have hw : w.length = n+C.size := by simpa [w,hlen,Circuit.size] using runLength C.gates xs
  change (((C.gates.map shift ++ _).foldl step (v :: xs)).getD _ false) = _
  rw [List.foldl_append,shiftRun]
  let a := v && w.getD p false
  have hOne : step (v::w) ⟨.and,[0,p+1]⟩ = (v::w) ++ [a] := by
    simp [step,GateOp.eval,a,List.getD]
  change (step (step (v::w) _) _).getD _ false = (a || w.getD C.output false)
  rw [hOne]
  simp only [step,GateOp.eval,List.map_cons,List.map_nil,List.any_cons,List.any_nil,id_eq,Bool.or_false]
  rw [readSnoc,ite_eq_left (by simp [hw,wrap])]
  rw [readSnoc,ite_eq_left (by simp [hw]),readSnoc,ite_eq_right (by simp [hw]; omega)]
  rfl

end PEqualNP.Outside.Draft_meta_17387_CofactorLift

theorem PEqualNP.Outside.Draft_meta_17387_CofactorLift : ∀ (n : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) (p : Nat),
    PEqualNP.MetaComplexity.FanInTwo C → C.output < n+C.size →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size = C.size + 2 ∧
    ∀ (v : Bool) (xs : List Bool), xs.length = n → D.eval (v :: xs) =
      ((v && (PEqualNP.CircuitLowerBounds.Circuit.mk C.gates p).eval xs) || C.eval xs) := by
  intro n C p h ho
  exact ⟨Draft_meta_17387_CofactorLift.wrap n C p, (Draft_meta_17387_CofactorLift.shape n C p h).1,
    (Draft_meta_17387_CofactorLift.shape n C p h).2, Draft_meta_17387_CofactorLift.value n C p ho⟩
