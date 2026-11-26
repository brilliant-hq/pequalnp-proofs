import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

namespace PEqualNP.Outside.L_meta_20575

-- D marks the last two rows, V marks row zero together with those rows,
-- and P marks the first two columns.
def witness (n : Nat) : Circuit := ⟨[
  ⟨.or,[n-2,n-1]⟩,
  ⟨.or,[0,2*n+0]⟩,
  ⟨.or,[n,n+1]⟩,
  ⟨.and,[n+2,2*n+1]⟩,
  ⟨.or,[n+2,2*n+1]⟩,
  ⟨.not,[2*n+4]⟩,
  ⟨.and,[2*n+2,2*n+0]⟩,
  ⟨.or,[2*n+3,2*n+5]⟩,
  ⟨.or,[2*n+7,2*n+6]⟩],2*n+8⟩

theorem readRow {n} (u v : Fin n) (t : List Bool) (i : Nat) (hi : i<n) :
    (oneEach u v++t).getD i false = decide (u.val=i) := by
  have rowlen : i<(List.ofFn (fun j : Fin n => decide (j=u))).length := by simpa
  have fulllen : i<(oneEach u v).length := by simp [oneEach]; omega
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left fulllen]
  unfold oneEach
  rw [List.getElem?_append_left rowlen,List.getElem?_eq_getElem rowlen]
  simp [Fin.ext_iff,eq_comm]

theorem readCol {n} (u v : Fin n) (t : List Bool) (i : Nat) (hi : i<n) :
    (oneEach u v++t).getD (n+i) false = decide (v.val=i) := by
  have fulllen : n+i<(oneEach u v).length := by simp [oneEach]; omega
  rw [List.getD_eq_getElem?_getD,List.getElem?_append_left fulllen]
  simp [oneEach,hi,Fin.ext_iff,eq_comm]

theorem readGate {n} (u v : Fin n) (t : List Bool) (i : Nat) :
    (oneEach u v++t).getD (2*n+i) false=t.getD i false := by
  have len : (oneEach u v).length=2*n := by simp [oneEach]; omega
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_right (show (oneEach u v).length≤2*n+i by omega),len]

theorem correct {n : Nat} (hn : 4≤n) (u v : Fin n) :
    (witness n).eval (oneEach u v)=decide ((u.val=0 ∧ v.val=2) ∨
      (1≤u.val ∧ u.val+3≤n ∧ v.val≠2) ∨ (n≤u.val+2 ∧ v.val≤2)) := by
  let x := oneEach u v
  let d := decide (u.val=n-2) || decide (u.val=n-1)
  let a := decide (u.val=0) || d
  let p := decide (v.val=0) || decide (v.val=1)
  let y := decide (v.val=2)
  have ra (t : List Bool) := readRow u v t (n-2) (by omega)
  have rb (t : List Bool) := readRow u v t (n-1) (by omega)
  have rz (t : List Bool) := readRow u v t 0 (by omega)
  have cz (t : List Bool) : (x++t).getD n false=decide (v.val=0) := by simpa [x] using readCol u v t 0 (by omega)
  have co (t : List Bool) := readCol u v t 1 (by omega)
  have ct (t : List Bool) := readCol u v t 2 (by omega)
  have trace : (witness n).wires (x++[])=x++[
      d,a,p,y && a,y || a,!(y || a),p && d,
      (y && a) || !(y || a),((y && a) || !(y || a)) || (p && d)] := by
    simp only [x] at cz ⊢
    simp only [witness,Circuit.wires,List.foldl_cons,List.foldl_nil,GateOp.eval,
      List.map_cons,List.map_nil,List.any_cons,List.any_nil,List.all_cons,List.all_nil,
      List.headD_cons,id_eq,Bool.or_false,Bool.and_true,List.append_assoc,
      List.cons_append,List.nil_append,ra,rb,rz,co,ct,cz,readGate]
    rfl
  simp only [List.append_nil] at trace
  change ((witness n).wires x).getD (2*n+8) false=_
  rw [trace,readGate]
  change (((y && a) || !(y || a)) || (p && d))=_
  apply Bool.eq_iff_iff.mpr
  simp [a,d,p,y]
  omega

end PEqualNP.Outside.L_meta_20575

theorem PEqualNP.Outside.L_meta_20575 : ∀ n : ℕ, 4 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin n => decide ((u.val = 0 ∧ v.val = 2) ∨ (1 ≤ u.val ∧ u.val + 3 ≤ n ∧ v.val ≠ 2) ∨ (n ≤ u.val + 2 ∧ v.val ≤ 2))) C := by
  intro n hn
  refine ⟨PEqualNP.Outside.L_meta_20575.witness n,?_,by change 9 ≤ 9; rfl,fun u v => PEqualNP.Outside.L_meta_20575.correct hn u v⟩
  intro g hg
  simp [PEqualNP.Outside.L_meta_20575.witness] at hg
  rcases hg with h|h|h|h|h|h|h|h|h <;> subst g <;> simp
