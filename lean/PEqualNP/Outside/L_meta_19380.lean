import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19380
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

theorem gL {n : ℕ} (u i : Fin n) (v : Fin n) :
    (oneEach u v).getD i false = decide (u = i) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, eq_comm]

theorem gR {n : ℕ} (u : Fin n) (v j : Fin n) :
    (oneEach u v).getD (n + j) false = decide (v = j) := by
  simp [oneEach, List.getD_eq_getElem?_getD, eq_comm]

end PEqualNP.Outside.L_meta_19380


open PEqualNP.Outside.L_meta_19380 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19380 : ∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (u.val = 1 ∧ ¬ (v.val + 1 = n ∨ v.val + 2 = n)) ∨ (2 ≤ u.val ∧ v.val + 1 ≠ n))) C := by
  intro n hn
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  let c : Fin n := ⟨n-2,by omega⟩
  let d : Fin n := ⟨n-1,by omega⟩
  refine ⟨⟨[⟨.or,[n+(n-2),n+(n-1)]⟩,⟨.or,[0,n+(n-1)]⟩,⟨.and,[1,n+n]⟩,
    ⟨.or,[n+n+1,n+n+2]⟩,⟨.and,[0,n+n]⟩,⟨.not,[n+n+3]⟩,
    ⟨.or,[n+n+4,n+n+5]⟩],n+n+6⟩, ?_, le_rfl, ?_⟩
  · intro g hg
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp
  · intro u v
    have hl : (PEqualNP.Represents.oneEach u v).length = n+n := by simp [PEqualNP.Represents.oneEach]
    have h0 : (PEqualNP.Represents.oneEach u v).getD 0 false = decide (u.val=0) := by simpa [a,Fin.ext_iff] using gL u a v
    have h1 : (PEqualNP.Represents.oneEach u v).getD 1 false = decide (u.val=1) := by simpa [b,Fin.ext_iff] using gL u b v
    have h3 : (PEqualNP.Represents.oneEach u v).getD (n+(n-2)) false = decide (v.val=n-2) := by simpa [c,Fin.ext_iff] using gR u v c
    have h4 : (PEqualNP.Represents.oneEach u v).getD (n+(n-1)) false = decide (v.val=n-1) := by simpa [d,Fin.ext_iff] using gR u v d
    generalize PEqualNP.Represents.oneEach u v = l at hl h0 h1 h3 h4
    have hlt0 : 0 < l.length := by omega
    have hlt1 : 1 < l.length := by omega
    have hlt3 : n+(n-2) < l.length := by omega
    have hlt4 : n+(n-1) < l.length := by omega
    rw [show n+n=l.length from hl.symm]
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval,PEqualNP.CircuitLowerBounds.Circuit.wires,
      List.foldl,List.map,List.getD_append _ _ _ _ hlt0,List.getD_append _ _ _ _ hlt1,
      List.getD_append _ _ _ _ hlt3,List.getD_append _ _ _ _ hlt4,h0,h1,h3,h4]
    simp [List.getD_eq_getElem?_getD,PEqualNP.CircuitLowerBounds.GateOp.eval, List.getElem?_append_left hlt0, List.getElem?_append_left hlt1, List.getElem?_append_left hlt3, List.getElem?_append_left hlt4]
    by_cases hu0 : u.val=0 <;> by_cases hu1 : u.val=1 <;>
      by_cases hv1 : v.val=n-2 <;> by_cases hv2 : v.val=n-1 <;>
      simp_all <;> try omega
