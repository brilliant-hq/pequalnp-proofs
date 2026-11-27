import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def c7 (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0)

def foldWires (gs : List Gate) (acc : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc

lemma foldWires_cons (g : Gate) (gs : List Gate) (acc : List Bool) :
    foldWires (g :: gs) acc =
      foldWires gs (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) := rfl

lemma foldWires_getD_lt (gs : List Gate) (acc : List Bool) (k : ℕ) (hk : k < acc.length) :
    (foldWires gs acc).getD k false = acc.getD k false := by
  induction gs generalizing acc with
  | nil => simp [foldWires]
  | cons g gs ih =>
    rw [foldWires_cons]
    have hk' : k < (acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]).length := by
      simp; omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma foldWires_agree (gs : List Gate) (w1 w2 : List Bool)
    (hlen : w1.length = w2.length)
    (h2_1 : w1.getD 2 false = true)
    (h2_2 : w2.getD 2 false = true)
    (h2_lt : 2 < w1.length)
    (hagree : ∀ u : ℕ, u ≠ 0 → w1.getD u false = w2.getD u false)
    (hgate : ∀ g ∈ gs, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ 2 ∈ g.inputs)) :
    ∀ u : ℕ, u ≠ 0 → (foldWires gs w1).getD u false = (foldWires gs w2).getD u false := by
  induction gs generalizing w1 w2 with
  | nil =>
    exact hagree
  | cons g gs ih =>
    rw [foldWires_cons, foldWires_cons]
    have hbit : g.op.eval (g.inputs.map fun i => w1.getD i false) =
        g.op.eval (g.inputs.map fun i => w2.getD i false) := by
      rcases hgate g (List.mem_cons_self ..) with hno0 | ⟨hor, h2mem⟩
      · congr 1
        apply List.map_congr_left
        intro u hu
        exact hagree u (fun h => hno0 (h ▸ hu))
      · rw [hor]
        have h1 : GateOp.eval GateOp.or (g.inputs.map fun i => w1.getD i false) = true := by
          simp only [GateOp.eval, List.any_eq_true, List.mem_map]
          exact ⟨true, ⟨2, h2mem, h2_1⟩, rfl⟩
        have h2 : GateOp.eval GateOp.or (g.inputs.map fun i => w2.getD i false) = true := by
          simp only [GateOp.eval, List.any_eq_true, List.mem_map]
          exact ⟨true, ⟨2, h2mem, h2_2⟩, rfl⟩
        rw [h1, h2]
    let v := g.op.eval (g.inputs.map fun i => w1.getD i false)
    rw [← hbit]
    apply ih (w1 ++ [v]) (w2 ++ [v])
    · simp [hlen]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2_lt, ← List.getD_eq_getElem?_getD]
      exact h2_1
    · have h2_lt2 : 2 < w2.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h2_lt2, ← List.getD_eq_getElem?_getD]
      exact h2_2
    · simp; omega
    · intro u hu
      by_cases hlt : u < w1.length
      · have hlt2 : u < w2.length := by omega
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
          List.getElem?_append_left hlt2]
        simpa [List.getD_eq_getElem?_getD] using hagree u hu
      · by_cases heq : u = w1.length
        · subst heq
          simp [List.getD_eq_getElem?_getD, hlen]
        · have hgt1 : (w1 ++ [v]).length ≤ u := by simp; omega
          have hgt2 : (w2 ++ [v]).length ≤ u := by simp; omega
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hgt1,
                List.getElem?_eq_none hgt2]
    · intro g' hg'
      exact hgate g' (List.mem_cons_of_mem _ hg')

lemma main_proof :
    ¬ (∃ (C : Circuit) (i k : Fin C.gates.length),
      i.val = 8 ∧ FanInTwo C ∧ C.size = 10 ∧
      (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = c7 x) ∧
      0 ∈ (C.gates.get i).inputs ∧
      (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧
      (C.gates.get i).op = GateOp.or ∧
      (C.gates.get k).op = GateOp.and ∧
      i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧
      2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧
      ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧
        (C.wires (List.ofFn x)).getD 2 false = true) := by
  rintro ⟨C, i, k, _, _, _, heval, _, honly0, hori, _, _, _, h2mem, _, _, _⟩
  have hout_ne0 : C.output ≠ 0 := by
    intro h0
    let x : Fin 7 → Bool := fun t => decide (t.val = 1 ∨ t.val = 2)
    have h := heval x
    unfold Circuit.eval Circuit.wires at h
    rw [h0] at h
    change (foldWires C.gates (List.ofFn x)).getD 0 false = c7 x at h
    rw [foldWires_getD_lt C.gates (List.ofFn x) 0 (by simp)] at h
    have hcontra : (List.ofFn x).getD 0 false ≠ c7 x := by decide
    exact hcontra h
  let xlo : Fin 7 → Bool := fun t => decide (t.val = 2 ∨ t.val = 6)
  let xhi : Fin 7 → Bool := fun t => decide (t.val = 0 ∨ t.val = 2 ∨ t.val = 6)
  have hgate : ∀ g ∈ C.gates, 0 ∉ g.inputs ∨ (g.op = GateOp.or ∧ 2 ∈ g.inputs) := by
    intro g hg
    by_cases h0 : 0 ∈ g.inputs
    · right
      rcases List.mem_iff_get.mp hg with ⟨j, rfl⟩
      have hji : j = i := honly0 j h0
      subst hji
      exact ⟨hori, h2mem⟩
    · left
      exact h0
  have hagree_out : (foldWires C.gates (List.ofFn xlo)).getD C.output false =
      (foldWires C.gates (List.ofFn xhi)).getD C.output false := by
    apply foldWires_agree C.gates (List.ofFn xlo) (List.ofFn xhi)
    · simp
    · decide
    · decide
    · simp
    · intro u hu
      by_cases hlt : u < 7
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_ofFn, List.getElem?_ofFn]
        simp [hlt, xlo, xhi, hu]
      · have h1 : (List.ofFn xlo).length ≤ u := by simp; omega
        have h2 : (List.ofFn xhi).length ≤ u := by simp; omega
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_none h1, List.getElem?_eq_none h2]
    · exact hgate
    · exact hout_ne0
  have h1 : (foldWires C.gates (List.ofFn xlo)).getD C.output false = c7 xlo := heval xlo
  have h2 : (foldWires C.gates (List.ofFn xhi)).getD C.output false = c7 xhi := heval xhi
  rw [h1, h2] at hagree_out
  have hneq : c7 xlo ≠ c7 xhi := by decide
  exact hneq hagree_out

end PEqualNP.Outside.L_meta_29904_aux

theorem PEqualNP.Outside.L_meta_29904 : (¬ (∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (i k : Fin C.gates.length), i.val = 8 ∧ PEqualNP.MetaComplexity.FanInTwo C ∧ C.size = 10 ∧ (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0))) ∧ 0 ∈ (C.gates.get i).inputs ∧ (∀ j : Fin C.gates.length, 0 ∈ (C.gates.get j).inputs → j = i) ∧ (C.gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ (C.gates.get k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ i.val < k.val ∧ 7 + i.val ∈ (C.gates.get k).inputs ∧ 2 ∈ (C.gates.get i).inputs ∧ 2 ≠ 0 ∧ 2 < 7 + i.val ∧ ∃ x : Fin 7 → Bool, x 0 = false ∧ x 1 = false ∧ x 6 = false ∧ (C.wires (List.ofFn x)).getD 2 false = true)) :=
  PEqualNP.Outside.L_meta_29904_aux.main_proof
