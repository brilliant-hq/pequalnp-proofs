import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20821.Aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_append (gs hs : List Gate) (w : List Bool) :
    wf (gs ++ hs) w = wf hs (wf gs w) := by
  simp [wf, List.foldl_append]

lemma wf_length (gs : List Gate) (w : List Bool) :
    (wf gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wf]
  | cons g gs ih =>
    have h := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at h ⊢
    rw [h]
    simp
    omega

lemma wf_getD_lt (hs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wf hs w).getD i false = w.getD i false := by
  induction hs generalizing w with
  | nil => rfl
  | cons g hs ih =>
    have h := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (by simp; omega)
    simp only [wf, List.foldl_cons] at h ⊢
    rw [h, List.getD_append _ _ _ _ hi]

lemma wf_getD_gate (C : Circuit) (init : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires init).getD (init.length + j) false =
      (gateAt C j).op.eval
        ((gateAt C j).inputs.map fun w => (wf (C.gates.take j) init).getD w false) := by
  have hg : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  have hsplit : C.gates = (C.gates.take j ++ [C.gates[j]]) ++ C.gates.drop (j + 1) := by
    rw [← List.take_succ_eq_append_getElem hj, List.take_append_drop]
  let w0 := wf (C.gates.take j) init
  have hw0 : w0.length = init.length + j := by
    simp [w0, wf_length, List.length_take, Nat.min_eq_left hj.le]
  change (wf C.gates init).getD (init.length + j) false = _
  conv_lhs => rw [hsplit, wf_append, wf_append]
  have hstep : wf [C.gates[j]] w0 =
      w0 ++ [C.gates[j].op.eval (C.gates[j].inputs.map fun i => w0.getD i false)] := rfl
  rw [hstep, wf_getD_lt _ _ _ (by simp [hw0]), ← hw0, List.getD_append_right _ _ _ _ le_rfl]
  simp only [Nat.sub_self, List.getD_cons_zero, hg, w0]

lemma wf_take_getD (C : Circuit) (init : List Bool) (j i : ℕ) (hj : j < C.gates.length)
    (hi : i < init.length + j) :
    (wf (C.gates.take j) init).getD i false = (C.wires init).getD i false := by
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  change _ = (wf C.gates init).getD i false
  conv_rhs => rw [hsplit, wf_append]
  exact (wf_getD_lt (C.gates.drop j) (wf (C.gates.take j) init) i
    (by rw [wf_length, List.length_take, Nat.min_eq_left hj.le]; omega)).symm

lemma wires_getD_input (C : Circuit) {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  change (wf C.gates (List.ofFn x)).getD i false = _
  rw [wf_getD_lt _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

end PEqualNP.Outside.L_meta_20821.Aux

open PEqualNP.Outside.L_meta_20821.Aux PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover in
theorem PEqualNP.Outside.L_meta_20821 : (∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (S Rg : Finset ℕ),
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C → (∀ i ∈ S, i < m) → (∀ j ∈ Rg, j < C.size) →
  (∀ j ∈ Rg,
    (((PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.length = 2) ∧
    ∀ w ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs, w ∈ S ∨ (m ≤ w ∧ w - m ∈ Rg)) →
  ∀ x : Fin m → Bool, (∀ i : Fin m, (i : ℕ) ∈ S → x i = false) →
    ∀ j ∈ Rg, (C.wires (List.ofFn x)).getD (m + j) false = false) := by
  intro m C S Rg hrb hS hRg hgate x hx j hj
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hjlen : j < C.gates.length := hRg j hj
    obtain ⟨⟨hop, hlen⟩, hinp⟩ := hgate j hj
    have hval := wf_getD_gate C (List.ofFn x) j hjlen
    rw [List.length_ofFn] at hval
    rw [hval]
    have hfalse : ∀ w ∈ (gateAt C j).inputs,
        (wf (C.gates.take j) (List.ofFn x)).getD w false = false := by
      intro w hw
      have hlt : w < m + j := hrb j hjlen w hw
      rw [wf_take_getD C (List.ofFn x) j w hjlen (by simpa using hlt)]
      rcases hinp w hw with hwS | ⟨hmw, hwRg⟩
      · have hwm : w < m := hS w hwS
        rw [wires_getD_input C x w hwm]
        exact hx ⟨w, hwm⟩ hwS
      · have hsub : w - m < j := by omega
        have hadd : m + (w - m) = w := by omega
        rw [← hadd]
        exact ih (w - m) hsub hwRg
    rcases hlist : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
    · simp [hlist] at hlen
    · simp [hlist] at hlen
    · have ha : (wf (C.gates.take j) (List.ofFn x)).getD a false = false :=
        hfalse a (by simp [hlist])
      have hb : (wf (C.gates.take j) (List.ofFn x)).getD b false = false :=
        hfalse b (by simp [hlist])
      rcases hop with hop | hop <;>
        simp only [hop, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          List.any_cons, List.any_nil, id, ha, hb, Bool.and_true, Bool.false_and, Bool.and_false,
          Bool.or_false, Bool.false_or]
    · simp [hlist] at hlen
