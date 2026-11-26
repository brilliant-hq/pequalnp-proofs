import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18896_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

private lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp
    omega

private lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).getD j false =
      acc.getD j false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (acc ++ [_]) (by simp; omega)]
    rw [List.getD_append _ _ _ _ hj]

private lemma foldl_wires_append (gs1 gs2 : List Gate) (acc : List Bool) :
    ((gs1 ++ gs2).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc) =
      gs2.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (gs1.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc) :=
  List.foldl_append

private lemma wires_getD_gate (C : Circuit) (inp : List Bool) (k : ℕ) (hk : k < C.gates.length)
    (hreads : ∀ i ∈ C.gates[k].inputs, i < inp.length + k) :
    (C.wires inp).getD (inp.length + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => (C.wires inp).getD i false) := by
  unfold Circuit.wires
  have hsplit : C.gates = C.gates.take k ++ (C.gates[k] :: C.gates.drop (k + 1)) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [← h2, h1]
  set f : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  set pre := (C.gates.take k).foldl f inp
  have hpre_len : pre.length = inp.length + k := by
    dsimp only [pre, f]
    rw [foldl_wires_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hfull : C.gates.foldl f inp = (C.gates.drop (k + 1)).foldl f (f pre C.gates[k]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_pre : ∀ i < inp.length + k, (C.gates.foldl f inp).getD i false = pre.getD i false := by
    intro i hi
    rw [hfull, foldl_wires_getD_lt _ _ _ (by simp [f, hpre_len]; omega)]
    rw [List.getD_append _ _ _ _ (by omega)]
  have hval : (C.gates.foldl f inp).getD (inp.length + k) false =
      C.gates[k].op.eval (C.gates[k].inputs.map fun i => pre.getD i false) := by
    rw [hfull, foldl_wires_getD_lt _ _ _ (by simp [f, hpre_len])]
    simp only [f, ← hpre_len]
    rw [List.getD_append_right _ _ _ _ le_rfl]
    simp
  rw [hval]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (hlt_pre i (hreads i hi)).symm

private lemma getD_ofFn_lt {n : ℕ} (f : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn f).getD w false = f ⟨w, hw⟩ := by
  simp [List.getD_eq_getElem?_getD, hw]

private lemma getD_ge_len (l : List Bool) (i : ℕ) (hi : l.length ≤ i) :
    l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

theorem compact_main :
    ∀ (n m : ℕ) (C : Circuit) (p : Fin n → Option (Fin m)), IsAO2 n C →
      let top := C.wires (List.ofFn (fun i => (p i).isSome))
      ∃ D : Circuit, IsAO2 m D ∧
        D.size ≤ (C.gates.filter (fun g => g.inputs.all (fun i => top.getD i false))).length ∧
        ∀ x : Fin m → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (fun i => (p i).elim false x)) := by
  intro n m C p hAO
  dsimp only
  set top := C.wires (List.ofFn (fun i => (p i).isSome))
  set P : Gate → Bool := fun g => g.inputs.all (fun i => top.getD i false)
  have hStep : ∀ k, k ≤ C.gates.length →
      ∃ (dg : List Gate) (wmap : ℕ → Option ℕ),
        IsAO2 m ⟨dg, 0⟩ ∧
        dg.length ≤ ((C.gates.take k).filter P).length ∧
        (∀ w < n + k, match wmap w with
          | none => top.getD w false = false
          | some w' => top.getD w false = true ∧ w' < m + dg.length) ∧
        (∀ (x : Fin m → Bool) (w : ℕ), w < n + k →
          (match wmap w with
            | none => false
            | some w' => (Circuit.wires ⟨dg, 0⟩ (List.ofFn x)).getD w' false) =
          (C.wires (List.ofFn (fun i => (p i).elim false x))).getD w false) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : w < n then (p ⟨w, h⟩).map Fin.val else none, ?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_⟩
        · intro g hg; simp at hg
        · intro j hj; simp at hj
        · intro g hg; simp at hg
      · simp
      · intro w hw
        have hwn : w < n := by omega
        have htopw : top.getD w false = (p ⟨w, hwn⟩).isSome := by
          simp only [top, Circuit.wires]
          rw [foldl_wires_getD_lt _ _ _ (by simp [hwn])]
          exact getD_ofFn_lt _ w hwn
        simp only [hwn, dite_true]
        cases hp : p ⟨w, hwn⟩ with
        | none =>
          dsimp only [Option.map_none]
          rw [htopw, hp]
          rfl
        | some j =>
          dsimp only [Option.map_some]
          exact ⟨by rw [htopw, hp]; rfl, by omega⟩
      · intro x w hw
        have hwn : w < n := by omega
        have hcw : (C.wires (List.ofFn (fun i => (p i).elim false x))).getD w false = (p ⟨w, hwn⟩).elim false x := by
          unfold Circuit.wires
          rw [foldl_wires_getD_lt _ _ _ (by simp [hwn])]
          exact getD_ofFn_lt _ w hwn
        simp only [hwn, dite_true, hcw]
        cases hp : p ⟨w, hwn⟩ with
        | none => rfl
        | some j =>
          simp only [Option.map_some, Option.elim_some, Circuit.wires, List.foldl_nil]
          exact getD_ofFn_lt x j.val j.isLt
    | succ k ih =>
      intro hk1
      have hk : k < C.gates.length := by omega
      obtain ⟨dg, wmap, hAOd, hlen, hbd, hev⟩ := ih (Nat.le_of_lt hk)
      set g := C.gates[k]
      have hg_mem : g ∈ C.gates := List.getElem_mem hk
      have hgop : g.op = GateOp.and ∨ g.op = GateOp.or := hAO.1 g hg_mem
      have hglen : g.inputs.length = 2 := hAO.2.2 g hg_mem
      have hgreads : ∀ i ∈ g.inputs, i < n + k := by
        intro i hi
        have hrb := hAO.2.1 k hk i
        have hga : gateAt C k = g := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          rfl
        rw [hga] at hrb
        exact hrb hi
      have htake : C.gates.take (k + 1) = C.gates.take k ++ [g] := List.take_succ_eq_append_getElem hk
      have hfilt : ((C.gates.take (k + 1)).filter P).length =
          ((C.gates.take k).filter P).length + (if P g then 1 else 0) := by
        rw [htake, List.filter_append, List.length_append]
        simp only [List.filter_cons, List.filter_nil]
        cases P g <;> simp
      rcases hgi : g.inputs with _ | ⟨a, _ | ⟨b, _ | _⟩⟩
      · simp [hgi] at hglen
      · simp [hgi] at hglen
      · have ha : a < n + k := hgreads a (by simp [hgi])
        have hb : b < n + k := hgreads b (by simp [hgi])
        have htop_k : top.getD (n + k) false = g.op.eval [top.getD a false, top.getD b false] := by
          have h1 := wires_getD_gate C (List.ofFn (fun i => (p i).isSome)) k hk
            (by simpa [List.length_ofFn] using hgreads)
          simp only [List.length_ofFn] at h1
          simpa [top, g, hgi] using h1
        have hcw_k : ∀ x : Fin m → Bool,
            (C.wires (List.ofFn (fun i => (p i).elim false x))).getD (n + k) false =
            g.op.eval [(C.wires (List.ofFn (fun i => (p i).elim false x))).getD a false,
                       (C.wires (List.ofFn (fun i => (p i).elim false x))).getD b false] := by
          intro x
          have h1 := wires_getD_gate C (List.ofFn (fun i => (p i).elim false x)) k hk
            (by simpa [List.length_ofFn] using hgreads)
          simp only [List.length_ofFn] at h1
          simpa [g, hgi] using h1
        have hbda := hbd a ha
        have hbdb := hbd b hb
        cases hma : wmap a with
        | none =>
          rw [hma] at hbda
          cases hmb : wmap b with
          | none =>
            rw [hmb] at hbdb
            refine ⟨dg, fun w => if w = n + k then none else wmap w, hAOd, ?_, ?_, ?_⟩
            · rw [hfilt]; omega
            · intro w hw
              by_cases heq : w = n + k
              · subst heq
                simp only [ite_true]
                rw [htop_k, hbda, hbdb]
                rcases hgop with h | h <;> rw [h] <;> rfl
              · simp only [heq, ite_false]
                exact hbd w (by omega)
            · intro x w hw
              by_cases heq : w = n + k
              · subst heq
                have heva := hev x a ha; rw [hma] at heva; dsimp only at heva
                have hevb := hev x b hb; rw [hmb] at hevb; dsimp only at hevb
                simp only [ite_true]
                rw [hcw_k, ← heva, ← hevb]
                rcases hgop with h | h <;> rw [h] <;> rfl
              · simp only [heq, ite_false]
                exact hev x w (by omega)
          | some wb =>
            rw [hmb] at hbdb
            rcases hgop with h | h
            · refine ⟨dg, fun w => if w = n + k then none else wmap w, hAOd, ?_, ?_, ?_⟩
              · rw [hfilt]; omega
              · intro w hw
                by_cases heq : w = n + k
                · subst heq
                  simp only [ite_true]
                  rw [htop_k, hbda, hbdb.1, h]
                  rfl
                · simp only [heq, ite_false]
                  exact hbd w (by omega)
              · intro x w hw
                by_cases heq : w = n + k
                · subst heq
                  have heva := hev x a ha; rw [hma] at heva; dsimp only at heva
                  simp only [ite_true]
                  rw [hcw_k, ← heva, h]
                  rfl
                · simp only [heq, ite_false]
                  exact hev x w (by omega)
            · refine ⟨dg, fun w => if w = n + k then some wb else wmap w, hAOd, ?_, ?_, ?_⟩
              · rw [hfilt]; omega
              · intro w hw
                by_cases heq : w = n + k
                · subst heq
                  simp only [ite_true]
                  exact ⟨by rw [htop_k, hbda, hbdb.1, h]; rfl, hbdb.2⟩
                · simp only [heq, ite_false]
                  exact hbd w (by omega)
              · intro x w hw
                by_cases heq : w = n + k
                · subst heq
                  have heva := hev x a ha; rw [hma] at heva; dsimp only at heva
                  have hevb := hev x b hb; rw [hmb] at hevb; dsimp only at hevb
                  simp only [ite_true]
                  rw [hcw_k, ← heva, ← hevb, h]
                  simp [GateOp.eval]
                · simp only [heq, ite_false]
                  exact hev x w (by omega)
        | some wa =>
          rw [hma] at hbda
          cases hmb : wmap b with
          | none =>
            rw [hmb] at hbdb
            rcases hgop with h | h
            · refine ⟨dg, fun w => if w = n + k then none else wmap w, hAOd, ?_, ?_, ?_⟩
              · rw [hfilt]; omega
              · intro w hw
                by_cases heq : w = n + k
                · subst heq
                  simp only [ite_true]
                  rw [htop_k, hbda.1, hbdb, h]
                  rfl
                · simp only [heq, ite_false]
                  exact hbd w (by omega)
              · intro x w hw
                by_cases heq : w = n + k
                · subst heq
                  have hevb := hev x b hb; rw [hmb] at hevb; dsimp only at hevb
                  simp only [ite_true]
                  rw [hcw_k, ← hevb, h]
                  simp [GateOp.eval]
                · simp only [heq, ite_false]
                  exact hev x w (by omega)
            · refine ⟨dg, fun w => if w = n + k then some wa else wmap w, hAOd, ?_, ?_, ?_⟩
              · rw [hfilt]; omega
              · intro w hw
                by_cases heq : w = n + k
                · subst heq
                  simp only [ite_true]
                  exact ⟨by rw [htop_k, hbda.1, hbdb, h]; rfl, hbda.2⟩
                · simp only [heq, ite_false]
                  exact hbd w (by omega)
              · intro x w hw
                by_cases heq : w = n + k
                · subst heq
                  have heva := hev x a ha; rw [hma] at heva; dsimp only at heva
                  have hevb := hev x b hb; rw [hmb] at hevb; dsimp only at hevb
                  simp only [ite_true]
                  rw [hcw_k, ← heva, ← hevb, h]
                  simp [GateOp.eval]
                · simp only [heq, ite_false]
                  exact hev x w (by omega)
          | some wb =>
            rw [hmb] at hbdb
            let newG : Gate := ⟨g.op, [wa, wb]⟩
            let dg' : List Gate := dg ++ [newG]
            have hPg : P g = true := by
              simp only [P, hgi, List.all_cons, List.all_nil, Bool.and_true]
              rw [hbda.1, hbdb.1]
              rfl
            have hAOd' : IsAO2 m ⟨dg', 0⟩ := by
              refine ⟨?_, ?_, ?_⟩
              · intro g' hg'
                simp only [dg', List.mem_append, List.mem_singleton] at hg'
                rcases hg' with hg' | rfl
                · exact hAOd.1 g' hg'
                · exact hgop
              · intro j hj i hi
                simp only [dg', List.length_append, List.length_singleton] at hj
                by_cases hjlt : j < dg.length
                · have hga : gateAt ⟨dg', 0⟩ j = gateAt ⟨dg, 0⟩ j := by
                    unfold gateAt
                    simp only [dg']
                    rw [List.getD_append _ _ _ _ hjlt]
                  rw [hga] at hi
                  exact hAOd.2.1 j hjlt i hi
                · have hjeq : j = dg.length := by omega
                  subst hjeq
                  have hga : gateAt ⟨dg', 0⟩ dg.length = newG := by
                    unfold gateAt
                    simp only [dg']
                    rw [List.getD_append_right _ _ _ _ le_rfl]
                    simp
                  rw [hga] at hi
                  simp only [newG, List.mem_cons, List.not_mem_nil, or_false] at hi
                  rcases hi with rfl | rfl
                  · exact hbda.2
                  · exact hbdb.2
              · intro g' hg'
                simp only [dg', List.mem_append, List.mem_singleton] at hg'
                rcases hg' with hg' | rfl
                · exact hAOd.2.2 g' hg'
                · rfl
            refine ⟨dg', fun w => if w = n + k then some (m + dg.length) else wmap w, hAOd', ?_, ?_, ?_⟩
            · rw [hfilt, hPg]
              simp only [dg', List.length_append, List.length_singleton, ite_true]
              omega
            · intro w hw
              by_cases heq : w = n + k
              · subst heq
                simp only [ite_true, dg', List.length_append, List.length_singleton]
                refine ⟨?_, by omega⟩
                rw [htop_k, hbda.1, hbdb.1]
                rcases hgop with h | h <;> rw [h] <;> rfl
              · simp only [heq, ite_false]
                have hbw := hbd w (by omega)
                cases hmw : wmap w with
                | none => simpa [hmw] using hbw
                | some w' =>
                  rw [hmw] at hbw
                  dsimp only at hbw ⊢
                  refine ⟨hbw.1, ?_⟩
                  simp only [dg', List.length_append, List.length_singleton]
                  omega
            · intro x w hw
              have hdw_eq : ∀ w' < m + dg.length,
                  (Circuit.wires ⟨dg', 0⟩ (List.ofFn x)).getD w' false =
                  (Circuit.wires ⟨dg, 0⟩ (List.ofFn x)).getD w' false := by
                intro w' hw'
                unfold Circuit.wires
                simp only [dg', foldl_wires_append]
                rw [foldl_wires_getD_lt _ _ _ (by rw [foldl_wires_len, List.length_ofFn]; exact hw')]
              by_cases heq : w = n + k
              · subst heq
                simp only [ite_true]
                have hstep_d : (Circuit.wires ⟨dg', 0⟩ (List.ofFn x)).getD (m + dg.length) false =
                    g.op.eval [(Circuit.wires ⟨dg, 0⟩ (List.ofFn x)).getD wa false,
                               (Circuit.wires ⟨dg, 0⟩ (List.ofFn x)).getD wb false] := by
                  unfold Circuit.wires
                  simp only [dg', foldl_wires_append, List.foldl_cons, List.foldl_nil]
                  have hlen_pre : (dg.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)).length = m + dg.length := by
                    rw [foldl_wires_len, List.length_ofFn]
                  rw [← hlen_pre, List.getD_append_right _ _ _ _ le_rfl]
                  simp [newG]
                have heva := hev x a ha; rw [hma] at heva; dsimp only at heva
                have hevb := hev x b hb; rw [hmb] at hevb; dsimp only at hevb
                rw [hstep_d, heva, hevb, hcw_k]
              · simp only [heq, ite_false]
                have hbw := hbd w (by omega)
                have hevw := hev x w (by omega)
                cases hmw : wmap w with
                | none => simpa [hmw] using hevw
                | some w' =>
                  rw [hmw] at hbw hevw
                  dsimp only at hbw hevw ⊢
                  rw [hdw_eq w' hbw.2, hevw]
      · simp [hgi] at hglen
  obtain ⟨dg, wmap, hAOd, hlen, hbd, hev⟩ := hStep C.gates.length le_rfl
  rw [List.take_length] at hlen
  by_cases hout : C.output < n + C.gates.length
  · cases hmo : wmap C.output with
    | none =>
      refine ⟨⟨dg, m + dg.length⟩, hAOd, hlen, ?_⟩
      intro x
      unfold Circuit.eval
      have hevo := hev x C.output hout
      rw [hmo] at hevo
      dsimp only at hevo
      rw [← hevo]
      apply getD_ge_len
      unfold Circuit.wires
      rw [foldl_wires_len, List.length_ofFn]
    | some wout =>
      refine ⟨⟨dg, wout⟩, hAOd, hlen, ?_⟩
      intro x
      unfold Circuit.eval
      have hevo := hev x C.output hout
      rw [hmo] at hevo
      exact hevo
  · refine ⟨⟨dg, m + dg.length⟩, hAOd, hlen, ?_⟩
    intro x
    unfold Circuit.eval
    have h1 : (Circuit.wires ⟨dg, m + dg.length⟩ (List.ofFn x)).getD (m + dg.length) false = false := by
      apply getD_ge_len
      unfold Circuit.wires
      rw [foldl_wires_len, List.length_ofFn]
    have h2 : (C.wires (List.ofFn (fun i => (p i).elim false x))).getD C.output false = false := by
      apply getD_ge_len
      unfold Circuit.wires
      rw [foldl_wires_len, List.length_ofFn]
      omega
    rw [h1, h2]

end PEqualNP.Outside.L_meta_18896_aux

theorem PEqualNP.Outside.L_meta_18896 : ∀ (x1 x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin x1 → Option (Fin x2)),   PEqualNP.TopForm.IsAO2 x1 x3 →     have x6 : List Bool := x3.wires (List.ofFn fun (x6 : Fin x1) => (x4 x6).isSome);     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x2 x7 ∧ x7.size ≤ (List.filter (fun (x8 : PEqualNP.CircuitLowerBounds.Gate) => x8.inputs.all fun (x9 : ℕ) => x6.getD x9 Bool.false) x3.gates).length ∧ ∀ (x8 : Fin x2 → Bool), x7.eval (List.ofFn x8) = x3.eval (List.ofFn fun (x9 : Fin x1) => (x4 x9).elim Bool.false x8) := by
  exact PEqualNP.Outside.L_meta_18896_aux.compact_main
