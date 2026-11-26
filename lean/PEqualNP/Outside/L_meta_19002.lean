import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19002_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl wireStep x := rfl

lemma foldl_append (gs : List Gate) (w : List Bool) :
    ∃ T : List Bool, gs.foldl wireStep w = w ++ T ∧ T.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp, rfl⟩
  | cons g rest ih =>
    obtain ⟨T, hT, hlen⟩ := ih (wireStep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: T, ?_, by simp [hlen]⟩
    rw [List.foldl_cons, hT]
    simp [wireStep]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  obtain ⟨T, hT, hlen⟩ := foldl_append gs w
  rw [hT, List.length_append, hlen]

lemma getD_append_left_lt (a b : List Bool) (i : ℕ) (hi : i < a.length) :
    (a ++ b).getD i false = a.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_eq_false_of_le (a : List Bool) (i : ℕ) (hi : a.length ≤ i) :
    a.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]
  rfl

lemma wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [wires_eq_foldl]
  obtain ⟨T, hT, _⟩ := foldl_append C.gates (List.ofFn x)
  rw [hT, getD_append_left_lt _ _ i (by simpa using hi)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi)]
  simp

lemma wires_gate_prefix (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length) :
    (gs.foldl wireStep w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => ((gs.take k).foldl wireStep w).getD i false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set pref := (gs.take k).foldl wireStep w
  have hplen : pref.length = w.length + k := by
    rw [foldl_length, List.length_take_of_le (Nat.le_of_lt hk)]
  obtain ⟨T, hT, _⟩ := foldl_append (gs.drop (k + 1)) (wireStep pref gs[k])
  rw [hT]
  have hlt : w.length + k < (wireStep pref gs[k]).length := by
    simp [wireStep, hplen]
  rw [getD_append_left_lt _ _ _ hlt]
  simp only [wireStep, ← hplen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

lemma pref_getD_eq (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length)
    (i : ℕ) :
    ((gs.take k).foldl wireStep w).getD i false =
      if i < w.length + k then (gs.foldl wireStep w).getD i false else false := by
  have hplen : ((gs.take k).foldl wireStep w).length = w.length + k := by
    rw [foldl_length, List.length_take_of_le (Nat.le_of_lt hk)]
  split_ifs with hi
  · have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
    conv_rhs => rw [hsplit]
    rw [List.foldl_append]
    obtain ⟨T, hT, _⟩ := foldl_append (gs.drop k) ((gs.take k).foldl wireStep w)
    rw [hT, getD_append_left_lt _ _ i (by rw [hplen]; exact hi)]
  · exact getD_eq_false_of_le _ _ (by rw [hplen]; omega)

lemma gateVal_eval (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    gateVal n C k x =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
        if i < n + k then (C.wires (List.ofFn x)).getD i false else false) := by
  have hga : gateAt C k = C.gates[k] := by
    unfold gateAt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
    rfl
  rw [hga]
  unfold gateVal
  rw [wires_eq_foldl]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h1 := wires_gate_prefix C.gates (List.ofFn x) k hk
  rw [hlen] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i _
  have h2 := pref_getD_eq C.gates (List.ofFn x) k hk i
  rw [hlen] at h2
  exact h2

lemma gateVal_or_iff (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hor : (gateAt C k).op = GateOp.or) :
    gateVal n C k x = true ↔
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ (C.wires (List.ofFn x)).getD i false = true := by
  rw [gateVal_eval n C x k hk, hor]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
  constructor
  · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    split_ifs at hb with hlt
    exact ⟨i, hi, hlt, hb⟩
  · rintro ⟨i, hi, hlt, hb⟩
    refine ⟨true, ⟨i, hi, ?_⟩, rfl⟩
    split_ifs
    exact hb

lemma graphFun_pair_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) :
    graphFun G ∅ (pairInput u v) = true := by
  simp only [graphFun, pairInput, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩

lemma graphFun_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n) :
    graphFun G ∅ (pairInput w w) = false := by
  unfold graphFun
  simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
    decide_eq_false_iff_not]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [pairInput, or_self, decide_eq_true_eq] at ha hb
  subst ha
  subst hb
  exact G.loopless.irrefl _ hab

lemma main {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hao : AndOrOnly C) (hcf : circuitFun n C = graphFun G ∅) :
    EveryEdgeOwned n G C := by
  intro u v huv
  have hfun : ∀ x, C.eval (List.ofFn x) = graphFun G ∅ x := fun x =>
    congrFun hcf x
  have huv_true : (C.wires (List.ofFn (pairInput u v))).getD C.output false = true := by
    have h := hfun (pairInput u v)
    rw [graphFun_pair_adj G u v huv] at h
    exact h
  have hu_false : (C.wires (List.ofFn (pairInput u u))).getD C.output false = false := by
    have h := hfun (pairInput u u)
    rw [graphFun_single G u] at h
    exact h
  have hv_false : (C.wires (List.ofFn (pairInput v v))).getD C.output false = false := by
    have h := hfun (pairInput v v)
    rw [graphFun_single G v] at h
    exact h
  have hout_lt : C.output < n + C.gates.length := by
    by_contra hge
    have hle : (C.wires (List.ofFn (pairInput u v))).length ≤ C.output := by
      rw [wires_eq_foldl, foldl_length, List.length_ofFn]
      omega
    have := getD_eq_false_of_le (C.wires (List.ofFn (pairInput u v))) C.output hle
    rw [huv_true] at this
    cases this
  have hout_ge : n ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < n := Nat.lt_of_not_ge hlt
    rw [wires_input n C (pairInput u v) C.output hlt'] at huv_true
    unfold pairInput at huv_true
    simp only [decide_eq_true_eq] at huv_true
    rcases huv_true with hcu | hcv
    · rw [wires_input n C (pairInput u u) C.output hlt', hcu] at hu_false
      simp [pairInput] at hu_false
    · rw [wires_input n C (pairInput v v) C.output hlt', hcv] at hv_false
      simp [pairInput] at hv_false
  set j0 := C.output - n
  have hj0_lt : j0 < C.gates.length := by omega
  have hj0_eq : n + j0 = C.output := by omega
  have hj0_uv : gateVal n C j0 (pairInput u v) = true := by
    unfold gateVal; rw [hj0_eq]; exact huv_true
  have hj0_u : gateVal n C j0 (pairInput u u) = false := by
    unfold gateVal; rw [hj0_eq]; exact hu_false
  have hj0_v : gateVal n C j0 (pairInput v v) = false := by
    unfold gateVal; rw [hj0_eq]; exact hv_false
  have hex : ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      gateVal n C j (pairInput u v) = true := by
    by_contra hno
    push Not at hno
    have hclaim : ∀ k, k < C.gates.length → gateVal n C k (pairInput u v) = true →
        gateVal n C k (pairInput u u) = true ∨ gateVal n C k (pairInput v v) = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | _ k ih =>
        intro hk hval
        have hga : gateAt C k = C.gates[k] := by
          unfold gateAt
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          rfl
        have hor : (gateAt C k).op = GateOp.or := by
          rcases hao C.gates[k] (List.getElem_mem hk) with hand | hor
          · exfalso
            rw [← hga] at hand
            exact hno k hk hand hval
          · rw [hga]; exact hor
        obtain ⟨i, hi_mem, hi_lt, hi_true⟩ := (gateVal_or_iff n C (pairInput u v) k hk hor).mp hval
        by_cases hin : i < n
        · rw [wires_input n C (pairInput u v) i hin] at hi_true
          unfold pairInput at hi_true
          simp only [decide_eq_true_eq] at hi_true
          rcases hi_true with hiu | hiv
          · left
            apply (gateVal_or_iff n C (pairInput u u) k hk hor).mpr
            refine ⟨i, hi_mem, hi_lt, ?_⟩
            rw [wires_input n C (pairInput u u) i hin, hiu]
            simp [pairInput]
          · right
            apply (gateVal_or_iff n C (pairInput v v) k hk hor).mpr
            refine ⟨i, hi_mem, hi_lt, ?_⟩
            rw [wires_input n C (pairInput v v) i hin, hiv]
            simp [pairInput]
        · set m := i - n
          have hm_lt : m < k := by omega
          have hm_len : m < C.gates.length := Nat.lt_trans hm_lt hk
          have hm_eq : n + m = i := by omega
          have hm_true : gateVal n C m (pairInput u v) = true := by
            unfold gateVal; rw [hm_eq]; exact hi_true
          rcases ih m hm_lt hm_len hm_true with hmu | hmv
          · left
            apply (gateVal_or_iff n C (pairInput u u) k hk hor).mpr
            refine ⟨i, hi_mem, hi_lt, ?_⟩
            rw [← hm_eq]; exact hmu
          · right
            apply (gateVal_or_iff n C (pairInput v v) k hk hor).mpr
            refine ⟨i, hi_mem, hi_lt, ?_⟩
            rw [← hm_eq]; exact hmv
    rcases hclaim j0 hj0_lt hj0_uv with hu | hv
    · rw [hj0_u] at hu; cases hu
    · rw [hj0_v] at hv; cases hv
  classical
  let j := Nat.find hex
  have hj := Nat.find_spec hex
  refine ⟨j, hj.1, hj.1, hj.2.1, hj.2.2, ?_⟩
  intro i hij _ hiand
  by_contra hne
  have hitrue : gateVal n C i (pairInput u v) = true := by
    cases h : gateVal n C i (pairInput u v)
    · exact absurd h hne
    · rfl
  exact Nat.find_min hex hij ⟨Nat.lt_trans hij hj.1, hiand, hitrue⟩

end PEqualNP.Outside.L_meta_19002_aux

theorem PEqualNP.Outside.L_meta_19002 : (∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned x1 x2 x4) := by
  intro x1 x2 x3 x4 hao hcf
  exact PEqualNP.Outside.L_meta_19002_aux.main x2 x4 hao hcf
