import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19002

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

-- Wire lemmas adapted from the published proof of L-meta-18800.
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_len_w (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]; omega

theorem getD_append_lt {α : Type*} (d : α) (l1 l2 : List α) (i : ℕ) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_append]; omega), List.getElem_append_left hi,
      List.getD_eq_getElem _ _ hi]

theorem getD_snoc {α : Type*} (d : α) (l : List α) (x : α) :
    (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)]
  simp

theorem foldl_w_prefix (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wstep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih _ (by simp [wstep]; omega)]
    exact getD_append_lt false w _ i hi

theorem foldl_w_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl wstep w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        ((gs.take j).foldl wstep w).getD i false) := by
  induction gs using List.reverseRecOn with
  | nil => simp at hj
  | append_singleton gs g ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl wstep w).length = w.length + gs.length := foldl_len_w gs w
    by_cases hlt : j < gs.length
    · rw [wstep, getD_append_lt false _ _ _ (by omega)]
      rw [List.getElem_append_left hlt, List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact ih hlt
    · have heq : j = gs.length := by simp at hj; omega
      subst heq
      rw [wstep, ← hlen, getD_snoc]
      simp


private theorem or_earlier {n j : ℕ} (C : Circuit) (jvalid : j < C.gates.length)
    (hop : (C.gates[j]).op = .or) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ ∃ i ∈ (C.gates[j]).inputs, i < n + j ∧
      (C.wires (List.ofFn x)).getD i false = true := by
  let w := List.ofFn x
  let pre := (C.gates.take j).foldl wstep w
  have hw : w.length = n := by simp [w]
  have hp : pre.length = n + j := by
    simp [pre, foldl_len_w, hw, Nat.min_eq_left (Nat.le_of_lt jvalid)]
  have hread (i : ℕ) : pre.getD i false = true ↔ i < n + j ∧
      (C.wires (List.ofFn x)).getD i false = true := by
    by_cases hi : i < n + j
    · have hprefix : (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
        change (C.gates.foldl wstep w).getD i false = _
        rw [← List.take_append_drop j C.gates, List.foldl_append]
        exact foldl_w_prefix _ _ _ (show i < pre.length by omega)
      rw [hprefix]
      simp [hi]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp [hi]
  have hg := foldl_w_gate C.gates w j jvalid
  rw [hw, hop] at hg
  change (C.gates.foldl wstep w).getD (n + j) false = _ at hg
  change (C.gates.foldl wstep w).getD (n + j) false = true ↔ _
  rw [hg]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  constructor
  · rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨i, hi, (hread i).mp hb⟩
  · rintro ⟨i, hi, hv⟩
    exact ⟨true, ⟨i, hi, (hread i).mpr hv⟩, rfl⟩

private theorem input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) {i : ℕ} (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  change (C.gates.foldl wstep (List.ofFn x)).getD i false = _
  rw [foldl_w_prefix _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
    List.getElem_ofFn]

private theorem some_true_and {n : ℕ} (C : Circuit) (ao : AndOrOnly C)
    (u v : Fin n) (huv : C.eval (List.ofFn (pairInput u v)) = true)
    (hu : C.eval (List.ofFn (pairInput u u)) = false)
    (hv : C.eval (List.ofFn (pairInput v v)) = false) :
    ∃ j, j < C.gates.length ∧ (gateAt C j).op = .and ∧ gateVal n C j (pairInput u v) = true := by
  by_contra h
  have split : ∀ w, (C.wires (List.ofFn (pairInput u v))).getD w false = true →
      (C.wires (List.ofFn (pairInput u u))).getD w false = true ∨
      (C.wires (List.ofFn (pairInput v v))).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hi : w < n
      · rw [input_value _ _ hi] at hw
        rw [input_value _ _ hi, input_value _ _ hi]
        simpa only [pairInput, decide_eq_true_eq, or_self] using hw
      · by_cases hj : w < n + C.gates.length
        · let j := w - n
          have hjv : j < C.gates.length := by omega
          have he : w = n + j := by omega
          have hga : gateAt C j = C.gates[j] := by
            unfold gateAt
            exact List.getD_eq_getElem _ _ hjv
          have hop : (C.gates[j]).op = .or := by
            rcases ao _ (List.getElem_mem hjv) with ha | ho
            · exact (h ⟨j, hjv, (congrArg Gate.op hga).trans ha, by simpa [gateVal, ← he] using hw⟩).elim
            · exact ho
          rw [he] at hw ⊢
          obtain ⟨i, hm, hlt, ht⟩ := (or_earlier C hjv hop _).mp hw
          rcases ih i (by omega) ht with hs | hs
          · exact Or.inl ((or_earlier C hjv hop _).mpr ⟨i, hm, hlt, hs⟩)
          · exact Or.inr ((or_earlier C hjv hop _).mpr ⟨i, hm, hlt, hs⟩)
        · have hlen : (C.wires (List.ofFn (pairInput u v))).length ≤ w := by
            change (C.gates.foldl wstep (List.ofFn (pairInput u v))).length ≤ w
            simp only [foldl_len_w, List.length_ofFn]
            omega
          rw [List.getD_eq_default _ _ hlen] at hw
          contradiction
  rcases split C.output huv with h | h
  · change C.eval (List.ofFn (pairInput u u)) = true at h
    rw [hu] at h
    contradiction
  · change C.eval (List.ofFn (pairInput v v)) = true at h
    rw [hv] at h
    contradiction

private theorem result (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ao : AndOrOnly C) (h : circuitFun n C = graphFun G ∅) :
    EveryEdgeOwned n G C := by
  classical
  intro u v huv
  have pos : C.eval (List.ofFn (pairInput u v)) = true := by
    change circuitFun n C (pairInput u v) = true
    rw [h]
    simp [graphFun, pairInput]
    exact ⟨u, v, huv, Or.inl rfl, Or.inr rfl⟩
  have neg (a : Fin n) : C.eval (List.ofFn (pairInput a a)) = false := by
    change circuitFun n C (pairInput a a) = false
    rw [h]
    simp [graphFun, pairInput]
  have ex := some_true_and C ao u v pos (neg u) (neg v)
  let j := Nat.find ex
  have hj := Nat.find_spec ex
  refine ⟨j, hj.1, hj.1, hj.2.1, hj.2.2, ?_⟩
  intro i hi _ hop
  cases hiVal : gateVal n C i (pairInput u v)
  · rfl
  · exact (Nat.find_min ex hi ⟨by omega, hop, hiVal⟩).elim

end PEqualNP.Outside.L_meta_19002

theorem PEqualNP.Outside.L_meta_19002 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.EdgeOwnership.AndOrOnly x4 → PEqualNP.MetaComplexity.circuitFun x1 x4 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → PEqualNP.EdgeOwnership.EveryEdgeOwned x1 x2 x4 := by
  exact PEqualNP.Outside.L_meta_19002.result
