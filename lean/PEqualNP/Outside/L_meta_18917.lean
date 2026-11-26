import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18917_aux

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

private def dstep (w : ℕ → Bool) (acc : List Bool) (g : Gate) : List Bool :=
  let a := g.inputs.getD 0 0
  let b := g.inputs.getD 1 0
  acc ++ [match g.op with
    | .and => (w a && acc.getD b false) || (acc.getD a false && w b)
    | _ => acc.getD a false || acc.getD b false]

private lemma foldl_dstep_len (w : ℕ → Bool) (gs : List Gate) (acc : List Bool) :
    (gs.foldl (dstep w) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [dstep]
    omega

private lemma foldl_dstep_getD_lt (w : ℕ → Bool) (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (dstep w) acc).getD i false = acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (dstep w acc g) (by simp [dstep]; omega)]
    rw [dstep, List.getD_append _ _ _ _ hi]

private lemma getD_ofFn_lt {n : ℕ} (f : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn f).getD i false = f ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem terminal_main :
    ∀ (n : ℕ) (C : Circuit) (j u v s : ℕ) (x : Fin n → Bool),
      IsAO2 n C → C.output = n + j → j + 1 = C.size →
      C.gates[j]? = some ⟨.and, [u, v]⟩ →
      let w : ℕ → Bool := fun k => (C.wires (List.ofFn x)).getD k false
      w u = false → w v = false →
      ∃ d : ℕ → Bool,
        (∀ i < n, d i = decide (i = s)) ∧
        (∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a, b] →
          (g.op = .and → d (n + k) = (w a && d b || d a && w b)) ∧
          (g.op = .or → d (n + k) = (d a || d b))) ∧
        d C.output = false := by
  intro n C j u v s x hAO hout _ hgj w hwu hwv
  let d0 : List Bool := List.ofFn (fun i : Fin n => decide (i.val = s))
  let dlist : List Bool := C.gates.foldl (dstep w) d0
  let d : ℕ → Bool := fun k => dlist.getD k false
  have hd_init : ∀ i < n, d i = decide (i = s) := by
    intro i hi
    simp only [d, dlist]
    rw [foldl_dstep_getD_lt w C.gates d0 i (by simp [d0, hi])]
    exact getD_ofFn_lt _ i hi
  have hd_step : ∀ (k : ℕ) (g : Gate) (a b : ℕ), C.gates[k]? = some g → g.inputs = [a, b] →
      (g.op = .and → d (n + k) = (w a && d b || d a && w b)) ∧
      (g.op = .or → d (n + k) = (d a || d b)) := by
    intro k g a b hgk hgab
    have hk : k < C.gates.length := (List.getElem?_eq_some_iff.mp hgk).1
    have hge : C.gates[k] = g := by
      have h1 : C.gates[k]? = some C.gates[k] := List.getElem?_eq_getElem hk
      rw [h1] at hgk
      exact Option.some.inj hgk
    have hga : gateAt C k = g := by
      unfold gateAt
      rw [List.getD_eq_getElem?_getD, hgk]
      rfl
    have ha : a < n + k := by
      have hrb := hAO.2.1 k hk a
      rw [hga, hgab] at hrb
      exact hrb (by simp)
    have hb : b < n + k := by
      have hrb := hAO.2.1 k hk b
      rw [hga, hgab] at hrb
      exact hrb (by simp)
    have hsplit : C.gates = C.gates.take k ++ (g :: C.gates.drop (k + 1)) := by
      have h1 := List.take_append_drop k C.gates
      have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
      rw [hge] at h2
      rw [← h2, h1]
    set pre : List Bool := (C.gates.take k).foldl (dstep w) d0
    have hpre_len : pre.length = n + k := by
      simp only [pre, foldl_dstep_len, d0, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
    have hfull : dlist = (C.gates.drop (k + 1)).foldl (dstep w) (dstep w pre g) := by
      simp only [dlist]
      conv_lhs => rw [hsplit]
      rw [List.foldl_append, List.foldl_cons]
    have hpre_eq : ∀ i < n + k, d i = pre.getD i false := by
      intro i hi
      simp only [d]
      rw [hfull, foldl_dstep_getD_lt _ _ _ _ (by simp [dstep, hpre_len]; omega)]
      rw [dstep, List.getD_append _ _ _ _ (by omega)]
    have hdk : d (n + k) =
        (match g.op with
          | .and => (w a && pre.getD b false) || (pre.getD a false && w b)
          | _ => pre.getD a false || pre.getD b false) := by
      simp only [d]
      rw [hfull, foldl_dstep_getD_lt _ _ _ _ (by simp [dstep, hpre_len])]
      simp only [dstep, hgab, List.getD_cons_zero, List.getD_cons_succ, ← hpre_len]
      rw [List.getD_append_right _ _ _ _ le_rfl]
      simp
    rw [← hpre_eq a ha, ← hpre_eq b hb] at hdk
    constructor
    · intro hop; rw [hdk, hop]
    · intro hop; rw [hdk, hop]
  refine ⟨d, hd_init, hd_step, ?_⟩
  rw [hout]
  have h1 := (hd_step j ⟨.and, [u, v]⟩ u v hgj rfl).1 rfl
  rw [h1, hwu, hwv]
  simp

end PEqualNP.Outside.L_meta_18917_aux

theorem PEqualNP.Outside.L_meta_18917 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 x5 x6 : ℕ) (x7 : Fin x1 → Bool),   PEqualNP.TopForm.IsAO2 x1 x2 →     x2.output = x1 + x3 →       x3 + (1 : ℕ) = x2.size →         x2.gates[x3]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x4, x5] : PEqualNP.CircuitLowerBounds.Gate } →           have x12 : ℕ → Bool := fun (x12 : ℕ) => (x2.wires (List.ofFn x7)).getD x12 Bool.false;           x12 x4 = Bool.false → x12 x5 = Bool.false → ∃ (x15 : ℕ → Bool), (∀ x16 < x1, x15 x16 = Decidable.decide (x16 = x6)) ∧ (∀ (x16 : ℕ) (x17 : PEqualNP.CircuitLowerBounds.Gate) (x18 x19 : ℕ), x2.gates[x16]? = Option.some x17 → x17.inputs = [x18, x19] → (x17.op = PEqualNP.CircuitLowerBounds.GateOp.and → x15 (x1 + x16) = (x12 x18 && x15 x19 || x15 x18 && x12 x19)) ∧ (x17.op = PEqualNP.CircuitLowerBounds.GateOp.or → x15 (x1 + x16) = (x15 x18 || x15 x19))) ∧ x15 x2.output = Bool.false := by
  exact PEqualNP.Outside.L_meta_18917_aux.terminal_main
