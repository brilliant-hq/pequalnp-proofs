import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_49933

open PEqualNP.CircuitLowerBounds

/-! ### Part 1: Circuit wires and Markov NOT-vector monotonicity -/

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

private lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

private lemma wiresFrom_exists_tail (gs : List Gate) : ∀ w : List Bool,
    ∃ tl : List Bool, wiresFrom gs w = w ++ tl ∧ tl.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    rcases ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) with ⟨tl, htl, hlen⟩
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: tl, ?_, by simp [hlen]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [htl]; simp

private lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  rcases wiresFrom_exists_tail gs w with ⟨tl, htl, hlen⟩
  rw [htl, List.length_append, hlen]

private lemma getD_append_left {l1 l2 : List Bool} {i : Nat} (h : i < l1.length) :
    (l1 ++ l2).getD i false = l1.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private lemma getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  rcases wiresFrom_exists_tail gs w with ⟨tl, htl, _⟩
  rw [htl]
  exact getD_append_left hi

private lemma circuit_wires_gate (C : Circuit) (x : List Bool) (j : Nat) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map (fun i =>
        (wiresFrom (C.gates.take j) x).getD i false)) := by
  have hsplit : C.gates = C.gates.take j ++ [C.gates[j]'hj] ++ C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = (C.gates[j]'hj) :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    conv_lhs => rw [← h1]
    simp
  have hw : C.wires x = wiresFrom (C.gates.drop (j + 1))
      (wiresFrom [C.gates[j]'hj] (wiresFrom (C.gates.take j) x)) := by
    change wiresFrom C.gates x = _
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append, wiresFrom_append]
  rw [hw]
  set p := wiresFrom (C.gates.take j) x
  have hplen : p.length = x.length + j := by
    dsimp only [p]
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hstep : wiresFrom [C.gates[j]'hj] p =
      p ++ [(C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map (fun i => p.getD i false))] := rfl
  rw [hstep]
  have hlt : x.length + j < (p ++ [(C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map (fun i => p.getD i false))]).length := by
    rw [List.length_append, hplen]; simp
  rw [getD_wiresFrom_lt _ _ _ hlt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hplen]
  simp

private lemma circuit_wires_gate_rb (C : Circuit) (x : List Bool)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack x.length C) (j : Nat) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      (C.gates[j]'hj).op.eval ((C.gates[j]'hj).inputs.map (fun i => (C.wires x).getD i false)) := by
  rw [circuit_wires_gate C x j hj]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  have hlt : i < x.length + j := by
    have h := hrb j hj i
    have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j]'hj := by
      dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [hgat] at h
    exact h hi
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  have hw : C.wires x = wiresFrom (C.gates.drop j) (wiresFrom (C.gates.take j) x) := by
    change wiresFrom C.gates x = _
    conv_lhs => rw [hsplit]
    rw [wiresFrom_append]
  rw [hw]
  have hlen : (wiresFrom (C.gates.take j) x).length = x.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  exact (getD_wiresFrom_lt _ _ _ (by omega)).symm

private lemma circuit_wires_input (C : Circuit) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  getD_wiresFrom_lt C.gates x i hi

private lemma notCount_append (gs1 gs2 : List Gate) (o1 o2 o3 : Nat) :
    PEqualNP.NotBracket.notCount ⟨gs1 ++ gs2, o3⟩ =
      PEqualNP.NotBracket.notCount ⟨gs1, o1⟩ + PEqualNP.NotBracket.notCount ⟨gs2, o2⟩ := by
  simp [PEqualNP.NotBracket.notCount, List.filter_append]

private def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

private lemma isNotOp_eq_true (op : GateOp) : isNotOp op = true ↔ op = GateOp.not := by
  cases op <;> simp [isNotOp]

private lemma notCount_cons (g : Gate) (gs : List Gate) (o : Nat) :
    PEqualNP.NotBracket.notCount ⟨g :: gs, o⟩ =
      (if isNotOp g.op then 1 else 0) + PEqualNP.NotBracket.notCount ⟨gs, o⟩ := by
  have h1 := notCount_append [g] gs o o o
  simp only [List.singleton_append] at h1
  rw [h1]
  cases g with
  | mk op ins => cases op <;> rfl

private def notIndices (gs : List Gate) : List Nat :=
  (List.range gs.length).filter (fun j => isNotOp (gs.getD j ⟨.or, []⟩).op)

private lemma notIndices_length (C : Circuit) : (notIndices C.gates).length = PEqualNP.NotBracket.notCount C := by
  have hgen : ∀ (l : List Gate) (o : Nat),
      (notIndices l).length = PEqualNP.NotBracket.notCount ⟨l, o⟩ := by
    intro l o
    induction l with
    | nil => rfl
    | cons g gs ih =>
      dsimp only [notIndices]
      rw [List.length_cons, List.range_succ_eq_map, List.filter_cons, notCount_cons g gs o]
      have h0 : (g :: gs).getD 0 ⟨.or, []⟩ = g := rfl
      rw [h0]
      have hmap : ((List.range gs.length).map Nat.succ).filter (fun j => isNotOp ((g :: gs).getD j ⟨.or, []⟩).op) =
          ((List.range gs.length).filter (fun j => isNotOp (gs.getD j ⟨.or, []⟩).op)).map Nat.succ := by
        rw [List.filter_map]; rfl
      rw [hmap]
      cases h : isNotOp g.op <;> simp [notIndices] at ih ⊢ <;> omega
  cases C; exact hgen _ _

private lemma notIndices_strict (gs : List Gate) : (notIndices gs).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

private lemma notIndices_mem_iff (gs : List Gate) (j : Nat) :
    j ∈ notIndices gs ↔ ∃ hj : j < gs.length, (gs[j]'hj).op = GateOp.not := by
  simp only [notIndices, List.mem_filter, List.mem_range, isNotOp_eq_true]
  constructor
  · rintro ⟨hj, hop⟩
    have hg : gs.getD j ⟨.or, []⟩ = gs[j]'hj := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [hg] at hop; exact ⟨hj, hop⟩
  · rintro ⟨hj, hop⟩
    have hg : gs.getD j ⟨.or, []⟩ = gs[j]'hj := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    exact ⟨hj, by rw [hg]; exact hop⟩

private def notInVal (C : Circuit) (y : List Bool) (j : Nat) : Bool :=
  match (C.gates.getD j ⟨.or, []⟩).inputs with
  | [] => false
  | i :: _ => (C.wires y).getD i false

private def notVecVal (C : Circuit) (y : List Bool) : Nat :=
  let ns := notIndices C.gates
  (List.finRange ns.length).foldl (fun acc t =>
    acc + if notInVal C y (ns[t.val]'t.isLt) = true then 2 ^ (ns.length - 1 - t.val) else 0) 0

private lemma notVecVal_eq_sum (C : Circuit) (y : List Bool) :
    let ns := notIndices C.gates
    notVecVal C y = ∑ t : Fin ns.length,
      if notInVal C y (ns[t.val]'t.isLt) = true then 2 ^ (ns.length - 1 - t.val) else 0 := by
  intro ns
  dsimp only [notVecVal]
  have hfold : ∀ (l : List (Fin ns.length)) (f : Fin ns.length → Nat) (init : Nat),
      l.foldl (fun acc t => acc + f t) init = init + (l.map f).sum := by
    intro l f; induction l with
    | nil => intro init; simp
    | cons a as ih => intro init; simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih]; omega
  rw [hfold, zero_add]
  let f : Fin ns.length → Nat := fun t =>
    if notInVal C y (ns[t.val]'t.isLt) = true then 2 ^ (ns.length - 1 - t.val) else 0
  have hsum_tl : ∀ (s : Finset (Fin ns.length)), (s.toList.map f).sum = ∑ t ∈ s, f t := by
    intro s
    have h1 : ∑ t ∈ s, f t = (s.val.map f).sum := rfl
    rw [h1, ← Finset.coe_toList s, Multiset.map_coe, Multiset.sum_coe]
  have hperm : (Finset.univ : Finset (Fin ns.length)).toList.Perm (List.finRange ns.length) := by
    refine (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_finRange _)).mpr fun x => by simp
  exact ((hperm.map f).sum_eq.symm).trans (hsum_tl Finset.univ)

private lemma notVecVal_lt (C : Circuit) (y : List Bool) :
    notVecVal C y < 2 ^ PEqualNP.NotBracket.notCount C := by
  rw [← notIndices_length C, notVecVal_eq_sum]
  set k := (notIndices C.gates).length
  have hsum_pow : ∀ m : Nat, ∑ t : Fin m, 2 ^ (m - 1 - t.val) = 2 ^ m - 1 := by
    intro m; induction m with
    | zero => simp
    | succ m ih =>
      rw [Fin.sum_univ_succ]
      have h0 : m + 1 - 1 - 0 = m := by omega
      have hrest : ∀ t : Fin m, m + 1 - 1 - (t.val + 1) = m - 1 - t.val := fun t => by omega
      simp only [Fin.val_zero, h0, Fin.val_succ, hrest, ih]
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow m 2 (by omega)
      have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by ring
      omega
  have hle : ∑ t : Fin k, (if notInVal C y ((notIndices C.gates)[t.val]'t.isLt) = true then 2 ^ (k - 1 - t.val) else 0) ≤
      ∑ t : Fin k, 2 ^ (k - 1 - t.val) :=
    Finset.sum_le_sum fun t _ => by split_ifs; exact le_rfl; exact Nat.zero_le _
  rw [hsum_pow k] at hle
  have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
  change ∑ t : Fin k, (if notInVal C y ((notIndices C.gates)[t.val]'t.isLt) = true then 2 ^ (k - 1 - t.val) else 0) < 2 ^ k
  exact lt_of_le_of_lt hle (by omega)

private lemma markov_mono_and_fall {w : Nat} (C : Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (w + 2) C)
    (y1 y2 : List Bool) (hy1 : y1.length = w + 2) (hy2 : y2.length = w + 2)
    (hmon : ∀ i < w + 2, y1.getD i false = true → y2.getD i false = true) :
    notVecVal C y1 ≤ notVecVal C y2 ∧
    ((∃ p < w + 2 + C.size, (C.wires y1).getD p false = true ∧ (C.wires y2).getD p false = false) →
      notVecVal C y1 < notVecVal C y2) := by
  let ns := notIndices C.gates
  have hmono_upto : ∀ (lim : Nat),
      (∀ t : Fin ns.length, (ns[t.val]'t.isLt) < lim →
        notInVal C y1 (ns[t.val]'t.isLt) = notInVal C y2 (ns[t.val]'t.isLt)) →
      ∀ p < w + 2 + lim, p < w + 2 + C.size →
        (C.wires y1).getD p false = true → (C.wires y2).getD p false = true := by
    intro lim hagree p
    induction p using Nat.strong_induction_on with
    | ind p ih =>
      intro hplim hpsz hp1
      by_cases hp_in : p < w + 2
      · rw [circuit_wires_input C y1 p (by omega)] at hp1
        rw [circuit_wires_input C y2 p (by omega)]
        exact hmon p hp_in hp1
      · let j := p - (w + 2)
        have hj : j < C.gates.length := by dsimp [Circuit.size] at hpsz; omega
        have hj_lim : j < lim := by omega
        have hrb1 : PEqualNP.MetaComplexity.NestedCover.ReadsBack y1.length C := by rw [hy1]; exact hrb
        have hrb2 : PEqualNP.MetaComplexity.NestedCover.ReadsBack y2.length C := by rw [hy2]; exact hrb
        have hp_eq1 : p = y1.length + j := by omega
        have hp_eq2 : p = y2.length + j := by omega
        rw [hp_eq1, circuit_wires_gate_rb C y1 hrb1 j hj] at hp1
        rw [hp_eq2, circuit_wires_gate_rb C y2 hrb2 j hj]
        have hlt_ins : ∀ i ∈ (C.gates[j]'hj).inputs, i < p := by
          intro i hi
          have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j]'hj := by
            dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
          have := hrb j hj i; rw [hgat] at this; have := this hi; omega
        have hfg := (hfan (C.gates[j]'hj) (List.getElem_mem hj)).1
        rcases hfg with hop | hop | hop
        · rw [hop] at hp1 ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hp1 ⊢
          rintro _ ⟨i, hi, rfl⟩
          have hip := hlt_ins i hi
          exact ih i hip (by omega) (by omega) (hp1 _ ⟨i, hi, rfl⟩)
        · rw [hop] at hp1 ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hp1 ⊢
          rcases hp1 with ⟨_, ⟨i, hi, rfl⟩, hvi⟩
          have hip := hlt_ins i hi
          exact ⟨_, ⟨i, hi, rfl⟩, ih i hip (by omega) (by omega) hvi⟩
        · rw [hop] at hp1 ⊢
          have hj_mem : j ∈ ns := (notIndices_mem_iff C.gates j).mpr ⟨hj, hop⟩
          rcases List.getElem_of_mem hj_mem with ⟨t, ht, hnt⟩
          have hag := hagree ⟨t, ht⟩ (by simpa [hnt] using hj_lim)
          simp only [hnt] at hag
          have hgetD : C.gates.getD j ⟨.or, []⟩ = C.gates[j]'hj := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
          have heval_eq : ∀ y, GateOp.not.eval ((C.gates[j]'hj).inputs.map fun i => (C.wires y).getD i false) = !(notInVal C y j) := by
            intro y; dsimp only [notInVal]; rw [hgetD]
            cases (C.gates[j]'hj).inputs <;> rfl
          rw [heval_eq y1] at hp1; rw [heval_eq y2, ← hag]; exact hp1
  by_cases hall : ∀ t : Fin ns.length, notInVal C y1 (ns[t.val]'t.isLt) = notInVal C y2 (ns[t.val]'t.isLt)
  · have hveq : notVecVal C y1 = notVecVal C y2 := by
      rw [notVecVal_eq_sum, notVecVal_eq_sum]
      exact Finset.sum_congr rfl fun t _ => by rw [hall t]
    refine ⟨le_of_eq hveq, fun ⟨p, hp, hp1, hp2⟩ => ?_⟩
    have h2 := hmono_upto C.size (fun t _ => hall t) p hp hp hp1
    rw [h2] at hp2; cases hp2
  · push Not at hall
    let S := (Finset.univ : Finset (Fin ns.length)).filter
      (fun t => notInVal C y1 (ns[t.val]'t.isLt) ≠ notInVal C y2 (ns[t.val]'t.isLt))
    have hSne : S.Nonempty := by
      rcases hall with ⟨t, ht⟩; exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩⟩
    let t0 := S.min' hSne
    have ht0_mem : t0 ∈ S := Finset.min'_mem S hSne
    have ht0_ne : notInVal C y1 (ns[t0.val]'t0.isLt) ≠ notInVal C y2 (ns[t0.val]'t0.isLt) :=
      (Finset.mem_filter.mp ht0_mem).2
    have hlt_agree : ∀ t : Fin ns.length, t.val < t0.val →
        notInVal C y1 (ns[t.val]'t.isLt) = notInVal C y2 (ns[t.val]'t.isLt) := by
      intro t ht; by_contra hne
      have hle : t0 ≤ t := Finset.min'_le S t (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      exact Nat.not_le_of_lt ht hle
    let j0 := ns[t0.val]'t0.isLt
    have hj0_lt : j0 < C.gates.length := ((notIndices_mem_iff C.gates j0).mp (List.getElem_mem t0.isLt)).1
    have hagree_j0 : ∀ t : Fin ns.length, (ns[t.val]'t.isLt) < j0 →
        notInVal C y1 (ns[t.val]'t.isLt) = notInVal C y2 (ns[t.val]'t.isLt) := by
      intro t htj
      have htl : t.val < t0.val := by
        by_contra hge
        have hle : t0.val ≤ t.val := by omega
        by_cases heq : t0.val = t.val
        · have hteq : t = t0 := Fin.ext heq.symm
          subst hteq; exact Nat.lt_irrefl _ htj
        · have hlt := List.pairwise_iff_getElem.mp (notIndices_strict C.gates) t0.val t.val t0.isLt t.isLt (by omega)
          dsimp only [j0, ns] at htj; omega
      exact hlt_agree t htl
    have h01 : notInVal C y1 j0 = false ∧ notInVal C y2 j0 = true := by
      have hmono_j0 : notInVal C y1 j0 = true → notInVal C y2 j0 = true := by
        intro h1
        have hgetD : C.gates.getD j0 ⟨.or, []⟩ = C.gates[j0]'hj0_lt := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0_lt]; rfl
        dsimp only [notInVal] at h1 ⊢; rw [hgetD] at h1 ⊢
        cases hins : (C.gates[j0]'hj0_lt).inputs with
        | nil => rw [hins] at h1; cases h1
        | cons i0 rest =>
          rw [hins] at h1
          have hi0_lt : i0 < w + 2 + j0 := by
            have hgat : PEqualNP.MetaComplexity.NestedCover.gateAt C j0 = C.gates[j0]'hj0_lt := by
              dsimp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj0_lt]; rfl
            have := hrb j0 hj0_lt i0; rw [hgat, hins] at this; exact this (by simp)
          exact hmono_upto j0 hagree_j0 i0 hi0_lt (by dsimp [Circuit.size]; omega) h1
      cases hv1 : notInVal C y1 j0 <;> cases hv2 : notInVal C y2 j0
      · exact absurd (hv1.trans hv2.symm) ht0_ne
      · exact ⟨rfl, rfl⟩
      · have := hmono_j0 hv1; rw [hv2] at this; cases this
      · exact absurd (hv1.trans hv2.symm) ht0_ne
    have hlt_val : notVecVal C y1 < notVecVal C y2 := by
      rw [notVecVal_eq_sum, notVecVal_eq_sum]
      let k := ns.length
      let f1 : Fin k → Nat := fun t => if notInVal C y1 (ns[t.val]'t.isLt) = true then 2 ^ (k - 1 - t.val) else 0
      let f2 : Fin k → Nat := fun t => if notInVal C y2 (ns[t.val]'t.isLt) = true then 2 ^ (k - 1 - t.val) else 0
      have hsplit : ∀ f : Fin k → Nat,
          ∑ t : Fin k, f t =
            (∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < t0.val), f t) + f t0 +
            (∑ t ∈ Finset.univ.filter (fun t : Fin k => t0.val < t.val), f t) := by
        intro f
        let A := Finset.univ.filter (fun t : Fin k => t.val < t0.val)
        let B := Finset.univ.filter (fun t : Fin k => t0.val < t.val)
        have hAB : Disjoint A B := by
          rw [Finset.disjoint_left]; intro t h1 h2
          simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2; omega
        have ht0A : t0 ∉ A := by simp [A]
        have ht0B : t0 ∉ B := by simp [B]
        have hun : insert t0 (A ∪ B) = Finset.univ := by
          ext t; simp only [A, B, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          rcases lt_trichotomy t.val t0.val with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl (Fin.ext h)
          · exact Or.inr (Or.inr h)
        conv_lhs => rw [← hun]
        rw [Finset.sum_insert (by simp [ht0A, ht0B]), Finset.sum_union hAB]; dsimp only [A, B]; omega
      rw [hsplit f1, hsplit f2]
      have hpre_eq : ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < t0.val), f1 t =
          ∑ t ∈ Finset.univ.filter (fun t : Fin k => t.val < t0.val), f2 t := by
        refine Finset.sum_congr rfl fun t ht => ?_
        have htl := (Finset.mem_filter.mp ht).2
        dsimp only [f1, f2]; rw [hlt_agree t htl]
      have hf1_t0 : f1 t0 = 0 := by dsimp only [f1]; rw [h01.1]; rfl
      have hf2_t0 : f2 t0 = 2 ^ (k - 1 - t0.val) := by dsimp only [f2]; rw [h01.2]; rfl
      have htail_lt : ∑ t ∈ Finset.univ.filter (fun t : Fin k => t0.val < t.val), f1 t < 2 ^ (k - 1 - t0.val) := by
        have hle1 : ∑ t ∈ Finset.univ.filter (fun t : Fin k => t0.val < t.val), f1 t ≤
            ∑ t ∈ Finset.univ.filter (fun t : Fin k => t0.val < t.val), 2 ^ (k - 1 - t.val) :=
          Finset.sum_le_sum fun t _ => by dsimp only [f1]; split_ifs; exact le_rfl; exact Nat.zero_le _
        let rem := k - 1 - t0.val
        have hbij : ∑ t ∈ Finset.univ.filter (fun t : Fin k => t0.val < t.val), 2 ^ (k - 1 - t.val) =
            ∑ u : Fin rem, 2 ^ u.val := by
          refine Finset.sum_bij (fun t ht => ⟨k - 1 - t.val, by have := (Finset.mem_filter.mp ht).2; have := t.isLt; dsimp [rem]; omega⟩) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro a _ b _ h; have := congrArg Fin.val h; dsimp at this; have := a.isLt; have := b.isLt; exact Fin.ext (by omega)
          · intro u _; refine ⟨⟨k - 1 - u.val, by have := u.isLt; dsimp [rem] at *; omega⟩, ?_, Fin.ext (by dsimp; have := u.isLt; dsimp [rem] at *; omega)⟩
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]; have := u.isLt; dsimp [rem] at *; omega
          · intro _ _; rfl
        have hsum_rem : ∀ m : Nat, ∑ u : Fin m, 2 ^ u.val = 2 ^ m - 1 := by
          intro m; induction m with
          | zero => simp
          | succ r ihr =>
            rw [Fin.sum_univ_castSucc]
            simp only [Fin.val_castSucc, Fin.val_last, ihr]
            have h1 : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
            have h2 : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by ring
            omega
        have hpos : 1 ≤ 2 ^ rem := Nat.one_le_pow rem 2 (by omega)
        rw [hbij, hsum_rem rem] at hle1; dsimp only [rem] at hle1 hpos; omega
      omega
    exact ⟨le_of_lt hlt_val, fun _ => hlt_val⟩

/-! ### Part 2: Standard input encoding and core combinatorics -/

private def stdBits (l : Nat) (x : Finset (Fin l)) : List Bool :=
  List.ofFn (fun i : Fin l => decide (i ∈ x))

private lemma stdBits_length (l : Nat) (x : Finset (Fin l)) : (stdBits l x).length = l := by
  simp [stdBits]

private lemma getD_stdBits (l : Nat) (x : Finset (Fin l)) (i : Fin l) :
    (stdBits l x).getD i.val false = decide (i ∈ x) := by
  have hi : i.val < (List.ofFn (fun k : Fin l => decide (k ∈ x))).length := by simp [i.isLt]
  simp only [stdBits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    List.getElem_ofFn, Fin.eta, Option.getD_some]

private lemma stdInput_mono {n : Nat} {x1 x2 : Finset (Fin n)} (hx : x1 ⊆ x2) :
    ∀ i < n + 2, (stdBits n x1 ++ [false, true]).getD i false = true →
      (stdBits n x2 ++ [false, true]).getD i false = true := by
  intro i hi h1
  by_cases hin : i < n
  · rw [getD_append_left (by rw [stdBits_length]; exact hin), getD_stdBits n x1 ⟨i, hin⟩, decide_eq_true_eq] at h1
    rw [getD_append_left (by rw [stdBits_length]; exact hin), getD_stdBits n x2 ⟨i, hin⟩, decide_eq_true_eq]
    exact hx h1
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [stdBits_length]; omega), stdBits_length] at h1 ⊢
    exact h1

private lemma core_private_bound (n m e : Nat) (a : Fin m → Finset (Fin n))
    (C : Circuit) (tap : Fin m → Fin (n + 2 + C.size))
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (herr : ∀ x : Finset (Fin n),
      ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (C.wires (stdBits n x ++ [false, true])).getD (tap j).val false ≠
          decide (∀ v ∈ x, v ∉ a j))).card ≤ e)
    (s : Finset (Fin m))
    (hpriv : ∀ j ∈ s, ∃ v ∈ a j, ∀ k ∈ s, k ≠ j → v ∉ a k) :
    s.card < (e + 1) * 2 ^ PEqualNP.NotBracket.notCount C := by
  by_cases hs_empty : s = ∅
  · subst hs_empty
    have hpow : 1 ≤ 2 ^ PEqualNP.NotBracket.notCount C := Nat.one_le_pow _ 2 (by omega)
    have hmul : 1 ≤ (e + 1) * 2 ^ PEqualNP.NotBracket.notCount C := Nat.mul_pos (by omega) hpow
    rw [Finset.card_empty]; omega
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs_empty
  rcases hne with ⟨j0, hj0⟩
  rcases hpriv j0 hj0 with ⟨v0, _, _⟩
  let priv : Fin m → Fin n := fun j =>
    if h : j ∈ s then Classical.choose (hpriv j h) else v0
  have hpriv_in : ∀ j ∈ s, priv j ∈ a j := by
    intro j hj; dsimp only [priv]; rw [dif_pos hj]; exact (Classical.choose_spec (hpriv j hj)).1
  have hpriv_out : ∀ j ∈ s, ∀ k ∈ s, k ≠ j → priv j ∉ a k := by
    intro j hj k hk hne; dsimp only [priv]; rw [dif_pos hj]; exact (Classical.choose_spec (hpriv j hj)).2 k hk hne
  let xOf : Finset (Fin m) → Finset (Fin n) := fun T => T.image priv
  let yOf : Finset (Fin m) → List Bool := fun T => stdBits n (xOf T) ++ [false, true]
  have hyLen : ∀ T, (yOf T).length = n + 2 := fun T => by simp [yOf, stdBits_length]
  let wire : Finset (Fin m) → Fin m → Bool := fun T j => (C.wires (yOf T)).getD (tap j).val false
  let V : Finset (Fin m) → Nat := fun T => notVecVal C (yOf T)
  let FH : Finset (Fin m) → Nat := fun T => (T.filter (fun j => wire T j = true)).card
  let FL : Finset (Fin m) → Nat := fun T => ((s \ T).filter (fun j => wire T j = false)).card
  have hdisj_char : ∀ T : Finset (Fin m), T ⊆ s → ∀ j ∈ s,
      decide (∀ v ∈ xOf T, v ∉ a j) = decide (j ∉ T) := by
    intro T hTs j hjs
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, xOf, Finset.mem_image]
    constructor
    · intro hall hjT
      exact hall (priv j) ⟨j, hjT, rfl⟩ (hpriv_in j hjs)
    · rintro hjT _ ⟨k, hkT, rfl⟩
      have hkj : j ≠ k := fun h => hjT (h ▸ hkT)
      exact hpriv_out k (hTs hkT) j hjs hkj
  have herr_sum : ∀ T : Finset (Fin m), T ⊆ s → FH T + FL T ≤ e := by
    intro T hTs
    let A := T.filter (fun j => wire T j = true)
    let B := (s \ T).filter (fun j => wire T j = false)
    have hdisj : Disjoint A B := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [A, B, Finset.mem_filter, Finset.mem_sdiff] at h1 h2
      exact h2.1.2 h1.1
    have hsub : A ∪ B ⊆ (Finset.univ : Finset (Fin m)).filter (fun j =>
        (C.wires (stdBits n (xOf T) ++ [false, true])).getD (tap j).val false ≠
          decide (∀ v ∈ xOf T, v ∉ a j)) := by
      intro j hj
      simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hj ⊢
      rcases hj with ⟨hjT, hw⟩ | ⟨⟨hjs, hjT⟩, hw⟩
      · have hjs : j ∈ s := hTs hjT
        rw [hdisj_char T hTs j hjs]
        change wire T j ≠ decide (j ∉ T)
        rw [hw, decide_eq_false (by simp [hjT])]; decide
      · rw [hdisj_char T hTs j hjs]
        change wire T j ≠ decide (j ∉ T)
        rw [hw, decide_eq_true hjT]; decide
    have hcard_ab : FH T + FL T = (A ∪ B).card := (Finset.card_union_of_disjoint hdisj).symm
    rw [hcard_ab]
    exact (Finset.card_le_card hsub).trans (herr (xOf T))
  let Good : Finset (Fin m) → Bool := fun T => decide (T.card ≤ FH T + (e + 1) * V T)
  let cands : Finset (Finset (Fin m)) := s.powerset.filter (fun T => Good T = true)
  have hne_cands : cands.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset s), ?_⟩⟩
    simp [Good]
  rcases Finset.exists_max_image cands Finset.card hne_cands with ⟨T, hT_mem, hT_max⟩
  have hT_sub : T ⊆ s := Finset.mem_powerset.mp (Finset.mem_filter.mp hT_mem).1
  have hT_good : T.card ≤ FH T + (e + 1) * V T := of_decide_eq_true (Finset.mem_filter.mp hT_mem).2
  have hall_false : ∀ j ∈ s \ T, wire T j = false := by
    intro j hj
    by_contra hne_f
    have hwj : wire T j = true := by cases h : wire T j <;> simp_all
    have hjs : j ∈ s := (Finset.mem_sdiff.mp hj).1
    have hjT : j ∉ T := (Finset.mem_sdiff.mp hj).2
    let T' := insert j T
    have hT'_sub : T' ⊆ s := Finset.insert_subset hjs hT_sub
    have hT'_card : T'.card = T.card + 1 := Finset.card_insert_of_notMem hjT
    have hx_sub : xOf T ⊆ xOf T' := Finset.image_subset_image (Finset.subset_insert j T)
    have hmark := markov_mono_and_fall C hfan hrb (yOf T) (yOf T') (hyLen T) (hyLen T') (stdInput_mono hx_sub)
    have hV_le : V T ≤ V T' := hmark.1
    have hT'_good : T'.card ≤ FH T' + (e + 1) * V T' := by
      by_cases hVeq : V T = V T'
      · have hno_fall : ∀ k : Fin m, wire T k = true → wire T' k = true := by
          intro k hwk
          by_contra hwk'
          have hwf : wire T' k = false := by cases h : wire T' k <;> simp_all
          have hlt := hmark.2 ⟨(tap k).val, (tap k).isLt, hwk, hwf⟩
          dsimp only [V] at hVeq; omega
        have hsub_fh : insert j (T.filter (fun k => wire T k = true)) ⊆ T'.filter (fun k => wire T' k = true) := by
          intro k hk
          simp only [Finset.mem_insert, Finset.mem_filter] at hk ⊢
          rcases hk with hkj | ⟨hkT, hwk⟩
          · rw [hkj]; exact ⟨Finset.mem_insert_self j T, hno_fall j hwj⟩
          · exact ⟨Finset.mem_insert_of_mem hkT, hno_fall k hwk⟩
        have hj_not : j ∉ T.filter (fun k => wire T k = true) := fun h => hjT (Finset.mem_filter.mp h).1
        have hfh_inc : FH T + 1 ≤ FH T' := by
          have h1 := Finset.card_le_card hsub_fh
          rw [Finset.card_insert_of_notMem hj_not] at h1
          exact h1
        rw [hT'_card, ← hVeq]; omega
      · have hVlt : V T + 1 ≤ V T' := by omega
        have hfh_le : FH T ≤ e := by have := herr_sum T hT_sub; omega
        have hmul : (e + 1) * (V T + 1) = (e + 1) * V T + (e + 1) := by ring
        have hmul_le : (e + 1) * (V T + 1) ≤ (e + 1) * V T' := Nat.mul_le_mul_left (e + 1) hVlt
        omega
    have hT'_mem : T' ∈ cands := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT'_sub, decide_eq_true hT'_good⟩
    have hle := hT_max T' hT'_mem
    omega
  have hFL_eq : FL T = (s \ T).card := by
    dsimp only [FL]
    congr 1
    ext j; simp only [Finset.mem_filter, and_iff_left_iff_imp]
    exact hall_false j
  have hs_split : s.card = T.card + (s \ T).card := by
    have hun : T ∪ (s \ T) = s := Finset.union_sdiff_of_subset hT_sub
    conv_lhs => rw [← hun]
    exact Finset.card_union_of_disjoint disjoint_sdiff_self_right
  have herr_T : FH T + FL T ≤ e := herr_sum T hT_sub
  have hV_lt : V T < 2 ^ PEqualNP.NotBracket.notCount C := notVecVal_lt C (yOf T)
  have hpow_pos : 1 ≤ 2 ^ PEqualNP.NotBracket.notCount C := Nat.one_le_pow _ 2 (by omega)
  have hV_le : V T ≤ 2 ^ PEqualNP.NotBracket.notCount C - 1 := by omega
  have hmul_le : (e + 1) * V T ≤ (e + 1) * (2 ^ PEqualNP.NotBracket.notCount C - 1) :=
    Nat.mul_le_mul_left (e + 1) hV_le
  have hmul_sub : (e + 1) * (2 ^ PEqualNP.NotBracket.notCount C - 1) + (e + 1) =
      (e + 1) * 2 ^ PEqualNP.NotBracket.notCount C := by
    rw [← Nat.mul_add_one, Nat.sub_add_cancel hpow_pos]
  omega

private lemma core_main (n m e : Nat) (g : Fin n → Fin n → Prop) (a : Fin m → Finset (Fin n))
    (hcov : ∀ v, ∃ j, v ∈ a j)
    (hindep : ∀ j u v, u ∈ a j → v ∈ a j → ¬ g u v)
    (C : Circuit) (tap : Fin m → Fin (n + 2 + C.size))
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hrb : PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + 2) C)
    (herr : ∀ x : Finset (Fin n),
      ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (C.wires (stdBits n x ++ [false, true])).getD (tap j).val false ≠
          decide (∀ v ∈ x, v ∉ a j))).card ≤ e) :
    let B := (e + 1) * 2 ^ PEqualNP.NotBracket.notCount C
    (∀ s : Finset (Fin m),
      (∀ j ∈ s, ∃ v ∈ a j, ∀ k ∈ s, k ≠ j → v ∉ a k) → s.card < B) ∧
    ∃ color : Fin n → Fin (B - 1), ∀ u v, g u v → color u ≠ color v := by
  intro B
  have hpart1 : ∀ s : Finset (Fin m),
      (∀ j ∈ s, ∃ v ∈ a j, ∀ k ∈ s, k ≠ j → v ∉ a k) → s.card < B :=
    core_private_bound n m e a C tap hfan hrb herr
  refine ⟨hpart1, ?_⟩
  let covers : Finset (Finset (Fin m)) :=
    Finset.univ.filter (fun s : Finset (Fin m) => ∀ v : Fin n, ∃ j ∈ s, v ∈ a j)
  have hne_cov : covers.Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v => ?_⟩⟩
    rcases hcov v with ⟨j, hj⟩
    exact ⟨j, Finset.mem_univ j, hj⟩
  rcases Finset.exists_min_image covers Finset.card hne_cov with ⟨s, hs_mem, hs_min⟩
  have hs_cov : ∀ v : Fin n, ∃ j ∈ s, v ∈ a j := (Finset.mem_filter.mp hs_mem).2
  have hs_priv : ∀ j ∈ s, ∃ v ∈ a j, ∀ k ∈ s, k ≠ j → v ∉ a k := by
    intro j hj
    by_contra hnone
    push Not at hnone
    have her_cov : ∀ v : Fin n, ∃ k ∈ s.erase j, v ∈ a k := by
      intro v
      rcases hs_cov v with ⟨k, hks, hvk⟩
      by_cases hkj : k = j
      · subst hkj
        rcases hnone v hvk with ⟨k', hk's, hk'ne, hvk'⟩
        exact ⟨k', Finset.mem_erase.mpr ⟨hk'ne, hk's⟩, hvk'⟩
      · exact ⟨k, Finset.mem_erase.mpr ⟨hkj, hks⟩, hvk⟩
    have her_mem : s.erase j ∈ covers := Finset.mem_filter.mpr ⟨Finset.mem_univ _, her_cov⟩
    have hle := hs_min (s.erase j) her_mem
    have hlt : (s.erase j).card < s.card := Finset.card_erase_lt_of_mem hj
    omega
  have hs_lt : s.card < B := hpart1 s hs_priv
  let eFin : s ≃ Fin s.card := s.equivFin
  let color : Fin n → Fin (B - 1) := fun v =>
    let j := Classical.choose (hs_cov v)
    have hj : j ∈ s := (Classical.choose_spec (hs_cov v)).1
    ⟨(eFin ⟨j, hj⟩).val, lt_of_lt_of_le (eFin ⟨j, hj⟩).isLt (by omega)⟩
  refine ⟨color, fun u v huv hcol => ?_⟩
  have hval : (eFin ⟨Classical.choose (hs_cov u), (Classical.choose_spec (hs_cov u)).1⟩).val =
      (eFin ⟨Classical.choose (hs_cov v), (Classical.choose_spec (hs_cov v)).1⟩).val :=
    congrArg (Fin.val : Fin (B - 1) → Nat) hcol
  have heq_sub : (⟨Classical.choose (hs_cov u), (Classical.choose_spec (hs_cov u)).1⟩ : s) =
      ⟨Classical.choose (hs_cov v), (Classical.choose_spec (hs_cov v)).1⟩ :=
    eFin.injective (Fin.ext hval)
  have hjeq : Classical.choose (hs_cov u) = Classical.choose (hs_cov v) := congrArg Subtype.val heq_sub
  have hu : u ∈ a (Classical.choose (hs_cov u)) := (Classical.choose_spec (hs_cov u)).2
  have hv : v ∈ a (Classical.choose (hs_cov u)) := hjeq ▸ (Classical.choose_spec (hs_cov v)).2
  exact hindep _ u v hu hv huv

/-! ### Part 3: Main proof bridging Classical.propDecidable -/

private lemma bits_eq_stdBits {l : Nat} (d : ∀ P : Prop, Decidable P) (x : Finset (Fin l)) :
    List.ofFn (fun i : Fin l => @decide (i ∈ x) (d _)) = stdBits l x := by
  dsimp only [stdBits]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  rw [List.getElem_ofFn, List.getElem_ofFn]
  exact decide_eq_decide.mpr Iff.rfl

theorem main_proof :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m e : Nat) (g : Fin n → Fin n → Prop) (a : Fin m → Finset (Fin n)),
  (∀ v, ∃ j, v ∈ a j) →
  (∀ j u v, u ∈ a j → v ∈ a j → ¬ g u v) →
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
    (∀ x : Finset (Fin n),
      let input := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
      ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (C.wires input).getD (tap j).val false ≠ decide (Disjoint x (a j)))).card ≤ e) →
    let B := (e+1)*2^PEqualNP.NotBracket.notCount C
    (∀ s : Finset (Fin m),
      (∀ j ∈ s, ∃ v ∈ a j, ∀ k ∈ s, k ≠ j → v ∉ a k) → s.card < B) ∧
    ∃ color : Fin n → Fin (B-1), ∀ u v, g u v → color u ≠ color v := by
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro n m e g a hcov hindep C tap hfan hrb herr
  exact core_main n m e g a hcov hindep C tap hfan hrb (by
    intro x
    have h1 := herr x
    convert h1 using 2
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bits_eq_stdBits]
    exact iff_of_eq (congrArg (fun b => (C.wires (stdBits n x ++ [false, true])).getD (tap j).val false ≠ b)
      (decide_eq_decide.mpr Finset.disjoint_left.symm)))

end PEqualNP.Outside.L_meta_49933

theorem PEqualNP.Outside.L_meta_49933 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (n m e : Nat) (g : Fin n → Fin n → Prop) (a : Fin m → Finset (Fin n)),
  (∀ v, ∃ j, v ∈ a j) →
  (∀ j u v, u ∈ a j → v ∈ a j → ¬ g u v) →
  ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (tap : Fin m → Fin (n+2+C.size)),
    PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+2) C →
    (∀ x : Finset (Fin n),
      let input := List.ofFn (fun i : Fin n => decide (i ∈ x)) ++ [false,true]
      ((Finset.univ : Finset (Fin m)).filter (fun j =>
        (C.wires input).getD (tap j).val false ≠ decide (Disjoint x (a j)))).card ≤ e) →
    let B := (e+1)*2^PEqualNP.NotBracket.notCount C
    (∀ s : Finset (Fin m),
      (∀ j ∈ s, ∃ v ∈ a j, ∀ k ∈ s, k ≠ j → v ∉ a k) → s.card < B) ∧
    ∃ color : Fin n → Fin (B-1), ∀ u v, g u v → color u ≠ color v :=
  PEqualNP.Outside.L_meta_49933.main_proof
