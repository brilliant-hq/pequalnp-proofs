import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Girth

namespace PEqualNP.Outside.L_meta_18930

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private def actIn (g : Gate) : List ℕ :=
  List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs

private theorem actIn_eval (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hlen : g.inputs.length ≤ 2) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((actIn g).map f) := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with h | h | h
  · dsimp only [actIn]; rw [h]
    have hev : GateOp.and.eval [Bool.false] = Bool.false := rfl
    rw [hev]; simp [List.take_of_length_le hlen]
  · dsimp only [actIn]; rw [h]
    have hev : GateOp.or.eval [Bool.false] = Bool.false := rfl
    rw [hev]; simp [List.take_of_length_le hlen]
  · dsimp only [actIn]; rw [h]
    have hev : GateOp.not.eval [Bool.false] = Bool.true := rfl
    rw [hev]
    cases hi : g.inputs with
    | nil => rfl
    | cons a rest => rfl

private theorem actIn_len_le (g : Gate) :
    (actIn g).length ≤ 2 ∧ (g.op = GateOp.not → (actIn g).length ≤ 1) := by
  constructor
  · dsimp only [actIn]; cases g.op.eval [Bool.false] <;> simp [List.length_take]
  · intro h; dsimp only [actIn]; rw [h]
    have hev : GateOp.not.eval [Bool.false] = Bool.true := rfl
    rw [hev]; simp [List.length_take]

private def pushW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl pushW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, pushW, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl pushW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (pushW w g) (by dsimp [pushW]; simp; omega)]
    exact List.getD_append _ _ _ _ hi

private theorem wires_getD_gate (C : Circuit) (inp : List Bool) (k : ℕ) (hk : k < C.gates.length) :
    (C.wires inp).getD (inp.length + k) false =
      let w := (C.gates.take k).foldl pushW inp
      let g := C.gates[k]
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hsplit : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k C.gates]
    congr 1
    exact List.drop_eq_getElem_cons hk
  change (C.gates.foldl pushW inp).getD (inp.length + k) false = _
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_cons]
  set w := (C.gates.take k).foldl pushW inp
  have hwlen : w.length = inp.length + k := by
    dsimp [w]; rw [fold_len, List.length_take]; omega
  rw [fold_getD_lt _ _ _ (by dsimp [pushW]; simp; omega)]
  dsimp [pushW]
  rw [← hwlen, List.getD_append_right _ _ _ _ (le_refl _)]
  simp

private def remapIdx (cut rep w : ℕ) : ℕ :=
  if w = cut then rep else if cut < w then w - 1 else w

private def remapGate (cut rep : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapIdx cut rep)⟩

private def elimGate (n k rep : ℕ) (C : Circuit) : Circuit :=
  { gates := C.gates.take k ++ (C.gates.drop (k + 1)).map (remapGate (n + k) rep)
    output := remapIdx (n + k) rep C.output }

private theorem elimGate_fanIn (n k rep : ℕ) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (elimGate n k rep C) := by
  intro g hg
  dsimp only [elimGate] at hg
  rcases List.mem_append.mp hg with h1 | h2
  · exact hC g (List.mem_of_mem_take h1)
  · rcases List.mem_map.mp h2 with ⟨g', hg', rfl⟩
    have h := hC g' (List.mem_of_mem_drop hg')
    exact ⟨h.1, by simp [remapGate, h.2]⟩

private theorem elimGate_size (n k rep : ℕ) (C : Circuit) (hk : k < C.gates.length) :
    (elimGate n k rep C).size = C.size - 1 := by
  change (C.gates.take k ++ (C.gates.drop (k + 1)).map (remapGate (n + k) rep)).length = C.gates.length - 1
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

private theorem elimGate_eval_eq (n k rep : ℕ) (C : Circuit)
    (hC : FanInTwo C) (hk : k < C.gates.length) (x : Fin n → Bool)
    (hrep_lt : rep < n + k)
    (hagree : (n + k ≠ C.output ∧ ∀ j (hj : k < j) (hjl : j < C.gates.length), n + k ∉ actIn C.gates[j]) ∨
              (C.wires (List.ofFn x)).getD (n + k) false = (C.wires (List.ofFn x)).getD rep false) :
    (elimGate n k rep C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  set inp := List.ofFn x
  have hinp : inp.length = n := List.length_ofFn
  set w0 := (C.gates.take k).foldl pushW inp
  have hw0_len : w0.length = n + k := by dsimp [w0]; rw [fold_len, hinp, List.length_take]; omega
  set g_k := C.gates[k]
  set w1 := pushW w0 g_k
  have hw1_len : w1.length = n + k + 1 := by dsimp [w1, pushW]; simp [hw0_len]
  have hsplit : C.gates = C.gates.take k ++ g_k :: C.gates.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k C.gates]
    congr 1; exact List.drop_eq_getElem_cons hk
  -- After folding any suffix `gs` of `C.gates.drop (k + 1)`, wires align via `remapIdx`!
  have hsim : ∀ (m : ℕ) (hm : k + 1 + m ≤ C.gates.length),
      let D_w := ((C.gates.drop (k + 1)).take m |>.map (remapGate (n + k) rep)).foldl pushW w0
      let C_w := ((C.gates.drop (k + 1)).take m).foldl pushW w1
      D_w.length = n + k + m ∧ C_w.length = n + k + 1 + m ∧
      (∀ i < n + k, D_w.getD i false = C_w.getD i false) ∧
      (∀ j < m, D_w.getD (n + k + j) false = C_w.getD (n + k + 1 + j) false) := by
    intro m hm
    induction m with
    | zero =>
      refine ⟨hw0_len, hw1_len, ?_, by simp⟩
      intro i hi
      dsimp only [w1, pushW]
      simp only [List.take_zero, List.map_nil, List.foldl_nil]
      exact (List.getD_append _ _ _ _ (by rw [hw0_len]; exact hi)).symm
    | succ m ih =>
      obtain ⟨hDl, hCl, hlo, hhi⟩ := ih (by omega)
      have hidx : k + 1 + m < C.gates.length := by omega
      have hdrop_take : (C.gates.drop (k + 1)).take (m + 1) =
          (C.gates.drop (k + 1)).take m ++ [C.gates[k + 1 + m]] := by
        rw [List.take_succ_eq_append_getElem (by simp; omega)]
        simp [List.getElem_drop]
      dsimp only
      rw [hdrop_take, List.map_append, List.map_singleton, List.foldl_append, List.foldl_append,
        List.foldl_cons, List.foldl_nil, List.foldl_cons, List.foldl_nil]
      set Dw := (((C.gates.drop (k + 1)).take m).map (remapGate (n + k) rep)).foldl pushW w0
      set Cw := ((C.gates.drop (k + 1)).take m).foldl pushW w1
      set gm := C.gates[k + 1 + m]
      have hgm_fan : FanInTwo C := hC
      have hgm := hC gm (List.getElem_mem hidx)
      have hgate_eq : (remapGate (n + k) rep gm).op.eval ((remapGate (n + k) rep gm).inputs.map fun i => Dw.getD i false) =
          gm.op.eval (gm.inputs.map fun i => Cw.getD i false) := by
        have hlen_rm : (remapGate (n + k) rep gm).inputs.length ≤ 2 := by simp [remapGate, hgm.2]
        rw [actIn_eval (remapGate (n + k) rep gm) hgm.1 hlen_rm, actIn_eval gm hgm.1 hgm.2]
        dsimp only [remapGate]
        have hact_map : actIn ⟨gm.op, gm.inputs.map (remapIdx (n + k) rep)⟩ =
            (actIn gm).map (remapIdx (n + k) rep) := by
          dsimp only [actIn]; rw [List.map_take]
        rw [hact_map, List.map_map]
        congr 1
        apply List.map_congr_left
        intro w hw
        dsimp only [Function.comp_def, remapIdx]
        by_cases hw_lt : w < n + k
        · rw [if_neg (by omega), if_neg (by omega)]
          exact hlo w hw_lt
        · by_cases hw_eq : w = n + k
          · subst hw_eq
            rw [if_pos rfl]
            rcases hagree with ⟨_, hno⟩ | hval
            · exact absurd hw (hno (k + 1 + m) (by omega) hidx)
            · have hCw_full : C.wires inp = ((C.gates.drop (k + 1)).drop m).foldl pushW Cw := by
                change C.gates.foldl pushW inp = _
                conv_lhs => rw [hsplit]
                rw [List.foldl_append, List.foldl_cons]
                change (C.gates.drop (k + 1)).foldl pushW w1 = _
                conv_lhs => rw [← List.take_append_drop m (C.gates.drop (k + 1))]
                rw [List.foldl_append]
              have hC_nk : (C.wires inp).getD (n + k) false = Cw.getD (n + k) false := by
                rw [hCw_full]; exact fold_getD_lt _ _ _ (by omega)
              have hC_rep : (C.wires inp).getD rep false = Cw.getD rep false := by
                rw [hCw_full]; exact fold_getD_lt _ _ _ (by omega)
              rw [hlo rep hrep_lt, ← hC_rep, ← hval, hC_nk]
          · rw [if_neg hw_eq, if_pos (by omega)]
            by_cases hw_in : w - 1 < n + k + m
            · have h1 := hhi (w - 1 - (n + k)) (by omega)
              have heq1 : n + k + (w - 1 - (n + k)) = w - 1 := by omega
              have heq2 : n + k + 1 + (w - 1 - (n + k)) = w := by omega
              rw [heq1, heq2] at h1
              exact h1
            · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      refine ⟨by dsimp [pushW]; simp [hDl]; omega, by dsimp [pushW]; simp [hCl]; omega, ?_, ?_⟩
      · intro i hi
        dsimp [pushW]
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hlo i hi
      · intro j hj
        by_cases hjm : j < m
        · dsimp [pushW]
          rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
          exact hhi j hjm
        · have hjeq : j = m := by omega
          subst hjeq
          dsimp [pushW]
          rw [← hDl, List.getD_append_right _ _ _ _ (le_refl _),
              ← hCl, List.getD_append_right _ _ _ _ (le_refl _)]
          simp only [Nat.sub_self, List.getD_cons_zero]
          exact hgate_eq
  have hfull := hsim (C.gates.length - (k + 1)) (by omega)
  have htake_all : (C.gates.drop (k + 1)).take (C.gates.length - (k + 1)) = C.gates.drop (k + 1) := by
    rw [List.take_of_length_le]; simp
  dsimp only at hfull
  rw [htake_all] at hfull
  obtain ⟨hDl, hCl, hlo, hhi⟩ := hfull
  have hDw_eq : (elimGate n k rep C).wires inp = ((C.gates.drop (k + 1)).map (remapGate (n + k) rep)).foldl pushW w0 := by
    change (C.gates.take k ++ (C.gates.drop (k + 1)).map (remapGate (n + k) rep)).foldl pushW inp = _
    rw [List.foldl_append]
  have hCw_eq : C.wires inp = (C.gates.drop (k + 1)).foldl pushW w1 := by
    change C.gates.foldl pushW inp = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  dsimp only [Circuit.eval]
  rw [hDw_eq, hCw_eq]
  change (((C.gates.drop (k + 1)).map (remapGate (n + k) rep)).foldl pushW w0).getD (remapIdx (n + k) rep C.output) false =
    ((C.gates.drop (k + 1)).foldl pushW w1).getD C.output false
  dsimp only [remapIdx]
  by_cases ho_lt : C.output < n + k
  · rw [if_neg (by omega), if_neg (by omega)]; exact hlo C.output ho_lt
  · by_cases ho_eq : C.output = n + k
    · rw [if_pos ho_eq]
      rcases hagree with ⟨hne, _⟩ | hval
      · exact absurd ho_eq.symm hne
      · rw [ho_eq, hlo rep hrep_lt, ← hCw_eq, ← hval, hCw_eq]
    · rw [if_neg ho_eq, if_pos (by omega)]
      by_cases ho_in : C.output - 1 < n + k + (C.gates.length - (k + 1))
      · have h1 := hhi (C.output - 1 - (n + k)) (by omega)
        have heq1 : n + k + (C.output - 1 - (n + k)) = C.output - 1 := by omega
        have heq2 : n + k + 1 + (C.output - 1 - (n + k)) = C.output := by omega
        rw [heq1, heq2] at h1; exact h1
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

private theorem wires_indep_of_unused {n : ℕ} (C : Circuit) (hC : FanInTwo C)
    (v : Fin n) (x y : Fin n → Bool)
    (hxy : ∀ i : Fin n, i ≠ v → x i = y i)
    (hskip : ∀ k (hk : k < C.gates.length),
      v.val ∉ actIn C.gates[k] ∨
        (C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) =
         C.gates[k].op.eval (C.gates[k].inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn y)).getD i false))) :
    ∀ w, w ≠ v.val → (C.wires (List.ofFn x)).getD w false = (C.wires (List.ofFn y)).getD w false := by
  have hstep : ∀ m (hm : m ≤ C.gates.length) (w : ℕ), w ≠ v.val →
      ((C.gates.take m).foldl pushW (List.ofFn x)).getD w false =
      ((C.gates.take m).foldl pushW (List.ofFn y)).getD w false := by
    intro m hm
    induction m with
    | zero =>
      intro w hw
      simp only [List.take_zero, List.foldl_nil]
      by_cases hwn : w < n
      · rw [List.getD_eq_getElem _ _ (by simp [hwn]), List.getD_eq_getElem _ _ (by simp [hwn]),
            List.getElem_ofFn, List.getElem_ofFn]
        exact hxy ⟨w, hwn⟩ (fun h => hw (congrArg Fin.val h))
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
    | succ m ih =>
      have hmlt : m < C.gates.length := by omega
      have htake : C.gates.take (m + 1) = C.gates.take m ++ [C.gates[m]] :=
        List.take_succ_eq_append_getElem hmlt
      set wx := (C.gates.take m).foldl pushW (List.ofFn x)
      set wy := (C.gates.take m).foldl pushW (List.ofFn y)
      have hwx_len : wx.length = n + m := by dsimp [wx]; rw [fold_len, List.length_ofFn, List.length_take]; omega
      have hwy_len : wy.length = n + m := by dsimp [wy]; rw [fold_len, List.length_ofFn, List.length_take]; omega
      have hval_eq : C.gates[m].op.eval (C.gates[m].inputs.map fun i => wx.getD i false) =
          C.gates[m].op.eval (C.gates[m].inputs.map fun i => wy.getD i false) := by
        rcases hskip m hmlt with hnotin | heq
        · have hgm := hC C.gates[m] (List.getElem_mem hmlt)
          rw [actIn_eval _ hgm.1 hgm.2, actIn_eval _ hgm.1 hgm.2]
          congr 1
          apply List.map_congr_left
          intro i hi
          exact ih (by omega) i (fun h => hnotin (h ▸ hi))
        · exact heq
      intro w hw
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (pushW wx C.gates[m]).getD w false = (pushW wy C.gates[m]).getD w false
      dsimp only [pushW]
      by_cases hlt : w < n + m
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ih (by omega) w hw
      · by_cases heq : w = n + m
        · subst heq
          have h1 : (wx ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => wx.getD i false)]).getD (n + m) false =
              C.gates[m].op.eval (C.gates[m].inputs.map fun i => wx.getD i false) := by
            rw [← hwx_len, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
          have h2 : (wy ++ [C.gates[m].op.eval (C.gates[m].inputs.map fun i => wy.getD i false)]).getD (n + m) false =
              C.gates[m].op.eval (C.gates[m].inputs.map fun i => wy.getD i false) := by
            rw [← hwy_len, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
          rw [h1, h2]
          exact hval_eq
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
  intro w hw
  have h := hstep C.gates.length (le_refl _) w hw
  rw [List.take_length] at h
  exact h

private theorem girth5_nonadj_nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hgirth : (5 : ℕ∞) ≤ G.egirth) (v u : Fin n) (hvu : v ≠ u) (hdeg : 2 ≤ G.degree v) :
    ∃ w : Fin n, G.Adj v w ∧ w ≠ u ∧ ¬ G.Adj u w := by
  have hcard : 2 ≤ (G.neighborFinset v).card := by simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdeg
  obtain ⟨w1, hw1, w2, hw2, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset v).card)
  rw [SimpleGraph.mem_neighborFinset] at hw1 hw2
  have hno3 : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → G.Adj c a → False := by
    intro a b c hab hbc hca
    have hne_ab : a ≠ b := G.ne_of_adj hab
    have hne_bc : b ≠ c := G.ne_of_adj hbc
    have hne_ca : c ≠ a := G.ne_of_adj hca
    let cyc : G.Walk a a := SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hca SimpleGraph.Walk.nil))
    have hcyc : cyc.IsCycle := by
      refine ⟨⟨⟨?_⟩, by simp [cyc]⟩, ?_⟩
      · simp [cyc, SimpleGraph.Walk.edges, hne_ab, hne_bc, hne_ca, hne_ab.symm, hne_ca.symm]
      · simp [cyc, hne_ab, hne_bc, hne_ca, hne_ab.symm, hne_bc.symm, hne_ca.symm]
    have h5 := (SimpleGraph.le_egirth.mp hgirth) a cyc hcyc
    have hlen : cyc.length = 3 := rfl
    rw [hlen] at h5
    exact absurd h5 (by decide)
  have hno4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → False := by
    intro a b c d hac hbd hab hbc hcd hda
    have hne_ab : a ≠ b := G.ne_of_adj hab
    have hne_bc : b ≠ c := G.ne_of_adj hbc
    have hne_cd : c ≠ d := G.ne_of_adj hcd
    have hne_da : d ≠ a := G.ne_of_adj hda
    let cyc : G.Walk a a := SimpleGraph.Walk.cons hab (SimpleGraph.Walk.cons hbc (SimpleGraph.Walk.cons hcd (SimpleGraph.Walk.cons hda SimpleGraph.Walk.nil)))
    have hcyc : cyc.IsCycle := by
      refine ⟨⟨⟨?_⟩, by simp [cyc]⟩, ?_⟩
      · simp [cyc, SimpleGraph.Walk.edges,
          hne_ab, hne_bc, hne_cd, hne_da, hac, hbd,
          hne_ab.symm, hne_da.symm, hac.symm]
      · simp [cyc, hne_ab, hne_bc, hne_cd, hne_da, hac, hbd,
          hne_ab.symm, hne_bc.symm, hne_cd.symm, hne_da.symm, hac.symm, hbd.symm]
    have h5 := (SimpleGraph.le_egirth.mp hgirth) a cyc hcyc
    have hlen : cyc.length = 4 := rfl
    rw [hlen] at h5
    exact absurd h5 (by decide)
  by_cases h1 : w1 ≠ u ∧ ¬ G.Adj u w1
  · exact ⟨w1, hw1, h1.1, h1.2⟩
  · by_cases h2 : w2 ≠ u ∧ ¬ G.Adj u w2
    · exact ⟨w2, hw2, h2.1, h2.2⟩
    · exfalso
      by_cases hw1u : w1 = u
      · subst hw1u
        have hw2u : w2 ≠ w1 := hne12.symm
        have huw2 : G.Adj w1 w2 := by
          by_contra hna; exact h2 ⟨hw2u, hna⟩
        exact hno3 v w1 w2 hw1 huw2 hw2.symm
      · by_cases hw2u : w2 = u
        · subst hw2u
          have huw1 : G.Adj w2 w1 := by
            by_contra hna; exact h1 ⟨hw1u, hna⟩
          exact hno3 v w2 w1 hw2 huw1 hw1.symm
        · have huw1 : G.Adj u w1 := by by_contra hna; exact h1 ⟨hw1u, hna⟩
          have huw2 : G.Adj u w2 := by by_contra hna; exact h2 ⟨hw2u, hna⟩
          exact hno4 v w1 u w2 hvu hne12 hw1 huw1.symm huw2 hw2.symm

private theorem filter_unique_of_idx {α : Type} (l : List α) (p : α → Bool) (k : ℕ)
    (hk : k < l.length) (hpk : p l[k] = true)
    (huniq : ∀ j (hj : j < l.length), p l[j] = true → j = k) :
    l.filter p = [l[k]] := by
  have hsplit : l = l.take k ++ l[k] :: l.drop (k + 1) := by
    conv_lhs => rw [← List.take_append_drop k l]
    congr 1; exact List.drop_eq_getElem_cons hk
  conv_lhs => rw [hsplit]
  rw [List.filter_append, List.filter_cons, if_pos hpk]
  have h1 : (l.take k).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha hp
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjl : j < l.length := by simp at hj; omega
    have hjk : j < k := by simp at hj; omega
    rw [List.getElem_take] at hp
    have := huniq j hjl hp
    omega
  have h2 : (l.drop (k + 1)).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha hp
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ha
    have hjl : k + 1 + j < l.length := by simp at hj; omega
    rw [List.getElem_drop] at hp
    have := huniq (k + 1 + j) hjl hp
    omega
  rw [h1, h2]
  rfl

theorem main :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : Circuit),
      (∀ x6 ∉ x4, (2 : ℕ) ≤ x2.degree x6) →
      (5 : ℕ∞) ≤ x2.egirth →
      (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) →
      IsMinimalCircuit x1 x5 →
      circuitFun x1 x5 = graphFun x2 ∅ →
      x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) →
      ∃ x12 ∉ x4, ∃ (x13 : ℕ) (x14 : Gate) (x15 : ℕ),
        x5.gates[x13]? = Option.some x14 ∧
        List.filter (fun (x16 : Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x12) x5.gates = [x14] ∧
        (x14.op = GateOp.and ∨ x14.op = GateOp.or) ∧
        x1 ≤ x15 ∧ x15 < x1 + x13 ∧ (x14.inputs = [↑x12, x15] ∨ x14.inputs = [x15, ↑x12]) := by
  classical
  intro n G hdec I C hdeg hgirth ⟨eu, ev, heuv⟩ hmin hcomp hsize
  have hfan : FanInTwo C := hmin.1
  have heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x => congrFun hcomp x
  -- 1. Output wire is a real gate wire: n ≤ C.output < n + C.size
  have hout_ge : n ≤ C.output := by
    by_contra hlt
    have hlt' : C.output < n := Nat.lt_of_not_le hlt
    let x : Fin n → Bool := fun i => decide (i.val = C.output)
    have h1 : C.eval (List.ofFn x) = true := by
      change (C.gates.foldl pushW (List.ofFn x)).getD C.output false = true
      rw [fold_getD_lt _ _ _ (by simp [hlt']), List.getD_eq_getElem _ _ (by simp [hlt']), List.getElem_ofFn]
      simp [x]
    rw [heval x] at h1
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
      decide_eq_true_eq] at h1
    obtain ⟨a, b, hab, ha, hb⟩ := h1
    simp only [x, decide_eq_true_eq] at ha hb
    exact G.loopless.irrefl a (by rwa [show b = a from Fin.ext (hb.trans ha.symm)] at hab)
  have hout_lt : C.output < n + C.size := by
    by_contra hge
    have hge' : n + C.gates.length ≤ C.output := Nat.le_of_not_lt hge
    let x : Fin n → Bool := fun i => decide (i = eu ∨ i = ev)
    have h1 : C.eval (List.ofFn x) = false := by
      change (C.gates.foldl pushW (List.ofFn x)).getD C.output false = false
      rw [List.getD_eq_default _ _ (by rw [fold_len, List.length_ofFn]; omega)]
    rw [heval x] at h1
    have h2 : graphFun G ∅ x = true := by
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq]
      exact ⟨eu, ev, heuv, by simp [x], by simp [x]⟩
    rw [h2] at h1; exact Bool.noConfusion h1
  -- 2. Every non-output gate k < C.size is read by some later gate j > k
  have hnonout_read : ∀ k < C.size, n + k ≠ C.output →
      ∃ j < C.size, k < j ∧ n + k ∈ actIn (gateAt C j) := by
    intro k hk hne
    by_contra hno
    push Not at hno
    let D := elimGate n k 0 C
    have hDfan : FanInTwo D := elimGate_fanIn n k 0 C hfan
    have hDeq : circuitFun n D = circuitFun n C := by
      funext x
      apply elimGate_eval_eq n k 0 C hfan hk x (by omega)
      left
      refine ⟨hne, fun j hkj hjl => ?_⟩
      have := hno j hjl hkj
      have hga : gateAt C j = C.gates[j] := by
        dsimp only [gateAt]; rw [List.getD_eq_getElem _ _ hjl]
      rwa [hga] at this
    have hle := hmin.2 D hDfan hDeq
    rw [elimGate_size n k 0 C hk] at hle
    have : 0 < C.gates.length := by omega
    omega
  -- 3. Active vertices V = univ \ I; every v ∈ V is read by ≥ 1 gate
  let V : Finset (Fin n) := Finset.univ \ I
  have hV_card : V.card = n - I.card := by
    dsimp [V]
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_fin]
  let R (w : ℕ) : Finset ℕ := (Finset.range C.size).filter (fun j => w ∈ actIn (gateAt C j))
  have hV_read : ∀ v ∈ V, 1 ≤ (R v.val).card := by
    intro v hv
    have hvI : v ∉ I := (Finset.mem_sdiff.mp hv).2
    have hdv := hdeg v hvI
    have hcard_nbr : 1 ≤ (G.neighborFinset v).card := by
      have := SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v); omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset v).card)
    rw [SimpleGraph.mem_neighborFinset] at hw
    by_contra h0
    have hR0 : R v.val = ∅ := Finset.card_eq_zero.mp (by omega)
    let x0 : Fin n → Bool := fun i => decide (i = w)
    let x1 : Fin n → Bool := fun i => decide (i = w ∨ i = v)
    have hsame : C.eval (List.ofFn x0) = C.eval (List.ofFn x1) := by
      apply wires_indep_of_unused C hfan v x0 x1
      · intro i hi; simp [x0, x1, hi]
      · intro k hk; left
        intro hmem
        have hga : gateAt C k = C.gates[k] := by dsimp [gateAt]; rw [List.getD_eq_getElem _ _ hk]
        have : k ∈ R v.val := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, by rwa [hga]⟩
        rw [hR0] at this; exact Finset.notMem_empty k this
      · omega
    rw [heval x0, heval x1] at hsame
    have hfx0 : graphFun G ∅ x0 = false := by
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_false_iff_not, not_exists, not_and]
      intro a b hab ha hb
      simp only [x0, decide_eq_true_eq] at ha hb
      subst ha; subst hb; exact G.loopless.irrefl _ hab
    have hfx1 : graphFun G ∅ x1 = true := by
      simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
        decide_eq_true_eq]
      exact ⟨v, w, hw, by simp [x1], by simp [x1]⟩
    rw [hfx0, hfx1] at hsame; exact Bool.noConfusion hsame
  -- 4. Suppose for contradiction the conclusion fails; then every v ∈ V with (R v).card = 1 is read ONLY by a NOT gate!
  by_contra hno_wit
  have hsingle_not : ∀ v ∈ V, (R v.val).card = 1 →
      ∃ k < C.size, R v.val = {k} ∧ (gateAt C k).op = GateOp.not ∧ actIn (gateAt C k) = [v.val] := by
    intro v hv hcard1
    obtain ⟨k, hk_eq⟩ := Finset.card_eq_one.mp hcard1
    have hk_mem : k ∈ R v.val := by rw [hk_eq]; exact Finset.mem_singleton_self k
    have hk_lt : k < C.size := Finset.mem_range.mp (Finset.mem_filter.mp hk_mem).1
    have hv_in : v.val ∈ actIn (gateAt C k) := (Finset.mem_filter.mp hk_mem).2
    have hga : gateAt C k = C.gates[k] := by dsimp [gateAt]; rw [List.getD_eq_getElem _ _ hk_lt]
    set g := C.gates[k]
    have hg_fan := hfan g (List.getElem_mem hk_lt)
    have hv_in_g : v.val ∈ actIn g := by rwa [hga] at hv_in
    have hfilt : List.filter (fun h => (actIn h).contains v.val) C.gates = [g] := by
      apply filter_unique_of_idx C.gates _ k hk_lt
      · exact List.contains_iff_mem.mpr hv_in_g
      · intro j hj hjp
        have hjm : v.val ∈ actIn (gateAt C j) := by
          have : gateAt C j = C.gates[j] := by dsimp [gateAt]; rw [List.getD_eq_getElem _ _ hj]
          rw [this]; exact List.contains_iff_mem.mp hjp
        have : j ∈ R v.val := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hjm⟩
        rw [hk_eq] at this; exact Finset.mem_singleton.mp this
    have hg_ops := hg_fan.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg_ops
    rcases hg_ops with hand | hor | hnot
    · -- g.op = .and: derive contradiction with hno_wit, minimality, or deg ≥ 2
      exfalso
      have hact_eq : actIn g = g.inputs := by
        dsimp [actIn]; rw [hand]
        have hev : GateOp.and.eval [Bool.false] = Bool.false := rfl
        rw [hev]; simp [List.take_of_length_le hg_fan.2]
      rw [hact_eq] at hv_in_g
      have hlen2 := hg_fan.2
      -- Helper: g cannot copy wire v.val (contradicts minimality!)
      have hno_copy : ¬ (∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD (n + k) false = (C.wires (List.ofFn x)).getD v.val false) := by
        intro hcp
        let D := elimGate n k v.val C
        have hle := hmin.2 D (elimGate_fanIn n k v.val C hfan) (by
          funext x; exact elimGate_eval_eq n k v.val C hfan hk_lt x (by omega) (Or.inr (hcp x)))
        rw [elimGate_size n k v.val C hk_lt] at hle; omega
      -- Helper: g cannot be constant false on all inputs (contradicts deg(v) ≥ 2!)
      have hno_const_false : ¬ (∀ x : Fin n → Bool,
          g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = false) := by
        intro hcf
        have hvI : v ∉ I := (Finset.mem_sdiff.mp hv).2
        have hcard_nbr : 1 ≤ (G.neighborFinset v).card := by
          have := SimpleGraph.card_neighborFinset_eq_degree (G := G) (v := v); have := hdeg v hvI; omega
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (G.neighborFinset v).card)
        rw [SimpleGraph.mem_neighborFinset] at hw
        let x0 : Fin n → Bool := fun i => decide (i = w)
        let x1 : Fin n → Bool := fun i => decide (i = w ∨ i = v)
        have hsame : C.eval (List.ofFn x0) = C.eval (List.ofFn x1) := by
          apply wires_indep_of_unused C hfan v x0 x1
          · intro i hi; simp [x0, x1, hi]
          · intro j hj
            by_cases hjk : j = k
            · subst j; right
              change g.op.eval (g.inputs.map _) = g.op.eval (g.inputs.map _)
              rw [hcf x0, hcf x1]
            · left; intro hmem
              have hga' : gateAt C j = C.gates[j] := by dsimp [gateAt]; rw [List.getD_eq_getElem _ _ hj]
              have : j ∈ R v.val := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, by rwa [hga']⟩
              rw [hk_eq] at this; exact hjk (Finset.mem_singleton.mp this)
          · omega
        rw [heval x0, heval x1] at hsame
        have hfx0 : graphFun G ∅ x0 = false := by
          simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
            decide_eq_false_iff_not, not_exists, not_and]
          intro a b hab ha hb; simp only [x0, decide_eq_true_eq] at ha hb
          subst ha; subst hb; exact G.loopless.irrefl _ hab
        have hfx1 : graphFun G ∅ x1 = true := by
          simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
            decide_eq_true_eq]
          exact ⟨v, w, hw, by simp [x1], by simp [x1]⟩
        rw [hfx0, hfx1] at hsame; exact Bool.noConfusion hsame
      -- Extract the other wire u from g.inputs!
      have hv_wire : ∀ x : Fin n → Bool,
          ((C.gates.take k).foldl pushW (List.ofFn x)).getD v.val false =
          (C.wires (List.ofFn x)).getD v.val false := by
        intro x
        change _ = (C.gates.foldl pushW (List.ofFn x)).getD v.val false
        rw [fold_getD_lt _ _ _ (by simp [v.isLt]), fold_getD_lt _ _ _ (by simp [v.isLt])]
      have hpair : ∃ u : ℕ, u ≠ v.val ∧ (g.inputs = [v.val, u] ∨ g.inputs = [u, v.val]) := by
        cases hgi : g.inputs with
        | nil => rw [hgi] at hv_in_g; simp at hv_in_g
        | cons a rest =>
          cases rest with
          | nil =>
            rw [hgi] at hv_in_g; simp only [List.mem_singleton] at hv_in_g
            subst hv_in_g
            exfalso; apply hno_copy; intro x
            have h1 := wires_getD_gate C (List.ofFn x) k hk_lt
            rw [List.length_ofFn] at h1; rw [h1]
            change g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = _
            rw [hand, hgi]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, hv_wire x]
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              rw [hgi] at hv_in_g; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv_in_g
              rcases hv_in_g with rfl | rfl
              · by_cases hbv : b = v.val
                · subst hbv; exfalso; apply hno_copy; intro x
                  have h1 := wires_getD_gate C (List.ofFn x) k hk_lt
                  rw [List.length_ofFn] at h1; rw [h1]
                  change g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = _
                  rw [hand, hgi]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self, hv_wire x]
                · exact ⟨b, hbv, Or.inl rfl⟩
              · by_cases hav : a = v.val
                · subst hav; exfalso; apply hno_copy; intro x
                  have h1 := wires_getD_gate C (List.ofFn x) k hk_lt
                  rw [List.length_ofFn] at h1; rw [h1]
                  change g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = _
                  rw [hand, hgi]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self, hv_wire x]
                · exact ⟨a, hav, Or.inr rfl⟩
            | cons _ _ => rw [hgi] at hlen2; simp at hlen2
      obtain ⟨u, huv, hgin⟩ := hpair
      by_cases hu_ge : n + k ≤ u
      · apply hno_const_false; intro x
        have hk_len : k < C.gates.length := hk_lt
        have hlen_w : ((C.gates.take k).foldl pushW (List.ofFn x)).length = n + k := by
          rw [fold_len, List.length_ofFn, List.length_take]; omega
        have hu_f : ((C.gates.take k).foldl pushW (List.ofFn x)).getD u false = false :=
          List.getD_eq_default _ _ (by omega)
        rcases hgin with h1 | h1 <;> (
          rw [hand, h1]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hu_f, Bool.and_false, Bool.false_and, Bool.and_true])
      · by_cases hu_lt : u < n
        · -- u < n: pick neighbor w ≠ u of v, set x_w = 1, x_u = 0, flip x_v!
          have hvI : v ∉ I := (Finset.mem_sdiff.mp hv).2
          have hcard_nbr : 2 ≤ (G.neighborFinset v).card := by
            simpa [SimpleGraph.card_neighborFinset_eq_degree] using hdeg v hvI
          obtain ⟨w1, hw1, w2, hw2, hne12⟩ := Finset.one_lt_card.mp (by omega : 1 < (G.neighborFinset v).card)
          rw [SimpleGraph.mem_neighborFinset] at hw1 hw2
          have hex_w : ∃ w : Fin n, G.Adj v w ∧ w.val ≠ u := by
            by_cases h1 : w1.val = u
            · exact ⟨w2, hw2, fun h2 => hne12 (Fin.ext (h1.trans h2.symm))⟩
            · exact ⟨w1, hw1, h1⟩
          obtain ⟨w, hvw, hwu⟩ := hex_w
          let x0 : Fin n → Bool := fun i => decide (i = w)
          let x1 : Fin n → Bool := fun i => decide (i = w ∨ i = v)
          have hsame : C.eval (List.ofFn x0) = C.eval (List.ofFn x1) := by
            apply wires_indep_of_unused C hfan v x0 x1
            · intro i hi; simp [x0, x1, hi]
            · intro j hj
              by_cases hjk : j = k
              · subst j; right
                change g.op.eval (g.inputs.map _) = g.op.eval (g.inputs.map _)
                have hu0 : ((C.gates.take k).foldl pushW (List.ofFn x0)).getD u false = false := by
                  rw [fold_getD_lt _ _ _ (by simp [hu_lt]), List.getD_eq_getElem _ _ (by simp [hu_lt]),
                      List.getElem_ofFn]
                  simp [x0, Fin.ext_iff, Ne.symm hwu]
                have hu1 : ((C.gates.take k).foldl pushW (List.ofFn x1)).getD u false = false := by
                  rw [fold_getD_lt _ _ _ (by simp [hu_lt]), List.getD_eq_getElem _ _ (by simp [hu_lt]),
                      List.getElem_ofFn]
                  simp [x1, Fin.ext_iff, Ne.symm hwu, huv]
                rcases hgin with h1 | h1 <;> (
                  rw [hand, h1]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, hu0, hu1, Bool.and_false, Bool.false_and, Bool.and_true])
              · left; intro hmem
                have hga' : gateAt C j = C.gates[j] := by dsimp [gateAt]; rw [List.getD_eq_getElem _ _ hj]
                have : j ∈ R v.val := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, by rwa [hga']⟩
                rw [hk_eq] at this; exact hjk (Finset.mem_singleton.mp this)
            · omega
          rw [heval x0, heval x1] at hsame
          have hfx0 : graphFun G ∅ x0 = false := by
            simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
              decide_eq_false_iff_not, not_exists, not_and]
            intro a b hab ha hb; simp only [x0, decide_eq_true_eq] at ha hb
            subst ha; subst hb; exact G.loopless.irrefl _ hab
          have hfx1 : graphFun G ∅ x1 = true := by
            simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
              decide_eq_true_eq]
            exact ⟨v, w, hvw, by simp [x1], by simp [x1]⟩
          rw [hfx0, hfx1] at hsame; exact Bool.noConfusion hsame
        · -- n ≤ u < n + k: WITNESS FOUND!
          exact hno_wit ⟨v, (Finset.mem_sdiff.mp hv).2, k, g, u, List.getElem?_eq_getElem hk_lt,
            hfilt, Or.inl hand, by omega, by omega, hgin⟩
    · -- g.op = .or: symmetric + girth ≥ 5!
      exfalso
      have hact_eq : actIn g = g.inputs := by
        dsimp [actIn]; rw [hor]
        have hev : GateOp.or.eval [Bool.false] = Bool.false := rfl
        rw [hev]; simp [List.take_of_length_le hg_fan.2]
      rw [hact_eq] at hv_in_g
      have hlen2 := hg_fan.2
      have hno_copy : ¬ (∀ x : Fin n → Bool,
          (C.wires (List.ofFn x)).getD (n + k) false = (C.wires (List.ofFn x)).getD v.val false) := by
        intro hcp
        let D := elimGate n k v.val C
        have hle := hmin.2 D (elimGate_fanIn n k v.val C hfan) (by
          funext x; exact elimGate_eval_eq n k v.val C hfan hk_lt x (by omega) (Or.inr (hcp x)))
        rw [elimGate_size n k v.val C hk_lt] at hle; omega
      have hv_wire : ∀ x : Fin n → Bool,
          ((C.gates.take k).foldl pushW (List.ofFn x)).getD v.val false =
          (C.wires (List.ofFn x)).getD v.val false := by
        intro x
        change _ = (C.gates.foldl pushW (List.ofFn x)).getD v.val false
        rw [fold_getD_lt _ _ _ (by simp [v.isLt]), fold_getD_lt _ _ _ (by simp [v.isLt])]
      have hpair : ∃ u : ℕ, u ≠ v.val ∧ (g.inputs = [v.val, u] ∨ g.inputs = [u, v.val]) := by
        cases hgi : g.inputs with
        | nil => rw [hgi] at hv_in_g; simp at hv_in_g
        | cons a rest =>
          cases rest with
          | nil =>
            rw [hgi] at hv_in_g; simp only [List.mem_singleton] at hv_in_g
            subst hv_in_g
            exfalso; apply hno_copy; intro x
            have h1 := wires_getD_gate C (List.ofFn x) k hk_lt
            rw [List.length_ofFn] at h1; rw [h1]
            change g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = _
            rw [hor, hgi]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, hv_wire x]
          | cons b rest2 =>
            cases rest2 with
            | nil =>
              rw [hgi] at hv_in_g; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv_in_g
              rcases hv_in_g with rfl | rfl
              · by_cases hbv : b = v.val
                · subst hbv; exfalso; apply hno_copy; intro x
                  have h1 := wires_getD_gate C (List.ofFn x) k hk_lt
                  rw [List.length_ofFn] at h1; rw [h1]
                  change g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = _
                  rw [hor, hgi]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self, hv_wire x]
                · exact ⟨b, hbv, Or.inl rfl⟩
              · by_cases hav : a = v.val
                · subst hav; exfalso; apply hno_copy; intro x
                  have h1 := wires_getD_gate C (List.ofFn x) k hk_lt
                  rw [List.length_ofFn] at h1; rw [h1]
                  change g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = _
                  rw [hor, hgi]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self, hv_wire x]
                · exact ⟨a, hav, Or.inr rfl⟩
            | cons _ _ => rw [hgi] at hlen2; simp at hlen2
      obtain ⟨u, huv, hgin⟩ := hpair
      by_cases hu_ge : n + k ≤ u
      · apply hno_copy; intro x
        have h1 := wires_getD_gate C (List.ofFn x) k hk_lt
        rw [List.length_ofFn] at h1; rw [h1]
        change g.op.eval (g.inputs.map fun i => ((C.gates.take k).foldl pushW (List.ofFn x)).getD i false) = _
        have hk_len : k < C.gates.length := hk_lt
        have hlen_w : ((C.gates.take k).foldl pushW (List.ofFn x)).length = n + k := by
          rw [fold_len, List.length_ofFn, List.length_take]; omega
        have hu_f : ((C.gates.take k).foldl pushW (List.ofFn x)).getD u false = false :=
          List.getD_eq_default _ _ (by omega)
        rcases hgin with h2 | h2 <;> (
          rw [hor, h2]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hu_f, Bool.or_false, Bool.false_or, hv_wire x])
      · by_cases hu_lt : u < n
        · -- u < n: use girth ≥ 5 to get neighbor w of v with w ≠ u' and ¬ G.Adj u' w!
          let u' : Fin n := ⟨u, hu_lt⟩
          have hvu' : v ≠ u' := fun h => huv (congrArg Fin.val h).symm
          obtain ⟨w, hvw, hwu', hna⟩ := girth5_nonadj_nbr G hgirth v u' hvu' (hdeg v (Finset.mem_sdiff.mp hv).2)
          let x0 : Fin n → Bool := fun i => decide (i = u' ∨ i = w)
          let x1 : Fin n → Bool := fun i => decide (i = u' ∨ i = w ∨ i = v)
          have hsame : C.eval (List.ofFn x0) = C.eval (List.ofFn x1) := by
            apply wires_indep_of_unused C hfan v x0 x1
            · intro i hi; simp [x0, x1, hi]
            · intro j hj
              by_cases hjk : j = k
              · subst j; right
                change g.op.eval (g.inputs.map _) = g.op.eval (g.inputs.map _)
                have hu0 : ((C.gates.take k).foldl pushW (List.ofFn x0)).getD u false = true := by
                  rw [fold_getD_lt _ _ _ (by simp [hu_lt]), List.getD_eq_getElem _ _ (by simp [hu_lt]),
                      List.getElem_ofFn]
                  simp [x0, u']
                have hu1 : ((C.gates.take k).foldl pushW (List.ofFn x1)).getD u false = true := by
                  rw [fold_getD_lt _ _ _ (by simp [hu_lt]), List.getD_eq_getElem _ _ (by simp [hu_lt]),
                      List.getElem_ofFn]
                  simp [x1, u']
                rcases hgin with h1 | h1 <;> (
                  rw [hor, h1]
                  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, hu0, hu1, Bool.or_true, Bool.true_or, Bool.or_false])
              · left; intro hmem
                have hga' : gateAt C j = C.gates[j] := by dsimp [gateAt]; rw [List.getD_eq_getElem _ _ hj]
                have : j ∈ R v.val := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, by rwa [hga']⟩
                rw [hk_eq] at this; exact hjk (Finset.mem_singleton.mp this)
            · omega
          rw [heval x0, heval x1] at hsame
          have hfx0 : graphFun G ∅ x0 = false := by
            simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
              decide_eq_false_iff_not, not_exists, not_and]
            intro a b hab ha hb; simp only [x0, decide_eq_true_eq] at ha hb
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact G.loopless.irrefl _ hab
            · exact hna hab
            · exact hna hab.symm
            · exact G.loopless.irrefl _ hab
          have hfx1 : graphFun G ∅ x1 = true := by
            simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or,
              decide_eq_true_eq]
            exact ⟨v, w, hvw, by simp [x1], by simp [x1]⟩
          rw [hfx0, hfx1] at hsame; exact Bool.noConfusion hsame
        · exact hno_wit ⟨v, (Finset.mem_sdiff.mp hv).2, k, g, u, List.getElem?_eq_getElem hk_lt,
            hfilt, Or.inr hor, by omega, by omega, hgin⟩
    · -- g.op = .not: record!
      refine ⟨k, hk_lt, hk_eq, by rw [hga]; exact hnot, ?_⟩
      rw [hga]
      have hlen1 : (actIn g).length ≤ 1 := (actIn_len_le g).2 hnot
      cases hact : actIn g with
      | nil => rw [hact] at hv_in_g; simp at hv_in_g
      | cons a rest =>
        cases rest with
        | nil =>
          rw [hact] at hv_in_g; simp only [List.mem_singleton] at hv_in_g
          subst hv_in_g; rfl
        | cons _ _ => rw [hact] at hlen1; simp at hlen1
  -- 5. Slot counting contradiction: 2 * m - 1 ≤ C.size!
  let V1 : Finset (Fin n) := V.filter (fun v => (R v.val).card = 1)
  let V2 : Finset (Fin n) := V.filter (fun v => 2 ≤ (R v.val).card)
  have hV_split : V1.card + V2.card = V.card := by
    have hd : Disjoint V1 V2 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
    have hu : V1 ∪ V2 = V := by
      ext v; simp only [V1, V2, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
      · intro hv
        have := hV_read v hv
        by_cases h1 : (R v.val).card = 1
        · exact Or.inl ⟨hv, h1⟩
        · exact Or.inr ⟨hv, by omega⟩
    rw [← Finset.card_union_of_disjoint hd, hu]
  let Nnot : Finset ℕ := (Finset.range C.size).filter (fun j => (gateAt C j).op = GateOp.not)
  have hV1_le_Nnot : V1.card ≤ Nnot.card := by
    let f : Fin n → ℕ := fun v =>
      if h : v ∈ V1 then Classical.choose (hsingle_not v (Finset.mem_filter.mp h).1 (Finset.mem_filter.mp h).2) else 0
    have hf_mem : ∀ v ∈ V1, f v ∈ Nnot := by
      intro v hv
      simp only [f, hv, ↓reduceDIte]
      have hsp := Classical.choose_spec (hsingle_not v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2)
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hsp.1, hsp.2.2.1⟩
    have hf_inj : Set.InjOn f V1 := by
      intro v1 hv1 v2 hv2 heq
      have hv1' : v1 ∈ V1 := Finset.mem_coe.mp hv1
      have hv2' : v2 ∈ V1 := Finset.mem_coe.mp hv2
      simp only [f, hv1', hv2', ↓reduceDIte] at heq
      have hs1 := Classical.choose_spec (hsingle_not v1 (Finset.mem_filter.mp hv1').1 (Finset.mem_filter.mp hv1').2)
      have hs2 := Classical.choose_spec (hsingle_not v2 (Finset.mem_filter.mp hv2').1 (Finset.mem_filter.mp hv2').2)
      have hact1 := hs1.2.2.2
      have hact2 := hs2.2.2.2
      rw [heq] at hact1
      have hlist := hact1.symm.trans hact2
      exact Fin.ext (List.cons.inj hlist).1
    calc V1.card = (V1.image f).card := (Finset.card_image_of_injOn hf_inj).symm
      _ ≤ Nnot.card := Finset.card_le_card (Finset.image_subset_iff.mpr hf_mem)
  -- Upper bound on sum of active input lengths: ≤ 2 * C.size - Nnot.card
  have hsum_upper : (∑ j ∈ Finset.range C.size, (actIn (gateAt C j)).length) + Nnot.card ≤ 2 * C.size := by
    have h1 : ∑ j ∈ Finset.range C.size, ((actIn (gateAt C j)).length + if (gateAt C j).op = GateOp.not then 1 else 0) ≤
        ∑ _j ∈ Finset.range C.size, 2 := by
      apply Finset.sum_le_sum
      intro j _
      have hlen := actIn_len_le (gateAt C j)
      split_ifs with hnot
      · have := hlen.2 hnot; omega
      · have := hlen.1; omega
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at h1
    have hN : ∑ j ∈ Finset.range C.size, (if (gateAt C j).op = GateOp.not then 1 else 0) = Nnot.card := by
      rw [Finset.sum_boole]; rfl
    rw [hN] at h1
    omega
  -- Lower bound via double counting wires w ∈ W = (V.image Fin.val) ∪ (non-output gate wires)
  let WV : Finset ℕ := V.image Fin.val
  let WG : Finset ℕ := ((Finset.range C.size).erase (C.output - n)).image (n + ·)
  have hdisj_W : Disjoint WV WG := by
    rw [Finset.disjoint_left]
    intro w hw1 hw2
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw1
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hw2
    omega
  have hsum_lower : V1.card + 2 * V2.card + (C.size - 1) ≤
      ∑ j ∈ Finset.range C.size, (actIn (gateAt C j)).length := by
    have hswap : ∑ w ∈ WV ∪ WG, (R w).card =
        ∑ j ∈ Finset.range C.size, ((WV ∪ WG).filter (fun w => w ∈ actIn (gateAt C j))).card := by
      simp only [R, Finset.card_filter]
      exact Finset.sum_comm
    have hstep1 : ∑ j ∈ Finset.range C.size, ((WV ∪ WG).filter (fun w => w ∈ actIn (gateAt C j))).card ≤
        ∑ j ∈ Finset.range C.size, (actIn (gateAt C j)).length := by
      apply Finset.sum_le_sum
      intro j _
      calc ((WV ∪ WG).filter (fun w => w ∈ actIn (gateAt C j))).card
          ≤ (actIn (gateAt C j)).toFinset.card := Finset.card_le_card (fun w hw => List.mem_toFinset.mpr (Finset.mem_filter.mp hw).2)
        _ ≤ (actIn (gateAt C j)).length := List.toFinset_card_le _
    rw [Finset.sum_union hdisj_W] at hswap
    have hWV_sum : V1.card + 2 * V2.card ≤ ∑ w ∈ WV, (R w).card := by
      rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
      have hd : Disjoint V1 V2 := Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
      have hu : V1 ∪ V2 = V := by
        ext v; simp only [V1, V2, Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
        · intro hv; have := hV_read v hv
          by_cases h1 : (R v.val).card = 1; exact Or.inl ⟨hv, h1⟩; exact Or.inr ⟨hv, by omega⟩
      rw [← hu, Finset.sum_union hd]
      have h1 : V1.card ≤ ∑ v ∈ V1, (R v.val).card := by
        calc V1.card = ∑ _v ∈ V1, 1 := by simp
          _ ≤ ∑ v ∈ V1, (R v.val).card := Finset.sum_le_sum (fun v hv => by have := (Finset.mem_filter.mp hv).2; omega)
      have h2 : 2 * V2.card ≤ ∑ v ∈ V2, (R v.val).card := by
        calc 2 * V2.card = ∑ _v ∈ V2, 2 := by simp [mul_comm]
          _ ≤ ∑ v ∈ V2, (R v.val).card := Finset.sum_le_sum (fun v hv => (Finset.mem_filter.mp hv).2)
      omega
    have hWG_sum : C.size - 1 ≤ ∑ w ∈ WG, (R w).card := by
      have hcard_WG : WG.card = C.size - 1 := by
        dsimp [WG]
        rw [Finset.card_image_of_injective _ (fun a b h => by omega),
            Finset.card_erase_of_mem (Finset.mem_range.mpr (by omega)), Finset.card_range]
      calc C.size - 1 = ∑ _w ∈ WG, 1 := by simp [hcard_WG]
        _ ≤ ∑ w ∈ WG, (R w).card := by
          apply Finset.sum_le_sum
          intro w hw
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
          have hne : k ≠ C.output - n := (Finset.mem_erase.mp hk).1
          have hkl : k < C.size := Finset.mem_range.mp (Finset.mem_erase.mp hk).2
          obtain ⟨j, hj, _, hmem⟩ := hnonout_read k hkl (by omega)
          exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hmem⟩⟩
    omega
  omega

end PEqualNP.Outside.L_meta_18930

theorem PEqualNP.Outside.L_meta_18930 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x6 ∉ x4, (2 : ℕ) ≤ x2.degree x6) → (5 : ℕ∞) ≤ x2.egirth → (∃ (x8 : Fin x1) (x9 : Fin x1), x2.Adj x8 x9) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ → x5.size < (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) → ∃ x12 ∉ x4, ∃ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate) (x15 : ℕ), x5.gates[x13]? = Option.some x14 ∧ List.filter (fun (x16 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x16.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x16.inputs).contains ↑x12) x5.gates = [x14] ∧ (x14.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ x1 ≤ x15 ∧ x15 < x1 + x13 ∧ (x14.inputs = [↑x12, x15] ∨ x14.inputs = [x15, ↑x12])
    :=
  PEqualNP.Outside.L_meta_18930.main
