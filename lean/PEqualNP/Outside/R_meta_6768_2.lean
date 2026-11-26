import Mathlib.Data.Finset.Card
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover PEqualNP.ReadTwo

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_6768_2
(residual : let G := edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun t => (t / 11, t % 11))
    ∀ C : Circuit, IsLeastAO G C → TopForm G C → 2 ≤ (junk G C).card → C.size ≤ 21 →
      2*(centreless G C).card + (junk G C).card + (orN G C \ lam G C).card < 2*(Ustar G C).card →
      (∀ v : Fin 11, v.val < 4 → (readers 0 C v.val).card ≤ 2) →
      (∀ v a b : Fin 11, v.val < 4 → a ≤ b → v ≠ a → v ≠ b → ¬ G.Adj a b →
        readers 0 C v.val ⊆ readers 0 C a.val ∪ readers 0 C b.val →
        121*v.val+11*a.val+b.val ∈ ([29, 30, 49, 51, 61, 74, 186, 230, 250, 295, 316, 317, 472] : List ℕ)) →
      ∃ v : Fin 11, v.val < 4 ∧ (let dup := (fun j : ℕ => ∃ k < 11+j, ∀ x : Fin 11 → Bool, x v = false → wval C x (11+j) = wval C x k);
        ∃ i j k, i < j ∧ j < k ∧ k < C.size ∧ dup i ∧ dup j ∧ dup k)) :
(let x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       (2 : ℕ) ≤ (PEqualNP.TopForm.junk x1 x2).card →         x2.size ≤ (21 : ℕ) →           (2 : ℕ) * (PEqualNP.TopForm.centreless x1 x2).card + (PEqualNP.TopForm.junk x1 x2).card + (PEqualNP.TopForm.orN x1 x2 \ PEqualNP.TopForm.lam x1 x2).card < (2 : ℕ) * (PEqualNP.TopForm.Ustar x1 x2).card →             (∀ (x8 : Fin (11 : ℕ)), ↑x8 < (4 : ℕ) → (∀ x10 < x2.size, ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∀ (x10 x11 x12 : ℕ), x10 < x11 → x11 < x12 → x12 < x2.size → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x10).inputs → ↑x8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x11).inputs → ↑x8 ∉ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x12).inputs) →               ∃ (x9 : Fin (11 : ℕ)),                 ↑x9 < (4 : ℕ) ∧                   have x10 : ℕ → Prop := fun (x10 : ℕ) => ∃ x11 < (11 : ℕ) + x10, ∀ (x12 : Fin (11 : ℕ) → Bool), x12 x9 = Bool.false → PEqualNP.ReadTwo.wval x2 x12 ((11 : ℕ) + x10) = PEqualNP.ReadTwo.wval x2 x12 x11;                   ∃ (x11 : ℕ) (x12 : ℕ) (x13 : ℕ), x11 < x12 ∧ x12 < x13 ∧ x13 < x2.size ∧ x10 x11 ∧ x10 x12 ∧ x10 x13) := by
  let step : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have fold_getD_lt : ∀ (gs : List Gate) (w : List Bool) (k : ℕ), k < w.length →
      (gs.foldl step w).getD k false = w.getD k false := by
    intro gs w k hk
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons]
      rw [ih (step w g) (by simp [step]; omega)]
      dsimp [step]
      rw [List.getD_append _ _ _ _ hk]
  have fold_getD_ne : ∀ (gs : List Gate) (v a b : ℕ)
      (hread : ∀ g ∈ gs, v ∈ g.inputs →
        g.op = GateOp.or ∧ (a ∈ g.inputs ∨ b ∈ g.inputs))
      (hge : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (hva : v ≠ a) (hvb : v ≠ b)
      (wx wy : List Bool) (hlen : wx.length = wy.length)
      (hva_len : v < wx.length) (ha_len : a < wx.length) (hb_len : b < wx.length)
      (hne : ∀ k, k ≠ v → wx.getD k false = wy.getD k false)
      (ha : wx.getD a false = true) (hb : wx.getD b false = true)
      (ha' : wy.getD a false = true) (hb' : wy.getD b false = true),
      ∀ k, k ≠ v → (gs.foldl step wx).getD k false = (gs.foldl step wy).getD k false := by
    intro gs v a b hread hge hva hvb wx wy hlen hva_len ha_len hb_len hne ha hb ha' hb'
    induction gs generalizing wx wy with
    | nil => simpa using hne
    | cons g gs ih =>
      have hgread := hread g (by simp)
      have hgge := hge g (by simp)
      have hval : g.op.eval (g.inputs.map fun i => wx.getD i false) =
          g.op.eval (g.inputs.map fun i => wy.getD i false) := by
        rcases hgge with hop | hop
        · -- AND cannot read v
          have hvnot : v ∉ g.inputs := by
            intro hv
            rcases hgread hv with ⟨hop', _⟩
            rw [hop] at hop'
            cases hop'
          apply congrArg g.op.eval
          apply List.map_congr_left
          intro i hi
          exact hne i (fun hiv => hvnot (hiv ▸ hi))
        · by_cases hv : v ∈ g.inputs
          · rcases hgread hv with ⟨_, hmem | hmem⟩
            · have hx : (g.inputs.map fun i => wx.getD i false).any id = true := by
                apply List.any_eq_true.mpr
                exact ⟨wx.getD a false, List.mem_map.mpr ⟨a, hmem, rfl⟩, ha⟩
              have hy : (g.inputs.map fun i => wy.getD i false).any id = true := by
                apply List.any_eq_true.mpr
                exact ⟨wy.getD a false, List.mem_map.mpr ⟨a, hmem, rfl⟩, ha'⟩
              rw [hop]
              simp only [GateOp.eval]
              rw [hx, hy]
            · have hx : (g.inputs.map fun i => wx.getD i false).any id = true := by
                apply List.any_eq_true.mpr
                exact ⟨wx.getD b false, List.mem_map.mpr ⟨b, hmem, rfl⟩, hb⟩
              have hy : (g.inputs.map fun i => wy.getD i false).any id = true := by
                apply List.any_eq_true.mpr
                exact ⟨wy.getD b false, List.mem_map.mpr ⟨b, hmem, rfl⟩, hb'⟩
              rw [hop]
              simp only [GateOp.eval]
              rw [hx, hy]
          · apply congrArg g.op.eval
            apply List.map_congr_left
            intro i hi
            exact hne i (fun hiv => hv (hiv ▸ hi))
      let vx := g.op.eval (g.inputs.map fun i => wx.getD i false)
      let vy := g.op.eval (g.inputs.map fun i => wy.getD i false)
      have hxy : vx = vy := hval
      have hlen' : (wx ++ [vx]).length = (wy ++ [vy]).length := by simp [hlen]
      have hva' : v < (wx ++ [vx]).length := by simp; omega
      have ha'len : a < (wx ++ [vx]).length := by simp; omega
      have hb'len : b < (wx ++ [vx]).length := by simp; omega
      have hne' : ∀ k, k ≠ v →
          (wx ++ [vx]).getD k false = (wy ++ [vy]).getD k false := by
        intro k hk
        by_cases hkw : k < wx.length
        · rw [List.getD_append _ _ _ _ hkw, List.getD_append _ _ _ _ (by simpa [hlen] using hkw)]
          exact hne k hk
        · by_cases hkeq : k = wx.length
          · subst k
            rw [List.getD_append_right _ _ _ _ (le_refl _),
              List.getD_append_right _ _ _ _ (by simpa [hlen] using (le_refl wx.length))]
            simp [hxy, hlen]
          · have hkgt : wx.length < k := by omega
            rw [List.getD_eq_default _ _ (by simp; omega),
              List.getD_eq_default _ _ (by simp [hlen]; omega)]
      have ha'' : (wx ++ [vx]).getD a false = true := by
        rw [List.getD_append _ _ _ _ ha_len]; exact ha
      have hb'' : (wx ++ [vx]).getD b false = true := by
        rw [List.getD_append _ _ _ _ hb_len]; exact hb
      have ha''' : (wy ++ [vy]).getD a false = true := by
        rw [List.getD_append _ _ _ _ (by simpa [hlen] using ha_len)]; exact ha'
      have hb''' : (wy ++ [vy]).getD b false = true := by
        rw [List.getD_append _ _ _ _ (by simpa [hlen] using hb_len)]; exact hb'
      exact ih (fun g hg => hread g (by simp [hg])) (fun g hg => hge g (by simp [hg]))
        (wx ++ [vx]) (wy ++ [vy]) hlen' hva' ha'len hb'len hne' ha'' hb'' ha''' hb'''
  have shield :  ∀ (n : ℕ) (C : Circuit) (v a b : Fin n), IsAO2 n C → v ≠ a → v ≠ b →
    (∀ j < C.size, v.val ∈ (gateAt C j).inputs →
      (gateAt C j).op = GateOp.or ∧ (a.val ∈ (gateAt C j).inputs ∨ b.val ∈ (gateAt C j).inputs)) →
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) = x v) ∨ ∀ (x y : Fin n → Bool), x a = true → x b = true →
      (∀ k, k ≠ v → x k = y k) → C.eval (List.ofFn x) = C.eval (List.ofFn y) := fun n C v a b hAO hva hvb hshield => by

      classical
      have hgread : ∀ g ∈ C.gates, v.val ∈ g.inputs →
          g.op = GateOp.or ∧ (a.val ∈ g.inputs ∨ b.val ∈ g.inputs) := by
        intro g hg hv
        obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp hg
        rw [← hgj] at hv
        have hgate : gateAt C j = C.gates[j] := by simp [gateAt, hj]
        simpa [hgate, hgj] using hshield j hj (by simpa [hgate] using hv)
      have hge : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or :=
        hAO.1
      have hne0 (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
          ∀ k, k ≠ v.val → (List.ofFn x).getD k false = (List.ofFn y).getD k false := by
        intro k hk
        by_cases hkn : k < n
        · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simpa using hkn),
            List.getElem?_eq_getElem (by simpa using hkn)]
          simp only [Option.getD_some, List.getElem_ofFn]
          exact hxy ⟨k, hkn⟩ (fun h => hk (congrArg Fin.val h))
        · rw [List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
      have hbase (x y : Fin n → Bool) (hxy : ∀ k, k ≠ v → x k = y k) :
          ∀ k, k ≠ v.val → (List.ofFn x).getD k false = (List.ofFn y).getD k false :=
        hne0 x y hxy
      have hva' : v.val ≠ a.val := fun h => hva (Fin.ext h)
      have hvb' : v.val ≠ b.val := fun h => hvb (Fin.ext h)
      by_cases hout : C.output < n
      · by_cases hov : C.output = v.val
        · left
          intro x
          have hw : (C.wires (List.ofFn x)).getD C.output false =
              (List.ofFn x).getD C.output false := by
            change (C.gates.foldl step (List.ofFn x)).getD C.output false = _
            exact fold_getD_lt C.gates (List.ofFn x) C.output (by simpa [hov] using v.isLt)
          rw [Circuit.eval]
          rw [hw]
          rw [hov]
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem (by simpa using v.isLt)]
          simp
        · right
          intro x y hxa hxb hxy
          have hfold := fold_getD_ne C.gates v.val a.val b.val hgread hge hva' hvb'
            (List.ofFn x) (List.ofFn y) (by simp) (by simpa using v.isLt)
            (by simpa using a.isLt) (by simpa using b.isLt)
            (hne0 x y hxy)
            (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using a.isLt)]; simp [hxa])
            (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using b.isLt)]; simp [hxb])
            (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using a.isLt)]; simp [hxy a hva.symm])
            (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using b.isLt)]; simp [hxy b hvb.symm])
          rw [Circuit.eval, Circuit.eval]
          exact hfold C.output hov
      · right
        intro x y hxa hxb hxy
        have hfold := fold_getD_ne C.gates v.val a.val b.val hgread hge hva' hvb'
          (List.ofFn x) (List.ofFn y) (by simp) (by simpa using v.isLt)
          (by simpa using a.isLt) (by simpa using b.isLt)
          (hne0 x y hxy)
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using a.isLt)]; simp [hxa])
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using b.isLt)]; simp [hxb])
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using a.isLt)]; simp [hxy a hva.symm])
          (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using b.isLt)]; simp [hxy b hvb.symm])
        rw [Circuit.eval, Circuit.eval]
        exact hfold C.output (by omega)

  classical
  intro G C least top junk size deficit raw
  have reader (i : Fin 11) (j : ℕ) : j ∈ readers 0 C i.val ↔
      j < C.size ∧ i.val ∈ (gateAt C j).inputs := by
    change j ∈ (Finset.range C.gates.length).filter (fun k => 0 + i.val ∈ (gateAt C k).inputs) ↔ j < C.gates.length ∧ _
    rw [Finset.mem_filter,Finset.mem_range,Nat.zero_add]
  apply residual C least top junk size deficit
  · intro v hv
    by_contra h
    have many : 2 < (readers 0 C v.val).card := Nat.lt_of_not_ge h
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp many
    have step (i j k : ℕ) (hi : i ∈ readers 0 C v.val) (hj : j ∈ readers 0 C v.val) (hk : k ∈ readers 0 C v.val) (ij : i < j) (jk : j < k) : False := by
      exact (raw v hv).2 i j k ij jk ((reader _ _).mp hk).1 ((reader _ _).mp hi).2
        ((reader _ _).mp hj).2 ((reader _ _).mp hk).2
    first | exact step a b c ha hb hc (by omega) (by omega) | skip
    rcases lt_or_gt_of_ne ab with h | h <;> rcases lt_or_gt_of_ne ac with h2 | h2 <;> rcases lt_or_gt_of_ne bc with h3 | h3 <;> first | omega | exact step a b c ha hb hc (by omega) (by omega) | exact step a c b ha hc hb (by omega) (by omega) | exact step b a c hb ha hc (by omega) (by omega) | exact step b c a hb hc ha (by omega) (by omega) | exact step c a b hc ha hb (by omega) (by omega) | exact step c b a hc hb ha (by omega) (by omega)
  · intro v a b hv ab va vb nab sharing
    by_contra absent
    have cert : ∀ v a b : Fin 11, v.val < 4 → a ≤ b → v ≠ a → v ≠ b →
        ¬ G.Adj a b → 121*v.val+11*a.val+b.val ∉ ([29, 30, 49, 51, 61, 74, 186, 230, 250, 295, 316, 317, 472] : List ℕ) →
        ∃ z : Fin 11, G.Adj v z ∧ ¬ G.Adj a z ∧ ¬ G.Adj b z := by
      change ∀ v a b : Fin 11, v.val < 4 → a ≤ b → v ≠ a → v ≠ b →
        ¬ (edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun t => (t / 11, t % 11))).Adj a b → 121*v.val+11*a.val+b.val ∉ ([29, 30, 49, 51, 61, 74, 186, 230, 250, 295, 316, 317, 472] : List ℕ) →
        ∃ z : Fin 11, (edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun t => (t / 11, t % 11))).Adj v z ∧ ¬ (edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun t => (t / 11, t % 11))).Adj a z ∧ ¬ (edgeGraph 11 (([9, 10, 15, 19, 27, 32, 39, 40, 52, 54, 63, 64, 73, 76, 86, 97] : List ℕ).map fun t => (t / 11, t % 11))).Adj b z
      decide +kernel
    obtain ⟨z,vz,az,bz⟩ := cert v a b hv ab va vb nab absent
    have guard := shield 11 C v a b least.1 va vb (by
      intro j hj hit
      have mem := Finset.mem_union.mp (sharing ((reader v j).mpr ⟨hj,hit⟩))
      exact ⟨(raw v hv).1 j hj hit, mem.imp (fun t => ((reader _ _).mp t).2) (fun t => ((reader _ _).mp t).2)⟩)
    let x := fun k : Fin 11 => decide (k = a ∨ k = b ∨ k = z)
    let y := fun k : Fin 11 => decide (k = v) || x k
    have spec (u : Fin 11 → Bool) : C.eval (List.ofFn u) = true ↔
      ∃ r s, G.Adj r s ∧ u r = true ∧ u s = true := by
      change PEqualNP.MetaComplexity.circuitFun 11 C u = true ↔ _
      rw [congrFun least.2.1 u]
      change (decide (∃ a ∈ (∅ : Finset (Fin 11)), u a = true) || decide (∃ r s, G.Adj r s ∧ u r = true ∧ u s = true)) = true ↔ _
      simp only [Finset.notMem_empty, false_and, exists_false, decide_false,
        Bool.false_or, decide_eq_true_iff]
    have neg : C.eval (List.ofFn x) ≠ true := by
      intro h
      obtain ⟨r,s,rs,hr,hs⟩ := (spec x).mp h
      rcases of_decide_eq_true hr with rfl|rfl|rfl <;> rcases of_decide_eq_true hs with rfl|rfl|rfl <;>
        first | exact rs.ne rfl | exact nab rs | exact nab rs.symm | exact az rs | exact az rs.symm | exact bz rs | exact bz rs.symm
    have pos : C.eval (List.ofFn y) = true := (spec y).mpr ⟨v,z,vz,by simp only [y,decide_true,Bool.true_or],
      Bool.or_eq_true_iff.mpr (Or.inr (decide_eq_true (Or.inr (Or.inr rfl))))⟩
    rcases guard with out | same
    · let zero := fun k : Fin 11 => decide (k = v)
      have hvwire : C.eval (List.ofFn zero) = true := by
        exact (out zero).trans (decide_eq_true rfl)
      obtain ⟨r,s,rs,hr,hs⟩ := (spec zero).mp hvwire
      exact rs.ne ((of_decide_eq_true hr).trans (of_decide_eq_true hs).symm)
    · exact neg ((same x y (decide_eq_true (Or.inl rfl)) (decide_eq_true (Or.inr (Or.inl rfl)))
        (fun k ne => by simp only [y,decide_eq_false ne,Bool.false_or])).trans pos)
