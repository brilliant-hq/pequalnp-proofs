import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18961_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

private lemma pg_adj_iff (u v : Fin 26) :
    (SimpleGraph.fromRel (fun u v : Fin 26 =>
      u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))).Adj u v ↔
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
      (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) := by
  rw [SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    intro heq; subst heq
    rcases h with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> omega

private lemma pg_noFourCycle (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hAdj : ∀ u v : Fin 26, G.Adj u v ↔
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
      (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) :
    NoFourCycle G := by
  intro a b hab
  by_contra hgt
  rcases Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.filter fun w : Fin 26 => G.Adj a w ∧ G.Adj b w).card) with
    ⟨w1, hw1, w2, hw2, hw12⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
  have ha1 := (hAdj a w1).mp hw1.1
  have hb1 := (hAdj b w1).mp hw1.2
  have ha2 := (hAdj a w2).mp hw2.1
  have hb2 := (hAdj b w2).mp hw2.2
  have hsidon : ∀ (x y z1 z2 : Fin 13), x ≠ y → z1 ≠ z2 →
      (x.val + z1.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
      (y.val + z1.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
      (x.val + z2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
      (y.val + z2.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) → False := by
    intro x y z1 z2 hxy hz12 h1 h2 h3 h4
    have hdiff : ∀ d1 d2 d3 d4 : Fin 13,
        d1.val ∈ ([0, 1, 3, 9] : List ℕ) → d2.val ∈ ([0, 1, 3, 9] : List ℕ) →
        d3.val ∈ ([0, 1, 3, 9] : List ℕ) → d4.val ∈ ([0, 1, 3, 9] : List ℕ) →
        d1 ≠ d2 → d1 - d2 = d3 - d4 → d1 = d3 ∧ d2 = d4 := by decide
    have hx : x + z1 ≠ y + z1 := fun h => hxy (add_right_cancel h)
    have hm : ∀ (u v : Fin 13), (u + v).val = (u.val + v.val) % 13 := fun _ _ => rfl
    have heq : (x + z1) - (y + z1) = (x + z2) - (y + z2) := by
      rw [add_sub_add_right_eq_sub, add_sub_add_right_eq_sub]
    have ⟨hc, _⟩ := hdiff (x + z1) (y + z1) (x + z2) (y + z2)
      (by rw [hm]; exact h1) (by rw [hm]; exact h2)
      (by rw [hm]; exact h3) (by rw [hm]; exact h4) hx heq
    exact hz12 (add_left_cancel hc)
  rcases ha1 with ha1 | ha1 <;> rcases hb1 with hb1 | hb1 <;>
    rcases ha2 with ha2 | ha2 <;> rcases hb2 with hb2 | hb2
  all_goals try omega
  · refine hsidon ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ ⟨w1.val - 13, by omega⟩ ⟨w2.val - 13, by omega⟩
      (fun h => hab (Fin.ext (congrArg (Fin.val : Fin 13 → ℕ) h)))
      (fun h => hw12 (Fin.ext (by have := congrArg (Fin.val : Fin 13 → ℕ) h; dsimp only at this; omega)))
      ?_ ?_ ?_ ?_
    · have : (a.val + (w1.val - 13)) % 13 = (a.val + w1.val) % 13 := by omega
      rw [this]; exact ha1.2.2
    · have : (b.val + (w1.val - 13)) % 13 = (b.val + w1.val) % 13 := by omega
      rw [this]; exact hb1.2.2
    · have : (a.val + (w2.val - 13)) % 13 = (a.val + w2.val) % 13 := by omega
      rw [this]; exact ha2.2.2
    · have : (b.val + (w2.val - 13)) % 13 = (b.val + w2.val) % 13 := by omega
      rw [this]; exact hb2.2.2
  · refine hsidon ⟨a.val - 13, by omega⟩ ⟨b.val - 13, by omega⟩ ⟨w1.val, by omega⟩ ⟨w2.val, by omega⟩
      (fun h => hab (Fin.ext (by have := congrArg (Fin.val : Fin 13 → ℕ) h; dsimp only at this; omega)))
      (fun h => hw12 (Fin.ext (congrArg (Fin.val : Fin 13 → ℕ) h)))
      ?_ ?_ ?_ ?_
    · have : (a.val - 13 + w1.val) % 13 = (w1.val + a.val) % 13 := by omega
      rw [this]; exact ha1.2.2
    · have : (b.val - 13 + w1.val) % 13 = (w1.val + b.val) % 13 := by omega
      rw [this]; exact hb1.2.2
    · have : (a.val - 13 + w2.val) % 13 = (w2.val + a.val) % 13 := by omega
      rw [this]; exact ha2.2.2
    · have : (b.val - 13 + w2.val) % 13 = (w2.val + b.val) % 13 := by omega
      rw [this]; exact hb2.2.2

private lemma foldl_append_len {α β : Type*} (f : List α → β → α) (gs : List β) (acc : List α) :
    (gs.foldl (fun l g => l ++ [f l g]) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp; omega

private lemma foldl_append_getD_lt {α β : Type*} (f : List α → β → α) (gs : List β) (acc : List α)
    (j : ℕ) (d : α) (hj : j < acc.length) :
    (gs.foldl (fun l g => l ++ [f l g]) acc).getD j d = acc.getD j d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (acc ++ [f acc g]) (by simp; omega)]
    rw [List.getD_append _ _ _ _ hj]

private lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool)
    (k : ℕ) (hk : k < C.gates.length) :
    (C.wires (List.ofFn x)).getD (n + k) false =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  unfold Circuit.wires
  have hga : gateAt C k = C.gates[k] := by
    unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
  rw [hga]
  have hsplit : C.gates = C.gates.take k ++ (C.gates[k] :: C.gates.drop (k + 1)) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [← h2, h1]
  set f : List Bool → Gate → Bool := fun w g => g.op.eval (g.inputs.map fun i => w.getD i false)
  set pre := (C.gates.take k).foldl (fun l g => l ++ [f l g]) (List.ofFn x)
  have hpre_len : pre.length = n + k := by
    simp only [pre, foldl_append_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)]
  have hfull : C.gates.foldl (fun l g => l ++ [f l g]) (List.ofFn x) =
      (C.gates.drop (k + 1)).foldl (fun l g => l ++ [f l g]) (pre ++ [f pre C.gates[k]]) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_pre : ∀ i < n + k, (C.gates.foldl (fun l g => l ++ [f l g]) (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [hfull, foldl_append_getD_lt f _ _ _ _ (by simp [hpre_len]; omega)]
    rw [List.getD_append _ _ _ _ (by omega)]
  have hval : (C.gates.foldl (fun l g => l ++ [f l g]) (List.ofFn x)).getD (n + k) false = f pre C.gates[k] := by
    rw [hfull, foldl_append_getD_lt f _ _ _ _ (by simp [hpre_len])]
    rw [← hpre_len, List.getD_append_right _ _ _ _ le_rfl]
    simp
  change (C.gates.foldl (fun l g => l ++ [f l g]) (List.ofFn x)).getD (n + k) false = _
  rw [hval]
  dsimp only [f]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hreads : i < n + k := by
    have hrb := hRB k hk i
    rw [hga] at hrb
    exact hrb hi
  exact (hlt_pre i hreads).symm

private lemma orSets_true (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool) :
    ∀ k ≤ C.gates.length,
      let cs := (C.gates.take k).foldl (orStep n) []
      cs.length = k ∧
      ∀ j < k, ∀ g ∈ cs.getD j [],
        (C.wires (List.ofFn x)).getD (n + g) false = true →
        (C.wires (List.ofFn x)).getD (n + j) false = true := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨rfl, fun j hj => by omega⟩
  | succ k ih =>
    intro hk1
    have hk : k < C.gates.length := by omega
    obtain ⟨hlen, hprop⟩ := ih (Nat.le_of_lt hk)
    set cs := (C.gates.take k).foldl (orStep n) []
    have htake : C.gates.take (k + 1) = C.gates.take k ++ [C.gates[k]] := List.take_succ_eq_append_getElem hk
    have hcs1 : (C.gates.take (k + 1)).foldl (orStep n) [] = orStep n cs C.gates[k] := by
      rw [htake, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hcs1]
    refine ⟨by simp [orStep, hlen], ?_⟩
    intro j hj g hg hgt
    by_cases hjk : j < k
    · rw [orStep, List.getD_append _ _ _ _ (by omega)] at hg
      exact hprop j hjk g hg hgt
    · have hjeq : j = k := by omega
      subst hjeq
      rw [orStep] at hg
      rw [List.getD_append_right _ _ _ _ (by omega)] at hg
      simp only [hlen, Nat.sub_self, List.getD_cons_zero, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact hgt
      · split_ifs at hg with hop
        · rw [List.mem_flatMap] at hg
          rcases hg with ⟨w, hw, hgw⟩
          rw [List.mem_filter] at hw
          have hwb : n ≤ w ∧ w < n + j := by simpa using hw.2
          have hwt : (C.wires (List.ofFn x)).getD (n + (w - n)) false = true :=
            hprop (w - n) (by omega) g hgw hgt
          have hwn : n + (w - n) = w := by omega
          rw [hwn] at hwt
          rw [wires_getD_gate n C hRB x j hk]
          have hga : gateAt C j = C.gates[j] := by
            unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
          rw [hga, hop]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
          exact ⟨true, ⟨w, hw.1, hwt⟩, rfl⟩
        · simp at hg

private lemma orIn_true (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (x : Fin n → Bool)
    (w : ℕ) (i : Fin n) (hi : i ∈ orIn n C w) (hxi : x i = true) :
    (C.wires (List.ofFn x)).getD w false = true := by
  have hwin : (C.wires (List.ofFn x)).getD i.val false = true := by
    unfold Circuit.wires
    set f : List Bool → Gate → Bool := fun l g => g.op.eval (g.inputs.map fun u => l.getD u false)
    change (C.gates.foldl (fun l g => l ++ [f l g]) (List.ofFn x)).getD i.val false = true
    rw [foldl_append_getD_lt f _ _ _ _ (by simp [i.isLt])]
    simpa [List.getD_eq_getElem?_getD, i.isLt] using hxi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  rcases hi with rfl | ⟨k, hk, hreach, hop, hmem⟩
  · exact hwin
  · have hkt : (C.wires (List.ofFn x)).getD (n + k) false = true := by
      rw [wires_getD_gate n C hRB x k hk, hop]
      simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
      exact ⟨true, ⟨i.val, hmem, hwin⟩, rfl⟩
    obtain ⟨hnw, hkin⟩ := hreach
    obtain ⟨hlen, hprop⟩ := orSets_true n C hRB x C.gates.length le_rfl
    rw [List.take_length] at hlen hprop
    have hwlt : w - n < C.gates.length := by
      by_contra hge
      have hempty : (orSets n C).getD (w - n) [] = [] := by
        unfold orSets
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [hempty] at hkin
      simp at hkin
    have hwval := hprop (w - n) hwlt k hkin hkt
    have hwn : n + (w - n) = w := by omega
    rwa [hwn] at hwval

private lemma top_side_adj (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 26 C) (a : ℕ) (ha : a ∈ tops G C)
    (u : Fin 26) (hu : u ∈ side C a 0) (v : Fin 26) (hv : v ∈ side C a 1) :
    G.Adj u v := by
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨halt, haop, hbelow⟩ := ha
  let x : Fin 26 → Bool := fun w => decide (w = u ∨ w = v)
  have hxu : x u = true := by simp [x]
  have hxv : x v = true := by simp [x]
  have h0 : (C.wires (List.ofFn x)).getD (opnd C a 0) false = true :=
    orIn_true 26 C hAO.2.1 x (opnd C a 0) u hu hxu
  have h1 : (C.wires (List.ofFn x)).getD (opnd C a 1) false = true :=
    orIn_true 26 C hAO.2.1 x (opnd C a 1) v hv hxv
  have hga : gateAt C a = C.gates[a] := by
    unfold gateAt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem halt]; rfl
  have hlen2 : (gateAt C a).inputs.length = 2 := by
    rw [hga]; exact hAO.2.2 C.gates[a] (List.getElem_mem halt)
  rcases hgi : (gateAt C a).inputs with _ | ⟨i0, _ | ⟨i1, _ | _⟩⟩
  · simp [hgi] at hlen2
  · simp [hgi] at hlen2
  · have hi0 : opnd C a 0 = i0 := by simp [opnd, hgi]
    have hi1 : opnd C a 1 = i1 := by simp [opnd, hgi]
    have hgv : gateVal 26 C a x = true := by
      unfold gateVal
      rw [wires_getD_gate 26 C hAO.2.1 x a halt, haop, hgi]
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
      rw [← hi0, ← hi1, h0, h1]
      rfl
    have hF := hbelow x hgv
    unfold graphFun at hF
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hF
    rcases hF with ⟨_, h, _⟩ | ⟨p, q, hpq, hxp, hxq⟩
    · simp at h
    · simp only [x, decide_eq_true_eq] at hxp hxq
      rcases hxp with rfl | rfl <;> rcases hxq with rfl | rfl
      · exact False.elim (G.loopless.irrefl _ hpq)
      · exact hpq
      · exact hpq.symm
      · exact False.elim (G.loopless.irrefl _ hpq)
  · simp [hgi] at hlen2

private lemma top_has_centre (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hC4 : NoFourCycle G) (C : Circuit) (hAO : IsAO2 26 C) (a : ℕ)
    (ha : a ∈ tops G C \ centreless G C) :
    ∃ c : Fin 26, ∀ u ∈ side C a 0, ∀ v ∈ side C a 1, c = u ∨ c = v := by
  rw [Finset.mem_sdiff] at ha
  obtain ⟨hatop, hanotc⟩ := ha
  simp only [centreless, Finset.mem_filter, hatop, true_and, not_or] at hanotc
  have hne0 : (side (n := 26) C a 0).Nonempty := Finset.nonempty_iff_ne_empty.mpr hanotc.1
  have hne1 : (side (n := 26) C a 1).Nonempty := Finset.nonempty_iff_ne_empty.mpr hanotc.2
  by_cases hc0 : (side (n := 26) C a 0).card ≤ 1
  · rcases hne0 with ⟨c, hc⟩
    refine ⟨c, fun u hu _ _ => Or.inl ?_⟩
    exact Finset.card_le_one.mp hc0 c hc u hu
  · have hlt0 : 1 < (side (n := 26) C a 0).card := by omega
    rcases Finset.one_lt_card.mp hlt0 with ⟨u1, hu1, u2, hu2, hu12⟩
    have hc1 : (side (n := 26) C a 1).card ≤ 1 := by
      have hsub : side (n := 26) C a 1 ⊆ Finset.univ.filter fun w : Fin 26 => G.Adj u1 w ∧ G.Adj u2 w := by
        intro w hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, top_side_adj G C hAO a hatop u1 hu1 w hw,
          top_side_adj G C hAO a hatop u2 hu2 w hw⟩
      exact le_trans (Finset.card_le_card hsub) (hC4 u1 u2 hu12)
    rcases hne1 with ⟨c, hc⟩
    refine ⟨c, fun _ _ v hv => Or.inr ?_⟩
    exact Finset.card_le_one.mp hc1 c hc v hv

private def pgMatch (d : Fin 13) : Finset (Sym2 (Fin 26)) :=
  Finset.univ.image fun p : Fin 13 => s(Fin.castAdd 13 p, Fin.natAdd 13 (d - p))

private lemma pgMatch_pair_inj (d : Fin 13) (p1 p2 : Fin 13)
    (h : s(Fin.castAdd 13 p1, Fin.natAdd 13 (d - p1)) = s(Fin.castAdd 13 p2, Fin.natAdd 13 (d - p2))) :
    p1 = p2 := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact Fin.ext (by have := congrArg Fin.val h1; simpa using this)
  · have := congrArg Fin.val h1; simp at this; omega

private lemma pgMatch_card (d : Fin 13) : (pgMatch d).card = 13 := by
  unfold pgMatch
  rw [Finset.card_image_of_injective _ (fun p1 p2 h => pgMatch_pair_inj d p1 p2 h)]
  simp

private lemma pgMatch_sub_edges (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hAdj : ∀ u v : Fin 26, G.Adj u v ↔
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
      (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)))
    (d : Fin 13) (hd : d ∈ ({0, 1, 3, 9} : Finset (Fin 13))) :
    pgMatch d ⊆ G.edgeFinset := by
  intro e he
  rcases Finset.mem_image.mp he with ⟨p, _, rfl⟩
  rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hAdj]
  left
  refine ⟨by simp, by simp, ?_⟩
  have hsum : (p.val + (13 + (d - p).val)) % 13 = d.val := by
    have h1 : (p + (d - p)).val = d.val := by simp
    have h2 : (p + (d - p)).val = (p.val + (d - p).val) % 13 := rfl
    omega
  simp only [Fin.val_castAdd, Fin.val_natAdd, hsum]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl <;> decide

private lemma pgMatch_disjoint {d1 d2 : Fin 13} (hne : d1 ≠ d2) :
    Disjoint (pgMatch d1) (pgMatch d2) := by
  rw [Finset.disjoint_left]
  intro e he1 he2
  rcases Finset.mem_image.mp he1 with ⟨p1, _, rfl⟩
  rcases Finset.mem_image.mp he2 with ⟨p2, _, h⟩
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, _⟩
  · have hp : p1 = p2 := Fin.ext (by have := congrArg Fin.val h1; simpa using this.symm)
    have hq : d1 - p1 = d2 - p2 := Fin.ext (by have := congrArg Fin.val h2; simp at this; omega)
    subst hp
    exact hne (sub_left_inj.mp hq)
  · have := congrArg Fin.val h1; simp at this; omega

private lemma pgMatch_vertex_unique (d : Fin 13) (c : Fin 26) {e1 e2 : Sym2 (Fin 26)}
    (he1 : e1 ∈ pgMatch d) (he2 : e2 ∈ pgMatch d) (hc1 : c ∈ e1) (hc2 : c ∈ e2) :
    e1 = e2 := by
  rcases Finset.mem_image.mp he1 with ⟨p1, _, rfl⟩
  rcases Finset.mem_image.mp he2 with ⟨p2, _, rfl⟩
  rw [Sym2.mem_iff] at hc1 hc2
  rcases hc1 with rfl | rfl <;> rcases hc2 with h | h
  · have hp : p1 = p2 := Fin.ext (by have := congrArg Fin.val h; simpa using this)
    subst hp; rfl
  · have := congrArg Fin.val h; simp at this; omega
  · have := congrArg Fin.val h; simp at this; omega
  · have hq : d - p1 = d - p2 := Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
    have hp : p1 = p2 := sub_right_inj.mp hq
    subst hp; rfl

private lemma pg_edges_sub_biUnion (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hAdj : ∀ u v : Fin 26, G.Adj u v ↔
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
      (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))) :
    G.edgeFinset ⊆ ({0, 1, 3, 9} : Finset (Fin 13)).biUnion pgMatch := by
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hAdj] at he
    have hmem_pair : ∀ (a b : Fin 26), a.val < 13 → 13 ≤ b.val →
        (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ) →
        s(a, b) ∈ ({0, 1, 3, 9} : Finset (Fin 13)).biUnion pgMatch := by
      intro a b ha hb hmod
      let p : Fin 13 := ⟨a.val, ha⟩
      let q : Fin 13 := ⟨b.val - 13, by omega⟩
      let d : Fin 13 := p + q
      have hd_val : d.val = (a.val + b.val) % 13 := by
        change (a.val + (b.val - 13)) % 13 = (a.val + b.val) % 13
        omega
      have hd_mem : d ∈ ({0, 1, 3, 9} : Finset (Fin 13)) := by
        rw [← hd_val] at hmod
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmod
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rcases hmod with h | h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
        · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))
      refine Finset.mem_biUnion.mpr ⟨d, hd_mem, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, ?_⟩⟩
      have ha_eq : Fin.castAdd 13 p = a := Fin.ext rfl
      have hb_eq : Fin.natAdd 13 (d - p) = b := by
        apply Fin.ext
        have hdp : d - p = q := add_sub_cancel_left p q
        rw [hdp]
        simp [q]; omega
      rw [ha_eq, hb_eq]
    rcases he with ⟨ha, hb, hm⟩ | ⟨ha, hb, hm⟩
    · exact hmem_pair u v ha hb hm
    · rw [Sym2.eq_swap]; exact hmem_pair v u ha hb hm

private lemma profiles_general (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj]
    (hAdj : ∀ u v : Fin 26, G.Adj u v ↔
      (u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)) ∨
      (v.val < 13 ∧ 13 ≤ u.val ∧ (v.val + u.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)))
    (C : Circuit) (hLeast : IsLeastAO G C) :
    (∀ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)),
      13 ≤ (tops G C \ centreless G C).card + (Ustar G C ∩ pgMatch d).card) ∧
    ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)),
      4 * (Ustar G C ∩ pgMatch d).card ≤ (Ustar G C).card := by
  classical
  have hC4 : NoFourCycle G := pg_noFourCycle G hAdj
  let shifts : Finset (Fin 13) := {0, 1, 3, 9}
  constructor
  · intro d hd
    let S := pgMatch d ∩ starEdges G C
    have hsplit : pgMatch d ⊆ (Ustar G C ∩ pgMatch d) ∪ S := by
      intro e he
      rw [Finset.mem_union]
      by_cases hs : e ∈ starEdges G C
      · exact Or.inr (Finset.mem_inter.mpr ⟨he, hs⟩)
      · exact Or.inl (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨pgMatch_sub_edges G hAdj d hd he, hs⟩, he⟩)
    have h13 : 13 ≤ (Ustar G C ∩ pgMatch d).card + S.card := by
      calc 13 = (pgMatch d).card := (pgMatch_card d).symm
        _ ≤ ((Ustar G C ∩ pgMatch d) ∪ S).card := Finset.card_le_card hsplit
        _ ≤ (Ustar G C ∩ pgMatch d).card + S.card := Finset.card_union_le _ _
    have hS_le : S.card ≤ (tops G C \ centreless G C).card := by
      have hex : ∀ e ∈ S, ∃ a ∈ tops G C \ centreless G C,
          ∃ u ∈ side (n := 26) C a 0, ∃ v ∈ side (n := 26) C a 1, e = s(u, v) := by
        intro e he
        have hs : e ∈ starEdges G C := (Finset.mem_inter.mp he).2
        simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hs
        rcases hs with ⟨a, hatop, ⟨u, v⟩, ⟨hu, hv⟩, rfl⟩
        have hanotc : a ∉ centreless G C := by
          simp only [centreless, Finset.mem_filter, hatop, true_and, not_or]
          exact ⟨Finset.nonempty_iff_ne_empty.mp ⟨u, hu⟩, Finset.nonempty_iff_ne_empty.mp ⟨v, hv⟩⟩
        exact ⟨a, Finset.mem_sdiff.mpr ⟨hatop, hanotc⟩, u, hu, v, hv, rfl⟩
      let f : Sym2 (Fin 26) → ℕ := fun e =>
        if h : e ∈ S then (hex e h).choose else 0
      refine Finset.card_le_card_of_injOn f ?_ ?_
      · intro e he
        have heS : e ∈ S := he
        simp only [Finset.mem_coe, f, heS, dite_true]
        exact (hex e heS).choose_spec.1
      · intro e1 he1 e2 he2 hfeq
        have he1S : e1 ∈ S := he1
        have he2S : e2 ∈ S := he2
        simp only [f, he1S, he2S, dite_true] at hfeq
        set a := (hex e1 he1S).choose
        have ha : a ∈ tops G C \ centreless G C := (hex e1 he1S).choose_spec.1
        obtain ⟨u1, hu1, v1, hv1, he1eq⟩ := (hex e1 he1S).choose_spec.2
        obtain ⟨u2, hu2, v2, hv2, he2eq⟩ := hfeq ▸ (hex e2 he2S).choose_spec.2
        obtain ⟨c, hc⟩ := top_has_centre G hC4 C hLeast.1 a ha
        have hc1 : c ∈ e1 := by
          rw [he1eq, Sym2.mem_iff]
          exact hc u1 hu1 v1 hv1
        have hc2 : c ∈ e2 := by
          rw [he2eq, Sym2.mem_iff]
          exact hc u2 hu2 v2 hv2
        exact pgMatch_vertex_unique d c (Finset.mem_inter.mp he1S).1 (Finset.mem_inter.mp he2S).1 hc1 hc2
    omega
  · have hpart : Ustar G C = shifts.biUnion fun d => Ustar G C ∩ pgMatch d := by
      ext e
      simp only [Finset.mem_biUnion, Finset.mem_inter]
      constructor
      · intro he
        have hedge : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp he).1
        rcases Finset.mem_biUnion.mp (pg_edges_sub_biUnion G hAdj hedge) with ⟨d, hd, hmd⟩
        exact ⟨d, hd, he, hmd⟩
      · rintro ⟨_, _, he, _⟩
        exact he
    have hsum : ∑ d ∈ shifts, (Ustar G C ∩ pgMatch d).card = (Ustar G C).card := by
      rw [← Finset.card_biUnion]
      · rw [← hpart]
      · intro d1 _ d2 _ hne
        exact (pgMatch_disjoint hne).mono Finset.inter_subset_right Finset.inter_subset_right
    have hsum4 : (Ustar G C ∩ pgMatch 0).card + (Ustar G C ∩ pgMatch 1).card +
        (Ustar G C ∩ pgMatch 3).card + (Ustar G C ∩ pgMatch 9).card = (Ustar G C).card := by
      have h0 : (0 : Fin 13) ∉ ({1, 3, 9} : Finset (Fin 13)) := by decide
      have h1 : (1 : Fin 13) ∉ ({3, 9} : Finset (Fin 13)) := by decide
      have h3 : (3 : Fin 13) ∉ ({9} : Finset (Fin 13)) := by decide
      simp only [shifts, Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_insert h3,
        Finset.sum_singleton] at hsum
      omega
    by_contra hnone
    push Not at hnone
    have c0 := hnone 0 (by decide)
    have c1 := hnone 1 (by decide)
    have c3 := hnone 3 (by decide)
    have c9 := hnone 9 (by decide)
    omega

theorem profiles_main :
    let G := SimpleGraph.fromRel (fun u v : Fin 26 =>
      u.val < 13 ∧ 13 ≤ v.val ∧ (u.val + v.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ))
    ∀ C : Circuit, IsLeastAO G C → TopForm G C →
    let U := Ustar G C
    let A := (tops G C \ centreless G C).card
    let shifts : Finset (Fin 13) := {0, 1, 3, 9}
    let loss (d : Fin 13) := (U ∩ (Finset.univ.image fun p : Fin 13 =>
      s(Fin.castAdd 13 p, Fin.natAdd 13 (d - p)))).card
    (∀ d ∈ shifts, 13 ≤ A + loss d) ∧ ∃ d ∈ shifts, 4 * loss d ≤ U.card := by
  dsimp only
  intro C hLeast _
  exact profiles_general _ pg_adj_iff C hLeast

end PEqualNP.Outside.L_meta_18961_aux

theorem PEqualNP.Outside.L_meta_18961 : let x1 : SimpleGraph (Fin (26 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (26 : ℕ)) => ↑x1 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x6 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card;       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → ℕ := fun (x8 : Fin (13 : ℕ)) => (x5 ∩ Finset.image (fun (x9 : Fin (13 : ℕ)) => s(Fin.castAdd (13 : ℕ) x9, Fin.natAdd (13 : ℕ) (x8 - x9))) Finset.univ).card;       (∀ x9 ∈ x7, (13 : ℕ) ≤ x6 + x8 x9) ∧ ∃ x9 ∈ x7, (4 : ℕ) * x8 x9 ≤ x5.card := by
  exact PEqualNP.Outside.L_meta_18961_aux.profiles_main
