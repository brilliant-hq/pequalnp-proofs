import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18961

-- The vertex-cover argument is adapted from the published proof of L-meta-18800.
namespace StarCover
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_len_w (gs : List Gate) (w : List Bool) :
    (gs.foldl wstep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, wstep, List.length_append, List.length_cons, List.length_nil]; omega

theorem foldl_len_or (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons, List.length_nil]; omega

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

theorem foldl_w_gate_mono_or (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length)
    (hor : (gs[j]).op = GateOp.or) (u : ℕ) (hu : u ∈ (gs[j]).inputs)
    (hval : ((gs.take j).foldl wstep w).getD u false = true) :
    (gs.foldl wstep w).getD (w.length + j) false = true := by
  rw [foldl_w_gate gs w j hj, hor]
  simp only [GateOp.eval, List.any_eq_true, List.mem_map]
  exact ⟨true, ⟨u, hu, hval⟩, rfl⟩

theorem foldl_orSets_mono (n : ℕ) (gs : List Gate) (x : Fin n → Bool) :
    ∀ j < gs.length, ∀ k ∈ (gs.foldl (orStep n) []).getD j [],
      (gs.foldl wstep (List.ofFn x)).getD (n + k) false = true →
      (gs.foldl wstep (List.ofFn x)).getD (n + j) false = true := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj k hk htk
    have hlen_or : (gs.foldl (orStep n) []).length = gs.length := by
      rw [foldl_len_or]; simp
    have hlen_w : (gs.foldl wstep (List.ofFn x)).length = n + gs.length := by
      rw [foldl_len_w, List.length_ofFn]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hk htk ⊢
    by_cases hlt : j < gs.length
    · rw [orStep, getD_append_lt [] _ _ j (by omega)] at hk
      have hk_lt : k < gs.length := by
        have hmem : ∀ (gs' : List Gate) (j' : ℕ), j' < gs'.length →
            ∀ k' ∈ (gs'.foldl (orStep n) []).getD j' [], k' < gs'.length := by
          intro gs'
          induction gs' using List.reverseRecOn with
          | nil => intro _ hj'; simp at hj'
          | append_singleton gs' g' ih' =>
            intro j' hj' k' hk'
            have hl' : (gs'.foldl (orStep n) []).length = gs'.length := by rw [foldl_len_or]; simp
            rw [List.foldl_append, List.foldl_cons, List.foldl_nil, orStep] at hk'
            by_cases hlt' : j' < gs'.length
            · rw [getD_append_lt [] _ _ j' (by omega)] at hk'
              have := ih' j' hlt' k' hk'
              simp; omega
            · have heq' : j' = gs'.length := by simp at hj'; omega
              subst heq'
              rw [← hl', getD_snoc] at hk'
              simp only [List.mem_cons] at hk'
              rcases hk' with rfl | hk'
              · rw [hl']; simp
              · split at hk'
                · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk'
                  rcases hk' with ⟨w, ⟨_, hw1, hw2⟩, hk''⟩
                  have := ih' (w - n) (by omega) k' hk''
                  simp; omega
                · simp at hk'
        exact hmem gs j hlt k hk
      rw [wstep, getD_append_lt false _ _ _ (by omega)] at htk
      rw [wstep, getD_append_lt false _ _ _ (by omega)]
      exact ih j hlt k hk htk
    · have heq : j = gs.length := by simp at hj; omega
      subst heq
      rw [orStep, ← hlen_or, getD_snoc] at hk
      simp only [List.mem_cons] at hk
      rcases hk with rfl | hk
      · rw [hlen_or] at htk; exact htk
      · split at hk
        · rename_i hor
          simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk
          rcases hk with ⟨w, ⟨hw_in, hw1, hw2⟩, hk'⟩
          rw [hlen_or] at hw2
          have hwn : w - n < gs.length := by omega
          have hkw : (gs.foldl wstep (List.ofFn x)).getD (n + k) false = true := by
            have hk_lt : k < gs.length := by
              have hmem : ∀ (gs' : List Gate) (j' : ℕ), j' < gs'.length →
                  ∀ k' ∈ (gs'.foldl (orStep n) []).getD j' [], k' < gs'.length := by
                intro gs'
                induction gs' using List.reverseRecOn with
                | nil => intro _ hj'; simp at hj'
                | append_singleton gs' g' ih' =>
                  intro j' hj' k' hk'
                  have hl' : (gs'.foldl (orStep n) []).length = gs'.length := by rw [foldl_len_or]; simp
                  rw [List.foldl_append, List.foldl_cons, List.foldl_nil, orStep] at hk'
                  by_cases hlt' : j' < gs'.length
                  · rw [getD_append_lt [] _ _ j' (by omega)] at hk'
                    have := ih' j' hlt' k' hk'; simp; omega
                  · have heq' : j' = gs'.length := by simp at hj'; omega
                    subst heq'
                    rw [← hl', getD_snoc] at hk'
                    simp only [List.mem_cons] at hk'
                    rcases hk' with rfl | hk'
                    · rw [hl']; simp
                    · split at hk'
                      · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq] at hk'
                        rcases hk' with ⟨w', ⟨_, hw1', hw2'⟩, hk''⟩
                        have := ih' (w' - n) (by omega) k' hk''; simp; omega
                      · simp at hk'
              exact hmem gs (w - n) hwn k hk'
            rw [wstep, getD_append_lt false _ _ _ (by omega)] at htk
            exact htk
          have hw_true : (gs.foldl wstep (List.ofFn x)).getD w false = true := by
            have := ih (w - n) hwn k hk' hkw
            rwa [show n + (w - n) = w by omega] at this
          rw [wstep, ← hlen_w, getD_snoc, hor]
          simp only [GateOp.eval, List.any_eq_true, List.mem_map]
          exact ⟨true, ⟨w, hw_in, hw_true⟩, rfl⟩
        · simp at hk

theorem orIn_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (u : Fin n)
    (hu : u ∈ orIn n C w) (hx : x u = true) :
    (C.wires (List.ofFn x)).getD w false = true := by
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with heq | ⟨k, hk, hreach, hor, hin⟩
  · subst heq
    change (C.gates.foldl wstep (List.ofFn x)).getD u.val false = true
    rw [foldl_w_prefix C.gates (List.ofFn x) u.val (by simp),
        List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    exact hx
  · rcases hreach with ⟨hnw, hmem⟩
    have hwn_lt : w - n < C.gates.length := by
      by_contra h
      have hlen : (orSets n C).length = C.gates.length := by
        unfold orSets; rw [foldl_len_or]; simp
      rw [List.getD_eq_default _ _ (by omega)] at hmem
      simp at hmem
    have hgk : (C.gates[k]).op = GateOp.or := by
      simpa only [gateAt, List.getD_eq_getElem _ _ hk] using hor
    have hgin : u.val ∈ (C.gates[k]).inputs := by
      simpa only [gateAt, List.getD_eq_getElem _ _ hk] using hin
    have hku : ((C.gates.take k).foldl wstep (List.ofFn x)).getD u.val false = true := by
      rw [foldl_w_prefix _ _ u.val (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      exact hx
    have hk_true : (C.gates.foldl wstep (List.ofFn x)).getD (n + k) false = true := by
      have := foldl_w_gate_mono_or C.gates (List.ofFn x) k hk hgk u.val hgin hku
      rwa [List.length_ofFn] at this
    have hw_true := foldl_orSets_mono n C.gates x (w - n) hwn_lt k hmem hk_true
    rwa [show n + (w - n) = w by omega] at hw_true

theorem top_cross_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hao : IsAO2 n C) (a : ℕ) (ha : a ∈ tops G C) (u v : Fin n)
    (hu : u ∈ side C a 0) (hv : v ∈ side C a 1) : G.Adj u v := by
  simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ha
  rcases ha with ⟨ha_lt, ha_and, ha_below⟩
  have hga : gateAt C a = C.gates[a] := List.getD_eq_getElem _ _ ha_lt
  have hlen2 : (C.gates[a]).inputs.length = 2 := hao.2.2 _ (List.getElem_mem ha_lt)
  obtain ⟨w0, w1, hw⟩ : ∃ w0 w1, (C.gates[a]).inputs = [w0, w1] := by
    match h : (C.gates[a]).inputs with
    | [w0, w1] => exact ⟨w0, w1, rfl⟩
    | [] | [_] | _ :: _ :: _ :: _ => simp [h] at hlen2
  have hop0 : opnd C a 0 = w0 := by
    simp only [opnd, hga, hw]; rfl
  have hop1 : opnd C a 1 = w1 := by
    simp only [opnd, hga, hw]; rfl
  have hw0_lt : w0 < n + a := hao.2.1 a ha_lt w0 (by rw [hga, hw]; simp)
  have hw1_lt : w1 < n + a := hao.2.1 a ha_lt w1 (by rw [hga, hw]; simp)
  let x : Fin n → Bool := pairInput u v
  have hxu : x u = true := by simp [x, pairInput]
  have hxv : x v = true := by simp [x, pairInput]
  have h0_full : (C.wires (List.ofFn x)).getD w0 false = true :=
    orIn_true C x w0 u (hop0 ▸ hu) hxu
  have h1_full : (C.wires (List.ofFn x)).getD w1 false = true :=
    orIn_true C x w1 v (hop1 ▸ hv) hxv
  have hpref_take : ∀ i < n + a,
      ((C.gates.take a).foldl wstep (List.ofFn x)).getD i false =
      (C.wires (List.ofFn x)).getD i false := by
    intro i hi
    have hsplit : C.gates = C.gates.take a ++ C.gates.drop a := (List.take_append_drop a C.gates).symm
    have hlen_t : ((C.gates.take a).foldl wstep (List.ofFn x)).length = n + a := by
      rw [foldl_len_w, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt ha_lt)]
    change _ = (C.gates.foldl wstep (List.ofFn x)).getD i false
    conv_rhs => rw [hsplit, List.foldl_append]
    exact (foldl_w_prefix (C.gates.drop a) _ i (by omega)).symm
  have hgate_true : gateVal n C a x = true := by
    change (C.gates.foldl wstep (List.ofFn x)).getD (n + a) false = true
    have := foldl_w_gate C.gates (List.ofFn x) a ha_lt
    rw [List.length_ofFn] at this
    rw [this, show (C.gates[a]).op = GateOp.and from hga ▸ ha_and, hw]
    simp only [GateOp.eval, List.map, List.all_cons, List.all_nil, Bool.and_true]
    rw [hpref_take w0 hw0_lt, hpref_take w1 hw1_lt, h0_full, h1_full]
    rfl
  have hgf := ha_below x hgate_true
  simp [graphFun] at hgf
  rcases hgf with ⟨p, q, hpq, hp, hq⟩
  simp only [x, pairInput, decide_eq_true_eq] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl (G.ne_of_adj hpq)
  · exact hpq
  · exact hpq.symm
  · exact absurd rfl (G.ne_of_adj hpq)

theorem main_proof :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit), NoFourCycle G → IsLeastAO G C → TopForm G C →
      ∃ S : Finset (Fin n),
        (∀ u v, G.Adj u v → s(u, v) ∉ Ustar G C → u ∈ S ∨ v ∈ S) ∧
        S.card ≤ (tops G C \ centreless G C).card := by
  classical
  intro n G _ C hno4 hleast _
  have hao : IsAO2 n C := hleast.1
  have hcard1 : ∀ a ∈ tops G C \ centreless G C,
      (side (n := n) C a 0).card = 1 ∨ (side (n := n) C a 1).card = 1 := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    rcases ha with ⟨ha_top, ha_nc⟩
    simp only [centreless, Finset.mem_filter, not_and, not_or] at ha_nc
    rcases ha_nc ha_top with ⟨h0ne, h1ne⟩
    have h0pos : 0 < (side (n := n) C a 0).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0ne)
    have h1pos : 0 < (side (n := n) C a 1).card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h1ne)
    by_contra hboth
    push Not at hboth
    have h0ge2 : 1 < (side (n := n) C a 0).card := by omega
    have h1ge2 : 1 < (side (n := n) C a 1).card := by omega
    rcases Finset.one_lt_card.mp h0ge2 with ⟨u1, hu1, u2, hu2, hune⟩
    rcases Finset.one_lt_card.mp h1ge2 with ⟨v1, hv1, v2, hv2, hvne⟩
    have hsub : {v1, v2} ⊆ Finset.univ.filter fun w => G.Adj u1 w ∧ G.Adj u2 w := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hw with rfl | rfl
      · exact ⟨top_cross_adj G C hao a ha_top u1 w hu1 hv1,
               top_cross_adj G C hao a ha_top u2 w hu2 hv1⟩
      · exact ⟨top_cross_adj G C hao a ha_top u1 w hu1 hv2,
               top_cross_adj G C hao a ha_top u2 w hu2 hv2⟩
    have h2 : 2 ≤ (Finset.univ.filter fun w => G.Adj u1 w ∧ G.Adj u2 w).card := by
      calc 2 = ({v1, v2} : Finset (Fin n)).card := (Finset.card_pair hvne).symm
        _ ≤ _ := Finset.card_le_card hsub
    have h1 := hno4 u1 u2 hune
    omega
  have hex : ∀ a ∈ tops G C \ centreless G C, ∃ c : Fin n,
      (∀ u ∈ side (n := n) C a 0, u = c) ∨ (∀ v ∈ side (n := n) C a 1, v = c) := by
    intro a ha
    rcases hcard1 a ha with h0 | h1
    · rcases Finset.card_eq_one.mp h0 with ⟨c, hc⟩
      exact ⟨c, Or.inl (fun u hu => by rw [hc] at hu; exact Finset.mem_singleton.mp hu)⟩
    · rcases Finset.card_eq_one.mp h1 with ⟨c, hc⟩
      exact ⟨c, Or.inr (fun v hv => by rw [hc] at hv; exact Finset.mem_singleton.mp hv)⟩
  let S : Finset (Fin n) := (tops G C \ centreless G C).attach.image fun a => (hex a.1 a.2).choose
  refine ⟨S, ?_, ?_⟩
  · intro u v huv hnotU
    have hedge : s(u, v) ∈ G.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    have hstar : s(u, v) ∈ starEdges G C := by
      by_contra h
      exact hnotU (Finset.mem_sdiff.mpr ⟨hedge, h⟩)
    simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product] at hstar
    rcases hstar with ⟨a, ha_top, ⟨p, q⟩, ⟨hp, hq⟩, hpq⟩
    have ha_sdiff : a ∈ tops G C \ centreless G C := by
      rw [Finset.mem_sdiff]
      refine ⟨ha_top, ?_⟩
      simp only [centreless, Finset.mem_filter, not_and, not_or]
      intro _
      exact ⟨Finset.nonempty_iff_ne_empty.mp ⟨p, hp⟩, Finset.nonempty_iff_ne_empty.mp ⟨q, hq⟩⟩
    have hspec := (hex a ha_sdiff).choose_spec
    have hc_mem : (hex a ha_sdiff).choose ∈ S :=
      Finset.mem_image.mpr ⟨⟨a, ha_sdiff⟩, Finset.mem_attach _ _, rfl⟩
    rw [Sym2.eq_iff] at hpq
    rcases hspec with h0 | h1
    · have hpc : p = (hex a ha_sdiff).choose := h0 p hp
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (hpc ▸ hc_mem)
      · exact Or.inr (hpc ▸ hc_mem)
    · have hqc : q = (hex a ha_sdiff).choose := h1 q hq
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (hqc ▸ hc_mem)
      · exact Or.inl (hqc ▸ hc_mem)
  · calc S.card ≤ (tops G C \ centreless G C).attach.card := Finset.card_image_le
      _ = (tops G C \ centreless G C).card := Finset.card_attach

end StarCover

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

private def graph : SimpleGraph (Fin 26) := SimpleGraph.fromRel fun a b =>
  a.val < 13 ∧ 13 ≤ b.val ∧ (a.val + b.val) % 13 ∈ [0, 1, 3, 9]

private instance : DecidableRel graph.Adj := by
  unfold graph
  infer_instance

private def left (p : Fin 13) : Fin 26 := Fin.castAdd 13 p
private def right (p : Fin 13) : Fin 26 := Fin.natAdd 13 p
private def edge (d p : Fin 13) : Sym2 (Fin 26) := s(left p, right (d - p))
private def matching (d : Fin 13) : Finset (Sym2 (Fin 26)) := Finset.univ.image (edge d)
private def offsets : Finset (Fin 13) := {0, 1, 3, 9}
private def count (U : Finset (Sym2 (Fin 26))) (d : Fin 13) := (U ∩ matching d).card

private theorem left_inj : Function.Injective left := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 26 => x.val) h

private theorem right_inj : Function.Injective right := by
  intro a b h
  have hv := congrArg Fin.val h
  change 13 + a.val = 13 + b.val at hv
  exact Fin.ext (by omega)

private theorem sides (p q : Fin 13) : left p ≠ right q := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = 13 + q.val at hv
  omega

private theorem edge_eq {d e p q : Fin 13} (h : edge d p = edge e q) : p = q ∧ d = e := by
  change s(left p, right (d - p)) = s(left q, right (e - q)) at h
  rcases Sym2.eq_iff.mp h with ⟨hp, hd⟩ | ⟨hp, _⟩
  · have hp' := left_inj hp
    subst q
    exact ⟨rfl, sub_left_inj.mp (right_inj hd)⟩
  · exact (sides _ _ hp).elim

private theorem edge_inj (d : Fin 13) : Function.Injective (edge d) :=
  fun _ _ h => (edge_eq h).1

private theorem match_disjoint {d e : Fin 13} (hne : d ≠ e) :
    Disjoint (matching d) (matching e) := by
  apply Finset.disjoint_left.mpr
  intro a hd he
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hd
  obtain ⟨q, _, hq⟩ := Finset.mem_image.mp he
  exact hne (edge_eq (hp.trans hq.symm)).2

private theorem edge_adj {d : Fin 13} (hd : d ∈ offsets) (p : Fin 13) :
    graph.Adj (left p) (right (d - p)) := by
  have hadd : (p.val + (d - p).val) % 13 = d.val :=
    congrArg Fin.val (show p + (d - p) = d by rw [add_comm, sub_add_cancel])
  have hsum : (p.val + (13 + (d - p).val)) % 13 = d.val := by omega
  have hmem : d.val ∈ [0, 1, 3, 9] := by
    have hc : ∀ e : Fin 13, e ∈ offsets → e.val ∈ [0, 1, 3, 9] := by decide
    exact hc d hd
  change (SimpleGraph.fromRel _).Adj _ _
  rw [SimpleGraph.fromRel_adj]
  refine ⟨sides _ _, Or.inl ?_⟩
  change p.val < 13 ∧ 13 ≤ 13 + (d - p).val ∧
    (p.val + (13 + (d - p).val)) % 13 ∈ [0, 1, 3, 9]
  exact ⟨p.isLt, by omega, hsum ▸ hmem⟩

set_option maxRecDepth 12000 in
set_option maxHeartbeats 20000000 in
private theorem no_four : NoFourCycle graph := by
  unfold graph
  simp +decide

private theorem each_bound (U : Finset (Sym2 (Fin 26))) (S : Finset (Fin 26))
    (cover : ∀ u v, graph.Adj u v → s(u, v) ∉ U → u ∈ S ∨ v ∈ S)
    {d : Fin 13} (hd : d ∈ offsets) : 13 ≤ S.card + count U d := by
  let P : Finset (Fin 13) := Finset.univ.filter fun p => edge d p ∉ U
  let pick (p : Fin 13) := if left p ∈ S then left p else right (d - p)
  have hpick : Function.Injective pick := by
    intro p q h
    dsimp [pick] at h
    split at h <;> split at h
    · exact left_inj h
    · exact (sides _ _ h).elim
    · exact (sides _ _ h.symm).elim
    · exact sub_right_inj.mp (right_inj h)
  have himage : P.image pick ⊆ S := by
    intro a ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    have hcover := cover (left p) (right (d - p)) (edge_adj hd p) (Finset.mem_filter.mp hp).2
    by_cases h : left p ∈ S
    · simpa [pick, h] using h
    · simpa [pick, h] using hcover.resolve_left h
  have hP : P.image (edge d) = matching d \ U := by
    ext a
    constructor
    · intro ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩, (Finset.mem_filter.mp hp).2⟩
    · intro ha
      obtain ⟨hm, hn⟩ := Finset.mem_sdiff.mp ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hn⟩, rfl⟩
  have hm : (matching d).card = 13 := by
    simp [matching, Finset.card_image_of_injective _ (edge_inj d)]
  have hc := Finset.card_le_card himage
  rw [Finset.card_image_of_injective _ hpick, ← Finset.card_image_of_injective P (edge_inj d),
    hP] at hc
  have hparts := Finset.card_sdiff_add_card_inter (matching d) U
  rw [hm, Finset.inter_comm] at hparts
  unfold count
  omega

private theorem some_bound (U : Finset (Sym2 (Fin 26))) :
    ∃ d ∈ offsets, 4 * count U d ≤ U.card := by
  let V (d : Fin 13) := U ∩ matching d
  have disj {d e : Fin 13} (hne : d ≠ e) : Disjoint (V d) (V e) := by
    apply Finset.disjoint_left.mpr
    intro a hd he
    exact Finset.disjoint_left.mp (match_disjoint hne) (Finset.mem_inter.mp hd).2
      (Finset.mem_inter.mp he).2
  have h01 : Disjoint (V 0) (V 1) := disj (by decide)
  have h03 : Disjoint (V 0) (V 3) := disj (by decide)
  have h09 : Disjoint (V 0) (V 9) := disj (by decide)
  have h13 : Disjoint (V 1) (V 3) := disj (by decide)
  have h19 : Disjoint (V 1) (V 9) := disj (by decide)
  have h39 : Disjoint (V 3) (V 9) := disj (by decide)
  have h013 : Disjoint (V 0 ∪ V 1) (V 3) := Finset.disjoint_union_left.mpr ⟨h03, h13⟩
  have h0139 : Disjoint (V 0 ∪ V 1 ∪ V 3) (V 9) :=
    Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨h09, h19⟩, h39⟩
  have subset : V 0 ∪ V 1 ∪ V 3 ∪ V 9 ⊆ U := by
    intro a ha
    simp only [Finset.mem_union] at ha
    rcases ha with ((h | h) | h) | h <;> exact (Finset.mem_inter.mp h).1
  have hcard := Finset.card_le_card subset
  rw [Finset.card_union_of_disjoint h0139, Finset.card_union_of_disjoint h013,
    Finset.card_union_of_disjoint h01] at hcard
  change count U 0 + count U 1 + count U 3 + count U 9 ≤ U.card at hcard
  by_contra! h
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h3 := h 3 (by decide)
  have h9 := h 9 (by decide)
  omega

private theorem result (C : Circuit) (least : IsLeastAO graph C) (top : TopForm graph C) :
    (∀ d ∈ offsets, 13 ≤ (tops graph C \ centreless graph C).card + count (Ustar graph C) d) ∧
      ∃ d ∈ offsets, 4 * count (Ustar graph C) d ≤ (Ustar graph C).card := by
  obtain ⟨S, cover, hS⟩ := StarCover.main_proof 26 graph C no_four least top
  refine ⟨?_, some_bound _⟩
  intro d hd
  have h := each_bound _ S cover hd
  omega

end PEqualNP.Outside.L_meta_18961

theorem PEqualNP.Outside.L_meta_18961 : let x1 : SimpleGraph (Fin (26 : ℕ)) := SimpleGraph.fromRel fun (x1 x2 : Fin (26 : ℕ)) => ↑x1 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x2 ∧ (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]; ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsLeastAO x1 x2 →     PEqualNP.TopForm.TopForm x1 x2 →       have x5 : Finset (Sym2 (Fin (26 : ℕ))) := PEqualNP.TopForm.Ustar x1 x2;       have x6 : ℕ := (PEqualNP.TopForm.tops x1 x2 \ PEqualNP.TopForm.centreless x1 x2).card;       have x7 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))};       have x8 : Fin (13 : ℕ) → ℕ := fun (x8 : Fin (13 : ℕ)) => (x5 ∩ Finset.image (fun (x9 : Fin (13 : ℕ)) => s(Fin.castAdd (13 : ℕ) x9, Fin.natAdd (13 : ℕ) (x8 - x9))) Finset.univ).card;       (∀ x9 ∈ x7, (13 : ℕ) ≤ x6 + x8 x9) ∧ ∃ x9 ∈ x7, (4 : ℕ) * x8 x9 ≤ x5.card := by
  exact PEqualNP.Outside.L_meta_18961.result
