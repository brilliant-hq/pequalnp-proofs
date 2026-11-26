import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23964

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

theorem foldl_len (gs : List Gate) (x : List Bool) :
    (gs.foldl stp x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => simp only [List.foldl_cons, ih, stp, List.length_append, List.length_cons,
      List.length_nil]; omega

theorem foldl_prefix (gs : List Gate) (x : List Bool) : x <+: gs.foldl stp x := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih => exact (List.prefix_append x _).trans (ih _)

theorem getD_prefix {l l' : List Bool} (h : l <+: l') {i : ℕ} (hi : i < l.length) :
    l'.getD i false = l.getD i false := by
  obtain ⟨t, rfl⟩ := h
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem gate_val (gs : List Gate) (x : List Bool)
    (hrb : ∀ j (hj : j < gs.length), ∀ i ∈ (gs[j]).inputs, i < x.length + j)
    (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stp x).getD (x.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (gs.foldl stp x).getD i false) := by
  have hF : gs.foldl stp x =
      (gs.drop (j+1)).foldl stp (stp ((gs.take j).foldl stp x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop (j+1) gs]
    rw [List.foldl_append, List.take_succ_eq_append_getElem hj, List.foldl_append]
    rfl
  have hAl : ((gs.take j).foldl stp x).length = x.length + j := by
    rw [foldl_len, List.length_take]; omega
  have hpre := foldl_prefix (gs.drop (j+1)) (stp ((gs.take j).foldl stp x) gs[j])
  rw [← hF] at hpre
  have hpre2 : (gs.take j).foldl stp x <+: gs.foldl stp x :=
    (List.prefix_append _ _).trans hpre
  rw [getD_prefix hpre (by simp [stp, hAl])]
  simp only [stp]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
  simp only [hAl, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact (getD_prefix hpre2 (by rw [hAl]; exact hrb j hj i hi)).symm

def inp (N : ℕ) (S : Finset (Fin N)) : List Bool := List.ofFn fun k : Fin N => decide (k ∈ S)

def wv (F : Circuit) (N : ℕ) (S : Finset (Fin N)) (w : ℕ) : Bool := (F.wires (inp N S)).getD w false

theorem gateAt_eq (F : Circuit) {j : ℕ} (hj : j < F.gates.length) : gateAt F j = F.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem wv_input (F : Circuit) (N : ℕ) (S : Finset (Fin N)) {w : ℕ} (hw : w < N) :
    wv F N S w = decide (⟨w, hw⟩ ∈ S) := by
  unfold wv
  rw [wires_eq, getD_prefix (foldl_prefix _ _) (by simp [inp]; exact hw)]
  simp [inp, List.getD_eq_getElem?_getD, hw]

theorem wv_big (F : Circuit) (N : ℕ) (S : Finset (Fin N)) {w : ℕ} (hw : N + F.gates.length ≤ w) :
    wv F N S w = false := by
  unfold wv
  rw [wires_eq, List.getD_eq_getElem?_getD, List.getElem?_eq_none]
  · rfl
  · rw [foldl_len]; simp [inp]; omega

theorem wv_gate (F : Circuit) (N : ℕ) (hrb : ReadsBack N F) (S : Finset (Fin N)) {j : ℕ}
    (hj : j < F.gates.length) :
    wv F N S (N + j) = (gateAt F j).op.eval ((gateAt F j).inputs.map (wv F N S)) := by
  unfold wv
  rw [wires_eq, gateAt_eq F hj]
  have hl : (inp N S).length = N := by simp [inp]
  have := gate_val F.gates (inp N S) (fun j hj i hi => by
    rw [hl]; exact hrb j hj i (by rw [gateAt_eq F hj]; exact hi)) j hj
  rw [hl] at this
  exact this

def Rd (F : Circuit) (N : ℕ) (a b : ℕ) : Prop :=
  N ≤ a ∧ a - N < F.gates.length ∧ b ∈ (gateAt F (a - N)).inputs

def below (F : Circuit) (N : ℕ) : ℕ → ℕ → Prop := Relation.ReflTransGen (Rd F N)

theorem Rd_lt {F : Circuit} {N : ℕ} (hrb : ReadsBack N F) {a b : ℕ} (h : Rd F N a b) : b < a := by
  obtain ⟨h1, h2, h3⟩ := h
  have := hrb _ h2 b h3
  omega

theorem below_le {F : Circuit} {N : ℕ} (hrb : ReadsBack N F) {a b : ℕ} (h : below F N a b) :
    b ≤ a := by
  induction h with
  | refl => exact le_rfl
  | tail _ h2 ih => exact (Rd_lt hrb h2).le.trans ih

theorem count_le_reads (F : Circuit) {j : ℕ} (hj : j < F.size) (v : ℕ) :
    (gateAt F j).inputs.count v ≤ readsIn F (Finset.range F.size) v := by
  unfold readsIn
  exact Finset.single_le_sum (f := fun j => (gateAt F j).inputs.count v) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr hj)

theorem count_two_le_reads (F : Circuit) {j j' : ℕ} (hj : j < F.size) (hj' : j' < F.size)
    (hne : j ≠ j') (v : ℕ) :
    (gateAt F j).inputs.count v + (gateAt F j').inputs.count v ≤
      readsIn F (Finset.range F.size) v := by
  unfold readsIn
  calc (gateAt F j).inputs.count v + (gateAt F j').inputs.count v
      = ∑ x ∈ ({j, j'} : Finset ℕ), (gateAt F x).inputs.count v := (Finset.sum_pair (f := fun x => (gateAt F x).inputs.count v) hne).symm
    _ ≤ ∑ x ∈ Finset.range F.size, (gateAt F x).inputs.count v := by
      apply Finset.sum_le_sum_of_subset
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simpa using ‹_›

theorem reads_le_one (F : Circuit) (N : ℕ) (hrb : ReadsBack N F)
    (hin : ∀ i < N, readsIn F (Finset.range F.size) i ≤ 1)
    (hgt : ∀ j < F.size, readsIn F (Finset.range F.size) (N + j) = if j + 1 = F.size then 0 else 1)
    (v : ℕ) : readsIn F (Finset.range F.size) v ≤ 1 := by
  by_cases h1 : v < N
  · exact hin v h1
  by_cases h2 : v < N + F.size
  · have := hgt (v - N) (by omega)
    rw [show N + (v - N) = v by omega] at this
    rw [this]; split <;> omega
  · unfold readsIn
    apply le_of_eq_of_le _ (Nat.zero_le 1)
    apply Finset.sum_eq_zero
    intro j hj
    rw [List.count_eq_zero]
    intro hv
    have := hrb j (Finset.mem_range.mp hj) v hv
    have : j < F.size := Finset.mem_range.mp hj
    simp only [Circuit.size] at *
    omega

theorem Rd_unique {F : Circuit} {N : ℕ} (hR : ∀ v, readsIn F (Finset.range F.size) v ≤ 1)
    {a a' v : ℕ} (h : Rd F N a v) (h' : Rd F N a' v) : a = a' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  by_contra hne
  have hne' : a - N ≠ a' - N := by omega
  have := count_two_le_reads F h2 h2' hne' v
  have c1 := List.count_pos_iff.mpr h3
  have c2 := List.count_pos_iff.mpr h3'
  have := hR v
  omega

theorem chain {F : Circuit} {N : ℕ} (hrb : ReadsBack N F)
    (hR : ∀ v, readsIn F (Finset.range F.size) v ≤ 1) :
    ∀ i a b, below F N a i → below F N b i → below F N a b ∨ below F N b a := by
  intro i
  induction h : N + F.gates.length - i using Nat.strong_induction_on generalizing i with
  | _ m ih =>
    intro a b ha hb
    rcases Relation.ReflTransGen.cases_tail ha with rfl | ⟨c, hac, hci⟩
    · exact Or.inr hb
    rcases Relation.ReflTransGen.cases_tail hb with rfl | ⟨c', hbc, hci'⟩
    · exact Or.inl ha
    have := Rd_unique hR hci hci'
    subst this
    have hic := Rd_lt hrb hci
    have hcb : c < N + F.gates.length := by obtain ⟨h1, h2, _⟩ := hci; omega
    exact ih (N + F.gates.length - c) (by omega) c rfl a b hac hbc

theorem disj {F : Circuit} {N : ℕ} (hrb : ReadsBack N F)
    (hR : ∀ v, readsIn F (Finset.range F.size) v ≤ 1) {j : ℕ} (hj : j < F.gates.length)
    {p q : ℕ} (hpq : (gateAt F j).inputs = [p, q]) (i : ℕ) :
    below F N p i → below F N q i → False := by
  intro hp hq
  have hRp : Rd F N (N + j) p := ⟨by omega, by simpa using hj, by simp [hpq]⟩
  have hRq : Rd F N (N + j) q := ⟨by omega, by simpa using hj, by simp [hpq]⟩
  have hne : p ≠ q := by
    rintro rfl
    have c := count_le_reads F (j := j) hj p
    rw [hpq] at c
    simp only [List.count_cons_self, List.count_singleton_self] at c
    have := hR p
    omega
  have hpl := Rd_lt hrb hRp
  have hql := Rd_lt hrb hRq
  rcases chain hrb hR i p q hp hq with h | h
  · rcases Relation.ReflTransGen.cases_tail h with h' | ⟨c, hpc, hcq⟩
    · exact hne h'.symm
    have := Rd_unique hR hcq hRq
    subst this
    have := below_le hrb hpc
    omega
  · rcases Relation.ReflTransGen.cases_tail h with h' | ⟨c, hqc, hcp⟩
    · exact hne h'
    have := Rd_unique hR hcp hRp
    subst this
    have := below_le hrb hqc
    omega

theorem gate_two {F : Circuit}
    (hG : ∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    {j : ℕ} (hj : j < F.gates.length) :
    ((gateAt F j).op = GateOp.and ∨ (gateAt F j).op = GateOp.or) ∧
      ∃ p q, (gateAt F j).inputs = [p, q] := by
  rw [gateAt_eq F hj]
  obtain ⟨h1, h2⟩ := hG _ (List.getElem_mem hj)
  exact ⟨h1, List.length_eq_two.mp h2⟩

theorem supp (F : Circuit) (N : ℕ) (hrb : ReadsBack N F) :
    ∀ w (S T : Finset (Fin N)), (∀ i : Fin N, below F N w i.val → (i ∈ S ↔ i ∈ T)) →
      wv F N S w = wv F N T w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro S T h
    by_cases h1 : w < N
    · rw [wv_input F N S h1, wv_input F N T h1]
      simp [h ⟨w, h1⟩ Relation.ReflTransGen.refl]
    by_cases h2 : w < N + F.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < F.gates.length := by omega
      rw [wv_gate F N hrb S hj, wv_gate F N hrb T hj]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hRk : Rd F N (N + j) k := ⟨by omega, by simpa using hj, by simpa using hk⟩
      exact ih k (Rd_lt hrb hRk) S T (fun i hi => h i (Relation.ReflTransGen.head hRk hi))
    · rw [wv_big F N S (by omega), wv_big F N T (by omega)]

theorem eval_and (u v : Bool) : GateOp.eval GateOp.and [u, v] = (u && v) := by
  simp [GateOp.eval]

theorem eval_or (u v : Bool) : GateOp.eval GateOp.or [u, v] = (u || v) := by
  simp [GateOp.eval]

theorem mono (F : Circuit) (N : ℕ) (hrb : ReadsBack N F)
    (hG : ∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) :
    ∀ w (S T : Finset (Fin N)), S ⊆ T → wv F N S w = true → wv F N T w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro S T hST h
    by_cases h1 : w < N
    · rw [wv_input F N S h1] at h
      rw [wv_input F N T h1]
      simp only [decide_eq_true_eq] at *
      exact hST h
    by_cases h2 : w < N + F.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < F.gates.length := by omega
      rw [wv_gate F N hrb S hj] at h
      rw [wv_gate F N hrb T hj]
      obtain ⟨hop, p, q, hpq⟩ := gate_two hG hj
      have hRp : Rd F N (N + j) p := ⟨by omega, by simpa using hj, by simp [hpq]⟩
      have hRq : Rd F N (N + j) q := ⟨by omega, by simpa using hj, by simp [hpq]⟩
      have ip := ih p (Rd_lt hrb hRp) S T hST
      have iq := ih q (Rd_lt hrb hRq) S T hST
      rw [hpq] at h ⊢
      simp only [List.map_cons, List.map_nil] at h ⊢
      rcases hop with hop | hop <;> rw [hop] at h ⊢
      · rw [eval_and] at h ⊢
        simp only [Bool.and_eq_true] at h ⊢
        exact ⟨ip h.1, iq h.2⟩
      · rw [eval_or] at h ⊢
        simp only [Bool.or_eq_true] at h ⊢
        exact h.imp ip iq
    · rw [wv_big F N S (by omega)] at h
      exact absurd h (by simp)

def P4 {N : ℕ} (h : Finset (Fin N) → Bool) : Prop :=
  h ∅ = false → ∀ a b c d : Fin N, h {a} = false → h {b} = false → h {c} = false →
    h {d} = false → h {a, b} = true → h {c, b} = true → h {c, d} = true → h {a, d} = true

theorem s1 {N : ℕ} (h : Finset (Fin N) → Bool) (L : Fin N → Prop)
    (hs : ∀ S T : Finset (Fin N), (∀ i, L i → (i ∈ S ↔ i ∈ T)) → h S = h T) {a b : Fin N} (hb : ¬ L b) : h {a, b} = h {a} := by
  apply hs
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact absurd hi hb
  · intro h; exact Or.inl h

theorem s2 {N : ℕ} (h : Finset (Fin N) → Bool) (L : Fin N → Prop)
    (hs : ∀ S T : Finset (Fin N), (∀ i, L i → (i ∈ S ↔ i ∈ T)) → h S = h T) {a b : Fin N} (ha : ¬ L a) : h {a, b} = h {b} := by
  apply hs
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact absurd hi ha
    · rfl
  · intro h; exact Or.inr h

theorem s3 {N : ℕ} (h : Finset (Fin N) → Bool) (L : Fin N → Prop)
    (hs : ∀ S T : Finset (Fin N), (∀ i, L i → (i ∈ S ↔ i ∈ T)) → h S = h T) {a : Fin N} (ha : ¬ L a) : h {a} = h ∅ := by
  apply hs
  intro i hi
  simp only [Finset.mem_singleton, Finset.notMem_empty, iff_false]
  rintro rfl
  exact ha hi

theorem or_side {N : ℕ} (hp hq : Finset (Fin N) → Bool) (Lp Lq : Fin N → Prop)
    (sp : ∀ S T : Finset (Fin N), (∀ i, Lp i → (i ∈ S ↔ i ∈ T)) → hp S = hp T)
    (sq : ∀ S T : Finset (Fin N), (∀ i, Lq i → (i ∈ S ↔ i ∈ T)) → hq S = hq T)
    (dj : ∀ i, Lp i → Lq i → False) (Pp : P4 hp)
    (a b c d : Fin N) (e0 : hp ∅ = false)
    (pa : hp {a} = false) (pb : hp {b} = false) (pc : hp {c} = false) (pd : hp {d} = false)
    (qa : hq {a} = false) (qb : hq {b} = false) (qc : hq {c} = false) (qd : hq {d} = false)
    (hab : hp {a, b} = true) (hcb : (hp {c, b} || hq {c, b}) = true)
    (hcd : (hp {c, d} || hq {c, d}) = true) : (hp {a, d} || hq {a, d}) = true := by
  have Lb : Lp b := by
    by_contra hn; rw [s1 hp Lp sp hn] at hab; rw [pa] at hab; exact absurd hab (by simp)
  have La : Lp a := by
    by_contra hn; rw [s2 hp Lp sp hn] at hab; rw [pb] at hab; exact absurd hab (by simp)
  have nqb : ¬ Lq b := fun h => dj b Lb h
  have hcb' : hp {c, b} = true := by
    rw [s1 hq Lq sq nqb, qc] at hcb; simpa using hcb
  have Lc : Lp c := by
    by_contra hn; rw [s2 hp Lp sp hn, pb] at hcb'; exact absurd hcb' (by simp)
  have nqc : ¬ Lq c := fun h => dj c Lc h
  have hcd' : hp {c, d} = true := by
    rw [s2 hq Lq sq nqc, qd] at hcd; simpa using hcd
  have := Pp e0 a b c d pa pb pc pd hab hcb' hcd'
  simp [this]

theorem P4_or {N : ℕ} (hp hq : Finset (Fin N) → Bool) (Lp Lq : Fin N → Prop)
    (sp : ∀ S T : Finset (Fin N), (∀ i, Lp i → (i ∈ S ↔ i ∈ T)) → hp S = hp T)
    (sq : ∀ S T : Finset (Fin N), (∀ i, Lq i → (i ∈ S ↔ i ∈ T)) → hq S = hq T)
    (dj : ∀ i, Lp i → Lq i → False) (Pp : P4 hp) (Pq : P4 hq) :
    P4 (fun S => hp S || hq S) := by
  intro e a b c d ha hb hc hd hab hcb hcd
  simp only [Bool.or_eq_false_iff] at e ha hb hc hd
  simp only at hab hcb hcd ⊢
  rcases Bool.or_eq_true_iff.mp hab with h | h
  · exact or_side hp hq Lp Lq sp sq dj Pp a b c d e.1 ha.1 hb.1 hc.1 hd.1 ha.2 hb.2 hc.2 hd.2
      h hcb hcd
  · have := or_side hq hp Lq Lp sq sp (fun i h1 h2 => dj i h2 h1) Pq a b c d e.2 ha.2 hb.2 hc.2
      hd.2 ha.1 hb.1 hc.1 hd.1 h (by rw [Bool.or_comm]; exact hcb) (by rw [Bool.or_comm]; exact hcd)
    rw [Bool.or_comm]; exact this

theorem P4_and {N : ℕ} (hp hq : Finset (Fin N) → Bool) (Lp Lq : Fin N → Prop)
    (sp : ∀ S T : Finset (Fin N), (∀ i, Lp i → (i ∈ S ↔ i ∈ T)) → hp S = hp T)
    (sq : ∀ S T : Finset (Fin N), (∀ i, Lq i → (i ∈ S ↔ i ∈ T)) → hq S = hq T)
    (dj : ∀ i, Lp i → Lq i → False) (Pp : P4 hp) (Pq : P4 hq)
    (mp : ∀ S T : Finset (Fin N), S ⊆ T → hp S = true → hp T = true)
    (mq : ∀ S T : Finset (Fin N), S ⊆ T → hq S = true → hq T = true) :
    P4 (fun S => hp S && hq S) := by
  intro e a b c d ha hb hc hd hab hcb hcd
  simp only at e ha hb hc hd hab hcb hcd ⊢
  cases e1 : hp ∅ with
  | true =>
    have hall : ∀ S, hp S = true := fun S => mp ∅ S (Finset.empty_subset S) e1
    simp only [hall, Bool.true_and] at e ha hb hc hd hab hcb hcd ⊢
    exact Pq e a b c d ha hb hc hd hab hcb hcd
  | false =>
  cases e2 : hq ∅ with
  | true =>
    have hall : ∀ S, hq S = true := fun S => mq ∅ S (Finset.empty_subset S) e2
    simp only [hall, Bool.and_true] at e ha hb hc hd hab hcb hcd ⊢
    exact Pp e a b c d ha hb hc hd hab hcb hcd
  | false =>
  simp only [Bool.and_eq_true] at hab hcb hcd ⊢
  have onp : ∀ x : Fin N, hp {x} = true → Lp x := fun x hx => by
    by_contra hn; rw [s3 hp Lp sp hn, e1] at hx; exact absurd hx (by simp)
  have onq : ∀ x : Fin N, hq {x} = true → Lq x := fun x hx => by
    by_contra hn; rw [s3 hq Lq sq hn, e2] at hx; exact absurd hx (by simp)
  have pab : Lp a ∨ Lp b := by
    by_contra hn; push Not at hn
    have := hab.1; rw [s2 hp Lp sp hn.1, s3 hp Lp sp hn.2, e1] at this; exact absurd this (by simp)
  by_cases La : Lp a
  · have nqa : ¬ Lq a := fun h => dj a La h
    have qb : hq {b} = true := by have := hab.2; rwa [s2 hq Lq sq nqa] at this
    have Lqb := onq b qb
    have npb : ¬ Lp b := fun h => dj b h Lqb
    have pa : hp {a} = true := by have := hab.1; rwa [s1 hp Lp sp npb] at this
    have pc : hp {c} = true := by have := hcb.1; rwa [s1 hp Lp sp npb] at this
    have nqc : ¬ Lq c := fun h => dj c (onp c pc) h
    have qd : hq {d} = true := by have := hcd.2; rwa [s2 hq Lq sq nqc] at this
    have npd : ¬ Lp d := fun h => dj d h (onq d qd)
    exact ⟨by rw [s1 hp Lp sp npd]; exact pa, by rw [s2 hq Lq sq nqa]; exact qd⟩
  · have Lb : Lp b := pab.resolve_left La
    have nqb : ¬ Lq b := fun h => dj b Lb h
    have pb : hp {b} = true := by have := hab.1; rwa [s2 hp Lp sp La] at this
    have qa : hq {a} = true := by have := hab.2; rwa [s1 hq Lq sq nqb] at this
    have qc : hq {c} = true := by have := hcb.2; rwa [s1 hq Lq sq nqb] at this
    have npc : ¬ Lp c := fun h => dj c h (onq c qc)
    have pd : hp {d} = true := by have := hcd.1; rwa [s2 hp Lp sp npc] at this
    have nqd : ¬ Lq d := fun h => dj d (onp d pd) h
    exact ⟨by rw [s2 hp Lp sp La]; exact pd, by rw [s1 hq Lq sq nqd]; exact qa⟩

theorem wire_P4 (F : Circuit) (N : ℕ) (hrb : ReadsBack N F)
    (hG : ∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hR : ∀ v, readsIn F (Finset.range F.size) v ≤ 1) :
    ∀ w, P4 (fun S => wv F N S w) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases h1 : w < N
    · intro e a b c d ha hb hc hd hab _ _
      simp only [wv_input F N _ h1, decide_eq_false_iff_not, decide_eq_true_eq,
        Finset.mem_singleton, Finset.mem_insert] at ha hb hab
      rcases hab with h | h
      · exact absurd h ha
      · exact absurd h hb
    by_cases h2 : w < N + F.gates.length
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < F.gates.length := by omega
      obtain ⟨hop, p, q, hpq⟩ := gate_two hG hj
      have hRp : Rd F N (N + j) p := ⟨by omega, by simpa using hj, by simp [hpq]⟩
      have hRq : Rd F N (N + j) q := ⟨by omega, by simpa using hj, by simp [hpq]⟩
      have Pp := ih p (Rd_lt hrb hRp)
      have Pq := ih q (Rd_lt hrb hRq)
      have sp := supp F N hrb p
      have sq := supp F N hrb q
      have dj : ∀ i : Fin N, below F N p i.val → below F N q i.val → False :=
        fun i => disj hrb hR hj hpq i.val
      have heq : (fun S => wv F N S (N + j)) =
          fun S => (gateAt F j).op.eval [wv F N S p, wv F N S q] := by
        funext S; rw [wv_gate F N hrb S hj, hpq]; rfl
      rw [heq]
      rcases hop with hop | hop <;> rw [hop]
      · simp only [eval_and]
        exact P4_and _ _ _ _ sp sq dj Pp Pq (mono F N hrb hG p) (mono F N hrb hG q)
      · simp only [eval_or]
        exact P4_or _ _ _ _ sp sq dj Pp Pq
    · intro e a b c d ha hb hc hd hab _ _
      simp only [wv_big F N _ (show N + F.gates.length ≤ w by omega)] at hab
      exact absurd hab (by simp)

theorem two_leaves (N : ℕ) (F : Circuit)
    (hG : ∀ g ∈ F.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (hrb : ReadsBack N F)
    (hout : F.output + 1 = N + F.size ∨ (F.size = 0 ∧ F.output < N))
    (hgt : ∀ j < F.size, readsIn F (Finset.range F.size) (N + j) = if j + 1 = F.size then 0 else 1)
    (hR : ∀ v, readsIn F (Finset.range F.size) v ≤ 1)
    (a b : Fin N) (hab : a ≠ b)
    (hrd : ∀ i : Fin N, readsIn F (Finset.range F.size) i.val = 1 ↔ (i = a ∨ i = b)) :
    (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a && x b)) ∨
      (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a || x b)) := by
  have hsz : 0 < F.size := by
    by_contra h0
    have := (hrd a).mpr (Or.inl rfl)
    simp only [show F.size = 0 by omega, Finset.range_zero, readsIn, Finset.sum_empty] at this
    omega
  have hl : 0 < F.gates.length := hsz
  obtain ⟨hop, p, q, hpq⟩ := gate_two hG hl
  have hp : p < N := by have := hrb 0 hl p (by simp [hpq]); omega
  have hq : q < N := by have := hrb 0 hl q (by simp [hpq]); omega

  have readab : ∀ v (hv : v < N), v ∈ (gateAt F 0).inputs → (⟨v, hv⟩ : Fin N) = a ∨ ⟨v, hv⟩ = b := by
    intro v hv hmem
    apply (hrd ⟨v, hv⟩).mp
    have := count_le_reads F hsz v
    have := List.count_pos_iff.mpr hmem
    have := hR v
    simp only at *
    omega
  have hpq' : p ≠ q := by
    rintro rfl
    have c := count_le_reads F hsz p
    rw [hpq] at c
    simp only [List.count_cons_self, List.count_singleton_self] at c
    have := hR p
    omega

  have hs1 : F.size = 1 := by
    by_contra hne
    have h1 : 1 < F.gates.length := by simp only [Circuit.size] at *; omega
    obtain ⟨_, r, s, hrs⟩ := gate_two hG h1
    have only_N : ∀ v ∈ (gateAt F 1).inputs, v = N := by
      intro v hv
      have hvlt : v < N + 1 := hrb 1 h1 v hv
      by_contra hvN
      have hvN' : v < N := by omega
      have c1 := List.count_pos_iff.mpr hv
      have two := count_two_le_reads F hsz (show 1 < F.size from h1) (by omega) v
      have := hR v
      by_cases h0 : v ∈ (gateAt F 0).inputs
      · have := List.count_pos_iff.mpr h0
        omega
      · have hz := List.count_eq_zero.mpr h0

        have hone : readsIn F (Finset.range F.size) v = 1 := by
          have := count_le_reads F (show 1 < F.size from h1) v
          omega
        rcases (hrd ⟨v, hvN'⟩).mp hone with h | h
        · have : v = p ∨ v = q := by
            rcases readab p hp (by simp [hpq]) with h' | h' <;>
            rcases readab q hq (by simp [hpq]) with h'' | h'' <;>
            simp only [Fin.ext_iff] at h h' h'' <;> omega
          rcases this with rfl | rfl <;> simp [hpq] at h0
        · have : v = p ∨ v = q := by
            rcases readab p hp (by simp [hpq]) with h' | h' <;>
            rcases readab q hq (by simp [hpq]) with h'' | h'' <;>
            simp only [Fin.ext_iff] at h h' h'' <;> omega
          rcases this with rfl | rfl <;> simp [hpq] at h0
    have hr := only_N r (by simp [hrs])
    have hs := only_N s (by simp [hrs])
    have c := count_le_reads F (show 1 < F.size from h1) N
    rw [hrs, hr, hs] at c
    simp only [List.count_cons_self, List.count_singleton_self] at c
    have := hR N
    omega
  have hgl : F.gates.length = 1 := hs1
  have hout' : F.output = N := by
    rcases hout with h | h
    · omega
    · omega
  obtain ⟨g0, hg0⟩ := List.length_eq_one_iff.mp hgl
  have hg0' : gateAt F 0 = g0 := by simp [gateAt, hg0]
  rw [hg0'] at hop hpq
  have pa := readab p hp (by simp [hg0', hpq])
  have qa := readab q hq (by simp [hg0', hpq])
  have hval : ∀ x : Fin N → Bool, F.eval (List.ofFn x) =
      g0.op.eval [x ⟨p, hp⟩, x ⟨q, hq⟩] := by
    intro x
    simp only [Circuit.eval, Circuit.wires, hg0, List.foldl_cons, List.foldl_nil, hout', hpq,
      List.map_cons, List.map_nil]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp [List.getD_eq_getElem?_getD, hp, hq]
  have key : (⟨p, hp⟩ = a ∧ (⟨q, hq⟩ : Fin N) = b) ∨ (⟨p, hp⟩ = b ∧ (⟨q, hq⟩ : Fin N) = a) := by
    have hne : (⟨p, hp⟩ : Fin N) ≠ ⟨q, hq⟩ := by simp [Fin.ext_iff, hpq']
    rcases pa with h1 | h1 <;> rcases qa with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hne
  rcases hop with hop | hop
  · left; intro x; rw [hval, hop, eval_and]
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]; rw [Bool.and_comm]
  · right; intro x; rw [hval, hop, eval_or]
    rcases key with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]; rw [Bool.or_comm]

end PEqualNP.Outside.L_meta_23964

theorem PEqualNP.Outside.L_meta_23964 : (∀ (N : ℕ) (F : PEqualNP.CircuitLowerBounds.Circuit), ((∀ g ∈ F.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N F ∧ (F.output + 1 = N + F.size ∨ (F.size = 0 ∧ F.output < N)) ∧ (∀ i < N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i ≤ 1) ∧ (∀ j < F.size, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) (N + j) = if j + 1 = F.size then 0 else 1)) → ((F.eval (List.ofFn fun k : Fin N => decide (k ∈ (∅ : Finset (Fin N)))) = false → (∀ a : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a} : Finset (Fin N)))) = false) → ∀ a b c d : Fin N, F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, b} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({c, d} : Finset (Fin N)))) = true → F.eval (List.ofFn fun k : Fin N => decide (k ∈ ({a, d} : Finset (Fin N)))) = true) ∧ (∀ a b : Fin N, a ≠ b → (∀ i : Fin N, PEqualNP.MetaComplexity.NestedCover.readsIn F (Finset.range F.size) i.val = 1 ↔ (i = a ∨ i = b)) → (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a && x b)) ∨ (∀ x : Fin N → Bool, F.eval (List.ofFn x) = (x a || x b))))) := by
  intro N F ⟨hG, hrb, hout, hin, hgt⟩
  have hR := PEqualNP.Outside.L_meta_23964.reads_le_one F N hrb hin hgt
  refine ⟨?_, ?_⟩
  · intro e hs a b c d hab hcb hcd
    exact PEqualNP.Outside.L_meta_23964.wire_P4 F N hrb hG hR F.output e a b c d (hs a) (hs b)
      (hs c) (hs d) hab hcb hcd
  · intro a b hne hrd
    exact PEqualNP.Outside.L_meta_23964.two_leaves N F hG hrb hout hgt hR a b hne hrd
