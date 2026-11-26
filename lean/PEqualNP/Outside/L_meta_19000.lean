import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19000

open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

theorem V_append {n : ℕ} (fs fs' : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    V (fs ++ fs') x = V fs x ++ fs'.map (fun f => f x) := by
  simp [V]

theorem V_length {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (V fs x).length = n + fs.length := by simp [V]

theorem V_read {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) (j : ℕ)
    (hj : j < fs.length) : (V fs x).getD (n + j) false = fs.getD j (fun _ => false) x := by
  simp only [V]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem val_ext {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Val fs i F) (fs' : List ((Fin n → Bool) → Bool)) : Val (fs ++ fs') i F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [V_append, List.getD_append _ _ _ _ (by rw [V_length]; exact h.1)]
  exact h.2 x

theorem val_congr {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ}
    {F F' : (Fin n → Bool) → Bool} (h : Val fs i F) (e : ∀ x, F x = F' x) : Val fs i F' :=
  ⟨h.1, fun x => by rw [h.2 x, e x]⟩

theorem val_in {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (a : Fin n) :
    Val fs a.val (fun x => x a) := by
  refine ⟨by omega, fun x => ?_⟩
  simp only [V]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

theorem val_new {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) :
    Val (fs ++ [f]) (n + fs.length) f := by
  refine ⟨by simp, fun x => ?_⟩
  rw [V_read _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem sem_snoc {n : ℕ} {gs : List Gate} {fs : List ((Fin n → Bool) → Bool)} (h : Sem gs fs)
    (op : GateOp) (a b : ℕ) (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B) :
    Sem (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) := by
  intro x
  rw [wf_snoc, h x, V_append]
  simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def StrictAO2 (n : ℕ) (gs : List Gate) : Prop :=
  ∀ (j : ℕ) (g : Gate), gs[j]? = some g →
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    ∃ (a b : Fin (n + j)), g.inputs = [a.val, b.val] ∧ a ≠ b

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ StrictAO2 n gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true)

theorem st_nil {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : St G P [] [] := by
  refine ⟨fun x => by simp [wf, V], rfl, fun j g h => by simp at h, ?_⟩
  simp

theorem st_weak {n : ℕ} {G : SimpleGraph (Fin n)} {P Q : Fin n → Prop} {gs fs}
    (h : St G P gs fs) (hPQ : ∀ l, P l → Q l) : St G Q gs fs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, fun j hj hand => ?_⟩
  obtain ⟨l, hl, hl2⟩ := h4 j hj hand
  exact ⟨l, hPQ l hl, hl2⟩

theorem push {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} {gs : List Gate}
    {fs : List ((Fin n → Bool) → Bool)} (h : St G P gs fs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (hab : a ≠ b)
    (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B)
    (nA : op = GateOp.and → ∃ l, P l ∧ ∀ x, op.eval [A x, B x] = true → x l = true) :
    St G P (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Val (fs ++ [fun x => op.eval [A x, B x]]) (n + fs.length) (fun x => op.eval [A x, B x]) := by
  obtain ⟨hs, hl, hm, hA⟩ := h
  refine ⟨⟨sem_snoc hs op a b A B ha hb, by simp [hl], ?_, ?_⟩, val_new _ _⟩
  · intro j g hj
    by_cases hlt : j < gs.length
    · rw [List.getElem?_append_left hlt] at hj
      exact hm j g hj
    · by_cases heq : j = gs.length
      · subst heq
        rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero] at hj
        injection hj with hgeq
        subst hgeq
        refine ⟨hop, ⟨a, by have := ha.1; omega⟩, ⟨b, by have := hb.1; omega⟩, rfl, ?_⟩
        intro heq_fin
        exact hab (congrArg Fin.val heq_fin)
      · have hge : (gs ++ [Gate.mk op [a, b]]).length ≤ j := by simp; omega
        rw [List.getElem?_eq_none hge] at hj
        cases hj
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨l, hl1, hl2⟩ := hA j hj hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨l, hl1, hl2⟩ := nA hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx

theorem chain {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} (c : Fin n) :
    ∀ (rest : List (Fin n)) (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (a : ℕ)
      (A : (Fin n → Bool) → Bool), St G P gs fs → Val fs a A →
      (∀ w ∈ rest, a ≠ w.val) → a ≠ c.val → (∀ w ∈ rest, w.val ≠ c.val) →
      ∃ gs' fs' o, St G P gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
        gs'.length = gs.length + rest.length ∧ o ≠ c.val ∧
        Val fs' o (fun x => A x || rest.any (fun w => x w))
  | [], gs, fs, a, A, h, ha, _, hac, _ =>
    ⟨gs, fs, a, h, ⟨[], by simp⟩, by simp, hac, by simpa using ha⟩
  | w :: rest, gs, fs, a, A, h, ha, hne, hac, hrest_c => by
    have haw : a ≠ w.val := hne w (List.mem_cons_self)
    obtain ⟨h1, h2⟩ := push h GateOp.or (Or.inr rfl) a w.val haw A (fun x => x w) ha (val_in fs w)
      (fun e => by simp at e)
    obtain ⟨gs', fs', o, h3, ⟨fsn, hfs⟩, hlen, hoc, hv⟩ :=
      chain c rest _ _ (n + fs.length) _ h1 h2
        (fun w' _ => by omega) (by omega) (fun w' hw' => hrest_c w' (List.mem_cons_of_mem _ hw'))
    refine ⟨gs', fs', o, h3, ⟨(fun x => GateOp.or.eval [A x, x w]) :: fsn, by rw [hfs]; simp⟩, ?_, hoc, ?_⟩
    · rw [hlen]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    refine ⟨hv.1, fun x => ?_⟩
    rw [hv.2 x]
    simp [GateOp.eval, Bool.or_assoc]

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

theorem gad_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {c : Fin n} (h : N G C c = ∅) (x : Fin n → Bool) : gad G C c x = false := by
  simp [gad, h]

theorem gadget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {P : Fin n → Prop} (c : Fin n) (hne : (N G C c).Nonempty)
    (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (h : St G P gs fs) :
    ∃ gs' fs' o, St G (fun l => P l ∨ l = c) gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
      gs'.length = gs.length + (N G C c).card ∧ n + fs.length ≤ o ∧ Val fs' o (gad G C c) := by
  have hL : (N G C c).toList ≠ [] := by
    rw [Ne, Finset.toList_eq_nil]; exact hne.ne_empty
  obtain ⟨w0, rest, hL⟩ := List.exists_cons_of_ne_nil hL
  have hnd : (w0 :: rest).Nodup := by
    rw [← hL]; exact Finset.nodup_toList _
  have hw0_not_rest : w0 ∉ rest := (List.nodup_cons.1 hnd).1
  have hw0 : w0 ∈ N G C c := by
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_self
  have hmem_rest : ∀ w ∈ rest, w ∈ N G C c := by
    intro w hw
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_of_mem _ hw
  have hne_c : ∀ w ∈ N G C c, w.val ≠ c.val := by
    intro w hw heq
    have hwc : w = c := Fin.ext heq
    subst hwc
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact G.irrefl hw.1
  have hcard : (N G C c).card = rest.length + 1 := by
    rw [← Finset.length_toList, hL]; simp
  have key : ∀ x : Fin n → Bool,
      (x w0 || rest.any (fun w => x w)) = decide (∃ w ∈ N G C c, x w = true) := by
    intro x
    have : (x w0 || rest.any (fun w => x w)) = (N G C c).toList.any (fun w => x w) := by
      rw [hL]; simp
    rw [this, Bool.eq_iff_iff]
    simp [List.any_eq_true, Finset.mem_toList]
  obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, ho1c, hv1⟩ :=
    chain c rest gs fs w0.val (fun x => x w0) h (val_in fs w0)
      (fun w hw heq => hw0_not_rest (Fin.ext heq ▸ hw))
      (hne_c w0 hw0)
      (fun w hw => hne_c w (hmem_rest w hw))
  obtain ⟨h2, hv2⟩ := push (st_weak (Q := fun l => P l ∨ l = c) h1 (fun l hl => Or.inl hl))
    GateOp.and (Or.inl rfl) c.val o1 (Ne.symm ho1c)
    (fun x => x c) _ (val_in fs1 c) hv1
    (fun _ => ⟨c, Or.inr rfl, fun x hx => by simp [GateOp.eval] at hx; exact hx.1⟩)
  refine ⟨_, _, n + fs1.length, h2,
    ⟨fsn ++ [fun x => GateOp.and.eval [x c, x w0 || rest.any fun w => x w]], by rw [hfs]; simp⟩,
    ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen1, hcard]; omega
  · rw [hfs, List.length_append]; omega
  refine val_congr hv2 (fun x => ?_)
  simp only [GateOp.eval, gad, ← key x]
  simp

theorem build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (S : Finset (Fin n)) : S ⊆ C →
    ∃ gs fs, St G (fun l => l ∈ S) gs fs ∧
      ((gs = [] ∧ ∀ c ∈ S, N G C c = ∅) ∨
       ∃ o, Val fs o (fun x => decide (∃ c ∈ S, gad G C c x = true)) ∧
         gs.length + 1 ≤ (∑ c ∈ S, (N G C c).card) + S.card) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; exact ⟨[], [], st_nil G _, Or.inl ⟨rfl, by simp⟩⟩
  | insert c S hlt ih =>
    intro hsub
    have hcS : c ∉ S := fun hc => lt_irrefl _ (hlt c hc)
    obtain ⟨gs, fs, h, hcase⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    by_cases hN : N G C c = ∅
    · refine ⟨gs, fs, st_weak h (fun l hl => Finset.mem_insert_of_mem hl), ?_⟩
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · left
        refine ⟨hg, ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hN
        · exact hall c' hc'
      · right
        refine ⟨o, val_congr hv ?_, ?_⟩
        · intro x
          simp [Finset.mem_insert, gad_empty hN]
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]; omega
    · have hne : (N G C c).Nonempty := Finset.nonempty_iff_ne_empty.2 hN
      obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, ho1ge, hv1⟩ := gadget c hne gs fs h
      have h1' : St G (fun l => l ∈ insert c S) gs1 fs1 := by
        refine st_weak h1 ?_
        intro l hl
        rcases hl with hl | rfl
        · exact Finset.mem_insert_of_mem hl
        · exact Finset.mem_insert_self _ _
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · refine ⟨gs1, fs1, h1', Or.inr ⟨o1, val_congr hv1 ?_, ?_⟩⟩
        · intro x
          have : ¬ ∃ c' ∈ S, gad G C c' x = true := by
            rintro ⟨c', hc', hg'⟩
            rw [gad_empty (hall c' hc')] at hg'
            exact Bool.false_ne_true hg'
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, Finset.mem_insert]
          constructor
          · intro hx; exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact hx
            · exact absurd ⟨c', hc', hx⟩ this
        · subst hg
          rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp at hlen1
          omega
      · have hoo1 : o ≠ o1 := by have := hv.1; omega
        obtain ⟨h2, hv2⟩ := push h1' GateOp.or (Or.inr rfl) o o1 hoo1 _ _
          (by rw [hfs]; exact val_ext hv fsn) hv1 (fun e => by simp at e)
        refine ⟨_, _, h2, Or.inr ⟨_, val_congr hv2 ?_, ?_⟩⟩
        · intro x
          rw [Bool.eq_iff_iff]
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id,
            Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
          constructor
          · rintro (⟨c', hc', hx⟩ | hx)
            · exact ⟨c', Or.inr hc', hx⟩
            · exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact Or.inr hx
            · exact Or.inl ⟨c', hc', hx⟩
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp only [List.length_append, List.length_singleton]
          omega

theorem edge_N {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) {u v : Fin n} (h : G.Adj u v) :
    ∃ c ∈ C, ∃ w ∈ N G C c, (c = u ∧ w = v) ∨ (c = v ∧ w = u) := by
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hC u v h with hu | hv
  · by_cases hv' : v ∈ C ∧ v < u
    · refine ⟨v, hv'.1, u, ⟨h.symm, fun hh => lt_asymm hh.2 hv'.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨u, hu, v, ⟨h, hv'⟩, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hu' : u ∈ C ∧ u < v
    · exact ⟨u, hu'.1, v, ⟨h, fun hh => lt_asymm hh.2 hu'.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, ⟨h.symm, hu'⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem any_gad {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (x : Fin n → Bool) :
    decide (∃ c ∈ C, gad G C c x = true) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
  rw [Bool.eq_iff_iff]
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, gad, decide_eq_true_eq,
    Bool.and_eq_true, Bool.or_eq_true, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨c, -, hc, w, hw, hxw⟩
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨c, w, hw.1, hc, hxw⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨c, hc, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge_N hC h
    · exact ⟨c, hc, hu, w, hw, hv⟩
    · exact ⟨c, hc, hv, w, hw, hu⟩

theorem sumN_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    ∑ c ∈ C, (N G C c).card ≤ G.edgeFinset.card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2.1
  · rintro ⟨c, w⟩ hp ⟨c', w'⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      have e1 : ¬ w < c := fun hl => hp.2.2 ⟨hq.1, hl⟩
      have e2 : ¬ c < w := fun hl => hq.2.2 ⟨hp.1, hl⟩
      have : c = w := le_antisymm (not_lt.1 e1) (not_lt.1 e2)
      subst this
      exact G.irrefl hp.2.1

theorem main2 (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : ∀ u v : Fin n, G.Adj u v → u ∈ C ∨ v ∈ C) :
    ∃ D : Circuit, StrictAO2 n D.gates ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      PEqualNP.EdgeOwnership.HasStarProfile n G D ∧
      D.size ≤ G.edgeFinset.card + C.card - 1 := by
  obtain ⟨gs, fs, ⟨hs, hl, hm, hA⟩, hcase⟩ := build G C C (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, fun j g h => by simp at h, ?_, ?_, by simp [Circuit.size]⟩
    · funext x
      rw [← any_gad hC x]
      have : ¬ ∃ c ∈ C, gad G C c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp at hj
  · refine ⟨⟨gs, o⟩, hm, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hC x
    · intro j hj hand
      have hj' : j < gs.length := hj
      obtain ⟨l, -, hl2⟩ := hA j hj' hand
      have gv : ∀ i, i < gs.length → ∀ y : Fin n → Bool,
          PEqualNP.EdgeOwnership.gateVal n ⟨gs, o⟩ i y = fs.getD i (fun _ => false) y := by
        intro i hi y
        show (wf gs (List.ofFn y)).getD (n + i) false = _
        rw [hs y, V_read _ _ _ (by omega)]
      right
      refine ⟨l, fun u v _ hown => ?_⟩
      have h1 := hown.2.2.1
      rw [gv j hj'] at h1
      have h2 := hl2 _ h1
      simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at h2
      rcases h2 with h2 | h2
      · exact Or.inl h2.symm
      · exact Or.inr h2.symm
    · have h1 := sumN_le G C
      show gs.length ≤ _
      omega

end PEqualNP.Outside.L_meta_19000

theorem PEqualNP.Outside.L_meta_19000 : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : Finset (Fin (26 : ℕ))), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 → x4 ∈ x3 ∨ x5 ∈ x3) → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 : ℕ) (x7 : PEqualNP.CircuitLowerBounds.Gate), x5.gates[x6]? = Option.some x7 → (x7.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x7.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x9 : Fin ((26 : ℕ) + x6)) (x10 : Fin ((26 : ℕ) + x6)), x7.inputs = [↑x9, ↑x10] ∧ x9 ≠ x10) ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x5 = PEqualNP.MetaComplexity.NestedCover.graphFun x1 ∅ ∧ PEqualNP.EdgeOwnership.HasStarProfile (26 : ℕ) x1 x5 ∧ x5.size ≤ x1.edgeFinset.card + x3.card - (1 : ℕ) := by
  intro G _ K hK
  exact PEqualNP.Outside.L_meta_19000.main2 26 G K hK
