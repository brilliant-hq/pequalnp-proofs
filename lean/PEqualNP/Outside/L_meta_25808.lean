import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x
theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]
theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega
theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]
theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]
theorem run_init (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]
theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_init [] gs x i (by simpa using hi)
  simpa [run] using this
theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_init gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_init gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)
def rv (w : List Bool) : Bool ⊕ ℕ → Bool
  | .inl b => b
  | .inr t => w.getD t false
theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_init _ _ _ _ (h t rfl)
theorem gv (N : ℕ) (C : Circuit) (hb : ReadsBack N C) (x : List Bool) (hx : x.length = N) (j : ℕ)
    (hj : j < C.gates.length) :
    (run C.gates x).getD (N + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (run C.gates x).getD i false) := by
  have hw := run_gate C.gates x j hj
  have he : gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj
  rw [hx, ← he] at hw
  rw [hw]
  congr 1
  exact List.map_congr_left fun i hi => if_pos (hb j hj i hi)
theorem past (gs : List Gate) (x : List Bool) (i : ℕ) (hi : x.length + gs.length ≤ i) :
    (run gs x).getD i false = false :=
  List.getD_eq_default _ _ (by rw [run_length]; exact hi)
theorem oneEach_length {n m : ℕ} (u : Fin n) (v : Fin m) :
    (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]
theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  by_cases h : i < n
  · rw [List.getElem?_append_left (by simpa using h)]
    simp only [List.getElem?_ofFn]
    simp [h, Fin.ext_iff]
    omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp [h2, Fin.ext_iff]
      have hu : ¬ i = u.val := by omega
      by_cases hv : i = n + v.val
      · simp [hv]
      · have hv' : ¬ i - n = v.val := by omega
        simp [hu, hv, hv']
    · simp [h2]
      omega
def reads (g : Gate) (w : ℕ) : Prop :=
  (g.op = .not ∧ g.inputs.head? = some w) ∨ (g.op ≠ .not ∧ w ∈ g.inputs)
def Good (P : Prop) (g : Gate) : Prop :=
  ((g.op = .not ∧ ∃ a, g.inputs = [a]) ∨
    ((g.op = .and ∨ g.op = .or) ∧ ∃ a b, a ≠ b ∧ g.inputs = [a,b])) ∧
    (P → g.op = .and ∨ g.op = .or)
theorem good_fan {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) : FanInTwo C := by
  intro g hg
  rcases (h g hg).1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [ho,ha]
  · rcases ho with ho|ho <;> simp [ho,ha]
theorem good_mono {P : Prop} {C : Circuit} (h : ∀ g ∈ C.gates, Good P g) :
    P → Monotone2 C := by
  intro p g hg
  exact ⟨by simpa using (h g hg).2 p,(good_fan h g hg).2⟩
theorem good_read {P : Prop} {g : Gate} (h : Good P g) (w : ℕ) : reads g w ↔ w ∈ g.inputs := by
  rcases h.1 with ⟨ho,a,ha⟩ | ⟨ho,a,b,_,ha⟩
  · simp [reads,ho,ha,eq_comm]
  · rcases ho with ho|ho <;> simp [reads,ho]
end PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
namespace PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
theorem emit (P : Prop) (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (hmon : P → op = GateOp.and ∨ op = GateOp.or)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
      (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, Good P g → (∀ t ∈ g.inputs, t < N + hs.length) →
      (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, Good P g) ∧
        (∀ g ∈ e, ∀ t ∈ g.inputs, t < N + hs.length) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h1' h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, by simpa using h1', ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  by_cases hn : op = GateOp.not
  · subst op
    rcases rs with _ | ⟨r, rs⟩
    · exact keep (.inl true) (by simp) (by intro y hy; rfl)
    · have hr := hv r (by simp)
      rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y hy; rfl)
      · exact add ⟨.not,[t]⟩ ⟨Or.inl ⟨rfl,t,rfl⟩,hmon⟩ (by simpa using hr t rfl)
          (by intro y hy; rfl)
  have hop' : op = GateOp.and ∨ op = GateOp.or := by tauto
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop' with rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop' with rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop' with rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.and,[t,q]⟩ ⟨Or.inr ⟨Or.inl rfl,t,q,same,rfl⟩,fun _ => Or.inl rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · by_cases same : t=q
          · subst q
            exact keep (.inr t) hr (by intro y _; simp [GateOp.eval,rv])
          · exact add ⟨GateOp.or,[t,q]⟩ ⟨Or.inr ⟨Or.inr rfl,t,q,same,rfl⟩,fun _ => Or.inr rfl⟩
              (by simp; exact ⟨hr t rfl, hs' q rfl⟩) (by intro y _; simp [GateOp.eval,rv])
  · simp at hl
theorem engine {X : Type} (P : Prop) (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : FanInTwo C) (hmon : P → Monotone2 C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size + F.card ≤ C.size ∧
      ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, by simp, ?_, ?_⟩
      · intro w t hw ht
        beta_reduce at ht
        split_ifs at ht with h1 h2
        cases ht
        simpa using h1.choose_spec.1
      · intro x w hw
        simp only [Nat.add_zero] at hw
        rw [run_input _ _ _ (by rw [hsrc]; exact hw)]
        beta_reduce
        split_ifs with h1 h2
        · exact h1.choose_spec.2 x
        · exact h2.choose_spec x
        · rcases h0 w hw with h | h
          · exact absurd h h2
          · exact absurd h h1
    | succ k ih =>
      intro hk
      obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega
      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, Good P g) → (∀ g ∈ e, ∀ t ∈ g.inputs, t < M + hs.length) →
          (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, Good P g) ∧
      (∀ i (hi : i < hs.length), ∀ t ∈ hs[i].inputs, t < M + i) ∧
      hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he he' hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · intro i hi t ht
          rw [List.getElem_append] at ht
          split_ifs at ht with hih
          · exact h5 i hih t ht
          · have hmem : e[i - hs.length]'(by simp at hi; omega) ∈ e := List.mem_iff_getElem.mpr ⟨_, _, rfl⟩
            have := he' _ hmem t ht
            omega
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [if_pos hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [if_pos hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [if_neg hkF] at e2 hlen
            rw [Finset.card_empty] at e2
            omega
        · intro w t hw ht
          rw [List.length_append]
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self] at ht
            have := hr t ht; omega
          · rw [Function.update_of_ne hwe] at ht
            have := h3 w t (by omega) ht; omega
        · intro x w hw
          by_cases hwe : w = n + k
          · subst hwe; rw [Function.update_self]; exact hval x
          · rw [Function.update_of_ne hwe, h4 x w (by omega)]
            refine (rv_ext hs e (tgt x) (m w) fun t ht => ?_).symm
            have := h3 w t (by omega) ht
            rw [htgt]; exact this
      by_cases hkF : k ∈ F
      · rcases (hF k hkF).2 with ⟨b, hb⟩ | ⟨w, hw, hb⟩
        · exact fin (.inl b) [] (by simp) (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e2', e3, e4⟩ := emit P M hs C.gates[k].op hop (fun p => by simpa using (hmon p _ (List.getElem_mem hk')).1) (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e2' e3 (by simp [hkF]; exact e1) (fun x => ?_)
        rw [e4 _ (htgt x)]
        have rg := run_gate C.gates (src x) k hk'
        rw [hsrc] at rg
        rw [rg, List.map_map]
        congr 1
        refine List.map_congr_left fun i _ => ?_
        simp only [Function.comp, m']
        split_ifs with h
        · exact h4 x i h
        · rfl
  obtain ⟨hs, m, h1, h5, h2, h3, h4⟩ := key C.gates.length le_rfl
  have hFc : (F.filter fun j => j < C.gates.length) = F := Finset.filter_true_of_mem fun j hj => (hF j hj).1
  rw [hFc] at h2
  have hout : C.output < n + C.gates.length := by
    by_contra h
    refine hne ⟨false, fun x => ?_⟩
    change (run C.gates (src x)).getD C.output false = false
    rw [List.getD_eq_default _ _ (by rw [run_length, hsrc]; omega)]
  have hev : ∀ x, C.eval (src x) = rv (run hs (tgt x)) (m C.output) := fun x => h4 x _ hout
  rcases hm : m C.output with b | t
  · exact absurd ⟨b, fun x => by rw [hev, hm]; rfl⟩ hne
  · refine ⟨⟨hs, t⟩, ?_, ?_, h2, fun x => ?_⟩
    · exact h1
    · intro j hj i hi
      have hj' : j < hs.length := hj
      have he : gateAt ⟨hs, t⟩ j = hs[j] := List.getD_eq_getElem _ _ hj'
      rw [he] at hi
      exact h5 j hj' i hi
    · have := hev x
      rw [hm] at this
      exact this.symm
end PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
namespace PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def collapses {X : Type} (W : X → ℕ → Bool) (top : ℕ) (out : X → Bool) : Prop :=
  (∃ b, ∀ x, out x = b) ∨ ∃ w < top, ∀ x, out x = W x w
theorem read_pair (l : List ℕ) (w : ℕ) (hlen : l.length ≤ 2) (hw : w ∈ l) :
    l = [w] ∨ ∃ v, l = [w,v] ∨ l = [v,w] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d,tail⟩⟩⟩
  · simp at hw
  · have e : w=a := by simpa using hw
    exact Or.inl (by rw [e])
  · rcases List.mem_cons.mp hw with e | h
    · exact Or.inr ⟨b,Or.inl (by rw [e])⟩
    · have e : w=b := by simpa using h
      exact Or.inr ⟨a,Or.inr (by rw [e])⟩
  · simp at hlen
theorem not_value {X : Type} (W : X → ℕ → Bool) (g : Gate) {w : ℕ} {b : Bool}
    (op : g.op = .not) (r : reads g w) (fixed : ∀ x, W x w = b) (x : X) :
    g.op.eval (g.inputs.map (W x)) = !b := by
  have he : g.inputs.head? = some w := by simpa [reads,op] using r
  cases h : g.inputs with
  | nil => simp [h] at he
  | cons a tail =>
    have e : a=w := by simpa [h] using he
    simp [op,h,GateOp.eval,e,fixed]
theorem dominant {X : Type} (W : X → ℕ → Bool) (g : Gate) (w : ℕ)
    (hlen : g.inputs.length ≤ 2) (r : reads g w) (op : g.op = .and ∨ g.op = .not)
    (fixed : ∀ x, W x w = false) :
    ∃ b, ∀ x, g.op.eval (g.inputs.map (W x)) = b := by
  rcases op with h|h
  · have mem : w ∈ g.inputs := by simpa [reads,h] using r
    refine ⟨false,fun x => ?_⟩
    rcases read_pair _ w hlen mem with e | ⟨v,e|e⟩ <;> simp [h,e,GateOp.eval,fixed]
  · exact ⟨true,not_value W g h r fixed⟩
theorem when_read {X : Type} (W : X → ℕ → Bool) (g : Gate) (top w : ℕ) (b : Bool)
    (ok : g.op = .and ∨ g.op = .or ∨ g.op = .not) (hlen : g.inputs.length ≤ 2)
    (before : ∀ t ∈ g.inputs, t < top) (r : reads g w) (fixed : ∀ x, W x w = b) :
    collapses W top (fun x => g.op.eval (g.inputs.map (W x))) := by
  by_cases hn : g.op = .not
  · exact Or.inl ⟨!b,not_value W g hn r fixed⟩
  have hop : g.op = .and ∨ g.op = .or := by tauto
  have mem : w ∈ g.inputs := by simpa [reads,hn] using r
  rcases read_pair _ w hlen mem with e | ⟨v,e⟩
  · refine Or.inl ⟨b,fun x => ?_⟩
    rcases hop with ho|ho <;> simp [ho,e,GateOp.eval,fixed]
  · have hv : v < top := before v (by rcases e with h|h <;> simp [h])
    rcases hop with h|h
    · cases b
      · refine Or.inl ⟨false,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
    · cases b
      · refine Or.inr ⟨v,hv,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
      · refine Or.inl ⟨true,fun x => ?_⟩
        rcases e with h'|h' <;> simp [h,h',GateOp.eval,fixed]
def toNat {s : ℕ} (K : Finset (Fin s)) : Finset ℕ := K.map ⟨Fin.val,Fin.val_injective⟩
theorem marked {X : Type} (N : ℕ) (C : Circuit) (src : X → List Bool)
    (hs : ∀ x, (src x).length=N) (u : ℕ) (hu : u<N) (hu0 : ∀ x, (src x).getD u false=false)
    (fan : FanInTwo C) (back : ReadsBack N C) (K : Finset (Fin C.gates.length))
    (mark : ∀ j ∈ K, reads (C.gates.get j) u ∨ ∃ i : Fin C.gates.length, i<j ∧
      reads (C.gates.get i) u ∧ ((C.gates.get i).op=.and ∨ (C.gates.get i).op=.not) ∧
      reads (C.gates.get j) (N+i.val)) :
    ∀ k ∈ toNat K, k < C.gates.length ∧
      collapses (fun x w => (run C.gates (src x)).getD w false) (N+k)
        (fun x => (run C.gates (src x)).getD (N+k) false) := by
  let W := fun (x : X) (w : ℕ) => (run C.gates (src x)).getD w false
  have raw (x : X) : W x u = false :=
    (run_input _ _ _ (by rw [hs]; exact hu)).trans (hu0 x)
  have atGate (j : Fin C.gates.length) : gateAt C j.val=C.gates.get j :=
    List.getD_eq_getElem _ _ j.isLt
  have ev (j : Fin C.gates.length) (x : X) :
      W x (N+j.val) = (C.gates.get j).op.eval ((C.gates.get j).inputs.map (W x)) := by
    simpa only [W,atGate j] using gv N C back (src x) (hs x) j.val j.isLt
  intro k hk
  obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hk
  refine ⟨j.isLt,?_⟩
  change collapses W (N+j.val) (fun x => W x (N+j.val))
  have same := funext (ev j)
  rw [same]
  have ok := fan (C.gates.get j) (List.get_mem _ _)
  have before (t : ℕ) (ht : t∈(C.gates.get j).inputs) : t<N+j.val :=
    back j.val j.isLt t (by rwa [atGate])
  have folded (w : ℕ) (b : Bool) (r : reads (C.gates.get j) w) (h : ∀ x, W x w=b) :=
    when_read W _ (N+j.val) w b (by simpa using ok.1) ok.2 before r h
  rcases mark j hj with direct | ⟨i,_,ri,oi,rj⟩
  · exact folded u false direct raw
  · have fi := fan (C.gates.get i) (List.get_mem _ _)
    obtain ⟨b,hb⟩ := dominant W _ u fi.2 ri oi raw
    exact folded (N+i.val) b rj (fun x => (ev i x).trans (hb x))
end PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
namespace PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
private theorem blank_dead_signed (P : Prop) (N : ℕ) (C : Circuit)
    (hc : FanInTwo C) (hm : P → Monotone2 C) (hb : ReadsBack N C)
    (j : ℕ) (hj : j < C.gates.length)
    (hdead : ∀ k < C.gates.length, N + j ∉ (gateAt C k).inputs) (ho : C.output ≠ N + j) :
    let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
    FanInTwo E ∧ (P → Monotone2 E) ∧ ReadsBack N E ∧ E.size = C.size ∧
      (∀ x : List Bool, x.length = N → E.eval x = C.eval x) ∧
      (∀ x : List Bool, x.length = N → (run E.gates x).getD (N + j) false = false) := by
  let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
  have hlen : E.gates.length = C.gates.length := by simp [E]
  have hg : ∀ k, gateAt E k = if k = j then ⟨GateOp.or, []⟩ else gateAt C k := by
    intro k
    simp only [gateAt, E, List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hk : k = j
    · subst hk; simp [hj]
    · simp [hk, Ne.symm hk]
  have hc' : FanInTwo E := by
    intro g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hc g h
    · subst h; simp
  have hm' : P → Monotone2 E := by
    intro hP g h
    rcases List.mem_or_eq_of_mem_set h with h | h
    · exact hm hP g h
    · subst h; simp
  have hb' : ReadsBack N E := by
    intro k hk i hi
    rw [hg] at hi
    split_ifs at hi with h
    · simp at hi
    · exact hb k (by rw [hlen] at hk; exact hk) i hi
  have agree : ∀ x : List Bool, x.length = N → ∀ i, i ≠ N + j →
      (run E.gates x).getD i false = (run C.gates x).getD i false := by
    intro x hx i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      by_cases hlo : i < N
      · rw [run_input _ _ _ (by omega), run_input _ _ _ (by omega)]
      by_cases hhi : N + C.gates.length ≤ i
      · rw [past _ _ _ (by rw [hlen]; omega), past _ _ _ (by omega)]
      have hk : i - N < C.gates.length := by omega
      have hik : i = N + (i - N) := by omega
      rw [hik, gv N E hb' x hx _ (by rw [hlen]; exact hk), gv N C hb x hx _ hk, hg,
        if_neg (by omega)]
      congr 1
      refine List.map_congr_left fun i' hi' => ih i' ?_ ?_
      · have := hb _ hk i' hi'; omega
      · rintro rfl; exact hdead _ hk hi'
  refine ⟨hc', hm', hb', hlen, fun x hx => agree x hx _ ho, fun x hx => ?_⟩
  change (run E.gates x).getD (N + j) false = false
  rw [gv N E hb' x hx j (by rw [hlen]; exact hj), hg, if_pos rfl]
  simp [GateOp.eval]
theorem finish_live {X : Type} (P : Prop) (M : ℕ) (y : X → List Bool)
    (hy : ∀ x, (y x).length = M) (f : X → Bool)
    (hnc : ¬ ∃ b : Bool, ∀ x, f x = b) (C : Circuit)
    (hg : ∀ g ∈ C.gates, Good P g) (hb : ReadsBack M C) (hf : ∀ x, C.eval (y x) = f x) :
    ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧ D.size ≤ C.size ∧
      (∀ x, D.eval (y x) = f x) ∧
      ∀ i : Fin D.gates.length, M + i.val ≠ D.output →
        ∃ j : Fin D.gates.length, i < j ∧ reads (D.gates.get j) (M + i.val) := by
  classical
  have hex : ∃ k, ∃ D : Circuit, (∀ g ∈ D.gates, Good P g) ∧ ReadsBack M D ∧
      D.size ≤ k ∧ ∀ x, D.eval (y x) = f x := ⟨C.size, C, hg, hb, le_rfl, hf⟩
  obtain ⟨D, hgood, hback, hsize, hval⟩ := Nat.find_spec hex
  have hmin0 : Nat.find hex ≤ C.size := Nat.find_min' hex ⟨C, hg, hb, le_rfl, hf⟩
  refine ⟨D, hgood, hback, hsize.trans hmin0, hval, ?_⟩
  intro i hout
  by_contra hn
  have dead : ∀ k < D.gates.length, M + i.val ∉ (gateAt D k).inputs := by
    intro k hk hpin
    have hh := hback k hk _ hpin
    have later : i < (⟨k, hk⟩ : Fin D.gates.length) := by
      change i.val < k
      omega
    have eqg : D.gates.get ⟨k, hk⟩ = gateAt D k := (List.getD_eq_getElem _ _ hk).symm
    have hgk : Good P (D.gates.get ⟨k, hk⟩) := hgood _ (List.getElem_mem hk)
    have hread : reads (D.gates.get ⟨k, hk⟩) (M + i.val) ↔
        M + i.val ∈ (D.gates.get ⟨k, hk⟩).inputs := by
      apply good_read
      exact hgk
    exact hn ⟨⟨k, hk⟩, later, hread.2 (by rwa [eqg])⟩
  let E : Circuit := ⟨D.gates.set i.val ⟨GateOp.or, []⟩, D.output⟩
  have hdf : FanInTwo D := by apply good_fan; exact hgood
  have hdm : P → Monotone2 D := by
    intro hP
    apply good_mono <;> assumption
  obtain ⟨hef, hem, _, hes, heq, hzero⟩ :=
    blank_dead_signed P M D hdf hdm hback i.val i.isLt dead hout.symm
  have heval (x : X) : E.eval (y x) = f x := (heq _ (hy x)).trans (hval x)
  have hmarked : ∀ j ∈ ({i.val} : Finset ℕ), j < E.gates.length ∧
      ((∃ b, ∀ x, (run E.gates (y x)).getD (M + j) false = b) ∨
       ∃ w < M + j, ∀ x, (run E.gates (y x)).getD (M + j) false =
         (run E.gates (y x)).getD w false) := by
    intro j hj
    rw [Finset.mem_singleton] at hj
    subst j
    exact ⟨by simpa [E] using i.isLt, Or.inl ⟨false, fun x => hzero _ (hy x)⟩⟩
  obtain ⟨J, hJg, hJb, hJs, hJv⟩ := engine P M M E y y hy hy {i.val} hef hem
    (fun w hw => Or.inr ⟨w, hw, fun _ => rfl⟩)
    (fun ⟨b, h⟩ => hnc ⟨b, fun x => (heval x).symm.trans (h x)⟩) hmarked
  have lower : Nat.find hex ≤ J.size :=
    Nat.find_min' hex ⟨J, hJg, hJb, le_rfl, fun x => (hJv x).trans (heval x)⟩
  rw [Finset.card_singleton] at hJs
  change E.size = D.size at hes
  omega
end PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
namespace PEqualNP.Outside.L_meta_25808_aux.Normal
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open scoped Classical
abbrev Active (C : Circuit) := readsIn C (Finset.range C.size)
theorem output_not_raw {n m : ℕ} {G : Fin n → Fin m → Bool} {C : Circuit} (rep : Represents G C)
    (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) : n+m≤C.output := by
  by_contra! small
  have readRaw (a c) : G a c=decide (C.output=a.val ∨ C.output=n+c.val) := by
    rw [←rep a c]
    change (Normalize.run C.gates (oneEach a c)).getD C.output false=_
    rw [Normalize.run_input _ _ _ (by rwa [Normalize.oneEach_length]),Normalize.oneEach_getD]
  by_cases l : C.output<n
  · obtain ⟨a,c,d,diff⟩ := horizontal
    apply diff
    rw [readRaw,readRaw]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]; omega
  · obtain ⟨a,b,c,diff⟩ := vertical
    have ha := a.isLt; have hb := b.isLt
    apply diff
    rw [readRaw,readRaw]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]; omega
theorem wire_positive {C : Circuit} {w j : ℕ} (hj : j<C.size) (hw : w∈(gateAt C j).inputs) :
    0<Active C w := lt_of_lt_of_le (List.count_pos_iff.mpr hw) (Finset.single_le_sum
      (f:=fun k => (gateAt C k).inputs.count w) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj))
theorem normalized {n m : ℕ} {G : Fin n → Fin m → Bool} (C : Circuit) (fan : FanInTwo C)
    (rep : Represents G C) (horizontal : ∃ a c d, G a c ≠ G a d) (vertical : ∃ a b c, G a c ≠ G b c) :
    ∃ D : Circuit, D.size≤C.size ∧ Represents G D ∧ ReadsBack (n+m) D ∧
      (∀ g∈D.gates, ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1)) ∧
      0<D.size ∧ D.output+1=n+m+D.size ∧ (∀ j<D.size, j+1<D.size → 0<Active D (n+m+j)) := by
  classical
  let N := n+m
  let y (p : Fin n × Fin m) := oneEach p.1 p.2
  let f (p : Fin n × Fin m) := G p.1 p.2
  have len (p) : (y p).length=N := Normalize.oneEach_length _ _
  have nc : ¬∃ b : Bool, ∀ p, f p=b := by
    rintro ⟨z,h⟩
    obtain ⟨a,b,c,ne⟩ := vertical
    exact ne ((h (a,c)).trans (h (b,c)).symm)
  obtain ⟨E,shape,back,sz,values⟩ := Normalize.engine False N N C y y len len ∅ fan False.elim
    (fun w hw => Or.inr ⟨w,hw,fun _ => rfl⟩)
    (fun ⟨z,h⟩ => nc ⟨z,fun p => (rep p.1 p.2).symm.trans (h p)⟩) (by simp)
  have esize : E.size≤C.size := by simpa only [Finset.card_empty,Nat.add_zero] using sz
  obtain ⟨D,dshape,db,ds,dv,live⟩ := Normalize.finish_live False N y len f nc E shape back
    (fun p => (values p).trans (rep p.1 p.2))
  have dr : Represents G D := fun a c => dv (a,c)
  have out := output_not_raw dr horizontal vertical
  have bound : D.output<N+D.size := by
    by_contra! high
    apply nc; refine ⟨false,?_⟩; intro p
    rw [←dv p]
    change (Normalize.run D.gates (y p)).getD D.output false=false
    exact Normalize.past _ _ _ (by rw [len]; exact high)
  have pos : 0<D.size := by dsimp [N] at bound; omega
  let last : Fin D.gates.length := ⟨D.size-1,by change D.size-1<D.size; omega⟩
  have final : N+last.val=D.output := by
    by_contra no
    obtain ⟨j,lt,_⟩ := live last no
    have hj := j.isLt
    change D.size-1<j.val at lt
    change j.val<D.size at hj
    omega
  have lastEq : D.output+1=N+D.size := by change N+(D.size-1)=D.output at final; omega
  refine ⟨D,ds.trans esize,dr,db,?_,pos,lastEq,?_⟩
  · intro g hg
    rcases (dshape g hg).1 with ⟨op,a,h⟩|⟨op,a,b,_,h⟩
    · exact Or.inr ⟨op,by simp [h]⟩
    · exact Or.inl ⟨op,by simp [h]⟩
  · intro j hj nonfinal
    have ne : N+j≠D.output := by omega
    obtain ⟨p,_,usage⟩ := live ⟨j,hj⟩ ne
    have ray : (D.gates.get p)=gateAt D p.val := (List.getD_eq_getElem _ _ p.isLt).symm
    change Normalize.reads (D.gates.get p) (N+j) at usage
    rw [ray] at usage
    apply wire_positive p.isLt
    rcases usage with ⟨_,h⟩|⟨_,h⟩
    · cases l : (gateAt D p.val).inputs with
      | nil => simp [l] at h
      | cons a tail =>
        simp [l] at h
        exact List.mem_cons.mpr (Or.inl h.symm)
    · exact h
end PEqualNP.Outside.L_meta_25808_aux.Normal
namespace PEqualNP.Outside.L_meta_25808_aux.Slots
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
lemma list_sum_count {α : Type*} [DecidableEq α] (l : List α) (S : Finset α)
    (hS : ∀ a ∈ l, a ∈ S) :
    ∑ a ∈ S, l.count a = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    have hx : x ∈ S := hS x (by simp)
    have hxs : ∀ a ∈ xs, a ∈ S := fun a ha => hS a (by simp [ha])
    simp only [List.count_cons, List.length_cons, beq_iff_eq]
    have hsum : (∑ a ∈ S, (xs.count a + if x = a then 1 else 0)) =
        (∑ a ∈ S, xs.count a) + ∑ a ∈ S, (if x = a then 1 else 0) := Finset.sum_add_distrib
    rw [hsum, ih hxs]
    have h1 : (∑ a ∈ S, if x = a then 1 else 0) = 1 := by
      rw [Finset.sum_ite_eq]; simp [hx]
    omega
lemma list_sum_count_eq_countP {α : Type*} [DecidableEq α] (l : List α) (S : Finset α) :
    ∑ a ∈ S, l.count a = l.countP (fun a => decide (a ∈ S)) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, List.countP_cons, beq_iff_eq]
    rw [Finset.sum_add_distrib, ih]
    by_cases hx : x ∈ S
    · have h1 : (∑ a ∈ S, if x = a then 1 else 0) = 1 := by
        rw [Finset.sum_ite_eq]; simp [hx]
      simp [hx, h1]
    · have h1 : (∑ a ∈ S, if x = a then 1 else 0) = 0 := by
        rw [Finset.sum_ite_eq]; simp [hx]
      simp [hx, h1]
lemma readsIn_union {C : Circuit} {G₁ G₂ : Finset ℕ} (hdisj : Disjoint G₁ G₂) (w : ℕ) :
    readsIn C (G₁ ∪ G₂) w = readsIn C G₁ w + readsIn C G₂ w := by
  unfold readsIn
  exact Finset.sum_union hdisj
lemma readsIn_mono {C : Circuit} {G₁ G₂ : Finset ℕ} (hsub : G₁ ⊆ G₂) (w : ℕ) :
    readsIn C G₁ w ≤ readsIn C G₂ w := by
  unfold readsIn
  exact Finset.sum_le_sum_of_subset hsub
lemma readsIn_pos_iff {C : Circuit} {G : Finset ℕ} {w : ℕ} :
    0 < readsIn C G w ↔ ∃ k ∈ G, w ∈ (gateAt C k).inputs := by
  unfold readsIn
  rw [Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  constructor
  · rintro ⟨k, hk, hpos⟩
    exact ⟨k, hk, List.count_pos_iff.mp hpos⟩
  · rintro ⟨k, hk, hmem⟩
    exact ⟨k, hk, List.count_pos_iff.mpr hmem⟩
lemma readsIn_zero_iff {C : Circuit} {G : Finset ℕ} {w : ℕ} :
    readsIn C G w = 0 ↔ ∀ k ∈ G, w ∉ (gateAt C k).inputs := by
  constructor
  · intro h0 k hk hmem
    have hpos : 0 < readsIn C G w := readsIn_pos_iff.mpr ⟨k, hk, hmem⟩
    omega
  · intro hall
    by_contra hne
    rcases readsIn_pos_iff.mp (Nat.pos_of_ne_zero hne) with ⟨k, hk, hmem⟩
    exact hall k hk hmem
lemma sum_readsIn_eq_sum_countP (C : Circuit) (G S : Finset ℕ) :
    ∑ w ∈ S, readsIn C G w = ∑ k ∈ G, (gateAt C k).inputs.countP (fun w => decide (w ∈ S)) := by
  unfold readsIn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  exact list_sum_count_eq_countP (gateAt C k).inputs S
lemma sum_readsIn_all {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (G : Finset ℕ)
    (hG : G ⊆ Finset.range C.size) :
    ∑ w ∈ Finset.range (n + C.size), readsIn C G w = ∑ k ∈ G, (gateAt C k).inputs.length := by
  unfold readsIn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply list_sum_count
  intro w hw
  have hk_lt : k < C.gates.length := Finset.mem_range.mp (hG hk)
  have hw_lt : w < n + k := hRB k hk_lt w hw
  exact Finset.mem_range.mpr (by change w < n + C.gates.length; omega)
def subWires (n : ℕ) (C : Circuit) (G W : Finset ℕ) (v : ℕ) : Finset ℕ :=
  if v ∈ W then
    if n ≤ v ∧ v - n ∈ G then
      insert v (((gateAt C (v - n)).inputs.toFinset.filter (· < v)).attach.biUnion
        (fun w => subWires n C G W w.1))
    else {v}
  else ∅
termination_by v
decreasing_by
  exact (Finset.mem_filter.mp w.2).2
lemma subWires_unfold (n : ℕ) (C : Circuit) (G W : Finset ℕ) (v : ℕ) :
    subWires n C G W v =
      if v ∈ W then
        if n ≤ v ∧ v - n ∈ G then
          insert v (((gateAt C (v - n)).inputs.toFinset.filter (· < v)).biUnion (fun w => subWires n C G W w))
        else {v}
      else ∅ := by
  conv_lhs => rw [subWires]
  split_ifs <;> try rfl
  congr 1; ext x; simp
lemma subWires_subset {n : ℕ} {C : Circuit} {G W : Finset ℕ} (v : ℕ) :
    subWires n C G W v ⊆ W ∧ ∀ x ∈ subWires n C G W v, x ≤ v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    rw [subWires_unfold]
    by_cases hv : v ∈ W
    · simp only [hv, ite_true]
      by_cases hk : n ≤ v ∧ v - n ∈ G
      · simp only [hk.1, hk.2, and_self, ite_true]
        constructor
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact hv
          · rcases Finset.mem_biUnion.mp hx' with ⟨w, hw, hxw⟩
            exact (ih w (Finset.mem_filter.mp hw).2).1 hxw
        · intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx'
          · exact le_rfl
          · rcases Finset.mem_biUnion.mp hx' with ⟨w, hw, hxw⟩
            have hlt := (Finset.mem_filter.mp hw).2
            have hle := (ih w hlt).2 x hxw
            omega
      · simp only [hk, ite_false]
        exact ⟨Finset.singleton_subset_iff.mpr hv, fun x hx => by rw [Finset.mem_singleton.mp hx]⟩
    · simp only [hv, ite_false]
      exact ⟨Finset.empty_subset _, fun _ hx => by simp at hx⟩
lemma mem_subWires_self {n : ℕ} {C : Circuit} {G W : Finset ℕ} {v : ℕ} (hv : v ∈ W) :
    v ∈ subWires n C G W v := by
  rw [subWires_unfold]
  simp only [hv, ite_true]
  by_cases hk : n ≤ v ∧ v - n ∈ G
  · simp only [hk.1, hk.2, and_self, ite_true, Finset.mem_insert, true_or]
  · simp only [hk, ite_false, Finset.mem_singleton]
lemma subWires_eq_of_gate {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size) {k : ℕ} (hk : k ∈ G) (hW : n + k ∈ W) :
    subWires n C G W (n + k) =
      insert (n + k) ((gateAt C k).inputs.toFinset.biUnion (fun w => subWires n C G W w)) := by
  rw [subWires_unfold]
  have h1 : n ≤ n + k := Nat.le_add_right n k
  simp only [hW, h1, Nat.add_sub_cancel_left, hk, and_self, ite_true]
  congr 1
  have hfilt : (gateAt C k).inputs.toFinset.filter (· < n + k) = (gateAt C k).inputs.toFinset := by
    apply Finset.filter_true_of_mem
    intro w hw
    exact hRB k (Finset.mem_range.mp (hG hk)) w (List.mem_toFinset.mp hw)
  rw [hfilt]
lemma subWires_eq_of_not_gate {n : ℕ} {C : Circuit} {G W : Finset ℕ} {v : ℕ}
    (hv : v ∈ W) (hng : ¬ (n ≤ v ∧ v - n ∈ G)) :
    subWires n C G W v = {v} := by
  rw [subWires_unfold]
  simp only [hv, hng, ite_true, ite_false]
lemma subWires_closed_down {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size) {v : ℕ} :
    ∀ {k : ℕ}, k ∈ G → n + k ∈ subWires n C G W v →
      ∀ w ∈ (gateAt C k).inputs, w ∈ W → w ∈ subWires n C G W v := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    intro k hk hnk w hw hwW
    by_cases hv : v ∈ W
    · by_cases hkg : n ≤ v ∧ v - n ∈ G
      · have hv_eq : v = n + (v - n) := by omega
        have hsub : subWires n C G W v =
            insert v ((gateAt C (v - n)).inputs.toFinset.biUnion (fun u => subWires n C G W u)) := by
          conv_lhs => rw [hv_eq]
          rw [subWires_eq_of_gate hRB hG hkg.2 (hv_eq ▸ hv), ← hv_eq]
        rw [hsub] at hnk ⊢
        rcases Finset.mem_insert.mp hnk with heq | hmem
        · have hk_eq : k = v - n := by omega
          subst hk_eq
          refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨w, List.mem_toFinset.mpr hw, ?_⟩)
          exact mem_subWires_self hwW
        · rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hnk_u⟩
          have hu_lt : u < v := by
            have h1 := hRB (v - n) (Finset.mem_range.mp (hG hkg.2)) u (List.mem_toFinset.mp hu)
            omega
          exact Finset.mem_insert_of_mem
            (Finset.mem_biUnion.mpr ⟨u, hu, ih u hu_lt hk hnk_u w hw hwW⟩)
      · rw [subWires_eq_of_not_gate hv hkg, Finset.mem_singleton] at hnk
        exfalso
        apply hkg
        rw [← hnk]
        exact ⟨Nat.le_add_right n k, by simpa using hk⟩
    · exfalso
      rw [subWires_unfold] at hnk
      simp [hv] at hnk
lemma mem_subWires_ne_has_parent {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size) {v x : ℕ} (hx : x ∈ subWires n C G W v) (hne : x ≠ v) :
    ∃ k ∈ G, n + k ∈ subWires n C G W v ∧ x ∈ (gateAt C k).inputs := by
  induction v using Nat.strong_induction_on with
  | ind v ih =>
    have hv : v ∈ W := by
      by_contra hnv
      rw [subWires_unfold] at hx
      simp [hnv] at hx
    by_cases hkg : n ≤ v ∧ v - n ∈ G
    · have hv_eq : v = n + (v - n) := by omega
      have hsub : subWires n C G W v =
          insert v ((gateAt C (v - n)).inputs.toFinset.biUnion (fun u => subWires n C G W u)) := by
        conv_lhs => rw [hv_eq]
        rw [subWires_eq_of_gate hRB hG hkg.2 (hv_eq ▸ hv), ← hv_eq]
      rw [hsub] at hx
      rcases Finset.mem_insert.mp hx with rfl | hmem
      · exact absurd rfl hne
      · rcases Finset.mem_biUnion.mp hmem with ⟨u, hu, hxu⟩
        by_cases hxu_eq : x = u
        · subst hxu_eq
          refine ⟨v - n, hkg.2, ?_, List.mem_toFinset.mp hu⟩
          rw [← hv_eq]
          exact mem_subWires_self hv
        · have hu_lt : u < v := by
            have h1 := hRB (v - n) (Finset.mem_range.mp (hG hkg.2)) u (List.mem_toFinset.mp hu)
            omega
          rcases ih u hu_lt hxu hxu_eq with ⟨k, hk, hnk_u, hxk⟩
          refine ⟨k, hk, ?_, hxk⟩
          rw [hsub]
          exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨u, hu, hnk_u⟩)
    · rw [subWires_eq_of_not_gate hv hkg, Finset.mem_singleton] at hx
      exact absurd hx hne
lemma subWires_disjoint {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {G W : Finset ℕ}
    (hG : G ⊆ Finset.range C.size)
    (hread1 : ∀ w ∈ W, readsIn C G w ≤ 1)
    {v₁ v₂ : ℕ} (h12 : v₁ ∉ subWires n C G W v₂) (h21 : v₂ ∉ subWires n C G W v₁) :
    Disjoint (subWires n C G W v₁) (subWires n C G W v₂) := by
  rw [Finset.disjoint_left]
  intro x₀ hx₁ hx₂
  set I := subWires n C G W v₁ ∩ subWires n C G W v₂
  have hIne : I.Nonempty := ⟨x₀, Finset.mem_inter.mpr ⟨hx₁, hx₂⟩⟩
  set x := I.max' hIne
  have hxI : x ∈ I := Finset.max'_mem I hIne
  rcases Finset.mem_inter.mp hxI with ⟨hxm1, hxm2⟩
  have hne1 : x ≠ v₁ := fun h => h12 (h ▸ hxm2)
  have hne2 : x ≠ v₂ := fun h => h21 (h ▸ hxm1)
  rcases mem_subWires_ne_has_parent hRB hG hxm1 hne1 with ⟨k₁, hk₁, hnk1, hxk1⟩
  rcases mem_subWires_ne_has_parent hRB hG hxm2 hne2 with ⟨k₂, hk₂, hnk2, hxk2⟩
  have hxW : x ∈ W := (subWires_subset v₁).1 hxm1
  have hr1 : readsIn C G x ≤ 1 := hread1 x hxW
  have hk_eq : k₁ = k₂ := by
    by_contra hkne
    have hsub : ({k₁, k₂} : Finset ℕ) ⊆ G := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl <;> assumption
    have hle : (gateAt C k₁).inputs.count x + (gateAt C k₂).inputs.count x ≤ readsIn C G x := by
      have h1 := readsIn_mono (C := C) hsub x
      rw [show readsIn C {k₁, k₂} x = (gateAt C k₁).inputs.count x + (gateAt C k₂).inputs.count x from by
        unfold readsIn; exact Finset.sum_pair hkne] at h1
      exact h1
    have c1 : 0 < (gateAt C k₁).inputs.count x := List.count_pos_iff.mpr hxk1
    have c2 : 0 < (gateAt C k₂).inputs.count x := List.count_pos_iff.mpr hxk2
    omega
  subst hk_eq
  have hnkI : n + k₁ ∈ I := Finset.mem_inter.mpr ⟨hnk1, hnk2⟩
  have hle_max : n + k₁ ≤ x := Finset.le_max' I (n + k₁) hnkI
  have hlt : x < n + k₁ := hRB k₁ (Finset.mem_range.mp (hG hk₁)) x hxk1
  omega
def extSlots (C : Circuit) (G W : Finset ℕ) : ℕ :=
  ∑ k ∈ G, (gateAt C k).inputs.countP (fun w => decide (w ∉ W))
structure CutTree (n : ℕ) (C : Circuit) (ordinaryGates once : Finset ℕ)
    (G S : Finset ℕ) (r : ℕ) : Prop where
  G_sub : G ⊆ ordinaryGates
  S_sub : S ⊆ once
  r_mem : r ∈ S ∪ G.image (fun k => n + k)
  r_reads : readsIn C G r = 0
  nonroot : ∀ w ∈ S ∪ G.image (fun k => n + k), w ≠ r →
    readsIn C G w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w
lemma subWires_mem_partition {n : ℕ} {C : Circuit} {G S W : Finset ℕ}
    (_hS : ∀ w ∈ S, w < n) (hW : W = S ∪ G.image (fun k => n + k)) (v : ℕ) :
    let Wv := subWires n C G W v
    let Gv := G.filter (fun k => n + k ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    Wv = Sv ∪ Gv.image (fun k => n + k) := by
  intro Wv Gv Sv
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_image, Sv, Gv]
  constructor
  · intro hx
    have hxW : x ∈ W := (subWires_subset v).1 hx
    rw [hW] at hxW
    rcases Finset.mem_union.mp hxW with hxS | hxG
    · exact Or.inl ⟨hxS, hx⟩
    · rcases Finset.mem_image.mp hxG with ⟨k, hk, rfl⟩
      exact Or.inr ⟨k, ⟨hk, hx⟩, rfl⟩
  · rintro (⟨_, hx⟩ | ⟨k, ⟨_, hx⟩, rfl⟩)
    · exact hx
    · exact hx
lemma subWires_cutTree {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} (hG : G ⊆ ordinaryGates) (hS : S ⊆ once)
    (hread_le : ∀ w ∈ S ∪ G.image (fun k => n + k), readsIn C G w ≤ 1)
    (hnonroot_all : ∀ w ∈ S ∪ G.image (fun k => n + k),
      readsIn C G w = 1 → readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    {v : ℕ} (hv : v ∈ S ∪ G.image (fun k => n + k)) :
    let W := S ∪ G.image (fun k => n + k)
    let Wv := subWires n C G W v
    let Gv := G.filter (fun k => n + k ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    CutTree n C ordinaryGates once Gv Sv v := by
  intro W Wv Gv Sv
  have hWv_eq : Wv = Sv ∪ Gv.image (fun k => n + k) :=
    subWires_mem_partition (fun w hw => honce w (hS hw)) rfl v
  have hGv_sub : Gv ⊆ G := Finset.filter_subset _ _
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hG hord
  refine ⟨Finset.Subset.trans hGv_sub hG, Finset.Subset.trans (Finset.filter_subset _ _) hS,
    ?_, ?_, ?_⟩
  · rw [← hWv_eq]; exact mem_subWires_self hv
  · rw [readsIn_zero_iff]
    intro k hk hmem
    have hnk_mem : n + k ∈ Wv := (Finset.mem_filter.mp hk).2
    have hle : n + k ≤ v := (subWires_subset v).2 (n + k) hnk_mem
    have hlt : v < n + k := hRB k (Finset.mem_range.mp (hG_range (hGv_sub hk))) v hmem
    omega
  · intro w hw hne
    rw [← hWv_eq] at hw
    rcases mem_subWires_ne_has_parent hRB hG_range hw hne with ⟨k, hk, hnk, hwk⟩
    have hpos : 0 < readsIn C Gv w := readsIn_pos_iff.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hnk⟩, hwk⟩
    have hle1 : readsIn C Gv w ≤ readsIn C G w := readsIn_mono hGv_sub w
    have hwW : w ∈ W := (subWires_subset v).1 hw
    have hr1 : readsIn C G w ≤ 1 := hread_le w hwW
    have hGv1 : readsIn C Gv w = 1 := by omega
    have hG1 : readsIn C G w = 1 := by omega
    have hnr := hnonroot_all w hwW hG1
    exact ⟨hGv1, hnr.1, hnr.2⟩
lemma cutTree_of_ext0 {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    (he0 : extSlots C G (S ∪ G.image (fun k => n + k)) = 0) :
    let W := S ∪ G.image (fun k => n + k)
    G ⊆ ordinaryGates ∧ r ∈ W ∧ readsIn C G r = 0 ∧
    (∀ b ∈ (∅ : Finset ℕ), b ∉ W ∧ b < r ∧ readsIn C G b = 1) ∧
    (∀ j ∈ G, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ W ∨ w ∈ (∅ : Finset ℕ)) ∧
    (∀ w ∈ W, w ≠ r → readsIn C G w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w) := by
  intro W
  change extSlots C G W = 0 at he0
  refine ⟨hct.G_sub, hct.r_mem, hct.r_reads, fun _ hb => by simp at hb, ?_, hct.nonroot⟩
  intro j hj
  have hbj := hbin j (hct.G_sub hj)
  refine ⟨hbj.1, hbj.2, fun w hw => Or.inl ?_⟩
  by_contra hnw
  have hpos : 0 < (gateAt C j).inputs.countP (fun u => decide (u ∉ W)) :=
    List.countP_pos_iff.mpr ⟨w, hw, by simp [hnw]⟩
  have hle : (gateAt C j).inputs.countP (fun u => decide (u ∉ W)) ≤ extSlots C G W :=
    Finset.single_le_sum (f := fun k => (gateAt C k).inputs.countP (fun u => decide (u ∉ W)))
      (fun _ _ => Nat.zero_le _) hj
  omega
lemma cutTree_of_ext1 {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    (_honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    (he1 : extSlots C G (S ∪ G.image (fun k => n + k)) = 1) :
    let W := S ∪ G.image (fun k => n + k)
    ∃ b : ℕ,
      G ⊆ ordinaryGates ∧ r ∈ W ∧ readsIn C G r = 0 ∧
      (∀ x ∈ ({b} : Finset ℕ), x ∉ W ∧ x < r ∧ readsIn C G x = 1) ∧
      (∀ j ∈ G, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
        (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ W ∨ w ∈ ({b} : Finset ℕ)) ∧
      (∀ w ∈ W, w ≠ r → readsIn C G w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w) := by
  intro W
  change extSlots C G W = 1 at he1
  have hpos_sum : 0 < ∑ k ∈ G, (gateAt C k).inputs.countP (fun u => decide (u ∉ W)) := by
    change 0 < extSlots C G W; omega
  rcases Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _) |>.mp hpos_sum with ⟨k0, hk0, hk0_pos⟩
  rcases List.countP_pos_iff.mp hk0_pos with ⟨b, hb_in, hb_out⟩
  have hbW : b ∉ W := by simpa using hb_out
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  have hW_le_r : ∀ w ∈ W, w ≤ r := by
    have hlt_max : ∀ m, ∀ x ∈ W, m = n + C.size - x → x ≤ r := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ihm =>
        intro x hx hm
        by_cases hxr : x = r
        · omega
        · have hr1' := (hct.nonroot x hx hxr).1
          rcases readsIn_pos_iff.mp (by omega : 0 < readsIn C G x) with ⟨k', hk', hxk'⟩
          have hlt' : x < n + k' := hRB k' (Finset.mem_range.mp (hG_range hk')) x hxk'
          have hnk'_lt : n + k' < n + C.size := by
            have := Finset.mem_range.mp (hG_range hk'); omega
          have hnk'W : n + k' ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk')
          have hle' := ihm (n + C.size - (n + k')) (by omega) (n + k') hnk'W rfl
          omega
    intro w hw
    exact hlt_max (n + C.size - w) w hw rfl
  have hb_lt_r : b < r := by
    have h1 : b < n + k0 := hRB k0 (Finset.mem_range.mp (hG_range hk0)) b hb_in
    have h2 : n + k0 ≤ r := hW_le_r (n + k0) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk0))
    omega
  have hb_reads_le : readsIn C G b ≤ extSlots C G W := by
    unfold readsIn extSlots
    apply Finset.sum_le_sum
    intro k _
    have h1 : (gateAt C k).inputs.count b = (gateAt C k).inputs.countP (fun u => decide (u = b)) := by
      induction (gateAt C k).inputs with
      | nil => simp
      | cons a l ih =>
        simp only [List.count_cons, List.countP_cons, beq_iff_eq]
        by_cases h : a = b <;> simp [h, ih]
    rw [h1]
    apply List.countP_mono_left
    intro u _ hu
    have hub : u = b := by simpa using hu
    subst hub
    simpa using hbW
  have hb_reads_pos : 0 < readsIn C G b := readsIn_pos_iff.mpr ⟨k0, hk0, hb_in⟩
  have hb_reads : readsIn C G b = 1 := by omega
  have hall_out_eq_b : ∀ j ∈ G, ∀ w ∈ (gateAt C j).inputs, w ∉ W → w = b := by
    intro j hj w hw hnw
    by_contra hne
    have hle_sum : readsIn C G b + readsIn C G w ≤ extSlots C G W := by
      have hpair : ∑ u ∈ ({b, w} : Finset ℕ), readsIn C G u ≤ extSlots C G W := by
        rw [sum_readsIn_eq_sum_countP]
        unfold extSlots
        apply Finset.sum_le_sum
        intro k _
        apply List.countP_mono_left
        intro u _ hu
        have hu' : u = b ∨ u = w := by simpa using hu
        rcases hu' with rfl | rfl
        · simpa using hbW
        · simpa using hnw
      rw [Finset.sum_pair (Ne.symm hne)] at hpair
      exact hpair
    have hw_pos : 0 < readsIn C G w := readsIn_pos_iff.mpr ⟨j, hj, hw⟩
    omega
  refine ⟨b, hct.G_sub, hct.r_mem, hct.r_reads, ?_, ?_, hct.nonroot⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact ⟨hbW, hb_lt_r, hb_reads⟩
  · intro j hj
    have hbj := hbin j (hct.G_sub hj)
    refine ⟨hbj.1, hbj.2, fun w hw => ?_⟩
    by_cases hwW : w ∈ W
    · exact Or.inl hwW
    · exact Or.inr (Finset.mem_singleton.mpr (hall_out_eq_b j hj w hw hwW))
lemma cutTree_W_eq_subWires_r {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r) :
    subWires n C G (S ∪ G.image (fun k => n + k)) r = S ∪ G.image (fun k => n + k) := by
  set W := S ∪ G.image (fun k => n + k)
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  apply Finset.Subset.antisymm (subWires_subset r).1
  have hdown : ∀ (m : ℕ) (w : ℕ), w ∈ W → n + C.size - w = m → w ∈ subWires n C G W r := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro w hw hm
      by_cases hwr : w = r
      · subst hwr; exact mem_subWires_self hct.r_mem
      · have hr1 := (hct.nonroot w hw hwr).1
        rcases readsIn_pos_iff.mp (by omega : 0 < readsIn C G w) with ⟨k, hk, hwk⟩
        have hlt : w < n + k := hRB k (Finset.mem_range.mp (hG_range hk)) w hwk
        have hnk_lt : n + k < n + C.size := by
          have := Finset.mem_range.mp (hG_range hk); omega
        have hnkW : n + k ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
        have hnk_in : n + k ∈ subWires n C G W r := ih (n + C.size - (n + k)) (by omega) (n + k) hnkW rfl
        exact subWires_closed_down hRB hG_range hk hnk_in w hwk hw
  intro w hw
  exact hdown (n + C.size - w) w hw rfl
lemma cutTree_upper_split {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} {r v : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    (hv : v ∈ S ∪ G.image (fun k => n + k)) (hvr : v ≠ r) :
    let W := S ∪ G.image (fun k => n + k)
    let Wv := subWires n C G W v
    let Gv := G.filter (fun k => n + k ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    let G' := G \ Gv
    let S' := S \ Sv
    CutTree n C ordinaryGates once G' S' r ∧
    extSlots C G' (S' ∪ G'.image (fun k => n + k)) + extSlots C Gv Wv = extSlots C G W + 1 := by
  intro W Wv Gv Sv G' S'
  set W' := S' ∪ G'.image (fun k => n + k)
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  have hS_lt : ∀ w ∈ S, w < n := fun w hw => honce w (hct.S_sub hw)
  have hWv_eq : Wv = Sv ∪ Gv.image (fun k => n + k) := subWires_mem_partition hS_lt rfl v
  have hGv_sub : Gv ⊆ G := Finset.filter_subset _ _
  have hSv_sub : Sv ⊆ S := Finset.filter_subset _ _
  have hW'_eq : W' = W \ Wv := by
    ext x
    simp only [W', W, Finset.mem_union, Finset.mem_sdiff, Finset.mem_image, G', S', Gv, Sv,
      Finset.mem_filter]
    constructor
    · rintro (⟨hxS, hnx⟩ | ⟨k, ⟨hkG, hnk⟩, rfl⟩)
      · exact ⟨Or.inl hxS, fun hx => hnx ⟨hxS, hx⟩⟩
      · exact ⟨Or.inr ⟨k, hkG, rfl⟩, fun hx => hnk ⟨hkG, hx⟩⟩
    · rintro ⟨hxS | ⟨k, hkG, rfl⟩, hnx⟩
      · exact Or.inl ⟨hxS, fun h => hnx h.2⟩
      · exact Or.inr ⟨k, ⟨hkG, fun h => hnx h.2⟩, rfl⟩
  have hread_le : ∀ w ∈ W, readsIn C G w ≤ 1 := by
    intro w hw
    by_cases hwr : w = r
    · subst hwr; rw [hct.r_reads]; exact Nat.zero_le 1
    · rw [(hct.nonroot w hw hwr).1]
  have hsub_ct : CutTree n C ordinaryGates once Gv Sv v :=
    subWires_cutTree hRB hord honce hct.G_sub hct.S_sub hread_le
      (fun w hw hr1 => by
        have hne : w ≠ r := fun h => by subst h; rw [hct.r_reads] at hr1; omega
        have := hct.nonroot w hw hne
        exact ⟨this.2.1, this.2.2⟩) hv
  have hr_notin_Wv : r ∉ Wv := by
    intro hrWv
    have hle : r ≤ v := (subWires_subset v).2 r hrWv
    have hlt_v_r : v < r := by
      have hr1 := (hct.nonroot v hv hvr).1
      have hmax : ∀ (m : ℕ) (x : ℕ), x ∈ W → x ≠ r → n + C.size - x = m → x < r := by
        intro m
        induction m using Nat.strong_induction_on with
        | ind m ih =>
          intro x hx hxr hm
          have hx1 := (hct.nonroot x hx hxr).1
          rcases readsIn_pos_iff.mp (by omega : 0 < readsIn C G x) with ⟨k, hk, hxk⟩
          have hlt1 : x < n + k := hRB k (Finset.mem_range.mp (hG_range hk)) x hxk
          have hnk_lt : n + k < n + C.size := by
            have := Finset.mem_range.mp (hG_range hk); omega
          have hnkW : n + k ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
          by_cases hnkr : n + k = r
          · omega
          · have hlt2 := ih (n + C.size - (n + k)) (by omega) (n + k) hnkW hnkr rfl
            omega
      exact hmax (n + C.size - v) v hv hvr rfl
    omega
  have hdisjG : Disjoint G' Gv := Finset.sdiff_disjoint
  have hunionG : G' ∪ Gv = G := Finset.sdiff_union_of_subset hGv_sub
  have hGv_no_read_W' : ∀ w ∈ W', readsIn C Gv w = 0 := by
    intro w hw'
    rw [hW'_eq] at hw'
    rcases Finset.mem_sdiff.mp hw' with ⟨hwW, hnwv⟩
    rw [readsIn_zero_iff]
    intro k hk hwk
    rcases Finset.mem_filter.mp hk with ⟨hkG, hnkWv⟩
    exact hnwv (subWires_closed_down hRB hG_range hkG hnkWv w hwk hwW)
  have hct' : CutTree n C ordinaryGates once G' S' r := by
    refine ⟨Finset.Subset.trans Finset.sdiff_subset hct.G_sub,
      Finset.Subset.trans Finset.sdiff_subset hct.S_sub, ?_, ?_, ?_⟩
    · change r ∈ W'; rw [hW'_eq]; exact Finset.mem_sdiff.mpr ⟨hct.r_mem, hr_notin_Wv⟩
    · have hle : readsIn C G' r ≤ readsIn C G r :=
        readsIn_mono (C := C) (Finset.sdiff_subset (s := G) (t := Gv)) r
      rw [hct.r_reads] at hle; omega
    · intro w hw' hne
      change w ∈ W' at hw'
      have htot := readsIn_union (C := C) hdisjG w
      rw [hunionG] at htot
      have hwW : w ∈ W := (Finset.mem_sdiff.mp (hW'_eq ▸ hw')).1
      have hnr := hct.nonroot w hwW hne
      have h0 := hGv_no_read_W' w hw'
      exact ⟨by omega, hnr.2.1, hnr.2.2⟩
  refine ⟨hct', ?_⟩
  have hext_Gv : ∀ k ∈ Gv,
      (gateAt C k).inputs.countP (fun w => decide (w ∉ Wv)) =
      (gateAt C k).inputs.countP (fun w => decide (w ∉ W)) := by
    intro k hk
    rcases Finset.mem_filter.mp hk with ⟨hkG, hnkWv⟩
    apply List.countP_congr
    intro w hw
    have hiff : w ∈ Wv ↔ w ∈ W :=
      ⟨fun h => (subWires_subset v).1 h, fun h => subWires_closed_down hRB hG_range hkG hnkWv w hw h⟩
    simp [hiff]
  have hG'_read_Wv : ∀ k ∈ G', ∀ w ∈ (gateAt C k).inputs, w ∈ Wv → w = v := by
    intro k hk w hw hwWv
    by_contra hne
    have hr_sub : readsIn C Gv w = 1 := (hsub_ct.nonroot w (hWv_eq ▸ hwWv) hne).1
    have hr_pos : 0 < readsIn C G' w := readsIn_pos_iff.mpr ⟨k, hk, hw⟩
    have htot := readsIn_union (C := C) hdisjG w
    rw [hunionG] at htot
    have hle1 : readsIn C G w ≤ 1 := hread_le w ((subWires_subset v).1 hwWv)
    omega
  have hext_G' : ∀ k ∈ G',
      (gateAt C k).inputs.countP (fun w => decide (w ∉ W')) =
      (gateAt C k).inputs.countP (fun w => decide (w ∉ W)) + (gateAt C k).inputs.count v := by
    intro k hk
    have hsplit : ∀ l : List ℕ, (∀ w ∈ l, w ∈ Wv → w = v) →
        l.countP (fun w => decide (w ∉ W')) =
        l.countP (fun w => decide (w ∉ W)) + l.count v := by
      intro l hl
      induction l with
      | nil => simp
      | cons a xs ih =>
        have hxs := ih (fun w hw => hl w (by simp [hw]))
        simp only [List.countP_cons, List.count_cons, beq_iff_eq]
        rw [hxs]
        by_cases haW : a ∈ W
        · by_cases haWv : a ∈ Wv
          · have hav : a = v := hl a (by simp) haWv
            have haW' : a ∉ W' := by rw [hW'_eq, Finset.mem_sdiff]; intro h; exact h.2 haWv
            have hd1 : decide (a ∉ W') = true := by simp [haW']
            have hd2 : decide (a ∉ W) = false := by simp [haW]
            rw [hd1, hd2]; simp [hav]; omega
          · have haW' : a ∈ W' := by rw [hW'_eq]; exact Finset.mem_sdiff.mpr ⟨haW, haWv⟩
            have hav : a ≠ v := fun h => haWv (h ▸ mem_subWires_self hv)
            have hd1 : decide (a ∉ W') = false := by simp [haW']
            have hd2 : decide (a ∉ W) = false := by simp [haW]
            rw [hd1, hd2]; simp [hav]
        · have haW' : a ∉ W' := by rw [hW'_eq, Finset.mem_sdiff]; intro h; exact haW h.1
          have hav : a ≠ v := fun h => haW (h ▸ hv)
          have hd1 : decide (a ∉ W') = true := by simp [haW']
          have hd2 : decide (a ∉ W) = true := by simp [haW]
          rw [hd1, hd2]; simp [hav]; omega
    exact hsplit (gateAt C k).inputs (hG'_read_Wv k hk)
  have hv_reads_G' : readsIn C G' v = 1 := by
    have htot := readsIn_union (C := C) hdisjG v
    rw [hunionG, hsub_ct.r_reads, add_zero] at htot
    rw [← htot]
    exact (hct.nonroot v hv hvr).1
  unfold extSlots
  rw [Finset.sum_congr rfl hext_G', Finset.sum_add_distrib, Finset.sum_congr rfl hext_Gv]
  have h1 : (∑ k ∈ G', (gateAt C k).inputs.count v) = 1 := hv_reads_G'
  rw [h1]
  have h2 : (∑ k ∈ G', (gateAt C k).inputs.countP (fun w => decide (w ∉ W))) +
      (∑ k ∈ Gv, (gateAt C k).inputs.countP (fun w => decide (w ∉ W))) =
      ∑ k ∈ G, (gateAt C k).inputs.countP (fun w => decide (w ∉ W)) := by
    rw [← Finset.sum_union hdisjG, hunionG]
  omega
lemma cutTree_node_children {n : ℕ} {C : Circuit} {ordinaryGates once : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (_hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    (honce : ∀ w ∈ once, w < n)
    {G S : Finset ℕ} {r : ℕ} (hct : CutTree n C ordinaryGates once G S r)
    {k : ℕ} (hk : k ∈ G) (w₁ w₂ : ℕ) (hins : (gateAt C k).inputs = [w₁, w₂]) :
    let W := S ∪ G.image (fun j => n + j)
    let Wv := subWires n C G W (n + k)
    let Gv := G.filter (fun j => n + j ∈ Wv)
    let Sv := S.filter (fun w => w ∈ Wv)
    let W1 := subWires n C G W w₁
    let G1 := G.filter (fun j => n + j ∈ W1)
    let S1 := S.filter (fun w => w ∈ W1)
    let W2 := subWires n C G W w₂
    let G2 := G.filter (fun j => n + j ∈ W2)
    let S2 := S.filter (fun w => w ∈ W2)
    (Sv ⊆ S1 ∪ S2) ∧
    extSlots C Gv Wv =
      (if w₁ ∈ W then extSlots C G1 W1 else 1) + (if w₂ ∈ W then extSlots C G2 W2 else 1) := by
  intro W Wv Gv Sv W1 G1 S1 W2 G2 S2
  have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
  have hS_lt : ∀ w ∈ S, w < n := fun w hw => honce w (hct.S_sub hw)
  have hnkW : n + k ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
  have hWv_eq : Wv = insert (n + k) (W1 ∪ W2) := by
    dsimp only [Wv]
    rw [subWires_eq_of_gate hRB hG_range hk hnkW, hins]
    ext x
    simp [W1, W2]
  have hread_le : ∀ w ∈ W, readsIn C G w ≤ 1 := by
    intro w hw
    by_cases hwr : w = r
    · subst hwr; rw [hct.r_reads]; exact Nat.zero_le 1
    · rw [(hct.nonroot w hw hwr).1]
  have hSv_sub : Sv ⊆ S1 ∪ S2 := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxS, hxWv⟩
    rw [hWv_eq] at hxWv
    rcases Finset.mem_insert.mp hxWv with rfl | hx12
    · have := hS_lt (n + k) hxS; omega
    · rcases Finset.mem_union.mp hx12 with h1 | h2
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxS, h1⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxS, h2⟩)
  refine ⟨hSv_sub, ?_⟩
  have hnk_notin1 : n + k ∉ W1 := by
    intro h
    have hle := (subWires_subset w₁).2 (n + k) h
    have hlt := hRB k (Finset.mem_range.mp (hG_range hk)) w₁ (by rw [hins]; simp)
    omega
  have hnk_notin2 : n + k ∉ W2 := by
    intro h
    have hle := (subWires_subset w₂).2 (n + k) h
    have hlt := hRB k (Finset.mem_range.mp (hG_range hk)) w₂ (by rw [hins]; simp)
    omega
  have hdisj12 : Disjoint W1 W2 := by
    by_cases h1 : w₁ ∈ W
    · by_cases h2 : w₂ ∈ W
      · have hne12 : w₁ ≠ w₂ := by
          intro heq
          subst heq
          have h2c : 2 ≤ readsIn C G w₁ := by
            have hle := Finset.single_le_sum (f := fun j => (gateAt C j).inputs.count w₁)
              (fun _ _ => Nat.zero_le _) hk
            rw [hins] at hle
            simpa [readsIn] using hle
          have := hread_le w₁ h1
          omega
        have hn12 : w₁ ∉ W2 := by
          intro hmem
          rcases mem_subWires_ne_has_parent hRB hG_range hmem hne12 with ⟨k', hk', hnk', hwk'⟩
          have hkne : k' ≠ k := by
            intro heq; subst heq; exact hnk_notin2 hnk'
          have h2c : 2 ≤ readsIn C G w₁ := by
            have hsub : ({k, k'} : Finset ℕ) ⊆ G := by
              intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl <;> assumption
            have hle : (gateAt C k).inputs.count w₁ + (gateAt C k').inputs.count w₁ ≤ readsIn C G w₁ := by
              have h1 := readsIn_mono (C := C) hsub w₁
              rw [show readsIn C {k, k'} w₁ = (gateAt C k).inputs.count w₁ + (gateAt C k').inputs.count w₁ from by
                unfold readsIn; exact Finset.sum_pair hkne.symm] at h1
              exact h1
            have c1 : 0 < (gateAt C k).inputs.count w₁ := List.count_pos_iff.mpr (by rw [hins]; simp)
            have c2 : 0 < (gateAt C k').inputs.count w₁ := List.count_pos_iff.mpr hwk'
            omega
          have := hread_le w₁ h1
          omega
        have hn21 : w₂ ∉ W1 := by
          intro hmem
          rcases mem_subWires_ne_has_parent hRB hG_range hmem hne12.symm with ⟨k', hk', hnk', hwk'⟩
          have hkne : k' ≠ k := by
            intro heq; subst heq; exact hnk_notin1 hnk'
          have h2c : 2 ≤ readsIn C G w₂ := by
            have hsub : ({k, k'} : Finset ℕ) ⊆ G := by
              intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
              rcases hj with rfl | rfl <;> assumption
            have hle : (gateAt C k).inputs.count w₂ + (gateAt C k').inputs.count w₂ ≤ readsIn C G w₂ := by
              have h1 := readsIn_mono (C := C) hsub w₂
              rw [show readsIn C {k, k'} w₂ = (gateAt C k).inputs.count w₂ + (gateAt C k').inputs.count w₂ from by
                unfold readsIn; exact Finset.sum_pair hkne.symm] at h1
              exact h1
            have c1 : 0 < (gateAt C k).inputs.count w₂ := List.count_pos_iff.mpr (by rw [hins]; simp)
            have c2 : 0 < (gateAt C k').inputs.count w₂ := List.count_pos_iff.mpr hwk'
            omega
          have := hread_le w₂ h2
          omega
        exact subWires_disjoint hRB hG_range hread_le hn12 hn21
      · have hW2e : W2 = ∅ := by dsimp only [W2]; rw [subWires]; simp [h2]
        rw [hW2e]; exact Finset.disjoint_empty_right _
    · have hW1e : W1 = ∅ := by dsimp only [W1]; rw [subWires]; simp [h1]
      rw [hW1e]; exact Finset.disjoint_empty_left _
  have hGv_eq : Gv = insert k (G1 ∪ G2) := by
    ext j
    simp only [Gv, G1, G2, Finset.mem_filter, Finset.mem_insert, Finset.mem_union, hWv_eq]
    constructor
    · rintro ⟨hjG, hnj | h1 | h2⟩
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl ⟨hjG, h1⟩)
      · exact Or.inr (Or.inr ⟨hjG, h2⟩)
    · rintro (rfl | ⟨hjG, h1⟩ | ⟨hjG, h2⟩)
      · exact ⟨hk, Or.inl rfl⟩
      · exact ⟨hjG, Or.inr (Or.inl h1)⟩
      · exact ⟨hjG, Or.inr (Or.inr h2)⟩
  have hk_notin12 : k ∉ G1 ∪ G2 := by
    simp only [G1, G2, Finset.mem_union, Finset.mem_filter]
    rintro (⟨_, h1⟩ | ⟨_, h2⟩)
    · exact hnk_notin1 h1
    · exact hnk_notin2 h2
  have hdisjG12 : Disjoint G1 G2 := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    exact Finset.disjoint_left.mp hdisj12 (Finset.mem_filter.mp hj1).2 (Finset.mem_filter.mp hj2).2
  have hcongr1 : ∀ j ∈ G1,
      (gateAt C j).inputs.countP (fun w => decide (w ∉ Wv)) =
      (gateAt C j).inputs.countP (fun w => decide (w ∉ W1)) := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjG, hnjW1⟩
    apply List.countP_congr
    intro w hw
    have hiff : w ∈ Wv ↔ w ∈ W1 := by
      constructor
      · intro hwWv
        exact subWires_closed_down hRB hG_range hjG hnjW1 w hw ((subWires_subset (n + k)).1 hwWv)
      · intro hwW1
        rw [hWv_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hwW1)
    simp [hiff]
  have hcongr2 : ∀ j ∈ G2,
      (gateAt C j).inputs.countP (fun w => decide (w ∉ Wv)) =
      (gateAt C j).inputs.countP (fun w => decide (w ∉ W2)) := by
    intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hjG, hnjW2⟩
    apply List.countP_congr
    intro w hw
    have hiff : w ∈ Wv ↔ w ∈ W2 := by
      constructor
      · intro hwWv
        exact subWires_closed_down hRB hG_range hjG hnjW2 w hw ((subWires_subset (n + k)).1 hwWv)
      · intro hwW2
        rw [hWv_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hwW2)
    simp [hiff]
  have hk_term : (gateAt C k).inputs.countP (fun w => decide (w ∉ Wv)) =
      (if w₁ ∈ W then 0 else 1) + (if w₂ ∈ W then 0 else 1) := by
    rw [hins]
    have h1 : w₁ ∈ Wv ↔ w₁ ∈ W :=
      ⟨fun h => (subWires_subset (n + k)).1 h,
       fun h => subWires_closed_down hRB hG_range hk (mem_subWires_self hnkW) w₁ (by rw [hins]; simp) h⟩
    have h2 : w₂ ∈ Wv ↔ w₂ ∈ W :=
      ⟨fun h => (subWires_subset (n + k)).1 h,
       fun h => subWires_closed_down hRB hG_range hk (mem_subWires_self hnkW) w₂ (by rw [hins]; simp) h⟩
    simp only [List.countP_cons, List.countP_nil, h1, h2]
    by_cases hw1 : w₁ ∈ W <;> by_cases hw2 : w₂ ∈ W <;> simp [hw1, hw2]
  have hG1_empty : w₁ ∉ W → extSlots C G1 W1 = 0 := by
    intro hnw1
    have hW1e : W1 = ∅ := by dsimp only [W1]; rw [subWires_unfold]; simp [hnw1]
    have hG1e : G1 = ∅ := by ext j; simp [G1, hW1e]
    simp [extSlots, hG1e]
  have hG2_empty : w₂ ∉ W → extSlots C G2 W2 = 0 := by
    intro hnw2
    have hW2e : W2 = ∅ := by dsimp only [W2]; rw [subWires_unfold]; simp [hnw2]
    have hG2e : G2 = ∅ := by ext j; simp [G2, hW2e]
    simp [extSlots, hG2e]
  have hmain : extSlots C Gv Wv =
      ((if w₁ ∈ W then 0 else 1) + (if w₂ ∈ W then 0 else 1)) + (extSlots C G1 W1 + extSlots C G2 W2) := by
    unfold extSlots
    rw [hGv_eq, Finset.sum_insert hk_notin12, Finset.sum_union hdisjG12,
        Finset.sum_congr rfl hcongr1, Finset.sum_congr rfl hcongr2, hk_term]
  rw [hmain]
  by_cases hw1 : w₁ ∈ W <;> by_cases hw2 : w₂ ∈ W
  · simp [hw1, hw2]
  · rw [hG2_empty hw2]; simp [hw1, hw2]; omega
  · rw [hG1_empty hw1]; simp [hw1, hw2]
  · rw [hG1_empty hw1, hG2_empty hw2]; simp [hw1, hw2]
lemma cutTree_leaf_bound {n p c : ℕ} {C : Circuit} {ordinaryGates once H : Finset ℕ}
    (hRB : ReadsBack n C) (hord : ordinaryGates ⊆ Finset.range C.size)
    (hbin : ∀ k ∈ ordinaryGates,
      ((gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) ∧
      (gateAt C k).inputs.length = 2)
    (honce : ∀ w ∈ once, w < n)
    (hp_bd : ∀ S : Finset ℕ, S ⊆ once →
      (∃ (region : Finset ℕ) (root : ℕ),
        let wires := S ∪ region.image (fun k => n + k)
        let localReads := readsIn C region
        region ⊆ ordinaryGates ∧ root ∈ wires ∧ localReads root = 0 ∧
        (∀ b ∈ (∅ : Finset ℕ), b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
        (∀ j ∈ region, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
          (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ (∅ : Finset ℕ)) ∧
        (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)) →
      (S \ H).card ≤ p)
    (hc_bd : ∀ (S : Finset ℕ) (b : ℕ), S ⊆ once →
      (∃ (region : Finset ℕ) (root : ℕ),
        let wires := S ∪ region.image (fun k => n + k)
        let localReads := readsIn C region
        region ⊆ ordinaryGates ∧ root ∈ wires ∧ localReads root = 0 ∧
        (∀ x ∈ ({b} : Finset ℕ), x ∉ wires ∧ x < root ∧ localReads x = 1) ∧
        (∀ j ∈ region, ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
          (gateAt C j).inputs.length = 2 ∧ ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ ({b} : Finset ℕ)) ∧
        (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)) →
      (S \ H).card ≤ c)
    (e : ℕ) :
    ∀ (G S : Finset ℕ) (r : ℕ),
      CutTree n C ordinaryGates once G S r →
      extSlots C G (S ∪ G.image (fun k => n + k)) = e →
      (S \ H).card ≤ if e = 0 then p else c * (2 * e - 1) := by
  induction e using Nat.strong_induction_on with
  | ind e ih =>
    intro G S r hct he
    set W := S ∪ G.image (fun k => n + k)
    by_cases he0 : e = 0
    · subst he0
      simp only [ite_true]
      exact hp_bd S hct.S_sub ⟨G, r, cutTree_of_ext0 hbin hct he⟩
    · simp only [he0, ite_false]
      by_cases he1 : e = 1
      · subst he1
        rcases cutTree_of_ext1 hRB hord hbin honce hct he with ⟨b, hb⟩
        have hle := hc_bd S b hct.S_sub ⟨G, r, hb⟩
        simpa using hle
      · have he2 : 2 ≤ e := by omega
        have hread_le : ∀ w ∈ W, readsIn C G w ≤ 1 := by
          intro w hw
          by_cases hwr : w = r
          · subst hwr; rw [hct.r_reads]; exact Nat.zero_le 1
          · rw [(hct.nonroot w hw hwr).1]
        have hsub_ct : ∀ v ∈ W,
            CutTree n C ordinaryGates once
              (G.filter (fun j => n + j ∈ subWires n C G W v))
              (S.filter (fun w => w ∈ subWires n C G W v)) v :=
          fun v hv => subWires_cutTree hRB hord honce hct.G_sub hct.S_sub hread_le
            (fun w hw hr1 => by
              have hne : w ≠ r := fun h => by subst h; rw [hct.r_reads] at hr1; omega
              have := hct.nonroot w hw hne
              exact ⟨this.2.1, this.2.2⟩) hv
        set bad := G.filter (fun k => 2 ≤ extSlots C (G.filter (fun j => n + j ∈ subWires n C G W (n + k)))
          (subWires n C G W (n + k)))
        have hbad_ne : bad.Nonempty := by
          rcases Finset.mem_union.mp hct.r_mem with hrS | hrG
          · exfalso
            have hGe : G = ∅ := by
              have hsub_r := cutTree_W_eq_subWires_r hRB hord hct
              have hr_lt : r < n := honce r (hct.S_sub hrS)
              have hng : ¬ (n ≤ r ∧ r - n ∈ G) := fun h => by omega
              have hsing := subWires_eq_of_not_gate (C := C) hct.r_mem hng
              rw [hsing] at hsub_r
              ext k
              simp only [Finset.notMem_empty, iff_false]
              intro hk
              have hnk : n + k ∈ ({r} : Finset ℕ) := by
                rw [hsub_r]; exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
              rw [Finset.mem_singleton] at hnk
              omega
            rw [hGe] at he
            simp [extSlots] at he
            omega
          · rcases Finset.mem_image.mp hrG with ⟨kr, hkr, hkr_eq⟩
            refine ⟨kr, Finset.mem_filter.mpr ⟨hkr, ?_⟩⟩
            rw [hkr_eq, cutTree_W_eq_subWires_r hRB hord hct]
            have hGfilt : G.filter (fun j => n + j ∈ W) = G :=
              Finset.filter_true_of_mem (fun j hj => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hj))
            rw [hGfilt, he]
            exact he2
        set k0 := bad.min' hbad_ne
        have hk0_bad : k0 ∈ bad := Finset.min'_mem bad hbad_ne
        rcases Finset.mem_filter.mp hk0_bad with ⟨hk0G, hk0_ge2⟩
        have hlen2 : (gateAt C k0).inputs.length = 2 := (hbin k0 (hct.G_sub hk0G)).2
        rcases List.length_eq_two.mp hlen2 with ⟨w₁, w₂, hins⟩
        have hchildren := cutTree_node_children hRB hord hbin honce hct hk0G w₁ w₂ hins
        set Wv := subWires n C G W (n + k0)
        set Gv := G.filter (fun j => n + j ∈ Wv)
        set Sv := S.filter (fun w => w ∈ Wv)
        set W1 := subWires n C G W w₁
        set G1 := G.filter (fun j => n + j ∈ W1)
        set S1 := S.filter (fun w => w ∈ W1)
        set W2 := subWires n C G W w₂
        set G2 := G.filter (fun j => n + j ∈ W2)
        set S2 := S.filter (fun w => w ∈ W2)
        have hG_range : G ⊆ Finset.range C.size := Finset.Subset.trans hct.G_sub hord
        have he_child_le1 : ∀ w, w ∈ (gateAt C k0).inputs → w ∈ W →
            extSlots C (G.filter (fun j => n + j ∈ subWires n C G W w)) (subWires n C G W w) ≤ 1 := by
          intro w hw hwW
          rcases Finset.mem_union.mp hwW with hwS | hwG
          · have hw_lt : w < n := honce w (hct.S_sub hwS)
            have hng : ¬ (n ≤ w ∧ w - n ∈ G) := fun h => by omega
            have hsing := subWires_eq_of_not_gate (C := C) hwW hng
            have hGe : G.filter (fun j => n + j ∈ subWires n C G W w) = ∅ := by
              rw [hsing]; ext j; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
              intro h; omega
            rw [hGe]; simp [extSlots]
          · rcases Finset.mem_image.mp hwG with ⟨kw, hkw, rfl⟩
            have hlt : n + kw < n + k0 := hRB k0 (Finset.mem_range.mp (hG_range hk0G)) (n + kw) hw
            by_contra hge2
            have hkw_bad : kw ∈ bad := Finset.mem_filter.mpr ⟨hkw, by omega⟩
            have hmin : k0 ≤ kw := Finset.min'_le bad kw hkw_bad
            omega
        have he1_le : (if w₁ ∈ W then extSlots C G1 W1 else 1) ≤ 1 := by
          by_cases h1 : w₁ ∈ W
          · simp only [h1, ite_true]
            exact he_child_le1 w₁ (by rw [hins]; simp) h1
          · simp [h1]
        have he2_le : (if w₂ ∈ W then extSlots C G2 W2 else 1) ≤ 1 := by
          by_cases h2 : w₂ ∈ W
          · simp only [h2, ite_true]
            exact he_child_le1 w₂ (by rw [hins]; simp) h2
          · simp [h2]
        have hch2 : extSlots C Gv Wv =
            (if w₁ ∈ W then extSlots C G1 W1 else 1) + (if w₂ ∈ W then extSlots C G2 W2 else 1) :=
          hchildren.2
        have hkv2 : 2 ≤ extSlots C Gv Wv := hk0_ge2
        have hEv_eq2 : extSlots C Gv Wv = 2 := by omega
        have he1_eq1 : (if w₁ ∈ W then extSlots C G1 W1 else 1) = 1 := by omega
        have he2_eq1 : (if w₂ ∈ W then extSlots C G2 W2 else 1) = 1 := by omega
        have hS1_le : (S1 \ H).card ≤ c := by
          by_cases h1 : w₁ ∈ W
          · simp only [h1, ite_true] at he1_eq1
            have hW1_eq : W1 = S1 ∪ G1.image (fun j => n + j) :=
              subWires_mem_partition (fun w hw => honce w (hct.S_sub hw)) rfl w₁
            have hct1 := hsub_ct w₁ h1
            have hle := ih 1 (by omega) G1 S1 w₁ hct1 (by rw [← hW1_eq]; exact he1_eq1)
            simpa using hle
          · have hW1e : W1 = ∅ := by dsimp only [W1]; rw [subWires]; simp [h1]
            have hS1e : S1 = ∅ := by ext x; simp [S1, hW1e]
            simp [hS1e]
        have hS2_le : (S2 \ H).card ≤ c := by
          by_cases h2 : w₂ ∈ W
          · simp only [h2, ite_true] at he2_eq1
            have hW2_eq : W2 = S2 ∪ G2.image (fun j => n + j) :=
              subWires_mem_partition (fun w hw => honce w (hct.S_sub hw)) rfl w₂
            have hct2 := hsub_ct w₂ h2
            have hle := ih 1 (by omega) G2 S2 w₂ hct2 (by rw [← hW2_eq]; exact he2_eq1)
            simpa using hle
          · have hW2e : W2 = ∅ := by dsimp only [W2]; rw [subWires]; simp [h2]
            have hS2e : S2 = ∅ := by ext x; simp [S2, hW2e]
            simp [hS2e]
        have hSv_le : (Sv \ H).card ≤ 2 * c := by
          have hsub : Sv \ H ⊆ (S1 \ H) ∪ (S2 \ H) := by
            intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hxSv, hxH⟩
            rcases Finset.mem_union.mp (hchildren.1 hxSv) with h1 | h2
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h1, hxH⟩)
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h2, hxH⟩)
          have hle := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
          omega
        by_cases hvr : n + k0 = r
        · have hWv_all : Wv = W := by dsimp only [Wv]; rw [hvr]; exact cutTree_W_eq_subWires_r hRB hord hct
          have hSv_all : Sv = S := by
            dsimp only [Sv]; rw [hWv_all]
            exact Finset.filter_true_of_mem (fun w hw => Finset.mem_union_left _ hw)
          rw [← hSv_all]
          have h3 : 2 * c ≤ c * (2 * e - 1) := by
            have : 2 ≤ 2 * e - 1 := by omega
            calc 2 * c = c * 2 := Nat.mul_comm 2 c
              _ ≤ c * (2 * e - 1) := Nat.mul_le_mul_left c this
          omega
        · have hnk0W : n + k0 ∈ W := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk0G)
          have hup := cutTree_upper_split hRB hord honce hct hnk0W hvr
          set G' := G \ Gv
          set S' := S \ Sv
          have he' : extSlots C G' (S' ∪ G'.image (fun k => n + k)) = e - 1 := by
            have hup2 : extSlots C G' (S' ∪ G'.image (fun k => n + k)) + extSlots C Gv Wv = extSlots C G W + 1 :=
              hup.2
            have heW : extSlots C G W = e := he
            omega
          have hS'_le := ih (e - 1) (by omega) G' S' r hup.1 he'
          have hne0' : e - 1 ≠ 0 := by omega
          simp only [hne0', ite_false] at hS'_le
          have hS_split : S \ H ⊆ (S' \ H) ∪ (Sv \ H) := by
            intro x hx
            rcases Finset.mem_sdiff.mp hx with ⟨hxS, hxH⟩
            by_cases hxSv : x ∈ Sv
            · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxSv, hxH⟩)
            · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxS, hxSv⟩, hxH⟩)
          have hle_sum := le_trans (Finset.card_le_card hS_split) (Finset.card_union_le _ _)
          have hmul_eq : c * (2 * (e - 1) - 1) + 2 * c = c * (2 * e - 1) := by
            have h1 : 2 * (e - 1) - 1 + 2 = 2 * e - 1 := by omega
            calc c * (2 * (e - 1) - 1) + 2 * c
                = c * (2 * (e - 1) - 1) + c * 2 := by rw [Nat.mul_comm 2 c]
              _ = c * (2 * (e - 1) - 1 + 2) := (Nat.mul_add c _ _).symm
              _ = c * (2 * e - 1) := by rw [h1]
          omega
end PEqualNP.Outside.L_meta_25808_aux.Slots
namespace PEqualNP.Outside.L_meta_25808_aux
theorem weighted :
∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let gates := Finset.range C.size
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  let reads := PEqualNP.MetaComplexity.NestedCover.readsIn C gates
  let neg := @Finset.filter ℕ (fun k => (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (fun k => Classical.propDecidable ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not)) gates
  let special := ((Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)) ∪
    neg.image (fun k => n + k)
  let ordinaryGates := gates.filter (fun k => n + k ∉ special)
  let used := (Finset.range n).filter (fun w => 0 < reads w)
  let multiple := (Finset.range n).filter (fun w => 2 ≤ reads w)
  let once := (Finset.range n).filter (fun w => reads w = 1)
  let excess := C.size-neg.card+1-used.card
  let tree := fun (S E : Finset ℕ) => ∃ (region : Finset ℕ) (root : ℕ),
    let wires := S ∪ region.image (fun k => n + k)
    let localReads := PEqualNP.MetaComplexity.NestedCover.readsIn C region
    region ⊆ ordinaryGates ∧ root ∈ wires ∧ localReads root = 0 ∧
    (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
    (∀ j ∈ region,
      ((gate j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate j).inputs.length = 2 ∧ ∀ w ∈ (gate j).inputs, w ∈ wires ∨ w ∈ E) ∧
    (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧ reads w = 1 ∧ C.output ≠ w)
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      g.inputs.length = 2) ∨ (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack n C →
  0 < C.size → C.output + 1 = n + C.size →
  (∀ j < C.size, j + 1 < C.size → 0 < reads (n + j)) →
  ∀ (p c : ℕ) (H : Finset ℕ), 0 < p → H ⊆ Finset.range n →
    (∀ w < n, reads w = 0 → w ∈ H) →
    (∀ S : Finset ℕ, S ⊆ once → tree S ∅ → (S \ H).card ≤ p) →
    (∀ (S : Finset ℕ) (b : ℕ), S ⊆ once → tree S {b} → (S \ H).card ≤ c) →
    used.card ≤ C.size-neg.card+1 ∧
    n + (2*p-1)*multiple.card ≤
      (2*p+4*c)*excess + (p+2*c)*neg.card + p + H.card := by
  intro n C gates gate reads neg special ordinaryGates used multiple once excess tree
    hgates hRB hpos hout hnonout p c H hp hHsub hHunused hp_bd hc_bd
  classical
  have hgate_mem : ∀ k ∈ gates, gate k ∈ C.gates := by
    intro k hk
    have hklt : k < C.gates.length := Finset.mem_range.mp hk
    dsimp only [gate, PEqualNP.MetaComplexity.NestedCover.gateAt]
    rw [List.getD_eq_getElem _ _ hklt]
    exact List.getElem_mem hklt
  have hgate_len : ∀ k ∈ gates, (gate k).inputs.length = if k ∈ neg then 1 else 2 := by
    intro k hk
    have hgk := hgates (gate k) (hgate_mem k hk)
    by_cases hkn : k ∈ neg
    · simp only [hkn, ite_true]
      have hop : (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.not := (Finset.mem_filter.mp hkn).2
      rcases hgk with ⟨hor | hor, _⟩ | ⟨_, hlen⟩
      · rw [hop] at hor; cases hor
      · rw [hop] at hor; cases hor
      · exact hlen
    · simp only [hkn, ite_false]
      have hne : (gate k).op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := fun h =>
        hkn (Finset.mem_filter.mpr ⟨hk, h⟩)
      rcases hgk with ⟨_, hlen⟩ | ⟨hop, _⟩
      · exact hlen
      · exact absurd hop hne
  have hneg_sub : neg ⊆ gates := Finset.filter_subset _ _
  have hord_sub : ordinaryGates ⊆ gates := Finset.filter_subset _ _
  have hbin_ord : ∀ k ∈ ordinaryGates,
      ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
       (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
      (gate k).inputs.length = 2 := by
    intro k hk
    have hkg : k ∈ gates := hord_sub hk
    have hns : n + k ∉ special := (Finset.mem_filter.mp hk).2
    have hnn : k ∉ neg := fun h => hns (Finset.mem_union_right _ (Finset.mem_image_of_mem _ h))
    have hgk := hgates (gate k) (hgate_mem k hkg)
    rcases hgk with h1 | ⟨hop, _⟩
    · exact h1
    · exact absurd (Finset.mem_filter.mpr ⟨hkg, hop⟩) hnn
  have htot_reads : ∑ w ∈ Finset.range (n + C.size), reads w = 2 * C.size - neg.card := by
    rw [PEqualNP.Outside.L_meta_25808_aux.Slots.sum_readsIn_all hRB gates (Finset.Subset.refl _)]
    have hsum : ∑ k ∈ gates, (gate k).inputs.length =
        ∑ k ∈ neg, 1 + ∑ k ∈ gates \ neg, 2 := by
      have hdisj : Disjoint neg (gates \ neg) := Finset.disjoint_sdiff
      have hu : neg ∪ (gates \ neg) = gates := Finset.union_sdiff_of_subset hneg_sub
      conv_lhs => rw [← hu, Finset.sum_union hdisj]
      congr 1
      · apply Finset.sum_congr rfl; intro k hk; rw [hgate_len k (hneg_sub hk)]; simp [hk]
      · apply Finset.sum_congr rfl; intro k hk
        rcases Finset.mem_sdiff.mp hk with ⟨hkg, hnn⟩
        rw [hgate_len k hkg]; simp [hnn]
    rw [hsum]
    simp only [Finset.sum_const, smul_eq_mul, mul_one]
    have hcard_sdiff : (gates \ neg).card = C.size - neg.card := by
      rw [Finset.card_sdiff_of_subset hneg_sub, Finset.card_range]
    have hneg_le : neg.card ≤ C.size := by
      have := Finset.card_le_card hneg_sub; rwa [Finset.card_range] at this
    rw [hcard_sdiff]
    omega
  have hout_reads : reads (n + (C.size - 1)) = 0 := by
    rw [PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_zero_iff]
    intro k hk hmem
    have hlt := hRB k (Finset.mem_range.mp hk) (n + (C.size - 1)) hmem
    have hklt : k < C.size := Finset.mem_range.mp hk
    omega
  have hpos_wires : (Finset.range (n + C.size)).filter (fun w => 0 < reads w) =
      used ∪ (Finset.range (C.size - 1)).image (fun j => n + j) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image, used]
    constructor
    · rintro ⟨hw, hposw⟩
      by_cases hwn : w < n
      · exact Or.inl ⟨hwn, hposw⟩
      · right
        refine ⟨w - n, ?_, by omega⟩
        by_contra hge
        have heq : w = n + (C.size - 1) := by omega
        rw [heq, hout_reads] at hposw
        omega
    · rintro (⟨hwn, hposw⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨by omega, hposw⟩
      · exact ⟨by omega, hnonout j (by omega) (by omega)⟩
  have hpos_card : ((Finset.range (n + C.size)).filter (fun w => 0 < reads w)).card =
      used.card + (C.size - 1) := by
    rw [hpos_wires, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => by omega),
        Finset.card_range]
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hwn : w < n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    rcases Finset.mem_image.mp h2 with ⟨j, _, rfl⟩
    omega
  set R := ∑ w ∈ Finset.range (n + C.size), (reads w - 1)
  have hreads_decomp : ∑ w ∈ Finset.range (n + C.size), reads w =
      ((Finset.range (n + C.size)).filter (fun w => 0 < reads w)).card + R := by
    have hpt : ∀ w ∈ Finset.range (n + C.size),
        reads w = (if 0 < reads w then 1 else 0) + (reads w - 1) := by
      intro w _
      by_cases h : 0 < reads w <;> simp [h] <;> omega
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_boole, Nat.cast_id]
  have hneg_le : neg.card ≤ C.size := by
    have := Finset.card_le_card hneg_sub; rwa [Finset.card_range] at this
  have hR_eq : R = excess := by
    dsimp only [excess]
    rw [hpos_card] at hreads_decomp
    omega
  have hused_le : used.card ≤ C.size - neg.card + 1 := by
    rw [hpos_card] at hreads_decomp
    omega
  refine ⟨hused_le,?_⟩
  set specialGates := gates.filter (fun k => n + k ∈ special)
  set g := specialGates.card
  set u := multiple.card
  set t := neg.card
  set d := excess
  set e := ∑ k ∈ ordinaryGates, (gate k).inputs.countP (fun w => decide (w ∈ special))
  set x := ∑ k ∈ specialGates, (gate k).inputs.countP (fun w => decide (w ∉ special))
  have hneg_sub_sg : neg ⊆ specialGates := by
    intro k hk
    exact Finset.mem_filter.mpr ⟨hneg_sub hk, Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)⟩
  have hineqA : x + t ≤ 2 * g := by
    have hx_le : x ≤ ∑ k ∈ specialGates, (gate k).inputs.length := by
      dsimp only [x]
      apply Finset.sum_le_sum
      intro k _
      exact List.countP_le_length
    have hsum_sg : ∑ k ∈ specialGates, (gate k).inputs.length = 2 * g - t := by
      have hdisj : Disjoint neg (specialGates \ neg) := Finset.disjoint_sdiff
      have hu : neg ∪ (specialGates \ neg) = specialGates := Finset.union_sdiff_of_subset hneg_sub_sg
      conv_lhs => rw [← hu, Finset.sum_union hdisj]
      have s1 : ∑ k ∈ neg, (gate k).inputs.length = t := by
        have hpt : ∀ k ∈ neg, (gate k).inputs.length = 1 := fun k hk => by
          rw [hgate_len k (hneg_sub hk)]; simp [hk]
        rw [Finset.sum_congr rfl hpt]; simp [t]
      have s2 : ∑ k ∈ specialGates \ neg, (gate k).inputs.length = 2 * (g - t) := by
        have hpt : ∀ k ∈ specialGates \ neg, (gate k).inputs.length = 2 := fun k hk => by
          rcases Finset.mem_sdiff.mp hk with ⟨hks, hnn⟩
          rw [hgate_len k (Finset.mem_filter.mp hks).1]; simp [hnn]
        rw [Finset.sum_congr rfl hpt]
        simp only [Finset.sum_const, smul_eq_mul]
        rw [Finset.card_sdiff_of_subset hneg_sub_sg]
        ring
      have ht_le_g : t ≤ g := Finset.card_le_card hneg_sub_sg
      rw [s1, s2]
      omega
    have ht_le_g : t ≤ g := Finset.card_le_card hneg_sub_sg
    omega
  have hspec_sub : special ⊆ Finset.range (n + C.size) := by
    intro w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · exact (Finset.mem_filter.mp h1).1
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      have := Finset.mem_range.mp (hneg_sub hk)
      exact Finset.mem_range.mpr (by omega)
  have hspec_card : special.card = u + g := by
    have hpart : special = multiple ∪ specialGates.image (fun k => n + k) := by
      ext w
      simp only [Finset.mem_union, Finset.mem_image, multiple, specialGates, gates, Finset.mem_filter,
        Finset.mem_range]
      constructor
      · intro hw
        have hwlt : w < n + C.size := Finset.mem_range.mp (hspec_sub hw)
        by_cases hwn : w < n
        · left
          refine ⟨hwn, ?_⟩
          rcases Finset.mem_union.mp hw with h1 | h2
          · exact (Finset.mem_filter.mp h1).2
          · rcases Finset.mem_image.mp h2 with ⟨k, _, heq⟩; omega
        · right
          exact ⟨w - n, ⟨by omega, by rwa [show n + (w - n) = w by omega]⟩, by omega⟩
      · rintro (⟨hwn, hr2⟩ | ⟨k, ⟨_, hsp⟩, rfl⟩)
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hr2⟩)
        · exact hsp
    rw [hpart, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
    rw [Finset.disjoint_left]
    intro w h1 h2
    have hwn : w < n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
    rcases Finset.mem_image.mp h2 with ⟨k, _, rfl⟩
    omega
  have hineqB : g + u ≤ d + t := by
    set shared := (Finset.range (n + C.size)).filter (fun w => 2 ≤ reads w)
    have h1 : special.card ≤ shared.card + (neg.image (fun k => n + k)).card :=
      Finset.card_union_le _ _
    have h2 : (neg.image (fun k => n + k)).card ≤ t := Finset.card_image_le
    have h3 : shared.card ≤ R := by
      have hle1 : shared.card = ∑ _w ∈ shared, 1 := by simp
      rw [hle1]
      calc ∑ _w ∈ shared, 1
          ≤ ∑ w ∈ shared, (reads w - 1) := by
            apply Finset.sum_le_sum; intro w hw
            have := (Finset.mem_filter.mp hw).2; omega
        _ ≤ ∑ w ∈ Finset.range (n + C.size), (reads w - 1) :=
            Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    rw [hspec_card] at h1
    omega
  have hineqC : e ≤ d + u + g := by
    have he_eq : e = ∑ w ∈ special, PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w :=
      (PEqualNP.Outside.L_meta_25808_aux.Slots.sum_readsIn_eq_sum_countP C ordinaryGates special).symm
    have hle1 : e ≤ ∑ w ∈ special, reads w := by
      rw [he_eq]
      apply Finset.sum_le_sum
      intro w _
      exact PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_mono hord_sub w
    have hle2 : ∑ w ∈ special, reads w ≤ (∑ w ∈ special, (reads w - 1)) + special.card := by
      calc ∑ w ∈ special, reads w
          ≤ ∑ w ∈ special, ((reads w - 1) + 1) := by
            apply Finset.sum_le_sum; intro w _; omega
        _ = (∑ w ∈ special, (reads w - 1)) + ∑ _w ∈ special, 1 := Finset.sum_add_distrib
        _ = (∑ w ∈ special, (reads w - 1)) + special.card := by simp
    have hle3 : ∑ w ∈ special, (reads w - 1) ≤ R :=
      Finset.sum_le_sum_of_subset hspec_sub
    omega
  set OrdWires := once ∪ ordinaryGates.image (fun k => n + k)
  set Roots := OrdWires.filter (fun w => PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w = 0)
  have hord_read_le : ∀ w ∈ OrdWires, reads w ≤ 1 := by
    intro w hw
    rcases Finset.mem_union.mp hw with h1 | h2
    · have := (Finset.mem_filter.mp h1).2; omega
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      have hns : n + k ∉ special := (Finset.mem_filter.mp hk).2
      have hklt : k < C.size := Finset.mem_range.mp (hord_sub hk)
      by_contra hgt
      apply hns
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), by omega⟩)
  have hord_nonout_eq1 : ∀ w ∈ OrdWires, w ≠ C.output → reads w = 1 := by
    intro w hw hne
    rcases Finset.mem_union.mp hw with h1 | h2
    · exact (Finset.mem_filter.mp h1).2
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      have hklt : k < C.size := Finset.mem_range.mp (hord_sub hk)
      have hposw : 0 < reads (n + k) := hnonout k hklt (by omega)
      have hle1 := hord_read_le (n + k) hw
      omega
  have hord_disj_spec : ∀ w ∈ OrdWires, w ∉ special := by
    intro w hw hsp
    rcases Finset.mem_union.mp hw with h1 | h2
    · have hwn : w < n := Finset.mem_range.mp (Finset.mem_filter.mp h1).1
      have hr1 : reads w = 1 := (Finset.mem_filter.mp h1).2
      rcases Finset.mem_union.mp hsp with hsp1 | hsp2
      · have := (Finset.mem_filter.mp hsp1).2; omega
      · rcases Finset.mem_image.mp hsp2 with ⟨k, _, heq⟩; omega
    · rcases Finset.mem_image.mp h2 with ⟨k, hk, rfl⟩
      exact (Finset.mem_filter.mp hk).2 hsp
  have hdisj_ord_sg : Disjoint ordinaryGates specialGates := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    exact (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
  have hunion_ord_sg : ordinaryGates ∪ specialGates = gates := by
    ext k
    simp only [Finset.mem_union, ordinaryGates, specialGates, Finset.mem_filter]
    tauto
  have hRoots_le : Roots.card ≤ x + 1 := by
    have hsub : Roots \ {C.output} ⊆ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w) := by
      intro w hw
      rcases Finset.mem_sdiff.mp hw with ⟨hwR, hne⟩
      rcases Finset.mem_filter.mp hwR with ⟨hwO, hr0⟩
      refine Finset.mem_filter.mpr ⟨hwO, ?_⟩
      have hr1 : reads w = 1 := hord_nonout_eq1 w hwO (by simpa using hne)
      have htot := PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_union (C := C) hdisj_ord_sg w
      rw [hunion_ord_sg] at htot
      change reads w = PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w +
        PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w at htot
      omega
    have hcard1 : (Roots \ {C.output}).card ≤ x := by
      calc (Roots \ {C.output}).card
          ≤ (OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w)).card :=
            Finset.card_le_card hsub
        _ ≤ ∑ w ∈ OrdWires, PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w := by
            have h1 : (OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w)).card =
                ∑ _w ∈ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w), 1 := by simp
            rw [h1]
            calc ∑ _w ∈ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w), 1
                ≤ ∑ w ∈ OrdWires.filter (fun w => 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w),
                    PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w := by
                  apply Finset.sum_le_sum; intro w hw
                  exact (Finset.mem_filter.mp hw).2
              _ ≤ ∑ w ∈ OrdWires, PEqualNP.MetaComplexity.NestedCover.readsIn C specialGates w :=
                  Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ = ∑ k ∈ specialGates, (gate k).inputs.countP (fun w => decide (w ∈ OrdWires)) :=
            PEqualNP.Outside.L_meta_25808_aux.Slots.sum_readsIn_eq_sum_countP C specialGates OrdWires
        _ ≤ x := by
            dsimp only [x]
            apply Finset.sum_le_sum
            intro k _
            apply List.countP_mono_left
            intro w _ hw
            have hwO : w ∈ OrdWires := by simpa using hw
            simpa using hord_disj_spec w hwO
    have hcard2 : Roots.card ≤ (Roots \ {C.output}).card + 1 := by
      have := Finset.card_le_card (show Roots ⊆ (Roots \ {C.output}) ∪ {C.output} from
        fun w hw => by by_cases h : w = C.output <;> simp [hw, h])
      exact le_trans this (by simpa using Finset.card_union_le (Roots \ {C.output}) {C.output})
    omega
  have hord_reads_le1 : ∀ w ∈ OrdWires, PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w ≤ 1 :=
    fun w hw => le_trans (PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_mono hord_sub w) (hord_read_le w hw)
  have hcover_ord : ∀ w ∈ OrdWires, ∃ r ∈ Roots, w ∈ PEqualNP.Outside.L_meta_25808_aux.Slots.subWires n C ordinaryGates OrdWires r := by
    have hdown : ∀ (m : ℕ) (w : ℕ), w ∈ OrdWires → n + C.size - w = m →
        ∃ r ∈ Roots, w ∈ PEqualNP.Outside.L_meta_25808_aux.Slots.subWires n C ordinaryGates OrdWires r := by
      intro m
      induction m using Nat.strong_induction_on with
      | ind m ih =>
        intro w hw hm
        by_cases hr0 : PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates w = 0
        · exact ⟨w, Finset.mem_filter.mpr ⟨hw, hr0⟩, PEqualNP.Outside.L_meta_25808_aux.Slots.mem_subWires_self hw⟩
        · rcases PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_pos_iff.mp (Nat.pos_of_ne_zero hr0) with ⟨k, hk, hwk⟩
          have hklt : k < C.size := Finset.mem_range.mp (hord_sub hk)
          have hlt : w < n + k := hRB k hklt w hwk
          have hnkO : n + k ∈ OrdWires := Finset.mem_union_right _ (Finset.mem_image_of_mem _ hk)
          rcases ih (n + C.size - (n + k)) (by omega) (n + k) hnkO rfl with ⟨r, hrR, hnk_in⟩
          exact ⟨r, hrR, PEqualNP.Outside.L_meta_25808_aux.Slots.subWires_closed_down hRB hord_sub hk hnk_in w hwk hw⟩
    intro w hw
    exact hdown (n + C.size - w) w hw rfl
  let Wr : ℕ → Finset ℕ := fun r => PEqualNP.Outside.L_meta_25808_aux.Slots.subWires n C ordinaryGates OrdWires r
  let Gr : ℕ → Finset ℕ := fun r => ordinaryGates.filter (fun k => n + k ∈ Wr r)
  let Sr : ℕ → Finset ℕ := fun r => once.filter (fun w => w ∈ Wr r)
  have hWr_disj : ∀ r₁ ∈ Roots, ∀ r₂ ∈ Roots, r₁ ≠ r₂ → Disjoint (Wr r₁) (Wr r₂) := by
    intro r₁ hr₁ r₂ hr₂ hne
    have hnot : ∀ a ∈ Roots, ∀ b ∈ Roots, a ≠ b → a ∉ Wr b := by
      intro a ha b _ hab haWb
      rcases PEqualNP.Outside.L_meta_25808_aux.Slots.mem_subWires_ne_has_parent hRB hord_sub haWb hab with
        ⟨k, hk, _, hak⟩
      have hposa : 0 < PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates a :=
        PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_pos_iff.mpr ⟨k, hk, hak⟩
      have h0a := (Finset.mem_filter.mp ha).2
      omega
    exact PEqualNP.Outside.L_meta_25808_aux.Slots.subWires_disjoint hRB hord_sub hord_reads_le1
      (hnot r₁ hr₁ r₂ hr₂ hne) (hnot r₂ hr₂ r₁ hr₁ hne.symm)
  have hGr_disj : Set.PairwiseDisjoint (Roots : Set ℕ) Gr := by
    intro r₁ hr₁ r₂ hr₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro k hk1 hk2
    exact Finset.disjoint_left.mp (hWr_disj r₁ hr₁ r₂ hr₂ hne)
      (Finset.mem_filter.mp hk1).2 (Finset.mem_filter.mp hk2).2
  have honce_lt : ∀ w ∈ once, w < n := fun w hw => Finset.mem_range.mp (Finset.mem_filter.mp hw).1
  have htree_bd : ∀ r ∈ Roots,
      (Sr r \ H).card ≤ p + 2 * c * PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) := by
    intro r hrR
    have hrO : r ∈ OrdWires := (Finset.mem_filter.mp hrR).1
    have hct := PEqualNP.Outside.L_meta_25808_aux.Slots.subWires_cutTree hRB hord_sub honce_lt
      (Finset.Subset.refl _) (Finset.Subset.refl _) hord_reads_le1
      (fun w hw hr1 => by
        have hne : w ≠ C.output := by
          intro h; subst h
          have h0 : reads C.output = 0 := by rw [show C.output = n + (C.size - 1) by omega]; exact hout_reads
          have hle := PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_mono (C := C) hord_sub C.output
          change PEqualNP.MetaComplexity.NestedCover.readsIn C ordinaryGates C.output ≤ reads C.output at hle
          omega
        exact ⟨hord_nonout_eq1 w hw hne, hne.symm⟩) hrO
    have hWr_eq : Wr r = Sr r ∪ (Gr r).image (fun k => n + k) :=
      PEqualNP.Outside.L_meta_25808_aux.Slots.subWires_mem_partition honce_lt rfl r
    have hbd := PEqualNP.Outside.L_meta_25808_aux.Slots.cutTree_leaf_bound hRB hord_sub hbin_ord honce_lt
      hp_bd hc_bd (PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r))
      (Gr r) (Sr r) r hct (by rw [← hWr_eq])
    by_cases h0 : PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) = 0
    · simp only [h0, ite_true] at hbd; omega
    · simp only [h0, ite_false] at hbd
      have h1 : c * (2 * PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) - 1) ≤
          2 * c * PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) := by
        calc c * (2 * PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) - 1)
            ≤ c * (2 * PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r)) :=
              Nat.mul_le_mul_left c (Nat.sub_le _ _)
          _ = 2 * c * PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) := by ring
      omega
  have hext_le_e : ∑ r ∈ Roots, PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) ≤ e := by
    have hpt : ∀ r ∈ Roots, PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) ≤
        ∑ k ∈ Gr r, (gate k).inputs.countP (fun w => decide (w ∈ special)) := by
      intro r _
      unfold PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots
      apply Finset.sum_le_sum
      intro k hk
      rcases Finset.mem_filter.mp hk with ⟨hkO, hnkWr⟩
      apply List.countP_mono_left
      intro w hw hnw
      have hnw' : w ∉ Wr r := by simpa using hnw
      have hnwO : w ∉ OrdWires := fun h => hnw' (PEqualNP.Outside.L_meta_25808_aux.Slots.subWires_closed_down hRB hord_sub hkO hnkWr w hw h)
      have hwlt : w < n + C.size := by
        have hklt : k < C.size := Finset.mem_range.mp (hord_sub hkO)
        have := hRB k hklt w hw; omega
      have hposw : 0 < reads w := PEqualNP.Outside.L_meta_25808_aux.Slots.readsIn_pos_iff.mpr ⟨k, hord_sub hkO, hw⟩
      have hwsp : w ∈ special := by
        by_cases hwn : w < n
        · have hge2 : 2 ≤ reads w := by
            by_contra hlt2
            have hr1 : reads w = 1 := by omega
            exact hnwO (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, hr1⟩))
          exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwlt, hge2⟩)
        · by_contra hnsp
          have hkg : w - n ∈ gates := Finset.mem_range.mpr (by omega)
          have hkord : w - n ∈ ordinaryGates :=
            Finset.mem_filter.mpr ⟨hkg, by rwa [show n + (w - n) = w by omega]⟩
          exact hnwO (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w - n, hkord, by omega⟩))
      simpa using hwsp
    calc ∑ r ∈ Roots, PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r)
        ≤ ∑ r ∈ Roots, ∑ k ∈ Gr r, (gate k).inputs.countP (fun w => decide (w ∈ special)) :=
          Finset.sum_le_sum hpt
      _ = ∑ k ∈ Roots.biUnion Gr, (gate k).inputs.countP (fun w => decide (w ∈ special)) :=
          (Finset.sum_biUnion hGr_disj).symm
      _ ≤ e := Finset.sum_le_sum_of_subset (Finset.biUnion_subset.mpr (fun r _ => Finset.filter_subset _ _))
  have honceH_le : (once \ H).card ≤ p * (x + 1) + 2 * c * e := by
    have hsub : once \ H ⊆ Roots.biUnion (fun r => Sr r \ H) := by
      intro w hw
      rcases Finset.mem_sdiff.mp hw with ⟨hw1, hwH⟩
      rcases hcover_ord w (Finset.mem_union_left _ hw1) with ⟨r, hrR, hwWr⟩
      exact Finset.mem_biUnion.mpr ⟨r, hrR, Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hw1, hwWr⟩, hwH⟩⟩
    calc (once \ H).card
        ≤ (Roots.biUnion (fun r => Sr r \ H)).card := Finset.card_le_card hsub
      _ ≤ ∑ r ∈ Roots, (Sr r \ H).card := Finset.card_biUnion_le
      _ ≤ ∑ r ∈ Roots, (p + 2 * c * PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r)) :=
          Finset.sum_le_sum htree_bd
      _ = Roots.card * p + 2 * c * ∑ r ∈ Roots, PEqualNP.Outside.L_meta_25808_aux.Slots.extSlots C (Gr r) (Wr r) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, ← Finset.mul_sum]
      _ ≤ (x + 1) * p + 2 * c * e := by
          have h1 := Nat.mul_le_mul_right p hRoots_le
          have h2 := Nat.mul_le_mul_left (2 * c) hext_le_e
          omega
      _ = p * (x + 1) + 2 * c * e := by ring
  have hn_le : n ≤ H.card + u + (once \ H).card := by
    have hsub : Finset.range n ⊆ H ∪ multiple ∪ (once \ H) := by
      intro w hw
      have hwn : w < n := Finset.mem_range.mp hw
      by_cases hwH : w ∈ H
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hwH)
      · by_cases hr0 : reads w = 0
        · exact absurd (hHunused w hwn hr0) hwH
        · by_cases hr1 : reads w = 1
          · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨hw, hr1⟩, hwH⟩)
          · exact Finset.mem_union_left _ (Finset.mem_union_right _
              (Finset.mem_filter.mpr ⟨hw, by omega⟩))
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 := Finset.card_union_le (H ∪ multiple) (once \ H)
    have h3 := Finset.card_union_le H multiple
    omega
  have hmain0 : n ≤ H.card + u + p * (x + 1) + 2 * c * e := by omega
  have hpx : p * x + p * t ≤ 2 * p * g := by
    calc p * x + p * t = p * (x + t) := (Nat.mul_add p x t).symm
      _ ≤ p * (2 * g) := Nat.mul_le_mul_left p hineqA
      _ = 2 * p * g := by ring
  have hce : 2 * c * e ≤ 2 * c * d + 2 * c * u + 2 * c * g := by
    calc 2 * c * e ≤ 2 * c * (d + u + g) := Nat.mul_le_mul_left (2 * c) hineqC
      _ = 2 * c * d + 2 * c * u + 2 * c * g := by ring
  have hgu : (2 * p + 2 * c) * g + (2 * p + 2 * c) * u ≤ (2 * p + 2 * c) * d + (2 * p + 2 * c) * t := by
    calc (2 * p + 2 * c) * g + (2 * p + 2 * c) * u
        = (2 * p + 2 * c) * (g + u) := (Nat.mul_add _ g u).symm
      _ ≤ (2 * p + 2 * c) * (d + t) := Nat.mul_le_mul_left _ hineqB
      _ = (2 * p + 2 * c) * d + (2 * p + 2 * c) * t := Nat.mul_add _ d t
  have hu_id : (2 * p - 1) * u + u = 2 * p * u := by
    have : 2 * p - 1 + 1 = 2 * p := by omega
    calc (2 * p - 1) * u + u = (2 * p - 1 + 1) * u := by ring
      _ = 2 * p * u := by rw [this]
  have hstep1 : n + (2 * p - 1) * u + p * t ≤
      H.card + p + 2 * c * d + (2 * p + 2 * c) * g + (2 * p + 2 * c) * u := by
    have hx1 : p * (x + 1) = p * x + p := by ring
    have hg1 : 2 * p * g + 2 * c * g = (2 * p + 2 * c) * g := by ring
    have hu1 : 2 * p * u + 2 * c * u = (2 * p + 2 * c) * u := by ring
    omega
  have hstep2 : (2 * p + 4 * c) * d = 2 * c * d + (2 * p + 2 * c) * d := by ring
  have hstep3 : (p + 2 * c) * t + p * t = (2 * p + 2 * c) * t := by ring
  omega
end PEqualNP.Outside.L_meta_25808_aux
namespace PEqualNP.Outside.L_meta_25808_aux.Cone.Profile.Wire
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w
theorem W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl
theorem step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]
theorem W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega
theorem getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]
theorem getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]
theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
theorem step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h
theorem step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _
theorem W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi
theorem W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)
theorem W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key
theorem gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]
theorem getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
theorem eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl
theorem val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)
theorem val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)
theorem val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj
theorem val_gate_rb {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) (hrb : ∀ i ∈ (gateAt C j).inputs, i < n + j) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => val C x i) := by
  rw [val_gate hx hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hrb i hi)]
theorem val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]
theorem val_ofFn_lt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    val C (List.ofFn x) u = x ⟨u, hu⟩ := val_ofFn C x ⟨u, hu⟩
def pt (n m a b : ℕ) : Fin (n + m) → Bool := fun k => decide (k.val = a) || decide (k.val = b)
theorem oneEach_pt (n m : ℕ) (u : Fin n) (v : Fin m) :
    PEqualNP.Represents.oneEach u v = List.ofFn (pt n m u.val (n + v.val)) := by
  rw [List.ofFn_add]
  unfold PEqualNP.Represents.oneEach
  have hu := u.isLt
  have hv := v.isLt
  congr 1
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.val_castAdd, Fin.coe_castLE]
    omega
  · congr 1
    funext k
    have hk := k.isLt
    rw [Bool.eq_iff_iff]
    simp only [pt, decide_eq_true_eq, Bool.or_eq_true, Fin.ext_iff, Fin.coe_natAdd]
    omega
end PEqualNP.Outside.L_meta_25808_aux.Cone.Profile.Wire
namespace PEqualNP.Outside.L_meta_25808_aux.Cone.Profile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def inner51 (N : Nat) (D : Finset Nat) (w : Nat) : Prop :=
  N≤w ∧ w-N∈D
structure Region51 (N : Nat) (C : Circuit) (S D E : Finset Nat) (top : Nat) : Prop where
  back : ReadsBack N C
  small : ∀ w∈S, w<N
  kept : D ⊆ Finset.range C.size
  topMem : top∈D
  one : E.card≤1
  entries : ∀ w∈E,w<N+top ∧ w∉S ∧ ¬inner51 N D w
  gates : ∀ j∈D, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    ∀ w∈(gateAt C j).inputs,w∈S ∨ inner51 N D w ∨ w∈E
  sealedInputs : ∀ j<C.size,j∉D → ∀ w∈(gateAt C j).inputs,w∉S ∧ (inner51 N D w → w=N+top)
  outS : C.output∉S
  outD : inner51 N D C.output → C.output=N+top
def cutVal51 (C : Circuit) (N : Nat) (E : Finset Nat) (lit : Nat) (e : Bool) (w : Nat) : Bool :=
  if w∈E then e else if w<N then decide (w=lit) else
    (gateAt C (w-N)).op.eval ((gateAt C (w-N)).inputs.map fun v =>
      if hv : v<w then cutVal51 C N E lit e v else false)
termination_by w
private lemma gateMono51 {l : List Nat} {f g : Nat → Bool} {op : GateOp}
    (h : op=.and ∨ op=.or) (le : ∀ v∈l,f v=true → g v=true)
    (x : op.eval (l.map f)=true) : op.eval (l.map g)=true := by
  rcases h with rfl|rfl
  · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at x ⊢
    exact fun v hv => le v hv (x v hv)
  · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at x ⊢
    obtain ⟨v,hv,hf⟩ := x
    exact ⟨v,hv,le v hv hf⟩
theorem cutMono51 {C : Circuit} {N lit top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) {a b : Bool} (le : ∀ v∈E,a=true → b=true) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E →
      cutVal51 C N E lit a w=true → cutVal51 C N E lit b w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    rw [cutVal51,cutVal51]
    by_cases he : w∈E
    · simpa only [if_pos he] using le w he
    simp only [if_neg he]
    by_cases raw : w<N
    · simp only [if_pos raw,imp_self]
    simp only [if_neg raw]
    have ins : inner51 N D w := (h.resolve_left (fun z => raw (H.small w z))).resolve_right he
    have jmem := ins.2
    refine gateMono51 (H.gates _ jmem).1 ?_
    intro v hv
    have lt := H.back (w-N) (Finset.mem_range.mp (H.kept jmem)) v hv
    have bound : v<w := by have := ins.1;omega
    simpa only [dif_pos bound] using ih v bound ((H.gates _ jmem).2 v hv)
theorem cutMatches51 {C : Circuit} {N lit top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (values : Nat → Bool) (e : Bool)
    (base : ∀ w∈S,values w=decide (w=lit)) (boundary : ∀ w∈E,values w=e)
    (step : ∀ j<C.size,values (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map values)) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E → values w=cutVal51 C N E lit e w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    rw [cutVal51]
    by_cases he : w∈E
    · simpa only [if_pos he] using boundary w he
    simp only [if_neg he]
    by_cases raw : w<N
    · rw [if_pos raw]
      exact base w (h.resolve_right (fun z => z.elim (fun si => (Nat.not_le_of_gt raw) si.1) he))
    rw [if_neg raw]
    have ins : inner51 N D w := (h.resolve_left (fun z => raw (H.small w z))).resolve_right he
    have jmem := ins.2
    have jlt := Finset.mem_range.mp (H.kept jmem)
    have eq := step (w-N) jlt
    rw [show N+(w-N)=w by omega] at eq
    rw [eq]
    congr 1
    apply List.map_congr_left
    intro v hv
    have lt := H.back (w-N) jlt v hv
    have bound : v<w := by have := ins.1;omega
    rw [dif_pos bound]
    exact ih v bound ((H.gates _ jmem).2 v hv)
theorem outside51 {C : Circuit} {N top : Nat} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (x y : Nat → Bool)
    (raw : ∀ w<N,w∉S → x w=y w)
    (gate : ∀ j<C.size,(∀ v∈(gateAt C j).inputs,x v=y v) → x (N+j)=y (N+j))
    (large : ∀ w,N+C.size≤w → x w=y w) :
    ∀ w,w∉S → (inner51 N D w → w=N+top) → (N+top≤w → x (N+top)=y (N+top)) → x w=y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ns ex term
    by_cases inp : w<N
    · exact raw w inp ns
    by_cases high : N+C.size≤w
    · exact large w high
    by_cases localWire : inner51 N D w
    · have eq := ex localWire
      exact eq ▸ term (by omega)
    have jlt : w-N<C.size := by omega
    have nreg : w-N∉D := fun hit => localWire ⟨by omega,hit⟩
    have add : N+(w-N)=w := by omega
    have agree (v : Nat) (hv : v∈(gateAt C (w-N)).inputs) : x v=y v := by
      have b := H.back (w-N) jlt v hv
      have bv : v<w := by omega
      have e := H.sealedInputs _ jlt nreg v hv
      exact ih v bv e.1 e.2 (fun z => term (by omega))
    exact add ▸ gate _ jlt agree
end PEqualNP.Outside.L_meta_25808_aux.Cone.Profile
namespace PEqualNP.Outside.L_meta_25808_aux.Cone.Profile
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
theorem sideCap51 {n m d N top : Nat} {C : Circuit} {S D E : Finset Nat}
    (H : Region51 N C S D E top) (A : Finset (Fin n)) (B : Finset (Fin m))
    (G : Fin n → Fin m → Bool) (pin : Fin n → Nat) (other : Fin m → Nat)
    (V : Fin n → Fin m → Nat → Bool)
    (distance : ∀ a b : Fin n,a≠b → d≤(Finset.univ.filter (fun v=>G a v≠G b v)).card)
    (privatePin : ∀ a∈A,pin a∈S) (unmarked : ∀ v∉B,other v∉S)
    (inputs : ∀ a v w,w<N → V a v w=(decide (w=pin a) || decide (w=other v)))
    (step : ∀ a v j,j<C.size → V a v (N+j)=(gateAt C j).op.eval ((gateAt C j).inputs.map (V a v)))
    (large : ∀ a v w,N+C.size≤w → V a v w=false)
    (result : ∀ a v,V a v C.output=G a v) (short : B.card<d) :
    A.card≤2+E.card := by
  classical
  let sig (a : Fin n) (e : Bool) := cutVal51 C N E (pin a) e (N+top)
  have itop : inner51 N D (N+top) := ⟨by omega,by simpa using H.topMem⟩
  have mon (a : Fin n) : sig a false=true → sig a true=true :=
    cutMono51 H (fun _ _ _ => rfl) _ (Or.inr (Or.inl itop))
  let code (a : Fin n) : Nat := if sig a false then 0 else if sig a true then 2 else 1
  have cap (a : Fin n) : code a<2+E.card := by
    by_cases nonempty : E.Nonempty
    · have h := Finset.card_pos.mpr nonempty
      dsimp [code]; split <;> (try split) <;> omega
    · have rev : sig a true=true → sig a false=true :=
        cutMono51 H (fun w hw => (nonempty ⟨w,hw⟩).elim) _ (Or.inr (Or.inl itop))
      dsimp [code]; split <;> (try split) <;> first | omega | solve_by_elim
  have same {a b : Fin n} (h : code a=code b) (t : Bool) : sig a t=sig b t := by
    have ma := mon a
    have mb := mon b
    dsimp only [code] at h
    cases t <;> cases fa : sig a false <;> cases fb : sig b false <;>
      cases ta : sig a true <;> cases tb : sig b true <;> simp_all
  have inj : Set.InjOn code (↑A : Set (Fin n)) := by
    intro a ha b hb eqcode
    by_contra ne
    have subset : Finset.univ.filter (fun v=>G a v≠G b v) ⊆ B := by
      intro v hv
      by_contra nv
      have agreeRaw : ∀ w<N,w∉S → V a v w=V b v w := by
        intro w hw ns
        have na : w≠pin a := fun z=>ns (z ▸ privatePin a ha)
        have nb : w≠pin b := fun z=>ns (z ▸ privatePin b hb)
        simp [inputs a v w hw,inputs b v w hw,na,nb]
      have outside := outside51 H (V a v) (V b v) agreeRaw (fun j hj h => by
        rw [step a v j hj,step b v j hj,List.map_congr_left h])
        (fun w hw => (large a v w hw).trans (large b v w hw).symm)
      have entrySame {w : Nat} (hw : w∈E) : V a v w=V b v w := by
        obtain ⟨less,ns,nd⟩ := H.entries w hw
        exact outside w ns (fun i=> (nd i).elim) (fun le=> (Nat.not_le_of_gt less le).elim)
      obtain ⟨state,ab,bb⟩ : ∃ t : Bool,(∀ w∈E,V a v w=t) ∧ ∀ w∈E,V b v w=t := by
        by_cases ex : E.Nonempty
        · obtain ⟨w,hw⟩ := ex
          refine ⟨V a v w,?_,?_⟩
          · intro t ht
            rw [Finset.card_le_one.mp H.one t ht w hw]
          · intro t ht
            rw [Finset.card_le_one.mp H.one t ht w hw,entrySame hw]
        · exact ⟨false,fun w hw=>(ex ⟨w,hw⟩).elim,fun w hw=>(ex ⟨w,hw⟩).elim⟩
      have base (q : Fin n) (w : Nat) (hw : w∈S) : V q v w=decide (w=pin q) := by
        have otherNe : w≠other v := fun en => unmarked v nv (en ▸ hw)
        simp [inputs q v w (H.small w hw),otherNe]
      have topA := cutMatches51 H (V a v) state (base a) ab (step a v) (N+top) (Or.inr (Or.inl itop))
      have topB := cutMatches51 H (V b v) state (base b) bb (step b v) (N+top) (Or.inr (Or.inl itop))
      have topAgree := topA.trans ((same eqcode state).trans topB.symm)
      apply (Finset.mem_filter.mp hv).2
      exact (result a v).symm.trans ((outside _ H.outS H.outD (fun _=>topAgree)).trans (result b v))
    have low := distance a b ne
    have up := Finset.card_le_card subset
    omega
  have small : A.image code ⊆ Finset.range (2+E.card) := by
    intro j hj
    obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (cap a)
  have cnt := Finset.card_le_card small
  simpa [Finset.card_image_of_injOn inj] using cnt
end PEqualNP.Outside.L_meta_25808_aux.Cone.Profile
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
open PEqualNP.Outside.L_meta_25808_aux.Cone.Profile in
theorem cap51 :
∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card) := by
  intro n m d G C R B region entry top raw sources inside gate farR farB back rep kept topMem one ext gates privateReads outputRaw outputGate
  classical
  let row := fun u : Fin n => u.val
  let col := fun v : Fin m => n+v.val
  have containsRow (u : Fin n) : row u∈sources ↔ u∈R := by
    constructor
    · intro hu
      rcases Finset.mem_union.mp hu with h|h
      · obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp h
        exact (Fin.ext eqn : q=u) ▸ hq
      · obtain ⟨q,_,eqn⟩ := Finset.mem_image.mp h
        change n+q.val=u.val at eqn
        omega
    · exact fun hu=>Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u,hu,rfl⟩)
  have containsCol (v : Fin m) : col v∈sources ↔ v∈B := by
    constructor
    · intro hv
      rcases Finset.mem_union.mp hv with h|h
      · obtain ⟨q,_,eqn⟩ := Finset.mem_image.mp h
        change q.val=n+v.val at eqn
        omega
      · obtain ⟨q,hq,eqn⟩ := Finset.mem_image.mp h
        change n+q.val=n+v.val at eqn
        exact (Fin.ext (Nat.add_left_cancel eqn) : q=v) ▸ hq
    · exact fun hv=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩)
  have small : ∀ w∈sources,w<raw := by
    intro w h
    rcases Finset.mem_union.mp h with h|h
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
      change q.val<n+m; omega
    · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp h
      change n+q.val<n+m; omega
  have H : Region51 raw C sources region entry top :=
    ⟨back,small,kept,topMem,one,ext,gates,privateReads,outputRaw,outputGate⟩
  let V := fun (u : Fin n) (v : Fin m) => Wire.val C (List.ofFn (Wire.pt n m (row u) (col v)))
  have inp (a : Fin n) (v : Fin m) (w : Nat) (hw : w<raw) :
      V a v w=(decide (w=row a) || decide (w=col v)) :=
    Wire.val_ofFn_lt C (Wire.pt n m (row a) (col v)) w hw
  have next (a : Fin n) (v : Fin m) (j : Nat) (hj : j<C.size) :
      V a v (raw+j)=(gate j).op.eval ((gate j).inputs.map (V a v)) :=
    Wire.val_gate_rb (by simp [raw]) hj (back j hj)
  have high (a : Fin n) (v : Fin m) (w : Nat) (hw : raw+C.size≤w) : V a v w=false :=
    Wire.val_ge (by simp [raw]) hw
  have out (a : Fin n) (v : Fin m) : V a v C.output=G a v := by
    have h := rep a v
    rw [Wire.oneEach_pt] at h
    exact h
  refine ⟨sideCap51 H R B G row col V farR (fun a=> (containsRow a).2)
      (fun v hv h=>hv ((containsCol v).1 h)) inp next high out,?_⟩
  apply sideCap51 H B R (fun v a=>G a v) col row (fun v a=>V a v) farB
      (fun v=>(containsCol v).2) (fun a ha h=>ha ((containsRow a).1 h))
  · intro v a w l
    rw [inp a v w l,Bool.or_comm]
  · exact fun v a => next a v
  · exact fun v a => high a v
  · exact fun v a => out a v
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
def nodes (N:Nat) (region S:Finset Nat) := S ∪ region.image (fun j=>N+j)
def edge (N:Nat) (C:Circuit) (region:Finset Nat) (w z:Nat) : Prop :=
  ∃ j∈region,z=N+j ∧ w∈(gateAt C j).inputs
abbrev reach (N:Nat) (C:Circuit) (region:Finset Nat) := Relation.ReflTransGen (edge N C region)
noncomputable def subsetAt (N:Nat) (C:Circuit) (region S:Finset Nat) (top:Nat) : Finset Nat := by
  classical exact S.filter (fun w=>reach N C region w top)
structure Frame (N:Nat) (C:Circuit) (region S entries:Finset Nat) (root:Nat) : Prop where
  low : ∀w∈S,w<N
  back : ReadsBack N C
  reg : region ⊆ Finset.range C.size
  rootIn : root∈nodes N region S
  entryOut : ∀e∈entries,e∉nodes N region S
  entryRead : ∀e∈entries,readsIn C region e=1
  shape : ∀j∈region, ((gateAt C j).op=.and ∨ (gateAt C j).op=.or) ∧
    (gateAt C j).inputs.length=2 ∧
    ∀ w∈(gateAt C j).inputs,w∈nodes N region S ∨ w∈entries
  rootZero : readsIn C region root=0
  priv : ∀w∈nodes N region S,w≠root →
    readsIn C region w=1 ∧ readsIn C (Finset.range C.size) w=1 ∧ C.output≠w
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {reg S X : Finset Nat} {root : Nat}
variable (F : Frame N C reg S X root)
include F
lemma edge_lt {u v:Nat} (e:edge N C reg u v) : u<v := by
  obtain ⟨j,hj,rfl,hit⟩:=e
  exact F.back j (Finset.mem_range.mp (F.reg hj)) u hit
lemma reach_le {u v:Nat} (h:reach N C reg u v) : u≤v := by
  induction h with
  | refl => rfl
  | tail _ e ih => exact ih.trans (Nat.le_of_lt (edge_lt F e))
lemma reader_le_one {j w:Nat} (hj:j∈reg) (hw:w∈(gateAt C j).inputs) : readsIn C reg w≤1 := by
  rcases (F.shape j hj).2.2 w hw with inside|ent
  · by_cases eq:w=root
    · simp [eq,F.rootZero]
    · exact Nat.le_of_eq (F.priv w inside eq).1
  · exact Nat.le_of_eq (F.entryRead w ent)
lemma succUnique {u v w:Nat} (h:edge N C reg u v) (h':edge N C reg u w) : v=w := by
  obtain ⟨i,hi,rfl,iu⟩:=h;obtain ⟨j,hj,rfl,ju⟩:=h'
  by_contra neq
  have ij : i≠j:=by omega
  have le:=Finset.add_le_sum (f:=fun k=>(gateAt C k).inputs.count u) (fun _ _=>Nat.zero_le _) hi hj ij
  have h1:=List.count_pos_iff.mpr iu
  have h2:=List.count_pos_iff.mpr ju
  have h3:=reader_le_one F hi iu
  change _≤readsIn C reg u at le
  omega
lemma enters {u v : Nat} (e:edge N C reg u v) : ∃ j∈reg,v=N+j := by
  obtain ⟨j,h,rfl,_⟩:=e;exact ⟨j,h,rfl⟩
lemma reachesRoot {w:Nat} (hw:w∈nodes N reg S) : reach N C reg w root := by
  let M:=N+C.size
  have bl {i:Nat} (h:i∈nodes N reg S) : i<M := by
    rcases Finset.mem_union.mp h with hs|hi
    · have:=F.low _ hs;dsimp [M];omega
    · obtain ⟨j,hj,rfl⟩:=Finset.mem_image.mp hi
      have:=Finset.mem_range.mp (F.reg hj);dsimp [M];omega
  suffices work : ∀ d,∀ i∈nodes N reg S, M-i=d → reach N C reg i root by exact work _ w hw rfl
  intro d;induction d using Nat.strong_induction_on with
  | ind d ih =>
    intro i hi eq
    by_cases ir:i=root
    · subst i;exact .refl
    have one:readsIn C reg i=1 := (F.priv _ hi ir).1
    have hit:∃j∈reg,i∈(gateAt C j).inputs := by
      by_contra! nh
      have z:readsIn C reg i=0:=Finset.sum_eq_zero (fun j hj=>List.count_eq_zero.mpr (nh j hj))
      omega
    obtain ⟨j,hj,m⟩:=hit
    have ed : edge N C reg i (N+j) := ⟨j,hj,rfl,m⟩
    have next:N+j∈nodes N reg S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
    exact (ih (M-(N+j)) (by have:=edge_lt F ed;have:=bl next;omega) (N+j) next rfl).head ed
lemma siblingsApart {x y top u:Nat} (ex:edge N C reg x top) (ey:edge N C reg y top)
    (ne:x≠y) (px:reach N C reg u x) (py:reach N C reg u y) : False := by
  have impossible {a b:Nat} (aa:edge N C reg a top) (bb:edge N C reg b top)
      (nn:a≠b) (path:reach N C reg a b) : False := by
    rcases path.cases_head with eq|⟨c,ac,cb⟩
    · exact nn eq
    · have same:=succUnique F aa ac
      have :=reach_le F cb;have:=edge_lt F bb;omega
  have unique : Relator.RightUnique (edge N C reg) := by
    intro a b c x y;exact succUnique F x y
  rcases Relation.ReflTransGen.total_of_right_unique unique px py with xy|yx
  · exact impossible ex ey ne xy
  · exact impossible ey ex ne.symm yx
lemma rootLeaves : subsetAt N C reg S root=S := by
  classical
  ext w;constructor
  · exact fun h=>(Finset.mem_filter.mp h).1
  · intro h;exact Finset.mem_filter.mpr ⟨h,reachesRoot F (Finset.mem_union_left _ h)⟩
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
variable {N : Nat} {C : Circuit} {reg S X : Finset Nat} {root : Nat}
variable (F : Frame N C reg S X root)
include F
private lemma splitNode (top:Nat) :
    (subsetAt N C reg S top).card≤1 ∨
    ∃ x y : Nat, x≠y ∧ top∈nodes N reg S ∧ edge N C reg x top ∧ edge N C reg y top ∧
      (subsetAt N C reg S top).card≤(subsetAt N C reg S x).card+(subsetAt N C reg S y).card := by
  classical
  by_cases gate : ∃ j∈reg,top=N+j
  · right
    obtain ⟨j,hj,rfl⟩:=gate
    obtain ⟨x,y,eq⟩:=List.length_eq_two.mp (F.shape j hj).2.1
    have hitx : x∈(gateAt C j).inputs := by simp [eq]
    have hity : y∈(gateAt C j).inputs := by simp [eq]
    have ne:x≠y := by
      intro e;subst y
      have le:=Finset.single_le_sum (f:=fun k=>(gateAt C k).inputs.count x) (fun _ _=>Nat.zero_le _) hj
      change (gateAt C j).inputs.count x≤readsIn C reg x at le
      have lim:=reader_le_one F hj hitx
      simp [eq] at le;omega
    refine ⟨x,y,ne,Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j,hj,rfl⟩),⟨j,hj,rfl,hitx⟩,⟨j,hj,rfl,hity⟩,?_⟩
    apply le_trans (b:=((subsetAt N C reg S x) ∪ (subsetAt N C reg S y)).card) _ (Finset.card_union_le _ _)
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hs,p⟩:=Finset.mem_filter.mp hw
    rcases p.cases_tail with same|⟨v,pv,i,hi,ii,m⟩
    · have:=F.low w hs;omega
    · have ij:i=j:=by omega
      subst i
      rw [eq] at m
      rcases (by simpa using m : v=x ∨ v=y) with rfl|rfl
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hs,pv⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hs,pv⟩)
  · left;apply Finset.card_le_one.mpr
    intro a ha b hb
    have eqtop (w:Nat) (h:w∈subsetAt N C reg S top) : w=top := by
      have p:reach N C reg w top := (Finset.mem_filter.mp h).2
      rcases p.cases_tail with eq|⟨v,_,e⟩
      · exact eq.symm
      · exact (gate (enters F e)).elim
    exact (eqtop _ ha).trans (eqtop _ hb).symm
omit F in
private lemma below {a b : Nat} {T:Finset Nat} (e:edge N C reg a b) :
    subsetAt N C reg T a ⊆ subsetAt N C reg T b := by
  classical
  intro w hw;obtain ⟨h,p⟩:=Finset.mem_filter.mp hw
  exact Finset.mem_filter.mpr ⟨h,p.tail e⟩
lemma pureBounds (cap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
    5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False) :
    ∀top,(subsetAt N C reg X top)=∅ → (subsetAt N C reg S top).card≤4 := by
  intro t;induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro empty
    rcases splitNode F t with leaf|⟨x,y,ne,ht,ex,ey,le⟩
    · omega
    · have bx:=ih x (edge_lt F ex) (Finset.subset_empty.mp (empty ▸ below (T:=X) ex))
      have by':=ih y (edge_lt F ey) (Finset.subset_empty.mp (empty ▸ below (T:=X) ey))
      by_contra! hlarge
      exact cap t ht empty (by omega) (by omega)
lemma boundPure (cap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
    5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False)
    (empty:X=∅) : S.card≤4 := by
  have hx : subsetAt N C reg X root=∅ := by simp [subsetAt,empty]
  simpa [rootLeaves F] using pureBounds F cap root hx
lemma boundMixed (cardX:X.card≤1)
    (pureCap:∀top∈nodes N reg S,(subsetAt N C reg X top)=∅ →
      5≤(subsetAt N C reg S top).card → (subsetAt N C reg S top).card≤8 → False)
    (mixCap:∀top∈nodes N reg S,7≤(subsetAt N C reg S top).card →
      (subsetAt N C reg S top).card≤10 → False) : S.card≤6 := by
  classical
  suffices all : ∀t,(subsetAt N C reg S t).card≤6 by simpa [rootLeaves F] using all root
  intro t;induction t using Nat.strong_induction_on with
  | ind t ih =>
    rcases splitNode F t with leaf|⟨x,y,ne,ht,ex,ey,le⟩
    · omega
    · have bx:=ih x (edge_lt F ex);have by':=ih y (edge_lt F ey)
      have either : subsetAt N C reg X x=∅ ∨ subsetAt N C reg X y=∅ := by
        by_contra! h
        obtain ⟨a,ha⟩:=h.1
        obtain ⟨b,hb⟩:=h.2
        obtain ⟨ax,ap⟩:=Finset.mem_filter.mp ha
        obtain ⟨bx,bp⟩:=Finset.mem_filter.mp hb
        have ab:=Finset.card_le_one.mp cardX a ax b bx;subst b
        exact siblingsApart F ex ey ne ap bp
      by_contra! large
      apply mixCap t ht (by omega)
      rcases either with h|h
      · have:=pureBounds F pureCap x h;omega
      · have:=pureBounds F pureCap y h;omega
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
abbrev srcSet {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) :=
  R.image (fun u=>u.val) ∪ B.image (fun v=>n+v.val)
lemma srcCard {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) :
    (srcSet R B).card=R.card+B.card := by
  classical
  unfold srcSet
  rw [Finset.card_union_of_disjoint,Finset.card_image_of_injective _ Fin.val_injective,
      Finset.card_image_of_injective _ (show Function.Injective (fun v:Fin m=>n+v.val) from fun _ _ e=>Fin.ext (Nat.add_left_cancel e))]
  apply Finset.disjoint_left.mpr
  intro w hu hv
  obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp hu
  obtain ⟨v,_,e⟩:=Finset.mem_image.mp hv
  have:=u.isLt;omega
lemma srcLow {n m:Nat} (R:Finset (Fin n)) (B:Finset (Fin m)) (w:Nat) (hw:w∈srcSet R B) : w<n+m := by
  rcases Finset.mem_union.mp hw with a|b
  · obtain ⟨u,_,rfl⟩:=Finset.mem_image.mp a;have:=u.isLt;omega
  · obtain ⟨v,_,rfl⟩:=Finset.mem_image.mp b;have:=v.isLt;omega
def WindowCap {N:Nat} (C:Circuit) (reg S X:Finset Nat) (d:Nat) : Prop :=
  ∀top∈nodes N reg S,
    let l:=(subsetAt N C reg S top).card
    let e:=(subsetAt N C reg X top).card
    e≤1 → 2+e<d → l<2*d → l≤2*(2+e)
lemma pure59 {N root : Nat} {C:Circuit} {reg S:Finset Nat} (F:Frame N C reg S ∅ root)
    (cap:WindowCap (N:=N) C reg S ∅ 5) : S.card≤4 := by
  apply boundPure F _ rfl
  intro t ht empty low hi
  have val:=cap t ht
  dsimp only at val;rw [empty,Finset.card_empty] at val;omega
lemma mixed62 {N root e : Nat} {C:Circuit} {reg S:Finset Nat} (F:Frame N C reg S {e} root)
    (cap:WindowCap (N:=N) C reg S {e} 6) : S.card≤6 := by
  apply boundMixed F (by simp)
  · intro t ht empty low hi
    have val:=cap t ht
    dsimp only at val;rw [empty,Finset.card_empty] at val;omega
  · intro t ht low hi
    classical
    have le : (subsetAt N C reg {e} t).card≤1 := by
      exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_singleton e).le
    have val:=cap t ht
    dsimp only at val;omega
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
noncomputable def gateSubset (N : Nat) (C : Circuit) (region : Finset Nat) (top : Nat) : Finset Nat := by
  classical exact region.filter (fun j => reach N C region (N+j) top)
private theorem walk_le {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {x y : Nat} (h : reach N C P x y) : x≤y := by
  induction h with
  | refl => exact le_rfl
  | tail _ e ih =>
    obtain ⟨j,hj,rfl,inp⟩:=e
    exact ih.trans (Nat.le_of_lt (F.back j (Finset.mem_range.mp (F.reg hj)) _ inp))
private theorem first_observer {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {w top : Nat} (inW : w∈nodes N P S)
    (path : reach N C P w top) (notTop : w≠top) :
    C.output≠w ∧ ∀j<C.size,w∈(gateAt C j).inputs → j∈gateSubset N C P top := by
  classical
  obtain ⟨v,edge,rest⟩ := path.cases_head.resolve_left notTop
  obtain ⟨i,hi,rfl,hit⟩ := edge
  have count := List.count_pos_iff.mpr hit
  have sub : (gateAt C i).inputs.count w ≤ readsIn C P w :=
    Finset.single_le_sum (fun l _ => Nat.zero_le ((gateAt C l).inputs.count w)) hi
  have nr : w≠root := by
    intro eq
    subst w
    rw [F.rootZero] at sub
    omega
  obtain ⟨_,one,out⟩ := F.priv w inW nr
  refine ⟨out,?_⟩
  intro j hj readJ
  have ji : j=i := by
    by_contra ne
    have cnt2 := List.count_pos_iff.mpr readJ
    have both := Finset.add_le_sum (f:=fun l => (gateAt C l).inputs.count w) (fun _ _=>Nat.zero_le _)
      (Finset.mem_range.mpr hj) (F.reg hi) ne
    change _ ≤ readsIn C (Finset.range C.size) w at both
    omega
  subst j
  exact Finset.mem_filter.mpr ⟨hi,rest⟩
theorem subtree_boundary {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {top : Nat} (member : top∈nodes N P S) (large : N≤top) :
    let P' := gateSubset N C P top
    let S' := subsetAt N C P S top
    let E' := subsetAt N C P E top
    let inside := fun w => N≤w ∧ w-N∈P'
    P' ⊆ Finset.range C.size ∧ top-N∈P' ∧
    (∀ e∈E', e<top ∧ e∉S' ∧ ¬inside e) ∧
    (∀ k∈P', ((gateAt C k).op=.and ∨ (gateAt C k).op=.or) ∧
      ∀w∈(gateAt C k).inputs,w∈S' ∨ inside w ∨ w∈E') ∧
    (∀ k<C.size, k∉P' → ∀w∈(gateAt C k).inputs, w∉S' ∧ (inside w → w=top)) ∧
    C.output∉S' ∧ (inside C.output → C.output=top) := by
  classical
  dsimp only
  have in_orig {w : Nat} (h : N≤w ∧ w-N∈gateSubset N C P top) :
      w∈nodes N P S ∧ reach N C P w top := by
    obtain ⟨lo,hw⟩:=h
    obtain ⟨hp,way⟩:=Finset.mem_filter.mp hw
    have eq : N+(w-N)=w:=by omega
    exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨w-N,hp,eq⟩),eq ▸ way⟩
  have raw_prop {w : Nat} (h : w∈subsetAt N C P S top) :
      w∈nodes N P S ∧ reach N C P w top ∧ w≠top := by
    obtain ⟨hs,path⟩:=Finset.mem_filter.mp h
    exact ⟨Finset.mem_union_left _ hs,path,ne_of_lt ((F.low _ hs).trans_le large)⟩
  have idx : top-N∈P := by
    rcases Finset.mem_union.mp member with hs | hg
    · have := F.low top hs;omega
    · obtain ⟨j,hj,eq⟩:=Finset.mem_image.mp hg
      exact (show top-N=j by omega) ▸ hj
  refine ⟨fun _ h=>F.reg (Finset.mem_filter.mp h).1,
    Finset.mem_filter.mpr ⟨idx,by rw [Nat.add_sub_of_le large]⟩,?_,?_,?_,?_,?_⟩
  · intro e he
    obtain ⟨inE,path⟩:=Finset.mem_filter.mp he
    have no := F.entryOut e inE
    exact ⟨lt_of_le_of_ne (walk_le F path) (fun eq=>no (eq ▸ member)),
      fun hs=>no (raw_prop hs).1,fun hi=>no (in_orig hi).1⟩
  · intro j hj
    obtain ⟨occurs,path⟩:=Finset.mem_filter.mp hj
    obtain ⟨op,_,inputs⟩:=F.shape j occurs
    refine ⟨op,?_⟩
    intro w hit
    have way : reach N C P w top := path.head ⟨j,occurs,rfl,hit⟩
    rcases inputs w hit with orig | ent
    · rcases Finset.mem_union.mp orig with src | g
      · exact Or.inl (Finset.mem_filter.mpr ⟨src,way⟩)
      · obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp g
        refine Or.inr (Or.inl ⟨by omega,?_⟩)
        rw [Nat.add_sub_cancel_left]
        exact Finset.mem_filter.mpr ⟨hk,way⟩
    · exact Or.inr (Or.inr (Finset.mem_filter.mpr ⟨ent,way⟩))
  · intro j hj outside w read
    constructor
    · intro hs
      obtain ⟨inW,way,ne⟩:=raw_prop hs
      exact outside ((first_observer F inW way ne).2 j hj read)
    · intro hi
      by_contra ne
      obtain ⟨inW,way⟩:=in_orig hi
      exact outside ((first_observer F inW way ne).2 j hj read)
  · intro hs
    obtain ⟨inW,way,ne⟩:=raw_prop hs
    exact (first_observer F inW way ne).1 rfl
  · intro hi
    by_contra ne
    obtain ⟨inW,way⟩:=in_orig hi
    exact (first_observer F inW way ne).1 rfl
theorem leaves_one_of_low {N root : Nat} {C : Circuit} {P S E : Finset Nat}
    (F : Frame N C P S E root) {top : Nat} (small : top<N) : (subsetAt N C P S top).card≤1 := by
  classical
  have sub : subsetAt N C P S top ⊆ {top} := by
    intro w hw;obtain ⟨_,path⟩:=Finset.mem_filter.mp hw
    rcases path.cases_tail with eq | ⟨v,_,j,hj,eq,_⟩
    · simpa using eq.symm
    · omega
  exact (Finset.card_le_card sub).trans (by simp)
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
def Gap51 : Prop :=
∀ (n m d : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (region entry : Finset ℕ) (top : ℕ),
  let raw := n + m
  let sources := R.image (fun sourceRow => sourceRow.val) ∪ B.image (fun sourceCol => n + sourceCol.val)
  let inside := fun (w : ℕ) => raw ≤ w ∧ w - raw ∈ region
  let gate := PEqualNP.MetaComplexity.NestedCover.gateAt C
  (∀ firstRow secondRow : Fin n, firstRow ≠ secondRow → d ≤ (Finset.univ.filter (fun col => G firstRow col ≠ G secondRow col)).card) →
  (∀ firstCol secondCol : Fin m, firstCol ≠ secondCol → d ≤ (Finset.univ.filter (fun row => G row firstCol ≠ G row secondCol)).card) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack raw C →
  PEqualNP.Represents.Represents G C → region ⊆ Finset.range C.size → top ∈ region →
  entry.card ≤ 1 → (∀ w ∈ entry, w < raw + top ∧ w ∉ sources ∧ ¬ inside w) →
  (∀ k ∈ region,
    ((gate k).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
     (gate k).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
    ∀ w ∈ (gate k).inputs, w ∈ sources ∨ inside w ∨ w ∈ entry) →
  (∀ k < C.size, k ∉ region → ∀ w ∈ (gate k).inputs,
    w ∉ sources ∧ (inside w → w = raw + top)) →
  C.output ∉ sources → (inside C.output → C.output = raw + top) →
  (B.card < d → R.card ≤ 2 + entry.card) ∧ (R.card < d → B.card ≤ 2 + entry.card)
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Cone
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
def sourceIds {n m : Nat} (R : Finset (Fin n)) (B : Finset (Fin m)) : Finset Nat :=
  R.image Fin.val ∪ B.image (fun v=>n+v.val)
theorem sourceCard {n m : Nat} (R : Finset (Fin n)) (B : Finset (Fin m)) :
    (sourceIds R B).card = R.card+B.card := by
  classical
  have dis : Disjoint (R.image Fin.val) (B.image (fun v=>n+v.val)) := by
    apply Finset.disjoint_left.mpr
    intro w hw hb
    obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hw
    obtain ⟨v,hv,e⟩:=Finset.mem_image.mp hb
    have:=u.isLt;omega
  unfold sourceIds
  rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective _ Fin.val_injective,
    Finset.card_image_of_injective _ (fun _ _ e=>Fin.ext (Nat.add_left_cancel e))]
theorem forbiddenWindow {n m d root : Nat} {G : Fin n → Fin m → Bool} {C : Circuit}
    {R : Finset (Fin n)} {B : Finset (Fin m)} {region entries : Finset Nat}
    (cap : Gap51)
    (dr : ∀ a b : Fin n, a≠b → d≤(Finset.univ.filter (fun col=>G a col≠G b col)).card)
    (dc : ∀ a b : Fin m, a≠b → d≤(Finset.univ.filter (fun row=>G row a≠G row b)).card)
    (rep : Represents G C) (F : Frame (n+m) C region (sourceIds R B) entries root)
    {top : Nat} (ht : top∈nodes (n+m) region (sourceIds R B))
    (one : (subsetAt (n+m) C region entries top).card≤1)
    (narrow : 2+(subsetAt (n+m) C region entries top).card<d)
    (window : (subsetAt (n+m) C region (sourceIds R B) top).card<2*d) :
    (subsetAt (n+m) C region (sourceIds R B) top).card ≤
      2*(2+(subsetAt (n+m) C region entries top).card) := by
  classical
  let N:=n+m
  let S:=sourceIds R B
  let P' := gateSubset N C region top
  let E' := subsetAt N C region entries top
  let A := R.filter (fun u => reach N C region u.val top)
  let H := B.filter (fun v => reach N C region (n+v.val) top)
  have ids : sourceIds A H = subsetAt N C region S top := by
    ext w
    simp only [sourceIds, A, H, S,subsetAt,Finset.mem_filter,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro (⟨u,⟨hu,way⟩,rfl⟩ | ⟨v,⟨hv,way⟩,rfl⟩)
      · exact ⟨Or.inl ⟨u,hu,rfl⟩,way⟩
      · exact ⟨Or.inr ⟨v,hv,rfl⟩,way⟩
    · rintro ⟨(⟨u,hu,rfl⟩ | ⟨v,hv,rfl⟩),way⟩
      · exact Or.inl ⟨u,⟨hu,way⟩,rfl⟩
      · exact Or.inr ⟨v,⟨hv,way⟩,rfl⟩
  have card : (subsetAt N C region S top).card = A.card+H.card := by rw [←ids,sourceCard]
  by_cases inside : N≤top
  · obtain ⟨sub,topIn,ent,op,out,privateR,privateG⟩:=subtree_boundary F ht inside
    have eq : N+(top-N)=top := Nat.add_sub_of_le inside
    have rule := cap n m d G C A H P' E' (top-N) dr dc F.back rep sub topIn one
    change (∀w∈E', w<N+(top-N) ∧ w∉sourceIds A H ∧ ¬(N≤w ∧ w-N∈P')) → _ at rule
    have answer := rule (by simpa only [eq,ids] using ent)
      (by
        change ∀k∈P', _ ∧ ∀w∈(gateAt C k).inputs,w∈sourceIds A H ∨ (N≤w ∧ w-N∈P') ∨ w∈E'
        rw [ids];exact op)
      (by
        change ∀k<C.size,k∉P' → ∀w∈(gateAt C k).inputs,w∉sourceIds A H ∧ ((N≤w ∧ w-N∈P') → w=N+(top-N))
        rw [ids,eq];exact out)
      (by change C.output∉sourceIds A H;rw [ids];exact privateR)
      (by change (N≤C.output ∧ C.output-N∈P') → C.output=N+(top-N);rw [eq];exact privateG)
    obtain ⟨bsmall,asmall⟩ := answer
    change H.card<d → A.card≤2+E'.card at bsmall
    change A.card<d → H.card≤2+E'.card at asmall
    change 2+E'.card<d at narrow
    change (subsetAt N C region S top).card<2*d at window
    change (subsetAt N C region S top).card≤2*(2+E'.card)
    omega
  · have small:=leaves_one_of_low F (top:=top) (by omega)
    omega
end PEqualNP.Outside.L_meta_25808_aux.Cone
namespace PEqualNP.Outside.L_meta_25808_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Cone Cone.Profile Cone.Profile.Wire
def world (N : Nat) (C : Circuit) (X : Finset Nat) (w : Nat) :=
  val C (List.ofFn (fun i : Fin N => decide (i.val ∈ X))) w
lemma world_raw {N C X w} (hw : w < N) : world N C X w = decide (w∈X) :=
  val_ofFn_lt C _ w hw
lemma world_step {N C X} (back : ReadsBack N C) (j : Nat) (hj : j<C.size) :
    world N C X (N+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (world N C X)) :=
  val_gate_rb (by simp) hj (back j hj)
lemma world_past {N C X w} (far : N+C.size≤w) : world N C X w=false :=
  val_ge (by simp) far
def localVal (N : Nat) (C : Circuit) (E I : Finset Nat) (t : Bool) (w : Nat) : Bool :=
  if w∈E then t else if w<N then decide (w∈I) else
    (gateAt C (w-N)).op.eval ((gateAt C (w-N)).inputs.map (fun v =>
      if h : v<w then localVal N C E I t v else false))
termination_by w
variable {N : Nat} {C : Circuit} {S D E : Finset Nat} {j : Nat}
lemma local_mono (H : Region51 N C S D E j) {I J : Finset Nat} {a b : Bool}
    (growth : ∀w∈S, w∈I → w∈J) (bound : ∀w∈E, a=true → b=true) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E → localVal N C E I a w=true → localVal N C E J b w=true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rw [localVal,localVal]
    by_cases he : w∈E
    · simpa only [if_pos he] using bound w he
    simp only [if_neg he]
    by_cases low : w<N
    · have hs : w∈S := (hw.resolve_right (fun h => h.elim (fun h => (Nat.not_le_of_gt low) h.1) he))
      simpa only [if_pos low,decide_eq_true_eq] using growth w hs
    simp only [if_neg low]
    have hd : inner51 N D w := (hw.resolve_left (fun h => low (H.small w h))).resolve_right he
    have mono {l : List Nat} {f g : Nat → Bool} {op : GateOp} (hop : op=.and ∨ op=.or)
        (h : ∀v∈l, f v=true → g v=true) : op.eval (l.map f)=true → op.eval (l.map g)=true := by
      rcases hop with rfl|rfl
      · simp only [GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq]
        exact fun yes v hv => h v hv (yes v hv)
      · simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq]
        rintro ⟨v,hv,one⟩; exact ⟨v,hv,h v hv one⟩
    apply mono (H.gates _ hd.2).1
    intro v hv
    have lt := H.back (w-N) (Finset.mem_range.mp (H.kept hd.2)) v hv
    have less : v<w := by have := hd.1; omega
    simpa only [dif_pos less] using ih v less ((H.gates _ hd.2).2 v hv)
lemma agrees_inside (H : Region51 N C S D E j) (X I : Finset Nat) (a : Bool)
    (inside : ∀w∈S,w∈X ↔ w∈I) (boundary : ∀w∈E,world N C X w=a) :
    ∀ w, w∈S ∨ inner51 N D w ∨ w∈E → world N C X w=localVal N C E I a w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rw [localVal]
    by_cases he : w∈E
    · simpa only [if_pos he] using boundary w he
    simp only [if_neg he]
    by_cases low : w<N
    · have hs : w∈S := hw.resolve_right (fun h => h.elim (fun h => (Nat.not_le_of_gt low) h.1) he)
      simp only [if_pos low,world_raw low,inside w hs]
    simp only [if_neg low]
    have hd : inner51 N D w := (hw.resolve_left (fun h => low (H.small w h))).resolve_right he
    have eq := world_step (X:=X) H.back (w-N) (Finset.mem_range.mp (H.kept hd.2))
    rw [Nat.add_sub_of_le hd.1] at eq
    rw [eq]
    congr 1
    apply List.map_congr_left
    intro v hv
    have lt:=H.back (w-N) (Finset.mem_range.mp (H.kept hd.2)) v hv
    have less : v<w := by have := hd.1; omega
    rw [dif_pos less]
    exact ih v less ((H.gates _ hd.2).2 v hv)
lemma compare_worlds (H : Region51 N C S D E j) {X Y I J : Finset Nat}
    (hx : ∀w∈S,w∈X ↔ w∈I) (hy : ∀w∈S,w∈Y ↔ w∈J)
    (agree : ∀w<N,w∉S → (w∈X ↔ w∈Y))
    (sec : ∀t,localVal N C E I t (N+j)=localVal N C E J t (N+j)) :
    world N C X C.output=world N C Y C.output := by
  have ext := outside51 H (world N C X) (world N C Y)
    (fun w low ns => by simp only [world_raw low, agree w low ns])
    (fun k hk h => by rw [world_step H.back k hk,world_step H.back k hk,List.map_congr_left h])
    (fun w hi => (world_past hi).trans (world_past hi).symm)
  have entry {w} (hw : w∈E) : world N C X w = world N C Y w := by
    obtain ⟨low,ns,outer⟩ := H.entries w hw
    exact ext w ns (fun z => (outer z).elim) (fun z => (Nat.not_le_of_gt low z).elim)
  obtain ⟨t, tx, ty⟩ : ∃ t : Bool, (∀w∈E,world N C X w=t) ∧ ∀w∈E,world N C Y w=t := by
    by_cases non : E.Nonempty
    · obtain ⟨b,hb⟩ := non
      refine ⟨world N C X b,?_,?_⟩
      · intro w hw; rw [Finset.card_le_one.mp H.one w hw b hb]
      · intro w hw; rw [Finset.card_le_one.mp H.one w hw b hb,←entry hb]
    · exact ⟨false,fun w h=>(non ⟨w,h⟩).elim,fun w h=>(non ⟨w,h⟩).elim⟩
  have top : inner51 N D (N+j) := ⟨by omega,by simpa using H.topMem⟩
  have left := agrees_inside H X I t hx tx (N+j) (Or.inr (Or.inl top))
  have right := agrees_inside H Y J t hy ty (N+j) (Or.inr (Or.inl top))
  exact ext _ H.outS H.outD (fun _ => left.trans ((sec t).trans right.symm))
def code (N : Nat) (C : Circuit) (E I : Finset Nat) (root : Nat) : Nat :=
  if localVal N C E I false root then 2 else if localVal N C E I true root then 1 else 0
lemma ordered (H : Region51 N C S D E j) (I : Finset Nat) :
    localVal N C E I false (N+j)=true → localVal N C E I true (N+j)=true :=
  local_mono H (fun _ _ h=>h) (fun _ _ _=>rfl) _
    (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩))
lemma same_code (H : Region51 N C S D E j) {I J : Finset Nat}
    (eq : code N C E I (N+j)=code N C E J (N+j)) (t : Bool) :
    localVal N C E I t (N+j)=localVal N C E J t (N+j) := by
  have u:=ordered H I; have v:=ordered H J
  dsimp only [code] at eq
  cases t <;> cases a:localVal N C E I false (N+j) <;> cases b:localVal N C E I true (N+j) <;>
    cases c:localVal N C E J false (N+j) <;> cases d:localVal N C E J true (N+j) <;> simp_all
lemma key_mem (H : Region51 N C S D E j) (I : Finset Nat) :
    code N C E I (N+j) ∈ (if E=∅ then {0,2} else {0,1,2} : Finset Nat) := by
  by_cases em : E=∅
  · have reverse : localVal N C E I true (N+j)=true → localVal N C E I false (N+j)=true :=
      local_mono H (fun _ _ h=>h) (fun w hw => (Finset.notMem_empty w (em ▸ hw)).elim) _
        (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩))
    rw [if_pos em]
    dsimp only [code]
    cases a:localVal N C E I false (N+j) <;> cases b:localVal N C E I true (N+j) <;> simp_all
  · rw [if_neg em]
    dsimp only [code]
    split <;> (try split) <;> decide
lemma masks (H : Region51 N C S D E j) {b : Nat} (top : code N C E {b} (N+j) = 2)
    {I : Finset Nat} (hb : b∈I) (t : Bool) :
    localVal N C E I t (N+j)=localVal N C E {b} t (N+j) := by
  have on : localVal N C E {b} false (N+j)=true := by
    dsimp only [code] at top
    split at top
    · assumption
    · split at top <;> contradiction
  have pulse : localVal N C E {b} t (N+j)=true := by cases t; exact on; exact ordered H _ on
  have both := local_mono H (I:={b}) (J:=I) (a:=t) (b:=t)
    (fun w _ hw => (Finset.mem_singleton.mp hw).symm ▸ hb) (fun _ _ h=>h) (N+j)
    (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩)) pulse
  exact both.trans pulse.symm
end PEqualNP.Outside.L_meta_25808_aux.Local
namespace PEqualNP.Outside.L_meta_25808_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Cone Cone.Profile
abbrev dist {m : Nat} (f g : Fin m → Bool) := (Finset.univ.filter (fun i => f i ≠ g i)).card
def near {n m} (G : Fin n → Fin m → Bool) (base : Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun a => dist (G a) base ≤ 2)
lemma near_small {n m} (G : Fin n → Fin m → Bool) (base : Fin m → Bool)
    (far : ∀a b, a≠b → 6 ≤ dist (G a) (G b)) : (near G base).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ne
  have incl : Finset.univ.filter (fun i=>G a i≠G b i) ⊆
      Finset.univ.filter (fun i=>G a i≠base i) ∪ Finset.univ.filter (fun i=>G b i≠base i) := by
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hi ⊢
    by_cases eq : G a i=base i
    · exact Or.inr (fun eqb=>hi (eq.trans eqb.symm))
    · exact Or.inl eq
  have count := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  have da := (Finset.mem_filter.mp ha).2
  have db := (Finset.mem_filter.mp hb).2
  have dl := far a b ne
  unfold dist at da db dl
  omega
variable {N : Nat} {C : Circuit} {S D E : Finset Nat} {j : Nat}
lemma exterior (H : Region51 N C S D E j) {I J : Finset Nat} (hI : I ⊆ S) (hJ : J ⊆ S)
    (z : Nat) (outside : z∉S) (eq : code N C E I (N+j) = code N C E J (N+j)) :
    world N C (insert z I) C.output = world N C (insert z J) C.output := by
  apply compare_worlds H (I:=I) (J:=J)
  · intro w hw
    simp [show w≠z from fun h=>outside (h ▸ hw)]
  · intro w hw
    simp [show w≠z from fun h=>outside (h ▸ hw)]
  · intro w _ hw
    simp [show w∉I from fun i=>hw (hI i),show w∉J from fun i=>hw (hJ i)]
  · exact same_code H eq
def palette (E : Finset Nat) : Finset Nat := if E=∅ then {0,2} else {0,1,2}
lemma palette_card (le : E.card ≤ 1) : (palette E).card = 2+E.card := by
  by_cases e : E=∅
  · simp [palette,e]
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr e)
    have one : E.card=1 := by omega
    simp [palette,e,one]
lemma key_injective {n m : Nat} (H : Region51 N C S D E j) (p : Fin n → Nat) (q : Fin m → Nat)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (rpin : ∀a∈R,p a∈S)
    (bpin : ∀v∉B,q v∉S) (G : Fin n → Fin m → Bool)
    (rep : ∀a v, G a v = world N C {q v,p a} C.output)
    (far : ∀a b,a≠b → 6≤dist (G a) (G b)) (size : R.card+B.card≤6) :
    Set.InjOn (fun a => code N C E {p a} (N+j)) (↑R : Set (Fin n)) := by
  intro a ha b hb eq
  by_contra ne
  have incl : Finset.univ.filter (fun v => G a v≠G b v) ⊆ B := by
    intro v hv
    by_contra out
    apply (Finset.mem_filter.mp hv).2
    rw [rep,rep]
    exact exterior H (Finset.singleton_subset_iff.mpr (rpin a ha))
      (Finset.singleton_subset_iff.mpr (rpin b hb)) (q v) (bpin v out) eq
  have hi := Finset.card_le_card incl
  have lo := far a b ne
  have non := Finset.card_pos.mpr (show R.Nonempty from ⟨a,ha⟩)
  unfold dist at lo
  omega
lemma bank_cap {n m : Nat} (H : Region51 N C S D E j) (p : Fin n → Nat) (q : Fin m → Nat)
    (R : Finset (Fin n)) (B : Finset (Fin m)) (rpin : ∀a∈R,p a∈S)
    (bpin : ∀v∉B,q v∉S) (G : Fin n → Fin m → Bool)
    (rep : ∀a v, G a v = world N C {q v,p a} C.output)
    (ri : Set.InjOn (fun a => code N C E {p a} (N+j)) (↑R : Set (Fin n)))
    (bi : Set.InjOn (fun v => code N C E {q v} (N+j)) (↑B : Set (Fin m))) :
    (R \ near G (fun v => world N C {q v} C.output)).card ≤ 1+E.card := by
  classical
  let kr := fun a => code N C E {p a} (N+j)
  let kc := fun v => code N C E {q v} (N+j)
  let zero := code N C E ∅ (N+j)
  let base := fun v => world N C {q v} C.output
  have rc (a) : kr a∈palette E := key_mem H _
  have cc (v) : kc v∈palette E := key_mem H _
  have baseMem : zero∈palette E := key_mem H _
  have colorSub : B.image kc ⊆ palette E := by
    intro z hz; obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hz; exact cc v
  have bcount := Finset.card_le_card colorSub
  rw [Finset.card_image_of_injOn bi, palette_card H.one] at bcount
  have matched (a) (ha : a∈R) (k0 : kr a=zero) : a∈near G base := by
    let diff := Finset.univ.filter (fun v=>G a v≠base v)
    have sub : diff⊆B := by
      intro v hv
      by_contra out
      apply (Finset.mem_filter.mp hv).2
      rw [rep]
      exact exterior H (Finset.singleton_subset_iff.mpr (rpin a ha)) (Finset.empty_subset _) _ (bpin v out) k0
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change diff.card≤2
    by_cases small : B.card≤2
    · exact (Finset.card_le_card sub).trans small
    · have cap := H.one
      have full : B.image kc=palette E := Finset.eq_of_subset_of_card_le colorSub (by
        rw [Finset.card_image_of_injOn bi,palette_card cap]; omega)
      have two : 2∈B.image kc := by rw [full]; unfold palette; split <;> decide
      obtain ⟨v,hv,top⟩:=Finset.mem_image.mp two
      have same : G a v=base v := by
        rw [rep]
        apply compare_worlds H (I:={q v,p a}) (J:={q v}) (fun _ _=>Iff.rfl) (fun _ _=>Iff.rfl)
        · intro w _ out
          simp [show w≠p a from fun e=>out (e.symm ▸ rpin a ha)]
        · exact masks H top (by simp)
      have without : diff⊆B.erase v := fun w h => Finset.mem_erase.mpr
        ⟨fun e => (Finset.mem_filter.mp h).2 (e.symm ▸ same), sub h⟩
      have bound := Finset.card_le_card without
      rw [Finset.card_erase_of_mem hv] at bound
      omega
  have sub : (R \ near G base).image kr ⊆ (palette E).erase zero := by
    intro k hk
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨inR,out⟩ := Finset.mem_sdiff.mp ha
    exact Finset.mem_erase.mpr ⟨fun z=>out (matched a inR z),rc a⟩
  have count := Finset.card_le_card sub
  rw [Finset.card_image_of_injOn (ri.mono (by intro a ha; exact (Finset.mem_sdiff.mp ha).1)),
    Finset.card_erase_of_mem baseMem,palette_card H.one] at count
  change (R \ near G base).card ≤ 1+E.card
  omega
end PEqualNP.Outside.L_meta_25808_aux.Local
namespace PEqualNP.Outside.L_meta_25808_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile Cone.Profile.Wire
def rowBase (n m : Nat) (C : Circuit) (v : Fin m) := world (n+m) C {n+v.val} C.output
def colBase (n m : Nat) (C : Circuit) (a : Fin n) := world (n+m) C {a.val} C.output
def marked {n m} (G : Fin n → Fin m → Bool) (C : Circuit) : Finset Nat :=
  srcSet (near G (rowBase n m C)) (near (fun v a=>G a v) (colBase n m C))
lemma on_pair {n m G C} (rep : Represents (n:=n) (m:=m) G C) (a : Fin n) (v : Fin m) :
    G a v = world (n+m) C {n+v.val,a.val} C.output := by
  rw [←rep a v,eval_eq_val,oneEach_pt]
  unfold world
  congr 2
  funext i
  apply Bool.eq_iff_iff.mpr
  simp only [pt,Bool.or_eq_true,decide_eq_true_eq,Finset.mem_insert,Finset.mem_singleton]
  exact or_comm
lemma namedRow {n m} (R : Finset (Fin n)) (B : Finset (Fin m)) (a : Fin n) :
    a.val∈srcSet R B ↔ a∈R := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with l|r
    · obtain ⟨a',ha,e⟩:=Finset.mem_image.mp l
      exact (Fin.ext e : a'=a) ▸ ha
    · obtain ⟨v,_,e⟩:=Finset.mem_image.mp r
      change n+v.val=a.val at e
      have:=a.isLt; omega
  · exact fun h=>Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
lemma namedCol {n m} (R : Finset (Fin n)) (B : Finset (Fin m)) (v : Fin m) :
    n+v.val∈srcSet R B ↔ v∈B := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with l|r
    · obtain ⟨a,_,e⟩:=Finset.mem_image.mp l
      change a.val=n+v.val at e
      have:=a.isLt; omega
    · obtain ⟨v',hv,e⟩:=Finset.mem_image.mp r
      exact (Fin.ext (Nat.add_left_cancel e) : v'=v) ▸ hv
  · exact fun h=>Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)
lemma small_regions {n m : Nat} {G : Fin n → Fin m → Bool} {C P E root} (R : Finset (Fin n)) (B : Finset (Fin m))
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w))
    (rep : Represents G C) (F : Frame (n+m) C P (srcSet R B) E root) (one : E.card≤1) :
    R.card+B.card≤6 := by
  rw [←srcCard]
  have cap {k : Nat} (low : k≤6) : WindowCap C P (srcSet R B) E k :=
    fun _ ht => forbiddenWindow (R:=R) (B:=B) cap51
      (fun a b h=>low.trans (dr a b h)) (fun v w h=>low.trans (dc v w h)) rep F ht
  by_cases em : E=∅
  · subst E
    exact (pure59 F (cap (k:=5) (by decide))).trans (by decide)
  · have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr em)
    obtain ⟨e,he⟩ := Finset.card_eq_one.mp (show E.card=1 by omega)
    subst E
    exact mixed62 F (cap (le_refl 6))
lemma local_cap {n m : Nat} {G : Fin n → Fin m → Bool} {C D E t} (R : Finset (Fin n)) (B : Finset (Fin m))
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (H : Region51 (n+m) C (srcSet R B) D E t) (size : R.card+B.card≤6) :
    (srcSet R B \ marked G C).card ≤ 2+2*E.card := by
  let p := fun a : Fin n=>a.val
  let q := fun v : Fin m=>n+v.val
  let T := fun v a=>G a v
  have inR a : a∈R → p a∈srcSet R B := (namedRow R B a).mpr
  have inC v : v∈B → q v∈srcSet R B := (namedCol R B v).mpr
  have outR a : a∉R → p a∉srcSet R B := mt (namedRow R B a).mp
  have outC v : v∉B → q v∉srcSet R B := mt (namedCol R B v).mp
  have pval (a v) : G a v=world (n+m) C {q v,p a} C.output := on_pair rep a v
  have qval (v a) : T v a=world (n+m) C {p a,q v} C.output := by
    rw [Finset.pair_comm]; exact pval a v
  have kr := key_injective H p q R B inR outC G pval dr size
  have kc := key_injective H q p B R inC outR T qval dc (by omega)
  have first := bank_cap H p q R B inR outC G pval kr kc
  have last := bank_cap H q p B R inC outR T qval kc kr
  let X := near G (rowBase n m C)
  let Y := near T (colBase n m C)
  change (R \ X).card≤1+E.card at first
  change (B \ Y).card≤1+E.card at last
  have sub : srcSet R B \ marked G C ⊆ srcSet (R \ X) (B \ Y) := by
    intro w hw
    obtain ⟨inside,out⟩:=Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp inside with left|right
    · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp left
      exact (namedRow _ _ a).mpr (Finset.mem_sdiff.mpr ⟨ha,fun h=>out ((namedRow X Y a).mpr h)⟩)
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp right
      exact (namedCol _ _ v).mpr (Finset.mem_sdiff.mpr ⟨hv,fun h=>out ((namedCol X Y v).mpr h)⟩)
  have bound:=Finset.card_le_card sub
  rw [srcCard] at bound
  omega
lemma split_sources {n m : Nat} {S : Finset Nat} (small : ∀w∈S,w<n+m) :
    ∃(R : Finset (Fin n)) (B : Finset (Fin m)), S=srcSet R B := by
  let R:=Finset.univ.filter (fun a : Fin n=>a.val∈S)
  let B:=Finset.univ.filter (fun v : Fin m=>n+v.val∈S)
  refine ⟨R,B,?_⟩
  ext w
  by_cases lo : w<n
  · change (⟨w,lo⟩ : Fin n).val∈S ↔ (⟨w,lo⟩ : Fin n).val∈srcSet R B
    exact (show w∈S ↔ (⟨w,lo⟩ : Fin n) ∈ R by simp [R]).trans (namedRow R B ⟨w,lo⟩).symm
  · by_cases hi : w<n+m
    · let v : Fin m:=⟨w-n,by omega⟩
      have eq : n+v.val=w := by dsimp [v]; omega
      rw [←eq, namedCol]
      simp [B]
    · exact iff_of_false (fun h=>hi (small w h)) (fun h=>hi (srcLow R B w h))
lemma frame_cap {n m : Nat} {G : Fin n → Fin m → Bool} {C P S E root} (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (F : Frame (n+m) C P S E root) (one : E.card≤1) : (S \ marked G C).card ≤ 2+2*E.card := by
  classical
  by_cases high : n+m≤root
  · obtain ⟨R,B,shape⟩ := split_sources F.low
    subst S
    let N := n+m
    let S := srcSet R B
    let E' := subsetAt N C P E root
    let P' := gateSubset N C P root
    have ecount : E'.card≤E.card := Finset.card_le_card (Finset.filter_subset _ _)
    have back := subtree_boundary F F.rootIn high
    dsimp only at back
    rw [rootLeaves F] at back
    obtain ⟨sub,mem,entries,gates,out,raw,inner⟩ := back
    have eq : N+(root-N)=root := Nat.add_sub_of_le high
    have H : Region51 N C S P' E' (root-N) := by
      refine ⟨F.back,F.low,sub,mem,ecount.trans one,?_,gates,?_,raw,?_⟩
      · simpa only [eq,E',S,P',inner51,N] using entries
      · simpa only [eq,E',S,P',inner51,N] using out
      · simpa only [eq,E',S,P',inner51,N] using inner
    have lim := local_cap R B dr dc rep H (small_regions R B dr dc rep F one)
    omega
  · have sz := leaves_one_of_low F (top:=root) (by omega)
    rw [rootLeaves F] at sz
    have le := Finset.card_le_card (show S \ marked G C ⊆ S from Finset.sdiff_subset)
    omega
end PEqualNP.Outside.L_meta_25808_aux.Local
namespace PEqualNP.Outside.L_meta_25808_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile Cone.Profile.Wire
lemma unread_world {N : Nat} {C : Circuit} (back : ReadsBack N C) {p : Nat}
    (off : Normal.Active C p=0) {X Y : Finset Nat} (same : ∀w, w≠p → (w∈X ↔ w∈Y)) :
    ∀w, w≠p → world N C X w=world N C Y w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro ne
    by_cases low : w<N
    · simp only [world_raw low,same w ne]
    by_cases high : N+C.size≤w
    · rw [world_past high,world_past high]
    have k : w-N<C.size := by omega
    have eq : N+(w-N)=w := by omega
    have h (v) (hv : v∈(gateAt C (w-N)).inputs) : world N C X v=world N C Y v := by
      have active := Normal.wire_positive k hv
      have earlier := back (w-N) k v hv
      apply ih v (by omega)
      rintro rfl; omega
    have left := world_step (X:=X) back (w-N) k
    have right := world_step (X:=Y) back (w-N) k
    rw [eq] at left right
    rw [left,right,List.map_congr_left h]
lemma unread_marked {n m : Nat} {G : Fin n→Fin m→Bool} {C : Circuit}
    (back : ReadsBack (n+m) C) (rep : Represents G C) (high : n+m≤C.output)
    {w : Nat} (hw : w<n+m) (off : Normal.Active C w=0) : w∈marked G C := by
  by_cases row : w<n
  · let a : Fin n := ⟨w,row⟩
    apply (namedRow _ _ a).mpr
    have eq (v : Fin m) : G a v=rowBase n m C v := by
      rw [on_pair rep]
      apply unread_world back off _ _ (by omega)
      intro z ne
      simp [a,ne]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [dist,eq]⟩
  · let v : Fin m := ⟨w-n,by omega⟩
    have p : n+v.val=w := by dsimp [v]; omega
    rw [←p]
    apply (namedCol _ _ v).mpr
    have eq (a : Fin n) : G a v=colBase n m C a := by
      rw [on_pair rep]
      apply unread_world back off _ _ (by omega)
      intro z ne
      simp [p,ne]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [dist,eq]⟩
lemma apply_tree {n m : Nat} {G : Fin n→Fin m→Bool} {C : Circuit}
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (back : ReadsBack (n+m) C) {O S E : Finset Nat} (one : E.card≤1)
    (gates : O⊆Finset.range C.size) (small : ∀w∈S,w<n+m)
    (tree : ∃(P : Finset Nat) (root : Nat), let wires := nodes (n+m) P S
      P⊆O ∧ root∈wires ∧ readsIn C P root=0 ∧
      (∀e∈E,e∉wires ∧ e<root ∧ readsIn C P e=1) ∧
      (∀k∈P, ((gateAt C k).op=.and ∨ (gateAt C k).op=.or) ∧ (gateAt C k).inputs.length=2 ∧
        ∀w∈(gateAt C k).inputs,w∈wires ∨ w∈E) ∧
      ∀w∈wires,w≠root → readsIn C P w=1 ∧ Normal.Active C w=1 ∧ C.output≠w) :
    (S \ marked G C).card≤2+2*E.card := by
  obtain ⟨P,root,sub,loc,z,ent,shape,once⟩ := tree
  exact frame_cap dr dc rep (show Frame (n+m) C P S E root from ⟨small,back,sub.trans gates,loc,
    fun e h=>(ent e h).1,fun e h=>(ent e h).2.2,shape,z,once⟩) one
lemma live_bound {n m : Nat} {G : Fin n→Fin m→Bool} {C : Circuit}
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b)) (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w))
    (rep : Represents G C) (back : ReadsBack (n+m) C)
    (shape : ∀g∈C.gates, ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1))
    (pos : 0<C.size) (out : C.output+1=n+m+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<Normal.Active C (n+m+j)) : 21*(n+m)≤20*C.size+64 := by
  classical
  let N:=n+m
  let H:=marked G C
  let used:=(Finset.range N).filter (fun w=>0<Normal.Active C w)
  let neg := @Finset.filter Nat (fun k=>(gateAt C k).op=.not) (fun _=>Classical.propDecidable _) (Finset.range C.size)
  have high : N≤C.output := by dsimp [N]; omega
  have marksize : H.card≤2 := by
    change (srcSet _ _).card≤2
    rw [srcCard]
    have a := near_small G (rowBase n m C) dr
    have b := near_small (fun v a=>G a v) (colBase n m C) dc
    omega
  have marklow : H⊆Finset.range N := fun w hw=>Finset.mem_range.mpr (srcLow _ _ w hw)
  have missing (w) (hw : w<N) (off : Normal.Active C w=0) : w∈H := unread_marked back rep high hw off
  have population : N≤used.card+H.card := by
    have sub : Finset.range N ⊆ used∪H := by
      intro w hw
      by_cases h : 0<Normal.Active C w
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,h⟩)
      · exact Finset.mem_union_right _ (missing w (Finset.mem_range.mp hw) (by omega))
    simpa only [Finset.card_range] using (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have count := weighted N C shape back pos out live 2 4 H (by decide) marklow missing
    (by
      intro S low tree
      have cap := apply_tree dr dc rep back (E:=∅) (by simp) (Finset.filter_subset _ _)
        (fun w hw=>Finset.mem_range.mp (Finset.mem_filter.mp (low hw)).1) tree
      simpa only [Finset.card_empty,Nat.mul_zero,Nat.add_zero] using cap)
    (by
      intro S b low tree
      have cap := apply_tree dr dc rep back (E:={b}) (by simp) (Finset.filter_subset _ _)
        (fun w hw=>Finset.mem_range.mp (Finset.mem_filter.mp (low hw)).1) tree
      simpa only [Finset.card_singleton] using cap)
  obtain ⟨usedBound,pieces⟩:=count
  change used.card≤C.size-neg.card+1 at usedBound
  have pressure : N≤20*(C.size-neg.card+1-used.card)+10*neg.card+2+H.card :=
    (Nat.le_add_right _ _).trans pieces
  have negBound : neg.card≤C.size := by
    have h := Finset.card_le_card (show neg ⊆ Finset.range C.size from Finset.filter_subset _ _)
    simpa only [Finset.card_range] using h
  change 21*N≤20*C.size+64
  omega
lemma variation {n m : Nat} (G : Fin n→Fin m→Bool) (h : 2≤n)
    (far : ∀a b,a≠b → 6≤dist (G a) (G b)) : 6≤m ∧ ∃a b v,G a v≠G b v := by
  let a : Fin n := ⟨0,by omega⟩
  let b : Fin n := ⟨1,by omega⟩
  have low := far a b (by intro eq; have:=congrArg Fin.val eq; contradiction)
  let F := Finset.univ.filter (fun v=>G a v≠G b v)
  change 6≤F.card at low
  have upper := Finset.card_le_card (show F⊆Finset.univ from Finset.subset_univ _)
  rw [Finset.card_univ,Fintype.card_fin] at upper
  obtain ⟨v,hv⟩ := Finset.card_pos.mp (show 0<F.card by omega)
  exact ⟨low.trans upper,a,b,v,(Finset.mem_filter.mp hv).2⟩
lemma total {n m : Nat} (G : Fin n → Fin m → Bool) (C : Circuit)
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b)) (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w))
    (fan : FanInTwo C) (rep : Represents G C) : 21*(n+m)≤20*C.size+64 := by
  by_cases tiny : n+m≤3
  · omega
  have n2 : 2≤n := by
    by_contra! bad
    have := (variation (fun v a=>G a v) (by omega) dc).1
    omega
  obtain ⟨lots,vert⟩:=variation G n2 dr
  obtain ⟨_,v,w,a,diff⟩:=variation (fun v a=>G a v) (by omega) dc
  obtain ⟨D,sz,repD,back,shape,pos,out,live⟩:=Normal.normalized C fan rep ⟨a,v,w,diff⟩ vert
  have lower:=live_bound dr dc repD back shape pos out live
  omega
end PEqualNP.Outside.L_meta_25808_aux.Local
namespace PEqualNP.Outside.L_meta_25808_aux.Packing
variable {α : Type} [Fintype α] [DecidableEq α]
def ends (F : Finset (α×α)) := F.image Prod.fst ∪ F.image Prod.snd
def matching (rel : α → α → Prop) (F : Finset (α×α)) : Prop :=
  (∀e∈F,e.1≠e.2 ∧ rel e.1 e.2) ∧ ∀e∈F,∀f∈F,e≠f →
    e.1≠f.1 ∧ e.1≠f.2 ∧ e.2≠f.1 ∧ e.2≠f.2
lemma ends_size (F : Finset (α×α)) : (ends F).card≤2*F.card := by
  have a:=Finset.card_image_le (s:=F) (f:=Prod.fst)
  have b:=Finset.card_image_le (s:=F) (f:=Prod.snd)
  have c:=Finset.card_union_le (F.image Prod.fst) (F.image Prod.snd)
  change (F.image Prod.fst ∪ F.image Prod.snd).card≤2*F.card
  omega
lemma ends_insert (a b : α) (F : Finset (α×α)) : ends (insert (a,b) F) = insert a (insert b (ends F)) := by
  unfold ends
  ext w
  simp only [Finset.image_insert,Finset.mem_union,Finset.mem_insert]
  tauto
lemma append_edge {F : Finset (α×α)} {rel : α→α→Prop} (old : matching rel F)
    {a b : α} (freshA : a∉ends F) (freshB : b∉ends F) (ab : a≠b) (edge : rel a b) :
    matching rel (insert (a,b) F) := by
  have away {x : α} (h : x∉ends F) {e : α×α} (he : e∈F) : x≠e.1 ∧ x≠e.2 := by
    refine ⟨fun eq=>h (eq ▸ Finset.mem_union_left _ (Finset.mem_image_of_mem _ he)),
      fun eq=>h (eq ▸ Finset.mem_union_right _ (Finset.mem_image_of_mem _ he))⟩
  constructor
  · intro e he
    rcases Finset.mem_insert.mp he with rfl|prior
    · exact ⟨ab,edge⟩
    · exact old.1 e prior
  · intro e he f hf diff
    rcases Finset.mem_insert.mp he with rfl|oldE <;> rcases Finset.mem_insert.mp hf with rfl|oldF
    · exact (diff rfl).elim
    · exact ⟨(away freshA oldF).1,(away freshA oldF).2,(away freshB oldF).1,(away freshB oldF).2⟩
    · exact ⟨(away freshA oldE).1.symm,(away freshB oldE).1.symm,(away freshA oldE).2.symm,(away freshB oldE).2.symm⟩
    · exact old.2 _ oldE _ oldF diff
lemma edge_new {a b : α} {F : Finset (α×α)} (aNew : a∉ends F) : (a,b)∉F :=
  fun h=>aNew (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))

lemma cover {n h : Nat} (rel : Fin n → Fin n → Prop) (U : Finset (Fin n)) (many : 2*h+2≤n)
    (single : U.card≤1) (unread : ∀a∈U,∀b,a≠b → rel a b)
    (bounded : ∀F,matching rel F → F.card≤h) :
    ∃H : Finset (Fin n), U⊆H ∧ H.card+U.card≤2*h ∧
      ∀a∉H,∀b∉H,a≠b → ¬rel a b := by
  classical
  let choices := Finset.univ.filter (fun F : Finset (Fin n×Fin n) => matching rel F ∧ Disjoint (ends F) U)
  have ex : choices.Nonempty := by refine ⟨∅,?_⟩; simp [choices,matching,ends]
  obtain ⟨F,hF,best⟩:=Finset.exists_max_image choices Finset.card ex
  obtain ⟨ok,apart⟩:=(Finset.mem_filter.mp hF).2
  let H := ends F ∪ U
  have free {a : Fin n} (outside : a∉H) : a∉ends F ∧ a∉U :=
    ⟨fun inF=>outside (Finset.mem_union_left _ inF),fun inU=>outside (Finset.mem_union_right _ inU)⟩
  have base := bounded F ok
  have counts := ends_size F
  have cost := Finset.card_union_le (ends F) U
  change H.card ≤ (ends F).card+U.card at cost
  refine ⟨H,Finset.subset_union_right,?_,?_⟩
  · by_cases empty : U=∅
    · rw [empty,Finset.card_empty] at cost ⊢; omega
    · obtain ⟨a,ha⟩:=Finset.nonempty_iff_ne_empty.mpr empty
      have aNew : a∉ends F := fun k=>Finset.disjoint_left.mp apart k ha
      have avail : Hᶜ.Nonempty := by
        apply Finset.card_pos.mp
        have total:=Finset.card_add_card_compl H
        rw [Fintype.card_fin] at total
        omega
      obtain ⟨b,hb⟩:=avail
      have bOut:=Finset.mem_compl.mp hb
      have distinct : a≠b := fun eq=>(free bOut).2 (eq ▸ ha)
      have enlarged:=bounded _ (append_edge ok aNew (free bOut).1 distinct (unread a ha b distinct))
      rw [Finset.card_insert_of_notMem (edge_new aNew)] at enlarged
      omega
  · intro a ha b hb ne edge
    have m := append_edge ok (free ha).1 (free hb).1 ne edge
    have dis : Disjoint (ends (insert (a,b) F)) U := by
      rw [ends_insert]
      refine Finset.disjoint_left.mpr ?_
      intro x hx hxU
      rcases Finset.mem_insert.mp hx with rfl|rest
      · exact (free ha).2 hxU
      rcases Finset.mem_insert.mp rest with rfl|part
      · exact (free hb).2 hxU
      · exact Finset.disjoint_left.mp apart part hxU
    have hl := best _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,m,dis⟩)
    rw [Finset.card_insert_of_notMem (edge_new (free ha).1)] at hl
    omega
end PEqualNP.Outside.L_meta_25808_aux.Packing
namespace PEqualNP.Outside.L_meta_25808_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile
variable {N : Nat} {C : Circuit} {S D E : Finset Nat} {j : Nat}
lemma around (H : Region51 N C S D E j) {X Y : Finset Nat}
    (agree : ∀w<N,w∉S → (w∈X ↔ w∈Y)) :
    ∀w,w∉S → (inner51 N D w → w=N+j) →
      (N+j≤w → world N C X (N+j)=world N C Y (N+j)) → world N C X w=world N C Y w :=
  outside51 H (world N C X) (world N C Y)
    (fun w low ns=>by simp only [world_raw low,agree w low ns])
    (fun k hk h=>by rw [world_step H.back k hk,world_step H.back k hk,List.map_congr_left h])
    (fun w hi=>(world_past hi).trans (world_past hi).symm)
lemma exterior_state (H : Region51 N C S D E j) (z : Nat) (out : z∉S) :
    ∃t : Bool, ∀I J : Finset Nat, I⊆S → J⊆S →
      localVal N C E I t (N+j)=localVal N C E J t (N+j) →
      world N C (insert z I) C.output=world N C (insert z J) C.output := by
  obtain ⟨t,raw⟩ : ∃t : Bool, ∀w∈E,world N C {z} w=t := by
    by_cases non : E.Nonempty
    · obtain ⟨w,hw⟩:=non
      exact ⟨world N C {z} w,fun e he=>congrArg (world N C {z}) (Finset.card_le_one.mp H.one e he w hw)⟩
    · exact ⟨false,fun e he=>(non ⟨e,he⟩).elim⟩
  have outside {I : Finset Nat} (inc : I⊆S) {w} (hw : w∉S) : w∈insert z I ↔ w=z := by
    simp [show w∉I from fun h=>hw (inc h)]
  have inside (I : Finset Nat) (w) (hw : w∈S) : w∈insert z I ↔ w∈I := by
    simp [show w≠z from fun h=>out (h ▸ hw)]
  have response (I : Finset Nat) (inc : I⊆S) :
      world N C (insert z I) (N+j)=localVal N C E I t (N+j) := by
    apply agrees_inside H _ _ _ (inside I) _ _ (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩))
    intro e he
    obtain ⟨before,ns,away⟩:=H.entries e he
    have cmp:=around H (X:=insert z I) (Y:={z}) (fun w _ hw => (outside inc hw).trans Finset.mem_singleton.symm)
    exact (cmp e ns (fun a=>(away a).elim) (fun h=>(Nat.not_le_of_gt before h).elim)).trans (raw e he)
  refine ⟨t,?_⟩
  intro I J hi hj eq
  exact around H (fun w _ hw=>(outside hi hw).trans (outside hj hw).symm) _ H.outS H.outD
    (fun _=>(response I hi).trans (eq.trans (response J hj).symm))
lemma le_code (H : Region51 N C S D E j) {I J : Finset Nat}
    (le : code N C E I (N+j)≤code N C E J (N+j)) (t : Bool) :
    localVal N C E I t (N+j)=true → localVal N C E J t (N+j)=true := by
  have u:=ordered H I; have v:=ordered H J
  dsimp only [code] at le
  cases t <;> cases a:localVal N C E I false (N+j) <;> cases b:localVal N C E I true (N+j) <;>
    cases c:localVal N C E J false (N+j) <;> cases d:localVal N C E J true (N+j) <;> simp_all
def affordable {n m} (G : Fin n→Fin m→Bool) (base : Fin m→Bool) (a b : Fin n) :=
  (Finset.univ.filter (fun v=>G a v≠G b v ∧ G a v≠base v)).card≤3
lemma relative_pair {n m : Nat} (H : Region51 N C S D E j) (p : Fin n→Nat) (q : Fin m→Nat)
    (G : Fin n→Fin m→Bool) (rep : ∀a v,G a v=world N C {q v,p a} C.output)
    (B : Finset (Fin m)) (bpin : ∀v∉B,q v∉S) (bound : B.card≤3)
    (a b : Fin n) (ha : p a∈S) (hb : p b∈S) (order : code N C E {p a} (N+j) ≤ code N C E {p b} (N+j)) :
    affordable G (fun v=>world N C {q v} C.output) a b := by
  unfold affordable
  apply le_trans (Finset.card_le_card ?_) bound
  intro v hv
  by_contra outside
  obtain ⟨t,cmp⟩:=exterior_state H (q v) (bpin v outside)
  obtain ⟨different,above⟩:=(Finset.mem_filter.mp hv).2
  have start:=local_mono H (I:=∅) (J:={p a}) (a:=t) (b:=t)
    (fun w _ h=>(Finset.notMem_empty w h).elim) (fun _ _ h=>h) (N+j) (Or.inr (Or.inl ⟨by omega,by simpa using H.topMem⟩))
  have finish:=le_code H order t
  have options : localVal N C E {p a} t (N+j)=localVal N C E ∅ t (N+j) ∨
      localVal N C E {p a} t (N+j)=localVal N C E {p b} t (N+j) := by
    cases l:localVal N C E ∅ t (N+j) <;> cases m:localVal N C E {p a} t (N+j) <;>
      cases r:localVal N C E {p b} t (N+j) <;> simp_all
  rcases options with low|high
  · exact above ((rep a v).trans (cmp _ ∅ (Finset.singleton_subset_iff.mpr ha) (Finset.empty_subset _) low))
  · exact different ((rep a v).trans ((cmp _ _ (Finset.singleton_subset_iff.mpr ha)
      (Finset.singleton_subset_iff.mpr hb) high).trans (rep b v).symm))
end PEqualNP.Outside.L_meta_25808_aux.Local
namespace PEqualNP.Outside.L_meta_25808_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile Cone.Profile.Wire
lemma pair_cap {n m : Nat} {G : Fin n → Fin m → Bool} {C D E t} (R : Finset (Fin n)) (B : Finset (Fin m))
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (H : Region51 (n+m) C (srcSet R B) D E t) (size : R.card+B.card≤6)
    (MR : Finset (Fin n)) (MC : Finset (Fin m))
    (blockR : ∀a∉MR,∀b∉MR,a≠b → ¬affordable G (rowBase n m C) a b)
    (blockC : ∀a∉MC,∀b∉MC,a≠b → ¬affordable (fun v i=>G i v) (colBase n m C) a b) :
    (srcSet R B \ srcSet MR MC).card ≤ 2 := by
  let p := fun a : Fin n=>a.val
  let q := fun v : Fin m=>n+v.val
  let T := fun v a=>G a v
  have inR a : a∈R → p a∈srcSet R B := (namedRow R B a).mpr
  have inC v : v∈B → q v∈srcSet R B := (namedCol R B v).mpr
  have outR a : a∉R → p a∉srcSet R B := mt (namedRow R B a).mp
  have outC v : v∉B → q v∉srcSet R B := mt (namedCol R B v).mp
  have pval (a v) : G a v=world (n+m) C {q v,p a} C.output := on_pair rep a v
  have qval (v a) : T v a=world (n+m) C {p a,q v} C.output := by
    rw [Finset.pair_comm]; exact pval a v
  have kr := key_injective H p q R B inR outC G pval dr size
  have kc := key_injective H q p B R inC outR T qval dc (by omega)
  have card_bound {k : Nat} (A : Finset (Fin k)) (key : Fin k→Nat) (inj : Set.InjOn key (↑A : Set (Fin k)))
      (mem : ∀i,key i∈palette E) : A.card≤3 := by
    have inside : A.image key⊆palette E := by
      intro t ht; obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ht; exact mem i
    have count:=Finset.card_le_card inside
    rw [Finset.card_image_of_injOn inj,palette_card H.one] at count
    have:=H.one; omega
  have rcount:=card_bound R _ kr (fun a=>key_mem H _)
  have ccount:=card_bound B _ kc (fun v=>key_mem H _)
  have independent {i k : Nat} (U : Finset (Fin i)) (V : Finset (Fin k)) (p' : Fin i→Nat) (q' : Fin k→Nat)
      (A : Fin i→Fin k→Bool) (names : Finset (Fin i))
      (wires : ∀a∈U,p' a∈srcSet R B) (away : ∀v∉V,q' v∉srcSet R B) (csmall : V.card≤3)
      (agrees : ∀a v,A a v=world (n+m) C {q' v,p' a} C.output)
      (blocked : ∀a∉names,∀b∉names,a≠b → ¬affordable A (fun v=>world (n+m) C {q' v} C.output) a b) :
      (U \ names).card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨inA,outA⟩:=Finset.mem_sdiff.mp ha
    obtain ⟨inB,outB⟩:=Finset.mem_sdiff.mp hb
    by_contra ne
    rcases le_total (code (n+m) C E {p' a} ((n+m)+t)) (code (n+m) C E {p' b} ((n+m)+t)) with le|le
    · exact blocked a outA b outB ne (relative_pair H p' q' A agrees V away csmall a b (wires a inA) (wires b inB) le)
    · exact blocked b outB a outA (Ne.symm ne) (relative_pair H p' q' A agrees V away csmall b a (wires b inB) (wires a inA) le)
  have first:=independent R B p q G MR inR outC ccount pval blockR
  have last:=independent B R q p T MC inC outR rcount qval blockC
  have sub : srcSet R B \ srcSet MR MC ⊆ srcSet (R \ MR) (B \ MC) := by
    intro w hw
    obtain ⟨inside,out⟩:=Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp inside with left|right
    · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp left
      exact (namedRow _ _ a).mpr (Finset.mem_sdiff.mpr ⟨ha,fun h=>out ((namedRow MR MC a).mpr h)⟩)
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp right
      exact (namedCol _ _ v).mpr (Finset.mem_sdiff.mpr ⟨hv,fun h=>out ((namedCol MR MC v).mpr h)⟩)
  have bound:=Finset.card_le_card sub
  rw [srcCard] at bound
  omega
lemma pair_frame {n m : Nat} {G : Fin n → Fin m → Bool} {C P S E root} (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (F : Frame (n+m) C P S E root) (one : E.card≤1)
    (MR : Finset (Fin n)) (MC : Finset (Fin m))
    (blockR : ∀a∉MR,∀b∉MR,a≠b → ¬affordable G (rowBase n m C) a b)
    (blockC : ∀a∉MC,∀b∉MC,a≠b → ¬affordable (fun v i=>G i v) (colBase n m C) a b) :
    (S \ srcSet MR MC).card ≤ 2 := by
  classical
  by_cases high : n+m≤root
  · obtain ⟨R,B,shape⟩ := split_sources F.low
    subst S
    let N := n+m
    let S := srcSet R B
    let E' := subsetAt N C P E root
    let P' := gateSubset N C P root
    have ecount : E'.card≤E.card := Finset.card_le_card (Finset.filter_subset _ _)
    have back := subtree_boundary F F.rootIn high
    dsimp only at back
    rw [rootLeaves F] at back
    obtain ⟨sub,mem,entries,gates,out,raw,inner⟩ := back
    have eq : N+(root-N)=root := Nat.add_sub_of_le high
    have H : Region51 N C S P' E' (root-N) := by
      refine ⟨F.back,F.low,sub,mem,ecount.trans one,?_,gates,?_,raw,?_⟩
      · simpa only [eq,E',S,P',inner51,N] using entries
      · simpa only [eq,E',S,P',inner51,N] using out
      · simpa only [eq,E',S,P',inner51,N] using inner
    exact pair_cap R B dr dc rep H (small_regions R B dr dc rep F one) MR MC blockR blockC
  · have sz := leaves_one_of_low F (top:=root) (by omega)
    rw [rootLeaves F] at sz
    have le := Finset.card_le_card (show S \ srcSet MR MC ⊆ S from Finset.sdiff_subset)
    omega
end PEqualNP.Outside.L_meta_25808_aux.Local
namespace PEqualNP.Outside.L_meta_25808_aux.Local
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents
open Cone Cone.Profile Cone.Profile.Wire
lemma pair_tree {n m : Nat} {G : Fin n→Fin m→Bool} {C : Circuit}
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b))
    (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w)) (rep : Represents G C)
    (back : ReadsBack (n+m) C) {O S E : Finset Nat} (one : E.card≤1)
    (gates : O⊆Finset.range C.size) (small : ∀w∈S,w<n+m)
    (MR : Finset (Fin n)) (MC : Finset (Fin m))
    (blockR : ∀a∉MR,∀b∉MR,a≠b → ¬affordable G (rowBase n m C) a b)
    (blockC : ∀a∉MC,∀b∉MC,a≠b → ¬affordable (fun v i=>G i v) (colBase n m C) a b)
    (tree : ∃(P : Finset Nat) (root : Nat), let wires := nodes (n+m) P S
      P⊆O ∧ root∈wires ∧ readsIn C P root=0 ∧
      (∀e∈E,e∉wires ∧ e<root ∧ readsIn C P e=1) ∧
      (∀k∈P, ((gateAt C k).op=.and ∨ (gateAt C k).op=.or) ∧ (gateAt C k).inputs.length=2 ∧
        ∀w∈(gateAt C k).inputs,w∈wires ∨ w∈E) ∧
      ∀w∈wires,w≠root → readsIn C P w=1 ∧ Normal.Active C w=1 ∧ C.output≠w) :
    (S \ srcSet MR MC).card≤2 := by
  obtain ⟨P,root,sub,loc,z,ent,shape,once⟩ := tree
  exact pair_frame dr dc rep (show Frame (n+m) C P S E root from ⟨small,back,sub.trans gates,loc,
    fun e h=>(ent e h).1,fun e h=>(ent e h).2.2,shape,z,once⟩) one MR MC blockR blockC
lemma paired_live {n m hr hc : Nat} (G : Fin n→Fin m→Bool) (C : Circuit)
    (hsR : 2*hr+2≤n) (hsC : 2*hc+2≤m)
    (dr : ∀a b,a≠b → 6≤dist (G a) (G b)) (dc : ∀v w,v≠w → 6≤dist (fun a=>G a v) (fun a=>G a w))
    (br : ∀off F,Packing.matching (affordable G off) F → F.card≤hr)
    (bc : ∀off F,Packing.matching (affordable (fun v a=>G a v) off) F → F.card≤hc)
    (rep : Represents G C) (back : ReadsBack (n+m) C)
    (shape : ∀g∈C.gates, ((g.op=.and ∨ g.op=.or) ∧ g.inputs.length=2) ∨ (g.op=.not ∧ g.inputs.length=1))
    (pos : 0<C.size) (out : C.output+1=n+m+C.size)
    (live : ∀j<C.size,j+1<C.size → 0<Normal.Active C (n+m+j)) :
    13*(n+m)≤12*C.size+36+2*(hr+hc) := by
  classical
  let N:=n+m
  let UR:=Finset.univ.filter (fun a : Fin n=>Normal.Active C a.val=0)
  let UC:=Finset.univ.filter (fun v : Fin m=>Normal.Active C (n+v.val)=0)
  let T:=fun v a=>G a v
  let used:=(Finset.range N).filter (fun w=>0<Normal.Active C w)
  let neg := @Finset.filter Nat (fun k=>(gateAt C k).op=.not) (fun _=>Classical.propDecidable _) (Finset.range C.size)
  have high : N≤C.output := by dsimp [N]; omega
  have missR (a) (ha : a∈UR) : G a=rowBase n m C := by
    have off:Normal.Active C a.val=0 := (Finset.mem_filter.mp ha).2
    funext v
    rw [on_pair rep]
    apply unread_world back off _ _ (by dsimp [N] at high; have:=a.isLt; omega)
    intro z ne; simp [ne]
  have missC (v) (hv : v∈UC) : T v=colBase n m C := by
    have off:Normal.Active C (n+v.val)=0 := (Finset.mem_filter.mp hv).2
    funext a
    change G a v=_
    rw [on_pair rep]
    apply unread_world back off _ _ (by dsimp [N] at high; have:=v.isLt; omega)
    intro z ne; simp [ne]
  have extras {i k : Nat} (A : Fin i→Fin k→Bool) (base : Fin k→Bool) (U : Finset (Fin i))
      (same : ∀a∈U,A a=base) (far : ∀a b,a≠b → 6≤dist (A a) (A b)) :
      U.card≤1 ∧ ∀a∈U,∀b,a≠b → affordable A base a b := by
    have sub : U⊆near A base := fun a ha=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [dist,same a ha]⟩
    exact ⟨(Finset.card_le_card sub).trans (near_small A base far),fun a ha b _=>by simp [affordable,same a ha]⟩
  obtain ⟨ur,rEdges⟩:=extras G _ UR missR dr
  obtain ⟨uc,cEdges⟩:=extras T _ UC missC dc
  obtain ⟨MR,rm,rCost,rBlock⟩:=Packing.cover _ UR hsR ur rEdges (br _)
  obtain ⟨MC,cm,cCost,cBlock⟩:=Packing.cover _ UC hsC uc cEdges (bc _)
  let H:=srcSet MR MC
  have missing {w : Nat} (hw : w<N) (off : Normal.Active C w=0) : w∈srcSet UR UC := by
    by_cases lo : w<n
    · exact (namedRow UR UC ⟨w,lo⟩).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,off⟩)
    · let v : Fin m:=⟨w-n,by dsimp [N] at hw; omega⟩
      have add : n+v.val=w := by dsimp [v]; omega
      rw [←add]
      exact (namedCol UR UC v).mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,add.symm ▸ off⟩)
  have included : srcSet UR UC ⊆ H := by
    intro w ht
    rcases Finset.mem_union.mp ht with row|col
    · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp row
      exact (namedRow MR MC a).mpr (rm ha)
    · obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp col
      exact (namedCol MR MC v).mpr (cm hv)
  have population : N≤used.card+(UR.card+UC.card) := by
    have sub : Finset.range N ⊆ used ∪ srcSet UR UC := by
      intro w hw
      by_cases h : 0<Normal.Active C w
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw,h⟩)
      · exact Finset.mem_union_right _ (missing (Finset.mem_range.mp hw) (by omega))
    simpa only [srcCard,Finset.card_range] using (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  have count := weighted N C shape back pos out live 2 2 H (by decide)
    (fun w h=>Finset.mem_range.mpr (srcLow MR MC w h)) (fun _ hw off=>included (missing hw off))
    (by
      intro S low tree
      exact pair_tree dr dc rep back (E:=∅) (by simp) (Finset.filter_subset _ _)
        (fun w hw=>Finset.mem_range.mp (Finset.mem_filter.mp (low hw)).1) MR MC rBlock cBlock tree)
    (by
      intro S b low tree
      exact pair_tree dr dc rep back (E:={b}) (by simp) (Finset.filter_subset _ _)
        (fun w hw=>Finset.mem_range.mp (Finset.mem_filter.mp (low hw)).1) MR MC rBlock cBlock tree)
  obtain ⟨usedBound,pieces⟩:=count
  change used.card≤C.size-neg.card+1 at usedBound
  have pressure : N≤12*(C.size-neg.card+1-used.card)+6*neg.card+2+H.card := (Nat.le_add_right _ _).trans pieces
  have hEq : H.card=MR.card+MC.card:=srcCard MR MC
  have negBound : neg.card≤C.size := by
    have h := Finset.card_le_card (show neg ⊆ Finset.range C.size from Finset.filter_subset _ _)
    simpa only [Finset.card_range] using h
  change 13*N≤12*C.size+36+2*(hr+hc)
  omega
theorem comparison_bound : (∀ (n m hr hc : ℕ) (G : Fin n → Fin m → Bool)
    (C : PEqualNP.CircuitLowerBounds.Circuit),
  let bounded := fun (i j : ℕ) (T : Fin i → Fin j → Bool) (h : ℕ) =>
    ∀ (off : Fin j → Bool) (F : Finset (Fin i × Fin i)),
      ((∀ e ∈ F, e.1 ≠ e.2 ∧
        (Finset.univ.filter (fun col => T e.1 col ≠ T e.2 col ∧ T e.1 col ≠ off col)).card ≤ 3) ∧
      (∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2)) → F.card ≤ h
  2*hr+2 ≤ n → 2*hc+2 ≤ m →
  (∀ a b : Fin n, a ≠ b → 6 ≤ (Finset.univ.filter (fun j => G a j ≠ G b j)).card) →
  (∀ a b : Fin m, a ≠ b → 6 ≤ (Finset.univ.filter (fun i => G i a ≠ G i b)).card) →
  bounded n m G hr → bounded m n (fun j i => G i j) hc →
  PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents G C →
    13 * (n+m) ≤ 12*C.size + 36 + 2*(hr+hc)) := by
  intro n m hr hc G C bounded hR hC dr dc br bc fan rep
  obtain ⟨_,vert⟩:=variation G (by omega) dr
  obtain ⟨_,v,w,a,diff⟩:=variation (fun v a=>G a v) (by omega) dc
  obtain ⟨D,sz,repD,back,shape,pos,out,live⟩:=Normal.normalized C fan rep ⟨a,v,w,diff⟩ vert
  have result:=paired_live G D hR hC dr dc br bc repD back shape pos out live
  omega
end PEqualNP.Outside.L_meta_25808_aux.Local
namespace PEqualNP.Outside.L_meta_25808_aux.Four
open Finset
def bits (k : ℕ) (v : Fin (2 ^ k)) : Finset (Fin k) :=
  (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)
def dot (k : ℕ) (u v : Fin (2 ^ k)) : Bool := ((bits k u ∩ bits k v).card % 2 == 1)
def G (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (u v : Fin (2 ^ k)) : Bool :=
  (dot k u v != rf u) != cf v

def β (b : Bool) : ZMod 2 := if b then 1 else 0

def ψ (k : ℕ) (x : ℕ) : Fin k → ZMod 2 := fun i => β (x.testBit i.val)
lemma z2_self (z : ZMod 2) : z + z = 0 := by revert z; decide

lemma ψ_xor (k x y : ℕ) : ψ k (x ^^^ y) = ψ k x + ψ k y := by
  funext i
  simp only [ψ, Pi.add_apply, Nat.testBit_xor]
  cases x.testBit i.val <;> cases y.testBit i.val <;> decide

lemma ψ_zero_iff (k x : ℕ) (hx : x < 2 ^ k) : ψ k x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.zero_testBit]
    by_cases hi : i < k
    · have := congrFun h ⟨i, hi⟩
      simp only [ψ, Pi.zero_apply, β] at this
      by_contra hne
      simp only [Bool.not_eq_false] at hne
      rw [hne] at this
      exact absurd this (by decide)
    · exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (not_lt.mp hi)))
  · rintro rfl
    funext i
    simp [ψ, β]

lemma ψ_add_ne (k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k) (hne : x ≠ y) :
    ψ k x + ψ k y ≠ 0 := by
  intro h
  rw [← ψ_xor, ψ_zero_iff k _ (Nat.xor_lt_two_pow hx hy)] at h
  apply hne
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun z => z.testBit i) h
  simp only [Nat.testBit_xor, Nat.zero_testBit] at this
  revert this
  cases x.testBit i <;> cases y.testBit i <;> decide

lemma ψ_inj (k x y : ℕ) (hx : x < 2 ^ k) (hy : y < 2 ^ k) (h : ψ k x = ψ k y) : x = y := by
  by_contra hne
  apply ψ_add_ne k x y hx hy hne
  rw [h]
  funext i
  exact z2_self _
lemma dot_eq (k : ℕ) (u v : Fin (2 ^ k)) : β (dot k u v) = ψ k u.val ⬝ᵥ ψ k v.val := by
  have hI : bits k u ∩ bits k v =
      (Finset.univ : Finset (Fin k)).filter (fun i => u.val.testBit i.val ∧ v.val.testBit i.val) := by
    ext i; simp [bits]
  have h1 : ψ k u.val ⬝ᵥ ψ k v.val = ((bits k u ∩ bits k v).card : ZMod 2) := by
    rw [hI, Finset.natCast_card_filter]
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro i _
    simp only [ψ, β]
    cases u.val.testBit i.val <;> cases v.val.testBit i.val <;> simp
  rw [h1]
  unfold dot
  generalize (bits k u ∩ bits k v).card = c
  rw [← ZMod.natCast_mod c 2]
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> rw [h] <;> rfl
lemma bool_ne (p q : Bool) : p ≠ q ↔ β p + β q = 1 := by cases p <;> cases q <;> decide
lemma bool_eq (p q : Bool) : p = q ↔ β p + β q = 0 := by cases p <;> cases q <;> decide

lemma βG (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (u v : Fin (2 ^ k)) :
    β (G k rf cf u v) = β (dot k u v) + β (rf u) + β (cf v) := by
  unfold G
  cases dot k u v <;> cases rf u <;> cases cf v <;> decide
lemma pairG (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (a b j : Fin (2 ^ k)) :
    β (G k rf cf a j) + β (G k rf cf b j) =
      (ψ k a.val + ψ k b.val) ⬝ᵥ ψ k j.val + (β (rf a) + β (rf b)) := by
  rw [βG, βG, dot_eq, dot_eq, add_dotProduct]
  linear_combination z2_self (β (cf j))
lemma z2_one (x c : ZMod 2) : x + c = 1 ↔ x = 1 + c := by revert x c; decide
lemma z2_zero (x c : ZMod 2) : x + c = 0 ↔ x = c := by revert x c; decide
lemma fiber (k m : ℕ) (R : Fin m → (Fin k → ZMod 2)) (hR : LinearIndependent (ZMod 2) R)
    (t : Fin m → ZMod 2) :
    ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∀ i, R i ⬝ᵥ w = t i)).card
      = 2 ^ (k - m) := by
  classical
  let L := Matrix.mulVecLin (Matrix.of R)
  have hL : ∀ w, L w = fun i => R i ⬝ᵥ w := fun w => rfl
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    have h1 := Matrix.rank_eq_finrank_span_row (Matrix.of R)
    unfold Matrix.rank at h1
    rw [h1]
    exact (finrank_span_eq_card hR).trans (Fintype.card_fin m)
  have hfib : ∀ t, ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => L w = t)).card =
      ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => L w = 0)).card := by
    intro t
    obtain ⟨w0, hw0⟩ := hsurj t
    apply Finset.card_bij (fun w _ => w - w0)
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [map_sub, hw, hw0, sub_self]
    · intro w1 _ w2 _ h
      simpa using h
    · intro w hw
      refine ⟨w + w0, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
        rw [map_add, hw, hw0, zero_add]
      · simp
  have htot := Finset.card_eq_sum_card_fiberwise (f := L)
    (s := (Finset.univ : Finset (Fin k → ZMod 2))) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
  rw [Finset.sum_congr rfl (fun t _ => hfib t), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, smul_eq_mul] at htot
  simp only [Fintype.card_fun, ZMod.card, Fintype.card_fin] at htot
  have heq : ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => ∀ i, R i ⬝ᵥ w = t i)) =
      (Finset.univ.filter (fun w => L w = t)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hL, funext_iff]
  rw [heq, hfib]
  set X := ((Finset.univ : Finset (Fin k → ZMod 2)).filter (fun w => L w = 0)).card
  have hX : 1 ≤ X := by
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have hmk : m ≤ k := by
    have : 2 ^ m ≤ 2 ^ k := by rw [htot]; exact Nat.le_mul_of_pos_right _ hX
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
  have h2 : 2 ^ k = 2 ^ m * 2 ^ (k - m) := by rw [← pow_add, Nat.add_sub_cancel' hmk]
  rw [h2] at htot
  exact (Nat.eq_of_mul_eq_mul_left (by positivity) htot).symm
lemma z2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide
theorem main (k : ℕ) (rf cf : Fin (2 ^ k) → Bool) (_hk : 3 ≤ k) (a b c d : Fin (2 ^ k))
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun j : Fin (2 ^ k) =>
      G k rf cf a j ≠ G k rf cf b j ∧ G k rf cf a j ≠ G k rf cf c j ∧
        G k rf cf a j = G k rf cf d j)).card =
      if (a.val ^^^ b.val ^^^ c.val ^^^ d.val) = 0 then
        (if (rf a != rf b) = (rf c != rf d) then 2 ^ (k - 2) else 0) else 2 ^ (k - 3) := by
  classical
  set R0 := ψ k a.val + ψ k b.val with hR0
  set R1 := ψ k a.val + ψ k c.val with hR1
  set R2 := ψ k a.val + ψ k d.val with hR2
  set t0 := 1 + (β (rf a) + β (rf b)) with ht0
  set t1 := 1 + (β (rf a) + β (rf c)) with ht1
  set t2 := β (rf a) + β (rf d) with ht2
  let Q := fun w : Fin k → ZMod 2 => R0 ⬝ᵥ w = t0 ∧ R1 ⬝ᵥ w = t1 ∧ R2 ⬝ᵥ w = t2
  have hmem : ∀ j : Fin (2 ^ k), (G k rf cf a j ≠ G k rf cf b j ∧ G k rf cf a j ≠ G k rf cf c j ∧
        G k rf cf a j = G k rf cf d j) ↔ Q (ψ k j.val) := by
    intro j
    rw [bool_ne, bool_ne, bool_eq, pairG, pairG, pairG, z2_one, z2_one, z2_zero]
  have hbij : Function.Bijective (fun j : Fin (2 ^ k) => ψ k j.val) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x y h => Fin.ext (ψ_inj k _ _ x.isLt y.isLt h), ?_⟩
    simp [ZMod.card]
  have hcard : ((Finset.univ : Finset (Fin (2 ^ k))).filter (fun j : Fin (2 ^ k) =>
      G k rf cf a j ≠ G k rf cf b j ∧ G k rf cf a j ≠ G k rf cf c j ∧
        G k rf cf a j = G k rf cf d j)).card =
      ((Finset.univ : Finset (Fin k → ZMod 2)).filter Q).card := by
    apply Finset.card_bij (fun j _ => ψ k j.val)
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact (hmem j).mp hj
    · intro x _ y _ h
      exact hbij.1 h
    · intro w hw
      obtain ⟨j, hj⟩ := hbij.2 w
      refine ⟨j, ?_, hj⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [hmem, show ψ k j.val = w from hj]
      exact hw
  rw [hcard]
  have hne01 : R0 + R1 = ψ k b.val + ψ k c.val := by
    funext i; simp only [hR0, hR1, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k b.val i = y; generalize ψ k c.val i = z
    revert x y z; decide
  have hne02 : R0 + R2 = ψ k b.val + ψ k d.val := by
    funext i; simp only [hR0, hR2, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k b.val i = y; generalize ψ k d.val i = z
    revert x y z; decide
  have hne12 : R1 + R2 = ψ k c.val + ψ k d.val := by
    funext i; simp only [hR1, hR2, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k c.val i = y; generalize ψ k d.val i = z
    revert x y z; decide
  have h012 : R0 + R1 + R2 = ψ k (a.val ^^^ b.val ^^^ c.val ^^^ d.val) := by
    rw [ψ_xor, ψ_xor, ψ_xor]
    funext i; simp only [hR0, hR1, hR2, Pi.add_apply]
    generalize ψ k a.val i = x; generalize ψ k b.val i = y; generalize ψ k c.val i = z
    generalize ψ k d.val i = w
    revert x y z w; decide
  have nR0 : R0 ≠ 0 := ψ_add_ne k _ _ a.isLt b.isLt (fun h => hab (Fin.ext h))
  have nR1 : R1 ≠ 0 := ψ_add_ne k _ _ a.isLt c.isLt (fun h => hac (Fin.ext h))
  have nR2 : R2 ≠ 0 := ψ_add_ne k _ _ a.isLt d.isLt (fun h => had (Fin.ext h))
  have n01 : R0 + R1 ≠ 0 := by rw [hne01]; exact ψ_add_ne k _ _ b.isLt c.isLt (fun h => hbc (Fin.ext h))
  have n02 : R0 + R2 ≠ 0 := by rw [hne02]; exact ψ_add_ne k _ _ b.isLt d.isLt (fun h => hbd (Fin.ext h))
  have n12 : R1 + R2 ≠ 0 := by rw [hne12]; exact ψ_add_ne k _ _ c.isLt d.isLt (fun h => hcd (Fin.ext h))
  split_ifs with hpar hev
  ·
    have hR2' : R2 = R0 + R1 := by
      have : R0 + R1 + R2 = 0 := by rw [h012, hpar]; funext i; simp [ψ, β]
      funext i
      have := congrFun this i
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      revert this
      generalize R0 i = x; generalize R1 i = y; generalize R2 i = z
      revert x y z; decide
    have ht : t2 = t0 + t1 := by
      simp only [ht0, ht1, ht2]
      revert hev
      cases rf a <;> cases rf b <;> cases rf c <;> cases rf d <;> decide
    have hli : LinearIndependent (ZMod 2) ![R0, R1] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
      rcases z2_cases (g 0) with h0 | h0 <;> rcases z2_cases (g 1) with h1 | h1 <;>
        rw [h0, h1] at hg <;> simp at hg
      · fin_cases i <;> simp [h0, h1]
      · exact absurd hg nR1
      · exact absurd hg nR0
      · exact absurd hg n01
    rw [← fiber k 2 ![R0, R1] hli ![t0, t1]]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, Fin.forall_fin_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, hR2', ht, add_dotProduct]
    constructor
    · rintro ⟨h0, h1, _⟩; exact ⟨h0, h1⟩
    · rintro ⟨h0, h1⟩; exact ⟨h0, h1, by rw [h0, h1]⟩
  ·
    have hR2' : R2 = R0 + R1 := by
      have : R0 + R1 + R2 = 0 := by rw [h012, hpar]; funext i; simp [ψ, β]
      funext i
      have := congrFun this i
      simp only [Pi.add_apply, Pi.zero_apply] at this ⊢
      revert this
      generalize R0 i = x; generalize R1 i = y; generalize R2 i = z
      revert x y z; decide
    have ht : t2 ≠ t0 + t1 := by
      simp only [ht0, ht1, ht2]
      revert hev
      cases rf a <;> cases rf b <;> cases rf c <;> cases rf d <;> decide
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro w - ⟨h0, h1, h2⟩
    rw [hR2', add_dotProduct, h0, h1] at h2
    exact ht h2.symm
  ·
    have nall : R0 + R1 + R2 ≠ 0 := by
      rw [h012]; intro h
      exact hpar ((ψ_zero_iff k _ (Nat.xor_lt_two_pow (Nat.xor_lt_two_pow
        (Nat.xor_lt_two_pow a.isLt b.isLt) c.isLt) d.isLt)).mp h)
    have hli : LinearIndependent (ZMod 2) ![R0, R1, R2] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hg
      rcases z2_cases (g 0) with h0 | h0 <;> rcases z2_cases (g 1) with h1 | h1 <;>
        rcases z2_cases (g 2) with h2 | h2 <;> rw [h0, h1, h2] at hg <;> simp at hg
      · fin_cases i <;> simp [h0, h1, h2]
      · exact absurd hg nR2
      · exact absurd hg nR1
      · exact absurd hg n12
      · exact absurd hg nR0
      · exact absurd hg n02
      · exact absurd hg n01
      · exact absurd hg nall
    rw [← fiber k 3 ![R0, R1, R2] hli ![t0, t1, t2]]
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Q, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, IsEmpty.forall_iff, and_true]
end PEqualNP.Outside.L_meta_25808_aux.Four
namespace PEqualNP.Outside.L_meta_25808_aux.Errors
open Finset
variable {α β : Type} [Fintype β] [DecidableEq β]
def errors (B : Finset β) (G T : α → β → Bool) (a : α) := B.filter (fun j => T a j ≠ G a j)
def diff (B : Finset β) (T : α → β → Bool) (a b : α) := B.filter (fun j => T a j ≠ T b j)
def cost (B : Finset β) (T : α → β → Bool) (off : β → Bool) (a b : α) :=
  B.filter (fun j => T a j ≠ T b j ∧ T a j ≠ off j)
def split4 (G : α → β → Bool) (a b c d : α) :=
  univ.filter (fun j => G a j ≠ G b j ∧ G a j ≠ G c j ∧ G a j = G d j)
theorem distance_loss (B : Finset β) (G T : α → β → Bool) (a b : α) :
    (diff univ G a b).card ≤ (Fintype.card β-B.card) +
      (errors B G T a).card + (errors B G T b).card + (diff B T a b).card := by
  classical
  let D := univ \ B
  let A := errors B G T a
  let E := errors B G T b
  let H := diff B T a b
  have incl : diff univ G a b ⊆ D ∪ A ∪ E ∪ H := by
    intro j hj
    have neq := (mem_filter.mp hj).2
    by_cases jB : j ∈ B
    · by_cases ha : T a j = G a j
      · by_cases hb : T b j = G b j
        · exact mem_union_right _ (mem_filter.mpr ⟨jB, by simpa [ha,hb] using neq⟩)
        · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨jB,hb⟩))
      · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨jB,ha⟩)))
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _,jB⟩)))
  have hc := card_le_card incl
  have hd : D.card = Fintype.card β-B.card := by simp [D,card_sdiff_of_subset]
  have h₁ := card_union_le D A
  have h₂ := card_union_le (D ∪ A) E
  have h₃ := card_union_le (D ∪ A ∪ E) H
  change _ ≤ _ + A.card + E.card + H.card
  omega
theorem four_loss (B : Finset β) (G T : α → β → Bool) (off : β → Bool) (a b c d : α) :
    (split4 G a b c d).card ≤ Fintype.card β - B.card + (errors B G T a).card +
      (errors B G T b).card + (errors B G T c).card + (errors B G T d).card +
      (cost B T off a b).card + (cost B T off c d).card := by
  classical
  let D := univ \ B
  let A := errors B G T a
  let E := errors B G T b
  let F := errors B G T c
  let H := errors B G T d
  let P := cost B T off a b
  let Q := cost B T off c d
  have incl : split4 G a b c d ⊆ D ∪ A ∪ E ∪ F ∪ H ∪ P ∪ Q := by
    intro j hj
    obtain ⟨nab,nac,ead⟩ := (mem_filter.mp hj).2
    simp only [mem_union]
    by_cases jB : j ∈ B
    · by_cases ha : T a j = G a j
      · by_cases hb : T b j = G b j
        · by_cases hc : T c j = G c j
          · by_cases hd : T d j = G d j
            · by_cases ho : G a j = off j
              · exact Or.inr (mem_filter.mpr ⟨jB,by rw [hc,hd,← ead]; exact Ne.symm nac,
                  by rw [hc,← ho]; exact Ne.symm nac⟩)
              · exact Or.inl (Or.inr (mem_filter.mpr ⟨jB,by rwa [ha,hb],by rwa [ha]⟩))
            · exact Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨jB,hd⟩)))
          · exact Or.inl (Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨jB,hc⟩))))
        · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨jB,hb⟩)))))
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (mem_filter.mpr ⟨jB,ha⟩))))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (mem_sdiff.mpr ⟨mem_univ _,jB⟩))))))
  have h := card_le_card incl
  have hd : D.card = Fintype.card β-B.card := by simp [D,card_sdiff_of_subset]
  have h₁ := card_union_le D A
  have h₂ := card_union_le (D∪A) E
  have h₃ := card_union_le (D∪A∪E) F
  have h₄ := card_union_le (D∪A∪E∪F) H
  have h₅ := card_union_le (D∪A∪E∪F∪H) P
  have h₆ := card_union_le (D∪A∪E∪F∪H∪P) Q
  change _ ≤ _ + A.card + E.card + F.card + H.card + P.card + Q.card
  omega
end PEqualNP.Outside.L_meta_25808_aux.Errors
namespace PEqualNP.Outside.L_meta_25808_aux.Switched
open Finset Four Errors
abbrev Name (k : Nat) := Fin (2^k)
theorem clean_distance {k : Nat} (rf cf : Name k → Bool) {a b : Name k} (hab : a≠b) :
    (diff univ (G k rf cf) a b).card = 2^(k-1) := by
  classical
  let r := ψ k a.val + ψ k b.val
  let t := 1 + (β (rf a) + β (rf b))
  have mem (j : Name k) : G k rf cf a j ≠ G k rf cf b j ↔ r ⬝ᵥ ψ k j.val = t := by
    rw [bool_ne,pairG,z2_one]
  have bij : Function.Bijective (fun j : Name k => ψ k j.val) := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨fun x y h => Fin.ext (ψ_inj k _ _ x.isLt y.isLt h),by simp [Name,ZMod.card]⟩
  let rows : Fin 1 → Fin k → ZMod 2 := fun _ => r
  let tar : Fin 1 → ZMod 2 := fun _ => t
  have independent : LinearIndependent (ZMod 2) rows := by
    rw [linearIndependent_unique_iff]
    exact ψ_add_ne k _ _ a.isLt b.isLt (fun e=>hab (Fin.ext e))
  rw [← fiber k 1 rows independent tar]
  apply Finset.card_bij (fun j _ => ψ k j.val)
  · intro j hj
    exact mem_filter.mpr ⟨mem_univ _,fun _=>(mem j).mp (mem_filter.mp hj).2⟩
  · intro j _ l _ h; exact bij.1 h
  · intro v hv
    obtain ⟨j,rfl⟩ := bij.2 v
    exact ⟨j,mem_filter.mpr ⟨mem_univ _,(mem j).mpr ((mem_filter.mp hv).2 0)⟩,rfl⟩
theorem survived_distance {k er : Nat} (rf cf : Name k → Bool) (B : Finset (Name k))
    (T : Name k → Name k → Bool) (budget : 7 + (2^k - B.card) + 4*er ≤ 2^(k-3))
    {a b : Name k} (hab : a≠b) (ea : (errors B (G k rf cf) T a).card ≤ er)
    (eb : (errors B (G k rf cf) T b).card ≤ er) : 6 ≤ (diff B T a b).card := by
  have h:=distance_loss B (G k rf cf) T a b
  rw [clean_distance rf cf hab] at h
  have card : Fintype.card (Name k) = 2^k := Fintype.card_fin _
  rw [card] at h
  have power : 2^(k-3) ≤ 2^(k-1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega
theorem clash {k er : Nat} (hk : 3≤k) (rf cf : Name k → Bool) (B : Finset (Name k))
    (T : Name k → Name k → Bool) (off : Name k → Bool)
    (budget : 7 + (2^k - B.card) + 4*er ≤ 2^(k-3)) {a b c d : Name k}
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d)
    (ea : (errors B (G k rf cf) T a).card ≤ er) (eb : (errors B (G k rf cf) T b).card ≤ er)
    (ec : (errors B (G k rf cf) T c).card ≤ er) (ed : (errors B (G k rf cf) T d).card ≤ er)
    (p : (cost B T off a b).card ≤ 3) (q : (cost B T off c d).card ≤ 3) :
    (a.val ^^^ b.val ^^^ c.val ^^^ d.val) = 0 ∧ (rf a != rf b) ≠ (rf c != rf d) := by
  have loss := four_loss B (G k rf cf) T off a b c d
  have card : Fintype.card (Name k) = 2^k := Fintype.card_fin _
  rw [card] at loss
  have h := Four.main k rf cf hk a b c d ab ac ad bc bd cd
  change (split4 (G k rf cf) a b c d).card = _ at h
  have power : 2^(k-3) ≤ 2^(k-2) := Nat.pow_le_pow_right (by decide) (by omega)
  split_ifs at h with par same <;> first | exact ⟨par,same⟩ | omega
lemma beta_xor (p q : Bool) : β (p != q) = β p+β q := by cases p <;> cases q <;> decide
lemma beta_inj : Function.Injective β := by intro p q; cases p <;> cases q <;> decide
lemma affine_derivative {k : Nat} (u a b c d : Name k) (z : Bool)
    (par : (a.val ^^^ b.val ^^^ c.val ^^^ d.val) = 0) :
    ((z != dot k u a) != (z != dot k u b)) = ((z != dot k u c) != (z != dot k u d)) := by
  have sum : ψ k a.val + ψ k b.val + ψ k c.val + ψ k d.val = 0 := by
    rw [← ψ_xor,← ψ_xor,← ψ_xor,par]
    exact (ψ_zero_iff k 0 (Nat.two_pow_pos k)).mpr rfl
  have h := congrArg (fun v => ψ k u.val ⬝ᵥ v) sum
  change ψ k u.val ⬝ᵥ (ψ k a.val + ψ k b.val + ψ k c.val + ψ k d.val) = ψ k u.val ⬝ᵥ 0 at h
  simp only [dotProduct_add,dotProduct_zero] at h
  apply beta_inj
  simp only [beta_xor,dot_eq]
  linear_combination h - z2_self (ψ k u.val ⬝ᵥ ψ k c.val) - z2_self (ψ k u.val ⬝ᵥ ψ k d.val)
end PEqualNP.Outside.L_meta_25808_aux.Switched
namespace PEqualNP.Outside.L_meta_25808_aux.Switched
open Finset Four Errors
def lab {N : Nat} (S : Finset (Fin N)) (i : Fin S.card) : Fin N := S.orderEmbOfFin rfl i
lemma lab_mem {N : Nat} (S : Finset (Fin N)) (i : Fin S.card) : lab S i∈S :=
  S.orderEmbOfFin_mem rfl i
lemma lab_inj {N : Nat} (S : Finset (Fin N)) : Function.Injective (lab S) :=
  (S.orderEmbOfFin rfl).injective
def extend {N : Nat} (S : Finset (Fin N)) (f : Fin S.card → Bool) (j : Fin N) : Bool :=
  if hj : j∈S then f ((S.orderIsoOfFin rfl).symm ⟨j,hj⟩) else false
lemma extend_lab {N : Nat} (S : Finset (Fin N)) (f : Fin S.card → Bool) (i : Fin S.card) :
    extend S f (lab S i) = f i := by
  rw [extend,dif_pos (lab_mem S i)]
  apply congrArg f
  apply (S.orderIsoOfFin rfl).injective
  exact (S.orderIsoOfFin rfl).apply_symm_apply _
lemma count_pull {N : Nat} (S : Finset (Fin N)) (p : Fin N → Prop) [DecidablePred p] :
    (univ.filter (fun i : Fin S.card => p (lab S i))).card = (S.filter p).card := by
  apply Finset.card_bij (fun i _=>lab S i)
  · intro i hi; exact mem_filter.mpr ⟨lab_mem S i,(mem_filter.mp hi).2⟩
  · intro i _ j _ h; exact lab_inj S h
  · intro j hj
    let v : ↥S := ⟨j,(mem_filter.mp hj).1⟩
    let i := (S.orderIsoOfFin rfl).symm v
    have eq : lab S i=j := congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply v)
    exact ⟨i,mem_filter.mpr ⟨mem_univ _, eq ▸ (mem_filter.mp hj).2⟩,eq⟩
def price {k : Nat} (R : Finset (Name k)) (rf : Name k → Bool) : Nat :=
  if ∃ z u, ∀ r∈R, rf r = (z != dot k u r) then 1 else 2
theorem bounded_observed {k er : Nat} (hk : 3≤k) (rf cf : Name k→Bool)
    (R B : Finset (Name k)) (T : Name k→Name k→Bool)
    (budget : 7 + (2^k-B.card) + 4*er ≤ 2^(k-3))
    (errs : ∀ r∈R, (errors B (G k rf cf) T r).card ≤ er)
    (off : Fin B.card → Bool) (F : Finset (Fin R.card × Fin R.card))
    (small : ∀ e∈F, e.1 ≠ e.2 ∧
      (univ.filter (fun j : Fin B.card => T (lab R e.1) (lab B j) ≠ T (lab R e.2) (lab B j) ∧
        T (lab R e.1) (lab B j) ≠ off j)).card ≤ 3)
    (disj : ∀ e∈F, ∀ f∈F, e≠f → e.1≠f.1 ∧ e.1≠f.2 ∧ e.2≠f.1 ∧ e.2≠f.2) :
    F.card ≤ price R rf := by
  classical
  let key := fun e : Fin R.card × Fin R.card => rf (lab R e.1) != rf (lab R e.2)
  have cheap e (he : e∈F) : (cost B T (extend B off) (lab R e.1) (lab R e.2)).card ≤ 3 := by
    unfold cost
    rw [← count_pull]
    simpa only [extend_lab] using (small e he).2
  have conflict e (he : e∈F) f (hf : f∈F) (ne : e≠f) :
      ((lab R e.1).val ^^^ (lab R e.2).val ^^^ (lab R f.1).val ^^^ (lab R f.2).val) = 0 ∧
      key e ≠ key f := by
    obtain ⟨ac,ad,bc,bd⟩ := disj e he f hf ne
    exact clash hk rf cf B T (extend B off) budget ((lab_inj R).ne (small e he).1)
      ((lab_inj R).ne ac) ((lab_inj R).ne ad) ((lab_inj R).ne bc) ((lab_inj R).ne bd)
      ((lab_inj R).ne (small f hf).1) (errs _ (lab_mem R _)) (errs _ (lab_mem R _))
      (errs _ (lab_mem R _)) (errs _ (lab_mem R _)) (cheap e he) (cheap f hf)
  unfold price
  split_ifs with aff
  · obtain ⟨z,u,aff⟩ := aff
    apply Finset.card_le_one.mpr
    intro e he f hf
    by_contra neq
    obtain ⟨p,n⟩ := conflict e he f hf neq
    apply n
    dsimp only [key]
    rw [aff _ (lab_mem R _),aff _ (lab_mem R _),aff _ (lab_mem R _),aff _ (lab_mem R _)]
    exact affine_derivative u _ _ _ _ z p
  · have inject : Set.InjOn key (F : Set (Fin R.card × Fin R.card)) := by
      intro e he f hf eq
      by_contra ne
      exact (conflict e he f hf ne).2 eq
    have count := Finset.card_le_univ (F.image key)
    rw [Finset.card_image_of_injOn inject,Fintype.card_bool] at count
    exact count
end PEqualNP.Outside.L_meta_25808_aux.Switched
namespace PEqualNP.Outside.L_meta_25808_aux.Restriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Outside.L_meta_25808_aux.Normal.Normalize
open Switched
def wire (n m : Nat) (raw : Nat → Nat) (w : Nat) := if w<n then raw w else m+(w-n)
def renameGate (f : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map f⟩
def renameCircuit (f : Nat → Nat) (C : Circuit) : Circuit := ⟨C.gates.map (renameGate f), f C.output⟩
lemma val_read {n m t : Nat} {raw : Nat→Nat} {x y : List Bool} (lx : x.length=n) (ly : y.length=m)
    (shape : ∀i<n, raw i<m ∨ m+t≤raw i)
    (init : ∀i<n, y.getD (raw i) false = x.getD i false) (z : List Bool) (cap : z.length≤t) (i : Nat) :
    (y++z).getD (wire n m raw i) false = (x++z).getD i false := by
  by_cases h : i<n
  · rw [wire,if_pos h,List.getD_append x z false i (by omega)]
    rcases shape i h with lo|hi
    · rw [List.getD_append _ _ _ _ (by omega),init i h]
    · rw [List.getD_eq_default (y++z) false (show (y++z).length ≤ raw i by simp; omega),← init i h,List.getD_eq_default y false (by omega)]
  · rw [wire,if_neg h,List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega),lx,ly]
    simp
lemma run_transfer {n m t : Nat} {raw : Nat→Nat} {x y : List Bool} (lx : x.length=n) (ly : y.length=m)
    (shape : ∀i<n,raw i<m ∨ m+t≤raw i) (init : ∀i<n, y.getD (raw i) false=x.getD i false)
    (gs : List Gate) (acc : List Bool) (cap : acc.length+gs.length≤t) :
    ∃ z : List Bool, z.length≤t ∧ run gs (x++acc)=x++z ∧
      run (gs.map (renameGate (wire n m raw))) (y++acc)=y++z := by
  induction gs generalizing acc with
  | nil => exact ⟨acc,by simpa using cap,rfl,rfl⟩
  | cons g gs ih =>
    let val := g.op.eval (g.inputs.map fun i => (x++acc).getD i false)
    have eval : (renameGate (wire n m raw) g).op.eval
        ((renameGate (wire n m raw) g).inputs.map fun j => (y++acc).getD j false) = val := by
      unfold renameGate
      simp only [List.map_map,Function.comp_def]
      apply congrArg g.op.eval
      exact List.map_congr_left (fun i _=>val_read lx ly shape init acc (by simp at cap; omega) i)
    have bound : (acc++[val]).length+gs.length≤t := by simp at cap ⊢; omega
    obtain ⟨z,sz,h₁,h₂⟩ := ih (acc++[val]) bound
    refine ⟨z,sz,?_,?_⟩
    · change run gs ((x++acc)++[val])=_
      rwa [List.append_assoc]
    · change run (gs.map _) ((y++acc)++[_])=_
      rw [eval,List.append_assoc]
      exact h₂
lemma eval_transfer {n m : Nat} (C : Circuit) (raw : Nat→Nat) {x y : List Bool}
    (lx : x.length=n) (ly : y.length=m) (shape : ∀i<n,raw i<m ∨ m+C.size≤raw i)
    (init : ∀i<n, y.getD (raw i) false=x.getD i false) :
    (renameCircuit (wire n m raw) C).eval y = C.eval x := by
  obtain ⟨z,cap,hx,hy⟩ := run_transfer lx ly shape init C.gates [] (by simp [Circuit.size])
  simp only [List.append_nil] at hx hy
  change (run (C.gates.map _) y).getD _ false = (run C.gates x).getD _ false
  rw [hx,hy]
  exact val_read lx ly shape init z cap C.output
def index {N : Nat} (S : Finset (Fin N)) (a : Fin N) (h : a∈S) : Fin S.card :=
  (S.orderIsoOfFin rfl).symm ⟨a,h⟩
lemma index_spec {N : Nat} (S : Finset (Fin N)) (a : Fin N) (h : a∈S) :
    lab S (index S a h) = a := congrArg Subtype.val ((S.orderIsoOfFin rfl).apply_symm_apply ⟨a,h⟩)
def rawIndex {N : Nat} (R B : Finset (Fin N)) (t i : Nat) : Nat :=
  if hi : i<N then
    if h : (⟨i,hi⟩ : Fin N)∈R then (index R ⟨i,hi⟩ h).val else R.card+B.card+t
  else if hi : i-N<N then
    if h : (⟨i-N,hi⟩ : Fin N)∈B then R.card+(index B ⟨i-N,hi⟩ h).val else R.card+B.card+t
  else R.card+B.card+t
lemma raw_shape {N : Nat} (R B : Finset (Fin N)) (t i : Nat) :
    rawIndex R B t i < R.card+B.card ∨ R.card+B.card+t≤rawIndex R B t i := by
  unfold rawIndex
  split_ifs with first kept second keptCol
  · have lim := (index R ⟨i,first⟩ kept).isLt; omega
  · omega
  · have lim := (index B ⟨i-N,second⟩ keptCol).isLt; omega
  all_goals omega
lemma raw_init {N : Nat} (R B : Finset (Fin N)) (a : Fin R.card) (b : Fin B.card) (t i : Nat)
    (cap : i<N+N) : (oneEach a b).getD (rawIndex R B t i) false =
      (oneEach (lab R a) (lab B b)).getD i false := by
  rw [oneEach_getD,oneEach_getD]
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  have ha:=a.isLt
  have hb:=b.isLt
  have pr:=(lab R a).isLt
  have pc:=(lab B b).isLt
  unfold rawIndex
  split_ifs with first kept second keptCol
  · let j : Fin N := ⟨i,first⟩
    have val := (index R j kept).isLt
    have iff : (index R j kept).val=a.val ↔ i=(lab R a).val := by
      constructor
      · intro h
        exact congrArg Fin.val ((index_spec R j kept).symm.trans (congrArg (lab R) (Fin.ext h)))
      · intro h
        exact congrArg Fin.val (lab_inj R ((index_spec R j kept).trans (Fin.ext h)))
    change (index R j kept).val=_ ∨ _ ↔ _
    omega
  · have ne : i ≠ (lab R a).val := by
      intro eq; exact kept ((Fin.ext eq : (⟨i,first⟩ : Fin N)=lab R a) ▸ lab_mem R a)
    omega
  · let j : Fin N := ⟨i-N,second⟩
    have val := (index B j keptCol).isLt
    have iff : (index B j keptCol).val=b.val ↔ i-N=(lab B b).val := by
      constructor
      · intro h
        exact congrArg Fin.val ((index_spec B j keptCol).symm.trans (congrArg (lab B) (Fin.ext h)))
      · intro h
        exact congrArg Fin.val (lab_inj B ((index_spec B j keptCol).trans (Fin.ext h)))
    dsimp only [j] at val iff
    omega
  · have ne : i-N ≠ (lab B b).val := by
      intro eq; exact keptCol ((Fin.ext eq : (⟨i-N,second⟩ : Fin N)=lab B b) ▸ lab_mem B b)
    omega
  · omega
theorem restrict_banks {N : Nat} (R B : Finset (Fin N)) (C : Circuit) (fan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size=C.size ∧
      Represents (fun a b => C.eval (oneEach (lab R a) (lab B b))) D := by
  let raw := rawIndex R B C.size
  let f := wire (N+N) (R.card+B.card) raw
  refine ⟨renameCircuit f C,?_,by simp [renameCircuit,Circuit.size],?_⟩
  · intro g hg
    obtain ⟨old,ho,rfl⟩ := List.mem_map.mp (show g∈C.gates.map (renameGate f) from hg)
    simpa [renameGate] using fan old ho
  · intro a b
    exact eval_transfer C raw (oneEach_length _ _) (oneEach_length _ _)
      (fun i _=>raw_shape R B C.size i) (raw_init R B a b C.size)
end PEqualNP.Outside.L_meta_25808_aux.Restriction
namespace PEqualNP.Outside.L_meta_25808_aux.Switched
open Finset Four Errors Restriction
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
theorem transpose_G {k : Nat} (rf cf : Name k → Bool) (a b : Name k) :
    G k cf rf b a = G k rf cf a b := by
  have eq : dot k b a=dot k a b := by simp [dot,inter_comm (bits k b) (bits k a)]
  simp only [G,eq]
  cases dot k a b <;> cases rf a <;> cases cf b <;> decide
lemma enough {k e : Nat} (R : Finset (Name k)) (rf : Name k → Bool)
    (budget : 7+(2^k-R.card)+4*e ≤ 2^(k-3)) : 2*price R rf+2 ≤ R.card := by
  have lim : 2^(k-3) ≤ 2^k := Nat.pow_le_pow_right (by decide) (by omega)
  unfold price; split_ifs <;> omega
theorem robust {k er ec : Nat} (hk : 6≤k) (rf cf : Name k → Bool) (R B : Finset (Name k))
    (C : Circuit)
    (rowBudget : 7+(2^k-B.card)+4*er ≤ 2^(k-3))
    (colBudget : 7+(2^k-R.card)+4*ec ≤ 2^(k-3))
    (rows : ∀ a∈R, (errors B (G k rf cf) (fun r j=>C.eval (oneEach r j)) a).card ≤ er)
    (cols : ∀ b∈B, (errors R (G k cf rf) (fun j r=>C.eval (oneEach r j)) b).card ≤ ec)
    (fan : FanInTwo C) :
    13*(R.card+B.card) ≤ 12*C.size+36+2*(price R rf + price B cf) := by
  classical
  let T := fun (a b : Name k) => C.eval (oneEach a b)
  let F := fun (a : Fin R.card) (b : Fin B.card) => T (lab R a) (lab B b)
  obtain ⟨D,df,ds,dr⟩ := restrict_banks R B C fan
  have rd a b (ne : a≠b) : 6 ≤ (univ.filter (fun j => F a j ≠ F b j)).card := by
    unfold F
    rw [count_pull B (fun j=>T (lab R a) j ≠ T (lab R b) j)]
    exact survived_distance rf cf B T rowBudget ((lab_inj R).ne ne) (rows _ (lab_mem R a)) (rows _ (lab_mem R b))
  have cd a b (ne : a≠b) : 6 ≤ (univ.filter (fun i => F i a ≠ F i b)).card := by
    unfold F
    rw [count_pull R (fun i=>T i (lab B a) ≠ T i (lab B b))]
    exact survived_distance cf rf R (fun j i=>T i j) colBudget ((lab_inj B).ne ne)
      (cols _ (lab_mem B a)) (cols _ (lab_mem B b))
  have res := PEqualNP.Outside.L_meta_25808_aux.Local.comparison_bound R.card B.card
    (price R rf) (price B cf) F D (enough R rf colBudget) (enough B cf rowBudget) rd cd
    (fun off edges h => bounded_observed (by omega) rf cf R B T rowBudget rows off edges h.1 h.2)
    (fun off edges h => bounded_observed (by omega) cf rf B R (fun j i=>T i j) colBudget cols off edges h.1 h.2)
    df dr
  rwa [ds] at res
end PEqualNP.Outside.L_meta_25808_aux.Switched
namespace PEqualNP.Outside.L_meta_25808_aux
open Switched Four Errors
theorem robust_bound : (∀ (k er ec : ℕ) (rowFlip colFlip : Fin (2^k) → Bool)
    (R B : Finset (Fin (2^k))) (C : PEqualNP.CircuitLowerBounds.Circuit), 6 ≤ k →
  let N := 2 ^ k
  let bits := fun (v : Fin N) =>
    (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)
  let dot := fun (u v : Fin N) => ((bits u ∩ bits v).card % 2 == 1)
  let G := fun (u v : Fin N) => (dot u v != rowFlip u) != colFlip v
  let observed := fun (r j : Fin N) => C.eval
    (List.ofFn (fun x : Fin N => decide (x = r)) ++ List.ofFn (fun y : Fin N => decide (y = j)))
  let hr := if ∃ (z : Bool) (u : Fin N), ∀ r ∈ R, rowFlip r = (z != dot u r) then 1 else 2
  let hc := if ∃ (z : Bool) (v : Fin N), ∀ j ∈ B, colFlip j = (z != dot v j) then 1 else 2
  7 + (N-B.card) + 4*er ≤ 2^(k-3) → 7 + (N-R.card) + 4*ec ≤ 2^(k-3) →
  (∀ r ∈ R, (B.filter (fun j => observed r j ≠ G r j)).card ≤ er) →
  (∀ j ∈ B, (R.filter (fun r => observed r j ≠ G r j)).card ≤ ec) →
  PEqualNP.MetaComplexity.FanInTwo C →
    13*(R.card+B.card) ≤ 12*C.size + 36 + 2*(hr+hc)) := by
  intro k er ec rf cf R B C hk N bits dot G observed hr hc rb cb rows cols fan
  apply robust hk rf cf R B C rb cb rows _ fan
  intro j hj
  change (R.filter (fun r => C.eval (PEqualNP.Represents.oneEach r j) ≠ Four.G k cf rf j r)).card ≤ ec
  simp_rw [transpose_G rf cf]
  exact cols j hj
end PEqualNP.Outside.L_meta_25808_aux
theorem PEqualNP.Outside.L_meta_25808 : (∀ (k er ec : ℕ) (rowFlip colFlip : Fin (2^k) → Bool)
    (R B : Finset (Fin (2^k))) (C : PEqualNP.CircuitLowerBounds.Circuit), 6 ≤ k →
  let N := 2 ^ k
  let bits := fun (v : Fin N) =>
    (Finset.univ : Finset (Fin k)).filter (fun i => v.val.testBit i.val)
  let dot := fun (u v : Fin N) => ((bits u ∩ bits v).card % 2 == 1)
  let G := fun (u v : Fin N) => (dot u v != rowFlip u) != colFlip v
  let observed := fun (r j : Fin N) => C.eval
    (List.ofFn (fun x : Fin N => decide (x = r)) ++ List.ofFn (fun y : Fin N => decide (y = j)))
  let hr := if ∃ (z : Bool) (u : Fin N), ∀ r ∈ R, rowFlip r = (z != dot u r) then 1 else 2
  let hc := if ∃ (z : Bool) (v : Fin N), ∀ j ∈ B, colFlip j = (z != dot v j) then 1 else 2
  7 + (N-B.card) + 4*er ≤ 2^(k-3) → 7 + (N-R.card) + 4*ec ≤ 2^(k-3) →
  (∀ r ∈ R, (B.filter (fun j => observed r j ≠ G r j)).card ≤ er) →
  (∀ j ∈ B, (R.filter (fun r => observed r j ≠ G r j)).card ≤ ec) →
  PEqualNP.MetaComplexity.FanInTwo C →
    13*(R.card+B.card) ≤ 12*C.size + 36 + 2*(hr+hc)) :=
  PEqualNP.Outside.L_meta_25808_aux.robust_bound
