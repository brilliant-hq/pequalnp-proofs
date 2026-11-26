import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
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
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
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

def fok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem rv_ext (hs e : List Gate) (y : List Bool) (r : Bool ⊕ ℕ) (h : ∀ t, r = .inr t → t < y.length + hs.length) :
    rv (run (hs ++ e) y) r = rv (run hs y) r := by
  rcases r with b | t
  · rfl
  · exact run_prefix _ _ _ _ (h t rfl)

theorem emit (N : ℕ) (hs : List Gate) (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (rs : List (Bool ⊕ ℕ)) (hl : rs.length ≤ 2) (hv : ∀ r ∈ rs, ∀ t, r = .inr t → t < N + hs.length) :
    ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
      ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
  have keep : ∀ r : Bool ⊕ ℕ, (∀ t, r = .inr t → t < N + hs.length) → (∀ y : List Bool, y.length = N → rv (run hs y) r = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro r h1 h2
    exact ⟨r, [], by simp, by simp, by simpa using h1, fun y hy => by rw [List.append_nil]; exact h2 y hy⟩
  have add : ∀ g : Gate, fok g → (∀ y : List Bool, y.length = N → g.op.eval (g.inputs.map fun i => (run hs y).getD i false) = op.eval (rs.map (rv (run hs y)))) →
      ∃ (r : Bool ⊕ ℕ) (e : List Gate), e.length ≤ 1 ∧ (∀ g ∈ e, fok g) ∧ (∀ t, r = .inr t → t < N + hs.length + e.length) ∧
        ∀ y : List Bool, y.length = N → rv (run (hs ++ e) y) r = op.eval (rs.map (rv (run hs y))) := by
    intro g h1 h2
    refine ⟨.inr (N + hs.length), [g], by simp, by simpa using h1, ?_, fun y hy => ?_⟩
    · intro t ht
      cases ht
      simp
    · have : N + hs.length = (run hs y).length := by rw [run_length, hy]
      simp only [rv]
      rw [run_snoc, this, getD_at]
      exact h2 y hy
  rcases rs with _ | ⟨r, _ | ⟨s, _ | ⟨u, rs⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
    · exact keep (.inl false) (by simp) (by intro y _; rfl)
    · exact keep (.inl true) (by simp) (by intro y _; rfl)
  · have hr := hv r (by simp)
    rcases hop with rfl | rfl | rfl
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · exact keep r hr (by intro y _; simp [GateOp.eval])
    · rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · exact add ⟨GateOp.not, [t]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · have hr := hv r (by simp)
    have hs' := hv s (by simp)
    rcases hop with rfl | rfl | rfl
    · rcases r with b | t
      · cases b
        · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inl false) (by simp) (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.and, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · cases b
        · exact keep s hs' (by intro y _; simp [GateOp.eval, rv])
        · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · rcases s with b | q
        · cases b
          · exact keep (.inr t) hr (by intro y _; simp [GateOp.eval, rv])
          · exact keep (.inl true) (by simp) (by intro y _; simp [GateOp.eval, rv])
        · exact add ⟨GateOp.or, [t, q]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
    · rcases r with b | t
      · exact keep (.inl (!b)) (by simp) (by intro y _; simp [GateOp.eval, rv])
      · exact add ⟨GateOp.not, [t]⟩ ⟨by simp, by simp⟩ (by intro y _; simp [GateOp.eval, rv])
  · simp at hl

theorem engine2 {X : Type} (n M : ℕ) (C : Circuit) (src tgt : X → List Bool) (hsrc : ∀ x, (src x).length = n) (htgt : ∀ x, (tgt x).length = M) (F : Finset ℕ)
    (hC : PEqualNP.MetaComplexity.FanInTwo C)
    (h0 : ∀ w < n, (∃ b, ∀ x, (src x).getD w false = b) ∨ ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false)
    (hne : ¬∃ b, ∀ x, C.eval (src x) = b)
    (hF : ∀ j ∈ F, j < C.gates.length ∧ ((∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
      ∃ w < n + j, ∀ x, (run C.gates (src x)).getD (n + j) false = (run C.gates (src x)).getD w false)) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + F.card ≤ C.size ∧ ∀ x, D.eval (tgt x) = C.eval (src x) := by
  classical
  have key : ∀ k, k ≤ C.gates.length → ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k).card ≤ k ∧
      (∀ w t, w < n + k → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + k, (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨[], fun w => if h : ∃ t, t < M ∧ ∀ x, (src x).getD w false = (tgt x).getD t false then .inr h.choose else if hb : ∃ b, ∀ x, (src x).getD w false = b then .inl hb.choose else .inl false, by simp, by simp, ?_, ?_⟩
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
      obtain ⟨hs, m, h1, h2, h3, h4⟩ := ih (by omega)
      have hk' : k < C.gates.length := by omega

      have fin : ∀ (r : Bool ⊕ ℕ) (e : List Gate), (∀ g ∈ e, fok g) → (∀ t, r = .inr t → t < M + hs.length + e.length) → e.length + (if k ∈ F then 1 else 0) ≤ 1 →
          (∀ x : X, (run C.gates (src x)).getD (n + k) false = rv (run (hs ++ e) (tgt x)) r) →
          ∃ (hs : List Gate) (m : ℕ → Bool ⊕ ℕ), (∀ g ∈ hs, fok g) ∧ hs.length + (F.filter fun j => j < k + 1).card ≤ k + 1 ∧
      (∀ w t, w < n + (k + 1) → m w = .inr t → t < M + hs.length) ∧
      ∀ x : X, ∀ w < n + (k + 1), (run C.gates (src x)).getD w false = rv (run hs (tgt x)) (m w) := by
        intro r e he hr hlen hval
        refine ⟨hs ++ e, Function.update m (n + k) r, ?_, ?_, ?_, ?_⟩
        · intro g hg
          rcases List.mem_append.1 hg with hg | hg
          · exact h1 g hg
          · exact he g hg
        · have e1 : (F.filter fun j => j < k + 1) ⊆ (F.filter fun j => j < k) ∪ (if k ∈ F then {k} else ∅) := by
            intro j hj
            rw [Finset.mem_filter] at hj
            rcases Nat.lt_or_ge j k with h | h
            · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hj.1, h⟩)
            · have : j = k := by omega
              subst this
              rw [ite_eq_left hj.1]; simp
          have e2 := (Finset.card_le_card e1).trans (Finset.card_union_le _ _)
          rw [List.length_append]
          by_cases hkF : k ∈ F
          · rw [ite_eq_left hkF] at e2 hlen
            rw [Finset.card_singleton] at e2
            omega
          · rw [ite_eq_right hkF] at e2 hlen
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
        · exact fin (.inl b) [] (by simp) (by simp) (by simp [hkF]) (fun x => hb x)
        · refine fin (m w) [] (by simp) (fun t ht => by simpa using h3 w t hw ht) (by simp [hkF]) (fun x => ?_)
          rw [List.append_nil, ← h4 x w hw]
          exact hb x
      · have hg := hC _ (List.getElem_mem hk')
        have hop : C.gates[k].op = GateOp.and ∨ C.gates[k].op = GateOp.or ∨ C.gates[k].op = GateOp.not := by simpa using hg.1
        let m' : ℕ → Bool ⊕ ℕ := fun i => if i < n + k then m i else .inl false
        obtain ⟨r, e, e1, e2, e3, e4⟩ := emit M hs C.gates[k].op hop (C.gates[k].inputs.map m') (by rw [List.length_map]; exact hg.2) (by
          intro r hr t ht
          obtain ⟨i, _, rfl⟩ := List.mem_map.1 hr
          simp only [m'] at ht
          split_ifs at ht with h
          exact h3 i t h ht)
        refine fin r e e2 e3 (by simp [hkF]; exact e1) (fun x => ?_)
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
  obtain ⟨hs, m, h1, h2, h3, h4⟩ := key C.gates.length le_rfl
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
  · refine ⟨⟨hs, t⟩, ?_, h2, fun x => ?_⟩
    · intro g hg
      exact ⟨by simpa using (h1 g hg).1, (h1 g hg).2⟩
    · have := hev x
      rw [hm] at this
      exact this.symm

theorem simplifyRead {X : Type} (n : ℕ) (C : Circuit) (src : X → List Bool)
    (hsrc : ∀ x, (src x).length = n) (hC : FanInTwo C) (j : ℕ) (hj' : j < C.gates.length)
    (u : ℕ) (hr : C.gates[j].inputs.head? = some u ∨ C.gates[j].op ≠ GateOp.not ∧ u ∈ C.gates[j].inputs)
    (hcu : ∃ c, ∀ x, (run C.gates (src x)).getD u false = c) :
    (∃ b, ∀ x, (run C.gates (src x)).getD (n + j) false = b) ∨
    ∃ w < n+j, ∀ x, (run C.gates (src x)).getD (n+j) false = (run C.gates (src x)).getD w false := by
  let W := fun (x : X) w => (run C.gates (src x)).getD w false
  change (∃ b, ∀ x, W x (n+j) = b) ∨ ∃ w < n+j, ∀ x, W x (n+j) = W x w
  have Wg : ∀ x k (hk : k < C.gates.length), W x (n+k) = C.gates[k].op.eval (C.gates[k].inputs.map fun i => if i<n+k then W x i else false) := by
    intro x k hk
    have h := run_gate C.gates (src x) k hk
    rw [hsrc] at h
    exact h
  have hcr : ∃ c, ∀ x, (if u < n + j then W x u else false) = c := by
    obtain ⟨c, hc⟩ := hcu
    by_cases h : u < n + j
    · exact ⟨c, fun x => by rw [ite_eq_left h]; exact hc x⟩
    · exact ⟨false, fun x => by rw [ite_eq_right h]⟩
  obtain ⟨c, hc⟩ := hcr
  have cp : ∀ b, (∃ c, ∀ x, (if b < n + j then W x b else false) = c) ∨ ∃ w < n + j, ∀ x, (if b < n + j then W x b else false) = W x w := by
    intro b
    by_cases h : b < n + j
    · exact Or.inr ⟨b, h, fun x => by rw [ite_eq_left h]⟩
    · exact Or.inl ⟨false, fun x => by rw [ite_eq_right h]⟩
  have hop : C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ C.gates[j].op = PEqualNP.CircuitLowerBounds.GateOp.not := by simpa using (hC _ (List.getElem_mem hj')).1
  have hlen := (hC _ (List.getElem_mem hj')).2
  have wg := fun x => Wg x j hj'
  generalize C.gates[j].inputs = l at hr hlen wg
  generalize C.gates[j].op = o at hr hop wg
  have hmem : u ∈ l := by
    rcases hr with h | ⟨_, h⟩
    · exact List.mem_of_mem_head? h
    · exact h
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · cases hmem
  · have ha : u = a := by simpa using hmem
    subst ha
    refine Or.inl ⟨o.eval [c], fun x => ?_⟩
    rw [wg]; simp only [List.map_cons, List.map_nil, hc]
  · by_cases ha : u = a
    · subst ha
      rcases hop with rfl | rfl | rfl
      · cases c
        · refine Or.inl ⟨false, fun x => ?_⟩
          rw [wg]; simp only [List.map_cons, List.map_nil, hc]; rfl
        · have e : ∀ x, W x (n + j) = (if b < n + j then W x b else false) := by
            intro x
            rw [wg]; simp only [List.map_cons, List.map_nil, hc]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          simp only [e]
          exact cp b
      · cases c
        · have e : ∀ x, W x (n + j) = (if b < n + j then W x b else false) := by
            intro x
            rw [wg]; simp only [List.map_cons, List.map_nil, hc]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          simp only [e]
          exact cp b
        · refine Or.inl ⟨true, fun x => ?_⟩
          rw [wg]; simp only [List.map_cons, List.map_nil, hc]; rfl
      · refine Or.inl ⟨!c, fun x => ?_⟩
        rw [wg]; simp only [List.map_cons, List.map_nil, hc]; rfl
    · have hb : u = b := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        exact hmem.resolve_left ha
      subst hb
      rcases hop with rfl | rfl | rfl
      · cases c
        · refine Or.inl ⟨false, fun x => ?_⟩
          rw [wg]; simp only [List.map_cons, List.map_nil, hc]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
        · have e : ∀ x, W x (n + j) = (if a < n + j then W x a else false) := by
            intro x
            rw [wg]; simp only [List.map_cons, List.map_nil, hc]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          simp only [e]
          exact cp a
      · cases c
        · have e : ∀ x, W x (n + j) = (if a < n + j then W x a else false) := by
            intro x
            rw [wg]; simp only [List.map_cons, List.map_nil, hc]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
          simp only [e]
          exact cp a
        · refine Or.inl ⟨true, fun x => ?_⟩
          rw [wg]; simp only [List.map_cons, List.map_nil, hc]; simp [PEqualNP.CircuitLowerBounds.GateOp.eval]
      · exfalso
        rcases hr with h | ⟨h, _⟩
        · simp only [List.head?_cons, Option.some.injEq] at h
          exact ha h.symm
        · exact h rfl
  · simp at hlen

end PEqualNP.Outside.L_meta_18545

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_18545

theorem PEqualNP.Outside.L_meta_18545 : ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (v : Fin n) (b : Bool) (K : Finset (Fin C.gates.length)), PEqualNP.MetaComplexity.FanInTwo C → (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not → g.inputs.length = 1) → (∃ y : Fin n → Bool, C.eval (List.ofFn (Function.update y v b)) = false) → (∀ j ∈ K, (∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD (n + j.val) false = c) ∨ ∃ w ∈ (C.gates.get j).inputs, ∃ c : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn (Function.update x v b))).getD w false = c) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D ∧ D.size + K.card ≤ C.size ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn (Function.update x v b)) := by
  classical
  intro n C v b K fan hnot hfalse hK
  let F := K.map Fin.valEmbedding
  let src := fun x : Fin n → Bool => List.ofFn (Function.update x v b)
  have hsrc (x : Fin n → Bool) : (src x).length = n := by simp [src]
  have pin (x : Fin n → Bool) : (src x).getD v.val false = b := by
    simp [src,List.getD_eq_getElem?_getD]
  by_cases hconstant : ∃ c, ∀ x, C.eval (src x) = c
  · obtain ⟨c,hc⟩ := hconstant
    obtain ⟨y,hy⟩ := hfalse
    have he : c = false := (hc y).symm.trans hy
    have ht : K.card ≤ C.gates.length := by simpa using Finset.card_le_univ K
    refine ⟨⟨[],n⟩, by simp [FanInTwo], ?_, ?_⟩
    · simpa [Circuit.size] using ht
    · intro x
      change _ = C.eval (src x)
      rw [hc,he]
      simp [Circuit.eval,Circuit.wires,List.getD_eq_getElem?_getD]
  · obtain ⟨D, hf, hs, hd⟩ := engine2 n n C src List.ofFn hsrc (by simp) F fan (by
      intro w hw
      by_cases eq : w = v.val
      · subst w; exact Or.inl ⟨b,pin⟩
      · refine Or.inr ⟨w,hw,fun x => ?_⟩
        have ne : (⟨w,hw⟩ : Fin n) ≠ v := fun e => eq (congrArg Fin.val e)
        simp [src,List.getD_eq_getElem?_getD,hw,Function.update_of_ne ne]) hconstant (by
      intro j hj
      obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
      refine ⟨k.isLt, ?_⟩
      rcases hK k hk with h | ⟨w,hm,c,hc⟩
      · exact Or.inl h
      · apply simplifyRead n C src hsrc fan k.val k.isLt w
        · change w ∈ C.gates[k.val].inputs at hm
          by_cases op : C.gates[k.val].op = GateOp.not
          · left
            have eq := hnot _ (List.getElem_mem k.isLt) op
            generalize C.gates[k.val].inputs = ls at eq hm ⊢
            rcases ls with _ | ⟨i, _ | ⟨q,qs⟩⟩ <;> simp_all
          · exact Or.inr ⟨op,hm⟩
        · exact ⟨c,hc⟩)
    exact ⟨D,hf,by simpa [F] using hs,hd⟩
