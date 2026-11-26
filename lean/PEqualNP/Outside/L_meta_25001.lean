import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25001

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
  PEqualNP.EdgeOwnership PEqualNP.Core PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false
lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

theorem snoc {α : Type} (l : List α) (b d : α) (w : ℕ) :
    (l ++ [b]).getD w d = if w < l.length then l.getD w d else if w = l.length then b else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp


theorem clen (n : ℕ) (gs : List Gate) : (gs.foldl (coneStep n) []).length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih => simp [List.foldl_append, coneStep, ih]

theorem cmem (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
    (j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro j i; simp
  | append_singleton gs g ih =>
    intro j i
    have hl := clen n gs
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize gs.foldl (coneStep n) [] = F at ih hl ⊢
    unfold coneStep
    have e : ∀ k b, k < gs.length → (F ++ [b]).getD k [] = F.getD k [] := fun k b hk => by
      rw [snoc, if_pos (by omega)]
    rw [snoc, snoc, hl]
    split_ifs with h1 h2
    · rw [ih j i]
      constructor
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨by simp; omega, w, hw, h3, h4, by rwa [e _ _ (by omega)]⟩
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨h1, w, hw, h3, h4, by rwa [e _ _ (by omega)] at h5⟩
    · subst h2
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h3, h4⟩, h5⟩
        exact ⟨by simp, w, hw, h3, h4, by rwa [e _ _ (by omega)]⟩
      · rintro ⟨-, w, hw, h3, h4, h5⟩
        exact ⟨w, ⟨hw, h3, h4⟩, by rwa [e _ _ (by omega)] at h5⟩
    · simp

theorem ctrans (n : ℕ) (C : Circuit) : ∀ j i k, InCone n C i j → InCone n C k i → InCone n C k j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ihj =>
    intro i k hi hk
    unfold InCone cones at *
    obtain ⟨hj, w, hw, h3, h4, h5⟩ := (cmem n C.gates j i).1 hi
    refine (cmem n C.gates j k).2 ⟨hj, w, hw, h3, h4, Or.inr ?_⟩
    rcases h5 with rfl | h5
    · exact hk
    · exact ihj _ (by omega) i k h5 hk

/-- The output cone is closed under reading earlier gates. -/
theorem oclosed (N : ℕ) (C : Circuit) (j : ℕ) (hj : InOutputCone N C j) (w : ℕ)
    (hw : w ∈ (gateAt C j).inputs) (h1 : N ≤ w) (h2 : w < N + j) : InOutputCone N C (w - N) := by
  have hd : InCone N C (w - N) j := by
    unfold InCone cones
    exact (cmem N C.gates j _).2 ⟨hj.1, w, hw, h1, h2, Or.inl rfl⟩
  refine ⟨by have := hj.1; omega, Or.inr ?_⟩
  rcases hj.2 with h | ⟨h3, h4⟩
  · exact ⟨by omega, by rwa [h, Nat.add_sub_cancel_left]⟩
  · exact ⟨h3, ctrans N C _ _ _ h4 hd⟩


/-- Retain all gate indices and erase the input lists of gates outside the output cone. -/
def trim (N : ℕ) (C : Circuit) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length =>
      if InOutputCone N C j.val then C.gates[j.val] else ⟨GateOp.and, []⟩), C.output⟩

lemma trim_len (N : ℕ) (C : Circuit) : (trim N C).gates.length = C.gates.length := by
  simp [trim]

lemma trim_gate (N : ℕ) (C : Circuit) (j : ℕ) (h : InOutputCone N C j) :
    gateAt (trim N C) j = gateAt C j := by
  have hj := h.1
  simp [gateAt, trim, List.getD_eq_getElem?_getD, hj, h]

lemma trim_mem (N : ℕ) (C : Circuit) (g : Gate) (hg : g ∈ (trim N C).gates) :
    g = ⟨GateOp.and, []⟩ ∨ g ∈ C.gates := by
  simp only [trim, List.mem_ofFn] at hg
  obtain ⟨j, rfl⟩ := hg
  split_ifs
  · exact Or.inr (List.getElem_mem j.isLt)
  · exact Or.inl rfl

lemma trim_eval (N : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = N) :
    (trim N C).eval x = C.eval x := by
  have heq : ∀ j, InOutputCone N C j →
      val (trim N C) x (N + j) = val C x (N + j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj
      have hj2 : j < (trim N C).gates.length := by rw [trim_len]; exact hj.1
      rw [val_gate hx hj2, val_gate hx hj.1, trim_gate N C j hj]
      congr 1
      apply List.map_congr_left
      intro i hi
      by_cases ht : i < N + j
      · simp only [if_pos ht]
        by_cases hn : i < N
        · rw [val_input hx hn, val_input hx hn]
        · have hc := oclosed N C j hj i hi (by omega) ht
          have e : N + (i - N) = i := by omega
          rw [← e]
          exact ih (i - N) (by omega) hc
      · simp only [if_neg ht]
  change val (trim N C) x C.output = val C x C.output
  by_cases hn : C.output < N
  · rw [val_input hx hn, val_input hx hn]
  · by_cases hb : C.output < N + C.gates.length
    · have h : InOutputCone N C (C.output - N) :=
        ⟨by omega, Or.inl (by omega)⟩
      have e : N + (C.output - N) = C.output := by omega
      simpa only [e] using heq (C.output - N) h
    · rw [val_ge hx (by rw [trim_len]; omega), val_ge hx (by omega)]

lemma trim_fanin (N : ℕ) (C : Circuit) (hc : FanInTwo C) : FanInTwo (trim N C) := by
  intro g hg
  rcases trim_mem N C g hg with rfl | hg
  · simp
  · exact hc g hg

lemma gd_and (C : Circuit) {j : ℕ} (h : j < C.gates.length) :
    C.gates.getD j ⟨GateOp.and, []⟩ = gateAt C j := by
  rw [gateAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h]
  rfl

end PEqualNP.Outside.L_meta_25001

open PEqualNP.Outside.L_meta_25001 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.EdgeOwnership PEqualNP.Core PEqualNP.MetaComplexity.NestedCover
theorem PEqualNP.Outside.L_meta_25001 : (∀ (n m : ℕ) (A : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (w : ℕ), w < n + m → PEqualNP.MetaComplexity.FanInTwo C → PEqualNP.Represents.Represents A C → (C.output ≠ w ∧ ∀ g < C.gates.length, (C.output = (n + m) + g ∨ ((n + m) ≤ C.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) C g (C.output - (n + m)))) → w ∉ (C.gates.getD g ⟨PEqualNP.CircuitLowerBounds.GateOp.and, []⟩).inputs) → ∃ C2 : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C2 ∧ PEqualNP.Represents.Represents A C2 ∧ C2.size ≤ C.size ∧ (∀ g ∈ C2.gates, w ∉ g.inputs) ∧ C2.output ≠ w ∧ (∀ i < (n + m), ((∃ g ∈ C2.gates, i ∈ g.inputs) ∨ C2.output = i) → ((∃ g ∈ C.gates, i ∈ g.inputs) ∨ C.output = i))) := by
  intro n m A C w hw hf hr hc
  refine ⟨trim (n+m) C, trim_fanin _ _ hf, ?_, ?_, ?_, hc.1, ?_⟩
  · intro u v
    rw [trim_eval (n+m) C _ (by simp [oneEach])]
    exact hr u v
  · simp [Circuit.size, trim]
  · intro g hg
    simp only [trim, List.mem_ofFn] at hg
    obtain ⟨j, rfl⟩ := hg
    split_ifs with hj
    · have h := hc.2 j.val j.isLt hj.2
      simpa [List.getD_eq_getElem?_getD, j.isLt] using h
    · simp
  · intro i hi h
    rcases h with ⟨g, hg, hgi⟩ | ho
    · rcases trim_mem _ _ g hg with rfl | hgc
      · simp at hgi
      · exact Or.inl ⟨g, hgc, hgi⟩
    · exact Or.inr ho
