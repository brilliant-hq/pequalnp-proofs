import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25479

open PEqualNP.CircuitLowerBounds

-- helpers stp, getD_snoc, getD_ge, pre, vgate, run, oe_len, any_mem_true copied from our parked Pre_L_meta_25458

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_snoc (l : List Bool) (b : Bool) (w : ℕ) :
    (l ++ [b]).getD w false = if w < l.length then l.getD w false else if w = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]; simp

theorem getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem stp_len (W : List Bool) (g : Gate) : (stp W g).length = W.length + 1 := by
  simp [stp]

theorem stp_getD (W : List Bool) (g : Gate) (j : ℕ) : (stp W g).getD j false =
    if j < W.length then W.getD j false else if j = W.length then
      g.op.eval (g.inputs.map fun i => W.getD i false) else false := getD_snoc _ _ _

theorem flen : ∀ (gs : List Gate) (W : List Bool), (gs.foldl stp W).length = W.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro W; simp
  | cons g t ih => intro W; rw [List.foldl_cons, ih, stp_len]; simp; omega

theorem pre : ∀ (gs : List Gate) (W : List Bool) (j : ℕ), j < W.length →
    (gs.foldl stp W).getD j false = W.getD j false := by
  intro gs
  induction gs with
  | nil => intro W j _; rfl
  | cons g t ih =>
    intro W j hj
    rw [List.foldl_cons, ih _ _ (by rw [stp_len]; omega), stp_getD, if_pos hj]

theorem vgate : ∀ (gs : List Gate) (W : List Bool) (r : ℕ) (h : r < gs.length),
    (gs.foldl stp W).getD (W.length + r) false = gs[r].op.eval (gs[r].inputs.map fun a =>
      if a < W.length + r then (gs.foldl stp W).getD a false else false) := by
  intro gs
  induction gs with
  | nil => intro W r h; simp at h
  | cons g t ih =>
    intro W r h
    cases r with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pre t (stp W g) W.length (by rw [stp_len]; omega), stp_getD, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro a _
      split_ifs with ha
      · rw [pre t _ a (by rw [stp_len]; omega), stp_getD, if_pos ha]
      · exact getD_ge W a (by omega)
    | succ r =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have := ih (stp W g) r (by simp at h; omega)
      rw [stp_len] at this
      rw [show W.length + (r + 1) = W.length + 1 + r by omega]
      exact this

theorem run (R : ℕ → Bool → Prop) : ∀ (gs : List Gate) (W : List Bool),
    (∀ j < W.length, R j (W.getD j false)) →
    (∀ r (h : r < gs.length) (w : List Bool), w.length = W.length + r →
      (∀ j < W.length + r, R j (w.getD j false)) →
      R (W.length + r) (gs[r].op.eval (gs[r].inputs.map fun a => w.getD a false))) →
    ∀ j < W.length + gs.length, R j ((gs.foldl stp W).getD j false) := by
  intro gs
  induction gs with
  | nil => intro W hW _ j hj; exact hW j (by simpa using hj)
  | cons g t ih =>
    intro W hW H j hj
    rw [List.foldl_cons]
    apply ih (stp W g)
    · intro j' hj'
      rw [stp_len] at hj'
      rw [stp_getD]
      by_cases h1 : j' < W.length
      · rw [if_pos h1]; exact hW j' h1
      · have e : j' = W.length := by omega
        rw [if_neg h1, if_pos e]
        subst e
        have := H 0 (by simp) W (by simp) (by intro j2 hj2; exact hW j2 (by omega))
        simpa using this
    · intro r hr w hw hrel
      rw [stp_len] at hw hrel ⊢
      have := H (r + 1) (by simp; omega) w (by omega) (by intro j2 hj2; exact hrel j2 (by omega))
      rw [show W.length + 1 + r = W.length + (r + 1) by omega]
      simpa using this
    · rw [stp_len]; simp at hj; omega

theorem oe_len {n m : ℕ} (u : Fin n) (v : Fin m) : (PEqualNP.Represents.oneEach u v).length = n + m := by
  simp [PEqualNP.Represents.oneEach]

theorem all_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l)
    (h : GateOp.and.eval (l.map f) = true) : f a = true := by
  have h' : (l.map f).all id = true := h
  rw [List.all_eq_true] at h'
  exact h' (f a) (List.mem_map.2 ⟨a, ha, rfl⟩)

theorem any_mem_true (l : List ℕ) (f : ℕ → Bool) (a : ℕ) (ha : a ∈ l) (h : f a = true) :
    GateOp.or.eval (l.map f) = true := by
  show (l.map f).any id = true
  rw [List.any_eq_true]
  exact ⟨f a, List.mem_map.2 ⟨a, ha, rfl⟩, h⟩

theorem oe_get {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (PEqualNP.Represents.oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  unfold PEqualNP.Represents.oneEach
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i n with h | h
  · rw [List.getElem?_append_left (by simp; omega)]
    simp only [List.getElem?_ofFn, h, dite_true, Option.getD_some, Fin.ext_iff]
    apply decide_eq_decide.2
    constructor <;> intro hh <;> omega
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_ofFn, List.getElem?_ofFn]
    by_cases h2 : i - n < m
    · simp only [h2, dite_true, Option.getD_some, Fin.ext_iff]
      apply decide_eq_decide.2
      constructor <;> intro hh <;> omega
    · simp only [h2, dite_false, Option.getD_none]
      symm
      apply decide_eq_false
      omega

theorem uniq (C : Circuit) (s : ℕ)
    (h : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) s = 1)
    (k p : ℕ) (hk : k < C.gates.length) (hp : p < C.gates.length)
    (hks : s ∈ (C.gates[k]).inputs) (hps : s ∈ (C.gates[p]).inputs) : k = p := by
  by_contra hne
  unfold PEqualNP.MetaComplexity.NestedCover.readsIn at h
  have hsub : ({k, p} : Finset ℕ) ⊆ Finset.range C.size := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Finset.mem_range, Circuit.size]
    omega
  have hle := Finset.sum_le_sum_of_subset hsub
    (f := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).inputs.count s)
  rw [Finset.sum_pair hne, h] at hle
  have e1 : PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hk]
  have e2 : PEqualNP.MetaComplexity.NestedCover.gateAt C p = C.gates[p] := by
    unfold PEqualNP.MetaComplexity.NestedCover.gateAt
    rw [List.getD_eq_getElem _ _ hp]
  simp only [e1, e2] at hle
  have c1 := List.count_pos_iff.2 hks
  have c2 := List.count_pos_iff.2 hps
  omega

theorem reader (C : Circuit) (r c : ℕ) (hrc : r ≠ c)
    (hg : ∃ g ∈ C.gates, g.op = GateOp.or ∧ (g.inputs = [r, c] ∨ g.inputs = [c, r]))
    (h1 : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) r = 1)
    (h2 : PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) c = 1)
    (k : ℕ) (hk : k < C.gates.length) (s : ℕ) (hs : s ∈ (C.gates[k]).inputs) (hsrc : s = r ∨ s = c) :
    (C.gates[k]).op = GateOp.or ∧ r ∈ (C.gates[k]).inputs ∧ c ∈ (C.gates[k]).inputs := by
  obtain ⟨g, hgm, hop, hin⟩ := hg
  obtain ⟨p, hp, hpg⟩ := List.mem_iff_getElem.1 hgm
  have hr : r ∈ (C.gates[p]).inputs := by rw [hpg]; rcases hin with e | e <;> rw [e] <;> simp
  have hc : c ∈ (C.gates[p]).inputs := by rw [hpg]; rcases hin with e | e <;> rw [e] <;> simp
  have hkp : k = p := by
    rcases hsrc with e | e
    · subst e; exact uniq C s h1 k p hk hp hs hr
    · subst e; exact uniq C s h2 k p hk hp hs hc
  subst hkp
  exact ⟨by rw [hpg]; exact hop, hr, hc⟩

end PEqualNP.Outside.L_meta_25479

open PEqualNP.Outside.L_meta_25479 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_25479 : ∀ (n m : ℕ) (G : Fin n → Fin m → Bool)
  (C : PEqualNP.CircuitLowerBounds.Circuit)
  (u u' : Fin n) (b b' : Fin m),
  let x := u.val
  let x' := u'.val
  let y := n + b.val
  let y' := n + b'.val
  let paired := fun (r c : ℕ) =>
    ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      (g.inputs = [r, c] ∨ g.inputs = [c, r])
  u ≠ u' → b ≠ b' →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack (n + m) C →
  PEqualNP.Represents.Represents G C →
  paired x y → paired x' y' →
  (∀ w ∈ [x, x', y, y'],
    PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w = 1) →
  C.output ∉ [x, x', y, y'] →
  G u b' = G u' b := by
  intro n m G C u u' b b' x x' y y' paired hu hb _ hrep h1 h2 hread hout
  have ex : x = u.val := rfl
  have ex' : x' = u'.val := rfl
  have ey : y = n + b.val := rfl
  have ey' : y' = n + b'.val := rfl
  have hu1 := u.2
  have hu2 := u'.2
  have hb1 := b.2
  have hb2 := b'.2
  have huv : u.val ≠ u'.val := fun e => hu (Fin.ext e)
  have hbv : b.val ≠ b'.val := fun e => hb (Fin.ext e)
  have hS : ∀ j, j ∈ [x, x', y, y'] ↔ (j = x ∨ j = x' ∨ j = y ∨ j = y') := by intro j; simp
  have rx := hread x (by simp)
  have rx' := hread x' (by simp)
  have ry := hread y (by simp)
  have ry' := hread y' (by simp)
  have hA : ∀ i, (PEqualNP.Represents.oneEach u b').getD i false = decide (i = x ∨ i = y') :=
    fun i => oe_get u b' i
  have hB : ∀ i, (PEqualNP.Represents.oneEach u' b).getD i false = decide (i = x' ∨ i = y) :=
    fun i => oe_get u' b i
  have hAl : (PEqualNP.Represents.oneEach u b').length = n + m := oe_len u b'
  have hBl : (PEqualNP.Represents.oneEach u' b).length = n + m := oe_len u' b
  have hAB : ∀ i, i ∉ [x, x', y, y'] → (PEqualNP.Represents.oneEach u b').getD i false =
      (PEqualNP.Represents.oneEach u' b).getD i false := by
    intro i hi
    rw [hS] at hi
    rw [hA, hB]
    have n1 : ¬ (i = x ∨ i = y') := by tauto
    have n2 : ¬ (i = x' ∨ i = y) := by tauto
    simp only [n1, n2, decide_false]
  have hrun := run (fun j bb => (j ∈ [x, x', y, y'] →
      bb = (PEqualNP.Represents.oneEach u b').getD j false) ∧ (j ∉ [x, x', y, y'] →
      bb = (C.gates.foldl stp (PEqualNP.Represents.oneEach u' b)).getD j false))
    C.gates (PEqualNP.Represents.oneEach u b')
    (by
      intro j hj
      refine ⟨fun _ => rfl, fun hn => ?_⟩
      rw [pre _ _ _ (by rw [hBl]; rw [hAl] at hj; exact hj)]
      exact hAB j hn)
    (by
      intro r hr w hw hrel
      rw [hAl] at hw hrel ⊢
      have hnS : n + m + r ∉ [x, x', y, y'] := by rw [hS]; omega
      refine ⟨fun hm => absurd hm hnS, fun _ => ?_⟩
      have hv := vgate C.gates (PEqualNP.Represents.oneEach u' b) r hr
      rw [hBl] at hv
      rw [hv]
      by_cases hany : ∃ s ∈ (C.gates[r]).inputs, s ∈ [x, x', y, y']
      · obtain ⟨s, hs, hsS⟩ := hany
        rw [hS] at hsS
        have key : (C.gates[r]).op = GateOp.or ∧ ∃ a ∈ (C.gates[r]).inputs, ∃ a' ∈ (C.gates[r]).inputs,
            a ∈ [x, x', y, y'] ∧ a < n + m ∧ a' < n + m ∧
            (PEqualNP.Represents.oneEach u b').getD a false = true ∧
            (PEqualNP.Represents.oneEach u' b).getD a' false = true := by
          rcases hsS with e | e | e | e
          · obtain ⟨ho, hr1, hr2⟩ := reader C x y (by omega) h1 rx ry r hr s hs (Or.inl e)
            refine ⟨ho, x, hr1, y, hr2, by simp, by omega, by omega, ?_, ?_⟩
            · rw [hA]; simp
            · rw [hB]; simp
          · obtain ⟨ho, hr1, hr2⟩ := reader C x' y' (by omega) h2 rx' ry' r hr s hs (Or.inl e)
            refine ⟨ho, y', hr2, x', hr1, by simp, by omega, by omega, ?_, ?_⟩
            · rw [hA]; simp
            · rw [hB]; simp
          · obtain ⟨ho, hr1, hr2⟩ := reader C x y (by omega) h1 rx ry r hr s hs (Or.inr e)
            refine ⟨ho, x, hr1, y, hr2, by simp, by omega, by omega, ?_, ?_⟩
            · rw [hA]; simp
            · rw [hB]; simp
          · obtain ⟨ho, hr1, hr2⟩ := reader C x' y' (by omega) h2 rx' ry' r hr s hs (Or.inr e)
            refine ⟨ho, y', hr2, x', hr1, by simp, by omega, by omega, ?_, ?_⟩
            · rw [hA]; simp
            · rw [hB]; simp
        obtain ⟨hop, a, ha, a', ha', haS, hal, hal', hva, hva'⟩ := key
        rw [hop]
        rw [any_mem_true _ _ a ha (by rw [(hrel a (by omega)).1 haS]; exact hva)]
        rw [any_mem_true _ _ a' ha' (by
          rw [if_pos (by omega), pre _ _ _ (by rw [hBl]; exact hal')]; exact hva')]
      · congr 1
        apply List.map_congr_left
        intro a ha
        have haS : a ∉ [x, x', y, y'] := fun h => hany ⟨a, ha, h⟩
        by_cases hlt : a < n + m + r
        · rw [if_pos hlt]
          exact (hrel a hlt).2 haS
        · rw [if_neg hlt]
          exact getD_ge w a (by omega))
  rw [← hrep u b', ← hrep u' b]
  show (C.gates.foldl stp (PEqualNP.Represents.oneEach u b')).getD C.output false =
    (C.gates.foldl stp (PEqualNP.Represents.oneEach u' b)).getD C.output false
  by_cases hl : C.output < n + m + C.gates.length
  · exact (hrun C.output (by rw [hAl]; exact hl)).2 hout
  · rw [getD_ge _ _ (by rw [flen, hAl]; omega), getD_ge _ _ (by rw [flen, hBl]; omega)]
