import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_687

open PEqualNP.CircuitLowerBounds

def E (D : Finset ℕ) (v : List Bool) : List Bool :=
  ((List.range v.length).filter fun i => decide (i ∉ D)).map fun i => v.getD i false

def c (D : Finset ℕ) (n : ℕ) : ℕ := (D.filter fun i => i < n).card

theorem c_succ (D : Finset ℕ) (n : ℕ) : c D (n + 1) = c D n + if n ∈ D then 1 else 0 := by
  unfold c
  split_ifs with h
  · have : D.filter (fun i => i < n + 1) = insert n (D.filter fun i => i < n) := by
      ext j; simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | h3
        · exact Or.inr ⟨h1, h3⟩
        · exact Or.inl h3
      · rintro (h3 | ⟨h1, h3⟩)
        · subst h3; exact ⟨h, by omega⟩
        · exact ⟨h1, by omega⟩
    rw [this, Finset.card_insert_of_notMem (by simp)]
  · have : D.filter (fun i => i < n + 1) = D.filter fun i => i < n := by
      ext j; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h3 | h3
        · exact h3
        · subst h3; exact absurd h1 h
      · rintro ⟨h1, h3⟩; exact ⟨h1, by omega⟩
    rw [this]; simp

theorem c_le (D : Finset ℕ) (n : ℕ) : c D n ≤ n := by
  induction n with
  | zero => simp [c]
  | succ n ih => rw [c_succ]; split_ifs <;> omega

theorem E_snoc (D : Finset ℕ) (v : List Bool) (b : Bool) :
    E D (v ++ [b]) = E D v ++ (if v.length ∈ D then [] else [b]) := by
  unfold E
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append,
    List.map_append]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have : i < v.length := by
      have := (List.mem_filter.1 hi).1
      simpa using this
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left this]
  · split_ifs with h
    · simp [h]
    · simp [h]

theorem E_len (D : Finset ℕ) (v : List Bool) : (E D v).length + c D v.length = v.length := by
  induction v using List.reverseRecOn with
  | nil => simp [E, c]
  | append_singleton v b ih =>
    rw [E_snoc, List.length_append, List.length_append, List.length_singleton, c_succ]
    split_ifs <;> simp <;> omega

theorem E_get (D : Finset ℕ) (v : List Bool) : ∀ i, i ∉ D → i < v.length →
    i - c D i < (E D v).length ∧ (E D v).getD (i - c D i) false = v.getD i false := by
  induction v using List.reverseRecOn with
  | nil => intro i _ h; simp at h
  | append_singleton v b ih =>
    intro i hi hlt
    rw [List.length_append, List.length_singleton] at hlt
    rw [E_snoc]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hlt with h | h
    · obtain ⟨h1, h2⟩ := ih i hi h
      refine ⟨by rw [List.length_append]; omega, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h1, ← List.getD_eq_getElem?_getD,
        h2, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left h]
    · subst h
      have hl := E_len D v
      have hc := c_le D v.length
      rw [if_neg hi]
      refine ⟨by rw [List.length_append]; simp; omega, ?_⟩
      have e1 : v.length - c D v.length = (E D v).length := by omega
      rw [e1]
      simp [List.getD_eq_getElem?_getD]

theorem E_far (D : Finset ℕ) (v : List Bool) (hD : ∀ i ∈ D, i < v.length) (i : ℕ)
    (hi : v.length ≤ i) : (E D v).getD (i - c D i) false = false := by
  have h1 : c D i = c D v.length := by
    unfold c
    rw [Finset.filter_true_of_mem (fun j hj => by have := hD j hj; omega),
      Finset.filter_true_of_mem (fun j hj => hD j hj)]
  have hl := E_len D v
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
  rfl

theorem gen (D : Finset ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ D) :
    ∀ w : List Bool, (∀ i ∈ D, i < w.length) →
    (gs.map (fun g => (⟨g.op, g.inputs.map fun w => w - c D w⟩ : Gate))).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (E D w) =
    E D (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hw
    simp only [List.map_cons, List.foldl_cons]
    have hval : g.op.eval ((g.inputs.map fun w => w - c D w).map fun i => (E D w).getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro i hi
      have hiD := hg g (by simp) i hi
      simp only [Function.comp]
      by_cases hlt : i < w.length
      · exact (E_get D w i hiD hlt).2
      · rw [E_far D w hw i (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega)]
        rfl
    rw [hval]
    have hn : w.length ∉ D := fun h => by have := hw _ h; omega
    have := ih (fun g' hg' => hg g' (by simp [hg'])) (w ++ [g.op.eval
      (g.inputs.map fun i => w.getD i false)])
      (fun i hi => by have := hw i hi; simp; omega)
    rw [E_snoc, if_neg hn] at this
    exact this

end PEqualNP.Outside.L_lib_687

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_lib_687 in
theorem PEqualNP.Outside.L_lib_687 : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool) (D : Finset ℕ),
  (∀ i ∈ D, i < x.length) →
  (∀ g ∈ C.gates, ∀ i ∈ g.inputs, i ∉ D) →
  let erase : List Bool → List Bool := fun v =>
    ((List.range v.length).filter fun i => decide (i ∉ D)).map fun i => v.getD i false
  let ren : ℕ → ℕ := fun w => w - (D.filter fun i => i < w).card
  let small : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨C.gates.map (fun g => ⟨g.op, g.inputs.map ren⟩), ren C.output⟩
  small.wires (erase x) = erase (C.wires x) := by
  intro C x D hD hg
  exact gen D C.gates hg x hD
