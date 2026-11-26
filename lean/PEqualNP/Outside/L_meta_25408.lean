import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25408_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def compute (x : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => x.getD i false)

def step (x : List Bool) (g : Gate) : List Bool := x ++ [compute x g]

theorem snoc (l : List Bool) (b : Bool) (i : ℕ) :
    (l ++ [b]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    rfl

def Below (x y : List Bool) : Prop := ∀ i, x.getD i false = true → y.getD i false = true

theorem compute_monotone {x y : List Bool} (h : Below x y) {g : Gate}
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) :
    compute x g = true → compute y g = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with e | e
  · simp only [compute, e, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro h0 a ha
    obtain ⟨i, hi, rfl⟩ := ha
    exact h i (h0 _ ⟨i, hi, rfl⟩)
  · simp only [compute, e, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨a, ⟨i, hi, rfl⟩, ea⟩
    exact ⟨y.getD i false, ⟨i, hi, rfl⟩, h i ea⟩

theorem fold_monotone (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    {x y : List Bool} (he : x.length = y.length) (h : Below x y) :
    Below (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact h
  | cons g gs ih =>
    have hnext : Below (step x g) (step y g) := by
      intro i hi
      simp only [step, snoc, ← he] at hi ⊢
      split_ifs at hi ⊢
      · exact h i hi
      · exact compute_monotone h (hg g (by simp)) hi
    exact ih (fun a ha => hg a (List.mem_cons_of_mem _ ha)) (by simp [step, he]) hnext


theorem len (gs : List Gate) (x : List Bool) : (gs.foldl step x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp
  | append_singleton gs g ih => simp [List.foldl_append, step, ih]; omega


theorem cone (N : ℕ) (gs : List Gate) (hg : ∀ g ∈ gs, g.inputs.length ≤ 2) (R : Finset ℕ) :
    ∃ R' : Finset ℕ, R'.card ≤ R.card + gs.length ∧ ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R', x.getD i false = y.getD i false) →
      ∀ w ∈ R, (gs.foldl step x).getD w false = (gs.foldl step y).getD w false := by
  induction gs using List.reverseRecOn generalizing R with
  | nil => exact ⟨R, by simp, fun x y _ _ h => by simpa using h⟩
  | append_singleton gs g ih =>
    have hg' : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun g' h => hg g' (by simp [h])
    have h2 : g.inputs.length ≤ 2 := hg g (by simp)
    let t := N + gs.length
    let R0 := if t ∈ R then R.erase t ∪ g.inputs.toFinset else R
    obtain ⟨R', hc, hR'⟩ := ih hg' R0
    refine ⟨R', ?_, ?_⟩
    · have : R0.card ≤ R.card + 1 := by
        simp only [R0]; split_ifs with ht
        · have := Finset.card_union_le (R.erase t) g.inputs.toFinset
          have := Finset.card_erase_of_mem ht
          have := List.toFinset_card_le g.inputs
          have : 0 < R.card := Finset.card_pos.2 ⟨t, ht⟩
          omega
        · omega
      simp; omega
    · intro x y hx hy hxy w hw
      have e := hR' x y hx hy hxy
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, step, compute]
      rw [snoc, snoc, len, len, hx, hy]
      split_ifs with h1 h3
      · exact e w (by simp only [R0]; split_ifs <;> simp_all; omega)
      · have ht : t ∈ R := by simp only [t]; rw [← h3]; exact hw
        congr 1
        refine List.map_congr_left fun i hi => e i ?_
        simp [R0, ht, hi]
      · rfl


theorem setD (l : List Bool) (k i : ℕ) :
    (l.set k false).getD i false = if i = k then false else l.getD i false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases h : k = i
  · subst h; simp only [ite_true]; split_ifs <;> rfl
  · simp [h, Ne.symm h]


theorem each_value {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = decide (i = u.val ∨ i = n + v.val) := by
  have hu := u.isLt
  have hv := v.isLt
  apply Bool.eq_iff_iff.2
  simp only [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn,
    List.getElem?_ofFn]
  split_ifs <;> simp [Fin.ext_iff] <;> omega




theorem needed {N : ℕ} {C : Circuit} (hC : Monotone2 C) (R : Finset ℕ)
    (hR : ∀ x y : List Bool, x.length = N → y.length = N →
      (∀ i ∈ R, x.getD i false = y.getD i false) →
      ∀ w ∈ ({C.output} : Finset ℕ),
        (C.gates.foldl step x).getD w false = (C.gates.foldl step y).getD w false)
    {x y : List Bool} (hx : x.length = N) (hy : y.length = N) (i : ℕ)
    (he : Below (x.set i false) y) (ht : C.eval x = true) (hf : C.eval y = false) :
    i ∈ R := by
  by_contra h
  have hr : C.eval x = C.eval (x.set i false) := by
    apply hR x (x.set i false) hx (by simpa using hx) _ C.output (Finset.mem_singleton_self _)
    intro a ha
    have hn : a ≠ i := fun e => h (e ▸ ha)
    rw [setD, ite_eq_right hn]
  have hmono := fold_monotone C.gates (fun a ha => (hC a ha).1)
    (show (x.set i false).length = y.length by simp [hx, hy]) he C.output
  have hv : C.eval y = true := hmono (hr.symm.trans ht)
  rw [hf] at hv
  contradiction



def graph {n : ℕ} (S T : Finset (Fin n)) (u v : Fin n) : Bool :=
  decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))

theorem graph_lower {n : ℕ} (hn : 3 ≤ n) (S T : Finset (Fin n))
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) (hT : T.Nonempty) (hTc : Tᶜ.Nonempty)
    (C : Circuit) (hC : Monotone2 C) (hG : Represents (graph S T) C) : 2 * n - 1 ≤ C.size := by
  obtain ⟨R, hR, hr⟩ := cone (n + n) C.gates (fun g hg => (hC g hg).2) {C.output}
  rw [Finset.card_singleton] at hR
  have forceRow (u u' v : Fin n) (ht : graph S T u v = true)
      (hf : graph S T u' v = false) : u.val ∈ R := by
    apply needed hC R hr (x := oneEach u v) (y := oneEach u' v)
      (by simp [oneEach]) (by simp [oneEach]) u.val _ ((hG u v).trans ht) ((hG u' v).trans hf)
    intro i hi
    rw [setD] at hi
    by_cases he : i = u.val
    · simp [he] at hi
    · simp only [ite_eq_right he, each_value, decide_eq_true_eq] at hi
      rw [each_value, decide_eq_true_eq]
      exact Or.inr (hi.resolve_left he)
  have forceCol (u v v' : Fin n) (ht : graph S T u v = true)
      (hf : graph S T u v' = false) : n + v.val ∈ R := by
    apply needed hC R hr (x := oneEach u v) (y := oneEach u v')
      (by simp [oneEach]) (by simp [oneEach]) (n + v.val) _ ((hG u v).trans ht) ((hG u v').trans hf)
    intro i hi
    rw [setD] at hi
    by_cases he : i = n + v.val
    · simp [he] at hi
    · simp only [ite_eq_right he, each_value, decide_eq_true_eq] at hi
      rw [each_value, decide_eq_true_eq]
      exact Or.inl (hi.resolve_right he)
  have row (u : Fin n) : u.val ∈ R := by
    by_cases hu : u ∈ S
    · obtain ⟨u', hu'⟩ := hSc
      obtain ⟨v, hv⟩ := hT
      have hnot := Finset.mem_compl.mp hu'
      exact forceRow u u' v (by simp [graph, hu, hv]) (by simp [graph, hnot, hv])
    · obtain ⟨u', hu'⟩ := hS
      obtain ⟨v, hv⟩ := hTc
      have hnot := Finset.mem_compl.mp hv
      exact forceRow u u' v (by simp [graph, hu, hnot]) (by simp [graph, hu', hnot])
  have col (v : Fin n) : n + v.val ∈ R := by
    by_cases hv : v ∈ T
    · obtain ⟨u, hu⟩ := hS
      obtain ⟨v', hv'⟩ := hTc
      have hnot := Finset.mem_compl.mp hv'
      exact forceCol u v v' (by simp [graph, hu, hv]) (by simp [graph, hu, hnot])
    · obtain ⟨u, hu⟩ := hSc
      obtain ⟨v', hv'⟩ := hT
      have hnot := Finset.mem_compl.mp hu
      exact forceCol u v v' (by simp [graph, hnot, hv]) (by simp [graph, hnot, hv'])
  have hsub : Finset.range (2 * n) ⊆ R := by
    intro i hi
    have hb := Finset.mem_range.mp hi
    by_cases h : i < n
    · exact row ⟨i, h⟩
    · let v : Fin n := ⟨i - n, by omega⟩
      have e : n + v.val = i := by dsimp [v]; omega
      simpa only [e] using col v
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_range] at hcard
  change R.card ≤ 1 + C.size at hR
  omega

end PEqualNP.Outside.L_meta_25408_aux

open PEqualNP.Outside.L_meta_25408_aux in
theorem PEqualNP.Outside.L_meta_25408 : ∀ (n s : ℕ) (S T : Finset (Fin n)), 3 ≤ n → S.Nonempty → Sᶜ.Nonempty → T.Nonempty → Tᶜ.Nonempty → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide ((u ∈ S ∧ v ∈ T) ∨ (u ∉ S ∧ v ∉ T))) s → 2 * n - 1 ≤ s := by
  intro n s S T hn hS hSc hT hTc h
  obtain ⟨C, hC, hs, hr⟩ := h
  exact (graph_lower hn S T hS hSc hT hTc C hC hr).trans hs
