import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18904_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

def Shape (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), (gs[j].op = .and ∨ gs[j].op = .or) ∧
    gs[j].inputs.length = 2 ∧ ∀ i ∈ gs[j].inputs, i < n + j

theorem shape_to {n o : ℕ} {gs : List Gate} (h : Shape n gs) : IsAO2 n (⟨gs,o⟩ : Circuit) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    exact (h j hj).1
  · intro j hj i hi
    apply (h j hj).2.2 i
    simpa only [NestedCover.gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] using hi
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    exact (h j hj).2.1

def appendTable (w : List ℕ) (g : Gate) : List ℕ :=
  w ++ [if g.op.eval [false,true] = true then
      w.getD (g.inputs.getD 0 0) 0 ||| w.getD (g.inputs.getD 1 0) 0
    else w.getD (g.inputs.getD 0 0) 0 &&& w.getD (g.inputs.getD 1 0) 0]

theorem tableLen (w : List ℕ) (gs : List Gate) :
    (gs.foldl appendTable w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, appendTable]
    omega

theorem rightShape {n : ℕ} {gs : List Gate} (good : Shape n gs)
    {op : GateOp} (hop : op = .and ∨ op = .or) {a b : ℕ} (ha : a < n + gs.length)
    (hb : b < n + gs.length) : Shape n (gs ++ [⟨op,[a,b]⟩]) := by
  intro j hj
  by_cases h : j < gs.length
  · rw [List.getElem_append_left h]
    exact good j h
  · have h : j = gs.length := by simp at hj; omega
    subst j
    have e : (gs ++ [⟨op,[a,b]⟩])[gs.length]'(by simp) = (⟨op,[a,b]⟩ : Gate) := by simp
    rw [e]
    refine ⟨hop, rfl, ?_⟩
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl
    · exact ha
    · exact hb

theorem realize (seed : List ℕ) (bank : ℕ → ℕ)
    (init : ∀ i < seed.length, bank i = seed.getD i 0) :
    ∀ k, (∀ j < k, ∃ a < seed.length + j, ∃ b < seed.length + j,
      bank (seed.length + j) = bank a ||| bank b ∨ bank (seed.length + j) = bank a &&& bank b) →
    ∃ gs : List Gate, gs.length = k ∧ Shape seed.length gs ∧
      ∀ i < seed.length + k, (gs.foldl appendTable seed).getD i 0 = bank i := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨[], rfl, by simp [Shape], fun i hi => (init i (by simpa using hi)).symm⟩
  | succ k ih =>
    intro step
    obtain ⟨gs,hlen,sh,agree⟩ := ih (fun j hj => step j (Nat.lt_succ_of_lt hj))
    obtain ⟨a,ha,b,hb,hcalc⟩ := step k (Nat.lt_succ_self k)
    obtain ⟨op,hop,eq⟩ : ∃ op : GateOp, (op = .and ∨ op = .or) ∧
      (appendTable (gs.foldl appendTable seed) ⟨op,[a,b]⟩).getD
        (seed.length + k) 0 = bank (seed.length + k) := by
      have len : (gs.foldl appendTable seed).length = seed.length + k := by rw [tableLen,hlen]
      have last (v : ℕ) :
          (gs.foldl appendTable seed ++ [v]).getD (seed.length + k) 0 = v := by
        rw [← len]
        simp [List.getD_eq_getElem?_getD]
      rcases hcalc with hor|hand
      · refine ⟨.or, Or.inr rfl, ?_⟩
        change (gs.foldl appendTable seed ++ [(gs.foldl appendTable seed).getD a 0 |||
          (gs.foldl appendTable seed).getD b 0]).getD (seed.length + k) 0 = _
        rw [last, agree a ha, agree b hb, hor]
      · refine ⟨.and, Or.inl rfl, ?_⟩
        change (gs.foldl appendTable seed ++ [(gs.foldl appendTable seed).getD a 0 &&&
          (gs.foldl appendTable seed).getD b 0]).getD (seed.length + k) 0 = _
        rw [last, agree a ha, agree b hb, hand]
    refine ⟨gs ++ [⟨op,[a,b]⟩], by simp [hlen], rightShape sh hop (hlen ▸ ha) (hlen ▸ hb), ?_⟩
    intro i hi
    rw [List.foldl_append]
    change (appendTable (gs.foldl appendTable seed) ⟨op,[a,b]⟩).getD i 0 = _
    by_cases h : i < seed.length + k
    · have h' : i < (gs.foldl appendTable seed).length := by simpa [tableLen, hlen] using h
      simpa [appendTable, List.getD_eq_getElem?_getD, List.getElem?_append_left h'] using agree i h
    · have he : i = seed.length + k := by omega
      subst i
      exact eq
end PEqualNP.Outside.L_meta_18904_aux

open PEqualNP.Outside.L_meta_18904_aux in
theorem PEqualNP.Outside.L_meta_18904 : (∀ (x1 : List ℕ) (x2 : ℕ) (x3 : ℕ → ℕ), (∀ x4 < x1.length, x3 x4 = x1.getD x4 (0 : ℕ)) → (∀ x5 < x2, ∃ x7 < x1.length + x5, ∃ x8 < x1.length + x5, x3 (x1.length + x5) = x3 x7 ||| x3 x8 ∨ x3 (x1.length + x5) = x3 x7 &&& x3 x8) → ∀ x6 < x1.length + x2, ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit), x8.size ≤ x2 ∧ PEqualNP.TopForm.IsAO2 x1.length x8 ∧ (List.foldl (fun (x9 : List ℕ) (x10 : PEqualNP.CircuitLowerBounds.Gate) => x9 ++ [if x10.op.eval [Bool.false, Bool.true] = Bool.true then x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) ||| x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ) else x9.getD (x10.inputs.getD (0 : ℕ) (0 : ℕ)) (0 : ℕ) &&& x9.getD (x10.inputs.getD (1 : ℕ) (0 : ℕ)) (0 : ℕ)]) x1 x8.gates).getD x8.output (0 : ℕ) = x3 x6) := by
  intro seed k bank init step i hi
  obtain ⟨gs,hsize,sh,agree⟩ := realize seed bank init k step
  exact ⟨⟨gs,i⟩, by simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using hsize.le,
    shape_to sh, agree i hi⟩
