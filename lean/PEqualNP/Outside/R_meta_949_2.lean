import Mathlib
import PEqualNP.Defs

-- A color class D consists of oriented edges. Its tails and heads span a
-- biclique exactly when every tail is adjacent to every head of the class.
-- Allowing either orientation avoids conflating pairwise compatibility of
-- unoriented edges with compatibility of the whole class (e.g. a triangle).
--
-- Two independent censuses, on the 156 isomorphism classes of six-vertex
-- graphs. The proposed cutoffs for budgets 0,1,2,3 are 1,10,71,151:
-- enumerate disjoint ternary-labeled shores and take unions of edge masks.
-- At budget 4 the union enumeration already contains all 32768 labeled
-- graphs. Every cover also gives an AND-count circuit, using one AND per
-- rectangle. Thus exceeding one of these cutoffs detects any separation;
-- the circuit census only needs lower bounds, never a proof of optimality.
theorem PEqualNP.Outside.R_meta_949_2
    (hColors : ∀ (b : Fin 4) (S : Finset (SimpleGraph (Fin 6))),
      (∀ G ∈ S, ∀ H ∈ S, Nonempty (SimpleGraph.Iso G H) → G = H) →
      (∀ G ∈ S, ∃ D : Fin b.val → Fin 6 → Fin 6 → Prop,
        (∀ a b, G.Adj a b → ∃ i, D i a b ∨ D i b a) ∧
        (∀ i a b c d, D i a b → D i c d → G.Adj a d)) →
      S.card ≤ (if b = 0 then 1 else if b = 1 then 10 else if b = 2 then 71 else 151))
    (hSearch : ∃ (b : Fin 4) (S : Finset (SimpleGraph (Fin 6))),
      (if b = 0 then 1 else if b = 1 then 10 else if b = 2 then 71 else 151) < S.card ∧
      (∀ G ∈ S, ∀ H ∈ S, Nonempty (SimpleGraph.Iso G H) → G = H) ∧
      ∀ G ∈ S, ∃ C : PEqualNP.AndCount.AndCountCircuit 6, C.size ≤ b.val ∧ C.WellFormed ∧
        ∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
          (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
          C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) :
    ∃ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6), C.WellFormed ∧ (∀ I : Finset (Fin 6), (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) → (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) ∧ ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ C.size ∧ (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧ (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k, (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i))) := by
  classical
  obtain ⟨b, S, hcard, hIso, hC⟩ := hSearch
  -- The equivalence is for each graph and budget separately, with no census
  -- or circuit assumptions; unused colors correspond to empty rectangles.
  have bridge (G : SimpleGraph (Fin 6)) :
      (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)), k ≤ b.val ∧
        (∀ i, ∀ a ∈ X i, ∀ d ∈ Y i, G.Adj a d) ∧
        ∀ a d, G.Adj a d → ∃ i, (a ∈ X i ∧ d ∈ Y i) ∨ (d ∈ X i ∧ a ∈ Y i)) ↔
      (∃ D : Fin b.val → Fin 6 → Fin 6 → Prop,
        (∀ a d, G.Adj a d → ∃ i, D i a d ∨ D i d a) ∧
        ∀ i a d c f, D i a d → D i c f → G.Adj a f) := by
    constructor
    · rintro ⟨k, X, Y, hk, hxy, hc⟩
      refine ⟨fun i a d => ∃ j : Fin k, j.val = i.val ∧ a ∈ X j ∧ d ∈ Y j, ?_, ?_⟩
      · intro a d had
        obtain ⟨j, hj⟩ := hc a d had
        refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hk⟩, ?_⟩
        rcases hj with hj | hj
        · exact Or.inl ⟨j, rfl, hj⟩
        · exact Or.inr ⟨j, rfl, hj⟩
      · rintro i a d c f ⟨j, hj, ha, _⟩ ⟨l, hl, _, hf⟩
        have he : j = l := Fin.ext (hj.trans hl.symm)
        subst l
        exact hxy j a ha f hf
    · rintro ⟨D, hc, hcross⟩
      refine ⟨b.val, fun i => Finset.univ.filter (fun a => ∃ d, D i a d),
        fun i => Finset.univ.filter (fun d => ∃ a, D i a d), le_rfl, ?_, ?_⟩
      · intro i a ha f hf
        obtain ⟨d, had⟩ := (Finset.mem_filter.mp ha).2
        obtain ⟨c, hcf⟩ := (Finset.mem_filter.mp hf).2
        exact hcross i a d c f had hcf
      · intro a d had
        obtain ⟨i, hi⟩ := hc a d had
        refine ⟨i, ?_⟩
        rcases hi with h | h
        · left
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, h⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, h⟩⟩
        · right
          exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, h⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, h⟩⟩
  by_contra hn
  apply (Nat.not_le_of_lt hcard)
  apply hColors b S hIso
  intro G hG
  obtain ⟨C, hsize, hwf, heval⟩ := hC G hG
  apply (bridge G).mp
  by_contra hncover
  apply hn
  refine ⟨G, C, hwf, heval, ?_⟩
  rintro ⟨k, X, Y, hk, hxy, hc⟩
  exact hncover ⟨k, X, Y, hk.trans hsize, hxy, hc⟩
