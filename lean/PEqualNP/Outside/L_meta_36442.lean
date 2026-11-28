import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36442

open Finset

theorem pair_eq {n : ℕ} {e : Finset (Fin n)} (he : e.card = 2) {a b : Fin n} (ha : a ∈ e)
    (hb : b ∈ e) (hab : a ≠ b) : e = {a, b} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [he, Finset.card_pair hab]

theorem not_old_single {n : ℕ} {E : Finset (Finset (Fin n))} (hE : ∀ e ∈ E, e.card = 2)
    (i : Fin n) : ¬ ∃ e ∈ E, e ⊆ ({i} : Finset (Fin n)) := by
  rintro ⟨e, he, hs⟩
  have := Finset.card_le_card hs
  rw [hE e he, Finset.card_singleton] at this
  omega

def T {n : ℕ} (E : Finset (Finset (Fin n))) (c : Finset (Fin n) → Fin n) (y : Fin n)
    (uC : Bool) (uL : Fin n → Bool) (i : Fin n) : Prop :=
  (∃ e ∈ E, c e = i ∧ y ∈ e ∧ y ≠ i ∧ uL i = true) ∨
    (uC = true ∧ ∃ e ∈ E, c e = y ∧ i ∈ e ∧ i ≠ y)

theorem lhs_iff {n : ℕ} {E : Finset (Finset (Fin n))} (hE : ∀ e ∈ E, e.card = 2)
    (c : Finset (Fin n) → Fin n) (hc : ∀ e ∈ E, c e ∈ e) (y : Fin n) (uC : Bool)
    (uL : Fin n → Bool) (X : Finset (Fin n)) (z : Bool) :
    (∃ e ∈ E, (c e ∈ X ∨ (z = true ∧ c e = y ∧ uC = true)) ∧
        ∃ j ∈ e, j ≠ c e ∧ (j ∈ X ∨ (z = true ∧ j = y ∧ uL (c e) = true))) ↔
      (∃ e ∈ E, e ⊆ X) ∨ (z = true ∧ ∃ i ∈ X, T E c y uC uL i) := by
  constructor
  · rintro ⟨e, he, h1, j, hj, hjc, h2⟩
    have hpe := pair_eq (hE e he) (hc e he) hj (Ne.symm hjc)
    rcases h1 with h1 | ⟨hz, hcy, hu⟩
    · rcases h2 with h2 | ⟨hz, hjy, hl⟩
      · left
        refine ⟨e, he, ?_⟩
        rw [hpe]
        intro x hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      · right
        subst hjy
        exact ⟨hz, c e, h1, Or.inl ⟨e, he, rfl, hj, hjc, hl⟩⟩
    · rcases h2 with h2 | ⟨_, hjy, _⟩
      · right
        refine ⟨hz, j, h2, Or.inr ⟨hu, e, he, hcy, hj, ?_⟩⟩
        rw [← hcy]
        exact hjc
      · exact absurd (hjy.trans hcy.symm) hjc
  · rintro (⟨e, he, hs⟩ | ⟨hz, i, hi, (⟨e, he, rfl, hy, hyi, hl⟩ | ⟨hu, e, he, hce, hie, hiy⟩)⟩)
    · obtain ⟨j, hj, hjc⟩ := Finset.exists_mem_ne (by rw [hE e he]; norm_num) (c e)
      exact ⟨e, he, Or.inl (hs (hc e he)), j, hj, hjc, Or.inl (hs hj)⟩
    · exact ⟨e, he, Or.inl hi, y, hy, hyi, Or.inr ⟨hz, rfl, hl⟩⟩
    · refine ⟨e, he, Or.inr ⟨hz, hce, hu⟩, i, hie, ?_, Or.inl hi⟩
      rw [hce]
      exact hiy

theorem iff_T {n : ℕ} {E : Finset (Finset (Fin n))} (hE : ∀ e ∈ E, e.card = 2)
    (c : Finset (Fin n) → Fin n) (hc : ∀ e ∈ E, c e ∈ e) (y : Fin n) (uC : Bool)
    (uL : Fin n → Bool) (S : Finset (Fin n)) :
    (∀ (X : Finset (Fin n)) (z : Bool),
      (∃ e ∈ E, (c e ∈ X ∨ (z = true ∧ c e = y ∧ uC = true)) ∧
        ∃ j ∈ e, j ≠ c e ∧ (j ∈ X ∨ (z = true ∧ j = y ∧ uL (c e) = true))) ↔
      (∃ e ∈ E, e ⊆ X) ∨ (z = true ∧ ∃ i ∈ S, i ∈ X)) ↔
    ∀ i, T E c y uC uL i ↔ i ∈ S := by
  simp only [lhs_iff hE c hc y uC uL]
  constructor
  · intro h i
    have h1 := h {i} true
    constructor
    · intro hT
      rcases h1.mp (Or.inr ⟨rfl, i, mem_singleton_self i, hT⟩) with h0 | ⟨_, k, hk, hkX⟩
      · exact absurd h0 (not_old_single hE i)
      · rw [mem_singleton] at hkX
        exact hkX ▸ hk
    · intro hi
      rcases h1.mpr (Or.inr ⟨rfl, i, hi, mem_singleton_self i⟩) with h0 | ⟨_, k, hkX, hT⟩
      · exact absurd h0 (not_old_single hE i)
      · rw [mem_singleton] at hkX
        exact hkX ▸ hT
  · intro h X z
    constructor
    · rintro (h0 | ⟨hz, i, hi, hT⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨hz, i, (h i).mp hT, hi⟩
    · rintro (h0 | ⟨hz, i, hi, hX⟩)
      · exact Or.inl h0
      · exact Or.inr ⟨hz, i, hX, (h i).mpr hi⟩

theorem build {n : ℕ} (E : Finset (Finset (Fin n))) (C : Finset (Fin n)) (y : Fin n)
    (R : Finset (Fin n) → Fin n → Prop) (hR : ∀ e ∈ E, ∃ v ∈ e, v ∈ C ∧ R e v) :
    ∃ c : Finset (Fin n) → Fin n, ∀ e ∈ E, c e ∈ e ∧ c e ∈ C ∧ R e (c e) := by
  classical
  refine ⟨fun e => if h : ∃ v ∈ e, v ∈ C ∧ R e v then h.choose else y, fun e he => ?_⟩
  have h := hR e he
  simp only [h, ↓reduceDIte]
  exact h.choose_spec

end PEqualNP.Outside.L_meta_36442

open Finset PEqualNP.Outside.L_meta_36442 in
theorem PEqualNP.Outside.L_meta_36442 :
∀ (n : Nat) (E : Finset (Finset (Fin n))) (C S : Finset (Fin n)),
  (∀ e ∈ E, e.card = 2) → S.Nonempty →
  let cover := fun (K : Finset (Fin n)) => ∀ e ∈ E, ∃ v ∈ e, v ∈ K
  cover C → (∀ v ∈ C, ¬cover (C.erase v)) →
  let N := fun (y : Fin n) =>
    (Finset.univ : Finset (Fin n)).filter (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E)
  let old := fun (X : Finset (Fin n)) => ∃ e ∈ E, e ⊆ X
  ∀ y : Fin n,
    (∃ (center : Finset (Fin n) → Fin n) (useCenter : Bool) (useLeaf : Fin n → Bool),
      (∀ e ∈ E, center e ∈ e ∧ center e ∈ C) ∧
      ∀ (X : Finset (Fin n)) (z : Bool),
        ((∃ e ∈ E,
          (center e ∈ X ∨ (z = true ∧ center e = y ∧ useCenter = true)) ∧
          ∃ j ∈ e, j ≠ center e ∧
            (j ∈ X ∨ (z = true ∧ j = y ∧ useLeaf (center e) = true))) ↔
         old X ∨ (z = true ∧ ∃ i ∈ S, i ∈ X))) ↔
    S ⊆ N y ∧ (y ∉ C ∨ Disjoint S (N y \ C) ∨ N y \ C ⊆ S) := by
  intro n E C S hE _hS
  dsimp only
  intro hC _hmin y
  constructor
  · rintro ⟨c, uC, uL, hc, h⟩
    have hc1 : ∀ e ∈ E, c e ∈ e := fun e he => (hc e he).1
    have hT := (iff_T hE c hc1 y uC uL S).mp h
    have edge : ∀ i, T E c y uC uL i → i ≠ y ∧ ({y, i} : Finset (Fin n)) ∈ E := by
      rintro i (⟨e, he, rfl, hy, hyi, -⟩ | ⟨-, e, he, hce, hie, hiy⟩)
      · refine ⟨Ne.symm hyi, ?_⟩
        rw [← pair_eq (hE e he) hy (hc1 e he) hyi]
        exact he
      · refine ⟨hiy, ?_⟩
        have hye : y ∈ e := by
          rw [← hce]
          exact hc1 e he
        rw [← pair_eq (hE e he) hye hie (Ne.symm hiy)]
        exact he
    refine ⟨fun i hi => ?_, ?_⟩
    · simpa using edge i ((hT i).mpr hi)
    · by_cases hyC : y ∈ C
      · right
        by_cases hdis : Disjoint S ((univ.filter
            (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E)) \ C)
        · exact Or.inl hdis
        · right
          intro k hkN
          by_contra hkS
          rw [Finset.not_disjoint_iff] at hdis
          obtain ⟨i, hiS, hiN⟩ := hdis
          simp only [mem_sdiff, mem_filter, mem_univ, true_and] at hiN hkN
          have huC : uC = true := by
            rcases (hT i).mpr hiS with ⟨e, he, hce, -⟩ | ⟨hu, -⟩
            · exact absurd (hce ▸ (hc e he).2) hiN.2
            · exact hu
          apply hkS
          apply (hT k).mp
          right
          refine ⟨huC, {y, k}, hkN.1.2, ?_, by simp, hkN.1.1⟩
          have h2 := hc _ hkN.1.2
          have h3 : c {y, k} = y ∨ c {y, k} = k := by simpa using h2.1
          rcases h3 with h3 | h3
          · exact h3
          · exact absurd (h3 ▸ h2.2) hkN.2
      · exact Or.inl hyC
  · rintro ⟨hSN, hcase⟩
    have hSN' : ∀ i ∈ S, i ≠ y ∧ ({y, i} : Finset (Fin n)) ∈ E := fun i hi => by
      simpa using hSN hi
    have caseAB : (∀ i ∈ S, i ∈ C) → ∃ (center : Finset (Fin n) → Fin n) (useCenter : Bool)
        (useLeaf : Fin n → Bool), (∀ e ∈ E, center e ∈ e ∧ center e ∈ C) ∧
        ∀ i, T E center y useCenter useLeaf i ↔ i ∈ S := by
      intro hSC
      obtain ⟨c, hcR⟩ := build E C y (fun e v => y ∈ e → ∀ w ∈ e, w ≠ y → w ∈ S → v = w)
        (by
          intro e he
          by_cases h : ∃ w ∈ e, w ≠ y ∧ w ∈ S ∧ y ∈ e
          · obtain ⟨w, hw, hwy, hwS, hy⟩ := h
            refine ⟨w, hw, hSC w hwS, fun _ w' hw' hw'y _ => ?_⟩
            have hpe := pair_eq (hE e he) hy hw (Ne.symm hwy)
            rw [hpe] at hw'
            simp only [mem_insert, mem_singleton] at hw'
            rcases hw' with hw' | hw'
            · exact absurd hw' hw'y
            · exact hw'.symm
          · obtain ⟨v, hv, hvC⟩ := hC e he
            exact ⟨v, hv, hvC, fun hy w hw hwy hwS => absurd ⟨w, hw, hwy, hwS, hy⟩ h⟩)
      refine ⟨c, false, fun i => decide (i ∈ S), fun e he => ⟨(hcR e he).1, (hcR e he).2.1⟩,
        fun i => ?_⟩
      constructor
      · rintro (⟨-, -, -, -, -, h⟩ | ⟨h, -⟩)
        · simpa using h
        · exact absurd h Bool.false_ne_true
      · intro hi
        left
        obtain ⟨hiy, hE'⟩ := hSN' i hi
        refine ⟨{y, i}, hE', ?_, by simp, Ne.symm hiy, by simpa using hi⟩
        exact (hcR _ hE').2.2 (by simp) i (by simp) hiy hi
    have fin : (∃ (center : Finset (Fin n) → Fin n) (useCenter : Bool)
        (useLeaf : Fin n → Bool), (∀ e ∈ E, center e ∈ e ∧ center e ∈ C) ∧
        ∀ i, T E center y useCenter useLeaf i ↔ i ∈ S) := by
      by_cases hyC : y ∈ C
      · rcases hcase with h | hdis | hsub
        · exact absurd hyC h
        · apply caseAB
          intro i hi
          by_contra hiC
          have hiN : i ∈ (univ.filter
              (fun j => j ≠ y ∧ ({y, j} : Finset (Fin n)) ∈ E)) \ C := by
            simp only [mem_sdiff, mem_filter, mem_univ, true_and]
            exact ⟨hSN' i hi, hiC⟩
          exact Finset.disjoint_left.mp hdis hi hiN
        · obtain ⟨c, hcR⟩ := build E C y
            (fun e v => y ∈ e → ∀ w ∈ e, w ≠ y → (w ∈ S → v = y) ∧ (w ∉ S → v = w))
            (by
              intro e he
              by_cases hy : y ∈ e
              · obtain ⟨w, hw, hwy⟩ := Finset.exists_mem_ne (by rw [hE e he]; norm_num) y
                have hpe := pair_eq (hE e he) hy hw (Ne.symm hwy)
                have hone : ∀ w' ∈ e, w' ≠ y → w' = w := by
                  intro w' hw' hw'y
                  rw [hpe] at hw'
                  simp only [mem_insert, mem_singleton] at hw'
                  rcases hw' with hw' | hw'
                  · exact absurd hw' hw'y
                  · exact hw'
                by_cases hwS : w ∈ S
                · refine ⟨y, hy, hyC, fun _ w' hw' hw'y => ⟨fun _ => rfl, fun h => ?_⟩⟩
                  exact absurd (hone w' hw' hw'y ▸ hwS) h
                · have hwC : w ∈ C := by
                    by_contra hwC
                    apply hwS
                    apply hsub
                    simp only [mem_sdiff, mem_filter, mem_univ, true_and]
                    refine ⟨⟨hwy, ?_⟩, hwC⟩
                    rw [← hpe]
                    exact he
                  refine ⟨w, hw, hwC, fun _ w' hw' hw'y => ⟨fun h => ?_, fun _ => ?_⟩⟩
                  · exact absurd (hone w' hw' hw'y ▸ h) hwS
                  · exact (hone w' hw' hw'y).symm
              · obtain ⟨v, hv, hvC⟩ := hC e he
                exact ⟨v, hv, hvC, fun h => absurd h hy⟩)
          refine ⟨c, true, fun _ => false, fun e he => ⟨(hcR e he).1, (hcR e he).2.1⟩,
            fun i => ?_⟩
          constructor
          · rintro (⟨-, -, -, -, -, h⟩ | ⟨-, e, he, hce, hie, hiy⟩)
            · exact absurd h Bool.false_ne_true
            · by_contra hiS
              have hye : y ∈ e := by
                rw [← hce]
                exact (hcR e he).1
              have := ((hcR e he).2.2 hye i hie hiy).2 hiS
              exact hiy (this.symm.trans hce)
          · intro hi
            right
            obtain ⟨hiy, hE'⟩ := hSN' i hi
            refine ⟨rfl, {y, i}, hE', ?_, by simp, hiy⟩
            exact ((hcR _ hE').2.2 (by simp) i (by simp) hiy).1 hi
      · apply caseAB
        intro i hi
        obtain ⟨v, hv, hvC⟩ := hC _ (hSN' i hi).2
        simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact absurd hvC hyC
        · exact hvC
    obtain ⟨c, uC, uL, hc, hT⟩ := fin
    exact ⟨c, uC, uL, hc, (iff_T hE c (fun e he => (hc e he).1) y uC uL S).mpr hT⟩
