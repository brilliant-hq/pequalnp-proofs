import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_18660 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)),   have x3 : Finset (Fin x1) → Prop := fun (x3 : Finset (Fin x1)) => ∀ (x4 x5 : Fin x1), x2.Adj x4 x5 → x4 ∈ x3 ∨ x5 ∈ x3;   ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → ∃ (x6 : Finset (Fin x1)), x3 x6 ∧ (∀ (x7 : Finset (Fin x1)), x3 x7 → x6.card ≤ x7.card) ∧ (∀ x7 ∈ x6, ∃ x9 ∉ x6, x2.Adj x7 x9) ∧ (∃ x7 ∈ x6, ∃ x8 ∈ x6, x2.Adj x7 x8) ∧ ∀ x7 ∈ x6, ∀ x9 ∈ x6, x2.Adj x7 x9 → (x2.edgeSet \ (x2.incidenceSet x7 ∪ x2.incidenceSet x9)).ncard + ((x6.erase x7).erase x9).card + (7 : ℕ) = x2.edgeSet.ncard + x6.card := by
  classical
  intro n G
  dsimp only
  intro hcolor hdegree
  let covers : Finset (Fin n) → Prop := fun S => ∀ a b, G.Adj a b → a ∈ S ∨ b ∈ S
  have hex : ({S | covers S} : Set (Finset (Fin n))).Nonempty :=
    ⟨Finset.univ, fun _ _ _ => Or.inl (Finset.mem_univ _)⟩
  obtain ⟨S, hcov, hmin⟩ := Set.exists_min_image _ Finset.card (Set.toFinite _) hex
  change covers S at hcov
  change ∀ T, covers T → S.card ≤ T.card at hmin
  refine ⟨S, hcov, hmin, ?_, ?_, ?_⟩
  · intro a ha
    by_contra! h
    have hn : ∀ b, G.Adj a b → b ∈ S := by
      intro b hab
      by_contra hbs
      exact h b hbs hab
    have hremove : covers (S.erase a) := by
      intro i j hij
      by_cases hi : i = a
      · subst i
        exact Or.inr (Finset.mem_erase.mpr ⟨hij.ne.symm, hn j hij⟩)
      by_cases hj : j = a
      · subst j
        exact Or.inl (Finset.mem_erase.mpr ⟨hi, hn i hij.symm⟩)
      exact (hcov i j hij).imp (fun h => Finset.mem_erase.mpr ⟨hi,h⟩) (fun h => Finset.mem_erase.mpr ⟨hj,h⟩)
    have hsmall := hmin _ hremove
    have hone := Finset.card_erase_add_one ha
    omega
  · by_contra! h
    apply hcolor
    refine ⟨SimpleGraph.Coloring.mk (fun i => if i ∈ S then (0 : Fin 2) else 1) ?_⟩
    intro i j hij
    by_cases hi : i ∈ S
    · have hj : j ∉ S := fun hj => h i hi j hj hij
      simp [hi,hj]
    · have hj : j ∈ S := (hcov i j hij).resolve_left hi
      simp [hi,hj]
  · intro a ha b hb hab
    have da := hdegree a ⟨b,hab⟩
    have db := hdegree b ⟨a,hab.symm⟩
    rw [G.ncard_neighborSet] at da db
    have h := Set.ncard_union_add_ncard_inter (G.incidenceSet a) (G.incidenceSet b)
    rw [G.incidenceSet_inter_incidenceSet_of_adj hab, Set.ncard_singleton,
      G.ncard_incidenceSet, G.ncard_incidenceSet, da, db] at h
    have hu := Set.ncard_sdiff_add_ncard_of_subset (Set.union_subset (G.incidenceSet_subset a) (G.incidenceSet_subset b))
    have h1 := Finset.card_erase_add_one ha
    have h2 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hab.ne.symm,hb⟩ : b ∈ S.erase a)
    omega
