import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18860

open Classical

private noncomputable def available {α : Type} (base : Set (Set α)) (xs : List (Set α)) : Set (Set α) :=
  base ∪ ↑xs.toFinset

private def generated {α : Type} (current : Set (Set α)) (z : Set α) : Prop :=
  ∃ a ∈ current, ∃ b ∈ current, z = a ∩ b ∨ z = a ∪ b

private def ordered {α : Type} (base : Set (Set α)) (xs : List (Set α)) : Prop :=
  ∀ j z, xs[j]? = some z → generated (available base (xs.take j)) z

private theorem ordered_snoc {α : Type} {base : Set (Set α)} {xs : List (Set α)} {z : Set α}
    (hxs : ordered base xs) (hz : generated (available base xs) z) :
    ordered base (xs ++ [z]) := by
  intro j w hw
  by_cases hj : j < xs.length
  · rw [List.getElem?_append_left hj] at hw
    have ht : (xs ++ [z]).take j = xs.take j := List.take_append_of_le_length (Nat.le_of_lt hj)
    rw [ht]
    exact hxs j w hw
  · obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hw
    have he : j = xs.length := by
      simp only [List.length_append, List.length_singleton] at hlt
      omega
    subst j
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at hw
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hw
    have ht : (xs ++ [z]).take xs.length = xs := by simp
    rw [← hw, ht]
    exact hz

private def closedInside {α : Type} (pool : Finset (Set α)) (current : Set (Set α)) : Prop :=
  ∀ z ∈ pool, generated current z → z ∈ current

private theorem finish {α : Type} (base : Set (Set α)) (pool : Finset (Set α)) :
    ∀ (k : ℕ) (xs : List (Set α)), (pool \ xs.toFinset).card = k →
      xs.Nodup → xs.toFinset ⊆ pool → ordered base xs →
      ∃ ys : List (Set α), ys.Nodup ∧ ys.toFinset ⊆ pool ∧
        ordered base ys ∧ closedInside pool (available base ys) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro xs hk hn hsub hord
    by_cases hc : closedInside pool (available base xs)
    · exact ⟨xs, hn, hsub, hord, hc⟩
    · unfold closedInside at hc
      push Not at hc
      obtain ⟨z, hp, hgen, hout⟩ := hc
      have hz : z ∉ xs.toFinset := fun hz => hout (Or.inr hz)
      have hzList : z ∉ xs := fun hz' => hz (List.mem_toFinset.mpr hz')
      let next := xs ++ [z]
      have hn' : next.Nodup := by
        refine List.nodup_append.mpr ⟨hn, by simp, ?_⟩
        intro a ha b hb he
        simp only [List.mem_singleton] at hb
        exact hzList (he.trans hb ▸ ha)
      have hsub' : next.toFinset ⊆ pool := by
        intro w hw
        have hmem : w ∈ xs ∨ w = z := by simpa [next] using List.mem_toFinset.mp hw
        rcases hmem with hm | rfl
        · exact hsub (List.mem_toFinset.mpr hm)
        · exact hp
      have hremove : pool \ next.toFinset = (pool \ xs.toFinset).erase z := by
        ext w
        simp [next]
        tauto
      have hlt : (pool \ next.toFinset).card < k := by
        rw [hremove, ← hk]
        exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hp, hz⟩)
      exact ih _ hlt next rfl hn' hsub' (ordered_snoc hord hgen)

theorem result {α : Type} (base : Set (Set α)) (pool : Finset (Set α)) :
    ∃ xs : List (Set α), xs.Nodup ∧ xs.toFinset ⊆ pool ∧
      ordered base xs ∧ closedInside pool (available base xs) := by
  exact finish base pool _ [] rfl (by simp) (by simp) (by simp [ordered])

end PEqualNP.Outside.L_meta_18860

open Classical in
theorem PEqualNP.Outside.L_meta_18860 :
    ∀ (x1 : Set (Set (Fin (26 : ℕ) → Bool))) (x2 : Finset (Set (Fin (26 : ℕ) → Bool))),
      (∀ x3 ∈ x2, x3 ∉ x1) → ∃ (x4 : List (Set (Fin (26 : ℕ) → Bool))),
        x4.Nodup ∧ x4.toFinset ⊆ x2 ∧
          (∀ (x5 : ℕ) (x6 : Set (Fin (26 : ℕ) → Bool)), x4[x5]? = Option.some x6 →
            ∃ x8 ∈ x1 ∪ ↑(List.take x5 x4).toFinset, ∃ x9 ∈ x1 ∪ ↑(List.take x5 x4).toFinset,
              x6 = x8 ∩ x9 ∨ x6 = x8 ∪ x9) ∧
          ∀ x5 ∈ x1 ∪ ↑x4.toFinset, ∀ x7 ∈ x1 ∪ ↑x4.toFinset,
            ∀ x9 ∈ x2, x9 = x5 ∩ x7 ∨ x9 = x5 ∪ x7 → x9 ∈ x1 ∪ ↑x4.toFinset := by
  intro base pool _
  obtain ⟨xs, hn, hsub, hord, hclosed⟩ := L_meta_18860.result base pool
  refine ⟨xs, hn, hsub, hord, ?_⟩
  intro a ha b hb z hz hab
  exact hclosed z hz ⟨a, ha, b, hb, hab⟩
