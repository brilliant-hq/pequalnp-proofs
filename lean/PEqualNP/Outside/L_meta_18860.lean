import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18860_aux

open Classical

abbrev T := Set (Fin 26 → Bool)

noncomputable def ValidPrefix (B : Set T) (S : Finset T) (l : List T) : Prop :=
  l.Nodup ∧ l.toFinset ⊆ S ∧
  ∀ (i : ℕ) (x : T), l[i]? = some x →
    ∃ a ∈ B ∪ ↑(l.take i).toFinset, ∃ b ∈ B ∪ ↑(l.take i).toFinset,
      x = a ∩ b ∨ x = a ∪ b

noncomputable def IsClosed (B : Set T) (S : Finset T) (l : List T) : Prop :=
  ∀ a ∈ B ∪ ↑l.toFinset, ∀ b ∈ B ∪ ↑l.toFinset, ∀ c ∈ S,
    c = a ∩ b ∨ c = a ∪ b → c ∈ B ∪ ↑l.toFinset

lemma extend_aux (B : Set T) (S : Finset T) :
    ∀ (k : ℕ) (l : List T), (S \ l.toFinset).card ≤ k → ValidPrefix B S l →
      ∃ l' : List T, ValidPrefix B S l' ∧ IsClosed B S l' := by
  classical
  intro k
  induction k with
  | zero =>
    intro l hk hval
    refine ⟨l, hval, ?_⟩
    intro a _ b _ c hc _
    have hempty : S \ l.toFinset = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hk)
    have hcl : c ∈ l.toFinset := by
      by_contra hnot
      have : c ∈ S \ l.toFinset := Finset.mem_sdiff.mpr ⟨hc, hnot⟩
      rw [hempty] at this
      exact Finset.notMem_empty c this
    exact Or.inr hcl
  | succ k ih =>
    intro l hk hval
    by_cases hcl : IsClosed B S l
    · exact ⟨l, hval, hcl⟩
    · simp only [IsClosed, not_forall] at hcl
      rcases hcl with ⟨a, ha, b, hb, c, hcS, hcab, hcnot⟩
      have hcnotl : c ∉ l := by
        intro hmem
        exact hcnot (Or.inr (List.mem_toFinset.mpr hmem))
      have hcnotfs : c ∉ l.toFinset := by
        simpa [List.mem_toFinset] using hcnotl
      have hval' : ValidPrefix B S (l ++ [c]) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [List.nodup_append]
          refine ⟨hval.1, List.nodup_singleton c, ?_⟩
          intro x hx y hy hxy
          rw [List.mem_singleton] at hy
          subst hy; subst hxy
          exact hcnotl hx
        · intro x hx
          rw [List.mem_toFinset, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hval.2.1 (List.mem_toFinset.mpr hx)
          · exact hcS
        · intro i x hget
          by_cases hi : i < l.length
          · rw [List.getElem?_append_left hi] at hget
            rw [List.take_append_of_le_length (Nat.le_of_lt hi)]
            exact hval.2.2 i x hget
          · have hge : l.length ≤ i := Nat.le_of_not_lt hi
            rw [List.getElem?_append_right hge] at hget
            cases hsub : i - l.length with
            | zero =>
              have hieq : i = l.length := by omega
              rw [hsub] at hget
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
              subst hget
              rw [hieq, List.take_left]
              exact ⟨a, ha, b, hb, hcab⟩
            | succ m =>
              rw [hsub] at hget
              simp at hget
      have hcard' : (S \ (l ++ [c]).toFinset).card ≤ k := by
        have hmem : c ∈ S \ l.toFinset := Finset.mem_sdiff.mpr ⟨hcS, hcnotfs⟩
        have hsub : S \ (l ++ [c]).toFinset ⊆ (S \ l.toFinset).erase c := by
          intro x hx
          rw [Finset.mem_sdiff] at hx
          rw [Finset.mem_erase, Finset.mem_sdiff]
          refine ⟨?_, hx.1, ?_⟩
          · intro hxc
            subst hxc
            apply hx.2
            simp [List.mem_toFinset]
          · intro hxl
            apply hx.2
            simp [List.mem_toFinset] at hxl ⊢
            exact Or.inr hxl
        have hle := Finset.card_le_card hsub
        have her := Finset.card_erase_of_mem hmem
        omega
      exact ih (l ++ [c]) hcard' hval'

end PEqualNP.Outside.L_meta_18860_aux

theorem PEqualNP.Outside.L_meta_18860 :
    ∀ (x1 : Set (Set (Fin (26 : ℕ) → Bool))) (x2 : Finset (Set (Fin (26 : ℕ) → Bool))),
      (∀ x3 ∈ x2, x3 ∉ x1) →
      ∃ (x4 : List (Set (Fin (26 : ℕ) → Bool))),
        x4.Nodup ∧ x4.toFinset ⊆ x2 ∧
        (∀ (x5 : ℕ) (x6 : Set (Fin (26 : ℕ) → Bool)), x4[x5]? = Option.some x6 →
          ∃ x8 ∈ x1 ∪ ↑(List.take x5 x4).toFinset,
          ∃ x9 ∈ x1 ∪ ↑(List.take x5 x4).toFinset,
          x6 = x8 ∩ x9 ∨ x6 = x8 ∪ x9) ∧
        ∀ x5 ∈ x1 ∪ ↑x4.toFinset, ∀ x7 ∈ x1 ∪ ↑x4.toFinset, ∀ x9 ∈ x2,
          x9 = x5 ∩ x7 ∨ x9 = x5 ∪ x7 → x9 ∈ x1 ∪ ↑x4.toFinset := by
  intro x1 x2 _
  have h0 : PEqualNP.Outside.L_meta_18860_aux.ValidPrefix x1 x2 [] := by
    refine ⟨List.nodup_nil, ?_, ?_⟩
    · simp
    · intro i x h; simp at h
  obtain ⟨l, hval, hcl⟩ := PEqualNP.Outside.L_meta_18860_aux.extend_aux x1 x2 x2.card [] (by simp) h0
  exact ⟨l, hval.1, hval.2.1, hval.2.2, hcl⟩
