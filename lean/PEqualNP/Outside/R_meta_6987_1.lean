import PEqualNP.Defs

open PEqualNP.GenericRejection PEqualNP.HeptadCover

set_option maxHeartbeats 2000000 in
theorem PEqualNP.Outside.R_meta_6987_1
    (orbits : ∀ X : Finset (Fin 13), (∃ Y, (X,Y) ∈ genericInputs singerLines3 3) →
      ∃ (s : Fin 16) (a : Fin 13) (b : Fin 3), ∀ p : Fin 13, p ∈ X ↔
        (([4544,2464,6464,5440,4416,3332,5264,3204,3076,2336,6400,5376,5136,6164,6148,6160] : List ℕ).getD s.val 0).testBit
          (((p-a) * ([1,3,9] : List (Fin 13)).getD b.val 0).val) = true)
    (obstruction : ∀ (L : List (Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4)))
      (T : Finset (Finset (Fin 13 × Fin 4) × Finset (Fin 13 × Fin 4))),
      L.length + T.card ≤ 50 →
      (∀ p ∈ L, p.1 ∪ p.2 ≠ Finset.univ ∧ ¬p.1 ⊆ p.2 ∧ ¬p.2 ⊆ p.1) →
      (∀ p ∈ T, p.1 ∪ p.2 = Finset.univ) →
      ∃ X : Finset (Fin 13), (∃ Y, (X,Y) ∈ genericInputs singerLines3 3) ∧
        let D := L.foldl (fun F p S => F S ∨ S ⊆ p.1 ∪ p.2 ∧ F p.1 ∧ F p.2)
          (fun S => S = ∅ ∨ (∃ p : Fin 13, p ∉ X ∧ ∀ e ∈ S, e.1 + ([0,1,3,9] : List (Fin 13)).getD e.2.val 0 = p) ∨
            ∃ l : Fin 13, (∃ p ∈ X, p ∈ singerLines3 l) ∧ ∀ e ∈ S, e.1 = l)
        ∀ p ∈ T, ¬ (D p.1 ∧ D p.2)) :
    (∀ (x1 : List (Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ)))),   x1.length ≤ (50 : ℕ) →     ∃ (x3 : Fin (16 : ℕ)) (x4 : Fin (13 : ℕ)) (x5 : Fin (3 : ℕ)),       have x6 : Fin (13 : ℕ) × Fin (4 : ℕ) → Fin (26 : ℕ) → Bool := fun (x6 : Fin (13 : ℕ) × Fin (4 : ℕ)) (x7 : Fin (26 : ℕ)) => Decidable.decide (x7 = Fin.castAdd (13 : ℕ) (x6.1 + [(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x6.2 (0 : Fin (13 : ℕ))) ∨ x7 = Fin.natAdd (13 : ℕ) x6.1);       let x7 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x7 x8 : Fin (13 : ℕ)) => x7 = x8 ∨ x7 = x8 + (1 : Fin (13 : ℕ)) ∨ x7 = x8 + (3 : Fin (13 : ℕ)) ∨ x7 = x8 + (9 : Fin (13 : ℕ));       have x8 : Finset (Fin (13 : ℕ)) := {x8 : Fin (13 : ℕ) | ([(4544 : ℕ), (2464 : ℕ), (6464 : ℕ), (5440 : ℕ), (4416 : ℕ), (3332 : ℕ), (5264 : ℕ), (3204 : ℕ), (3076 : ℕ), (2336 : ℕ), (6400 : ℕ), (5376 : ℕ), (5136 : ℕ), (6164 : ℕ), (6148 : ℕ), (6160 : ℕ)].getD ↑x3 (0 : ℕ)).testBit ↑((x8 - x4) * [(1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))].getD ↑x5 (0 : Fin (13 : ℕ))) = Bool.true};       have x9 : Fin (26 : ℕ) → Bool := fun (x9 : Fin (26 : ℕ)) => Decidable.decide ((∃ x10 ∈ x8, x9 = Fin.castAdd (13 : ℕ) x10) ∨ ∃ (x10 : Fin (13 : ℕ)), x9 = Fin.natAdd (13 : ℕ) x10 ∧ ∀ x11 ∈ x8, ¬x7 x11 x10);       ¬List.foldl (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) → Prop) (x11 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ)) × Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) (x12 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 x12 ∨ x12 ⊆ x11.1 ∪ x11.2 ∧ x10 x11.1 ∧ x10 x11.2) (fun (x10 : Finset (Fin (13 : ℕ) × Fin (4 : ℕ))) => x10 = ∅ ∨ ∃ (x11 : Fin (26 : ℕ)), x9 x11 = Bool.false ∧ ∀ x12 ∈ x10, x6 x12 x11 = Bool.true) x1 Finset.univ) := by
  classical
  intro G hG
  let E := Fin 13 × Fin 4
  let ordinary (p : Finset E × Finset E) : Prop :=
    p.1 ∪ p.2 ≠ Finset.univ ∧ ¬ p.1 ⊆ p.2 ∧ ¬ p.2 ⊆ p.1
  let L := G.filter (fun p => decide (ordinary p))
  let outs := G.filter (fun p => decide (p.1 ∪ p.2 = Finset.univ))
  let T := outs.toFinset
  have hin (p) (hp : p ∈ G) (ht : p.1 ∪ p.2 = Finset.univ) : p ∈ T := by
    simpa [T, outs, ht] using hp
  have len : L.length + T.card ≤ 50 := by
    have bound (A : List (Finset E × Finset E)) :
        (A.filter (fun p => decide (ordinary p))).length +
        (A.filter (fun p => decide (p.1 ∪ p.2 = Finset.univ))).length ≤ A.length := by
      induction A with
      | nil => simp
      | cons p ps ih =>
        by_cases ho : ordinary p
        · have hr := ho.1
          simpa [ho, hr, Nat.add_right_comm, Nat.add_comm, Nat.add_left_comm] using ih
        · by_cases ht : p.1 ∪ p.2 = Finset.univ <;> simp [ho, ht] <;> omega
    have tc := List.toFinset_card_le outs
    dsimp [L, T, outs] at *
    exact le_trans (Nat.add_le_add_left tc _) ((bound G).trans hG)
  obtain ⟨X, hX, blocked⟩ := obstruction L T len
    (by simp [L, ordinary])
    (by simp [T, outs])
  obtain ⟨s, a, b, horb⟩ := orbits X hX
  refine ⟨s, a, b, ?_⟩
  let pt (e : E) := e.1 + ([0,1,3,9] : List (Fin 13)).getD e.2.val 0
  let neg (v : Fin 26) := decide ((∃ p ∈ X, v = Fin.castAdd 13 p) ∨
    ∃ l : Fin 13, v = Fin.natAdd 13 l ∧ ∀ p ∈ X, ¬ (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9))
  let Q (S : Finset E) : Prop := S = ∅ ∨ (∃ p : Fin 13, p ∉ X ∧ ∀ e ∈ S, pt e = p) ∨
    ∃ l : Fin 13, (∃ p ∈ X, p ∈ singerLines3 l) ∧ ∀ e ∈ S, e.1 = l
  let Q0 (S : Finset E) : Prop := S = ∅ ∨ ∃ v : Fin 26, neg v = false ∧ ∀ e ∈ S,
    decide (v = Fin.castAdd 13 (pt e) ∨ v = Fin.natAdd 13 e.1) = true
  let st (D : Finset E → Prop) (p : Finset E × Finset E) (S : Finset E) :=
    D S ∨ S ⊆ p.1 ∪ p.2 ∧ D p.1 ∧ D p.2
  have inc : ∀ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) → p ∈ singerLines3 l := by
    decide +kernel
  have disj (p l : Fin 13) : Fin.castAdd 13 p ≠ Fin.natAdd 13 l := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have init (S) (h : Q0 S) : Q S := by
    rcases h with he | ⟨v, hv, hall⟩
    · exact Or.inl he
    induction v using Fin.addCases (m := 13) (n := 13) with
    | left p =>
      refine Or.inr (Or.inl ⟨p, ?_, ?_⟩)
      · intro hp
        have : neg (Fin.castAdd 13 p) = true := decide_eq_true (Or.inl ⟨p,hp,rfl⟩)
        simp_all
      · intro e he
        have hh := (of_decide_eq_true (hall e he)).resolve_right (disj p e.1)
        exact Fin.ext (show (pt e).val = p.val from (congrArg Fin.val hh).symm)
    | right l =>
      refine Or.inr (Or.inr ⟨l, ?_, ?_⟩)
      · by_contra! hn
        have : neg (Fin.natAdd 13 l) = true := decide_eq_true
          (Or.inr ⟨l,rfl,fun p hp hi => hn p hp (inc p l hi)⟩)
        simp_all
      · intro e he
        have hh := (of_decide_eq_true (hall e he)).resolve_left (Ne.symm (disj (pt e) l))
        apply Fin.ext
        have hvv := congrArg Fin.val hh
        simp only [Fin.val_natAdd] at hvv
        omega
  let D := L.foldl st Q
  change ∀ p ∈ T, ¬ (D p.1 ∧ D p.2) at blocked
  have down (A : List (Finset E × Finset E)) : ∀ {U V}, U ⊆ V → A.foldl st Q V → A.foldl st Q U := by
    induction A using List.reverseRecOn with
    | nil =>
      intro U V h hV
      rcases hV with rfl | ⟨p,hp,hh⟩ | ⟨l,hl,hh⟩
      · exact Or.inl (Finset.subset_empty.mp h)
      · exact Or.inr (Or.inl ⟨p,hp,fun e he => hh e (h he)⟩)
      · exact Or.inr (Or.inr ⟨l,hl,fun e he => hh e (h he)⟩)
    | append_singleton A p ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      intro U V h hV
      rcases hV with hh | ⟨hs,hh⟩
      · exact Or.inl (ih h hh)
      · exact Or.inr ⟨h.trans hs,hh⟩
  have keeps (A B : List (Finset E × Finset E)) (U) (h : A.foldl st Q U) :
      (A++B).foldl st Q U := by
    induction B using List.reverseRecOn with
    | nil => simpa using h
    | append_singleton B p ih =>
      rw [← List.append_assoc, List.foldl_append]
      exact Or.inl ih
  have norm (A B : List (Finset E × Finset E)) (eqG : G = A ++ B) :
      ∀ U, A.foldl st Q0 U → (A.filter (fun p => decide (ordinary p))).foldl st Q U := by
    induction A using List.reverseRecOn generalizing B with
    | nil => exact init
    | append_singleton A p ih =>
      have eq' : G = A ++ p :: B := by simpa [List.append_assoc] using eqG
      have step := ih (p :: B) eq'
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.filter_append]
      intro U hu
      by_cases ho : ordinary p
      · simp [ho]
        rcases hu with h | ⟨hs,h1,h2⟩
        · exact Or.inl (step U h)
        · exact Or.inr ⟨hs,step _ h1,step _ h2⟩
      · simp [ho]
        rcases hu with h | ⟨hs,h1,h2⟩
        · exact step U h
        have ha := step _ h1
        have hb := step _ h2
        by_cases ht : p.1 ∪ p.2 = Finset.univ
        · have lift (V) (h : (A.filter (fun p => decide (ordinary p))).foldl st Q V) : D V := by
            dsimp [D,L]
            rw [eq', List.filter_append]
            apply keeps _ _ _ h
          exact False.elim (blocked p (hin p (by simp [eq']) ht) ⟨lift _ ha,lift _ hb⟩)
        · by_cases hsub : p.1 ⊆ p.2
          · exact down _ (hs.trans (Finset.union_subset hsub (Finset.Subset.refl _))) hb
          · have hrev : p.2 ⊆ p.1 := by by_contra hn; exact ho ⟨ht,hsub,hn⟩
            exact down _ (hs.trans (Finset.union_subset (Finset.Subset.refl _) hrev)) ha
  have noInit : ¬ Q Finset.univ := by
    rintro (he | ⟨p,_,hp⟩ | ⟨l,_,hl⟩)
    · exact Finset.univ_nonempty.ne_empty he
    · have h0 := hp (0,0) (by simp)
      have h1 := hp (1,0) (by simp)
      have bad : pt (0,0) ≠ pt (1,0) := by decide
      exact bad (h0.trans h1.symm)
    · have h0 := hl (0,0) (by simp)
      have h1 := hl (1,0) (by simp)
      exact (by decide : (0 : Fin 13) ≠ 1) (h0.trans h1.symm)
  have noFull (A : List (Finset E × Finset E)) (hA : ∀ p ∈ A, ordinary p) :
      ¬ A.foldl st Q Finset.univ := by
    induction A using List.reverseRecOn with
    | nil => exact noInit
    | append_singleton A p ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      rintro (h | ⟨hs,_,_⟩)
      · exact ih (fun q hq => hA q (by simp [hq])) h
      · exact (hA p (by simp)).1 (Finset.univ_subset_iff.mp hs)
  dsimp only
  have hx : X = Finset.univ.filter (fun p : Fin 13 =>
      (([4544,2464,6464,5440,4416,3332,5264,3204,3076,2336,6400,5376,5136,6164,6148,6160] : List ℕ).getD s.val 0).testBit
        (((p - a) * ([1,3,9] : List (Fin 13)).getD b.val 0).val) = true) := by
    ext p
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using horb p
  rw [← hx]
  change ¬ G.foldl st Q0 Finset.univ
  exact fun h => noFull L (by simp [L]) (norm G [] (by simp) _ h)
