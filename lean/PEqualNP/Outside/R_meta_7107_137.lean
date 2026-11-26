import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_7107_137 :
  (let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)];
    ∀ (fs : List ((Fin 10 → Bool) → Bool)) (op : Fin fs.length → Bool),
    (∀ i : Fin fs.length, let A := ((fun (_ : Fin 10 → Bool) => false) :: (fun (_ : Fin 10 → Bool) => true) :: List.ofFn (fun (j : Fin 10) (x : Fin 10 → Bool) => x j)) ++ [fun (x : Fin 10 → Bool) => x 0 && x 1] ++ fs.take i.val;
      fs.get i ∉ A ∧ ∃ u ∈ A, ∃ v ∈ A,
        fs.get i = fun x => if op i then u x && v x else u x || v x) →
    (∀ f ∈ fs, ∀ u v : Fin 10, u ≠ v →
      (¬(E.any (fun e => decide ((u,v) = e ∨ (v,u) = e))) = true →
        f ≠ fun x => x u && x v) ∧ f ≠ fun x => x u || x v) →
    (fun x => E.any (fun e => x e.1 && x e.2)) ∈ fs →
    14 ≤ (Finset.univ.filter (fun i => op i = false)).card) →
  (let E : List (Fin 10 × Fin 10) := [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)];
    ∀ (fs : List ((Fin 10 → Bool) → Bool)) (op : Fin fs.length → Bool),
    (∀ i : Fin fs.length, let A := ((fun (_ : Fin 10 → Bool) => false) :: (fun (_ : Fin 10 → Bool) => true) :: List.ofFn (fun (j : Fin 10) (x : Fin 10 → Bool) => x j)) ++ [fun (x : Fin 10 → Bool) => x 0 && x 1] ++ fs.take i.val;
      fs.get i ∉ A ∧ ∃ u ∈ A, ∃ v ∈ A,
        fs.get i = fun x => if op i then u x && v x else u x || v x) →
    (∀ f ∈ fs, ∀ u v : Fin 10, u ≠ v →
      (¬(E.any (fun e => decide ((u,v) = e ∨ (v,u) = e))) = true →
        f ≠ fun x => x u && x v) ∧ f ≠ fun x => x u || x v) →
    (fun x => E.any (fun e => x e.1 && x e.2)) ∈ fs →
    5 ≤ (Finset.univ.filter (fun i => op i = true)).card) →
  (have x1 : List (Fin (10 : ℕ) × Fin (10 : ℕ)) := [((0 : Fin (10 : ℕ)), (1 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (2 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (3 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (4 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (0 : Fin (10 : ℕ))), ((0 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ))), ((1 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((2 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((3 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((4 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((5 : Fin (10 : ℕ)), (7 : Fin (10 : ℕ))), ((7 : Fin (10 : ℕ)), (9 : Fin (10 : ℕ))), ((9 : Fin (10 : ℕ)), (6 : Fin (10 : ℕ))), ((6 : Fin (10 : ℕ)), (8 : Fin (10 : ℕ))), ((8 : Fin (10 : ℕ)), (5 : Fin (10 : ℕ)))]; ∀ (x2 : List ((Fin (10 : ℕ) → Bool) → Bool)),   x2.length ≤ (18 : ℕ) →     (∀ (x4 : Fin x2.length),         have x5 : List ((Fin (10 : ℕ) → Bool) → Bool) := ((fun (x5 : Fin (10 : ℕ) → Bool) => Bool.false) :: (fun (x5 : Fin (10 : ℕ) → Bool) => Bool.true) :: List.ofFn fun (x5 : Fin (10 : ℕ)) (x6 : Fin (10 : ℕ) → Bool) => x6 x5) ++ [fun (x5 : Fin (10 : ℕ) → Bool) => x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ))] ++ List.take (↑x4) x2;         x2.get x4 ∉ x5 ∧ ∃ x6 ∈ x5, ∃ x7 ∈ x5, (x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 && x7 x8) ∨ x2.get x4 = fun (x8 : Fin (10 : ℕ) → Bool) => x6 x8 || x7 x8) →       (∀ x5 ∈ x2, ∀ (x7 x8 : Fin (10 : ℕ)), x7 ≠ x8 → (¬(x1.any fun (x10 : Fin (10 : ℕ) × Fin (10 : ℕ)) => Decidable.decide ((x7, x8) = x10 ∨ (x8, x7) = x10)) = Bool.true → x5 ≠ fun (x11 : Fin (10 : ℕ) → Bool) => x11 x7 && x11 x8) ∧ x5 ≠ fun (x10 : Fin (10 : ℕ) → Bool) => x10 x7 || x10 x8) → (fun (x6 : Fin (10 : ℕ) → Bool) => x1.any fun (x7 : Fin (10 : ℕ) × Fin (10 : ℕ)) => x6 x7.1 && x6 x7.2) ∉ x2) := by
  intro hOr hAnd
  dsimp only at hOr hAnd ⊢
  intro fs hlen hbuild hforbid hmem
  have hc : ∀ i : Fin fs.length, ∃ b : Bool,
      let A := ((fun (_ : Fin 10 → Bool) => false) :: (fun (_ : Fin 10 → Bool) => true) :: List.ofFn (fun (j : Fin 10) (x : Fin 10 → Bool) => x j)) ++ [fun (x : Fin 10 → Bool) => x 0 && x 1] ++ fs.take i.val;
      fs.get i ∉ A ∧ ∃ u ∈ A, ∃ v ∈ A,
        fs.get i = fun x => if b then u x && v x else u x || v x := by
    intro i
    obtain ⟨hn, u, hu, v, hv, he⟩ := hbuild i
    rcases he with he | he
    · exact ⟨true, hn, u, hu, v, hv, he⟩
    · exact ⟨false, hn, u, hu, v, hv, he⟩
  let op : Fin fs.length → Bool := fun i => Classical.choose (hc i)
  have hb : ∀ i : Fin fs.length, let A := ((fun (_ : Fin 10 → Bool) => false) :: (fun (_ : Fin 10 → Bool) => true) :: List.ofFn (fun (j : Fin 10) (x : Fin 10 → Bool) => x j)) ++ [fun (x : Fin 10 → Bool) => x 0 && x 1] ++ fs.take i.val;
      fs.get i ∉ A ∧ ∃ u ∈ A, ∃ v ∈ A,
        fs.get i = fun x => if op i then u x && v x else u x || v x := by
    intro i
    exact Classical.choose_spec (hc i)
  have h₁ := hOr fs op hb hforbid hmem
  have h₂ := hAnd fs op hb hforbid hmem
  have hcount := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin fs.length))) (p := fun i => op i = true)
  simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hcount
  omega
