import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_18956_2
    (hChainToCircuit :
      ∀ (L : List (Set (Fin (26 : ℕ) → Bool))),
        have B : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (i : Fin (26 : ℕ)) => {x : Fin (26 : ℕ) → Bool | x i = Bool.true};
        have T : Set (Fin (26 : ℕ) → Bool) := {x : Fin (26 : ℕ) → Bool | ∃ (p l : Fin (13 : ℕ)), (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true};
        L.length ≤ (62 : ℕ) →
        L.Nodup →
        (∀ s ∈ L, s ∉ B) →
        (∀ (i : ℕ) (s : Set (Fin (26 : ℕ) → Bool)), L[i]? = Option.some s →
          ∃ a, (a ∈ B ∨ a ∈ L.take i) ∧ ∃ b, (b ∈ B ∨ b ∈ L.take i) ∧ (s = a ∩ b ∨ s = a ∪ b)) →
        T ∈ L →
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.Monotone2 C ∧
          C.size ≤ (62 : ℕ) ∧
          ∀ (x : Fin (26 : ℕ) → Bool), C.eval (List.ofFn x) = Bool.true ↔ x ∈ T)
    (hLowerBound63 :
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 C →
        (∀ (x : Fin (26 : ℕ) → Bool),
          C.eval (List.ofFn x) = Bool.true ↔
            ∃ (p l : Fin (13 : ℕ)), (↑p + ↑l) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧
              x (Fin.castAdd (13 : ℕ) p) = Bool.true ∧ x (Fin.natAdd (13 : ℕ) l) = Bool.true) →
        (63 : ℕ) ≤ C.size) :
    (have x1 : Set (Set (Fin (26 : ℕ) → Bool)) := {∅, Set.univ} ∪ Set.range fun (x1 : Fin (26 : ℕ)) => {x2 : Fin (26 : ℕ) → Bool | x2 x1 = Bool.true}; have x2 : Set (Fin (26 : ℕ) → Bool) := {x2 : Fin (26 : ℕ) → Bool | ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)), (↑x3 + ↑x4) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)] ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true}; ∀ (x3 : List (Set (Fin (26 : ℕ) → Bool))), x3.length ≤ (62 : ℕ) → x3.Nodup → (∀ x6 ∈ x3, x6 ∉ x1) → (∀ (x7 : ℕ) (x8 : Set (Fin (26 : ℕ) → Bool)), x3[x7]? = Option.some x8 → ∃ (x10 : Set (Fin (26 : ℕ) → Bool)), (x10 ∈ x1 ∨ x10 ∈ List.take x7 x3) ∧ ∃ (x11 : Set (Fin (26 : ℕ) → Bool)), (x11 ∈ x1 ∨ x11 ∈ List.take x7 x3) ∧ (x8 = x10 ∩ x11 ∨ x8 = x10 ∪ x11)) → x2 ∉ x3) := by
  intro x1 x2 x3 hlen hnd hnotB hstep hmem
  obtain ⟨C, hmono, hsz, hev⟩ := hChainToCircuit x3 hlen hnd hnotB hstep hmem
  have hge := hLowerBound63 C hmono hev
  omega

