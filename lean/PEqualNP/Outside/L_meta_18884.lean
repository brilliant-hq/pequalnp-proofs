import PEqualNP.Defs

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_meta_18884 : ∀ (x1 : Finset (Fin (26 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (SimpleGraph.fromRel fun (x2 x3 : Fin (26 : ℕ)) => ↑x2 < (13 : ℕ) ∧ (13 : ℕ) ≤ ↑x3 ∧ (↑x2 + ↑x3) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) x1 → (13 : ℕ) ≤ x1.card := by
  classical
  intro S covers
  let a : Fin 13 → Fin 26 := Fin.castAdd 13
  let b : Fin 13 → Fin 26 := fun i => Fin.natAdd 13 (-i)
  have edge : ∀ i, (SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧ (u.val+v.val)%13 ∈ ([0,1,3,9] : List ℕ))).Adj (a i) (b i) := by decide +kernel
  have ai : Function.Injective a := by
    intro i j eq
    apply Fin.ext
    simpa [a] using congrArg (fun z : Fin 26 => z.val) eq
  have bi : Function.Injective b := by
    intro i j eq
    have val := congrArg Fin.val eq
    have neg : -i = -j := by
      apply Fin.ext
      dsimp [b] at val
      omega
    exact neg_injective neg
  have apart : ∀ i j, a i ≠ b j := by
    intro i j eq
    have val := congrArg Fin.val eq
    have hi := i.isLt
    dsimp [a,b] at val
    omega
  let f : Fin 13 → Fin 26 := fun i => if a i ∈ S then a i else b i
  have member : ∀ i, f i ∈ S := by
    intro i
    dsimp [f]
    split_ifs with h
    · exact h
    · exact (covers (a i) (b i) (edge i)).resolve_left h
  have inj : Function.Injective f := by
    intro i j eq
    by_cases hi : a i ∈ S <;> by_cases hj : a j ∈ S
    · simp only [f,hi,hj,ite_true] at eq
      exact ai eq
    · simp only [f,hi,hj,ite_true,ite_false] at eq
      exact False.elim (apart i j eq)
    · simp only [f,hi,hj,ite_true,ite_false] at eq
      exact False.elim (apart j i eq.symm)
    · simp only [f,hi,hj,ite_false] at eq
      exact bi eq
  have subset : Finset.univ.image f ⊆ S := by
    intro y hy
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hy
    exact member i
  have count := Finset.card_le_card subset
  rwa [Finset.card_image_of_injective _ inj, Finset.card_univ, Fintype.card_fin] at count
