import Mathlib

namespace PEqualNP.Outside.L_lib_486

def mismatch {n q : Nat} (x y : Fin n → Fin q) := Finset.univ.filter (fun i => x i ≠ y i)

theorem fiber {n q : Nat} (x : Fin n → Fin q) (s : Finset (Fin n)) :
    (Finset.univ.filter (fun y : Fin n → Fin q => mismatch x y = s)).card = (q-1)^s.card := by
  classical
  let choices (i : Fin n) : Finset (Fin q) := if i ∈ s then Finset.univ.erase (x i) else {x i}
  have sides : Finset.univ.filter (fun y : Fin n → Fin q => mismatch x y = s) = Fintype.piFinset choices := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro eq i
      have hi : i ∈ mismatch x y ↔ i ∈ s := eq ▸ Iff.rfl
      simp only [mismatch,Finset.mem_filter,Finset.mem_univ,true_and] at hi
      by_cases h : i ∈ s
      · simpa [choices,h,ne_comm] using (hi.mpr h)
      · have equal : x i = y i := by by_contra ne; exact h (hi.mp ne)
        simpa [choices,h] using equal.symm
    · intro all
      ext i
      have this := all i
      by_cases h : i ∈ s <;> simp_all [choices,mismatch,ne_comm]
  rw [sides,Fintype.card_piFinset]
  have cards (i : Fin n) : (choices i).card = if i ∈ s then q-1 else 1 := by
    by_cases hi : i ∈ s <;> simp [choices,hi,Finset.card_erase_of_mem]
  simp_rw [cards]
  rw [← Finset.prod_filter]
  simp

theorem volume {n q : Nat} (x : Fin n → Fin q) (r : Nat) :
    (Finset.univ.filter (fun y : Fin n → Fin q => (mismatch x y).card ≤ r)).card =
    ((List.range (r+1)).map (fun j => Nat.choose n j * (q-1)^j)).sum := by
  classical
  have shell (j : Nat) :
      (Finset.univ.filter (fun y : Fin n → Fin q => (mismatch x y).card = j)).card =
      Nat.choose n j * (q-1)^j := by
    have sums := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n → Fin q))
      ((Finset.univ : Finset (Fin n)).powersetCard j) (mismatch x)
    simp only [Finset.mem_powersetCard,Finset.subset_univ,true_and] at sums
    rw [← sums]
    apply (Finset.sum_const_nat (m := (q-1)^j) (fun s hs => ?_)).trans
    · simp
    · rw [fiber,(Finset.mem_powersetCard.mp hs).2]
  have sums := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (Fin n → Fin q))
    (Finset.range (r+1)) (fun y => (mismatch x y).card)
  simp only [Finset.mem_range,Nat.lt_succ_iff] at sums
  rw [← sums]
  simp_rw [shell]
  have seq (f : ℕ → ℕ) (k : ℕ) : (∑ j ∈ Finset.range k, f j) = ((List.range k).map f).sum := by
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp
  exact seq _ _

end PEqualNP.Outside.L_lib_486

open PEqualNP.Outside

theorem PEqualNP.Outside.L_lib_486 :
  ∀ (q n r t : Nat), 2 ≤ q → r ≤ n →
  let Word := Fin n → Fin q
  let dist := fun (x y : Word) =>
    ((Finset.univ : Finset (Fin n)).filter (fun i => x i ≠ y i)).card
  let A := q^n
  let V := ((List.range (r+1)).map (fun j => Nat.choose n j * (q-1)^j)).sum
  ∃ C : Finset Word, (∀ point : Word, ∃ c ∈ C, dist point c ≤ r) ∧
    C.card * A^t ≤ t*A^t + A*(A-V)^t := by
  classical
  intro q n r t hq _
  dsimp only
  let Word := Fin n → Fin q
  let Centers := Fin t → Word
  have : Nonempty (Fin q) := ⟨⟨0,by omega⟩⟩
  let V := ((List.range (r+1)).map (fun j => Nat.choose n j * (q-1)^j)).sum
  let ball (x : Word) : Finset Word := Finset.univ.filter (fun y => (L_lib_486.mismatch x y).card ≤ r)
  let missed (z : Centers) := Finset.univ.filter (fun x : Word => ∀ j, z j ∉ ball x)
  have hcardW : Fintype.card Word = q^n := by simp [Word]
  have hcardZ : Fintype.card Centers = (q^n)^t := by simp [Centers,hcardW]
  have avoid (x : Word) : (Finset.univ.filter (fun z : Centers => ∀ j, z j ∉ ball x)).card = (q^n-V)^t := by
    have same : Finset.univ.filter (fun z : Centers => ∀ j, z j ∉ ball x) = Fintype.piFinset (fun _ : Fin t => (ball x)ᶜ) := by
      ext z
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · exact fun h => Fintype.mem_piFinset.mpr (fun j => Finset.mem_compl.mpr (h j))
      · exact fun h j => Finset.mem_compl.mp (Fintype.mem_piFinset.mp h j)
    have size : (ball x).card = V := L_lib_486.volume x r
    have rest : (ball x)ᶜ.card = q^n-V := by rw [Finset.card_compl,hcardW,size]
    rw [same,Fintype.card_piFinset]
    simp only [rest,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have count : (∑ z : Centers, (missed z).card) = q^n*(q^n-V)^t := by
    calc
      _ = ∑ x : Word, (Finset.univ.filter (fun z : Centers => ∀ j, z j ∉ ball x)).card := by
        simp only [missed,Finset.card_filter]
        exact Finset.sum_comm
      _ = _ := by simp [avoid,hcardW]
  obtain ⟨z,_,hz⟩ := (Finset.univ : Finset Centers).exists_min_image (fun z => (missed z).card) Finset.univ_nonempty
  have hb : (missed z).card * (q^n)^t ≤ q^n*(q^n-V)^t := by
    have le := Finset.sum_le_sum (s := (Finset.univ : Finset Centers)) (fun i hi => hz i hi)
    rw [count] at le
    simpa [hcardZ,Nat.mul_comm] using le
  let base : Finset Word := Finset.univ.image z
  refine ⟨base ∪ missed z, ?_, ?_⟩
  · intro x
    by_cases covered : ∃ j, z j ∈ ball x
    · obtain ⟨j,hj⟩ := covered
      exact ⟨z j,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩),(Finset.mem_filter.mp hj).2⟩
    · refine ⟨x,Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j hj => covered ⟨j,hj⟩⟩),?_⟩
      simp
  · have nb : base.card ≤ t := by simpa [base] using (Finset.card_image_le (s := Finset.univ) (f := z))
    have total : (base ∪ missed z).card ≤ t + (missed z).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_right nb _)
    calc
      _ ≤ (t + (missed z).card) * (q^n)^t := Nat.mul_le_mul_right _ total
      _ ≤ _ := by rw [Nat.add_mul]; exact Nat.add_le_add_left hb _
