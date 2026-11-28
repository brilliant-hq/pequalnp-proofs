import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_17744_3 (h1 : let S := PEqualNP.HeptadCover.singerLines3
    let row := PEqualNP.GenericRejection.incidenceInput
    let q := PEqualNP.HeptadCover.quadrangles S
    let fit := fun (p l : Fin 13) (f g : List Bool → Bool) =>
      let neg := fun Q : Finset (Fin 13) => row (Q.erase p) ((PEqualNP.HeptadCover.missLines S Q).erase l)
      (∀ i j : Fin 13, i ≠ p → j ≠ l → i ∈ S j → f (row {i} {j}) = true ∧ g (row {i} {j}) = true) ∧
      (∀ Q ∈ q, (f (neg Q) && g (neg Q)) = false) ∧
      (∃ Q ∈ q, f (neg Q) = true) ∧ (∃ Q ∈ q, g (neg Q) = true)
    let ok := fun g : PEqualNP.CircuitLowerBounds.Gate => (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
    let term := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) =>
      g.op.eval (g.inputs.map fun i => (D.wires (x ++ [true])).getD i false)
    ∀ (p l : Fin 13) (C E : PEqualNP.CircuitLowerBounds.Circuit), p ∈ S l → C.gates = E.gates →
      PEqualNP.MetaComplexity.Monotone2 C → fit p l C.eval E.eval → ∃ D G H,
        PEqualNP.MetaComplexity.Monotone2 D ∧ ok G ∧ ok H ∧ D.size + 2 ≤ C.size ∧ fit 0 0 (term D G) (term D H)) (h2 : let ok := fun g : PEqualNP.CircuitLowerBounds.Gate => (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2
    let term := fun (D : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) =>
      g.op.eval (g.inputs.map fun i => (D.wires (x ++ [true])).getD i false)
    let R := Finset (List Bool)
    let bank := fun (T : R) (n : ℕ) (w : List R) =>
      insert ∅ (insert T ((Finset.range n).image (fun i => T.filter (fun r => r.getD i false = true)))) ∪ w.toFinset
    let make := fun (B : Finset R) (s : R) => ∃ a ∈ B, ∃ b ∈ B, s = a ∪ b ∨ s = a ∩ b
    let grows := fun (T : R) (n : ℕ) (w : List R) => ∀ i : Fin w.length,
      w[i.val] ∉ bank T n (w.take i.val) ∧ make (bank T n (w.take i.val)) w[i.val]
    ∀ (T : R) (n : ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit) (G H : PEqualNP.CircuitLowerBounds.Gate),
      (∀ r ∈ T, r.length = n) → PEqualNP.MetaComplexity.Monotone2 D → ok G → ok H →
        ∃ w : List R, w.length ≤ D.size ∧ grows T n w ∧
          make (bank T n w) (T.filter (fun r => term D G r = true)) ∧
          make (bank T n w) (T.filter (fun r => term D H r = true))) (h3 : let S := PEqualNP.HeptadCover.singerLines3
    let row := PEqualNP.GenericRejection.incidenceInput
    let P := (Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 ≠ 0 ∧ e.2 ≠ 0 ∧ e.1 ∈ S e.2)).image
      (fun e => row {e.1} {e.2})
    let N := (PEqualNP.HeptadCover.quadrangles S).image
      (fun Q => row (Q.erase 0) ((PEqualNP.HeptadCover.missLines S Q).erase 0))
    let R := Finset (List Bool)
    let bank := fun (T : R) (n : ℕ) (w : List R) =>
      insert ∅ (insert T ((Finset.range n).image (fun i => T.filter (fun r => r.getD i false = true)))) ∪ w.toFinset
    let make := fun (B : Finset R) (s : R) => ∃ a ∈ B, ∃ b ∈ B, s = a ∪ b ∨ s = a ∩ b
    let grows := fun (T : R) (n : ℕ) (w : List R) => ∀ i : Fin w.length,
      w[i.val] ∉ bank T n (w.take i.val) ∧ make (bank T n (w.take i.val)) w[i.val]
    ∀ (w : List R) (a b : R), grows (P ∪ N) 26 w → make (bank (P ∪ N) 26 w) a →
      make (bank (P ∪ N) 26 w) b → a ∩ b = P → (a ∩ N).Nonempty → (b ∩ N).Nonempty → 54 ≤ w.length) : have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; ∀ (x2 x3 : Fin (13 : ℕ)) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 ∈ x1 x3 →     x4.gates = x5.gates →       PEqualNP.MetaComplexity.Monotone2 x4 →         (∀ (x9 x10 : Fin (13 : ℕ)), x9 ≠ x2 → x10 ≠ x3 → x9 ∈ x1 x10 → ∀ x14 ∈ [x4, x5], x14.eval (PEqualNP.GenericRejection.incidenceInput {x9} {x10}) = Bool.true) →           have x10 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Finset (Fin (13 : ℕ))) := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => {x11 ∈ PEqualNP.HeptadCover.quadrangles x1 | x10.eval (PEqualNP.GenericRejection.incidenceInput (x11.erase x2) ((PEqualNP.HeptadCover.missLines x1 x11).erase x3)) = Bool.true};           Disjoint (x10 x4) (x10 x5) → (x10 x4).Nonempty → (x10 x5).Nonempty → (56 : ℕ) ≤ x4.size := by
  intro S0 p l C E hp he hm hpos F0 hd hu hv
  have hf := h1 p l C E hp he hm
  obtain ⟨D,G,H,hD,hG,hH,hsize,fit⟩ := hf (by
    refine ⟨?_,?_,?_,?_⟩
    · intro i j hi hj hs
      exact ⟨hpos i j hi hj hs C (by simp),hpos i j hi hj hs E (by simp)⟩
    · intro Q hQ
      apply Bool.eq_false_iff.mpr
      intro hh
      simp only [Bool.and_eq_true] at hh
      obtain ⟨ha,hb⟩ := hh
      exact (Finset.disjoint_left.mp hd) (Finset.mem_filter.mpr ⟨hQ,ha⟩) (Finset.mem_filter.mpr ⟨hQ,hb⟩)
    · obtain ⟨Q,h⟩ := hu
      exact ⟨Q,(Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2⟩
    · obtain ⟨Q,h⟩ := hv
      exact ⟨Q,(Finset.mem_filter.mp h).1,(Finset.mem_filter.mp h).2⟩)
  let S := PEqualNP.HeptadCover.singerLines3
  let row := @PEqualNP.GenericRejection.incidenceInput 13 13
  let P := (Finset.univ.filter (fun e : Fin 13 × Fin 13 => e.1 ≠ 0 ∧ e.2 ≠ 0 ∧ e.1 ∈ S e.2)).image
    (fun e => row {e.1} {e.2})
  let N := (PEqualNP.HeptadCover.quadrangles S).image
    (fun Q => row (Q.erase 0) ((PEqualNP.HeptadCover.missLines S Q).erase 0))
  let T := P ∪ N
  let f := (fun (D : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) =>
      g.op.eval (g.inputs.map fun i => (D.wires (x ++ [true])).getD i false)) D G
  let g := (fun (D : PEqualNP.CircuitLowerBounds.Circuit) (g : PEqualNP.CircuitLowerBounds.Gate) (x : List Bool) =>
      g.op.eval (g.inputs.map fun i => (D.wires (x ++ [true])).getD i false)) D H
  let a := T.filter (fun r => f r = true)
  let b := T.filter (fun r => g r = true)
  have good (r) (hr : r ∈ P) : f r = true ∧ g r = true := by
    obtain ⟨⟨i,j⟩,h,rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hi,hj,hs⟩ := (Finset.mem_filter.mp h).2
    exact fit.1 i j hi hj hs
  have miss (r) (hr : r ∈ N) : (f r && g r) = false := by
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hr
    exact fit.2.1 Q hQ
  have hl : ∀ r ∈ T, List.length r = 26 := by
    intro r hr
    rcases Finset.mem_union.mp hr with h|h <;> obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp h <;>
      simp [row,PEqualNP.GenericRejection.incidenceInput]
  obtain ⟨w,hw,hgrow,hA,hB⟩ := h2 T 26 D G H hl hD hG hH
  have bound := h3 w a b hgrow hA hB (by
    ext r
    constructor
    · intro h
      obtain ⟨l,rh⟩ := Finset.mem_inter.mp h
      obtain ⟨ht,hu⟩ := Finset.mem_filter.mp l
      rcases Finset.mem_union.mp ht with h|h
      · exact h
      · have e := miss r h
        simp [hu,(Finset.mem_filter.mp rh).2] at e
    · intro h
      obtain ⟨ha,hb⟩ := good r h
      exact Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_union_left _ h,ha⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_union_left _ h,hb⟩⟩) (by
    obtain ⟨Q,hQ,h⟩ := fit.2.2.1
    have hmem := Finset.mem_image_of_mem (s := PEqualNP.HeptadCover.quadrangles S)
      (fun Q => row (Q.erase 0) ((PEqualNP.HeptadCover.missLines S Q).erase 0)) hQ
    exact ⟨_,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hmem,h⟩,hmem⟩⟩) (by
    obtain ⟨Q,hQ,h⟩ := fit.2.2.2
    have hmem := Finset.mem_image_of_mem (s := PEqualNP.HeptadCover.quadrangles S)
      (fun Q => row (Q.erase 0) ((PEqualNP.HeptadCover.missLines S Q).erase 0)) hQ
    exact ⟨_,Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_union_right _ hmem,h⟩,hmem⟩⟩)
  omega
