import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_20814 : (∀ (m : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
  (∀ g ∈ C.gates,
    ((g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
        g.inputs.length = 2) ∨
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ g.inputs.length = 1)) →
  PEqualNP.MetaComplexity.NestedCover.ReadsBack m C →
  0 < C.size →
  (∀ j < C.size,
    (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) = 0 ↔ j + 1 = C.size)) →
  (∑ w ∈ @Finset.filter ℕ
        (fun w1 => 2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w1)
        (fun d1 => Classical.propDecidable _) (Finset.range m),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
    (∑ j ∈ @Finset.filter ℕ
        (fun j1 => (PEqualNP.MetaComplexity.NestedCover.gateAt C j1).op =
            PEqualNP.CircuitLowerBounds.GateOp.not ∨
          2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j1))
        (fun d2 => Classical.propDecidable _) (Finset.range C.size),
      PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j)) +
    2 * (@Finset.filter ℕ
        (fun w2 => 1 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w2)
        (fun d3 => Classical.propDecidable _) (Finset.range m)).card ≤
  2 * ((∑ w ∈ Finset.range m, PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) w) +
      (∑ j ∈ @Finset.filter ℕ (fun i => i + 1 < C.size) (fun d4 => Classical.propDecidable _)
          (Finset.range C.size),
        (PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size) (m + j) - 1)) +
      (@Finset.filter ℕ (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op =
          PEqualNP.CircuitLowerBounds.GateOp.not) (fun d5 => Classical.propDecidable _)
          (Finset.range C.size)).card)) := by
  classical
  intro m C _ _ _ last
  let R := PEqualNP.MetaComplexity.NestedCover.readsIn C (Finset.range C.size)
  let N := fun j => (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
    PEqualNP.CircuitLowerBounds.GateOp.not
  have inputs := Finset.sum_le_sum (s := Finset.range m) (fun w _ =>
    show (if 2 ≤ R w then R w else 0) + 2 * (if 1 ≤ R w then 1 else 0) ≤ 2 * R w by
      split_ifs <;> omega)
  have gates := Finset.sum_le_sum (s := Finset.range C.size) (fun j hj =>
    show (if N j ∨ 2 ≤ R (m+j) then R (m+j) else 0) ≤
      2 * (if j+1 < C.size then R (m+j)-1 else 0) + 2 * (if N j then 1 else 0) by
      have hj' := Finset.mem_range.mp hj
      have hz : R (m+j) = 0 ↔ j+1 = C.size := last j hj'
      by_cases final : j+1 = C.size
      · have z := hz.mpr final
        simp [z]
      · have earlier : j+1 < C.size := by omega
        by_cases hn : N j <;> by_cases many : 2 ≤ R (m+j) <;>
          simp [earlier,hn,many] <;> omega)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at inputs gates
  simp only [Finset.sum_filter, Finset.card_filter]
  dsimp only [R,N] at inputs gates
  let charge (p : Prop) (a : ℕ) := @ite ℕ p (Classical.propDecidable p) a 0
  have norm (p : Prop) [Decidable p] (a : ℕ) : (if p then a else 0) = charge p a := by
    by_cases h : p <;> simp [charge,h]
  simp only [norm] at inputs gates ⊢
  omega
