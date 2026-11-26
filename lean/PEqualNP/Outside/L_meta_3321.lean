import Mathlib
import PEqualNP.Defs

/- 已用 lake env lean --stdin 核验本文件。指定的 lake build 因构建目录只读而失败。
   原定理尚未证完。normalize_of_descent 将剩余工作归结为 steps 中的两条改写命题：
   一条处理在单点上为真的 AND 门，另一条处理所有单点均已排除后的混合输入。
   两种改写须保持输出、保持大小上界，并使同一个自然数势函数严格下降。 -/

namespace PEqualNP.Outside.L_meta_3321

open CircuitLowerBounds MetaComplexity MetaComplexity.NestedCover
open EdgeOwnership (gateVal)

variable {N : ℕ}

abbrev Edge (I : Fin N → Fin N → Prop) (z : Fin (N + N) → Bool) :=
  ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true

abbrev one (a k : Fin (N + N)) := decide (k = a)

private theorem apart (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = N + l.val at hv
  have := p.isLt
  omega

private theorem noEdge_one (I : Fin N → Fin N → Prop) (a : Fin (N + N)) :
    ¬ Edge I (one a) := by
  rintro ⟨p, l, _, hp, hl⟩
  exact apart p l ((of_decide_eq_true hp).trans (of_decide_eq_true hl).symm)

theorem edge_pair (I : Fin N → Fin N → Prop) (p l : Fin N) :
    Edge I (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) ↔ I p l := by
  constructor
  · rintro ⟨q, m, h, hq, hm⟩
    have h₁ := (of_decide_eq_true hq).resolve_right (apart q l)
    have h₂ := (of_decide_eq_true hm).resolve_left (Ne.symm (apart p m))
    have hq' : q = p := Fin.ext (congrArg (Fin.val (n := N + N)) h₁)
    have hm' : m = l := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h₂))
    simpa [hq', hm'] using h
  · intro h
    exact ⟨p, l, h, by simp, by simp⟩

abbrev leftPart (z : Fin (N + N) → Bool) (k : Fin (N + N)) :=
  decide (k.val < N) && z k

abbrev rightPart (z : Fin (N + N) → Bool) (k : Fin (N + N)) :=
  decide (N ≤ k.val) && z k

abbrev Fires (D : Circuit) (j : ℕ) (z : Fin (N + N) → Bool) :=
  gateVal (N + N) D j z = true

abbrev Mixed (I : Fin N → Fin N → Prop) (D : Circuit) (j : ℕ) :=
  ∃ z, Fires D j z ∧ ¬ Fires D j (leftPart z) ∧ ¬ Fires D j (rightPart z) ∧ ¬ Edge I z

abbrev Single (N : ℕ) (D : Circuit) (j : ℕ) :=
  (∃ p : Fin N, Fires D j (one (Fin.castAdd N p))) ∨
  (∃ l : Fin N, Fires D j (one (Fin.natAdd N l)))

theorem clean_of_forces (I : Fin N → Fin N → Prop) (D : Circuit) (j : ℕ)
    (hf : ∀ z, Fires D j z → Edge I z) : ¬ Mixed I D j ∧ ¬ Single N D j := by
  constructor
  · rintro ⟨z, hw, _, _, he⟩
    exact he (hf z hw)
  · rintro (⟨p, h⟩ | ⟨l, h⟩)
    · exact noEdge_one I _ (hf _ h)
    · exact noEdge_one I _ (hf _ h)

abbrev HasAnd (P : Circuit → ℕ → Prop) (D : Circuit) :=
  ∃ j < D.gates.length, (gateAt D j).op = GateOp.and ∧ P D j

abbrev Candidate (I : Fin N → Fin N → Prop) (D : Circuit) :=
  Monotone2 D ∧ ReadsBack (N + N) D ∧
  ∀ z, circuitFun (N + N) D z = true ↔ Edge I z

abbrev C4Free (I : Fin N → Fin N → Prop) :=
  ∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')

abbrev Improves (I : Fin N → Fin N → Prop) (rank : Circuit → ℕ) (D : Circuit) :=
  ∃ E, Candidate I E ∧ E.size ≤ D.size ∧ rank E < rank D

theorem normalize_of_descent
    (steps : ∀ {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I], C4Free I →
      ∃ rank : Circuit → ℕ,
        (∀ D, Candidate I D → HasAnd (Single n) D → Improves I rank D) ∧
        (∀ D, Candidate I D → ¬ HasAnd (Single n) D → HasAnd (Mixed I) D →
          Improves I rank D)) :
∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ z : Fin (N + N) → Bool, (D.wires (List.ofFn z)).getD (N + N + j) false = true → (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨ (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I inst C h4 hmono hreads hfun
  classical
  have hC : Candidate I C := ⟨hmono, hreads, hfun⟩
  obtain ⟨rank, hs, hm⟩ := steps I h4
  let P (r : ℕ) := ∃ D, Candidate I D ∧ D.size ≤ C.size ∧ rank D = r
  have hex : ∃ r, P r := ⟨_, C, hC, le_rfl, rfl⟩
  obtain ⟨D, hd, hsize, hr⟩ := Nat.find_spec hex
  have minimal : ¬ ∃ E, Candidate I E ∧ E.size ≤ D.size ∧ rank E < rank D := by
    rintro ⟨E, he, hle, hlt⟩
    have hmin := Nat.find_min' hex (show P (rank E) from ⟨E, he, hle.trans hsize, rfl⟩)
    omega
  have ns : ¬ HasAnd (Single N) D := fun h => minimal (hs D hd h)
  have nm : ¬ HasAnd (Mixed I) D := fun h => minimal (hm D hd ns h)
  refine ⟨D, hd.1, hd.2.1, hsize, hd.2.2, ?_, ?_⟩
  · intro j hj ha z hz
    by_cases hl : Fires D j (leftPart z)
    · exact Or.inl hl
    by_cases hr' : Fires D j (rightPart z)
    · exact Or.inr (Or.inl hr')
    exact Or.inr (Or.inr (by_contra fun he => nm ⟨j, hj, ha, z, hz, hl, hr', he⟩))
  · intro j hj ha
    constructor
    · intro p
      apply Bool.eq_false_iff.mpr
      exact fun h => ns ⟨j, hj, ha, Or.inl ⟨p, h⟩⟩
    · intro l
      apply Bool.eq_false_iff.mpr
      exact fun h => ns ⟨j, hj, ha, Or.inr ⟨l, h⟩⟩

end PEqualNP.Outside.L_meta_3321
