import PEqualNP.Outside.L_meta_25825
import PEqualNP.Outside.L_meta_25826
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.ReadersExport
import PEqualNP.MetaComplexity.Helpers.ForestBound
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Pre-bridge for the negative twin of L-meta-9753

This local scaffold fixes the exact finite targets, proves the local size-ten
obstruction by fan-out and cofactor bounds, and composes it with the remaining
outer full-to-local bridge.  It is not a desk submission: the outer bridge
remains an explicit hypothesis.
-/

namespace PEqualNP.Outside.Pre_L_meta_9753_bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Represents
open PEqualNP.MetaComplexity.Helpers.PermInputs
open PEqualNP.MetaComplexity.Helpers.Readers

def localTarget (x : Fin 9 → Bool) : Bool :=
  (x 0 && (x 3 || x 4 || x 6)) ||
  (x 1 && (x 3 || x 5 || x 7)) ||
  (x 2 && (x 4 || x 5 || x 8))

def localGraph (u : Fin 3) (v : Fin 6) : Bool :=
  decide
    ((u = 0 ∧ (v = 0 ∨ v = 1 ∨ v = 3)) ∨
     (u = 1 ∧ (v = 0 ∨ v = 2 ∨ v = 4)) ∨
     (u = 2 ∧ (v = 1 ∨ v = 2 ∨ v = 5)))

def oneEachLocal (u : Fin 3) (v : Fin 6) : Fin 9 → Bool :=
  fun i => decide (i.val = u.val ∨ i.val = 3 + v.val)

theorem localTarget_oneEach (u : Fin 3) (v : Fin 6) :
    localTarget (oneEachLocal u v) = localGraph u v := by
  fin_cases u <;> fin_cases v <;> decide

def bits9 (w : Nat) : Fin 9 → Bool :=
  fun i => w.testBit i.val

theorem local_dep : ∃ p, Dep localTarget p := by
  exact ⟨0, bits9 8, by decide⟩

theorem local_restrNC : RestrNC localTarget := by
  intro p _ b
  fin_cases p <;> cases b <;>
    first
    | exact ⟨bits9 0, bits9 10, by decide⟩
    | exact ⟨bits9 0, bits9 9, by decide⟩
    | exact ⟨bits9 0, bits9 8, by decide⟩
    | exact ⟨bits9 0, bits9 17, by decide⟩
    | exact ⟨bits9 0, bits9 1, by decide⟩
    | exact ⟨bits9 0, bits9 2, by decide⟩
    | exact ⟨bits9 0, bits9 4, by decide⟩

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 10000 in
theorem local_noFunnel : NoFunnel localTarget := by
  intro p q hpq _ _ hf
  obtain ⟨a, b, hab⟩ := hf
  fin_cases p <;> fin_cases q <;> cases a <;> cases b <;> simp_all
  all_goals
    first
    | have h := hab (bits9 0); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 1); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 2); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 4); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 8); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 16); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 32); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 64); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 128); norm_num [bits9, set2, localTarget] at h; contradiction
    | have h := hab (bits9 256); norm_num [bits9, set2, localTarget] at h; contradiction

def LowerRestriction (p : Fin 9) (b : Bool) (lower : Nat) : Prop :=
  ∀ s, HasCircuitSize 9 (fun x => localTarget (Function.update x p b)) s → lower ≤ s

def CofactorBounds : Prop :=
  (∀ p : Fin 9, p.val < 3 →
    LowerRestriction p false 7 ∧ LowerRestriction p true 8) ∧
  (∀ p : Fin 9, 3 ≤ p.val → p.val < 6 →
    LowerRestriction p false 9 ∧ LowerRestriction p true 5) ∧
  (∀ p : Fin 9, 6 ≤ p.val →
    LowerRestriction p false 7 ∧ LowerRestriction p true 8)

theorem contradiction_of_row_or_private
    {p : Fin 9}
    (h0 : LowerRestriction p false 7)
    (h1 : LowerRestriction p true 8)
    (pay : Pays localTarget p 10) : False := by
  rcases pay with ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨d0, d1⟩
  · obtain ⟨s, hs, hc⟩ := d1
    have := h1 s hc
    omega
  · obtain ⟨s, hs, hc⟩ := d0
    have := h0 s hc
    omega
  · obtain ⟨s, hs, hc⟩ := d1
    have := h1 s hc
    omega

theorem contradiction_of_shared
    {p : Fin 9}
    (h0 : LowerRestriction p false 9)
    (pay : Pays localTarget p 10) : False := by
  rcases pay with ⟨d0, d1⟩ | ⟨d0, d1⟩ | ⟨d0, d1⟩ <;>
    obtain ⟨s, hs, hc⟩ := d0 <;>
    have := h0 s hc <;> omega

theorem no_local_ten_of_cofactor_bounds (bounds : CofactorBounds) :
    ¬ HasCircuitSize 9 localTarget 10 := by
  intro hlocal
  obtain ⟨p, hdep, pay⟩ := fanout_step 8 localTarget 10 local_dep local_restrNC local_noFunnel hlocal
  rcases bounds with ⟨hrow, hshared, hprivate⟩
  by_cases hr : p.val < 3
  · obtain ⟨h0, h1⟩ := hrow p hr
    exact contradiction_of_row_or_private h0 h1 pay
  · by_cases hs : p.val < 6
    · obtain ⟨h0, h1⟩ := hshared p (by omega) hs
      exact contradiction_of_shared h0 pay
    · obtain ⟨h0, h1⟩ := hprivate p (by omega)
      exact contradiction_of_row_or_private h0 h1 pay

def baseRelB (i j : Fin 9) : Bool :=
  ((i.val == 0) && ((j.val == 3) || (j.val == 4) || (j.val == 6))) ||
  ((i.val == 1) && ((j.val == 3) || (j.val == 5) || (j.val == 7))) ||
  ((i.val == 2) && ((j.val == 4) || (j.val == 5) || (j.val == 8)))

def baseRel (i j : Fin 9) : Prop := baseRelB i j = true

def baseAdjB (i j : Fin 9) : Bool :=
  !(i == j) && (baseRelB i j || baseRelB j i)

theorem baseAdjB_comm (i j : Fin 9) : baseAdjB j i = baseAdjB i j := by
  unfold baseAdjB
  have heq : (j == i) = (i == j) := Bool.beq_comm
  rw [heq, Bool.or_comm]

def baseGraph : SimpleGraph (Fin 9) where
  Adj i j := baseAdjB i j = true
  symm := ⟨fun i j h => by
    rw [baseAdjB_comm]
    exact h⟩
  loopless := ⟨fun i h => by
    unfold baseAdjB at h
    simp at h⟩

instance baseGraph_decidable : DecidableRel baseGraph.Adj := fun i j =>
  Bool.decEq (baseAdjB i j) true

def freeOf (p : Fin 9) : Finset (Fin 9) :=
  match p.val with
  | 0 => {3, 4, 6}
  | 1 => {3, 5, 7}
  | 2 => {4, 5, 8}
  | 3 => {0, 1}
  | 4 => {0, 2}
  | 5 => {1, 2}
  | 6 => {0}
  | 7 => {1}
  | _ => {2}

def falseAdjB (p i j : Fin 9) : Bool :=
  baseAdjB i j && !(i == p) && !(j == p)

theorem falseAdjB_comm (p i j : Fin 9) : falseAdjB p j i = falseAdjB p i j := by
  unfold falseAdjB
  rw [baseAdjB_comm]
  ac_rfl

def falseGraph (p : Fin 9) : SimpleGraph (Fin 9) where
  Adj i j := falseAdjB p i j = true
  symm := ⟨fun i j h => by
    rw [falseAdjB_comm]
    exact h⟩
  loopless := ⟨fun i h => by
    unfold falseAdjB baseAdjB at h
    simp at h⟩

instance falseGraph_decidable (p : Fin 9) : DecidableRel (falseGraph p).Adj :=
  fun i j => Bool.decEq (falseAdjB p i j) true

def trueAdjB (p i j : Fin 9) : Bool :=
  baseAdjB i j && !(i == p) && !(j == p) &&
    !(decide (i ∈ freeOf p)) && !(decide (j ∈ freeOf p))

theorem trueAdjB_comm (p i j : Fin 9) : trueAdjB p j i = trueAdjB p i j := by
  unfold trueAdjB
  rw [baseAdjB_comm]
  ac_rfl

def trueGraph (p : Fin 9) : SimpleGraph (Fin 9) where
  Adj i j := trueAdjB p i j = true
  symm := ⟨fun i j h => by
    rw [trueAdjB_comm]
    exact h⟩
  loopless := ⟨fun i h => by
    unfold trueAdjB baseAdjB at h
    simp at h⟩

instance trueGraph_decidable (p : Fin 9) : DecidableRel (trueGraph p).Adj :=
  fun i j => Bool.decEq (trueAdjB p i j) true

theorem localTarget_true_iff (x : Fin 9 → Bool) :
    localTarget x = true ↔
      ∃ i j : Fin 9, baseGraph.Adj i j ∧ x i = true ∧ x j = true := by
  simp only [localTarget, Bool.or_eq_true, Bool.and_eq_true]
  constructor
  · rintro ((⟨h0, (h3 | h4) | h6⟩ | ⟨h1, (h3 | h5) | h7⟩) |
      ⟨h2, (h4 | h5) | h8⟩)
    · exact ⟨0, 3, by change baseAdjB 0 3 = true; decide, h0, h3⟩
    · exact ⟨0, 4, by change baseAdjB 0 4 = true; decide, h0, h4⟩
    · exact ⟨0, 6, by change baseAdjB 0 6 = true; decide, h0, h6⟩
    · exact ⟨1, 3, by change baseAdjB 1 3 = true; decide, h1, h3⟩
    · exact ⟨1, 5, by change baseAdjB 1 5 = true; decide, h1, h5⟩
    · exact ⟨1, 7, by change baseAdjB 1 7 = true; decide, h1, h7⟩
    · exact ⟨2, 4, by change baseAdjB 2 4 = true; decide, h2, h4⟩
    · exact ⟨2, 5, by change baseAdjB 2 5 = true; decide, h2, h5⟩
    · exact ⟨2, 8, by change baseAdjB 2 8 = true; decide, h2, h8⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    fin_cases i <;> fin_cases j <;>
      simp_all [baseGraph, baseAdjB, baseRelB]

theorem falseGraph_adj_iff (p i j : Fin 9) :
    (falseGraph p).Adj i j ↔ baseGraph.Adj i j ∧ i ≠ p ∧ j ≠ p := by
  change falseAdjB p i j = true ↔ baseAdjB i j = true ∧ i ≠ p ∧ j ≠ p
  simp [falseAdjB, and_assoc]

theorem trueGraph_adj_iff (p i j : Fin 9) :
    (trueGraph p).Adj i j ↔
      baseGraph.Adj i j ∧ i ≠ p ∧ j ≠ p ∧ i ∉ freeOf p ∧ j ∉ freeOf p := by
  change trueAdjB p i j = true ↔
    baseAdjB i j = true ∧ i ≠ p ∧ j ≠ p ∧ i ∉ freeOf p ∧ j ∉ freeOf p
  simp [trueAdjB, and_assoc]

theorem mem_freeOf_iff (p j : Fin 9) : j ∈ freeOf p ↔ baseGraph.Adj p j := by
  change j ∈ freeOf p ↔ baseAdjB p j = true
  fin_cases p <;> fin_cases j <;> decide

theorem false_edge_iff (p : Fin 9) (x : Fin 9 → Bool) :
    (∃ i j, (falseGraph p).Adj i j ∧ x i = true ∧ x j = true) ↔
      ∃ i j, baseGraph.Adj i j ∧
        Function.update x p false i = true ∧ Function.update x p false j = true := by
  constructor
  · rintro ⟨i, j, hij, hi, hj⟩
    obtain ⟨hbase, hip, hjp⟩ := (falseGraph_adj_iff p i j).1 hij
    exact ⟨i, j, hbase, by simpa [Function.update_of_ne hip] using hi,
      by simpa [Function.update_of_ne hjp] using hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    have hip : i ≠ p := by
      intro e
      subst i
      simp at hi
    have hjp : j ≠ p := by
      intro e
      subst j
      simp at hj
    exact ⟨i, j, (falseGraph_adj_iff p i j).2 ⟨hij, hip, hjp⟩,
      by simpa [Function.update_of_ne hip] using hi,
      by simpa [Function.update_of_ne hjp] using hj⟩

theorem true_edge_iff (p : Fin 9) (x : Fin 9 → Bool) :
    ((∃ a ∈ freeOf p, x a = true) ∨
      ∃ i j, (trueGraph p).Adj i j ∧ x i = true ∧ x j = true) ↔
      ∃ i j, baseGraph.Adj i j ∧
        Function.update x p true i = true ∧ Function.update x p true j = true := by
  constructor
  · rintro (⟨a, ha, hxa⟩ | ⟨i, j, hij, hi, hj⟩)
    · have hpa := (mem_freeOf_iff p a).1 ha
      exact ⟨p, a, hpa, by simp, by
        have hap : a ≠ p := hpa.ne.symm
        simpa [Function.update_of_ne hap] using hxa⟩
    · obtain ⟨hbase, hip, hjp, _, _⟩ := (trueGraph_adj_iff p i j).1 hij
      exact ⟨i, j, hbase, by simpa [Function.update_of_ne hip] using hi,
        by simpa [Function.update_of_ne hjp] using hj⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    by_cases hip : i = p
    · subst i
      left
      exact ⟨j, (mem_freeOf_iff p j).2 hij, by
        have hjp : j ≠ p := hij.ne.symm
        simpa [Function.update_of_ne hjp] using hj⟩
    · by_cases hjp : j = p
      · subst j
        left
        exact ⟨i, (mem_freeOf_iff p i).2 hij.symm, by
          simpa [Function.update_of_ne hip] using hi⟩
      · have hxi : x i = true := by simpa [Function.update_of_ne hip] using hi
        have hxj : x j = true := by simpa [Function.update_of_ne hjp] using hj
        by_cases hif : i ∈ freeOf p
        · exact Or.inl ⟨i, hif, hxi⟩
        by_cases hjf : j ∈ freeOf p
        · exact Or.inl ⟨j, hjf, hxj⟩
        exact Or.inr ⟨i, j, (trueGraph_adj_iff p i j).2
          ⟨hij, hip, hjp, hif, hjf⟩, hxi, hxj⟩

theorem falseCofactor_eq_forest (p : Fin 9) :
    (fun x => localTarget (Function.update x p false)) =
      PEqualNP.MetaComplexity.Helpers.Forest.F (falseGraph p) ∅ := by
  funext x
  rw [Bool.eq_iff_iff, PEqualNP.MetaComplexity.Helpers.Forest.F_true,
    localTarget_true_iff]
  simpa using (false_edge_iff p x).symm

theorem trueCofactor_eq_forest (p : Fin 9) :
    (fun x => localTarget (Function.update x p true)) =
      PEqualNP.MetaComplexity.Helpers.Forest.F (trueGraph p) (freeOf p) := by
  funext x
  rw [Bool.eq_iff_iff, PEqualNP.MetaComplexity.Helpers.Forest.F_true,
    localTarget_true_iff]
  exact (true_edge_iff p x).symm

def falseExtraB (p i j : Fin 9) : Bool :=
  match p.val with
  | 0 => (i == 1) && ((j == 0) || (j == 6))
  | 1 => (i == 0) && ((j == 1) || (j == 7))
  | 2 => (i == 0) && ((j == 2) || (j == 8))
  | 3 => (i == 0) && (j == 3)
  | 4 => (i == 0) && (j == 4)
  | 5 => (i == 1) && (j == 5)
  | _ => false

def trueExtraB (p i j : Fin 9) : Bool :=
  match p.val with
  | 0 => (i == 1) && ((j == 0) || (j == 3) || (j == 4) || (j == 6))
  | 1 => (i == 0) && ((j == 1) || (j == 3) || (j == 5) || (j == 7))
  | 2 => (i == 0) && ((j == 2) || (j == 4) || (j == 5) || (j == 8))
  | 3 => (i == 2) && ((j == 0) || (j == 1) || (j == 3) || (j == 6) || (j == 7))
  | 4 => (i == 1) && ((j == 0) || (j == 2) || (j == 4) || (j == 6) || (j == 8))
  | 5 => (i == 0) && ((j == 1) || (j == 2) || (j == 5) || (j == 7) || (j == 8))
  | 6 => (i == 1) && ((j == 0) || (j == 6))
  | 7 => (i == 0) && ((j == 1) || (j == 7))
  | _ => (i == 0) && ((j == 2) || (j == 8))

def falseClosureAdjB (p i j : Fin 9) : Bool :=
  falseAdjB p i j || falseExtraB p i j || falseExtraB p j i

theorem falseClosureAdjB_comm (p i j : Fin 9) :
    falseClosureAdjB p j i = falseClosureAdjB p i j := by
  unfold falseClosureAdjB
  rw [falseAdjB_comm]
  ac_rfl

def trueClosureAdjB (p i j : Fin 9) : Bool :=
  trueAdjB p i j || trueExtraB p i j || trueExtraB p j i

theorem trueClosureAdjB_comm (p i j : Fin 9) :
    trueClosureAdjB p j i = trueClosureAdjB p i j := by
  unfold trueClosureAdjB
  rw [trueAdjB_comm]
  ac_rfl

def falseClosure (p : Fin 9) : SimpleGraph (Fin 9) where
  Adj i j := falseClosureAdjB p i j = true
  symm := ⟨fun i j h => by
    rw [falseClosureAdjB_comm]
    exact h⟩
  loopless := ⟨fun i h => by
    fin_cases p <;> fin_cases i <;>
      simp_all [falseClosureAdjB, falseAdjB, falseExtraB, baseAdjB, baseRelB]⟩

def trueClosure (p : Fin 9) : SimpleGraph (Fin 9) where
  Adj i j := trueClosureAdjB p i j = true
  symm := ⟨fun i j h => by
    rw [trueClosureAdjB_comm]
    exact h⟩
  loopless := ⟨fun i h => by
    fin_cases p <;> fin_cases i <;>
      simp_all [trueClosureAdjB, trueAdjB, trueExtraB, baseAdjB, baseRelB, freeOf]⟩

instance falseClosure_decidable (p : Fin 9) : DecidableRel (falseClosure p).Adj :=
  fun i j => Bool.decEq (falseClosureAdjB p i j) true

instance trueClosure_decidable (p : Fin 9) : DecidableRel (trueClosure p).Adj :=
  fun i j => Bool.decEq (trueClosureAdjB p i j) true

def explicitEdges (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj] : Finset (Sym2 (Fin 9)) :=
  Finset.univ.filter fun e => e ∈ G.edgeSet

theorem edge_ncard_eq_explicit (G : SimpleGraph (Fin 9)) [DecidableRel G.Adj] :
    G.edgeSet.ncard = (explicitEdges G).card := by
  have heq : G.edgeSet = (explicitEdges G : Set (Sym2 (Fin 9))) := by
    ext e
    simp [explicitEdges]
  rw [heq, Set.ncard_coe_finset]

theorem falseGraph_le_closure (p : Fin 9) : falseGraph p ≤ falseClosure p := by
  intro i j hij
  change falseAdjB p i j = true at hij
  change falseClosureAdjB p i j = true
  simp [falseClosureAdjB, hij]

theorem trueGraph_le_closure (p : Fin 9) : trueGraph p ≤ trueClosure p := by
  intro i j hij
  change trueAdjB p i j = true at hij
  change trueClosureAdjB p i j = true
  simp [trueClosureAdjB, hij]

theorem falseGraph_acyclic (p : Fin 9) (hp : p.val < 6) : (falseGraph p).IsAcyclic := by
  apply SimpleGraph.IsAcyclic.anti (falseGraph_le_closure p)
  have htree : (falseClosure p).IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    constructor
    · fin_cases p <;> simp_all <;> decide +kernel
    · rw [Nat.card_coe_set_eq, edge_ncard_eq_explicit, Nat.card_eq_fintype_card]
      fin_cases p <;> simp_all <;> decide +kernel
  exact htree.isAcyclic

theorem trueGraph_acyclic (p : Fin 9) : (trueGraph p).IsAcyclic := by
  apply SimpleGraph.IsAcyclic.anti (trueGraph_le_closure p)
  have htree : (trueClosure p).IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    constructor
    · fin_cases p <;> decide +kernel
    · rw [Nat.card_coe_set_eq, edge_ncard_eq_explicit, Nat.card_eq_fintype_card]
      fin_cases p <;> decide +kernel
  exact htree.isAcyclic

theorem false_lower_of_forest (p : Fin 9) (m k lower : Nat)
    (hm : (falseGraph p).edgeSet.ncard = m)
    (hac : (falseGraph p).IsAcyclic)
    (hedge : ∃ i j, (falseGraph p).Adj i j)
    (hcov : ∀ T, PEqualNP.MetaComplexity.Helpers.Forest.Cov (falseGraph p) T → k ≤ T.card)
    (hsize : lower + 1 ≤ m + k) : LowerRestriction p false lower := by
  intro s hc
  rw [falseCofactor_eq_forest p] at hc
  have h := PEqualNP.MetaComplexity.Helpers.Forest.claimQ m 9 (falseGraph p) ∅ k s
    hm hac (by simp) hcov (Or.inr hedge) hc
  simp only [Finset.card_empty, zero_add] at h
  omega

theorem true_lower_of_forest (p : Fin 9) (m k lower : Nat)
    (hm : (trueGraph p).edgeSet.ncard = m)
    (hac : (trueGraph p).IsAcyclic)
    (hinv : ∀ i j, (trueGraph p).Adj i j → i ∉ freeOf p)
    (hcov : ∀ T, PEqualNP.MetaComplexity.Helpers.Forest.Cov (trueGraph p) T → k ≤ T.card)
    (hne : (freeOf p).Nonempty ∨ ∃ i j, (trueGraph p).Adj i j)
    (hsize : lower + 1 ≤ (freeOf p).card + m + k) : LowerRestriction p true lower := by
  intro s hc
  rw [trueCofactor_eq_forest p] at hc
  have h := PEqualNP.MetaComplexity.Helpers.Forest.claimQ m 9 (trueGraph p) (freeOf p) k s
    hm hac hinv hcov hne hc
  omega

theorem cover_one_of_edge (G : SimpleGraph (Fin 9)) {a b : Fin 9}
    (hab : G.Adj a b) (T : Finset (Fin 9))
    (hcov : PEqualNP.MetaComplexity.Helpers.Forest.Cov G T) : 1 ≤ T.card := by
  rcases hcov a b hab with ha | hb
  · exact Finset.card_pos.mpr ⟨a, ha⟩
  · exact Finset.card_pos.mpr ⟨b, hb⟩

theorem cover_two_of_edges (G : SimpleGraph (Fin 9)) {a b c d : Fin 9}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (T : Finset (Fin 9)) (hcov : PEqualNP.MetaComplexity.Helpers.Forest.Cov G T) :
    2 ≤ T.card := by
  rcases hcov a b hab with ha | hb <;> rcases hcov c d hcd with hc | hd
  · exact Finset.Nontrivial.two_le_card ⟨a, ha, c, hc, hac⟩
  · exact Finset.Nontrivial.two_le_card ⟨a, ha, d, hd, had⟩
  · exact Finset.Nontrivial.two_le_card ⟨b, hb, c, hc, hbc⟩
  · exact Finset.Nontrivial.two_le_card ⟨b, hb, d, hd, hbd⟩

theorem three_of_mem (T : Finset (Fin 9)) {a b c : Fin 9}
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ T.card := by
  have hsub : ({a, b, c} : Finset (Fin 9)) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcard := Finset.card_le_card hsub
  simpa [hab, hac, hbc] using hcard

theorem cover_three_private (G : SimpleGraph (Fin 9))
    (h06 : G.Adj 0 6) (h17 : G.Adj 1 7) (h28 : G.Adj 2 8)
    (T : Finset (Fin 9)) (hcov : PEqualNP.MetaComplexity.Helpers.Forest.Cov G T) :
    3 ≤ T.card := by
  rcases hcov 0 6 h06 with h0 | h6 <;>
    rcases hcov 1 7 h17 with h1 | h7 <;>
    rcases hcov 2 8 h28 with h2 | h8
  · exact three_of_mem T h0 h1 h2 (by decide) (by decide) (by decide)
  · exact three_of_mem T h0 h1 h8 (by decide) (by decide) (by decide)
  · exact three_of_mem T h0 h7 h2 (by decide) (by decide) (by decide)
  · exact three_of_mem T h0 h7 h8 (by decide) (by decide) (by decide)
  · exact three_of_mem T h6 h1 h2 (by decide) (by decide) (by decide)
  · exact three_of_mem T h6 h1 h8 (by decide) (by decide) (by decide)
  · exact three_of_mem T h6 h7 h2 (by decide) (by decide) (by decide)
  · exact three_of_mem T h6 h7 h8 (by decide) (by decide) (by decide)

theorem row0_false_lower : LowerRestriction 0 false 7 :=
  false_lower_of_forest 0 6 2 7
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (falseGraph_acyclic 0 (by omega))
    (by decide +kernel)
    (fun T hT => cover_two_of_edges (falseGraph 0) (a := 1) (b := 7) (c := 2) (d := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by omega)

theorem row0_true_lower : LowerRestriction 0 true 8 :=
  true_lower_of_forest 0 4 2 8
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 0) (by decide +kernel)
    (fun T hT => cover_two_of_edges (trueGraph 0) (a := 1) (b := 7) (c := 2) (d := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by decide +kernel) (by decide +kernel)

theorem row1_false_lower : LowerRestriction 1 false 7 :=
  false_lower_of_forest 1 6 2 7
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (falseGraph_acyclic 1 (by omega))
    (by decide +kernel)
    (fun T hT => cover_two_of_edges (falseGraph 1) (a := 0) (b := 6) (c := 2) (d := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by omega)

theorem row1_true_lower : LowerRestriction 1 true 8 :=
  true_lower_of_forest 1 4 2 8
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 1)
    (fun i j h => ((trueGraph_adj_iff 1 i j).1 h).2.2.2.1)
    (fun T hT => cover_two_of_edges (trueGraph 1) (a := 0) (b := 6) (c := 2) (d := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem row2_false_lower : LowerRestriction 2 false 7 :=
  false_lower_of_forest 2 6 2 7
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (falseGraph_acyclic 2 (by omega))
    (by decide +kernel)
    (fun T hT => cover_two_of_edges (falseGraph 2) (a := 0) (b := 6) (c := 1) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by omega)

theorem row2_true_lower : LowerRestriction 2 true 8 :=
  true_lower_of_forest 2 4 2 8
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 2)
    (fun i j h => ((trueGraph_adj_iff 2 i j).1 h).2.2.2.1)
    (fun T hT => cover_two_of_edges (trueGraph 2) (a := 0) (b := 6) (c := 1) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem shared3_false_lower : LowerRestriction 3 false 9 :=
  false_lower_of_forest 3 7 3 9
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (falseGraph_acyclic 3 (by omega))
    (by decide +kernel)
    (fun T hT => cover_three_private (falseGraph 3) (by decide) (by decide) (by decide) T hT)
    (by omega)

theorem shared3_true_lower : LowerRestriction 3 true 5 :=
  true_lower_of_forest 3 3 1 5
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 3)
    (fun i j h => ((trueGraph_adj_iff 3 i j).1 h).2.2.2.1)
    (fun T hT => cover_one_of_edge (trueGraph 3) (a := 2) (b := 8) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem shared4_false_lower : LowerRestriction 4 false 9 :=
  false_lower_of_forest 4 7 3 9
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (falseGraph_acyclic 4 (by omega))
    (by decide +kernel)
    (fun T hT => cover_three_private (falseGraph 4) (by decide) (by decide) (by decide) T hT)
    (by omega)

theorem shared4_true_lower : LowerRestriction 4 true 5 :=
  true_lower_of_forest 4 3 1 5
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 4)
    (fun i j h => ((trueGraph_adj_iff 4 i j).1 h).2.2.2.1)
    (fun T hT => cover_one_of_edge (trueGraph 4) (a := 1) (b := 7) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem shared5_false_lower : LowerRestriction 5 false 9 :=
  false_lower_of_forest 5 7 3 9
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (falseGraph_acyclic 5 (by omega))
    (by decide +kernel)
    (fun T hT => cover_three_private (falseGraph 5) (by decide) (by decide) (by decide) T hT)
    (by omega)

theorem shared5_true_lower : LowerRestriction 5 true 5 :=
  true_lower_of_forest 5 3 1 5
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 5)
    (fun i j h => ((trueGraph_adj_iff 5 i j).1 h).2.2.2.1)
    (fun T hT => cover_one_of_edge (trueGraph 5) (a := 0) (b := 6) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem private6_true_lower : LowerRestriction 6 true 8 :=
  true_lower_of_forest 6 6 2 8
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 6)
    (fun i j h => ((trueGraph_adj_iff 6 i j).1 h).2.2.2.1)
    (fun T hT => cover_two_of_edges (trueGraph 6) (a := 1) (b := 7) (c := 2) (d := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem private7_true_lower : LowerRestriction 7 true 8 :=
  true_lower_of_forest 7 6 2 8
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 7)
    (fun i j h => ((trueGraph_adj_iff 7 i j).1 h).2.2.2.1)
    (fun T hT => cover_two_of_edges (trueGraph 7) (a := 0) (b := 6) (c := 2) (d := 8)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem private8_true_lower : LowerRestriction 8 true 8 :=
  true_lower_of_forest 8 6 2 8
    (by rw [edge_ncard_eq_explicit]; decide +kernel) (trueGraph_acyclic 8)
    (fun i j h => ((trueGraph_adj_iff 8 i j).1 h).2.2.2.1)
    (fun T hT => cover_two_of_edges (trueGraph 8) (a := 0) (b := 6) (c := 1) (d := 7)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) T hT)
    (by left; decide +kernel) (by decide +kernel)

theorem private_false_dep (p q : Fin 9) (hp : 6 ≤ p.val) (hpq : q ≠ p) :
    Dep (fun x => localTarget (Function.update x p false)) q := by
  fin_cases p <;> fin_cases q <;> simp_all [Dep]
  all_goals
    first
    | exact ⟨bits9 1, by decide⟩
    | exact ⟨bits9 2, by decide⟩
    | exact ⟨bits9 4, by decide⟩
    | exact ⟨bits9 8, by decide⟩
    | exact ⟨bits9 16, by decide⟩

theorem private_false_lower (p : Fin 9) (hp : 6 ≤ p.val) :
    LowerRestriction p false 7 := by
  intro s hc
  have h := PEqualNP.MetaComplexity.Helpers.PermInputs.dep_lower_set 9
    (fun x => localTarget (Function.update x p false)) (Finset.univ.erase p)
    (fun q hq => private_false_dep p q hp (Finset.mem_erase.mp hq).1) s hc
  have hcard : (Finset.univ.erase p : Finset (Fin 9)).card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, Fintype.card_fin]
  rw [hcard] at h
  omega

theorem cofactor_bounds : CofactorBounds := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    fin_cases p <;> simp_all
    · exact ⟨row0_false_lower, row0_true_lower⟩
    · exact ⟨row1_false_lower, row1_true_lower⟩
    · exact ⟨row2_false_lower, row2_true_lower⟩
  · intro p hp3 hp6
    fin_cases p <;> simp_all
    · exact ⟨shared3_false_lower, shared3_true_lower⟩
    · exact ⟨shared4_false_lower, shared4_true_lower⟩
    · exact ⟨shared5_false_lower, shared5_true_lower⟩
  · intro p hp
    fin_cases p <;> simp_all
    · exact ⟨private_false_lower 6 (by omega), private6_true_lower⟩
    · exact ⟨private_false_lower 7 (by omega), private7_true_lower⟩
    · exact ⟨private_false_lower 8 (by omega), private8_true_lower⟩

theorem no_local_ten : ¬ HasCircuitSize 9 localTarget 10 :=
  no_local_ten_of_cofactor_bounds cofactor_bounds

/-- Mask-362 column order `[8,3,7,6]` in the original nine-input numbering. -/
def col362 : Fin 4 → Fin 6
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 4
  | _ => 3

def restriction362 (u v : Fin 4) : Bool :=
  if h : u.val < 3 then localGraph ⟨u.val, h⟩ (col362 v) else false

theorem restriction362_eq_mask :
    restriction362 = fun u v : Fin 4 => (362 : Nat).testBit (4 * u.val + v.val) := by
  funext u v
  fin_cases u <;> fin_cases v <;> decide

/-- One mask-363 column order `[4,3,7,6]` in original input numbering. -/
def col363 : Fin 4 → Fin 6
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 4
  | _ => 3

def restriction363 (u : Fin 3) (v : Fin 4) : Bool :=
  localGraph u (col363 v)

theorem restriction363_eq_mask :
    restriction363 = fun u v => (363 : Nat).testBit (4 * u.val + v.val) := by
  funext u v
  fin_cases u <;> fin_cases v <;> decide

def Mask362Six : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 6 ∧ Represents restriction362 C

def LocalTenToMask362Six : Prop :=
  HasCircuitSize 9 localTarget 10 → Mask362Six

def restrictedFalse (x : Fin 9 → Bool) : Bool :=
  localTarget (Function.update (Function.update x (4 : Fin 9) false) (5 : Fin 9) false)

/-- Original inputs into the padded mask-362 order: rows 0,1,2; dummy row 3;
columns `[8,3,7,6]`.  Fixed inputs 4 and 5 may map arbitrarily. -/
def pi362 : Fin 9 → Fin 8
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 0
  | ⟨6, _⟩ => 7
  | ⟨7, _⟩ => 6
  | _ => 4

def promise8 (u v : Fin 4) : Fin 8 → Bool :=
  fun i => decide (i.val = u.val ∨ i.val = 4 + v.val)

theorem oneEach_eq_ofFn_promise8 (u v : Fin 4) :
    oneEach u v = List.ofFn (promise8 u v) := by
  fin_cases u <;> fin_cases v <;> decide

theorem restrictedFalse_promise8 (u v : Fin 4) :
    restrictedFalse (promise8 u v ∘ pi362) = restriction362 u v := by
  fin_cases u <;> fin_cases v <;> decide

def DoubleFalseSavesFour : Prop :=
  HasCircuitSize 9 localTarget 10 → HasCircuitSize 9 restrictedFalse 6

/-- The named four-gate saving now follows from the unconditional local lower bound:
there is no size-ten local circuit from which a counterexample could arise. -/
theorem doubleFalseSavesFour : DoubleFalseSavesFour := by
  intro hlocal
  exact (no_local_ten hlocal).elim

theorem local_to_mask_of_double_false (saving : DoubleFalseSavesFour) :
    LocalTenToMask362Six := by
  intro hlocal
  have h9 := saving hlocal
  have h8 := relabel_size pi362 restrictedFalse 6 h9
  obtain ⟨C, hfan, hsize, hev⟩ := h8
  refine ⟨C, hfan, hsize, ?_⟩
  intro u v
  rw [oneEach_eq_ofFn_promise8, hev]
  exact restrictedFalse_promise8 u v

theorem no_local_ten_of_bridge (bridge : LocalTenToMask362Six) :
    ¬ HasCircuitSize 9 localTarget 10 := by
  intro hlocal
  obtain ⟨C, hfan, hsize, hrep⟩ := bridge hlocal
  apply PEqualNP.Outside.L_meta_25825
  refine ⟨C, hfan, hsize, ?_⟩
  intro u v
  rw [← restriction362_eq_mask]
  exact hrep u v

theorem no_local_ten_of_double_false (saving : DoubleFalseSavesFour) :
    ¬ HasCircuitSize 9 localTarget 10 :=
  no_local_ten_of_bridge (local_to_mask_of_double_false saving)

def fullTarget (x : Fin 14 → Bool) : Bool :=
  (x 0 && x 7) || (x 0 && x 8) || (x 0 && x 10) ||
  (x 1 && x 7) || (x 1 && x 9) || (x 1 && x 13) ||
  (x 2 && x 8) || (x 2 && x 12) || (x 2 && x 13) ||
  (x 3 && x 7) || (x 3 && x 11) || (x 3 && x 12) ||
  (x 4 && x 10) || (x 4 && x 11) || (x 4 && x 13) ||
  (x 5 && x 9) || (x 5 && x 10) || (x 5 && x 12) ||
  (x 6 && x 8) || (x 6 && x 9) || (x 6 && x 11)

def Full26ToLocalTen : Prop :=
  HasCircuitSize 14 fullTarget 26 → HasCircuitSize 9 localTarget 10

theorem no_full_26_of_outer (outer : Full26ToLocalTen) :
    ¬ HasCircuitSize 14 fullTarget 26 := by
  intro full
  exact no_local_ten (outer full)

theorem no_full_26_of_bridges
    (outer : Full26ToLocalTen) (inner : LocalTenToMask362Six) :
    ¬ HasCircuitSize 14 fullTarget 26 := by
  intro full
  exact no_local_ten_of_bridge inner (outer full)

end PEqualNP.Outside.Pre_L_meta_9753_bridge
