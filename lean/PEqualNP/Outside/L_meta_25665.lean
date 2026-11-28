import PEqualNP.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert

namespace PEqualNP.Outside.L_meta_25665_aux

-- The statement is false for every s. On oneEach inputs every wire is affine in the raw inputs plus the
-- nonlinear gates below it (module S). The operand slot row labels are injective by the row condition,
-- hence a bijection onto label space, so G u c = r u + s c + f (La u + Lb c) with f bent (module C).
-- In a bent chain of nonlinear gates no operand holds an earlier product (module B), so every operand
-- of a nonlinear gate is affine in the raw inputs, against the last clause (module G).

open PEqualNP.CircuitLowerBounds

def chi (z : ZMod 2) : ℤ := if z = 0 then 1 else -1
def walsh {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → ZMod 2) → ZMod 2) (w : ι → ZMod 2) : ℤ :=
  ∑ d : ι → ZMod 2, chi (F d + ∑ i, w i * d i)
def toZ (b : Bool) : ZMod 2 := if b then 1 else 0
def val (C : Circuit) (l : List Bool) (i : ℕ) : Bool := (C.wires l).getD i false
def nlB (g : Gate) : Bool := (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false,false]) (g.op.eval [false,true])) (xor (g.op.eval [true,false]) (g.op.eval [true,true]))

section ModS

open PEqualNP.Represents PEqualNP.MetaComplexity.NestedCover

-- one step of the wire fold of Circuit.wires
def smStep (w : List Bool) (g : Gate) : List Bool := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem smWires (C : Circuit) (l : List Bool) : C.wires l = C.gates.foldl smStep l := rfl

theorem smFoldLen (gs : List Gate) (w : List Bool) : (gs.foldl smStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [ih, smStep]; omega

theorem smFoldFront (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl smStep w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => rw [List.foldl_cons, ih _ (by simp [smStep]; omega)]; exact List.getD_append _ _ _ _ hk

theorem smGateAt (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

theorem smValBeyond (C : Circuit) (l : List Bool) (i : ℕ) (hi : l.length + C.gates.length ≤ i) :
    val C l i = false :=
  List.getD_eq_default _ _ (by rw [smWires, smFoldLen]; exact hi)

theorem val_input (C : Circuit) (l : List Bool) (i : ℕ) (hi : i < l.length) : val C l i = l.getD i false :=
  smFoldFront _ _ _ hi

theorem val_gate (C : Circuit) (n : ℕ) (hRB : ReadsBack n C) (l : List Bool) (hl : l.length = n) (j : ℕ)
    (hj : j < C.gates.length) :
    val C l (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val C l)) := by
  have hW : ((C.gates.take j).foldl smStep l).length = n + j := by rw [smFoldLen, hl, List.length_take]; omega
  have e1 : C.wires l =
      (C.gates.drop (j + 1)).foldl smStep (smStep ((C.gates.take j).foldl smStep l) (gateAt C j)) := by
    rw [smWires, smGateAt C j hj, ← List.foldl_cons, ← List.drop_eq_getElem_cons hj, ← List.foldl_append,
      List.take_append_drop]
  have hrb := hRB j hj
  revert hW e1 hrb
  generalize (C.gates.take j).foldl smStep l = X
  generalize gateAt C j = g
  intro hW e1 hrb
  have key : ∀ k < n + j + 1,
      val C l k = (X ++ [g.op.eval (g.inputs.map fun i => X.getD i false)]).getD k false := fun k hk => by
    unfold val; rw [e1]; exact smFoldFront _ _ _ (by simp [smStep]; omega)
  have hle : X.length ≤ n + j := by omega
  rw [key (n + j) (by omega), List.getD_append_right _ _ _ _ hle, hW, Nat.sub_self, List.getD_cons_zero]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi2 : i < X.length := by have := hrb i hi; omega
  rw [key i (by omega), List.getD_append _ _ _ _ hi2]

-- F is, on inputs of length n, affine in the inputs and the nonlinear gates below wire i
def smRep (C : Circuit) (n i : ℕ) (F : List Bool → ZMod 2) : Prop :=
  ∃ (b : ZMod 2) (cS : Fin n → ZMod 2) (cT : ℕ → ZMod 2),
    (∀ j, cT j ≠ 0 → j < C.gates.length ∧ nlB (gateAt C j) = true ∧ n + j ≤ i) ∧
    ∀ l : List Bool, l.length = n → F l = b + ∑ t : Fin n, cS t * toZ (l.getD t false) +
      ∑ j ∈ Finset.range C.gates.length, cT j * toZ (val C l (n + j))

theorem smRepConst (C : Circuit) (n i : ℕ) (a : ZMod 2) : smRep C n i (fun _ => a) :=
  ⟨a, fun _ => 0, fun _ => 0, fun _ h => (h rfl).elim, fun _ _ => by simp⟩

theorem smRepAdd {C : Circuit} {n i : ℕ} {F G : List Bool → ZMod 2} (hF : smRep C n i F)
    (hG : smRep C n i G) : smRep C n i (fun l => F l + G l) := by
  obtain ⟨b1, s1, t1, h1, e1⟩ := hF
  obtain ⟨b2, s2, t2, h2, e2⟩ := hG
  refine ⟨b1 + b2, fun t => s1 t + s2 t, fun j => t1 j + t2 j, fun j hj => ?_, fun l hl => ?_⟩
  · exact (em (t1 j = 0)).elim (fun h => h2 j (by simpa [h] using hj)) (h1 j)
  · simp only [e1 l hl, e2 l hl, add_mul, Finset.sum_add_distrib]
    ring

theorem smRepSmul {C : Circuit} {n i : ℕ} {F : List Bool → ZMod 2} (a : ZMod 2) (hF : smRep C n i F) :
    smRep C n i (fun l => a * F l) := by
  obtain ⟨b, s, t, h, e⟩ := hF
  refine ⟨a * b, fun x => a * s x, fun j => a * t j, fun j hj => h j fun h0 => hj (by simp [h0]),
    fun l hl => ?_⟩
  simp only [e l hl, mul_add, Finset.mul_sum, mul_assoc]

theorem smRepMono {C : Circuit} {n i i' : ℕ} {F : List Bool → ZMod 2} (hF : smRep C n i F) (hii : i ≤ i') :
    smRep C n i' F := by
  obtain ⟨b, s, t, h, e⟩ := hF
  exact ⟨b, s, t, fun j hj => ⟨(h j hj).1, (h j hj).2.1, le_trans (h j hj).2.2 hii⟩, e⟩

theorem smRepCongr {C : Circuit} {n i : ℕ} {F G : List Bool → ZMod 2} (hF : smRep C n i F)
    (hFG : ∀ l : List Bool, l.length = n → F l = G l) : smRep C n i G := by
  obtain ⟨b, s, t, h, e⟩ := hF
  exact ⟨b, s, t, h, fun l hl => (hFG l hl).symm.trans (e l hl)⟩

theorem smRepInput (C : Circuit) (n i : ℕ) (hi : i < n) : smRep C n i (fun l => toZ (val C l i)) := by
  refine ⟨0, fun t => if t = ⟨i, hi⟩ then 1 else 0, fun _ => 0, fun _ h => (h rfl).elim, fun l hl => ?_⟩
  simp [val_input C l i (by omega)]

theorem smRepNl (C : Circuit) (n j : ℕ) (hj : j < C.gates.length) (hnl : nlB (gateAt C j) = true) :
    smRep C n (n + j) (fun l => toZ (val C l (n + j))) := by
  refine ⟨0, fun _ => 0, fun j' => if j' = j then 1 else 0, fun j' h => ?_, fun l _ => by simp [hj]⟩
  by_cases e : j' = j
  · subst e; exact ⟨hj, hnl, le_refl _⟩
  · simp [e] at h

theorem smC2 (f : Bool → Bool → Bool) (v0 v1 : Bool) :
    f v0 v1 = cond v0 (cond v1 (f true true) (f true false)) (cond v1 (f false true) (f false false)) := by
  cases v0 <;> cases v1 <;> rfl

theorem smAff1 (f : Bool → Bool) (v : Bool) :
    toZ (f v) = toZ (f false) + (toZ (f false) + toZ (f true)) * toZ v := by
  rw [show f v = cond v (f true) (f false) by cases v <;> rfl]
  generalize f false = a; generalize f true = b; revert a b v; decide

theorem smAff2 (f : Bool → Bool → Bool)
    (h : xor (xor (f false false) (f false true)) (xor (f true false) (f true true)) ≠ true) (v0 v1 : Bool) :
    toZ (f v0 v1) = toZ (f false false) + (toZ (f false false) + toZ (f true false)) * toZ v0 +
      (toZ (f false false) + toZ (f false true)) * toZ v1 := by
  rw [smC2 f v0 v1]; revert h; generalize f false false = a; generalize f false true = b
  generalize f true false = c; generalize f true true = d; revert a b c d v0 v1; decide

theorem smNl2 (f : Bool → Bool → Bool)
    (h : xor (xor (f false false) (f false true)) (xor (f true false) (f true true)) = true) (v0 v1 : Bool) :
    toZ (f v0 v1) = (toZ v0 + (toZ (f false false) + toZ (f false true))) *
      (toZ v1 + (toZ (f false false) + toZ (f true false))) +
      (toZ (f false false) + (toZ (f false false) + toZ (f false true)) *
        (toZ (f false false) + toZ (f true false))) := by
  rw [smC2 f v0 v1]; revert h; generalize f false false = a; generalize f false true = b
  generalize f true false = c; generalize f true true = d; revert a b c d v0 v1; decide

theorem smRepGate1 {C : Circuit} {n i a : ℕ} (g : Gate) (ha : smRep C n i (fun l => toZ (val C l a))) :
    smRep C n i (fun l => toZ (g.op.eval [val C l a])) :=
  smRepCongr (smRepAdd (smRepConst C n i (toZ (g.op.eval [false])))
    (smRepSmul (toZ (g.op.eval [false]) + toZ (g.op.eval [true])) ha))
    (fun l _ => (smAff1 (fun v => g.op.eval [v]) (val C l a)).symm)

theorem smRepGate2 {C : Circuit} {n i a b : ℕ} (g : Gate) (hin : g.inputs = [a, b]) (hnl : ¬ nlB g = true)
    (ha : smRep C n i (fun l => toZ (val C l a))) (hb : smRep C n i (fun l => toZ (val C l b))) :
    smRep C n i (fun l => toZ (g.op.eval [val C l a, val C l b])) := by
  have hx : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true])) ≠ true :=
    fun hc => hnl (by unfold nlB; rw [hin, hc]; rfl)
  exact smRepCongr (smRepAdd (smRepAdd (smRepConst C n i (toZ (g.op.eval [false, false])))
    (smRepSmul (toZ (g.op.eval [false, false]) + toZ (g.op.eval [true, false])) ha))
    (smRepSmul (toZ (g.op.eval [false, false]) + toZ (g.op.eval [false, true])) hb))
    (fun l _ => (smAff2 (fun v0 v1 => g.op.eval [v0, v1]) hx (val C l a) (val C l b)).symm)

theorem smRepAll (C : Circuit) (n : ℕ) (hRB : ReadsBack n C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (i : ℕ) : smRep C n i (fun l => toZ (val C l i)) := by
  refine Nat.strong_induction_on i (fun i ih => ?_)
  by_cases hi : i < n
  · exact smRepInput C n i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
  by_cases hj : C.gates.length ≤ j
  · exact smRepCongr (smRepConst C n (n + j) 0) (fun l hl => by rw [smValBeyond C l (n + j) (by omega)]; rfl)
  have hj' : j < C.gates.length := by omega
  by_cases hnl : nlB (gateAt C j) = true
  · exact smRepNl C n j hj' hnl
  have hlen := hfan (gateAt C j) (by rw [smGateAt C j hj']; exact List.getElem_mem hj')
  have hrb := hRB j hj'
  have hval : ∀ l : List Bool, l.length = n →
      val C l (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (val C l)) :=
    fun l hl => val_gate C n hRB l hl j hj'
  revert hnl hlen hrb hval
  generalize gateAt C j = g
  intro hnl hlen hrb hval
  rcases hin : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact smRepCongr (smRepConst C n (n + j) (toZ (g.op.eval []))) (fun l hl => by
      rw [hval l hl, hin, List.map_nil])
  · have ha : a < n + j := hrb a (by simp [hin])
    exact smRepCongr (smRepGate1 g (smRepMono (ih a ha) ha.le)) (fun l hl => by
      rw [hval l hl, hin, List.map_cons, List.map_nil])
  · have ha : a < n + j := hrb a (by simp [hin])
    have hb : b < n + j := hrb b (by simp [hin])
    exact smRepCongr (smRepGate2 g hin hnl (smRepMono (ih a ha) ha.le) (smRepMono (ih b hb) hb.le)) (fun l hl => by
      rw [hval l hl, hin, List.map_cons, List.map_cons, List.map_nil])
  · rw [hin, List.length_cons, List.length_cons, List.length_cons] at hlen
    omega

theorem rep_exists (C : Circuit) (n : ℕ) (hRB : ReadsBack n C) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (i : ℕ) :
    ∃ (b : ZMod 2) (cS : Fin n → ZMod 2) (cT : ℕ → ZMod 2),
      (∀ j, cT j ≠ 0 → j < C.gates.length ∧ nlB (gateAt C j) = true ∧ n + j ≤ i) ∧
      ∀ l : List Bool, l.length = n → toZ (val C l i) = b + ∑ t : Fin n, cS t * toZ (l.getD t false) +
        ∑ j ∈ Finset.range C.gates.length, cT j * toZ (val C l (n + j)) :=
  smRepAll C n hRB hfan i

theorem nl_normal (g : Gate) (h : nlB g = true) : ∃ i0 i1 : ℕ, g.inputs = [i0, i1] ∧
    ∃ p q r : ZMod 2, ∀ v0 v1 : Bool, toZ (g.op.eval [v0, v1]) = (toZ v0 + p) * (toZ v1 + q) + r := by
  unfold nlB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h2, hx⟩ := h
  match hin : g.inputs, h2 with
  | [i0, i1], _ => exact ⟨i0, i1, rfl, _, _, _, smNl2 (fun v0 v1 => g.op.eval [v0, v1]) hx⟩

theorem oneEach_length {N : ℕ} (u c : Fin N) : (oneEach u c).length = N + N := by
  simp [oneEach]

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (t : Fin n) : (List.ofFn x).getD t false = x t := by
  simp

theorem sum_oneEach {N : ℕ} (cS : Fin (N + N) → ZMod 2) (u c : Fin N) :
    ∑ t : Fin (N + N), cS t * toZ ((oneEach u c).getD t false) = cS (Fin.castAdd N u) + cS (Fin.natAdd N c) := by
  have h1 : ∀ i : Fin N, (oneEach u c).getD (Fin.castAdd N i : ℕ) false = decide (i = u) := fun i => by
    rw [oneEach, List.getD_append _ _ _ _ (by simp)]; simp
  rw [Fin.sum_univ_add]
  simp only [h1]
  simp [oneEach, toZ]

theorem gate_mem (C : Circuit) (g : Gate) (hg : g ∈ C.gates) : ∃ j < C.gates.length, gateAt C j = g := by
  obtain ⟨j, hj, e⟩ := List.mem_iff_getElem.mp hg
  exact ⟨j, hj, by rw [smGateAt C j hj]; exact e⟩

theorem card_nl (C : Circuit) :
    (Finset.univ.filter (fun j : Fin C.gates.length => nlB (gateAt C j) = true)).card = C.gates.countP nlB := by
  conv_rhs => rw [← List.ofFn_getElem (xs := C.gates)]
  rw [List.countP_ofFn]
  exact congrArg Finset.card (Finset.filter_congr (fun j _ => by rw [smGateAt C j j.isLt]))

theorem toZ_xor (a b : Bool) : toZ (xor a b) = toZ a + toZ b := by
  cases a <;> cases b <;> decide

theorem toZ_inj {a b : Bool} (h : toZ a = toZ b) : a = b := by
  revert h
  cases a <;> cases b <;> decide

end ModS


-- module C: the row condition makes f bent
theorem mc_chi_add : ∀ a b : ZMod 2, chi (a + b) = chi a * chi b := by decide
theorem mc_chi_ne : ∀ a : ZMod 2, chi a ≠ 0 := by decide
theorem mc_chi_pow2 : ∀ a : ZMod 2, chi a ^ 2 = 1 := by decide
theorem mc_chi_four : ∀ a b : ZMod 2, chi a * chi b * (chi a * chi b) = 1 := by decide
theorem mc_chi_row : ∀ a b c d e : ZMod 2,
    chi ((a + b + c) + (d + b + e)) = chi (a + d) * (chi c * chi e) := by decide
theorem mc_zz : ∀ a : ZMod 2, a + a = 0 := by decide

theorem walsh_sq_of_rows {ι R K : Type} [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] [Fintype K]
    (x : R → (ι → ZMod 2)) (hx : Function.Bijective x) (y : K → (ι → ZMod 2))
    (f : (ι → ZMod 2) → ZMod 2) (r : R → ZMod 2) (s : K → ZMod 2)
    (hrows : ∀ u u' : R, u ≠ u' → ∑ c : K, chi ((r u + s c + f (x u + y c)) + (r u' + s c + f (x u' + y c))) = 0)
    (hK : 0 < Fintype.card K) (w : ι → ZMod 2) : walsh f w ^ 2 = 2 ^ Fintype.card ι := by
  have horth : ∀ u u' : R, u ≠ u' → ∑ c : K, chi (f (x u + y c)) * chi (f (x u' + y c)) = 0 := by
    intro u u' h
    have h1 := hrows u u' h
    simp only [mc_chi_row] at h1
    rw [← Finset.mul_sum] at h1
    exact (mul_eq_zero.mp h1).resolve_left (mc_chi_ne _)
  have hT : ∀ c : K, ∑ u : R, chi (∑ i, w i * x u i) * chi (f (x u + y c)) =
      chi (∑ i, w i * y c i) * walsh f w := by
    intro c
    have hyy : y c + y c = 0 := funext fun i => mc_zz (y c i)
    have e1 : ∑ u : R, chi (∑ i, w i * x u i) * chi (f (x u + y c)) =
        ∑ d : ι → ZMod 2, chi (∑ i, w i * d i) * chi (f (d + y c)) :=
      hx.sum_comp (fun d => chi (∑ i, w i * d i) * chi (f (d + y c)))
    have e2 : ∑ d : ι → ZMod 2, chi (∑ i, w i * d i) * chi (f (d + y c)) =
        ∑ d : ι → ZMod 2, chi (∑ i, w i * (d + y c) i) * chi (f (d + y c + y c)) :=
      ((AddGroup.addRight_bijective (y c)).sum_comp
        (fun d => chi (∑ i, w i * d i) * chi (f (d + y c)))).symm
    rw [e1, e2, walsh, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [add_assoc, hyy, add_zero]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, mc_chi_add]
    ring
  have hu : ∀ u : R, ∑ c : K, ∑ u' : R, chi (∑ i, w i * x u i) * chi (f (x u + y c)) *
      (chi (∑ i, w i * x u' i) * chi (f (x u' + y c))) = Fintype.card K := by
    intro u
    have hz : ∀ u' : R, u' ≠ u → ∑ c : K, chi (∑ i, w i * x u i) * chi (f (x u + y c)) *
        (chi (∑ i, w i * x u' i) * chi (f (x u' + y c))) = 0 := by
      intro u' hu'
      have h2 : ∀ c : K, chi (∑ i, w i * x u i) * chi (f (x u + y c)) *
          (chi (∑ i, w i * x u' i) * chi (f (x u' + y c))) =
          chi (∑ i, w i * x u i) * chi (∑ i, w i * x u' i) *
            (chi (f (x u + y c)) * chi (f (x u' + y c))) :=
        fun c => by ring
      rw [Finset.sum_congr rfl (fun c _ => h2 c), ← Finset.mul_sum, horth u u' (Ne.symm hu'), mul_zero]
    rw [Finset.sum_comm, Fintype.sum_eq_single u hz]
    rw [Finset.sum_congr rfl (fun c _ => mc_chi_four (∑ i, w i * x u i) (f (x u + y c)))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hB : ∑ c : K, (∑ u : R, chi (∑ i, w i * x u i) * chi (f (x u + y c))) ^ 2 =
      (Fintype.card R : ℤ) * Fintype.card K := by
    simp only [sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun u _ => hu u)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hA : ∑ c : K, (∑ u : R, chi (∑ i, w i * x u i) * chi (f (x u + y c))) ^ 2 =
      (Fintype.card K : ℤ) * walsh f w ^ 2 := by
    simp only [hT, mul_pow, mc_chi_pow2, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hR : Fintype.card R = 2 ^ Fintype.card ι := by
    rw [Fintype.card_of_bijective hx, Fintype.card_fun, ZMod.card]
  have hKz : (0 : ℤ) < Fintype.card K := by exact_mod_cast hK
  have key : (Fintype.card K : ℤ) * walsh f w ^ 2 = (Fintype.card K : ℤ) * 2 ^ Fintype.card ι := by
    rw [← hA, hB, hR]
    push_cast
    ring
  exact mul_left_cancel₀ hKz.ne' key


-- Module B: the bent-chain lemma (all names start with mb).

theorem mbchi_add : ∀ a b : ZMod 2, chi (a + b) = chi a * chi b := by decide

theorem mbchi_sq : ∀ a : ZMod 2, chi a ^ 2 = 1 := by decide

theorem mbchi_one : ∀ a : ZMod 2, chi (a + 1) = - chi a := by decide

theorem mbtwo : ∀ a : ZMod 2, a + a = 0 := by decide

theorem mbzo : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

def mbg (a b x y : ZMod 2) : ℤ := chi (x * y + a * x + b * y)

theorem mbg4 : ∀ a b x y : ZMod 2, mbg a b (x + 0) (y + 0) + mbg a b (x + 1) (y + 0) +
    mbg a b (x + 0) (y + 1) + mbg a b (x + 1) (y + 1) = 2 * chi (a * b) := by decide

theorem mbsq (X Y c : ℤ) (h : 2 * X = c * Y) (hc : c ^ 2 = 1) : 4 * X ^ 2 = Y ^ 2 := by
  linear_combination (2 * X + c * Y) * h + Y ^ 2 * hc

theorem mbpow (X : ℤ) (n : ℕ) (h : X ^ 2 = 2 ^ n) (h0 : X = 0) : False := by
  rw [h0] at h
  have h2 : (0 : ℤ) < 2 ^ n := by positivity
  rw [← h] at h2
  norm_num at h2

def mbsg {ι : Type} [DecidableEq ι] (σ : ι) (x : ZMod 2) (i : ι) : ZMod 2 := if i = σ then x else 0

theorem mbsg_same {ι : Type} [DecidableEq ι] (σ : ι) (x : ZMod 2) : mbsg σ x σ = x := by simp [mbsg]

theorem mbsg_ne {ι : Type} [DecidableEq ι] {σ i : ι} (h : i ≠ σ) (x : ZMod 2) : mbsg σ x i = 0 := by
  simp [mbsg, h]

theorem mbdot_add {ι : Type} [Fintype ι] (w d e : ι → ZMod 2) :
    ∑ i, w i * (d + e) i = ∑ i, w i * d i + ∑ i, w i * e i := by
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem mbdotL_add {ι : Type} [Fintype ι] (u v e : ι → ZMod 2) :
    ∑ i, (u + v) i * e i = ∑ i, u i * e i + ∑ i, v i * e i := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem mbdot_sg {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ZMod 2) (σ : ι) (x : ZMod 2) :
    ∑ i, w i * mbsg σ x i = w σ * x := by simp [mbsg, mul_ite]

theorem mbdotL_sg {ι : Type} [Fintype ι] [DecidableEq ι] (x : ZMod 2) (σ : ι) (e : ι → ZMod 2) :
    ∑ i, mbsg σ x i * e i = x * e σ := by simp [mbsg, ite_mul]

theorem mbev0 {ι : Type} [DecidableEq ι] (A0 A1 : ι) (hne : A0 ≠ A1) (x : ι → ZMod 2) (s t : ZMod 2) :
    (x + mbsg A0 s + mbsg A1 t) A0 = x A0 + s := by simp [mbsg, hne]

theorem mbev1 {ι : Type} [DecidableEq ι] (A0 A1 : ι) (hne : A0 ≠ A1) (x : ι → ZMod 2) (s t : ZMod 2) :
    (x + mbsg A0 s + mbsg A1 t) A1 = x A1 + t := by simp [mbsg, hne.symm]

theorem mbevo {ι : Type} [DecidableEq ι] (A0 A1 : ι) (x : ι → ZMod 2) (s t : ZMod 2) (i : ι)
    (h0 : i ≠ A0) (h1 : i ≠ A1) : (x + mbsg A0 s + mbsg A1 t) i = x i := by simp [mbsg, h0, h1]

theorem mbshinv {ι : Type} [DecidableEq ι] (A0 A1 : ι) (x0 y0 : ZMod 2) :
    Function.Involutive (fun e : ι → ZMod 2 => e + mbsg A0 x0 + mbsg A1 y0) := by
  intro e
  funext i
  simp only [Pi.add_apply]
  linear_combination mbtwo (mbsg A0 x0 i) + mbtwo (mbsg A1 y0 i)

-- (K1) F ignores slot σ, w σ = 1: zero coefficient
theorem mbK1 {ι : Type} [Fintype ι] [DecidableEq ι] (F : (ι → ZMod 2) → ZMod 2) (σ τ : ι)
    (hF : ∀ d, F (d + mbsg σ 1 + mbsg τ 0) = F d) (w : ι → ZMod 2) (hw : w σ = 1) : walsh F w = 0 := by
  have h : walsh F w = - walsh F w := by
    unfold walsh
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_bijective _ (mbshinv σ τ 1 0).bijective _ _ fun d => ?_
    rw [hF, mbdot_add, mbdot_add, mbdot_sg, mbdot_sg, hw, mul_zero, add_zero, mul_one, ← add_assoc,
      mbchi_one, neg_neg]
  linarith

-- (K2) peeling the gate on the slots A0 A1
theorem mbK2 {ι : Type} [Fintype ι] [DecidableEq ι] (A0 A1 : ι) (hne : A0 ≠ A1)
    (F : (ι → ZMod 2) → ZMod 2) {L M R T : (ι → ZMod 2) → ZMod 2}
    (hL : ∀ e s t, L (e + mbsg A0 s + mbsg A1 t) = L e) (hM : ∀ e s t, M (e + mbsg A0 s + mbsg A1 t) = M e)
    (hR : ∀ e s t, R (e + mbsg A0 s + mbsg A1 t) = R e)
    (hF : ∀ d, F d = (d A0 + L d) * (d A1 + M d) + R d) (a b : ZMod 2) (w' : ι → ZMod 2)
    (h0 : w' A0 = 0) (h1 : w' A1 = 0) (hT : ∀ d, R d + a * L d + b * M d = T d) :
    4 * walsh F (w' + mbsg A0 a + mbsg A1 b) ^ 2 = walsh T w' ^ 2 := by
  have dsh : ∀ (x : ι → ZMod 2) (s t : ZMod 2),
      ∑ i, w' i * (x + mbsg A0 s + mbsg A1 t) i = ∑ i, w' i * x i := fun x s t => by
    simp only [mbdot_add, mbdot_sg, h0, h1, zero_mul, add_zero]
  have inv : Function.Involutive (fun e : ι → ZMod 2 => e + mbsg A0 (L e) + mbsg A1 (M e)) := by
    intro e
    simp only [hL, hM]
    funext i
    simp only [Pi.add_apply]
    linear_combination mbtwo (mbsg A0 (L e) i) + mbtwo (mbsg A1 (M e) i)
  have hsh : ∀ x0 y0 : ZMod 2, ∑ e, chi (T e + ∑ i, w' i * e i) * mbg a b (e A0 + x0) (e A1 + y0) =
      walsh F (w' + mbsg A0 a + mbsg A1 b) := fun x0 y0 =>
    Fintype.sum_bijective _ (inv.bijective.comp (mbshinv A0 A1 x0 y0).bijective) _ _ fun e => by
      simp only [Function.comp_apply, ← hT, ← mbchi_add, mbg, hF, mbdotL_add, mbdotL_sg,
        mbev0 A0 A1 hne, mbev1 A0 A1 hne, dsh, hL, hM, hR]
      congr 1
      linear_combination (-(e A1 + y0 + M e + M e)) * mbtwo (L e) - (e A0 + x0) * mbtwo (M e)
  have h4 := Fintype.sum_congr _ _ fun e =>
    congrArg (fun t => chi (T e + ∑ i, w' i * e i) * t) (mbg4 a b (e A0) (e A1))
  simp only [mul_add, Finset.sum_add_distrib, hsh, ← Finset.sum_mul] at h4
  exact mbsq _ _ _ (by unfold walsh at h4 ⊢; linarith) (mbchi_sq (a * b))

theorem mbne_slot {J : Type} (i : J × Fin 2) (a : J) (k : Fin 2) (h : i.1 ≠ a) : i ≠ (a, k) :=
  fun he => h (congrArg Prod.fst he)

theorem mbslot_ne {J : Type} (a : J) : ((a, 0) : J × Fin 2) ≠ (a, 1) := by simp

-- the chain, and the sums beta + sum mu j A j
abbrev mbok {J : Type} [Fintype J] [LinearOrder J] (A : J → (J × Fin 2 → ZMod 2) → ZMod 2)
    (c0 c1 : J → J → ZMod 2) (p q r : J → ZMod 2) : Prop :=
  (∀ j j', c0 j j' ≠ 0 ∨ c1 j j' ≠ 0 → j' < j) ∧ ∀ j d, A j d =
    (d (j, 0) + p j + ∑ j', c0 j j' * A j' d) * (d (j, 1) + q j + ∑ j', c1 j j' * A j' d) + r j

def mbG {J : Type} [Fintype J] (A : J → (J × Fin 2 → ZMod 2) → ZMod 2) (μ : J → ZMod 2)
    (β : ZMod 2) (d : J × Fin 2 → ZMod 2) : ZMod 2 := β + ∑ j, μ j * A j d

-- (dep) gates below a read only slots below a
theorem mbdep {J : Type} [Fintype J] [LinearOrder J] {A : J → (J × Fin 2 → ZMod 2) → ZMod 2}
    {c0 c1 : J → J → ZMod 2} {p q r : J → ZMod 2} (h : mbok A c0 c1 p q r) (a : J) :
    ∀ μ : J → ZMod 2, (∀ j, μ j ≠ 0 → j < a) → ∀ d e : J × Fin 2 → ZMod 2,
      (∀ i : J × Fin 2, i.1 < a → d i = e i) → ∑ j, μ j * A j d = ∑ j, μ j * A j e := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    intro μ hμ d e hde
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h0 : μ j = 0
    · rw [h0, zero_mul, zero_mul]
    · have hj := hμ j h0
      have hd : ∀ i : J × Fin 2, i.1 < j → d i = e i := fun i hi => hde i (lt_trans hi hj)
      rw [h.2 j d, h.2 j e, hde (j, 0) hj, hde (j, 1) hj,
        ih j hj (c0 j) (fun j' h' => h.1 j j' (Or.inl h')) d e hd,
        ih j hj (c1 j) (fun j' h' => h.1 j j' (Or.inr h')) d e hd]

theorem mbign {J : Type} [Fintype J] [LinearOrder J] {A : J → (J × Fin 2 → ZMod 2) → ZMod 2}
    {c0 c1 : J → J → ZMod 2} {p q r : J → ZMod 2} (h : mbok A c0 c1 p q r) (μ : J → ZMod 2)
    (β : ZMod 2) (a : J) (hμ : ∀ j, μ j ≠ 0 → j < a) (e : J × Fin 2 → ZMod 2) (s t : ZMod 2) :
    mbG A μ β (e + mbsg (a, 0) s + mbsg (a, 1) t) = mbG A μ β e :=
  congrArg (fun x => β + x) (mbdep h a μ hμ _ e fun i hi =>
    mbevo _ _ e s t i (mbne_slot i a 0 (ne_of_lt hi)) (mbne_slot i a 1 (ne_of_lt hi)))

theorem mblin {J : Type} [Fintype J] (A : J → (J × Fin 2 → ZMod 2) → ZMod 2) (u v z : J → ZMod 2)
    (k m n s t : ZMod 2) (d : J × Fin 2 → ZMod 2) :
    mbG A u k d + s * mbG A v m d + t * mbG A z n d =
      mbG A (fun j => u j + s * v j + t * z j) (k + s * m + t * n) d := by
  simp only [mbG, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  ring

theorem mbsplit {J X : Type} [Fintype J] [DecidableEq J] (μ : J → ZMod 2)
    (A : J → X → ZMod 2) (d : X) (a : J) (ha : μ a = 1) :
    ∑ j, μ j * A j d = A a d + ∑ j, (if j = a then 0 else μ j) * A j d := by
  have h := Fintype.sum_ite_eq' a fun j => A j d
  rw [← h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by by_cases hj : j = a <;> simp [hj, ha]

-- (Ind) induction over downward closed S
theorem mbind {J : Type} [Fintype J] [LinearOrder J] {A : J → (J × Fin 2 → ZMod 2) → ZMod 2}
    {c0 c1 : J → J → ZMod 2} {p q r : J → ZMod 2} (h : mbok A c0 c1 p q r) (S : Finset J) :
    (∀ x ∈ S, ∀ y, y < x → y ∈ S) → ∀ (μ : J → ZMod 2) (β : ZMod 2), (∀ j, j ∉ S → μ j = 0) →
    (∀ w : J × Fin 2 → ZMod 2, (∀ i : J × Fin 2, i.1 ∉ S → w i = 0) →
      walsh (mbG A μ β) w ^ 2 = 2 ^ (4 * Fintype.card J - 2 * S.card)) →
    ∀ j ∈ S, μ j = 1 ∧ ∀ j', c0 j j' = 0 ∧ c1 j j' = 0 := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a S hlt ih =>
    intro hdc μ β hμ hw
    have haS : a ∉ S := fun h' => lt_irrefl a (hlt a h')
    have hK := Finset.card_lt_univ_of_notMem haS
    have hmem : ∀ j, j < a → j ∈ S := fun j hj =>
      (Finset.mem_insert.mp (hdc a (Finset.mem_insert_self a S) j hj)).resolve_left (ne_of_lt hj)
    have hc : ∀ j, j ∉ S → c0 a j = 0 ∧ c1 a j = 0 := fun j hj => by
      by_contra hn
      exact hj (hmem j (h.1 a j (not_and_or.mp hn)))
    have hμ0 : ∀ j, j ∉ S → (if j = a then 0 else μ j) = 0 := fun j hj => by
      by_cases e : j = a <;> simp [e, hj, hμ j]
    have hlow0 : ∀ j, (if j = a then 0 else μ j) ≠ 0 → j < a := fun j hj =>
      hlt j (Classical.byContradiction fun hn => hj (hμ0 j hn))
    have hμa : μ a = 1 := (mbzo (μ a)).resolve_left fun h0 => mbpow _ _
      (hw (mbsg (a, 0) 1) fun i hi => mbsg_ne (by rintro rfl; simp at hi) 1)
      (mbK1 (mbG A μ β) (a, 0) (a, 1) (fun d => mbign h μ β a (fun j hj =>
        hlow0 j (by rwa [ite_eq_right fun e => hj (by rw [e]; exact h0)])) d 1 0) _ (mbsg_same _ _))
    have key : ∀ ωa ωb : ZMod 2, ∀ j ∈ S,
        (if j = a then 0 else μ j) + ωa * c0 a j + ωb * c1 a j = 1 ∧ ∀ j', c0 j j' = 0 ∧ c1 j j' = 0 :=
      fun ωa ωb => ih (fun x hx y hy => hmem y (lt_trans hy (hlt x hx))) _ (r a + β + ωa * p a + ωb * q a)
        (fun j hj => by simp [hμ0 j hj, hc j hj]) fun w' hw' => by
        rw [← mbK2 (a, 0) (a, 1) (mbslot_ne a) (mbG A μ β)
          (mbign h (c0 a) (p a) a fun j e => h.1 a j (Or.inl e))
          (mbign h (c1 a) (q a) a fun j e => h.1 a j (Or.inr e)) (mbign h _ (r a + β) a hlow0)
          (fun d => by
            simp only [mbG]
            rw [mbsplit μ A d a hμa, h.2 a d]
            ring) ωa ωb w' (hw' (a, 0) haS) (hw' (a, 1) haS) (mblin A _ _ _ _ _ _ ωa ωb),
          hw (w' + mbsg (a, 0) ωa + mbsg (a, 1) ωb) (fun i hi => by
            simp only [Finset.mem_insert, not_or] at hi
            rw [mbevo _ _ w' ωa ωb i (mbne_slot i a 0 hi.1) (mbne_slot i a 1 hi.1), hw' i hi.2]),
          Finset.card_insert_of_notMem haS,
          show 4 * Fintype.card J - 2 * S.card = 4 * Fintype.card J - 2 * (S.card + 1) + 2 by omega,
          pow_add]
        ring
    intro j hj
    rcases Finset.mem_insert.mp hj with e | hjS
    · rw [e]
      refine ⟨hμa, fun j' => ?_⟩
      by_cases hj' : j' ∈ S
      · exact ⟨by linear_combination (key 1 0 j' hj').1 - (key 0 0 j' hj').1,
          by linear_combination (key 0 1 j' hj').1 - (key 0 0 j' hj').1⟩
      · exact hc j' hj'
    · simpa [show j ≠ a by rintro rfl; exact haS hjS] using key 0 0 j hjS

theorem chain_parallel {J : Type} [Fintype J] [LinearOrder J]
    (A : J → (J × Fin 2 → ZMod 2) → ZMod 2) (c0 c1 : J → J → ZMod 2) (p q r : J → ZMod 2)
    (hsupp : ∀ j j', c0 j j' ≠ 0 ∨ c1 j j' ≠ 0 → j' < j)
    (hrec : ∀ j d, A j d = (d (j, 0) + p j + ∑ j', c0 j j' * A j' d) * (d (j, 1) + q j + ∑ j', c1 j j' * A j' d) + r j)
    (μ : J → ZMod 2) (β : ZMod 2)
    (hbent : ∀ w : J × Fin 2 → ZMod 2, walsh (fun d => β + ∑ j, μ j * A j d) w ^ 2 = 2 ^ (2 * Fintype.card J)) :
    ∀ j j', c0 j j' = 0 ∧ c1 j j' = 0 := fun j j' =>
  (mbind (A := A) ⟨hsupp, hrec⟩ Finset.univ (fun _ _ y _ => Finset.mem_univ y) μ β
    (fun k hk => absurd (Finset.mem_univ k) hk) (fun w _ => by
      rw [Finset.card_univ, show 4 * Fintype.card J - 2 * Fintype.card J = 2 * Fintype.card J by omega]
      exact hbent w) j (Finset.mem_univ j)).2 j'


section ModG

open PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

-- module G: labels, bijection, transport and the final contradiction
abbrev mg_NL (C : Circuit) : Type := {j : Fin C.gates.length // nlB (gateAt C j) = true}

def mg_sel (a b : ℕ) (e : Fin 2) : ℕ := if e = 0 then a else b

theorem mg_sel0 (a b : ℕ) : mg_sel a b 0 = a := rfl

theorem mg_sel1 (a b : ℕ) : mg_sel a b 1 = b := rfl

theorem mg_zero_or_one : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide

theorem mg_cancel : ∀ a b c x y : ZMod 2, a + (x + c) + b + (a + (y + c) + b) = x + y := by decide

theorem mg_toZ_false : toZ false = 0 := by decide

theorem mg_eq_of_add : ∀ a b : Bool, toZ a + toZ b = 0 → a = b := by decide

theorem mg_ne_of_add : ∀ a b : Bool, toZ a + toZ b = 1 → a ≠ b := by decide

theorem mg_chi_bool : ∀ a b : Bool, chi (toZ a + toZ b) = 1 - 2 * (if a ≠ b then 1 else 0) := by decide

theorem mg_chi_rows {N : ℕ} (G : Fin N → Fin N → Bool) (u u' : Fin N)
    (h : 2 * ((Finset.univ : Finset (Fin N)).filter (fun c => G u c ≠ G u' c)).card = N) :
    ∑ c : Fin N, chi (toZ (G u c) + toZ (G u' c)) = 0 := by
  rw [Finset.sum_congr rfl (fun c _ => mg_chi_bool (G u c) (G u' c)), Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_boole, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  omega

theorem mg_sumJ (C : Circuit) (a v : ℕ → ZMod 2) (ha : ∀ j, a j ≠ 0 → nlB (gateAt C j) = true) :
    ∑ j ∈ Finset.range C.gates.length, a j * v j = ∑ j : mg_NL C, a j.1.1 * v j.1.1 := by
  rw [Finset.sum_range]
  have h1 : ∑ j : Fin C.gates.length, a j * v j =
      ∑ j ∈ Finset.univ.filter (fun j : Fin C.gates.length => nlB (gateAt C j) = true), a j * v j :=
    (Finset.sum_filter_of_ne (f := fun j : Fin C.gates.length => a j * v j)
      (fun (j : Fin C.gates.length) _ h => ha j (left_ne_zero_of_mul h))).symm
  rw [h1]
  exact Finset.sum_subtype _ (fun j => by simp) (fun j : Fin C.gates.length => a j * v j)

theorem mg_rb {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j a b : ℕ} (hj : j < C.gates.length)
    (h : (gateAt C j).inputs = [a, b]) : a < n + j ∧ b < n + j :=
  ⟨hRB j hj a (by rw [h]; simp), hRB j hj b (by rw [h]; simp)⟩

theorem mg_main (s N : ℕ) (hN : N = 2 ^ (2 * s)) (G : Fin N → Fin N → Bool)
    (hHad : ∀ u v : Fin N, u ≠ v →
      2 * ((Finset.univ : Finset (Fin N)).filter (fun c => G u c ≠ G v c)).card = N)
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2) (hRB : ReadsBack (N + N) C)
    (hRep : PEqualNP.Represents.Represents G C) (hcount : C.gates.countP nlB ≤ s)
    (g : Gate) (hg : g ∈ C.gates) (hnl : nlB g = true) (w : ℕ) (hw : w ∈ g.inputs)
    (x y : Fin (N + N) → Bool) :
    xor (val C (List.ofFn x) w) (val C (List.ofFn y) w) =
      xor (val C (List.ofFn (fun i => xor (x i) (y i))) w) (val C (List.ofFn (fun _ : Fin (N + N) => false)) w) := by
  have hNpos : 0 < N := by rw [hN]; exact Nat.two_pow_pos _
  choose b cS cT hsupp hrep using fun i => rep_exists C (N + N) hRB hfan i
  choose i0 i1 hin p q r hev using fun j : mg_NL C => nl_normal (gateAt C j.1) j.2
  obtain ⟨La, hLa⟩ : ∃ La : Fin N → (mg_NL C × Fin 2 → ZMod 2),
      ∀ u σ, La u σ = cS (mg_sel (i0 σ.1) (i1 σ.1) σ.2) (Fin.castAdd N u) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨Lb, hLb⟩ : ∃ Lb : Fin N → (mg_NL C × Fin 2 → ZMod 2),
      ∀ c σ, Lb c σ = cS (mg_sel (i0 σ.1) (i1 σ.1) σ.2) (Fin.natAdd N c) := ⟨_, fun _ _ => rfl⟩
  -- a nonlinear gate's value depends only on the slot labels
  have hdep : ∀ u c u' c' : Fin N, La u + Lb c = La u' + Lb c' → ∀ k : ℕ, ∀ jj : mg_NL C, jj.1.1 < k →
      val C (oneEach u c) (N + N + jj.1.1) = val C (oneEach u' c') (N + N + jj.1.1) := by
    intro u c u' c' hL k
    induction k with
    | zero => intro jj h; exact absurd h (Nat.not_lt_zero _)
    | succ k IH =>
      intro jj hk
      have key : ∀ i, i < N + N + jj.1.1 → cS i (Fin.castAdd N u) + cS i (Fin.natAdd N c) =
          cS i (Fin.castAdd N u') + cS i (Fin.natAdd N c') → val C (oneEach u c) i = val C (oneEach u' c') i := by
        intro i hi hraw
        apply toZ_inj
        rw [hrep i _ (oneEach_length u c), hrep i _ (oneEach_length u' c'), sum_oneEach, sum_oneEach, hraw]
        congr 1
        refine Finset.sum_congr rfl fun j' _ => ?_
        by_cases h0 : cT i j' = 0
        · simp only [h0, zero_mul]
        · obtain ⟨h1, h2, h3⟩ := hsupp i j' h0
          rw [show val C (oneEach u c) (N + N + j') = val C (oneEach u' c') (N + N + j') from
            IH ⟨⟨j', h1⟩, h2⟩ (show j' < k by omega)]
      have hr := fun e : Fin 2 => congrFun hL (jj, e)
      simp only [Pi.add_apply, hLa, hLb] at hr
      obtain ⟨r0, r1⟩ := mg_rb hRB jj.1.2 (hin jj)
      rw [val_gate C (N + N) hRB _ (oneEach_length u c) _ jj.1.2,
        val_gate C (N + N) hRB _ (oneEach_length u' c') _ jj.1.2, hin jj]
      simp only [List.map_cons, List.map_nil, key _ r0 (hr 0), key _ r1 (hr 1)]
  have hout : ∀ u c : Fin N, toZ (G u c) = b C.output + (cS C.output (Fin.castAdd N u) +
      cS C.output (Fin.natAdd N c)) + ∑ j : mg_NL C, cT C.output j.1.1 * toZ (val C (oneEach u c) (N + N + j.1.1)) := by
    intro u c
    rw [← hRep u c]
    show toZ (val C (oneEach u c) C.output) = _
    rw [hrep C.output _ (oneEach_length u c), sum_oneEach, mg_sumJ C (cT C.output) _ (fun j h => (hsupp _ j h).2.1)]
  -- the row labels are injective, hence (counting) a bijection
  have hinj : Function.Injective La := by
    intro u u' huu
    by_cases hne : u = u'
    · exact hne
    exfalso
    have hc : ∀ c, toZ (G u c) + toZ (G u' c) = cS C.output (Fin.castAdd N u) + cS C.output (Fin.castAdd N u') := by
      intro c
      rw [hout u c, hout u' c]
      simp only [fun j : mg_NL C => hdep u c u' c (by rw [huu]) _ j (Nat.lt_succ_self _)]
      exact mg_cancel _ _ _ _ _
    have hH := hHad u u' hne
    rcases mg_zero_or_one (cS C.output (Fin.castAdd N u) + cS C.output (Fin.castAdd N u')) with hk | hk
    · rw [Finset.filter_false_of_mem (p := fun c => G u c ≠ G u' c)
        (fun c _ h => h (mg_eq_of_add _ _ (by rw [hc c, hk]))), Finset.card_empty] at hH
      omega
    · rw [Finset.filter_true_of_mem (p := fun c => G u c ≠ G u' c)
        (fun c _ => mg_ne_of_add _ _ (by rw [hc c, hk])), Finset.card_univ, Fintype.card_fin] at hH
      omega
  have hcardJ : Fintype.card (mg_NL C) ≤ s := by rw [Fintype.card_subtype, card_nl]; exact hcount
  have hcardF : Fintype.card (mg_NL C × Fin 2 → ZMod 2) = 2 ^ (2 * Fintype.card (mg_NL C)) := by
    rw [Fintype.card_fun, Fintype.card_prod, ZMod.card, Fintype.card_fin, Nat.mul_comm]
  have hle := Fintype.card_le_of_injective La hinj
  rw [Fintype.card_fin, hcardF] at hle
  have hge : 2 ^ (2 * Fintype.card (mg_NL C)) ≤ N := by
    rw [hN]; exact Nat.pow_le_pow_right (by omega) (by omega)
  have hbij : Function.Bijective La := (Fintype.bijective_iff_injective_and_card La).mpr
    ⟨hinj, by rw [Fintype.card_fin, hcardF]; exact le_antisymm hle hge⟩
  -- transport the nonlinear gates to label space
  choose inv hinv using hbij.2
  have c00 : Fin N := ⟨0, hNpos⟩
  obtain ⟨Ah, hAh⟩ : ∃ Ah : mg_NL C → (mg_NL C × Fin 2 → ZMod 2) → ZMod 2,
      ∀ j u c, toZ (val C (oneEach u c) (N + N + j.1.1)) = Ah j (La u + Lb c) :=
    ⟨fun j d => toZ (val C (oneEach (inv (d - Lb c00)) c00) (N + N + j.1.1)), fun j u c =>
      congrArg toZ (hdep u c _ c00 (by rw [hinv, sub_add_cancel]) _ j (Nat.lt_succ_self _))⟩
  have hop : ∀ (j : mg_NL C) (e : Fin 2) (u c : Fin N), toZ (val C (oneEach u c) (mg_sel (i0 j) (i1 j) e)) =
      b (mg_sel (i0 j) (i1 j) e) + (La u + Lb c) (j, e) +
        ∑ j' : mg_NL C, cT (mg_sel (i0 j) (i1 j) e) j'.1.1 * Ah j' (La u + Lb c) := by
    intro j e u c
    rw [hrep _ _ (oneEach_length u c), sum_oneEach, mg_sumJ C (cT _) _ (fun j' h => (hsupp _ j' h).2.1)]
    simp only [Pi.add_apply, hLa, hLb, hAh]
  have hrec : ∀ (j : mg_NL C) d, Ah j d =
      (d (j, 0) + (b (i0 j) + p j) + ∑ j' : mg_NL C, cT (i0 j) j'.1.1 * Ah j' d) *
        (d (j, 1) + (b (i1 j) + q j) + ∑ j' : mg_NL C, cT (i1 j) j'.1.1 * Ah j' d) + r j := by
    intro j d
    obtain ⟨u, rfl⟩ : ∃ u, La u + Lb c00 = d := ⟨inv (d - Lb c00), by rw [hinv, sub_add_cancel]⟩
    rw [← hAh, val_gate C (N + N) hRB _ (oneEach_length u c00) _ j.1.2, hin j]
    simp only [List.map_cons, List.map_nil]
    have h0 := hop j 0 u c00
    have h1 := hop j 1 u c00
    rw [mg_sel0] at h0
    rw [mg_sel1] at h1
    rw [hev j, h0, h1]
    ring
  have hsuppB : ∀ j j' : mg_NL C, cT (i0 j) j'.1.1 ≠ 0 ∨ cT (i1 j) j'.1.1 ≠ 0 → j' < j := by
    intro j j' h
    obtain ⟨r0, r1⟩ := mg_rb hRB j.1.2 (hin j)
    have hlt : j'.1.1 < j.1.1 := by
      rcases h with h | h
      · have := (hsupp _ _ h).2.2; omega
      · have := (hsupp _ _ h).2.2; omega
    exact hlt
  -- the output function is bent ([C]), so no operand reads an earlier product ([B])
  have hG : ∀ u c : Fin N, toZ (G u c) = cS C.output (Fin.castAdd N u) + cS C.output (Fin.natAdd N c) +
      (b C.output + ∑ j : mg_NL C, cT C.output j.1.1 * Ah j (La u + Lb c)) := by
    intro u c
    rw [hout u c]
    simp only [hAh]
    ring
  have hB := chain_parallel Ah (fun j j' => cT (i0 j) j'.1.1) (fun j j' => cT (i1 j) j'.1.1)
    (fun j => b (i0 j) + p j) (fun j => b (i1 j) + q j) r hsuppB hrec
    (fun j => cT C.output j.1.1) (b C.output) (fun wv => by
      have hW := walsh_sq_of_rows La hbij Lb (fun d => b C.output + ∑ j : mg_NL C, cT C.output j.1.1 * Ah j d)
        (fun u => cS C.output (Fin.castAdd N u)) (fun c => cS C.output (Fin.natAdd N c))
        (fun u u' hne => by
          have h := mg_chi_rows G u u' (hHad u u' hne)
          simp only [hG] at h
          exact h)
        (by rw [Fintype.card_fin]; exact hNpos) wv
      rw [Fintype.card_prod, Fintype.card_fin, Nat.mul_comm] at hW
      convert hW using 3)
  -- so the operand w of g is affine in the raw inputs
  obtain ⟨jg, hjg, hgj⟩ := gate_mem C g hg
  obtain ⟨jj, hjj⟩ : ∃ jj : mg_NL C, jj.1.1 = jg := ⟨⟨⟨jg, hjg⟩, by rw [hgj]; exact hnl⟩, rfl⟩
  subst hjj
  have hwin : w ∈ [i0 jj, i1 jj] := by rw [← hin jj, hgj]; exact hw
  have hzero : ∀ j', cT w j' = 0 := by
    intro j'
    by_cases hne : cT w j' = 0
    · exact hne
    · exfalso
      obtain ⟨h1, h2, -⟩ := hsupp w j' hne
      have hBj := hB jj ⟨⟨j', h1⟩, h2⟩
      rcases List.mem_cons.mp hwin with h | h
      · rw [h] at hne; exact hne hBj.1
      · rw [List.mem_singleton.mp h] at hne; exact hne hBj.2
  have hWz : ∀ z : Fin (N + N) → Bool, toZ (val C (List.ofFn z) w) = b w + ∑ t, cS w t * toZ (z t) := by
    intro z
    rw [hrep w (List.ofFn z) List.length_ofFn]
    simp only [hzero, zero_mul, Finset.sum_const_zero, add_zero, getD_ofFn]
  apply toZ_inj
  rw [toZ_xor, toZ_xor, hWz, hWz, hWz, hWz]
  simp only [toZ_xor, mg_toZ_false, mul_add, mul_zero, Finset.sum_add_distrib, Finset.sum_const_zero, add_zero]
  ring

end ModG

end PEqualNP.Outside.L_meta_25665_aux

theorem PEqualNP.Outside.L_meta_25665 : ¬ (∃ s : ℕ, 0 < s ∧
  let k := 2 * s
  let N := 2 ^ k
  let dot := fun (x y : Fin N) =>
    ((Finset.univ : Finset (Fin k)).filter (fun i =>
      x.val.testBit i.val && y.val.testBit i.val)).card % 2 == 1
  let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
    (g.inputs.length == 2) &&
    xor (xor (g.op.eval [false,false]) (g.op.eval [false,true]))
        (xor (g.op.eval [true,false]) (g.op.eval [true,true]))
  ∃ G : Fin N → Fin N → Bool,
  (∀ u v : Fin N, u ≠ v →
    2 * ((Finset.univ : Finset (Fin N)).filter (fun c => G u c ≠ G v c)).card = N) ∧
  let represents := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C ∧
    PEqualNP.Represents.Represents G C
  ∃ C, represents C ∧ C.gates.countP nonlinear ≤ s ∧
    ∃ g ∈ C.gates, nonlinear g = true ∧ ∃ w ∈ g.inputs,
      let W := fun (x : Fin (N+N) → Bool) => (C.wires (List.ofFn x)).getD w false
      ∃ x y, xor (W x) (W y) ≠
        xor (W (fun i => xor (x i) (y i))) (W (fun _ => false))) := by
  intro h
  obtain ⟨s, -, h⟩ := h
  dsimp only at h
  obtain ⟨G, hHad, C, ⟨hfan, hRB, hRep⟩, hcount, g, hg, hnl, w, hw, x, y, hxy⟩ := h
  exact hxy (PEqualNP.Outside.L_meta_25665_aux.mg_main s _ rfl G hHad C hfan hRB hRep hcount g hg hnl w hw x y)
