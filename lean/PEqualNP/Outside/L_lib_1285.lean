import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1285_aux

open scoped Classical
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.NotBracket

section CircuitBasics

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_append_left {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type*} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_mem {α : Type*} (l : List α) (k : ℕ) (d : α) (hk : k < l.length) :
    l.getD k d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
  exact List.getElem_mem hk

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (wiresFrom gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    · exact getD_append_left _ _ k false hk
    · simp; omega

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma notCount_nil (o : ℕ) : notCount ⟨[], o⟩ = 0 := rfl

lemma notCount_append (gs1 gs2 : List Gate) (o : ℕ) :
    notCount ⟨gs1 ++ gs2, o⟩ = notCount ⟨gs1, 0⟩ + notCount ⟨gs2, 0⟩ := by
  simp [notCount, List.filter_append]

lemma notCount_cons (g : Gate) (gs : List Gate) (o : ℕ) :
    notCount ⟨g :: gs, o⟩ = (if g.op = GateOp.not then 1 else 0) + notCount ⟨gs, 0⟩ := by
  simp only [notCount, List.filter_cons]
  by_cases h : g.op = GateOp.not <;> simp [h] <;> omega

lemma fanInTwo_nil (o : ℕ) : FanInTwo ⟨[], o⟩ := by
  intro g hg; cases hg

lemma fanInTwo_append {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : FanInTwo ⟨gs1, 0⟩) (h2 : FanInTwo ⟨gs2, 0⟩) :
    FanInTwo ⟨gs1 ++ gs2, o⟩ := by
  intro g hg
  rcases List.mem_append.mp hg with hg1 | hg2
  · exact h1 g hg1
  · exact h2 g hg2

lemma readsBack_nil (m o : ℕ) : ReadsBack m ⟨[], o⟩ := by
  intro j hj; cases hj

lemma readsBack_append {m : ℕ} {gs1 gs2 : List Gate} {o : ℕ}
    (h1 : ReadsBack m ⟨gs1, 0⟩) (h2 : ReadsBack (m + gs1.length) ⟨gs2, 0⟩) :
    ReadsBack m ⟨gs1 ++ gs2, o⟩ := by
  intro j hj i hi
  rw [gateAt_eq_getElem _ j hj] at hi
  by_cases hj1 : j < gs1.length
  · have hget : (gs1 ++ gs2)[j] = gs1[j] := List.getElem_append_left hj1
    rw [hget] at hi
    have h1' := h1 j hj1
    rw [gateAt_eq_getElem _ j hj1] at h1'
    exact h1' i hi
  · have hj1' : gs1.length ≤ j := Nat.le_of_not_lt hj1
    have hj2 : j - gs1.length < gs2.length := by
      simp only [List.length_append] at hj
      omega
    have hget : (gs1 ++ gs2)[j] = gs2[j - gs1.length] := List.getElem_append_right hj1'
    rw [hget] at hi
    have h2' := h2 (j - gs1.length) hj2
    rw [gateAt_eq_getElem _ (j - gs1.length) hj2] at h2'
    have hlt := h2' i hi
    omega

def Extends (base : ℕ) (gs1 gs2 : List Gate) : Prop :=
  ∃ extra : List Gate, gs2 = gs1 ++ extra ∧ FanInTwo ⟨extra, 0⟩ ∧
    ReadsBack (base + gs1.length) ⟨extra, 0⟩

lemma Extends.refl (base : ℕ) (gs : List Gate) : Extends base gs gs :=
  ⟨[], by simp, fanInTwo_nil 0, readsBack_nil _ 0⟩

lemma Extends.trans {base : ℕ} {gs1 gs2 gs3 : List Gate}
    (h1 : Extends base gs1 gs2) (h2 : Extends base gs2 gs3) :
    Extends base gs1 gs3 := by
  rcases h1 with ⟨e1, rfl, hf1, hr1⟩
  rcases h2 with ⟨e2, rfl, hf2, hr2⟩
  refine ⟨e1 ++ e2, by rw [List.append_assoc], fanInTwo_append hf1 hf2, ?_⟩
  have hr2' : ReadsBack ((base + gs1.length) + e1.length) ⟨e2, 0⟩ := by
    simpa [List.length_append, Nat.add_assoc] using hr2
  exact readsBack_append hr1 hr2'

lemma Extends.length_le {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2) :
    gs1.length ≤ gs2.length := by
  rcases h with ⟨e, rfl, _, _⟩; simp

lemma Extends.wire_eq {base : ℕ} {gs1 gs2 : List Gate} (h : Extends base gs1 gs2)
    (w : List Bool) (hw : w.length = base) (i : ℕ) (hi : i < base + gs1.length) :
    (wiresFrom gs2 w).getD i false = (wiresFrom gs1 w).getD i false := by
  rcases h with ⟨e, rfl, _, _⟩
  rw [wiresFrom_append]
  exact wiresFrom_getD_lt e (wiresFrom gs1 w) i (by rw [wiresFrom_length, hw]; exact hi)

def emitAnd (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], base + gs.length)

def emitOr (base : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], base + gs.length)

def emitNot (base : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], base + gs.length)

def emitCopyGate (base : ℕ) (gs : List Gate) (wMap : List ℕ) (g : Gate) : List Gate × ℕ :=
  (gs ++ [⟨g.op, g.inputs.map (fun i => wMap.getD i 0)⟩], base + gs.length)

lemma emitAnd_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitAnd base gs a b
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false && (wiresFrom gs w).getD b false) := by
  dsimp only [emitAnd]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.and, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitOr_spec (base : ℕ) (gs : List Gate) (a b : ℕ)
    (ha : a < base + gs.length) (hb : b < base + gs.length) :
    let r := emitOr base gs a b
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        ((wiresFrom gs w).getD a false || (wiresFrom gs w).getD b false) := by
  dsimp only [emitOr]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.or, [a, b]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl <;> omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitNot_spec (base : ℕ) (gs : List Gate) (a : ℕ)
    (ha : a < base + gs.length) :
    let r := emitNot base gs a
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + 1 ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false = !((wiresFrom gs w).getD a false) := by
  dsimp only [emitNot]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨GateOp.not, [a]⟩], rfl, ?_, ?_⟩
    · intro g hg; simp only [List.mem_singleton] at hg; subst hg; simp
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_singleton] at hi
      subst hi; omega
  · rw [notCount_append]; simp [notCount]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, GateOp.eval]

lemma emitCopyGate_spec (base : ℕ) (gs : List Gate) (wMap : List ℕ) (g : Gate)
    (hfit : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < wMap.length)
    (hmap : ∀ w ∈ wMap, w < base + gs.length) :
    let r := emitCopyGate base gs wMap g
    Extends base gs r.1 ∧
    r.1.length = gs.length + 1 ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ + (if g.op = GateOp.not then 1 else 0) ∧
    ∀ (w : List Bool), w.length = base →
      (wiresFrom r.1 w).getD r.2 false =
        g.op.eval (g.inputs.map fun i => (wiresFrom gs w).getD (wMap.getD i 0) false) := by
  dsimp only [emitCopyGate]
  refine ⟨?_, by simp, by simp, ?_, ?_⟩
  · refine ⟨[⟨g.op, g.inputs.map (fun i => wMap.getD i 0)⟩], rfl, ?_, ?_⟩
    · intro g' hg'; simp only [List.mem_singleton] at hg'; subst hg'
      exact ⟨hfit.1, by simp [hfit.2]⟩
    · intro j hj i hi
      have hj0 : j = 0 := by simp at hj; omega
      subst hj0
      rw [gateAt_eq_getElem _ 0 hj] at hi
      simp only [List.getElem_singleton, List.mem_map] at hi
      rcases hi with ⟨k, hk, rfl⟩
      have hk' := hin k hk
      have := hmap _ (getD_mem wMap k 0 hk')
      omega
  · simp [notCount_append, notCount_cons, notCount_nil]
  · intro w hw
    rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
    have hlen : (wiresFrom gs w).length = base + gs.length := by rw [wiresFrom_length, hw]
    rw [getD_append_right _ _ (base + gs.length) false (by omega)]
    simp [hlen, List.map_map, Function.comp_def]

end CircuitBasics

section InputEncoding

noncomputable def bitsCls (w : ℕ) (x : Finset (Fin w)) : List Bool :=
  letI : ∀ P : Prop, Decidable P := Classical.propDecidable
  List.ofFn (fun i : Fin w => decide (i ∈ x))

noncomputable def dsVec {n : ℕ} (x : Finset (Fin n)) : List Bool :=
  bitsCls n x ++ [false, true]

noncomputable def csVec {n m : ℕ} (x : Finset (Fin n)) (z : Finset (Fin m)) : List Bool :=
  bitsCls n x ++ bitsCls m z ++ [false, true]

lemma bitsCls_length {w : ℕ} (x : Finset (Fin w)) : (bitsCls w x).length = w := by
  simp [bitsCls]

lemma dsVec_length {n : ℕ} (x : Finset (Fin n)) : (dsVec x).length = n + 2 := by
  simp [dsVec, bitsCls_length]

lemma csVec_length {n m : ℕ} (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (csVec x z).length = n + m + 2 := by
  simp [csVec, bitsCls_length]; omega

lemma bitsCls_getD {w : ℕ} (x : Finset (Fin w)) (i : Fin w) :
    (bitsCls w x).getD i.val false = @decide (i ∈ x) (Classical.propDecidable _) := by
  simp [bitsCls, List.getD_eq_getElem?_getD, i.isLt]

lemma dsVec_getD_lt {n : ℕ} (x : Finset (Fin n)) (i : Fin n) :
    (dsVec x).getD i.val false = @decide (i ∈ x) (Classical.propDecidable _) := by
  dsimp only [dsVec]
  rw [getD_append_left _ _ i.val false (by rw [bitsCls_length]; exact i.isLt), bitsCls_getD]

lemma dsVec_getD_false {n : ℕ} (x : Finset (Fin n)) :
    (dsVec x).getD n false = false := by
  dsimp only [dsVec]
  rw [getD_append_right _ _ n false (by rw [bitsCls_length]), bitsCls_length]
  simp

lemma dsVec_getD_true {n : ℕ} (x : Finset (Fin n)) :
    (dsVec x).getD (n + 1) false = true := by
  dsimp only [dsVec]
  rw [getD_append_right _ _ (n + 1) false (by rw [bitsCls_length]; omega), bitsCls_length]
  have hsub : n + 1 - n = 1 := by omega
  simp [hsub]

lemma csVec_getD_x {n m : ℕ} (x : Finset (Fin n)) (z : Finset (Fin m)) (i : Fin n) :
    (csVec x z).getD i.val false = @decide (i ∈ x) (Classical.propDecidable _) := by
  dsimp only [csVec]
  rw [getD_append_left _ _ i.val false (by simp [bitsCls_length]; omega),
      getD_append_left _ _ i.val false (by rw [bitsCls_length]; exact i.isLt), bitsCls_getD]

lemma csVec_getD_z {n m : ℕ} (x : Finset (Fin n)) (z : Finset (Fin m)) (j : Fin m) :
    (csVec x z).getD (n + j.val) false = @decide (j ∈ z) (Classical.propDecidable _) := by
  dsimp only [csVec]
  rw [getD_append_left _ _ (n + j.val) false (by simp [bitsCls_length, j.isLt]),
      getD_append_right _ _ (n + j.val) false (by rw [bitsCls_length]; omega),
      bitsCls_length]
  have hsub : n + j.val - n = j.val := by omega
  rw [hsub, bitsCls_getD]

lemma csVec_getD_false {n m : ℕ} (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (csVec x z).getD (n + m) false = false := by
  dsimp only [csVec]
  rw [getD_append_right _ _ (n + m) false (by simp [bitsCls_length])]
  simp [bitsCls_length]

lemma csVec_getD_true {n m : ℕ} (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (csVec x z).getD (n + m + 1) false = true := by
  dsimp only [csVec]
  rw [getD_append_right _ _ (n + m + 1) false (by simp [bitsCls_length])]
  have hlen : (bitsCls n x ++ bitsCls m z).length = n + m := by simp [bitsCls_length]
  rw [hlen]
  have hsub : n + m + 1 - (n + m) = 1 := by omega
  simp [hsub]

noncomputable def prefLen {m : ℕ} (z : Finset (Fin m)) : ℕ :=
  if h : ∃ j : Fin m, j ∉ z then
    ((Finset.univ.filter (fun j : Fin m => j ∉ z)).min'
      (by rcases h with ⟨j, hj⟩; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)).val
  else m

lemma prefLen_le {m : ℕ} (z : Finset (Fin m)) : prefLen z ≤ m := by
  dsimp only [prefLen]
  split_ifs with h
  · generalize_proofs hne
    exact le_of_lt (Finset.min' _ hne).isLt
  · exact le_refl m

lemma prefLen_eq_m_iff {m : ℕ} (z : Finset (Fin m)) : prefLen z = m ↔ z = Finset.univ := by
  dsimp only [prefLen]
  split_ifs with h
  · generalize_proofs hne
    constructor
    · intro heq; have := (Finset.min' _ hne).isLt; omega
    · intro hzu; rcases h with ⟨j, hj⟩; exact absurd (hzu ▸ Finset.mem_univ j) hj
  · push Not at h
    constructor
    · intro _; ext j; simp [h j]
    · intro _; rfl

lemma prefLen_eq_of_first_miss {m : ℕ} {z : Finset (Fin m)} {j : Fin m}
    (hprev : ∀ i : Fin m, i < j → i ∈ z) (hmiss : j ∉ z) :
    prefLen z = j.val := by
  have hex : ∃ k : Fin m, k ∉ z := ⟨j, hmiss⟩
  dsimp only [prefLen]
  rw [dif_pos hex]
  generalize_proofs hne
  have hmin_mem := Finset.min'_mem (Finset.univ.filter (fun k : Fin m => k ∉ z)) hne
  have hmin_miss : (Finset.univ.filter (fun k : Fin m => k ∉ z)).min' hne ∉ z :=
    (Finset.mem_filter.mp hmin_mem).2
  have hle1 : (Finset.univ.filter (fun k : Fin m => k ∉ z)).min' hne ≤ j :=
    Finset.min'_le _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hmiss⟩)
  have hle2 : j ≤ (Finset.univ.filter (fun k : Fin m => k ∉ z)).min' hne := by
    by_contra hlt
    exact hmin_miss (hprev _ (lt_of_not_ge hlt))
  exact congrArg Fin.val (le_antisymm hle1 hle2)

lemma le_prefLen_iff {m : ℕ} (z : Finset (Fin m)) (t : ℕ) (ht : t ≤ m) :
    t ≤ prefLen z ↔ ∀ i : Fin m, i.val < t → i ∈ z := by
  dsimp only [prefLen]
  split_ifs with h
  · generalize_proofs hne
    constructor
    · intro hle i hi
      by_contra hni
      have hmi : (Finset.univ.filter (fun k : Fin m => k ∉ z)).min' hne ≤ i :=
        Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hni⟩)
      have hmi_val : ((Finset.univ.filter (fun k : Fin m => k ∉ z)).min' hne).val ≤ i.val := hmi
      omega
    · intro hall
      by_contra hlt
      have hmin_mem := Finset.min'_mem (Finset.univ.filter (fun k : Fin m => k ∉ z)) hne
      have hmin_miss : (Finset.univ.filter (fun k : Fin m => k ∉ z)).min' hne ∉ z :=
        (Finset.mem_filter.mp hmin_mem).2
      exact hmin_miss (hall _ (by omega))
  · push Not at h
    exact ⟨fun _ i _ => h i, fun _ => ht⟩

end InputEncoding

section PrefixAndSim

def buildPrefixes (n m : ℕ) : ℕ → List Gate → List Gate × List ℕ
  | 0, gs => (gs, [n + m + 1])
  | k + 1, gs =>
    let r1 := buildPrefixes n m k gs
    let prev := r1.2.getD k (n + m + 1)
    let r2 := emitAnd (n + m + 2) r1.1 prev (n + k)
    (r2.1, r1.2 ++ [r2.2])

lemma buildPrefixes_spec (n m : ℕ) :
    ∀ k, k ≤ m → ∀ gs : List Gate,
      let r := buildPrefixes n m k gs
      Extends (n + m + 2) gs r.1 ∧
      r.1.length = gs.length + k ∧
      r.2.length = k + 1 ∧
      (∀ w ∈ r.2, w < (n + m + 2) + r.1.length) ∧
      notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
      ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (t : ℕ), t ≤ k →
        (wiresFrom r.1 (csVec x z)).getD (r.2.getD t 0) false = decide (t ≤ prefLen z) := by
  intro k
  induction k with
  | zero =>
    intro _ gs
    dsimp only [buildPrefixes]
    refine ⟨Extends.refl _ gs, by simp, rfl, ?_, rfl, ?_⟩
    · intro w hw; simp only [List.mem_singleton] at hw; subst hw; omega
    · intro x z t ht
      have ht0 : t = 0 := by omega
      subst ht0
      change (wiresFrom gs (csVec x z)).getD (n + m + 1) false = decide (0 ≤ prefLen z)
      rw [wiresFrom_getD_lt gs (csVec x z) (n + m + 1) (by rw [csVec_length]; omega),
          csVec_getD_true]
      simp
  | succ k ih =>
    intro hk gs
    dsimp only [buildPrefixes]
    set r1 := buildPrefixes n m k gs with hr1
    have h1 := ih (by omega) gs
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen_g1, hlen_w1, hlt1, hnc1, hval1⟩
    have hprev_lt : r1.2.getD k (n + m + 1) < (n + m + 2) + r1.1.length := by
      have hget : r1.2.getD k (n + m + 1) = r1.2.getD k 0 := by
        simp [List.getD_eq_getElem?_getD, show k < r1.2.length by omega]
      rw [hget]
      exact hlt1 _ (getD_mem r1.2 k 0 (by omega))
    have hnk_lt : n + k < (n + m + 2) + r1.1.length := by omega
    set r2 := emitAnd (n + m + 2) r1.1 (r1.2.getD k (n + m + 1)) (n + k) with hr2
    have h2 := emitAnd_spec (n + m + 2) r1.1 (r1.2.getD k (n + m + 1)) (n + k) hprev_lt hnk_lt
    rw [← hr2] at h2
    rcases h2 with ⟨hext2, hlen_g2, hlt2, hnc2, hval2⟩
    refine ⟨hext1.trans hext2, by omega, by simp [hlen_w1], ?_, by omega, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with hw1 | hw2
      · have := hlt1 w hw1; omega
      · simp only [List.mem_singleton] at hw2; subst hw2; exact hlt2
    · intro x z t ht
      by_cases htk : t ≤ k
      · rw [getD_append_left _ _ t 0 (by omega),
            hext2.wire_eq (csVec x z) (csVec_length x z) _ (hlt1 _ (getD_mem r1.2 t 0 (by omega)))]
        exact hval1 x z t htk
      · have hteq : t = k + 1 := by omega
        subst hteq
        rw [getD_append_right _ _ (k + 1) 0 (by omega), hlen_w1]
        have hsub : k + 1 - (k + 1) = 0 := by omega
        rw [hsub]
        change (wiresFrom r2.1 (csVec x z)).getD r2.2 false = _
        rw [hval2 (csVec x z) (csVec_length x z)]
        have hget : r1.2.getD k (n + m + 1) = r1.2.getD k 0 := by
          simp [List.getD_eq_getElem?_getD, show k < r1.2.length by omega]
        rw [hget, hval1 x z k (le_refl k),
            wiresFrom_getD_lt r1.1 (csVec x z) (n + k) (by rw [csVec_length]; omega)]
        have hfk : (csVec x z).getD (n + k) false = @decide ((⟨k, by omega⟩ : Fin m) ∈ z) (Classical.propDecidable _) :=
          csVec_getD_z x z ⟨k, by omega⟩
        rw [hfk]
        apply Bool.eq_iff_iff.mpr
        simp only [Bool.and_eq_true, decide_eq_true_eq, le_prefLen_iff z k (by omega),
          le_prefLen_iff z (k + 1) hk]
        constructor
        · rintro ⟨hall, hkmem⟩ i hi
          by_cases hik : i.val < k
          · exact hall i hik
          · have : i = ⟨k, by omega⟩ := Fin.ext (by dsimp; omega)
            rw [this]; exact hkmem
        · intro hall
          exact ⟨fun i hi => hall i (by omega), hall ⟨k, by omega⟩ (by simp)⟩

structure SimState where
  gs : List Gate
  done : List Gate
  rem : List Gate
  wMap : List ℕ

def SimInv (n m : ℕ) (D : Circuit) (st : SimState) : Prop :=
  st.done ++ st.rem = D.gates ∧
  st.wMap.length = n + 2 + st.done.length ∧
  (∀ w ∈ st.wMap, w < (n + m + 2) + st.gs.length) ∧
  ∀ (x : Finset (Fin n)) (k : ℕ), k < n + 2 + st.done.length →
    (wiresFrom st.gs (csVec x (Finset.univ : Finset (Fin m)))).getD (st.wMap.getD k 0) false =
      (wiresFrom st.done (dsVec x)).getD k false

lemma simInv_ext {n m : ℕ} {D : Circuit} {st : SimState} (hinv : SimInv n m D st)
    {gs' : List Gate} (hext : Extends (n + m + 2) st.gs gs') :
    SimInv n m D ⟨gs', st.done, st.rem, st.wMap⟩ := by
  rcases hinv with ⟨hsplit, hlen, hlt, hval⟩
  have hgl := hext.length_le
  refine ⟨hsplit, hlen, fun w hw => by dsimp only; exact lt_of_lt_of_le (hlt w hw) (by omega), fun x k hk => ?_⟩
  dsimp only at hk ⊢
  rw [hext.wire_eq (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) _ (hlt _ (getD_mem st.wMap k 0 (by omega)))]
  exact hval x k hk

noncomputable def simNonNotsAux (base : ℕ) : List Gate → List Gate → List ℕ → List Gate → SimState
  | gs, done, wMap, [] => ⟨gs, done, [], wMap⟩
  | gs, done, wMap, g :: rest =>
    if g.op = GateOp.not then ⟨gs, done, g :: rest, wMap⟩
    else
      let r := emitCopyGate base gs wMap g
      simNonNotsAux base r.1 (done ++ [g]) (wMap ++ [r.2]) rest

noncomputable def simNonNots (base : ℕ) (st : SimState) : SimState :=
  simNonNotsAux base st.gs st.done st.wMap st.rem

lemma simNonNotsAux_spec {n m : ℕ} {D : Circuit}
    (hfitD : FanInTwo D) (hrbD : ReadsBack (n + 2) D) :
    ∀ (rem gs done : List Gate) (wMap : List ℕ),
      SimInv n m D ⟨gs, done, rem, wMap⟩ →
      let st' := simNonNotsAux (n + m + 2) gs done wMap rem
      Extends (n + m + 2) gs st'.gs ∧
      SimInv n m D st' ∧
      st'.gs.length + done.length = gs.length + st'.done.length ∧
      done.length ≤ st'.done.length ∧
      notCount ⟨st'.gs, 0⟩ = notCount ⟨gs, 0⟩ ∧
      notCount ⟨st'.rem, 0⟩ = notCount ⟨rem, 0⟩ ∧
      (∀ g rest, st'.rem = g :: rest → g.op = GateOp.not) := by
  intro rem
  induction rem with
  | nil =>
    intro gs done wMap hinv
    dsimp only [simNonNotsAux]
    exact ⟨Extends.refl _ gs, hinv, rfl, le_refl _, rfl, rfl, fun _ _ h => by cases h⟩
  | cons g rest ih =>
    intro gs done wMap hinv
    dsimp only [simNonNotsAux]
    by_cases hnot : g.op = GateOp.not
    · rw [if_pos hnot]
      refine ⟨Extends.refl _ gs, hinv, rfl, le_refl _, rfl, rfl, ?_⟩
      intro g' rest' heq; injection heq with h1 _; rw [← h1]; exact hnot
    · rw [if_neg hnot]
      rcases hinv with ⟨hsplit, hlen, hlt, hval⟩
      dsimp only at hsplit hlen hlt hval
      have hg_mem : g ∈ D.gates := by rw [← hsplit]; simp
      have hg_fit := hfitD g hg_mem
      have hpos_lt : done.length < D.gates.length := by rw [← hsplit]; simp
      have hget_g : D.gates[done.length] = g := by
        have h1 : (done ++ g :: rest)[done.length]'(by simp) = (g :: rest)[0]'(by simp) := by
          rw [List.getElem_append_right (le_refl _)]; simp
        have h2 : D.gates[done.length]'hpos_lt = (done ++ g :: rest)[done.length]'(by simp) := by
          congr 1; exact hsplit.symm
        rw [h2, h1]; rfl
      have hg_in : ∀ i ∈ g.inputs, i < wMap.length := by
        intro i hi
        have hrb := hrbD done.length hpos_lt
        rw [gateAt_eq_getElem D done.length hpos_lt, hget_g] at hrb
        have := hrb i hi
        omega
      set r := emitCopyGate (n + m + 2) gs wMap g with hr
      have hr_spec := emitCopyGate_spec (n + m + 2) gs wMap g hg_fit hg_in hlt
      rw [← hr] at hr_spec
      rcases hr_spec with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
      have hinv1 : SimInv n m D ⟨r.1, done ++ [g], rest, wMap ++ [r.2]⟩ := by
        refine ⟨by dsimp only; rw [List.append_assoc, List.singleton_append, hsplit],
                by dsimp only; simp [hlen]; omega, ?_, ?_⟩
        · intro w hw
          dsimp only at hw ⊢
          rcases List.mem_append.mp hw with hw1 | hw2
          · have := hlt w hw1; omega
          · simp only [List.mem_singleton] at hw2; subst hw2; exact hlt1
        · intro x k hk
          dsimp only at hk ⊢
          simp only [List.length_append, List.length_singleton] at hk
          by_cases hk_lt : k < n + 2 + done.length
          · rw [getD_append_left _ _ k 0 (by omega),
                hext1.wire_eq (csVec x Finset.univ) (csVec_length x Finset.univ) _ (hlt _ (getD_mem wMap k 0 (by omega))),
                hval x k hk_lt, wiresFrom_append,
                wiresFrom_getD_lt [g] _ k (by rw [wiresFrom_length, dsVec_length]; exact hk_lt)]
          · have hkeq : k = n + 2 + done.length := by omega
            subst hkeq
            rw [getD_append_right _ _ (n + 2 + done.length) 0 (by omega), hlen]
            have hsub : n + 2 + done.length - (n + 2 + done.length) = 0 := by omega
            rw [hsub]
            change (wiresFrom r.1 (csVec x Finset.univ)).getD r.2 false = _
            rw [hval1 (csVec x Finset.univ) (csVec_length x Finset.univ)]
            rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
            have hdl : (wiresFrom done (dsVec x)).length = n + 2 + done.length := by
              rw [wiresFrom_length, dsVec_length]
            rw [getD_append_right _ _ (n + 2 + done.length) false (by omega), hdl, hsub]
            simp only [List.getD_cons_zero]
            congr 1
            refine List.map_congr_left fun i hi => ?_
            have hi' := hg_in i hi
            exact hval x i (by omega)
      have hrec := ih r.1 (done ++ [g]) (wMap ++ [r.2]) hinv1
      rcases hrec with ⟨hext2, hinv2, hsz2, hdone2, hnc2, hrem2, hhead2⟩
      have hrem_eq : notCount ⟨g :: rest, 0⟩ = notCount ⟨rest, 0⟩ := by
        rw [notCount_cons, if_neg hnot, zero_add]
      refine ⟨hext1.trans hext2, hinv2, ?_, ?_, ?_, by omega, hhead2⟩
      · simp only [List.length_append, List.length_singleton] at hsz2; omega
      · simp only [List.length_append, List.length_singleton] at hdone2; omega
      · rw [if_neg hnot, add_zero] at hnc1; omega

noncomputable def simSharedNot (base zeroW fullW digitW : ℕ) (st : SimState) : SimState × ℕ :=
  let st1 := simNonNots base st
  match st1.rem with
  | [] =>
    let r3 := emitNot base st1.gs digitW
    (⟨r3.1, st1.done, [], st1.wMap⟩, r3.2)
  | g :: rest =>
    let opW := match g.inputs with
      | [] => zeroW
      | a :: _ => st1.wMap.getD a 0
    let r1 := emitAnd base st1.gs fullW opW
    let r2 := emitOr base r1.1 digitW r1.2
    let r3 := emitNot base r2.1 r2.2
    (⟨r3.1, st1.done ++ [g], rest, st1.wMap ++ [r3.2]⟩, r3.2)

lemma simSharedNot_spec {n m : ℕ} {D : Circuit}
    (hfitD : FanInTwo D) (hrbD : ReadsBack (n + 2) D)
    (st : SimState) (hinv : SimInv n m D st)
    (fullW digitW : ℕ)
    (hfull_lt : fullW < (n + m + 2) + st.gs.length)
    (hdig_lt : digitW < (n + m + 2) + st.gs.length)
    (hfull_val : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (wiresFrom st.gs (csVec x z)).getD fullW false = decide (z = Finset.univ))
    (hdig_univ : ∀ (x : Finset (Fin n)),
      (wiresFrom st.gs (csVec x (Finset.univ : Finset (Fin m)))).getD digitW false = false) :
    let res := simSharedNot (n + m + 2) (n + m) fullW digitW st
    Extends (n + m + 2) st.gs res.1.gs ∧
    SimInv n m D res.1 ∧
    res.2 < (n + m + 2) + res.1.gs.length ∧
    res.1.gs.length + st.done.length ≤ st.gs.length + res.1.done.length + 2 ∧
    st.done.length ≤ res.1.done.length ∧
    notCount ⟨res.1.gs, 0⟩ = notCount ⟨st.gs, 0⟩ + 1 ∧
    notCount ⟨res.1.rem, 0⟩ = notCount ⟨st.rem, 0⟩ - 1 ∧
    ∀ (x : Finset (Fin n)) (z : Finset (Fin m)), z ≠ Finset.univ →
      (wiresFrom res.1.gs (csVec x z)).getD res.2 false =
        !((wiresFrom st.gs (csVec x z)).getD digitW false) := by
  dsimp only [simSharedNot, simNonNots]
  set st1 := simNonNotsAux (n + m + 2) st.gs st.done st.wMap st.rem with hst1
  have h1 := simNonNotsAux_spec hfitD hrbD st.rem st.gs st.done st.wMap hinv
  rw [← hst1] at h1
  rcases h1 with ⟨hext1, hinv1, hsz1, hdone1, hnc1, hrem1, hhead1⟩
  have hgl1 := hext1.length_le
  cases hrem_eq : st1.rem with
  | nil =>
    dsimp only
    have hdig1 : digitW < (n + m + 2) + st1.gs.length := by omega
    set r3 := emitNot (n + m + 2) st1.gs digitW with hr3
    have h3 := emitNot_spec (n + m + 2) st1.gs digitW hdig1
    rw [← hr3] at h3
    rcases h3 with ⟨hext3, hlen3, hlt3, hnc3, hval3⟩
    have hrem0 : notCount ⟨st.rem, 0⟩ = 0 := by rw [← hrem1, hrem_eq]; rfl
    refine ⟨hext1.trans hext3, ?_, hlt3, by omega, hdone1, by omega, ?_, ?_⟩
    · have hinv1' : SimInv n m D ⟨st1.gs, st1.done, [], st1.wMap⟩ := by
        rcases st1 with ⟨gs1, done1, rem1, wMap1⟩
        dsimp only at hrem_eq
        subst hrem_eq
        exact hinv1
      exact simInv_ext hinv1' hext3
    · change notCount ⟨[], 0⟩ = notCount ⟨st.rem, 0⟩ - 1
      rw [hrem0]; rfl
    · intro x z _
      rw [hval3 (csVec x z) (csVec_length x z),
          hext1.wire_eq (csVec x z) (csVec_length x z) digitW hdig_lt]
  | cons g rest =>
    dsimp only
    have hg_not : g.op = GateOp.not := hhead1 g rest hrem_eq
    rcases hinv1 with ⟨hsplit1, hlen1, hlt1, hval1⟩
    rw [hrem_eq] at hsplit1
    have hpos_lt : st1.done.length < D.gates.length := by rw [← hsplit1]; simp
    have hget_g : D.gates[st1.done.length] = g := by
      have h1' : (st1.done ++ g :: rest)[st1.done.length]'(by simp) = (g :: rest)[0]'(by simp) := by
        rw [List.getElem_append_right (le_refl _)]; simp
      have h2' : D.gates[st1.done.length]'hpos_lt = (st1.done ++ g :: rest)[st1.done.length]'(by simp) := by
        congr 1; exact hsplit1.symm
      rw [h2', h1']; rfl
    have hg_in : ∀ i ∈ g.inputs, i < st1.wMap.length := by
      intro i hi
      have hrb := hrbD st1.done.length hpos_lt
      rw [gateAt_eq_getElem D st1.done.length hpos_lt, hget_g] at hrb
      have := hrb i hi
      omega
    let opW := match g.inputs with
      | [] => n + m
      | a :: _ => st1.wMap.getD a 0
    have hopW_lt : opW < (n + m + 2) + st1.gs.length := by
      dsimp only [opW]
      cases hgi : g.inputs with
      | nil => dsimp only; omega
      | cons a tl =>
        exact hlt1 _ (getD_mem st1.wMap a 0 (hg_in a (by rw [hgi]; exact List.mem_cons_self ..)))
    have hfull1 : fullW < (n + m + 2) + st1.gs.length := by omega
    have hdig1 : digitW < (n + m + 2) + st1.gs.length := by omega
    set r1 := emitAnd (n + m + 2) st1.gs fullW opW with hr1
    have hr1_s := emitAnd_spec (n + m + 2) st1.gs fullW opW hfull1 hopW_lt
    rw [← hr1] at hr1_s
    rcases hr1_s with ⟨hextA, hlenA, hltA, hncA, hvalA⟩
    set r2 := emitOr (n + m + 2) r1.1 digitW r1.2 with hr2
    have hr2_s := emitOr_spec (n + m + 2) r1.1 digitW r1.2 (by omega) hltA
    rw [← hr2] at hr2_s
    rcases hr2_s with ⟨hextO, hlenO, hltO, hncO, hvalO⟩
    set r3 := emitNot (n + m + 2) r2.1 r2.2 with hr3
    have hr3_s := emitNot_spec (n + m + 2) r2.1 r2.2 hltO
    rw [← hr3] at hr3_s
    rcases hr3_s with ⟨hextN, hlenN, hltN, hncN, hvalN⟩
    have hextAO : Extends (n + m + 2) st1.gs r2.1 := hextA.trans hextO
    have hextAON : Extends (n + m + 2) st1.gs r3.1 := hextAO.trans hextN
    have hrem_drop : notCount ⟨rest, 0⟩ = notCount ⟨st.rem, 0⟩ - 1 := by
      rw [← hrem1, hrem_eq, notCount_cons, if_pos hg_not]; omega
    refine ⟨hext1.trans hextAON, ?_, hltN, ?_, ?_, by omega, hrem_drop, ?_⟩
    · refine ⟨by dsimp only; rw [List.append_assoc, List.singleton_append, hsplit1],
              by dsimp only; simp [hlen1]; omega, ?_, ?_⟩
      · intro w hw
        dsimp only at hw ⊢
        rcases List.mem_append.mp hw with hw1 | hw2
        · have := hlt1 w hw1; omega
        · simp only [List.mem_singleton] at hw2; subst hw2; exact hltN
      · intro x k hk
        dsimp only at hk ⊢
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hk_lt : k < n + 2 + st1.done.length
        · rw [getD_append_left _ _ k 0 (by omega),
              hextAON.wire_eq (csVec x Finset.univ) (csVec_length x Finset.univ) _ (hlt1 _ (getD_mem st1.wMap k 0 (by omega))),
              hval1 x k hk_lt, wiresFrom_append,
              wiresFrom_getD_lt [g] _ k (by rw [wiresFrom_length, dsVec_length]; exact hk_lt)]
        · have hkeq : k = n + 2 + st1.done.length := by omega
          subst hkeq
          rw [getD_append_right _ _ (n + 2 + st1.done.length) 0 (by omega), hlen1]
          have hsub : n + 2 + st1.done.length - (n + 2 + st1.done.length) = 0 := by omega
          rw [hsub]
          change (wiresFrom r3.1 (csVec x Finset.univ)).getD r3.2 false = _
          rw [hvalN (csVec x Finset.univ) (csVec_length x Finset.univ),
              hvalO (csVec x Finset.univ) (csVec_length x Finset.univ),
              hvalA (csVec x Finset.univ) (csVec_length x Finset.univ),
              hextA.wire_eq (csVec x Finset.univ) (csVec_length x Finset.univ) digitW hdig1,
              hext1.wire_eq (csVec x Finset.univ) (csVec_length x Finset.univ) digitW hdig_lt,
              hext1.wire_eq (csVec x Finset.univ) (csVec_length x Finset.univ) fullW hfull_lt,
              hdig_univ x, hfull_val x Finset.univ]
          simp only [↓reduceIte, Bool.true_and, Bool.false_or]
          rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
          have hdl : (wiresFrom st1.done (dsVec x)).length = n + 2 + st1.done.length := by
            rw [wiresFrom_length, dsVec_length]
          rw [getD_append_right _ _ (n + 2 + st1.done.length) false (by omega), hdl, hsub]
          simp only [List.getD_cons_zero, hg_not, GateOp.eval]
          congr 1
          dsimp only [opW]
          cases hgi : g.inputs with
          | nil =>
            rw [wiresFrom_getD_lt st1.gs (csVec x Finset.univ) (n + m) (by rw [csVec_length]; omega),
                csVec_getD_false]
            rfl
          | cons a tl =>
            simp only [List.map_cons, List.headD_cons]
            have ha := hg_in a (by rw [hgi]; exact List.mem_cons_self ..)
            exact hval1 x a (by omega)
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · intro x z hne
      rw [hvalN (csVec x z) (csVec_length x z),
          hvalO (csVec x z) (csVec_length x z),
          hvalA (csVec x z) (csVec_length x z),
          hextA.wire_eq (csVec x z) (csVec_length x z) digitW hdig1,
          hext1.wire_eq (csVec x z) (csVec_length x z) digitW hdig_lt,
          hext1.wire_eq (csVec x z) (csVec_length x z) fullW hfull_lt,
          hfull_val x z, decide_eq_false hne]
      simp

def simRestAux (base : ℕ) : List Gate → List Gate → List ℕ → List Gate → SimState
  | gs, done, wMap, [] => ⟨gs, done, [], wMap⟩
  | gs, done, wMap, g :: rest =>
    let r := emitCopyGate base gs wMap g
    simRestAux base r.1 (done ++ [g]) (wMap ++ [r.2]) rest

def simRest (base : ℕ) (st : SimState) : SimState :=
  simRestAux base st.gs st.done st.wMap st.rem

lemma simRestAux_spec {n m : ℕ} {D : Circuit}
    (hfitD : FanInTwo D) (hrbD : ReadsBack (n + 2) D) :
    ∀ (rem gs done : List Gate) (wMap : List ℕ),
      SimInv n m D ⟨gs, done, rem, wMap⟩ →
      let st' := simRestAux (n + m + 2) gs done wMap rem
      Extends (n + m + 2) gs st'.gs ∧
      SimInv n m D st' ∧
      st'.rem = [] ∧
      st'.gs.length + done.length = gs.length + st'.done.length ∧
      notCount ⟨st'.gs, 0⟩ = notCount ⟨gs, 0⟩ + notCount ⟨rem, 0⟩ := by
  intro rem
  induction rem with
  | nil =>
    intro gs done wMap hinv
    dsimp only [simRestAux]
    exact ⟨Extends.refl _ gs, hinv, rfl, rfl, by simp [notCount]⟩
  | cons g rest ih =>
    intro gs done wMap hinv
    dsimp only [simRestAux]
    rcases hinv with ⟨hsplit, hlen, hlt, hval⟩
    dsimp only at hsplit hlen hlt hval
    have hg_mem : g ∈ D.gates := by rw [← hsplit]; simp
    have hg_fit := hfitD g hg_mem
    have hpos_lt : done.length < D.gates.length := by rw [← hsplit]; simp
    have hget_g : D.gates[done.length] = g := by
      have h1 : (done ++ g :: rest)[done.length]'(by simp) = (g :: rest)[0]'(by simp) := by
        rw [List.getElem_append_right (le_refl _)]; simp
      have h2 : D.gates[done.length]'hpos_lt = (done ++ g :: rest)[done.length]'(by simp) := by
        congr 1; exact hsplit.symm
      rw [h2, h1]; rfl
    have hg_in : ∀ i ∈ g.inputs, i < wMap.length := by
      intro i hi
      have hrb := hrbD done.length hpos_lt
      rw [gateAt_eq_getElem D done.length hpos_lt, hget_g] at hrb
      have := hrb i hi
      omega
    set r := emitCopyGate (n + m + 2) gs wMap g with hr
    have hr_spec := emitCopyGate_spec (n + m + 2) gs wMap g hg_fit hg_in hlt
    rw [← hr] at hr_spec
    rcases hr_spec with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    have hinv1 : SimInv n m D ⟨r.1, done ++ [g], rest, wMap ++ [r.2]⟩ := by
      refine ⟨by dsimp only; rw [List.append_assoc, List.singleton_append, hsplit],
              by dsimp only; simp [hlen]; omega, ?_, ?_⟩
      · intro w hw
        dsimp only at hw ⊢
        rcases List.mem_append.mp hw with hw1 | hw2
        · have := hlt w hw1; omega
        · simp only [List.mem_singleton] at hw2; subst hw2; exact hlt1
      · intro x k hk
        dsimp only at hk ⊢
        simp only [List.length_append, List.length_singleton] at hk
        by_cases hk_lt : k < n + 2 + done.length
        · rw [getD_append_left _ _ k 0 (by omega),
              hext1.wire_eq (csVec x Finset.univ) (csVec_length x Finset.univ) _ (hlt _ (getD_mem wMap k 0 (by omega))),
              hval x k hk_lt, wiresFrom_append,
              wiresFrom_getD_lt [g] _ k (by rw [wiresFrom_length, dsVec_length]; exact hk_lt)]
        · have hkeq : k = n + 2 + done.length := by omega
          subst hkeq
          rw [getD_append_right _ _ (n + 2 + done.length) 0 (by omega), hlen]
          have hsub : n + 2 + done.length - (n + 2 + done.length) = 0 := by omega
          rw [hsub]
          change (wiresFrom r.1 (csVec x Finset.univ)).getD r.2 false = _
          rw [hval1 (csVec x Finset.univ) (csVec_length x Finset.univ)]
          rw [wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
          have hdl : (wiresFrom done (dsVec x)).length = n + 2 + done.length := by
            rw [wiresFrom_length, dsVec_length]
          rw [getD_append_right _ _ (n + 2 + done.length) false (by omega), hdl, hsub]
          simp only [List.getD_cons_zero]
          congr 1
          refine List.map_congr_left fun i hi => ?_
          have hi' := hg_in i hi
          exact hval x i (by omega)
    have hrec := ih r.1 (done ++ [g]) (wMap ++ [r.2]) hinv1
    rcases hrec with ⟨hext2, hinv2, hrem2, hsz2, hnc2⟩
    refine ⟨hext1.trans hext2, hinv2, hrem2, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton] at hsz2; omega
    · rw [notCount_cons]; omega

end PrefixAndSim

section TreeDecoder

def vGeWire (n m : ℕ) (prefs : List ℕ) (k : ℕ) : ℕ :=
  if k = 0 then n + m + 1
  else if 2 * k - 1 ≤ m then prefs.getD (2 * k - 1) (n + m)
  else n + m

lemma vGeWire_lt {n m : ℕ} {prefs : List ℕ} {baseLen : ℕ}
    (hlen : prefs.length = m + 1)
    (hlt : ∀ w ∈ prefs, w < (n + m + 2) + baseLen) (k : ℕ) :
    vGeWire n m prefs k < (n + m + 2) + baseLen := by
  dsimp only [vGeWire]
  split_ifs with h0 hle
  · omega
  · have hget : prefs.getD (2 * k - 1) (n + m) = prefs.getD (2 * k - 1) 0 := by
      simp [List.getD_eq_getElem?_getD, show 2 * k - 1 < prefs.length by omega]
    rw [hget]
    exact hlt _ (getD_mem prefs (2 * k - 1) 0 (by omega))
  · omega

lemma vGeWire_val {n m : ℕ} {prefs : List ℕ} {gs : List Gate}
    (hlen : prefs.length = m + 1)
    (hpref : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (t : ℕ), t ≤ m →
      (wiresFrom gs (csVec x z)).getD (prefs.getD t 0) false = decide (t ≤ prefLen z))
    (x : Finset (Fin n)) (z : Finset (Fin m)) (k : ℕ) :
    (wiresFrom gs (csVec x z)).getD (vGeWire n m prefs k) false = decide (k ≤ (prefLen z + 1) / 2) := by
  dsimp only [vGeWire]
  split_ifs with h0 hle
  · subst h0
    rw [wiresFrom_getD_lt gs (csVec x z) (n + m + 1) (by rw [csVec_length]; omega), csVec_getD_true]
    simp
  · have hget : prefs.getD (2 * k - 1) (n + m) = prefs.getD (2 * k - 1) 0 := by
      simp [List.getD_eq_getElem?_getD, show 2 * k - 1 < prefs.length by omega]
    rw [hget, hpref x z (2 * k - 1) hle]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    omega
  · rw [wiresFrom_getD_lt gs (csVec x z) (n + m) (by rw [csVec_length]; omega), csVec_getD_false]
    have hpl := prefLen_le z
    symm; exact decide_eq_false (by omega)

def orAndPairs (base : ℕ) : List Gate → ℕ → List ℕ → List ℕ → List Gate × ℕ
  | gs, acc, [], _ => (gs, acc)
  | gs, acc, _, [] => (gs, acc)
  | gs, acc, a :: as, b :: bs =>
    let r1 := emitAnd base gs a b
    let r2 := emitOr base r1.1 acc r1.2
    orAndPairs base r2.1 r2.2 as bs

lemma orAndPairs_spec (base : ℕ) (as bs : List ℕ) (gs : List Gate) (acc : ℕ)
    (hlen : as.length = bs.length)
    (hacc : acc < base + gs.length)
    (has : ∀ i ∈ as, i < base + gs.length)
    (hbs : ∀ i ∈ bs, i < base + gs.length) :
    let r := orAndPairs base gs acc as bs
    Extends base gs r.1 ∧
    r.1.length = gs.length + 2 * as.length ∧
    r.2 < base + r.1.length ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (v : List Bool), v.length = base →
      (wiresFrom r.1 v).getD r.2 false =
        ((wiresFrom gs v).getD acc false ||
          (List.range as.length).any fun ℓ =>
            (wiresFrom gs v).getD (as.getD ℓ 0) false &&
            (wiresFrom gs v).getD (bs.getD ℓ 0) false) := by
  induction as generalizing bs gs acc with
  | nil =>
    cases bs with
    | nil =>
      dsimp only [orAndPairs]
      refine ⟨Extends.refl base gs, by simp, hacc, rfl, fun v _ => by simp⟩
    | cons _ _ => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      dsimp only [orAndPairs]
      have ha : a < base + gs.length := has a (List.mem_cons_self ..)
      have hb : b < base + gs.length := hbs b (List.mem_cons_self ..)
      have has' : ∀ i ∈ as, i < base + gs.length := fun i hi => has i (List.mem_cons_of_mem _ hi)
      have hbs' : ∀ i ∈ bs, i < base + gs.length := fun i hi => hbs i (List.mem_cons_of_mem _ hi)
      set r1 := emitAnd base gs a b with hr1
      have h1 := emitAnd_spec base gs a b ha hb
      rw [← hr1] at h1
      rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
      set r2 := emitOr base r1.1 acc r1.2 with hr2
      have h2 := emitOr_spec base r1.1 acc r1.2 (by omega) hlt1
      rw [← hr2] at h2
      rcases h2 with ⟨hext2, hlen2, hlt2, hnc2, hval2⟩
      have hext12 := hext1.trans hext2
      have h3 := ih bs r2.1 r2.2 (by simp at hlen; omega) hlt2
        (fun i hi => lt_of_lt_of_le (has' i hi) (by omega))
        (fun i hi => lt_of_lt_of_le (hbs' i hi) (by omega))
      rcases h3 with ⟨hext3, hlen3, hlt3, hnc3, hval3⟩
      refine ⟨hext12.trans hext3, by simp only [List.length_cons]; omega, hlt3, by omega, fun v hv => ?_⟩
      rw [hval3 v hv, hval2 v hv, hval1 v hv, hext1.wire_eq v hv acc hacc]
      have hany : ((List.range as.length).any fun ℓ =>
          (wiresFrom r2.1 v).getD (as.getD ℓ 0) false &&
          (wiresFrom r2.1 v).getD (bs.getD ℓ 0) false) =
        ((List.range as.length).any fun ℓ =>
          (wiresFrom gs v).getD (as.getD ℓ 0) false &&
          (wiresFrom gs v).getD (bs.getD ℓ 0) false) := by
        apply Bool.eq_iff_iff.mpr
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
        constructor
        · rintro ⟨ℓ, hℓ, h1', h2'⟩
          rw [hext12.wire_eq v hv _ (has' _ (getD_mem as ℓ 0 hℓ))] at h1'
          rw [hext12.wire_eq v hv _ (hbs' _ (getD_mem bs ℓ 0 (by simp at hlen; omega)))] at h2'
          exact ⟨ℓ, hℓ, h1', h2'⟩
        · rintro ⟨ℓ, hℓ, h1', h2'⟩
          refine ⟨ℓ, hℓ, ?_, ?_⟩
          · rw [hext12.wire_eq v hv _ (has' _ (getD_mem as ℓ 0 hℓ))]; exact h1'
          · rw [hext12.wire_eq v hv _ (hbs' _ (getD_mem bs ℓ 0 (by simp at hlen; omega)))]; exact h2'
      rw [hany, Bool.or_assoc]
      congr 1
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range, Bool.and_eq_true, List.length_cons]
      constructor
      · rintro (⟨h1a, h1b⟩ | ⟨ℓ, hℓ, h2a, h2b⟩)
        · exact ⟨0, by omega, h1a, h1b⟩
        · exact ⟨ℓ + 1, by omega, h2a, h2b⟩
      · rintro ⟨ℓ, hℓ, h2a, h2b⟩
        cases ℓ with
        | zero => exact Or.inl ⟨h2a, h2b⟩
        | succ ℓ' => exact Or.inr ⟨ℓ', by omega, h2a, h2b⟩

def splitBlocks (base notW digW : ℕ) : List Gate → List ℕ → List Gate × List ℕ
  | gs, [] => (gs, [])
  | gs, u :: us =>
    let r0 := emitAnd base gs u notW
    let r1 := emitAnd base r0.1 u digW
    let rest := splitBlocks base notW digW r1.1 us
    (rest.1, r0.2 :: r1.2 :: rest.2)

lemma splitBlocks_spec (base notW digW : ℕ) (us : List ℕ) (gs : List Gate)
    (hnot : notW < base + gs.length) (hdig : digW < base + gs.length)
    (hus : ∀ i ∈ us, i < base + gs.length) :
    let r := splitBlocks base notW digW gs us
    Extends base gs r.1 ∧
    r.1.length = gs.length + 2 * us.length ∧
    r.2.length = 2 * us.length ∧
    (∀ i ∈ r.2, i < base + r.1.length) ∧
    notCount ⟨r.1, 0⟩ = notCount ⟨gs, 0⟩ ∧
    ∀ (v : List Bool), v.length = base →
      ∀ (k : ℕ), k < 2 * us.length →
        (wiresFrom r.1 v).getD (r.2.getD k 0) false =
          ((wiresFrom gs v).getD (us.getD (k / 2) 0) false &&
            (if k % 2 = 0 then (wiresFrom gs v).getD notW false else (wiresFrom gs v).getD digW false)) := by
  induction us generalizing gs with
  | nil =>
    dsimp only [splitBlocks]
    refine ⟨Extends.refl base gs, by simp, rfl, (fun _ h => by cases h), rfl, (fun _ _ k hk => by simp at hk)⟩
  | cons u us ih =>
    dsimp only [splitBlocks]
    have hu : u < base + gs.length := hus u (List.mem_cons_self ..)
    have hus' : ∀ i ∈ us, i < base + gs.length := fun i hi => hus i (List.mem_cons_of_mem _ hi)
    set r0 := emitAnd base gs u notW with hr0
    have h0 := emitAnd_spec base gs u notW hu hnot
    rw [← hr0] at h0
    rcases h0 with ⟨hext0, hlen0, hlt0, hnc0, hval0⟩
    set r1 := emitAnd base r0.1 u digW with hr1
    have h1 := emitAnd_spec base r0.1 u digW (by omega) (by omega)
    rw [← hr1] at h1
    rcases h1 with ⟨hext1, hlen1, hlt1, hnc1, hval1⟩
    have hext01 := hext0.trans hext1
    set rest := splitBlocks base notW digW r1.1 us with hrest
    have h2 := ih r1.1 (by omega) (by omega) (fun i hi => lt_of_lt_of_le (hus' i hi) (by omega))
    rw [← hrest] at h2
    rcases h2 with ⟨hext2, hlen2, hlen_w2, hlt2, hnc2, hval2⟩
    have hgl2 := hext2.length_le
    refine ⟨hext01.trans hext2, by simp only [List.length_cons]; omega, by simp only [List.length_cons]; omega,
            ?_, by omega, ?_⟩
    · intro i hi
      simp only [List.mem_cons] at hi
      rcases hi with rfl | rfl | hi
      · omega
      · omega
      · exact hlt2 i hi
    · intro v hv k hk
      cases k with
      | zero =>
        change (wiresFrom rest.1 v).getD r0.2 false = _
        rw [(hext1.trans hext2).wire_eq v hv r0.2 hlt0, hval0 v hv]
        simp
      | succ k1 =>
        cases k1 with
        | zero =>
          change (wiresFrom rest.1 v).getD r1.2 false = _
          rw [hext2.wire_eq v hv r1.2 hlt1, hval1 v hv,
              hext0.wire_eq v hv u hu, hext0.wire_eq v hv digW hdig]
          simp
        | succ k2 =>
          have hk2 : k2 < 2 * us.length := by simp at hk; omega
          change (wiresFrom rest.1 v).getD (rest.2.getD k2 0) false = _
          rw [hval2 v hv k2 hk2]
          have hdiv : (k2 + 2) / 2 = k2 / 2 + 1 := by omega
          have hmod : (k2 + 2) % 2 = k2 % 2 := by omega
          have hus_mem : us.getD (k2 / 2) 0 ∈ us := getD_mem us (k2 / 2) 0 (by omega)
          rw [hdiv, hmod, hext01.wire_eq v hv _ (hus' _ hus_mem),
              hext01.wire_eq v hv notW hnot, hext01.wire_eq v hv digW hdig]
          rfl

noncomputable def treeStep (n s b m : ℕ) (prefs : List ℕ) (fullW : ℕ) (t : ℕ) (st : SimState) (blks : List ℕ) :
    SimState × List ℕ :=
  let j := b - 1 - t
  let threshes := (List.range (2 ^ t)).map (fun u => vGeWire n m prefs ((2 * u + 1) * 2 ^ j))
  let rDig := orAndPairs (n + m + 2) st.gs (n + m) blks threshes
  let digW := rDig.2
  let stDig : SimState := ⟨rDig.1, st.done, st.rem, st.wMap⟩
  let (stNot, notW) :=
    if t < b - s then
      let rNot := emitNot (n + m + 2) stDig.gs digW
      (⟨rNot.1, stDig.done, stDig.rem, stDig.wMap⟩, rNot.2)
    else
      simSharedNot (n + m + 2) (n + m) fullW digW stDig
  let rSp := splitBlocks (n + m + 2) notW digW stNot.gs blks
  (⟨rSp.1, stNot.done, stNot.rem, stNot.wMap⟩, rSp.2)

noncomputable def treeLoop (n s b m : ℕ) (prefs : List ℕ) (fullW : ℕ) :
    ℕ → SimState → List ℕ → SimState × List ℕ
  | 0, st, blks => (st, blks)
  | t + 1, st, blks =>
    let res := treeLoop n s b m prefs fullW t st blks
    treeStep n s b m prefs fullW t res.1 res.2

lemma treeStep_spec {n s b : ℕ} (hsb : s < b) {D : Circuit}
    (hfitD : FanInTwo D) (hrbD : ReadsBack (n + 2) D)
    (prefs : List ℕ) (fullW : ℕ) (gs0 : List Gate)
    (hpref_len : prefs.length = 2 * (2 ^ b - 2 ^ s) + 1)
    (hpref_lt : ∀ w ∈ prefs, w < (n + 2 * (2 ^ b - 2 ^ s) + 2) + gs0.length)
    (hpref_val : ∀ (x : Finset (Fin n)) (z : Finset (Fin (2 * (2 ^ b - 2 ^ s)))) (t : ℕ),
      t ≤ 2 * (2 ^ b - 2 ^ s) →
      (wiresFrom gs0 (csVec x z)).getD (prefs.getD t 0) false = decide (t ≤ prefLen z))
    (hfull_lt : fullW < (n + 2 * (2 ^ b - 2 ^ s) + 2) + gs0.length)
    (hfull_val : ∀ (x : Finset (Fin n)) (z : Finset (Fin (2 * (2 ^ b - 2 ^ s)))),
      (wiresFrom gs0 (csVec x z)).getD fullW false = decide (z = Finset.univ))
    (t : ℕ) (ht : t < b) (st : SimState) (blks : List ℕ)
    (hext0 : Extends (n + 2 * (2 ^ b - 2 ^ s) + 2) gs0 st.gs)
    (hinv : SimInv n (2 * (2 ^ b - 2 ^ s)) D st)
    (hblk_len : blks.length = 2 ^ t)
    (hblk_lt : ∀ w ∈ blks, w < (n + 2 * (2 ^ b - 2 ^ s) + 2) + st.gs.length)
    (hblk_prop : ∀ (x : Finset (Fin n)) (z : Finset (Fin (2 * (2 ^ b - 2 ^ s)))), z ≠ Finset.univ →
      ∀ u < 2 ^ t, (wiresFrom st.gs (csVec x z)).getD (blks.getD u 0) false =
        decide ((prefLen z + 1) / 2 / 2 ^ (b - t) = u))
    (hblk_univ : ∀ (x : Finset (Fin n)) (u : ℕ), u < 2 ^ t →
      (t < b - s → (wiresFrom st.gs (csVec x (Finset.univ : Finset (Fin (2 * (2 ^ b - 2 ^ s)))))).getD (blks.getD u 0) false =
        decide ((2 ^ b - 2 ^ s) / 2 ^ (b - t) = u)) ∧
      (b - s ≤ t → u * 2 ^ (b - t) < 2 ^ b - 2 ^ s →
        (wiresFrom st.gs (csVec x (Finset.univ : Finset (Fin (2 * (2 ^ b - 2 ^ s)))))).getD (blks.getD u 0) false = false)) :
    let m := 2 * (2 ^ b - 2 ^ s)
    let res := treeStep n s b m prefs fullW t st blks
    Extends (n + m + 2) st.gs res.1.gs ∧
    SimInv n m D res.1 ∧
    res.1.gs.length + st.done.length ≤ st.gs.length + res.1.done.length + 4 * 2 ^ t + 2 ∧
    st.done.length ≤ res.1.done.length ∧
    notCount ⟨res.1.gs, 0⟩ = notCount ⟨st.gs, 0⟩ + 1 ∧
    notCount ⟨res.1.rem, 0⟩ = (if t < b - s then notCount ⟨st.rem, 0⟩ else notCount ⟨st.rem, 0⟩ - 1) ∧
    res.2.length = 2 ^ (t + 1) ∧
    (∀ w ∈ res.2, w < (n + m + 2) + res.1.gs.length) ∧
    (∀ (x : Finset (Fin n)) (z : Finset (Fin m)), z ≠ Finset.univ →
      ∀ u < 2 ^ (t + 1), (wiresFrom res.1.gs (csVec x z)).getD (res.2.getD u 0) false =
        decide ((prefLen z + 1) / 2 / 2 ^ (b - (t + 1)) = u)) ∧
    (∀ (x : Finset (Fin n)) (u : ℕ), u < 2 ^ (t + 1) →
      (t + 1 < b - s → (wiresFrom res.1.gs (csVec x (Finset.univ : Finset (Fin m)))).getD (res.2.getD u 0) false =
        decide ((2 ^ b - 2 ^ s) / 2 ^ (b - (t + 1)) = u)) ∧
      (b - s ≤ t + 1 → u * 2 ^ (b - (t + 1)) < 2 ^ b - 2 ^ s →
        (wiresFrom res.1.gs (csVec x (Finset.univ : Finset (Fin m)))).getD (res.2.getD u 0) false = false)) := by
  let m := 2 * (2 ^ b - 2 ^ s)
  let j := b - 1 - t
  have hj_eq : b - (t + 1) = j := by omega
  have hbt_eq : b - t = j + 1 := by omega
  have hpow_bt : 2 ^ (b - t) = 2 * 2 ^ j := by rw [hbt_eq, pow_succ]; ring
  have hgl0 := hext0.length_le
  let threshes := (List.range (2 ^ t)).map (fun u => vGeWire n m prefs ((2 * u + 1) * 2 ^ j))
  have hth_len : threshes.length = 2 ^ t := by simp [threshes]
  have hth_lt : ∀ w ∈ threshes, w < (n + m + 2) + st.gs.length := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨u, _, rfl⟩
    exact lt_of_lt_of_le (vGeWire_lt hpref_len hpref_lt _) (by omega)
  set rDig := orAndPairs (n + m + 2) st.gs (n + m) blks threshes with hrDig
  have hDig := orAndPairs_spec (n + m + 2) blks threshes st.gs (n + m) (by omega) (by omega) hblk_lt hth_lt
  rw [← hrDig] at hDig
  rcases hDig with ⟨hextD, hlenD, hltD, hncD, hvalD⟩
  have hdig_eval : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (wiresFrom rDig.1 (csVec x z)).getD rDig.2 false =
        (List.range (2 ^ t)).any fun u =>
          (wiresFrom st.gs (csVec x z)).getD (blks.getD u 0) false &&
          decide ((2 * u + 1) * 2 ^ j ≤ (prefLen z + 1) / 2) := by
    intro x z
    rw [hvalD (csVec x z) (csVec_length x z),
        wiresFrom_getD_lt st.gs (csVec x z) (n + m) (by rw [csVec_length]; omega),
        csVec_getD_false, Bool.false_or, hblk_len]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor <;> rintro ⟨u, hu, h1, h2⟩ <;> refine ⟨u, hu, h1, ?_⟩
    · have hgt : threshes.getD u 0 = vGeWire n m prefs ((2 * u + 1) * 2 ^ j) := by
        dsimp only [threshes]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]; rfl
      rw [hgt, hext0.wire_eq (csVec x z) (csVec_length x z) _ (vGeWire_lt hpref_len hpref_lt _),
          vGeWire_val hpref_len hpref_val x z _] at h2
      exact h2
    · have hgt : threshes.getD u 0 = vGeWire n m prefs ((2 * u + 1) * 2 ^ j) := by
        dsimp only [threshes]
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]; rfl
      rw [hgt, hext0.wire_eq (csVec x z) (csVec_length x z) _ (vGeWire_lt hpref_len hpref_lt _),
          vGeWire_val hpref_len hpref_val x z _]
      exact h2
  have hdig_val_of_exact : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (∀ u < 2 ^ t, (wiresFrom st.gs (csVec x z)).getD (blks.getD u 0) false =
        decide ((prefLen z + 1) / 2 / 2 ^ (b - t) = u)) →
      (wiresFrom rDig.1 (csVec x z)).getD rDig.2 false =
        decide (((prefLen z + 1) / 2 / 2 ^ j) % 2 = 1) := by
    intro x z hexact
    rw [hdig_eval x z]
    set v := (prefLen z + 1) / 2
    have hv_lt : v < 2 ^ b := by
      have hpl := prefLen_le z
      have hpos_s : 0 < 2 ^ s := Nat.pow_pos (by omega)
      have hlt_sb : 2 ^ s < 2 ^ b := Nat.pow_lt_pow_right (by omega) hsb
      dsimp only [v, m] at hpl ⊢
      omega
    have hv_div_lt : v / 2 ^ (b - t) < 2 ^ t := by
      have hpow : 2 ^ b = 2 ^ t * 2 ^ (b - t) := by rw [← pow_add]; congr 1; omega
      exact (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by omega))).mpr (by omega)
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, h1, h2⟩
      rw [hexact u hu, decide_eq_true_eq] at h1
      have hdiv2 : v / 2 ^ (b - t) = (v / 2 ^ j) / 2 := by
        rw [hbt_eq, pow_succ, ← Nat.div_div_eq_div_mul]
      have hdiv_ge : 2 * u + 1 ≤ v / 2 ^ j :=
        (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).mpr h2
      omega
    · intro hmod
      refine ⟨v / 2 ^ (b - t), hv_div_lt, ?_, ?_⟩
      · rw [hexact _ hv_div_lt]; exact decide_eq_true rfl
      · have hdiv2 : v / 2 ^ (b - t) = (v / 2 ^ j) / 2 := by
          rw [hbt_eq, pow_succ, ← Nat.div_div_eq_div_mul]
        have hle : 2 * (v / 2 ^ (b - t)) + 1 ≤ v / 2 ^ j := by omega
        calc (2 * (v / 2 ^ (b - t)) + 1) * 2 ^ j
            ≤ (v / 2 ^ j) * 2 ^ j := Nat.mul_le_mul_right _ hle
          _ ≤ v := Nat.div_mul_le_self v (2 ^ j)
  have hpref_univ : (prefLen (Finset.univ : Finset (Fin m)) + 1) / 2 = 2 ^ b - 2 ^ s := by
    have hpm : prefLen (Finset.univ : Finset (Fin m)) = m := (prefLen_eq_m_iff _).mpr rfl
    rw [hpm]; dsimp only [m]; omega
  have hdig_prop : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)), z ≠ Finset.univ →
      (wiresFrom rDig.1 (csVec x z)).getD rDig.2 false =
        decide (((prefLen z + 1) / 2 / 2 ^ j) % 2 = 1) :=
    fun x z hne => hdig_val_of_exact x z (hblk_prop x z hne)
  have hdig_univ_ge : b - s ≤ t → ∀ x : Finset (Fin n),
      (wiresFrom rDig.1 (csVec x (Finset.univ : Finset (Fin m)))).getD rDig.2 false = false := by
    intro hge x
    rw [hdig_eval x Finset.univ, hpref_univ]
    apply Bool.eq_false_iff.mpr
    intro htrue
    rcases List.any_eq_true.mp htrue with ⟨u, hu, hand⟩
    rw [List.mem_range] at hu
    rcases Bool.and_eq_true _ _ |>.mp hand with ⟨h1, h2⟩
    have h2' := of_decide_eq_true h2
    have hlt_u : u * 2 ^ (b - t) < 2 ^ b - 2 ^ s := by
      have hpos : 0 < 2 ^ j := Nat.pow_pos (by omega)
      have h1 : u * 2 ^ (b - t) + 2 ^ j = (2 * u + 1) * 2 ^ j := by rw [hpow_bt]; ring
      omega
    have h0 := (hblk_univ x u hu).2 hge hlt_u
    rw [h0] at h1; cases h1
  let stDig : SimState := ⟨rDig.1, st.done, st.rem, st.wMap⟩
  have hinvDig : SimInv n m D stDig := simInv_ext hinv hextD
  have hfull_dig : ∀ x z, (wiresFrom stDig.gs (csVec x z)).getD fullW false = decide (z = Finset.univ) :=
    fun x z => by
      dsimp only [stDig]
      rw [(hext0.trans hextD).wire_eq (csVec x z) (csVec_length x z) fullW hfull_lt]
      exact hfull_val x z
  have hNot_step :
      let pair := if t < b - s then
        let rNot := emitNot (n + m + 2) stDig.gs rDig.2
        (⟨rNot.1, stDig.done, stDig.rem, stDig.wMap⟩, rNot.2)
      else simSharedNot (n + m + 2) (n + m) fullW rDig.2 stDig
      Extends (n + m + 2) stDig.gs pair.1.gs ∧
      SimInv n m D pair.1 ∧
      pair.2 < (n + m + 2) + pair.1.gs.length ∧
      pair.1.gs.length + st.done.length ≤ stDig.gs.length + pair.1.done.length + 2 ∧
      st.done.length ≤ pair.1.done.length ∧
      notCount ⟨pair.1.gs, 0⟩ = notCount ⟨stDig.gs, 0⟩ + 1 ∧
      notCount ⟨pair.1.rem, 0⟩ = (if t < b - s then notCount ⟨st.rem, 0⟩ else notCount ⟨st.rem, 0⟩ - 1) ∧
      (∀ (x : Finset (Fin n)) (z : Finset (Fin m)), z ≠ Finset.univ →
        (wiresFrom pair.1.gs (csVec x z)).getD pair.2 false =
          !((wiresFrom stDig.gs (csVec x z)).getD rDig.2 false)) ∧
      (t < b - s → ∀ (x : Finset (Fin n)),
        (wiresFrom pair.1.gs (csVec x (Finset.univ : Finset (Fin m)))).getD pair.2 false =
          !((wiresFrom stDig.gs (csVec x (Finset.univ : Finset (Fin m)))).getD rDig.2 false)) := by
    by_cases hts : t < b - s
    · dsimp only
      rw [if_pos hts, if_pos hts]
      have hN := emitNot_spec (n + m + 2) stDig.gs rDig.2 hltD
      rcases hN with ⟨hextN, hlenN, hltN, hncN, hvalN⟩
      exact ⟨hextN, simInv_ext hinvDig hextN, hltN, by dsimp only [stDig] at hlenN ⊢; omega, le_refl _, hncN, rfl,
        fun x z _ => hvalN (csVec x z) (csVec_length x z),
        fun _ x => hvalN (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _)⟩
    · dsimp only
      rw [if_neg hts, if_neg hts]
      have hS := simSharedNot_spec hfitD hrbD stDig hinvDig fullW rDig.2
        (by dsimp only [stDig, m]; omega) hltD hfull_dig (hdig_univ_ge (by omega))
      rcases hS with ⟨hextS, hinvS, hltS, hszS, hdoneS, hncS, hremS, hvalS⟩
      exact ⟨hextS, hinvS, hltS, hszS, hdoneS, hncS, hremS, hvalS, fun h => absurd h hts⟩
  set pair := if t < b - s then
    let rNot := emitNot (n + m + 2) stDig.gs rDig.2
    (⟨rNot.1, stDig.done, stDig.rem, stDig.wMap⟩, rNot.2)
  else simSharedNot (n + m + 2) (n + m) fullW rDig.2 stDig with hpair
  rcases hNot_step with ⟨hextN, hinvN, hltN, hszN, hdoneN, hncN, hremN, hvalN_prop, hvalN_univ⟩
  dsimp only [stDig] at hextN hszN hncN hvalN_prop hvalN_univ
  have hglN := hextN.length_le
  have hextDN : Extends (n + m + 2) st.gs pair.1.gs := hextD.trans hextN
  have hglDN := hextDN.length_le
  have hdigN_lt : rDig.2 < (n + m + 2) + pair.1.gs.length := by omega
  have hblkN_lt : ∀ w ∈ blks, w < (n + m + 2) + pair.1.gs.length := fun w hw =>
    lt_of_lt_of_le (hblk_lt w hw) (by omega)
  set rSp := splitBlocks (n + m + 2) pair.2 rDig.2 pair.1.gs blks with hrSp
  have hSp := splitBlocks_spec (n + m + 2) pair.2 rDig.2 blks pair.1.gs hltN hdigN_lt hblkN_lt
  rw [← hrSp] at hSp
  rcases hSp with ⟨hextSp, hlenSp, hlen_wSp, hltSp, hncSp, hvalSp⟩
  have hpow_succ : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
  have hstep_eq : treeStep n s b (2 * (2 ^ b - 2 ^ s)) prefs fullW t st blks =
      (⟨rSp.1, pair.1.done, pair.1.rem, pair.1.wMap⟩, rSp.2) := rfl
  dsimp only
  rw [hstep_eq]
  dsimp only
  refine ⟨hextDN.trans hextSp, simInv_ext hinvN hextSp, ?_, hdoneN, by omega, hremN,
          by omega, hltSp, ?_, ?_⟩
  · omega
  · intro x z hne u hu
    rw [hvalSp (csVec x z) (csVec_length x z) u (by omega),
        hextDN.wire_eq (csVec x z) (csVec_length x z) _ (hblk_lt _ (getD_mem blks (u / 2) 0 (by omega))),
        hblk_prop x z hne (u / 2) (by omega),
        hvalN_prop x z hne,
        hextN.wire_eq (csVec x z) (csVec_length x z) rDig.2 hltD,
        hdig_prop x z hne, hj_eq]
    have hdiv2 : (prefLen z + 1) / 2 / 2 ^ (b - t) = ((prefLen z + 1) / 2 / 2 ^ j) / 2 := by
      rw [hbt_eq, pow_succ, ← Nat.div_div_eq_div_mul]
    rw [hdiv2]
    apply Bool.eq_iff_iff.mpr
    by_cases hmod : u % 2 = 0
    · simp only [hmod, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
      omega
    · simp only [hmod, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
      omega
  · intro x u hu
    constructor
    · intro hts1
      have hts : t < b - s := by omega
      have hexact_univ : ∀ w < 2 ^ t,
          (wiresFrom st.gs (csVec x (Finset.univ : Finset (Fin m)))).getD (blks.getD w 0) false =
            decide ((prefLen (Finset.univ : Finset (Fin m)) + 1) / 2 / 2 ^ (b - t) = w) := by
        intro w hw; rw [hpref_univ]; exact (hblk_univ x w hw).1 hts
      have hdig_u := hdig_val_of_exact x Finset.univ hexact_univ
      rw [hpref_univ] at hdig_u
      rw [hvalSp (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) u (by omega),
          hextDN.wire_eq (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) _ (hblk_lt _ (getD_mem blks (u / 2) 0 (by omega))),
          (hblk_univ x (u / 2) (by omega)).1 hts,
          hvalN_univ hts x,
          hextN.wire_eq (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) rDig.2 hltD,
          hdig_u, hj_eq]
      have hdiv2 : (2 ^ b - 2 ^ s) / 2 ^ (b - t) = ((2 ^ b - 2 ^ s) / 2 ^ j) / 2 := by
        rw [hbt_eq, pow_succ, ← Nat.div_div_eq_div_mul]
      rw [hdiv2]
      apply Bool.eq_iff_iff.mpr
      by_cases hmod : u % 2 = 0
      · simp only [hmod, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        omega
      · simp only [hmod, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq]
        omega
    · intro hge1 hult
      rw [hvalSp (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) u (by omega),
          hextDN.wire_eq (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) _ (hblk_lt _ (getD_mem blks (u / 2) 0 (by omega)))]
      by_cases hts : t < b - s
      · have hteq : t + 1 = b - s := by omega
        have hj_eq_s : j = s := by omega
        have hbt_eq_s1 : b - t = s + 1 := by omega
        have hexact_univ : ∀ w < 2 ^ t,
            (wiresFrom st.gs (csVec x (Finset.univ : Finset (Fin m)))).getD (blks.getD w 0) false =
              decide ((prefLen (Finset.univ : Finset (Fin m)) + 1) / 2 / 2 ^ (b - t) = w) := by
          intro w hw; rw [hpref_univ]; exact (hblk_univ x w hw).1 hts
        have hdig_u := hdig_val_of_exact x Finset.univ hexact_univ
        rw [hpref_univ] at hdig_u
        rw [(hblk_univ x (u / 2) (by omega)).1 hts,
            hvalN_univ hts x,
            hextN.wire_eq (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) rDig.2 hltD,
            hdig_u]
        have hdiv_s : (2 ^ b - 2 ^ s) / 2 ^ s = 2 ^ (b - s) - 1 := by
          have hpow : 2 ^ b = 2 ^ (b - s) * 2 ^ s := by rw [← pow_add]; congr 1; omega
          have hsub : 2 ^ b - 2 ^ s = (2 ^ (b - s) - 1) * 2 ^ s := by
            rw [Nat.sub_mul, one_mul, hpow]
          rw [hsub, Nat.mul_div_cancel _ (Nat.pow_pos (by omega))]
        have hdiv2 : (2 ^ b - 2 ^ s) / 2 ^ (b - t) = ((2 ^ b - 2 ^ s) / 2 ^ j) / 2 := by
          rw [hbt_eq, pow_succ, ← Nat.div_div_eq_div_mul]
        have hu_lt_div : u < (2 ^ b - 2 ^ s) / 2 ^ j := by
          rw [hj_eq] at hult
          rw [hj_eq_s, hdiv_s]
          have hpow : 2 ^ b = 2 ^ (b - s) * 2 ^ s := by rw [← pow_add]; congr 1; omega
          have hsub : 2 ^ b - 2 ^ s = (2 ^ (b - s) - 1) * 2 ^ s := by rw [Nat.sub_mul, one_mul, hpow]
          rw [hj_eq_s, hsub] at hult
          exact lt_of_mul_lt_mul_right hult (Nat.zero_le _)
        rw [hdiv2]
        apply Bool.eq_false_iff.mpr
        intro hand
        rcases Bool.and_eq_true _ _ |>.mp hand with ⟨h1, h2⟩
        have h1' := of_decide_eq_true h1
        by_cases hmod : u % 2 = 0
        · simp only [hmod, ↓reduceIte, Bool.not_eq_true', decide_eq_false_iff_not] at h2
          omega
        · simp only [hmod, ↓reduceIte, decide_eq_true_eq] at h2
          omega
      · have hge : b - s ≤ t := by omega
        by_cases hmod : u % 2 = 0
        · have hu2_lt : (u / 2) * 2 ^ (b - t) < 2 ^ b - 2 ^ s := by
            have hu2 : 2 * (u / 2) = u := by omega
            have heq : (u / 2) * 2 ^ (b - t) = u * 2 ^ (b - (t + 1)) := by
              rw [hpow_bt, hj_eq]
              calc (u / 2) * (2 * 2 ^ j) = (2 * (u / 2)) * 2 ^ j := by ring
                _ = u * 2 ^ j := by rw [hu2]
            rw [heq]; exact hult
          rw [(hblk_univ x (u / 2) (by omega)).2 hge hu2_lt, Bool.false_and]
        · rw [if_neg hmod, hextN.wire_eq (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) rDig.2 hltD,
              hdig_univ_ge hge x, Bool.and_false]

lemma treeLoop_spec {n s b : ℕ} (hsb : s < b) {D : Circuit}
    (hfitD : FanInTwo D) (hrbD : ReadsBack (n + 2) D)
    (prefs : List ℕ) (fullW : ℕ) (gs0 : List Gate) (wMap0 : List ℕ)
    (hpref_len : prefs.length = 2 * (2 ^ b - 2 ^ s) + 1)
    (hpref_lt : ∀ w ∈ prefs, w < (n + 2 * (2 ^ b - 2 ^ s) + 2) + gs0.length)
    (hpref_val : ∀ (x : Finset (Fin n)) (z : Finset (Fin (2 * (2 ^ b - 2 ^ s)))) (t : ℕ),
      t ≤ 2 * (2 ^ b - 2 ^ s) →
      (wiresFrom gs0 (csVec x z)).getD (prefs.getD t 0) false = decide (t ≤ prefLen z))
    (hfull_lt : fullW < (n + 2 * (2 ^ b - 2 ^ s) + 2) + gs0.length)
    (hfull_val : ∀ (x : Finset (Fin n)) (z : Finset (Fin (2 * (2 ^ b - 2 ^ s)))),
      (wiresFrom gs0 (csVec x z)).getD fullW false = decide (z = Finset.univ))
    (hinv0 : SimInv n (2 * (2 ^ b - 2 ^ s)) D ⟨gs0, [], D.gates, wMap0⟩) :
    ∀ t, t ≤ b →
      let m := 2 * (2 ^ b - 2 ^ s)
      let res := treeLoop n s b m prefs fullW t ⟨gs0, [], D.gates, wMap0⟩ [n + m + 1]
      Extends (n + m + 2) gs0 res.1.gs ∧
      SimInv n m D res.1 ∧
      res.1.gs.length ≤ gs0.length + res.1.done.length + 4 * (2 ^ t - 1) + 2 * t ∧
      notCount ⟨res.1.gs, 0⟩ = notCount ⟨gs0, 0⟩ + t ∧
      notCount ⟨res.1.rem, 0⟩ = notCount D - (if t ≤ b - s then 0 else t - (b - s)) ∧
      res.2.length = 2 ^ t ∧
      (∀ w ∈ res.2, w < (n + m + 2) + res.1.gs.length) ∧
      (∀ (x : Finset (Fin n)) (z : Finset (Fin m)), z ≠ Finset.univ →
        ∀ u < 2 ^ t, (wiresFrom res.1.gs (csVec x z)).getD (res.2.getD u 0) false =
          decide ((prefLen z + 1) / 2 / 2 ^ (b - t) = u)) ∧
      (∀ (x : Finset (Fin n)) (u : ℕ), u < 2 ^ t →
        (t < b - s → (wiresFrom res.1.gs (csVec x (Finset.univ : Finset (Fin m)))).getD (res.2.getD u 0) false =
          decide ((2 ^ b - 2 ^ s) / 2 ^ (b - t) = u)) ∧
        (b - s ≤ t → u * 2 ^ (b - t) < 2 ^ b - 2 ^ s →
          (wiresFrom res.1.gs (csVec x (Finset.univ : Finset (Fin m)))).getD (res.2.getD u 0) false = false)) := by
  intro t
  induction t with
  | zero =>
    intro _
    dsimp only [treeLoop]
    refine ⟨Extends.refl _ gs0, hinv0, by simp, by simp, by simp [notCount], rfl, ?_, ?_, ?_⟩
    · intro w hw; simp only [List.mem_singleton] at hw; subst hw; omega
    · intro x z _ u hu
      have hu0 : u = 0 := by simp at hu; omega
      subst hu0
      change (wiresFrom gs0 (csVec x z)).getD (n + 2 * (2 ^ b - 2 ^ s) + 1) false = _
      rw [wiresFrom_getD_lt gs0 (csVec x z) _ (by rw [csVec_length]; omega), csVec_getD_true]
      have hpl := prefLen_le z
      have hpos_s : 0 < 2 ^ s := Nat.pow_pos (by omega)
      have hlt_sb : 2 ^ s < 2 ^ b := Nat.pow_lt_pow_right (by omega) hsb
      have hlt : (prefLen z + 1) / 2 < 2 ^ b := by omega
      simp [Nat.div_eq_of_lt hlt]
    · intro x u hu
      have hu0 : u = 0 := by simp at hu; omega
      subst hu0
      constructor
      · intro _
        change (wiresFrom gs0 (csVec x (Finset.univ : Finset (Fin (2 * (2 ^ b - 2 ^ s)))))).getD
          (n + 2 * (2 ^ b - 2 ^ s) + 1) false = _
        rw [wiresFrom_getD_lt gs0 (csVec x (Finset.univ : Finset (Fin (2 * (2 ^ b - 2 ^ s))))) _ (by rw [csVec_length]; omega),
            csVec_getD_true]
        have hlt : 2 ^ b - 2 ^ s < 2 ^ b := by
          have : 0 < 2 ^ s := Nat.pow_pos (by omega)
          have : 2 ^ s < 2 ^ b := Nat.pow_lt_pow_right (by omega) hsb
          omega
        simp [Nat.div_eq_of_lt hlt]
      · intro hge; omega
  | succ t ih =>
    intro ht
    dsimp only [treeLoop]
    set res := treeLoop n s b (2 * (2 ^ b - 2 ^ s)) prefs fullW t ⟨gs0, [], D.gates, wMap0⟩ [n + 2 * (2 ^ b - 2 ^ s) + 1] with hres
    have hprev := ih (by omega)
    dsimp only at hprev
    rw [← hres] at hprev
    rcases hprev with ⟨hext1, hinv1, hsz1, hnc1, hrem1, hlen1, hlt1, hprop1, huniv1⟩
    have hstep := treeStep_spec hsb hfitD hrbD prefs fullW gs0 hpref_len hpref_lt hpref_val
      hfull_lt hfull_val t (by omega) res.1 res.2 hext1 hinv1 hlen1 hlt1 hprop1 huniv1
    rcases hstep with ⟨hext2, hinv2, hsz2, hdone2, hnc2, hrem2, hlen2, hlt2, hprop2, huniv2⟩
    refine ⟨hext1.trans hext2, hinv2, ?_, by omega, ?_, hlen2, hlt2, hprop2, huniv2⟩
    · have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; ring
      have hpos : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
      omega
    · rw [hrem2, hrem1]
      split_ifs <;> omega

end TreeDecoder

section MainProof

lemma two_pow_le_m {s b : ℕ} (hsb : s < b) : 2 ^ b ≤ 2 * (2 ^ b - 2 ^ s) := by
  have h1 : 2 ^ s ≤ 2 ^ (b - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have h2 : 2 ^ b = 2 * 2 ^ (b - 1) := by
    have : b = (b - 1) + 1 := by omega
    conv_lhs => rw [this, pow_succ]
    ring
  omega

lemma main_std (n s b : ℕ) (hsb : s < b) (D : Circuit)
    (hfitD : FanInTwo D) (hrbD : ReadsBack (n + 2) D) (houtD : D.output < n + 2 + D.size) :
    let m := 2 * (2 ^ b - 2 ^ s)
    ∃ C : Circuit,
      FanInTwo C ∧ ReadsBack (n + m + 2) C ∧ C.output < n + m + 2 + C.size ∧
      C.size ≤ D.size + 32 * (m + 1) ∧
      notCount C = b + (notCount D - s) ∧
      ∃ p : Fin (n + 2 + D.size) → Fin (n + m + 2 + C.size),
        ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
          (z = Finset.univ → C.eval (csVec x z) = D.eval (dsVec x) ∧
            ∀ k, (C.wires (csVec x z)).getD (p k).val false = (D.wires (dsVec x)).getD k.val false) ∧
          ∀ j : Fin m, (∀ i : Fin m, i < j → i ∈ z) → j ∉ z →
            C.eval (csVec x z) = @decide (j.val % 2 = 0) (Classical.propDecidable _) := by
  let m := 2 * (2 ^ b - 2 ^ s)
  have hm_ge : 2 ^ b ≤ m := two_pow_le_m hsb
  have hhalf_eq : 2 ^ b - 2 ^ s = m / 2 := by dsimp only [m]; omega
  set rP := buildPrefixes n m m [] with hrP
  have hP := buildPrefixes_spec n m m (le_refl m) []
  rw [← hrP] at hP
  rcases hP with ⟨hextP, hlenP, hlen_wP, hltP, hncP, hvalP⟩
  simp only [List.length_nil, zero_add, notCount_nil] at hlenP hncP
  let fullW := rP.2.getD m 0
  have hfull_lt : fullW < (n + m + 2) + rP.1.length := hltP _ (getD_mem rP.2 m 0 (by omega))
  have hfull_val : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (wiresFrom rP.1 (csVec x z)).getD fullW false = decide (z = Finset.univ) := by
    intro x z
    rw [hvalP x z m (le_refl m)]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, ← prefLen_eq_m_iff]
    have := prefLen_le z
    omega
  let wMap0 : List ℕ := List.range n ++ [n + m, n + m + 1]
  have hinv0 : SimInv n m D ⟨rP.1, [], D.gates, wMap0⟩ := by
    refine ⟨rfl, by simp [wMap0], ?_, ?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with hw1 | hw2
      · rw [List.mem_range] at hw1; omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw2
        rcases hw2 with rfl | rfl <;> omega
    · intro x k hk
      simp only [List.length_nil, add_zero] at hk
      rw [wiresFrom_nil]
      by_cases hkn : k < n
      · have hget : wMap0.getD k 0 = k := by
          dsimp only [wMap0]
          rw [getD_append_left _ _ k 0 (by simp [hkn]), List.getD_eq_getElem?_getD, List.getElem?_range hkn]; rfl
        rw [hget, wiresFrom_getD_lt rP.1 (csVec x Finset.univ) k (by rw [csVec_length]; omega),
            csVec_getD_x x Finset.univ ⟨k, hkn⟩, dsVec_getD_lt x ⟨k, hkn⟩]
      · by_cases hkn0 : k = n
        · rw [hkn0]
          have hget : wMap0.getD n 0 = n + m := by
            dsimp only [wMap0]
            rw [getD_append_right _ _ n 0 (by simp), List.length_range]; simp
          rw [hget, wiresFrom_getD_lt rP.1 (csVec x Finset.univ) (n + m) (by rw [csVec_length]; omega),
              csVec_getD_false, dsVec_getD_false]
        · have hkn1 : k = n + 1 := by omega
          rw [hkn1]
          have hget : wMap0.getD (n + 1) 0 = n + m + 1 := by
            dsimp only [wMap0]
            rw [getD_append_right _ _ (n + 1) 0 (by simp), List.length_range]
            have : n + 1 - n = 1 := by omega
            simp [this]
          rw [hget, wiresFrom_getD_lt rP.1 (csVec x Finset.univ) (n + m + 1) (by rw [csVec_length]; omega),
              csVec_getD_true, dsVec_getD_true]
  set rT := treeLoop n s b m rP.2 fullW b ⟨rP.1, [], D.gates, wMap0⟩ [n + m + 1] with hrT
  have hT := treeLoop_spec hsb hfitD hrbD rP.2 fullW rP.1 wMap0 hlen_wP hltP hvalP hfull_lt hfull_val hinv0 b (le_refl b)
  dsimp only at hT
  rw [← hrT] at hT
  rcases hT with ⟨hextT, hinvT, hszT, hncT, hremT, hlenT, hltT, hpropT, hunivT⟩
  have hremT' : notCount ⟨rT.1.rem, 0⟩ = notCount D - s := by
    rw [hremT]; split_ifs <;> omega
  set stR := simRest (n + m + 2) rT.1 with hstR
  have hR := simRestAux_spec hfitD hrbD rT.1.rem rT.1.gs rT.1.done rT.1.wMap hinvT
  dsimp only [simRest, m] at hstR
  dsimp only at hR
  rw [← hstR] at hR
  rcases hR with ⟨hextR, hinvR, hremR, hszR, hncR⟩
  have hdoneR : stR.done = D.gates := by
    have := hinvR.1; rw [hremR, List.append_nil] at this; exact this
  have hglR := hextR.length_le
  let half := 2 ^ b - 2 ^ s
  have h2s_pos : 0 < 2 ^ s := Nat.pow_pos (by omega)
  have h2s_lt : 2 ^ s < 2 ^ b := Nat.pow_lt_pow_right (by omega) hsb
  have hhalf_le : half ≤ 2 ^ b := by dsimp only [half]; omega
  have hm_eq_half : m = 2 * half := rfl
  let blksHalf := rT.2.take half
  let evenPrefs := (List.range half).map (fun u => rP.2.getD (2 * u) 0)
  have hbh_len : blksHalf.length = half := by
    dsimp only [blksHalf]; rw [List.length_take, hlenT]; omega
  have hep_len : evenPrefs.length = half := by simp [evenPrefs]
  have hbh_lt : ∀ w ∈ blksHalf, w < (n + m + 2) + stR.gs.length := fun w hw =>
    lt_of_lt_of_le (hltT w (List.mem_of_mem_take hw)) (by omega)
  have hep_lt : ∀ w ∈ evenPrefs, w < (n + m + 2) + stR.gs.length := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨u, hu, rfl⟩
    rw [List.mem_range] at hu
    have hlt := hltP _ (getD_mem rP.2 (2 * u) 0 (by omega))
    have hglTR := (hextT.trans hextR).length_le
    omega
  set rEv := orAndPairs (n + m + 2) stR.gs (n + m) blksHalf evenPrefs with hrEv
  have hEv := orAndPairs_spec (n + m + 2) blksHalf evenPrefs stR.gs (n + m) (by omega) (by omega) hbh_lt hep_lt
  dsimp only at hEv; rw [← hrEv] at hEv
  rcases hEv with ⟨hextEv, hlenEv, hltEv, hncEv, hvalEv⟩
  have hglT := hextT.length_le
  have hfull_ev : fullW < (n + m + 2) + rEv.1.length := by omega
  have hdOut_lt_wMap : D.output < stR.wMap.length := by
    rw [hinvR.2.1, hdoneR]; exact houtD
  let dOutW := stR.wMap.getD D.output 0
  have hdOut_lt : dOutW < (n + m + 2) + rEv.1.length := by
    have := hinvR.2.2.1 _ (getD_mem stR.wMap D.output 0 hdOut_lt_wMap)
    omega
  set rGated := emitAnd (n + m + 2) rEv.1 fullW dOutW with hrGated
  have hGated := emitAnd_spec (n + m + 2) rEv.1 fullW dOutW hfull_ev hdOut_lt
  dsimp only at hGated; rw [← hrGated] at hGated
  rcases hGated with ⟨hextG, hlenG, hltG, hncG, hvalG⟩
  set rFinal := emitOr (n + m + 2) rGated.1 rEv.2 rGated.2 with hrFinal
  have hFinal := emitOr_spec (n + m + 2) rGated.1 rEv.2 rGated.2 (by omega) hltG
  dsimp only at hFinal; rw [← hrFinal] at hFinal
  rcases hFinal with ⟨hextF, hlenF, hltF, hncF, hvalF⟩
  have hextAll : Extends (n + m + 2) [] rFinal.1 :=
    ((((hextP.trans hextT).trans hextR).trans hextEv).trans hextG).trans hextF
  rcases hextAll with ⟨e, heq, hfitC, hrbC⟩
  simp only [List.nil_append, List.length_nil, add_zero] at heq hfitC hrbC
  subst heq
  let C : Circuit := ⟨rFinal.1, rFinal.2⟩
  have hC_sz : C.size ≤ D.size + 32 * (m + 1) := by
    have hD_len : stR.done.length = D.size := by rw [hdoneR]; rfl
    have hb_le : b ≤ 2 ^ b := le_of_lt Nat.lt_two_pow_self
    change rFinal.1.length ≤ D.size + 32 * (m + 1)
    omega
  have hC_nc : notCount C = b + (notCount D - s) := by
    change notCount ⟨rFinal.1, 0⟩ = b + (notCount D - s)
    omega
  have hext_stR_C : Extends (n + m + 2) stR.gs C.gates := (hextEv.trans hextG).trans hextF
  have hgl_stR_C := hext_stR_C.length_le
  let p : Fin (n + 2 + D.size) → Fin (n + m + 2 + C.size) := fun k =>
    ⟨stR.wMap.getD k.val 0, by
      have hk : k.val < stR.wMap.length := by rw [hinvR.2.1, hdoneR]; exact k.isLt
      have := hinvR.2.2.1 _ (getD_mem stR.wMap k.val 0 hk)
      change stR.wMap.getD k.val 0 < n + m + 2 + C.gates.length
      exact lt_of_lt_of_le this (by omega)⟩
  refine ⟨C, hfitC, hrbC, hltF, hC_sz, hC_nc, p, fun x z => ?_⟩
  have hEv_eval : (wiresFrom rEv.1 (csVec x z)).getD rEv.2 false =
      (List.range half).any fun u =>
        (wiresFrom rT.1.gs (csVec x z)).getD (rT.2.getD u 0) false &&
        decide (2 * u ≤ prefLen z) := by
    rw [hvalEv (csVec x z) (csVec_length x z),
        wiresFrom_getD_lt stR.gs (csVec x z) (n + m) (by rw [csVec_length]; omega),
        csVec_getD_false, Bool.false_or, hbh_len]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true]
    constructor <;> rintro ⟨u, hu, h1, h2⟩ <;> refine ⟨u, hu, ?_, ?_⟩
    · have hgt1 : blksHalf.getD u 0 = rT.2.getD u 0 := by
        dsimp only [blksHalf]; simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hu]
      rw [hgt1, hextR.wire_eq (csVec x z) (csVec_length x z) _ (hltT _ (getD_mem rT.2 u 0 (by omega)))] at h1
      exact h1
    · have hgt2 : evenPrefs.getD u 0 = rP.2.getD (2 * u) 0 := by
        dsimp only [evenPrefs]; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]; rfl
      rw [hgt2, (hextT.trans hextR).wire_eq (csVec x z) (csVec_length x z) _ (hltP _ (getD_mem rP.2 (2 * u) 0 (by omega))),
          hvalP x z (2 * u) (by omega)] at h2
      exact h2
    · have hgt1 : blksHalf.getD u 0 = rT.2.getD u 0 := by
        dsimp only [blksHalf]; simp [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hu]
      rw [hgt1, hextR.wire_eq (csVec x z) (csVec_length x z) _ (hltT _ (getD_mem rT.2 u 0 (by omega)))]
      exact h1
    · have hgt2 : evenPrefs.getD u 0 = rP.2.getD (2 * u) 0 := by
        dsimp only [evenPrefs]; rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]; rfl
      rw [hgt2, (hextT.trans hextR).wire_eq (csVec x z) (csVec_length x z) _ (hltP _ (getD_mem rP.2 (2 * u) 0 (by omega))),
          hvalP x z (2 * u) (by omega)]
      exact h2
  have hC_eval : C.eval (csVec x z) =
      ((wiresFrom rEv.1 (csVec x z)).getD rEv.2 false ||
        (decide (z = Finset.univ) && (wiresFrom stR.gs (csVec x z)).getD dOutW false)) := by
    change (wiresFrom rFinal.1 (csVec x z)).getD rFinal.2 false = _
    rw [hvalF (csVec x z) (csVec_length x z),
        hextG.wire_eq (csVec x z) (csVec_length x z) rEv.2 hltEv,
        hvalG (csVec x z) (csVec_length x z),
        ((hextT.trans hextR).trans hextEv).wire_eq (csVec x z) (csVec_length x z) fullW hfull_lt,
        hfull_val x z,
        hextEv.wire_eq (csVec x z) (csVec_length x z) dOutW
          (hinvR.2.2.1 _ (getD_mem stR.wMap D.output 0 hdOut_lt_wMap))]
  constructor
  · intro hzu
    subst hzu
    have hEv_false : (wiresFrom rEv.1 (csVec x (Finset.univ : Finset (Fin m)))).getD rEv.2 false = false := by
      rw [hEv_eval]
      apply Bool.eq_false_iff.mpr
      intro htrue
      rcases List.any_eq_true.mp htrue with ⟨u, hu, hand⟩
      rw [List.mem_range] at hu
      have h1 := (Bool.and_eq_true _ _ |>.mp hand).1
      have h0 := (hunivT x u (by omega)).2 (by omega) (by simp only [Nat.sub_self, pow_zero, mul_one]; exact hu)
      rw [h0] at h1; cases h1
    have hsim_all : ∀ k : Fin (n + 2 + D.size),
        (C.wires (csVec x (Finset.univ : Finset (Fin m)))).getD (p k).val false = (D.wires (dsVec x)).getD k.val false := by
      intro k
      have hk : k.val < stR.wMap.length := by rw [hinvR.2.1, hdoneR]; exact k.isLt
      have h1 := hinvR.2.2.2 x k.val (by rw [hdoneR]; exact k.isLt)
      rw [hdoneR] at h1
      change (wiresFrom C.gates (csVec x (Finset.univ : Finset (Fin m)))).getD (stR.wMap.getD k.val 0) false = _
      rw [hext_stR_C.wire_eq (csVec x (Finset.univ : Finset (Fin m))) (csVec_length x _) _ (hinvR.2.2.1 _ (getD_mem stR.wMap k.val 0 hk))]
      exact h1
    refine ⟨?_, hsim_all⟩
    rw [hC_eval, hEv_false]
    simp only [Bool.false_or, decide_true, Bool.true_and]
    have h1 := hinvR.2.2.2 x D.output (by rw [hdoneR]; exact houtD)
    rw [hdoneR] at h1
    exact h1
  · intro j hprev hmiss
    have hne : z ≠ Finset.univ := fun h => hmiss (h ▸ Finset.mem_univ j)
    have hpl_j : prefLen z = j.val := prefLen_eq_of_first_miss hprev hmiss
    rw [hC_eval, decide_eq_false hne, Bool.false_and, Bool.or_false, hEv_eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨u, hu, h1, h2⟩
      rw [hpropT x z hne u (by omega), hpl_j] at h1
      simp only [Nat.sub_self, pow_zero, Nat.div_one, decide_eq_true_eq] at h1
      rw [hpl_j] at h2
      omega
    · intro hmod
      have hj_lt := j.isLt
      refine ⟨j.val / 2, by omega, ?_, ?_⟩
      · rw [hpropT x z hne (j.val / 2) (by omega), hpl_j]
        simp only [Nat.sub_self, pow_zero, Nat.div_one, decide_eq_true_eq]
        omega
      · rw [hpl_j]; omega

lemma main_bridge :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (n s b : Nat), s < b →
      let m := 2*(2^b-2^s)
      let bits := fun (w : Nat) (x : Finset (Fin w)) => List.ofFn (fun i : Fin w => decide (i ∈ x))
      let valid := fun (w : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (w+2) D ∧
          D.output < w+2+D.size
      ∀ D, valid n D → ∃ C, valid (n+m) C ∧
        C.size ≤ D.size+32*(m+1) ∧
        PEqualNP.NotBracket.notCount C = b + (PEqualNP.NotBracket.notCount D - s) ∧
        ∃ p : Fin (n+2+D.size) → Fin (n+m+2+C.size), ∀ x (z : Finset (Fin m)),
          let ds := bits n x ++ [false,true]
          let cs := bits n x ++ bits m z ++ [false,true]
          (z = Finset.univ → C.eval cs = D.eval ds ∧
            ∀ k, (C.wires cs).getD (p k).val false = (D.wires ds).getD k.val false) ∧
          ∀ j : Fin m, (∀ i : Fin m, i < j → i ∈ z) → j ∉ z → C.eval cs = decide (j.val % 2 = 0) := by
  intro n s b hsb
  dsimp only
  intro D ⟨h1, h2, h3⟩
  rcases main_std n s b hsb D h1 h2 h3 with ⟨C, hc1, hc2, hc3, hsz, hnc, p, hspec⟩
  exact ⟨C, ⟨hc1, hc2, hc3⟩, hsz, hnc, p, hspec⟩

end MainProof

end PEqualNP.Outside.L_lib_1285_aux

theorem PEqualNP.Outside.L_lib_1285 :
letI : ∀ P : Prop, Decidable P := Classical.propDecidable
∀ (n s b : Nat), s < b →
  let m := 2*(2^b-2^s)
  let bits := fun (w : Nat) (x : Finset (Fin w)) => List.ofFn (fun i : Fin w => decide (i ∈ x))
  let valid := fun (w : Nat) (D : PEqualNP.CircuitLowerBounds.Circuit) =>
    PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (w+2) D ∧
      D.output < w+2+D.size
  ∀ D, valid n D → ∃ C, valid (n+m) C ∧
    C.size ≤ D.size+32*(m+1) ∧
    PEqualNP.NotBracket.notCount C = b + (PEqualNP.NotBracket.notCount D - s) ∧
    ∃ p : Fin (n+2+D.size) → Fin (n+m+2+C.size), ∀ x (z : Finset (Fin m)),
      let ds := bits n x ++ [false,true]
      let cs := bits n x ++ bits m z ++ [false,true]
      (z = Finset.univ → C.eval cs = D.eval ds ∧
        ∀ k, (C.wires cs).getD (p k).val false = (D.wires ds).getD k.val false) ∧
      ∀ j : Fin m, (∀ i : Fin m, i < j → i ∈ z) → j ∉ z → C.eval cs = decide (j.val % 2 = 0) :=
  PEqualNP.Outside.L_lib_1285_aux.main_bridge
