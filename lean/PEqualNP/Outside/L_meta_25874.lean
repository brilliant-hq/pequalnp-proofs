import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_25644
import PEqualNP.Outside.L_meta_25872
import PEqualNP.Outside.L_meta_25806

/-!
  L-meta-25874 glue (in progress).

  Plan, following the desk sketch:
  1. Contract unary (fan-in ≤ 1) gates; the two-input gate count is unchanged.
     The contracted form is a `BinaryCircuit` (arbitrary `Bool → Bool → Bool` ops)
     plus a leftover output inversion, and still represents `G`.
     Done via `L_meta_25806_aux.Normalize.normalize_live`.
  2. Cut the binary wiring with `L_meta_25644` on the AND-shadow
     `binarySkeleton` of the live contracted circuit (pure trees and one-entry
     chains, plus marked components).
  3. A 5-to-8 leaf prefix would give three nonzero triple cuts through one entry,
     contradicting `rich`. So each piece has at most two names per bank.
  4. Two-state response supports (via `L_meta_25872`) are nested or disjoint,
     giving an affordable pair in the sense of `bounded` (charged to `hr` / `hc`).
  5. Mark matching endpoints and unread names. With excess `d`, shared raw `u`,
     shared gates `P` and marked components `e`,
       w ≤ marks + u + 2*P + 2 + 4*(d + u + P) - 4*e
     together with `u + P ≤ d` and `e ≥ 1` (when there is any marked read/NOT).
  6. Close the arithmetic to
       11*(n+m) ≤ 10*(# two-input gates) + 26 + 2*(hr+hc).

  Supporting lemmas 25644, 25872 and 25806 are on main and lake-build cleanly.
-/

namespace PEqualNP.Outside.L_meta_25874_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_25806_aux
open PEqualNP.Outside.L_meta_25806_aux.Normalize
open PEqualNP.Represents

/-- The counting relation in the desk sketch, after `u+P ≤ d` and `e ≥ 1`. -/
theorem sketch_count {w marks u P d e : ℕ}
    (h : w + 4 * e ≤ marks + u + 2 * P + 2 + 4 * (d + u + P))
    (hup : u + P ≤ d) (he : 1 ≤ e) :
    w + 2 ≤ marks + 5 * u + 6 * P + 4 * d := by
  nlinarith

lemma length_oneEach {n m : ℕ} (u : Fin n) (v : Fin m) :
    (oneEach u v).length = n + m := by
  simp [oneEach]

lemma getD_oneEach_left {n m : ℕ} (u : Fin n) (v : Fin m) (k : ℕ) (hk : k < n) :
    (oneEach u v).getD k false = decide (k = u.val) := by
  unfold oneEach
  have hlt : k < (List.ofFn (fun i : Fin n => decide (i = u))).length := by
    simpa using hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, List.getElem?_ofFn]
  simp [hk, Fin.ext_iff]

lemma getD_oneEach_right {n m : ℕ} (u : Fin n) (v : Fin m) (k : ℕ)
    (hnk : n ≤ k) (hk : k < n + m) :
    (oneEach u v).getD k false = decide (k - n = v.val) := by
  have hlen : (oneEach u v).length = n + m := length_oneEach u v
  have hkt : k < (oneEach u v).length := by omega
  unfold oneEach at hlen hkt ⊢
  have hleft : (List.ofFn (fun i : Fin n => decide (i = u))).length = n := by simp
  have hge : (List.ofFn (fun i : Fin n => decide (i = u))).length ≤ k := by
    omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right hge]
  have hk' : k - n < m := by omega
  simp [hleft, List.getElem?_ofFn, hk', Fin.ext_iff]

lemma eval_empty (B : BinaryCircuit) (h : B.gates = []) (x : List Bool) :
    B.eval x = x.getD B.output false := by
  simp [BinaryCircuit.eval, BinaryCircuit.wires, h]

/-- A matrix that depends only on the row cannot be `rich` when there are at least
three rows and three columns. -/
lemma rich_not_row_function {n m : ℕ} {G : Fin n → Fin m → Bool}
    (hn : 3 ≤ n) (_hm : 3 ≤ m)
    (hrich : ∀ (i j k : Fin n), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (G j col != G i col) = x ∧ (G k col != G i col) = y)).card)
    (f : Fin n → Bool) (hG : ∀ u v, G u v = f u) : False := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by
    intro h; apply_fun Fin.val at h; simp [i, j] at h
  have hik : i ≠ k := by
    intro h; apply_fun Fin.val at h; simp [i, k] at h
  have hjk : j ≠ k := by
    intro h; apply_fun Fin.val at h; simp [j, k] at h
  have hconst (x y : Bool) :
      (Finset.univ.filter (fun col : Fin m =>
        (G j col != G i col) = x ∧ (G k col != G i col) = y)) =
      if (f j != f i) = x ∧ (f k != f i) = y then Finset.univ else ∅ := by
    ext col
    by_cases h : (f j != f i) = x ∧ (f k != f i) = y
    · simp [hG, h]
    · simp [hG, h]
  have htf := hrich i j k hij hik hjk true false (Or.inl rfl)
  have hft := hrich i j k hij hik hjk false true (Or.inr rfl)
  rw [hconst] at htf hft
  by_cases hpair : (f j != f i) = true ∧ (f k != f i) = false
  · have hneg : ¬((f j != f i) = false ∧ (f k != f i) = true) := by
      intro ⟨h1, _⟩
      exact Bool.noConfusion (hpair.1.symm.trans h1)
    rw [if_neg hneg] at hft
    simp at hft
  · rw [if_neg hpair] at htf
    simp at htf

/-- Live contracted circuits have every intermediate gate wire actually read,
so the AND-shadow satisfies the `hused` hypothesis of 25644. -/
lemma live_skeleton_used (N : ℕ) (B : BinaryCircuit)
    (hl : Live N B) (hpos : 0 < B.gates.length)
    (hout : B.output = N + (B.gates.length - 1)) :
    ∀ j < (binarySkeleton B).size, j + 1 < (binarySkeleton B).size →
      0 < readsIn (binarySkeleton B) (Finset.range (binarySkeleton B).size) (N + j) := by
  intro j hj hj'
  have hsz : (binarySkeleton B).size = B.gates.length := by
    simpa [BinaryCircuit.size] using binarySkeleton_size B
  rw [hsz] at hj hj'
  have hne : N + j ≠ B.output := by
    rw [hout]
    omega
  obtain ⟨k, hk, _hjk, hr⟩ := hl j hj hne
  have hk' : k ∈ Finset.range (binarySkeleton B).size := by
    simpa [hsz] using hk
  have hin : N + j ∈ (gateAt (binarySkeleton B) k).inputs := by
    rw [binarySkeleton_gate B k hk]
    simpa [eq_comm] using hr
  have hposc : 0 < (gateAt (binarySkeleton B) k).inputs.count (N + j) :=
    List.count_pos_iff.mpr hin
  let fcnt := fun t : ℕ => (gateAt (binarySkeleton B) t).inputs.count (N + j)
  have hle : fcnt k ≤ ∑ t ∈ Finset.range (binarySkeleton B).size, fcnt t :=
    Finset.single_le_sum (f := fcnt) (fun _ _ => Nat.zero_le _) hk'
  simpa [readsIn, fcnt] using (lt_of_lt_of_le hposc hle)

/-- The AND-shadow of a nonempty live binary circuit meets every structural
hypothesis of `L_meta_25644`. -/
lemma skeleton_hyps (N : ℕ) (B : BinaryCircuit)
    (hback : Back N B.gates) (hl : Live N B) (hpos : 0 < B.gates.length) :
    (∀ g ∈ (binarySkeleton B).gates,
      ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∨
      (g.op = GateOp.not ∧ g.inputs.length = 1)) ∧
    ReadsBack N (binarySkeleton B) ∧
    0 < (binarySkeleton B).size ∧
    (binarySkeleton B).output + 1 = N + (binarySkeleton B).size ∧
    (∀ j < (binarySkeleton B).size, j + 1 < (binarySkeleton B).size →
      0 < readsIn (binarySkeleton B) (Finset.range (binarySkeleton B).size) (N + j)) := by
  have hout := live_output_last N B hl hpos
  refine ⟨binarySkeleton_shape B,
    binarySkeleton_back N B (fun j hj => hback j hj), ?_, ?_, ?_⟩
  · simpa [binarySkeleton_size, BinaryCircuit.size] using hpos
  · have hsz : (binarySkeleton B).size = B.gates.length := by
      simpa [BinaryCircuit.size] using binarySkeleton_size B
    have hout' : (binarySkeleton B).output = B.output := rfl
    rw [hout', hsz, hout]
    omega
  · exact live_skeleton_used N B hl hpos hout

/-- A later gate cannot be an input of an earlier one, so the locally maximal
gate of a region is unread inside that region. -/
lemma readsIn_root_of_max (N : ℕ) (C : Circuit) (region : Finset ℕ) (k : ℕ)
    (hsub : region ⊆ Finset.range C.size)
    (hback : ReadsBack N C) (hk : k ∈ region)
    (hmax : ∀ j ∈ region, j ≤ k) :
    readsIn C region (N + k) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hjsz : j < C.size := Finset.mem_range.mp (hsub hj)
  apply List.count_eq_zero.mpr
  intro hw
  have hlt : N + k < N + j := hback j hjsz (N + k) hw
  have : j ≤ k := hmax j hj
  omega

/-- If a 25644 region is nonempty, its unique locally unread wire is the
output of the region's latest gate (never a raw input). -/
lemma tree_root_is_gate (N : ℕ) (C : Circuit) (S region : Finset ℕ) (root : ℕ)
    (hsub : region ⊆ Finset.range C.size)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1)
    (hback : ReadsBack N C) (hne : region.Nonempty) :
    ∃ top, top ∈ region ∧ root = N + top := by
  let k := region.max' hne
  have hk : k ∈ region := Finset.max'_mem region hne
  have h0 : readsIn C region (N + k) = 0 :=
    readsIn_root_of_max N C region k hsub hback hk
      (fun j hj => Finset.le_max' region j hj)
  have hin : N + k ∈ S ∪ region.image (fun t => N + t) :=
    Finset.mem_union_right S (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
  have heq : root = N + k := by
    by_contra hne'
    have := hwires (N + k) hin (Ne.symm hne')
    omega
  exact ⟨k, hk, heq⟩

/-- Gates outside a 25644 tree do not read that tree's private once-read
inputs or its internal non-root wires. -/
lemma tree_outside_unread (N : ℕ) (C : Circuit) (S E region : Finset ℕ) (root : ℕ)
    (hsub : region ⊆ Finset.range C.size)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1)
    {j w : ℕ} (hj : j < C.size) (hjout : j ∉ region)
    (hw : w ∈ (gateAt C j).inputs)
    (hpriv : w ∈ S ∪ region.image (fun k => N + k)) (hne : w ≠ root) :
    False := by
  have hread : 0 < (gateAt C j).inputs.count w := List.count_pos_iff.mpr hw
  have hinG : j ∈ Finset.range C.size := Finset.mem_range.mpr hj
  have hglob : readsIn C (Finset.range C.size) w = 1 := (hwires w hpriv hne).2
  have hloc : readsIn C region w = 1 := (hwires w hpriv hne).1
  have hdis : Disjoint region (Finset.range C.size \ region) := Finset.disjoint_sdiff
  have hunion : region ∪ (Finset.range C.size \ region) = Finset.range C.size :=
    Finset.union_sdiff_of_subset hsub
  have hsplit : readsIn C (Finset.range C.size) w =
      readsIn C region w + readsIn C (Finset.range C.size \ region) w := by
    unfold readsIn
    have hsum := Finset.sum_union (s₁ := region) (s₂ := Finset.range C.size \ region)
      (f := fun t => (gateAt C t).inputs.count w) hdis
    rw [hunion] at hsum
    exact hsum
  have hj' : j ∈ Finset.range C.size \ region := Finset.mem_sdiff.mpr ⟨hinG, hjout⟩
  have houtle : (gateAt C j).inputs.count w
      ≤ readsIn C (Finset.range C.size \ region) w :=
    Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count w)
      (fun _ _ => Nat.zero_le _) hj'
  omega

/-- Row names among a set of raw input wires. -/
def rowNames (n : ℕ) (S : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i.val ∈ S)

/-- Column names among a set of raw input wires. -/
def colNames (n m : ℕ) (S : Finset ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => n + j.val ∈ S)

lemma rowNames_colNames_card {n m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range (n + m)) :
    S.card = (rowNames n S).card + (colNames n m S).card := by
  classical
  have hsplit : S = (S.filter (fun w => w < n)) ∪ (S.filter (fun w => n ≤ w)) := by
    ext w
    constructor
    · intro hw
      have : w < n + m := Finset.mem_range.mp (hS hw)
      by_cases hwn : w < n
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hw, hwn⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw, by omega⟩)
    · intro hw
      rcases Finset.mem_union.mp hw with h | h
      · exact (Finset.mem_filter.mp h).1
      · exact (Finset.mem_filter.mp h).1
  have hdis : Disjoint (S.filter (fun w => w < n)) (S.filter (fun w => n ≤ w)) := by
    refine Finset.disjoint_left.mpr ?_
    intro w hw1 hw2
    exact (lt_irrefl _) ((Finset.mem_filter.mp hw1).2.trans_le (Finset.mem_filter.mp hw2).2)
  have hrow : (S.filter (fun w => w < n)).card = (rowNames n S).card := by
    refine Finset.card_bij (fun w hw => ⟨w, (Finset.mem_filter.mp hw).2⟩)
      (fun w hw => ?_) (fun a ha b hb h => by cases h; rfl)
      (fun i hi => ?_)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).1⟩
    · refine ⟨i.val, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩, rfl⟩
  have hcol : (S.filter (fun w => n ≤ w)).card = (colNames n m S).card := by
    refine Finset.card_bij (fun w hw => ⟨w - n, ?_⟩)
      (fun w hw => ?_) (fun a ha b hb h => ?_) (fun j hj => ?_)
    · have hw' := Finset.mem_filter.mp hw
      have : w < n + m := Finset.mem_range.mp (hS hw'.1)
      omega
    · have hw' := Finset.mem_filter.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        have : n + (w - n) = w := Nat.add_sub_of_le hw'.2
        simpa [this] using hw'.1⟩
    · have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have : a - n = b - n := Fin.val_eq_of_eq h
      omega
    · refine ⟨n + j.val, Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp hj).2, by omega⟩, ?_⟩
      ext
      simp
  have hcard : S.card =
      (S.filter (fun w => w < n)).card + (S.filter (fun w => n ≤ w)).card :=
    (congrArg Finset.card hsplit).trans (Finset.card_union_of_disjoint hdis)
  rw [hcard, hrow, hcol]

lemma sources_of_names {n m : ℕ} (S : Finset ℕ) (hS : S ⊆ Finset.range (n + m)) :
    (rowNames n S).image Fin.val ∪ (colNames n m S).image (fun j => n + j.val) = S := by
  ext w
  constructor
  · intro hw
    rcases Finset.mem_union.mp hw with h | h
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hi).2
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hj).2
  · intro hw
    have hwlt : w < n + m := Finset.mem_range.mp (hS hw)
    by_cases hwn : w < n
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨⟨w, hwn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩, rfl⟩)
    · have hge : n ≤ w := by omega
      refine Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨⟨w - n, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩)
      · simpa [Nat.add_sub_of_le hge] using hw
      · simp [Nat.add_sub_of_le hge]

/-- Three distinct elements of a finset with card at least 3. -/
lemma rowNames_filter_card {n m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range (n + m)) :
    (rowNames n S).card = (S.filter (fun w => w < n)).card := by
  refine Eq.symm (Finset.card_bij (fun w hw => ⟨w, (Finset.mem_filter.mp hw).2⟩)
    (fun w hw => ?_) (fun a ha b hb h => by cases h; rfl)
    (fun i hi => ?_))
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).1⟩
  · exact ⟨i.val, Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, i.isLt⟩, rfl⟩

lemma colNames_filter_card {n m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range (n + m)) :
    (colNames n m S).card = (S.filter (fun w => n ≤ w)).card := by
  refine Eq.symm (Finset.card_bij (fun w hw => ⟨w - n, ?_⟩)
    (fun w hw => ?_) (fun a ha b hb h => ?_) (fun j hj => ?_))
  · have hw' := Finset.mem_filter.mp hw
    have : w < n + m := Finset.mem_range.mp (hS hw'.1)
    omega
  · have hw' := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
      have : n + (w - n) = w := Nat.add_sub_of_le hw'.2
      simpa [this] using hw'.1⟩
  · have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have : a - n = b - n := Fin.val_eq_of_eq h
    omega
  · refine ⟨n + j.val, Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hj).2, by omega⟩, ?_⟩
    ext
    simp

lemma three_mem_of_card {α : Type*} [DecidableEq α] {s : Finset α}
    (h : 3 ≤ s.card) : ∃ a b c, a ∈ s ∧ b ∈ s ∧ c ∈ s ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  obtain ⟨t, hts, hcard⟩ := Finset.exists_subset_card_eq h
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
  exact ⟨a, b, c, hts (by simp), hts (by simp), hts (by simp), hab, hac, hbc⟩

/-- If a 1-bit factorization leaves some nonzero triple pattern missing
outside a set of at most four columns, richness is contradicted when
there are three row names. -/
lemma bank_card_le_two_of_factor {n m : ℕ} {G : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {T : Finset (Fin m)}
    (hrich : ∀ (i j k : Fin n), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (G j col != G i col) = x ∧ (G k col != G i col) = y)).card)
    (hT : T.card ≤ 4)
    (t : Fin m → Bool) (q : Fin n → Bool → Bool) (U : Fin m → Bool → Bool)
    (hfactor : ∀ a ∈ R, ∀ x, x ∉ T → G a x = U x (q a (t x))) :
    R.card ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ R.card := by omega
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := three_mem_of_card h3
  obtain ⟨p, r, hnz, hmiss⟩ :=
    PEqualNP.Outside.L_meta_25806_aux.factored_triple_missing
      G a b c {x | x ∈ T} (q a) (q b) (q c) t (fun x => U x)
      (fun x hx => hfactor a ha x (by exact hx))
      (fun x hx => hfactor b hb x (by exact hx))
      (fun x hx => hfactor c hc x (by exact hx))
  have hle := hrich a b c hab hac hbc p r hnz
  have hsub :
      (Finset.univ.filter (fun col : Fin m =>
        (G b col != G a col) = p ∧ (G c col != G a col) = r)) ⊆ T := by
    intro col hcol
    have ⟨_, hpat⟩ := Finset.mem_filter.mp hcol
    by_contra hnot
    exact hmiss col hnot hpat
  have : 5 ≤ T.card := (Finset.card_le_card hsub).trans' hle
  omega

/-- The same cap on the column bank, via the transpose. -/
lemma bank_card_le_two_of_factor_col {n m : ℕ} {G : Fin n → Fin m → Bool}
    {R : Finset (Fin n)} {T : Finset (Fin m)}
    (hrich : ∀ (i j k : Fin m), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun row =>
          (G row j != G row i) = x ∧ (G row k != G row i) = y)).card)
    (hR : R.card ≤ 4)
    (t : Fin n → Bool) (q : Fin m → Bool → Bool) (U : Fin n → Bool → Bool)
    (hfactor : ∀ a ∈ T, ∀ x, x ∉ R → G x a = U x (q a (t x))) :
    T.card ≤ 2 :=
  bank_card_le_two_of_factor (G := fun j i => G i j) (R := T) (T := R)
    hrich hR t q U hfactor

/-- Rectangular form of `tree_bank_caps_of_small_regions`. -/
lemma tree_bank_caps_rect {N n : ℕ} {C : Circuit}
    (hback : ReadsBack N C) (hout : C.output + 1 = N + C.size)
    (t : BTree) (ht : GoodTree N C t) (hm : t.marks ≤ 1)
    (_hraw : t.privs ⊆ Finset.range N)
    (hsmall : ∀ S E : Finset ℕ, S ⊆ t.privs → S.Nonempty → E.card ≤ 1 →
      IsTree N C S E →
      (S.filter (fun w => w < n)).card ≤ 4 →
      (S.filter (fun w => n ≤ w)).card ≤ 4 →
      (S.filter (fun w => w < n)).card ≤ 2 ∧
      (S.filter (fun w => n ≤ w)).card ≤ 2) :
    (t.privs.filter (fun w => w < n)).card ≤ 2 ∧
    (t.privs.filter (fun w => n ≤ w)).card ≤ 2 := by
  classical
  change t.bankCount (fun w => w < n) ≤ 2 ∧ t.bankCount (fun w => n ≤ w) ≤ 2
  by_contra hnot
  have hlarge : 2 < t.bankCount (fun w => w < n) ∨ 2 < t.bankCount (fun w => n ≤ w) := by
    omega
  obtain ⟨u, hgu, hmu, hpriv, hlu, hpu, hqu⟩ :=
    BTree.good_small_violating_subtree (fun w => w < n) (fun w => n ≤ w)
      t ht hm hlarge
  have hne : u.privs.Nonempty := by
    by_contra hn
    have he : u.privs = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [BTree.bankCount, he] at hlu
  obtain ⟨E, he, htree⟩ := one_mark_good_isTree hback hout hgu hmu hne
  obtain ⟨hpr, hqr⟩ := hsmall u.privs E hpriv hne he htree
    (by simpa only [BTree.bankCount] using hpu)
    (by simpa only [BTree.bankCount] using hqu)
  change u.bankCount (fun w => w < n) ≤ 2 at hpr
  change u.bankCount (fun w => n ≤ w) ≤ 2 at hqr
  omega

def rowOff {n m : ℕ} (j : Fin m) : List Bool :=
  List.replicate n false ++ List.ofFn (fun v : Fin m => decide (v = j))

def colOff {n m : ℕ} (i : Fin n) : List Bool :=
  List.ofFn (fun u : Fin n => decide (u = i)) ++ List.replicate m false

lemma bne_eq_xor (a b : Bool) : (a != b) = xor a b := by
  cases a <;> cases b <;> rfl

lemma xor_bne_cancel (off val : Bool) : xor off (val != off) = val := by
  cases off <;> cases val <;> rfl

lemma isTree_of_empty_region {N : ℕ} {C : Circuit} {S region : Finset ℕ} {root : ℕ}
    (hreg : region = ∅)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1) :
    S ⊆ {root} := by
  intro w hw
  have hwires' : w ∈ S ∪ region.image (fun k => N + k) :=
    Finset.mem_union_left _ hw
  by_contra hne
  have hne' : w ≠ root := by
    intro h
    exact hne (Finset.mem_singleton.mpr h)
  have h1 := hwires w hwires' hne'
  subst hreg
  simp [readsIn] at h1

/-- From an `IsTree` on the AND-shadow with at most one entry, 25872 gives a
1-bit factorization of `G` on each bank, and richness then caps each bank at
two names when the other bank has at most four. -/
lemma isTree_bank_le_two {n m : ℕ} {G : Fin n → Fin m → Bool}
    (outFn : Bool → Bool) (D : BinaryCircuit) (S E : Finset ℕ)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hrich : ∀ (i j k : Fin n), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (G j col != G i col) = x ∧ (G k col != G i col) = y)).card)
    (htrich : ∀ (i j k : Fin m), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun row =>
          (G row j != G row i) = x ∧ (G row k != G row i) = y)).card)
    (hrep : ∀ (u : Fin n) (v : Fin m), outFn (D.eval (oneEach u v)) = G u v)
    (htree : IsTree (n + m) (binarySkeleton D) S E)
    (hE : E.card ≤ 1)
    (hS : S ⊆ Finset.range (n + m))
    (hback : Back (n + m) D.gates)
    (hReads : ReadsBack (n + m) (binarySkeleton D))
    (hout : (binarySkeleton D).output + 1 = n + m + (binarySkeleton D).size)
    (hrow4 : (rowNames n S).card ≤ 4)
    (hcol4 : (colNames n m S).card ≤ 4) :
    (rowNames n S).card ≤ 2 ∧ (colNames n m S).card ≤ 2 := by
  classical
  obtain ⟨region, root, hreg, hroot, hlr0, hEcond, hshape, hwires⟩ := htree
  by_cases hre : region = ∅
  · have hsing := isTree_of_empty_region hre hroot
      (fun w hw hne => (hwires w hw hne).1)
    have hcard : S.card ≤ 1 := (Finset.card_le_card hsing).trans (by simp)
    have hsum := rowNames_colNames_card (n := n) (m := m) hS
    constructor <;> omega
  · have hne : region.Nonempty := Finset.nonempty_iff_ne_empty.mpr hre
    obtain ⟨top, htop, hroot_eq⟩ := tree_root_is_gate (n + m) (binarySkeleton D)
      S region root hreg hroot
      (fun w hw hne => (hwires w hw hne).1) hReads hne
    let raw := n + m
    let Rnm := rowNames n S
    let Cnm := colNames n m S
    let sources := Rnm.image Fin.val ∪ Cnm.image (fun j => n + j.val)
    have hsrc : sources = S := sources_of_names S hS
    have hinside (w : ℕ) : raw ≤ w ∧ w - raw ∈ region ↔
        w ∈ region.image (fun k => raw + k) := by
      constructor
      · intro ⟨hle, hmem⟩
        exact Finset.mem_image.mpr ⟨w - raw, hmem, by omega⟩
      · intro hw
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨by omega, by simp [hk]⟩
    have hentry : ∀ e ∈ E, e < raw + top ∧ e ∉ sources ∧ ¬(raw ≤ e ∧ e - raw ∈ region) := by
      intro e he
      obtain ⟨hneW, hlt, _⟩ := hEcond e he
      have hwireset : sources ∪ region.image (fun k => raw + k) =
          S ∪ region.image (fun k => raw + k) := by rw [hsrc]
      have : e ∉ S ∪ region.image (fun k => raw + k) := hneW
      rw [← hwireset] at this
      rw [hroot_eq] at hlt
      refine ⟨hlt, ?_, ?_⟩
      · intro hs
        exact this (Finset.mem_union_left _ hs)
      · intro hin
        exact this (Finset.mem_union_right _ ((hinside e).mp hin))
    have hsz : (binarySkeleton D).size = D.gates.length := by
      simpa [BinaryCircuit.size] using binarySkeleton_size D
    have hgates : ∀ g : Fin D.gates.length,
        let node := D.gates.get g
        ∀ w ∈ ({node.left, node.right} : Finset ℕ),
          w < raw + g.val ∧
          (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ E) ∧
          (g.val ∉ region → w ∉ sources ∧
            ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)) := by
      intro g node w hw
      have hj : g.val < D.gates.length := g.isLt
      have hwr : w = node.left ∨ w = node.right := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hw
      have heqL : node.left = (D.gates[g.val]'hj).left := rfl
      have heqR : node.right = (D.gates[g.val]'hj).right := rfl
      have hbackg := hback g.val hj
      have hwlt : w < raw + g.val := by
        rcases hwr with h | h
        · rw [h, heqL]; exact hbackg.1
        · rw [h, heqR]; exact hbackg.2
      have hwr' : w = D.gates[g.val].left ∨ w = D.gates[g.val].right := by
        rcases hwr with h | h
        · exact Or.inl (h.trans heqL)
        · exact Or.inr (h.trans heqR)
      refine ⟨hwlt, ?_, ?_⟩
      · intro hgin
        have hinp : w ∈ (gateAt (binarySkeleton D) g.val).inputs := by
          rw [binarySkeleton_gate D g.val hj]
          simpa [eq_comm] using hwr'
        have := (hshape g.val hgin).2.2 w hinp
        rcases this with hW | hEnt
        · rcases Finset.mem_union.mp hW with hS' | himg
          · exact Or.inl (hsrc.symm ▸ hS')
          · exact Or.inr (Or.inl ((hinside w).mpr himg))
        · exact Or.inr (Or.inr hEnt)
      · intro hgout
        constructor
        · intro hs
          have hpriv : w ∈ S ∪ region.image (fun k => raw + k) := by
            rw [hsrc] at hs
            exact Finset.mem_union_left _ hs
          have hne_root : w ≠ root := by
            intro hwr
            -- sources are < raw, root = raw+top ≥ raw
            have : w < raw := by
              have : w ∈ sources := hs
              rw [hsrc] at this
              exact Finset.mem_range.mp (hS this)
            rw [hroot_eq] at hwr
            omega
          have hinp : w ∈ (gateAt (binarySkeleton D) g.val).inputs := by
            rw [binarySkeleton_gate D g.val hj]
            simpa [eq_comm] using hwr'
          have hjC : g.val < (binarySkeleton D).size := by simpa [hsz] using hj
          exact tree_outside_unread (n + m) (binarySkeleton D) S E region root
            hreg (fun w' hw' hne' => ⟨(hwires w' hw' hne').1, (hwires w' hw' hne').2.1⟩) hjC hgout hinp hpriv hne_root
        · intro hin
          have himg : w ∈ region.image (fun k => raw + k) := (hinside w).mp hin
          have hpriv : w ∈ S ∪ region.image (fun k => raw + k) :=
            Finset.mem_union_right _ himg
          by_cases hne_root : w = root
          · rw [hne_root, hroot_eq]
          · have hinp : w ∈ (gateAt (binarySkeleton D) g.val).inputs := by
              rw [binarySkeleton_gate D g.val hj]
              simpa [eq_comm] using hwr'
            have hjC : g.val < (binarySkeleton D).size := by simpa [hsz] using hj
            exact (tree_outside_unread (n + m) (binarySkeleton D) S E region root
              hreg (fun w' hw' hne' => ⟨(hwires w' hw' hne').1, (hwires w' hw' hne').2.1⟩) hjC hgout hinp hpriv
              hne_root).elim
    have hout_ns : D.output ∉ sources := by
      intro hs
      have hsS : D.output ∈ S := by rwa [hsrc] at hs
      have hlt : D.output < raw := Finset.mem_range.mp (hS hsS)
      have hpos : 0 < (binarySkeleton D).size := by
        obtain ⟨k, hk⟩ := hne
        have : k < (binarySkeleton D).size := Finset.mem_range.mp (hreg hk)
        omega
      have hout' : D.output + 1 = raw + (binarySkeleton D).size := hout
      omega
    have hout_in : (raw ≤ D.output ∧ D.output - raw ∈ region) → D.output = raw + top := by
      intro hin
      have himg : D.output ∈ region.image (fun k => raw + k) := (hinside D.output).mp hin
      have hpriv : D.output ∈ S ∪ region.image (fun k => raw + k) :=
        Finset.mem_union_right _ himg
      by_cases hne_root : D.output = root
      · rw [hne_root, hroot_eq]
      · have : (binarySkeleton D).output ≠ D.output :=
          (hwires D.output hpriv hne_root).2.2
        exact (this rfl).elim
    have hregD : region ⊆ Finset.range D.size := by
      simpa [BinaryCircuit.size, binarySkeleton_size] using hreg
    obtain ⟨hrowResp, hcolResp⟩ :=
      PEqualNP.Outside.L_meta_25872 n m D Rnm Cnm region E top
        hregD htop hentry hgates hout_ns hout_in
    -- Row-side 1-bit factorization
    obtain ⟨mask, response, hresp⟩ := hrowResp
    let t : Fin m → Bool := fun j =>
      if hneE : E.Nonempty then
        (D.wires (rowOff (n := n) j)).getD (E.min' hneE) false
      else false
    let q : Fin n → Bool → Bool := fun i bit => response i (fun _ => bit)
    let U : Fin m → Bool → Bool := fun j b =>
      outFn (xor (D.eval (rowOff (n := n) j)) (mask j && b))
    have hfactor : ∀ a ∈ Rnm, ∀ x, x ∉ Cnm → G a x = U x (q a (t x)) := by
      intro a ha x hx
      have hval := hresp a ha x hx
      -- value a x = D.eval (one n a ++ one m x) = D.eval (oneEach a x)
      have hone : List.ofFn (fun v : Fin n => decide (v = a)) ++
          List.ofFn (fun v : Fin m => decide (v = x)) = oneEach a x := rfl
      have hval' :
          (D.eval (oneEach a x) != D.eval (rowOff (n := n) x)) =
          (mask x && response a (fun e => (D.wires (rowOff (n := n) x)).getD e.val false)) := by
        simpa [hone, rowOff] using hval
      have hfun : (fun e : ↥E => (D.wires (rowOff (n := n) x)).getD e.val false) =
          (fun _ => t x) := by
        funext e
        have hneE : E.Nonempty := ⟨e.val, e.property⟩
        dsimp [t]
        simp only [hneE, ↓reduceDIte]
        have hcard1 : E.card = 1 := by
          have : 0 < E.card := Finset.card_pos.mpr hneE
          omega
        obtain ⟨b, hbE⟩ := Finset.card_eq_one.mp hcard1
        have huniq : ∀ x ∈ E, x = b := by
          intro x hx
          have : x ∈ ({b} : Finset ℕ) := by
            rw [← hbE]
            exact hx
          exact Finset.mem_singleton.mp this
        have hbmin : E.min' hneE = b := huniq _ (Finset.min'_mem E hneE)
        have heval : e.val = b := huniq _ e.property
        simp [hbmin, heval]
      have hxor : D.eval (oneEach a x) =
          xor (D.eval (rowOff (n := n) x))
            (mask x && response a (fun e => (D.wires (rowOff (n := n) x)).getD e.val false)) := by
        exact (xor_bne_cancel (D.eval (rowOff (n := n) x)) (D.eval (oneEach a x))).symm.trans
          (by rw [← bne_eq_xor, hval'])
      rw [← hrep, hxor, hfun]
    have hR := bank_card_le_two_of_factor (G := G) (R := Rnm) (T := Cnm)
      hrich hcol4 t q U hfactor
    -- Column-side factorization
    obtain ⟨maskC, responseC, hrespC⟩ := hcolResp
    let tC : Fin n → Bool := fun i =>
      if hneE : E.Nonempty then
        (D.wires (colOff (m := m) i)).getD (E.min' hneE) false
      else false
    let qC : Fin m → Bool → Bool := fun j bit => responseC j (fun _ => bit)
    let UC : Fin n → Bool → Bool := fun i b =>
      outFn (xor (D.eval (colOff (m := m) i)) (maskC i && b))
    have hfactorC : ∀ a ∈ Cnm, ∀ x, x ∉ Rnm → G x a = UC x (qC a (tC x)) := by
      intro a ha x hx
      have hone : List.ofFn (fun v : Fin n => decide (v = x)) ++
          List.ofFn (fun v : Fin m => decide (v = a)) = oneEach x a := rfl
      have hval' :
          (D.eval (oneEach x a) != D.eval (colOff (m := m) x)) =
          (maskC x && responseC a (fun e => (D.wires (colOff (m := m) x)).getD e.val false)) := by
        simpa [hone, colOff] using hrespC a ha x hx
      have hfun : (fun e : ↥E => (D.wires (colOff (m := m) x)).getD e.val false) =
          (fun _ => tC x) := by
        funext e
        have hneE : E.Nonempty := ⟨e.val, e.property⟩
        dsimp [tC]
        simp only [hneE, ↓reduceDIte]
        have hcard1 : E.card = 1 := by
          have : 0 < E.card := Finset.card_pos.mpr hneE
          omega
        obtain ⟨b, hbE⟩ := Finset.card_eq_one.mp hcard1
        have huniq : ∀ x ∈ E, x = b := by
          intro x hx
          have : x ∈ ({b} : Finset ℕ) := by
            rw [← hbE]
            exact hx
          exact Finset.mem_singleton.mp this
        have hbmin : E.min' hneE = b := huniq _ (Finset.min'_mem E hneE)
        have heval : e.val = b := huniq _ e.property
        simp [hbmin, heval]
      have hxor : D.eval (oneEach x a) =
          xor (D.eval (colOff (m := m) x))
            (maskC x && responseC a (fun e => (D.wires (colOff (m := m) x)).getD e.val false)) := by
        exact (xor_bne_cancel (D.eval (colOff (m := m) x)) (D.eval (oneEach x a))).symm.trans
          (by rw [← bne_eq_xor, hval'])
      rw [← hrep, hxor, hfun]
    have hC := bank_card_le_two_of_factor_col (G := G) (R := Rnm) (T := Cnm)
      htrich hrow4 tC qC UC hfactorC
    exact ⟨hR, hC⟩


/-- Copy of the 25646 marked-union count: once-read names over a disjoint list
    of small pieces are at most two per piece plus two marks. -/
lemma marked_union (L : List (Finset ℕ)) (H : Finset ℕ)
    (separate : L.Pairwise Disjoint)
    (small : ∀ S ∈ L, S.card ≤ 2 + 2 * (S ∩ H).card) :
    (L.toFinset.biUnion id).card ≤ 2 * L.length + 2 * ((L.toFinset.biUnion id) ∩ H).card := by
  classical
  induction L with
  | nil => simp
  | cons S l ih =>
    obtain ⟨bySet, rest⟩ := List.pairwise_cons.mp separate
    have bound := small S (by simp)
    have tail := ih rest (fun t ht => small t (by simp [ht]))
    let A := l.toFinset.biUnion id
    have dis : Disjoint S A := by
      apply Finset.disjoint_left.mpr
      intro w ws wa
      obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp wa
      exact Finset.disjoint_left.mp (bySet t (List.mem_toFinset.mp ht)) ws hit
    have di : Disjoint (S ∩ H) (A ∩ H) := by
      apply Finset.disjoint_left.mpr
      intro w hs ha
      exact Finset.disjoint_left.mp dis (Finset.mem_inter.mp hs).1 (Finset.mem_inter.mp ha).1
    rw [List.toFinset_cons, Finset.biUnion_insert, List.length_cons]
    change (S ∪ A).card ≤ 2 * (l.length + 1) + 2 * ((S ∪ A) ∩ H).card
    rw [Finset.card_union_of_disjoint dis, Finset.union_inter_distrib_right,
      Finset.card_union_of_disjoint di]
    change A.card ≤ 2 * l.length + 2 * (A ∩ H).card at tail
    omega

lemma xor_eq_true_iff (a b : Bool) : xor a b = true ↔ a ≠ b := by
  cases a <;> cases b <;> simp

lemma xor_true (b : Bool) : xor true b = !b := by
  cases b <;> rfl

lemma xor_cancel_triple (a b h : Bool) :
    xor (xor a h) (xor b h) = xor a b := by
  cases a <;> cases b <;> cases h <;> rfl

/-- A 1-bit factorization of two named rows, with the other bank at most two
    names, yields an affordable pair in the sense of `bounded`, relative to the
    blank-row offset `Hr`. -/
lemma affordable_of_row_factor {n m : ℕ} (G : Fin n → Fin m → Bool)
    (R : Finset (Fin n)) (T : Finset (Fin m)) (Hr : Fin m → Bool)
    (hT : T.card ≤ 2)
    (t : Fin m → Bool) (q0 : Bool → Bool) (q : Fin n → Bool → Bool)
    (U : Fin m → Bool → Bool)
    (h0 : ∀ x, x ∉ T → Hr x = U x (q0 (t x)))
    (hfac : ∀ a ∈ R, ∀ x, x ∉ T → G a x = U x (q a (t x)))
    {a b : Fin n} (ha : a ∈ R) (hb : b ∈ R) (hne : a ≠ b) :
    ∃ e : Fin n × Fin n,
      e.1 ≠ e.2 ∧ (e.1 = a ∨ e.1 = b) ∧ (e.2 = a ∨ e.2 = b) ∧
      ∃ side : Bool,
        (Finset.univ.filter (fun col =>
          (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
  classical
  obtain ⟨p, r, hz, hm⟩ :=
    Causal.factored_outputs_pair_missing (fun x => x ∉ T)
      (G a) (G b) Hr t q0 (q a) (q b) U h0 (hfac a ha) (hfac b hb)
  have hsubset (e1 e2 : Fin n) (side : Bool)
      (hmiss : ∀ x, x ∉ T →
        ¬(xor (G e1 x) (Hr x) = true ∧ xor (G e2 x) (Hr x) = !side)) :
      (Finset.univ.filter (fun col =>
        (G e1 col != G e2 col) = side ∧ G e1 col ≠ Hr col)).card ≤ 2 := by
    refine le_trans (Finset.card_le_card ?_) hT
    intro col hcol
    have ⟨_, hcond⟩ := Finset.mem_filter.mp hcol
    by_contra hnot
    have hxor1 : xor (G e1 col) (Hr col) = true :=
      (xor_eq_true_iff _ _).mpr hcond.2
    have hxor2 : xor (G e1 col) (G e2 col) = side := by
      simpa [bne_eq_xor] using hcond.1
    have hr' : xor (G e2 col) (Hr col) = !side := by
      have h3 : xor (xor (G e1 col) (Hr col)) (xor (G e2 col) (Hr col))
          = xor (G e1 col) (G e2 col) := xor_cancel_triple _ _ _
      rw [hxor1, xor_true, hxor2] at h3
      simpa using congrArg (fun b => !b) h3
    exact hmiss col hnot ⟨hxor1, hr'⟩
  cases hp : p
  · have hr : r = true := by
      cases r
      · have hfalse : (p, false) ≠ (false, false) := hz
        simp [hp] at hfalse
      · rfl
    refine ⟨(b, a), hne.symm, Or.inr rfl, Or.inl rfl, true, ?_⟩
    apply hsubset b a true
    intro x hx hpat
    have : xor (G a x) (Hr x) = p ∧ xor (G b x) (Hr x) = r := by
      rw [hp, hr]
      exact ⟨hpat.2, hpat.1⟩
    exact hm x hx this
  · refine ⟨(a, b), hne, Or.inl rfl, Or.inr rfl, !r, ?_⟩
    apply hsubset a b (!r)
    intro x hx hpat
    have : xor (G a x) (Hr x) = p ∧ xor (G b x) (Hr x) = r := by
      rw [hp]
      refine ⟨hpat.1, ?_⟩
      have : xor (G b x) (Hr x) = !(!r) := hpat.2
      simpa using this
    exact hm x hx this

lemma affordable_of_col_factor {n m : ℕ} (G : Fin n → Fin m → Bool)
    (Cnm : Finset (Fin m)) (R : Finset (Fin n)) (Hc : Fin n → Bool)
    (hR : R.card ≤ 2)
    (t : Fin n → Bool) (q0 : Bool → Bool) (q : Fin m → Bool → Bool)
    (U : Fin n → Bool → Bool)
    (h0 : ∀ x, x ∉ R → Hc x = U x (q0 (t x)))
    (hfac : ∀ a ∈ Cnm, ∀ x, x ∉ R → G x a = U x (q a (t x)))
    {a b : Fin m} (ha : a ∈ Cnm) (hb : b ∈ Cnm) (hne : a ≠ b) :
    ∃ e : Fin m × Fin m,
      e.1 ≠ e.2 ∧ (e.1 = a ∨ e.1 = b) ∧ (e.2 = a ∨ e.2 = b) ∧
      ∃ side : Bool,
        (Finset.univ.filter (fun row =>
          (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
  simpa using
    affordable_of_row_factor (G := fun j i => G i j) (R := Cnm) (T := R) (Hr := Hc)
      hR t q0 q U h0 hfac ha hb hne

/-- `BinarySupport.reads` agrees with `readsOf` of the AND-shadow. -/
lemma reads_eq_readsOf (D : BinaryCircuit) (w : ℕ) :
    BinarySupport.reads D w = readsOf (binarySkeleton D) w := by
  unfold BinarySupport.reads readsOf readsIn BinarySupport.gateAt
  have hsz : (binarySkeleton D).size = D.size := binarySkeleton_size D
  simp only [hsz]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj' : j < D.gates.length := by
    simpa [BinaryCircuit.size] using Finset.mem_range.mp hj
  rw [binarySkeleton_gate D j hj', List.getD_eq_getElem _ _ hj']
  simp only [List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]
  have hiteq (a : ℕ) : (if w = a then 1 else 0) = (if a = w then 1 else 0) := by
    simp [eq_comm]
  rw [hiteq, hiteq, add_comm]

lemma used_surplus_eq_size_succ {N : ℕ} (D : BinaryCircuit)
    (hpos : 0 < D.size) (hBack : Back N D.gates) (hLive : Live N D) :
    ((Finset.range N).filter (fun w => 1 ≤ readsOf (binarySkeleton D) w)).card
      + ∑ w ∈ Finset.range (N + D.size), (readsOf (binarySkeleton D) w - 1)
      = D.size + 1 := by
  have h := BinarySupport.normalized_reads_budget N D hpos hBack hLive
  have hr : ∀ w, BinarySupport.reads D w = readsOf (binarySkeleton D) w :=
    reads_eq_readsOf D
  simp only [hr] at h
  exact h

lemma many_count_sub (S : Finset ℕ) (f : ℕ → ℕ) :
    (S.filter (fun w => 2 ≤ f w)).card ≤ ∑ w ∈ S, (f w - 1) := by
  rw [Finset.card_filter]
  apply Finset.sum_le_sum
  intro w _
  split_ifs <;> omega

lemma shared_le_surplus {N : ℕ} (D : BinaryCircuit) :
    ((Finset.range N).filter
        (fun w => 2 ≤ readsOf (binarySkeleton D) w)).card
      + ((Finset.range D.size).filter
        (fun j => 2 ≤ readsOf (binarySkeleton D) (N + j))).card
      ≤ ∑ w ∈ Finset.range (N + D.size), (readsOf (binarySkeleton D) w - 1) := by
  classical
  let reads := readsOf (binarySkeleton D)
  have h1 : ((Finset.range N).filter (fun w => 2 ≤ reads w)).card
      ≤ ∑ w ∈ Finset.range N, (reads w - 1) :=
    many_count_sub (Finset.range N) reads
  have h2 : ((Finset.range D.size).filter (fun j => 2 ≤ reads (N + j))).card
      ≤ ∑ j ∈ Finset.range D.size, (reads (N + j) - 1) :=
    many_count_sub (Finset.range D.size) (fun j => reads (N + j))
  have hsum := (Finset.sum_range_add (fun w => reads w - 1) N D.size).symm
  dsimp only [reads] at h1 h2 hsum ⊢
  omega

lemma hitUses_decomp {N : ℕ} (D : BinaryCircuit) :
    let reads := readsOf (binarySkeleton D)
    let shared := (Finset.range (N + D.size)).filter (fun w => 2 ≤ reads w)
    ∑ w ∈ shared, reads w
      = (∑ w ∈ shared, (reads w - 1)) + shared.card := by
  intro reads shared
  have hterm : ∀ w ∈ shared, reads w = (reads w - 1) + 1 := by
    intro w hw
    have : 2 ≤ reads w := (Finset.mem_filter.mp hw).2
    omega
  calc
    ∑ w ∈ shared, reads w = ∑ w ∈ shared, ((reads w - 1) + 1) :=
      Finset.sum_congr rfl hterm
    _ = ∑ w ∈ shared, (reads w - 1) + ∑ w ∈ shared, 1 :=
      Finset.sum_add_distrib
    _ = ∑ w ∈ shared, (reads w - 1) + shared.card := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_one]

lemma unread_not_input (D : BinaryCircuit) (w : ℕ)
    (hun : readsOf (binarySkeleton D) w = 0) {g : BinaryGate} (hg : g ∈ D.gates) :
    g.left ≠ w ∧ g.right ≠ w := by
  obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hg
  have hjmem : j ∈ Finset.range (binarySkeleton D).size := by
    simpa [binarySkeleton_size, BinaryCircuit.size] using hj
  have hterm :
      (gateAt (binarySkeleton D) j).inputs.count w
        ≤ readsIn (binarySkeleton D) (Finset.range (binarySkeleton D).size) w :=
    Finset.single_le_sum
      (f := fun j => (gateAt (binarySkeleton D) j).inputs.count w)
      (fun _ _ => Nat.zero_le _) hjmem
  have h0 : (gateAt (binarySkeleton D) j).inputs.count w = 0 := by
    unfold readsOf at hun
    omega
  rw [binarySkeleton_gate D j hj] at h0
  simp [List.count_cons, List.count_nil] at h0
  have hg' : D.gates[j] = g := heq
  rw [hg'] at h0
  constructor <;> intro h <;> simp [h] at h0

lemma foldl_wires_ignore (gs : List BinaryGate) (x y : List Bool) (w : ℕ)
    (hlen : x.length = y.length)
    (hxy : ∀ i, i ≠ w → x.getD i false = y.getD i false)
    (hun : ∀ g ∈ gs, g.left ≠ w ∧ g.right ≠ w) :
    (∀ k, k ≠ w →
      (gs.foldl (fun acc g => acc ++ [g.op (acc.getD g.left false)
          (acc.getD g.right false)]) x).getD k false =
      (gs.foldl (fun acc g => acc ++ [g.op (acc.getD g.left false)
          (acc.getD g.right false)]) y).getD k false) := by
  induction gs generalizing x y with
  | nil =>
    exact hxy
  | cons g gs ih =>
    have hg : g.left ≠ w ∧ g.right ≠ w := hun g (List.mem_cons.mpr (Or.inl rfl))
    have htl : ∀ g' ∈ gs, g'.left ≠ w ∧ g'.right ≠ w :=
      fun g' hg' => hun g' (List.mem_cons.mpr (Or.inr hg'))
    have hop : g.op (x.getD g.left false) (x.getD g.right false)
        = g.op (y.getD g.left false) (y.getD g.right false) := by
      rw [hxy g.left hg.1, hxy g.right hg.2]
    let x' := x ++ [g.op (x.getD g.left false) (x.getD g.right false)]
    let y' := y ++ [g.op (y.getD g.left false) (y.getD g.right false)]
    have hlen' : x'.length = y'.length := by simp [x', y', hlen]
    have hxy' : ∀ i, i ≠ w → x'.getD i false = y'.getD i false := by
      intro i hi
      simp only [x', y', List.getD_eq_getElem?_getD]
      by_cases hix : i < x.length
      · have hiy : i < y.length := by omega
        rw [List.getElem?_append_left hix, List.getElem?_append_left hiy]
        simpa [List.getD_eq_getElem?_getD] using hxy i hi
      · rw [List.getElem?_append_right (Nat.le_of_not_gt hix),
          List.getElem?_append_right (by omega : y.length ≤ i)]
        have hxlen : i - y.length = i - x.length := by omega
        rw [hxlen]
        cases hiz : i - x.length
        · simpa [List.getD_eq_getElem?_getD] using hop
        · simp [List.getElem?_cons_succ, List.getElem?_nil]
    exact ih x' y' hlen' hxy' htl

lemma eval_eq_of_unread (D : BinaryCircuit) (x y : List Bool) (w : ℕ)
    (hlen : x.length = y.length)
    (hxy : ∀ i, i ≠ w → x.getD i false = y.getD i false)
    (hun : readsOf (binarySkeleton D) w = 0)
    (hout : D.output ≠ w) :
    D.eval x = D.eval y := by
  have hgs : ∀ g ∈ D.gates, g.left ≠ w ∧ g.right ≠ w :=
    fun g hg => unread_not_input D w hun hg
  have hagree := foldl_wires_ignore D.gates x y w hlen hxy hgs
  simpa [BinaryCircuit.eval, BinaryCircuit.wires] using hagree D.output hout

lemma oneEach_agree_rowOff {n m : ℕ} (i : Fin n) (j : Fin m) (k : ℕ)
    (hk : k ≠ i.val) :
    (oneEach i j).getD k false = (rowOff (n := n) j).getD k false := by
  have hlen : (oneEach i j).length = n + m := length_oneEach i j
  have hlen' : (rowOff (n := n) j).length = n + m := by
    simp [rowOff]
  by_cases hkn : k < n
  · have := getD_oneEach_left i j k hkn
    have hrow : (rowOff (n := n) j).getD k false = false := by
      simp [rowOff, List.getD_eq_getElem?_getD, List.getElem?_append_left
        (by simpa using hkn : k < (List.replicate n false).length)]
    rw [this, hrow]
    simp [hk]
  · by_cases hkm : k < n + m
    · have hge : n ≤ k := by omega
      have := getD_oneEach_right i j k hge hkm
      have hrow : (rowOff (n := n) j).getD k false = decide (k - n = j.val) := by
        simp [rowOff, List.getD_eq_getElem?_getD]
        have hleft : (List.replicate n false).length = n := by simp
        rw [List.getElem?_append_right (by simp [hleft]; exact hge)]
        simp [hleft]
        have hk' : k - n < m := by omega
        simp [List.getElem?_ofFn, hk', Fin.ext_iff]
      rw [this, hrow]
    · simp [List.getD_eq_getElem?_getD]
      have : (oneEach i j)[k]? = none := List.getElem?_eq_none (by omega)
      have : (rowOff (n := n) j)[k]? = none := List.getElem?_eq_none (by omega)
      simp_all

lemma oneEach_agree_colOff {n m : ℕ} (i : Fin n) (j : Fin m) (k : ℕ)
    (hk : k ≠ n + j.val) :
    (oneEach i j).getD k false = (colOff (m := m) i).getD k false := by
  by_cases hkn : k < n
  · have := getD_oneEach_left i j k hkn
    have hcol : (colOff (m := m) i).getD k false = decide (k = i.val) := by
      simp [colOff, List.getD_eq_getElem?_getD, List.getElem?_append_left
        (by simpa using hkn : k < (List.ofFn (fun u : Fin n => decide (u = i))).length)]
      simp [List.getElem?_ofFn, hkn, Fin.ext_iff]
    rw [this, hcol]
  · by_cases hkm : k < n + m
    · have hge : n ≤ k := by omega
      have := getD_oneEach_right i j k hge hkm
      have hcol : (colOff (m := m) i).getD k false = false := by
        simp [colOff, List.getD_eq_getElem?_getD]
        have hleft : (List.ofFn (fun u : Fin n => decide (u = i))).length = n := by simp
        rw [List.getElem?_append_right (by simp [hleft]; exact hge)]
        have hk' : k - n < m := by omega
        simp [hleft, List.getElem?_replicate, hk']
      have hne : k - n ≠ j.val := by omega
      rw [this, hcol]
      simp [hne]
    · simp [List.getD_eq_getElem?_getD]
      have : (oneEach i j)[k]? = none := List.getElem?_eq_none (by
        have : (oneEach i j).length = n + m := length_oneEach i j
        omega)
      have : (colOff (m := m) i)[k]? = none := List.getElem?_eq_none (by
        simp [colOff]; omega)
      simp_all

/-- Two identical rows contradict richness when there are at least three rows. -/
lemma equal_rows_not_rich {n m : ℕ} {G : Fin n → Fin m → Bool}
    (hn : 3 ≤ n) (_hm : 3 ≤ m)
    (hrich : ∀ (i j k : Fin n), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (G j col != G i col) = x ∧ (G k col != G i col) = y)).card)
    {i k : Fin n} (hik : i ≠ k)
    (heq : ∀ v : Fin m, G i v = G k v) : False := by
  classical
  have hne : ((Finset.univ.erase i).erase k).Nonempty := by
    have hmemk : k ∈ (Finset.univ : Finset (Fin n)).erase i :=
      Finset.mem_erase.mpr ⟨hik.symm, Finset.mem_univ k⟩
    have hpos : 0 < (((Finset.univ : Finset (Fin n)).erase i).erase k).card := by
      rw [Finset.card_erase_of_mem hmemk, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]
      omega
    exact Finset.card_pos.mp hpos
  obtain ⟨j, hj⟩ := hne
  have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
  have hji : j ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  have hcard := hrich i j k hji.symm hik hjk true true (Or.inl rfl)
  have hempty :
      (Finset.univ.filter (fun col =>
        (G j col != G i col) = true ∧ (G k col != G i col) = true)) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro col _
    intro hcond
    have : (G k col != G i col) = false := by
      rw [heq col]
      cases (G k col) <;> rfl
    simp [this] at hcond
  rw [hempty, Finset.card_empty] at hcard
  exact Nat.not_succ_le_zero 4 hcard



lemma unread_row_eval {n m : ℕ} {G : Fin n → Fin m → Bool}
    (outFn : Bool → Bool) (D : BinaryCircuit)
    (hrep : ∀ (u : Fin n) (v : Fin m), outFn (D.eval (oneEach u v)) = G u v)
    (i : Fin n) (hread : readsOf (binarySkeleton D) i.val = 0)
    (hout : D.output ≠ i.val) :
    ∀ v : Fin m, G i v = outFn (D.eval (rowOff (n := n) v)) := by
  intro v
  have hlen : (oneEach i v).length = (rowOff (n := n) v).length := by
    simp [length_oneEach, rowOff]
  have hxy : ∀ k, k ≠ i.val →
      (oneEach i v).getD k false = (rowOff (n := n) v).getD k false :=
    fun k hk => oneEach_agree_rowOff i v k hk
  have heval := eval_eq_of_unread D (oneEach i v) (rowOff (n := n) v) i.val
    hlen hxy hread hout
  rw [← hrep, heval]

lemma unread_col_eval {n m : ℕ} {G : Fin n → Fin m → Bool}
    (outFn : Bool → Bool) (D : BinaryCircuit)
    (hrep : ∀ (u : Fin n) (v : Fin m), outFn (D.eval (oneEach u v)) = G u v)
    (j : Fin m) (hread : readsOf (binarySkeleton D) (n + j.val) = 0)
    (hout : D.output ≠ n + j.val) :
    ∀ u : Fin n, G u j = outFn (D.eval (colOff (m := m) u)) := by
  intro u
  have hlen : (oneEach u j).length = (colOff (m := m) u).length := by
    simp [length_oneEach, colOff]
  have hxy : ∀ k, k ≠ n + j.val →
      (oneEach u j).getD k false = (colOff (m := m) u).getD k false :=
    fun k hk => oneEach_agree_colOff u j k hk
  have heval := eval_eq_of_unread D (oneEach u j) (colOff (m := m) u) (n + j.val)
    hlen hxy hread hout
  rw [← hrep, heval]

lemma output_ne_raw {N : ℕ} (D : BinaryCircuit)
    (hpos : 0 < D.size)
    (hout : D.output + 1 = N + D.size) (w : ℕ) (hw : w < N) :
    D.output ≠ w := by
  omega

lemma unread_rows_le_one {n m : ℕ} {G : Fin n → Fin m → Bool}
    (outFn : Bool → Bool) (D : BinaryCircuit)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hrich : ∀ (i j k : Fin n), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (G j col != G i col) = x ∧ (G k col != G i col) = y)).card)
    (hrep : ∀ (u : Fin n) (v : Fin m), outFn (D.eval (oneEach u v)) = G u v)
    (hpos : 0 < D.size)
    (houtLast : D.output + 1 = n + m + D.size) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun i => readsOf (binarySkeleton D) i.val = 0)).card ≤ 1 := by
  classical
  by_contra h
  have h2 : 2 ≤ ((Finset.univ : Finset (Fin n)).filter
      (fun i => readsOf (binarySkeleton D) i.val = 0)).card := by omega
  obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq h2
  obtain ⟨i, k, hik, rfl⟩ := Finset.card_eq_two.mp hsc
  have hi : readsOf (binarySkeleton D) i.val = 0 :=
    (Finset.mem_filter.mp (hs (by simp))).2
  have hk : readsOf (binarySkeleton D) k.val = 0 :=
    (Finset.mem_filter.mp (hs (by simp))).2
  have houti : D.output ≠ i.val :=
    output_ne_raw (N := n + m) D hpos houtLast i.val (by omega)
  have houtk : D.output ≠ k.val :=
    output_ne_raw (N := n + m) D hpos houtLast k.val (by omega)
  have hie := unread_row_eval (G := G) outFn D hrep i hi houti
  have hke := unread_row_eval (G := G) outFn D hrep k hk houtk
  exact equal_rows_not_rich (G := G) hn hm hrich hik
    (fun v => (hie v).trans (hke v).symm)

lemma equal_cols_not_rich {n m : ℕ} {G : Fin n → Fin m → Bool}
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (htrich : ∀ (i j k : Fin m), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun row =>
          (G row j != G row i) = x ∧ (G row k != G row i) = y)).card)
    {i k : Fin m} (hik : i ≠ k)
    (heq : ∀ u : Fin n, G u i = G u k) : False :=
  equal_rows_not_rich (G := fun j i => G i j) hm hn htrich hik heq

lemma unread_cols_le_one {n m : ℕ} {G : Fin n → Fin m → Bool}
    (outFn : Bool → Bool) (D : BinaryCircuit)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (htrich : ∀ (i j k : Fin m), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun row =>
          (G row j != G row i) = x ∧ (G row k != G row i) = y)).card)
    (hrep : ∀ (u : Fin n) (v : Fin m), outFn (D.eval (oneEach u v)) = G u v)
    (hpos : 0 < D.size)
    (houtLast : D.output + 1 = n + m + D.size) :
    ((Finset.univ : Finset (Fin m)).filter
      (fun j => readsOf (binarySkeleton D) (n + j.val) = 0)).card ≤ 1 := by
  classical
  by_contra h
  have h2 : 2 ≤ ((Finset.univ : Finset (Fin m)).filter
      (fun j => readsOf (binarySkeleton D) (n + j.val) = 0)).card := by omega
  obtain ⟨s, hs, hsc⟩ := Finset.exists_subset_card_eq h2
  obtain ⟨i, k, hik, rfl⟩ := Finset.card_eq_two.mp hsc
  have hi : readsOf (binarySkeleton D) (n + i.val) = 0 :=
    (Finset.mem_filter.mp (hs (by simp))).2
  have hk : readsOf (binarySkeleton D) (n + k.val) = 0 :=
    (Finset.mem_filter.mp (hs (by simp))).2
  have houti : D.output ≠ n + i.val :=
    output_ne_raw (N := n + m) D hpos houtLast (n + i.val) (by omega)
  have houtk : D.output ≠ n + k.val :=
    output_ne_raw (N := n + m) D hpos houtLast (n + k.val) (by omega)
  have hie := unread_col_eval (G := G) outFn D hrep i hi houti
  have hke := unread_col_eval (G := G) outFn D hrep k hk houtk
  exact equal_cols_not_rich (G := G) hn hm htrich hik
    (fun u => (hie u).trans (hke u).symm)


/-- 25872 responses on a marks-≤1 `IsTree` adapt to 1-bit factors on each bank,
    provided the tree is not a lone leaf (so the region is nonempty). -/
lemma isTree_factors {n m : ℕ} {G : Fin n → Fin m → Bool}
    (outFn : Bool → Bool) (D : BinaryCircuit) (S E : Finset ℕ)
    (hrep : ∀ (u : Fin n) (v : Fin m), outFn (D.eval (oneEach u v)) = G u v)
    (htree : IsTree (n + m) (binarySkeleton D) S E)
    (hE : E.card ≤ 1)
    (hS : S ⊆ Finset.range (n + m))
    (hback : Back (n + m) D.gates)
    (hReads : ReadsBack (n + m) (binarySkeleton D))
    (hout : (binarySkeleton D).output + 1 = n + m + (binarySkeleton D).size)
    (h2 : 2 ≤ (rowNames n S).card ∨ 2 ≤ (colNames n m S).card) :
    (∃ (t : Fin m → Bool) (q0 : Bool → Bool) (q : Fin n → Bool → Bool)
      (U : Fin m → Bool → Bool),
      (∀ x, x ∉ colNames n m S →
        outFn (D.eval (rowOff (n := n) x)) = U x (q0 (t x))) ∧
      (∀ a ∈ rowNames n S, ∀ x, x ∉ colNames n m S →
        G a x = U x (q a (t x)))) ∧
    (∃ (t : Fin n → Bool) (q0 : Bool → Bool) (q : Fin m → Bool → Bool)
      (U : Fin n → Bool → Bool),
      (∀ x, x ∉ rowNames n S →
        outFn (D.eval (colOff (m := m) x)) = U x (q0 (t x))) ∧
      (∀ a ∈ colNames n m S, ∀ x, x ∉ rowNames n S →
        G x a = U x (q a (t x)))) := by
  classical
  obtain ⟨region, root, hreg, hroot, hlr0, hEcond, hshape, hwires⟩ := htree
  by_cases hre : region = ∅
  · have hsing := isTree_of_empty_region hre hroot
      (fun w hw hne => (hwires w hw hne).1)
    have hcard : S.card ≤ 1 := (Finset.card_le_card hsing).trans (by simp)
    have hsum := rowNames_colNames_card (n := n) (m := m) hS
    have : (rowNames n S).card ≤ 1 ∧ (colNames n m S).card ≤ 1 := by omega
    rcases h2 with h | h <;> omega
  · have hne : region.Nonempty := Finset.nonempty_iff_ne_empty.mpr hre
    obtain ⟨top, htop, hroot_eq⟩ := tree_root_is_gate (n + m) (binarySkeleton D)
      S region root hreg hroot
      (fun w hw hne => (hwires w hw hne).1) hReads hne
    let raw := n + m
    let Rnm := rowNames n S
    let Cnm := colNames n m S
    let sources := Rnm.image Fin.val ∪ Cnm.image (fun j => n + j.val)
    have hsrc : sources = S := sources_of_names S hS
    have hinside (w : ℕ) : raw ≤ w ∧ w - raw ∈ region ↔
        w ∈ region.image (fun k => raw + k) := by
      constructor
      · intro ⟨hle, hmem⟩
        exact Finset.mem_image.mpr ⟨w - raw, hmem, by omega⟩
      · intro hw
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨by omega, by simp [hk]⟩
    have hentry : ∀ e ∈ E, e < raw + top ∧ e ∉ sources ∧ ¬(raw ≤ e ∧ e - raw ∈ region) := by
      intro e he
      obtain ⟨hneW, hlt, _⟩ := hEcond e he
      have hwireset : sources ∪ region.image (fun k => raw + k) =
          S ∪ region.image (fun k => raw + k) := by rw [hsrc]
      have : e ∉ S ∪ region.image (fun k => raw + k) := hneW
      rw [← hwireset] at this
      rw [hroot_eq] at hlt
      refine ⟨hlt, ?_, ?_⟩
      · intro hs
        exact this (Finset.mem_union_left _ hs)
      · intro hin
        exact this (Finset.mem_union_right _ ((hinside e).mp hin))
    have hsz : (binarySkeleton D).size = D.gates.length := by
      simpa [BinaryCircuit.size] using binarySkeleton_size D
    have hgates : ∀ g : Fin D.gates.length,
        let node := D.gates.get g
        ∀ w ∈ ({node.left, node.right} : Finset ℕ),
          w < raw + g.val ∧
          (g.val ∈ region → w ∈ sources ∨ (raw ≤ w ∧ w - raw ∈ region) ∨ w ∈ E) ∧
          (g.val ∉ region → w ∉ sources ∧
            ((raw ≤ w ∧ w - raw ∈ region) → w = raw + top)) := by
      intro g node w hw
      have hj : g.val < D.gates.length := g.isLt
      have hwr : w = node.left ∨ w = node.right := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hw
      have heqL : node.left = (D.gates[g.val]'hj).left := rfl
      have heqR : node.right = (D.gates[g.val]'hj).right := rfl
      have hbackg := hback g.val hj
      have hwlt : w < raw + g.val := by
        rcases hwr with h | h
        · rw [h, heqL]; exact hbackg.1
        · rw [h, heqR]; exact hbackg.2
      have hwr' : w = D.gates[g.val].left ∨ w = D.gates[g.val].right := by
        rcases hwr with h | h
        · exact Or.inl (h.trans heqL)
        · exact Or.inr (h.trans heqR)
      refine ⟨hwlt, ?_, ?_⟩
      · intro hgin
        have hinp : w ∈ (gateAt (binarySkeleton D) g.val).inputs := by
          rw [binarySkeleton_gate D g.val hj]
          simpa [eq_comm] using hwr'
        have := (hshape g.val hgin).2.2 w hinp
        rcases this with hW | hEnt
        · rcases Finset.mem_union.mp hW with hS' | himg
          · exact Or.inl (hsrc.symm ▸ hS')
          · exact Or.inr (Or.inl ((hinside w).mpr himg))
        · exact Or.inr (Or.inr hEnt)
      · intro hgout
        constructor
        · intro hs
          have hpriv : w ∈ S ∪ region.image (fun k => raw + k) := by
            rw [hsrc] at hs
            exact Finset.mem_union_left _ hs
          have hne_root : w ≠ root := by
            intro hwr
            -- sources are < raw, root = raw+top ≥ raw
            have : w < raw := by
              have : w ∈ sources := hs
              rw [hsrc] at this
              exact Finset.mem_range.mp (hS this)
            rw [hroot_eq] at hwr
            omega
          have hinp : w ∈ (gateAt (binarySkeleton D) g.val).inputs := by
            rw [binarySkeleton_gate D g.val hj]
            simpa [eq_comm] using hwr'
          have hjC : g.val < (binarySkeleton D).size := by simpa [hsz] using hj
          exact tree_outside_unread (n + m) (binarySkeleton D) S E region root
            hreg (fun w' hw' hne' => ⟨(hwires w' hw' hne').1, (hwires w' hw' hne').2.1⟩) hjC hgout hinp hpriv hne_root
        · intro hin
          have himg : w ∈ region.image (fun k => raw + k) := (hinside w).mp hin
          have hpriv : w ∈ S ∪ region.image (fun k => raw + k) :=
            Finset.mem_union_right _ himg
          by_cases hne_root : w = root
          · rw [hne_root, hroot_eq]
          · have hinp : w ∈ (gateAt (binarySkeleton D) g.val).inputs := by
              rw [binarySkeleton_gate D g.val hj]
              simpa [eq_comm] using hwr'
            have hjC : g.val < (binarySkeleton D).size := by simpa [hsz] using hj
            exact (tree_outside_unread (n + m) (binarySkeleton D) S E region root
              hreg (fun w' hw' hne' => ⟨(hwires w' hw' hne').1, (hwires w' hw' hne').2.1⟩) hjC hgout hinp hpriv
              hne_root).elim
    have hout_ns : D.output ∉ sources := by
      intro hs
      have hsS : D.output ∈ S := by rwa [hsrc] at hs
      have hlt : D.output < raw := Finset.mem_range.mp (hS hsS)
      have hpos : 0 < (binarySkeleton D).size := by
        obtain ⟨k, hk⟩ := hne
        have : k < (binarySkeleton D).size := Finset.mem_range.mp (hreg hk)
        omega
      have hout' : D.output + 1 = raw + (binarySkeleton D).size := hout
      omega
    have hout_in : (raw ≤ D.output ∧ D.output - raw ∈ region) → D.output = raw + top := by
      intro hin
      have himg : D.output ∈ region.image (fun k => raw + k) := (hinside D.output).mp hin
      have hpriv : D.output ∈ S ∪ region.image (fun k => raw + k) :=
        Finset.mem_union_right _ himg
      by_cases hne_root : D.output = root
      · rw [hne_root, hroot_eq]
      · have : (binarySkeleton D).output ≠ D.output :=
          (hwires D.output hpriv hne_root).2.2
        exact (this rfl).elim
    have hregD : region ⊆ Finset.range D.size := by
      simpa [BinaryCircuit.size, binarySkeleton_size] using hreg
    obtain ⟨hrowResp, hcolResp⟩ :=
      PEqualNP.Outside.L_meta_25872 n m D Rnm Cnm region E top
        hregD htop hentry hgates hout_ns hout_in
    -- Row-side 1-bit factorization
    obtain ⟨mask, response, hresp⟩ := hrowResp
    let t : Fin m → Bool := fun j =>
      if hneE : E.Nonempty then
        (D.wires (rowOff (n := n) j)).getD (E.min' hneE) false
      else false
    let q : Fin n → Bool → Bool := fun i bit => response i (fun _ => bit)
    let U : Fin m → Bool → Bool := fun j b =>
      outFn (xor (D.eval (rowOff (n := n) j)) (mask j && b))
    have hfactor : ∀ a ∈ Rnm, ∀ x, x ∉ Cnm → G a x = U x (q a (t x)) := by
      intro a ha x hx
      have hval := hresp a ha x hx
      -- value a x = D.eval (one n a ++ one m x) = D.eval (oneEach a x)
      have hone : List.ofFn (fun v : Fin n => decide (v = a)) ++
          List.ofFn (fun v : Fin m => decide (v = x)) = oneEach a x := rfl
      have hval' :
          (D.eval (oneEach a x) != D.eval (rowOff (n := n) x)) =
          (mask x && response a (fun e => (D.wires (rowOff (n := n) x)).getD e.val false)) := by
        simpa [hone, rowOff] using hval
      have hfun : (fun e : ↥E => (D.wires (rowOff (n := n) x)).getD e.val false) =
          (fun _ => t x) := by
        funext e
        have hneE : E.Nonempty := ⟨e.val, e.property⟩
        dsimp [t]
        simp only [hneE, ↓reduceDIte]
        have hcard1 : E.card = 1 := by
          have : 0 < E.card := Finset.card_pos.mpr hneE
          omega
        obtain ⟨b, hbE⟩ := Finset.card_eq_one.mp hcard1
        have huniq : ∀ x ∈ E, x = b := by
          intro x hx
          have : x ∈ ({b} : Finset ℕ) := by
            rw [← hbE]
            exact hx
          exact Finset.mem_singleton.mp this
        have hbmin : E.min' hneE = b := huniq _ (Finset.min'_mem E hneE)
        have heval : e.val = b := huniq _ e.property
        simp [hbmin, heval]
      have hxor : D.eval (oneEach a x) =
          xor (D.eval (rowOff (n := n) x))
            (mask x && response a (fun e => (D.wires (rowOff (n := n) x)).getD e.val false)) := by
        exact (xor_bne_cancel (D.eval (rowOff (n := n) x)) (D.eval (oneEach a x))).symm.trans
          (by rw [← bne_eq_xor, hval'])
      rw [← hrep, hxor, hfun]
    obtain ⟨maskC, responseC, hrespC⟩ := hcolResp
    let tC : Fin n → Bool := fun i =>
      if hneE : E.Nonempty then
        (D.wires (colOff (m := m) i)).getD (E.min' hneE) false
      else false
    let qC : Fin m → Bool → Bool := fun j bit => responseC j (fun _ => bit)
    let UC : Fin n → Bool → Bool := fun i b =>
      outFn (xor (D.eval (colOff (m := m) i)) (maskC i && b))
    have hfactorC : ∀ a ∈ Cnm, ∀ x, x ∉ Rnm → G x a = UC x (qC a (tC x)) := by
      intro a ha x hx
      have hone : List.ofFn (fun v : Fin n => decide (v = x)) ++
          List.ofFn (fun v : Fin m => decide (v = a)) = oneEach x a := rfl
      have hval' :
          (D.eval (oneEach x a) != D.eval (colOff (m := m) x)) =
          (maskC x && responseC a (fun e => (D.wires (colOff (m := m) x)).getD e.val false)) := by
        simpa [hone, colOff] using hrespC a ha x hx
      have hfun : (fun e : ↥E => (D.wires (colOff (m := m) x)).getD e.val false) =
          (fun _ => tC x) := by
        funext e
        have hneE : E.Nonempty := ⟨e.val, e.property⟩
        dsimp [tC]
        simp only [hneE, ↓reduceDIte]
        have hcard1 : E.card = 1 := by
          have : 0 < E.card := Finset.card_pos.mpr hneE
          omega
        obtain ⟨b, hbE⟩ := Finset.card_eq_one.mp hcard1
        have huniq : ∀ x ∈ E, x = b := by
          intro x hx
          have : x ∈ ({b} : Finset ℕ) := by
            rw [← hbE]
            exact hx
          exact Finset.mem_singleton.mp this
        have hbmin : E.min' hneE = b := huniq _ (Finset.min'_mem E hneE)
        have heval : e.val = b := huniq _ e.property
        simp [hbmin, heval]
      have hxor : D.eval (oneEach x a) =
          xor (D.eval (colOff (m := m) x))
            (maskC x && responseC a (fun e => (D.wires (colOff (m := m) x)).getD e.val false)) := by
        exact (xor_bne_cancel (D.eval (colOff (m := m) x)) (D.eval (oneEach x a))).symm.trans
          (by rw [← bne_eq_xor, hval'])
      rw [← hrep, hxor, hfun]
    let q0 : Bool → Bool := fun _ => false
    have h0 : ∀ x, x ∉ Cnm →
        outFn (D.eval (rowOff (n := n) x)) = U x (q0 (t x)) := by
      intro x _hx
      simp [U, q0, Bool.xor_false]
    let q0C : Bool → Bool := fun _ => false
    have h0C : ∀ x, x ∉ Rnm →
        outFn (D.eval (colOff (m := m) x)) = UC x (q0C (tC x)) := by
      intro x _hx
      simp [UC, q0C, Bool.xor_false]
    exact ⟨⟨t, q0, q, U, h0, hfactor⟩, ⟨tC, q0C, qC, UC, h0C, hfactorC⟩⟩


open Classical in
noncomputable def treeOfRegion (N : ℕ) (C : Circuit) (region E : Finset ℕ) (r : ℕ) : BTree :=
  if h : N ≤ r ∧ r - N ∈ region then
    let j := r - N
    let u0 := (gateAt C j).inputs.getD 0 0
    let u1 := (gateAt C j).inputs.getD 1 0
    let child (u : ℕ) : BTree :=
      if u ∈ E then BTree.mark u
      else if u < N then BTree.priv u
      else if hu : u < r then treeOfRegion N C region E u
      else BTree.mark u
    BTree.node j (child u0) (child u1)
  else if r < N then BTree.priv r
  else BTree.mark r
termination_by r
decreasing_by
  all_goals (try exact hu)

lemma treeOfRegion_root (N : ℕ) (C : Circuit) (region E : Finset ℕ) (r : ℕ) :
    (treeOfRegion N C region E r).root N = r := by
  unfold treeOfRegion
  split_ifs with h1 h2
  · simp only [BTree.root]; omega
  · rfl
  · rfl

lemma marked_union_one (L : List (Finset ℕ)) (H : Finset ℕ)
    (separate : L.Pairwise Disjoint)
    (small : ∀ S ∈ L, S.card ≤ 2 + (S ∩ H).card) :
    (L.toFinset.biUnion id).card ≤ 2 * L.length + ((L.toFinset.biUnion id) ∩ H).card := by
  classical
  induction L with
  | nil => simp
  | cons S l ih =>
    obtain ⟨bySet, rest⟩ := List.pairwise_cons.mp separate
    have bound := small S (by simp)
    have tail := ih rest (fun t ht => small t (by simp [ht]))
    let A := l.toFinset.biUnion id
    have dis : Disjoint S A := by
      apply Finset.disjoint_left.mpr
      intro w ws wa
      obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp wa
      exact Finset.disjoint_left.mp (bySet t (List.mem_toFinset.mp ht)) ws hit
    have di : Disjoint (S ∩ H) (A ∩ H) := by
      apply Finset.disjoint_left.mpr
      intro w hs ha
      exact Finset.disjoint_left.mp dis (Finset.mem_inter.mp hs).1 (Finset.mem_inter.mp ha).1
    rw [List.toFinset_cons, Finset.biUnion_insert, List.length_cons]
    change (S ∪ A).card ≤ 2 * (l.length + 1) + ((S ∪ A) ∩ H).card
    rw [Finset.card_union_of_disjoint dis, Finset.union_inter_distrib_right,
      Finset.card_union_of_disjoint di]
    change A.card ≤ 2 * l.length + (A ∩ H).card at tail
    omega

private noncomputable def treeChild (N : ℕ) (C : Circuit) (region E : Finset ℕ) (r u : ℕ) : BTree :=
  if u ∈ E then BTree.mark u
  else if u < N then BTree.priv u
  else if hu : u < r then treeOfRegion N C region E u
  else BTree.mark u

lemma treeChild_root (N : ℕ) (C : Circuit) (region E : Finset ℕ) (r u : ℕ) :
    (treeChild N C region E r u).root N = u := by
  unfold treeChild
  split_ifs
  · rfl
  · rfl
  · exact treeOfRegion_root N C region E u
  · rfl

lemma treeOfRegion_eq_node (N : ℕ) (C : Circuit) (region E : Finset ℕ) {r : ℕ}
    (h : N ≤ r ∧ r - N ∈ region) :
    treeOfRegion N C region E r =
      BTree.node (r - N)
        (treeChild N C region E r ((gateAt C (r - N)).inputs.getD 0 0))
        (treeChild N C region E r ((gateAt C (r - N)).inputs.getD 1 0)) := by
  rw [treeOfRegion, dif_pos h]
  rfl

lemma len2_inputs (l : List ℕ) (h : l.length = 2) :
    l = [l.getD 0 0, l.getD 1 0] := by
  obtain ⟨a, b, rfl⟩ := List.length_eq_two.mp h
  simp

noncomputable def regParent (C : Circuit) (region : Finset ℕ) (w : ℕ) : ℕ :=
  if h : readsIn C region w = 1 then
    Classical.choose (readsIn_eq_one_unique C region w h)
  else 0

lemma regParent_spec {C : Circuit} {region : Finset ℕ} {w : ℕ}
    (h : readsIn C region w = 1) :
    regParent C region w ∈ region ∧
      w ∈ (gateAt C (regParent C region w)).inputs ∧
      (gateAt C (regParent C region w)).inputs.count w = 1 ∧
      ∀ j' ∈ region, w ∈ (gateAt C j').inputs → j' = regParent C region w := by
  dsimp [regParent]
  simp only [h, ↓reduceDIte]
  exact Classical.choose_spec (readsIn_eq_one_unique C region w h)

inductive Reaches (N : ℕ) (C : Circuit) (region : Finset ℕ) : ℕ → ℕ → Prop where
  | refl (w : ℕ) : Reaches N C region w w
  | climb (w r : ℕ) (hread : readsIn C region w = 1)
      (hnext : Reaches N C region (N + regParent C region w) r) :
      Reaches N C region w r

lemma reaches_trans {N : ℕ} {C : Circuit} {region : Finset ℕ} {w a r : ℕ}
    (h1 : Reaches N C region w a) (h2 : Reaches N C region a r) :
    Reaches N C region w r := by
  induction h1 with
  | refl => exact h2
  | climb w a hread hnext ih => exact Reaches.climb w r hread (ih h2)

lemma reaches_le {N : ℕ} {C : Circuit} {region : Finset ℕ} {w r : ℕ}
    (h : Reaches N C region w r) (hback : ReadsBack N C)
    (hsub : region ⊆ Finset.range C.size) : w ≤ r := by
  induction h with
  | refl => exact le_rfl
  | climb w r hread hnext ih =>
    have ⟨hp, hw, _, _⟩ := regParent_spec hread
    have hjlt : regParent C region w < C.size := Finset.mem_range.mp (hsub hp)
    have hlt : w < N + regParent C region w := hback _ hjlt w hw
    omega

lemma reaches_lt {N : ℕ} {C : Circuit} {region : Finset ℕ} {w r : ℕ}
    (h : Reaches N C region w r) (hne : w ≠ r) (hback : ReadsBack N C)
    (hsub : region ⊆ Finset.range C.size) : w < r := by
  cases h with
  | refl => exact (hne rfl).elim
  | climb w r hread hnext =>
    have ⟨hp, hw, _, _⟩ := regParent_spec hread
    have hjlt : regParent C region w < C.size := Finset.mem_range.mp (hsub hp)
    have hlt : w < N + regParent C region w := hback _ hjlt w hw
    have hle := reaches_le hnext hback hsub
    omega

lemma reaches_pred {N : ℕ} {C : Circuit} {region : Finset ℕ} {w r : ℕ}
    (h : Reaches N C region w r) (hne : w ≠ r) :
    readsIn C region w = 1 ∧ Reaches N C region (N + regParent C region w) r := by
  cases h with
  | refl => exact (hne rfl).elim
  | climb _ _ hread hnext => exact ⟨hread, hnext⟩

lemma reaches_chain {N : ℕ} {C : Circuit} {region : Finset ℕ} {w a r : ℕ}
    (ha : Reaches N C region w a) (hr : Reaches N C region w r) :
    Reaches N C region a r ∨ Reaches N C region r a := by
  induction hr generalizing a with
  | refl => exact Or.inr ha
  | climb w r hread hnext ih =>
    cases ha with
    | refl => exact Or.inl (Reaches.climb w r hread hnext)
    | climb w a _ hnext' => exact ih hnext'

lemma reaches_one_step {N : ℕ} {C : Circuit} {region : Finset ℕ} {w : ℕ}
    (hread : readsIn C region w = 1) :
    Reaches N C region w (N + regParent C region w) :=
  Reaches.climb w _ hread (Reaches.refl _)

lemma reaches_siblings {N : ℕ} {C : Circuit} {region : Finset ℕ} {w u0 u1 : ℕ}
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (h0 : Reaches N C region w u0) (h1 : Reaches N C region w u1)
    (hne : u0 ≠ u1)
    (hr0 : readsIn C region u0 = 1) (hr1 : readsIn C region u1 = 1)
    (hp : regParent C region u0 = regParent C region u1) : False := by
  have ⟨hp0, hw0, _, _⟩ := regParent_spec hr0
  have ⟨hp1, hw1, _, _⟩ := regParent_spec hr1
  have hj0 : regParent C region u0 < C.size := Finset.mem_range.mp (hsub hp0)
  have hlt0 : u0 < N + regParent C region u0 := hback _ hj0 u0 hw0
  have hup1 : Reaches N C region u1 (N + regParent C region u1) :=
    reaches_one_step (N := N) hr1
  rcases reaches_chain h0 h1 with h01 | h10
  · have hne' : u0 ≠ u1 := hne
    have hpred := reaches_pred h01 hne'
    have : Reaches N C region (N + regParent C region u0) u1 := hpred.2
    rw [hp] at this
    have hneP : u1 ≠ N + regParent C region u1 := by
      have hj1 : regParent C region u1 < C.size := Finset.mem_range.mp (hsub hp1)
      have : u1 < N + regParent C region u1 := hback _ hj1 u1 hw1
      omega
    have hltA := reaches_lt this (Ne.symm hneP) hback hsub
    have hltB := reaches_lt hup1 hneP hback hsub
    omega
  · have hpred := reaches_pred h10 hne.symm
    have : Reaches N C region (N + regParent C region u1) u0 := hpred.2
    rw [← hp] at this
    have hneP : u0 ≠ N + regParent C region u0 := by omega
    have hltA := reaches_lt this (Ne.symm hneP) hback hsub
    have hup0 : Reaches N C region u0 (N + regParent C region u0) :=
      reaches_one_step (N := N) hr0
    have hltB := reaches_lt hup0 hneP hback hsub
    omega

lemma treeOfRegion_eq_priv {N : ℕ} {C : Circuit} {region E : Finset ℕ} {r : ℕ}
    (hreg : ¬(N ≤ r ∧ r - N ∈ region)) (hraw : r < N) :
    treeOfRegion N C region E r = BTree.priv r := by
  rw [treeOfRegion]
  simp [hreg, hraw]

lemma treeChild_cases {N : ℕ} {C : Circuit} {region E : Finset ℕ} {r u : ℕ}
    (hult : u < r) :
    (u ∈ E ∧ treeChild N C region E r u = BTree.mark u) ∨
      (u ∉ E ∧ u < N ∧ treeChild N C region E r u = BTree.priv u) ∨
      (u ∉ E ∧ ¬(u < N) ∧
        treeChild N C region E r u = treeOfRegion N C region E u) := by
  unfold treeChild
  by_cases hE : u ∈ E
  · refine Or.inl ⟨hE, ?_⟩
    simp [hE]
  · by_cases hN : u < N
    · refine Or.inr (Or.inl ⟨hE, hN, ?_⟩)
      simp [hE, hN]
    · refine Or.inr (Or.inr ⟨hE, hN, ?_⟩)
      simp [hE, hN, hult]

lemma treeChild_privs_marks_gates {N : ℕ} {C : Circuit} {S E region : Finset ℕ}
    {root r u : ℕ}
    (_hback : ReadsBack N C)
    (_hE : E.card ≤ 1)
    (_hneR : region.Nonempty)
    (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (_hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hEcond : ∀ b ∈ E, b ∉ S ∪ region.image (fun k => N + k) ∧ b < root ∧
      readsIn C region b = 1)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    (ih : ∀ u < r, u ∈ S ∪ region.image (fun k => N + k) →
      GoodTree N C (treeOfRegion N C region E u) ∧
        (treeOfRegion N C region E u).privs ⊆ S ∧
        (treeOfRegion N C region E u).marks ≤ 1 ∧
        (treeOfRegion N C region E u).gates ⊆ region)
    {j : ℕ} (hjR : j ∈ region) (hum : u ∈ (gateAt C j).inputs) (hult : u < r) :
    GoodTree N C (treeChild N C region E r u) ∧
      (treeChild N C region E r u).privs ⊆ S ∧
      (treeChild N C region E r u).marks ≤ 1 ∧
      (treeChild N C region E r u).gates ⊆ region ∧
      ((treeChild N C region E r u).nonMark →
        readsOf C ((treeChild N C region E r u).root N) = 1) := by
  have huor := (hshape j hjR).2.2 u hum
  have hne_root : u ≠ root := by
    intro heq
    have : readsIn C region u = 0 := by simpa [heq] using hlr0
    have hcnt_pos : 0 < readsIn C region u :=
      lt_of_lt_of_le (List.count_pos_iff.mpr hum)
        (Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count u)
          (fun _ _ => Nat.zero_le _) hjR)
    omega
  rcases treeChild_cases (N := N) (C := C) (region := region) (E := E) (r := r) (u := u)
    hult with hmk | hpv | hrec
  · obtain ⟨_, heq⟩ := hmk
    rw [heq]
    exact ⟨trivial, by simp [BTree.privs], by simp [BTree.marks],
      by simp [BTree.gates], fun h => False.elim h⟩
  · obtain ⟨hEu, hRu, heq⟩ := hpv
    rw [heq]
    have huS : u ∈ S := by
      rcases huor with hW | hEE
      · rcases Finset.mem_union.mp hW with hS' | himg
        · exact hS'
        · obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp himg
          omega
      · exact (hEu hEE).elim
    have hrd := hwires u (Finset.mem_union_left _ huS) hne_root
    refine ⟨⟨Finset.mem_range.mp (hS huS), hrd.2.1⟩,
      Finset.singleton_subset_iff.mpr huS,
      by simp [BTree.marks], by simp [BTree.gates], ?_⟩
    intro
    simpa [BTree.root] using hrd.2.1
  · obtain ⟨hEu, hNu, heq⟩ := hrec
    rw [heq]
    have huW : u ∈ S ∪ region.image (fun k => N + k) := by
      rcases huor with hW | hEE
      · exact hW
      · exact (hEu hEE).elim
    have ⟨hg, hpv, hmk, hgs⟩ := ih u hult huW
    refine ⟨hg, hpv, hmk, hgs, ?_⟩
    intro
    rw [treeOfRegion_root]
    exact (hwires u huW hne_root).2.1

lemma treeOfRegion_marks_zero_of_empty {N : ℕ} {C : Circuit}
    {S E region : Finset ℕ} {r : ℕ}
    (hE0 : E = ∅) (hS : S ⊆ Finset.range N)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (hrw : r ∈ S ∪ region.image (fun k => N + k)) :
    (treeOfRegion N C region E r).marks = 0 := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hreg : N ≤ r ∧ r - N ∈ region
    · have heq := treeOfRegion_eq_node N C region E hreg
      rw [heq]
      set j := r - N
      set u0 := (gateAt C j).inputs.getD 0 0
      set u1 := (gateAt C j).inputs.getD 1 0
      have hjR : j ∈ region := hreg.2
      have hjlt : j < C.size := Finset.mem_range.mp (hsub hjR)
      have hlen := (hshape j hjR).2.1
      have hinpEq : (gateAt C j).inputs = [u0, u1] := by
        simpa [u0, u1] using len2_inputs _ hlen
      have hu0mem : u0 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu1mem : u1 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu0lt : u0 < r := by
        have := hback j hjlt u0 hu0mem; omega
      have hu1lt : u1 < r := by
        have := hback j hjlt u1 hu1mem; omega
      have aux (u : ℕ) (hum : u ∈ (gateAt C j).inputs) (hult : u < r) :
          (treeChild N C region E r u).marks = 0 := by
        rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
          (r := r) (u := u) hult with hmk | hpv | hrec
        · exact (Finset.notMem_empty _ (hE0 ▸ hmk.1)).elim
        · rw [hpv.2.2]; rfl
        · rw [hrec.2.2]
          have huW : u ∈ S ∪ region.image (fun k => N + k) := by
            rcases (hshape j hjR).2.2 u hum with hW | hEE
            · exact hW
            · exact (Finset.notMem_empty _ (hE0 ▸ hEE)).elim
          exact ih u hult huW
      have z0 := aux u0 hu0mem hu0lt
      have z1 := aux u1 hu1mem hu1lt
      simp [BTree.marks, z0, z1]
    · have hraw : r < N := by
        rcases Finset.mem_union.mp hrw with hS' | himg
        · exact Finset.mem_range.mp (hS hS')
        · obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp himg
          have hNle : N ≤ r := by omega
          have hmem : r - N ∈ region := by
            have : r - N = k := by omega
            simpa [this] using hk
          exact (hreg ⟨hNle, hmem⟩).elim
      rw [treeOfRegion_eq_priv hreg hraw]
      simp [BTree.marks]

lemma treeOfRegion_gates_reaches {N : ℕ} {C : Circuit} {S E region : Finset ℕ}
    {root r : ℕ}
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hEcond : ∀ b ∈ E, b ∉ S ∪ region.image (fun k => N + k) ∧ b < root ∧
      readsIn C region b = 1)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    (hrw : r ∈ S ∪ region.image (fun k => N + k))
    {k : ℕ} (hk : k ∈ (treeOfRegion N C region E r).gates) :
    k ∈ region ∧ N + k ≤ r ∧ Reaches N C region (N + k) r := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hreg : N ≤ r ∧ r - N ∈ region
    · have heq := treeOfRegion_eq_node N C region E hreg
      rw [heq] at hk
      set j := r - N
      set u0 := (gateAt C j).inputs.getD 0 0
      set u1 := (gateAt C j).inputs.getD 1 0
      have hjR : j ∈ region := hreg.2
      have hjlt : j < C.size := Finset.mem_range.mp (hsub hjR)
      have hlen := (hshape j hjR).2.1
      have hinpEq : (gateAt C j).inputs = [u0, u1] := by
        simpa [u0, u1] using len2_inputs _ hlen
      have hu0mem : u0 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu1mem : u1 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu0lt : u0 < r := by
        have := hback j hjlt u0 hu0mem; omega
      have hu1lt : u1 < r := by
        have := hback j hjlt u1 hu1mem; omega
      have hroot_step (u : ℕ) (hum : u ∈ (gateAt C j).inputs)
          (hrec : u ∉ E ∧ ¬(u < N) ∧
            treeChild N C region E r u = treeOfRegion N C region E u) :
          u ∈ S ∪ region.image (fun t => N + t) ∧ u ≠ root ∧
            readsIn C region u = 1 ∧
            regParent C region u = j := by
        have huW : u ∈ S ∪ region.image (fun t => N + t) := by
          rcases (hshape j hjR).2.2 u hum with hW | hEE
          · exact hW
          · exact (hrec.1 hEE).elim
        have hne : u ≠ root := by
          intro heq
          have : readsIn C region u = 0 := by simpa [heq] using hlr0
          have hcnt_pos : 0 < readsIn C region u :=
            lt_of_lt_of_le (List.count_pos_iff.mpr hum)
              (Finset.single_le_sum (f := fun t => (gateAt C t).inputs.count u)
                (fun _ _ => Nat.zero_le _) hjR)
          omega
        have hrd := (hwires u huW hne).1
        have hpar : regParent C region u = j :=
          ((regParent_spec hrd).2.2.2 j hjR hum).symm
        exact ⟨huW, hne, hrd, hpar⟩
      simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hk
      have hjr : N + j = r := by omega
      rcases hk with hk | hk | hk
      · subst hk
        have hreach : Reaches N C region (N + j) r := by
          simpa [hjr] using
            (Reaches.refl (N := N) (C := C) (region := region) r)
        exact ⟨hjR, by omega, hreach⟩
      · rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
          (r := r) (u := u0) hu0lt with hmk | hpv | hrec
        · rw [hmk.2] at hk; simp [BTree.gates] at hk
        · rw [hpv.2.2] at hk; simp [BTree.gates] at hk
        · rw [hrec.2.2] at hk
          obtain ⟨huW, _, hrd, hpar⟩ := hroot_step u0 hu0mem hrec
          have ⟨hkR, hkle, hreach⟩ := ih u0 hu0lt huW hk
          have hup : Reaches N C region u0 r := by
            have : N + regParent C region u0 = r := by rw [hpar, hjr]
            simpa [this] using reaches_one_step (N := N) hrd
          exact ⟨hkR, by omega, reaches_trans hreach hup⟩
      · rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
          (r := r) (u := u1) hu1lt with hmk | hpv | hrec
        · rw [hmk.2] at hk; simp [BTree.gates] at hk
        · rw [hpv.2.2] at hk; simp [BTree.gates] at hk
        · rw [hrec.2.2] at hk
          obtain ⟨huW, _, hrd, hpar⟩ := hroot_step u1 hu1mem hrec
          have ⟨hkR, hkle, hreach⟩ := ih u1 hu1lt huW hk
          have hup : Reaches N C region u1 r := by
            have : N + regParent C region u1 = r := by rw [hpar, hjr]
            simpa [this] using reaches_one_step (N := N) hrd
          exact ⟨hkR, by omega, reaches_trans hreach hup⟩
    · have hraw : r < N := by
        rcases Finset.mem_union.mp hrw with hS' | himg
        · exact Finset.mem_range.mp (hS hS')
        · obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp himg
          have hNle : N ≤ r := by omega
          have hmem : r - N ∈ region := by
            have : r - N = k := by omega
            simpa [this] using hk
          exact (hreg ⟨hNle, hmem⟩).elim
      rw [treeOfRegion_eq_priv hreg hraw] at hk
      simp [BTree.gates] at hk

lemma treeOfRegion_mark_witness {N : ℕ} {C : Circuit} {S E region : Finset ℕ}
    {r : ℕ}
    (hS : S ⊆ Finset.range N)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (hrw : r ∈ S ∪ region.image (fun k => N + k))
    (hpos : 1 ≤ (treeOfRegion N C region E r).marks) :
    ∃ b, b ∈ E ∧ ∃ k ∈ (treeOfRegion N C region E r).gates,
      b ∈ (gateAt C k).inputs := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hreg : N ≤ r ∧ r - N ∈ region
    · have heq := treeOfRegion_eq_node N C region E hreg
      rw [heq] at hpos ⊢
      set j := r - N
      set u0 := (gateAt C j).inputs.getD 0 0
      set u1 := (gateAt C j).inputs.getD 1 0
      have hjR : j ∈ region := hreg.2
      have hjlt : j < C.size := Finset.mem_range.mp (hsub hjR)
      have hlen := (hshape j hjR).2.1
      have hinpEq : (gateAt C j).inputs = [u0, u1] := by
        simpa [u0, u1] using len2_inputs _ hlen
      have hu0mem : u0 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu1mem : u1 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu0lt : u0 < r := by
        have := hback j hjlt u0 hu0mem; omega
      have hu1lt : u1 < r := by
        have := hback j hjlt u1 hu1mem; omega
      have hchild (u : ℕ) (hum : u ∈ (gateAt C j).inputs) (hult : u < r)
          (hposc : 1 ≤ (treeChild N C region E r u).marks) :
          ∃ b, b ∈ E ∧ ∃ k ∈ (BTree.node (r - N)
              (treeChild N C region E r u0)
              (treeChild N C region E r u1)).gates,
            b ∈ (gateAt C k).inputs := by
        rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
          (r := r) (u := u) hult with hmk | hpv | hrec
        · refine ⟨u, hmk.1, r - N, ?_, ?_⟩
          · simp [BTree.gates]
          · simpa [hmk.2] using hum
        · rw [hpv.2.2] at hposc; simp [BTree.marks] at hposc
        · rw [hrec.2.2] at hposc
          have huW : u ∈ S ∪ region.image (fun t => N + t) := by
            rcases (hshape j hjR).2.2 u hum with hW | hEE
            · exact hW
            · exact (hrec.1 hEE).elim
          obtain ⟨b, hbE, k, hk, hin⟩ := ih u hult huW hposc
          refine ⟨b, hbE, k, ?_, hin⟩
          simp only [BTree.gates, Finset.mem_insert, Finset.mem_union]
          rw [← hrec.2.2] at hk
          have huor : u = u0 ∨ u = u1 := by
            rw [hinpEq] at hum; simp at hum; exact hum
          rcases huor with hu | hu
          · exact Or.inr (Or.inl (by simpa [hu] using hk))
          · exact Or.inr (Or.inr (by simpa [hu] using hk))
      simp only [BTree.marks] at hpos
      by_cases hpos0 : 1 ≤ (treeChild N C region E r u0).marks
      · exact hchild u0 hu0mem hu0lt hpos0
      · have hpos1 : 1 ≤ (treeChild N C region E r u1).marks := by omega
        exact hchild u1 hu1mem hu1lt hpos1
    · have hraw : r < N := by
        rcases Finset.mem_union.mp hrw with hS' | himg
        · exact Finset.mem_range.mp (hS hS')
        · obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp himg
          have hNle : N ≤ r := by omega
          have hmem : r - N ∈ region := by
            have : r - N = k := by omega
            simpa [this] using hk
          exact (hreg ⟨hNle, hmem⟩).elim
      rw [treeOfRegion_eq_priv hreg hraw] at hpos
      simp [BTree.marks] at hpos

lemma treeOfRegion_good {N : ℕ} {C : Circuit} {S E region : Finset ℕ} {root r : ℕ}
    (hback : ReadsBack N C)
    (hE : E.card ≤ 1)
    (hneR : region.Nonempty)
    (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hEcond : ∀ b ∈ E, b ∉ S ∪ region.image (fun k => N + k) ∧ b < root ∧
      readsIn C region b = 1)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    (hrw : r ∈ S ∪ region.image (fun k => N + k)) :
    GoodTree N C (treeOfRegion N C region E r) ∧
      (treeOfRegion N C region E r).privs ⊆ S ∧
      (treeOfRegion N C region E r).marks ≤ 1 ∧
      (treeOfRegion N C region E r).gates ⊆ region := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    have ⟨top, htopMem, hrootEq⟩ :=
      tree_root_is_gate N C S region root hsub hroot
        (fun w hw hne => (hwires w hw hne).1) hback hneR
    by_cases hreg : N ≤ r ∧ r - N ∈ region
    · have heq := treeOfRegion_eq_node N C region E hreg
      rw [heq]
      set j := r - N
      set u0 := (gateAt C j).inputs.getD 0 0
      set u1 := (gateAt C j).inputs.getD 1 0
      have hjR : j ∈ region := hreg.2
      have hjlt : j < C.size := Finset.mem_range.mp (hsub hjR)
      have ⟨hop, hlen, hinp⟩ := hshape j hjR
      have hinpEq : (gateAt C j).inputs = [u0, u1] := by
        simpa [u0, u1] using len2_inputs _ hlen
      have hu0mem : u0 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu1mem : u1 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu0lt : u0 < r := by
        have := hback j hjlt u0 hu0mem; omega
      have hu1lt : u1 < r := by
        have := hback j hjlt u1 hu1mem; omega
      have hc0 := treeChild_privs_marks_gates (S := S) (E := E) (region := region)
        (root := root) (r := r) (u := u0) hback hE hneR hsub hS hroot hlr0 hEcond
        hshape hwires (fun u hult huW => ih u hult huW) hjR hu0mem hu0lt
      have hc1 := treeChild_privs_marks_gates (S := S) (E := E) (region := region)
        (root := root) (r := r) (u := u1) hback hE hneR hsub hS hroot hlr0 hEcond
        hshape hwires (fun u hult huW => ih u hult huW) hjR hu1mem hu1lt
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨hjlt, hop, ?_, hc0.1, hc1.1, hc0.2.2.2.2, hc1.2.2.2.2⟩
        rw [hinpEq, treeChild_root, treeChild_root]
      · simp only [BTree.privs]
        exact Finset.union_subset hc0.2.1 hc1.2.1
      · simp only [BTree.marks]
        have hm0 := hc0.2.2.1
        have hm1 := hc1.2.2.1
        by_contra hmk
        have hpos0 : 1 ≤ (treeChild N C region E r u0).marks := by omega
        have hpos1 : 1 ≤ (treeChild N C region E r u1).marks := by omega
        have hEne : E.Nonempty := by
          by_contra hz
          have hE0 : E = ∅ := Finset.not_nonempty_iff_eq_empty.mp hz
          have z0 : (treeChild N C region E r u0).marks = 0 := by
            have := treeOfRegion_marks_zero_of_empty (S := S) (E := E)
              (region := region) (r := r) hE0 hS hshape hback hsub hrw
            -- not quite — need the child, not the node
            rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
              (r := r) (u := u0) hu0lt with hM | hP | hR
            · exact (Finset.notMem_empty _ (hE0 ▸ hM.1)).elim
            · rw [hP.2.2]; rfl
            · rw [hR.2.2]
              have huW : u0 ∈ S ∪ region.image (fun t => N + t) := by
                rcases (hshape j hjR).2.2 u0 hu0mem with hW | hEE
                · exact hW
                · exact (Finset.notMem_empty _ (hE0 ▸ hEE)).elim
              exact treeOfRegion_marks_zero_of_empty (S := S) hE0 hS hshape
                hback hsub huW
          omega
        obtain ⟨b, hbE⟩ := hEne
        have hcard : E.card = 1 := by
          have : 0 < E.card := Finset.card_pos.mpr ⟨b, hbE⟩
          omega
        have huniq : ∀ x ∈ E, x = b := by
          obtain ⟨b', hb'⟩ := Finset.card_eq_one.mp hcard
          intro x hx
          have hx' : x ∈ ({b'} : Finset ℕ) := hb' ▸ hx
          have hbE' : b ∈ ({b'} : Finset ℕ) := hb' ▸ hbE
          simp only [Finset.mem_singleton] at hx' hbE'
          exact hbE'.symm ▸ hx'
        have hb1 := (hEcond b hbE).2.2
        -- witnesses from each marks-positive child
        have wit (u : ℕ) (hum : u ∈ (gateAt C j).inputs) (hult : u < r)
            (hposc : 1 ≤ (treeChild N C region E r u).marks) :
            u = b ∨ ∃ k ∈ (treeChild N C region E r u).gates,
              b ∈ (gateAt C k).inputs := by
          rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
            (r := r) (u := u) hult with hM | hP | hR
          · have : u = b := huniq u hM.1
            exact Or.inl this
          · rw [hP.2.2] at hposc; simp [BTree.marks] at hposc
          · rw [hR.2.2] at hposc
            have huW : u ∈ S ∪ region.image (fun t => N + t) := by
              rcases (hshape j hjR).2.2 u hum with hW | hEE
              · exact hW
              · exact (hR.1 hEE).elim
            obtain ⟨b', hb'E, k, hk, hin⟩ :=
              treeOfRegion_mark_witness (S := S) hS hshape hback hsub huW hposc
            have hb'eq : b' = b := huniq b' hb'E
            refine Or.inr ⟨k, ?_, by simpa [hb'eq] using hin⟩
            rw [hR.2.2]; exact hk
        have w0 := wit u0 hu0mem hu0lt hpos0
        have w1 := wit u1 hu1mem hu1lt hpos1
        have hjr : N + j = r := by omega
        have htwo : 2 ≤ readsIn C region b := by
          rcases w0 with h0b | ⟨k0, hk0, hin0⟩ <;>
            rcases w1 with h1b | ⟨k1, hk1, hin1⟩
          · -- both children are the mark leaf b, so this gate reads b twice
            have hcnt2 : (gateAt C j).inputs.count b = 2 := by
              rw [hinpEq, h0b, h1b]
              simp [List.count_cons, List.count_nil]
            have hle := Finset.single_le_sum
              (f := fun t => (gateAt C t).inputs.count b)
              (fun _ _ => Nat.zero_le _) hjR
            have : 2 ≤ readsIn C region b := by
              unfold readsIn at hle ⊢
              omega
            exact this
          · -- left is mark b, right has a deeper gate k1
            have ⟨hk1R, hk1le, _⟩ : k1 ∈ region ∧ N + k1 ≤ u1 ∧
                Reaches N C region (N + k1) u1 := by
              rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
                (r := r) (u := u1) hu1lt with hM | hP | hR
              · rw [hM.2] at hk1; simp [BTree.gates] at hk1
              · rw [hP.2.2] at hk1; simp [BTree.gates] at hk1
              · rw [hR.2.2] at hk1
                have huW : u1 ∈ S ∪ region.image (fun t => N + t) := by
                  rcases (hshape j hjR).2.2 u1 hu1mem with hW | hEE
                  · exact hW
                  · exact (hR.1 hEE).elim
                have := treeOfRegion_gates_reaches (S := S) (E := E)
                  (region := region) (root := root) (r := u1)
                  hback hsub hS hroot hlr0 hEcond hshape hwires huW hk1
                exact this
            have hjdef : j = r - N := rfl
            have hrj : r = N + j := by
              have : N ≤ r := hreg.1
              omega
            have hkne : j ≠ k1 := by
              have : N + k1 < N + j := by omega
              omega
            have hsub2 : ({j, k1} : Finset ℕ) ⊆ region := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            have hle := Finset.sum_le_sum_of_subset
              (f := fun i => (gateAt C i).inputs.count b) hsub2
            have hne : j ≠ k1 := hkne
            rw [Finset.sum_pair hne] at hle
            have c0 : 0 < (gateAt C j).inputs.count b := by
              apply List.count_pos_iff.mpr
              simpa [h0b] using hu0mem
            have c1 : 0 < (gateAt C k1).inputs.count b :=
              List.count_pos_iff.mpr hin1
            unfold readsIn
            omega
          · -- symmetric
            have ⟨hk0R, hk0le, _⟩ : k0 ∈ region ∧ N + k0 ≤ u0 ∧
                Reaches N C region (N + k0) u0 := by
              rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
                (r := r) (u := u0) hu0lt with hM | hP | hR
              · rw [hM.2] at hk0; simp [BTree.gates] at hk0
              · rw [hP.2.2] at hk0; simp [BTree.gates] at hk0
              · rw [hR.2.2] at hk0
                have huW : u0 ∈ S ∪ region.image (fun t => N + t) := by
                  rcases (hshape j hjR).2.2 u0 hu0mem with hW | hEE
                  · exact hW
                  · exact (hR.1 hEE).elim
                have := treeOfRegion_gates_reaches (S := S) (E := E)
                  (region := region) (root := root) (r := u0)
                  hback hsub hS hroot hlr0 hEcond hshape hwires huW hk0
                exact this
            have hjdef : j = r - N := rfl
            have hrj : r = N + j := by
              have : N ≤ r := hreg.1
              omega
            have hkne : j ≠ k0 := by
              have : N + k0 < N + j := by omega
              omega
            have hsub2 : ({j, k0} : Finset ℕ) ⊆ region := by
              intro x hx
              simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            have hle := Finset.sum_le_sum_of_subset
              (f := fun i => (gateAt C i).inputs.count b) hsub2
            rw [Finset.sum_pair hkne] at hle
            have c0 : 0 < (gateAt C k0).inputs.count b :=
              List.count_pos_iff.mpr hin0
            have c1 : 0 < (gateAt C j).inputs.count b := by
              apply List.count_pos_iff.mpr
              simpa [h1b] using hu1mem
            unfold readsIn
            omega
          · -- two deeper gates
            have rec1 (u : ℕ) (hum : u ∈ (gateAt C j).inputs) (hult : u < r)
                {k : ℕ} (hk : k ∈ (treeChild N C region E r u).gates) :
                u ∈ S ∪ region.image (fun t => N + t) ∧
                  k ∈ region ∧ N + k ≤ u ∧ Reaches N C region (N + k) u := by
              rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
                (r := r) (u := u) hult with hM | hP | hR
              · rw [hM.2] at hk; simp [BTree.gates] at hk
              · rw [hP.2.2] at hk; simp [BTree.gates] at hk
              · rw [hR.2.2] at hk
                have huW : u ∈ S ∪ region.image (fun t => N + t) := by
                  rcases (hshape j hjR).2.2 u hum with hW | hEE
                  · exact hW
                  · exact (hR.1 hEE).elim
                have := treeOfRegion_gates_reaches (S := S) (E := E)
                  (region := region) (root := root) (r := u)
                  hback hsub hS hroot hlr0 hEcond hshape hwires huW hk
                exact ⟨huW, this⟩
            obtain ⟨huW0, hk0R, hk0le, hreach0⟩ := rec1 u0 hu0mem hu0lt hk0
            obtain ⟨huW1, hk1R, hk1le, hreach1⟩ := rec1 u1 hu1mem hu1lt hk1
            by_cases hkeq : k0 = k1
            · -- same gate in both cones: sibling contradiction
              have hneU : u0 ≠ u1 := by
                intro heq
                have hcnt2 : (gateAt C j).inputs.count u0 = 2 := by
                  rw [hinpEq, heq]
                  simp [List.count_cons, List.count_nil]
                have hle := Finset.single_le_sum
                  (f := fun t => (gateAt C t).inputs.count u0)
                  (fun _ _ => Nat.zero_le _) hjR
                have hge : 2 ≤ readsIn C region u0 := by
                  unfold readsIn at hle ⊢; omega
                have hneR : u0 ≠ root := by
                  intro hr
                  have : readsIn C region u0 = 0 := by simpa [hr] using hlr0
                  omega
                have : readsIn C region u0 = 1 := (hwires u0 huW0 hneR).1
                omega
              have hrd0 : readsIn C region u0 = 1 := by
                have hneR : u0 ≠ root := by
                  intro hr
                  have : readsIn C region u0 = 0 := by simpa [hr] using hlr0
                  have hcnt_pos : 0 < readsIn C region u0 :=
                    lt_of_lt_of_le (List.count_pos_iff.mpr hu0mem)
                      (Finset.single_le_sum
                        (f := fun t => (gateAt C t).inputs.count u0)
                        (fun _ _ => Nat.zero_le _) hjR)
                  omega
                exact (hwires u0 huW0 hneR).1
              have hrd1 : readsIn C region u1 = 1 := by
                have hneR : u1 ≠ root := by
                  intro hr
                  have : readsIn C region u1 = 0 := by simpa [hr] using hlr0
                  have hcnt_pos : 0 < readsIn C region u1 :=
                    lt_of_lt_of_le (List.count_pos_iff.mpr hu1mem)
                      (Finset.single_le_sum
                        (f := fun t => (gateAt C t).inputs.count u1)
                        (fun _ _ => Nat.zero_le _) hjR)
                  omega
                exact (hwires u1 huW1 hneR).1
              have hpar0 : regParent C region u0 = j :=
                ((regParent_spec hrd0).2.2.2 j hjR hu0mem).symm
              have hpar1 : regParent C region u1 = j :=
                ((regParent_spec hrd1).2.2.2 j hjR hu1mem).symm
              rw [hkeq] at hreach0
              exact (reaches_siblings (N := N) (C := C) (region := region)
                (w := N + k1) (u0 := u0) (u1 := u1)
                hback hsub hreach0 hreach1 hneU hrd0 hrd1
                (by rw [hpar0, hpar1])).elim
            · have hsub2 : ({k0, k1} : Finset ℕ) ⊆ region := by
                intro x hx
                simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                rcases hx with rfl | rfl <;> assumption
              have hle := Finset.sum_le_sum_of_subset
                (f := fun i => (gateAt C i).inputs.count b) hsub2
              rw [Finset.sum_pair (Ne.symm (Ne.symm hkeq))] at hle
              have c0 : 0 < (gateAt C k0).inputs.count b :=
                List.count_pos_iff.mpr hin0
              have c1 : 0 < (gateAt C k1).inputs.count b :=
                List.count_pos_iff.mpr hin1
              unfold readsIn
              omega
        omega
      · simp only [BTree.gates]
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_union] at hk
        rcases hk with hk | hk0 | hk1
        · have hjdef : j = r - N := rfl
          have hjmem : r - N ∈ region := hjdef ▸ hjR
          have : k = r - N := by
            first | exact hk | simpa [hjdef] using hk
          exact this ▸ hjmem
        · exact hc0.2.2.2.1 hk0
        · exact hc1.2.2.2.1 hk1
    · have hraw : r < N := by
        rcases Finset.mem_union.mp hrw with hS' | himg
        · exact Finset.mem_range.mp (hS hS')
        · obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp himg
          have hNle : N ≤ r := by omega
          have hmem : r - N ∈ region := by
            have : r - N = k := by omega
            simpa [this] using hk
          exact (hreg ⟨hNle, hmem⟩).elim
      have hrS : r ∈ S := by
        rcases Finset.mem_union.mp hrw with hS' | himg
        · exact hS'
        · obtain ⟨k, _, hkEq⟩ := Finset.mem_image.mp himg
          omega
      have hne : r ≠ root := by
        intro h
        have : N ≤ root := by omega
        rw [← h] at this
        omega
      have hrd := hwires r (Finset.mem_union_left _ hrS) hne
      rw [treeOfRegion_eq_priv hreg hraw]
      exact ⟨⟨hraw, hrd.2.1⟩, Finset.singleton_subset_iff.mpr hrS,
        by simp [BTree.marks], by simp [BTree.gates]⟩




lemma treeOfRegion_subtree_mono {N : ℕ} {C : Circuit} {S E region : Finset ℕ}
    {root r : ℕ}
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hEcond : ∀ b ∈ E, b ∉ S ∪ region.image (fun k => N + k) ∧ b < root ∧
      readsIn C region b = 1)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    (hrw : r ∈ S ∪ region.image (fun k => N + k))
    {q : ℕ} (hq : q ∈ (treeOfRegion N C region E r).gates) :
    (treeOfRegion N C region E (N + q)).privs ⊆
        (treeOfRegion N C region E r).privs ∧
      (treeOfRegion N C region E (N + q)).gates ⊆
        (treeOfRegion N C region E r).gates := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases hreg : N ≤ r ∧ r - N ∈ region
    · have heq := treeOfRegion_eq_node N C region E hreg
      rw [heq] at hq ⊢
      set j := r - N
      set u0 := (gateAt C j).inputs.getD 0 0
      set u1 := (gateAt C j).inputs.getD 1 0
      have hjR : j ∈ region := hreg.2
      have hjlt : j < C.size := Finset.mem_range.mp (hsub hjR)
      have hlen := (hshape j hjR).2.1
      have hinpEq : (gateAt C j).inputs = [u0, u1] := by
        simpa [u0, u1] using len2_inputs _ hlen
      have hu0mem : u0 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu1mem : u1 ∈ (gateAt C j).inputs := by rw [hinpEq]; simp
      have hu0lt : u0 < r := by
        have := hback j hjlt u0 hu0mem; omega
      have hu1lt : u1 < r := by
        have := hback j hjlt u1 hu1mem; omega
      have child_sub (u : ℕ) (hum : u ∈ (gateAt C j).inputs) (hult : u < r)
          (hqc : q ∈ (treeChild N C region E r u).gates) :
          (treeOfRegion N C region E (N + q)).privs ⊆
              (BTree.node (r - N)
                (treeChild N C region E r u0)
                (treeChild N C region E r u1)).privs ∧
            (treeOfRegion N C region E (N + q)).gates ⊆
              (BTree.node (r - N)
                (treeChild N C region E r u0)
                (treeChild N C region E r u1)).gates := by
        rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
          (r := r) (u := u) hult with hM | hP | hR
        · rw [hM.2] at hqc; simp [BTree.gates] at hqc
        · rw [hP.2.2] at hqc; simp [BTree.gates] at hqc
        · rw [hR.2.2] at hqc
          have huW : u ∈ S ∪ region.image (fun t => N + t) := by
            rcases (hshape j hjR).2.2 u hum with hW | hEE
            · exact hW
            · exact (hR.1 hEE).elim
          have ⟨hpv, hgs⟩ := ih u hult huW hqc
          have huor : u = u0 ∨ u = u1 := by
            rw [hinpEq] at hum; simp at hum; exact hum
          have hpriv_sub : (treeOfRegion N C region E u).privs ⊆
              (BTree.node (r - N)
                (treeChild N C region E r u0)
                (treeChild N C region E r u1)).privs := by
            intro w hw
            simp only [BTree.privs, Finset.mem_union]
            rcases huor with hu | hu
            · have heqc : treeChild N C region E r u0 =
                  treeOfRegion N C region E u := by simpa [hu] using hR.2.2
              exact Or.inl (by simpa [heqc] using hw)
            · have heqc : treeChild N C region E r u1 =
                  treeOfRegion N C region E u := by simpa [hu] using hR.2.2
              exact Or.inr (by simpa [heqc] using hw)
          have hgates_sub : (treeOfRegion N C region E u).gates ⊆
              (BTree.node (r - N)
                (treeChild N C region E r u0)
                (treeChild N C region E r u1)).gates := by
            intro k hk
            simp only [BTree.gates, Finset.mem_insert, Finset.mem_union]
            rcases huor with hu | hu
            · have heqc : treeChild N C region E r u0 =
                  treeOfRegion N C region E u := by simpa [hu] using hR.2.2
              exact Or.inr (Or.inl (by simpa [heqc] using hk))
            · have heqc : treeChild N C region E r u1 =
                  treeOfRegion N C region E u := by simpa [hu] using hR.2.2
              exact Or.inr (Or.inr (by simpa [heqc] using hk))
          exact ⟨hpv.trans hpriv_sub, hgs.trans hgates_sub⟩
      simp only [BTree.gates, Finset.mem_insert, Finset.mem_union] at hq
      rcases hq with hq | hq0 | hq1
      · have hqj : q = r - N := by
          first | exact hq | (have hjdef : j = r - N := rfl; simpa [hjdef] using hq)
        subst hqj
        have hNr : N + (r - N) = r := Nat.add_sub_of_le hreg.1
        simp [hNr, heq]
      · exact child_sub u0 hu0mem hu0lt hq0
      · exact child_sub u1 hu1mem hu1lt hq1
    · have hraw : r < N := by
        rcases Finset.mem_union.mp hrw with hS' | himg
        · exact Finset.mem_range.mp (hS hS')
        · obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp himg
          have hNle : N ≤ r := by omega
          have hmem : r - N ∈ region := by
            have : r - N = k := by omega
            simpa [this] using hk
          exact (hreg ⟨hNle, hmem⟩).elim
      rw [treeOfRegion_eq_priv hreg hraw] at hq
      simp [BTree.gates] at hq

lemma climb_reaches_root {N : ℕ} {C : Circuit} {S E region : Finset ℕ} {root w : ℕ}
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    (hw : w ∈ S ∪ region.image (fun k => N + k)) :
    w ≤ root ∧ Reaches N C region w root := by
  have hWbound (x : ℕ) (hx : x ∈ S ∪ region.image (fun k => N + k)) :
      x < N + C.size := by
    rcases Finset.mem_union.mp hx with hS' | himg
    · have : x < N := Finset.mem_range.mp (hS hS')
      omega
    · obtain ⟨k, hk, hkEq⟩ := Finset.mem_image.mp himg
      have : k < C.size := Finset.mem_range.mp (hsub hk)
      omega
  have climbAux : ∀ (d x : ℕ), N + C.size - x = d →
      x ∈ S ∪ region.image (fun k => N + k) → x < N + C.size →
      x ≤ root ∧ Reaches N C region x root := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro x hd hx hxb
      by_cases heq : x = root
      · rw [heq]
        exact ⟨le_rfl, Reaches.refl (N := N) (C := C) (region := region) root⟩
      · have hrd := (hwires x hx heq).1
        have ⟨hp, hin, _, _⟩ := regParent_spec hrd
        have hjlt : regParent C region x < C.size := Finset.mem_range.mp (hsub hp)
        have hlt : x < N + regParent C region x := hback _ hjlt x hin
        have hnextW : N + regParent C region x ∈
            S ∪ region.image (fun k => N + k) :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hp, rfl⟩)
        have hnb : N + regParent C region x < N + C.size := by omega
        have hd' : N + C.size - (N + regParent C region x) < d := by omega
        have ⟨hle, hreach⟩ :=
          ih _ hd' (N + regParent C region x) rfl hnextW hnb
        exact ⟨by omega, Reaches.climb x root hrd hreach⟩
  exact climbAux (N + C.size - w) w rfl hw (hWbound w hw)


lemma reaches_gate_mem {N : ℕ} {C : Circuit} {S E region : Finset ℕ}
    {root r p : ℕ}
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hEcond : ∀ b ∈ E, b ∉ S ∪ region.image (fun k => N + k) ∧ b < root ∧
      readsIn C region b = 1)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    (hrw : r ∈ S ∪ region.image (fun k => N + k))
    (hpR : p ∈ region)
    (hR : Reaches N C region (N + p) r) :
    p ∈ (treeOfRegion N C region E r).gates := by
  have aux : ∀ (d x q : ℕ), r - x = d →
      Reaches N C region x r → x = N + q → q ∈ region →
      q ∈ (treeOfRegion N C region E r).gates := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro x q hd hxR hx hqR
      by_cases heq : x = r
      · have hreg : N ≤ r ∧ r - N ∈ region := by
          have : r = N + q := by simpa [heq] using hx
          refine ⟨by omega, ?_⟩
          have : r - N = q := by omega
          simpa [this] using hqR
        have heqT := treeOfRegion_eq_node N C region E hreg
        rw [heqT]
        have : r - N = q := by
          have : r = N + q := by simpa [heq] using hx
          omega
        simp [BTree.gates, this]
      · have ⟨hread, hnext⟩ := reaches_pred hxR heq
        set g := regParent C region x
        have ⟨hgR, hin, _, _⟩ := regParent_spec hread
        have hlt : x < N + g := by
          have hjlt : g < C.size := Finset.mem_range.mp (hsub hgR)
          exact hback _ hjlt x hin
        have hle := reaches_le hnext hback hsub
        have hd' : r - (N + g) < d := by omega
        have hgmem : g ∈ (treeOfRegion N C region E r).gates :=
          ih _ hd' (N + g) g rfl hnext rfl hgR
        have ⟨_, hgsub⟩ := treeOfRegion_subtree_mono (S := S) (E := E)
          (region := region) (root := root) (r := r)
          hback hsub hS hroot hlr0 hEcond hshape hwires hrw hgmem
        have hqW : N + q ∈ S ∪ region.image (fun k => N + k) :=
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨q, hqR, rfl⟩)
        have hq_notE : N + q ∉ E := by
          intro hEb
          exact (hEcond (N + q) hEb).1 hqW
        have hq_notN : ¬(N + q < N) := by omega
        have hlen := (hshape g hgR).2.1
        have hinpEq : (gateAt C g).inputs =
            [(gateAt C g).inputs.getD 0 0, (gateAt C g).inputs.getD 1 0] :=
          len2_inputs _ hlen
        have hplt' : N + q < N + g := by simpa [hx] using hlt
        have hchild :
            treeChild N C region E (N + g) (N + q) =
              treeOfRegion N C region E (N + q) := by
          rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
            (r := N + g) (u := N + q) hplt' with hM | hP | hR'
          · exact (hq_notE hM.1).elim
          · exact (hq_notN hP.2.1).elim
          · exact hR'.2.2
        have hq_in_self : q ∈ (treeOfRegion N C region E (N + q)).gates := by
          have hregQ : N ≤ N + q ∧ (N + q) - N ∈ region :=
            ⟨Nat.le_add_right _ _, by simpa using hqR⟩
          have heqQ := treeOfRegion_eq_node N C region E hregQ
          rw [heqQ]
          simp [BTree.gates]
        have hgdef : (N + g) - N = g := Nat.add_sub_cancel_left N g
        have hin' : x ∈ (gateAt C g).inputs := hin
        have huor : x = (gateAt C g).inputs.getD 0 0 ∨
            x = (gateAt C g).inputs.getD 1 0 := by
          rw [hinpEq] at hin'; simp at hin'; exact hin'
        have hq_in_g : q ∈ (treeOfRegion N C region E (N + g)).gates := by
          have hregG : N ≤ N + g ∧ (N + g) - N ∈ region :=
            ⟨Nat.le_add_right _ _, by simpa using hgR⟩
          have heqG := treeOfRegion_eq_node N C region E hregG
          rw [heqG, hgdef]
          simp only [BTree.gates, Finset.mem_insert, Finset.mem_union]
          have hchild' :
              treeChild N C region E (N + g) x =
                treeOfRegion N C region E (N + q) := by
            simpa [hx] using hchild
          rcases huor with hu | hu
          · have heqc : treeChild N C region E (N + g)
                ((gateAt C g).inputs.getD 0 0) =
              treeOfRegion N C region E (N + q) := by
              simpa [hu] using hchild'
            exact Or.inr (Or.inl (heqc ▸ hq_in_self))
          · have heqc : treeChild N C region E (N + g)
                ((gateAt C g).inputs.getD 1 0) =
              treeOfRegion N C region E (N + q) := by
              simpa [hu] using hchild'
            exact Or.inr (Or.inr (heqc ▸ hq_in_self))
        exact hgsub hq_in_g
  have hle0 := reaches_le hR hback hsub
  exact aux (r - (N + p)) (N + p) p (by omega) hR rfl hpR

lemma reaches_source_mem_privs {N : ℕ} {C : Circuit} {S E region : Finset ℕ}
    {root r w : ℕ}
    (hback : ReadsBack N C) (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hEcond : ∀ b ∈ E, b ∉ S ∪ region.image (fun k => N + k) ∧ b < root ∧
      readsIn C region b = 1)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)
    (hrw : r ∈ S ∪ region.image (fun k => N + k))
    (hwS : w ∈ S) (hR : Reaches N C region w r) :
    w ∈ (treeOfRegion N C region E r).privs := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    by_cases heq : w = r
    · have hwN : w < N := Finset.mem_range.mp (hS hwS)
      have hrN : r < N := by simpa [heq] using hwN
      have hreg : ¬(N ≤ r ∧ r - N ∈ region) := by
        intro h; omega
      rw [heq, treeOfRegion_eq_priv hreg hrN]
      simp [BTree.privs]
    · have ⟨hread, hnext⟩ := reaches_pred hR heq
      set g := regParent C region w
      have ⟨hgR, hin, _, _⟩ := regParent_spec hread
      have hjlt : g < C.size := Finset.mem_range.mp (hsub hgR)
      have hlt : w < N + g := hback _ hjlt w hin
      have hgW : N + g ∈ S ∪ region.image (fun k => N + k) :=
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨g, hgR, rfl⟩)
      have hwW : w ∈ S ∪ region.image (fun k => N + k) :=
        Finset.mem_union_left _ hwS
      have hg_in : g ∈ (treeOfRegion N C region E r).gates :=
        reaches_gate_mem (S := S) (E := E) (region := region) (root := root)
          (r := r) (p := g)
          hback hsub hS hroot hlr0 hEcond hshape hwires hrw hgR hnext
      have ⟨hpv, _⟩ := treeOfRegion_subtree_mono (S := S) (E := E)
        (region := region) (root := root) (r := r)
        hback hsub hS hroot hlr0 hEcond hshape hwires hrw hg_in
      have hregG : N ≤ N + g ∧ (N + g) - N ∈ region :=
        ⟨Nat.le_add_right _ _, by simpa using hgR⟩
      have heqG := treeOfRegion_eq_node N C region E hregG
      have hnotE : w ∉ E := by
        intro hEb
        exact (hEcond w hEb).1 hwW
      have hchild :
          treeChild N C region E (N + g) w = BTree.priv w := by
        have hwN : w < N := Finset.mem_range.mp (hS hwS)
        rcases treeChild_cases (N := N) (C := C) (region := region) (E := E)
          (r := N + g) (u := w) hlt with hM | hP | hR'
        · exact (hnotE hM.1).elim
        · exact hP.2.2
        · exact (hR'.2.1 hwN).elim
      have hgdef : (N + g) - N = g := Nat.add_sub_cancel_left N g
      have hw_in : w ∈ (treeOfRegion N C region E (N + g)).privs := by
        rw [heqG, hgdef]
        have hinpEq : (gateAt C g).inputs =
            [(gateAt C g).inputs.getD 0 0, (gateAt C g).inputs.getD 1 0] :=
          len2_inputs _ (hshape g hgR).2.1
        have hin' : w ∈ (gateAt C g).inputs := hin
        have huor : w = (gateAt C g).inputs.getD 0 0 ∨
            w = (gateAt C g).inputs.getD 1 0 := by
          rw [hinpEq] at hin'; simp at hin'; exact hin'
        simp only [BTree.privs, Finset.mem_union]
        rcases huor with hu | hu
        · have heqc : treeChild N C region E (N + g)
              ((gateAt C g).inputs.getD 0 0) = BTree.priv w := by
            simpa [hu] using hchild
          rw [heqc]
          simp [BTree.privs]
        · have heqc : treeChild N C region E (N + g)
              ((gateAt C g).inputs.getD 1 0) = BTree.priv w := by
            simpa [hu] using hchild
          rw [heqc]
          simp [BTree.privs]
      exact hpv hw_in

lemma treeOfRegion_privs_eq {N : ℕ} {C : Circuit} {S E region : Finset ℕ}
    {root : ℕ}
    (hback : ReadsBack N C)
    (hE : E.card ≤ 1)
    (hneR : region.Nonempty)
    (hsub : region ⊆ Finset.range C.size)
    (hS : S ⊆ Finset.range N)
    (hroot : root ∈ S ∪ region.image (fun k => N + k))
    (hlr0 : readsIn C region root = 0)
    (hEcond : ∀ b ∈ E, b ∉ S ∪ region.image (fun k => N + k) ∧ b < root ∧
      readsIn C region b = 1)
    (hshape : ∀ j ∈ region,
      isBinOp (gateAt C j).op ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ S ∪ region.image (fun k => N + k) ∨ w ∈ E)
    (hwires : ∀ w ∈ S ∪ region.image (fun k => N + k),
      w ≠ root → readsIn C region w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w) :
    (treeOfRegion N C region E root).privs = S := by
  apply Finset.Subset.antisymm
  · exact (treeOfRegion_good (root := root) (r := root)
      hback hE hneR hsub hS hroot hlr0 hEcond hshape hwires hroot).2.1
  · intro w hwS
    exact reaches_source_mem_privs (S := S) (E := E) (region := region)
      (root := root) (r := root) (w := w)
      hback hsub hS hroot hlr0 hEcond hshape hwires hroot hwS
      (climb_reaches_root (S := S) (E := E) (region := region) (root := root)
        (w := w) hback hsub hS hroot hlr0 hwires
        (Finset.mem_union_left _ hwS)).2

lemma isTree_piece_bank_caps {n m : ℕ} {G : Fin n → Fin m → Bool}
    (outFn : Bool → Bool) (D : BinaryCircuit) (S E : Finset ℕ)
    (hn : 3 ≤ n) (hm : 3 ≤ m)
    (hrich : ∀ (i j k : Fin n), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (G j col != G i col) = x ∧ (G k col != G i col) = y)).card)
    (htrich : ∀ (i j k : Fin m), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun row =>
          (G row j != G row i) = x ∧ (G row k != G row i) = y)).card)
    (hrep : ∀ (u : Fin n) (v : Fin m), outFn (D.eval (oneEach u v)) = G u v)
    (htree : IsTree (n + m) (binarySkeleton D) S E)
    (hE : E.card ≤ 1)
    (hS : S ⊆ Finset.range (n + m))
    (hBack : Back (n + m) D.gates)
    (hReads : ReadsBack (n + m) (binarySkeleton D))
    (hout : (binarySkeleton D).output + 1 = n + m + (binarySkeleton D).size) :
    (rowNames n S).card ≤ 2 ∧ (colNames n m S).card ≤ 2 := by
  classical
  obtain ⟨region, root, hreg, hroot, hlr0, hEcond, hshape, hwires⟩ := htree
  by_cases hneR : region.Nonempty
  · let t := treeOfRegion (n + m) (binarySkeleton D) region E root
    have hgood := treeOfRegion_good (N := n + m) (C := binarySkeleton D)
      (S := S) (E := E) (region := region) (root := root) (r := root)
      hReads hE hneR hreg hS hroot hlr0 hEcond hshape hwires hroot
    have hpriv : t.privs = S :=
      treeOfRegion_privs_eq (N := n + m) (C := binarySkeleton D)
        (S := S) (E := E) (region := region) (root := root)
        hReads hE hneR hreg hS hroot hlr0 hEcond hshape hwires
    have hcap := tree_bank_caps_rect (N := n + m) (n := n)
      hReads hout t hgood.1 hgood.2.2.1 (by simpa [hpriv] using hS) ?_
    · simpa [hpriv, rowNames_filter_card hS, colNames_filter_card hS] using hcap
    · intro S' E' hsub hSne hEcard htree' hrow4 hcol4
      have hSrange : S' ⊆ Finset.range (n + m) :=
        hsub.trans (by simpa [hpriv] using hS)
      have ⟨hR, hC⟩ := isTree_bank_le_two (outFn := outFn) (D := D)
        (S := S') (E := E') hn hm hrich htrich hrep htree' hEcard hSrange
        hBack hReads hout
        (by rwa [rowNames_filter_card hSrange])
        (by rwa [colNames_filter_card hSrange])
      exact ⟨by rwa [← rowNames_filter_card hSrange],
        by rwa [← colNames_filter_card hSrange]⟩
  · have hreg0 : region = ∅ := Finset.not_nonempty_iff_eq_empty.mp hneR
    have hsubS : S ⊆ {root} := isTree_of_empty_region hreg0 hroot
      (fun w hw hne => (hwires w hw hne).1)
    have hcard : S.card ≤ 1 :=
      (Finset.card_le_card hsubS).trans_eq (by simp)
    have hsplit := rowNames_colNames_card (n := n) (m := m) hS
    constructor <;> omega


lemma isTree_of_andOr_tree {N : ℕ} {C : Circuit} {S E : Finset ℕ}
    (ht : ∃ (region : Finset ℕ) (root : ℕ),
      let wires := S ∪ region.image (fun k => N + k)
      let localReads := readsIn C region
      region ⊆ Finset.range C.size ∧ root ∈ wires ∧ localReads root = 0 ∧
      (∀ b ∈ E, b ∉ wires ∧ b < root ∧ localReads b = 1) ∧
      (∀ j ∈ region,
        ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
        (gateAt C j).inputs.length = 2 ∧
          ∀ w ∈ (gateAt C j).inputs, w ∈ wires ∨ w ∈ E) ∧
      (∀ w ∈ wires, w ≠ root → localReads w = 1 ∧
        readsIn C (Finset.range C.size) w = 1 ∧ C.output ≠ w)) :
    IsTree N C S E := by
  obtain ⟨region, root, hreg, hroot, hlr0, hEcond, hshape, hwires⟩ := ht
  refine ⟨region, root, hreg, hroot, hlr0, hEcond, ?_, hwires⟩
  intro j hj
  obtain ⟨hop, hlen, hin⟩ := hshape j hj
  exact ⟨trivial, hlen, hin⟩

end PEqualNP.Outside.L_meta_25874_aux



open PEqualNP.Outside.L_meta_25874_aux
open PEqualNP.Represents
open PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_25806_aux
open PEqualNP.Outside.L_meta_25806_aux.Normalize

theorem PEqualNP.Outside.L_meta_25874 : (∀ (n m hr hc : ℕ) (G : Fin n → Fin m → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
  let rich := fun (v w : ℕ) (T : Fin v → Fin w → Bool) =>
    ∀ (i j k : Fin v), i ≠ j → i ≠ k → j ≠ k →
      ∀ (x y : Bool), (x = true ∨ y = true) →
        5 ≤ (Finset.univ.filter (fun col =>
          (T j col != T i col) = x ∧ (T k col != T i col) = y)).card
  let bounded := fun (v w : ℕ) (T : Fin v → Fin w → Bool) (h : ℕ) =>
    ∀ (off : Fin w → Bool) (F : Finset (Fin v × Fin v)),
      (∀ e ∈ F, e.1 ≠ e.2 ∧ ∃ side : Bool,
        (Finset.univ.filter (fun col =>
          (T e.1 col != T e.2 col) = side ∧ T e.1 col ≠ off col)).card ≤ 2) →
      (∀ e ∈ F, ∀ f ∈ F, e ≠ f →
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2) → F.card ≤ h
  let tr := fun (j : Fin m) (i : Fin n) => G i j
  3 ≤ n → 3 ≤ m → 2*hr+2 ≤ n → 2*hc+2 ≤ m →
  rich n m G → rich m n tr → bounded n m G hr → bounded m n tr hc →
  (∀ g ∈ C.gates, g.inputs.length ≤ 2) → PEqualNP.Represents.Represents G C →
    11*(n+m) ≤ 10*(C.gates.countP (fun g => g.inputs.length == 2)) + 26 + 2*(hr+hc))  := by
  intro n m hr hc G C rich bounded tr hn hm hhr hhc hrich htrich hbd htbd hfan hrep
  have hN : 0 < n + m := by omega
  obtain ⟨B, outFn, hBsz, hBack, hBout, hLive, _hReach, hBeval⟩ :=
    PEqualNP.Outside.L_meta_25806_aux.Normalize.normalize_live (n + m) hN C hfan
  have hrepB : ∀ (u : Fin n) (v : Fin m), outFn (B.eval (oneEach u v)) = G u v := by
    intro u v
    have hx : (oneEach u v).length = n + m := length_oneEach u v
    exact (hBeval (oneEach u v) hx).symm.trans (hrep u v)
  have houtFn_inj : Function.Injective outFn := by
    intro a b hab
    by_contra hne
    have hconst : ∀ x : Bool, outFn x = outFn a := by
      intro x
      cases a <;> cases b
      · exact (hne rfl).elim
      · cases x with
        | false => rfl
        | true => exact hab.symm
      · cases x with
        | false => exact hab.symm
        | true => rfl
      · exact (hne rfl).elim
    exact rich_not_row_function (G := G) hn hm hrich
      (fun _ => outFn a) (fun u v => by rw [← hrepB, hconst])
  by_cases hsz0 : B.gates.length = 0
  · have hnil : B.gates = [] := List.length_eq_zero_iff.mp hsz0
    have houtlt : B.output < n + m := by
      have : B.output < n + m + B.gates.length := hBout
      omega
    have hBe : ∀ (u : Fin n) (v : Fin m),
        B.eval (oneEach u v) = (oneEach u v).getD B.output false := by
      intro u v
      exact eval_empty B hnil _
    by_cases hrow : B.output < n
    · refine (rich_not_row_function (G := G) hn hm hrich
        (fun u => outFn (decide (u.val = B.output))) ?_).elim
      intro u v
      rw [← hrepB, hBe, getD_oneEach_left u v B.output hrow]
      simp [eq_comm]
    · have hge : n ≤ B.output := by omega
      refine (rich_not_row_function (n := m) (m := n) (G := tr) hm hn htrich
        (fun v => outFn (decide (v.val = B.output - n))) ?_).elim
      intro v u
      change G u v = outFn (decide (v.val = B.output - n))
      rw [← hrepB, hBe, getD_oneEach_right u v B.output hge houtlt]
      simp [eq_comm]
  · have hpos : 0 < B.gates.length := Nat.pos_of_ne_zero hsz0
    obtain ⟨hshape, hSback, hSpos, hSout, hSused⟩ :=
      skeleton_hyps (n + m) B hBack hLive hpos
    obtain ⟨pure, chains, e, hlen1, hlen2, hepos, hdisj, hcov, hpure, hchains⟩ :=
      PEqualNP.Outside.L_meta_25644 (n + m) (binarySkeleton B)
        hshape hSback hSpos hSout hSused
    have hBpos : 0 < B.size := by
      simpa [BinaryCircuit.size] using hpos
    have houtB : B.output + 1 = n + m + B.size := by
      simpa [binarySkeleton_size, show (binarySkeleton B).output = B.output from rfl]
        using hSout
    have husedOf : ∀ j < B.size, j + 1 < B.size →
        0 < readsOf (binarySkeleton B) (n + m + j) := by
      intro j hj hj'
      have hsz : (binarySkeleton B).size = B.size := binarySkeleton_size B
      simpa [readsOf, hsz] using hSused j (by simpa [hsz] using hj) (by simpa [hsz] using hj')
    obtain ⟨Rtrees, trees, hRcard, hgood, htdisj, htcov, hmarksum⟩ :=
      binarySkeleton_forest (n + m) B hSback hBpos houtB husedOf
    obtain ⟨L, hLlen, hLgood, hLdisj, hLcov⟩ :=
      concrete_forest_bad_partition hSback hSout (∅ : Finset ℕ) Rtrees trees
        hgood htdisj
    have honce :
        ((@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs) =
          (Rtrees.biUnion fun r => (trees r).privs) := by
      simpa using hLcov
    have hpriv_range : ∀ p ∈ L, p.privs ⊆ Finset.range (n + m) := by
      intro p hp w hw
      have hw' : w ∈ (@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs :=
        Finset.mem_biUnion.mpr ⟨p, (@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, hw⟩
      rw [honce, htcov] at hw'
      exact (Finset.mem_filter.mp hw').1
    have hbank : ∀ p ∈ L,
        (p.privs.filter (fun w => w < n)).card ≤ 2 ∧
        (p.privs.filter (fun w => n ≤ w)).card ≤ 2 := by
      intro p hp
      obtain ⟨hgp, hmp, hnep⟩ := hLgood p hp
      refine tree_bank_caps_rect (N := n + m) (n := n) hSback hSout p hgp hmp
        (hpriv_range p hp) ?_
      intro S E hsub hSne hEcard htree hrow4 hcol4
      have hSrange : S ⊆ Finset.range (n + m) := hsub.trans (hpriv_range p hp)
      have ⟨hR, hC⟩ := isTree_bank_le_two (outFn := outFn) (D := B) (S := S) (E := E)
        hn hm hrich htrich hrepB htree hEcard hSrange hBack hSback hSout
        (by rwa [rowNames_filter_card hSrange])
        (by rwa [colNames_filter_card hSrange])
      exact ⟨by rwa [← rowNames_filter_card hSrange],
        by rwa [← colNames_filter_card hSrange]⟩
    classical
    let reads := readsOf (binarySkeleton B)
    let once : Finset ℕ := (Finset.range (n + m)).filter (fun w => reads w = 1)
    have honce' :
        ((@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs) = once := by
      rw [honce, htcov]
    let Hr : Fin m → Bool := fun j => outFn (B.eval (rowOff (n := n) j))
    let Hc : Fin n → Bool := fun i => outFn (B.eval (colOff (m := m) i))
    have hrow_pair : ∀ p ∈ L, (rowNames n p.privs).card = 2 →
        ∃ e : Fin n × Fin n,
          e.1 ≠ e.2 ∧ e.1.val ∈ p.privs ∧ e.2.val ∈ p.privs ∧
          ∃ side : Bool,
            (Finset.univ.filter (fun col =>
              (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
      intro p hp h2r
      obtain ⟨hgp, hmp, hnep⟩ := hLgood p hp
      obtain ⟨E, hEcard, htree⟩ := one_mark_good_isTree hSback hSout hgp hmp hnep
      have h2 : 2 ≤ (rowNames n p.privs).card ∨ 2 ≤ (colNames n m p.privs).card :=
        Or.inl (by omega)
      obtain ⟨⟨t, q0, q, U, h0, hfac⟩, _⟩ :=
        isTree_factors (G := G) outFn B p.privs E hrepB htree hEcard
          (hpriv_range p hp) hBack hSback hSout h2
      have hT : (colNames n m p.privs).card ≤ 2 := by
        have hSrange := hpriv_range p hp
        simpa [colNames_filter_card hSrange] using (hbank p hp).2
      obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2r
      have ha : a ∈ rowNames n p.privs := by simp [hs]
      have hb : b ∈ rowNames n p.privs := by simp [hs]
      obtain ⟨e, hne, he1, he2, hside⟩ :=
        affordable_of_row_factor (G := G) (rowNames n p.privs)
          (colNames n m p.privs) Hr hT t q0 q U h0 hfac ha hb hab
      have hmem (x : Fin n) (hx : x = a ∨ x = b) : x.val ∈ p.privs := by
        have : x ∈ rowNames n p.privs := by
          rcases hx with hx | hx <;> simp [hs, hx]
        exact (Finset.mem_filter.mp this).2
      exact ⟨e, hne, hmem e.1 he1, hmem e.2 he2, hside⟩
    have hcol_pair : ∀ p ∈ L, (colNames n m p.privs).card = 2 →
        ∃ e : Fin m × Fin m,
          e.1 ≠ e.2 ∧ n + e.1.val ∈ p.privs ∧ n + e.2.val ∈ p.privs ∧
          ∃ side : Bool,
            (Finset.univ.filter (fun row =>
              (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
      intro p hp h2c
      obtain ⟨hgp, hmp, hnep⟩ := hLgood p hp
      obtain ⟨E, hEcard, htree⟩ := one_mark_good_isTree hSback hSout hgp hmp hnep
      have h2 : 2 ≤ (rowNames n p.privs).card ∨ 2 ≤ (colNames n m p.privs).card :=
        Or.inr (by omega)
      obtain ⟨_, ⟨t, q0, q, U, h0, hfac⟩⟩ :=
        isTree_factors (G := G) outFn B p.privs E hrepB htree hEcard
          (hpriv_range p hp) hBack hSback hSout h2
      have hRc : (rowNames n p.privs).card ≤ 2 := by
        have hSrange := hpriv_range p hp
        simpa [rowNames_filter_card hSrange] using (hbank p hp).1
      obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2c
      have ha : a ∈ colNames n m p.privs := by simp [hs]
      have hb : b ∈ colNames n m p.privs := by simp [hs]
      obtain ⟨e, hne, he1, he2, hside⟩ :=
        affordable_of_col_factor (G := G) (colNames n m p.privs)
          (rowNames n p.privs) Hc hRc t q0 q U h0 hfac ha hb hab
      have hmem (x : Fin m) (hx : x = a ∨ x = b) : n + x.val ∈ p.privs := by
        have : x ∈ colNames n m p.privs := by
          rcases hx with hx | hx <;> simp [hs, hx]
        exact (Finset.mem_filter.mp this).2
      exact ⟨e, hne, hmem e.1 he1, hmem e.2 he2, hside⟩
    let Lfin := @List.toFinset BTree (Classical.decEq _) L
    let rowPieces := Lfin.filter (fun p => (rowNames n p.privs).card = 2)
    let colPieces := Lfin.filter (fun p => (colNames n m p.privs).card = 2)
    have hexR : ∀ p ∈ rowPieces, ∃ e : Fin n × Fin n,
        e.1 ≠ e.2 ∧ e.1.val ∈ p.privs ∧ e.2.val ∈ p.privs ∧
        ∃ side : Bool,
          (Finset.univ.filter (fun col =>
            (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
      intro p hp
      have ⟨hpL, h2r⟩ := Finset.mem_filter.mp hp
      exact hrow_pair p ((@List.mem_toFinset BTree (Classical.decEq _) L).mp hpL) h2r
    choose fR hfR using hexR
    have hexC : ∀ p ∈ colPieces, ∃ e : Fin m × Fin m,
        e.1 ≠ e.2 ∧ n + e.1.val ∈ p.privs ∧ n + e.2.val ∈ p.privs ∧
        ∃ side : Bool,
          (Finset.univ.filter (fun row =>
            (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
      intro p hp
      have ⟨hpL, h2c⟩ := Finset.mem_filter.mp hp
      exact hcol_pair p ((@List.mem_toFinset BTree (Classical.decEq _) L).mp hpL) h2c
    choose fC hfC using hexC
    let Frow := rowPieces.attach.image (fun p => fR p.1 p.2)
    let Fcol := colPieces.attach.image (fun p => fC p.1 p.2)
    have hFrow_aff : ∀ e ∈ Frow, e.1 ≠ e.2 ∧ ∃ side : Bool,
        (Finset.univ.filter (fun col =>
          (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      exact ⟨(hfR p.1 p.2).1, (hfR p.1 p.2).2.2.2⟩
    have hFcol_aff : ∀ e ∈ Fcol, e.1 ≠ e.2 ∧ ∃ side : Bool,
        (Finset.univ.filter (fun row =>
          (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
      intro e he
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      exact ⟨(hfC p.1 p.2).1, (hfC p.1 p.2).2.2.2⟩
    have hdisj_of_mem {p q : BTree} (hp : p ∈ L) (hq : q ∈ L) (hne : p ≠ q) :
        Disjoint p.privs q.privs := by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hq
      have hij : i ≠ j := fun h => hne (by subst h; rfl)
      have hpw := List.pairwise_iff_get.mp hLdisj
      let i' : Fin L.length := ⟨i, hi⟩
      let j' : Fin L.length := ⟨j, hj⟩
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · exact hpw i' j' hlt
      · exact (hpw j' i' hgt).symm
    have hFrow_disj : ∀ e ∈ Frow, ∀ f ∈ Frow, e ≠ f →
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
      intro e he f hf hne
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
      have hpq : p.1 ≠ q.1 := fun h => hne (by cases p; cases q; subst h; rfl)
      have hpL := ((@List.mem_toFinset BTree (Classical.decEq _) L).mp
        (Finset.mem_filter.mp p.2).1)
      have hqL := ((@List.mem_toFinset BTree (Classical.decEq _) L).mp
        (Finset.mem_filter.mp q.2).1)
      have hdis := hdisj_of_mem hpL hqL hpq
      have dp := hfR p.1 p.2
      have dq := hfR q.1 q.2
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.1 (h ▸ dq.2.1)
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.1 (h ▸ dq.2.2.1)
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.2.1 (h ▸ dq.2.1)
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.2.1 (h ▸ dq.2.2.1)
    have hFcol_disj : ∀ e ∈ Fcol, ∀ f ∈ Fcol, e ≠ f →
        e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
      intro e he f hf hne
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hf
      have hpq : p.1 ≠ q.1 := fun h => hne (by cases p; cases q; subst h; rfl)
      have hpL := ((@List.mem_toFinset BTree (Classical.decEq _) L).mp
        (Finset.mem_filter.mp p.2).1)
      have hqL := ((@List.mem_toFinset BTree (Classical.decEq _) L).mp
        (Finset.mem_filter.mp q.2).1)
      have hdis := hdisj_of_mem hpL hqL hpq
      have dp := hfC p.1 p.2
      have dq := hfC q.1 q.2
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.1 (by rw [h]; exact dq.2.1)
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.1 (by rw [h]; exact dq.2.2.1)
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.2.1 (by rw [h]; exact dq.2.1)
      · intro h; exact Finset.disjoint_left.mp hdis dp.2.2.1 (by rw [h]; exact dq.2.2.1)
    have hFrow_le : Frow.card ≤ hr := hbd Hr Frow hFrow_aff hFrow_disj
    have hFcol_le : Fcol.card ≤ hc := htbd Hc Fcol hFcol_aff hFcol_disj
    let H : Finset ℕ :=
      Frow.image (fun e => e.1.val) ∪ Fcol.image (fun e => n + e.1.val)
    have hHle : H.card ≤ hr + hc :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add
        (Finset.card_image_le.trans hFrow_le) (Finset.card_image_le.trans hFcol_le))
    have hsmallP : ∀ p ∈ L, p.privs.card ≤ 2 + 2 * (p.privs ∩ H).card := by
      intro p hp
      have hSrange := hpriv_range p hp
      have hsum := rowNames_colNames_card (n := n) (m := m) hSrange
      have hr2 : (rowNames n p.privs).card ≤ 2 := by
        simpa [rowNames_filter_card hSrange] using (hbank p hp).1
      have hc2 : (colNames n m p.privs).card ≤ 2 := by
        simpa [colNames_filter_card hSrange] using (hbank p hp).2
      have hmr (h2r : (rowNames n p.privs).card = 2) :
          (fR p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2r⟩)).1.val
            ∈ p.privs ∩ H := by
        have hpR : p ∈ rowPieces :=
          Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2r⟩
        let a : { x // x ∈ rowPieces } := ⟨p, hpR⟩
        have hin : a ∈ rowPieces.attach := Finset.mem_attach _ _
        have heF : fR p hpR ∈ Frow := Finset.mem_image.mpr ⟨a, hin, rfl⟩
        exact Finset.mem_inter.mpr ⟨(hfR p hpR).2.1,
          Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fR p hpR, heF, rfl⟩)⟩
      have hmc (h2c : (colNames n m p.privs).card = 2) :
          n + (fC p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2c⟩)).1.val
            ∈ p.privs ∩ H := by
        have hpC : p ∈ colPieces :=
          Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2c⟩
        let b : { x // x ∈ colPieces } := ⟨p, hpC⟩
        have hin : b ∈ colPieces.attach := Finset.mem_attach _ _
        have heF : fC p hpC ∈ Fcol := Finset.mem_image.mpr ⟨b, hin, rfl⟩
        exact Finset.mem_inter.mpr ⟨(hfC p hpC).2.1,
          Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fC p hpC, heF, rfl⟩)⟩
      -- marks are distinct (row wire < n ≤ col wire)
      have : p.privs.card ≤ 2 + 2 * (p.privs ∩ H).card := by
        have hRcard := hr2
        have hCcard := hc2
        by_cases h2r : (rowNames n p.privs).card = 2
        · by_cases h2c : (colNames n m p.privs).card = 2
          · have h1 := hmr h2r
            have h2 := hmc h2c
            have hne : (fR p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2r⟩)).1.val ≠ n + (fC p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2c⟩)).1.val := by
              have : (fR p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2r⟩)).1.val < n :=
                (fR p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2r⟩)).1.isLt
              omega
            have htwo : 2 ≤ (p.privs ∩ H).card := by
              have hsub : ({(fR p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2r⟩)).1.val, n + (fC p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2c⟩)).1.val} : Finset ℕ) ⊆ p.privs ∩ H := by
                intro w hw
                simp only [Finset.mem_insert, Finset.mem_singleton] at hw
                rcases hw with rfl | rfl
                · exact h1
                · exact h2
              have hcard2 : ({(fR p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2r⟩)).1.val, n + (fC p (Finset.mem_filter.mpr ⟨(@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, h2c⟩)).1.val} : Finset ℕ).card = 2 :=
                Finset.card_pair hne
              exact (by omega : 2 ≤ _).trans (Finset.card_le_card hsub)
            omega
          · have h1 := hmr h2r
            have hone : 1 ≤ (p.privs ∩ H).card := Finset.card_pos.mpr ⟨_, h1⟩
            omega
        · by_cases h2c : (colNames n m p.privs).card = 2
          · have h2 := hmc h2c
            have hone : 1 ≤ (p.privs ∩ H).card := Finset.card_pos.mpr ⟨_, h2⟩
            omega
          · omega
      exact this
    have hsmallL : ∀ S ∈ L.map BTree.privs, S.card ≤ 2 + 2 * (S ∩ H).card := by
      intro S hS
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hS
      exact hsmallP p hp
    have hdisjL : (L.map BTree.privs).Pairwise Disjoint := by
      refine List.pairwise_iff_get.mpr ?_
      intro i j hij
      have hiL : i.val < L.length := by simpa [List.length_map] using i.isLt
      have hjL : j.val < L.length := by simpa [List.length_map] using j.isLt
      have := (List.pairwise_iff_get.mp hLdisj) ⟨i.val, hiL⟩ ⟨j.val, hjL⟩ hij
      simpa [List.getElem_map] using this
    have hunion := marked_union (L.map BTree.privs) H hdisjL hsmallL
    have hmaplen : (L.map BTree.privs).length = L.length := List.length_map _
    have hmapcov :
        ((L.map BTree.privs).toFinset.biUnion id) = once := by
      apply Eq.trans ?_ honce'
      ext w
      constructor
      · intro hw
        obtain ⟨S, hS, hwS⟩ := Finset.mem_biUnion.mp hw
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hS)
        exact Finset.mem_biUnion.mpr
          ⟨p, (@List.mem_toFinset BTree (Classical.decEq _) L).mpr hp, hwS⟩
      · intro hw
        obtain ⟨p, hp, hwS⟩ := Finset.mem_biUnion.mp hw
        have hpL : p ∈ L := (@List.mem_toFinset BTree (Classical.decEq _) L).mp hp
        exact Finset.mem_biUnion.mpr
          ⟨p.privs, List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hpL, rfl⟩), hwS⟩
    have honce_le : once.card ≤ 2 * L.length + 2 * (once ∩ H).card := by
      have h := hunion
      rw [hmapcov, hmaplen] at h
      exact h
    -- Handshake and unused.
    have hbudget := used_surplus_eq_size_succ (N := n + m) B hBpos hBack hLive
    let usedN := ((Finset.range (n + m)).filter (fun w => 1 ≤ reads w)).card
    let surplusN := ∑ w ∈ Finset.range (n + m + B.size), (reads w - 1)
    have hbudget' : usedN + surplusN = B.size + 1 := by
      simpa [usedN, surplusN, reads] using hbudget
    have hsplit : usedN = once.card +
        ((Finset.range (n + m)).filter (fun w => 2 ≤ reads w)).card := by
      simp only [usedN, once, Finset.card_filter]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (if 1 ≤ reads i then 1 else 0) =
        (if reads i = 1 then 1 else 0) + (if 2 ≤ reads i then 1 else 0)
      split_ifs <;> omega

    have hunrow := unread_rows_le_one (G := G) outFn B hn hm hrich hrepB hBpos houtB
    have huncol := unread_cols_le_one (G := G) outFn B hn hm htrich hrepB hBpos houtB
    let unusedN := ((Finset.range (n + m)).filter (fun w => reads w = 0)).card
    have hrows0 : ((Finset.range n).filter (fun w => reads w = 0)).card ≤ 1 := by
      have hbij : ((Finset.range n).filter (fun w => reads w = 0)).card =
          ((Finset.univ : Finset (Fin n)).filter
            (fun i => reads i.val = 0)).card := by
        refine Finset.card_bij
          (fun w hw => ⟨w, Finset.mem_range.mp (Finset.mem_filter.mp hw).1⟩)
          (fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hw).2⟩)
          (fun a ha b hb h => by cases h; rfl)
          (fun i hi => ⟨i.val, Finset.mem_filter.mpr
            ⟨Finset.mem_range.mpr i.isLt, (Finset.mem_filter.mp hi).2⟩, rfl⟩)
      simpa [reads] using (hbij.trans_le hunrow)
    have hcols0 : ((Finset.range (n + m) \ Finset.range n).filter
        (fun w => reads w = 0)).card ≤ 1 := by
      have hbij : ((Finset.range (n + m) \ Finset.range n).filter
          (fun w => reads w = 0)).card =
          ((Finset.univ : Finset (Fin m)).filter
            (fun j => reads (n + j.val) = 0)).card := by
        refine Finset.card_bij (fun w hw => ⟨w - n, ?_⟩) ?_ ?_ ?_
        · have hw' := Finset.mem_filter.mp hw
          have : w ∈ Finset.range (n + m) \ Finset.range n := hw'.1
          have ⟨hwR, hwn⟩ := Finset.mem_sdiff.mp this
          have : n ≤ w := Nat.le_of_not_gt (fun h => hwn (Finset.mem_range.mpr h))
          have : w < n + m := Finset.mem_range.mp hwR
          omega
        · intro w hw
          have hw' := Finset.mem_filter.mp hw
          have ⟨hwR, hwn⟩ := Finset.mem_sdiff.mp hw'.1
          have hge : n ≤ w := Nat.le_of_not_gt (fun h => hwn (Finset.mem_range.mpr h))
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          simpa [Nat.add_sub_of_le hge] using hw'.2
        · intro a ha b hb h
          have ha' := (Finset.mem_filter.mp ha).1
          have hb' := (Finset.mem_filter.mp hb).1
          have hage := Nat.le_of_not_gt (fun h => (Finset.mem_sdiff.mp ha').2 (Finset.mem_range.mpr h))
          have hbge := Nat.le_of_not_gt (fun h => (Finset.mem_sdiff.mp hb').2 (Finset.mem_range.mpr h))
          have : a - n = b - n := Fin.val_eq_of_eq h
          omega
        · intro j hj
          refine ⟨n + j.val, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
            ⟨Finset.mem_range.mpr (by omega), fun h => ?_⟩,
            by simpa using (Finset.mem_filter.mp hj).2⟩, ?_⟩
          · have : n + j.val < n := Finset.mem_range.mp h
            omega
          · ext; simp
      simpa [reads] using (hbij.trans_le huncol)
    have hunused_le : unusedN ≤ 2 := by
      have hsplit : unusedN =
          ((Finset.range (n + m)).filter (fun w => w < n ∧ reads w = 0)).card +
          ((Finset.range (n + m)).filter (fun w => n ≤ w ∧ reads w = 0)).card := by
        unfold unusedN
        simp only [Finset.card_filter]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hwn : w < n <;> by_cases hr : reads w = 0 <;> simp [hwn, hr]
      have hrowf : ((Finset.range (n + m)).filter (fun w => w < n ∧ reads w = 0)).card
          ≤ ((Finset.range n).filter (fun w => reads w = 0)).card := by
        apply Finset.card_le_card
        intro w hw
        have ⟨hwR, ⟨hwn, hr⟩⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, hr⟩
      have hcolf : ((Finset.range (n + m)).filter (fun w => n ≤ w ∧ reads w = 0)).card
          ≤ ((Finset.range (n + m) \ Finset.range n).filter (fun w => reads w = 0)).card := by
        apply Finset.card_le_card
        intro w hw
        have ⟨hwR, ⟨hge, hr⟩⟩ := Finset.mem_filter.mp hw
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwR, fun h =>
          Nat.lt_irrefl _ ((Finset.mem_range.mp h).trans_le hge)⟩, hr⟩
      omega
    have hwu : usedN + unusedN = n + m := by
      change ((Finset.range (n + m)).filter (fun w => 1 ≤ reads w)).card
          + ((Finset.range (n + m)).filter (fun w => reads w = 0)).card = n + m
      have hdis0 : Disjoint
          ((Finset.range (n + m)).filter (fun w => 1 ≤ reads w))
          ((Finset.range (n + m)).filter (fun w => reads w = 0)) :=
        Finset.disjoint_left.mpr fun x hx hy => by
          have := (Finset.mem_filter.mp hx).2
          have := (Finset.mem_filter.mp hy).2
          omega
      have hunion0 :
          ((Finset.range (n + m)).filter (fun w => 1 ≤ reads w))
            ∪ ((Finset.range (n + m)).filter (fun w => reads w = 0))
            = Finset.range (n + m) := by
        ext w
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · intro h; rcases h with h | h <;> exact h.1
        · intro hw
          by_cases h0 : reads w = 0
          · exact Or.inr ⟨hw, h0⟩
          · exact Or.inl ⟨hw, Nat.pos_of_ne_zero h0⟩
      rw [← Finset.card_union_of_disjoint hdis0, hunion0, Finset.card_range]
    let u := ((Finset.range (n + m)).filter (fun w => 2 ≤ reads w)).card
    let P := ((Finset.range B.size).filter (fun j => 2 ≤ reads (n + m + j))).card
    have huP : u + P ≤ surplusN := by
      simpa [u, P, surplusN, reads] using shared_le_surplus (N := n + m) B
    let sharedAll := (Finset.range (n + m + B.size)).filter (fun w => 2 ≤ reads w)
    let hitUses := ∑ w ∈ sharedAll, reads w
    have hhit : hitUses = (∑ w ∈ sharedAll, (reads w - 1)) + sharedAll.card := by
      simpa [hitUses, sharedAll, reads] using hitUses_decomp (N := n + m) B
    have hhit_le : hitUses ≤ surplusN + u + P := by
      have hsub : (∑ w ∈ sharedAll, (reads w - 1)) ≤ surplusN :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (s := sharedAll) (t := Finset.range (n + m + B.size))
          (fun w hw => (Finset.mem_filter.mp hw).1) (fun _ _ _ => Nat.zero_le _)
      have hsc : sharedAll.card ≤ u + P := by
        -- sharedAll ⊆ raw shared ∪ image of shared gates; actually equality
        have h1 : (sharedAll ∩ Finset.range (n + m)).card ≤ u := by
          have : sharedAll ∩ Finset.range (n + m) ⊆
              (Finset.range (n + m)).filter (fun w => 2 ≤ reads w) := by
            intro w hw
            have ⟨hs, hr⟩ := Finset.mem_inter.mp hw
            exact Finset.mem_filter.mpr ⟨hr, (Finset.mem_filter.mp hs).2⟩
          exact (Finset.card_le_card this).trans_eq rfl
        have h2 : (sharedAll \ Finset.range (n + m)).card ≤ P := by
          refine (Finset.card_le_card_of_injOn (t := (Finset.range B.size).filter
              (fun j => 2 ≤ reads (n + m + j))) (fun w => w - (n + m)) ?_ ?_).trans le_rfl
          · intro w hw
            have ⟨hs, hn⟩ := Finset.mem_sdiff.mp hw
            have hge : n + m ≤ w := Nat.le_of_not_gt (fun h => hn (Finset.mem_range.mpr h))
            have hlt : w < n + m + B.size := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
            have : 2 ≤ reads w := (Finset.mem_filter.mp hs).2
            have : 2 ≤ reads (n + m + (w - (n + m))) := by simpa [Nat.add_sub_of_le hge] using this
            have hwj : w - (n + m) < B.size := Nat.sub_lt_left_of_lt_add hge hlt
            exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwj, this⟩
          · intro a ha b hb h
            have hage := Nat.le_of_not_gt (fun h => (Finset.mem_sdiff.mp ha).2 (Finset.mem_range.mpr h))
            have hbge := Nat.le_of_not_gt (fun h => (Finset.mem_sdiff.mp hb).2 (Finset.mem_range.mpr h))
            have hsub : a - (n + m) = b - (n + m) := h
            have : n + m + (a - (n + m)) = n + m + (b - (n + m)) := by rw [hsub]
            simpa [Nat.add_sub_of_le hage, Nat.add_sub_of_le hbge] using this
        have : sharedAll.card = (sharedAll ∩ Finset.range (n + m)).card +
            (sharedAll \ Finset.range (n + m)).card := by
          have hdisSP : Disjoint (sharedAll ∩ Finset.range (n + m))
              (sharedAll \ Finset.range (n + m)) :=
            Finset.disjoint_left.mpr fun x hx hy =>
              (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).2
          rw [← Finset.card_union_of_disjoint hdisSP, Finset.union_comm, Finset.sdiff_union_inter]
        omega
      omega
    have hLle : L.length ≤ 2 * hitUses + P + 1 := by
      have hbad : (∅ : Finset ℕ).card = 0 := rfl
      have : L.length ≤ 2 * ((∑ r ∈ Rtrees, (trees r).marks) + (∅ : Finset ℕ).card) + Rtrees.card :=
        hLlen
      have : L.length ≤ 2 * (∑ r ∈ Rtrees, (trees r).marks) + Rtrees.card := by
        simpa using this
      have hmR : (∑ r ∈ Rtrees, (trees r).marks) ≤ hitUses := by
        -- hmarksum : sum marks ≤ markedReads, markedReads is hitUses
        simpa [hitUses, sharedAll, reads] using hmarksum
      have hR : Rtrees.card ≤ P + 1 := by
        simpa [P, reads] using hRcard
      omega
    have honceH : (once ∩ H).card ≤ H.card :=
      Finset.card_le_card (by intro x hx; exact (Finset.mem_inter.mp hx).2)
    have honce_bound : once.card ≤ 4 * hitUses + 2 * P + 2 + 2 * H.card := by
      have := honce_le
      omega
    have hused_le : usedN ≤ 10 * surplusN + 2 + 2 * H.card := by
      have : usedN = once.card + u := hsplit
      have : usedN ≤ 4 * hitUses + 2 * P + 2 + 2 * H.card + u := by omega
      have : usedN ≤ 4 * (surplusN + u + P) + 2 * P + 2 + 2 * H.card + u := by omega
      have : usedN ≤ 4 * surplusN + 5 * u + 6 * P + 2 + 2 * H.card := by omega
      have : usedN ≤ 4 * surplusN + 5 * (u + P) + P + 2 + 2 * H.card := by omega
      have : usedN ≤ 9 * surplusN + P + 2 + 2 * H.card := by omega
      omega
    have hclose11 : 11 * (usedN + unusedN) ≤
        10 * B.size + 12 + 2 * H.card + 11 * unusedN := by
      have : usedN + surplusN = B.size + 1 := hbudget'
      have : usedN ≤ 10 * surplusN + 2 + 2 * H.card := hused_le
      omega
    have hgoal_aux : 11 * (n + m) ≤ 10 * B.size + 12 + 2 * H.card + 11 * unusedN := by
      rw [← hwu]
      exact hclose11
    have hs2 : B.size ≤ C.gates.countP (fun g => g.inputs.length == 2) := hBsz
    by_cases hU : unusedN ≤ 1
    · have : 11 * (n + m) ≤ 10 * B.size + 26 + 2 * (hr + hc) := by
        have : 11 * unusedN ≤ 11 := Nat.mul_le_mul_left 11 hU
        have : 2 * H.card ≤ 2 * (hr + hc) := Nat.mul_le_mul_left 2 hHle
        omega
      exact this.trans (Nat.add_le_add_right (Nat.add_le_add_right
        (Nat.mul_le_mul_left 10 hs2) _) _)
    · have hU2 : unusedN = 2 := by omega
      have hsum0 : unusedN ≤
          ((Finset.range n).filter (fun w => reads w = 0)).card +
          ((Finset.range (n + m) \ Finset.range n).filter (fun w => reads w = 0)).card := by
        have hsplit : unusedN =
            ((Finset.range (n + m)).filter (fun w => w < n ∧ reads w = 0)).card +
            ((Finset.range (n + m)).filter (fun w => n ≤ w ∧ reads w = 0)).card := by
          unfold unusedN
          simp only [Finset.card_filter]
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hwn : w < n <;> by_cases hr : reads w = 0 <;> simp [hwn, hr]
        have hrowf : ((Finset.range (n + m)).filter (fun w => w < n ∧ reads w = 0)).card
            ≤ ((Finset.range n).filter (fun w => reads w = 0)).card := by
          apply Finset.card_le_card
          intro w hw
          have ⟨hwR, ⟨hwn, hr⟩⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hwn, hr⟩
        have hcolf : ((Finset.range (n + m)).filter (fun w => n ≤ w ∧ reads w = 0)).card
            ≤ ((Finset.range (n + m) \ Finset.range n).filter (fun w => reads w = 0)).card := by
          apply Finset.card_le_card
          intro w hw
          have ⟨hwR, ⟨hge, hr⟩⟩ := Finset.mem_filter.mp hw
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwR, fun h =>
            Nat.lt_irrefl _ ((Finset.mem_range.mp h).trans_le hge)⟩, hr⟩
        omega
      have hR0 : ((Finset.range n).filter (fun w => reads w = 0)).card = 1 := by
        omega
      have hC0 : ((Finset.range (n + m) \ Finset.range n).filter
          (fun w => reads w = 0)).card = 1 := by
        omega
      have hrowU : ∃ i0 : Fin n, reads i0.val = 0 := by
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < _ by omega : 0 <
          ((Finset.range n).filter (fun w => reads w = 0)).card)
        have ⟨hwR, hr⟩ := Finset.mem_filter.mp hw
        exact ⟨⟨w, Finset.mem_range.mp hwR⟩, hr⟩
      have hcolU : ∃ j0 : Fin m, reads (n + j0.val) = 0 := by
        obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < _ by omega : 0 <
          ((Finset.range (n + m) \ Finset.range n).filter (fun w => reads w = 0)).card)
        have ⟨hws, hr⟩ := Finset.mem_filter.mp hw
        have ⟨hwR, hwn⟩ := Finset.mem_sdiff.mp hws
        have hge : n ≤ w := Nat.le_of_not_gt (fun h => hwn (Finset.mem_range.mpr h))
        have hlt : w < n + m := Finset.mem_range.mp hwR
        refine ⟨⟨w - n, by omega⟩, ?_⟩
        simpa [Nat.add_sub_of_le hge] using hr
      obtain ⟨i0, hi0r⟩ := hrowU
      obtain ⟨j0, hj0r⟩ := hcolU
      let i1 : Fin n := ⟨(i0.val + 1) % n, Nat.mod_lt (i0.val + 1) (by omega)⟩
      have hi01 : i0 ≠ i1 := by
        intro heq
        have hv : i0.val = i1.val := Fin.val_eq_of_eq heq
        change i0.val = (i0.val + 1) % n at hv
        cases Nat.lt_or_ge (i0.val + 1) n with
        | inl hlt =>
          have : (i0.val + 1) % n = i0.val + 1 := Nat.mod_eq_of_lt hlt
          omega
        | inr hge =>
          have : i0.val + 1 = n := by omega
          have : (i0.val + 1) % n = 0 := by rw [this, Nat.mod_self]
          omega
      let j1 : Fin m := ⟨(j0.val + 1) % m, Nat.mod_lt (j0.val + 1) (by omega)⟩
      have hj01 : j0 ≠ j1 := by
        intro heq
        have hv : j0.val = j1.val := Fin.val_eq_of_eq heq
        change j0.val = (j0.val + 1) % m at hv
        cases Nat.lt_or_ge (j0.val + 1) m with
        | inl hlt =>
          have : (j0.val + 1) % m = j0.val + 1 := Nat.mod_eq_of_lt hlt
          omega
        | inr hge =>
          have : j0.val + 1 = m := by omega
          have : (j0.val + 1) % m = 0 := by rw [this, Nat.mod_self]
          omega
      have houti0 : B.output ≠ i0.val :=
        output_ne_raw (N := n + m) B hBpos houtB i0.val (by omega)
      have houtj0 : B.output ≠ n + j0.val :=
        output_ne_raw (N := n + m) B hBpos houtB (n + j0.val) (by omega)
      have hGHr : ∀ v : Fin m, G i0 v = Hr v :=
        unread_row_eval (G := G) outFn B hrepB i0 (by simpa [reads] using hi0r) houti0
      have hGHc : ∀ u : Fin n, G u j0 = Hc u :=
        unread_col_eval (G := G) outFn B hrepB j0 (by simpa [reads] using hj0r) houtj0
      have hFrowU : ∀ e ∈ ({(i0, i1)} : Finset (Fin n × Fin n)),
          e.1 ≠ e.2 ∧ ∃ side : Bool,
            (Finset.univ.filter (fun col =>
              (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
        intro e he
        have heq : e = (i0, i1) := Finset.mem_singleton.mp he
        subst heq
        refine ⟨hi01, true, ?_⟩
        refine (Finset.card_eq_zero.mpr ?_).le.trans (Nat.zero_le _)
        apply Finset.filter_eq_empty_iff.mpr
        intro col _
        intro hcond
        exact hcond.2 (hGHr col)
      have hFrowD : ∀ e ∈ ({(i0, i1)} : Finset (Fin n × Fin n)),
          ∀ f ∈ ({(i0, i1)} : Finset (Fin n × Fin n)), e ≠ f →
            e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
        intro e he f hf hne
        exact (hne ((Finset.mem_singleton.mp he).trans
          (Finset.mem_singleton.mp hf).symm)).elim
      have hhr1 : 1 ≤ hr := by
        have hle := hbd Hr {(i0, i1)} hFrowU hFrowD
        simpa using hle
      have hFcolU : ∀ e ∈ ({(j0, j1)} : Finset (Fin m × Fin m)),
          e.1 ≠ e.2 ∧ ∃ side : Bool,
            (Finset.univ.filter (fun row =>
              (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
        intro e he
        have heq : e = (j0, j1) := Finset.mem_singleton.mp he
        subst heq
        refine ⟨hj01, true, ?_⟩
        refine (Finset.card_eq_zero.mpr ?_).le.trans (Nat.zero_le _)
        apply Finset.filter_eq_empty_iff.mpr
        intro row _
        intro hcond
        exact hcond.2 (hGHc row)
      have hFcolD : ∀ e ∈ ({(j0, j1)} : Finset (Fin m × Fin m)),
          ∀ f ∈ ({(j0, j1)} : Finset (Fin m × Fin m)), e ≠ f →
            e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
        intro e he f hf hne
        exact (hne ((Finset.mem_singleton.mp he).trans
          (Finset.mem_singleton.mp hf).symm)).elim
      have hhc1 : 1 ≤ hc := by
        have hle := htbd Hc {(j0, j1)} hFcolU hFcolD
        simpa using hle
      have hn4 : 4 ≤ n := by omega
      have hm4 : 4 ≤ m := by omega
      have hused6 : 6 ≤ usedN := by
        have := hwu
        omega
      by_cases hshare : surplusN = 0
      · have hu0 : u = 0 := by omega
        have hP0 : P = 0 := by omega
        have hhit0 : hitUses = 0 := by omega
        have hL1 : L.length ≤ 1 := by
          have := hLle
          omega
        have hpriv4 : ∀ p ∈ L, p.privs.card ≤ 4 := by
          intro p hp
          have hSrange := hpriv_range p hp
          have hsum := rowNames_colNames_card (n := n) (m := m) hSrange
          have hr2 : (rowNames n p.privs).card ≤ 2 := by
            simpa [rowNames_filter_card hSrange] using (hbank p hp).1
          have hc2 : (colNames n m p.privs).card ≤ 2 := by
            simpa [colNames_filter_card hSrange] using (hbank p hp).2
          omega
        have honce4 : once.card ≤ 4 * L.length := by
          have hcov' :
              ((@List.toFinset BTree (Classical.decEq _) L).biUnion BTree.privs) = once := honce'
          have hle := Finset.card_biUnion_le
            (s := @List.toFinset BTree (Classical.decEq _) L) (t := BTree.privs)
          have : once.card ≤
              ∑ p ∈ (@List.toFinset BTree (Classical.decEq _) L), p.privs.card := by
            rw [← hcov']
            exact hle
          have hsum4 :
              ∑ p ∈ (@List.toFinset BTree (Classical.decEq _) L), p.privs.card ≤
                ∑ p ∈ (@List.toFinset BTree (Classical.decEq _) L), 4 :=
            Finset.sum_le_sum (fun p hp =>
              hpriv4 p ((@List.mem_toFinset BTree (Classical.decEq _) L).mp hp))
          have hconst :
              ∑ p ∈ (@List.toFinset BTree (Classical.decEq _) L), 4 =
                4 * (@List.toFinset BTree (Classical.decEq _) L).card := by
            simp [Finset.sum_const, Nat.mul_comm]
          have hcardL :
              (@List.toFinset BTree (Classical.decEq _) L).card ≤ L.length :=
            List.toFinset_card_le L
          omega
        have : usedN ≤ 4 := by
          have := hsplit
          omega
        omega
      · -- unused=2, surplus≥1: caps on pure++chains, coeff-1 union, unread pairs
        have hneg0 :
            ((Finset.range (binarySkeleton B).size).filter
              (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt
                (binarySkeleton B) k).op =
                  PEqualNP.CircuitLowerBounds.GateOp.not)).card = 0 := by
          refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr ?_)
          intro k hk hnot
          have hsz : (binarySkeleton B).size = B.size := binarySkeleton_size B
          have hkl : k < B.gates.length := by
            have : k < (binarySkeleton B).size := Finset.mem_range.mp hk
            simpa [hsz, BinaryCircuit.size] using this
          have hop : (PEqualNP.MetaComplexity.NestedCover.gateAt
              (binarySkeleton B) k).op = PEqualNP.CircuitLowerBounds.GateOp.and := by
            rw [binarySkeleton_gate B k hkl]
          cases hop.symm.trans hnot
        have hshared_ne : sharedAll.Nonempty := by
          by_contra hempty
          have he : sharedAll = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
          have hz : surplusN = 0 := by
            change ∑ w ∈ Finset.range (n + m + B.size), (reads w - 1) = 0
            refine Finset.sum_eq_zero ?_
            intro w hw
            have hle1 : reads w ≤ 1 := by
              by_contra h
              have : 2 ≤ reads w := by omega
              have : w ∈ sharedAll := Finset.mem_filter.mpr ⟨hw, this⟩
              exact Finset.notMem_empty w (he ▸ this)
            omega
          omega
        have hhit_pos : 0 < hitUses := by
          obtain ⟨w, hw⟩ := hshared_ne
          have h2 : 2 ≤ reads w := (Finset.mem_filter.mp hw).2
          have hle := Finset.single_le_sum (f := fun t => reads t)
            (fun _ _ => Nat.zero_le _) hw
          have : 2 ≤ hitUses := by
            change 2 ≤ ∑ t ∈ sharedAll, reads t
            omega
          omega
        have hszB : (binarySkeleton B).size = B.size := binarySkeleton_size B
        have hPeq : P =
            ((Finset.range (binarySkeleton B).size).filter
              (fun k => 2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn
                (binarySkeleton B) (Finset.range (binarySkeleton B).size)
                  (n + m + k))).card := by
          dsimp only [P, reads]
          dsimp only [readsOf]
          rw [← hszB]
        have hMeq : hitUses =
            ∑ w ∈ (Finset.range (n + m + (binarySkeleton B).size)).filter
              (fun w => 2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn
                (binarySkeleton B) (Finset.range (binarySkeleton B).size) w),
              PEqualNP.MetaComplexity.NestedCover.readsIn
                (binarySkeleton B) (Finset.range (binarySkeleton B).size) w := by
          dsimp only [hitUses, sharedAll, reads]
          dsimp only [readsOf]
          rw [← hszB]
        have he1 : 1 ≤ e := by
          have hpos'' : 0 <
              (∑ w ∈ (Finset.range (n + m + (binarySkeleton B).size)).filter
                (fun w => 2 ≤ PEqualNP.MetaComplexity.NestedCover.readsIn
                  (binarySkeleton B) (Finset.range (binarySkeleton B).size) w),
                PEqualNP.MetaComplexity.NestedCover.readsIn
                  (binarySkeleton B) (Finset.range (binarySkeleton B).size) w)
              + ((Finset.range (binarySkeleton B).size).filter
                  (fun k => (PEqualNP.MetaComplexity.NestedCover.gateAt
                    (binarySkeleton B) k).op =
                      PEqualNP.CircuitLowerBounds.GateOp.not)).card := by
            have : 0 < hitUses := hhit_pos
            rw [hMeq] at this
            rw [hneg0]
            exact this
          exact Nat.succ_le_of_lt (hepos hpos'')
        let pieces := pure ++ chains
        have hlenP : pieces.length + 2 * e ≤ P + 1 + 2 * hitUses := by
          have hlen : pieces.length = pure.length + chains.length := by
            simp [pieces, List.length_append]
          have h1 : pure.length + e ≤ P + 1 := by
            have := hlen1
            rw [hneg0] at this
            rw [hPeq]
            exact this
          have h2 : chains.length + e ≤ 2 * hitUses := by
            have := hlen2
            rw [hneg0] at this
            rw [hMeq]
            simpa using this
          have hre : pieces.length + 2 * e = (pure.length + e) + (chains.length + e) := by
            rw [hlen, Nat.two_mul, Nat.add_add_add_comm]
          exact (le_of_eq hre).trans (Nat.add_le_add h1 h2)
        have hdisj_mem {A B : Finset ℕ} (hA : A ∈ pieces) (hB : B ∈ pieces)
            (hne : A ≠ B) : Disjoint A B := by
          obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hA
          obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hB
          have hij : i ≠ j := fun h => hne (by subst h; rfl)
          have hpw := List.pairwise_iff_get.mp hdisj
          let i' : Fin pieces.length := ⟨i, by simpa [pieces] using hi⟩
          let j' : Fin pieces.length := ⟨j, by simpa [pieces] using hj⟩
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · exact hpw i' j' hlt
          · exact (hpw j' i' hgt).symm
        have hcov_once : pieces.toFinset.biUnion id = once := by
          have h2 : once = (Finset.range (n + m)).filter
              (fun w => PEqualNP.MetaComplexity.NestedCover.readsIn
                (binarySkeleton B) (Finset.range (binarySkeleton B).size) w = 1) := by
            dsimp only [once, reads, readsOf]
          have h1 : pieces.toFinset.biUnion id =
              (pure ++ chains).toFinset.biUnion (fun S => S) := rfl
          exact h1.trans (hcov.trans h2.symm)
        have hSrangeP : ∀ S ∈ pieces, S ⊆ Finset.range (n + m) := by
          intro S hS w hw
          have : w ∈ (pieces.toFinset.biUnion id) :=
            Finset.mem_biUnion.mpr ⟨S, List.mem_toFinset.mpr hS, hw⟩
          have : w ∈ once := by rwa [hcov_once] at this
          exact (Finset.mem_filter.mp this).1
        have htreep : ∀ S ∈ pieces,
            S.Nonempty ∧ ∃ E, E.card ≤ 1 ∧
              IsTree (n + m) (binarySkeleton B) S E := by
          intro S hS
          have hmem : S ∈ pure ∨ S ∈ chains := List.mem_append.mp (by simpa [pieces] using hS)
          rcases hmem with hS' | hS'
          · obtain ⟨hne, ht⟩ := hpure S hS'
            exact ⟨hne, ∅, by simp, isTree_of_andOr_tree ht⟩
          · obtain ⟨hne, ⟨b, ht⟩⟩ := hchains S hS'
            exact ⟨hne, {b}, by simp, isTree_of_andOr_tree ht⟩
        have hbankS : ∀ S ∈ pieces,
            (rowNames n S).card ≤ 2 ∧ (colNames n m S).card ≤ 2 := by
          intro S hS
          obtain ⟨hne, E, hEcard, htree⟩ := htreep S hS
          exact isTree_piece_bank_caps (outFn := outFn) (D := B) (S := S) (E := E)
            hn hm hrich htrich hrepB htree hEcard (hSrangeP S hS) hBack hSback hSout
        have hrow_pairS : ∀ S ∈ pieces, (rowNames n S).card = 2 →
            ∃ e : Fin n × Fin n,
              e.1 ≠ e.2 ∧ e.1.val ∈ S ∧ e.2.val ∈ S ∧
              ∃ side : Bool,
                (Finset.univ.filter (fun col =>
                  (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
          intro S hS h2r
          obtain ⟨hne, E, hEcard, htree⟩ := htreep S hS
          have h2 : 2 ≤ (rowNames n S).card ∨ 2 ≤ (colNames n m S).card :=
            Or.inl (by omega)
          obtain ⟨⟨t, q0, q, U, h0, hfac⟩, _⟩ :=
            isTree_factors (G := G) outFn B S E hrepB htree hEcard
              (hSrangeP S hS) hBack hSback hSout h2
          have hT : (colNames n m S).card ≤ 2 := (hbankS S hS).2
          obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2r
          have ha : a ∈ rowNames n S := by simp [hs]
          have hb : b ∈ rowNames n S := by simp [hs]
          obtain ⟨e, hne, he1, he2, hside⟩ :=
            affordable_of_row_factor (G := G) (rowNames n S)
              (colNames n m S) Hr hT t q0 q U h0 hfac ha hb hab
          have hmem (x : Fin n) (hx : x = a ∨ x = b) : x.val ∈ S := by
            have : x ∈ rowNames n S := by
              rcases hx with hx | hx <;> simp [hs, hx]
            exact (Finset.mem_filter.mp this).2
          exact ⟨e, hne, hmem e.1 he1, hmem e.2 he2, hside⟩
        have hcol_pairS : ∀ S ∈ pieces, (colNames n m S).card = 2 →
            ∃ e : Fin m × Fin m,
              e.1 ≠ e.2 ∧ n + e.1.val ∈ S ∧ n + e.2.val ∈ S ∧
              ∃ side : Bool,
                (Finset.univ.filter (fun row =>
                  (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
          intro S hS h2c
          obtain ⟨hne, E, hEcard, htree⟩ := htreep S hS
          have h2 : 2 ≤ (rowNames n S).card ∨ 2 ≤ (colNames n m S).card :=
            Or.inr (by omega)
          obtain ⟨_, ⟨t, q0, q, U, h0, hfac⟩⟩ :=
            isTree_factors (G := G) outFn B S E hrepB htree hEcard
              (hSrangeP S hS) hBack hSback hSout h2
          have hR2 : (rowNames n S).card ≤ 2 := (hbankS S hS).1
          obtain ⟨a, b, hab, hs⟩ := Finset.card_eq_two.mp h2c
          have ha : a ∈ colNames n m S := by simp [hs]
          have hb : b ∈ colNames n m S := by simp [hs]
          obtain ⟨e, hne, he1, he2, hside⟩ :=
            affordable_of_col_factor (G := G) (colNames n m S)
              (rowNames n S) Hc hR2 t q0 q U h0 hfac ha hb hab
          have hmem (x : Fin m) (hx : x = a ∨ x = b) : n + x.val ∈ S := by
            have : x ∈ colNames n m S := by
              rcases hx with hx | hx <;> simp [hs, hx]
            exact (Finset.mem_filter.mp this).2
          exact ⟨e, hne, hmem e.1 he1, hmem e.2 he2, hside⟩
        let Pfin := pieces.toFinset
        let rowPiecesS := Pfin.filter (fun S => (rowNames n S).card = 2)
        let colPiecesS := Pfin.filter (fun S => (colNames n m S).card = 2)
        have hexRS : ∀ S ∈ rowPiecesS, ∃ e : Fin n × Fin n,
            e.1 ≠ e.2 ∧ e.1.val ∈ S ∧ e.2.val ∈ S ∧
            ∃ side : Bool,
              (Finset.univ.filter (fun col =>
                (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
          intro S hS
          have ⟨hSp, h2r⟩ := Finset.mem_filter.mp hS
          exact hrow_pairS S (List.mem_toFinset.mp hSp) h2r
        choose fRS hfRS using hexRS
        have hexCS : ∀ S ∈ colPiecesS, ∃ e : Fin m × Fin m,
            e.1 ≠ e.2 ∧ n + e.1.val ∈ S ∧ n + e.2.val ∈ S ∧
            ∃ side : Bool,
              (Finset.univ.filter (fun row =>
                (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
          intro S hS
          have ⟨hSp, h2c⟩ := Finset.mem_filter.mp hS
          exact hcol_pairS S (List.mem_toFinset.mp hSp) h2c
        choose fCS hfCS using hexCS
        let FrowP := rowPiecesS.attach.image (fun S => fRS S.1 S.2)
        let FcolP := colPiecesS.attach.image (fun S => fCS S.1 S.2)
        have hFrowP_aff : ∀ e ∈ FrowP, e.1 ≠ e.2 ∧ ∃ side : Bool,
            (Finset.univ.filter (fun col =>
              (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
          intro e he
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp he
          exact ⟨(hfRS S.1 S.2).1, (hfRS S.1 S.2).2.2.2⟩
        have hFcolP_aff : ∀ e ∈ FcolP, e.1 ≠ e.2 ∧ ∃ side : Bool,
            (Finset.univ.filter (fun row =>
              (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
          intro e he
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp he
          exact ⟨(hfCS S.1 S.2).1, (hfCS S.1 S.2).2.2.2⟩
        have hFrowP_disj : ∀ e ∈ FrowP, ∀ f ∈ FrowP, e ≠ f →
            e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
          intro e he f hf hne
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hf
          have hST : S.1 ≠ T.1 := fun h => hne (by cases S; cases T; subst h; rfl)
          have hSL := List.mem_toFinset.mp (Finset.mem_filter.mp S.2).1
          have hTL := List.mem_toFinset.mp (Finset.mem_filter.mp T.2).1
          have hdis := hdisj_mem hSL hTL hST
          have dS := hfRS S.1 S.2
          have dT := hfRS T.1 T.2
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.1 (h ▸ dT.2.1)
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.1 (h ▸ dT.2.2.1)
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.2.1 (h ▸ dT.2.1)
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.2.1 (h ▸ dT.2.2.1)
        have hFcolP_disj : ∀ e ∈ FcolP, ∀ f ∈ FcolP, e ≠ f →
            e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
          intro e he f hf hne
          obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp he
          obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hf
          have hST : S.1 ≠ T.1 := fun h => hne (by cases S; cases T; subst h; rfl)
          have hSL := List.mem_toFinset.mp (Finset.mem_filter.mp S.2).1
          have hTL := List.mem_toFinset.mp (Finset.mem_filter.mp T.2).1
          have hdis := hdisj_mem hSL hTL hST
          have dS := hfCS S.1 S.2
          have dT := hfCS T.1 T.2
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.1 (h ▸ dT.2.1)
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.1 (h ▸ dT.2.2.1)
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.2.1 (h ▸ dT.2.1)
          · intro h; exact Finset.disjoint_left.mp hdis dS.2.2.1 (h ▸ dT.2.2.1)
        have hFrowP_le : FrowP.card ≤ hr := hbd Hr FrowP hFrowP_aff hFrowP_disj
        have hFcolP_le : FcolP.card ≤ hc := htbd Hc FcolP hFcolP_aff hFcolP_disj
        let rowEnds : Finset (Fin n) :=
          FrowP.image Prod.fst ∪ FrowP.image Prod.snd
        have hi0n : i0 ∉ rowEnds := by
          intro hin
          have hmem : i0.val ∈ once := by
            rcases Finset.mem_union.mp hin with h | h
            · obtain ⟨ep, hep, heq⟩ := Finset.mem_image.mp h
              obtain ⟨S, hS, hSeq⟩ := Finset.mem_image.mp hep
              have : i0.val ∈ S.1 := by
                have := (hfRS S.1 S.2).2.1
                simpa [hSeq, heq] using this
              have hSL := List.mem_toFinset.mp (Finset.mem_filter.mp S.2).1
              exact hcov_once ▸ Finset.mem_biUnion.mpr ⟨S.1, List.mem_toFinset.mpr hSL, this⟩
            · obtain ⟨ep, hep, heq⟩ := Finset.mem_image.mp h
              obtain ⟨S, hS, hSeq⟩ := Finset.mem_image.mp hep
              have : i0.val ∈ S.1 := by
                have := (hfRS S.1 S.2).2.2.1
                simpa [hSeq, heq] using this
              have hSL := List.mem_toFinset.mp (Finset.mem_filter.mp S.2).1
              exact hcov_once ▸ Finset.mem_biUnion.mpr ⟨S.1, List.mem_toFinset.mpr hSL, this⟩
          have : reads i0.val = 1 := (Finset.mem_filter.mp hmem).2
          have : reads i0.val = 0 := hi0r
          omega
        have hfreeR : (Finset.univ \ (rowEnds ∪ {i0}) : Finset (Fin n)).Nonempty := by
          have hends : rowEnds.card ≤ 2 * FrowP.card :=
            (Finset.card_union_le _ _).trans
              ((Nat.add_le_add
                (Finset.card_image_le (f := Prod.fst) (s := FrowP))
                (Finset.card_image_le (f := Prod.snd) (s := FrowP))).trans
                (le_of_eq (Nat.two_mul FrowP.card).symm))
          have hunion : (rowEnds ∪ {i0}).card ≤ rowEnds.card + 1 :=
            (Finset.card_union_le _ _).trans (by simp)
          have hU : (Finset.univ : Finset (Fin n)).card = n := by simp
          have hunion' : (rowEnds ∪ {i0}).card ≤ 2 * hr + 1 :=
            hunion.trans (Nat.add_le_add_right
              (hends.trans (Nat.mul_le_mul_left 2 hFrowP_le)) 1)
          have hsdiff :
              (Finset.univ \ (rowEnds ∪ {i0}) : Finset (Fin n)).card =
                n - (rowEnds ∪ {i0}).card := by
            have hcs : (Finset.univ \ (rowEnds ∪ {i0}) : Finset (Fin n)).card =
                (Finset.univ : Finset (Fin n)).card
                  - ((rowEnds ∪ {i0}) ∩ Finset.univ).card :=
              Finset.card_sdiff
            simpa [hU, Finset.inter_univ] using hcs
          have : 0 < (Finset.univ \ (rowEnds ∪ {i0}) : Finset (Fin n)).card := by
            rw [hsdiff]
            exact Nat.sub_pos_of_lt (lt_of_le_of_lt hunion' (Nat.lt_of_succ_le hhr))
          exact Finset.card_pos.mp this
        obtain ⟨i1', hi1'm⟩ := hfreeR
        have hi01' : i0 ≠ i1' := by
          intro h
          have := (Finset.mem_sdiff.mp hi1'm).2
          exact this (Finset.mem_union_right _ (by simp [h]))
        have hi1'n : i1' ∉ rowEnds := by
          intro h
          exact (Finset.mem_sdiff.mp hi1'm).2 (Finset.mem_union_left _ h)
        have hFrowU' : ∀ e ∈ (FrowP ∪ ({(i0, i1')} : Finset (Fin n × Fin n))),
            e.1 ≠ e.2 ∧ ∃ side : Bool,
              (Finset.univ.filter (fun col =>
                (G e.1 col != G e.2 col) = side ∧ G e.1 col ≠ Hr col)).card ≤ 2 := by
          intro e he
          rcases Finset.mem_union.mp he with h | h
          · exact hFrowP_aff e h
          · have heq : e = (i0, i1') := Finset.mem_singleton.mp h
            subst heq
            refine ⟨hi01', true, ?_⟩
            refine (Finset.card_eq_zero.mpr ?_).le.trans (Nat.zero_le _)
            apply Finset.filter_eq_empty_iff.mpr
            intro col _
            intro hcond
            exact hcond.2 (hGHr col)
        have hFrowD' : ∀ e ∈ (FrowP ∪ ({(i0, i1')} : Finset (Fin n × Fin n))),
            ∀ f ∈ (FrowP ∪ ({(i0, i1')} : Finset (Fin n × Fin n))), e ≠ f →
              e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
          intro e he f hf hne
          rcases Finset.mem_union.mp he with heP | heU <;>
            rcases Finset.mem_union.mp hf with hfP | hfU
          · exact hFrowP_disj e heP f hfP hne
          · have hf' : f = (i0, i1') := Finset.mem_singleton.mp hfU
            subst hf'
            have h1 : e.1 ≠ i0 := by
              intro h
              have : i0 ∈ rowEnds := by
                exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩)
              exact hi0n this
            have h2 : e.2 ≠ i0 := by
              intro h
              have : i0 ∈ rowEnds := by
                exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩)
              exact hi0n this
            have h3 : e.1 ≠ i1' := by
              intro h
              have : i1' ∈ rowEnds :=
                Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩)
              exact hi1'n this
            have h4 : e.2 ≠ i1' := by
              intro h
              have : i1' ∈ rowEnds :=
                Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩)
              exact hi1'n this
            exact ⟨h1, h3, h2, h4⟩
          · have he' : e = (i0, i1') := Finset.mem_singleton.mp heU
            subst he'
            have h1 : i0 ≠ f.1 := by
              intro h
              have : i0 ∈ rowEnds :=
                Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩)
              exact hi0n this
            have h2 : i0 ≠ f.2 := by
              intro h
              have : i0 ∈ rowEnds :=
                Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩)
              exact hi0n this
            have h3 : i1' ≠ f.1 := by
              intro h
              have : i1' ∈ rowEnds :=
                Finset.mem_union_left _ (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩)
              exact hi1'n this
            have h4 : i1' ≠ f.2 := by
              intro h
              have : i1' ∈ rowEnds :=
                Finset.mem_union_right _ (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩)
              exact hi1'n this
            exact ⟨h1, h2, h3, h4⟩
          · exact (hne ((Finset.mem_singleton.mp heU).trans
              (Finset.mem_singleton.mp hfU).symm)).elim
        have hFrowP1 : (FrowP ∪ ({(i0, i1')} : Finset (Fin n × Fin n))).card ≤ hr :=
          hbd Hr _ hFrowU' hFrowD'
        have hFrowP_lt : FrowP.card + 1 ≤ hr := by
          have hnin : (i0, i1') ∉ FrowP := by
            intro h
            exact hi0n (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨(i0, i1'), h, rfl⟩))
          have hdis : Disjoint FrowP ({(i0, i1')} : Finset (Fin n × Fin n)) :=
            Finset.disjoint_singleton_right.mpr hnin
          have := hFrowP1
          rw [Finset.card_union_of_disjoint hdis, Finset.card_singleton] at this
          exact this
        -- same for columns
        let colEnds : Finset (Fin m) :=
          FcolP.image Prod.fst ∪ FcolP.image Prod.snd
        have hj0n : j0 ∉ colEnds := by
          intro hin
          have hmem : n + j0.val ∈ once := by
            rcases Finset.mem_union.mp hin with h | h
            · obtain ⟨ep, hep, heq⟩ := Finset.mem_image.mp h
              obtain ⟨S, hS, hSeq⟩ := Finset.mem_image.mp hep
              have : n + j0.val ∈ S.1 := by
                have := (hfCS S.1 S.2).2.1
                simpa [hSeq, heq] using this
              have hSL := List.mem_toFinset.mp (Finset.mem_filter.mp S.2).1
              exact hcov_once ▸ Finset.mem_biUnion.mpr ⟨S.1, List.mem_toFinset.mpr hSL, this⟩
            · obtain ⟨ep, hep, heq⟩ := Finset.mem_image.mp h
              obtain ⟨S, hS, hSeq⟩ := Finset.mem_image.mp hep
              have : n + j0.val ∈ S.1 := by
                have := (hfCS S.1 S.2).2.2.1
                simpa [hSeq, heq] using this
              have hSL := List.mem_toFinset.mp (Finset.mem_filter.mp S.2).1
              exact hcov_once ▸ Finset.mem_biUnion.mpr ⟨S.1, List.mem_toFinset.mpr hSL, this⟩
          have : reads (n + j0.val) = 1 := (Finset.mem_filter.mp hmem).2
          have : reads (n + j0.val) = 0 := hj0r
          omega
        have hfreeC : (Finset.univ \ (colEnds ∪ {j0}) : Finset (Fin m)).Nonempty := by
          have hends : colEnds.card ≤ 2 * FcolP.card :=
            (Finset.card_union_le _ _).trans
              ((Nat.add_le_add
                (Finset.card_image_le (f := Prod.fst) (s := FcolP))
                (Finset.card_image_le (f := Prod.snd) (s := FcolP))).trans
                (le_of_eq (Nat.two_mul FcolP.card).symm))
          have hunion : (colEnds ∪ {j0}).card ≤ colEnds.card + 1 :=
            (Finset.card_union_le _ _).trans (by simp)
          have hU : (Finset.univ : Finset (Fin m)).card = m := by simp
          have hunion' : (colEnds ∪ {j0}).card ≤ 2 * hc + 1 :=
            hunion.trans (Nat.add_le_add_right
              (hends.trans (Nat.mul_le_mul_left 2 hFcolP_le)) 1)
          have hsdiff :
              (Finset.univ \ (colEnds ∪ {j0}) : Finset (Fin m)).card =
                m - (colEnds ∪ {j0}).card := by
            have hcs : (Finset.univ \ (colEnds ∪ {j0}) : Finset (Fin m)).card =
                (Finset.univ : Finset (Fin m)).card
                  - ((colEnds ∪ {j0}) ∩ Finset.univ).card :=
              Finset.card_sdiff
            simpa [hU, Finset.inter_univ] using hcs
          have : 0 < (Finset.univ \ (colEnds ∪ {j0}) : Finset (Fin m)).card := by
            rw [hsdiff]
            exact Nat.sub_pos_of_lt (lt_of_le_of_lt hunion' (Nat.lt_of_succ_le hhc))
          exact Finset.card_pos.mp this
        obtain ⟨j1', hj1'm⟩ := hfreeC
        have hj01' : j0 ≠ j1' := by
          intro h
          exact (Finset.mem_sdiff.mp hj1'm).2 (Finset.mem_union_right _ (by simp [h]))
        have hj1'n : j1' ∉ colEnds := by
          intro h
          exact (Finset.mem_sdiff.mp hj1'm).2 (Finset.mem_union_left _ h)
        have hFcolU' : ∀ e ∈ (FcolP ∪ ({(j0, j1')} : Finset (Fin m × Fin m))),
            e.1 ≠ e.2 ∧ ∃ side : Bool,
              (Finset.univ.filter (fun row =>
                (G row e.1 != G row e.2) = side ∧ G row e.1 ≠ Hc row)).card ≤ 2 := by
          intro e he
          rcases Finset.mem_union.mp he with h | h
          · exact hFcolP_aff e h
          · have heq : e = (j0, j1') := Finset.mem_singleton.mp h
            subst heq
            refine ⟨hj01', true, ?_⟩
            refine (Finset.card_eq_zero.mpr ?_).le.trans (Nat.zero_le _)
            apply Finset.filter_eq_empty_iff.mpr
            intro row _
            intro hcond
            exact hcond.2 (hGHc row)
        have hFcolD' : ∀ e ∈ (FcolP ∪ ({(j0, j1')} : Finset (Fin m × Fin m))),
            ∀ f ∈ (FcolP ∪ ({(j0, j1')} : Finset (Fin m × Fin m))), e ≠ f →
              e.1 ≠ f.1 ∧ e.1 ≠ f.2 ∧ e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
          intro e he f hf hne
          rcases Finset.mem_union.mp he with heP | heU <;>
            rcases Finset.mem_union.mp hf with hfP | hfU
          · exact hFcolP_disj e heP f hfP hne
          · have hf' : f = (j0, j1') := Finset.mem_singleton.mp hfU
            subst hf'
            have h1 : e.1 ≠ j0 := by
              intro h
              exact hj0n (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩))
            have h2 : e.2 ≠ j0 := by
              intro h
              exact hj0n (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩))
            have h3 : e.1 ≠ j1' := by
              intro h
              exact hj1'n (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩))
            have h4 : e.2 ≠ j1' := by
              intro h
              exact hj1'n (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨e, heP, by simp [h]⟩))
            exact ⟨h1, h3, h2, h4⟩
          · have he' : e = (j0, j1') := Finset.mem_singleton.mp heU
            subst he'
            have h1 : j0 ≠ f.1 := by
              intro h
              exact hj0n (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩))
            have h2 : j0 ≠ f.2 := by
              intro h
              exact hj0n (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩))
            have h3 : j1' ≠ f.1 := by
              intro h
              exact hj1'n (Finset.mem_union_left _
                (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩))
            have h4 : j1' ≠ f.2 := by
              intro h
              exact hj1'n (Finset.mem_union_right _
                (Finset.mem_image.mpr ⟨f, hfP, by simp [h]⟩))
            exact ⟨h1, h2, h3, h4⟩
          · exact (hne ((Finset.mem_singleton.mp heU).trans
              (Finset.mem_singleton.mp hfU).symm)).elim
        have hFcolP1 : (FcolP ∪ ({(j0, j1')} : Finset (Fin m × Fin m))).card ≤ hc :=
          htbd Hc _ hFcolU' hFcolD'
        have hFcolP_lt : FcolP.card + 1 ≤ hc := by
          have hnin : (j0, j1') ∉ FcolP := by
            intro h
            exact hj0n (Finset.mem_union_left _
              (Finset.mem_image.mpr ⟨(j0, j1'), h, rfl⟩))
          have hdis : Disjoint FcolP ({(j0, j1')} : Finset (Fin m × Fin m)) :=
            Finset.disjoint_singleton_right.mpr hnin
          have := hFcolP1
          rw [Finset.card_union_of_disjoint hdis, Finset.card_singleton] at this
          exact this
        let HP : Finset ℕ :=
          FrowP.image (fun e => e.1.val) ∪ FcolP.image (fun e => n + e.1.val)
        have hHPle : HP.card + 2 ≤ hr + hc := by
          have hcard : HP.card ≤ FrowP.card + FcolP.card :=
            (Finset.card_union_le _ _).trans (Nat.add_le_add
              (Finset.card_image_le (f := fun e : Fin n × Fin n => e.1.val) (s := FrowP))
              (Finset.card_image_le (f := fun e : Fin m × Fin m => n + e.1.val) (s := FcolP)))
          have := hFrowP_lt
          have := hFcolP_lt
          omega
        have hsmall1 : ∀ S ∈ pieces, S.card ≤ 2 + (S ∩ HP).card := by
          intro S hS
          have hSr := hSrangeP S hS
          have hsum := rowNames_colNames_card (n := n) (m := m) hSr
          have hr2 : (rowNames n S).card ≤ 2 := (hbankS S hS).1
          have hc2 : (colNames n m S).card ≤ 2 := (hbankS S hS).2
          have hmr (h2r : (rowNames n S).card = 2) :
              (fRS S (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hS, h2r⟩)).1.val
                ∈ S ∩ HP := by
            have hpR : S ∈ rowPiecesS :=
              Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hS, h2r⟩
            let a : { x // x ∈ rowPiecesS } := ⟨S, hpR⟩
            have hin : a ∈ rowPiecesS.attach := Finset.mem_attach _ _
            have heF : fRS S hpR ∈ FrowP := Finset.mem_image.mpr ⟨a, hin, rfl⟩
            exact Finset.mem_inter.mpr ⟨(hfRS S hpR).2.1,
              Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fRS S hpR, heF, rfl⟩)⟩
          have hmc (h2c : (colNames n m S).card = 2) :
              n + (fCS S (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hS, h2c⟩)).1.val
                ∈ S ∩ HP := by
            have hpC : S ∈ colPiecesS :=
              Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hS, h2c⟩
            let a : { x // x ∈ colPiecesS } := ⟨S, hpC⟩
            have hin : a ∈ colPiecesS.attach := Finset.mem_attach _ _
            have heF : fCS S hpC ∈ FcolP := Finset.mem_image.mpr ⟨a, hin, rfl⟩
            exact Finset.mem_inter.mpr ⟨(hfCS S hpC).2.1,
              Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fCS S hpC, heF, rfl⟩)⟩
          by_cases h2r : (rowNames n S).card = 2
          · by_cases h2c : (colNames n m S).card = 2
            · have hrH := hmr h2r
              have hcH := hmc h2c
              have hpR : S ∈ rowPiecesS :=
                Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hS, h2r⟩
              have hpC : S ∈ colPiecesS :=
                Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hS, h2c⟩
              have hdis : (fRS S hpR).1.val ≠ n + (fCS S hpC).1.val :=
                Nat.ne_of_lt ((fRS S hpR).1.isLt.trans_le (Nat.le_add_right _ _))
              have hinter : 2 ≤ (S ∩ HP).card := by
                have h2in : ({(fRS S hpR).1.val, n + (fCS S hpC).1.val} : Finset ℕ) ⊆ S ∩ HP := by
                  intro x hx
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                  rcases hx with rfl | rfl <;> assumption
                have hcard : ({(fRS S hpR).1.val, n + (fCS S hpC).1.val} : Finset ℕ).card = 2 :=
                  Finset.card_pair hdis
                exact hcard.symm.le.trans (Finset.card_le_card h2in)
              have hScard : S.card = 4 := by
                rw [hsum, h2r, h2c]
              rw [hScard]
              exact Nat.add_le_add_left hinter 2
            · have hinter : 1 ≤ (S ∩ HP).card :=
                Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨_, hmr h2r⟩)
              have hc1 : (colNames n m S).card ≤ 1 := by
                apply Nat.le_of_lt_succ
                exact Nat.lt_of_le_of_ne hc2 (Ne.symm (by intro h; exact h2c h.symm))
              have hScard : S.card ≤ 3 := by
                have : S.card = 2 + (colNames n m S).card := by rw [hsum, h2r]
                exact this.le.trans (Nat.add_le_add_left hc1 2)
              exact hScard.trans (Nat.add_le_add_left hinter 2)
          · by_cases h2c : (colNames n m S).card = 2
            · have hinter : 1 ≤ (S ∩ HP).card :=
                Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨_, hmc h2c⟩)
              have hr1 : (rowNames n S).card ≤ 1 := by
                apply Nat.le_of_lt_succ
                exact Nat.lt_of_le_of_ne hr2 (Ne.symm (by intro h; exact h2r h.symm))
              have hScard : S.card ≤ 3 := by
                have : S.card = (rowNames n S).card + 2 := by rw [hsum, h2c]
                exact this.le.trans (Nat.add_le_add_right hr1 2)
              exact hScard.trans (Nat.add_le_add_left hinter 2)
            · have hr1 : (rowNames n S).card ≤ 1 := by
                apply Nat.le_of_lt_succ
                exact Nat.lt_of_le_of_ne hr2 (Ne.symm (by intro h; exact h2r h.symm))
              have hc1 : (colNames n m S).card ≤ 1 := by
                apply Nat.le_of_lt_succ
                exact Nat.lt_of_le_of_ne hc2 (Ne.symm (by intro h; exact h2c h.symm))
              have hScard : S.card ≤ 2 := by
                have := hsum
                exact this.le.trans (Nat.add_le_add hr1 hc1)
              exact hScard.trans (Nat.le_add_right _ _)
        have honce_le :
            once.card ≤ 2 * pieces.length + (once ∩ HP).card := by
          have hmu := marked_union_one pieces HP (by simpa [pieces] using hdisj)
            (fun S hS => hsmall1 S hS)
          simpa [hcov_once] using hmu
        have husedP : usedN + 4 * e ≤ 10 * surplusN + 2 + HP.card := by
          have honceH : (once ∩ HP).card ≤ HP.card :=
            Finset.card_le_card (fun x hx => (Finset.mem_inter.mp hx).2)
          have honce' : once.card ≤ 2 * pieces.length + HP.card := by
            have := honce_le
            omega
          have hused_eq : usedN = once.card + u := by simpa [u] using hsplit
          have : usedN + 4 * e ≤ 4 * hitUses + 2 * P + 2 + HP.card + u := by
            have := hlenP
            omega
          have : usedN + 4 * e ≤
              4 * (surplusN + u + P) + 2 * P + 2 + HP.card + u := by
            have := hhit_le
            omega
          have : usedN + 4 * e ≤ 4 * surplusN + 5 * u + 6 * P + 2 + HP.card := by omega
          have : usedN + 4 * e ≤ 4 * surplusN + 5 * (u + P) + P + 2 + HP.card := by omega
          have : usedN + 4 * e ≤ 9 * surplusN + P + 2 + HP.card := by omega
          omega
        have : 11 * (n + m) ≤ 10 * B.size + 26 + 2 * (hr + hc) := by
          have hwu' : usedN + unusedN = n + m := hwu
          have hU2' : unusedN = 2 := hU2
          have hbud : usedN + surplusN = B.size + 1 := hbudget'
          have hclose : 11 * usedN + 4 * e ≤ 10 * B.size + 12 + HP.card := by
            have := husedP
            -- 11 used + 4e ≤ 10 used + (10d + 2 + HP.card) = 10(used+d) + 2 + HP
            omega
          have : 11 * (n + m) + 4 * e ≤ 10 * B.size + 34 + HP.card := by omega
          have : 11 * (n + m) + 4 ≤ 10 * B.size + 34 + HP.card := by
            have := he1
            omega
          have : 11 * (n + m) ≤ 10 * B.size + 30 + HP.card := by omega
          have : 11 * (n + m) + 2 ≤ 10 * B.size + 30 + (hr + hc) := by
            have := hHPle
            omega
          have : 11 * (n + m) ≤ 10 * B.size + 28 + (hr + hc) := by omega
          omega
        exact this.trans (Nat.add_le_add_right (Nat.add_le_add_right
          (Nat.mul_le_mul_left 10 hs2) _) _)
