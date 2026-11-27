import PEqualNP.Defs
import PEqualNP.Outside.L_meta_24613
import PEqualNP.Outside.L_meta_19452
import PEqualNP.Outside.L_meta_19453
import PEqualNP.Outside.L_meta_20813

/-!
# L-meta-25930 — a small `FanInTwo` circuit is already `Monotone2`

If a boolean matrix `G` (with at most `a` equal rows and at most `b` equal columns) is
represented by a `FanInTwo` circuit of size at most `s`, and `s + a + b < n + m`, then `G`
is also represented by a `Monotone2` circuit of the same size.

Proof route.

* `L_meta_24613` normalises `C` into a circuit `D` whose AND/OR gates have fan-in exactly two
  and whose NOT gates have fan-in exactly one, reading only earlier wires, with
  `D.output + 1 = (n + m) + D.size` and `D.size ≤ C.size`.
* `L_meta_19453` / `L_meta_19452` say that two input wires that no gate of `D` ever reads
  force the corresponding two columns / rows of `G` to be equal. Hence at most `a` left wires
  and at most `b` right wires go unread, so at least `n + m - a - b` input wires are read and
  therefore at least that many input occurrences are counted.
* `L_meta_20813` writes `D.size + 1` as input occurrences plus repeated internal reads plus
  one slot per NOT gate. A NOT gate would give `n + m - a - b ≤ D.size`, while
  `D.size ≤ C.size ≤ s` and `s + a + b < n + m` give `D.size < n + m - a - b`. Contradiction,
  so `D` has no NOT gate and is `Monotone2`.

SPDX-License-Identifier: Apache-2.0
-/

namespace PEqualNP.Outside.L_meta_25930_aux

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents

/-- Counting indices below `k` as elements of `Fin k`. -/private theorem card_filter_range_eq_fin (k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((Finset.range k).filter P).card =
      ((Finset.univ : Finset (Fin k)).filter (fun i => P i.val)).card := by
  classical
  have hinj : Function.Injective (fun i : Fin k => i.val) := fun a b h => Fin.ext h
  have heq : (Finset.range k).filter P =
      ((Finset.univ : Finset (Fin k)).filter (fun i => P i.val)).image (fun i => i.val) := by
    ext w
    constructor
    · intro hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      exact Finset.mem_image.mpr ⟨⟨w, Finset.mem_range.mp hw1⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw2⟩, rfl⟩
    · intro hw
      obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp hw
      have hi' := (Finset.mem_filter.mp hi).2
      rw [← hiv]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hi'⟩
  rw [heq, Finset.card_image_of_injective _ hinj]

/-- Shifting by `n`: the indices `w` of `range (n + m)` with `n ≤ w` are the `Fin m`. -/
private theorem card_filter_shift (n m : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (((Finset.range (n + m)).filter (fun w => n ≤ w)).filter P).card =
      ((Finset.univ : Finset (Fin m)).filter (fun v => P (n + v.val))).card := by
  classical
  have hinj : Function.Injective (fun v : Fin m => n + v.val) := by
    intro a b h
    exact Fin.ext (by simp only at h; omega)
  have heq : ((Finset.range (n + m)).filter (fun w => n ≤ w)).filter P =
      ((Finset.univ : Finset (Fin m)).filter (fun v => P (n + v.val))).image
        (fun v => n + v.val) := by
    ext w
    constructor
    · intro hw
      obtain ⟨hw1, hw2⟩ := Finset.mem_filter.mp hw
      obtain ⟨hw1, hw3⟩ := Finset.mem_filter.mp hw1
      have hw4 := Finset.mem_range.mp hw1
      refine Finset.mem_image.mpr ⟨⟨w - n, by omega⟩, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rwa [Nat.add_sub_cancel' hw3]
      · simp only [Fin.val_mk]
        omega
    · intro hw
      obtain ⟨v, hv, hvw⟩ := Finset.mem_image.mp hw
      have hvP := (Finset.mem_filter.mp hv).2
      rw [← hvw]
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), by omega⟩, hvP⟩
  rw [heq, Finset.card_image_of_injective _ hinj]

/-- A single gate contributes at most the total read count of a wire. -/
private theorem count_le_readsIn (D : Circuit) (w : ℕ) {j : ℕ} (hj : j < D.size) :
    (gateAt D j).inputs.count w ≤ readsIn D (Finset.range D.size) w := by
  rw [readsIn]
  exact Finset.single_le_sum (f := fun i => (gateAt D i).inputs.count w)
    (fun i _ => Nat.zero_le _) (Finset.mem_range.mpr hj)

/-- A gate that reads wire `w` makes that wire's read count positive. -/
private theorem one_le_readsIn (D : Circuit) (w : ℕ) {g : ℕ} (hg : g < D.size)
    (hmem : w ∈ (gateAt D g).inputs) : 1 ≤ readsIn D (Finset.range D.size) w := by
  have h1 : 1 ≤ (gateAt D g).inputs.count w := List.one_le_count_iff.mpr hmem
  have h2 := count_le_readsIn D w hg
  omega

/-- A NOT gate inside `D` forces its `not`-count to be positive. -/
private theorem not_count_pos (D : Circuit) (h : ∃ g ∈ D.gates, g.op = GateOp.not) :
    0 < (@Finset.filter ℕ (fun k => (gateAt D k).op = GateOp.not)
      (fun d1 => Classical.propDecidable _) (Finset.range D.size)).card := by
  classical
  obtain ⟨g, hg, hop⟩ := h
  obtain ⟨k, hk, hkg⟩ := List.mem_iff_getElem.mp hg
  refine Finset.card_pos.mpr ⟨k, ?_⟩
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
  · simpa [Circuit.size] using hk
  · rw [gateAt, List.getD_eq_getElem _ _ hk, hkg]
    exact hop

end PEqualNP.Outside.L_meta_25930_aux

open PEqualNP.Outside.L_meta_25930_aux
open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Represents

theorem PEqualNP.Outside.L_meta_25930 :
    ∀ (n m a b s : ℕ) (G : Fin n → Fin m → Bool),
  (∃ (r t : Fin n) (c u : Fin m), G r c ≠ G t u) →
  (∀ r : Fin n, (Finset.univ.filter (fun t : Fin n => ∀ c : Fin m, G t c = G r c)).card ≤ a) →
  (∀ c : Fin m, (Finset.univ.filter (fun u : Fin m => ∀ r : Fin n, G r u = G r c)).card ≤ b) →
  s + a + b < n + m →
  (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
    C.size ≤ s ∧ PEqualNP.Represents.Represents G C) →
  ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
    D.size ≤ s ∧ PEqualNP.Represents.Represents G D := by
  classical
  intro n m a b s G hne hrow hcol hstrict ⟨C, hfan, hsize, hrep⟩
  obtain ⟨D, hDfan, hDrep, hDsizeC, hDbig⟩ :=
    PEqualNP.Outside.L_meta_24613 n m G C hfan hrep hne
  rcases hDbig.1 with ⟨hshp, hrb, hpos, hout, hlast⟩ | ⟨hzero, houtlt⟩
  · -- Positive normal form: `D.output + 1 = (n + m) + D.size`.
    have hbig : n + m ≤ D.output := by omega
    -- Two unread rows of `D` agree everywhere in `G`.
    have row_eq : ∀ (u u' : Fin n),
        readsIn D (Finset.range D.size) u.val = 0 →
        readsIn D (Finset.range D.size) u'.val = 0 → ∀ c : Fin m, G u c = G u' c := by
      intro u u' hu hu' c
      have hout1 : D.output ≠ u.val := by omega
      have hout2 : D.output ≠ u'.val := by omega
      have key : ∀ (w : ℕ), readsIn D (Finset.range D.size) w = 0 →
          ∀ g < D.gates.length, (D.output = n + m + g ∨
            (n + m ≤ D.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) D g
              (D.output - (n + m)))) →
            w ∉ (D.gates.getD g ⟨GateOp.and, []⟩).inputs := by
        intro w hw g hg _
        intro hmem
        rw [PEqualNP.Outside.L_meta_19452_aux.gd D hg] at hmem
        have h1 := one_le_readsIn D w hg hmem
        omega
      exact PEqualNP.Outside.L_meta_19452 n m G D u u' hDfan hDrep
        ⟨hout1, key u.val hu⟩ ⟨hout2, key u'.val hu'⟩ c
    -- Two unread columns of `D` agree everywhere in `G`.
    have col_eq : ∀ (v v' : Fin m),
        readsIn D (Finset.range D.size) (n + v.val) = 0 →
        readsIn D (Finset.range D.size) (n + v'.val) = 0 →
        ∀ u : Fin n, G u v = G u v' := by
      intro v v' hv hv' u
      have hout1 : D.output ≠ n + v.val := by omega
      have hout2 : D.output ≠ n + v'.val := by omega
      have key : ∀ (w : ℕ), readsIn D (Finset.range D.size) w = 0 →
          ∀ g < D.gates.length, (D.output = n + m + g ∨
            (n + m ≤ D.output ∧ PEqualNP.EdgeOwnership.InCone (n + m) D g
              (D.output - (n + m)))) →
            w ∉ (D.gates.getD g ⟨GateOp.and, []⟩).inputs := by
        intro w hw g hg _
        intro hmem
        rw [PEqualNP.Outside.L_meta_19452_aux.gd D hg] at hmem
        have h1 := one_le_readsIn D w hg hmem
        omega
      exact PEqualNP.Outside.L_meta_19453 n m G D v v' hDfan hDrep
        ⟨hout1, key (n + v.val) hv⟩ ⟨hout2, key (n + v'.val) hv'⟩ u
    -- At most `a` left wires are unread.
    have hrows : ((Finset.range n).filter
        (fun w => readsIn D (Finset.range D.size) w = 0)).card ≤ a := by
      rw [card_filter_range_eq_fin n (fun w => readsIn D (Finset.range D.size) w = 0)]
      rcases Finset.eq_empty_or_nonempty
        ((Finset.univ : Finset (Fin n)).filter
          (fun u => readsIn D (Finset.range D.size) u.val = 0)) with hE | ⟨r₀, hr₀⟩
      · rw [hE]; simp
      · have hr₀' : readsIn D (Finset.range D.size) r₀.val = 0 := (Finset.mem_filter.mp hr₀).2
        have hsub : (Finset.univ : Finset (Fin n)).filter
            (fun u => readsIn D (Finset.range D.size) u.val = 0) ⊆
            (Finset.univ : Finset (Fin n)).filter (fun t => ∀ c : Fin m, G t c = G r₀ c) := by
          intro u hu
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, fun c => row_eq u r₀ (Finset.mem_filter.mp hu).2 hr₀' c⟩
        exact le_trans (Finset.card_le_card hsub) (hrow r₀)
    -- At most `b` right wires are unread.
    have hcols : (((Finset.range (n + m)).filter (fun w => n ≤ w)).filter
        (fun w => readsIn D (Finset.range D.size) w = 0)).card ≤ b := by
      rw [card_filter_shift n m (fun w => readsIn D (Finset.range D.size) w = 0)]
      rcases Finset.eq_empty_or_nonempty
        ((Finset.univ : Finset (Fin m)).filter
          (fun v => readsIn D (Finset.range D.size) (n + v.val) = 0)) with hE | ⟨r₀, hr₀⟩
      · rw [hE]; simp
      · have hr₀' : readsIn D (Finset.range D.size) (n + r₀.val) = 0 :=
          (Finset.mem_filter.mp hr₀).2
        have hsub : (Finset.univ : Finset (Fin m)).filter
            (fun v => readsIn D (Finset.range D.size) (n + v.val) = 0) ⊆
            (Finset.univ : Finset (Fin m)).filter (fun t => ∀ u : Fin n, G u t = G u r₀) := by
          intro v hv
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, fun u => col_eq v r₀ (Finset.mem_filter.mp hv).2 hr₀' u⟩
        exact le_trans (Finset.card_le_card hsub) (hcol r₀)
    -- The unread wires split into the left and the right ones.
    have hZle : ((Finset.range (n + m)).filter
        (fun w => readsIn D (Finset.range D.size) w = 0)).card ≤ a + b := by
      have hunion : ((Finset.range (n + m)).filter
            (fun w => readsIn D (Finset.range D.size) w = 0))
          = ((Finset.range n).filter (fun w => readsIn D (Finset.range D.size) w = 0)) ∪
            (((Finset.range (n + m)).filter (fun w => n ≤ w)).filter
              (fun w => readsIn D (Finset.range D.size) w = 0)) := by
        ext w
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases hw : w < n
          · exact Or.inl ⟨hw, h2⟩
          · exact Or.inr ⟨⟨h1, by omega⟩, h2⟩
        · rintro (⟨h1, h2⟩ | ⟨⟨h1, _⟩, h2⟩)
          · exact ⟨by omega, h2⟩
          · exact ⟨h1, h2⟩
      have hdisj : Disjoint ((Finset.range n).filter
            (fun w => readsIn D (Finset.range D.size) w = 0))
          (((Finset.range (n + m)).filter (fun w => n ≤ w)).filter
            (fun w => readsIn D (Finset.range D.size) w = 0)) := by
        rw [Finset.disjoint_left]
        intro w hw1 hw2
        simp only [Finset.mem_filter, Finset.mem_range] at hw1 hw2
        omega
      rw [hunion, Finset.card_union_of_disjoint hdisj]
      omega
    -- At least `n + m - a - b` input occurrences.
    have hoccur : n + m - a - b ≤
        ∑ w ∈ Finset.range (n + m), readsIn D (Finset.range D.size) w := by
      have hcard : ((Finset.range (n + m)).filter
            (fun w => ¬ (readsIn D (Finset.range D.size) w = 0))).card
          = (n + m) - ((Finset.range (n + m)).filter
              (fun w => readsIn D (Finset.range D.size) w = 0)).card := by
        have h := Finset.card_filter_add_card_filter_not
          (s := Finset.range (n + m))
          (p := fun w => readsIn D (Finset.range D.size) w = 0)
        have h2 : (Finset.range (n + m)).card = n + m := by simp
        omega
      have hge : ((Finset.range (n + m)).filter
            (fun w => ¬ (readsIn D (Finset.range D.size) w = 0))).card
          ≤ ∑ w ∈ (Finset.range (n + m)).filter
              (fun w => ¬ (readsIn D (Finset.range D.size) w = 0)),
              readsIn D (Finset.range D.size) w := by
        rw [Finset.card_eq_sum_ones]
        refine Finset.sum_le_sum (fun w hw => ?_)
        have hw' : readsIn D (Finset.range D.size) w ≠ 0 := (Finset.mem_filter.mp hw).2
        omega
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (s := Finset.range (n + m))
        (p := fun w => readsIn D (Finset.range D.size) w = 0)
        (f := fun w => readsIn D (Finset.range D.size) w)
      omega
    -- The size accounting: `D` carries no NOT gate.
    obtain ⟨_, heq⟩ := PEqualNP.Outside.L_meta_20813 (n + m) D hshp hrb hpos hlast
    refine ⟨D, ?_, by omega, hDrep⟩
    intro g hg
    rcases hshp g hg with ⟨h1 | h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by simp [h1], by omega⟩
    · exact ⟨by simp [h1], by omega⟩
    · exfalso
      have hnotpos := not_count_pos D ⟨g, hg, h1⟩
      omega
  · -- Zero normal form: `D` has no gate, so it is `Monotone2` vacuously.
    refine ⟨D, ?_, by omega, hDrep⟩
    intro g hg
    have hlen : D.gates.length = 0 := hzero
    rw [List.length_eq_zero_iff.mp hlen] at hg
    simp at hg
