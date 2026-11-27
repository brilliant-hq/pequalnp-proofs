import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_584_aux

abbrev V (m r : Nat) := Fin m × Fin r
abbrev W (m r : Nat) := V m r → Bool

def b2z (b : Bool) : ZMod 2 := if b then 1 else 0

def monEval {m r : Nat} (M : Finset (V m r)) (x : W m r) : ZMod 2 :=
  if ∀ v ∈ M, x v = true then 1 else 0

theorem monEval_mul {m r : Nat} (M N : Finset (V m r)) (x : W m r) :
    monEval M x * monEval N x = monEval (M ∪ N) x := by
  unfold monEval
  split_ifs with hM hN hMN
  · exact mul_one 1
  · exfalso; apply hMN; intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact hM v h
    · exact hN v h
  · exfalso; exact hN (fun v hv => ‹∀ v ∈ M ∪ N, x v = true› v (Finset.mem_union_right M hv))
  · exact mul_zero 1
  · exfalso; exact hM (fun v hv => ‹∀ v ∈ M ∪ N, x v = true› v (Finset.mem_union_left N hv))
  · exact zero_mul 1
  · exfalso; exact hM (fun v hv => ‹∀ v ∈ M ∪ N, x v = true› v (Finset.mem_union_left N hv))
  · exact zero_mul 0

theorem par_eq_b2z (z : Nat) : b2z (z % 2 == 1) = (z : ZMod 2) := by
  have hdiv : z = 2 * (z / 2) + z % 2 := (Nat.div_add_mod z 2).symm
  have hcast : (z : ZMod 2) = (2 : ZMod 2) * ((z / 2 : Nat) : ZMod 2) + ((z % 2 : Nat) : ZMod 2) := by
    conv_lhs => rw [hdiv]
    push_cast
    rfl
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [hcast, h2, zero_mul, zero_add]
  rcases Nat.mod_two_eq_zero_or_one z with h | h
  · simp [b2z, h]
  · simp [b2z, h]

theorem sum_monEval {m r : Nat} (terms : Finset (Finset (V m r))) (x : W m r) :
    (∑ M ∈ terms, monEval M x) =
      b2z ((terms.filter (fun mon => ∀ j ∈ mon, x j = true)).card % 2 == 1) := by
  rw [par_eq_b2z]
  unfold monEval
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]

def blockVars {m r : Nat} (I : Finset (Fin m)) : Finset (V m r) :=
  I.biUnion (fun i => Finset.univ.image (fun j : Fin r => (i, j)))

theorem mem_blockVars {m r : Nat} {I : Finset (Fin m)} {v : V m r} :
    v ∈ blockVars I ↔ v.1 ∈ I := by
  rcases v with ⟨i, j⟩
  simp [blockVars]

theorem card_blockVars {m r : Nat} (I : Finset (Fin m)) :
    (blockVars (r := r) I).card = r * I.card := by
  unfold blockVars
  rw [Finset.card_biUnion]
  · have hinj : ∀ i : Fin m, Function.Injective (fun j : Fin r => (i, j)) :=
      fun _ _ _ h => (Prod.mk.inj h).2
    simp only [Finset.card_image_of_injective _ (hinj _),
      Finset.card_univ, Fintype.card_fin, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  · intro i1 _ i2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hv1 hv2
    rcases hv1 with ⟨j1, rfl⟩
    rcases hv2 with ⟨j2, h2⟩
    exact hne (Prod.mk.inj h2).1.symm

theorem monEval_blockVars {m r : Nat} (I : Finset (Fin m)) (x : W m r) :
    monEval (blockVars I) x = b2z (decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true)) := by
  unfold monEval b2z
  split_ifs with h1 h2 h2
  · rfl
  · exfalso
    apply h2
    rw [decide_eq_true_iff]
    intro i hi j
    exact h1 (i, j) (mem_blockVars.mpr hi)
  · exfalso
    apply h1
    rw [decide_eq_true_iff] at h2
    intro v hv
    rcases v with ⟨i, j⟩
    exact h2 i (mem_blockVars.mp hv) j
  · rfl

def fullBlocks {m r : Nat} (x : W m r) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∀ j : Fin r, x (i, j) = true)

def fullBlocksM {m r : Nat} (M : Finset (V m r)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => ∀ j : Fin r, (i, j) ∈ M)

def goodMons (m r k : Nat) : Finset (Finset (V m r)) :=
  Finset.univ.filter (fun M => (fullBlocksM M).card < k)

def extremalSet (m r k : Nat) : Finset (W m r) :=
  Finset.univ.filter (fun sample => (fullBlocks sample).card < k)

theorem card_goodMons_eq_extremal (m r k : Nat) :
    (goodMons m r k).card = (extremalSet m r k).card := by
  refine Finset.card_bij (fun M _ => fun v => decide (v ∈ M)) ?_ ?_ ?_
  · intro M hM
    simp only [goodMons, extremalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hM ⊢
    have hfb : fullBlocks (fun v => decide (v ∈ M)) = fullBlocksM M := by
      ext i; simp [fullBlocks, fullBlocksM]
    rw [hfb]
    exact hM
  · intro M1 _ M2 _ heq
    ext v
    have hv := congrFun heq v
    simpa using hv
  · intro x hx
    refine ⟨Finset.univ.filter (fun v => x v = true), ?_, ?_⟩
    · simp only [goodMons, extremalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hfb : fullBlocksM (Finset.univ.filter (fun v => x v = true)) = fullBlocks x := by
        ext i; simp [fullBlocks, fullBlocksM]
      rw [hfb]
      exact hx
    · funext v
      simp

theorem card_nonfull_row (r : Nat) :
    Fintype.card {f : Fin r → Bool // ¬ ∀ j : Fin r, f j = true} = 2 ^ r - 1 := by
  rw [Fintype.card_subtype_compl]
  have htot : Fintype.card (Fin r → Bool) = 2 ^ r := by simp
  have h1 : Fintype.card {f : Fin r → Bool // ∀ j : Fin r, f j = true} = 1 := by
    refine Fintype.card_eq_one_iff.mpr ⟨⟨fun _ => true, fun _ => rfl⟩, ?_⟩
    rintro ⟨f, hf⟩
    ext j
    exact hf j
  rw [htot, h1]

theorem card_fiber_fullBlocks {m r : Nat} (J : Finset (Fin m)) :
    ((Finset.univ : Finset (W m r)).filter (fun x => fullBlocks x = J)).card =
      (2 ^ r - 1) ^ (m - J.card) := by
  rw [← Fintype.card_coe]
  let e : {x : W m r // x ∈ (Finset.univ : Finset (W m r)).filter (fun x => fullBlocks x = J)} ≃
      ((i : {i : Fin m // i ∉ J}) → {f : Fin r → Bool // ¬ ∀ j : Fin r, f j = true}) :=
    { toFun := fun ⟨x, hx⟩ ⟨i, hi⟩ =>
        ⟨fun j => x (i, j), by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
          intro hall
          apply hi
          rw [← hx]
          simp [fullBlocks, hall]⟩
      invFun := fun g =>
        ⟨fun v => if hv : v.1 ∈ J then true else (g ⟨v.1, hv⟩).1 v.2, by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          ext i
          simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
          by_cases hi : i ∈ J
          · simp [hi]
          · simp [hi, (g ⟨i, hi⟩).2]⟩
      left_inv := by
        rintro ⟨x, hx⟩
        ext ⟨i, j⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        by_cases hi : i ∈ J
        · simp only [hi, ↓reduceDIte]
          have hmem : i ∈ fullBlocks x := by rw [hx]; exact hi
          simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
          exact (hmem j).symm
        · simp [hi]
      right_inv := by
        intro g
        funext ⟨i, hi⟩
        ext j
        simp [hi] }
  rw [Fintype.card_congr e, Fintype.card_pi]
  simp only [card_nonfull_row, Finset.prod_const, Finset.card_univ]
  have hcomp : Fintype.card {i : Fin m // i ∉ J} = m - J.card := by
    rw [Fintype.card_subtype_compl]
    simp [Fintype.card_coe]
  rw [hcomp]

theorem extremal_card_eq_budget (m r k : Nat) :
    (extremalSet m r k).card =
      (Finset.range (m + 1)).sum (fun j =>
        if j < k then Nat.choose m j * (2 ^ r - 1) ^ (m - j) else 0) := by
  have hpart : (extremalSet m r k).card =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k),
        ((Finset.univ : Finset (W m r)).filter (fun x => fullBlocks x = J)).card := by
    have hmap : ∀ x ∈ extremalSet m r k,
        fullBlocks x ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k) := by
      intro x hx
      simp only [extremalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hx
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    refine Finset.sum_congr rfl fun J hJ => ?_
    congr 1
    ext x
    simp only [extremalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hJ ⊢
    constructor
    · intro h; exact h.2
    · intro h; exact ⟨by rw [h]; exact hJ, h⟩
  rw [hpart]
  have hrew :
      (∑ J ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k),
        ((Finset.univ : Finset (W m r)).filter (fun x => fullBlocks x = J)).card) =
      ∑ J ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k),
        (2 ^ r - 1) ^ (m - J.card) :=
    Finset.sum_congr rfl fun J _ => card_fiber_fullBlocks J
  rw [hrew]
  have hmap2 : ∀ J ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k),
      J.card ∈ Finset.range (m + 1) := by
    intro J _
    rw [Finset.mem_range]
    have hle : J.card ≤ m := by
      simpa using Finset.card_le_univ J
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmap2]
  refine Finset.sum_congr rfl fun j hj => ?_
  by_cases hjk : j < k
  · simp only [hjk, ↓reduceIte]
    have hset : ((Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k)).filter
        (fun J => J.card = j) = Finset.powersetCard j (Finset.univ : Finset (Fin m)) := by
      ext J
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard,
        Finset.subset_univ]
      constructor
      · intro h; exact h.2
      · intro h; exact ⟨by omega, h⟩
    rw [hset]
    have hconst : ∀ J ∈ Finset.powersetCard j (Finset.univ : Finset (Fin m)),
        (2 ^ r - 1) ^ (m - J.card) = (2 ^ r - 1) ^ (m - j) := by
      intro J hJ
      rw [(Finset.mem_powersetCard.mp hJ).2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin]
  · simp only [hjk, ↓reduceIte]
    have hemp : ((Finset.univ : Finset (Finset (Fin m))).filter (fun J => J.card < k)).filter
        (fun J => J.card = j) = ∅ := by
      ext J
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨h1, h2⟩
      omega
    rw [hemp, Finset.sum_empty]

theorem lowers_extremal (m r k : Nat) :
    ∀ I : Finset (Fin m), I.card = k →
      ∃ q : W m r → Bool,
        (∃ terms : Finset (Finset (V m r)), (∀ mon ∈ terms, mon.card ≤ r * k - 1) ∧
          ∀ word, q word = ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2 == 1)) ∧
        ∀ x ∈ extremalSet m r k, q x = decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true) := by
  intro I hI
  refine ⟨fun _ => false, ⟨∅, by simp, fun _ => rfl⟩, ?_⟩
  intro x hx
  simp only [extremalSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  symm
  rw [decide_eq_false_iff_not]
  intro hall
  have hsub : I ⊆ fullBlocks x := by
    intro i hi
    simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hall i hi
  have hle : I.card ≤ (fullBlocks x).card := Finset.card_le_card hsub
  omega

theorem card_le_budget {m r k : Nat} (hr : 0 < r) (hk : 0 < k) (S : Finset (W m r))
    (hlow : ∀ I : Finset (Fin m), I.card = k →
      ∃ q : W m r → Bool,
        (∃ terms : Finset (Finset (V m r)), (∀ mon ∈ terms, mon.card ≤ r * k - 1) ∧
          ∀ word, q word = ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card % 2 == 1)) ∧
        ∀ x ∈ S, q x = decide (∀ i ∈ I, ∀ j : Fin r, x (i, j) = true)) :
    S.card ≤ (Finset.range (m + 1)).sum (fun j =>
      if j < k then Nat.choose m j * (2 ^ r - 1) ^ (m - j) else 0) := by
  let vecOf : Finset (V m r) → (S → ZMod 2) := fun M x => monEval M x.1
  let G_set : Finset (S → ZMod 2) := (goodMons m r k).image vecOf
  let G_span : Submodule (ZMod 2) (S → ZMod 2) := Submodule.span (ZMod 2) (G_set : Set (S → ZMod 2))
  have hmem_G : ∀ n : Nat, ∀ M : Finset (V m r), M.card = n → vecOf M ∈ G_span := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro M hMcard
      by_cases hgood : (fullBlocksM M).card < k
      · apply Submodule.subset_span
        simp only [G_set, Finset.coe_image, Set.mem_image, Finset.mem_coe]
        exact ⟨M, by simp [goodMons, hgood], rfl⟩
      · have hge : k ≤ (fullBlocksM M).card := Nat.le_of_not_lt hgood
        obtain ⟨I, hIsub, hIcard⟩ := Finset.exists_subset_card_eq hge
        obtain ⟨q, ⟨terms, hdeg, hqpar⟩, hqS⟩ := hlow I hIcard
        have hBsub : blockVars (r := r) I ⊆ M := by
          intro v hv
          rcases v with ⟨i, j⟩
          have hi : i ∈ fullBlocksM M := hIsub (mem_blockVars.mp hv)
          simp only [fullBlocksM, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact hi j
        let R : Finset (V m r) := M \ blockVars (r := r) I
        have hMR : blockVars (r := r) I ∪ R = M := Finset.union_sdiff_of_subset hBsub
        have hdisj : Disjoint (blockVars (r := r) I) R := Finset.disjoint_sdiff
        have hcard_eq : M.card = r * k + R.card := by
          rw [← hMR, Finset.card_union_of_disjoint hdisj, card_blockVars, hIcard]
        have hveq : vecOf M = ∑ mon ∈ terms, vecOf (mon ∪ R) := by
          funext x
          simp only [vecOf, Finset.sum_apply]
          have h1 : monEval M x.1 = monEval (blockVars (r := r) I) x.1 * monEval R x.1 := by
            rw [monEval_mul, hMR]
          rw [h1, monEval_blockVars, ← hqS x.1 x.2, hqpar x.1, ← sum_monEval, Finset.sum_mul]
          refine Finset.sum_congr rfl fun mon _ => ?_
          exact monEval_mul mon R x.1
        rw [hveq]
        refine Submodule.sum_mem G_span fun mon hmon => ?_
        have hlt : (mon ∪ R).card < n := by
          have h1 : (mon ∪ R).card ≤ mon.card + R.card := Finset.card_union_le mon R
          have h2 : mon.card ≤ r * k - 1 := hdeg mon hmon
          have hrk : 0 < r * k := Nat.mul_pos hr hk
          omega
        exact ih (mon ∪ R).card hlt (mon ∪ R) rfl
  let AllSpan : Submodule (ZMod 2) (S → ZMod 2) :=
    Submodule.span (ZMod 2) (Set.range vecOf)
  have hAll_le : AllSpan ≤ G_span := by
    rw [Submodule.span_le]
    rintro _ ⟨M, rfl⟩
    exact hmem_G M.card M rfl
  have hmul_closed : ∀ (v : V m r) (f : S → ZMod 2), f ∈ AllSpan →
      (fun x : S => monEval {v} x.1 * f x) ∈ AllSpan := by
    intro v f hf
    refine Submodule.span_induction (p := fun f _ => (fun x : S => monEval {v} x.1 * f x) ∈ AllSpan)
      ?_ ?_ ?_ ?_ hf
    · rintro _ ⟨M, rfl⟩
      have heq : (fun x : S => monEval {v} x.1 * vecOf M x) = vecOf ({v} ∪ M) := by
        funext x; exact monEval_mul {v} M x.1
      rw [heq]
      exact Submodule.subset_span ⟨{v} ∪ M, rfl⟩
    · have heq : (fun x : S => monEval {v} x.1 * (0 : S → ZMod 2) x) = 0 := by
        funext x; simp
      rw [heq]
      exact AllSpan.zero_mem
    · intro f1 f2 _ _ hf1 hf2
      have heq : (fun x : S => monEval {v} x.1 * (f1 + f2) x) =
          (fun x : S => monEval {v} x.1 * f1 x) + (fun x : S => monEval {v} x.1 * f2 x) := by
        funext x; simp [mul_add]
      rw [heq]
      exact AllSpan.add_mem hf1 hf2
    · intro c f1 _ hf1
      have heq : (fun x : S => monEval {v} x.1 * (c • f1) x) =
          c • (fun x : S => monEval {v} x.1 * f1 x) := by
        funext x; simp [Pi.smul_apply, smul_eq_mul]; ring
      rw [heq]
      exact AllSpan.smul_mem c hf1
  have hprod_mem : ∀ (x0 : S) (U : Finset (V m r)),
      (fun x : S => ∏ v ∈ U, (if x0.1 v = true then monEval {v} x.1 else 1 - monEval {v} x.1)) ∈ AllSpan := by
    intro x0 U
    induction U using Finset.induction_on with
    | empty =>
      have heq : (fun x : S => ∏ v ∈ (∅ : Finset (V m r)),
            (if x0.1 v = true then monEval {v} x.1 else 1 - monEval {v} x.1)) = vecOf ∅ := by
        funext x; simp [vecOf, monEval]
      rw [heq]
      exact Submodule.subset_span ⟨∅, rfl⟩
    | @insert v U hv ih =>
      have hstep : (fun x : S => ∏ u ∈ insert v U,
            (if x0.1 u = true then monEval {u} x.1 else 1 - monEval {u} x.1)) =
          (fun x : S => (if x0.1 v = true then monEval {v} x.1 else 1 - monEval {v} x.1) *
            ∏ u ∈ U, (if x0.1 u = true then monEval {u} x.1 else 1 - monEval {u} x.1)) := by
        funext x
        exact Finset.prod_insert hv
      rw [hstep]
      by_cases hx0v : x0.1 v = true
      · simp only [hx0v, ite_true]
        exact hmul_closed v _ ih
      · have hsub : (fun x : S => (if x0.1 v = true then monEval {v} x.1 else 1 - monEval {v} x.1) *
              ∏ u ∈ U, (if x0.1 u = true then monEval {u} x.1 else 1 - monEval {u} x.1)) =
            (fun x : S => ∏ u ∈ U, (if x0.1 u = true then monEval {u} x.1 else 1 - monEval {u} x.1)) -
            (fun x : S => monEval {v} x.1 *
              ∏ u ∈ U, (if x0.1 u = true then monEval {u} x.1 else 1 - monEval {u} x.1)) := by
          funext x; simp [hx0v, sub_mul]
        rw [hsub]
        exact AllSpan.sub_mem ih (hmul_closed v _ ih)
  have hsingle_mem : ∀ x0 : S, Pi.single x0 (1 : ZMod 2) ∈ G_span := by
    intro x0
    have heq : Pi.single x0 (1 : ZMod 2) =
        (fun x : S => ∏ v ∈ (Finset.univ : Finset (V m r)),
          (if x0.1 v = true then monEval {v} x.1 else 1 - monEval {v} x.1)) := by
      funext x
      by_cases hxx : x = x0
      · subst hxx
        simp only [Pi.single_eq_same]
        symm
        apply Finset.prod_eq_one
        intro v _
        by_cases hv : x.1 v = true
        · simp [hv, monEval]
        · simp [hv, monEval]
      · simp only [Pi.single_eq_of_ne hxx]
        have hne : x.1 ≠ x0.1 := fun h => hxx (Subtype.ext h)
        have hex : ∃ v : V m r, x.1 v ≠ x0.1 v := by
          by_contra hall
          push Not at hall
          exact hne (funext hall)
        rcases hex with ⟨v, hv⟩
        symm
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        cases hx1 : x.1 v <;> cases hx0 : x0.1 v
        · exact absurd (hx1.trans hx0.symm) hv
        · simp [monEval, hx1]
        · simp [monEval, hx1]
        · exact absurd (hx1.trans hx0.symm) hv
    rw [heq]
    exact hAll_le (hprod_mem x0 Finset.univ)
  have htop : G_span = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hf : f = ∑ x0 : S, f x0 • Pi.single x0 (1 : ZMod 2) := by
      funext x
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hf]
    exact Submodule.sum_mem G_span fun x0 _ => Submodule.smul_mem G_span (f x0) (hsingle_mem x0)
  have hdim1 : S.card = Module.finrank (ZMod 2) G_span := by
    rw [htop, finrank_top, Module.finrank_pi, Fintype.card_coe]
  have hdim2 : Module.finrank (ZMod 2) G_span ≤ G_set.card := by
    simpa [G_span] using finrank_span_le_card (G_set : Set (S → ZMod 2))
  have hcard1 : G_set.card ≤ (goodMons m r k).card := Finset.card_image_le
  rw [hdim1, ← extremal_card_eq_budget, ← card_goodMons_eq_extremal]
  exact hdim2.trans hcard1

end PEqualNP.Outside.L_lib_584_aux

theorem PEqualNP.Outside.L_lib_584 : ∀ (m r k : Nat), 0 < r → 0 < k →
  let V := Fin m × Fin r
  let W := V → Bool
  let par := fun (z : Nat) => z % 2 == 1
  let deg := fun (u : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ u) ∧
      ∀ word, f word = par ((terms.filter (fun mon => ∀ j ∈ mon, word j = true)).card)
  let productOn := fun (I : Finset (Fin m)) (x : W) =>
    decide (∀ i ∈ I, ∀ j : Fin r, x (i,j) = true)
  let budget := (Finset.range (m+1)).sum (fun j =>
    if j < k then Nat.choose m j * (2^r-1)^(m-j) else 0)
  let lowers := fun (S : Finset W) => ∀ I : Finset (Fin m), I.card = k →
    ∃ q : W → Bool, deg (r*k-1) q ∧ ∀ x ∈ S, q x = productOn I x
  (∀ S : Finset W, lowers S → S.card ≤ budget) ∧
  let extremal := (Finset.univ : Finset W).filter (fun sample =>
    ((Finset.univ : Finset (Fin m)).filter (fun i => ∀ j : Fin r, sample (i,j) = true)).card < k)
  lowers extremal ∧ extremal.card = budget := by
  intro m r k hr hk
  dsimp only
  exact ⟨fun S hS => PEqualNP.Outside.L_lib_584_aux.card_le_budget hr hk S hS,
    PEqualNP.Outside.L_lib_584_aux.lowers_extremal m r k,
    PEqualNP.Outside.L_lib_584_aux.extremal_card_eq_budget m r k⟩
