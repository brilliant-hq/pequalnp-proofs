import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1226

/-! ### Part 1: Cut factorization of independent-set count -/

private noncomputable def boundary {N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool) :
    Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun u => side u = false ∧ ∃ v ∈ H u, side v = true)

private def isIndep {N : Nat} (H : Fin N → Finset (Fin N)) (I : Finset (Fin N)) : Prop :=
  ∀ u ∈ I, ∀ v ∈ H u, v ∉ I

private def isLive {m N : Nat} (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool) (f g : Fin m → Bool)
    (I : Finset (Fin N)) : Prop :=
  ∀ v ∈ I, (if side v = true then right g v else left f v) = true

private noncomputable def goodSet {m N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool) (f g : Fin m → Bool) :
    Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun I => isLive side left right f g I ∧ isIndep H I)

private lemma mem_goodSet {m N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool) (f g : Fin m → Bool) (I : Finset (Fin N)) :
    I ∈ goodSet H side left right f g ↔ isLive side left right f g I ∧ isIndep H I := by
  classical simp [goodSet]

private noncomputable def leftSet {m N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left : (Fin m → Bool) → Fin N → Bool) (f : Fin m → Bool) (S : Finset (Fin N)) :
    Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun IL =>
    (∀ v ∈ IL, side v = false ∧ left f v = true) ∧ isIndep H IL ∧ IL ∩ boundary H side = S)

private noncomputable def rightSet {m N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (right : (Fin m → Bool) → Fin N → Bool) (g : Fin m → Bool) (S : Finset (Fin N)) :
    Finset (Finset (Fin N)) := by
  classical
  exact Finset.univ.filter (fun IR =>
    (∀ v ∈ IR, side v = true ∧ right g v = true) ∧ isIndep H IR ∧ ∀ u ∈ S, ∀ v ∈ IR, v ∉ H u)

private lemma fiber_card_eq_mul {m N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool)
    (hsym : ∀ u v, v ∈ H u ↔ u ∈ H v) (f g : Fin m → Bool) (S : Finset (Fin N)) :
    ((goodSet H side left right f g).filter (fun I => I ∩ boundary H side = S)).card =
      (leftSet H side left f S).card * (rightSet H side right g S).card := by
  classical
  rw [← Finset.card_product]
  symm
  refine Finset.card_bij (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_
  · rintro ⟨IL, IR⟩ hp
    simp only [Finset.mem_product, leftSet, rightSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    rcases hp with ⟨⟨hLside, hLind, hLcap⟩, ⟨hRside, hRind, hRno⟩⟩
    simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro v hv
      simp only [Finset.mem_union] at hv
      rcases hv with hvL | hvR
      · have h1 := hLside v hvL; simp [h1.1, h1.2]
      · have h1 := hRside v hvR; simp [h1.1, h1.2]
    · intro u hu v hv hu'
      simp only [Finset.mem_union] at hu hu'
      rcases hu with huL | huR <;> rcases hu' with hvL | hvR
      · exact hLind u huL v hv hvL
      · have huB : u ∈ boundary H side := by
          simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(hLside u huL).1, v, hv, (hRside v hvR).1⟩
        have huS : u ∈ S := by rw [← hLcap]; exact Finset.mem_inter.mpr ⟨huL, huB⟩
        exact hRno u huS v hvR hv
      · have huv : u ∈ H v := (hsym v u).mpr hv
        have hvB : v ∈ boundary H side := by
          simp only [boundary, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨(hLside v hvL).1, u, huv, (hRside u huR).1⟩
        have hvS : v ∈ S := by rw [← hLcap]; exact Finset.mem_inter.mpr ⟨hvL, hvB⟩
        exact hRno v hvS u huR huv
      · exact hRind u huR v hv hvR
    · rw [Finset.union_inter_distrib_right, hLcap]
      have hRempty : IR ∩ boundary H side = ∅ := by
        ext v; simp only [Finset.mem_inter, boundary, Finset.mem_filter, Finset.mem_univ,
          true_and, Finset.notMem_empty, iff_false]
        rintro ⟨hvR, hsf, _⟩
        have hst := (hRside v hvR).1
        rw [hst] at hsf; cases hsf
      rw [hRempty, Finset.union_empty]
  · rintro ⟨IL1, IR1⟩ hp1 ⟨IL2, IR2⟩ hp2 heq
    simp only [Finset.mem_product, leftSet, rightSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp1 hp2
    have hL : IL1 = IL2 := by
      ext v; constructor <;> intro hv
      · have hmem : v ∈ IL2 ∪ IR2 := by rw [← heq]; exact Finset.mem_union_left _ hv
        simp only [Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact h
        · have h1 := (hp1.1.1 v hv).1; have h2 := (hp2.2.1 v h).1; rw [h1] at h2; cases h2
      · have hmem : v ∈ IL1 ∪ IR1 := by rw [heq]; exact Finset.mem_union_left _ hv
        simp only [Finset.mem_union] at hmem
        rcases hmem with h | h
        · exact h
        · have h1 := (hp2.1.1 v hv).1; have h2 := (hp1.2.1 v h).1; rw [h1] at h2; cases h2
    have hR : IR1 = IR2 := by
      ext v; constructor <;> intro hv
      · have hmem : v ∈ IL2 ∪ IR2 := by rw [← heq]; exact Finset.mem_union_right _ hv
        simp only [Finset.mem_union] at hmem
        rcases hmem with h | h
        · have h1 := (hp1.2.1 v hv).1; have h2 := (hp2.1.1 v h).1; rw [h1] at h2; cases h2
        · exact h
      · have hmem : v ∈ IL1 ∪ IR1 := by rw [heq]; exact Finset.mem_union_right _ hv
        simp only [Finset.mem_union] at hmem
        rcases hmem with h | h
        · have h1 := (hp2.2.1 v hv).1; have h2 := (hp1.1.1 v h).1; rw [h1] at h2; cases h2
        · exact h
    exact Prod.ext hL hR
  · intro I hI
    simp only [goodSet, Finset.mem_filter, Finset.mem_univ, true_and] at hI
    rcases hI with ⟨⟨hLive, hInd⟩, hcap⟩
    let IL := I.filter (fun v => side v = false)
    let IR := I.filter (fun v => side v = true)
    refine ⟨(IL, IR), ?_, ?_⟩
    · simp only [Finset.mem_product, leftSet, rightSet, Finset.mem_filter, Finset.mem_univ,
        true_and]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
      · intro v hv; simp only [IL, Finset.mem_filter] at hv
        refine ⟨hv.2, ?_⟩
        have hl := hLive v hv.1; simp [hv.2] at hl; exact hl
      · intro u hu v hv hu'; simp only [IL, Finset.mem_filter] at hu hu'
        exact hInd u hu.1 v hv hu'.1
      · rw [← hcap]; ext v
        simp only [IL, Finset.mem_inter, Finset.mem_filter, boundary, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨⟨hvI, _⟩, hB⟩; exact ⟨hvI, hB⟩
        · rintro ⟨hvI, hsf, hex⟩; exact ⟨⟨hvI, hsf⟩, hsf, hex⟩
      · intro v hv; simp only [IR, Finset.mem_filter] at hv
        refine ⟨hv.2, ?_⟩
        have hl := hLive v hv.1; simp [hv.2] at hl; exact hl
      · intro u hu v hv hu'; simp only [IR, Finset.mem_filter] at hu hu'
        exact hInd u hu.1 v hv hu'.1
      · intro u huS v hvIR hvu
        have huI : u ∈ I := by
          rw [← hcap] at huS; exact (Finset.mem_inter.mp huS).1
        exact hInd u huI v hvu (Finset.mem_filter.mp hvIR).1
    · ext v; simp only [IL, IR, Finset.mem_union, Finset.mem_filter]
      cases side v <;> simp

private lemma goodSet_factor_rat {m t N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool)
    (hsym : ∀ u v, v ∈ H u ↔ u ∈ H v) (hB : (boundary H side).card ≤ t) :
    ∃ (u v : Fin (2 ^ t) → (Fin m → Bool) → ℚ),
      ∀ f g : Fin m → Bool,
        ((goodSet H side left right f g).card : ℚ) = ∑ j : Fin (2 ^ t), u j f * v j g := by
  classical
  let P := (boundary H side).powerset
  have hPcard : P.card = 2 ^ (boundary H side).card := Finset.card_powerset _
  have hP_le : P.card ≤ 2 ^ t := by
    rw [hPcard]; exact Nat.pow_le_pow_right (by omega) hB
  let e : Fin P.card ≃ ↥P := (Fintype.equivFinOfCardEq (Fintype.card_coe P)).symm
  let u : Fin (2 ^ t) → (Fin m → Bool) → ℚ := fun j f =>
    if hj : j.val < P.card then ((leftSet H side left f (e ⟨j.val, hj⟩).val).card : ℚ) else 0
  let v : Fin (2 ^ t) → (Fin m → Bool) → ℚ := fun j g =>
    if hj : j.val < P.card then ((rightSet H side right g (e ⟨j.val, hj⟩).val).card : ℚ) else 0
  refine ⟨u, v, fun f g => ?_⟩
  have hnat : (goodSet H side left right f g).card =
      ∑ S ∈ P, (leftSet H side left f S).card * (rightSet H side right g S).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun I => I ∩ boundary H side) (t := P)
      (fun I _ => Finset.mem_powerset.mpr Finset.inter_subset_right)]
    refine Finset.sum_congr rfl fun S _ => ?_
    exact fiber_card_eq_mul H side left right hsym f g S
  rw [hnat, Nat.cast_sum]
  have hsum_coe :
      (∑ S ∈ P, (((leftSet H side left f S).card * (rightSet H side right g S).card : Nat) : ℚ)) =
      ∑ S : ↥P, ((leftSet H side left f S.val).card : ℚ) * ((rightSet H side right g S.val).card : ℚ) := by
    rw [← Finset.sum_coe_sort P]
    refine Finset.sum_congr rfl fun S _ => ?_
    push_cast; rfl
  rw [hsum_coe]
  rw [← Equiv.sum_comp e]
  symm
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin (2 ^ t) => j.val < P.card)]
  have hzero :
      ∑ j ∈ Finset.univ.filter (fun j : Fin (2 ^ t) => ¬ j.val < P.card), u j f * v j g = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    have hnot : ¬ j.val < P.card := (Finset.mem_filter.mp hj).2
    dsimp only [u, v]
    rw [dif_neg hnot, zero_mul]
  rw [hzero, add_zero]
  refine Finset.sum_bij (fun j hj => (⟨j.val, (Finset.mem_filter.mp hj).2⟩ : Fin P.card))
    (fun _ _ => Finset.mem_univ _)
    (fun a _ b _ h => Fin.ext (congrArg (fun x : Fin P.card => x.val) h))
    (fun k _ => ⟨⟨k.val, lt_of_lt_of_le k.isLt hP_le⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, k.isLt⟩, Fin.ext rfl⟩)
    (fun j hj => ?_)
  have hlt : j.val < P.card := (Finset.mem_filter.mp hj).2
  dsimp only [u, v]
  rw [dite_eq_left hlt, dite_eq_left hlt]

/-! ### Part 2: Exponents set and stars-and-bars count -/

private def Exps (R d : Nat) : Finset (Fin R → Nat) :=
  (Fintype.piFinset fun _ : Fin R => Finset.range (d + 1)).filter (fun α => ∑ j : Fin R, α j ≤ d)

private lemma mem_Exps {R d : Nat} {α : Fin R → Nat} :
    α ∈ Exps R d ↔ ∑ j : Fin R, α j ≤ d := by
  simp only [Exps, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, and_iff_right_iff_imp]
  intro hsum j
  have hle : α j ≤ ∑ i : Fin R, α i :=
    Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

private lemma Exps_mono {R k d : Nat} (hk : k ≤ d) : Exps R k ⊆ Exps R d := by
  intro α hα; rw [mem_Exps] at hα ⊢; omega

private lemma sum_choose_diag (R d : Nat) :
    ∑ k ∈ Finset.range (d + 1), Nat.choose (R + k) k = Nat.choose (R + 1 + d) d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : R + 1 + (d + 1) = (R + d + 1) + 1 := by omega
    have h2 : R + 1 + d = R + d + 1 := by omega
    have h3 : R + (d + 1) = R + d + 1 := by omega
    rw [h1, h2, h3]
    exact (Nat.choose_succ_succ (R + d + 1) d).symm

private lemma card_Exps (R d : Nat) : (Exps R d).card = Nat.choose (R + d) d := by
  induction R generalizing d with
  | zero =>
    have hsub : Exps 0 d = {Fin.elim0} := by
      ext α; simp only [mem_Exps, Finset.univ_eq_empty, Finset.sum_empty, Nat.zero_le,
        Finset.mem_singleton, true_iff]
      funext i; exact Fin.elim0 i
    rw [hsub, Finset.card_singleton, zero_add, Nat.choose_self]
  | succ R ih =>
    have hfib : (Exps (R + 1) d).card =
        ∑ a ∈ Finset.range (d + 1),
          ((Exps (R + 1) d).filter (fun α => α (Fin.last R) = a)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun α : Fin (R + 1) → Nat => α (Fin.last R))
        (t := Finset.range (d + 1))]
      intro α hα
      rw [Finset.mem_coe, mem_Exps] at hα
      have hle : α (Fin.last R) ≤ ∑ j : Fin (R + 1), α j :=
        Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
      rw [Finset.mem_coe, Finset.mem_range]; dsimp only; omega
    rw [hfib]
    have hstep : ∀ a ∈ Finset.range (d + 1),
        ((Exps (R + 1) d).filter (fun α => α (Fin.last R) = a)).card = (Exps R (d - a)).card := by
      intro a ha
      rw [Finset.mem_range] at ha
      refine Finset.card_bij (fun α _ => fun j : Fin R => α j.castSucc) ?_ ?_ ?_
      · intro α hα
        simp only [Finset.mem_filter, mem_Exps] at hα ⊢
        rw [Fin.sum_univ_castSucc, hα.2] at hα
        omega
      · intro α1 hα1 α2 hα2 heq
        simp only [Finset.mem_filter] at hα1 hα2
        funext j
        refine Fin.lastCases ?_ (fun i => congrFun heq i) j
        rw [hα1.2, hα2.2]
      · intro β hβ
        rw [mem_Exps] at hβ
        let α : Fin (R + 1) → Nat := Fin.snoc β a
        refine ⟨α, ?_, ?_⟩
        · simp only [Finset.mem_filter, mem_Exps]
          refine ⟨?_, by simp [α]⟩
          rw [Fin.sum_univ_castSucc]
          simp only [α, Fin.snoc_castSucc, Fin.snoc_last]
          omega
        · funext i; simp [α]
    rw [Finset.sum_congr rfl hstep]
    have hsum_ih : ∑ a ∈ Finset.range (d + 1), (Exps R (d - a)).card =
        ∑ k ∈ Finset.range (d + 1), Nat.choose (R + k) k := by
      refine Finset.sum_bij (fun a _ => d - a)
        (fun a ha => by rw [Finset.mem_range] at ha ⊢; omega)
        (fun a1 ha1 a2 ha2 h => by rw [Finset.mem_range] at ha1 ha2; omega)
        (fun k hk => ⟨d - k, by rw [Finset.mem_range] at hk ⊢; omega, by rw [Finset.mem_range] at hk; omega⟩)
        (fun a _ => ih (d - a))
    rw [hsum_ih, sum_choose_diag]

/-! ### Part 3: Expansion of powers of bilinear sums over `Exps` -/

private lemma pow_sum_mul_expand (R k : Nat) :
    ∃ c : (Fin R → Nat) → ℚ,
      ∀ (a b : Fin R → ℚ),
        (∑ j : Fin R, a j * b j) ^ k =
          ∑ α ∈ Exps R k, c α * (∏ j : Fin R, (a j) ^ (α j)) * (∏ j : Fin R, (b j) ^ (α j)) := by
  induction k with
  | zero =>
    refine ⟨fun _ => 1, fun a b => ?_⟩
    have h0 : Exps R 0 = {fun _ => 0} := by
      ext α; simp only [mem_Exps, Nat.le_zero, Finset.sum_eq_zero_iff, Finset.mem_univ,
        forall_true_left, Finset.mem_singleton]
      exact ⟨fun h => funext h, fun h i => by rw [h]⟩
    rw [h0]; simp
  | succ k ih =>
    rcases ih with ⟨c, hc⟩
    let dec : Fin R → (Fin R → Nat) → (Fin R → Nat) := fun j β => Function.update β j (β j - 1)
    let inc : Fin R → (Fin R → Nat) → (Fin R → Nat) := fun j α => Function.update α j (α j + 1)
    let c' : (Fin R → Nat) → ℚ := fun β =>
      ∑ j : Fin R, if 0 < β j then c (dec j β) else 0
    refine ⟨c', fun a b => ?_⟩
    rw [pow_succ', hc a b, Finset.sum_mul]
    have hterm : ∀ j : Fin R,
        (a j * b j) *
          (∑ α ∈ Exps R k, c α * (∏ i : Fin R, (a i) ^ (α i)) * (∏ i : Fin R, (b i) ^ (α i))) =
        ∑ β ∈ Exps R (k + 1),
          (if 0 < β j then c (dec j β) else 0) *
            (∏ i : Fin R, (a i) ^ (β i)) * (∏ i : Fin R, (b i) ^ (β i)) := by
      intro j
      rw [Finset.mul_sum]
      have hmul : ∀ α ∈ Exps R k,
          (a j * b j) * (c α * (∏ i : Fin R, (a i) ^ (α i)) * (∏ i : Fin R, (b i) ^ (α i))) =
          c α * (∏ i : Fin R, (a i) ^ (inc j α i)) * (∏ i : Fin R, (b i) ^ (inc j α i)) := by
        intro α _
        have hpa : a j * ∏ i : Fin R, (a i) ^ (α i) = ∏ i : Fin R, (a i) ^ (inc j α i) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
          rw [← Finset.mul_prod_erase Finset.univ (fun i => (a i) ^ (inc j α i)) (Finset.mem_univ j)]
          rw [← mul_assoc]
          congr 1
          · simp [inc, pow_succ']
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [inc, (Finset.mem_erase.mp hi).1]
        have hpb : b j * ∏ i : Fin R, (b i) ^ (α i) = ∏ i : Fin R, (b i) ^ (inc j α i) := by
          rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
          rw [← Finset.mul_prod_erase Finset.univ (fun i => (b i) ^ (inc j α i)) (Finset.mem_univ j)]
          rw [← mul_assoc]
          congr 1
          · simp [inc, pow_succ']
          · refine Finset.prod_congr rfl fun i hi => ?_
            simp [inc, (Finset.mem_erase.mp hi).1]
        calc
          (a j * b j) * (c α * (∏ i : Fin R, (a i) ^ (α i)) * (∏ i : Fin R, (b i) ^ (α i)))
              = c α * (a j * ∏ i : Fin R, (a i) ^ (α i)) * (b j * ∏ i : Fin R, (b i) ^ (α i)) := by
                ring
          _ = c α * (∏ i : Fin R, (a i) ^ (inc j α i)) * (∏ i : Fin R, (b i) ^ (inc j α i)) := by
                rw [hpa, hpb]
      rw [Finset.sum_congr rfl hmul]
      rw [← Finset.sum_filter_add_sum_filter_not (Exps R (k + 1)) (fun β => 0 < β j)]
      have hzero :
          ∑ β ∈ (Exps R (k + 1)).filter (fun β => ¬ 0 < β j),
            (if 0 < β j then c (dec j β) else 0) *
              (∏ i : Fin R, (a i) ^ (β i)) * (∏ i : Fin R, (b i) ^ (β i)) = 0 := by
        refine Finset.sum_eq_zero fun β hβ => ?_
        have hn : ¬ 0 < β j := (Finset.mem_filter.mp hβ).2
        simp [hn]
      rw [hzero, add_zero]
      refine Finset.sum_bij (fun α _ => inc j α) ?_ ?_ ?_ ?_
      · intro α hα
        simp only [Finset.mem_filter, mem_Exps] at hα ⊢
        refine ⟨?_, by simp [inc]⟩
        rw [← Finset.add_sum_erase Finset.univ (inc j α) (Finset.mem_univ j)]
        rw [← Finset.add_sum_erase Finset.univ α (Finset.mem_univ j)] at hα
        have hrest : ∑ i ∈ Finset.univ.erase j, inc j α i = ∑ i ∈ Finset.univ.erase j, α i :=
          Finset.sum_congr rfl fun i hi => by simp [inc, (Finset.mem_erase.mp hi).1]
        rw [hrest]; simp only [inc, Function.update_self]; omega
      · intro α1 _ α2 _ heq
        funext i
        by_cases hi : i = j
        · subst hi
          have h := congrFun heq i
          simp only [inc, Function.update_self] at h; omega
        · have h := congrFun heq i
          simpa [inc, hi] using h
      · intro β hβ
        simp only [Finset.mem_filter, mem_Exps] at hβ
        refine ⟨dec j β, ?_, ?_⟩
        · rw [mem_Exps]
          rw [← Finset.add_sum_erase Finset.univ (dec j β) (Finset.mem_univ j)]
          rw [← Finset.add_sum_erase Finset.univ β (Finset.mem_univ j)] at hβ
          have hrest : ∑ i ∈ Finset.univ.erase j, dec j β i = ∑ i ∈ Finset.univ.erase j, β i :=
            Finset.sum_congr rfl fun i hi => by simp [dec, (Finset.mem_erase.mp hi).1]
          rw [hrest]; simp only [dec, Function.update_self]; omega
        · funext i
          by_cases hi : i = j
          · subst hi; simp only [inc, dec, Function.update_self]; omega
          · simp [inc, dec, hi]
      · intro α _
        have hpos : 0 < inc j α j := by simp [inc]
        have hdi : dec j (inc j α) = α := by
          funext i
          by_cases hi : i = j
          · subst hi; simp [dec, inc]
          · simp [dec, inc, hi]
        rw [if_pos hpos, hdi]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    dsimp only [c']
    simp only [Finset.sum_mul]

private lemma poly_eval_sum_mul_expand (R : Nat) (Q : Polynomial ℚ) (d : Nat)
    (hdeg : Q.natDegree ≤ d) :
    ∃ C : (Fin R → Nat) → ℚ,
      ∀ (a b : Fin R → ℚ),
        Q.eval (∑ j : Fin R, a j * b j) =
          ∑ α ∈ Exps R d, C α * (∏ j : Fin R, (a j) ^ (α j)) * (∏ j : Fin R, (b j) ^ (α j)) := by
  classical
  have hck : ∀ k : Nat, ∃ c : (Fin R → Nat) → ℚ,
      ∀ (a b : Fin R → ℚ),
        (∑ j : Fin R, a j * b j) ^ k =
          ∑ α ∈ Exps R k, c α * (∏ j : Fin R, (a j) ^ (α j)) * (∏ j : Fin R, (b j) ^ (α j)) :=
    fun k => pow_sum_mul_expand R k
  choose ck hck using hck
  let C : (Fin R → Nat) → ℚ := fun α =>
    ∑ k ∈ Finset.range (d + 1), if α ∈ Exps R k then Q.coeff k * ck k α else 0
  refine ⟨C, fun a b => ?_⟩
  have heval : Q.eval (∑ j : Fin R, a j * b j) =
      ∑ k ∈ Finset.range (d + 1), Q.coeff k * (∑ j : Fin R, a j * b j) ^ k := by
    rw [Polynomial.eval_eq_sum_range' (lt_of_le_of_lt hdeg (Nat.lt_succ_self d))]
  rw [heval]
  have hrew : ∀ k ∈ Finset.range (d + 1),
      Q.coeff k * (∑ j : Fin R, a j * b j) ^ k =
        ∑ α ∈ Exps R d,
          (if α ∈ Exps R k then Q.coeff k * ck k α else 0) *
            (∏ j : Fin R, (a j) ^ (α j)) * (∏ j : Fin R, (b j) ^ (α j)) := by
    intro k hk
    have hk_le : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [hck k a b, Finset.mul_sum]
    rw [← Finset.sum_subset (Exps_mono hk_le) (fun α _ hnot => by simp [hnot])]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [if_pos hα]; ring
  rw [Finset.sum_congr rfl hrew, Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ => ?_
  dsimp only [C]
  simp only [Finset.sum_mul]

/-! ### Part 4: Walsh-Hadamard orthogonality and rank lower bound -/

private def bitVal {m : Nat} (f g : Fin m → Bool) : Bool :=
  decide (((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1)

private def walsh {m : Nat} (f g : Fin m → Bool) : ℚ :=
  if bitVal f g = true then -1 else 1

private lemma walsh_eq_prod {m : Nat} (f g : Fin m → Bool) :
    walsh f g = ∏ i : Fin m, (if (f i && g i) = true then (-1 : ℚ) else 1) := by
  have h1 : (∏ i : Fin m, (if (f i && g i) = true then (-1 : ℚ) else 1)) =
      (-1 : ℚ) ^ ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [h1]
  set c := ((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card
  have hbit_eq : bitVal f g = decide (c % 2 = 1) := rfl
  dsimp only [walsh]; rw [hbit_eq]
  have hmod : c % 2 = 0 ∨ c % 2 = 1 := by omega
  rcases hmod with h0 | h1
  · have hev : Even c := Nat.even_iff.mpr h0
    have hd : decide (c % 2 = 1) = false := by rw [h0]; rfl
    rw [hd, hev.neg_one_pow]; norm_num
  · have hodd : Odd c := Nat.odd_iff.mpr h1
    have hd : decide (c % 2 = 1) = true := by rw [h1]; rfl
    rw [hd, hodd.neg_one_pow]; norm_num

private lemma walsh_orth {m : Nat} (f h : Fin m → Bool) :
    ∑ g : Fin m → Bool, walsh f g * walsh g h = if f = h then (2 ^ m : ℚ) else 0 := by
  have hterm : ∀ g : Fin m → Bool,
      walsh f g * walsh g h =
        ∏ i : Fin m, (if ((f i != h i) && g i) = true then (-1 : ℚ) else 1) := by
    intro g
    rw [walsh_eq_prod f g, walsh_eq_prod g h, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    cases f i <;> cases g i <;> cases h i <;> norm_num
  simp_rw [hterm]
  rw [← Fintype.prod_sum (fun (i : Fin m) (b : Bool) =>
    if ((f i != h i) && b) = true then (-1 : ℚ) else 1)]
  by_cases hfh : f = h
  · subst hfh
    rw [if_pos rfl]
    have h2 : ∀ i : Fin m,
        ∑ b : Bool, (if ((f i != f i) && b) = true then (-1 : ℚ) else 1) = (2 : ℚ) := by
      intro i; rw [Fintype.sum_bool]; cases f i <;> norm_num
    simp [h2]
  · rw [if_neg hfh]
    have hex : ∃ i : Fin m, f i ≠ h i := by
      by_contra hall; push Not at hall; exact hfh (funext hall)
    rcases hex with ⟨i0, hi0⟩
    refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
    rw [Fintype.sum_bool]
    cases hf : f i0 <;> cases hh : h i0 <;> simp_all

private lemma rank_bound_from_factor {m R : Nat}
    (u v : Fin R → (Fin m → Bool) → ℚ) (P : Polynomial ℚ)
    (hP : ∀ f g, P.eval (∑ j : Fin R, u j f * v j g) = if bitVal f g = true then 1 else 0) :
    2 ^ m ≤ Nat.choose (R + P.natDegree) P.natDegree := by
  let d0 := P.natDegree
  let Q : Polynomial ℚ := Polynomial.C 1 - Polynomial.C 2 * P
  have hQdeg : Q.natDegree ≤ d0 := by
    have h1 : (Polynomial.C (1 : ℚ)).natDegree ≤ d0 := by simp
    have h2 : (Polynomial.C (2 : ℚ) * P).natDegree ≤ d0 :=
      le_trans (Polynomial.natDegree_C_mul_le (2 : ℚ) P) le_rfl
    exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le h1 h2)
  have hQeval : ∀ f g, Q.eval (∑ j : Fin R, u j f * v j g) = walsh f g := by
    intro f g
    simp only [Q, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hP f g, walsh]
    cases bitVal f g <;> norm_num
  rcases poly_eval_sum_mul_expand R Q d0 hQdeg with ⟨C, hC⟩
  let V : ↥(Exps R d0) → (Fin m → Bool) → ℚ := fun α g => ∏ j : Fin R, (v j g) ^ (α.val j)
  let Ψ : (↥(Exps R d0) → ℚ) →ₗ[ℚ] ((Fin m → Bool) → ℚ) :=
    { toFun := fun w g => ∑ α : ↥(Exps R d0), w α * V α g
      map_add' := fun w1 w2 => by
        funext g; dsimp only [Pi.add_apply]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun α _ => add_mul (w1 α) (w2 α) (V α g)
      map_smul' := fun r w => by
        funext g; dsimp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun α _ => mul_assoc r (w α) (V α g) }
  have hsurj : Function.Surjective Ψ := by
    intro ψ
    let φ : (Fin m → Bool) → ℚ := fun f => ((2 ^ m : ℚ)⁻¹) * ∑ h : Fin m → Bool, ψ h * walsh h f
    let w : ↥(Exps R d0) → ℚ := fun α =>
      ∑ f : Fin m → Bool, φ f * C α.val * ∏ j : Fin R, (u j f) ^ (α.val j)
    refine ⟨w, ?_⟩
    funext g
    have h1 : (Ψ w) g = ∑ f : Fin m → Bool, φ f * walsh f g := by
      change (∑ α : ↥(Exps R d0), w α * V α g) = _
      dsimp only [w, V]
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun f _ => ?_
      rw [← hQeval f g, hC (fun j => u j f) (fun j => v j g)]
      rw [← Finset.sum_coe_sort (Exps R d0), Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => by ring
    rw [h1]
    have h2 : ∑ f : Fin m → Bool, φ f * walsh f g =
        ((2 ^ m : ℚ)⁻¹) * ∑ h : Fin m → Bool, ψ h * (∑ f : Fin m → Bool, walsh h f * walsh f g) := by
      dsimp only [φ]
      calc
        ∑ f : Fin m → Bool, (((2 ^ m : ℚ)⁻¹) * ∑ h : Fin m → Bool, ψ h * walsh h f) * walsh f g
            = ((2 ^ m : ℚ)⁻¹) * ∑ f : Fin m → Bool, (∑ h : Fin m → Bool, ψ h * walsh h f) * walsh f g := by
              rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun f _ => by ring
        _ = ((2 ^ m : ℚ)⁻¹) * ∑ f : Fin m → Bool, ∑ h : Fin m → Bool, ψ h * (walsh h f * walsh f g) := by
              congr 1; refine Finset.sum_congr rfl fun f _ => ?_
              rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun h _ => by ring
        _ = ((2 ^ m : ℚ)⁻¹) * ∑ h : Fin m → Bool, ψ h * ∑ f : Fin m → Bool, walsh h f * walsh f g := by
              congr 1; rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun h _ => by rw [Finset.mul_sum]
    rw [h2]
    have hsum : ∑ h : Fin m → Bool, ψ h * (∑ f : Fin m → Bool, walsh h f * walsh f g) =
        ψ g * (2 ^ m : ℚ) := by
      have hrew : ∀ h : Fin m → Bool,
          ψ h * (∑ f : Fin m → Bool, walsh h f * walsh f g) =
            if h = g then ψ g * (2 ^ m : ℚ) else 0 := by
        intro h
        rw [walsh_orth h g]
        split_ifs with hh
        · subst hh; rfl
        · ring
      simp_rw [hrew]
      simp
    rw [hsum]
    have hne : (2 ^ m : ℚ) ≠ 0 := by positivity
    field_simp [hne]
  have hfin : Module.finrank ℚ ((Fin m → Bool) → ℚ) ≤ Module.finrank ℚ (↥(Exps R d0) → ℚ) := by
    have hle := LinearMap.finrank_range_le Ψ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hle
    exact hle
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at hfin
  have hc1 : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
  have hc2 : Fintype.card ↥(Exps R d0) = Nat.choose (R + d0) d0 := by
    rw [Fintype.card_coe, card_Exps]
  rw [hc1, hc2] at hfin
  exact hfin

/-! ### Part 5: Pure arithmetic bound `2^t ≤ m → 2^m ≤ C(2^t + d, d) → m < 4 * d` -/

private lemma choose_four_bound {m t d : Nat}
    (h2t : 2 ^ t ≤ m) (hch : 2 ^ m ≤ Nat.choose (2 ^ t + d) d) : m < 4 * d := by
  by_contra hge
  have h4d : 4 * d ≤ m := by omega
  have hm1 : 1 ≤ m := le_trans Nat.one_le_two_pow h2t
  have hch_m : 2 ^ m ≤ Nat.choose (m + d) d :=
    le_trans hch (Nat.choose_le_choose d (by omega))
  have hbin : Nat.choose (m + d) d * 4 ^ m < 5 ^ (m + d) := by
    have hexp : (1 + 4 : Nat) ^ (m + d) =
        ∑ k ∈ Finset.range (m + d + 1), 1 ^ k * 4 ^ (m + d - k) * Nat.choose (m + d) k := by
      exact add_pow 1 4 (m + d)
    have hsub : ({d, m + d} : Finset Nat) ⊆ Finset.range (m + d + 1) := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rw [Finset.mem_range]; rcases hk with rfl | rfl <;> omega
    have hle := Finset.sum_le_sum_of_subset (f := fun k => 1 ^ k * 4 ^ (m + d - k) * Nat.choose (m + d) k) hsub
    have hne : d ≠ m + d := by omega
    rw [Finset.sum_pair hne] at hle
    have h1 : 1 ^ d * 4 ^ (m + d - d) * Nat.choose (m + d) d = Nat.choose (m + d) d * 4 ^ m := by
      have hsub_eq : m + d - d = m := by omega
      rw [one_pow, one_mul, hsub_eq, mul_comm]
    have h2 : 1 ^ (m + d) * 4 ^ (m + d - (m + d)) * Nat.choose (m + d) (m + d) = 1 := by
      simp
    rw [h1, h2] at hle
    have h5 : (1 + 4 : Nat) ^ (m + d) = 5 ^ (m + d) := rfl
    rw [← hexp, h5] at hle
    omega
  have hlt1 : 2 ^ m * 4 ^ m < 5 ^ (m + d) :=
    lt_of_le_of_lt (Nat.mul_le_mul_right (4 ^ m) hch_m) hbin
  have hlt4 : (2 ^ m * 4 ^ m) ^ 4 < (5 ^ (m + d)) ^ 4 :=
    Nat.pow_lt_pow_left hlt1 (by omega)
  have hlhs : (2 ^ m * 4 ^ m) ^ 4 = 4096 ^ m := by
    calc
      (2 ^ m * 4 ^ m) ^ 4 = ((2 * 4) ^ m) ^ 4 := by rw [← mul_pow]
      _ = 8 ^ (m * 4) := by rw [← pow_mul]
      _ = (8 ^ 4) ^ m := by rw [mul_comm, pow_mul]
      _ = 4096 ^ m := by norm_num
  have hrhs : (5 ^ (m + d)) ^ 4 ≤ 3125 ^ m := by
    calc
      (5 ^ (m + d)) ^ 4 = 5 ^ ((m + d) * 4) := by rw [← pow_mul]
      _ ≤ 5 ^ (5 * m) := Nat.pow_le_pow_right (by omega) (by omega)
      _ = (5 ^ 5) ^ m := by rw [pow_mul]
      _ = 3125 ^ m := by norm_num
  have h4096 : 4096 ^ m < 3125 ^ m := lt_of_lt_of_le (hlhs ▸ hlt4) hrhs
  have h3125 : 3125 ^ m ≤ 4096 ^ m := Nat.pow_le_pow_left (by omega) m
  omega

/-! ### Part 6: Lagrange interpolation over `ℚ` on a finite `Nat` image -/

private lemma exists_interp_poly {m : Nat} (val : (Fin m → Bool) → (Fin m → Bool) → Nat)
    (decode : Nat → Bool) :
    ∃ P : Polynomial ℚ,
      ∀ f g : Fin m → Bool,
        P.eval (val f g : ℚ) = if decode (val f g) = true then (1 : ℚ) else 0 := by
  classical
  let S : Finset Nat :=
    (Finset.univ : Finset ((Fin m → Bool) × (Fin m → Bool))).image (fun p => val p.1 p.2)
  let L : Nat → Polynomial ℚ := fun a =>
    ∏ b ∈ S.erase a,
      Polynomial.C (((a : ℚ) - (b : ℚ))⁻¹) * (Polynomial.X - Polynomial.C (b : ℚ))
  let P : Polynomial ℚ :=
    ∑ a ∈ S, Polynomial.C (if decode a = true then (1 : ℚ) else 0) * L a
  refine ⟨P, fun f g => ?_⟩
  set k := val f g
  have hkS : k ∈ S := Finset.mem_image.mpr ⟨(f, g), Finset.mem_univ _, rfl⟩
  dsimp only [P]
  change (Polynomial.evalRingHom (k : ℚ))
      (∑ a ∈ S, Polynomial.C (if decode a = true then (1 : ℚ) else 0) * L a) = _
  rw [map_sum]
  have hterm : ∀ a ∈ S,
      (Polynomial.evalRingHom (k : ℚ))
        (Polynomial.C (if decode a = true then (1 : ℚ) else 0) * L a) =
        if a = k then (if decode k = true then (1 : ℚ) else 0) else 0 := by
    intro a haS
    change (Polynomial.C (if decode a = true then (1 : ℚ) else 0) * L a).eval (k : ℚ) = _
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hak : a = k
    · subst hak
      rw [if_pos rfl]
      have hLk : (L k).eval (k : ℚ) = 1 := by
        dsimp only [L]
        rw [Polynomial.eval_prod]
        refine Finset.prod_eq_one fun b hb => ?_
        have hbk : b ≠ k := (Finset.mem_erase.mp hb).1
        have hne : (k : ℚ) - (b : ℚ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hbk.symm)
        rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          Polynomial.eval_C, inv_mul_cancel₀ hne]
      rw [hLk, mul_one]
    · rw [if_neg hak]
      have hLa : (L a).eval (k : ℚ) = 0 := by
        dsimp only [L]
        rw [Polynomial.eval_prod]
        refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hak, hkS⟩) ?_
        simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      rw [hLa, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  simp [hkS]

/-! ### Main Body (clean context without `letI`) and Final Bridge -/

private def exactProp {m N : Nat} (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool) (P : Polynomial ℚ) : Prop :=
  ∀ f g : Fin m → Bool,
    P.eval ((goodSet H side left right f g).card : ℚ) =
      if bitVal f g = true then (1 : ℚ) else 0

private lemma main_body (m t N : Nat) (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
    (left right : (Fin m → Bool) → Fin N → Bool)
    (hsym : ∀ u v, v ∈ H u ↔ u ∈ H v)
    (hB : (boundary H side).card ≤ t) :
    let tot := fun f g => (goodSet H side left right f g).card
    ((∃ decode : Nat → Bool, ∀ f g, decode (tot f g) = bitVal f g) ↔
      ∃ P : Polynomial ℚ, exactProp H side left right P) ∧
    ∀ P : Polynomial ℚ, exactProp H side left right P →
      2 ^ m ≤ Nat.choose (2 ^ t + P.natDegree) P.natDegree ∧
      (2 ^ t ≤ m → m < 4 * P.natDegree) := by
  intro tot
  constructor
  · constructor
    · rintro ⟨decode, hdec⟩
      rcases exists_interp_poly tot decode with ⟨P, hP⟩
      refine ⟨P, fun f g => ?_⟩
      rw [hP f g, hdec f g]
    · rintro ⟨P, hP⟩
      refine ⟨fun k => decide (P.eval (k : ℚ) = 1), fun f g => ?_⟩
      dsimp only
      rw [hP f g]
      cases bitVal f g <;> norm_num
  · intro P hP
    rcases goodSet_factor_rat H side left right hsym hB with ⟨u, v, huv⟩
    have hP' : ∀ f g, P.eval (∑ j : Fin (2 ^ t), u j f * v j g) =
        if bitVal f g = true then (1 : ℚ) else 0 := by
      intro f g; rw [← huv f g]; exact hP f g
    have hrank : 2 ^ m ≤ Nat.choose (2 ^ t + P.natDegree) P.natDegree :=
      rank_bound_from_factor u v P hP'
    exact ⟨hrank, fun h2t => choose_four_bound h2t hrank⟩

theorem main_proof :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ (m t N : Nat) (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
      (left right : (Fin m → Bool) → Fin N → Bool),
      (∀ u, u ∉ H u) → (∀ u v, v ∈ H u ↔ u ∈ H v) →
      ((Finset.univ : Finset (Fin N)).filter (fun u =>
        side u = false ∧ ∃ v ∈ H u, side v = true)).card ≤ t →
      let total := fun (f g : Fin m → Bool) =>
        ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
          (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
          ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
      let bit := fun (f g : Fin m → Bool) =>
        decide (((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1)
      let exact := fun (P : Polynomial ℚ) => ∀ f g, P.eval (total f g : ℚ) =
        (if bit f g then (1 : ℚ) else 0)
      ((∃ decode : Nat → Bool, ∀ f g, decode (total f g) = bit f g) ↔
        ∃ P : Polynomial ℚ, exact P) ∧
      ∀ P : Polynomial ℚ, exact P →
        2^m ≤ Nat.choose (2^t + P.natDegree) P.natDegree ∧
        (2^t ≤ m → m < 4*P.natDegree) := by
  let _ : ∀ p : Prop, Decidable p := Classical.propDecidable
  intro m t N H side left right _hirr hsym hB_stmt total bit exact
  have hB : (boundary H side).card ≤ t := by
    have heq : (boundary H side) =
        (Finset.univ : Finset (Fin N)).filter (fun u => side u = false ∧ ∃ v ∈ H u, side v = true) := by
      ext u; simp [boundary]
    rw [heq]; exact hB_stmt
  have htot : ∀ f g, total f g = (goodSet H side left right f g).card := by
    intro f g
    dsimp only [total]
    congr 1
    ext I
    rw [Finset.mem_filter, mem_goodSet]
    simp only [Finset.mem_univ, true_and, isLive, isIndep]
    constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun v hv => ?_, h2⟩
    · have h1v := h1 v hv
      by_cases hs : side v = true
      · simp only [hs, ↓reduceIte] at h1v ⊢; exact h1v
      · simp only [hs, ↓reduceIte] at h1v ⊢; exact h1v
    · have h1v := h1 v hv
      by_cases hs : side v = true
      · simp only [hs, ↓reduceIte] at h1v ⊢; exact h1v
      · simp only [hs, ↓reduceIte] at h1v ⊢; exact h1v
  have hbit : ∀ f g, bit f g = bitVal f g := by
    intro f g
    dsimp only [bit, bitVal]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    apply iff_of_eq
    congr 3
    ext i
    simp only [Finset.mem_filter]
  have hexact : ∀ P : Polynomial ℚ, exact P ↔ exactProp H side left right P := by
    intro P
    dsimp only [exact, exactProp]
    constructor <;> intro hP f g
    · have h := hP f g; rw [htot f g, hbit f g] at h
      by_cases hb : bitVal f g = true
      · simp only [hb, ↓reduceIte] at h ⊢; exact h
      · simp only [hb] at h ⊢; exact h
    · have h := hP f g; rw [htot f g, hbit f g]
      by_cases hb : bitVal f g = true
      · simp only [hb, ↓reduceIte] at h ⊢; exact h
      · simp only [hb] at h ⊢; exact h
  have hres := main_body m t N H side left right hsym hB
  dsimp only at hres
  constructor
  · constructor
    · rintro ⟨decode, hdec⟩
      have hdec' : ∀ f g, decode (goodSet H side left right f g).card = bitVal f g := by
        intro f g; rw [← htot f g, ← hbit f g]; exact hdec f g
      rcases hres.1.mp ⟨decode, hdec'⟩ with ⟨P, hP⟩
      exact ⟨P, (hexact P).mpr hP⟩
    · rintro ⟨P, hP⟩
      rcases hres.1.mpr ⟨P, (hexact P).mp hP⟩ with ⟨decode, hdec⟩
      exact ⟨decode, fun f g => by rw [htot f g, hbit f g]; exact hdec f g⟩
  · intro P hP
    exact hres.2 P ((hexact P).mp hP)

end PEqualNP.Outside.L_lib_1226

theorem PEqualNP.Outside.L_lib_1226 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ (m t N : Nat) (H : Fin N → Finset (Fin N)) (side : Fin N → Bool)
  (left right : (Fin m → Bool) → Fin N → Bool),
  (∀ u, u ∉ H u) → (∀ u v, v ∈ H u ↔ u ∈ H v) →
  ((Finset.univ : Finset (Fin N)).filter (fun u =>
    side u = false ∧ ∃ v ∈ H u, side v = true)).card ≤ t →
  let total := fun (f g : Fin m → Bool) =>
    ((Finset.univ : Finset (Finset (Fin N))).filter (fun I =>
      (∀ v ∈ I, (if side v then right g v else left f v) = true) ∧
      ∀ u ∈ I, ∀ v ∈ H u, v ∉ I)).card
  let bit := fun (f g : Fin m → Bool) =>
    decide (((Finset.univ : Finset (Fin m)).filter (fun i => f i && g i)).card % 2 = 1)
  let exact := fun (P : Polynomial ℚ) => ∀ f g, P.eval (total f g : ℚ) =
    (if bit f g then (1 : ℚ) else 0)
  ((∃ decode : Nat → Bool, ∀ f g, decode (total f g) = bit f g) ↔
    ∃ P : Polynomial ℚ, exact P) ∧
  ∀ P : Polynomial ℚ, exact P →
    2^m ≤ Nat.choose (2^t + P.natDegree) P.natDegree ∧
    (2^t ≤ m → m < 4*P.natDegree) :=
  PEqualNP.Outside.L_lib_1226.main_proof
