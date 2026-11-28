import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1132

def ind {α : Type*} [DecidableEq α] (S : Finset α) : α → ZMod 2 :=
  fun i => if i ∈ S then 1 else 0

lemma zmod2_val_eq (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

lemma ind_injective {α : Type*} [DecidableEq α] [Fintype α] :
    Function.Injective (ind (α := α)) := by
  intro S T h
  ext i
  have hi := congrFun h i
  simp only [ind] at hi
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp_all

lemma ind_surjective {α : Type*} [DecidableEq α] [Fintype α] (f : α → ZMod 2) :
    ∃ S : Finset α, ind S = f := by
  refine ⟨Finset.univ.filter (fun i => f i = 1), ?_⟩
  ext i
  simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases zmod2_val_eq (f i) with h0 | h1
  · simp [h0]
  · simp [h1]

lemma ind_symmDiff {α : Type*} [DecidableEq α] (S T : Finset α) :
    ind (symmDiff S T) = ind S + ind T := by
  ext i
  simp only [ind, Pi.add_apply, Finset.mem_symmDiff]
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> (simp [hS, hT]; try decide)

def dot {α : Type*} [Fintype α] (a b : α → ZMod 2) : ZMod 2 :=
  ∑ i : α, a i * b i

lemma dot_comm {α : Type*} [Fintype α] (a b : α → ZMod 2) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_add_right {α : Type*} [Fintype α] (a b c : α → ZMod 2) :
    dot a (b + c) = dot a b + dot a c := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dot_add_left {α : Type*} [Fintype α] (a b c : α → ZMod 2) :
    dot (a + b) c = dot a c + dot b c := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma dot_zero_right {α : Type*} [Fintype α] (a : α → ZMod 2) : dot a 0 = 0 := by
  simp [dot]

lemma dot_ind_ind {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    dot (ind A) (ind B) = ((A ∩ B).card : ZMod 2) := by
  simp only [dot, ind]
  calc ∑ i : α, (if i ∈ A then (1 : ZMod 2) else 0) * (if i ∈ B then 1 else 0)
      = ∑ i : α, if i ∈ A ∩ B then (1 : ZMod 2) else 0 :=
        Finset.sum_congr rfl fun i _ => by
          by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;> simp [hA, hB]
    _ = ∑ _i ∈ Finset.univ.filter (fun i => i ∈ A ∩ B), (1 : ZMod 2) := by
        rw [Finset.sum_filter]
    _ = ∑ _i ∈ A ∩ B, (1 : ZMod 2) := by
        congr 1; ext i; simp
    _ = ((A ∩ B).card : ZMod 2) := by simp

lemma sum_ind_filter {α : Type*} [Fintype α] [DecidableEq α] (S : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (∑ i : α, if p i then ind S i else 0) = ((S.filter p).card : ZMod 2) := by
  calc ∑ i : α, (if p i then ind S i else 0)
      = ∑ i : α, if i ∈ S.filter p then (1 : ZMod 2) else 0 :=
        Finset.sum_congr rfl fun i _ => by
          simp only [ind, Finset.mem_filter]
          by_cases hp : p i <;> by_cases hi : i ∈ S <;> simp [hp, hi]
    _ = ∑ _i ∈ Finset.univ.filter (fun i => i ∈ S.filter p), (1 : ZMod 2) := by
        rw [Finset.sum_filter]
    _ = ∑ _i ∈ S.filter p, (1 : ZMod 2) := by
        congr 1; ext i; simp
    _ = ((S.filter p).card : ZMod 2) := by simp

def chi (x : ZMod 2) : Int := if x = 0 then 1 else -1

lemma chi_add (x y : ZMod 2) : chi (x + y) = chi x * chi y := by
  fin_cases x <;> fin_cases y <;> decide

lemma chi_zero : chi 0 = 1 := rfl

lemma sum_chi_dot_all {α : Type*} [Fintype α] [DecidableEq α] (w : α → ZMod 2) :
    (∑ a : α → ZMod 2, chi (dot a w)) = if w = 0 then (2 : Int) ^ Fintype.card α else 0 := by
  by_cases hw : w = 0
  · subst hw
    rw [if_pos rfl]
    simp only [dot_zero_right, chi_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_pow, Nat.cast_ofNat]
  · rw [if_neg hw]
    have hex : ∃ i, w i ≠ 0 := by
      by_contra h
      push Not at h
      exact hw (funext h)
    obtain ⟨i0, hi0⟩ := hex
    have hi01 : w i0 = 1 := (zmod2_val_eq (w i0)).resolve_left hi0
    let e0 : α → ZMod 2 := fun i => if i = i0 then 1 else 0
    have hdot : dot e0 w = 1 := by
      simp [dot, e0, hi01]
    have hsum : (∑ a : α → ZMod 2, chi (dot (a + e0) w)) = ∑ a : α → ZMod 2, chi (dot a w) :=
      Fintype.sum_equiv (Equiv.addRight e0) (fun a => chi (dot (a + e0) w)) (fun a => chi (dot a w)) (fun _ => rfl)
    have hneg : (∑ a : α → ZMod 2, chi (dot (a + e0) w)) = - ∑ a : α → ZMod 2, chi (dot a w) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [dot_add_left, hdot, chi_add]
      change chi (dot a w) * (-1) = -chi (dot a w)
      ring
    linarith

lemma sum_chi_dot_subspace {α : Type*} [Fintype α] [DecidableEq α]
    (M : Finset (α → ZMod 2)) (h0 : (0 : α → ZMod 2) ∈ M)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M) (a : α → ZMod 2) :
    (∑ w ∈ M, chi (dot a w)) = if (∀ w ∈ M, dot a w = 0) then (M.card : Int) else 0 := by
  by_cases ha : ∀ w ∈ M, dot a w = 0
  · rw [if_pos ha]
    calc ∑ w ∈ M, chi (dot a w) = ∑ _w ∈ M, (1 : Int) :=
          Finset.sum_congr rfl fun w hw => by rw [ha w hw, chi_zero]
      _ = (M.card : Int) := by simp
  · rw [if_neg ha]
    push Not at ha
    obtain ⟨w0, hw0, hne⟩ := ha
    have hw01 : dot a w0 = 1 := (zmod2_val_eq _).resolve_left hne
    have hbij : (∑ w ∈ M, chi (dot a (w + w0))) = ∑ w ∈ M, chi (dot a w) := by
      refine Finset.sum_bij (fun w _ => w + w0) ?_ ?_ ?_ ?_
      · intro w hw; exact hadd w hw w0 hw0
      · intro w1 _ w2 _ h; exact add_right_cancel h
      · intro w hw
        refine ⟨w + w0, hadd w hw w0 hw0, ?_⟩
        ext i; simp only [Pi.add_apply]; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · intro _ _; rfl
    have hneg : (∑ w ∈ M, chi (dot a (w + w0))) = - ∑ w ∈ M, chi (dot a w) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [dot_add_right, hw01, chi_add]
      change chi (dot a w) * (-1) = -chi (dot a w)
      ring
    linarith

lemma card_mul_orth {α : Type*} [Fintype α] [DecidableEq α]
    (M : Finset (α → ZMod 2)) (h0 : (0 : α → ZMod 2) ∈ M)
    (hadd : ∀ x ∈ M, ∀ y ∈ M, x + y ∈ M) :
    M.card * (Finset.univ.filter (fun a : α → ZMod 2 => ∀ w ∈ M, dot a w = 0)).card =
      2 ^ Fintype.card α := by
  have h1 : (∑ a : α → ZMod 2, ∑ w ∈ M, chi (dot a w)) =
      (Finset.univ.filter (fun a : α → ZMod 2 => ∀ w ∈ M, dot a w = 0)).card * (M.card : Int) := by
    calc ∑ a : α → ZMod 2, ∑ w ∈ M, chi (dot a w)
        = ∑ a : α → ZMod 2, if (∀ w ∈ M, dot a w = 0) then (M.card : Int) else 0 :=
          Finset.sum_congr rfl fun a _ => sum_chi_dot_subspace M h0 hadd a
      _ = ∑ _a ∈ Finset.univ.filter (fun a : α → ZMod 2 => ∀ w ∈ M, dot a w = 0), (M.card : Int) := by
          rw [Finset.sum_filter]
      _ = _ := by simp [mul_comm]
  have h2 : (∑ a : α → ZMod 2, ∑ w ∈ M, chi (dot a w)) = (2 : Int) ^ Fintype.card α := by
    rw [Finset.sum_comm]
    calc ∑ w ∈ M, ∑ a : α → ZMod 2, chi (dot a w)
        = ∑ w ∈ M, if w = 0 then (2 : Int) ^ Fintype.card α else 0 :=
          Finset.sum_congr rfl fun w _ => sum_chi_dot_all w
      _ = (2 : Int) ^ Fintype.card α := by simp [h0]
  have h3 : ((M.card * (Finset.univ.filter (fun a : α → ZMod 2 => ∀ w ∈ M, dot a w = 0)).card : Nat) : Int) =
      ((2 ^ Fintype.card α : Nat) : Int) := by
    push_cast
    linarith
  exact Int.ofNat.inj h3

lemma parity_of_nat_cast_zmod2 (k : Nat) : ((k : ZMod 2) = 1) ↔ k % 2 = 1 := by
  have h := Nat.div_add_mod k 2
  have h2 : (k : ZMod 2) = ((k % 2 : Nat) : ZMod 2) := by
    have : (k : ZMod 2) = ((2 * (k / 2) + k % 2 : Nat) : ZMod 2) := by rw [h]
    rw [this]; push_cast
    have : (2 : ZMod 2) = 0 := rfl
    rw [this, zero_mul, zero_add]
  rw [h2]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · rw [h0]; decide
  · rw [h1]; decide

lemma mod2_eq_of_zmod2_eq {a b : Nat} (h : (a : ZMod 2) = (b : ZMod 2)) : a % 2 = b % 2 := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · omega
  · exfalso; have h1 := (parity_of_nat_cast_zmod2 b).mpr hb; rw [← h, parity_of_nat_cast_zmod2] at h1; omega
  · exfalso; have h1 := (parity_of_nat_cast_zmod2 a).mpr ha; rw [h, parity_of_nat_cast_zmod2] at h1; omega
  · omega

lemma card_symmDiff_mod2 {α : Type*} [DecidableEq α] (A B : Finset α) :
    (symmDiff A B).card % 2 = (A.card + B.card) % 2 := by
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm] at h2
  have h3 : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  omega

lemma card_inter_symmDiff_mod2 {α : Type*} [Fintype α] [DecidableEq α] (A B C : Finset α) :
    (symmDiff A B ∩ C).card % 2 = ((A ∩ C).card + (B ∩ C).card) % 2 := by
  have h : symmDiff A B ∩ C = symmDiff (A ∩ C) (B ∩ C) := by
    ext i; simp only [Finset.mem_inter, Finset.mem_symmDiff]; tauto
  rw [h, card_symmDiff_mod2]

lemma sum_powerset_neg_one_pow {α : Type*} [DecidableEq α] (B : Finset α) (hB : B.Nonempty) :
    (∑ t ∈ B.powerset.erase ∅, (-1 : Int) ^ t.card) = -1 := by
  have hall : (∑ t ∈ B.powerset, (-1 : Int) ^ t.card) = 0 := by
    have h := Finset.sum_powerset_apply_card (x := B) (f := fun k => (-1 : Int) ^ k)
    have hbin : (∑ k ∈ Finset.range (B.card + 1), (B.card.choose k : Int) * (-1 : Int) ^ k) =
        ((-1 : Int) + 1) ^ B.card := by
      rw [add_pow]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [mul_comm]
    rw [h]
    simp only [nsmul_eq_mul]
    rw [hbin]
    simp [Nat.pos_iff_ne_zero.mp hB.card_pos]
  have hmem : (∅ : Finset α) ∈ B.powerset := Finset.empty_mem_powerset B
  have hsplit := Finset.add_sum_erase B.powerset (fun t => (-1 : Int) ^ t.card) hmem
  simp only [Finset.card_empty, pow_zero] at hsplit
  linarith

lemma sum_partition_factor {α : Type*} [DecidableEq α] (K : Finset α)
    (packets : Finset (Finset α))
    (hsub : ∀ B ∈ packets, B.Nonempty ∧ B ⊆ K)
    (hpart : ∀ j ∈ K, ∃! B : Finset α, B ∈ packets ∧ j ∈ B) :
    (∑ s ∈ K.powerset.filter (fun s => ∀ B ∈ packets, (s ∩ B).Nonempty), (-1 : Int) ^ s.card) =
      (-1 : Int) ^ packets.card := by
  have hdisj : (packets : Set (Finset α)).PairwiseDisjoint id := by
    intro B1 hB1 B2 hB2 hne
    change Disjoint B1 B2
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    obtain ⟨B, _, huniq⟩ := hpart j ((hsub B1 hB1).2 hj1)
    exact hne ((huniq B1 ⟨hB1, hj1⟩).trans (huniq B2 ⟨hB2, hj2⟩).symm)
  have hprod : (∏ B ∈ packets, ∑ t ∈ B.powerset.erase ∅, (-1 : Int) ^ t.card) =
      (-1 : Int) ^ packets.card := by
    calc ∏ B ∈ packets, ∑ t ∈ B.powerset.erase ∅, (-1 : Int) ^ t.card
        = ∏ _B ∈ packets, (-1 : Int) :=
          Finset.prod_congr rfl fun B hB => sum_powerset_neg_one_pow B (hsub B hB).1
      _ = (-1 : Int) ^ packets.card := by simp
  rw [← hprod, Finset.prod_sum]
  symm
  refine Finset.sum_bij (fun f _ => packets.attach.biUnion (fun B => f B.1 B.2)) ?_ ?_ ?_ ?_
  · intro f hf
    rw [Finset.mem_pi] at hf
    rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro j hj
      rw [Finset.mem_biUnion] at hj
      obtain ⟨⟨B, hB⟩, _, hjf⟩ := hj
      exact (hsub B hB).2 (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf B hB)) hjf)
    · intro B hB
      have hne : (f B hB).Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase (hf B hB))
      obtain ⟨j, hj⟩ := hne
      refine ⟨j, Finset.mem_inter.mpr ⟨?_, Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf B hB)) hj⟩⟩
      exact Finset.mem_biUnion.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, hj⟩
  · intro f1 hf1 f2 hf2 heq
    rw [Finset.mem_pi] at hf1 hf2
    funext B hB
    ext j
    have h1 : f1 B hB ⊆ B := Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf1 B hB))
    have h2 : f2 B hB ⊆ B := Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf2 B hB))
    have hmem : j ∈ packets.attach.biUnion (fun C => f1 C.1 C.2) ↔
        j ∈ packets.attach.biUnion (fun C => f2 C.1 C.2) := by rw [heq]
    constructor
    · intro hj1
      have : j ∈ packets.attach.biUnion (fun C => f2 C.1 C.2) :=
        hmem.mp (Finset.mem_biUnion.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, hj1⟩)
      rw [Finset.mem_biUnion] at this
      obtain ⟨⟨C, hC⟩, _, hj2⟩ := this
      have hBC : B = C := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj hB hC hne) (h1 hj1)
          (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf2 C hC)) hj2)
      subst hBC; exact hj2
    · intro hj2
      have : j ∈ packets.attach.biUnion (fun C => f1 C.1 C.2) :=
        hmem.mpr (Finset.mem_biUnion.mpr ⟨⟨B, hB⟩, Finset.mem_attach _ _, hj2⟩)
      rw [Finset.mem_biUnion] at this
      obtain ⟨⟨C, hC⟩, _, hj1⟩ := this
      have hBC : B = C := by
        by_contra hne
        exact Finset.disjoint_left.mp (hdisj hB hC hne) (h2 hj2)
          (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf1 C hC)) hj1)
      subst hBC; exact hj1
  · intro s hs
    rw [Finset.mem_filter, Finset.mem_powerset] at hs
    refine ⟨fun B _ => s ∩ B, ?_, ?_⟩
    · rw [Finset.mem_pi]
      intro B hB
      rw [Finset.mem_erase, Finset.mem_powerset]
      exact ⟨Finset.nonempty_iff_ne_empty.mp (hs.2 B hB), Finset.inter_subset_right⟩
    · ext j
      simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Subtype.exists, Finset.mem_inter]
      constructor
      · rintro ⟨_, _, hj, _⟩; exact hj
      · intro hj
        obtain ⟨B, ⟨hB, hjB⟩, _⟩ := hpart j (hs.1 hj)
        exact ⟨B, hB, hj, hjB⟩
  · intro f hf
    rw [Finset.mem_pi] at hf
    have hpw : (packets.attach : Set {B // B ∈ packets}).PairwiseDisjoint (fun B => f B.1 B.2) := by
      intro B1 _ B2 _ hne
      have hne' : B1.1 ≠ B2.1 := fun h => hne (Subtype.ext h)
      exact (hdisj B1.2 B2.2 hne').mono
        (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf B1.1 B1.2)))
        (Finset.mem_powerset.mp (Finset.mem_of_mem_erase (hf B2.1 B2.2)))
    rw [Finset.card_biUnion hpw, Finset.prod_pow_eq_pow_sum]

def bdy {n m : Nat} (u v : Fin m → Fin n) (f : Fin m → ZMod 2) : Fin n → ZMod 2 :=
  fun j => (∑ i : Fin m, if u i = j then f i else 0) + (∑ i : Fin m, if v i = j then f i else 0)

def boundaryF {n m : Nat} (u v : Fin m → Fin n) (x : Finset (Fin m)) : Finset (Fin n) :=
  Finset.univ.filter (fun j =>
    ((x.filter (fun i => u i = j)).card + (x.filter (fun i => v i = j)).card) % 2 = 1)

def crossingF {n m : Nat} (u v : Fin m → Fin n) (U : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => decide (u i ∈ U) != decide (v i ∈ U))

lemma bdy_add {n m : Nat} (u v : Fin m → Fin n) (f g : Fin m → ZMod 2) :
    bdy u v (f + g) = bdy u v f + bdy u v g := by
  ext j
  simp only [bdy, Pi.add_apply]
  have h1 : (∑ i : Fin m, if u i = j then f i + g i else 0) =
      (∑ i : Fin m, if u i = j then f i else 0) + (∑ i : Fin m, if u i = j then g i else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have h2 : (∑ i : Fin m, if v i = j then f i + g i else 0) =
      (∑ i : Fin m, if v i = j then f i else 0) + (∑ i : Fin m, if v i = j then g i else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  rw [h1, h2]; ring

lemma bdy_ind {n m : Nat} (u v : Fin m → Fin n) (S : Finset (Fin m)) :
    bdy u v (ind S) = ind (boundaryF u v S) := by
  ext j
  have hu : (∑ i : Fin m, if u i = j then ind S i else 0) = ((S.filter (fun i => u i = j)).card : ZMod 2) :=
    sum_ind_filter S (fun i => u i = j)
  have hv : (∑ i : Fin m, if v i = j then ind S i else 0) = ((S.filter (fun i => v i = j)).card : ZMod 2) :=
    sum_ind_filter S (fun i => v i = j)
  change (∑ i : Fin m, if u i = j then ind S i else 0) + (∑ i : Fin m, if v i = j then ind S i else 0) =
    if j ∈ boundaryF u v S then 1 else 0
  rw [hu, hv, ← Nat.cast_add]
  simp only [boundaryF, Finset.mem_filter, Finset.mem_univ, true_and]
  set k := (S.filter (fun i => u i = j)).card + (S.filter (fun i => v i = j)).card
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · rw [if_neg (by omega)]
    exact (zmod2_val_eq _).resolve_right (by rw [parity_of_nat_cast_zmod2]; omega)
  · rw [if_pos h1]
    exact (parity_of_nat_cast_zmod2 k).mpr h1

lemma boundaryF_symmDiff {n m : Nat} (u v : Fin m → Fin n) (S1 S2 : Finset (Fin m)) :
    boundaryF u v (symmDiff S1 S2) = symmDiff (boundaryF u v S1) (boundaryF u v S2) := by
  apply ind_injective
  rw [← bdy_ind, ind_symmDiff, bdy_add, bdy_ind, bdy_ind, ind_symmDiff]

lemma crossingF_symmDiff {n m : Nat} (u v : Fin m → Fin n) (W1 W2 : Finset (Fin n)) :
    crossingF u v (symmDiff W1 W2) = symmDiff (crossingF u v W1) (crossingF u v W2) := by
  ext i
  simp only [crossingF, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_symmDiff]
  by_cases h1 : u i ∈ W1 <;> by_cases h2 : u i ∈ W2 <;> by_cases h3 : v i ∈ W1 <;> by_cases h4 : v i ∈ W2 <;>
    simp [h1, h2, h3, h4]

lemma dot_dual {n m : Nat} (u v : Fin m → Fin n) (W : Finset (Fin n)) (f : Fin m → ZMod 2) :
    dot (ind (crossingF u v W)) f = dot (ind W) (bdy u v f) := by
  simp only [dot, bdy, mul_add, Finset.sum_add_distrib]
  have h1 : (∑ j : Fin n, ind W j * ∑ i : Fin m, if u i = j then f i else 0) =
      ∑ i : Fin m, (if u i ∈ W then 1 else 0) * f i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (∑ j : Fin n, ind W j * if u i = j then f i else 0) = ind W (u i) * f i := by
      rw [Finset.sum_eq_single (u i)]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]; rfl
  have h2 : (∑ j : Fin n, ind W j * ∑ i : Fin m, if v i = j then f i else 0) =
      ∑ i : Fin m, (if v i ∈ W then 1 else 0) * f i := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (∑ j : Fin n, ind W j * if v i = j then f i else 0) = ind W (v i) * f i := by
      rw [Finset.sum_eq_single (v i)]
      · simp
      · intro j _ hj; simp [Ne.symm hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [this]; rfl
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [ind, crossingF, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hu : u i ∈ W <;> by_cases hv : v i ∈ W <;> simp [hu, hv]
  exact (CharTwo.add_self_eq_zero (f i)).symm

lemma cut_parity {n m : Nat} (u v : Fin m → Fin n) (W : Finset (Fin n)) (S : Finset (Fin m)) :
    (S ∩ crossingF u v W).card % 2 = (boundaryF u v S ∩ W).card % 2 := by
  apply mod2_eq_of_zmod2_eq
  rw [Finset.inter_comm S, Finset.inter_comm (boundaryF u v S), ← dot_ind_ind, ← dot_ind_ind, ← bdy_ind]
  exact dot_dual u v W (ind S)

lemma ker_proj_surj {n m : Nat} (u v : Fin m → Fin n) (U : Finset (Fin n))
    (hK_ne : (crossingF u v U).Nonempty)
    (hno_subcut : ∀ V : Finset (Fin n), crossingF u v V ⊆ crossingF u v U →
      crossingF u v V = ∅ ∨ crossingF u v V = crossingF u v U) :
    let K := crossingF u v U
    let kerB := (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun f => bdy u v f = 0)
    let proj : (Fin m → ZMod 2) → ({i // i ∈ K} → ZMod 2) := fun f i => f i.1
    let H0 := (Finset.univ : Finset ({i // i ∈ K} → ZMod 2)).filter (fun w => ∑ i, w i = 0)
    kerB.image proj = H0 ∧ H0.card = 2 ^ (K.card - 1) := by
  intro K kerB proj H0
  let cutSp : Finset (Fin m → ZMod 2) := Finset.univ.image (fun W : Finset (Fin n) => ind (crossingF u v W))
  have hkerB0 : (0 : Fin m → ZMod 2) ∈ kerB := by
    simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and]
    ext j; simp [bdy]
  have hkerBadd : ∀ f ∈ kerB, ∀ g ∈ kerB, f + g ∈ kerB := by
    intro f hf g hg
    simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg ⊢
    rw [bdy_add, hf, hg, add_zero]
  have hcut0 : (0 : Fin m → ZMod 2) ∈ cutSp := by
    rw [Finset.mem_image]
    refine ⟨∅, Finset.mem_univ _, ?_⟩
    ext i; simp [ind, crossingF]
  have hcutadd : ∀ f ∈ cutSp, ∀ g ∈ cutSp, f + g ∈ cutSp := by
    intro f hf g hg
    rw [Finset.mem_image] at hf hg ⊢
    obtain ⟨W1, _, rfl⟩ := hf
    obtain ⟨W2, _, rfl⟩ := hg
    exact ⟨symmDiff W1 W2, Finset.mem_univ _, by rw [crossingF_symmDiff, ind_symmDiff]⟩
  have hcut_orth : Finset.univ.filter (fun f : Fin m → ZMod 2 => ∀ a ∈ cutSp, dot f a = 0) = kerB := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, kerB]
    constructor
    · intro h
      ext j
      have hj := h (ind (crossingF u v {j})) (Finset.mem_image.mpr ⟨{j}, Finset.mem_univ _, rfl⟩)
      rw [dot_comm, dot_dual] at hj
      have : dot (ind ({j} : Finset (Fin n))) (bdy u v f) = bdy u v f j := by simp [dot, ind]
      rwa [this] at hj
    · intro h a ha
      rw [Finset.mem_image] at ha
      obtain ⟨W, _, rfl⟩ := ha
      rw [dot_comm, dot_dual, h, dot_zero_right]
  have hkerB_orth : Finset.univ.filter (fun a : Fin m → ZMod 2 => ∀ f ∈ kerB, dot a f = 0) = cutSp := by
    have hsub : cutSp ⊆ Finset.univ.filter (fun a : Fin m → ZMod 2 => ∀ f ∈ kerB, dot a f = 0) := by
      intro a ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun f hf => ?_⟩
      rw [Finset.mem_image] at ha
      obtain ⟨W, _, rfl⟩ := ha
      simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rw [dot_dual, hf, dot_zero_right]
    have hcard1 := card_mul_orth kerB hkerB0 hkerBadd
    have hcard2 := card_mul_orth cutSp hcut0 hcutadd
    rw [hcut_orth] at hcard2
    have hpos : 0 < kerB.card := Finset.card_pos.mpr ⟨0, hkerB0⟩
    have heq_card : (Finset.univ.filter (fun a : Fin m → ZMod 2 => ∀ f ∈ kerB, dot a f = 0)).card = cutSp.card := by
      exact Nat.eq_of_mul_eq_mul_left hpos (by linarith)
    exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq heq_card)).symm
  let imP := kerB.image proj
  have himP0 : (0 : {i // i ∈ K} → ZMod 2) ∈ imP := Finset.mem_image.mpr ⟨0, hkerB0, rfl⟩
  have himPadd : ∀ a ∈ imP, ∀ b ∈ imP, a + b ∈ imP := by
    intro a ha b hb
    rw [Finset.mem_image] at ha hb ⊢
    obtain ⟨f, hf, rfl⟩ := ha
    obtain ⟨g, hg, rfl⟩ := hb
    exact ⟨f + g, hkerBadd f hf g hg, rfl⟩
  have himP_sub : imP ⊆ H0 := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨f, hf, rfl⟩ := hw
    simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    have hd := dot_dual u v U f
    rw [hf, dot_zero_right] at hd
    have hsum : (∑ i : {i // i ∈ K}, f i.1) = dot (ind K) f := by
      rw [Finset.sum_coe_sort K f, dot]
      calc ∑ i ∈ K, f i = ∑ i ∈ Finset.univ.filter (fun i => i ∈ K), f i := by
            congr 1; ext i; simp
        _ = ∑ i : Fin m, if i ∈ K then f i else 0 := Finset.sum_filter _ _
        _ = ∑ i : Fin m, ind K i * f i :=
            Finset.sum_congr rfl fun i _ => by simp only [ind]; split_ifs <;> simp
    rw [hsum]; exact hd
  have himP_orth_sub : Finset.univ.filter (fun a : {i // i ∈ K} → ZMod 2 => ∀ w ∈ imP, dot a w = 0) ⊆
      {0, (fun _ => 1)} := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    let extA : Fin m → ZMod 2 := fun i => if hi : i ∈ K then a ⟨i, hi⟩ else 0
    have hext_orth : ∀ f ∈ kerB, dot extA f = 0 := by
      intro f hf
      have h1 : dot extA f = dot a (proj f) := by
        simp only [dot, extA, proj]
        calc ∑ i : Fin m, (if hi : i ∈ K then a ⟨i, hi⟩ else 0) * f i
            = ∑ i : Fin m, if hi : i ∈ K then a ⟨i, hi⟩ * f i else 0 :=
              Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
          _ = ∑ i ∈ Finset.univ.filter (fun i => i ∈ K), if hi : i ∈ K then a ⟨i, hi⟩ * f i else 0 := by
              rw [Finset.sum_filter]; refine Finset.sum_congr rfl fun i _ => by split_ifs <;> rfl
          _ = ∑ i : {i // i ∈ K}, a i * f i.1 := by
              symm
              refine Finset.sum_bij (fun i _ => i.1) (fun i _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, i.2⟩)
                (fun _ _ _ _ h => Subtype.ext h)
                (fun i hi => ⟨⟨i, (Finset.mem_filter.mp hi).2⟩, Finset.mem_univ _, rfl⟩)
                (fun i _ => by simp [i.2])
      rw [h1]
      exact ha (proj f) (Finset.mem_image.mpr ⟨f, hf, rfl⟩)
    have hmem_cut : extA ∈ cutSp := by
      rw [← hkerB_orth, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hext_orth⟩
    rw [Finset.mem_image] at hmem_cut
    obtain ⟨V, _, hVeq⟩ := hmem_cut
    have hVK : crossingF u v V ⊆ K := by
      intro i hi
      by_contra hni
      have h1 := congrFun hVeq i
      simp only [ind, extA, hi, hni, ↓reduceIte, ↓reduceDIte] at h1
      exact one_ne_zero h1
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hno_subcut V hVK with h0 | hfull
    · left
      ext ⟨i, hi⟩
      have h1 := congrFun hVeq i
      simp only [h0, ind, extA, hi, Finset.notMem_empty, ↓reduceIte, ↓reduceDIte] at h1
      exact h1.symm
    · right
      ext ⟨i, hi⟩
      have h1 := congrFun hVeq i
      have hi' : i ∈ crossingF u v U := hi
      simp only [hfull, ind, extA, hi, hi', ↓reduceIte, ↓reduceDIte] at h1
      exact h1.symm
  have hH0_card : 2 * H0.card = 2 ^ K.card := by
    obtain ⟨i0, hi0⟩ := hK_ne
    let e0 : {i // i ∈ K} → ZMod 2 := fun i => if i.1 = i0 then 1 else 0
    have he0_sum : (∑ i : {i // i ∈ K}, e0 i) = 1 := by
      rw [Finset.sum_eq_single ⟨i0, hi0⟩]
      · simp [e0]
      · intro j _ hj
        have hne : j.1 ≠ i0 := fun h => hj (Subtype.ext h)
        simp [e0, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hcomp : Finset.univ.filter (fun w : {i // i ∈ K} → ZMod 2 => ∑ i, w i = 1) =
        H0.image (fun w => w + e0) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, H0]
      constructor
      · intro hw
        refine ⟨w + e0, ?_, ?_⟩
        · simp only [Pi.add_apply]
          rw [Finset.sum_add_distrib]
          change (∑ i, w i) + (∑ i, e0 i) = 0
          rw [hw, he0_sum]; decide
        · ext i; simp only [Pi.add_apply]; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      · rintro ⟨w', hw', rfl⟩
        simp only [Pi.add_apply]
        rw [Finset.sum_add_distrib]
        change (∑ i, w' i) + (∑ i, e0 i) = 1
        rw [hw', he0_sum, zero_add]
    have hinj : Function.Injective (fun w : {i // i ∈ K} → ZMod 2 => w + e0) :=
      fun _ _ h => add_right_cancel h
    have hcard_eq : (Finset.univ.filter (fun w : {i // i ∈ K} → ZMod 2 => ∑ i, w i = 1)).card = H0.card := by
      rw [hcomp, Finset.card_image_of_injective _ hinj]
    have hdisj : Disjoint H0 (Finset.univ.filter (fun w : {i // i ∈ K} → ZMod 2 => ∑ i, w i = 1)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      simp only [H0, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h1] at h2; exact zero_ne_one h2
    have hunion : H0 ∪ Finset.univ.filter (fun w : {i // i ∈ K} → ZMod 2 => ∑ i, w i = 1) = Finset.univ := by
      ext w; simp only [Finset.mem_union, H0, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact zmod2_val_eq _
    have htot := congrArg Finset.card hunion
    rw [Finset.card_union_of_disjoint hdisj, hcard_eq, Finset.card_univ, Fintype.card_fun, ZMod.card,
      Fintype.card_coe] at htot
    omega
  have himP_eq : imP = H0 := by
    have hcm := card_mul_orth imP himP0 himPadd
    rw [Fintype.card_coe] at hcm
    have horth_le : (Finset.univ.filter (fun a : {i // i ∈ K} → ZMod 2 => ∀ w ∈ imP, dot a w = 0)).card ≤ 2 := by
      calc _ ≤ ({(0 : {i // i ∈ K} → ZMod 2), fun _ => 1} : Finset _).card := Finset.card_le_card himP_orth_sub
        _ ≤ 2 := Finset.card_le_two
    have hle : H0.card ≤ imP.card := by
      have : 2 * H0.card ≤ 2 * imP.card := by
        calc 2 * H0.card = 2 ^ K.card := hH0_card
          _ = imP.card * (Finset.univ.filter (fun a : {i // i ∈ K} → ZMod 2 => ∀ w ∈ imP, dot a w = 0)).card := hcm.symm
          _ ≤ imP.card * 2 := Nat.mul_le_mul_left _ horth_le
          _ = 2 * imP.card := Nat.mul_comm _ _
      omega
    exact Finset.eq_of_subset_of_card_le himP_sub hle
  have hH0_pow : H0.card = 2 ^ (K.card - 1) := by
    have hk1 : 1 ≤ K.card := hK_ne.card_pos
    have hpow : 2 * 2 ^ (K.card - 1) = 2 ^ K.card := by
      rw [← pow_succ', Nat.sub_add_cancel hk1]
    omega
  exact ⟨himP_eq, hH0_pow⟩

set_option maxHeartbeats 800000 in
theorem main_proof : ∀ (n m : Nat) (u v : Fin m → Fin n) (T : Finset (Fin m)),
  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let vertices := (Finset.univ : Finset (Finset (Fin n)))
  let boundary := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card +
       (x.filter (fun i => v i = j)).card) % 2 = 1)
  let crossing := fun (U : Finset (Fin n)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun i => decide (u i ∈ U) != decide (v i ∈ U))
  ∀ (d e : Finset (Fin n)) (x : Finset (Fin m)), boundary x = d →
    (∃ y ∈ cube, boundary y = e) →
    let odd := fun (U : Finset (Fin n)) =>
      crossing U ⊆ T ∧ (d ∩ U).card % 2 ≠ (e ∩ U).card % 2
    ∀ U ∈ vertices, odd U → (∀ V ∈ vertices, odd V → (crossing U).card ≤ (crossing V).card) →
      let K := crossing U
      ∀ packets : Finset (Finset (Fin m)),
        (∀ B ∈ packets, B.Nonempty ∧ B ⊆ K) →
        (∀ j ∈ K, ∃! B : Finset (Fin m), B ∈ packets ∧ j ∈ B) →
        let accept := fun (z : Finset (Fin m)) => ∀ B ∈ packets, z ∩ B ≠ x ∩ B
        let models := fun (a : Finset (Fin n)) => cube.filter (fun z => boundary z = a)
        let lhs := ((models d).filter accept).card
        let rhs := ((models e).filter accept).card
        (2 : Int) ^ (K.card - 1) * ((lhs : Int) - (rhs : Int)) =
          (-1 : Int) ^ packets.card * ((models d).card : Int) := by
  intro n m u v T cube vertices boundary crossing d e x hbx ⟨y, _, hby⟩ odd U _ hoddU hminU K
    packets hpk_sub hpk_part accept models lhs rhs
  have hK_ne : K.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hxK := cut_parity u v U x
    have hyK := cut_parity u v U y
    change (x ∩ K).card % 2 = (boundary x ∩ U).card % 2 at hxK
    change (y ∩ K).card % 2 = (boundary y ∩ U).card % 2 at hyK
    rw [hbx] at hxK; rw [hby] at hyK
    rw [h, Finset.inter_empty, Finset.card_empty] at hxK hyK
    exact hoddU.2 (by omega)
  have hno_subcut : ∀ V : Finset (Fin n), crossingF u v V ⊆ crossingF u v U →
      crossingF u v V = ∅ ∨ crossingF u v V = crossingF u v U := by
    intro V hVK
    by_contra hc
    push Not at hc
    obtain ⟨hne0, hneK⟩ := hc
    have hVlt : (crossingF u v V).card < (crossingF u v U).card := Finset.card_lt_card (lt_of_le_of_ne hVK hneK)
    by_cases hoddV : (d ∩ V).card % 2 ≠ (e ∩ V).card % 2
    · have hle : (crossingF u v U).card ≤ (crossingF u v V).card :=
        hminU V (Finset.mem_univ V) ⟨hVK.trans hoddU.1, hoddV⟩
      omega
    · push Not at hoddV
      let W := symmDiff U V
      have hcrW : crossingF u v W = crossingF u v U \ crossingF u v V := by
        rw [crossingF_symmDiff]
        ext i; simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
        constructor
        · rintro (⟨hiK, hiV⟩ | ⟨hiV, hiK⟩)
          · exact ⟨hiK, hiV⟩
          · exact absurd (hVK hiV) hiK
        · rintro ⟨hiK, hiV⟩; exact Or.inl ⟨hiK, hiV⟩
      have hWlt : (crossingF u v W).card < (crossingF u v U).card := by
        rw [hcrW]
        have hpos : 0 < (crossingF u v V).card := Finset.card_pos.mpr hne0
        have hsum := Finset.card_sdiff_add_card_eq_card hVK
        omega
      have hoddW : (d ∩ W).card % 2 ≠ (e ∩ W).card % 2 := by
        have h1 : (d ∩ W).card % 2 = ((d ∩ U).card + (d ∩ V).card) % 2 := by
          rw [Finset.inter_comm d W, Finset.inter_comm d U, Finset.inter_comm d V]
          exact card_inter_symmDiff_mod2 U V d
        have h2 : (e ∩ W).card % 2 = ((e ∩ U).card + (e ∩ V).card) % 2 := by
          rw [Finset.inter_comm e W, Finset.inter_comm e U, Finset.inter_comm e V]
          exact card_inter_symmDiff_mod2 U V e
        have := hoddU.2
        omega
      have hle : (crossingF u v U).card ≤ (crossingF u v W).card :=
        hminU W (Finset.mem_univ W) ⟨(hcrW ▸ Finset.sdiff_subset).trans hoddU.1, hoddW⟩
      omega
  obtain ⟨himP_eq, hH0_pow⟩ := ker_proj_surj u v U hK_ne hno_subcut
  let kerB := (Finset.univ : Finset (Fin m → ZMod 2)).filter (fun f => bdy u v f = 0)
  let proj : (Fin m → ZMod 2) → ({i // i ∈ K} → ZMod 2) := fun f i => f i.1
  let H0 := (Finset.univ : Finset ({i // i ∈ K} → ZMod 2)).filter (fun w => ∑ i, w i = 0)
  change kerB.image proj = H0 at himP_eq
  change H0.card = 2 ^ (K.card - 1) at hH0_pow
  have hkerBadd : ∀ f ∈ kerB, ∀ g ∈ kerB, f + g ∈ kerB := by
    intro f hf g hg
    simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and] at hf hg ⊢
    rw [bdy_add, hf, hg, add_zero]
  let fib0 := kerB.filter (fun f => proj f = 0)
  have hfib_card : ∀ w ∈ H0, (kerB.filter (fun f => proj f = w)).card = fib0.card := by
    intro w hw
    rw [← himP_eq, Finset.mem_image] at hw
    obtain ⟨f0, hf0, rfl⟩ := hw
    refine Finset.card_bij (fun f _ => f + f0) ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_filter] at hf
      simp only [fib0, Finset.mem_filter]
      refine ⟨hkerBadd f hf.1 f0 hf0, ?_⟩
      ext i; change f i.1 + f0 i.1 = 0
      have hfi : f i.1 = f0 i.1 := congrFun hf.2 i
      rw [hfi, CharTwo.add_self_eq_zero]
    · intro f1 _ f2 _ h; exact add_right_cancel h
    · intro g hg
      simp only [fib0, Finset.mem_filter] at hg
      refine ⟨g + f0, ?_, ?_⟩
      · simp only [Finset.mem_filter]
        refine ⟨hkerBadd g hg.1 f0 hf0, ?_⟩
        ext i; change g i.1 + f0 i.1 = f0 i.1
        have hgi : g i.1 = 0 := congrFun hg.2 i
        rw [hgi, zero_add]
      · ext i; simp only [Pi.add_apply]; rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have hkerB_card_eq : kerB.card = H0.card * fib0.card := by
    have := Finset.card_eq_sum_card_fiberwise (f := proj) (s := kerB) (t := H0)
      (fun f hf => himP_eq ▸ Finset.mem_image.mpr ⟨f, hf, rfl⟩)
    rw [this]
    calc ∑ w ∈ H0, (kerB.filter (fun f => proj f = w)).card
        = ∑ _w ∈ H0, fib0.card := Finset.sum_congr rfl fun w hw => hfib_card w hw
      _ = H0.card * fib0.card := by simp
  have hmodels_d_card : (models d).card = kerB.card := by
    refine Finset.card_bij (fun z _ => ind (symmDiff z x)) ?_ ?_ ?_
    · intro z hz
      simp only [models, cube, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [bdy_ind, boundaryF_symmDiff]
      change ind (symmDiff (boundary z) (boundary x)) = 0
      rw [hz, hbx, symmDiff_self, Finset.bot_eq_empty]
      ext j; simp [ind]
    · intro z1 _ z2 _ h
      have hs := ind_injective h
      calc z1 = symmDiff (symmDiff z1 x) x := by simp
        _ = symmDiff (symmDiff z2 x) x := by rw [hs]
        _ = z2 := by simp
    · intro f hf
      obtain ⟨c, rfl⟩ := ind_surjective f
      simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and] at hf
      have hbc : boundaryF u v c = ∅ := by
        apply ind_injective; rw [← bdy_ind, hf]; ext j; simp [ind]
      refine ⟨symmDiff c x, ?_, by simp⟩
      simp only [models, cube, Finset.mem_filter, Finset.mem_univ, true_and]
      change boundaryF u v (symmDiff c x) = d
      rw [boundaryF_symmDiff, hbc, ← Finset.bot_eq_empty, bot_symmDiff]
      exact hbx
  let accK : Finset (Fin m) → Prop := fun s => ∀ B ∈ packets, (s ∩ B).Nonempty
  have hacc_iff : ∀ z : Finset (Fin m), accept z ↔ accK (symmDiff (z ∩ K) (x ∩ K)) := by
    intro z
    simp only [accept, accK]
    refine forall₂_congr fun B hB => ?_
    have hBK := (hpk_sub B hB).2
    have heq : symmDiff (z ∩ K) (x ∩ K) ∩ B = symmDiff (z ∩ B) (x ∩ B) := by
      ext i; simp only [Finset.mem_inter, Finset.mem_symmDiff]
      constructor
      · rintro ⟨(⟨⟨hz, _⟩, hnx⟩ | ⟨⟨hx, _⟩, hnz⟩), hiB⟩
        · exact Or.inl ⟨⟨hz, hiB⟩, fun h => hnx ⟨h.1, hBK hiB⟩⟩
        · exact Or.inr ⟨⟨hx, hiB⟩, fun h => hnz ⟨h.1, hBK hiB⟩⟩
      · rintro (⟨⟨hz, hiB⟩, hnx⟩ | ⟨⟨hx, hiB⟩, hnz⟩)
        · exact ⟨Or.inl ⟨⟨hz, hBK hiB⟩, fun h => hnx ⟨h.1, hiB⟩⟩, hiB⟩
        · exact ⟨Or.inr ⟨⟨hx, hBK hiB⟩, fun h => hnz ⟨h.1, hiB⟩⟩, hiB⟩
    rw [heq, Finset.nonempty_iff_ne_empty, ← Finset.bot_eq_empty, ne_eq, ne_eq, symmDiff_eq_bot]
  let evenK := K.powerset.filter (fun s => s.card % 2 = 0)
  let oddK := K.powerset.filter (fun s => s.card % 2 = 1)
  have hbij_even : ∀ s ∈ K.powerset, s ∈ evenK ↔ (fun i : {i // i ∈ K} => ind s i.1) ∈ H0 := by
    intro s hs
    rw [Finset.mem_powerset] at hs
    simp only [evenK, H0, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset, hs]
    have hsum : (∑ i : {i // i ∈ K}, ind s i.1) = (s.card : ZMod 2) := by
      rw [Finset.sum_coe_sort K (fun i => ind s i)]
      calc ∑ i ∈ K, ind s i = ∑ i ∈ K, if i ∈ s then (1 : ZMod 2) else 0 := rfl
        _ = ∑ _i ∈ K.filter (· ∈ s), (1 : ZMod 2) := (Finset.sum_filter _ _).symm
        _ = ∑ _i ∈ s, (1 : ZMod 2) := by
            congr 1; ext i; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hs h, h⟩⟩
        _ = (s.card : ZMod 2) := by simp
    rw [hsum]
    rcases Nat.mod_two_eq_zero_or_one s.card with h0 | h1
    · constructor
      · intro _; exact (zmod2_val_eq _).resolve_right (by rw [parity_of_nat_cast_zmod2]; omega)
      · intro _; exact h0
    · constructor
      · intro h; omega
      · intro h; exfalso; have h1' := (parity_of_nat_cast_zmod2 _).mpr h1; rw [h] at h1'; exact zero_ne_one h1'
  have hlhs_card : lhs = (evenK.filter accK).card * fib0.card := by
    have h1 : lhs = ∑ s ∈ evenK.filter accK,
        ((models d).filter (fun z => symmDiff (z ∩ K) (x ∩ K) = s)).card := by
      have hsub_map : ∀ z ∈ (models d).filter accept, symmDiff (z ∩ K) (x ∩ K) ∈ evenK.filter accK := by
        intro z hz
        simp only [Finset.mem_filter] at hz
        rw [Finset.mem_filter]
        refine ⟨?_, (hacc_iff z).mp hz.2⟩
        have hzmod := hz.1
        simp only [models, cube, Finset.mem_filter, Finset.mem_univ, true_and] at hzmod
        have hpar : (symmDiff z x ∩ K).card % 2 = 0 := by
          have := cut_parity u v U (symmDiff z x)
          rw [boundaryF_symmDiff] at this
          change (symmDiff z x ∩ K).card % 2 = (symmDiff (boundary z) (boundary x) ∩ U).card % 2 at this
          rw [hzmod, hbx, symmDiff_self, Finset.bot_eq_empty, Finset.empty_inter, Finset.card_empty] at this
          exact this
        have hinter : symmDiff (z ∩ K) (x ∩ K) = symmDiff z x ∩ K := by
          ext i; simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
        simp only [evenK, Finset.mem_filter, Finset.mem_powerset]
        exact ⟨by rw [hinter]; exact Finset.inter_subset_right, by rw [hinter]; exact hpar⟩
      have hfw := Finset.card_eq_sum_card_fiberwise (f := fun z => symmDiff (z ∩ K) (x ∩ K))
        (s := (models d).filter accept) (t := evenK.filter accK) hsub_map
      change ((models d).filter accept).card = _
      rw [hfw]
      refine Finset.sum_congr rfl fun s hs => ?_
      congr 1; ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hzm, _⟩, rfl⟩; exact ⟨hzm, rfl⟩
      · rintro ⟨hzm, rfl⟩; exact ⟨⟨hzm, (hacc_iff z).mpr (Finset.mem_filter.mp hs).2⟩, rfl⟩
    rw [h1]
    have hfib : ∀ s ∈ evenK.filter accK,
        ((models d).filter (fun z => symmDiff (z ∩ K) (x ∩ K) = s)).card = fib0.card := by
      intro s hs
      have hsE := (Finset.mem_filter.mp hs).1
      have hsK : s ∈ K.powerset := (Finset.mem_filter.mp hsE).1
      have hwH0 : (fun i : {i // i ∈ K} => ind s i.1) ∈ H0 := (hbij_even s hsK).mp hsE
      rw [← hfib_card _ hwH0]
      refine Finset.card_bij (fun z _ => ind (symmDiff z x)) ?_ ?_ ?_
      · intro z hz
        simp only [Finset.mem_filter, models, cube, Finset.mem_univ, true_and] at hz
        simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rw [bdy_ind, boundaryF_symmDiff]
          change ind (symmDiff (boundary z) (boundary x)) = 0
          rw [hz.1, hbx, symmDiff_self, Finset.bot_eq_empty]; ext j; simp [ind]
        · ext ⟨i, hi⟩
          simp only [proj, ind]
          have hmem : i ∈ symmDiff z x ↔ i ∈ s := by
            rw [← hz.2]; simp only [Finset.mem_symmDiff, Finset.mem_inter, hi, and_true]
          simp [hmem]
      · intro z1 _ z2 _ h
        have hs' := ind_injective h
        calc z1 = symmDiff (symmDiff z1 x) x := by simp
          _ = symmDiff (symmDiff z2 x) x := by rw [hs']
          _ = z2 := by simp
      · intro f hf
        obtain ⟨c, rfl⟩ := ind_surjective f
        simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        have hbc : boundaryF u v c = ∅ := by
          apply ind_injective; rw [← bdy_ind, hf.1]; ext j; simp [ind]
        refine ⟨symmDiff c x, ?_, by simp⟩
        simp only [Finset.mem_filter, models, cube, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · change boundaryF u v (symmDiff c x) = d
          rw [boundaryF_symmDiff, hbc, ← Finset.bot_eq_empty, bot_symmDiff]
          exact hbx
        · ext i
          have h1 : i ∈ symmDiff (symmDiff c x ∩ K) (x ∩ K) ↔ i ∈ c ∧ i ∈ K := by
            simp only [Finset.mem_symmDiff, Finset.mem_inter]; tauto
          rw [h1]
          by_cases hiK : i ∈ K
          · have hfi := congrFun hf.2 ⟨i, hiK⟩
            simp only [proj, ind] at hfi
            simp only [hiK, and_true]
            by_cases hc : i ∈ c <;> by_cases hs' : i ∈ s <;> simp_all
          · simp only [hiK, and_false, false_iff]
            exact fun h => hiK (Finset.mem_powerset.mp hsK h)
    calc ∑ s ∈ evenK.filter accK, ((models d).filter (fun z => symmDiff (z ∩ K) (x ∩ K) = s)).card
        = ∑ _s ∈ evenK.filter accK, fib0.card := Finset.sum_congr rfl hfib
      _ = (evenK.filter accK).card * fib0.card := by simp
  have hrhs_card : rhs = (oddK.filter accK).card * fib0.card := by
    have hxy_odd : (symmDiff y x ∩ K).card % 2 = 1 := by
      have h1 := cut_parity u v U (symmDiff y x)
      rw [boundaryF_symmDiff] at h1
      change (symmDiff y x ∩ K).card % 2 = (symmDiff (boundary y) (boundary x) ∩ U).card % 2 at h1
      rw [hby, hbx, card_inter_symmDiff_mod2 e d U] at h1
      have := hoddU.2
      omega
    have h1 : rhs = ∑ s ∈ oddK.filter accK,
        ((models e).filter (fun z => symmDiff (z ∩ K) (x ∩ K) = s)).card := by
      have hsub_map : ∀ z ∈ (models e).filter accept, symmDiff (z ∩ K) (x ∩ K) ∈ oddK.filter accK := by
        intro z hz
        simp only [Finset.mem_filter] at hz
        rw [Finset.mem_filter]
        refine ⟨?_, (hacc_iff z).mp hz.2⟩
        have hzmod := hz.1
        simp only [models, cube, Finset.mem_filter, Finset.mem_univ, true_and] at hzmod
        have hpar : (symmDiff z y ∩ K).card % 2 = 0 := by
          have := cut_parity u v U (symmDiff z y)
          rw [boundaryF_symmDiff] at this
          change (symmDiff z y ∩ K).card % 2 = (symmDiff (boundary z) (boundary y) ∩ U).card % 2 at this
          rw [hzmod, hby, symmDiff_self, Finset.bot_eq_empty, Finset.empty_inter, Finset.card_empty] at this
          exact this
        have hsym : symmDiff (z ∩ K) (x ∩ K) = symmDiff (symmDiff z y ∩ K) (symmDiff y x ∩ K) := by
          ext i; simp only [Finset.mem_symmDiff, Finset.mem_inter]
          by_cases hz' : i ∈ z <;> by_cases hy' : i ∈ y <;> by_cases hx' : i ∈ x <;> by_cases hk' : i ∈ K <;> simp [hz', hy', hx', hk']
        have hcard_par : (symmDiff (z ∩ K) (x ∩ K)).card % 2 = 1 := by
          rw [hsym, card_symmDiff_mod2]; omega
        simp only [oddK, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨?_, hcard_par⟩
        intro i hi; rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨h, _⟩ | ⟨h, _⟩ <;> exact (Finset.mem_inter.mp h).2
      have hfw := Finset.card_eq_sum_card_fiberwise (f := fun z => symmDiff (z ∩ K) (x ∩ K))
        (s := (models e).filter accept) (t := oddK.filter accK) hsub_map
      change ((models e).filter accept).card = _
      rw [hfw]
      refine Finset.sum_congr rfl fun s hs => ?_
      congr 1; ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hzm, _⟩, rfl⟩; exact ⟨hzm, rfl⟩
      · rintro ⟨hzm, rfl⟩; exact ⟨⟨hzm, (hacc_iff z).mpr (Finset.mem_filter.mp hs).2⟩, rfl⟩
    rw [h1]
    have hfib : ∀ s ∈ oddK.filter accK,
        ((models e).filter (fun z => symmDiff (z ∩ K) (x ∩ K) = s)).card = fib0.card := by
      intro s hs
      have hsO := (Finset.mem_filter.mp hs).1
      have hsK : s ∈ K.powerset := (Finset.mem_filter.mp hsO).1
      let s' := symmDiff s (symmDiff y x ∩ K)
      have hs'K : s' ∈ K.powerset := by
        rw [Finset.mem_powerset]
        intro i hi; rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨h, _⟩ | ⟨h, _⟩
        · exact Finset.mem_powerset.mp hsK h
        · exact (Finset.mem_inter.mp h).2
      have hs'E : s' ∈ evenK := by
        simp only [evenK, Finset.mem_filter, hs'K, true_and]
        rw [card_symmDiff_mod2]
        have hsp := (Finset.mem_filter.mp hsO).2
        omega
      have hwH0 : (fun i : {i // i ∈ K} => ind s' i.1) ∈ H0 := (hbij_even s' hs'K).mp hs'E
      rw [← hfib_card _ hwH0]
      refine Finset.card_bij (fun z _ => ind (symmDiff z y)) ?_ ?_ ?_
      · intro z hz
        simp only [Finset.mem_filter, models, cube, Finset.mem_univ, true_and] at hz
        simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · rw [bdy_ind, boundaryF_symmDiff]
          change ind (symmDiff (boundary z) (boundary y)) = 0
          rw [hz.1, hby, symmDiff_self, Finset.bot_eq_empty]; ext j; simp [ind]
        · ext ⟨i, hi⟩
          simp only [proj, ind]
          have hmem : i ∈ symmDiff z y ↔ i ∈ s' := by
            simp only [s', ← hz.2, Finset.mem_symmDiff, Finset.mem_inter, hi, and_true]
            by_cases hz' : i ∈ z <;> by_cases hy' : i ∈ y <;> by_cases hx' : i ∈ x <;> simp [hz', hy', hx']
          simp [hmem]
      · intro z1 _ z2 _ h
        have hs'' := ind_injective h
        calc z1 = symmDiff (symmDiff z1 y) y := by simp
          _ = symmDiff (symmDiff z2 y) y := by rw [hs'']
          _ = z2 := by simp
      · intro f hf
        obtain ⟨c, rfl⟩ := ind_surjective f
        simp only [kerB, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        have hbc : boundaryF u v c = ∅ := by
          apply ind_injective; rw [← bdy_ind, hf.1]; ext j; simp [ind]
        refine ⟨symmDiff c y, ?_, by simp⟩
        simp only [Finset.mem_filter, models, cube, Finset.mem_univ, true_and]
        refine ⟨?_, ?_⟩
        · change boundaryF u v (symmDiff c y) = e
          rw [boundaryF_symmDiff, hbc, ← Finset.bot_eq_empty, bot_symmDiff]
          exact hby
        · ext i
          by_cases hiK : i ∈ K
          · have hfi := congrFun hf.2 ⟨i, hiK⟩
            simp only [proj, ind] at hfi
            have hc_iff : i ∈ c ↔ i ∈ s' := by
              by_cases hc : i ∈ c <;> by_cases hs'' : i ∈ s' <;> simp_all
            simp only [s', Finset.mem_symmDiff, Finset.mem_inter, hiK, and_true] at hc_iff ⊢
            by_cases hc : i ∈ c <;> by_cases hy' : i ∈ y <;> by_cases hx' : i ∈ x <;> by_cases hs'' : i ∈ s <;> simp_all
          · have hni : i ∉ s := fun h => hiK (Finset.mem_powerset.mp hsK h)
            simp [Finset.mem_symmDiff, Finset.mem_inter, hiK, hni]
    calc ∑ s ∈ oddK.filter accK, ((models e).filter (fun z => symmDiff (z ∩ K) (x ∩ K) = s)).card
        = ∑ _s ∈ oddK.filter accK, fib0.card := Finset.sum_congr rfl hfib
      _ = (oddK.filter accK).card * fib0.card := by simp
  have hdiff : ((evenK.filter accK).card : Int) - ((oddK.filter accK).card : Int) =
      (-1 : Int) ^ packets.card := by
    have hdisj : Disjoint (evenK.filter accK) (oddK.filter accK) := by
      rw [Finset.disjoint_left]
      intro s h1 h2
      simp only [evenK, oddK, Finset.mem_filter] at h1 h2
      omega
    have hsum_eq : (∑ s ∈ evenK.filter accK ∪ oddK.filter accK, (-1 : Int) ^ s.card) =
        (-1 : Int) ^ packets.card := by
      rw [← sum_partition_factor K packets hpk_sub hpk_part]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext s
      simp only [Finset.mem_union, evenK, oddK, Finset.mem_filter, accK]
      rcases Nat.mod_two_eq_zero_or_one s.card with h0 | h1 <;> constructor <;> intro h <;> simp_all
    rw [← hsum_eq, Finset.sum_union hdisj]
    have hev : (∑ s ∈ evenK.filter accK, (-1 : Int) ^ s.card) = ((evenK.filter accK).card : Int) := by
      calc ∑ s ∈ evenK.filter accK, (-1 : Int) ^ s.card
          = ∑ _s ∈ evenK.filter accK, (1 : Int) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            have h0 := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
            exact (Nat.even_iff.mpr h0).neg_one_pow
        _ = _ := by simp
    have hodd : (∑ s ∈ oddK.filter accK, (-1 : Int) ^ s.card) = -((oddK.filter accK).card : Int) := by
      calc ∑ s ∈ oddK.filter accK, (-1 : Int) ^ s.card
          = ∑ _s ∈ oddK.filter accK, (-1 : Int) := by
            refine Finset.sum_congr rfl fun s hs => ?_
            have h1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
            exact (Nat.odd_iff.mpr h1).neg_one_pow
        _ = _ := by simp
    rw [hev, hodd]; ring
  have hmod_eq : ((models d).card : Int) = (2 : Int) ^ (K.card - 1) * (fib0.card : Int) := by
    rw [hmodels_d_card, hkerB_card_eq, hH0_pow]; push_cast; ring
  rw [hlhs_card, hrhs_card, hmod_eq]
  push_cast
  calc (2 : Int) ^ (K.card - 1) *
        (((evenK.filter accK).card : Int) * (fib0.card : Int) -
         ((oddK.filter accK).card : Int) * (fib0.card : Int))
      = (((evenK.filter accK).card : Int) - ((oddK.filter accK).card : Int)) *
        ((2 : Int) ^ (K.card - 1) * (fib0.card : Int)) := by ring
    _ = (-1 : Int) ^ packets.card * ((2 : Int) ^ (K.card - 1) * (fib0.card : Int)) := by rw [hdiff]

end PEqualNP.Outside.L_lib_1132

theorem PEqualNP.Outside.L_lib_1132 : (∀ (n m : Nat) (u v : Fin m → Fin n) (T : Finset (Fin m)),
  let cube := (Finset.univ : Finset (Finset (Fin m)))
  let vertices := (Finset.univ : Finset (Finset (Fin n)))
  let boundary := fun (x : Finset (Fin m)) =>
    (Finset.univ : Finset (Fin n)).filter (fun j =>
      ((x.filter (fun i => u i = j)).card +
       (x.filter (fun i => v i = j)).card) % 2 = 1)
  let crossing := fun (U : Finset (Fin n)) =>
    (Finset.univ : Finset (Fin m)).filter
      (fun i => decide (u i ∈ U) != decide (v i ∈ U))


  ∀ (d e : Finset (Fin n)) (x : Finset (Fin m)), boundary x = d →
    (∃ y ∈ cube, boundary y = e) →
    let odd := fun (U : Finset (Fin n)) =>
      crossing U ⊆ T ∧ (d ∩ U).card % 2 ≠ (e ∩ U).card % 2
    ∀ U ∈ vertices, odd U → (∀ V ∈ vertices, odd V → (crossing U).card ≤ (crossing V).card) →
      let K := crossing U
      ∀ packets : Finset (Finset (Fin m)),
        (∀ B ∈ packets, B.Nonempty ∧ B ⊆ K) →
        (∀ j ∈ K, ∃! B : Finset (Fin m), B ∈ packets ∧ j ∈ B) →
        let accept := fun (z : Finset (Fin m)) => ∀ B ∈ packets, z ∩ B ≠ x ∩ B
        let models := fun (a : Finset (Fin n)) => cube.filter (fun z => boundary z = a)
        let lhs := ((models d).filter accept).card
        let rhs := ((models e).filter accept).card
        (2 : Int) ^ (K.card - 1) * ((lhs : Int) - (rhs : Int)) =
          (-1 : Int) ^ packets.card * ((models d).card : Int)) :=
  PEqualNP.Outside.L_lib_1132.main_proof
