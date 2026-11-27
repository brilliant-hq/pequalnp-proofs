import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1003_aux


namespace Lib1003Kernel
open Finset

theorem axis_surjective {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {n : Nat} (L : V →ₗ[ZMod 2] (Fin n → ZMod 2)) (v : Fin n → V)
    (hv : ∀ i, L (v i) = Pi.single i 1) : Function.Surjective L := by
  classical
  intro x
  refine ⟨∑ i, x i • v i,?_⟩
  rw [map_sum]
  simp_rw [map_smul,hv,← Pi.single_smul,smul_eq_mul,mul_one]
  exact LinearMap.sum_single_apply _ x

theorem small_subspace {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {n : Nat} (L : V →ₗ[ZMod 2] (Fin n → ZMod 2)) (K : Submodule (ZMod 2) V)
    (hL : Function.Surjective L) (hK : K ≤ L.ker) :
    2^n * Nat.card K ≤ Nat.card V := by
  have hcard := AddSubgroup.card_ker_mul_card_of_surjective
    (f := L.toAddMonoidHom) hL
  have hle : Nat.card K ≤ Nat.card L.toAddMonoidHom.ker :=
    Nat.card_le_card_of_injective
      (fun x : K => (⟨x.1,hK x.2⟩ : L.toAddMonoidHom.ker))
      (fun _ _ h => Subtype.ext (congrArg (fun z : L.toAddMonoidHom.ker => z.val) h))
  have hpow : Nat.card (Fin n → ZMod 2)=2^n := by
    rw [Nat.card_fun,Nat.card_fin,Nat.card_eq_fintype_card,ZMod.card]
  rw [hpow] at hcard
  calc
    2^n * Nat.card K ≤ 2^n * Nat.card L.toAddMonoidHom.ker := Nat.mul_le_mul_left _ hle
    _ = Nat.card V := by simpa only [Nat.mul_comm] using hcard

def eval2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (y : V) : V →ₗ[ZMod 2] ZMod 2 where
  toFun x := B x y
  map_add' := by intros; simp
  map_smul' := by intros; simp

theorem bilinear_kernel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (halt : ∀ x, B x x = 0) (hsym : ∀ x y, B x y = B y x)
    (a b : V) (hab : B a b = 1) : 4 * Nat.card B.ker ≤ Nat.card V := by
  classical
  let L : V →ₗ[ZMod 2] (Fin 2 → ZMod 2) := LinearMap.pi ![eval2 B b,eval2 B a]
  have hv : ∀ i : Fin 2, L (![a,b] i)=Pi.single i 1 := by
    intro i
    funext j
    fin_cases i <;> fin_cases j <;> simp [L,eval2,halt,hab,hsym b a]
  have hL := axis_surjective L ![a,b] hv
  have hK : B.ker ≤ L.ker := by
    intro x hx
    change L x = 0
    funext i
    have hz : B x = 0 := hx
    fin_cases i <;> simp [L,eval2,hz]
  exact small_subspace L B.ker hL hK

def eval3 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (T : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (y z : V) :
    V →ₗ[ZMod 2] ZMod 2 where
  toFun x := T x y z
  map_add' := by intros; simp
  map_smul' := by intros; simp

theorem trilinear_kernel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (T : V →ₗ[ZMod 2] V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (h12 : ∀ x y z, T x y z = T y x z)
    (h23 : ∀ x y z, T x y z = T x z y)
    (halt : ∀ x y, T x x y = 0)
    (a b c : V) (habc : T a b c = 1) : 8 * Nat.card T.ker ≤ Nat.card V := by
  classical
  have hz13 (x y : V) : T x y x = 0 := by rw [h23,halt]
  have hz23 (x y : V) : T x y y = 0 := by rw [h12,hz13]
  have hb : T b a c=1 := by rw [h12,habc]
  have hc : T c a b=1 := by rw [h12,h23,habc]
  let L : V →ₗ[ZMod 2] (Fin 3 → ZMod 2) :=
    LinearMap.pi ![eval3 T b c,eval3 T a c,eval3 T a b]
  have hv : ∀ i : Fin 3, L (![a,b,c] i)=Pi.single i 1 := by
    intro i
    funext j
    fin_cases i <;> fin_cases j <;> simp [L,eval3,halt,hz13,hz23,habc,hb,hc]
  have hL := axis_surjective L ![a,b,c] hv
  have hK : T.ker ≤ L.ker := by
    intro x hx
    change L x = 0
    funext i
    have hz : T x = 0 := hx
    fin_cases i <;> simp [L,eval3,hz]
  exact small_subspace L T.ker hL hK

end Lib1003Kernel




namespace FourSubgroups

theorem intersection_product {G : Type*} [AddGroup G] [Finite G]
    (A B : AddSubgroup G) : Nat.card A * Nat.card B ≤ Nat.card (A ⊓ B : AddSubgroup G) * Nat.card G := by
  have ha := A.card_mul_index
  have hb := B.card_mul_index
  have hc := (A ⊓ B).card_mul_index
  have hi : (A ⊓ B).index ≤ A.index * B.index := AddSubgroup.index_inf_le
  apply Nat.le_of_mul_le_mul_right (c := (A ⊓ B).index) _
    (Nat.pos_of_ne_zero AddSubgroup.index_ne_zero)
  calc
    Nat.card A * Nat.card B * (A ⊓ B).index ≤
        Nat.card A * Nat.card B * (A.index * B.index) := Nat.mul_le_mul_left _ hi
    _ = (Nat.card A * A.index) * (Nat.card B * B.index) := by ring
    _ = Nat.card G * Nat.card G := by rw [ha, hb]
    _ = (Nat.card (A ⊓ B : AddSubgroup G) * Nat.card G) * (A ⊓ B).index := by
      rw [← hc]
      ring

theorem numeric (N a b c d u ib ic id : ℚ)
    (hN : 0 < N) (ha0 : 0 ≤ a)
    (ha : 4*a ≤ N) (hb : 4*b ≤ N) (hc : 4*c ≤ N) (hd : 4*d ≤ N)
    (hu : u ≤ a+b+c+d-ib-ic-id)
    (hib : a*b ≤ ib*N) (hic : a*c ≤ ic*N) (hid : a*d ≤ id*N) :
    16*u ≤ 13*N := by
  have hprod := mul_nonneg (show 0 ≤ N-a by linarith)
    (show 0 ≤ 3*N-4*(b+c+d) by linarith)
  have hnu := mul_le_mul_of_nonneg_left hu hN.le
  have hmid : 4*N*u ≤ 3*N*N+N*a := by nlinarith
  have hlast := mul_nonneg hN.le (show 0 ≤ N-4*a by linarith)
  by_contra h
  have hp := mul_pos hN (show 0 < 16*u-13*N by linarith)
  nlinarith

theorem finset_bound {α : Type*} [DecidableEq α] (A B C D : Finset α) (N : Nat)
    (hN : 0 < N)
    (ha : 4*A.card ≤ N) (hb : 4*B.card ≤ N) (hc : 4*C.card ≤ N) (hd : 4*D.card ≤ N)
    (hib : A.card*B.card ≤ (A ∩ B).card*N)
    (hic : A.card*C.card ≤ (A ∩ C).card*N)
    (hid : A.card*D.card ≤ (A ∩ D).card*N) :
    16*(A ∪ B ∪ C ∪ D).card ≤ 13*N := by
  have hs : A ∪ B ∪ C ∪ D ⊆ A ∪ (B \ A) ∪ (C \ A) ∪ (D \ A) := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_sdiff] at *
    by_cases hxa : x ∈ A <;> aesop
  have hcard := Finset.card_le_card hs
  have h1 := Finset.card_union_le A (B \ A)
  have h2 := Finset.card_union_le (A ∪ (B \ A)) (C \ A)
  have h3 := Finset.card_union_le (A ∪ (B \ A) ∪ (C \ A)) (D \ A)
  have hb' := Finset.card_sdiff_add_card_inter B A
  have hc' := Finset.card_sdiff_add_card_inter C A
  have hd' := Finset.card_sdiff_add_card_inter D A
  rw [Finset.inter_comm B A] at hb'
  rw [Finset.inter_comm C A] at hc'
  rw [Finset.inter_comm D A] at hd'
  have hu : (A ∪ B ∪ C ∪ D).card + (A ∩ B).card + (A ∩ C).card + (A ∩ D).card ≤
      A.card+B.card+C.card+D.card := by omega
  have huq : ((A ∪ B ∪ C ∪ D).card : ℚ) ≤
      A.card+B.card+C.card+D.card-(A ∩ B).card-(A ∩ C).card-(A ∩ D).card := by
    have h : ((A ∪ B ∪ C ∪ D).card : ℚ) + (A ∩ B).card + (A ∩ C).card + (A ∩ D).card ≤
        A.card+B.card+C.card+D.card := by exact_mod_cast hu
    linarith
  have h := numeric N A.card B.card C.card D.card (A ∪ B ∪ C ∪ D).card
    (A ∩ B).card (A ∩ C).card (A ∩ D).card
    (by exact_mod_cast hN) (Nat.cast_nonneg _) (by exact_mod_cast ha)
    (by exact_mod_cast hb) (by exact_mod_cast hc) (by exact_mod_cast hd) huq
    (by exact_mod_cast hib) (by exact_mod_cast hic) (by exact_mod_cast hid)
  exact_mod_cast h

noncomputable def elems {G : Type*} [AddGroup G] [Fintype G] (A : AddSubgroup G) : Finset G := by
  classical
  exact Set.toFinset (A : Set G)

theorem card_elems {G : Type*} [AddGroup G] [Fintype G] (A : AddSubgroup G) :
    (elems A).card = Nat.card A := by
  classical
  simp [elems, Set.toFinset_card, Nat.card_eq_fintype_card]

theorem elems_inf {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G] (A B : AddSubgroup G) :
    elems (A ⊓ B) = elems A ∩ elems B := by
  classical
  ext x
  simp [elems]

theorem bound {G : Type*} [AddGroup G] [Fintype G] [DecidableEq G] (A B C D : AddSubgroup G)
    (ha : 4*Nat.card A ≤ Nat.card G) (hb : 4*Nat.card B ≤ Nat.card G)
    (hc : 4*Nat.card C ≤ Nat.card G) (hd : 4*Nat.card D ≤ Nat.card G) :
    16*(elems A ∪ elems B ∪ elems C ∪ elems D).card ≤ 13*Nat.card G := by
  classical
  apply finset_bound (elems A) (elems B) (elems C) (elems D) (Nat.card G) Nat.card_pos
  · simpa only [card_elems] using ha
  · simpa only [card_elems] using hb
  · simpa only [card_elems] using hc
  · simpa only [card_elems] using hd
  · simpa only [← elems_inf, card_elems] using intersection_product A B
  · simpa only [← elems_inf, card_elems] using intersection_product A C
  · simpa only [← elems_inf, card_elems] using intersection_product A D

end FourSubgroups

namespace CubicPairs
open Finset
theorem count_rows {V : Type*} [Fintype V] (P : V → V → Prop) [DecidableRel P] :
    ((Finset.univ : Finset (V × V)).filter (fun x => P x.1 x.2)).card =
      ∑ a : V, ((Finset.univ : Finset V).filter (P a)).card := by
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact Fintype.sum_prod_type _
theorem rectangle_count {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → V → Prop) [DecidableRel P] (A : Finset V)
    (ha : Fintype.card V ≤ 2*A.card)
    (hb : ∀ a ∈ A, 3*Fintype.card V ≤ 16*((Finset.univ : Finset V).filter (P a)).card) :
    3*(Fintype.card V)^2 ≤
      32*((Finset.univ : Finset (V × V)).filter (fun x => P x.1 x.2)).card := by
  have hs := Finset.sum_le_sum hb
  simp only [Finset.sum_const,smul_eq_mul] at hs
  rw [← Finset.mul_sum] at hs
  have ht : (∑ a ∈ A, ((Finset.univ : Finset V).filter (P a)).card) ≤
      ∑ a : V, ((Finset.univ : Finset V).filter (P a)).card :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ A)
  rw [← count_rows P] at ht
  have hm := Nat.mul_le_mul_left (3*Fintype.card V) ha
  nlinarith

theorem four_eighths {V : Type*} [Fintype V] [DecidableEq V]
    (A B C D : Finset V)
    (ha : 8*A.card ≤ Fintype.card V) (hb : 8*B.card ≤ Fintype.card V)
    (hc : 8*C.card ≤ Fintype.card V) (hd : 8*D.card ≤ Fintype.card V) :
    Fintype.card V ≤ 2*(Finset.univ \ (A ∪ B ∪ C ∪ D)).card := by
  have h1 := Finset.card_union_le A B
  have h2 := Finset.card_union_le (A ∪ B) C
  have h3 := Finset.card_union_le (A ∪ B ∪ C) D
  have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A ∪ B ∪ C ∪ D))
  simp only [Finset.card_univ] at he
  omega

theorem four_quarters {V : Type*} [AddCommGroup V] [Fintype V] [DecidableEq V]
    (A B C D : AddSubgroup V)
    (ha : 4*Nat.card A ≤ Nat.card V) (hb : 4*Nat.card B ≤ Nat.card V)
    (hc : 4*Nat.card C ≤ Nat.card V) (hd : 4*Nat.card D ≤ Nat.card V) :
    3*Fintype.card V ≤
      16*(Finset.univ \ (FourSubgroups.elems A ∪ FourSubgroups.elems B ∪
        FourSubgroups.elems C ∪ FourSubgroups.elems D)).card := by
  have hh := FourSubgroups.bound A B C D ha hb hc hd
  have he := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ
    (FourSubgroups.elems A ∪ FourSubgroups.elems B ∪ FourSubgroups.elems C ∪ FourSubgroups.elems D))
  simp only [Finset.card_univ,Nat.card_eq_fintype_card] at he hh
  omega

theorem linear_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (L : V →ₗ[ZMod 2] ZMod 2) (hL : L ≠ 0) : ∃ x, L x = 1 := by
  by_contra hh
  apply hL
  apply LinearMap.ext
  intro x
  have hx : L x = 0 ∨ L x = 1 := by
    generalize L x = z
    fin_cases z
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hx with hx|hx
  · exact hx
  · exact (hh ⟨x,hx⟩).elim

theorem bilinear_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2) (hB : B ≠ 0) : ∃ a b, B a b=1 := by
  by_contra hh
  apply hB
  apply LinearMap.ext
  intro a
  by_contra ha
  obtain ⟨b,hb⟩ := linear_one (B a) ha
  exact hh ⟨a,b,hb⟩

theorem four_forms {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (T : Fin 4 → V →ₗ[ZMod 2] V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2)
    (h12 : ∀ i x y z, T i x y z = T i y x z)
    (h23 : ∀ i x y z, T i x y z = T i x z y)
    (halt : ∀ i x y, T i x x y = 0)
    (hne : ∀ i, ∃ a b c, T i a b c = 1) :
    3*(Fintype.card V)^2 ≤
      32*((Finset.univ : Finset (V × V)).filter
        (fun x => ∀ i, ∃ c, T i x.1 x.2 c=1)).card := by
  classical
  let K (i : Fin 4) := FourSubgroups.elems (T i).ker.toAddSubgroup
  let A := Finset.univ \ (K 0 ∪ K 1 ∪ K 2 ∪ K 3)
  have hk (i : Fin 4) : 8*(K i).card ≤ Fintype.card V := by
    obtain ⟨a,b,c,h⟩ := hne i
    have hh := Lib1003Kernel.trilinear_kernel (T i) (h12 i) (h23 i) (halt i) a b c h
    change 8*(FourSubgroups.elems (T i).ker.toAddSubgroup).card ≤ Fintype.card V
    rw [FourSubgroups.card_elems]
    change 8*Nat.card (T i).ker ≤ Fintype.card V
    simpa only [Nat.card_eq_fintype_card] using hh
  have ha : Fintype.card V ≤ 2*A.card := four_eighths _ _ _ _ (hk 0) (hk 1) (hk 2) (hk 3)
  apply rectangle_count (fun a b => ∀ i, ∃ c, T i a b c=1) A ha
  intro a ha
  have hna (i : Fin 4) : T i a ≠ 0 := by
    have hh : a ∉ K 0 ∪ K 1 ∪ K 2 ∪ K 3 := (Finset.mem_sdiff.mp ha).2
    simp only [Finset.mem_union,not_or] at hh
    have hmem (j : Fin 4) : a ∈ K j ↔ T j a=0 := by simp [K,FourSubgroups.elems]
    fin_cases i
    · exact fun h => hh.1.1.1 ((hmem 0).mpr h)
    · exact fun h => hh.1.1.2 ((hmem 1).mpr h)
    · exact fun h => hh.1.2 ((hmem 2).mpr h)
    · exact fun h => hh.2 ((hmem 3).mpr h)
  let B (i : Fin 4) := (T i a).ker.toAddSubgroup
  have hb (i : Fin 4) : 4*Nat.card (B i) ≤ Nat.card V := by
    obtain ⟨b,c,h⟩ := bilinear_one (T i a) (hna i)
    apply Lib1003Kernel.bilinear_kernel (T i a) _ (h23 i a) b c h
    intro x
    rw [h12,h23,halt]
  have hbound := four_quarters (B 0) (B 1) (B 2) (B 3) (hb 0) (hb 1) (hb 2) (hb 3)
  have hsub : Finset.univ \ (FourSubgroups.elems (B 0) ∪ FourSubgroups.elems (B 1) ∪
      FourSubgroups.elems (B 2) ∪ FourSubgroups.elems (B 3)) ⊆
      (Finset.univ : Finset V).filter (fun b => ∀ i, ∃ c, T i a b c=1) := by
    intro b hb
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    intro i
    apply linear_one
    have hh := (Finset.mem_sdiff.mp hb).2
    simp only [Finset.mem_union,not_or] at hh
    have hmem (j : Fin 4) : b ∈ FourSubgroups.elems (B j) ↔ T j a b=0 := by
      simp [B,FourSubgroups.elems]
    fin_cases i
    · exact fun h => hh.1.1.1 ((hmem 0).mpr h)
    · exact fun h => hh.1.1.2 ((hmem 1).mpr h)
    · exact fun h => hh.1.2 ((hmem 2).mpr h)
    · exact fun h => hh.2 ((hmem 3).mpr h)
  exact hbound.trans (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))

end CubicPairs



namespace Lib1003
open Finset


theorem binary_cases (x : ZMod 2) : x=0 ∨ x=1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem dual_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    ∃ U : Finset ι, ∀ v, φ v = ∑ i ∈ U, v i := by
  classical
  let U := univ.filter (fun i => φ (Pi.single i 1)=1)
  refine ⟨U,fun v => ?_⟩
  have hv : v = ∑ i, v i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.smul_apply,Pi.single_apply]
  calc
    φ v = φ (∑ i, v i • Pi.single i (1 : ZMod 2)) := congrArg φ hv
    _ = ∑ i, v i * φ (Pi.single i 1) := by simp
    _ = ∑ i ∈ U, v i := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      rcases binary_cases (φ (Pi.single i 1)) with h | h <;> simp [h]

def subsetSum {ι : Type*} (U : Finset ι) : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i ∈ U, v i
  map_add' := by intros; simp [sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum,smul_eq_mul]

theorem fit_iff_subsets {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup V] [Module (ZMod 2) V]
    (P : Submodule (ZMod 2) (ι → ZMod 2)) (T : V →ₗ[ZMod 2] (ι → ZMod 2))
    (h : ι → ZMod 2) :
    (∃ c p, p ∈ P ∧ h = p + T c) ↔
    ∀ U : Finset ι, (∀ p ∈ P, (∑ i ∈ U, p i)=0) →
      (∑ i ∈ U, h i)=1 → ∃ c, (∑ i ∈ U, T c i)=1 := by
  constructor
  · rintro ⟨c,p,hp,rfl⟩ U hU hh
    refine ⟨c,?_⟩
    simpa only [Pi.add_apply,sum_add_distrib,hU p hp,zero_add] using hh
  · intro hh
    have hm : h ∈ P ⊔ LinearMap.range T := by
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ h).mp
      intro φ hφ
      have hz := (Submodule.mem_dualAnnihilator φ).mp hφ
      obtain ⟨U,hU⟩ := dual_subset φ
      rcases binary_cases (φ h) with hf | hf
      · exact hf
      · have hUP : ∀ p ∈ P, (∑ i ∈ U, p i)=0 := by
          intro p hp
          rw [← hU]
          exact hz p (Submodule.mem_sup.mpr ⟨p,hp,0,Submodule.zero_mem _,by simp⟩)
        obtain ⟨c,hc⟩ := hh U hUP (by simpa only [← hU] using hf)
        have ht : φ (T c)=0 := hz (T c)
          (Submodule.mem_sup.mpr ⟨0,Submodule.zero_mem _,T c,LinearMap.mem_range_self T c,by simp⟩)
        rw [hU,hc] at ht
        exact (one_ne_zero ht).elim
    obtain ⟨p,hp,z,hz,he⟩ := Submodule.mem_sup.mp hm
    obtain ⟨c,rfl⟩ := hz
    exact ⟨c,p,hp,he.symm⟩

abbrev State (k : Nat) := Fin k → ZMod 2
def Quad (k : Nat) (f : State k → ZMod 2) : Prop :=
  ∃ (b : ZMod 2) (l : State k) (M : Fin k → Fin k → ZMod 2),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j

def quadSpace (k : Nat) : Submodule (ZMod 2) (State k → ZMod 2) := by
  refine { carrier := {f | Quad k f}, zero_mem' := ?_, add_mem' := ?_, smul_mem' := ?_ }
  ·
    rintro f g ⟨bf,lf,Mf,hf⟩ ⟨bg,lg,Mg,hg⟩
    refine ⟨bf+bg,lf+lg,Mf+Mg,?_⟩
    intro s
    dsimp only [Pi.add_apply]
    rw [hf,hg]
    simp only [dotProduct,Pi.add_apply,add_mul,sum_add_distrib]
    ring
  ·
    refine ⟨0,0,0,?_⟩
    intro s
    simp [dotProduct]
  ·
    rintro c f ⟨bf,lf,Mf,hf⟩
    refine ⟨c*bf,c • lf,c • Mf,?_⟩
    intro s
    dsimp only [Pi.smul_apply,smul_eq_mul]
    rw [hf]
    simp only [dotProduct,Pi.smul_apply,smul_eq_mul,mul_add,Finset.mul_sum,mul_assoc]

def restrict {k : Nat} (E : Finset (State k)) :
    (State k → ZMod 2) →ₗ[ZMod 2] (E → ZMod 2) where
  toFun f s := f s
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def tripleMap {k : Nat} (E : Finset (State k)) (a b : State k) :
    State k →ₗ[ZMod 2] (E → ZMod 2) where
  toFun c s := dotProduct a s * dotProduct b s * dotProduct c s
  map_add' := by
    intro c d
    funext s
    simp [add_dotProduct,mul_add]
  map_smul' := by
    intro r c
    funext s
    simp [smul_dotProduct,smul_eq_mul]
    ring

theorem restricted_fit {k : Nat} (E : Finset (State k)) (h : State k → ZMod 2) (a b : State k) :
    (∃ (c : State k) (f : State k → ZMod 2), Quad k f ∧
      ∀ s ∈ E, h s = f s + dotProduct a s * dotProduct b s * dotProduct c s) ↔
    ∀ U : Finset E,
      (∀ f, Quad k f → (∑ s ∈ U, f s)=0) →
      (∑ s ∈ U, h s)=1 →
      ∃ c : State k, (∑ s ∈ U, dotProduct a s * dotProduct b s * dotProduct c s)=1 := by
  classical
  have hbase := fit_iff_subsets ((quadSpace k).map (restrict E)) (tripleMap E a b) (restrict E h)
  have hleft : (∃ (c : State k) (f : State k → ZMod 2), Quad k f ∧
      ∀ s ∈ E, h s = f s + dotProduct a s * dotProduct b s * dotProduct c s) ↔
      ∃ c p, p ∈ (quadSpace k).map (restrict E) ∧ restrict E h = p + tripleMap E a b c := by
    constructor
    · rintro ⟨c,f,hf,he⟩
      refine ⟨c,restrict E f,Submodule.mem_map.mpr ⟨f,hf,rfl⟩,?_⟩
      funext s
      exact he s s.property
    · rintro ⟨c,p,hp,he⟩
      obtain ⟨f,hf,rfl⟩ := Submodule.mem_map.mp hp
      refine ⟨c,f,hf,fun s hs => ?_⟩
      exact congrFun he ⟨s,hs⟩
  rw [hleft,hbase]
  have hann (U : Finset E) :
      (∀ p ∈ (quadSpace k).map (restrict E), (∑ s ∈ U, p s)=0) ↔
      ∀ f, Quad k f → (∑ s ∈ U, f s)=0 := by
    constructor
    · intro hh f hf
      exact hh (restrict E f) (Submodule.mem_map.mpr ⟨f,hf,rfl⟩)
    · intro hh p hp
      obtain ⟨f,hf,rfl⟩ := Submodule.mem_map.mp hp
      exact hh f hf
  simp_rw [hann]
  rfl

theorem fit_iff_relations {k : Nat} (E : Finset (State k)) (h : State k → ZMod 2) (a b : State k) :
    (∃ (c : State k) (f : State k → ZMod 2), Quad k f ∧
      ∀ s ∈ E, h s = f s + dotProduct a s * dotProduct b s * dotProduct c s) ↔
    ∀ U : Finset (State k), U ⊆ E →
      (∀ f, Quad k f → (∑ s ∈ U, f s)=0) →
      (∑ s ∈ U, h s)=1 →
      ∃ c : State k, (∑ s ∈ U, dotProduct a s * dotProduct b s * dotProduct c s)=1 := by
  classical
  constructor
  · rintro ⟨c,f,hf,he⟩ U hU hann hh
    refine ⟨c,?_⟩
    have hz := Finset.sum_congr rfl (fun s hs => he s (hU hs))
    rw [Finset.sum_add_distrib,hann f hf,zero_add,hh] at hz
    exact hz.symm
  · intro hh
    apply (restricted_fit E h a b).mpr
    intro U hann hodd
    let V := U.image (fun s : E => (s : State k))
    have hsum (f : State k → ZMod 2) : (∑ s ∈ V, f s) = ∑ s ∈ U, f s := by
      exact Finset.sum_image (fun _ _ _ _ he => Subtype.ext he)
    have hV : V ⊆ E := by
      intro s hs
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hs
      exact t.property
    obtain ⟨c,hc⟩ := hh V hV (fun f hf => by rw [hsum]; exact hann f hf)
      (by rw [hsum]; exact hodd)
    exact ⟨c,by simpa only [hsum] using hc⟩

noncomputable def relations {k : Nat} (E : Finset (State k)) : Finset (Finset (State k)) := by
  classical
  exact E.powerset.filter (fun U => ∀ f, Quad k f → (∑ s ∈ U, f s)=0)

theorem exact_fit {k : Nat} (E : Finset (State k)) (h : State k → ZMod 2) (a b : State k) :
    (∃ (c : State k) (f : State k → ZMod 2), Quad k f ∧
      ∀ s ∈ E, h s = f s + dotProduct a s * dotProduct b s * dotProduct c s) ↔
    ∀ U ∈ (relations E).filter (fun U => (∑ s ∈ U, h s)=1),
      ∃ c : State k, (∑ s ∈ U, dotProduct a s * dotProduct b s * dotProduct c s)=1 := by
  classical
  rw [fit_iff_relations]
  simp only [relations,Finset.mem_filter,Finset.mem_powerset]
  constructor
  · intro hh U hU
    exact hh U hU.1.1 hU.1.2 hU.2
  · intro hh U hU hann hodd
    exact hh U ⟨⟨hU,hann⟩,hodd⟩

theorem square_eq (x : ZMod 2) : x*x=x := by
  rcases binary_cases x with rfl|rfl <;> decide

theorem quad_product {k : Nat} (a b : State k) :
    Quad k (fun s => dotProduct a s * dotProduct b s) := by
  refine ⟨0,0,fun i j => a i * b j,?_⟩
  intro s
  simp only [zero_add,dotProduct,Pi.zero_apply,zero_mul,Finset.sum_const_zero,
    Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

def trilinear {k : Nat} (U : Finset (State k)) :
    State k →ₗ[ZMod 2] State k →ₗ[ZMod 2] State k →ₗ[ZMod 2] ZMod 2 where
  toFun a := {
    toFun b := {
      toFun c := ∑ s ∈ U, dotProduct a s * dotProduct b s * dotProduct c s
      map_add' := by intros; simp [add_dotProduct,mul_add,Finset.sum_add_distrib]
      map_smul' := by
        intros
        simp only [smul_dotProduct,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
        apply Finset.sum_congr rfl
        intros
        ring }
    map_add' := by
      intros
      apply LinearMap.ext
      intro c
      simp [add_dotProduct,add_mul,mul_add,Finset.sum_add_distrib]
    map_smul' := by
      intros
      apply LinearMap.ext
      intro c
      change (∑ s ∈ U, dotProduct a s * dotProduct (_ • _) s * dotProduct c s) =
        _ * (∑ s ∈ U, dotProduct a s * dotProduct _ s * dotProduct c s)
      simp only [smul_dotProduct,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
      apply Finset.sum_congr rfl
      intros
      ring }
  map_add' := by
    intros
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    simp [add_dotProduct,add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intros
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    change (∑ s ∈ U, dotProduct (_ • _) s * dotProduct b s * dotProduct c s) =
      _ * (∑ s ∈ U, dotProduct _ s * dotProduct b s * dotProduct c s)
    simp only [smul_dotProduct,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intros
    ring

theorem trilinear_swap12 {k : Nat} (U : Finset (State k)) (a b c : State k) :
    trilinear U a b c = trilinear U b a c := by
  apply Finset.sum_congr rfl
  intros
  ring

theorem trilinear_swap23 {k : Nat} (U : Finset (State k)) (a b c : State k) :
    trilinear U a b c = trilinear U a c b := by
  apply Finset.sum_congr rfl
  intros
  ring

theorem trilinear_alternating {k : Nat} (U : Finset (State k))
    (hU : ∀ f, Quad k f → (∑ s ∈ U, f s)=0) (a b : State k) :
    trilinear U a a b = 0 := by
  change (∑ s ∈ U, dotProduct a s * dotProduct a s * dotProduct b s)=0
  simp_rw [square_eq]
  exact hU _ (quad_product a b)

end Lib1003

namespace CubicFamily
open Finset
theorem enumerate_four {α : Type*} [Fintype α] [Nonempty α] (hcard : Fintype.card α ≤ 4) :
    ∃ f : Fin 4 → α, Function.Surjective f := by
  classical
  let e := Fintype.equivFin α
  let f (i : Fin 4) := if h : i.val < Fintype.card α then e.symm ⟨i.val,h⟩ else Classical.choice ‹Nonempty α›
  refine ⟨f,fun x => ?_⟩
  let i : Fin 4 := ⟨(e x).val,lt_of_lt_of_le (e x).isLt hcard⟩
  refine ⟨i,?_⟩
  simp only [f,i,dif_pos (e x).isLt]
  exact e.symm_apply_apply x

theorem small_family {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    (F : Finset (V →ₗ[ZMod 2] V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2))
    (hcard : F.card ≤ 4)
    (h12 : ∀ T ∈ F, ∀ x y z, T x y z = T y x z)
    (h23 : ∀ T ∈ F, ∀ x y z, T x y z = T x z y)
    (halt : ∀ T ∈ F, ∀ x y, T x x y = 0)
    (hne : ∀ T ∈ F, ∃ a b c, T a b c=1) :
    3*(Fintype.card V)^2 ≤
      32*((Finset.univ : Finset (V × V)).filter
        (fun x => ∀ T ∈ F, ∃ c, T x.1 x.2 c=1)).card := by
  classical
  by_cases hF : F.Nonempty
  · haveI : Nonempty F := hF.to_subtype
    obtain ⟨f,hf⟩ := enumerate_four (α := F) (by simpa using hcard)
    have h := CubicPairs.four_forms (fun i => (f i).val)
      (fun i => h12 _ (f i).property) (fun i => h23 _ (f i).property)
      (fun i => halt _ (f i).property) (fun i => hne _ (f i).property)
    have he : ((Finset.univ : Finset (V × V)).filter
        (fun x => ∀ i, ∃ c, (f i).val x.1 x.2 c=1)) =
        ((Finset.univ : Finset (V × V)).filter
        (fun x => ∀ T ∈ F, ∃ c, T x.1 x.2 c=1)) := by
      ext x
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro hh T hT
        obtain ⟨i,hi⟩ := hf ⟨T,hT⟩
        simpa only [hi] using hh i
      · intro hh i
        exact hh _ (f i).property
    rwa [he] at h
  · have hF := Finset.not_nonempty_iff_eq_empty.mp hF
    subst F
    simp [Fintype.card_prod]
    nlinarith

open scoped Classical in
theorem probability_of_forms {k : Nat} (E : Finset (Lib1003.State k))
    (h : Lib1003.State k → ZMod 2)
    (hcard : (((Lib1003.relations E).filter (fun U => (∑ s ∈ U,h s)=1)).image
      (fun U a b c => ∑ s ∈ U, dotProduct a s * dotProduct b s * dotProduct c s)).card ≤ 4)
    (hne : ∀ U ∈ (Lib1003.relations E).filter (fun U => (∑ s ∈ U,h s)=1),
      ∃ a b c : Lib1003.State k, (∑ s ∈ U,dotProduct a s * dotProduct b s * dotProduct c s)=1) :
    3*2^(2*k) ≤ 32*((Finset.univ : Finset (Lib1003.State k × Lib1003.State k)).filter
      (fun x : Lib1003.State k × Lib1003.State k => ∃ (c : Lib1003.State k) (f : Lib1003.State k → ZMod 2), Lib1003.Quad k f ∧
        ∀ s ∈ E, h s = f s + dotProduct x.1 s * dotProduct x.2 s * dotProduct c s)).card := by
  classical
  let odd := (Lib1003.relations E).filter (fun U => (∑ s ∈ U,h s)=1)
  let F := odd.image Lib1003.trilinear
  let flatten (T : Lib1003.State k →ₗ[ZMod 2] Lib1003.State k →ₗ[ZMod 2]
      Lib1003.State k →ₗ[ZMod 2] ZMod 2) := fun a b c => T a b c
  have hinj : Function.Injective flatten := by
    intro T S he
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply LinearMap.ext
    intro c
    exact congrFun (congrFun (congrFun he a) b) c
  have hFc : F.card ≤ 4 := by
    rw [← Finset.card_image_of_injective F hinj]
    change ((odd.image Lib1003.trilinear).image flatten).card ≤ 4
    rw [Finset.image_image]
    exact hcard
  have hFrel (U : Finset (Lib1003.State k)) (hU : U ∈ odd) :
      ∀ f, Lib1003.Quad k f → (∑ s ∈ U,f s)=0 := by
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hU).1).2
  have hbound := small_family F hFc
    (by rintro T hT; obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hT; exact Lib1003.trilinear_swap12 U)
    (by rintro T hT; obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hT; exact Lib1003.trilinear_swap23 U)
    (by rintro T hT; obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hT; exact Lib1003.trilinear_alternating U (hFrel U hU))
    (by rintro T hT; obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hT; exact hne U hU)
  have heq (a b : Lib1003.State k) : (∀ T ∈ F, ∃ c, T a b c=1) ↔
      ∃ (c : Lib1003.State k) (f : Lib1003.State k → ZMod 2), Lib1003.Quad k f ∧
        ∀ s ∈ E, h s = f s + dotProduct a s * dotProduct b s * dotProduct c s := by
    rw [Lib1003.exact_fit]
    constructor
    · intro hh U hU
      exact hh (Lib1003.trilinear U) (Finset.mem_image.mpr ⟨U,hU,rfl⟩)
    · intro hh T hT
      obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp hT
      exact hh U hU
  simp_rw [heq] at hbound
  have hpow : (Fintype.card (Lib1003.State k))^2 = 2^(2*k) := by
    simp [Lib1003.State,Fintype.card_fun,ZMod.card,← pow_mul,Nat.mul_comm]
  rwa [hpow] at hbound

end CubicFamily



namespace QuadRelationCuts
open Finset
abbrev F := ZMod 2
abbrev S (k : Nat) := Fin k → F

theorem indicator (x y : F) : x+1+y = if x=y then 1 else 0 := by
  fin_cases x <;> fin_cases y <;> decide

theorem distinct_sum (x y : F) (h : x ≠ y) : x+y=1 := by
  fin_cases x <;> fin_cases y <;> first | exact (h rfl).elim | decide

theorem another {k : Nat} (U : Finset (S k)) (v : S k) (hv : v ∈ U)
    (h0 : (∑ s ∈ U, (1 : F))=0) : ∃ w ∈ U, w ≠ v := by
  classical
  by_contra! hn
  have he : U={v} := by ext x; simp only [mem_singleton]; exact ⟨fun h => hn x h, fun h => h ▸ hv⟩
  simp [he] at h0

theorem another_fiber {k : Nat} (U : Finset (S k)) (v : S k) (hv : v ∈ U)
    (h0 : (∑ s ∈ U, (1 : F))=0)
    (h1 : ∀ i, (∑ s ∈ U, s i)=0)
    (h2 : ∀ i j, (∑ s ∈ U, s i*s j)=0) (i j : Fin k) :
    ∃ w ∈ U, w ≠ v ∧ w i=v i ∧ w j=v j := by
  classical
  have hz : (∑ s ∈ U, (s i+1+v i)*(s j+1+v j))=0 := by
    calc
      _ = ∑ s ∈ U, (s i*s j+(1+v j)*s i+(1+v i)*s j+(1+v i)*(1+v j)*1) := by
        apply sum_congr rfl
        intro s hs
        ring
      _ = (∑ s ∈ U, s i*s j)+(1+v j)*(∑ s ∈ U, s i)+(1+v i)*(∑ s ∈ U, s j)+
          (1+v i)*(1+v j)*(∑ s ∈ U, (1 : F)) := by simp only [sum_add_distrib, mul_sum]
      _ = 0 := by rw [h2, h1, h1, h0]; ring
  by_contra! hn
  have ho : (∑ s ∈ U, (s i+1+v i)*(s j+1+v j))=1 := by
    calc
      _ = (v i+1+v i)*(v j+1+v j) := by
        apply sum_eq_single v
        · intro w hw hne
          have h := hn w hw hne
          rw [indicator, indicator]
          split_ifs <;> simp_all
        · intro h
          exact (h hv).elim
      _ = 1 := by rw [indicator, indicator]; simp
  rw [ho] at hz
  exact one_ne_zero hz

theorem tetrahedron {k : Nat} (U : Finset (S k)) (hne : U.Nonempty)
    (h0 : (∑ s ∈ U, (1 : F))=0)
    (h1 : ∀ i, (∑ s ∈ U, s i)=0)
    (h2 : ∀ i j, (∑ s ∈ U, s i*s j)=0) :
    ∃ x0 ∈ U, ∃ x1 ∈ U, ∃ x2 ∈ U, ∃ x3 ∈ U, ∃ i j l : Fin k,
      x1 i ≠ x0 i ∧ x2 i=x0 i ∧ x2 j ≠ x0 j ∧
      x3 i=x0 i ∧ x3 j=x0 j ∧ x3 l ≠ x0 l := by
  classical
  obtain ⟨x0,hx0⟩ := hne
  obtain ⟨x1,hx1,hn1⟩ := another U x0 hx0 h0
  obtain ⟨i,hi⟩ : ∃ i, x1 i ≠ x0 i := by
    by_contra! h
    exact hn1 (funext h)
  obtain ⟨x2,hx2,hn2,he2,_⟩ := another_fiber U x0 hx0 h0 h1 h2 i i
  obtain ⟨j,hj⟩ : ∃ j, x2 j ≠ x0 j := by
    by_contra! h
    exact hn2 (funext h)
  obtain ⟨x3,hx3,hn3,he3,he4⟩ := another_fiber U x0 hx0 h0 h1 h2 i j
  obtain ⟨l,hl⟩ : ∃ l, x3 l ≠ x0 l := by
    by_contra! h
    exact hn3 (funext h)
  exact ⟨x0,hx0,x1,hx1,x2,hx2,x3,hx3,i,j,l,hi,he2,hj,he3,he4,hl⟩

theorem twice (x : F) : x+x=0 := by fin_cases x <;> decide

theorem one_test (x y : F) : (x=1 ↔ y=1) → x=y := by
  intro h
  by_cases hx : x=1
  · exact hx.trans (h.mp hx).symm
  · have hy : y ≠ 1 := fun hy => hx (h.mpr hy)
    have zero_of_not_one (z : F) (hz : z ≠ 1) : z=0 := by
      fin_cases z
      · rfl
      · exact (hz rfl).elim
    rw [zero_of_not_one x hx,zero_of_not_one y hy]

def aff {k : Nat} (x0 : S k) (i j l : Fin k) (c : Fin 4 → F) (s : S k) : F :=
  c 0+c 1*(s i+x0 i)+c 2*(s j+x0 j)+c 3*(s l+x0 l)

noncomputable def cut {k : Nat} (U : Finset (S k)) (x0 : S k) (i j l : Fin k)
    (c : Fin 4 → F) : Finset (S k) := by
  classical
  exact U.filter (fun s => aff x0 i j l c s=1)

theorem cuts_injective {k : Nat} (U : Finset (S k))
    (x0 x1 x2 x3 : S k) (hx0 : x0 ∈ U) (hx1 : x1 ∈ U)
    (hx2 : x2 ∈ U) (hx3 : x3 ∈ U) (i j l : Fin k)
    (hi : x1 i ≠ x0 i) (h2i : x2 i=x0 i) (hj : x2 j ≠ x0 j)
    (h3i : x3 i=x0 i) (h3j : x3 j=x0 j) (hl : x3 l ≠ x0 l) :
    Function.Injective (cut U x0 i j l) := by
  classical
  intro c d hcd
  have value (s : S k) (hs : s ∈ U) : aff x0 i j l c s=aff x0 i j l d s := by
    apply one_test
    have h : s ∈ cut U x0 i j l c ↔ s ∈ cut U x0 i j l d := by rw [hcd]
    simpa only [cut, mem_filter, hs, true_and] using h
  have h0 : c 0=d 0 := by simpa [aff,twice] using value x0 hx0
  have h3 := value x3 hx3
  simp only [aff,h3i,h3j,twice,distinct_sum _ _ hl,mul_zero,add_zero,mul_one] at h3
  rw [h0] at h3
  have h3' : c 3=d 3 := add_left_cancel h3
  have h2 := value x2 hx2
  simp only [aff,h2i,twice,distinct_sum _ _ hj,mul_zero,add_zero,mul_one] at h2
  rw [h0,h3'] at h2
  have h2' : c 2=d 2 := add_left_cancel (add_right_cancel h2)
  have h1 := value x1 hx1
  simp only [aff,distinct_sum _ _ hi,mul_one] at h1
  rw [h0,h2',h3'] at h1
  have h1' : c 1=d 1 := add_left_cancel (add_right_cancel (add_right_cancel h1))
  funext q
  fin_cases q
  · exact h0
  · exact h1'
  · exact h2'
  · exact h3'

theorem sixteen_cuts {k : Nat} (U : Finset (S k)) (hne : U.Nonempty)
    (h0 : (∑ s ∈ U, (1 : F))=0)
    (h1 : ∀ i, (∑ s ∈ U, s i)=0)
    (h2 : ∀ i j, (∑ s ∈ U, s i*s j)=0) :
    ∃ x0 i j l, (Finset.univ.image (cut U x0 i j l)).card=16 := by
  classical
  obtain ⟨x0,hx0,x1,hx1,x2,hx2,x3,hx3,i,j,l,hi,h2i,hj,h3i,h3j,hl⟩ :=
    tetrahedron U hne h0 h1 h2
  refine ⟨x0,i,j,l,?_⟩
  rw [Finset.card_image_of_injective _
    (cuts_injective U x0 x1 x2 x3 hx0 hx1 hx2 hx3 i j l hi h2i hj h3i h3j hl)]
  decide

theorem sum_cut {k : Nat} (U : Finset (S k)) (x0 : S k) (i j l : Fin k)
    (c : Fin 4 → F) (f : S k → F) :
    (∑ s ∈ cut U x0 i j l c, f s) = ∑ s ∈ U, aff x0 i j l c s*f s := by
  classical
  rw [cut, sum_filter]
  apply sum_congr rfl
  intro s hs
  generalize aff x0 i j l c s = a
  have ha : a=0 ∨ a=1 := by
    fin_cases a
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases ha with rfl | rfl <;> simp

theorem moment_cut {k : Nat} (U : Finset (S k)) (x0 : S k) (i j l : Fin k)
    (c : Fin 4 → F) (f : S k → F)
    (hf : (∑ s ∈ U, f s)=0) (hx : ∀ q, (∑ s ∈ U, s q*f s)=0) :
    (∑ s ∈ cut U x0 i j l c, f s)=0 := by
  rw [sum_cut]
  simp only [aff, add_mul, mul_assoc, sum_add_distrib, ← mul_sum, hf, hx, mul_zero, add_zero]

theorem cut_moments {k : Nat} (U : Finset (S k)) (x0 : S k) (i j l : Fin k)
    (c : Fin 4 → F)
    (h0 : (∑ s ∈ U, (1 : F))=0)
    (h1 : ∀ i, (∑ s ∈ U, s i)=0)
    (h2 : ∀ i j, (∑ s ∈ U, s i*s j)=0)
    (h3 : ∀ i j l, (∑ s ∈ U, s i*s j*s l)=0) :
    (∑ s ∈ cut U x0 i j l c, (1 : F))=0 ∧
    (∀ q, (∑ s ∈ cut U x0 i j l c, s q)=0) ∧
    (∀ q r, (∑ s ∈ cut U x0 i j l c, s q*s r)=0) := by
  refine ⟨moment_cut U x0 i j l c _ h0 (by simpa using h1), ?_, ?_⟩
  · intro q
    exact moment_cut U x0 i j l c _ (h1 q) (fun r => h2 r q)
  · intro q r
    exact moment_cut U x0 i j l c _ (h2 q r) (fun p => by simpa only [mul_assoc] using h3 p q r)

theorem annihilate_quad {k : Nat} (U : Finset (S k))
    (h0 : (∑ s ∈ U, (1 : F))=0)
    (h1 : ∀ i, (∑ s ∈ U, s i)=0)
    (h2 : ∀ i j, (∑ s ∈ U, s i*s j)=0)
    (b : F) (l : S k) (M : Fin k → Fin k → F) :
    (∑ s ∈ U, (b + dotProduct l s + (∑ i, ∑ j, M i j*s i*s j)))=0 := by
  have hb : (∑ s ∈ U, b)=0 := by
    have he : (∑ s ∈ U, b)=b*(∑ s ∈ U, (1 : F)) := by simp [mul_comm]
    rw [he,h0,mul_zero]
  have hl : (∑ s ∈ U, dotProduct l s)=0 := by
    change (∑ s ∈ U, ∑ i, l i*s i)=0
    rw [sum_comm]
    simp only [← mul_sum,h1,mul_zero,sum_const_zero]
  have hm : (∑ s ∈ U, ∑ i, ∑ j, M i j*s i*s j)=0 := by
    rw [sum_comm]
    apply sum_eq_zero
    intro i hi
    rw [sum_comm]
    apply sum_eq_zero
    intro j hj
    simp only [mul_assoc,← mul_sum,h2,mul_zero]
  simp only [sum_add_distrib,hb,hl,hm,add_zero]

end QuadRelationCuts

namespace SmallRelations
open Finset Lib1003

theorem quad_one (k : Nat) : Quad k (fun _ => 1) := by
  refine ⟨1,0,0,?_⟩
  intro s
  simp [dotProduct]

theorem dot_basis {k : Nat} (i : Fin k) (s : State k) :
    dotProduct (Pi.single i (1 : ZMod 2)) s = s i := by
  classical
  simp [dotProduct,Pi.single_apply]

theorem quad_coordinate {k : Nat} (i : Fin k) : Quad k (fun s => s i) := by
  refine ⟨0,Pi.single i 1,0,?_⟩
  intro s
  simp [dot_basis]

theorem quad_coordinates {k : Nat} (i j : Fin k) : Quad k (fun s => s i*s j) := by
  simpa only [dot_basis] using quad_product (Pi.single i (1 : ZMod 2)) (Pi.single j (1 : ZMod 2))

theorem relation_moments {k : Nat} (E U : Finset (State k)) (hU : U ∈ relations E) :
    (∑ s ∈ U, (1 : ZMod 2))=0 ∧ (∀ i, (∑ s ∈ U,s i)=0) ∧
      (∀ i j, (∑ s ∈ U,s i*s j)=0) := by
  classical
  have hh := (Finset.mem_filter.mp hU).2
  exact ⟨hh _ (quad_one k),fun i => hh _ (quad_coordinate i),fun i j => hh _ (quad_coordinates i j)⟩

theorem zero_form_large {k : Nat} (E U : Finset (State k))
    (hU : U ∈ relations E) (hne : U.Nonempty)
    (hzero : ∀ a b c : State k, trilinear U a b c=0) : 16 ≤ (relations E).card := by
  classical
  obtain ⟨h0,h1,h2⟩ := relation_moments E U hU
  have h3 (i j l : Fin k) : (∑ s ∈ U,s i*s j*s l)=0 := by
    have hh := hzero (Pi.single i 1) (Pi.single j 1) (Pi.single l 1)
    change (∑ s ∈ U, dotProduct (Pi.single i 1) s *
      dotProduct (Pi.single j 1) s * dotProduct (Pi.single l 1) s)=0 at hh
    simpa only [dot_basis] using hh
  obtain ⟨x0,i,j,l,hcard⟩ := QuadRelationCuts.sixteen_cuts U hne h0 h1 h2
  rw [← hcard]
  apply Finset.card_le_card
  intro C hC
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hC
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_powerset.mpr
    exact (Finset.filter_subset _ _).trans (Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1)
  · intro f hf
    obtain ⟨h0c,h1c,h2c⟩ := QuadRelationCuts.cut_moments U x0 i j l c h0 h1 h2 h3
    obtain ⟨b,a,M,hf⟩ := hf
    simp_rw [hf]
    exact QuadRelationCuts.annihilate_quad _ h0c h1c h2c b a M

theorem small_rel_nonzero {k : Nat} (E : Finset (State k)) (h : State k → ZMod 2)
    (hcard : (relations E).card ≤ 8)
    (U : Finset (State k)) (hU : U ∈ (relations E).filter (fun U => (∑ s ∈ U,h s)=1)) :
    ∃ a b c : State k, (∑ s ∈ U,dotProduct a s * dotProduct b s * dotProduct c s)=1 := by
  classical
  by_contra hn
  have hzero (a b c : State k) : trilinear U a b c=0 := by
    rcases binary_cases (trilinear U a b c) with hz|hz
    · exact hz
    · exact (hn ⟨a,b,c,hz⟩).elim
  have hnonempty : U.Nonempty := by
    by_contra he
    have he := Finset.not_nonempty_iff_eq_empty.mp he
    have hh := (Finset.mem_filter.mp hU).2
    simp [he] at hh
  have hlarge := zero_form_large E U (Finset.mem_filter.mp hU).1 hnonempty hzero
  omega

end SmallRelations



namespace OddRelations
open Finset
open scoped symmDiff

theorem sum_symmDiff {α : Type*} [DecidableEq α] (A B : Finset α) (h : α → ZMod 2) :
    (∑ x ∈ A ∆ B, h x) = (∑ x ∈ A, h x)+(∑ x ∈ B, h x) := by
  have lift (C : Finset α) (hc : C ⊆ A ∪ B) :
      (∑ x ∈ C, h x) = ∑ x ∈ A ∪ B, if x ∈ C then h x else 0 := by
    rw [← sum_filter]
    congr 1
    ext x
    simp only [mem_filter]
    exact ⟨fun hx => ⟨hc hx,hx⟩,fun hx => hx.2⟩
  rw [lift _ Finset.symmDiff_subset_union,lift _ subset_union_left,lift _ subset_union_right,
    ← sum_add_distrib]
  apply sum_congr rfl
  intro x hx
  have twice (a : ZMod 2) : a+a=0 := by fin_cases a <;> decide
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;>
    simp [Finset.mem_symmDiff,ha,hb,twice]

theorem half {α : Type*} [DecidableEq α] (A : Finset α) (p : α → Prop) [DecidablePred p]
    (f : α → α) (hf : ∀ x ∈ A, f x ∈ A)
    (hinv : ∀ x ∈ A, f (f x)=x) (hflip : ∀ x ∈ A, p (f x) ↔ ¬p x) :
    2*(A.filter p).card=A.card := by
  classical
  have he : (A.filter p).card=(A.filter fun x => ¬p x).card := by
    apply card_bij (fun x _ => f x)
    · intro x hx
      obtain ⟨hxa,hxp⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hf x hxa,fun h => (hflip x hxa).mp h hxp⟩
    · intro x hx y hy h
      have h' := congrArg f h
      simpa only [hinv x (mem_filter.mp hx).1,hinv y (mem_filter.mp hy).1] using h'
    · intro y hy
      obtain ⟨hya,hyp⟩ := mem_filter.mp hy
      have hm : f y ∈ A.filter p := mem_filter.mpr ⟨hf y hya,(hflip y hya).mpr hyp⟩
      exact ⟨f y,hm,hinv y hya⟩
  have hc := card_filter_add_card_filter_not (s := A) p
  omega

theorem odd_bound {α : Type*} [DecidableEq α] (R : Finset (Finset α))
    (hc : ∀ U ∈ R, ∀ V ∈ R, U ∆ V ∈ R) (h : α → ZMod 2) :
    2*(R.filter (fun U => (∑ x ∈ U, h x)=1)).card ≤ R.card := by
  classical
  by_cases he : (R.filter (fun U => (∑ x ∈ U, h x)=1)).Nonempty
  · obtain ⟨U,hU⟩ := he
    obtain ⟨hUR,hU1⟩ := mem_filter.mp hU
    have flip (V : Finset α) (hV : V ∈ R) :
        (∑ x ∈ V ∆ U, h x)=1 ↔ ¬(∑ x ∈ V, h x)=1 := by
      rw [sum_symmDiff,hU1]
      generalize (∑ x ∈ V, h x)=a
      have ha : a=0 ∨ a=1 := by
        fin_cases a
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases ha with rfl | rfl
      · simp
      · have hz : (1 : ZMod 2)+1=0 := by decide
        simp [hz]
    exact le_of_eq (half R (fun U => (∑ x ∈ U, h x)=1) (fun V => V ∆ U)
      (fun V hV => hc V hV U hUR) (fun V _ => symmDiff_symmDiff_cancel_right U V) flip)
  · have hempty := Finset.not_nonempty_iff_eq_empty.mp he
    simp [hempty]

end OddRelations

namespace SmallRelations
open Finset Lib1003
open scoped symmDiff

theorem relations_closed {k : Nat} (E : Finset (State k))
    (U : Finset (State k)) (hU : U ∈ relations E)
    (V : Finset (State k)) (hV : V ∈ relations E) : U ∆ V ∈ relations E := by
  classical
  obtain ⟨hUE,hU⟩ := Finset.mem_filter.mp hU
  obtain ⟨hVE,hV⟩ := Finset.mem_filter.mp hV
  refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_,?_⟩
  · exact Finset.symmDiff_subset_union.trans
      (Finset.union_subset (Finset.mem_powerset.mp hUE) (Finset.mem_powerset.mp hVE))
  · intro f hf
    rw [OddRelations.sum_symmDiff,hU f hf,hV f hf,zero_add]

theorem odd_small {k : Nat} (E : Finset (State k)) (h : State k → ZMod 2)
    (hcard : (relations E).card ≤ 8) :
    ((relations E).filter (fun U => (∑ s ∈ U,h s)=1)).card ≤ 4 := by
  have hb := OddRelations.odd_bound (relations E) (relations_closed E) h
  omega

open scoped Classical in
theorem probability {k : Nat} (E : Finset (State k)) (h : State k → ZMod 2)
    (hh : (relations E).card ≤ 8 ∨
      ((((relations E).filter (fun U => (∑ s ∈ U,h s)=1)).image
        (fun U a b c => ∑ s ∈ U, dotProduct a s * dotProduct b s * dotProduct c s)).card ≤ 4 ∧
       ∀ U ∈ (relations E).filter (fun U => (∑ s ∈ U,h s)=1),
        ∃ a b c : State k, (∑ s ∈ U,dotProduct a s * dotProduct b s * dotProduct c s)=1)) :
    3*2^(2*k) ≤ 32*((Finset.univ : Finset (State k × State k)).filter
      (fun x : State k × State k => ∃ (c : State k) (f : State k → ZMod 2), Quad k f ∧
        ∀ s ∈ E, h s = f s + dotProduct x.1 s * dotProduct x.2 s * dotProduct c s)).card := by
  classical
  apply CubicFamily.probability_of_forms
  · rcases hh with hc|hc
    · exact (Finset.card_image_le).trans (odd_small E h hc)
    · exact hc.1
  · rcases hh with hc|hc
    · exact small_rel_nonzero E h hc
    · exact hc.2

end SmallRelations

namespace SharpFive
open Finset
abbrev F := ZMod 2
abbrev V := Fin 18 → F
def pts : Fin 18 → Lib1003.State 5 := ![![0,0,0,0,0],![1,0,0,0,0],![0,1,0,0,0],![1,1,0,0,0],![0,0,1,0,0],![1,0,1,0,0],![0,1,1,0,0],![0,0,0,1,0],![1,0,0,1,0],![0,1,0,1,0],![0,0,1,1,0],![0,0,0,0,1],![1,0,0,0,1],![0,1,0,0,1],![1,1,1,0,0],![1,1,0,1,0],![1,0,1,1,0],![1,1,0,0,1]]
def A : Matrix (Fin 18) (Fin 14) F := ![![1,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,1,0,0,0,0,0,0,0,0,0,0,0,0],![1,0,1,0,0,0,0,0,0,0,0,0,0,0],![1,1,1,1,0,0,0,0,0,0,0,0,0,0],![1,0,0,0,1,0,0,0,0,0,0,0,0,0],![1,1,0,0,1,1,0,0,0,0,0,0,0,0],![1,0,1,0,1,0,1,0,0,0,0,0,0,0],![1,0,0,0,0,0,0,1,0,0,0,0,0,0],![1,1,0,0,0,0,0,1,1,0,0,0,0,0],![1,0,1,0,0,0,0,1,0,1,0,0,0,0],![1,0,0,0,1,0,0,1,0,0,1,0,0,0],![1,0,0,0,0,0,0,0,0,0,0,1,0,0],![1,1,0,0,0,0,0,0,0,0,0,1,1,0],![1,0,1,0,0,0,0,0,0,0,0,1,0,1],![1,1,1,1,1,1,1,0,0,0,0,0,0,0],![1,1,1,1,0,0,0,1,1,1,0,0,0,0],![1,1,0,0,1,1,0,1,1,0,1,0,0,0],![1,1,1,1,0,0,0,0,0,0,0,1,1,1]]
def B : Matrix (Fin 14) (Fin 18) F := ![![1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,1,1,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0],![1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,0,0],![1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0],![1,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0],![1,1,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,0],![1,0,1,0,0,0,0,1,0,1,0,0,0,0,0,0,0,0],![1,0,0,0,1,0,0,1,0,0,1,0,0,0,0,0,0,0],![1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0],![1,1,0,0,0,0,0,0,0,0,0,1,1,0,0,0,0,0],![1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,0,0]]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem inv : B * A = 1 := by decide

theorem inj : Function.Injective A.mulVecLin := by
 have h : B.mulVecLin.comp A.mulVecLin = LinearMap.id := by
  rw [← Matrix.mulVecLin_mul, inv, Matrix.mulVecLin_one]
 have hi : Function.LeftInverse B.mulVecLin A.mulVecLin := fun x => congrArg (fun L => L x) h
 exact hi.injective

theorem rankA : Module.finrank F A.mulVecLin.range = 14 := by
 rw [LinearMap.finrank_range_of_inj inj]
 simp

def poly (c : Fin 14 → F) (s : Lib1003.State 5) : F := c 0 + c 1 * s 0 + c 2 * s 1 + c 3 * s 0 * s 1 + c 4 * s 2 + c 5 * s 0 * s 2 + c 6 * s 1 * s 2 + c 7 * s 3 + c 8 * s 0 * s 3 + c 9 * s 1 * s 3 + c 10 * s 2 * s 3 + c 11 * s 4 + c 12 * s 0 * s 4 + c 13 * s 1 * s 4
set_option maxHeartbeats 0 in
theorem poly_quad (c : Fin 14 → F) : Lib1003.Quad 5 (poly c) := by
 refine ⟨c 0, ![c 1,c 2,c 4,c 7,c 11], ![![0,c 3,c 5,c 8,c 12],![0,0,c 6,c 9,c 13],![0,0,0,c 10,0],![0,0,0,0,0],![0,0,0,0,0]], ?_⟩
 intro s
 simp [poly, dotProduct, Fin.sum_univ_succ]
 ring
set_option maxHeartbeats 0 in
theorem eval_poly (c : Fin 14 → F) : (fun i => poly c (pts i)) = A.mulVecLin c := by
 funext i
 change poly c (pts i) = ∑ j, A i j * c j
 fin_cases i <;> simp [poly,pts,A, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
set_option maxHeartbeats 0 in
theorem eval_quad (f : Lib1003.State 5 → F) (hf : Lib1003.Quad 5 f) :
 (fun i => f (pts i)) ∈ A.mulVecLin.range := by
 obtain ⟨b,l,M,hf⟩ := hf
 refine ⟨![b,l 0 + M 0 0,l 1 + M 1 1,M 0 1 + M 1 0,l 2 + M 2 2,M 0 2 + M 2 0,M 1 2 + M 2 1,l 3 + M 3 3,M 0 3 + M 3 0,M 1 3 + M 3 1,M 2 3 + M 3 2,l 4 + M 4 4,M 0 4 + M 4 0,M 1 4 + M 4 1], ?_⟩
 funext i
 change (∑ j, A i j * _) = f (pts i)
 rw [hf]
 fin_cases i <;> simp [pts,A, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> ring
def evaluate : (Lib1003.State 5 → F) →ₗ[F] V where
 toFun f i := f (pts i)
 map_add' := by intros; rfl
 map_smul' := by intros; rfl

theorem range_eq : (Lib1003.quadSpace 5).map evaluate = A.mulVecLin.range := by
 ext v
 constructor
 · intro hv
   obtain ⟨f,hf,rfl⟩ := Submodule.mem_map.mp hv
   exact eval_quad f hf
 · intro hv
   obtain ⟨c,rfl⟩ := hv
   exact Submodule.mem_map.mpr ⟨poly c,poly_quad c,eval_poly c⟩

theorem finrank_evaluate : Module.finrank F ((Lib1003.quadSpace 5).map evaluate) = 14 := by
 rw [range_eq,rankA]
set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
theorem pts_injective : Function.Injective pts := by decide

def E : Finset (Lib1003.State 5) := Finset.univ.image pts
@[simp] theorem mem_E (i : Fin 18) : pts i ∈ E := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
theorem card_E : E.card = 18 := by rw [E,Finset.card_image_of_injective _ pts_injective]; decide
end SharpFive

namespace BinaryDualCard
open Finset


theorem binary_cases (x : ZMod 2) : x=0 ∨ x=1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem dual_subset {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : Module.Dual (ZMod 2) (ι → ZMod 2)) :
    ∃ U : Finset ι, ∀ v, φ v = ∑ i ∈ U, v i := by
  classical
  let U := univ.filter (fun i => φ (Pi.single i 1)=1)
  refine ⟨U,fun v => ?_⟩
  have hv : v = ∑ i, v i • Pi.single i (1 : ZMod 2) := by
    ext j
    simp [Pi.smul_apply,Pi.single_apply]
  calc
    φ v = φ (∑ i, v i • Pi.single i (1 : ZMod 2)) := congrArg φ hv
    _ = ∑ i, v i * φ (Pi.single i 1) := by simp
    _ = ∑ i ∈ U, v i := by
      rw [sum_filter]
      apply sum_congr rfl
      intro i hi
      rcases binary_cases (φ (Pi.single i 1)) with h | h <;> simp [h]

def subsetSum {ι : Type*} (U : Finset ι) : (ι → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun v := ∑ i ∈ U, v i
  map_add' := by intros; simp [sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum,smul_eq_mul]

def Annihilates {ι : Type*} (P : Submodule (ZMod 2) (ι → ZMod 2)) (U : Finset ι) : Prop :=
  ∀ v ∈ P, (∑ i ∈ U, v i)=0

def toAnnihilator {ι : Type*} (P : Submodule (ZMod 2) (ι → ZMod 2))
    (U : {U : Finset ι // Annihilates P U}) : P.dualAnnihilator :=
  ⟨subsetSum U.val, (Submodule.mem_dualAnnihilator _).mpr U.property⟩

theorem toAnnihilator_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Submodule (ZMod 2) (ι → ZMod 2)) : Function.Injective (toAnnihilator P) := by
  intro A B h
  apply Subtype.ext
  ext i
  have hv := congrArg (fun φ : P.dualAnnihilator => φ.val (Pi.single i 1)) h
  change (∑ j ∈ A.val, (Pi.single i (1 : ZMod 2)) j)=
    (∑ j ∈ B.val, (Pi.single i (1 : ZMod 2)) j) at hv
  by_cases ha : i ∈ A.val <;> by_cases hb : i ∈ B.val <;>
    simp_all [Pi.single_apply]

theorem toAnnihilator_surjective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Submodule (ZMod 2) (ι → ZMod 2)) : Function.Surjective (toAnnihilator P) := by
  intro φ
  obtain ⟨U,hU⟩ := dual_subset φ.val
  have hu : Annihilates P U := by
    intro p hp
    rw [← hU]
    exact (Submodule.mem_dualAnnihilator _).mp φ.property p hp
  refine ⟨⟨U,hu⟩,?_⟩
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  exact (hU v).symm

noncomputable def annihilatorEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Submodule (ZMod 2) (ι → ZMod 2)) :
    {U : Finset ι // Annihilates P U} ≃ P.dualAnnihilator :=
  Equiv.ofBijective (toAnnihilator P)
    ⟨toAnnihilator_injective P,toAnnihilator_surjective P⟩

theorem card_annihilating {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Submodule (ZMod 2) (ι → ZMod 2)) :
    Nat.card {U : Finset ι // Annihilates P U} =
      2^(Fintype.card ι-Module.finrank (ZMod 2) P) := by
  rw [Nat.card_congr (annihilatorEquiv P),Module.natCard_eq_pow_finrank (K := ZMod 2)]
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq P
  rw [Module.finrank_pi] at hd
  have hr : Module.finrank (ZMod 2) P.dualAnnihilator =
      Fintype.card ι-Module.finrank (ZMod 2) P := by omega
  simp [hr,Nat.card_eq_fintype_card]

theorem card_filter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Submodule (ZMod 2) (ι → ZMod 2)) :
    (Finset.univ.filter (fun U : Finset ι => @decide (Annihilates P U) (Classical.propDecidable _))).card =
      2^(Fintype.card ι-Module.finrank (ZMod 2) P) := by
  classical
  let R := Finset.univ.filter (fun U : Finset ι => @decide (Annihilates P U) (Classical.propDecidable _))
  have e : {U : Finset ι // U ∈ R} ≃ {U : Finset ι // Annihilates P U} :=
    Equiv.subtypeEquivRight (fun U => by simp [R])
  change R.card=_
  calc
    R.card = Nat.card {U : Finset ι // U ∈ R} := by simp [Nat.card_eq_fintype_card]
    _ = Nat.card {U : Finset ι // Annihilates P U} := Nat.card_congr e
    _ = _ := card_annihilating P

end BinaryDualCard


namespace SharpCount
open Finset
noncomputable def indexed {k n : Nat} (e : Fin n → Lib1003.State k) : Finset (Finset (Fin n)) := by
 classical
 exact univ.filter (fun U => ∀ f, Lib1003.Quad k f → (∑ i ∈ U, f (e i))=0)

def evaluate {k n : Nat} (e : Fin n → Lib1003.State k) :
 (Lib1003.State k → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2) where
 toFun f i := f (e i)
 map_add' := by intros; rfl
 map_smul' := by intros; rfl

theorem indexed_card {k n : Nat} (e : Fin n → Lib1003.State k) :
 (indexed e).card = 2^(n-Module.finrank (ZMod 2) ((Lib1003.quadSpace k).map (evaluate e))) := by
 classical
 have hh : indexed e = univ.filter (fun U : Finset (Fin n) => @decide
  (BinaryDualCard.Annihilates ((Lib1003.quadSpace k).map (evaluate e)) U) (Classical.propDecidable _)) := by
  ext U
  simp only [indexed,mem_filter,mem_univ,true_and,decide_eq_true_eq]
  constructor
  · intro h v hv
    obtain ⟨f,hf,rfl⟩ := Submodule.mem_map.mp hv
    exact h f hf
  · intro h f hf
    exact h (evaluate e f) (Submodule.mem_map.mpr ⟨f,hf,rfl⟩)
 rw [hh,BinaryDualCard.card_filter]
 simp

theorem relation_image {k n : Nat} (e : Fin n → Lib1003.State k) (he : Function.Injective e) :
 Lib1003.relations (univ.image e) = (indexed e).image (Finset.image e) := by
 classical
 ext U
 constructor
 · intro hu
   have hu' : U ⊆ univ.image e ∧ ∀ f, Lib1003.Quad k f → (∑ s ∈ U,f s)=0 := by
    simpa only [Lib1003.relations,mem_filter,mem_powerset] using hu
   let V := univ.filter (fun i => e i ∈ U)
   have hv : V.image e=U := by
    ext s
    simp only [mem_image,mem_filter,mem_univ,true_and,V]
    constructor
    · rintro ⟨i,hi,rfl⟩; exact hi
    · intro hs
      obtain ⟨i,hi,rfl⟩ := mem_image.mp (hu'.1 hs)
      exact ⟨i,hs,rfl⟩
   refine mem_image.mpr ⟨V,?_,hv⟩
   simp only [indexed,mem_filter,mem_univ,true_and]
   intro f hf
   have hh := hu'.2 f hf
   rw [← hv,Finset.sum_image (fun _ _ _ _ h => he h)] at hh
   exact hh
 · intro hu
   obtain ⟨V,hv,rfl⟩ := mem_image.mp hu
   have hv' : ∀ f, Lib1003.Quad k f → (∑ i ∈ V,f (e i))=0 := by
    simpa only [indexed,mem_filter,mem_univ,true_and] using hv
   simp only [Lib1003.relations,mem_filter,mem_powerset]
   constructor
   · exact Finset.image_subset_image (subset_univ V)
   · intro f hf
     rw [Finset.sum_image (fun _ _ _ _ h => he h)]
     exact hv' f hf

theorem card_image {k n : Nat} (e : Fin n → Lib1003.State k) (he : Function.Injective e) :
 (Lib1003.relations (univ.image e)).card =
  2^(n-Module.finrank (ZMod 2) ((Lib1003.quadSpace k).map (evaluate e))) := by
 rw [relation_image e he,Finset.card_image_of_injective _ (Finset.image_injective he),indexed_card]

theorem sharpFive_card : (Lib1003.relations SharpFive.E).card = 16 := by
 rw [SharpFive.E,card_image _ SharpFive.pts_injective]
 change 2^(18-Module.finrank (ZMod 2) ((Lib1003.quadSpace 5).map SharpFive.evaluate))=16
 rw [SharpFive.finrank_evaluate]
 decide
end SharpCount

namespace SharpPadding
open Finset
abbrev F := ZMod 2
abbrev S := Lib1003.State

def embed (n : Nat) (s : S 5) : S (5+n) := Fin.append s (fun _ => 0)
def project (n : Nat) (s : S (5+n)) : S 5 := fun i => s (Fin.castAdd n i)
@[simp] theorem project_embed (n : Nat) (s : S 5) : project n (embed n s)=s := by
 funext i
 simp [project,embed]
theorem embed_injective (n : Nat) : Function.Injective (embed n) := by
 intro x y h
 simpa using congrArg (project n) h

theorem dot_embed (n : Nat) (a : S (5+n)) (s : S 5) :
 dotProduct a (embed n s) = dotProduct (project n a) s := by
 simp [dotProduct, embed, project, Fin.sum_univ_add]

theorem quad_embed (n : Nat) (f : S (5+n) → F) (hf : Lib1003.Quad (5+n) f) :
 Lib1003.Quad 5 (fun s => f (embed n s)) := by
 obtain ⟨b,l,M,hf⟩ := hf
 refine ⟨b,project n l,fun i j => M (Fin.castAdd n i) (Fin.castAdd n j),?_⟩
 intro s
 dsimp only
 rw [hf,dot_embed]
 simp [embed,Fin.sum_univ_add]

theorem quad_project (n : Nat) (f : S 5 → F) (hf : Lib1003.Quad 5 f) :
 Lib1003.Quad (5+n) (fun s => f (project n s)) := by
 obtain ⟨b,l,M,hf⟩ := hf
 refine ⟨b,embed n l,
  Fin.append (fun i => Fin.append (M i) (fun _ => 0)) (fun _ _ => 0),?_⟩
 intro s
 dsimp only
 rw [hf]
 simp [dotProduct,embed,project,Fin.sum_univ_add]
end SharpPadding

namespace SharpPadding
open Finset

def points (n : Nat) : Fin 18 → S (5+n) := fun i => embed n (SharpFive.pts i)
def E (n : Nat) : Finset (S (5+n)) := univ.image (points n)

theorem points_injective (n : Nat) : Function.Injective (points n) :=
 (embed_injective n).comp SharpFive.pts_injective

theorem range_points (n : Nat) :
 (Lib1003.quadSpace (5+n)).map (SharpCount.evaluate (points n)) = SharpFive.A.mulVecLin.range := by
 ext v
 constructor
 · intro hv
   obtain ⟨f,hf,rfl⟩ := Submodule.mem_map.mp hv
   exact SharpFive.eval_quad (fun s => f (embed n s)) (quad_embed n f hf)
 · intro hv
   obtain ⟨c,rfl⟩ := hv
   refine Submodule.mem_map.mpr ⟨fun s => SharpFive.poly c (project n s),
    quad_project n (SharpFive.poly c) (SharpFive.poly_quad c),?_⟩
   change (fun i => SharpFive.poly c (project n (embed n (SharpFive.pts i)))) = _
   simpa only [project_embed] using SharpFive.eval_poly c

theorem card_relations (n : Nat) : (Lib1003.relations (E n)).card=16 := by
 rw [E,SharpCount.card_image _ (points_injective n),range_points,SharpFive.rankA]
 decide

def NoFit {k : Nat} (E : Finset (S k)) (h : S k → F) : Prop :=
 ∀ a b : S k, ¬ ∃ (c : S k) (f : S k → F), Lib1003.Quad k f ∧
  ∀ s ∈ E, h s=f s+dotProduct a s*dotProduct b s*dotProduct c s

theorem lift_noFit (n : Nat) (h : S 5 → F) (hn : NoFit SharpFive.E h) :
 NoFit (E n) (fun s => h (project n s)) := by
 intro a b hf
 obtain ⟨c,f,hfq,hfit⟩ := hf
 apply hn (project n a) (project n b)
 refine ⟨project n c,fun s => f (embed n s),quad_embed n f hfq,?_⟩
 intro s hs
 have he : embed n s ∈ E n := by
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hs
  exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
 have hh := hfit (embed n s) he
 simpa only [project_embed,dot_embed] using hh

theorem lift_sharpness (h : S 5 → F) (hn : NoFit SharpFive.E h) :
 ∀ k : Nat, 5≤k → ∃ (E : Finset (S k)) (h : S k → F),
  (Lib1003.relations E).card=16 ∧ NoFit E h := by
 intro k hk
 obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le hk
 exact ⟨E n,fun s => h (project n s),card_relations n,lift_noFit n h hn⟩

end SharpPadding

namespace SelectorCubic

def bracket {R : Type*} [CommRing R] (a b c : Fin 5 → R) (i j k : Fin 5) : R :=
  a i * (b j * c k - b k * c j) - a j * (b i * c k - b k * c i) +
    a k * (b i * c j - b j * c i)

set_option maxHeartbeats 1000000 in
theorem plucker {R : Type*} [CommRing R] (a b c : Fin 5 → R) :
    bracket a b c 0 1 2 * bracket a b c 0 3 4 -
    bracket a b c 0 1 3 * bracket a b c 0 2 4 +
    bracket a b c 0 1 4 * bracket a b c 0 2 3 = 0 := by
  simp only [bracket]
  ring

theorem obstruction (a b c : Fin 5 → ZMod 2)
    (h012 : bracket a b c 0 1 2 = 0)
    (h013 : bracket a b c 0 1 3 = 0)
    (h014 : bracket a b c 0 1 4 = 1)
    (h023 : bracket a b c 0 2 3 = 1) : False := by
  have h := plucker a b c
  simp only [h012, h013, h014, h023, zero_mul, sub_zero, one_mul, zero_add] at h
  exact one_ne_zero h

end SelectorCubic

namespace SharpNoFit
open Finset SharpFive

def cube : Fin 4 → Fin 8 → Fin 18 :=
  ![![0,1,2,3,4,5,6,14], ![0,1,2,3,7,8,9,15],
    ![0,1,2,3,11,12,13,17], ![0,1,4,5,7,8,10,16]]

def faces : Fin 4 → Fin 3 → Fin 5 := ![![0,1,2],![0,1,3],![0,1,4],![0,2,3]]

def h (s : Lib1003.State 5) : F := s 0*s 1*s 4+s 0*s 2*s 3

theorem neg_self (x : F) : -x=x := by
  rcases Lib1003.binary_cases x with rfl | rfl
  · rfl
  · change (-1 : ZMod 2)=1
    decide

set_option maxHeartbeats 0 in
theorem poly_cube (v : Fin 14 → F) (q : Fin 4) :
    (∑ t : Fin 8, poly v (pts (cube q t)))=0 := by
  have two : (2 : F)=0 := by decide
  have four : (4 : F)=0 := by decide
  have eight : (8 : F)=0 := by decide
  fin_cases q <;> simp [cube,poly,pts,Fin.sum_univ_succ] <;> ring_nf <;> simp [two,four,eight]

theorem quad_cube (f : Lib1003.State 5 → F) (hf : Lib1003.Quad 5 f) (q : Fin 4) :
    (∑ t : Fin 8, f (pts (cube q t)))=0 := by
  obtain ⟨v,hv⟩ := eval_quad f hf
  have he : ∀ i, f (pts i)=poly v (pts i) := by
    intro i
    have h1 := congrFun hv i
    have h2 := congrFun (eval_poly v) i
    exact h1.symm.trans h2.symm
  simp_rw [he]
  exact poly_cube v q

set_option maxHeartbeats 0 in
theorem triple_cube (a b c : Lib1003.State 5) (q : Fin 4) :
    (∑ t : Fin 8, dotProduct a (pts (cube q t))*dotProduct b (pts (cube q t))*
      dotProduct c (pts (cube q t)))=
    SelectorCubic.bracket a b c (faces q 0) (faces q 1) (faces q 2) := by
  have two : (2 : F)=0 := by decide
  have four : (4 : F)=0 := by decide
  fin_cases q <;> simp [cube,faces,pts,dotProduct,Fin.sum_univ_succ,SelectorCubic.bracket,
    sub_eq_add_neg,neg_self] <;> ring_nf <;> simp [two,four]

theorem h_cube : ∀ q : Fin 4, (∑ t : Fin 8, h (pts (cube q t)))=(![0,0,1,1] : Fin 4 → F) q := by
  decide

theorem no_fit (a b : Lib1003.State 5) :
    ¬∃ (c : Lib1003.State 5) (f : Lib1003.State 5 → F), Lib1003.Quad 5 f ∧
      ∀ s ∈ E, h s=f s+dotProduct a s*dotProduct b s*dotProduct c s := by
  rintro ⟨c,f,hf,he⟩
  have hc (q : Fin 4) :
      (![0,0,1,1] : Fin 4 → F) q =
      SelectorCubic.bracket a b c (faces q 0) (faces q 1) (faces q 2) := by
    have hs : (∑ t : Fin 8, h (pts (cube q t))) =
        ∑ t : Fin 8, (f (pts (cube q t))+dotProduct a (pts (cube q t))*
          dotProduct b (pts (cube q t))*dotProduct c (pts (cube q t))) := by
      apply sum_congr rfl
      intro t ht
      exact he _ (mem_E _)
    rw [sum_add_distrib,quad_cube f hf q,zero_add,triple_cube,h_cube] at hs
    exact hs
  exact SelectorCubic.obstruction a b c
    (by simpa [faces] using (hc 0).symm)
    (by simpa [faces] using (hc 1).symm)
    (by simpa [faces] using (hc 2).symm)
    (by simpa [faces] using (hc 3).symm)

end SharpNoFit

namespace Lib1003First
set_option maxHeartbeats 50000 in
theorem first_part : ∀ k : ℕ,
  let F := ZMod 2
  let S := Fin k → F
  let quad := fun (f : S → F) => ∃ (b : F) (l : S) (M : Fin k → Fin k → F),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
  let rel := fun (E : Finset S) => E.powerset.filter (fun U => @decide
    (∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0) (Classical.propDecidable _))
  let triple := fun (a b c s : S) => dotProduct a s * dotProduct b s * dotProduct c s
  let sig := fun (U : Finset S) (a b c : S) => ∑ s ∈ U, triple a b c s
  let fit := fun (E : Finset S) (h : S → F) (a b : S) =>
    ∃ (c : S) (f : S → F), quad f ∧ ∀ s ∈ E, h s = f s + triple a b c s
  (∀ (E : Finset S) (h : S → F),
    let odd := (rel E).filter (fun U => (∑ s ∈ U, h s) = 1)
    let forms := odd.image sig
    (∀ a b : S, fit E h a b ↔ ∀ U ∈ odd, ∃ c : S, sig U a b c = 1) ∧
    ((rel E).card ≤ 8 ∨ (forms.card ≤ 4 ∧ ∀ U ∈ odd, ∃ a b c : S, sig U a b c = 1) →
      let pairs := (Finset.univ : Finset (S × S)).filter
        (fun v => @decide (fit E h v.1 v.2) (Classical.propDecidable _))
      3 * 2^(2*k) ≤ 32 * pairs.card)) := by
  classical
  intro k
  dsimp only
  intro E h
  have hrel : E.powerset.filter (fun U => @decide
    (∀ f : Lib1003.State k → ZMod 2, (∃ (b : ZMod 2) (l : Lib1003.State k)
       (M : Fin k → Fin k → ZMod 2),
       ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j) →
       (∑ s ∈ U, f s)=0) (Classical.propDecidable _)) = Lib1003.relations E := by
    ext U
    simp [Lib1003.relations,Lib1003.Quad]
  rw [hrel]
  constructor
  · intro a b
    exact Lib1003.exact_fit E h a b
  · intro hh
    have hp := SmallRelations.probability E h hh
    have hpairs :
      (Finset.univ : Finset (Lib1003.State k × Lib1003.State k)).filter
        (fun v => @decide (∃ (c : Lib1003.State k) (f : Lib1003.State k → ZMod 2),
          (∃ (b : ZMod 2) (l : Lib1003.State k) (M : Fin k → Fin k → ZMod 2),
           ∀ s, f s=b+dotProduct l s+∑ i,∑ j,M i j*s i*s j) ∧
          ∀ s ∈ E, h s=f s+dotProduct v.1 s*dotProduct v.2 s*dotProduct c s)
          (Classical.propDecidable _)) =
      (Finset.univ : Finset (Lib1003.State k × Lib1003.State k)).filter
        (fun v => ∃ (c : Lib1003.State k) (f : Lib1003.State k → ZMod 2),
          Lib1003.Quad k f ∧ ∀ s ∈ E,
          h s=f s+dotProduct v.1 s*dotProduct v.2 s*dotProduct c s) := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,decide_eq_true_eq]
      rfl
    rw [hpairs]
    exact hp
end Lib1003First

end PEqualNP.Outside.L_lib_1003_aux

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4096 in
open PEqualNP.Outside.L_lib_1003_aux in
theorem PEqualNP.Outside.L_lib_1003 : ∀ k : ℕ,
  let F := ZMod 2
  let S := Fin k → F
  let quad := fun (f : S → F) => ∃ (b : F) (l : S) (M : Fin k → Fin k → F),
    ∀ s, f s = b + dotProduct l s + ∑ i, ∑ j, M i j * s i * s j
  let rel := fun (E : Finset S) => E.powerset.filter (fun U => @decide
    (∀ f : S → F, quad f → (∑ s ∈ U, f s) = 0) (Classical.propDecidable _))
  let triple := fun (a b c s : S) => dotProduct a s * dotProduct b s * dotProduct c s
  let sig := fun (U : Finset S) (a b c : S) => ∑ s ∈ U, triple a b c s
  let fit := fun (E : Finset S) (h : S → F) (a b : S) =>
    ∃ (c : S) (f : S → F), quad f ∧ ∀ s ∈ E, h s = f s + triple a b c s
  (∀ (E : Finset S) (h : S → F),
    let odd := (rel E).filter (fun U => (∑ s ∈ U, h s) = 1)
    let forms := odd.image sig
    (∀ a b : S, fit E h a b ↔ ∀ U ∈ odd, ∃ c : S, sig U a b c = 1) ∧
    ((rel E).card ≤ 8 ∨ (forms.card ≤ 4 ∧ ∀ U ∈ odd, ∃ a b c : S, sig U a b c = 1) →
      let pairs := (Finset.univ : Finset (S × S)).filter
        (fun v => @decide (fit E h v.1 v.2) (Classical.propDecidable _))
      3 * 2^(2*k) ≤ 32 * pairs.card)) ∧
  (5 ≤ k → ∃ (E : Finset S) (h : S → F), (rel E).card = 16 ∧
    ∀ a b : S, ¬ fit E h a b) := by
  classical
  intro k
  dsimp only
  constructor
  · exact Lib1003First.first_part k
  · intro hk
    obtain ⟨E,h,hcard,hn⟩ := SharpPadding.lift_sharpness SharpNoFit.h SharpNoFit.no_fit k hk
    refine ⟨E,h,?_,hn⟩
    have hr : E.powerset.filter (fun U => @decide
        (∀ f : Lib1003.State k → ZMod 2,
          (∃ (b : ZMod 2) (l : Lib1003.State k) (M : Fin k → Fin k → ZMod 2),
            ∀ s, f s=b+dotProduct l s+∑ i,∑ j,M i j*s i*s j) → (∑ s ∈ U,f s)=0)
        (Classical.propDecidable _)) = Lib1003.relations E := by
      ext U
      simp [Lib1003.relations,Lib1003.Quad]
    rw [hr]
    exact hcard
