import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_814

open Finset

theorem sig {K W V : Type} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [AddCommGroup V] [Module K V] (f g : W →ₗ[K] V) (h : LinearMap.range f = LinearMap.range g) :
    ∃ σ : W →ₗ[K] W, Function.Surjective σ ∧ ∀ w, f (σ w) = g w := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  let g' : W →ₗ[K] LinearMap.range f :=
    g.codRestrict (LinearMap.range f) (fun x => h ▸ LinearMap.mem_range_self g x)
  have hfs : ∀ y, f (s y) = (y : V) := by
    intro y
    have := congrArg (fun φ => (φ y : V)) hs
    simpa using this
  have hdim : Module.finrank K (LinearMap.ker g) = Module.finrank K (LinearMap.ker f) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    have h2 := LinearMap.finrank_range_add_finrank_ker g
    rw [h] at h1
    omega
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.ker g).subtype
    (Submodule.ker_subtype _)
  let ι := LinearEquiv.ofFinrankEq _ _ hdim
  let σ : W →ₗ[K] W := s.comp g' + (LinearMap.ker f).subtype.comp (ι.toLinearMap.comp π)
  have hσ : ∀ w, f (σ w) = g w := by
    intro w
    have h3 : f ((ι (π w) : W)) = 0 := (ι (π w)).2
    simp only [σ, LinearMap.add_apply, LinearMap.comp_apply, map_add, hfs, Submodule.subtype_apply,
      LinearEquiv.coe_coe, h3, add_zero]
    rfl
  refine ⟨σ, ?_, hσ⟩
  rw [← LinearMap.injective_iff_surjective]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hgx : g x = 0 := by rw [← hσ, hx, map_zero]
  have hg' : g' x = 0 := Subtype.ext hgx
  have hπx : π x = ⟨x, hgx⟩ := by
    have := congrArg (fun φ => φ ⟨x, hgx⟩) hπ
    simpa using this
  have h4 : ((ι (π x) : W)) = 0 := by
    have : σ x = s (g' x) + ((ι (π x) : W)) := rfl
    rw [hx, hg', map_zero, zero_add] at this
    exact this.symm
  have h5 : ι (π x) = 0 := Subtype.ext h4
  rw [LinearEquiv.map_eq_zero_iff, hπx] at h5
  exact congrArg Subtype.val h5


def nx (n : ℕ) (i : Fin n) : Fin n :=
  ⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩

theorem memf {α : Type} {inst : Fintype α} {p : α → Prop} {d : DecidablePred p} (x : α) :
    x ∈ @Finset.filter α p d (@Finset.univ α inst) ↔ p x := by
  simp

noncomputable def good (n m j : ℕ) (h : Fin n → Fin m → ZMod 2) (Y : Fin j → Fin m → ZMod 2) :
    Finset (Fin n → Fin j → ZMod 2) :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  let next := fun i : Fin n =>
    (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ : Fin n)
  (Finset.univ : Finset (Fin n → Fin j → ZMod 2)).filter (fun x =>
      (∀ i, x i = 0 ∨ x (next i) = 0 ∨ x i = x (next i)) ∧
      (∀ b : Fin j, ∀ a : Fin m, (∑ i, h i a * x i b) = Y b a))

def Ok {n j : ℕ} (x : Fin n → Fin j → ZMod 2) : Prop :=
  ∀ i, x i = 0 ∨ x (nx n i) = 0 ∨ x i = x (nx n i)

def Syn {n m j : ℕ} (h : Fin n → Fin m → ZMod 2) (x : Fin n → Fin j → ZMod 2)
    (Y : Fin j → Fin m → ZMod 2) : Prop :=
  ∀ b : Fin j, ∀ a : Fin m, (∑ i, h i a * x i b) = Y b a

theorem mem_good {n m j : ℕ} (h : Fin n → Fin m → ZMod 2) (Y : Fin j → Fin m → ZMod 2)
    (x : Fin n → Fin j → ZMod 2) : x ∈ good n m j h Y ↔ Ok x ∧ Syn h x Y := by
  unfold good
  exact memf _

def cs {m j : ℕ} (Y : Fin j → Fin m → ZMod 2) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range Y)

theorem card_le {n m j : ℕ} (h : Fin n → Fin m → ZMod 2) (Y Z : Fin j → Fin m → ZMod 2)
    (hYZ : cs Y = cs Z) : (good n m j h Y).card ≤ (good n m j h Z).card := by
  let fY := Fintype.linearCombination (ZMod 2) Y
  let fZ := Fintype.linearCombination (ZMod 2) Z
  have hr : LinearMap.range fY = LinearMap.range fZ := by
    simp only [fY, fZ, Fintype.range_linearCombination]
    exact hYZ
  obtain ⟨σ, hsurj, hσ⟩ := sig fY fZ hr
  let D : (Fin j → ZMod 2) → (Fin j → ZMod 2) := fun c b =>
    Fintype.linearCombination (ZMod 2) c (σ (Pi.single b 1))
  have D0 : D 0 = 0 := by
    funext b
    simp [D, Fintype.linearCombination_apply]
  have Dinj : Function.Injective D := by
    intro c c' hD
    have hcomp : (Fintype.linearCombination (ZMod 2) c).comp σ =
        (Fintype.linearCombination (ZMod 2) c').comp σ := by
      refine (Pi.basisFun (ZMod 2) (Fin j)).ext (fun b => ?_)
      simpa [Pi.basisFun_apply] using congrFun hD b
    funext k
    obtain ⟨u, hu⟩ := hsurj (Pi.single k 1)
    have := LinearMap.congr_fun hcomp u
    simpa [hu, Fintype.linearCombination_apply_single] using this
  have hZ : ∀ b a, Z b a = ∑ b', σ (Pi.single b 1) b' * Y b' a := by
    intro b a
    have h1 := hσ (Pi.single b 1)
    simp only [fZ, Fintype.linearCombination_apply_single, one_smul] at h1
    rw [← h1]
    simp [fY, Fintype.linearCombination_apply, Finset.sum_apply]
  refine Finset.card_le_card_of_injOn (fun x i => D (x i)) ?_ ?_
  · intro x hx
    rw [Finset.mem_coe, mem_good] at hx ⊢
    obtain ⟨hok, hsyn⟩ := hx
    refine ⟨fun i => ?_, fun b a => ?_⟩
    · rcases hok i with e | e | e
      · left; simp only [e, D0]
      · right; left; simp only [e, D0]
      · right; right; simp only [e]
    · rw [hZ]
      simp only [D, Fintype.linearCombination_apply, smul_eq_mul]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b' _ => ?_)
      rw [← hsyn b' a, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
  · intro x _ y _ hxy
    funext i
    exact Dinj (congrFun hxy i)


theorem nx_val {n : ℕ} (i : Fin n) : (nx n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  have := i.isLt
  unfold nx
  simp only
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

theorem nx_inj {n : ℕ} : Function.Injective (nx n) := by
  intro a b hab
  have hv := congrArg Fin.val hab
  rw [nx_val, nx_val] at hv
  have := a.isLt
  have := b.isLt
  ext
  split_ifs at hv <;> omega

theorem cyc {n : ℕ} (P : Fin n → Prop) (i0 : Fin n) (h0 : P i0)
    (hs : ∀ i, P i → P (nx n i)) : ∀ i, P i := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
  have key : ∀ k : ℕ, ∀ i : Fin n, i.val = (i0.val + k) % n → P i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : i = i0 := Fin.ext (by rw [hi, add_zero, Nat.mod_eq_of_lt i0.isLt])
      rw [this]; exact h0
    | succ k ih =>
      intro i hi
      let i' : Fin n := ⟨(i0.val + k) % n, Nat.mod_lt _ hn⟩
      have h1 := hs i' (ih i' rfl)
      have e : nx n i' = i := by
        apply Fin.ext
        show ((i0.val + k) % n + 1) % n = i.val
        rw [Nat.mod_add_mod, hi, add_assoc]
      rw [e] at h1
      exact h1
  intro i
  apply key (n - i0.val + i.val)
  have := i0.isLt
  have := i.isLt
  rw [show i0.val + (n - i0.val + i.val) = n + i.val by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt i.isLt]

noncomputable def bnd (n : ℕ) : ℕ :=
  letI : ∀ p : Prop, Decidable p := Classical.propDecidable
  if n = 0 then 0 else max 1 (n / 2)

theorem vals_le {n j : ℕ} (x : Fin n → Fin j → ZMod 2) (hx : Ok x) :
    ((univ.image x).filter (· ≠ 0)).card ≤ bnd n := by
  by_cases hn : n = 0
  · subst hn
    simp [bnd]
  have hb : bnd n = max 1 (n / 2) := by unfold bnd; exact if_neg hn
  rw [hb]
  by_cases hz : ∃ z, x z = 0
  · obtain ⟨z, hz⟩ := hz
    let E := univ.filter (fun i => x i ≠ 0 ∧ x (nx n i) = 0)
    have h1 : (univ.image x).filter (· ≠ 0) ⊆ E.image x := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨⟨i, rfl⟩, hv0⟩ := hv
      by_contra hne
      have hcl : ∀ e, x e = x i → x (nx n e) = x i := by
        intro e he
        rcases hx e with e1 | e1 | e1
        · exact absurd (he ▸ e1) hv0
        · exact absurd (Finset.mem_image.2 ⟨e, by simp [E, e1, he, hv0], he⟩) hne
        · rw [← e1, he]
      have := cyc (fun e => x e = x i) i rfl hcl z
      exact hv0 (this ▸ hz)
    have h2 : 2 * E.card ≤ n := by
      have hd : Disjoint E (E.image (nx n)) := by
        rw [Finset.disjoint_left]
        intro a ha ha'
        obtain ⟨b, hb, hba⟩ := Finset.mem_image.1 ha'
        simp only [E, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
        rw [hba] at hb
        exact ha.1 hb.2
      have := Finset.card_le_univ (E ∪ E.image (nx n))
      rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ nx_inj,
        Fintype.card_fin] at this
      omega
    have h3 := (Finset.card_le_card h1).trans Finset.card_image_le
    have : E.card ≤ n / 2 := by omega
    exact (h3.trans this).trans (le_max_right _ _)
  · push Not at hz
    let i0 : Fin n := ⟨0, by omega⟩
    have hall := cyc (fun e => x e = x i0) i0 rfl (fun e he => by
      rcases hx e with e1 | e1 | e1
      · exact absurd e1 (hz e)
      · exact absurd e1 (hz _)
      · rw [← e1, he])
    have : (univ.image x).filter (· ≠ 0) ⊆ {x i0} := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and] at hv
      obtain ⟨⟨i, rfl⟩, _⟩ := hv
      simp [hall i]
    exact (Finset.card_le_card this).trans (by simp)

theorem rk_le {n m j : ℕ} (h : Fin n → Fin m → ZMod 2) (x : Fin n → Fin j → ZMod 2)
    (Y : Fin j → Fin m → ZMod 2) (hs : Syn h x Y) :
    Module.finrank (ZMod 2) (cs Y) ≤ ((univ.image x).filter (· ≠ 0)).card := by
  let M : Matrix (Fin j) (Fin m) (ZMod 2) := Y
  have e1 : Module.finrank (ZMod 2) (cs Y) = M.rank := (Matrix.rank_eq_finrank_span_row M).symm
  have e2 : M.rank = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range M.transpose)) := by
    rw [← Matrix.rank_transpose, Matrix.rank_eq_finrank_span_row]
    rfl
  rw [e1, e2]
  let S := (univ.image x).filter (· ≠ 0)
  have hle : Submodule.span (ZMod 2) (Set.range M.transpose) ≤ Submodule.span (ZMod 2) (S : Set _) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hT : M.transpose a = ∑ i, h i a • x i := by
      funext b
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, M]
      exact (hs b a).symm
    rw [hT]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    by_cases h0 : x i = 0
    · rw [h0]; exact Submodule.zero_mem _
    · apply Submodule.subset_span
      simp [S, h0]
  exact (Submodule.finrank_mono hle).trans (finrank_span_finset_le_card S)

theorem tbl_low {n m j : ℕ} (h : Fin n → Fin m → ZMod 2) (Y : Fin j → Fin m → ZMod 2)
    (hY : bnd n < Module.finrank (ZMod 2) (cs Y)) : (good n m j h Y).card = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_good] at hx
  have := (rk_le h x Y hx.2).trans (vals_le x hx.1)
  omega

theorem constr {n m j : ℕ} (Y0 : Fin j → Fin m → ZMod 2)
    (hr : Module.finrank (ZMod 2) (cs Y0) ≤ bnd n) :
    ∃ h : Fin n → Fin m → ZMod 2, 0 < (good n m j h Y0).card ∧
      ∀ Y, (good n m j h Y).card ≠ 0 → cs Y ≤ cs Y0 := by
  set r := Module.finrank (ZMod 2) (cs Y0) with hrdef
  have hr' : r = 0 ∨ (n ≠ 0 ∧ (r ≤ 1 ∨ r ≤ n / 2)) := by
    unfold bnd at hr
    by_cases hn : n = 0
    · rw [if_pos hn] at hr; omega
    · rw [if_neg hn, le_max_iff] at hr; omega
  have hk : ∀ k < r, 2 * k < n := by intro k hk; omega
  have hwrap : ∀ k < r, 2 * k + 1 = n → k = 0 := by intro k hk; omega
  let β := Module.finBasis (ZMod 2) (cs Y0)
  let φ : Fin r → Fin n := fun k => ⟨2 * k.val, hk k k.isLt⟩
  have φinj : Function.Injective φ := by
    intro a b hab
    have := congrArg Fin.val hab
    simp only [φ] at this
    ext; omega
  let hv : Fin r → (Fin m → ZMod 2) := fun k => (β k : Fin m → ZMod 2)
  let c : Fin r → Fin j → ZMod 2 := fun k b => β.repr ⟨Y0 b, Submodule.subset_span ⟨b, rfl⟩⟩ k
  let h : Fin n → Fin m → ZMod 2 := Function.extend φ hv 0
  let xs : Fin n → Fin j → ZMod 2 := Function.extend φ c 0
  have hin : ∀ k, h (φ k) = hv k := fun k => φinj.extend_apply _ _ _
  have hout : ∀ i, (¬∃ k, φ k = i) → h i = 0 := fun i hi => by
    simp only [h, Function.extend_apply' _ _ _ hi, Pi.zero_apply]
  have xin : ∀ k, xs (φ k) = c k := fun k => φinj.extend_apply _ _ _
  have xout : ∀ i, (¬∃ k, φ k = i) → xs i = 0 := fun i hi => by
    simp only [xs, Function.extend_apply' _ _ _ hi, Pi.zero_apply]
  refine ⟨h, ?_, ?_⟩
  · apply Finset.card_pos.2
    refine ⟨xs, (mem_good _ _ _).2 ⟨fun i => ?_, fun b a => ?_⟩⟩
    · by_cases hi : ∃ k, φ k = i
      · obtain ⟨k, rfl⟩ := hi
        by_cases hw : 2 * k.val + 1 = n
        · have k0 := hwrap k k.isLt hw
          have e : nx n (φ k) = φ k := by
            apply Fin.ext
            rw [nx_val]
            simp only [φ]
            rw [if_pos hw]
            omega
          right; right; rw [e]
        · right; left
          apply xout
          rintro ⟨k', hk'⟩
          have := congrArg Fin.val hk'
          rw [nx_val] at this
          simp only [φ] at this
          rw [if_neg hw] at this
          omega
      · left; exact xout i hi
    · rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image φ)) (fun i _ hi => by
        rw [hout i (fun ⟨k, hk⟩ => hi (Finset.mem_image.2 ⟨k, Finset.mem_univ _, hk⟩))]
        simp)]
      rw [Finset.sum_image (fun a _ b _ hab => φinj hab)]
      simp only [hin, xin]
      have := congrArg (fun v : cs Y0 => (v : Fin m → ZMod 2) a)
        (β.sum_repr ⟨Y0 b, Submodule.subset_span ⟨b, rfl⟩⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      simp only [hv, c]
      ring
  · intro Y hY
    obtain ⟨x, hx⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hY)
    have hsyn := ((mem_good _ _ _).1 hx).2
    rw [cs, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hYb : Y b = ∑ i, x i b • h i := by
      funext a
      rw [← hsyn b a, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [SetLike.mem_coe, hYb]
    refine Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ ?_)
    by_cases hi : ∃ k, φ k = i
    · obtain ⟨k, rfl⟩ := hi
      rw [hin]
      exact (β k).2
    · rw [hout i hi]; exact Submodule.zero_mem _

noncomputable def tb (n m j : ℕ) (h : Fin n → Fin m → ZMod 2) :
    (Fin j → Fin m → ZMod 2) → ℚ := fun Y => ((good n m j h Y).card : ℚ)

def Inv {m j : ℕ} (g : (Fin j → Fin m → ZMod 2) → ℚ) : Prop := ∀ Y Z, cs Y = cs Z → g Y = g Z

def Low {m j : ℕ} (k : ℕ) (g : (Fin j → Fin m → ZMod 2) → ℚ) : Prop :=
  ∀ Y, k < Module.finrank (ZMod 2) (cs Y) → g Y = 0

theorem tb_inv {n m j : ℕ} (h : Fin n → Fin m → ZMod 2) : Inv (tb n m j h) := by
  intro Y Z e
  simp only [tb]
  exact congrArg Nat.cast (le_antisymm (card_le h Y Z e) (card_le h Z Y e.symm))

theorem tb_low {n m j : ℕ} (h : Fin n → Fin m → ZMod 2) : Low (bnd n) (tb n m j h) := by
  intro Y hY
  simp only [tb, tbl_low h Y hY, Nat.cast_zero]

theorem inner {n m j : ℕ} (k : ℕ)
    (hprev : ∀ g : (Fin j → Fin m → ZMod 2) → ℚ, Inv g → Low (bnd n) g →
      (∀ Y, k ≤ Module.finrank (ZMod 2) (cs Y) → g Y = 0) →
      g ∈ Submodule.span ℚ (Set.range (tb n m j))) :
    ∀ N : ℕ, ∀ g : (Fin j → Fin m → ZMod 2) → ℚ, Inv g → Low (bnd n) g → Low k g →
      (Finset.univ.filter (fun Y => Module.finrank (ZMod 2) (cs Y) = k ∧ g Y ≠ 0)).card ≤ N →
      g ∈ Submodule.span ℚ (Set.range (tb n m j)) := by
  intro N
  induction N with
  | zero =>
    intro g hi hb hk hN
    apply hprev g hi hb
    intro Y hY
    rcases Nat.eq_or_lt_of_le hY with e | e
    · by_contra hne
      have : 0 < (Finset.univ.filter
          (fun Y => Module.finrank (ZMod 2) (cs Y) = k ∧ g Y ≠ 0)).card :=
        Finset.card_pos.2 ⟨Y, by simp [e.symm, hne]⟩
      omega
    · exact hk Y e
  | succ N ih =>
    intro g hi hb hk hN
    by_cases hc : (Finset.univ.filter
        (fun Y => Module.finrank (ZMod 2) (cs Y) = k ∧ g Y ≠ 0)).card ≤ N
    · exact ih g hi hb hk hc
    obtain ⟨Y0, hY0⟩ := Finset.card_pos.1 (by omega : 0 < (Finset.univ.filter
        (fun Y => Module.finrank (ZMod 2) (cs Y) = k ∧ g Y ≠ 0)).card)
    have hY0' := (Finset.mem_filter.1 hY0).2
    have hr : Module.finrank (ZMod 2) (cs Y0) ≤ bnd n := by
      by_contra hlt
      exact hY0'.2 (hb Y0 (by omega))
    obtain ⟨h, hpos, hsupp⟩ := constr (n := n) Y0 hr
    set t := tb n m j h with ht
    have tY0 : t Y0 ≠ 0 := by
      simp only [t, tb]
      exact_mod_cast hpos.ne'
    set cc := g Y0 / t Y0 with hcc
    let g' : (Fin j → Fin m → ZMod 2) → ℚ := fun Y => g Y - cc * t Y
    have hg'inv : Inv g' := by
      intro Y Z e
      simp only [g', hi Y Z e, tb_inv h Y Z e, t]
    have hsup : ∀ Y, t Y ≠ 0 → cs Y ≤ cs Y0 := by
      intro Y hY
      apply hsupp
      intro h0
      apply hY
      simp only [t, tb, h0, Nat.cast_zero]
    have hg' : g' ∈ Submodule.span ℚ (Set.range (tb n m j)) := by
      apply ih g' hg'inv
      · intro Y hY
        simp only [g', hb Y hY, tb_low h Y hY, t, mul_zero, sub_zero]
      · intro Y hY
        have htY : t Y = 0 := by
          by_contra hne
          have := Submodule.finrank_mono (hsup Y hne)
          omega
        simp only [g', hk Y hY, htY, mul_zero, sub_zero]
      · have hsub : Finset.univ.filter
            (fun Y => Module.finrank (ZMod 2) (cs Y) = k ∧ g' Y ≠ 0) ⊆
            (Finset.univ.filter
              (fun Y => Module.finrank (ZMod 2) (cs Y) = k ∧ g Y ≠ 0)).erase Y0 := by
          intro Y hY
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hY
          obtain ⟨hrk, hne⟩ := hY
          by_cases htY : t Y = 0
          · have hgY : g Y ≠ 0 := by simpa [g', htY] using hne
            rw [Finset.mem_erase]
            refine ⟨?_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hrk, hgY⟩⟩
            rintro rfl
            exact tY0 htY
          · exfalso
            have e : cs Y = cs Y0 := Submodule.eq_of_le_of_finrank_eq (hsup Y htY)
              (by rw [hrk, hY0'.1])
            apply hne
            rw [hg'inv Y Y0 e]
            simp only [g', hcc]
            field_simp
            ring
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hY0] at this
        omega
    have hg : g = g' + cc • t := by
      funext Y
      simp [g']
    rw [hg]
    exact Submodule.add_mem _ hg' (Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩))

theorem Qk {n m j : ℕ} : ∀ k : ℕ, ∀ g : (Fin j → Fin m → ZMod 2) → ℚ,
    Inv g → Low (bnd n) g → Low k g → g ∈ Submodule.span ℚ (Set.range (tb n m j)) := by
  intro k
  induction k with
  | zero =>
    intro g hi hb hk
    refine inner 0 (fun g _ _ hv => ?_) _ g hi hb hk le_rfl
    have : g = 0 := funext (fun Y => hv Y (Nat.zero_le _))
    rw [this]; exact Submodule.zero_mem _
  | succ k ih =>
    intro g hi hb hk
    exact inner (k+1) (fun g hi hb hv => ih g hi hb (fun Y hY => hv Y hY)) _ g hi hb hk le_rfl

theorem key (n m j : ℕ) (g : (Fin j → Fin m → ZMod 2) → ℚ) :
    g ∈ Submodule.span ℚ (Set.range (tb n m j)) ↔ Inv g ∧ Low (bnd n) g := by
  constructor
  · intro hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact ⟨tb_inv h, tb_low h⟩
    | zero => exact ⟨fun _ _ _ => rfl, fun _ _ => rfl⟩
    | add x y _ _ hx hy =>
      exact ⟨fun Y Z e => by simp [hx.1 Y Z e, hy.1 Y Z e],
        fun Y hY => by simp [hx.2 Y hY, hy.2 Y hY]⟩
    | smul a x _ hx =>
      exact ⟨fun Y Z e => by simp [hx.1 Y Z e], fun Y hY => by simp [hx.2 Y hY]⟩
  · rintro ⟨hi, hb⟩
    exact Qk (bnd n) g hi hb hb

end PEqualNP.Outside.L_lib_814

open PEqualNP.Outside.L_lib_814 in
theorem PEqualNP.Outside.L_lib_814 :
    ∀ (n m j : ℕ),
      letI : ∀ p : Prop, Decidable p := Classical.propDecidable
      let F := ZMod 2
      let A := Fin m → F
      let C := Fin j → F
      let next := fun i : Fin n =>
        (⟨(i.val+1) % n, Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)⟩ : Fin n)
      let table := fun (h : Fin n → A) (Y : Fin j → A) =>
        let good := (Finset.univ : Finset (Fin n → C)).filter (fun x =>
          (∀ i, x i = 0 ∨ x (next i) = 0 ∨ x i = x (next i)) ∧
          (∀ b : Fin j, ∀ a : Fin m, (∑ i, h i a * x i b) = Y b a))
        (good.card : ℚ)
      let colSpace := fun Y : Fin j → A => Submodule.span F (Set.range Y)
      let bound := if n = 0 then 0 else max 1 (n / 2)
      ∀ g : (Fin j → A) → ℚ, g ∈ Submodule.span ℚ (Set.range table) ↔
        (∀ Y Z, colSpace Y = colSpace Z → g Y = g Z) ∧
        (∀ Y, bound < Module.finrank F (colSpace Y) → g Y = 0) := by
  intro n m j
  exact key n m j
