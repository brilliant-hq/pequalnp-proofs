import Mathlib
import PEqualNP.Defs

open Module

namespace PEqualNP.Outside.L_lib_917_aux

variable {F : Type*} [Field F]

theorem inf_ker_bound {V Y : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
    (P : Submodule F V) (f : V →ₗ[F] Y) :
    finrank F P ≤ finrank F ↥(P ⊓ LinearMap.ker f) + finrank F Y := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq P (LinearMap.ker f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  have h3 := Submodule.finrank_le (P ⊔ LinearMap.ker f)
  have h4 := Submodule.finrank_le (LinearMap.range f)
  omega

theorem map_add_inf_ker {V Y : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup Y] [Module F Y] [FiniteDimensional F Y]
    (W : Submodule F V) (f : V →ₗ[F] Y) :
    finrank F W = finrank F ↥(W.map f) + finrank F ↥(W ⊓ LinearMap.ker f) := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict W)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict,
    ← Submodule.finrank_map_subtype_eq W, Submodule.map_comap_subtype] at h
  omega

def rho (m : ℕ) (S Z : Type*) [AddCommGroup S] [Module F S] [AddCommGroup Z] [Module F Z]
    (C0 C1 : Finset (Fin m)) :
    (S × ((Fin m → F) × ((Fin m → F) × Z))) →ₗ[F] ((C0 → F) × (C1 → F)) where
  toFun w := (fun i => w.2.1 i, fun i => w.2.2.1 i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def good (m : ℕ) {S Z : Type*} [AddCommGroup S] [Module F S] [AddCommGroup Z] [Module F Z]
    (W : Submodule F (S × ((Fin m → F) × ((Fin m → F) × Z)))) (C0 C1 : Finset (Fin m)) : Prop :=
  ∀ b c : Fin m → F, ∃ w ∈ W, w.1 = 0 ∧ (∀ i ∈ C0, w.2.1 i = b i) ∧ (∀ i ∈ C1, w.2.2.1 i = c i)

theorem step (m r : ℕ) {S : Type*} [AddCommGroup S] [Module F S] [FiniteDimensional F S]
    (W : Submodule F (S × ((Fin m → F) × ((Fin m → F) × (Fin r → F)))))
    (C0 C1 : Finset (Fin m)) (hg : good m W C0 C1)
    (hlt : C0.card + C1.card + r <
      finrank F ↥(W ⊓ LinearMap.ker (LinearMap.fst F S ((Fin m → F) × ((Fin m → F) × (Fin r → F)))))) :
    ∃ C0' C1' : Finset (Fin m), good m W C0' C1' ∧ C0.card + C1.card + 1 ≤ C0'.card + C1'.card := by
  set K := W ⊓ LinearMap.ker (LinearMap.fst F S ((Fin m → F) × ((Fin m → F) × (Fin r → F))))
    with hK
  set Mm := K ⊓ LinearMap.ker (rho m S (Fin r → F) C0 C1) with hM
  have hb := inf_ker_bound K (rho m S (Fin r → F) C0 C1)
  rw [← hM] at hb
  have hY : finrank F ((C0 → F) × (C1 → F)) = C0.card + C1.card := by
    simp [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  have memM : ∀ x, x ∈ Mm → x ∈ W ∧ x.1 = 0 ∧ (∀ i ∈ C0, x.2.1 i = 0) ∧ (∀ i ∈ C1, x.2.2.1 i = 0) := by
    intro x hx
    rw [hM, hK, Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hx
    obtain ⟨⟨hxW, hx1⟩, hx2⟩ := hx
    refine ⟨hxW, hx1, ?_, ?_⟩
    · intro i hi
      exact congrFun (congrArg Prod.fst hx2) ⟨i, hi⟩
    · intro i hi
      exact congrFun (congrArg Prod.snd hx2) ⟨i, hi⟩
  have hex : ∃ x ∈ Mm, x.2.1 ≠ 0 ∨ x.2.2.1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let g : ↥Mm →ₗ[F] (Fin r → F) :=
      ((LinearMap.snd F _ _).comp ((LinearMap.snd F _ _).comp (LinearMap.snd F _ _))).comp
        Mm.subtype
    have hinj : Function.Injective g := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx
      obtain ⟨h1, h2⟩ := hcon x x.2
      obtain ⟨_, hx1, _, _⟩ := memM x x.2
      apply Subtype.ext
      exact Prod.ext hx1 (Prod.ext h1 (Prod.ext h2 hx))
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    omega
  obtain ⟨x, hxM, hx⟩ := hex
  obtain ⟨hxW, hx1, hx0, hx0'⟩ := memM x hxM
  rcases hx with hx | hx
  · obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hx
    have hnot : i0 ∉ C0 := fun h => hi0 (hx0 i0 h)
    refine ⟨insert i0 C0, C1, ?_, ?_⟩
    · intro b c
      obtain ⟨w, hw, hw1, hwb, hwc⟩ := hg b c
      refine ⟨w + ((b i0 - w.2.1 i0) / x.2.1 i0) • x, W.add_mem hw (W.smul_mem _ hxW), ?_, ?_, ?_⟩
      · simp [hw1, hx1]
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul]
          rw [div_mul_cancel₀ _ hi0]
          ring
        · simp [hwb i hi, hx0 i hi]
      · intro i hi
        simp [hwc i hi, hx0' i hi]
    · rw [Finset.card_insert_of_notMem hnot]
      omega
  · obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hx
    have hnot : i0 ∉ C1 := fun h => hi0 (hx0' i0 h)
    refine ⟨C0, insert i0 C1, ?_, ?_⟩
    · intro b c
      obtain ⟨w, hw, hw1, hwb, hwc⟩ := hg b c
      refine ⟨w + ((c i0 - w.2.2.1 i0) / x.2.2.1 i0) • x, W.add_mem hw (W.smul_mem _ hxW), ?_, ?_, ?_⟩
      · simp [hw1, hx1]
      · intro i hi
        simp [hwb i hi, hx0 i hi]
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simp only [Prod.snd_add, Prod.fst_add, Prod.smul_snd, Prod.smul_fst, Pi.add_apply,
            Pi.smul_apply, smul_eq_mul]
          rw [div_mul_cancel₀ _ hi0]
          ring
        · simp [hwc i hi, hx0' i hi]
    · rw [Finset.card_insert_of_notMem hnot]
      omega

theorem exists_good (m r : ℕ) {S : Type*} [AddCommGroup S] [Module F S] [FiniteDimensional F S]
    (W : Submodule F (S × ((Fin m → F) × ((Fin m → F) × (Fin r → F))))) :
    ∀ n : ℕ, n ≤
      finrank F ↥(W ⊓ LinearMap.ker (LinearMap.fst F S ((Fin m → F) × ((Fin m → F) × (Fin r → F))))) - r
      → ∃ C0 C1 : Finset (Fin m), good m W C0 C1 ∧ n ≤ C0.card + C1.card := by
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨∅, ∅, ?_, by simp⟩
    intro b c
    exact ⟨0, W.zero_mem, rfl, by simp, by simp⟩
  | succ n ih =>
    intro hn
    obtain ⟨C0, C1, hg, hc⟩ := ih (by omega)
    by_cases h : n + 1 ≤ C0.card + C1.card
    · exact ⟨C0, C1, hg, h⟩
    · obtain ⟨C0', C1', hg', hc'⟩ := step m r W C0 C1 hg (by omega)
      exact ⟨C0', C1', hg', by omega⟩

def mu (k m : ℕ) (A : Fin m → Fin k → F) (T : Finset (Fin m)) :
    (Fin k → F) →ₗ[F] (↥Tᶜ → F) where
  toFun v := fun i => dotProduct (A i) v
  map_add' u v := by
    funext i
    simp [dotProduct_add]
  map_smul' c v := by
    funext i
    simp [dotProduct_smul]

theorem main (k m r j : ℕ) (A : Fin m → Fin k → F)
    (W : Submodule F ((Fin k → F) × ((Fin m → F) × ((Fin m → F) × (Fin r → F)))))
    (hW : 2 * m + r + j ≤ finrank F W) :
    ∃ B : (Fin j → F) →ₗ[F] (Fin k → F), Function.Injective B ∧
      (∀ a : Fin j → F, ∃ w ∈ W, w.1 = B a) ∧
      ∀ b c : Fin m → F, ∃ w ∈ W, w.1 = 0 ∧
        ∀ i : Fin m, (∃ a : Fin j → F, dotProduct (A i) (B a) ≠ 0) →
          w.2.1 i = b i ∧ w.2.2.1 i = c i := by
  have hPK := map_add_inf_ker W
    (LinearMap.fst F (Fin k → F) ((Fin m → F) × ((Fin m → F) × (Fin r → F))))
  obtain ⟨C0, C1, hg, hc⟩ := exists_good m r W _ le_rfl
  obtain ⟨T, hT⟩ : ∃ T : Finset (Fin m), T = C0 ∩ C1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Submodule F (Fin k → F), N = (W.map
      (LinearMap.fst F (Fin k → F) ((Fin m → F) × ((Fin m → F) × (Fin r → F))))) ⊓
        LinearMap.ker (mu k m A T) := ⟨_, rfl⟩
  have hNb : finrank F ↥(W.map
      (LinearMap.fst F (Fin k → F) ((Fin m → F) × ((Fin m → F) × (Fin r → F))))) ≤
      finrank F N + finrank F (↥Tᶜ → F) := by
    rw [hN]
    exact inf_ker_bound _ (mu k m A T)
  have hcard : finrank F (↥Tᶜ → F) = m - T.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
  have hU : (C0 ∪ C1).card + T.card = C0.card + C1.card := by
    rw [hT]
    exact Finset.card_union_add_card_inter C0 C1
  have hU2 : (C0 ∪ C1).card ≤ m := by
    have := Finset.card_le_univ (C0 ∪ C1)
    simpa using this
  have hTm : T.card ≤ m := by
    have := Finset.card_le_univ T
    simpa using this
  have hjN : j ≤ finrank F N := by
    rw [hcard] at hNb
    omega
  let bN := Module.finBasis F N
  let v : Fin j → N := fun l => bN (Fin.castLE hjN l)
  have hli : LinearIndependent F v :=
    bN.linearIndependent.comp _ (Fin.castLE_injective hjN)
  refine ⟨N.subtype.comp (Fintype.linearCombination F v), ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp hli.fintypeLinearCombination_injective
  · intro a
    have h2 := (Fintype.linearCombination F v a).2
    replace h2 := hN.le h2
    have hmem := (Submodule.mem_inf.mp h2).1
    obtain ⟨y, hy, hyf⟩ := Submodule.mem_map.mp hmem
    exact ⟨y, hy, hyf⟩
  · intro b c
    obtain ⟨w, hw, hw1, hwb, hwc⟩ := hg b c
    refine ⟨w, hw, hw1, ?_⟩
    intro i ⟨a, ha⟩
    have hiT : i ∈ T := by
      by_contra hi
      have h2 := (Fintype.linearCombination F v a).2
      replace h2 := hN.le h2
      have hker := (Submodule.mem_inf.mp h2).2
      rw [LinearMap.mem_ker] at hker
      have := congrFun hker ⟨i, Finset.mem_compl.mpr hi⟩
      exact ha this
    rw [hT, Finset.mem_inter] at hiT
    exact ⟨hwb i hiT.1, hwc i hiT.2⟩

end PEqualNP.Outside.L_lib_917_aux

theorem PEqualNP.Outside.L_lib_917 : (∀ (k m r j : ℕ),
  let F := ZMod 2
  let S := Fin k → F
  let D := Fin m → F
  let Z := Fin r → F
  let V := S × (D × (D × Z))
  let J := Fin j → F
  let base := 2*m+r
  ∀ (A : Fin m → S) (W : Submodule F V), base+j ≤ Module.finrank F W →
    ∃ B : J →ₗ[F] S, Function.Injective B ∧
      (∀ a : J, ∃ w ∈ W, w.1 = B a) ∧
      ∀ b c : D, ∃ w ∈ W, w.1 = 0 ∧
        ∀ i : Fin m, (∃ a : J, dotProduct (A i) (B a) ≠ 0) →
          w.2.1 i = b i ∧ w.2.2.1 i = c i) := by
  intro k m r j F S D Z V J base A W hW
  exact PEqualNP.Outside.L_lib_917_aux.main k m r j A W hW
