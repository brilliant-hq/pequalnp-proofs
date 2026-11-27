import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_991_aux

open Module

variable {K : Type} [Field K] {n m : ℕ}

def msk (J : Finset (Fin m)) : (Fin m → K) →ₗ[K] (Fin m → K) where
  toFun v := fun j => if j ∈ J then v j else 0
  map_add' x y := by
    funext j
    by_cases h : j ∈ J <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : j ∈ J <;> simp [h]

theorem msk_apply (J : Finset (Fin m)) (v : Fin m → K) (j : Fin m) :
    msk J v j = if j ∈ J then v j else 0 := rfl

theorem msk_msk (J J' : Finset (Fin m)) (h : J ⊆ J') (v : Fin m → K) :
    msk J (msk J' v) = msk J v := by
  funext j
  by_cases hj : j ∈ J
  · simp [msk_apply, hj, h hj]
  · simp [msk_apply, hj]

theorem msk_univ (v : Fin m → K) : msk Finset.univ v = v := by
  funext j
  simp [msk_apply]

def rowSp (A : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) : Submodule K (Fin m → K) :=
  Submodule.span K ((fun i => A i) '' (I : Set (Fin n)))

theorem rowSp_mono (A : Matrix (Fin n) (Fin m) K) {I I' : Finset (Fin n)} (h : I ⊆ I') :
    rowSp A I ≤ rowSp A I' :=
  Submodule.span_mono (Set.image_mono (by exact_mod_cast h))

theorem mem_rowSp (A : Matrix (Fin n) (Fin m) K) {I : Finset (Fin n)} {i : Fin n} (h : i ∈ I) :
    A i ∈ rowSp A I :=
  Submodule.subset_span ⟨i, by exact_mod_cast h, rfl⟩

def ext0 (J : Finset (Fin m)) : (J → K) →ₗ[K] (Fin m → K) where
  toFun v := fun j => if h : j ∈ J then v ⟨j, h⟩ else 0
  map_add' x y := by
    funext j
    by_cases h : j ∈ J <;> simp [h]
  map_smul' c x := by
    funext j
    by_cases h : j ∈ J <;> simp [h]

theorem ext0_inj (J : Finset (Fin m)) : Function.Injective (ext0 (K := K) J) := by
  intro x y h
  funext j
  have := congrFun h j.1
  simpa [ext0, j.2] using this

theorem rk_eq (A : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) :
    Matrix.rank (A.submatrix (fun i : I => i.val) (fun j : J => j.val)) =
      finrank K ((rowSp A I).map (msk J)) := by
  rw [Matrix.rank_eq_finrank_span_row]
  have e := (Submodule.equivMapOfInjective (ext0 (K := K) J) (ext0_inj J)
    (Submodule.span K (Set.range (A.submatrix (fun i : I => i.val) (fun j : J => j.val)).row))).finrank_eq
  rw [e]
  have hs : (ext0 (K := K) J) '' Set.range (A.submatrix (fun i : I => i.val) (fun j : J => j.val)).row
      = (msk J) '' ((fun i => A i) '' (I : Set (Fin n))) := by
    ext v
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨A i.1, ⟨i.1, i.2, rfl⟩, ?_⟩
      funext j
      by_cases h : j ∈ J <;> simp [msk_apply, ext0, h, Matrix.row]
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨_, ⟨⟨i, hi⟩, rfl⟩, ?_⟩
      funext j
      by_cases h : j ∈ J <;> simp [msk_apply, ext0, h, Matrix.row]
  rw [Submodule.map_span, rowSp, Submodule.map_span, hs]

theorem rank_le_of_rows (B : Matrix (Fin n) (Fin m) K) (W : Submodule K (Fin m → K))
    (h : ∀ i, B i ∈ W) : B.rank ≤ finrank K W := by
  rw [Matrix.rank_eq_finrank_span_row]
  apply Submodule.finrank_mono
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact h i

theorem rank_eq_rowSp (B : Matrix (Fin n) (Fin m) K) :
    B.rank = finrank K (rowSp B Finset.univ) := by
  have hs : Set.range B.row = (fun i => B i) '' ((Finset.univ : Finset (Fin n)) : Set (Fin n)) := by
    ext v
    simp [Matrix.row]
    exact Iff.rfl
  rw [Matrix.rank_eq_finrank_span_row, rowSp, hs]

section generic
variable {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem map_add_ker (f : E →ₗ[K] E) (U : Submodule K E) :
    finrank K (U.map f) + finrank K (U ⊓ LinearMap.ker f : Submodule K E) = finrank K U := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  have h1 : LinearMap.range (f.domRestrict U) = U.map f := by
    ext x
    simp [LinearMap.domRestrict]
  have h2 : finrank K (LinearMap.ker (f.domRestrict U)) =
      finrank K (U ⊓ LinearMap.ker f : Submodule K E) := by
    have e : (LinearMap.ker (f.domRestrict U)).map U.subtype = U ⊓ LinearMap.ker f := by
      ext x
      simp [LinearMap.domRestrict]
      exact and_comm
    rw [← e]
    exact ((Submodule.equivMapOfInjective U.subtype U.subtype_injective _).finrank_eq)
  rw [h1, h2] at h
  exact h

theorem submod (f : E →ₗ[K] E) {U U' : Submodule K E} (h : U ≤ U') :
    finrank K (U'.map f) + finrank K U ≤ finrank K U' + finrank K (U.map f) := by
  have h1 := map_add_ker f U
  have h2 := map_add_ker f U'
  have h3 : finrank K (U ⊓ LinearMap.ker f : Submodule K E) ≤
      finrank K (U' ⊓ LinearMap.ker f : Submodule K E) :=
    Submodule.finrank_mono (inf_le_inf_right _ h)
  omega

theorem exists_compl_in {U V : Submodule K E} (h : U ≤ V) :
    ∃ Y : Submodule K E, Y ≤ V ∧ U ⊔ Y = V ∧ finrank K U + finrank K Y = finrank K V := by
  obtain ⟨Y0, hY0⟩ := Submodule.exists_isCompl U
  refine ⟨Y0 ⊓ V, inf_le_right, ?_, ?_⟩
  · rw [← sup_inf_assoc_of_le Y0 h, hY0.sup_eq_top, top_inf_eq]
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq U (Y0 ⊓ V)
    have h2 : U ⊓ (Y0 ⊓ V) = ⊥ := by
      rw [← inf_assoc, hY0.inf_eq_bot, bot_inf_eq]
    have h3 : U ⊔ Y0 ⊓ V = V := by
      rw [← sup_inf_assoc_of_le Y0 h, hY0.sup_eq_top, top_inf_eq]
    rw [h2, h3] at h1
    simp at h1
    omega

theorem exists_cover (Q : Submodule K E) (t : ℕ) (h : finrank K Q ≤ t) :
    ∃ f : (Fin t → K) →ₗ[K] E, Q ≤ LinearMap.range f := by
  let b := Module.finBasis K Q
  let f : (Fin t → K) →ₗ[K] E :=
    ∑ i : Fin (finrank K Q), (LinearMap.proj (Fin.castLE h i)).smulRight (b i : E)
  refine ⟨f, ?_⟩
  intro q hq
  have hsp := b.mem_span (⟨q, hq⟩ : Q)
  have : (⟨q, hq⟩ : Q) ∈ (LinearMap.range f).comap Q.subtype := by
    refine (Submodule.span_le.mpr ?_) hsp
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single (Fin.castLE h i) 1, ?_⟩
    simp only [f, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply,
      Submodule.subtype_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      have : Fin.castLE h j ≠ Fin.castLE h i := fun e => hj (Fin.castLE_injective h e)
      simp [this]
    · simp
  exact this

end generic

theorem msk_msk' (J J' : Finset (Fin m)) (h : J' ⊆ J) (v : Fin m → K) :
    msk J (msk J' v) = msk J' v := by
  funext j
  by_cases hj : j ∈ J'
  · simp [msk_apply, hj, h hj]
  · simp [msk_apply, hj]

theorem msk_of_mem_map {J : Finset (Fin m)} {U : Submodule K (Fin m → K)} {v : Fin m → K}
    (h : v ∈ U.map (msk J)) : msk J v = v := by
  obtain ⟨w, _, rfl⟩ := h
  exact msk_msk J J (subset_refl _) w

theorem map_msk_univ (U : Submodule K (Fin m → K)) : U.map (msk Finset.univ) = U := by
  have : (msk Finset.univ : (Fin m → K) →ₗ[K] (Fin m → K)) = LinearMap.id :=
    LinearMap.ext msk_univ
  rw [this, Submodule.map_id]

theorem map_msk_msk (J J' : Finset (Fin m)) (h : J ⊆ J') (U : Submodule K (Fin m → K)) :
    (U.map (msk J')).map (msk J) = U.map (msk J) := by
  ext x
  constructor
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w, hw, (msk_msk J J' h w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨msk J' w, ⟨w, hw, rfl⟩, msk_msk J J' h w⟩

noncomputable def fr (A : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m)) : ℕ :=
  finrank K ((rowSp A I).map (msk J))

theorem fr_univ (A : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) :
    fr A I Finset.univ = finrank K (rowSp A I) := by
  rw [fr, map_msk_univ]

theorem fr_congr (A B : Matrix (Fin n) (Fin m) K) (I : Finset (Fin n)) (J : Finset (Fin m))
    (h : ∀ i ∈ I, ∀ j ∈ J, B i j = A i j) : fr B I J = fr A I J := by
  rw [fr, fr, ← rk_eq, ← rk_eq]
  congr 1
  ext i j
  exact h i.1 i.2 j.1 j.2

theorem fr_ineq (B : Matrix (Fin n) (Fin m) K) {I I' : Finset (Fin n)} (h : I ⊆ I')
    (J : Finset (Fin m)) :
    fr B I' J + finrank K (rowSp B I) ≤ finrank K (rowSp B I') + fr B I J := by
  have h1 := map_add_ker (msk J) (rowSp B I)
  have h2 := map_add_ker (msk J) (rowSp B I')
  have h3 : finrank K (rowSp B I ⊓ LinearMap.ker (msk J) : Submodule K (Fin m → K)) ≤
      finrank K (rowSp B I' ⊓ LinearMap.ker (msk J) : Submodule K (Fin m → K)) :=
    Submodule.finrank_mono (inf_le_inf_right _ (rowSp_mono B h))
  unfold fr
  omega

section generic2
variable {E : Type} [AddCommGroup E] [Module K E] [FiniteDimensional K E]

theorem section_ext (π : E →ₗ[K] E) (T : Submodule K E) :
    ∃ g : E →ₗ[K] E, ∀ u ∈ T.map π, u + g u ∈ T ∧ π (u + g u) = u := by
  obtain ⟨σ, hσ⟩ := (π.submoduleMap T).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (π.submoduleMap_surjective T))
  obtain ⟨g, hg⟩ := (T.subtype.comp σ - (T.map π).subtype).exists_extend
  refine ⟨g, fun u hu => ?_⟩
  have h1 : g u = (σ ⟨u, hu⟩ : E) - u := by
    have := LinearMap.congr_fun hg ⟨u, hu⟩
    simpa using this
  have h2 : π (σ ⟨u, hu⟩ : E) = u := by
    have := LinearMap.congr_fun hσ ⟨u, hu⟩
    have := congrArg Subtype.val this
    simpa using this
  rw [h1]
  simp only [add_sub_cancel]
  exact ⟨(σ ⟨u, hu⟩).2, h2⟩

end generic2

section main

variable {d : ℕ}

def Rr (row : Fin n → Option (Fin d)) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)

def Mr (row : Fin n → Option (Fin d)) (a : Fin d) : Finset (Fin n) :=
  Finset.univ.filter (fun i => row i = some a)

def rws (row : Fin n → Option (Fin d)) (a : Fin d) : Finset (Fin n) := Rr row ∪ Mr row a

theorem supp_lemma (col : Fin m → Option (Fin d)) (a : Fin d) (σ : Fin m → K)
    (h1 : msk (rws col a) σ = σ) :
    msk (Mr col a) (σ - msk (Rr col) σ) = σ - msk (Rr col) σ := by
  funext j
  by_cases hj : j ∈ Mr col a
  · simp [msk_apply, hj]
  · by_cases hc : j ∈ Rr col
    · simp [msk_apply, hj, hc]
    · have : j ∉ rws col a := by simp [rws, hj, hc]
      have h2 := congrFun h1 j
      simp only [msk_apply, this, ite_false] at h2
      simp [msk_apply, hj, hc, ← h2]

theorem proj_sum (col : Fin m → Option (Fin d)) (a : Fin d) (F : Fin d → (Fin m → K)) :
    msk (rws col a) (∑ b, msk (Mr col b) (F b)) = msk (Mr col a) (F a) := by
  rw [map_sum, Finset.sum_eq_single a]
  · exact msk_msk' _ _ (by simp [rws]) _
  · intro b _ hb
    funext j
    by_cases hj : j ∈ Mr col b
    · have : j ∉ rws col a := by
        simp only [Mr, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [rws, Rr, Mr, hj, hb]
      simp [msk_apply, this]
    · simp [msk_apply, hj]
  · simp

theorem main (A : Matrix (Fin n) (Fin m) K) (row : Fin n → Option (Fin d))
    (col : Fin m → Option (Fin d)) (r : ℕ) :
    (∃ B : Matrix (Fin n) (Fin m) K, Matrix.rank B ≤ r ∧
      ∀ i j, (row i = none ∨ col j = none ∨ row i = col j) → B i j = A i j) ↔
    (fr A Finset.univ (Rr col) + fr A (Rr row) Finset.univ ≤ r + fr A (Rr row) (Rr col) ∧
      ∀ a : Fin d, fr A Finset.univ (Rr col) + fr A (Rr row) Finset.univ
          + fr A (rws row a) (rws col a)
        ≤ r + fr A (rws row a) (Rr col) + fr A (Rr row) (rws col a)) := by
  constructor
  · rintro ⟨B, hB, hag⟩
    have hR : ∀ i ∈ Rr row, row i = none := fun i hi => by simpa [Rr] using hi
    have hC : ∀ j ∈ Rr col, col j = none := fun j hj => by simpa [Rr] using hj
    have e1 : fr B Finset.univ (Rr col) = fr A Finset.univ (Rr col) :=
      fr_congr A B _ _ fun i _ j hj => hag i j (Or.inr (Or.inl (hC j hj)))
    have e2 : fr B (Rr row) Finset.univ = fr A (Rr row) Finset.univ :=
      fr_congr A B _ _ fun i hi j _ => hag i j (Or.inl (hR i hi))
    have e3 : fr B (Rr row) (Rr col) = fr A (Rr row) (Rr col) :=
      fr_congr A B _ _ fun i hi j _ => hag i j (Or.inl (hR i hi))
    rw [Matrix.rank_eq_finrank_span_row] at hB
    have hBr := rank_eq_rowSp B
    rw [Matrix.rank_eq_finrank_span_row] at hBr
    have s0 := fr_ineq B (Finset.subset_univ (Rr row)) (Rr col)
    rw [← fr_univ] at s0
    refine ⟨by omega, fun a => ?_⟩
    have e4 : fr B (rws row a) (rws col a) = fr A (rws row a) (rws col a) :=
      fr_congr A B _ _ fun i hi j hj => by
        apply hag
        simp only [rws, Rr, Mr, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and] at hi hj
        rcases hi with hi | hi
        · exact Or.inl hi
        · rcases hj with hj | hj
          · exact Or.inr (Or.inl hj)
          · exact Or.inr (Or.inr (hi.trans hj.symm))
    have e5 : fr B (rws row a) (Rr col) = fr A (rws row a) (Rr col) :=
      fr_congr A B _ _ fun i _ j hj => hag i j (Or.inr (Or.inl (hC j hj)))
    have e6 : fr B (Rr row) (rws col a) = fr A (Rr row) (rws col a) :=
      fr_congr A B _ _ fun i hi j _ => hag i j (Or.inl (hR i hi))
    have s1 := fr_ineq B (Finset.subset_univ (rws row a)) (Rr col)
    have s2 := fr_ineq B (I := Rr row) (I' := rws row a) (by simp [rws]) (rws col a)
    rw [← fr_univ] at s2
    omega
  · rintro ⟨h0, h1⟩

    set WR := rowSp A (Rr row) with hWR
    set πC : (Fin m → K) →ₗ[K] (Fin m → K) := msk (Rr col) with hπC
    have hUV : WR.map πC ≤ (rowSp A Finset.univ).map πC :=
      Submodule.map_mono (rowSp_mono A (Finset.subset_univ _))
    obtain ⟨Y, hYV, hsup, hYdim⟩ := exists_compl_in hUV
    have hYdim' : fr A (Rr row) (Rr col) + finrank K Y = fr A Finset.univ (Rr col) := hYdim
    have hWRdim : finrank K WR = fr A (Rr row) Finset.univ := (fr_univ A _).symm
    let T : Fin d → Submodule K (Fin m → K) := fun a => (rowSp A (rws row a)).map (msk (rws col a))
    let S : Fin d → Submodule K (Fin m → K) := fun a => WR.map (msk (rws col a))
    have hST : ∀ a, S a ≤ T a := fun a =>
      Submodule.map_mono (rowSp_mono A (by simp [rws]))
    have hCsub : ∀ a, Rr col ⊆ rws col a := fun a => by simp [rws]
    choose g hg using fun a => section_ext πC (T a)
    choose Q hQle hQsup hQdim using fun a =>
      exists_compl_in (inf_le_inf_right (LinearMap.ker πC) (hST a))
    set t := r - (finrank K WR + finrank K Y) with ht
    have hbound : ∀ a, finrank K (Q a) ≤ t := by
      intro a
      have k1 := map_add_ker πC (T a)
      have k2 := map_add_ker πC (S a)
      have k3 : finrank K ((T a).map πC) = fr A (rws row a) (Rr col) := by
        show finrank K (((rowSp A (rws row a)).map (msk (rws col a))).map (msk (Rr col))) = _
        rw [map_msk_msk _ _ (hCsub a)]
        rfl
      have k4 : finrank K ((S a).map πC) = fr A (Rr row) (Rr col) := by
        show finrank K (((rowSp A (Rr row)).map (msk (rws col a))).map (msk (Rr col))) = _
        rw [map_msk_msk _ _ (hCsub a)]
        rfl
      have k5 : finrank K (T a) = fr A (rws row a) (rws col a) := rfl
      have k6 : finrank K (S a) = fr A (Rr row) (rws col a) := rfl
      have := hQdim a
      have := h1 a
      omega
    choose Hh hH using fun a => exists_cover (Q a) t (hbound a)
    let G : (Fin m → K) →ₗ[K] (Fin m → K) :=
      LinearMap.id + ∑ a, (msk (Mr col a)).comp (g a)
    let Hmap : (Fin t → K) →ₗ[K] (Fin m → K) := ∑ a, (msk (Mr col a)).comp (Hh a)
    set W : Submodule K (Fin m → K) := WR ⊔ Y.map G ⊔ LinearMap.range Hmap with hW
    have hWdim : finrank K W ≤ r := by
      have a1 : finrank K W ≤ finrank K (WR ⊔ Y.map G : Submodule K (Fin m → K))
          + finrank K (LinearMap.range Hmap) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      have a2 : finrank K (WR ⊔ Y.map G : Submodule K (Fin m → K))
          ≤ finrank K WR + finrank K (Y.map G) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      have a3 : finrank K (Y.map G) ≤ finrank K Y := Submodule.finrank_map_le G Y
      have a4 : finrank K (LinearMap.range Hmap) ≤ t := by
        have := LinearMap.finrank_range_le Hmap
        simpa using this
      omega
    have hkey : ∀ a, T a ≤ W.map (msk (rws col a)) := by
      intro a x hx
      have hc : πC x ∈ (rowSp A Finset.univ).map πC := by
        have h2 : πC x ∈ (T a).map πC := Submodule.mem_map_of_mem hx
        have h3 : (T a).map πC = (rowSp A (rws row a)).map πC := map_msk_msk _ _ (hCsub a) _
        rw [h3] at h2
        exact Submodule.map_mono (rowSp_mono A (Finset.subset_univ _)) h2
      rw [← hsup] at hc
      obtain ⟨u, hu, y, hy, huy⟩ := Submodule.mem_sup.mp hc
      obtain ⟨s, hs, rfl⟩ := hu
      have hs' : msk (rws col a) s ∈ T a := hST a (Submodule.mem_map_of_mem hs)
      have hyT : y ∈ (T a).map πC := by
        refine ⟨x - msk (rws col a) s, sub_mem hx hs', ?_⟩
        rw [map_sub, hπC, msk_msk _ _ (hCsub a), ← hπC, ← huy]
        simp
      obtain ⟨hσT, hσC⟩ := hg a y hyT
      have hyC : πC y = y := msk_of_mem_map (hYV hy)
      have hya : msk (rws col a) y = y := by
        rw [← hyC, hπC]
        exact msk_msk' _ _ (hCsub a) _
      have hgy : msk (Mr col a) (g a y) = g a y := by
        have h4 := supp_lemma col a (y + g a y) (msk_of_mem_map hσT)
        rw [← hπC, hσC] at h4
        simpa using h4
      have hGy : msk (rws col a) (G y) = y + g a y := by
        have : G y = y + ∑ b, msk (Mr col b) (g b y) := by
          simp [G, LinearMap.sum_apply]
        rw [this, map_add, hya, proj_sum, hgy]
      have hx' : x - msk (rws col a) s - (y + g a y) ∈ T a ⊓ LinearMap.ker πC := by
        refine Submodule.mem_inf.mpr ⟨sub_mem (sub_mem hx hs') hσT, LinearMap.mem_ker.mpr ?_⟩
        rw [map_sub, map_sub, hσC, hπC, msk_msk _ _ (hCsub a), ← hπC, ← huy]
        simp
      rw [← hQsup a] at hx'
      obtain ⟨s1, hs1, q, hq, hsq⟩ := Submodule.mem_sup.mp hx'
      obtain ⟨s2, hs2, hs2e⟩ := hs1.1
      obtain ⟨z, hz⟩ := hH a hq
      have hqT : q ∈ T a ⊓ LinearMap.ker πC := hQle a hq
      have hqM : msk (Mr col a) q = q := by
        have h4 := supp_lemma col a q (msk_of_mem_map hqT.1)
        have h5 : msk (Rr col) q = 0 := hqT.2
        rw [h5] at h4
        simpa using h4
      have hHz : msk (rws col a) (Hmap z) = q := by
        have : Hmap z = ∑ b, msk (Mr col b) (Hh b z) := by
          simp [Hmap, LinearMap.sum_apply]
        rw [this, proj_sum, hz, hqM]
      refine ⟨s + G y + s2 + Hmap z, ?_, ?_⟩
      · refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_) ?_
        · exact Submodule.mem_sup_left (Submodule.mem_sup_left hs)
        · exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_map_of_mem hy))
        · exact Submodule.mem_sup_left (Submodule.mem_sup_left hs2)
        · exact Submodule.mem_sup_right ⟨z, rfl⟩
      · rw [map_add, map_add, map_add, hGy, hHz, hs2e, add_assoc _ s1 q, hsq]
        abel
    have hrow : ∀ i, ∃ b ∈ W, ∀ j, (row i = none ∨ col j = none ∨ row i = col j) → b j = A i j := by
      intro i
      cases hri : row i with
      | none =>
        refine ⟨A i, ?_, fun j _ => rfl⟩
        exact Submodule.mem_sup_left (Submodule.mem_sup_left (mem_rowSp A (by simp [Rr, hri])))
      | some a =>
        have hi : msk (rws col a) (A i) ∈ T a :=
          Submodule.mem_map_of_mem (mem_rowSp A (by simp [rws, Mr, hri]))
        obtain ⟨w, hw, hwe⟩ := hkey a hi
        refine ⟨w, hw, fun j hj => ?_⟩
        have hjc : j ∈ rws col a := by
          rcases hj with h | h | h
          · exact absurd h (by simp)
          · simp [rws, Rr, h]
          · simp [rws, Mr, ← h]
        have := congrFun hwe j
        simpa [msk_apply, hjc] using this
    choose b hbW hbag using hrow
    exact ⟨Matrix.of b, (rank_le_of_rows _ W hbW).trans hWdim, fun i j h => hbag i j h⟩

end main

end PEqualNP.Outside.L_lib_991_aux

theorem PEqualNP.Outside.L_lib_991 : (∀ (K : Type) [Field K] (n m d r : ℕ) (A : Matrix (Fin n) (Fin m) K)
  (row : Fin n → Option (Fin d)) (col : Fin m → Option (Fin d)),
  let R := (Finset.univ : Finset (Fin n)).filter (fun i => row i = none)
  let C := (Finset.univ : Finset (Fin m)).filter (fun j => col j = none)
  let rows := fun a : Fin d => R ∪ Finset.univ.filter (fun i => row i = some a)
  let cols := fun a : Fin d => C ∪ Finset.univ.filter (fun j => col j = some a)
  let rk := fun (I : Finset (Fin n)) (J : Finset (Fin m)) =>
    Matrix.rank (A.submatrix (fun i : I => i.val) (fun j : J => j.val))
  let strips := rk Finset.univ C + rk R Finset.univ
  (∃ B : Matrix (Fin n) (Fin m) K, Matrix.rank B ≤ r ∧
    ∀ i j, (row i = none ∨ col j = none ∨ row i = col j) → B i j = A i j) ↔
  strips ≤ r + rk R C ∧ ∀ a : Fin d,
    strips + rk (rows a) (cols a) ≤ r + rk (rows a) C + rk R (cols a)) := by
  intro K _ n m d r A row col
  simp only [PEqualNP.Outside.L_lib_991_aux.rk_eq]
  exact PEqualNP.Outside.L_lib_991_aux.main A row col r
