import Mathlib
import PEqualNP.Defs

open Module LinearMap

section L_lib_1010_sec

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem L_lib_1010_addvec {p : Submodule K W} {v : W} (hv : v ∉ p) :
    finrank K ↥(p ⊔ K ∙ v) = finrank K p + 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq p (K ∙ v)
  have hv0 : v ≠ 0 := fun h0 => hv (h0 ▸ p.zero_mem)
  have hinf : p ⊓ K ∙ v = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf, Submodule.mem_span_singleton] at hw
    obtain ⟨hwp, c, rfl⟩ := hw
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [hc] using p.smul_mem c⁻¹ hwp) hv
  rw [hinf, finrank_bot, finrank_span_singleton hv0] at h
  omega

theorem L_lib_1010_dual {E : Type*} [AddCommGroup E] [Module K E] {p : Submodule K E} {x : E}
    (hx : x ∉ p) : ∃ f : E →ₗ[K] K, f x = 1 ∧ ∀ v ∈ p, f v = 0 := by
  obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
  refine ⟨(f x)⁻¹ • f, by simp [hf], fun v hv => ?_⟩
  have : f v ∈ p.map f := Submodule.mem_map_of_mem hv
  rw [hf'] at this
  simp [(Submodule.mem_bot K).1 this]

theorem L_lib_1010_dual2 {p : Submodule K V} {x y : V} (hx : x ∉ p) (hy : y ∉ p) :
    ∃ f : V →ₗ[K] K, f x = 1 ∧ f y ≠ 0 ∧ ∀ v ∈ p, f v = 0 := by
  obtain ⟨f1, h1x, h1p⟩ := L_lib_1010_dual hx
  by_cases h1y : f1 y ≠ 0
  · exact ⟨f1, h1x, h1y, h1p⟩
  push_neg at h1y
  obtain ⟨f2, h2y, h2p⟩ := L_lib_1010_dual hy
  by_cases hc : 1 + f2 x = 0
  · refine ⟨-f2, ?_, by simp [h2y], fun v hv => by simp [h2p v hv]⟩
    simp; linear_combination -hc
  · refine ⟨(1 + f2 x)⁻¹ • (f1 + f2), ?_, ?_, fun v hv => by simp [h1p v hv, h2p v hv]⟩
    · simp [h1x]; field_simp
    · simp [h1y, h2y, hc]

theorem L_lib_1010_avoid {P Q : Submodule K V} (hP : P ≠ ⊤) (hQ : Q ≠ ⊤) :
    ∃ x, x ∉ P ∧ x ∉ Q := by
  obtain ⟨y, hy⟩ : ∃ y, y ∉ P := by
    by_contra h; push_neg at h; exact hP (eq_top_iff.2 fun v _ => h v)
  obtain ⟨z, hz⟩ : ∃ z, z ∉ Q := by
    by_contra h; push_neg at h; exact hQ (eq_top_iff.2 fun v _ => h v)
  by_cases hyQ : y ∈ Q
  · by_cases hzP : z ∈ P
    · refine ⟨y + z, fun h => hy ?_, fun h => hz ?_⟩
      · simpa using P.sub_mem h hzP
      · simpa using Q.sub_mem h hyQ
    · exact ⟨z, hzP, hz⟩
  · exact ⟨y, hy, hyQ⟩

theorem L_lib_1010_core (α β : V →ₗ[K] W) (x : V) (f : V →ₗ[K] K) (hfx : f x = 1)
    (hN : ∀ v, α v = β v → f v = 0) :
    finrank K (range ((α + f.smulRight (β x - α x)) - β)) + 1 = finrank K (range (α - β)) ∧
    finrank K (range (α - (α + f.smulRight (β x - α x)))) ≤ 1 ∧
    range (α + f.smulRight (β x - α x)) ≤ range α ⊔ K ∙ β x ∧
    range α ≤ range (α + f.smulRight (β x - α x)) ⊔ K ∙ α x ∧
    β x ∈ range (α + f.smulRight (β x - α x)) := by
  set α' := α + f.smulRight (β x - α x) with hα'
  have happ : ∀ v, α' v = α v + f v • (β x - α x) := fun v => by simp [α']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hnot : α x - β x ∉ range (α' - β) := by
      rintro ⟨v, hv⟩
      simp only [LinearMap.sub_apply, happ] at hv
      have h0 := hN (x - v + f v • x) (by
        simp only [map_add, map_sub, map_smul]
        linear_combination (norm := module) -hv)
      simp [hfx] at h0
    have heq : range (α' - β) ⊔ K ∙ (α x - β x) = range (α - β) := by
      apply le_antisymm
      · apply sup_le
        · rintro _ ⟨v, rfl⟩
          refine ⟨v - f v • x, ?_⟩
          simp only [LinearMap.sub_apply, happ, map_sub, map_smul]
          module
        · rw [Submodule.span_singleton_le_iff_mem]
          exact ⟨x, by simp⟩
      · rintro _ ⟨v, rfl⟩
        refine Submodule.mem_sup.2 ⟨(α' - β) v, ⟨v, rfl⟩, f v • (α x - β x),
          Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
        simp only [LinearMap.sub_apply, happ]
        module
    rw [← heq, L_lib_1010_addvec hnot]
  · have : range (α - α') ≤ K ∙ (β x - α x) := by
      rintro _ ⟨v, rfl⟩
      rw [Submodule.mem_span_singleton]
      exact ⟨-f v, by simp only [LinearMap.sub_apply, happ]; module⟩
    refine (Submodule.finrank_mono this).trans ?_
    simpa using finrank_span_le_card ({β x - α x} : Set W)
  · rintro _ ⟨v, rfl⟩
    refine Submodule.mem_sup.2 ⟨α (v - f v • x), ⟨_, rfl⟩, f v • β x,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    simp only [happ, map_sub, map_smul]
    module
  · rintro _ ⟨v, rfl⟩
    refine Submodule.mem_sup.2 ⟨α' (v - f v • x), ⟨_, rfl⟩, f v • α x,
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _), ?_⟩
    simp only [happ, map_sub, map_smul, hfx, smul_eq_mul, mul_one, sub_self, zero_smul]
    module
  · exact ⟨x, by simp [happ, hfx]⟩

theorem L_lib_1010_step (α β : V →ₗ[K] W) (n : ℕ) (h : finrank K (range (α - β)) = n + 1) :
    ∃ α' : V →ₗ[K] W, finrank K (range (α - α')) ≤ 1 ∧ finrank K (range (α' - β)) = n ∧
      finrank K ↥(range α' ⊔ range β) - finrank K (range α') =
        finrank K ↥(range α ⊔ range β) - finrank K (range α) - 1 ∧
      finrank K ↥(range α' ⊔ range β) - finrank K (range β) =
        finrank K ↥(range α ⊔ range β) - finrank K (range β) - 1 := by
  have hUs := Submodule.finrank_mono (le_sup_left : range α ≤ range α ⊔ range β)
  have hTs := Submodule.finrank_mono (le_sup_right : range β ≤ range α ⊔ range β)
  have rnα := LinearMap.finrank_range_add_finrank_ker α
  have rnβ := LinearMap.finrank_range_add_finrank_ker β
  by_cases hb : range α ≤ range β
  · -- image of α inside image of β
    have hsT : range α ⊔ range β = range β := sup_eq_right.2 hb
    obtain ⟨x, y, c, hxN, hyN, hαy, hcase⟩ : ∃ (x y : V) (c : K), α x ≠ β x ∧ α y ≠ β y ∧
        α y = c • β x ∧ (range β ≤ range α ∨ β x ∉ range α) := by
      by_cases ha : range β ≤ range α
      · obtain ⟨x, hx⟩ : ∃ x, α x ≠ β x := by
          by_contra hall
          push_neg at hall
          have : α - β = 0 := LinearMap.ext fun v => by simp [hall v]
          rw [this, LinearMap.range_zero, finrank_bot] at h
          omega
        by_cases hk : ∃ k, α k = 0 ∧ α k ≠ β k
        · obtain ⟨k, hk0, hk1⟩ := hk
          exact ⟨x, k, 0, hx, hk1, by simp [hk0], Or.inl ha⟩
        · push_neg at hk
          have hker : ker α ≤ ker β := fun v hv => by
            rw [mem_ker] at hv ⊢; rw [← hk v hv, hv]
          have hUT : range α = range β := le_antisymm hb ha
          have hkereq : ker α = ker β := Submodule.eq_of_le_of_finrank_eq hker (by
            rw [hUT] at rnα; omega)
          obtain ⟨y, hy⟩ : β x ∈ range α := ha ⟨x, rfl⟩
          refine ⟨x, y, 1, hx, fun hyy => hx ?_, by simp [hy], Or.inl ha⟩
          have : x - y ∈ ker α := by
            rw [hkereq, mem_ker, map_sub, ← hyy, hy, sub_self]
          rw [mem_ker, map_sub, sub_eq_zero] at this
          rw [this, hy]
      · obtain ⟨_, ⟨x, rfl⟩, hx⟩ := SetLike.not_le_iff_exists.1 ha
        have hxN : α x ≠ β x := fun he => hx (he ▸ ⟨x, rfl⟩)
        obtain ⟨k, hk0, hk1⟩ : ∃ k, α k = 0 ∧ α k ≠ β k := by
          by_contra hk
          push_neg at hk
          have hker : ker α ≤ ker β := fun v hv => by
            rw [mem_ker] at hv ⊢; rw [← hk v hv, hv]
          have h1 := Submodule.finrank_mono hker
          have h2 := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hb (fun he => ha he.ge))
          omega
        exact ⟨x, k, 0, hxN, hk1, by simp [hk0], Or.inr hx⟩
    have hmemN : ∀ v, v ∈ ker (α - β) ↔ α v = β v := fun v => by
      rw [mem_ker, LinearMap.sub_apply, sub_eq_zero]
    obtain ⟨f, hfx, hfy, hfN⟩ := L_lib_1010_dual2 (p := ker (α - β))
      (fun hh => hxN ((hmemN x).1 hh)) (fun hh => hyN ((hmemN y).1 hh))
    have hN : ∀ v, α v = β v → f v = 0 := fun v hv => hfN v ((hmemN v).2 hv)
    obtain ⟨h1, h2, h3, h4, h5⟩ := L_lib_1010_core α β x f hfx hN
    set α' := α + f.smulRight (β x - α x) with hα'
    have happ : ∀ v, α' v = α v + f v • (β x - α x) := fun v => by simp [α']
    have hαx : α x ∈ range α' := by
      have hm : f y • α x ∈ range α' := by
        have : f y • α x = (c + f y) • α' x - α' y := by
          simp only [happ, hfx, hαy, one_smul]
          module
        rw [this]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ⟨x, rfl⟩) ⟨y, rfl⟩
      exact (Submodule.smul_mem_iff _ hfy).1 hm
    have hU : range α ≤ range α' :=
      h4.trans (sup_le le_rfl ((Submodule.span_singleton_le_iff_mem _ _).2 hαx))
    have hα'T : range α' ≤ range β :=
      h3.trans (sup_le hb ((Submodule.span_singleton_le_iff_mem _ _).2 ⟨x, rfl⟩))
    have hs' : range α' ⊔ range β = range β := sup_eq_right.2 hα'T
    refine ⟨α', h2, by omega, ?_⟩
    rw [hs', hsT]
    have hr1 := Submodule.finrank_mono hU
    have hr2 := Submodule.finrank_mono hα'T
    rcases hcase with ha | hβU
    · have := Submodule.finrank_mono ha
      constructor <;> omega
    · have hge : range α ⊔ K ∙ β x ≤ range α' :=
        sup_le hU ((Submodule.span_singleton_le_iff_mem _ _).2 h5)
      have e1 := Submodule.finrank_mono hge
      have e2 := Submodule.finrank_mono h3
      rw [L_lib_1010_addvec hβU] at e1 e2
      constructor <;> omega
  · -- image of α not inside image of β
    obtain ⟨x, hxT, hx2⟩ : ∃ x, α x ∉ range β ∧ (β x ∉ range α ∨ range β ≤ range α) := by
      by_cases ha : range β ≤ range α
      · obtain ⟨_, ⟨x, rfl⟩, hx⟩ := SetLike.not_le_iff_exists.1 hb
        exact ⟨x, hx, Or.inr ha⟩
      · obtain ⟨x, hx1, hx2⟩ := L_lib_1010_avoid (P := (range β).comap α) (Q := (range α).comap β)
          (fun he => hb (by
            rintro _ ⟨v, rfl⟩
            have : v ∈ (range β).comap α := he ▸ Submodule.mem_top
            exact this))
          (fun he => ha (by
            rintro _ ⟨v, rfl⟩
            have : v ∈ (range α).comap β := he ▸ Submodule.mem_top
            exact this))
        exact ⟨x, hx1, Or.inl hx2⟩
    obtain ⟨g, hg1, hg0⟩ := L_lib_1010_dual hxT
    have hfx : (g ∘ₗ α) x = 1 := by simp [hg1]
    have hN : ∀ v, α v = β v → (g ∘ₗ α) v = 0 := fun v hv => by
      simp only [comp_apply]; rw [hv]; exact hg0 _ ⟨v, rfl⟩
    obtain ⟨h1, h2, h3, h4, h5⟩ := L_lib_1010_core α β x _ hfx hN
    set α' := α + (g ∘ₗ α).smulRight (β x - α x) with hα'
    have happ : ∀ v, α' v = α v + g (α v) • (β x - α x) := fun v => by simp [α']
    have hgβx : g (β x) = 0 := hg0 _ ⟨x, rfl⟩
    have hgα' : range α' ⊔ range β ≤ ker g := by
      apply sup_le
      · rintro _ ⟨v, rfl⟩
        rw [mem_ker, happ, map_add, map_smul, map_sub, hgβx, hg1, smul_eq_mul]
        ring
      · rintro _ ⟨v, rfl⟩
        exact hg0 _ ⟨v, rfl⟩
    have hnot : α x ∉ range α' ⊔ range β := fun hh => by
      have := hgα' hh
      rw [mem_ker, hg1] at this
      exact one_ne_zero this
    have hnot' : α x ∉ range α' := fun hh => hnot (Submodule.mem_sup_left hh)
    have hαxU : α x ∈ range α := ⟨x, rfl⟩
    have E1 : (range α' ⊔ range β) ⊔ K ∙ α x = range α ⊔ range β := by
      apply le_antisymm
      · apply sup_le
        · apply sup_le _ le_sup_right
          refine h3.trans (sup_le le_sup_left ?_)
          rw [Submodule.span_singleton_le_iff_mem]
          exact Submodule.mem_sup_right ⟨x, rfl⟩
        · rw [Submodule.span_singleton_le_iff_mem]
          exact Submodule.mem_sup_left hαxU
      · apply sup_le
        · exact h4.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        · exact le_sup_right.trans le_sup_left
    have e1 := L_lib_1010_addvec hnot
    rw [E1] at e1
    have e2 := L_lib_1010_addvec hnot'
    have hTs' := Submodule.finrank_mono (le_sup_right : range β ≤ range α' ⊔ range β)
    refine ⟨α', h2, by omega, ?_⟩
    rcases hx2 with hβU | ha
    · have E2 : range α' ⊔ K ∙ α x = range α ⊔ K ∙ β x := by
        apply le_antisymm
        · exact sup_le h3 ((Submodule.span_singleton_le_iff_mem _ _).2
            (Submodule.mem_sup_left hαxU))
        · exact sup_le h4 ((Submodule.span_singleton_le_iff_mem _ _).2
            (Submodule.mem_sup_left h5))
      rw [E2, L_lib_1010_addvec hβU] at e2
      constructor <;> omega
    · have E2 : range α' ⊔ K ∙ α x = range α := by
        apply le_antisymm
        · refine sup_le (h3.trans (sup_le le_rfl ?_)) ((Submodule.span_singleton_le_iff_mem _ _).2 hαxU)
          exact (Submodule.span_singleton_le_iff_mem _ _).2 (ha ⟨x, rfl⟩)
        · exact h4
      rw [E2] at e2
      have hsU : range α ⊔ range β = range α := sup_eq_left.2 ha
      have hh : finrank K ↥(range α ⊔ range β) = finrank K (range α) := by rw [hsU]
      constructor <;> omega

theorem L_lib_1010_tri (a b c : V →ₗ[K] W) :
    finrank K (range (a - c)) ≤ finrank K (range (a - b)) + finrank K (range (b - c)) := by
  have : a - c = (a - b) + (b - c) := by abel
  rw [this]
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem L_lib_1010_chain (Q : ℕ → V →ₗ[K] W) (n : ℕ)
    (hs : ∀ i < n, finrank K (range (Q i - Q (i+1))) ≤ 1) :
    ∀ i j, i ≤ j → j ≤ n → finrank K (range (Q i - Q j)) ≤ j - i := by
  intro i j hij hjn
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; simp
  | succ j ih =>
    rcases Nat.eq_or_lt_of_le hij with h | h
    · subst h; simp
    · have := ih (by omega) (by omega)
      have := hs j (by omega)
      have := L_lib_1010_tri (Q i) (Q j) (Q (j+1))
      omega

theorem L_lib_1010_path (β : V →ₗ[K] W) : ∀ (n : ℕ) (α : V →ₗ[K] W),
    finrank K (range (α - β)) = n →
    ∃ Q : ℕ → (V →ₗ[K] W), Q 0 = α ∧ Q n = β ∧
      (∀ i < n, finrank K (range (Q i - Q (i+1))) ≤ 1) ∧
      ∀ i ≤ n, finrank K ↥(range (Q i) ⊔ range β) - finrank K (range (Q i)) =
          finrank K ↥(range α ⊔ range β) - finrank K (range α) - i ∧
        finrank K ↥(range (Q i) ⊔ range β) - finrank K (range β) =
          finrank K ↥(range α ⊔ range β) - finrank K (range β) - i := by
  intro n
  induction n with
  | zero =>
    intro α h
    have h0 : range (α - β) = ⊥ := Submodule.finrank_eq_zero.1 h
    rw [LinearMap.range_eq_bot, sub_eq_zero] at h0
    subst h0
    refine ⟨fun _ => α, rfl, rfl, fun i hi => by omega, fun i hi => ?_⟩
    have : i = 0 := by omega
    subst this
    simp
  | succ n ih =>
    intro α h
    obtain ⟨α', h1, h2, h3, h4⟩ := L_lib_1010_step α β n h
    obtain ⟨Q', hQ0, hQn, hQs, hQd⟩ := ih α' h2
    refine ⟨fun i => Nat.rec α (fun j _ => Q' j) i, rfl, hQn, ?_, ?_⟩
    · intro i hi
      rcases i with _ | i
      · show finrank K (range (α - Q' 0)) ≤ 1
        rw [hQ0]; exact h1
      · exact hQs i (by omega)
    · intro i hi
      rcases i with _ | i
      · exact ⟨rfl, rfl⟩
      · have := hQd i (by omega)
        show finrank K ↥(range (Q' i) ⊔ range β) - finrank K (range (Q' i)) = _ ∧
          finrank K ↥(range (Q' i) ⊔ range β) - finrank K (range β) = _
        omega

end L_lib_1010_sec

theorem PEqualNP.Outside.L_lib_1010 : (∀ (K : Type) [Field K] (q r : ℕ) (H J : Matrix (Fin q) (Fin r) K),
  let size := fun (A : Matrix (Fin q) (Fin r) K) =>
    Matrix.rank (fun i z => Sum.elim (A i) (J i) z : Matrix (Fin q) (Fin r ⊕ Fin r) K)
  let d := Matrix.rank (H-J)
  ∃ P : Fin (d+1) → Matrix (Fin q) (Fin r) K,
    P 0 = H ∧ P (Fin.last d) = J ∧
    (∀ i j : Fin (d+1), i ≤ j → Matrix.rank (P i-P j) = j.val-i.val) ∧
    ∀ i : Fin (d+1),
      size (P i) - Matrix.rank (P i) = size H - Matrix.rank H - i.val ∧
      size (P i) - Matrix.rank J = size H - Matrix.rank J - i.val) := by
  intro K _ q r H J size d
  have hrk : ∀ M : Matrix (Fin q) (Fin r) K, M.rank = finrank K (range (Matrix.toLin' M)) :=
    fun M => by rw [Matrix.toLin'_apply']; rfl
  have hsz : ∀ A : Matrix (Fin q) (Fin r) K,
      size A = finrank K ↥(range (Matrix.toLin' A) ⊔ range (Matrix.toLin' J)) := by
    intro A
    show Matrix.rank (Matrix.fromCols A J) = _
    rw [Matrix.rank, Matrix.toLin'_apply', Matrix.toLin'_apply']
    suffices hR : range (Matrix.fromCols A J).mulVecLin = range A.mulVecLin ⊔ range J.mulVecLin by
      rw [hR]
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.fromCols_mulVec]
      exact Submodule.add_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
    · apply sup_le
      · rintro _ ⟨v, rfl⟩
        exact ⟨Sum.elim v 0, by simp [Matrix.fromCols_mulVec_sumElim]⟩
      · rintro _ ⟨v, rfl⟩
        exact ⟨Sum.elim 0 v, by simp [Matrix.fromCols_mulVec_sumElim]⟩
  have hd : finrank K (range (Matrix.toLin' H - Matrix.toLin' J)) = d := by
    rw [← map_sub, ← hrk]
  obtain ⟨Q, hQ0, hQn, hQs, hQd⟩ := L_lib_1010_path (Matrix.toLin' J) d (Matrix.toLin' H) hd
  have hQ : ∀ k, Matrix.toLin' (LinearMap.toMatrix' (Q k)) = Q k := fun k =>
    Matrix.toLin'_toMatrix' _
  have hch := L_lib_1010_chain Q d hQs
  refine ⟨fun i => LinearMap.toMatrix' (Q i.val), ?_, ?_, ?_, ?_⟩
  · simp [hQ0]
  · simp [hQn]
  · intro i j hij
    have hij' : i.val ≤ j.val := hij
    rw [hrk, map_sub, hQ, hQ]
    apply le_antisymm (hch i j hij' (by omega))
    have t1 := L_lib_1010_tri (Q 0) (Q i) (Q d)
    have t2 := L_lib_1010_tri (Q i) (Q j) (Q d)
    have c1 := hch 0 i (by omega) (by omega)
    have c2 := hch j d (by omega) (by omega)
    rw [hQ0, hQn, hd] at t1
    rw [hQ0] at c1
    rw [hQn] at c2 t2
    omega
  · intro i
    have := hQd i.val (by omega)
    simp only [hsz, hrk]
    rw [hQ]
    exact this
