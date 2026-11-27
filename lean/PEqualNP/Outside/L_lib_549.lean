import Mathlib

namespace PEqualNP.Outside.L_lib_549_aux

theorem foldl_mem_short_span {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (A : ι → V →ₗ[K] V) (s : V) (w : List ι) :
    w.foldl (fun x a => A a x) s ∈ Submodule.span K {x : V | ∃ w' : List ι,
      w'.length < Module.finrank K V ∧ w'.foldl (fun x a => A a x) s = x} := by
  let step := fun (x : V) (a : ι) => A a x
  let S := fun n : ℕ => Submodule.span K {x : V | ∃ u : List ι,
    u.length < n ∧ u.foldl step s = x}
  change w.foldl step s ∈ S (Module.finrank K V)
  have hmono : Monotone S := by
    intro i j hij
    apply Submodule.span_mono
    rintro x ⟨u, hu, rfl⟩
    exact ⟨u, lt_of_lt_of_le hu hij, rfl⟩
  have hstep (n : ℕ) (a : ι) : S n ≤ (S (n + 1)).comap (A a) := by
    apply Submodule.span_le.mpr
    rintro x ⟨u, hu, rfl⟩
    apply Submodule.subset_span (s := {x : V | ∃ u : List ι,
      u.length < n + 1 ∧ u.foldl step s = x})
    exact ⟨u ++ [a], by simpa using Nat.succ_lt_succ hu, by simp [step, List.foldl_append]⟩
  by_cases hflat : ∃ n < Module.finrank K V, S n = S (n + 1)
  · obtain ⟨n, hn, he⟩ := hflat
    have hs : s ∈ S n := by
      rw [he]
      exact Submodule.subset_span ⟨[], Nat.zero_lt_succ n, rfl⟩
    have hclosed (a : ι) {x : V} (hx : x ∈ S n) : step x a ∈ S n := by
      rw [he]
      exact hstep n a hx
    have hfold (u : List ι) (x : V) (hx : x ∈ S n) : u.foldl step x ∈ S n := by
      induction u generalizing x with
      | nil => exact hx
      | cons a u ih => exact ih _ (hclosed a hx)
    exact hmono hn.le (hfold w s hs)
  · have hrank (n : ℕ) (hn : n ≤ Module.finrank K V) : n ≤ Module.finrank K (S n) := by
      induction n with
      | zero => exact Nat.zero_le _
      | succ n ih =>
        have hlt : S n < S (n + 1) := lt_of_le_of_ne (hmono (Nat.le_succ n))
          (fun he => hflat ⟨n, hn, he⟩)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih (by omega))
          (Submodule.finrank_lt_finrank_of_lt hlt))
    have htop : S (Module.finrank K V) = ⊤ := Submodule.eq_top_of_finrank_eq
      ((Submodule.finrank_le _).antisymm (hrank _ le_rfl))
    rw [htop]
    exact Submodule.mem_top

def wordAction {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : ι → V →ₗ[K] V) : List ι → V →ₗ[K] V
  | [] => LinearMap.id
  | a :: t => (wordAction A t).comp (A a)

theorem wordAction_apply {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : ι → V →ₗ[K] V) (w : List ι) (x : V) :
    wordAction A w x = w.foldl (fun y a => A a y) x := by
  induction w generalizing x with
  | nil => rfl
  | cons a t ih => exact ih _

theorem backwards {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (A : ι → V →ₗ[K] V) (w : List ι) (f : V →ₗ[K] K) :
    w.reverse.foldl (fun g a => (A a).dualMap g) f = f.comp (wordAction A w) := by
  induction w with
  | nil => rfl
  | cons a t ih => simp only [List.reverse_cons, List.foldl_append, ih]; rfl

theorem assemble {K : Type} [Field K] (q d : ℕ) (s : Fin d → K)
    (A : Fin q → (Fin d → K) →ₗ[K] (Fin d → K)) (f : (Fin d → K) →ₗ[K] K)
    (hfront : ∀ w : List (Fin q), w.foldl (fun x a => A a x) s ∈ Submodule.span K
      {x | ∃ t : List (Fin q), t.length < Module.finrank K (Fin d → K) ∧ t.foldl (fun y a => A a y) s = x})
    (hback : ∀ w : List (Fin q), w.foldl (fun x a => (A a).dualMap x) f ∈ Submodule.span K
      {x | ∃ t : List (Fin q), t.length < Module.finrank K ((Fin d → K) →ₗ[K] K) ∧ t.foldl (fun y a => (A a).dualMap y) f = x}) :
    let val := fun w : List (Fin q) => f (w.foldl (fun x a => A a x) s)
    let H := fun u v : List (Fin q) => val (u ++ v)
    let R := Submodule.span K (Set.range H)
    FiniteDimensional K R ∧ R = Submodule.span K (H '' {u | u.length < d}) ∧
      ∀ g ∈ R, (∀ v : List (Fin q), v.length < d → g v = 0) → g = 0 := by
  classical
  dsimp only
  let obs : (Fin d → K) →ₗ[K] (List (Fin q) → K) := LinearMap.pi (fun w => f.comp (wordAction A w))
  let run := fun w : List (Fin q) => w.foldl (fun x a => A a x) s
  let H := fun u v : List (Fin q) => f (run (u ++ v))
  let R := Submodule.span K (Set.range H)
  change FiniteDimensional K R ∧ R = _ ∧ _
  have he (u : List (Fin q)) : H u = obs (run u) := by
    funext v; simp [H, obs, run, List.foldl_append, wordAction_apply]
  have hle : R ≤ LinearMap.range obs := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩; exact ⟨run u, (he u).symm⟩
  refine ⟨Submodule.finiteDimensional_of_le hle, le_antisymm ?_ ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨u, rfl⟩
    rw [he u]
    change run u ∈ (Submodule.span K (H '' {t | t.length < d})).comap obs
    refine (Submodule.span_le.mpr ?_) (hfront u)
    rintro _ ⟨t, ht, rfl⟩
    change obs (run t) ∈ Submodule.span K (H '' {t | t.length < d})
    rw [← he t]; apply Submodule.subset_span
    exact ⟨t, by simpa using ht, rfl⟩
  · apply Submodule.span_mono
    rintro _ ⟨u, _, rfl⟩; exact ⟨u, rfl⟩
  · intro g hg hz
    obtain ⟨x, rfl⟩ := hle hg
    funext w
    let ev : ((Fin d → K) →ₗ[K] K) →ₗ[K] K := LinearMap.applyₗ (R := K) (M₂ := K) x
    have hh : Submodule.span K {z | ∃ t : List (Fin q), t.length < Module.finrank K ((Fin d → K) →ₗ[K] K) ∧
        t.foldl (fun y a => (A a).dualMap y) f = z} ≤ LinearMap.ker ev := by
      apply Submodule.span_le.mpr
      rintro _ ⟨t, ht, rfl⟩
      have ht' : t.reverse.length < d := by simpa using ht
      have hb := backwards A t.reverse f
      rw [List.reverse_reverse] at hb
      rw [hb]; exact hz t.reverse ht'
    have final := hh (hback w.reverse)
    rw [backwards] at final
    exact final

open Module

private theorem basis_from_spanning_family {K M I : Type*} [Field K] [AddCommGroup M]
    [Module K M] [FiniteDimensional K M] (f : I → M)
    (h : ⊤ ≤ Submodule.span K (Set.range f)) (n : ℕ) (hn : finrank K M = n) :
    ∃ (b : Basis (Fin n) K M) (u : Fin n → I), ∀ i, f (u i) = b i := by
  classical
  let b := Basis.ofSpan h
  let := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFinOfCardEq ((Module.finrank_eq_card_basis b).symm.trans hn)
  have hmem (i : Fin n) : b (e.symm i) ∈ Set.range f :=
    Basis.ofSpan_subset h (Set.mem_range_self (e.symm i))
  choose u hu using hmem
  exact ⟨b.reindex e, u, fun i => (hu i).trans (b.reindex_apply e i).symm⟩

theorem exists_short_minor {K W : Type*} [Field K] (H : W → W → K) (short : W → Prop)
    [FiniteDimensional K (Submodule.span K (Set.range H))]
    (hspan : Submodule.span K (Set.range H) = Submodule.span K (H '' {u | short u}))
    (hsep : ∀ g ∈ Submodule.span K (Set.range H), (∀ v, short v → g v = 0) → g = 0) :
    ∃ U V : Fin (Module.finrank K (Submodule.span K (Set.range H))) → W,
      (∀ i, short (U i)) ∧ (∀ i, short (V i)) ∧
      (Matrix.of (fun i j => H (U i) (V j))).det ≠ 0 := by
  classical
  let R := Submodule.span K (Set.range H)
  let row (u : {w // short w}) : R := ⟨H u, Submodule.subset_span ⟨u, rfl⟩⟩
  have rows_span : Submodule.span K (Set.range row) = ⊤ := by
    apply Submodule.map_injective_of_injective R.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top]
    have hrange : R.subtype '' Set.range row = H '' {u | short u} := by
      ext g
      constructor
      · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
        exact ⟨u, u.property, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨row ⟨u, hu⟩, ⟨⟨u, hu⟩, rfl⟩, rfl⟩
    rw [hrange]
    exact hspan.symm
  obtain ⟨b, u, hu⟩ := basis_from_spanning_family row rows_span.ge _ rfl
  let ev (v : {w // short w}) : Module.Dual K R :=
    (LinearMap.proj (R := K) (φ := fun _ : W => K) v.val).comp R.subtype
  let E := Submodule.span K (Set.range ev)
  have hbot : E.dualCoannihilator = ⊥ := by
    apply eq_bot_iff.mpr
    intro g hg
    apply Subtype.ext
    apply hsep g g.property
    intro v hv
    exact (Submodule.mem_dualCoannihilator g).mp hg (ev ⟨v, hv⟩)
      (Submodule.subset_span ⟨⟨v, hv⟩, rfl⟩)
  have heval : E = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := E), hbot,
      Submodule.dualAnnihilator_bot]
  obtain ⟨d, v, hv⟩ := basis_from_spanning_family ev heval.ge (finrank K R)
    Subspace.dual_finrank_eq
  let A := Matrix.of (fun i j => H (u i) (v j))
  refine ⟨fun i => (u i).val, fun j => (v j).val, fun i => (u i).property,
    fun j => (v j).property, ?_⟩
  change A.det ≠ 0
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det A).mp
  apply Matrix.linearIndependent_col_iff_isUnit.mp
  have hcol : A.col = (d.map b.dualBasis.equivFun) := by
    funext j i
    change H (u i) (v j) = b.dualBasis.equivFun (d j) i
    rw [b.dualBasis_equivFun, ← hv j, ← hu i]
    rfl
  rw [hcol]
  exact (d.map b.dualBasis.equivFun).linearIndependent

end PEqualNP.Outside.L_lib_549_aux

open PEqualNP.Outside.L_lib_549_aux

theorem PEqualNP.Outside.L_lib_549 : (∀ (K : Type) [Field K] (q d : ℕ),
  let V := Fin d → K
  ∀ (s : V) (A : Fin q → V →ₗ[K] V),
    let run := fun (w : List (Fin q)) => w.foldl (fun x a => A a x) s
    ∀ f : V →ₗ[K] K,
      let val := fun w => f (run w)
      let R := Submodule.span K (Set.range (fun u : List (Fin q) => fun v : List (Fin q) => val (u ++ v)))
      let r := Module.finrank K R
      ∃ U W : Fin r → List (Fin q),
        (∀ i, (U i).length < d ∧ (W i).length < d) ∧
        (Matrix.of (fun i j : Fin r => val (U i ++ W j))).det ≠ 0) := by
  classical
  intro K _ q d
  dsimp only
  intro s A f
  let H := fun u v : List (Fin q) => f ((u ++ v).foldl (fun x a => A a x) s)
  let short := fun w : List (Fin q) => w.length < d
  obtain ⟨hfd, hspan, hsep⟩ := assemble q d s A f (foldl_mem_short_span A s)
    (foldl_mem_short_span (fun a => (A a).dualMap) f)
  letI : FiniteDimensional K (Submodule.span K (Set.range H)) := hfd
  obtain ⟨U, W, hu, hw, hdet⟩ := exists_short_minor H short hspan hsep
  exact ⟨U, W, fun i => ⟨hu i, hw i⟩, hdet⟩
