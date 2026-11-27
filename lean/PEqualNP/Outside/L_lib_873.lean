import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_873_aux

private lemma finrank_subspace_identity {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (U V B : Submodule (ZMod 2) W) :
    Module.finrank (ZMod 2) ↥((U ⊔ V) ⊓ B) =
      Module.finrank (ZMod 2) ↥((U ⊓ B) ⊔ (V ⊓ B)) +
      (Module.finrank (ZMod 2) ↥((U ⊔ B) ⊓ (V ⊔ B)) -
        Module.finrank (ZMod 2) ↥((U ⊓ V) ⊔ B)) := by
  have hle : (U ⊓ V) ⊔ B ≤ (U ⊔ B) ⊓ (V ⊔ B) :=
    le_inf (sup_le (inf_le_left.trans le_sup_left) le_sup_right)
      (sup_le (inf_le_right.trans le_sup_left) le_sup_right)
  have hle_dim : Module.finrank (ZMod 2) ↥((U ⊓ V) ⊔ B) ≤
      Module.finrank (ZMod 2) ↥((U ⊔ B) ⊓ (V ⊔ B)) :=
    Submodule.finrank_mono hle
  have hA := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ V) B
  have hB := Submodule.finrank_sup_add_finrank_inf_eq U V
  have hC := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ B) (V ⊔ B)
  have hD := Submodule.finrank_sup_add_finrank_inf_eq U B
  have hE := Submodule.finrank_sup_add_finrank_inf_eq V B
  have hF := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ B) (V ⊓ B)
  have hG := Submodule.finrank_sup_add_finrank_inf_eq (U ⊓ V) B
  have hsup_eq : (U ⊔ B) ⊔ (V ⊔ B) = (U ⊔ V) ⊔ B := by
    apply le_antisymm
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
    · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
        (le_sup_right.trans le_sup_left)
  have hinf_eq : (U ⊓ B) ⊓ (V ⊓ B) = (U ⊓ V) ⊓ B := by
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
        (inf_le_left.trans inf_le_right)
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  rw [hsup_eq] at hC
  rw [hinf_eq] at hF
  omega

private lemma nat_card_subspace {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (S : Submodule (ZMod 2) W) :
    Nat.card ↥S = 2 ^ Module.finrank (ZMod 2) ↥S := by
  let b := Module.finBasis (ZMod 2) ↥S
  have heq : Nat.card ↥S = Nat.card (Fin (Module.finrank (ZMod 2) ↥S) → ZMod 2) :=
    Nat.card_congr b.equivFun.toEquiv
  rw [heq, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin, ZMod.card]

private lemma main_proof (f s u v m n : ℕ) (hf : 0 < f) (hu : 0 < u) (hv : 0 < v) :
    let F := ZMod 2
    let P := Fin s → F
    let E := Fin f × P
    let W := E → F
    ∀ (row : Fin u → Fin f → P → Fin m → F)
      (col : Fin v → Fin f → P → Fin n → F),
      let a := fun (i : Fin u) (j : Fin m) (e : E) =>
        row i e.1 e.2 j - row i e.1 0 j
      let b := fun (i : Fin v) (j : Fin n) (e : E) =>
        col i e.1 e.2 j - col i e.1 0 j
      let U : Submodule F W := ⨅ i : Fin u, Submodule.span F (Set.range (a i))
      let V : Submodule F W := ⨅ i : Fin v, Submodule.span F (Set.range (b i))
      let B : Submodule F W := Submodule.span F (Set.range (fun j : Fin s => fun e : E => e.2 j))
      let solo := Module.finrank F (((U ⊓ B) ⊔ (V ⊓ B)) : Submodule F W)
      let extra := Module.finrank F (((U ⊔ B) ⊓ (V ⊔ B)) : Submodule F W) -
        Module.finrank F (((U ⊓ V) ⊔ B) : Submodule F W)
      Nat.card {mask : P //
        ∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F),
          ∀ (i : Fin u) (j : Fin v) (e : E),
            (∑ h : Fin m, c i h * a i h e) + (∑ h : Fin n, t j h * b j h e) =
              ∑ h : Fin s, mask h * e.2 h} = 2 ^ (solo + extra) := by
  intro F P E W row col a b U V B solo extra
  let Φ : P →ₗ[F] W :=
    { toFun := fun mask e => ∑ h : Fin s, mask h * e.2 h
      map_add' := fun x y => by
        funext e
        change (∑ h : Fin s, (x h + y h) * e.2 h) = (∑ h : Fin s, x h * e.2 h) + (∑ h : Fin s, y h * e.2 h)
        simp only [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        funext e
        change (∑ h : Fin s, (r * x h) * e.2 h) = r * (∑ h : Fin s, x h * e.2 h)
        simp only [Finset.mul_sum, mul_assoc] }
  have hΦ_inj : Function.Injective Φ := by
    intro x y hxy
    funext k
    let ek : P := Pi.single k (1 : F)
    have hk := congrFun hxy (⟨0, hf⟩, ek)
    dsimp only [Φ, LinearMap.coe_mk, AddHom.coe_mk] at hk
    have h1 : (∑ h : Fin s, x h * ek h) = x k := by
      rw [Finset.sum_eq_single k]
      · simp [ek]
      · intro h _ hne; simp [ek, Pi.single_eq_of_ne hne]
      · intro hnot; exact absurd (Finset.mem_univ k) hnot
    have h2 : (∑ h : Fin s, y h * ek h) = y k := by
      rw [Finset.sum_eq_single k]
      · simp [ek]
      · intro h _ hne; simp [ek, Pi.single_eq_of_ne hne]
      · intro hnot; exact absurd (Finset.mem_univ k) hnot
    rw [h1, h2] at hk
    exact hk
  have hΦ_memB : ∀ mask : P, Φ mask ∈ B := by
    intro mask
    have hEq : Φ mask = ∑ h : Fin s, mask h • (fun e : E => e.2 h) := by
      funext e
      change (∑ h : Fin s, mask h * e.2 h) = (∑ h : Fin s, mask h • (fun e : E => e.2 h)) e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hEq]
    exact Submodule.sum_mem B fun h _ => Submodule.smul_mem B (mask h) (Submodule.subset_span ⟨h, rfl⟩)
  have hB_surj : ∀ w ∈ B, ∃ mask : P, Φ mask = w := by
    intro w hw
    obtain ⟨mask, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 hw
    refine ⟨mask, ?_⟩
    funext e
    change (∑ h : Fin s, mask h * e.2 h) = (∑ h : Fin s, mask h • (fun e : E => e.2 h)) e
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let S := {mask : P //
    ∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F),
      ∀ (i : Fin u) (j : Fin v) (e : E),
        (∑ h : Fin m, c i h * a i h e) + (∑ h : Fin n, t j h * b j h e) =
          ∑ h : Fin s, mask h * e.2 h}
  have hmem_iff : ∀ mask : P,
      (∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F),
        ∀ (i : Fin u) (j : Fin v) (e : E),
          (∑ h : Fin m, c i h * a i h e) + (∑ h : Fin n, t j h * b j h e) =
            ∑ h : Fin s, mask h * e.2 h) ↔ Φ mask ∈ U ⊔ V := by
    intro mask
    constructor
    · rintro ⟨c, t, hct⟩
      let r : Fin u → W := fun i => ∑ h : Fin m, c i h • a i h
      let l : Fin v → W := fun j => ∑ h : Fin n, t j h • b j h
      have hrl : ∀ i j, r i + l j = Φ mask := by
        intro i j
        funext e
        have h := hct i j e
        change (∑ h : Fin m, c i h • a i h) e + (∑ h : Fin n, t j h • b j h) e = ∑ h : Fin s, mask h * e.2 h
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact h
      let i0 : Fin u := ⟨0, hu⟩
      let j0 : Fin v := ⟨0, hv⟩
      have hr_const : ∀ i : Fin u, r i = r i0 := fun i => by
        exact add_right_cancel ((hrl i j0).trans (hrl i0 j0).symm)
      have hl_const : ∀ j : Fin v, l j = l j0 := fun j => by
        exact add_left_cancel ((hrl i0 j).trans (hrl i0 j0).symm)
      have hrU : r i0 ∈ U := by
        rw [Submodule.mem_iInf]
        intro i
        rw [← hr_const i]
        exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
      have hlV : l j0 ∈ V := by
        rw [Submodule.mem_iInf]
        intro j
        rw [← hl_const j]
        exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
      rw [← hrl i0 j0]
      exact Submodule.add_mem_sup hrU hlV
    · intro hUV
      rw [Submodule.mem_sup] at hUV
      obtain ⟨x, hxU, y, hyV, hxy⟩ := hUV
      have hx : ∀ i : Fin u, ∃ ci : Fin m → F, ∑ h : Fin m, ci h • a i h = x := by
        intro i
        have hi : x ∈ Submodule.span F (Set.range (a i)) := (Submodule.mem_iInf _).1 hxU i
        exact (Submodule.mem_span_range_iff_exists_fun F).1 hi
      have hy : ∀ j : Fin v, ∃ tj : Fin n → F, ∑ h : Fin n, tj h • b j h = y := by
        intro j
        have hj : y ∈ Submodule.span F (Set.range (b j)) := (Submodule.mem_iInf _).1 hyV j
        exact (Submodule.mem_span_range_iff_exists_fun F).1 hj
      refine ⟨fun i => (hx i).choose, fun j => (hy j).choose, fun i j e => ?_⟩
      have h1 := congrFun (hx i).choose_spec e
      have h2 := congrFun (hy j).choose_spec e
      have h3 := congrFun hxy e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
      rw [h1, h2]
      exact h3
  have hbij : Function.Bijective (fun z : S =>
      (⟨Φ z.1, ⟨(hmem_iff z.1).1 z.2, hΦ_memB z.1⟩⟩ : ↥((U ⊔ V) ⊓ B))) := by
    refine ⟨?_, ?_⟩
    · intro z1 z2 h
      apply Subtype.ext
      exact hΦ_inj (congrArg Subtype.val h)
    · rintro ⟨w, ⟨hwUV, hwB⟩⟩
      obtain ⟨mask, rfl⟩ := hB_surj w hwB
      exact ⟨⟨mask, (hmem_iff mask).2 hwUV⟩, rfl⟩
  have hcard : Nat.card S = Nat.card ↥((U ⊔ V) ⊓ B) :=
    Nat.card_congr (Equiv.ofBijective _ hbij)
  rw [hcard, nat_card_subspace ((U ⊔ V) ⊓ B), finrank_subspace_identity U V B]

end PEqualNP.Outside.L_lib_873_aux

theorem PEqualNP.Outside.L_lib_873 :
  (∀ (f s u v m n : ℕ), 0 < f → 0 < u → 0 < v →
  let F := ZMod 2
  let P := Fin s → F
  let E := Fin f × P
  let W := E → F
  ∀ (row : Fin u → Fin f → P → Fin m → F)
    (col : Fin v → Fin f → P → Fin n → F),
    let a := fun (i : Fin u) (j : Fin m) (e : E) =>
      row i e.1 e.2 j - row i e.1 0 j
    let b := fun (i : Fin v) (j : Fin n) (e : E) =>
      col i e.1 e.2 j - col i e.1 0 j
    let U : Submodule F W := ⨅ i : Fin u, Submodule.span F (Set.range (a i))
    let V : Submodule F W := ⨅ i : Fin v, Submodule.span F (Set.range (b i))
    let B : Submodule F W := Submodule.span F (Set.range (fun j : Fin s => fun e : E => e.2 j))
    let solo := Module.finrank F (((U ⊓ B) ⊔ (V ⊓ B)) : Submodule F W)
    let extra := Module.finrank F (((U ⊔ B) ⊓ (V ⊔ B)) : Submodule F W) -
      Module.finrank F (((U ⊓ V) ⊔ B) : Submodule F W)
    Nat.card {mask : P //
      ∃ (c : Fin u → Fin m → F) (t : Fin v → Fin n → F),
        ∀ (i : Fin u) (j : Fin v) (e : E),
          (∑ h : Fin m, c i h * a i h e) + (∑ h : Fin n, t j h * b j h e) =
            ∑ h : Fin s, mask h * e.2 h} = 2 ^ (solo + extra)) := by
  exact PEqualNP.Outside.L_lib_873_aux.main_proof
