import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_389_aux

private lemma zmod2_decide_eq {a b c : ZMod 2} :
    (decide (a = c) = decide (b = c)) ↔ a = b := by
  revert a b c
  decide

private lemma zmod2_decide_zero {a : ZMod 2} {t : Bool} :
    (decide (a = 0) = t) ↔ a = (if t then 0 else 1) := by
  revert a t
  decide

private lemma card_submodule_zmod2 {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype V] (S : Submodule (ZMod 2) V) [Fintype S] :
    Fintype.card S = 2 ^ Module.finrank (ZMod 2) S := by
  have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := S)
  simp only [Nat.card_eq_fintype_card, ZMod.card] at h1
  exact h1

private lemma tree_to_flat (n m : ℕ)
    (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (allowed : Set (Set (Fin m → ZMod 2))) (K : ℕ)
    (htree : ∃ (N J : Finset (List Bool))
      (query : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
      (bias : List Bool → ZMod 2) (out : List Bool → Set (Fin m → ZMod 2)),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) →
          z.2 + Q z.1 ∈ out p) :
    ∃ (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2)))
      (base : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (L : Set (Fin m → ZMod 2)), L ∈ allowed ∧
      2 ^ (n + m) ≤ K * 2 ^ (Module.finrank (ZMod 2) S) ∧
      ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), z - base ∈ S → z.2 + Q z.1 ∈ L := by
  classical
  rcases htree with ⟨N, J, query, bias, out, hroot, hJN, _, hchild, hK, hleaf⟩
  let V := (Fin n → ZMod 2) × (Fin m → ZMod 2)
  let reaches : List Bool → V → Prop := fun p z =>
    ∀ j : Fin p.length, decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j
  let maxLen : ℕ := (N.image List.length).max' ⟨0, Finset.mem_image.mpr ⟨[], hroot, rfl⟩⟩
  have hle_max : ∀ p ∈ N, p.length ≤ maxLen := fun p hp =>
    Finset.le_max' _ _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have hreach_leaf : ∀ (k : ℕ) (p : List Bool) (z : V),
      p ∈ N → reaches p z → maxLen - p.length ≤ k →
      ∃ q ∈ N \ J, reaches q z := by
    intro k
    induction k with
    | zero =>
      intro p z hp hrz hk
      by_cases hJ : p ∈ J
      · exfalso
        have hch := (hchild p hJ).1
        have h1 := hle_max (p ++ [false]) hch
        simp at h1
        omega
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hrz⟩
    | succ k ih =>
      intro p z hp hrz hk
      by_cases hJ : p ∈ J
      · let t : Bool := decide (query p z = bias p)
        have hch : p ++ [t] ∈ N := by
          cases ht : t
          · exact (hchild p hJ).1
          · exact (hchild p hJ).2
        have hrz' : reaches (p ++ [t]) z := by
          intro j
          by_cases hj : j.val < p.length
          · have htake : (p ++ [t]).take j.val = p.take j.val :=
              List.take_append_of_le_length (le_of_lt hj)
            have hget : (p ++ [t]).get j = p.get ⟨j.val, hj⟩ := by
              simp [List.getElem_append_left hj]
            rw [htake, hget]
            exact hrz ⟨j.val, hj⟩
          · have hjeq : j.val = p.length := by
              have hlen : j.val < (p ++ [t]).length := j.isLt
              simp at hlen
              omega
            have htake : (p ++ [t]).take j.val = p := by
              rw [hjeq, List.take_left]
            have hget : (p ++ [t]).get j = t := by
              simp [hjeq]
            rw [htake, hget]
        have hlen' : (p ++ [t]).length = p.length + 1 := by simp
        exact ih (p ++ [t]) z hch hrz' (by omega)
      · exact ⟨p, Finset.mem_sdiff.mpr ⟨hp, hJ⟩, hrz⟩
  have hevery : ∀ z : V, ∃ q ∈ N \ J, reaches q z := fun z =>
    hreach_leaf maxLen [] z hroot (fun j => Fin.elim0 j) (by simp)
  let cell : List Bool → Finset V := fun p => Finset.univ.filter (fun z => reaches p z)
  have hcover : (Finset.univ : Finset V) ⊆ (N \ J).biUnion cell := by
    intro z _
    rcases hevery z with ⟨q, hq, hrz⟩
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_filter.mpr ⟨Finset.mem_univ z, hrz⟩⟩
  have hcardV : (Finset.univ : Finset V).card = 2 ^ (n + m) := by
    rw [Finset.card_univ]
    simp [V, Fintype.card_prod, Fintype.card_pi, ZMod.card, pow_add]
  have hne : (N \ J).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hc := Finset.card_le_card hcover
    rw [hcardV, h, Finset.biUnion_empty, Finset.card_empty] at hc
    have hpos : 0 < 2 ^ (n + m) := by positivity
    omega
  rcases Finset.exists_max_image (N \ J) (fun p => (cell p).card) hne with ⟨p, hp, hmax⟩
  have hbound : 2 ^ (n + m) ≤ K * (cell p).card := by
    calc 2 ^ (n + m) = (Finset.univ : Finset V).card := hcardV.symm
      _ ≤ ((N \ J).biUnion cell).card := Finset.card_le_card hcover
      _ ≤ ∑ q ∈ N \ J, (cell q).card := Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ N \ J, (cell p).card := Finset.sum_le_sum (fun q hq => hmax q hq)
      _ = (N \ J).card * (cell p).card := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ K * (cell p).card := Nat.mul_le_mul_right _ hK
  have hcell_ne : (cell p).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty, mul_zero] at hbound
    have hpos : 0 < 2 ^ (n + m) := by positivity
    omega
  rcases hcell_ne with ⟨base, hbase_mem⟩
  have hbase : reaches p base := (Finset.mem_filter.mp hbase_mem).2
  let S : Submodule (ZMod 2) V := ⨅ j : Fin p.length, LinearMap.ker (query (p.take j.val))
  have hmem_iff : ∀ z : V, z ∈ cell p ↔ z - base ∈ S := by
    intro z
    simp only [cell, Finset.mem_filter, Finset.mem_univ, true_and, S, Submodule.mem_iInf,
      LinearMap.mem_ker, map_sub, sub_eq_zero]
    constructor
    · intro hz j
      have h1 : decide (query (p.take j.val) z = bias (p.take j.val)) =
          decide (query (p.take j.val) base = bias (p.take j.val)) := (hz j).trans (hbase j).symm
      exact zmod2_decide_eq.mp h1
    · intro hz j
      rw [hz j]
      exact hbase j
  have hcell_card : (cell p).card = 2 ^ Module.finrank (ZMod 2) S := by
    let e : S ≃ {z : V // z ∈ cell p} :=
      { toFun := fun s => ⟨s.1 + base, (hmem_iff (s.1 + base)).mpr (by simp [s.2])⟩
        invFun := fun z => ⟨z.1 - base, (hmem_iff z.1).mp z.2⟩
        left_inv := fun s => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    rw [← Fintype.card_coe (cell p), ← Fintype.card_congr e]
    exact card_submodule_zmod2 S
  rw [hcell_card] at hbound
  exact ⟨S, base, out p, (hleaf p hp).1, hbound, fun z hz =>
    (hleaf p hp).2 z ((Finset.mem_filter.mp ((hmem_iff z).mpr hz)).2)⟩

private lemma flat_to_batches (n m : ℕ)
    (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (hQ : ∀ a : Fin n → ZMod 2, ∃ B : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2),
      ∀ h : Fin n → ZMod 2, Q (a + h) = Q a + Q h - Q 0 + B h)
    (allowed : Set (Set (Fin m → ZMod 2)))
    (hallowed : ∀ L ∈ allowed, ∀ v : Fin m → ZMod 2, {z | z - v ∈ L} ∈ allowed) (K : ℕ)
    (hflat : ∃ (S : Submodule (ZMod 2) ((Fin n → ZMod 2) × (Fin m → ZMod 2)))
      (base : (Fin n → ZMod 2) × (Fin m → ZMod 2)) (L : Set (Fin m → ZMod 2)), L ∈ allowed ∧
      2 ^ (n + m) ≤ K * 2 ^ (Module.finrank (ZMod 2) S) ∧
      ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), z - base ∈ S → z.2 + Q z.1 ∈ L) :
    ∃ (a b : ℕ) (first : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2))
      (second : (Fin a → ZMod 2) → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] (Fin b → ZMod 2))
      (readout : (Fin a → ZMod 2) → (Fin b → ZMod 2) → Set (Fin m → ZMod 2)),
      2 ^ (a + b) ≤ K ∧ ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2),
        let L := readout (first z.1) (second (first z.1) z)
        L ∈ allowed ∧ z.2 + Q z.1 ∈ L := by
  classical
  rcases hflat with ⟨S, base, L, hL, hK, hS⟩
  let F := ZMod 2
  let X := Fin n → F
  let Y := Fin m → F
  let SX : Submodule F X := S.map (LinearMap.fst F X Y)
  let P : Submodule F (X × Y) := SX.prod (⊤ : Submodule F Y)
  have hSP : S ≤ P := by
    intro p hp
    exact ⟨Submodule.mem_map.mpr ⟨p, hp, rfl⟩, trivial⟩
  have hfrX : Module.finrank F X = n := Module.finrank_fin_fun F
  have hfrY : Module.finrank F Y = m := Module.finrank_fin_fun F
  have hfrSX_le : Module.finrank F SX ≤ n :=
    (Submodule.finrank_le SX).trans (le_of_eq hfrX)
  have hfrP : Module.finrank F P = Module.finrank F SX + m := by
    have h1 : Module.finrank F (SX × (⊤ : Submodule F Y)) =
        Module.finrank F SX + Module.finrank F (⊤ : Submodule F Y) :=
      Module.finrank_prod
    have h2 : Module.finrank F (⊤ : Submodule F Y) = m := by
      rw [finrank_top, hfrY]
    have eP : P ≃ₗ[F] (SX × (⊤ : Submodule F Y)) :=
      { toFun := fun p => (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
        invFun := fun q => ⟨(q.1.1, q.2.1), ⟨q.1.2, q.2.2⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [eP.finrank_eq, h1, h2]
  have hfrS_le : Module.finrank F S ≤ Module.finrank F SX + m := by
    rw [← hfrP]
    exact Submodule.finrank_mono hSP
  let a : ℕ := n - Module.finrank F SX
  let b : ℕ := Module.finrank F SX + m - Module.finrank F S
  have hab : a + b + Module.finrank F S = n + m := by omega
  have h2ab : 2 ^ (a + b) ≤ K := by
    have h1 : 2 ^ (a + b) * 2 ^ Module.finrank F S ≤ K * 2 ^ Module.finrank F S := by
      rw [← pow_add, hab]
      exact hK
    exact Nat.le_of_mul_le_mul_right h1 (by positivity)
  have hfrQ1 : Module.finrank F (X ⧸ SX) = Module.finrank F (Fin a → F) := by
    have h := Submodule.finrank_quotient_add_finrank SX
    rw [hfrX] at h
    rw [Module.finrank_fin_fun]
    omega
  let e1 : (X ⧸ SX) ≃ₗ[F] (Fin a → F) := LinearEquiv.ofFinrankEq _ _ hfrQ1
  let first : X →ₗ[F] (Fin a → F) := e1.toLinearMap.comp SX.mkQ
  have hker_first : LinearMap.ker first = SX := by
    ext x
    simp [first]
  have hfirst_surj : Function.Surjective first :=
    e1.surjective.comp (Submodule.mkQ_surjective SX)
  let c : (Fin a → F) → X := fun u => Classical.choose (hfirst_surj u)
  have hc : ∀ u, first (c u) = u := fun u => Classical.choose_spec (hfirst_surj u)
  let B_of : X → (X →ₗ[F] Y) := fun x => Classical.choose (hQ x)
  have hB_of : ∀ x h, Q (x + h) = Q x + Q h - Q 0 + B_of x h :=
    fun x => Classical.choose_spec (hQ x)
  let D : (Fin a → F) → (X →ₗ[F] Y) := fun u => B_of (c u) - B_of base.1
  let shear : (Fin a → F) → ((X × Y) ≃ₗ[F] (X × Y)) := fun u =>
    { toFun := fun p => (p.1, p.2 - D u p.1)
      invFun := fun p => (p.1, p.2 + D u p.1)
      map_add' := fun p q => by
        apply Prod.ext
        · rfl
        · dsimp only [Prod.fst_add, Prod.snd_add]
          rw [map_add]
          abel
      map_smul' := fun r p => by
        apply Prod.ext
        · rfl
        · dsimp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply]
          rw [map_smul, smul_sub]
      left_inv := fun p => by
        apply Prod.ext
        · rfl
        · dsimp only
          abel
      right_inv := fun p => by
        apply Prod.ext
        · rfl
        · dsimp only
          abel }
  let Su : (Fin a → F) → Submodule F (X × Y) := fun u => S.map (shear u).toLinearMap
  have hSu_le : ∀ u, Su u ≤ P := by
    intro u p hp
    rcases Submodule.mem_map.mp hp with ⟨q, hq, rfl⟩
    exact ⟨Submodule.mem_map.mpr ⟨q, hq, rfl⟩, trivial⟩
  have hfrSu : ∀ u, Module.finrank F (Su u) = Module.finrank F S := fun u =>
    LinearEquiv.finrank_map_eq (shear u) S
  let SuP : (Fin a → F) → Submodule F P := fun u => (Su u).comap P.subtype
  have hfrSuP : ∀ u, Module.finrank F (SuP u) = Module.finrank F S := by
    intro u
    let e : SuP u ≃ₗ[F] Su u :=
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hSu_le u y.2⟩, y.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [e.finrank_eq, hfrSu u]
  rcases Submodule.exists_isCompl P with ⟨P', hPP'⟩
  let projP : (X × Y) →ₗ[F] P := Submodule.projectionOnto P P' hPP'
  have hprojP : ∀ p : P, projP p.1 = p := fun p =>
    Submodule.projectionOnto_apply_left hPP' p
  let second : (Fin a → F) → ((X × Y) →ₗ[F] (Fin b → F)) := fun u =>
    have hfrQ2 : Module.finrank F (P ⧸ SuP u) = Module.finrank F (Fin b → F) := by
      have h := Submodule.finrank_quotient_add_finrank (SuP u)
      rw [hfrP, hfrSuP u] at h
      rw [Module.finrank_fin_fun]
      omega
    (LinearEquiv.ofFinrankEq _ _ hfrQ2).toLinearMap.comp ((SuP u).mkQ.comp projP)
  have hker_second : ∀ u (p : X × Y), p ∈ P → (second u p = 0 ↔ p ∈ Su u) := by
    intro u p hp
    have hfrQ2 : Module.finrank F (P ⧸ SuP u) = Module.finrank F (Fin b → F) := by
      have h := Submodule.finrank_quotient_add_finrank (SuP u)
      rw [hfrP, hfrSuP u] at h
      rw [Module.finrank_fin_fun]
      omega
    change (LinearEquiv.ofFinrankEq _ _ hfrQ2) ((SuP u).mkQ (projP p)) = 0 ↔ p ∈ Su u
    rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have hpp : projP p = ⟨p, hp⟩ := hprojP ⟨p, hp⟩
    rw [hpp]
    rfl
  let readout : (Fin a → F) → (Fin b → F) → Set Y := fun u w =>
    if h : ∃ y : Y, second u (c u, y) = w then
      let ystar := Classical.choose h
      let v := ystar - base.2 + Q (c u) - Q base.1
      {t : Y | t - v ∈ L}
    else L
  refine ⟨a, b, first, second, readout, h2ab, ?_⟩
  intro z
  set u := first z.1
  set w := second u z
  have hex : ∃ y : Y, second u (c u, y) = w := by
    have hdiff_x : z.1 - c u ∈ SX := by
      rw [← hker_first, LinearMap.mem_ker, map_sub, hc u, sub_self]
    rcases Submodule.mem_map.mp hdiff_x with ⟨q, hq, hq1⟩
    let y' : Y := z.2 - (q.2 - D u q.1)
    refine ⟨y', ?_⟩
    have hsh : shear u q ∈ Su u := Submodule.mem_map.mpr ⟨q, hq, rfl⟩
    have hsub : z - (c u, y') = shear u q := by
      apply Prod.ext
      · change z.1 - c u = q.1
        exact hq1.symm
      · change z.2 - (z.2 - (q.2 - D u q.1)) = q.2 - D u q.1
        abel
    have hzero : second u (z - (c u, y')) = 0 := by
      rw [hsub]
      exact (hker_second u _ (hSu_le u hsh)).mpr hsh
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  have hread : readout u w =
      {t : Y | t - (Classical.choose hex - base.2 + Q (c u) - Q base.1) ∈ L} := by
    simp only [readout, hex, ↓reduceDIte]
  rw [hread]
  refine ⟨hallowed L hL _, ?_⟩
  set ystar := Classical.choose hex
  have hystar : second u (c u, ystar) = w := Classical.choose_spec hex
  have hdiffP : z - (c u, ystar) ∈ P := by
    refine ⟨?_, trivial⟩
    change z.1 - c u ∈ SX
    rw [← hker_first, LinearMap.mem_ker, map_sub, hc u, sub_self]
  have hdiffSu : z - (c u, ystar) ∈ Su u := by
    rw [← hker_second u _ hdiffP, map_sub, hystar, sub_self]
  rcases Submodule.mem_map.mp hdiffSu with ⟨q, hq, hqeq⟩
  have hzx : z.1 = c u + q.1 := by
    have h1 : z.1 - c u = q.1 := congrArg Prod.fst hqeq.symm
    calc z.1 = c u + (z.1 - c u) := by abel
      _ = c u + q.1 := by rw [h1]
  have hzy : z.2 = ystar + q.2 - D u q.1 := by
    have h2 : z.2 - ystar = q.2 - D u q.1 := congrArg Prod.snd hqeq.symm
    calc z.2 = (z.2 - ystar) + ystar := by abel
      _ = (q.2 - D u q.1) + ystar := by rw [h2]
      _ = ystar + q.2 - D u q.1 := by abel
  have hQdiff : Q (c u + q.1) = Q (base.1 + q.1) + Q (c u) - Q base.1 + D u q.1 := by
    have h1 := hB_of (c u) q.1
    have h2 := hB_of base.1 q.1
    have hD : D u q.1 = B_of (c u) q.1 - B_of base.1 q.1 := rfl
    rw [h1, h2, hD]
    abel
  have hbase_mem : (base.1 + q.1, base.2 + q.2) - base ∈ S := by
    have : (base.1 + q.1, base.2 + q.2) - base = q := by
      apply Prod.ext <;> simp
    rw [this]
    exact hq
  have hgood := hS (base.1 + q.1, base.2 + q.2) hbase_mem
  have heq : (z.2 + Q z.1) - (ystar - base.2 + Q (c u) - Q base.1) =
      (base.2 + q.2) + Q (base.1 + q.1) := by
    rw [hzx, hzy, hQdiff]
    abel
  change (z.2 + Q z.1) - (ystar - base.2 + Q (c u) - Q base.1) ∈ L
  rw [heq]
  exact hgood

private lemma batches_to_tree (n m : ℕ)
    (Q : (Fin n → ZMod 2) → (Fin m → ZMod 2))
    (allowed : Set (Set (Fin m → ZMod 2))) (K : ℕ)
    (hbatches : ∃ (a b : ℕ) (first : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin a → ZMod 2))
      (second : (Fin a → ZMod 2) → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] (Fin b → ZMod 2))
      (readout : (Fin a → ZMod 2) → (Fin b → ZMod 2) → Set (Fin m → ZMod 2)),
      2 ^ (a + b) ≤ K ∧ ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2),
        let L := readout (first z.1) (second (first z.1) z)
        L ∈ allowed ∧ z.2 + Q z.1 ∈ L) :
    ∃ (N J : Finset (List Bool))
      (query : List Bool → ((Fin n → ZMod 2) × (Fin m → ZMod 2)) →ₗ[ZMod 2] ZMod 2)
      (bias : List Bool → ZMod 2) (out : List Bool → Set (Fin m → ZMod 2)),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : (Fin n → ZMod 2) × (Fin m → ZMod 2), (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) →
          z.2 + Q z.1 ∈ out p := by
  classical
  rcases hbatches with ⟨a, b, first, second, readout, hK, hbatch⟩
  let F := ZMod 2
  let X := Fin n → F
  let Y := Fin m → F
  let layer : ℕ → Finset (List Bool) := fun k =>
    (Finset.univ : Finset (Fin k → Bool)).image List.ofFn
  have hmem_layer : ∀ k (p : List Bool), p ∈ layer k ↔ p.length = k := by
    intro k p
    simp only [layer, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨f, rfl⟩
      exact List.length_ofFn
    · intro hk
      refine ⟨fun i => p.get ⟨i.val, hk.symm ▸ i.isLt⟩, ?_⟩
      apply List.ext_getElem
      · simp [hk]
      · intro i hi1 hi2
        simp
  let N : Finset (List Bool) := (Finset.range (a + b + 1)).biUnion layer
  let J : Finset (List Bool) := (Finset.range (a + b)).biUnion layer
  have hmemN : ∀ p, p ∈ N ↔ p.length ≤ a + b := by
    intro p
    simp only [N, Finset.mem_biUnion, Finset.mem_range, hmem_layer]
    constructor
    · rintro ⟨k, hk, hlen⟩; omega
    · intro hlen; exact ⟨p.length, by omega, rfl⟩
  have hmemJ : ∀ p, p ∈ J ↔ p.length < a + b := by
    intro p
    simp only [J, Finset.mem_biUnion, Finset.mem_range, hmem_layer]
    constructor
    · rintro ⟨k, hk, hlen⟩; omega
    · intro hlen; exact ⟨p.length, hlen, rfl⟩
  have hNJ : N \ J = layer (a + b) := by
    ext p
    simp only [Finset.mem_sdiff, hmemN, hmemJ, hmem_layer]
    omega
  have hcard_NJ : (N \ J).card ≤ K := by
    rw [hNJ]
    calc (layer (a + b)).card ≤ (Finset.univ : Finset (Fin (a + b) → Bool)).card :=
          Finset.card_image_le
      _ = 2 ^ (a + b) := by simp
      _ ≤ K := hK
  let b2f : Bool → F := fun t => if t then 0 else 1
  let decU : List Bool → (Fin a → F) := fun p i => b2f (p.getD i.val false)
  let decV : List Bool → (Fin b → F) := fun p j => b2f (p.getD (a + j.val) false)
  let query : List Bool → ((X × Y) →ₗ[F] F) := fun p =>
    if h1 : p.length < a then
      (LinearMap.proj ⟨p.length, h1⟩).comp (first.comp (LinearMap.fst F X Y))
    else if h2 : p.length < a + b then
      (LinearMap.proj ⟨p.length - a, by omega⟩).comp (second (decU p))
    else 0
  let bias : List Bool → F := fun _ => 0
  let out : List Bool → Set Y := fun p =>
    if ∃ z : X × Y, first z.1 = decU p ∧ second (first z.1) z = decV p then
      readout (decU p) (decV p)
    else readout (first 0) (second (first 0) (0, 0))
  refine ⟨N, J, query, bias, out, ?_, ?_, ?_, ?_, hcard_NJ, ?_⟩
  · rw [hmemN]; simp
  · intro p hp
    rw [hmemN]
    exact Nat.le_of_lt ((hmemJ p).mp hp)
  · intro p t hp
    rw [hmemJ]
    have hlen := (hmemN (p ++ [t])).mp hp
    simp at hlen
    omega
  · intro p hp
    have hlen := (hmemJ p).mp hp
    constructor <;> rw [hmemN] <;> simp <;> omega
  · intro p hp
    have hplen : p.length = a + b := by
      rw [hNJ, hmem_layer] at hp
      exact hp
    constructor
    · dsimp only [out]
      split_ifs with h
      · rcases h with ⟨z, h1, h2⟩
        rw [← h1, ← h2]
        exact (hbatch z).1
      · exact (hbatch (0, 0)).1
    · intro z hreach
      have hu : first z.1 = decU p := by
        ext i
        have hi : i.val < p.length := by omega
        have hstep := hreach ⟨i.val, hi⟩
        have htlen : (p.take i.val).length = i.val := List.length_take_of_le (le_of_lt hi)
        have hq : query (p.take i.val) z = first z.1 i := by
          dsimp only [query]
          rw [dite_eq_left (by omega : (p.take i.val).length < a)]
          simp [htlen]
        rw [hq] at hstep
        have hval := zmod2_decide_zero.mp hstep
        simp only [decU, b2f]
        have hgetD : p.getD i.val false = p.get ⟨i.val, hi⟩ := by
          simp [List.getD_eq_getElem?_getD, hi]
        rw [hgetD]
        exact hval
      have hv : second (first z.1) z = decV p := by
        ext j
        have hj : a + j.val < p.length := by omega
        have hstep := hreach ⟨a + j.val, hj⟩
        have htlen : (p.take (a + j.val)).length = a + j.val :=
          List.length_take_of_le (le_of_lt hj)
        have hdec : decU (p.take (a + j.val)) = decU p := by
          ext i
          simp only [decU]
          have hi1 : i.val < (p.take (a + j.val)).length := by omega
          have hi2 : i.val < p.length := by omega
          rw [List.getD_eq_getElem _ _ hi1, List.getD_eq_getElem _ _ hi2, List.getElem_take]
        have hq : query (p.take (a + j.val)) z = second (first z.1) z j := by
          dsimp only [query]
          rw [dite_eq_right (by omega : ¬ (p.take (a + j.val)).length < a)]
          rw [dite_eq_left (by omega : (p.take (a + j.val)).length < a + b)]
          rw [hdec, ← hu]
          simp [htlen]
        rw [hq] at hstep
        have hval := zmod2_decide_zero.mp hstep
        simp only [decV, b2f]
        have hgetD : p.getD (a + j.val) false = p.get ⟨a + j.val, hj⟩ := by
          simp [List.getD_eq_getElem?_getD, hj]
        rw [hgetD]
        exact hval
      have hex : ∃ z' : X × Y, first z'.1 = decU p ∧ second (first z'.1) z' = decV p :=
        ⟨z, hu, hv⟩
      have hout : out p = readout (decU p) (decV p) := by
        simp only [out, ite_eq_left_iff]
        intro hne
        exact absurd hex hne
      rw [hout, ← hu, ← hv]
      exact (hbatch z).2

end PEqualNP.Outside.L_pcx_389_aux

theorem PEqualNP.Outside.L_pcx_389 : (∀ (n m : ℕ),
  let F := ZMod 2
  let X := Fin n → F
  let Y := Fin m → F
  let tree := fun (target : (X × Y) → Y) (allowed : Set (Set Y)) (K : ℕ) =>
    ∃ (N J : Finset (List Bool)) (query : List Bool → (X × Y) →ₗ[F] F)
      (bias : List Bool → F) (out : List Bool → Set Y),
      [] ∈ N ∧ J ⊆ N ∧
      (∀ (p : List Bool) (t : Bool), p ++ [t] ∈ N → p ∈ J) ∧
      (∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N) ∧
      (N \ J).card ≤ K ∧ ∀ p ∈ N \ J, out p ∈ allowed ∧
        ∀ z : X × Y, (∀ j : Fin p.length,
          decide (query (p.take j.val) z = bias (p.take j.val)) = p.get j) → target z ∈ out p
  ∀ (Q : X → Y)
    (_ : ∀ a : X, ∃ B : X →ₗ[F] Y, ∀ h : X, Q (a+h) = Q a + Q h - Q 0 + B h)
    (allowed : Set (Set Y))
    (_ : ∀ L ∈ allowed, ∀ v : Y, {z : Y | z-v ∈ L} ∈ allowed) (K : ℕ),
    let target := fun z : X × Y => z.2 + Q z.1
    let flat := ∃ (S : Submodule F (X × Y)) (base : X × Y) (L : Set Y), L ∈ allowed ∧
      2^(n+m) ≤ K * 2^(Module.finrank F S) ∧
      ∀ z : X × Y, z-base ∈ S → target z ∈ L
    let batches := ∃ (a b : ℕ) (first : X →ₗ[F] (Fin a → F))
      (second : (Fin a → F) → (X × Y) →ₗ[F] (Fin b → F))
      (readout : (Fin a → F) → (Fin b → F) → Set Y),
      2^(a+b) ≤ K ∧ ∀ z : X × Y,
        let L := readout (first z.1) (second (first z.1) z)
        L ∈ allowed ∧ target z ∈ L
    (tree target allowed K ↔ flat) ∧ (flat ↔ batches)) := by
  intro n m F X Y tree Q hQ allowed hallowed K
  have htf := PEqualNP.Outside.L_pcx_389_aux.tree_to_flat n m Q allowed K
  have hfb := PEqualNP.Outside.L_pcx_389_aux.flat_to_batches n m Q hQ allowed hallowed K
  have hbt := PEqualNP.Outside.L_pcx_389_aux.batches_to_tree n m Q allowed K
  exact ⟨⟨htf, fun hf => hbt (hfb hf)⟩, ⟨hfb, fun hb => htf (hbt hb)⟩⟩
