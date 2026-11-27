import Mathlib
import PEqualNP.Defs

open scoped BigOperators

namespace PEqualNP.Outside.L_lib_606

def toN (b : Bool) : ℕ := if b then 1 else 0

theorem toN_mod (c : ℕ) : toN ((c % 2 == 1)) = c % 2 := by
  rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [toN, h]

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

structure Fam (ι V : Type*) where
  sw : V → Bool
  idx : V → ι
  neg : V → Bool
  cst : V → Bool

def Fam.apply (F : Fam ι V) (T : Finset ι) : V → Bool := fun v =>
  if F.sw v then (decide (F.idx v ∈ T) ^^ F.neg v) else F.cst v

def Fam.refs (F : Fam ι V) (mon : Finset V) : Finset ι :=
  (mon.filter (fun j => F.sw j = true)).image F.idx

theorem Fam.mem_refs {F : Fam ι V} {mon : Finset V} {j : V} (hj : j ∈ mon) (hsw : F.sw j = true) :
    F.idx j ∈ F.refs mon := by
  unfold Fam.refs
  rw [Finset.mem_image]
  exact ⟨j, Finset.mem_filter.mpr ⟨hj, hsw⟩, rfl⟩

theorem Fam.card_refs_le (F : Fam ι V) (mon : Finset V) : (F.refs mon).card ≤ mon.card := by
  unfold Fam.refs
  exact le_trans (Finset.card_image_le) (Finset.card_filter_le _ _)

theorem Fam.apply_update_on {F : Fam ι V} {T : Finset ι} {k : ι} {mon : Finset V}
    (hk : ∀ j ∈ mon, F.sw j = true → F.idx j ≠ k) :
    ∀ j ∈ mon, F.apply (insert k T) j = F.apply T j := by
  intro j hj
  unfold Fam.apply
  by_cases hsw : F.sw j = true
  · have hik : F.idx j ≠ k := hk j hj hsw
    simp [hsw, hik]
  · simp [hsw]

theorem toN_decide (p : Prop) [Decidable p] : toN (decide p) = if p then 1 else 0 := by
  unfold toN; by_cases h : p <;> simp [h]

noncomputable def allB {α : Type*} (s : Finset α) (p : α → Bool) : Bool := s.toList.all p

theorem allB_eq_true {α : Type*} (s : Finset α) (p : α → Bool) :
    allB s p = true ↔ ∀ x ∈ s, p x = true := by
  simp [allB, List.all_eq_true, Finset.mem_toList]

theorem allB_congr {α : Type*} (s : Finset α) (p q : α → Bool) (h : ∀ x ∈ s, p x = q x) :
    allB s p = allB s q := by
  cases hp : allB s p with
  | true =>
    have hq : allB s q = true := Iff.mpr (allB_eq_true _ _) fun x hx => (h x hx) ▸ Iff.mp (allB_eq_true _ _) hp x hx
    rw [hq]
  | false =>
    have hp' : allB s p ≠ true := by rw [hp]; simp
    have hq : allB s q ≠ true := fun hq =>
      hp' (Iff.mpr (allB_eq_true _ _) fun x hx => (h x hx) ▸ Iff.mp (allB_eq_true _ _) hq x hx)
    cases hq' : allB s q with
    | true => exact absurd hq' hq
    | false => rfl

theorem toN_all {α : Type*} (s : Finset α) (p : α → Bool) :
    toN (allB s p) = if ∀ x ∈ s, p x = true then 1 else 0 := by
  unfold toN
  by_cases h : ∀ x ∈ s, p x = true
  · have hb : allB s p = true := Iff.mpr (allB_eq_true s p) h
    rw [ite_eq_left hb, ite_eq_left h]
  · have hb : allB s p ≠ true := fun hb => h (Iff.mp (allB_eq_true s p) hb)
    rw [ite_eq_right hb, ite_eq_right h]

theorem parity_vanish {b : ℕ}
    (f : (V → Bool) → Bool) (terms : Finset (Finset V)) (hb : ∀ mon ∈ terms, mon.card ≤ b)
    (heval : ∀ input, ∃ inst : DecidablePred (fun mon : Finset V => ∀ j ∈ mon, input j = true),
      f input = (((@Finset.filter (Finset V) (fun mon => ∀ j ∈ mon, input j = true) inst terms).card % 2) == 1))
    (T₀ : Finset ι) (hT₀ : T₀.card = b + 1) (F : Fam ι V) :
    (∑ T ∈ T₀.powerset, toN (f (F.apply T))) % 2 = 0 := by
  classical

  set DI : (input : V → Bool) → DecidablePred (fun mon : Finset V => ∀ j ∈ mon, input j = true) :=
    fun _input => inferInstance with hDI
  set flt : (V → Bool) → Finset (Finset V) :=
    fun input => @Finset.filter (Finset V) (fun mon => ∀ j ∈ mon, input j = true) (DI input) terms with hflt

  have hstep1 : ∀ T ∈ T₀.powerset, toN (f (F.apply T)) % 2 = (flt (F.apply T)).card % 2 := by
    intro T _
    obtain ⟨inst, h⟩ := heval (F.apply T)
    have hf : @Finset.filter (Finset V) (fun mon => ∀ j ∈ mon, F.apply T j = true) inst terms =
        flt (F.apply T) :=
      congrArg (fun i => @Finset.filter (Finset V) (fun mon => ∀ j ∈ mon, F.apply T j = true) i terms)
        (Subsingleton.elim _ _)
    rw [h, toN_mod, Nat.mod_mod, hf]
  have hstep2 : ∀ T ∈ T₀.powerset, (flt (F.apply T)).card =
      ∑ mon ∈ terms, toN (allB mon (fun j => F.apply T j)) := by
    intro T _
    rw [Finset.sum_congr rfl (fun mon _ => toN_all mon _)]
    simp only [Finset.sum_boole, Nat.cast_id]
    exact congrArg Finset.card
      (congrArg (fun i => @Finset.filter (Finset V) (fun mon => ∀ j ∈ mon, F.apply T j = true) i terms)
        (Subsingleton.elim _ _))

  have heven : ∀ mon ∈ terms, (∑ T ∈ T₀.powerset, toN (allB mon (fun j => F.apply T j))) % 2 = 0 := by
    intro mon hmon
    have hle : (F.refs mon).card ≤ b := le_trans (F.card_refs_le mon) (hb mon hmon)
    obtain ⟨k, hk, hkI⟩ : ∃ k ∈ T₀, k ∉ F.refs mon := by
      by_contra h
      push Not at h
      have hsub : T₀ ⊆ F.refs mon := h
      have hcard : T₀.card ≤ (F.refs mon).card := Finset.card_le_card hsub
      rw [hT₀] at hcard; omega
    have hTk : T₀ = insert k (T₀.erase k) := (Finset.insert_erase hk).symm
    have hdisj : Disjoint (T₀.erase k).powerset ((T₀.erase k).powerset.image (insert k)) := by
      rw [Finset.disjoint_left]
      intro t ht ht'
      have ht1 : t ⊆ T₀.erase k := Finset.mem_powerset.mp ht
      have hkE : k ∉ t := fun h => (Finset.mem_erase.mp (ht1 h)).1 rfl
      obtain ⟨t', ht', rfl⟩ := Finset.mem_image.mp ht'
      exact hkE (Finset.mem_insert_self k t')
    have hinj : Set.InjOn (insert k) ((T₀.erase k).powerset : Set (Finset ι)) := by
      intro t ht t' ht' hEq
      apply Finset.ext
      intro x
      have htm : t ∈ (T₀.erase k).powerset := ht
      have htm' : t' ∈ (T₀.erase k).powerset := ht'
      have hkt : k ∉ t := fun h => (Finset.mem_erase.mp ((Finset.mem_powerset.mp htm) h)).1 rfl
      have hkt' : k ∉ t' := fun h => (Finset.mem_erase.mp ((Finset.mem_powerset.mp htm') h)).1 rfl
      by_cases hxk : x = k
      · simp [hxk, hkt, hkt']
      · have h1 : (x ∈ insert k t) ↔ (x ∈ t) := by simp [hxk]
        have h2 : (x ∈ insert k t') ↔ (x ∈ t') := by simp [hxk]
        rw [← h1, hEq, h2]
    have hkref : ∀ j ∈ mon, F.sw j = true → F.idx j ≠ k := by
      intro j hj hsw h
      exact hkI (h ▸ F.mem_refs hj hsw)
    have hsame : ∀ t : Finset ι,
        (allB mon (fun j => F.apply (insert k t) j)) = (allB mon (fun j => F.apply t j)) :=
      fun t => allB_congr mon _ _ fun j hj => F.apply_update_on hkref j hj
    have hpair : (∑ T ∈ T₀.powerset, toN (allB mon (fun j => F.apply T j))) =
        2 * ∑ t ∈ (T₀.erase k).powerset, toN (allB mon (fun j => F.apply t j)) := by
      conv_lhs => rw [hTk]
      rw [Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
        Finset.sum_congr rfl (fun t _ => congrArg toN (hsame t))]
      omega
    rw [hpair, Nat.mul_mod_right]
  have H4 : (∑ mon ∈ terms, ∑ T ∈ T₀.powerset, toN (allB mon (fun j => F.apply T j))) % 2 = 0 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl heven, Finset.sum_const_zero, Nat.zero_mod]
  have e1 : (∑ T ∈ T₀.powerset, toN (f (F.apply T))) % 2 =
      (∑ T ∈ T₀.powerset, (toN (f (F.apply T)) % 2)) % 2 := Finset.sum_nat_mod _ _ _
  rw [e1, Finset.sum_congr rfl hstep1, ← Finset.sum_nat_mod, Finset.sum_congr rfl hstep2,
    Finset.sum_comm]
  exact H4

variable {g m r : ℕ}

theorem label_injective (label : Fin g → Fin m → Fin (m+1) → Fin r → Bool)
    (pick : (Fin g × Fin m × Fin r → Bool) → (Fin g → Fin (m+1)))
    (H : ∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j)) (j : Fin g) (i : Fin m) :
    Function.Injective (label j i) := by
  classical
  intro a a' haa
  by_contra hne
  have hcardD : (((Finset.univ.erase a).erase a' : Finset (Fin (m+1)))).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ a'⟩),
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    omega
  have hcardR : (Finset.univ.erase i : Finset (Fin m)).card = m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  have hc : (Finset.univ.erase i : Finset (Fin m)).card =
      ((Finset.univ.erase a).erase a' : Finset (Fin (m+1))).card := by rw [hcardR, hcardD]
  let e1 := (Finset.univ.erase i : Finset (Fin m)).equivFin
  let e3 := (((Finset.univ.erase a).erase a' : Finset (Fin (m+1)))).equivFin.symm
  let e2 : Fin (Finset.univ.erase i : Finset (Fin m)).card ≃
      Fin ((Finset.univ.erase a).erase a' : Finset (Fin (m+1))).card := finCongr hc
  let e : {x // x ∈ (Finset.univ.erase i : Finset (Fin m))} ≃
      {z // z ∈ ((Finset.univ.erase a).erase a' : Finset (Fin (m+1)))} := e1.trans (e2.trans e3)
  let x : Fin g × Fin m × Fin r → Bool := fun (j', i', v) =>
    if j' = j then
      (if h : i' = i then label j i a v
        else label j i' ↑(e ⟨i', Finset.mem_erase.mpr ⟨h, Finset.mem_univ i'⟩⟩) v)
    else false
  have hex : ∃ i', (fun v => x (j,i',v)) = label j i' (pick x j) := by
    by_cases h1 : pick x j = a
    · refine ⟨i, ?_⟩
      funext v
      have hx : x (j, i, v) = label j i a v := by simp [x]
      rw [hx, h1]
    by_cases h2 : pick x j = a'
    · refine ⟨i, ?_⟩
      funext v
      have hx : x (j, i, v) = label j i a v := by simp [x]
      rw [hx, h2, haa]
    · have hz : pick x j ∈ ((Finset.univ.erase a).erase a' : Finset (Fin (m+1))) := by
        rw [Finset.mem_erase, Finset.mem_erase]
        exact ⟨h2, h1, Finset.mem_univ _⟩
      obtain ⟨p, hp⟩ := e.surjective ⟨pick x j, hz⟩
      obtain ⟨i', hi'⟩ := p
      have hv : ↑(e ⟨i', hi'⟩) = pick x j := congrArg Subtype.val hp
      have hne' : i' ≠ i := (Finset.mem_erase.mp hi').1
      refine ⟨i', ?_⟩
      funext v
      have hx : x (j, i', v) = label j i' ↑(e ⟨i', hi'⟩) v := by simp [x, hne']
      rw [hx, hv]
  obtain ⟨i', hi'⟩ := hex
  exact H x j i' hi'

theorem forced (label : Fin g → Fin m → Fin (m+1) → Fin r → Bool)
    (pick : (Fin g × Fin m × Fin r → Bool) → (Fin g → Fin (m+1)))
    (H : ∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j))
    (j : Fin g) (a₀ : Fin (m+1)) (ρ : Fin m ≃ {z : Fin (m+1) // z ≠ a₀})
    (x : Fin g × Fin m × Fin r → Bool) (hx : ∀ i, (fun v => x (j,i,v)) = label j i (ρ i)) :
    pick x j = a₀ := by
  by_contra h
  obtain ⟨i, hi⟩ := ρ.surjective ⟨pick x j, h⟩
  have hrow : (fun v => x (j,i,v)) = label j i (pick x j) := by
    rw [hx i, hi]
  exact H x j i hrow

theorem lower_bound_core (label : Fin g → Fin m → Fin (m+1) → Fin r → Bool)
    (pick : (Fin g × Fin m × Fin r → Bool) → (Fin g → Fin (m+1)))
    (H : ∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j))
    (test : (Fin g → Fin (m+1)) → Bool) (base : Fin g → Fin (m+1)) (coord : Fin g)
    (L S : Finset (Fin (m+1))) (vL : Bool)
    (hL : ∀ z ∈ L, test (Function.update base coord z) = vL)
    (hS : ∀ z ∈ S, test (Function.update base coord z) = !vL)
    (hdisj : ∀ z ∈ S, z ∉ L) (hSne : S.Nonempty)
    (b : ℕ) (hb : b + 1 ≤ L.card)
    (terms : Finset (Finset (Fin g × Fin m × Fin r)))
    (hsize : ∀ mon ∈ terms, mon.card ≤ b)
    (heval : ∀ input, test (pick input) =
      (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)) : False := by
  classical
  obtain ⟨ℓ₀, hℓ₀⟩ := hSne
  have hcard : ∀ j : Fin g,
      Fintype.card {z : Fin (m+1) // z ≠ Function.update base coord ℓ₀ j} = m := by
    intro j
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin]
    omega
  set rho : ∀ j : Fin g, Fin m ≃ {z : Fin (m+1) // z ≠ Function.update base coord ℓ₀ j} :=
    fun j => (Fintype.equivFinOfCardEq (hcard j)).symm with hrho

  set switch : Finset (Fin m) := Finset.univ.filter (fun i => (rho coord i : Fin (m+1)) ∈ L) with hswitch
  have hinjr : Function.Injective (fun i : Fin m => (rho coord i : Fin (m+1))) :=
    fun i i' h => (rho coord).injective (Subtype.ext h)
  have himage : (switch.image (fun i : Fin m => (rho coord i : Fin (m+1)))) = L := by
    rw [hswitch]
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨i, hi, hfi⟩ := Finset.mem_image.mp hz
      rw [← hfi]
      exact (Finset.mem_filter.mp hi).2
    · intro hz
      have hne : z ≠ ℓ₀ := fun h => hdisj ℓ₀ hℓ₀ (h ▸ hz)
      have hne' : z ≠ Function.update base coord ℓ₀ coord := by
        rw [Function.update_self]; exact hne
      obtain ⟨i, hp⟩ := (rho coord).surjective ⟨z, hne'⟩
      have hv : ↑(rho coord i) = z := congrArg Subtype.val hp
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, by rw [hv]; exact hz⟩, hv⟩
  have hswcard : switch.card = L.card := by
    rw [← himage, Finset.card_image_of_injective _ hinjr]
  have hle : b + 1 ≤ switch.card := by rw [hswcard]; exact hb
  obtain ⟨T₀, hT₀sub, hT₀card⟩ : ∃ T₀ : Finset (Fin m), T₀ ⊆ switch ∧ T₀.card = b + 1 := by
    let e := switch.equivFin.symm
    let c : Fin (b+1) → Fin switch.card := Fin.castLE hle
    refine ⟨Finset.univ.image (fun k => (e (c k) : Fin m)), ?_, ?_⟩
    · rw [Finset.image_subset_iff]
      intro k _
      exact (e (c k)).property
    · rw [Finset.card_image_of_injective _
        (fun k k' h => Fin.castLE_injective hle (e.injective (Subtype.val_injective h))),
        Finset.card_univ, Fintype.card_fin]

  set F : Fam (Fin m) (Fin g × Fin m × Fin r) :=
    { sw := fun (j', i, v) => decide (j' = coord ∧ (rho coord i : Fin (m+1)) ∈ L ∧
        label coord i ℓ₀ v ≠ label coord i (rho coord i) v)
      idx := fun (_j', i, _v) => i
      neg := fun (_j', i, v) => label coord i (rho coord i) v
      cst := fun (j', i, v) => label j' i (rho j' i) v } with hF
  have hother : ∀ (T : Finset (Fin m)) (j' : Fin g), j' ≠ coord → ∀ (i : Fin m) (v : Fin r),
      F.apply T (j', i, v) = label j' i (rho j' i) v := by
    intro T j' hj i v
    simp [Fam.apply, hF, hj]
  have hcoord : ∀ (T : Finset (Fin m)) (i : Fin m) (v : Fin r),
      F.apply T (coord, i, v) =
      (if ((rho coord i : Fin (m+1)) ∈ L ∧ i ∈ T) then label coord i ℓ₀ v
        else label coord i (rho coord i) v) := by
    intro T i v
    have hunf : F.apply T (coord, i, v) =
        (if decide (True ∧ (rho coord i : Fin (m+1)) ∈ L ∧
            label coord i ℓ₀ v ≠ label coord i (rho coord i) v) = true
          then decide (i ∈ T) ^^ label coord i (rho coord i) v
          else label coord i (rho coord i) v) := by simp only [Fam.apply, hF]
    rw [hunf]
    by_cases hLi : (rho coord i : Fin (m+1)) ∈ L
    · by_cases hT : i ∈ T
      · conv_rhs => rw [ite_eq_left ⟨hLi, hT⟩]
        by_cases hc : label coord i ℓ₀ v = label coord i (rho coord i) v
        · have hnsw : decide (True ∧ (rho coord i : Fin (m+1)) ∈ L ∧
              label coord i ℓ₀ v ≠ label coord i (rho coord i) v) = false := by simp [hc, hLi]
          rw [hnsw]
          simp [hc]
        · have hsw : decide (True ∧ (rho coord i : Fin (m+1)) ∈ L ∧
              label coord i ℓ₀ v ≠ label coord i (rho coord i) v) = true := by simp [hc, hLi]
          have hne : label coord i ℓ₀ v = !label coord i (rho coord i) v := by
            cases h1 : label coord i ℓ₀ v <;> cases h2 : label coord i (rho coord i) v <;>
              simp_all
          rw [hsw]
          simp [hT, hne]
      · conv_rhs => rw [ite_eq_right (fun h => hT h.2)]
        by_cases hc : label coord i ℓ₀ v = label coord i (rho coord i) v
        · have hnsw : decide (True ∧ (rho coord i : Fin (m+1)) ∈ L ∧
              label coord i ℓ₀ v ≠ label coord i (rho coord i) v) = false := by simp [hc, hLi]
          rw [hnsw]
          simp [hc]
        · have hsw : decide (True ∧ (rho coord i : Fin (m+1)) ∈ L ∧
              label coord i ℓ₀ v ≠ label coord i (rho coord i) v) = true := by simp [hc, hLi]
          rw [hsw]
          simp [hT]
    · conv_rhs => rw [ite_eq_right (fun h => hLi h.1)]
      have hnsw : decide (True ∧ (rho coord i : Fin (m+1)) ∈ L ∧
          label coord i ℓ₀ v ≠ label coord i (rho coord i) v) = false := by simp [hLi]
      rw [hnsw]
      simp

  have hpick : ∀ T : Finset (Fin m), T ⊆ switch → (T ≠ ∅ → pick (F.apply T) coord ∈ L) ∧
      (T = ∅ → pick (F.apply T) coord = ℓ₀) := by
    intro T hTsub
    have hunused : ∀ i : Fin m, (fun v => F.apply T (coord, i, v)) ≠
        label coord i (pick (F.apply T) coord) := fun i => H (F.apply T) coord i
    have hex : pick (F.apply T) coord ≠ ℓ₀ →
        ∃ i ∈ T, (rho coord i : Fin (m+1)) ∈ L ∧ pick (F.apply T) coord = (rho coord i : Fin (m+1)) := by
      intro hne
      have hne' : pick (F.apply T) coord ≠ Function.update base coord ℓ₀ coord := by
        rw [Function.update_self]; exact hne
      obtain ⟨i, hp⟩ := (rho coord).surjective ⟨pick (F.apply T) coord, hne'⟩
      have hv : ↑(rho coord i) = pick (F.apply T) coord := congrArg Subtype.val hp
      have hiT : i ∈ T := by
        by_contra hiT
        apply hunused i
        have hrow : ∀ v, F.apply T (coord, i, v) = label coord i (rho coord i) v := by
          intro v; rw [hcoord, ite_eq_right (fun h => hiT h.2)]
        funext v
        rw [hrow v, hv]
      exact ⟨i, hiT, (Finset.mem_filter.mp (hTsub hiT)).2, hv.symm⟩
    constructor
    · intro hTne
      by_contra hnotL
      have hne : pick (F.apply T) coord ≠ ℓ₀ := by
        intro h
        obtain ⟨i, hiT⟩ := Finset.nonempty_iff_ne_empty.mpr hTne
        have hiL := (Finset.mem_filter.mp (hTsub hiT)).2
        apply hunused i
        have hrow : ∀ v, F.apply T (coord, i, v) = label coord i ℓ₀ v := by
          intro v; rw [hcoord, ite_eq_left ⟨hiL, hiT⟩]
        funext v
        rw [hrow v, h]
      obtain ⟨i, hiT, hiL, hv⟩ := hex hne
      rw [← hv] at hiL
      exact hnotL hiL
    · intro hT0
      by_contra hne
      obtain ⟨i, hiT, -⟩ := hex hne
      exact absurd (hT0 ▸ hiT) (Finset.notMem_empty i)

  have hfun : ∀ T ∈ T₀.powerset,
      toN (test (pick (F.apply T))) = (if T = ∅ then toN (!vL) else toN vL) := by
    intro T hT
    have hTsub : T ⊆ switch := (Finset.mem_powerset.mp hT).trans hT₀sub
    have hothers : pick (F.apply T) = Function.update base coord (pick (F.apply T) coord) := by
      funext j'
      by_cases hj : j' = coord
      · subst hj; rw [Function.update_self]
      · rw [Function.update_of_ne hj]
        have hforced := forced label pick H j' (Function.update base coord ℓ₀ j') (rho j')
          (F.apply T) (fun i => funext (hother T j' hj i))
        rw [hforced]
        exact Function.update_of_ne hj _ _
    rw [hothers]
    by_cases hT0 : T = ∅
    · have hp := (hpick T hTsub).2 hT0
      rw [ite_eq_left hT0, hp, hS ℓ₀ hℓ₀]
    · have hp := (hpick T hTsub).1 hT0
      rw [ite_eq_right hT0, hL _ hp]

  have hvan : (∑ T ∈ T₀.powerset, toN ((fun word => test (pick word)) (F.apply T))) % 2 = 0 := by
    refine parity_vanish (fun word => test (pick word)) terms hsize ?_ T₀ hT₀card F
    intro input
    exact ⟨_, heval input⟩
  rw [Finset.sum_congr rfl (fun T hT => by rw [hfun T hT])] at hvan
  have hsum : (∑ T ∈ T₀.powerset, if T = ∅ then toN (!vL) else toN vL) =
      toN (!vL) + 2 * (toN vL * (2 ^ b - 1)) + toN vL := by
    have hmem : (∅ : Finset (Fin m)) ∈ T₀.powerset := Finset.mem_powerset.mpr (Finset.empty_subset _)
    rw [← Finset.insert_erase hmem, Finset.sum_insert (Finset.notMem_erase _ _), ite_eq_left rfl,
        Finset.sum_congr rfl (fun T hT => ite_eq_right (Finset.ne_of_mem_erase hT)), Finset.sum_const,
        Nat.nsmul_eq_mul, Finset.card_erase_of_mem hmem, Finset.card_powerset, hT₀card]
    have hpos : 1 ≤ 2 ^ b := Nat.one_le_two_pow
    have e1 : 2 ^ (b + 1) - 1 = 2 * (2 ^ b - 1) + 1 := by
      rw [Nat.pow_succ]; omega
    rw [e1]
    have e2 : (2 * (2 ^ b - 1) + 1) * toN vL = 2 * (toN vL * (2 ^ b - 1)) + toN vL := by ring
    rw [e2, Nat.add_assoc]
  rw [hsum] at hvan
  have hA := Nat.add_mod (toN (!vL) + 2 * (toN vL * (2 ^ b - 1))) (toN vL) 2
  have hB := Nat.add_mod (toN (!vL)) (2 * (toN vL * (2 ^ b - 1))) 2
  have hC : 2 * (toN vL * (2 ^ b - 1)) % 2 = 0 := Nat.mul_mod_right _ _
  rw [hA, hB, hC, Nat.add_zero, Nat.mod_mod] at hvan
  cases vL <;> simp [toN] at hvan

end PEqualNP.Outside.L_lib_606

theorem PEqualNP.Outside.L_lib_606 : ∀ (g m r : Nat),
  let A := Fin (m+1)
  let V := Fin g × Fin m × Fin r
  let W := V → Bool
  let deg := fun (b : Nat) (f : W → Bool) =>
    ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card ≤ b) ∧
      ∀ input, f input = (((terms.filter (fun mon => ∀ j ∈ mon, input j = true)).card % 2) == 1)
  let Y := Fin g → A
  ∀ (label : Fin g → Fin m → A → Fin r → Bool) (pick : W → Y),
    (∀ x j i, (fun v => x (j,i,v)) ≠ label j i (pick x j)) →
    ∀ (test : Y → Bool) (base : Y) (coord : Fin g),
      let ones := ((Finset.univ : Finset A).filter (fun z =>
        test (Function.update base coord z) = true)).card
      0 < ones → ones < m+1 →
      ∀ b : Nat, deg b (fun word => test (pick word)) → max ones (m+1-ones) ≤ b := by
  intro g m r A V W deg Y label pick H test base coord ones hones0 hones1 b hb
  classical
  obtain ⟨terms, hsize, heval⟩ :=
    (show ∃ terms : Finset (Finset (Fin g × Fin m × Fin r)), _ from hb)
  by_contra hcon
  have hlt : b + 1 ≤ max ones (m + 1 - ones) := by omega
  set Ttrue : Finset (Fin (m+1)) :=
    Finset.univ.filter (fun z => test (Function.update base coord z) = true) with hTtrue_def
  have hTtrue : Ttrue.card = ones := rfl
  have hFfalse : (Finset.univ \ Ttrue : Finset (Fin (m+1))).card = m + 1 - ones := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hTtrue]
  have hmemT : ∀ z, z ∈ Ttrue ↔ test (Function.update base coord z) = true :=
    fun z => Finset.mem_filter.trans (by simp)
  have hcompl : ∀ z, z ∈ (Finset.univ \ Ttrue : Finset (Fin (m+1))) →
      test (Function.update base coord z) = false := by
    intro z hz
    have h1 : ¬ test (Function.update base coord z) = true :=
      fun h => (Finset.mem_sdiff.mp hz).2 ((hmemT z).mpr h)
    rw [Bool.not_eq_true] at h1
    exact h1
  by_cases hL : m + 1 - ones ≤ ones
  · have hcard : Ttrue.card = max ones (m + 1 - ones) := hTtrue.trans (Nat.max_eq_left hL).symm
    have hSne : (Finset.univ \ Ttrue : Finset (Fin (m+1))).Nonempty :=
      Finset.card_pos.mp (by rw [hFfalse]; omega)
    exact PEqualNP.Outside.L_lib_606.lower_bound_core label pick H test base coord Ttrue (Finset.univ \ Ttrue) true
      (fun z hz => (hmemT z).mp hz) (fun z hz => by rw [hcompl z hz]; rfl)
      (fun z hz => (Finset.mem_sdiff.mp hz).2) hSne b (by rw [hcard]; exact hlt) terms hsize heval
  · have hcard : (Finset.univ \ Ttrue : Finset (Fin (m+1))).card = max ones (m + 1 - ones) := by
      rw [hFfalse, Nat.max_eq_right (by omega)]
    have hSne : Ttrue.Nonempty := Finset.card_pos.mp (by rw [hTtrue]; omega)
    exact PEqualNP.Outside.L_lib_606.lower_bound_core label pick H test base coord (Finset.univ \ Ttrue) Ttrue false
      (fun z hz => hcompl z hz) (fun z hz => by rw [(hmemT z).mp hz]; rfl)
      (fun z hz => fun h => (Finset.mem_sdiff.mp h).2 hz) hSne b (by rw [hcard]; exact hlt)
      terms hsize heval
