import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1201_aux

open scoped Classical

section RingExpansion

variable {L A S : Type*} [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

inductive Pair (L A : Type*) where
  | spare (u : L)
  | outEnd (a : A)
  | inEnd (a : A)
  deriving DecidableEq

def pairEquivSum (L A : Type*) : Pair L A ≃ L ⊕ A ⊕ A where
  toFun
    | .spare u => Sum.inl u
    | .outEnd a => Sum.inr (Sum.inl a)
    | .inEnd a => Sum.inr (Sum.inr a)
  invFun
    | Sum.inl u => .spare u
    | Sum.inr (Sum.inl a) => .outEnd a
    | Sum.inr (Sum.inr a) => .inEnd a
  left_inv p := by cases p <;> rfl
  right_inv s := by rcases s with u | (a | a) <;> rfl

instance instFintypePair : Fintype (Pair L A) :=
  Fintype.ofEquiv (L ⊕ A ⊕ A) (pairEquivSum L A).symm

lemma card_pair : Fintype.card (Pair L A) = Fintype.card L + 2 * Fintype.card A := by
  rw [Fintype.card_congr (pairEquivSum L A), Fintype.card_sum, Fintype.card_sum]
  ring

def owner (src dst : A → L) : Pair L A → L
  | .spare u => u
  | .outEnd a => src a
  | .inEnd a => dst a

noncomputable def ringList (src dst : A → L) (u : L) : List (Pair L A) :=
  [.spare u] ++
  ((Finset.univ.filter (fun a : A => src a = u)).toList).map Pair.outEnd ++
  ((Finset.univ.filter (fun a : A => dst a = u)).toList).map Pair.inEnd

lemma mem_ringList_iff (src dst : A → L) (u : L) (p : Pair L A) :
    p ∈ ringList src dst u ↔ owner src dst p = u := by
  cases p with
  | spare v => simp [ringList, owner, eq_comm]
  | outEnd a => simp [ringList, owner]
  | inEnd a => simp [ringList, owner]

lemma ringList_nodup (src dst : A → L) (u : L) : (ringList src dst u).Nodup := by
  have h1 : (((Finset.univ.filter (fun a : A => src a = u)).toList).map (@Pair.outEnd L A)).Nodup :=
    (Finset.nodup_toList _).map (fun _ _ h => by cases h; rfl)
  have h2 : (((Finset.univ.filter (fun a : A => dst a = u)).toList).map (@Pair.inEnd L A)).Nodup :=
    (Finset.nodup_toList _).map (fun _ _ h => by cases h; rfl)
  dsimp only [ringList]
  rw [List.nodup_append, List.nodup_append]
  refine ⟨⟨by simp, h1, ?_⟩, h2, ?_⟩
  · intro x hx y hy
    simp only [List.mem_singleton] at hx; subst hx
    rcases List.mem_map.mp hy with ⟨a, _, rfl⟩
    intro h; cases h
  · intro x hx y hy
    rcases List.mem_map.mp hy with ⟨a, _, rfl⟩
    rcases List.mem_append.mp hx with hx1 | hx2
    · simp only [List.mem_singleton] at hx1; subst hx1; intro h; cases h
    · rcases List.mem_map.mp hx2 with ⟨b, _, rfl⟩; intro h; cases h

def listNext {α : Type*} [DecidableEq α] (K : List α) (p : α) : Option α :=
  if h2 : 2 ≤ K.length then
    if hmem : p ∈ K then
      some (K[(K.idxOf p + 1) % K.length]'(Nat.mod_lt _ (by omega)))
    else none
  else none

def listPrev {α : Type*} [DecidableEq α] (K : List α) (p : α) : Option α :=
  if h2 : 2 ≤ K.length then
    if hmem : p ∈ K then
      some (K[(K.idxOf p + K.length - 1) % K.length]'(Nat.mod_lt _ (by omega)))
    else none
  else none

lemma listNext_iff_listPrev {α : Type*} [DecidableEq α] (K : List α) (hnd : K.Nodup) (p q : α) :
    listNext K p = some q ↔ listPrev K q = some p := by
  dsimp only [listNext, listPrev]
  by_cases h2 : 2 ≤ K.length
  · rw [dif_pos h2, dif_pos h2]
    constructor
    · intro h
      by_cases hp : p ∈ K
      · rw [dif_pos hp] at h
        have hq_eq : K[(K.idxOf p + 1) % K.length]'(Nat.mod_lt _ (by omega)) = q :=
          Option.some.inj h
        have hq : q ∈ K := hq_eq ▸ List.getElem_mem _
        rw [dif_pos hq]
        congr 1
        have hp_idx : K.idxOf p < K.length := List.idxOf_lt_length_of_mem hp
        have hq_idx : K.idxOf q = (K.idxOf p + 1) % K.length := by
          rw [← hq_eq]; exact List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ (by omega))
        have hmod : ((K.idxOf p + 1) % K.length + K.length - 1) % K.length = K.idxOf p := by
          by_cases hlast : K.idxOf p + 1 = K.length
          · have hlt : K.length - 1 < K.length := by omega
            rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt hlt]; omega
          · have hlt : K.idxOf p + 1 < K.length := by omega
            rw [Nat.mod_eq_of_lt hlt,
              show K.idxOf p + 1 + K.length - 1 = K.idxOf p + K.length by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hp_idx]
        have hget : K[(K.idxOf q + K.length - 1) % K.length]'(Nat.mod_lt _ (by omega)) =
            K[K.idxOf p]'hp_idx := by simp only [hq_idx, hmod]
        rw [hget]; exact List.getElem_idxOf hp_idx
      · rw [dif_neg hp] at h; cases h
    · intro h
      by_cases hq : q ∈ K
      · rw [dif_pos hq] at h
        have hp_eq : K[(K.idxOf q + K.length - 1) % K.length]'(Nat.mod_lt _ (by omega)) = p :=
          Option.some.inj h
        have hp : p ∈ K := hp_eq ▸ List.getElem_mem _
        rw [dif_pos hp]
        congr 1
        have hq_idx : K.idxOf q < K.length := List.idxOf_lt_length_of_mem hq
        have hp_idx : K.idxOf p = (K.idxOf q + K.length - 1) % K.length := by
          rw [← hp_eq]; exact List.Nodup.idxOf_getElem hnd _ (Nat.mod_lt _ (by omega))
        have hmod : ((K.idxOf q + K.length - 1) % K.length + 1) % K.length = K.idxOf q := by
          by_cases hzero : K.idxOf q = 0
          · have hlt : K.length - 1 < K.length := by omega
            rw [hzero, zero_add, Nat.mod_eq_of_lt hlt,
              show K.length - 1 + 1 = K.length by omega, Nat.mod_self]
          · have hlt : K.idxOf q - 1 < K.length := by omega
            rw [show K.idxOf q + K.length - 1 = (K.idxOf q - 1) + K.length by omega,
              Nat.add_mod_right, Nat.mod_eq_of_lt hlt,
              show K.idxOf q - 1 + 1 = K.idxOf q by omega, Nat.mod_eq_of_lt hq_idx]
        have hget : K[(K.idxOf p + 1) % K.length]'(Nat.mod_lt _ (by omega)) =
            K[K.idxOf q]'hq_idx := by simp only [hp_idx, hmod]
        rw [hget]; exact List.getElem_idxOf hq_idx
      · rw [dif_neg hq] at h; cases h
  · rw [dif_neg h2, dif_neg h2]; simp

noncomputable def ringNext (src dst : A → L) (p : Pair L A) : Option (Pair L A) :=
  listNext (ringList src dst (owner src dst p)) p

noncomputable def ringPrev (src dst : A → L) (p : Pair L A) : Option (Pair L A) :=
  listPrev (ringList src dst (owner src dst p)) p

lemma ringNext_owner (src dst : A → L) (p q : Pair L A) (h : ringNext src dst p = some q) :
    owner src dst q = owner src dst p := by
  dsimp only [ringNext, listNext] at h
  split_ifs at h with h2 hmem
  have hq_eq := Option.some.inj h
  have hq_mem : q ∈ ringList src dst (owner src dst p) := hq_eq ▸ List.getElem_mem _
  exact (mem_ringList_iff src dst _ q).mp hq_mem

lemma ringPrev_owner (src dst : A → L) (p q : Pair L A) (h : ringPrev src dst p = some q) :
    owner src dst q = owner src dst p := by
  dsimp only [ringPrev, listPrev] at h
  split_ifs at h with h2 hmem
  have hq_eq := Option.some.inj h
  have hq_mem : q ∈ ringList src dst (owner src dst p) := hq_eq ▸ List.getElem_mem _
  exact (mem_ringList_iff src dst _ q).mp hq_mem

lemma ringNext_iff_ringPrev (src dst : A → L) (p q : Pair L A) :
    ringNext src dst p = some q ↔ ringPrev src dst q = some p := by
  constructor
  · intro h
    have hown := ringNext_owner src dst p q h
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hown]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst _) p q).mp h
  · intro h
    have hown := ringPrev_owner src dst q p h
    dsimp only [ringNext, ringPrev] at h ⊢
    rw [hown]
    exact (listNext_iff_listPrev _ (ringList_nodup src dst _) p q).mpr h

noncomputable def ringNb (src dst : A → L) : Pair L A × Bool → Option (Pair L A × Bool)
  | (p, true) => (ringNext src dst p).map (fun q => (q, false))
  | (p, false) => (ringPrev src dst p).map (fun q => (q, true))

lemma ringNb_symm (src dst : A → L) (x y : Pair L A × Bool) :
    ringNb src dst x = some y ↔ ringNb src dst y = some x := by
  rcases x with ⟨p, c1⟩; rcases y with ⟨q, c2⟩
  cases c1 <;> cases c2 <;> simp [ringNb, ringNext_iff_ringPrev]

lemma ringNb_bip (src dst : A → L) (x y : Pair L A × Bool) (h : ringNb src dst x = some y) :
    x.2 ≠ y.2 := by
  rcases x with ⟨p, c1⟩; rcases y with ⟨q, c2⟩
  cases c1 <;> cases c2 <;> simp [ringNb] at h ⊢

def arcNb : Pair L A × Bool → Option (Pair L A × Bool)
  | (.outEnd a, true) => some (.inEnd a, false)
  | (.inEnd a, false) => some (.outEnd a, true)
  | _ => none

lemma arcNb_symm (x y : Pair L A × Bool) :
    @arcNb L A x = some y ↔ @arcNb L A y = some x := by
  rcases x with ⟨p, c1⟩; rcases y with ⟨q, c2⟩
  cases p <;> cases q <;> cases c1 <;> cases c2 <;> simp [arcNb, eq_comm]

lemma arcNb_bip (x y : Pair L A × Bool) (h : @arcNb L A x = some y) :
    x.2 ≠ y.2 := by
  rcases x with ⟨p, c1⟩; rcases y with ⟨q, c2⟩
  cases p <;> cases c1 <;> cases c2 <;> simp [arcNb] at h ⊢

noncomputable def nbPair (src dst : A → L) (x : Pair L A × Bool) : Finset (Pair L A × Bool) :=
  {(x.1, !x.2)} ∪ (ringNb src dst x).toFinset ∪ (arcNb x).toFinset

lemma nbPair_bip (src dst : A → L) (x y : Pair L A × Bool) (h : y ∈ nbPair src dst x) :
    x.2 ≠ y.2 := by
  simp only [nbPair, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset,
    Option.mem_def] at h
  rcases h with (h1 | h2) | h3
  · rcases x with ⟨p, c1⟩; rcases y with ⟨q, c2⟩
    have hc : c2 = !c1 := congrArg Prod.snd h1
    cases c1 <;> cases c2 <;> simp at hc ⊢
  · exact ringNb_bip src dst x y h2
  · exact arcNb_bip x y h3

lemma nbPair_irrefl (src dst : A → L) (x : Pair L A × Bool) : x ∉ nbPair src dst x :=
  fun h => nbPair_bip src dst x x h rfl

lemma nbPair_card_le (src dst : A → L) (x : Pair L A × Bool) : (nbPair src dst x).card ≤ 3 := by
  have h1 : ({(x.1, !x.2)} : Finset (Pair L A × Bool)).card = 1 := Finset.card_singleton _
  have h2 : (ringNb src dst x).toFinset.card ≤ 1 := by cases ringNb src dst x <;> simp
  have h3 : (@arcNb L A x).toFinset.card ≤ 1 := by cases @arcNb L A x <;> simp
  have hu2 := Finset.card_union_le ({(x.1, !x.2)} ∪ (ringNb src dst x).toFinset) (@arcNb L A x).toFinset
  have hu1 := Finset.card_union_le ({(x.1, !x.2)} : Finset (Pair L A × Bool)) (ringNb src dst x).toFinset
  dsimp only [nbPair]
  omega

lemma nbPair_symm (src dst : A → L) (x y : Pair L A × Bool) :
    y ∈ nbPair src dst x ↔ x ∈ nbPair src dst y := by
  simp only [nbPair, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset, Option.mem_def]
  have h1 : y = (x.1, !x.2) ↔ x = (y.1, !y.2) := by
    rcases x with ⟨p, c1⟩; rcases y with ⟨q, c2⟩
    cases c1 <;> cases c2 <;> simp [eq_comm]
  rw [h1, ringNb_symm, arcNb_symm]

lemma ring_expansion_card (src dst : A → L) (act : L → Bool) :
    ((Finset.univ : Finset ((Pair L A × Bool) → Bool)).filter (fun x =>
      (∀ p, ∀ q ∈ nbPair src dst p, x p = true ∨ x q = true) ∧
      ∀ p, xor (x (p, false)) (x (p, true)) = act (owner src dst p))).card =
    ((Finset.univ : Finset (L → Bool)).filter (fun v =>
      (∀ u, act u = false → v u = false) ∧
      ∀ a : A, act (src a) = true → act (dst a) = true →
        v (src a) = true → v (dst a) = true)).card := by
  let enc : (L → Bool) → ((Pair L A × Bool) → Bool) := fun v pc =>
    if act (owner src dst pc.1) = true then
      if pc.2 then !(v (owner src dst pc.1)) else v (owner src dst pc.1)
    else true
  let dec : ((Pair L A × Bool) → Bool) → (L → Bool) := fun x u =>
    if act u = true then x (.spare u, false) else false
  -- Helper: any valid physical assignment x equals enc (dec x) and dec x is valid
  have hphys_char : ∀ x : (Pair L A × Bool) → Bool,
      (∀ p, ∀ q ∈ nbPair src dst p, x p = true ∨ x q = true) →
      (∀ p, xor (x (p, false)) (x (p, true)) = act (owner src dst p)) →
      ((∀ u, act u = false → dec x u = false) ∧
        ∀ a : A, act (src a) = true → act (dst a) = true →
          dec x (src a) = true → dec x (dst a) = true) ∧
      x = enc (dec x) := by
    intro x hcov hxor
    have hpair_inactive : ∀ p : Pair L A, act (owner src dst p) = false →
        x (p, false) = true ∧ x (p, true) = true := by
      intro p hp
      have hx := hxor p; rw [hp] at hx
      have hc : x (p, false) = true ∨ x (p, true) = true :=
        hcov (p, false) (p, true) (by simp [nbPair])
      cases hf : x (p, false) <;> cases ht : x (p, true) <;> simp [hf, ht] at hx hc ⊢
    have hpair_active : ∀ p : Pair L A, act (owner src dst p) = true →
        x (p, true) = !(x (p, false)) := by
      intro p hp
      have hx := hxor p; rw [hp] at hx
      cases hf : x (p, false) <;> cases ht : x (p, true) <;> simp [hf, ht] at hx ⊢
    have hring_step : ∀ (u : L) (p q : Pair L A),
        act u = true → owner src dst p = u → ringNext src dst p = some q →
        x (p, false) = true → x (q, false) = true := by
      intro u p q hu hown hnext hpf
      have hpt : x (p, true) = false := by
        rw [hpair_active p (by rw [hown, hu]), hpf]; rfl
      have hmem : (q, false) ∈ nbPair src dst (p, true) := by simp [nbPair, ringNb, hnext]
      rcases hcov (p, true) (q, false) hmem with h1 | h2
      · rw [hpt] at h1; cases h1
      · exact h2
    have hring_imp : ∀ (u : L) (p q : Pair L A),
        act u = true → owner src dst p = u → owner src dst q = u →
        x (p, false) = true → x (q, false) = true := by
      intro u p q hu hwp hwq hpf
      let K := ringList src dst u
      have hpK : p ∈ K := (mem_ringList_iff src dst u p).mpr hwp
      have hqK : q ∈ K := (mem_ringList_iff src dst u q).mpr hwq
      by_cases h2 : 2 ≤ K.length
      · have hwalk : ∀ (d i : Nat) (hi : i < K.length),
            x (K[i]'hi, false) = true →
            x (K[(i + d) % K.length]'(Nat.mod_lt _ (by omega)), false) = true := by
          intro d
          induction d with
          | zero => intro i hi hxi; simpa [Nat.mod_eq_of_lt hi] using hxi
          | succ d ih =>
            intro i hi hxi
            let j := (i + d) % K.length
            have hj : j < K.length := Nat.mod_lt _ (by omega)
            have hxj := ih i hi hxi
            have hown_j : owner src dst (K[j]'hj) = u :=
              (mem_ringList_iff src dst u _).mp (List.getElem_mem hj)
            have hidx_j : K.idxOf (K[j]'hj) = j :=
              List.Nodup.idxOf_getElem (ringList_nodup src dst u) j hj
            have hnext_j : ringNext src dst (K[j]'hj) =
                some (K[(j + 1) % K.length]'(Nat.mod_lt _ (by omega))) := by
              dsimp only [ringNext]; rw [hown_j]
              change listNext K (K[j]'hj) = _
              dsimp only [listNext]; rw [dif_pos h2, dif_pos (List.getElem_mem hj)]
              simp only [hidx_j]
            have hres := hring_step u _ _ hu hown_j hnext_j hxj
            have hmod : (j + 1) % K.length = (i + (d + 1)) % K.length := by
              dsimp only [j]; rw [Nat.mod_add_mod, add_assoc]
            simpa only [hmod] using hres
        have hp_idx : K.idxOf p < K.length := List.idxOf_lt_length_of_mem hpK
        have hq_idx : K.idxOf q < K.length := List.idxOf_lt_length_of_mem hqK
        let d := (K.idxOf q + K.length - K.idxOf p) % K.length
        have hstart : x (K[K.idxOf p]'hp_idx, false) = true := by
          simpa [List.getElem_idxOf hp_idx] using hpf
        have hres := hwalk d (K.idxOf p) hp_idx hstart
        have hmod_end : (K.idxOf p + d) % K.length = K.idxOf q := by
          dsimp only [d]; rw [Nat.add_mod_mod]
          rw [show K.idxOf p + (K.idxOf q + K.length - K.idxOf p) = K.idxOf q + K.length by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt hq_idx]
        have hres' : x (K[K.idxOf q]'hq_idx, false) = true := by simpa only [hmod_end] using hres
        simpa [List.getElem_idxOf hq_idx] using hres'
      · have hlen1 : K.length = 1 := by
          have hpos : 0 < K.length := List.length_pos_of_mem hpK; omega
        cases hK : K with
        | nil => simp [hK] at hlen1
        | cons p0 tl =>
          cases tl with
          | nil =>
            rw [hK] at hpK hqK; simp at hpK hqK; subst hpK; subst hqK; exact hpf
          | cons p1 tl2 => simp [hK] at hlen1
    have hring_eq : ∀ (p : Pair L A), act (owner src dst p) = true →
        x (p, false) = x (.spare (owner src dst p), false) := by
      intro p hp
      apply Bool.eq_iff_iff.mpr
      exact ⟨hring_imp (owner src dst p) p (.spare (owner src dst p)) hp rfl rfl,
        hring_imp (owner src dst p) (.spare (owner src dst p)) p hp rfl rfl⟩
    constructor
    · refine ⟨fun u hu => by simp [dec, hu], ?_⟩
      intro a hsrc hdst hv
      simp only [dec, hsrc, hdst, ↓reduceIte] at hv ⊢
      have hout_f : x (.outEnd a, false) = true := by
        rw [hring_eq (.outEnd a) hsrc]; exact hv
      have hout_t : x (.outEnd a, true) = false := by
        rw [hpair_active (.outEnd a) hsrc, hout_f]; rfl
      have hmem : (Pair.inEnd a, false) ∈ nbPair src dst (.outEnd a, true) := by
        simp [nbPair, arcNb]
      rcases hcov (.outEnd a, true) (.inEnd a, false) hmem with h1 | h2
      · rw [hout_t] at h1; cases h1
      · rw [hring_eq (.inEnd a) hdst] at h2; exact h2
    · funext ⟨p, c⟩
      dsimp only [enc, dec]
      by_cases ha : act (owner src dst p) = true
      · simp only [ha, ↓reduceIte]
        cases c
        · exact hring_eq p ha
        · rw [hpair_active p ha, hring_eq p ha]; rfl
      · have haf : act (owner src dst p) = false := Bool.eq_false_iff.mpr ha
        simp only [ha, ↓reduceIte]
        cases c
        · exact (hpair_inactive p haf).1
        · exact (hpair_inactive p haf).2
  refine Finset.card_bij (fun x _ => dec x) ?_ ?_ ?_
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact (hphys_char x hx.1 hx.2).1
  · intro x1 hx1 x2 hx2 hEq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx1 hx2
    rw [(hphys_char x1 hx1.1 hx1.2).2, (hphys_char x2 hx2.1 hx2.2).2, hEq]
  · intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨enc v, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro p q hqp
        simp only [nbPair, Finset.mem_union, Finset.mem_singleton, Option.mem_toFinset,
          Option.mem_def] at hqp
        rcases p with ⟨p1, c1⟩; rcases q with ⟨q1, c2⟩
        rcases hqp with (h1 | h2) | h3
        · have hq : q1 = p1 := congrArg Prod.fst h1
          have hc : c2 = !c1 := congrArg Prod.snd h1
          rw [hq, hc]
          dsimp only [enc]
          by_cases ha : act (owner src dst p1) = true
          · cases c1 <;> cases v (owner src dst p1) <;> simp [ha]
          · simp [ha]
        · cases c1
          · simp only [ringNb, Option.map_eq_some_iff] at h2
            rcases h2 with ⟨q', hprev, heq⟩
            have hq : q' = q1 := congrArg Prod.fst heq
            have hc : true = c2 := congrArg Prod.snd heq
            rw [← hq, ← hc]
            have hown := ringPrev_owner src dst p1 q' hprev
            dsimp only [enc]; rw [hown]
            by_cases ha : act (owner src dst p1) = true
            · cases v (owner src dst p1) <;> simp [ha]
            · simp [ha]
          · simp only [ringNb, Option.map_eq_some_iff] at h2
            rcases h2 with ⟨q', hnext, heq⟩
            have hq : q' = q1 := congrArg Prod.fst heq
            have hc : false = c2 := congrArg Prod.snd heq
            rw [← hq, ← hc]
            have hown := ringNext_owner src dst p1 q' hnext
            dsimp only [enc]; rw [hown]
            by_cases ha : act (owner src dst p1) = true
            · cases v (owner src dst p1) <;> simp [ha]
            · simp [ha]
        · cases p1 <;> cases c1 <;> simp only [arcNb] at h3
          · cases h3
          · cases h3
          · cases h3
          · rename_i a
            have hq : Pair.inEnd a = q1 := congrArg Prod.fst (Option.some.inj h3)
            have hc : false = c2 := congrArg Prod.snd (Option.some.inj h3)
            rw [← hq, ← hc]
            dsimp only [enc, owner]
            by_cases hsrc : act (src a) = true
            · by_cases hdst : act (dst a) = true
              · simp only [hsrc, hdst, ↓reduceIte]
                cases hvs : v (src a)
                · left; rfl
                · right; exact hv.2 a hsrc hdst hvs
              · right; simp [hdst]
            · left; simp [hsrc]
          · rename_i a
            have hq : Pair.outEnd a = q1 := congrArg Prod.fst (Option.some.inj h3)
            have hc : true = c2 := congrArg Prod.snd (Option.some.inj h3)
            rw [← hq, ← hc]
            dsimp only [enc, owner]
            by_cases hdst : act (dst a) = true
            · by_cases hsrc : act (src a) = true
              · simp only [hsrc, hdst, ↓reduceIte]
                cases hvs : v (src a)
                · right; rfl
                · left; exact hv.2 a hsrc hdst hvs
              · right; simp [hsrc]
            · left; simp [hdst]
          · cases h3
      · intro p
        dsimp only [enc]
        cases ha : act (owner src dst p)
        · simp
        · cases v (owner src dst p) <;> simp
    · funext u
      dsimp only [dec, enc, owner]
      by_cases ha : act u = true
      · simp [ha]
      · have haf : act u = false := Bool.eq_false_iff.mpr ha
        simp [ha, hv.1 u haf]

end RingExpansion

section CNFEncoding

inductive LNode (n k h : Nat) where
  | lit (i : Fin n) (c : Bool)
  | lo (i : Fin n) (t : Fin ((n + 1) * h))
  | hi (i : Fin n) (t : Fin ((n + 1) * h))
  | occ (e : Fin k) (i : Fin n) (c : Bool)
  | cl (e : Fin k) (r : Fin (n + 1))
  deriving DecidableEq

inductive LArc (n k h : Nat) where
  | loToLit (i : Fin n) (t : Fin ((n + 1) * h)) (c : Bool)
  | litToHi (i : Fin n) (c : Bool) (t : Fin ((n + 1) * h))
  | litToOcc (e : Fin k) (i : Fin n) (c : Bool)
  | occToLit (e : Fin k) (i : Fin n) (c : Bool)
  | occToCl (e : Fin k) (i : Fin n) (c : Bool) (r : Fin (n + 1))
  deriving DecidableEq

def lnodeEquiv (n k h : Nat) :
    LNode n k h ≃
      (Fin n × Bool) ⊕
      (Fin n × Fin ((n + 1) * h)) ⊕
      (Fin n × Fin ((n + 1) * h)) ⊕
      (Fin k × Fin n × Bool) ⊕
      (Fin k × Fin (n + 1)) where
  toFun
    | .lit i c => Sum.inl (i, c)
    | .lo i t => Sum.inr (Sum.inl (i, t))
    | .hi i t => Sum.inr (Sum.inr (Sum.inl (i, t)))
    | .occ e i c => Sum.inr (Sum.inr (Sum.inr (Sum.inl (e, i, c))))
    | .cl e r => Sum.inr (Sum.inr (Sum.inr (Sum.inr (e, r))))
  invFun
    | Sum.inl (i, c) => .lit i c
    | Sum.inr (Sum.inl (i, t)) => .lo i t
    | Sum.inr (Sum.inr (Sum.inl (i, t))) => .hi i t
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (e, i, c)))) => .occ e i c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (e, r)))) => .cl e r
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, c⟩ | (⟨i, t⟩ | (⟨i, t⟩ | (⟨e, i, c⟩ | ⟨e, r⟩))) <;> rfl

def larcEquiv (n k h : Nat) :
    LArc n k h ≃
      (Fin n × Fin ((n + 1) * h) × Bool) ⊕
      (Fin n × Bool × Fin ((n + 1) * h)) ⊕
      (Fin k × Fin n × Bool) ⊕
      (Fin k × Fin n × Bool) ⊕
      (Fin k × Fin n × Bool × Fin (n + 1)) where
  toFun
    | .loToLit i t c => Sum.inl (i, t, c)
    | .litToHi i c t => Sum.inr (Sum.inl (i, c, t))
    | .litToOcc e i c => Sum.inr (Sum.inr (Sum.inl (e, i, c)))
    | .occToLit e i c => Sum.inr (Sum.inr (Sum.inr (Sum.inl (e, i, c))))
    | .occToCl e i c r => Sum.inr (Sum.inr (Sum.inr (Sum.inr (e, i, c, r))))
  invFun
    | Sum.inl (i, t, c) => .loToLit i t c
    | Sum.inr (Sum.inl (i, c, t)) => .litToHi i c t
    | Sum.inr (Sum.inr (Sum.inl (e, i, c))) => .litToOcc e i c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inl (e, i, c)))) => .occToLit e i c
    | Sum.inr (Sum.inr (Sum.inr (Sum.inr (e, i, c, r)))) => .occToCl e i c r
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨i, t, c⟩ | (⟨i, c, t⟩ | (⟨e, i, c⟩ | (⟨e, i, c⟩ | ⟨e, i, c, r⟩))) <;> rfl

instance instFintypeLNode (n k h : Nat) : Fintype (LNode n k h) :=
  Fintype.ofEquiv _ (lnodeEquiv n k h).symm

instance instFintypeLArc (n k h : Nat) : Fintype (LArc n k h) :=
  Fintype.ofEquiv _ (larcEquiv n k h).symm

lemma card_lnode (n k h : Nat) :
    Fintype.card (LNode n k h) =
      2 * n + 2 * n * ((n + 1) * h) + 2 * n * k + k * (n + 1) := by
  rw [Fintype.card_congr (lnodeEquiv n k h)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

lemma card_larc (n k h : Nat) :
    Fintype.card (LArc n k h) =
      4 * n * ((n + 1) * h) + 4 * n * k + 2 * n * k * (n + 1) := by
  rw [Fintype.card_congr (larcEquiv n k h)]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

def lSrc {n k h : Nat} : LArc n k h → LNode n k h
  | .loToLit i t _ => .lo i t
  | .litToHi i c _ => .lit i c
  | .litToOcc _ i c => .lit i c
  | .occToLit e i c => .occ e i c
  | .occToCl e i c _ => .occ e i c

def lDst {n k h : Nat} : LArc n k h → LNode n k h
  | .loToLit i _ c => .lit i c
  | .litToHi i _ t => .hi i t
  | .litToOcc e i c => .occ e i c
  | .occToLit _ i c => .lit i c
  | .occToCl e _ _ r => .cl e r

def lSource {n k h : Nat} : LNode n k h → Option (Fin k ⊕ (Fin k × Fin n × Bool))
  | .lit _ _ => none
  | .lo _ _ => none
  | .hi _ _ => none
  | .occ e i c => some (Sum.inr (e, i, c))
  | .cl e _ => some (Sum.inl e)

lemma card_bool_pred_all (P : Prop) :
    ((Finset.univ : Finset Bool).filter (fun x => x = true → P)).card = if P then 2 else 1 := by
  by_cases hP : P
  · simp [hP]
  · have : (Finset.univ : Finset Bool).filter (fun x => x = true → P) = {false} := by
      ext b; cases b <;> simp [hP]
    rw [this]; simp [hP]

lemma card_bool_pred_rev (P : Prop) :
    ((Finset.univ : Finset Bool).filter (fun x => P → x = true)).card = if P then 1 else 2 := by
  by_cases hP : P
  · have : (Finset.univ : Finset Bool).filter (fun x => P → x = true) = {true} := by
      ext b; cases b <;> simp [hP]
    rw [this]; simp [hP]
  · simp [hP]

lemma card_filter_univ_eq {α : Type*} {F1 F2 : Fintype α} {p q : α → Prop}
    {dp : DecidablePred p} {dq : DecidablePred q} (h : ∀ a, p a ↔ q a) :
    (@Finset.filter α p dp (@Finset.univ α F1)).card =
    (@Finset.filter α q dq (@Finset.univ α F2)).card := by
  congr 1; ext a; simp only [Finset.mem_filter]
  exact ⟨fun ⟨_, hp⟩ => ⟨@Finset.mem_univ α F2 a, (h a).mp hp⟩,
         fun ⟨_, hq⟩ => ⟨@Finset.mem_univ α F1 a, (h a).mpr hq⟩⟩

lemma logValid_fiber_card (n k h : Nat)
    (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool)
    (ℓ : Fin n → Bool → Bool) :
    let act : LNode n k h → Bool := fun u =>
      (lSource u).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))
    let b := n + 1
    let B := 2 ^ b
    ((Finset.univ : Finset (LNode n k h → Bool)).filter (fun v =>
      (∀ i c, v (.lit i c) = ℓ i c) ∧
      (∀ u, act u = false → v u = false) ∧
      ∀ a : LArc n k h, act (lSrc a) = true → act (lDst a) = true →
        v (lSrc a) = true → v (lDst a) = true)).card =
    (∏ i : Fin n, if ℓ i false = true ∧ ℓ i true = true then B ^ h else 1) *
    (∏ i : Fin n, if ℓ i false = false ∧ ℓ i true = false then B ^ h else 1) *
    (∏ e : Fin k, if on e = true ∧ ∀ i c, lit e i c = true → ℓ i c = false then B else 1) := by
  intro act b B
  let Slo : Finset (Fin n × Fin (b * h) → Bool) :=
    Finset.univ.filter (fun f => ∀ p, f p = true → ℓ p.1 false = true ∧ ℓ p.1 true = true)
  let Shi : Finset (Fin n × Fin (b * h) → Bool) :=
    Finset.univ.filter (fun f => ∀ p, (ℓ p.1 false = true ∨ ℓ p.1 true = true) → f p = true)
  let Scl : Finset (Fin k × Fin b → Bool) :=
    Finset.univ.filter (fun f => ∀ p,
      (on p.1 = false → f p = false) ∧
      (on p.1 = true → (∃ i c, lit p.1 i c = true ∧ ℓ i c = true) → f p = true))
  -- Step 1: Bijection with Slo × Shi × Scl
  have hbij :
      ((Finset.univ : Finset (LNode n k h → Bool)).filter (fun v =>
        (∀ i c, v (.lit i c) = ℓ i c) ∧
        (∀ u, act u = false → v u = false) ∧
        ∀ a : LArc n k h, act (lSrc a) = true → act (lDst a) = true →
          v (lSrc a) = true → v (lDst a) = true)).card =
      ((Slo ×ˢ Shi) ×ˢ Scl).card := by
    let toTrip : (LNode n k h → Bool) →
        ((Fin n × Fin (b * h) → Bool) × (Fin n × Fin (b * h) → Bool)) × (Fin k × Fin b → Bool) :=
      fun v => ((fun p => v (.lo p.1 p.2), fun p => v (.hi p.1 p.2)), fun p => v (.cl p.1 p.2))
    let fromTrip :
        ((Fin n × Fin (b * h) → Bool) × (Fin n × Fin (b * h) → Bool)) × (Fin k × Fin b → Bool) →
        (LNode n k h → Bool) := fun ⟨⟨flo, fhi⟩, fcl⟩ u =>
      match u with
      | .lit i c => ℓ i c
      | .lo i t => flo (i, t)
      | .hi i t => fhi (i, t)
      | .occ e i c => if lit e i c = true then ℓ i c else false
      | .cl e r => fcl (e, r)
    refine Finset.card_bij (fun v _ => toTrip v) ?_ ?_ ?_
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      rcases hv with ⟨hlit, hinact, harc⟩
      have hocc : ∀ e i c, v (.occ e i c) = if lit e i c = true then ℓ i c else false := by
        intro e i c
        by_cases hlic : lit e i c = true
        · simp only [hlic, ↓reduceIte]
          have ha1 : act (.lit i c) = true := rfl
          have ha2 : act (.occ e i c) = true := hlic
          have h1 := harc (.litToOcc e i c) ha1 ha2
          have h2 := harc (.occToLit e i c) ha2 ha1
          dsimp only [lSrc, lDst] at h1 h2
          rw [hlit i c] at h1 h2
          apply Bool.eq_iff_iff.mpr; exact ⟨h2, h1⟩
        · simp only [hlic, ↓reduceIte]
          have hlicf : lit e i c = false := Bool.eq_false_iff.mpr hlic
          exact hinact (.occ e i c) hlicf
      simp only [Finset.mem_product, Slo, Shi, Scl, Finset.mem_filter, Finset.mem_univ, true_and,
        toTrip]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro ⟨i, t⟩ hft
        constructor
        · have := harc (.loToLit i t false) rfl rfl hft
          dsimp only [lDst] at this; rwa [hlit i false] at this
        · have := harc (.loToLit i t true) rfl rfl hft
          dsimp only [lDst] at this; rwa [hlit i true] at this
      · intro ⟨i, t⟩ hor
        rcases hor with hf | ht
        · have := harc (.litToHi i false t) rfl rfl (by dsimp only [lSrc]; rw [hlit i false]; exact hf)
          exact this
        · have := harc (.litToHi i true t) rfl rfl (by dsimp only [lSrc]; rw [hlit i true]; exact ht)
          exact this
      · intro ⟨e, r⟩
        refine ⟨fun hoff => hinact (.cl e r) hoff, ?_⟩
        rintro hon ⟨i, c, hlic, hℓ⟩
        have hv_occ : v (.occ e i c) = true := by rw [hocc e i c, if_pos hlic, hℓ]
        exact harc (.occToCl e i c r) hlic hon hv_occ
    · intro v1 hv1 v2 hv2 hEq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv1 hv2
      have hocc : ∀ v : LNode n k h → Bool,
          (∀ i c, v (.lit i c) = ℓ i c) →
          (∀ u, act u = false → v u = false) →
          (∀ a : LArc n k h, act (lSrc a) = true → act (lDst a) = true →
            v (lSrc a) = true → v (lDst a) = true) →
          ∀ e i c, v (.occ e i c) = if lit e i c = true then ℓ i c else false := by
        intro v hlit hinact harc e i c
        by_cases hlic : lit e i c = true
        · simp only [hlic, ↓reduceIte]
          have h1 := harc (.litToOcc e i c) rfl hlic
          have h2 := harc (.occToLit e i c) hlic rfl
          dsimp only [lSrc, lDst] at h1 h2; rw [hlit i c] at h1 h2
          apply Bool.eq_iff_iff.mpr; exact ⟨h2, h1⟩
        · simp only [hlic, ↓reduceIte]
          exact hinact (.occ e i c) (Bool.eq_false_iff.mpr hlic)
      have hlo := congrArg (fun z => z.1.1) hEq
      have hhi := congrArg (fun z => z.1.2) hEq
      have hcl := congrArg (fun z => z.2) hEq
      funext u
      cases u with
      | lit i c => rw [hv1.1 i c, hv2.1 i c]
      | lo i t => exact congrFun hlo (i, t)
      | hi i t => exact congrFun hhi (i, t)
      | occ e i c => rw [hocc v1 hv1.1 hv1.2.1 hv1.2.2, hocc v2 hv2.1 hv2.2.1 hv2.2.2]
      | cl e r => exact congrFun hcl (e, r)
    · rintro ⟨⟨flo, fhi⟩, fcl⟩ ht
      simp only [Finset.mem_product, Slo, Shi, Scl, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rcases ht with ⟨⟨hflo, hfhi⟩, hfcl⟩
      refine ⟨fromTrip ((flo, fhi), fcl), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨fun i c => rfl, ?_, ?_⟩
      · intro u hu
        cases u with
        | lit i c => simp [act, lSource] at hu
        | lo i t => simp [act, lSource] at hu
        | hi i t => simp [act, lSource] at hu
        | occ e i c =>
          have hlic : lit e i c = false := hu
          simp [fromTrip, hlic]
        | cl e r =>
          exact (hfcl (e, r)).1 hu
      · intro a hsrc hdst hv
        cases a with
        | loToLit i t c =>
          have hpair := hflo (i, t) hv
          cases c <;> simp [fromTrip, lDst, hpair]
        | litToHi i c t =>
          apply hfhi (i, t)
          cases c
          · exact Or.inl hv
          · exact Or.inr hv
        | litToOcc e i c =>
          have hlic : lit e i c = true := hdst
          simp [fromTrip, lDst, hlic]; exact hv
        | occToLit e i c =>
          have hlic : lit e i c = true := hsrc
          dsimp only [fromTrip, lSrc, lDst] at hv ⊢
          rw [if_pos hlic] at hv; exact hv
        | occToCl e i c r =>
          have hlic : lit e i c = true := hsrc
          have hon : on e = true := hdst
          dsimp only [fromTrip, lSrc, lDst] at hv ⊢
          rw [if_pos hlic] at hv
          exact (hfcl (e, r)).2 hon ⟨i, c, hlic, hv⟩
  rw [hbij, Finset.card_product, Finset.card_product]
  -- Step 2: Evaluate Slo.card, Shi.card, Scl.card
  have hSlo : Slo.card = ∏ i : Fin n, if ℓ i false = true ∧ ℓ i true = true then B ^ h else 1 := by
    have hpi : Slo = Fintype.piFinset (fun p : Fin n × Fin (b * h) =>
        (Finset.univ : Finset Bool).filter (fun x => x = true → ℓ p.1 false = true ∧ ℓ p.1 true = true)) := by
      ext f; simp [Slo]
    rw [hpi, Fintype.card_piFinset]
    have h1 : (∏ p : Fin n × Fin (b * h),
        ((Finset.univ : Finset Bool).filter (fun x => x = true → ℓ p.1 false = true ∧ ℓ p.1 true = true)).card) =
        ∏ p : Fin n × Fin (b * h), if ℓ p.1 false = true ∧ ℓ p.1 true = true then 2 else 1 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      cases ℓ p.1 false <;> cases ℓ p.1 true <;> decide
    rw [h1, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hc : ℓ i false = true ∧ ℓ i true = true <;> simp [hc, B, pow_mul]
  have hShi : Shi.card = ∏ i : Fin n, if ℓ i false = false ∧ ℓ i true = false then B ^ h else 1 := by
    have hpi : Shi = Fintype.piFinset (fun p : Fin n × Fin (b * h) =>
        (Finset.univ : Finset Bool).filter (fun x => (ℓ p.1 false = true ∨ ℓ p.1 true = true) → x = true)) := by
      ext f; simp [Shi]
    rw [hpi, Fintype.card_piFinset]
    have h1 : (∏ p : Fin n × Fin (b * h),
        ((Finset.univ : Finset Bool).filter (fun x => (ℓ p.1 false = true ∨ ℓ p.1 true = true) → x = true)).card) =
        ∏ p : Fin n × Fin (b * h), if ℓ p.1 false = false ∧ ℓ p.1 true = false then 2 else 1 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      cases ℓ p.1 false <;> cases ℓ p.1 true <;> decide
    rw [h1, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hc : ℓ i false = false ∧ ℓ i true = false <;> simp [hc, B, pow_mul]
  have hScl : Scl.card = ∏ e : Fin k,
      if on e = true ∧ ∀ i c, lit e i c = true → ℓ i c = false then B else 1 := by
    have hpi : Scl = Fintype.piFinset (fun p : Fin k × Fin b =>
        (Finset.univ : Finset Bool).filter (fun x =>
          (on p.1 = false → x = false) ∧
          (on p.1 = true → (∃ i c, lit p.1 i c = true ∧ ℓ i c = true) → x = true))) := by
      ext f; simp [Scl]
    rw [hpi, Fintype.card_piFinset]
    have h1 : (∏ p : Fin k × Fin b,
        ((Finset.univ : Finset Bool).filter (fun x =>
          (on p.1 = false → x = false) ∧
          (on p.1 = true → (∃ i c, lit p.1 i c = true ∧ ℓ i c = true) → x = true))).card) =
        ∏ p : Fin k × Fin b,
          if on p.1 = true ∧ ∀ i c, lit p.1 i c = true → ℓ i c = false then 2 else 1 := by
      refine Finset.prod_congr rfl fun p _ => ?_
      by_cases hon : on p.1 = true
      · by_cases hall : ∀ i c, lit p.1 i c = true → ℓ i c = false
        · have hno : ¬ ∃ i c, lit p.1 i c = true ∧ ℓ i c = true := by
            rintro ⟨i, c, hlic, hℓ⟩; have := hall i c hlic; rw [hℓ] at this; cases this
          have hfilt : (Finset.univ : Finset Bool).filter (fun x =>
              (on p.1 = false → x = false) ∧
              (on p.1 = true → (∃ i c, lit p.1 i c = true ∧ ℓ i c = true) → x = true)) = Finset.univ := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
            exact ⟨fun hf => (by rw [hon] at hf; cases hf), fun _ hex => absurd hex hno⟩
          rw [hfilt, if_pos ⟨hon, hall⟩]; decide
        · have hex : ∃ i c, lit p.1 i c = true ∧ ℓ i c = true := by
            by_contra hno
            apply hall; intro i c hlic
            cases hv : ℓ i c
            · rfl
            · exact absurd ⟨i, c, hlic, hv⟩ hno
          have hfilt : (Finset.univ : Finset Bool).filter (fun x =>
              (on p.1 = false → x = false) ∧
              (on p.1 = true → (∃ i c, lit p.1 i c = true ∧ ℓ i c = true) → x = true)) = {true} := by
            ext x
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro ⟨_, h2⟩; exact h2 hon hex
            · rintro rfl; exact ⟨fun hf => (by rw [hon] at hf; cases hf), fun _ _ => rfl⟩
          rw [hfilt, if_neg (fun h => hall h.2)]; decide
      · have hoff : on p.1 = false := Bool.eq_false_iff.mpr hon
        have hfilt : (Finset.univ : Finset Bool).filter (fun x =>
            (on p.1 = false → x = false) ∧
            (on p.1 = true → (∃ i c, lit p.1 i c = true ∧ ℓ i c = true) → x = true)) = {false} := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · intro ⟨h1, _⟩; exact h1 hoff
          · rintro rfl; exact ⟨fun _ => rfl, fun ht => (by rw [hoff] at ht; cases ht)⟩
        rw [hfilt, if_neg (fun h => hon h.1)]; decide
    rw [h1, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun e _ => ?_
    by_cases hc : on e = true ∧ ∀ i c, lit e i c = true → ℓ i c = false <;> simp [hc, B]
  rw [hSlo, hShi, hScl]

lemma baseB_digit_extraction (n k h : Nat)
    (violations : (Fin n → Bool) → Nat) (Zill : Nat)
    (hdiv : (2 ^ (n + 1)) ^ h ∣ Zill) :
    let B := 2 ^ (n + 1)
    let Z := (∑ y : Fin n → Bool, B ^ (violations y)) + Zill
    0 < Z ∧ ∀ j : Nat, j < h →
      (Z / B ^ j) % B = ((Finset.univ : Finset (Fin n → Bool)).filter
        (fun y => violations y = j)).card := by
  intro B Z
  have hB_pos : 0 < B := by positivity
  have hpow_pos : ∀ r : Nat, 0 < B ^ r := fun r => pow_pos hB_pos r
  have hZ_pos : 0 < Z := by
    have h1 : 0 < ∑ y : Fin n → Bool, B ^ (violations y) := by
      have hmem : (fun _ : Fin n => false) ∈ (Finset.univ : Finset (Fin n → Bool)) := Finset.mem_univ _
      calc 0 < B ^ (violations (fun _ => false)) := hpow_pos _
        _ ≤ ∑ y : Fin n → Bool, B ^ (violations y) :=
            Finset.single_le_sum (f := fun y => B ^ (violations y)) (fun _ _ => Nat.zero_le _) hmem
    omega
  refine ⟨hZ_pos, ?_⟩
  intro j hj
  let Ylo := (Finset.univ : Finset (Fin n → Bool)).filter (fun y => violations y < j)
  let Yeq := (Finset.univ : Finset (Fin n → Bool)).filter (fun y => violations y = j)
  let Yhi := (Finset.univ : Finset (Fin n → Bool)).filter (fun y => j < violations y)
  have hpart : (∑ y : Fin n → Bool, B ^ (violations y)) =
      (∑ y ∈ Ylo, B ^ (violations y)) +
      (∑ y ∈ Yeq, B ^ (violations y)) +
      (∑ y ∈ Yhi, B ^ (violations y)) := by
    have h1 : (Finset.univ : Finset (Fin n → Bool)) = (Ylo ∪ Yeq) ∪ Yhi := by
      ext y; simp only [Ylo, Yeq, Yhi, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact ⟨fun _ => by omega, fun _ => trivial⟩
    have hd1 : Disjoint Ylo Yeq := by
      rw [Finset.disjoint_left]; intro y h1 h2
      simp only [Ylo, Yeq, Finset.mem_filter] at h1 h2; omega
    have hd2 : Disjoint (Ylo ∪ Yeq) Yhi := by
      rw [Finset.disjoint_left]; intro y h1 h2
      simp only [Ylo, Yeq, Yhi, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
    conv_lhs => rw [h1]
    rw [Finset.sum_union hd2, Finset.sum_union hd1]
  have hSlo_lt : (∑ y ∈ Ylo, B ^ (violations y)) < B ^ j := by
    cases j with
    | zero =>
      have : Ylo = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro y hy; simp only [Ylo, Finset.mem_filter] at hy; omega
      rw [this, Finset.sum_empty]; simp
    | succ j' =>
      have hterm : ∀ y ∈ Ylo, B ^ (violations y) ≤ B ^ j' := by
        intro y hy
        simp only [Ylo, Finset.mem_filter] at hy
        exact Nat.pow_le_pow_right hB_pos (by omega)
      have hcard_le : Ylo.card ≤ 2 ^ n := by
        have := Finset.card_le_univ Ylo
        simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this
      have h2n_lt : 2 ^ n < B := by
        dsimp only [B]; rw [pow_succ]
        have hpos : 0 < 2 ^ n := by positivity
        omega
      calc (∑ y ∈ Ylo, B ^ (violations y))
          ≤ ∑ _y ∈ Ylo, B ^ j' := Finset.sum_le_sum hterm
        _ = Ylo.card * B ^ j' := by simp
        _ ≤ 2 ^ n * B ^ j' := Nat.mul_le_mul_right _ hcard_le
        _ < B * B ^ j' := Nat.mul_lt_mul_of_pos_right h2n_lt (hpow_pos j')
        _ = B ^ (j' + 1) := by rw [pow_succ']
  have hSeq_eq : (∑ y ∈ Yeq, B ^ (violations y)) = Yeq.card * B ^ j := by
    calc (∑ y ∈ Yeq, B ^ (violations y))
        = ∑ _y ∈ Yeq, B ^ j := Finset.sum_congr rfl fun y hy => by
            rw [(Finset.mem_filter.mp hy).2]
      _ = Yeq.card * B ^ j := by simp
  have hYeq_lt : Yeq.card < B := by
    have hcard_le : Yeq.card ≤ 2 ^ n := by
      have := Finset.card_le_univ Yeq
      simpa [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using this
    have h2n_lt : 2 ^ n < B := by
      dsimp only [B]; rw [pow_succ]
      have hpos : 0 < 2 ^ n := by positivity
      omega
    omega
  have hShi_div : B ^ (j + 1) ∣ (∑ y ∈ Yhi, B ^ (violations y)) := by
    apply Finset.dvd_sum
    intro y hy
    simp only [Yhi, Finset.mem_filter] at hy
    exact pow_dvd_pow B (by omega)
  have hZill_div : B ^ (j + 1) ∣ Zill :=
    dvd_trans (pow_dvd_pow B (by omega)) hdiv
  rcases dvd_add hShi_div hZill_div with ⟨M, hM⟩
  have hZ_eq : Z = (∑ y ∈ Ylo, B ^ (violations y)) + (Yeq.card + M * B) * B ^ j := by
    dsimp only [Z]
    rw [hpart, hSeq_eq, add_assoc, add_assoc, hM, pow_succ']
    ring
  rw [hZ_eq, Nat.add_mul_div_right _ _ (hpow_pos j), Nat.div_eq_of_lt hSlo_lt, zero_add,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hYeq_lt]

theorem main (n k h : Nat) (hh : 0 < h) :
    let b := n + 1
    let B := 2 ^ b
    ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
      (source : Fin m → Option (Fin k ⊕ (Fin k × Fin n × Bool))),
      m ≤ 2 * n + 10 * n * k + 10 * n * b * h + k * b + 4 * n * k * b ∧
      (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
      (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧ (∀ p, ∀ q ∈ nb p, p.2 ≠ q.2) ∧
      (∀ i, (i, true) ∈ nb (i, false)) ∧
      ∀ (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool),
        let active := fun i => (source i).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))
        let Z := ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
          (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
          ∀ i, xor (x (i, false)) (x (i, true)) = active i)).card
        let violations := fun (y : Fin n → Bool) =>
          ((Finset.univ : Finset (Fin k)).filter (fun e =>
            on e = true ∧ ∀ i, lit e i (y i) = false)).card
        0 < Z ∧ ∀ j : Nat, j < h →
          (Z / B ^ j) % B = ((Finset.univ : Finset (Fin n → Bool)).filter
            (fun y => violations y = j)).card := by
  intro b B
  let P := Pair (LNode n k h) (LArc n k h)
  let m := Fintype.card P
  let eqP : P ≃ Fin m := Fintype.equivFin P
  let eqPB : (P × Bool) ≃ (Fin m × Bool) := eqP.prodCongr (Equiv.refl Bool)
  let nb : (Fin m × Bool) → Finset (Fin m × Bool) :=
    fun p => (nbPair lSrc lDst (eqPB.symm p)).image eqPB
  let source : Fin m → Option (Fin k ⊕ (Fin k × Fin n × Bool)) :=
    fun i => lSource (owner lSrc lDst (eqP.symm i))
  have hmem_nb : ∀ (p q : P) (c1 c2 : Bool),
      (eqP q, c2) ∈ nb (eqP p, c1) ↔ (q, c2) ∈ nbPair lSrc lDst (p, c1) := by
    intro p q c1 c2
    dsimp only [nb]
    have hsym : eqPB.symm (eqP p, c1) = (p, c1) := by simp [eqPB]
    rw [hsym, Finset.mem_image]
    constructor
    · rintro ⟨⟨q', c2'⟩, hmem, heq⟩
      have hq' : q' = q := eqP.injective (congrArg Prod.fst heq)
      have hc2' : c2' = c2 := congrArg Prod.snd heq
      subst hq'; subst hc2'; exact hmem
    · intro hmem; exact ⟨(q, c2), hmem, rfl⟩
  have hm_eq : m = 2 * n + 10 * n * k + 10 * n * b * h + k * b + 4 * n * k * b := by
    dsimp only [m, P, b]
    rw [card_pair, card_lnode, card_larc]
    ring
  refine ⟨m, nb, source, le_of_eq hm_eq, ?_, ?_, ?_, ?_, ?_⟩
  · intro ⟨i, c⟩
    constructor
    · rw [← eqP.apply_symm_apply i, hmem_nb]
      exact nbPair_irrefl lSrc lDst _
    · dsimp only [nb]
      exact le_trans Finset.card_image_le (nbPair_card_le lSrc lDst _)
  · intro ⟨i, c1⟩ ⟨j, c2⟩
    rw [← eqP.apply_symm_apply i, ← eqP.apply_symm_apply j, hmem_nb, hmem_nb]
    exact nbPair_symm lSrc lDst _ _
  · intro ⟨i, c1⟩ ⟨j, c2⟩ hmem
    rw [← eqP.apply_symm_apply i, ← eqP.apply_symm_apply j, hmem_nb] at hmem
    exact nbPair_bip lSrc lDst _ _ hmem
  · intro i
    rw [← eqP.apply_symm_apply i, hmem_nb]
    simp [nbPair]
  · intro on lit
    dsimp only
    let act : LNode n k h → Bool := fun u =>
      (lSource u).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))
    let violations : (Fin n → Bool) → Nat := fun y =>
      ((Finset.univ : Finset (Fin k)).filter (fun e =>
        on e = true ∧ ∀ i, lit e i (y i) = false)).card
    -- Transport Z from Fin m to Pair
    have hZ_eq_pair :
        ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
          (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
          ∀ i, xor (x (i, false)) (x (i, true)) =
            (source i).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2)))).card =
        ((Finset.univ : Finset ((P × Bool) → Bool)).filter (fun x =>
          (∀ p, ∀ q ∈ nbPair lSrc lDst p, x p = true ∨ x q = true) ∧
          ∀ p, xor (x (p, false)) (x (p, true)) = act (owner lSrc lDst p))).card := by
      refine Finset.card_bij (fun x _ => fun pc => x (eqPB pc)) ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
        constructor
        · intro ⟨p1, c1⟩ ⟨q1, c2⟩ hqp
          apply hx.1 (eqP p1, c1) (eqP q1, c2)
          rw [hmem_nb]; exact hqp
        · intro p
          have hxp := hx.2 (eqP p)
          simpa [eqPB, source, act] using hxp
      · intro x1 _ x2 _ hEq
        funext ⟨i, c⟩
        have h1 := congrFun hEq (eqP.symm i, c)
        simpa [eqPB] using h1
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        refine ⟨fun pc => x (eqPB.symm pc), ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro ⟨i, c1⟩ ⟨j, c2⟩ hij
            have hmem : (eqP.symm j, c2) ∈ nbPair lSrc lDst (eqP.symm i, c1) := by
              rw [← eqP.apply_symm_apply i, ← eqP.apply_symm_apply j, hmem_nb] at hij
              exact hij
            simpa [eqPB] using hx.1 (eqP.symm i, c1) (eqP.symm j, c2) hmem
          · intro i
            simpa [eqPB, source, act] using hx.2 (eqP.symm i)
        · funext ⟨p, c⟩; simp [eqPB]
    rw [hZ_eq_pair, ring_expansion_card lSrc lDst act]
    -- Partition logValid by ℓ : Fin n → Bool → Bool
    let logValid := (Finset.univ : Finset (LNode n k h → Bool)).filter (fun v =>
      (∀ u, act u = false → v u = false) ∧
      ∀ a : LArc n k h, act (lSrc a) = true → act (lDst a) = true →
        v (lSrc a) = true → v (lDst a) = true)
    let fiberOf : (Fin n → Bool → Bool) → Finset (LNode n k h → Bool) := fun ℓ =>
      (Finset.univ : Finset (LNode n k h → Bool)).filter (fun v =>
        (∀ i c, v (.lit i c) = ℓ i c) ∧
        (∀ u, act u = false → v u = false) ∧
        ∀ a : LArc n k h, act (lSrc a) = true → act (lDst a) = true →
          v (lSrc a) = true → v (lDst a) = true)
    have hZ_sum_ell : logValid.card = ∑ ℓ : Fin n → Bool → Bool, (fiberOf ℓ).card := by
      have hmap := Finset.card_eq_sum_card_fiberwise
        (s := logValid) (t := (Finset.univ : Finset (Fin n → Bool → Bool)))
        (f := fun v i c => v (.lit i c)) (fun _ _ => Finset.mem_univ _)
      rw [hmap]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      congr 1
      ext v
      simp only [logValid, fiberOf, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨fun i c => congrFun (congrFun h3 i) c, h1, h2⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h2, h3⟩, funext fun i => funext fun c => h1 i c⟩
    rw [hZ_sum_ell]
    let Legal : Finset (Fin n → Bool → Bool) :=
      Finset.univ.filter (fun ℓ => ∀ i : Fin n, ℓ i false ≠ ℓ i true)
    let Illegal : Finset (Fin n → Bool → Bool) :=
      Finset.univ.filter (fun ℓ => ∃ i : Fin n, ℓ i false = ℓ i true)
    have hsplit : (∑ ℓ : Fin n → Bool → Bool, (fiberOf ℓ).card) =
        (∑ ℓ ∈ Legal, (fiberOf ℓ).card) + (∑ ℓ ∈ Illegal, (fiberOf ℓ).card) := by
      have hunion : (Finset.univ : Finset (Fin n → Bool → Bool)) = Legal ∪ Illegal := by
        ext ℓ
        simp only [Legal, Illegal, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro _
          by_cases h1 : ∀ i, ℓ i false ≠ ℓ i true
          · exact Or.inl h1
          · right; push_neg at h1; exact h1
        · intro _; trivial
      have hdisj : Disjoint Legal Illegal := by
        rw [Finset.disjoint_left]
        intro ℓ h1 h2
        simp only [Legal, Illegal, Finset.mem_filter] at h1 h2
        rcases h2.2 with ⟨i, hi⟩
        exact h1.2 i hi
      conv_lhs => rw [hunion]
      exact Finset.sum_union hdisj
    rw [hsplit]
    have hZ_legal : (∑ ℓ ∈ Legal, (fiberOf ℓ).card) = ∑ y : Fin n → Bool, B ^ (violations y) := by
      refine Finset.sum_bij (fun (ℓ : Fin n → Bool → Bool) _ => fun i => ℓ i true) ?_ ?_ ?_ ?_
      · intro _ _; exact Finset.mem_univ _
      · intro ℓ1 h1 ℓ2 h2 hEq
        simp only [Legal, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
        funext i c
        have ht : ℓ1 i true = ℓ2 i true := congrFun hEq i
        cases c
        · have hne1 := h1 i; have hne2 := h2 i
          cases h1f : ℓ1 i false <;> cases h1t : ℓ1 i true <;>
            cases h2f : ℓ2 i false <;> cases h2t : ℓ2 i true <;>
            simp [h1f, h1t, h2f, h2t] at hne1 hne2 ht ⊢
        · exact ht
      · intro y _
        refine ⟨fun i c => (y i == c), ?_, ?_⟩
        · simp only [Legal, Finset.mem_filter, Finset.mem_univ, true_and]
          intro i; cases y i <;> decide
        · funext i; dsimp only; cases y i <;> rfl
      · intro ℓ hℓ
        simp only [Legal, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
        have hfib := logValid_fiber_card n k h on lit ℓ
        change (fiberOf ℓ).card = _ at hfib
        rw [hfib]
        have hlo1 : (∏ i : Fin n, if ℓ i false = true ∧ ℓ i true = true then B ^ h else 1) = 1 := by
          apply Finset.prod_eq_one
          intro i _
          have hne := hℓ i
          rw [if_neg]; rintro ⟨h1, h2⟩; exact hne (h1.trans h2.symm)
        have hhi1 : (∏ i : Fin n, if ℓ i false = false ∧ ℓ i true = false then B ^ h else 1) = 1 := by
          apply Finset.prod_eq_one
          intro i _
          have hne := hℓ i
          rw [if_neg]; rintro ⟨h1, h2⟩; exact hne (h1.trans h2.symm)
        rw [hlo1, hhi1, one_mul, one_mul]
        have hcl_eq : ∀ e : Fin k,
            (if on e = true ∧ ∀ i c, lit e i c = true → ℓ i c = false then B else 1) =
            if on e = true ∧ ∀ i, lit e i (ℓ i true) = false then B else 1 := by
          intro e
          have hiff : (∀ i c, lit e i c = true → ℓ i c = false) ↔
              (∀ i, lit e i (ℓ i true) = false) := by
            constructor
            · intro hall i
              cases hli : lit e i (ℓ i true)
              · rfl
              · have h0 := hall i (ℓ i true) hli
                have hne := hℓ i
                cases h1 : ℓ i true
                · rw [h1] at h0 hne; cases h2 : ℓ i false <;> simp [h2] at h0 hne
                · rw [h1] at h0; rw [h1] at h0; cases h0
            · intro hall i c hlic
              cases hc : c
              · have hne := hℓ i
                cases h1 : ℓ i true
                · have := hall i; rw [h1] at this; rw [hc, this] at hlic; cases hlic
                · cases h2 : ℓ i false <;> simp [h1, h2] at hne ⊢
              · cases h1 : ℓ i true
                · rfl
                · have := hall i; rw [h1] at this; rw [hc, this] at hlic; cases hlic
          simp only [hiff]
        have hprod_eq : (∏ e : Fin k, if on e = true ∧ ∀ i c, lit e i c = true → ℓ i c = false then B else 1) =
            ∏ e : Fin k, if on e = true ∧ ∀ i, lit e i (ℓ i true) = false then B else 1 :=
          Finset.prod_congr rfl fun e _ => hcl_eq e
        rw [hprod_eq, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    have hZ_ill_div : B ^ h ∣ ∑ ℓ ∈ Illegal, (fiberOf ℓ).card := by
      apply Finset.dvd_sum
      intro ℓ hℓ
      simp only [Illegal, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
      rcases hℓ with ⟨i0, hi0⟩
      have hfib := logValid_fiber_card n k h on lit ℓ
      change (fiberOf ℓ).card = _ at hfib
      rw [hfib]
      cases hv : ℓ i0 false
      · have hi0t : ℓ i0 true = false := hi0.symm.trans hv
        have hd : B ^ h ∣ ∏ i : Fin n, if ℓ i false = false ∧ ℓ i true = false then B ^ h else 1 := by
          have := Finset.dvd_prod_of_mem
            (fun i : Fin n => if ℓ i false = false ∧ ℓ i true = false then B ^ h else 1)
            (Finset.mem_univ i0)
          simpa [hv, hi0t] using this
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd _) _
      · have hi0t : ℓ i0 true = true := hi0.symm.trans hv
        have hd : B ^ h ∣ ∏ i : Fin n, if ℓ i false = true ∧ ℓ i true = true then B ^ h else 1 := by
          have := Finset.dvd_prod_of_mem
            (fun i : Fin n => if ℓ i false = true ∧ ℓ i true = true then B ^ h else 1)
            (Finset.mem_univ i0)
          simpa [hv, hi0t] using this
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
    rw [hZ_legal]
    exact baseB_digit_extraction n k h violations (∑ ℓ ∈ Illegal, (fiberOf ℓ).card) hZ_ill_div

end CNFEncoding

end PEqualNP.Outside.L_lib_1201_aux

theorem PEqualNP.Outside.L_lib_1201 :
letI : ∀ p : Prop, Decidable p := Classical.propDecidable
∀ n k h : Nat, 0 < h →
  let b := n+1
  let B := 2^b
  ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
    (source : Fin m → Option (Fin k ⊕ (Fin k × Fin n × Bool))),
    m ≤ 2*n + 10*n*k + 10*n*b*h + k*b + 4*n*k*b ∧
    (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
    (∀ p q, q ∈ nb p ↔ p ∈ nb q) ∧ (∀ p, ∀ q ∈ nb p, p.2 ≠ q.2) ∧
    (∀ i, (i,true) ∈ nb (i,false)) ∧
    ∀ (on : Fin k → Bool) (lit : Fin k → Fin n → Bool → Bool),
      let active := fun i => (source i).elim true (Sum.elim on (fun p => lit p.1 p.2.1 p.2.2))
      let Z := ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
        (∀ p, ∀ q ∈ nb p, x p = true ∨ x q = true) ∧
        ∀ i, xor (x (i,false)) (x (i,true)) = active i)).card
      let violations := fun (y : Fin n → Bool) =>
        ((Finset.univ : Finset (Fin k)).filter (fun e =>
          on e = true ∧ ∀ i, lit e i (y i) = false)).card
      0 < Z ∧ ∀ j : Nat, j < h →
        (Z / B^j) % B = ((Finset.univ : Finset (Fin n → Bool)).filter
          (fun y => violations y = j)).card := by
  intro n k h hh
  rcases PEqualNP.Outside.L_lib_1201_aux.main n k h hh with
    ⟨m, nb, source, hm, h1, h2, h3, h4, h5⟩
  refine ⟨m, nb, source, hm, h1, h2, h3, h4, fun on lit => ?_⟩
  rcases h5 on lit with ⟨hpos, hdig⟩
  dsimp only at hpos hdig ⊢
  refine ⟨?_, fun j hj => ?_⟩
  · refine lt_of_lt_of_eq hpos ?_
    exact PEqualNP.Outside.L_lib_1201_aux.card_filter_univ_eq (fun _ => Iff.rfl)
  · exact (congrArg (fun z => (z / (2 ^ (n + 1)) ^ j) % 2 ^ (n + 1))
      (PEqualNP.Outside.L_lib_1201_aux.card_filter_univ_eq (fun _ => Iff.rfl))).trans
      ((hdig j hj).trans
        (PEqualNP.Outside.L_lib_1201_aux.card_filter_univ_eq (fun y =>
          Eq.to_iff (congrArg (· = j)
            (PEqualNP.Outside.L_lib_1201_aux.card_filter_univ_eq (fun _ => Iff.rfl))))))
