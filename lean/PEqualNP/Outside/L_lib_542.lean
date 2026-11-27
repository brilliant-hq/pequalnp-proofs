import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_542

open Finset

/-- A cyclic position. -/
def loc (n : Nat) (hn : 0 < n) (k : Nat) : Fin n := ⟨k % n, Nat.mod_lt _ hn⟩

theorem loc_mod (n : Nat) (hn : 0 < n) (k a : Nat) :
    loc n hn (k + a % n) = loc n hn (k + a) := by
  unfold loc; ext; simp [Nat.add_mod_mod]

theorem loc_add_n (n : Nat) (hn : 0 < n) (k : Nat) : loc n hn (k + n) = loc n hn k := by
  unfold loc; ext; simp

theorem loc_lt (n : Nat) (hn : 0 < n) (k : Nat) (hk : k < n) : (loc n hn k).val = k := by
  simp [loc, Nat.mod_eq_of_lt hk]

theorem loc_inj (n : Nat) (hn : 0 < n) (k a b : Nat) (ha : a < n) (hb : b < n)
    (h : loc n hn (k + a) = loc n hn (k + b)) : a = b := by
  have h1 : (k + a) % n = (k + b) % n := congrArg Fin.val h
  have h2 : a % n = b % n := Nat.ModEq.add_left_cancel' k h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2

theorem shift (n : Nat) (hn : 0 < n) (k k' : Nat) :
    ∃ d < n, ∀ j, loc n hn (k' + j) = loc n hn (k + d + j) := by
  refine ⟨(k' + n - k % n) % n, Nat.mod_lt _ hn, fun j => ?_⟩
  have h1 := Nat.mod_add_div k n
  have h2 := Nat.mod_lt k hn
  have e : k + (k' + n - k % n) + j = k' + j + n * (k / n + 1) := by
    rw [Nat.mul_add, mul_one]
    generalize k % n = r at *
    generalize n * (k / n) = s at *
    omega
  have key : (k + (k' + n - k % n) % n + j) % n = (k' + j) % n := by
    rw [Nat.add_right_comm k, Nat.add_mod_mod, Nat.add_right_comm, e, Nat.add_mul_mod_self_left]
  unfold loc; ext; exact key.symm

/-- The rotation of offsets by a base. -/
def rot (n : Nat) (hn : 0 < n) (K : Nat) : Fin n → Fin n := fun o => loc n hn (K + o.val)

theorem rot_loc (n : Nat) (hn : 0 < n) (K o : Nat) :
    rot n hn K (loc n hn o) = loc n hn (K + o) := loc_mod n hn K o

theorem rot_bij (n : Nat) (hn : 0 < n) (K : Nat) : Function.Bijective (rot n hn K) := by
  apply Finite.injective_iff_bijective.mp
  intro a b hab
  exact Fin.ext (loc_inj n hn K a.val b.val a.isLt b.isLt hab)

/-- An all zero window of length t at an offset. -/
def Zr (n : Nat) (hn : 0 < n) (t : Nat) (u : Fin n → Bool) (d : Nat) : Prop :=
  ∀ j < t, u (loc n hn (d + j)) = false

def C0 (n : Nat) (hn : 0 < n) (t : Nat) (u : Fin n → Bool) : Prop :=
  (∀ o < t, u (loc n hn o) = false) ∧ u (loc n hn t) = true ∧ u (loc n hn (n - 1)) = true

def Uq (n : Nat) (hn : 0 < n) (t : Nat) (u : Fin n → Bool) : Prop :=
  ∀ d < n, Zr n hn t u d → d = 0

def G0 (n : Nat) (hn : 0 < n) (t : Nat) (u : Fin n → Bool) : Prop :=
  C0 n hn t u ∧ Uq n hn t u

/-- Free completions of the prescribed pattern. -/
def mk (n t : Nat) (y : Fin (n - t - 2) → Bool) : Fin n → Bool := fun q =>
  if q.val < t then false else if q.val = t then true else
    if h : q.val - t - 1 < n - t - 2 then y ⟨q.val - t - 1, h⟩ else true

/-- Overwrite a window of length t at offset d. -/
def ow (n t d : Nat) (p : (Fin n → Bool) × (Fin t → Bool)) : Fin n → Bool := fun q =>
  if h : d ≤ q.val ∧ q.val < d + t then p.2 ⟨q.val - d, by omega⟩ else p.1 q

theorem far (n : Nat) (hn : 0 < n) (t : Nat) (ht : t + 3 ≤ n) (u : Fin n → Bool)
    (hu : C0 n hn t u) (d : Nat) (hd0 : 0 < d) (hdn : d < n) (hz : Zr n hn t u d) : t < d ∧ d + t < n := by
  obtain ⟨_, hB, hC⟩ := hu
  constructor
  · by_contra hc
    have := hz (t - d) (by omega)
    rw [show d + (t - d) = t by omega, hB] at this
    exact absurd this (by decide)
  · by_contra hc
    have := hz (n - 1 - d) (by omega)
    rw [show d + (n - 1 - d) = n - 1 by omega, hC] at this
    exact absurd this (by decide)

open Classical in
theorem count0 (n : Nat) (hn : 0 < n) (t : Nat) (ht3 : t + 3 ≤ n) (h2 : 2 * n ≤ 2 ^ t) :
    2 ^ (n - t - 3) ≤ (univ.filter (fun u => G0 n hn t u)).card := by
  set C := (univ : Finset (Fin n → Bool)).filter (fun u => C0 n hn t u) with hCdef
  have hC : 2 ^ (n - t - 2) ≤ C.card := by
    have hmk : ∀ y, C0 n hn t (mk n t y) := by
      intro y
      refine ⟨fun o ho => ?_, ?_, ?_⟩
      · simp only [mk, loc_lt n hn o (by omega)]; rw [if_pos ho]
      · simp only [mk, loc_lt n hn t (by omega)]; simp
      · simp only [mk, loc_lt n hn (n - 1) (by omega)]
        rw [if_neg (by omega), if_neg (by omega), dif_neg (by omega)]
    have inj : Function.Injective (mk n t) := by
      intro y1 y2 hy
      funext j
      have key : ∀ y, mk n t y ⟨t + 1 + j.val, by omega⟩ = y j := by
        intro y
        simp only [mk]
        rw [if_neg (by omega), if_neg (by omega), dif_pos (by omega)]
        exact congrArg y (Fin.ext (by show t + 1 + j.val - t - 1 = j.val; omega))
      rw [← key y1, ← key y2, hy]
    calc 2 ^ (n - t - 2) = (univ : Finset (Fin (n - t - 2) → Bool)).card := by simp
      _ = (univ.image (mk n t)).card := (card_image_of_injective _ inj).symm
      _ ≤ C.card := by
        apply card_le_card
        intro u hu
        simp only [mem_image, mem_univ, true_and] at hu
        obtain ⟨y, rfl⟩ := hu
        simp [C, hmk]
  have hZ : ∀ d, t < d → d + t < n →
      (C.filter (fun u => Zr n hn t u d)).card * 2 ^ t ≤ C.card := by
    intro d htd hdn
    have e1 : ((C.filter (fun u => Zr n hn t u d)) ×ˢ
        (univ : Finset (Fin t → Bool))).card = (C.filter (fun u => Zr n hn t u d)).card * 2 ^ t := by
      simp [card_product]
    rw [← e1]
    apply card_le_card_of_injOn (ow n t d)
    · intro p hp
      simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, C, mem_univ, true_and] at hp
      obtain ⟨⟨⟨hA, hB, hCc⟩, _⟩, _⟩ := hp
      simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq, C]
      refine ⟨fun o ho => ?_, ?_, ?_⟩
      · simp only [ow, loc_lt n hn o (by omega)]
        rw [dif_neg (by omega)]
        exact hA o ho
      · simp only [ow, loc_lt n hn t (by omega)]
        rw [dif_neg (by omega)]
        exact hB
      · simp only [ow, loc_lt n hn (n - 1) (by omega)]
        rw [dif_neg (by omega)]
        exact hCc
    · intro p1 hp1 p2 hp2 he
      simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, C, mem_univ, true_and] at hp1 hp2
      have hb : p1.2 = p2.2 := by
        funext j
        have := congrFun he ⟨d + j.val, by omega⟩
        simp only [ow] at this
        rw [dif_pos (by first | (simp; done) | (simp; omega) | omega),
          dif_pos (by first | (simp; done) | (simp; omega) | omega)] at this
        have ej : (⟨d + j.val - d, by omega⟩ : Fin t) = j := Fin.ext (by simp)
        simpa [ej] using this
      have ha : p1.1 = p2.1 := by
        funext q
        by_cases hq : d ≤ q.val ∧ q.val < d + t
        · have eq : loc n hn (d + (q.val - d)) = q := by
            apply Fin.ext; rw [loc_lt n hn _ (by omega)]; omega
          have z1 := hp1.1.2 (q.val - d) (by omega)
          have z2 := hp2.1.2 (q.val - d) (by omega)
          rw [eq] at z1 z2
          rw [z1, z2]
        · have := congrFun he q
          simp only [ow] at this
          rwa [dif_neg hq, dif_neg hq] at this
      exact Prod.ext ha hb
  set D := (range n).filter (fun d => t < d ∧ d + t < n)
  set Bad := C.filter (fun u => ¬ Uq n hn t u)
  have hsub : Bad ⊆ D.biUnion (fun d => C.filter (fun u => Zr n hn t u d)) := by
    intro u hu
    obtain ⟨huC, hne⟩ := Finset.mem_filter.mp hu
    have hc : C0 n hn t u := (Finset.mem_filter.mp huC).2
    unfold Uq at hne
    push_neg at hne
    obtain ⟨d, hdn, hz, hd0⟩ := hne
    have := far n hn t ht3 u hc d (Nat.pos_of_ne_zero hd0) hdn hz
    rw [Finset.mem_biUnion]
    exact ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hdn, this⟩,
      Finset.mem_filter.mpr ⟨huC, hz⟩⟩
  have hbad : Bad.card * 2 ^ t ≤ n * C.card := by
    calc Bad.card * 2 ^ t
        ≤ (∑ d ∈ D, (C.filter (fun u => Zr n hn t u d)).card) * 2 ^ t :=
          Nat.mul_le_mul_right _ ((card_le_card hsub).trans card_biUnion_le)
      _ = ∑ d ∈ D, (C.filter (fun u => Zr n hn t u d)).card * 2 ^ t := Finset.sum_mul _ _ _
      _ ≤ ∑ d ∈ D, C.card := by
          apply sum_le_sum
          intro d hd
          simp only [D, mem_filter, mem_range] at hd
          exact hZ d hd.2.1 hd.2.2
      _ = D.card * C.card := by rw [sum_const, smul_eq_mul]
      _ ≤ n * C.card := by
          apply Nat.mul_le_mul_right
          exact (card_filter_le _ _).trans (by simp)
  have hpos : 0 < 2 ^ t := by positivity
  have h2bad : 2 * Bad.card ≤ C.card := by
    apply Nat.le_of_mul_le_mul_right _ hpos
    calc 2 * Bad.card * 2 ^ t = 2 * (Bad.card * 2 ^ t) := by ring
      _ ≤ 2 * (n * C.card) := Nat.mul_le_mul_left _ hbad
      _ = (2 * n) * C.card := by ring
      _ ≤ 2 ^ t * C.card := Nat.mul_le_mul_right _ h2
      _ = C.card * 2 ^ t := by ring
  have hsplit : (C.filter (fun u => Uq n hn t u)).card + Bad.card = C.card :=
    card_filter_add_card_filter_not _
  have hG : (C.filter (fun u => Uq n hn t u)).card ≤
      (univ.filter (fun u => G0 n hn t u)).card := by
    apply card_le_card
    intro u hu
    obtain ⟨huC, huq⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_filter.mpr ⟨mem_univ _, (Finset.mem_filter.mp huC).2, huq⟩
  have hp : 2 ^ (n - t - 2) = 2 * 2 ^ (n - t - 3) := by
    rw [show n - t - 2 = (n - t - 3) + 1 by omega, pow_succ]; ring
  omega

open Classical in
theorem card_rot (n : Nat) (σ : Fin n → Fin n) (hσ : Function.Bijective σ)
    (P : (Fin n → Bool) → Prop) :
    (univ.filter (fun x : Fin n → Bool => P (x ∘ σ))).card = (univ.filter P).card := by
  let e := Equiv.ofBijective σ hσ
  have h1 : ∀ q, e.symm (σ q) = q := fun q => e.symm_apply_apply q
  have h2 : ∀ q, σ (e.symm q) = q := fun q => e.apply_symm_apply q
  apply Finset.card_nbij' (fun x => x ∘ σ) (fun y => y ∘ e.symm)
  · intro x hx; simpa using hx
  · intro y hy
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy ⊢
    have : (y ∘ e.symm) ∘ σ = y := by funext q; simp [h1]
    rwa [this]
  · intro x _; funext q; simp [h2]
  · intro y _; funext q; simp [h1]

end PEqualNP.Outside.L_lib_542

open PEqualNP.Outside.L_lib_542 Finset in
theorem PEqualNP.Outside.L_lib_542 : ∀ (n h t : Nat) (hn : 0 < n), h ≤ t → t+3 ≤ n → 2*n ≤ 2^t →
  let Word := Fin n → Bool
  let loc := fun k : Nat => (⟨k%n, Nat.mod_lt _ hn⟩ : Fin n)
  ∀ sites : Finset (Fin n), ∃ (pool : Finset Word) (owner : ↥pool → ↥sites),
    (∀ i : ↥sites, 2^(n-t-3) ≤
      ((Finset.univ : Finset (↥pool)).filter (fun z => owner z = i)).card) ∧
    ∀ a b : ↥pool,
      (∀ j : Fin (n-h), a.val (loc ((owner a).val.val+j.val)) =
          b.val (loc ((owner a).val.val+j.val))) → a = b := by
  intro n h t hn hht ht3 h2
  intro Word locS sites
  classical
  let K : Fin n → Nat := fun i => i.val + n - t
  let Good : Fin n → Finset (Fin n → Bool) := fun i =>
    univ.filter (fun x => G0 n hn t (x ∘ rot n hn (K i)))
  have comp : ∀ (i : Fin n) (x : Fin n → Bool) (o : Nat),
      (x ∘ rot n hn (K i)) (loc n hn o) = x (loc n hn (K i + o)) := by
    intro i x o; simp only [Function.comp_apply, rot_loc]
  have gA : ∀ i x, x ∈ Good i → ∀ o < t, x (loc n hn (K i + o)) = false := by
    intro i x hx o ho
    simp only [Good, mem_filter, mem_univ, true_and] at hx
    rw [← comp i x o]; exact hx.1.1 o ho
  have gB : ∀ i x, x ∈ Good i → x (loc n hn (K i + t)) = true := by
    intro i x hx
    simp only [Good, mem_filter, mem_univ, true_and] at hx
    rw [← comp i x t]; exact hx.1.2.1
  have gC : ∀ i x, x ∈ Good i → x (loc n hn (K i + (n - 1))) = true := by
    intro i x hx
    simp only [Good, mem_filter, mem_univ, true_and] at hx
    rw [← comp i x (n - 1)]; exact hx.1.2.2
  have gD : ∀ i x, x ∈ Good i → ∀ d < n,
      (∀ j < t, x (loc n hn (K i + d + j)) = false) → d = 0 := by
    intro i x hx d hd hz
    simp only [Good, mem_filter, mem_univ, true_and] at hx
    apply hx.2 d hd
    intro j hj
    rw [comp, ← add_assoc]; exact hz j hj
  have runs : ∀ i j x, x ∈ Good j → ∃ d < n, ∀ o < t, x (loc n hn (K i + d + o)) = false := by
    intro i j x hx
    obtain ⟨d, hd, hs⟩ := shift n hn (K i) (K j)
    exact ⟨d, hd, fun o ho => by rw [← hs]; exact gA j x hx o ho⟩
  have disj : ∀ i j x, x ∈ Good i → x ∈ Good j → i = j := by
    intro i j x hi hj
    obtain ⟨d, hd, hs⟩ := shift n hn (K i) (K j)
    have hd0 : d = 0 := gD i x hi d hd (fun o ho => by rw [← hs]; exact gA j x hj o ho)
    have e := hs t
    rw [hd0, add_zero] at e
    simp only [K] at e
    rw [show j.val + n - t + t = j.val + n by omega, show i.val + n - t + t = i.val + n by omega,
      loc_add_n, loc_add_n] at e
    apply Fin.ext
    have := congrArg Fin.val e
    rw [loc_lt n hn _ j.isLt, loc_lt n hn _ i.isLt] at this
    exact this.symm
  have cnt : ∀ i, 2 ^ (n - t - 3) ≤ (Good i).card := by
    intro i
    have := card_rot n (rot n hn (K i)) (rot_bij n hn (K i)) (fun u => G0 n hn t u)
    simp only [Good]
    rw [this]
    exact count0 n hn t ht3 h2
  let pool : Finset (Fin n → Bool) := sites.biUnion Good
  have memp : ∀ x : ↥pool, ∃ i ∈ sites, x.val ∈ Good i := fun x => by
    exact Finset.mem_biUnion.mp x.property
  let owner : ↥pool → ↥sites := fun x => ⟨(memp x).choose, (memp x).choose_spec.1⟩
  have own : ∀ x : ↥pool, x.val ∈ Good (owner x).val := fun x => (memp x).choose_spec.2
  refine ⟨pool, owner, ?_, ?_⟩
  · intro i
    calc 2 ^ (n - t - 3) ≤ (Good i.val).card := cnt i.val
      _ = ((Good i.val).subtype (· ∈ pool)).card := by
          rw [card_subtype, filter_true_of_mem]
          intro x hx
          simp only [pool, mem_biUnion]
          exact ⟨i.val, i.property, hx⟩
      _ ≤ _ := by
          apply card_le_card
          intro z hz
          rw [mem_subtype] at hz
          simp only [mem_filter, mem_univ, true_and]
          apply Subtype.ext
          exact (disj _ _ z.val hz (own z)).symm
  · intro a b hab
    set i := (owner a).val with hi
    set x := a.val
    set y := b.val
    have hx := own a
    rw [← hi] at hx
    have hy := own b
    have win : ∀ o < n, (o < t - h ∨ t ≤ o) →
        x (loc n hn (K i + o)) = y (loc n hn (K i + o)) := by
      intro o ho hw
      rcases hw with hw | hw
      · have e : x (loc n hn (i.val + (o + n - t))) = y (loc n hn (i.val + (o + n - t))) :=
          hab ⟨o + n - t, by omega⟩
        simp only [K]
        rwa [show i.val + n - t + o = i.val + (o + n - t) by omega]
      · have e : x (loc n hn (i.val + (o - t))) = y (loc n hn (i.val + (o - t))) :=
          hab ⟨o - t, by omega⟩
        simp only [K]
        rw [show i.val + n - t + o = i.val + (o - t) + n by omega, loc_add_n]
        exact e
    apply Subtype.ext
    funext q
    by_contra hq
    obtain ⟨o, ho⟩ := (rot_bij n hn (K i)).2 q
    have hq' : x (loc n hn (K i + o.val)) ≠ y (loc n hn (K i + o.val)) := by
      rw [show loc n hn (K i + o.val) = q from ho]; exact hq
    have hlo : t - h ≤ o.val ∧ o.val < t := by
      by_contra hc
      exact hq' (win o.val o.isLt (by omega))
    have yo : y (loc n hn (K i + o.val)) = true := by
      have := gA i x hx o.val hlo.2
      rw [this] at hq'
      cases hyv : y (loc n hn (K i + o.val))
      · rw [hyv] at hq'; exact absurd rfl hq'
      · rfl
    obtain ⟨d, hdn, hz⟩ := runs i (owner b).val y hy
    by_cases hd0 : d = 0
    · have := hz o.val hlo.2
      rw [hd0, add_zero, yo] at this
      exact absurd this (by decide)
    by_cases hdt : d ≤ t
    · have := hz (t - d) (by omega)
      rw [add_assoc, show d + (t - d) = t by omega, ← win t (by omega) (Or.inr le_rfl),
        gB i x hx] at this
      exact absurd this (by decide)
    by_cases hdn' : n ≤ d + t
    · have := hz (n - 1 - d) (by omega)
      rw [add_assoc, show d + (n - 1 - d) = n - 1 by omega,
        ← win (n - 1) (by omega) (Or.inr (by omega)), gC i x hx] at this
      exact absurd this (by decide)
    apply hd0
    apply gD i x hx d hdn
    intro j hj
    rw [add_assoc, win (d + j) (by omega) (Or.inr (by omega)), ← add_assoc]
    exact hz j hj
