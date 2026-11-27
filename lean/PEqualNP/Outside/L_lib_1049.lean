import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_1049

open Polynomial

variable {n m : ℕ}

def rel (l r : Fin m → Fin n) (S : Finset (Fin m)) : Fin n → Fin n → Prop :=
  fun x z => ∃ e ∈ S, l e = x ∧ r e = z

noncomputable def comp (l r : Fin m → Fin n) (S : Finset (Fin m)) (v : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun y : Fin n =>
    @decide (Relation.EqvGen (rel l r S) v y) (Classical.propDecidable _) = true)

lemma mem_comp (l r : Fin m → Fin n) (S : Finset (Fin m)) (v y : Fin n) :
    y ∈ comp l r S v ↔ Relation.EqvGen (rel l r S) v y := by
  simp [comp]

lemma comp_eq_iff (l r : Fin m → Fin n) (S : Finset (Fin m)) (v w : Fin n) :
    comp l r S v = comp l r S w ↔ Relation.EqvGen (rel l r S) v w := by
  constructor
  · intro h
    have : w ∈ comp l r S w := (mem_comp l r S w w).2 (Relation.EqvGen.refl _)
    rw [← h, mem_comp] at this
    exact this
  · intro h
    ext y
    rw [mem_comp, mem_comp]
    constructor
    · intro h2; exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ h) h2
    · intro h2; exact Relation.EqvGen.trans _ _ _ h h2

lemma const_iff {β : Type} (l r : Fin m → Fin n) (S : Finset (Fin m)) (t : Fin n → β) :
    (∀ e ∈ S, t (l e) = t (r e)) ↔ ∀ v w, Relation.EqvGen (rel l r S) v w → t v = t w := by
  constructor
  · intro h v w hvw
    induction hvw with
    | rel x y hr => obtain ⟨e, he, rfl, rfl⟩ := hr; exact h e he
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  · intro h e he
    exact h _ _ (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)

abbrev T (l r : Fin m → Fin n) (S : Finset (Fin m)) : Type :=
  ↥(Finset.univ.image (comp l r S))

noncomputable def cls (l r : Fin m → Fin n) (S : Finset (Fin m)) (v : Fin n) : T l r S :=
  ⟨comp l r S v, Finset.mem_image_of_mem _ (Finset.mem_univ v)⟩

lemma reindex {β : Type} [Fintype β] {M : Type} [AddCommMonoid M]
    (l r : Fin m → Fin n) (S : Finset (Fin m)) (F : (Fin n → β) → M)
    [∀ t : Fin n → β, Decidable (∀ e ∈ S, t (l e) = t (r e))] :
    ∑ t : Fin n → β, (if (∀ e ∈ S, t (l e) = t (r e)) then F t else 0) =
      ∑ g : T l r S → β, F (fun v => g (cls l r S v)) := by
  classical
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun g _ => fun v => g (cls l r S v)) ?_ ?_ ?_ ?_
  · intro g _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro e he
    have : cls l r S (l e) = cls l r S (r e) := by
      apply Subtype.ext
      exact (comp_eq_iff l r S _ _).2 (Relation.EqvGen.rel _ _ ⟨e, he, rfl, rfl⟩)
    simp only [this]
  · intro g1 _ g2 _ h
    funext ⟨U, hU⟩
    obtain ⟨v, -, rfl⟩ := Finset.mem_image.1 hU
    exact congrFun h v
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    have hc := (const_iff l r S t).1 ht
    refine ⟨fun x => t (Classical.choose (Finset.mem_image.1 x.2)), Finset.mem_univ _, ?_⟩
    funext v
    have hx := Classical.choose_spec (Finset.mem_image.1 (cls l r S v).2)
    exact hc _ _ ((comp_eq_iff l r S _ _).1 hx.2)
  · intro g _; rfl

lemma sum_part (l r : Fin m → Fin n) (S : Finset (Fin m)) (g : Fin n → ℕ) :
    ∑ v, g v = ∑ U ∈ Finset.univ.image (comp l r S), ∑ v ∈ U, g v := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := comp l r S)
    (t := Finset.univ.image (comp l r S)) (fun v _ => Finset.mem_image_of_mem _ (Finset.mem_univ v))]
  refine Finset.sum_congr rfl (fun U hU => ?_)
  obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hU
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext v
  rw [Finset.mem_filter, mem_comp, comp_eq_iff]
  simp only [Finset.mem_univ, true_and]
  exact ⟨fun h => Relation.EqvGen.symm _ _ h, fun h => Relation.EqvGen.symm _ _ h⟩

def phase (l r : Fin m → Fin n) (sign : Fin m → Bool) (S : Finset (Fin m))
    (s : Fin n → Bool) : Prop :=
  ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e

def vc (target : Fin n → Bool) (pin : Fin n → ℕ) (U : Finset (Fin n)) (s : Fin n → Bool) : ℕ :=
  (U.filter (fun v => s v ≠ target v)).sum pin

lemma xor4 : ∀ a b c d sg : Bool, xor a b ≠ sg → (xor (xor a c) (xor b d) ≠ sg ↔ c = d) := by
  decide

lemma phase_shift (l r : Fin m → Fin n) (sign : Fin m → Bool) (S : Finset (Fin m))
    (s0 : Fin n → Bool) (h0 : phase l r sign S s0) (t : Fin n → Bool) :
    phase l r sign S (fun v => xor (s0 v) (t v)) ↔ ∀ e ∈ S, t (l e) = t (r e) := by
  unfold phase
  exact forall₂_congr (fun e he => xor4 _ _ _ _ _ (h0 e he))

lemma vc_univ (l r : Fin m → Fin n) (S : Finset (Fin m)) (target : Fin n → Bool)
    (pin : Fin n → ℕ) (s : Fin n → Bool) :
    vc target pin Finset.univ s = ∑ U ∈ Finset.univ.image (comp l r S), vc target pin U s := by
  unfold vc
  simp only [Finset.sum_filter]
  exact sum_part l r S (fun v => if s v ≠ target v then pin v else 0)

lemma vc_flip (l r : Fin m → Fin n) (S : Finset (Fin m)) (target : Fin n → Bool)
    (pin : Fin n → ℕ) (s0 : Fin n → Bool) (g : T l r S → Bool) (U : T l r S) :
    vc target pin U.1 (fun v => xor (s0 v) (g (cls l r S v))) =
      vc target pin U.1 (if g U then fun v => !(s0 v) else s0) := by
  obtain ⟨U, hU⟩ := U
  obtain ⟨w, -, hw⟩ := Finset.mem_image.1 hU
  unfold vc
  congr 1
  apply Finset.filter_congr
  intro v hv
  have hc : cls l r S v = ⟨U, hU⟩ := by
    apply Subtype.ext
    subst hw
    exact (comp_eq_iff l r S _ _).2 (Relation.EqvGen.symm _ _ ((mem_comp l r S w v).1 hv))
  simp only [hc]
  cases hb : g ⟨U, hU⟩ <;> simp

open Classical in
lemma sum_s (l r : Fin m → Fin n) (sign : Fin m → Bool) (S : Finset (Fin m))
    (target : Fin n → Bool) (pin : Fin n → ℕ) (s0 : Fin n → Bool) (h0 : phase l r sign S s0) :
    ∑ s : Fin n → Bool, (X : ℤ[X]) ^ (vc target pin Finset.univ s) *
        (if phase l r sign S s then (1 : ℤ[X]) else 0) =
      ∏ U ∈ Finset.univ.image (comp l r S),
        ((X : ℤ[X]) ^ vc target pin U s0 + (X : ℤ[X]) ^ vc target pin U (fun v => !(s0 v))) := by
  classical
  let e : (Fin n → Bool) ≃ (Fin n → Bool) :=
    ⟨fun t v => xor (s0 v) (t v), fun t v => xor (s0 v) (t v),
      fun t => by funext v; simp, fun t => by funext v; simp⟩
  rw [← Equiv.sum_comp e]
  have hterm : ∀ t : Fin n → Bool,
      (X : ℤ[X]) ^ (vc target pin Finset.univ (e t)) *
        (if phase l r sign S (e t) then (1 : ℤ[X]) else 0) =
      if (∀ k ∈ S, t (l k) = t (r k)) then
        (X : ℤ[X]) ^ (vc target pin Finset.univ (fun v => xor (s0 v) (t v))) else 0 := by
    intro t
    have := phase_shift l r sign S s0 h0 t
    have he : e t = fun v => xor (s0 v) (t v) := rfl
    rw [he]
    by_cases ht : ∀ k ∈ S, t (l k) = t (r k)
    · rw [if_pos ht, if_pos (this.2 ht)]; simp
    · rw [if_neg ht, if_neg (fun h => ht (this.1 h))]; simp
  simp only [hterm]
  rw [reindex l r S (fun t => (X : ℤ[X]) ^ (vc target pin Finset.univ (fun v => xor (s0 v) (t v))))]
  have h2 : ∀ g : T l r S → Bool,
      (X : ℤ[X]) ^ (vc target pin Finset.univ (fun v => xor (s0 v) (g (cls l r S v)))) =
      ∏ x : T l r S, (X : ℤ[X]) ^ (vc target pin x.1 (if g x then fun v => !(s0 v) else s0)) := by
    intro g
    rw [vc_univ l r S, ← Finset.sum_coe_sort,
      Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (T l r S)) _ (X : ℤ[X])]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => vc_flip l r S target pin s0 g x)
  simp only [h2]
  have h3 := Finset.prod_univ_sum (fun _ : T l r S => (Finset.univ : Finset Bool))
    (fun (x : T l r S) (b : Bool) =>
      (X : ℤ[X]) ^ (vc target pin x.1 (if b then fun v => !(s0 v) else s0)))
  rw [Fintype.piFinset_univ] at h3
  rw [← h3, ← Finset.prod_coe_sort (Finset.univ.image (comp l r S))]
  refine Finset.prod_congr rfl (fun x _ => ?_)
  rw [Fintype.sum_bool]
  simp [add_comm]

open Classical in
lemma sum_c (l r : Fin m → Fin n) (q : ℕ) (S : Finset (Fin m)) :
    ∑ c : Fin n → Fin q, (if (∀ k ∈ S, c (l k) = c (r k)) then (1 : ℤ[X]) else 0) =
      ∏ _U ∈ Finset.univ.image (comp l r S), (C (q : ℤ)) := by
  classical
  have := reindex l r S (β := Fin q) (fun _ => (1 : ℤ[X]))
  rw [this]
  simp [Finset.prod_const]

open Classical in
lemma per_S_pos (l r : Fin m → Fin n) (sign : Fin m → Bool) (q : ℕ) (S : Finset (Fin m))
    (target : Fin n → Bool) (pin : Fin n → ℕ) (s0 : Fin n → Bool) (h0 : phase l r sign S s0) :
    ∑ c : Fin n → Fin q, ∑ s : Fin n → Bool, (X : ℤ[X]) ^ (vc target pin Finset.univ s) *
        (if (∀ k ∈ S, c (l k) = c (r k)) ∧ phase l r sign S s then (1 : ℤ[X]) else 0) =
      ∏ U ∈ Finset.univ.image (comp l r S),
        (C (q : ℤ) * ((X : ℤ[X]) ^ vc target pin U s0 +
          (X : ℤ[X]) ^ vc target pin U (fun v => !(s0 v)))) := by
  have hsplit : ∀ (c : Fin n → Fin q) (s : Fin n → Bool),
      (X : ℤ[X]) ^ (vc target pin Finset.univ s) *
        (if (∀ k ∈ S, c (l k) = c (r k)) ∧ phase l r sign S s then (1 : ℤ[X]) else 0) =
      (if (∀ k ∈ S, c (l k) = c (r k)) then (1 : ℤ[X]) else 0) *
        ((X : ℤ[X]) ^ (vc target pin Finset.univ s) *
          (if phase l r sign S s then (1 : ℤ[X]) else 0)) := by
    intro c s
    by_cases h1 : ∀ k ∈ S, c (l k) = c (r k) <;> by_cases h2 : phase l r sign S s <;> simp [h1, h2]
  simp only [hsplit]
  rw [← Finset.sum_mul_sum, sum_c, sum_s l r sign S target pin s0 h0, Finset.prod_mul_distrib]

open Classical in
lemma per_S_neg (l r : Fin m → Fin n) (sign : Fin m → Bool) (q : ℕ) (S : Finset (Fin m))
    (target : Fin n → Bool) (pin : Fin n → ℕ) (h : ¬ ∃ s, phase l r sign S s) :
    ∑ c : Fin n → Fin q, ∑ s : Fin n → Bool, (X : ℤ[X]) ^ (vc target pin Finset.univ s) *
        (if (∀ k ∈ S, c (l k) = c (r k)) ∧ phase l r sign S s then (1 : ℤ[X]) else 0) = 0 := by
  refine Finset.sum_eq_zero (fun c _ => Finset.sum_eq_zero (fun s _ => ?_))
  have : ¬ phase l r sign S s := fun hs => h ⟨s, hs⟩
  simp [this]

open Classical in
lemma expand (l r : Fin m → Fin n) (sign : Fin m → Bool) (q : ℕ) (wt : Fin m → ℕ)
    (target : Fin n → Bool) (pin : Fin n → ℕ) :
    ∑ c : Fin n → Fin q, ∑ s : Fin n → Bool, (X : ℤ[X]) ^
      (vc target pin Finset.univ s + (Finset.univ.filter (fun e : Fin m =>
        c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt) =
    ∑ S : Finset (Fin m), (∑ c : Fin n → Fin q, ∑ s : Fin n → Bool,
      (X : ℤ[X]) ^ (vc target pin Finset.univ s) *
        (if (∀ k ∈ S, c (l k) = c (r k)) ∧ phase l r sign S s then (1 : ℤ[X]) else 0)) *
      ∏ e ∈ S, ((X : ℤ[X]) ^ wt e - 1) := by
  have step : ∀ (c : Fin n → Fin q) (s : Fin n → Bool),
      (X : ℤ[X]) ^ (vc target pin Finset.univ s + (Finset.univ.filter (fun e : Fin m =>
        c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt) =
      ∑ S : Finset (Fin m), (X : ℤ[X]) ^ (vc target pin Finset.univ s) *
        ((if (∀ k ∈ S, c (l k) = c (r k)) ∧ phase l r sign S s then (1 : ℤ[X]) else 0) *
          ∏ e ∈ S, ((X : ℤ[X]) ^ wt e - 1)) := by
    intro c s
    rw [pow_add, ← Finset.prod_pow_eq_pow_sum, Finset.prod_filter]
    have h1 : ∀ e : Fin m, (if c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e
        then (X : ℤ[X]) ^ wt e else 1) =
        1 + (if c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e
          then (X : ℤ[X]) ^ wt e - 1 else 0) := by
      intro e; split_ifs <;> ring
    simp only [h1]
    rw [Finset.prod_one_add, ← Finset.powerset_univ, ← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [Finset.prod_ite_zero]
    have hiff : (∀ e ∈ S, c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e) ↔
        ((∀ k ∈ S, c (l k) = c (r k)) ∧ phase l r sign S s) :=
      ⟨fun h => ⟨fun e he => (h e he).1, fun e he => (h e he).2⟩,
        fun h e he => ⟨h.1 e he, h.2 e he⟩⟩
    by_cases hh : (∀ k ∈ S, c (l k) = c (r k)) ∧ phase l r sign S s
    · rw [if_pos (hiff.2 hh), if_pos hh, one_mul]
    · rw [if_neg (fun h' => hh (hiff.1 h')), if_neg hh, zero_mul]
  simp only [step]
  rw [Finset.sum_congr rfl (fun c _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  ring

end PEqualNP.Outside.L_lib_1049

theorem PEqualNP.Outside.L_lib_1049 : ∀ (n m q : ℕ) (l r : Fin m → Fin n) (sign : Fin m → Bool)
  (wt : Fin m → ℕ) (target : Fin n → Bool) (pin : Fin n → ℕ),
  let comp := fun (S : Finset (Fin m)) (v : Fin n) => Finset.univ.filter (fun y : Fin n =>
    @decide (Relation.EqvGen (fun x z : Fin n => ∃ e ∈ S, l e = x ∧ r e = z) v y)
      (Classical.propDecidable _) = true)
  let phase := fun (S : Finset (Fin m)) (s : Fin n → Bool) =>
    ∀ e ∈ S, xor (s (l e)) (s (r e)) ≠ sign e
  let X : Polynomial ℤ := Polynomial.X
  let vertexCost := fun (U : Finset (Fin n)) (s : Fin n → Bool) =>
    (U.filter (fun v => s v ≠ target v)).sum pin
  let fieldFactor := fun (S : Finset (Fin m)) =>
    if h : ∃ s : Fin n → Bool, phase S s then
      let s := Classical.choose h
      ∏ U ∈ Finset.univ.image (comp S),
        (Polynomial.C (q : ℤ)) * (X ^ vertexCost U s + X ^ vertexCost U (fun v => !(s v)))
    else 0
  let Z := ∑ S : Finset (Fin m), fieldFactor S * ∏ e ∈ S, (X ^ wt e - 1)
  let loss := fun (c : Fin n → Fin q) (s : Fin n → Bool) =>
    vertexCost Finset.univ s + (Finset.univ.filter (fun e : Fin m =>
      c (l e) = c (r e) ∧ xor (s (l e)) (s (r e)) ≠ sign e)).sum wt
  Z = ∑ c : Fin n → Fin q, ∑ s : Fin n → Bool, X ^ loss c s := by
  intro n m q l r sign wt target pin cmp ph X' vcost ff Z loss
  have hE := PEqualNP.Outside.L_lib_1049.expand l r sign q wt target pin
  refine Eq.trans ?_ hE.symm
  refine Finset.sum_congr rfl (fun S _ => ?_)
  congr 1
  by_cases h : ∃ s : Fin n → Bool, ph S s
  · have h' : ∃ s : Fin n → Bool, PEqualNP.Outside.L_lib_1049.phase l r sign S s := h
    have hff : ff S = _ := dif_pos h
    rw [hff]
    exact (PEqualNP.Outside.L_lib_1049.per_S_pos l r sign q S target pin
      (Classical.choose h) (Classical.choose_spec h)).symm
  · have h' : ¬ ∃ s : Fin n → Bool, PEqualNP.Outside.L_lib_1049.phase l r sign S s := h
    have hff : ff S = 0 := dif_neg h
    rw [hff]
    exact (PEqualNP.Outside.L_lib_1049.per_S_neg l r sign q S target pin h').symm
