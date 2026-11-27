import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_591

open Finset

variable {K : Type} [Field K] {q : ℕ}

def E (p : Equiv.Perm (Fin q)) : Matrix (Fin q) (Fin q) K := fun i k => if p i = k then 1 else 0

def frob (X Y : Matrix (Fin q) (Fin q) K) : K := ∑ i, ∑ k, X i k * Y i k

def op (u v : Fin q → K) : Matrix (Fin q) (Fin q) K := fun i k => u i * v k

def ev (x : Fin q) : Fin q → K := fun i => if i = x then 1 else 0

def dot (u v : Fin q → K) : K := ∑ i, u i * v i

lemma fixed_eq (p r : Equiv.Perm (Fin q)) :
    (((univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card : K) = frob (E p) (E (K := K) r⁻¹) := by
  unfold frob E
  rw [Finset.card_filter]
  push_cast
  refine sum_congr rfl fun i _ => ?_
  have : r (p i) = i ↔ p i = r⁻¹ i := Equiv.Perm.eq_inv_iff_eq.symm
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, this]

lemma frob_add_left (X X' Y : Matrix (Fin q) (Fin q) K) : frob (X + X') Y = frob X Y + frob X' Y := by
  simp [frob, add_mul, Finset.sum_add_distrib]
lemma frob_sub_left (X X' Y : Matrix (Fin q) (Fin q) K) : frob (X - X') Y = frob X Y - frob X' Y := by
  simp [frob, sub_mul, Finset.sum_sub_distrib]
lemma frob_smul_left (c : K) (X Y : Matrix (Fin q) (Fin q) K) : frob (c • X) Y = c * frob X Y := by
  simp [frob, Finset.mul_sum, mul_assoc]
lemma frob_comm (X Y : Matrix (Fin q) (Fin q) K) : frob X Y = frob Y X := by
  simp [frob, mul_comm]
lemma frob_sum_left {ι : Type} (s : Finset ι) (X : ι → Matrix (Fin q) (Fin q) K) (Y : Matrix (Fin q) (Fin q) K) :
    frob (∑ a ∈ s, X a) Y = ∑ a ∈ s, frob (X a) Y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frob]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, frob_add_left, ih]
lemma frob_sub_right (X Y Y' : Matrix (Fin q) (Fin q) K) : frob X (Y - Y') = frob X Y - frob X Y' := by
  rw [frob_comm, frob_sub_left, frob_comm, frob_comm Y']
lemma frob_smul_right (c : K) (X Y : Matrix (Fin q) (Fin q) K) : frob X (c • Y) = c * frob X Y := by
  rw [frob_comm, frob_smul_left, frob_comm]
lemma frob_sum_right {ι : Type} (s : Finset ι) (X : Matrix (Fin q) (Fin q) K) (Y : ι → Matrix (Fin q) (Fin q) K) :
    frob X (∑ a ∈ s, Y a) = ∑ a ∈ s, frob X (Y a) := by
  rw [frob_comm, frob_sum_left]; simp [frob_comm]

lemma frob_op_op (u v u' v' : Fin q → K) : frob (op u v) (op u' v') = dot u u' * dot v v' := by
  simp only [frob, op, dot, Finset.sum_mul_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
  ring

lemma frob_op_E (u v : Fin q → K) (r : Equiv.Perm (Fin q)) : frob (op u v) (E r) = ∑ i, u i * v (r i) := by
  simp [frob, op, E]

lemma frob_E_one : frob (E (K := K) (1 : Equiv.Perm (Fin q))) (E 1) = q := by
  have h := fixed_eq (K := K) (1 : Equiv.Perm (Fin q)) 1
  rw [inv_one] at h
  rw [← h]
  simp

lemma frob_sum_E {α β : Equiv.Perm (Fin q) → K} :
    frob (∑ p, α p • E p) (∑ ρ, β ρ • E ρ) = ∑ p, ∑ ρ, α p * β ρ * frob (E (K := K) p) (E ρ) := by
  rw [frob_sum_left]
  refine sum_congr rfl fun p _ => ?_
  rw [frob_smul_left, frob_sum_right, Finset.mul_sum]
  refine sum_congr rfl fun ρ _ => ?_
  rw [frob_smul_right]; ring

lemma lb {d : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Equiv.Perm (Fin q) → Fin d → K)
    (hAB : ∀ p r : Equiv.Perm (Fin q),
      (((univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card : K) = ∑ j, A p j * B r j)
    (X Y : ι → Matrix (Fin q) (Fin q) K)
    (hX : ∀ a, X a ∈ Submodule.span K (Set.range (E (K := K) (q := q))))
    (hY : ∀ a, Y a ∈ Submodule.span K (Set.range (E (K := K) (q := q))))
    (D : ι → K) (hD : ∀ a, D a ≠ 0)
    (hXY : ∀ a c, frob (X a) (Y c) = if a = c then D a else 0) :
    Fintype.card ι ≤ d := by
  choose α hα using fun a => (Submodule.mem_span_range_iff_exists_fun K).1 (hX a)
  choose β hβ using fun a => (Submodule.mem_span_range_iff_exists_fun K).1 (hY a)
  let u : ι → Fin d → K := fun a => ∑ p, α a p • A p
  let w : ι → Fin d → K := fun c => ∑ ρ, β c ρ • B ρ⁻¹
  have key : ∀ a c, ∑ j, u a j * w c j = frob (X a) (Y c) := by
    intro a c
    have h1 : ∀ p ρ : Equiv.Perm (Fin q), frob (E (K := K) p) (E ρ) = ∑ j, A p j * B ρ⁻¹ j := by
      intro p ρ
      have := hAB p ρ⁻¹
      rwa [fixed_eq, inv_inv] at this
    rw [← hα a, ← hβ c, frob_sum_E]
    simp only [h1, u, w, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => arg 2; ext j; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact sum_congr rfl fun ρ _ => sum_congr rfl fun j _ => by ring
  have hli : LinearIndependent K u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg c
    have h2 : ∑ a, g a * (∑ j, u a j * w c j) = 0 := by
      have := congrArg (fun v => ∑ j, v j * w c j) hg
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, zero_mul,
        Finset.sum_const_zero, Finset.sum_mul] at this
      rw [← this, Finset.sum_comm]
      refine sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun j _ => ?_
      ring
    simp only [key, hXY, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h2
    exact (mul_eq_zero.mp h2).resolve_right (hD c)
  have := hli.fintype_card_le_finrank
  simpa using this

def N : Submodule K (Matrix (Fin q) (Fin q) K) where
  carrier := {G | ∀ r : Equiv.Perm (Fin q), frob G (E r) = 0}
  add_mem' := by
    intro a b ha hb r
    simp only [Set.mem_ofPred_eq] at *
    rw [frob_add_left, ha, hb, add_zero]
  zero_mem' := by
    intro r
    simp [frob]
  smul_mem' := by
    intro c a ha r
    simp only [Set.mem_ofPred_eq] at *
    rw [frob_smul_left, ha, mul_zero]

lemma ub {ι : Type} [Fintype ι] (F : ι → Matrix (Fin q) (Fin q) K)
    (h : ∀ p : Equiv.Perm (Fin q), E p ∈ Submodule.span K (Set.range F) ⊔ N) :
    ∃ A B : Equiv.Perm (Fin q) → ι → K, ∀ p r : Equiv.Perm (Fin q),
      (((univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card : K) = ∑ a, A p a * B r a := by
  have h' : ∀ p : Equiv.Perm (Fin q), ∃ c : ι → K, ∃ G ∈ (N : Submodule K _),
      (E p : Matrix (Fin q) (Fin q) K) = ∑ a, c a • F a + G := by
    intro p
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (h p)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hy
    exact ⟨c, z, hz, by rw [hc, hyz]⟩
  choose c G hG hE using h'
  refine ⟨c, fun r a => frob (F a) (E r⁻¹), fun p r => ?_⟩
  rw [fixed_eq, hE p, frob_add_left, frob_sum_left, hG p r⁻¹, add_zero]
  refine sum_congr rfl fun a _ => ?_
  rw [frob_smul_left]

lemma pad {ι : Type} [Fintype ι] {d : ℕ} (hd : Fintype.card ι ≤ d)
    (M : Equiv.Perm (Fin q) → Equiv.Perm (Fin q) → K)
    (h : ∃ A B : Equiv.Perm (Fin q) → ι → K, ∀ p r, M p r = ∑ a, A p a * B r a) :
    ∃ A B : Equiv.Perm (Fin q) → Fin d → K, ∀ p r, M p r = ∑ j, A p j * B r j := by
  classical
  obtain ⟨A, B, hAB⟩ := h
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin d) := Function.Embedding.nonempty_of_card_le (by simpa using hd)
  refine ⟨fun p => Function.extend e (A p) 0, fun r => Function.extend e (B r) 0, fun p r => ?_⟩
  rw [hAB]
  symm
  rw [← Finset.sum_subset (Finset.subset_univ (univ.map e)), Finset.sum_map]
  · simp [e.injective.extend_apply]
  · intro j _ hj
    have : ¬ ∃ a, e a = j := by simpa using hj
    simp [Function.extend_apply' _ _ _ this]

lemma op_sub_sub (u u' v v' : Fin q → K) :
    op (u - u') (v - v') = op u v - op u v' - op u' v + op u' v' := by
  ext i k; simp [op]; ring

lemma op_zero_left (v : Fin q → K) : op 0 v = 0 := by ext i k; simp [op]
lemma op_zero_right (u : Fin q → K) : op u 0 = 0 := by ext i k; simp [op]

lemma op_sum {ι κ : Type} [Fintype ι] [Fintype κ] (c : ι → K) (d : κ → K) (u : ι → Fin q → K)
    (v : κ → Fin q → K) :
    op (∑ x, c x • u x) (∑ y, d y • v y) = ∑ x, ∑ y, (c x * d y) • op (u x) (v y) := by
  ext i k
  simp only [op, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_apply, Matrix.smul_apply,
    Finset.sum_mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

lemma E_swap (f : Equiv.Perm (Fin q)) {x y : Fin q} (hxy : x ≠ y) :
    (E (Equiv.swap x y * f) : Matrix (Fin q) (Fin q) K) =
      E f - op (ev (f⁻¹ x) - ev (f⁻¹ y)) (ev x - ev y) := by
  ext i k
  simp only [E, op, ev, Equiv.Perm.mul_apply, Matrix.sub_apply, Pi.sub_apply]
  have e1 : (i = f⁻¹ x) ↔ f i = x := Equiv.Perm.eq_inv_iff_eq
  have e2 : (i = f⁻¹ y) ↔ f i = y := Equiv.Perm.eq_inv_iff_eq
  simp only [e1, e2]
  by_cases h1 : f i = x
  · simp only [h1, Equiv.swap_apply_left]
    have : x ≠ y := hxy
    by_cases hk1 : k = x <;> by_cases hk2 : k = y <;> simp_all [eq_comm]
  by_cases h2 : f i = y
  · simp only [h2, Equiv.swap_apply_right]
    by_cases hk1 : k = x <;> by_cases hk2 : k = y <;> simp_all [eq_comm]
  simp only [Equiv.swap_apply_of_ne_of_ne h1 h2]
  simp [h1, h2]

lemma rect_mem (a b c d : Fin q) :
    op (ev a - ev b) (ev c - ev d) ∈ Submodule.span K (Set.range (E (K := K) (q := q))) := by
  by_cases hab : a = b
  · subst hab; simp [op_zero_left]
  by_cases hcd : c = d
  · subst hcd; simp [op_zero_right]
  set f : Equiv.Perm (Fin q) := Equiv.swap (Equiv.swap a c b) d * Equiv.swap a c with hf
  have hfa : f a = c := by
    have h1 : Equiv.swap a c b ≠ c := by
      intro h
      have : Equiv.swap a c b = Equiv.swap a c a := by rw [h]; simp
      exact hab (Equiv.injective _ this).symm
    simp [hf, Equiv.swap_apply_of_ne_of_ne (Ne.symm h1) hcd]
  have hfb : f b = d := by simp [hf]
  have ha : f⁻¹ c = a := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hfa.symm
  have hb : f⁻¹ d = b := by rw [Equiv.Perm.inv_eq_iff_eq]; exact hfb.symm
  have := E_swap (K := K) f hcd
  rw [ha, hb] at this
  have h2 : op (ev a - ev b) (ev c - ev d) = (E f : Matrix (Fin q) (Fin q) K) - E (Equiv.swap c d * f) := by
    rw [this]; abel
  rw [h2]
  exact sub_mem (Submodule.subset_span ⟨f, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)

lemma zs_expand (o : Fin q) (u : Fin q → K) (hu : ∑ i, u i = 0) :
    u = ∑ x, u x • (ev x - ev o) := by
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hu, zero_mul, sub_zero]
  simp [ev]

lemma op_mem (o : Fin q) (u v : Fin q → K) (hu : ∑ i, u i = 0) (hv : ∑ i, v i = 0) :
    op u v ∈ Submodule.span K (Set.range (E (K := K) (q := q))) := by
  rw [zs_expand o u hu, zs_expand o v hv, op_sum]
  exact Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun y _ =>
    Submodule.smul_mem _ _ (rect_mem _ _ _ _)

lemma frob_op_one (u v : Fin q → K) : frob (op u v) (E 1) = dot u v := by
  rw [frob_op_E]; simp [dot]

lemma lb2 {d m : ℕ} (A B : Equiv.Perm (Fin q) → Fin d → K)
    (hAB : ∀ p r : Equiv.Perm (Fin q),
      (((univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card : K) = ∑ j, A p j * B r j)
    (o : Fin q) (f g : Fin m → Fin q → K) (hf : ∀ j, ∑ i, f j i = 0) (hg : ∀ j, ∑ i, g j i = 0)
    (hfg : ∀ j l, dot (f j) (g l) = if j = l then 1 else 0) :
    m * m ≤ d ∧ ((q : K) - ∑ j, ∑ l, dot (f j) (f l) * dot (g j) (g l) ≠ 0 → m * m + 1 ≤ d) := by
  classical
  have hpair : ∀ a c : Fin m × Fin m,
      frob (op (f a.1) (f a.2)) (op (g c.1) (g c.2)) = if a = c then 1 else 0 := by
    rintro ⟨a1, a2⟩ ⟨c1, c2⟩
    rw [frob_op_op, hfg, hfg]
    simp only [Prod.mk.injEq]
    split_ifs <;> simp_all
  have hspan : ∀ a : Fin m × Fin m, ∀ (h : Fin m → Fin q → K), (∀ j, ∑ i, h j i = 0) →
      op (h a.1) (h a.2) ∈ Submodule.span K (Set.range (E (K := K) (q := q))) :=
    fun a h hh => op_mem o _ _ (hh _) (hh _)
  constructor
  · have := lb A B hAB (fun a : Fin m × Fin m => op (f a.1) (f a.2))
      (fun a => op (g a.1) (g a.2)) (fun a => hspan a f hf) (fun a => hspan a g hg)
      (fun _ => 1) (fun _ => one_ne_zero) (fun a c => hpair a c)
    simpa using this
  · intro hz
    let X : (Fin m × Fin m) ⊕ Unit → Matrix (Fin q) (Fin q) K := fun a => match a with
      | Sum.inl a => op (f a.1) (f a.2)
      | Sum.inr _ => E 1 - ∑ c : Fin m × Fin m, dot (g c.1) (g c.2) • op (f c.1) (f c.2)
    let Y : (Fin m × Fin m) ⊕ Unit → Matrix (Fin q) (Fin q) K := fun a => match a with
      | Sum.inl a => op (g a.1) (g a.2)
      | Sum.inr _ => E 1 - ∑ c : Fin m × Fin m, dot (f c.1) (f c.2) • op (g c.1) (g c.2)
    let D : (Fin m × Fin m) ⊕ Unit → K := fun a => match a with
      | Sum.inl _ => 1
      | Sum.inr _ => (q : K) - ∑ j, ∑ l, dot (f j) (f l) * dot (g j) (g l)
    have one_mem : (E 1 : Matrix (Fin q) (Fin q) K) ∈ Submodule.span K (Set.range (E (K := K) (q := q))) :=
      Submodule.subset_span ⟨1, rfl⟩
    have hX : ∀ a, X a ∈ Submodule.span K (Set.range (E (K := K) (q := q))) := by
      rintro (a | _)
      · exact hspan a f hf
      · exact sub_mem one_mem (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hspan c f hf))
    have hY : ∀ a, Y a ∈ Submodule.span K (Set.range (E (K := K) (q := q))) := by
      rintro (a | _)
      · exact hspan a g hg
      · exact sub_mem one_mem (Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hspan c g hg))
    have hD : ∀ a, D a ≠ 0 := by
      rintro (a | _)
      · exact one_ne_zero
      · exact hz
    have h1 : ∀ a : Fin m × Fin m, frob (op (f a.1) (f a.2)) (Y (Sum.inr ())) = 0 := by
      intro a
      simp only [Y, frob_sub_right, frob_sum_right, frob_smul_right, frob_op_one, hpair, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true, sub_self]
    have h2 : ∀ c : Fin m × Fin m, frob (X (Sum.inr ())) (op (g c.1) (g c.2)) = 0 := by
      intro c
      simp only [X, frob_sub_left, frob_sum_left, frob_smul_left, hpair, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      rw [frob_comm, frob_op_one, sub_self]
    have h3 : frob (X (Sum.inr ())) (Y (Sum.inr ())) = D (Sum.inr ()) := by
      simp only [X, frob_sub_left, frob_sum_left, frob_smul_left, h1, mul_zero, Finset.sum_const_zero,
        sub_zero]
      simp only [Y, frob_sub_right, frob_sum_right, frob_smul_right, frob_E_one, D]
      congr 1
      rw [Fintype.sum_prod_type]
      refine sum_congr rfl fun j _ => sum_congr rfl fun l _ => ?_
      rw [frob_comm, frob_op_one]
    have := lb A B hAB X Y hX hY D hD (by
      rintro (a | ⟨⟩) (c | ⟨⟩)
      · simp only [X, Y, D, hpair, Sum.inl.injEq]
      · rw [ite_eq_right (by simp)]; exact h1 a
      · rw [ite_eq_right (by simp)]; exact h2 c
      · rw [ite_eq_left rfl]; exact h3)
    simpa using this

lemma ub_swap (L : Submodule K (Matrix (Fin q) (Fin q) K)) (h1 : (E 1 : Matrix (Fin q) (Fin q) K) ∈ L)
    (hr : ∀ a b c d : Fin q, op (ev a - ev b) (ev c - ev d) ∈ L) (p : Equiv.Perm (Fin q)) :
    (E p : Matrix (Fin q) (Fin q) K) ∈ L := by
  induction p using Equiv.Perm.swap_induction_on with
  | one => exact h1
  | swap_mul f x y hxy ih =>
    rw [E_swap (K := K) f hxy]
    exact sub_mem ih (hr _ _ _ _)

lemma rect_of_phi (L : Submodule K (Matrix (Fin q) (Fin q) K)) (o : Fin q)
    (hφ : ∀ x y : Fin q, op (ev x - ev o) (ev y - ev o) ∈ L) (a b c d : Fin q) :
    op (ev a - ev b) (ev c - ev d) ∈ L := by
  have e : (op (ev a - ev b) (ev c - ev d) : Matrix (Fin q) (Fin q) K) = op ((ev a - ev o) - (ev b - ev o)) ((ev c - ev o) - (ev d - ev o)) := by
    congr 1 <;> abel
  rw [e, op_sub_sub]
  exact add_mem (sub_mem (sub_mem (hφ _ _) (hφ _ _)) (hφ _ _)) (hφ _ _)

lemma op_one_right_mem (u : Fin q → K) (hu : ∑ i, u i = 0) : op u 1 ∈ (N : Submodule K _) := by
  intro r
  rw [frob_op_E]; simpa using hu

lemma op_one_left_mem (v : Fin q → K) (hv : ∑ i, v i = 0) : op 1 v ∈ (N : Submodule K _) := by
  intro r
  rw [frob_op_E]
  simp only [Pi.one_apply, one_mul]
  rw [Equiv.sum_comp r v]; exact hv

lemma op_one_one_mem (hq : (q : K) = 0) : op (1 : Fin q → K) 1 ∈ (N : Submodule K _) := by
  intro r
  rw [frob_op_E]; simpa using hq

lemma ubA (n : ℕ) : ∃ A B : Equiv.Perm (Fin (n + 1)) → ((Fin n × Fin n) ⊕ Unit) → K,
    ∀ p r : Equiv.Perm (Fin (n + 1)),
      (((univ : Finset (Fin (n + 1))).filter (fun i => r (p i) = i)).card : K) = ∑ a, A p a * B r a := by
  let f : Fin n → Fin (n + 1) → K := fun j => ev (Fin.castSucc j) - ev (Fin.last n)
  let F : ((Fin n × Fin n) ⊕ Unit) → Matrix (Fin (n + 1)) (Fin (n + 1)) K := fun a => match a with
    | Sum.inl a => op (f a.1) (f a.2)
    | Sum.inr _ => E 1
  apply ub F
  intro p
  apply Submodule.mem_sup_left
  apply ub_swap (Submodule.span K (Set.range F)) (Submodule.subset_span ⟨Sum.inr (), rfl⟩)
  apply rect_of_phi _ (Fin.last n)
  intro x y
  induction x using Fin.lastCases with
  | last => simp [op_zero_left]
  | cast j =>
    induction y using Fin.lastCases with
    | last => simp [op_zero_right]
    | cast l => exact Submodule.subset_span ⟨Sum.inl (j, l), rfl⟩

lemma op_add_one (u v : Fin q → K) (β β' : K) :
    op (u + β • 1) (v + β' • 1) = op u v + β' • op u 1 + β • op 1 v + (β * β') • op 1 1 := by
  ext i k; simp [op]; ring

lemma rectBC (b : ℕ) (hq : ((b + 2 : ℕ) : K) = 0) (L : Submodule K (Matrix (Fin (b + 2)) (Fin (b + 2)) K))
    (hN : (N : Submodule K _) ≤ L)
    (hF : ∀ j l : Fin b, op (ev (Fin.castSucc (Fin.castSucc j)) - ev (Fin.last (b + 1)))
      (ev (Fin.castSucc (Fin.castSucc l)) - ev (Fin.last (b + 1))) ∈ L)
    (x y : Fin (b + 2)) :
    op (ev x - ev (Fin.last (b + 1))) (ev y - ev (Fin.last (b + 1))) ∈ L := by
  set o := Fin.last (b + 1)
  let f : Fin b → Fin (b + 2) → K := fun j => ev (Fin.castSucc (Fin.castSucc j)) - ev o
  have hf : ∀ j, ∑ i, f j i = 0 := by
    intro j; simp [f, ev, Finset.sum_sub_distrib]
  have hsum : ∀ α : Fin b → K, ∑ i, (∑ j, α j • f j) i = 0 := by
    intro α
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp [← Finset.mul_sum, hf]
  have Qmem : ∀ (α α' : Fin b → K) (β β' : K),
      op (∑ j, α j • f j + β • 1) (∑ l, α' l • f l + β' • 1) ∈ L := by
    intro α α' β β'
    rw [op_add_one]
    refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
    · rw [op_sum]
      exact Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hF j l)
    · exact Submodule.smul_mem _ _ (hN (op_one_right_mem _ (hsum α)))
    · exact Submodule.smul_mem _ _ (hN (op_one_left_mem _ (hsum α')))
    · exact Submodule.smul_mem _ _ (hN (op_one_one_mem hq))
  have hrep : ∀ x : Fin (b + 2), ∃ (α : Fin b → K) (β : K), ev x - ev o = ∑ j, α j • f j + β • 1 := by
    intro x
    induction x using Fin.lastCases with
    | last => exact ⟨0, 0, by simp [o]⟩
    | cast x' =>
      induction x' using Fin.lastCases with
      | last =>
        refine ⟨fun _ => -1, 1, ?_⟩
        have hb : (b : K) + 2 = 0 := by exact_mod_cast hq
        have n1 : ∀ z : Fin (b + 1), Fin.last (b + 1) ≠ z.castSucc := fun z h => Fin.castSucc_ne_last z h.symm
        have n2 : ∀ z : Fin b, Fin.last b ≠ z.castSucc := fun z h => Fin.castSucc_ne_last z h.symm
        funext i
        induction i using Fin.lastCases with
        | last =>
          simp [f, ev, o, n1]
          linear_combination (-1 : K) * hb
        | cast i' =>
          induction i' using Fin.lastCases with
          | last => simp [f, ev, o, n2]
          | cast i'' => simp [f, ev, o, Fin.castSucc_inj]
      | cast j =>
        refine ⟨fun l => if l = j then 1 else 0, 0, ?_⟩
        simp [ite_smul, f]
  obtain ⟨α, β, hx⟩ := hrep x
  obtain ⟨α', β', hy⟩ := hrep y
  rw [hx, hy]
  exact Qmem α α' β β'

lemma ubB (b : ℕ) (hq : ((b + 2 : ℕ) : K) = 0) :
    ∃ A B : Equiv.Perm (Fin (b + 2)) → ((Fin b × Fin b) ⊕ Unit) → K,
    ∀ p r : Equiv.Perm (Fin (b + 2)),
      (((univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) = ∑ a, A p a * B r a := by
  let f : Fin b → Fin (b + 2) → K := fun j => ev (Fin.castSucc (Fin.castSucc j)) - ev (Fin.last (b + 1))
  let F : ((Fin b × Fin b) ⊕ Unit) → Matrix (Fin (b + 2)) (Fin (b + 2)) K := fun a => match a with
    | Sum.inl a => op (f a.1) (f a.2)
    | Sum.inr _ => E 1
  apply ub F
  intro p
  apply ub_swap (Submodule.span K (Set.range F) ⊔ N)
    (Submodule.mem_sup_left (Submodule.subset_span ⟨Sum.inr (), rfl⟩))
  apply rect_of_phi _ (Fin.last (b + 1))
  apply rectBC b hq _ le_sup_right
  intro j l
  exact Submodule.mem_sup_left (Submodule.subset_span ⟨Sum.inl (j, l), rfl⟩)

lemma one_decomp (o : Fin q) : (E 1 : Matrix (Fin q) (Fin q) K) =
    ∑ x, op (ev x - ev o) (ev x - ev o) + (op 1 (ev o) + op (ev o) 1) - (q : K) • op (ev o) (ev o) := by
  ext i k
  simp only [E, op, ev, Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    Pi.sub_apply, Pi.one_apply, Equiv.Perm.one_apply, smul_eq_mul, sub_mul, mul_sub,
    Finset.sum_sub_distrib]
  by_cases hi : i = o <;> by_cases hk : k = o <;> by_cases hik : i = k <;> simp_all

lemma ubC (b : ℕ) (hq : ((b + 2 : ℕ) : K) = 0) (h2 : (2 : K) = 0) :
    ∃ A B : Equiv.Perm (Fin (b + 2)) → (Fin b × Fin b) → K,
    ∀ p r : Equiv.Perm (Fin (b + 2)),
      (((univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) = ∑ a, A p a * B r a := by
  let f : Fin b → Fin (b + 2) → K := fun j => ev (Fin.castSucc (Fin.castSucc j)) - ev (Fin.last (b + 1))
  let F : (Fin b × Fin b) → Matrix (Fin (b + 2)) (Fin (b + 2)) K := fun a => op (f a.1) (f a.2)
  apply ub F
  intro p
  have hφ := rectBC b hq (Submodule.span K (Set.range F) ⊔ N) le_sup_right
    (fun j l => Submodule.mem_sup_left (Submodule.subset_span ⟨(j, l), rfl⟩))
  apply ub_swap (Submodule.span K (Set.range F) ⊔ N) _ (rect_of_phi _ _ hφ)
  rw [one_decomp (Fin.last (b + 1)), hq, zero_smul, sub_zero]
  refine add_mem (Submodule.sum_mem _ fun x _ => hφ x x) (Submodule.mem_sup_right ?_)
  intro r
  rw [frob_add_left, frob_op_E, frob_op_E]
  simp only [Pi.one_apply, one_mul, mul_one]
  rw [Equiv.sum_comp r (ev (Fin.last (b + 1)))]
  simp [ev]
  linear_combination h2

lemma dot_sub_left (u v w : Fin q → K) : dot (u - v) w = dot u w - dot v w := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]
lemma dot_sub_right (u v w : Fin q → K) : dot w (u - v) = dot w u - dot w v := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]
lemma dot_smul_left (c : K) (u w : Fin q → K) : dot (c • u) w = c * dot u w := by
  simp [dot, Finset.mul_sum, mul_assoc]
lemma dot_smul_right (c : K) (u w : Fin q → K) : dot w (c • u) = c * dot w u := by
  simp [dot, Finset.mul_sum, mul_left_comm]
lemma dot_ev_ev (a b : Fin q) : dot (ev (K := K) a) (ev b) = if a = b then 1 else 0 := by
  by_cases h : a = b
  · subst h; simp [dot, ev]
  · simp [dot, ev, h, Ne.symm h]
lemma dot_ev_one (a : Fin q) : dot (ev (K := K) a) 1 = 1 := by simp [dot, ev]
lemma dot_one_ev (a : Fin q) : dot 1 (ev (K := K) a) = 1 := by simp [dot, ev]
lemma dot_one_one : dot (1 : Fin q → K) 1 = q := by simp [dot]

lemma lbA {d n : ℕ} (hq : ((n + 1 : ℕ) : K) ≠ 0) (A B : Equiv.Perm (Fin (n + 1)) → Fin d → K)
    (hAB : ∀ p r : Equiv.Perm (Fin (n + 1)),
      (((univ : Finset (Fin (n + 1))).filter (fun i => r (p i) = i)).card : K) = ∑ j, A p j * B r j) :
    n * n + 1 ≤ d := by
  set c : K := ((n + 1 : ℕ) : K)⁻¹ with hc
  have hc1 : ((n : K) + 1) * c = 1 := by rw [hc]; push_cast at hq ⊢; field_simp
  let f : Fin n → Fin (n + 1) → K := fun j => ev (Fin.castSucc j) - ev (Fin.last n)
  let g : Fin n → Fin (n + 1) → K := fun j => ev (Fin.castSucc j) - c • 1
  have n1 : ∀ z : Fin n, Fin.castSucc z ≠ Fin.last n := Fin.castSucc_ne_last
  have n1' : ∀ z : Fin n, Fin.last n ≠ Fin.castSucc z := fun z h => n1 z h.symm
  have hf : ∀ j, ∑ i, f j i = 0 := by intro j; simp [f, ev, Finset.sum_sub_distrib]
  have hg : ∀ j, ∑ i, g j i = 0 := by
    intro j; simp [g, ev, Finset.sum_sub_distrib]
    linear_combination -hc1
  have hfg : ∀ j l, dot (f j) (g l) = if j = l then 1 else 0 := by
    intro j l
    simp [f, g, dot_sub_left, dot_sub_right, dot_smul_right, dot_ev_ev, dot_ev_one, n1', Fin.castSucc_inj]
  have hff : ∀ j l, dot (f j) (f l) = (if j = l then 1 else 0) + 1 := by
    intro j l
    simp [f, dot_sub_left, dot_sub_right, dot_ev_ev, n1, n1', Fin.castSucc_inj]
  have hgg : ∀ j l, dot (g j) (g l) = (if j = l then 1 else 0) - c := by
    intro j l
    simp [g, dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right, dot_ev_ev, dot_ev_one,
      dot_one_ev, dot_one_one, Fin.castSucc_inj]
    right
    linear_combination -hc1
  have hprod : ∀ j l : Fin n, dot (f j) (f l) * dot (g j) (g l) = (if j = l then 2 - c else 0) + -c := by
    intro j l
    rw [hff, hgg]
    split_ifs <;> ring
  obtain ⟨_, h2⟩ := lb2 A B hAB (Fin.last n) f g hf hg hfg
  apply h2
  simp only [hprod, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  intro h
  simp only [Nat.cast_add, Nat.cast_one] at h
  have : (1 : K) = 0 := by linear_combination h - (n : K) * hc1
  exact one_ne_zero this

lemma lbBC {d b : ℕ} (hq : ((b + 2 : ℕ) : K) = 0) (A B : Equiv.Perm (Fin (b + 2)) → Fin d → K)
    (hAB : ∀ p r : Equiv.Perm (Fin (b + 2)),
      (((univ : Finset (Fin (b + 2))).filter (fun i => r (p i) = i)).card : K) = ∑ j, A p j * B r j) :
    b * b ≤ d ∧ ((2 : K) ≠ 0 → b * b + 1 ≤ d) := by
  let f : Fin b → Fin (b + 2) → K := fun j => ev (Fin.castSucc (Fin.castSucc j)) - ev (Fin.last (b + 1))
  let g : Fin b → Fin (b + 2) → K := fun j => ev (Fin.castSucc (Fin.castSucc j)) - ev (Fin.castSucc (Fin.last b))
  have n1 : ∀ z : Fin (b + 1), Fin.castSucc z ≠ Fin.last (b + 1) := Fin.castSucc_ne_last
  have n1' : ∀ z : Fin (b + 1), Fin.last (b + 1) ≠ Fin.castSucc z := fun z h => n1 z h.symm
  have n2 : ∀ z : Fin b, Fin.castSucc z ≠ Fin.last b := Fin.castSucc_ne_last
  have n2' : ∀ z : Fin b, Fin.last b ≠ Fin.castSucc z := fun z h => n2 z h.symm
  have hf : ∀ j, ∑ i, f j i = 0 := by intro j; simp [f, ev, Finset.sum_sub_distrib]
  have hg : ∀ j, ∑ i, g j i = 0 := by intro j; simp [g, ev, Finset.sum_sub_distrib]
  have hfg : ∀ j l, dot (f j) (g l) = if j = l then 1 else 0 := by
    intro j l
    simp [f, g, dot_sub_left, dot_sub_right, dot_ev_ev, n1', n2, Fin.castSucc_inj]
  have hff : ∀ j l, dot (f j) (f l) = (if j = l then 1 else 0) + 1 := by
    intro j l
    simp [f, dot_sub_left, dot_sub_right, dot_ev_ev, n1, n1', Fin.castSucc_inj]
  have hgg : ∀ j l, dot (g j) (g l) = (if j = l then 1 else 0) + 1 := by
    intro j l
    simp [g, dot_sub_left, dot_sub_right, dot_ev_ev, n2, n2', Fin.castSucc_inj]
  have hprod : ∀ j l : Fin b, dot (f j) (f l) * dot (g j) (g l) = (if j = l then 3 else 0) + 1 := by
    intro j l
    rw [hff, hgg]
    split_ifs <;> ring
  obtain ⟨h1, h2⟩ := lb2 A B hAB (Fin.last (b + 1)) f g hf hg hfg
  refine ⟨h1, fun h2ne => h2 ?_⟩
  simp only [hprod, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast at hq ⊢
  intro h
  apply h2ne
  linear_combination h + (b : K) * hq

end PEqualNP.Outside.L_lib_591

theorem PEqualNP.Outside.L_lib_591 : ∀ (K : Type) [Field K] (b d : ℕ),
  let q := b + 2
  let P := Equiv.Perm (Fin q)
  let fixed := fun (p r : P) =>
    ((Finset.univ : Finset (Fin q)).filter (fun i => r (p i) = i)).card
  let threshold := if ringChar K ∣ q then
      (q - 2) ^ 2 + (if ringChar K = 2 then 0 else 1)
    else (q - 1) ^ 2 + 1
  (∃ (A B : P → Fin d → K),
    ∀ p r, (fixed p r : K) = ∑ j : Fin d, A p j * B r j) ↔
    threshold ≤ d := by
  intro K _ b d
  dsimp only
  by_cases hdiv : ringChar K ∣ b + 2
  · have hq : ((b + 2 : ℕ) : K) = 0 := (ringChar.spec K (b + 2)).2 hdiv
    rw [ite_eq_left hdiv]
    have hb2 : b + 2 - 2 = b := by omega
    rw [hb2]
    by_cases h2 : ringChar K = 2
    · have h2K : (2 : K) = 0 := by
        have := (ringChar.spec K 2).2 (by rw [h2])
        exact_mod_cast this
      rw [ite_eq_left h2, add_zero, sq]
      constructor
      · rintro ⟨A, B, hAB⟩
        exact (L_lib_591.lbBC hq A B hAB).1
      · intro hd
        exact L_lib_591.pad (by simpa using hd) _ (L_lib_591.ubC b hq h2K)
    · have h2K : (2 : K) ≠ 0 := by
        intro h
        have h' : ringChar K ∣ 2 := (ringChar.spec K 2).1 (by exact_mod_cast h)
        rcases (Nat.dvd_prime Nat.prime_two).1 h' with h1 | h1
        · have : ((1 : ℕ) : K) = 0 := (ringChar.spec K 1).2 (by rw [h1])
          simp at this
        · exact h2 h1
      rw [ite_eq_right h2, sq]
      constructor
      · rintro ⟨A, B, hAB⟩
        exact (L_lib_591.lbBC hq A B hAB).2 h2K
      · intro hd
        exact L_lib_591.pad (by simpa using hd) _ (L_lib_591.ubB b hq)
  · have hq : ((b + 1 + 1 : ℕ) : K) ≠ 0 := fun h => hdiv ((ringChar.spec K _).1 h)
    rw [ite_eq_right hdiv]
    have hb1 : b + 2 - 1 = b + 1 := by omega
    rw [hb1, sq]
    constructor
    · rintro ⟨A, B, hAB⟩
      exact L_lib_591.lbA hq A B hAB
    · intro hd
      exact L_lib_591.pad (by simpa using hd) _ (L_lib_591.ubA (b + 1))
