import Mathlib

-- Finite difference and quartic reduction adapted from accepted
-- lean/PEqualNP/Outside/L_meta_29772.lean at bb94de33ac09036a8d6d03893ec35540ccd9ef2f.
namespace PEqualNP.Outside.L_meta_29744_aux

section Differences

variable {W W' R : Type} [AddCommGroup W] [AddCommGroup W'] [CommRing R]

private def delta (f : W → R) (u x : W) : R := f (x + u) - f x

private def differences (f : W → R) (directions : List W) : W → R :=
  directions.foldl delta f

private def degree : ℕ → (W → R) → Prop
  | 0, f => ∀ u x, delta f u x = 0
  | n + 1, f => ∀ u, degree n (delta f u)

private theorem degree_zero_const {f : W → R} (h : degree 0 f) (x : W) : f x = f 0 := by
  have hx := h x 0
  simpa [delta, sub_eq_zero] using hx

private theorem delta_add (f g : W → R) (u : W) :
    delta (fun x => f x + g x) u = fun x => delta f u x + delta g u x := by
  funext x
  unfold delta
  ring

private theorem delta_sub (f g : W → R) (u : W) :
    delta (fun x => f x - g x) u = fun x => delta f u x - delta g u x := by
  funext x
  unfold delta
  ring

private theorem delta_scale (c : R) (f : W → R) (u : W) :
    delta (fun x => c * f x) u = fun x => c * delta f u x := by
  funext x
  unfold delta
  ring

private theorem delta_shift (f : W → R) (u v : W) :
    delta (fun x => f (x + v)) u = fun x => delta f u (x + v) := by
  funext x
  simp only [delta, add_right_comm x u v]

private theorem delta_mul (f g : W → R) (u : W) :
    delta (fun x => f x * g x) u =
      fun x => delta f u x * g (x + u) + f x * delta g u x := by
  funext x
  unfold delta
  ring

private theorem degree_const (n : ℕ) (c : R) : degree n (fun _ : W => c) := by
  induction n generalizing c with
  | zero => intro u x; simp [delta]
  | succ n ih =>
    intro u
    have h : delta (fun _ : W => c) u = fun _ => 0 := by funext x; simp [delta]
    rw [h]
    exact ih 0

private theorem degree_add {n : ℕ} {f g : W → R}
    (hf : degree n f) (hg : degree n g) : degree n (fun x => f x + g x) := by
  induction n generalizing f g with
  | zero => intro u x; simpa [hf u x, hg u x] using congrFun (delta_add f g u) x
  | succ n ih =>
    intro u
    rw [delta_add]
    exact ih (hf u) (hg u)

private theorem degree_scale {n : ℕ} (c : R) {f : W → R}
    (hf : degree n f) : degree n (fun x => c * f x) := by
  induction n generalizing f with
  | zero => intro u x; simpa [hf u x] using congrFun (delta_scale c f u) x
  | succ n ih =>
    intro u
    rw [delta_scale]
    exact ih (hf u)

private theorem degree_shift {n : ℕ} (v : W) {f : W → R}
    (hf : degree n f) : degree n (fun x => f (x + v)) := by
  induction n generalizing f with
  | zero =>
    intro u x
    rw [delta_shift]
    exact hf u (x + v)
  | succ n ih =>
    intro u
    rw [delta_shift]
    exact ih (hf u)

private theorem degree_raise {n : ℕ} {f : W → R} (hf : degree n f) : degree (n + 1) f := by
  induction n generalizing f with
  | zero =>
    intro u v x
    change delta f u (x + v) - delta f u x = 0
    rw [hf u (x + v), hf u x, sub_self]
  | succ n ih => exact fun u => ih (hf u)

private theorem degree_mul {a b : ℕ} {f g : W → R}
    (hf : degree a f) (hg : degree b g) : degree (a + b) (fun x => f x * g x) := by
  induction a generalizing b f g with
  | zero =>
    have he : (fun x => f x * g x) = fun x => f 0 * g x := by
      funext x
      rw [degree_zero_const hf x]
    simpa only [Nat.zero_add, he] using degree_scale (f 0) hg
  | succ a ia =>
    induction b generalizing f g with
    | zero =>
      have he : (fun x => f x * g x) = fun x => g 0 * f x := by
        funext x
        rw [degree_zero_const hg x, mul_comm]
      simpa only [Nat.add_zero, he] using degree_scale (g 0) hf
    | succ b ib =>
      change degree (a + 1 + b + 1) _
      intro u
      rw [delta_mul]
      have h₁ := ia (hf u) (degree_shift u hg)
      have h₂ := ib hf (hg u)
      rw [show a + (b + 1) = a + 1 + b by omega] at h₁
      exact degree_add h₁ h₂

private theorem degree_fold {f : W → R} (us : List W) (n : ℕ)
    (hf : degree (us.length + n) f) : degree n (differences f us) := by
  induction us generalizing f with
  | nil => simpa [differences] using hf
  | cons u us ih =>
    change degree n (differences (delta f u) us)
    apply ih
    rw [show (u :: us).length + n = (us.length + n) + 1 by simp; omega] at hf
    exact hf u

private theorem differences_sub (f g : W → R) (us : List W) (x : W) :
    differences (fun y => f y - g y) us x = differences f us x - differences g us x := by
  induction us generalizing f g with
  | nil => rfl
  | cons u us ih =>
    change differences (delta (fun y => f y - g y) u) us x = _
    rw [delta_sub, ih]
    rfl

private theorem differences_zero {f : W → R} (us : List W) {n : ℕ} (hu : us.length = n + 1)
    (hf : degree n f) (x : W) : differences f us x = 0 := by
  induction us generalizing n f with
  | nil => simp at hu
  | cons u us ih =>
    cases n with
    | zero =>
      have hnil : us = [] := List.length_eq_zero_iff.1 (by simpa using hu)
      subst us
      exact hf u x
    | succ n => exact ih (Nat.succ.inj hu) (hf u)

private theorem differences_eq_on {S : AddSubgroup W} {f g : W → R} (hfg : ∀ x ∈ S, f x = g x)
    (us : List W) (hu : ∀ u ∈ us, u ∈ S) (x : W) (hx : x ∈ S) :
    differences f us x = differences g us x := by
  induction us generalizing f g with
  | nil => exact hfg x hx
  | cons u us ih =>
    change differences (delta f u) us x = differences (delta g u) us x
    refine ih (fun z hz => ?_) (fun v hv => hu v (List.mem_cons_of_mem _ hv))
    simp only [delta, hfg (z + u) (S.add_mem hz (hu u List.mem_cons_self)), hfg z hz]

private theorem differences_comp (p : W →+ W') (c : W') (f : W' → R) (us : List W) (x : W) :
    differences (fun y => f (p y + c)) us x = differences f (us.map p) (p x + c) := by
  induction us generalizing f with
  | nil => rfl
  | cons u us ih =>
    change differences (delta (fun y => f (p y + c)) u) us x =
      differences (delta f (p u)) (us.map p) (p x + c)
    have hδ : delta (fun y => f (p y + c)) u = fun y => delta f (p u) (p y + c) := by
      funext y
      simp only [delta, map_add, add_right_comm (p y) (p u) c]
    rw [hδ, ih]

end Differences

private abbrev Scalar := ZMod 2
private abbrev Word (k : ℕ) := Fin k → Scalar
private abbrev Query (k : ℕ) := Word k →ₗ[Scalar] Scalar

private def index {k : ℕ} (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

private def rotate {k : ℕ} (hk : 0 < k) (s : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x (index hk (i.val + k - s % k))

private def mix {k : ℕ} (hk : 0 < k) (g : ℕ) (x : Word k) (i : Fin k) : Scalar :=
  x i + x (index hk (i.val + g)) + x (index hk (i.val + k - g % k))

private def step {k : ℕ} (hk : 0 < k) (x : Word k) (i : Fin k) : Scalar :=
  x i + (1 + x (index hk (i.val + 1))) * x (index hk (i.val + 2))

private def gap (b : Bool) : ℕ := if b then 2 else 1

private def spin (b : Bool) : ℕ := if b then 3 else 1

private def linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x)

private def namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  mix hk (gap b) (rotate hk (spin b) x + name b)

private def firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (x : Word k) : Word k :=
  step hk (namedInput hk name b x) + rotate hk (if b then 4 else 0) x + c₁ b

private def quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (x : Word k) (j : Fin k) : Scalar :=
  linearInput hk b x (index hk (j.val + 1)) * linearInput hk b x (index hk (j.val + 2))

private def outputWord {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (x : Word k) (b : Bool) : Word k :=
  step hk (mix hk (gap b) (firstRow hk name c₁ b x)) +
    rotate hk (if b then 7 else 2) x + c₂ b

private def topWord {k : ℕ} (hk : 0 < k) (x : Word k) (b : Bool) (i : Fin k) : Scalar :=
  mix hk (gap b) (quadratic hk b x) (index hk (i.val + 1)) *
    mix hk (gap b) (quadratic hk b x) (index hk (i.val + 2))

private theorem degree_coord {k : ℕ} (i : Fin k) : degree 1 (fun x : Word k => x i) := by
  intro u v x
  simp only [delta, Pi.add_apply]
  ring

private theorem degree_mix {k n : ℕ} (hk : 0 < k) (g : ℕ) (f : Word k → Word k)
    (hf : ∀ i, degree n (fun x => f x i)) (i : Fin k) :
    degree n (fun x => mix hk g (f x) i) :=
  degree_add (degree_add (hf i) (hf _)) (hf _)

private theorem mix_sub {k : ℕ} (hk : 0 < k) (g : ℕ) (f h : Word k) (i : Fin k) :
    mix hk g f i - mix hk g h i = mix hk g (f - h) i := by
  simp only [mix, Pi.sub_apply]
  ring

private theorem namedInput_eq {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (x : Word k)
    (i : Fin k) : namedInput hk name b x i = linearInput hk b x i + mix hk (gap b) (name b) i := by
  simp only [namedInput, linearInput, mix, Pi.add_apply]
  ring

private theorem degree_linearInput {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => linearInput hk b x i) :=
  degree_mix hk _ _ (fun _ => degree_coord _) i

private theorem degree_namedInput {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 1 (fun x => namedInput hk name b x i) := by
  simpa only [namedInput_eq] using
    degree_add (degree_linearInput hk b i) (degree_const 1 (mix hk (gap b) (name b) i))

private theorem degree_input_remainder {k : ℕ} (hk : 0 < k) (name : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 0 (fun x => namedInput hk name b x i - linearInput hk b x i) := by
  simp only [namedInput_eq, add_sub_cancel_left]
  exact degree_const 0 _

private theorem degree_quadratic {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => quadratic hk b x i) :=
  degree_mul (degree_linearInput hk b _) (degree_linearInput hk b _)

private theorem product_remainder {k n : ℕ} {a b a₀ b₀ : Word k → Scalar}
    (hb : degree (n + 1) b) (ha₀ : degree (n + 1) a₀)
    (ha : degree n (fun x => a x - a₀ x)) (hb' : degree n (fun x => b x - b₀ x)) :
    degree (n + (n + 1)) (fun x => (1 + a x) * b x - a₀ x * b₀ x) := by
  have hp := degree_mul (degree_add (degree_const n (1 : Scalar)) ha) hb
  have hq := degree_mul ha₀ hb'
  rw [Nat.add_comm (n + 1) n] at hq
  convert degree_add hp hq using 1
  funext x
  ring

private theorem degree_first_remainder {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 1 (fun x => firstRow hk name c₁ b x i - quadratic hk b x i) := by
  have hp := product_remainder (n := 0) (degree_namedInput hk name b (index hk (i.val + 2)))
    (degree_linearInput hk b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 1)))
    (degree_input_remainder hk name b (index hk (i.val + 2)))
  have hd := degree_add (degree_add (degree_add (degree_namedInput hk name b i) hp)
    (degree_coord (index hk (i.val + k - (if b then 4 else 0) % k)))) (degree_const 1 (c₁ b i))
  convert hd using 1
  funext x
  simp only [firstRow, step, quadratic, rotate, Pi.add_apply]
  ring

private theorem degree_firstRow {k : ℕ} (hk : 0 < k) (name c₁ : Bool → Word k) (b : Bool) (i : Fin k) :
    degree 2 (fun x => firstRow hk name c₁ b x i) := by
  simpa only [sub_add_cancel] using
    degree_add (degree_raise (degree_first_remainder hk name c₁ b i)) (degree_quadratic hk b i)

private theorem degree_output_remainder {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (b : Bool)
    (i : Fin k) : degree 3 (fun x => outputWord hk name c₁ c₂ x b i - topWord hk x b i) := by
  let y := fun x => mix hk (gap b) (firstRow hk name c₁ b x)
  let q := fun x => mix hk (gap b) (quadratic hk b x)
  have hy (j : Fin k) : degree 2 (fun x => y x j) :=
    degree_mix hk _ _ (degree_firstRow hk name c₁ b) j
  have hq (j : Fin k) : degree 2 (fun x => q x j) :=
    degree_mix hk _ _ (degree_quadratic hk b) j
  have hdiff (j : Fin k) : degree 1 (fun x => y x j - q x j) := by
    simpa only [y, q, mix_sub] using
      degree_mix hk (gap b) (fun x => firstRow hk name c₁ b x - quadratic hk b x)
        (degree_first_remainder hk name c₁ b) j
  have hp := product_remainder (n := 1) (hy (index hk (i.val + 2))) (hq (index hk (i.val + 1)))
    (hdiff (index hk (i.val + 1))) (hdiff (index hk (i.val + 2)))
  have hrotate := degree_raise (degree_raise
    (degree_coord (index hk (i.val + k - (if b then 7 else 2) % k))))
  have hd := degree_add (degree_add (degree_add (degree_raise (hy i)) hp) hrotate)
    (degree_const 3 (c₂ b i))
  convert hd using 1
  funext x
  simp only [outputWord, step, topWord, rotate, Pi.add_apply, y, q]
  ring

private theorem degree_topWord {k : ℕ} (hk : 0 < k) (b : Bool) (i : Fin k) :
    degree 4 (fun x => topWord hk x b i) :=
  degree_mul (degree_mix hk _ _ (degree_quadratic hk b) _)
    (degree_mix hk _ _ (degree_quadratic hk b) _)

private def fourthDifference {m : ℕ} (f : Word m → Scalar) (v : Fin 4 → Word m) : Word m → Scalar :=
  differences f (List.ofFn v)

private def IsCubic {k : ℕ} (f : Word k → Scalar) : Prop :=
  ∀ v x, fourthDifference f v x = 0

private theorem output_fourth {k : ℕ} (hk : 0 < k) (name c₁ c₂ : Bool → Word k) (b : Bool) (i : Fin k)
    (v : Fin 4 → Word k) (x : Word k) :
    fourthDifference (fun y => outputWord hk name c₁ c₂ y b i) v x =
      fourthDifference (fun y => topWord hk y b i) v 0 := by
  have hlen : (List.ofFn v).length = 4 := List.length_ofFn
  have h := differences_zero _ hlen (degree_output_remainder hk name c₁ c₂ b i) x
  rw [differences_sub, sub_eq_zero] at h
  have hc := degree_fold (List.ofFn v) 0 (by simpa [hlen] using degree_topWord hk b i)
  exact h.trans (degree_zero_const hc x)

private def queryRun {k d : ℕ} (ask : Fin d → ℕ → Query k) (x : Word k) : ℕ :=
  (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0

private def Marked {k : ℕ} (mark : Fin k → Bool × Bool) (b : Bool) (i : Fin k) : Prop :=
  (if b then (mark i).2 else (mark i).1) = true

private def Admiss {k : ℕ} (hk : 0 < k) (mark : Fin k → Bool × Bool)
    (U : Submodule Scalar (Word k)) : Prop :=
  ∀ b i, Marked mark b i → ∀ v : Fin 4 → Word k, (∀ j, v j ∈ U) →
    fourthDifference (fun x => topWord hk x b i) v 0 = 0

private def Fits {k : ℕ} (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Word k) : Prop :=
  ∃ (ask : Fin d → ℕ → Query k) (readout : ℕ → Bool → Fin k → Word k → Scalar),
    (∀ h b i, IsCubic (readout h b i)) ∧
    ∀ x b i, Marked mark b i →
      outputWord hk name c₁ c₂ x b i = readout (queryRun ask x) b i x

-- Binary transcript lemmas adapted from lean/PEqualNP/Outside/L_meta_29719.lean
-- at bb94de33ac09036a8d6d03893ec35540ccd9ef2f, lines 282–307.
private theorem kernel_bit_eq (a b : ZMod 2)
    (h : (if a = 0 then (0 : ℕ) else 1) = (if b = 0 then 0 else 1)) : a = b := by
  revert a b
  decide

private theorem kernel_fold_dec {α : Type*} (l : List α) :
    ∀ (c c' : α → ℕ), (∀ j, c j ≤ 1) → (∀ j, c' j ≤ 1) →
      l.foldl (fun h j => 2 * h + c j) 0 = l.foldl (fun h j => 2 * h + c' j) 0 →
      ∀ j ∈ l, c j = c' j := by
  induction l using List.reverseRecOn with
  | nil => intro c c' _ _ _ j hj; simp at hj
  | append_singleton l a ih =>
    intro c c' hc hc' h j hj
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at h
    have ha := hc a
    have ha' := hc' a
    have e1 : c a = c' a := by omega
    have e2 : l.foldl (fun h j => 2 * h + c j) 0 =
        l.foldl (fun h j => 2 * h + c' j) 0 := by omega
    rcases List.mem_append.mp hj with hj | hj
    · exact ih c c' hc hc' e2 j hj
    · have e : j = a := by simpa using hj
      subst j
      exact e1

private theorem kernel_fold_zero {α : Type*} (c : ℕ → α → ℕ) (l : List α)
    (h : ∀ j ∈ l, c 0 j = 0) : l.foldl (fun h j => 2 * h + c h j) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldl_cons, mul_zero, zero_add, h a (by simp)]
    exact ih (fun j hj => h j (by simp [hj]))

-- The zero path and affine retraction use the same pinned source, lines
-- 345–350 and 445–492, now with an unrestricted kernel dimension criterion.
private theorem fits_iff_admiss {k : ℕ} (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Word k) :
    Fits hk mark d name c₁ c₂ ↔
      ∃ U : Submodule Scalar (Word k), Admiss hk mark U ∧ k ≤ Module.finrank Scalar U + d := by
  classical
  constructor
  · rintro ⟨ask, readout, cubic, agree⟩
    let U : Submodule Scalar (Word k) := ⨅ j : Fin d, LinearMap.ker (ask j 0)
    have hrun0 (x : Word k) (hx : x ∈ U) : queryRun ask x = 0 := by
      simp only [U, Submodule.mem_iInf, LinearMap.mem_ker] at hx
      exact kernel_fold_zero (fun h j => if ask j h x = 0 then 0 else 1) _
        (fun j _ => by simp [hx j])
    refine ⟨U, ?_, ?_⟩
    · intro b i hm v hv
      have hfg (x : Word k) (hx : x ∈ U.toAddSubgroup) :
          outputWord hk name c₁ c₂ x b i = readout 0 b i x := by
        simpa only [hrun0 x hx] using agree x b i hm
      have hmem (w : Word k) (hw : w ∈ List.ofFn v) : w ∈ U.toAddSubgroup := by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
        exact hv j
      rw [← output_fourth hk name c₁ c₂ b i v 0]
      exact (differences_eq_on hfg _ hmem 0 (zero_mem _)).trans (cubic 0 b i v 0)
    · let Q : Word k →ₗ[Scalar] (Fin d → Scalar) := LinearMap.pi (fun j => ask j 0)
      have hker : LinearMap.ker Q = U := by
        ext x
        simp only [U, Submodule.mem_iInf, LinearMap.mem_ker]
        change (fun j : Fin d => ask j 0 x) = 0 ↔ _
        exact ⟨fun h j => congrFun h j, fun h => funext h⟩
      have hdim := LinearMap.finrank_range_add_finrank_ker Q
      rw [hker] at hdim
      change _ = Module.finrank Scalar (Fin k → Scalar) at hdim
      rw [Module.finrank_fin_fun] at hdim
      have hrank := LinearMap.finrank_le_finrank_of_injective
        (f := (LinearMap.range Q).subtype) Subtype.val_injective
      rw [Module.finrank_fin_fun] at hrank
      omega
  · rintro ⟨U, good, hdim⟩
    obtain ⟨V, hUV⟩ := U.exists_isCompl
    let p := U.projection V hUV
    let q := V.projectionOnto U hUV.symm
    let m := Module.finrank Scalar V
    let B := Module.finBasis Scalar V
    have hm : m ≤ d := by
      have he := Submodule.finrank_add_eq_of_isCompl hUV
      change Module.finrank Scalar U + m = Module.finrank Scalar (Fin k → Scalar) at he
      rw [Module.finrank_fin_fun] at he
      omega
    let qs (j : Fin d) : Query k :=
      if hj : j.val < m then (B.coord ⟨j.val, hj⟩).comp q else 0
    let ask (j : Fin d) (_ : ℕ) : Query k := qs j
    have hsame {x y : Word k} (h : queryRun ask y = queryRun ask x) : x - y ∈ U := by
      let bit (z : Word k) (j : Fin d) : ℕ := if qs j z = 0 then 0 else 1
      change (List.finRange d).foldl (fun a j => 2 * a + bit y j) 0 =
        (List.finRange d).foldl (fun a j => 2 * a + bit x j) 0 at h
      have hbit (z : Word k) (j : Fin d) : bit z j ≤ 1 := by
        dsimp [bit]
        split_ifs <;> omega
      have heq (j : Fin d) : qs j y = qs j x :=
        kernel_bit_eq _ _ (kernel_fold_dec _ _ _ (hbit y) (hbit x) h j (List.mem_finRange j))
      apply (Submodule.projectionOnto_apply_eq_zero_iff hUV.symm).mp
      change q (x - y) = 0
      apply B.forall_coord_eq_zero_iff.mp
      intro j
      let n : Fin d := ⟨j.val, lt_of_lt_of_le j.isLt hm⟩
      have hj := heq n
      change (if hn : j.val < m then (B.coord ⟨j.val, hn⟩).comp q else 0) y =
        (if hn : j.val < m then (B.coord ⟨j.val, hn⟩).comp q else 0) x at hj
      simp only [dite_eq_left (show j.val < m from j.isLt), LinearMap.comp_apply] at hj
      rw [map_sub, map_sub, hj, sub_self]
    let rep (h : ℕ) : Word k := if hr : ∃ z, queryRun ask z = h then Classical.choose hr else 0
    let readout (h : ℕ) (b : Bool) (i : Fin k) (x : Word k) : Scalar :=
      if Marked mark b i then outputWord hk name c₁ c₂ (p x + (rep h - p (rep h))) b i else 0
    refine ⟨ask, readout, fun h b i v x => ?_, fun x b i hmark => ?_⟩
    · by_cases hmark : Marked mark b i
      · simp only [readout, hmark, ↓reduceIte]
        have hcomp := differences_comp p.toAddMonoidHom (rep h - p (rep h))
          (fun y => outputWord hk name c₁ c₂ y b i) (List.ofFn v) x
        simp only [LinearMap.toAddMonoidHom_coe, List.map_ofFn] at hcomp
        refine hcomp.trans ?_
        change fourthDifference (fun y => outputWord hk name c₁ c₂ y b i) (p ∘ v) _ = 0
        rw [output_fourth]
        apply good b i hmark
        intro j
        change U.projection V hUV (v j) ∈ U
        rw [← Submodule.coe_projectionOnto_apply]
        exact (U.projectionOnto V hUV (v j)).property
      · simp only [readout, hmark, ↓reduceIte]
        exact differences_zero _ List.length_ofFn (degree_const 3 0) x
    · let y := rep (queryRun ask x)
      have hy : queryRun ask y = queryRun ask x := by
        have h : ∃ z, queryRun ask z = queryRun ask x := ⟨x, rfl⟩
        change queryRun ask (if hr : ∃ z, queryRun ask z = queryRun ask x then
          Classical.choose hr else 0) = queryRun ask x
        rw [dite_eq_left h]
        exact Classical.choose_spec h
      have hfix : p (x - y) = x - y := Submodule.projection_apply_of_mem_left hUV (hsame hy)
      have he : p x + (y - p y) = x := calc
        p x + (y - p y) = p (x - y) + y := by rw [map_sub]; abel
        _ = x := by rw [hfix, sub_add_cancel]
      simp only [readout, hmark, ↓reduceIte]
      change outputWord hk name c₁ c₂ x b i = outputWord hk name c₁ c₂ (p x + (y - p y)) b i
      rw [he]

private def leftWord {k l : ℕ} : Word (k + l) →ₗ[Scalar] Word k where
  toFun x i := x (Fin.castAdd l i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def rightWord {k l : ℕ} : Word (k + l) →ₗ[Scalar] Word l where
  toFun x i := x (Fin.natAdd k i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def seamIndex {n : ℕ} (hn : 0 < n) (z : ℤ) : Fin n :=
  ⟨(z % (n : ℤ)).toNat, (Int.toNat_lt (Int.emod_nonneg z (by omega))).2
    (Int.emod_lt_of_pos z (by omega))⟩

private def seamAt {n : ℕ} (hn : 0 < n) (x : Word n) (z : ℤ) : Scalar :=
  x (seamIndex hn z)

private theorem seamIndex_nat {n : ℕ} (hn : 0 < n) (m : ℕ) :
    seamIndex hn (m : ℤ) = index hn m := by
  apply Fin.ext
  change ((m : ℤ) % (n : ℤ)).toNat = m % n
  rw [← Int.natCast_emod]
  exact Int.toNat_natCast _

private theorem seamIndex_center {n : ℕ} (hn : 0 < n) (i : Fin n) :
    seamIndex hn (i.val : ℤ) = i := by
  rw [seamIndex_nat]
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

private theorem seamIndex_value {n : ℕ} (hn : 0 < n) (z : ℤ) :
    ((seamIndex hn z).val : ℤ) = z % (n : ℤ) :=
  Int.toNat_of_nonneg (Int.emod_nonneg z (by omega))

private theorem seamIndex_add {n : ℕ} (hn : 0 < n) (z : ℤ) (s : ℕ) :
    index hn ((seamIndex hn z).val + s) = seamIndex hn (z + (s : ℤ)) := by
  rw [← seamIndex_nat]
  apply Fin.ext
  change ((((seamIndex hn z).val + s : ℕ) : ℤ) % (n : ℤ)).toNat =
    ((z + (s : ℤ)) % (n : ℤ)).toNat
  rw [Int.natCast_add, seamIndex_value, Int.emod_add_emod]

private theorem seamIndex_sub {n : ℕ} (hn : 0 < n) (z : ℤ) (s : ℕ) :
    index hn ((seamIndex hn z).val + n - s % n) = seamIndex hn (z - (s : ℤ)) := by
  rw [← seamIndex_nat]
  apply Fin.ext
  change ((((seamIndex hn z).val + n - s % n : ℕ) : ℤ) % (n : ℤ)).toNat =
    ((z - (s : ℤ)) % (n : ℤ)).toNat
  have hs := Nat.mod_lt s hn
  rw [Int.natCast_sub (show s % n ≤ (seamIndex hn z).val + n by omega),
    Int.natCast_add, Int.natCast_emod, seamIndex_value]
  apply congrArg Int.toNat
  rw [show z % (n : ℤ) + (n : ℤ) - (s : ℤ) % (n : ℤ) =
    z % (n : ℤ) - (s : ℤ) % (n : ℤ) + (n : ℤ) by omega,
    Int.add_emod_right, Int.emod_sub_emod, Int.sub_emod_emod]

private theorem seamAt_period {n : ℕ} (hn : 0 < n) (x : Word n) (z : ℤ) :
    seamAt hn x (z + (n : ℤ)) = seamAt hn x z := by
  apply congrArg x
  apply Fin.ext
  change ((z + (n : ℤ)) % (n : ℤ)).toNat = (z % (n : ℤ)).toNat
  rw [Int.add_emod_right]

private def seamPosition (r : ℕ) (i : Fin (5 + r)) : ℤ :=
  if i.val < 5 then (i.val : ℤ) else (i.val : ℤ) - (5 + (r : ℤ))

private def seam {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (r : ℕ) :
    Word (k + l) →ₗ[Scalar] Word (5 + r) where
  toFun x i := seamAt hk (leftWord x) (seamPosition r i) -
    seamAt hl (rightWord x) (seamPosition r i)
  map_add' x y := by
    funext i
    simp only [seamAt, map_add, Pi.add_apply]
    abel
  map_smul' c x := by
    funext i
    simp only [seamAt, map_smul, RingHom.id_apply, Pi.smul_apply, smul_sub]

private theorem seam_agree {k l r : ℕ} (hk : 0 < k) (hl : 0 < l) {x : Word (k + l)}
    (hx : x ∈ LinearMap.ker (seam hk hl r)) (z : ℤ) (hz₀ : -(r : ℤ) ≤ z)
    (hz₁ : z < 5) : seamAt hk (leftWord x) z = seamAt hl (rightWord x) z := by
  have he := LinearMap.mem_ker.mp hx
  suffices h : ∃ i : Fin (5 + r), seamPosition r i = z by
    obtain ⟨i, hi⟩ := h
    have hz := congrFun he i
    change seamAt hk (leftWord x) (seamPosition r i) -
      seamAt hl (rightWord x) (seamPosition r i) = 0 at hz
    exact sub_eq_zero.mp (hi ▸ hz)
  by_cases h0 : 0 ≤ z
  · let i : Fin (5 + r) := ⟨z.toNat, by omega⟩
    exact ⟨i, by
      have hi : i.val < 5 := by change z.toNat < 5; omega
      simp only [seamPosition, ite_eq_left hi]
      exact Int.toNat_of_nonneg h0⟩
  · let i : Fin (5 + r) := ⟨(z + (5 + (r : ℤ))).toNat, by omega⟩
    exact ⟨i, by
      have hi : ¬i.val < 5 := by change ¬(z + (5 + (r : ℤ))).toNat < 5; omega
      simp only [seamPosition, ite_eq_right hi]
      change (((z + (5 + (r : ℤ))).toNat : ℕ) : ℤ) - (5 + (r : ℤ)) = z
      rw [Int.toNat_of_nonneg (show 0 ≤ z + (5 + (r : ℤ)) by omega)]
      omega⟩

private theorem seamAt_leftPart {k l : ℕ} (hk : 0 < k) (x : Word (k + l))
    (z : ℤ) (hz₀ : 0 ≤ z) (hz₁ : z < k) :
    seamAt (Nat.add_pos_left hk l) x z = seamAt hk (leftWord x) z := by
  change x (seamIndex _ z) = x (Fin.castAdd l (seamIndex hk z))
  apply congrArg x
  apply Fin.ext
  change (z % ((k + l : ℕ) : ℤ)).toNat = (z % (k : ℤ)).toNat
  rw [Int.emod_eq_of_lt hz₀ (show z < ((k + l : ℕ) : ℤ) by omega), Int.emod_eq_of_lt hz₀ hz₁]

private theorem seamAt_rightPart {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (x : Word (k + l))
    (z : ℤ) (hz₀ : 0 ≤ z) (hz₁ : z < l) :
    seamAt (Nat.add_pos_left hk l) x ((k : ℤ) + z) = seamAt hl (rightWord x) z := by
  change x (seamIndex _ ((k : ℤ) + z)) = x (Fin.natAdd k (seamIndex hl z))
  apply congrArg x
  apply Fin.ext
  change (((k : ℤ) + z) % ((k + l : ℕ) : ℤ)).toNat = k + (z % (l : ℤ)).toNat
  rw [Int.emod_eq_of_lt (show 0 ≤ (k : ℤ) + z by omega)
    (show (k : ℤ) + z < ((k + l : ℕ) : ℤ) by omega), Int.emod_eq_of_lt hz₀ hz₁]
  omega

-- If the window goes past both blocks, remove one full period and use the seam
-- at both offsets in the shorter interval. This needs no lower bound on block length.
private theorem seam_forward (k l : ℤ) (hk : 0 < k) (hl : 0 < l) (s : ℤ)
    (A L R : ℤ → Scalar) (hA : ∀ z, A (z + (k + l)) = A z)
    (hL : ∀ z, L (z + k) = L z) (hR : ∀ z, R (z + l) = R z)
    (hLp : ∀ z, 0 ≤ z → z < k → A z = L z)
    (hRp : ∀ z, 0 ≤ z → z < l → A (k + z) = R z)
    (hS : ∀ z, 0 ≤ z → z < s → L z = R z)
    (j : ℤ) (hj₀ : 0 ≤ j) (hj₁ : j < k + s) : A j = L j := by
  have h (m : ℕ) : (m : ℤ) < k + s → A m = L m := by
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro hm
      by_cases hmk : (m : ℤ) < k
      · exact hLp _ (by omega) hmk
      let d : ℤ := (m : ℤ) - k
      have hd₀ : 0 ≤ d := by dsimp [d]; omega
      have hds : d < s := by dsimp [d]; omega
      have hmd : (m : ℤ) = d + k := by dsimp [d]; omega
      have hleft : L m = R d := by rw [hmd, hL]; exact hS d hd₀ hds
      by_cases hdl : d < l
      · rw [hleft, show (m : ℤ) = k + d by omega]
        exact hRp d hd₀ hdl
      let e := (d - l).toNat
      have he : (e : ℤ) = d - l := Int.toNat_of_nonneg (by omega)
      calc
        A m = A e := by rw [show (m : ℤ) = (e : ℤ) + (k + l) by omega, hA]
        _ = L e := ih e (by omega) (by omega)
        _ = R e := hS _ (by omega) (by omega)
        _ = R d := by rw [show d = (e : ℤ) + l by omega, hR]
        _ = L m := hleft.symm
  have hj := Int.toNat_of_nonneg hj₀
  simpa only [hj] using h j.toNat (by rwa [hj])

-- Reverse around the end of each block to apply the same extension argument backward.
private theorem seam_interval (k l : ℤ) (hk : 0 < k) (hl : 0 < l) (s r : ℤ)
    (A L R : ℤ → Scalar) (hA : ∀ z, A (z + (k + l)) = A z)
    (hL : ∀ z, L (z + k) = L z) (hR : ∀ z, R (z + l) = R z)
    (hLp : ∀ z, 0 ≤ z → z < k → A z = L z)
    (hRp : ∀ z, 0 ≤ z → z < l → A (k + z) = R z)
    (hS : ∀ z, -r ≤ z → z < s → L z = R z) (hs : 0 ≤ s) (hr : 0 ≤ r)
    (j : ℤ) (hj₀ : -r ≤ j) (hj₁ : j < k + s) : A j = L j := by
  by_cases h0 : 0 ≤ j
  · exact seam_forward k l hk hl s A L R hA hL hR hLp hRp
      (fun z hz₀ hz₁ => hS z (by omega) hz₁) j h0 hj₁
  let a := fun z : ℤ => A (k - 1 - z)
  let p := fun z : ℤ => L (k - 1 - z)
  let q := fun z : ℤ => R (l - 1 - z)
  have ha (z : ℤ) : a (z + (k + l)) = a z := by
    calc
      _ = A ((k - 1 - (z + (k + l))) + (k + l)) := (hA _).symm
      _ = _ := congrArg A (by omega)
  have hp (z : ℤ) : p (z + k) = p z := by
    calc
      _ = L ((k - 1 - (z + k)) + k) := (hL _).symm
      _ = _ := congrArg L (by omega)
  have hq (z : ℤ) : q (z + l) = q z := by
    calc
      _ = R ((l - 1 - (z + l)) + l) := (hR _).symm
      _ = _ := congrArg R (by omega)
  have hap (z : ℤ) (hz₀ : 0 ≤ z) (hz₁ : z < k) : a z = p z :=
    hLp _ (by omega) (by omega)
  have haq (z : ℤ) (hz₀ : 0 ≤ z) (hz₁ : z < l) : a (k + z) = q z := by
    calc
      _ = A ((k - 1 - (k + z)) + (k + l)) := (hA _).symm
      _ = A (k + (l - 1 - z)) := congrArg A (by omega)
      _ = _ := hRp _ (by omega) (by omega)
  have hpq (z : ℤ) (hz₀ : 0 ≤ z) (hz₁ : z < r) : p z = q z := by
    change L (k - 1 - z) = R (l - 1 - z)
    calc
      _ = L (-1 - z) := by rw [show k - 1 - z = -1 - z + k by omega, hL]
      _ = R (-1 - z) := hS _ (by omega) (by omega)
      _ = _ := by rw [show l - 1 - z = -1 - z + l by omega, hR]
  have h := seam_forward k l hk hl r a p q ha hp hq hap haq hpq (k - 1 - j)
    (by omega) (by omega)
  change A (k - 1 - (k - 1 - j)) = L (k - 1 - (k - 1 - j)) at h
  rwa [show k - 1 - (k - 1 - j) = j by omega] at h

private theorem seamAt_leftWindow {k l r : ℕ} (hk : 0 < k) (hl : 0 < l) {x : Word (k + l)}
    (hx : x ∈ LinearMap.ker (seam hk hl r)) (z : ℤ) (hz₀ : -(r : ℤ) ≤ z)
    (hz₁ : z < (k : ℤ) + 5) :
    seamAt (Nat.add_pos_left hk l) x z = seamAt hk (leftWord x) z := by
  exact seam_interval k l (by omega) (by omega) 5 r
    (seamAt (Nat.add_pos_left hk l) x) (seamAt hk (leftWord x)) (seamAt hl (rightWord x))
    (fun j => by simpa only [Int.natCast_add] using seamAt_period (Nat.add_pos_left hk l) x j)
    (seamAt_period hk _) (seamAt_period hl _) (seamAt_leftPart hk x) (seamAt_rightPart hk hl x)
    (seam_agree hk hl hx) (by omega) (by omega) z hz₀ hz₁

private theorem seamAt_rightWindow {k l r : ℕ} (hk : 0 < k) (hl : 0 < l) {x : Word (k + l)}
    (hx : x ∈ LinearMap.ker (seam hk hl r)) (z : ℤ) (hz₀ : -(r : ℤ) ≤ z)
    (hz₁ : z < (l : ℤ) + 5) :
    seamAt (Nat.add_pos_left hk l) x ((k : ℤ) + z) = seamAt hl (rightWord x) z := by
  let A := seamAt (Nat.add_pos_left hk l) x
  have hA (j : ℤ) : A (j + ((k : ℤ) + (l : ℤ))) = A j := by
    simpa only [A, Int.natCast_add] using seamAt_period (Nat.add_pos_left hk l) x j
  refine seam_interval l k (by omega) (by omega) 5 r (fun j => A ((k : ℤ) + j))
    (seamAt hl (rightWord x)) (seamAt hk (leftWord x)) ?_ (seamAt_period hl _)
    (seamAt_period hk _) (seamAt_rightPart hk hl x) ?_ ?_ (by omega) (by omega) z hz₀ hz₁
  · intro j
    rw [show (k : ℤ) + (j + ((l : ℤ) + (k : ℤ))) = ((k : ℤ) + j) + ((k : ℤ) + (l : ℤ))
      by omega, hA]
  · intro j hj₀ hj₁
    rw [show (k : ℤ) + ((l : ℤ) + j) = j + ((k : ℤ) + (l : ℤ)) by omega, hA]
    exact seamAt_leftPart hk x j hj₀ hj₁
  · intro j hj₀ hj₁
    exact (seam_agree hk hl hx j hj₀ hj₁).symm

private def seamInput (u : ℤ → Scalar) (b : Bool) (j : ℤ) : Scalar :=
  let g : ℤ := gap b
  let s : ℤ := spin b
  u (j - s) + u (j + g - s) + u (j - g - s)

private def seamQuad (u : ℤ → Scalar) (b : Bool) (j : ℤ) : Scalar :=
  seamInput u b (j + 1) * seamInput u b (j + 2)

private def seamBlend (u : ℤ → Scalar) (b : Bool) (j : ℤ) : Scalar :=
  let g : ℤ := gap b
  seamQuad u b j + seamQuad u b (j + g) + seamQuad u b (j - g)

private def seamTop (u : ℤ → Scalar) (b : Bool) (j : ℤ) : Scalar :=
  seamBlend u b (j + 1) * seamBlend u b (j + 2)

private theorem seam_top_eq {n : ℕ} (hn : 0 < n) (x : Word n) (b : Bool) (z : ℤ) :
    topWord hn x b (seamIndex hn z) = seamTop (seamAt hn x) b z := by
  simp only [topWord, mix, quadratic, linearInput, rotate, seamIndex_add, seamIndex_sub,
    seamTop, seamBlend, seamQuad, seamInput, seamAt]
  rfl

private theorem seamTop_translate (u : ℤ → Scalar) (b : Bool) (d z : ℤ) :
    seamTop u b (d + z) = seamTop (fun j => u (d + j)) b z := by
  simp only [seamTop, seamBlend, seamQuad, seamInput, add_assoc, Int.add_sub_assoc]

private theorem seamTop_congr (u v : ℤ → Scalar) (b : Bool) (z : ℤ)
    (h : ∀ j : ℤ, z - (if b then 5 else 1) ≤ j → j ≤ z + 5 → u j = v j) :
    seamTop u b z = seamTop v b z := by
  let g : ℤ := gap b
  let s : ℤ := spin b
  let m : ℤ := if b then 5 else 1
  have hg : 0 ≤ g := by dsimp [g]; omega
  change ∀ j : ℤ, z - m ≤ j → j ≤ z + 5 → u j = v j at h
  have hi (j : ℤ) (h₁ : z - m + s + g ≤ j) (h₂ : j ≤ z + 5 + s - g) :
      seamInput u b j = seamInput v b j := by
    change u (j - s) + u (j + g - s) + u (j - g - s) =
      v (j - s) + v (j + g - s) + v (j - g - s)
    rw [h (j - s) (by omega) (by omega), h (j + g - s) (by omega) (by omega),
      h (j - g - s) (by omega) (by omega)]
  have hq (j : ℤ) (h₁ : z - m + s + g - 1 ≤ j) (h₂ : j ≤ z + 5 + s - g - 2) :
      seamQuad u b j = seamQuad v b j := by
    unfold seamQuad
    rw [hi (j + 1) (by omega) (by omega), hi (j + 2) (by omega) (by omega)]
  have hm (j : ℤ) (h₁ : z - m + s + g - 1 + g ≤ j) (h₂ : j ≤ z + 5 + s - g - 2 - g) :
      seamBlend u b j = seamBlend v b j := by
    change seamQuad u b j + seamQuad u b (j + g) + seamQuad u b (j - g) =
      seamQuad v b j + seamQuad v b (j + g) + seamQuad v b (j - g)
    rw [hq j (by omega) (by omega), hq (j + g) (by omega) (by omega),
      hq (j - g) (by omega) (by omega)]
  have hb₁ : z - m + s + g - 1 + g ≤ z + 1 := by
    cases b <;> (dsimp [m, s, g, spin, gap]; omega)
  have hb₂ : z + 2 ≤ z + 5 + s - g - 2 - g := by
    cases b <;> (simp [s, g, spin, gap]; omega)
  unfold seamTop
  rw [hm (z + 1) hb₁ (by omega), hm (z + 2) (by omega) hb₂]

private theorem seam_radius {r : ℕ} (b : Bool) (hr : r = 1 ∨ r = 5)
    (hb : b = true → r = 5) : (if b then (5 : ℤ) else 1) ≤ (r : ℤ) := by
  cases b
  · rcases hr with h | h <;> simp [h]
  · simp [hb rfl]

private theorem seam_left {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (b : Bool) (i : Fin k)
    {r : ℕ} {x : Word (k + l)} (hx : x ∈ LinearMap.ker (seam hk hl r))
    (hr : r = 1 ∨ r = 5) (hb : b = true → r = 5) :
    topWord (Nat.add_pos_left hk l) x b (Fin.castAdd l i) = topWord hk (leftWord x) b i := by
  have hcenter : seamIndex (Nat.add_pos_left hk l) (i.val : ℤ) = Fin.castAdd l i :=
    seamIndex_center _ (Fin.castAdd l i)
  calc
    _ = seamTop (seamAt (Nat.add_pos_left hk l) x) b (i.val : ℤ) :=
      hcenter ▸ seam_top_eq (Nat.add_pos_left hk l) x b (i.val : ℤ)
    _ = seamTop (seamAt hk (leftWord x)) b (i.val : ℤ) := by
      apply seamTop_congr
      intro j hj₀ hj₁
      have hrad := seam_radius b hr hb
      have hi := i.isLt
      exact seamAt_leftWindow hk hl hx j (by omega) (by omega)
    _ = _ := (seam_top_eq hk (leftWord x) b (i.val : ℤ)).symm.trans
      (congrArg (topWord hk (leftWord x) b) (seamIndex_center hk i))

private theorem seam_right {k l : ℕ} (hk : 0 < k) (hl : 0 < l) (b : Bool) (i : Fin l)
    {r : ℕ} {x : Word (k + l)} (hx : x ∈ LinearMap.ker (seam hk hl r))
    (hr : r = 1 ∨ r = 5) (hb : b = true → r = 5) :
    topWord (Nat.add_pos_left hk l) x b (Fin.natAdd k i) = topWord hl (rightWord x) b i := by
  have hcenter : seamIndex (Nat.add_pos_left hk l) ((k : ℤ) + (i.val : ℤ)) = Fin.natAdd k i := by
    simpa only [Fin.val_natAdd, Int.natCast_add] using
      seamIndex_center (Nat.add_pos_left hk l) (Fin.natAdd k i)
  calc
    _ = seamTop (seamAt (Nat.add_pos_left hk l) x) b ((k : ℤ) + (i.val : ℤ)) :=
      hcenter ▸ seam_top_eq (Nat.add_pos_left hk l) x b ((k : ℤ) + (i.val : ℤ))
    _ = seamTop (fun j => seamAt (Nat.add_pos_left hk l) x ((k : ℤ) + j)) b (i.val : ℤ) :=
      seamTop_translate _ b _ _
    _ = seamTop (seamAt hl (rightWord x)) b (i.val : ℤ) := by
      apply seamTop_congr
      intro j hj₀ hj₁
      have hrad := seam_radius b hr hb
      have hi := i.isLt
      exact seamAt_rightWindow hk hl hx j (by omega) (by omega)
    _ = _ := (seam_top_eq hl (rightWord x) b (i.val : ℤ)).symm.trans
      (congrArg (topWord hl (rightWord x) b) (seamIndex_center hl i))

private def pairedRestrict {k l : ℕ} (U : Submodule Scalar (Word (k+l)))
    (A : Submodule Scalar (Word k)) (B : Submodule Scalar (Word l))
    (ha : ∀ x ∈ U, leftWord x ∈ A) (hb : ∀ x ∈ U, rightWord x ∈ B) :
    U →ₗ[Scalar] A × B :=
  (LinearMap.codRestrict A (leftWord.comp U.subtype) (fun x => ha x x.property)).prod
    (LinearMap.codRestrict B (rightWord.comp U.subtype) (fun x => hb x x.property))

private theorem pairedInjective {k l : ℕ} (U : Submodule Scalar (Word (k+l)))
    (A : Submodule Scalar (Word k)) (B : Submodule Scalar (Word l))
    (ha : ∀ x ∈ U, leftWord x ∈ A) (hb : ∀ x ∈ U, rightWord x ∈ B) :
    Function.Injective (pairedRestrict U A B ha hb) := by
  intro x y h
  apply Subtype.ext
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · exact congrArg (fun p : A × B => (p.1 : Word k) j) h
  · exact congrArg (fun p : A × B => (p.2 : Word l) j) h

private theorem rankProj {k l : ℕ} (U : Submodule Scalar (Word (k+l))) :
    Module.finrank Scalar U ≤
      Module.finrank Scalar (U.map leftWord) + Module.finrank Scalar (U.map rightWord) := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (pairedInjective U (U.map leftWord) (U.map rightWord)
      (fun x hx => ⟨x, hx, rfl⟩) (fun x hx => ⟨x, hx, rfl⟩))
  simpa only [Module.finrank_prod] using h

private def combine {k l : ℕ} (A : Submodule Scalar (Word k))
    (B : Submodule Scalar (Word l)) : Submodule Scalar (Word (k+l)) :=
  A.comap leftWord ⊓ B.comap rightWord

private theorem rankCombine {k l : ℕ} (A : Submodule Scalar (Word k))
    (B : Submodule Scalar (Word l)) :
    Module.finrank Scalar A + Module.finrank Scalar B ≤ Module.finrank Scalar (combine A B) := by
  let P := pairedRestrict (combine A B) A B (fun _ hx => hx.1) (fun _ hx => hx.2)
  have hs : Function.Surjective P := by
    rintro ⟨a, b⟩
    let x : Word (k+l) := Fin.addCases (a : Word k) (b : Word l)
    have ha : leftWord x = (a : Word k) := by ext j; simp [leftWord, x]
    have hb : rightWord x = (b : Word l) := by ext j; simp [rightWord, x]
    have hx : x ∈ combine A B := by
      change leftWord x ∈ A ∧ rightWord x ∈ B
      rw [ha, hb]
      exact ⟨a.property, b.property⟩
    exact ⟨⟨x, hx⟩, Prod.ext (Subtype.ext ha) (Subtype.ext hb)⟩
  simpa only [Module.finrank_prod] using LinearMap.finrank_le_finrank_of_surjective hs

private theorem rankWord (n : ℕ) : Module.finrank Scalar (Word n) = n := by simp

private theorem rankLoss {n m : ℕ} (M : Word n →ₗ[Scalar] Word m)
    (U : Submodule Scalar (Word n)) :
    Module.finrank Scalar U ≤ Module.finrank Scalar (U ⊓ LinearMap.ker M : Submodule Scalar (Word n)) + m := by
  let Q := M.comp U.subtype
  have hdim := LinearMap.finrank_range_add_finrank_ker Q
  have hr := Submodule.finrank_le (LinearMap.range Q)
  rw [rankWord] at hr
  let J : LinearMap.ker Q →ₗ[Scalar] (U ⊓ LinearMap.ker M : Submodule Scalar (Word n)) :=
    LinearMap.codRestrict _ (U.subtype.comp (LinearMap.ker Q).subtype)
      (fun x => ⟨x.val.property, LinearMap.mem_ker.mp x.property⟩)
  have hj : Function.Injective J := by
    intro x y h
    have he := congrArg (fun z : (U ⊓ LinearMap.ker M : Submodule Scalar (Word n)) =>
      (z : Word n)) h
    exact Subtype.ext (Subtype.ext he)
  have hker := LinearMap.finrank_le_finrank_of_injective hj
  omega

private theorem fourth_pull_map {n m : ℕ} (P : Word n →ₗ[Scalar] Word m)
    (U : Submodule Scalar (Word n)) (f : Word n → Scalar) (g : Word m → Scalar)
    (hfg : ∀ x ∈ U, f x = g (P x)) (v : Fin 4 → Word n) (hv : ∀ j, v j ∈ U) :
    fourthDifference f v 0 = fourthDifference g (fun j => P (v j)) 0 := by
  change differences f (List.ofFn v) 0 = _
  have h₁ := differences_eq_on (S := U.toAddSubgroup) (fun x hx => hfg x hx)
    (List.ofFn v) (fun w hw => by obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw; exact hv j)
    0 U.zero_mem
  have h₂ := differences_comp P.toAddMonoidHom 0 g (List.ofFn v) 0
  exact h₁.trans (by simpa [fourthDifference, List.map_ofFn, Function.comp_def] using h₂)

private theorem zeroAdmiss {n : ℕ} (hn : 0 < n) (a : Fin n → Bool × Bool) :
    Admiss hn a ⊥ := by
  intro b i _ v hv
  have hzero : v = fun _ => 0 := funext (fun j => by simpa using hv j)
  rw [hzero]
  change differences (fun y => topWord hn y b i) (List.ofFn (fun _ : Fin 4 => (0 : Word n))) 0 = 0
  simp [List.ofFn_succ, differences, delta]

private noncomputable def cycleCost {n : ℕ} (hn : 0 < n) (a : Fin n → Bool × Bool) : ℕ :=
  sInf {d : ℕ | ∀ name c₁ c₂, Fits hn a d name c₁ c₂}

private theorem costWitness {n : ℕ} (hn : 0 < n) (a : Fin n → Bool × Bool) :
    ∃ U : Submodule Scalar (Word n), Admiss hn a U ∧ n ≤ Module.finrank Scalar U + cycleCost hn a := by
  let S : Set ℕ := {d | ∀ name c₁ c₂, Fits hn a d name c₁ c₂}
  have hS : S.Nonempty := ⟨n, fun name c₁ c₂ => (fits_iff_admiss hn a n name c₁ c₂).2
    ⟨⊥, zeroAdmiss hn a, Nat.le_add_left _ _⟩⟩
  have hmem : sInf S ∈ S := Nat.sInf_mem hS
  exact (fits_iff_admiss hn a _ 0 0 0).1 (hmem 0 0 0)

private theorem costLE {n : ℕ} (hn : 0 < n) (a : Fin n → Bool × Bool) {d : ℕ}
    (U : Submodule Scalar (Word n)) (hU : Admiss hn a U)
    (hd : n ≤ Module.finrank Scalar U + d) : cycleCost hn a ≤ d := by
  apply Nat.sInf_le
  intro name c₁ c₂
  exact (fits_iff_admiss hn a d name c₁ c₂).2 ⟨U, hU, hd⟩

private theorem costLESub {n : ℕ} (hn : 0 < n) (a : Fin n → Bool × Bool)
    (U : Submodule Scalar (Word n)) (hU : Admiss hn a U) :
    cycleCost hn a ≤ n - Module.finrank Scalar U := by
  exact costLE hn a U hU (by omega)

private theorem admissProjection {n m : ℕ} {hn : 0 < n} {hm : 0 < m}
    {a : Fin n → Bool × Bool} {b : Fin m → Bool × Bool}
    {U : Submodule Scalar (Word n)} (hU : Admiss hn a U)
    (P : Word n →ₗ[Scalar] Word m) (ι : Fin m → Fin n)
    (hmark : ∀ c i, Marked b c i → Marked a c (ι i))
    (htop : ∀ c i, Marked b c i → ∀ x ∈ U, topWord hn x c (ι i) = topWord hm (P x) c i) :
    Admiss hm b (U.map P) := by
  classical
  intro c i hi v hv
  have hlift (j : Fin 4) : ∃ z ∈ U, P z = v j := Submodule.mem_map.mp (hv j)
  choose z hz hp using hlift
  have he := fourth_pull_map P U (fun x => topWord hn x c (ι i)) (fun x => topWord hm x c i)
    (htop c i hi) z hz
  rw [show (fun j => P (z j)) = v from funext hp] at he
  exact he.symm.trans (hU c (ι i) (hmark c i hi) z hz)

private theorem seamCost {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (a : Fin k → Bool × Bool) (b : Fin l → Bool × Bool) :
    let u := cycleCost hk a + cycleCost hl b
    let v := cycleCost (Nat.add_pos_left hk l) (Fin.addCases a b)
    let e : ℕ := if (∀ i, (a i).2 = false) ∧ (∀ j, (b j).2 = false) then 6 else 10
    u ≤ v + e ∧ v ≤ u + e := by
  classical
  let none := (∀ i, (a i).2 = false) ∧ (∀ j, (b j).2 = false)
  let r : ℕ := if none then 1 else 5
  let hj : 0 < k+l := Nat.add_pos_left hk l
  let S := LinearMap.ker (seam hk hl r)
  have hr : r = 1 ∨ r = 5 := by by_cases h : none <;> simp [r, h]
  have he : (if none then (6 : ℕ) else 10) = 5+r := by by_cases h : none <;> simp [r, h]
  have ham (c : Bool) (i : Fin k) : Marked (Fin.addCases a b) c (Fin.castAdd l i) ↔ Marked a c i := by
    simp only [Marked, Fin.addCases_left]
  have hbm (c : Bool) (i : Fin l) : Marked (Fin.addCases a b) c (Fin.natAdd k i) ↔ Marked b c i := by
    simp only [Marked, Fin.addCases_right]
  have hleft (c : Bool) (i : Fin k) (hi : Marked a c i) (x : Word (k+l)) (hx : x ∈ S) :
      topWord hj x c (Fin.castAdd l i) = topWord hk (leftWord x) c i := by
    have hc : c = true → r = 5 := by
      intro h
      subst c
      have ht : (a i).2 = true := hi
      have hn : ¬ none := fun h => Bool.noConfusion ((h.1 i).symm.trans ht)
      simp [r, hn]
    exact seam_left hk hl c i hx hr hc
  have hright (c : Bool) (i : Fin l) (hi : Marked b c i) (x : Word (k+l)) (hx : x ∈ S) :
      topWord hj x c (Fin.natAdd k i) = topWord hl (rightWord x) c i := by
    have hc : c = true → r = 5 := by
      intro h
      subst c
      have ht : (b i).2 = true := hi
      have hn : ¬ none := fun h => Bool.noConfusion ((h.2 i).symm.trans ht)
      simp [r, hn]
    exact seam_right hk hl c i hx hr hc
  change cycleCost hk a + cycleCost hl b ≤ cycleCost hj (Fin.addCases a b) + (if none then 6 else 10) ∧
    cycleCost hj (Fin.addCases a b) ≤ cycleCost hk a + cycleCost hl b + (if none then 6 else 10)
  rw [he]
  constructor
  · obtain ⟨T, hT, hd⟩ := costWitness hj (Fin.addCases a b)
    let U := T ⊓ S
    have hU : Admiss hj (Fin.addCases a b) U := fun c i hi v hv => hT c i hi v (fun j => (hv j).1)
    have ha := admissProjection hU leftWord (Fin.castAdd l) (fun c i => (ham c i).2)
      (fun c i hi x hx => hleft c i hi x hx.2)
    have hb := admissProjection hU rightWord (Fin.natAdd k) (fun c i => (hbm c i).2)
      (fun c i hi x hx => hright c i hi x hx.2)
    have hca := costLESub hk a _ ha
    have hcb := costLESub hl b _ hb
    have hda := Submodule.finrank_le (U.map leftWord)
    have hdb := Submodule.finrank_le (U.map rightWord)
    rw [rankWord] at hda hdb
    have hproj := rankProj U
    have hloss : Module.finrank Scalar T ≤ Module.finrank Scalar U + (5+r) := rankLoss (seam hk hl r) T
    omega
  · obtain ⟨A, hA, hdA⟩ := costWitness hk a
    obtain ⟨B, hB, hdB⟩ := costWitness hl b
    let U := combine A B ⊓ S
    have hU : Admiss hj (Fin.addCases a b) U := by
      intro c i
      refine Fin.addCases (fun j hi v hv => ?_) (fun j hi v hv => ?_) i
      · have ha := (ham c j).1 hi
        exact (fourth_pull_map leftWord U (fun x => topWord hj x c (Fin.castAdd l j))
          (fun x => topWord hk x c j) (fun x hx => hleft c j ha x hx.2) v hv).trans
            (hA c j ha (fun p => leftWord (v p)) (fun p => (hv p).1.1))
      · have hb := (hbm c j).1 hi
        exact (fourth_pull_map rightWord U (fun x => topWord hj x c (Fin.natAdd k j))
          (fun x => topWord hl x c j) (fun x hx => hright c j hb x hx.2) v hv).trans
            (hB c j hb (fun p => rightWord (v p)) (fun p => (hv p).1.2))
    have hrank := rankCombine A B
    have hloss : Module.finrank Scalar (combine A B) ≤ Module.finrank Scalar U + (5+r) :=
      rankLoss (seam hk hl r) (combine A B)
    exact costLE hj (Fin.addCases a b) (d := cycleCost hk a + cycleCost hl b + (5+r)) U hU (by omega)

end PEqualNP.Outside.L_meta_29744_aux

theorem PEqualNP.Outside.L_meta_29744 :
let fits := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2) =>
  let F := ZMod 2
  let W := Fin k → F
  let D := W →ₗ[F] F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let rot := fun (s : ℕ) (x : W) (i : Fin k) => x (ix (i.val + k - s % k))
  let mix := fun (g : ℕ) (x : W) (i : Fin k) =>
    x i + x (ix (i.val + g)) + x (ix (i.val + k - g % k))
  let step := fun (x : W) (i : Fin k) =>
    x i + (1 + x (ix (i.val + 1))) * x (ix (i.val + 2))
  let gap := fun b : Bool => if b then 2 else (1 : ℕ)
  let spin := fun b : Bool => if b then 3 else (1 : ℕ)
  let diff := fun (f : W → F) (u x : W) => f (x + u) - f x
  let fourth := fun (f : W → F) (v : Fin 4 → W) => (List.ofFn v).foldl diff f
  let cubic := fun (f : W → F) => ∀ v x, fourth f v x = 0
  let out := fun (x : W) (b : Bool) =>
    let z := mix (gap b) (rot (spin b) x + name b)
    let y := step z + rot (if b then 4 else 0) x + c₁ b
    step (mix (gap b) y) + rot (if b then 7 else 2) x + c₂ b
  let run := fun (ask : Fin d → ℕ → D) (x : W) =>
    (List.finRange d).foldl (fun h j =>
      2 * h + (if ask j h x = 0 then 0 else 1)) (0 : ℕ)
  ∃ (ask : Fin d → ℕ → D) (readout : ℕ → Bool → Fin k → W → F),
    (∀ h b i, cubic (readout h b i)) ∧
    ∀ x b i, (if b then (mark i).2 else (mark i).1) = true →
      out x b i = readout (run ask x) b i x
let cost := fun (k : ℕ) (hk : 0 < k) (mark : Fin k → Bool × Bool) =>
  sInf {d : ℕ | ∀ name c₁ c₂, fits k hk mark d name c₁ c₂}
∀ (k l : ℕ) (hk : 0 < k) (hl : 0 < l) (a : Fin k → Bool × Bool) (b : Fin l → Bool × Bool),
  let u := cost k hk a + cost l hl b
  let v := cost (k + l) (Nat.add_pos_left hk l) (Fin.addCases a b)
  let e : ℕ := if (∀ i, (a i).2 = false) ∧ (∀ j, (b j).2 = false) then 6 else 10
  u ≤ v + e ∧ v ≤ u + e := by
  intro fits cost k l hk hl a b
  exact PEqualNP.Outside.L_meta_29744_aux.seamCost hk hl a b
