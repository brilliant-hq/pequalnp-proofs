import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29770

abbrev F := ZMod 2
abbrev W (k : ℕ) := Fin k → F

def ix (k : ℕ) (hk : 0 < k) (n : ℕ) : Fin k := ⟨n % k, Nat.mod_lt _ hk⟩

def rot (k : ℕ) (hk : 0 < k) (s : ℕ) (x : W k) (i : Fin k) : F :=
  x (ix k hk (i.val + k - s % k))

def mix (k : ℕ) (hk : 0 < k) (g : ℕ) (x : W k) (i : Fin k) : F :=
  x i + x (ix k hk (i.val + g)) + x (ix k hk (i.val + k - g % k))

def step (k : ℕ) (hk : 0 < k) (x : W k) (i : Fin k) : F :=
  x i + (1 + x (ix k hk (i.val + 1))) * x (ix k hk (i.val + 2))

def diffG {U : Type*} [AddCommGroup U] (f : U → F) (u x : U) : F := f (x + u) - f x

def fourthG {U : Type*} [AddCommGroup U] (f : U → F) (v : Fin 4 → U) : U → F :=
  (List.ofFn v).foldl diffG f

def cubicG {U : Type*} [AddCommGroup U] (f : U → F) : Prop := ∀ v x, fourthG f v x = 0

def zFun (k : ℕ) (hk : 0 < k) (x : W k) (n : ℕ) : F :=
  x (ix k hk n) + x (ix k hk (n + k - 1)) + x (ix k hk (n + 2 * k - 2))

def partsFun (k : ℕ) (hk : 0 < k) (i : Fin k) (x : W k) (t : Fin 4) : F :=
  let atZ := fun n : ℕ => zFun k hk x (i.val + n)
  if t.val = 0 then atZ 2 else if t.val = 1 then atZ 4 else
    if t.val = 2 then atZ 1 + atZ 3 else atZ 3 + atZ 5

def unitVec (k : ℕ) (j h : Fin k) : F := if h = j then 1 else 0

def formFun (k : ℕ) (hk : 0 < k) (i : Fin k) (a : Fin 4 → F) (j : Fin k) : F :=
  ∑ t, a t * partsFun k hk i (unitVec k j) t

def outFalse (k : ℕ) (hk : 0 < k) (name c₁ c₂ : Bool → Fin k → F) (x : W k) : Fin k → F :=
  let z := mix k hk 1 (rot k hk 1 x + name false)
  let y := step k hk z + rot k hk 0 x + c₁ false
  step k hk (mix k hk 1 y) + rot k hk 2 x + c₂ false

def runFn {k : ℕ} (d : ℕ) (ask : Fin d → ℕ → (W k →ₗ[F] F)) (x : W k) : ℕ :=
  (List.finRange d).foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0

lemma zmod2_mul_self (a : F) : a * a = a := by
  fin_cases a <;> rfl

lemma zmod2_sub_eq_add (a b : F) : a - b = a + b := by
  fin_cases a <;> fin_cases b <;> rfl

lemma zmod2_add_self (a : F) : a + a = 0 := by
  fin_cases a <;> rfl

def Deg (k : ℕ) : ℕ → Submodule F (W k → F)
  | 0 => Submodule.span F {fun _ => 1}
  | d + 1 =>
    Deg k d ⊔
      Submodule.span F {f | ∃ (L : W k →ₗ[F] F) (g : W k → F), g ∈ Deg k d ∧ f = fun x => L x * g x}

lemma deg_mono (k d : ℕ) : Deg k d ≤ Deg k (d + 1) := le_sup_left

lemma one_mem_deg (k : ℕ) : ∀ d, (fun _ : W k => (1 : F)) ∈ Deg k d
  | 0 => Submodule.subset_span rfl
  | d + 1 => deg_mono k d (one_mem_deg k d)

lemma const_mem_deg (k d : ℕ) (c : F) : (fun _ : W k => c) ∈ Deg k d := by
  have h : (fun _ : W k => c) = c • (fun _ : W k => (1 : F)) := by
    ext x; simp
  rw [h]
  exact Submodule.smul_mem _ c (one_mem_deg k d)

lemma mul_linear_mem_deg {k d : ℕ} (L : W k →ₗ[F] F) {g : W k → F} (hg : g ∈ Deg k d) :
    (fun x => L x * g x) ∈ Deg k (d + 1) :=
  Submodule.mem_sup_right (Submodule.subset_span ⟨L, g, hg, rfl⟩)

lemma linear_mem_deg {k d : ℕ} (L : W k →ₗ[F] F) : (fun x => L x) ∈ Deg k (d + 1) := by
  have h : (fun x => L x) = (fun x => L x * (fun _ : W k => (1 : F)) x) := by
    ext x; simp
  rw [h]
  exact mul_linear_mem_deg L (one_mem_deg k d)

lemma deg_le_of_le {k a b : ℕ} (h : a ≤ b) : Deg k a ≤ Deg k b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (deg_mono k _)

lemma mul_deg_mem_deg {k : ℕ} : ∀ {a b : ℕ} {f g : W k → F},
    f ∈ Deg k a → g ∈ Deg k b → (fun x => f x * g x) ∈ Deg k (a + b)
  | 0, b, f, g, hf, hg => by
    rw [Deg, Submodule.mem_span_singleton] at hf
    rcases hf with ⟨c, rfl⟩
    have h : (fun x => (c • fun _ : W k => (1 : F)) x * g x) = c • g := by
      ext x; simp
    rw [h, Nat.zero_add]
    exact Submodule.smul_mem _ c hg
  | a + 1, b, f, g, hf, hg => by
    let mulG : (W k → F) →ₗ[F] (W k → F) :=
      { toFun := fun h x => h x * g x
        map_add' := fun u v => by ext x; simp [add_mul]
        map_smul' := fun c u => by ext x; simp [mul_assoc] }
    let P : Submodule F (W k → F) := (Deg k (a + 1 + b)).comap mulG
    have hle : Deg k (a + 1) ≤ P := by
      refine sup_le ?_ (Submodule.span_le.mpr ?_)
      · intro u hu
        change (fun x => u x * g x) ∈ Deg k (a + 1 + b)
        have hm := mul_deg_mem_deg hu hg
        have hle' : a + b ≤ a + 1 + b := by omega
        exact deg_le_of_le hle' hm
      · rintro _ ⟨L, h, hh, rfl⟩
        change (fun x => (L x * h x) * g x) ∈ Deg k (a + 1 + b)
        have h1 : (fun x => (L x * h x) * g x) = (fun x => L x * (fun y => h y * g y) x) := by
          ext x; ring
        rw [h1, show a + 1 + b = a + b + 1 by omega]
        exact mul_linear_mem_deg L (mul_deg_mem_deg hh hg)
    exact hle hf

def diffLM {k : ℕ} (u : W k) : (W k → F) →ₗ[F] (W k → F) where
  toFun f := diffG f u
  map_add' f g := by ext x; simp [diffG]; ring
  map_smul' c f := by ext x; simp [diffG]; ring

lemma diff_deg_zero {k : ℕ} (u : W k) {f : W k → F} (hf : f ∈ Deg k 0) :
    diffG f u = 0 := by
  rw [Deg, Submodule.mem_span_singleton] at hf
  rcases hf with ⟨c, rfl⟩
  ext x
  simp [diffG]

lemma diff_deg_succ {k : ℕ} (u : W k) : ∀ {d : ℕ} {f : W k → F},
    f ∈ Deg k (d + 1) → diffG f u ∈ Deg k d
  | d, f, hf => by
    let P : Submodule F (W k → F) := (Deg k d).comap (diffLM u)
    have hle : Deg k (d + 1) ≤ P := by
      refine sup_le ?_ (Submodule.span_le.mpr ?_)
      · cases d with
        | zero =>
          intro h hh
          change diffG h u ∈ Deg k 0
          rw [diff_deg_zero u hh]
          exact Submodule.zero_mem _
        | succ d' =>
          intro h hh
          change diffG h u ∈ Deg k (d' + 1)
          exact deg_mono k d' (diff_deg_succ u hh)
      · rintro _ ⟨L, g, hg, rfl⟩
        change diffG (fun x => L x * g x) u ∈ Deg k d
        have hdiff : diffG (fun x => L x * g x) u =
            L u • g + L u • diffG g u + (fun x => L x * diffG g u x) := by
          ext x
          simp only [diffG, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]
          ring
        rw [hdiff]
        cases d with
        | zero =>
          rw [diff_deg_zero u hg]
          have h1 : L u • (0 : W k → F) = 0 := by simp
          have h2 : (fun x : W k => L x * (0 : W k → F) x) = 0 := by ext x; simp
          rw [h1, h2]
          exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hg)
            (Submodule.zero_mem _)) (Submodule.zero_mem _)
        | succ d' =>
          have hdg : diffG g u ∈ Deg k d' := diff_deg_succ u hg
          exact Submodule.add_mem _
            (Submodule.add_mem _ (Submodule.smul_mem _ _ hg)
              (Submodule.smul_mem _ _ (deg_mono k d' hdg)))
            (mul_linear_mem_deg L hdg)
    exact hle hf

lemma fourth_eq_fold {U : Type*} [AddCommGroup U] (f : U → F) (v : Fin 4 → U) :
    fourthG f v = diffG (diffG (diffG (diffG f (v 0)) (v 1)) (v 2)) (v 3) := by
  unfold fourthG
  simp [List.ofFn_succ]

lemma cubic_of_mem_deg3 {k : ℕ} {f : W k → F} (hf : f ∈ Deg k 3) : cubicG f := by
  intro v x
  rw [fourth_eq_fold]
  have h2 : diffG f (v 0) ∈ Deg k 2 := diff_deg_succ (v 0) hf
  have h1 : diffG (diffG f (v 0)) (v 1) ∈ Deg k 1 := diff_deg_succ (v 1) h2
  have h0 : diffG (diffG (diffG f (v 0)) (v 1)) (v 2) ∈ Deg k 0 := diff_deg_succ (v 2) h1
  rw [diff_deg_zero (v 3) h0]
  rfl

lemma fourthLM_linear {U : Type*} [AddCommGroup U] (v : Fin 4 → U) :
    ∀ f g : U → F, fourthG (f - g) v = fourthG f v - fourthG g v := by
  intro f g
  rw [fourth_eq_fold, fourth_eq_fold, fourth_eq_fold]
  have hsub : ∀ (u : U) (a b : U → F), diffG (a - b) u = diffG a u - diffG b u := by
    intro u a b
    ext x
    simp [diffG]
    ring
  rw [hsub, hsub, hsub, hsub]

lemma cubic_sub {U : Type*} [AddCommGroup U] {f g : U → F} (hf : cubicG f) (hg : cubicG g) :
    cubicG (f - g) := by
  intro v x
  have h := congrFun (fourthLM_linear v f g) x
  simp only [Pi.sub_apply] at h
  rw [h, hf v x, hg v x, sub_self]

lemma cubic_add {U : Type*} [AddCommGroup U] {f g : U → F} (hf : cubicG f) (hg : cubicG g) :
    cubicG (f + g) := by
  have h : f + g = f - (fun x => -g x) := by
    ext x; simp [sub_eq_add_neg]
  rw [h]
  refine cubic_sub hf ?_
  intro v x
  have h0 : (fun x => -g x) = (0 : U → F) - g := by ext y; simp
  rw [h0]
  have h1 := congrFun (fourthLM_linear v 0 g) x
  simp only [Pi.sub_apply] at h1
  have hz : fourthG (0 : U → F) v x = 0 := by
    rw [fourth_eq_fold]
    have hd : ∀ u, diffG (0 : U → F) u = 0 := fun u => by ext y; simp [diffG]
    rw [hd, hd, hd, hd]
    rfl
  rw [h1, hz, hg v x, sub_self]

lemma cubic_zero {U : Type*} [AddCommGroup U] : cubicG (0 : U → F) := by
  intro v x
  rw [fourth_eq_fold]
  have hd : ∀ u, diffG (0 : U → F) u = 0 := fun u => by ext y; simp [diffG]
  rw [hd, hd, hd, hd]
  rfl

lemma ix_mod (k : ℕ) (hk : 0 < k) (n : ℕ) : ix k hk (n % k) = ix k hk n := by
  ext
  simp [ix]

lemma ix_add_left (k : ℕ) (hk : 0 < k) (a b : ℕ) :
    ix k hk (a % k + b) = ix k hk (a + b) := by
  ext
  simp [ix, Nat.add_mod]

lemma ix_sub_one_eq (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ix k hk (n % k + k - 1 % k) = ix k hk (n + k - 1) := by
  ext
  simp only [ix]
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 < k := by omega
    rw [Nat.mod_eq_of_lt h1]
    have ha : n % k + k - 1 = n % k + (k - 1) := by omega
    have hb : n + k - 1 = n + (k - 1) := by omega
    rw [ha, hb, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

lemma ix_add_one_sub_one (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ix k hk ((n + 1) % k + k - 1 % k) = ix k hk n := by
  ext
  simp only [ix]
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 < k := by omega
    rw [Nat.mod_eq_of_lt h1]
    have ha : (n + 1) % k + k - 1 = (n + 1) % k + (k - 1) := by omega
    rw [ha, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
    have hb : n + 1 + (k - 1) = n + k := by omega
    rw [hb, Nat.add_mod_right]

lemma ix_sub_one_sub_one (k : ℕ) (hk : 0 < k) (n : ℕ) :
    ix k hk ((n % k + k - 1 % k) % k + k - 1 % k) = ix k hk (n + 2 * k - 2) := by
  ext
  simp only [ix]
  by_cases hk1 : k = 1
  · subst hk1; simp
  · have h1 : 1 < k := by omega
    rw [Nat.mod_eq_of_lt h1]
    have ha : n % k + k - 1 = n % k + (k - 1) := by omega
    have hb : (n % k + (k - 1)) % k + k - 1 = (n % k + (k - 1)) % k + (k - 1) := by omega
    have hc : n + 2 * k - 2 = n + (k - 1) + (k - 1) := by omega
    rw [ha, hb, hc, Nat.mod_add_mod, Nat.add_assoc, Nat.mod_add_mod, ← Nat.add_assoc]

lemma mix_one_rot_one (k : ℕ) (hk : 0 < k) (x : W k) (n : ℕ) :
    mix k hk 1 (rot k hk 1 x) (ix k hk n) = zFun k hk x n := by
  unfold mix rot zFun
  have h0 : ix k hk ((ix k hk n).val + k - 1 % k) = ix k hk (n + k - 1) :=
    ix_sub_one_eq k hk n
  have h1 : ix k hk ((ix k hk ((ix k hk n).val + 1)).val + k - 1 % k) = ix k hk n := by
    change ix k hk ((n % k + 1) % k + k - 1 % k) = ix k hk n
    rw [Nat.mod_add_mod]
    exact ix_add_one_sub_one k hk n
  have h2 : ix k hk ((ix k hk ((ix k hk n).val + k - 1 % k)).val + k - 1 % k) =
      ix k hk (n + 2 * k - 2) := by
    change ix k hk ((n % k + k - 1 % k) % k + k - 1 % k) = ix k hk (n + 2 * k - 2)
    exact ix_sub_one_sub_one k hk n
  rw [h2, h0, h1]
  ring

lemma mix_one_add (k : ℕ) (hk : 0 < k) (u v : W k) (i : Fin k) :
    mix k hk 1 (u + v) i = mix k hk 1 u i + mix k hk 1 v i := by
  simp only [mix, Pi.add_apply]
  ring

def zLM (k : ℕ) (hk : 0 < k) (n : ℕ) : W k →ₗ[F] F where
  toFun x := zFun k hk x n
  map_add' x y := by simp only [zFun, Pi.add_apply]; ring
  map_smul' c x := by simp only [zFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def coordLM (k : ℕ) (j : Fin k) : W k →ₗ[F] F where
  toFun x := x j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma step_z_diff_deg1 (k : ℕ) (hk : 0 < k) (name c₁ : Bool → Fin k → F) (n : ℕ) :
    (fun x : W k =>
      (step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk n) +
        rot k hk 0 x (ix k hk n) + c₁ false (ix k hk n)) -
      zLM k hk (n + 1) x * zLM k hk (n + 2) x) ∈ Deg k 1 := by
  let c0 : ℕ → F := fun m => mix k hk 1 (name false) (ix k hk m)
  have h1 : ∀ x : W k,
      mix k hk 1 (rot k hk 1 x + name false) (ix k hk (n % k + 1)) =
      zLM k hk (n + 1) x + c0 (n + 1) := by
    intro x
    have hix : ix k hk (n % k + 1) = ix k hk (n + 1) := ix_add_left k hk n 1
    rw [hix, mix_one_add, mix_one_rot_one]
    rfl
  have h2 : ∀ x : W k,
      mix k hk 1 (rot k hk 1 x + name false) (ix k hk (n % k + 2)) =
      zLM k hk (n + 2) x + c0 (n + 2) := by
    intro x
    have hix : ix k hk (n % k + 2) = ix k hk (n + 2) := ix_add_left k hk n 2
    rw [hix, mix_one_add, mix_one_rot_one]
    rfl
  have h0 : ∀ x : W k,
      mix k hk 1 (rot k hk 1 x + name false) (ix k hk n) =
      zLM k hk n x + c0 n := by
    intro x
    rw [mix_one_add, mix_one_rot_one]
    rfl
  let rot0LM : W k →ₗ[F] F := coordLM k (ix k hk ((ix k hk n).val + k - 0 % k))
  let Llin : W k →ₗ[F] F :=
    zLM k hk n + (1 + c0 (n + 1)) • zLM k hk (n + 2) + c0 (n + 2) • zLM k hk (n + 1) + rot0LM
  let Kconst : F := c0 n + (1 + c0 (n + 1)) * c0 (n + 2) + c₁ false (ix k hk n)
  have heq : (fun x : W k =>
      (step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk n) +
        rot k hk 0 x (ix k hk n) + c₁ false (ix k hk n)) -
      zLM k hk (n + 1) x * zLM k hk (n + 2) x) =
      (fun x => Llin x) + (fun _ => Kconst) := by
    ext x
    simp only [step, rot, ix, zLM, Llin, Kconst, rot0LM, coordLM, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
    have ha := h0 x
    have hb := h1 x
    have hc := h2 x
    simp only [ix, zLM, LinearMap.coe_mk, AddHom.coe_mk] at ha hb hc
    rw [ha, hb, hc]
    ring
  rw [heq]
  exact Submodule.add_mem _ (linear_mem_deg Llin) (const_mem_deg k 1 Kconst)

lemma step_z_mem_deg2 (k : ℕ) (hk : 0 < k) (name c₁ : Bool → Fin k → F) (n : ℕ) :
    (fun x : W k =>
      step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk n) +
        rot k hk 0 x (ix k hk n) + c₁ false (ix k hk n)) ∈ Deg k 2 := by
  have h1 := step_z_diff_deg1 k hk name c₁ n
  have h2 : (fun x : W k => zLM k hk (n + 1) x * zLM k hk (n + 2) x) ∈ Deg k 2 :=
    mul_linear_mem_deg (zLM k hk (n + 1)) (linear_mem_deg (zLM k hk (n + 2)))
  have h3 := Submodule.add_mem (Deg k 2) (deg_mono k 1 h1) h2
  have heq : (fun x : W k =>
      step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk n) +
        rot k hk 0 x (ix k hk n) + c₁ false (ix k hk n)) =
      (fun x : W k =>
        (step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk n) +
          rot k hk 0 x (ix k hk n) + c₁ false (ix k hk n)) -
        zLM k hk (n + 1) x * zLM k hk (n + 2) x) +
      (fun x : W k => zLM k hk (n + 1) x * zLM k hk (n + 2) x) := by
    ext x; simp
  rw [heq]
  exact h3

def yFalse (k : ℕ) (hk : 0 < k) (name c₁ : Bool → Fin k → F) (x : W k) : W k :=
  step k hk (mix k hk 1 (rot k hk 1 x + name false)) + rot k hk 0 x + c₁ false

lemma mix_y_quad (k : ℕ) (hk : 0 < k) (name c₁ : Bool → Fin k → F) (m' : ℕ) :
    (fun x : W k =>
      mix k hk 1 (yFalse k hk name c₁ x) (ix k hk (m' + 1)) -
        (zLM k hk (m' + 1) x * zLM k hk (m' + 2) x +
         zLM k hk (m' + 2) x * zLM k hk (m' + 3) x +
         zLM k hk (m' + 3) x * zLM k hk (m' + 4) x)) ∈ Deg k 1 := by
  have hm1 := step_z_diff_deg1 k hk name c₁ (m' + 1)
  have hm2 := step_z_diff_deg1 k hk name c₁ (m' + 2)
  have hm0 := step_z_diff_deg1 k hk name c₁ m'
  have hsum := Submodule.add_mem (Deg k 1) (Submodule.add_mem (Deg k 1) hm1 hm2) hm0
  have heq : (fun x : W k =>
      mix k hk 1 (yFalse k hk name c₁ x) (ix k hk (m' + 1)) -
        (zLM k hk (m' + 1) x * zLM k hk (m' + 2) x +
         zLM k hk (m' + 2) x * zLM k hk (m' + 3) x +
         zLM k hk (m' + 3) x * zLM k hk (m' + 4) x)) =
      (fun x : W k =>
        ((step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk (m' + 1)) +
            rot k hk 0 x (ix k hk (m' + 1)) + c₁ false (ix k hk (m' + 1))) -
          zLM k hk (m' + 2) x * zLM k hk (m' + 3) x) +
        ((step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk (m' + 2)) +
            rot k hk 0 x (ix k hk (m' + 2)) + c₁ false (ix k hk (m' + 2))) -
          zLM k hk (m' + 3) x * zLM k hk (m' + 4) x) +
        ((step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk m') +
            rot k hk 0 x (ix k hk m') + c₁ false (ix k hk m')) -
          zLM k hk (m' + 1) x * zLM k hk (m' + 2) x)) := by
    ext x
    simp only [yFalse, mix, Pi.add_apply]
    have hix1 : ix k hk ((ix k hk (m' + 1)).val + 1) = ix k hk (m' + 2) := ix_add_left k hk (m' + 1) 1
    have hix2 : ix k hk ((ix k hk (m' + 1)).val + k - 1 % k) = ix k hk m' := ix_add_one_sub_one k hk m'
    rw [hix1, hix2]
    ring
  rw [heq]
  exact hsum

lemma mix_y_mem_deg2 (k : ℕ) (hk : 0 < k) (name c₁ : Bool → Fin k → F) (i : Fin k) :
    (fun x : W k => mix k hk 1 (yFalse k hk name c₁ x) i) ∈ Deg k 2 := by
  have h1 := step_z_mem_deg2 k hk name c₁ i.val
  have h2 := step_z_mem_deg2 k hk name c₁ (i.val + 1)
  have h3 := step_z_mem_deg2 k hk name c₁ (i.val + k - 1 % k)
  have heq : (fun x : W k => mix k hk 1 (yFalse k hk name c₁ x) i) =
      (fun x : W k =>
        (step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk i.val) +
          rot k hk 0 x (ix k hk i.val) + c₁ false (ix k hk i.val)) +
        (step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk (i.val + 1)) +
          rot k hk 0 x (ix k hk (i.val + 1)) + c₁ false (ix k hk (i.val + 1))) +
        (step k hk (mix k hk 1 (rot k hk 1 x + name false)) (ix k hk (i.val + k - 1 % k)) +
          rot k hk 0 x (ix k hk (i.val + k - 1 % k)) + c₁ false (ix k hk (i.val + k - 1 % k)))) := by
    ext x
    have hi : ix k hk i.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    simp only [yFalse, mix, Pi.add_apply, hi]
  rw [heq]
  exact Submodule.add_mem _ (Submodule.add_mem _ h1 h2) h3

lemma quartic_zmod2_id (a b c d e : F) :
    (a * b + b * c + c * d) * (b * c + c * d + d * e) - b * d * (a + c) * (c + e) =
      a * b * c + b * c + b * c * d + c * d + c * d * e := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> fin_cases e <;> rfl

lemma out_sub_prod_cubic (k : ℕ) (hk : 0 < k) (name c₁ c₂ : Bool → Fin k → F) (i : Fin k) :
    cubicG (fun x : W k => outFalse k hk name c₁ c₂ x i - ∏ t : Fin 4, partsFun k hk i x t) := by
  refine cubic_of_mem_deg3 ?_
  let m0 : W k → F := fun x => mix k hk 1 (yFalse k hk name c₁ x) i
  let m1 : W k → F := fun x => mix k hk 1 (yFalse k hk name c₁ x) (ix k hk (i.val + 1))
  let m2 : W k → F := fun x => mix k hk 1 (yFalse k hk name c₁ x) (ix k hk (i.val + 2))
  let a := zLM k hk (i.val + 1)
  let b := zLM k hk (i.val + 2)
  let c := zLM k hk (i.val + 3)
  let d := zLM k hk (i.val + 4)
  let e := zLM k hk (i.val + 5)
  let q1 : W k → F := fun x => a x * b x + b x * c x + c x * d x
  let q2 : W k → F := fun x => b x * c x + c x * d x + d x * e x
  have hq1_deg : q1 ∈ Deg k 2 :=
    Submodule.add_mem _
      (Submodule.add_mem _
        (mul_linear_mem_deg a (linear_mem_deg b))
        (mul_linear_mem_deg b (linear_mem_deg c)))
      (mul_linear_mem_deg c (linear_mem_deg d))
  have hq2_deg : q2 ∈ Deg k 2 :=
    Submodule.add_mem _
      (Submodule.add_mem _
        (mul_linear_mem_deg b (linear_mem_deg c))
        (mul_linear_mem_deg c (linear_mem_deg d)))
      (mul_linear_mem_deg d (linear_mem_deg e))
  have hm1_diff : (fun x => m1 x - q1 x) ∈ Deg k 1 :=
    mix_y_quad k hk name c₁ i.val
  have hm2_diff : (fun x => m2 x - q2 x) ∈ Deg k 1 :=
    mix_y_quad k hk name c₁ (i.val + 1)
  have hm0_deg : m0 ∈ Deg k 2 :=
    mix_y_mem_deg2 k hk name c₁ i
  have hm2_deg : m2 ∈ Deg k 2 :=
    mix_y_mem_deg2 k hk name c₁ (ix k hk (i.val + 2))
  have hm12_diff : (fun x : W k => m1 x * m2 x - q1 x * q2 x) ∈ Deg k 3 := by
    have heq : (fun x : W k => m1 x * m2 x - q1 x * q2 x) =
        (fun x : W k => (m1 x - q1 x) * m2 x + q1 x * (m2 x - q2 x)) := by
      ext x; ring
    rw [heq]
    have t1 := mul_deg_mem_deg hm1_diff hm2_deg
    have t2 := mul_deg_mem_deg hq1_deg hm2_diff
    rw [show (1 : ℕ) + 2 = 3 by omega] at t1
    rw [show (2 : ℕ) + 1 = 3 by omega] at t2
    exact Submodule.add_mem _ t1 t2
  have hprod : ∀ x : W k, (∏ t : Fin 4, partsFun k hk i x t) =
      b x * d x * (a x + c x) * (c x + e x) := by
    intro x
    rw [Fin.prod_univ_four]
    simp [partsFun, a, b, c, d, e, zLM]
  have hqprod : (fun x : W k => q1 x * q2 x - ∏ t : Fin 4, partsFun k hk i x t) ∈ Deg k 3 := by
    simp_rw [hprod]
    have heq : (fun x : W k => q1 x * q2 x - b x * d x * (a x + c x) * (c x + e x)) =
        (fun x : W k => a x * b x * c x + b x * c x + b x * c x * d x + c x * d x + c x * d x * e x) := by
      ext x
      exact quartic_zmod2_id (a x) (b x) (c x) (d x) (e x)
    rw [heq]
    have d3 : ∀ L1 L2 L3 : W k →ₗ[F] F, (fun x => L1 x * L2 x * L3 x) ∈ Deg k 3 := fun L1 L2 L3 => by
      have h := mul_linear_mem_deg L3 (mul_linear_mem_deg L1 (linear_mem_deg (d := 0) L2))
      have heq' : (fun x => L1 x * L2 x * L3 x) = (fun x => L3 x * (L1 x * L2 x)) := by
        ext x; ring
      rw [heq']
      exact h
    have d2 : ∀ L1 L2 : W k →ₗ[F] F, (fun x => L1 x * L2 x) ∈ Deg k 3 := fun L1 L2 =>
      deg_mono k 2 (mul_linear_mem_deg L1 (linear_mem_deg (d := 0) L2))
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
      (d3 a b c) (d2 b c)) (d3 b c d)) (d2 c d)) (d3 c d e)
  have hrot2 : (fun x : W k => rot k hk 2 x i + c₂ false i) ∈ Deg k 3 := by
    let r2 : W k →ₗ[F] F := coordLM k (ix k hk (i.val + k - 2 % k))
    have heq : (fun x : W k => rot k hk 2 x i + c₂ false i) =
        (fun x => r2 x) + (fun _ => c₂ false i) := rfl
    rw [heq]
    exact deg_le_of_le (by omega : 1 ≤ 3) (Submodule.add_mem _ (linear_mem_deg r2) (const_mem_deg k 1 _))
  have hfinal : (fun x : W k => outFalse k hk name c₁ c₂ x i - ∏ t : Fin 4, partsFun k hk i x t) =
      (fun x : W k =>
        m0 x + m2 x + (rot k hk 2 x i + c₂ false i) +
        (m1 x * m2 x - q1 x * q2 x) +
        (q1 x * q2 x - ∏ t : Fin 4, partsFun k hk i x t)) := by
    ext x
    have hout : outFalse k hk name c₁ c₂ x i =
        m0 x + (1 + m1 x) * m2 x + rot k hk 2 x i + c₂ false i := by
      dsimp only [outFalse, m0, m1, m2]
      change step k hk (mix k hk 1 (yFalse k hk name c₁ x)) i + rot k hk 2 x i + c₂ false i = _
      rw [step]
    rw [hout]
    ring
  rw [hfinal]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (deg_mono k 2 hm0_deg) (deg_mono k 2 hm2_deg)) hrot2) hm12_diff) hqprod

def partsCoordLM (k : ℕ) (hk : 0 < k) (i : Fin k) (t : Fin 4) : W k →ₗ[F] F :=
  if t.val = 0 then zLM k hk (i.val + 2)
  else if t.val = 1 then zLM k hk (i.val + 4)
  else if t.val = 2 then zLM k hk (i.val + 1) + zLM k hk (i.val + 3)
  else zLM k hk (i.val + 3) + zLM k hk (i.val + 5)

lemma partsCoordLM_apply (k : ℕ) (hk : 0 < k) (i : Fin k) (t : Fin 4) (x : W k) :
    partsCoordLM k hk i t x = partsFun k hk i x t := by
  fin_cases t <;> rfl

def partsLM (k : ℕ) (hk : 0 < k) (i : Fin k) : W k →ₗ[F] (Fin 4 → F) :=
  LinearMap.pi (partsCoordLM k hk i)

lemma partsLM_apply (k : ℕ) (hk : 0 < k) (i : Fin k) (x : W k) :
    partsLM k hk i x = partsFun k hk i x := by
  ext t
  exact partsCoordLM_apply k hk i t x

def dotLM (k : ℕ) (u : W k) : W k →ₗ[F] F where
  toFun x := ∑ j : Fin k, x j * u j
  map_add' x y := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

lemma vec_eq_sum_unit (k : ℕ) (x : W k) : x = ∑ j : Fin k, x j • unitVec k j := by
  ext h
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVec, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

def vecToDual (k : ℕ) : W k ≃ₗ[F] (W k →ₗ[F] F) where
  toFun := dotLM k
  invFun L j := L (unitVec k j)
  map_add' u v := by
    apply LinearMap.ext
    intro x
    simp only [dotLM, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
  map_smul' c u := by
    apply LinearMap.ext
    intro x
    simp only [dotLM, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply,
      smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  left_inv u := by
    ext j
    simp only [dotLM, LinearMap.coe_mk, AddHom.coe_mk, unitVec, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  right_inv L := by
    apply LinearMap.ext
    intro x
    simp only [dotLM, LinearMap.coe_mk, AddHom.coe_mk]
    conv_rhs => rw [vec_eq_sum_unit k x]
    simp only [map_sum, map_smul, smul_eq_mul]

lemma dotLM_formFun (k : ℕ) (hk : 0 < k) (i : Fin k) (a : Fin 4 → F) (x : W k) :
    dotLM k (formFun k hk i a) x = ∑ t : Fin 4, a t * partsFun k hk i x t := by
  simp only [dotLM, LinearMap.coe_mk, AddHom.coe_mk, formFun, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hlin : partsFun k hk i x t = ∑ j : Fin k, x j * partsFun k hk i (unitVec k j) t := by
    rw [← partsCoordLM_apply]
    conv_lhs => rw [vec_eq_sum_unit k x]
    simp only [map_sum, map_smul, smul_eq_mul, partsCoordLM_apply]
  rw [hlin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma cubic_restrict {U : Type*} [AddCommGroup U] [Module F U]
    (V : Submodule F U) {f : U → F} (hf : cubicG f) :
    cubicG (fun y : V => f y.1) := by
  intro v x
  have h : fourthG (fun y : V => f y.1) v x = fourthG f (fun t => (v t).1) x.1 := by
    simp only [fourth_eq_fold]
    rfl
  rw [h]
  exact hf (fun t => (v t).1) x.1

lemma fourth_prod_basis {U : Type*} [AddCommGroup U] [Module F U]
    (L : Fin 4 → (U →ₗ[F] F)) (v : Fin 4 → U)
    (hv : ∀ t s : Fin 4, L t (v s) = if t = s then 1 else 0) :
    fourthG (fun x => ∏ t : Fin 4, L t x) v 0 = 1 := by
  rw [fourth_eq_fold]
  have hprod : (fun x : U => ∏ t : Fin 4, L t x) =
      fun x => L 0 x * L 1 x * L 2 x * L 3 x := by
    ext x; rw [Fin.prod_univ_four]
  rw [hprod]
  have h1 : diffG (fun x => L 0 x * L 1 x * L 2 x * L 3 x) (v 0) =
      fun x => L 1 x * L 2 x * L 3 x := by
    ext x
    simp only [diffG, map_add, hv 0 0, hv 1 0, hv 2 0, hv 3 0]
    norm_num
    ring
  have h2 : diffG (fun x => L 1 x * L 2 x * L 3 x) (v 1) =
      fun x => L 2 x * L 3 x := by
    ext x
    simp only [diffG, map_add, hv 1 1, hv 2 1, hv 3 1]
    norm_num
    ring
  have h3 : diffG (fun x => L 2 x * L 3 x) (v 2) = fun x => L 3 x := by
    ext x
    simp only [diffG, map_add, hv 2 2, hv 3 2]
    norm_num
    ring
  have h4 : diffG (fun x => L 3 x) (v 3) = fun _ => 1 := by
    ext x
    simp only [diffG, map_add, hv 3 3]
    norm_num
  rw [h1, h2, h3, h4]

lemma not_surj_of_cubic_prod (k : ℕ) (hk : 0 < k) (V : Submodule F (W k)) (i : Fin k)
    (hc : cubicG (fun y : V => ∏ t : Fin 4, partsFun k hk i y.1 t)) :
    ¬ Function.Surjective (partsLM k hk i ∘ₗ V.subtype) := by
  intro hsurj
  choose v hv using fun s : Fin 4 => hsurj (Pi.single s 1)
  have hL : ∀ t s : Fin 4, (partsCoordLM k hk i t ∘ₗ V.subtype) (v s) = if t = s then 1 else 0 := by
    intro t s
    have hvs := congrFun (hv s) t
    simpa [partsLM, Pi.single_apply, eq_comm] using hvs
  have h1 := fourth_prod_basis (fun t => partsCoordLM k hk i t ∘ₗ V.subtype) v hL
  have heq : (fun y : V => ∏ t : Fin 4, (partsCoordLM k hk i t ∘ₗ V.subtype) y) =
      (fun y : V => ∏ t : Fin 4, partsFun k hk i y.1 t) := by
    ext y
    refine Finset.prod_congr rfl fun t _ => ?_
    exact partsCoordLM_apply k hk i t y.1
  rw [heq] at h1
  rw [hc v 0] at h1
  exact zero_ne_one h1

lemma exists_annihilator_of_not_surj {U : Type*} [AddCommGroup U] [Module F U]
    (T : U →ₗ[F] (Fin 4 → F)) (hns : ¬ Function.Surjective T) :
    ∃ a : Fin 4 → F, a ≠ 0 ∧ ∀ y : U, ∑ t : Fin 4, a t * T y t = 0 := by
  have hne_top : LinearMap.range T ≠ ⊤ := by
    intro htop
    apply hns
    intro w
    have hw : w ∈ LinearMap.range T := htop.symm ▸ Submodule.mem_top
    exact hw
  have hlt : Module.finrank F (LinearMap.range T) < Module.finrank F (Fin 4 → F) :=
    Submodule.finrank_lt hne_top
  have hadd := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range T)
  have hpos : 0 < Module.finrank F (LinearMap.range T).dualAnnihilator := by omega
  have hne_bot : (LinearMap.range T).dualAnnihilator ≠ ⊥ := by
    intro hb
    rw [hb, finrank_bot] at hpos
    omega
  obtain ⟨φ, hφ_mem, hφ_ne⟩ := (Submodule.ne_bot_iff _).mp hne_bot
  let a : Fin 4 → F := fun t => φ (Pi.single t 1)
  refine ⟨a, ?_, ?_⟩
  · intro ha
    apply hφ_ne
    apply LinearMap.ext
    intro w
    have hw : w = ∑ t : Fin 4, w t • Pi.single t (1 : F) := by
      ext s
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hw, map_sum]
    simp [a, smul_eq_mul, congrFun ha]
  · intro y
    have hy : φ (T y) = 0 := (Submodule.mem_dualAnnihilator φ).mp hφ_mem (T y) ⟨y, rfl⟩
    have hTy : T y = ∑ t : Fin 4, T y t • Pi.single t (1 : F) := by
      ext s
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hTy, map_sum] at hy
    simp only [map_smul, smul_eq_mul] at hy
    simpa [a, mul_comm] using hy

lemma prod_of_affine_rel (a p : Fin 4 → F) (t₀ : Fin 4) (ha : a t₀ = 1) (c : F)
    (hrel : ∑ t : Fin 4, a t * p t = c) :
    ∏ t : Fin 4, p t = (c + ∑ t ∈ Finset.univ.erase t₀, a t) * ∏ t ∈ Finset.univ.erase t₀, p t := by
  have hsplit := Finset.add_sum_erase Finset.univ (fun t => a t * p t) (Finset.mem_univ t₀)
  rw [ha, one_mul] at hsplit
  have hp0 : p t₀ = c + ∑ t ∈ Finset.univ.erase t₀, a t * p t := by
    rw [← hrel, ← hsplit]
    have hz : p t₀ + ∑ x ∈ Finset.univ.erase t₀, a x * p x + ∑ x ∈ Finset.univ.erase t₀, a x * p x = p t₀ := by
      rw [add_assoc, zmod2_add_self, add_zero]
    exact hz.symm
  rw [← Finset.mul_prod_erase Finset.univ p (Finset.mem_univ t₀), hp0]
  simp only [add_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mul_assoc, ← Finset.mul_prod_erase (Finset.univ.erase t₀) p ht,
    ← mul_assoc (p t), zmod2_mul_self, Finset.mul_prod_erase (Finset.univ.erase t₀) p ht]

lemma prod_erase_mem_deg3 (k : ℕ) (hk : 0 < k) (i : Fin k) (t₀ : Fin 4) :
    (fun x : W k => ∏ t ∈ Finset.univ.erase t₀, partsFun k hk i x t) ∈ Deg k 3 := by
  have d3 : ∀ t1 t2 t3 : Fin 4,
      (fun x : W k => partsFun k hk i x t1 * (partsFun k hk i x t2 * partsFun k hk i x t3)) ∈ Deg k 3 :=
    fun t1 t2 t3 => by
      have h := mul_linear_mem_deg (partsCoordLM k hk i t1)
        (mul_linear_mem_deg (partsCoordLM k hk i t2) (linear_mem_deg (d := 0) (partsCoordLM k hk i t3)))
      simpa only [partsCoordLM_apply] using h
  fin_cases t₀
  · have hs : (Finset.univ.erase (0 : Fin 4)) = {1, 2, 3} := by decide
    simpa [hs, mul_assoc] using d3 1 2 3
  · have hs : (Finset.univ.erase (1 : Fin 4)) = {0, 2, 3} := by decide
    simpa [hs, mul_assoc] using d3 0 2 3
  · have hs : (Finset.univ.erase (2 : Fin 4)) = {0, 1, 3} := by decide
    simpa [hs, mul_assoc] using d3 0 1 3
  · have hs : (Finset.univ.erase (3 : Fin 4)) = {0, 1, 2} := by decide
    simpa [hs, mul_assoc] using d3 0 1 2

lemma zmod2_ne_zero_eq_one (a : F) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl

lemma exists_eq_one_of_ne_zero {α : Type*} (a : α → F) (ha : a ≠ 0) : ∃ t, a t = 1 := by
  by_contra h
  push Not at h
  apply ha
  ext t
  by_contra ht
  exact h t (zmod2_ne_zero_eq_one (a t) ht)

lemma prod_parts_cubic_of_not_surj (k : ℕ) (hk : 0 < k) (i : Fin k)
    (hns : ¬ Function.Surjective (partsFun k hk i)) :
    cubicG (fun x : W k => ∏ t : Fin 4, partsFun k hk i x t) := by
  have hns' : ¬ Function.Surjective (partsLM k hk i) := by
    intro hs
    apply hns
    intro w
    obtain ⟨x, hx⟩ := hs w
    exact ⟨x, by rw [← partsLM_apply, hx]⟩
  obtain ⟨a, ha_ne, ha_rel⟩ := exists_annihilator_of_not_surj (partsLM k hk i) hns'
  obtain ⟨t₀, ht₀⟩ := exists_eq_one_of_ne_zero a ha_ne
  refine cubic_of_mem_deg3 ?_
  have heq : (fun x : W k => ∏ t : Fin 4, partsFun k hk i x t) =
      (0 + ∑ t ∈ Finset.univ.erase t₀, a t) •
        (fun x : W k => ∏ t ∈ Finset.univ.erase t₀, partsFun k hk i x t) := by
    ext x
    have hrel' : ∑ t : Fin 4, a t * partsFun k hk i x t = 0 := by
      simpa [partsLM_apply] using ha_rel x
    exact prod_of_affine_rel a (partsFun k hk i x) t₀ ht₀ 0 hrel'
  rw [heq]
  exact Submodule.smul_mem _ _ (prod_erase_mem_deg3 k hk i t₀)

lemma runFn_zero_of_all_zero {k d : ℕ} (ask : Fin d → ℕ → (W k →ₗ[F] F)) (x : W k)
    (hx : ∀ j : Fin d, ask j 0 x = 0) :
    runFn d ask x = 0 := by
  unfold runFn
  have hgen : ∀ (js : List (Fin d)), (∀ j ∈ js, ask j 0 x = 0) →
      js.foldl (fun h j => 2 * h + (if ask j h x = 0 then 0 else 1)) 0 = 0 := by
    intro js hjs
    induction js with
    | nil => rfl
    | cons j js ih =>
      simp only [List.foldl_cons]
      have hj : ask j 0 x = 0 := hjs j (by simp)
      simp only [hj, ↓reduceIte, Nat.mul_zero, Nat.add_zero]
      exact ih fun j' hj' => hjs j' (by simp [hj'])
  exact hgen (List.finRange d) fun j _ => hx j

lemma foldl_bits_eq {k d : ℕ} (L : Fin d → (W k →ₗ[F] F)) (x : W k) :
    ∀ (js : List (Fin d)) (h : ℕ),
      js.foldl (fun a j => 2 * a + (if L j x = 0 then 0 else 1)) h =
        h * 2 ^ js.length + js.foldl (fun a j => 2 * a + (if L j x = 0 then 0 else 1)) 0 ∧
      js.foldl (fun a j => 2 * a + (if L j x = 0 then 0 else 1)) 0 < 2 ^ js.length := by
  intro js
  induction js with
  | nil =>
    intro h
    simp
  | cons j js ih =>
    intro h
    simp only [List.foldl_cons, List.length_cons, Nat.pow_succ, Nat.mul_zero, Nat.zero_add]
    have ih1 := ih (2 * h + (if L j x = 0 then 0 else 1))
    have ih0 := ih (if L j x = 0 then 0 else 1)
    rw [ih1.1, ih0.1]
    have hlt := ih0.2
    by_cases hL : L j x = 0
    · simp only [hL, ↓reduceIte]
      constructor
      · ring
      · omega
    · simp only [hL, ↓reduceIte, Nat.one_mul]
      constructor
      · ring
      · omega

lemma foldl_bits_inj {k d : ℕ} (L : Fin d → (W k →ₗ[F] F)) (x y : W k) :
    ∀ (js : List (Fin d)),
      js.foldl (fun a j => 2 * a + (if L j x = 0 then 0 else 1)) 0 =
      js.foldl (fun a j => 2 * a + (if L j y = 0 then 0 else 1)) 0 →
      ∀ j ∈ js, L j x = L j y := by
  intro js
  induction js with
  | nil =>
    intro _ j hj
    simp at hj
  | cons j js ih =>
    intro heq j' hj'
    simp only [List.foldl_cons, Nat.mul_zero, Nat.zero_add] at heq
    have hx := foldl_bits_eq L x js (if L j x = 0 then 0 else 1)
    have hy := foldl_bits_eq L y js (if L j y = 0 then 0 else 1)
    rw [hx.1, hy.1] at heq
    have hrx := hx.2
    have hry := hy.2
    have hjj : L j x = L j y ∧
        js.foldl (fun a r => 2 * a + (if L r x = 0 then 0 else 1)) 0 =
        js.foldl (fun a r => 2 * a + (if L r y = 0 then 0 else 1)) 0 := by
      by_cases hLx : L j x = 0 <;> by_cases hLy : L j y = 0
      · simp only [hLx, hLy, ↓reduceIte, Nat.zero_mul, Nat.zero_add] at heq
        exact ⟨hLx.trans hLy.symm, heq⟩
      · simp only [hLx, hLy, ↓reduceIte, Nat.zero_mul, Nat.zero_add, Nat.one_mul] at heq
        omega
      · simp only [hLx, hLy, ↓reduceIte, Nat.zero_mul, Nat.zero_add, Nat.one_mul] at heq
        omega
      · simp only [hLx, hLy, ↓reduceIte, Nat.one_mul] at heq
        exact ⟨(zmod2_ne_zero_eq_one _ hLx).trans (zmod2_ne_zero_eq_one _ hLy).symm, by omega⟩
    rcases List.mem_cons.mp hj' with rfl | hmem
    · exact hjj.1
    · exact ih hjj.2 j' hmem

noncomputable def readoutFun (k : ℕ) (hk : 0 < k) (marked : Fin k → Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → F) (ask : Fin d → ℕ → (W k →ₗ[F] F))
    (pick : Fin k → Fin 4 → F)
    (hpick : ∀ i, pick i ≠ 0 ↔ marked i = true ∧ Function.Surjective (partsFun k hk i))
    (h : ℕ) (b : Bool) (i : Fin k) (x : W k) : F :=
  if b then 0 else
  if hsurj : Function.Surjective (partsFun k hk i) then
    if hmark : marked i = true then
      if hex : ∃ x₀ : W k, runFn d ask x₀ = h then
        let x₀ := Classical.choose hex
        let c := ∑ t : Fin 4, pick i t * partsFun k hk i x₀ t
        let t₀ := Classical.choose (exists_eq_one_of_ne_zero (pick i) ((hpick i).mpr ⟨hmark, hsurj⟩))
        (outFalse k hk name c₁ c₂ x i - ∏ t : Fin 4, partsFun k hk i x t) +
          (c + ∑ t ∈ Finset.univ.erase t₀, pick i t) * ∏ t ∈ Finset.univ.erase t₀, partsFun k hk i x t
      else 0
    else 0
  else outFalse k hk name c₁ c₂ x i

lemma readoutFun_cubic (k : ℕ) (hk : 0 < k) (marked : Fin k → Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → F) (ask : Fin d → ℕ → (W k →ₗ[F] F))
    (pick : Fin k → Fin 4 → F)
    (hpick : ∀ i, pick i ≠ 0 ↔ marked i = true ∧ Function.Surjective (partsFun k hk i))
    (h : ℕ) (b : Bool) (i : Fin k) :
    cubicG (readoutFun k hk marked d name c₁ c₂ ask pick hpick h b i) := by
  cases b
  · by_cases hsurj : Function.Surjective (partsFun k hk i)
    · by_cases hmark : marked i = true
      · by_cases hex : ∃ x₀ : W k, runFn d ask x₀ = h
        · let t₀ := Classical.choose (exists_eq_one_of_ne_zero (pick i) ((hpick i).mpr ⟨hmark, hsurj⟩))
          have heq : readoutFun k hk marked d name c₁ c₂ ask pick hpick h false i =
              fun x : W k =>
                (outFalse k hk name c₁ c₂ x i - ∏ t : Fin 4, partsFun k hk i x t) +
                  (∑ t : Fin 4, pick i t * partsFun k hk i (Classical.choose hex) t +
                    ∑ t ∈ Finset.univ.erase t₀, pick i t) *
                    ∏ t ∈ Finset.univ.erase t₀, partsFun k hk i x t := by
            ext x
            simp only [readoutFun, Bool.false_eq_true, ↓reduceIte, hsurj, ↓reduceDIte, hmark, hex]
            rfl
          rw [heq]
          have h1 := out_sub_prod_cubic k hk name c₁ c₂ i
          have h2 : cubicG (fun x : W k =>
              (∑ t : Fin 4, pick i t * partsFun k hk i (Classical.choose hex) t +
                ∑ t ∈ Finset.univ.erase t₀, pick i t) *
                ∏ t ∈ Finset.univ.erase t₀, partsFun k hk i x t) :=
            cubic_of_mem_deg3 (Submodule.smul_mem _ _ (prod_erase_mem_deg3 k hk i t₀))
          exact cubic_add h1 h2
        · have heq : readoutFun k hk marked d name c₁ c₂ ask pick hpick h false i = 0 := by
            ext x
            simp only [readoutFun, Bool.false_eq_true, ↓reduceIte, hsurj, ↓reduceDIte, hmark, hex,
              Pi.zero_apply]
          rw [heq]
          exact cubic_zero
      · have heq : readoutFun k hk marked d name c₁ c₂ ask pick hpick h false i = 0 := by
          ext x
          simp only [readoutFun, Bool.false_eq_true, ↓reduceIte, hsurj, ↓reduceDIte, hmark,
            Pi.zero_apply]
        rw [heq]
        exact cubic_zero
    · have heq : readoutFun k hk marked d name c₁ c₂ ask pick hpick h false i =
          (fun x : W k => outFalse k hk name c₁ c₂ x i - ∏ t : Fin 4, partsFun k hk i x t) +
            (fun x : W k => ∏ t : Fin 4, partsFun k hk i x t) := by
        ext x
        simp only [readoutFun, Bool.false_eq_true, ↓reduceIte, hsurj, ↓reduceDIte, Pi.add_apply]
        ring
      rw [heq]
      exact cubic_add (out_sub_prod_cubic k hk name c₁ c₂ i)
        (prod_parts_cubic_of_not_surj k hk i hsurj)
  · have heq : readoutFun k hk marked d name c₁ c₂ ask pick hpick h true i = 0 := by
      ext x
      simp only [readoutFun, ↓reduceIte, Pi.zero_apply]
    rw [heq]
    exact cubic_zero

lemma main_aux (k : ℕ) (hk : 0 < k) (marked : Fin k → Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → F) :
    (∃ (ask : Fin d → ℕ → (W k →ₗ[F] F)) (readout : ℕ → Bool → Fin k → W k → F),
      (∀ h b i, cubicG (readout h b i)) ∧
      ∀ x i, marked i = true → outFalse k hk name c₁ c₂ x i = readout (runFn d ask x) false i x) ↔
    ∃ pick : Fin k → Fin 4 → F,
      (∀ i, pick i ≠ 0 ↔ marked i = true ∧ Function.Surjective (partsFun k hk i)) ∧
      Module.finrank F (Submodule.span F (Set.range (fun i => formFun k hk i (pick i)))) ≤ d := by
  constructor
  · rintro ⟨ask, readout, hcubic, hmatch⟩
    let V : Submodule F (W k) := ⨅ j : Fin d, LinearMap.ker (ask j 0)
    have hV : ∀ x : W k, x ∈ V ↔ ∀ j : Fin d, ask j 0 x = 0 := by
      intro x
      simp only [V, Submodule.mem_iInf, LinearMap.mem_ker]
    have hex : ∀ i : Fin k, ∃ a : Fin 4 → F,
        (a ≠ 0 ↔ marked i = true ∧ Function.Surjective (partsFun k hk i)) ∧
        dotLM k (formFun k hk i a) ∈ Submodule.span F (Set.range fun j : Fin d => ask j 0) := by
      intro i
      by_cases hcond : marked i = true ∧ Function.Surjective (partsFun k hk i)
      · have hc_out : cubicG (fun y : V => ∏ t : Fin 4, partsFun k hk i y.1 t) := by
          have hc1 := cubic_restrict V (out_sub_prod_cubic k hk name c₁ c₂ i)
          have hc2 := cubic_restrict V (hcubic 0 false i)
          have hsub := cubic_sub hc2 hc1
          have heq : ((fun y : V => readout 0 false i y.1) -
              (fun y : V => outFalse k hk name c₁ c₂ y.1 i - ∏ t : Fin 4, partsFun k hk i y.1 t)) =
              fun y : V => ∏ t : Fin 4, partsFun k hk i y.1 t := by
            ext y
            simp only [Pi.sub_apply]
            have hrun : runFn d ask y.1 = 0 := runFn_zero_of_all_zero ask y.1 ((hV y.1).mp y.2)
            have hm : outFalse k hk name c₁ c₂ y.1 i = readout 0 false i y.1 := by
              have hmy := hmatch y.1 i hcond.1
              rw [hrun] at hmy
              exact hmy
            rw [hm]
            ring
          rw [heq] at hsub
          exact hsub
        have hnsV := not_surj_of_cubic_prod k hk V i hc_out
        obtain ⟨a, ha_ne, ha_rel⟩ := exists_annihilator_of_not_surj (partsLM k hk i ∘ₗ V.subtype) hnsV
        refine ⟨a, ⟨fun _ => hcond, fun _ => ha_ne⟩, ?_⟩
        refine mem_span_of_iInf_ker_le_ker ?_
        intro x hx
        rw [LinearMap.mem_ker, dotLM_formFun]
        have hxV : x ∈ V := hx
        simpa [partsLM_apply] using ha_rel ⟨x, hxV⟩
      · refine ⟨0, ⟨fun h => absurd rfl h, fun h => absurd h hcond⟩, ?_⟩
        have h0 : formFun k hk i 0 = 0 := by ext j; simp [formFun]
        have hd0 : dotLM k 0 = 0 := (vecToDual k).map_zero
        rw [h0, hd0]
        exact Submodule.zero_mem _
    choose pick hpick hspan using hex
    refine ⟨pick, hpick, ?_⟩
    have hle : Submodule.span F (Set.range fun i => dotLM k (formFun k hk i (pick i))) ≤
        Submodule.span F (Set.range fun j : Fin d => ask j 0) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hspan i
    have hfin1 := Submodule.finrank_mono hle
    have hfin2 : Module.finrank F (Submodule.span F (Set.range fun j : Fin d => ask j 0)) ≤ d := by
      change Set.finrank F (Set.range fun j : Fin d => ask j 0) ≤ d
      exact (finrank_range_le_card (R := F) (fun j : Fin d => ask j 0)).trans (by simp)
    have hmap : Submodule.map (vecToDual k).toLinearMap
        (Submodule.span F (Set.range fun i => formFun k hk i (pick i))) =
        Submodule.span F (Set.range fun i => dotLM k (formFun k hk i (pick i))) := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have hfin_eq : Module.finrank F (Submodule.span F (Set.range fun i => formFun k hk i (pick i))) =
        Module.finrank F (Submodule.span F (Set.range fun i => dotLM k (formFun k hk i (pick i)))) := by
      rw [← hmap]
      exact (LinearEquiv.finrank_map_eq (vecToDual k) _).symm
    rw [hfin_eq]
    exact hfin1.trans hfin2
  · rintro ⟨pick, hpick, hrank⟩
    let S : Submodule F (W k →ₗ[F] F) :=
      Submodule.span F (Set.range fun i => dotLM k (formFun k hk i (pick i)))
    have hmap : Submodule.map (vecToDual k).toLinearMap
        (Submodule.span F (Set.range fun i => formFun k hk i (pick i))) = S := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    have hrankS : Module.finrank F S ≤ d := by
      have hfin_eq : Module.finrank F (Submodule.span F (Set.range fun i => formFun k hk i (pick i))) =
          Module.finrank F S := by
        rw [← hmap]
        exact (LinearEquiv.finrank_map_eq (vecToDual k) _).symm
      omega
    have : Module.Free F S := Module.Free.of_divisionRing F S
    let b := Module.finBasis F S
    let L : Fin d → (W k →ₗ[F] F) := fun j =>
      if hj : j.val < Module.finrank F S then (b ⟨j.val, hj⟩).1 else 0
    have hS_le : S ≤ Submodule.span F (Set.range L) := by
      intro f hf
      have hrep := b.sum_repr ⟨f, hf⟩
      have hf_eq : f = ∑ r : Fin (Module.finrank F S),
          b.repr ⟨f, hf⟩ r • L ⟨r.val, lt_of_lt_of_le r.isLt hrankS⟩ := by
        have h1 : f = (∑ r : Fin (Module.finrank F S), b.repr ⟨f, hf⟩ r • b r : S).1 :=
          congrArg Subtype.val hrep.symm
        conv_lhs => rw [h1, Submodule.coe_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [SetLike.val_smul, L, r.isLt, ↓reduceDIte, Fin.eta]
      rw [hf_eq]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨r.val, lt_of_lt_of_le r.isLt hrankS⟩, rfl⟩)
    let ask : Fin d → ℕ → (W k →ₗ[F] F) := fun j _ => L j
    have hspan_eval : ∀ x y : W k, (∀ j : Fin d, L j x = L j y) →
        ∀ v ∈ Submodule.span F (Set.range L), v x = v y := by
      intro x y hL v hv
      induction hv using Submodule.span_induction with
      | mem f hf =>
        rcases hf with ⟨j, rfl⟩
        exact hL j
      | zero => rfl
      | add f g _ _ ihf ihg =>
        simp only [LinearMap.add_apply, ihf, ihg]
      | smul c f _ ihf =>
        simp only [LinearMap.smul_apply, smul_eq_mul, ihf]
    have hrun_eq : ∀ x y : W k, runFn d ask x = runFn d ask y →
        ∀ i : Fin k, dotLM k (formFun k hk i (pick i)) x = dotLM k (formFun k hk i (pick i)) y := by
      intro x y hxy i
      have hL : ∀ j : Fin d, L j x = L j y := fun j =>
        foldl_bits_inj L x y (List.finRange d) hxy j (List.mem_finRange j)
      exact hspan_eval x y hL _ (hS_le (Submodule.subset_span ⟨i, rfl⟩))
    refine ⟨ask, readoutFun k hk marked d name c₁ c₂ ask pick hpick,
      readoutFun_cubic k hk marked d name c₁ c₂ ask pick hpick, ?_⟩
    intro x i hmark
    by_cases hsurj : Function.Surjective (partsFun k hk i)
    · have hex : ∃ x₀ : W k, runFn d ask x₀ = runFn d ask x := ⟨x, rfl⟩
      simp only [readoutFun, Bool.false_eq_true, ↓reduceIte, hsurj, ↓reduceDIte, hmark, hex]
      set x₀ := Classical.choose hex
      have hx₀ : runFn d ask x₀ = runFn d ask x := Classical.choose_spec hex
      set t₀ := Classical.choose (exists_eq_one_of_ne_zero (pick i) ((hpick i).mpr ⟨hmark, hsurj⟩))
      have ht₀ : pick i t₀ = 1 :=
        Classical.choose_spec (exists_eq_one_of_ne_zero (pick i) ((hpick i).mpr ⟨hmark, hsurj⟩))
      have hrel : ∑ t : Fin 4, pick i t * partsFun k hk i x t =
          ∑ t : Fin 4, pick i t * partsFun k hk i x₀ t := by
        rw [← dotLM_formFun, ← dotLM_formFun]
        exact hrun_eq x x₀ hx₀.symm i
      have hprod := prod_of_affine_rel (pick i) (partsFun k hk i x) t₀ ht₀
        (∑ t : Fin 4, pick i t * partsFun k hk i x₀ t) hrel
      rw [← hprod]
      ring
    · simp only [readoutFun, Bool.false_eq_true, ↓reduceIte, hsurj, ↓reduceDIte]

lemma main :
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
∀ (k : ℕ) (hk : 0 < k) (marked : Fin k → Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let z := fun (x : W) (n : ℕ) =>
    x (ix n) + x (ix (n + k - 1)) + x (ix (n + 2 * k - 2))
  let parts := fun (i : Fin k) (x : W) (t : Fin 4) =>
    let atZ := fun n : ℕ => z x (i.val + n)
    if t.val = 0 then atZ 2 else if t.val = 1 then atZ 4 else
      if t.val = 2 then atZ 1 + atZ 3 else atZ 3 + atZ 5
  let unit := fun (j h : Fin k) => if h = j then (1 : F) else 0
  let form := fun (i : Fin k) (a : Fin 4 → F) (j : Fin k) =>
    ∑ t, a t * parts i (unit j) t
  fits k hk (fun i => (marked i, false)) d name c₁ c₂ ↔
    ∃ pick : Fin k → Fin 4 → F,
      (∀ i, pick i ≠ 0 ↔ marked i = true ∧ Function.Surjective (parts i)) ∧
      Module.finrank F (Submodule.span F (Set.range (fun i => form i (pick i)))) ≤ d := by
  intro fits k hk marked d name c₁ c₂ F' W' ix' z' parts' unit' form'
  have hlhs : fits k hk (fun i => (marked i, false)) d name c₁ c₂ ↔
      ∃ (ask : Fin d → ℕ → (W k →ₗ[F] F)) (readout : ℕ → Bool → Fin k → W k → F),
        (∀ h b i, cubicG (readout h b i)) ∧
        ∀ x i, marked i = true → outFalse k hk name c₁ c₂ x i = readout (runFn d ask x) false i x := by
    constructor
    · rintro ⟨ask, readout, hc, hm⟩
      exact ⟨ask, readout, hc, fun x i hi => hm x false i (by simpa using hi)⟩
    · rintro ⟨ask, readout, hc, hm⟩
      refine ⟨ask, readout, hc, fun x b i hbi => ?_⟩
      cases b
      · exact hm x i (by simpa using hbi)
      · simp at hbi
  exact hlhs.trans (main_aux k hk marked d name c₁ c₂)

end PEqualNP.Outside.L_meta_29770

theorem PEqualNP.Outside.L_meta_29770 :
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
∀ (k : ℕ) (hk : 0 < k) (marked : Fin k → Bool) (d : ℕ)
    (name c₁ c₂ : Bool → Fin k → ZMod 2),
  let F := ZMod 2
  let W := Fin k → F
  let ix := fun n : ℕ => (⟨n % k, Nat.mod_lt _ hk⟩ : Fin k)
  let z := fun (x : W) (n : ℕ) =>
    x (ix n) + x (ix (n + k - 1)) + x (ix (n + 2 * k - 2))
  let parts := fun (i : Fin k) (x : W) (t : Fin 4) =>
    let atZ := fun n : ℕ => z x (i.val + n)
    if t.val = 0 then atZ 2 else if t.val = 1 then atZ 4 else
      if t.val = 2 then atZ 1 + atZ 3 else atZ 3 + atZ 5
  let unit := fun (j h : Fin k) => if h = j then (1 : F) else 0
  let form := fun (i : Fin k) (a : Fin 4 → F) (j : Fin k) =>
    ∑ t, a t * parts i (unit j) t
  fits k hk (fun i => (marked i, false)) d name c₁ c₂ ↔
    ∃ pick : Fin k → Fin 4 → F,
      (∀ i, pick i ≠ 0 ↔ marked i = true ∧ Function.Surjective (parts i)) ∧
      Module.finrank F (Submodule.span F (Set.range (fun i => form i (pick i)))) ≤ d :=
  PEqualNP.Outside.L_meta_29770.main
