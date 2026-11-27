import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_gct_278
open Finset Module
noncomputable section
-- The embedding sum rewrite sumEmb adapts lemma cK of the merged L_gct_215 (credit to its author).
def gz (ζ : ℂ) (a b : Fin 4 → ℂ) (i : Fin 4) (k : Fin 5) : ℂ :=
  1 + a i * ζ ^ k.val + b i * ζ ^ (2 * k.val)
abbrev yH : Fin 5 × Fin 5 × Fin 5 × Fin 5 ≃ (Fin 4 → Fin 5) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun z := (z 0, z 1, z 2, z 3)
  left_inv _ := rfl
  right_inv z := by ext i; fin_cases i <;> rfl
lemma sumEmb (g : Fin 4 → Fin 5 → ℂ) :
    (∑ e : Fin 4 ↪ Fin 5, ∏ r, g r (e r)) = ∑ j, ∑ l, ∑ m, ∑ n,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
      g 0 j * g 1 l * g 2 m * g 3 n := by
  classical
  let u (z : Fin 4 → Fin 5) := ∏ r, g r (z r)
  have A : (∑ e : Fin 4 ↪ Fin 5, ∏ r, g r (e r)) =
      ∑ z : Fin 4 → Fin 5, if Function.Injective z then u z else 0 := by
    let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 5)
    change (∑ e : Fin 4 ↪ Fin 5, u e) = _
    rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 5 => u e), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) u).symm
  rw [A, ← yH.sum_comp (fun z => if Function.Injective z then u z else 0)]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  let z := yH (a, b, c, d)
  have p : z 0 = a := rfl
  have q : z 1 = b := rfl
  have s : z 2 = c := rfl
  have t : z 3 = d := rfl
  have f : Function.Injective z ↔ ¬(a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) := by
    constructor
    · intro o
      have h (i j : Fin 4) (g : i ≠ j) : z i ≠ z j := fun h => g (o h)
      exact not_or_intro (h 0 1 (by decide)) (not_or_intro (h 0 2 (by decide))
        (not_or_intro (h 0 3 (by decide)) (not_or_intro (h 1 2 (by decide))
          (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
    · intro g i j v
      simp only [not_or] at g
      fin_cases i <;> fin_cases j <;> first | rfl | grind
  change (if Function.Injective z then u z else 0) = _
  by_cases gg : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d
  · have k : ¬Function.Injective z := fun h => f.mp h gg
    rw [ite_eq_right k, ite_eq_left gg]
  · rw [ite_eq_left (f.mpr gg), ite_eq_right gg]
    change (∏ r, g r (z r)) = _
    simp [Fin.prod_univ_succ, p, q, s, t, mul_assoc]
def c4 (a b : Fin 4 → ℂ) : ℂ :=
  a 0 * (b 1 * b 2 + b 1 * b 3 + b 2 * b 3) + a 1 * (b 0 * b 2 + b 0 * b 3 + b 2 * b 3) +
  a 2 * (b 0 * b 1 + b 0 * b 3 + b 1 * b 3) + a 3 * (b 0 * b 1 + b 0 * b 2 + b 1 * b 2)
def d4 (a b : Fin 4 → ℂ) : ℂ :=
  b 0 * a 1 * a 2 * a 3 + b 1 * a 0 * a 2 * a 3 + b 2 * a 0 * a 1 * a 3 + b 3 * a 0 * a 1 * a 2
set_option maxRecDepth 65536 in
set_option maxHeartbeats 12000000 in
lemma expand (ζ : ℂ) (hζ : IsPrimitiveRoot ζ 5) (a b : Fin 4 → ℂ) :
    (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
      (1 + a i * ζ ^ (f i).val + b i * ζ ^ (2 * (f i).val))) = 120 + 20 * c4 a b - 30 * d4 a b := by
  have h5 : ζ ^ 5 = 1 := hζ.pow_eq_one
  have hΦ : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    have := hζ.geom_sum_eq_zero (by norm_num : 1 < 5)
    simp [Finset.sum_range_succ] at this
    linear_combination this
  have g0 : ∀ i, gz ζ a b i 0 = 1 + a i + b i := fun i => by
    show 1 + a i * ζ ^ 0 + b i * ζ ^ (2 * 0) = _
    ring
  have g1 : ∀ i, gz ζ a b i 1 = 1 + a i * ζ + b i * ζ ^ 2 := fun i => by
    show 1 + a i * ζ ^ 1 + b i * ζ ^ (2 * 1) = _
    ring
  have g2 : ∀ i, gz ζ a b i 2 = 1 + a i * ζ ^ 2 + b i * ζ ^ 4 := fun i => by
    show 1 + a i * ζ ^ 2 + b i * ζ ^ (2 * 2) = _
    ring
  have g3 : ∀ i, gz ζ a b i 3 = 1 + a i * ζ ^ 3 + b i * ζ := fun i => by
    show 1 + a i * ζ ^ 3 + b i * ζ ^ (2 * 3) = _
    linear_combination b i * ζ * h5
  have g4 : ∀ i, gz ζ a b i 4 = 1 + a i * ζ ^ 4 + b i * ζ ^ 3 := fun i => by
    show 1 + a i * ζ ^ 4 + b i * ζ ^ (2 * 4) = _
    linear_combination b i * ζ ^ 3 * h5
  change (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4, gz ζ a b i (f i)) = _
  rw [sumEmb]
  simp (config := {decide := true}) only [Fin.sum_univ_five, ite_true, ite_false, add_zero, zero_add,
    g0, g1, g2, g3, g4]
  unfold c4 d4
  linear_combination (b 3*((24)*ζ^0) +
    b 2*((24)*ζ^0) +
    b 2*b 3*((12)*ζ^1+(12)*ζ^3) +
    b 1*((24)*ζ^0) +
    b 1*b 3*((12)*ζ^1+(12)*ζ^3) +
    b 1*b 2*((12)*ζ^1+(12)*ζ^3) +
    b 1*b 2*b 3*((12)*ζ^3+(12)*ζ^5) +
    b 0*((24)*ζ^0) +
    b 0*b 3*((12)*ζ^1+(12)*ζ^3) +
    b 0*b 2*((12)*ζ^1+(12)*ζ^3) +
    b 0*b 2*b 3*((12)*ζ^3+(12)*ζ^5) +
    b 0*b 1*((12)*ζ^1+(12)*ζ^3) +
    b 0*b 1*b 3*((12)*ζ^3+(12)*ζ^5) +
    b 0*b 1*b 2*((12)*ζ^3+(12)*ζ^5) +
    b 0*b 1*b 2*b 3*((24)*ζ^6) +
    a 3*((24)*ζ^0) +
    a 3*b 2*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 3*b 1*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 3*b 1*b 2*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 3*b 0*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 3*b 0*b 2*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 3*b 0*b 1*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 3*b 0*b 1*b 2*((12)*ζ^5+(6)*ζ^6+(6)*ζ^8) +
    a 2*((24)*ζ^0) +
    a 2*b 3*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 2*b 1*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 2*b 1*b 3*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 2*b 0*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 2*b 0*b 3*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 2*b 0*b 1*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 2*b 0*b 1*b 3*((12)*ζ^5+(6)*ζ^6+(6)*ζ^8) +
    a 2*a 3*((12)*ζ^1+(12)*ζ^3) +
    a 2*a 3*b 1*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 2*a 3*b 0*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 2*a 3*b 0*b 1*((4)*ζ^4+(4)*ζ^5+(8)*ζ^6+(8)*ζ^7+(-4)*ζ^8+(4)*ζ^9) +
    a 1*((24)*ζ^0) +
    a 1*b 3*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 1*b 2*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 1*b 2*b 3*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 1*b 0*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 1*b 0*b 3*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 1*b 0*b 2*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 1*b 0*b 2*b 3*((12)*ζ^5+(6)*ζ^6+(6)*ζ^8) +
    a 1*a 3*((12)*ζ^1+(12)*ζ^3) +
    a 1*a 3*b 2*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 1*a 3*b 0*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 1*a 3*b 0*b 2*((4)*ζ^4+(4)*ζ^5+(8)*ζ^6+(8)*ζ^7+(-4)*ζ^8+(4)*ζ^9) +
    a 1*a 2*((12)*ζ^1+(12)*ζ^3) +
    a 1*a 2*b 3*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 1*a 2*b 0*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 1*a 2*b 0*b 3*((4)*ζ^4+(4)*ζ^5+(8)*ζ^6+(8)*ζ^7+(-4)*ζ^8+(4)*ζ^9) +
    a 1*a 2*a 3*((12)*ζ^3+(12)*ζ^5) +
    a 1*a 2*a 3*b 0*((30)*ζ^0+(-30)*ζ^1+(6)*ζ^4+(24)*ζ^5+(-12)*ζ^6+(6)*ζ^7+(6)*ζ^8) +
    a 0*((24)*ζ^0) +
    a 0*b 3*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 0*b 2*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 0*b 2*b 3*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 0*b 1*((12)*ζ^1+(6)*ζ^2+(6)*ζ^4) +
    a 0*b 1*b 3*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 0*b 1*b 2*((-20)*ζ^0+(20)*ζ^1+(4)*ζ^2+(4)*ζ^3+(4)*ζ^4+(8)*ζ^6) +
    a 0*b 1*b 2*b 3*((12)*ζ^5+(6)*ζ^6+(6)*ζ^8) +
    a 0*a 3*((12)*ζ^1+(12)*ζ^3) +
    a 0*a 3*b 2*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 0*a 3*b 1*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 0*a 3*b 1*b 2*((4)*ζ^4+(4)*ζ^5+(8)*ζ^6+(8)*ζ^7+(-4)*ζ^8+(4)*ζ^9) +
    a 0*a 2*((12)*ζ^1+(12)*ζ^3) +
    a 0*a 2*b 3*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 0*a 2*b 1*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 0*a 2*b 1*b 3*((4)*ζ^4+(4)*ζ^5+(8)*ζ^6+(8)*ζ^7+(-4)*ζ^8+(4)*ζ^9) +
    a 0*a 2*a 3*((12)*ζ^3+(12)*ζ^5) +
    a 0*a 2*a 3*b 1*((30)*ζ^0+(-30)*ζ^1+(6)*ζ^4+(24)*ζ^5+(-12)*ζ^6+(6)*ζ^7+(6)*ζ^8) +
    a 0*a 1*((12)*ζ^1+(12)*ζ^3) +
    a 0*a 1*b 3*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 0*a 1*b 2*((4)*ζ^2+(4)*ζ^3+(8)*ζ^4+(8)*ζ^5+(-4)*ζ^6+(4)*ζ^7) +
    a 0*a 1*b 2*b 3*((4)*ζ^4+(4)*ζ^5+(8)*ζ^6+(8)*ζ^7+(-4)*ζ^8+(4)*ζ^9) +
    a 0*a 1*a 3*((12)*ζ^3+(12)*ζ^5) +
    a 0*a 1*a 3*b 2*((30)*ζ^0+(-30)*ζ^1+(6)*ζ^4+(24)*ζ^5+(-12)*ζ^6+(6)*ζ^7+(6)*ζ^8) +
    a 0*a 1*a 2*((12)*ζ^3+(12)*ζ^5) +
    a 0*a 1*a 2*b 3*((30)*ζ^0+(-30)*ζ^1+(6)*ζ^4+(24)*ζ^5+(-12)*ζ^6+(6)*ζ^7+(6)*ζ^8) +
    a 0*a 1*a 2*a 3*((24)*ζ^6)) * hΦ
abbrev V3 := Fin 3 → ℂ
abbrev E3 := V3 × V3
def cC (x y : Fin 3 → ℂ) : ℂ := x 0 * y 1 * y 2 + x 1 * y 2 * y 0 + x 2 * y 0 * y 1
def qQ (x y : Fin 3 → ℂ) : ℂ := x 0 * y 0 * (x 0 ^ 2 - x 1 ^ 2 - x 2 ^ 2) +
  x 1 * y 1 * (x 1 ^ 2 - x 0 ^ 2 - x 2 ^ 2) + x 2 * y 2 * (x 2 ^ 2 - x 0 ^ 2 - x 1 ^ 2)
def cr (n w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![n 1 * w 2 - n 2 * w 1, n 2 * w 0 - n 0 * w 2, n 0 * w 1 - n 1 * w 0]
lemma nrm (X : Submodule ℂ V3) (h : 2 ≤ finrank ℂ X) :
    ∃ n : V3, n ≠ 0 ∧ ∀ x : V3, n 0 * x 0 + n 1 * x 1 + n 2 * x 2 = 0 → x ∈ X := by
  classical
  by_cases hX : X = ⊤
  · refine ⟨![1, 0, 0], ?_, fun x _ => by rw [hX]; trivial⟩
    intro c; have := congrFun c 0; simp at this
  · obtain ⟨v, -, hv⟩ := IsConcreteLE.exists_of_lt (lt_top_iff_ne_top.mpr hX)
    obtain ⟨f, hf, hb⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
    have f0 : f ≠ 0 := by rintro rfl; exact hf rfl
    have hk := Module.Dual.finrank_ker_add_one_of_ne_zero f0
    have d3 : finrank ℂ V3 = 3 := by simp
    have le : X ≤ LinearMap.ker f := by
      intro x hx
      have : f x ∈ X.map f := ⟨x, hx, rfl⟩
      rw [hb] at this; exact this
    have eq : X = LinearMap.ker f := Submodule.eq_of_le_of_finrank_le le (by omega)
    let n : V3 := fun i => f (fun j => if i = j then 1 else 0)
    have hfx : ∀ x : V3, f x = n 0 * x 0 + n 1 * x 1 + n 2 * x 2 := by
      intro x; rw [LinearMap.pi_apply_eq_sum_univ f x]; simp [Fin.sum_univ_three, n, mul_comm]
    refine ⟨n, ?_, fun x hx => by rw [eq, LinearMap.mem_ker, hfx]; exact hx⟩
    intro c; apply hf; rw [hfx]; simp [c]
lemma fin (n m : Fin 3 → ℂ) (hn : n ≠ 0) (hm : m ≠ 0)
    (h : ∀ w z, cC (cr n w) (cr m z) = 0 ∧ qQ (cr n w) (cr m z) = 0) : False := by
  have hn' : n 0 ≠ 0 ∨ n 1 ≠ 0 ∨ n 2 ≠ 0 := by
    by_contra c; push Not at c; apply hn; funext i; fin_cases i <;> simp [c.1, c.2.1, c.2.2]
  have hm' : m 0 ≠ 0 ∨ m 1 ≠ 0 ∨ m 2 ≠ 0 := by
    by_contra c; push Not at c; apply hm; funext i; fin_cases i <;> simp [c.1, c.2.1, c.2.2]
  have E : ∀ w z, cC (cr n w) (cr m z) = 0 := fun w z => (h w z).1
  have F : ∀ w z, qQ (cr n w) (cr m z) = 0 := fun w z => (h w z).2
  have c00 := E ![1,0,0] ![1,0,0]
  have c01 := E ![1,0,0] ![0,1,0]
  have c02 := E ![1,0,0] ![0,0,1]
  have c10 := E ![0,1,0] ![1,0,0]
  have c11 := E ![0,1,0] ![0,1,0]
  have c12 := E ![0,1,0] ![0,0,1]
  have c20 := E ![0,0,1] ![1,0,0]
  have c21 := E ![0,0,1] ![0,1,0]
  have c22 := E ![0,0,1] ![0,0,1]
  have d01 := E ![1,0,0] ![1,1,0]
  have d02 := E ![1,0,0] ![1,0,1]
  have d12 := E ![1,0,0] ![0,1,1]
  have d101 := E ![0,1,0] ![1,1,0]
  have d102 := E ![0,1,0] ![1,0,1]
  have d112 := E ![0,1,0] ![0,1,1]
  have d201 := E ![0,0,1] ![1,1,0]
  have d202 := E ![0,0,1] ![1,0,1]
  have d212 := E ![0,0,1] ![0,1,1]
  have q0 := F ![1,0,0] ![1,0,0]
  have q1 := F ![0,1,0] ![0,1,0]
  have q2 := F ![0,0,1] ![0,0,1]
  simp [cC, qQ, cr] at c00 c01 c02 c10 c11 c12 c20 c21 c22 d01 d02 d12 d101 d102 d112 d201 d202 d212 q0 q1 q2
  grind
set_option maxHeartbeats 2000000 in
lemma ub (L : Submodule ℂ E3) (hL : ∀ z ∈ L, cC z.1 z.2 = 0 ∧ qQ z.1 z.2 = 0) :
    finrank ℂ L ≤ 3 := by
  classical
  by_contra hc; push Not at hc
  have d3 : finrank ℂ V3 = 3 := by simp
  let fs : L →ₗ[ℂ] V3 := LinearMap.fst ℂ V3 V3 ∘ₗ L.subtype
  let sn : L →ₗ[ℂ] V3 := LinearMap.snd ℂ V3 V3 ∘ₗ L.subtype
  have r1 := LinearMap.finrank_range_add_finrank_ker fs
  have r2 := LinearMap.finrank_range_add_finrank_ker sn
  have b1 : finrank ℂ (LinearMap.range fs) ≤ 3 := (Submodule.finrank_le _).trans d3.le
  have b2 : finrank ℂ (LinearMap.range sn) ≤ 3 := (Submodule.finrank_le _).trans d3.le
  have nz : ∀ p : Submodule ℂ L, 1 ≤ finrank ℂ p → ∃ w ∈ p, (w : E3) ≠ 0 := by
    intro p hp
    have : p ≠ ⊥ := by intro e; rw [e, finrank_bot] at hp; omega
    obtain ⟨w, hw, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot this
    exact ⟨w, hw, fun e => h0 (Subtype.ext e)⟩
  by_cases A : finrank ℂ (LinearMap.ker fs) ≤ 1
  · have top : LinearMap.range fs = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    obtain ⟨w, hw, w0⟩ := nz (LinearMap.ker fs) (by omega)
    have w1 : (w : E3).1 = 0 := hw
    have key : ∀ x : V3, qQ x (w : E3).2 = 0 := by
      intro x
      obtain ⟨z, hz⟩ : x ∈ LinearMap.range fs := by rw [top]; trivial
      have e1 := (hL _ z.2).2
      have e2 := (hL _ (L.add_mem z.2 w.2)).2
      have hz' : (z : E3).1 = x := hz
      simp only [Prod.fst_add, Prod.snd_add, w1, add_zero, hz'] at e1 e2
      have : qQ x ((z : E3).2 + (w : E3).2) = qQ x (z : E3).2 + qQ x (w : E3).2 := by
        simp only [qQ, Pi.add_apply]; ring
      rw [this, e1] at e2; simpa using e2
    apply w0
    have k0 := key ![1, 0, 0]
    have k1 := key ![0, 1, 0]
    have k2 := key ![0, 0, 1]
    simp [qQ] at k0 k1 k2
    refine Prod.ext w1 ?_
    funext i; fin_cases i <;> simp [k0, k1, k2]
  by_cases B : finrank ℂ (LinearMap.ker sn) ≤ 1
  · have top : LinearMap.range sn = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
    obtain ⟨w, hw, w0⟩ := nz (LinearMap.ker sn) (by omega)
    have w1 : (w : E3).2 = 0 := hw
    have key : ∀ y : V3, cC (w : E3).1 y = 0 := by
      intro y
      obtain ⟨z, hz⟩ : y ∈ LinearMap.range sn := by rw [top]; trivial
      have e1 := (hL _ z.2).1
      have e2 := (hL _ (L.add_mem z.2 w.2)).1
      have hz' : (z : E3).2 = y := hz
      simp only [Prod.fst_add, Prod.snd_add, w1, add_zero, hz'] at e1 e2
      have : cC ((z : E3).1 + (w : E3).1) y = cC (z : E3).1 y + cC (w : E3).1 y := by
        simp only [cC, Pi.add_apply]; ring
      rw [this, e1] at e2; simpa using e2
    apply w0
    have k0 := key ![0, 1, 1]
    have k1 := key ![1, 0, 1]
    have k2 := key ![1, 1, 0]
    simp [cC] at k0 k1 k2
    refine Prod.ext ?_ w1
    funext i; fin_cases i <;> simp [k0, k1, k2]
  push Not at A B
  let Y := LinearMap.range (sn ∘ₗ (LinearMap.ker fs).subtype)
  let X := LinearMap.range (fs ∘ₗ (LinearMap.ker sn).subtype)
  have iY : Function.Injective (sn ∘ₗ (LinearMap.ker fs).subtype) := by
    intro u v e
    have a1 : ((u : L) : E3).1 = 0 := u.2
    have a2 : ((v : L) : E3).1 = 0 := v.2
    have e' : ((u : L) : E3).2 = ((v : L) : E3).2 := e
    exact Subtype.ext (Subtype.ext (Prod.ext (a1.trans a2.symm) e'))
  have iX : Function.Injective (fs ∘ₗ (LinearMap.ker sn).subtype) := by
    intro u v e
    have a1 : ((u : L) : E3).2 = 0 := u.2
    have a2 : ((v : L) : E3).2 = 0 := v.2
    have e' : ((u : L) : E3).1 = ((v : L) : E3).1 := e
    exact Subtype.ext (Subtype.ext (Prod.ext e' (a1.trans a2.symm)))
  have fY := LinearMap.finrank_range_of_inj iY
  have fX := LinearMap.finrank_range_of_inj iX
  have mY : ∀ y ∈ Y, ((0 : V3), y) ∈ L := by
    rintro y ⟨u, rfl⟩
    have a1 : ((u : L) : E3).1 = 0 := u.2
    have : ((u : L) : E3) = (0, ((u : L) : E3).2) := Prod.ext a1 rfl
    have h2 := ((u : L)).2
    rw [this] at h2; exact h2
  have mX : ∀ x ∈ X, (x, (0 : V3)) ∈ L := by
    rintro x ⟨u, rfl⟩
    have a1 : ((u : L) : E3).2 = 0 := u.2
    have : ((u : L) : E3) = (((u : L) : E3).1, 0) := Prod.ext rfl a1
    have h2 := ((u : L)).2
    rw [this] at h2; exact h2
  have fX' : finrank ℂ X = finrank ℂ (LinearMap.ker sn) := fX
  have fY' : finrank ℂ Y = finrank ℂ (LinearMap.ker fs) := fY
  obtain ⟨n, n0, hn⟩ := nrm X (by omega)
  obtain ⟨m, m0, hm⟩ := nrm Y (by omega)
  apply fin n m n0 m0
  intro w z
  have hx : cr n w ∈ X := hn _ (by
    show n 0 * (n 1 * w 2 - n 2 * w 1) + n 1 * (n 2 * w 0 - n 0 * w 2) + n 2 * (n 0 * w 1 - n 1 * w 0) = 0
    ring)
  have hy : cr m z ∈ Y := hm _ (by
    show m 0 * (m 1 * z 2 - m 2 * z 1) + m 1 * (m 2 * z 0 - m 0 * z 2) + m 2 * (m 0 * z 1 - m 1 * z 0) = 0
    ring)
  have := hL _ (L.add_mem (mX _ hx) (mY _ hy))
  simp only [Prod.fst_add, Prod.snd_add, add_zero, zero_add] at this
  exact this
def hd : V3 →ₗ[ℂ] (Fin 4 → ℂ) where
  toFun x := ![x 0 + x 1 + x 2, x 0 - x 1 - x 2, -x 0 + x 1 - x 2, -x 0 - x 1 + x 2]
  map_add' x y := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c x := by funext i; fin_cases i <;> simp <;> ring
def hinv (a : Fin 4 → ℂ) : V3 :=
  ![(a 0 + a 1 - a 2 - a 3) / 4, (a 0 - a 1 + a 2 - a 3) / 4, (a 0 - a 1 - a 2 + a 3) / 4]
lemma hinv_hd (x : V3) : hinv (hd x) = x := by
  funext i; fin_cases i <;> simp [hinv, hd] <;> ring
lemma hd_hinv (a : Fin 4 → ℂ) (h : ∑ i, a i = 0) : hd (hinv a) = a := by
  rw [Fin.sum_univ_four] at h
  funext i; fin_cases i <;> simp [hinv, hd] <;> linear_combination (-1 / 4 : ℂ) * h
lemma sum_hd (x : V3) : ∑ i, hd x i = 0 := by simp [Fin.sum_univ_four, hd]; ring
lemma c4hd (x y : V3) : c4 (hd x) (hd y) = 8 * cC x y := by simp [c4, hd, cC]; ring
lemma d4hd (x y : V3) : d4 (hd x) (hd y) = 4 * qQ x y := by simp [d4, hd, qQ]; ring
lemma cC2 (x y : V3) : cC ((2 : ℂ) • x) ((2 : ℂ) • y) = 8 * cC x y := by simp [cC]; ring
lemma qQ2 (x y : V3) : qQ ((2 : ℂ) • x) ((2 : ℂ) • y) = 16 * qQ x y := by simp [qQ]; ring
lemma main : ∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
  (∀ L : Submodule ℂ ((Fin 4 → ℂ) × (Fin 4 → ℂ)),
    (∀ x ∈ L, (∑ i, x.1 i) = 0 ∧ (∑ i, x.2 i) = 0 ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + x.1 i * ζ ^ (f i).val + x.2 i * ζ ^ (2 * (f i).val))) = 120) →
      Module.finrank ℂ L ≤ 3) ∧
  (∃ L : Submodule ℂ ((Fin 4 → ℂ) × (Fin 4 → ℂ)),
    Module.finrank ℂ L = 3 ∧
      ∀ x ∈ L, (∑ i, x.1 i) = 0 ∧ (∑ i, x.2 i) = 0 ∧
        (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
          (1 + x.1 i * ζ ^ (f i).val + x.2 i * ζ ^ (2 * (f i).val))) = 120) := by
  intro ζ hζ
  refine ⟨fun L hL => ?_, ?_⟩
  · let T : E3 →ₗ[ℂ] (Fin 4 → ℂ) × (Fin 4 → ℂ) := hd.prodMap hd
    have hT : ∀ z : E3, T z = (hd z.1, hd z.2) := fun z => rfl
    have hle : L ≤ LinearMap.range T := by
      intro z hz
      obtain ⟨s1, s2, -⟩ := hL z hz
      exact ⟨(hinv z.1, hinv z.2), by rw [hT, hd_hinv _ s1, hd_hinv _ s2]⟩
    have hmap : (L.comap T).map T = L := Submodule.map_comap_eq_self hle
    have key : ∀ z ∈ L.comap T, cC z.1 z.2 = 0 ∧ qQ z.1 z.2 = 0 := by
      intro z hz
      have hz2 : (2 : ℂ) • z ∈ L.comap T := (L.comap T).smul_mem (2 : ℂ) hz
      have h1 : 120 + 20 * c4 (hd z.1) (hd z.2) - 30 * d4 (hd z.1) (hd z.2) = 120 := by
        rw [← expand ζ hζ]; exact (hL _ hz).2.2
      have h2 : 120 + 20 * c4 (hd ((2 : ℂ) • z).1) (hd ((2 : ℂ) • z).2) -
          30 * d4 (hd ((2 : ℂ) • z).1) (hd ((2 : ℂ) • z).2) = 120 := by
        rw [← expand ζ hζ]; exact (hL _ hz2).2.2
      rw [c4hd, d4hd] at h1 h2
      rw [Prod.smul_fst, Prod.smul_snd, cC2, qQ2] at h2
      constructor
      · linear_combination (16 * h1 - h2) / 1280
      · linear_combination (8 * h1 - h2) / 960
    calc Module.finrank ℂ L = Module.finrank ℂ ((L.comap T).map T) := by rw [hmap]
      _ ≤ Module.finrank ℂ (L.comap T) := Submodule.finrank_map_le _ _
      _ ≤ 3 := ub _ key
  · let J : V3 →ₗ[ℂ] (Fin 4 → ℂ) × (Fin 4 → ℂ) := LinearMap.inl ℂ _ _ ∘ₗ hd
    have hJ : ∀ x : V3, J x = (hd x, 0) := fun x => rfl
    have iJ : Function.Injective J := by
      intro x y e
      have := congrArg (fun p => hinv p.1) e
      simpa [hJ, hinv_hd] using this
    refine ⟨LinearMap.range J, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj iJ]; simp
    · rintro _ ⟨x, rfl⟩
      rw [hJ]
      refine ⟨sum_hd x, by simp, ?_⟩
      rw [expand ζ hζ]; simp [c4, d4]
end
end PEqualNP.Outside.L_gct_278
open PEqualNP.Outside.L_gct_278 in
theorem PEqualNP.Outside.L_gct_278 : ∀ (ζ : ℂ), IsPrimitiveRoot ζ 5 →
  (∀ L : Submodule ℂ ((Fin 4 → ℂ) × (Fin 4 → ℂ)),
    (∀ x ∈ L, (∑ i, x.1 i) = 0 ∧ (∑ i, x.2 i) = 0 ∧
      (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
        (1 + x.1 i * ζ ^ (f i).val + x.2 i * ζ ^ (2 * (f i).val))) = 120) →
      Module.finrank ℂ L ≤ 3) ∧
  (∃ L : Submodule ℂ ((Fin 4 → ℂ) × (Fin 4 → ℂ)),
    Module.finrank ℂ L = 3 ∧
      ∀ x ∈ L, (∑ i, x.1 i) = 0 ∧ (∑ i, x.2 i) = 0 ∧
        (∑ f : Fin 4 ↪ Fin 5, ∏ i : Fin 4,
          (1 + x.1 i * ζ ^ (f i).val + x.2 i * ζ ^ (2 * (f i).val))) = 120) :=
  main
