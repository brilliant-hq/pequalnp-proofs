import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_415

open Finset

theorem fiber_sq {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq Y] (f : X → Y) :
    Fintype.card X ^ 2 ≤ Fintype.card Y * ∑ u, (univ.filter (fun v => f u = f v)).card := by
  have h1 : ∑ u, (univ.filter (fun v => f u = f v)).card =
      ∑ y, (univ.filter (fun v => f v = y)).card ^ 2 := by
    rw [← Finset.sum_fiberwise univ f (fun u => (univ.filter (fun v => f u = f v)).card)]
    refine sum_congr rfl fun y _ => ?_
    have : ∀ u ∈ univ.filter (fun u => f u = y),
        (univ.filter (fun v => f u = f v)).card = (univ.filter (fun v => f v = y)).card := by
      intro u hu
      rw [mem_filter] at hu
      rw [hu.2]
      congr 1
      ext v
      simp [eq_comm]
    rw [sum_congr rfl this, sum_const, smul_eq_mul, sq]
  have h2 : ∑ y, (univ.filter (fun v => f v = y)).card = Fintype.card X := by
    rw [← card_univ]
    exact (card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)).symm
  rw [h1, ← h2]
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset Y))
    (f := fun y => (univ.filter (fun v => f v = y)).card)
  simpa only [Nat.cast_id, card_univ] using this

theorem coll_bound {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (K : ℕ) (hK : 0 < K) (hXY : Fintype.card X = Fintype.card Y * K) (hY : 0 < Fintype.card Y)
    (r errors : ℕ) (f : Fin r → X → Y)
    (h : ∀ u v : X, u ≠ v → (univ.filter (fun i : Fin r => f i u = f i v)).card ≤ errors) :
    r * (K - 1) ≤ errors * (Fintype.card X - 1) ∧
    (errors * (Fintype.card X - 1) = r * (K - 1) →
      ∀ u v : X, u ≠ v → (univ.filter (fun i : Fin r => f i u = f i v)).card = errors) := by
  set N := Fintype.card X with hN
  set c := fun u v : X => (univ.filter (fun i : Fin r => f i u = f i v)).card with hc
  have hdiag : ∀ u, c u u = r := by intro u; simp [hc]
  have hNpos : 0 < N := by rw [hXY]; positivity
  have hlow : r * (N * K) ≤ ∑ u, ∑ v, c u v := by
    have e : ∑ u, ∑ v, c u v =
        ∑ i : Fin r, ∑ u, (univ.filter (fun v => f i u = f i v)).card := by
      simp only [hc, card_filter]
      calc _ = ∑ u : X, ∑ i : Fin r, ∑ v : X, (if f i u = f i v then 1 else 0) :=
            sum_congr rfl (fun u _ => sum_comm)
        _ = _ := sum_comm
    rw [e]
    have hi : ∀ i ∈ (univ : Finset (Fin r)),
        N * K ≤ ∑ u, (univ.filter (fun v => f i u = f i v)).card := by
      intro i _
      have h1 := fiber_sq (f i)
      rw [← hN] at h1
      have h2 : N ^ 2 = Fintype.card Y * (N * K) := by rw [sq]; nth_rewrite 1 [hXY]; ring
      rw [h2] at h1
      exact Nat.le_of_mul_le_mul_left h1 hY
    have := card_nsmul_le_sum _ _ _ hi
    simpa [card_univ, smul_eq_mul] using this
  have hup : ∀ u, ∑ v, c u v ≤ r + (N - 1) * errors := by
    intro u
    rw [← add_sum_erase _ _ (mem_univ u), hdiag]
    have : ∑ v ∈ univ.erase u, c u v ≤ (univ.erase u).card • errors :=
      sum_le_card_nsmul _ _ _ (fun v hv => h u v (ne_of_mem_erase hv).symm)
    rw [card_erase_of_mem (mem_univ _), card_univ, smul_eq_mul, ← hN] at this
    omega
  have htot : ∑ u, ∑ v, c u v ≤ N * (r + (N - 1) * errors) := by
    calc _ ≤ ∑ _u : X, (r + (N - 1) * errors) := sum_le_sum fun u _ => hup u
      _ = _ := by rw [sum_const, card_univ, smul_eq_mul]
  have hrK : r * K = r * (K - 1) + r := by
    conv_lhs => rw [show K = (K - 1) + 1 by omega]
    ring
  have key : r * K ≤ r + (N - 1) * errors := by
    have := hlow.trans htot
    have e : r * (N * K) = N * (r * K) := by ring
    rw [e] at this
    exact Nat.le_of_mul_le_mul_left this hNpos
  constructor
  · rw [hrK] at key
    have e : errors * (N - 1) = (N - 1) * errors := mul_comm _ _
    rw [e]
    omega
  · intro heq u v huv
    have hsum : ∑ u, ∑ v, c u v = ∑ _u : X, (r + (N - 1) * errors) := by
      apply le_antisymm (sum_le_sum fun u _ => hup u)
      rw [sum_const, card_univ, smul_eq_mul]
      have e : N * (r + (N - 1) * errors) = r * (N * K) := by
        rw [mul_comm (N - 1), heq]
        calc N * (r + r * (K - 1)) = N * (r * (K - 1) + r) := by ring
          _ = N * (r * K) := by rw [hrK]
          _ = r * (N * K) := by ring
      rw [e]
      exact hlow
    have hu := (sum_eq_sum_iff_of_le (fun u _ => hup u)).1 hsum u (mem_univ u)
    rw [← add_sum_erase _ _ (mem_univ u), hdiag] at hu
    have hu1 := Nat.add_left_cancel hu
    have hu2 : ∑ x ∈ univ.erase u, c u x = ∑ _x ∈ univ.erase u, errors := by
      rw [sum_const, card_erase_of_mem (mem_univ _), card_univ, smul_eq_mul]
      exact hu1
    exact (sum_eq_sum_iff_of_le (fun x hx => h u x (ne_of_mem_erase hx).symm)).1 hu2 v
      (mem_erase.2 ⟨huv.symm, mem_univ _⟩)

theorem gcd_aux (m s : ℕ) (hs : s ≤ m) : Nat.gcd (m - s) m = Nat.gcd m s := by
  have h1 := Nat.gcd_sub_self_right (show m - s ≤ m by omega)
  rw [show m - (m - s) = s by omega] at h1
  rw [← h1, Nat.gcd_sub_self_left hs]

theorem part2 (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) (r errors : ℕ)
    (f : Fin r → (Fin m → Bool) → (Fin s → Bool))
    (h : ∀ u v : Fin m → Bool, u ≠ v →
      (univ.filter (fun i : Fin r => f i u = f i v)).card ≤ errors) :
    r * (2 ^ (m - s) - 1) ≤ errors * (2 ^ m - 1) ∧
    (errors * (2 ^ m - 1) = r * (2 ^ (m - s) - 1) →
      (2 ^ m - 1) / (2 ^ Nat.gcd m s - 1) ∣ r ∧
      ∀ u v : Fin m → Bool, u ≠ v →
        (univ.filter (fun i : Fin r => f i u = f i v)).card = errors) := by
  have hcX : Fintype.card (Fin m → Bool) = 2 ^ m := by simp
  have hX : Fintype.card (Fin m → Bool) = Fintype.card (Fin s → Bool) * 2 ^ (m - s) := by
    rw [hcX]
    simp [← pow_add, Nat.add_sub_cancel' hs]
  obtain ⟨h1, h2⟩ := coll_bound (2 ^ (m - s)) (by positivity) hX (by simp) r errors f h
  rw [hcX] at h1 h2
  refine ⟨h1, fun heq => ⟨?_, h2 heq⟩⟩
  set G := Nat.gcd (2 ^ (m - s) - 1) (2 ^ m - 1) with hGdef
  have hG : G = 2 ^ Nat.gcd m s - 1 := by
    rw [hGdef, Nat.pow_sub_one_gcd_pow_sub_one, gcd_aux m s hs]
  have hgpos : 0 < Nat.gcd m s := Nat.gcd_pos_of_pos_left _ hm
  have hGpos : 0 < G := by
    rw [hG]
    have : 2 ≤ 2 ^ Nat.gcd m s := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Nat.gcd m s := Nat.pow_le_pow_right (by norm_num) hgpos
    omega
  rw [← hG]
  have hcop := Nat.coprime_div_gcd_div_gcd hGpos
  have e1 : 2 ^ (m - s) - 1 = (2 ^ (m - s) - 1) / G * G :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
  have e2 : 2 ^ m - 1 = (2 ^ m - 1) / G * G :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)).symm
  have hh : r * ((2 ^ (m - s) - 1) / G) = errors * ((2 ^ m - 1) / G) := by
    apply Nat.eq_of_mul_eq_mul_right hGpos
    rw [mul_assoc, mul_assoc, ← e1, ← e2]
    exact heq.symm
  apply Nat.Coprime.dvd_of_dvd_mul_right (n := (2 ^ (m - s) - 1) / G) hcop.symm
  rw [hh]
  exact dvd_mul_left _ _


theorem periodic_shift (f : ℕ → ℕ) (p : ℕ) (hf : ∀ j, f (j + p) = f j) :
    ∀ c i, f (p * c + i) = f i := by
  intro c
  induction c with
  | zero => intro i; simp
  | succ c ih =>
    intro i
    rw [Nat.mul_succ, show p * c + p + i = (p * c + i) + p by ring, hf, ih]

theorem periodic_sum (f : ℕ → ℕ) (p : ℕ) (hf : ∀ j, f (j + p) = f j) (c : ℕ) :
    ∑ j ∈ range (p * c), f j = c * ∑ i ∈ range p, f i := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.mul_succ, sum_range_add, ih]
    simp only [periodic_shift f p hf c]
    ring

theorem unit_count {L : Type} [Field L] [Fintype L] [DecidableEq L] (γ : Lˣ)
    (hγ : ∀ y : Lˣ, y ∈ Subgroup.zpowers γ) (W : L → Prop) [DecidablePred W] (hW0 : W 0)
    (x : L) (hx : x ≠ 0) :
    ((range (Fintype.card L - 1)).filter (fun j => W ((γ : L) ^ j * x))).card =
      (univ.filter W).card - 1 := by
  have hn : orderOf γ = Fintype.card L - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card, Fintype.card_units]
  rw [← card_erase_of_mem (mem_filter.2 ⟨mem_univ _, hW0⟩)]
  have hinj : Set.InjOn (fun j => (γ : L) ^ j * x)
      ((range (Fintype.card L - 1)).filter (fun j => W ((γ : L) ^ j * x)) : Set ℕ) := by
    intro a ha b hb hab
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at ha hb
    have h1 : (γ : L) ^ a = (γ : L) ^ b := mul_right_cancel₀ hx hab
    have h2 : γ ^ a = γ ^ b := by
      apply Units.ext
      simpa using h1
    exact pow_injOn_Iio_orderOf (by rw [hn]; exact ha.1) (by rw [hn]; exact hb.1) h2
  rw [← card_image_of_injOn hinj]
  congr 1
  ext y
  simp only [mem_image, mem_filter, mem_range, mem_erase, mem_univ, true_and]
  constructor
  · rintro ⟨j, ⟨_, hW⟩, rfl⟩
    exact ⟨mul_ne_zero (pow_ne_zero _ γ.ne_zero) hx, hW⟩
  · rintro ⟨hy, hW⟩
    have hmem := hγ (Units.mk0 (y * x⁻¹) (mul_ne_zero hy (inv_ne_zero hx)))
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk0⟩ := hmem
    have hk : γ ^ k = Units.mk0 (y * x⁻¹) (mul_ne_zero hy (inv_ne_zero hx)) := hk0
    have hpos : 0 < orderOf γ := orderOf_pos γ
    refine ⟨k % orderOf γ, ⟨?_, ?_⟩, ?_⟩
    · rw [← hn]; exact Nat.mod_lt _ hpos
    · have : (γ : L) ^ (k % orderOf γ) * x = y := by
        have e : (γ : L) ^ (k % orderOf γ) = y * x⁻¹ := by
          rw [← Units.val_pow_eq_pow_val, pow_mod_orderOf, hk]
          simp
        rw [e, mul_assoc, inv_mul_cancel₀ hx, mul_one]
      rw [this]; exact hW
    · have e : (γ : L) ^ (k % orderOf γ) = y * x⁻¹ := by
        rw [← Units.val_pow_eq_pow_val, pow_mod_orderOf, hk]
        simp
      rw [e, mul_assoc, inv_mul_cancel₀ hx, mul_one]

theorem in_range {E L : Type} [Field E] [Fintype E] [Field L] (φ : E →+* L) (β : L)
    (hβ : β ^ Fintype.card E = β) : β ∈ Set.range φ := by
  classical
  by_contra hb
  have hq : 1 < Fintype.card E := Fintype.one_lt_card
  have hdeg : (Polynomial.X ^ Fintype.card E - Polynomial.X : Polynomial L).natDegree =
      Fintype.card E := Polynomial.natDegree_X_pow_sub_X hq
  have hP : (Polynomial.X ^ Fintype.card E - Polynomial.X : Polynomial L) ≠ 0 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
    omega
  have hnot : β ∉ (univ : Finset E).image φ := by
    intro h
    apply hb
    obtain ⟨e, _, he⟩ := mem_image.1 h
    exact ⟨e, he⟩
  have hZ : (insert β ((univ : Finset E).image φ)).val ⊆
      (Polynomial.X ^ Fintype.card E - Polynomial.X : Polynomial L).roots := by
    intro z hz
    rw [Finset.mem_val, mem_insert] at hz
    rw [Polynomial.mem_roots hP]
    simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    rcases hz with rfl | hz
    · rw [hβ, sub_self]
    · obtain ⟨e, _, rfl⟩ := mem_image.1 hz
      rw [← map_pow, FiniteField.pow_card, sub_self]
  have := Polynomial.card_le_degree_of_subset_roots hZ
  rw [card_insert_of_notMem hnot, card_image_of_injective _ φ.injective, card_univ, hdeg] at this
  omega

def tz (b : Bool) : ZMod 2 := if b then 1 else 0

def fz (z : ZMod 2) : Bool := decide (z = 1)

theorem tz_xor (a b : Bool) : tz (xor a b) = tz a + tz b := by
  cases a <;> cases b <;> decide

theorem fz_add : ∀ a b : ZMod 2, fz (a + b) = xor (fz a) (fz b) := by decide

theorem fz_inj : ∀ a b : ZMod 2, fz a = fz b → a = b := by decide

theorem fz_tz (b : Bool) : fz (tz b) = b := by cases b <;> decide

theorem tz_fz : ∀ z : ZMod 2, tz (fz z) = z := by decide

theorem tz_inj (a b : Bool) (h : tz a = tz b) : a = b := by
  rw [← fz_tz a, h, fz_tz]

theorem exists_family (m s : ℕ) (hm : 0 < m) (hs : s ≤ m) :
    ∃ family : Fin ((2 ^ m - 1) / (2 ^ Nat.gcd m s - 1)) → (Fin m → Bool) → (Fin s → Bool),
      (∀ i, Function.Surjective (family i)) ∧
      (∀ i u v, family i (fun j => xor (u j) (v j)) =
        fun out => xor (family i u out) (family i v out)) ∧
      ∀ u v : Fin m → Bool, u ≠ v →
        (univ.filter (fun i => family i u = family i v)).card =
          (2 ^ (m - s) - 1) / (2 ^ Nat.gcd m s - 1) := by
  classical
  set g := Nat.gcd m s with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  have hgm : g ∣ m := Nat.gcd_dvd_left _ _
  have hgs : g ∣ s := Nat.gcd_dvd_right _ _
  let _ : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  let _ : Fintype (GaloisField 2 g) := Fintype.ofFinite _
  have hcardL : Fintype.card (GaloisField 2 m) = 2 ^ m := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 m (by omega)
  have hcardE : Fintype.card (GaloisField 2 g) = 2 ^ g := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 g (by omega)
  have hfr : Module.finrank (ZMod 2) (GaloisField 2 g) ∣
      Module.finrank (ZMod 2) (GaloisField 2 m) := by
    rw [GaloisField.finrank 2 (by omega), GaloisField.finrank 2 (by omega)]
    exact hgm
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hfr
  let _ : Algebra (GaloisField 2 g) (GaloisField 2 m) := φ.toRingHom.toAlgebra
  have : Module.Finite (GaloisField 2 g) (GaloisField 2 m) := Module.Finite.of_finite
  set d := Module.finrank (GaloisField 2 g) (GaloisField 2 m) with hd
  have hmd : m = g * d := by
    have := Module.card_eq_pow_finrank (K := GaloisField 2 g) (V := GaloisField 2 m)
    rw [hcardL, hcardE, ← pow_mul] at this
    exact Nat.pow_right_injective le_rfl this
  set t := s / g with ht
  have hst : s = g * t := (Nat.mul_div_cancel' hgs).symm
  have htd : t ≤ d := Nat.le_of_mul_le_mul_left (by omega : g * t ≤ g * d) hg0
  let b := Module.finBasis (GaloisField 2 g) (GaloisField 2 m)
  let ρ : GaloisField 2 m →ₗ[GaloisField 2 g] (Fin t → GaloisField 2 g) :=
    (LinearMap.funLeft (GaloisField 2 g) (GaloisField 2 g) (Fin.castLE htd)) ∘ₗ
      b.equivFun.toLinearMap
  have hρ : Function.Surjective ρ :=
    (LinearMap.funLeft_surjective_of_injective (GaloisField 2 g) (GaloisField 2 g) _
      (Fin.castLE_injective htd)).comp
      b.equivFun.surjective
  have hcardT : Fintype.card (Fin t → GaloisField 2 g) = 2 ^ s := by
    rw [Fintype.card_fun, hcardE, Fintype.card_fin, ← pow_mul, hst]
  have hfrT : Module.finrank (ZMod 2) (Fin t → GaloisField 2 g) =
      Module.finrank (ZMod 2) (Fin s → ZMod 2) := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod 2) (V := Fin t → GaloisField 2 g)
    rw [hcardT, ZMod.card] at h1
    rw [Module.finrank_fin_fun]
    exact (Nat.pow_right_injective le_rfl h1).symm
  let e2 := LinearEquiv.ofFinrankEq _ _ hfrT
  have hfrL : Module.finrank (ZMod 2) (Fin m → ZMod 2) =
      Module.finrank (ZMod 2) (GaloisField 2 m) := by
    rw [Module.finrank_fin_fun, GaloisField.finrank 2 (by omega)]
  let ψ := LinearEquiv.ofFinrankEq _ _ hfrL
  -- the kernel
  have hWmul : ∀ (e : GaloisField 2 g) (y : GaloisField 2 m), ρ y = 0 → ρ (φ e * y) = 0 := by
    intro e y hy
    have : φ e * y = e • y := by rw [Algebra.smul_def]; rfl
    rw [this, map_smul, hy, smul_zero]
  have hfib : ∀ z, (univ.filter (fun y => ρ y = z)).card =
      (univ.filter (fun y => ρ y = 0)).card := by
    intro z
    obtain ⟨y0, hy0⟩ := hρ z
    apply card_nbij' (fun y => y - y0) (fun y => y + y0)
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      rw [map_sub, hy, hy0, sub_self]
    · intro y hy
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
      rw [map_add, hy, hy0, zero_add]
    · intro y _; simp
    · intro y _; simp
  have hker : (univ.filter (fun y => ρ y = 0)).card = 2 ^ (m - s) := by
    have h1 : Fintype.card (GaloisField 2 m) =
        ∑ z : Fin t → GaloisField 2 g, (univ.filter (fun y => ρ y = z)).card := by
      rw [← card_univ]
      exact card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    rw [sum_congr rfl (fun z _ => hfib z), sum_const, card_univ, hcardT, smul_eq_mul,
      hcardL] at h1
    have h2 : 2 ^ m = 2 ^ s * 2 ^ (m - s) := by rw [← pow_add, Nat.add_sub_cancel' hs]
    exact Nat.eq_of_mul_eq_mul_left (by positivity) (h1.symm.trans h2)
  -- the generator
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (GaloisField 2 m)ˣ)
  have hn : orderOf γ = 2 ^ m - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card,
      Fintype.card_units, hcardL]
  set c := 2 ^ g - 1 with hc
  have hc1 : 2 ^ g = c + 1 := by
    have : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    omega
  have hcpos : 0 < c := by
    have : 2 ≤ 2 ^ g := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg0
    omega
  have hcdvd : c ∣ 2 ^ m - 1 := by
    have := Nat.pow_sub_one_gcd_pow_sub_one 2 g m
    rw [Nat.gcd_eq_left hgm] at this
    rw [hc, ← this]
    exact Nat.gcd_dvd_right _ _
  have hcdvd' : c ∣ 2 ^ (m - s) - 1 := by
    have := Nat.pow_sub_one_gcd_pow_sub_one 2 g (m - s)
    rw [Nat.gcd_eq_left (Nat.dvd_sub hgm hgs)] at this
    rw [hc, ← this]
    exact Nat.gcd_dvd_right _ _
  set p := (2 ^ m - 1) / c with hp
  have hpc : p * c = 2 ^ m - 1 := Nat.div_mul_cancel hcdvd
  set β : GaloisField 2 m := (γ : GaloisField 2 m) ^ p with hβ
  have hβc : β ^ c = 1 := by
    rw [hβ, ← pow_mul, hpc, ← hn, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hβ0 : β ≠ 0 := pow_ne_zero _ γ.ne_zero
  obtain ⟨eβ, heβ⟩ := in_range φ.toRingHom β (by
    rw [hcardE, hc1, pow_succ, hβc, one_mul])
  have heβ' : φ eβ = β := heβ
  have hper : ∀ y : GaloisField 2 m, ρ (β * y) = 0 ↔ ρ y = 0 := by
    intro y
    constructor
    · intro h
      have := hWmul eβ⁻¹ _ h
      rwa [map_inv₀, heβ', ← mul_assoc, inv_mul_cancel₀ hβ0, one_mul] at this
    · intro h
      have := hWmul eβ y h
      rwa [heβ'] at this
  -- the count for a fixed nonzero difference
  have hcount : ∀ x : GaloisField 2 m, x ≠ 0 →
      ((range p).filter (fun i => ρ ((γ : GaloisField 2 m) ^ i * x) = 0)).card =
        (2 ^ (m - s) - 1) / c := by
    intro x hx
    have hall := unit_count γ hγ (fun y => ρ y = 0) (map_zero ρ) x hx
    rw [hcardL, hker, ← hpc] at hall
    let F : ℕ → ℕ := fun j => if ρ ((γ : GaloisField 2 m) ^ j * x) = 0 then 1 else 0
    have hf : ∀ j, F (j + p) = F j := by
      intro j
      simp only [F]
      rw [show (γ : GaloisField 2 m) ^ (j + p) * x = β * ((γ : GaloisField 2 m) ^ j * x) by
        rw [hβ, pow_add]; ring]
      simp only [hper]
    have hs := periodic_sum F p hf c
    simp only [F] at hs
    rw [← card_filter, ← card_filter] at hs
    rw [hs] at hall
    symm
    apply Nat.div_eq_of_eq_mul_left hcpos
    rw [← hall, mul_comm]
  -- the family
  let fam : Fin p → (Fin m → Bool) → (Fin s → Bool) := fun i u out =>
    fz (e2 (ρ ((γ : GaloisField 2 m) ^ (i : ℕ) * ψ (fun j => tz (u j)))) out)
  have hfam : ∀ i u v, fam i u = fam i v ↔
      ρ ((γ : GaloisField 2 m) ^ (i : ℕ) * (ψ (fun j => tz (u j)) - ψ (fun j => tz (v j)))) = 0 := by
    intro i u v
    rw [mul_sub, map_sub, sub_eq_zero]
    constructor
    · intro h
      apply e2.injective
      funext out
      exact fz_inj _ _ (congrFun h out)
    · intro h
      funext out
      simp only [fam, h]
  refine ⟨fam, ?_, ?_, ?_⟩
  · intro i y
    obtain ⟨a, ha⟩ := hρ (e2.symm (fun out => tz (y out)))
    refine ⟨fun j => fz (ψ.symm (((γ⁻¹ : (GaloisField 2 m)ˣ) : GaloisField 2 m) ^ (i : ℕ) * a) j), ?_⟩
    funext out
    simp only [fam, tz_fz]
    have e : (fun j => (ψ.symm (((γ⁻¹ : (GaloisField 2 m)ˣ) : GaloisField 2 m) ^ (i : ℕ) * a)) j) =
        ψ.symm (((γ⁻¹ : (GaloisField 2 m)ˣ) : GaloisField 2 m) ^ (i : ℕ) * a) := rfl
    rw [e, LinearEquiv.apply_symm_apply, ← mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, one_pow, one_mul, ha, LinearEquiv.apply_symm_apply, fz_tz]
  · intro i u v
    funext out
    simp only [fam]
    have e : (fun j => tz (xor (u j) (v j))) = (fun j => tz (u j)) + (fun j => tz (v j)) := by
      funext j; simp [tz_xor]
    rw [e, map_add, mul_add, map_add, map_add, Pi.add_apply, fz_add]
  · intro u v huv
    have hx : ψ (fun j => tz (u j)) - ψ (fun j => tz (v j)) ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply huv
      funext j
      exact tz_inj _ _ (congrFun (ψ.injective h) j)
    rw [← hcount _ hx]
    simp only [hfam]
    rw [card_filter, card_filter]
    exact Fin.sum_univ_eq_sum_range
      (fun i => if ρ ((γ : GaloisField 2 m) ^ i *
        (ψ (fun j => tz (u j)) - ψ (fun j => tz (v j)))) = 0 then 1 else 0) p

end PEqualNP.Outside.L_lib_415

open PEqualNP.Outside.L_lib_415 in
theorem PEqualNP.Outside.L_lib_415 : ∀ (m s : ℕ), 0 < m → s ≤ m →
  let N := 2 ^ m
  let K := 2 ^ (m - s)
  let divisor := 2 ^ Nat.gcd m s - 1
  let period := (N - 1) / divisor
  let hits := (K - 1) / divisor
  let X := Fin m → Bool
  let Y := Fin s → Bool
  let collisions := fun (r : ℕ) (f : Fin r → X → Y) (u v : X) =>
    (Finset.univ.filter (fun i : Fin r => f i u = f i v)).card
  (∃ family : Fin period → X → Y,
    (∀ i, Function.Surjective (family i)) ∧
    (∀ i u v, family i (fun j => xor (u j) (v j)) =
      fun out => xor (family i u out) (family i v out)) ∧
    ∀ u v : X, u ≠ v → collisions period family u v = hits) ∧
  ∀ (r errors : ℕ) (f : Fin r → X → Y), 0 < r →
    (∀ u v : X, u ≠ v → collisions r f u v ≤ errors) →
    r * (K - 1) ≤ errors * (N - 1) ∧
    (errors * (N - 1) = r * (K - 1) →
      period ∣ r ∧ ∀ u v : X, u ≠ v → collisions r f u v = errors) := by
  intro m s hm hs N K divisor period hits X Y collisions
  exact ⟨exists_family m s hm hs, fun r errors f _ h => part2 m s hm hs r errors f h⟩
