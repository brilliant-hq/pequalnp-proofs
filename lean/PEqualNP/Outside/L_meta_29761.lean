import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_29761

abbrev F := ZMod 2
abbrev W (k : ℕ) := ZMod k → F
variable {k : ℕ} [NeZero k]

def rot (r : ℕ) (x : W k) (i : ZMod k) := x (i - r)
def mix (s : ℕ) (x : W k) (i : ZMod k) := x (i-s) + x i + x (i+s)
def chi (z : W k) (i : ZMod k) := z i + (1+z (i+1))*z (i+2)
def delta (a z : W k) (i : ZMod k) :=
  a i + (1+z (i+1))*a (i+2) + a (i+1)*(z (i+2)+a (i+2))
def update (s : ℕ) (x : W k) := chi (mix s x)

theorem mix_add (s : ℕ) (x y : W k) : mix s (x+y) = mix s x + mix s y := by
  funext i
  simp only [mix, Pi.add_apply]
  ring

theorem rot_add (s : ℕ) (x y : W k) : rot s (x+y) = rot s x + rot s y := rfl

theorem chi_add (z a : W k) : chi (z+a) = chi z + delta a z := by
  funext i
  simp only [chi, delta, Pi.add_apply]
  ring

theorem mix_surj (hk : k % 3 ≠ 0) (s : ℕ) : Function.Surjective (mix (k:=k) s) := by
  apply Finite.injective_iff_surjective.mp
  intro x y he
  let d : W k := x-y
  have hd (i : ZMod k) : d (i-s) + d i + d (i+s) = 0 := by
    have h := congrFun he i
    dsimp [mix] at h
    dsimp [d]
    linear_combination h
  have periodic (i : ZMod k) : d (i + 3 * s) = d i := by
    have h₁ := hd (i+s)
    have h₂ := hd (i+2*s)
    rw [show i + (s:ZMod k) - s = i by ring,
      show i + (s:ZMod k) + s = i+2*s by ring] at h₁
    rw [show i + 2*(s:ZMod k) - s = i+s by ring,
      show i + 2*(s:ZMod k) + s = i+3*s by ring] at h₂
    linear_combination h₂ - h₁
  have iter (n : ℕ) (i : ZMod k) : d (i + n * (3 * (s:ZMod k))) = d i := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, periodic, ih]
  have mult : ∃ n : ℕ, (n:ZMod k)*3 = 1 := by
    by_cases h : k % 3 = 2
    · use (k+1)/3
      have heq : (k+1)/3*3=k+1 := by omega
      have hh := congrArg (fun n : ℕ => (n : ZMod k)) heq
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, zero_add] using hh
    · use (2*k+1)/3
      have heq : (2*k+1)/3*3=2*k+1 := by omega
      have hh := congrArg (fun n : ℕ => (n : ZMod k)) heq
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, mul_zero, zero_add] using hh
  obtain ⟨n,hn⟩ := mult
  have per (i : ZMod k) : d (i+s) = d i := by
    simpa only [← mul_assoc, hn, one_mul] using iter n i
  funext i
  have h := hd i
  have h' := per (i-s)
  rw [sub_add_cancel] at h'
  rw [← h', per, CharTwo.add_self_eq_zero, zero_add] at h
  exact sub_eq_zero.mp h

theorem independent (hk : k % 3 ≠ 0) (s r p : ℕ) (c : W k) (z w : W k) :
    ∃ key name : W k, mix s (rot r key + name) = z ∧
      mix s (chi z + rot p key + c) = w := by
  obtain ⟨v,hv⟩ := mix_surj hk s w
  obtain ⟨u,hu⟩ := mix_surj hk s z
  let key : W k := fun i => (v - c - chi z) (i+p)
  have hrot : rot p key = v - c - chi z := by
    funext i
    simp [rot, key]
  refine ⟨key, u - rot r key, ?_, ?_⟩
  · rwa [add_sub_cancel]
  · rw [hrot, show chi z + (v-c-chi z) + c = v by abel, hv]

def shiftRun (s r p t : ℕ) (key name c₁ c₂ : W k) :=
  update s (update s (rot r key + name) + rot p key + c₁) + rot t key + c₂

def inc (s : ℕ) (a b z : W k) := mix s (delta a z) + b

theorem shift_identity (s r p t : ℕ) (key name c₁ c₂ dn dk : W k) (i : ZMod k) :
    shiftRun s r p t (key+dk) (name+dn) c₁ c₂ i + shiftRun s r p t key name c₁ c₂ i =
      delta (inc s (mix s (rot r dk + dn)) (mix s (rot p dk)) (mix s (rot r key + name)))
        (mix s (update s (rot r key+name)+rot p key+c₁)) i + rot t dk i := by
  let z := mix s (rot r key+name)
  let a := mix s (rot r dk+dn)
  let w := mix s (chi z + rot p key + c₁)
  have hz : mix s (rot r (key+dk) + (name+dn)) = z+a := by
    rw [rot_add, show rot r key + rot r dk + (name+dn) =
      (rot r key + name) + (rot r dk + dn) by abel, mix_add]
  have hw : mix s (chi (z+a) + rot p (key+dk) + c₁) =
      w + inc s a (mix s (rot p dk)) z := by
    rw [chi_add, rot_add, show chi z + delta a z + (rot p key + rot p dk) + c₁ =
      (chi z + rot p key + c₁) + (delta a z + rot p dk) by abel, mix_add, mix_add s (delta a z)]
    rfl
  change (chi (mix s (chi (mix s (rot r (key+dk)+(name+dn))) + rot p (key+dk) + c₁)) + rot t (key+dk) + c₂) i +
    (chi w + rot t key + c₂) i = delta (inc s a (mix s (rot p dk)) z) w i + rot t dk i
  rw [hz, hw, chi_add, rot_add]
  simp only [Pi.add_apply]
  abel_nf
  simp [two_mul, CharTwo.add_self_eq_zero]

end PEqualNP.Outside.L_meta_29761

namespace PEqualNP.Outside.L_meta_29761

variable {k m : ℕ} [NeZero k]

def pulse (j i : ZMod k) : ZMod 2 := if i=j then 1 else 0

def edge (a z : ZMod k → ZMod 2) (i j : ZMod k) :=
  z i * a j + a i * z j

theorem consecutive_inj (h : m ≤ k) (j : ZMod k) :
    Function.Injective (fun q : Fin m => j + (q.val : ZMod k)) := by
  intro p q hpq
  apply Fin.ext
  have he : (p.val : ZMod k) = q.val := add_left_cancel hpq
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt (p.isLt.trans_le h), ZMod.val_natCast_of_lt (q.isLt.trans_le h)] using hv

theorem path_zero (p : Fin 4 → ZMod k) (hp : Function.Injective p)
    (a : ZMod k → ZMod 2)
    (h : ∀ z, edge a z (p 0) (p 1) + edge a z (p 1) (p 2) + edge a z (p 2) (p 3) = 0) :
    ∀ q, a (p q) = 0 := by
  have h₀ := h (pulse (p 0))
  have h₁ := h (pulse (p 1))
  have h₂ := h (pulse (p 2))
  have h₃ := h (pulse (p 3))
  norm_num [edge, pulse, hp.eq_iff] at h₀ h₁ h₂ h₃
  intro q
  fin_cases q <;> simp_all

theorem disjoint_zero (p : Fin 6 → ZMod k) (hp : Function.Injective p)
    (a : ZMod k → ZMod 2)
    (h : ∀ z, edge a z (p 0) (p 1) + edge a z (p 2) (p 3) + edge a z (p 4) (p 5) = 0) :
    ∀ q, a (p q) = 0 := by
  have h₀ := h (pulse (p 0))
  have h₁ := h (pulse (p 1))
  have h₂ := h (pulse (p 2))
  have h₃ := h (pulse (p 3))
  have h₄ := h (pulse (p 4))
  have h₅ := h (pulse (p 5))
  norm_num [edge, pulse, hp.eq_iff] at h₀ h₁ h₂ h₃ h₄ h₅
  intro q
  fin_cases q <;> simp_all

end PEqualNP.Outside.L_meta_29761

namespace PEqualNP.Outside.L_meta_29761

variable {k : ℕ} [NeZero k]

theorem inc_affine (s : ℕ) (a b z : W k) (j : ZMod k) :
    inc s a b z j = inc s a b 0 j +
      (edge a z ((j-s)+1) ((j-s)+2) + edge a z (j+1) (j+2) +
       edge a z ((j+s)+1) ((j+s)+2)) := by
  simp only [inc, Pi.add_apply, mix, delta, edge, Pi.zero_apply]
  ring

theorem row_window (hk : 7 ≤ k) (a b : W k) (j : ZMod k) (v : F) :
    (∀ z : W k, inc 1 a b z j = v) ↔
    (∀ q : Fin 4, a (j + (q.val : ZMod k)) = 0) ∧ a (j-1) + b j = v := by
  let p : Fin 4 → ZMod k := fun q => j + (q.val : ZMod k)
  have hp : Function.Injective p := consecutive_inj (by omega) j
  have e0 : ((j-1)+1) = p 0 := by norm_num [p] <;> ring
  have e1 : ((j-1)+2) = p 1 := by norm_num [p] <;> ring
  have e2 : (j+1) = p 1 := by norm_num [p] <;> ring
  have e3 : (j+2) = p 2 := by norm_num [p] <;> ring
  have e4 : ((j+1)+1) = p 2 := by norm_num [p] <;> ring
  have e5 : ((j+1)+2) = p 3 := by norm_num [p] <;> ring
  have aff (z : W k) : inc 1 a b z j = inc 1 a b 0 j + (edge a z (p 0) (p 1) + edge a z (p 1) (p 2) + edge a z (p 2) (p 3)) := by
    rw [inc_affine]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    exact congrArg (fun x => inc 1 a b 0 j + x) (congrArg₂ (·+·)
      (congrArg₂ (·+·) (congrArg₂ (edge a z) e0 e1) (congrArg₂ (edge a z) e2 e3))
      (congrArg₂ (edge a z) e4 e5))
  have base (h : ∀ q, a (p q) = 0) : inc 1 a b 0 j = a (j-1) + b j := by
    have h0 : a ((j-1)+1) = 0 := by
      calc
        _ = a (p 0) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 0
    have h1 : a ((j-1)+2) = 0 := by
      calc
        _ = a (p 1) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 1
    have h2 : a (j+1) = 0 := by
      calc
        _ = a (p 1) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 1
    have h3 : a (j+2) = 0 := by
      calc
        _ = a (p 2) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 2
    have h4 : a ((j+1)+1) = 0 := by
      calc
        _ = a (p 2) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 2
    have h5 : a ((j+1)+2) = 0 := by
      calc
        _ = a (p 3) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 3
    have h6 : a j = 0 := by
      calc
        _ = a (p 0) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 0
    have h7 : a (j+1) = 0 := by
      calc
        _ = a (p 1) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 1
    simp only [inc, mix, delta, Pi.add_apply, Nat.cast_one, Nat.cast_ofNat, Pi.zero_apply, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero, mul_zero, zero_mul]
  constructor
  · intro h
    have hz := h 0
    have localZero : ∀ q, a (p q) = 0 := by
      apply path_zero p hp a
      intro z
      have he := h z
      rw [aff] at he
      linear_combination he - hz
    exact ⟨localZero, (base localZero).symm.trans hz⟩
  · rintro ⟨h, hv⟩ z
    change ∀ q, a (p q) = 0 at h
    rw [aff z, base h]
    simpa only [edge, h, mul_zero, zero_mul, add_zero] using hv

theorem col_window (hk : 7 ≤ k) (a b : W k) (j : ZMod k) (v : F) :
    (∀ z : W k, inc 2 a b z j = v) ↔
    (∀ q : Fin 6, a ((j-1) + (q.val : ZMod k)) = 0) ∧ a (j-2) + b j = v := by
  let p : Fin 6 → ZMod k := fun q => (j-1) + (q.val : ZMod k)
  have hp : Function.Injective p := consecutive_inj (by omega) (j-1)
  have e0 : ((j-2)+1) = p 0 := by norm_num [p] <;> ring
  have e1 : ((j-2)+2) = p 1 := by norm_num [p] <;> ring
  have e2 : (j+1) = p 2 := by norm_num [p] <;> ring
  have e3 : (j+2) = p 3 := by norm_num [p] <;> ring
  have e4 : ((j+2)+1) = p 4 := by norm_num [p] <;> ring
  have e5 : ((j+2)+2) = p 5 := by norm_num [p] <;> ring
  have aff (z : W k) : inc 2 a b z j = inc 2 a b 0 j + (edge a z (p 0) (p 1) + edge a z (p 2) (p 3) + edge a z (p 4) (p 5)) := by
    rw [inc_affine]
    simp only [Nat.cast_one, Nat.cast_ofNat]
    exact congrArg (fun x => inc 2 a b 0 j + x) (congrArg₂ (·+·)
      (congrArg₂ (·+·) (congrArg₂ (edge a z) e0 e1) (congrArg₂ (edge a z) e2 e3))
      (congrArg₂ (edge a z) e4 e5))
  have base (h : ∀ q, a (p q) = 0) : inc 2 a b 0 j = a (j-2) + b j := by
    have h0 : a ((j-2)+1) = 0 := by
      calc
        _ = a (p 0) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 0
    have h1 : a ((j-2)+2) = 0 := by
      calc
        _ = a (p 1) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 1
    have h2 : a (j+1) = 0 := by
      calc
        _ = a (p 2) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 2
    have h3 : a (j+2) = 0 := by
      calc
        _ = a (p 3) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 3
    have h4 : a ((j+2)+1) = 0 := by
      calc
        _ = a (p 4) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 4
    have h5 : a ((j+2)+2) = 0 := by
      calc
        _ = a (p 5) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 5
    have h6 : a j = 0 := by
      calc
        _ = a (p 1) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 1
    have h7 : a (j+2) = 0 := by
      calc
        _ = a (p 3) := congrArg a (by norm_num [p] <;> ring)
        _ = 0 := h 3
    simp only [inc, mix, delta, Pi.add_apply, Nat.cast_one, Nat.cast_ofNat, Pi.zero_apply, h0, h1, h2, h3, h4, h5, h6, h7, zero_add, add_zero, mul_zero, zero_mul]
  constructor
  · intro h
    have hz := h 0
    have localZero : ∀ q, a (p q) = 0 := by
      apply disjoint_zero p hp a
      intro z
      have he := h z
      rw [aff] at he
      linear_combination he - hz
    exact ⟨localZero, (base localZero).symm.trans hz⟩
  · rintro ⟨h, hv⟩ z
    change ∀ q, a (p q) = 0 at h
    rw [aff z, base h]
    simpa only [edge, h, mul_zero, zero_mul, add_zero] using hv


end PEqualNP.Outside.L_meta_29761

namespace PEqualNP.Outside.L_meta_29761

variable {k : ℕ} [NeZero k]

theorem outer_one (hk : 7 ≤ k) (t : W k) (i : ZMod k) (off value : F) :
    (∀ w : W k, delta t w i + off = value) ↔
    t (i+1) = 0 ∧ t (i+2) = 0 ∧ t i = value-off := by
  have distinct : i+1 ≠ i+2 := by
    have hin := consecutive_inj (m:=3) (by omega : 3 ≤ k) i
    intro h
    have h' : (1 : Fin 3) = 2 := hin (by simpa using h)
    exact (by decide : (1 : Fin 3) ≠ 2) h'
  constructor
  · intro h
    have h₀ := h 0
    have h₁ := h (pulse (i+1))
    have h₂ := h (pulse (i+2))
    simp only [delta, Pi.zero_apply, pulse, if_pos rfl, if_true, if_neg distinct, if_neg (Ne.symm distinct),
      zero_add, add_zero, mul_one, one_mul, mul_zero, zero_mul, CharTwo.add_self_eq_zero] at h₀ h₁ h₂
    have hz₁ : t (i+1) = 0 := by linear_combination h₂ - h₀
    have hz₂ : t (i+2) = 0 := by
      rw [hz₁, zero_mul, add_zero] at h₀ h₁
      linear_combination h₀ - h₁
    refine ⟨hz₁, hz₂, ?_⟩
    simp [hz₁, hz₂] at h₀
    linear_combination h₀
  · rintro ⟨h₁,h₂,h⟩ w
    simp only [delta, h₁, h₂, mul_zero, zero_mul, add_zero]
    linear_combination h

theorem outer_all (hk : 7 ≤ k) (s : ℕ) (a b : W k) (i : ZMod k) (off value : F) :
    (∀ z w : W k, delta (inc s a b z) w i + off = value) ↔
    (∀ z, inc s a b z i = value-off) ∧
    (∀ z, inc s a b z (i+1) = 0) ∧ (∀ z, inc s a b z (i+2) = 0) := by
  constructor
  · intro h
    have hh (z : W k) := (outer_one hk _ i off value).mp (h z)
    exact ⟨fun z => (hh z).2.2, fun z => (hh z).1, fun z => (hh z).2.1⟩
  · rintro ⟨h,h₁,h₂⟩ z
    exact (outer_one hk _ i off value).mpr ⟨h₁ z,h₂ z,h z⟩

end PEqualNP.Outside.L_meta_29761

namespace PEqualNP.Outside.L_meta_29761

variable {k : ℕ} [NeZero k]

theorem reduceRun (hk : k % 3 ≠ 0) (s r p t : ℕ) (c₁ c₂ dn dk : W k)
    (i : ZMod k) (v : F) :
    (∀ key name : W k, shiftRun s r p t (key+dk) (name+dn) c₁ c₂ i +
      shiftRun s r p t key name c₁ c₂ i = v) ↔
    (∀ z w : W k, delta (inc s (mix s (rot r dk+dn)) (mix s (rot p dk)) z) w i +
      rot t dk i = v) := by
  constructor
  · intro h z w
    obtain ⟨key,name,hz,hw⟩ := independent hk s r p c₁ z w
    have hh := h key name
    rw [shift_identity, hz] at hh
    unfold update at hh
    rwa [hz, hw] at hh
  · intro h key name
    rw [shift_identity]
    exact h _ _

theorem glue (i d : ZMod k) (a b : W k) (n : ℕ) (hn : 2 ≤ n) (off v : F) :
    (((∀ q : Fin n, a (i-d+q.val) = 0) ∧ a (i-(d+1)) + b i = v-off) ∧
     ((∀ q : Fin n, a (i+1-d+q.val) = 0) ∧ a (i+1-(d+1)) + b (i+1) = 0) ∧
     ((∀ q : Fin n, a (i+2-d+q.val) = 0) ∧ a (i+2-(d+1)) + b (i+2) = 0)) ↔
    (∀ q : Fin (n+2), a (i-d+q.val) = 0) ∧ b (i+1) = 0 ∧ b (i+2) = 0 ∧
      v = a (i-(d+1)) + b i + off := by
  have shifted (h : ∀ q : Fin (n+2), a (i-d+q.val) = 0) (m : ℕ) (hm : m ≤ 2)
      (q : Fin n) : a (i+m-d+q.val) = 0 := by
    have lt := q.isLt
    have hz := h ⟨q.val+m, by omega⟩
    simpa only [Nat.cast_add, show i - d + (q.val + (m : ZMod k)) = i+m-d+q.val by ring] using hz
  have first_two (h : ∀ q : Fin (n+2), a (i-d+q.val) = 0) :
      a (i+1-(d+1)) = 0 ∧ a (i+2-(d+1)) = 0 := by
    have h₀ := h ⟨0, by omega⟩
    have h₁ := h ⟨1, by omega⟩
    rw [show i+1-(d+1) = i-d by ring, show i+2-(d+1) = i-d+1 by ring]
    exact ⟨by simpa using h₀, by simpa using h₁⟩
  constructor
  · rintro ⟨⟨w₀,hv⟩,⟨_,hb₁⟩,w₂,hb₂⟩
    have h (q : Fin (n+2)) : a (i-d+q.val) = 0 := by
      by_cases hq : q.val < n
      · exact w₀ ⟨q.val,hq⟩
      · have lt := q.isLt
        have h₂ := w₂ ⟨q.val-2, by omega⟩
        have eq : (q.val : ZMod k) = (q.val-2 : ℕ) + (2 : ZMod k) := by
          have he := congrArg (fun x : ℕ => (x : ZMod k)) (show q.val = (q.val-2)+2 by omega)
          simpa only [Nat.cast_add, Nat.cast_ofNat] using he
        rw [eq, show i-d+((↑(q.val-2 : ℕ) : ZMod k)+2) = i+2-d+↑(q.val-2 : ℕ) by ring]
        exact h₂
    obtain ⟨z₁,z₂⟩ := first_two h
    exact ⟨h, by simpa only [z₁, zero_add] using hb₁,
      by simpa only [z₂, zero_add] using hb₂, by linear_combination -hv⟩
  · rintro ⟨h,hb₁,hb₂,hv⟩
    obtain ⟨z₁,z₂⟩ := first_two h
    exact ⟨⟨fun q => by simpa using shifted h 0 (by decide) q, by linear_combination -hv⟩,
      ⟨fun q => by simpa using shifted h 1 (by decide) q, by rw [z₁, zero_add, hb₁]⟩,
      fun q => by simpa using shifted h 2 (by decide) q, by rw [z₂, zero_add, hb₂]⟩

theorem row_class (hk : 7 ≤ k) (a b : W k) (i : ZMod k) (off v : F) :
    (∀ z w : W k, delta (inc 1 a b z) w i + off = v) ↔
    (∀ q : Fin 6, a (i-0+q.val) = 0) ∧ b (i+1) = 0 ∧ b (i+2) = 0 ∧
      v = a (i-1) + b i + off := by
  rw [outer_all hk, row_window hk, row_window hk, row_window hk]
  simpa only [sub_zero, zero_add, one_add_one_eq_two] using glue i 0 a b 4 (by decide) off v

theorem col_class (hk : 7 ≤ k) (a b : W k) (i : ZMod k) (off v : F) :
    (∀ z w : W k, delta (inc 2 a b z) w i + off = v) ↔
    (∀ q : Fin 8, a (i-1+q.val) = 0) ∧ b (i+1) = 0 ∧ b (i+2) = 0 ∧
      v = a (i-2) + b i + off := by
  rw [outer_all hk, col_window hk, col_window hk, col_window hk]
  simpa only [sub_zero, zero_add, one_add_one_eq_two] using glue i 1 a b 6 (by decide) off v

end PEqualNP.Outside.L_meta_29761

open PEqualNP.Outside.L_meta_29761

theorem PEqualNP.Outside.L_meta_29761 : (∀ (k : ℕ) [NeZero k], 7 ≤ k → k % 3 ≠ 0 →
  let I := ZMod k
  let W := I → ZMod 2
  let rot := fun (s : ℕ) (x : W) (i : I) => x (i-(s : I))
  let mix := fun (s : ℕ) (x : W) (i : I) => x (i-(s : I)) + x i + x (i+(s : I))
  let update := fun (s : ℕ) (x : W) (i : I) =>
    let z := mix s x
    z i + (1+z (i+1))*z (i+2)
  let run := fun (col : Bool) (key name c1 c2 : W) =>
    let s : ℕ := if col then 2 else 1
    let first := update s (rot (if col then 3 else 1) key + name) +
      rot (if col then 4 else 0) key + c1
    update s first + rot (if col then 7 else 2) key + c2
  ∀ (col : Bool) (c1 c2 dn dk : W) (site : I) (value : ZMod 2),
    let s : ℕ := if col then 2 else 1
    let a := mix s (rot (if col then 3 else 1) dk + dn)
    let b := mix s (rot (if col then 4 else 0) dk)
    let f := rot (if col then 7 else 2) dk
    Iff (∀ key name : W,
      run col (key+dk) (name+dn) c1 c2 site + run col key name c1 c2 site = value)
      ((∀ q : Fin (if col then 8 else 6),
        a (site - (if col then 1 else 0) + (q.val : I)) = 0) ∧
       b (site+1) = 0 ∧ b (site+2) = 0 ∧
       value = a (site-(if col then 2 else 1)) + b site + f site)) := by
  intro k inst hsize hk
  dsimp only
  intro col c₁ c₂ dn dk i v
  cases col
  · change (∀ key name : W k, shiftRun 1 1 0 2 (key+dk) (name+dn) c₁ c₂ i +
        shiftRun 1 1 0 2 key name c₁ c₂ i = v) ↔
        (∀ q : Fin 6, (mix 1 (rot 1 dk + dn)) (i-0+q.val) = 0) ∧
        (mix 1 (rot 0 dk)) (i+1) = 0 ∧ (mix 1 (rot 0 dk)) (i+2) = 0 ∧ v = (mix 1 (rot 1 dk + dn)) (i-1) + (mix 1 (rot 0 dk)) i + rot 2 dk i
    exact (reduceRun hk 1 1 0 2 c₁ c₂ dn dk i v).trans (row_class hsize _ _ i _ v)
  · change (∀ key name : W k, shiftRun 2 3 4 7 (key+dk) (name+dn) c₁ c₂ i +
        shiftRun 2 3 4 7 key name c₁ c₂ i = v) ↔
        (∀ q : Fin 8, (mix 2 (rot 3 dk + dn)) (i-1+q.val) = 0) ∧
        (mix 2 (rot 4 dk)) (i+1) = 0 ∧ (mix 2 (rot 4 dk)) (i+2) = 0 ∧ v = (mix 2 (rot 3 dk + dn)) (i-2) + (mix 2 (rot 4 dk)) i + rot 7 dk i
    exact (reduceRun hk 2 3 4 7 c₁ c₂ dn dk i v).trans (col_class hsize _ _ i _ v)
