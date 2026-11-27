import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25580_aux

def mixF (x : ℤ → Bool) (z : ℤ) : Bool := xor (xor (x (z-1)) (x z)) (x (z+1))

def updF (x inj : ℤ → Bool) (z : ℤ) : Bool :=
  xor (xor (mixF x z) (!(mixF x (z+1)) && mixF x (z+2))) (inj z)

def fitsF (mode : ℕ) (u v left right : Bool) : Prop :=
  if mode = 1 then ¬ (left = !u ∧ right = !v)
  else if mode = 2 then right = v
  else if mode = 3 then xor left right = !(xor u v)
  else True

def fitsB (mode : ℕ) (u v left right : Bool) : Bool :=
  if mode = 1 then !(left == !u && right == !v)
  else if mode = 2 then right == v
  else if mode = 3 then xor left right == !(xor u v)
  else true

def alignedB (m : ℕ) (near far : Bool) : Bool :=
  ((m == 1) && near && far) || ((m == 2) && far) || ((m == 3) && near)

def diagB (m : ℕ) (near far hit : Bool) : Bool :=
  (m == 3) || (!hit && (((m == 1) && !near && !far) || (m == 2)))

def nextB (aligned diagonal hit : Bool) : ℕ :=
  if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1

def mixB (p q r : Bool) : Bool := xor (xor p q) r

def updB (w0 w1 w2 w3 w4 i : Bool) : Bool :=
  xor (xor (mixB w0 w1 w2) (!(mixB w1 w2 w3) && mixB w2 w3 w4)) i

theorem fits_iff (mode : ℕ) (u v l r : Bool) : fitsF mode u v l r ↔ fitsB mode u v l r = true := by
  unfold fitsF fitsB
  split_ifs <;> cases u <;> cases v <;> cases l <;> cases r <;> decide

theorem mix_eq (x : ℤ → Bool) (z z0 z1 : ℤ) (h0 : z - 1 = z0) (h1 : z + 1 = z1) :
    mixF x z = mixB (x z0) (x z) (x z1) := by
  subst h0 h1
  rfl

theorem upd_eq (x inj : ℤ → Bool) (z z0 z1 z2 z3 : ℤ) (h0 : z - 1 = z0) (h1 : z + 1 = z1)
    (h2 : z + 2 = z2) (h3 : z + 3 = z3) :
    updF x inj z = updB (x z0) (x z) (x z1) (x z2) (x z3) (inj z) := by
  subst h0 h1 h2 h3
  unfold updF mixF updB mixB
  rw [show z + 1 - 1 = z by ring, show z + 1 + 1 = z + 2 by ring, show z + 2 - 1 = z + 1 by ring,
    show z + 2 + 1 = z + 3 by ring]

theorem mix_congr (x y : ℤ → Bool) (z : ℤ) (h : ∀ k, k ≤ z + 1 → y k = x k) :
    mixF y z = mixF x z := by
  unfold mixF
  rw [h (z-1) (by omega), h z (by omega), h (z+1) (by omega)]

theorem upd_congr (x y inj : ℤ → Bool) (z : ℤ) (h : ∀ k, k ≤ z + 3 → y k = x k) :
    updF y inj z = updF x inj z := by
  rw [upd_eq y inj z (z-1) (z+1) (z+2) (z+3) rfl rfl rfl rfl,
    upd_eq x inj z (z-1) (z+1) (z+2) (z+3) rfl rfl rfl rfl,
    h (z-1) (by omega), h z (by omega), h (z+1) (by omega), h (z+2) (by omega), h (z+3) (by omega)]

theorem upd_hit (x y inj : ℤ → Bool) (b : ℤ) (hy : ∀ z ≤ b, y z = x z) (ht : mixF x (b-1) = true) :
    updF y inj (b-2) = updF x inj (b-2) := by
  rw [mix_eq x (b-1) (b-2) b (by omega) (by omega)] at ht
  rw [upd_eq y inj (b-2) (b-3) (b-1) b (b+1) (by omega) (by omega) (by omega) (by omega),
    upd_eq x inj (b-2) (b-3) (b-1) b (b+1) (by omega) (by omega) (by omega) (by omega),
    hy (b-3) (by omega), hy (b-2) (by omega), hy (b-1) (by omega), hy b (by omega)]
  unfold updB
  rw [ht]
  simp

theorem mk (x : ℤ → Bool) (b : ℤ) (P Q R S : Bool) :
    ∃ y : ℤ → Bool, (∀ z ≤ b, y z = x z) ∧ y (b+1) = P ∧ y (b+2) = Q ∧ y (b+3) = R ∧
      y (b+4) = S := by
  have n1 : ¬ (b + 1 ≤ b) := by omega
  have n2 : ¬ (b + 2 ≤ b) := by omega
  have n3 : ¬ (b + 3 ≤ b) := by omega
  have n4 : ¬ (b + 4 ≤ b) := by omega
  have m21 : ¬ (b + 2 = b + 1) := by omega
  have m31 : ¬ (b + 3 = b + 1) := by omega
  have m32 : ¬ (b + 3 = b + 2) := by omega
  have m41 : ¬ (b + 4 = b + 1) := by omega
  have m42 : ¬ (b + 4 = b + 2) := by omega
  have m43 : ¬ (b + 4 = b + 3) := by omega
  refine ⟨fun z => if z ≤ b then x z else if z = b+1 then P else if z = b+2 then Q
    else if z = b+3 then R else S, ?_, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simp [hz]
  · simp [n1]
  · simp [n2, m21]
  · simp [n3, m31, m32]
  · simp [n4, m41, m42, m43]

theorem K0 : ∀ (m : Fin 4) (u v A C D E I2 I1 left right : Bool), false = mixB C D E →
    (fitsB (nextB (alignedB m.val (E == !(xor u v)) (D == v))
        (diagB m.val (E == !(xor u v)) (D == v) false) false)
        (xor (mixB A C D) I2) I1 left right = true ↔
      ∃ P Q : Bool, fitsB m.val u v P Q = true ∧ updB A C D E P I2 = left ∧
        updB C D E P Q I1 = right) := by
  decide +kernel

theorem K1 : ∀ (m : Fin 4) (u v C D E I1 I0 left right : Bool), true = mixB C D E →
    false = alignedB m.val (E == !(xor u v)) (D == v) →
    (fitsB (nextB false (diagB m.val (E == !(xor u v)) (D == v) true) true)
        (xor (mixB C D E) I1) I0 left right = true ↔
      ∃ P Q R : Bool, fitsB m.val u v P Q = true ∧ updB C D E P Q I1 = left ∧
        updB D E P Q R I0 = right) := by
  decide +kernel

theorem K2a : ∀ (m : Fin 4) (u v C D E p q P Q I1 : Bool),
    true = alignedB m.val (E == !(xor u v)) (D == v) → fitsB m.val u v p q = true →
    fitsB m.val u v P Q = true → updB C D E P Q I1 = updB C D E p q I1 := by
  decide +kernel

theorem K2b : ∀ (m : Fin 4) (u v D E I0 J1 left right : Bool),
    true = alignedB m.val (E == !(xor u v)) (D == v) →
    ∃ P Q R S : Bool, fitsB m.val u v P Q = true ∧ updB D E P Q R I0 = left ∧
      updB E P Q R S J1 = right := by
  decide +kernel

theorem core (x inj : ℤ → Bool) (b : ℤ) (mode : Fin 4) (u v : Bool)
    (h : fitsF mode.val u v (x (b+1)) (x (b+2)))
    (near far hit aligned diagonal : Bool) (nextMode : ℕ) (f : ℤ)
    (hnear : near = (x b == !(xor u v))) (hfar : far = (x (b-1) == v))
    (hhit : hit = mixF x (b-1))
    (hal : aligned = alignedB mode.val near far)
    (hdi : diagonal = diagB mode.val near far hit)
    (hnm : nextMode = nextB aligned diagonal hit)
    (hf : f = b-3+(hit.toNat : ℤ)+((aligned && hit).toNat : ℤ)) :
    (∀ y : ℤ → Bool, ((∀ z ≤ b, y z = x z) ∧ fitsF mode.val u v (y (b+1)) (y (b+2))) →
      (∀ z ≤ f, updF y inj z = updF x inj z) ∧
      (nextMode ≠ 0 → xor (mixF y (f+1)) (inj (f+1)) = xor (mixF x (f+1)) (inj (f+1)))) ∧
    (∀ left right : Bool,
      fitsF nextMode (xor (mixF x (f+1)) (inj (f+1))) (inj (f+2)) left right ↔
      ∃ y : ℤ → Bool, ((∀ z ≤ b, y z = x z) ∧ fitsF mode.val u v (y (b+1)) (y (b+2))) ∧
        updF y inj (f+1) = left ∧ updF y inj (f+2) = right) := by
  have hhit0 := hhit
  rw [mix_eq x (b-1) (b-2) b (by omega) (by omega)] at hhit
  rw [fits_iff] at h
  subst hnear hfar
  cases hit
  · have hf' : f = b - 3 := by
      subst hf
      simp only [Bool.toNat_false, Bool.and_false, Nat.cast_zero]
      omega
    subst hf'
    subst hnm hdi hal
    refine ⟨fun y hy => ⟨fun z hz => upd_congr x y inj z (fun k hk => hy.1 k (by omega)),
      fun _ => ?_⟩, ?_⟩
    · rw [mix_congr x y (b - 3 + 1) (fun k hk => hy.1 k (by omega))]
    · intro left right
      have e1 : b - 3 + 1 = b - 2 := by omega
      have e2 : b - 3 + 2 = b - 1 := by omega
      rw [e1, e2, mix_eq x (b-2) (b-3) (b-1) (by omega) (by omega), fits_iff]
      constructor
      · intro hfit
        obtain ⟨P, Q, hPQ, hl, hr⟩ := (K0 mode u v (x (b-3)) (x (b-2)) (x (b-1)) (x b)
          (inj (b-2)) (inj (b-1)) left right hhit).1 hfit
        obtain ⟨y, hy, h1, h2, -, -⟩ := mk x b P Q false false
        refine ⟨y, ⟨hy, ?_⟩, ?_, ?_⟩
        · rw [h1, h2, fits_iff]
          exact hPQ
        · rw [upd_eq y inj (b-2) (b-3) (b-1) b (b+1) (by omega) (by omega) (by omega) (by omega),
            hy (b-3) (by omega), hy (b-2) (by omega), hy (b-1) (by omega), hy b (by omega), h1]
          exact hl
        · rw [upd_eq y inj (b-1) (b-2) b (b+1) (b+2) (by omega) (by omega) (by omega) (by omega),
            hy (b-2) (by omega), hy (b-1) (by omega), hy b (by omega), h1, h2]
          exact hr
      · rintro ⟨y, ⟨hy, hfy⟩, hl, hr⟩
        rw [fits_iff] at hfy
        rw [upd_eq y inj (b-2) (b-3) (b-1) b (b+1) (by omega) (by omega) (by omega) (by omega),
          hy (b-3) (by omega), hy (b-2) (by omega), hy (b-1) (by omega), hy b (by omega)] at hl
        rw [upd_eq y inj (b-1) (b-2) b (b+1) (b+2) (by omega) (by omega) (by omega) (by omega),
          hy (b-2) (by omega), hy (b-1) (by omega), hy b (by omega)] at hr
        exact (K0 mode u v (x (b-3)) (x (b-2)) (x (b-1)) (x b) (inj (b-2)) (inj (b-1))
          left right hhit).2 ⟨y (b+1), y (b+2), hfy, hl, hr⟩
  · cases aligned
    · have hf' : f = b - 2 := by
        subst hf
        simp only [Bool.toNat_true, Bool.toNat_false, Bool.false_and, Nat.cast_zero, Nat.cast_one]
        omega
      subst hf'
      subst hnm hdi
      refine ⟨fun y hy => ⟨fun z hz => ?_, fun _ => ?_⟩, ?_⟩
      · by_cases hz' : z ≤ b - 3
        · exact upd_congr x y inj z (fun k hk => hy.1 k (by omega))
        · have hzz : z = b - 2 := by omega
          subst hzz
          exact upd_hit x y inj b hy.1 hhit0.symm
      · rw [mix_congr x y (b - 2 + 1) (fun k hk => hy.1 k (by omega))]
      · intro left right
        have e1 : b - 2 + 1 = b - 1 := by omega
        have e2 : b - 2 + 2 = b := by omega
        rw [e1, e2, mix_eq x (b-1) (b-2) b (by omega) (by omega), fits_iff]
        constructor
        · intro hfit
          obtain ⟨P, Q, R, hPQ, hl, hr⟩ := (K1 mode u v (x (b-2)) (x (b-1)) (x b)
            (inj (b-1)) (inj b) left right hhit hal).1 hfit
          obtain ⟨y, hy, h1, h2, h3, -⟩ := mk x b P Q R false
          refine ⟨y, ⟨hy, ?_⟩, ?_, ?_⟩
          · rw [h1, h2, fits_iff]
            exact hPQ
          · rw [upd_eq y inj (b-1) (b-2) b (b+1) (b+2) (by omega) (by omega) (by omega)
              (by omega), hy (b-2) (by omega), hy (b-1) (by omega), hy b (by omega), h1, h2]
            exact hl
          · rw [upd_eq y inj b (b-1) (b+1) (b+2) (b+3) (by omega) (by omega) (by omega)
              (by omega), hy (b-1) (by omega), hy b (by omega), h1, h2, h3]
            exact hr
        · rintro ⟨y, ⟨hy, hfy⟩, hl, hr⟩
          rw [fits_iff] at hfy
          rw [upd_eq y inj (b-1) (b-2) b (b+1) (b+2) (by omega) (by omega) (by omega) (by omega),
            hy (b-2) (by omega), hy (b-1) (by omega), hy b (by omega)] at hl
          rw [upd_eq y inj b (b-1) (b+1) (b+2) (b+3) (by omega) (by omega) (by omega) (by omega),
            hy (b-1) (by omega), hy b (by omega)] at hr
          exact (K1 mode u v (x (b-2)) (x (b-1)) (x b) (inj (b-1)) (inj b) left right hhit
            hal).2 ⟨y (b+1), y (b+2), y (b+3), hfy, hl, hr⟩
    · have hf' : f = b - 1 := by
        subst hf
        simp only [Bool.toNat_true, Bool.true_and, Nat.cast_one]
        omega
      subst hf'
      subst hnm
      refine ⟨fun y hy => ⟨fun z hz => ?_, fun hne => ?_⟩, ?_⟩
      · by_cases hz' : z ≤ b - 3
        · exact upd_congr x y inj z (fun k hk => hy.1 k (by omega))
        · by_cases hz2 : z = b - 2
          · subst hz2
            exact upd_hit x y inj b hy.1 hhit0.symm
          · have hzz : z = b - 1 := by omega
            subst hzz
            have hfy := (fits_iff _ _ _ _ _).1 hy.2
            rw [upd_eq y inj (b-1) (b-2) b (b+1) (b+2) (by omega) (by omega) (by omega)
              (by omega),
              upd_eq x inj (b-1) (b-2) b (b+1) (b+2) (by omega) (by omega) (by omega) (by omega),
              hy.1 (b-2) (by omega), hy.1 (b-1) (by omega), hy.1 b (by omega)]
            exact K2a mode u v (x (b-2)) (x (b-1)) (x b) (x (b+1)) (x (b+2)) (y (b+1))
              (y (b+2)) (inj (b-1)) hal h hfy
      · exact absurd (by simp [nextB]) hne
      · intro left right
        have e1 : b - 1 + 1 = b := by omega
        have e2 : b - 1 + 2 = b + 1 := by omega
        rw [e1, e2]
        refine ⟨fun _ => ?_, fun _ => ?_⟩
        · obtain ⟨P, Q, R, S, hPQ, hl, hr⟩ := K2b mode u v (x (b-1)) (x b) (inj b)
            (inj (b+1)) left right hal
          obtain ⟨y, hy, h1, h2, h3, h4⟩ := mk x b P Q R S
          refine ⟨y, ⟨hy, ?_⟩, ?_, ?_⟩
          · rw [h1, h2, fits_iff]
            exact hPQ
          · rw [upd_eq y inj b (b-1) (b+1) (b+2) (b+3) (by omega) (by omega) (by omega)
              (by omega), hy (b-1) (by omega), hy b (by omega), h1, h2, h3]
            exact hl
          · rw [upd_eq y inj (b+1) b (b+2) (b+3) (b+4) (by omega) (by omega) (by omega)
              (by omega), hy b (by omega), h1, h2, h3, h4]
            exact hr
        · rw [fits_iff]
          simp [nextB, fitsB]

end PEqualNP.Outside.L_meta_25580_aux

theorem PEqualNP.Outside.L_meta_25580 : (let mix := fun (x : Int → Bool) (z : Int) => xor (xor (x (z-1)) (x z)) (x (z+1))
let update := fun (x inj : Int → Bool) (z : Int) =>
  xor (xor (mix x z) (!(mix x (z+1)) && mix x (z+2))) (inj z)
let fits := fun (mode : Nat) (u v left right : Bool) =>
  if mode = 1 then ¬ (left = !u ∧ right = !v)
  else if mode = 2 then right = v
  else if mode = 3 then xor left right = !(xor u v)
  else True
∀ (x inj : Int → Bool) (b : Int) (mode : Fin 4) (u v : Bool),
  fits mode.val u v (x (b+1)) (x (b+2)) →
  let near := x b == !(xor u v)
  let far := x (b-1) == v
  let hit := mix x (b-1)
  let aligned := ((mode.val == 1) && near && far) || ((mode.val == 2) && far) ||
    ((mode.val == 3) && near)
  let diagonal := (mode.val == 3) ||
    (!hit && (((mode.val == 1) && !near && !far) || (mode.val == 2)))
  let nextMode : Nat := if aligned then (if hit then 0 else 2) else if diagonal then 3 else 1
  let f := b-3+(hit.toNat : Int)+((aligned && hit).toNat : Int)
  let nextU := xor (mix x (f+1)) (inj (f+1))
  let nextV := inj (f+2)
  let completion := fun (y : Int → Bool) =>
    (∀ z ≤ b, y z = x z) ∧ fits mode.val u v (y (b+1)) (y (b+2))
  (∀ y : Int → Bool, completion y →
    (∀ z ≤ f, update y inj z = update x inj z) ∧
    (nextMode ≠ 0 → xor (mix y (f+1)) (inj (f+1)) = nextU)) ∧
  (∀ left right : Bool, fits nextMode nextU nextV left right ↔
    ∃ y : Int → Bool, completion y ∧
      update y inj (f+1) = left ∧ update y inj (f+2) = right)) := by
  intro mix update fits x inj b mode u v h near far hit aligned diagonal nextMode f nextU nextV completion
  exact PEqualNP.Outside.L_meta_25580_aux.core x inj b mode u v h near far hit aligned diagonal nextMode f
    rfl rfl rfl rfl rfl rfl rfl
