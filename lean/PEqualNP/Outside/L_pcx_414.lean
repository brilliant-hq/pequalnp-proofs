import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_414

def Brs (u0 u1 v0 v1 v2 : ZMod 2) : ZMod 2 := v2 + v0 * v1 + u0 * v1 + u1 * v0

theorem L1 (s0 s1 s2 v0 v1 v2 p q : ZMod 2) :
    (s2 + v2) + ((s0 + v0) + p) * ((s1 + v1) + q) =
      (s2 + (s0 + p) * (s1 + q)) + Brs (s0 + p) (s1 + q) v0 v1 v2 := by
  unfold Brs; ring

theorem L2 : ∀ x e : ZMod 2, x = e ∨ x + 1 = e := by decide

theorem L3 : ∀ (u0 u1 a0 a1 a2 b0 b1 b2 c0 c1 c2 : ZMod 2),
    u0 * c1 + u1 * c0 = (a2 + a0 * a1) + (b2 + b0 * b1) + ((a2 + b2 + c2) + (a0 + b0 + c0) * (a1 + b1 + c1)) + 1 →
    Brs u0 u1 a0 a1 a2 = 1 ∨ Brs u0 u1 b0 b1 b2 = 1 ∨
      Brs u0 u1 (a0 + b0 + c0) (a1 + b1 + c1) (a2 + b2 + c2) = 1 := by
  unfold Brs; decide +kernel

theorem L4 : ∀ c0 c1 t : ZMod 2, ¬ (c0 = 0 ∧ c1 = 0) → ∃ p q : ZMod 2, p * c1 + q * c0 = t := by decide

theorem L5 : ∀ v0 v1 v2 : ZMod 2, ¬ (v0 = 0 ∧ v1 = 0 ∧ v2 = 0) → ∃ p q : ZMod 2, Brs p q v0 v1 v2 = 1 := by
  unfold Brs; decide

theorem L6a (u0 u1 x0 x1 x2 y0 y1 y2 : ZMod 2) :
    Brs u0 u1 (x0 + y0) (x1 + y1) (x2 + y2) = Brs u0 u1 x0 x1 x2 + Brs u0 u1 y0 y1 y2 + (x0 * y1 + x1 * y0) := by
  unfold Brs; ring

theorem L6b : ∀ (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 f0 f1 : ZMod 2),
    a0 * d1 + a1 * d0 = 0 → a0 * e1 + a1 * e0 = 0 → a0 * (d1 + e1 + f1) + a1 * (d0 + e0 + f0) = 0 →
    b0 * d1 + b1 * d0 = 0 → b0 * e1 + b1 * e0 = 0 → b0 * (d1 + e1 + f1) + b1 * (d0 + e0 + f0) = 0 →
    (a0 + b0 + c0) * d1 + (a1 + b1 + c1) * d0 = 0 → (a0 + b0 + c0) * e1 + (a1 + b1 + c1) * e0 = 0 →
    (a0 + b0 + c0) * (d1 + e1 + f1) + (a1 + b1 + c1) * (d0 + e0 + f0) = 0 →
    c0 * f1 + c1 * f0 = 0 := by decide +kernel

theorem L7 : ∀ x : ZMod 2, x ≠ 1 → x = 0 := by decide

theorem L8 : ∀ x y z : ZMod 2, x = 0 → y = 0 → x + y + z = 0 → z = 0 := by decide

def dl (m : Fin 4) : Fin 3 → ZMod 2 := ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![1, 1, 1]] m

theorem dl_ok : ∀ (t : ZMod 2) (m : Fin 4), t + dl m 2 + (0 + dl m 0) * (0 + dl m 1) = t := by decide

theorem dl_zero : dl 0 = 0 := by decide

def E (r : ℕ) : (Fin r → ZMod 2) →ₗ[ZMod 2] (Fin r → Fin 3 → ZMod 2) where
  toFun b := fun j c => if c = 2 then b j else 0
  map_add' := by
    intro x y; ext j c
    by_cases h : c = 2 <;> simp [h]
  map_smul' := by
    intro a x; ext j c
    by_cases h : c = 2 <;> simp [h]

theorem E_apply (r : ℕ) (b : Fin r → ZMod 2) (j : Fin r) (c : Fin 3) :
    E r b j c = if c = 2 then b j else 0 := rfl

theorem LV {r : ℕ} (φ : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (h : ∀ k, φ (Pi.single k 1) = 0)
    (b : Fin r → ZMod 2) : φ b = 0 := by
  have h0 : φ = 0 := by
    apply LinearMap.pi_ext
    intro k x
    have hx : (Pi.single k x : Fin r → ZMod 2) = x • Pi.single k 1 := by
      ext j
      simp [Pi.single_apply]
    rw [hx, map_smul, h k]
    simp
  rw [h0]; rfl

theorem single3 {r : ℕ} (i : Fin r) :
    (Pi.single i (dl 3) : Fin r → Fin 3 → ZMod 2) =
      Pi.single i (dl 1) + Pi.single i (dl 2) + E r (Pi.single i 1) := by
  ext j c
  by_cases h : j = i
  · subst h
    fin_cases c <;> simp [E_apply, dl]
  · fin_cases c <;> simp [E_apply, dl, Pi.single_apply, h]

theorem tgt0 {r : ℕ} (b : Fin r → ZMod 2) :
    (fun k : Fin r => E r b k 2 + E r b k 0 * E r b k 1) = b := by
  funext k
  simp [E_apply]

theorem tgt1 {r : ℕ} (b : Fin r → ZMod 2) (i : Fin r) (m : Fin 4) (D : Fin r → Fin 3 → ZMod 2)
    (hD : D = Pi.single i (dl m)) :
    (fun k : Fin r => (E r b + D) k 2 + (E r b + D) k 0 * (E r b + D) k 1) = b := by
  subst hD
  funext k
  by_cases h : k = i
  · subst h
    have h1 := dl_ok (b k) m
    simpa [E_apply] using h1
  · simp [Pi.single_apply, h, E_apply]

theorem tgt2 {r : ℕ} (b : Fin r → ZMod 2) (i j : Fin r) (hij : i ≠ j) (m m' : Fin 4) (D : Fin r → Fin 3 → ZMod 2)
    (hD : D = Pi.single i (dl m) + Pi.single j (dl m')) :
    (fun k : Fin r => (E r b + D) k 2 + (E r b + D) k 0 * (E r b + D) k 1) = b := by
  subst hD
  funext k
  by_cases h : k = i
  · subst h
    have h1 := dl_ok (b k) m
    simpa [E_apply, Pi.single_apply, hij] using h1
  · by_cases h' : k = j
    · subst h'
      have h1 := dl_ok (b k) m'
      simpa [E_apply, Pi.single_apply, h] using h1
    · simp [Pi.single_apply, h, h', E_apply]

theorem fin1 {r : ℕ} (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (p q : ZMod 2) (b : Fin r → ZMod 2) (e : ZMod 2) (D : Fin r → Fin 3 → ZMod 2)
    (hD : (fun k : Fin r => (E r b + D) k 2 + (E r b + D) k 0 * (E r b + D) k 1) = b)
    (hB : Brs ((g (E r b)) 0 + p) ((g (E r b)) 1 + q) ((g D) 0) ((g D) 1) ((g D) 2) = 1) :
    ∃ w : Fin r → Fin 3 → ZMod 2,
      (fun i : Fin r => w i 2 + w i 0 * w i 1) = b ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  rcases L2 ((g (E r b)) 2 + ((g (E r b)) 0 + p) * ((g (E r b)) 1 + q)) e with h | h
  · exact ⟨E r b, tgt0 b, h⟩
  · refine ⟨E r b + D, hD, ?_⟩
    have h2 := L1 ((g (E r b)) 0) ((g (E r b)) 1) ((g (E r b)) 2) ((g D) 0) ((g D) 1) ((g D) 2) p q
    rw [hB] at h2
    rw [map_add]
    show (g (E r b) 2 + g D 2) + ((g (E r b) 0 + g D 0) + p) * ((g (E r b) 1 + g D 1) + q) = e
    rw [h2]
    exact h

theorem g3 {r : ℕ} (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (i : Fin r) (c : Fin 3) :
    (g (Pi.single i (dl 3))) c = (g (Pi.single i (dl 1))) c + (g (Pi.single i (dl 2))) c + (g (E r (Pi.single i 1))) c := by
  rw [single3, map_add, map_add]
  rfl

theorem caseB {r : ℕ} (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (i j : Fin r)
    (hij : (g (E r (Pi.single i 1))) 0 * (g (E r (Pi.single j 1))) 1 +
      (g (E r (Pi.single i 1))) 1 * (g (E r (Pi.single j 1))) 0 = 1)
    (p q : ZMod 2) (b : Fin r → ZMod 2) (e : ZMod 2) :
    ∃ w : Fin r → Fin 3 → ZMod 2,
      (fun i : Fin r => w i 2 + w i 0 * w i 1) = b ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  have hne : i ≠ j := by
    rintro rfl
    have : ∀ x y : ZMod 2, x * y + y * x = 1 → False := by decide
    exact this _ _ hij
  by_contra hno
  have hi : ∀ m : Fin 4, Brs ((g (E r b)) 0 + p) ((g (E r b)) 1 + q)
      ((g (Pi.single i (dl m))) 0) ((g (Pi.single i (dl m))) 1) ((g (Pi.single i (dl m))) 2) = 0 := by
    intro m
    apply L7
    intro h1
    exact hno (fin1 g p q b e (Pi.single i (dl m)) (tgt1 b i m _ rfl) h1)
  have hj : ∀ m' : Fin 4, Brs ((g (E r b)) 0 + p) ((g (E r b)) 1 + q)
      ((g (Pi.single j (dl m'))) 0) ((g (Pi.single j (dl m'))) 1) ((g (Pi.single j (dl m'))) 2) = 0 := by
    intro m'
    apply L7
    intro h1
    exact hno (fin1 g p q b e (Pi.single j (dl m')) (tgt1 b j m' _ rfl) h1)
  have hom : ∀ m m' : Fin 4, (g (Pi.single i (dl m))) 0 * (g (Pi.single j (dl m'))) 1 +
      (g (Pi.single i (dl m))) 1 * (g (Pi.single j (dl m'))) 0 = 0 := by
    intro m m'
    have h0 : Brs ((g (E r b)) 0 + p) ((g (E r b)) 1 + q)
        ((g (Pi.single i (dl m))) 0 + (g (Pi.single j (dl m'))) 0)
        ((g (Pi.single i (dl m))) 1 + (g (Pi.single j (dl m'))) 1)
        ((g (Pi.single i (dl m))) 2 + (g (Pi.single j (dl m'))) 2) = 0 := by
      apply L7
      intro h1
      refine hno (fin1 g p q b e (Pi.single i (dl m) + Pi.single j (dl m')) (tgt2 b i j hne m m' _ rfl) ?_)
      rw [map_add]
      exact h1
    rw [L6a, hi m, hj m'] at h0
    have h8 : ∀ z : ZMod 2, 0 + 0 + z = 0 → z = 0 := by decide
    exact h8 _ h0
  have h11 := hom 1 1
  have h12 := hom 1 2
  have h13 := hom 1 3
  have h21 := hom 2 1
  have h22 := hom 2 2
  have h23 := hom 2 3
  have h31 := hom 3 1
  have h32 := hom 3 2
  have h33 := hom 3 3
  rw [g3 g j 0, g3 g j 1] at h13 h23 h33
  rw [g3 g i 0, g3 g i 1] at h31 h32 h33
  have hz := L6b _ _ _ _ _ _ _ _ _ _ _ _ h11 h12 h13 h21 h22 h23 h31 h32 h33
  rw [hz] at hij
  exact zero_ne_one hij

theorem caseA {r : ℕ} (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (i : Fin r)
    (hω : ∀ k : Fin r, (g (E r (Pi.single k 1))) 0 * (g (E r (Pi.single i 1))) 1 +
        (g (E r (Pi.single k 1))) 1 * (g (E r (Pi.single i 1))) 0 = 0)
    (p q : ZMod 2)
    (hpq : p * (g (E r (Pi.single i 1))) 1 + q * (g (E r (Pi.single i 1))) 0 =
      ((g (Pi.single i (dl 1))) 2 + (g (Pi.single i (dl 1))) 0 * (g (Pi.single i (dl 1))) 1) +
        ((g (Pi.single i (dl 2))) 2 + (g (Pi.single i (dl 2))) 0 * (g (Pi.single i (dl 2))) 1) +
        (((g (Pi.single i (dl 1))) 2 + (g (Pi.single i (dl 2))) 2 + (g (E r (Pi.single i 1))) 2) +
          ((g (Pi.single i (dl 1))) 0 + (g (Pi.single i (dl 2))) 0 + (g (E r (Pi.single i 1))) 0) *
          ((g (Pi.single i (dl 1))) 1 + (g (Pi.single i (dl 2))) 1 + (g (E r (Pi.single i 1))) 1)) + 1)
    (b : Fin r → ZMod 2) (e : ZMod 2) :
    ∃ w : Fin r → Fin 3 → ZMod 2,
      (fun i : Fin r => w i 2 + w i 0 * w i 1) = b ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  have hs : (g (E r b)) 0 * (g (E r (Pi.single i 1))) 1 + (g (E r b)) 1 * (g (E r (Pi.single i 1))) 0 = 0 := by
    have h1 := LV (((g (E r (Pi.single i 1))) 1) • ((LinearMap.proj 0).comp (g.comp (E r))) +
      ((g (E r (Pi.single i 1))) 0) • ((LinearMap.proj 1).comp (g.comp (E r)))) (fun k => by
        have h2 := hω k
        simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]
        linear_combination h2) b
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul] at h1
    linear_combination h1
  have hL := L3 ((g (E r b)) 0 + p) ((g (E r b)) 1 + q)
    ((g (Pi.single i (dl 1))) 0) ((g (Pi.single i (dl 1))) 1) ((g (Pi.single i (dl 1))) 2)
    ((g (Pi.single i (dl 2))) 0) ((g (Pi.single i (dl 2))) 1) ((g (Pi.single i (dl 2))) 2)
    ((g (E r (Pi.single i 1))) 0) ((g (E r (Pi.single i 1))) 1) ((g (E r (Pi.single i 1))) 2)
    (by linear_combination hs + hpq)
  rcases hL with h | h | h
  · exact fin1 g p q b e _ (tgt1 b i 1 _ rfl) h
  · exact fin1 g p q b e _ (tgt1 b i 2 _ rfl) h
  · refine fin1 g p q b e _ (tgt1 b i 3 _ rfl) ?_
    rw [g3 g i 0, g3 g i 1, g3 g i 2]
    exact h

theorem caseI {r : ℕ} (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (i : Fin r) (m : Fin 4)
    (hc : ∀ k : Fin r, (g (E r (Pi.single k 1))) 0 = 0 ∧ (g (E r (Pi.single k 1))) 1 = 0)
    (p q : ZMod 2)
    (hpq : Brs p q ((g (Pi.single i (dl m))) 0) ((g (Pi.single i (dl m))) 1) ((g (Pi.single i (dl m))) 2) = 1)
    (b : Fin r → ZMod 2) (e : ZMod 2) :
    ∃ w : Fin r → Fin 3 → ZMod 2,
      (fun i : Fin r => w i 2 + w i 0 * w i 1) = b ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  have hs0 : (g (E r b)) 0 = 0 :=
    LV ((LinearMap.proj 0).comp (g.comp (E r))) (fun k => (hc k).1) b
  have hs1 : (g (E r b)) 1 = 0 :=
    LV ((LinearMap.proj 1).comp (g.comp (E r))) (fun k => (hc k).2) b
  refine fin1 g p q b e _ (tgt1 b i m _ rfl) ?_
  rw [hs0, hs1, zero_add, zero_add]
  exact hpq

theorem moves_ne {r : ℕ} (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (hg : g ≠ 0) :
    ∃ (i : Fin r) (m : Fin 4), ¬ ((g (Pi.single i (dl m))) 0 = 0 ∧ (g (Pi.single i (dl m))) 1 = 0 ∧
      (g (Pi.single i (dl m))) 2 = 0) := by
  by_contra hno
  push_neg at hno
  apply hg
  apply LinearMap.pi_ext
  intro i x
  have hv : ∀ m : Fin 4, g (Pi.single i (dl m)) = 0 := by
    intro m
    ext c
    have h1 := hno i m
    fin_cases c
    · exact h1.1
    · exact h1.2.1
    · exact h1.2.2
  have h5 : ∀ (a b c : ZMod 2), (![a, b, c] : Fin 3 → ZMod 2) =
      a • dl 1 + b • dl 2 + c • (dl 3 + dl 1 + dl 2) := by decide
  have h6 : x = ![x 0, x 1, x 2] := by
    ext k
    fin_cases k <;> rfl
  have hx : x = x 0 • dl 1 + x 1 • dl 2 + x 2 • (dl 3 + dl 1 + dl 2) := h6.trans (h5 _ _ _)
  have hG : ∀ m : Fin 4, (g.comp (LinearMap.single (ZMod 2) (fun _ : Fin r => Fin 3 → ZMod 2) i)) (dl m) = 0 :=
    fun m => hv m
  show (g.comp (LinearMap.single (ZMod 2) (fun _ : Fin r => Fin 3 → ZMod 2) i)) x = 0
  rw [hx]
  simp only [map_add, map_smul, hG, smul_zero, add_zero]

theorem main (r : ℕ) (g : (Fin r → Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)) (hg : g ≠ 0) :
    ∃ p q : ZMod 2, ∀ (b : Fin r → ZMod 2) (e : ZMod 2), ∃ w : Fin r → Fin 3 → ZMod 2,
      (fun i : Fin r => w i 2 + w i 0 * w i 1) = b ∧ (g w) 2 + ((g w) 0 + p) * ((g w) 1 + q) = e := by
  by_cases hb : ∃ i j : Fin r, (g (E r (Pi.single i 1))) 0 * (g (E r (Pi.single j 1))) 1 +
      (g (E r (Pi.single i 1))) 1 * (g (E r (Pi.single j 1))) 0 = 1
  · obtain ⟨i, j, hij⟩ := hb
    exact ⟨0, 0, fun b e => caseB g i j hij 0 0 b e⟩
  · push_neg at hb
    by_cases hc : ∃ i : Fin r, ¬ ((g (E r (Pi.single i 1))) 0 = 0 ∧ (g (E r (Pi.single i 1))) 1 = 0)
    · obtain ⟨i, hi⟩ := hc
      obtain ⟨p, q, hpq⟩ := L4 _ _ (((g (Pi.single i (dl 1))) 2 + (g (Pi.single i (dl 1))) 0 * (g (Pi.single i (dl 1))) 1) +
        ((g (Pi.single i (dl 2))) 2 + (g (Pi.single i (dl 2))) 0 * (g (Pi.single i (dl 2))) 1) +
        (((g (Pi.single i (dl 1))) 2 + (g (Pi.single i (dl 2))) 2 + (g (E r (Pi.single i 1))) 2) +
          ((g (Pi.single i (dl 1))) 0 + (g (Pi.single i (dl 2))) 0 + (g (E r (Pi.single i 1))) 0) *
          ((g (Pi.single i (dl 1))) 1 + (g (Pi.single i (dl 2))) 1 + (g (E r (Pi.single i 1))) 1)) + 1) hi
      exact ⟨p, q, fun b e => caseA g i (fun k => L7 _ (hb k i)) p q hpq b e⟩
    · push_neg at hc
      obtain ⟨i, m, hm⟩ := moves_ne g hg
      obtain ⟨p, q, hpq⟩ := L5 _ _ _ hm
      exact ⟨p, q, fun b e => caseI g i m hc p q hpq b e⟩

end PEqualNP.Outside.L_pcx_414

theorem PEqualNP.Outside.L_pcx_414 : (∀ r : ℕ,
  let F := ZMod 2
  let X := Fin r → Fin 3 → F
  let target := fun (w : X) (i : Fin r) => w i 2 + w i 0 * w i 1
  ∀ (g : X →ₗ[F] (Fin 3 → F)) (_ : g ≠ 0),
    ∃ p q : F, ∀ (b : Fin r → F) (e : F), ∃ w : X,
      target w = b ∧ (g w) 2 + ((g w) 0+p)*((g w) 1+q) = e) := by
  intro r F X target g hg
  exact PEqualNP.Outside.L_pcx_414.main r g hg
