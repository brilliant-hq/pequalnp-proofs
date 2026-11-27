import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_29734

namespace Dervish29734

def Period (c : ℕ) (opt : ℕ → ℕ) (d : ℕ) := ∀ b : ℕ, 0 < b →
  b^2 * opt d ≤ d^2 * opt b ∧ d^2 * opt b ≤ b^2 * opt d + (b%d)^2*d^2*c

theorem Period.of_dvd {c d D : ℕ} {opt : ℕ → ℕ} (h : Period c opt d)
    (hd : 0 < d) (hD : 0 < D) (dvd : d ∣ D) : Period c opt D := by
  obtain ⟨k, rfl⟩ := dvd
  obtain ⟨lo,hi⟩ := h (d*k) hD
  have hpow : (d*k)^2 = d^2*k^2 := mul_pow ..
  rw [hpow, Nat.mul_mod_right, zero_pow (by decide : 2 ≠ 0)] at hi
  simp only [Nat.zero_mul,Nat.add_zero] at hi
  rw [hpow] at lo
  have exact_at : opt (d*k) = k^2*opt d := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pow_pos hd (n := 2))
    simpa [Nat.mul_assoc] using (le_antisymm hi lo)
  intro b hb
  obtain ⟨hl,hu⟩ := h b hb
  rw [hpow,exact_at]
  constructor
  · calc b^2 * (k^2*opt d) = k^2*(b^2*opt d) := by ring
         _ ≤ k^2*(d^2*opt b) := Nat.mul_le_mul_left _ hl
         _ = _ := by ring
  · have mod_le : b%d ≤ b%(d*k) := by
      calc b%d = (b%(d*k))%d := (Nat.mod_mod_of_dvd b (show d∣d*k from dvd_mul_right _ _)).symm
           _ ≤ _ := Nat.mod_le _ _
    have rem := Nat.mul_le_mul_right (d^2*c) (Nat.pow_le_pow_left mod_le 2)
    have hu' : d^2*opt b ≤ b^2*opt d + (b%(d*k))^2*d^2*c := hu.trans (Nat.add_le_add_left (by simpa [Nat.mul_assoc] using rem) _)
    calc d^2*k^2*opt b = k^2*(d^2*opt b) := by ring
         _ ≤ k^2*(b^2*opt d + (b%(d*k))^2*d^2*c) := Nat.mul_le_mul_left _ hu'
         _ = _ := by ring

theorem common {ι : Type*} [Fintype ι] (c : ℕ) (opt : ι → ℕ → ℕ)
    (h : ∀ i, ∃ d, 0 < d ∧ Period c (opt i) d) :
    ∃ D, 0 < D ∧ ∀ i, Period c (opt i) D := by
  classical
  choose d hd hp using h
  refine ⟨∏ i, d i, Finset.prod_pos (fun i _ => hd i), ?_⟩
  intro i
  exact (hp i).of_dvd (hd i) (Finset.prod_pos (fun i _ => hd i))
    (Finset.dvd_prod_of_mem d (Finset.mem_univ i))

end Dervish29734

namespace Dervish29734

def Fits (q s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) : Prop :=
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget

noncomputable def Opt (n : ℕ) (hn : 0 < n) (q : ℕ) (G : Fin n → Fin n → Bool) (b : ℕ) :=
  sInf {e : ℕ | Fits q (n*b) (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) e}

theorem assemble
    (low : ∀ n (hn : 0<n) (q : Fin n) (G : Fin n → Fin n → Bool),
      ∃ d, 0<d ∧ Period (Nat.choose n 2) (Opt n hn q.val G) d)
    (high : ∀ n (hn : 0<n) q (G : Fin n → Fin n → Bool), n≤q →
      ∀ b, 0<b → Opt n hn q G b = 0) :
  ∀ (n : ℕ) (hn : 0 < n), ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ,
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) =>
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget
  ∀ G : Fin n → Fin n → Bool,
    let opt := fun (b : ℕ) => sInf {e : ℕ | fits (n*b)
      (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) e}
    ∀ b : ℕ, 0 < b →
      b^2 * opt D ≤ D^2 * opt b ∧
      D^2 * opt b ≤ b^2 * opt D + (b % D)^2 * D^2 * Nat.choose n 2 := by
  intro n hn
  let ι := Fin n × (Fin n → Fin n → Bool)
  obtain ⟨D, hD, h⟩ := common (ι := ι) (Nat.choose n 2)
    (fun i : ι => Opt n hn i.1.val i.2) (fun i => low n hn i.1 i.2)
  refine ⟨D,hD,?_⟩
  intro q fits G opt b hb
  change b^2 * Opt n hn q G D ≤ D^2 * Opt n hn q G b ∧ _
  by_cases hq : q<n
  · exact h (⟨q,hq⟩,G) b hb
  · change b^2 * Opt n hn q G D ≤ D^2 * Opt n hn q G b ∧ D^2*Opt n hn q G b ≤ b^2*Opt n hn q G D + _
    simp [high n hn q G (by omega) D hD,high n hn q G (by omega) b hb]

end Dervish29734

namespace Dervish29734.LargeQ

def Fits (q : ℕ) (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) : Prop :=
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget

private theorem pair_cases {α : Type*} [DecidableEq α] {a b i j : α}
    (h : ({a,b} : Finset α) = {i,j}) : (a = i ∧ b = j) ∨ (a = j ∧ b = i) := by
  have ha : a ∈ ({i,j} : Finset α) := by rw [← h]; simp
  have hb : b ∈ ({i,j} : Finset α) := by rw [← h]; simp
  have hi : i ∈ ({a,b} : Finset α) := by rw [h]; simp
  have hj : j ∈ ({a,b} : Finset α) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at *
  tauto

theorem fits_zero (n q : ℕ) (hn : 0 < n) (hq : n ≤ 2^q) (G : Fin n → Fin n → Bool)
    (b : ℕ) : Fits q (n*b)
      (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) 0 := by
  classical
  obtain ⟨code⟩ := Function.Embedding.nonempty_of_card_le (α := Fin n) (β := Fin q → Bool)
    (by simpa using hq)
  let res (i : Fin (n*b)) : Fin n := ⟨i.val % n, Nat.mod_lt _ hn⟩
  let R (l : Fin q) := Finset.univ.filter (fun i : Fin (n*b) => code (res i) l = true)
  let out (U : Finset (Fin (n*b))) (c : Fin q → Bool) := decide (∃ i j,
    ({i,j} : Finset _) = U ∧ code (res i) = c ∧ G (res i) (res j) = true)
  have good (i j : Fin (n*b)) : out {i,j} (code (res i)) = G (res i) (res j) := by
    apply Bool.eq_iff_iff.mpr
    simp only [out, decide_eq_true_eq]
    constructor
    · rintro ⟨a,b',hp,hc,hg⟩
      have hr := code.injective hc
      rcases pair_cases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hg
      · simpa [hr] using hg
    · exact fun h => ⟨i,j,rfl,rfl,h⟩
  refine ⟨Equiv.refl _, fun _ => false, fun _ => false, R, fun _ => ∅, out, ?_⟩
  have hobs (i j : Fin (n*b)) : (fun l => decide (i ∈ R l ∨ (Equiv.refl _) j ∈ (∅ : Finset _))) = code (res i) := by
    funext l
    simp [R]
  simp
  intro i j
  simpa using ((congrArg (out {i,j}) (hobs i j)).trans (good i j))

theorem opt_zero (n q : ℕ) (hn : 0 < n) (hq : n ≤ 2^q) (G : Fin n → Fin n → Bool)
    (b : ℕ) : sInf {e : ℕ | Fits q (n*b)
      (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) e} = 0 := by
  exact Nat.eq_zero_of_le_zero (Nat.sInf_le (fits_zero n q hn hq G b))

theorem fits_zero_of_le (n q : ℕ) (hn : 0 < n) (hq : n ≤ q) (G : Fin n → Fin n → Bool)
    (b : ℕ) : Fits q (n*b)
      (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) 0 := by
  suffices h : ∀ k : ℕ, k < 2^k by exact fits_zero n q hn (hq.trans (h q).le) G b
  intro k
  induction k with
  | zero => decide
  | succ k ih => rw [pow_succ]; omega

end Dervish29734.LargeQ

namespace Dervish29734

theorem onlySmall
    (small : ∀ n (hn : 0<n) (q : Fin n) (G : Fin n → Fin n → Bool),
      2^q.val < n → ∃ d, 0<d ∧ Period (Nat.choose n 2) (Opt n hn q.val G) d) :
  ∀ (n : ℕ) (hn : 0 < n), ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ,
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) =>
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget
  ∀ G : Fin n → Fin n → Bool,
    let opt := fun (b : ℕ) => sInf {e : ℕ | fits (n*b)
      (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) e}
    ∀ b : ℕ, 0 < b →
      b^2 * opt D ≤ D^2 * opt b ∧
      D^2 * opt b ≤ b^2 * opt D + (b % D)^2 * D^2 * Nat.choose n 2 := by
  apply assemble
  · intro n hn q G
    by_cases h : 2^q.val < n
    · exact small n hn q G h
    · refine ⟨1, by decide, ?_⟩
      intro b hb
      have hz (a : ℕ) : Opt n hn q.val G a = 0 := LargeQ.opt_zero n q.val hn (by omega) G a
      simp [hz]
  · intro n hn q G hq b _
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le (LargeQ.fits_zero_of_le n q hn hq G b))

end Dervish29734

namespace Dervish29734

abbrev Tag (n q : ℕ) := Fin n × Fin n × Bool × Bool × (Fin q → Bool) × (Fin q → Bool)

variable {n q : ℕ}

def Left (t : Tag n q) := t.1
def Right (t : Tag n q) := t.2.1
def rowFlip (t : Tag n q) := t.2.2.1
def colFlip (t : Tag n q) := t.2.2.2.1
def rowMem (t : Tag n q) := t.2.2.2.2.1
def colMem (t : Tag n q) := t.2.2.2.2.2

def targetOf (G : Fin n → Fin n → Bool) (t u : Tag n q) :=
  Bool.xor (G (Left t) (Right u)) (Bool.xor (rowFlip t) (colFlip u))

def sigOf (t u : Tag n q) : Fin q → Bool := fun j => decide (rowMem t j = true ∨ colMem u j = true)

theorem sigOf_eq (t u : Tag n q) : sigOf t u = fun j => decide (rowMem t j = true ∨ colMem u j = true) := rfl

def K (G : Fin n → Fin n → Bool) (t u : Tag n q) : ℕ :=
  if targetOf G t u = false ∧ targetOf G u t = true ∧ sigOf t u = sigOf u t then 1 else 0

@[simp] theorem K_diag (G : Fin n → Fin n → Bool) (t : Tag n q) : K G t t = 0 := by
  simp [K]

theorem K_swap_le (G : Fin n → Fin n → Bool) (t u : Tag n q) : K G t u + K G u t ≤ 1 := by
  unfold K
  split <;> split <;> simp_all

def Loss (G : Fin n → Fin n → Bool) (f : Tag n q → ℕ) := ∑ t, ∑ u, K G t u * f t * f u

def Margins (b : ℕ) (f : Tag n q → ℕ) :=
  (∀ a, (∑ t ∈ Finset.univ.filter (fun t => Left t = a), f t) = b) ∧
  (∀ a, (∑ t ∈ Finset.univ.filter (fun t => Right t = a), f t) = b)

def freq {I T : Type*} [Fintype I] [DecidableEq T] (label : I → T) (t : T) :=
  (Finset.univ.filter (fun i => label i = t)).card

theorem sum_tag_freq {I T : Type*} [Fintype I] [Fintype T] [DecidableEq T]
    (label : I → T) (c : T → ℕ) : (∑ i, c (label i)) = ∑ t, c t * freq label t := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ label (fun i => c (label i))]
  apply Finset.sum_congr rfl
  intro t _
  calc _ = ∑ i ∈ Finset.univ.filter (fun i => label i = t), c t := by
             apply Finset.sum_congr rfl
             intro i hi
             rw [(Finset.mem_filter.mp hi).2]
       _ = _ := by simp [freq, Nat.mul_comm]

open scoped Classical in
theorem count_eq_loss {I : Type*} [Fintype I]
    (G : Fin n → Fin n → Bool) (label : I → Tag n q) :
    ((Finset.univ : Finset (I × I)).filter (fun z =>
      targetOf G (label z.1) (label z.2) = false ∧ targetOf G (label z.2) (label z.1) = true ∧
      sigOf (label z.1) (label z.2) = sigOf (label z.2) (label z.1))).card = Loss G (freq label) := by
  classical
  calc _ = ∑ z : I × I, K G (label z.1) (label z.2) := by
             unfold K
             exact (Finset.sum_boole (R := ℕ) _ _).symm
       _ = ∑ i : I, ∑ j : I, K G (label i) (label j) := Fintype.sum_prod_type _
       _ = ∑ t, (∑ j : I, K G t (label j)) * freq label t := sum_tag_freq label (fun t => ∑ j : I, K G t (label j))
       _ = _ := by
             apply Finset.sum_congr rfl
             intro t _
             rw [sum_tag_freq label (K G t), Finset.sum_mul]
             apply Finset.sum_congr rfl
             intro u _
             ac_rfl

end Dervish29734

namespace Dervish29734

variable {I S : Type*} [Fintype I] [DecidableEq I]
variable (target : I → I → Bool) (sig : I → I → S)

noncomputable def pairConflicts : Finset (I × I) := by
  classical
  exact Finset.univ.filter (fun z => target z.1 z.2 = false ∧
    target z.2 z.1 = true ∧ sig z.1 z.2 = sig z.2 z.1)

def pairErrors (out : Finset I → S → Bool) : Finset (I × I) :=
  Finset.univ.filter (fun z => out {z.1, z.2} (sig z.1 z.2) ≠ target z.1 z.2)

noncomputable def pairDecoder (u : Finset I) (s : S) : Bool := by
  classical
  exact decide (∃ i j, ({i,j} : Finset I) = u ∧ sig i j = s ∧ target i j = true)

omit [Fintype I] in
private theorem pair_or_swap {a b i j : I} (h : ({a,b} : Finset I) = {i,j}) :
    a = i ∧ b = j ∨ a = j ∧ b = i := by
  have h' (k : I) : k = a ∨ k = b ↔ k = i ∨ k = j := by
    simpa using (show k ∈ ({a,b} : Finset I) ↔ k ∈ ({i,j} : Finset I) by rw [h])
  have ha := (h' a).mp (Or.inl rfl)
  have hb := (h' b).mp (Or.inr rfl)
  have hi := (h' i).mpr (Or.inl rfl)
  have hj := (h' j).mpr (Or.inr rfl)
  grind only

theorem pairErrors_pairDecoder :
    pairErrors target sig (pairDecoder target sig) = pairConflicts target sig := by
  classical
  ext ⟨i,j⟩
  simp only [pairErrors, pairConflicts, Finset.mem_filter, Finset.mem_univ, true_and]
  have ht : pairDecoder target sig {i,j} (sig i j) = true ↔
      target i j = true ∨ (target j i = true ∧ sig i j = sig j i) := by
    simp only [pairDecoder, decide_eq_true_eq]
    constructor
    · rintro ⟨a,b,h,e,t⟩
      rcases pair_or_swap h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl t
      · exact Or.inr ⟨t,e.symm⟩
    · rintro (h | ⟨h,e⟩)
      · exact ⟨i,j,rfl,rfl,h⟩
      · exact ⟨j,i,Finset.pair_comm ..,e.symm,h⟩
  cases e : target i j <;> simp_all

theorem pairErrors_optimal : ∃ out, pairErrors target sig out = pairConflicts target sig :=
  ⟨pairDecoder target sig, pairErrors_pairDecoder target sig⟩

theorem pairConflicts_le_errors (out : Finset I → S → Bool) :
    (pairConflicts target sig).card ≤ (pairErrors target sig out).card := by
  classical
  let pred (z : I × I) := out {z.1,z.2} (sig z.1 z.2)
  let f (z : I × I) := if pred z = true then z else z.swap
  let g (z : I × I) := if target z.1 z.2 = false then z else z.swap
  have mem {z : I × I} (hz : z ∈ pairConflicts target sig) :
      target z.1 z.2 = false ∧ target z.2 z.1 = true ∧ sig z.1 z.2 = sig z.2 z.1 :=
    (Finset.mem_filter.mp hz).2
  have inv (z : I × I) (hz : z ∈ pairConflicts target sig) : g (f z) = z := by
    rcases mem hz with ⟨hf,ht,_⟩
    cases hp : pred z <;> simp [g,f,hp,hf,ht]
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    rcases mem hz with ⟨hf,ht,hs⟩
    have hp' : pred z.swap = pred z := by
      change out {z.2,z.1} (sig z.2 z.1) = out {z.1,z.2} (sig z.1 z.2)
      rw [Finset.pair_comm z.2 z.1, hs]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    change pred (f z) ≠ target (f z).1 (f z).2
    cases hp : pred z <;> simp [f,hp,hp',hf,ht]
  · intro a ha b hb hab
    simpa only [inv a ha, inv b hb] using congrArg g hab

end Dervish29734

namespace Dervish29734

private abbrev tResidue {n b : ℕ} (hn : 0 < n) (i : Fin (n*b)) : Fin n :=
  ⟨i.val % n, Nat.mod_lt _ hn⟩

private theorem card_residue_fiber {n b : ℕ} (hn : 0 < n) (a : Fin n) :
    Fintype.card { i : Fin (n*b) // tResidue hn i = a } = b := by
  let e : Fin (n*b) ≃ Fin b × Fin n :=
    (finCongr (Nat.mul_comm n b)).trans finProdFinEquiv.symm
  let d : { p : Fin b × Fin n // p.2 = a } ≃ Fin b :=
    ⟨fun p => p.1.1, fun i => ⟨(i,a),rfl⟩, by rintro ⟨⟨k,y⟩,rfl⟩; rfl, fun _ => rfl⟩
  let c : { i : Fin (n*b) // tResidue hn i = a } ≃ { p : Fin b × Fin n // p.2 = a } :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  simpa using Fintype.card_congr (c.trans d)

private theorem count_group {I T A : Type*} [Fintype I] [Fintype T] [DecidableEq T]
    [DecidableEq A] (tag : I → T) (L : T → A) (a : A) :
    (∑ t ∈ Finset.univ.filter (fun t => L t = a),
      (Finset.univ.filter (fun i => tag i = t)).card) =
    (Finset.univ.filter (fun i => L (tag i) = a)).card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter Finset.univ
    (Finset.univ.filter (fun t => L t = a)) tag

private theorem freq_sigma {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℕ) (t : T) :
    (Finset.univ.filter (fun x : Σ t, Fin (f t) => x.1 = t)).card = f t := by
  rw [← Fintype.card_subtype]
  simpa using Fintype.card_congr (Equiv.sigmaSubtype (β := fun t => Fin (f t)) t)

private theorem enumerate_margin {T : Type*} [Fintype T] [DecidableEq T] {n b : ℕ}
    (hn : 0 < n) (L : T → Fin n) (f : T → ℕ)
    (h : ∀ a, (∑ t ∈ Finset.univ.filter (fun t => L t = a), f t) = b) :
    ∃ e : Fin (n*b) ≃ (Σ t, Fin (f t)), ∀ i, L (e i).1 = tResidue hn i := by
  classical
  let fibers (a : Fin n) : {i : Fin (n*b) // tResidue hn i = a} ≃
      {x : Σ t, Fin (f t) // L x.1 = a} := by
    apply Fintype.equivOfCardEq
    rw [card_residue_fiber, Fintype.card_subtype, ← h a]
    simpa only [freq_sigma] using count_group (fun x : Σ t, Fin (f t) => x.1) L a
  exact ⟨Equiv.ofFiberEquiv fibers, Equiv.ofFiberEquiv_map fibers⟩

private theorem margin_of_tag {T : Type*} [Fintype T] [DecidableEq T] {n b : ℕ} (hn : 0 < n)
    (M : T → Fin n) (f : T → ℕ) (π : Equiv.Perm (Fin (n*b))) (tag : Fin (n*b) → T)
    (hM : ∀ i, M (tag i) = tResidue hn (π i))
    (hf : ∀ t, (Finset.univ.filter (fun i => tag i = t)).card = f t) (a : Fin n) :
    (∑ t ∈ Finset.univ.filter (fun t => M t = a), f t) = b := by
  simp_rw [← hf]
  rw [count_group, ← Fintype.card_subtype]
  apply Eq.trans _ (card_residue_fiber (b := b) hn a)
  exact Fintype.card_congr (π.subtypeEquiv (fun i => by rw [hM]))

theorem margins_iff_realize {T : Type*} [Fintype T] [DecidableEq T] {n b : ℕ}
    (hn : 0 < n) (L R : T → Fin n) (f : T → ℕ) :
    ((∀ a, (∑ t ∈ Finset.univ.filter (fun t => L t = a), f t) = b) ∧
      (∀ a, (∑ t ∈ Finset.univ.filter (fun t => R t = a), f t) = b)) ↔
    ∃ (π : Equiv.Perm (Fin (n*b))) (tag : Fin (n*b) → T),
      (∀ i, L (tag i) = ⟨i.val % n, Nat.mod_lt _ hn⟩) ∧
      (∀ i, R (tag i) = ⟨(π i).val % n, Nat.mod_lt _ hn⟩) ∧
      ∀ t, (Finset.univ.filter (fun i => tag i = t)).card = f t := by
  constructor
  · rintro ⟨hl,hr⟩
    obtain ⟨e,he⟩ := enumerate_margin hn L f hl
    obtain ⟨d,hd⟩ := enumerate_margin hn R f hr
    refine ⟨e.trans d.symm, fun i => (e i).1, he, ?_, ?_⟩
    · intro i
      simpa using hd (d.symm (e i))
    · intro t
      rw [← freq_sigma f t, ← Fintype.card_subtype, ← Fintype.card_subtype]
      exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
  · rintro ⟨π,tag,hl,hr,hf⟩
    exact ⟨margin_of_tag hn L f (Equiv.refl _) tag hl hf, margin_of_tag hn R f π tag hr hf⟩

end Dervish29734

namespace Dervish29734

variable {n q b : ℕ}

def blow (hn : 0 < n) (G : Fin n → Fin n → Bool) (b : ℕ) (i j : Fin (n*b)) : Bool :=
  G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩

open scoped Classical in
private theorem typedPairConflicts {I : Type*} [Fintype I] [DecidableEq I]
    (G : Fin n → Fin n → Bool) (label : I → Tag n q) :
    (pairConflicts (fun i j => targetOf G (label i) (label j))
      (fun i j => sigOf (label i) (label j))).card = Loss G (freq label) := by
  classical
  convert count_eq_loss G label using 1
  congr 1
  ext z
  simp [pairConflicts]

private theorem fits_freq_forward (hn : 0 < n) (G : Fin n → Fin n → Bool) {e : ℕ}
    (h : Fits q (n*b) (blow hn G b) e) : ∃ f, Margins b f ∧ Loss (q := q) G f ≤ e := by
  classical
  obtain ⟨π,rf,cf,R,C,out,h⟩ := h
  let label (i : Fin (n*b)) : Tag n q :=
    (⟨i.val % n, Nat.mod_lt _ hn⟩, ⟨(π i).val % n, Nat.mod_lt _ hn⟩, rf i, cf (π i),
     (fun j => decide (i ∈ R j)), (fun j => decide (π i ∈ C j)))
  refine ⟨freq label, (margins_iff_realize hn Left Right _).2 ⟨π, label, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩, ?_⟩
  let tar (i k : Fin (n*b)) := targetOf G (label i) (label k)
  let sg (i k : Fin (n*b)) := sigOf (label i) (label k)
  calc Loss G (freq label) = (pairConflicts tar sg).card := (typedPairConflicts G label).symm
       _ ≤ (pairErrors tar sg out).card := pairConflicts_le_errors tar sg out
       _ ≤ e := by
         have hs (i k : Fin (n*b)) : sg i k = fun j => decide (i ∈ R j ∨ π k ∈ C j) := by
           funext j
           simp [sg,sigOf,label,rowMem,colMem]
         apply le_trans _ h
         apply le_of_eq
         congr 1

private theorem fits_freq_reverse (hn : 0 < n) (G : Fin n → Fin n → Bool)
    (f : Tag n q → ℕ) (hf : Margins b f) : Fits q (n*b) (blow hn G b) (Loss G f) := by
  classical
  obtain ⟨π,label,hL,hR,hfreq⟩ := (margins_iff_realize hn Left Right f).1 hf
  have hfreq' : freq label = f := funext hfreq
  let tar (i k : Fin (n*b)) := targetOf G (label i) (label k)
  let sg (i k : Fin (n*b)) := sigOf (label i) (label k)
  obtain ⟨out,hout⟩ := pairErrors_optimal tar sg
  let R (j : Fin q) := Finset.univ.filter (fun i => rowMem (label i) j = true)
  let C (j : Fin q) := Finset.univ.filter (fun k => colMem (label (π.symm k)) j = true)
  refine ⟨π, fun i => rowFlip (label i), fun k => colFlip (label (π.symm k)), R, C, out, ?_⟩
  have hcard : (pairErrors tar sg out).card = Loss G f := by
    rw [hout, ←hfreq']
    exact typedPairConflicts G label
  simpa only [pairErrors,tar,targetOf,sg,sigOf_eq,R,C,Finset.mem_filter,Finset.mem_univ,
    true_and,Equiv.symm_apply_apply,hL,hR,blow] using hcard.le

theorem fits_iff_frequency (hn : 0 < n) (G : Fin n → Fin n → Bool) (e : ℕ) :
    Fits q (n*b) (blow hn G b) e ↔ ∃ f, Margins b f ∧ Loss (q := q) G f ≤ e := by
  constructor
  · exact fits_freq_forward hn G
  · rintro ⟨f,hf,he⟩
    obtain ⟨π,rf,cf,R,C,out,h⟩ := fits_freq_reverse hn G f hf
    exact ⟨π,rf,cf,R,C,out,h.trans he⟩

theorem opt_type_spec (n : ℕ) (hn : 0 < n) (q : ℕ) (G : Fin n → Fin n → Bool) (b : ℕ) :
    (∃ f, Margins b f ∧ Loss (q := q) G f = Opt n hn q G b) ∧
    (∀ f, Margins b f → Opt n hn q G b ≤ Loss (q := q) G f) := by
  classical
  have lower (f : Tag n q → ℕ) (hf : Margins b f) : Opt n hn q G b ≤ Loss G f :=
    Nat.sInf_le (s := {e : ℕ | Fits q (n*b) (blow hn G b) e}) (fits_freq_reverse hn G f hf)
  have ex : ∃ e, Fits q (n*b) (blow hn G b) e := by
    refine ⟨_, Equiv.refl _, fun _ => false, fun _ => false, fun _ => ∅, fun _ => ∅, fun _ _ => false, le_refl _⟩
  obtain ⟨f,hf,hle⟩ := fits_freq_forward hn G (e := Opt n hn q G b)
    (show Fits q (n*b) (blow hn G b) _ from Nat.sInf_mem (s := {e : ℕ | Fits q (n*b) (blow hn G b) e}) ex)
  exact ⟨⟨f, hf, le_antisymm hle (lower f hf)⟩, lower⟩

end Dervish29734

namespace RS
open scoped BigOperators Topology
open Filter

noncomputable def bil {I : Type*} [Fintype I] (B : Matrix I I ℝ) (x v : I → ℝ) : ℝ :=
  ∑ i, ∑ j, B i j * (x i * v j)

private theorem quad_line {I : Type*} [Fintype I] (B : Matrix I I ℝ)
    (x v : I → ℝ) (t : ℝ) :
    bil B (x + t • v) (x + t • v) = bil B x x +
      t * (bil B x v + bil B v x + t * bil B v v) := by
  simp only [bil, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem coeff_zero (D C : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ t * (D + t * C)) : D = 0 := by
  have hc : ContinuousAt (fun t : ℝ => D + t * C) 0 := by fun_prop
  rcases lt_trichotomy D 0 with hn | he | hp
  · have s : ∀ᶠ t : ℝ in 𝓝 0, D + t * C < 0 :=
      hc.eventually_lt (g := fun _ => (0 : ℝ)) continuousAt_const (by simpa)
    obtain ⟨t, ht, ht', ht''⟩ := ((frequently_gt_nhds (0 : ℝ)).and_eventually (s.and h)).exists
    exact False.elim ((not_lt_of_ge ht'') (mul_neg_of_pos_of_neg ht ht'))
  · exact he
  · have s : ∀ᶠ t : ℝ in 𝓝 0, 0 < D + t * C :=
      continuousAt_const.eventually_lt hc (by simpa)
    obtain ⟨t, ht, ht', ht''⟩ := ((frequently_lt_nhds (0 : ℝ)).and_eventually (s.and h)).exists
    exact False.elim ((not_lt_of_ge ht'') (mul_neg_of_neg_of_pos ht ht'))

theorem station {I J : Type*} [Fintype I] (A : Matrix J I ℝ) (B : Matrix I I ℝ)
    (x v : I → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hm : ∀ y : I → ℝ, (∀ i, 0 ≤ y i) → A.mulVec y = A.mulVec x → bil B x x ≤ bil B y y)
    (hv : A.mulVec v = 0) (hs : ∀ i, x i = 0 → v i = 0) :
    bil B x v + bil B v x = 0 := by
  have feasible : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 ≤ x i + t * v i := by
    apply eventually_all.mpr
    intro i
    by_cases hi : x i = 0
    · simp [hi, hs i hi]
    · have hi' : 0 < x i := lt_of_le_of_ne (hx i) (Ne.symm hi)
      have hc : ContinuousAt (fun t : ℝ => x i + t * v i) 0 := by fun_prop
      exact (continuousAt_const.eventually_lt hc (by simpa using hi')).mono (fun _ ht => le_of_lt ht)
  apply coeff_zero _ (bil B v v)
  filter_upwards [feasible] with t ht
  have h := hm (x + t • v) ht (by simp [Matrix.mulVec_add, Matrix.mulVec_smul, hv])
  rw [quad_line] at h
  linarith

end RS

namespace RR29734
open scoped BigOperators
variable {I J : Type*} [Fintype I]
noncomputable section

def lift (x : I → ℚ) : I → ℝ := fun i => x i

def row (a : I → ℚ) (x : I → ℝ) : ℝ := ∑ i, (a i : ℝ) * x i

def bil (B : I → I → ℚ) (x v : I → ℝ) : ℝ :=
  ∑ i, ∑ j, (B i j : ℝ) * (x i * v j)

def der (B : I → I → ℚ) (x v : I → ℝ) := bil B x v + bil B v x

def Tang (A : J → I → ℚ) (x v : I → ℝ) :=
  (∀ j, row (A j) v = 0) ∧ (∀ i, x i = 0 → v i = 0)

def Stat (A : J → I → ℚ) (B : I → I → ℚ) (x : I → ℝ) :=
  ∀ v, Tang A x v → der B x v = 0

private theorem map_mul (f : ℝ →ₗ[ℚ] ℚ) (a : ℚ) (t : ℝ) :
    f ((a : ℝ) * t) = a * f t := by
  simpa [Rat.smul_def] using f.map_smul a t

private theorem map_rat (f : ℝ →ₗ[ℚ] ℚ) (h : f 1 = 1) (a : ℚ) : f (a : ℝ) = a := by
  simpa [h] using map_mul f a 1

private theorem map_row (f : ℝ →ₗ[ℚ] ℚ) (a : I → ℚ) (x : I → ℝ) :
    (f (row a x) : ℝ) = row a (lift fun i => f (x i)) := by
  simp [row,lift,map_sum,map_mul]

private theorem map_bil₁ (f : ℝ →ₗ[ℚ] ℚ) (B : I → I → ℚ) (x : I → ℝ) (v : I → ℚ) :
    (f (bil B x (lift v)) : ℝ) = bil B (lift fun i => f (x i)) (lift v) := by
  have h (i j : I) : (B i j : ℝ) * (x i * (v j : ℝ)) = ((B i j * v j : ℚ) : ℝ) * x i := by push_cast; ring
  simp only [bil,lift,map_sum,h,map_mul,Rat.cast_sum]
  push_cast
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

private theorem map_bil₂ (f : ℝ →ₗ[ℚ] ℚ) (B : I → I → ℚ) (v : I → ℚ) (x : I → ℝ) :
    (f (bil B (lift v) x) : ℝ) = bil B (lift v) (lift fun i => f (x i)) := by
  have h (i j : I) : (B i j : ℝ) * ((v i : ℝ) * x j) = ((B i j * v i : ℚ) : ℝ) * x j := by push_cast; ring
  simp only [bil,lift,map_sum,h,map_mul,Rat.cast_sum]
  push_cast
  simp only [mul_assoc]

private theorem map_der₁ (f : ℝ →ₗ[ℚ] ℚ) (B : I → I → ℚ) (x : I → ℝ) (v : I → ℚ) :
    (f (der B x (lift v)) : ℝ) = der B (lift fun i => f (x i)) (lift v) := by
  simp [der, map_bil₁, map_bil₂]

private theorem map_der₂ (f : ℝ →ₗ[ℚ] ℚ) (B : I → I → ℚ) (v : I → ℚ) (x : I → ℝ) :
    (f (der B (lift v) x) : ℝ) = der B (lift v) (lift fun i => f (x i)) := by
  simp [der, map_bil₁, map_bil₂]

private theorem bil_sub_left (B : I → I → ℚ) (x y z : I → ℝ) :
    bil B (x-y) z = bil B x z - bil B y z := by
  simp [bil, Pi.sub_apply,sub_mul,mul_sub,Finset.sum_sub_distrib]

private theorem bil_sub_right (B : I → I → ℚ) (x y z : I → ℝ) :
    bil B x (y-z) = bil B x y - bil B x z := by
  simp [bil, Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]

abbrev ProjPos (I : Type*) := ∀ x : I → ℝ, ∃ f : ℝ →ₗ[ℚ] ℚ, f 1 = 1 ∧ ∀ i, 0 < x i → 0 < f (x i)

theorem replace_station (pr : ProjPos I) (A : J → I → ℚ) (B : I → I → ℚ) (b : J → ℚ)
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hm : ∀ j, row (A j) x = b j) (st : Stat A B x) :
    ∃ y : I → ℚ, (∀ i, 0 ≤ y i) ∧ (∀ i, 0 < y i ↔ 0 < x i) ∧
      (∀ j, row (A j) (lift y) = b j) ∧ Stat A B (lift y) ∧ bil B (lift y) (lift y) = bil B x x := by
  obtain ⟨f,hf,hpos⟩ := pr x
  let y (i : I) : ℚ := f (x i)
  have hzero (i : I) : x i = 0 → y i = 0 := by intro h; simp [y,h]
  have hpos' (i : I) : 0 < y i ↔ 0 < x i := by
    constructor
    · intro h; by_contra! hn; simp [hzero i (le_antisymm hn (hx i))] at h
    · exact hpos i
  have hy (i : I) : 0 ≤ y i := by
    rcases (hx i).eq_or_lt with he|hp
    · rw [hzero i he.symm]
    · exact (hpos i hp).le
  have hz (i : I) : lift y i = 0 ↔ x i = 0 := by
    simp only [lift,Rat.cast_eq_zero]
    constructor
    · intro h; by_contra hs; have := hpos i (lt_of_le_of_ne (hx i) (Ne.symm hs)); change 0 < y i at this; simp [h] at this
    · exact hzero i
  have hym (j : J) : row (A j) (lift y) = b j := by
    rw [← map_row f (A j) x,hm,map_rat f hf]
  have ratst (w : I → ℚ) (hw : Tang A x (lift w)) : der B (lift y) (lift w) = 0 := by
    rw [← map_der₁ f B x w, st _ hw]; simp
  have hst : Stat A B (lift y) := by
    intro v hv
    by_contra hn
    obtain ⟨g,hg⟩ := Module.Projective.exists_dual_ne_zero ℚ hn
    have hgv : Tang A x (lift fun i => g (v i)) := by
      constructor
      · intro j; rw [← map_row, hv.1 j]; simp
      · intro i hi; simp [lift,hv.2 i ((hz i).2 hi)]
    have h := map_der₂ g B y v
    rw [ratst _ hgv] at h
    exact hg (by exact_mod_cast h)
  refine ⟨y,hy,hpos',hym,hst,?_⟩
  let v : I → ℝ := lift y - x
  have hvr (j : J) : row (A j) v = 0 := by
    simp only [row, v, Pi.sub_apply, mul_sub,Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr ((hym j).trans (hm j).symm)
  have hvz (i : I) (h : x i = 0) : v i = 0 := by simp [v,h,(hz i).2 h]
  have h₁ := st v ⟨hvr,hvz⟩
  have h₂ := hst v ⟨hvr,fun i hi => hvz i ((hz i).1 hi)⟩
  simp only [der,v,bil_sub_left,bil_sub_right] at h₁ h₂
  linarith

end
end RR29734

namespace RR29734
open Filter Topology

theorem rationalProjection {I : Type*} [Finite I] (x : I → ℝ) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, f 1 = 1 ∧ ∀ i, 0 < x i → 0 < f (x i) := by
  classical
  let J := Module.Free.ChooseBasisIndex ℚ ℝ
  let b : Module.Basis J ℚ ℝ := Module.Free.chooseBasis ℚ ℝ
  let E (z : ℝ) (v : J → ℝ) := b.constr ℚ v z
  have hid : b.constr ℚ (fun j => b j) = LinearMap.id :=
    b.constr_eq ℚ (fun _ => rfl)
  have he (z : ℝ) : E z (fun j => b j) = z := by simp [E, hid]
  have hc (z : ℝ) : Continuous (E z) := by
    simp only [E, Module.Basis.constr_apply, Finsupp.sum]
    fun_prop
  have hp (z : ℝ) (hz : 0 < z) : ∀ᶠ v in 𝓝 (fun j => b j), 0 < E z v :=
    (hc z).continuousAt (Ioi_mem_nhds (by simpa only [he] using hz : 0 < E z (fun j => b j)))
  have ha : ∀ᶠ v in 𝓝 (fun j => b j), ∀ i, 0 < x i → 0 < E (x i) v := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases h : 0 < x i
    · exact (hp _ h).mono fun _ hv _ => hv
    · exact Eventually.of_forall fun _ hx => (h hx).elim
  let castV (v : J → ℚ) : J → ℝ := fun j => v j
  have hd : DenseRange castV := DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨v, hv⟩ := hd.mem_nhds ((hp 1 one_pos).and ha)
  let g : ℝ →ₗ[ℚ] ℚ := b.constr ℚ v
  have hg (z : ℝ) : E z (castV v) = (g z : ℝ) := by
    simp [E, g, castV, Module.Basis.constr_apply, Finsupp.sum, Rat.smul_def]
  have hv' : 0 < E 1 (castV v) ∧ ∀ i, 0 < x i → 0 < E (x i) (castV v) := hv
  simp only [hg, Rat.cast_pos] at hv'
  refine ⟨(g 1)⁻¹ • g, ?_, ?_⟩
  · simp [ne_of_gt hv'.1]
  · intro i hi
    exact mul_pos (inv_pos.mpr hv'.1) (hv'.2 i hi)

end RR29734

namespace Compact29734
open scoped BigOperators

variable {I J : Type*} [Fintype I]

theorem exists_quadratic_min (A : Matrix J I ℝ) (b : J → ℝ) (B : Matrix I I ℝ)
    (hne : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧ A.mulVec x = b)
    (hbox : ∀ x : I → ℝ, (∀ i, 0 ≤ x i) → A.mulVec x = b → ∀ i, x i ≤ 1) :
    ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧ A.mulVec x = b ∧
      ∀ y : I → ℝ, (∀ i, 0 ≤ y i) → A.mulVec y = b →
        dotProduct x (B.mulVec x) ≤ dotProduct y (B.mulVec y) := by
  let s : Set (I → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ A.mulVec x = b}
  have hc : Continuous (fun x : I → ℝ => A.mulVec x) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hclosed : IsClosed s := by
    change IsClosed ({x : I → ℝ | ∀ i, 0 ≤ x i} ∩ {x | A.mulVec x = b})
    apply IsClosed.inter _ (isClosed_eq hc continuous_const)
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hsmall : s ⊆ Set.univ.pi (fun _ : I => Set.Icc (0 : ℝ) 1) := by
    intro x hx i _
    exact ⟨hx.1 i, hbox x hx.1 hx.2 i⟩
  have hcompact : IsCompact s :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hclosed hsmall
  have hcont : Continuous (fun x : I → ℝ => dotProduct x (B.mulVec x)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  obtain ⟨x, hx, hm⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  exact ⟨x, hx.1, hx.2, fun y hy he => isMinOn_iff.mp hm y ⟨hy, he⟩⟩

theorem le_one_of_row_masses {R : Type*} [DecidableEq R] (row : I → R) (x : I → ℝ)
    (hn : ∀ i, 0 ≤ x i)
    (hm : ∀ r, (∑ i ∈ Finset.univ.filter (fun i => row i = r), x i) ≤ 1) :
    ∀ i, x i ≤ 1 := by
  intro i
  apply le_trans _ (hm (row i))
  exact Finset.single_le_sum (f := x) (fun j _ => hn j)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩)

theorem exists_sum_min (A : J → I → ℝ) (b : J → ℝ) (B : I → I → ℝ)
    (hne : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧ ∀ j, ∑ i, A j i * x i = b j)
    (hbox : ∀ x : I → ℝ, (∀ i, 0 ≤ x i) → (∀ j, ∑ i, A j i * x i = b j) → ∀ i, x i ≤ 1) :
    ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ j, ∑ i, A j i * x i = b j) ∧
      ∀ y : I → ℝ, (∀ i, 0 ≤ y i) → (∀ j, ∑ i, A j i * y i = b j) →
        (∑ i, ∑ k, B i k * (x i * x k)) ≤ ∑ i, ∑ k, B i k * (y i * y k) := by
  have eqn (x : I → ℝ) : Matrix.mulVec A x = b ↔ ∀ j, ∑ i, A j i * x i = b j :=
    funext_iff
  have cost (x : I → ℝ) : dotProduct x (Matrix.mulVec B x) =
      ∑ i, ∑ k, B i k * (x i * x k) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  obtain ⟨z, hz, he⟩ := hne
  obtain ⟨x, hx, hxe, hmin⟩ := exists_quadratic_min A b B ⟨z, hz, (eqn z).mpr he⟩
    (fun y hy heq => hbox y hy ((eqn y).mp heq))
  exact ⟨x, hx, (eqn x).mp hxe, fun y hy heq => by
    simpa only [cost] using hmin y hy ((eqn y).mpr heq)⟩

end Compact29734

namespace RR29734
open scoped BigOperators
variable {I J : Type*} [Fintype I]
noncomputable section

theorem replace_min (A : J → I → ℚ) (B : I → I → ℚ) (b : J → ℚ)
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) (hm : ∀ j, row (A j) x = b j)
    (hmin : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) → (∀ j, row (A j) z = b j) → bil B x x ≤ bil B z z) :
    ∃ y : I → ℚ, (∀ i, 0 ≤ y i) ∧ (∀ i, 0 < y i ↔ 0 < x i) ∧
      (∀ j, row (A j) (lift y) = b j) ∧ Stat A B (lift y) ∧ bil B (lift y) (lift y) = bil B x x := by
  refine replace_station rationalProjection A B b x hx hm ?_
  intro v hv
  let A' : Matrix J I ℝ := fun j i => A j i
  let B' : Matrix I I ℝ := fun i j => B i j
  apply RS.station A' B' x v hx _ _ hv.2
  · intro z hz he; exact hmin z hz (fun j => (congrFun he j).trans (hm j))
  · funext j; exact hv.1 j

theorem transport_min (S : J → Finset I) (B : I → I → ℚ)
    (cover : ∀ i, ∃ j, i ∈ S j)
    (hne : ∃ x : I → ℝ, (∀ i, 0 ≤ x i) ∧ (∀ j, ∑ i ∈ S j, x i = 1)) :
    ∃ y : I → ℚ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i ∈ S j, lift y i = 1) ∧
      (∀ z : I → ℝ, (∀ i, 0 ≤ z i) → (∀ j, ∑ i ∈ S j, z i = 1) →
        bil B (lift y) (lift y) ≤ bil B z z) ∧
      ∀ v, (∀ j, ∑ i ∈ S j, v i = 0) → (∀ i, lift y i = 0 → v i = 0) →
        der B (lift y) v = 0 := by
  classical
  let A (j : J) (i : I) : ℚ := if i ∈ S j then 1 else 0
  let A' : Matrix J I ℝ := fun j i => A j i
  let B' : Matrix I I ℝ := fun i j => B i j
  have hr (j : J) (z : I → ℝ) : row (A j) z = ∑ i ∈ S j, z i := by
    simp [row,A,apply_ite Rat.cast,ite_mul,← Finset.sum_filter]
  have hmr (j : J) (z : I → ℝ) : A'.mulVec z j = ∑ i ∈ S j, z i := hr j z
  have hfe (z : I → ℝ) : A'.mulVec z = (fun _ => 1) ↔ ∀ j, ∑ i ∈ S j, z i = 1 := by
    simp only [funext_iff,hmr]
  have hb (z : I → ℝ) : dotProduct z (B'.mulVec z) = bil B z z := by
    simp only [Matrix.mulVec,dotProduct,bil,B',Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; ring
  obtain ⟨x,hx,hm,hmin⟩ := Compact29734.exists_quadratic_min A' (fun _ => 1) B'
    (hne.imp fun z h => ⟨h.1,(hfe _).2 h.2⟩) (by
      intro z hz he i
      obtain ⟨j,hj⟩ := cover i
      exact (Finset.single_le_sum (f := z) (fun k _ => hz k) hj).trans (((hfe _).1 he j).le))
  have hrx (j : J) : row (A j) x = ((1 : ℚ) : ℝ) := by simpa only [hr,Rat.cast_one] using (hfe x).1 hm j
  have hopt (z : I → ℝ) (hz : ∀ i, 0 ≤ z i) (hmz : ∀ j, row (A j) z = ((1 : ℚ) : ℝ)) :
      bil B x x ≤ bil B z z := by
    simpa only [hb] using hmin z hz ((hfe z).2 <| by simpa only [hr,Rat.cast_one] using hmz)
  obtain ⟨y,hy,_,hmy,hsy,he⟩ := replace_min A B (fun _ => 1) x hx hrx hopt
  refine ⟨y,hy,by simpa only [hr,Rat.cast_one] using hmy,?_,?_⟩
  · intro z hz hzm; rw [he]; exact hopt z hz (by simpa only [hr,Rat.cast_one] using hzm)
  · intro v hv hs; exact hsy v ⟨by simpa only [hr] using hv,hs⟩

end
end RR29734

namespace Dervish29734.Dilation

open scoped BigOperators
variable {I J : Type*} [Fintype I]

theorem clear_nonneg (y : I → ℚ) (hy : ∀ i, 0 ≤ y i) :
    ∃ D : ℕ, 0 < D ∧ ∃ F : I → ℕ, ∀ i, (F i : ℚ) = (D : ℚ) * y i := by
  classical
  let D := ∏ i, (y i).den
  have hd : 0 < D := Finset.prod_pos fun i _ => (y i).den_pos
  have each (i : I) : ∃ n : ℕ, (n : ℚ) = (D : ℚ) * y i := by
    obtain ⟨t,ht⟩ := Finset.dvd_prod_of_mem (fun i => (y i).den) (Finset.mem_univ i)
    change D = (y i).den * t at ht
    refine ⟨(y i).num.toNat * t, ?_⟩
    have hn : (((y i).num.toNat : ℕ) : ℚ) = ((y i).num : ℚ) := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hy i))
    rw [ht, Nat.cast_mul, Nat.cast_mul, hn]
    have h := (div_eq_iff (show ((y i).den : ℚ) ≠ 0 by exact_mod_cast (y i).den_ne_zero)).mp (y i).num_div_den
    rw [h]; ring
  choose F hF using each
  exact ⟨D,hd,F,hF⟩

omit [Fintype I] in

theorem integral_margin {D : ℕ} {F : I → ℕ} {y : I → ℝ}
    (hF : ∀ i, (F i : ℝ) = (D : ℝ) * y i) (s : Finset I) (hs : ∑ i ∈ s, y i = 1) :
    ∑ i ∈ s, F i = D := by
  have h : (∑ i ∈ s, (F i : ℝ)) = (D : ℝ) := by simp only [hF, ← Finset.mul_sum, hs, mul_one]
  exact_mod_cast h

noncomputable def normalized (b : ℕ) (f : I → ℕ) : I → ℝ := fun i => (f i : ℝ) / b

omit [Fintype I] in
theorem unit_margin {b : ℕ} (hb : 0 < b) (f : I → ℕ) (s : Finset I) (hm : ∑ i ∈ s, f i = b) :
    ∑ i ∈ s, normalized b f i = 1 := by
  simp only [normalized, div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hm]
  exact mul_inv_cancel₀ (by exact_mod_cast hb.ne')

noncomputable def bil (K : I → I → ℕ) (x z : I → ℝ) : ℝ :=
  ∑ i, ∑ j, (K i j : ℝ) * (x i * z j)

def natPair (K : I → I → ℕ) (f g : I → ℕ) : ℕ := ∑ i, ∑ j, K i j * f i * g j

theorem normalized_bil (K : I → I → ℕ) (f g : I → ℕ) (a b : ℕ) :
    bil K (normalized a f) (normalized b g) = (natPair K f g : ℝ) / ((a : ℝ) * b) := by
  simp only [bil,normalized,natPair,Nat.cast_sum,Nat.cast_mul,div_eq_mul_inv,mul_inv_rev,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

theorem lower_of_min (K : I → I → ℕ) (S : J → Finset I) {D : ℕ} (hD : 0 < D)
    (F : I → ℕ) (hmin : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) → (∀ j, ∑ i ∈ S j, z i = 1) →
      bil K (normalized D F) (normalized D F) ≤ bil K z z)
    (b : ℕ) (f : I → ℕ) (hm : ∀ j, ∑ i ∈ S j, f i = b) :
    b^2 * natPair K F F ≤ D^2 * natPair K f f := by
  rcases b.eq_zero_or_pos with rfl|hb
  · simp
  have h := hmin (normalized b f) (fun i => by unfold normalized; positivity)
    (fun j => unit_margin hb f (S j) (hm j))
  rw [normalized_bil,normalized_bil] at h
  have hh := (div_le_div_iff₀ (by positivity) (by positivity)).mp h
  exact_mod_cast (by simpa only [pow_two,mul_comm] using hh : (b : ℝ)^2 * (natPair K F F : ℝ) ≤ (D : ℝ)^2 * natPair K f f)

theorem exists_integral_min (K : I → I → ℕ) (S : J → Finset I) (y : I → ℚ)
    (hy : ∀ i, 0 ≤ y i) (hS : ∀ j, ∑ i ∈ S j, (y i : ℝ) = 1)
    (hmin : ∀ z : I → ℝ, (∀ i, 0 ≤ z i) → (∀ j, ∑ i ∈ S j, z i = 1) →
      bil K (fun i => y i) (fun i => y i) ≤ bil K z z) :
    ∃ D : ℕ, 0 < D ∧ ∃ F : I → ℕ, normalized D F = (fun i => (y i : ℝ)) ∧
      (∀ j, ∑ i ∈ S j, F i = D) ∧ ∀ b (f : I → ℕ), (∀ j, ∑ i ∈ S j, f i = b) →
        b^2 * natPair K F F ≤ D^2 * natPair K f f := by
  obtain ⟨D,hD,F,hF⟩ := clear_nonneg y hy
  have hR (i : I) : (F i : ℝ) = (D : ℝ) * (y i : ℝ) := by exact_mod_cast hF i
  have he : normalized D F = fun i => (y i : ℝ) := by
    funext i
    unfold normalized
    rw [div_eq_iff (by exact_mod_cast hD.ne'), hR, mul_comm]
  refine ⟨D,hD,F,he,fun j => integral_margin hR (S j) (hS j), ?_⟩
  exact lower_of_min K S hD F (he.symm ▸ hmin)

theorem cross_of_unit_stationary (K : I → I → ℕ) (S : J → Finset I)
    {D : ℕ} (hD : 0 < D) (F M : I → ℕ)
    (hF : ∀ j, ∑ i ∈ S j, F i = D) (hM : ∀ j, ∑ i ∈ S j, M i = 1)
    (hsupp : ∀ i, F i = 0 → M i = 0)
    (hst : ∀ v : I → ℝ, (∀ j, ∑ i ∈ S j, v i = 0) → (∀ i, normalized D F i = 0 → v i = 0) →
      bil K (normalized D F) v + bil K v (normalized D F) = 0) :
    D * (natPair K M F + natPair K F M) = 2 * natPair K F F := by
  let v : I → ℝ := fun i => normalized 1 M i - normalized D F i
  have hrow (j : J) : ∑ i ∈ S j, v i = 0 := by
    simp only [v,Finset.sum_sub_distrib,unit_margin hD F _ (hF j),unit_margin Nat.zero_lt_one M _ (hM j),sub_self]
  have hz (i : I) (hi : normalized D F i = 0) : v i = 0 := by
    have : F i = 0 := by simpa [normalized, div_eq_zero_iff, hD.ne'] using hi
    simp [v,normalized,hsupp i this,this]
  have h := hst v hrow hz
  have hl (x y z : I → ℝ) : bil K (fun i => x i-y i) z = bil K x z - bil K y z := by
    simp [bil,sub_mul,mul_sub,Finset.sum_sub_distrib]
  have hr (x y z : I → ℝ) : bil K x (fun i => y i-z i) = bil K x y - bil K x z := by
    simp [bil,mul_sub,Finset.sum_sub_distrib]
  simp only [v,hl,hr,normalized_bil,Nat.cast_one,one_mul,mul_one] at h
  have hn : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  field_simp [hn] at h
  have hr' : (D : ℝ) * ((natPair K M F : ℝ) + natPair K F M) = 2 * natPair K F F := by
    linarith only [h]
  exact_mod_cast hr'

end Dervish29734.Dilation

namespace Dervish29734

open Finset

universe u v

namespace HallSupport

variable {ι : Type u} {α : Type v} [DecidableEq α] {t : ι → Finset α}

section Fintype

variable [Fintype ι]

theorem hall_cond_of_erase {x : ι} (a : α)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t))
    (s' : Finset { x' : ι | x' ≠ x }) : #s' ≤ #(s'.biUnion fun x' => (t x').erase a) := by
  have := Classical.decEq ι
  specialize ha (s'.image fun z => z.1)
  rw [image_nonempty, Finset.card_image_of_injective s' Subtype.coe_injective] at ha
  by_cases! he : s'.Nonempty
  · have ha' : #s' < #(s'.biUnion fun x => t x) := by
      convert ha he fun h => by simpa [← h] using mem_univ x using 2
      ext x
      simp only [mem_image, mem_biUnion, SetCoe.exists, exists_and_right,
        exists_eq_right]
    rw [← erase_biUnion]
    by_cases hb : a ∈ s'.biUnion fun x => t x
    · rw [card_erase_of_mem hb]
      exact Nat.le_sub_one_of_lt ha'
    · rw [erase_eq_of_notMem hb]
      exact Nat.le_of_lt ha'
  · subst s'
    simp

theorem hall_hard_inductive_step_A {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (ha : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (hn.symm ▸ Nat.succ_pos _)
  have := Classical.decEq ι

  let x := Classical.arbitrary ι
  have tx_ne : (t x).Nonempty := by
    rw [← Finset.card_pos]
    calc
      0 < 1 := Nat.one_pos
      _ ≤ #(.biUnion {x} t) := ht {x}
      _ = (t x).card := by rw [Finset.singleton_biUnion]
  choose y hy using tx_ne

  let ι' := { x' : ι | x' ≠ x }
  let t' : ι' → Finset α := fun x' => (t x').erase y
  have card_ι' : Fintype.card ι' = n :=
    calc
      Fintype.card ι' = Fintype.card ι - 1 := Set.card_ne_eq _
      _ = n := by rw [hn, Nat.add_succ_sub_one, add_zero]
  rcases ih t' card_ι'.le (hall_cond_of_erase y ha) with ⟨f', hfinj, hfr⟩

  refine ⟨fun z => if h : z = x then y else f' ⟨z, h⟩, ?_, ?_⟩
  · rintro z₁ z₂
    have key : ∀ {x}, y ≠ f' x := by
      intro x h
      simpa [t', ← h] using hfr x
    by_cases h₁ : z₁ = x <;> by_cases h₂ : z₂ = x <;>
      simp [h₁, h₂, hfinj.eq_iff, key, key.symm]
  · intro z
    simp only
    split_ifs with hz
    · rwa [hz]
    · specialize hfr ⟨z, hz⟩
      rw [mem_erase] at hfr
      exact hfr.2

theorem hall_cond_of_restrict {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) (s' : Finset (s : Set ι)) :
    #s' ≤ #(s'.biUnion fun a' => t a') := by
  classical
    rw [← card_image_of_injective s' Subtype.coe_injective]
    convert ht (s'.image fun z => z.1) using 1
    apply congr_arg
    ext y
    simp

theorem hall_cond_of_compl {ι : Type u} {t : ι → Finset α} {s : Finset ι}
    (hus : #s = #(s.biUnion t)) (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (s' : Finset (sᶜ : Set ι)) : #s' ≤ #(s'.biUnion fun x' => t x' \ s.biUnion t) := by
  have := Classical.decEq ι
  have disj : Disjoint s (s'.image fun z => z.1) := by
    simp only [disjoint_left, not_exists, mem_image, SetCoe.exists, exists_and_right,
      exists_eq_right]
    intro x hx hc _
    exact absurd hx hc
  have : #s' = #(s ∪ s'.image fun z => z.1) - #s := by
    simp [disj, card_image_of_injective _ Subtype.coe_injective]
  rw [this, hus]
  refine (Nat.sub_le_sub_right (ht _) _).trans ?_
  rw [← card_sdiff_of_subset]
  · gcongr
    intro t
    simp only [mem_biUnion, mem_sdiff, not_exists, mem_image, and_imp, mem_union,
      exists_imp]
    rintro x (hx | ⟨x', hx', rfl⟩) rat hs
    · exact False.elim <| (hs x) <| And.intro hx rat
    · use x', hx', rat, hs
  · apply biUnion_subset_biUnion_of_subset_left
    apply subset_union_left

theorem hall_hard_inductive_step_B {n : ℕ} (hn : Fintype.card ι = n + 1)
    (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t))
    (ih :
      ∀ {ι' : Type u} [Fintype ι'] (t' : ι' → Finset α),
        Fintype.card ι' ≤ n →
          (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
            ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x)
    (s : Finset ι) (hs : s.Nonempty) (hns : s ≠ univ) (hus : #s = #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  have := Classical.decEq ι

  rw [Nat.add_one] at hn
  have card_ι'_le : Fintype.card s ≤ n := by
    apply Nat.le_of_lt_succ
    calc
      Fintype.card s = #s := Fintype.card_coe _
      _ < Fintype.card ι := (card_lt_iff_ne_univ _).mpr hns
      _ = n.succ := hn
  let t' : s → Finset α := fun x' => t x'
  rcases ih t' card_ι'_le (hall_cond_of_restrict ht) with ⟨f', hf', hsf'⟩

  set ι'' := (s : Set ι)ᶜ
  let t'' : ι'' → Finset α := fun a'' => t a'' \ s.biUnion t
  have card_ι''_le : Fintype.card ι'' ≤ n := by
    simp_rw [ι'', ← Nat.lt_succ_iff, ← hn, ← Finset.coe_compl, coe_sort_coe]
    rwa [Fintype.card_coe, card_compl_lt_iff_nonempty]
  rcases ih t'' card_ι''_le (hall_cond_of_compl hus ht) with ⟨f'', hf'', hsf''⟩

  have f''_notMem_biUnion : ∀ (x'') (hx'' : x'' ∉ s), f'' ⟨x'', hx''⟩ ∉ s.biUnion t := by
    intro x'' hx''
    have h := hsf'' ⟨x'', hx''⟩
    rw [mem_sdiff] at h
    exact h.2
  have im_disj :
      ∀ (x' x'' : ι) (hx' : x' ∈ s) (hx'' : x'' ∉ s), f' ⟨x', hx'⟩ ≠ f'' ⟨x'', hx''⟩ := by
    grind
  refine ⟨fun x => if h : x ∈ s then f' ⟨x, h⟩ else f'' ⟨x, h⟩, ?_, ?_⟩
  · refine hf'.dite _ hf'' (@fun x x' => im_disj x x' _ _)
  · intro x
    simp only
    split_ifs with h
    · exact hsf' ⟨x, h⟩
    · exact sdiff_subset (hsf'' ⟨x, h⟩)

end Fintype

variable [Finite ι]

theorem hall_hard_inductive (ht : ∀ s : Finset ι, #s ≤ #(s.biUnion t)) :
    ∃ f : ι → α, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  cases nonempty_fintype ι
  generalize hn : Fintype.card ι = m
  induction m using Nat.strongRecOn generalizing ι with | ind n ih => _
  rcases n with (_ | n)
  · rw [Fintype.card_eq_zero_iff] at hn
    exact ⟨isEmptyElim, isEmptyElim, isEmptyElim⟩
  · have ih' : ∀ (ι' : Type u) [Fintype ι'] (t' : ι' → Finset α), Fintype.card ι' ≤ n →
        (∀ s' : Finset ι', #s' ≤ #(s'.biUnion t')) →
        ∃ f : ι' → α, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
      intro ι' _ _ hι' ht'
      exact ih _ (Nat.lt_succ_of_le hι') ht' _ rfl
    by_cases! h : ∀ s : Finset ι, s.Nonempty → s ≠ univ → #s < #(s.biUnion t)
    · refine hall_hard_inductive_step_A hn ht (@fun ι' => ih' ι') h
    · rcases h with ⟨s, sne, snu, sle⟩
      exact hall_hard_inductive_step_B hn ht (@fun ι' => ih' ι')
        s sne snu (Nat.le_antisymm (ht _) sle)

end HallSupport

theorem supportedPerm {ι : Type*} [Fintype ι] (M : ι → ι → ℕ) {d : ℕ} (hd : 0 < d)
    (row : ∀ i, ∑ j, M i j = d) (col : ∀ j, ∑ i, M i j = d) :
    ∃ σ : Equiv.Perm ι, ∀ i, 0 < M i (σ i) := by
  classical
  let f (i : ι) : Finset ι := univ.filter fun j => M i j ≠ 0
  have hf (A : Finset ι) : A.card ≤ (A.biUnion f).card := by
    have h (i : ι) : ∑ j ∈ f i, M i j = d := by
      rw [← row i]
      apply sum_subset (filter_subset _ _)
      intro j _ hj
      simpa [f] using hj
    have h₁ : ∑ i ∈ A, ∑ j ∈ f i, M i j = A.card * d := by simp [h]
    have h₂ : ∑ i, ∑ j ∈ A.biUnion f, M i j = (A.biUnion f).card * d := by
      rw [sum_comm]; simp [col]
    apply Nat.le_of_mul_le_mul_right _ hd
    rw [← h₁, ← h₂]
    trans ∑ i ∈ A, ∑ j ∈ A.biUnion f, M i j
    · apply sum_le_sum
      intro i hi
      exact sum_le_sum_of_subset (subset_biUnion_of_mem f hi)
    · exact sum_le_sum_of_subset (subset_univ A)
  obtain ⟨g, hg, hmem⟩ := HallSupport.hall_hard_inductive hf
  refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hg), fun i => ?_⟩
  exact Nat.pos_of_ne_zero (mem_filter.mp (hmem i)).2

theorem supportedLabelledPerm {ι Label : Type*} [Fintype ι] [Fintype Label]
    (M : ι → ι → Label → ℕ) {d : ℕ} (hd : 0 < d)
    (row : ∀ i, ∑ j, ∑ l, M i j l = d) (col : ∀ j, ∑ i, ∑ l, M i j l = d) :
    ∃ (σ : Equiv.Perm ι) (label : ι → Label), ∀ i, 0 < M i (σ i) (label i) := by
  classical
  obtain ⟨σ, hσ⟩ := supportedPerm (fun i j => ∑ l, M i j l) hd row col
  have h (i : ι) : ∃ l, 0 < M i (σ i) l := by
    by_contra! h
    exact (Nat.ne_of_gt (hσ i)) (sum_eq_zero fun l _ => Nat.eq_zero_of_le_zero (h l))
  choose label hlabel using h
  exact ⟨σ, label, hlabel⟩

theorem supportedHistogram {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq ι]
    (L R : A → ι) (x : A → ℕ) {d : ℕ} (hd : 0 < d)
    (hL : ∀ i, (∑ a, if L a = i then x a else 0) = d)
    (hR : ∀ j, (∑ a, if R a = j then x a else 0) = d) :
    ∃ m : ι → A, (∀ i, L (m i) = i) ∧ Function.Bijective (R ∘ m) ∧ ∀ i, 0 < x (m i) := by
  classical
  let M (i j : ι) (a : A) := if L a = i ∧ R a = j then x a else 0
  have hrow (i : ι) : ∑ j, ∑ a, M i j a = d := by
    rw [sum_comm, ← hL i]
    apply sum_congr rfl
    intro a _
    by_cases h : L a = i <;> simp [M, h]
  have hcol (j : ι) : ∑ i, ∑ a, M i j a = d := by
    rw [sum_comm, ← hR j]
    apply sum_congr rfl
    intro a _
    by_cases h : R a = j <;> simp [M, h]
  obtain ⟨σ, m, hm⟩ := supportedLabelledPerm M hd hrow hcol
  have h (i : ι) : (L (m i) = i ∧ R (m i) = σ i) ∧ 0 < x (m i) := by
    have := hm i
    simpa [M, apply_ite] using this
  refine ⟨m, fun i => (h i).1.1, ?_, fun i => (h i).2⟩
  have he : R ∘ m = (σ : ι → ι) := funext fun i => (h i).1.2
  rw [he]
  exact σ.bijective

theorem supportedCounts {A ι : Type*} [Fintype A] [Fintype ι] [DecidableEq A] [DecidableEq ι]
    (L R : A → ι) (x : A → ℕ) {d : ℕ} (hd : 0 < d)
    (hL : ∀ i, ∑ a ∈ univ.filter (fun a => L a = i), x a = d)
    (hR : ∀ j, ∑ a ∈ univ.filter (fun a => R a = j), x a = d) :
    ∃ m : ι → A, let h := fun a => (univ.filter fun i => m i = a).card
      (∀ i, L (m i) = i) ∧ Function.Bijective (R ∘ m) ∧ (∀ a, h a ≤ x a) ∧
      (∀ i, ∑ a ∈ univ.filter (fun a => L a = i), h a = 1) ∧
       ∀ j, ∑ a ∈ univ.filter (fun a => R a = j), h a = 1 := by
  obtain ⟨m, hleft, hright, hpos⟩ := supportedHistogram L R x hd
    (fun i => by simpa only [sum_filter] using hL i)
    (fun j => by simpa only [sum_filter] using hR j)
  have hinj : Function.Injective m := Function.LeftInverse.injective hleft
  have single (k : ι) : (univ.filter fun i => i = k) = {k} := by ext; simp
  have count (a : A) : (univ.filter fun i => m i = a).card ≤ x a := by
    by_cases hex : ∃ i, m i = a
    · obtain ⟨i, rfl⟩ := hex
      simpa [hinj.eq_iff, single] using (show 1 ≤ x (m i) by have := hpos i; omega)
    · have hz : (univ.filter fun i => m i = a) = ∅ := by
        apply filter_false_of_mem
        exact fun i _ hi => hex ⟨i, hi⟩
      simp [hz]
  have margin (q : A → ι) (hb : Function.Bijective (q ∘ m)) (j : ι) :
      (∑ a ∈ univ.filter (fun a => q a = j), (univ.filter fun i => m i = a).card) = 1 := by
    obtain ⟨k, rfl⟩ := hb.2 j
    have eqs : ∀ i, q (m i) = q (m k) ↔ i = k := fun i => hb.1.eq_iff
    simpa [Function.comp_apply, eqs, single] using sum_card_fiberwise_eq_card_filter univ
      (univ.filter fun a => q a = q (m k)) m
  have hl : L ∘ m = id := funext hleft
  exact ⟨m, hleft, hright, count, margin L (hl ▸ Function.bijective_id), margin R hright⟩

end Dervish29734

namespace Dervish29734

theorem matchingConflictSum_le {τ : Type*} {n : ℕ} (m : Fin n → τ)
    (K : τ → τ → ℕ) (diag : ∀ a, K a a = 0) (unit : ∀ a b, K a b ≤ 1) :
    (∑ i, ∑ j, K (m i) (m j)) ≤ n * (n - 1) := by
  classical
  calc
    _ ≤ ∑ i : Fin n, (n - 1) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ = ∑ j ∈ Finset.univ.erase i, K (m i) (m j) := by
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), diag, Nat.add_zero]
        _ ≤ ∑ j ∈ Finset.univ.erase i, 1 := Finset.sum_le_sum fun j _ => unit _ _
        _ = _ := by simp [Finset.card_erase_of_mem]
    _ = _ := by simp

theorem matchingCost_le_choose_two {τ : Type*} {n : ℕ} (m : Fin n → τ)
    (K : τ → τ → ℕ) (diag : ∀ a, K a a = 0) (unit : ∀ a b, K a b ≤ 1) :
    (∑ i, ∑ j, K (m i) (m j)) / 2 ≤ Nat.choose n 2 := by
  rw [Nat.choose_two_right]
  exact Nat.div_le_div_right (matchingConflictSum_le m K diag unit)

def matchHistogram {n : ℕ} {τ : Type*} [DecidableEq τ] (m : Fin n → τ) (a : τ) : ℕ :=
  (Finset.univ.filter (fun i => m i = a)).card

theorem sum_mul_matchHistogram {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (m : Fin n → τ) (f : τ → ℕ) : (∑ a, f a * matchHistogram m a) = ∑ i, f (m i) := by
  calc
    _ = ∑ a, ∑ i ∈ Finset.univ.filter (fun i => m i = a), f a := by
      simp [matchHistogram, Nat.mul_comm]
    _ = ∑ a, ∑ i ∈ Finset.univ.filter (fun i => m i = a), f (m i) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise _ _ _

theorem histogram_pairCost_eq {n : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]
    (m : Fin n → τ) (K : τ → τ → ℕ) :
    (∑ a, ∑ b, K a b * matchHistogram m a * matchHistogram m b) = ∑ i, ∑ j, K (m i) (m j) := by
  calc
    _ = ∑ a, (∑ b, K a b * matchHistogram m b) * matchHistogram m a := by
      simp only [Finset.sum_mul, Nat.mul_right_comm]
    _ = ∑ i, ∑ b, K (m i) b * matchHistogram m b := sum_mul_matchHistogram _ _
    _ = _ := Finset.sum_congr rfl (fun i _ => sum_mul_matchHistogram _ _)

theorem orientedMatchingCost_le {τ : Type*} {n : ℕ} (m : Fin n → τ)
    (K : τ → τ → ℕ) (diag : ∀ a, K a a = 0) (orient : ∀ a b, K a b + K b a ≤ 1) :
    (∑ i, ∑ j, K (m i) (m j)) ≤ Nat.choose n 2 := by
  have h := matchingConflictSum_le m (fun a b => K a b + K b a)
    (fun a => by simp [diag]) orient
  simp only [Finset.sum_add_distrib] at h
  have sw : (∑ i, ∑ j, K (m j) (m i)) = ∑ i, ∑ j, K (m i) (m j) := Finset.sum_comm
  rw [sw] at h
  rw [Nat.choose_two_right]
  omega

theorem orientedHistogramCost_le {τ : Type*} [Fintype τ] [DecidableEq τ] {n : ℕ}
    (m : Fin n → τ) (K : τ → τ → ℕ) (diag : ∀ a, K a a = 0)
    (orient : ∀ a b, K a b + K b a ≤ 1) :
    (∑ a, ∑ b, K a b * matchHistogram m a * matchHistogram m b) ≤ Nat.choose n 2 := by
  rw [histogram_pairCost_eq]
  exact orientedMatchingCost_le m K diag orient

end Dervish29734

namespace Rounding29734

open Finset

variable {A : Type*} [Fintype A]

def pair {R : Type*} [CommSemiring R] (K : A → A → R) (x y : A → R) : R :=
  ∑ a, ∑ b, K a b * x a * y b

theorem add_left {R : Type*} [CommSemiring R] (K : A → A → R) (x y z : A → R) :
    pair K (fun a => x a+y a) z = pair K x z + pair K y z := by
  simp [pair, mul_add, add_mul, Finset.sum_add_distrib]

theorem add_right {R : Type*} [CommSemiring R] (K : A → A → R) (x y z : A → R) :
    pair K x (fun a => y a+z a) = pair K x y + pair K x z := by
  simp [pair, mul_add, Finset.sum_add_distrib]

theorem scale_left {R : Type*} [CommSemiring R] (K : A → A → R) (t : R) (x y : A → R) :
    pair K (fun a => t * x a) y = t * pair K x y := by
  simp [pair, Finset.mul_sum, mul_left_comm, mul_comm]

theorem scale_right {R : Type*} [CommSemiring R] (K : A → A → R) (t : R) (x y : A → R) :
    pair K x (fun a => t * y a) = t * pair K x y := by
  simp [pair, Finset.mul_sum, mul_left_comm, mul_comm]

def marg {n : ℕ} (L R : A → Fin n) (d : ℕ) (x : A → ℕ) : Prop :=
  (∀ i, ∑ a ∈ univ.filter (fun a => L a = i), x a = d) ∧
  (∀ i, ∑ a ∈ univ.filter (fun a => R a = i), x a = d)

private theorem marg_mix {n : ℕ} {L R : A → Fin n} {D E : ℕ} {x m : A → ℕ}
    (hx : marg L R D x) (hm : marg L R E m) (t r : ℕ) :
    marg L R (t*D + r*E) (fun a => t*x a + r*m a) := by
  constructor <;> intro i <;> simp [Finset.sum_add_distrib, ← Finset.mul_sum, hx.1, hx.2, hm.1, hm.2]

private theorem marg_remove {n : ℕ} {L R : A → Fin n} {d : ℕ} {x m : A → ℕ}
    (hx : marg L R (d+1) x) (hm : marg L R 1 m) (le : ∀ a, m a ≤ x a) :
    marg L R d (fun a => x a - m a) := by
  have addBack (f : A → Fin n) (i : Fin n) :
      (∑ a ∈ univ.filter (fun a => f a = i), (x a - m a)) +
      (∑ a ∈ univ.filter (fun a => f a = i), m a) =
      ∑ a ∈ univ.filter (fun a => f a = i), x a := by
    rw [← Finset.sum_add_distrib]; simp [Nat.sub_add_cancel (le _)]
  constructor
  · intro i; have h := addBack L i; rw [hx.1,hm.1] at h; exact Nat.add_right_cancel h
  · intro i; have h := addBack R i; rw [hx.2,hm.2] at h; exact Nat.add_right_cancel h

private theorem each_layer {n : ℕ} {L R : A → Fin n} {P : (A → ℕ) → Prop}
    (peel : ∀ d, 0<d → ∀ x, marg L R d x → ∃ m, marg L R 1 m ∧ (∀ a, m a ≤ x a) ∧ P m)
    (W : (A → ℕ) → ℕ) (addW : ∀ x y, W (fun a => x a+y a) = W x + W y)
    (c : ℕ) (d : ℕ) (x : A → ℕ) (hx : marg L R d x)
    (lo : ∀ m, marg L R 1 m → (∀ a, m a ≤ x a) → P m → c ≤ W m) : d*c ≤ W x := by
  induction d generalizing x with
  | zero => simp
  | succ d ih =>
    obtain ⟨m,hm,hle,hP⟩ := peel _ (Nat.succ_pos _) x hx
    let z := fun a => x a - m a
    have hz : marg L R d z := marg_remove hx hm hle
    have hzlo := ih z hz (fun u hu hule hp => lo u hu (fun a => (hule a).trans (Nat.sub_le ..)) hp)
    have hxz : (fun a => z a + m a) = x := funext fun a => Nat.sub_add_cancel (hle a)
    rw [Nat.succ_mul, ← hxz, addW]
    exact Nat.add_le_add hzlo (lo m hm hle hP)

theorem pick_layer {n : ℕ} {L R : A → Fin n} {P : (A → ℕ) → Prop}
    (peel : ∀ d, 0<d → ∀ x, marg L R d x → ∃ m, marg L R 1 m ∧ (∀ a, m a ≤ x a) ∧ P m)
    (W : (A → ℕ) → ℕ) (addW : ∀ x y, W (fun a => x a+y a) = W x + W y)
    {D : ℕ} (hD : 0<D) {x : A → ℕ} (hx : marg L R D x) :
    ∃ m, marg L R 1 m ∧ (∀ a, m a ≤ x a) ∧ P m ∧ D*W m ≤ W x := by
  classical
  by_contra! h
  have lo (m) (hm : marg L R 1 m) (hle : ∀ a, m a ≤ x a) (hp : P m) : W x / D + 1 ≤ W m := by
    have hh := h m hm hle hp
    exact (Nat.div_lt_iff_lt_mul hD).mpr ((Nat.mul_comm _ _).symm ▸ hh)
  have bound := each_layer peel W addW (W x/D+1) D x hx lo
  have bad : W x < (W x/D+1)*D := (Nat.div_lt_iff_lt_mul hD).mp (Nat.lt_succ_self _)
  rw [Nat.mul_comm] at bad
  omega

theorem round_of_cross_le (K : A → A → ℕ) (D b c : ℕ) (x m : A → ℕ)
    (cross : D*(pair K m x + pair K x m) ≤ 2*pair K x x) (hm : pair K m m ≤ c) :
    let y := fun a => (b/D)*x a + (b%D)*m a
    D^2*pair K y y ≤ b^2*pair K x x + (b%D)^2*D^2*c := by
  dsimp only
  let t := b / D
  let r := b % D
  have eqb : t*D+r=b := by simpa [t,r,Nat.mul_comm] using Nat.div_add_mod b D
  change D^2 * pair K (fun a => t*x a+r*m a) (fun a => t*x a+r*m a) ≤ _
  simp only [add_left, add_right, scale_left, scale_right]
  calc
    _ = ((t*D)^2*pair K x x + (t*r*D)*(D*(pair K m x + pair K x m))) +
        (r^2*D^2)*pair K m m := by ring
    _ ≤ ((t*D)^2*pair K x x + (t*r*D)*(2*pair K x x)) + (r^2*D^2)*c := by gcongr
    _ ≤ (t*D+r)^2*pair K x x + (r^2*D^2)*c := by
      have h : ((t*D)^2*pair K x x + (t*r*D)*(2*pair K x x)) + r^2*pair K x x =
          (t*D+r)^2*pair K x x := by ring
      omega
    _ = _ := by rw [eqb]

theorem round_by_layers {n : ℕ} {L R : A → Fin n} (K : A → A → ℕ) (cap : ℕ)
    (peel : ∀ d, 0<d → ∀ x, marg L R d x → ∃ m, marg L R 1 m ∧ (∀ a, m a ≤ x a) ∧ pair K m m ≤ cap)
    {D : ℕ} (hD : 0<D) {x : A → ℕ} (hx : marg L R D x) (b : ℕ) :
    ∃ y, marg L R b y ∧ D^2 * pair K y y ≤ b^2 * pair K x x + (b%D)^2*D^2*cap := by
  let W := fun m => pair K m x + pair K x m
  have addW (u v : A → ℕ) : W (fun a => u a+v a) = W u+W v := by
    simp [W,add_left,add_right]; omega
  obtain ⟨m,hm,_,hcap,hcross⟩ := pick_layer peel W addW hD hx
  have hcr : D*(pair K m x+pair K x m) ≤ 2*pair K x x := by simpa [W,two_mul] using hcross
  refine ⟨_, ?_, round_of_cross_le K D b cap x m hcr hcap⟩
  have eqb : (b/D)*D+(b%D)*1=b := by simpa [Nat.mul_comm] using Nat.div_add_mod b D
  simpa only [eqb] using marg_mix hx hm (b/D) (b%D)

end Rounding29734

namespace Rounding29734

theorem round_regular {A : Type*} [Fintype A] {n : ℕ} (L R : A → Fin n)
    (K : A → A → ℕ) (diag : ∀ a, K a a = 0) (orient : ∀ a b, K a b + K b a ≤ 1)
    {D : ℕ} (hD : 0<D) {x : A → ℕ} (hx : marg L R D x) (b : ℕ) :
    ∃ y, marg L R b y ∧ D^2 * pair K y y ≤ b^2 * pair K x x + (b%D)^2*D^2*Nat.choose n 2 := by
  classical
  apply round_by_layers K (Nat.choose n 2) _ hD hx b
  intro d hd v hv
  obtain ⟨m,_,_,hle,hmL,hmR⟩ := Dervish29734.supportedCounts L R v hd hv.1 hv.2
  exact ⟨Dervish29734.matchHistogram m, ⟨hmL,hmR⟩, hle, Dervish29734.orientedHistogramCost_le m K diag orient⟩

end Rounding29734

namespace Dervish29734

theorem period_of_model {X : Type*} {adm : ℕ → X → Prop} {cost : X → ℕ}
    {opt : ℕ → ℕ} {D c : ℕ} {x : X} (hD : 0<D) (hx : adm D x)
    (rep : ∀ b, 0<b → (∃ f, adm b f ∧ cost f = opt b) ∧ (∀ f, adm b f → opt b ≤ cost f))
    (lower : ∀ b, 0<b → ∀ f, adm b f → b^2*cost x ≤ D^2*cost f)
    (upper : ∀ b, 0<b → ∃ f, adm b f ∧ D^2*cost f ≤ b^2*cost x+(b%D)^2*D^2*c) :
    Period c opt D := by
  obtain ⟨f, hf, hef⟩ := (rep D hD).1
  have lo := lower D hD f hf
  rw [hef] at lo
  have base : cost x = opt D := le_antisymm (Nat.le_of_mul_le_mul_left lo (pow_pos hD 2)) ((rep D hD).2 x hx)
  intro b hb
  obtain ⟨g, hg, heg⟩ := (rep b hb).1
  obtain ⟨k, hk, ub⟩ := upper b hb
  rw [← base]
  exact ⟨heg ▸ lower b hb g hg, (Nat.mul_le_mul_left _ ((rep b hb).2 k hk)).trans ub⟩

end Dervish29734

namespace Dervish29734

theorem individual (n : ℕ) (hn : 0<n) (q : ℕ) (G : Fin n → Fin n → Bool) :
    ∃ d, 0<d ∧ Period (Nat.choose n 2) (Opt n hn q G) d := by
  classical
  let S : Fin n ⊕ Fin n → Finset (Tag n q) := Sum.elim
    (fun i => Finset.univ.filter (fun t => Left t = i))
    (fun i => Finset.univ.filter (fun t => Right t = i))
  have hs (b : ℕ) (f : Tag n q → ℕ) : Margins b f ↔ ∀ j, ∑ t ∈ S j, f t = b := by
    constructor
    · intro h j; cases j with
      | inl a => exact h.1 a
      | inr a => exact h.2 a
    · intro h; exact ⟨fun a => h (.inl a),fun a => h (.inr a)⟩
  obtain ⟨f,hf,_⟩ := (opt_type_spec n hn q G 1).1
  let KQ : Tag n q → Tag n q → ℚ := fun i j => K G i j
  obtain ⟨y,hy,hm,hmin,_⟩ := RR29734.transport_min S KQ
    (fun i => ⟨Sum.inl (Left i),by simp [S]⟩)
    ⟨fun i => (f i : ℝ), fun i => Nat.cast_nonneg _, fun j => by
      change (∑ i ∈ S j, (f i : ℝ)) = 1
      rw [← Nat.cast_sum]
      exact_mod_cast (hs _ _).1 hf j⟩
  have hc (z : Tag n q → ℝ) (hz : ∀ i, 0 ≤ z i) (har : ∀ j, ∑ i ∈ S j, z i = 1) :
      Dilation.bil (K G) (fun i => (y i : ℝ)) (fun i => (y i : ℝ)) ≤ Dilation.bil (K G) z z := by
    simpa only [Dilation.bil,RR29734.bil,KQ,RR29734.lift,Rat.cast_natCast] using hmin z hz har
  obtain ⟨D,hD,x,_,hx,hlo⟩ := Dilation.exists_integral_min (K G) S y hy hm hc
  have hmx := (hs D x).2 hx
  refine ⟨D,hD,period_of_model (cost := Loss G) (adm := fun b f => Margins b f) hD hmx
    (fun b _ => opt_type_spec n hn q G b) ?_ ?_⟩
  · intro b _ v hv
    exact hlo b v ((hs b v).1 hv)
  · intro b _
    exact Rounding29734.round_regular Left Right (K G) (K_diag G) (K_swap_le G) hD hmx b

end Dervish29734

end PEqualNP.Outside.L_meta_29734

theorem PEqualNP.Outside.L_meta_29734 : (∀ (n : ℕ) (hn : 0 < n), ∃ D : ℕ, 0 < D ∧ ∀ q : ℕ,
  let fits := fun (s : ℕ) (G : Fin s → Fin s → Bool) (budget : ℕ) =>
    ∃ (π : Equiv.Perm (Fin s)) (rf cf : Fin s → Bool) (R C : Fin q → Finset (Fin s))
      (out : Finset (Fin s) → (Fin q → Bool) → Bool),
      ((Finset.univ : Finset (Fin s × Fin s)).filter (fun z =>
        out {z.1,z.2} (fun j => decide (z.1 ∈ R j ∨ π z.2 ∈ C j)) ≠
          Bool.xor (G z.1 (π z.2)) (Bool.xor (rf z.1) (cf (π z.2))))).card ≤ budget
  ∀ G : Fin n → Fin n → Bool,
    let opt := fun (b : ℕ) => sInf {e : ℕ | fits (n*b)
      (fun i j => G ⟨i.val % n, Nat.mod_lt _ hn⟩ ⟨j.val % n, Nat.mod_lt _ hn⟩) e}
    ∀ b : ℕ, 0 < b →
      b^2 * opt D ≤ D^2 * opt b ∧
      D^2 * opt b ≤ b^2 * opt D + (b % D)^2 * D^2 * Nat.choose n 2) := by
  apply PEqualNP.Outside.L_meta_29734.Dervish29734.assemble
  · intro n hn q G; exact PEqualNP.Outside.L_meta_29734.Dervish29734.individual n hn q.val G
  · intro n hn q G hq b _
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le (PEqualNP.Outside.L_meta_29734.Dervish29734.LargeQ.fits_zero_of_le n q hn hq G b))
