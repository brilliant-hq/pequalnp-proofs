import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25746

def bitB (b : Bool) : ZMod 2 := if b then 1 else 0

def quad (G : Fin 4 → Fin 4 → Bool) (f : Fin 4 → Fin 4) (i j : Fin 4) : Bool :=
  Bool.xor (Bool.xor (G i (f i)) (G j (f j))) (Bool.xor (G i (f j)) (G j (f i)))

abbrev condB (G : Fin 4 → Fin 4 → Bool) (f : Fin 4 → Fin 4) (k l : Fin 4 → Bool) : Prop :=
  ∀ i j, k i = true → k j = true → quad G f i j = Bool.xor (l i) (l j)

def cnt (l : Fin 4 → Bool) : ℕ := (l 0).toNat + (l 1).toNat + (l 2).toNat + (l 3).toNat

def anch (G : Fin 4 → Fin 4 → Bool) : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun i j =>
  bitB (G i.succ j.succ) + bitB (G i.succ 0) + bitB (G 0 j.succ) + bitB (G 0 0)

def detE (G : Fin 4 → Fin 4 → Bool) : ZMod 2 :=
  anch G 0 0 * anch G 1 1 * anch G 2 2 - anch G 0 0 * anch G 1 2 * anch G 2 1
    - anch G 0 1 * anch G 1 0 * anch G 2 2 + anch G 0 1 * anch G 1 2 * anch G 2 0
    + anch G 0 2 * anch G 1 0 * anch G 2 1 - anch G 0 2 * anch G 1 1 * anch G 2 0

def tot (G : Fin 4 → Fin 4 → Bool) : ZMod 2 := ∑ i : Fin 4, ∑ j : Fin 4, bitB (G i j)

def mk (a b c d e f g h k : Bool) : Fin 4 → Fin 4 → Bool :=
  ![![false, false, false, false], ![false, a, b, c], ![false, d, e, f], ![false, g, h, k]]

abbrev Core (G : Fin 4 → Fin 4 → Bool) : Prop :=
  detE G ≠ 0 →
  (∃ a b c d : Fin 4, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ∃ k0 k1 k2 k3 : Bool, cnt ![k0, k1, k2, k3] = 3 ∧
      condB G ![a, b, c, d] ![k0, k1, k2, k3] (fun _ => false)) ∧
  (∃ a b c d : Fin 4, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    ∃ l0 l1 l2 l3 : Bool, cnt ![l0, l1, l2, l3] ≤ 2 ∧ (tot G ≠ 0 → cnt ![l0, l1, l2, l3] ≤ 1) ∧
      condB G ![a, b, c, d] (fun _ => true) ![l0, l1, l2, l3]) ∧
  (∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ l0 l1 l2 l3 : Bool, cnt ![l0, l1, l2, l3] ≤ 1 →
      condB G ![a, b, c, d] (fun _ => true) ![l0, l1, l2, l3] →
      cnt ![l0, l1, l2, l3] = 1 ∧ tot G ≠ 0)

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_fff : ∀ d e f g h k : Bool, Core (mk false false false d e f g h k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_fft : ∀ d e f g h k : Bool, Core (mk false false true d e f g h k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_ftf : ∀ d e f g h k : Bool, Core (mk false true false d e f g h k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_ftt : ∀ d e f g h k : Bool, Core (mk false true true d e f g h k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_tff : ∀ d e f g h k : Bool, Core (mk true false false d e f g h k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_tft : ∀ d e f g h k : Bool, Core (mk true false true d e f g h k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_ttf : ∀ d e f g h k : Bool, Core (mk true true false d e f g h k) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem core_ttt : ∀ d e f g h k : Bool, Core (mk true true true d e f g h k) := by
  decide +kernel

theorem core_all : ∀ a b c d e f g h k : Bool, Core (mk a b c d e f g h k) := by
  intro a b c
  cases a <;> cases b <;> cases c
  exacts [core_fff, core_fft, core_ftf, core_ftt, core_tff, core_tft, core_ttf, core_ttt]

theorem inj4 : ∀ a b c d : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    Function.Injective ![a, b, c, d] := by
  intro a b c d hab hac had hbc hbd hcd x y hxy
  fin_cases x <;> fin_cases y <;> simp_all [eq_comm]

theorem v4 {α : Type} (l : Fin 4 → α) : ![l 0, l 1, l 2, l 3] = l := by
  funext i
  fin_cases i <;> rfl

theorem cntc (l : Fin 4 → Bool) : (Finset.univ.filter (fun i => l i = true)).card = cnt l := by
  rw [Finset.card_filter, Fin.sum_univ_four]
  simp only [cnt]
  generalize l 0 = b0
  generalize l 1 = b1
  generalize l 2 = b2
  generalize l 3 = b3
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;> rfl

theorem hb : ∀ a b c d : Bool,
    bitB (Bool.xor (Bool.xor a b) (Bool.xor c d)) = bitB a + bitB b + bitB c + bitB d := by
  decide

end PEqualNP.Outside.L_meta_25746

open PEqualNP.Outside.L_meta_25746 in
theorem PEqualNP.Outside.L_meta_25746 : ∀ (G : Fin 4 → Fin 4 → Bool) (u t : ℕ),
  let bit := fun (i j : Fin 4) => (if G i j then 1 else 0 : ZMod 2)
  let anchored : Matrix (Fin 3) (Fin 3) (ZMod 2) := fun i j =>
    bit i.succ j.succ + bit i.succ 0 + bit 0 j.succ + bit 0 0
  let total := ∑ i : Fin 4, ∑ j : Fin 4, bit i j
  let cost : ℕ := if u = 0 ∨ (u = 1 ∧ total = 0) then 1 else 0
  anchored.det ≠ 0 →
  ((∃ (π : Equiv.Perm (Fin 4)) (K L : Finset (Fin 4)),
    L ⊆ K ∧ L.card ≤ u ∧ 4 ≤ K.card + t ∧
    ∀ i ∈ K, ∀ j ∈ K,
      Bool.xor (Bool.xor (G i (π i)) (G j (π j))) (Bool.xor (G i (π j)) (G j (π i))) =
      Bool.xor (decide (i ∈ L)) (decide (j ∈ L))) ↔ cost ≤ t) := by
  intro G u t
  dsimp only
  intro hdet
  obtain ⟨N, hNdef⟩ : ∃ N : Fin 4 → Fin 4 → Bool,
      N = fun i j => Bool.xor (Bool.xor (G i j) (G i 0)) (Bool.xor (G 0 j) (G 0 0)) := ⟨_, rfl⟩
  have hr : ∀ j, N 0 j = false := by
    intro j
    rw [hNdef]
    exact Bool.xor_self _
  have hc0 : ∀ i, N i 0 = false := by
    intro i
    rw [hNdef]
    simp only [Bool.xor_self]
  have hmk : mk (N 1 1) (N 1 2) (N 1 3) (N 2 1) (N 2 2) (N 2 3) (N 3 1) (N 3 2) (N 3 3) = N := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [mk, hr, hc0]
  have hcore : Core N := hmk ▸ core_all _ _ _ _ _ _ _ _ _
  have hanch : anch N = anch G := by
    funext i j
    simp only [anch, hNdef]
    generalize G i.succ j.succ = x1
    generalize G i.succ 0 = x2
    generalize G 0 j.succ = x3
    generalize G 0 0 = x4
    revert x1 x2 x3 x4
    decide
  have hdetN : detE N ≠ 0 := by
    have h1 : Matrix.det (anch N) = detE N := by rw [Matrix.det_fin_three]; rfl
    rw [← h1, hanch]
    exact hdet
  have htot : tot N = tot G := by
    have h4 : ∀ x : ZMod 2, (4 : ℕ) • x = 0 := by decide
    simp only [tot, hNdef, hb, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, h4, add_zero]
  have htotal : tot N = ∑ i : Fin 4, ∑ j : Fin 4, (if G i j then (1 : ZMod 2) else 0) := htot
  have hq : ∀ (f : Fin 4 → Fin 4) (i j : Fin 4), quad N f i j = quad G f i j := by
    intro f i j
    simp only [quad, hNdef]
    generalize G i (f i) = x1
    generalize G j (f j) = x2
    generalize G i (f j) = x3
    generalize G j (f i) = x4
    generalize G i 0 = x5
    generalize G j 0 = x6
    generalize G 0 (f i) = x7
    generalize G 0 (f j) = x8
    generalize G 0 0 = x9
    revert x1 x2 x3 x4 x5 x6 x7 x8 x9
    decide
  obtain ⟨E3, E4, I4⟩ := hcore hdetN
  constructor
  · rintro ⟨π, K, L, hLK, hLu, hK, hc⟩
    split_ifs with hcost
    · by_contra ht0
      have ht : t = 0 := by omega
      subst ht
      have hKu : K = Finset.univ := Finset.eq_univ_of_card K (by
        have := Finset.card_le_univ K
        simp only [Fintype.card_fin] at this ⊢
        omega)
      subst hKu
      have hcond : condB N ⇑π (fun _ => true) (fun i => decide (i ∈ L)) := by
        intro i j _ _
        rw [hq]
        exact hc i (Finset.mem_univ _) j (Finset.mem_univ _)
      have hcard : cnt (fun i => decide (i ∈ L)) = L.card := by
        rw [← cntc]
        congr 1
        ext i
        simp
      have := I4 (π 0) (π 1) (π 2) (π 3) (π.injective.ne (by decide)) (π.injective.ne (by decide))
        (π.injective.ne (by decide)) (π.injective.ne (by decide)) (π.injective.ne (by decide))
        (π.injective.ne (by decide)) (decide (0 ∈ L)) (decide (1 ∈ L)) (decide (2 ∈ L))
        (decide (3 ∈ L))
      rw [v4 (⇑π), v4 (fun i => decide (i ∈ L)), hcard] at this
      rcases hcost with hu | ⟨hu, hz⟩
      · have := (this (by omega) hcond).1
        omega
      · have := (this (by omega) hcond).2
        exact this (by rw [htotal]; exact hz)
    · exact Nat.zero_le _
  · intro hct
    by_cases ht : 1 ≤ t
    · obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, k0, k1, k2, k3, hk, hcond⟩ := E3
      have hinj := inj4 a b c d hab hac had hbc hbd hcd
      refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj),
        Finset.univ.filter (fun i => ![k0, k1, k2, k3] i = true), ∅, Finset.empty_subset _,
        by simp, ?_, ?_⟩
      · rw [cntc]
        omega
      · intro i hi j hj
        have h := hcond i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
        rw [hq] at h
        have e : ∀ x : Fin 4, decide (x ∈ (∅ : Finset (Fin 4))) = false := fun x => by simp
        rw [e, e]
        exact h
    · have ht0 : t = 0 := by omega
      subst ht0
      split_ifs at hct with hcost
      · omega
      obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, l0, l1, l2, l3, hl2, hl1, hcond⟩ := E4
      have hinj := inj4 a b c d hab hac had hbc hbd hcd
      refine ⟨Equiv.ofBijective _ (Finite.injective_iff_bijective.mp hinj), Finset.univ,
        Finset.univ.filter (fun i => ![l0, l1, l2, l3] i = true), Finset.subset_univ _, ?_,
        by simp, ?_⟩
      · rw [cntc]
        by_cases hz : tot N = 0
        · have : ¬ (u = 0 ∨ u = 1) := by
            rintro (h | h)
            · exact hcost (Or.inl h)
            · exact hcost (Or.inr ⟨h, by rw [← htotal]; exact hz⟩)
          omega
        · have := hl1 hz
          have : u ≠ 0 := fun h => hcost (Or.inl h)
          omega
      · intro i _ j _
        have h := hcond i j rfl rfl
        rw [hq] at h
        have e : ∀ x : Fin 4, decide (x ∈ Finset.univ.filter (fun i => ![l0, l1, l2, l3] i = true))
            = ![l0, l1, l2, l3] x := fun x => by simp
        rw [e, e]
        exact h
