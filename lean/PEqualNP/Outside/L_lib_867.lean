import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_867

open Finset

theorem shv {l : ℕ} (i : Fin l) (d : ℕ) (hd : d ≤ l) :
    (i.val + d) % l = if i.val + d < l then i.val + d else i.val + d - l := by
  have := i.isLt
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

theorem count1 {l : ℕ} (Mi N S : Fin l → Prop) {_ : DecidablePred Mi} {_ : DecidablePred N}
    {_ : DecidablePred S}
    (σ : Fin l → Fin l) (hσ : Function.Bijective σ)
    (hM : ∀ i, Mi i ↔ ¬ (N i ∨ S i ∨ N (σ i)))
    (x1 : ∀ i, ¬ (N i ∧ S i)) (x2 : ∀ i, ¬ (N i ∧ N (σ i))) (x3 : ∀ i, ¬ (S i ∧ N (σ i))) :
    (univ.filter Mi).card + 2 * (univ.filter N).card + (univ.filter S).card = l := by
  have hN : (univ.filter (fun i => N (σ i))).card = (univ.filter N).card := by
    rw [card_filter, card_filter]
    exact Fintype.sum_bijective σ hσ _ _ (fun _ => rfl)
  have key : (univ.filter Mi).card + (univ.filter N).card + (univ.filter S).card
      + (univ.filter (fun i => N (σ i))).card = l := by
    simp only [card_filter, ← sum_add_distrib]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (by simp : ∑ _i : Fin l, (1 : ℕ) = l)
    have a := hM i
    have b := x1 i
    have c := x2 i
    have d := x3 i
    split_ifs <;> first | rfl | (exfalso; tauto)
  omega

theorem count2 {l : ℕ} (O N : Fin l → Prop) {_ : DecidablePred O} {_ : DecidablePred N}
    (τ : Fin l → Fin l) (hτ : Function.Bijective τ)
    (hO : ∀ i, O i ↔ ¬ N i ∧ ¬ N (τ i)) (x : ∀ i, ¬ (N i ∧ N (τ i))) :
    (univ.filter O).card + 2 * (univ.filter N).card = l := by
  have hN : (univ.filter (fun i => N (τ i))).card = (univ.filter N).card := by
    rw [card_filter, card_filter]
    exact Fintype.sum_bijective τ hτ _ _ (fun _ => rfl)
  have key : (univ.filter O).card + (univ.filter N).card
      + (univ.filter (fun i => N (τ i))).card = l := by
    simp only [card_filter, ← sum_add_distrib]
    refine (Finset.sum_congr rfl (fun i _ => ?_)).trans (by simp : ∑ _i : Fin l, (1 : ℕ) = l)
    have a := hO i
    have b := x i
    split_ifs <;> first | rfl | (exfalso; tauto)
  omega

theorem alt {l : ℕ} (hl : 0 < l) (N : Fin l → Prop)
    (h : ∀ i : Fin l, N ⟨(i.val+1) % l, Nat.mod_lt _ hl⟩ ↔ ¬ N i) :
    l % 2 = 0 ∧ ∃ b : Fin 2, ∀ i : Fin l, N i ↔ i.val % 2 = b.val := by
  classical
  let b : Fin 2 := if N ⟨0, hl⟩ then 0 else 1
  have hb : ∀ n (hn : n < l), N ⟨n, hn⟩ ↔ n % 2 = b.val := by
    intro n
    induction n with
    | zero =>
      intro hn
      by_cases h0 : N ⟨0, hl⟩ <;> simp [b, h0]
    | succ n ih =>
      intro hn
      have e := h ⟨n, by omega⟩
      have e2 : (⟨(n + 1) % l, Nat.mod_lt _ hl⟩ : Fin l) = ⟨n + 1, hn⟩ :=
        Fin.ext (Nat.mod_eq_of_lt hn)
      rw [e2] at e
      rw [e, ih (by omega)]
      have := b.isLt
      constructor <;> intro <;> omega
  refine ⟨?_, b, fun i => hb i.val i.isLt⟩
  by_contra hodd
  have e := h ⟨l - 1, by omega⟩
  have e2 : (⟨(l - 1 + 1) % l, Nat.mod_lt _ hl⟩ : Fin l) = ⟨0, hl⟩ :=
    Fin.ext (by simp [Nat.sub_add_cancel hl])
  rw [e2, hb 0 hl, hb (l - 1) (by omega)] at e
  have e3 : (l - 1) % 2 = 0 % 2 := by omega
  rw [e3] at e
  tauto

end PEqualNP.Outside.L_lib_867

open PEqualNP.Outside.L_lib_867 in
theorem PEqualNP.Outside.L_lib_867 :
∀ (k l : Nat) (hl : 0 < l), 5 ≤ l →
  ∀ (name : Fin l → Fin k), Function.Injective name →
  ∀ p : Equiv.Perm (Fin k), Function.Involutive p →
  let shift := fun (i : Fin l) (d : Nat) => (⟨(i.val+d) % l, Nat.mod_lt _ hl⟩ : Fin l)
  let edge := fun i j : Fin l => p (name i) = name j
  let near := Finset.univ.filter (fun i : Fin l => edge i (shift i 1))
  let skip := Finset.univ.filter (fun i : Fin l => edge i (shift i 2))
  let miss := Finset.univ.filter (fun i : Fin l =>
    ¬ (edge i (shift i 1) ∨ edge i (shift i 2) ∨ edge (shift i 1) (shift i 2)))
  let off := Finset.univ.filter (fun i : Fin l =>
    ¬ edge i (shift i 1) ∧ ¬ edge (shift i (l-1)) i)
  miss.card + 2*near.card + skip.card = l ∧
    miss.card + skip.card = off.card ∧
    (miss.card = 0 ↔ l % 2 = 0 ∧
      ∃ b : Fin 2, ∀ i : Fin l, edge i (shift i 1) ↔ i.val % 2 = b.val) := by
  intro k l hl h5 name hname p hp shift edge near skip miss off
  have esymm : ∀ i j, edge i j → edge j i := by
    intro i j h
    change p (name i) = name j at h
    change p (name j) = name i
    rw [← h]
    exact hp _
  have uniq : ∀ i j j', edge i j → edge i j' → j = j' := by
    intro i j j' h h'
    change p (name i) = name j at h
    change p (name i) = name j' at h'
    exact hname (h.symm.trans h')
  have ss : ∀ (i : Fin l) (a b : ℕ), shift (shift i a) b = shift i (a + b) := by
    intro i a b
    apply Fin.ext
    change ((i.val + a) % l + b) % l = (i.val + (a + b)) % l
    rw [Nat.mod_add_mod, add_assoc]
  have s0 : ∀ i, shift i 0 = i := by
    intro i
    apply Fin.ext
    change (i.val + 0) % l = i.val
    rw [add_zero, Nat.mod_eq_of_lt i.isLt]
  have sl : ∀ i, shift i l = i := by
    intro i
    apply Fin.ext
    change (i.val + l) % l = i.val
    rw [Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  have dist : ∀ (i : Fin l) (a b : ℕ), a < l → b < l → a ≠ b → shift i a ≠ shift i b := by
    intro i a b ha hb hab h
    have h' := congrArg Fin.val h
    change (i.val + a) % l = (i.val + b) % l at h'
    rw [shv i a ha.le, shv i b hb.le] at h'
    have := i.isLt
    split_ifs at h' <;> omega
  have d0 : ∀ i (b : ℕ), 0 < b → b < l → i ≠ shift i b := fun i b h1 h2 h =>
    dist i 0 b (by omega) h2 (by omega) ((s0 i).trans h)
  have s11 : ∀ i, shift (shift i 1) 1 = shift i 2 := fun i => ss i 1 1
  have s12 : ∀ i, shift (shift i 1) 2 = shift i 3 := fun i => ss i 1 2
  have s21 : ∀ i, shift (shift i 2) 1 = shift i 3 := fun i => ss i 2 1
  have s22 : ∀ i, shift (shift i 2) 2 = shift i 4 := fun i => ss i 2 2
  have sm1 : ∀ i, shift (shift i (l - 1)) 1 = i := fun i => by
    rw [ss, Nat.sub_add_cancel hl, sl]
  have hbij : ∀ d, d ≤ l → Function.Bijective (fun i => shift i d) := by
    intro d hd
    have hinv : Function.LeftInverse (fun i => shift i (l - d)) (fun i => shift i d) := by
      intro i
      change shift (shift i d) (l - d) = i
      rw [ss, Nat.add_sub_cancel' hd, sl]
    exact hinv.injective.bijective_of_finite
  have x2 : ∀ i, ¬ (edge i (shift i 1) ∧ edge (shift i 1) (shift (shift i 1) 1)) := by
    rintro i ⟨a, b⟩
    exact d0 i 2 (by omega) (by omega) ((uniq _ _ _ (esymm _ _ a) b).trans (s11 i))
  have c1 : miss.card + 2 * near.card + skip.card = l := by
    refine count1 (fun i => ¬ (edge i (shift i 1) ∨ edge i (shift i 2) ∨
      edge (shift i 1) (shift i 2))) (fun i => edge i (shift i 1)) (fun i => edge i (shift i 2))
      (fun i => shift i 1) (hbij 1 (by omega)) ?_ ?_ x2 ?_
    · intro i
      simp only [s11]
    · rintro i ⟨a, b⟩
      exact dist i 1 2 (by omega) (by omega) (by omega) (uniq _ _ _ a b)
    · rintro i ⟨a, b⟩
      simp only [s11] at b
      exact d0 i 1 (by omega) (by omega) (uniq _ _ _ (esymm _ _ a) (esymm _ _ b))
  have c2 : off.card + 2 * near.card = l := by
    refine count2 (fun i => ¬ edge i (shift i 1) ∧ ¬ edge (shift i (l - 1)) i)
      (fun i => edge i (shift i 1)) (fun i => shift i (l - 1)) (hbij (l - 1) (by omega)) ?_ ?_
    · intro i
      simp only [sm1]
    · rintro i ⟨a, b⟩
      simp only [sm1] at b
      exact dist i 1 (l - 1) (by omega) (by omega) (by omega) (uniq _ _ _ a (esymm _ _ b))
  refine ⟨c1, by omega, ⟨fun h0 => ?_, fun ⟨hev, b, hb⟩ => ?_⟩⟩
  · have nm : ∀ i, edge i (shift i 1) ∨ edge i (shift i 2) ∨ edge (shift i 1) (shift i 2) := by
      intro i
      by_contra hi
      have hmem : i ∈ miss := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
      rw [Finset.card_eq_zero] at h0
      rw [h0] at hmem
      simp at hmem
    have noskip : ∀ i, ¬ edge i (shift i 2) := by
      intro i h
      have n1 := nm (shift i 1)
      rw [s11, s12] at n1
      rcases n1 with a | a | a
      · exact d0 i 1 (by omega) (by omega) (uniq _ _ _ (esymm _ _ h) (esymm _ _ a))
      · have n2 := nm (shift i 2)
        rw [s21, s22] at n2
        rcases n2 with c | c | c
        · exact d0 i 3 (by omega) (by omega) (uniq _ _ _ (esymm _ _ h) c)
        · exact d0 i 4 (by omega) (by omega) (uniq _ _ _ (esymm _ _ h) c)
        · exact dist i 1 4 (by omega) (by omega) (by omega) (uniq _ _ _ (esymm _ _ a) c)
      · exact d0 i 3 (by omega) (by omega) (uniq _ _ _ (esymm _ _ h) a)
    have halt : ∀ i, edge (shift i 1) (shift (shift i 1) 1) ↔ ¬ edge i (shift i 1) := by
      intro i
      constructor
      · intro a b
        exact x2 i ⟨b, a⟩
      · intro hn
        rcases nm i with a | a | a
        · exact absurd a hn
        · exact absurd a (noskip i)
        · rw [s11]
          exact a
    exact alt hl (fun i => edge i (shift i 1)) halt
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i _ hn
    apply hn
    have := b.isLt
    have hi := i.isLt
    by_cases hp0 : i.val % 2 = b.val
    · exact Or.inl ((hb i).mpr hp0)
    · right
      right
      rw [← s11]
      apply (hb (shift i 1)).mpr
      change ((i.val + 1) % l) % 2 = b.val
      rw [shv i 1 (by omega)]
      split_ifs <;> omega
