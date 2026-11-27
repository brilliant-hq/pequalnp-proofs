import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_893

open Finset

theorem z2 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

section
variable {n m : ℕ}

def pol (g : (Fin n → ZMod 2) → (Fin n → ZMod 2)) (x y : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  g (x + y) - g x - g y + g 0

def uv (i : Fin n) : Fin n → ZMod 2 := fun h => if h = i then 1 else 0

def preG (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (a : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (Q : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    Set ((Fin m → ZMod 2) × (Fin n → ZMod 2)) :=
  {s | (s.1, g s.2 - g 0 + a s.1) ∈ Q ∧
    ∀ i : Fin n, ((0 : Fin m → ZMod 2), pol g (uv i) s.2) ∈ Q}

def resp (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (a : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (p : Fin m → ZMod 2) (d b : Fin n → ZMod 2) : (Fin m → ZMod 2) × (Fin n → ZMod 2) :=
  (p, g (b + d) - g b + a p)

def RS (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (a : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (L : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)) where
  carrier := {s | ∀ b, resp g a s.1 s.2 b ∈ L}
  zero_mem' := by
    intro b
    simp [resp]
    exact L.zero_mem
  add_mem' := by
    intro s t hs ht b
    have h := L.add_mem (ht (b + s.2)) (hs b)
    convert h using 1
    simp only [resp, Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk, Prod.mk.injEq]
    constructor
    · abel
    · simp only [add_assoc]
      abel
  smul_mem' := by
    intro c s hs
    rcases z2 c with rfl | rfl
    · intro b
      simp [resp]
      exact L.zero_mem
    · simpa using hs

theorem pol_zero (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hp : ∀ x y z, pol g (x + y) z = pol g x z + pol g y z) (z : Fin n → ZMod 2) :
    pol g 0 z = 0 := by
  have h := hp 0 0 z
  rw [add_zero] at h
  simpa using h

theorem pol_mem (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (hp : ∀ x y z, pol g (x + y) z = pol g x z + pol g y z)
    (L : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2))) (d : Fin n → ZMod 2)
    (hu : ∀ i : Fin n, ((0 : Fin m → ZMod 2), pol g (uv i) d) ∈ L) (b : Fin n → ZMod 2) :
    ((0 : Fin m → ZMod 2), pol g b d) ∈ L := by
  let S : AddSubmonoid (Fin n → ZMod 2) :=
    { carrier := {x | ((0 : Fin m → ZMod 2), pol g x d) ∈ L}
      add_mem' := by
        intro x y hx hy
        have h := L.add_mem hx hy
        show ((0 : Fin m → ZMod 2), pol g (x + y) d) ∈ L
        rw [hp]
        simpa using h
      zero_mem' := by
        show ((0 : Fin m → ZMod 2), pol g 0 d) ∈ L
        rw [pol_zero g hp]
        exact L.zero_mem }
  have hb : b ∈ S := by
    rw [← Finset.univ_sum_single b]
    refine S.sum_mem (fun i _ => ?_)
    rcases z2 (b i) with h | h
    · rw [h, Pi.single_zero]
      exact S.zero_mem
    · have e : Pi.single i (b i) = uv i := by
        funext k
        simp [uv, Pi.single_apply, h]
      rw [e]
      exact hu i
  exact hb

theorem resp_shift (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (a : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (p : Fin m → ZMod 2) (d b : Fin n → ZMod 2) :
    resp g a p d b = resp g a p d 0 + ((0 : Fin m → ZMod 2), pol g b d) := by
  simp only [resp, pol, zero_add, Prod.mk_add_mk, add_zero, Prod.mk.injEq, true_and]
  abel

theorem preG_eq (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (a : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hp : ∀ x y z, pol g (x + y) z = pol g x z + pol g y z)
    (L : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    preG g a (L : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) =
      {s | ∀ b, resp g a s.1 s.2 b ∈ L} := by
  ext ⟨p, d⟩
  simp only [preG, Set.mem_ofPred_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨h0, hu⟩ b
    rw [resp_shift g a p d b]
    refine L.add_mem ?_ (pol_mem g hp L d hu b)
    simpa [resp] using h0
  · intro h
    refine ⟨by simpa [resp] using h 0, fun i => ?_⟩
    have h1 := L.sub_mem (h (uv i)) (h 0)
    rw [resp_shift g a p d (uv i)] at h1
    simpa using h1

open Classical in
theorem half (g : (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (a : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))
    (hp : ∀ x y z, pol g (x + y) z = pol g x z + pol g y z)
    (L : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)))
    (p : Fin m → ZMod 2) (d : Fin n → ZMod 2) (hs : ¬ ∀ b, resp g a p d b ∈ L) :
    2 ^ n ≤ 2 * (univ.filter (fun b => resp g a p d b ∉ L)).card := by
  push Not at hs
  obtain ⟨bs, hbs⟩ := hs
  have hcard : (univ.filter (fun b => resp g a p d b ∈ L)).card +
      (univ.filter (fun b => resp g a p d b ∉ L)).card = 2 ^ n := by
    rw [Finset.card_filter_add_card_filter_not]
    simp
  have hle : (univ.filter (fun b => resp g a p d b ∈ L)).card ≤
      (univ.filter (fun b => resp g a p d b ∉ L)).card := by
    rcases (univ.filter (fun b => resp g a p d b ∈ L)).eq_empty_or_nonempty with he | ⟨b0, hb0⟩
    · rw [he]
      simp
    · simp only [mem_filter, mem_univ, true_and] at hb0
      refine Finset.card_le_card_of_injOn (fun b => b + (bs - b0)) ?_ ?_
      · intro b hb
        simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
          true_and, Set.mem_ofPred_eq] at hb ⊢
        intro hc
        apply hbs
        have h2 := hp (bs - b0) b0 d
        rw [sub_add_cancel] at h2
        have e : resp g a p d bs =
            resp g a p d (b + (bs - b0)) - resp g a p d b + resp g a p d b0 := by
          rw [resp_shift g a p d bs, resp_shift g a p d (b + (bs - b0)),
            resp_shift g a p d b, resp_shift g a p d b0, hp b (bs - b0) d, h2]
          refine Prod.ext ?_ ?_ <;>
            simp only [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub] <;> abel
        rw [e]
        exact L.add_mem (L.sub_mem hc hb) hb0
      · intro x _ y _ hxy
        exact add_right_cancel hxy
  omega

end

def consE (α : Type*) (r : ℕ) : α × (Fin r → α) ≃ (Fin (r + 1) → α) where
  toFun x := Fin.cons x.1 x.2
  invFun f := (f 0, Fin.tail f)
  left_inv x := by simp
  right_inv f := by simp

theorem card_split {α : Type*} [Fintype α] {r : ℕ} (Q : (Fin (r + 1) → α) → Prop) :
    Nat.card {x // Q x} = ∑ b : α, Nat.card {y : Fin r → α // Q (Fin.cons b y)} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  rw [← (consE α r).sum_comp, Fintype.sum_prod_type]
  rfl

theorem key (n r : ℕ) {α : Type*} [Fintype α] (c : α → ℕ) (G : Finset α)
    (hG : 2 ^ n ≤ 2 * G.card) (hc : ∀ b ∈ G, 2 ^ (n * r) ≤ 2 ^ r * c b) :
    2 ^ (n * (r + 1)) ≤ 2 ^ (r + 1) * ∑ b, c b := by
  have h1 : ∑ b ∈ G, c b ≤ ∑ b, c b := Finset.sum_le_sum_of_subset (Finset.subset_univ G)
  have h2 : G.card * 2 ^ (n * r) ≤ 2 ^ r * ∑ b ∈ G, c b := by
    rw [Finset.mul_sum]
    calc G.card * 2 ^ (n * r) = ∑ b ∈ G, 2 ^ (n * r) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ b ∈ G, 2 ^ r * c b := Finset.sum_le_sum hc
  have e1 : 2 ^ (n * (r + 1)) = 2 ^ n * 2 ^ (n * r) := by
    rw [mul_add, mul_one, pow_add, Nat.mul_comm]
  have e2 : 2 ^ (r + 1) = 2 * 2 ^ r := by rw [pow_succ, Nat.mul_comm]
  rw [e1, e2]
  calc 2 ^ n * 2 ^ (n * r) ≤ (2 * G.card) * 2 ^ (n * r) := Nat.mul_le_mul_right _ hG
    _ = 2 * (G.card * 2 ^ (n * r)) := by ring
    _ ≤ 2 * (2 ^ r * ∑ b ∈ G, c b) := Nat.mul_le_mul_left _ h2
    _ ≤ 2 * (2 ^ r * ∑ b, c b) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
    _ = 2 * 2 ^ r * ∑ b, c b := by ring

section
variable {n m : ℕ}

def startG {r : ℕ} (f : Fin r → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin r → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    Set ((Fin m → ZMod 2) × (Fin n → ZMod 2)) :=
  (List.finRange r).foldr (fun j Q => preG (f j) (inject j) Q) target

def finG {r : ℕ} (f : Fin r → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin r → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (p : Fin m → ZMod 2) (d : Fin n → ZMod 2) (base : Fin r → (Fin n → ZMod 2)) :
    Fin n → ZMod 2 :=
  (List.finRange r).foldl (fun v j => f j (base j + v) - f j (base j) + inject j p) d

theorem startG_succ {r : ℕ} (f : Fin (r + 1) → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin (r + 1) → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    startG f inject target = preG (f 0) (inject 0)
      (startG (fun j => f j.succ) (fun j => inject j.succ) target) := by
  simp only [startG, List.finRange_succ, List.foldr_cons, List.foldr_map]

theorem finG_succ {r : ℕ} (f : Fin (r + 1) → (Fin n → ZMod 2) → (Fin n → ZMod 2))
    (inject : Fin (r + 1) → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2)))
    (p : Fin m → ZMod 2) (d : Fin n → ZMod 2) (base : Fin (r + 1) → (Fin n → ZMod 2)) :
    finG f inject p d base = finG (fun j => f j.succ) (fun j => inject j.succ) p
      (f 0 (base 0 + d) - f 0 (base 0) + inject 0 p) (fun j => base j.succ) := by
  simp only [finG, List.finRange_succ, List.foldl_cons, List.foldl_map]

end

theorem main (n m : ℕ) (target : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2))) :
    ∀ (r : ℕ) (f : Fin r → (Fin n → ZMod 2) → (Fin n → ZMod 2))
      (inject : Fin r → ((Fin m → ZMod 2) →ₗ[ZMod 2] (Fin n → ZMod 2))),
      (∀ j x y z, pol (f j) (x + y) z = pol (f j) x z + pol (f j) y z) →
      (∃ L : Submodule (ZMod 2) ((Fin m → ZMod 2) × (Fin n → ZMod 2)),
        (L : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) =
          startG f inject (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2)))) ∧
      ∀ (p : Fin m → ZMod 2) (d : Fin n → ZMod 2),
        ((p, d) ∈ startG f inject (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) ↔
          ∀ base : Fin r → (Fin n → ZMod 2), (p, finG f inject p d base) ∈ target) ∧
        ((p, d) ∉ startG f inject (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) →
          2 ^ (n * r) ≤ 2 ^ r *
            Nat.card {base : Fin r → (Fin n → ZMod 2) // (p, finG f inject p d base) ∉ target}) := by
  intro r
  induction r with
  | zero =>
    intro f inject _
    have hs : startG f inject (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) =
        (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) := by
      simp [startG]
    have hf : ∀ p d base, finG f inject p d base = d := by
      intro p d base
      simp [finG]
    refine ⟨⟨target, hs.symm⟩, fun p d => ⟨?_, ?_⟩⟩
    · rw [hs]
      simp only [hf, SetLike.mem_coe]
      exact ⟨fun h _ => h, fun h => h Fin.elim0⟩
    · intro hnot
      rw [hs] at hnot
      simp only [hf]
      have : Nonempty {base : Fin 0 → (Fin n → ZMod 2) // (p, d) ∉ target} :=
        ⟨⟨Fin.elim0, hnot⟩⟩
      have h1 : 0 < Nat.card {base : Fin 0 → (Fin n → ZMod 2) // (p, d) ∉ target} :=
        Nat.card_pos
      simp only [mul_zero, pow_zero, one_mul]
      exact h1
  | succ r ih =>
    intro f inject hp
    obtain ⟨⟨L', hL'⟩, H'⟩ :=
      ih (fun j => f j.succ) (fun j => inject j.succ) (fun j => hp j.succ)
    have hst : startG f inject (target : Set ((Fin m → ZMod 2) × (Fin n → ZMod 2))) =
        {s | ∀ b, resp (f 0) (inject 0) s.1 s.2 b ∈ L'} := by
      rw [startG_succ, ← hL', preG_eq (f 0) (inject 0) (hp 0) L']
    refine ⟨⟨RS (f 0) (inject 0) L', by rw [hst]; rfl⟩, fun p d => ?_⟩
    have hmem : ∀ b, resp (f 0) (inject 0) p d b ∈ L' ↔
        ∀ base' : Fin r → (Fin n → ZMod 2),
          (p, finG (fun j => f j.succ) (fun j => inject j.succ) p
            (f 0 (b + d) - f 0 b + inject 0 p) base') ∈ target := by
      intro b
      rw [← SetLike.mem_coe, hL']
      exact (H' p _).1
    rw [hst]
    simp only [Set.mem_ofPred_eq]
    constructor
    · refine Iff.trans ?_ Fin.forall_fin_succ_pi.symm
      simp only [finG_succ, Fin.cons_zero, Fin.cons_succ]
      exact forall_congr' hmem
    · intro hnot
      classical
      have hh := half (f 0) (inject 0) (hp 0) L' p d hnot
      rw [card_split (fun base => (p, finG f inject p d base) ∉ target)]
      simp only [finG_succ, Fin.cons_zero, Fin.cons_succ]
      refine key n r _ _ hh ?_
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      have h3 := (H' p (f 0 (b + d) - f 0 b + inject 0 p)).2 (by rw [← hL']; exact hb)
      exact h3

end PEqualNP.Outside.L_lib_893

open PEqualNP.Outside.L_lib_893 in
theorem PEqualNP.Outside.L_lib_893 : ∀ (n m r : ℕ),
  let F := ZMod 2
  let W := Fin n → F
  let P := Fin m → F
  ∀ (f : Fin r → W → W) (inject : Fin r → (P →ₗ[F] W))
    (target : Submodule F (P × W)),
    let polar := fun (j : Fin r) (x y : W) =>
      f j (x+y) - f j x - f j y + f j 0
    (∀ j x y z, polar j (x+y) z = polar j x z + polar j y z) →
    let unit := fun (i h : Fin n) => (if h=i then 1 else 0 : F)
    let pre := fun (j : Fin r) (Q : Set (P × W)) =>
      {s : P × W | (s.1, f j s.2 - f j 0 + inject j s.1) ∈ Q ∧
        ∀ i : Fin n, ((0 : P), polar j (unit i) s.2) ∈ Q}
    let start := (List.finRange r).foldr pre (target : Set (P × W))
    let finish := fun (p : P) (d : W) (base : Fin r → W) =>
      (List.finRange r).foldl (fun (v : W) (j : Fin r) =>
        f j (base j + v) - f j (base j) + inject j p) d
    (∃ L : Submodule F (P × W), (L : Set (P × W)) = start) ∧
    ∀ (p : P) (d : W),
      ((p,d) ∈ start ↔ ∀ base : Fin r → W, (p,finish p d base) ∈ target) ∧
      ((p,d) ∉ start → 2^(n*r) ≤ 2^r *
        Nat.card {base : Fin r → W // (p,finish p d base) ∉ target}) := by
  intro n m r F W P f inject target polar hpol unit pre start finish
  exact main n m target r f inject hpol
