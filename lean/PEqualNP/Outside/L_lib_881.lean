import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_881

open Finset

abbrev X (n : ℕ) := Fin n → ZMod 2

def IsQ {n : ℕ} (g : X n → Bool) : Prop :=
  ∃ (l : X n →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), g = fun x => decide (l x = b)

def Shape (N J : Finset (List Bool)) : Prop :=
  [] ∈ N ∧ J ⊆ N ∧ (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N

def Reach {n : ℕ} (q : List Bool → X n → Bool) (p : List Bool) (x : X n) : Prop :=
  ∀ j : Fin p.length, q (p.take j.val) x = p.get j

theorem zmod2_iff : ∀ a c b : ZMod 2, ((a = b) ↔ (c = b)) ↔ a = c := by decide

theorem isQ_eq {n : ℕ} {g : X n → Bool} (hg : IsQ g) :
    ∃ l : X n →ₗ[ZMod 2] ZMod 2, ∀ x y, g x = g y ↔ l x = l y := by
  obtain ⟨l, b, rfl⟩ := hg
  refine ⟨l, fun x y => ?_⟩
  rw [← zmod2_iff (l x) (l y) b]
  simp only [decide_eq_decide]

/-! ## walks -/

def walk {n : ℕ} (q : List Bool → X n → Bool) (x : X n) : ℕ → List Bool
  | 0 => []
  | k + 1 => walk q x k ++ [q (walk q x k) x]

theorem walk_length {n : ℕ} (q : List Bool → X n → Bool) (x : X n) (k : ℕ) :
    (walk q x k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [walk, ih]

theorem walk_add {n : ℕ} (q : List Bool → X n → Bool) (x : X n) (k s : ℕ) :
    ∃ t, walk q x (k + s) = walk q x k ++ t ∧ t.length = s := by
  induction s with
  | zero => exact ⟨[], by simp, rfl⟩
  | succ s ih =>
    obtain ⟨t, ht, hl⟩ := ih
    refine ⟨t ++ [q (walk q x (k + s)) x], ?_, by simp [hl]⟩
    rw [← Nat.add_assoc, walk, ht, List.append_assoc]

theorem reach_snoc {n : ℕ} (q : List Bool → X n → Bool) (p : List Bool) (b : Bool) (x : X n) :
    Reach q (p ++ [b]) x ↔ Reach q p x ∧ q p x = b := by
  unfold Reach
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have := h ⟨j.val, by simp⟩
      simpa [List.take_append_of_le_length (le_of_lt j.isLt),
        List.getElem_append_left j.isLt] using this
    · have := h ⟨p.length, by simp⟩
      simpa using this
  · rintro ⟨h1, h2⟩ j
    by_cases hj : j.val < p.length
    · have := h1 ⟨j.val, hj⟩
      simpa [List.take_append_of_le_length hj.le, List.getElem_append_left hj] using this
    · have hj2 : j.val = p.length := by
        have := j.isLt
        simp at this
        omega
      simp [hj2, h2]

theorem reach_iff {n : ℕ} (q : List Bool → X n → Bool) (x : X n) :
    ∀ p, Reach q p x ↔ p = walk q x p.length := by
  intro p
  induction p using List.reverseRecOn with
  | nil => simp [Reach, walk]
  | append_singleton p b ih =>
    rw [reach_snoc, ih]
    simp only [List.length_append, List.length_singleton, walk]
    constructor
    · rintro ⟨h1, h2⟩
      rw [← h1, h2]
    · intro h
      obtain ⟨h1, h2⟩ := List.append_inj' h (by simp)
      refine ⟨h1, ?_⟩
      rw [← h1] at h2
      simp only [List.cons.injEq, and_true] at h2
      exact h2.symm

theorem pre {N J : Finset (List Bool)} (hS : Shape N J) :
    ∀ s p, p ++ s ∈ N → p ∈ N ∧ (s ≠ [] → p ∈ J) := by
  intro s
  induction s using List.reverseRecOn with
  | nil => intro p h; simpa using h
  | append_singleton s b ih =>
    intro p h
    rw [← List.append_assoc] at h
    have hJ := hS.2.2.1 _ _ h
    have hN := (ih p (hS.2.1 hJ)).1
    refine ⟨hN, fun _ => ?_⟩
    by_cases hs : s = []
    · subst hs
      simpa using hJ
    · exact (ih p (hS.2.1 hJ)).2 hs

theorem walk_mem {n : ℕ} {N J : Finset (List Bool)} (hS : Shape N J)
    (q : List Bool → X n → Bool) (x : X n) :
    ∀ k, (∀ j < k, walk q x j ∈ J) → walk q x k ∈ N
  | 0 => fun _ => hS.1
  | k + 1 => fun h => by
    obtain ⟨h0, h1⟩ := hS.2.2.2 _ (h k (by omega))
    have key : ∀ b, walk q x k ++ [b] ∈ N := by
      intro b
      cases b
      · exact h0
      · exact h1
    exact key _

theorem exists_leaf {n : ℕ} {N J : Finset (List Bool)} (hS : Shape N J)
    (q : List Bool → X n → Bool) (x : X n) : ∃ k, walk q x k ∈ N \ J := by
  by_contra hne
  push Not at hne
  have hall : ∀ k, walk q x k ∈ J := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      have hN := walk_mem hS q x k (fun j hj => ih j hj)
      by_contra hJ
      exact hne k (Finset.mem_sdiff.2 ⟨hN, hJ⟩)
  have inj : Function.Injective (walk q x) := fun a b h => by
    have := congrArg List.length h
    simpa [walk_length] using this
  exact (Set.infinite_of_injective_forall_mem (s := (J : Set (List Bool))) inj
    (fun k => Finset.mem_coe.2 (hall k))) J.finite_toSet

theorem take_mem_J {N J : Finset (List Bool)} (hS : Shape N J) {p : List Bool} (hp : p ∈ N)
    {j : ℕ} (hj : j < p.length) : p.take j ∈ J := by
  refine (pre hS (p.drop j) (p.take j) (by rw [List.take_append_drop]; exact hp)).2 ?_
  intro h
  rw [List.drop_eq_nil_iff] at h
  omega

/-! ## forward direction -/

theorem fiber {n m : ℕ} {N J : Finset (List Bool)} (hS : Shape N J)
    {q : List Bool → X n → Bool} {out : List Bool → Fin m} {f : X n → Fin m}
    (hc : ∀ p ∈ N \ J, ∀ x, Reach q p x → f x = out p) {a : Fin m} {pa : List Bool}
    (hpa : pa ∈ N \ J) (hout : out pa = a) (huniq : ∀ p ∈ N \ J, out p = a → p = pa) :
    ∀ x, f x = a ↔ Reach q pa x := by
  intro x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := exists_leaf hS q x
    have hr : Reach q (walk q x k) x := by rw [reach_iff, walk_length]
    have := hc _ hk x hr
    rw [huniq _ hk (by rw [← this, hx])] at hr
    exact hr
  · intro hr
    rw [hc _ hpa x hr, hout]

theorem fwd {n m : ℕ} (f : X n → Fin m) (Q : Finset (Fin m))
    (hQ : ∀ a ∈ Q, ∃ x, f x = a) (N J : Finset (List Bool)) (q : List Bool → X n → Bool)
    (out : List Bool → Fin m) (hS : Shape N J) (hq : ∀ p ∈ J, IsQ (q p))
    (hc : ∀ p ∈ N \ J, ∀ x, Reach q p x → f x = out p)
    (hcount : ∀ a ∈ Q, ((N \ J).filter (fun p => out p = a)).card = 1) :
    (∀ a ∈ Q, ∃ (v : X n) (A : Submodule (ZMod 2) (X n)), ∀ x, x - v ∈ A ↔ f x = a) ∧
    ∀ S ⊆ Q, 1 < S.card → ∃ h : X n →ₗ[ZMod 2] ZMod 2,
      (∀ x y : X n, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : X n, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y := by
  have hU : ∀ a ∈ Q, ∃ p, p ∈ N \ J ∧ out p = a ∧ ∀ p' ∈ N \ J, out p' = a → p' = p := by
    intro a ha
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 (hcount a ha)
    have hpm : p ∈ (N \ J).filter (fun p => out p = a) := by rw [hp]; exact mem_singleton_self p
    rw [mem_filter] at hpm
    refine ⟨p, hpm.1, hpm.2, fun p' hp' ho => ?_⟩
    have : p' ∈ (N \ J).filter (fun p => out p = a) := mem_filter.2 ⟨hp', ho⟩
    rw [hp] at this
    exact mem_singleton.1 this
  choose! P hP using hU
  have hfib : ∀ a ∈ Q, ∀ x, f x = a ↔ Reach q (P a) x := fun a ha =>
    fiber hS hc (hP a ha).1 (hP a ha).2.1 (hP a ha).2.2
  have hPN : ∀ a ∈ Q, P a ∈ N := fun a ha => (mem_sdiff.1 (hP a ha).1).1
  have hPJ : ∀ a ∈ Q, P a ∉ J := fun a ha => (mem_sdiff.1 (hP a ha).1).2
  refine ⟨fun a ha => ?_, fun S hSQ hcard => ?_⟩
  · obtain ⟨v, hv⟩ := hQ a ha
    have hvr := (hfib a ha v).1 hv
    choose L hL using fun j : Fin (P a).length =>
      isQ_eq (hq _ (take_mem_J hS (hPN a ha) j.isLt))
    refine ⟨v, ⨅ j, LinearMap.ker (L j), fun x => ?_⟩
    rw [hfib a ha x, Submodule.mem_iInf]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    unfold Reach
    refine forall_congr' fun j => ?_
    rw [← hL j x v, hvr j]
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 hcard
    have Pab : P a ≠ P b := by
      intro h
      apply hab
      rw [← (hP a (hSQ ha)).2.1, ← (hP b (hSQ hb)).2.1, h]
    have hD : ∃ k, ∃ c ∈ S, ∃ d ∈ S, (P c).take k ≠ (P d).take k :=
      ⟨(P a).length + (P b).length, a, ha, b, hb, by
        rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        exact Pab⟩
    classical
    have hk0 : Nat.find hD ≠ 0 := by
      intro h
      have := Nat.find_spec hD
      rw [h] at this
      obtain ⟨c, _, d, _, hcd⟩ := this
      simp at hcd
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hnD := Nat.find_min hD (show k < Nat.find hD by omega)
    have hDk1 := Nat.find_spec hD
    rw [hk] at hDk1
    push Not at hnD
    have hlen : ∀ c ∈ S, k < (P c).length := by
      intro c hc
      by_contra hle
      push Not at hle
      have hpre : ∀ d ∈ S, P d = P c := by
        intro d hd
        have e : (P d).take k = P c := by rw [hnD d hd c hc, List.take_of_length_le hle]
        have hsplit : P c ++ (P d).drop k = P d := by rw [← e, List.take_append_drop]
        by_contra hne
        have hdrop : (P d).drop k ≠ [] := by
          intro h0
          rw [h0, List.append_nil] at hsplit
          exact hne hsplit.symm
        have hmem : P c ++ (P d).drop k ∈ N := by rw [hsplit]; exact hPN d (hSQ hd)
        exact hPJ c (hSQ hc) ((pre hS _ (P c) hmem).2 hdrop)
      obtain ⟨c', hc', d', hd', hcd⟩ := hDk1
      exact hcd (by rw [hpre c' hc', hpre d' hd'])
    obtain ⟨c, hc, d, hd, hcd⟩ := hDk1
    have hLJ : (P c).take k ∈ J := take_mem_J hS (hPN c (hSQ hc)) (hlen c hc)
    obtain ⟨l, hl⟩ := isQ_eq (hq _ hLJ)
    refine ⟨l, ?_, ?_⟩
    · intro x y hx hxy
      have rx := (hfib _ (hSQ hx) x).1 rfl
      have ry := (hfib _ (hSQ hx) y).1 hxy.symm
      have e := hnD _ hx c hc
      rw [← hl]
      have h1 := rx ⟨k, hlen _ hx⟩
      have h2 := ry ⟨k, hlen _ hx⟩
      dsimp only at h1 h2
      rw [e] at h1 h2
      exact h1.trans h2.symm
    · obtain ⟨x, hx⟩ := hQ c (hSQ hc)
      obtain ⟨y, hy⟩ := hQ d (hSQ hd)
      refine ⟨x, y, by rw [hx]; exact hc, by rw [hy]; exact hd, ?_⟩
      rw [Ne, ← hl]
      have rx := (hfib c (hSQ hc) x).1 hx
      have ry := (hfib d (hSQ hd) y).1 hy
      have h1 := rx ⟨k, hlen c hc⟩
      have h2 := ry ⟨k, hlen d hd⟩
      dsimp only at h1 h2
      rw [← hnD c hc d hd] at h2
      rw [h1, h2]
      intro heq
      apply hcd
      rw [List.take_add_one, List.take_add_one, List.getElem?_eq_getElem (hlen c hc),
        List.getElem?_eq_getElem (hlen d hd), hnD c hc d hd]
      simp only [List.get_eq_getElem] at heq
      rw [heq]

/-! ## trees as prefix-closed sets of paths -/

section trees
variable {n m : ℕ}

def nodeN (N0 N1 : Finset (List Bool)) : Finset (List Bool) :=
  insert [] (N0.image (List.cons false) ∪ N1.image (List.cons true))

def nodeQ (r : X n → Bool) (q0 q1 : List Bool → X n → Bool) : List Bool → X n → Bool
  | [] => r
  | false :: p => q0 p
  | true :: p => q1 p

def nodeO (o0 o1 : List Bool → Fin m) : List Bool → Fin m
  | [] => o0 []
  | false :: p => o0 p
  | true :: p => o1 p

@[simp] theorem nil_nodeN (N0 N1 : Finset (List Bool)) : [] ∈ nodeN N0 N1 := by simp [nodeN]
@[simp] theorem f_nodeN (N0 N1 : Finset (List Bool)) (p : List Bool) :
    false :: p ∈ nodeN N0 N1 ↔ p ∈ N0 := by simp [nodeN]
@[simp] theorem t_nodeN (N0 N1 : Finset (List Bool)) (p : List Bool) :
    true :: p ∈ nodeN N0 N1 ↔ p ∈ N1 := by simp [nodeN]

theorem shape_leaf : Shape {[]} ∅ :=
  ⟨by simp, by simp, fun p b h => by simp at h, fun p h => by simp at h⟩

theorem shape_node {N0 J0 N1 J1 : Finset (List Bool)} (h0 : Shape N0 J0) (h1 : Shape N1 J1) :
    Shape (nodeN N0 N1) (nodeN J0 J1) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro p hp
    rcases p with _ | ⟨_ | _, p⟩
    · simp
    · simp only [f_nodeN] at hp ⊢
      exact h0.2.1 hp
    · simp only [t_nodeN] at hp ⊢
      exact h1.2.1 hp
  · intro p b h
    rcases p with _ | ⟨_ | _, p⟩
    · simp
    · simp only [List.cons_append, f_nodeN] at h ⊢
      exact h0.2.2.1 p b h
    · simp only [List.cons_append, t_nodeN] at h ⊢
      exact h1.2.2.1 p b h
  · intro p hp
    rcases p with _ | ⟨_ | _, p⟩
    · exact ⟨(f_nodeN _ _ _).2 h0.1, (t_nodeN _ _ _).2 h1.1⟩
    · simp only [f_nodeN] at hp
      simpa using h0.2.2.2 p hp
    · simp only [t_nodeN] at hp
      simpa using h1.2.2.2 p hp

theorem q_node {J0 J1 : Finset (List Bool)} {r : X n → Bool} {q0 q1 : List Bool → X n → Bool}
    (hr : IsQ r) (h0 : ∀ p ∈ J0, IsQ (q0 p)) (h1 : ∀ p ∈ J1, IsQ (q1 p)) :
    ∀ p ∈ nodeN J0 J1, IsQ (nodeQ r q0 q1 p) := by
  intro p hp
  rcases p with _ | ⟨_ | _, p⟩
  · exact hr
  · exact h0 p (by simpa using hp)
  · exact h1 p (by simpa using hp)

theorem reach_cons (Q : List Bool → X n → Bool) (b : Bool) (p : List Bool) (x : X n) :
    Reach Q (b :: p) x ↔ Q [] x = b ∧ Reach (fun p' => Q (b :: p')) p x := by
  unfold Reach
  constructor
  · intro h
    refine ⟨by simpa using h ⟨0, by simp⟩, fun j => ?_⟩
    have := h ⟨j.val + 1, by simp⟩
    simpa using this
  · rintro ⟨h0, h1⟩ j
    rcases j with ⟨_ | j, hj⟩
    · simpa using h0
    · have := h1 ⟨j, by simpa using hj⟩
      simpa using this

theorem correct_node {f : X n → Fin m} {C : Finset (X n)} {N0 J0 N1 J1 : Finset (List Bool)}
    {r : X n → Bool} {q0 q1 : List Bool → X n → Bool} {o0 o1 : List Bool → Fin m}
    (h0 : ∀ p ∈ N0 \ J0, ∀ x ∈ C.filter (fun z => r z = false), Reach q0 p x → f x = o0 p)
    (h1 : ∀ p ∈ N1 \ J1, ∀ x ∈ C.filter (fun z => r z = true), Reach q1 p x → f x = o1 p) :
    ∀ p ∈ nodeN N0 N1 \ nodeN J0 J1, ∀ x ∈ C, Reach (nodeQ r q0 q1) p x →
      f x = nodeO o0 o1 p := by
  intro p hp x hx hr
  rw [mem_sdiff] at hp
  rcases p with _ | ⟨_ | _, p⟩
  · exact absurd (nil_nodeN _ _) hp.2
  · rw [reach_cons] at hr
    obtain ⟨hr0, hr1⟩ := hr
    simp only [f_nodeN] at hp
    exact h0 p (mem_sdiff.2 hp) x (mem_filter.2 ⟨hx, hr0⟩) hr1
  · rw [reach_cons] at hr
    obtain ⟨hr0, hr1⟩ := hr
    simp only [t_nodeN] at hp
    exact h1 p (mem_sdiff.2 hp) x (mem_filter.2 ⟨hx, hr0⟩) hr1

theorem count_node {N0 J0 N1 J1 : Finset (List Bool)} {o0 o1 : List Bool → Fin m} (a : Fin m) :
    ((nodeN N0 N1 \ nodeN J0 J1).filter (fun p => nodeO o0 o1 p = a)).card =
      ((N0 \ J0).filter (fun p => o0 p = a)).card + ((N1 \ J1).filter (fun p => o1 p = a)).card := by
  have e : (nodeN N0 N1 \ nodeN J0 J1).filter (fun p => nodeO o0 o1 p = a) =
      ((N0 \ J0).filter (fun p => o0 p = a)).image (List.cons false) ∪
      ((N1 \ J1).filter (fun p => o1 p = a)).image (List.cons true) := by
    ext p
    rcases p with _ | ⟨_ | _, p⟩
    · simp
    · simp only [mem_filter, mem_sdiff, f_nodeN, mem_union, mem_image]
      simp [nodeO]
    · simp only [mem_filter, mem_sdiff, t_nodeN, mem_union, mem_image]
      simp [nodeO]
  rw [e, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (List.cons_injective),
    Finset.card_image_of_injective _ (List.cons_injective)]
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  simp only [Finset.mem_image] at hp1 hp2
  obtain ⟨u, -, rfl⟩ := hp1
  obtain ⟨w, -, hw⟩ := hp2
  simp at hw

end trees

/-! ## construction -/

def Closed {n m : ℕ} (f : X n → Fin m) (Q : Finset (Fin m)) (C : Finset (X n)) : Prop :=
  ∀ a ∈ Q, ∀ x y, f x = a → f y = a → x ∈ C → y ∈ C

def Spec {n m : ℕ} (f : X n → Fin m) (Q : Finset (Fin m)) (C : Finset (X n))
    (N J : Finset (List Bool)) (q : List Bool → X n → Bool) (out : List Bool → Fin m) : Prop :=
  Shape N J ∧ (∀ p ∈ J, IsQ (q p)) ∧ (∀ p ∈ N \ J, ∀ x ∈ C, Reach q p x → f x = out p) ∧
    (∀ a ∈ Q, (∃ x ∈ C, f x = a) → ((N \ J).filter (fun p => out p = a)).card = 1) ∧
    ∀ a ∈ Q, (¬ ∃ x ∈ C, f x = a) → ((N \ J).filter (fun p => out p = a)).card = 0

theorem combine {n m : ℕ} {f : X n → Fin m} {Q : Finset (Fin m)} {C : Finset (X n)}
    (r : X n → Bool) (hr : IsQ r)
    (hcon : ∀ z ∈ C, ∀ w ∈ C, f z = f w → f z ∈ Q → r z = r w)
    {N0 J0 N1 J1 : Finset (List Bool)} {q0 q1 : List Bool → X n → Bool}
    {o0 o1 : List Bool → Fin m}
    (h0 : Spec f Q (C.filter (fun z => r z = false)) N0 J0 q0 o0)
    (h1 : Spec f Q (C.filter (fun z => r z = true)) N1 J1 q1 o1) :
    Spec f Q C (nodeN N0 N1) (nodeN J0 J1) (nodeQ r q0 q1) (nodeO o0 o1) := by
  refine ⟨shape_node h0.1 h1.1, q_node hr h0.2.1 h1.2.1, correct_node h0.2.2.1 h1.2.2.1,
    fun a ha hex => ?_, fun a ha hex => ?_⟩
  · obtain ⟨x, hxC, hxa⟩ := hex
    rw [count_node]
    cases hrx : r x
    · rw [h0.2.2.2.1 a ha ⟨x, mem_filter.2 ⟨hxC, hrx⟩, hxa⟩, h1.2.2.2.2 a ha ?_]
      rintro ⟨y, hy, hya⟩
      rw [mem_filter] at hy
      have := hcon y hy.1 x hxC (hya.trans hxa.symm) (by rw [hya]; exact ha)
      rw [hy.2, hrx] at this
      exact Bool.noConfusion this
    · rw [h1.2.2.2.1 a ha ⟨x, mem_filter.2 ⟨hxC, hrx⟩, hxa⟩, h0.2.2.2.2 a ha ?_]
      rintro ⟨y, hy, hya⟩
      rw [mem_filter] at hy
      have := hcon y hy.1 x hxC (hya.trans hxa.symm) (by rw [hya]; exact ha)
      rw [hy.2, hrx] at this
      exact Bool.noConfusion this
  · rw [count_node, h0.2.2.2.2 a ha ?_, h1.2.2.2.2 a ha ?_]
    · rintro ⟨y, hy, hya⟩
      exact hex ⟨y, (mem_filter.1 hy).1, hya⟩
    · rintro ⟨y, hy, hya⟩
      exact hex ⟨y, (mem_filter.1 hy).1, hya⟩

theorem zmod2_ne : ∀ a b : ZMod 2, a ≠ b → (a = 1 ∧ b ≠ 1) ∨ (a ≠ 1 ∧ b = 1) := by decide


theorem split_exists {n m : ℕ} (f : X n → Fin m) (Q : Finset (Fin m))
    (H1 : ∀ a ∈ Q, ∃ (v : X n) (A : Submodule (ZMod 2) (X n)), ∀ x, x - v ∈ A ↔ f x = a)
    (H2 : ∀ S ⊆ Q, 1 < S.card → ∃ h : X n →ₗ[ZMod 2] ZMod 2,
      (∀ x y : X n, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : X n, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y)
    {C : Finset (X n)} (hcl : Closed f Q C) {x y : X n} (hx : x ∈ C) (hy : y ∈ C)
    (hxy : f x ≠ f y) :
    ∃ r : X n → Bool, IsQ r ∧ (∃ z ∈ C, r z = false) ∧ (∃ z ∈ C, r z = true) ∧
      ∀ z ∈ C, ∀ w ∈ C, f z = f w → f z ∈ Q → r z = r w := by
  classical
  set S := Q.filter (fun a => ∃ z ∈ C, f z = a) with hSdef
  have memS : ∀ z ∈ C, f z ∈ Q → f z ∈ S := fun z hz hq => mem_filter.2 ⟨hq, z, hz, rfl⟩
  have Sfib : ∀ a ∈ S, ∀ w, f w = a → w ∈ C := by
    intro a ha w hw
    obtain ⟨haQ, z, hz, hza⟩ := mem_filter.1 ha
    exact hcl a haQ z w hza hw hz
  rcases lt_or_ge 1 S.card with h2 | h1
  · obtain ⟨h, hconst, u, w, hu, hw, huw⟩ := H2 S (filter_subset _ _) h2
    refine ⟨fun z => decide (h z = 1), ⟨h, 1, rfl⟩, ?_⟩
    have huC := Sfib _ hu u rfl
    have hwC := Sfib _ hw w rfl
    have key : ∀ z ∈ C, ∀ w ∈ C, f z = f w → f z ∈ Q →
        decide (h z = 1) = decide (h w = 1) := by
      intro z hz w' _ hzw hq
      rw [hconst z w' (memS z hz hq) hzw]
    rcases zmod2_ne _ _ huw with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨⟨w, hwC, by simp [e2]⟩, ⟨u, huC, by simp [e1]⟩, key⟩
    · exact ⟨⟨u, huC, by simp [e1]⟩, ⟨w, hwC, by simp [e2]⟩, key⟩
  · rcases S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩
    · have hne : x ≠ y := fun h => hxy (by rw [h])
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
      refine ⟨fun z => decide (LinearMap.proj (R := ZMod 2) (φ := fun _ : Fin n => ZMod 2) i z = x i),
        ⟨LinearMap.proj i, x i, rfl⟩, ⟨y, hy, by simp [Ne.symm hi]⟩, ⟨x, hx, by simp⟩, ?_⟩
      intro z hz w _ _ hq
      have := memS z hz hq
      rw [hS0] at this
      simp at this
    · have hone : ∀ b ∈ S, b = a := fun b hb => Finset.card_le_one.1 h1 b hb a ha
      have haQ : a ∈ Q := (mem_filter.1 ha).1
      obtain ⟨y', hy'C, hy'a⟩ : ∃ y' ∈ C, f y' ≠ a := by
        by_cases hxa : f x = a
        · exact ⟨y, hy, fun h => hxy (hxa.trans h.symm)⟩
        · exact ⟨x, hx, hxa⟩
      obtain ⟨v, A, hA⟩ := H1 a haQ
      have hv : f v = a := (hA v).1 (by simp)
      have hvC := Sfib a ha v hv
      have hnot : y' - v ∉ A := fun h => hy'a ((hA y').1 h)
      obtain ⟨l, hl0, hlA⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
      have hlz : ∀ z, f z = a → l z = l v := by
        intro z hz
        have hm : l (z - v) ∈ A.map l := Submodule.mem_map_of_mem ((hA z).2 hz)
        rw [hlA, Submodule.mem_bot, map_sub, sub_eq_zero] at hm
        exact hm
      refine ⟨fun z => decide (l z = l v), ⟨l, l v, rfl⟩, ⟨y', hy'C, ?_⟩, ⟨v, hvC, by simp⟩, ?_⟩
      · rw [map_sub, Ne, sub_eq_zero] at hl0
        simp [hl0]
      · intro z hz w _ hzw hq
        have hza := hone _ (memS z hz hq)
        dsimp only
        rw [hlz z hza, hlz w (hzw.symm.trans hza)]


theorem build {n m : ℕ} (f : X n → Fin m) (Q : Finset (Fin m))
    (H1 : ∀ a ∈ Q, ∃ (v : X n) (A : Submodule (ZMod 2) (X n)), ∀ x, x - v ∈ A ↔ f x = a)
    (H2 : ∀ S ⊆ Q, 1 < S.card → ∃ h : X n →ₗ[ZMod 2] ZMod 2,
      (∀ x y : X n, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : X n, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y) :
    ∀ k, ∀ C : Finset (X n), C.card ≤ k → C.Nonempty → Closed f Q C →
      ∃ N J q out, Spec f Q C N J q out := by
  intro k
  induction k with
  | zero =>
    intro C hk hne _
    have := Finset.card_pos.2 hne
    omega
  | succ k ih =>
    intro C hk hne hcl
    by_cases hall : ∃ x ∈ C, ∃ y ∈ C, f x ≠ f y
    · obtain ⟨x, hx, y, hy, hxy⟩ := hall
      obtain ⟨r, hr, ⟨z0, hz0, hr0⟩, ⟨z1, hz1, hr1⟩, hcon⟩ := split_exists f Q H1 H2 hcl hx hy hxy
      have side : ∀ b : Bool, (∃ z ∈ C, r z = b) → (∃ z ∈ C, r z ≠ b) →
          ∃ N J q out, Spec f Q (C.filter (fun z => r z = b)) N J q out := by
        intro b ⟨z, hz, hzb⟩ ⟨z', hz', hz'b⟩
        refine ih _ ?_ ⟨z, mem_filter.2 ⟨hz, hzb⟩⟩ ?_
        · have := Finset.card_lt_card
            ((Finset.filter_ssubset (p := fun z => r z = b)).2 ⟨z', hz', hz'b⟩)
          omega
        · intro a ha u w hu hw huC
          rw [mem_filter] at huC ⊢
          have hwC := hcl a ha u w hu hw huC.1
          refine ⟨hwC, ?_⟩
          rw [← hcon u huC.1 w hwC (hu.trans hw.symm) (by rw [hu]; exact ha)]
          exact huC.2
      obtain ⟨N0, J0, q0, o0, ht0⟩ := side false ⟨z0, hz0, hr0⟩ ⟨z1, hz1, by rw [hr1]; decide⟩
      obtain ⟨N1, J1, q1, o1, ht1⟩ := side true ⟨z1, hz1, hr1⟩ ⟨z0, hz0, by rw [hr0]; decide⟩
      exact ⟨_, _, _, _, combine r hr hcon ht0 ht1⟩
    · push Not at hall
      obtain ⟨x0, hx0⟩ := hne
      refine ⟨{[]}, ∅, fun _ _ => false, fun _ => f x0, shape_leaf, fun p hp => by simp at hp,
        fun p _ x hx _ => (hall x0 hx0 x hx).symm, fun a _ hex => ?_, fun a _ hex => ?_⟩
      · obtain ⟨x, hx, hxa⟩ := hex
        rw [sdiff_empty, Finset.filter_singleton, if_pos ((hall x0 hx0 x hx).trans hxa),
          card_singleton]
      · rw [sdiff_empty, Finset.filter_singleton, if_neg (fun h => hex ⟨x0, hx0, h⟩), card_empty]

theorem bwd {n m : ℕ} (f : X n → Fin m) (Q : Finset (Fin m))
    (hQ : ∀ a ∈ Q, ∃ x, f x = a)
    (H1 : ∀ a ∈ Q, ∃ (v : X n) (A : Submodule (ZMod 2) (X n)), ∀ x, x - v ∈ A ↔ f x = a)
    (H2 : ∀ S ⊆ Q, 1 < S.card → ∃ h : X n →ₗ[ZMod 2] ZMod 2,
      (∀ x y : X n, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : X n, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y) :
    ∃ (N J : Finset (List Bool)) (q : List Bool → X n → Bool) (out : List Bool → Fin m),
      (Shape N J ∧ (∀ p ∈ J, IsQ (q p)) ∧ ∀ p ∈ N \ J, ∀ x, Reach q p x → f x = out p) ∧
      ∀ a ∈ Q, ((N \ J).filter (fun p => out p = a)).card = 1 := by
  obtain ⟨N, J, q, out, ht⟩ := build f Q H1 H2 _ Finset.univ le_rfl Finset.univ_nonempty
    (fun _ _ _ _ _ _ _ => mem_univ _)
  refine ⟨N, J, q, out, ⟨ht.1, ht.2.1, fun p hp x hr => ht.2.2.1 p hp x (mem_univ x) hr⟩,
    fun a ha => ?_⟩
  obtain ⟨x, hx⟩ := hQ a ha
  exact ht.2.2.2.1 a ha ⟨x, mem_univ _, hx⟩

end PEqualNP.Outside.L_lib_881

open PEqualNP.Outside.L_lib_881 in
theorem PEqualNP.Outside.L_lib_881 : ∀ (n m : ℕ),
  let X := Fin n → ZMod 2
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  let queries := fun (V : Type) [AddCommGroup V] [Module (ZMod 2) V] =>
    {f : V → Bool | ∃ (l : V →ₗ[ZMod 2] ZMod 2) (b : ZMod 2), f = fun x => decide (l x = b)}
  let cert := fun {V O : Type} (qs : Set (V → Bool)) (ok : V → O → Prop)
      (N J : Finset (List Bool)) (q : List Bool → V → Bool) (out : List Bool → O) =>
    shape N J ∧ (∀ p ∈ J, q p ∈ qs) ∧ ∀ p ∈ N \ J, ∀ x : V,
      (∀ j : Fin p.length, q (p.take j.val) x = p.get j) → ok x (out p)
  ∀ (f : X → Fin m) (Q : Finset (Fin m)) (_ : Q ⊆ Finset.univ.image f),
    (∃ (N J : Finset (List Bool)) (q : List Bool → X → Bool) (out : List Bool → Fin m),
      cert (queries X) (fun x a => f x = a) N J q out ∧
      ∀ a ∈ Q, ((N \ J).filter (fun p => out p = a)).card = 1) ↔
    (∀ a ∈ Q, ∃ (v : X) (A : Submodule (ZMod 2) X), ∀ x, x-v ∈ A ↔ f x = a) ∧
    ∀ S ⊆ Q, 1 < S.card → ∃ h : X →ₗ[ZMod 2] ZMod 2,
      (∀ x y : X, f x ∈ S → f x = f y → h x = h y) ∧
      ∃ x y : X, f x ∈ S ∧ f y ∈ S ∧ h x ≠ h y := by
  intro n m X shape queries cert f Q hQ
  have hQ' : ∀ a ∈ Q, ∃ x, f x = a := by
    intro a ha
    obtain ⟨x, -, hx⟩ := Finset.mem_image.1 (hQ ha)
    exact ⟨x, hx⟩
  constructor
  · rintro ⟨N, J, q, out, ⟨hS, hq, hc⟩, hcount⟩
    exact fwd f Q hQ' N J q out hS hq hc hcount
  · rintro ⟨H1, H2⟩
    obtain ⟨N, J, q, out, ⟨hS, hq, hc⟩, hcount⟩ := bwd f Q hQ' H1 H2
    exact ⟨N, J, q, out, ⟨hS, hq, hc⟩, hcount⟩
