import Mathlib.Init

namespace PEqualNP.Outside.L_lib_1314

def baseBV : List (BitVec 8) := [0,128,192,224,240,248,252,254,255,15,51]

def ok8 (x : BitVec 8) : Prop :=
  (x.getLsbD 0 = true → x.getLsbD 1 = true) ∧
  (x.getLsbD 2 = true → x.getLsbD 3 = true) ∧
  (x.getLsbD 4 = true → x.getLsbD 5 = true) ∧
  (x.getLsbD 6 = true → x.getLsbD 7 = true)

theorem ok8_and {a b : BitVec 8} (ha : ok8 a) (hb : ok8 b) : ok8 (a &&& b) := by
  rcases ha with ⟨a0, a1, a2, a3⟩
  rcases hb with ⟨b0, b1, b2, b3⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    simp only [BitVec.getLsbD_and, Bool.and_eq_true] at h ⊢
  · exact ⟨a0 h.1, b0 h.2⟩
  · exact ⟨a1 h.1, b1 h.2⟩
  · exact ⟨a2 h.1, b2 h.2⟩
  · exact ⟨a3 h.1, b3 h.2⟩

theorem ok8_or {a b : BitVec 8} (ha : ok8 a) (hb : ok8 b) : ok8 (a ||| b) := by
  rcases ha with ⟨a0, a1, a2, a3⟩
  rcases hb with ⟨b0, b1, b2, b3⟩
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;>
    simp only [BitVec.getLsbD_or, Bool.or_eq_true] at h ⊢
  · exact h.elim (fun h => Or.inl (a0 h)) (fun h => Or.inr (b0 h))
  · exact h.elim (fun h => Or.inl (a1 h)) (fun h => Or.inr (b1 h))
  · exact h.elim (fun h => Or.inl (a2 h)) (fun h => Or.inr (b2 h))
  · exact h.elim (fun h => Or.inl (a3 h)) (fun h => Or.inr (b3 h))

theorem ok8_base : ∀ x ∈ baseBV, ok8 x := by
  intro x hx
  simp only [baseBV, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide⟩

def pairCode (lo hi : Bool) : Nat :=
  if lo then 2 else if hi then 1 else 0

def code (x : BitVec 8) : Nat :=
  pairCode (x.getLsbD 0) (x.getLsbD 1) +
  3 * (pairCode (x.getLsbD 2) (x.getLsbD 3) +
  3 * (pairCode (x.getLsbD 4) (x.getLsbD 5) +
  3 * pairCode (x.getLsbD 6) (x.getLsbD 7)))

def cAnd (a b : Nat) : Nat :=
  min (a % 3) (b % 3) +
  3 * (min ((a / 3) % 3) ((b / 3) % 3) +
  3 * (min ((a / 9) % 3) ((b / 9) % 3) +
  3 * min ((a / 27) % 3) ((b / 27) % 3)))

def cOr (a b : Nat) : Nat :=
  max (a % 3) (b % 3) +
  3 * (max ((a / 3) % 3) ((b / 3) % 3) +
  3 * (max ((a / 9) % 3) ((b / 9) % 3) +
  3 * max ((a / 27) % 3) ((b / 27) % 3)))

def sym (c : Nat) : Nat :=
  (2 - (c / 27) % 3) +
  3 * ((2 - (c / 9) % 3) +
  3 * ((2 - (c / 3) % 3) +
  3 * (2 - c % 3)))

def isBase (c : Nat) : Bool :=
  Nat.beq c 0 || Nat.beq c 8 || Nat.beq c 20 || Nat.beq c 27 || Nat.beq c 54 ||
  Nat.beq c 63 || Nat.beq c 72 || Nat.beq c 75 || Nat.beq c 78 || Nat.beq c 79 || Nat.beq c 80

theorem pairCode_lt (lo hi : Bool) : pairCode lo hi < 3 := by
  cases lo <;> cases hi <;> decide

theorem pairCode_and {l1 h1 l2 h2 : Bool}
    (o1 : l1 = true → h1 = true) (o2 : l2 = true → h2 = true) :
    pairCode (l1 && l2) (h1 && h2) = min (pairCode l1 h1) (pairCode l2 h2) := by
  cases l1 <;> cases h1 <;> cases l2 <;> cases h2 <;> simp_all [pairCode]

theorem pairCode_or {l1 h1 l2 h2 : Bool}
    (o1 : l1 = true → h1 = true) (o2 : l2 = true → h2 = true) :
    pairCode (l1 || l2) (h1 || h2) = max (pairCode l1 h1) (pairCode l2 h2) := by
  cases l1 <;> cases h1 <;> cases l2 <;> cases h2 <;> simp_all [pairCode]

theorem code_lt (x : BitVec 8) : code x < 81 := by
  unfold code
  have h0 := pairCode_lt (x.getLsbD 0) (x.getLsbD 1)
  have h1 := pairCode_lt (x.getLsbD 2) (x.getLsbD 3)
  have h2 := pairCode_lt (x.getLsbD 4) (x.getLsbD 5)
  have h3 := pairCode_lt (x.getLsbD 6) (x.getLsbD 7)
  omega

theorem digits_extract (d0 d1 d2 d3 : Nat) (h0 : d0 < 3) (h1 : d1 < 3) (h2 : d2 < 3) (h3 : d3 < 3) :
    let n := d0 + 3 * (d1 + 3 * (d2 + 3 * d3))
    n % 3 = d0 ∧ (n / 3) % 3 = d1 ∧ (n / 9) % 3 = d2 ∧ (n / 27) % 3 = d3 := by
  omega

theorem code_and {a b : BitVec 8} (ha : ok8 a) (hb : ok8 b) :
    code (a &&& b) = cAnd (code a) (code b) := by
  rcases ha with ⟨a0, a1, a2, a3⟩
  rcases hb with ⟨b0, b1, b2, b3⟩
  have ha0 := pairCode_lt (a.getLsbD 0) (a.getLsbD 1)
  have ha1 := pairCode_lt (a.getLsbD 2) (a.getLsbD 3)
  have ha2 := pairCode_lt (a.getLsbD 4) (a.getLsbD 5)
  have ha3 := pairCode_lt (a.getLsbD 6) (a.getLsbD 7)
  have hb0 := pairCode_lt (b.getLsbD 0) (b.getLsbD 1)
  have hb1 := pairCode_lt (b.getLsbD 2) (b.getLsbD 3)
  have hb2 := pairCode_lt (b.getLsbD 4) (b.getLsbD 5)
  have hb3 := pairCode_lt (b.getLsbD 6) (b.getLsbD 7)
  have ea := digits_extract _ _ _ _ ha0 ha1 ha2 ha3
  have eb := digits_extract _ _ _ _ hb0 hb1 hb2 hb3
  unfold code cAnd
  rw [BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and,
      BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and, BitVec.getLsbD_and]
  rw [pairCode_and a0 b0, pairCode_and a1 b1, pairCode_and a2 b2, pairCode_and a3 b3]
  rw [ea.1, ea.2.1, ea.2.2.1, ea.2.2.2, eb.1, eb.2.1, eb.2.2.1, eb.2.2.2]

theorem code_or {a b : BitVec 8} (ha : ok8 a) (hb : ok8 b) :
    code (a ||| b) = cOr (code a) (code b) := by
  rcases ha with ⟨a0, a1, a2, a3⟩
  rcases hb with ⟨b0, b1, b2, b3⟩
  have ha0 := pairCode_lt (a.getLsbD 0) (a.getLsbD 1)
  have ha1 := pairCode_lt (a.getLsbD 2) (a.getLsbD 3)
  have ha2 := pairCode_lt (a.getLsbD 4) (a.getLsbD 5)
  have ha3 := pairCode_lt (a.getLsbD 6) (a.getLsbD 7)
  have hb0 := pairCode_lt (b.getLsbD 0) (b.getLsbD 1)
  have hb1 := pairCode_lt (b.getLsbD 2) (b.getLsbD 3)
  have hb2 := pairCode_lt (b.getLsbD 4) (b.getLsbD 5)
  have hb3 := pairCode_lt (b.getLsbD 6) (b.getLsbD 7)
  have ea := digits_extract _ _ _ _ ha0 ha1 ha2 ha3
  have eb := digits_extract _ _ _ _ hb0 hb1 hb2 hb3
  unfold code cOr
  rw [BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or,
      BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or, BitVec.getLsbD_or]
  rw [pairCode_or a0 b0, pairCode_or a1 b1, pairCode_or a2 b2, pairCode_or a3 b3]
  rw [ea.1, ea.2.1, ea.2.2.1, ea.2.2.2, eb.1, eb.2.1, eb.2.2.1, eb.2.2.2]

theorem isBase_code_base : ∀ x ∈ baseBV, isBase (code x) = true := by
  intro x hx
  simp only [baseBV, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem sym_lt (c : Nat) : sym c < 81 := by
  unfold sym; omega

theorem sym_sym {c : Nat} (hc : c < 81) : sym (sym c) = c := by
  have h : ∀ i : Fin 81, sym (sym i.val) = i.val := by decide
  exact h ⟨c, hc⟩

theorem sym_isBase {c : Nat} (hc : c < 81) : isBase (sym c) = isBase c := by
  have h : ∀ i : Fin 81, isBase (sym i.val) = isBase i.val := by decide
  exact h ⟨c, hc⟩

theorem cAnd_comm (a b : Nat) : cAnd a b = cAnd b a := by
  unfold cAnd; omega

theorem cOr_comm (a b : Nat) : cOr a b = cOr b a := by
  unfold cOr; omega

theorem cAnd_self {a : Nat} (ha : a < 81) : cAnd a a = a := by
  unfold cAnd; omega

theorem cOr_self {a : Nat} (ha : a < 81) : cOr a a = a := by
  unfold cOr; omega

theorem two_sub_min (x y : Nat) (hx : x < 3) (hy : y < 3) :
    2 - min x y = max (2 - x) (2 - y) := by omega

theorem two_sub_max (x y : Nat) (hx : x < 3) (hy : y < 3) :
    2 - max x y = min (2 - x) (2 - y) := by omega

theorem sym_cAnd (a b : Nat) : sym (cAnd a b) = cOr (sym a) (sym b) := by
  have ea := digits_extract (2 - (a / 27) % 3) (2 - (a / 9) % 3) (2 - (a / 3) % 3) (2 - a % 3)
    (by omega) (by omega) (by omega) (by omega)
  have eb := digits_extract (2 - (b / 27) % 3) (2 - (b / 9) % 3) (2 - (b / 3) % 3) (2 - b % 3)
    (by omega) (by omega) (by omega) (by omega)
  have ec := digits_extract (min (a % 3) (b % 3)) (min ((a / 3) % 3) ((b / 3) % 3))
    (min ((a / 9) % 3) ((b / 9) % 3)) (min ((a / 27) % 3) ((b / 27) % 3))
    (by omega) (by omega) (by omega) (by omega)
  unfold sym cAnd cOr
  rw [ec.1, ec.2.1, ec.2.2.1, ec.2.2.2,
      ea.1, ea.2.1, ea.2.2.1, ea.2.2.2,
      eb.1, eb.2.1, eb.2.2.1, eb.2.2.2]
  rw [two_sub_min _ _ (by omega) (by omega), two_sub_min _ _ (by omega) (by omega),
      two_sub_min _ _ (by omega) (by omega), two_sub_min _ _ (by omega) (by omega)]

theorem sym_cOr (a b : Nat) : sym (cOr a b) = cAnd (sym a) (sym b) := by
  have ea := digits_extract (2 - (a / 27) % 3) (2 - (a / 9) % 3) (2 - (a / 3) % 3) (2 - a % 3)
    (by omega) (by omega) (by omega) (by omega)
  have eb := digits_extract (2 - (b / 27) % 3) (2 - (b / 9) % 3) (2 - (b / 3) % 3) (2 - b % 3)
    (by omega) (by omega) (by omega) (by omega)
  have ec := digits_extract (max (a % 3) (b % 3)) (max ((a / 3) % 3) ((b / 3) % 3))
    (max ((a / 9) % 3) ((b / 9) % 3)) (max ((a / 27) % 3) ((b / 27) % 3))
    (by omega) (by omega) (by omega) (by omega)
  unfold sym cAnd cOr
  rw [ec.1, ec.2.1, ec.2.2.1, ec.2.2.2,
      ea.1, ea.2.1, ea.2.2.1, ea.2.2.2,
      eb.1, eb.2.1, eb.2.2.1, eb.2.2.2]
  rw [two_sub_max _ _ (by omega) (by omega), two_sub_max _ _ (by omega) (by omega),
      two_sub_max _ _ (by omega) (by omega), two_sub_max _ _ (by omega) (by omega)]

def ValidSeq (w : List Nat) : Prop :=
  (∀ x ∈ w, x < 81) ∧
  ∀ p v q, w = p ++ v :: q →
    ∃ a b, a < 81 ∧ b < 81 ∧
      (isBase a = true ∨ a ∈ p) ∧
      (isBase b = true ∨ b ∈ p) ∧
      (v = cAnd a b ∨ v = cOr a b)

theorem validSeq_prefix {p : List Nat} {v : Nat} (h : ValidSeq (p ++ [v])) : ValidSeq p := by
  refine ⟨fun x hx => h.1 x (List.mem_append_left _ hx), ?_⟩
  intro p1 v1 q1 heq
  have hw : p ++ [v] = p1 ++ v1 :: (q1 ++ [v]) := by
    rw [heq]; simp [List.append_assoc]
  exact h.2 p1 v1 (q1 ++ [v]) hw

theorem validSeq_map_sym {w : List Nat} (h : ValidSeq w) : ValidSeq (w.map sym) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
    exact sym_lt y
  · intro p' v' q' heq
    rcases List.map_eq_append_iff.mp heq with ⟨p, r, hw, hp, hr⟩
    rcases List.map_eq_cons_iff.mp hr with ⟨v, q, hr', hv, _⟩
    subst hr'
    rcases h.2 p v q hw with ⟨a, b, ha, hb, hap, hbp, hop⟩
    refine ⟨sym a, sym b, sym_lt a, sym_lt b, ?_, ?_, ?_⟩
    · rcases hap with hba | hma
      · exact Or.inl (by rw [sym_isBase ha]; exact hba)
      · exact Or.inr (by rw [← hp]; exact List.mem_map_of_mem hma)
    · rcases hbp with hbb | hmb
      · exact Or.inl (by rw [sym_isBase hb]; exact hbb)
      · exact Or.inr (by rw [← hp]; exact List.mem_map_of_mem hmb)
    · subst hv
      rcases hop with rfl | rfl
      · exact Or.inr (sym_cAnd a b)
      · exact Or.inl (sym_cOr a b)

def Coverable (k : Nat) (s : List Nat) : Prop :=
  ∃ w : List Nat, w.length ≤ k ∧ ValidSeq w ∧ ∀ x ∈ s, x ∈ w

theorem coverable_mono {k : Nat} {s t : List Nat}
    (hsub : ∀ x ∈ t, x ∈ s) (hs : Coverable k s) : Coverable k t := by
  rcases hs with ⟨w, hlen, hval, hcov⟩
  exact ⟨w, hlen, hval, fun x hx => hcov x (hsub x hx)⟩

theorem coverable_sym_inv {k : Nat} {s t : List Nat}
    (hlt : ∀ x ∈ t, x < 81) (hsub : ∀ x ∈ t, sym x ∈ s) (hs : Coverable k s) : Coverable k t := by
  rcases hs with ⟨w, hlen, hval, hcov⟩
  refine ⟨w.map sym, by simpa using hlen, validSeq_map_sym hval, ?_⟩
  intro x hx
  have h1 : sym x ∈ w := hcov (sym x) (hsub x hx)
  have h2 : sym (sym x) ∈ w.map sym := List.mem_map_of_mem h1
  rwa [sym_sym (hlt x hx)] at h2

theorem nodup_length_le : ∀ {s w : List Nat}, s.Nodup → (∀ x ∈ s, x ∈ w) → s.length ≤ w.length
  | [], _, _, _ => Nat.zero_le _
  | a :: t, w, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ w := hsub a (List.mem_cons_self ..)
    have hsub' : ∀ x ∈ t, x ∈ w.erase a := by
      intro x hx
      have hne : x ≠ a := fun heq => hnd.1 (heq ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem _ hx))
    have ih := nodup_length_le hnd.2 hsub'
    have hlen := List.length_erase_of_mem ha
    have hpos : 0 < w.length := by cases w with | nil => cases ha | cons _ _ => simp
    simp only [List.length_cons]
    omega

theorem coverable_length_le {k : Nat} {s : List Nat}
    (hnd : s.Nodup) (hc : Coverable k s) : s.length ≤ k := by
  rcases hc with ⟨w, hlen, _, hcov⟩
  exact Nat.le_trans (nodup_length_le hnd hcov) hlen

theorem ok8_of_gate_list : ∀ n (w : List (BitVec 8)), w.length ≤ n →
    (∀ p v q, w = p ++ v :: q →
      ∃ a ∈ baseBV ++ p, ∃ b ∈ baseBV ++ p, v = a &&& b ∨ v = a ||| b) →
    ∀ x ∈ w, ok8 x
  | 0, w, hlen, _ => by
    cases w with
    | nil => intro x hx; cases hx
    | cons _ _ => simp at hlen
  | n + 1, w, hlen, hg => by
    rcases List.eq_nil_or_concat w with rfl | ⟨p, v, rfl⟩
    · intro x hx; cases hx
    · rw [List.concat_eq_append] at hlen hg ⊢
      have hplen : p.length ≤ n := by simp at hlen; omega
      have hpg : ∀ p1 v1 q1, p = p1 ++ v1 :: q1 →
          ∃ a ∈ baseBV ++ p1, ∃ b ∈ baseBV ++ p1, v1 = a &&& b ∨ v1 = a ||| b := by
        intro p1 v1 q1 heq
        have hw : p ++ [v] = p1 ++ v1 :: (q1 ++ [v]) := by rw [heq]; simp [List.append_assoc]
        exact hg p1 v1 (q1 ++ [v]) hw
      have hokp := ok8_of_gate_list n p hplen hpg
      have hokbp : ∀ y ∈ baseBV ++ p, ok8 y := by
        intro y hy
        rcases List.mem_append.mp hy with hb | hp
        · exact ok8_base y hb
        · exact hokp y hp
      rcases hg p v [] (by simp) with ⟨a, ha, b, hb, hvv⟩
      have hokv : ok8 v := by
        rcases hvv with rfl | rfl
        · exact ok8_and (hokbp a ha) (hokbp b hb)
        · exact ok8_or (hokbp a ha) (hokbp b hb)
      intro x hx
      rcases List.mem_append.mp hx with hp | hv
      · exact hokp x hp
      · simp at hv; subst hv; exact hokv

theorem validSeq_of_bv {w : List (BitVec 8)}
    (hg : ∀ p v q, w = p ++ v :: q →
      ∃ a ∈ baseBV ++ p, ∃ b ∈ baseBV ++ p, v = a &&& b ∨ v = a ||| b) :
    ValidSeq (w.map code) := by
  have hokw := ok8_of_gate_list w.length w (Nat.le_refl _) hg
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
    exact code_lt y
  · intro p' v' q' heq
    rcases List.map_eq_append_iff.mp heq with ⟨p, r, hw, hp, hr⟩
    rcases List.map_eq_cons_iff.mp hr with ⟨v, q, hr', hv, _⟩
    subst hr'
    rcases hg p v q hw with ⟨a, ha, b, hb, hop⟩
    have hoka : ok8 a := by
      rcases List.mem_append.mp ha with h1 | h2
      · exact ok8_base a h1
      · exact hokw a (by rw [hw]; exact List.mem_append_left _ h2)
    have hokb : ok8 b := by
      rcases List.mem_append.mp hb with h1 | h2
      · exact ok8_base b h1
      · exact hokw b (by rw [hw]; exact List.mem_append_left _ h2)
    refine ⟨code a, code b, code_lt a, code_lt b, ?_, ?_, ?_⟩
    · rcases List.mem_append.mp ha with h1 | h2
      · exact Or.inl (isBase_code_base a h1)
      · exact Or.inr (by rw [← hp]; exact List.mem_map_of_mem h2)
    · rcases List.mem_append.mp hb with h1 | h2
      · exact Or.inl (isBase_code_base b h1)
      · exact Or.inr (by rw [← hp]; exact List.mem_map_of_mem h2)
    · subst hv
      rcases hop with rfl | rfl
      · exact Or.inl (code_and hoka hokb)
      · exact Or.inr (code_or hoka hokb)

def natMem (x : Nat) : List Nat → Bool
  | [] => false
  | a :: t => Nat.beq x a || natMem x t

theorem natMem_iff : ∀ {x : Nat} {l : List Nat}, natMem x l = true ↔ x ∈ l
  | _, [] => by simp [natMem]
  | x, a :: t => by
    simp only [natMem, Bool.or_eq_true, Nat.beq_eq, List.mem_cons, natMem_iff]

def natSubset : List Nat → List Nat → Bool
  | [], _ => true
  | a :: t, r => natMem a r && natSubset t r

theorem natSubset_spec : ∀ {t r : List Nat}, natSubset t r = true → ∀ x ∈ t, x ∈ r
  | [], _, _, _, hx => by cases hx
  | a :: t, r, h, x, hx => by
    simp only [natSubset, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | ht
    · exact natMem_iff.mp h.1
    · exact natSubset_spec h.2 x ht

def natSubsetSym : List Nat → List Nat → Bool
  | [], _ => true
  | a :: t, r => natMem (sym a) r && natSubsetSym t r

theorem natSubsetSym_spec : ∀ {t r : List Nat}, natSubsetSym t r = true → ∀ x ∈ t, sym x ∈ r
  | [], _, _, _, hx => by cases hx
  | a :: t, r, h, x, hx => by
    simp only [natSubsetSym, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hx with rfl | ht
    · exact natMem_iff.mp h.1
    · exact natSubsetSym_spec h.2 x ht

def natErase (x : Nat) : List Nat → List Nat
  | [] => []
  | a :: t => match Nat.beq x a with | true => t | false => a :: natErase x t

theorem mem_of_mem_natErase : ∀ {x y : Nat} {l : List Nat}, y ∈ natErase x l → y ∈ l
  | _, _, [], h => by cases h
  | x, y, a :: t, h => by
    unfold natErase at h
    cases hb : Nat.beq x a
    · rw [hb] at h
      rcases List.mem_cons.mp h with rfl | ht
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (mem_of_mem_natErase ht)
    · rw [hb] at h
      exact List.mem_cons_of_mem _ h

theorem not_mem_natErase : ∀ {x : Nat} {l : List Nat}, l.Nodup → x ∉ natErase x l
  | _, [], _ => by simp [natErase]
  | x, a :: t, hnd => by
    rw [List.nodup_cons] at hnd
    unfold natErase
    cases hb : Nat.beq x a
    · intro hm
      rcases List.mem_cons.mp hm with rfl | ht
      · simp at hb
      · exact not_mem_natErase hnd.2 ht
    · have hxa : x = a := Nat.beq_eq.mp hb
      subst hxa
      exact hnd.1

theorem nodup_natErase : ∀ {x : Nat} {l : List Nat}, l.Nodup → (natErase x l).Nodup
  | _, [], _ => List.nodup_nil
  | x, a :: t, hnd => by
    rw [List.nodup_cons] at hnd
    unfold natErase
    cases hb : Nat.beq x a
    · rw [List.nodup_cons]
      exact ⟨fun hm => hnd.1 (mem_of_mem_natErase hm), nodup_natErase hnd.2⟩
    · exact hnd.2

def decodeAdd (p : Nat) : List Nat :=
  let a := p % 128
  let b := p / 128
  match Nat.beq a 0 with
  | true => []
  | false => match Nat.beq b 0 with
    | true => [a - 1]
    | false => [a - 1, b - 1]

def decodeSet (w : Nat) : List Nat :=
  let d := (w / 2097152) % 128
  let l := match Nat.beq d 0 with | true => [] | false => [d - 1]
  let c := (w / 16384) % 128
  let l := match Nat.beq c 0 with | true => l | false => (c - 1) :: l
  let b := (w / 128) % 128
  let l := match Nat.beq b 0 with | true => l | false => (b - 1) :: l
  let a := w % 128
  match Nat.beq a 0 with | true => l | false => (a - 1) :: l

def strictlyInc : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: t => Nat.blt a b && strictlyInc (b :: t)

theorem strictlyInc_lt : ∀ {a : Nat} {t : List Nat},
    strictlyInc (a :: t) = true → ∀ x ∈ t, a < x
  | _, [], _, _, hx => by cases hx
  | a, b :: t, h, x, hx => by
    simp only [strictlyInc, Bool.and_eq_true, Nat.blt_eq] at h
    rcases List.mem_cons.mp hx with rfl | ht
    · exact h.1
    · exact Nat.lt_trans h.1 (strictlyInc_lt h.2 x ht)

theorem nodup_of_strictlyInc : ∀ {s : List Nat}, strictlyInc s = true → s.Nodup
  | [], _ => List.nodup_nil
  | a :: t, h => by
    rw [List.nodup_cons]
    refine ⟨fun ha => Nat.lt_irrefl a (strictlyInc_lt h a ha), ?_⟩
    cases t with
    | nil => exact List.nodup_nil
    | cons b r =>
      simp only [strictlyInc, Bool.and_eq_true] at h
      exact nodup_of_strictlyInc h.2

def allValidElts : List Nat → Bool
  | [] => true
  | x :: t => Nat.blt x 81 && !isBase x && allValidElts t

theorem allValidElts_spec : ∀ {s : List Nat},
    allValidElts s = true → ∀ x ∈ s, x < 81 ∧ isBase x = false
  | [], _, _, hx => by cases hx
  | a :: t, h, x, hx => by
    simp only [allValidElts, Bool.and_eq_true, Nat.blt_eq, Bool.not_eq_true'] at h
    rcases List.mem_cons.mp hx with rfl | ht
    · exact h.1
    · exact allValidElts_spec h.2 x ht

def validSet (s : List Nat) : Bool :=
  !s.isEmpty && strictlyInc s && allValidElts s

theorem validSet_spec {s : List Nat} (h : validSet s = true) :
    s ≠ [] ∧ s.Nodup ∧ ∀ x ∈ s, x < 81 ∧ isBase x = false := by
  simp only [validSet, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨?_, nodup_of_strictlyInc h.1.2, allValidElts_spec h.2⟩
  intro heq; subst heq; simp at h

def insOne (x : Nat) (l : List Nat) : List Nat :=
  match natMem x l with | true => l | false => x :: l

theorem insOne_nodup {x : Nat} {l : List Nat} (h : l.Nodup) : (insOne x l).Nodup := by
  unfold insOne
  cases he : natMem x l
  · rw [List.nodup_cons]
    refine ⟨?_, h⟩
    intro hm
    have := natMem_iff.mpr hm
    rw [this] at he
    cases he
  · exact h

theorem mem_insOne {x y : Nat} {l : List Nat} : y ∈ insOne x l ↔ y = x ∨ y ∈ l := by
  unfold insOne
  cases he : natMem x l
  · exact List.mem_cons
  · have hx : x ∈ l := natMem_iff.mp he
    constructor
    · intro hy; exact Or.inr hy
    · intro hy; rcases hy with rfl | hy; exact hx; exact hy

def insAdd : List Nat → List Nat → List Nat
  | [], rest => rest
  | x :: xs, rest => insAdd xs (insOne x rest)

theorem insAdd_nodup : ∀ (add rest : List Nat), rest.Nodup → (insAdd add rest).Nodup
  | [], _, h => h
  | x :: xs, rest, h => insAdd_nodup xs (insOne x rest) (insOne_nodup h)

theorem mem_insAdd : ∀ {add rest : List Nat} {y : Nat},
    y ∈ insAdd add rest ↔ y ∈ add ∨ y ∈ rest
  | [], _, _ => by simp [insAdd]
  | x :: xs, rest, y => by
    unfold insAdd
    rw [mem_insAdd, mem_insOne, List.mem_cons]
    constructor
    · intro h
      rcases h with hxs | rfl | hr
      · exact Or.inl (Or.inr hxs)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hr
    · intro h
      rcases h with (rfl | hxs) | hr
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hxs
      · exact Or.inr (Or.inr hr)

theorem exists_not_mem_of_not_forall : ∀ {s p : List Nat},
    (¬ ∀ x ∈ s, x ∈ p) → ∃ x ∈ s, x ∉ p
  | [], _, h => absurd (fun _ hx => by cases hx) h
  | a :: t, p, h => by
    by_cases ha : a ∈ p
    · have hnt : ¬ ∀ x ∈ t, x ∈ p := fun ht => h (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hxt; exact ha; exact ht x hxt)
      rcases exists_not_mem_of_not_forall hnt with ⟨x, hxt, hxp⟩
      exact ⟨x, List.mem_cons_of_mem _ hxt, hxp⟩
    · exact ⟨a, List.mem_cons_self .., ha⟩

def pow28 (j : Nat) : Nat :=
  (match Nat.blt j 8 with | true => (match Nat.blt j 4 with | true => (match Nat.blt j 2 with | true => (match Nat.blt j 1 with | true => 0x1 | false => 0x10000000) | false => (match Nat.blt j 3 with | true => 0x100000000000000 | false => 0x1000000000000000000000)) | false => (match Nat.blt j 6 with | true => (match Nat.blt j 5 with | true => 0x10000000000000000000000000000 | false => 0x100000000000000000000000000000000000) | false => (match Nat.blt j 7 with | true => 0x1000000000000000000000000000000000000000000 | false => 0x10000000000000000000000000000000000000000000000000))) | false => (match Nat.blt j 12 with | true => (match Nat.blt j 10 with | true => (match Nat.blt j 9 with | true => 0x100000000000000000000000000000000000000000000000000000000 | false => 0x1000000000000000000000000000000000000000000000000000000000000000) | false => (match Nat.blt j 11 with | true => 0x10000000000000000000000000000000000000000000000000000000000000000000000 | false => 0x100000000000000000000000000000000000000000000000000000000000000000000000000000)) | false => (match Nat.blt j 14 with | true => (match Nat.blt j 13 with | true => 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => 0x10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) | false => (match Nat.blt j 15 with | true => 0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 | false => 0x1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000))))

def preds (v : Nat) : List Nat :=
  (match Nat.blt v 40 with | true => (match Nat.blt v 20 with | true => (match Nat.blt v 10 with | true => (match Nat.blt v 5 with | true => (match Nat.blt v 2 with | true => (match Nat.blt v 1 with | true => [] | false => [3, 5, 8, 11, 20, 29, 32, 35, 38, 47, 56, 59, 62, 65, 74, 3854, 7310, 3857, 7313, 3863, 7319, 3866, 7322]) | false => (match Nat.blt v 3 with | true => [0] | false => (match Nat.blt v 4 with | true => [0] | false => [6, 14, 23, 32, 41, 50, 59, 68, 77, 514, 1928, 3080, 4232, 5384, 6536, 7688, 8840, 9992, 4495, 7951, 4241, 7697, 4504, 7960, 4250, 7706]))) | false => (match Nat.blt v 7 with | true => (match Nat.blt v 6 with | true => [15, 24, 33, 42, 51, 60, 69, 78, 515, 643] | false => [0]) | false => (match Nat.blt v 8 with | true => [0] | false => (match Nat.blt v 9 with | true => [] | false => [0])))) | false => (match Nat.blt v 15 with | true => (match Nat.blt v 12 with | true => (match Nat.blt v 11 with | true => [12, 14, 17, 38, 41, 44, 65, 68, 71, 1282, 2575, 6031, 9487, 2578, 6034, 9490, 5012, 5396, 5780, 8468, 8852, 9236, 5015, 8471, 5018, 8474] | false => [15, 18, 39, 42, 45, 66, 69, 72, 1283, 1411]) | false => (match Nat.blt v 13 with | true => [14, 15, 16, 17, 18, 1284, 5142, 5270, 5398, 5526, 5654, 5782, 8598, 8726, 8854, 8982, 9110, 9238, 5143, 5527, 8599, 8983, 5144, 5528, 8600, 8984, 5145, 5273, 5401, 8601, 8729, 8857, 5146, 8602, 5147, 8603] | false => (match Nat.blt v 14 with | true => [15, 1666, 1412, 1285, 1413, 1669, 1675, 2961, 3089, 5265, 5393, 6417, 6545, 8721, 8849, 9873, 10001, 2962, 5266, 6418, 8722, 9874, 5271, 5399, 5655, 5783, 8727, 8855, 9111, 9239, 5272, 5656, 8728, 9112, 5274, 5402, 8730, 8858, 5275, 8731] | false => [1667, 1795, 1540, 1541, 1286, 1414, 1542, 1670, 1798, 1676, 1804, 3090, 5394, 6546, 8850, 10002, 5400, 5784, 8856, 9240, 5403, 8859]))) | false => (match Nat.blt v 17 with | true => (match Nat.blt v 16 with | true => [17, 18, 1287, 1671, 5529, 5657, 5785, 8985, 9113, 9241, 5530, 8986, 5531, 8987] | false => [18, 2050, 2053, 1415, 1799, 1288, 1416, 1672, 1800, 2056, 2059, 2062, 5658, 5786, 9114, 9242, 5659, 9115]) | false => (match Nat.blt v 18 with | true => [10, 11, 12, 13, 14, 15, 16, 17, 5787, 9243] | false => (match Nat.blt v 19 with | true => [0] | false => [0]))))) | false => (match Nat.blt v 30 with | true => (match Nat.blt v 25 with | true => (match Nat.blt v 22 with | true => (match Nat.blt v 21 with | true => [] | false => [23, 24, 25, 26, 27, 2436, 2445]) | false => (match Nat.blt v 23 with | true => [24, 2818, 2564, 2437, 2565, 2821, 2827, 2573, 2446, 2574, 2830, 2836, 6426, 6554, 9882, 10010, 6427, 9883] | false => (match Nat.blt v 24 with | true => [4, 5, 6, 13, 14, 15, 22, 23, 6555, 10011] | false => [26, 27, 2439, 2823, 2448, 2832]))) | false => (match Nat.blt v 27 with | true => (match Nat.blt v 26 with | true => [27, 3202, 3205, 2567, 2951, 2440, 2568, 2824, 2952, 3208, 3211, 3214, 2576, 2960, 2449, 2577, 2833, 2961, 3217, 3220, 3223] | false => [0]) | false => (match Nat.blt v 28 with | true => [] | false => (match Nat.blt v 29 with | true => [2, 30, 4896, 5024, 6048, 6176, 7200, 7328, 8352, 8480, 9504, 9632, 4897, 6049, 7201, 8353, 9505, 4899, 5027, 6051, 6179, 7203, 7331, 8355, 8483, 9507, 9635, 4900, 6052, 7204, 8356, 9508, 7206, 7334, 7590, 7718, 7974, 8102, 7207, 7591, 7975, 7209, 7337, 7210, 7212, 7340, 7213, 7215, 7343, 7599, 7727, 7983, 8111, 7216, 7600, 7984, 7218, 7346, 7219, 7221, 7349, 7222] | false => [3, 5025, 6177, 7329, 8481, 9633, 5028, 6180, 7332, 8484, 9636, 7335, 7719, 8103, 7338, 7341, 7344, 7728, 8112, 7347, 7350])))) | false => (match Nat.blt v 35 with | true => (match Nat.blt v 32 with | true => (match Nat.blt v 31 with | true => [4, 32, 33, 34, 35, 36, 7464, 7592, 7720, 7848, 7976, 8104, 7465, 7849, 7466, 7850, 7467, 7595, 7723, 7468, 7469, 7473, 7601, 7729, 7857, 7985, 8113, 7474, 7858, 7475, 7859, 7476, 7604, 7732, 7477, 7478] | false => [5, 33, 3970, 3716, 3997, 5283, 5411, 6435, 6563, 7587, 7715, 8739, 8867, 9891, 10019, 5284, 6436, 7588, 8740, 9892, 7593, 7721, 7977, 8105, 7594, 7978, 7596, 7724, 7597, 7602, 7730, 7986, 8114, 7603, 7987, 7605, 7733, 7606]) | false => (match Nat.blt v 33 with | true => [6, 3971, 4099, 3844, 3845, 3998, 4126, 5412, 6564, 7716, 8868, 10020, 7722, 8106, 7725, 7731, 8115, 7734] | false => (match Nat.blt v 34 with | true => [7, 35, 36, 7851, 7979, 8107, 7852, 7853, 7860, 7988, 8116, 7861, 7862] | false => [8, 36, 4354, 4357, 3719, 4103, 4381, 4384, 7980, 8108, 7981, 7989, 8117, 7990]))) | false => (match Nat.blt v 37 with | true => (match Nat.blt v 36 with | true => [0] | false => [10, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54]) | false => (match Nat.blt v 38 with | true => [11, 39, 4738, 3722, 4765, 6057, 6185, 8361, 8489, 9513, 9641, 6058, 8362, 9514, 6060, 6188, 8364, 8492, 9516, 9644, 6061, 8365, 9517, 8367, 8495, 8751, 8879, 9135, 9263, 8368, 8752, 9136, 8370, 8498, 8371, 8373, 8501, 8374] | false => (match Nat.blt v 39 with | true => [12, 4739, 4867, 3850, 3851, 4766, 4894, 6186, 8490, 9642, 6189, 8493, 9645, 8496, 8880, 9264, 8499, 8502] | false => [13, 41, 42, 43, 44, 45, 4740, 3978, 4767, 8625, 8753, 8881, 9009, 9137, 9265, 8626, 9010, 8627, 9011, 8628, 8756, 8884, 8629, 8630])))))) | false => (match Nat.blt v 60 with | true => (match Nat.blt v 50 with | true => (match Nat.blt v 45 with | true => (match Nat.blt v 42 with | true => (match Nat.blt v 41 with | true => [14, 42, 5122, 4868, 4741, 4869, 5125, 4106, 3979, 4107, 5131, 3725, 4109, 4877, 5149, 4895, 4768, 4896, 5152, 5158, 6444, 6572, 8748, 8876, 9900, 10028, 6445, 8749, 9901, 8754, 8882, 9138, 9266, 8755, 9139, 8757, 8885, 8758] | false => [15, 5123, 5251, 4996, 4997, 4742, 4870, 4998, 5126, 5254, 4234, 4235, 3980, 4108, 4236, 5132, 5260, 3853, 4237, 5005, 3854, 4238, 5006, 5150, 5278, 5023, 5024, 4769, 4897, 5025, 5153, 5281, 5159, 5287, 6573, 8877, 10029, 8883, 9267, 8886]) | false => (match Nat.blt v 43 with | true => [16, 44, 45, 4743, 5127, 4362, 4365, 4770, 5154, 9012, 9140, 9268, 9013, 9014] | false => (match Nat.blt v 44 with | true => [17, 45, 5506, 5509, 4871, 5255, 4744, 4872, 5128, 5256, 5512, 4490, 4363, 4491, 5515, 4493, 4366, 4494, 5518, 3728, 4112, 4496, 4880, 5264, 5533, 5536, 4898, 5282, 4771, 4899, 5155, 5283, 5539, 5542, 5545, 9141, 9269, 9142] | false => [18, 37, 38, 39, 40, 41, 42, 43, 44, 4618, 4619, 4364, 4492, 4620, 4621, 4622, 4367, 4495, 4623, 3856, 4240, 4624, 3857, 4241, 4625, 9270]))) | false => (match Nat.blt v 47 with | true => (match Nat.blt v 46 with | true => [19, 47, 48, 49, 50, 51, 52, 53, 54] | false => [20, 48, 5890, 5899, 3731, 4883, 5917, 5926, 9522, 9650, 9523, 9525, 9653, 9526]) | false => (match Nat.blt v 48 with | true => [0] | false => (match Nat.blt v 49 with | true => [22, 50, 51, 52, 53, 54, 5892, 5901, 3987, 5139, 5919, 5928] | false => [23, 51, 6274, 6020, 5893, 6021, 6277, 6283, 6029, 5902, 6030, 6286, 4115, 5267, 3988, 4116, 5140, 5268, 6292, 3734, 4118, 4886, 5270, 6038, 6301, 6047, 5920, 6048, 6304, 6310, 6056, 5929, 6057, 6313, 6319, 9909, 10037, 9910])))) | false => (match Nat.blt v 55 with | true => (match Nat.blt v 52 with | true => (match Nat.blt v 51 with | true => [24, 31, 32, 33, 40, 41, 42, 49, 50, 6148, 6149, 5894, 6022, 6150, 6157, 6158, 5903, 6031, 6159, 3862, 5014, 6166, 3863, 5015, 6167, 10038] | false => [25, 53, 54, 5895, 6279, 5904, 6288, 4371, 5523, 4374, 5526, 5922, 6306, 5931, 6315]) | false => (match Nat.blt v 53 with | true => [26, 54, 6658, 6661, 6023, 6407, 5896, 6024, 6280, 6408, 6664, 6667, 6670, 6032, 6416, 5905, 6033, 6289, 6417, 6673, 4499, 5651, 4372, 4500, 5524, 5652, 6676, 4502, 5654, 4375, 4503, 5527, 5655, 6679, 3737, 4121, 4505, 4889, 5273, 5657, 6041, 6425, 6685, 6688, 6050, 6434, 5923, 6051, 6307, 6435, 6691, 6694, 6697, 6059, 6443, 5932, 6060, 6316, 6444, 6700, 6703, 6706] | false => (match Nat.blt v 54 with | true => [27, 34, 35, 36, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 3865, 4249, 5017, 5401, 3866, 4250, 5018, 5402] | false => []))) | false => (match Nat.blt v 57 with | true => (match Nat.blt v 56 with | true => [2, 29, 57, 8379, 8507, 9531, 9659, 8380, 9532, 8382, 8510, 9534, 9662, 8383, 9535] | false => [3, 30, 8508, 9660, 8511, 9663]) | false => (match Nat.blt v 58 with | true => [4, 31, 59, 60, 61, 62, 63] | false => (match Nat.blt v 59 with | true => [5, 32, 60, 7426, 7172, 7453, 7199, 7480, 8766, 8894, 9918, 10046, 8767, 9919] | false => [6, 33, 7427, 7555, 7300, 7301, 7454, 7582, 7327, 7328, 7481, 7609, 8895, 10047]))))) | false => (match Nat.blt v 70 with | true => (match Nat.blt v 65 with | true => (match Nat.blt v 62 with | true => (match Nat.blt v 61 with | true => [7, 34, 62, 63] | false => [8, 35, 63, 7810, 7813, 7175, 7559, 7837, 7840, 7202, 7586, 7864, 7867]) | false => (match Nat.blt v 63 with | true => [0] | false => (match Nat.blt v 64 with | true => [] | false => [2, 11, 29, 38, 56, 66, 9540, 9668, 9541, 9543, 9671, 9544]))) | false => (match Nat.blt v 67 with | true => (match Nat.blt v 66 with | true => [3, 12, 30, 39, 57, 9669, 9672] | false => [4, 13, 31, 40, 58, 68, 69, 70, 71, 72]) | false => (match Nat.blt v 68 with | true => [5, 14, 32, 41, 59, 69, 8578, 8324, 7435, 8587, 7181, 8333, 8605, 8351, 7462, 8614, 7208, 8360, 8632, 8378, 8641, 9927, 10055, 9928] | false => (match Nat.blt v 69 with | true => [6, 15, 33, 42, 60, 8579, 8707, 8452, 8453, 7436, 7564, 8588, 8716, 7309, 8461, 7310, 8462, 8606, 8734, 8479, 8480, 7463, 7591, 8615, 8743, 7336, 8488, 7337, 8489, 8633, 8761, 8506, 8507, 8642, 8770, 10056] | false => [7, 16, 34, 43, 61, 71, 72])))) | false => (match Nat.blt v 75 with | true => (match Nat.blt v 72 with | true => (match Nat.blt v 71 with | true => [8, 17, 35, 44, 62, 72, 8962, 8965, 8327, 8711, 7819, 8971, 7822, 8974, 7184, 7568, 8336, 8720, 8989, 8992, 8354, 8738, 7846, 8998, 7849, 9001, 7211, 7595, 8363, 8747, 9016, 9019, 8381, 8765, 9025, 9028] | false => [0]) | false => (match Nat.blt v 73 with | true => [] | false => (match Nat.blt v 74 with | true => [2, 11, 20, 29, 38, 47, 56, 65, 75] | false => [0]))) | false => (match Nat.blt v 78 with | true => (match Nat.blt v 76 with | true => [] | false => (match Nat.blt v 77 with | true => [2, 5, 11, 14, 20, 23, 29, 32, 38, 41, 47, 50, 56, 59, 65, 68, 74, 78] | false => [0])) | false => (match Nat.blt v 79 with | true => [] | false => (match Nat.blt v 80 with | true => [] | false => [])))))))

def checkPredPair (a b : Nat) : Bool :=
  let v1 := cAnd a b
  let ok1 := Nat.beq v1 a || Nat.beq v1 b || isBase v1 ||
    (preds v1).any (fun p =>
      (decodeAdd p).all (fun x => (Nat.beq x a || Nat.beq x b) && !isBase x))
  let v2 := cOr a b
  let ok2 := Nat.beq v2 a || Nat.beq v2 b || isBase v2 ||
    (preds v2).any (fun p =>
      (decodeAdd p).all (fun x => (Nat.beq x a || Nat.beq x b) && !isBase x))
  ok1 && ok2

def checkPairsB (a : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | b, n + 1 => checkPredPair a b && checkPairsB a (b + 1) n

def checkPairsA : Nat → Nat → Bool
  | _, 0 => true
  | a, n + 1 => checkPairsB a (a + 1) (80 - a) && checkPairsA (a + 1) n

theorem checkPairsB_sound : ∀ a b n, checkPairsB a b n = true →
    ∀ j, b ≤ j → j < b + n → checkPredPair a j = true
  | _, _, 0, _, _, h1, h2 => by omega
  | a, b, n + 1, h, j, h1, h2 => by
    simp only [checkPairsB, Bool.and_eq_true] at h
    by_cases hjb : j = b
    · subst hjb; exact h.1
    · exact checkPairsB_sound a (b + 1) n h.2 j (by omega) (by omega)

theorem checkPairsA_sound : ∀ a n, checkPairsA a n = true →
    ∀ i, a ≤ i → i < a + n → ∀ j, i < j → j < 81 → checkPredPair i j = true
  | _, 0, _, _, h1, h2, _, _, _ => by omega
  | a, n + 1, h, i, h1, h2, j, h3, h4 => by
    simp only [checkPairsA, Bool.and_eq_true] at h
    by_cases hia : i = a
    · subst hia
      exact checkPairsB_sound i (i + 1) (80 - i) h.1 j (by omega) (by omega)
    · exact checkPairsA_sound (a + 1) n h.2 i (by omega) (by omega) j h3 h4

theorem preds_check_0 : checkPairsA 0 27 = true := by decide +kernel
theorem preds_check_1 : checkPairsA 27 27 = true := by decide +kernel
theorem preds_check_2 : checkPairsA 54 27 = true := by decide +kernel

theorem checkPredPair_all {a b : Nat} (ha : a < 81) (hb : b < 81) (hab : a < b) :
    checkPredPair a b = true := by
  by_cases h1 : a < 27
  · exact checkPairsA_sound 0 27 preds_check_0 a (Nat.zero_le _) h1 b hab hb
  · by_cases h2 : a < 54
    · exact checkPairsA_sound 27 27 preds_check_1 a (by omega) h2 b hab hb
    · exact checkPairsA_sound 54 27 preds_check_2 a (by omega) ha b hab hb

theorem preds_complete {a b v : Nat} (ha : a < 81) (hb : b < 81)
    (hnb : isBase v = false) (hna : a ≠ v) (hnb' : b ≠ v)
    (hop : v = cAnd a b ∨ v = cOr a b) :
    ∃ p ∈ preds v, ∀ x ∈ decodeAdd p, (x = a ∨ x = b) ∧ isBase x = false := by
  have hab_ne : a ≠ b := by
    intro heq; subst heq
    rcases hop with rfl | rfl
    · exact hna (cAnd_self ha).symm
    · exact hna (cOr_self ha).symm
  have hcheck : ∀ x y, x < 81 → y < 81 → x < y → x ≠ v → y ≠ v →
      (v = cAnd x y ∨ v = cOr x y) →
      ∃ p ∈ preds v, ∀ u ∈ decodeAdd p, (u = x ∨ u = y) ∧ isBase u = false := by
    intro x y hx hy hxy hxv hyv hxyop
    have hcp := checkPredPair_all hx hy hxy
    simp only [checkPredPair, Bool.and_eq_true] at hcp
    rcases hxyop with rfl | rfl
    · have h1 := hcp.1
      simp only [Bool.or_eq_true, Nat.beq_eq, List.any_eq_true, List.all_eq_true,
        Bool.and_eq_true, Bool.not_eq_true'] at h1
      rcases h1 with ((h1a | h1b) | h1c) | ⟨p, hp, hall⟩
      · exact absurd h1a.symm hxv
      · exact absurd h1b.symm hyv
      · rw [hnb] at h1c; cases h1c
      · exact ⟨p, hp, hall⟩
    · have h2 := hcp.2
      simp only [Bool.or_eq_true, Nat.beq_eq, List.any_eq_true, List.all_eq_true,
        Bool.and_eq_true, Bool.not_eq_true'] at h2
      rcases h2 with ((h2a | h2b) | h2c) | ⟨p, hp, hall⟩
      · exact absurd h2a.symm hxv
      · exact absurd h2b.symm hyv
      · rw [hnb] at h2c; cases h2c
      · exact ⟨p, hp, hall⟩
  by_cases hlt : a < b
  · exact hcheck a b ha hb hlt hna hnb' hop
  · have hba : b < a := by omega
    have hop' : v = cAnd b a ∨ v = cOr b a := by
      rcases hop with h1 | h2
      · exact Or.inl (by rw [cAnd_comm]; exact h1)
      · exact Or.inr (by rw [cOr_comm]; exact h2)
    rcases hcheck b a hb ha hba hnb' hna hop' with ⟨p, hp, hall⟩
    exact ⟨p, hp, fun u hu => by
      rcases hall u hu with ⟨h1 | h2, h3⟩
      · exact ⟨Or.inr h1, h3⟩
      · exact ⟨Or.inl h2, h3⟩⟩

def checkOne (getPrev : Nat → Nat) (prevN : Nat) (r : List Nat) (wits : Nat) : Bool × Nat :=
  let c := wits % 2048
  let wits' := wits / 2048
  let flip := c % 2
  let idx := c / 2
  match Nat.blt idx prevN with
  | true =>
    let t := decodeSet (getPrev idx)
    let ok := match Nat.beq flip 0 with | true => natSubset t r | false => natSubsetSym t r
    (ok, wits')
  | false =>
    (false, wits')

theorem checkOne_sound {k : Nat} {getPrev : Nat → Nat} {prevN : Nat}
    (hPrevLt : ∀ j < prevN, ∀ x ∈ decodeSet (getPrev j), x < 81)
    (hPrevNo : ∀ j < prevN, ¬ Coverable k (decodeSet (getPrev j)))
    {r : List Nat} {wits : Nat}
    (h : (checkOne getPrev prevN r wits).1 = true) :
    ¬ Coverable k r := by
  dsimp only [checkOne] at h
  cases hlt : Nat.blt ((wits % 2048) / 2) prevN
  · rw [hlt] at h; cases h
  · rw [hlt] at h
    have hidx : (wits % 2048) / 2 < prevN := Nat.blt_eq.mp hlt
    dsimp only at h
    cases hf : Nat.beq ((wits % 2048) % 2) 0
    · rw [hf] at h
      intro hcr
      exact hPrevNo _ hidx (coverable_sym_inv (hPrevLt _ hidx) (natSubsetSym_spec h) hcr)
    · rw [hf] at h
      intro hcr
      exact hPrevNo _ hidx (coverable_mono (natSubset_spec h) hcr)

def checkPredList (k : Nat) (getPrev : Nat → Nat) (prevN : Nat) (rest : List Nat) :
    List Nat → Nat → Bool × Nat
  | [], wits => (true, wits)
  | p :: ps, wits =>
    let r := insAdd (decodeAdd p) rest
    match Nat.ble r.length k with
    | true =>
      let res := checkOne getPrev prevN r wits
      match res.1 with
      | true => checkPredList k getPrev prevN rest ps res.2
      | false => (false, res.2)
    | false => checkPredList k getPrev prevN rest ps wits

theorem checkPredList_sound {k : Nat} {getPrev : Nat → Nat} {prevN : Nat} {rest : List Nat} :
    ∀ {ps : List Nat} {wits : Nat},
      (checkPredList k getPrev prevN rest ps wits).1 = true →
      ∀ p ∈ ps, (insAdd (decodeAdd p) rest).length ≤ k →
        ∃ w, (checkOne getPrev prevN (insAdd (decodeAdd p) rest) w).1 = true
  | [], _, _, _, hp, _ => by cases hp
  | p :: ps, wits, h, q, hq, hlen => by
    dsimp only [checkPredList] at h
    cases hle : Nat.ble (insAdd (decodeAdd p) rest).length k
    · rw [hle] at h
      rcases List.mem_cons.mp hq with rfl | hqs
      · have htr := Nat.ble_eq.mpr hlen
        rw [htr] at hle; cases hle
      · exact checkPredList_sound h q hqs hlen
    · rw [hle] at h
      cases hc : (checkOne getPrev prevN (insAdd (decodeAdd p) rest) wits).1
      · rw [hc] at h; cases h
      · rw [hc] at h
        rcases List.mem_cons.mp hq with rfl | hqs
        · exact ⟨wits, hc⟩
        · exact checkPredList_sound h q hqs hlen

def checkVs (k : Nat) (getPrev : Nat → Nat) (prevN : Nat) (s : List Nat) :
    List Nat → Nat → Bool × Nat
  | [], wits => (true, wits)
  | v :: vs, wits =>
    let res := checkPredList k getPrev prevN (natErase v s) (preds v) wits
    match res.1 with
    | true => checkVs k getPrev prevN s vs res.2
    | false => (false, res.2)

theorem checkVs_sound {k : Nat} {getPrev : Nat → Nat} {prevN : Nat} {s : List Nat} :
    ∀ {vs : List Nat} {wits : Nat},
      (checkVs k getPrev prevN s vs wits).1 = true →
      ∀ v ∈ vs, ∀ p ∈ preds v, (insAdd (decodeAdd p) (natErase v s)).length ≤ k →
        ∃ w, (checkOne getPrev prevN (insAdd (decodeAdd p) (natErase v s)) w).1 = true
  | [], _, _, _, hv, _, _, _ => by cases hv
  | v :: vs, wits, h, x, hx, p, hp, hlen => by
    dsimp only [checkVs] at h
    cases hc : (checkPredList k getPrev prevN (natErase v s) (preds v) wits).1
    · rw [hc] at h; cases h
    · rw [hc] at h
      rcases List.mem_cons.mp hx with rfl | hxs
      · exact checkPredList_sound hc p hp hlen
      · exact checkVs_sound h x hxs p hp hlen

def checkSet (k : Nat) (getPrev : Nat → Nat) (prevN : Nat) (s : List Nat) (wits : Nat) : Bool × Nat :=
  match Nat.ble s.length k with
  | true =>
    let res := checkOne getPrev prevN s wits
    match res.1 with
    | true => checkVs k getPrev prevN s s res.2
    | false => (false, res.2)
  | false => checkVs k getPrev prevN s s wits

theorem step_sound {k : Nat} {getPrev : Nat → Nat} {prevN : Nat}
    (hPrevLt : ∀ j < prevN, ∀ x ∈ decodeSet (getPrev j), x < 81)
    (hPrevNo : ∀ j < prevN, ¬ Coverable k (decodeSet (getPrev j)))
    {s : List Nat} {wits : Nat}
    (hval : validSet s = true)
    (hchk : (checkSet k getPrev prevN s wits).1 = true) :
    ¬ Coverable (k + 1) s := by
  rcases validSet_spec hval with ⟨hne, hnd, hmem⟩
  have hvs : ∃ wv, (checkVs k getPrev prevN s s wv).1 = true := by
    dsimp only [checkSet] at hchk
    cases hle : Nat.ble s.length k
    · rw [hle] at hchk; exact ⟨wits, hchk⟩
    · rw [hle] at hchk
      cases hc : (checkOne getPrev prevN s wits).1
      · rw [hc] at hchk; cases hchk
      · rw [hc] at hchk; exact ⟨_, hchk⟩
  intro ⟨w, hlen, hwval, hcov⟩
  rcases List.eq_nil_or_concat w with rfl | ⟨p, v, rfl⟩
  · cases s with
    | nil => exact hne rfl
    | cons a _ => cases hcov a (List.mem_cons_self ..)
  · rw [List.concat_eq_append] at hlen hwval hcov
    have hplen : p.length ≤ k := by simp at hlen; omega
    have hpval : ValidSeq p := validSeq_prefix hwval
    by_cases hpall : ∀ x ∈ s, x ∈ p
    · have hcp : Coverable k s := ⟨p, hplen, hpval, hpall⟩
      have hslen : s.length ≤ k := coverable_length_le hnd hcp
      dsimp only [checkSet] at hchk
      have hble : Nat.ble s.length k = true := Nat.ble_eq.mpr hslen
      rw [hble] at hchk
      cases hc : (checkOne getPrev prevN s wits).1
      · rw [hc] at hchk; cases hchk
      · exact checkOne_sound hPrevLt hPrevNo hc hcp
    · rcases exists_not_mem_of_not_forall hpall with ⟨x, hxs, hxp⟩
      have hxv : x = v := by
        rcases List.mem_append.mp (hcov x hxs) with hp' | hv'
        · exact absurd hp' hxp
        · simp at hv'; exact hv'
      subst hxv
      have hv_nb : isBase x = false := (hmem x hxs).2
      rcases hwval.2 p x [] (by simp) with ⟨a, b, ha, hb, hap, hbp, hop⟩
      have hax : a ≠ x := by
        intro heq; subst heq
        rcases hap with h1 | h2
        · rw [hv_nb] at h1; cases h1
        · exact hxp h2
      have hbx : b ≠ x := by
        intro heq; subst heq
        rcases hbp with h1 | h2
        · rw [hv_nb] at h1; cases h1
        · exact hxp h2
      rcases preds_complete ha hb hv_nb hax hbx hop with ⟨pr, hpr, hadd⟩
      let r := insAdd (decodeAdd pr) (natErase x s)
      have hrnd : r.Nodup := insAdd_nodup _ _ (nodup_natErase hnd)
      have hrcov : ∀ y ∈ r, y ∈ p := by
        intro y hy
        rcases mem_insAdd.mp hy with h1 | h2
        · rcases hadd y h1 with ⟨rfl | rfl, hynb⟩
          · rcases hap with hba | hpa
            · rw [hynb] at hba; cases hba
            · exact hpa
          · rcases hbp with hbb | hpb
            · rw [hynb] at hbb; cases hbb
            · exact hpb
        · have hys : y ∈ s := mem_of_mem_natErase h2
          have hyne : y ≠ x := by
            intro heq; subst heq
            exact not_mem_natErase hnd h2
          rcases List.mem_append.mp (hcov y hys) with hyp | hyv
          · exact hyp
          · simp at hyv; exact absurd hyv hyne
      have hcr : Coverable k r := ⟨p, hplen, hpval, hrcov⟩
      have hrlen : r.length ≤ k := coverable_length_le hrnd hcr
      rcases hvs with ⟨wv, hwv⟩
      rcases checkVs_sound hwv x hxs pr hpr hrlen with ⟨wr, hwr⟩
      exact checkOne_sound hPrevLt hPrevNo hwr hcr

def checkRange (k : Nat) (getCur getPrev : Nat → Nat) (prevN : Nat) :
    Nat → Nat → Nat → Bool
  | _, 0, _ => true
  | start, count + 1, wits =>
    let s := decodeSet (getCur start)
    match validSet s with
    | false => false
    | true =>
      let res := checkSet k getPrev prevN s wits
      match res.1 with
      | true => checkRange k getCur getPrev prevN (start + 1) count res.2
      | false => false

theorem checkRange_sound (k : Nat) (getCur getPrev : Nat → Nat) (prevN : Nat)
    (hPrevLt : ∀ j < prevN, ∀ x ∈ decodeSet (getPrev j), x < 81)
    (hPrevNo : ∀ j < prevN, ¬ Coverable k (decodeSet (getPrev j))) :
    ∀ start count wits, checkRange k getCur getPrev prevN start count wits = true →
      ∀ i, start ≤ i → i < start + count →
        (∀ x ∈ decodeSet (getCur i), x < 81) ∧ ¬ Coverable (k + 1) (decodeSet (getCur i))
  | _, 0, _, _, _, h1, h2 => by omega
  | start, count + 1, wits, h, i, h1, h2 => by
    dsimp only [checkRange] at h
    cases hv : validSet (decodeSet (getCur start))
    · rw [hv] at h; cases h
    · rw [hv] at h
      cases hr : (checkSet k getPrev prevN (decodeSet (getCur start)) wits).1
      · rw [hr] at h; cases h
      · rw [hr] at h
        by_cases his : i = start
        · subst his
          exact ⟨fun x hx => (validSet_spec hv).2.2 x hx |>.1,
                 step_sound hPrevLt hPrevNo hv hr⟩
        · exact checkRange_sound k getCur getPrev prevN hPrevLt hPrevNo
            (start + 1) count _ h i (by omega) (by omega)

def f1Chunk (q : Nat) : Nat :=
  (match Nat.blt q 1 with | true => 0x260000025000002300000220000020000001f000001d00000170000011000000f000000e000000d000000c000000b00000060000005 | false => 0x3d0000031000002f000002b00000290000028)
def f1 (i : Nat) : Nat :=
  (f1Chunk (i / 16) / pow28 (i % 16)) % 268435456

def f2Chunk (q : Nat) : Nat :=
  (match Nat.blt q 5 with | true => (match Nat.blt q 2 with | true => (match Nat.blt q 1 with | true => 0x128200011020000f82000090200008020000682000002900000280000026000002000000170000011000000f000000e000000b0000005 | false => 0x686000060600005060000386000238400020840001f040001e8400017840000e840000604000158300006830001e8200018820001582) | false => (match Nat.blt q 3 with | true => 0x687000060700023860001f860001f060001e860001a860001a0600018860001806000178600017060001586000128600011060000d06 | false => (match Nat.blt q 4 with | true => 0xc08000068800026870002387000228700020870001d870001a87000188700017870001587000128700011870000f870000e870000c07 | false => 0x118c000110c0000f8c0000e8c000068c000268a0001e8a0001d8a000118a0000e8a0001e8800018880001588000128800011080000f88))) | false => (match Nat.blt q 8 with | true => (match Nat.blt q 6 with | true => 0x1e8d0001d8d0001c0d000180d000178d000118d000110d0000f0d0000e8d0000a0d000268c0001f0c0001e8c0001a8c000188c000158c | false => (match Nat.blt q 7 with | true => 0x1594000129400011140000f9400026900001f100001e90000179000011900000f100000e90000268d000250d000238d000208d0001f0d | false => 0x1f1d0001e9d000189d000159d000129d000111d0000f9d0001e9a0001d9a00023960001f160001e9600017960000e960001e940001894)) | false => (match Nat.blt q 9 with | true => 0x1c2200018a200017a200015a200012a200011a2000239f000209f0001f1f0001e9f0001d9f0001c1f000179f000119f000111f000219d | false => (match Nat.blt q 10 with | true => 0x26a5000252500020a50001ea50001da50001c2500017a50001ea300018a300015a300012a300026a200020a20001f220001ea20001da2 | false => 0x1eb400020b10001eb10001eaf00018af0001eae000252b00020ab0001eab0001dab0001c2b00017ab))))
def f2 (i : Nat) : Nat :=
  (f2Chunk (i / 16) / pow28 (i % 16)) % 268435456

def f3Chunk (q : Nat) : Nat :=
  (match Nat.blt q 17 with | true => (match Nat.blt q 8 with | true => (match Nat.blt q 4 with | true => (match Nat.blt q 2 with | true => (match Nat.blt q 1 with | true => 0x6850000585000050500003850001384000058400014030001682000158200014020000682000002900000260000020000000f000000e | false => 0x1f850001f050001e850001a850001a0500019850001885000180500017850001705000168500015850001405000138500012850001105) | false => (match Nat.blt q 3 with | true => 0x108a00019880001408000220700019870001407000138700010870000b87000088700005870001e860001a86000140600013860001286 | false => 0x1e8c000140c000110c000108c0000f8c0001f0b0001e8b000198b000188b000158b000140b000118b000110b000108b0000f8b000068b)) | false => (match Nat.blt q 6 with | true => (match Nat.blt q 5 with | true => 0x22110001f110001e91000141100011110000f910000e910000b910000e900001f0d0001e8d000178d000138d000108d0000f0d0000e8d | false => 0x209f0001f1f0001e9f0001e9d000159d000141d000221a000239700022170001f170001e9700014170001297000111700014140002691) | false => (match Nat.blt q 7 with | true => 0x1ea80001da80001c2800017a800026a500022250001ea50001da50001ea30001423000222200020a20001da20001422000239f000221f | false => 0xf45020088502007c50200c43820094382007c3820048382004038200f420200942020001eb10001eaf0001eab0002528000222800020a8))) | false => (match Nat.blt q 12 with | true => (match Nat.blt q 10 with | true => (match Nat.blt q 9 with | true => 0xf5202010d10200f510200c5102009510200fcf820094f820088f8200f4b0200fc90200f8902008890200fc80200f880200f48020088802 | false => 0xf5b02010da820115a02010da0200f5a020119982010d982012188201198820115882010d88200fd88200f580200f570200fd28200f9282) | false => (match Nat.blt q 11 with | true => 0xf4404011c384010438400bc38400743840030384010da8300fd58300ad10300f480300fc683008868300ac3830034383010de82010db02 | false => 0x11d7840109784010578400fd78400f978400f928400bd10400f4f0400fce8400f8e840094e840088e8400f4a0400fc60400f86040074504)) | false => (match Nat.blt q 14 with | true => (match Nat.blt q 13 with | true => 0x28386011df840105f84011df040105f040121e840109e8400f9e8400f5c040109a840105a84011d804010580400f980400f58040121784 | false => 0x8868600fc60600f860600fc50600f85060088506011c38600d038600c438600c038600bc38600b838600ac386006838600343860030386) | false => (match Nat.blt q 15 with | true => 0xf9786011d70600fd70600f970600fd58600d110600c510600c110600bd10600b910600ad10600fcd0600f8d060088d060088a0600fc686 | false => (match Nat.blt q 16 with | true => 0xc440700ac4070094407007c40700604070034407011df86011df0600fda0600f9a0600fd886011d80600fd80600f9806011d78600fd786 | false => 0xec68700e0687008c6870050687013460700d460700c460700ac6070090607008c60700746070034607013450700ec507008c5070074507))))) | false => (match Nat.blt q 25 with | true => (match Nat.blt q 21 with | true => (match Nat.blt q 19 with | true => (match Nat.blt q 18 with | true => 0x74c07011cb0700bcb070074b070114a0700c4a0700aca070094a07007ca070134807008c807007880701346870128687011c6870104687 | false => 0xe0f8700bcf87008cf8700acf07010ce8700c4e870094e87007ce8700f0d0700ecd070114c070104c0700ecc0700d4c070094c07008cc07) | false => (match Nat.blt q 20 with | true => 0x115207010520700ed20701391870135187011d1870115187010518700f118700ed18700c518700ad18700951870114f870108f8700ecf87 | false => 0x129587011d5870115587010558700ed58700e158700bd587013928701292870115287010528700f128700e128700bd2870135207011d207)) | false => (match Nat.blt q 23 with | true => (match Nat.blt q 22 with | true => 0x135807011d8070115807010580700ed8070135787011d7870109787010578700f178700ed78700c57870135707011570700ed7070139587 | false => 0x8868800f45080139a870135a87011da87010da870109a870105a870135a07011da070115a0700eda0701358870115887010588700ed887) | false => (match Nat.blt q 24 with | true => 0x1155880139288011528800f928800f128800f520800f510800c510800ad10800951080088f880094c080088c0800f4b0800f480800c0688 | false => 0x13510a008d10a00f4f0a00f8e8a0088e8a007ce8a00f4a0a0139e8800f5e080115a0800f5a08011588800f5808011570800f57080139588))) | false => (match Nat.blt q 29 with | true => (match Nat.blt q 27 with | true => (match Nat.blt q 26 with | true => 0x10da0b00f1a0b00eda0b00e9a0b0135f0a0139e8a0129e8a00f5e0a00f9d8a00f5c0a013918a013518a011518a00f918a00f118a00ed18a | false => 0xc118d013510d012910d00e110d008d10d0088a0d0135f0c010da8c00f9a8c00e9a8c013518c00f918c00f8e8c010da8b00e9a8b0115a0b) | false => (match Nat.blt q 28 with | true => 0xe5a8d00e1a8d011d80d010580d00ed80d00e180d013518d012d18d012918d011518d010918d010518d00f118d00ed18d00e518d00e118d | false => 0xf5c1000f981000f9790013519000f91900135110008d11001350900134f100110f1000f8f1000f4f100088f1000f4a100109a8d0105a8d)) | false => (match Nat.blt q 31 with | true => (match Nat.blt q 30 with | true => 0x109e9400f5a1400f581400f571400f9294010911400f511400c511400ad11400951140108f940088f9400f4b140135f100129e9000f9e90 | false => 0xf9e96011d79600f9796011d39600f929600bd116011cf160110f1600f8f1600f4f16011ce960118e960110e96010ce9600f8e960088e96) | false => (match Nat.blt q 32 with | true => 0x10d89d00f929d010d11d00c511d009511d0094f9d0088f9d010de9a00f9d9a010ce9a0110f190110e99010ce990118e97010ce97011df16 | false => (match Nat.blt q 33 with | true => 0xe15a200bd5a201292a200e12a200bd2a201351a200c51a200ad1a200951a200e111f00bd11f008d11f010df1d010da9d010da1d011989d | false => 0x10deb400f5c340129eae00f5c2e00f9ea2010dc2200f5c220135a2201358a201357a200c57a2013572201295a2))))))
def f3 (i : Nat) : Nat :=
  (f3Chunk (i / 16) / pow28 (i % 16)) % 268435456

def f4Chunk (q : Nat) : Nat :=
  (match Nat.blt q 28 with | true => (match Nat.blt q 14 with | true => (match Nat.blt q 7 with | true => (match Nat.blt q 3 with | true => (match Nat.blt q 1 with | true => 0x100b0000f8b000100a000190700016070001307000100700007870001e85000140500013050001285000130400014020000029000000e | false => (match Nat.blt q 2 with | true => 0x1420000132000012a00001120000131f000141d0001e970001e910001e8f000110f000130d000100d0000e8d0001e8b000140b000110b | false => 0xf480200fc68200f868200f4682008868200b438200ac38200343820001ea80001ea600014260002222000192200013220001f200001ea0)) | false => (match Nat.blt q 5 with | true => (match Nat.blt q 4 with | true => 0xf558300fd40300a110300f468300a038300f588200fd68200f968200fd58200f958200f558200f528200b510200ad10200f4f8200f4902 | false => 0x9c3850034385002c3850028385011de840105e8400f578400fd38400f9384009d10400f4e8400f460400fc58400f8584009c384002c384) | false => (match Nat.blt q 6 with | true => 0xf8685008868500fc58500f858500fc50500f8505008850500d438500d038500cc38500c438500c038500bc38500b838500b438500ac385 | false => 0xf970500fd58500f958500fd38500f938500d510500d110500cd10500c510500c110500bd10500b910500b510500ad105009d10500fc685))) | false => (match Nat.blt q 10 with | true => (match Nat.blt q 8 with | true => 0xd438600a0386009c386009438600fda8500f9a8500fda0500f9a0500fd98500fd88500f988500fd80500f980500fd78500f978500fd705 | false => (match Nat.blt q 9 with | true => 0xf570600f558600fd40600fd38600f938600fd28600f928600f528600d510600a1106009d106009510600f4d0600f468600f460600f4506 | false => 0xac5870090587008c58700845870034587008450700cc40700a0407011de8600fda8600f9a8600f5a8600f5a0600f588600f580600f5786)) | false => (match Nat.blt q 12 with | true => (match Nat.blt q 11 with | true => 0x11088700cc88700a0887007c88700748870060887005c8870074807009c6870084687007868700a06070084607007c60700cc58700c4587 | false => 0x9cf8700a0f0700ace870114d070110d07011cc070110c07011cb870114b870110b8700a0b870094b8700a0a07013888701348870114887) | false => (match Nat.blt q 13 with | true => 0x135287011128700ed2870111207011118700cd18700a1187011d087011108700d508700a1087009d0870095087011cf870110f870104f87 | false => 0x115787011178701117070135587011158701354070129407011d4070111407010540700ed40700e140700bd4070135387011138700a1387)))) | false => (match Nat.blt q 21 with | true => (match Nat.blt q 17 with | true => (match Nat.blt q 15 with | true => 0xf558800f528800cd10800a110800f4f8800f4c0800f468800f1a8700eda870111a070115987010598700ed987011d88701118870111807 | false => (match Nat.blt q 16 with | true => 0xf4f8c0088f8c00f4e8c00f468c00f988b00f958b00f918b00f908b00f868b0135e8a00f5d8a00f518a00f908a008908a00f4e8a00f5888 | false => 0x8908d00f8f0d00f4f0d0088f0d00f4a0d0135e8c00f5a8c00f588c00f558c00f518c013510c00f510c00a110c00f908c008908c00f8f8c)) | false => (match Nat.blt q 19 with | true => (match Nat.blt q 18 with | true => 0xf4e900088e900135e8d0129e8d011de8d0105e8d00f9e8d00f5d8d00f5c0d00f980d00f978d00f578d00f938d00f518d009d10d00f908d | false => 0xa111400f4f940135f110111f11013511100a111100f8f910088f9100f8e910088e9100f8b910088b910135e9000f519000f4f1000f8e90) | false => (match Nat.blt q 20 with | true => 0xad11d00f4f9d0111f1a00f5d9a011df170111f1700f9297011d11700a11170095117011de9600f579600f4e9600f589400f559400f5294 | false => 0x111f1f0105f1f011de9f0105e9f00f9e9f00f5d9f00f5c1f00f579f00f519f011d11f010511f010de9d00f589d00f959d00f559d00f529d))) | false => (match Nat.blt q 24 with | true => (match Nat.blt q 22 with | true => 0xf57a500f58a300f55a300f52a30105ea200f5da201355a201354220129422010542200ed42200e142200bd42201352a200ed2a200a11a2 | false => (match Nat.blt q 23 with | true => 0x7c942024a882027a282024a1c2020105eb100f58af0129eab0105eab00f5dab00f5c2b00f57ab0135ea50129ea50105ea500f5da500f5c25 | false => 0x8ad038286d03828ccc38286cc38290c43828cc43828ac438286c43824a7c3823e283827ad82027ad42027ad02027ac02027ab82027e94202)) | false => (match Nat.blt q 26 with | true => (match Nat.blt q 25 with | true => 0x86f4d028af4c8286f4c828cf4c0286f4c0290f4b028cf4b028af4b0286f4b027a905027a885027e7c5027c7c502447c50286d838286d4382 | false => 0x86f518286f510286d910286d51028ad110286d11028ccd10286cd10290c51028cc51028ac510286c51027e94f827c94f824a88f8286f4d82) | false => (match Nat.blt q 27 with | true => 0x7af1a027ae9a028cfd98286fd98290fd8828cfd8828afd88286fd88290f98828cf98828af988286f988286f580286f578286f570286f5202 | false => 0x86d43837ad42037a9420386f5b027ae9b0286fda8286f9a828cf5a827ae9a828afda0286fda028af9a0286f9a0290f5a028cf5a0286f5a02))))) | false => (match Nat.blt q 42 with | true => (match Nat.blt q 35 with | true => (match Nat.blt q 31 with | true => (match Nat.blt q 29 with | true => 0x82bc3844a743843a2838486fda8386f9a838cf5a837ae9a8386f5a038cf588386f588386d51037ad4f837a94f8386f4d037a7cd037a7c503 | false => (match Nat.blt q 30 with | true => 0x84f4d0490f4a048af4a0484f4a047a785047e745047c7450444745047ac040484d438482d43848ec038482c038490bc3848ebc38484bc384 | false => 0x82f97847cf52847ac118484d510482d51048ec110482c110490bd1048ebd10484bd10482bd1047ad4f047a94f047e94e847c94e844a88e84)) | false => (match Nat.blt q 33 with | true => (match Nat.blt q 32 with | true => 0x7ae5a847ae1a848efd80482fd8048ef980482f980484f58047cf58047ae18048efd7848afd78484fd78482fd7848ef97848af978484f9784 | false => 0x8ebd1068eb91068cf4e867a8cc867a74c867a8cb067a8ca067a88a067a8c9868ec03868ebc3868eb838684fda8482fda8484f9a8482f9a84) | false => (match Nat.blt q 34 with | true => 0x8ad04078ac44078ab84079cac4078aac4079c944078a9440778944074a604078efd8068ef98068efd7868ef97868efd7068ef97068ec1106 | false => 0x9a8c60786d458774d45878ad058786d058778d058776d058774d05879a9050776905079c8c5079a8c5078a8c507788c507768c5073e74507))) | false => (match Nat.blt q 38 with | true => (match Nat.blt q 36 with | true => 0x9c8c6879a8c687968c687948c6878a8c687848c687828c687788c687768c687728c687708c687608c6875e8c68786d460774d46079a90607 | false => (match Nat.blt q 37 with | true => 0x82c068776c068770c06878ebc68784bc68782bc68778bc68776bc68772bc68770bc6879a9068794906878290687769068770906875e90687 | false => 0x8a8c987789488770cc8079a908079c8c8079a8c8078a8c8079a848079a78807887880784d468782d468772d468770d468770cc6878ec0687)) | false => (match Nat.blt q 40 with | true => (match Nat.blt q 39 with | true => 0x8e9cb078a8cb078e78b078878b078e74b078c74b078a74b078874b078674b078af4a078ad0a078ac4a078aaca078a8ca078a7ca07847ca07 | false => 0x7894d07847cd078674d078a8cc878878c878a74c878874c878674c874a8cc078c74c078674c07847cb878c74b878674b878ec0b078ebcb07) | false => (match Nat.blt q 41 with | true => 0x789518784d4f8784bcf8786d4f0786d4e878ad0e8786d0e878ccce8786cce878cc4e878ac4e8786c4e874a7ce8784a0d0778a0d0772a0d07 | false => 0x86e1a878ce198786e19877af178770cd58784d540772d540786d538774d53878ad11878ac51878ab91879cad1878aad1879c951878a95187)))) | false => (match Nat.blt q 49 with | true => (match Nat.blt q 45 with | true => (match Nat.blt q 43 with | true => 0x7ac0b087a78b088af4a088af49889cf48088af48089cf45088af45087af05089d1da879b1da878709a878705a8784e9a8782e9a8786e5a87 | false => (match Nat.blt q 44 with | true => 0x9cf95888af95889cf92888af92887cf12888ad11088ac51088ab91089cad1088aad1089c951088a9510878951088af4c884a88c088af4b08 | false => 0x7a7cf0a7c7ce8a447ce8a8af9a089cf5a0886f5a087af1a088af98889cf58087af18088af97889cf57887af17888af97089cf57087af1708)) | false => (match Nat.blt q 47 with | true => (match Nat.blt q 46 with | true => 0x7ce9a8b8af9a0b86f9a0b7cf1a0b7ceda0b7ce9a0b9af918a8af918a7cf118a7ced18a9c8d10a9a8d10a8a8d10a788d10a768d10a94f4f8a | false => 0x708d10d608d10d5e8d10d84f4d0d7ae4d0d86f9a8c7ce9a8c86f5a0c7af1a0c7ae9a0c9af918c86d510c74d510c86f4d0c7ae8d0c86f9a8b) | false => (match Nat.blt q 48 with | true => 0x8ebd10d84bd10d82bd10d78bd10d76bd10d72bd10d70bd10d9a8d10d968d10d948d10d8a8d10d848d10d828d10d788d10d768d10d728d10d | false => 0x96f918d94f918d84f918d82f918d7cf118d7ced18d7ce518d7ce118d84d510d82d510d72d510d70d510d8ec110d82c110d76c110d70c110d))) | false => (match Nat.blt q 52 with | true => (match Nat.blt q 50 with | true => 0x9a8d1109af90909a8909094f4f909af8f1088f8f109a88f1084f9a8d82f9a8d7ce5a8d7ae5a8d7ce1a8d84f580d7af180d7ae580d9af918d | false => (match Nat.blt q 51 with | true => 0x8688e9686f5a1484f519484f511484f8f948488f947ae5a907ae1a907ae18907cf58107ae18107cf57907af17907ae57907ae17909af9190 | false => 0x8e9d1168ef8f1688f8f168cf4f1686f4f1682f4f167cf4f167aecf167a8cf168e88f168ef8e968cf8e9688f8e9686f8e968e88e968c88e96)) | false => (match Nat.blt q 54 with | true => (match Nat.blt q 53 with | true => 0x7aecf1988f8e9986f8e998ef4e998cf4e997aece997ae8e998688e998cf8e9786f8e978c88e978688e978ef97968ef93967cf52968ebd116 | false => 0x7c94f9d4a88f9d9b1de9a8705e9a82f5d1a86f5c1a86f4f1a7a7cf1a86f8e9a8ef4e9a8cf4e9a7ae8e9a8688e9a88f8f198ef4f1986f4f19) | false => (match Nat.blt q 55 with | true => 0x86f5a2f8705eae82f5d2e86f5c2e86f5a2386f5c227ae9a9d86f9a1d8cf5a1d7ae9a1d8cf989d86f989d86d511d86d111d8cc511d86c511d | false => 0x86f5c348cf5c3186f5c31))))))
def f4 (i : Nat) : Nat :=
  (f4Chunk (i / 16) / pow28 (i % 16)) % 268435456

def f5Chunk (q : Nat) : Nat :=
  (match Nat.blt q 8 with | true => (match Nat.blt q 4 with | true => (match Nat.blt q 2 with | true => (match Nat.blt q 1 with | true => 0xf558200fd40200f940200f540200a110200f468200a03820001ea60001ea00001e8f0001f0e0001e8e000110e000150700007070000029 | false => 0x99105009510500f468500f458500f450500a03850098385009438500f538400fd30400f9304009910400f4584009838400f540300f5682) | false => (match Nat.blt q 3 with | true => 0xf588500f580500f578500f570500f568500f558500fd40500f940500f540500f538500fd30500f930500fd28500f928500f528500a1105 | false => 0x98f8700a0e8700986870080687007468700a05870080587007c587008050700f5a8600f540600f538600f528600f5a8500f5a0500f5985)) | false => (match Nat.blt q 6 with | true => (match Nat.blt q 5 with | true => 0x111a87011d9870111987011d90701159070111907013960701356070115607011160700cd60700c960700a130700a100700990070095007 | false => 0xf518b00f510b00a110b00f508b00f900b008900b00f8f8b00f4f8b0088f8b00f468b00f508a00f900a008900a00f598800f54080115a87) | false => (match Nat.blt q 7 with | true => 0x9910d00f508d00f900d008900d00f4f0d00f8e8d00f4e8d0088e8d00f540c00f508c00f4f8c00f598b00f588b00f558b00f940b00f540b | false => 0xa111d0111e9a011de970111e9700f541700f529700f54140135e910111e9100f541100f4f9100f4e9100f4b9100f4e9000f538d00f930d))) | false => (match Nat.blt q 12 with | true => (match Nat.blt q 10 with | true => (match Nat.blt q 9 with | true => 0x11192200a132200f942000f932000f92a000a112000991200095120011de9f0111e9f0105e9f00f931f009911f00f559d00f941d00f541d | false => 0x8af588286f58827a94f827a7c5027a942020129ea80111ea80105ea800f5da800f5c2800f57a80135ea50111ea500f5da500f54230111ea2) | false => (match Nat.blt q 11 with | true => 0x90f57848ef57848af578484f578482f57847a94e847a7450486f5a8386f5b0286f5a828af5a0286f5a028cf598286f598290f58828cf5882 | false => 0x8af57888af57089cf55888af55889cf52888af52887af12887a94c088af57878ef58068ef57868ef570684f5a8482f5a848ef580482f5804)) | false => (match Nat.blt q 14 with | true => (match Nat.blt q 13 with | true => 0x9af510c86f5a8b7ae9a8b8af5a0b86f5a0b7af1a0b7aeda0b7ae9a0b9cf518a9af518a8af518a7af118a7aed18a7a7ce8a8af5a088af5888 | false => 0x7ae178d9af518d96f518d94f518d8af518d84f518d82f518d7af118d7aed18d7ae518d7ae118d7ac118d7abd18d86f5a8c7ae9a8c9af518c) | false => (match Nat.blt q 15 with | true => 0x82f5a8d7ae5a8d7ae1a8d8ef580d82f580d7cf580d7aed80d7ae180d8ef578d8af578d84f578d82f578d7cf578d7af178d7aed78d7ae578d | false => (match Nat.blt q 16 with | true => 0x8cf4e9786f4e978ef57968ef53968ef4f1688f4f168ef4e968cf4e9688f4e9686f4e9684f4f949af51909af50909af4f1088f4f1084f5a8d | false => 0x86f5a9d86f5a1d8cf589d86f589d7a94f9d86f4e9a88f4f1988f4e9986f4e99)))))
def f5 (i : Nat) : Nat :=
  (f5Chunk (i / 16) / pow28 (i % 16)) % 268435456

def f6Chunk (q : Nat) : Nat :=
  (match Nat.blt q 1 with | true => 0xf530d00f500d00f4e8d00f540b00f500b00f4f8b00f500a00f540500f530500f528500f530400f54020001ea900014a20001e8e0001487 | false => 0xf542600f542000f532000f52a000f531f00f541d)
def f6 (i : Nat) : Nat :=
  (f6Chunk (i / 16) / pow28 (i % 16)) % 268435456

def f7 (i : Nat) : Nat :=
  (0x1ea9 / pow28 (i % 16)) % 268435456

theorem chk_1_0 : checkRange 0 f1 (fun _ => 0) 0 0 22 0x0 = true := by decide +kernel

theorem level_1 : ∀ i < 22, (∀ x ∈ decodeSet (f1 i), x < 81) ∧ ¬ Coverable 1 (decodeSet (f1 i)) := by
  have hlt : ∀ j < 0, ∀ x ∈ decodeSet ((fun _ => 0) j), x < 81 := by intro j hj; omega
  have hno : ∀ j < 0, ¬ Coverable 0 (decodeSet ((fun _ => 0) j)) := by intro j hj; omega
  intro i hi
  exact checkRange_sound 0 f1 (fun _ => 0) 0 hlt hno 0 22 _ chk_1_0 i (by omega) (by omega)

theorem chk_2_0 : checkRange 1 f2 f1 22 0 172 0x130180340680c02a0500900e0180280200401d0540940d0120540a01201c0300500380803a0540482904a04c140260480700d01402401c040060040080100202a0a40c82a04c0480302401002c0502200205c1200b044020100110080780780002c01c0800301c0300600a02a084148170440780700a00c0100e82104a07c1101602002801000 = true := by decide +kernel

theorem level_2 : ∀ i < 172, (∀ x ∈ decodeSet (f2 i), x < 81) ∧ ¬ Coverable 2 (decodeSet (f2 i)) := by
  have hlt : ∀ j < 22, ∀ x ∈ decodeSet (f1 j), x < 81 := fun j hj => (level_1 j hj).1
  have hno : ∀ j < 22, ¬ Coverable 1 (decodeSet (f1 j)) := fun j hj => (level_1 j hj).2
  intro i hi
  exact checkRange_sound 1 f2 f1 22 hlt hno 0 172 _ chk_2_0 i (by omega) (by omega)

theorem chk_3_0 : checkRange 2 f3 f2 172 0 14 0x2500889001e0480600a0080e8000000f40443900f024030050040700001500b0160d80883401a048070080080a801002002034140050240980801001a0800281202002c0701e0300040080100200400801002004008010020040000100200406816294520909442845000712c0183e06f00210c0001402000203410005024050080100200400801001c04006010020008080000200400c00802c018020c61843005e0ba16c0385a00c15c2b00107c0000980a01115e0440180301e03c0780f0020040080d01a0340680301a0380600c0180380800e0182b8010020040300000000003808005008048118e51f600c0780f1b20447082f20e2dc088e729e0040080101a0340680d01a0340280500a04809012024048090f61180780580201c084658f900600c0780f01e03c0080d01a014028120240480908502221c0781211e4ac5a81119e4b40180f00a0487902c0340240000c04e014158970020141d83f0060141e80412c0101f03c0040e80002a008098030110242c40880502426c0880d0240280500a014004050050141140880f024028040080100200180800a020040080040000000000405003004 = true := by decide +kernel
theorem chk_3_1 : checkRange 2 f3 f2 172 14 20 0x3c01602c0580300a024058060160642905000603c2704c0941200080d08c014090100160381d09519235c018050122ac030440001a40886b01e0480600a008160000000000000009d00c45c0891901e0480600a008158000000000000013902251c0781201802802054000000000001ee0447c80f024030050040a4000000000004d40894301e0480600a00814000000000000000000000000000000000c0180300600c0180300600c01800000000000000000009d81129203c0900c01401027000000374088df01e0480600a008130000000004cc0894101e0480600a00812800000000000000000000000000027a044a580f0240300500409000000000000000000000000000000100200400801002004008010000000000026e044a200f0240300500408c00000000000000000000200400800f020030050040200000000b01602c0580b0160280200b000000000000000000000000000000000000000000000000000013e0224d80781201802802044000000000002500449000f0240300500408400000000000000000c80222f0078120180280203e0000000000000000000000000000010020040080100200400801000 = true := by decide +kernel
theorem chk_3_2 : checkRange 2 f3 f2 172 34 28 0xfe2782e0331823ac0080501615c0309c078024048090020140480900c0243f89e1380240602a06e3147680100a02c2d806134008010022060448e80d0240380400415000801002004008868112a60340900e01001053002004008010020040080100200400c0180300600c0180300600c01002004008010020044440895401a0480700800828801001004008858112900340900e0100105000200200801002004008080100200340800e010010080020040088281125e0340900e0100104f0020040080110f0224980681201c0200209c00400804809012024048090100100480200400801002004008890112200340900e0100104d00200400801002004310088c201a048070080082580103a0120240788800a048080090182003f0030060040688600a0483e0100201d8390120180100001102203c370050240400480c0c81800180300203435005024178080100b802c058380120243000a014010010590100203c0110e80340900e0100102e0020041602b04207024c5f8d3006014048a700c1500c84011a2bc6580300a0244c8060a40040684600a0481f0100200400180501204003010 = true := by decide +kernel
theorem chk_3_3 : checkRange 2 f3 f2 172 62 35 0x880c52140480600400004408811012030088111da420070f20040684492f24c024060342201e48208024e040419152480240603221c1e4871020c800c0795200a0480808b2604880480c060430388fe1e8188788241f8004068ca1de0807c00101a3e00281215c040080101623b80900c008000088110140280500a0100284d80a0140280500a0080000880a0140280509d0140280500a01429c050010140280280a0140400500a0140280180a0140280500a002028050050140280500a0142ac0500a0140285480a0020346f0050242b0080100100200400801002004008010020040080100200200200002022808010020040080080000880801002004043010020040080101540400101002002808010040040080100202b808010020040080100202d80801002029808010028040cc02c14c040ca0ee2d03e043010350030041801dc600b20bc154040d200c0105f0b815812c040d000c0105b0960160200580600802c1f0090100240300401209820808198018020b016005029808194018020ae0c22a04e05c0622fc7480100a02c2a80614c004068a000a0484b0100200400080501604003010 = true := by decide +kernel
theorem chk_3_4 : checkRange 2 f3 f2 172 97 73 0x2020a0399181a40983b8b20501a81305e0440881201e2520900e01a038060218161a80900e01a0440780d01802c0900f07524e470370251fa5580180f1d05483691b2341b0718e22a01cc909180d4004068d228c04008010020038080100040400080d294014090c602004008010020040060040000440880101a044028110220400801001c04001010002034a4005024308080100200400800101a5180281217c0400800c0000040694400a0485e0100200400800101a5080281217404008010002034a00050242d8080952780449d13626803c9901201c0307b00a1b80100100003c07c7b93500603c9d8dd2664f40080d26e014090100160384a13e1924d80900c0080000881102200c078110220440880101a0440281102002c070110221ec949160d00947e95600603ca90e32a05300080d28c01409010016038491381ae030000211f250c0180f29237ca094b002034a20050240400580e1204d8339152281984588a2600040692c00a0485a0100200406092002403002000022044088111d6478070f40040704492f0e84986a80c00021c968722400040691800a048590100200400803721c034820081002048290f0120301b112 = true := by decide +kernel
theorem chk_3_5 : checkRange 2 f3 f2 172 170 299 0x1b4408740d41a8338670d21883085e0ba1682d05a0b213c45c4909329a34c8c95711c23c958b511c4546792d2502388a0f11fc3d0790921c4228498d31765586188a1c631ca60861222f442095192210948d711422c411222384608b0822042ac548e81a41f05c0b21142483808d1ee3cc808e51f64d4848bb2864ec619542921e86e8781b21d8568741c21c86f86c26641c7394f1a2504a713d18e52c3509129442c5e948288508a006812a4f06493a1ae4d0361320f42143c0810ec1f43a0890e421c3308f256198828b525e33c9692e2584a8628ed214420830662083bc800fa1ec3c8668ee12e28c5089915627c528ec1cc3903b0b90dc380350de0d0370320d81ac338660c818c310610bc1742d02f0ac154290510a00b81fc4f09812c1e84a072120198470621181b84406a10c1a0420641001803f05e0f81682b05009c168260580ac128240460841002103e0780e82c0560841682804e0701302504808c1001f03c0700e81b0650681bc1910323a0c0188e906448cab8e51f60d86c8341c20c86d8301c60b8179071ce53c1706d2364a48d0f10581c47f0f61e80c07102a0c22a01608c0602281b0780681d01706c0581881505c = true := by decide +kernel
theorem chk_3_6 : checkRange 2 f3 f2 172 469 72 0x9212423c4688d12b25c4b09511e2344108a1141e83a8750e92ac3887194c2523ac6d1222384608b0ed = true := by decide +kernel

theorem level_3 : ∀ i < 541, (∀ x ∈ decodeSet (f3 i), x < 81) ∧ ¬ Coverable 3 (decodeSet (f3 i)) := by
  have hlt : ∀ j < 172, ∀ x ∈ decodeSet (f2 j), x < 81 := fun j hj => (level_2 j hj).1
  have hno : ∀ j < 172, ¬ Coverable 2 (decodeSet (f2 j)) := fun j hj => (level_2 j hj).2
  intro i hi
  by_cases h0_3 : i < 62
  · by_cases h0_1 : i < 14
    · exact checkRange_sound 2 f3 f2 172 hlt hno 0 14 _ chk_3_0 i (by omega) (by omega)
    · by_cases h1_2 : i < 34
      · exact checkRange_sound 2 f3 f2 172 hlt hno 14 20 _ chk_3_1 i (by omega) (by omega)
      · exact checkRange_sound 2 f3 f2 172 hlt hno 34 28 _ chk_3_2 i (by omega) (by omega)
  · by_cases h3_5 : i < 170
    · by_cases h3_4 : i < 97
      · exact checkRange_sound 2 f3 f2 172 hlt hno 62 35 _ chk_3_3 i (by omega) (by omega)
      · exact checkRange_sound 2 f3 f2 172 hlt hno 97 73 _ chk_3_4 i (by omega) (by omega)
    · by_cases h5_6 : i < 469
      · exact checkRange_sound 2 f3 f2 172 hlt hno 170 299 _ chk_3_5 i (by omega) (by omega)
      · exact checkRange_sound 2 f3 f2 172 hlt hno 469 72 _ chk_3_6 i (by omega) (by omega)

theorem chk_4_0 : checkRange 3 f4 f3 541 0 6 0x88380700d0038070600c01802e05c0b81702e05c0a81502a00a0140280500a0140080100202004008010020040220340881201c00c0180300600c0180100200c018030060020180300200c0180300600c01802006000018030110700d81a0070640c01702c0540141400101009812006034e3c5087b696e4450802004bf17d2f60b800450ae80043b06b0d41a001c0400414c00020022262630c506f00e01cc40a330c600bf0891b25f0bd02d0660bc0280500a0140280500200400808010020040080105a8b00ec02c050030062804f09d0db2704d09900700e4c05f92e258384951121f43b00800501c0040400a7d62cc540a8130260000001c8380658dc1b4360030cc0082d05106a0b40980900c01a2045a8630d601c0380700e08c1380700a0140280500a01403004008010030b400c0104006a0081880202600c0880300c0020000401301020c590010101dc3e80501005c5808715c094028010101042280701010c2f8a010a278328070020203c8900c00780e01a02802801000 = true := by decide +kernel
theorem chk_4_1 : checkRange 3 f4 f3 541 6 8 0x788f16e19c3680700e01c0382900a01400801010020040085fa16d80807010ca99432619ac899006900e004043142c03e82f01a00801091ada5b0aa004008010150030040080112e254474020030044708d0040540088b804004000000000880940600c0182b03e02b04e00e01c8a96f5ac0200326801015003266010018020b60100191500411c000000004341282504a4047f00405400c7e8040060300381f84c00a01494ad25a0158038075781615c1795642242c2b055c0b41982f00a0140280500a0140080100202004008010020042524003d82904a00c0180788f16e1582b00700e01c0382900a01400801010020040085041613d0070109e13b2720b09b93605600e004042502ac3d028018008010a58012ca9281f8013727042b00137a001040003446802519e030550001440040081f03c040061c489b0f61fc4d09a0040098808b61c1700089b0fe008770d31be39c038080082a8000480740441c03606c0d81a03400e01c190320640c8190320440681102a00a0a00080803ce344f87b1982604c0020041682d05a0b40042d05a0040306a8e21b801c0400415000022026 = true := by decide +kernel
theorem chk_4_2 : checkRange 3 f4 f3 541 14 5 0x2b8740cc129e68ab1542a8c188b77c0c4008ab092124248020040087f0bb1be3ac0280800c2680007e0e44cda23401b6cf83807000e01c3706e0dc1b83706e0c41880a03500a1b0008080c0f44578a8150288510a2062004510e41b028801002004030608e21c0014040061300003e06a0e41c82b8740e40d4028570d81b02e868094f3c568a414861446bb4062004569d93be794010020043f05e8ca1900140400612c0003d06601e23c5b8670da01c0380700e0a402805002004040080100202e85b0ba01c040680d01a0340680d01a0038010101880a0620c8070020040080100200400801000804008010020020040080200400801002004008010000040084d5a133c674ce03807000e01c2b86e0dc1b83706e06a0143606c0d80040080801015c3506a0d41a83505d0d019832004028f4c58bd9162625bdbaa062004589dd3c67a4010020043e8610c017c014040061280003b062 = true := by decide +kernel
theorem chk_4_3 : checkRange 3 f4 f3 541 19 5 0x4008010021160043f87f07600424849092004248000fc000240480901201d07e0002280100200400801002004008010020040080100211a004b188d07a004db88d0ea004dd8000f4000df07a0cc6d01007a0005200112d704e003780700ede851b78110220440881102201683305e0140280500a014028010020040400801002004008100200050860c00180300600c018030060020180300600c0180300600c0180300600c0180300600c018028060020180300600c018030020000180788f16e19c3680700e01c0382900a01400801010020040085f616d7f807010c9db936c19ad99b206900e004040801000284201e0080100200400801002001008010020040080100200400801002004008010020040080100200100801002004008010010000084edbf37c68201c0388c6ecdd0440881102204408806e014028010100204308610c0180300600c01803305612c34440066e0db9b53686c4d81af08810c0184208410821003004008010020040080100200400820805153168fb05a37f7d0f9800808168d35a88b6168f91f10b6150635e53c8706f19e203900a2d8008081685802389211c00800080 = true := by decide +kernel
theorem chk_4_4 : checkRange 3 f4 f3 541 24 6 0x40080100200400801002004008010020010080100200400803c478b70ce1b40380700e01c1480500a00400808010020040d60b634003808652359b98cd73234034807002021fa16a2242841100400801002004008010020040080100200400803c478b70ce1b40380700e01c1480500a00400808010020042f90b63180380864b050468ca72e31834807002021f91682202741000417cf2c5f06f00e01c610a317c5fc61089180f745f02d0660bc0280500a014028050020040080801002004008010fd18a1121621880300600c0180300600c0180300600c0180300600c0180280600c0180080100c0180300600c0180300600c018030060080180313d808df46dc02686d14038073162fe003811c2ff9fa3142d40e4028b6002020400da7d23686d00700e32c6e0da0b232c6c0d81b03601b80500a0040400814a2bc5780600c0180300600c390700da1b0018660cc198330660cc1983305780613e27c4f89f00c0100200400801002004008010020b30182d0298ac1481386980763634c3980774c000000001141c81d03a0745988707f1541444e0960982ec029711760ec028000e4b880008a0e4b700004a0744082489a = true := by decide +kernel
theorem chk_4_5 : checkRange 3 f4 f3 541 30 5 0x321e18c80de01c038bd146320bb8bd112329ed8c805a0cc1780500a0140280500a0040080101002004008010021fb31622c2b43300600c0180300600c0140300600c0180300600c0100200400801002004008010020040080100788f16e19c3380700e01c0382100a01400801010020040085da16d77807010c7607b5718ae4e0886700e004040bc2d82f04b83c0080100200400803c478b70ce1b40380700e01c1480500a00400808010020040d30b639c0380819c338458cd19c338348070020205c0b817426c1d00400801002004008010020040080100200400801002004008010020040080040200401e23c5b8670da01c0380700e0a402805002004040080100206a85b1b801c040cc198330660cc1981a4038010102d05a00c13e098020040080100200400801002004008010020040080100200400801002004008010020010020040200400801002004008010020040080180300600c0180300600c0180300500a0040080600c0180300600c0180300600c0180300600c018030060020180300600c01803004 = true := by decide +kernel
theorem chk_4_6 : checkRange 3 f4 f3 541 35 9 0x280500a21025880002000d686408c18cd60440066ac010403540c0b780f14801401407001010030290061ec3c80802d0660841483705e0181f8040720c41a83f0300fc0800c1ec040028f001ca794c0c752ca51490064d00105b2320947f00c14601c3c8260f0004000052244402310f21c1100190d004100860251f4030510050591963102a14317222c6dc380e61cc038071d42ec7508b1be3a85d0ba1a40ec028e6002020450de00c018030061d62e45c86f00e01c5d8a31d63a05d8891b23a07402d0660bc0280500a0140280500200400808010020040080102e05c0d21561c80300600c0180300600c0180300600c0180300600c0180300600c01802806002018030e078e3803780700e304518e01b0304448d81b03601683305e0140280500a0140280100200404008010020040081682d0060af0d4018ba8bd17a3206442e1883100300617cfe8643580cc1986411c11a31804004000080068b50aa3146d82700a154628dd0b63342c0ca242c65fec24010020040c400c01002004814fe1ea00800c011e03b0010288023a80100100000000022033020040080b91180ea2900380700e01c0380700a01c0380700e01c03807 = true := by decide +kernel
theorem chk_4_7 : checkRange 3 f4 f3 541 44 12 0x701000a41951ac118ea5d64aab00c9b4020b656e15d3d8282a00380700e01c0380800520831c638c718e31c6380618e0105b0c70d831c140c701c0380700e01c040029021cc398638e61cc398030ce0082d87306c1cc0a07300e2444808b0f627c2e49b07300e3a8930e82480400280e002020060ab00c3f8690d21a4340690d200c338020b81a41c8690221a43480107a00a038008080182b403116210040080100200b4198210520dc1780607a0101c83106a0f41003d0200308b00a1f80400290001c0380700e01c03a100c818e31a0f41c00d040020b675c1997702029c0388a0bc2203d0398071d40040400c23c3388d09b0083b85d0ba1742e85d0ba00c2e8020b81741885d03a1742e88610a2103c84d1020040000507e0e43f8248490921242484900c124020470921242483a092124831042003c02489a7443add00e773c3a0030ce008239c20725c40e8a61020144302890600400152ac5118a6d6588800c9cc0208057615d3f81e2940280500a0140288509c2080080008c1182304608c110018460041002303008c03c2300500a01402805049134408010001142284508a1142200308a008200450601140784500a = true := by decide +kernel
theorem chk_4_8 : checkRange 3 f4 f3 541 56 24 0x30090290520a401c0400409c000210180300600c0020000791305843c01c0400409c000d10180300600c0050100180c0000300702504a09401c04004094000250180300690305840801c0400409c000cf0181be3ac04006000050ca19000a3384d15e3386605e95c1762ecc918e00c2e00a0ee3346586415a1d63acbc1762e4560c11661d03a00b16409e0580b01602c588528160f40580b01615a058b716c2d0558b80ee1702e0b21620f4550ca08b3240ec008160920083f07e0286702a99a00a020030510005902b8140280500a19818a6580280800c270001620e8050aa0160a4058ae0582b401404006098000aa014094050a80c729c5181d80529839873012032014a80010105282c81207a014a7001010520090120243100914a118520a2049134530010001142281f80528c00404144024150091281924607c13e1724d83980721c3a8750c91ce3a87400619c0105c0ea0dc3a8190ea1d40400280e0020200604f00c488860190320640c8190320180c8040320640c819032064080100200400800501c0040400c14a0189010a04208410821042084030210080841082104208410810 = true := by decide +kernel
theorem chk_4_9 : checkRange 3 f4 f3 541 80 18 0x200480900c0a71522b403808008290000420400781f03e07c0080028d0aaa6c0380800814c001c003c0780f01e03c0f01e03c0040003d80211823046007010010460001180780f01e03008010020004001ae0ca18c01c04004148000df01e0380f81f03e00a0200303e0000f82b8550ae01c040040a60002b81c0380700e01c0780f01e0050100181e0000781d0010740e81d0038080081d0000740380681f2910aaa840380800814c001b80340680d01a0340f03d80266c315970070100105600036c0680d01a0300818f0ca18c01c04004148000da01a00e0600c0110300e16c05816e01c0400409c00023018030060088180300d96705859001c0400409c000d801803001c0c0010100600c0040300601a0560ac1582b007010010270000ac0600881803006003818064b182c2c000e0200204e0006b80c018060af82c2b600e0200204e0006b00c0180300b95a05855401c0400409c000d50180220600c01800e0600c0180300b15305854401c0400409c000d401800a06000808030060030180300a81182705201c0400404a0001f8180300600c0050300a06885852c01c0400409c000d3018 = true := by decide +kernel
theorem chk_4_10 : checkRange 3 f4 f3 541 98 16 0xb81702e05c0c01e07b00505c62c1d00e020020ac0007781702c0220e01b03400e0c81802e07ca3c2aa9f00e020020530007681602c0580b0160110700d81a0070640c01703c0f600a0d8c584201c04004158000ec02c0500640283e1a21554b807010010298003ac0a0140280500a0108050781ec010c718a31c038080082b0000c70500901f04f09e13c0380800813c00042048090120240480f03d80214a294528070100105280008409003820040080100110400e01c038030ff45a8b700e020020a400011810020040080100110400801b03606c0d81b01885432863007010010520003a80801000704000404020040010100200680d00c05c0ea1ac368070100103a8000ea08008820040080038200640c80c42819431803808008290001d204008018030030edc518c600e020020a4000740100200400b81701884c328630070100105200039c08008820040080038200400801002c058062110ca18c01c04004148000e6020004080028200020201002000c0801002a0540a80c02304e0a4038080080940003d0400801001e034080028200500a014028050060688ca18c01c04004148000e5020 = true := by decide +kernel
theorem chk_4_11 : checkRange 3 f4 f3 541 114 18 0x1c838c710d204863620dc487300226c3f802090700461be344120240480040004508a1141cc008840fe008241bc3741e8d00480901201d8010841200107e0fc1f8398010f01f8010483706d8da19e090cd045b300e60042f07f004120039aa21a690232da10223c2b0010a09100104607e014d3001010688220540a81502a0010a015001044340108290520a4148008500a40082110d08c6c02b00735c6b0d51a807e014d30010101102100633c1014828c510158008504840082003806c0441f2530aa2dc0380800814c000460700e01c0380700d80883c0f6009fb8b516e01c040041580002303806c0441c03e50e1554a807010010298003dc0d81b03606c0d8088380781ec0141918b07c038080082b0001ec06c0d0180070640040402607c0101f03e09612c2584b00e0200204b00012c1a0320220e01b03400e0f94585553201c040040a6000f50320640c8190320220e01b03400e0f03d80219231464807010010560001920c81803e46215519807010010298003cc0c0180300600c01e07b004eb451baf00e020020ac0007901802e0600f94285552601c040040a6000f002e = true := by decide +kernel
theorem chk_4_12 : checkRange 3 f4 f3 541 132 16 0x7b8f61d43601202304865a22dcf87300226c3f8020907a8649d235c1202304809001c240ea1163a8398011361fc010483cc790e81ac090c4c45b850e60044d87f004120f01de39c6a8240481d02247407300226c3f802090768ec1cc3501202304809001c240480901219988b7461cc0089b0fe008241d618e728d303b00a1207308b1cc1cc0089b0fe00824044032014eb0010107002c8590b212c0084d0b20082204237813c2784f0960042684f004108210420846e8528a514a19c008910f6008210401e6118f704b00e7a8f31e03b4064029d60020202204200c6e103a2745a12c0084d42e00820040080100848463d819c038c93c8778ec02100a31c00808088108031b663ed75ca86700225c3d802080100200400801202304809001c240480901201d80509000404044084018240d2116348398011361fc0104000e738521c22167102304608c1198c88111e1d40089368e0082303d00a7280080837c1102204418823462075002274620020881e8210420842b4468ad0ea004488ad004108858463a81d4039d23a0738e603d00a72800808088108031b40801002033711ae943a80113ad4c01040 = true := by decide +kernel
theorem chk_4_13 : checkRange 3 f4 f3 541 148 25 0x1302604c098010260000947cc4a04c0981300004a08e2482604c0980080004c098060260000946f43c84c09800025043120131140f01008002384c11c239040520981480100010c148d105009814001000108140a21c90988a0010001042081f805420004042080a81502a03f0021482a0020f8150d00500a01401f8010a0140010780a08390607a0a0010aa19d4c89881f8010a47cc010760ec01c25001010128250040941282b0560ac014040060980002b0700941282504a09401c250bf0b0b080280800c130002120dc1282504a06a0142529c0b0a600280800c130002100d8128252800b09f00280800c1300020e0ba1280204a0941293a0584e00140400609800106068094128280500a001404006098000280640941282504a0040011105844001404006098001040600946782805e0a001cff001010150280043f07d82b05c0ac0fc029fc002020fa0540b4150240480100180004809012002848090120f91f017a6c85d88b17618c008950ee008240461e67210088111e12c0084d4160082304608c118849c662e2044786700224c3d80208c1182304608c120240b910223c398011261fc01046 = true := by decide +kernel
theorem chk_4_14 : checkRange 3 f4 f3 541 173 27 0x140280080080000c058132140038500a0140230930a00fc028500020202804413e14028042122140280500a0140038500a01402803f00a140008080a0140030500802842805817c6745e0054b4130fc2804e82f4280042b8308610be4c8980040040000602c0580b0140020581801613125e00c940250f44f89c0640500085685f0be0ec148290520a00100b0b10a40fc02a58002020410121661502a2520720144725801c2d85b24e002140011a409c8d8a588310620d260080080000c04e0b004c590580b0920b287b00a900261f609c8f0010004446c80c15c0ee1dd252460100100001809c160010000b01600c0580fa1602704e02e1380284e0981383b8b009c1380084e0041392508709c138270080080000c05815c1381280509c0040404e0a82a02704e09c1382700709c1382704e04a014270010101382700609c9085304e062015190010108602a0a20a81300004a37217c2604c0981302604c09801c2600800c0102604c098000250180980002504114013026001098008260000947044284c098130040040000600004a08a278260070980040404c0980102604c0001282b0650980fc0284c002020260000941504c04c = true := by decide +kernel
theorem chk_4_15 : checkRange 3 f4 f3 541 200 19 0x540a81502a0540a801c2a00800c0102a04e0a80002501801808c028d1002021130d50a81502a0540a80182a0540940301680553c004042241c81502a0540a8150028540981505f83f00aa70008084443042a0540a81502a0080080000c0580b009c028580020202c0e20a81502a0060a81280603300aa60008084403802a0540080601480552c0040421e1b81502a0540180dc02a940020210e0da0a81502a02f00aa48008081103602a0520a4148290520a401c2900800c0102904e0a4000250180a4858538520a4148040040000602c0a90a40fc028520020202905415e1494828e0b0a286828600ea1004006008948272300001280c0f6246b616705600eb195f2b454c08c028d10020202a05200c8186b0d651834004004000060068580b0158038580b01602c02700a160008080a8148030581a81614400403003c5bac80ac01d602b6554a881480552c004040540a4019020d01a09f93d0080080000c0580b61613926c010010000180081602c05819a16003a6a0020202a050008969200040ac1582b0690ac0fc02a680020210d0040a81502a0cc0a8140280500a00142804c0a06c84a850 = true := by decide +kernel
theorem chk_4_16 : checkRange 3 f4 f3 541 219 24 0x5e0bc140da09d0bcb6d8c316400c687f0b81709f464af03fc47c5cb0a0b801d720ea1d49ec63aee3f80ec02ae21cc39941af85d87e88f8b9614170038ea60c3a18103b00a398008080b42ac032dc1a434803af00020202d09d008ba97305c0b81583a85c07a01577001010b782d05a0a83102d281178ba8fc05c00e3a8008080b4bd0672f2136010af0ba17483c3dae63ec2a9720020002282403a2bc1fc3fa7f118b78fa049134b88010001142282804600eab083a4e11e23c4780403001d5500f4982dc5baca590020020000301602c00d0b01606d8580ac004280020ac01d62001010150280044c8928308560ac1580305609415803ac20020202a0500082f92406f0ac1580201800eb00008080a81400226048c1b42b05858466c648054d4130ff1155acb302b0074782fc5fac4580020020000300342c0580ac01c2c0e10b0ae95b0080080000c058146161560010a0008d52ba46c22444889554020020000301602c0d90b0a91510080080000c00d0b01602b0070b01602c0581ca1615029e0b0a614b29400ea48040060082d8272320001280c00e0a83581180545834468a9a52c020020000301502c02700a1606e858 = true := by decide +kernel
theorem chk_4_17 : checkRange 3 f4 f3 541 243 18 0x1e83d07a0f41f83f07e0760143f07e0fc1f8c888b7be0ec008ab0920083d03d00a1e8008080f41f03e0541882346203d0022b4620020f41343c07837425c4b897042004488970041e03c0780a01e84e88d13a0f40089113a0083c0760ec1d86487c5ced203d0780085885e0bc178084008a51780083b0760ec1d83b07300e1f8008080f81f83f07a0f00103f0ba1162e81d801156124010760ec1d83b07a0f41e83c0040f466446be107a004569f10041d922b460f48283f07e17022c5c0390022ac238020fc92c4607a4101243f07e0040004508a1140ec008860920083f0570d01b83a0740e819c0387417e314648050100184e0001921b82b8680d80840287418e314638050100184e00018e1b02b8680d01d03a02100a1743a40918b04c0280800c270003480d0134320640e82544b89700a020030970001e0320570c01803a0740e80080008c1182300280800c2300008c0c0cd1990df1d639d960071d0020030041702a9890000e40687f29166cc79030d31a6a85970c6408cc00201a1ce39d3cb2463880988adc19c3382685e0bc6d84b85e = true := by decide +kernel
theorem chk_4_18 : checkRange 3 f4 f3 541 261 22 0x4508a00c2003000a58a23064220092268758020002284508a0082000f00a1142284508c11823046049134e8001000114a6c460c643c2280201e092268738020002296588c6b0870450800141244d39e004000452376bcb80461c3138e700100011822044088118230e789c73400800088110220440881142282489a1d00080008809e2184308c14a270528020002193988c6ac8684508a092268670020002283d08610c1485689615a0080008609a2104208c12e25c4b802000210420840a06f84e89613a008000841042084108c38a271c50020002084108210420845049134e20010001042084108229071c4b386004000412bb118d510c08a092269c20020002283f07e0fc1f83f07e00e1f8040060081f83f07e0001c81d07e486d483d2161a622c6982300229c208020fc8fda707a4281f83f0b91022e41d8011561240107e4923243d2120fc1f83f07300e1f87508b1d40ec008ab0920083f24718e1e90803b00a1f87308b1cc0ec008ab0920083f2416901e90607e0fc338458ce076004558490041f83d07a0f41e83d07a00e1e8040060081e83d07a0001981007a5d2d290b17511af5c1180114e1040107a = true := by decide +kernel
theorem chk_4_19 : checkRange 3 f4 f3 541 283 22 0x15fbb67588c0938b97781cc038ea7743a1dc03100a398008081442ac033121a43481880575c004043541442882a0c4144af45e3a845c1cc038ea0020205130719cec84d8042cc2e85d05f1382704e09c13801c4e00800c010490901380003a03c138144500a00822704289c0100100003c0a22784f04513817c4b09612c2584b00712c020030041242404b0000cc0804b0a01401302089607a0144b0010102584c0980983104b0511282504e0981382704b0970082705e0941282502609612c2584b00412c7c44a0920a22484909c1382700309c13811c490921241304b09608e248288901201e4218901202402607908624198ba21be3ac73b9e00e3a004006008238553840001c81d102512e91ca22c08226869a6f72ce491530f5c41244d0ce49ee29c32282981244d38811c2384708e738e68528067144102389211c2384708e11ce20810471242384708e11ce18800471242384508a1142284508a00e220040060082004508a0001800f00a51a231ae226082268698020002284508a11422003080114180052a5118d6912049134e88010001142284500800c0003008a1140144508a114994460bd4442ec2489a1760080008a = true := by decide +kernel
theorem chk_4_20 : checkRange 3 f4 f3 541 305 21 0x3e1818019f90622202f85f0be1903206409d0083205f0b81702e0458b81702d05c080170b56033fa4acfc4a10b85a2325fc2541702e05c07300e2e0750ea1702d85b0b616c0840288e18e31c5280618e0385b0b616c2d85b03900a2387300e16cb65fe3f64a42e05c0b80e601c5c0b81702e01c80516c004040b41560185c0d21a42e05a3f6100c581c80511c2d85b0b616c2d85b3ef01c2d96b8bc7e494039807170004040b41702e05c09b0082e05d0ba17020df70080080001e0551642c8098b24b2fb86324c7120101d0e71ce05c56005158240560531602c03b8ac10e2b0040040000f0298ae15c1ec5605314c298560ac15819c038ac1582b05602100a2b000808150294030ac0f6298520a402e290028a4120290580b009c1dc5202500a290008081482a05404e188290520a41481d4038a41482905202500a29000808148290030a414c2982735314837c7580800c000391937bc0146709a5c898df00bd4782ec5d8bb0ee2a85dab17b4f511d3bf74c3a0740e80fe2a8742d3784f011c3cc21c2e05c0b80fe2a85c2b9192ec11a127172ef03980774c3a8752b718eeb91903100ae10730e6 = true := by decide +kernel
theorem chk_4_21 : checkRange 3 f4 f3 541 326 14 0x3105102f00b0700080811036066054188cde0d0ca19031a0c00782c020030047ec291d60000cc0808b1217fb0a83a807850ede13422046014688010103105380663c3586b0d61ace940202001e2dc6306d00e318630c618c0a4028c6002020620ad00c318680d01a03181e805820004043560082d01000c188168660cc0a83105e0bc17802002000078154600c018a3142d8c518a25c020c51782f05e0061781885e0be17c2f8648cb5e304c640970086585e0ba174020030000c42e85d0051742505d0c21782f46106300e2ec008081762ec5d8bb12a0105d8ba1742e8030b80c42e85f0bc17c2f8378071d4004040de1d63386409b0083ac5d0ba1740105c03a1742e85d0ba1782f05e0bc0ce01c648c9002020658cb5e633a180970086405d29d178319300ba1740101d0e70da01c738e71cc004040dc1b839c670c6136010738ba59a2f20625e1742e05d07300e3a8008081b4c2c6742c136010c70ba5662f20525c1742e8398071d0004040d81d03387409b0083a05d2751790212d0ba1741a4038ce002020660ce19c3384d80419c2e8600be3322f002c08128ba8610c21842f45e8bd12a0105e8bd = true := by decide +kernel
theorem chk_4_22 : checkRange 3 f4 f3 541 340 15 0x1a4348030b80e434963c29190a28758b91d61bc038ea1d63a07583300a398008081bc2ac030eb1a4340680c61a03480202201e2dc7386d00e39c738e71ce0a4028e60020206e0ab00c39c682cf857061430d21703489b8b986c1cc038ea77a3a21903700a398008081b42ac0332c1a4ad613c16508348690e81723a0398071d03a0740e805e01473001010360558061d0349388c98249a8670b919c1a4038ce1d43a86726d18f0413403b00a338730e619c9de0ac0e4cc3385c8ce0d201c670ce19c3381d80519c004040cc156018670d21a4339efc2c00c2e03311a190320640c81d62e47583300a398758ce1d6320630c618c319d080404003c5b8e7052014730e719c39c6332f840328640c683c01e0e00800c0105b0a475c0003302001c3106b35c63c08c02b941a231c688d11a2344688c4188310620c418801c6200800c0105a0a41440003302001808c028d1002021ae0d5198150620c4188310620061682883300c05a01610001010d68720cc0a8310620c400c2d03300c06601464001010320700cc0a8310620040400a4028c6002020630dc198150620c41680301b80583c004043581b43302a0c4 = true := by decide +kernel
theorem chk_4_23 : checkRange 3 f4 f3 541 355 129 0x1a45a96cbfc7ecf34b319430622c4599277c5c18d1602dcb6cb63182d0c58af18260c6316918a5a0570c42bc2b46195c1583005e4bf2b22f8ac0bd2ae2d4948ab1604005492bbfb1722e45c8b98703a8750ea80e2e45d3f01742e85d1525a82e45c8d21a44f89e3fb1722e49d1386b30bc9b13626c4d0991282604b89612a192324648c91925087414219c4708e075230460890bc22c5083f90e21c3f88f0fc2343e88a0bc1783f0881402784e89c0562684c87c1301f04b89612a2243d07d13e1724d8771262483b0911202e8458770fe1d83d8750ea00c2e0370ea586324642c21d62e47586f00e3ac752af193091540e81723a0398071d03a8750e81cc398730e600c2d87306c01ca8c63c2053c0b402ba21cc3987300616c1b0072c118e3214c03300a3ac7329718e3194b0e60080a0148051ce399648c783ca50730b601c0dc02b9e1ccaac63c1c5243987302f00a3a0730d21a4348690d01a401c6900800c0105c0a61a4000390221a43586b0d61ac34c5c8d30e601c698d31a634c118051a2004040d314e018698d21a4348690d200c2e0690721a4a9e11c1a51c4945cc330e601c753b91d10d0168051cc004040de156019990d2 = true := by decide +kernel
theorem chk_4_24 : checkRange 3 f4 f3 541 484 222 0x604ccdd18c760031d7f0c75f0bf18fafa6babd9ca88d11a2357732f11abb19b88d74a22da988b5c8efde608b11622c45ae266222d6e31066822c45b0e660b598abf578affde4c017cf00c2b33967eab07433b78efa5f1be56c2da5b7a68642d95333296e6e65e5bdd7db011bec020acd0da2a54800e05ff3f47a2e35f5b8f7a6fb1b1bea6fefa1f334b47cd35a8bd909cf91f123c756f71ec36b7a4f41e5238790e0de33c446c22c45aca6eab11bca9a6ee9c9afa646f6989d52726e2e459ea2c5ee8a991b986cee41c738c704e01bf37c682889bd2206f0879bb21c6e8220440881102204408844cbed12305440c250f2ff438c3444088434c9db921a6e0db9b636a6d0d99b23626c0869af0886a0d310b2e9694d11a134067ccf19d33840ca097ea044f4c05012786549d99427264c9b99126c6409418a2ca618b11842a46087f150300534bf8fd2905f8a317d2885ec909741e83e4790f81e23bc770ec0bd090120e10480906c8f41e23b86311c98a4aaf05fc8b9172620ce22f30c6691a984330ea4cb3b1324e9cc2190766639de97e4ba2244497c4765e954976816225eac252e8348670ce7863205e8bd190320b917717af6c640b9 = true := by decide +kernel
theorem chk_4_25 : checkRange 3 f4 f3 541 706 177 0x1d43ae170b81702e1fc3f61d62e05c0b8170291ed0a57acf39e63ce784f021c0ce768f7c5e3b47c2e71d039e734e61cc08a114229b908c6e0db9b53686ccd91b136017a320633586e4d59b836e6d8da9b43666c8d89b03566bc221a707e6941f83a07465103d93357644e4d90411638ca992b28828c9846b2272ec80630ba1742f18b3f2618d658532d870e7d840c960cc4189b0e70a224448e81d03a18235b = true := by decide +kernel

theorem level_4 : ∀ i < 883, (∀ x ∈ decodeSet (f4 i), x < 81) ∧ ¬ Coverable 4 (decodeSet (f4 i)) := by
  have hlt : ∀ j < 541, ∀ x ∈ decodeSet (f3 j), x < 81 := fun j hj => (level_3 j hj).1
  have hno : ∀ j < 541, ¬ Coverable 3 (decodeSet (f3 j)) := fun j hj => (level_3 j hj).2
  intro i hi
  by_cases h0_13 : i < 148
  · by_cases h0_6 : i < 35
    · by_cases h0_3 : i < 19
      · by_cases h0_1 : i < 6
        · exact checkRange_sound 3 f4 f3 541 hlt hno 0 6 _ chk_4_0 i (by omega) (by omega)
        · by_cases h1_2 : i < 14
          · exact checkRange_sound 3 f4 f3 541 hlt hno 6 8 _ chk_4_1 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 14 5 _ chk_4_2 i (by omega) (by omega)
      · by_cases h3_4 : i < 24
        · exact checkRange_sound 3 f4 f3 541 hlt hno 19 5 _ chk_4_3 i (by omega) (by omega)
        · by_cases h4_5 : i < 30
          · exact checkRange_sound 3 f4 f3 541 hlt hno 24 6 _ chk_4_4 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 30 5 _ chk_4_5 i (by omega) (by omega)
    · by_cases h6_9 : i < 80
      · by_cases h6_7 : i < 44
        · exact checkRange_sound 3 f4 f3 541 hlt hno 35 9 _ chk_4_6 i (by omega) (by omega)
        · by_cases h7_8 : i < 56
          · exact checkRange_sound 3 f4 f3 541 hlt hno 44 12 _ chk_4_7 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 56 24 _ chk_4_8 i (by omega) (by omega)
      · by_cases h9_11 : i < 114
        · by_cases h9_10 : i < 98
          · exact checkRange_sound 3 f4 f3 541 hlt hno 80 18 _ chk_4_9 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 98 16 _ chk_4_10 i (by omega) (by omega)
        · by_cases h11_12 : i < 132
          · exact checkRange_sound 3 f4 f3 541 hlt hno 114 18 _ chk_4_11 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 132 16 _ chk_4_12 i (by omega) (by omega)
  · by_cases h13_19 : i < 283
    · by_cases h13_16 : i < 219
      · by_cases h13_14 : i < 173
        · exact checkRange_sound 3 f4 f3 541 hlt hno 148 25 _ chk_4_13 i (by omega) (by omega)
        · by_cases h14_15 : i < 200
          · exact checkRange_sound 3 f4 f3 541 hlt hno 173 27 _ chk_4_14 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 200 19 _ chk_4_15 i (by omega) (by omega)
      · by_cases h16_17 : i < 243
        · exact checkRange_sound 3 f4 f3 541 hlt hno 219 24 _ chk_4_16 i (by omega) (by omega)
        · by_cases h17_18 : i < 261
          · exact checkRange_sound 3 f4 f3 541 hlt hno 243 18 _ chk_4_17 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 261 22 _ chk_4_18 i (by omega) (by omega)
    · by_cases h19_22 : i < 340
      · by_cases h19_20 : i < 305
        · exact checkRange_sound 3 f4 f3 541 hlt hno 283 22 _ chk_4_19 i (by omega) (by omega)
        · by_cases h20_21 : i < 326
          · exact checkRange_sound 3 f4 f3 541 hlt hno 305 21 _ chk_4_20 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 326 14 _ chk_4_21 i (by omega) (by omega)
      · by_cases h22_24 : i < 484
        · by_cases h22_23 : i < 355
          · exact checkRange_sound 3 f4 f3 541 hlt hno 340 15 _ chk_4_22 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 355 129 _ chk_4_23 i (by omega) (by omega)
        · by_cases h24_25 : i < 706
          · exact checkRange_sound 3 f4 f3 541 hlt hno 484 222 _ chk_4_24 i (by omega) (by omega)
          · exact checkRange_sound 3 f4 f3 541 hlt hno 706 177 _ chk_4_25 i (by omega) (by omega)

theorem chk_5_0 : checkRange 4 f5 f4 883 0 7 0x441682c0201e4008893f203c0090120a094009030007e0001042040908000e1100003c02e0000000000000000000000000000000000001ec012194f4004011fd40e0e40108d4ec88d3a0c30720040110921a1140110b3ca9690fa5804211400802406928f70be1702d04205a05a000000000000002780243613c008023fe13c208020640c81903201e0c80080222213c268020640c018030060094180010040c01802401c038070240b00b8000000000000000000000000000000000000000900090e8480020090084808600847a7044e1206b8430020088984808c0088b9e74ac884241f108c004012054900805e0201640802b02c000174439ca16e3045d802340008c51880286180917e0045f000000000538a614a004520a30122884e09a0021f83e80a0f813c208010760200040087d0045e0bb0010045d0b9016004244b816e2d83640b0010044548d818004464b21622c0578ae018002008aa15226c2704d098100140080000000141383503a08c0383705612c0480d01606c1d82907e07c1e84a07c0f01d0360680a8140260440780e01a0180280400600800400002 = true := by decide +kernel
theorem chk_5_1 : checkRange 4 f5 f4 883 7 6 0x8010020046f0a251784f6c00941284d09a1d03a0740e813c3a0620c41a0078410d40040105809c138190320600c00000009c1382484e09c1382504e07c0d02702209c03027004674ce19b048668cc99804608ccb94eb2c65412194322608b70330430c800401056008010020040080100200400801002004009a953da6e4dc9512a000000ab956049554aa1530445400e01a25e0407600607a0081702d0560a0c800231e008c7027b1a0020080231862c1a8020320640c8023144d4c498804f61c03c2086a002008022da0c00c02f02e0017590d0320640c0180000008e11a2324608b91402a4480a013216048748070780b0c09802fe398bf17d2f80300617b1c45e8bc8e12f05dcbb16c05402c148008020a00128017c2d45a8ad15a000000d91ac0926a8d41a6028648090342cc0889800c0ec0100c8470880503aa6750e0942684d4ba13d328935228a427a695aa03c0780f082104208410821040080100200801002004008012803c41a01982409805c210380241ad1fa830420940a84509a1340784108200400802004008011dd09e77c268023d2ae51284f48aaec1284d0020093e08a0c40c407040 = true := by decide +kernel
theorem chk_5_2 : checkRange 4 f5 f4 883 13 7 0x86108080403be0660c8193bc774ee00780106647c4912305c0b8172da12c13c4a0410040181800011009012357758ea8e4018030ea0e03a6748e88df1bc740e78708ed1ca0580b01602c0580b0010020040100200400801002738e696c0821000180a0060f81243d076642a251784f7200941284d09a2554cb8e46a13dc6386700de8078410fc0040107809c138390700cc151758300600c02f0310bc0b81702c000160eaa0c410091860410d4004010040661303406001e03c0780f01e03c0000001e03c0780f01e03c0780f01e03c0780f01e0380780f0dc1b0320526eedc1b22936c4010340566140103400f08217b4fa790640c818030000001692d056ab39662ca098ae8202824c4090ef00e0fc1a8023036e8db0d4b6a6b4d600a8156ac605aa35235ad41933085c01c80986e0020082e4f72ee68cbb98f2ee000001bb386124db9cd37a064cb817068704111990181f002004008010020040080100200400801002004676dc9b42a96cc0841084508ad3945b4c694ab5a432460cb78380390d80040105a0921242484909212400000092124248490921242384907c0d02482209203024804 = true := by decide +kernel
theorem chk_5_3 : checkRange 4 f5 f4 883 20 6 0x1cc580b01580600c0a81502a0530a614c298530a61442885101602c0580b01602c0040080100400801002004008040980102784d00a0280500a014028050080100280500a0140020500a01000c0500a01402800809014000050050731602b8560181542a0530a4144058500010040304f00a1300227f1864173ba5e1860200421a4328604c80098685c0416c19e3386680c0020245a0000f80102404708c104c5412bbd42efc80780f01e0040080100cf18123b600cde8440330660197bc068085040a8157f459dfc3a57d8fa8d3be87cc294558a702604c0981302604c0080100200801002004008013c4768b80480860320180300600c0180300600c0180300600c0180332f8050001084508afd92fbf47a2f91f12a77c0f78648cf1960e41c8390720e41c8010020040100200400801002784ec96f08e10811c0334f7b0f58fb84608cf50243d27a0f3915848798f286f8eb1c610c2184308610c218010020040100200400801002780ec16e08c0400180300600c0180300600c0180300600c01822006 = true := by decide +kernel
theorem chk_5_4 : checkRange 4 f5 f4 883 26 5 0x388d41a4340230ce198328640c608631000802018308050b20100200400801002004008010020040080118dd2da0bb978f52d82c0595aab45663b40052dd62058b7152048544118010384d8000840081802f85e09c01c0300700c01c038070010040300700e01c0300700e01c0300700e01c0380700e01c038070010040300700e01c038070004860c504a0d0600c01682e3a4748e90250020c4e902e0b08e827a3009a00814032000410070ba1700804d00e01c0380700e01c0380700101c0380700e01c0380700e01c0380700e0040280700001c09012024048090120240480901202404800412024048090120240480900101e0480001200e16c2d05909801c90c18a093d00c01802d05d54aa854e04a004189d405cb68f604f3d41340101a0640008000e0e62c0570ae15c2b0560180302a8550aa1542a855008130020510161400040109c019408c5049324568ad0100204c09813026000498130020010da1ae354060010122d40007e00c = true := by decide +kernel
theorem chk_5_5 : checkRange 4 f5 f4 883 31 5 0x202a8f61e43b80a8ec1d0390700a302637000802018360050b695e58d05c5f96258c0881189f22e5c93d00258e308115c067cda9b902a0080b9a5000450040080100200400801002004008010020040080ce3d07802108a3a8730e21bc31c1c8da002008060d60142d319a5741682f1da5705a0b6bd578aec08400a574160b56f2a5562acc228020749c800112010020040080100380700e01c0380700e01c0380700e01c0040100c01c02807243062825068300600b4171dc3b8770128010627501706859013d6104d0040e819000220020388d41a4120690d01a0118230ce19c3386704819c0205900818c10c620010042f00600c0180300600c0180300600c018030066354b2125502544a80b0161d83b0760ec0013b076016004560121550460040e137000218030388d41a834023046198120660ca194328240ca194318630c608610c2184308610c008010020080100200400801008164020610200140280500a0140280500a0140280500a014110220440881102202c058110220440880042204405801822044088110010380880002200a = true := by decide +kernel
theorem chk_5_6 : checkRange 4 f5 f4 883 36 5 0x180300600c0180300600c0180100600c01819c7a0f01e03c01082108a114750ea1d43a8750ea0102d0040c70723680080217c124248490921242482d05a124248490420042484905a010248490921140103e0920002480c0180300600c01c0380700e01c0380700e01c0380700e01c0380700801c0200700e01c0040100e09c0c42484e0600c01682e09c138270250020c42702e0081382704e09a0081f032000138060d81ac3084f00e01c0380700e01c038070010020040500801c0380500801c0cc188330660c01802d05c0cc1983304a0041883305c0cc198330660cc010330640001980e0141547b0f61dc0540a8e81d03a0720e41c8390720e414628c5181302604c098130260040080100400801002004008040b60103605d0190320640c819032044088190320640c801032064088060320640c81500405c0c8000320280500a0140280500a0140280500a014028050671e83d01084508a398730e61c4388710e21c4388638c718e0e41c8390720e41c80100200401002004008010020102d0040d617011c2384708e11c2382d05a11c238470420042384705a0182384708e1140103c08e0002380a = true := by decide +kernel
theorem chk_5_7 : checkRange 4 f5 f4 883 41 7 0x760ea19c2a80600e0180380700e01c0380700e01c039218314128341803005a0b8f01e03c0094008313a80b83a2c509eb44268020800c80012401c3a0730cc150039218314128341803005a0bac7217b18094008313a80b97226109e98c268020800c80012201c390710ca14c0380700e01c0380700a01c0280700e01c03807243062825068300600b417588453618128010627501709257e13d6584d00410019000240038700de1902900700e01c0380700e01c03807243062825068300600b41758247360012801062750172e258e13d6984d0041001900023c038518c718c2880700e01c0380700e01c0380700e0000380700e01c0380700e01c0040100c01c0280400e01e03c0780f01e03c0780f01e03c0780f00203c0780f01e0240680f0160080780f00003c070dc1b43105000e01c0380700e0180200700e0180200700e01c90c18a0941a0c01802d05c778ef1de04a004189d405c1a96184f59c134010400640008e00e0181547b0f21e43c8770ee02a054760ec1d83b0760ec0102d8040a3026370008021812b4af84932e63caf811022664cc99927a004af999022010ce9af36e054010173460008d00c = true := by decide +kernel
theorem chk_5_8 : checkRange 4 f5 f4 883 48 6 0x11a0924307e0612504982792604a0942684d12a4909212409e4908810022003c2091c0020088200c09c1382704e04a0041884e05c1388c1162143e8308252444889100f01e03c00801002130880242001308810201c0cc19833066094008310660b8199142244207c0612504981284d2484889011e01e1048e0010041381984c200021bd1ed47691c12801062854171101ec3d06a0b001c0380700e01c0380700e01c0080500e01c0380700e01c0380700e01c038070020140380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0000700e01c0380700e01c0380700e01c0391f8313f67ec1803005a0b8f182747e094008313a80b97428106aa0c268020800c80012801c3c8780d215c0380700e01c0380700e01c0380700e01c0380700e4860c504a0d0600c01682eb2c8bec90250020c4ea02e5ccb0427acd09a00820032000498070ee0423405600e01c0380700e01c0380700e01c0000700e01c0380700e01c038008020180380700e01c0941282104a0941282104a0941282504a0041282504a0941282304a0940102504a0001280e = true := by decide +kernel
theorem chk_5_9 : checkRange 4 f5 f4 883 54 5 0x6b31722c1cc8ac508a1018030500a0140280500a001c0382007781627c00401136a08680b516a2cc598b30e9002598d91a62cc040080100086c0d71ac02c0080a15a000520110220de740e70212840540c0180303740b016002004010020040089e13c2780600113a2744e89d13a2744e80c0010040704001c2702680901202404809012024048008120240480901002004009012024048090020240480001203c049adc5a8a914a280242840600c140280090a01402803bc0b13e27c4f80080100400811022044088110222784e8101380242027e17e9d05f9fdcc29803a40097e84b0a616810020041761843046000b00202856000144038070379d039c084e30150300600c0dd02c058008010040080100289c6622601800512a2444632d1122119403000401440734bb09a0980240680912c2544387f04d2401041e8410821042691c0041309304d2484808f0462401009304d2401040104c8301020b0320640c8190320830509304123904a0804181c0c0180300600c0269200000909304d2484808f0182400389306120c039be1e304e8fc128010627ec17128 = true := by decide +kernel
theorem chk_5_10 : checkRange 4 f5 f4 883 59 3 0x6a72aa541c8030062501c093cfae4c1be37925a4a0e11da3940b01602c0580b01600200400802004008010020040981305029c4d80a0140280500a014028004010140280500a0140280500a0140280500a0140280500a0140280040101400c0500a014020000150140de740e702138c0540c0180303740b0160020040100200400a451989080600147e8f91d8cb4708dc6500c00100409813050298270090120240480901202400401012024048090120240480901202404809012024048090120240040101202404809012020000140126db29a524a20300611649c9346fd1549292123a460f302c05800802004538a714e0280500a014028052444869052000a47a8f11d23946c8d51a23314e028530a614c298050090120240480901202404809012294141cc8349f40d27a4f29e0004010349d93a8bd0349cd390bd03480f35a6a4d29a13387b8162f4004010347344b4ab15002000013026 = true := by decide +kernel
theorem chk_5_11 : checkRange 4 f5 f4 883 62 4 0x240480901202404809012024048090120240480901202404809012024048090120020040080200400801002004048090120240480a0140280500a0140280500a01402805000801004008010020280500a0140040500a0140280500a0140280040101400c0500a00a07804809012024048090120240480901202404800802024048090120de740cd0213340540c0180303740b01600200401002004008cf1983340600152233d480cb51e3346500c001005419ce2ee30c0201d012301470c0180030060c2182300fb4c21be305468c00e11da3940b01602c0580b016002004008020040080100200541a202ee2fc0700a0140280500a0140280500a0140280500a0140280500a014028050008010040080a0140280500a0140280500a0140240181b0146eb45a8a1cca2544287018031014e250ca1470a84506880e707b8162f4004010263514c8d41a8030060249aa350698249a634c698d30f302c05800802004124d01a00280500a014028050d91ac3506980a192324648c9192324648c9192028628c518a3140500901202404809012024048090122f80101a034 = true := by decide +kernel
theorem chk_5_12 : checkRange 4 f5 f4 883 66 4 0x2c0580b01602c0580b0100200400001602c0580b01602c0580b0010040580b01202c0580e88703a0080a1940046480a1940040500917a004050ca0122a0000000003284f89d0203284c8011300284c8010141401485d95c03e0580b01602c058010020040580a0120240480b01602c0080a01202c05801016024058010120000000001602c0580b01602c0580b01603001c0c0020280600101802806001014024060010140300480c0000000000c0180300600c0180040600a0180040500c0180160601e8160280500a0140280500a0140280500a0140280500a0140280180a014028004010143594d0d61ac030060d81ae358698d31a634c698d30e11da3940b01602c0580b01600200400802004008010020040d01a004340088250140240480901202404809012024048090120240480901202404809012024004010120de740d50213540540c0180303740b01600200401002004008da19835406001192324648c91923246480c0010040d01a0043140301f012 = true := by decide +kernel
theorem chk_5_13 : checkRange 4 f5 f4 883 70 5 0x1c0c0180300600c0180300500a0180300600c0180300600c018030008090000300141a8353780080100234c05009012024608e11bc004050094d0384008b301230400809000000000de140154298521bc38408cb604b03005984bb5a980080a5260046480a5220040500917a0040525b0122a0000000008fc4f89d0208950e0011300290d0010141401485b9640360580b01602c0580b01602c058010140240580b0160000580b01664ef16a50020286e001192028678010140245e801014968048a80000000023e13e274082241b80044c00a19e004050500520125881d81602c0580b01602c0580b0020040580b01602c0580b01202c0580b0000000580b01602c0580b01602c0580b016002058080160ba09c1380202949001192029480010140245e801014964048a80000000023b13e274082234360044c00a432004050500521825801481602c0580b01602c0580b0160280500b01602c0580b01602c0580b0160040480001600a0d41a80202865801192028658010140245e80101432c048a8000000000cb13e274080cb1b60044c00a19c0040505005201a5781f816 = true := by decide +kernel
theorem chk_5_14 : checkRange 4 f5 f4 883 75 4 0x467201182538d4f0119c838d4d801002028050119c8025440119c838d2e800000284090119c8158be84382102c650ae1326125c0b81709c537a6d010020040004a081902a040a8750060e20010046c0c80123085d00e81d10e0740e9c83914e8d61a8028050c050e391288a1142390be0e51c6004048000ac00a5b0b616c38068a6c010020040001c03806f0dd0a8380060e10010046b8c70123045c8118230300600c0180300600c018030060010020280500c0180240600c018030060000000300600c0180300600381802c0600c01864f532a51c4004008011a6028048090123087127000202804a6b1c40045980918400404800000001260a00aa14c291d11c403a5c01b81800e0600c0180300600c0020040600c0180300600c0120300600c0000000600c0180300600c0180300600c018002060080180ba09c139be004008011a60280480901237d428df00202804a694c8004598094c2004048000000006f8a00aa14c290df2f23945b815818 = true := by decide +kernel
theorem chk_5_15 : checkRange 4 f5 f4 883 79 5 0x680d0170340680781a02e0680d01a03404836a4150a084fa81508a118230db08610c0080100400801002af6122bf8460056aad45a6091692d11f308c0040159a760c10f20b20700689e8213b44c9868320640caaf033ab80b81702e0007489112023c039d704d3c00040104e062100eb1d404a094cc8493b04c1a0a8945e13eca02504a134268953c0780f004f3c0758eb1dc01e104ef0010047482704e76a0d6a41cea880d6a00020054d299035a6073a97012a380d68c0000012aa530358c873a310b07580d5bf1d0002630080fe0306f80b01602c0580b01837c0080a52c0314a8df5280306f8095140306f80b0020293e0094f42dc058b716e2dc05a6e4ca02d31a6222d02d2f8b00182c0580b001837c0022c43e0310f0df43a0306f8572fe0ba5e01382778b532a5546a854f8d61a8028050c05169512922e45a754c00139ce004048000b00306f00b01602c0580b01836c0080a196030658cb196030120091cc0306f00b002028658094f22d8058b616c090058cb1cc02c6d8cb04802c658af0182bc578af018378000e61cc030708de1ba0306f0571cc00a5d81a835 = true := by decide +kernel
theorem chk_5_16 : checkRange 4 f5 f4 883 84 5 0x700e01c0380901202404809012024048090120240480901202401e090120240480040080200408811022044088110240480801201e0489ac1983206425d1ba5c01e0041991f24248c1702e05c1894d04f53010401036060000ff01c0380700e01c03803c0e01c0380700e01c03808010020040080100200400801002004008010020040080100200400040080200408010020040080100200400801001e0419f53be854eefdd16e541ce0053bc2384f0ac1602c058c114604851410c010364a0000fe01c3967b81013604808812022048090120010040881202404808812024048088120240480901202401e090120010040881202404809012000bb00cc1903242c8590b00f0020cc8f9212460b81702e0b08d827a34082008150300007e0121653cc7909a05f04a0940780100354ce9d5704a0040d59e01ced80d3802000c41881a0340680d01a0340480900e03405c0d01a0ca8f53f8210420542284508a3141c8390020040100200400ab59d9ade114015abb656c150daeb5808422801005671d93063cc2d02101a = true := by decide +kernel
theorem chk_5_17 : checkRange 4 f5 f4 883 89 4 0x15d3e00809c02404809007801002090120240480040f01c01c0900f01c0480c4188310620c41883101e004188310620c41702e05c0c4188310620c4010310600001882403c0780f01e03c0780901201c0780b81e03c1951ea7f0420840a84508a1146283907200400802004008011db3b276c228023e47c8f91f23e47c8108450020080e0840387c05c04208410821042084108210010841082104205a0b41681a084108210390040f0210000840780f01e02e0780f00f03c05c0f01e03c078090200400801002002a080100200400801000100200801002004080100200400081002004008010020040080008020380800e0200400e01c0380700e01c0380700041c0380700e01602c0580681c0380700e0010380700001c01e0380700e01c0380700e01c01c0700e01c038ccedf5b8b6d6d010821048114e49f60487d8fb1f61a20e4fa1f43e80040080200408811022044088111db3e4080f801e1099b538e7f4e2f5703e5619a00538c1d83f0841682d05ac1946a9e5380e4010364a40010001c = true := by decide +kernel
theorem chk_5_18 : checkRange 4 f5 f4 883 93 6 0x1c73e80809f0240480901202404008010020044090078240499c41983206498918a6201e0041991f24248c1702e05c1a94a84f5a01040104c060001070240440881002003c0881102201801011022044cc6e05bc5536e81082108a114fb1f63ec7d8fb1f6038070420d10727d0008023dc1242484909212424849092004248490921241682d05a010248490920e40104709200024822044088100220480901202404809012024048090120240480901201c038090078240480040102409c0cc1903209c1382700f0020cc2704e09c0b81702e0081382704e08200825030000138111953e40809d0240480900781304807810012048038100240499bc19832064f6d12e5a01e0041991f24248c1702e05c7a14784f57a1040104c06000106024040080100200480901202404803c12024048090120240499cc19832064fc516e5801e0041991f24248c1602c058c294b84856c10401044060001040200400801002004008010020040080100200400801001c03808010020040004010200440881102204403c11022044088110220459ed3aa6e4dc97916a5e1ce0052f2ae54c9781602c0580114f84855810c010444a800103020 = true := by decide +kernel
theorem chk_5_19 : checkRange 4 f5 f4 883 99 5 0x5cc24a06290c5d0922f09f7401282509a1344aa1042084027a103fc7f84400f082838008023f00882704e09c138078010661381704e2aa811011460be0941280f002004ea9d33aa094008403fc038440403fc408120310620c41880f0020c41882e0625d5001fc288c65095ce59b7301282509a135082104208410821001e1050720e41c004008020041382484e09c138271d541882018840110071c009746e9ac078010664bc171fe286084101420480901202404809012024048090000240480901200e048090120010040881201e0380901282504a0941282504a03c0082504a0941282504a0941281d0460940f80204a09400025048724fb0202800880e02203809012024048090120240499d4198320642551aa6401e0041991f24248c1702e05c1d14c84f5ac1040104c06000108024 = true := by decide +kernel
theorem chk_5_20 : checkRange 4 f5 f4 883 104 2 0x981302604c8bb1522e04a13426a2c4608b8dfa284508a11422801e10420801004008198330660641502a0540a8152383c28b91402a44889112224448891122240660a8188310620c4150280500a0140280500a0140280508682c288068a201a62b09ea200080206884d09a130680c819032064999332664cc13d3300f082998008020682289483047c0b80002604c0981302604c03c1302604c0981302604cda705608b7a1182322cc05800dfa2abf17dafa5f21e210c21801004009112224440641502a0540a815585b23666c582abdd7b2f45e6bc177aee5da4440a90f21e43c878150280500a0140280500a0140280508602b397069a981a62d091a400080206974eeaa7e069a2b4427e06900f31660c621232f0f50869f800802068ec095a4c4780b000026 = true := by decide +kernel
theorem chk_5_21 : checkRange 4 f5 f4 883 106 3 0x1402802e0a01400f05005c140280500a00906d482a14109f502a114230461b610c21801002008010020055e42457d08c00ad8df0bd4122f25e23e61180080204c0982b21e1780e01c0380700e01c0380020081c0380700e01c0380700e01c0380700e01c0380700e01c0380020081c01a0700e01c02c0000a0bca1c4305298e82599b8931100f0020cc19833ab3586b2d5b0660c4188310620c43c38509dac8275d709fa800080209d70ee2a7909c0c819032064efd35678bb213f3b00f0829e40080209ced8838304840b80021a04c0981302604c0981302601c0981302604ccdf1662804211422a2c4588b0dfa2a4548a91522a1a60e41c8010040091322644c0641502a0540a815571ae75d51502ac3d8730d618c258411622a44c0a910220440880150280500a0140280500a0140280508702d38b069ab81a60bd39a680080206971ee4a84069a3b46284068f6735668c1f99b320d5072a1000802068ec887a4e4800b400026 = true := by decide +kernel
theorem chk_5_22 : checkRange 4 f5 f4 883 109 3 0xd2f0760c3ee11823606091811f1dfe456122fe5fa1be3ac7184308610c218430860040080100400801002004008130260ac8881002a0540641502a01e0a80c82a0540a81501408811022044088110220010041102204408811022044088110220440881102204408810c2200100411003044088110160000545851021e29817c1282501e00400d513a7554128010508680721a0501e0820310620c4188310620c4008020620c4188310620c4188310620c4188310620c41880f0620c4008020620c4188300620b8000310500a0140280500980901201c0a00b8280501951ea7f0420840a84508a1146283907200400802004008015693b35b422802b4f882f5aa1c2d85010845002008130260b48805f04207c1081f0420841080080207c1082104207c1082104207c10821042084108210420721080080207c068210420840b400028 = true := by decide +kernel
theorem chk_5_23 : checkRange 4 f5 f4 883 112 4 0x189494920a90300600c0180250600c0000000000c01200e01c038180300600c81903206403c190000480c8000320480c80002401c0c8190303a29011e1506bf94b2802509a13726263c954e7246465979132100f082104008020040cc1983303211c2604c098132c09e1b2761c2624448891122244488911220330980c4188310620c420040080100200400801001983c484179c9a82d54a09ffe98d2c03c20a8204c7889483047c5bd1322229cc4412bbb42f8980780f01e004008010548681221a0541e0fc0330660cc198330660cc008020660cc198330660c8190320640cc198330660cc1980f0660cc008020660cc198300660b8000330540a81502a0500980a0140140a80c82a054caf1862e04211422a2c4588b11522a4548a91522a19233c658390720e41c8390720040080100400801002004008130260b4898f704708e11c2384708e11c0080208e11c2384708e11c2384708e11c2384708e11c2384707211c0080208e0182384708e0b40002a = true := by decide +kernel
theorem chk_5_24 : checkRange 4 f5 f4 883 116 6 0x1c1092978b33475128bc27e5c04a0942684d12a9913223509e9912e25c4c003c20a620020090b04e09c0c0180300600c018030060008180300600c018000048038181874b4958b1387076f1f5d00907600012246000748121ec0000900705e2220c0180300600c0180300600c0180300600c018030048090180300600c001030000038c5a580905782783f09e13c0683f0000902780009e090278000480382784f06063c24a542b40c0180300600c0128250600c0180300600c0180300600c01800f0600c0008020601382084e09c03c208000441380004e0441380002201801027030322949281580600c018030060094128300600c0180300600c01800f0600c018030002004010020600c0180300600c0180300600c0180305341044ba9a01e1040001c3ac000e901c3ac0000e00e0bc4bc1818d49c930ab0300600c0128300600c0180300600c0180300600c007830060004010020600c0180190600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c0180300600c018030060e2420bc9d5803c208000488f8000260487880002401c17894830 = true := by decide +kernel
theorem chk_5_25 : checkRange 4 f5 f4 883 122 5 0x78f67f5d6b8d6dad02704e0981314c2884688b812024128c790da780041000000e2fa9e82417606413c180300600c01803209e0001204f06413c2784f06413c0704f09e13c190320640c8190320640c819032004008190320640c8190320640c819032000000120240640c8070320640c8190320600c8bfa764e05c1c3837b3fae80e8374d40000000042c0900700e01c259351ff0640c8190320640c8190320640c8190320640c8190240480c8190320640081900001c6853a0482d813c2584f09e08c2584f0000000004f0480380700e09e13c278323461253716a0640c819032064094128320640c8190320640c8190320640c8078320640040103209c1342704e04a13427000000000270220180300604e008138191a54e49b0b40320640c8128320640c81903201e0c8190010040c819032064b20269ed59009426a6000000000216048020040084c01a10a832 = true := by decide +kernel
theorem chk_5_26 : checkRange 4 f5 f4 883 127 3 0xd01a0340680d01a034068030020340680d19cec7c12aa76802104211422bd7517b2b06aadd91aface3c21aa0e542001004098248490920842284509212424849092124248490921241c839002008010490921240c84708e11c238470921242484908e1242484909212424849092124238490921242484707c0f81f03e07c0f81f03e07c0f0248040680d01a034068a214422f09ea201282509a1344aa8650c8d427a864f87884500f082a080080204c1382704e04a1342684909c1382704909c1382704e01e10420801004008198330660642384a0941282504e09c1382704a09c1382704e09c1382704e066128188310620c41883e07c0f81f03e07c0f81f033078138020346e7b1b14848d896fee084608d0054eec2c5e123606bcb34f007a8434fc004010260680d01a03406803c1a0340680d01a034068aa34eaa855011823049554aa0de84954ca99532a61e210c2180100400824a754ea06422044088110222ae558aa153044540a81502a0540a81502a04ea1112ca594b2964220380700e01c0380700e01c0380709ec02034 = true := by decide +kernel
theorem chk_5_27 : checkRange 4 f5 f4 883 130 4 0x4ba9a5348dc2784f4d6a481b27c038188e2a9c5146003aa87c9eb377182504a13426ad656eb596b2d15ac03c20ad059cb40008010040082704909c1382704e3c2af55b0310802514c03606c0d81b03606c0500a00a06c0641b03653998d4e02108a11546a5f538f3d46dff53da054e0c919e32c1c8390720e41c8390020040080200400801002005aface3244e20702384708e11c238210421142281908e11c2384708e11c1c84708e11c008010040080c84708e11c2384708e11c220470780181b28acd6a28fb84608ca302428a7caa3115848d0ea286f8eb1c610c2184308610c218010020040100200400801002d79669912770380d81b01906c0d8078360320d81b03606c0502204408811022025088110220190881102204408811021844088110008010040080c84408811022044088110220440700181b1cf5089f8bd36fda6ff549ece068a00131e2068a000784147cb334aacc04a13426ab54c6b31652b5594b29652ca01e10420801004008198330660642384c098130262d23c2b316504c574ae95d2ba574ae95d2ba066130188310620c41884008010020040080100200330789e435282 = true := by decide +kernel
theorem chk_5_28 : checkRange 4 f5 f4 883 134 4 0x1c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e00080100200801002004008010380340e01c01e0780f00b83c07803c1e0170780f01e03c024110220440421100a8440881102204308600400802004008010440881102200208811022044088110220440020081b00606c110050380700e01c0380700e01c0380700e01c0380020081c0380700681d03a02e0e81d00f07405c1d03a0740e80906d482a14109f502a114230461b610c2180100200801002004a90242a208c00ad9aa4c4212320aa23e611800802d78f019125b0100e027a9809ea614a29209ea614a2920040081b036090a282027c09ea614a2920000000e01c09e6000706212ea5820a8e060758c2a8d51861031a7d526a4d4981d03a0dc1b981516a654ca9953203c20a9552aa54008010040082704909c1382704e3aea3d4b8310802594d097534a694c2985241382703606ca613e23445c0700e0940c48dd4a002080000071b153c120c100506a13c2784f04608c2584b09e13c2784f09e13c0683f09e13c278010020080104e0921382704e09c13c278480621002784f = true := by decide +kernel
theorem chk_5_29 : checkRange 4 f5 f4 883 138 4 0x7c0f81c03807c0d0090120180100b83e07c108210420841081082108410821042084108210420740681d04207210800802050124248490420840a84508a1142483907200400802004008010490921242280209212424849092124108450020081a0340081240603e0780f01c0380780f0090120140f00b83c07810821042042108210420841082104208410821042084108210390720e41c83907200400801004008010020040081d01a0741080f04708e11c1082102a1142284508e0e41c8010020080100200411c2384708a0082384708e11c238470421140080206c0181b0470140f01d03a0700e01d03a0240480403a02e0e81d04208410810842084108210420840e4210010040f82103c0341951ea7f0420840a84508a1146283907200400802004008012a53b2acc22802b52a96f8aa1c7eacc1084500200b5f3c264895c0403a0700e01c0380700e01c0380700e01c0380700e01c0380340e01c0380700040102807c0f80b83e07c03c1f01707c0f81f03e0241b520a850427d40a84508c1186d84308600400802004008012b0090aa823002540a8150048540a80f98460020081a03400896406038 = true := by decide +kernel
theorem chk_5_30 : checkRange 4 f5 f4 883 142 5 0xdcab3544668cf84f3daa951d84f580a49402c00d091c1d0080d6a0d6682509ab4531acb5a603c20ace002008270330987a961197092a80c933f51289427ed604a0942684d12aa3d5e22509eaf1471e857003c20aba0020091204909c124078130720e01a0120680300204e09c139eea9752ead95b6d409c13822044514a211a22e0400804a33c466ad001038000038240480901200283509e13c2780d07e13c2784f09e13c2784800e0dc1b84608c118230460881102304608c1181002008c118158460040e00004600a0d41a848004008010480880e01c038090120240020880e0240480041201c0480040e00000000012010048090120240480461200283502a1142580b07a0542284b09612c0c0460881102204408811022044088110220440881102203606c018220430880040102a55999d561f708c1194f848558a994fa2b090a99530df1d638c2184308610c2184300200400802004008010020040d01a0044ea0802504a03211c2500f0820642384a0941280a044 = true := by decide +kernel
theorem chk_5_31 : checkRange 4 f5 f4 883 147 7 0x9c1382704e09c1382704e0941282703409c1381102209c0102704e0040f80000c35e124241ae00a0d42784f09e08c1184b09613c2784f09e13c2784f09e13c0683f09e0040104f09c1382704e09c1382704e09c1281a02200870c24aac3581d543a2f09fb841282509a1344aa995ac8d427ad6530a604a00f082b4000802468138db8495546a82704e0921242484909c1381a04e0081381f00c0d6a0d1784f59a0941284d09a2554cad146a13d68a943d4b080784159c0040123009c73424aa8350138270490921242484e09c1382704e09c1381a0046c2a251784fdc80941284d09a2554cee246a13f70292524b00078415980040122e09c6f424aa634c1382704e04a1342684a0681281a022008138273455128a427ede04a0942684d126a456a22909eb514829012403c20aca0020091404e3dab1827ac4584b0026abe0041301d280064980000240101a0cfaa554867834a8158209426ac54c2afd63809076b0c0080209c0cc261ec590b20f6ac8588b116004e09c130262985008d1170240482503423b5840081d0000106d5588483380141a84f04612c2784f09e13c0683f09e0040104e0661302784f = true := by decide +kernel
theorem chk_5_32 : checkRange 4 f5 f4 883 154 8 0x1d1ab34e65cbd97588b6c809403b1412a2544a89512a24c260950802544a82412a0384a8740e81d03a06a0e81783a354698cb17a3776e0d881284d625b6d6b2b75a3b896a04c578101432640487800738e0e81d00083105c1d1a934a654bc82c82745e09415b1046a8d51aa3546a8a4262250808d51a8243c00391a8740e81d03a07409e1d0020620b01d1a8348650bc1bc2896c009426b0edbab595bad1dc0b50262bc080a19320243c0039c607464cc91912ee0c41883102509a188310620c403c208620020080203306c1881284d0d0004010040d01a0340310741a16329852ca514929006ca381d27c4b8070eb00870c18984306608bb01284d0e8004010046187a185031034b68315a0530a58f52925200d8f401a3c49700e1d601ce00312e05bcb716c2ea5d0b981284d0e8b90492e201e10435001004010198065b41a1630947b8b096009200cae01d08a4c0090ee0086f41a02704e09c1382503409c088021bb092ab8d93435128bc27ed904a0942684d12aa676da3509fb75635a058c03c20ad20020091c04e = true := by decide +kernel
theorem chk_5_33 : checkRange 4 f5 f4 883 162 12 0x1242480083105c249f53e24566f90bbba45224849033124220493e87c0f31d03f27709a44909212401845024124f99ef3ca73c2504a2d5124f11e13c07382284508a04a1344508a1142280784111400401034066018453c60d0a00453b4764ec1cd3b65b4228f108a1169f5ca02706ae48273880f0df1cc396714df990b84512a25758636ee16402b760081882c2ea606ced9d302512d801284d0e8d19a234201e1043534067ccf1903430eacf435b6168a1319f840510d1c1234101cc85bc08b4fadc0138356dc010310585d0dd1b9338600d81bc31e512a1d44a83512a2426289080a214482451203944a896bc0041882e24cdb1b43365fc16413b1c45e8bd17a2f45e8a4262250808bd1782445e03917a2f6c8a4db122f09ed70020620b0b99b5366668bf1bc289635b6770ed559bb936f04cdac1014465c049650073906c00940e82504a094128256b4085992fa09a1d0008020080c4200626300941282104a0941282504a094128250480940702504a0940e82504a08c1280404a09412b58042cc17c04d0e8004010040621003131604a0941082504a0941282504a0941282404a03812825 = true := by decide +kernel
theorem chk_5_34 : checkRange 4 f5 f4 883 174 15 0xef0010620b88e485af95b21b00f053551189de3b913ebd56a868c34f1d9604a134f058eb116080781b3bc0040104e066132a91ed3b87700083105c44245d78ad10c82c82745e094159e042e8a51c80f0527780080209c0cc265504767725cd76acd0c0189100be8fec902509a782c6586b0003c209de00200827033099539239dc8c282eb142e3a8750ea02509a750ea1d43a803c209d400200827033098750191dc05c000e91100107710a9d4a70004188102406f8df1be37c85e6622937c13c9100209800012122244104910302450b2154208184b92ea174ba074008313fe0b89104f2400082600004824c900412400c09042884d07a0512225ca4514a9103a004189ff05c4802791e0041300002423c4782091e06047a124228390203092824c0741b924244480975a14738e40e8010627fc1711e7fc0cde40886f901a013d8758c55df2674ce99dfe00611409174404800f59d5075128a1c4a04f12800803000048ef5f80417b40c1d73fa7ecf51d40964ba259f93ee00c228122e47f0fd1e93a61289944a09274af45e83a477aef04989209e2480100600009049092082248180927d8f91e73a212c25948892 = true := by decide +kernel
theorem chk_5_35 : checkRange 4 f5 f4 883 189 17 0xa236f81045a04809012024048070120240480913e83550e1040104c060001090240480041202404928ede0208b00901202445e8bc27a2f052008260300008bc12024048090120240480880e0240494eedd0208ac0901202452613f7084100413018000ba00925ddb8041150120240480901229309f93c208020980c0005ce0494dedb0208a40900f00e0480901229309eb34208020980c0002cd0494f6da0208a0090120240480900e0240480901229309fb8c208020980c0005cc0487a225dabb5512aa9d523d27a0f41e809e7a0f41e809a7a00104c034788191e8000090071e8a476cad44483ba7b15c9e83d00041882e2011fed85a688c74ea82253d12ded75a48880c480557a9c914f4527b5968a211e8034038ef9ea5767a2a6d9cb351001284d3c4004010343c4788f103103422acf0624f878ac90010620b893483b315d21f05904f59117a2f3c00041882e24921ec857287816413a2f04a0aeb02353c16180083105c48240d8a4566f90bd5a4528a6c00010620b88f489b095c21d05904e8bc1282b3c085d14d584728e4ef44dafd5ba1c00f037558f59de = true := by decide +kernel
theorem chk_5_36 : checkRange 4 f5 f4 883 206 15 0x2244488911202a04c85812058a53872f64784707488f8304880b800224448891120010620b882477bd77aa3b1d33a4895129050608941700044889019a1a3f01e26ee1abd11d2b09d282a0c12202e0008911222405409812058a57862f34723c2748928304880b80022496785af2470062412aa9d248a0c12202e00089292e14bc51b91202801c77ce911d060910170004493e7095e08d88683c5653a50641824405c0011252dc2177a3522404c161171d224e0c12202e00089262a2cbb91a11255b3a504c1824405c001121bf45576a3322442c8a0e91210609101700044822d0921204e0d50904e3fc7e0444ebba972232317b8822c13a6701e00419a8905c84a76dd2b8d18909212424849091fe110c66e108b04e99c0780106706c172123d283027a0c41883026a0c004130201fa0648300002401c83277dca415178eaa145728955c8090020cc8882e4188210404841082104046410008220383f40c9040000400390420a414829050694248500483b41c755062147ba8cf418090020cc8882c41009012024048090120220380901250fb800822e0240480913e83550e1040104c06000109024 = true := by decide +kernel
theorem chk_5_37 : checkRange 4 f5 f4 883 221 17 0x1457146089498a81305845c8b893830ca00b80022e09e8d00102a000091dda2c082890181d29868b3034a046c9752e8304ba0b800236c4c8b81502604816264a2cc092791a125060994170004688c11702804c0382c4cd4487491622c4588b1194110619301680045931d166029398901400e4604741826305c001184cb4598024d62204c161171270619281700045c13d1400205400012093450105120303a46fd155fe9308d90b2682420c14882e0008a1142284500041882e2086fd1522b37c85d0b2294524141822905c00114228066868fc07837e8aafe496c4c858908304d20b8002284508a015026048160dfa2abf52511a2162420c16a82e0008a1142280500980705837e890e91bf4548a91522c42c4841864805a001141bf4557e2490312098910b121061918170004506fd155f69208a01400e4608588e8305960b80022837e8aafa48e4341e3112162420c32202e0008a0dfa2abe5231140260b08b90b121061908170004507a51204f4488911204d4480081502804c0c90b0000480382c521c417c23e1dd3a44441824405c0011222497f87af747aab274a078304880b800224 = true := by decide +kernel
theorem chk_5_38 : checkRange 4 f5 f4 883 238 15 0x33066008198000480cc198330660c019ce9d099fa6f26a0660cc198330640cc27e740041300002477f9c820e6e0615727ee7ccd936935383d63a88ff8324d57673800208000007505cf41226c04f09e13c2784f06413c27a6600413133000048999330414cc0c13351dcd598a6b26a4d4e27566983fe0c9332664cc9993326647c99aa2e68cc13533c312727aab4b213064999332664cc0082000001d4d7330489a013c2784f09e13c2783209e999332664cc13d330344cc09845549cc997a6767661ca21442884260c93325c066970ff25c9c795b2a4c004a1353200100413aafe5acb00c4203b84d6970f4a4409e9112224409a9100104c0808f8192440000900705ea3f9031f4b43ba918888304880c4188310620c418831062008188310620c41880004803818cbdc798ea582460620c018a4248413d21242484135210020981011f0324840001200e0bd3ff1b63295c918838304849092100208000007503c681225604f09e0c027e2a066868fc0789a78c3074aa623761338304ce0b8002674ce8b81502604816285e2ec192a03aa3424a0c14382e0008d27ae2cc152990d07863b75a0b830ca40b80062a = true := by decide +kernel
theorem chk_5_39 : checkRange 4 f5 f4 883 253 12 0x22d3eed304e0d7690344f809845517d8fb1a8b288510a2144289512a2544a887faa4f6722f09fb301a27c04c22a9fed0d8944944288511ad5b028812aa194328250c8f943543d95b0a8636fda7b381284d4cdadc3a28612aa194323509ea181a27c04c22aa3ec8d814214428851009426a66d721d14354bd7daf28327c4f89f01284d4f89f13e27c01e1053e0010040d0198363c409426a800020081a280500a001883a115aec3127c793ab35521b09faa01a27c04c22a8ceaed4d3eb5931e510a22ebe9e0041000000ea03a90244f609e13c2784f5118af4a00208000007533d381227904f09e13c2784f7ffa634b62b09fa481a27c04c22aa0e9ad213c35031a510a21440320640c8190320640ca97e8ed15398190324260c8190320640c8190320640c813032a63a33444e40640c90983209e9a00104c00009049a680829a018268a37a1b404e04ba9a948a915227fc19268 = true := by decide +kernel

theorem level_5 : ∀ i < 265, (∀ x ∈ decodeSet (f5 i), x < 81) ∧ ¬ Coverable 5 (decodeSet (f5 i)) := by
  have hlt : ∀ j < 883, ∀ x ∈ decodeSet (f4 j), x < 81 := fun j hj => (level_4 j hj).1
  have hno : ∀ j < 883, ¬ Coverable 4 (decodeSet (f4 j)) := fun j hj => (level_4 j hj).2
  intro i hi
  by_cases h0_20 : i < 104
  · by_cases h0_10 : i < 59
    · by_cases h0_5 : i < 31
      · by_cases h0_2 : i < 13
        · by_cases h0_1 : i < 7
          · exact checkRange_sound 4 f5 f4 883 hlt hno 0 7 _ chk_5_0 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 7 6 _ chk_5_1 i (by omega) (by omega)
        · by_cases h2_3 : i < 20
          · exact checkRange_sound 4 f5 f4 883 hlt hno 13 7 _ chk_5_2 i (by omega) (by omega)
          · by_cases h3_4 : i < 26
            · exact checkRange_sound 4 f5 f4 883 hlt hno 20 6 _ chk_5_3 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 26 5 _ chk_5_4 i (by omega) (by omega)
      · by_cases h5_7 : i < 41
        · by_cases h5_6 : i < 36
          · exact checkRange_sound 4 f5 f4 883 hlt hno 31 5 _ chk_5_5 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 36 5 _ chk_5_6 i (by omega) (by omega)
        · by_cases h7_8 : i < 48
          · exact checkRange_sound 4 f5 f4 883 hlt hno 41 7 _ chk_5_7 i (by omega) (by omega)
          · by_cases h8_9 : i < 54
            · exact checkRange_sound 4 f5 f4 883 hlt hno 48 6 _ chk_5_8 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 54 5 _ chk_5_9 i (by omega) (by omega)
    · by_cases h10_15 : i < 79
      · by_cases h10_12 : i < 66
        · by_cases h10_11 : i < 62
          · exact checkRange_sound 4 f5 f4 883 hlt hno 59 3 _ chk_5_10 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 62 4 _ chk_5_11 i (by omega) (by omega)
        · by_cases h12_13 : i < 70
          · exact checkRange_sound 4 f5 f4 883 hlt hno 66 4 _ chk_5_12 i (by omega) (by omega)
          · by_cases h13_14 : i < 75
            · exact checkRange_sound 4 f5 f4 883 hlt hno 70 5 _ chk_5_13 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 75 4 _ chk_5_14 i (by omega) (by omega)
      · by_cases h15_17 : i < 89
        · by_cases h15_16 : i < 84
          · exact checkRange_sound 4 f5 f4 883 hlt hno 79 5 _ chk_5_15 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 84 5 _ chk_5_16 i (by omega) (by omega)
        · by_cases h17_18 : i < 93
          · exact checkRange_sound 4 f5 f4 883 hlt hno 89 4 _ chk_5_17 i (by omega) (by omega)
          · by_cases h18_19 : i < 99
            · exact checkRange_sound 4 f5 f4 883 hlt hno 93 6 _ chk_5_18 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 99 5 _ chk_5_19 i (by omega) (by omega)
  · by_cases h20_30 : i < 142
    · by_cases h20_25 : i < 122
      · by_cases h20_22 : i < 109
        · by_cases h20_21 : i < 106
          · exact checkRange_sound 4 f5 f4 883 hlt hno 104 2 _ chk_5_20 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 106 3 _ chk_5_21 i (by omega) (by omega)
        · by_cases h22_23 : i < 112
          · exact checkRange_sound 4 f5 f4 883 hlt hno 109 3 _ chk_5_22 i (by omega) (by omega)
          · by_cases h23_24 : i < 116
            · exact checkRange_sound 4 f5 f4 883 hlt hno 112 4 _ chk_5_23 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 116 6 _ chk_5_24 i (by omega) (by omega)
      · by_cases h25_27 : i < 130
        · by_cases h25_26 : i < 127
          · exact checkRange_sound 4 f5 f4 883 hlt hno 122 5 _ chk_5_25 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 127 3 _ chk_5_26 i (by omega) (by omega)
        · by_cases h27_28 : i < 134
          · exact checkRange_sound 4 f5 f4 883 hlt hno 130 4 _ chk_5_27 i (by omega) (by omega)
          · by_cases h28_29 : i < 138
            · exact checkRange_sound 4 f5 f4 883 hlt hno 134 4 _ chk_5_28 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 138 4 _ chk_5_29 i (by omega) (by omega)
    · by_cases h30_35 : i < 189
      · by_cases h30_32 : i < 154
        · by_cases h30_31 : i < 147
          · exact checkRange_sound 4 f5 f4 883 hlt hno 142 5 _ chk_5_30 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 147 7 _ chk_5_31 i (by omega) (by omega)
        · by_cases h32_33 : i < 162
          · exact checkRange_sound 4 f5 f4 883 hlt hno 154 8 _ chk_5_32 i (by omega) (by omega)
          · by_cases h33_34 : i < 174
            · exact checkRange_sound 4 f5 f4 883 hlt hno 162 12 _ chk_5_33 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 174 15 _ chk_5_34 i (by omega) (by omega)
      · by_cases h35_37 : i < 221
        · by_cases h35_36 : i < 206
          · exact checkRange_sound 4 f5 f4 883 hlt hno 189 17 _ chk_5_35 i (by omega) (by omega)
          · exact checkRange_sound 4 f5 f4 883 hlt hno 206 15 _ chk_5_36 i (by omega) (by omega)
        · by_cases h37_38 : i < 238
          · exact checkRange_sound 4 f5 f4 883 hlt hno 221 17 _ chk_5_37 i (by omega) (by omega)
          · by_cases h38_39 : i < 253
            · exact checkRange_sound 4 f5 f4 883 hlt hno 238 15 _ chk_5_38 i (by omega) (by omega)
            · exact checkRange_sound 4 f5 f4 883 hlt hno 253 12 _ chk_5_39 i (by omega) (by omega)

theorem chk_6_0 : checkRange 5 f6 f5 265 0 6 0x580a814024286598b20c7022044b10f32c0578ae15a256560ab0590be16c0780f01e03c0780f0120240480000000000000000550a913605c098080100380680b01229c530a512d290518a20110225088594027c4c49e13a2704d81000f03c0240001440a3f47b0f61d83b0040082684c09092e2584a80812201c400790c0144138110180000000000003234c808b11820440881102210c2781101e03c0780f01e03c0800e01c03808100020038690c001c2c00704e020108080180120200001b1aa40c598c30564247091e08a144248a922e36c8d8b72324708a1122204187f0de1b03405d0b415c2982003e0780a00b00b00c000000000000000000000000000000000000000050140180102300035c7e00900032c6780f0000bc7d0e31f01340780900019c358110001a4558f01ba3b85c811012000668e61580e81c03604c0500600803a2804f09c1340b44c09612811c2984b1242404708c114220430841042003f07c0f41e03b0740e41c0370340640c01201200800800000 = true := by decide +kernel
theorem chk_6_1 : checkRange 5 f6 f5 265 6 5 0x13a2c85707028e668ca19232032064011022318630c618c3186306101e310620c401202400000136300600c0180300528be1782e0070263ee3ecfc8fb2c6764f505d0123ecb496b2da0300600c2704388610a01e000080ea010328580931502983701f1ca4145e8c5022044088110aa03c07807012000000000005dc5197b022000c718c31448cc418617e044048003085489c0aa06c038070520a01001a0210c8188310620c0180088110bc1782f05e0bc17821036084158078540120001d1e31de484910ec1d8030060a2144288510091442880601824e4c8970110000387b0080d41382504807c0c8108640c8180088110b81702e05a0b41682d05a0b41582b05601e03c0780f01e03c04809012000000000000000004206c10826038020040080100200400600c020040080100120400800c0200400801002000007010010040080460880f0180210c8188300110bc1702d0580ac03c2a0090001382601006c7947899f34279c7880c0185d8ba172148024789700184d8941262480440000e1e802033042 = true := by decide +kernel
theorem chk_6_2 : checkRange 5 f6 f5 265 11 4 0x478da1b01e00f8e520a2f4628110220440885501e03c03809000000000002ea28cbc81100062cde1b62466c0d70bf022024000d21a40506e03a01c0380700e01c038070090000380700e01c0380700e01c0380700e01c0380700e01c038070090000380700e01c0380600801c2846a0d00ec52cee1da332044089d43a4740b79c6388708e01be0c603c07809000000710e21c4040080100200400817d30260cbf8103746e0da1b23586a8d41a61c40406e0dc1b83700800e01c0380700e01c0380700e01c3580a151200818801dd4048000480020068cd29042007f8fe1041ec59cf91f03c27b8f606501e41004800200548368e81c8030040d21363085d07428a670cc12d32c32064011022318630c618c318630b01600983080f188024000ac3ea3e47b0f61e43c87905d0123c89a12a1e40300600c0304349913001e000080ec0103386008b16c2d03901f1ca4145e8c5022044088110aa03c0780701200000000000294518a50220005f0be17c2f85f0be17c04404800160098580b80700380700e01c0380700e01c0240700e01c0380600c0180380700e01c0380000e01c0200700e = true := by decide +kernel
theorem chk_6_3 : checkRange 5 f6 f5 265 15 4 0x489162202000700e01c0380700e01c0380700e01c0380480001c0380700e03e394828bd18a044088110221540780f00e02400000000000940a32480440018d2506f4919e92482fc08809000820aa13a1e2108070992104183f10a3e6428638110224387990a2ba438e790c3f64282c85f0b603c0780f01e03c0780901202400000000000000004106109d0fb1600400801002004008010020040080100200400801002003c080100200240480000004008010020040080100200400800e0200404f9021fc1f0a6a103b64b50719b33a04408965216830ef931414820c21540ca03c82009000348962032584b0088112424b89612a2424a89512a25418c0780f012000000f91f23e408010020040080102684c09612a02048891122244488911222443e4080ef1de3bc7781001c0380700e01c0380700e01c0387e81820025c700de0f44fcf01de18e044089d81e6758ad9ce3984ace51c80b217c2d80f01e03c0780f01e0240480900000000000000000690d20283885601002004008010020040048000200400801002004008010020040080100200400801001e040048000200400801002003004010 = true := by decide +kernel
theorem chk_6_4 : checkRange 5 f6 f5 265 19 3 0x2548f91c10c040080100200400801002004008010020040080100200400801001e040048000204c0f793018e0440890d1e64c09510d2544a89512a0b217c2d80f01e03c0780f01e0240480900000000000000000801000303e46001011a4688a08401c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c0240000e03e394828bd18a044088110221540780f00e02400000000000938a325c04400122244488911222442fc08809000400800181de138070892304484100e01c0380700e01c0380700e01c0380700e01c0380700e01c0380700e01c03807009012024000000000000000001c0380700e01c04008010020040080100200400800f01e01c0480000000000010020040080000200400801002004008010012000080100200400800e = true := by decide +kernel

theorem level_6 : ∀ i < 22, (∀ x ∈ decodeSet (f6 i), x < 81) ∧ ¬ Coverable 6 (decodeSet (f6 i)) := by
  have hlt : ∀ j < 265, ∀ x ∈ decodeSet (f5 j), x < 81 := fun j hj => (level_5 j hj).1
  have hno : ∀ j < 265, ¬ Coverable 5 (decodeSet (f5 j)) := fun j hj => (level_5 j hj).2
  intro i hi
  by_cases h0_2 : i < 11
  · by_cases h0_1 : i < 6
    · exact checkRange_sound 5 f6 f5 265 hlt hno 0 6 _ chk_6_0 i (by omega) (by omega)
    · exact checkRange_sound 5 f6 f5 265 hlt hno 6 5 _ chk_6_1 i (by omega) (by omega)
  · by_cases h2_3 : i < 15
    · exact checkRange_sound 5 f6 f5 265 hlt hno 11 4 _ chk_6_2 i (by omega) (by omega)
    · by_cases h3_4 : i < 19
      · exact checkRange_sound 5 f6 f5 265 hlt hno 15 4 _ chk_6_3 i (by omega) (by omega)
      · exact checkRange_sound 5 f6 f5 265 hlt hno 19 3 _ chk_6_4 i (by omega) (by omega)

theorem chk_7_0 : checkRange 6 f7 f6 22 0 1 0x4028040000240d82102a0640582303e0ac0681101e04c1281d05205c1382a050098120220400780e01a0300580a0120200380600a01000c01006 = true := by decide +kernel

theorem level_7 : ∀ i < 1, (∀ x ∈ decodeSet (f7 i), x < 81) ∧ ¬ Coverable 7 (decodeSet (f7 i)) := by
  have hlt : ∀ j < 22, ∀ x ∈ decodeSet (f6 j), x < 81 := fun j hj => (level_6 j hj).1
  have hno : ∀ j < 22, ¬ Coverable 6 (decodeSet (f6 j)) := fun j hj => (level_6 j hj).2
  intro i hi
  exact checkRange_sound 6 f7 f6 22 hlt hno 0 1 _ chk_7_0 i (by omega) (by omega)

theorem main_proof :
    ∀ w : List (BitVec 8), w.length ≤ 7 →
      (∀ p v q, w = p ++ v :: q →
        ∃ a ∈ baseBV ++ p, ∃ b ∈ baseBV ++ p, v = a &&& b ∨ v = a ||| b) →
      ¬ ((204 : BitVec 8) ∈ w ∧ (170 : BitVec 8) ∈ w) := by
  intro w hlen hg ⟨h204, h170⟩
  have hno := (level_7 0 (by decide)).2
  have hdec : decodeSet (f7 0) = [40, 60] := by decide
  rw [hdec] at hno
  apply hno
  refine ⟨w.map code, by simpa using hlen, validSeq_of_bv hg, ?_⟩
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact List.mem_map_of_mem h170
  · exact List.mem_map_of_mem h204

end PEqualNP.Outside.L_lib_1314

theorem PEqualNP.Outside.L_lib_1314 :
let base : List (BitVec 8) := [0,128,192,224,240,248,252,254,255,15,51]
∀ w : List (BitVec 8), w.length ≤ 7 →
  (∀ p v q, w = p ++ v :: q →
    ∃ a ∈ base ++ p, ∃ b ∈ base ++ p, v = a &&& b ∨ v = a ||| b) →
  ¬ ((204 : BitVec 8) ∈ w ∧ (170 : BitVec 8) ∈ w) := by
  exact PEqualNP.Outside.L_lib_1314.main_proof
