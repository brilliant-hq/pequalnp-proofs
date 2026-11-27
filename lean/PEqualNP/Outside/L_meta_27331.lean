import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27331

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev Row := Fin 128
abbrev Sig := BitVec 128

def u128 (hi lo : ℕ) : Sig :=
  BitVec.ofNat 128 (Nat.lor (Nat.shiftLeft hi 64) lo)

def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def properB (a : Sig) : Bool := a != zero && a != one

theorem proper_of {a : Sig} (h : properB a = true) : proper a := by
  simp only [properB, Bool.and_eq_true, bne_iff_ne] at h
  exact h

private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin, BitVec.and_comm, BitVec.or_comm]

def bit (i : Row) (a : Sig) : Bool := a.getLsbD i.val
private theorem bit_zero (i : Row) : bit i zero = false := by simp [bit, zero]
private theorem bit_one (i : Row) : bit i one = true := by
  unfold bit one; rw [BitVec.getLsbD_allOnes]; simp [i.isLt]
private theorem bit_neg (i : Row) (a : Sig) : bit i (neg a) = !(bit i a) := by
  simp [bit, neg, i.isLt]
private theorem bit_bin (i : Row) (d : Bool) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by
  cases d <;> simp [bit, bin]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

private lemma b_read (i : Row) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i : Row) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg, bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i : Row) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit i g w (hg g (by simp))]

lemma execute_length (gs : List Gate) (w : List Sig) :
    (execute gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [execute]
  | cons g gs ih =>
    simp only [execute, List.foldl_cons] at ih ⊢
    rw [ih (w ++ [gv w g])]
    simp; omega

lemma execute_getD_lt (gs : List Gate) (w : List Sig) (j : Nat) (hj : j < w.length) :
    (execute gs w).getD j zero = w.getD j zero := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w ++ [gv w g])).getD j zero = _
    rw [ih (w ++ [gv w g]) (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma execute_getD_gate (gs : List Gate) (w : List Sig) (j : Nat) (hj : j < gs.length) :
    (execute gs w).getD (w.length + j) zero =
      gv (execute (gs.take j) w) (gs.get ⟨j, hj⟩) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      change (execute gs (w ++ [gv w g])).getD (w.length + 0) zero = gv w g
      rw [Nat.add_zero, execute_getD_lt gs (w ++ [gv w g]) w.length (by simp)]
      simp
    | succ j =>
      have hj' : j < gs.length := by simp at hj; omega
      change (execute gs (w ++ [gv w g])).getD (w.length + (j + 1)) zero = _
      have h1 := ih (w ++ [gv w g]) j hj'
      simp only [List.length_append, List.length_singleton] at h1
      rw [show w.length + (j + 1) = w.length + 1 + j by omega, h1]
      rfl

def Live (T : Sig) : Nat → Nat → Finset Sig → Prop
  | 0, t, S => t = 0 ∧ S = {T} ∧ proper T
  | k + 1, n, S =>
    (∃ t U a, n = t + 1 ∧ S = insert a U ∧ proper a ∧ neg a ∉ insert a U ∧ Live T k t (insert (neg a) U)) ∨
    (∃ U a b d, S = insert a (insert b U) ∧ proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k n (insert (bin d a b) U))

theorem Live.stop {T} (h : proper T) : Live T 0 0 {T} := ⟨rfl, rfl, h⟩
theorem Live.unary {T k t U a} (ha : proper a) (hf : neg a ∉ insert a U)
    (h : Live T k t (insert (neg a) U)) : Live T (k + 1) (t + 1) (insert a U) :=
  Or.inl ⟨_, _, _, rfl, rfl, ha, hf, h⟩
theorem Live.binary {T k t U a b d} (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hf : bin d a b ∉ insert a (insert b U)) (h : Live T k t (insert (bin d a b) U)) :
    Live T (k + 1) t (insert a (insert b U)) := Or.inr ⟨_, _, _, _, rfl, ha, hb, hab, hf, h⟩

theorem Live.ind {T} {motive : (k t : Nat) → (S : Finset Sig) → Live T k t S → Prop}
    (stop : (hp : proper T) → motive 0 0 {T} (Live.stop hp))
    (unary : ∀ {k t U a}, (ha : proper a) → (hf : neg a ∉ insert a U) → (tail : Live T k t (insert (neg a) U)) →
      motive k t (insert (neg a) U) tail → motive (k + 1) (t + 1) (insert a U) (Live.unary ha hf tail))
    (binary : ∀ {k t U a b d}, (ha : proper a) → (hb : proper b) → (hab : a ≠ b) → (hf : bin d a b ∉ insert a (insert b U)) →
      (tail : Live T k t (insert (bin d a b) U)) → motive k t (insert (bin d a b) U) tail →
      motive (k + 1) t (insert a (insert b U)) (Live.binary ha hb hab hf tail))
    {k t S} (h : Live T k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl, rfl, hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨_, _, _, rfl, rfl, hp, hf, h⟩ | ⟨_, _, _, _, rfl, ha, hb, hab, hf, h⟩
    · exact unary hp hf h (ih h)
    · exact binary ha hb hab hf h (ih h)

private lemma live_proper {T k t S} (h : Live T k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {T k t S} (h : Live T k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin, one, zero, Bool.false_eq_true, ite_false, ite_true,
    BitVec.and_allOnes, BitVec.or_zero, BitVec.and_zero, BitVec.or_allOnes,
    BitVec.and_self, BitVec.or_self, and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg, zero, one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz, ho⟩), hz, ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws a
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)

private lemma bin_not_proper_left {w : List Sig} (d : Bool) {a b : Sig}
    (ha : ¬proper a) (hb : represented w b) : represented w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have h1 : a = zero ∨ a = one := by
    by_cases hz : a = zero
    · exact Or.inl hz
    · by_cases ho : a = one
      · exact Or.inr ho
      · exact False.elim (ha ⟨hz, ho⟩)
  rcases h1 with rfl | rfl
  · rw [bin_comm]; cases d <;> simp [(bin_laws b).2.1, (bin_laws b).2.2.1, rz, hb]
  · rw [bin_comm]; cases d <;> simp [(bin_laws b).1, (bin_laws b).2.2.2.1, ro, hb]

def GateNF (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ g.inputs.length = 1) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)

private lemma gate_nf_legal {g : Gate} (h : GateNF g) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1 | h1, h2⟩ <;> simp [h1, h2]

private lemma gate_rep (w : List Sig) (g : Gate) (h : GateNF g) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  rcases h with ⟨rfl, hl⟩ | ⟨ho, hl⟩
  · rcases l with _ | ⟨i, _ | ⟨j, rest⟩⟩ <;> simp at hl
    rcases operand_cases (get_rep w i) with h0 | h1 | ⟨hm, hp⟩
    · rw [gv, List.map_cons, List.map_nil, List.headD_cons, h0, neg_laws.1]
      exact Or.inl (Or.inr (fun hh => hh.2 rfl))
    · rw [gv, List.map_cons, List.map_nil, List.headD_cons, h1, neg_laws.2]
      exact Or.inl (Or.inr (fun hh => hh.1 rfl))
    · exact Or.inr (Or.inl ⟨_, hm, hp, rfl⟩)
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨c, rest⟩⟩⟩ <;> simp at hl
    rcases ho with rfl | rfl
    · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).1] using
        bin_rep false (get_rep w i) (get_rep w j)
    · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1] using
        bin_rep true (get_rep w i) (get_rep w j)

private lemma gate_rep_collapsed (w : List Sig) (g : Gate) (h : GateNF g)
    (hnp : ∃ a ∈ g.inputs, ¬proper (w.getD a zero)) :
    represented w (gv w g) := by
  obtain ⟨o, l⟩ := g
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  rcases h with ⟨rfl, hl⟩ | ⟨ho, hl⟩
  · rcases l with _ | ⟨i, _ | ⟨j, rest⟩⟩ <;> simp at hl
    simp only [List.mem_singleton] at hnp
    obtain ⟨a, rfl, ha⟩ := hnp
    by_cases hz : w.getD a zero = zero
    · rw [gv, List.map_cons, List.map_nil, List.headD_cons, hz, neg_laws.1]; exact ro
    · by_cases hoo : w.getD a zero = one
      · rw [gv, List.map_cons, List.map_nil, List.headD_cons, hoo, neg_laws.2]; exact rz
      · exact False.elim (ha ⟨hz, hoo⟩)
  · rcases l with _ | ⟨i, _ | ⟨j, _ | ⟨c, rest⟩⟩⟩ <;> simp at hl
    rcases hnp with ⟨a, ha, hpa⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    rcases ho with rfl | rfl
    · simp only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).1]
      rcases ha with rfl | rfl
      · exact bin_not_proper_left false hpa (get_rep w j)
      · rw [bin_comm]; exact bin_not_proper_left false hpa (get_rep w i)
    · simp only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, (bin_laws _).2.1]
      rcases ha with rfl | rfl
      · exact bin_not_proper_left true hpa (get_rep w j)
      · rw [bin_comm]; exact bin_not_proper_left true hpa (get_rep w i)

private lemma gate_both_collapsed (w : List Sig) (g : Gate)
    (ho : g.op = GateOp.and ∨ g.op = GateOp.or) (a b : ℕ) (hi : g.inputs = [a, b])
    (ha : ¬proper (w.getD a zero)) (hb : ¬proper (w.getD b zero)) :
    ¬proper (gv w g) := by
  have h1 : w.getD a zero = zero ∨ w.getD a zero = one := by
    by_cases hz : w.getD a zero = zero
    · exact Or.inl hz
    · by_cases ho1 : w.getD a zero = one
      · exact Or.inr ho1
      · exact False.elim (ha ⟨hz, ho1⟩)
  have h2 : w.getD b zero = zero ∨ w.getD b zero = one := by
    by_cases hz : w.getD b zero = zero
    · exact Or.inl hz
    · by_cases ho1 : w.getD b zero = one
      · exact Or.inr ho1
      · exact False.elim (hb ⟨hz, ho1⟩)
  rcases ho with ho | ho <;> rw [gv, ho, hi] <;> simp only [List.map_cons, List.map_nil,
    List.foldr_cons, List.foldr_nil, (bin_laws _).1, (bin_laws _).2.1]
  · rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> rw [e1, e2]
    · simp [bin, zero]; exact fun h => h.1 rfl
    · simp [bin, zero, one]; exact fun h => h.1 rfl
    · simp [bin, zero, one]; exact fun h => h.1 rfl
    · simp [bin, one]; exact fun h => h.2 rfl
  · rcases h1 with e1 | e1 <;> rcases h2 with e2 | e2 <;> rw [e1, e2]
    · simp [bin, zero]; exact fun h => h.1 rfl
    · simp [bin, zero, one]; exact fun h => h.2 rfl
    · simp [bin, zero, one]; exact fun h => h.2 rfl
    · simp [bin, one]; exact fun h => h.2 rfl

private lemma pull_gate_rep {T : Sig} {w : List Sig} {z : Sig} {k t S} (h : Live T k t S)
    (hz : represented w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ t' S', Live T k t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨t, S, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · exact False.elim ((hz.resolve_left hw) (live_proper h z hm))
  · refine ⟨t, S, h, ?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma pull_gate {T : Sig} {w : List Sig} {z : Sig} {k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  rcases hz with hr | hwt
  · obtain ⟨t', S', h', hs'⟩ := pull_gate_rep h hr sub
    exact ⟨k, t', S', by omega, h', hs'⟩
  · by_cases hm : z ∈ S
    · by_cases hw : z ∈ w
      · refine ⟨k, t, S, by omega, h, ?_⟩
        intro a ha
        rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
        · exact hu
        · exact hw
      · rcases hwt with ⟨a, ha, hp', eq⟩ | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩
        · subst z
          let U := S.erase (neg a)
          have ht : Live T k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U, v ∈ w := by
            intro v hv
            obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv
            simpa [hne] using sub v hm
          have hf : neg a ∉ insert a U := by
            intro hh
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            · exact hw (hu _ u)
          exact ⟨_, _, _, Nat.le_refl _, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
        · subst z
          let U := S.erase (bin d a b)
          have ht : Live T k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
          have hu : ∀ v ∈ U, v ∈ w := by
            intro v hv
            obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv
            simpa [hne] using sub v hm
          have hf : bin d a b ∉ insert a (insert b U) := by
            intro hh
            rcases Finset.mem_insert.mp hh with eq | u
            · exact hw (eq.symm ▸ ha)
            rcases Finset.mem_insert.mp u with eq | u
            · exact hw (eq.symm ▸ hb)
            · exact hw (hu _ u)
          exact ⟨_, _, _, Nat.le_refl _, Live.binary pa pb hab hf ht, by simpa using And.intro ha (And.intro hb hu)⟩
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      have hn : a ≠ z := fun hh => hm (hh ▸ ha)
      simpa [hn] using sub a ha

noncomputable def nonPropCount (w : List Sig) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
    (by classical exact if ∃ a ∈ g.inputs, ¬proper (w.getD a zero) then 1 else 0) +
      nonPropCount (w ++ [gv w g]) gs

private lemma extract_count (T : Sig) (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, GateNF g) (hp : proper T) (hout : T ∈ execute gs w) :
    ∃ k t S, k + nonPropCount w gs ≤ gs.length ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ w := by
  classical
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {T}, by simp [nonPropCount], Live.stop hp, by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) (fun a ha => legal a (by simp [ha])) hout
    by_cases hnp : ∃ a ∈ g.inputs, ¬proper (w.getD a zero)
    · obtain ⟨t', S', h', hs'⟩ := pull_gate_rep ht (gate_rep_collapsed w g (legal g (by simp)) hnp) hs
      refine ⟨k, t', S', ?_, h', hs'⟩
      simp only [nonPropCount, if_pos hnp, List.length_cons]
      omega
    · obtain ⟨k', t', S', hk', h', hs'⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
      refine ⟨k', t', S', ?_, h', hs'⟩
      simp only [nonPropCount, if_neg hnp, Nat.zero_add, List.length_cons]
      omega

private lemma nonPropCount_pos (w : List Sig) (gs : List Gate) (j : ℕ) (hj : j < gs.length)
    (hj_np : ∃ b ∈ (gs.get ⟨j, hj⟩).inputs, ¬proper ((execute (gs.take j) w).getD b zero)) :
    1 ≤ nonPropCount w gs := by
  classical
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      have hj0 : ∃ b ∈ g.inputs, ¬proper (w.getD b zero) := by simpa [execute] using hj_np
      rw [nonPropCount, if_pos hj0]; omega
    | succ j =>
      have hj' : j < gs.length := by simp at hj; omega
      have hsub := ih (w ++ [gv w g]) j hj' (by simpa [execute, List.foldl_cons] using hj_np)
      rw [nonPropCount]; omega

private lemma nonPropCount_two (w : List Sig) (gs : List Gate) (i j : ℕ)
    (hij : i < j) (hj : j < gs.length)
    (hi_np : ∃ a ∈ (gs.get ⟨i, by omega⟩).inputs, ¬proper ((execute (gs.take i) w).getD a zero))
    (hj_np : ∃ b ∈ (gs.get ⟨j, hj⟩).inputs, ¬proper ((execute (gs.take j) w).getD b zero)) :
    2 ≤ nonPropCount w gs := by
  classical
  induction gs generalizing w i j with
  | nil => simp at hj
  | cons g gs ih =>
    cases i with
    | zero =>
      cases j with
      | zero => omega
      | succ j =>
        have hj' : j < gs.length := by simp at hj; omega
        have hi0 : ∃ a ∈ g.inputs, ¬proper (w.getD a zero) := by simpa [execute] using hi_np
        have hpos : 1 ≤ nonPropCount (w ++ [gv w g]) gs :=
          nonPropCount_pos (w ++ [gv w g]) gs j hj' (by simpa [execute, List.foldl_cons] using hj_np)
        rw [nonPropCount, if_pos hi0]; omega
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        have hj' : j < gs.length := by simp at hj; omega
        have hsub := ih (w ++ [gv w g]) i j (by omega) hj'
          (by simpa [execute, List.foldl_cons] using hi_np)
          (by simpa [execute, List.foldl_cons] using hj_np)
        simp only [nonPropCount]; omega

abbrev Wire (R : Type) := R → Bool
def inv {R} (a : Wire R) : Wire R := fun r => !(a r)
def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0
noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum
def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v
def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

def Reach {R} (roots : List (Wire R)) (q : Nat) (ws : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop, M 0 roots →
    (∀ {p bank a}, M p bank → Available bank a → M (p + 1) (inv a :: bank)) →
    (∀ {p bank a b} (d : Bool), M p bank → Available bank a → Available bank b →
      M (p + 1) (combine d a b :: bank)) → M q ws
theorem Reach.start {R} {roots : List (Wire R)} : Reach roots 0 roots := fun _ h _ _ => h
theorem Reach.one {R} {roots : List (Wire R)} {p bank a} (h : Reach roots p bank) (ha : Available bank a) :
    Reach roots (p + 1) (inv a :: bank) := fun M z u b => u (h M z @u @b) ha
theorem Reach.two {R} {roots : List (Wire R)} {p bank a b} (d : Bool) (h : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    Reach roots (p + 1) (combine d a b :: bank) := fun M z u bi => bi d (h M z @u @bi) ha hb
theorem Reach.ind {R} {roots : List (Wire R)} {motive : (p : Nat) → (bank : List (Wire R)) → Reach roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (one : ∀ {p bank a} (h : Reach roots p bank) (ha : Available bank a), motive p bank h → motive (p + 1) (inv a :: bank) (Reach.one h ha))
    (two : ∀ {p bank a b} (d : Bool) (h : Reach roots p bank) (ha : Available bank a) (hb : Available bank b),
      motive p bank h → motive (p + 1) (combine d a b :: bank) (Reach.two d h ha hb))
    {q ws} (h : Reach roots q ws) : motive q ws h := by
  have v := h (fun p bank => ∃ u : Reach roots p bank, motive p bank u) ⟨_, start⟩
    (fun ⟨u, m⟩ ha => ⟨_, one u ha m⟩) (fun d ⟨u, m⟩ ha hb => ⟨_, two d u ha hb m⟩)
  exact v.elim fun _ m => m

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x :: xs else xs

def Run {R} (goal : Wire R) (n : Nat) (ws : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop, M 0 [goal] →
  (∀ {s xs zs}, List.Perm xs zs → M s xs → M s zs) →
  (∀ {s a rest} (save : Bool), M s (inv a :: kept save a rest) → M (s + 1) (a :: rest)) →
  (∀ {s a b rest} (op ka kb : Bool), M s (combine op a b :: kept ka a (kept kb b rest)) →
      M (s + 1) (a :: b :: rest)) → M n ws
theorem Run.stop {R} {goal : Wire R} : Run goal 0 [goal] := fun _ z _ _ _ => z
theorem Run.perm {R} {goal : Wire R} {s xs zs} (hp : List.Perm xs zs) (h : Run goal s xs) :
    Run goal s zs := fun M z p u b => p hp (h M z @p @u @b)
theorem Run.one {R} {goal : Wire R} {s a rest} (save : Bool) (h : Run goal s (inv a :: kept save a rest)) :
    Run goal (s + 1) (a :: rest) := fun M z p u b => u save (h M z @p @u @b)
theorem Run.two {R} {goal : Wire R} {s a b rest} (op ka kb : Bool)
    (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))) :
    Run goal (s + 1) (a :: b :: rest) := fun M z p u bi => bi op ka kb (h M z @p @u @bi)
theorem Run.ind {R} {goal : Wire R} {motive : (n : Nat) → (xs : List (Wire R)) → Run goal n xs → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (one : ∀ {s a rest} (save : Bool) (h : Run goal s (inv a :: kept save a rest)),
      motive _ _ h → motive (s + 1) (a :: rest) (Run.one save h))
    (two : ∀ {s a b rest} (op ka kb : Bool) (h : Run goal s (combine op a b :: kept ka a (kept kb b rest))),
      motive _ _ h → motive (s + 1) (a :: b :: rest) (Run.two op ka kb h))
    {n ws} (h : Run goal n ws) : motive n ws h := by
  have v := h (fun s xs => ∃ u : Run goal s xs, motive s xs u) ⟨_, stop⟩
    (fun p ⟨u, m⟩ => ⟨_, perm p u m⟩) (fun save ⟨u, m⟩ => ⟨_, one save u m⟩)
    (fun d ka kb ⟨u, m⟩ => ⟨_, two d ka kb u m⟩)
  exact v.elim fun _ m => m

theorem mass_cons {R} (a : Wire R) (xs) : mass (a :: xs) = cost a + mass xs := by simp [mass]
theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept, mass_cons]
theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v, rfl⟩ := h; obtain ⟨w, rfl⟩ := g; cases op <;> exact ⟨_, rfl⟩
theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w :: bank) v := h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
      (∀ v, Available bank v → Available next v) ∧ q + cost a ≤ p + 1 + cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p, bank, hp, Or.inr (inv_constant c), fun _ h => h, by simp [cost, c, inv_constant c]⟩
  · exact ⟨p + 1, _, Reach.one hp ha, Or.inl (by simp), fun _ h => available_cons _ h, by simp [cost, c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
      (∀ v, Available bank v → Available next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p, bank, hp, from_constant op c ha hb, fun _ h => h, ?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b <;>
      simp [cost, ca, cb, both_constant op]; omega
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p + 1, _, Reach.two op hp ha hb, Or.inl (by simp), fun _ h => available_cons _ h,
      by simp [cost, ca, cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x = a ∨ x ∈ xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q + mass ws ≤ p + s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, W, hW, hv, hl⟩ := ih hp hsub
    exact ⟨q, W, hW, hv, by simpa only [mass, ← (eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q, W, hW, hv, by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v; apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q, W, hW, hv, hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q, W, hW, hv, ?_⟩
    rw [mass_cons, mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S := fun r => a (rows r)
theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) = kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]
theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih => simp only [List.map_cons, restrict_kept] at ih ⊢; exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons, restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p + s := by
  obtain ⟨q, bs, hq, ht, hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega

def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)
theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit, table, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp [r.isLt]
theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj; exact bit_table (observe v) ⟨j, hj⟩
theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r; exact bit_table f r
theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r; exact bit_neg _ _
theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r; cases d <;> exact bit_bin _ _ _ _
theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl
theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept, hn, ha]
theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv; simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail = kept save a rest by rfl, kept_fin, er]
      by_cases hh : a ∈ U <;> simp [save, hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz; exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    rw [List.map_cons, map_kept, obs_neg] at progress
    have perm : (a :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm, hr⟩) hv
      simp [er, eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid, kept, h, hab, ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin, kept_fin, er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j = a <;>
        by_cases bj : j = b <;> simp_all [ka, kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b :: tail) (List.nodup_cons.mpr ⟨hf, nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b :: kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons, map_kept, map_kept, obs_bin] at progress
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) hv
      ext j; by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)

theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [← table_observe (neg (table f)), obs_neg, observe_table]
theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [← table_observe (bin d (table f) (table g)), obs_bin, observe_table, observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b, rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        exact (bit_table _ ⟨j, hj⟩).trans (bit_zero ⟨j, hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq; intro j hj
        exact (bit_table _ ⟨j, hj⟩).trans (bit_one ⟨j, hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm, hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z :: w) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz; intro a hm; simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p + k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h using Reach.ind generalizing k t S with
  | start => exact ⟨k, t, S, by omega, run, sub⟩
  | @one p bank a _ ha ih =>
    rw [List.map_cons, table_inv] at sub
    obtain ⟨k', t', S', hk, run', sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l, v, U, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, v, U, by omega, hr, hs⟩
  | @two p bank a b d _ ha hb ih =>
    rw [List.map_cons, table_bin] at sub
    obtain ⟨k', t', S', hk, run', sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l, v, U, hl, hr, hs⟩ := ih run' sub'
    exact ⟨l, v, U, by omega, hr, hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l, v, U, hl, hr, hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l, v, U, by omega, hr, ?_⟩
  simpa [List.map_map, Function.comp_def, table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_, by simp, diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a, by simp, ?_⟩
      exact fun he => hd (by rw [bit_neg, bit_neg, he])
    · exact ⟨v, Finset.mem_insert_of_mem hu, hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v, hv, hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b, by simp, ?_⟩
        intro beq; exact hd (by rw [bit_bin, bit_bin, aeq, beq])
      · exact ⟨a, by simp, aeq⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu), hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v, hv, hd⟩ := live_row_difference h diff
  by_cases veq : v = a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) : Bool :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)

theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB, Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at ok
  exact ⟨rs.1, rs.2, ok.1, fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) : Bool :=
  xs.all (fun a => witnessB T raw a.1 a.2)

theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b, h⟩
  have h1 : ∀ r : Row, bit r v = b := fun r => congrFun h r
  cases b
  · apply hv.1
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    exact (h1 ⟨j, hj⟩).trans (bit_zero ⟨j, hj⟩).symm
  · apply hv.2
    apply BitVec.eq_of_getLsbD_eq; intro j hj
    exact (h1 ⟨j, hj⟩).trans (bit_one ⟨j, hj⟩).symm

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card - 1) := by
  intro p bank hr hit
  obtain ⟨k, t, S, hk, run, sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r, s, hd, iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def fixRow (fm fv : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ fm)) ||| fv) % 128, Nat.mod_lt _ (by decide)⟩

def rename (f : Row → Row) (a : Sig) : Sig := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r

def isMaskedConstant (d a : Sig) : Bool := (a &&& d == zero) || (a &&& d == d)

theorem masked_constant_sound {fm fv : Nat} {d a : Sig}
    (hdom : ∀ r : Row, bit (fixRow fm fv r) d = true)
    (hm : isMaskedConstant d a = true) :
    Constant (restrictRows (fixRow fm fv) (observe a)) := by
  simp only [isMaskedConstant, Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with hz | ho
  · refine ⟨false, funext fun r => ?_⟩
    change bit (fixRow fm fv r) a = false
    have hb : bit (fixRow fm fv r) (a &&& d) = bit (fixRow fm fv r) zero := by rw [hz]
    have h1 := bit_bin (fixRow fm fv r) false a d
    change bit (fixRow fm fv r) (a &&& d) = (bit (fixRow fm fv r) a && bit (fixRow fm fv r) d) at h1
    rw [hb, bit_zero, hdom r, Bool.and_true] at h1
    exact h1.symm
  · refine ⟨true, funext fun r => ?_⟩
    change bit (fixRow fm fv r) a = true
    have hb : bit (fixRow fm fv r) (a &&& d) = bit (fixRow fm fv r) d := by rw [ho]
    have h1 := bit_bin (fixRow fm fv r) false a d
    change bit (fixRow fm fv r) (a &&& d) = (bit (fixRow fm fv r) a && bit (fixRow fm fv r) d) at h1
    rw [hb, hdom r, Bool.and_true] at h1
    exact h1.symm

theorem count_constants {fm fv : Nat} {d : Sig}
    (hdom : ∀ r : Row, bit (fixRow fm fv r) d = true) (ws : List Sig) :
    ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows (fixRow fm fv))) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows (fixRow fm fv) (observe a)) :=
        masked_constant_sound hdom h
      simpa [cost, hc, Nat.add_comm] using Nat.succ_le_succ ih

structure SliceSpec where
  fm : Nat
  fv : Nat
  L : Nat
  dom : Sig
  ess : List (Sig × Row × Row)

def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)

def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [h.mem_erase_iff]

theorem childOne_nodup {ws : List Sig} (hn : ws.Nodup) {a : Sig} (ha : a ∈ ws)
    (hf : neg a ∉ ws) (keep : Bool) : (childOne ws a keep).Nodup := by
  have he : (ws.erase a).Nodup := hn.erase a
  have hna : a ∉ ws.erase a := fun hm => hn.not_mem_erase hm
  have hk := kept_nd keep a (ws.erase a) he hna
  refine List.nodup_cons.mpr ⟨fun hm => hf ?_, hk⟩
  rcases mem_kept hm with heq | hmem
  · rw [heq]; exact ha
  · exact List.mem_of_mem_erase hmem

theorem childTwo_nodup {ws : List Sig} (hn : ws.Nodup) {a b : Sig} (ha : a ∈ ws) (hb : b ∈ ws)
    (hab : a ≠ b) (d : Bool) (hf : bin d a b ∉ ws) (ka kb : Bool) :
    (childTwo ws a b d ka kb).Nodup := by
  have he1 : (ws.erase a).Nodup := hn.erase a
  have he2 : ((ws.erase a).erase b).Nodup := he1.erase b
  have hnb : b ∉ (ws.erase a).erase b := fun hm => he1.not_mem_erase hm
  have hk1 := kept_nd kb b ((ws.erase a).erase b) he2 hnb
  have hna : a ∉ kept kb b ((ws.erase a).erase b) := by
    intro hm
    rcases mem_kept hm with rfl | hmem
    · exact hab rfl
    · exact hn.not_mem_erase (List.mem_of_mem_erase hmem)
  have hk2 := kept_nd ka a _ hk1 hna
  refine List.nodup_cons.mpr ⟨fun hm => hf ?_, hk2⟩
  rcases mem_kept hm with heq | hm2
  · rw [heq]; exact ha
  · rcases mem_kept hm2 with heq | hmem
    · rw [heq]; exact hb
    · exact List.mem_of_mem_erase (List.mem_of_mem_erase hmem)

theorem childOne_fin {ws : List Sig} (hn : ws.Nodup) {a : Sig}
    (U : Finset Sig) (he : ws.toFinset = insert a U) :
    (childOne ws a (decide (a ∈ U))).toFinset = insert (neg a) U := by
  classical
  ext x
  have h1 : ∀ y, y ∈ ws.erase a ↔ y ≠ a ∧ y ∈ ws := fun y => hn.mem_erase_iff
  have hk : ∀ y, y ∈ kept (decide (a ∈ U)) a (ws.erase a) ↔
      (a ∈ U ∧ y = a) ∨ y ∈ ws.erase a := by
    intro y; by_cases haU : a ∈ U <;> simp [kept, haU]
  have hmem : ∀ y, y ∈ ws ↔ y = a ∨ y ∈ U := fun y => by
    simpa [Finset.mem_insert] using Finset.ext_iff.mp he y
  simp only [childOne, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    hk, h1, hmem]
  by_cases hxa : x = a
  · subst x; by_cases hx : a = neg a
    · exact iff_of_true (Or.inl hx) (Or.inl hx)
    · by_cases haU : a ∈ U <;> simp [hx, haU]
  · simp [hxa]

theorem childTwo_fin {ws : List Sig} (hn : ws.Nodup) {a b : Sig} (hab : a ≠ b)
    (U : Finset Sig) (he : ws.toFinset = insert a (insert b U)) :
    (childTwo ws a b d (decide (a ∈ U)) (decide (b ∈ U))).toFinset = insert (bin d a b) U := by
  classical
  ext x
  have h1 : ∀ y, y ∈ (ws.erase a).erase b ↔ y ≠ b ∧ y ≠ a ∧ y ∈ ws := by
    intro y; simp [(hn.erase a).mem_erase_iff, hn.mem_erase_iff]
  have hka : ∀ y l, y ∈ kept (decide (a ∈ U)) a l ↔ (a ∈ U ∧ y = a) ∨ y ∈ l := by
    intro y l; by_cases h : a ∈ U <;> simp [kept, h]
  have hkb : ∀ y l, y ∈ kept (decide (b ∈ U)) b l ↔ (b ∈ U ∧ y = b) ∨ y ∈ l := by
    intro y l; by_cases h : b ∈ U <;> simp [kept, h]
  have hmem : ∀ y, y ∈ ws ↔ y = a ∨ y = b ∨ y ∈ U := by
    intro y; simpa [Finset.mem_insert] using Finset.ext_iff.mp he y
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset,
    hka, hkb, h1, hmem]
  by_cases hxa : x = a
  · subst x; by_cases hx : a = bin d a b
    · exact iff_of_true (Or.inl hx) (Or.inl hx)
    · by_cases haU : a ∈ U <;> simp [hx, haU, hab]
  · by_cases hxb : x = b
    · subst x; by_cases hx : b = bin d a b
      · exact iff_of_true (Or.inl hx) (Or.inl hx)
      · by_cases hbU : b ∈ U <;> simp [hx, hbU, hxa]
    · simp [hxa, hxb]

theorem childTwo_swap_fin {ws : List Sig} (hn : ws.Nodup) {a b : Sig} (d ka kb : Bool) :
    (childTwo ws b a d kb ka).toFinset = (childTwo ws a b d ka kb).toFinset := by
  classical
  have h1 : ∀ y, y ∈ (ws.erase b).erase a ↔ y ≠ a ∧ y ≠ b ∧ y ∈ ws := by
    intro y; simp [(hn.erase b).mem_erase_iff, hn.mem_erase_iff]
  have h2 : ∀ y, y ∈ (ws.erase a).erase b ↔ y ≠ b ∧ y ≠ a ∧ y ∈ ws := by
    intro y; simp [(hn.erase a).mem_erase_iff, hn.mem_erase_iff]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
  rw [bin_comm d b a]
  have hka : ∀ y l, y ∈ kept ka a l ↔ (ka = true ∧ y = a) ∨ y ∈ l := by
    intro y l; cases ka <;> simp [kept]
  have hkb : ∀ y l, y ∈ kept kb b l ↔ (kb = true ∧ y = b) ∨ y ∈ l := by
    intro y l; cases kb <;> simp [kept]
  simp only [hka, hkb, h1, h2]
  tauto

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap - 1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    exact out (List.mem_toFinset.mp (by rw [he]; simp))
  | @unary k t U a ha hf tail _ =>
    have ha' : a ∈ ws := List.mem_toFinset.mp (by rw [he]; simp)
    have hna : neg a ∉ ws := fun hm => hf (by rw [← he]; exact List.mem_toFinset.mpr hm)
    have hna_p : proper (neg a) := live_proper tail (neg a) (by simp)
    have hlen_U : (insert (neg a) U).card + t ≤ k + 1 := (live_size tail).2
    have hfin := childOne_fin hn U he
    have hnd := childOne_nodup hn ha' hna (decide (a ∈ U))
    have hcard : (childOne ws a (decide (a ∈ U))).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup hnd, hfin]
      omega
    exact oneStep a ha' (decide (a ∈ U)) hna hna_p hcard k t (by omega) (hfin.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have ha' : a ∈ ws := List.mem_toFinset.mp (by rw [he]; simp)
    have hb' : b ∈ ws := List.mem_toFinset.mp (by rw [he]; simp)
    have hnab : bin d a b ∉ ws := fun hm => hf (by rw [← he]; exact List.mem_toFinset.mpr hm)
    have hnab_p : proper (bin d a b) := live_proper tail (bin d a b) (by simp)
    have hlen_U : (insert (bin d a b) U).card + t ≤ k + 1 := (live_size tail).2
    have hfin := childTwo_fin (d := d) hn hab U he
    have hnd := childTwo_nodup hn ha' hb' hab d hnab (decide (a ∈ U)) (decide (b ∈ U))
    have hcard : (childTwo ws a b d (decide (a ∈ U)) (decide (b ∈ U))).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup hnd, hfin]
      omega
    exact twoStep a ha' b hb' d (decide (a ∈ U)) (decide (b ∈ U)) hab hnab hnab_p hcard k t
      (by omega) (hfin.symm ▸ tail)

def inputs : List Sig := [u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, u128 0xcccccccccccccccc 0xcccccccccccccccc, u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, u128 0xffff0000ffff0000 0xffff0000ffff0000, u128 0xffffffff00000000 0xffffffff00000000, u128 0xffffffffffffffff 0x0000000000000000]
def target : Sig := u128 0xeeeaece0e0e0e0e0 0xeeeaccc0c0c0c0c0
def slices : List SliceSpec := [⟨1, 0, 3, u128 0x5555555555555555 0x5555555555555555, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨1, 1, 5, u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨5, by decide⟩, ⟨7, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨3, by decide⟩, ⟨7, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨2, 0, 4, u128 0x3333333333333333 0x3333333333333333, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨2, 2, 4, u128 0xcccccccccccccccc 0xcccccccccccccccc, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨4, 0, 4, u128 0x0f0f0f0f0f0f0f0f 0x0f0f0f0f0f0f0f0f, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨4, 4, 4, u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨8, 0, 5, u128 0x00ff00ff00ff00ff 0x00ff00ff00ff00ff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨8, 8, 5, u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨56, by decide⟩, ⟨57, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨12, by decide⟩, ⟨14, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨10, by decide⟩, ⟨14, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨16, 0, 5, u128 0x0000ffff0000ffff 0x0000ffff0000ffff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨16, 16, 5, u128 0xffff0000ffff0000 0xffff0000ffff0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨32, 32, 5, u128 0xffffffff00000000 0xffffffff00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨36, by decide⟩, ⟨38, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨34, by decide⟩, ⟨38, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨64, 0, 5, u128 0x0000000000000000 0xffffffffffffffff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨64, 64, 5, u128 0xffffffffffffffff 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨68, by decide⟩, ⟨70, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨98, by decide⟩, ⟨106, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨74, by decide⟩, ⟨106, by decide⟩)]⟩, ⟨3, 2, 2, u128 0x4444444444444444 0x4444444444444444, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨3, 1, 3, u128 0x2222222222222222 0x2222222222222222, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨3, 3, 3, u128 0x8888888888888888 0x8888888888888888, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨3, by decide⟩, ⟨7, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩)]⟩, ⟨5, 0, 2, u128 0x0505050505050505 0x0505050505050505, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨5, 1, 3, u128 0x0a0a0a0a0a0a0a0a 0x0a0a0a0a0a0a0a0a, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨41, by decide⟩, ⟨43, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩)]⟩, ⟨5, 5, 3, u128 0xa0a0a0a0a0a0a0a0 0xa0a0a0a0a0a0a0a0, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨5, by decide⟩, ⟨7, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨9, 8, 2, u128 0x5500550055005500 0x5500550055005500, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨12, by decide⟩, ⟨14, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨10, by decide⟩, ⟨14, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨9, 1, 4, u128 0x00aa00aa00aa00aa 0x00aa00aa00aa00aa, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨5, by decide⟩, ⟨7, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨3, by decide⟩, ⟨7, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨9, 9, 4, u128 0xaa00aa00aa00aa00 0xaa00aa00aa00aa00, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨13, by decide⟩, ⟨15, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨11, by decide⟩, ⟨15, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨17, 0, 3, u128 0x0000555500005555 0x0000555500005555, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨17, 16, 3, u128 0x5555000055550000 0x5555000055550000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨26, by decide⟩, ⟨58, by decide⟩)]⟩, ⟨17, 1, 4, u128 0x0000aaaa0000aaaa 0x0000aaaa0000aaaa, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨5, by decide⟩, ⟨7, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨3, by decide⟩, ⟨7, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨17, 17, 3, u128 0xaaaa0000aaaa0000 0xaaaa0000aaaa0000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨21, by decide⟩, ⟨23, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨19, by decide⟩, ⟨23, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨33, 32, 2, u128 0x5555555500000000 0x5555555500000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨36, by decide⟩, ⟨38, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨34, by decide⟩, ⟨38, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨33, 33, 4, u128 0xaaaaaaaa00000000 0xaaaaaaaa00000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨37, by decide⟩, ⟨39, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨35, by decide⟩, ⟨39, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨65, 0, 3, u128 0x0000000000000000 0x5555555555555555, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨65, 64, 3, u128 0x5555555555555555 0x0000000000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨68, by decide⟩, ⟨70, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨66, by decide⟩, ⟨70, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨98, by decide⟩, ⟨106, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨74, by decide⟩, ⟨106, by decide⟩)]⟩, ⟨65, 1, 4, u128 0x0000000000000000 0xaaaaaaaaaaaaaaaa, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨5, by decide⟩, ⟨7, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨3, by decide⟩, ⟨7, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩)]⟩, ⟨65, 65, 4, u128 0xaaaaaaaaaaaaaaaa 0x0000000000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨105, by decide⟩, ⟨107, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨99, by decide⟩, ⟨107, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨75, by decide⟩, ⟨107, by decide⟩)]⟩, ⟨6, 0, 2, u128 0x0303030303030303 0x0303030303030303, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨6, 4, 3, u128 0x3030303030303030 0x3030303030303030, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨6, 2, 3, u128 0x0c0c0c0c0c0c0c0c 0x0c0c0c0c0c0c0c0c, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨10, 0, 4, u128 0x0033003300330033 0x0033003300330033, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨10, 8, 4, u128 0x3300330033003300 0x3300330033003300, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨56, by decide⟩, ⟨57, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨73, by decide⟩, ⟨77, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨25, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨18, 0, 2, u128 0x0000333300003333 0x0000333300003333, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨18, 16, 3, u128 0x3333000033330000 0x3333000033330000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨81, by decide⟩, ⟨85, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨18, 18, 3, u128 0xcccc0000cccc0000 0xcccc0000cccc0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨19, by decide⟩, ⟨51, by decide⟩)]⟩, ⟨34, 0, 2, u128 0x0000000033333333 0x0000000033333333, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨34, 32, 3, u128 0x3333333300000000 0x3333333300000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨97, by decide⟩, ⟨101, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨34, 34, 3, u128 0xcccccccc00000000 0xcccccccc00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨34, by decide⟩, ⟨38, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩)]⟩, ⟨66, 0, 2, u128 0x0000000000000000 0x3333333333333333, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨66, 64, 3, u128 0x3333333333333333 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨81, by decide⟩, ⟨113, by decide⟩)]⟩, ⟨66, 2, 4, u128 0x0000000000000000 0xcccccccccccccccc, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨66, 66, 4, u128 0xcccccccccccccccc 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨114, by decide⟩, ⟨115, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨66, by decide⟩, ⟨70, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨98, by decide⟩, ⟨106, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨99, by decide⟩, ⟨115, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨74, by decide⟩, ⟨106, by decide⟩)]⟩, ⟨12, 0, 2, u128 0x000f000f000f000f 0x000f000f000f000f, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨12, 8, 3, u128 0x0f000f000f000f00 0x0f000f000f000f00, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨56, by decide⟩, ⟨57, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨12, 4, 4, u128 0x00f000f000f000f0 0x00f000f000f000f0, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨12, 12, 4, u128 0xf000f000f000f000 0xf000f000f000f000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨60, by decide⟩, ⟨61, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨12, by decide⟩, ⟨14, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨45, by decide⟩, ⟨61, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨29, by decide⟩, ⟨61, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨20, 0, 2, u128 0x00000f0f00000f0f 0x00000f0f00000f0f, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨20, 16, 3, u128 0x0f0f00000f0f0000 0x0f0f00000f0f0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨56, by decide⟩, ⟨58, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨20, 20, 3, u128 0xf0f00000f0f00000 0xf0f00000f0f00000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨36, 32, 3, u128 0x0f0f0f0f00000000 0x0f0f0f0f00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨36, 4, 2, u128 0x00000000f0f0f0f0 0x00000000f0f0f0f0, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨36, 36, 3, u128 0xf0f0f0f000000000 0xf0f0f0f000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨36, by decide⟩, ⟨38, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨68, 0, 4, u128 0x0000000000000000 0x0f0f0f0f0f0f0f0f, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨68, 64, 4, u128 0x0f0f0f0f0f0f0f0f 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨112, by decide⟩, ⟨113, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨104, by decide⟩, ⟨106, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨98, by decide⟩, ⟨106, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨74, by decide⟩, ⟨106, by decide⟩)]⟩, ⟨24, 0, 3, u128 0x000000ff000000ff 0x000000ff000000ff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨24, 16, 4, u128 0x00ff000000ff0000 0x00ff000000ff0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨24, 8, 4, u128 0x0000ff000000ff00 0x0000ff000000ff00, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨76, by decide⟩, ⟨77, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨12, by decide⟩, ⟨14, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨10, by decide⟩, ⟨14, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨24, 24, 4, u128 0xff000000ff000000 0xff000000ff000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨56, by decide⟩, ⟨57, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨28, by decide⟩, ⟨30, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨26, by decide⟩, ⟨30, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨25, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨29, by decide⟩, ⟨93, by decide⟩)]⟩, ⟨40, 0, 3, u128 0x0000000000ff00ff 0x0000000000ff00ff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨40, 32, 4, u128 0x00ff00ff00000000 0x00ff00ff00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨36, by decide⟩, ⟨38, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨34, by decide⟩, ⟨38, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨40, 8, 3, u128 0x00000000ff00ff00 0x00000000ff00ff00, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨76, by decide⟩, ⟨77, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨12, by decide⟩, ⟨14, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨10, by decide⟩, ⟨14, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨40, 40, 4, u128 0xff00ff0000000000 0xff00ff0000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨56, by decide⟩, ⟨57, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨105, by decide⟩, ⟨109, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨45, by decide⟩, ⟨109, by decide⟩)]⟩, ⟨72, 0, 4, u128 0x0000000000000000 0x00ff00ff00ff00ff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨72, 64, 4, u128 0x00ff00ff00ff00ff 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨68, by decide⟩, ⟨70, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨81, by decide⟩, ⟨113, by decide⟩)]⟩, ⟨72, 8, 4, u128 0x0000000000000000 0xff00ff00ff00ff00, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨56, by decide⟩, ⟨57, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨12, by decide⟩, ⟨14, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨10, by decide⟩, ⟨14, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨72, 72, 4, u128 0xff00ff00ff00ff00 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨76, by decide⟩, ⟨77, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨76, by decide⟩, ⟨78, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨73, by decide⟩, ⟨77, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨105, by decide⟩, ⟨121, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨74, by decide⟩, ⟨106, by decide⟩)]⟩, ⟨48, 0, 3, u128 0x000000000000ffff 0x000000000000ffff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨48, 32, 4, u128 0x0000ffff00000000 0x0000ffff00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨100, by decide⟩, ⟨101, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨36, by decide⟩, ⟨38, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨34, by decide⟩, ⟨38, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨48, 16, 3, u128 0x00000000ffff0000 0x00000000ffff0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨84, by decide⟩, ⟨85, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨48, 48, 3, u128 0xffff000000000000 0xffff000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨52, by decide⟩, ⟨54, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨50, by decide⟩, ⟨54, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩)]⟩, ⟨80, 64, 4, u128 0x0000ffff0000ffff 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨68, by decide⟩, ⟨70, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨98, by decide⟩, ⟨106, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨74, by decide⟩, ⟨106, by decide⟩)]⟩, ⟨80, 16, 4, u128 0x0000000000000000 0xffff0000ffff0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨80, 80, 4, u128 0xffff0000ffff0000 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨84, by decide⟩, ⟨85, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨84, by decide⟩, ⟨86, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨81, by decide⟩, ⟨85, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨114, by decide⟩, ⟨122, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨81, by decide⟩, ⟨113, by decide⟩)]⟩, ⟨96, 32, 4, u128 0x0000000000000000 0xffffffff00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨36, by decide⟩, ⟨38, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨34, by decide⟩, ⟨38, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨96, 96, 4, u128 0xffffffff00000000 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨100, by decide⟩, ⟨101, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨100, by decide⟩, ⟨102, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨97, by decide⟩, ⟨101, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨98, by decide⟩, ⟨106, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩)]⟩, ⟨11, 1, 3, u128 0x0022002200220022 0x0022002200220022, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨19, 2, 2, u128 0x0000444400004444 0x0000444400004444, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨19, 18, 2, u128 0x4444000044440000 0x4444000044440000, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨26, by decide⟩, ⟨58, by decide⟩)]⟩, ⟨67, 2, 2, u128 0x0000000000000000 0x4444444444444444, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨67, 3, 3, u128 0x0000000000000000 0x8888888888888888, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨3, by decide⟩, ⟨7, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩)]⟩, ⟨67, 67, 3, u128 0x8888888888888888 0x0000000000000000, [(u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨67, by decide⟩, ⟨71, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨99, by decide⟩, ⟨107, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨99, by decide⟩, ⟨115, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨75, by decide⟩, ⟨107, by decide⟩)]⟩, ⟨13, 5, 3, u128 0x00a000a000a000a0 0x00a000a000a000a0, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨5, by decide⟩, ⟨7, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨13, 13, 3, u128 0xa000a000a000a000 0xa000a000a000a000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨13, by decide⟩, ⟨15, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨45, by decide⟩, ⟨61, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨29, by decide⟩, ⟨61, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨21, 0, 2, u128 0x0000050500000505 0x0000050500000505, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨21, 16, 2, u128 0x0505000005050000 0x0505000005050000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨56, by decide⟩, ⟨58, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨26, by decide⟩, ⟨58, by decide⟩)]⟩, ⟨37, 37, 2, u128 0xa0a0a0a000000000 0xa0a0a0a000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨37, by decide⟩, ⟨39, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨69, 0, 2, u128 0x0000000000000000 0x0505050505050505, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨69, 1, 3, u128 0x0000000000000000 0x0a0a0a0a0a0a0a0a, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨41, by decide⟩, ⟨43, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩)]⟩, ⟨25, 9, 3, u128 0x0000aa000000aa00 0x0000aa000000aa00, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨13, by decide⟩, ⟨15, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨11, by decide⟩, ⟨15, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨11, by decide⟩, ⟨43, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨25, 17, 3, u128 0x00aa000000aa0000 0x00aa000000aa0000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨21, by decide⟩, ⟨23, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨19, by decide⟩, ⟨23, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨41, 33, 3, u128 0x00aa00aa00000000 0x00aa00aa00000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨37, by decide⟩, ⟨39, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨35, by decide⟩, ⟨39, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨41, 41, 3, u128 0xaa00aa0000000000 0xaa00aa0000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨41, by decide⟩, ⟨43, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨105, by decide⟩, ⟨109, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨45, by decide⟩, ⟨109, by decide⟩)]⟩, ⟨49, 33, 3, u128 0x0000aaaa00000000 0x0000aaaa00000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨37, by decide⟩, ⟨39, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨35, by decide⟩, ⟨39, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨35, by decide⟩, ⟨43, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨81, 0, 3, u128 0x0000000000000000 0x0000555500005555, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨81, 16, 3, u128 0x0000000000000000 0x5555000055550000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨26, by decide⟩, ⟨58, by decide⟩)]⟩, ⟨81, 64, 3, u128 0x0000555500005555 0x0000000000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨68, by decide⟩, ⟨70, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨66, by decide⟩, ⟨70, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨98, by decide⟩, ⟨106, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨74, by decide⟩, ⟨106, by decide⟩)]⟩, ⟨81, 65, 3, u128 0x0000aaaa0000aaaa 0x0000000000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨105, by decide⟩, ⟨107, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨99, by decide⟩, ⟨107, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨75, by decide⟩, ⟨107, by decide⟩)]⟩, ⟨81, 80, 3, u128 0x5555000055550000 0x0000000000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨84, by decide⟩, ⟨86, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨82, by decide⟩, ⟨86, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨114, by decide⟩, ⟨122, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨90, by decide⟩, ⟨122, by decide⟩)]⟩, ⟨97, 97, 3, u128 0xaaaaaaaa00000000 0x0000000000000000, [(u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨105, by decide⟩, ⟨107, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨97, by decide⟩, ⟨101, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨99, by decide⟩, ⟨107, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩)]⟩, ⟨14, 0, 2, u128 0x0003000300030003 0x0003000300030003, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨14, 4, 3, u128 0x0030003000300030 0x0030003000300030, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨70, 0, 2, u128 0x0000000000000000 0x0303030303030303, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨70, 2, 3, u128 0x0000000000000000 0x0c0c0c0c0c0c0c0c, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨70, 64, 2, u128 0x0303030303030303 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨112, by decide⟩, ⟨113, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨81, by decide⟩, ⟨113, by decide⟩)]⟩, ⟨26, 16, 3, u128 0x0033000000330000 0x0033000000330000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨81, by decide⟩, ⟨85, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨42, 0, 2, u128 0x0000000000330033 0x0000000000330033, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨42, 32, 3, u128 0x0033003300000000 0x0033003300000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨97, by decide⟩, ⟨101, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨74, 2, 3, u128 0x0000000000000000 0x00cc00cc00cc00cc, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨19, by decide⟩, ⟨51, by decide⟩)]⟩, ⟨74, 64, 3, u128 0x0033003300330033 0x0000000000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨97, by decide⟩, ⟨113, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨81, by decide⟩, ⟨113, by decide⟩)]⟩, ⟨50, 0, 2, u128 0x0000000000003333 0x0000000000003333, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨65, by decide⟩, ⟨69, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨82, 18, 3, u128 0x0000000000000000 0xcccc0000cccc0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨19, by decide⟩, ⟨51, by decide⟩)]⟩, ⟨98, 34, 3, u128 0x0000000000000000 0xcccccccc00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨50, by decide⟩, ⟨51, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨34, by decide⟩, ⟨38, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨35, by decide⟩, ⟨51, by decide⟩)]⟩, ⟨28, 20, 3, u128 0x00f0000000f00000 0x00f0000000f00000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨44, 36, 3, u128 0x00f000f000000000 0x00f000f000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨36, by decide⟩, ⟨38, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨37, by decide⟩, ⟨101, by decide⟩)]⟩, ⟨76, 4, 3, u128 0x0000000000000000 0x00f000f000f000f0, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨52, by decide⟩, ⟨53, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨37, by decide⟩, ⟨53, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨21, by decide⟩, ⟨53, by decide⟩)]⟩, ⟨76, 8, 3, u128 0x0000000000000000 0x0f000f000f000f00, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨56, by decide⟩, ⟨57, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨41, by decide⟩, ⟨57, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩)]⟩, ⟨52, 4, 2, u128 0x000000000000f0f0 0x000000000000f0f0, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨84, 16, 3, u128 0x0000000000000000 0x0f0f00000f0f0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨56, by decide⟩, ⟨58, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨50, by decide⟩, ⟨58, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨17, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨100, 32, 3, u128 0x0000000000000000 0x0f0f0f0f00000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩)]⟩, ⟨56, 0, 3, u128 0x00000000000000ff 0x00000000000000ff, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨68, by decide⟩, ⟨69, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]⟩, ⟨56, 8, 3, u128 0x000000000000ff00 0x000000000000ff00, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨76, by decide⟩, ⟨77, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨12, by decide⟩, ⟨14, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨10, by decide⟩, ⟨14, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨13, by decide⟩, ⟨77, by decide⟩)]⟩, ⟨56, 16, 3, u128 0x0000000000ff0000 0x0000000000ff0000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨84, by decide⟩, ⟨85, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨20, by decide⟩, ⟨22, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨18, by decide⟩, ⟨22, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨21, by decide⟩, ⟨85, by decide⟩)]⟩, ⟨56, 40, 3, u128 0x0000ff0000000000 0x0000ff0000000000, [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨108, by decide⟩, ⟨109, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨40, by decide⟩, ⟨42, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨105, by decide⟩, ⟨109, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨45, by decide⟩, ⟨109, by decide⟩)]⟩]
def rootEss : List (Sig × Row × Row) := [(u128 0xaaaaaaaaaaaaaaaa 0xaaaaaaaaaaaaaaaa, ⟨48, by decide⟩, ⟨49, by decide⟩), (u128 0xcccccccccccccccc 0xcccccccccccccccc, ⟨4, by decide⟩, ⟨6, by decide⟩), (u128 0xf0f0f0f0f0f0f0f0 0xf0f0f0f0f0f0f0f0, ⟨2, by decide⟩, ⟨6, by decide⟩), (u128 0xff00ff00ff00ff00 0xff00ff00ff00ff00, ⟨34, by decide⟩, ⟨42, by decide⟩), (u128 0xffff0000ffff0000 0xffff0000ffff0000, ⟨33, by decide⟩, ⟨49, by decide⟩), (u128 0xffffffff00000000 0xffffffff00000000, ⟨10, by decide⟩, ⟨42, by decide⟩), (u128 0xffffffffffffffff 0x0000000000000000, ⟨5, by decide⟩, ⟨69, by decide⟩)]

def stepPath (dom : Sig) : Sig × Option Sig → ℕ
  | (a, none) => if isMaskedConstant dom a then 0 else 1
  | (a, some b) => if isMaskedConstant dom a || isMaskedConstant dom b then 0 else 1

def costOnSlice (dom : Sig) (path : List (Sig × Option Sig)) : ℕ :=
  (path.map (stepPath dom)).sum

def varLit (i : Nat) (val : Bool) : Sig :=
  let v := inputs.getD i zero
  if val then v else neg v

def domStep (fm fv : Nat) (i : Nat) (acc : Sig) : Sig :=
  if fm.testBit i then acc &&& varLit i (fv.testBit i) else acc

def domMask (fm fv : Nat) : Sig :=
  ([0, 1, 2, 3, 4, 5, 6] : List Nat).foldl (fun acc i => domStep fm fv i acc) one

def checkRange (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => p n && checkRange p n

theorem checkRange_sound {p : Nat → Bool} {n : Nat} (h : checkRange p n = true) :
    ∀ k < n, p k = true := by
  induction n with
  | zero => intro k hk; omega
  | succ n ih =>
    simp only [checkRange, Bool.and_eq_true] at h
    intro k hk
    by_cases he : k = n
    · exact he ▸ h.1
    · exact ih h.2 k (by omega)

private theorem inputs_bit_chk :
    checkRange (fun i => checkRange (fun r => (inputs.getD i zero).getLsbD r == r.testBit i) 128) 7 = true := by
  decide +kernel

theorem inputs_bit (i : Fin 7) (r : Row) : bit r (inputs.getD i.val zero) = r.val.testBit i.val := by
  have h1 := checkRange_sound inputs_bit_chk i.val i.isLt
  have h2 := checkRange_sound h1 r.val r.isLt
  exact beq_iff_eq.mp h2

private theorem fixRow_testBit {fm fv : Nat} (r : Row) (i : Fin 7)
    (hfm : fm.testBit i.val = true) : (fixRow fm fv r).val.testBit i.val = fv.testBit i.val := by
  simp only [fixRow]
  have hi : i.val < 7 := i.isLt
  change (((r.val &&& (127 ^^^ fm)) ||| fv) % 2 ^ 7).testBit i.val = fv.testBit i.val
  rw [Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and,
      Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  have h127 : (127 : Nat).testBit i.val = true := by clear hfm; revert i; decide
  rw [h127, hfm]
  simp

private theorem bit_domStep {fm fv : Nat} (r : Row) (i : Fin 7) {acc : Sig}
    (hacc : bit (fixRow fm fv r) acc = true) :
    bit (fixRow fm fv r) (domStep fm fv i.val acc) = true := by
  unfold domStep
  by_cases hfm : fm.testBit i.val = true
  · rw [if_pos hfm]
    have hbin := bit_bin (fixRow fm fv r) false acc (varLit i.val (fv.testBit i.val))
    change bit (fixRow fm fv r) (acc &&& varLit i.val (fv.testBit i.val)) =
      (bit (fixRow fm fv r) acc && bit (fixRow fm fv r) (varLit i.val (fv.testBit i.val))) at hbin
    rw [hbin, hacc, Bool.true_and]
    have htb := @fixRow_testBit fm fv r i hfm
    unfold varLit
    cases hval : fv.testBit i.val
    · rw [if_neg (by simp), bit_neg, inputs_bit i, htb, hval]; rfl
    · rw [if_pos rfl, inputs_bit i, htb, hval]
  · rw [if_neg hfm]; exact hacc

theorem bit_domMask (fm fv : Nat) (r : Row) : bit (fixRow fm fv r) (domMask fm fv) = true := by
  unfold domMask
  simp only [List.foldl_cons, List.foldl_nil]
  refine bit_domStep r ⟨6, by decide⟩ (bit_domStep r ⟨5, by decide⟩ (bit_domStep r ⟨4, by decide⟩
    (bit_domStep r ⟨3, by decide⟩ (bit_domStep r ⟨2, by decide⟩ (bit_domStep r ⟨1, by decide⟩
      (bit_domStep r ⟨0, by decide⟩ (bit_one _)))))))

def witnessF (f : Row → Row) (a : Sig) (rs : Row × Row) : Bool :=
  (bit (f rs.1) target != bit (f rs.2) target) &&
  (bit (f rs.1) a != bit (f rs.2) a) &&
  inputs.all (fun w => w == a || bit (f rs.1) w == bit (f rs.2) w)

def sliceValidB (s : SliceSpec) : Bool :=
  let f := fixRow s.fm s.fv
  (s.dom == domMask s.fm s.fv) &&
  decide (s.L + 1 ≤ s.ess.length) &&
  decide (s.ess.map Prod.fst).Nodup &&
  s.ess.all (fun e => inputs.contains e.1 && witnessF f e.1 e.2)

theorem slice_essential_ok {s : SliceSpec} (hs : sliceValidB s = true) :
    proper (rename (fixRow s.fm s.fv) target) ∧
    (∀ r : Row, bit (fixRow s.fm s.fv r) s.dom = true) ∧
    Lower (inputs.map (rename (fixRow s.fm s.fv))) (rename (fixRow s.fm s.fv) target) s.L := by
  let f := fixRow s.fm s.fv
  simp only [sliceValidB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true,
    List.contains_eq_mem] at hs
  obtain ⟨⟨⟨hdom, hlen⟩, hnd⟩, hess⟩ := hs
  have hdom' : ∀ r : Row, bit (f r) s.dom = true := fun r => by rw [hdom]; exact bit_domMask s.fm s.fv r
  have hne_nil : s.ess ≠ [] := by intro hnil; simp [hnil] at hlen
  obtain ⟨e0, rest, heq_ess⟩ := List.exists_cons_of_ne_nil hne_nil
  have he0 := hess e0 (by rw [heq_ess]; simp)
  simp only [Bool.and_eq_true, witnessF, bne_iff_ne, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, beq_iff_eq] at he0
  have hpG : proper (rename f target) := by
    have hdiff : bit e0.2.1 (rename f target) ≠ bit e0.2.2 (rename f target) := by
      rw [bit_rename, bit_rename]; exact he0.2.1.1
    constructor
    · intro hz; rw [hz, bit_zero, bit_zero] at hdiff; exact hdiff rfl
    · intro ho; rw [ho, bit_one, bit_one] at hdiff; exact hdiff rfl
  refine ⟨hpG, hdom', ?_⟩
  let essR := s.ess.map (fun e => (rename f e.1, e.2.1, e.2.2))
  have hessR : checkEssential (rename f target) (inputs.map (rename f)) essR = true := by
    simp only [checkEssential, List.all_eq_true, essR, List.mem_map]
    rintro _ ⟨e, he, rfl⟩
    have hwe := (hess e he).2
    simp only [witnessF, witnessB, Bool.and_eq_true, bne_iff_ne, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq, List.mem_map] at hwe ⊢
    refine ⟨?_, ?_⟩
    · rw [bit_rename, bit_rename]; exact hwe.1.1
    · rintro _ ⟨w, hw, rfl⟩
      rcases hwe.2 w hw with rfl | hbit
      · exact Or.inl rfl
      · right; rw [bit_rename, bit_rename]; exact hbit
  have hndR : (essR.map Prod.fst).Nodup := by
    have hmap : essR.map Prod.fst = (s.ess.map Prod.fst).map (rename f) := by
      simp [essR, List.map_map, Function.comp_def]
    rw [hmap]
    refine List.Nodup.map_on ?_ hnd
    intro a ha b hb hab
    obtain ⟨⟨a', r1, r2⟩, ha_mem, rfl⟩ := List.mem_map.mp ha
    obtain ⟨⟨b', r1', r2'⟩, hb_mem, rfl⟩ := List.mem_map.mp hb
    have hwa := hess (a', r1, r2) ha_mem
    have hwb := hess (b', r1', r2') hb_mem
    simp only [Bool.and_eq_true, decide_eq_true_eq, witnessF, bne_iff_ne, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq] at hwa
    have ha_diff : bit r1 (rename f a') ≠ bit r2 (rename f a') := by
      rw [bit_rename, bit_rename]; exact hwa.2.1.2
    by_contra hne
    rcases hwa.2.2 b' hwb.1 with rfl | hsame
    · exact hne rfl
    · have hb_same : bit r1 (rename f b') = bit r2 (rename f b') := by
        rw [bit_rename, bit_rename]; exact hsame
      rw [← hab] at hb_same
      exact ha_diff hb_same
  have hcard : s.L + 1 ≤ (essR.map Prod.fst).toFinset.card := by
    rw [List.toFinset_card_of_nodup hndR]
    simpa [essR] using hlen
  intro p bank hr ha
  have hl := lower_count hpG essR hessR p bank hr ha
  omega

set_option maxHeartbeats 4000000 in
theorem allSlicesValid : slices.all sliceValidB = true := by decide +kernel

def ValidState (ws : List Sig) (path : List (Sig × Option Sig)) : Prop :=
  ws.Nodup ∧ (∀ a ∈ ws, proper a) ∧
  ∀ (sl : SliceSpec), sl ∈ slices →
    ∃ bank, Reach ((inputs.map (rename (fixRow sl.fm sl.fv))).map observe) (costOnSlice sl.dom path) bank ∧
      supply bank ((ws.map observe).map (restrictRows (fixRow sl.fm sl.fv)))

theorem validState_init : ValidState inputs [] := by
  refine ⟨by decide +kernel, fun a ha => ?_, fun sl _ => ?_⟩
  · have : inputs.all properB = true := by decide +kernel
    exact proper_of (List.all_eq_true.mp this a ha)
  · refine ⟨(inputs.map (rename (fixRow sl.fm sl.fv))).map observe, Reach.start, ?_⟩
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    rw [← observe_rename]
    exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem ha))

theorem validState_one {ws path a keep} (hv : ValidState ws path) (ha : a ∈ ws)
    (hp : proper (neg a)) (hna : neg a ∉ ws) :
    ValidState (childOne ws a keep) ((a, none) :: path) := by
  obtain ⟨hnd, hprop, hreach⟩ := hv
  refine ⟨childOne_nodup hnd ha hna keep, fun v hv' => ?_, fun sl hsl => ?_⟩
  · simp only [childOne, List.mem_cons] at hv'
    rcases hv' with rfl | hv'
    · exact hp
    · rcases mem_kept hv' with heq | hv''
      · rw [heq]; exact hprop a ha
      · exact hprop v (List.mem_of_mem_erase hv'')
  · obtain ⟨bank, hr, hsup⟩ := hreach sl hsl
    let f := fixRow sl.fm sl.fv
    have hdom : ∀ r : Row, bit (f r) sl.dom = true := by
      exact (slice_essential_ok (List.all_eq_true.mp allSlicesValid sl hsl)).2.1
    have ha_avail : Available bank (restrictRows f (observe a)) :=
      hsup _ (List.mem_map_of_mem (List.mem_map_of_mem ha))
    have htail_sup : ∀ v ∈ kept keep a (ws.erase a),
        Available bank (restrictRows f (observe v)) := by
      intro v hv'
      have hvw : v ∈ ws := by
        rcases mem_kept hv' with rfl | hv''
        · exact ha
        · exact List.mem_of_mem_erase hv''
      exact hsup _ (List.mem_map_of_mem (List.mem_map_of_mem hvw))
    by_cases hmc : isMaskedConstant sl.dom a = true
    · refine ⟨bank, ?_, ?_⟩
      · simpa [costOnSlice, stepPath, hmc] using hr
      · intro w hw
        obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hw
        obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hm
        simp only [childOne, List.mem_cons] at hv'
        rcases hv' with rfl | hv'
        · rw [obs_neg]
          exact Or.inr (inv_constant (masked_constant_sound hdom hmc))
        · exact htail_sup v hv'
    · refine ⟨inv (restrictRows f (observe a)) :: bank, ?_, ?_⟩
      · have hmc' : isMaskedConstant sl.dom a = false := Bool.eq_false_iff.mpr hmc
        have : costOnSlice sl.dom ((a, none) :: path) = costOnSlice sl.dom path + 1 := by
          simp [costOnSlice, stepPath, hmc', Nat.add_comm]
        rw [this]
        exact Reach.one hr ha_avail
      · intro w hw
        obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hw
        obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hm
        simp only [childOne, List.mem_cons] at hv'
        rcases hv' with rfl | hv'
        · change Available _ (restrictRows f (observe (neg a)))
          rw [obs_neg]; exact Or.inl List.mem_cons_self
        · exact available_cons _ (htail_sup v hv')

theorem validState_two {ws path a b d ka kb} (hv : ValidState ws path)
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (hp : proper (bin d a b)) (hnab : bin d a b ∉ ws) :
    ValidState (childTwo ws a b d ka kb) ((a, some b) :: path) := by
  obtain ⟨hnd, hprop, hreach⟩ := hv
  refine ⟨childTwo_nodup hnd ha hb hab d hnab ka kb, fun v hv' => ?_, fun sl hsl => ?_⟩
  · simp only [childTwo, List.mem_cons] at hv'
    rcases hv' with rfl | hv'
    · exact hp
    · rcases mem_kept hv' with heq | hv''
      · rw [heq]; exact hprop a ha
      · rcases mem_kept hv'' with heq | hv'''
        · rw [heq]; exact hprop b hb
        · exact hprop v (List.mem_of_mem_erase (List.mem_of_mem_erase hv'''))
  · obtain ⟨bank, hr, hsup⟩ := hreach sl hsl
    let f := fixRow sl.fm sl.fv
    have hdom : ∀ r : Row, bit (f r) sl.dom = true := by
      exact (slice_essential_ok (List.all_eq_true.mp allSlicesValid sl hsl)).2.1
    have ha_avail : Available bank (restrictRows f (observe a)) :=
      hsup _ (List.mem_map_of_mem (List.mem_map_of_mem ha))
    have hb_avail : Available bank (restrictRows f (observe b)) :=
      hsup _ (List.mem_map_of_mem (List.mem_map_of_mem hb))
    have htail_sup : ∀ v ∈ kept ka a (kept kb b ((ws.erase a).erase b)),
        Available bank (restrictRows f (observe v)) := by
      intro v hv'
      have hvw : v ∈ ws := by
        rcases mem_kept hv' with rfl | hv''
        · exact ha
        · rcases mem_kept hv'' with rfl | hv'''
          · exact hb
          · exact List.mem_of_mem_erase (List.mem_of_mem_erase hv''')
      exact hsup _ (List.mem_map_of_mem (List.mem_map_of_mem hvw))
    by_cases hmc : (isMaskedConstant sl.dom a || isMaskedConstant sl.dom b) = true
    · refine ⟨bank, ?_, ?_⟩
      · simpa [costOnSlice, stepPath, hmc] using hr
      · intro w hw
        obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hw
        obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hm
        simp only [childTwo, List.mem_cons] at hv'
        rcases hv' with rfl | hv'
        · have hc : Constant (restrictRows f (observe a)) ∨ Constant (restrictRows f (observe b)) := by
            rcases Bool.or_eq_true _ _ |>.mp hmc with ha1 | hb1
            · exact Or.inl (masked_constant_sound hdom ha1)
            · exact Or.inr (masked_constant_sound hdom hb1)
          have : restrictRows f (observe (bin d a b)) =
              combine d (restrictRows f (observe a)) (restrictRows f (observe b)) := by
            rw [obs_bin]; cases d <;> rfl
          rw [this]
          exact from_constant d hc ha_avail hb_avail
        · exact htail_sup v hv'
    · refine ⟨combine d (restrictRows f (observe a)) (restrictRows f (observe b)) :: bank, ?_, ?_⟩
      · have hmc' : (isMaskedConstant sl.dom a || isMaskedConstant sl.dom b) = false :=
          Bool.eq_false_iff.mpr hmc
        have : costOnSlice sl.dom ((a, some b) :: path) = costOnSlice sl.dom path + 1 := by
          simp [costOnSlice, stepPath, hmc', Nat.add_comm]
        rw [this]
        exact Reach.two d hr ha_avail hb_avail
      · intro w hw
        obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hw
        obtain ⟨v, hv', rfl⟩ := List.mem_map.mp hm
        simp only [childTwo, List.mem_cons] at hv'
        rcases hv' with rfl | hv'
        · have : restrictRows f (observe (bin d a b)) =
              combine d (restrictRows f (observe a)) (restrictRows f (observe b)) := by
            rw [obs_bin]; cases d <;> rfl
          rw [this]
          exact Or.inl (by simp)
        · exact available_cons _ (htail_sup v hv')

theorem target_proper : proper target := proper_of (by decide +kernel)

def oneKids (cap : Nat) (ws : List Sig) : List (List Sig × (Sig × Option Sig)) :=
  ws.flatMap fun a => [false, true].filterMap fun keep =>
    if properB (neg a) && !(ws.contains (neg a)) && (childOne ws a keep).length ≤ cap
    then some (childOne ws a keep, (a, none)) else none

def twoKidsAux (cap : Nat) (ws : List Sig) : List Sig → List (List Sig × (Sig × Option Sig))
  | [] => []
  | a :: rest =>
    (rest.flatMap fun b =>
      [false, true].flatMap fun d =>
        [false, true].flatMap fun ka =>
          [false, true].filterMap fun kb =>
            if properB (bin d a b) && !(ws.contains (bin d a b)) && (childTwo ws a b d ka kb).length ≤ cap
            then some (childTwo ws a b d ka kb, (a, some b)) else none) ++
    twoKidsAux cap ws rest

def genChildren (cap : Nat) (ws : List Sig) : List (List Sig × (Sig × Option Sig)) :=
  oneKids cap ws ++ twoKidsAux cap ws ws

theorem mem_oneKids {cap ws a keep} (ha : a ∈ ws) (hp : proper (neg a)) (hna : neg a ∉ ws)
    (hl : (childOne ws a keep).length ≤ cap) :
    (childOne ws a keep, (a, none)) ∈ genChildren cap ws := by
  simp only [genChildren, List.mem_append, oneKids, List.mem_flatMap, List.mem_filterMap,
    List.mem_cons, List.mem_singleton]
  left
  refine ⟨a, ha, keep, ?_, ?_⟩
  · cases keep <;> simp
  · have hpb : properB (neg a) = true := by
      simp only [properB, Bool.and_eq_true, bne_iff_ne]; exact hp
    simp [hpb, hna, hl]

theorem mem_twoKidsAux_ordered {cap ws a b d ka kb} (l : List Sig) (hws_nd : ws.Nodup)
    (hsub : ∀ x ∈ l, x ∈ ws)
    (hl_nd : l.Nodup) (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b)
    (hp : proper (bin d a b)) (hnab : bin d a b ∉ ws)
    (hl : (childTwo ws a b d ka kb).length ≤ cap) :
    (childTwo ws a b d ka kb, (a, some b)) ∈ twoKidsAux cap ws l ∨
    (childTwo ws b a d kb ka, (b, some a)) ∈ twoKidsAux cap ws l := by
  have hpb : properB (bin d a b) = true := by
    simp only [properB, Bool.and_eq_true, bne_iff_ne]; exact hp
  have hpb' : properB (bin d b a) = true := by rw [bin_comm]; exact hpb
  have hnab' : bin d b a ∉ ws := by rw [bin_comm]; exact hnab
  have hl' : (childTwo ws b a d kb ka).length ≤ cap := by
    have hnd1 := childTwo_nodup hws_nd (hsub a ha) (hsub b hb) hab d hnab ka kb
    have hnd2 := childTwo_nodup hws_nd (hsub b hb) (hsub a ha) hab.symm d (bin_comm d b a ▸ hnab) kb ka
    rw [← List.toFinset_card_of_nodup hnd2, childTwo_swap_fin hws_nd, List.toFinset_card_of_nodup hnd1]
    exact hl
  induction l with
  | nil => simp at ha
  | cons x rest ih =>
    simp only [List.mem_cons] at ha hb
    have hx_nd := (List.nodup_cons.mp hl_nd).2
    have hsub_rest : ∀ y ∈ rest, y ∈ ws := fun y hy => hsub y (List.mem_cons_of_mem _ hy)
    rcases ha with rfl | ha'
    · rcases hb with rfl | hb'
      · exact False.elim (hab rfl)
      · left
        simp only [twoKidsAux, List.mem_append, List.mem_flatMap, List.mem_filterMap,
          List.mem_cons, List.mem_singleton]
        left
        refine ⟨b, hb', d, by cases d <;> simp, ka, by cases ka <;> simp, kb, by cases kb <;> simp, ?_⟩
        simp [hpb, hnab, hl]
    · rcases hb with rfl | hb'
      · right
        simp only [twoKidsAux, List.mem_append, List.mem_flatMap, List.mem_filterMap,
          List.mem_cons, List.mem_singleton]
        left
        refine ⟨a, ha', d, by cases d <;> simp, kb, by cases kb <;> simp, ka, by cases ka <;> simp, ?_⟩
        simp [hpb', hnab', hl']
      · rcases ih hsub_rest hx_nd ha' hb' with h | h
        · left; simp only [twoKidsAux, List.mem_append]; right; exact h
        · right; simp only [twoKidsAux, List.mem_append]; right; exact h

def checkKidsWith (f : List Sig → List (Sig × Option Sig) → List Nat → Option (List Nat))
    (path : List (Sig × Option Sig)) : List (List Sig × (Sig × Option Sig)) → List Nat → Option (List Nat)
  | [], code => some code
  | ch :: cs, code =>
    match f ch.1 (ch.2 :: path) code with
    | none => none
    | some code' => checkKidsWith f path cs code'

def checkStream (cap : Nat) (ws : List Sig) (path : List (Sig × Option Sig)) (code : List Nat) :
    Option (List Nat) :=
  match code with
  | [] => none
  | (idx + 1) :: rest =>
    match slices[idx]? with
    | none => none
    | some sl =>
      if decide (costOnSlice sl.dom path + cap < sl.L + ws.countP (isMaskedConstant sl.dom))
      then some rest else none
  | 0 :: rest =>
    match cap with
    | 0 => none
    | cap' + 1 =>
      if ws.contains target then none
      else checkKidsWith (checkStream cap') path (genChildren (cap' + 1) ws) rest

theorem checkKidsWith_mem {f : List Sig → List (Sig × Option Sig) → List Nat → Option (List Nat)}
    {path cs code rem ch} (hok : checkKidsWith f path cs code = some rem)
    (hmem : ch ∈ cs) : ∃ c r, f ch.1 (ch.2 :: path) c = some r := by
  induction cs generalizing code with
  | nil => simp at hmem
  | cons c cs ih =>
    simp only [checkKidsWith] at hok
    cases hfx : f c.1 (c.2 :: path) code with
    | none => simp [hfx] at hok
    | some code' =>
      simp only [hfx] at hok
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem'
      · exact ⟨code, code', hfx⟩
      · exact ih hok hmem'

private theorem cut_sound {cap : Nat} {ws : List Sig} {path : List (Sig × Option Sig)}
    {idx : Nat} {rest rem : List Nat}
    (hok : (match slices[idx]? with
      | none => none
      | some sl =>
        if decide (costOnSlice sl.dom path + cap < sl.L + ws.countP (isMaskedConstant sl.dom))
        then some rest else none) = some rem)
    (hv : ValidState ws path) : Impossible target cap ws.toFinset := by
  intro k u hk hlive
  cases hsl : slices[idx]? with
  | none => simp [hsl] at hok
  | some sl =>
    simp only [hsl] at hok
    split_ifs at hok with hlt
    simp only [decide_eq_true_eq] at hlt
    have hsl_mem : sl ∈ slices := List.mem_of_getElem? hsl
    have hvalid := List.all_eq_true.mp allSlicesValid sl hsl_mem
    obtain ⟨hpG, hdom', hlow⟩ := slice_essential_ok hvalid
    let f := fixRow sl.fm sl.fv
    have hnc : ¬Constant (restrictRows f (observe target)) := by
      rw [← observe_rename f target]
      exact observe_proper hpG
    obtain ⟨hnd_ws, _, hreach⟩ := hv
    obtain ⟨bank, hrb, hsup⟩ := hreach sl hsl_mem
    have hb := projected_bound (fixRow sl.fm sl.fv) (list_run hlive ws hnd_ws rfl) hnc hrb hsup
      (by rw [← observe_rename f target]; exact hlow)
    have hcnt := count_constants hdom' ws
    omega

theorem checkStream_sound (cap : Nat) : ∀ ws path code rem,
    checkStream cap ws path code = some rem → ValidState ws path → Impossible target cap ws.toFinset := by
  induction cap with
  | zero =>
    intro ws path code rem hok hv
    rcases code with _ | ⟨n, rest⟩
    · simp [checkStream] at hok
    · cases n with
      | zero => simp [checkStream] at hok
      | succ idx =>
        simp only [checkStream] at hok
        exact cut_sound hok hv
  | succ cap' ih =>
    intro ws path code rem hok hv
    rcases code with _ | ⟨n, rest⟩
    · simp [checkStream] at hok
    · cases n with
      | zero =>
        simp only [checkStream] at hok
        split_ifs at hok with hnot
        have hnot' : target ∉ ws := by simpa [List.contains_eq_mem] using hnot
        have hnd : ws.Nodup := hv.1
        refine enum_step hnd hnot' ?_ ?_
        · intro a ha keep hna hpa hl
          have hmem := mem_oneKids ha hpa hna hl
          obtain ⟨c, r, htok⟩ := checkKidsWith_mem hok hmem
          exact ih _ _ c r htok (validState_one hv ha hpa hna)
        · intro a ha b hb d ka kb hab hnab hpab hl
          rcases mem_twoKidsAux_ordered ws hnd (fun _ h => h) hnd ha hb hab hpab hnab hl with h | h
          · obtain ⟨c, r, htok⟩ := checkKidsWith_mem hok (List.mem_append_right _ h)
            exact ih _ _ c r htok (validState_two hv ha hb hab hpab hnab)
          · obtain ⟨c, r, htok⟩ := checkKidsWith_mem hok (List.mem_append_right _ h)
            have hnd1 := childTwo_nodup hnd ha hb hab d hnab ka kb
            have hnd2 := childTwo_nodup hnd hb ha hab.symm d (bin_comm d b a ▸ hnab) kb ka
            have hl' : (childTwo ws b a d kb ka).length ≤ cap' + 1 := by
              rw [← List.toFinset_card_of_nodup hnd2, childTwo_swap_fin hnd, List.toFinset_card_of_nodup hnd1]
              exact hl
            have himp := ih _ _ c r htok
              (validState_two hv hb ha hab.symm (bin_comm d b a ▸ hpab) (bin_comm d b a ▸ hnab))
            simpa only [childTwo_swap_fin hnd, Nat.add_sub_cancel] using himp
      | succ idx =>
        simp only [checkStream] at hok
        exact cut_sound hok hv

def rootCodes0 : List (List Nat) := [[0, 2, 99, 2, 99, 2, 99, 2, 0, 25, 10, 25, 10, 21, 10, 25, 10, 25, 10, 81, 84, 21, 22, 81, 28, 29, 30, 21, 22, 92, 28, 29, 30, 21, 22, 21, 22, 29, 28, 2, 99, 2, 0, 31, 13, 31, 13, 21, 13, 25, 13, 31, 13, 59, 47, 21, 22, 23, 24, 81, 28, 21, 22, 23, 24, 59, 28, 21, 22, 21, 22, 23, 24, 81, 85, 21, 22, 25, 85, 81, 28, 31, 32, 21, 22, 25, 87, 93, 28, 31, 32, 21, 22, 21, 22, 21, 22, 25, 28, 25, 32, 31, 28], [0, 46, 36, 46, 36, 46, 0, 113, 3, 108, 3, 113, 3, 113, 3, 46, 3, 107, 15, 62, 15, 115, 15, 46, 15, 62, 34, 107, 34, 46, 34, 62, 39, 46, 39, 46, 42, 46, 36, 46, 36, 0, 4, 81, 4, 106, 4, 37, 4, 110, 4, 112, 35, 16, 36, 16, 0, 4, 114, 9, 106, 9, 37, 9, 43, 4, 106, 4, 37, 4, 73, 35, 37, 35, 43, 36, 37, 16, 82, 16, 35, 37, 35, 40, 35, 43, 36, 37, 36, 37, 82, 40, 36, 108, 81, 36, 37, 0, 9, 36, 9, 106, 9, 37, 9, 112, 9, 47, 46, 36, 46, 62, 46, 36, 0, 4, 114, 4, 106, 4, 37, 4, 73, 9, 106, 9, 37, 9, 43, 35, 37, 35, 43, 36, 37, 36, 36, 37, 108, 73, 46, 47, 36, 37, 36, 37, 46, 47, 81, 0, 46, 36, 82, 106, 36, 37, 84, 110, 46, 47, 46, 36, 46, 115, 46, 36, 82, 36, 36, 37, 82, 83, 46, 47, 36, 37, 36, 37, 46, 47, 81, 46, 47, 36, 37, 108, 106, 108, 106, 46, 47, 36, 37, 36, 37, 36, 37, 0, 9, 36, 9, 81, 9, 106, 9, 37, 9, 47, 46, 25, 46, 36, 46, 62, 82, 36, 82, 25, 36, 25, 46, 25, 36, 37, 46, 47, 36, 37, 110, 46, 47, 46, 47], [0, 50, 58, 50, 58, 0, 6, 93, 6, 108, 6, 121, 6, 121, 6, 59, 34, 19, 122, 19, 122, 19, 58, 19, 34, 54, 34, 57, 34, 59, 0, 6, 121, 9, 19, 9, 108, 9, 59, 6, 25, 6, 108, 6, 59, 34, 19, 58, 19, 34, 59, 54, 58, 54, 58, 57, 58, 50, 58, 50, 58, 50, 0, 120, 5, 106, 5, 50, 5, 120, 5, 120, 5, 89, 18, 50, 18, 76, 18, 89, 18, 50, 35, 76, 35, 105, 35, 50, 49, 50, 49, 76, 53, 106, 87, 50, 51, 0, 9, 58, 9, 108, 9, 51, 9, 119, 9, 59, 50, 58, 122, 58, 50, 58, 50, 76, 50, 51, 106, 73, 58, 59, 50, 51, 50, 51, 58, 59, 87, 0, 50, 58, 89, 108, 50, 51, 92, 118, 58, 59, 50, 58, 122, 58, 50, 58, 50, 89, 50, 51, 89, 90, 58, 59, 50, 51, 50, 51, 58, 59, 87, 58, 59, 50, 51, 106, 108, 106, 108, 58, 59, 50, 51, 50, 51, 50, 51, 0, 9, 58, 9, 87, 9, 108, 9, 51, 9, 59, 50, 25, 50, 58, 0, 6, 121, 6, 25, 6, 108, 6, 59, 9, 19, 9, 108, 9, 59, 34, 19, 58, 19, 34, 59, 58, 50, 76, 89, 25, 50, 25, 58, 25, 50, 51, 58, 59, 50, 51, 118, 58, 59, 58, 59], [0, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 8, 7, 36, 21, 121, 21, 62, 21, 125, 21, 68, 21, 36, 50, 36, 61, 36, 65, 36, 69, 62, 50, 121, 50, 68, 50, 62, 61, 62, 61, 68, 65], [0, 10, 9, 10, 9, 10, 9, 10, 9, 10, 9, 10, 9, 99, 25, 99, 25, 61, 25, 99, 25, 77, 25, 110, 116, 61, 62, 110, 73, 77, 76, 61, 62, 123, 73, 77, 76, 61, 62, 61, 62, 77, 73], [0, 11, 125, 11, 125, 11, 125, 11, 0, 65, 8, 65, 8, 65, 8, 65, 8, 65, 8, 37, 22, 121, 22, 62, 22, 70, 22, 37, 51, 37, 63, 37, 71, 62, 51, 70, 51, 62, 63, 11, 0, 73, 10, 73, 10, 73, 10, 65, 10, 73, 10, 100, 28, 100, 28, 61, 28, 77, 28, 110, 116, 61, 63, 77, 78, 61, 63, 77, 78, 61, 63, 11, 125, 112, 28, 124, 28, 65, 28, 73, 28, 79, 28, 112, 117, 65, 67, 73, 117, 79, 80, 65, 67, 73, 119, 79, 80, 65, 67, 65, 67, 73, 80], [0, 13, 12, 13, 12, 13, 12, 13, 12, 13, 12, 13, 12, 99, 31, 58, 31, 68, 31, 76, 31, 99, 31, 58, 46, 68, 46, 76, 46, 114, 46, 58, 70, 58, 77, 58, 79, 68, 70, 68, 70, 76, 77], [0, 36, 106, 36, 99, 112, 99, 36, 36, 3, 0, 50, 36, 99, 112, 85, 36, 7, 36, 37, 8, 6, 99, 9, 50, 50, 10, 6, 0, 89, 36, 89, 85, 36, 7, 17, 37, 8, 37, 92, 9, 17, 100, 10, 57, 85, 12, 17, 86, 13, 57, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 85, 12, 9, 86, 13, 10, 111, 50, 50, 11, 6, 99, 12, 50, 50, 13, 6, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 99, 99, 9, 100, 11, 10, 85, 12, 9, 86, 13, 10, 85, 12, 85, 86, 13, 11, 50, 36, 99, 7, 3, 0, 8, 51, 62, 67, 70, 36, 36, 8, 8, 8, 8, 36, 9, 8, 8, 8, 8, 36, 36, 8, 8, 8, 8, 36, 12, 8, 8, 8, 8, 62, 9, 49, 51, 10, 34, 121, 66, 49, 51, 11, 34, 70, 12, 49, 51, 13, 34, 62, 62, 9, 63, 11, 10, 62, 12, 9, 63, 13, 10, 70, 12, 66, 67, 13, 11, 8, 36, 36, 9, 3, 0, 10, 106, 36, 112, 77, 99, 58, 10, 10, 10, 10, 36, 7, 10, 10, 8, 10, 99, 99, 10, 10, 10, 10, 0, 12, 58, 36, 79, 12, 12, 12, 78, 34, 12, 12, 7, 12, 37, 8, 12, 12, 12, 12, 78, 11, 12, 36, 7, 36, 37, 8, 34, 58, 58, 53, 79, 11, 34, 36, 36, 7, 37, 11, 8, 12, 10, 10, 10, 10, 36, 7, 36, 37, 8, 34, 123, 74, 53, 106, 11, 34, 77, 12, 53, 78, 13, 34, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 77, 12, 74, 78, 13, 11, 10, 36, 36, 36, 3, 0, 11, 106, 36, 73, 79, 0, 58, 36, 73, 58, 36, 7, 5, 37, 8, 37, 58, 9, 5, 100, 10, 57, 79, 12, 5, 80, 13, 57, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 58, 11, 11, 11, 11, 36, 7, 11, 11, 8, 11, 99, 9, 11, 11, 10, 11, 99, 12, 11, 11, 11, 11, 36, 7, 36, 37, 8, 34, 73, 9, 55, 100, 10, 34, 79, 12, 55, 80, 13, 34, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 73, 12, 9, 80, 13, 10, 11, 36, 36, 12, 3, 0, 13, 59, 36, 76, 80, 99, 58, 13, 13, 13, 13, 36, 7, 13, 13, 8, 13, 0, 9, 59, 36, 73, 9, 9, 9, 78, 34, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 78, 11, 9, 36, 7, 36, 37, 8, 34, 59, 59, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 9, 13, 13, 10, 13, 99, 80, 13, 13, 11, 13, 36, 7, 36, 37, 8, 34, 59, 9, 58, 78, 10, 34, 59, 59, 58, 80, 11, 34, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 76, 76, 9, 78, 11, 10, 13, 36, 36, 7, 36, 37, 8, 34, 99, 9, 58, 100, 10, 34, 0, 58, 36, 36, 89, 58, 36, 3, 5, 0, 85, 36, 89, 58, 36, 7, 17, 37, 8, 16, 92, 9, 17, 85, 10, 16, 58, 12, 17, 59, 13, 16, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 36, 58, 36, 7, 5, 37, 8, 37, 58, 9, 5, 100, 10, 58, 89, 12, 5, 101, 13, 58, 89, 7, 3, 121, 8, 36, 36, 9, 3, 123, 10, 36, 36, 12, 3, 59, 13, 36, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 111, 58, 106, 11, 34, 99, 12, 89, 101, 13, 34, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 99, 99, 9, 100, 11, 10, 0, 9, 23, 58, 36, 73, 9, 3, 9, 0, 23, 58, 36, 73, 23, 23, 23, 78, 34, 16, 23, 7, 23, 37, 8, 16, 23, 23, 23, 73, 11, 16, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 23, 9, 9, 9, 9, 103, 34, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 103, 11, 9, 23, 23, 3, 85, 50, 23, 23, 7, 3, 62, 8, 23, 23, 23, 3, 73, 11, 23, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 12, 9, 110, 13, 10, 99, 12, 99, 101, 13, 11], [36], [99], [0, 2, 87, 21, 25, 28, 31, 0, 58, 21, 25, 28, 31, 21, 7, 5, 22, 8, 19, 25, 9, 5, 87, 10, 19, 58, 28, 5, 28, 11, 19, 31, 12, 5, 32, 13, 19, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 58, 2, 2, 2, 2, 0, 7, 50, 25, 28, 31, 7, 7, 7, 22, 19, 7, 7, 7, 7, 22, 10, 7, 7, 7, 7, 22, 11, 7, 7, 7, 7, 22, 13, 7, 25, 9, 18, 50, 10, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 7, 2, 2, 2, 2, 0, 9, 87, 21, 28, 31, 9, 9, 9, 87, 19, 9, 9, 7, 9, 22, 8, 9, 9, 9, 9, 28, 11, 9, 9, 9, 9, 32, 13, 9, 21, 7, 18, 22, 8, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11, 9, 2, 2, 2, 2, 0, 28, 87, 21, 25, 31, 93, 18, 28, 28, 19, 28, 21, 7, 21, 22, 8, 22, 25, 9, 25, 28, 10, 28, 31, 12, 28, 28, 13, 28, 21, 7, 18, 22, 8, 19, 25, 9, 18, 87, 10, 19, 31, 12, 18, 32, 13, 19, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 28, 2, 2, 2, 2, 0, 12, 58, 21, 25, 28, 12, 12, 12, 32, 19, 12, 12, 7, 12, 22, 8, 12, 12, 9, 12, 32, 10, 12, 12, 12, 12, 28, 11, 12, 21, 7, 18, 22, 8, 19, 25, 9, 18, 77, 10, 19, 58, 28, 18, 28, 11, 19, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 25, 25, 9, 28, 11, 10, 12, 2, 2, 2, 2, 21, 7, 18, 22, 8, 19, 25, 9, 18, 87, 10, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11], [46], [2], [0, 58, 108, 121, 99, 124, 58, 58, 36, 5, 0, 46, 87, 99, 117, 46, 0, 7, 61, 65, 46, 7, 7, 7, 88, 10, 7, 7, 7, 7, 88, 11, 7, 7, 7, 7, 47, 13, 7, 99, 64, 9, 61, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 7, 46, 46, 8, 4, 99, 9, 46, 46, 10, 4, 0, 105, 87, 99, 46, 87, 7, 33, 88, 8, 43, 99, 9, 33, 100, 10, 43, 46, 12, 33, 47, 13, 43, 87, 9, 7, 88, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 117, 46, 46, 11, 4, 58, 12, 46, 59, 13, 4, 87, 9, 7, 88, 10, 8, 87, 87, 7, 88, 11, 8, 46, 12, 7, 47, 13, 8, 99, 99, 9, 100, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 46, 58, 58, 7, 5, 0, 8, 37, 62, 67, 58, 0, 36, 62, 67, 58, 36, 9, 3, 63, 10, 36, 36, 36, 3, 67, 11, 36, 36, 12, 3, 59, 13, 36, 62, 62, 9, 63, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11, 36, 8, 8, 8, 8, 99, 9, 8, 8, 8, 8, 0, 67, 37, 62, 58, 37, 36, 37, 67, 35, 67, 62, 9, 48, 63, 10, 63, 58, 12, 48, 59, 13, 59, 37, 9, 36, 63, 10, 35, 37, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 67, 8, 8, 8, 8, 58, 12, 8, 8, 8, 8, 37, 9, 36, 63, 10, 35, 37, 37, 36, 67, 11, 35, 37, 12, 36, 59, 13, 35, 62, 62, 9, 63, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11, 8, 58, 58, 9, 5, 0, 10, 108, 61, 124, 58, 99, 36, 10, 10, 10, 10, 99, 7, 10, 10, 8, 10, 99, 99, 10, 10, 10, 10, 58, 12, 10, 10, 10, 10, 61, 7, 39, 63, 8, 35, 110, 74, 36, 108, 11, 35, 58, 12, 36, 59, 13, 35, 61, 61, 7, 63, 11, 8, 58, 12, 7, 59, 13, 8, 58, 12, 58, 59, 13, 11, 10, 58, 58, 58, 5, 0, 11, 108, 65, 73, 58, 0, 36, 36, 73, 58, 65, 7, 3, 67, 8, 36, 36, 9, 3, 100, 10, 36, 36, 12, 3, 59, 13, 36, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 36, 11, 11, 11, 11, 0, 7, 36, 61, 58, 7, 7, 7, 67, 35, 7, 7, 7, 7, 67, 10, 7, 7, 7, 7, 59, 13, 7, 36, 9, 36, 61, 10, 35, 36, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 7, 11, 11, 8, 11, 99, 9, 11, 11, 10, 11, 58, 12, 11, 11, 11, 11, 65, 7, 42, 67, 8, 35, 73, 9, 36, 100, 10, 35, 58, 12, 36, 59, 13, 35, 65, 9, 7, 67, 10, 8, 58, 12, 7, 59, 13, 8, 58, 12, 9, 59, 13, 10, 11, 58, 0, 5, 35, 49, 23, 55, 5, 5, 1, 0, 35, 49, 23, 55, 68, 7, 33, 35, 8, 4, 23, 9, 23, 24, 10, 4, 105, 55, 33, 35, 11, 4, 23, 9, 7, 24, 10, 8, 68, 55, 7, 49, 11, 8, 23, 23, 9, 24, 11, 10, 35, 5, 5, 5, 1, 0, 8, 35, 23, 55, 68, 33, 8, 8, 8, 8, 23, 9, 8, 8, 8, 8, 68, 55, 8, 8, 8, 8, 23, 9, 23, 24, 10, 14, 37, 37, 33, 35, 11, 14, 23, 23, 9, 24, 11, 10, 8, 5, 5, 5, 1, 0, 10, 35, 49, 55, 23, 23, 10, 10, 10, 10, 23, 7, 10, 10, 8, 10, 23, 23, 10, 10, 10, 10, 61, 7, 33, 35, 8, 14, 105, 55, 33, 35, 11, 14, 61, 55, 7, 49, 11, 8, 10, 5, 5, 5, 1, 0, 11, 35, 49, 23, 105, 33, 11, 11, 11, 11, 68, 7, 11, 11, 8, 11, 23, 9, 11, 11, 10, 11, 65, 7, 33, 35, 8, 14, 23, 9, 23, 24, 10, 14, 23, 9, 7, 24, 10, 8, 11, 5, 68, 7, 33, 35, 8, 14, 23, 9, 23, 24, 10, 14, 105, 55, 33, 35, 11, 14, 23, 9, 7, 24, 10, 8, 68, 55, 7, 49, 11, 8, 23, 23, 9, 24, 11, 10, 12, 5, 0, 13, 47, 69, 76, 80, 58, 36, 13, 13, 13, 13, 58, 7, 13, 13, 8, 13, 58, 9, 13, 13, 10, 13, 58, 58, 13, 13, 11, 13, 69, 7, 45, 47, 8, 35, 76, 9, 36, 47, 10, 35, 114, 80, 36, 47, 11, 35, 69, 9, 7, 71, 10, 8, 69, 69, 7, 71, 11, 8, 76, 76, 9, 78, 11, 10, 13, 58, 0, 7, 58, 61, 65, 58, 7, 5, 3, 0, 87, 61, 65, 58, 99, 9, 33, 61, 10, 19, 107, 64, 33, 65, 11, 19, 58, 12, 33, 59, 13, 19, 99, 64, 9, 61, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11, 58, 7, 7, 7, 3, 100, 10, 7, 7, 7, 3, 124, 11, 7, 7, 7, 3, 59, 13, 7, 58, 9, 5, 61, 10, 58, 58, 58, 5, 65, 11, 58, 68, 12, 5, 69, 13, 58, 99, 64, 9, 61, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11, 7, 107, 108, 8, 35, 99, 9, 36, 100, 10, 35, 0, 36, 58, 36, 99, 58, 36, 5, 3, 0, 87, 36, 99, 58, 36, 7, 33, 37, 8, 19, 99, 9, 33, 87, 10, 19, 58, 12, 33, 59, 13, 19, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 58, 36, 107, 7, 3, 121, 8, 36, 36, 9, 3, 100, 10, 36, 36, 12, 3, 59, 13, 36, 36, 7, 5, 37, 8, 37, 58, 9, 5, 110, 10, 58, 105, 12, 5, 114, 13, 58, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 124, 36, 108, 11, 35, 58, 12, 36, 59, 13, 35, 99, 9, 7, 100, 10, 8, 0, 7, 58, 36, 61, 58, 7, 5, 7, 0, 67, 36, 61, 58, 36, 36, 36, 67, 35, 19, 99, 9, 48, 61, 10, 19, 58, 12, 48, 59, 13, 19, 36, 9, 36, 61, 10, 35, 36, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 58, 7, 7, 7, 7, 108, 35, 7, 7, 7, 7, 100, 10, 7, 7, 7, 7, 59, 13, 7, 36, 36, 5, 87, 36, 58, 58, 9, 5, 61, 10, 58, 68, 12, 5, 69, 13, 58, 36, 9, 36, 61, 10, 35, 36, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 124, 7, 121, 11, 8, 58, 12, 7, 59, 13, 8, 99, 99, 9, 100, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11], [58]]
def rootCodes1 : List (List Nat) := [[99], [0, 2, 81, 21, 25, 28, 31, 0, 36, 21, 25, 28, 31, 21, 7, 3, 22, 8, 16, 25, 9, 3, 85, 10, 16, 36, 28, 3, 28, 11, 16, 31, 12, 3, 32, 13, 16, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 36, 2, 2, 2, 2, 0, 7, 36, 25, 28, 31, 7, 7, 7, 22, 16, 7, 7, 7, 7, 22, 10, 7, 7, 7, 7, 22, 11, 7, 7, 7, 7, 22, 13, 7, 25, 9, 15, 61, 10, 16, 36, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 7, 2, 2, 2, 2, 0, 9, 81, 21, 28, 31, 9, 9, 9, 85, 16, 9, 9, 7, 9, 22, 8, 9, 9, 9, 9, 28, 11, 9, 9, 9, 9, 32, 13, 9, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11, 9, 2, 2, 2, 2, 0, 28, 81, 21, 25, 31, 81, 15, 28, 28, 16, 28, 21, 7, 21, 22, 8, 22, 25, 9, 25, 28, 10, 28, 31, 12, 28, 28, 13, 28, 21, 7, 15, 22, 8, 16, 25, 9, 15, 85, 10, 16, 31, 12, 15, 32, 13, 16, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 28, 2, 2, 2, 2, 0, 12, 46, 21, 25, 28, 12, 12, 12, 32, 16, 12, 12, 7, 12, 22, 8, 12, 12, 9, 12, 32, 10, 12, 12, 12, 12, 28, 11, 12, 21, 7, 15, 22, 8, 16, 25, 9, 15, 46, 10, 16, 81, 28, 15, 28, 11, 16, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 25, 25, 9, 28, 11, 10, 12, 2, 2, 2, 2, 21, 7, 15, 22, 8, 16, 25, 9, 15, 85, 10, 16, 81, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11], [50], [2], [0, 7, 36, 50, 61, 65, 68, 7, 7, 7, 0, 22, 50, 61, 65, 46, 36, 36, 22, 22, 22, 4, 36, 9, 22, 22, 10, 4, 36, 36, 22, 22, 11, 4, 36, 12, 22, 22, 13, 4, 94, 9, 35, 50, 10, 50, 108, 64, 35, 50, 11, 50, 46, 12, 35, 47, 13, 47, 94, 64, 9, 61, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 36, 7, 7, 7, 7, 0, 22, 36, 61, 65, 68, 36, 36, 22, 22, 22, 6, 99, 9, 22, 22, 10, 6, 125, 64, 22, 22, 11, 6, 68, 12, 22, 22, 13, 6, 36, 9, 34, 61, 10, 36, 36, 36, 34, 65, 11, 36, 36, 12, 34, 69, 13, 36, 94, 64, 9, 61, 11, 10, 68, 12, 9, 61, 13, 10, 68, 12, 64, 65, 13, 11, 50, 7, 7, 7, 7, 0, 10, 36, 50, 65, 68, 36, 36, 10, 10, 10, 10, 99, 50, 10, 10, 10, 10, 99, 64, 10, 10, 10, 10, 68, 12, 10, 10, 10, 10, 36, 36, 36, 50, 50, 36, 36, 36, 36, 65, 11, 36, 36, 12, 36, 69, 13, 36, 123, 64, 50, 50, 11, 50, 68, 12, 50, 50, 13, 50, 68, 12, 64, 65, 13, 11, 10, 7, 7, 7, 7, 0, 11, 36, 50, 61, 68, 36, 36, 11, 11, 11, 11, 125, 50, 11, 11, 11, 11, 99, 9, 11, 11, 10, 11, 68, 12, 11, 11, 11, 11, 36, 36, 36, 50, 50, 36, 36, 9, 36, 61, 10, 36, 36, 12, 36, 69, 13, 36, 73, 9, 50, 50, 10, 50, 68, 12, 50, 50, 13, 50, 68, 12, 9, 61, 13, 10, 11, 7, 7, 7, 7, 0, 13, 36, 50, 61, 65, 36, 36, 13, 13, 13, 13, 68, 50, 13, 13, 13, 13, 68, 9, 13, 13, 10, 13, 68, 64, 13, 13, 11, 13, 36, 36, 36, 47, 47, 36, 36, 9, 36, 47, 10, 36, 36, 36, 36, 47, 11, 36, 59, 9, 50, 50, 10, 50, 59, 59, 50, 50, 11, 50, 76, 64, 9, 61, 11, 10, 13, 7, 36, 36, 36, 50, 50, 36, 36, 9, 36, 61, 10, 36, 36, 36, 36, 65, 11, 36, 36, 12, 36, 69, 13, 36, 99, 9, 50, 50, 10, 50, 125, 64, 50, 50, 11, 50, 68, 12, 50, 50, 13, 50, 99, 64, 9, 61, 11, 10, 68, 12, 9, 61, 13, 10, 68, 12, 64, 65, 13, 11], [7], [99], [0, 2, 37, 51, 25, 28, 31, 0, 36, 51, 25, 28, 31, 36, 18, 3, 51, 19, 16, 25, 9, 3, 63, 10, 16, 36, 28, 3, 28, 11, 16, 31, 12, 3, 32, 13, 16, 25, 9, 18, 51, 10, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 36, 2, 2, 2, 2, 0, 51, 37, 25, 28, 31, 37, 15, 5, 51, 16, 19, 25, 9, 5, 51, 10, 19, 58, 28, 5, 28, 11, 19, 31, 12, 5, 32, 13, 19, 25, 9, 15, 63, 10, 16, 37, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 51, 2, 2, 2, 2, 0, 9, 37, 51, 28, 31, 9, 9, 9, 63, 16, 9, 9, 9, 9, 51, 19, 9, 9, 9, 9, 28, 11, 9, 9, 9, 9, 32, 13, 9, 37, 18, 15, 51, 19, 16, 37, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 31, 12, 28, 28, 13, 11, 9, 2, 2, 2, 2, 0, 28, 37, 51, 25, 31, 37, 15, 28, 28, 16, 28, 93, 18, 28, 28, 19, 28, 25, 9, 25, 28, 10, 28, 31, 12, 28, 28, 13, 28, 37, 18, 15, 51, 19, 16, 25, 9, 15, 63, 10, 16, 31, 12, 15, 32, 13, 16, 25, 9, 18, 51, 10, 19, 31, 12, 18, 32, 13, 19, 25, 12, 9, 32, 13, 10, 28, 2, 2, 2, 2, 0, 12, 37, 51, 25, 28, 12, 12, 12, 32, 16, 12, 12, 12, 12, 32, 19, 12, 12, 9, 12, 32, 10, 12, 12, 12, 12, 28, 11, 12, 37, 18, 15, 46, 19, 16, 25, 9, 15, 46, 10, 16, 37, 28, 15, 28, 11, 16, 25, 9, 18, 51, 10, 19, 58, 28, 18, 28, 11, 19, 25, 25, 9, 28, 11, 10, 12, 2, 2, 2, 2, 37, 18, 15, 51, 19, 16, 25, 9, 15, 63, 10, 16, 37, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 25, 9, 18, 51, 10, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11], [8], [2], [0, 9, 0, 9, 36, 46, 36, 46, 62, 46, 36, 0, 4, 114, 4, 106, 4, 37, 4, 73, 9, 106, 9, 37, 9, 43, 35, 37, 35, 43, 36, 37, 36, 9, 106, 9, 37, 9, 112, 9, 47, 36, 37, 108, 73, 46, 47, 36, 37, 36, 37, 46, 47, 0, 9, 58, 50, 58, 122, 58, 50, 58, 50, 76, 9, 108, 9, 51, 9, 119, 9, 59, 50, 51, 106, 73, 58, 59, 50, 51, 50, 51, 58, 59, 62, 73, 76, 9, 9, 9, 0, 46, 108, 62, 73, 46, 0, 58, 62, 73, 46, 58, 7, 5, 62, 8, 58, 58, 58, 5, 73, 11, 58, 46, 12, 5, 47, 13, 47, 95, 72, 7, 62, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 58, 46, 46, 46, 4, 125, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 0, 12, 58, 62, 73, 12, 12, 12, 47, 47, 12, 12, 7, 12, 47, 8, 12, 12, 12, 12, 47, 11, 12, 58, 7, 35, 62, 8, 58, 58, 58, 35, 73, 11, 50, 68, 68, 7, 62, 11, 8, 12, 46, 76, 13, 4, 95, 7, 35, 62, 8, 62, 108, 72, 35, 73, 11, 50, 46, 12, 35, 47, 13, 47, 95, 72, 7, 62, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 46, 9, 9, 9, 9, 0, 50, 106, 50, 73, 76, 0, 36, 36, 73, 76, 50, 7, 3, 51, 8, 36, 36, 36, 3, 73, 11, 36, 36, 12, 3, 76, 13, 36, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 92, 12, 72, 73, 13, 11, 36, 50, 50, 46, 6, 125, 7, 50, 62, 8, 6, 125, 72, 50, 50, 11, 6, 0, 12, 46, 50, 73, 12, 12, 12, 0, 46, 50, 73, 50, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 50, 50, 7, 51, 11, 8, 46, 12, 12, 7, 12, 51, 8, 12, 12, 12, 12, 73, 11, 12, 50, 7, 34, 46, 8, 46, 106, 72, 34, 46, 11, 46, 50, 50, 7, 51, 11, 8, 12, 50, 50, 13, 6, 50, 7, 34, 51, 8, 46, 106, 72, 34, 73, 11, 46, 106, 12, 34, 76, 13, 76, 50, 50, 7, 51, 11, 8, 50, 12, 7, 51, 13, 8, 120, 12, 72, 73, 13, 11, 50, 9, 9, 7, 9, 0, 8, 37, 51, 67, 70, 125, 36, 8, 8, 8, 8, 125, 51, 8, 8, 8, 8, 0, 60, 37, 51, 70, 37, 36, 37, 67, 37, 60, 60, 49, 60, 51, 50, 51, 60, 12, 60, 67, 13, 60, 37, 37, 36, 51, 50, 37, 37, 12, 36, 71, 13, 37, 70, 12, 49, 51, 13, 50, 67, 8, 8, 8, 8, 125, 12, 8, 8, 8, 8, 37, 37, 36, 51, 50, 37, 37, 37, 36, 67, 11, 37, 37, 12, 36, 71, 13, 37, 121, 66, 49, 51, 11, 50, 70, 12, 49, 51, 13, 50, 70, 12, 66, 67, 13, 11, 8, 9, 9, 9, 9, 0, 11, 112, 119, 62, 76, 125, 36, 11, 11, 11, 11, 125, 58, 11, 11, 11, 11, 0, 7, 36, 50, 68, 7, 7, 7, 67, 36, 7, 7, 7, 7, 67, 50, 7, 7, 7, 7, 67, 13, 7, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 7, 11, 11, 8, 11, 125, 12, 11, 11, 11, 11, 112, 55, 36, 117, 50, 43, 65, 7, 42, 62, 8, 43, 79, 12, 36, 76, 13, 43, 65, 7, 55, 62, 8, 57, 79, 12, 55, 76, 13, 50, 65, 12, 7, 62, 13, 8, 11, 9, 9, 9, 9, 0, 13, 47, 59, 62, 73, 0, 29, 59, 36, 73, 29, 29, 3, 47, 47, 29, 29, 7, 3, 47, 8, 29, 29, 29, 3, 47, 11, 29, 36, 7, 36, 37, 8, 34, 59, 59, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 36, 13, 13, 13, 13, 0, 29, 47, 62, 73, 29, 29, 5, 47, 46, 29, 29, 7, 5, 62, 8, 29, 29, 29, 5, 73, 11, 29, 69, 7, 45, 47, 8, 35, 114, 72, 36, 47, 11, 35, 69, 69, 7, 62, 11, 8, 58, 13, 13, 13, 13, 125, 7, 13, 13, 8, 13, 125, 72, 13, 13, 11, 13, 59, 58, 36, 47, 47, 46, 69, 7, 45, 47, 8, 46, 114, 72, 36, 47, 11, 46, 59, 7, 58, 62, 8, 59, 59, 59, 58, 73, 11, 50, 69, 69, 7, 62, 11, 8, 13, 9, 0, 36, 9, 36, 73, 58, 9, 9, 3, 0, 92, 36, 73, 58, 36, 7, 17, 37, 8, 26, 92, 72, 17, 73, 11, 26, 58, 12, 17, 59, 13, 26, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 58, 12, 58, 59, 13, 11, 9, 36, 58, 7, 3, 62, 8, 36, 36, 36, 3, 73, 11, 36, 36, 12, 3, 76, 13, 36, 9, 7, 9, 37, 8, 9, 9, 9, 9, 112, 11, 9, 9, 9, 9, 59, 13, 9, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 58, 12, 58, 59, 13, 11, 58, 36, 0, 46, 9, 50, 73, 46, 9, 9, 9, 46, 9, 4, 125, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 0, 12, 9, 50, 73, 9, 9, 9, 47, 9, 12, 12, 7, 12, 47, 8, 12, 12, 12, 12, 47, 11, 12, 9, 7, 9, 51, 8, 9, 9, 9, 9, 79, 11, 9, 50, 50, 7, 51, 11, 8, 12, 46, 50, 13, 4, 9, 7, 9, 51, 8, 9, 9, 9, 9, 117, 11, 9, 9, 9, 9, 47, 13, 9, 50, 50, 7, 51, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 50, 46, 125, 7, 115, 62, 8, 46, 125, 72, 36, 73, 11, 46, 0, 12, 9, 58, 36, 73, 9, 9, 3, 0, 29, 58, 36, 73, 29, 29, 29, 47, 34, 26, 29, 7, 29, 37, 8, 26, 29, 29, 29, 47, 11, 26, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 9, 12, 12, 12, 3, 0, 47, 9, 36, 73, 9, 9, 9, 47, 9, 6, 36, 7, 36, 37, 8, 6, 58, 58, 47, 47, 11, 6, 9, 7, 9, 37, 8, 9, 9, 9, 9, 79, 11, 9, 36, 36, 7, 37, 11, 8, 50, 12, 12, 7, 3, 62, 8, 12, 12, 12, 3, 73, 11, 12, 9, 9, 9, 106, 34, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 79, 11, 9, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 12, 36, 76, 13, 76, 125, 7, 58, 62, 8, 62, 125, 72, 58, 73, 11, 50, 0, 12, 9, 46, 62, 73, 9, 9, 5, 0, 29, 46, 62, 73, 29, 29, 17, 46, 35, 26, 29, 7, 17, 62, 8, 26, 29, 29, 17, 73, 11, 26, 68, 7, 46, 46, 8, 35, 125, 72, 36, 46, 11, 35, 68, 68, 7, 62, 11, 8, 9, 12, 12, 12, 5, 0, 46, 9, 62, 73, 9, 9, 9, 46, 9, 4, 68, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 9, 7, 9, 70, 8, 9, 9, 9, 9, 79, 11, 9, 68, 68, 7, 62, 11, 8, 46, 12, 12, 7, 5, 62, 8, 12, 12, 12, 5, 73, 11, 12, 9, 9, 9, 46, 35, 9, 9, 7, 9, 70, 8, 9, 9, 9, 9, 79, 11, 9, 68, 7, 46, 46, 8, 35, 125, 72, 36, 46, 11, 35, 68, 68, 7, 62, 11, 8, 12, 0, 5, 0, 5, 50, 17, 35, 17, 49, 17, 55, 5, 46, 5, 62, 5, 50, 50, 35, 105, 35, 50, 49, 5, 0, 5, 46, 9, 35, 50, 35, 105, 35, 5, 50, 5, 62, 5, 50, 9, 49, 9, 55, 50, 49, 5, 51, 5, 73, 5, 50, 5, 46, 5, 62, 5, 50, 9, 35, 9, 49, 9, 55, 50, 35, 105, 35, 50, 49, 76, 13, 50, 0, 7, 9, 36, 50, 68, 7, 7, 7, 0, 60, 36, 50, 68, 36, 36, 36, 67, 36, 26, 60, 50, 60, 50, 50, 26, 60, 12, 60, 67, 13, 26, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 9, 7, 7, 7, 7, 128, 36, 7, 7, 7, 7, 128, 50, 7, 7, 7, 7, 76, 13, 7, 9, 9, 9, 95, 36, 9, 9, 9, 9, 50, 50, 9, 9, 9, 9, 69, 13, 9, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 72, 7, 62, 11, 8, 125, 12, 7, 62, 13, 8, 125, 12, 72, 73, 13, 11], [9], [0, 9, 85, 9, 87, 9, 22, 9, 28, 9, 32, 29, 2, 29, 2, 29, 2, 29, 2, 0, 9, 32, 1, 32, 1, 32, 1, 22, 1, 28, 1, 46, 1, 87, 1, 22, 1, 28, 17, 14, 21, 14, 81, 14, 17, 20, 17, 27, 21, 20, 2, 81, 84, 21, 22, 81, 28, 29, 30, 21, 22, 92, 28, 29, 30, 21, 22, 21, 22, 29, 28], [0, 2, 81, 87, 21, 28, 31, 0, 36, 87, 21, 28, 31, 36, 18, 3, 85, 19, 16, 21, 7, 3, 22, 8, 16, 36, 28, 3, 28, 11, 16, 31, 12, 3, 32, 13, 16, 21, 7, 18, 22, 8, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11, 36, 2, 2, 2, 2, 0, 58, 81, 21, 28, 31, 58, 15, 5, 85, 16, 19, 21, 7, 5, 22, 8, 19, 58, 28, 5, 28, 11, 19, 31, 12, 5, 32, 13, 19, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11, 58, 2, 2, 2, 2, 0, 7, 36, 50, 28, 31, 7, 7, 7, 22, 16, 7, 7, 7, 7, 22, 19, 7, 7, 7, 7, 22, 11, 7, 7, 7, 7, 22, 13, 7, 36, 18, 15, 50, 19, 16, 36, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 31, 12, 28, 28, 13, 11, 7, 2, 2, 2, 2, 0, 28, 81, 87, 21, 31, 81, 15, 23, 28, 16, 28, 93, 18, 23, 28, 19, 28, 21, 7, 21, 22, 8, 22, 31, 12, 23, 28, 13, 28, 81, 18, 15, 85, 19, 16, 21, 7, 15, 22, 8, 16, 31, 12, 15, 32, 13, 16, 21, 7, 18, 22, 8, 19, 31, 12, 18, 32, 13, 19, 21, 12, 7, 22, 13, 8, 28, 2, 2, 2, 2, 0, 12, 46, 58, 21, 28, 12, 12, 12, 32, 16, 12, 12, 12, 12, 32, 19, 12, 12, 7, 12, 22, 8, 12, 12, 12, 12, 28, 11, 12, 58, 18, 15, 46, 19, 16, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 21, 7, 18, 22, 8, 19, 58, 28, 18, 28, 11, 19, 21, 21, 7, 22, 11, 8, 12, 2, 2, 2, 2, 81, 18, 15, 85, 19, 16, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 21, 7, 18, 22, 8, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11], [10]]
def rootCodes2 : List (List Nat) := [[2], [0, 99, 0, 46, 36, 46, 36, 46, 115, 46, 36, 82, 36, 82, 106, 36, 37, 84, 110, 46, 47, 36, 37, 82, 83, 46, 47, 36, 37, 36, 37, 46, 47, 0, 50, 58, 50, 58, 122, 58, 50, 58, 50, 89, 89, 108, 50, 51, 92, 118, 58, 59, 50, 51, 89, 90, 58, 59, 50, 51, 50, 51, 58, 59, 125, 99, 99, 99, 36, 23, 0, 28, 108, 96, 98, 46, 0, 58, 96, 89, 46, 58, 7, 5, 97, 8, 58, 58, 9, 5, 100, 10, 58, 46, 12, 5, 47, 13, 47, 89, 9, 7, 90, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 58, 28, 28, 28, 4, 125, 7, 28, 28, 8, 4, 99, 9, 28, 28, 10, 4, 99, 12, 28, 28, 13, 4, 96, 7, 35, 97, 8, 91, 98, 9, 35, 100, 10, 50, 46, 12, 35, 47, 13, 47, 96, 9, 7, 97, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 46, 28, 99, 58, 23, 0, 28, 106, 50, 98, 99, 0, 36, 36, 89, 92, 50, 7, 3, 51, 8, 36, 36, 9, 3, 100, 10, 36, 36, 12, 3, 101, 13, 36, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 89, 12, 9, 90, 13, 10, 36, 28, 28, 28, 6, 125, 7, 28, 28, 8, 6, 99, 9, 28, 28, 10, 6, 99, 12, 28, 28, 13, 6, 50, 7, 34, 51, 8, 46, 98, 9, 34, 100, 10, 46, 99, 12, 34, 101, 13, 82, 50, 9, 7, 51, 10, 8, 50, 12, 7, 51, 13, 8, 98, 12, 9, 104, 13, 10, 50, 28, 99, 7, 23, 0, 8, 37, 51, 62, 70, 125, 36, 8, 8, 8, 8, 125, 51, 8, 8, 8, 8, 99, 9, 8, 8, 8, 8, 99, 12, 8, 8, 8, 8, 37, 37, 36, 51, 50, 37, 37, 9, 36, 63, 10, 37, 37, 12, 36, 71, 13, 37, 62, 9, 49, 51, 10, 50, 70, 12, 49, 51, 13, 50, 62, 12, 9, 63, 13, 10, 8, 28, 0, 9, 84, 92, 62, 29, 9, 9, 1, 0, 46, 92, 62, 29, 92, 17, 41, 46, 46, 4, 64, 7, 41, 46, 8, 4, 29, 12, 29, 30, 13, 4, 64, 7, 17, 62, 8, 56, 29, 12, 17, 30, 13, 30, 29, 12, 7, 30, 13, 8, 46, 9, 9, 9, 1, 0, 50, 84, 50, 29, 92, 36, 17, 50, 14, 6, 64, 7, 17, 62, 8, 6, 29, 12, 17, 30, 13, 6, 50, 7, 34, 51, 8, 14, 29, 12, 29, 30, 13, 14, 29, 12, 7, 30, 13, 8, 50, 9, 9, 7, 1, 0, 8, 37, 51, 29, 64, 36, 8, 8, 8, 8, 64, 17, 8, 8, 8, 8, 29, 12, 8, 8, 8, 8, 37, 17, 36, 51, 50, 14, 29, 12, 29, 30, 13, 14, 29, 12, 17, 30, 13, 30, 8, 9, 9, 9, 1, 0, 13, 47, 59, 62, 29, 29, 13, 13, 13, 13, 29, 17, 13, 13, 13, 13, 29, 7, 13, 13, 8, 13, 59, 17, 36, 47, 47, 14, 64, 7, 41, 47, 8, 14, 59, 7, 17, 62, 8, 56, 13, 9, 92, 17, 36, 84, 50, 14, 64, 7, 41, 62, 8, 14, 29, 12, 29, 30, 13, 14, 64, 7, 17, 62, 8, 56, 29, 12, 17, 30, 13, 30, 29, 12, 7, 30, 13, 8, 9, 29, 0, 10, 110, 118, 61, 77, 99, 36, 10, 10, 10, 10, 99, 58, 10, 10, 10, 10, 99, 7, 10, 10, 8, 10, 125, 12, 10, 10, 10, 10, 110, 53, 36, 116, 50, 40, 61, 7, 39, 63, 8, 40, 77, 12, 36, 78, 13, 40, 61, 7, 53, 63, 8, 54, 77, 12, 53, 78, 13, 50, 61, 12, 7, 63, 13, 8, 10, 28, 125, 12, 23, 0, 13, 47, 59, 69, 76, 99, 36, 13, 13, 13, 13, 99, 58, 13, 13, 13, 13, 99, 7, 13, 13, 8, 13, 125, 9, 13, 13, 10, 13, 59, 58, 36, 47, 47, 46, 69, 7, 45, 47, 8, 46, 76, 9, 36, 47, 10, 46, 59, 7, 58, 71, 8, 59, 59, 9, 58, 78, 10, 50, 69, 9, 7, 71, 10, 8, 13, 28, 0, 36, 89, 36, 89, 58, 36, 23, 3, 0, 28, 36, 89, 58, 36, 7, 17, 28, 8, 28, 92, 9, 17, 28, 10, 28, 58, 12, 17, 28, 13, 28, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 28, 36, 58, 7, 3, 126, 8, 36, 36, 9, 3, 100, 10, 36, 36, 12, 3, 101, 13, 36, 36, 7, 17, 37, 8, 28, 92, 9, 17, 110, 10, 28, 58, 12, 17, 59, 13, 28, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 58, 36, 0, 46, 82, 50, 82, 46, 99, 23, 46, 46, 28, 4, 125, 7, 46, 46, 8, 4, 99, 9, 46, 46, 10, 4, 99, 12, 46, 50, 13, 4, 50, 7, 14, 51, 8, 28, 84, 9, 14, 116, 10, 28, 46, 12, 14, 47, 13, 28, 50, 9, 7, 51, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 50, 46, 125, 7, 115, 126, 8, 46, 99, 9, 36, 100, 10, 46, 99, 12, 36, 101, 13, 82, 125, 7, 58, 126, 8, 122, 99, 9, 58, 100, 10, 50, 99, 12, 89, 101, 13, 50, 99, 9, 7, 100, 10, 8, 99, 12, 7, 101, 13, 8, 125, 12, 9, 127, 13, 10], [125], [99], [0, 2, 81, 87, 21, 25, 31, 0, 36, 87, 21, 25, 31, 36, 18, 3, 85, 19, 16, 21, 7, 3, 22, 8, 16, 25, 9, 3, 85, 10, 16, 31, 12, 3, 32, 13, 16, 21, 7, 18, 22, 8, 19, 25, 9, 18, 87, 10, 19, 31, 12, 18, 32, 13, 19, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 36, 2, 2, 2, 2, 0, 58, 81, 21, 25, 31, 58, 15, 5, 85, 16, 19, 21, 7, 5, 22, 8, 19, 25, 9, 5, 87, 10, 19, 31, 12, 5, 32, 13, 19, 21, 7, 15, 22, 8, 16, 25, 9, 15, 85, 10, 16, 31, 12, 15, 32, 13, 16, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 58, 2, 2, 2, 2, 0, 7, 36, 50, 25, 31, 7, 7, 7, 22, 16, 7, 7, 7, 7, 22, 19, 7, 7, 7, 7, 22, 10, 7, 7, 7, 7, 22, 13, 7, 36, 18, 15, 50, 19, 16, 25, 9, 15, 61, 10, 16, 31, 12, 15, 32, 13, 16, 25, 9, 18, 50, 10, 19, 31, 12, 18, 32, 13, 19, 25, 12, 9, 32, 13, 10, 7, 2, 2, 2, 2, 0, 9, 81, 87, 21, 31, 9, 9, 9, 85, 16, 9, 9, 9, 9, 87, 19, 9, 9, 7, 9, 22, 8, 9, 9, 9, 9, 32, 13, 9, 81, 18, 15, 85, 19, 16, 21, 7, 15, 22, 8, 16, 31, 12, 15, 32, 13, 16, 21, 7, 18, 22, 8, 19, 31, 12, 18, 32, 13, 19, 21, 12, 7, 22, 13, 8, 9, 2, 2, 2, 2, 0, 12, 46, 58, 21, 25, 12, 12, 12, 32, 16, 12, 12, 12, 12, 32, 19, 12, 12, 7, 12, 22, 8, 12, 12, 9, 12, 32, 10, 12, 58, 18, 15, 46, 19, 16, 21, 7, 15, 22, 8, 16, 25, 9, 15, 46, 10, 16, 21, 7, 18, 22, 8, 19, 25, 9, 18, 77, 10, 19, 21, 9, 7, 22, 10, 8, 12, 2, 2, 2, 2, 81, 18, 15, 85, 19, 16, 21, 7, 15, 22, 8, 16, 25, 9, 15, 85, 10, 16, 31, 12, 15, 32, 13, 16, 21, 7, 18, 22, 8, 19, 25, 9, 18, 87, 10, 19, 31, 12, 18, 32, 13, 19, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10], [11], [2], [0, 12, 46, 58, 68, 77, 79, 12, 12, 12, 0, 32, 58, 68, 77, 79, 58, 58, 32, 32, 32, 4, 68, 7, 32, 32, 8, 4, 0, 9, 58, 62, 73, 9, 9, 9, 116, 50, 9, 9, 7, 9, 70, 8, 9, 9, 9, 9, 79, 11, 9, 58, 7, 35, 62, 8, 58, 58, 58, 35, 73, 11, 50, 68, 68, 7, 62, 11, 8, 9, 32, 32, 10, 4, 0, 104, 58, 68, 77, 58, 35, 44, 104, 50, 43, 68, 7, 44, 70, 8, 43, 102, 9, 44, 77, 10, 43, 58, 7, 35, 70, 8, 58, 58, 9, 35, 77, 10, 50, 68, 9, 7, 70, 10, 8, 79, 32, 32, 11, 4, 58, 7, 35, 70, 8, 58, 58, 9, 35, 77, 10, 50, 58, 58, 35, 79, 11, 50, 68, 9, 7, 70, 10, 8, 68, 68, 7, 70, 11, 8, 102, 79, 9, 77, 11, 10, 46, 12, 12, 12, 12, 0, 32, 46, 50, 77, 79, 58, 36, 32, 32, 32, 6, 58, 7, 32, 32, 8, 6, 58, 9, 32, 32, 10, 6, 58, 58, 32, 32, 11, 6, 50, 7, 34, 46, 8, 46, 102, 9, 34, 46, 10, 46, 106, 79, 34, 46, 11, 46, 50, 9, 7, 51, 10, 8, 50, 50, 7, 51, 11, 8, 102, 79, 9, 77, 11, 10, 50, 12, 12, 7, 12, 0, 8, 37, 51, 62, 67, 68, 36, 8, 8, 8, 8, 58, 51, 8, 8, 8, 8, 68, 9, 8, 8, 8, 8, 68, 67, 8, 8, 8, 8, 37, 37, 36, 46, 46, 37, 37, 9, 36, 46, 10, 37, 37, 37, 36, 46, 11, 37, 58, 9, 49, 51, 10, 50, 58, 58, 49, 51, 11, 50, 62, 62, 9, 63, 11, 10, 8, 12, 12, 9, 12, 0, 10, 46, 58, 61, 79, 0, 23, 58, 36, 79, 23, 23, 3, 86, 50, 23, 23, 7, 3, 63, 8, 23, 23, 23, 3, 79, 11, 23, 36, 7, 36, 37, 8, 34, 58, 58, 53, 79, 11, 34, 36, 36, 7, 37, 11, 8, 36, 10, 10, 10, 10, 58, 58, 10, 10, 10, 10, 68, 7, 10, 10, 8, 10, 0, 23, 46, 58, 61, 23, 23, 23, 46, 40, 23, 23, 23, 23, 104, 50, 23, 23, 7, 23, 63, 8, 23, 58, 53, 36, 46, 46, 40, 61, 7, 39, 46, 8, 40, 58, 7, 53, 63, 8, 54, 79, 10, 10, 10, 10, 58, 53, 36, 46, 46, 40, 61, 7, 39, 46, 8, 40, 110, 74, 36, 46, 11, 40, 58, 7, 53, 63, 8, 54, 58, 58, 53, 79, 11, 50, 61, 61, 7, 63, 11, 8, 10, 12, 12, 12, 12, 0, 11, 46, 58, 65, 73, 0, 36, 58, 36, 73, 36, 36, 3, 86, 50, 36, 65, 7, 3, 67, 8, 36, 36, 9, 3, 77, 10, 36, 36, 7, 36, 37, 8, 34, 58, 9, 55, 77, 10, 34, 36, 9, 7, 37, 10, 8, 36, 11, 11, 11, 11, 58, 58, 11, 11, 11, 11, 68, 7, 11, 11, 8, 11, 0, 9, 46, 58, 62, 9, 9, 9, 46, 43, 9, 9, 9, 9, 119, 50, 9, 9, 7, 9, 67, 8, 9, 58, 55, 36, 46, 46, 43, 65, 7, 42, 46, 8, 43, 58, 7, 55, 62, 8, 57, 9, 11, 11, 10, 11, 58, 55, 36, 46, 46, 43, 65, 7, 42, 46, 8, 43, 73, 9, 36, 46, 10, 43, 58, 7, 55, 67, 8, 57, 58, 9, 55, 77, 10, 50, 65, 9, 7, 67, 10, 8, 11, 12, 58, 58, 36, 46, 46, 46, 68, 7, 46, 46, 8, 46, 0, 9, 12, 58, 36, 73, 9, 9, 3, 0, 23, 58, 36, 73, 23, 23, 23, 32, 32, 23, 23, 7, 23, 32, 8, 23, 23, 23, 23, 32, 11, 23, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 12, 9, 9, 9, 3, 116, 50, 9, 9, 7, 3, 70, 8, 9, 9, 9, 3, 79, 11, 9, 12, 12, 12, 102, 34, 12, 12, 7, 12, 37, 8, 12, 12, 12, 12, 73, 11, 12, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 9, 36, 46, 10, 46, 0, 36, 12, 58, 36, 77, 12, 12, 3, 0, 32, 58, 36, 77, 58, 58, 32, 32, 32, 32, 36, 7, 32, 32, 8, 32, 107, 9, 32, 32, 10, 32, 36, 7, 36, 37, 8, 34, 58, 9, 58, 77, 10, 34, 36, 9, 7, 37, 10, 8, 12, 36, 36, 36, 3, 117, 50, 36, 68, 7, 3, 70, 8, 36, 36, 9, 3, 77, 10, 36, 12, 12, 12, 106, 34, 12, 12, 7, 12, 37, 8, 12, 12, 9, 12, 110, 10, 12, 36, 7, 36, 37, 8, 34, 58, 9, 58, 77, 10, 34, 36, 9, 7, 37, 10, 8, 79, 36, 46, 11, 46, 58, 7, 58, 70, 8, 58, 58, 9, 58, 77, 10, 50, 58, 58, 58, 79, 11, 50, 68, 9, 7, 70, 10, 8, 68, 68, 7, 70, 11, 8, 0, 9, 12, 46, 58, 62, 9, 9, 9, 0, 23, 46, 58, 62, 23, 23, 23, 32, 32, 23, 23, 23, 23, 32, 32, 23, 23, 7, 23, 32, 8, 23, 58, 58, 36, 46, 46, 46, 68, 7, 46, 46, 8, 46, 58, 7, 58, 62, 8, 58, 12, 9, 9, 9, 9, 46, 46, 9, 9, 9, 9, 120, 50, 9, 9, 7, 9, 70, 8, 9, 12, 12, 12, 102, 46, 12, 12, 12, 12, 102, 50, 12, 12, 7, 12, 62, 8, 12, 58, 58, 36, 46, 46, 46, 68, 7, 46, 46, 8, 46, 58, 7, 58, 62, 8, 58, 79, 9, 77, 11, 10], [12], [0, 12, 32, 12, 32, 12, 22, 12, 32, 12, 28, 23, 2, 23, 2, 23, 2, 0, 9, 32, 1, 46, 1, 87, 1, 22, 1, 28, 1, 32, 1, 32, 1, 22, 1, 28, 17, 14, 21, 14, 81, 14, 17, 20, 17, 27, 21, 20, 2, 23, 2, 58, 46, 21, 22, 23, 24, 81, 28, 21, 22, 23, 24, 58, 28, 21, 22, 21, 22, 23, 24], [0, 2, 47, 59, 21, 25, 28, 0, 36, 59, 21, 25, 28, 36, 18, 3, 47, 19, 16, 21, 7, 3, 22, 8, 16, 25, 9, 3, 47, 10, 16, 36, 28, 3, 28, 11, 16, 21, 7, 18, 22, 8, 19, 25, 9, 18, 78, 10, 19, 59, 28, 18, 28, 11, 19, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 25, 25, 9, 28, 11, 10, 36, 2, 2, 2, 2, 0, 58, 47, 21, 25, 28, 58, 15, 5, 47, 16, 19, 21, 7, 5, 22, 8, 19, 25, 9, 5, 78, 10, 19, 58, 28, 5, 28, 11, 19, 21, 7, 15, 22, 8, 16, 25, 9, 15, 47, 10, 16, 81, 28, 15, 28, 11, 16, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 25, 25, 9, 28, 11, 10, 58, 2, 2, 2, 2, 0, 7, 36, 50, 25, 28, 7, 7, 7, 22, 16, 7, 7, 7, 7, 22, 19, 7, 7, 7, 7, 22, 10, 7, 7, 7, 7, 22, 11, 7, 36, 18, 15, 47, 19, 16, 25, 9, 15, 47, 10, 16, 36, 28, 15, 28, 11, 16, 25, 9, 18, 50, 10, 19, 59, 28, 18, 28, 11, 19, 25, 25, 9, 28, 11, 10, 7, 2, 2, 2, 2, 0, 9, 47, 59, 21, 28, 9, 9, 9, 47, 16, 9, 9, 9, 9, 78, 19, 9, 9, 7, 9, 22, 8, 9, 9, 9, 9, 28, 11, 9, 59, 18, 15, 47, 19, 16, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 21, 7, 18, 22, 8, 19, 59, 28, 18, 28, 11, 19, 21, 21, 7, 22, 11, 8, 9, 2, 2, 2, 2, 0, 28, 47, 59, 21, 25, 81, 15, 28, 28, 16, 28, 59, 18, 28, 28, 19, 28, 21, 7, 21, 22, 8, 22, 25, 9, 25, 28, 10, 28, 59, 18, 15, 47, 19, 16, 21, 7, 15, 22, 8, 16, 25, 9, 15, 47, 10, 16, 21, 7, 18, 22, 8, 19, 25, 9, 18, 78, 10, 19, 21, 9, 7, 22, 10, 8, 28, 2, 2, 2, 2, 59, 18, 15, 47, 19, 16, 21, 7, 15, 22, 8, 16, 25, 9, 15, 47, 10, 16, 81, 28, 15, 28, 11, 16, 21, 7, 18, 22, 8, 19, 25, 9, 18, 78, 10, 19, 59, 28, 18, 28, 11, 19, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 25, 25, 9, 28, 11, 10], [13], [2], [0, 36, 81, 36, 110, 112, 58, 36, 36, 3, 0, 2, 21, 25, 28, 31, 36, 7, 2, 2, 2, 2, 0, 9, 21, 28, 31, 9, 7, 9, 22, 8, 9, 9, 9, 9, 28, 11, 9, 9, 9, 9, 32, 13, 9, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11, 9, 2, 2, 2, 2, 0, 28, 21, 25, 31, 21, 7, 17, 22, 8, 22, 25, 9, 17, 28, 10, 28, 31, 12, 17, 28, 13, 28, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 28, 2, 2, 2, 2, 58, 12, 2, 2, 2, 2, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 2, 36, 58, 7, 3, 0, 8, 22, 62, 67, 58, 36, 22, 8, 8, 2, 8, 36, 9, 8, 8, 8, 8, 36, 36, 8, 8, 8, 8, 36, 12, 8, 8, 8, 8, 62, 9, 22, 22, 10, 2, 126, 66, 22, 22, 11, 2, 58, 12, 22, 22, 13, 2, 62, 62, 9, 63, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11, 8, 36, 36, 9, 3, 0, 10, 81, 36, 112, 58, 0, 92, 36, 112, 58, 36, 7, 17, 37, 8, 26, 92, 74, 17, 95, 11, 26, 58, 12, 17, 59, 13, 26, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 58, 12, 58, 59, 13, 11, 81, 10, 10, 2, 10, 36, 7, 10, 10, 8, 10, 0, 89, 81, 36, 58, 100, 24, 38, 81, 2, 75, 36, 7, 36, 37, 8, 37, 58, 12, 38, 59, 13, 59, 36, 7, 24, 37, 8, 2, 58, 12, 24, 59, 13, 2, 36, 12, 7, 37, 13, 8, 111, 10, 10, 10, 10, 58, 12, 10, 10, 10, 10, 36, 7, 24, 37, 8, 2, 100, 74, 24, 81, 11, 2, 58, 12, 24, 59, 13, 2, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 58, 12, 58, 59, 13, 11, 10, 36, 36, 36, 3, 0, 11, 28, 36, 73, 58, 0, 28, 36, 73, 58, 36, 7, 17, 28, 8, 28, 73, 9, 17, 28, 10, 28, 58, 12, 17, 28, 13, 28, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 28, 11, 11, 2, 11, 36, 7, 11, 11, 8, 11, 0, 9, 25, 36, 58, 9, 9, 9, 28, 2, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 59, 13, 9, 36, 7, 23, 25, 8, 2, 58, 12, 23, 25, 13, 2, 36, 12, 7, 37, 13, 8, 9, 11, 11, 10, 11, 58, 12, 11, 11, 11, 11, 36, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 58, 12, 28, 28, 13, 2, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 11, 36, 36, 12, 3, 0, 13, 32, 36, 76, 80, 58, 32, 13, 13, 2, 13, 36, 7, 13, 13, 8, 13, 58, 9, 13, 13, 10, 13, 58, 58, 13, 13, 11, 13, 36, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 101, 80, 30, 32, 11, 2, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 76, 76, 9, 78, 11, 10, 13, 36, 36, 7, 36, 37, 8, 2, 0, 9, 36, 36, 73, 58, 9, 3, 9, 0, 92, 36, 73, 58, 36, 7, 17, 37, 8, 26, 92, 72, 17, 73, 11, 26, 58, 12, 17, 59, 13, 26, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 58, 12, 58, 59, 13, 11, 36, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 112, 11, 9, 9, 9, 9, 59, 13, 9, 58, 7, 3, 62, 8, 36, 36, 36, 3, 73, 11, 36, 36, 12, 3, 76, 13, 36, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 58, 12, 58, 59, 13, 11, 9, 81, 81, 10, 2, 0, 89, 36, 36, 89, 58, 36, 3, 23, 0, 28, 36, 89, 58, 36, 7, 17, 28, 8, 28, 92, 9, 17, 28, 10, 28, 58, 12, 17, 28, 13, 28, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 36, 28, 36, 7, 17, 37, 8, 28, 92, 9, 17, 110, 10, 28, 58, 12, 17, 59, 13, 28, 58, 7, 3, 126, 8, 36, 36, 9, 3, 100, 10, 36, 36, 12, 3, 101, 13, 36, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 111, 81, 81, 11, 2, 58, 12, 58, 59, 13, 2, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 0, 9, 36, 25, 36, 58, 9, 3, 9, 0, 89, 25, 36, 58, 99, 23, 38, 25, 2, 25, 36, 7, 36, 37, 8, 37, 58, 12, 38, 59, 13, 59, 36, 7, 23, 25, 8, 2, 58, 12, 23, 25, 13, 2, 36, 12, 7, 37, 13, 8, 36, 9, 9, 9, 9, 81, 2, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 59, 13, 9, 36, 23, 3, 25, 2, 25, 58, 7, 3, 62, 8, 36, 36, 12, 3, 76, 13, 36, 36, 7, 23, 25, 8, 2, 58, 12, 23, 25, 13, 2, 36, 12, 7, 37, 13, 8, 111, 9, 110, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11], [58]]
def rootCodes3 : List (List Nat) := [[36], [0, 46, 85, 50, 116, 117, 46, 0, 85, 50, 99, 117, 46, 50, 7, 23, 51, 8, 16, 0, 9, 50, 73, 29, 9, 7, 1, 51, 8, 9, 9, 9, 1, 117, 11, 9, 9, 9, 1, 47, 13, 9, 50, 50, 7, 51, 11, 8, 29, 12, 7, 30, 13, 8, 29, 12, 29, 30, 13, 11, 9, 29, 85, 10, 16, 99, 99, 23, 85, 11, 16, 46, 12, 23, 47, 13, 16, 50, 9, 7, 51, 10, 8, 50, 50, 7, 51, 11, 8, 46, 12, 7, 47, 13, 8, 99, 99, 9, 100, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 85, 46, 46, 2, 4, 0, 7, 21, 61, 65, 46, 7, 7, 7, 51, 2, 7, 7, 7, 7, 51, 10, 7, 7, 7, 7, 51, 11, 7, 7, 7, 7, 47, 13, 7, 125, 9, 21, 21, 10, 2, 125, 64, 21, 21, 11, 2, 46, 12, 21, 21, 13, 2, 0, 9, 7, 21, 46, 7, 7, 7, 51, 7, 9, 9, 9, 9, 21, 2, 9, 9, 9, 9, 47, 13, 9, 7, 7, 7, 25, 2, 7, 7, 7, 7, 47, 13, 7, 46, 12, 21, 21, 13, 2, 64, 9, 61, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 7, 46, 46, 8, 4, 0, 9, 25, 50, 73, 46, 9, 9, 9, 85, 2, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 116, 11, 9, 9, 9, 9, 47, 13, 9, 50, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 46, 12, 23, 25, 13, 2, 50, 50, 7, 51, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 9, 46, 46, 10, 4, 0, 117, 85, 50, 116, 46, 125, 82, 64, 85, 2, 43, 50, 7, 50, 51, 8, 43, 0, 9, 25, 50, 46, 9, 9, 9, 85, 2, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 47, 13, 9, 50, 7, 23, 25, 8, 2, 46, 12, 23, 25, 13, 2, 46, 12, 7, 47, 13, 8, 9, 64, 116, 10, 43, 46, 12, 46, 47, 13, 43, 50, 7, 50, 51, 8, 2, 125, 9, 84, 85, 10, 2, 46, 12, 46, 47, 13, 2, 50, 9, 7, 51, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 117, 46, 46, 11, 4, 0, 12, 31, 50, 77, 79, 12, 12, 12, 47, 2, 12, 12, 7, 12, 47, 8, 12, 12, 9, 12, 47, 10, 12, 12, 12, 12, 47, 11, 12, 50, 7, 29, 31, 8, 2, 0, 9, 12, 50, 73, 9, 9, 9, 47, 12, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 79, 11, 9, 12, 7, 12, 47, 8, 12, 12, 12, 12, 47, 11, 12, 50, 50, 7, 51, 11, 8, 9, 29, 31, 10, 2, 99, 79, 29, 31, 11, 2, 50, 9, 7, 51, 10, 8, 50, 50, 7, 51, 11, 8, 99, 79, 9, 77, 11, 10, 12, 46, 50, 13, 4, 50, 7, 50, 51, 8, 2, 0, 9, 46, 50, 73, 46, 9, 9, 9, 46, 4, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 117, 11, 9, 9, 9, 9, 47, 13, 9, 125, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 0, 12, 9, 50, 73, 9, 9, 9, 47, 9, 12, 12, 7, 12, 47, 8, 12, 12, 12, 12, 47, 11, 12, 9, 7, 9, 51, 8, 9, 9, 9, 9, 79, 11, 9, 50, 50, 7, 51, 11, 8, 12, 46, 50, 13, 4, 50, 50, 7, 51, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 9, 84, 85, 10, 2, 0, 82, 46, 50, 82, 46, 99, 46, 23, 46, 4, 28, 50, 7, 14, 51, 8, 28, 84, 9, 14, 116, 10, 28, 46, 12, 14, 47, 13, 28, 125, 7, 46, 46, 8, 4, 99, 9, 46, 46, 10, 4, 99, 12, 46, 50, 13, 4, 50, 9, 7, 51, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 117, 82, 85, 11, 2, 46, 12, 46, 47, 13, 2, 50, 9, 7, 51, 10, 8, 50, 50, 7, 51, 11, 8, 46, 12, 7, 47, 13, 8, 0, 9, 46, 25, 50, 46, 9, 9, 9, 46, 4, 9, 9, 9, 9, 85, 2, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 47, 13, 9, 99, 23, 46, 25, 2, 4, 0, 7, 9, 21, 46, 7, 7, 7, 51, 9, 7, 7, 7, 7, 25, 2, 7, 7, 7, 7, 47, 13, 7, 9, 9, 9, 21, 2, 9, 9, 9, 9, 47, 13, 9, 46, 12, 21, 21, 13, 2, 7, 46, 46, 8, 4, 99, 12, 46, 50, 13, 4, 50, 7, 23, 25, 8, 2, 46, 12, 23, 25, 13, 2, 46, 12, 7, 47, 13, 8, 117, 9, 116, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11], [50], [46], [0, 7, 21, 50, 61, 65, 68, 7, 7, 3, 0, 2, 50, 25, 28, 31, 0, 58, 25, 28, 31, 25, 9, 5, 61, 10, 19, 58, 28, 5, 28, 11, 19, 31, 12, 5, 32, 13, 19, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 50, 2, 2, 2, 2, 125, 9, 2, 2, 2, 2, 125, 28, 2, 2, 2, 2, 68, 12, 2, 2, 2, 2, 25, 9, 18, 50, 10, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 2, 7, 7, 7, 3, 0, 50, 21, 61, 65, 68, 0, 87, 61, 65, 68, 107, 9, 29, 61, 10, 19, 99, 64, 23, 65, 11, 19, 68, 12, 23, 69, 13, 19, 99, 64, 9, 61, 11, 10, 68, 12, 9, 61, 13, 10, 68, 12, 64, 65, 13, 11, 21, 50, 21, 2, 6, 125, 9, 50, 50, 10, 6, 125, 64, 50, 50, 11, 6, 68, 12, 50, 50, 13, 6, 125, 9, 21, 21, 10, 2, 125, 64, 21, 21, 11, 2, 68, 12, 21, 21, 13, 2, 0, 9, 50, 21, 68, 9, 9, 9, 50, 6, 9, 9, 9, 9, 21, 2, 9, 9, 9, 9, 69, 13, 9, 99, 21, 50, 21, 2, 6, 68, 12, 50, 50, 13, 6, 68, 12, 21, 21, 13, 2, 64, 9, 61, 11, 10, 68, 12, 9, 61, 13, 10, 68, 12, 64, 65, 13, 11, 50, 7, 7, 7, 3, 0, 10, 21, 50, 65, 68, 125, 21, 10, 10, 2, 10, 125, 50, 10, 10, 10, 10, 0, 60, 21, 50, 68, 60, 21, 38, 21, 2, 21, 60, 50, 38, 50, 34, 50, 60, 12, 38, 69, 13, 60, 100, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 68, 12, 50, 50, 13, 34, 64, 10, 10, 10, 10, 68, 12, 10, 10, 10, 10, 100, 50, 21, 21, 21, 2, 100, 64, 21, 21, 11, 2, 68, 12, 21, 21, 13, 2, 123, 64, 50, 50, 11, 34, 68, 12, 50, 50, 13, 34, 68, 12, 64, 65, 13, 11, 10, 7, 7, 7, 3, 0, 11, 21, 50, 61, 68, 125, 21, 11, 11, 2, 11, 125, 50, 11, 11, 11, 11, 0, 9, 21, 50, 68, 9, 9, 9, 21, 2, 9, 9, 9, 9, 50, 34, 9, 9, 9, 9, 69, 13, 9, 99, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 68, 12, 50, 50, 13, 34, 9, 11, 11, 10, 11, 68, 12, 11, 11, 11, 11, 124, 50, 21, 21, 21, 2, 73, 9, 21, 21, 10, 2, 68, 12, 21, 21, 13, 2, 73, 9, 50, 50, 10, 34, 68, 12, 50, 50, 13, 34, 68, 12, 9, 61, 13, 10, 11, 7, 7, 7, 3, 0, 13, 21, 50, 61, 65, 68, 21, 13, 13, 2, 13, 68, 50, 13, 13, 13, 13, 68, 9, 13, 13, 10, 13, 68, 64, 13, 13, 11, 13, 59, 50, 21, 21, 21, 2, 76, 9, 21, 21, 10, 2, 101, 64, 21, 21, 11, 2, 59, 9, 50, 50, 10, 34, 59, 59, 50, 50, 11, 34, 76, 64, 9, 61, 11, 10, 13, 7, 0, 58, 7, 61, 65, 58, 7, 3, 5, 0, 87, 61, 65, 58, 99, 9, 33, 61, 10, 19, 107, 64, 33, 65, 11, 19, 58, 12, 33, 59, 13, 19, 99, 64, 9, 61, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11, 7, 58, 58, 9, 5, 61, 10, 58, 58, 58, 5, 65, 11, 58, 68, 12, 5, 69, 13, 58, 7, 7, 3, 100, 10, 7, 7, 7, 3, 124, 11, 7, 7, 7, 3, 59, 13, 7, 99, 64, 9, 61, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11, 50, 21, 21, 21, 2, 125, 9, 21, 21, 10, 2, 125, 64, 21, 21, 11, 2, 68, 12, 21, 21, 13, 2, 125, 9, 50, 50, 10, 34, 125, 64, 50, 50, 11, 34, 68, 12, 50, 50, 13, 34, 0, 9, 7, 21, 50, 68, 7, 3, 7, 0, 60, 21, 50, 68, 60, 21, 38, 21, 2, 21, 60, 50, 38, 50, 34, 50, 60, 12, 38, 69, 13, 60, 99, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 68, 12, 50, 50, 13, 34, 7, 9, 9, 9, 9, 21, 2, 9, 9, 9, 9, 50, 34, 9, 9, 9, 9, 69, 13, 9, 7, 7, 3, 25, 2, 7, 7, 7, 3, 0, 50, 9, 21, 68, 9, 9, 9, 50, 9, 6, 99, 21, 50, 21, 2, 6, 68, 12, 50, 50, 13, 6, 9, 9, 9, 21, 2, 9, 9, 9, 9, 69, 13, 9, 68, 12, 21, 21, 13, 2, 50, 7, 7, 7, 3, 76, 13, 7, 99, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 68, 12, 50, 50, 13, 34, 64, 9, 61, 11, 10, 68, 12, 9, 61, 13, 10, 68, 12, 64, 65, 13, 11], [7], [0, 3, 85, 3, 0, 3, 46, 107, 15, 107, 34, 107, 34, 46, 34, 3, 21, 3, 46, 3, 46, 3, 69, 115, 15, 115, 15, 46, 15, 0, 9, 34, 3, 46, 9, 15, 9, 45, 3, 46, 82, 15, 46, 34, 3, 21, 3, 69, 46, 15, 39, 46, 39, 46, 42, 3, 116, 3, 117, 3, 47, 3, 21, 3, 46, 3, 46, 3, 46, 3, 69, 107, 15, 115, 15, 115, 15, 46, 15, 107, 34, 107, 34, 46, 34, 0, 3, 0, 3, 46, 38, 15, 38, 34, 38, 45, 3, 21, 3, 46, 3, 69, 82, 15, 46, 15, 46, 34, 3, 46, 9, 15, 9, 34, 9, 45, 3, 25, 3, 0, 9, 34, 3, 46, 82, 15, 46, 34, 3, 46, 9, 15, 9, 45, 3, 21, 3, 69, 46, 15, 3, 47, 3, 21, 3, 46, 3, 69, 82, 15, 46, 15, 46, 34, 39, 46, 39, 46, 42], [0, 8, 22, 51, 62, 67, 46, 0, 22, 51, 62, 67, 46, 36, 35, 22, 22, 22, 16, 36, 9, 22, 22, 10, 16, 36, 36, 22, 22, 11, 16, 36, 12, 22, 22, 13, 16, 62, 9, 35, 51, 10, 50, 108, 66, 35, 51, 11, 50, 46, 12, 35, 47, 13, 47, 62, 62, 9, 63, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 22, 8, 8, 2, 4, 0, 36, 22, 62, 67, 46, 36, 22, 5, 22, 2, 22, 36, 9, 5, 51, 10, 36, 36, 36, 5, 51, 11, 36, 36, 12, 5, 47, 13, 36, 62, 9, 22, 22, 10, 2, 126, 66, 22, 22, 11, 2, 46, 12, 22, 22, 13, 2, 62, 62, 9, 63, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 51, 8, 8, 8, 4, 0, 9, 22, 51, 67, 46, 9, 9, 9, 22, 2, 9, 9, 9, 9, 51, 50, 9, 9, 9, 9, 63, 11, 9, 9, 9, 9, 47, 13, 9, 99, 35, 22, 22, 22, 2, 99, 66, 22, 22, 11, 2, 46, 12, 22, 22, 13, 2, 108, 66, 35, 51, 11, 50, 46, 12, 35, 47, 13, 47, 46, 12, 46, 47, 13, 11, 9, 8, 8, 8, 4, 0, 36, 22, 51, 62, 46, 36, 22, 36, 22, 2, 22, 36, 35, 36, 51, 50, 36, 36, 9, 36, 63, 10, 36, 36, 12, 36, 47, 13, 36, 108, 35, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 46, 12, 22, 22, 13, 2, 62, 9, 35, 51, 10, 50, 46, 12, 35, 47, 13, 47, 46, 12, 9, 47, 13, 10, 67, 8, 8, 8, 4, 0, 12, 22, 51, 62, 67, 12, 12, 12, 22, 2, 12, 12, 12, 12, 47, 47, 12, 12, 9, 12, 47, 10, 12, 12, 12, 12, 47, 11, 12, 58, 35, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 99, 66, 22, 22, 11, 2, 58, 9, 35, 51, 10, 50, 58, 58, 35, 51, 11, 50, 62, 62, 9, 63, 11, 10, 12, 8, 8, 8, 4, 108, 35, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 126, 66, 22, 22, 11, 2, 46, 12, 22, 22, 13, 2, 62, 9, 35, 51, 10, 50, 108, 66, 35, 51, 11, 50, 46, 12, 35, 47, 13, 47, 62, 62, 9, 63, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11], [8], [46], [0, 9, 25, 106, 36, 73, 76, 9, 9, 3, 0, 2, 87, 21, 28, 31, 99, 58, 2, 2, 2, 2, 36, 7, 2, 2, 2, 2, 99, 28, 2, 2, 2, 2, 0, 12, 58, 21, 28, 12, 12, 12, 32, 19, 12, 12, 7, 12, 22, 8, 12, 12, 12, 12, 28, 11, 12, 21, 7, 18, 22, 8, 19, 58, 28, 18, 28, 11, 19, 21, 21, 7, 22, 11, 8, 12, 2, 2, 2, 2, 21, 7, 18, 22, 8, 19, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11, 2, 9, 9, 9, 3, 0, 50, 25, 36, 73, 76, 99, 23, 50, 25, 2, 6, 36, 7, 36, 37, 8, 6, 125, 72, 50, 50, 11, 6, 99, 12, 50, 50, 13, 6, 36, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 116, 12, 23, 25, 13, 2, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 99, 12, 72, 73, 13, 11, 50, 9, 9, 7, 3, 0, 8, 22, 51, 67, 70, 36, 22, 8, 8, 2, 8, 36, 36, 8, 8, 8, 8, 36, 36, 8, 8, 8, 8, 36, 12, 8, 8, 8, 8, 99, 49, 22, 22, 22, 2, 99, 66, 22, 22, 11, 2, 70, 12, 22, 22, 13, 2, 121, 66, 49, 51, 11, 34, 70, 12, 49, 51, 13, 34, 70, 12, 66, 67, 13, 11, 8, 9, 9, 9, 3, 0, 11, 25, 106, 36, 76, 99, 23, 11, 11, 2, 11, 125, 58, 11, 11, 11, 11, 36, 7, 11, 11, 8, 11, 99, 12, 11, 11, 11, 11, 99, 55, 23, 25, 25, 2, 36, 7, 23, 25, 8, 2, 79, 12, 23, 25, 13, 2, 36, 7, 36, 37, 8, 34, 79, 12, 55, 76, 13, 34, 36, 12, 7, 37, 13, 8, 11, 9, 9, 9, 3, 0, 13, 25, 59, 36, 73, 0, 23, 59, 36, 73, 23, 23, 23, 32, 32, 23, 23, 7, 23, 32, 8, 23, 23, 23, 23, 32, 11, 23, 36, 7, 36, 37, 8, 34, 59, 59, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 23, 13, 13, 2, 13, 99, 58, 13, 13, 13, 13, 36, 7, 13, 13, 8, 13, 99, 72, 13, 13, 11, 13, 59, 58, 23, 25, 25, 2, 36, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 36, 7, 36, 37, 8, 34, 59, 59, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 13, 9, 99, 58, 23, 25, 25, 2, 36, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 0, 12, 9, 58, 36, 73, 9, 3, 9, 0, 23, 58, 36, 73, 23, 23, 23, 32, 32, 23, 23, 7, 23, 32, 8, 23, 23, 23, 23, 32, 11, 23, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 9, 12, 12, 12, 12, 102, 34, 12, 12, 7, 12, 37, 8, 12, 12, 12, 12, 73, 11, 12, 9, 9, 3, 116, 50, 9, 9, 7, 3, 70, 8, 9, 9, 9, 3, 79, 11, 9, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 12, 23, 25, 13, 2, 36, 7, 36, 37, 8, 34, 125, 72, 58, 73, 11, 34, 99, 12, 89, 76, 13, 34, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 99, 12, 72, 73, 13, 11], [9], [36], [0, 10, 85, 108, 61, 117, 46, 0, 85, 108, 61, 117, 46, 99, 35, 23, 85, 50, 16, 61, 7, 23, 63, 8, 16, 99, 74, 23, 85, 11, 16, 46, 12, 23, 47, 13, 16, 61, 7, 35, 63, 8, 54, 108, 74, 35, 117, 11, 50, 46, 12, 35, 47, 13, 47, 61, 61, 7, 63, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 85, 10, 10, 2, 4, 0, 58, 85, 61, 117, 46, 58, 24, 5, 85, 2, 54, 58, 7, 5, 63, 8, 54, 58, 58, 5, 117, 11, 54, 46, 12, 5, 47, 13, 47, 61, 7, 24, 63, 8, 2, 100, 74, 24, 85, 11, 2, 46, 12, 24, 47, 13, 2, 61, 61, 7, 63, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 58, 10, 10, 10, 4, 0, 7, 21, 50, 65, 46, 7, 7, 7, 63, 2, 7, 7, 7, 7, 63, 50, 7, 7, 7, 7, 63, 11, 7, 7, 7, 7, 47, 13, 7, 100, 35, 21, 21, 21, 2, 100, 64, 21, 21, 11, 2, 46, 12, 21, 21, 13, 2, 108, 64, 35, 50, 11, 50, 46, 12, 35, 47, 13, 47, 46, 12, 46, 47, 13, 11, 7, 10, 10, 8, 4, 0, 117, 85, 108, 61, 46, 100, 24, 64, 85, 2, 43, 108, 35, 64, 117, 50, 43, 61, 7, 61, 63, 8, 43, 46, 12, 46, 47, 13, 43, 100, 35, 24, 85, 50, 2, 61, 7, 24, 63, 8, 2, 46, 12, 24, 47, 13, 2, 61, 7, 35, 63, 8, 54, 46, 12, 35, 47, 13, 47, 46, 12, 7, 47, 13, 8, 117, 10, 10, 10, 4, 0, 12, 31, 58, 61, 79, 12, 12, 12, 47, 2, 12, 12, 12, 12, 47, 47, 12, 12, 7, 12, 47, 8, 12, 12, 12, 12, 47, 11, 12, 58, 35, 24, 31, 31, 2, 61, 7, 24, 31, 8, 2, 99, 74, 24, 31, 11, 2, 58, 7, 35, 63, 8, 54, 58, 58, 35, 79, 11, 50, 61, 61, 7, 63, 11, 8, 12, 10, 10, 10, 4, 100, 35, 24, 85, 50, 2, 61, 7, 24, 63, 8, 2, 100, 74, 24, 85, 11, 2, 46, 12, 24, 47, 13, 2, 61, 7, 35, 63, 8, 54, 108, 74, 35, 117, 11, 50, 46, 12, 35, 47, 13, 47, 61, 61, 7, 63, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11], [10]]
def rootCodes4 : List (List Nat) := [[46], [0, 36, 81, 106, 36, 110, 114, 36, 36, 3, 0, 2, 87, 21, 25, 31, 0, 58, 21, 25, 31, 21, 7, 5, 22, 8, 19, 25, 9, 5, 87, 10, 19, 31, 12, 5, 32, 13, 19, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 58, 2, 2, 2, 2, 36, 7, 2, 2, 2, 2, 125, 9, 2, 2, 2, 2, 0, 12, 58, 21, 25, 12, 12, 12, 32, 19, 12, 12, 7, 12, 22, 8, 12, 12, 9, 12, 32, 10, 12, 21, 7, 18, 22, 8, 19, 25, 9, 18, 77, 10, 19, 21, 9, 7, 22, 10, 8, 12, 2, 2, 2, 2, 21, 7, 18, 22, 8, 19, 25, 9, 18, 87, 10, 19, 31, 12, 18, 32, 13, 19, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 2, 36, 36, 36, 3, 0, 50, 81, 36, 110, 114, 0, 87, 36, 99, 99, 36, 7, 23, 37, 8, 19, 105, 9, 29, 87, 10, 19, 105, 12, 23, 87, 13, 19, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 107, 12, 9, 109, 13, 10, 81, 50, 50, 2, 6, 36, 7, 36, 37, 8, 6, 125, 9, 50, 50, 10, 6, 0, 12, 31, 36, 77, 12, 12, 12, 81, 2, 12, 12, 7, 12, 37, 8, 12, 12, 9, 12, 110, 10, 12, 36, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 36, 9, 7, 37, 10, 8, 12, 50, 50, 13, 6, 36, 7, 36, 37, 8, 2, 125, 9, 81, 81, 10, 2, 117, 12, 81, 81, 13, 2, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 117, 12, 9, 110, 13, 10, 50, 36, 0, 3, 15, 34, 39, 45, 3, 3, 3, 0, 2, 34, 25, 31, 107, 33, 2, 2, 2, 2, 72, 9, 2, 2, 2, 2, 68, 12, 2, 2, 2, 2, 25, 9, 18, 34, 10, 19, 31, 12, 18, 32, 13, 19, 25, 12, 9, 32, 13, 10, 2, 3, 3, 3, 3, 0, 34, 15, 39, 45, 107, 15, 33, 15, 2, 6, 72, 9, 33, 34, 10, 6, 68, 12, 33, 34, 13, 6, 72, 9, 15, 15, 10, 2, 68, 12, 15, 15, 13, 2, 68, 12, 9, 39, 13, 10, 34, 3, 3, 3, 3, 0, 10, 15, 34, 45, 72, 15, 10, 10, 2, 10, 72, 33, 10, 10, 10, 10, 68, 12, 10, 10, 10, 10, 100, 33, 15, 15, 15, 2, 68, 12, 15, 15, 13, 2, 68, 12, 33, 34, 13, 34, 10, 3, 3, 3, 3, 0, 13, 15, 34, 39, 68, 15, 13, 13, 2, 13, 68, 33, 13, 13, 13, 13, 68, 9, 13, 13, 10, 13, 59, 33, 15, 15, 15, 2, 72, 9, 15, 15, 10, 2, 59, 9, 33, 34, 10, 34, 13, 3, 107, 33, 15, 15, 15, 2, 72, 9, 15, 15, 10, 2, 68, 12, 15, 15, 13, 2, 72, 9, 33, 34, 10, 34, 68, 12, 33, 34, 13, 34, 68, 12, 9, 39, 13, 10, 7, 3, 0, 8, 22, 51, 62, 70, 36, 22, 8, 8, 2, 8, 36, 36, 8, 8, 8, 8, 36, 9, 8, 8, 8, 8, 36, 12, 8, 8, 8, 8, 121, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 70, 12, 22, 22, 13, 2, 62, 9, 49, 51, 10, 34, 70, 12, 49, 51, 13, 34, 62, 12, 9, 63, 13, 10, 8, 36, 36, 9, 3, 0, 10, 81, 106, 36, 77, 125, 81, 10, 10, 2, 10, 125, 58, 10, 10, 10, 10, 36, 7, 10, 10, 8, 10, 125, 12, 10, 10, 10, 10, 100, 53, 24, 81, 34, 2, 36, 7, 24, 37, 8, 2, 77, 12, 24, 78, 13, 2, 36, 7, 36, 37, 8, 34, 77, 12, 53, 78, 13, 34, 36, 12, 7, 37, 13, 8, 10, 36, 36, 12, 3, 0, 13, 32, 59, 36, 76, 0, 32, 59, 36, 76, 59, 58, 23, 32, 32, 32, 36, 7, 23, 32, 8, 32, 76, 9, 29, 32, 10, 32, 36, 7, 36, 37, 8, 34, 59, 9, 58, 78, 10, 34, 36, 9, 7, 37, 10, 8, 32, 13, 13, 2, 13, 0, 58, 32, 36, 76, 58, 30, 5, 32, 2, 32, 36, 7, 5, 37, 8, 37, 58, 9, 5, 78, 10, 58, 36, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 36, 9, 7, 37, 10, 8, 58, 13, 13, 13, 13, 36, 7, 13, 13, 8, 13, 125, 9, 13, 13, 10, 13, 59, 58, 30, 32, 32, 2, 36, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 36, 7, 36, 37, 8, 34, 59, 9, 58, 78, 10, 34, 36, 9, 7, 37, 10, 8, 13, 36, 0, 58, 36, 36, 99, 58, 36, 3, 5, 0, 87, 36, 99, 58, 36, 7, 33, 37, 8, 19, 99, 9, 33, 87, 10, 19, 58, 12, 33, 59, 13, 19, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 36, 58, 36, 7, 5, 37, 8, 37, 58, 9, 5, 110, 10, 58, 105, 12, 5, 114, 13, 58, 107, 7, 3, 121, 8, 36, 36, 9, 3, 100, 10, 36, 36, 12, 3, 59, 13, 36, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 58, 81, 81, 34, 2, 36, 7, 36, 37, 8, 2, 125, 9, 81, 81, 10, 2, 0, 12, 36, 58, 36, 77, 12, 3, 12, 0, 32, 58, 36, 77, 58, 58, 32, 32, 32, 32, 36, 7, 32, 32, 8, 32, 107, 9, 32, 32, 10, 32, 36, 7, 36, 37, 8, 34, 58, 9, 58, 77, 10, 34, 36, 9, 7, 37, 10, 8, 36, 12, 12, 12, 12, 106, 34, 12, 12, 7, 12, 37, 8, 12, 12, 9, 12, 110, 10, 12, 36, 36, 3, 117, 50, 36, 68, 7, 3, 70, 8, 36, 36, 9, 3, 77, 10, 36, 36, 7, 36, 37, 8, 34, 58, 9, 58, 77, 10, 34, 36, 9, 7, 37, 10, 8, 12, 81, 81, 13, 2, 36, 7, 36, 37, 8, 34, 125, 9, 58, 106, 10, 34, 0, 12, 36, 31, 36, 77, 12, 3, 5, 0, 105, 31, 36, 77, 99, 29, 33, 31, 2, 31, 36, 7, 33, 37, 8, 37, 99, 9, 33, 77, 10, 43, 36, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 36, 9, 7, 37, 10, 8, 36, 12, 12, 12, 5, 81, 2, 12, 12, 7, 5, 37, 8, 12, 12, 9, 5, 110, 10, 12, 36, 29, 3, 31, 2, 31, 68, 7, 3, 70, 8, 36, 36, 9, 3, 77, 10, 36, 36, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 36, 9, 7, 37, 10, 8, 12, 105, 106, 13, 34, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 125, 12, 9, 110, 13, 10], [125], [36], [0, 11, 28, 108, 65, 73, 46, 0, 28, 108, 65, 73, 46, 99, 35, 23, 28, 28, 16, 65, 7, 23, 28, 8, 16, 73, 9, 28, 28, 10, 16, 46, 12, 23, 28, 13, 16, 65, 7, 35, 67, 8, 57, 73, 9, 35, 100, 10, 50, 46, 12, 35, 47, 13, 47, 65, 9, 7, 67, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 28, 11, 11, 2, 4, 0, 58, 28, 65, 73, 46, 58, 28, 5, 28, 2, 28, 58, 7, 5, 67, 8, 57, 58, 9, 5, 116, 10, 57, 46, 12, 5, 47, 13, 47, 65, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 46, 12, 28, 28, 13, 2, 65, 9, 7, 67, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 58, 11, 11, 11, 4, 0, 7, 21, 50, 61, 46, 7, 7, 7, 28, 2, 7, 7, 7, 7, 67, 50, 7, 7, 7, 7, 67, 10, 7, 7, 7, 7, 47, 13, 7, 108, 35, 21, 21, 21, 2, 73, 9, 21, 21, 10, 2, 46, 12, 21, 21, 13, 2, 73, 9, 35, 50, 10, 50, 46, 12, 35, 47, 13, 47, 46, 12, 9, 47, 13, 10, 7, 11, 11, 8, 4, 0, 9, 25, 108, 62, 46, 9, 9, 9, 28, 2, 9, 9, 9, 9, 116, 50, 9, 9, 7, 9, 67, 8, 9, 9, 9, 9, 47, 13, 9, 99, 35, 23, 25, 25, 2, 65, 7, 23, 25, 8, 2, 46, 12, 23, 25, 13, 2, 65, 7, 35, 62, 8, 57, 46, 12, 35, 47, 13, 47, 46, 12, 7, 47, 13, 8, 9, 11, 11, 10, 4, 0, 12, 28, 58, 65, 73, 12, 12, 12, 28, 2, 12, 12, 12, 12, 47, 47, 12, 12, 7, 12, 47, 8, 12, 12, 9, 12, 47, 10, 12, 58, 35, 28, 28, 28, 2, 65, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 58, 7, 35, 67, 8, 57, 58, 9, 35, 77, 10, 50, 65, 9, 7, 67, 10, 8, 12, 11, 11, 11, 4, 108, 35, 28, 28, 28, 2, 65, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 46, 12, 28, 28, 13, 2, 65, 7, 35, 67, 8, 57, 73, 9, 35, 116, 10, 50, 46, 12, 35, 47, 13, 47, 65, 9, 7, 67, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10], [11], [46], [0, 12, 31, 58, 36, 77, 79, 12, 12, 3, 0, 2, 58, 21, 25, 28, 58, 58, 2, 2, 2, 2, 36, 7, 2, 2, 2, 2, 0, 9, 58, 21, 28, 9, 9, 9, 87, 19, 9, 9, 7, 9, 22, 8, 9, 9, 9, 9, 28, 11, 9, 21, 7, 18, 22, 8, 19, 58, 28, 18, 28, 11, 19, 21, 21, 7, 22, 11, 8, 9, 2, 2, 2, 2, 99, 28, 2, 2, 2, 2, 21, 7, 18, 22, 8, 19, 25, 9, 18, 77, 10, 19, 58, 28, 18, 28, 11, 19, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 25, 25, 9, 28, 11, 10, 2, 12, 12, 12, 3, 0, 47, 31, 36, 77, 79, 58, 29, 47, 31, 2, 6, 36, 7, 36, 37, 8, 6, 58, 9, 47, 47, 10, 6, 58, 58, 47, 47, 11, 6, 36, 7, 29, 31, 8, 2, 0, 9, 47, 36, 73, 9, 9, 9, 47, 6, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 79, 11, 9, 36, 7, 36, 37, 8, 6, 58, 58, 47, 47, 11, 6, 36, 36, 7, 37, 11, 8, 9, 29, 31, 10, 2, 99, 79, 29, 31, 11, 2, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 99, 79, 9, 77, 11, 10, 50, 12, 12, 7, 3, 0, 8, 22, 51, 62, 67, 36, 22, 8, 8, 2, 8, 36, 36, 8, 8, 8, 8, 36, 9, 8, 8, 8, 8, 36, 36, 8, 8, 8, 8, 58, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 99, 66, 22, 22, 11, 2, 58, 9, 49, 51, 10, 34, 58, 58, 49, 51, 11, 34, 62, 62, 9, 63, 11, 10, 8, 12, 12, 9, 3, 0, 10, 31, 58, 36, 79, 0, 29, 58, 36, 79, 29, 29, 23, 86, 34, 26, 29, 7, 23, 37, 8, 26, 29, 29, 23, 79, 11, 26, 36, 7, 36, 37, 8, 34, 58, 58, 53, 79, 11, 34, 36, 36, 7, 37, 11, 8, 29, 10, 10, 2, 10, 58, 58, 10, 10, 10, 10, 36, 7, 10, 10, 8, 10, 99, 79, 10, 10, 10, 10, 58, 53, 24, 31, 31, 2, 36, 7, 24, 31, 8, 2, 99, 74, 24, 31, 11, 2, 36, 7, 36, 37, 8, 34, 58, 58, 53, 79, 11, 34, 36, 36, 7, 37, 11, 8, 10, 12, 12, 12, 3, 0, 11, 28, 58, 36, 73, 99, 28, 11, 11, 2, 11, 58, 58, 11, 11, 11, 11, 36, 7, 11, 11, 8, 11, 99, 9, 11, 11, 10, 11, 58, 55, 28, 28, 28, 2, 36, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 36, 7, 36, 37, 8, 34, 58, 9, 55, 77, 10, 34, 36, 9, 7, 37, 10, 8, 11, 12, 58, 58, 29, 31, 31, 2, 36, 7, 29, 31, 8, 2, 0, 9, 12, 58, 36, 73, 9, 3, 9, 0, 29, 58, 36, 73, 29, 29, 29, 47, 34, 26, 29, 7, 29, 37, 8, 26, 29, 29, 29, 47, 11, 26, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 12, 9, 9, 9, 9, 106, 34, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 79, 11, 9, 12, 12, 3, 0, 47, 9, 36, 73, 9, 9, 9, 47, 9, 6, 36, 7, 36, 37, 8, 6, 58, 58, 47, 47, 11, 6, 9, 7, 9, 37, 8, 9, 9, 9, 9, 79, 11, 9, 36, 36, 7, 37, 11, 8, 50, 12, 12, 7, 3, 62, 8, 12, 12, 12, 3, 73, 11, 12, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 9, 29, 31, 10, 2, 99, 79, 29, 31, 11, 2, 36, 7, 36, 37, 8, 34, 58, 9, 58, 77, 10, 34, 58, 58, 58, 79, 11, 34, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 99, 79, 9, 77, 11, 10], [12], [36], [0, 13, 32, 59, 69, 76, 80, 0, 32, 59, 69, 76, 80, 59, 35, 23, 32, 32, 16, 69, 7, 23, 32, 8, 16, 76, 9, 29, 32, 10, 16, 99, 80, 23, 32, 11, 16, 59, 7, 35, 71, 8, 59, 59, 9, 35, 78, 10, 50, 59, 59, 35, 80, 11, 50, 69, 9, 7, 71, 10, 8, 69, 69, 7, 71, 11, 8, 76, 76, 9, 78, 11, 10, 32, 13, 13, 2, 4, 0, 58, 32, 69, 76, 80, 58, 30, 5, 32, 2, 32, 58, 7, 5, 71, 8, 58, 58, 9, 5, 78, 10, 58, 58, 58, 5, 80, 11, 58, 69, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 101, 80, 30, 32, 11, 2, 69, 9, 7, 71, 10, 8, 69, 69, 7, 71, 11, 8, 76, 76, 9, 78, 11, 10, 58, 13, 13, 13, 4, 0, 7, 21, 50, 61, 65, 7, 7, 7, 32, 2, 7, 7, 7, 7, 71, 50, 7, 7, 7, 7, 71, 10, 7, 7, 7, 7, 71, 11, 7, 59, 35, 21, 21, 21, 2, 76, 9, 21, 21, 10, 2, 101, 64, 21, 21, 11, 2, 59, 9, 35, 50, 10, 50, 59, 59, 35, 50, 11, 50, 76, 64, 9, 61, 11, 10, 7, 13, 13, 8, 4, 0, 9, 25, 59, 62, 73, 9, 9, 9, 32, 2, 9, 9, 9, 9, 78, 50, 9, 9, 7, 9, 71, 8, 9, 9, 9, 9, 78, 11, 9, 59, 35, 23, 25, 25, 2, 69, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 59, 7, 35, 62, 8, 59, 59, 59, 35, 73, 11, 50, 69, 69, 7, 62, 11, 8, 9, 13, 13, 10, 4, 0, 80, 32, 59, 69, 76, 101, 30, 64, 32, 2, 32, 59, 35, 59, 80, 50, 43, 69, 7, 69, 71, 8, 43, 76, 9, 64, 78, 10, 43, 59, 35, 30, 32, 32, 2, 69, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 59, 7, 35, 71, 8, 59, 59, 9, 35, 78, 10, 50, 69, 9, 7, 71, 10, 8, 80, 13, 13, 11, 4, 59, 35, 30, 32, 32, 2, 69, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 101, 80, 30, 32, 11, 2, 59, 7, 35, 71, 8, 59, 59, 9, 35, 78, 10, 50, 59, 59, 35, 80, 11, 50, 69, 9, 7, 71, 10, 8, 69, 69, 7, 71, 11, 8, 76, 76, 9, 78, 11, 10], [13], [0, 0, 36, 4, 35, 16, 36, 16, 76, 16, 82, 16, 36, 4, 69, 4, 36, 4, 36, 4, 35, 37, 35, 40, 35, 43, 36, 37, 36, 37, 76, 40, 4, 0, 36, 4, 35, 16, 35, 37, 35, 40, 35, 43, 36, 4, 69, 4, 36, 4, 36, 4, 36, 16, 76, 16, 82, 16, 36, 37, 36, 37, 76, 40, 4, 36, 4, 0, 9, 4, 9, 16, 9, 40, 9, 37, 9, 40, 36, 4, 36, 4, 69, 4, 36, 4, 35, 16, 36, 16, 82, 16, 35, 37, 35, 43, 36, 37, 4, 0, 36, 4, 82, 16, 35, 43, 36, 37, 76, 40, 36, 4, 36, 4, 69, 4, 36, 4, 35, 16, 36, 16, 76, 16, 35, 37, 35, 40, 36, 37, 4, 36, 4, 36, 4, 69, 4, 36, 4, 36, 4, 35, 16, 36, 16, 76, 16, 82, 16, 35, 37, 35, 40, 35, 43, 36, 37, 36, 37, 76, 40], [0, 7, 21, 36, 61, 65, 58, 7, 7, 5, 0, 2, 36, 25, 28, 31, 36, 36, 2, 2, 2, 2, 125, 9, 2, 2, 2, 2, 125, 28, 2, 2, 2, 2, 58, 12, 2, 2, 2, 2, 25, 9, 15, 61, 10, 16, 36, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 25, 25, 9, 28, 11, 10, 25, 12, 9, 32, 13, 10, 31, 12, 28, 28, 13, 11, 2, 7, 7, 7, 5, 0, 36, 21, 61, 65, 46, 36, 21, 36, 21, 2, 4, 36, 9, 36, 46, 10, 4, 36, 36, 36, 46, 11, 4, 36, 12, 36, 51, 13, 4, 125, 9, 21, 21, 10, 2, 125, 64, 21, 21, 11, 2, 46, 12, 21, 21, 13, 2, 0, 9, 36, 21, 46, 9, 9, 9, 46, 4, 9, 9, 9, 9, 21, 2, 9, 9, 9, 9, 47, 13, 9, 36, 21, 36, 21, 2, 4, 36, 12, 36, 51, 13, 4, 46, 12, 21, 21, 13, 2, 64, 9, 61, 11, 10, 46, 12, 9, 47, 13, 10, 46, 12, 46, 47, 13, 11, 36, 7, 7, 7, 5, 0, 10, 21, 36, 65, 58, 125, 21, 10, 10, 2, 10, 36, 36, 10, 10, 10, 10, 0, 60, 21, 36, 58, 60, 21, 52, 21, 2, 21, 36, 36, 36, 108, 35, 60, 58, 12, 52, 59, 13, 59, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 64, 10, 10, 10, 10, 58, 12, 10, 10, 10, 10, 36, 36, 21, 21, 21, 2, 100, 64, 21, 21, 11, 2, 58, 12, 21, 21, 13, 2, 36, 36, 36, 65, 11, 35, 36, 12, 36, 59, 13, 35, 58, 12, 58, 59, 13, 11, 10, 7, 7, 7, 5, 0, 11, 21, 36, 61, 58, 125, 21, 11, 11, 2, 11, 36, 36, 11, 11, 11, 11, 0, 9, 21, 36, 58, 9, 9, 9, 21, 2, 9, 9, 9, 9, 108, 35, 9, 9, 9, 9, 59, 13, 9, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 9, 11, 11, 10, 11, 58, 12, 11, 11, 11, 11, 36, 36, 21, 21, 21, 2, 73, 9, 21, 21, 10, 2, 58, 12, 21, 21, 13, 2, 36, 9, 36, 61, 10, 35, 36, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 11, 7, 7, 7, 5, 0, 13, 21, 36, 61, 65, 58, 21, 13, 13, 2, 13, 36, 36, 13, 13, 13, 13, 58, 9, 13, 13, 10, 13, 58, 58, 13, 13, 11, 13, 36, 36, 21, 21, 21, 2, 76, 9, 21, 21, 10, 2, 101, 64, 21, 21, 11, 2, 36, 9, 36, 47, 10, 35, 36, 36, 36, 47, 11, 35, 76, 64, 9, 61, 11, 10, 13, 7, 36, 36, 21, 21, 21, 2, 125, 9, 21, 21, 10, 2, 125, 64, 21, 21, 11, 2, 58, 12, 21, 21, 13, 2, 36, 9, 36, 61, 10, 35, 36, 36, 36, 65, 11, 35, 36, 12, 36, 59, 13, 35, 0, 9, 7, 21, 36, 58, 7, 5, 7, 0, 51, 21, 36, 58, 60, 21, 51, 21, 2, 21, 36, 36, 36, 51, 35, 51, 58, 12, 51, 51, 13, 51, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 7, 9, 9, 9, 9, 21, 2, 9, 9, 9, 9, 108, 35, 9, 9, 9, 9, 59, 13, 9, 7, 7, 5, 25, 2, 7, 7, 7, 5, 0, 36, 9, 21, 46, 9, 9, 9, 46, 9, 4, 36, 21, 36, 21, 2, 4, 36, 12, 36, 51, 13, 4, 9, 9, 9, 21, 2, 9, 9, 9, 9, 47, 13, 9, 46, 12, 21, 21, 13, 2, 36, 7, 7, 7, 5, 76, 13, 7, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 64, 9, 61, 11, 10, 58, 12, 9, 59, 13, 10, 58, 12, 58, 59, 13, 11], [7]]
def rootCodes5 : List (List Nat) := [[58], [0, 8, 22, 37, 62, 67, 70, 0, 22, 37, 62, 67, 70, 37, 34, 22, 22, 22, 19, 62, 9, 22, 22, 10, 19, 99, 66, 22, 22, 11, 19, 70, 12, 22, 22, 13, 19, 37, 9, 34, 63, 10, 37, 37, 37, 34, 67, 11, 37, 37, 12, 34, 71, 13, 37, 62, 62, 9, 63, 11, 10, 62, 12, 9, 63, 13, 10, 70, 12, 66, 67, 13, 11, 22, 8, 8, 2, 6, 0, 36, 22, 62, 67, 70, 36, 22, 3, 22, 2, 22, 36, 9, 3, 63, 10, 36, 36, 36, 3, 67, 11, 36, 36, 12, 3, 71, 13, 36, 62, 9, 22, 22, 10, 2, 126, 66, 22, 22, 11, 2, 70, 12, 22, 22, 13, 2, 62, 62, 9, 63, 11, 10, 62, 12, 9, 63, 13, 10, 70, 12, 66, 67, 13, 11, 36, 8, 8, 8, 6, 0, 9, 22, 37, 67, 70, 9, 9, 9, 22, 2, 9, 9, 9, 9, 63, 37, 9, 9, 9, 9, 63, 11, 9, 9, 9, 9, 63, 13, 9, 37, 34, 22, 22, 22, 2, 99, 66, 22, 22, 11, 2, 70, 12, 22, 22, 13, 2, 37, 37, 34, 67, 11, 37, 37, 12, 34, 71, 13, 37, 70, 12, 66, 67, 13, 11, 9, 8, 8, 8, 6, 0, 67, 22, 37, 62, 70, 125, 22, 64, 22, 2, 22, 37, 34, 37, 67, 37, 57, 62, 9, 62, 63, 10, 57, 70, 12, 64, 67, 13, 57, 37, 34, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 70, 12, 22, 22, 13, 2, 37, 9, 34, 63, 10, 37, 37, 12, 34, 71, 13, 37, 62, 12, 9, 63, 13, 10, 67, 8, 8, 8, 6, 0, 12, 22, 37, 62, 67, 12, 12, 12, 22, 2, 12, 12, 12, 12, 71, 37, 12, 12, 9, 12, 63, 10, 12, 12, 12, 12, 67, 11, 12, 37, 34, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 99, 66, 22, 22, 11, 2, 37, 9, 34, 46, 10, 37, 37, 37, 34, 46, 11, 37, 62, 62, 9, 63, 11, 10, 12, 8, 8, 8, 6, 37, 34, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 126, 66, 22, 22, 11, 2, 70, 12, 22, 22, 13, 2, 37, 9, 34, 63, 10, 37, 37, 37, 34, 67, 11, 37, 37, 12, 34, 71, 13, 37, 62, 62, 9, 63, 11, 10, 62, 12, 9, 63, 13, 10, 70, 12, 66, 67, 13, 11], [8], [0, 0, 58, 6, 34, 19, 62, 19, 89, 19, 58, 19, 37, 6, 58, 6, 58, 6, 70, 6, 34, 54, 34, 57, 34, 59, 62, 54, 58, 54, 58, 57, 6, 0, 36, 6, 34, 19, 34, 54, 34, 57, 34, 59, 58, 6, 58, 6, 58, 6, 70, 6, 62, 19, 122, 19, 58, 19, 62, 54, 58, 54, 58, 57, 6, 0, 9, 6, 9, 19, 9, 54, 9, 54, 9, 54, 58, 6, 37, 6, 58, 6, 70, 6, 34, 19, 89, 19, 58, 19, 34, 57, 34, 59, 58, 57, 6, 0, 58, 6, 105, 19, 34, 57, 62, 54, 58, 57, 58, 6, 37, 6, 58, 6, 70, 6, 34, 19, 62, 19, 58, 19, 34, 54, 34, 59, 58, 54, 6, 58, 6, 58, 6, 37, 6, 58, 6, 58, 6, 70, 6, 34, 19, 62, 19, 122, 19, 58, 19, 34, 54, 34, 57, 34, 59, 62, 54, 58, 54, 58, 57], [0, 9, 25, 108, 62, 73, 58, 9, 9, 5, 0, 2, 81, 21, 28, 31, 99, 36, 2, 2, 2, 2, 99, 7, 2, 2, 2, 2, 99, 28, 2, 2, 2, 2, 58, 12, 2, 2, 2, 2, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 21, 21, 7, 22, 11, 8, 21, 12, 7, 22, 13, 8, 31, 12, 28, 28, 13, 11, 2, 9, 9, 9, 5, 0, 46, 25, 62, 73, 46, 99, 23, 46, 25, 2, 4, 125, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 58, 12, 46, 59, 13, 4, 99, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 46, 12, 23, 25, 13, 2, 113, 72, 7, 62, 11, 8, 46, 12, 7, 47, 13, 8, 46, 12, 46, 47, 13, 11, 46, 9, 9, 7, 5, 0, 8, 22, 37, 67, 58, 99, 22, 8, 8, 2, 8, 125, 36, 8, 8, 8, 8, 0, 60, 22, 37, 58, 60, 22, 48, 22, 2, 22, 37, 36, 37, 67, 35, 60, 58, 12, 48, 59, 13, 59, 37, 36, 22, 22, 22, 2, 58, 12, 22, 22, 13, 2, 37, 12, 36, 59, 13, 35, 67, 8, 8, 8, 8, 58, 12, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 99, 66, 22, 22, 11, 2, 58, 12, 22, 22, 13, 2, 37, 37, 36, 67, 11, 35, 37, 12, 36, 59, 13, 35, 58, 12, 58, 59, 13, 11, 8, 9, 9, 9, 5, 0, 11, 25, 108, 62, 58, 99, 23, 11, 11, 2, 11, 125, 36, 11, 11, 11, 11, 0, 7, 21, 36, 58, 7, 7, 7, 25, 2, 7, 7, 7, 7, 67, 35, 7, 7, 7, 7, 59, 13, 7, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 7, 11, 11, 8, 11, 58, 12, 11, 11, 11, 11, 99, 36, 23, 25, 25, 2, 65, 7, 23, 25, 8, 2, 58, 12, 23, 25, 13, 2, 65, 7, 42, 62, 8, 35, 58, 12, 36, 59, 13, 35, 58, 12, 7, 59, 13, 8, 11, 9, 9, 9, 5, 0, 13, 25, 47, 62, 73, 58, 23, 13, 13, 2, 13, 58, 36, 13, 13, 13, 13, 58, 7, 13, 13, 8, 13, 58, 58, 13, 13, 11, 13, 99, 36, 23, 25, 25, 2, 69, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 69, 7, 45, 47, 8, 35, 114, 72, 36, 47, 11, 35, 69, 69, 7, 62, 11, 8, 13, 9, 99, 36, 23, 25, 25, 2, 99, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 58, 12, 23, 25, 13, 2, 125, 7, 107, 62, 8, 35, 125, 72, 36, 73, 11, 35, 58, 12, 36, 59, 13, 35, 0, 7, 9, 21, 36, 58, 7, 5, 7, 0, 60, 21, 36, 58, 60, 21, 48, 21, 2, 21, 36, 36, 36, 67, 35, 54, 58, 12, 48, 59, 13, 54, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 9, 7, 7, 7, 7, 25, 2, 7, 7, 7, 7, 108, 35, 7, 7, 7, 7, 59, 13, 7, 9, 9, 5, 21, 2, 9, 9, 9, 5, 113, 36, 9, 9, 9, 5, 69, 13, 9, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 72, 7, 62, 11, 8, 58, 12, 7, 59, 13, 8, 58, 12, 58, 59, 13, 11], [9], [58], [0, 10, 87, 106, 50, 119, 77, 0, 87, 106, 50, 119, 77, 99, 34, 23, 87, 40, 19, 50, 7, 23, 51, 8, 19, 99, 74, 23, 87, 11, 19, 77, 12, 23, 78, 13, 19, 50, 7, 34, 51, 8, 40, 106, 74, 34, 116, 11, 40, 77, 12, 34, 78, 13, 40, 50, 50, 7, 51, 11, 8, 50, 12, 7, 51, 13, 8, 77, 12, 74, 78, 13, 11, 87, 10, 10, 2, 6, 0, 36, 81, 36, 112, 77, 36, 24, 3, 87, 2, 36, 50, 7, 3, 51, 8, 36, 36, 36, 3, 116, 11, 36, 36, 12, 3, 78, 13, 36, 36, 7, 24, 37, 8, 2, 100, 74, 24, 81, 11, 2, 77, 12, 24, 78, 13, 2, 36, 36, 7, 37, 11, 8, 36, 12, 7, 37, 13, 8, 77, 12, 74, 78, 13, 11, 36, 10, 10, 10, 6, 0, 7, 21, 36, 65, 68, 7, 7, 7, 51, 2, 7, 7, 7, 7, 51, 36, 7, 7, 7, 7, 51, 11, 7, 7, 7, 7, 51, 13, 7, 36, 34, 21, 21, 21, 2, 100, 64, 21, 21, 11, 2, 68, 12, 21, 21, 13, 2, 36, 36, 34, 65, 11, 36, 36, 12, 34, 69, 13, 36, 68, 12, 64, 65, 13, 11, 7, 10, 10, 8, 6, 0, 119, 87, 106, 50, 77, 100, 24, 64, 87, 2, 57, 106, 34, 64, 116, 40, 57, 50, 7, 50, 51, 8, 51, 77, 12, 64, 78, 13, 57, 100, 34, 24, 87, 40, 2, 50, 7, 24, 51, 8, 2, 77, 12, 24, 78, 13, 2, 50, 7, 34, 51, 8, 40, 77, 12, 34, 78, 13, 40, 50, 12, 7, 51, 13, 8, 119, 10, 10, 10, 6, 0, 12, 31, 46, 50, 79, 12, 12, 12, 78, 2, 12, 12, 12, 12, 78, 40, 12, 12, 7, 12, 51, 8, 12, 12, 12, 12, 78, 11, 12, 99, 34, 24, 31, 31, 2, 50, 7, 24, 31, 8, 2, 99, 74, 24, 31, 11, 2, 50, 7, 34, 46, 8, 40, 106, 74, 34, 46, 11, 40, 50, 50, 7, 51, 11, 8, 12, 10, 10, 10, 6, 100, 34, 24, 87, 40, 2, 50, 7, 24, 51, 8, 2, 100, 74, 24, 87, 11, 2, 77, 12, 24, 78, 13, 2, 50, 7, 34, 51, 8, 40, 106, 74, 34, 116, 11, 40, 77, 12, 34, 78, 13, 40, 50, 50, 7, 51, 11, 8, 50, 12, 7, 51, 13, 8, 77, 12, 74, 78, 13, 11], [10], [50], [0, 58, 93, 108, 121, 123, 58, 58, 58, 5, 0, 2, 81, 21, 25, 31, 0, 36, 21, 25, 31, 21, 7, 3, 22, 8, 16, 25, 9, 3, 85, 10, 16, 31, 12, 3, 32, 13, 16, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 36, 2, 2, 2, 2, 125, 7, 2, 2, 2, 2, 125, 9, 2, 2, 2, 2, 58, 12, 2, 2, 2, 2, 21, 7, 15, 22, 8, 16, 25, 9, 15, 85, 10, 16, 31, 12, 15, 32, 13, 16, 21, 9, 7, 22, 10, 8, 21, 12, 7, 22, 13, 8, 25, 12, 9, 32, 13, 10, 2, 58, 58, 36, 5, 0, 46, 85, 113, 116, 46, 0, 85, 105, 89, 46, 89, 7, 17, 85, 8, 16, 92, 9, 17, 85, 10, 16, 46, 12, 17, 47, 13, 16, 89, 9, 7, 90, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 85, 46, 46, 2, 4, 125, 7, 46, 46, 8, 4, 125, 9, 46, 46, 10, 4, 58, 12, 46, 59, 13, 4, 113, 7, 82, 85, 8, 2, 125, 9, 84, 85, 10, 2, 46, 12, 46, 47, 13, 2, 113, 9, 7, 116, 10, 8, 46, 12, 7, 47, 13, 8, 46, 12, 9, 47, 13, 10, 46, 58, 58, 7, 5, 0, 8, 22, 37, 62, 58, 125, 22, 8, 8, 2, 8, 125, 36, 8, 8, 8, 8, 0, 9, 22, 37, 58, 9, 9, 9, 22, 2, 9, 9, 9, 9, 63, 35, 9, 9, 9, 9, 59, 13, 9, 37, 36, 22, 22, 22, 2, 58, 12, 22, 22, 13, 2, 37, 12, 36, 59, 13, 35, 9, 8, 8, 8, 8, 58, 12, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 58, 12, 22, 22, 13, 2, 37, 9, 36, 63, 10, 35, 37, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 8, 58, 58, 9, 5, 0, 10, 93, 108, 61, 58, 125, 92, 10, 10, 2, 10, 125, 36, 10, 10, 10, 10, 0, 7, 21, 36, 58, 7, 7, 7, 63, 2, 7, 7, 7, 7, 63, 35, 7, 7, 7, 7, 59, 13, 7, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 7, 10, 10, 8, 10, 58, 12, 10, 10, 10, 10, 100, 36, 24, 93, 35, 2, 61, 7, 24, 63, 8, 2, 58, 12, 24, 59, 13, 2, 61, 7, 39, 63, 8, 35, 58, 12, 36, 59, 13, 35, 58, 12, 7, 59, 13, 8, 10, 58, 125, 12, 5, 0, 13, 32, 47, 69, 76, 58, 32, 13, 13, 2, 13, 58, 36, 13, 13, 13, 13, 58, 7, 13, 13, 8, 13, 58, 9, 13, 13, 10, 13, 101, 36, 30, 32, 32, 2, 69, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 69, 7, 45, 47, 8, 35, 76, 9, 36, 47, 10, 35, 69, 9, 7, 71, 10, 8, 13, 58, 0, 36, 58, 36, 89, 58, 36, 5, 3, 0, 85, 36, 89, 58, 36, 7, 17, 37, 8, 16, 92, 9, 17, 85, 10, 16, 58, 12, 17, 59, 13, 16, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 58, 36, 89, 7, 3, 121, 8, 36, 36, 9, 3, 123, 10, 36, 36, 12, 3, 59, 13, 36, 36, 7, 5, 37, 8, 37, 58, 9, 5, 100, 10, 58, 89, 12, 5, 101, 13, 58, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 58, 12, 9, 59, 13, 10, 36, 89, 93, 35, 2, 125, 7, 89, 93, 8, 2, 125, 9, 92, 93, 10, 2, 58, 12, 58, 59, 13, 2, 125, 7, 107, 108, 8, 35, 125, 9, 36, 108, 10, 35, 58, 12, 36, 59, 13, 35, 0, 7, 58, 21, 36, 58, 7, 5, 7, 0, 63, 21, 36, 58, 64, 21, 48, 21, 2, 21, 36, 36, 36, 63, 35, 57, 58, 12, 48, 59, 13, 57, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 58, 7, 7, 7, 7, 93, 2, 7, 7, 7, 7, 108, 35, 7, 7, 7, 7, 59, 13, 7, 58, 21, 5, 21, 2, 21, 36, 36, 5, 113, 36, 58, 64, 12, 5, 69, 13, 58, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 9, 7, 121, 10, 8, 58, 12, 7, 59, 13, 8, 58, 12, 9, 59, 13, 10], [125], [58], [0, 11, 28, 106, 50, 73, 79, 0, 28, 106, 50, 73, 79, 99, 34, 23, 28, 28, 19, 50, 7, 23, 28, 8, 19, 73, 9, 28, 28, 10, 19, 79, 12, 23, 28, 13, 19, 50, 7, 34, 51, 8, 43, 73, 9, 34, 100, 10, 43, 79, 12, 34, 80, 13, 43, 50, 9, 7, 51, 10, 8, 50, 12, 7, 51, 13, 8, 73, 12, 9, 80, 13, 10, 28, 11, 11, 2, 6, 0, 36, 28, 36, 73, 79, 36, 28, 3, 28, 2, 28, 50, 7, 3, 51, 8, 36, 36, 9, 3, 117, 10, 36, 36, 12, 3, 80, 13, 36, 36, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 79, 12, 28, 28, 13, 2, 36, 9, 7, 37, 10, 8, 36, 12, 7, 37, 13, 8, 73, 12, 9, 80, 13, 10, 36, 11, 11, 11, 6, 0, 7, 21, 36, 61, 68, 7, 7, 7, 28, 2, 7, 7, 7, 7, 51, 36, 7, 7, 7, 7, 51, 10, 7, 7, 7, 7, 51, 13, 7, 36, 34, 21, 21, 21, 2, 73, 9, 21, 21, 10, 2, 68, 12, 21, 21, 13, 2, 36, 9, 34, 61, 10, 36, 36, 12, 34, 69, 13, 36, 68, 12, 9, 61, 13, 10, 7, 11, 11, 8, 6, 0, 9, 25, 106, 50, 76, 9, 9, 9, 28, 2, 9, 9, 9, 9, 117, 43, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 80, 13, 9, 99, 34, 23, 25, 25, 2, 50, 7, 23, 25, 8, 2, 79, 12, 23, 25, 13, 2, 50, 7, 34, 51, 8, 43, 79, 12, 34, 76, 13, 43, 50, 12, 7, 51, 13, 8, 9, 11, 11, 10, 6, 0, 12, 28, 46, 50, 73, 12, 12, 12, 28, 2, 12, 12, 12, 12, 80, 43, 12, 12, 7, 12, 51, 8, 12, 12, 9, 12, 80, 10, 12, 99, 34, 28, 28, 28, 2, 50, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 50, 7, 34, 46, 8, 43, 73, 9, 34, 46, 10, 43, 50, 9, 7, 51, 10, 8, 12, 11, 11, 11, 6, 106, 34, 28, 28, 28, 2, 50, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 79, 12, 28, 28, 13, 2, 50, 7, 34, 51, 8, 43, 73, 9, 34, 117, 10, 43, 79, 12, 34, 80, 13, 43, 50, 9, 7, 51, 10, 8, 50, 12, 7, 51, 13, 8, 73, 12, 9, 80, 13, 10], [11]]
def rootCodes6 : List (List Nat) := [[50], [0, 12, 31, 46, 68, 77, 79, 12, 12, 5, 0, 2, 46, 21, 25, 28, 99, 36, 2, 2, 2, 2, 68, 7, 2, 2, 2, 2, 0, 9, 46, 21, 28, 9, 9, 9, 46, 16, 9, 9, 7, 9, 22, 8, 9, 9, 9, 9, 28, 11, 9, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 21, 21, 7, 22, 11, 8, 9, 2, 2, 2, 2, 99, 28, 2, 2, 2, 2, 21, 7, 15, 22, 8, 16, 25, 9, 15, 46, 10, 16, 81, 28, 15, 28, 11, 16, 21, 9, 7, 22, 10, 8, 21, 21, 7, 22, 11, 8, 25, 25, 9, 28, 11, 10, 2, 12, 12, 12, 5, 0, 46, 31, 68, 77, 79, 99, 29, 46, 31, 2, 4, 68, 7, 46, 46, 8, 4, 99, 9, 46, 46, 10, 4, 0, 105, 31, 68, 77, 99, 29, 33, 31, 2, 31, 68, 7, 33, 70, 8, 43, 99, 9, 33, 77, 10, 43, 68, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 68, 9, 7, 70, 10, 8, 79, 46, 46, 11, 4, 68, 7, 29, 31, 8, 2, 0, 9, 46, 62, 73, 9, 9, 9, 46, 4, 9, 9, 7, 9, 70, 8, 9, 9, 9, 9, 79, 11, 9, 68, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 68, 68, 7, 62, 11, 8, 9, 29, 31, 10, 2, 99, 79, 29, 31, 11, 2, 68, 9, 7, 70, 10, 8, 68, 68, 7, 70, 11, 8, 99, 79, 9, 77, 11, 10, 46, 12, 12, 7, 5, 0, 8, 22, 37, 62, 67, 68, 22, 8, 8, 2, 8, 68, 36, 8, 8, 8, 8, 68, 9, 8, 8, 8, 8, 68, 67, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 99, 66, 22, 22, 11, 2, 37, 9, 36, 46, 10, 35, 37, 37, 36, 46, 11, 35, 62, 62, 9, 63, 11, 10, 8, 12, 12, 9, 5, 0, 10, 31, 46, 61, 79, 0, 29, 46, 61, 79, 29, 29, 17, 46, 35, 26, 29, 7, 17, 63, 8, 26, 29, 29, 17, 79, 11, 26, 61, 7, 39, 46, 8, 35, 110, 74, 36, 46, 11, 35, 61, 61, 7, 63, 11, 8, 29, 10, 10, 2, 10, 99, 36, 10, 10, 10, 10, 68, 7, 10, 10, 8, 10, 99, 79, 10, 10, 10, 10, 99, 36, 24, 31, 31, 2, 61, 7, 24, 31, 8, 2, 99, 74, 24, 31, 11, 2, 61, 7, 39, 46, 8, 35, 110, 74, 36, 46, 11, 35, 61, 61, 7, 63, 11, 8, 10, 12, 12, 12, 5, 0, 11, 28, 46, 65, 73, 99, 28, 11, 11, 2, 11, 0, 36, 28, 36, 73, 36, 28, 3, 28, 2, 28, 65, 7, 3, 67, 8, 36, 36, 9, 3, 77, 10, 36, 36, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 36, 9, 7, 37, 10, 8, 36, 11, 11, 11, 11, 68, 7, 11, 11, 8, 11, 99, 9, 11, 11, 10, 11, 99, 36, 28, 28, 28, 2, 65, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 65, 7, 42, 46, 8, 35, 73, 9, 36, 46, 10, 35, 65, 9, 7, 67, 10, 8, 11, 12, 99, 36, 29, 31, 31, 2, 68, 7, 29, 31, 8, 2, 0, 9, 12, 46, 62, 73, 9, 5, 9, 0, 29, 46, 62, 73, 29, 29, 17, 46, 35, 26, 29, 7, 17, 62, 8, 26, 29, 29, 17, 73, 11, 26, 68, 7, 46, 46, 8, 35, 125, 72, 36, 46, 11, 35, 68, 68, 7, 62, 11, 8, 12, 9, 9, 9, 9, 46, 35, 9, 9, 7, 9, 70, 8, 9, 9, 9, 9, 79, 11, 9, 12, 12, 5, 0, 46, 9, 62, 73, 9, 9, 9, 46, 9, 4, 68, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 9, 7, 9, 70, 8, 9, 9, 9, 9, 79, 11, 9, 68, 68, 7, 62, 11, 8, 46, 12, 12, 7, 5, 62, 8, 12, 12, 12, 5, 73, 11, 12, 68, 7, 46, 46, 8, 35, 125, 72, 36, 46, 11, 35, 68, 68, 7, 62, 11, 8, 9, 29, 31, 10, 2, 99, 79, 29, 31, 11, 2, 68, 7, 46, 46, 8, 35, 99, 9, 36, 46, 10, 35, 0, 36, 12, 31, 36, 77, 12, 5, 3, 0, 105, 31, 36, 77, 99, 29, 33, 31, 2, 31, 36, 7, 33, 37, 8, 37, 99, 9, 33, 77, 10, 43, 36, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 36, 9, 7, 37, 10, 8, 12, 36, 36, 29, 3, 31, 2, 31, 68, 7, 3, 70, 8, 36, 36, 9, 3, 77, 10, 36, 12, 12, 5, 81, 2, 12, 12, 7, 5, 37, 8, 12, 12, 9, 5, 110, 10, 12, 36, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 36, 9, 7, 37, 10, 8, 79, 36, 46, 11, 35, 68, 9, 7, 70, 10, 8, 68, 68, 7, 70, 11, 8, 99, 79, 9, 77, 11, 10], [12], [0, 5, 87, 5, 0, 5, 46, 89, 18, 50, 35, 89, 35, 105, 35, 5, 31, 5, 70, 5, 50, 5, 50, 50, 18, 0, 9, 35, 5, 50, 9, 49, 9, 55, 5, 46, 50, 35, 105, 35, 5, 62, 5, 50, 50, 49, 18, 89, 18, 50, 49, 50, 49, 89, 53, 5, 51, 5, 118, 5, 119, 5, 31, 5, 46, 5, 70, 5, 50, 5, 50, 89, 18, 50, 18, 0, 5, 0, 5, 50, 17, 35, 17, 49, 17, 55, 5, 46, 5, 62, 5, 50, 50, 35, 105, 35, 50, 49, 5, 50, 9, 35, 9, 49, 9, 55, 5, 0, 9, 35, 5, 46, 50, 35, 105, 35, 5, 50, 9, 49, 9, 55, 5, 62, 5, 50, 50, 49, 5, 51, 5, 73, 5, 46, 5, 62, 5, 50, 50, 35, 105, 35, 50, 49, 18, 89, 18, 50, 35, 89, 35, 105, 35, 50, 49, 50, 49, 89, 53], [0, 13, 32, 47, 50, 76, 80, 0, 32, 47, 50, 76, 80, 58, 34, 23, 32, 32, 19, 50, 7, 23, 32, 8, 19, 58, 9, 29, 32, 10, 19, 58, 58, 23, 32, 11, 19, 50, 7, 34, 47, 8, 46, 76, 9, 34, 47, 10, 46, 106, 80, 34, 47, 11, 46, 50, 9, 7, 51, 10, 8, 50, 50, 7, 51, 11, 8, 76, 76, 9, 78, 11, 10, 32, 13, 13, 2, 6, 0, 36, 32, 36, 76, 80, 36, 30, 3, 32, 2, 32, 50, 7, 3, 47, 8, 36, 36, 9, 3, 47, 10, 36, 36, 36, 3, 47, 11, 36, 36, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 101, 80, 30, 32, 11, 2, 36, 9, 7, 37, 10, 8, 36, 36, 7, 37, 11, 8, 76, 76, 9, 78, 11, 10, 36, 13, 13, 13, 6, 0, 7, 21, 36, 61, 65, 7, 7, 7, 32, 2, 7, 7, 7, 7, 47, 36, 7, 7, 7, 7, 51, 10, 7, 7, 7, 7, 51, 11, 7, 36, 34, 21, 21, 21, 2, 76, 9, 21, 21, 10, 2, 101, 64, 21, 21, 11, 2, 36, 9, 34, 47, 10, 36, 36, 36, 34, 47, 11, 36, 76, 64, 9, 61, 11, 10, 7, 13, 13, 8, 6, 0, 9, 25, 47, 50, 73, 9, 9, 9, 32, 2, 9, 9, 9, 9, 47, 46, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 78, 11, 9, 99, 34, 23, 25, 25, 2, 50, 7, 23, 25, 8, 2, 99, 72, 23, 25, 11, 2, 50, 7, 34, 47, 8, 46, 106, 72, 34, 47, 11, 46, 50, 50, 7, 51, 11, 8, 9, 13, 13, 10, 6, 0, 58, 32, 47, 50, 76, 58, 30, 58, 32, 2, 32, 58, 34, 58, 47, 46, 47, 50, 7, 50, 51, 8, 51, 58, 9, 58, 78, 10, 57, 101, 34, 30, 32, 32, 2, 50, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 50, 7, 34, 47, 8, 46, 76, 9, 34, 47, 10, 46, 50, 9, 7, 51, 10, 8, 80, 13, 13, 11, 6, 101, 34, 30, 32, 32, 2, 50, 7, 30, 32, 8, 2, 76, 9, 30, 32, 10, 2, 101, 80, 30, 32, 11, 2, 50, 7, 34, 47, 8, 46, 76, 9, 34, 47, 10, 46, 106, 80, 34, 47, 11, 46, 50, 9, 7, 51, 10, 8, 50, 50, 7, 51, 11, 8, 76, 76, 9, 78, 11, 10], [13], [50], [0, 7, 21, 36, 50, 65, 68, 7, 7, 7, 0, 2, 36, 50, 28, 31, 36, 36, 2, 2, 2, 2, 99, 50, 2, 2, 2, 2, 99, 28, 2, 2, 2, 2, 68, 12, 2, 2, 2, 2, 36, 18, 15, 50, 19, 16, 36, 28, 15, 28, 11, 16, 31, 12, 15, 32, 13, 16, 93, 28, 18, 28, 11, 19, 31, 12, 18, 32, 13, 19, 31, 12, 28, 28, 13, 11, 2, 7, 7, 7, 7, 0, 36, 21, 50, 65, 46, 36, 21, 36, 21, 2, 4, 36, 36, 36, 46, 46, 4, 36, 36, 36, 46, 11, 4, 36, 12, 36, 63, 13, 4, 99, 35, 21, 21, 21, 2, 99, 64, 21, 21, 11, 2, 46, 12, 21, 21, 13, 2, 108, 64, 35, 50, 11, 50, 46, 12, 35, 47, 13, 47, 46, 12, 46, 47, 13, 11, 36, 7, 7, 7, 7, 0, 50, 21, 36, 65, 68, 99, 21, 50, 21, 2, 6, 36, 36, 36, 50, 36, 6, 0, 64, 21, 36, 68, 64, 21, 48, 21, 2, 21, 36, 34, 36, 113, 36, 57, 64, 12, 48, 69, 13, 57, 36, 34, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 36, 12, 34, 69, 13, 36, 64, 50, 50, 11, 6, 68, 12, 50, 50, 13, 6, 36, 34, 21, 21, 21, 2, 99, 64, 21, 21, 11, 2, 68, 12, 21, 21, 13, 2, 36, 36, 34, 65, 11, 36, 36, 12, 34, 69, 13, 36, 68, 12, 64, 65, 13, 11, 50, 7, 7, 7, 7, 0, 11, 21, 36, 50, 68, 99, 21, 11, 11, 2, 11, 36, 36, 11, 11, 11, 11, 0, 58, 21, 36, 58, 58, 21, 5, 21, 2, 21, 36, 36, 5, 113, 36, 57, 64, 12, 5, 69, 13, 57, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 50, 11, 11, 11, 11, 68, 12, 11, 11, 11, 11, 36, 36, 21, 21, 21, 2, 99, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 11, 7, 7, 7, 7, 0, 13, 21, 36, 50, 65, 68, 21, 13, 13, 2, 13, 36, 36, 13, 13, 13, 13, 68, 50, 13, 13, 13, 13, 68, 64, 13, 13, 11, 13, 36, 36, 21, 21, 21, 2, 59, 50, 21, 21, 21, 2, 99, 64, 21, 21, 11, 2, 36, 36, 36, 47, 47, 36, 36, 36, 36, 47, 11, 36, 59, 59, 50, 50, 11, 50, 13, 7, 36, 36, 21, 21, 21, 2, 99, 50, 21, 21, 21, 2, 99, 64, 21, 21, 11, 2, 68, 12, 21, 21, 13, 2, 36, 36, 36, 50, 50, 36, 36, 36, 36, 65, 11, 36, 36, 12, 36, 69, 13, 36, 0, 58, 7, 21, 36, 58, 7, 7, 5, 0, 63, 21, 36, 58, 64, 21, 48, 21, 2, 21, 36, 36, 36, 63, 35, 57, 58, 12, 48, 59, 13, 57, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 7, 58, 58, 21, 5, 21, 2, 21, 36, 36, 5, 113, 36, 58, 64, 12, 5, 69, 13, 58, 7, 7, 7, 93, 2, 7, 7, 7, 7, 108, 35, 7, 7, 7, 7, 59, 13, 7, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 64, 50, 50, 11, 50, 68, 12, 50, 50, 13, 50, 68, 12, 64, 65, 13, 11], [9], [7], [0, 8, 22, 37, 51, 67, 70, 0, 22, 37, 51, 67, 70, 37, 36, 22, 22, 22, 22, 99, 49, 22, 22, 22, 22, 99, 66, 22, 22, 11, 22, 70, 12, 22, 22, 13, 22, 37, 37, 36, 51, 50, 37, 37, 37, 36, 67, 11, 37, 37, 12, 36, 71, 13, 37, 121, 66, 49, 51, 11, 50, 70, 12, 49, 51, 13, 50, 70, 12, 66, 67, 13, 11, 22, 8, 8, 2, 8, 0, 36, 22, 51, 67, 70, 36, 22, 3, 22, 2, 22, 36, 36, 3, 51, 50, 36, 36, 36, 3, 67, 11, 36, 36, 12, 3, 71, 13, 36, 100, 49, 22, 22, 22, 2, 100, 66, 22, 22, 11, 2, 70, 12, 22, 22, 13, 2, 121, 66, 49, 51, 11, 34, 70, 12, 49, 51, 13, 34, 70, 12, 66, 67, 13, 11, 36, 8, 8, 8, 8, 0, 51, 22, 37, 67, 58, 58, 22, 5, 22, 2, 22, 37, 36, 5, 51, 37, 51, 58, 58, 5, 51, 11, 51, 70, 12, 5, 51, 13, 51, 37, 36, 22, 22, 22, 2, 100, 66, 22, 22, 11, 2, 58, 12, 22, 22, 13, 2, 37, 37, 36, 67, 11, 35, 37, 12, 36, 59, 13, 35, 58, 12, 58, 59, 13, 11, 51, 8, 8, 8, 8, 0, 67, 22, 37, 51, 70, 100, 22, 60, 22, 2, 22, 37, 36, 37, 67, 37, 67, 121, 49, 60, 51, 50, 51, 70, 12, 60, 67, 13, 67, 37, 36, 22, 22, 22, 2, 100, 49, 22, 22, 22, 2, 70, 12, 22, 22, 13, 2, 37, 37, 36, 51, 50, 37, 37, 12, 36, 71, 13, 37, 70, 12, 49, 51, 13, 50, 67, 8, 8, 8, 8, 0, 12, 22, 37, 51, 67, 12, 12, 12, 22, 2, 12, 12, 12, 12, 71, 37, 12, 12, 12, 12, 51, 50, 12, 12, 12, 12, 67, 11, 12, 37, 36, 22, 22, 22, 2, 58, 49, 22, 22, 22, 2, 99, 66, 22, 22, 11, 2, 37, 37, 36, 46, 46, 37, 37, 37, 36, 46, 11, 37, 58, 58, 49, 51, 11, 50, 12, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 100, 49, 22, 22, 22, 2, 100, 66, 22, 22, 11, 2, 70, 12, 22, 22, 13, 2, 37, 37, 36, 51, 50, 37, 37, 37, 36, 67, 11, 37, 37, 12, 36, 71, 13, 37, 121, 66, 49, 51, 11, 50, 70, 12, 49, 51, 13, 50, 70, 12, 66, 67, 13, 11], [10], [8], [0, 7, 21, 36, 50, 61, 68, 7, 7, 7, 0, 2, 36, 50, 25, 31, 36, 36, 2, 2, 2, 2, 0, 58, 36, 25, 31, 36, 15, 5, 85, 16, 19, 25, 9, 5, 61, 10, 19, 31, 12, 5, 32, 13, 19, 25, 9, 15, 61, 10, 16, 31, 12, 15, 32, 13, 16, 25, 12, 9, 32, 13, 10, 50, 2, 2, 2, 2, 0, 9, 36, 50, 31, 9, 9, 9, 85, 16, 9, 9, 9, 9, 50, 19, 9, 9, 9, 9, 32, 13, 9, 36, 18, 15, 50, 19, 16, 31, 12, 15, 32, 13, 16, 31, 12, 18, 32, 13, 19, 9, 2, 2, 2, 2, 68, 12, 2, 2, 2, 2, 36, 18, 15, 50, 19, 16, 25, 9, 15, 61, 10, 16, 31, 12, 15, 32, 13, 16, 25, 9, 18, 50, 10, 19, 31, 12, 18, 32, 13, 19, 25, 12, 9, 32, 13, 10, 2, 7, 7, 7, 7, 0, 36, 21, 50, 61, 46, 36, 21, 36, 21, 2, 4, 36, 36, 36, 46, 46, 4, 36, 9, 36, 46, 10, 4, 36, 12, 36, 67, 13, 4, 108, 35, 21, 21, 21, 2, 128, 9, 21, 21, 10, 2, 46, 12, 21, 21, 13, 2, 108, 9, 35, 50, 10, 50, 46, 12, 35, 47, 13, 47, 46, 12, 9, 47, 13, 10, 36, 7, 7, 7, 7, 0, 50, 21, 36, 61, 68, 0, 87, 36, 61, 68, 36, 34, 23, 87, 36, 19, 105, 9, 29, 61, 10, 19, 68, 12, 23, 69, 13, 19, 36, 9, 34, 61, 10, 36, 36, 12, 34, 69, 13, 36, 68, 12, 9, 61, 13, 10, 21, 50, 21, 2, 6, 36, 36, 36, 50, 36, 6, 0, 9, 21, 36, 68, 9, 9, 9, 21, 2, 9, 9, 9, 9, 113, 36, 9, 9, 9, 9, 69, 13, 9, 36, 34, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 36, 12, 34, 69, 13, 36, 9, 50, 50, 10, 6, 68, 12, 50, 50, 13, 6, 36, 34, 21, 21, 21, 2, 128, 9, 21, 21, 10, 2, 68, 12, 21, 21, 13, 2, 36, 9, 34, 61, 10, 36, 36, 12, 34, 69, 13, 36, 68, 12, 9, 61, 13, 10, 50, 7, 7, 7, 7, 0, 10, 21, 36, 50, 68, 0, 60, 36, 50, 68, 36, 36, 23, 95, 36, 26, 60, 50, 23, 50, 50, 26, 60, 12, 23, 69, 13, 26, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 21, 10, 10, 2, 10, 36, 36, 10, 10, 10, 10, 0, 58, 21, 36, 58, 58, 21, 5, 21, 2, 21, 36, 36, 5, 113, 36, 54, 60, 12, 5, 69, 13, 54, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 50, 10, 10, 10, 10, 68, 12, 10, 10, 10, 10, 36, 36, 21, 21, 21, 2, 100, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 10, 7, 7, 7, 7, 0, 13, 21, 36, 50, 61, 68, 21, 13, 13, 2, 13, 36, 36, 13, 13, 13, 13, 68, 50, 13, 13, 13, 13, 68, 9, 13, 13, 10, 13, 36, 36, 21, 21, 21, 2, 59, 50, 21, 21, 21, 2, 76, 9, 21, 21, 10, 2, 36, 36, 36, 47, 47, 36, 36, 9, 36, 47, 10, 36, 59, 9, 50, 50, 10, 50, 13, 7, 36, 36, 21, 21, 21, 2, 0, 58, 7, 36, 61, 58, 7, 7, 5, 0, 67, 36, 61, 58, 36, 36, 36, 67, 35, 19, 99, 9, 48, 61, 10, 19, 58, 12, 48, 59, 13, 19, 36, 9, 36, 61, 10, 35, 36, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 7, 58, 36, 36, 5, 87, 36, 58, 58, 9, 5, 61, 10, 58, 68, 12, 5, 69, 13, 58, 7, 7, 7, 108, 35, 7, 7, 7, 7, 100, 10, 7, 7, 7, 7, 59, 13, 7, 36, 9, 36, 61, 10, 35, 36, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 50, 21, 21, 21, 2, 0, 9, 7, 36, 50, 68, 7, 7, 7, 0, 60, 36, 50, 68, 36, 36, 36, 67, 36, 26, 60, 50, 60, 50, 50, 26, 60, 12, 60, 67, 13, 26, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 7, 9, 9, 9, 9, 95, 36, 9, 9, 9, 9, 50, 50, 9, 9, 9, 9, 69, 13, 9, 7, 7, 7, 128, 36, 7, 7, 7, 7, 128, 50, 7, 7, 7, 7, 76, 13, 7, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 9, 21, 21, 10, 2, 68, 12, 21, 21, 13, 2, 36, 36, 36, 50, 50, 36, 36, 9, 36, 61, 10, 36, 36, 12, 36, 69, 13, 36, 0, 9, 7, 21, 36, 58, 7, 7, 5, 0, 60, 21, 36, 58, 60, 21, 48, 21, 2, 21, 36, 36, 36, 67, 35, 54, 58, 12, 48, 59, 13, 54, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 7, 9, 9, 9, 5, 21, 2, 9, 9, 9, 5, 113, 36, 9, 9, 9, 5, 69, 13, 9, 7, 7, 7, 25, 2, 7, 7, 7, 7, 108, 35, 7, 7, 7, 7, 59, 13, 7, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 9, 50, 50, 10, 50, 68, 12, 50, 50, 13, 50, 68, 12, 9, 61, 13, 10], [0, 7, 28, 7, 67, 7, 67, 7, 67, 7, 67, 72, 11, 36, 11, 72, 11, 0, 7, 67, 9, 21, 9, 113, 9, 50, 9, 69, 7, 25, 7, 67, 7, 67, 7, 67, 36, 21, 99, 21, 68, 21, 36, 50, 36, 69, 68, 50, 11, 68, 11, 36, 21, 124, 21, 72, 21, 68, 21, 36, 50, 36, 61, 36, 69, 72, 50, 68, 50, 68, 61]]
def rootCodes7 : List (List Nat) := [[7], [0, 8, 22, 37, 51, 62, 70, 0, 22, 37, 51, 62, 70, 37, 36, 22, 22, 22, 22, 99, 49, 22, 22, 22, 22, 62, 9, 22, 22, 10, 22, 70, 12, 22, 22, 13, 22, 37, 37, 36, 51, 50, 37, 37, 9, 36, 63, 10, 37, 37, 12, 36, 71, 13, 37, 62, 9, 49, 51, 10, 50, 70, 12, 49, 51, 13, 50, 62, 12, 9, 63, 13, 10, 22, 8, 8, 2, 8, 0, 36, 22, 51, 62, 70, 36, 22, 3, 22, 2, 22, 36, 36, 3, 51, 50, 36, 36, 9, 3, 63, 10, 36, 36, 12, 3, 71, 13, 36, 121, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 70, 12, 22, 22, 13, 2, 62, 9, 49, 51, 10, 34, 70, 12, 49, 51, 13, 34, 62, 12, 9, 63, 13, 10, 36, 8, 8, 8, 8, 0, 51, 22, 37, 62, 58, 58, 22, 5, 22, 2, 22, 37, 36, 5, 51, 37, 51, 58, 9, 5, 51, 10, 51, 70, 12, 5, 51, 13, 51, 37, 36, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 58, 12, 22, 22, 13, 2, 37, 9, 36, 63, 10, 35, 37, 12, 36, 59, 13, 35, 58, 12, 9, 59, 13, 10, 51, 8, 8, 8, 8, 0, 9, 22, 37, 51, 70, 9, 9, 9, 22, 2, 9, 9, 9, 9, 63, 37, 9, 9, 9, 9, 51, 50, 9, 9, 9, 9, 63, 13, 9, 37, 36, 22, 22, 22, 2, 99, 49, 22, 22, 22, 2, 70, 12, 22, 22, 13, 2, 37, 37, 36, 51, 50, 37, 37, 12, 36, 71, 13, 37, 70, 12, 49, 51, 13, 50, 9, 8, 8, 8, 8, 0, 12, 22, 37, 51, 62, 12, 12, 12, 22, 2, 12, 12, 12, 12, 71, 37, 12, 12, 12, 12, 51, 50, 12, 12, 9, 12, 63, 10, 12, 37, 36, 22, 22, 22, 2, 58, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 37, 37, 36, 46, 46, 37, 37, 9, 36, 46, 10, 37, 58, 9, 49, 51, 10, 50, 12, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 121, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 70, 12, 22, 22, 13, 2, 37, 37, 36, 51, 50, 37, 37, 9, 36, 63, 10, 37, 37, 12, 36, 71, 13, 37, 62, 9, 49, 51, 10, 50, 70, 12, 49, 51, 13, 50, 62, 12, 9, 63, 13, 10], [11], [8], [0, 7, 21, 36, 50, 61, 65, 7, 7, 7, 0, 2, 36, 50, 25, 28, 36, 36, 2, 2, 2, 2, 58, 50, 2, 2, 2, 2, 125, 9, 2, 2, 2, 2, 99, 28, 2, 2, 2, 2, 36, 18, 15, 46, 19, 16, 25, 9, 15, 46, 10, 16, 36, 28, 15, 28, 11, 16, 25, 9, 18, 50, 10, 19, 58, 28, 18, 28, 11, 19, 25, 25, 9, 28, 11, 10, 2, 7, 7, 7, 7, 0, 36, 21, 50, 61, 65, 36, 21, 36, 21, 2, 4, 36, 36, 36, 46, 46, 4, 36, 9, 36, 46, 10, 4, 36, 36, 36, 46, 11, 4, 58, 35, 21, 21, 21, 2, 125, 9, 21, 21, 10, 2, 99, 64, 21, 21, 11, 2, 58, 9, 35, 50, 10, 50, 58, 58, 35, 50, 11, 50, 99, 64, 9, 61, 11, 10, 36, 7, 7, 7, 7, 0, 50, 21, 36, 61, 65, 58, 21, 50, 21, 2, 6, 36, 36, 36, 46, 36, 6, 58, 9, 50, 50, 10, 6, 58, 58, 50, 50, 11, 6, 36, 34, 21, 21, 21, 2, 125, 9, 21, 21, 10, 2, 99, 64, 21, 21, 11, 2, 36, 9, 34, 46, 10, 36, 36, 36, 34, 46, 11, 36, 99, 64, 9, 61, 11, 10, 50, 7, 7, 7, 7, 0, 10, 21, 36, 50, 65, 125, 21, 10, 10, 2, 10, 36, 36, 10, 10, 10, 10, 58, 50, 10, 10, 10, 10, 99, 64, 10, 10, 10, 10, 36, 36, 21, 21, 21, 2, 58, 50, 21, 21, 21, 2, 99, 64, 21, 21, 11, 2, 36, 36, 36, 46, 46, 36, 36, 36, 36, 46, 11, 36, 58, 58, 50, 50, 11, 50, 10, 7, 7, 7, 7, 0, 11, 21, 36, 50, 61, 99, 21, 11, 11, 2, 11, 36, 36, 11, 11, 11, 11, 58, 50, 11, 11, 11, 11, 99, 9, 11, 11, 10, 11, 36, 36, 21, 21, 21, 2, 58, 50, 21, 21, 21, 2, 73, 9, 21, 21, 10, 2, 36, 36, 36, 46, 46, 36, 36, 9, 36, 46, 10, 36, 58, 9, 50, 50, 10, 50, 11, 7, 36, 36, 21, 21, 21, 2, 58, 50, 21, 21, 21, 2, 125, 9, 21, 21, 10, 2, 99, 64, 21, 21, 11, 2, 36, 36, 36, 46, 46, 36, 36, 9, 36, 46, 10, 36, 36, 36, 36, 46, 11, 36, 58, 9, 50, 50, 10, 50, 58, 58, 50, 50, 11, 50, 99, 64, 9, 61, 11, 10], [12], [7], [0, 8, 22, 37, 51, 62, 67, 0, 22, 37, 51, 62, 67, 37, 36, 22, 22, 22, 22, 59, 49, 22, 22, 22, 22, 62, 9, 22, 22, 10, 22, 68, 66, 22, 22, 11, 22, 37, 37, 36, 47, 47, 37, 37, 9, 36, 47, 10, 37, 37, 37, 36, 47, 11, 37, 59, 9, 49, 51, 10, 50, 59, 59, 49, 51, 11, 50, 62, 62, 9, 63, 11, 10, 22, 8, 8, 2, 8, 0, 36, 22, 51, 62, 67, 36, 22, 3, 22, 2, 22, 36, 36, 3, 47, 47, 36, 36, 9, 3, 47, 10, 36, 36, 36, 3, 47, 11, 36, 59, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 101, 66, 22, 22, 11, 2, 59, 9, 49, 51, 10, 34, 59, 59, 49, 51, 11, 34, 62, 62, 9, 63, 11, 10, 36, 8, 8, 8, 8, 0, 51, 22, 37, 62, 67, 58, 22, 5, 22, 2, 22, 37, 36, 5, 47, 37, 47, 58, 9, 5, 51, 10, 51, 58, 58, 5, 51, 11, 51, 37, 36, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 101, 66, 22, 22, 11, 2, 37, 9, 36, 47, 10, 35, 37, 37, 36, 47, 11, 35, 62, 62, 9, 63, 11, 10, 51, 8, 8, 8, 8, 0, 9, 22, 37, 51, 67, 9, 9, 9, 22, 2, 9, 9, 9, 9, 47, 37, 9, 9, 9, 9, 51, 50, 9, 9, 9, 9, 63, 11, 9, 37, 36, 22, 22, 22, 2, 59, 49, 22, 22, 22, 2, 99, 66, 22, 22, 11, 2, 37, 37, 36, 47, 47, 37, 37, 37, 36, 47, 11, 37, 59, 59, 49, 51, 11, 50, 9, 8, 8, 8, 8, 0, 67, 22, 37, 51, 62, 68, 22, 64, 22, 2, 22, 37, 36, 37, 47, 37, 47, 59, 49, 59, 51, 50, 51, 62, 9, 62, 63, 10, 63, 37, 36, 22, 22, 22, 2, 59, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 37, 37, 36, 47, 47, 37, 37, 9, 36, 47, 10, 37, 59, 9, 49, 51, 10, 50, 67, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 59, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 101, 66, 22, 22, 11, 2, 37, 37, 36, 47, 47, 37, 37, 9, 36, 47, 10, 37, 37, 37, 36, 47, 11, 37, 59, 9, 49, 51, 10, 50, 59, 59, 49, 51, 11, 50, 62, 62, 9, 63, 11, 10], [13], [8], [0, 9, 25, 0, 9, 36, 46, 25, 46, 36, 46, 62, 82, 36, 9, 81, 9, 106, 9, 37, 9, 47, 82, 25, 36, 25, 46, 25, 36, 37, 46, 47, 36, 37, 0, 9, 58, 50, 25, 50, 58, 0, 6, 121, 6, 25, 6, 108, 6, 59, 9, 19, 9, 108, 9, 59, 34, 19, 58, 19, 34, 59, 58, 50, 76, 9, 87, 9, 108, 9, 51, 9, 59, 89, 25, 50, 25, 58, 25, 50, 51, 58, 59, 50, 51, 62, 76, 9, 9, 9, 0, 2, 81, 87, 21, 31, 99, 36, 2, 2, 2, 2, 99, 58, 2, 2, 2, 2, 99, 7, 2, 2, 2, 2, 0, 12, 46, 58, 21, 12, 12, 12, 32, 16, 12, 12, 12, 12, 32, 19, 12, 12, 7, 12, 22, 8, 12, 58, 18, 15, 46, 19, 16, 21, 7, 15, 22, 8, 16, 21, 7, 18, 22, 8, 19, 12, 2, 2, 2, 2, 81, 18, 15, 85, 19, 16, 21, 7, 15, 22, 8, 16, 31, 12, 15, 32, 13, 16, 21, 7, 18, 22, 8, 19, 31, 12, 18, 32, 13, 19, 21, 12, 7, 22, 13, 8, 2, 9, 9, 9, 9, 0, 46, 25, 108, 62, 46, 99, 23, 46, 25, 2, 4, 0, 58, 25, 62, 46, 58, 23, 5, 25, 2, 25, 58, 7, 5, 62, 8, 58, 46, 12, 5, 47, 13, 47, 89, 7, 23, 25, 8, 2, 46, 12, 23, 25, 13, 2, 46, 12, 7, 47, 13, 8, 58, 46, 46, 46, 4, 0, 7, 21, 50, 46, 7, 7, 7, 25, 2, 7, 7, 7, 7, 0, 50, 21, 46, 99, 21, 50, 21, 2, 6, 46, 12, 46, 47, 13, 6, 46, 12, 21, 21, 13, 2, 50, 7, 7, 7, 7, 47, 13, 7, 99, 35, 21, 21, 21, 2, 46, 12, 21, 21, 13, 2, 46, 12, 35, 47, 13, 47, 7, 46, 46, 8, 4, 99, 12, 46, 76, 13, 4, 99, 35, 23, 25, 25, 2, 99, 7, 23, 25, 8, 2, 46, 12, 23, 25, 13, 2, 108, 7, 35, 62, 8, 62, 46, 12, 35, 47, 13, 47, 46, 12, 7, 47, 13, 8, 46, 9, 9, 9, 9, 0, 50, 25, 106, 50, 76, 99, 23, 50, 25, 2, 6, 0, 36, 25, 36, 76, 36, 23, 3, 25, 2, 25, 50, 7, 3, 51, 8, 36, 36, 12, 3, 76, 13, 36, 36, 7, 23, 25, 8, 2, 89, 12, 23, 25, 13, 2, 36, 12, 7, 37, 13, 8, 36, 50, 50, 46, 6, 0, 7, 21, 36, 68, 7, 7, 7, 25, 2, 7, 7, 7, 7, 51, 36, 7, 7, 7, 7, 51, 13, 7, 36, 34, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 36, 12, 34, 69, 13, 36, 7, 50, 62, 8, 6, 99, 12, 50, 50, 13, 6, 99, 34, 23, 25, 25, 2, 50, 7, 23, 25, 8, 2, 120, 12, 23, 25, 13, 2, 50, 7, 34, 51, 8, 46, 99, 12, 34, 76, 13, 76, 50, 12, 7, 51, 13, 8, 50, 9, 9, 7, 9, 0, 8, 22, 37, 51, 70, 99, 22, 8, 8, 2, 8, 0, 36, 22, 51, 70, 36, 22, 3, 22, 2, 22, 36, 36, 3, 51, 50, 36, 36, 12, 3, 71, 13, 36, 99, 49, 22, 22, 22, 2, 70, 12, 22, 22, 13, 2, 70, 12, 49, 51, 13, 34, 36, 8, 8, 8, 8, 0, 51, 22, 37, 58, 58, 22, 5, 22, 2, 22, 37, 36, 5, 51, 37, 51, 60, 12, 5, 51, 13, 51, 37, 36, 22, 22, 22, 2, 58, 12, 22, 22, 13, 2, 37, 12, 36, 59, 13, 35, 51, 8, 8, 8, 8, 99, 12, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 99, 49, 22, 22, 22, 2, 70, 12, 22, 22, 13, 2, 37, 37, 36, 51, 50, 37, 37, 12, 36, 71, 13, 37, 70, 12, 49, 51, 13, 50, 8, 9, 9, 9, 9, 0, 13, 25, 47, 59, 62, 0, 23, 47, 59, 62, 23, 23, 23, 32, 32, 23, 23, 23, 23, 32, 32, 23, 23, 7, 23, 32, 8, 23, 59, 58, 36, 47, 47, 46, 69, 7, 45, 47, 8, 46, 59, 7, 58, 62, 8, 59, 23, 13, 13, 2, 13, 99, 36, 13, 13, 13, 13, 99, 58, 13, 13, 13, 13, 99, 7, 13, 13, 8, 13, 99, 36, 23, 25, 25, 2, 59, 58, 23, 25, 25, 2, 69, 7, 23, 25, 8, 2, 59, 58, 36, 47, 47, 46, 69, 7, 45, 47, 8, 46, 59, 7, 58, 62, 8, 59, 13, 9, 99, 36, 23, 25, 25, 2, 99, 58, 23, 25, 25, 2, 99, 7, 23, 25, 8, 2, 0, 12, 9, 46, 58, 62, 9, 9, 9, 0, 23, 46, 58, 62, 23, 23, 23, 32, 32, 23, 23, 23, 23, 32, 32, 23, 23, 7, 23, 32, 8, 23, 58, 58, 36, 46, 46, 46, 68, 7, 46, 46, 8, 46, 58, 7, 58, 62, 8, 58, 9, 12, 12, 12, 12, 102, 46, 12, 12, 12, 12, 102, 50, 12, 12, 7, 12, 62, 8, 12, 9, 9, 9, 46, 46, 9, 9, 9, 9, 120, 50, 9, 9, 7, 9, 70, 8, 9, 58, 58, 36, 46, 46, 46, 68, 7, 46, 46, 8, 46, 58, 7, 58, 62, 8, 58, 12, 23, 25, 13, 2, 0, 36, 9, 25, 36, 58, 9, 9, 3, 0, 89, 25, 36, 58, 99, 23, 38, 25, 2, 25, 36, 7, 36, 37, 8, 37, 58, 12, 38, 59, 13, 59, 36, 7, 23, 25, 8, 2, 58, 12, 23, 25, 13, 2, 36, 12, 7, 37, 13, 8, 9, 36, 36, 23, 3, 25, 2, 25, 58, 7, 3, 62, 8, 36, 36, 12, 3, 76, 13, 36, 9, 9, 9, 81, 2, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 59, 13, 9, 36, 7, 23, 25, 8, 2, 58, 12, 23, 25, 13, 2, 36, 12, 7, 37, 13, 8, 58, 36, 0, 46, 9, 25, 50, 46, 9, 9, 9, 46, 9, 4, 99, 23, 46, 25, 2, 4, 0, 7, 9, 21, 46, 7, 7, 7, 51, 9, 7, 7, 7, 7, 25, 2, 7, 7, 7, 7, 47, 13, 7, 9, 9, 9, 21, 2, 9, 9, 9, 9, 47, 13, 9, 46, 12, 21, 21, 13, 2, 7, 46, 46, 8, 4, 99, 12, 46, 50, 13, 4, 9, 9, 9, 85, 2, 9, 9, 7, 9, 51, 8, 9, 9, 9, 9, 47, 13, 9, 50, 7, 23, 25, 8, 2, 46, 12, 23, 25, 13, 2, 46, 12, 7, 47, 13, 8, 50, 46, 0, 7, 9, 21, 50, 68, 7, 7, 3, 0, 60, 21, 50, 68, 60, 21, 38, 21, 2, 21, 60, 50, 38, 50, 34, 50, 60, 12, 38, 69, 13, 60, 99, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 68, 12, 50, 50, 13, 34, 9, 7, 7, 7, 3, 25, 2, 7, 7, 7, 3, 0, 50, 9, 21, 68, 9, 9, 9, 50, 9, 6, 99, 21, 50, 21, 2, 6, 68, 12, 50, 50, 13, 6, 9, 9, 9, 21, 2, 9, 9, 9, 9, 69, 13, 9, 68, 12, 21, 21, 13, 2, 50, 7, 7, 7, 3, 76, 13, 7, 9, 9, 9, 21, 2, 9, 9, 9, 9, 50, 34, 9, 9, 9, 9, 69, 13, 9, 99, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 68, 12, 50, 50, 13, 34, 7, 0, 3, 0, 3, 46, 38, 15, 38, 34, 38, 45, 3, 21, 3, 46, 3, 69, 82, 15, 46, 15, 46, 34, 3, 25, 3, 0, 3, 46, 9, 34, 82, 15, 46, 34, 3, 46, 3, 21, 3, 69, 9, 15, 9, 45, 46, 15, 3, 47, 3, 46, 3, 21, 3, 46, 3, 69, 9, 15, 9, 34, 9, 45, 82, 15, 46, 15, 46, 34, 62, 8, 46, 99, 12, 36, 76, 13, 76, 0, 7, 9, 21, 36, 58, 7, 7, 5, 0, 51, 21, 36, 58, 60, 21, 51, 21, 2, 21, 36, 36, 36, 51, 35, 51, 58, 12, 51, 51, 13, 51, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 9, 7, 7, 7, 5, 25, 2, 7, 7, 7, 5, 0, 36, 9, 21, 46, 9, 9, 9, 46, 9, 4, 36, 21, 36, 21, 2, 4, 36, 12, 36, 51, 13, 4, 9, 9, 9, 21, 2, 9, 9, 9, 9, 47, 13, 9, 46, 12, 21, 21, 13, 2, 36, 7, 7, 7, 5, 76, 13, 7, 9, 9, 9, 21, 2, 9, 9, 9, 9, 108, 35, 9, 9, 9, 9, 59, 13, 9, 36, 36, 21, 21, 21, 2, 58, 12, 21, 21, 13, 2, 36, 12, 36, 59, 13, 35, 7, 58, 62, 8, 62, 99, 12, 89, 76, 13, 50, 99, 12, 7, 62, 13, 8], [0, 9, 28, 9, 117, 9, 119, 9, 67, 9, 80, 64, 11, 64, 11, 64, 11, 0, 7, 67, 7, 25, 7, 67, 7, 67, 7, 67, 9, 21, 9, 113, 9, 50, 9, 69, 36, 21, 99, 21, 68, 21, 36, 50, 36, 69, 68, 50, 11, 64, 11, 99, 25, 99, 25, 64, 25, 79, 25, 111, 117, 64, 62, 79, 76, 64, 62, 79, 76, 64, 62], [9], [0, 10, 28, 110, 118, 61, 77, 0, 28, 110, 118, 61, 77, 99, 36, 23, 28, 28, 26, 99, 53, 23, 28, 28, 26, 61, 7, 23, 28, 8, 26, 77, 12, 23, 28, 13, 26, 110, 53, 36, 116, 50, 40, 61, 7, 39, 63, 8, 40, 77, 12, 36, 78, 13, 40, 61, 7, 53, 63, 8, 54, 77, 12, 53, 78, 13, 50, 61, 12, 7, 63, 13, 8, 28, 10, 10, 2, 10, 0, 36, 28, 106, 36, 77, 36, 24, 3, 28, 2, 28, 36, 36, 3, 116, 50, 36, 61, 7, 3, 63, 8, 36, 36, 12, 3, 78, 13, 36, 100, 53, 24, 28, 28, 2, 36, 7, 24, 28, 8, 2, 77, 12, 24, 28, 13, 2, 36, 7, 36, 37, 8, 34, 77, 12, 53, 78, 13, 34, 36, 12, 7, 37, 13, 8, 36, 10, 10, 10, 10, 0, 58, 28, 108, 61, 58, 58, 24, 5, 28, 2, 28, 58, 36, 5, 116, 40, 54, 58, 7, 5, 63, 8, 54, 77, 12, 5, 78, 13, 54, 100, 36, 24, 28, 28, 2, 61, 7, 24, 28, 8, 2, 58, 12, 24, 28, 13, 2, 61, 7, 39, 63, 8, 35, 58, 12, 36, 59, 13, 35, 58, 12, 7, 59, 13, 8, 58, 10, 10, 10, 10, 0, 7, 21, 36, 50, 68, 7, 7, 7, 28, 2, 7, 7, 7, 7, 63, 36, 7, 7, 7, 7, 63, 50, 7, 7, 7, 7, 63, 13, 7, 36, 36, 21, 21, 21, 2, 100, 50, 21, 21, 21, 2, 68, 12, 21, 21, 13, 2, 36, 36, 36, 50, 50, 36, 36, 12, 36, 69, 13, 36, 68, 12, 50, 50, 13, 50, 7, 10, 10, 8, 10, 0, 12, 28, 46, 58, 61, 12, 12, 12, 28, 2, 12, 12, 12, 12, 78, 40, 12, 12, 12, 12, 78, 50, 12, 12, 7, 12, 63, 8, 12, 99, 36, 24, 28, 28, 2, 58, 53, 24, 28, 28, 2, 61, 7, 24, 28, 8, 2, 58, 53, 36, 46, 46, 40, 61, 7, 39, 46, 8, 40, 58, 7, 53, 63, 8, 54, 12, 10, 10, 10, 10, 100, 36, 24, 28, 28, 2, 100, 53, 24, 28, 28, 2, 61, 7, 24, 28, 8, 2, 77, 12, 24, 28, 13, 2, 110, 53, 36, 116, 50, 40, 61, 7, 39, 63, 8, 40, 77, 12, 36, 78, 13, 40, 61, 7, 53, 63, 8, 54, 77, 12, 53, 78, 13, 50, 61, 12, 7, 63, 13, 8], [11]]
def rootCodes8 : List (List Nat) := [[10], [0, 9, 25, 46, 58, 62, 73, 9, 9, 9, 0, 2, 46, 58, 21, 28, 0, 23, 58, 21, 28, 23, 18, 3, 85, 19, 16, 21, 7, 3, 22, 8, 16, 23, 23, 3, 28, 11, 16, 21, 7, 18, 22, 8, 19, 58, 28, 18, 28, 11, 19, 21, 21, 7, 22, 11, 8, 36, 2, 2, 2, 2, 58, 58, 2, 2, 2, 2, 68, 7, 2, 2, 2, 2, 125, 28, 2, 2, 2, 2, 58, 18, 15, 46, 19, 16, 21, 7, 15, 22, 8, 16, 81, 28, 15, 28, 11, 16, 21, 7, 18, 22, 8, 19, 58, 28, 18, 28, 11, 19, 21, 21, 7, 22, 11, 8, 2, 9, 9, 9, 9, 0, 46, 25, 58, 62, 73, 0, 23, 58, 62, 73, 23, 23, 23, 85, 50, 16, 23, 7, 23, 62, 8, 16, 23, 23, 23, 73, 11, 16, 58, 7, 35, 62, 8, 58, 58, 58, 35, 73, 11, 50, 68, 68, 7, 62, 11, 8, 23, 46, 25, 2, 4, 58, 58, 46, 46, 46, 4, 68, 7, 46, 46, 8, 4, 125, 72, 46, 46, 11, 4, 58, 35, 23, 25, 25, 2, 68, 7, 23, 25, 8, 2, 103, 72, 23, 25, 11, 2, 58, 7, 35, 62, 8, 58, 58, 58, 35, 73, 11, 50, 68, 68, 7, 62, 11, 8, 46, 9, 9, 9, 9, 0, 50, 25, 46, 50, 73, 58, 23, 50, 25, 2, 6, 58, 36, 50, 46, 46, 6, 58, 7, 50, 62, 8, 6, 58, 58, 50, 50, 11, 6, 103, 34, 23, 25, 25, 2, 50, 7, 23, 25, 8, 2, 103, 72, 23, 25, 11, 2, 50, 7, 34, 46, 8, 46, 106, 72, 34, 46, 11, 46, 50, 50, 7, 51, 11, 8, 50, 9, 9, 7, 9, 0, 8, 22, 37, 51, 67, 68, 22, 8, 8, 2, 8, 68, 36, 8, 8, 8, 8, 58, 51, 8, 8, 8, 8, 68, 67, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 58, 49, 22, 22, 22, 2, 103, 66, 22, 22, 11, 2, 37, 37, 36, 46, 46, 37, 37, 37, 36, 46, 11, 37, 58, 58, 49, 51, 11, 50, 8, 9, 9, 9, 9, 0, 11, 25, 46, 58, 62, 125, 23, 11, 11, 2, 11, 125, 36, 11, 11, 11, 11, 58, 58, 11, 11, 11, 11, 68, 7, 11, 11, 8, 11, 103, 36, 23, 25, 25, 2, 58, 55, 23, 25, 25, 2, 65, 7, 23, 25, 8, 2, 58, 55, 36, 46, 46, 43, 65, 7, 42, 46, 8, 43, 58, 7, 55, 62, 8, 57, 11, 9, 0, 23, 9, 58, 36, 73, 9, 9, 3, 0, 23, 58, 36, 73, 23, 23, 23, 78, 34, 16, 23, 7, 23, 37, 8, 16, 23, 23, 23, 73, 11, 16, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 9, 23, 23, 23, 3, 85, 50, 23, 23, 7, 3, 62, 8, 23, 23, 23, 3, 73, 11, 23, 9, 9, 9, 103, 34, 9, 9, 7, 9, 37, 8, 9, 9, 9, 9, 103, 11, 9, 36, 7, 36, 37, 8, 34, 58, 58, 58, 73, 11, 34, 36, 36, 7, 37, 11, 8, 36, 23, 25, 25, 2, 58, 58, 23, 25, 25, 2, 68, 7, 23, 25, 8, 2, 125, 72, 23, 25, 11, 2, 58, 58, 36, 46, 46, 46, 68, 7, 46, 46, 8, 46, 125, 72, 36, 46, 11, 46, 58, 7, 58, 62, 8, 58, 58, 58, 58, 73, 11, 50, 68, 68, 7, 62, 11, 8], [12], [9], [0, 10, 32, 47, 59, 61, 80, 0, 32, 47, 59, 61, 80, 110, 36, 23, 32, 32, 26, 59, 53, 23, 32, 32, 26, 61, 7, 23, 32, 8, 26, 127, 74, 23, 32, 11, 26, 59, 53, 36, 47, 47, 40, 61, 7, 39, 47, 8, 40, 110, 74, 36, 47, 11, 40, 59, 7, 53, 63, 8, 54, 59, 59, 53, 80, 11, 50, 61, 61, 7, 63, 11, 8, 32, 10, 10, 2, 10, 0, 36, 32, 59, 36, 80, 36, 24, 3, 32, 2, 32, 36, 36, 3, 47, 47, 36, 61, 7, 3, 47, 8, 36, 36, 36, 3, 47, 11, 36, 59, 53, 24, 32, 32, 2, 36, 7, 24, 32, 8, 2, 99, 74, 24, 32, 11, 2, 36, 7, 36, 37, 8, 34, 59, 59, 53, 80, 11, 34, 36, 36, 7, 37, 11, 8, 36, 10, 10, 10, 10, 0, 58, 32, 47, 61, 80, 58, 24, 5, 32, 2, 32, 58, 36, 5, 47, 40, 47, 58, 7, 5, 63, 8, 54, 58, 58, 5, 80, 11, 54, 99, 36, 24, 32, 32, 2, 61, 7, 24, 32, 8, 2, 99, 74, 24, 32, 11, 2, 61, 7, 39, 47, 8, 35, 110, 74, 36, 47, 11, 35, 61, 61, 7, 63, 11, 8, 58, 10, 10, 10, 10, 0, 7, 21, 36, 50, 65, 7, 7, 7, 32, 2, 7, 7, 7, 7, 47, 36, 7, 7, 7, 7, 63, 50, 7, 7, 7, 7, 63, 11, 7, 36, 36, 21, 21, 21, 2, 59, 50, 21, 21, 21, 2, 99, 64, 21, 21, 11, 2, 36, 36, 36, 47, 47, 36, 36, 36, 36, 47, 11, 36, 59, 59, 50, 50, 11, 50, 7, 10, 10, 8, 10, 0, 80, 32, 47, 59, 61, 125, 24, 64, 32, 2, 32, 99, 36, 64, 47, 40, 47, 59, 53, 59, 80, 50, 75, 61, 7, 61, 63, 8, 63, 99, 36, 24, 32, 32, 2, 59, 53, 24, 32, 32, 2, 61, 7, 24, 32, 8, 2, 59, 53, 36, 47, 47, 40, 61, 7, 39, 47, 8, 40, 59, 7, 53, 63, 8, 54, 80, 10, 10, 10, 10, 110, 36, 24, 32, 32, 2, 59, 53, 24, 32, 32, 2, 61, 7, 24, 32, 8, 2, 127, 74, 24, 32, 11, 2, 59, 53, 36, 47, 47, 40, 61, 7, 39, 47, 8, 40, 110, 74, 36, 47, 11, 40, 59, 7, 53, 63, 8, 54, 59, 59, 53, 80, 11, 50, 61, 61, 7, 63, 11, 8], [13], [10], [0, 12, 31, 46, 58, 68, 77, 12, 12, 12, 0, 2, 46, 58, 21, 25, 99, 36, 2, 2, 2, 2, 58, 58, 2, 2, 2, 2, 68, 7, 2, 2, 2, 2, 125, 9, 2, 2, 2, 2, 58, 18, 15, 46, 19, 16, 21, 7, 15, 22, 8, 16, 25, 9, 15, 46, 10, 16, 21, 7, 18, 22, 8, 19, 25, 9, 18, 77, 10, 19, 21, 9, 7, 22, 10, 8, 2, 12, 12, 12, 12, 0, 46, 31, 58, 68, 77, 99, 29, 46, 31, 2, 4, 58, 58, 46, 46, 46, 4, 68, 7, 46, 46, 8, 4, 99, 9, 46, 46, 10, 4, 58, 35, 29, 31, 31, 2, 68, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 58, 7, 35, 70, 8, 58, 58, 9, 35, 77, 10, 50, 68, 9, 7, 70, 10, 8, 46, 12, 12, 12, 12, 0, 50, 31, 46, 50, 77, 58, 29, 50, 31, 2, 6, 58, 36, 50, 46, 46, 6, 58, 7, 50, 70, 8, 6, 58, 9, 50, 50, 10, 6, 99, 34, 29, 31, 31, 2, 50, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 50, 7, 34, 46, 8, 46, 99, 9, 34, 46, 10, 46, 50, 9, 7, 51, 10, 8, 50, 12, 12, 7, 12, 0, 8, 22, 37, 51, 62, 68, 22, 8, 8, 2, 8, 68, 36, 8, 8, 8, 8, 58, 51, 8, 8, 8, 8, 68, 9, 8, 8, 8, 8, 37, 36, 22, 22, 22, 2, 58, 49, 22, 22, 22, 2, 62, 9, 22, 22, 10, 2, 37, 37, 36, 46, 46, 37, 37, 9, 36, 46, 10, 37, 58, 9, 49, 51, 10, 50, 8, 12, 12, 9, 12, 0, 10, 31, 46, 58, 61, 125, 29, 10, 10, 2, 10, 99, 36, 10, 10, 10, 10, 58, 58, 10, 10, 10, 10, 68, 7, 10, 10, 8, 10, 99, 36, 24, 31, 31, 2, 58, 53, 24, 31, 31, 2, 61, 7, 24, 31, 8, 2, 58, 53, 36, 46, 46, 40, 61, 7, 39, 46, 8, 40, 58, 7, 53, 63, 8, 54, 10, 12, 99, 36, 29, 31, 31, 2, 58, 58, 29, 31, 31, 2, 68, 7, 29, 31, 8, 2, 125, 9, 29, 31, 10, 2, 58, 58, 36, 46, 46, 46, 68, 7, 46, 46, 8, 46, 99, 9, 36, 46, 10, 46, 58, 7, 58, 70, 8, 58, 58, 9, 58, 77, 10, 50, 68, 9, 7, 70, 10, 8], [12], [125], [0, 11, 28, 47, 59, 65, 73, 0, 28, 47, 59, 65, 73, 99, 36, 23, 28, 28, 28, 59, 55, 23, 28, 28, 28, 65, 7, 23, 28, 8, 28, 73, 9, 28, 28, 10, 28, 59, 55, 36, 47, 47, 43, 65, 7, 42, 47, 8, 43, 73, 9, 36, 47, 10, 43, 59, 7, 55, 67, 8, 57, 59, 9, 55, 78, 10, 50, 65, 9, 7, 67, 10, 8, 28, 11, 11, 2, 11, 0, 36, 28, 59, 36, 73, 36, 28, 3, 28, 2, 28, 36, 36, 3, 47, 47, 36, 65, 7, 3, 47, 8, 36, 36, 9, 3, 47, 10, 36, 59, 55, 28, 28, 28, 2, 36, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 36, 7, 36, 37, 8, 34, 59, 9, 55, 78, 10, 34, 36, 9, 7, 37, 10, 8, 36, 11, 11, 11, 11, 0, 58, 28, 47, 65, 73, 58, 28, 5, 28, 2, 28, 58, 36, 5, 47, 43, 47, 58, 7, 5, 67, 8, 57, 58, 9, 5, 78, 10, 57, 101, 36, 28, 28, 28, 2, 65, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 65, 7, 42, 47, 8, 35, 73, 9, 36, 47, 10, 35, 65, 9, 7, 67, 10, 8, 58, 11, 11, 11, 11, 0, 7, 21, 36, 50, 61, 7, 7, 7, 28, 2, 7, 7, 7, 7, 47, 36, 7, 7, 7, 7, 67, 50, 7, 7, 7, 7, 67, 10, 7, 36, 36, 21, 21, 21, 2, 59, 50, 21, 21, 21, 2, 73, 9, 21, 21, 10, 2, 36, 36, 36, 47, 47, 36, 36, 9, 36, 47, 10, 36, 59, 9, 50, 50, 10, 50, 7, 11, 11, 8, 11, 0, 9, 25, 47, 59, 62, 9, 9, 9, 28, 2, 9, 9, 9, 9, 47, 43, 9, 9, 9, 9, 78, 50, 9, 9, 7, 9, 67, 8, 9, 99, 36, 23, 25, 25, 2, 59, 55, 23, 25, 25, 2, 65, 7, 23, 25, 8, 2, 59, 55, 36, 47, 47, 43, 65, 7, 42, 47, 8, 43, 59, 7, 55, 62, 8, 57, 9, 11, 11, 10, 11, 101, 36, 28, 28, 28, 2, 59, 55, 28, 28, 28, 2, 65, 7, 28, 28, 8, 2, 73, 9, 28, 28, 10, 2, 59, 55, 36, 47, 47, 43, 65, 7, 42, 47, 8, 43, 73, 9, 36, 47, 10, 43, 59, 7, 55, 67, 8, 57, 59, 9, 55, 78, 10, 50, 65, 9, 7, 67, 10, 8], [13], [11]]

def rootCodes : List (List Nat) :=
  rootCodes0 ++ rootCodes1 ++ rootCodes2 ++ rootCodes3 ++ rootCodes4 ++
  rootCodes5 ++ rootCodes6 ++ rootCodes7 ++ rootCodes8

def rootPairs : List ((List Sig × (Sig × Option Sig)) × List Nat) :=
  (genChildren 7 inputs).zip rootCodes

def checkPair (p : (List Sig × (Sig × Option Sig)) × List Nat) : Bool :=
  (checkStream 6 p.1.1 [p.1.2] p.2).isSome

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_len : (genChildren 7 inputs).length = rootCodes.length := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_not : !(inputs.contains target) = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_0 : (rootPairs.take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_1 : ((rootPairs.drop 15).take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_2 : ((rootPairs.drop 30).take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_3 : ((rootPairs.drop 45).take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_4 : ((rootPairs.drop 60).take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_5 : ((rootPairs.drop 75).take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_6 : ((rootPairs.drop 90).take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_7 : ((rootPairs.drop 105).take 15).all checkPair = true := by decide +kernel
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16384 in
theorem chk_8 : (rootPairs.drop 120).all checkPair = true := by decide +kernel

theorem all_of_chunks {α : Type} {p : α → Bool} {l : List α}
    (h0 : (l.take 15).all p = true)
    (h1 : ((l.drop 15).take 15).all p = true)
    (h2 : ((l.drop 30).take 15).all p = true)
    (h3 : ((l.drop 45).take 15).all p = true)
    (h4 : ((l.drop 60).take 15).all p = true)
    (h5 : ((l.drop 75).take 15).all p = true)
    (h6 : ((l.drop 90).take 15).all p = true)
    (h7 : ((l.drop 105).take 15).all p = true)
    (h8 : (l.drop 120).all p = true) : l.all p = true := by
  have step : ∀ (xs : List α), (xs.take 15).all p = true →
      (xs.drop 15).all p = true → xs.all p = true := by
    intro xs ht hd
    rw [← List.take_append_drop 15 xs, List.all_append, ht, hd]; rfl
  have d7 : (l.drop 105).all p = true := by
    refine step (l.drop 105) h7 ?_
    simpa [List.drop_drop] using h8
  have d6 : (l.drop 90).all p = true := by
    refine step (l.drop 90) h6 ?_
    simpa [List.drop_drop] using d7
  have d5 : (l.drop 75).all p = true := by
    refine step (l.drop 75) h5 ?_
    simpa [List.drop_drop] using d6
  have d4 : (l.drop 60).all p = true := by
    refine step (l.drop 60) h4 ?_
    simpa [List.drop_drop] using d5
  have d3 : (l.drop 45).all p = true := by
    refine step (l.drop 45) h3 ?_
    simpa [List.drop_drop] using d4
  have d2 : (l.drop 30).all p = true := by
    refine step (l.drop 30) h2 ?_
    simpa [List.drop_drop] using d3
  have d1 : (l.drop 15).all p = true := by
    refine step (l.drop 15) h1 ?_
    simpa [List.drop_drop] using d2
  exact step l h0 d1

private theorem check_zip_pair {cs : List (List Sig × (Sig × Option Sig))} {ks : List (List Nat)}
    (hlen : cs.length = ks.length)
    (hall : (cs.zip ks).all checkPair = true) :
    ∀ ch ∈ cs, ∃ c r, checkStream 6 ch.1 [ch.2] c = some r := by
  induction cs generalizing ks with
  | nil => intro _ hm; simp at hm
  | cons ch cs ih =>
    cases ks with
    | nil => simp at hlen
    | cons k ks =>
      simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true, checkPair, Option.isSome_iff_exists] at hall
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx'
      · obtain ⟨r, hr⟩ := hall.1
        exact ⟨k, r, hr⟩
      · exact ih (by simp at hlen; omega) hall.2 x hx'

theorem impossible_root : Impossible target 7 inputs.toFinset := by
  have hnot : target ∉ inputs := by simpa [List.contains_eq_mem] using chk_not
  have hv : ValidState inputs [] := validState_init
  have hnd : inputs.Nodup := hv.1
  have hkids := check_zip_pair chk_len (all_of_chunks chk_0 chk_1 chk_2 chk_3 chk_4 chk_5 chk_6 chk_7 chk_8)
  refine enum_step hnd hnot ?_ ?_
  · intro a ha keep hna hpa hl
    have hmem := mem_oneKids ha hpa hna hl
    obtain ⟨c, r, htok⟩ := hkids _ hmem
    exact checkStream_sound 6 _ _ c r htok (validState_one hv ha hpa hna)
  · intro a ha b hb d ka kb hab hnab hpab hl
    rcases mem_twoKidsAux_ordered inputs hnd (fun _ h => h) hnd ha hb hab hpab hnab hl with h | h
    · obtain ⟨c, r, htok⟩ := hkids _ (List.mem_append_right _ h)
      exact checkStream_sound 6 _ _ c r htok (validState_two hv ha hb hab hpab hnab)
    · obtain ⟨c, r, htok⟩ := hkids _ (List.mem_append_right _ h)
      have hnd1 := childTwo_nodup hnd ha hb hab d hnab ka kb
      have hnd2 := childTwo_nodup hnd hb ha hab.symm d (bin_comm d b a ▸ hnab) kb ka
      have hl' : (childTwo inputs b a d kb ka).length ≤ 7 := by
        rw [← List.toFinset_card_of_nodup hnd2, childTwo_swap_fin hnd, List.toFinset_card_of_nodup hnd1]
        exact hl
      have himp := checkStream_sound 6 _ _ c r htok
        (validState_two hv hb ha hab.symm (bin_comm d b a ▸ hpab) (bin_comm d b a ▸ hnab))
      simpa only [childTwo_swap_fin hnd] using himp

def proj (r : Row) : Fin 9 → Bool := fun i =>
  match i.val with
  | 0 => false
  | 1 => r.val.testBit 0
  | 2 => r.val.testBit 1
  | 3 => r.val.testBit 2
  | 4 => r.val.testBit 3
  | 5 => r.val.testBit 4
  | 6 => r.val.testBit 5
  | 7 => true
  | _ => r.val.testBit 6

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def in9 : List Sig :=
  [zero, inputs.getD 0 zero, inputs.getD 1 zero, inputs.getD 2 zero,
   inputs.getD 3 zero, inputs.getD 4 zero, inputs.getD 5 zero, one, inputs.getD 6 zero]

def w2 : List Sig := in9 ++ [zero, one]

theorem gate0_val : gv in9 ⟨GateOp.and, [0, 4]⟩ = zero := by decide +kernel
theorem gate1_val : gv (in9 ++ [zero]) ⟨GateOp.or, [2, 7]⟩ = one := by decide +kernel
def pm3Row (r : Nat) : Bool :=
  pm3 fun i =>
    match i.val with
    | 0 => false
    | 1 => r.testBit 0
    | 2 => r.testBit 1
    | 3 => r.testBit 2
    | 4 => r.testBit 3
    | 5 => r.testBit 4
    | 6 => r.testBit 5
    | 7 => true
    | _ => r.testBit 6

private theorem target_eq_chk :
    checkRange (fun r => target.getLsbD r == pm3Row r) 128 = true := by decide +kernel

theorem target_eq : ∀ r : Row, bit r target = pm3 (proj r) := by
  intro r
  exact beq_iff_eq.mp (checkRange_sound target_eq_chk r.val r.isLt)

theorem in9_eq : ∀ (r : Row) (j : Fin 9), (in9.map (bit r)).getD j.val false = proj r j := by
  intro r ⟨j, hj⟩
  rw [b_read]
  match j with
  | 0 => simp [in9, proj, bit_zero]
  | 1 => simpa [in9, proj] using inputs_bit ⟨0, by decide⟩ r
  | 2 => simpa [in9, proj] using inputs_bit ⟨1, by decide⟩ r
  | 3 => simpa [in9, proj] using inputs_bit ⟨2, by decide⟩ r
  | 4 => simpa [in9, proj] using inputs_bit ⟨3, by decide⟩ r
  | 5 => simpa [in9, proj] using inputs_bit ⟨4, by decide⟩ r
  | 6 => simpa [in9, proj] using inputs_bit ⟨5, by decide⟩ r
  | 7 => simp [in9, proj, bit_one]
  | 8 => simpa [in9, proj] using inputs_bit ⟨6, by decide⟩ r
  | _ + 9 => omega

theorem rootEss_ok : checkEssential target inputs rootEss = true := by decide +kernel
private theorem rootEss_mem_chk :
    inputs.all (fun x => (rootEss.map Prod.fst).contains x) = true := by decide +kernel

theorem rootEss_mem : ∀ x ∈ inputs, x ∈ (rootEss.map Prod.fst).toFinset := by
  intro x hx
  exact List.mem_toFinset.mpr (by simpa [List.contains_eq_mem] using List.all_eq_true.mp rootEss_mem_chk x hx)

theorem w2_mem : ∀ a ∈ w2, a ∈ inputs ∨ ¬proper a := by
  intro a ha
  simp only [w2, in9, List.append_assoc, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_nil_iff, or_false] at ha
  have hmem : ∀ i, i < 7 → inputs.getD i zero ∈ inputs := by
    intro i hi
    simp only [List.getD_eq_getElem?_getD]
    have hl : inputs.length = 7 := by decide
    cases h : inputs[i]? with
    | none => simp [List.getElem?_eq_none_iff, hl] at h; omega
    | some v => exact List.mem_of_getElem? h
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (fun h => h.1 rfl)
  · exact Or.inl (hmem 0 (by decide))
  · exact Or.inl (hmem 1 (by decide))
  · exact Or.inl (hmem 2 (by decide))
  · exact Or.inl (hmem 3 (by decide))
  · exact Or.inl (hmem 4 (by decide))
  · exact Or.inl (hmem 5 (by decide))
  · exact Or.inr (fun h => h.2 rfl)
  · exact Or.inl (hmem 6 (by decide))
  · exact Or.inr (fun h => h.1 rfl)
  · exact Or.inr (fun h => h.2 rfl)

theorem final (h : ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩) : False := by
  obtain ⟨C, hfan, hsize, hcomp, hout, hnf, _, huse, hhead, htail⟩ := h
  rcases hgs : C.gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp [hgs] at hhead
  · simp [hgs] at htail
  · simp only [hgs, List.head?_cons, Option.some.injEq] at hhead
    simp only [hgs, List.tail_cons, List.head?_cons, Option.some.injEq] at htail
    subst g0; subst g1
    have hclen : C.gates.length = rest.length + 2 := by simp [hgs]
    have hrest_le : rest.length ≤ 9 := by
      simp only [Circuit.size, hgs, List.length_cons] at hsize; omega
    have hrest_ne : rest ≠ [] := by
      intro hnil
      have hc : C.gates = [⟨GateOp.and, [0, 4]⟩, ⟨GateOp.or, [2, 7]⟩] := by simp [hgs, hnil]
      have ho : C.output = 10 := by simp [Circuit.size, hc] at hout; omega
      have hev := hcomp (fun i => decide (i.val = 2))
      have hev1 : C.eval (List.ofFn fun i : Fin 9 => decide (i.val = 2)) = true := by
        simp [Circuit.eval, Circuit.wires, hc, ho, GateOp.eval]
      have hev2 : pm3 (fun i : Fin 9 => decide (i.val = 2)) = false := by decide
      rw [hev1, hev2] at hev; cases hev
    have hrest_pos : 0 < rest.length := List.length_pos_of_ne_nil hrest_ne
    have hnf_rest : ∀ g ∈ rest, GateNF g := by
      intro g hg
      obtain ⟨j, _, rfl⟩ := List.mem_iff_get.mp hg
      have hj' : j.val + 2 < C.gates.length := by rw [hclen]; omega
      have hget : C.gates.get ⟨j.val + 2, hj'⟩ = rest.get j := by simp [hgs]
      rcases hnf ⟨j.val + 2, hj'⟩ with ⟨hop, _, _, hi⟩ | ⟨hop, _, _, _, _, hi⟩
      · left; refine ⟨by rw [← hget]; exact hop, by rw [← hget, hi]; rfl⟩
      · right; refine ⟨by rw [← hget]; exact hop, by rw [← hget, hi]; rfl⟩
    have hlegal_all : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hfan
    have hexec_out : (execute rest w2).getD C.output zero = target := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      let r : Row := ⟨j, hj⟩
      have h0 : execute C.gates in9 = execute rest w2 := by
        simp only [hgs, execute, List.foldl_cons]
        rw [gate0_val, gate1_val]; rfl
      have hbits := execute_bits C.gates r in9 (fun g hg => (hlegal_all g hg).1)
      have hget : bit r ((execute C.gates in9).getD C.output zero) =
          ((execute C.gates in9).map (bit r)).getD C.output false := (b_read r _ _).symm
      have hin9 : in9.map (bit r) = List.ofFn (proj r) := by
        simp only [in9, List.map_cons, List.map_nil, bit_zero, bit_one,
          inputs_bit ⟨0, by decide⟩ r, inputs_bit ⟨1, by decide⟩ r, inputs_bit ⟨2, by decide⟩ r,
          inputs_bit ⟨3, by decide⟩ r, inputs_bit ⟨4, by decide⟩ r, inputs_bit ⟨5, by decide⟩ r,
          inputs_bit ⟨6, by decide⟩ r]
        rfl
      rw [← h0]
      change bit r ((execute C.gates in9).getD C.output zero) = bit r target
      rw [hget, hbits, hin9, target_eq]
      exact hcomp (proj r)
    have ht_mem : target ∈ execute rest w2 := by
      have hr := get_rep (execute rest w2) C.output
      rw [hexec_out] at hr
      exact hr.resolve_right (fun hn => hn target_proper)
    have hlen_c : 2 < C.gates.length := by rw [hclen]; omega
    obtain ⟨k0, hk0_gt, hk0_in⟩ := huse ⟨0, by omega⟩ (by dsimp; omega)
    obtain ⟨k1, hk1_gt, hk1_in⟩ := huse ⟨1, by omega⟩ (by dsimp; omega)
    have hk0_gt' : 0 < k0.val := hk0_gt
    have hk1_gt' : 1 < k1.val := hk1_gt
    have hk0_ge2 : 2 ≤ k0.val := by
      by_contra hlt
      have hk0_eq : k0.val = 1 := by omega
      have hget1 : C.gates.get k0 = ⟨GateOp.or, [2, 7]⟩ := by
        have : k0 = ⟨1, by omega⟩ := Fin.ext hk0_eq
        rw [this]; simp [hgs]
      rw [hget1] at hk0_in; simp at hk0_in
    have hk1_ge2 : 2 ≤ k1.val := by omega
    have hw2_len : w2.length = 11 := by simp [w2, in9]
    have h9_np : ∀ t, ¬proper ((execute (rest.take t) w2).getD 9 zero) := by
      intro t
      rw [execute_getD_lt _ _ 9 (by omega)]
      have : w2.getD 9 zero = zero := by decide
      rw [this]; exact fun hh => hh.1 rfl
    have h10_np : ∀ t, ¬proper ((execute (rest.take t) w2).getD 10 zero) := by
      intro t
      rw [execute_getD_lt _ _ 10 (by omega)]
      have : w2.getD 10 zero = one := by decide
      rw [this]; exact fun hh => hh.2 rfl
    have hrest_get : ∀ t (ht : t < rest.length), C.gates.get ⟨t + 2, by rw [hclen]; omega⟩ = rest.get ⟨t, ht⟩ := by
      intro t ht; simp [hgs]
    have h2np : 2 ≤ nonPropCount w2 rest := by
      obtain ⟨i0, hi0_eq⟩ : ∃ i0, k0.val = i0 + 2 := ⟨k0.val - 2, by omega⟩
      obtain ⟨i1, hi1_eq⟩ : ∃ i1, k1.val = i1 + 2 := ⟨k1.val - 2, by omega⟩
      have hi0_lt : i0 < rest.length := by have := k0.isLt; omega
      have hi1_lt : i1 < rest.length := by have := k1.isLt; omega
      have hk0_fin : (⟨i0 + 2, by rw [hclen]; omega⟩ : Fin C.gates.length) = k0 := Fin.ext (by simp [hi0_eq])
      have hk1_fin : (⟨i1 + 2, by rw [hclen]; omega⟩ : Fin C.gates.length) = k1 := Fin.ext (by simp [hi1_eq])
      have hi0_in : 9 ∈ (rest.get ⟨i0, hi0_lt⟩).inputs := by
        rw [← hrest_get i0 hi0_lt, hk0_fin]; exact hk0_in
      have hi1_in : 10 ∈ (rest.get ⟨i1, hi1_lt⟩).inputs := by
        rw [← hrest_get i1 hi1_lt, hk1_fin]; exact hk1_in
      by_cases heq : i0 = i1
      · have hi1_in' : 10 ∈ (rest.get ⟨i0, hi0_lt⟩).inputs := by
          have hfin_eq : (⟨i0, hi0_lt⟩ : Fin rest.length) = ⟨i1, hi1_lt⟩ := Fin.ext heq
          rw [hfin_eq]; exact hi1_in
        have hk0_nf := hnf k0
        have hboth : (rest.get ⟨i0, hi0_lt⟩).op = GateOp.and ∨ (rest.get ⟨i0, hi0_lt⟩).op = GateOp.or := by
          rcases hk0_nf with ⟨_, _, _, hlen1⟩ | ⟨ho, _⟩
          · rw [← hrest_get i0 hi0_lt, hk0_fin, hlen1] at hi0_in hi1_in'
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi0_in hi1_in'; omega
          · rw [← hrest_get i0 hi0_lt, hk0_fin]; exact ho
        have hinputs : (rest.get ⟨i0, hi0_lt⟩).inputs = [9, 10] := by
          rcases hk0_nf with ⟨_, _, _, hlen1⟩ | ⟨_, a, b, hab, _, hlen2⟩
          · rw [← hrest_get i0 hi0_lt, hk0_fin, hlen1] at hi0_in hi1_in'
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi0_in hi1_in'; omega
          · rw [← hrest_get i0 hi0_lt, hk0_fin, hlen2] at hi0_in hi1_in' ⊢
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi0_in hi1_in'
            rcases hi0_in with h9a | h9b <;> rcases hi1_in' with h10a | h10b
            · omega
            · subst h9a; subst h10b; rfl
            · omega
            · omega
        have hout_np : ¬proper ((execute rest w2).getD (9 + k0.val) zero) := by
          have heq_idx : 9 + k0.val = w2.length + i0 := by omega
          rw [heq_idx, execute_getD_gate rest w2 i0 hi0_lt]
          exact gate_both_collapsed _ _ hboth 9 10 hinputs (h9_np i0) (h10_np i0)
        have hk0_not_last : k0.val + 1 < C.gates.length := by
          by_contra hge
          have hk0_last : k0.val + 1 = C.gates.length := by have := k0.isLt; omega
          have hco : C.output = 9 + k0.val := by simp [Circuit.size] at hout; omega
          rw [hco] at hexec_out
          exact hout_np (hexec_out.symm ▸ target_proper)
        obtain ⟨k2, hk2_gt, hk2_in⟩ := huse k0 hk0_not_last
        have hk2_gt' : k0.val < k2.val := hk2_gt
        obtain ⟨i2, hi2_eq⟩ : ∃ i2, k2.val = i2 + 2 := ⟨k2.val - 2, by omega⟩
        have hi2_lt : i2 < rest.length := by have := k2.isLt; omega
        have hi02 : i0 < i2 := by omega
        have hk2_fin : (⟨i2 + 2, by rw [hclen]; omega⟩ : Fin C.gates.length) = k2 := Fin.ext (by simp [hi2_eq])
        have hi2_in : 9 + k0.val ∈ (rest.get ⟨i2, hi2_lt⟩).inputs := by
          rw [← hrest_get i2 hi2_lt, hk2_fin]; exact hk2_in
        have hi2_np : ¬proper ((execute (rest.take i2) w2).getD (9 + k0.val) zero) := by
          have heq_idx : 9 + k0.val = w2.length + i0 := by omega
          have hi0_take : i0 < (rest.take i2).length := by simp [List.length_take]; omega
          rw [heq_idx, execute_getD_gate (rest.take i2) w2 i0 hi0_take]
          have htake_get : (rest.take i2).get ⟨i0, hi0_take⟩ = rest.get ⟨i0, hi0_lt⟩ := by
            simp [List.get_eq_getElem]
          have htake_take : (rest.take i2).take i0 = rest.take i0 := by
            rw [List.take_take, Nat.min_eq_left (by omega)]
          rw [htake_get, htake_take]
          exact gate_both_collapsed _ _ hboth 9 10 hinputs (h9_np i0) (h10_np i0)
        exact nonPropCount_two w2 rest i0 i2 hi02 hi2_lt ⟨9, hi0_in, h9_np i0⟩ ⟨9 + k0.val, hi2_in, hi2_np⟩
      · by_cases hlt : i0 < i1
        · exact nonPropCount_two w2 rest i0 i1 hlt hi1_lt ⟨9, hi0_in, h9_np i0⟩ ⟨10, hi1_in, h10_np i1⟩
        · exact nonPropCount_two w2 rest i1 i0 (by omega) hi0_lt ⟨10, hi1_in, h10_np i1⟩ ⟨9, hi0_in, h9_np i0⟩
    obtain ⟨k, t, S, hk_le, hlive, hsub⟩ := extract_count target rest w2 hnf_rest target_proper ht_mem
    have hk7 : k ≤ 7 := by omega
    have hS_sub : ∀ a ∈ S, a ∈ inputs := fun a ha =>
      (w2_mem a (hsub a ha)).resolve_right (fun hn => hn (live_proper hlive a ha))
    have hS_eq : S = inputs.toFinset := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨hS_sub a, fun ha => ?_⟩
      obtain ⟨r, s, hd, hiso⟩ := essential_ok rootEss_ok a (rootEss_mem a ha)
      exact raw_required hlive inputs a hS_sub r s hd hiso
    exact impossible_root k t hk7 (hS_eq ▸ hlive)

end PEqualNP.Outside.L_meta_27331

theorem PEqualNP.Outside.L_meta_27331 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 7]⟩)) :=
  PEqualNP.Outside.L_meta_27331.final
