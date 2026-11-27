import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27434_aux
open PEqualNP.CircuitLowerBounds

def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0


def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]


def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0


def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

theorem gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, hM]

theorem getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]


theorem wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))

def nub : List ℕ → List ℕ
  | [] => []
  | a :: l => if (nub l).contains a then nub l else a :: nub l

theorem mem_nub (x : ℕ) : ∀ l : List ℕ, x ∈ nub l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [nub]
  | cons a l ih =>
    simp only [nub]
    split
    · rename_i h
      simp only [List.contains_iff_mem] at h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h') <;> [exact (ih.1 h); exact h']
    · simp [ih]

theorem getD_mem_zero (S : List ℕ) (o : ℕ) : S.getD o 0 ∈ (0 :: S) := by
  rw [List.getD_eq_getElem?_getD]
  cases hs : S[o]? with
  | none => simp
  | some v => exact List.mem_cons_of_mem _ (List.mem_of_getElem? hs)

theorem mod_eq_of_testBit (B t tgt : ℕ) (htgt : tgt < 2 ^ B)
    (h : ∀ p, p < B → t.testBit p = tgt.testBit p) : t % 2 ^ B = tgt := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < B
  · simp [hi, h i hi]
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by norm_num) (by omega))

section Live
variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (unary : α → α) (goal : α) : ℕ → Finset α → Prop
  | 0, av => goal ∈ av
  | k+1, av => build ops unary goal k av ∨
    (∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ z ∈ ops a b, build ops unary goal k (insert z av)) ∨
    (∃ a ∈ av, build ops unary goal k (insert (unary a) av))

def live (ops : α → α → Finset α) (unary : α → α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops unary goal k s ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops unary goal k (insert z rest)) ∨
    (∃ a ∈ s, unary a ∉ s ∧ ∃ rest : Finset α, s = insert a rest ∧ live ops unary goal k (insert (unary a) rest))

theorem compress {ops : α → α → Finset α} {unary : α → α} {goal : α} {k : ℕ} {av : Finset α}
    (h : build ops unary goal k av) : ∃ s ⊆ av, live ops unary goal k s := by
  induction k generalizing av with
  | zero => exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,tail⟩ | ⟨a,ha,tail⟩
    · obtain ⟨s,hs,hr⟩ := ih skip
      exact ⟨s,hs,.inl hr⟩
    · obtain ⟨t,ht,hr⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t,sub,.inl hr⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ av := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ av := by
          intro u hu
          have h' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht h'.2)).resolve_left h'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ av := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s,hs,.inr (.inl ⟨a,by simp [s],b,by simp [s],hab,z,hz,fun h => hzout (hs h),rest,rfl,?_⟩)⟩
        simpa [rest, Finset.insert_erase hzmem] using hr
    · obtain ⟨t,ht,hr⟩ := ih tail
      by_cases sub : t ⊆ av
      · exact ⟨t,sub,.inl hr⟩
      · have hzmem : unary a ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : unary a ∉ av := fun hh => sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase (unary a)
        have hrest : rest ⊆ av := by
          intro u hu
          have h' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht h'.2)).resolve_left h'.1
        let s := insert a rest
        have hs : s ⊆ av := Finset.insert_subset ha hrest
        refine ⟨s,hs,.inr (.inr ⟨a,by simp [s],fun h => hzout (hs h),rest,rfl,?_⟩)⟩
        simpa [rest,Finset.insert_erase hzmem] using hr

theorem live_card {ops : α → α → Finset α} {unary : α → α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops unary goal k s) : s.card ≤ k+1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hout,r,rfl,tail⟩ | ⟨a,ha,hout,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ r := fun hm => hout (by simp [hm])
      have ht := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at ht
      have h₁ := Finset.card_insert_le a (insert b r)
      have h₂ := Finset.card_insert_le b r
      omega
    · have hzrest : unary a ∉ r := fun hm => hout (by simp [hm])
      have ht := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at ht
      have h₁ := Finset.card_insert_le a r
      omega

theorem live_separates {ops : α → α → Finset α} {unary : α → α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    (hun : ∀ a, D (unary a) → D a)
    {k : ℕ} {s : Finset α} (h : live ops unary goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal,by simp [h],hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hout,r,rfl,tail⟩ | ⟨a,ha,hout,r,rfl,tail⟩
    · exact ih skip
    · obtain ⟨w,hw,hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a,ha,h⟩
        · exact ⟨b,hb,h⟩
      · exact ⟨w,by simp [hw],hD⟩
    · obtain ⟨w,hw,hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact ⟨a,ha,hun a hD⟩
      · exact ⟨w,by simp [hw],hD⟩

theorem live_separates_tight {ops : α → α → Finset α} {unary : α → α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops unary goal k s) (htight : s.card = k+1) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal,by simp [h],hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hout,r,rfl,tail⟩ | ⟨a,ha,hout,r,rfl,tail⟩
    · have h := live_card skip
      omega
    · have hzrest : z ∉ r := fun hm => hout (by simp [hm])
      have ht := live_card tail
      have h₁ := Finset.card_insert_le a (insert b r)
      have h₂ := Finset.card_insert_le b r
      have hcard : (insert z r).card = k+1 := by
        rw [Finset.card_insert_of_notMem hzrest] at ht ⊢
        omega
      obtain ⟨w,hw,hD⟩ := ih tail hcard
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a,ha,h⟩
        · exact ⟨b,hb,h⟩
      · exact ⟨w,by simp [hw],hD⟩
    · have hzrest : unary a ∉ r := fun hm => hout (by simp [hm])
      have ht := live_card tail
      rw [Finset.card_insert_of_notMem hzrest] at ht
      have h₁ := Finset.card_insert_le a r
      omega

theorem first_live {ops : α → α → Finset α} {unary : α → α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops unary goal (k+1) s) :
    s = {goal} ∨
    (∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops unary goal k (insert z rest)) ∨
    (∃ a ∈ s, unary a ∉ s ∧ ∃ rest : Finset α, s = insert a rest ∧ live ops unary goal k (insert (unary a) rest)) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩ | ⟨a,ha,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr (.inl ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,.inl tail⟩)
      · exact .inr (.inr ⟨a,ha,hn,r,hs,.inl tail⟩)
    · exact .inr step
end Live

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))


def keepChoices (a b : ℕ) (r : List ℕ) : List (List ℕ) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List ℕ} {a b : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : ℕ} {ws : List ℕ} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc





def opList (a b : ℕ) : List ℕ := [a &&& b, a ||| b]
abbrev monoOps (a b : ℕ) : Finset ℕ := (opList a b).toFinset

theorem ops_swap (a b : ℕ) : monoOps a b = monoOps b a := by
  ext z
  simp only [monoOps, opList, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [Nat.land_comm a b, Nat.lor_comm a b]

def sepAt (p q w : ℕ) : Bool := w.testBit p && !(w.testBit q)

theorem op_sep (p q a b z : ℕ) (hz : z ∈ monoOps a b) (hd : sepAt p q z = true) :
    sepAt p q a = true ∨ sepAt p q b = true := by
  simp only [monoOps, opList, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;>
    simp only [sepAt, Nat.testBit_land, Nat.testBit_lor] at hd ⊢ <;>
    cases ha : a.testBit p <;> cases hb : b.testBit p <;>
    cases hc : a.testBit q <;> cases he : b.testBit q <;> simp_all

def negCol (M a : ℕ) : ℕ := M ^^^ a
def diffAt (p q w : ℕ) : Bool := w.testBit p != w.testBit q
theorem mask_bit (B p : ℕ) (hp : p < B) : (2 ^ B - 1).testBit p = true := by
  rw [Nat.testBit_two_pow_sub_one]; simpa using hp

theorem op_diff (p q a b z : ℕ) (hz : z ∈ monoOps a b) (hd : diffAt p q z = true) :
    diffAt p q a = true ∨ diffAt p q b = true := by
  simp only [monoOps, opList, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl <;>
    simp only [diffAt, Nat.testBit_land, Nat.testBit_lor] at hd ⊢ <;>
    cases ha : a.testBit p <;> cases hb : b.testBit p <;>
    cases hc : a.testBit q <;> cases he : b.testBit q <;> simp_all

theorem neg_diff (B p q : ℕ) (hp : p < B) (hq : q < B) (a : ℕ)
    (hd : diffAt p q (negCol (2 ^ B - 1) a) = true) : diffAt p q a = true := by
  simp only [diffAt, negCol, Nat.testBit_xor, mask_bit B p hp, mask_bit B q hq] at hd ⊢
  cases h1 : a.testBit p <;> cases h2 : a.testBit q <;> simp_all

def separatesPairs : List (ℕ × ℕ) := [(21, 20), (29, 24), (27, 0), (11, 3), (13, 12), (21, 15), (18, 16), (11, 10), (18, 1), (29, 28), (13, 5), (27, 25), (21, 4), (18, 17), (13, 7), (27, 26), (29, 2), (11, 8), (18, 22), (13, 14), (13, 36), (18, 37), (13, 30), (29, 31), (29, 19), (29, 35), (18, 9), (13, 22), (13, 9), (18, 31), (13, 37), (18, 19), (29, 14), (18, 35), (29, 30), (29, 36), (27, 23), (21, 23), (27, 34), (21, 6), (21, 33), (21, 34), (27, 38), (21, 38), (11, 23), (11, 33), (27, 33), (27, 6), (27, 32), (21, 32), (11, 38), (11, 34), (11, 32), (11, 6), (21, 14), (27, 36), (29, 6), (11, 37), (18, 34), (21, 19), (13, 31), (13, 19), (13, 23), (27, 37), (27, 35), (18, 32), (21, 9), (29, 9), (13, 6), (21, 22), (21, 36), (27, 22), (18, 36), (11, 35), (13, 33), (27, 31), (18, 38), (18, 33), (27, 30), (11, 36), (13, 32), (18, 30), (27, 14), (11, 28), (11, 30), (18, 23), (11, 31), (27, 19), (18, 14), (11, 22), (13, 10), (29, 32), (21, 37), (27, 9), (11, 14), (29, 37), (18, 8), (11, 16), (29, 38), (11, 19), (29, 33), (11, 9), (29, 34), (21, 35), (13, 8), (18, 6), (11, 12), (13, 34), (29, 22), (13, 35), (29, 23), (21, 30), (21, 31), (11, 7), (13, 38), (11, 1), (11, 2)]

def separates (B T : ℕ) (ws : List ℕ) : Bool :=
  separatesPairs.all fun pq =>
    if pq.1 < B ∧ pq.2 < B ∧ sepAt pq.1 pq.2 T = true then
      ws.any (diffAt pq.1 pq.2)
    else true

theorem separates_live {B T g k : ℕ} (hg : g % 2 ^ B = T) (ws : List ℕ)
    (hl : live monoOps (negCol (2 ^ B - 1)) g k ws.toFinset) : separates B T ws = true := by
  apply List.all_eq_true.mpr
  intro pq hm
  rcases pq with ⟨p,q⟩
  split
  · rename_i hvalid
    obtain ⟨hp',hq',h⟩ := hvalid
    have hbits (i : ℕ) (hi : i < B) : T.testBit i = g.testBit i := by
      rw [← hg, Nat.testBit_mod_two_pow]; simp [hi]
    have hd : diffAt p q g = true := by
      unfold diffAt
      rw [← hbits p hp', ← hbits q hq']
      unfold sepAt at h
      cases h1 : T.testBit p <;> cases h2 : T.testBit q <;> simp_all
    obtain ⟨w, hw, hsep⟩ := live_separates (fun w => diffAt p q w = true) hd (op_diff p q) (neg_diff B p q hp' hq') hl
    exact List.any_eq_true.mpr ⟨w, List.mem_toFinset.mp hw, hsep⟩
  · rfl

def orientedPairs : List (ℕ × ℕ) := [(21, 22), (18, 37), (29, 35), (13, 30), (27, 22), (18, 9), (27, 31), (21, 19), (18, 35), (11, 33), (21, 37), (27, 35), (18, 31), (11, 36), (18, 33), (27, 9), (29, 30), (21, 35), (18, 19), (11, 14), (11, 6), (13, 37), (13, 36)]

def oriented (B T : ℕ) (ws : List ℕ) : Bool :=
  orientedPairs.all fun pq =>
    if pq.1 < B ∧ pq.2 < B ∧ sepAt pq.1 pq.2 T = true then
      ws.any (sepAt pq.1 pq.2)
    else true

theorem oriented_live {B T g k : ℕ} (hg : g % 2 ^ B = T) (ws : List ℕ)
    (hl : live monoOps (negCol (2 ^ B - 1)) g k ws.toFinset) (htight : ws.toFinset.card = k+1) : oriented B T ws = true := by
  apply List.all_eq_true.mpr
  intro pq hm
  rcases pq with ⟨p,q⟩
  split
  · rename_i hvalid
    obtain ⟨hp',hq',h⟩ := hvalid
    have hbits (i : ℕ) (hi : i < B) : T.testBit i = g.testBit i := by
      rw [← hg, Nat.testBit_mod_two_pow]; simp [hi]
    have hd : sepAt p q g = true := by
      unfold sepAt at h ⊢
      rw [← hbits p hp', ← hbits q hq']
      exact h
    obtain ⟨w, hw, hsep⟩ := live_separates_tight (fun w => sepAt p q w = true) hd (op_sep p q) hl htight
    exact List.any_eq_true.mpr ⟨w, List.mem_toFinset.mp hw, hsep⟩
  · rfl


def keepOne (a : ℕ) (r : List ℕ) : List (List ℕ) := [r, a::r]
theorem recover_one {ws r : List ℕ} {a : ℕ} {needed : Finset ℕ}
    (hp : ws.Perm (a::r)) (hn : ws.Nodup) (hs : ws.toFinset = insert a needed) :
    ∃ kept ∈ keepOne a r, kept.Nodup ∧ kept.toFinset = needed := by
  have har := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a r.toFinset := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a := by
    intro v
    have he : (v ∈ insert a r.toFinset) ↔ v ∈ insert a needed := by rw [← hbase,← hs]
    simp only [Finset.mem_insert,List.mem_toFinset] at he
    simp only [List.nodup_cons] at har
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a::r,by simp [keepOne],har,?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r,by simp [keepOne],(List.nodup_cons.mp har).2,?_⟩
    ext v; simp [henne]; grind
def available (M : ℕ) (S : List ℕ) : Finset ℕ := insert 0 (insert M S.toFinset)

theorem lookup_mem (M : ℕ) (S : List ℕ) (i : ℕ) : S.getD i 0 ∈ available M S := by
  have h := getD_mem_zero S i
  simp only [List.mem_cons] at h
  rcases h with h | h
  · exact Finset.mem_insert.mpr (.inl h)
  · exact Finset.mem_insert.mpr (.inr (Finset.mem_insert.mpr (.inr (List.mem_toFinset.mpr h))))

theorem available_append (M z : ℕ) (S : List ℕ) :
    available M (S ++ [z]) = insert z (available M S) := by
  ext x
  simp only [available, Finset.mem_insert, List.mem_toFinset, List.mem_append, List.mem_singleton]
  tauto


theorem gate_add (M : ℕ) (S : List ℕ) (g : Gate) (hg : GOk g) :
    let z := gt M g.op (g.inputs.map fun i => S.getD i 0)
    z ∈ available M S ∨ (∃ a ∈ available M S, ∃ b ∈ available M S, a ≠ b ∧ z ∈ monoOps a b) ∨
      (∃ a ∈ available M S, z = negCol M a) := by
  obtain ⟨hop,hl⟩ := hg
  generalize g.inputs = ins at hl ⊢
  match ins, hl with
  | [], _ =>
    rcases hop with h | h | h <;> simp [h,gt,available]
  | [i], _ =>
    rcases hop with h | h | h <;> simp only [h,List.map_cons,List.map_nil,gt]
    · exact .inl (lookup_mem M S i)
    · exact .inl (lookup_mem M S i)
    · exact .inr (.inr ⟨_,lookup_mem M S i,rfl⟩)
  | [i,j], _ =>
    let a := S.getD i 0
    let b := S.getD j 0
    have ha : a ∈ available M S := lookup_mem M S i
    have hb : b ∈ available M S := lookup_mem M S j
    rcases hop with h | h | h
    · simp only [h,List.map_cons,List.map_nil,gt]
      by_cases he : a = b
      · left; change a &&& b ∈ _; rw [← he,Nat.and_self]; exact ha
      · exact .inr (.inl ⟨a,ha,b,hb,he,by simp [monoOps,opList,a,b]⟩)
    · simp only [h,List.map_cons,List.map_nil,gt]
      by_cases he : a = b
      · left; change a ||| b ∈ _; rw [← he,Nat.or_self]; exact ha
      · exact .inr (.inl ⟨a,ha,b,hb,he,by simp [monoOps,opList,a,b]⟩)
    · exact .inr (.inr ⟨a,ha,by simp [h,gt,negCol,a]⟩)

theorem build_base (M : ℕ) (S : List ℕ) (o k : ℕ) :
    build monoOps (negCol M) (S.getD o 0) k (available M S) := by
  induction k with
  | zero => exact lookup_mem M S o
  | succ k ih => exact .inl ih

theorem compile (M : ℕ) (gs : List Gate) (S : List ℕ) (o k : ℕ)
    (hl : gs.length ≤ k) (hg : ∀ g ∈ gs, GOk g) :
    build monoOps (negCol M) ((tabs M S gs).getD o 0) k (available M S) := by
  induction gs generalizing S k with
  | nil => exact build_base M S o k
  | cons g gs ih =>
    obtain ⟨k',rfl⟩ : ∃ k', k = k'+1 := ⟨k-1,by simp at hl; omega⟩
    let z := gt M g.op (g.inputs.map fun i => S.getD i 0)
    have ht := ih (S++[z]) k' (by simpa using hl) (fun g' hg' => hg g' (by simp [hg']))
    rw [available_append] at ht
    change build monoOps (negCol M) ((tabs M (S++[z]) gs).getD o 0) (k'+1) (available M S)
    rcases gate_add M S g (hg g (by simp)) with he | ⟨a,ha,b,hb,hab,hz⟩ | ⟨a,ha,hz⟩
    · apply Or.inl
      have e : insert z (available M S) = available M S := Finset.insert_eq_of_mem he
      exact e ▸ ht
    · exact .inr (.inl ⟨a,ha,b,hb,hab,z,hz,ht⟩)
    · refine .inr (.inr ⟨a,ha,?_⟩)
      rw [← hz]
      exact ht

def initial (M : ℕ) (S : List ℕ) : List ℕ := nub (0::M::S)

theorem nub_nodup (l : List ℕ) : (nub l).Nodup := by
  induction l with
  | nil => simp [nub]
  | cons a l ih =>
    simp only [nub]
    split
    · exact ih
    · rename_i h
      exact List.nodup_cons.mpr ⟨by simpa [List.contains_iff_mem] using h, ih⟩

theorem initial_set (M : ℕ) (S : List ℕ) :
    (initial M S).toFinset = available M S := by
  ext x
  simp [initial,available,mem_nub]

def good (B T w : ℕ) : Bool := w % 2 ^ B == T

abbrev Cert := List (ℕ × List ℕ)
def insertKey (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | a::as => if x ≤ a then x::a::as else a::insertKey x as

def key : List ℕ → List ℕ
  | [] => []
  | x::xs => insertKey x (key xs)

theorem insertKey_perm (x : ℕ) (ws : List ℕ) : (insertKey x ws).Perm (x::ws) := by
  induction ws with
  | nil => rfl
  | cons a as ih =>
    simp only [insertKey]
    split
    · rfl
    · exact (ih.cons a).trans (.swap _ _ _)

theorem key_perm (ws : List ℕ) : (key ws).Perm ws := by
  induction ws with
  | nil => rfl
  | cons a as ih =>
    exact (insertKey_perm a (key as)).trans (ih.cons a)

theorem key_set (ws : List ℕ) : (key ws).toFinset = ws.toFinset := by
  ext w
  simp only [List.mem_toFinset]
  exact (key_perm _).mem_iff

theorem key_nodup {ws : List ℕ} (hn : ws.Nodup) : (key ws).Nodup :=
  (key_perm _).nodup_iff.mpr hn



def staticBad (B T k : ℕ) (ws : List ℕ) : Bool :=
  decide (ws.length > k+1) || (decide (ws.length = k+1) && !(oriented B T ws)) ||
    !(separates B T ws)

def covered (B T : ℕ) (cert : Cert) (k : ℕ) (ws : List ℕ) : Bool :=
  staticBad B T k ws || cert.contains (k,key ws)

def closed (B T : ℕ) (cert : Cert) (e : ℕ × List ℕ) : Bool :=
  !(e.2.any (good B T)) &&
  match e.1 with
  | 0 => true
  | k+1 =>
    ((pairs e.2).all fun (a,b,r) => (opList a b).all fun z =>
      if e.2.contains z then true else
      (keepChoices a b r).all fun kept => covered B T cert k (z::kept)) &&
    ((singles e.2).all fun (a,r) =>
      let z := negCol (2 ^ B - 1) a
      if e.2.contains z then true else
      (keepOne a r).all fun kept => covered B T cert k (z::kept))

theorem live_not_staticBad {B T g k : ℕ} (hg : g % 2 ^ B = T) (ws : List ℕ)
    (hn : ws.Nodup) (hl : live monoOps (negCol (2 ^ B - 1)) g k ws.toFinset) :
    staticBad B T k ws = false := by
  have hlen := live_card hl
  rw [List.toFinset_card_of_nodup hn] at hlen
  by_cases ht : ws.length = k+1
  · have hc : ws.toFinset.card = k+1 := by rw [List.toFinset_card_of_nodup hn,ht]
    simp [staticBad,Nat.not_lt.mpr hlen,separates_live hg ws hl,ht,oriented_live hg ws hl hc]
  · simp [staticBad,Nat.not_lt.mpr hlen,separates_live hg ws hl,ht]

theorem covered_mem {B T g k : ℕ} (hg : g % 2 ^ B = T) (cert : Cert)
    (ws : List ℕ) (hn : ws.Nodup) (hl : live monoOps (negCol (2 ^ B - 1)) g k ws.toFinset)
    (hc : covered B T cert k ws = true) : (k,key ws) ∈ cert := by
  simpa [covered,live_not_staticBad hg ws hn hl,List.contains_iff_mem] using hc

theorem covered_impossible {B T g : ℕ} (hg : g % 2 ^ B = T) (cert : Cert)
    (hclosed : ∀ e ∈ cert, closed B T cert e = true) (k : ℕ) (ws : List ℕ)
    (hn : ws.Nodup) (hl : live monoOps (negCol (2 ^ B - 1)) g k ws.toFinset)
    (hc : covered B T cert k ws = true) : False := by
  induction k generalizing ws with
  | zero =>
    have hm := covered_mem hg cert ws hn hl hc
    have hcl := hclosed _ hm
    change ws.toFinset = {g} at hl
    have hmem : g ∈ key ws := by
      apply List.mem_toFinset.mp
      rw [key_set,hl]; simp
    have he : (key ws).any (good B T) = true :=
      List.any_eq_true.mpr ⟨g,hmem,by simp [good,hg]⟩
    simp [closed,he] at hcl
  | succ k ih =>
    have hm := covered_mem hg cert ws hn hl hc
    have hcl := hclosed _ hm
    let xs := key ws
    have hxl : live monoOps (negCol (2 ^ B - 1)) g (k+1) xs.toFinset := by simpa only [xs,key_set] using hl
    have hxn : xs.Nodup := key_nodup hn
    change closed B T cert (k+1,xs) = true at hcl
    simp only [closed, Bool.and_eq_true] at hcl
    rcases first_live hxl with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩ | ⟨a,ha,hout,needed,hs,tail⟩
    · have hmem : g ∈ xs := by
        apply List.mem_toFinset.mp
        rw [done]; simp
      have he : xs.any (good B T) = true :=
        List.any_eq_true.mpr ⟨g,hmem,by simp [good,hg]⟩
      simp [he] at hcl
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : ℕ} (perm : xs.Perm (a :: b :: r))
          (hset : xs.toFinset = insert a (insert b needed)) (hop : z ∈ monoOps a b)
          (hpair : (a,b,r) ∈ pairs xs) : False := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hxn hset
        have hznew : z ∉ kept := by
          intro h
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr h)))
        have hznot : z ∉ xs := fun h => hout (List.mem_toFinset.mpr h)
        have hzbool : xs.contains z = false := by simp [hznot]
        have hnd := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl' : live monoOps (negCol (2 ^ B - 1)) g k (z::kept).toFinset := by simpa [hfin] using tail
        have hstep := List.all_eq_true.mp hcl.2.1 (a,b,r) hpair
        have hstep' := List.all_eq_true.mp hstep z (List.mem_toFinset.mp hop)
        simp only [hzbool, Bool.false_eq_true, if_false] at hstep'
        exact ih _ hnd hl' (List.all_eq_true.mp hstep' kept hk)
      rcases hm with hdir | hrev
      · exact go hp hs hz hdir
      · exact go (hp.trans (.swap _ _ _)) (by rw [hs,Finset.insert_comm]) (ops_swap a b ▸ hz) hrev


    · obtain ⟨r,hm,hp⟩ := pick_one (List.mem_toFinset.mp ha)
      obtain ⟨kept,hk,hnk,hfin⟩ := recover_one hp hxn hs
      let z := negCol (2 ^ B - 1) a
      have hznew : z ∉ kept := by
        intro h
        apply hout
        rw [hs]
        exact Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr h))
      have hznot : z ∉ xs := fun h => hout (List.mem_toFinset.mpr h)
      have hzbool : xs.contains z = false := by simp [hznot]
      have hnd := List.nodup_cons.mpr ⟨hznew,hnk⟩
      have hl' : live monoOps (negCol (2 ^ B - 1)) g k (z::kept).toFinset := by simpa [hfin,z] using tail
      have hstep := List.all_eq_true.mp hcl.2.2 (a,r) hm
      change (if xs.contains z then true else (keepOne a r).all (fun kept => covered B T cert k (z::kept))) = true at hstep
      simp only [hzbool,Bool.false_eq_true,if_false] at hstep
      exact ih _ hnd hl' (List.all_eq_true.mp hstep kept hk)

def initialCovered (B T n : ℕ) (cert : Cert) (inputs : List ℕ) : Bool :=
  inputs.sublists.all fun ws => covered B T cert n ws

theorem cert_no_build {B T g n : ℕ} (hg : g % 2 ^ B = T) (cert : Cert)
    (hclosed : ∀ e ∈ cert, closed B T cert e = true) (inputs : List ℕ)
    (hn : inputs.Nodup) (hinit : initialCovered B T n cert inputs = true)
    (h : build monoOps (negCol (2 ^ B - 1)) g n inputs.toFinset) : False := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  exact covered_impossible hg cert hclosed n ws (hn.filter _) (eq.symm ▸ hl)
    (List.all_eq_true.mp hinit ws (List.mem_sublists.mpr (List.filter_sublist ..)))

theorem no_circuit_on_certificate (B T k : ℕ) (T0 : List ℕ) (hT : T < 2 ^ B)
    (cert : Cert) (hclosed : ∀ e ∈ cert, closed B T cert e = true)
    (hinit : initialCovered B T k cert (initial (2 ^ B-1) T0) = true) :
    ¬ ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ k ∧
      ∀ p < B, C.eval (T0.map fun t => t.testBit p) = T.testBit p := by
  rintro ⟨C,hC,hs,hev⟩
  have hok : ∀ g ∈ C.gates, GOk g := by
    intro g hg
    obtain ⟨hop,hl⟩ := hC g hg
    exact ⟨by simpa [Set.mem_insert_iff] using hop,hl⟩
  let M := 2 ^ B - 1
  let goal := (tabs M T0 C.gates).getD C.output 0
  have hgoal : goal % 2 ^ B = T := by
    apply mod_eq_of_testBit B _ T hT
    intro p hp
    have hM : M.testBit p = true := by
      unfold M
      rw [Nat.testBit_two_pow_sub_one]; simpa using hp
    have he := hev p hp
    rw [Circuit.eval,Circuit.wires,wires_tabs _ _ hM _ _ hok,getD_map_testBit] at he
    exact he
  have hb : build monoOps (negCol (2 ^ B - 1)) goal k (available M T0) := compile M _ _ _ _ hs hok
  rw [← initial_set M T0] at hb
  exact cert_no_build hgoal cert hclosed (initial M T0) (nub_nodup _) hinit hb

def block0 : Cert := [(5, [57473024596, 239625645035, 497964055676, 539232731075, 549755781120]), (5, [57473024596, 239625645035, 539232731075, 544135433292, 549746405488]), (5, [95743910625, 205649726302, 463000203891, 544135433292, 549747457920]), (5, [95743910625, 205649726302, 539232731075, 544135433292, 549746405488])]
def block1 : Cert := [(5, [134954410741, 170725804874, 394009661007, 545477623680, 549746405488]), (5, [134954410741, 170725804874, 539232731075, 544135433292, 549746405488]), (5, [134954410741, 394009661007, 428430356592, 545477623680, 549739891530]), (5, [134954410741, 394009661007, 445611080570, 545477623680, 549739036672])]
def block2 : Cert := [(5, [205649726302, 355153235020, 463000203891, 542424146657, 549747457920]), (5, [205649726302, 373574627053, 463000203891, 541182623744, 549747457920]), (5, [239625645035, 315894415939, 497964055676, 538509377492, 549755781120]), (5, [239625645035, 334704329303, 497964055676, 536879333248, 549755781120])]
def block3 : Cert := [(5, [239625645035, 492282789291, 497964055676, 539232731075, 549755781120]), (5, [239625645035, 492282789291, 539232731075, 544135433292, 549746405488]), (5, [315894415939, 497964055676, 538509377492, 542424146657, 549739891530]), (5, [334704329303, 373574627053, 445611080570, 536879333248, 549755781120])]
def block4 : Cert := [(5, [334704329303, 373574627053, 445611080570, 541182623744, 549747457920]), (5, [334704329303, 373574627053, 445611080570, 545477623680, 549739036672]), (5, [355153235020, 463000203891, 538509377492, 542424146657, 549739891530]), (5, [394009661007, 428430356592, 538509377492, 542424146657, 549739891530])]
def block5 : Cert := [(6, [57473024596, 95743910625, 170725804874, 394009661007, 545477623680, 549746405488]), (6, [57473024596, 95743910625, 170725804874, 463000203891, 544135433292, 549747457920]), (6, [57473024596, 95743910625, 170725804874, 497964055676, 539232731075, 549755781120]), (6, [57473024596, 95743910625, 170725804874, 539232731075, 544135433292, 549746405488])]
def block6 : Cert := [(6, [57473024596, 95743910625, 315894415939, 355153235020, 442389854976, 549739036672]), (6, [57473024596, 95743910625, 315894415939, 355153235020, 445611080570, 549755813760]), (6, [57473024596, 95743910625, 315894415939, 355153235020, 545477623680, 549747260282]), (6, [57473024596, 95743910625, 393996929610, 428430356592, 536879333248, 541182623744])]
def block7 : Cert := [(6, [57473024596, 95743910625, 394009661007, 428430356592, 545477623680, 549739891530]), (6, [57473024596, 95743910625, 394009661007, 445611080570, 545477623680, 549739036672]), (6, [57473024596, 95743910625, 394009661007, 536879333248, 541182623744, 549747260282]), (6, [57473024596, 95743910625, 428430356592, 539232731075, 544135433292, 549739891530])]
def block8 : Cert := [(6, [57473024596, 95743910625, 445611080570, 539232731075, 544135433292, 549739036672]), (6, [57473024596, 95743910625, 532525514367, 536879333248, 541182623744, 549739891530]), (6, [57473024596, 170725804874, 315894415939, 373569908352, 428430356592, 541182623744]), (6, [57473024596, 170725804874, 315894415939, 373574627053, 428430356592, 549755813760])]
def block9 : Cert := [(6, [57473024596, 170725804874, 315894415939, 428430356592, 545376956141, 549747457920]), (6, [57473024596, 170725804874, 355153235020, 456490623585, 536879333248, 549739036672]), (6, [57473024596, 170725804874, 355153235020, 463000203891, 542424146657, 549747457920]), (6, [57473024596, 170725804874, 355153235020, 539232731075, 542424146657, 549746405488])]
def block10 : Cert := [(6, [57473024596, 170725804874, 373574627053, 463000203891, 541182623744, 549747457920]), (6, [57473024596, 170725804874, 373574627053, 539232731075, 541182623744, 549746405488]), (6, [57473024596, 170725804874, 463000203891, 536879333248, 545376956141, 549739036672]), (6, [57473024596, 170725804874, 532525514367, 536879333248, 542424146657, 549739036672])]
def block11 : Cert := [(6, [57473024596, 229927824323, 355153235020, 428430356592, 541182623744, 549739036672]), (6, [57473024596, 239625645035, 315894415939, 497964055676, 536879333248, 549755781120]), (6, [57473024596, 239625645035, 315894415939, 497964055676, 541182623744, 549747457920]), (6, [57473024596, 239625645035, 315894415939, 497964055676, 545477623680, 549739036672])]
def block12 : Cert := [(6, [57473024596, 239625645035, 315894415939, 536879333248, 544135433292, 549746405488]), (6, [57473024596, 239625645035, 355153235020, 428430356592, 539232731075, 549755781120]), (6, [57473024596, 239625645035, 355153235020, 463000203891, 536879333248, 549755781120]), (6, [57473024596, 239625645035, 355153235020, 463000203891, 541182623744, 549747457920])]
def block13 : Cert := [(6, [57473024596, 239625645035, 355153235020, 463000203891, 545477623680, 549739036672]), (6, [57473024596, 239625645035, 355153235020, 539232731075, 541182623744, 549746405488]), (6, [57473024596, 239625645035, 394009661007, 428430356592, 536879333248, 549755781120]), (6, [57473024596, 239625645035, 394009661007, 428430356592, 541182623744, 549747457920])]
def block14 : Cert := [(6, [57473024596, 239625645035, 394009661007, 428430356592, 545477623680, 549739036672]), (6, [57473024596, 239625645035, 428430356592, 539232731075, 544135433292, 549739036672]), (6, [57473024596, 239625645035, 497964055676, 539232731075, 541182623744, 549739036672]), (6, [57473024596, 315894415939, 373574627053, 445611080570, 536879333248, 549755781120])]
def block15 : Cert := [(6, [57473024596, 315894415939, 373574627053, 445611080570, 541182623744, 549747457920]), (6, [57473024596, 315894415939, 373574627053, 445611080570, 545477623680, 549739036672]), (6, [57473024596, 315894415939, 497964055676, 536879333248, 542424146657, 549739891530]), (6, [57473024596, 355153235020, 428430356592, 539232731075, 542424146657, 549739891530])]
def block16 : Cert := [(6, [57473024596, 355153235020, 445611080570, 539232731075, 542424146657, 549739036672]), (6, [57473024596, 355153235020, 463000203891, 536879333248, 542424146657, 549739891530]), (6, [57473024596, 373574627053, 428430356592, 539232731075, 541182623744, 549739891530]), (6, [57473024596, 373574627053, 445611080570, 539232731075, 541182623744, 549739036672])]
def block17 : Cert := [(6, [57473024596, 394009661007, 428430356592, 536879333248, 542424146657, 549739891530]), (6, [95743910625, 170725804874, 315894415939, 486952959060, 541182623744, 549739036672]), (6, [95743910625, 170725804874, 315894415939, 497964055676, 538509377492, 549755781120]), (6, [95743910625, 170725804874, 315894415939, 538509377492, 544135433292, 549746405488])]
def block18 : Cert := [(6, [95743910625, 170725804874, 334704312320, 355153235020, 428430356592, 536879333248]), (6, [95743910625, 170725804874, 334704329303, 355153235020, 428430356592, 549755813760]), (6, [95743910625, 170725804874, 334704329303, 497964055676, 536879333248, 549755781120]), (6, [95743910625, 170725804874, 334704329303, 536879333248, 544135433292, 549746405488])]
def block19 : Cert := [(6, [95743910625, 170725804874, 355153235020, 428430356592, 540862775255, 549755781120]), (6, [95743910625, 170725804874, 394009661007, 492282789291, 545477623680, 549746405488]), (6, [95743910625, 170725804874, 463000203891, 492282789291, 544135433292, 549747457920]), (6, [95743910625, 170725804874, 492282789291, 497964055676, 539232731075, 549755781120])]
def block20 : Cert := [(6, [95743910625, 170725804874, 492282789291, 539232731075, 544135433292, 549746405488]), (6, [95743910625, 170725804874, 497964055676, 540862775255, 541182623744, 549739036672]), (6, [95743910625, 170725804874, 532525514367, 538509377492, 541182623744, 549739036672]), (6, [95743910625, 200264239180, 315894415939, 428430356592, 536879333248, 549739036672])]
def block21 : Cert := [(6, [95743910625, 205649726302, 315894415939, 428430356592, 544135433292, 549747457920]), (6, [95743910625, 205649726302, 315894415939, 497964055676, 536879333248, 549755781120]), (6, [95743910625, 205649726302, 315894415939, 497964055676, 541182623744, 549747457920]), (6, [95743910625, 205649726302, 315894415939, 497964055676, 545477623680, 549739036672])]
def block22 : Cert := [(6, [95743910625, 205649726302, 315894415939, 536879333248, 544135433292, 549746405488]), (6, [95743910625, 205649726302, 355153235020, 463000203891, 536879333248, 549755781120]), (6, [95743910625, 205649726302, 355153235020, 463000203891, 541182623744, 549747457920]), (6, [95743910625, 205649726302, 355153235020, 463000203891, 545477623680, 549739036672])]
def block23 : Cert := [(6, [95743910625, 205649726302, 355153235020, 539232731075, 541182623744, 549746405488]), (6, [95743910625, 205649726302, 394009661007, 428430356592, 536879333248, 549755781120]), (6, [95743910625, 205649726302, 394009661007, 428430356592, 541182623744, 549747457920]), (6, [95743910625, 205649726302, 394009661007, 428430356592, 545477623680, 549739036672])]
def block24 : Cert := [(6, [95743910625, 205649726302, 428430356592, 539232731075, 544135433292, 549739036672]), (6, [95743910625, 205649726302, 463000203891, 536879333248, 544135433292, 549739036672]), (6, [95743910625, 315894415939, 355153235020, 442389854976, 492282789291, 549739036672]), (6, [95743910625, 315894415939, 355153235020, 445611080570, 492282789291, 549755813760])]
def block25 : Cert := [(6, [95743910625, 315894415939, 355153235020, 492282789291, 545477623680, 549747260282]), (6, [95743910625, 315894415939, 428430356592, 538509377492, 544135433292, 549739891530]), (6, [95743910625, 315894415939, 445611080570, 538509377492, 544135433292, 549739036672]), (6, [95743910625, 315894415939, 497964055676, 538509377492, 541182623744, 549739891530])]
def block26 : Cert := [(6, [95743910625, 334704329303, 355153235020, 445611080570, 536879333248, 549755781120]), (6, [95743910625, 334704329303, 355153235020, 445611080570, 541182623744, 549747457920]), (6, [95743910625, 334704329303, 355153235020, 445611080570, 545477623680, 549739036672]), (6, [95743910625, 334704329303, 428430356592, 536879333248, 544135433292, 549739891530])]
def block27 : Cert := [(6, [95743910625, 334704329303, 445611080570, 536879333248, 544135433292, 549739036672]), (6, [95743910625, 355153235020, 463000203891, 538509377492, 541182623744, 549739891530]), (6, [95743910625, 393996929610, 428430356592, 492282789291, 536879333248, 541182623744]), (6, [95743910625, 394009661007, 428430356592, 492282789291, 545477623680, 549739891530])]
def block28 : Cert := [(6, [95743910625, 394009661007, 428430356592, 538509377492, 541182623744, 549739891530]), (6, [95743910625, 394009661007, 445611080570, 492282789291, 545477623680, 549739036672]), (6, [95743910625, 394009661007, 492282789291, 536879333248, 541182623744, 549747260282]), (6, [95743910625, 428430356592, 492282789291, 539232731075, 544135433292, 549739891530])]
def block29 : Cert := [(6, [95743910625, 445611080570, 492282789291, 539232731075, 544135433292, 549739036672]), (6, [95743910625, 492282789291, 532525514367, 536879333248, 541182623744, 549739891530]), (6, [134945464432, 170725804874, 315894415939, 355153235020, 536879333248, 541182623744]), (6, [134954410741, 170725804874, 315894415939, 355153235020, 545477623680, 549746405488])]
def block30 : Cert := [(6, [134954410741, 170725804874, 315894415939, 497964055676, 536879333248, 549755781120]), (6, [134954410741, 170725804874, 315894415939, 497964055676, 541182623744, 549747457920]), (6, [134954410741, 170725804874, 315894415939, 497964055676, 545477623680, 549739036672]), (6, [134954410741, 170725804874, 315894415939, 536879333248, 544135433292, 549746405488])]
def block31 : Cert := [(6, [134954410741, 170725804874, 355153235020, 463000203891, 536879333248, 549755781120]), (6, [134954410741, 170725804874, 355153235020, 463000203891, 541182623744, 549747457920]), (6, [134954410741, 170725804874, 355153235020, 463000203891, 545477623680, 549739036672]), (6, [134954410741, 170725804874, 355153235020, 539232731075, 541182623744, 549746405488])]
def block32 : Cert := [(6, [134954410741, 170725804874, 394009661007, 428430356592, 536879333248, 549755781120]), (6, [134954410741, 170725804874, 394009661007, 428430356592, 541182623744, 549747457920]), (6, [134954410741, 170725804874, 394009661007, 428430356592, 545477623680, 549739036672]), (6, [134954410741, 170725804874, 394009661007, 536879333248, 541182623744, 549746405488])]
def block33 : Cert := [(6, [134954410741, 170725804874, 428430356592, 539232731075, 544135433292, 549739036672]), (6, [134954410741, 315894415939, 355153235020, 428430356592, 545477623680, 549739891530]), (6, [134954410741, 315894415939, 355153235020, 445611080570, 545477623680, 549739036672]), (6, [134954410741, 315894415939, 355153235020, 536879333248, 541182623744, 549747260282])]
def block34 : Cert := [(6, [134954410741, 394009661007, 428430356592, 536879333248, 541182623744, 549739891530]), (6, [134954410741, 394009661007, 445611080570, 536879333248, 541182623744, 549739036672]), (6, [170725804874, 315894415939, 355153235020, 538509377492, 542424146657, 549746405488]), (6, [170725804874, 315894415939, 373569908352, 428430356592, 492282789291, 541182623744])]
def block35 : Cert := [(6, [170725804874, 315894415939, 373574627053, 428430356592, 492282789291, 549755813760]), (6, [170725804874, 315894415939, 373574627053, 538509377492, 541182623744, 549746405488]), (6, [170725804874, 315894415939, 428430356592, 492282789291, 545376956141, 549747457920]), (6, [170725804874, 315894415939, 497964055676, 538509377492, 542424146657, 549739036672])]
def block36 : Cert := [(6, [170725804874, 334704329303, 355153235020, 536879333248, 542424146657, 549746405488]), (6, [170725804874, 334704329303, 373574627053, 428430356592, 536879333248, 549755781120]), (6, [170725804874, 334704329303, 373574627053, 428430356592, 541182623744, 549747457920]), (6, [170725804874, 334704329303, 373574627053, 428430356592, 545477623680, 549739036672])]
def block37 : Cert := [(6, [170725804874, 334704329303, 373574627053, 536879333248, 541182623744, 549746405488]), (6, [170725804874, 355153235020, 456490623585, 492282789291, 536879333248, 549739036672]), (6, [170725804874, 355153235020, 463000203891, 492282789291, 542424146657, 549747457920]), (6, [170725804874, 355153235020, 463000203891, 538509377492, 542424146657, 549739036672])]
def block38 : Cert := [(6, [170725804874, 355153235020, 492282789291, 539232731075, 542424146657, 549746405488]), (6, [170725804874, 373574627053, 463000203891, 492282789291, 541182623744, 549747457920]), (6, [170725804874, 373574627053, 492282789291, 539232731075, 541182623744, 549746405488]), (6, [170725804874, 394009661007, 428430356592, 538509377492, 542424146657, 549739036672])]
def block39 : Cert := [(6, [170725804874, 463000203891, 492282789291, 536879333248, 545376956141, 549739036672]), (6, [170725804874, 492282789291, 532525514367, 536879333248, 542424146657, 549739036672]), (6, [205649726302, 315894415939, 355153235020, 428430356592, 542424146657, 549747457920]), (6, [205649726302, 315894415939, 373574627053, 428430356592, 541182623744, 549747457920])]
def block40 : Cert := [(6, [205649726302, 315894415939, 428430356592, 536879333248, 545376956141, 549739036672]), (6, [205649726302, 355153235020, 463000203891, 536879333248, 542424146657, 549739036672]), (6, [205649726302, 373574627053, 463000203891, 536879333248, 541182623744, 549739036672]), (6, [229927824323, 355153235020, 428430356592, 492282789291, 541182623744, 549739036672])]
def block41 : Cert := [(6, [239625645035, 315894415939, 355153235020, 428430356592, 538509377492, 549755781120]), (6, [239625645035, 315894415939, 492282789291, 497964055676, 536879333248, 549755781120]), (6, [239625645035, 315894415939, 492282789291, 497964055676, 541182623744, 549747457920]), (6, [239625645035, 315894415939, 492282789291, 497964055676, 545477623680, 549739036672])]
def block42 : Cert := [(6, [239625645035, 315894415939, 492282789291, 536879333248, 544135433292, 549746405488]), (6, [239625645035, 315894415939, 497964055676, 538509377492, 541182623744, 549739036672]), (6, [239625645035, 334704329303, 355153235020, 428430356592, 536879333248, 549755781120]), (6, [239625645035, 334704329303, 497964055676, 536879333248, 541182623744, 549739036672])]
def block43 : Cert := [(6, [239625645035, 355153235020, 428430356592, 492282789291, 539232731075, 549755781120]), (6, [239625645035, 355153235020, 428430356592, 540862775255, 541182623744, 549739036672]), (6, [239625645035, 355153235020, 463000203891, 492282789291, 536879333248, 549755781120]), (6, [239625645035, 355153235020, 463000203891, 492282789291, 541182623744, 549747457920])]
def block44 : Cert := [(6, [239625645035, 355153235020, 463000203891, 492282789291, 545477623680, 549739036672]), (6, [239625645035, 355153235020, 492282789291, 539232731075, 541182623744, 549746405488]), (6, [239625645035, 394009661007, 428430356592, 492282789291, 536879333248, 549755781120]), (6, [239625645035, 394009661007, 428430356592, 492282789291, 541182623744, 549747457920])]
def block45 : Cert := [(6, [239625645035, 394009661007, 428430356592, 492282789291, 545477623680, 549739036672]), (6, [239625645035, 428430356592, 492282789291, 539232731075, 544135433292, 549739036672]), (6, [239625645035, 492282789291, 497964055676, 539232731075, 541182623744, 549739036672]), (6, [274541177855, 315894415939, 355153235020, 536879333248, 541182623744, 549746405488])]
def block46 : Cert := [(6, [274541177855, 315894415939, 428430356592, 536879333248, 544135433292, 549739036672]), (6, [274541177855, 355153235020, 428430356592, 539232731075, 541182623744, 549739036672]), (6, [315894415939, 355153235020, 428430356592, 538509377492, 542424146657, 549739891530]), (6, [315894415939, 355153235020, 445611080570, 538509377492, 542424146657, 549739036672])]
def block47 : Cert := [(6, [315894415939, 373574627053, 428430356592, 538509377492, 541182623744, 549739891530]), (6, [315894415939, 373574627053, 445611080570, 492282789291, 536879333248, 549755781120]), (6, [315894415939, 373574627053, 445611080570, 492282789291, 541182623744, 549747457920]), (6, [315894415939, 373574627053, 445611080570, 492282789291, 545477623680, 549739036672])]
def block48 : Cert := [(6, [315894415939, 373574627053, 445611080570, 538509377492, 541182623744, 549739036672]), (6, [315894415939, 492282789291, 497964055676, 536879333248, 542424146657, 549739891530]), (6, [334704329303, 355153235020, 428430356592, 536879333248, 542424146657, 549739891530]), (6, [334704329303, 355153235020, 445611080570, 536879333248, 542424146657, 549739036672])]
def block49 : Cert := [(6, [334704329303, 373574627053, 428430356592, 536879333248, 541182623744, 549739891530]), (6, [334704329303, 373574627053, 445611080570, 536879333248, 541182623744, 549739036672]), (6, [355153235020, 428430356592, 492282789291, 539232731075, 542424146657, 549739891530]), (6, [355153235020, 445611080570, 492282789291, 539232731075, 542424146657, 549739036672])]
def block50 : Cert := [(6, [355153235020, 463000203891, 492282789291, 536879333248, 542424146657, 549739891530]), (6, [373574627053, 428430356592, 492282789291, 539232731075, 541182623744, 549739891530]), (6, [373574627053, 445611080570, 492282789291, 539232731075, 541182623744, 549739036672]), (6, [394009661007, 428430356592, 492282789291, 536879333248, 542424146657, 549739891530])]
def block51 : Cert := [(7, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 549755813760]), (7, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 545477623680, 549746405488]), (7, [57473024596, 95743910625, 170725804874, 315894415939, 428430356592, 544135433292, 549747457920]), (7, [57473024596, 95743910625, 170725804874, 315894415939, 497964055676, 536879333248, 549755781120])]
def block52 : Cert := [(7, [57473024596, 95743910625, 170725804874, 315894415939, 497964055676, 541182623744, 549747457920]), (7, [57473024596, 95743910625, 170725804874, 315894415939, 497964055676, 545477623680, 549739036672]), (7, [57473024596, 95743910625, 170725804874, 315894415939, 536879333248, 544135433292, 549746405488]), (7, [57473024596, 95743910625, 170725804874, 355153235020, 428430356592, 539232731075, 549755781120])]
def block53 : Cert := [(7, [57473024596, 95743910625, 170725804874, 355153235020, 463000203891, 536879333248, 549755781120]), (7, [57473024596, 95743910625, 170725804874, 355153235020, 463000203891, 541182623744, 549747457920]), (7, [57473024596, 95743910625, 170725804874, 355153235020, 463000203891, 545477623680, 549739036672]), (7, [57473024596, 95743910625, 170725804874, 355153235020, 539232731075, 541182623744, 549746405488])]
def block54 : Cert := [(7, [57473024596, 95743910625, 170725804874, 394009661007, 428430356592, 536879333248, 549755781120]), (7, [57473024596, 95743910625, 170725804874, 394009661007, 428430356592, 541182623744, 549747457920]), (7, [57473024596, 95743910625, 170725804874, 394009661007, 428430356592, 545477623680, 549739036672]), (7, [57473024596, 95743910625, 170725804874, 394009661007, 536879333248, 541182623744, 549746405488])]
def block55 : Cert := [(7, [57473024596, 95743910625, 170725804874, 428430356592, 539232731075, 544135433292, 549739036672]), (7, [57473024596, 95743910625, 170725804874, 463000203891, 536879333248, 544135433292, 549739036672]), (7, [57473024596, 95743910625, 170725804874, 497964055676, 539232731075, 541182623744, 549739036672]), (7, [57473024596, 95743910625, 170725804874, 532525514367, 536879333248, 541182623744, 549739036672])]
def block56 : Cert := [(7, [57473024596, 95743910625, 315894415939, 355153235020, 428430356592, 545477623680, 549739891530]), (7, [57473024596, 95743910625, 315894415939, 355153235020, 445611080570, 536879333248, 549755781120]), (7, [57473024596, 95743910625, 315894415939, 355153235020, 445611080570, 541182623744, 549747457920]), (7, [57473024596, 95743910625, 315894415939, 355153235020, 445611080570, 545477623680, 549739036672])]
def block57 : Cert := [(7, [57473024596, 95743910625, 315894415939, 355153235020, 536879333248, 541182623744, 549747260282]), (7, [57473024596, 95743910625, 315894415939, 428430356592, 536879333248, 544135433292, 549739891530]), (7, [57473024596, 95743910625, 315894415939, 445611080570, 536879333248, 544135433292, 549739036672]), (7, [57473024596, 95743910625, 315894415939, 497964055676, 536879333248, 541182623744, 549739891530])]
def block58 : Cert := [(7, [57473024596, 95743910625, 355153235020, 428430356592, 539232731075, 541182623744, 549739891530]), (7, [57473024596, 95743910625, 355153235020, 445611080570, 539232731075, 541182623744, 549739036672]), (7, [57473024596, 95743910625, 355153235020, 463000203891, 536879333248, 541182623744, 549739891530]), (7, [57473024596, 95743910625, 394009661007, 428430356592, 536879333248, 541182623744, 549739891530])]
def block59 : Cert := [(7, [57473024596, 95743910625, 394009661007, 445611080570, 536879333248, 541182623744, 549739036672]), (7, [57473024596, 170725804874, 315894415939, 355153235020, 428430356592, 542424146657, 549747457920]), (7, [57473024596, 170725804874, 315894415939, 355153235020, 536879333248, 542424146657, 549746405488]), (7, [57473024596, 170725804874, 315894415939, 373574627053, 428430356592, 536879333248, 549755781120])]
def block60 : Cert := [(7, [57473024596, 170725804874, 315894415939, 373574627053, 428430356592, 541182623744, 549747457920]), (7, [57473024596, 170725804874, 315894415939, 373574627053, 428430356592, 545477623680, 549739036672]), (7, [57473024596, 170725804874, 315894415939, 373574627053, 536879333248, 541182623744, 549746405488]), (7, [57473024596, 170725804874, 315894415939, 428430356592, 536879333248, 545376956141, 549739036672])]
def block61 : Cert := [(7, [57473024596, 170725804874, 315894415939, 497964055676, 536879333248, 542424146657, 549739036672]), (7, [57473024596, 170725804874, 355153235020, 428430356592, 539232731075, 542424146657, 549739036672]), (7, [57473024596, 170725804874, 355153235020, 463000203891, 536879333248, 542424146657, 549739036672]), (7, [57473024596, 170725804874, 373574627053, 428430356592, 539232731075, 541182623744, 549739036672])]
def block62 : Cert := [(7, [57473024596, 170725804874, 373574627053, 463000203891, 536879333248, 541182623744, 549739036672]), (7, [57473024596, 170725804874, 394009661007, 428430356592, 536879333248, 542424146657, 549739036672]), (7, [57473024596, 239625645035, 315894415939, 355153235020, 428430356592, 536879333248, 549755781120]), (7, [57473024596, 239625645035, 315894415939, 355153235020, 428430356592, 541182623744, 549747457920])]
def block63 : Cert := [(7, [57473024596, 239625645035, 315894415939, 355153235020, 428430356592, 545477623680, 549739036672]), (7, [57473024596, 239625645035, 315894415939, 355153235020, 536879333248, 541182623744, 549746405488]), (7, [57473024596, 239625645035, 315894415939, 428430356592, 536879333248, 544135433292, 549739036672]), (7, [57473024596, 239625645035, 315894415939, 497964055676, 536879333248, 541182623744, 549739036672])]
def block64 : Cert := [(7, [57473024596, 239625645035, 355153235020, 428430356592, 539232731075, 541182623744, 549739036672]), (7, [57473024596, 239625645035, 355153235020, 463000203891, 536879333248, 541182623744, 549739036672]), (7, [57473024596, 239625645035, 394009661007, 428430356592, 536879333248, 541182623744, 549739036672]), (7, [57473024596, 315894415939, 355153235020, 428430356592, 536879333248, 542424146657, 549739891530])]
def block65 : Cert := [(7, [57473024596, 315894415939, 355153235020, 445611080570, 536879333248, 542424146657, 549739036672]), (7, [57473024596, 315894415939, 373574627053, 428430356592, 536879333248, 541182623744, 549739891530]), (7, [57473024596, 315894415939, 373574627053, 445611080570, 536879333248, 541182623744, 549739036672]), (7, [95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 549755813760])]
def block66 : Cert := [(7, [95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 538509377492, 549755781120]), (7, [95743910625, 170725804874, 315894415939, 355153235020, 492282789291, 545477623680, 549746405488]), (7, [95743910625, 170725804874, 315894415939, 355153235020, 538509377492, 541182623744, 549746405488]), (7, [95743910625, 170725804874, 315894415939, 428430356592, 492282789291, 544135433292, 549747457920])]
def block67 : Cert := [(7, [95743910625, 170725804874, 315894415939, 428430356592, 538509377492, 544135433292, 549739036672]), (7, [95743910625, 170725804874, 315894415939, 492282789291, 497964055676, 536879333248, 549755781120]), (7, [95743910625, 170725804874, 315894415939, 492282789291, 497964055676, 541182623744, 549747457920]), (7, [95743910625, 170725804874, 315894415939, 492282789291, 497964055676, 545477623680, 549739036672])]
def block68 : Cert := [(7, [95743910625, 170725804874, 315894415939, 492282789291, 536879333248, 544135433292, 549746405488]), (7, [95743910625, 170725804874, 315894415939, 497964055676, 538509377492, 541182623744, 549739036672]), (7, [95743910625, 170725804874, 334704329303, 355153235020, 428430356592, 536879333248, 549755781120]), (7, [95743910625, 170725804874, 334704329303, 355153235020, 428430356592, 541182623744, 549747457920])]
def block69 : Cert := [(7, [95743910625, 170725804874, 334704329303, 355153235020, 428430356592, 545477623680, 549739036672]), (7, [95743910625, 170725804874, 334704329303, 355153235020, 536879333248, 541182623744, 549746405488]), (7, [95743910625, 170725804874, 334704329303, 428430356592, 536879333248, 544135433292, 549739036672]), (7, [95743910625, 170725804874, 334704329303, 497964055676, 536879333248, 541182623744, 549739036672])]
def block70 : Cert := [(7, [95743910625, 170725804874, 355153235020, 428430356592, 492282789291, 539232731075, 549755781120]), (7, [95743910625, 170725804874, 355153235020, 428430356592, 540862775255, 541182623744, 549739036672]), (7, [95743910625, 170725804874, 355153235020, 463000203891, 492282789291, 536879333248, 549755781120]), (7, [95743910625, 170725804874, 355153235020, 463000203891, 492282789291, 541182623744, 549747457920])]
def block71 : Cert := [(7, [95743910625, 170725804874, 355153235020, 463000203891, 492282789291, 545477623680, 549739036672]), (7, [95743910625, 170725804874, 355153235020, 463000203891, 538509377492, 541182623744, 549739036672]), (7, [95743910625, 170725804874, 355153235020, 492282789291, 539232731075, 541182623744, 549746405488]), (7, [95743910625, 170725804874, 394009661007, 428430356592, 492282789291, 536879333248, 549755781120])]
def block72 : Cert := [(7, [95743910625, 170725804874, 394009661007, 428430356592, 492282789291, 541182623744, 549747457920]), (7, [95743910625, 170725804874, 394009661007, 428430356592, 492282789291, 545477623680, 549739036672]), (7, [95743910625, 170725804874, 394009661007, 428430356592, 538509377492, 541182623744, 549739036672]), (7, [95743910625, 170725804874, 394009661007, 492282789291, 536879333248, 541182623744, 549746405488])]
def block73 : Cert := [(7, [95743910625, 170725804874, 428430356592, 492282789291, 539232731075, 544135433292, 549739036672]), (7, [95743910625, 170725804874, 463000203891, 492282789291, 536879333248, 544135433292, 549739036672]), (7, [95743910625, 170725804874, 492282789291, 497964055676, 539232731075, 541182623744, 549739036672]), (7, [95743910625, 170725804874, 492282789291, 532525514367, 536879333248, 541182623744, 549739036672])]
def block74 : Cert := [(7, [95743910625, 205649726302, 315894415939, 355153235020, 428430356592, 536879333248, 549755781120]), (7, [95743910625, 205649726302, 315894415939, 355153235020, 428430356592, 541182623744, 549747457920]), (7, [95743910625, 205649726302, 315894415939, 355153235020, 428430356592, 545477623680, 549739036672]), (7, [95743910625, 205649726302, 315894415939, 355153235020, 536879333248, 541182623744, 549746405488])]
def block75 : Cert := [(7, [95743910625, 205649726302, 315894415939, 428430356592, 536879333248, 544135433292, 549739036672]), (7, [95743910625, 205649726302, 315894415939, 497964055676, 536879333248, 541182623744, 549739036672]), (7, [95743910625, 205649726302, 355153235020, 428430356592, 539232731075, 541182623744, 549739036672]), (7, [95743910625, 205649726302, 355153235020, 463000203891, 536879333248, 541182623744, 549739036672])]
def block76 : Cert := [(7, [95743910625, 205649726302, 394009661007, 428430356592, 536879333248, 541182623744, 549739036672]), (7, [95743910625, 315894415939, 355153235020, 428430356592, 492282789291, 545477623680, 549739891530]), (7, [95743910625, 315894415939, 355153235020, 428430356592, 538509377492, 541182623744, 549739891530]), (7, [95743910625, 315894415939, 355153235020, 445611080570, 492282789291, 536879333248, 549755781120])]
def block77 : Cert := [(7, [95743910625, 315894415939, 355153235020, 445611080570, 492282789291, 541182623744, 549747457920]), (7, [95743910625, 315894415939, 355153235020, 445611080570, 492282789291, 545477623680, 549739036672]), (7, [95743910625, 315894415939, 355153235020, 445611080570, 538509377492, 541182623744, 549739036672]), (7, [95743910625, 315894415939, 355153235020, 492282789291, 536879333248, 541182623744, 549747260282])]
def block78 : Cert := [(7, [95743910625, 315894415939, 428430356592, 492282789291, 536879333248, 544135433292, 549739891530]), (7, [95743910625, 315894415939, 445611080570, 492282789291, 536879333248, 544135433292, 549739036672]), (7, [95743910625, 315894415939, 492282789291, 497964055676, 536879333248, 541182623744, 549739891530]), (7, [95743910625, 334704329303, 355153235020, 428430356592, 536879333248, 541182623744, 549739891530])]
def block79 : Cert := [(7, [95743910625, 334704329303, 355153235020, 445611080570, 536879333248, 541182623744, 549739036672]), (7, [95743910625, 355153235020, 428430356592, 492282789291, 539232731075, 541182623744, 549739891530]), (7, [95743910625, 355153235020, 445611080570, 492282789291, 539232731075, 541182623744, 549739036672]), (7, [95743910625, 355153235020, 463000203891, 492282789291, 536879333248, 541182623744, 549739891530])]
def block80 : Cert := [(7, [95743910625, 394009661007, 428430356592, 492282789291, 536879333248, 541182623744, 549739891530]), (7, [95743910625, 394009661007, 445611080570, 492282789291, 536879333248, 541182623744, 549739036672]), (7, [134954410741, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 549755781120]), (7, [134954410741, 170725804874, 315894415939, 355153235020, 428430356592, 541182623744, 549747457920])]
def block81 : Cert := [(7, [134954410741, 170725804874, 315894415939, 355153235020, 428430356592, 545477623680, 549739036672]), (7, [134954410741, 170725804874, 315894415939, 355153235020, 536879333248, 541182623744, 549746405488]), (7, [134954410741, 170725804874, 315894415939, 428430356592, 536879333248, 544135433292, 549739036672]), (7, [134954410741, 170725804874, 315894415939, 497964055676, 536879333248, 541182623744, 549739036672])]
def block82 : Cert := [(7, [134954410741, 170725804874, 355153235020, 428430356592, 539232731075, 541182623744, 549739036672]), (7, [134954410741, 170725804874, 355153235020, 463000203891, 536879333248, 541182623744, 549739036672]), (7, [134954410741, 170725804874, 394009661007, 428430356592, 536879333248, 541182623744, 549739036672]), (7, [134954410741, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739891530])]
def block83 : Cert := [(7, [134954410741, 315894415939, 355153235020, 445611080570, 536879333248, 541182623744, 549739036672]), (7, [170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 542424146657, 549747457920]), (7, [170725804874, 315894415939, 355153235020, 428430356592, 538509377492, 542424146657, 549739036672]), (7, [170725804874, 315894415939, 355153235020, 492282789291, 536879333248, 542424146657, 549746405488])]
def block84 : Cert := [(7, [170725804874, 315894415939, 373574627053, 428430356592, 492282789291, 536879333248, 549755781120]), (7, [170725804874, 315894415939, 373574627053, 428430356592, 492282789291, 541182623744, 549747457920]), (7, [170725804874, 315894415939, 373574627053, 428430356592, 492282789291, 545477623680, 549739036672]), (7, [170725804874, 315894415939, 373574627053, 428430356592, 538509377492, 541182623744, 549739036672])]
def block85 : Cert := [(7, [170725804874, 315894415939, 373574627053, 492282789291, 536879333248, 541182623744, 549746405488]), (7, [170725804874, 315894415939, 428430356592, 492282789291, 536879333248, 545376956141, 549739036672]), (7, [170725804874, 315894415939, 492282789291, 497964055676, 536879333248, 542424146657, 549739036672]), (7, [170725804874, 334704329303, 355153235020, 428430356592, 536879333248, 542424146657, 549739036672])]
def block86 : Cert := [(7, [170725804874, 334704329303, 373574627053, 428430356592, 536879333248, 541182623744, 549739036672]), (7, [170725804874, 355153235020, 428430356592, 492282789291, 539232731075, 542424146657, 549739036672]), (7, [170725804874, 355153235020, 463000203891, 492282789291, 536879333248, 542424146657, 549739036672]), (7, [170725804874, 373574627053, 428430356592, 492282789291, 539232731075, 541182623744, 549739036672])]
def block87 : Cert := [(7, [170725804874, 373574627053, 463000203891, 492282789291, 536879333248, 541182623744, 549739036672]), (7, [170725804874, 394009661007, 428430356592, 492282789291, 536879333248, 542424146657, 549739036672]), (7, [205649726302, 315894415939, 355153235020, 428430356592, 536879333248, 542424146657, 549739036672]), (7, [205649726302, 315894415939, 373574627053, 428430356592, 536879333248, 541182623744, 549739036672])]
def block88 : Cert := [(7, [239625645035, 315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 549755781120]), (7, [239625645035, 315894415939, 355153235020, 428430356592, 492282789291, 541182623744, 549747457920]), (7, [239625645035, 315894415939, 355153235020, 428430356592, 492282789291, 545477623680, 549739036672]), (7, [239625645035, 315894415939, 355153235020, 428430356592, 538509377492, 541182623744, 549739036672])]
def block89 : Cert := [(7, [239625645035, 315894415939, 355153235020, 492282789291, 536879333248, 541182623744, 549746405488]), (7, [239625645035, 315894415939, 428430356592, 492282789291, 536879333248, 544135433292, 549739036672]), (7, [239625645035, 315894415939, 492282789291, 497964055676, 536879333248, 541182623744, 549739036672]), (7, [239625645035, 334704329303, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672])]
def block90 : Cert := [(7, [239625645035, 355153235020, 428430356592, 492282789291, 539232731075, 541182623744, 549739036672]), (7, [239625645035, 355153235020, 463000203891, 492282789291, 536879333248, 541182623744, 549739036672]), (7, [239625645035, 394009661007, 428430356592, 492282789291, 536879333248, 541182623744, 549739036672]), (7, [274541177855, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672])]
def block91 : Cert := [(7, [315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 542424146657, 549739891530]), (7, [315894415939, 355153235020, 445611080570, 492282789291, 536879333248, 542424146657, 549739036672]), (7, [315894415939, 373574627053, 428430356592, 492282789291, 536879333248, 541182623744, 549739891530]), (7, [315894415939, 373574627053, 445611080570, 492282789291, 536879333248, 541182623744, 549739036672])]
def block92 : Cert := [(8, [57473024596, 77481386145, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 95743910625, 148176701706, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 95743910625, 170725804874, 277231304707, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 481036352896, 541182623744, 549739036672])]
def block93 : Cert := [(8, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 549755781120]), (8, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 541182623744, 549747457920]), (8, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 545477623680, 549739036672])]
def block94 : Cert := [(8, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 536879333248, 541182623744, 549746405488]), (8, [57473024596, 95743910625, 170725804874, 315894415939, 428430356592, 536879333248, 544135433292, 549739036672]), (8, [57473024596, 95743910625, 170725804874, 315894415939, 497964055676, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 95743910625, 170725804874, 355153235020, 428430356592, 539232731075, 541182623744, 549739036672])]
def block95 : Cert := [(8, [57473024596, 95743910625, 170725804874, 355153235020, 463000203891, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 95743910625, 170725804874, 394009661007, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 95743910625, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739891530]), (8, [57473024596, 95743910625, 315894415939, 355153235020, 445611080570, 536879333248, 541182623744, 549739036672])]
def block96 : Cert := [(8, [57473024596, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 542424146657, 549739036672]), (8, [57473024596, 170725804874, 315894415939, 373574627053, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [57473024596, 239625645035, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 549755781120])]
def block97 : Cert := [(8, [95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 541182623744, 549747457920]), (8, [95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 545477623680, 549739036672]), (8, [95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 538509377492, 541182623744, 549739036672]), (8, [95743910625, 170725804874, 315894415939, 355153235020, 492282789291, 536879333248, 541182623744, 549746405488])]
def block98 : Cert := [(8, [95743910625, 170725804874, 315894415939, 428430356592, 492282789291, 536879333248, 544135433292, 549739036672]), (8, [95743910625, 170725804874, 315894415939, 492282789291, 497964055676, 536879333248, 541182623744, 549739036672]), (8, [95743910625, 170725804874, 334704329303, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [95743910625, 170725804874, 355153235020, 428430356592, 492282789291, 539232731075, 541182623744, 549739036672])]
def block99 : Cert := [(8, [95743910625, 170725804874, 355153235020, 463000203891, 492282789291, 536879333248, 541182623744, 549739036672]), (8, [95743910625, 170725804874, 394009661007, 428430356592, 492282789291, 536879333248, 541182623744, 549739036672]), (8, [95743910625, 205649726302, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [95743910625, 315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 541182623744, 549739891530])]
def block100 : Cert := [(8, [95743910625, 315894415939, 355153235020, 445611080570, 492282789291, 536879333248, 541182623744, 549739036672]), (8, [134954410741, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (8, [170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 542424146657, 549739036672]), (8, [170725804874, 315894415939, 373574627053, 428430356592, 492282789291, 536879333248, 541182623744, 549739036672])]
def block101 : Cert := [(8, [239625645035, 315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 541182623744, 549739036672]), (9, [0, 57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (9, [57473024596, 95743910625, 170725804874, 315894415939, 354607434760, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (9, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 541182623744, 549739036672])]
def block102 : Cert := [(9, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672]), (9, [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672, 549755813887]), (9, [95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 492282789291, 536879333248, 541182623744, 549739036672])]
def allCert : Cert := [block0, block1, block2, block3, block4, block5, block6, block7, block8, block9, block10, block11, block12, block13, block14, block15, block16, block17, block18, block19, block20, block21, block22, block23, block24, block25, block26, block27, block28, block29, block30, block31, block32, block33, block34, block35, block36, block37, block38, block39, block40, block41, block42, block43, block44, block45, block46, block47, block48, block49, block50, block51, block52, block53, block54, block55, block56, block57, block58, block59, block60, block61, block62, block63, block64, block65, block66, block67, block68, block69, block70, block71, block72, block73, block74, block75, block76, block77, block78, block79, block80, block81, block82, block83, block84, block85, block86, block87, block88, block89, block90, block91, block92, block93, block94, block95, block96, block97, block98, block99, block100, block101, block102].flatten
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked0 : block0.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked1 : block1.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked2 : block2.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked3 : block3.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked4 : block4.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked5 : block5.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked6 : block6.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked7 : block7.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked8 : block8.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked9 : block9.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked10 : block10.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked11 : block11.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked12 : block12.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked13 : block13.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked14 : block14.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked15 : block15.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked16 : block16.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked17 : block17.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked18 : block18.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked19 : block19.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked20 : block20.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked21 : block21.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked22 : block22.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked23 : block23.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked24 : block24.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked25 : block25.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked26 : block26.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked27 : block27.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked28 : block28.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked29 : block29.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked30 : block30.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked31 : block31.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked32 : block32.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked33 : block33.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked34 : block34.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked35 : block35.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked36 : block36.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked37 : block37.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked38 : block38.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked39 : block39.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked40 : block40.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked41 : block41.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked42 : block42.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked43 : block43.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked44 : block44.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked45 : block45.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked46 : block46.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked47 : block47.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked48 : block48.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked49 : block49.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked50 : block50.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked51 : block51.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked52 : block52.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked53 : block53.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked54 : block54.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked55 : block55.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked56 : block56.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked57 : block57.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked58 : block58.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked59 : block59.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked60 : block60.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked61 : block61.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked62 : block62.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked63 : block63.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked64 : block64.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked65 : block65.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked66 : block66.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked67 : block67.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked68 : block68.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked69 : block69.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked70 : block70.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked71 : block71.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked72 : block72.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked73 : block73.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked74 : block74.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked75 : block75.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked76 : block76.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked77 : block77.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked78 : block78.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked79 : block79.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked80 : block80.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked81 : block81.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked82 : block82.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked83 : block83.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked84 : block84.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked85 : block85.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked86 : block86.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked87 : block87.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked88 : block88.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked89 : block89.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked90 : block90.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked91 : block91.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked92 : block92.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked93 : block93.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked94 : block94.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked95 : block95.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked96 : block96.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked97 : block97.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked98 : block98.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked99 : block99.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked100 : block100.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked101 : block101.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem checked102 : block102.all (closed 39 673458176 allCert) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem all_closed : ∀ e ∈ allCert, closed 39 673458176 allCert e = true := by
  intro e he
  obtain ⟨b,hb,hm⟩ := List.mem_flatten.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp checked0 e hm
  · exact List.all_eq_true.mp checked1 e hm
  · exact List.all_eq_true.mp checked2 e hm
  · exact List.all_eq_true.mp checked3 e hm
  · exact List.all_eq_true.mp checked4 e hm
  · exact List.all_eq_true.mp checked5 e hm
  · exact List.all_eq_true.mp checked6 e hm
  · exact List.all_eq_true.mp checked7 e hm
  · exact List.all_eq_true.mp checked8 e hm
  · exact List.all_eq_true.mp checked9 e hm
  · exact List.all_eq_true.mp checked10 e hm
  · exact List.all_eq_true.mp checked11 e hm
  · exact List.all_eq_true.mp checked12 e hm
  · exact List.all_eq_true.mp checked13 e hm
  · exact List.all_eq_true.mp checked14 e hm
  · exact List.all_eq_true.mp checked15 e hm
  · exact List.all_eq_true.mp checked16 e hm
  · exact List.all_eq_true.mp checked17 e hm
  · exact List.all_eq_true.mp checked18 e hm
  · exact List.all_eq_true.mp checked19 e hm
  · exact List.all_eq_true.mp checked20 e hm
  · exact List.all_eq_true.mp checked21 e hm
  · exact List.all_eq_true.mp checked22 e hm
  · exact List.all_eq_true.mp checked23 e hm
  · exact List.all_eq_true.mp checked24 e hm
  · exact List.all_eq_true.mp checked25 e hm
  · exact List.all_eq_true.mp checked26 e hm
  · exact List.all_eq_true.mp checked27 e hm
  · exact List.all_eq_true.mp checked28 e hm
  · exact List.all_eq_true.mp checked29 e hm
  · exact List.all_eq_true.mp checked30 e hm
  · exact List.all_eq_true.mp checked31 e hm
  · exact List.all_eq_true.mp checked32 e hm
  · exact List.all_eq_true.mp checked33 e hm
  · exact List.all_eq_true.mp checked34 e hm
  · exact List.all_eq_true.mp checked35 e hm
  · exact List.all_eq_true.mp checked36 e hm
  · exact List.all_eq_true.mp checked37 e hm
  · exact List.all_eq_true.mp checked38 e hm
  · exact List.all_eq_true.mp checked39 e hm
  · exact List.all_eq_true.mp checked40 e hm
  · exact List.all_eq_true.mp checked41 e hm
  · exact List.all_eq_true.mp checked42 e hm
  · exact List.all_eq_true.mp checked43 e hm
  · exact List.all_eq_true.mp checked44 e hm
  · exact List.all_eq_true.mp checked45 e hm
  · exact List.all_eq_true.mp checked46 e hm
  · exact List.all_eq_true.mp checked47 e hm
  · exact List.all_eq_true.mp checked48 e hm
  · exact List.all_eq_true.mp checked49 e hm
  · exact List.all_eq_true.mp checked50 e hm
  · exact List.all_eq_true.mp checked51 e hm
  · exact List.all_eq_true.mp checked52 e hm
  · exact List.all_eq_true.mp checked53 e hm
  · exact List.all_eq_true.mp checked54 e hm
  · exact List.all_eq_true.mp checked55 e hm
  · exact List.all_eq_true.mp checked56 e hm
  · exact List.all_eq_true.mp checked57 e hm
  · exact List.all_eq_true.mp checked58 e hm
  · exact List.all_eq_true.mp checked59 e hm
  · exact List.all_eq_true.mp checked60 e hm
  · exact List.all_eq_true.mp checked61 e hm
  · exact List.all_eq_true.mp checked62 e hm
  · exact List.all_eq_true.mp checked63 e hm
  · exact List.all_eq_true.mp checked64 e hm
  · exact List.all_eq_true.mp checked65 e hm
  · exact List.all_eq_true.mp checked66 e hm
  · exact List.all_eq_true.mp checked67 e hm
  · exact List.all_eq_true.mp checked68 e hm
  · exact List.all_eq_true.mp checked69 e hm
  · exact List.all_eq_true.mp checked70 e hm
  · exact List.all_eq_true.mp checked71 e hm
  · exact List.all_eq_true.mp checked72 e hm
  · exact List.all_eq_true.mp checked73 e hm
  · exact List.all_eq_true.mp checked74 e hm
  · exact List.all_eq_true.mp checked75 e hm
  · exact List.all_eq_true.mp checked76 e hm
  · exact List.all_eq_true.mp checked77 e hm
  · exact List.all_eq_true.mp checked78 e hm
  · exact List.all_eq_true.mp checked79 e hm
  · exact List.all_eq_true.mp checked80 e hm
  · exact List.all_eq_true.mp checked81 e hm
  · exact List.all_eq_true.mp checked82 e hm
  · exact List.all_eq_true.mp checked83 e hm
  · exact List.all_eq_true.mp checked84 e hm
  · exact List.all_eq_true.mp checked85 e hm
  · exact List.all_eq_true.mp checked86 e hm
  · exact List.all_eq_true.mp checked87 e hm
  · exact List.all_eq_true.mp checked88 e hm
  · exact List.all_eq_true.mp checked89 e hm
  · exact List.all_eq_true.mp checked90 e hm
  · exact List.all_eq_true.mp checked91 e hm
  · exact List.all_eq_true.mp checked92 e hm
  · exact List.all_eq_true.mp checked93 e hm
  · exact List.all_eq_true.mp checked94 e hm
  · exact List.all_eq_true.mp checked95 e hm
  · exact List.all_eq_true.mp checked96 e hm
  · exact List.all_eq_true.mp checked97 e hm
  · exact List.all_eq_true.mp checked98 e hm
  · exact List.all_eq_true.mp checked99 e hm
  · exact List.all_eq_true.mp checked100 e hm
  · exact List.all_eq_true.mp checked101 e hm
  · exact List.all_eq_true.mp checked102 e hm

def sample (p : Fin 39) : Fin 9 → Bool := fun i => (([10, 12, 17, 20, 33, 34, 63, 66, 68, 79, 80, 84, 96, 98, 121, 129, 132, 136, 140, 151, 160, 161, 186, 219, 257, 258, 264, 266, 272, 273, 295, 316, 365, 438, 455, 457, 466, 484, 504] : List ℕ).getD p.val 0).testBit i.val

def target (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def inCols : List ℕ := [57473024596, 95743910625, 170725804874, 315894415939, 355153235020, 428430356592, 536879333248, 541182623744, 549739036672, 492282789291, 354607434760]

def extend (w : List Bool) : List Bool :=
  (w ++ [!(w.getD 0 false)]) ++ [GateOp.and.eval [ (w ++ [!(w.getD 0 false)]).getD 4 false, (w ++ [!(w.getD 0 false)]).getD 9 false]]

theorem rowMatch (p : Fin 39) : inCols.map (fun t => t.testBit p.val) = extend (List.ofFn (sample p)) := by
  have h : ∀ q : Fin 39, inCols.map (fun t => t.testBit q.val) = extend (List.ofFn (sample q)) := by decide +kernel
  exact h p

theorem targetMatch (p : Fin 39) : target (sample p) = (673458176 : ℕ).testBit p.val := by
  have h : ∀ q : Fin 39, target (sample q) = (673458176 : ℕ).testBit q.val := by decide +kernel
  exact h p

theorem suffixEval (gs : List Gate) (o : ℕ) (w : List Bool) :
    (⟨⟨GateOp.not, [0]⟩ :: ⟨GateOp.and, [4, 9]⟩ :: gs, o⟩ : Circuit).eval w =
      (⟨gs,o⟩ : Circuit).eval (extend w) := by
  rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem impossible : ¬ ∃ C : Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ ∀ p < 39, C.eval (inCols.map fun t => t.testBit p) = (673458176 : ℕ).testBit p := by
  exact no_circuit_on_certificate 39 673458176 9 inCols (by decide) allCert all_closed (by decide +kernel)

end PEqualNP.Outside.L_meta_27434_aux

open PEqualNP.Outside.L_meta_27434_aux PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_27434 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
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
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.not, [0]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [4, 9]⟩)) := by
  rintro ⟨C,hC,hs,he,_,_,_,_,h1,h2⟩
  rcases C with ⟨gs,o⟩
  cases gs with
  | nil => simp at h1
  | cons a tail =>
    cases tail with
    | nil => simp at h2
    | cons b rest =>
      simp only [List.head?_cons, Option.some.injEq] at h1
      change some b = some ⟨GateOp.and,[4,9]⟩ at h2
      injection h2 with hb
      subst a
      subst b
      apply impossible
      refine ⟨(⟨rest,o⟩ : Circuit),?_,?_,?_⟩
      · intro g hg
        exact hC g (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hg))
      · change rest.length ≤ 9
        change rest.length + 2 ≤ 11 at hs
        omega
      · intro p hp
        let q : Fin 39 := ⟨p,hp⟩
        change (⟨rest,o⟩ : Circuit).eval (inCols.map (fun t => t.testBit q.val)) = (673458176 : ℕ).testBit q.val
        rw [rowMatch q, ← targetMatch q, ← suffixEval]
        exact he (sample q)
