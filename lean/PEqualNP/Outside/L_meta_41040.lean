import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41040_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 16000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 16000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 16000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 16000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 500

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 250 := ((x >>> 250) ^^^ x).setWidth 250
def cuts (ws : List W) : BitVec 250 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 250) ++ (0 : BitVec 250)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 16000 in
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

set_option maxRecDepth 16000 in
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 250) (w : W) : Prop :=
  w.getLsbD (250+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 16000 in
theorem ops_differs (i : Fin 250) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 250+i.val < 500 := by omega
  have hi' : i.val < 500 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 16000 in
theorem cuts_spec (ws : List W) (i : Fin 250) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 16000 in
theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 250)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 16000 in
theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 16000 in
theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
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

set_option maxRecDepth 16000 in
theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

noncomputable section Fast

def M120 : ℕ := ((((((((0xfffff * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff)
def M60 : ℕ := ((((0x3ff * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff)
def P60 : ℕ := ((((0x400 * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def gN : ℕ := ((((((((0xfffff * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xfffffffffffffff) * 2^60 + 0xffffffffffffc00) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)

def nsep (x : ℕ) : ℕ := Nat.mod (Nat.xor (Nat.shiftRight x 250) x) P60

def ncuts (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun w _ ih => Nat.lor (nsep w) ih) ws

def len (ws : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun _ _ ih => Nat.succ ih) ws

def nisGoal (ws : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun w t _ => List.rec (motive := fun _ => Bool)
      (Bool.rec (Nat.beq w M60) true (Nat.beq w gN)) (fun _ _ _ => false) t) ws

def frc (w : ℕ) (k : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k Nat.zero) (fun m _ => k (Nat.succ m)) w

def revK (xs : List ℕ) (acc : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool) (fun acc => k acc) (fun x _ ih acc => ih (x :: acc))
    xs acc

def insK (w : ℕ) (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [w])
    (fun x xs ih k => Bool.rec (ih (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x)) l k

def call (next : List ℕ → Bool) (c : List ℕ) : Bool := Bool.rec false true (next c)

def orB (x y : Bool) : Bool := Bool.rec y true x

def one0 (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) : Bool :=
  Bool.rec false
    (frc w (fun w2 => revK mid post (fun m => revK pre m (fun r =>
      insK w2 r (fun c => call next c)))))
    (Nat.beq (Nat.lor (nsep w) base) M60)

def pair0 (next : List ℕ → Bool) (a b _sa _sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (one0 next base pre mid post (Nat.land a b))
  (orB (one0 next base pre mid post (Nat.lor a b))
  (orB (one0 next base pre mid post (Nat.land a (Nat.sub M120 b)))
    (one0 next base pre mid post (Nat.land b (Nat.sub M120 a)))))

def reb (pre mid post : List ℕ) (k : List ℕ → Bool) : Bool :=
  revK mid post (fun m => revK pre m k)

def oneG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    Bool :=
  frc w (fun w2 =>
    orB (Bool.rec false (reb pre mid post (fun r => insK w2 r (fun c => call next c)))
      (Nat.beq (Nat.lor (nsep w2) base) M60))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK a r (fun r1 => insK w2 r1 (fun c => call next c))))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sa) M60))
    (orB (Bool.rec false
        (reb pre mid post (fun r => insK b r (fun r1 => insK w2 r1 (fun c => call next c))))
      (Nat.beq (Nat.lor (Nat.lor (nsep w2) base) sb) M60))
      (Bool.rec false
        (reb pre mid post (fun r =>
          insK b r (fun r1 => insK a r1 (fun r2 => insK w2 r2 (fun c => call next c)))))
        (Nat.ble 2 extra)))))

def pairG (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) : Bool :=
  orB (oneG next extra a b sa sb base pre mid post (Nat.land a b))
  (orB (oneG next extra a b sa sb base pre mid post (Nat.lor a b))
  (orB (oneG next extra a b sa sb base pre mid post (Nat.land a (Nat.sub M120 b)))
    (oneG next extra a b sa sb base pre mid post (Nat.land b (Nat.sub M120 a)))))

def innerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a sa : ℕ)
    (pre : List ℕ) (preCut : ℕ) (rest mid : List ℕ) (midCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun b post ih mid midCut =>
      Bool.rec (ih (b :: mid) (Nat.lor midCut (nsep b))) true
        (P a b sa (nsep b) (Nat.lor (Nat.lor preCut midCut) (ncuts post)) pre mid post))
    rest mid midCut

def outerAux (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (ws pre : List ℕ)
    (preCut : ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → ℕ → Bool) (fun _ _ => false)
    (fun a rest ih pre preCut =>
      Bool.rec (ih (a :: pre) (Nat.lor preCut (nsep a))) true
        (innerAux P a (nsep a) pre preCut rest [] 0))
    ws pre preCut

def stepF (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) : Bool :=
  Bool.rec
    (Bool.rec (outerAux (pairG next (Nat.sub (Nat.succ (Nat.succ k1)) (len ws))) ws [] 0)
      (outerAux (pair0 next) ws [] 0) (Nat.beq (len ws) (Nat.succ (Nat.succ k1))))
    true (nisGoal ws)

def nopt (k : ℕ) (ws : List ℕ) : Bool :=
  Nat.rec (motive := fun _ => List ℕ → Bool) (fun ws => nisGoal ws)
    (fun k1 ih ws => stepF k1 ih ws) k ws

def ins (w : ℕ) : List ℕ → List ℕ
  | [] => [w]
  | x :: xs => if Nat.ble w x = true then w :: x :: xs else x :: ins w xs

def cutR (l : List ℕ) : ℕ := l.foldr (fun x c => Nat.lor c (nsep x)) 0

def baseOf (pre mid post : List ℕ) : ℕ := Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post)

def rOf (pre mid post : List ℕ) : List ℕ := pre.reverse ++ (mid.reverse ++ post)

def opsN (a b : ℕ) : List ℕ :=
  [Nat.land a b, Nat.lor a b, Nat.land a (Nat.sub M120 b), Nat.land b (Nat.sub M120 a)]

abbrev Split := List ℕ × ℕ × List ℕ × ℕ × List ℕ

def innerS (pre : List ℕ) (a : ℕ) : List ℕ → List ℕ → List Split
  | [], _ => []
  | b :: post, mid => (pre, a, mid, b, post) :: innerS pre a post (b :: mid)

def outerS : List ℕ → List ℕ → List Split
  | [], _ => []
  | a :: rest, pre => innerS pre a rest [] ++ outerS rest (a :: pre)

def kids0 (base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  if Nat.beq (Nat.lor (nsep w) base) M60 = true then [ins w r] else []

def kidsG (extra a b sa sb base : ℕ) (r : List ℕ) (w : ℕ) : List (List ℕ) :=
  (if Nat.beq (Nat.lor (nsep w) base) M60 = true then [ins w r] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = true then [ins w (ins a r)] else []) ++
  ((if Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = true then [ins w (ins b r)] else []) ++
   (if Nat.ble 2 extra = true then [ins w (ins a (ins b r))] else [])))

def kidsPair0 (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap (kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsPairG (extra : ℕ) (t : Split) : List (List ℕ) :=
  (opsN t.2.1 t.2.2.2.1).flatMap
    (kidsG extra t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
      (rOf t.1 t.2.2.1 t.2.2.2.2))

def kidsL (k1 : ℕ) (ws : List ℕ) : List (List ℕ) :=
  if Nat.beq (len ws) (Nat.succ (Nat.succ k1)) = true then (outerS ws []).flatMap kidsPair0
  else (outerS ws []).flatMap (kidsPairG (Nat.sub (Nat.succ (Nat.succ k1)) (len ws)))

set_option maxRecDepth 16000 in
theorem brec {α : Type} (f t : α) (c : Bool) :
    (Bool.rec (motive := fun _ => α) f t c) = if c = true then t else f := by
  cases c <;> rfl

set_option maxRecDepth 16000 in
theorem frc_eq (w : ℕ) (k : ℕ → Bool) : frc w k = k w := by
  cases w <;> rfl

set_option maxRecDepth 16000 in
theorem revK_eq (xs : List ℕ) : ∀ (acc : List ℕ) (k : List ℕ → Bool),
    revK xs acc k = k (xs.reverse ++ acc) := by
  induction xs with
  | nil => intro acc k; rfl
  | cons x xs ih =>
    intro acc k
    have e : revK (x :: xs) acc k = revK xs (x :: acc) k := rfl
    rw [e, ih]
    simp

set_option maxRecDepth 16000 in
theorem insK_eq (w : ℕ) (l : List ℕ) : ∀ k : List ℕ → Bool, insK w l k = k (ins w l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : insK w (x :: xs) k =
        Bool.rec (insK w xs (fun l2 => k (x :: l2))) (k (w :: x :: xs)) (Nat.ble w x) := rfl
    rw [e, brec, ih]
    by_cases h : Nat.ble w x = true <;> simp [ins, h]

set_option maxRecDepth 16000 in
theorem call_eq (next : List ℕ → Bool) (c : List ℕ) : call next c = next c := by
  unfold call
  cases next c <;> rfl

set_option maxRecDepth 16000 in
theorem orB_eq (x y : Bool) : orB x y = (x || y) := by
  cases x <;> rfl

set_option maxRecDepth 16000 in
theorem one0_eq (next : List ℕ → Bool) (base : ℕ) (pre mid post : List ℕ) (w : ℕ) :
    one0 next base pre mid post w = (kids0 base (rOf pre mid post) w).any next := by
  unfold one0 kids0 rOf
  rw [brec]
  generalize Nat.beq (Nat.lor (nsep w) base) M60 = c
  cases c <;> simp [frc_eq, revK_eq, insK_eq, call_eq]

set_option maxRecDepth 16000 in
theorem oneG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ)
    (w : ℕ) :
    oneG next extra a b sa sb base pre mid post w =
      (kidsG extra a b sa sb base (rOf pre mid post) w).any next := by
  unfold oneG kidsG rOf reb
  simp only [frc_eq, revK_eq, insK_eq, call_eq, orB_eq, brec, List.any_append]
  generalize Nat.beq (Nat.lor (nsep w) base) M60 = c1
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = c2
  generalize Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = c3
  generalize Nat.ble 2 extra = c4
  cases c1 <;> cases c2 <;> cases c3 <;> cases c4 <;> simp

set_option maxRecDepth 16000 in
theorem pair0_eq (next : List ℕ → Bool) (a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pair0 next a b sa sb base pre mid post =
      ((opsN a b).flatMap (kids0 base (rOf pre mid post))).any next := by
  unfold pair0 opsN
  simp only [orB_eq, one0_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

set_option maxRecDepth 16000 in
theorem pairG_eq (next : List ℕ → Bool) (extra a b sa sb base : ℕ) (pre mid post : List ℕ) :
    pairG next extra a b sa sb base pre mid post =
      ((opsN a b).flatMap (kidsG extra a b sa sb base (rOf pre mid post))).any next := by
  unfold pairG opsN
  simp only [orB_eq, oneG_eq, List.flatMap_cons, List.flatMap_nil, List.any_append,
    List.any_nil, Bool.or_false]

def HP (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (t : Split) : Bool :=
  P t.2.1 t.2.2.2.1 (nsep t.2.1) (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2)
    t.1 t.2.2.1 t.2.2.2.2

set_option maxRecDepth 16000 in
theorem innerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) (a : ℕ)
    (pre : List ℕ) : ∀ rest mid : List ℕ,
    innerAux P a (nsep a) pre (cutR pre) rest mid (cutR mid) =
      (innerS pre a rest mid).any (HP P) := by
  intro rest
  induction rest with
  | nil => intro mid; rfl
  | cons b post ih =>
    intro mid
    have e : innerAux P a (nsep a) pre (cutR pre) (b :: post) mid (cutR mid) =
        Bool.rec (innerAux P a (nsep a) pre (cutR pre) post (b :: mid)
            (Nat.lor (cutR mid) (nsep b)))
          true (P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
            pre mid post) := rfl
    have c : Nat.lor (cutR mid) (nsep b) = cutR (b :: mid) := rfl
    rw [e, brec, c, ih]
    simp only [innerS, List.any_cons, HP, baseOf]
    cases P a b (nsep a) (nsep b) (Nat.lor (Nat.lor (cutR pre) (cutR mid)) (ncuts post))
      pre mid post <;> simp

set_option maxRecDepth 16000 in
theorem outerAux_eq (P : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → List ℕ → List ℕ → Bool) :
    ∀ ws pre : List ℕ, outerAux P ws pre (cutR pre) = (outerS ws pre).any (HP P) := by
  intro ws
  induction ws with
  | nil => intro pre; rfl
  | cons a rest ih =>
    intro pre
    have e : outerAux P (a :: rest) pre (cutR pre) =
        Bool.rec (outerAux P rest (a :: pre) (Nat.lor (cutR pre) (nsep a))) true
          (innerAux P a (nsep a) pre (cutR pre) rest [] 0) := rfl
    have c : Nat.lor (cutR pre) (nsep a) = cutR (a :: pre) := rfl
    have z : (0 : ℕ) = cutR [] := rfl
    rw [e, brec, c, ih, z, innerAux_eq]
    simp only [outerS, List.any_append]
    cases (innerS pre a rest []).any (HP P) <;> simp

set_option maxRecDepth 16000 in
theorem HP_pair0 (next : List ℕ → Bool) :
    HP (pair0 next) = fun t => (kidsPair0 t).any next := by
  funext t
  simp only [HP, pair0_eq, kidsPair0]

set_option maxRecDepth 16000 in
theorem HP_pairG (next : List ℕ → Bool) (extra : ℕ) :
    HP (pairG next extra) = fun t => (kidsPairG extra t).any next := by
  funext t
  simp only [HP, pairG_eq, kidsPairG]

set_option maxRecDepth 16000 in
theorem stepF_eq (k1 : ℕ) (next : List ℕ → Bool) (ws : List ℕ) :
    stepF k1 next ws = (nisGoal ws || (kidsL k1 ws).any next) := by
  have z : (0 : ℕ) = cutR [] := rfl
  unfold stepF kidsL
  rw [brec, brec, z, outerAux_eq, outerAux_eq, HP_pair0, HP_pairG]
  cases nisGoal ws
  · cases Nat.beq (len ws) (Nat.succ (Nat.succ k1)) <;> simp [List.any_flatMap]
  · simp

set_option maxRecDepth 16000 in
theorem nopt_zero (ws : List ℕ) : nopt 0 ws = nisGoal ws := rfl

set_option maxRecDepth 16000 in
theorem nopt_succ (k : ℕ) (ws : List ℕ) :
    nopt (k + 1) ws = (nisGoal ws || (kidsL k ws).any (nopt k)) := by
  rw [← stepF_eq]
  rfl

end Fast

noncomputable section Bridge

set_option maxRecDepth 16000 in
theorem beq_of_eq {a b : ℕ} (h : a = b) : Nat.beq a b = true := h ▸ Nat.beq_refl a

set_option maxRecDepth 16000 in
theorem negOne60 : (-1 : BitVec 250).toNat = M60 := by decide +kernel

set_option maxRecDepth 16000 in
theorem nsep_toNat (w : W) : nsep w.toNat = (sep w).toNat := by
  simp only [nsep, sep, BitVec.toNat_setWidth, BitVec.toNat_xor, BitVec.toNat_ushiftRight]
  rfl

set_option maxRecDepth 16000 in
theorem ncuts_cons (w : ℕ) (ws : List ℕ) : ncuts (w :: ws) = Nat.lor (nsep w) (ncuts ws) := rfl

set_option maxRecDepth 16000 in
theorem cuts_cons (a : W) (l : List W) : cuts (a :: l) = sep a ||| cuts l := rfl

set_option maxRecDepth 16000 in
theorem ncuts_map (l : List W) : ncuts (l.map BitVec.toNat) = (cuts l).toNat := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, ncuts_cons, cuts_cons, BitVec.toNat_or, ih, nsep_toNat]
    rfl

set_option maxRecDepth 16000 in
theorem ncuts_append (l1 l2 : List ℕ) : ncuts (l1 ++ l2) = Nat.lor (ncuts l1) (ncuts l2) := by
  induction l1 with
  | nil =>
    have e : ncuts ([] : List ℕ) = 0 := rfl
    rw [List.nil_append, e]
    exact (Nat.zero_or _).symm
  | cons a l ih =>
    rw [List.cons_append, ncuts_cons, ih, ncuts_cons]
    exact (Nat.or_assoc _ _ _).symm

set_option maxRecDepth 16000 in
theorem cutR_eq (l : List ℕ) : cutR l = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : cutR (a :: l) = Nat.lor (cutR l) (nsep a) := rfl
    rw [e, ih, ncuts_cons]
    exact Nat.or_comm _ _

set_option maxRecDepth 16000 in
theorem ncuts_reverse (l : List ℕ) : ncuts l.reverse = ncuts l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e1 : ncuts [a] = nsep a ||| 0 := rfl
    have e2 : ncuts (a :: l) = nsep a ||| ncuts l := rfl
    rw [List.reverse_cons, ncuts_append, ih, e1, e2]
    change (ncuts l ||| (nsep a ||| 0)) = (nsep a ||| ncuts l)
    rw [Nat.or_zero, Nat.or_comm]

set_option maxRecDepth 16000 in
theorem baseOf_map (xs ys zs : List W) :
    baseOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse (zs.map BitVec.toNat) =
      (cuts (xs ++ (ys ++ zs))).toNat := by
  rw [← ncuts_map, List.map_append, List.map_append, ncuts_append, ncuts_append]
  unfold baseOf
  rw [cutR_eq, cutR_eq, ncuts_reverse, ncuts_reverse]
  exact Nat.or_assoc _ _ _

set_option maxRecDepth 16000 in
theorem opsN_map (a b : W) : opsN a.toNat b.toNat = (ops a b).map BitVec.toNat := by
  simp only [opsN, ops, List.map_cons, List.map_nil, BitVec.toNat_and, BitVec.toNat_or,
    BitVec.toNat_not]
  rfl

set_option maxRecDepth 16000 in
theorem len_eq (l : List ℕ) : len l = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have e : len (a :: l) = Nat.succ (len l) := rfl
    rw [e, ih]
    rfl

def insW (w : W) : List W → List W
  | [] => [w]
  | x :: xs => if Nat.ble w.toNat x.toNat = true then w :: x :: xs else x :: insW w xs

set_option maxRecDepth 16000 in
theorem insW_map (w : W) (l : List W) :
    (insW w l).map BitVec.toNat = ins w.toNat (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [insW, ins, List.map_cons]
    split_ifs
    · rfl
    · rw [List.map_cons, ih]

set_option maxRecDepth 16000 in
theorem insW_perm (w : W) (l : List W) : (insW w l).Perm (w :: l) := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insW]
    split_ifs
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

set_option maxRecDepth 16000 in
theorem mem_innerS (pre : List ℕ) (a b : ℕ) (zs : List ℕ) : ∀ ys mid : List ℕ,
    (pre, a, ys.reverse ++ mid, b, zs) ∈ innerS pre a (ys ++ b :: zs) mid := by
  intro ys
  induction ys with
  | nil => intro mid; simp [innerS]
  | cons y ys ih =>
    intro mid
    simp only [List.cons_append, innerS, List.reverse_cons, List.append_assoc]
    exact List.mem_cons_of_mem _ (ih (y :: mid))

set_option maxRecDepth 16000 in
theorem mem_outerS (a b : ℕ) (ys zs : List ℕ) : ∀ xs pre : List ℕ,
    (xs.reverse ++ pre, a, ys.reverse, b, zs) ∈ outerS (xs ++ a :: (ys ++ b :: zs)) pre := by
  intro xs
  induction xs with
  | nil =>
    intro pre
    simp only [List.nil_append, List.reverse_nil, outerS]
    exact List.mem_append_left _ (by simpa using mem_innerS pre a b zs ys [])
  | cons x xs ih =>
    intro pre
    simp only [List.cons_append, outerS, List.reverse_cons, List.append_assoc]
    exact List.mem_append_right _ (ih (x :: pre))

set_option maxRecDepth 16000 in
theorem split_two {α : Type} {a b : α} {l : List α} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    (∃ xs ys zs, l = xs ++ a :: (ys ++ b :: zs)) ∨ (∃ xs ys zs, l = xs ++ b :: (ys ++ a :: zs)) := by
  obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
  rcases List.mem_append.mp hb with h | h
  · obtain ⟨s1, s2, rfl⟩ := List.append_of_mem h
    exact .inr ⟨s1, s2, t, by simp⟩
  · rcases List.mem_cons.mp h with h | h
    · exact absurd h.symm hne
    · obtain ⟨t1, t2, rfl⟩ := List.append_of_mem h
      exact .inl ⟨s, t1, t2, rfl⟩

set_option maxRecDepth 16000 in
theorem nisGoal_goal {g : W} (hg : g = goal ∨ g = ~~~goal) : nisGoal [g.toNat] = true := by
  rcases hg with rfl | rfl <;> decide +kernel

set_option maxRecDepth 16000 in
theorem mem_kids0 {base w : ℕ} {r : List ℕ} (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kids0 base r w := by
  unfold kids0
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG1 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (nsep w) base) M60 = true) :
    ins w r ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_left _ ?_
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG2 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sa) M60 = true) :
    ins w (ins a r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_left _ ?_)
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG3 {extra a b sa sb base w : ℕ} {r : List ℕ}
    (h : Nat.beq (Nat.lor (Nat.lor (nsep w) base) sb) M60 = true) :
    ins w (ins b r) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsG4 {extra a b sa sb base w : ℕ} {r : List ℕ} (h : Nat.ble 2 extra = true) :
    ins w (ins a (ins b r)) ∈ kidsG extra a b sa sb base r w := by
  unfold kidsG
  refine List.mem_append_right _ (List.mem_append_right _ (List.mem_append_right _ ?_))
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
  exact List.mem_singleton.mpr rfl

set_option maxRecDepth 16000 in
theorem mem_kidsL {k : ℕ} {wsN : List ℕ} {t : Split} {w : ℕ} {c : List ℕ}
    (ht : t ∈ outerS wsN []) (hw : w ∈ opsN t.2.1 t.2.2.2.1)
    (h0 : Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kids0 (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w)
    (hG : ¬ Nat.beq (len wsN) (Nat.succ (Nat.succ k)) = true →
      c ∈ kidsG (Nat.sub (Nat.succ (Nat.succ k)) (len wsN)) t.2.1 t.2.2.2.1 (nsep t.2.1)
        (nsep t.2.2.2.1) (baseOf t.1 t.2.2.1 t.2.2.2.2) (rOf t.1 t.2.2.1 t.2.2.2.2) w) :
    c ∈ kidsL k wsN := by
  unfold kidsL
  split_ifs with hd
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, h0 hd⟩⟩
  · exact List.mem_flatMap.mpr ⟨t, ht, List.mem_flatMap.mpr ⟨w, hw, hG hd⟩⟩

set_option maxRecDepth 16000 in
theorem guard1 {z : W} {r : List W} (h : cuts (z :: r) = -1) :
    Nat.beq (Nat.lor (nsep z.toNat) (cuts r).toNat) M60 = true := by
  rw [cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, ← nsep_toNat, negOne60] at e
  exact beq_of_eq e

set_option maxRecDepth 16000 in
theorem guard2 {z a : W} {r : List W} (h : cuts (z :: a :: r) = -1) :
    Nat.beq (Nat.lor (Nat.lor (nsep z.toNat) (cuts r).toNat) (nsep a.toNat)) M60 = true := by
  rw [cuts_cons, cuts_cons] at h
  have e := congrArg BitVec.toNat h
  rw [BitVec.toNat_or, BitVec.toNat_or, ← nsep_toNat, ← nsep_toNat, negOne60] at e
  refine beq_of_eq (Eq.trans ?_ e)
  change (nsep z.toNat ||| (cuts r).toNat ||| nsep a.toNat) =
    (nsep z.toNat ||| (nsep a.toNat ||| (cuts r).toNat))
  rw [Nat.or_assoc, Nat.or_comm (cuts r).toNat]

set_option maxRecDepth 16000 in
theorem child_of_split {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws xs ys zs : List W}
    {a b z : W} {needed : Finset W} (hn : ws.Nodup)
    (hsplit : ws = xs ++ a :: (ys ++ b :: zs)) (hz : z ∈ basicOps a b) (hout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (tail : live basicOps g k (insert z needed)) :
    ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  have p1 : (xs ++ a :: (ys ++ b :: zs)).Perm (a :: (xs ++ (ys ++ b :: zs))) := List.perm_middle
  have p2 : (xs ++ (ys ++ b :: zs)).Perm (b :: (xs ++ (ys ++ zs))) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_middle
  have perm : ws.Perm (a :: b :: (xs ++ (ys ++ zs))) := hsplit ▸ p1.trans (p2.cons a)
  obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hs
  have hznew : z ∉ kept := by
    intro hu
    apply hout
    rw [hs]
    exact Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
  have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
  have hl2 : live basicOps g k (z :: kept).toFinset := by
    simpa [hfin] using tail
  have hc := live_card hl2
  rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
  have hcut := cuts_full hg hl2
  have hlen2 := perm.length_eq
  simp only [List.length_cons] at hlen2
  have hmap : ws.map BitVec.toNat = xs.map BitVec.toNat ++
      a.toNat :: (ys.map BitVec.toNat ++ b.toNat :: zs.map BitVec.toNat) := by
    rw [hsplit]
    simp
  have ht := mem_outerS a.toNat b.toNat (ys.map BitVec.toNat) (zs.map BitVec.toNat)
    (xs.map BitVec.toNat) []
  rw [List.append_nil, ← hmap] at ht
  have hzN : z.toNat ∈ opsN a.toNat b.toNat := by
    rw [opsN_map]
    exact List.mem_map_of_mem (List.mem_toFinset.mp hz)
  have hr : rOf (xs.map BitVec.toNat).reverse (ys.map BitVec.toNat).reverse
      (zs.map BitVec.toNat) = (xs ++ (ys ++ zs)).map BitVec.toNat := by
    simp [rOf]
  have hbase := baseOf_map xs ys zs
  have hlenN : len (ws.map BitVec.toNat) = ws.length := by
    rw [len_eq, List.length_map]
  have live_of (cW : List W) (hp : cW.Perm (z :: kept)) :
      cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset := by
    refine ⟨hp.nodup_iff.mpr hnd, ?_, ?_⟩
    · rw [hp.length_eq, List.length_cons]
      exact hc
    · have e : cW.toFinset = (z :: kept).toFinset := List.toFinset_eq_of_perm _ _ hp
      rw [e]
      exact hl2
  simp only [keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · refine ⟨insW z (xs ++ (ys ++ zs)), (live_of _ (insW_perm _ _)).1, (live_of _ (insW_perm _ _)).2.1,
      (live_of _ (insW_perm _ _)).2.2, ?_⟩
    rw [insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro _
      simp only [hr, hbase]
      exact mem_kids0 (guard1 hcut)
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG1 (guard1 hcut)
  · have hp : (insW z (insW a (xs ++ (ys ++ zs)))).Perm (z :: a :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG2 (guard2 hcut)
  · have hp : (insW z (insW b (xs ++ (ys ++ zs)))).Perm (z :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans ((insW_perm _ _).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map]
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      simp only [List.length_cons] at hc
      omega
    · intro _
      simp only [hr, hbase]
      exact mem_kidsG3 (guard2 hcut)
  · have hp : (insW z (insW a (insW b (xs ++ (ys ++ zs))))).Perm
        (z :: a :: b :: (xs ++ (ys ++ zs))) :=
      (insW_perm _ _).trans (((insW_perm _ _).trans ((insW_perm _ _).cons a)).cons z)
    refine ⟨_, (live_of _ hp).1, (live_of _ hp).2.1, (live_of _ hp).2.2, ?_⟩
    rw [insW_map, insW_map, insW_map]
    simp only [List.length_cons] at hc
    refine mem_kidsL ht hzN ?_ ?_
    · intro hd
      exfalso
      rw [hlenN] at hd
      have := Nat.eq_of_beq_eq_true hd
      omega
    · intro _
      simp only [hr]
      refine mem_kidsG4 ?_
      rw [hlenN]
      apply Nat.ble_eq_true_of_le
      change 2 ≤ k + 2 - ws.length
      omega

set_option maxRecDepth 16000 in
theorem child_exists {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (hl : live basicOps g (k + 1) ws.toFinset) :
    ws = [g] ∨ ∃ cW : List W, cW.Nodup ∧ cW.length ≤ k + 1 ∧ live basicOps g k cW.toFinset ∧
      cW.map BitVec.toNat ∈ kidsL k (ws.map BitVec.toNat) := by
  rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact .inl (singleton_list hn done)
  · right
    rcases split_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab with
      ⟨xs, ys, zs, e⟩ | ⟨xs, ys, zs, e⟩
    · exact child_of_split hg hn e hz hout hs tail
    · exact child_of_split hg hn e (ops_swap a b ▸ hz) hout
        (by rw [hs, Finset.insert_comm]) tail

set_option maxRecDepth 16000 in
theorem nopt_complete {g : W} (hg : g = goal ∨ g = ~~~goal) : ∀ (k : ℕ) (ws : List W),
    ws.Nodup → live basicOps g k ws.toFinset → nopt k (ws.map BitVec.toNat) = true := by
  intro k
  induction k with
  | zero =>
    intro ws hn h
    have e := singleton_list hn h
    rw [e]
    exact nisGoal_goal hg
  | succ k ih =>
    intro ws hn hl
    rw [nopt_succ]
    rcases child_exists hg hn hl with e | ⟨cW, hcn, _, hcl, hmem⟩
    · rw [e]
      have := nisGoal_goal hg
      simp only [List.map_cons, List.map_nil, this, Bool.true_or]
    · have := ih cW hcn hcl
      rw [Bool.or_eq_true]
      exact .inr (List.any_eq_true.mpr ⟨_, hmem, this⟩)

def rootsN (n : ℕ) (insN : List ℕ) : List (List ℕ) :=
  insN.sublists.filter (fun ws => Nat.ble ws.length (n + 1) && Nat.beq (ncuts ws) M60)

def allKids (m : ℕ) (insN : List ℕ) : List (List ℕ) := (rootsN (m + 1) insN).flatMap (kidsL m)

def isort (l : List ℕ) : List ℕ := l.foldr ins []

def sortK (l : List ℕ) (k : List ℕ → Bool) : Bool :=
  List.rec (motive := fun _ => (List ℕ → Bool) → Bool) (fun k => k [])
    (fun x _ ih k => ih (fun s => frc x (fun x2 => insK x2 s k))) l k

set_option maxRecDepth 16000 in
theorem sortK_eq (l : List ℕ) : ∀ k : List ℕ → Bool, sortK l k = k (isort l) := by
  induction l with
  | nil => intro k; rfl
  | cons x xs ih =>
    intro k
    have e : sortK (x :: xs) k = sortK xs (fun s => frc x (fun x2 => insK x2 s k)) := rfl
    rw [e, ih, frc_eq, insK_eq]
    rfl

def isortW (l : List W) : List W := l.foldr insW []

set_option maxRecDepth 16000 in
theorem isortW_map (l : List W) :
    (isortW l).map BitVec.toNat = isort (l.map BitVec.toNat) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have e1 : isortW (x :: xs) = insW x (isortW xs) := rfl
    have e2 : isort (x.toNat :: xs.map BitVec.toNat) =
        ins x.toNat (isort (xs.map BitVec.toNat)) := rfl
    rw [List.map_cons, e1, e2, insW_map, ih]

set_option maxRecDepth 16000 in
theorem isortW_perm (l : List W) : (isortW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (insW_perm x (isortW xs)).trans (ih.cons x)

def dead (m : ℕ) (c : List ℕ) : Bool := sortK c (fun c2 => Bool.rec true false (nopt m c2))

set_option maxRecDepth 16000 in
theorem dead_eq (m : ℕ) (c : List ℕ) : dead m c = !nopt m (isort c) := by
  unfold dead
  rw [sortK_eq, brec]
  cases nopt m (isort c) <;> rfl

set_option maxRecDepth 16000 in
theorem refute (m : ℕ) (inputs : List W) (hnd : inputs.Nodup)
    (h0 : (rootsN (m + 1) (inputs.map BitVec.toNat)).all (fun ws => !nisGoal ws) = true)
    (hk : (allKids m (inputs.map BitVec.toNat)).all (dead m) = true) :
    ∀ t, t = goal ∨ t = ~~~goal → build basicOps t (m + 1) inputs.toFinset → False := by
  intro g hg hb
  classical
  obtain ⟨s, hs, hl⟩ := compress hb
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd2 : ws.Nodup := hnd.filter _
  have hl2 : live basicOps g (m + 1) ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl2
  rw [List.toFinset_card_of_nodup hnd2] at sz
  have hroot : ws.map BitVec.toNat ∈ rootsN (m + 1) (inputs.map BitVec.toNat) := by
    unfold rootsN
    refine List.mem_filter.mpr ⟨List.mem_sublists.mpr ((List.filter_sublist).map _), ?_⟩
    rw [Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · apply Nat.ble_eq_true_of_le
      rw [List.length_map]
      exact sz
    · rw [ncuts_map, cuts_full hg hl2, negOne60]
      exact Nat.beq_refl _
  rcases child_exists hg hnd2 hl2 with e | ⟨cW, hcn, _, hcl, hmem⟩
  · have h1 := List.all_eq_true.mp h0 _ hroot
    rw [e] at h1
    have h2 := nisGoal_goal hg
    simp only [List.map_cons, List.map_nil, h2] at h1
    exact absurd h1 (by decide)
  · have hd := List.all_eq_true.mp hk _ (List.mem_flatMap.mpr ⟨_, hroot, hmem⟩)
    have hp := isortW_perm cW
    have e : (isortW cW).toFinset = cW.toFinset := List.toFinset_eq_of_perm _ _ hp
    have run := nopt_complete hg m (isortW cW) (hp.nodup_iff.mpr hcn) (e ▸ hcl)
    rw [isortW_map] at run
    rw [dead_eq, run] at hd
    exact absurd hd (by decide)

set_option maxRecDepth 16000 in
theorem all_chunk {α : Type} (p : α → Bool) (l : List α) (i n : ℕ)
    (h1 : ((l.drop i).take n).all p = true) (h2 : (l.drop (i + n)).all p = true) :
    (l.drop i).all p = true := by
  have e : (l.drop i).take n ++ l.drop (i + n) = l.drop i := by
    rw [← List.drop_drop]
    exact List.take_append_drop n (l.drop i)
  rw [← e, List.all_append, h1, h2]
  rfl

end Bridge
def w0 : Nat := ((((((((0xfd5ff * 2^60 + 0xbff7f6ede0fb76e) * 2^60 + 0xdbebd77cfaafd57) * 2^60 + 0xfcb77bb96ee5bf9) * 2^60 + 0x7f2ffc93267fc0a) * 2^60 + 0x80000003060f800) * 2^60 + 0x3f81) * 2^60 + 0xfc0f00000000000) * 2^60 + 0x3e07c0fc00000ff)
def w1 : Nat := ((((((((0x6b3f2 * 2^60 + 0xde5b4f742f7dbb6) * 2^60 + 0x3db5cdad59f56ae) * 2^60 + 0x9d5ba572b5caf52) * 2^60 + 0xbafcb12e5dcf253) * 2^60 + 0x1c0383c07f0000) * 2^60 + 0xfe001fc1fc001) * 2^60 + 0xfff000001e00781) * 2^60 + 0xc007ff00038771c)
def w2 : Nat := ((((((((0xd8fd6 * 2^60 + 0xeadd8a1ef7bed1f) * 2^60 + 0x6ea6ebcead5d4fa) * 2^60 + 0xae6dc754dd537d7) * 2^60 + 0xea555274e9f909c) * 2^60 + 0xe01c03ff800000) * 2^60 + 0x7f000fe001ffffe) * 2^60 + 0x1e007801) * 2^60 + 0xfff800001c387e0)
def w3 : Nat := ((((((((0xc7f7f * 2^60 + 0xf490dfbf7bd8fdb) * 2^60 + 0xb77972ef3e79f3c) * 2^60 + 0xf78eee671fffd9c) * 2^60 + 0xd39a67c8fe924e0) * 2^60 + 0x3001ffc0000003f) * 2^60 + 0x80000ffffe00000) * 2^60 + 0x3e0007ffe) * 2^60 + 0xe03f800)
def w4 : Nat := ((((((((0x3ffa4 * 2^60 + 0x87feefdfbdef1e3) * 2^60 + 0xc7be7cf7cf9e7cf) * 2^60 + 0x3bf0f7fff99c6e7) * 2^60 + 0x1ce38bff9124b00) * 2^60 + 0x3ffe0000000003f) * 2^60 + 0xfffff0000000000) * 2^60 + 0x3ffff8000) * 2^60 + 0xffc0000)
def w5 : Nat := ((((((((0x691f2 * 2^60 + 0x9e5346642079326) * 2^60 + 0x19a1c52c58a5406) * 2^60 + 0x9c13213024c0b50) * 2^60 + 0x3a2cb002044f002) * 2^60 + 0x600000) * 2^60 + 0x1) * 2^60 + 0xfc0000000000000) * 2^60 + 0x7c000000001c)
def w6 : Nat := ((((((((0xff7ff * 2^60 + 0xfffffffdefffffe) * 2^60 + 0xffffdffdfbfffff) * 2^60 + 0xfdfffffbffefffb) * 2^60 + 0xfffffdbf7fffe5b) * 2^60 + 0x81c0383f07ff800) * 2^60 + 0xfe001fc1fff81) * 2^60 + 0xffff00001e00781) * 2^60 + 0xfe07fffc03877ff)
def w7 : Nat := ((((((((0x9440d * 2^60 + 0x21a4b089c082448) * 2^60 + 0xc24a1250a20a951) * 2^60 + 0x60a45a894a250a9) * 2^60 + 0x45034c912230c08) * 2^60 + 0x80000003000f800) * 2^60 + 0x3f80) * 2^60 + 0xf00000000000) * 2^60 + 0x3e0000fc00000e3)
def w8 : Nat := ((((((((0x2200 * 2^60 + 0x400809100f04890) * 2^60 + 0x2414088101502a8) * 2^60 + 0x1488442910a402) * 2^60 + 0x80d0012c5980251) * 2^60 + 0x1c0383c01f0000) * 2^60 + 0xfe001fc1fc000) * 2^60 + 0x3f000001e00781) * 2^60 + 0xc0003f000387700)
def w9 : Nat := ((((((((0xd85d6 * 2^60 + 0xaad5820ce0ba50e) * 2^60 + 0x4aa2c34ca80d452) * 2^60 + 0xac2543104c413d1) * 2^60 + 0x6a0550102079008) * 2^60 + 0x30000000) * 2^60 + 0x3f80) * 2^60 + 0x0) * 2^60 + 0x3e00000000000e0)
def w10 : Nat := ((((((((0xfdfff * 2^60 + 0xfffffefff7fff7f) * 2^60 + 0xffeffffeffffdff) * 2^60 + 0xfefffffdfff7fff) * 2^60 + 0xff7ffef7efffc9e) * 2^60 + 0x8e01c03ffe0f800) * 2^60 + 0x7f000fe001fffff) * 2^60 + 0xfc0f0001e007801) * 2^60 + 0xffffc0fc1c387ff)
def w11 : Nat := ((((((((0x25029 * 2^60 + 0x152274e10041260) * 2^60 + 0x9149143052a2905) * 2^60 + 0x509238a922a4828) * 2^60 + 0x152aac830606c02) * 2^60 + 0x80000000060f800) * 2^60 + 0x1) * 2^60 + 0xfc0f00000000000) * 2^60 + 0x7c0fc000001f)
def w12 : Nat := ((((((((0xa00 * 2^60 + 0x400808121704811) * 2^60 + 0x2404288205500a8) * 2^60 + 0x24884449112406) * 2^60 + 0x80500264c980094) * 2^60 + 0xe01c03cf800000) * 2^60 + 0x7f000fe001fc07e) * 2^60 + 0x1e007801) * 2^60 + 0xc1f800001c38700)
def w13 : Nat := ((((((((0xc557f * 2^60 + 0xb490d6ad60d874a) * 2^60 + 0x9369526c3a29d14) * 2^60 + 0xf4866a210ee5998) * 2^60 + 0x530a64802612400) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w14 : Nat := ((((((((0xfffff * 2^60 + 0xfff7fffffbfbfff) * 2^60 + 0xfffbf7fffefff7f) * 2^60 + 0xffbfffff7fffffd) * 2^60 + 0xffbfffdbfeffcea) * 2^60 + 0xb001ffc3060f83f) * 2^60 + 0x80000ffffe03f81) * 2^60 + 0xfc0f003e0007ffe) * 2^60 + 0x3e07c0fce03f8ff)
def w15 : Nat := ((((((((0x38080 * 2^60 + 0xb6720408023024) * 2^60 + 0x48828510c086043) * 2^60 + 0x83111986000261) * 2^60 + 0x2c259813006d80a) * 2^60 + 0x80000003060f800) * 2^60 + 0x3f81) * 2^60 + 0xfc0f00000000000) * 2^60 + 0x3e07c0fc00000ff)
def w16 : Nat := ((((((((0x2a00 * 2^60 + 0x400009121b00891) * 2^60 + 0x241020830450228) * 2^60 + 0x3088446111a404) * 2^60 + 0x80900348d8800e0) * 2^60 + 0x3001ffc0000003f) * 2^60 + 0x80000ffffe00000) * 2^60 + 0x3e0007ffe) * 2^60 + 0xe03f800)
def w17 : Nat := ((((((((0x3d5a4 * 2^60 + 0x87f6e6cda0eb162) * 2^60 + 0xc3aa5474ca8e547) * 2^60 + 0x38b073b968842e1) * 2^60 + 0x1c2388930024800) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0) * 2^60 + 0x0)
def w18 : Nat := ((((((((0xfffff * 2^60 + 0xbffffffffdff7ef) * 2^60 + 0xdfffffffffbffdf) * 2^60 + 0xfff7fffffffdfff) * 2^60 + 0x7fefffffb77ff0a) * 2^60 + 0xbffe0003060f83f) * 2^60 + 0xfffff0000003f81) * 2^60 + 0xfc0f003ffff8000) * 2^60 + 0x3e07c0fcffc00ff)
def w19 : Nat := ((((((((0xc005b * 2^60 + 0x38011020401060c) * 2^60 + 0x184183083021810) * 2^60 + 0xc40708000661918) * 2^60 + 0x630c7400265b40a) * 2^60 + 0x80000003060f800) * 2^60 + 0x3f81) * 2^60 + 0xfc0f00000000000) * 2^60 + 0x3e07c0fc00000ff)
def w20 : Nat := ((((((((0x2a00 * 2^60 + 0x809121d04081) * 2^60 + 0x41428830510288) * 2^60 + 0x34084469118406) * 2^60 + 0xc0036c9100300) * 2^60 + 0x3ffe0000000003f) * 2^60 + 0xfffff0000000000) * 2^60 + 0x3ffff8000) * 2^60 + 0xffc0000)
def w21 : Nat := ((((((((0x483d2 * 2^60 + 0xca590a14273c916) * 2^60 + 0x2ca4c98c09554aa) * 2^60 + 0x8c4985509542752) * 2^60 + 0xaa54102449c9010) * 2^60 + 0x3c0000000) * 2^60 + 0x1fc000) * 2^60 + 0x1) * 2^60 + 0xc00000000000700)
def w22 : Nat := ((((((((0xfbff6 * 2^60 + 0xfedfcf7efffffbf) * 2^60 + 0x7fb7efeffdfd6fe) * 2^60 + 0xbf7fe776fddbfd7) * 2^60 + 0xfafdf37efdff2df) * 2^60 + 0xfc1f83ffff0000) * 2^60 + 0x7ffe0fffc1fffff) * 2^60 + 0xfff00001fe07f81) * 2^60 + 0xffffff001fbf7fc)
def w23 : Nat := ((((((((0x23020 * 2^60 + 0x1402456008412a0) * 2^60 + 0x1111042150a0204) * 2^60 + 0x111220222088800) * 2^60 + 0x10a8a10a1406243) * 2^60 + 0x1c0380007f0000) * 2^60 + 0xfe001fc000001) * 2^60 + 0xfff000001e00780) * 2^60 + 0x7ff00038701c)
def w24 : Nat := ((((((((0x90c04 * 2^60 + 0x2084800ad082409) * 2^60 + 0x42022242a408050) * 2^60 + 0x222442044811085) * 2^60 + 0x40014250a03008c) * 2^60 + 0xe01c003f800000) * 2^60 + 0x7f000fe00003ffe) * 2^60 + 0x1e007800) * 2^60 + 0x3ff800001c380e0)
def w25 : Nat := ((((((((0x43372 * 2^60 + 0xd4104f342b58b92) * 2^60 + 0x353140ad187162c) * 2^60 + 0x950aa46215cad10) * 2^60 + 0x929821085c82040) * 2^60 + 0x38000000000) * 2^60 + 0x1fc000000) * 2^60 + 0x780) * 2^60 + 0x7000)
def w26 : Nat := ((((((((0xeffff * 2^60 + 0xfedbdfff7ffdfff) * 2^60 + 0xbffdffef7ffdfbe) * 2^60 + 0xffdfef77bffffde) * 2^60 + 0xfbfef7eeffdf6f3) * 2^60 + 0x31c1fffc07f003f) * 2^60 + 0x80fe0ffffffc001) * 2^60 + 0xfff0003e1e07fff) * 2^60 + 0xc007ff00e3bff1c)
def w27 : Nat := ((((((((0x28080 * 2^60 + 0xa4b00400425024) * 2^60 + 0x8848d004184082) * 2^60 + 0x8510110a000242) * 2^60 + 0x28649026014d213) * 2^60 + 0x1c0003c07f0000) * 2^60 + 0xfe000001fc001) * 2^60 + 0xfff000001e00001) * 2^60 + 0xc007ff00038071c)
def w28 : Nat := ((((((((0x84c0d * 2^60 + 0x2080908b5080449) * 2^60 + 0x824832422608910) * 2^60 + 0x62844a050a3508c) * 2^60 + 0x410246c0a2104a0) * 2^60 + 0x3001c7c0000003f) * 2^60 + 0x80000fe03e00000) * 2^60 + 0x3e000787e) * 2^60 + 0xe038800)
def w29 : Nat := ((((((((0x2b3a0 * 2^60 + 0x865a4f542d6d1a2) * 2^60 + 0x5b44ca5499468e) * 2^60 + 0x1950a572b188642) * 2^60 + 0x18e0812e1104200) * 2^60 + 0x1c000000000000) * 2^60 + 0xfe00000000000) * 2^60 + 0x1e00000) * 2^60 + 0x380000)
def w30 : Nat := ((((((((0x7fff6 * 2^60 + 0xdfffefffbfffbf7) * 2^60 + 0xffbffdffdfff7ef) * 2^60 + 0xbffbf7fffddeff7) * 2^60 + 0xbeffbbffddefb53) * 2^60 + 0x3ffe383c07f003f) * 2^60 + 0xfffff01fc1fc001) * 2^60 + 0xfff0003ffff8781) * 2^60 + 0xc007ff00ffc771c)
def w31 : Nat := ((((((((0x40052 * 2^60 + 0x580100200210a14) * 2^60 + 0x380181081061020) * 2^60 + 0x840b00000442910) * 2^60 + 0xa21c30004ccb053) * 2^60 + 0x383c07f0000) * 2^60 + 0x1fc1fc001) * 2^60 + 0xfff000000000781) * 2^60 + 0xc007ff00000771c)
def w32 : Nat := ((((((((0x14c04 * 2^60 + 0x1a4a08b9082041) * 2^60 + 0xc20a3052860a141) * 2^60 + 0x22a0528d48140a5) * 2^60 + 0x4030ad18020900) * 2^60 + 0x3e3e0000000003f) * 2^60 + 0xff01f0000000000) * 2^60 + 0x3fe1f8000) * 2^60 + 0xfc40000)
def w33 : Nat := ((((((((0xc0f56 * 2^60 + 0xe0908a1e7398d1b) * 2^60 + 0x262062ce2c59438) * 2^60 + 0xa60cc6441d53594) * 2^60 + 0xc2104240e890080) * 2^60 + 0x1c0000000000) * 2^60 + 0xfe00000000) * 2^60 + 0x7800) * 2^60 + 0x38000)
def w34 : Nat := ((((((((0xdffff * 2^60 + 0xfedddfbffffefdf) * 2^60 + 0xfffffbefbf7dffe) * 2^60 + 0xffefef77dffffdf) * 2^60 + 0xfbdf77fcfffb4fc) * 2^60 + 0x3e01fffff80003f) * 2^60 + 0xff000fffffffffe) * 2^60 + 0x3fe007fff) * 2^60 + 0xfff80000fc3ffe0)
def w35 : Nat := ((((((((0x18080 * 2^60 + 0xa4d00008426004) * 2^60 + 0x4886890081040c2) * 2^60 + 0x8610110c000243) * 2^60 + 0x28451034016901c) * 2^60 + 0xe00003ff800000) * 2^60 + 0x7f00000001ffffe) * 2^60 + 0x1e000001) * 2^60 + 0xfff800001c007e0)
def w36 : Nat := ((((((((0x7029 * 2^60 + 0x140055a108402c0) * 2^60 + 0x915910211220b04) * 2^60 + 0x5182282302ac808) * 2^60 + 0x118a25881602460) * 2^60 + 0x30003fc0000003f) * 2^60 + 0x8000001ffe00000) * 2^60 + 0x3e00007fe) * 2^60 + 0xe007800)
def w37 : Nat := ((((((((0x18f84 * 2^60 + 0x82dc8a1eb5ae103) * 2^60 + 0x46a668c68d1c4ca) * 2^60 + 0x2a60c754d9106c7) * 2^60 + 0x84102748120000) * 2^60 + 0xe0000000000000) * 2^60 + 0x7f0000000000000) * 2^60 + 0x1e000000) * 2^60 + 0x1c00000)
def w38 : Nat := ((((((((0xffff6 * 2^60 + 0xefffefdfffffdff) * 2^60 + 0xefbeffffefdf7ff) * 2^60 + 0xbffdf7fffddf7f7) * 2^60 + 0xfef7dbfff9fdb9c) * 2^60 + 0x3fffc03ff80003f) * 2^60 + 0xffffffe001ffffe) * 2^60 + 0x3fffff801) * 2^60 + 0xfff80000fff87e0)
def w39 : Nat := ((((((((0xc0052 * 2^60 + 0x680100004210c1c) * 2^60 + 0x280083082041030) * 2^60 + 0x840d00000443110) * 2^60 + 0xe214500068d909c) * 2^60 + 0x1c03ff800000) * 2^60 + 0xfe001ffffe) * 2^60 + 0x7801) * 2^60 + 0xfff8000000387e0)
def w40 : Nat := ((((((((0x27020 * 2^60 + 0x52265c108410e0) * 2^60 + 0x811814314282305) * 2^60 + 0x119030ab208c020) * 2^60 + 0x14a2898b1004b00) * 2^60 + 0x31fe0000000003f) * 2^60 + 0x80fff0000000000) * 2^60 + 0x3e1ff8000) * 2^60 + 0xe3c0000)
def w41 : Nat := ((((((((0x7f24 * 2^60 + 0x8490cf9f39c81c3) * 2^60 + 0x873870e70e1870c) * 2^60 + 0x3380e667199c484) * 2^60 + 0x108203c89000000) * 2^60 + 0x30000000000003f) * 2^60 + 0x800000000000000) * 2^60 + 0x3e0000000) * 2^60 + 0xe000000)
def w42 : Nat := ((((((((0xfffff * 2^60 + 0xf7feffffffffffb) * 2^60 + 0xf7ff7efffffffff) * 2^60 + 0xfffefffffffffff) * 2^60 + 0xdffbefffffb6fe0) * 2^60 + 0x3fffffc0000003f) * 2^60 + 0xfffffffffe00000) * 2^60 + 0x3fffffffe) * 2^60 + 0xffff800)
def w43 : Nat := ((((((((0xc005b * 2^60 + 0x700010204210e18) * 2^60 + 0x304102083061830) * 2^60 + 0xc40e08000663918) * 2^60 + 0xc31864006e924e0) * 2^60 + 0x1ffc00000000) * 2^60 + 0xffffe00000) * 2^60 + 0x7ffe) * 2^60 + 0x3f800)
def w44 : Nat := ((((((((0x38080 * 2^60 + 0x36e20408427020) * 2^60 + 0x40860c10c1860c3) * 2^60 + 0x8701198e000263) * 2^60 + 0xc6188370124b00) * 2^60 + 0xffe00000000000) * 2^60 + 0x7ffff0000000000) * 2^60 + 0x1fff8000) * 2^60 + 0x1fc0000)
def nums : List Nat := [w0,w1,w2,w3,w4]
def s0 : List Nat := [w4,w5,w1,w3,w2,w0]
def q0 := kidsL 6 s0
def s1 : List Nat := [w4,w1,w3,w2,w0,w6]
def q1 := kidsL 6 s1
def s2 : List Nat := [w4,w1,w7,w3,w2,w0]
def q2 := kidsL 6 s2
def s3 : List Nat := [w8,w4,w1,w3,w2,w0]
def q3 := kidsL 6 s3
def s4 : List Nat := [w4,w1,w3,w9,w2,w0]
def q4 := kidsL 6 s4
def s5 : List Nat := [w4,w1,w3,w2,w0,w10]
def q5 := kidsL 6 s5
def s6 : List Nat := [w11,w4,w1,w3,w2,w0]
def q6 := kidsL 6 s6
def s7 : List Nat := [w12,w4,w1,w3,w2,w0]
def q7 := kidsL 6 s7
def s8 : List Nat := [w4,w1,w13,w3,w2,w0]
def q8 := kidsL 6 s8
def s9 : List Nat := [w4,w1,w3,w2,w0,w14]
def q9 := kidsL 6 s9
def s10 : List Nat := [w15,w4,w1,w3,w2,w0]
def q10 := kidsL 6 s10
def s11 : List Nat := [w16,w4,w1,w3,w2,w0]
def q11 := kidsL 6 s11
def s12 : List Nat := [w17,w4,w1,w3,w2,w0]
def q12 := kidsL 6 s12
def s13 : List Nat := [w4,w1,w3,w2,w0,w18]
def q13 := kidsL 6 s13
def s14 : List Nat := [w4,w1,w19,w3,w2,w0]
def q14 := kidsL 6 s14
def s15 : List Nat := [w20,w4,w1,w3,w2,w0]
def q15 := kidsL 6 s15
def s16 : List Nat := [w4,w21,w1,w3,w2,w0]
def q16 := kidsL 6 s16
def s17 : List Nat := [w4,w1,w3,w2,w22,w0]
def q17 := kidsL 6 s17
def s18 : List Nat := [w23,w4,w1,w3,w2,w0]
def q18 := kidsL 6 s18
def s19 : List Nat := [w4,w1,w24,w3,w2,w0]
def q19 := kidsL 6 s19
def s20 : List Nat := [w4,w25,w1,w3,w2,w0]
def q20 := kidsL 6 s20
def s21 : List Nat := [w4,w1,w3,w2,w26,w0]
def q21 := kidsL 6 s21
def s22 : List Nat := [w27,w4,w1,w3,w2,w0]
def q22 := kidsL 6 s22
def s23 : List Nat := [w4,w1,w28,w3,w2,w0]
def q23 := kidsL 6 s23
def s24 : List Nat := [w29,w4,w1,w3,w2,w0]
def q24 := kidsL 6 s24
def s25 : List Nat := [w4,w1,w30,w3,w2,w0]
def q25 := kidsL 6 s25
def s26 : List Nat := [w4,w31,w1,w3,w2,w0]
def q26 := kidsL 6 s26
def s27 : List Nat := [w32,w4,w1,w3,w2,w0]
def q27 := kidsL 6 s27
def s28 : List Nat := [w4,w1,w33,w3,w2,w0]
def q28 := kidsL 6 s28
def s29 : List Nat := [w4,w1,w3,w2,w34,w0]
def q29 := kidsL 6 s29
def s30 : List Nat := [w35,w4,w1,w3,w2,w0]
def q30 := kidsL 6 s30
def s31 : List Nat := [w36,w4,w1,w3,w2,w0]
def q31 := kidsL 6 s31
def s32 : List Nat := [w37,w4,w1,w3,w2,w0]
def q32 := kidsL 6 s32
def s33 : List Nat := [w4,w1,w3,w2,w0,w38]
def q33 := kidsL 6 s33
def s34 : List Nat := [w4,w1,w39,w3,w2,w0]
def q34 := kidsL 6 s34
def s35 : List Nat := [w40,w4,w1,w3,w2,w0]
def q35 := kidsL 6 s35
def s36 : List Nat := [w41,w4,w1,w3,w2,w0]
def q36 := kidsL 6 s36
def s37 : List Nat := [w4,w1,w3,w2,w0,w42]
def q37 := kidsL 6 s37
def s38 : List Nat := [w4,w1,w43,w3,w2,w0]
def q38 := kidsL 6 s38
def s39 : List Nat := [w44,w4,w1,w3,w2,w0]
def q39 := kidsL 6 s39

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_0 : ((q0.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_3 : ((q0.drop 3).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_8 : ((q0.drop 8).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_16 : ((q0.drop 16).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_24 : ((q0.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_28 : ((q0.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_31 : ((q0.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_36 : ((q0.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_40 : ((q0.drop 40).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_44 : ((q0.drop 44).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_48 : ((q0.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_53 : ((q0.drop 53).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_56 : ((q0.drop 56).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_58 : ((q0.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_63 : ((q0.drop 63).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_71 : ((q0.drop 71).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_79 : ((q0.drop 79).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p0_87 : ((q0.drop 87).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok0 : nopt 7 s0 = false := by
  have h : q0.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p0_0 (all_chunk _ _ 3 5 p0_3 (all_chunk _ _ 8 8 p0_8 (all_chunk _ _ 16 8 p0_16 (all_chunk _ _ 24 4 p0_24 (all_chunk _ _ 28 3 p0_28 (all_chunk _ _ 31 5 p0_31 (all_chunk _ _ 36 4 p0_36 (all_chunk _ _ 40 4 p0_40 (all_chunk _ _ 44 4 p0_44 (all_chunk _ _ 48 5 p0_48 (all_chunk _ _ 53 3 p0_53 (all_chunk _ _ 56 2 p0_56 (all_chunk _ _ 58 5 p0_58 (all_chunk _ _ 63 8 p0_63 (all_chunk _ _ 71 8 p0_71 (all_chunk _ _ 79 8 p0_79 (all_chunk _ _ 87 3 p0_87 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s0 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_0 : ((q1.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_5 : ((q1.drop 5).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_11 : ((q1.drop 11).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_18 : ((q1.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_21 : ((q1.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_25 : ((q1.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_30 : ((q1.drop 30).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_33 : ((q1.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_38 : ((q1.drop 38).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_45 : ((q1.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_48 : ((q1.drop 48).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_51 : ((q1.drop 51).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_54 : ((q1.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_58 : ((q1.drop 58).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_65 : ((q1.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_68 : ((q1.drop 68).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_72 : ((q1.drop 72).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_78 : ((q1.drop 78).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_80 : ((q1.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_83 : ((q1.drop 83).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_86 : ((q1.drop 86).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_88 : ((q1.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p1_92 : ((q1.drop 92).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok1 : nopt 7 s1 = false := by
  have h : q1.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p1_0 (all_chunk _ _ 5 6 p1_5 (all_chunk _ _ 11 7 p1_11 (all_chunk _ _ 18 3 p1_18 (all_chunk _ _ 21 4 p1_21 (all_chunk _ _ 25 5 p1_25 (all_chunk _ _ 30 3 p1_30 (all_chunk _ _ 33 5 p1_33 (all_chunk _ _ 38 7 p1_38 (all_chunk _ _ 45 3 p1_45 (all_chunk _ _ 48 3 p1_48 (all_chunk _ _ 51 3 p1_51 (all_chunk _ _ 54 4 p1_54 (all_chunk _ _ 58 7 p1_58 (all_chunk _ _ 65 3 p1_65 (all_chunk _ _ 68 4 p1_68 (all_chunk _ _ 72 6 p1_72 (all_chunk _ _ 78 2 p1_78 (all_chunk _ _ 80 3 p1_80 (all_chunk _ _ 83 3 p1_83 (all_chunk _ _ 86 2 p1_86 (all_chunk _ _ 88 4 p1_88 (all_chunk _ _ 92 4 p1_92 (by decide +kernel))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s1 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_0 : ((q2.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_5 : ((q2.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_9 : ((q2.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_13 : ((q2.drop 13).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_19 : ((q2.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_25 : ((q2.drop 25).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_28 : ((q2.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_31 : ((q2.drop 31).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_34 : ((q2.drop 34).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_40 : ((q2.drop 40).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_47 : ((q2.drop 47).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_52 : ((q2.drop 52).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_56 : ((q2.drop 56).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_60 : ((q2.drop 60).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_63 : ((q2.drop 63).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_66 : ((q2.drop 66).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_69 : ((q2.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_72 : ((q2.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_75 : ((q2.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_78 : ((q2.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_82 : ((q2.drop 82).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p2_87 : ((q2.drop 87).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok2 : nopt 7 s2 = false := by
  have h : q2.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p2_0 (all_chunk _ _ 5 4 p2_5 (all_chunk _ _ 9 4 p2_9 (all_chunk _ _ 13 6 p2_13 (all_chunk _ _ 19 6 p2_19 (all_chunk _ _ 25 3 p2_25 (all_chunk _ _ 28 3 p2_28 (all_chunk _ _ 31 3 p2_31 (all_chunk _ _ 34 6 p2_34 (all_chunk _ _ 40 7 p2_40 (all_chunk _ _ 47 5 p2_47 (all_chunk _ _ 52 4 p2_52 (all_chunk _ _ 56 4 p2_56 (all_chunk _ _ 60 3 p2_60 (all_chunk _ _ 63 3 p2_63 (all_chunk _ _ 66 3 p2_66 (all_chunk _ _ 69 3 p2_69 (all_chunk _ _ 72 3 p2_72 (all_chunk _ _ 75 3 p2_75 (all_chunk _ _ 78 4 p2_78 (all_chunk _ _ 82 5 p2_82 (all_chunk _ _ 87 7 p2_87 (by decide +kernel)))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s2 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_0 : ((q3.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_5 : ((q3.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_9 : ((q3.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_13 : ((q3.drop 13).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_16 : ((q3.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_20 : ((q3.drop 20).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_25 : ((q3.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_29 : ((q3.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_32 : ((q3.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_36 : ((q3.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_41 : ((q3.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_45 : ((q3.drop 45).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_52 : ((q3.drop 52).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_61 : ((q3.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_69 : ((q3.drop 69).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_75 : ((q3.drop 75).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_83 : ((q3.drop 83).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p3_91 : ((q3.drop 91).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok3 : nopt 7 s3 = false := by
  have h : q3.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p3_0 (all_chunk _ _ 5 4 p3_5 (all_chunk _ _ 9 4 p3_9 (all_chunk _ _ 13 3 p3_13 (all_chunk _ _ 16 4 p3_16 (all_chunk _ _ 20 5 p3_20 (all_chunk _ _ 25 4 p3_25 (all_chunk _ _ 29 3 p3_29 (all_chunk _ _ 32 4 p3_32 (all_chunk _ _ 36 5 p3_36 (all_chunk _ _ 41 4 p3_41 (all_chunk _ _ 45 7 p3_45 (all_chunk _ _ 52 9 p3_52 (all_chunk _ _ 61 8 p3_61 (all_chunk _ _ 69 6 p3_69 (all_chunk _ _ 75 8 p3_75 (all_chunk _ _ 83 8 p3_83 (all_chunk _ _ 91 5 p3_91 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s3 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_0 : ((q4.drop 0).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_8 : ((q4.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_11 : ((q4.drop 11).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_16 : ((q4.drop 16).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_24 : ((q4.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_29 : ((q4.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_33 : ((q4.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_38 : ((q4.drop 38).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_45 : ((q4.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_49 : ((q4.drop 49).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_55 : ((q4.drop 55).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_61 : ((q4.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_65 : ((q4.drop 65).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_68 : ((q4.drop 68).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_73 : ((q4.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_76 : ((q4.drop 76).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_78 : ((q4.drop 78).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p4_83 : ((q4.drop 83).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok4 : nopt 7 s4 = false := by
  have h : q4.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 8 p4_0 (all_chunk _ _ 8 3 p4_8 (all_chunk _ _ 11 5 p4_11 (all_chunk _ _ 16 8 p4_16 (all_chunk _ _ 24 5 p4_24 (all_chunk _ _ 29 4 p4_29 (all_chunk _ _ 33 5 p4_33 (all_chunk _ _ 38 7 p4_38 (all_chunk _ _ 45 4 p4_45 (all_chunk _ _ 49 6 p4_49 (all_chunk _ _ 55 6 p4_55 (all_chunk _ _ 61 4 p4_61 (all_chunk _ _ 65 3 p4_65 (all_chunk _ _ 68 5 p4_68 (all_chunk _ _ 73 3 p4_73 (all_chunk _ _ 76 2 p4_76 (all_chunk _ _ 78 5 p4_78 (all_chunk _ _ 83 7 p4_83 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s4 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_0 : ((q5.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_6 : ((q5.drop 6).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_11 : ((q5.drop 11).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_19 : ((q5.drop 19).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_22 : ((q5.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_26 : ((q5.drop 26).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_31 : ((q5.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_36 : ((q5.drop 36).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_42 : ((q5.drop 42).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_43 : ((q5.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_46 : ((q5.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_50 : ((q5.drop 50).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_57 : ((q5.drop 57).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_61 : ((q5.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_65 : ((q5.drop 65).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_73 : ((q5.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_76 : ((q5.drop 76).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_79 : ((q5.drop 79).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_82 : ((q5.drop 82).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_86 : ((q5.drop 86).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_88 : ((q5.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p5_92 : ((q5.drop 92).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok5 : nopt 7 s5 = false := by
  have h : q5.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p5_0 (all_chunk _ _ 6 5 p5_6 (all_chunk _ _ 11 8 p5_11 (all_chunk _ _ 19 3 p5_19 (all_chunk _ _ 22 4 p5_22 (all_chunk _ _ 26 5 p5_26 (all_chunk _ _ 31 5 p5_31 (all_chunk _ _ 36 6 p5_36 (all_chunk _ _ 42 1 p5_42 (all_chunk _ _ 43 3 p5_43 (all_chunk _ _ 46 4 p5_46 (all_chunk _ _ 50 7 p5_50 (all_chunk _ _ 57 4 p5_57 (all_chunk _ _ 61 4 p5_61 (all_chunk _ _ 65 8 p5_65 (all_chunk _ _ 73 3 p5_73 (all_chunk _ _ 76 3 p5_76 (all_chunk _ _ 79 3 p5_79 (all_chunk _ _ 82 4 p5_82 (all_chunk _ _ 86 2 p5_86 (all_chunk _ _ 88 4 p5_88 (all_chunk _ _ 92 4 p5_92 (by decide +kernel)))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s5 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_0 : ((q6.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_2 : ((q6.drop 2).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_6 : ((q6.drop 6).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_10 : ((q6.drop 10).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_12 : ((q6.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_15 : ((q6.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_18 : ((q6.drop 18).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_21 : ((q6.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_25 : ((q6.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_29 : ((q6.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_32 : ((q6.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_36 : ((q6.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_39 : ((q6.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_42 : ((q6.drop 42).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_44 : ((q6.drop 44).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_46 : ((q6.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_50 : ((q6.drop 50).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_56 : ((q6.drop 56).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_62 : ((q6.drop 62).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_67 : ((q6.drop 67).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_73 : ((q6.drop 73).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_80 : ((q6.drop 80).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_86 : ((q6.drop 86).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p6_93 : ((q6.drop 93).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok6 : nopt 7 s6 = false := by
  have h : q6.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p6_0 (all_chunk _ _ 2 4 p6_2 (all_chunk _ _ 6 4 p6_6 (all_chunk _ _ 10 2 p6_10 (all_chunk _ _ 12 3 p6_12 (all_chunk _ _ 15 3 p6_15 (all_chunk _ _ 18 3 p6_18 (all_chunk _ _ 21 4 p6_21 (all_chunk _ _ 25 4 p6_25 (all_chunk _ _ 29 3 p6_29 (all_chunk _ _ 32 4 p6_32 (all_chunk _ _ 36 3 p6_36 (all_chunk _ _ 39 3 p6_39 (all_chunk _ _ 42 2 p6_42 (all_chunk _ _ 44 2 p6_44 (all_chunk _ _ 46 4 p6_46 (all_chunk _ _ 50 6 p6_50 (all_chunk _ _ 56 6 p6_56 (all_chunk _ _ 62 5 p6_62 (all_chunk _ _ 67 6 p6_67 (all_chunk _ _ 73 7 p6_73 (all_chunk _ _ 80 6 p6_80 (all_chunk _ _ 86 7 p6_86 (all_chunk _ _ 93 1 p6_93 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s6 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_0 : ((q7.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_5 : ((q7.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_9 : ((q7.drop 9).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_13 : ((q7.drop 13).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_18 : ((q7.drop 18).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_23 : ((q7.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_27 : ((q7.drop 27).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_30 : ((q7.drop 30).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_32 : ((q7.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_36 : ((q7.drop 36).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_41 : ((q7.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_45 : ((q7.drop 45).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_53 : ((q7.drop 53).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_61 : ((q7.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_69 : ((q7.drop 69).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_77 : ((q7.drop 77).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_85 : ((q7.drop 85).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p7_93 : ((q7.drop 93).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok7 : nopt 7 s7 = false := by
  have h : q7.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p7_0 (all_chunk _ _ 5 4 p7_5 (all_chunk _ _ 9 4 p7_9 (all_chunk _ _ 13 5 p7_13 (all_chunk _ _ 18 5 p7_18 (all_chunk _ _ 23 4 p7_23 (all_chunk _ _ 27 3 p7_27 (all_chunk _ _ 30 2 p7_30 (all_chunk _ _ 32 4 p7_32 (all_chunk _ _ 36 5 p7_36 (all_chunk _ _ 41 4 p7_41 (all_chunk _ _ 45 8 p7_45 (all_chunk _ _ 53 8 p7_53 (all_chunk _ _ 61 8 p7_61 (all_chunk _ _ 69 8 p7_69 (all_chunk _ _ 77 8 p7_77 (all_chunk _ _ 85 8 p7_85 (all_chunk _ _ 93 3 p7_93 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s7 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_0 : ((q8.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_4 : ((q8.drop 4).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_6 : ((q8.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_8 : ((q8.drop 8).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_10 : ((q8.drop 10).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_12 : ((q8.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_15 : ((q8.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_18 : ((q8.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_22 : ((q8.drop 22).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_25 : ((q8.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_29 : ((q8.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_31 : ((q8.drop 31).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_33 : ((q8.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_36 : ((q8.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_39 : ((q8.drop 39).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_41 : ((q8.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_45 : ((q8.drop 45).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_49 : ((q8.drop 49).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_53 : ((q8.drop 53).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_55 : ((q8.drop 55).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_57 : ((q8.drop 57).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_59 : ((q8.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_62 : ((q8.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_65 : ((q8.drop 65).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_67 : ((q8.drop 67).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_70 : ((q8.drop 70).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_72 : ((q8.drop 72).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_74 : ((q8.drop 74).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_77 : ((q8.drop 77).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_79 : ((q8.drop 79).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_82 : ((q8.drop 82).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_85 : ((q8.drop 85).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_88 : ((q8.drop 88).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_91 : ((q8.drop 91).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_95 : ((q8.drop 95).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p8_100 : ((q8.drop 100).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok8 : nopt 7 s8 = false := by
  have h : q8.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p8_0 (all_chunk _ _ 4 2 p8_4 (all_chunk _ _ 6 2 p8_6 (all_chunk _ _ 8 2 p8_8 (all_chunk _ _ 10 2 p8_10 (all_chunk _ _ 12 3 p8_12 (all_chunk _ _ 15 3 p8_15 (all_chunk _ _ 18 4 p8_18 (all_chunk _ _ 22 3 p8_22 (all_chunk _ _ 25 4 p8_25 (all_chunk _ _ 29 2 p8_29 (all_chunk _ _ 31 2 p8_31 (all_chunk _ _ 33 3 p8_33 (all_chunk _ _ 36 3 p8_36 (all_chunk _ _ 39 2 p8_39 (all_chunk _ _ 41 4 p8_41 (all_chunk _ _ 45 4 p8_45 (all_chunk _ _ 49 4 p8_49 (all_chunk _ _ 53 2 p8_53 (all_chunk _ _ 55 2 p8_55 (all_chunk _ _ 57 2 p8_57 (all_chunk _ _ 59 3 p8_59 (all_chunk _ _ 62 3 p8_62 (all_chunk _ _ 65 2 p8_65 (all_chunk _ _ 67 3 p8_67 (all_chunk _ _ 70 2 p8_70 (all_chunk _ _ 72 2 p8_72 (all_chunk _ _ 74 3 p8_74 (all_chunk _ _ 77 2 p8_77 (all_chunk _ _ 79 3 p8_79 (all_chunk _ _ 82 3 p8_82 (all_chunk _ _ 85 3 p8_85 (all_chunk _ _ 88 3 p8_88 (all_chunk _ _ 91 4 p8_91 (all_chunk _ _ 95 5 p8_95 (all_chunk _ _ 100 2 p8_100 (by decide +kernel)))))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s8 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_0 : ((q9.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_7 : ((q9.drop 7).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_15 : ((q9.drop 15).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_20 : ((q9.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_23 : ((q9.drop 23).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_29 : ((q9.drop 29).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_38 : ((q9.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_41 : ((q9.drop 41).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_45 : ((q9.drop 45).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_52 : ((q9.drop 52).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_59 : ((q9.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_62 : ((q9.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_65 : ((q9.drop 65).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_71 : ((q9.drop 71).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_76 : ((q9.drop 76).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_80 : ((q9.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_83 : ((q9.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_87 : ((q9.drop 87).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p9_89 : ((q9.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok9 : nopt 7 s9 = false := by
  have h : q9.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p9_0 (all_chunk _ _ 7 8 p9_7 (all_chunk _ _ 15 5 p9_15 (all_chunk _ _ 20 3 p9_20 (all_chunk _ _ 23 6 p9_23 (all_chunk _ _ 29 9 p9_29 (all_chunk _ _ 38 3 p9_38 (all_chunk _ _ 41 4 p9_41 (all_chunk _ _ 45 7 p9_45 (all_chunk _ _ 52 7 p9_52 (all_chunk _ _ 59 3 p9_59 (all_chunk _ _ 62 3 p9_62 (all_chunk _ _ 65 6 p9_65 (all_chunk _ _ 71 5 p9_71 (all_chunk _ _ 76 4 p9_76 (all_chunk _ _ 80 3 p9_80 (all_chunk _ _ 83 4 p9_83 (all_chunk _ _ 87 2 p9_87 (all_chunk _ _ 89 3 p9_89 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s9 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_0 : ((q10.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_3 : ((q10.drop 3).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_7 : ((q10.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_11 : ((q10.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_15 : ((q10.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_18 : ((q10.drop 18).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_23 : ((q10.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_26 : ((q10.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_30 : ((q10.drop 30).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_34 : ((q10.drop 34).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_38 : ((q10.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_41 : ((q10.drop 41).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_43 : ((q10.drop 43).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_46 : ((q10.drop 46).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_55 : ((q10.drop 55).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_63 : ((q10.drop 63).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_71 : ((q10.drop 71).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_79 : ((q10.drop 79).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p10_87 : ((q10.drop 87).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok10 : nopt 7 s10 = false := by
  have h : q10.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p10_0 (all_chunk _ _ 3 4 p10_3 (all_chunk _ _ 7 4 p10_7 (all_chunk _ _ 11 4 p10_11 (all_chunk _ _ 15 3 p10_15 (all_chunk _ _ 18 5 p10_18 (all_chunk _ _ 23 3 p10_23 (all_chunk _ _ 26 4 p10_26 (all_chunk _ _ 30 4 p10_30 (all_chunk _ _ 34 4 p10_34 (all_chunk _ _ 38 3 p10_38 (all_chunk _ _ 41 2 p10_41 (all_chunk _ _ 43 3 p10_43 (all_chunk _ _ 46 9 p10_46 (all_chunk _ _ 55 8 p10_55 (all_chunk _ _ 63 8 p10_63 (all_chunk _ _ 71 8 p10_71 (all_chunk _ _ 79 8 p10_79 (all_chunk _ _ 87 3 p10_87 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s10 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_0 : ((q11.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_4 : ((q11.drop 4).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_8 : ((q11.drop 8).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_12 : ((q11.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_16 : ((q11.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_20 : ((q11.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_23 : ((q11.drop 23).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_26 : ((q11.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_30 : ((q11.drop 30).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_34 : ((q11.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_37 : ((q11.drop 37).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_42 : ((q11.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_45 : ((q11.drop 45).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_53 : ((q11.drop 53).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_61 : ((q11.drop 61).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_69 : ((q11.drop 69).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_78 : ((q11.drop 78).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p11_85 : ((q11.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok11 : nopt 7 s11 = false := by
  have h : q11.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p11_0 (all_chunk _ _ 4 4 p11_4 (all_chunk _ _ 8 4 p11_8 (all_chunk _ _ 12 4 p11_12 (all_chunk _ _ 16 4 p11_16 (all_chunk _ _ 20 3 p11_20 (all_chunk _ _ 23 3 p11_23 (all_chunk _ _ 26 4 p11_26 (all_chunk _ _ 30 4 p11_30 (all_chunk _ _ 34 3 p11_34 (all_chunk _ _ 37 5 p11_37 (all_chunk _ _ 42 3 p11_42 (all_chunk _ _ 45 8 p11_45 (all_chunk _ _ 53 8 p11_53 (all_chunk _ _ 61 8 p11_61 (all_chunk _ _ 69 9 p11_69 (all_chunk _ _ 78 7 p11_78 (all_chunk _ _ 85 7 p11_85 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s11 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_0 : ((q12.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_2 : ((q12.drop 2).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_4 : ((q12.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_7 : ((q12.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_10 : ((q12.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_13 : ((q12.drop 13).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_15 : ((q12.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_18 : ((q12.drop 18).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_20 : ((q12.drop 20).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_22 : ((q12.drop 22).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_24 : ((q12.drop 24).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_26 : ((q12.drop 26).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_28 : ((q12.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_31 : ((q12.drop 31).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_33 : ((q12.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_36 : ((q12.drop 36).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_38 : ((q12.drop 38).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_40 : ((q12.drop 40).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_43 : ((q12.drop 43).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_45 : ((q12.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_48 : ((q12.drop 48).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_50 : ((q12.drop 50).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_52 : ((q12.drop 52).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_54 : ((q12.drop 54).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_57 : ((q12.drop 57).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_60 : ((q12.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_64 : ((q12.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_68 : ((q12.drop 68).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_71 : ((q12.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_75 : ((q12.drop 75).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_80 : ((q12.drop 80).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_84 : ((q12.drop 84).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_89 : ((q12.drop 89).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_93 : ((q12.drop 93).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_96 : ((q12.drop 96).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p12_101 : ((q12.drop 101).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok12 : nopt 7 s12 = false := by
  have h : q12.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p12_0 (all_chunk _ _ 2 2 p12_2 (all_chunk _ _ 4 3 p12_4 (all_chunk _ _ 7 3 p12_7 (all_chunk _ _ 10 3 p12_10 (all_chunk _ _ 13 2 p12_13 (all_chunk _ _ 15 3 p12_15 (all_chunk _ _ 18 2 p12_18 (all_chunk _ _ 20 2 p12_20 (all_chunk _ _ 22 2 p12_22 (all_chunk _ _ 24 2 p12_24 (all_chunk _ _ 26 2 p12_26 (all_chunk _ _ 28 3 p12_28 (all_chunk _ _ 31 2 p12_31 (all_chunk _ _ 33 3 p12_33 (all_chunk _ _ 36 2 p12_36 (all_chunk _ _ 38 2 p12_38 (all_chunk _ _ 40 3 p12_40 (all_chunk _ _ 43 2 p12_43 (all_chunk _ _ 45 3 p12_45 (all_chunk _ _ 48 2 p12_48 (all_chunk _ _ 50 2 p12_50 (all_chunk _ _ 52 2 p12_52 (all_chunk _ _ 54 3 p12_54 (all_chunk _ _ 57 3 p12_57 (all_chunk _ _ 60 4 p12_60 (all_chunk _ _ 64 4 p12_64 (all_chunk _ _ 68 3 p12_68 (all_chunk _ _ 71 4 p12_71 (all_chunk _ _ 75 5 p12_75 (all_chunk _ _ 80 4 p12_80 (all_chunk _ _ 84 5 p12_84 (all_chunk _ _ 89 4 p12_89 (all_chunk _ _ 93 3 p12_93 (all_chunk _ _ 96 5 p12_96 (all_chunk _ _ 101 1 p12_101 (by decide +kernel)))))))))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s12 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_0 : ((q13.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_7 : ((q13.drop 7).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_15 : ((q13.drop 15).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_21 : ((q13.drop 21).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_24 : ((q13.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_28 : ((q13.drop 28).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_30 : ((q13.drop 30).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_37 : ((q13.drop 37).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_45 : ((q13.drop 45).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_48 : ((q13.drop 48).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_52 : ((q13.drop 52).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_60 : ((q13.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_64 : ((q13.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_68 : ((q13.drop 68).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_75 : ((q13.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_78 : ((q13.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_82 : ((q13.drop 82).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_85 : ((q13.drop 85).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p13_88 : ((q13.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok13 : nopt 7 s13 = false := by
  have h : q13.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p13_0 (all_chunk _ _ 7 8 p13_7 (all_chunk _ _ 15 6 p13_15 (all_chunk _ _ 21 3 p13_21 (all_chunk _ _ 24 4 p13_24 (all_chunk _ _ 28 2 p13_28 (all_chunk _ _ 30 7 p13_30 (all_chunk _ _ 37 8 p13_37 (all_chunk _ _ 45 3 p13_45 (all_chunk _ _ 48 4 p13_48 (all_chunk _ _ 52 8 p13_52 (all_chunk _ _ 60 4 p13_60 (all_chunk _ _ 64 4 p13_64 (all_chunk _ _ 68 7 p13_68 (all_chunk _ _ 75 3 p13_75 (all_chunk _ _ 78 4 p13_78 (all_chunk _ _ 82 3 p13_82 (all_chunk _ _ 85 3 p13_85 (all_chunk _ _ 88 4 p13_88 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s13 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_0 : ((q14.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_5 : ((q14.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_10 : ((q14.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_13 : ((q14.drop 13).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_19 : ((q14.drop 19).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_27 : ((q14.drop 27).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_33 : ((q14.drop 33).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_38 : ((q14.drop 38).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_46 : ((q14.drop 46).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_52 : ((q14.drop 52).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_56 : ((q14.drop 56).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_61 : ((q14.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_65 : ((q14.drop 65).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_70 : ((q14.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_73 : ((q14.drop 73).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_75 : ((q14.drop 75).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_78 : ((q14.drop 78).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p14_86 : ((q14.drop 86).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok14 : nopt 7 s14 = false := by
  have h : q14.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p14_0 (all_chunk _ _ 5 5 p14_5 (all_chunk _ _ 10 3 p14_10 (all_chunk _ _ 13 6 p14_13 (all_chunk _ _ 19 8 p14_19 (all_chunk _ _ 27 6 p14_27 (all_chunk _ _ 33 5 p14_33 (all_chunk _ _ 38 8 p14_38 (all_chunk _ _ 46 6 p14_46 (all_chunk _ _ 52 4 p14_52 (all_chunk _ _ 56 5 p14_56 (all_chunk _ _ 61 4 p14_61 (all_chunk _ _ 65 5 p14_65 (all_chunk _ _ 70 3 p14_70 (all_chunk _ _ 73 2 p14_73 (all_chunk _ _ 75 3 p14_75 (all_chunk _ _ 78 8 p14_78 (all_chunk _ _ 86 4 p14_86 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s14 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_0 : ((q15.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_4 : ((q15.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_7 : ((q15.drop 7).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_10 : ((q15.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_14 : ((q15.drop 14).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_18 : ((q15.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_22 : ((q15.drop 22).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_26 : ((q15.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_30 : ((q15.drop 30).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_34 : ((q15.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_37 : ((q15.drop 37).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_42 : ((q15.drop 42).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_45 : ((q15.drop 45).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_52 : ((q15.drop 52).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_59 : ((q15.drop 59).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_65 : ((q15.drop 65).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_74 : ((q15.drop 74).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p15_84 : ((q15.drop 84).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok15 : nopt 7 s15 = false := by
  have h : q15.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p15_0 (all_chunk _ _ 4 3 p15_4 (all_chunk _ _ 7 3 p15_7 (all_chunk _ _ 10 4 p15_10 (all_chunk _ _ 14 4 p15_14 (all_chunk _ _ 18 4 p15_18 (all_chunk _ _ 22 4 p15_22 (all_chunk _ _ 26 4 p15_26 (all_chunk _ _ 30 4 p15_30 (all_chunk _ _ 34 3 p15_34 (all_chunk _ _ 37 5 p15_37 (all_chunk _ _ 42 3 p15_42 (all_chunk _ _ 45 7 p15_45 (all_chunk _ _ 52 7 p15_52 (all_chunk _ _ 59 6 p15_59 (all_chunk _ _ 65 9 p15_65 (all_chunk _ _ 74 10 p15_74 (all_chunk _ _ 84 8 p15_84 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s15 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_0 : ((q16.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_3 : ((q16.drop 3).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_7 : ((q16.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_11 : ((q16.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_15 : ((q16.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_19 : ((q16.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_23 : ((q16.drop 23).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_28 : ((q16.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_31 : ((q16.drop 31).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_33 : ((q16.drop 33).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_35 : ((q16.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_39 : ((q16.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_42 : ((q16.drop 42).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_46 : ((q16.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_50 : ((q16.drop 50).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_52 : ((q16.drop 52).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_54 : ((q16.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_58 : ((q16.drop 58).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_60 : ((q16.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_64 : ((q16.drop 64).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_67 : ((q16.drop 67).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_72 : ((q16.drop 72).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_74 : ((q16.drop 74).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_76 : ((q16.drop 76).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_81 : ((q16.drop 81).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_83 : ((q16.drop 83).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_88 : ((q16.drop 88).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_92 : ((q16.drop 92).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_97 : ((q16.drop 97).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p16_99 : ((q16.drop 99).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok16 : nopt 7 s16 = false := by
  have h : q16.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p16_0 (all_chunk _ _ 3 4 p16_3 (all_chunk _ _ 7 4 p16_7 (all_chunk _ _ 11 4 p16_11 (all_chunk _ _ 15 4 p16_15 (all_chunk _ _ 19 4 p16_19 (all_chunk _ _ 23 5 p16_23 (all_chunk _ _ 28 3 p16_28 (all_chunk _ _ 31 2 p16_31 (all_chunk _ _ 33 2 p16_33 (all_chunk _ _ 35 4 p16_35 (all_chunk _ _ 39 3 p16_39 (all_chunk _ _ 42 4 p16_42 (all_chunk _ _ 46 4 p16_46 (all_chunk _ _ 50 2 p16_50 (all_chunk _ _ 52 2 p16_52 (all_chunk _ _ 54 4 p16_54 (all_chunk _ _ 58 2 p16_58 (all_chunk _ _ 60 4 p16_60 (all_chunk _ _ 64 3 p16_64 (all_chunk _ _ 67 5 p16_67 (all_chunk _ _ 72 2 p16_72 (all_chunk _ _ 74 2 p16_74 (all_chunk _ _ 76 5 p16_76 (all_chunk _ _ 81 2 p16_81 (all_chunk _ _ 83 5 p16_83 (all_chunk _ _ 88 4 p16_88 (all_chunk _ _ 92 5 p16_92 (all_chunk _ _ 97 2 p16_97 (all_chunk _ _ 99 4 p16_99 (by decide +kernel)))))))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s16 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_0 : ((q17.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_6 : ((q17.drop 6).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_13 : ((q17.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_17 : ((q17.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_21 : ((q17.drop 21).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_28 : ((q17.drop 28).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_29 : ((q17.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_31 : ((q17.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_36 : ((q17.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_39 : ((q17.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_42 : ((q17.drop 42).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_44 : ((q17.drop 44).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_48 : ((q17.drop 48).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_55 : ((q17.drop 55).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_58 : ((q17.drop 58).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_61 : ((q17.drop 61).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_65 : ((q17.drop 65).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_70 : ((q17.drop 70).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_73 : ((q17.drop 73).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_75 : ((q17.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_79 : ((q17.drop 79).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_85 : ((q17.drop 85).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_86 : ((q17.drop 86).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p17_89 : ((q17.drop 89).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok17 : nopt 7 s17 = false := by
  have h : q17.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p17_0 (all_chunk _ _ 6 7 p17_6 (all_chunk _ _ 13 4 p17_13 (all_chunk _ _ 17 4 p17_17 (all_chunk _ _ 21 7 p17_21 (all_chunk _ _ 28 1 p17_28 (all_chunk _ _ 29 2 p17_29 (all_chunk _ _ 31 5 p17_31 (all_chunk _ _ 36 3 p17_36 (all_chunk _ _ 39 3 p17_39 (all_chunk _ _ 42 2 p17_42 (all_chunk _ _ 44 4 p17_44 (all_chunk _ _ 48 7 p17_48 (all_chunk _ _ 55 3 p17_55 (all_chunk _ _ 58 3 p17_58 (all_chunk _ _ 61 4 p17_61 (all_chunk _ _ 65 5 p17_65 (all_chunk _ _ 70 3 p17_70 (all_chunk _ _ 73 2 p17_73 (all_chunk _ _ 75 4 p17_75 (all_chunk _ _ 79 6 p17_79 (all_chunk _ _ 85 1 p17_85 (all_chunk _ _ 86 3 p17_86 (all_chunk _ _ 89 2 p17_89 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s17 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_0 : ((q18.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_4 : ((q18.drop 4).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_8 : ((q18.drop 8).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_11 : ((q18.drop 11).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_14 : ((q18.drop 14).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_16 : ((q18.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_19 : ((q18.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_23 : ((q18.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_27 : ((q18.drop 27).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_29 : ((q18.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_33 : ((q18.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_36 : ((q18.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_39 : ((q18.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_43 : ((q18.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_49 : ((q18.drop 49).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_58 : ((q18.drop 58).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_66 : ((q18.drop 66).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_72 : ((q18.drop 72).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_80 : ((q18.drop 80).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_87 : ((q18.drop 87).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p18_94 : ((q18.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok18 : nopt 7 s18 = false := by
  have h : q18.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p18_0 (all_chunk _ _ 4 4 p18_4 (all_chunk _ _ 8 3 p18_8 (all_chunk _ _ 11 3 p18_11 (all_chunk _ _ 14 2 p18_14 (all_chunk _ _ 16 3 p18_16 (all_chunk _ _ 19 4 p18_19 (all_chunk _ _ 23 4 p18_23 (all_chunk _ _ 27 2 p18_27 (all_chunk _ _ 29 4 p18_29 (all_chunk _ _ 33 3 p18_33 (all_chunk _ _ 36 3 p18_36 (all_chunk _ _ 39 4 p18_39 (all_chunk _ _ 43 6 p18_43 (all_chunk _ _ 49 9 p18_49 (all_chunk _ _ 58 8 p18_58 (all_chunk _ _ 66 6 p18_66 (all_chunk _ _ 72 8 p18_72 (all_chunk _ _ 80 7 p18_80 (all_chunk _ _ 87 7 p18_87 (all_chunk _ _ 94 2 p18_94 (by decide +kernel))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s18 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_0 : ((q19.drop 0).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_7 : ((q19.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_12 : ((q19.drop 12).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_17 : ((q19.drop 17).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_25 : ((q19.drop 25).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_28 : ((q19.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_32 : ((q19.drop 32).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_35 : ((q19.drop 35).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_41 : ((q19.drop 41).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_46 : ((q19.drop 46).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_53 : ((q19.drop 53).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_58 : ((q19.drop 58).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_62 : ((q19.drop 62).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_66 : ((q19.drop 66).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_69 : ((q19.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_72 : ((q19.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_75 : ((q19.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_79 : ((q19.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_83 : ((q19.drop 83).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p19_91 : ((q19.drop 91).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok19 : nopt 7 s19 = false := by
  have h : q19.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 7 p19_0 (all_chunk _ _ 7 5 p19_7 (all_chunk _ _ 12 5 p19_12 (all_chunk _ _ 17 8 p19_17 (all_chunk _ _ 25 3 p19_25 (all_chunk _ _ 28 4 p19_28 (all_chunk _ _ 32 3 p19_32 (all_chunk _ _ 35 6 p19_35 (all_chunk _ _ 41 5 p19_41 (all_chunk _ _ 46 7 p19_46 (all_chunk _ _ 53 5 p19_53 (all_chunk _ _ 58 4 p19_58 (all_chunk _ _ 62 4 p19_62 (all_chunk _ _ 66 3 p19_66 (all_chunk _ _ 69 3 p19_69 (all_chunk _ _ 72 3 p19_72 (all_chunk _ _ 75 4 p19_75 (all_chunk _ _ 79 4 p19_79 (all_chunk _ _ 83 8 p19_83 (all_chunk _ _ 91 5 p19_91 (by decide +kernel)))))))))))))))))))))
  rw [nopt_succ, show nisGoal s19 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_0 : ((q20.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_3 : ((q20.drop 3).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_8 : ((q20.drop 8).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_17 : ((q20.drop 17).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_24 : ((q20.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_28 : ((q20.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_31 : ((q20.drop 31).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_36 : ((q20.drop 36).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_40 : ((q20.drop 40).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_42 : ((q20.drop 42).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_47 : ((q20.drop 47).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_51 : ((q20.drop 51).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_55 : ((q20.drop 55).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_59 : ((q20.drop 59).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_65 : ((q20.drop 65).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_71 : ((q20.drop 71).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_79 : ((q20.drop 79).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p20_85 : ((q20.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok20 : nopt 7 s20 = false := by
  have h : q20.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p20_0 (all_chunk _ _ 3 5 p20_3 (all_chunk _ _ 8 9 p20_8 (all_chunk _ _ 17 7 p20_17 (all_chunk _ _ 24 4 p20_24 (all_chunk _ _ 28 3 p20_28 (all_chunk _ _ 31 5 p20_31 (all_chunk _ _ 36 4 p20_36 (all_chunk _ _ 40 2 p20_40 (all_chunk _ _ 42 5 p20_42 (all_chunk _ _ 47 4 p20_47 (all_chunk _ _ 51 4 p20_51 (all_chunk _ _ 55 4 p20_55 (all_chunk _ _ 59 6 p20_59 (all_chunk _ _ 65 6 p20_65 (all_chunk _ _ 71 8 p20_71 (all_chunk _ _ 79 6 p20_79 (all_chunk _ _ 85 7 p20_85 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s20 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_0 : ((q21.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_6 : ((q21.drop 6).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_13 : ((q21.drop 13).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_16 : ((q21.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_19 : ((q21.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_25 : ((q21.drop 25).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_30 : ((q21.drop 30).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_36 : ((q21.drop 36).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_38 : ((q21.drop 38).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_41 : ((q21.drop 41).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_43 : ((q21.drop 43).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_47 : ((q21.drop 47).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_51 : ((q21.drop 51).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_57 : ((q21.drop 57).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_59 : ((q21.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_62 : ((q21.drop 62).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_64 : ((q21.drop 64).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_68 : ((q21.drop 68).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_72 : ((q21.drop 72).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_74 : ((q21.drop 74).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_77 : ((q21.drop 77).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_81 : ((q21.drop 81).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_83 : ((q21.drop 83).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_89 : ((q21.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p21_92 : ((q21.drop 92).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok21 : nopt 7 s21 = false := by
  have h : q21.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p21_0 (all_chunk _ _ 6 7 p21_6 (all_chunk _ _ 13 3 p21_13 (all_chunk _ _ 16 3 p21_16 (all_chunk _ _ 19 6 p21_19 (all_chunk _ _ 25 5 p21_25 (all_chunk _ _ 30 6 p21_30 (all_chunk _ _ 36 2 p21_36 (all_chunk _ _ 38 3 p21_38 (all_chunk _ _ 41 2 p21_41 (all_chunk _ _ 43 4 p21_43 (all_chunk _ _ 47 4 p21_47 (all_chunk _ _ 51 6 p21_51 (all_chunk _ _ 57 2 p21_57 (all_chunk _ _ 59 3 p21_59 (all_chunk _ _ 62 2 p21_62 (all_chunk _ _ 64 4 p21_64 (all_chunk _ _ 68 4 p21_68 (all_chunk _ _ 72 2 p21_72 (all_chunk _ _ 74 3 p21_74 (all_chunk _ _ 77 4 p21_77 (all_chunk _ _ 81 2 p21_81 (all_chunk _ _ 83 6 p21_83 (all_chunk _ _ 89 3 p21_89 (all_chunk _ _ 92 4 p21_92 (by decide +kernel))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s21 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_0 : ((q22.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_5 : ((q22.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_10 : ((q22.drop 10).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_13 : ((q22.drop 13).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_16 : ((q22.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_20 : ((q22.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_24 : ((q22.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_28 : ((q22.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_31 : ((q22.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_35 : ((q22.drop 35).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_40 : ((q22.drop 40).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_45 : ((q22.drop 45).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_54 : ((q22.drop 54).take 10).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_64 : ((q22.drop 64).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_72 : ((q22.drop 72).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_81 : ((q22.drop 81).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p22_89 : ((q22.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok22 : nopt 7 s22 = false := by
  have h : q22.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p22_0 (all_chunk _ _ 5 5 p22_5 (all_chunk _ _ 10 3 p22_10 (all_chunk _ _ 13 3 p22_13 (all_chunk _ _ 16 4 p22_16 (all_chunk _ _ 20 4 p22_20 (all_chunk _ _ 24 4 p22_24 (all_chunk _ _ 28 3 p22_28 (all_chunk _ _ 31 4 p22_31 (all_chunk _ _ 35 5 p22_35 (all_chunk _ _ 40 5 p22_40 (all_chunk _ _ 45 9 p22_45 (all_chunk _ _ 54 10 p22_54 (all_chunk _ _ 64 8 p22_64 (all_chunk _ _ 72 9 p22_72 (all_chunk _ _ 81 8 p22_81 (all_chunk _ _ 89 3 p22_89 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s22 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_0 : ((q23.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_6 : ((q23.drop 6).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_11 : ((q23.drop 11).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_19 : ((q23.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_25 : ((q23.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_29 : ((q23.drop 29).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_31 : ((q23.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_35 : ((q23.drop 35).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_43 : ((q23.drop 43).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_48 : ((q23.drop 48).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_54 : ((q23.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_58 : ((q23.drop 58).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_60 : ((q23.drop 60).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_65 : ((q23.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_69 : ((q23.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_73 : ((q23.drop 73).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_77 : ((q23.drop 77).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_83 : ((q23.drop 83).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p23_91 : ((q23.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok23 : nopt 7 s23 = false := by
  have h : q23.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p23_0 (all_chunk _ _ 6 5 p23_6 (all_chunk _ _ 11 8 p23_11 (all_chunk _ _ 19 6 p23_19 (all_chunk _ _ 25 4 p23_25 (all_chunk _ _ 29 2 p23_29 (all_chunk _ _ 31 4 p23_31 (all_chunk _ _ 35 8 p23_35 (all_chunk _ _ 43 5 p23_43 (all_chunk _ _ 48 6 p23_48 (all_chunk _ _ 54 4 p23_54 (all_chunk _ _ 58 2 p23_58 (all_chunk _ _ 60 5 p23_60 (all_chunk _ _ 65 4 p23_65 (all_chunk _ _ 69 4 p23_69 (all_chunk _ _ 73 4 p23_73 (all_chunk _ _ 77 6 p23_77 (all_chunk _ _ 83 8 p23_83 (all_chunk _ _ 91 1 p23_91 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s23 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_0 : ((q24.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_4 : ((q24.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_7 : ((q24.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_12 : ((q24.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_16 : ((q24.drop 16).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_19 : ((q24.drop 19).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_23 : ((q24.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_27 : ((q24.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_31 : ((q24.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_35 : ((q24.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_39 : ((q24.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_43 : ((q24.drop 43).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_48 : ((q24.drop 48).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_56 : ((q24.drop 56).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_63 : ((q24.drop 63).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_71 : ((q24.drop 71).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_79 : ((q24.drop 79).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p24_86 : ((q24.drop 86).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok24 : nopt 7 s24 = false := by
  have h : q24.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p24_0 (all_chunk _ _ 4 3 p24_4 (all_chunk _ _ 7 5 p24_7 (all_chunk _ _ 12 4 p24_12 (all_chunk _ _ 16 3 p24_16 (all_chunk _ _ 19 4 p24_19 (all_chunk _ _ 23 4 p24_23 (all_chunk _ _ 27 4 p24_27 (all_chunk _ _ 31 4 p24_31 (all_chunk _ _ 35 4 p24_35 (all_chunk _ _ 39 4 p24_39 (all_chunk _ _ 43 5 p24_43 (all_chunk _ _ 48 8 p24_48 (all_chunk _ _ 56 7 p24_56 (all_chunk _ _ 63 8 p24_63 (all_chunk _ _ 71 8 p24_71 (all_chunk _ _ 79 7 p24_79 (all_chunk _ _ 86 6 p24_86 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s24 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_0 : ((q25.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_4 : ((q25.drop 4).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_9 : ((q25.drop 9).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_11 : ((q25.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_15 : ((q25.drop 15).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_19 : ((q25.drop 19).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_25 : ((q25.drop 25).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_29 : ((q25.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_33 : ((q25.drop 33).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_36 : ((q25.drop 36).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_38 : ((q25.drop 38).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_42 : ((q25.drop 42).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_48 : ((q25.drop 48).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_53 : ((q25.drop 53).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_58 : ((q25.drop 58).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_60 : ((q25.drop 60).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_64 : ((q25.drop 64).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_66 : ((q25.drop 66).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_69 : ((q25.drop 69).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_72 : ((q25.drop 72).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_75 : ((q25.drop 75).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_79 : ((q25.drop 79).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_83 : ((q25.drop 83).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p25_89 : ((q25.drop 89).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok25 : nopt 7 s25 = false := by
  have h : q25.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p25_0 (all_chunk _ _ 4 5 p25_4 (all_chunk _ _ 9 2 p25_9 (all_chunk _ _ 11 4 p25_11 (all_chunk _ _ 15 4 p25_15 (all_chunk _ _ 19 6 p25_19 (all_chunk _ _ 25 4 p25_25 (all_chunk _ _ 29 4 p25_29 (all_chunk _ _ 33 3 p25_33 (all_chunk _ _ 36 2 p25_36 (all_chunk _ _ 38 4 p25_38 (all_chunk _ _ 42 6 p25_42 (all_chunk _ _ 48 5 p25_48 (all_chunk _ _ 53 5 p25_53 (all_chunk _ _ 58 2 p25_58 (all_chunk _ _ 60 4 p25_60 (all_chunk _ _ 64 2 p25_64 (all_chunk _ _ 66 3 p25_66 (all_chunk _ _ 69 3 p25_69 (all_chunk _ _ 72 3 p25_72 (all_chunk _ _ 75 4 p25_75 (all_chunk _ _ 79 4 p25_79 (all_chunk _ _ 83 6 p25_83 (all_chunk _ _ 89 7 p25_89 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s25 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_0 : ((q26.drop 0).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_2 : ((q26.drop 2).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_6 : ((q26.drop 6).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_9 : ((q26.drop 9).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_15 : ((q26.drop 15).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_24 : ((q26.drop 24).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_32 : ((q26.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_36 : ((q26.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_39 : ((q26.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_44 : ((q26.drop 44).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_49 : ((q26.drop 49).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_54 : ((q26.drop 54).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_58 : ((q26.drop 58).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_63 : ((q26.drop 63).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_68 : ((q26.drop 68).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_77 : ((q26.drop 77).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p26_85 : ((q26.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok26 : nopt 7 s26 = false := by
  have h : q26.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 2 p26_0 (all_chunk _ _ 2 4 p26_2 (all_chunk _ _ 6 3 p26_6 (all_chunk _ _ 9 6 p26_9 (all_chunk _ _ 15 9 p26_15 (all_chunk _ _ 24 8 p26_24 (all_chunk _ _ 32 4 p26_32 (all_chunk _ _ 36 3 p26_36 (all_chunk _ _ 39 5 p26_39 (all_chunk _ _ 44 5 p26_44 (all_chunk _ _ 49 5 p26_49 (all_chunk _ _ 54 4 p26_54 (all_chunk _ _ 58 5 p26_58 (all_chunk _ _ 63 5 p26_63 (all_chunk _ _ 68 9 p26_68 (all_chunk _ _ 77 8 p26_77 (all_chunk _ _ 85 7 p26_85 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s26 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_0 : ((q27.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_4 : ((q27.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_7 : ((q27.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_12 : ((q27.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_16 : ((q27.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_20 : ((q27.drop 20).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_23 : ((q27.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_27 : ((q27.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_31 : ((q27.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_35 : ((q27.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_39 : ((q27.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_43 : ((q27.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_49 : ((q27.drop 49).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_57 : ((q27.drop 57).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_65 : ((q27.drop 65).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_71 : ((q27.drop 71).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_78 : ((q27.drop 78).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p27_86 : ((q27.drop 86).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok27 : nopt 7 s27 = false := by
  have h : q27.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p27_0 (all_chunk _ _ 4 3 p27_4 (all_chunk _ _ 7 5 p27_7 (all_chunk _ _ 12 4 p27_12 (all_chunk _ _ 16 4 p27_16 (all_chunk _ _ 20 3 p27_20 (all_chunk _ _ 23 4 p27_23 (all_chunk _ _ 27 4 p27_27 (all_chunk _ _ 31 4 p27_31 (all_chunk _ _ 35 4 p27_35 (all_chunk _ _ 39 4 p27_39 (all_chunk _ _ 43 6 p27_43 (all_chunk _ _ 49 8 p27_49 (all_chunk _ _ 57 8 p27_57 (all_chunk _ _ 65 6 p27_65 (all_chunk _ _ 71 7 p27_71 (all_chunk _ _ 78 8 p27_78 (all_chunk _ _ 86 6 p27_86 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s27 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_0 : ((q28.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_5 : ((q28.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_9 : ((q28.drop 9).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_15 : ((q28.drop 15).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_23 : ((q28.drop 23).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_27 : ((q28.drop 27).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_32 : ((q28.drop 32).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_37 : ((q28.drop 37).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_44 : ((q28.drop 44).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_49 : ((q28.drop 49).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_52 : ((q28.drop 52).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_54 : ((q28.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_59 : ((q28.drop 59).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_62 : ((q28.drop 62).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_65 : ((q28.drop 65).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_69 : ((q28.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_73 : ((q28.drop 73).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_78 : ((q28.drop 78).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p28_85 : ((q28.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok28 : nopt 7 s28 = false := by
  have h : q28.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p28_0 (all_chunk _ _ 5 4 p28_5 (all_chunk _ _ 9 6 p28_9 (all_chunk _ _ 15 8 p28_15 (all_chunk _ _ 23 4 p28_23 (all_chunk _ _ 27 5 p28_27 (all_chunk _ _ 32 5 p28_32 (all_chunk _ _ 37 7 p28_37 (all_chunk _ _ 44 5 p28_44 (all_chunk _ _ 49 3 p28_49 (all_chunk _ _ 52 2 p28_52 (all_chunk _ _ 54 5 p28_54 (all_chunk _ _ 59 3 p28_59 (all_chunk _ _ 62 3 p28_62 (all_chunk _ _ 65 4 p28_65 (all_chunk _ _ 69 4 p28_69 (all_chunk _ _ 73 5 p28_73 (all_chunk _ _ 78 7 p28_78 (all_chunk _ _ 85 7 p28_85 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s28 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_0 : ((q29.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_6 : ((q29.drop 6).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_12 : ((q29.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_15 : ((q29.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_18 : ((q29.drop 18).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_23 : ((q29.drop 23).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_29 : ((q29.drop 29).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_33 : ((q29.drop 33).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_35 : ((q29.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_39 : ((q29.drop 39).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_42 : ((q29.drop 42).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_47 : ((q29.drop 47).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_52 : ((q29.drop 52).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_57 : ((q29.drop 57).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_59 : ((q29.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_63 : ((q29.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_67 : ((q29.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_71 : ((q29.drop 71).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_73 : ((q29.drop 73).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_76 : ((q29.drop 76).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_78 : ((q29.drop 78).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_82 : ((q29.drop 82).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_86 : ((q29.drop 86).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_91 : ((q29.drop 91).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p29_95 : ((q29.drop 95).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok29 : nopt 7 s29 = false := by
  have h : q29.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p29_0 (all_chunk _ _ 6 6 p29_6 (all_chunk _ _ 12 3 p29_12 (all_chunk _ _ 15 3 p29_15 (all_chunk _ _ 18 5 p29_18 (all_chunk _ _ 23 6 p29_23 (all_chunk _ _ 29 4 p29_29 (all_chunk _ _ 33 2 p29_33 (all_chunk _ _ 35 4 p29_35 (all_chunk _ _ 39 3 p29_39 (all_chunk _ _ 42 5 p29_42 (all_chunk _ _ 47 5 p29_47 (all_chunk _ _ 52 5 p29_52 (all_chunk _ _ 57 2 p29_57 (all_chunk _ _ 59 4 p29_59 (all_chunk _ _ 63 4 p29_63 (all_chunk _ _ 67 4 p29_67 (all_chunk _ _ 71 2 p29_71 (all_chunk _ _ 73 3 p29_73 (all_chunk _ _ 76 2 p29_76 (all_chunk _ _ 78 4 p29_78 (all_chunk _ _ 82 4 p29_82 (all_chunk _ _ 86 5 p29_86 (all_chunk _ _ 91 4 p29_91 (all_chunk _ _ 95 1 p29_95 (by decide +kernel))))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s29 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_0 : ((q30.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_5 : ((q30.drop 5).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_10 : ((q30.drop 10).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_14 : ((q30.drop 14).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_17 : ((q30.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_21 : ((q30.drop 21).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_25 : ((q30.drop 25).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_28 : ((q30.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_32 : ((q30.drop 32).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_35 : ((q30.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_39 : ((q30.drop 39).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_44 : ((q30.drop 44).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_50 : ((q30.drop 50).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_59 : ((q30.drop 59).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_68 : ((q30.drop 68).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_77 : ((q30.drop 77).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p30_85 : ((q30.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok30 : nopt 7 s30 = false := by
  have h : q30.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p30_0 (all_chunk _ _ 5 5 p30_5 (all_chunk _ _ 10 4 p30_10 (all_chunk _ _ 14 3 p30_14 (all_chunk _ _ 17 4 p30_17 (all_chunk _ _ 21 4 p30_21 (all_chunk _ _ 25 3 p30_25 (all_chunk _ _ 28 4 p30_28 (all_chunk _ _ 32 3 p30_32 (all_chunk _ _ 35 4 p30_35 (all_chunk _ _ 39 5 p30_39 (all_chunk _ _ 44 6 p30_44 (all_chunk _ _ 50 9 p30_50 (all_chunk _ _ 59 9 p30_59 (all_chunk _ _ 68 9 p30_68 (all_chunk _ _ 77 8 p30_77 (all_chunk _ _ 85 7 p30_85 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s30 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_0 : ((q31.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_4 : ((q31.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_7 : ((q31.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_11 : ((q31.drop 11).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_13 : ((q31.drop 13).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_17 : ((q31.drop 17).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_21 : ((q31.drop 21).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_23 : ((q31.drop 23).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_28 : ((q31.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_32 : ((q31.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_36 : ((q31.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_39 : ((q31.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_43 : ((q31.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_49 : ((q31.drop 49).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_58 : ((q31.drop 58).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_66 : ((q31.drop 66).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_70 : ((q31.drop 70).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_78 : ((q31.drop 78).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p31_85 : ((q31.drop 85).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok31 : nopt 7 s31 = false := by
  have h : q31.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p31_0 (all_chunk _ _ 4 3 p31_4 (all_chunk _ _ 7 4 p31_7 (all_chunk _ _ 11 2 p31_11 (all_chunk _ _ 13 4 p31_13 (all_chunk _ _ 17 4 p31_17 (all_chunk _ _ 21 2 p31_21 (all_chunk _ _ 23 5 p31_23 (all_chunk _ _ 28 4 p31_28 (all_chunk _ _ 32 4 p31_32 (all_chunk _ _ 36 3 p31_36 (all_chunk _ _ 39 4 p31_39 (all_chunk _ _ 43 6 p31_43 (all_chunk _ _ 49 9 p31_49 (all_chunk _ _ 58 8 p31_58 (all_chunk _ _ 66 4 p31_66 (all_chunk _ _ 70 8 p31_70 (all_chunk _ _ 78 7 p31_78 (all_chunk _ _ 85 7 p31_85 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s31 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_0 : ((q32.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_4 : ((q32.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_7 : ((q32.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_12 : ((q32.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_16 : ((q32.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_20 : ((q32.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_24 : ((q32.drop 24).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_29 : ((q32.drop 29).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_32 : ((q32.drop 32).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_35 : ((q32.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_39 : ((q32.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_43 : ((q32.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_49 : ((q32.drop 49).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_56 : ((q32.drop 56).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_63 : ((q32.drop 63).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_71 : ((q32.drop 71).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_78 : ((q32.drop 78).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p32_86 : ((q32.drop 86).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok32 : nopt 7 s32 = false := by
  have h : q32.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p32_0 (all_chunk _ _ 4 3 p32_4 (all_chunk _ _ 7 5 p32_7 (all_chunk _ _ 12 4 p32_12 (all_chunk _ _ 16 4 p32_16 (all_chunk _ _ 20 4 p32_20 (all_chunk _ _ 24 5 p32_24 (all_chunk _ _ 29 3 p32_29 (all_chunk _ _ 32 3 p32_32 (all_chunk _ _ 35 4 p32_35 (all_chunk _ _ 39 4 p32_39 (all_chunk _ _ 43 6 p32_43 (all_chunk _ _ 49 7 p32_49 (all_chunk _ _ 56 7 p32_56 (all_chunk _ _ 63 8 p32_63 (all_chunk _ _ 71 7 p32_71 (all_chunk _ _ 78 8 p32_78 (all_chunk _ _ 86 6 p32_86 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s32 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_0 : ((q33.drop 0).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_6 : ((q33.drop 6).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_11 : ((q33.drop 11).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_17 : ((q33.drop 17).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_22 : ((q33.drop 22).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_25 : ((q33.drop 25).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_27 : ((q33.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_31 : ((q33.drop 31).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_37 : ((q33.drop 37).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_44 : ((q33.drop 44).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_46 : ((q33.drop 46).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_50 : ((q33.drop 50).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_53 : ((q33.drop 53).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_57 : ((q33.drop 57).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_63 : ((q33.drop 63).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_66 : ((q33.drop 66).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_69 : ((q33.drop 69).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_73 : ((q33.drop 73).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_78 : ((q33.drop 78).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_80 : ((q33.drop 80).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_84 : ((q33.drop 84).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_88 : ((q33.drop 88).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_91 : ((q33.drop 91).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p33_94 : ((q33.drop 94).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok33 : nopt 7 s33 = false := by
  have h : q33.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 6 p33_0 (all_chunk _ _ 6 5 p33_6 (all_chunk _ _ 11 6 p33_11 (all_chunk _ _ 17 5 p33_17 (all_chunk _ _ 22 3 p33_22 (all_chunk _ _ 25 2 p33_25 (all_chunk _ _ 27 4 p33_27 (all_chunk _ _ 31 6 p33_31 (all_chunk _ _ 37 7 p33_37 (all_chunk _ _ 44 2 p33_44 (all_chunk _ _ 46 4 p33_46 (all_chunk _ _ 50 3 p33_50 (all_chunk _ _ 53 4 p33_53 (all_chunk _ _ 57 6 p33_57 (all_chunk _ _ 63 3 p33_63 (all_chunk _ _ 66 3 p33_66 (all_chunk _ _ 69 4 p33_69 (all_chunk _ _ 73 5 p33_73 (all_chunk _ _ 78 2 p33_78 (all_chunk _ _ 80 4 p33_80 (all_chunk _ _ 84 4 p33_84 (all_chunk _ _ 88 3 p33_88 (all_chunk _ _ 91 3 p33_91 (all_chunk _ _ 94 2 p33_94 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s33 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_0 : ((q34.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_5 : ((q34.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_9 : ((q34.drop 9).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_11 : ((q34.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_15 : ((q34.drop 15).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_24 : ((q34.drop 24).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_32 : ((q34.drop 32).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_38 : ((q34.drop 38).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_47 : ((q34.drop 47).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_54 : ((q34.drop 54).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_59 : ((q34.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_63 : ((q34.drop 63).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_66 : ((q34.drop 66).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_71 : ((q34.drop 71).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_76 : ((q34.drop 76).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_82 : ((q34.drop 82).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p34_91 : ((q34.drop 91).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok34 : nopt 7 s34 = false := by
  have h : q34.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p34_0 (all_chunk _ _ 5 4 p34_5 (all_chunk _ _ 9 2 p34_9 (all_chunk _ _ 11 4 p34_11 (all_chunk _ _ 15 9 p34_15 (all_chunk _ _ 24 8 p34_24 (all_chunk _ _ 32 6 p34_32 (all_chunk _ _ 38 9 p34_38 (all_chunk _ _ 47 7 p34_47 (all_chunk _ _ 54 5 p34_54 (all_chunk _ _ 59 4 p34_59 (all_chunk _ _ 63 3 p34_63 (all_chunk _ _ 66 5 p34_66 (all_chunk _ _ 71 5 p34_71 (all_chunk _ _ 76 6 p34_76 (all_chunk _ _ 82 9 p34_82 (all_chunk _ _ 91 1 p34_91 (by decide +kernel))))))))))))))))))
  rw [nopt_succ, show nisGoal s34 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_0 : ((q35.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_4 : ((q35.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_7 : ((q35.drop 7).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_12 : ((q35.drop 12).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_16 : ((q35.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_20 : ((q35.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_24 : ((q35.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_28 : ((q35.drop 28).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_32 : ((q35.drop 32).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_36 : ((q35.drop 36).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_39 : ((q35.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_43 : ((q35.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_49 : ((q35.drop 49).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_57 : ((q35.drop 57).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_65 : ((q35.drop 65).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_71 : ((q35.drop 71).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_78 : ((q35.drop 78).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p35_86 : ((q35.drop 86).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok35 : nopt 7 s35 = false := by
  have h : q35.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p35_0 (all_chunk _ _ 4 3 p35_4 (all_chunk _ _ 7 5 p35_7 (all_chunk _ _ 12 4 p35_12 (all_chunk _ _ 16 4 p35_16 (all_chunk _ _ 20 4 p35_20 (all_chunk _ _ 24 4 p35_24 (all_chunk _ _ 28 4 p35_28 (all_chunk _ _ 32 4 p35_32 (all_chunk _ _ 36 3 p35_36 (all_chunk _ _ 39 4 p35_39 (all_chunk _ _ 43 6 p35_43 (all_chunk _ _ 49 8 p35_49 (all_chunk _ _ 57 8 p35_57 (all_chunk _ _ 65 6 p35_65 (all_chunk _ _ 71 7 p35_71 (all_chunk _ _ 78 8 p35_78 (all_chunk _ _ 86 6 p35_86 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s35 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_0 : ((q36.drop 0).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_3 : ((q36.drop 3).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_6 : ((q36.drop 6).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_8 : ((q36.drop 8).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_12 : ((q36.drop 12).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_15 : ((q36.drop 15).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_18 : ((q36.drop 18).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_22 : ((q36.drop 22).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_25 : ((q36.drop 25).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_27 : ((q36.drop 27).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_31 : ((q36.drop 31).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_34 : ((q36.drop 34).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_37 : ((q36.drop 37).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_40 : ((q36.drop 40).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_43 : ((q36.drop 43).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_48 : ((q36.drop 48).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_52 : ((q36.drop 52).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_55 : ((q36.drop 55).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_62 : ((q36.drop 62).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_69 : ((q36.drop 69).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_74 : ((q36.drop 74).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_81 : ((q36.drop 81).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p36_87 : ((q36.drop 87).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok36 : nopt 7 s36 = false := by
  have h : q36.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 3 p36_0 (all_chunk _ _ 3 3 p36_3 (all_chunk _ _ 6 2 p36_6 (all_chunk _ _ 8 4 p36_8 (all_chunk _ _ 12 3 p36_12 (all_chunk _ _ 15 3 p36_15 (all_chunk _ _ 18 4 p36_18 (all_chunk _ _ 22 3 p36_22 (all_chunk _ _ 25 2 p36_25 (all_chunk _ _ 27 4 p36_27 (all_chunk _ _ 31 3 p36_31 (all_chunk _ _ 34 3 p36_34 (all_chunk _ _ 37 3 p36_37 (all_chunk _ _ 40 3 p36_40 (all_chunk _ _ 43 5 p36_43 (all_chunk _ _ 48 4 p36_48 (all_chunk _ _ 52 3 p36_52 (all_chunk _ _ 55 7 p36_55 (all_chunk _ _ 62 7 p36_62 (all_chunk _ _ 69 5 p36_69 (all_chunk _ _ 74 7 p36_74 (all_chunk _ _ 81 6 p36_81 (all_chunk _ _ 87 4 p36_87 (by decide +kernel))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s36 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_0 : ((q37.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_5 : ((q37.drop 5).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_8 : ((q37.drop 8).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_14 : ((q37.drop 14).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_19 : ((q37.drop 19).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_24 : ((q37.drop 24).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_26 : ((q37.drop 26).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_30 : ((q37.drop 30).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_34 : ((q37.drop 34).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_40 : ((q37.drop 40).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_47 : ((q37.drop 47).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_50 : ((q37.drop 50).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_54 : ((q37.drop 54).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_60 : ((q37.drop 60).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_65 : ((q37.drop 65).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_67 : ((q37.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_71 : ((q37.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_75 : ((q37.drop 75).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_80 : ((q37.drop 80).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_83 : ((q37.drop 83).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_87 : ((q37.drop 87).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_88 : ((q37.drop 88).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_90 : ((q37.drop 90).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p37_94 : ((q37.drop 94).take 1).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok37 : nopt 7 s37 = false := by
  have h : q37.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p37_0 (all_chunk _ _ 5 3 p37_5 (all_chunk _ _ 8 6 p37_8 (all_chunk _ _ 14 5 p37_14 (all_chunk _ _ 19 5 p37_19 (all_chunk _ _ 24 2 p37_24 (all_chunk _ _ 26 4 p37_26 (all_chunk _ _ 30 4 p37_30 (all_chunk _ _ 34 6 p37_34 (all_chunk _ _ 40 7 p37_40 (all_chunk _ _ 47 3 p37_47 (all_chunk _ _ 50 4 p37_50 (all_chunk _ _ 54 6 p37_54 (all_chunk _ _ 60 5 p37_60 (all_chunk _ _ 65 2 p37_65 (all_chunk _ _ 67 4 p37_67 (all_chunk _ _ 71 4 p37_71 (all_chunk _ _ 75 5 p37_75 (all_chunk _ _ 80 3 p37_80 (all_chunk _ _ 83 4 p37_83 (all_chunk _ _ 87 1 p37_87 (all_chunk _ _ 88 2 p37_88 (all_chunk _ _ 90 4 p37_90 (all_chunk _ _ 94 1 p37_94 (by decide +kernel)))))))))))))))))))))))))
  rw [nopt_succ, show nisGoal s37 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_0 : ((q38.drop 0).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_5 : ((q38.drop 5).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_9 : ((q38.drop 9).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_11 : ((q38.drop 11).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_15 : ((q38.drop 15).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_22 : ((q38.drop 22).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_29 : ((q38.drop 29).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_34 : ((q38.drop 34).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_39 : ((q38.drop 39).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_47 : ((q38.drop 47).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_54 : ((q38.drop 54).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_57 : ((q38.drop 57).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_59 : ((q38.drop 59).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_63 : ((q38.drop 63).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_67 : ((q38.drop 67).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_71 : ((q38.drop 71).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_75 : ((q38.drop 75).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_81 : ((q38.drop 81).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p38_89 : ((q38.drop 89).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok38 : nopt 7 s38 = false := by
  have h : q38.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 5 p38_0 (all_chunk _ _ 5 4 p38_5 (all_chunk _ _ 9 2 p38_9 (all_chunk _ _ 11 4 p38_11 (all_chunk _ _ 15 7 p38_15 (all_chunk _ _ 22 7 p38_22 (all_chunk _ _ 29 5 p38_29 (all_chunk _ _ 34 5 p38_34 (all_chunk _ _ 39 8 p38_39 (all_chunk _ _ 47 7 p38_47 (all_chunk _ _ 54 3 p38_54 (all_chunk _ _ 57 2 p38_57 (all_chunk _ _ 59 4 p38_59 (all_chunk _ _ 63 4 p38_63 (all_chunk _ _ 67 4 p38_67 (all_chunk _ _ 71 4 p38_71 (all_chunk _ _ 75 6 p38_75 (all_chunk _ _ 81 8 p38_81 (all_chunk _ _ 89 3 p38_89 (by decide +kernel))))))))))))))))))))
  rw [nopt_succ, show nisGoal s38 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_0 : ((q39.drop 0).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_4 : ((q39.drop 4).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_7 : ((q39.drop 7).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_11 : ((q39.drop 11).take 5).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_16 : ((q39.drop 16).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_20 : ((q39.drop 20).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_24 : ((q39.drop 24).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_28 : ((q39.drop 28).take 3).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_31 : ((q39.drop 31).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_35 : ((q39.drop 35).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_39 : ((q39.drop 39).take 4).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_43 : ((q39.drop 43).take 6).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_49 : ((q39.drop 49).take 7).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_56 : ((q39.drop 56).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_64 : ((q39.drop 64).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_73 : ((q39.drop 73).take 9).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_82 : ((q39.drop 82).take 8).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem p39_90 : ((q39.drop 90).take 2).all (fun c => !nopt 6 c) = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem ok39 : nopt 7 s39 = false := by
  have h : q39.all (fun c => !nopt 6 c) = true := (all_chunk _ _ 0 4 p39_0 (all_chunk _ _ 4 3 p39_4 (all_chunk _ _ 7 4 p39_7 (all_chunk _ _ 11 5 p39_11 (all_chunk _ _ 16 4 p39_16 (all_chunk _ _ 20 4 p39_20 (all_chunk _ _ 24 4 p39_24 (all_chunk _ _ 28 3 p39_28 (all_chunk _ _ 31 4 p39_31 (all_chunk _ _ 35 4 p39_35 (all_chunk _ _ 39 4 p39_39 (all_chunk _ _ 43 6 p39_43 (all_chunk _ _ 49 7 p39_49 (all_chunk _ _ 56 8 p39_56 (all_chunk _ _ 64 9 p39_64 (all_chunk _ _ 73 9 p39_73 (all_chunk _ _ 82 8 p39_82 (all_chunk _ _ 90 2 p39_90 (by decide +kernel)))))))))))))))))))
  rw [nopt_succ, show nisGoal s39 = false by decide +kernel, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simpa using List.all_eq_true.mp h c hc

def inputs : List W := nums.map (BitVec.ofNat 500)

set_option maxRecDepth 16000 in
theorem nums_eq : inputs.map BitVec.toNat = nums := by decide +kernel

set_option maxRecDepth 16000 in
theorem front_eq : (allKids 7 nums).map isort = [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31, s32, s33, s34, s35, s36, s37, s38, s39] := by decide +kernel

set_option maxRecDepth 16000 in
theorem noEight (t : W) (ht : t = goal ∨ t = ~~~goal)
    (run : build basicOps t 8 inputs.toFinset) : False := by
  apply refute 7 inputs (by decide +kernel) _ _ t ht run
  · rw [nums_eq]
    decide +kernel
  · rw [nums_eq]
    have h : ((allKids 7 nums).map isort).all (fun c => !nopt 7 c) = true := by
      rw [front_eq]
      simp only [List.all_cons, List.all_nil, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11, ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23, ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35, ok36, ok37, ok38, ok39, Bool.not_false, Bool.true_and]
    exact List.all_eq_true.mpr fun c hc => (dead_eq 7 c).trans
      (List.all_eq_true.mp h (isort c) (List.mem_map.mpr ⟨c, hc, rfl⟩))
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 16000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 16000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 16000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 500 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 500)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 16000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 500) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 500) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 500) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#500)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 16000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
set_option maxRecDepth 16000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def targetTable : ℕ := 4276808426 * 2 ^ 32 + 4276808320

def targetSix (x : Fin 6 → Bool) : Bool :=
  targetTable.testBit (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def related (x y : W) : Prop := x = y ∨ x = 0 ∨ x = ~~~0

set_option maxRecDepth 16000 in
theorem related_read {w v : List W} (h : List.Forall₂ related w v) (i : ℕ) :
    related (w.getD i 0) (v.getD i 0) := by
  induction h generalizing i with
  | nil => exact .inl rfl
  | cons hxy _ ih =>
    cases i with
    | zero => exact hxy
    | succ i => exact ih i

set_option maxRecDepth 16000 in
theorem related_not {x y : W} (h : related x y) : related (~~~x) (~~~y) := by
  rcases h with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inr rfl)
  · exact .inr (.inl BitVec.not_not)

set_option maxRecDepth 16000 in
theorem related_and {av : Finset W} {x y x' y' : W}
    (hx : holds av x) (hy : holds av y) (rx : related x x') (ry : related y y') :
    related (x &&& y) (x' &&& y') ∨ holds av (x &&& y) := by
  rcases rx with rfl | rfl | rfl
  · rcases ry with rfl | rfl | rfl
    · exact .inl (.inl rfl)
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inr (.inl rfl)
    · rw [show x &&& ~~~(0 : W) = x from BitVec.and_allOnes]; exact .inr hx
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inr (.inl rfl)
  · rw [show ~~~(0 : W) &&& y = y from BitVec.allOnes_and]; exact .inr hy

set_option maxRecDepth 16000 in
theorem related_or {av : Finset W} {x y x' y' : W}
    (hx : holds av x) (hy : holds av y) (rx : related x x') (ry : related y y') :
    related (x ||| y) (x' ||| y') ∨ holds av (x ||| y) := by
  rcases related_and (holds_not hx) (holds_not hy) (related_not rx) (related_not ry) with h | h
  · exact .inl (by simpa only [BitVec.not_and, BitVec.not_not] using related_not h)
  · exact .inr (by simpa only [BitVec.not_and, BitVec.not_not] using holds_not h)

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem gate_related (w v : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (hr : List.Forall₂ related w v) (g : Gate) (hg : legal g) :
    related (action w g) (action v g) ∨ (isBinary g = true ∧ holds av (action w g)) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _ | ⟨i, _ | ⟨j, _ | ⟨u, tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl | rfl | rfl <;>
    simp only [isBinary, action, List.map_nil, List.map_cons, List.head?_nil, List.head?_cons,
      List.foldr_nil, List.foldr_cons, Option.map_none, Option.map_some, Option.getD_none,
      Option.getD_some, true_and, Bool.false_eq_true, false_and, or_false,
      show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
      show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl rfl
    | exact .inl (related_read hr _)
    | exact related_not (related_read hr _)
    | exact related_and (available_read hw _) (available_read hw _) (related_read hr _) (related_read hr _)
    | exact related_or (available_read hw _) (available_read hw _) (related_read hr _) (related_read hr _)

def probe : Fin 500 := 0

set_option maxRecDepth 5000 in
set_option maxRecDepth 16000 in
theorem compile_strict (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w v : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u) (hr : List.Forall₂ related w v)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal)
    (hd : (gs.foldl step (v.map (bit probe))).getD out false ≠ bit probe goal) :
    ∃ t m, (t = goal ∨ t = ~~~goal) ∧ m < binaryCost gs ∧ build basicOps t m av := by
  induction gs generalizing w v av with
  | nil =>
    have eq : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have r := related_read hr out
    rw [eq] at r
    rcases r with same | zero | ones
    · exact False.elim (hd (by simp only [List.foldl_nil, read_bit, ← same]))
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
  | cons g gs ih =>
    let z := action w g
    let z' := action v g
    have ok := hg g (by simp)
    have good (g' : Gate) (h : g' ∈ gs) := hg g' (by simp [h])
    have he' (k) : (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      simpa only [List.foldl_cons, action_spec w g ok] using he k
    have hd' : (gs.foldl step ((v ++ [z']).map (bit probe))).getD out false ≠ bit probe goal := by
      simpa only [List.foldl_cons, action_spec v g ok] using hd
    have extend (A : Finset W) (old : ∀ u ∈ w, holds A u) (new : holds A z) :
        ∀ u ∈ w ++ [z], holds A u := by
      intro u hu
      rcases List.mem_append.mp hu with h | h
      · exact old u h
      · exact List.mem_singleton.mp h ▸ new
    rcases gate_related w v av hw hr g ok with rr | ⟨cost, free⟩
    · have rr' : List.Forall₂ related (w ++ [z]) (v ++ [z']) := List.rel_append hr (.cons rr .nil)
      have cont (A : Finset W) (old : ∀ u ∈ w, holds A u) (new : holds A z) :=
        ih good (w ++ [z]) (v ++ [z']) A (extend A old new) rr' he' hd'
      have reach := gate_reach w av hw g ok
      cases cost : isBinary g
      · simp only [cost, Bool.false_eq_true, ite_false] at reach
        simpa [binaryCost, cost] using cont av hw reach
      · simp only [cost, ite_true] at reach
        have len : binaryCost (g :: gs) = binaryCost gs + 1 := by simp [binaryCost, cost]
        rcases reach with old | ⟨a, ha, b, hb, ne, p, hop, hp⟩
        · obtain ⟨t, m, ht, hm, run⟩ := cont av hw old
          exact ⟨t, m, ht, by omega, run⟩
        · obtain ⟨t, m, ht, hm, run⟩ := cont (insert p av) (fun u hu => holds_insert (hw u hu)) hp
          exact ⟨t, m+1, ht, by omega, Or.inr ⟨a, ha, b, hb, ne, p, hop, run⟩⟩
    · obtain ⟨t, ht, run⟩ := compile gs out good (w ++ [z]) av (extend av hw free) he'
      exact ⟨t, binaryCost gs, ht, by simp [binaryCost, cost], run⟩

def restricted : List W := [(inputs.getD 0 0), (inputs.getD 1 0), (inputs.getD 2 0), (inputs.getD 3 0), (inputs.getD 4 0), 0]
def flipped : List W := [(inputs.getD 0 0), (inputs.getD 1 0), (inputs.getD 2 0), (inputs.getD 3 0), (inputs.getD 4 0), (~~~0)]

theorem rows_related : List.Forall₂ related restricted flipped := by
  unfold restricted flipped
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inl rfl) ?_
  refine List.Forall₂.cons (.inr (.inl rfl)) ?_
  exact .nil

set_option maxRecDepth 8000 in
set_option maxRecDepth 16000 in
theorem restricted_rows : ∀ k : Fin 500,
    targetSix (fun i => bit k (restricted.getD i.val 0)) = bit k goal := by decide +kernel

set_option maxRecDepth 16000 in
theorem flipped_row : targetSix (fun i => bit probe (flipped.getD i.val 0)) ≠ bit probe goal := by
  decide +kernel

set_option maxRecDepth 16000 in
theorem six_lower_bound (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = targetSix x) :
    9 < binaryCost gs := by
  have evalRow (ws : List W) (width : ws.length = 6) (k : Fin 500) :
      (gs.foldl step (ws.map (bit k))).getD out false =
        targetSix (fun i => bit k (ws.getD i.val 0)) := by
    let x (i : Fin 6) := bit k (ws.getD i.val 0)
    have same : List.ofFn x = ws.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ws.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,out⟩ (ws.map (bit k)) = targetSix x
    rw [← same, he]
  have available : ∀ u ∈ restricted, holds inputs.toFinset u := by
    intro u hu
    simp only [restricted, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
    · exact .inr (.inr ⟨(inputs.getD 0 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 1 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 2 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 3 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inr (.inr ⟨(inputs.getD 4 0), List.mem_toFinset.mpr (by decide +kernel), .inl rfl⟩)
    · exact .inl rfl
  obtain ⟨t, m, ht, hm, run⟩ := compile_strict gs out hg restricted flipped inputs.toFinset available
    rows_related (fun k => (evalRow restricted rfl k).trans (restricted_rows k))
    (by rw [evalRow flipped rfl]; exact flipped_row)
  have lift {a b : ℕ} (le : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction le with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  by_contra! small
  exact noEight t ht (lift (by omega) run)

def upperCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[
    ⟨.and, [0, 1]⟩,
    ⟨.and, [3, 4]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.and, [2, 8]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [0, 11]⟩,
    ⟨.or, [3, 4]⟩,
    ⟨.or, [13, 5]⟩,
    ⟨.and, [12, 14]⟩,
    ⟨.or, [15, 9]⟩], 16⟩

set_option maxRecDepth 16000 in
theorem elevenGateUpper : PEqualNP.MetaComplexity.Monotone2 upperCircuit ∧ upperCircuit.size = 11 ∧
    ∀ x : Fin 6 → Bool, upperCircuit.eval (List.ofFn x) = targetSix x := by
  refine ⟨?_, by decide, ?_⟩
  · simp [upperCircuit, PEqualNP.MetaComplexity.Monotone2]
  · decide +kernel

end PEqualNP.Outside.L_meta_41040_aux

set_option maxRecDepth 16000 in
theorem PEqualNP.Outside.L_meta_41040 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4276808320) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro s hs
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_41040_aux.binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists
        (p := PEqualNP.Outside.L_meta_41040_aux.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_41040_aux.isBinary, op]⟩
    have bound := PEqualNP.Outside.L_meta_41040_aux.six_lower_bound C.gates C.output fits computes
    refine ⟨PEqualNP.Outside.L_meta_41040_aux.upperCircuit, PEqualNP.Outside.L_meta_41040_aux.elevenGateUpper.1,
      ?_, PEqualNP.Outside.L_meta_41040_aux.elevenGateUpper.2.2⟩
    change 11 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g,mem,eq⟩).elim)), cap⟩
