import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36593

open PEqualNP.CircuitLowerBounds

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

abbrev W := BitVec 60

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 30 := ((x >>> 30) ^^^ x).setWidth 30
def cuts (ws : List W) : BitVec 30 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 30) ++ (0 : BitVec 30)
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

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 30) (w : W) : Prop :=
  w.getLsbD (30+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 30) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 30+i.val < 60 := by omega
  have hi' : i.val < 60 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem goal_differs {t : W} (ht : t = goal ∨ t = ~~~goal) : ∀ i, differs i t := by
  rcases ht with rfl | rfl <;> unfold differs <;> decide +kernel

theorem cuts_spec (ws : List W) (i : Fin 30) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs hg _) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 30)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem and_ones (x : W) : x &&& ~~~0 = x :=
  (congrArg (x &&& ·) (BitVec.not_zero (n := 60))).trans BitVec.and_allOnes

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · rw [BitVec.and_comm, and_ones]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · rw [and_ones]; exact .inl oldx
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

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 60) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 60) :
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

theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 60) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#60)[k.val] = false; simp
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

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

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
    and_ones]

  · exact .inl (.inr (.inl rfl))
  · exact .inl (.inl rfl)
  · exact .inr (.inl rfl)
  · exact .inl (available_read hw _)
  · exact .inl (available_read hw _)
  · exact holds_not (available_read hw _)
  · exact and_reach (available_read hw _) (available_read hw _)
  · exact or_reach (available_read hw _) (available_read hw _)
  · exact holds_not (available_read hw _)

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
    · exact False.elim ((by decide +kernel : goal ≠ 0) zero)
    · exact False.elim ((by decide +kernel : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
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
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def ins : List W := [560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261, 1152920955840713728]

def checkMove (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) (w : W) : Bool :=
  let base := cuts r
  let v := sep w ||| base
  ((v == -1) && next extra (w :: r)) ||
  ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                     ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
  ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def firstTriple (i : Nat) : W × W × List W := (pairs ins).getD i (0, 0, [])
def firstGate (i : Nat) : Bool :=
  let (a, b, r) := firstTriple i
  dispatch 2 (optimized 6) a b r
def lane (i j : Nat) : Bool :=
  let (a, b, r) := firstTriple i
  checkMove 2 (optimized 6) a b r ((ops a b).getD j 0)

theorem lanes_join (i : Nat) (h0 : lane i 0 = false) (h1 : lane i 1 = false)
    (h2 : lane i 2 = false) (h3 : lane i 3 = false) : firstGate i = false := by
  generalize e : firstTriple i = q at *
  obtain ⟨a, b, r⟩ := q
  simp only [lane, e, ops, List.getD] at h0 h1 h2 h3
  simp only [firstGate, e, dispatch, ops, List.any_cons, List.any_nil]
  change (checkMove 2 (optimized 6) a b r (a &&& b) ||
         (checkMove 2 (optimized 6) a b r (a ||| b) ||
         (checkMove 2 (optimized 6) a b r (a &&& ~~~b) ||
         (checkMove 2 (optimized 6) a b r (b &&& ~~~a) || false)))) = false
  change checkMove 2 (optimized 6) a b r (a &&& b) = false at h0
  change checkMove 2 (optimized 6) a b r (a ||| b) = false at h1
  change checkMove 2 (optimized 6) a b r (a &&& ~~~b) = false at h2
  change checkMove 2 (optimized 6) a b r (b &&& ~~~a) = false at h3
  rw [h0, h1, h2, h3] <;> rfl

def branch (i j mode : Nat) : Bool :=
  let (a, b, r) := firstTriple i
  let w := (ops a b).getD j 0
  let v := sep w ||| cuts r
  match mode with
  | 0 => (v == -1) && optimized 6 2 (w :: r)
  | 1 => (2 != 0) && (v ||| sep a == -1) && optimized 6 1 (w :: a :: r)
  | 2 => (2 != 0) && (v ||| sep b == -1) && optimized 6 1 (w :: b :: r)
  | _ => (2 ≥ 2) && (v ||| sep a ||| sep b == -1) && optimized 6 0 (w :: a :: b :: r)

def branchArgs (i j mode : Nat) : Bool × Nat × List W :=
  let (a, b, r) := firstTriple i
  let w := (ops a b).getD j 0
  let v := sep w ||| cuts r
  match mode with
  | 0 => (v == -1, 2, w :: r)
  | 1 => ((2 != 0) && (v ||| sep a == -1), 1, w :: a :: r)
  | 2 => ((2 != 0) && (v ||| sep b == -1), 1, w :: b :: r)
  | _ => ((2 ≥ 2) && (v ||| sep a ||| sep b == -1), 0, w :: a :: b :: r)

theorem branch_expand (i j mode : Nat) :
    branch i j mode = ((branchArgs i j mode).1 && optimized 6 (branchArgs i j mode).2.1 (branchArgs i j mode).2.2) := by
  rcases h : firstTriple i with ⟨a, b, r⟩
  cases mode with
  | zero => simp only [branch, branchArgs, h]
  | succ t =>
    cases t with
    | zero => simp only [branch, branchArgs, h, Bool.and_assoc]
    | succ v =>
      cases v <;> simp only [branch, branchArgs, h, Bool.and_assoc]

theorem branch_lift (i j mode e : Nat) (st : List W)
    (ha : branchArgs i j mode = (true, e, st)) (hc : optimized 6 e st = false) :
    branch i j mode = false := by
  rw [branch_expand, ha]
  exact hc

theorem branch_join (i j : Nat) (h0 : branch i j 0 = false)
    (h1 : branch i j 1 = false) (h2 : branch i j 2 = false)
    (h3 : branch i j 3 = false) : lane i j = false := by
  have e : lane i j = (branch i j 0 || (branch i j 1 || branch i j 2) || branch i j 3) := by
    cases hh : firstTriple i with
    | mk a br =>
      obtain ⟨b, r⟩ := br
      simp only [lane, branch, hh, checkMove]
      rfl
  rw [e, h0, h1, h2, h3] <;> rfl

theorem splitDispatch (e k : Nat) (a b : W) (r : List W)
    (h0 : checkMove e (optimized k) a b r (a &&& b) = false)
    (h1 : checkMove e (optimized k) a b r (a ||| b) = false)
    (h2 : checkMove e (optimized k) a b r (a &&& ~~~b) = false)
    (h3 : checkMove e (optimized k) a b r (b &&& ~~~a) = false) :
    dispatch e (optimized k) a b r = false := by
  change (checkMove e (optimized k) a b r (a &&& b) ||
    (checkMove e (optimized k) a b r (a ||| b) ||
    (checkMove e (optimized k) a b r (a &&& ~~~b) ||
    (checkMove e (optimized k) a b r (b &&& ~~~a) || false)))) = false
  rw [h0, h1, h2, h3] <;> rfl

theorem b_0_0_0 : branch 0 0 0 = false := by decide +kernel
theorem b_0_0_1 : branch 0 0 1 = false := by decide +kernel
theorem b_0_0_2 : branch 0 0 2 = false := by decide +kernel
def state_0_0_3 : List W := [216847934933731345, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_0_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_0_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_0_0_3_0 : next_0_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_1 : next_0_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_2 : next_0_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_3 : next_0_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_4 : next_0_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_5 : next_0_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_6 : next_0_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_7 : next_0_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_8 : next_0_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_9 : next_0_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_10 : next_0_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_11 : next_0_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_12 : next_0_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_13 : next_0_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_14 : next_0_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_15 : next_0_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_16 : next_0_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_17 : next_0_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_18 : next_0_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_19 : next_0_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_0_3_20 : next_0_0_3 20 = false := by decide +kernel
theorem state_ok_0_0_3 : optimized 6 0 state_0_0_3 = false := by
  change ((state_0_0_3 == [goal] || state_0_0_3 == [~~~goal]) || _) = false
  rw [show (state_0_0_3 == [goal] || state_0_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_0_0_3 0 || (next_0_0_3 1 || (next_0_0_3 2 || (next_0_0_3 3 || (next_0_0_3 4 || (next_0_0_3 5 || (next_0_0_3 6 || (next_0_0_3 7 || (next_0_0_3 8 || (next_0_0_3 9 || (next_0_0_3 10 || (next_0_0_3 11 || (next_0_0_3 12 || (next_0_0_3 13 || (next_0_0_3 14 || (next_0_0_3 15 || (next_0_0_3 16 || (next_0_0_3 17 || (next_0_0_3 18 || (next_0_0_3 19 || (next_0_0_3 20 || false))))))))))))))))))))) = false
  rw [d_0_0_3_0, d_0_0_3_1, d_0_0_3_2, d_0_0_3_3, d_0_0_3_4, d_0_0_3_5, d_0_0_3_6, d_0_0_3_7, d_0_0_3_8, d_0_0_3_9, d_0_0_3_10, d_0_0_3_11, d_0_0_3_12, d_0_0_3_13, d_0_0_3_14, d_0_0_3_15, d_0_0_3_16, d_0_0_3_17, d_0_0_3_18, d_0_0_3_19, d_0_0_3_20] <;> rfl
theorem b_0_0_3 : branch 0 0 3 = false := branch_lift 0 0 3 0 state_0_0_3 (by decide +kernel) state_ok_0_0_3
theorem c_0_0 : lane 0 0 = false := branch_join 0 0 b_0_0_0 b_0_0_1 b_0_0_2 b_0_0_3
theorem b_0_1_0 : branch 0 1 0 = false := by decide +kernel
theorem b_0_1_1 : branch 0 1 1 = false := by decide +kernel
theorem b_0_1_2 : branch 0 1 2 = false := by decide +kernel
def state_0_1_3 : List W := [1152921504295139959, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_0_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_0_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_0_1_3_0 : next_0_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_1 : next_0_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_2 : next_0_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_3 : next_0_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_4 : next_0_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_5 : next_0_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_6 : next_0_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_7 : next_0_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_8 : next_0_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_9 : next_0_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_10 : next_0_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_11 : next_0_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_12 : next_0_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_13 : next_0_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_14 : next_0_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_15 : next_0_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_16 : next_0_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_17 : next_0_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_18 : next_0_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_19 : next_0_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_1_3_20 : next_0_1_3 20 = false := by decide +kernel
theorem state_ok_0_1_3 : optimized 6 0 state_0_1_3 = false := by
  change ((state_0_1_3 == [goal] || state_0_1_3 == [~~~goal]) || _) = false
  rw [show (state_0_1_3 == [goal] || state_0_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_0_1_3 0 || (next_0_1_3 1 || (next_0_1_3 2 || (next_0_1_3 3 || (next_0_1_3 4 || (next_0_1_3 5 || (next_0_1_3 6 || (next_0_1_3 7 || (next_0_1_3 8 || (next_0_1_3 9 || (next_0_1_3 10 || (next_0_1_3 11 || (next_0_1_3 12 || (next_0_1_3 13 || (next_0_1_3 14 || (next_0_1_3 15 || (next_0_1_3 16 || (next_0_1_3 17 || (next_0_1_3 18 || (next_0_1_3 19 || (next_0_1_3 20 || false))))))))))))))))))))) = false
  rw [d_0_1_3_0, d_0_1_3_1, d_0_1_3_2, d_0_1_3_3, d_0_1_3_4, d_0_1_3_5, d_0_1_3_6, d_0_1_3_7, d_0_1_3_8, d_0_1_3_9, d_0_1_3_10, d_0_1_3_11, d_0_1_3_12, d_0_1_3_13, d_0_1_3_14, d_0_1_3_15, d_0_1_3_16, d_0_1_3_17, d_0_1_3_18, d_0_1_3_19, d_0_1_3_20] <;> rfl
theorem b_0_1_3 : branch 0 1 3 = false := branch_lift 0 1 3 0 state_0_1_3 (by decide +kernel) state_ok_0_1_3
theorem c_0_1 : lane 0 1 = false := branch_join 0 1 b_0_1_0 b_0_1_1 b_0_1_2 b_0_1_3
theorem b_0_2_0 : branch 0 2 0 = false := by decide +kernel
theorem b_0_2_1 : branch 0 2 1 = false := by decide +kernel
theorem b_0_2_2 : branch 0 2 2 = false := by decide +kernel
def state_0_2_3 : List W := [343849927773921888, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_0_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_0_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_0_2_3_0 : next_0_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_1 : next_0_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_2 : next_0_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_3 : next_0_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_4 : next_0_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_5 : next_0_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_6 : next_0_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_7 : next_0_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_8 : next_0_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_9 : next_0_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_10 : next_0_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_11 : next_0_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_12 : next_0_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_13 : next_0_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_14 : next_0_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_15 : next_0_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_16 : next_0_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_17 : next_0_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_18 : next_0_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_19 : next_0_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_2_3_20 : next_0_2_3 20 = false := by decide +kernel
theorem state_ok_0_2_3 : optimized 6 0 state_0_2_3 = false := by
  change ((state_0_2_3 == [goal] || state_0_2_3 == [~~~goal]) || _) = false
  rw [show (state_0_2_3 == [goal] || state_0_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_0_2_3 0 || (next_0_2_3 1 || (next_0_2_3 2 || (next_0_2_3 3 || (next_0_2_3 4 || (next_0_2_3 5 || (next_0_2_3 6 || (next_0_2_3 7 || (next_0_2_3 8 || (next_0_2_3 9 || (next_0_2_3 10 || (next_0_2_3 11 || (next_0_2_3 12 || (next_0_2_3 13 || (next_0_2_3 14 || (next_0_2_3 15 || (next_0_2_3 16 || (next_0_2_3 17 || (next_0_2_3 18 || (next_0_2_3 19 || (next_0_2_3 20 || false))))))))))))))))))))) = false
  rw [d_0_2_3_0, d_0_2_3_1, d_0_2_3_2, d_0_2_3_3, d_0_2_3_4, d_0_2_3_5, d_0_2_3_6, d_0_2_3_7, d_0_2_3_8, d_0_2_3_9, d_0_2_3_10, d_0_2_3_11, d_0_2_3_12, d_0_2_3_13, d_0_2_3_14, d_0_2_3_15, d_0_2_3_16, d_0_2_3_17, d_0_2_3_18, d_0_2_3_19, d_0_2_3_20] <;> rfl
theorem b_0_2_3 : branch 0 2 3 = false := branch_lift 0 2 3 0 state_0_2_3 (by decide +kernel) state_ok_0_2_3
theorem c_0_2 : lane 0 2 = false := branch_join 0 2 b_0_2_0 b_0_2_1 b_0_2_2 b_0_2_3
theorem b_0_3_0 : branch 0 3 0 = false := by decide +kernel
theorem b_0_3_1 : branch 0 3 1 = false := by decide +kernel
theorem b_0_3_2 : branch 0 3 2 = false := by decide +kernel
def state_0_3_3 : List W := [592223641587486726, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_0_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_0_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_0_3_3_0 : next_0_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_1 : next_0_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_2 : next_0_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_3 : next_0_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_4 : next_0_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_5 : next_0_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_6 : next_0_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_7 : next_0_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_8 : next_0_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_9 : next_0_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_10 : next_0_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_11 : next_0_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_12 : next_0_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_13 : next_0_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_14 : next_0_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_15 : next_0_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_16 : next_0_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_17 : next_0_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_18 : next_0_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_19 : next_0_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_0_3_3_20 : next_0_3_3 20 = false := by decide +kernel
theorem state_ok_0_3_3 : optimized 6 0 state_0_3_3 = false := by
  change ((state_0_3_3 == [goal] || state_0_3_3 == [~~~goal]) || _) = false
  rw [show (state_0_3_3 == [goal] || state_0_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_0_3_3 0 || (next_0_3_3 1 || (next_0_3_3 2 || (next_0_3_3 3 || (next_0_3_3 4 || (next_0_3_3 5 || (next_0_3_3 6 || (next_0_3_3 7 || (next_0_3_3 8 || (next_0_3_3 9 || (next_0_3_3 10 || (next_0_3_3 11 || (next_0_3_3 12 || (next_0_3_3 13 || (next_0_3_3 14 || (next_0_3_3 15 || (next_0_3_3 16 || (next_0_3_3 17 || (next_0_3_3 18 || (next_0_3_3 19 || (next_0_3_3 20 || false))))))))))))))))))))) = false
  rw [d_0_3_3_0, d_0_3_3_1, d_0_3_3_2, d_0_3_3_3, d_0_3_3_4, d_0_3_3_5, d_0_3_3_6, d_0_3_3_7, d_0_3_3_8, d_0_3_3_9, d_0_3_3_10, d_0_3_3_11, d_0_3_3_12, d_0_3_3_13, d_0_3_3_14, d_0_3_3_15, d_0_3_3_16, d_0_3_3_17, d_0_3_3_18, d_0_3_3_19, d_0_3_3_20] <;> rfl
theorem b_0_3_3 : branch 0 3 3 = false := branch_lift 0 3 3 0 state_0_3_3 (by decide +kernel) state_ok_0_3_3
theorem c_0_3 : lane 0 3 = false := branch_join 0 3 b_0_3_0 b_0_3_1 b_0_3_2 b_0_3_3
theorem checked_0 : firstGate 0 = false := lanes_join 0 c_0_0 c_0_1 c_0_2 c_0_3
theorem b_1_0_0 : branch 1 0 0 = false := by decide +kernel
theorem b_1_0_1 : branch 1 0 1 = false := by decide +kernel
theorem b_1_0_2 : branch 1 0 2 = false := by decide +kernel
def state_1_0_3 : List W := [289488424686100480, 560697862707653233, 881712051380150656, 809071576521218071, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_1_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_1_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_1_0_3_0 : next_1_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_1 : next_1_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_2 : next_1_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_3 : next_1_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_4 : next_1_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_5 : next_1_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_6 : next_1_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_7 : next_1_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_8 : next_1_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_9 : next_1_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_10 : next_1_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_11 : next_1_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_12 : next_1_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_13 : next_1_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_14 : next_1_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_15 : next_1_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_16 : next_1_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_17 : next_1_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_18 : next_1_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_19 : next_1_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_0_3_20 : next_1_0_3 20 = false := by decide +kernel
theorem state_ok_1_0_3 : optimized 6 0 state_1_0_3 = false := by
  change ((state_1_0_3 == [goal] || state_1_0_3 == [~~~goal]) || _) = false
  rw [show (state_1_0_3 == [goal] || state_1_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_1_0_3 0 || (next_1_0_3 1 || (next_1_0_3 2 || (next_1_0_3 3 || (next_1_0_3 4 || (next_1_0_3 5 || (next_1_0_3 6 || (next_1_0_3 7 || (next_1_0_3 8 || (next_1_0_3 9 || (next_1_0_3 10 || (next_1_0_3 11 || (next_1_0_3 12 || (next_1_0_3 13 || (next_1_0_3 14 || (next_1_0_3 15 || (next_1_0_3 16 || (next_1_0_3 17 || (next_1_0_3 18 || (next_1_0_3 19 || (next_1_0_3 20 || false))))))))))))))))))))) = false
  rw [d_1_0_3_0, d_1_0_3_1, d_1_0_3_2, d_1_0_3_3, d_1_0_3_4, d_1_0_3_5, d_1_0_3_6, d_1_0_3_7, d_1_0_3_8, d_1_0_3_9, d_1_0_3_10, d_1_0_3_11, d_1_0_3_12, d_1_0_3_13, d_1_0_3_14, d_1_0_3_15, d_1_0_3_16, d_1_0_3_17, d_1_0_3_18, d_1_0_3_19, d_1_0_3_20] <;> rfl
theorem b_1_0_3 : branch 1 0 3 = false := branch_lift 1 0 3 0 state_1_0_3 (by decide +kernel) state_ok_1_0_3
theorem c_1_0 : lane 1 0 = false := branch_join 1 0 b_1_0_0 b_1_0_1 b_1_0_2 b_1_0_3
theorem b_1_1_0 : branch 1 1 0 = false := by decide +kernel
theorem b_1_1_1 : branch 1 1 1 = false := by decide +kernel
theorem b_1_1_2 : branch 1 1 2 = false := by decide +kernel
def state_1_1_3 : List W := [1152921489401703409, 560697862707653233, 881712051380150656, 809071576521218071, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_1_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_1_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_1_1_3_0 : next_1_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_1 : next_1_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_2 : next_1_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_3 : next_1_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_4 : next_1_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_5 : next_1_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_6 : next_1_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_7 : next_1_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_8 : next_1_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_9 : next_1_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_10 : next_1_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_11 : next_1_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_12 : next_1_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_13 : next_1_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_14 : next_1_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_15 : next_1_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_16 : next_1_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_17 : next_1_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_18 : next_1_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_19 : next_1_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_1_3_20 : next_1_1_3 20 = false := by decide +kernel
theorem state_ok_1_1_3 : optimized 6 0 state_1_1_3 = false := by
  change ((state_1_1_3 == [goal] || state_1_1_3 == [~~~goal]) || _) = false
  rw [show (state_1_1_3 == [goal] || state_1_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_1_1_3 0 || (next_1_1_3 1 || (next_1_1_3 2 || (next_1_1_3 3 || (next_1_1_3 4 || (next_1_1_3 5 || (next_1_1_3 6 || (next_1_1_3 7 || (next_1_1_3 8 || (next_1_1_3 9 || (next_1_1_3 10 || (next_1_1_3 11 || (next_1_1_3 12 || (next_1_1_3 13 || (next_1_1_3 14 || (next_1_1_3 15 || (next_1_1_3 16 || (next_1_1_3 17 || (next_1_1_3 18 || (next_1_1_3 19 || (next_1_1_3 20 || false))))))))))))))))))))) = false
  rw [d_1_1_3_0, d_1_1_3_1, d_1_1_3_2, d_1_1_3_3, d_1_1_3_4, d_1_1_3_5, d_1_1_3_6, d_1_1_3_7, d_1_1_3_8, d_1_1_3_9, d_1_1_3_10, d_1_1_3_11, d_1_1_3_12, d_1_1_3_13, d_1_1_3_14, d_1_1_3_15, d_1_1_3_16, d_1_1_3_17, d_1_1_3_18, d_1_1_3_19, d_1_1_3_20] <;> rfl
theorem b_1_1_3 : branch 1 1 3 = false := branch_lift 1 1 3 0 state_1_1_3 (by decide +kernel) state_ok_1_1_3
theorem c_1_1 : lane 1 1 = false := branch_join 1 1 b_1_1_0 b_1_1_1 b_1_1_2 b_1_1_3
theorem b_1_2_0 : branch 1 2 0 = false := by decide +kernel
theorem b_1_2_1 : branch 1 2 1 = false := by decide +kernel
theorem b_1_2_2 : branch 1 2 2 = false := by decide +kernel
def state_1_2_3 : List W := [271209438021552753, 560697862707653233, 881712051380150656, 809071576521218071, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_1_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_1_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_1_2_3_0 : next_1_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_1 : next_1_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_2 : next_1_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_3 : next_1_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_4 : next_1_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_5 : next_1_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_6 : next_1_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_7 : next_1_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_8 : next_1_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_9 : next_1_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_10 : next_1_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_11 : next_1_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_12 : next_1_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_13 : next_1_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_14 : next_1_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_15 : next_1_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_16 : next_1_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_17 : next_1_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_18 : next_1_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_19 : next_1_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_2_3_20 : next_1_2_3 20 = false := by decide +kernel
theorem state_ok_1_2_3 : optimized 6 0 state_1_2_3 = false := by
  change ((state_1_2_3 == [goal] || state_1_2_3 == [~~~goal]) || _) = false
  rw [show (state_1_2_3 == [goal] || state_1_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_1_2_3 0 || (next_1_2_3 1 || (next_1_2_3 2 || (next_1_2_3 3 || (next_1_2_3 4 || (next_1_2_3 5 || (next_1_2_3 6 || (next_1_2_3 7 || (next_1_2_3 8 || (next_1_2_3 9 || (next_1_2_3 10 || (next_1_2_3 11 || (next_1_2_3 12 || (next_1_2_3 13 || (next_1_2_3 14 || (next_1_2_3 15 || (next_1_2_3 16 || (next_1_2_3 17 || (next_1_2_3 18 || (next_1_2_3 19 || (next_1_2_3 20 || false))))))))))))))))))))) = false
  rw [d_1_2_3_0, d_1_2_3_1, d_1_2_3_2, d_1_2_3_3, d_1_2_3_4, d_1_2_3_5, d_1_2_3_6, d_1_2_3_7, d_1_2_3_8, d_1_2_3_9, d_1_2_3_10, d_1_2_3_11, d_1_2_3_12, d_1_2_3_13, d_1_2_3_14, d_1_2_3_15, d_1_2_3_16, d_1_2_3_17, d_1_2_3_18, d_1_2_3_19, d_1_2_3_20] <;> rfl
theorem b_1_2_3 : branch 1 2 3 = false := branch_lift 1 2 3 0 state_1_2_3 (by decide +kernel) state_ok_1_2_3
theorem c_1_2 : lane 1 2 = false := branch_join 1 2 b_1_2_0 b_1_2_1 b_1_2_2 b_1_2_3
theorem b_1_3_0 : branch 1 3 0 = false := by decide +kernel
theorem b_1_3_1 : branch 1 3 1 = false := by decide +kernel
theorem b_1_3_2 : branch 1 3 2 = false := by decide +kernel
def state_1_3_3 : List W := [592223626694050176, 560697862707653233, 881712051380150656, 809071576521218071, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_1_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_1_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_1_3_3_0 : next_1_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_1 : next_1_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_2 : next_1_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_3 : next_1_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_4 : next_1_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_5 : next_1_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_6 : next_1_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_7 : next_1_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_8 : next_1_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_9 : next_1_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_10 : next_1_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_11 : next_1_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_12 : next_1_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_13 : next_1_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_14 : next_1_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_15 : next_1_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_16 : next_1_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_17 : next_1_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_18 : next_1_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_19 : next_1_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_1_3_3_20 : next_1_3_3 20 = false := by decide +kernel
theorem state_ok_1_3_3 : optimized 6 0 state_1_3_3 = false := by
  change ((state_1_3_3 == [goal] || state_1_3_3 == [~~~goal]) || _) = false
  rw [show (state_1_3_3 == [goal] || state_1_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_1_3_3 0 || (next_1_3_3 1 || (next_1_3_3 2 || (next_1_3_3 3 || (next_1_3_3 4 || (next_1_3_3 5 || (next_1_3_3 6 || (next_1_3_3 7 || (next_1_3_3 8 || (next_1_3_3 9 || (next_1_3_3 10 || (next_1_3_3 11 || (next_1_3_3 12 || (next_1_3_3 13 || (next_1_3_3 14 || (next_1_3_3 15 || (next_1_3_3 16 || (next_1_3_3 17 || (next_1_3_3 18 || (next_1_3_3 19 || (next_1_3_3 20 || false))))))))))))))))))))) = false
  rw [d_1_3_3_0, d_1_3_3_1, d_1_3_3_2, d_1_3_3_3, d_1_3_3_4, d_1_3_3_5, d_1_3_3_6, d_1_3_3_7, d_1_3_3_8, d_1_3_3_9, d_1_3_3_10, d_1_3_3_11, d_1_3_3_12, d_1_3_3_13, d_1_3_3_14, d_1_3_3_15, d_1_3_3_16, d_1_3_3_17, d_1_3_3_18, d_1_3_3_19, d_1_3_3_20] <;> rfl
theorem b_1_3_3 : branch 1 3 3 = false := branch_lift 1 3 3 0 state_1_3_3 (by decide +kernel) state_ok_1_3_3
theorem c_1_3 : lane 1 3 = false := branch_join 1 3 b_1_3_0 b_1_3_1 b_1_3_2 b_1_3_3
theorem checked_1 : firstGate 1 = false := lanes_join 1 c_1_0 c_1_1 c_1_2 c_1_3
theorem b_2_0_0 : branch 2 0 0 = false := by decide +kernel
theorem b_2_0_1 : branch 2 0 1 = false := by decide +kernel
theorem b_2_0_2 : branch 2 0 2 = false := by decide +kernel
def state_2_0_3 : List W := [2111320023498848, 560697862707653233, 17874208644006378, 809071576521218071, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_2_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_2_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_2_0_3_0 : next_2_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_1 : next_2_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_2 : next_2_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_3 : next_2_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_4 : next_2_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_5 : next_2_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_6 : next_2_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_7 : next_2_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_8 : next_2_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_9 : next_2_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_10 : next_2_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_11 : next_2_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_12 : next_2_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_13 : next_2_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_14 : next_2_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_15 : next_2_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_16 : next_2_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_17 : next_2_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_18 : next_2_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_19 : next_2_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_0_3_20 : next_2_0_3 20 = false := by decide +kernel
theorem state_ok_2_0_3 : optimized 6 0 state_2_0_3 = false := by
  change ((state_2_0_3 == [goal] || state_2_0_3 == [~~~goal]) || _) = false
  rw [show (state_2_0_3 == [goal] || state_2_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_2_0_3 0 || (next_2_0_3 1 || (next_2_0_3 2 || (next_2_0_3 3 || (next_2_0_3 4 || (next_2_0_3 5 || (next_2_0_3 6 || (next_2_0_3 7 || (next_2_0_3 8 || (next_2_0_3 9 || (next_2_0_3 10 || (next_2_0_3 11 || (next_2_0_3 12 || (next_2_0_3 13 || (next_2_0_3 14 || (next_2_0_3 15 || (next_2_0_3 16 || (next_2_0_3 17 || (next_2_0_3 18 || (next_2_0_3 19 || (next_2_0_3 20 || false))))))))))))))))))))) = false
  rw [d_2_0_3_0, d_2_0_3_1, d_2_0_3_2, d_2_0_3_3, d_2_0_3_4, d_2_0_3_5, d_2_0_3_6, d_2_0_3_7, d_2_0_3_8, d_2_0_3_9, d_2_0_3_10, d_2_0_3_11, d_2_0_3_12, d_2_0_3_13, d_2_0_3_14, d_2_0_3_15, d_2_0_3_16, d_2_0_3_17, d_2_0_3_18, d_2_0_3_19, d_2_0_3_20] <;> rfl
theorem b_2_0_3 : branch 2 0 3 = false := branch_lift 2 0 3 0 state_2_0_3 (by decide +kernel) state_ok_2_0_3
theorem c_2_0 : lane 2 0 = false := branch_join 2 0 b_2_0_0 b_2_0_1 b_2_0_2 b_2_0_3
theorem b_2_1_0 : branch 2 1 0 = false := by decide +kernel
theorem b_2_1_1 : branch 2 1 1 = false := by decide +kernel
theorem b_2_1_2 : branch 2 1 2 = false := by decide +kernel
def state_2_1_3 : List W := [576460751328160763, 560697862707653233, 17874208644006378, 809071576521218071, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_2_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_2_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_2_1_3_0 : next_2_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_1 : next_2_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_2 : next_2_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_3 : next_2_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_4 : next_2_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_5 : next_2_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_6 : next_2_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_7 : next_2_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_8 : next_2_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_9 : next_2_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_10 : next_2_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_11 : next_2_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_12 : next_2_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_13 : next_2_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_14 : next_2_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_15 : next_2_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_16 : next_2_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_17 : next_2_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_18 : next_2_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_19 : next_2_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_1_3_20 : next_2_1_3 20 = false := by decide +kernel
theorem state_ok_2_1_3 : optimized 6 0 state_2_1_3 = false := by
  change ((state_2_1_3 == [goal] || state_2_1_3 == [~~~goal]) || _) = false
  rw [show (state_2_1_3 == [goal] || state_2_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_2_1_3 0 || (next_2_1_3 1 || (next_2_1_3 2 || (next_2_1_3 3 || (next_2_1_3 4 || (next_2_1_3 5 || (next_2_1_3 6 || (next_2_1_3 7 || (next_2_1_3 8 || (next_2_1_3 9 || (next_2_1_3 10 || (next_2_1_3 11 || (next_2_1_3 12 || (next_2_1_3 13 || (next_2_1_3 14 || (next_2_1_3 15 || (next_2_1_3 16 || (next_2_1_3 17 || (next_2_1_3 18 || (next_2_1_3 19 || (next_2_1_3 20 || false))))))))))))))))))))) = false
  rw [d_2_1_3_0, d_2_1_3_1, d_2_1_3_2, d_2_1_3_3, d_2_1_3_4, d_2_1_3_5, d_2_1_3_6, d_2_1_3_7, d_2_1_3_8, d_2_1_3_9, d_2_1_3_10, d_2_1_3_11, d_2_1_3_12, d_2_1_3_13, d_2_1_3_14, d_2_1_3_15, d_2_1_3_16, d_2_1_3_17, d_2_1_3_18, d_2_1_3_19, d_2_1_3_20] <;> rfl
theorem b_2_1_3 : branch 2 1 3 = false := branch_lift 2 1 3 0 state_2_1_3 (by decide +kernel) state_ok_2_1_3
theorem c_2_1 : lane 2 1 = false := branch_join 2 1 b_2_1_0 b_2_1_1 b_2_1_2 b_2_1_3
theorem b_2_2_0 : branch 2 2 0 = false := by decide +kernel
theorem b_2_2_1 : branch 2 2 1 = false := by decide +kernel
theorem b_2_2_2 : branch 2 2 2 = false := by decide +kernel
def state_2_2_3 : List W := [558586542684154385, 560697862707653233, 17874208644006378, 809071576521218071, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_2_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_2_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_2_2_3_0 : next_2_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_1 : next_2_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_2 : next_2_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_3 : next_2_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_4 : next_2_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_5 : next_2_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_6 : next_2_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_7 : next_2_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_8 : next_2_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_9 : next_2_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_10 : next_2_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_11 : next_2_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_12 : next_2_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_13 : next_2_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_14 : next_2_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_15 : next_2_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_16 : next_2_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_17 : next_2_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_18 : next_2_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_19 : next_2_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_2_3_20 : next_2_2_3 20 = false := by decide +kernel
theorem state_ok_2_2_3 : optimized 6 0 state_2_2_3 = false := by
  change ((state_2_2_3 == [goal] || state_2_2_3 == [~~~goal]) || _) = false
  rw [show (state_2_2_3 == [goal] || state_2_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_2_2_3 0 || (next_2_2_3 1 || (next_2_2_3 2 || (next_2_2_3 3 || (next_2_2_3 4 || (next_2_2_3 5 || (next_2_2_3 6 || (next_2_2_3 7 || (next_2_2_3 8 || (next_2_2_3 9 || (next_2_2_3 10 || (next_2_2_3 11 || (next_2_2_3 12 || (next_2_2_3 13 || (next_2_2_3 14 || (next_2_2_3 15 || (next_2_2_3 16 || (next_2_2_3 17 || (next_2_2_3 18 || (next_2_2_3 19 || (next_2_2_3 20 || false))))))))))))))))))))) = false
  rw [d_2_2_3_0, d_2_2_3_1, d_2_2_3_2, d_2_2_3_3, d_2_2_3_4, d_2_2_3_5, d_2_2_3_6, d_2_2_3_7, d_2_2_3_8, d_2_2_3_9, d_2_2_3_10, d_2_2_3_11, d_2_2_3_12, d_2_2_3_13, d_2_2_3_14, d_2_2_3_15, d_2_2_3_16, d_2_2_3_17, d_2_2_3_18, d_2_2_3_19, d_2_2_3_20] <;> rfl
theorem b_2_2_3 : branch 2 2 3 = false := branch_lift 2 2 3 0 state_2_2_3 (by decide +kernel) state_ok_2_2_3
theorem c_2_2 : lane 2 2 = false := branch_join 2 2 b_2_2_0 b_2_2_1 b_2_2_2 b_2_2_3
theorem b_2_3_0 : branch 2 3 0 = false := by decide +kernel
theorem b_2_3_1 : branch 2 3 1 = false := by decide +kernel
theorem b_2_3_2 : branch 2 3 2 = false := by decide +kernel
def state_2_3_3 : List W := [15762888620507530, 560697862707653233, 17874208644006378, 809071576521218071, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_2_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_2_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_2_3_3_0 : next_2_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_1 : next_2_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_2 : next_2_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_3 : next_2_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_4 : next_2_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_5 : next_2_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_6 : next_2_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_7 : next_2_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_8 : next_2_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_9 : next_2_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_10 : next_2_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_11 : next_2_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_12 : next_2_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_13 : next_2_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_14 : next_2_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_15 : next_2_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_16 : next_2_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_17 : next_2_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_18 : next_2_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_19 : next_2_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_2_3_3_20 : next_2_3_3 20 = false := by decide +kernel
theorem state_ok_2_3_3 : optimized 6 0 state_2_3_3 = false := by
  change ((state_2_3_3 == [goal] || state_2_3_3 == [~~~goal]) || _) = false
  rw [show (state_2_3_3 == [goal] || state_2_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_2_3_3 0 || (next_2_3_3 1 || (next_2_3_3 2 || (next_2_3_3 3 || (next_2_3_3 4 || (next_2_3_3 5 || (next_2_3_3 6 || (next_2_3_3 7 || (next_2_3_3 8 || (next_2_3_3 9 || (next_2_3_3 10 || (next_2_3_3 11 || (next_2_3_3 12 || (next_2_3_3 13 || (next_2_3_3 14 || (next_2_3_3 15 || (next_2_3_3 16 || (next_2_3_3 17 || (next_2_3_3 18 || (next_2_3_3 19 || (next_2_3_3 20 || false))))))))))))))))))))) = false
  rw [d_2_3_3_0, d_2_3_3_1, d_2_3_3_2, d_2_3_3_3, d_2_3_3_4, d_2_3_3_5, d_2_3_3_6, d_2_3_3_7, d_2_3_3_8, d_2_3_3_9, d_2_3_3_10, d_2_3_3_11, d_2_3_3_12, d_2_3_3_13, d_2_3_3_14, d_2_3_3_15, d_2_3_3_16, d_2_3_3_17, d_2_3_3_18, d_2_3_3_19, d_2_3_3_20] <;> rfl
theorem b_2_3_3 : branch 2 3 3 = false := branch_lift 2 3 3 0 state_2_3_3 (by decide +kernel) state_ok_2_3_3
theorem c_2_3 : lane 2 3 = false := branch_join 2 3 b_2_3_0 b_2_3_1 b_2_3_2 b_2_3_3
theorem checked_2 : firstGate 2 = false := lanes_join 2 c_2_0 c_2_1 c_2_2 c_2_3
theorem b_3_0_0 : branch 3 0 0 = false := by decide +kernel
theorem b_3_0_1 : branch 3 0 1 = false := by decide +kernel
theorem b_3_0_2 : branch 3 0 2 = false := by decide +kernel
def state_3_0_3 : List W := [558446612649607281, 560697862707653233, 1134907655299531261, 809071576521218071, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_3_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_3_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_3_0_3_0 : next_3_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_1 : next_3_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_2 : next_3_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_3 : next_3_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_4 : next_3_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_5 : next_3_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_6 : next_3_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_7 : next_3_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_8 : next_3_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_9 : next_3_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_10 : next_3_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_11 : next_3_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_12 : next_3_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_13 : next_3_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_14 : next_3_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_15 : next_3_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_16 : next_3_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_17 : next_3_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_18 : next_3_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_19 : next_3_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_0_3_20 : next_3_0_3 20 = false := by decide +kernel
theorem state_ok_3_0_3 : optimized 6 0 state_3_0_3 = false := by
  change ((state_3_0_3 == [goal] || state_3_0_3 == [~~~goal]) || _) = false
  rw [show (state_3_0_3 == [goal] || state_3_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_3_0_3 0 || (next_3_0_3 1 || (next_3_0_3 2 || (next_3_0_3 3 || (next_3_0_3 4 || (next_3_0_3 5 || (next_3_0_3 6 || (next_3_0_3 7 || (next_3_0_3 8 || (next_3_0_3 9 || (next_3_0_3 10 || (next_3_0_3 11 || (next_3_0_3 12 || (next_3_0_3 13 || (next_3_0_3 14 || (next_3_0_3 15 || (next_3_0_3 16 || (next_3_0_3 17 || (next_3_0_3 18 || (next_3_0_3 19 || (next_3_0_3 20 || false))))))))))))))))))))) = false
  rw [d_3_0_3_0, d_3_0_3_1, d_3_0_3_2, d_3_0_3_3, d_3_0_3_4, d_3_0_3_5, d_3_0_3_6, d_3_0_3_7, d_3_0_3_8, d_3_0_3_9, d_3_0_3_10, d_3_0_3_11, d_3_0_3_12, d_3_0_3_13, d_3_0_3_14, d_3_0_3_15, d_3_0_3_16, d_3_0_3_17, d_3_0_3_18, d_3_0_3_19, d_3_0_3_20] <;> rfl
theorem b_3_0_3 : branch 3 0 3 = false := branch_lift 3 0 3 0 state_3_0_3 (by decide +kernel) state_ok_3_0_3
theorem c_3_0 : lane 3 0 = false := branch_join 3 0 b_3_0_0 b_3_0_1 b_3_0_2 b_3_0_3
theorem b_3_1_0 : branch 3 1 0 = false := by decide +kernel
def state_3_1_1 : List W := [1137158905357577213, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_3_1_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_3_1_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_3_1_1_0 : next_3_1_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_1 : next_3_1_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_2 : next_3_1_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_3 : next_3_1_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_4 : next_3_1_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_5 : next_3_1_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_6 : next_3_1_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_7 : next_3_1_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_8 : next_3_1_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_9 : next_3_1_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_10 : next_3_1_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_11 : next_3_1_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_12 : next_3_1_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_13 : next_3_1_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_1_14 : next_3_1_1 14 = false := by decide +kernel
theorem state_ok_3_1_1 : optimized 6 1 state_3_1_1 = false := by
  change ((state_3_1_1 == [goal] || state_3_1_1 == [~~~goal]) || _) = false
  rw [show (state_3_1_1 == [goal] || state_3_1_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_3_1_1 0 || (next_3_1_1 1 || (next_3_1_1 2 || (next_3_1_1 3 || (next_3_1_1 4 || (next_3_1_1 5 || (next_3_1_1 6 || (next_3_1_1 7 || (next_3_1_1 8 || (next_3_1_1 9 || (next_3_1_1 10 || (next_3_1_1 11 || (next_3_1_1 12 || (next_3_1_1 13 || (next_3_1_1 14 || false))))))))))))))) = false
  rw [d_3_1_1_0, d_3_1_1_1, d_3_1_1_2, d_3_1_1_3, d_3_1_1_4, d_3_1_1_5, d_3_1_1_6, d_3_1_1_7, d_3_1_1_8, d_3_1_1_9, d_3_1_1_10, d_3_1_1_11, d_3_1_1_12, d_3_1_1_13, d_3_1_1_14] <;> rfl
theorem b_3_1_1 : branch 3 1 1 = false := branch_lift 3 1 1 1 state_3_1_1 (by decide +kernel) state_ok_3_1_1
theorem b_3_1_2 : branch 3 1 2 = false := by decide +kernel
def state_3_1_3 : List W := [1137158905357577213, 560697862707653233, 1134907655299531261, 809071576521218071, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_3_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_3_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_3_1_3_0 : next_3_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_1 : next_3_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_2 : next_3_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_3 : next_3_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_4 : next_3_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_5 : next_3_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_6 : next_3_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_7 : next_3_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_8 : next_3_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_9 : next_3_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_10 : next_3_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_11 : next_3_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_12 : next_3_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_13 : next_3_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_14 : next_3_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_15 : next_3_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_16 : next_3_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_17 : next_3_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_18 : next_3_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_19 : next_3_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_1_3_20 : next_3_1_3 20 = false := by decide +kernel
theorem state_ok_3_1_3 : optimized 6 0 state_3_1_3 = false := by
  change ((state_3_1_3 == [goal] || state_3_1_3 == [~~~goal]) || _) = false
  rw [show (state_3_1_3 == [goal] || state_3_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_3_1_3 0 || (next_3_1_3 1 || (next_3_1_3 2 || (next_3_1_3 3 || (next_3_1_3 4 || (next_3_1_3 5 || (next_3_1_3 6 || (next_3_1_3 7 || (next_3_1_3 8 || (next_3_1_3 9 || (next_3_1_3 10 || (next_3_1_3 11 || (next_3_1_3 12 || (next_3_1_3 13 || (next_3_1_3 14 || (next_3_1_3 15 || (next_3_1_3 16 || (next_3_1_3 17 || (next_3_1_3 18 || (next_3_1_3 19 || (next_3_1_3 20 || false))))))))))))))))))))) = false
  rw [d_3_1_3_0, d_3_1_3_1, d_3_1_3_2, d_3_1_3_3, d_3_1_3_4, d_3_1_3_5, d_3_1_3_6, d_3_1_3_7, d_3_1_3_8, d_3_1_3_9, d_3_1_3_10, d_3_1_3_11, d_3_1_3_12, d_3_1_3_13, d_3_1_3_14, d_3_1_3_15, d_3_1_3_16, d_3_1_3_17, d_3_1_3_18, d_3_1_3_19, d_3_1_3_20] <;> rfl
theorem b_3_1_3 : branch 3 1 3 = false := branch_lift 3 1 3 0 state_3_1_3 (by decide +kernel) state_ok_3_1_3
theorem c_3_1 : lane 3 1 = false := branch_join 3 1 b_3_1_0 b_3_1_1 b_3_1_2 b_3_1_3
theorem b_3_2_0 : branch 3 2 0 = false := by decide +kernel
theorem b_3_2_1 : branch 3 2 1 = false := by decide +kernel
theorem b_3_2_2 : branch 3 2 2 = false := by decide +kernel
def state_3_2_3 : List W := [2251250058045952, 560697862707653233, 1134907655299531261, 809071576521218071, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_3_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_3_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_3_2_3_0 : next_3_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_1 : next_3_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_2 : next_3_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_3 : next_3_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_4 : next_3_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_5 : next_3_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_6 : next_3_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_7 : next_3_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_8 : next_3_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_9 : next_3_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_10 : next_3_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_11 : next_3_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_12 : next_3_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_13 : next_3_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_14 : next_3_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_15 : next_3_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_16 : next_3_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_17 : next_3_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_18 : next_3_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_19 : next_3_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_2_3_20 : next_3_2_3 20 = false := by decide +kernel
theorem state_ok_3_2_3 : optimized 6 0 state_3_2_3 = false := by
  change ((state_3_2_3 == [goal] || state_3_2_3 == [~~~goal]) || _) = false
  rw [show (state_3_2_3 == [goal] || state_3_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_3_2_3 0 || (next_3_2_3 1 || (next_3_2_3 2 || (next_3_2_3 3 || (next_3_2_3 4 || (next_3_2_3 5 || (next_3_2_3 6 || (next_3_2_3 7 || (next_3_2_3 8 || (next_3_2_3 9 || (next_3_2_3 10 || (next_3_2_3 11 || (next_3_2_3 12 || (next_3_2_3 13 || (next_3_2_3 14 || (next_3_2_3 15 || (next_3_2_3 16 || (next_3_2_3 17 || (next_3_2_3 18 || (next_3_2_3 19 || (next_3_2_3 20 || false))))))))))))))))))))) = false
  rw [d_3_2_3_0, d_3_2_3_1, d_3_2_3_2, d_3_2_3_3, d_3_2_3_4, d_3_2_3_5, d_3_2_3_6, d_3_2_3_7, d_3_2_3_8, d_3_2_3_9, d_3_2_3_10, d_3_2_3_11, d_3_2_3_12, d_3_2_3_13, d_3_2_3_14, d_3_2_3_15, d_3_2_3_16, d_3_2_3_17, d_3_2_3_18, d_3_2_3_19, d_3_2_3_20] <;> rfl
theorem b_3_2_3 : branch 3 2 3 = false := branch_lift 3 2 3 0 state_3_2_3 (by decide +kernel) state_ok_3_2_3
theorem c_3_2 : lane 3 2 = false := branch_join 3 2 b_3_2_0 b_3_2_1 b_3_2_2 b_3_2_3
theorem b_3_3_0 : branch 3 3 0 = false := by decide +kernel
def state_3_3_1 : List W := [576461042649923980, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_3_3_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_3_3_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_3_3_1_0 : next_3_3_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_1 : next_3_3_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_2 : next_3_3_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_3 : next_3_3_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_4 : next_3_3_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_5 : next_3_3_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_6 : next_3_3_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_7 : next_3_3_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_8 : next_3_3_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_9 : next_3_3_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_10 : next_3_3_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_11 : next_3_3_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_12 : next_3_3_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_13 : next_3_3_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_1_14 : next_3_3_1 14 = false := by decide +kernel
theorem state_ok_3_3_1 : optimized 6 1 state_3_3_1 = false := by
  change ((state_3_3_1 == [goal] || state_3_3_1 == [~~~goal]) || _) = false
  rw [show (state_3_3_1 == [goal] || state_3_3_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_3_3_1 0 || (next_3_3_1 1 || (next_3_3_1 2 || (next_3_3_1 3 || (next_3_3_1 4 || (next_3_3_1 5 || (next_3_3_1 6 || (next_3_3_1 7 || (next_3_3_1 8 || (next_3_3_1 9 || (next_3_3_1 10 || (next_3_3_1 11 || (next_3_3_1 12 || (next_3_3_1 13 || (next_3_3_1 14 || false))))))))))))))) = false
  rw [d_3_3_1_0, d_3_3_1_1, d_3_3_1_2, d_3_3_1_3, d_3_3_1_4, d_3_3_1_5, d_3_3_1_6, d_3_3_1_7, d_3_3_1_8, d_3_3_1_9, d_3_3_1_10, d_3_3_1_11, d_3_3_1_12, d_3_3_1_13, d_3_3_1_14] <;> rfl
theorem b_3_3_1 : branch 3 3 1 = false := branch_lift 3 3 1 1 state_3_3_1 (by decide +kernel) state_ok_3_3_1
theorem b_3_3_2 : branch 3 3 2 = false := by decide +kernel
def state_3_3_3 : List W := [576461042649923980, 560697862707653233, 1134907655299531261, 809071576521218071, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_3_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_3_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_3_3_3_0 : next_3_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_1 : next_3_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_2 : next_3_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_3 : next_3_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_4 : next_3_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_5 : next_3_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_6 : next_3_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_7 : next_3_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_8 : next_3_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_9 : next_3_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_10 : next_3_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_11 : next_3_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_12 : next_3_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_13 : next_3_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_14 : next_3_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_15 : next_3_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_16 : next_3_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_17 : next_3_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_18 : next_3_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_19 : next_3_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_3_3_3_20 : next_3_3_3 20 = false := by decide +kernel
theorem state_ok_3_3_3 : optimized 6 0 state_3_3_3 = false := by
  change ((state_3_3_3 == [goal] || state_3_3_3 == [~~~goal]) || _) = false
  rw [show (state_3_3_3 == [goal] || state_3_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_3_3_3 0 || (next_3_3_3 1 || (next_3_3_3 2 || (next_3_3_3 3 || (next_3_3_3 4 || (next_3_3_3 5 || (next_3_3_3 6 || (next_3_3_3 7 || (next_3_3_3 8 || (next_3_3_3 9 || (next_3_3_3 10 || (next_3_3_3 11 || (next_3_3_3 12 || (next_3_3_3 13 || (next_3_3_3 14 || (next_3_3_3 15 || (next_3_3_3 16 || (next_3_3_3 17 || (next_3_3_3 18 || (next_3_3_3 19 || (next_3_3_3 20 || false))))))))))))))))))))) = false
  rw [d_3_3_3_0, d_3_3_3_1, d_3_3_3_2, d_3_3_3_3, d_3_3_3_4, d_3_3_3_5, d_3_3_3_6, d_3_3_3_7, d_3_3_3_8, d_3_3_3_9, d_3_3_3_10, d_3_3_3_11, d_3_3_3_12, d_3_3_3_13, d_3_3_3_14, d_3_3_3_15, d_3_3_3_16, d_3_3_3_17, d_3_3_3_18, d_3_3_3_19, d_3_3_3_20] <;> rfl
theorem b_3_3_3 : branch 3 3 3 = false := branch_lift 3 3 3 0 state_3_3_3 (by decide +kernel) state_ok_3_3_3
theorem c_3_3 : lane 3 3 = false := branch_join 3 3 b_3_3_0 b_3_3_1 b_3_3_2 b_3_3_3
theorem checked_3 : firstGate 3 = false := lanes_join 3 c_3_0 c_3_1 c_3_2 c_3_3
theorem b_4_0_0 : branch 4 0 0 = false := by decide +kernel
def state_4_0_1 : List W := [560697603851812864, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_4_0_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_4_0_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_4_0_1_0 : next_4_0_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_1 : next_4_0_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_2 : next_4_0_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_3 : next_4_0_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_4 : next_4_0_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_5 : next_4_0_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_6 : next_4_0_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_7 : next_4_0_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_8 : next_4_0_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_9 : next_4_0_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_10 : next_4_0_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_11 : next_4_0_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_12 : next_4_0_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_13 : next_4_0_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_1_14 : next_4_0_1 14 = false := by decide +kernel
theorem state_ok_4_0_1 : optimized 6 1 state_4_0_1 = false := by
  change ((state_4_0_1 == [goal] || state_4_0_1 == [~~~goal]) || _) = false
  rw [show (state_4_0_1 == [goal] || state_4_0_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_4_0_1 0 || (next_4_0_1 1 || (next_4_0_1 2 || (next_4_0_1 3 || (next_4_0_1 4 || (next_4_0_1 5 || (next_4_0_1 6 || (next_4_0_1 7 || (next_4_0_1 8 || (next_4_0_1 9 || (next_4_0_1 10 || (next_4_0_1 11 || (next_4_0_1 12 || (next_4_0_1 13 || (next_4_0_1 14 || false))))))))))))))) = false
  rw [d_4_0_1_0, d_4_0_1_1, d_4_0_1_2, d_4_0_1_3, d_4_0_1_4, d_4_0_1_5, d_4_0_1_6, d_4_0_1_7, d_4_0_1_8, d_4_0_1_9, d_4_0_1_10, d_4_0_1_11, d_4_0_1_12, d_4_0_1_13, d_4_0_1_14] <;> rfl
theorem b_4_0_1 : branch 4 0 1 = false := branch_lift 4 0 1 1 state_4_0_1 (by decide +kernel) state_ok_4_0_1
theorem b_4_0_2 : branch 4 0 2 = false := by decide +kernel
def state_4_0_3 : List W := [560697603851812864, 560697862707653233, 1152920955840713728, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_4_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_4_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_4_0_3_0 : next_4_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_1 : next_4_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_2 : next_4_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_3 : next_4_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_4 : next_4_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_5 : next_4_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_6 : next_4_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_7 : next_4_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_8 : next_4_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_9 : next_4_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_10 : next_4_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_11 : next_4_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_12 : next_4_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_13 : next_4_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_14 : next_4_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_15 : next_4_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_16 : next_4_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_17 : next_4_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_18 : next_4_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_19 : next_4_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_0_3_20 : next_4_0_3 20 = false := by decide +kernel
theorem state_ok_4_0_3 : optimized 6 0 state_4_0_3 = false := by
  change ((state_4_0_3 == [goal] || state_4_0_3 == [~~~goal]) || _) = false
  rw [show (state_4_0_3 == [goal] || state_4_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_4_0_3 0 || (next_4_0_3 1 || (next_4_0_3 2 || (next_4_0_3 3 || (next_4_0_3 4 || (next_4_0_3 5 || (next_4_0_3 6 || (next_4_0_3 7 || (next_4_0_3 8 || (next_4_0_3 9 || (next_4_0_3 10 || (next_4_0_3 11 || (next_4_0_3 12 || (next_4_0_3 13 || (next_4_0_3 14 || (next_4_0_3 15 || (next_4_0_3 16 || (next_4_0_3 17 || (next_4_0_3 18 || (next_4_0_3 19 || (next_4_0_3 20 || false))))))))))))))))))))) = false
  rw [d_4_0_3_0, d_4_0_3_1, d_4_0_3_2, d_4_0_3_3, d_4_0_3_4, d_4_0_3_5, d_4_0_3_6, d_4_0_3_7, d_4_0_3_8, d_4_0_3_9, d_4_0_3_10, d_4_0_3_11, d_4_0_3_12, d_4_0_3_13, d_4_0_3_14, d_4_0_3_15, d_4_0_3_16, d_4_0_3_17, d_4_0_3_18, d_4_0_3_19, d_4_0_3_20] <;> rfl
theorem b_4_0_3 : branch 4 0 3 = false := branch_lift 4 0 3 0 state_4_0_3 (by decide +kernel) state_ok_4_0_3
theorem c_4_0 : lane 4 0 = false := branch_join 4 0 b_4_0_0 b_4_0_1 b_4_0_2 b_4_0_3
theorem b_4_1_0 : branch 4 1 0 = false := by decide +kernel
theorem b_4_1_1 : branch 4 1 1 = false := by decide +kernel
theorem b_4_1_2 : branch 4 1 2 = false := by decide +kernel
def state_4_1_3 : List W := [1152921214696554097, 560697862707653233, 1152920955840713728, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_4_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_4_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_4_1_3_0 : next_4_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_1 : next_4_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_2 : next_4_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_3 : next_4_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_4 : next_4_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_5 : next_4_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_6 : next_4_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_7 : next_4_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_8 : next_4_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_9 : next_4_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_10 : next_4_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_11 : next_4_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_12 : next_4_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_13 : next_4_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_14 : next_4_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_15 : next_4_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_16 : next_4_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_17 : next_4_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_18 : next_4_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_19 : next_4_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_1_3_20 : next_4_1_3 20 = false := by decide +kernel
theorem state_ok_4_1_3 : optimized 6 0 state_4_1_3 = false := by
  change ((state_4_1_3 == [goal] || state_4_1_3 == [~~~goal]) || _) = false
  rw [show (state_4_1_3 == [goal] || state_4_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_4_1_3 0 || (next_4_1_3 1 || (next_4_1_3 2 || (next_4_1_3 3 || (next_4_1_3 4 || (next_4_1_3 5 || (next_4_1_3 6 || (next_4_1_3 7 || (next_4_1_3 8 || (next_4_1_3 9 || (next_4_1_3 10 || (next_4_1_3 11 || (next_4_1_3 12 || (next_4_1_3 13 || (next_4_1_3 14 || (next_4_1_3 15 || (next_4_1_3 16 || (next_4_1_3 17 || (next_4_1_3 18 || (next_4_1_3 19 || (next_4_1_3 20 || false))))))))))))))))))))) = false
  rw [d_4_1_3_0, d_4_1_3_1, d_4_1_3_2, d_4_1_3_3, d_4_1_3_4, d_4_1_3_5, d_4_1_3_6, d_4_1_3_7, d_4_1_3_8, d_4_1_3_9, d_4_1_3_10, d_4_1_3_11, d_4_1_3_12, d_4_1_3_13, d_4_1_3_14, d_4_1_3_15, d_4_1_3_16, d_4_1_3_17, d_4_1_3_18, d_4_1_3_19, d_4_1_3_20] <;> rfl
theorem b_4_1_3 : branch 4 1 3 = false := branch_lift 4 1 3 0 state_4_1_3 (by decide +kernel) state_ok_4_1_3
theorem c_4_1 : lane 4 1 = false := branch_join 4 1 b_4_1_0 b_4_1_1 b_4_1_2 b_4_1_3
theorem b_4_2_0 : branch 4 2 0 = false := by decide +kernel
def state_4_2_1 : List W := [258855840369, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_4_2_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_4_2_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_4_2_1_0 : next_4_2_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_1 : next_4_2_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_2 : next_4_2_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_3 : next_4_2_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_4 : next_4_2_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_5 : next_4_2_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_6 : next_4_2_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_7 : next_4_2_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_8 : next_4_2_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_9 : next_4_2_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_10 : next_4_2_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_11 : next_4_2_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_12 : next_4_2_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_13 : next_4_2_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_1_14 : next_4_2_1 14 = false := by decide +kernel
theorem state_ok_4_2_1 : optimized 6 1 state_4_2_1 = false := by
  change ((state_4_2_1 == [goal] || state_4_2_1 == [~~~goal]) || _) = false
  rw [show (state_4_2_1 == [goal] || state_4_2_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_4_2_1 0 || (next_4_2_1 1 || (next_4_2_1 2 || (next_4_2_1 3 || (next_4_2_1 4 || (next_4_2_1 5 || (next_4_2_1 6 || (next_4_2_1 7 || (next_4_2_1 8 || (next_4_2_1 9 || (next_4_2_1 10 || (next_4_2_1 11 || (next_4_2_1 12 || (next_4_2_1 13 || (next_4_2_1 14 || false))))))))))))))) = false
  rw [d_4_2_1_0, d_4_2_1_1, d_4_2_1_2, d_4_2_1_3, d_4_2_1_4, d_4_2_1_5, d_4_2_1_6, d_4_2_1_7, d_4_2_1_8, d_4_2_1_9, d_4_2_1_10, d_4_2_1_11, d_4_2_1_12, d_4_2_1_13, d_4_2_1_14] <;> rfl
theorem b_4_2_1 : branch 4 2 1 = false := branch_lift 4 2 1 1 state_4_2_1 (by decide +kernel) state_ok_4_2_1
theorem b_4_2_2 : branch 4 2 2 = false := by decide +kernel
def state_4_2_3 : List W := [258855840369, 560697862707653233, 1152920955840713728, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_4_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_4_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_4_2_3_0 : next_4_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_1 : next_4_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_2 : next_4_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_3 : next_4_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_4 : next_4_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_5 : next_4_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_6 : next_4_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_7 : next_4_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_8 : next_4_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_9 : next_4_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_10 : next_4_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_11 : next_4_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_12 : next_4_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_13 : next_4_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_14 : next_4_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_15 : next_4_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_16 : next_4_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_17 : next_4_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_18 : next_4_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_19 : next_4_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_2_3_20 : next_4_2_3 20 = false := by decide +kernel
theorem state_ok_4_2_3 : optimized 6 0 state_4_2_3 = false := by
  change ((state_4_2_3 == [goal] || state_4_2_3 == [~~~goal]) || _) = false
  rw [show (state_4_2_3 == [goal] || state_4_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_4_2_3 0 || (next_4_2_3 1 || (next_4_2_3 2 || (next_4_2_3 3 || (next_4_2_3 4 || (next_4_2_3 5 || (next_4_2_3 6 || (next_4_2_3 7 || (next_4_2_3 8 || (next_4_2_3 9 || (next_4_2_3 10 || (next_4_2_3 11 || (next_4_2_3 12 || (next_4_2_3 13 || (next_4_2_3 14 || (next_4_2_3 15 || (next_4_2_3 16 || (next_4_2_3 17 || (next_4_2_3 18 || (next_4_2_3 19 || (next_4_2_3 20 || false))))))))))))))))))))) = false
  rw [d_4_2_3_0, d_4_2_3_1, d_4_2_3_2, d_4_2_3_3, d_4_2_3_4, d_4_2_3_5, d_4_2_3_6, d_4_2_3_7, d_4_2_3_8, d_4_2_3_9, d_4_2_3_10, d_4_2_3_11, d_4_2_3_12, d_4_2_3_13, d_4_2_3_14, d_4_2_3_15, d_4_2_3_16, d_4_2_3_17, d_4_2_3_18, d_4_2_3_19, d_4_2_3_20] <;> rfl
theorem b_4_2_3 : branch 4 2 3 = false := branch_lift 4 2 3 0 state_4_2_3 (by decide +kernel) state_ok_4_2_3
theorem c_4_2 : lane 4 2 = false := branch_join 4 2 b_4_2_0 b_4_2_1 b_4_2_2 b_4_2_3
theorem b_4_3_0 : branch 4 3 0 = false := by decide +kernel
theorem b_4_3_1 : branch 4 3 1 = false := by decide +kernel
theorem b_4_3_2 : branch 4 3 2 = false := by decide +kernel
def state_4_3_3 : List W := [592223351988900864, 560697862707653233, 1152920955840713728, 809071576521218071, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_4_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_4_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_4_3_3_0 : next_4_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_1 : next_4_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_2 : next_4_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_3 : next_4_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_4 : next_4_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_5 : next_4_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_6 : next_4_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_7 : next_4_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_8 : next_4_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_9 : next_4_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_10 : next_4_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_11 : next_4_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_12 : next_4_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_13 : next_4_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_14 : next_4_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_15 : next_4_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_16 : next_4_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_17 : next_4_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_18 : next_4_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_19 : next_4_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_4_3_3_20 : next_4_3_3 20 = false := by decide +kernel
theorem state_ok_4_3_3 : optimized 6 0 state_4_3_3 = false := by
  change ((state_4_3_3 == [goal] || state_4_3_3 == [~~~goal]) || _) = false
  rw [show (state_4_3_3 == [goal] || state_4_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_4_3_3 0 || (next_4_3_3 1 || (next_4_3_3 2 || (next_4_3_3 3 || (next_4_3_3 4 || (next_4_3_3 5 || (next_4_3_3 6 || (next_4_3_3 7 || (next_4_3_3 8 || (next_4_3_3 9 || (next_4_3_3 10 || (next_4_3_3 11 || (next_4_3_3 12 || (next_4_3_3 13 || (next_4_3_3 14 || (next_4_3_3 15 || (next_4_3_3 16 || (next_4_3_3 17 || (next_4_3_3 18 || (next_4_3_3 19 || (next_4_3_3 20 || false))))))))))))))))))))) = false
  rw [d_4_3_3_0, d_4_3_3_1, d_4_3_3_2, d_4_3_3_3, d_4_3_3_4, d_4_3_3_5, d_4_3_3_6, d_4_3_3_7, d_4_3_3_8, d_4_3_3_9, d_4_3_3_10, d_4_3_3_11, d_4_3_3_12, d_4_3_3_13, d_4_3_3_14, d_4_3_3_15, d_4_3_3_16, d_4_3_3_17, d_4_3_3_18, d_4_3_3_19, d_4_3_3_20] <;> rfl
theorem b_4_3_3 : branch 4 3 3 = false := branch_lift 4 3 3 0 state_4_3_3 (by decide +kernel) state_ok_4_3_3
theorem c_4_3 : lane 4 3 = false := branch_join 4 3 b_4_3_0 b_4_3_1 b_4_3_2 b_4_3_3
theorem checked_4 : firstGate 4 = false := lanes_join 4 c_4_0 c_4_1 c_4_2 c_4_3
theorem b_5_0_0 : branch 5 0 0 = false := by decide +kernel
theorem b_5_0_1 : branch 5 0 1 = false := by decide +kernel
theorem b_5_0_2 : branch 5 0 2 = false := by decide +kernel
def state_5_0_3 : List W := [592329180606201856, 809071576521218071, 881712051380150656, 560697862707653233, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_5_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_5_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_5_0_3_0 : next_5_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_1 : next_5_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_2 : next_5_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_3 : next_5_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_4 : next_5_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_5 : next_5_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_6 : next_5_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_7 : next_5_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_8 : next_5_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_9 : next_5_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_10 : next_5_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_11 : next_5_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_12 : next_5_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_13 : next_5_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_14 : next_5_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_15 : next_5_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_16 : next_5_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_17 : next_5_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_18 : next_5_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_19 : next_5_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_0_3_20 : next_5_0_3 20 = false := by decide +kernel
theorem state_ok_5_0_3 : optimized 6 0 state_5_0_3 = false := by
  change ((state_5_0_3 == [goal] || state_5_0_3 == [~~~goal]) || _) = false
  rw [show (state_5_0_3 == [goal] || state_5_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_5_0_3 0 || (next_5_0_3 1 || (next_5_0_3 2 || (next_5_0_3 3 || (next_5_0_3 4 || (next_5_0_3 5 || (next_5_0_3 6 || (next_5_0_3 7 || (next_5_0_3 8 || (next_5_0_3 9 || (next_5_0_3 10 || (next_5_0_3 11 || (next_5_0_3 12 || (next_5_0_3 13 || (next_5_0_3 14 || (next_5_0_3 15 || (next_5_0_3 16 || (next_5_0_3 17 || (next_5_0_3 18 || (next_5_0_3 19 || (next_5_0_3 20 || false))))))))))))))))))))) = false
  rw [d_5_0_3_0, d_5_0_3_1, d_5_0_3_2, d_5_0_3_3, d_5_0_3_4, d_5_0_3_5, d_5_0_3_6, d_5_0_3_7, d_5_0_3_8, d_5_0_3_9, d_5_0_3_10, d_5_0_3_11, d_5_0_3_12, d_5_0_3_13, d_5_0_3_14, d_5_0_3_15, d_5_0_3_16, d_5_0_3_17, d_5_0_3_18, d_5_0_3_19, d_5_0_3_20] <;> rfl
theorem b_5_0_3 : branch 5 0 3 = false := branch_lift 5 0 3 0 state_5_0_3 (by decide +kernel) state_ok_5_0_3
theorem c_5_0 : lane 5 0 = false := branch_join 5 0 b_5_0_0 b_5_0_1 b_5_0_2 b_5_0_3
theorem b_5_1_0 : branch 5 1 0 = false := by decide +kernel
theorem b_5_1_1 : branch 5 1 1 = false := by decide +kernel
theorem b_5_1_2 : branch 5 1 2 = false := by decide +kernel
def state_5_1_3 : List W := [1098454447295166871, 809071576521218071, 881712051380150656, 560697862707653233, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_5_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_5_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_5_1_3_0 : next_5_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_1 : next_5_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_2 : next_5_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_3 : next_5_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_4 : next_5_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_5 : next_5_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_6 : next_5_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_7 : next_5_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_8 : next_5_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_9 : next_5_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_10 : next_5_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_11 : next_5_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_12 : next_5_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_13 : next_5_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_14 : next_5_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_15 : next_5_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_16 : next_5_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_17 : next_5_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_18 : next_5_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_19 : next_5_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_1_3_20 : next_5_1_3 20 = false := by decide +kernel
theorem state_ok_5_1_3 : optimized 6 0 state_5_1_3 = false := by
  change ((state_5_1_3 == [goal] || state_5_1_3 == [~~~goal]) || _) = false
  rw [show (state_5_1_3 == [goal] || state_5_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_5_1_3 0 || (next_5_1_3 1 || (next_5_1_3 2 || (next_5_1_3 3 || (next_5_1_3 4 || (next_5_1_3 5 || (next_5_1_3 6 || (next_5_1_3 7 || (next_5_1_3 8 || (next_5_1_3 9 || (next_5_1_3 10 || (next_5_1_3 11 || (next_5_1_3 12 || (next_5_1_3 13 || (next_5_1_3 14 || (next_5_1_3 15 || (next_5_1_3 16 || (next_5_1_3 17 || (next_5_1_3 18 || (next_5_1_3 19 || (next_5_1_3 20 || false))))))))))))))))))))) = false
  rw [d_5_1_3_0, d_5_1_3_1, d_5_1_3_2, d_5_1_3_3, d_5_1_3_4, d_5_1_3_5, d_5_1_3_6, d_5_1_3_7, d_5_1_3_8, d_5_1_3_9, d_5_1_3_10, d_5_1_3_11, d_5_1_3_12, d_5_1_3_13, d_5_1_3_14, d_5_1_3_15, d_5_1_3_16, d_5_1_3_17, d_5_1_3_18, d_5_1_3_19, d_5_1_3_20] <;> rfl
theorem b_5_1_3 : branch 5 1 3 = false := branch_lift 5 1 3 0 state_5_1_3 (by decide +kernel) state_ok_5_1_3
theorem c_5_1 : lane 5 1 = false := branch_join 5 1 b_5_1_0 b_5_1_1 b_5_1_2 b_5_1_3
theorem b_5_2_0 : branch 5 2 0 = false := by decide +kernel
theorem b_5_2_1 : branch 5 2 1 = false := by decide +kernel
theorem b_5_2_2 : branch 5 2 2 = false := by decide +kernel
def state_5_2_3 : List W := [216742395915016215, 809071576521218071, 881712051380150656, 560697862707653233, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_5_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_5_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_5_2_3_0 : next_5_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_1 : next_5_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_2 : next_5_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_3 : next_5_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_4 : next_5_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_5 : next_5_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_6 : next_5_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_7 : next_5_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_8 : next_5_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_9 : next_5_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_10 : next_5_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_11 : next_5_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_12 : next_5_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_13 : next_5_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_14 : next_5_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_15 : next_5_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_16 : next_5_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_17 : next_5_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_18 : next_5_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_19 : next_5_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_2_3_20 : next_5_2_3 20 = false := by decide +kernel
theorem state_ok_5_2_3 : optimized 6 0 state_5_2_3 = false := by
  change ((state_5_2_3 == [goal] || state_5_2_3 == [~~~goal]) || _) = false
  rw [show (state_5_2_3 == [goal] || state_5_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_5_2_3 0 || (next_5_2_3 1 || (next_5_2_3 2 || (next_5_2_3 3 || (next_5_2_3 4 || (next_5_2_3 5 || (next_5_2_3 6 || (next_5_2_3 7 || (next_5_2_3 8 || (next_5_2_3 9 || (next_5_2_3 10 || (next_5_2_3 11 || (next_5_2_3 12 || (next_5_2_3 13 || (next_5_2_3 14 || (next_5_2_3 15 || (next_5_2_3 16 || (next_5_2_3 17 || (next_5_2_3 18 || (next_5_2_3 19 || (next_5_2_3 20 || false))))))))))))))))))))) = false
  rw [d_5_2_3_0, d_5_2_3_1, d_5_2_3_2, d_5_2_3_3, d_5_2_3_4, d_5_2_3_5, d_5_2_3_6, d_5_2_3_7, d_5_2_3_8, d_5_2_3_9, d_5_2_3_10, d_5_2_3_11, d_5_2_3_12, d_5_2_3_13, d_5_2_3_14, d_5_2_3_15, d_5_2_3_16, d_5_2_3_17, d_5_2_3_18, d_5_2_3_19, d_5_2_3_20] <;> rfl
theorem b_5_2_3 : branch 5 2 3 = false := branch_lift 5 2 3 0 state_5_2_3 (by decide +kernel) state_ok_5_2_3
theorem c_5_2 : lane 5 2 = false := branch_join 5 2 b_5_2_0 b_5_2_1 b_5_2_2 b_5_2_3
theorem b_5_3_0 : branch 5 3 0 = false := by decide +kernel
theorem b_5_3_1 : branch 5 3 1 = false := by decide +kernel
theorem b_5_3_2 : branch 5 3 2 = false := by decide +kernel
def state_5_3_3 : List W := [289382870773948800, 809071576521218071, 881712051380150656, 560697862707653233, 17874208644006378, 1134907655299531261, 1152920955840713728]
def next_5_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_5_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_5_3_3_0 : next_5_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_1 : next_5_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_2 : next_5_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_3 : next_5_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_4 : next_5_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_5 : next_5_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_6 : next_5_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_7 : next_5_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_8 : next_5_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_9 : next_5_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_10 : next_5_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_11 : next_5_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_12 : next_5_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_13 : next_5_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_14 : next_5_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_15 : next_5_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_16 : next_5_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_17 : next_5_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_18 : next_5_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_19 : next_5_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_5_3_3_20 : next_5_3_3 20 = false := by decide +kernel
theorem state_ok_5_3_3 : optimized 6 0 state_5_3_3 = false := by
  change ((state_5_3_3 == [goal] || state_5_3_3 == [~~~goal]) || _) = false
  rw [show (state_5_3_3 == [goal] || state_5_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_5_3_3 0 || (next_5_3_3 1 || (next_5_3_3 2 || (next_5_3_3 3 || (next_5_3_3 4 || (next_5_3_3 5 || (next_5_3_3 6 || (next_5_3_3 7 || (next_5_3_3 8 || (next_5_3_3 9 || (next_5_3_3 10 || (next_5_3_3 11 || (next_5_3_3 12 || (next_5_3_3 13 || (next_5_3_3 14 || (next_5_3_3 15 || (next_5_3_3 16 || (next_5_3_3 17 || (next_5_3_3 18 || (next_5_3_3 19 || (next_5_3_3 20 || false))))))))))))))))))))) = false
  rw [d_5_3_3_0, d_5_3_3_1, d_5_3_3_2, d_5_3_3_3, d_5_3_3_4, d_5_3_3_5, d_5_3_3_6, d_5_3_3_7, d_5_3_3_8, d_5_3_3_9, d_5_3_3_10, d_5_3_3_11, d_5_3_3_12, d_5_3_3_13, d_5_3_3_14, d_5_3_3_15, d_5_3_3_16, d_5_3_3_17, d_5_3_3_18, d_5_3_3_19, d_5_3_3_20] <;> rfl
theorem b_5_3_3 : branch 5 3 3 = false := branch_lift 5 3 3 0 state_5_3_3 (by decide +kernel) state_ok_5_3_3
theorem c_5_3 : lane 5 3 = false := branch_join 5 3 b_5_3_0 b_5_3_1 b_5_3_2 b_5_3_3
theorem checked_5 : firstGate 5 = false := lanes_join 5 c_5_0 c_5_1 c_5_2 c_5_3
def state_6_0_0 : List W := [16325890103836674, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_0_0 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_0_0).getD idx (0, 0, [])
  dispatch 2 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_0_0_0 : next_6_0_0 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_1 : next_6_0_0 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_2 : next_6_0_0 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_3 : next_6_0_0 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_4 : next_6_0_0 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_5 : next_6_0_0 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_6 : next_6_0_0 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_7 : next_6_0_0 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_8 : next_6_0_0 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_0_9 : next_6_0_0 9 = false := by decide +kernel
theorem state_ok_6_0_0 : optimized 6 2 state_6_0_0 = false := by
  change ((state_6_0_0 == [goal] || state_6_0_0 == [~~~goal]) || _) = false
  rw [show (state_6_0_0 == [goal] || state_6_0_0 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_0_0 0 || (next_6_0_0 1 || (next_6_0_0 2 || (next_6_0_0 3 || (next_6_0_0 4 || (next_6_0_0 5 || (next_6_0_0 6 || (next_6_0_0 7 || (next_6_0_0 8 || (next_6_0_0 9 || false)))))))))) = false
  rw [d_6_0_0_0, d_6_0_0_1, d_6_0_0_2, d_6_0_0_3, d_6_0_0_4, d_6_0_0_5, d_6_0_0_6, d_6_0_0_7, d_6_0_0_8, d_6_0_0_9] <;> rfl
theorem b_6_0_0 : branch 6 0 0 = false := branch_lift 6 0 0 2 state_6_0_0 (by decide +kernel) state_ok_6_0_0
def state_6_0_1 : List W := [16325890103836674, 809071576521218071, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_0_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_0_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_0_1_0 : next_6_0_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_1 : next_6_0_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_2 : next_6_0_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_3 : next_6_0_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_4 : next_6_0_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_5 : next_6_0_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_6 : next_6_0_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_7 : next_6_0_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_8 : next_6_0_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_9 : next_6_0_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_10 : next_6_0_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_11 : next_6_0_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_12 : next_6_0_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_13 : next_6_0_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_1_14 : next_6_0_1 14 = false := by decide +kernel
theorem state_ok_6_0_1 : optimized 6 1 state_6_0_1 = false := by
  change ((state_6_0_1 == [goal] || state_6_0_1 == [~~~goal]) || _) = false
  rw [show (state_6_0_1 == [goal] || state_6_0_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_0_1 0 || (next_6_0_1 1 || (next_6_0_1 2 || (next_6_0_1 3 || (next_6_0_1 4 || (next_6_0_1 5 || (next_6_0_1 6 || (next_6_0_1 7 || (next_6_0_1 8 || (next_6_0_1 9 || (next_6_0_1 10 || (next_6_0_1 11 || (next_6_0_1 12 || (next_6_0_1 13 || (next_6_0_1 14 || false))))))))))))))) = false
  rw [d_6_0_1_0, d_6_0_1_1, d_6_0_1_2, d_6_0_1_3, d_6_0_1_4, d_6_0_1_5, d_6_0_1_6, d_6_0_1_7, d_6_0_1_8, d_6_0_1_9, d_6_0_1_10, d_6_0_1_11, d_6_0_1_12, d_6_0_1_13, d_6_0_1_14] <;> rfl
theorem b_6_0_1 : branch 6 0 1 = false := branch_lift 6 0 1 1 state_6_0_1 (by decide +kernel) state_ok_6_0_1
def state_6_0_2 : List W := [16325890103836674, 17874208644006378, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_0_2 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_0_2).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_0_2_0 : next_6_0_2 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_1 : next_6_0_2 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_2 : next_6_0_2 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_3 : next_6_0_2 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_4 : next_6_0_2 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_5 : next_6_0_2 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_6 : next_6_0_2 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_7 : next_6_0_2 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_8 : next_6_0_2 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_9 : next_6_0_2 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_10 : next_6_0_2 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_11 : next_6_0_2 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_12 : next_6_0_2 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_13 : next_6_0_2 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_2_14 : next_6_0_2 14 = false := by decide +kernel
theorem state_ok_6_0_2 : optimized 6 1 state_6_0_2 = false := by
  change ((state_6_0_2 == [goal] || state_6_0_2 == [~~~goal]) || _) = false
  rw [show (state_6_0_2 == [goal] || state_6_0_2 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_0_2 0 || (next_6_0_2 1 || (next_6_0_2 2 || (next_6_0_2 3 || (next_6_0_2 4 || (next_6_0_2 5 || (next_6_0_2 6 || (next_6_0_2 7 || (next_6_0_2 8 || (next_6_0_2 9 || (next_6_0_2 10 || (next_6_0_2 11 || (next_6_0_2 12 || (next_6_0_2 13 || (next_6_0_2 14 || false))))))))))))))) = false
  rw [d_6_0_2_0, d_6_0_2_1, d_6_0_2_2, d_6_0_2_3, d_6_0_2_4, d_6_0_2_5, d_6_0_2_6, d_6_0_2_7, d_6_0_2_8, d_6_0_2_9, d_6_0_2_10, d_6_0_2_11, d_6_0_2_12, d_6_0_2_13, d_6_0_2_14] <;> rfl
theorem b_6_0_2 : branch 6 0 2 = false := branch_lift 6 0 2 1 state_6_0_2 (by decide +kernel) state_ok_6_0_2
def state_6_0_3 : List W := [16325890103836674, 809071576521218071, 17874208644006378, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_0_3_0 : next_6_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_1 : next_6_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_2 : next_6_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_3 : next_6_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_4 : next_6_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_5 : next_6_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_6 : next_6_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_7 : next_6_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_8 : next_6_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_9 : next_6_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_10 : next_6_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_11 : next_6_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_12 : next_6_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_13 : next_6_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_14 : next_6_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_15 : next_6_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_16 : next_6_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_17 : next_6_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_18 : next_6_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_19 : next_6_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_0_3_20 : next_6_0_3 20 = false := by decide +kernel
theorem state_ok_6_0_3 : optimized 6 0 state_6_0_3 = false := by
  change ((state_6_0_3 == [goal] || state_6_0_3 == [~~~goal]) || _) = false
  rw [show (state_6_0_3 == [goal] || state_6_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_0_3 0 || (next_6_0_3 1 || (next_6_0_3 2 || (next_6_0_3 3 || (next_6_0_3 4 || (next_6_0_3 5 || (next_6_0_3 6 || (next_6_0_3 7 || (next_6_0_3 8 || (next_6_0_3 9 || (next_6_0_3 10 || (next_6_0_3 11 || (next_6_0_3 12 || (next_6_0_3 13 || (next_6_0_3 14 || (next_6_0_3 15 || (next_6_0_3 16 || (next_6_0_3 17 || (next_6_0_3 18 || (next_6_0_3 19 || (next_6_0_3 20 || false))))))))))))))))))))) = false
  rw [d_6_0_3_0, d_6_0_3_1, d_6_0_3_2, d_6_0_3_3, d_6_0_3_4, d_6_0_3_5, d_6_0_3_6, d_6_0_3_7, d_6_0_3_8, d_6_0_3_9, d_6_0_3_10, d_6_0_3_11, d_6_0_3_12, d_6_0_3_13, d_6_0_3_14, d_6_0_3_15, d_6_0_3_16, d_6_0_3_17, d_6_0_3_18, d_6_0_3_19, d_6_0_3_20] <;> rfl
theorem b_6_0_3 : branch 6 0 3 = false := branch_lift 6 0 3 0 state_6_0_3 (by decide +kernel) state_ok_6_0_3
theorem c_6_0 : lane 6 0 = false := branch_join 6 0 b_6_0_0 b_6_0_1 b_6_0_2 b_6_0_3
theorem b_6_1_0 : branch 6 1 0 = false := by decide +kernel
theorem b_6_1_1 : branch 6 1 1 = false := by decide +kernel
theorem b_6_1_2 : branch 6 1 2 = false := by decide +kernel
def state_6_1_3 : List W := [810619895061387775, 809071576521218071, 17874208644006378, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_1_3_0 : next_6_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_1 : next_6_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_2 : next_6_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_3 : next_6_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_4 : next_6_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_5 : next_6_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_6 : next_6_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_7 : next_6_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_8 : next_6_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_9 : next_6_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_10 : next_6_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_11 : next_6_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_12 : next_6_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_13 : next_6_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_14 : next_6_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_15 : next_6_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_16 : next_6_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_17 : next_6_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_18 : next_6_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_19 : next_6_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_1_3_20 : next_6_1_3 20 = false := by decide +kernel
theorem state_ok_6_1_3 : optimized 6 0 state_6_1_3 = false := by
  change ((state_6_1_3 == [goal] || state_6_1_3 == [~~~goal]) || _) = false
  rw [show (state_6_1_3 == [goal] || state_6_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_1_3 0 || (next_6_1_3 1 || (next_6_1_3 2 || (next_6_1_3 3 || (next_6_1_3 4 || (next_6_1_3 5 || (next_6_1_3 6 || (next_6_1_3 7 || (next_6_1_3 8 || (next_6_1_3 9 || (next_6_1_3 10 || (next_6_1_3 11 || (next_6_1_3 12 || (next_6_1_3 13 || (next_6_1_3 14 || (next_6_1_3 15 || (next_6_1_3 16 || (next_6_1_3 17 || (next_6_1_3 18 || (next_6_1_3 19 || (next_6_1_3 20 || false))))))))))))))))))))) = false
  rw [d_6_1_3_0, d_6_1_3_1, d_6_1_3_2, d_6_1_3_3, d_6_1_3_4, d_6_1_3_5, d_6_1_3_6, d_6_1_3_7, d_6_1_3_8, d_6_1_3_9, d_6_1_3_10, d_6_1_3_11, d_6_1_3_12, d_6_1_3_13, d_6_1_3_14, d_6_1_3_15, d_6_1_3_16, d_6_1_3_17, d_6_1_3_18, d_6_1_3_19, d_6_1_3_20] <;> rfl
theorem b_6_1_3 : branch 6 1 3 = false := branch_lift 6 1 3 0 state_6_1_3 (by decide +kernel) state_ok_6_1_3
theorem c_6_1 : lane 6 1 = false := branch_join 6 1 b_6_1_0 b_6_1_1 b_6_1_2 b_6_1_3
theorem b_6_2_0 : branch 6 2 0 = false := by decide +kernel
def state_6_2_1 : List W := [792745686417381397, 809071576521218071, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_2_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_2_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_2_1_0 : next_6_2_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_1 : next_6_2_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_2 : next_6_2_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_3 : next_6_2_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_4 : next_6_2_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_5 : next_6_2_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_6 : next_6_2_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_7 : next_6_2_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_8 : next_6_2_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_9 : next_6_2_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_10 : next_6_2_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_11 : next_6_2_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_12 : next_6_2_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_13 : next_6_2_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_1_14 : next_6_2_1 14 = false := by decide +kernel
theorem state_ok_6_2_1 : optimized 6 1 state_6_2_1 = false := by
  change ((state_6_2_1 == [goal] || state_6_2_1 == [~~~goal]) || _) = false
  rw [show (state_6_2_1 == [goal] || state_6_2_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_2_1 0 || (next_6_2_1 1 || (next_6_2_1 2 || (next_6_2_1 3 || (next_6_2_1 4 || (next_6_2_1 5 || (next_6_2_1 6 || (next_6_2_1 7 || (next_6_2_1 8 || (next_6_2_1 9 || (next_6_2_1 10 || (next_6_2_1 11 || (next_6_2_1 12 || (next_6_2_1 13 || (next_6_2_1 14 || false))))))))))))))) = false
  rw [d_6_2_1_0, d_6_2_1_1, d_6_2_1_2, d_6_2_1_3, d_6_2_1_4, d_6_2_1_5, d_6_2_1_6, d_6_2_1_7, d_6_2_1_8, d_6_2_1_9, d_6_2_1_10, d_6_2_1_11, d_6_2_1_12, d_6_2_1_13, d_6_2_1_14] <;> rfl
theorem b_6_2_1 : branch 6 2 1 = false := branch_lift 6 2 1 1 state_6_2_1 (by decide +kernel) state_ok_6_2_1
theorem b_6_2_2 : branch 6 2 2 = false := by decide +kernel
def state_6_2_3 : List W := [792745686417381397, 809071576521218071, 17874208644006378, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_2_3_0 : next_6_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_1 : next_6_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_2 : next_6_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_3 : next_6_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_4 : next_6_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_5 : next_6_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_6 : next_6_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_7 : next_6_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_8 : next_6_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_9 : next_6_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_10 : next_6_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_11 : next_6_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_12 : next_6_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_13 : next_6_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_14 : next_6_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_15 : next_6_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_16 : next_6_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_17 : next_6_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_18 : next_6_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_19 : next_6_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_2_3_20 : next_6_2_3 20 = false := by decide +kernel
theorem state_ok_6_2_3 : optimized 6 0 state_6_2_3 = false := by
  change ((state_6_2_3 == [goal] || state_6_2_3 == [~~~goal]) || _) = false
  rw [show (state_6_2_3 == [goal] || state_6_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_2_3 0 || (next_6_2_3 1 || (next_6_2_3 2 || (next_6_2_3 3 || (next_6_2_3 4 || (next_6_2_3 5 || (next_6_2_3 6 || (next_6_2_3 7 || (next_6_2_3 8 || (next_6_2_3 9 || (next_6_2_3 10 || (next_6_2_3 11 || (next_6_2_3 12 || (next_6_2_3 13 || (next_6_2_3 14 || (next_6_2_3 15 || (next_6_2_3 16 || (next_6_2_3 17 || (next_6_2_3 18 || (next_6_2_3 19 || (next_6_2_3 20 || false))))))))))))))))))))) = false
  rw [d_6_2_3_0, d_6_2_3_1, d_6_2_3_2, d_6_2_3_3, d_6_2_3_4, d_6_2_3_5, d_6_2_3_6, d_6_2_3_7, d_6_2_3_8, d_6_2_3_9, d_6_2_3_10, d_6_2_3_11, d_6_2_3_12, d_6_2_3_13, d_6_2_3_14, d_6_2_3_15, d_6_2_3_16, d_6_2_3_17, d_6_2_3_18, d_6_2_3_19, d_6_2_3_20] <;> rfl
theorem b_6_2_3 : branch 6 2 3 = false := branch_lift 6 2 3 0 state_6_2_3 (by decide +kernel) state_ok_6_2_3
theorem c_6_2 : lane 6 2 = false := branch_join 6 2 b_6_2_0 b_6_2_1 b_6_2_2 b_6_2_3
theorem b_6_3_0 : branch 6 3 0 = false := by decide +kernel
theorem b_6_3_1 : branch 6 3 1 = false := by decide +kernel
def state_6_3_2 : List W := [1548318540169704, 17874208644006378, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_3_2 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_3_2).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_3_2_0 : next_6_3_2 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_1 : next_6_3_2 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_2 : next_6_3_2 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_3 : next_6_3_2 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_4 : next_6_3_2 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_5 : next_6_3_2 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_6 : next_6_3_2 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_7 : next_6_3_2 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_8 : next_6_3_2 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_9 : next_6_3_2 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_10 : next_6_3_2 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_11 : next_6_3_2 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_12 : next_6_3_2 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_13 : next_6_3_2 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_2_14 : next_6_3_2 14 = false := by decide +kernel
theorem state_ok_6_3_2 : optimized 6 1 state_6_3_2 = false := by
  change ((state_6_3_2 == [goal] || state_6_3_2 == [~~~goal]) || _) = false
  rw [show (state_6_3_2 == [goal] || state_6_3_2 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_3_2 0 || (next_6_3_2 1 || (next_6_3_2 2 || (next_6_3_2 3 || (next_6_3_2 4 || (next_6_3_2 5 || (next_6_3_2 6 || (next_6_3_2 7 || (next_6_3_2 8 || (next_6_3_2 9 || (next_6_3_2 10 || (next_6_3_2 11 || (next_6_3_2 12 || (next_6_3_2 13 || (next_6_3_2 14 || false))))))))))))))) = false
  rw [d_6_3_2_0, d_6_3_2_1, d_6_3_2_2, d_6_3_2_3, d_6_3_2_4, d_6_3_2_5, d_6_3_2_6, d_6_3_2_7, d_6_3_2_8, d_6_3_2_9, d_6_3_2_10, d_6_3_2_11, d_6_3_2_12, d_6_3_2_13, d_6_3_2_14] <;> rfl
theorem b_6_3_2 : branch 6 3 2 = false := branch_lift 6 3 2 1 state_6_3_2 (by decide +kernel) state_ok_6_3_2
def state_6_3_3 : List W := [1548318540169704, 809071576521218071, 17874208644006378, 560697862707653233, 881712051380150656, 1134907655299531261, 1152920955840713728]
def next_6_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_6_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_6_3_3_0 : next_6_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_1 : next_6_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_2 : next_6_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_3 : next_6_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_4 : next_6_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_5 : next_6_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_6 : next_6_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_7 : next_6_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_8 : next_6_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_9 : next_6_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_10 : next_6_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_11 : next_6_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_12 : next_6_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_13 : next_6_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_14 : next_6_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_15 : next_6_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_16 : next_6_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_17 : next_6_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_18 : next_6_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_19 : next_6_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_6_3_3_20 : next_6_3_3 20 = false := by decide +kernel
theorem state_ok_6_3_3 : optimized 6 0 state_6_3_3 = false := by
  change ((state_6_3_3 == [goal] || state_6_3_3 == [~~~goal]) || _) = false
  rw [show (state_6_3_3 == [goal] || state_6_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_6_3_3 0 || (next_6_3_3 1 || (next_6_3_3 2 || (next_6_3_3 3 || (next_6_3_3 4 || (next_6_3_3 5 || (next_6_3_3 6 || (next_6_3_3 7 || (next_6_3_3 8 || (next_6_3_3 9 || (next_6_3_3 10 || (next_6_3_3 11 || (next_6_3_3 12 || (next_6_3_3 13 || (next_6_3_3 14 || (next_6_3_3 15 || (next_6_3_3 16 || (next_6_3_3 17 || (next_6_3_3 18 || (next_6_3_3 19 || (next_6_3_3 20 || false))))))))))))))))))))) = false
  rw [d_6_3_3_0, d_6_3_3_1, d_6_3_3_2, d_6_3_3_3, d_6_3_3_4, d_6_3_3_5, d_6_3_3_6, d_6_3_3_7, d_6_3_3_8, d_6_3_3_9, d_6_3_3_10, d_6_3_3_11, d_6_3_3_12, d_6_3_3_13, d_6_3_3_14, d_6_3_3_15, d_6_3_3_16, d_6_3_3_17, d_6_3_3_18, d_6_3_3_19, d_6_3_3_20] <;> rfl
theorem b_6_3_3 : branch 6 3 3 = false := branch_lift 6 3 3 0 state_6_3_3 (by decide +kernel) state_ok_6_3_3
theorem c_6_3 : lane 6 3 = false := branch_join 6 3 b_6_3_0 b_6_3_1 b_6_3_2 b_6_3_3
theorem checked_6 : firstGate 6 = false := lanes_join 6 c_6_0 c_6_1 c_6_2 c_6_3
theorem b_7_0_0 : branch 7 0 0 = false := by decide +kernel
def state_7_0_1 : List W := [792633877142175765, 809071576521218071, 560697862707653233, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_7_0_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_7_0_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_7_0_1_0 : next_7_0_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_1 : next_7_0_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_2 : next_7_0_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_3 : next_7_0_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_4 : next_7_0_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_5 : next_7_0_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_6 : next_7_0_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_7 : next_7_0_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_8 : next_7_0_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_9 : next_7_0_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_10 : next_7_0_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_11 : next_7_0_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_12 : next_7_0_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_13 : next_7_0_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_1_14 : next_7_0_1 14 = false := by decide +kernel
theorem state_ok_7_0_1 : optimized 6 1 state_7_0_1 = false := by
  change ((state_7_0_1 == [goal] || state_7_0_1 == [~~~goal]) || _) = false
  rw [show (state_7_0_1 == [goal] || state_7_0_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_7_0_1 0 || (next_7_0_1 1 || (next_7_0_1 2 || (next_7_0_1 3 || (next_7_0_1 4 || (next_7_0_1 5 || (next_7_0_1 6 || (next_7_0_1 7 || (next_7_0_1 8 || (next_7_0_1 9 || (next_7_0_1 10 || (next_7_0_1 11 || (next_7_0_1 12 || (next_7_0_1 13 || (next_7_0_1 14 || false))))))))))))))) = false
  rw [d_7_0_1_0, d_7_0_1_1, d_7_0_1_2, d_7_0_1_3, d_7_0_1_4, d_7_0_1_5, d_7_0_1_6, d_7_0_1_7, d_7_0_1_8, d_7_0_1_9, d_7_0_1_10, d_7_0_1_11, d_7_0_1_12, d_7_0_1_13, d_7_0_1_14] <;> rfl
theorem b_7_0_1 : branch 7 0 1 = false := branch_lift 7 0 1 1 state_7_0_1 (by decide +kernel) state_ok_7_0_1
theorem b_7_0_2 : branch 7 0 2 = false := by decide +kernel
def state_7_0_3 : List W := [792633877142175765, 809071576521218071, 1134907655299531261, 560697862707653233, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_7_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_7_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_7_0_3_0 : next_7_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_1 : next_7_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_2 : next_7_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_3 : next_7_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_4 : next_7_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_5 : next_7_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_6 : next_7_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_7 : next_7_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_8 : next_7_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_9 : next_7_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_10 : next_7_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_11 : next_7_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_12 : next_7_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_13 : next_7_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_14 : next_7_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_15 : next_7_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_16 : next_7_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_17 : next_7_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_18 : next_7_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_19 : next_7_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_0_3_20 : next_7_0_3 20 = false := by decide +kernel
theorem state_ok_7_0_3 : optimized 6 0 state_7_0_3 = false := by
  change ((state_7_0_3 == [goal] || state_7_0_3 == [~~~goal]) || _) = false
  rw [show (state_7_0_3 == [goal] || state_7_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_7_0_3 0 || (next_7_0_3 1 || (next_7_0_3 2 || (next_7_0_3 3 || (next_7_0_3 4 || (next_7_0_3 5 || (next_7_0_3 6 || (next_7_0_3 7 || (next_7_0_3 8 || (next_7_0_3 9 || (next_7_0_3 10 || (next_7_0_3 11 || (next_7_0_3 12 || (next_7_0_3 13 || (next_7_0_3 14 || (next_7_0_3 15 || (next_7_0_3 16 || (next_7_0_3 17 || (next_7_0_3 18 || (next_7_0_3 19 || (next_7_0_3 20 || false))))))))))))))))))))) = false
  rw [d_7_0_3_0, d_7_0_3_1, d_7_0_3_2, d_7_0_3_3, d_7_0_3_4, d_7_0_3_5, d_7_0_3_6, d_7_0_3_7, d_7_0_3_8, d_7_0_3_9, d_7_0_3_10, d_7_0_3_11, d_7_0_3_12, d_7_0_3_13, d_7_0_3_14, d_7_0_3_15, d_7_0_3_16, d_7_0_3_17, d_7_0_3_18, d_7_0_3_19, d_7_0_3_20] <;> rfl
theorem b_7_0_3 : branch 7 0 3 = false := branch_lift 7 0 3 0 state_7_0_3 (by decide +kernel) state_ok_7_0_3
theorem c_7_0 : lane 7 0 = false := branch_join 7 0 b_7_0_0 b_7_0_1 b_7_0_2 b_7_0_3
theorem b_7_1_0 : branch 7 1 0 = false := by decide +kernel
theorem b_7_1_1 : branch 7 1 1 = false := by decide +kernel
theorem b_7_1_2 : branch 7 1 2 = false := by decide +kernel
def state_7_1_3 : List W := [1151345354678573567, 809071576521218071, 1134907655299531261, 560697862707653233, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_7_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_7_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_7_1_3_0 : next_7_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_1 : next_7_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_2 : next_7_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_3 : next_7_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_4 : next_7_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_5 : next_7_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_6 : next_7_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_7 : next_7_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_8 : next_7_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_9 : next_7_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_10 : next_7_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_11 : next_7_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_12 : next_7_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_13 : next_7_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_14 : next_7_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_15 : next_7_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_16 : next_7_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_17 : next_7_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_18 : next_7_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_19 : next_7_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_1_3_20 : next_7_1_3 20 = false := by decide +kernel
theorem state_ok_7_1_3 : optimized 6 0 state_7_1_3 = false := by
  change ((state_7_1_3 == [goal] || state_7_1_3 == [~~~goal]) || _) = false
  rw [show (state_7_1_3 == [goal] || state_7_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_7_1_3 0 || (next_7_1_3 1 || (next_7_1_3 2 || (next_7_1_3 3 || (next_7_1_3 4 || (next_7_1_3 5 || (next_7_1_3 6 || (next_7_1_3 7 || (next_7_1_3 8 || (next_7_1_3 9 || (next_7_1_3 10 || (next_7_1_3 11 || (next_7_1_3 12 || (next_7_1_3 13 || (next_7_1_3 14 || (next_7_1_3 15 || (next_7_1_3 16 || (next_7_1_3 17 || (next_7_1_3 18 || (next_7_1_3 19 || (next_7_1_3 20 || false))))))))))))))))))))) = false
  rw [d_7_1_3_0, d_7_1_3_1, d_7_1_3_2, d_7_1_3_3, d_7_1_3_4, d_7_1_3_5, d_7_1_3_6, d_7_1_3_7, d_7_1_3_8, d_7_1_3_9, d_7_1_3_10, d_7_1_3_11, d_7_1_3_12, d_7_1_3_13, d_7_1_3_14, d_7_1_3_15, d_7_1_3_16, d_7_1_3_17, d_7_1_3_18, d_7_1_3_19, d_7_1_3_20] <;> rfl
theorem b_7_1_3 : branch 7 1 3 = false := branch_lift 7 1 3 0 state_7_1_3 (by decide +kernel) state_ok_7_1_3
theorem c_7_1 : lane 7 1 = false := branch_join 7 1 b_7_1_0 b_7_1_1 b_7_1_2 b_7_1_3
theorem b_7_2_0 : branch 7 2 0 = false := by decide +kernel
def state_7_2_1 : List W := [16437699379042306, 809071576521218071, 560697862707653233, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_7_2_1 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_7_2_1).getD idx (0, 0, [])
  dispatch 1 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_7_2_1_0 : next_7_2_1 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_1 : next_7_2_1 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_2 : next_7_2_1 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_3 : next_7_2_1 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_4 : next_7_2_1 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_5 : next_7_2_1 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_6 : next_7_2_1 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_7 : next_7_2_1 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_8 : next_7_2_1 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_9 : next_7_2_1 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_10 : next_7_2_1 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_11 : next_7_2_1 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_12 : next_7_2_1 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_13 : next_7_2_1 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_1_14 : next_7_2_1 14 = false := by decide +kernel
theorem state_ok_7_2_1 : optimized 6 1 state_7_2_1 = false := by
  change ((state_7_2_1 == [goal] || state_7_2_1 == [~~~goal]) || _) = false
  rw [show (state_7_2_1 == [goal] || state_7_2_1 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_7_2_1 0 || (next_7_2_1 1 || (next_7_2_1 2 || (next_7_2_1 3 || (next_7_2_1 4 || (next_7_2_1 5 || (next_7_2_1 6 || (next_7_2_1 7 || (next_7_2_1 8 || (next_7_2_1 9 || (next_7_2_1 10 || (next_7_2_1 11 || (next_7_2_1 12 || (next_7_2_1 13 || (next_7_2_1 14 || false))))))))))))))) = false
  rw [d_7_2_1_0, d_7_2_1_1, d_7_2_1_2, d_7_2_1_3, d_7_2_1_4, d_7_2_1_5, d_7_2_1_6, d_7_2_1_7, d_7_2_1_8, d_7_2_1_9, d_7_2_1_10, d_7_2_1_11, d_7_2_1_12, d_7_2_1_13, d_7_2_1_14] <;> rfl
theorem b_7_2_1 : branch 7 2 1 = false := branch_lift 7 2 1 1 state_7_2_1 (by decide +kernel) state_ok_7_2_1
theorem b_7_2_2 : branch 7 2 2 = false := by decide +kernel
def state_7_2_3 : List W := [16437699379042306, 809071576521218071, 1134907655299531261, 560697862707653233, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_7_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_7_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_7_2_3_0 : next_7_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_1 : next_7_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_2 : next_7_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_3 : next_7_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_4 : next_7_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_5 : next_7_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_6 : next_7_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_7 : next_7_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_8 : next_7_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_9 : next_7_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_10 : next_7_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_11 : next_7_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_12 : next_7_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_13 : next_7_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_14 : next_7_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_15 : next_7_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_16 : next_7_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_17 : next_7_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_18 : next_7_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_19 : next_7_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_2_3_20 : next_7_2_3 20 = false := by decide +kernel
theorem state_ok_7_2_3 : optimized 6 0 state_7_2_3 = false := by
  change ((state_7_2_3 == [goal] || state_7_2_3 == [~~~goal]) || _) = false
  rw [show (state_7_2_3 == [goal] || state_7_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_7_2_3 0 || (next_7_2_3 1 || (next_7_2_3 2 || (next_7_2_3 3 || (next_7_2_3 4 || (next_7_2_3 5 || (next_7_2_3 6 || (next_7_2_3 7 || (next_7_2_3 8 || (next_7_2_3 9 || (next_7_2_3 10 || (next_7_2_3 11 || (next_7_2_3 12 || (next_7_2_3 13 || (next_7_2_3 14 || (next_7_2_3 15 || (next_7_2_3 16 || (next_7_2_3 17 || (next_7_2_3 18 || (next_7_2_3 19 || (next_7_2_3 20 || false))))))))))))))))))))) = false
  rw [d_7_2_3_0, d_7_2_3_1, d_7_2_3_2, d_7_2_3_3, d_7_2_3_4, d_7_2_3_5, d_7_2_3_6, d_7_2_3_7, d_7_2_3_8, d_7_2_3_9, d_7_2_3_10, d_7_2_3_11, d_7_2_3_12, d_7_2_3_13, d_7_2_3_14, d_7_2_3_15, d_7_2_3_16, d_7_2_3_17, d_7_2_3_18, d_7_2_3_19, d_7_2_3_20] <;> rfl
theorem b_7_2_3 : branch 7 2 3 = false := branch_lift 7 2 3 0 state_7_2_3 (by decide +kernel) state_ok_7_2_3
theorem c_7_2 : lane 7 2 = false := branch_join 7 2 b_7_2_0 b_7_2_1 b_7_2_2 b_7_2_3
theorem b_7_3_0 : branch 7 3 0 = false := by decide +kernel
theorem b_7_3_1 : branch 7 3 1 = false := by decide +kernel
theorem b_7_3_2 : branch 7 3 2 = false := by decide +kernel
def state_7_3_3 : List W := [342273778157355496, 809071576521218071, 1134907655299531261, 560697862707653233, 881712051380150656, 17874208644006378, 1152920955840713728]
def next_7_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_7_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_7_3_3_0 : next_7_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_1 : next_7_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_2 : next_7_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_3 : next_7_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_4 : next_7_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_5 : next_7_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_6 : next_7_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_7 : next_7_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_8 : next_7_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_9 : next_7_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_10 : next_7_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_11 : next_7_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_12 : next_7_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_13 : next_7_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_14 : next_7_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_15 : next_7_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_16 : next_7_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_17 : next_7_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_18 : next_7_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_19 : next_7_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_7_3_3_20 : next_7_3_3 20 = false := by decide +kernel
theorem state_ok_7_3_3 : optimized 6 0 state_7_3_3 = false := by
  change ((state_7_3_3 == [goal] || state_7_3_3 == [~~~goal]) || _) = false
  rw [show (state_7_3_3 == [goal] || state_7_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_7_3_3 0 || (next_7_3_3 1 || (next_7_3_3 2 || (next_7_3_3 3 || (next_7_3_3 4 || (next_7_3_3 5 || (next_7_3_3 6 || (next_7_3_3 7 || (next_7_3_3 8 || (next_7_3_3 9 || (next_7_3_3 10 || (next_7_3_3 11 || (next_7_3_3 12 || (next_7_3_3 13 || (next_7_3_3 14 || (next_7_3_3 15 || (next_7_3_3 16 || (next_7_3_3 17 || (next_7_3_3 18 || (next_7_3_3 19 || (next_7_3_3 20 || false))))))))))))))))))))) = false
  rw [d_7_3_3_0, d_7_3_3_1, d_7_3_3_2, d_7_3_3_3, d_7_3_3_4, d_7_3_3_5, d_7_3_3_6, d_7_3_3_7, d_7_3_3_8, d_7_3_3_9, d_7_3_3_10, d_7_3_3_11, d_7_3_3_12, d_7_3_3_13, d_7_3_3_14, d_7_3_3_15, d_7_3_3_16, d_7_3_3_17, d_7_3_3_18, d_7_3_3_19, d_7_3_3_20] <;> rfl
theorem b_7_3_3 : branch 7 3 3 = false := branch_lift 7 3 3 0 state_7_3_3 (by decide +kernel) state_ok_7_3_3
theorem c_7_3 : lane 7 3 = false := branch_join 7 3 b_7_3_0 b_7_3_1 b_7_3_2 b_7_3_3
theorem checked_7 : firstGate 7 = false := lanes_join 7 c_7_0 c_7_1 c_7_2 c_7_3
theorem b_8_0_0 : branch 8 0 0 = false := by decide +kernel
theorem b_8_0_1 : branch 8 0 1 = false := by decide +kernel
theorem b_8_0_2 : branch 8 0 2 = false := by decide +kernel
def state_8_0_3 : List W := [809071233930432512, 809071576521218071, 1152920955840713728, 560697862707653233, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_8_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_8_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_8_0_3_0 : next_8_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_1 : next_8_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_2 : next_8_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_3 : next_8_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_4 : next_8_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_5 : next_8_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_6 : next_8_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_7 : next_8_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_8 : next_8_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_9 : next_8_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_10 : next_8_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_11 : next_8_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_12 : next_8_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_13 : next_8_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_14 : next_8_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_15 : next_8_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_16 : next_8_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_17 : next_8_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_18 : next_8_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_19 : next_8_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_0_3_20 : next_8_0_3 20 = false := by decide +kernel
theorem state_ok_8_0_3 : optimized 6 0 state_8_0_3 = false := by
  change ((state_8_0_3 == [goal] || state_8_0_3 == [~~~goal]) || _) = false
  rw [show (state_8_0_3 == [goal] || state_8_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_8_0_3 0 || (next_8_0_3 1 || (next_8_0_3 2 || (next_8_0_3 3 || (next_8_0_3 4 || (next_8_0_3 5 || (next_8_0_3 6 || (next_8_0_3 7 || (next_8_0_3 8 || (next_8_0_3 9 || (next_8_0_3 10 || (next_8_0_3 11 || (next_8_0_3 12 || (next_8_0_3 13 || (next_8_0_3 14 || (next_8_0_3 15 || (next_8_0_3 16 || (next_8_0_3 17 || (next_8_0_3 18 || (next_8_0_3 19 || (next_8_0_3 20 || false))))))))))))))))))))) = false
  rw [d_8_0_3_0, d_8_0_3_1, d_8_0_3_2, d_8_0_3_3, d_8_0_3_4, d_8_0_3_5, d_8_0_3_6, d_8_0_3_7, d_8_0_3_8, d_8_0_3_9, d_8_0_3_10, d_8_0_3_11, d_8_0_3_12, d_8_0_3_13, d_8_0_3_14, d_8_0_3_15, d_8_0_3_16, d_8_0_3_17, d_8_0_3_18, d_8_0_3_19, d_8_0_3_20] <;> rfl
theorem b_8_0_3 : branch 8 0 3 = false := branch_lift 8 0 3 0 state_8_0_3 (by decide +kernel) state_ok_8_0_3
theorem c_8_0 : lane 8 0 = false := branch_join 8 0 b_8_0_0 b_8_0_1 b_8_0_2 b_8_0_3
theorem b_8_1_0 : branch 8 1 0 = false := by decide +kernel
theorem b_8_1_1 : branch 8 1 1 = false := by decide +kernel
theorem b_8_1_2 : branch 8 1 2 = false := by decide +kernel
def state_8_1_3 : List W := [1152921298431499287, 809071576521218071, 1152920955840713728, 560697862707653233, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_8_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_8_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_8_1_3_0 : next_8_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_1 : next_8_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_2 : next_8_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_3 : next_8_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_4 : next_8_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_5 : next_8_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_6 : next_8_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_7 : next_8_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_8 : next_8_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_9 : next_8_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_10 : next_8_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_11 : next_8_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_12 : next_8_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_13 : next_8_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_14 : next_8_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_15 : next_8_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_16 : next_8_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_17 : next_8_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_18 : next_8_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_19 : next_8_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_1_3_20 : next_8_1_3 20 = false := by decide +kernel
theorem state_ok_8_1_3 : optimized 6 0 state_8_1_3 = false := by
  change ((state_8_1_3 == [goal] || state_8_1_3 == [~~~goal]) || _) = false
  rw [show (state_8_1_3 == [goal] || state_8_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_8_1_3 0 || (next_8_1_3 1 || (next_8_1_3 2 || (next_8_1_3 3 || (next_8_1_3 4 || (next_8_1_3 5 || (next_8_1_3 6 || (next_8_1_3 7 || (next_8_1_3 8 || (next_8_1_3 9 || (next_8_1_3 10 || (next_8_1_3 11 || (next_8_1_3 12 || (next_8_1_3 13 || (next_8_1_3 14 || (next_8_1_3 15 || (next_8_1_3 16 || (next_8_1_3 17 || (next_8_1_3 18 || (next_8_1_3 19 || (next_8_1_3 20 || false))))))))))))))))))))) = false
  rw [d_8_1_3_0, d_8_1_3_1, d_8_1_3_2, d_8_1_3_3, d_8_1_3_4, d_8_1_3_5, d_8_1_3_6, d_8_1_3_7, d_8_1_3_8, d_8_1_3_9, d_8_1_3_10, d_8_1_3_11, d_8_1_3_12, d_8_1_3_13, d_8_1_3_14, d_8_1_3_15, d_8_1_3_16, d_8_1_3_17, d_8_1_3_18, d_8_1_3_19, d_8_1_3_20] <;> rfl
theorem b_8_1_3 : branch 8 1 3 = false := branch_lift 8 1 3 0 state_8_1_3 (by decide +kernel) state_ok_8_1_3
theorem c_8_1 : lane 8 1 = false := branch_join 8 1 b_8_1_0 b_8_1_1 b_8_1_2 b_8_1_3
theorem b_8_2_0 : branch 8 2 0 = false := by decide +kernel
theorem b_8_2_1 : branch 8 2 1 = false := by decide +kernel
theorem b_8_2_2 : branch 8 2 2 = false := by decide +kernel
def state_8_2_3 : List W := [342590785559, 809071576521218071, 1152920955840713728, 560697862707653233, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_8_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_8_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_8_2_3_0 : next_8_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_1 : next_8_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_2 : next_8_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_3 : next_8_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_4 : next_8_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_5 : next_8_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_6 : next_8_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_7 : next_8_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_8 : next_8_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_9 : next_8_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_10 : next_8_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_11 : next_8_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_12 : next_8_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_13 : next_8_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_14 : next_8_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_15 : next_8_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_16 : next_8_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_17 : next_8_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_18 : next_8_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_19 : next_8_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_2_3_20 : next_8_2_3 20 = false := by decide +kernel
theorem state_ok_8_2_3 : optimized 6 0 state_8_2_3 = false := by
  change ((state_8_2_3 == [goal] || state_8_2_3 == [~~~goal]) || _) = false
  rw [show (state_8_2_3 == [goal] || state_8_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_8_2_3 0 || (next_8_2_3 1 || (next_8_2_3 2 || (next_8_2_3 3 || (next_8_2_3 4 || (next_8_2_3 5 || (next_8_2_3 6 || (next_8_2_3 7 || (next_8_2_3 8 || (next_8_2_3 9 || (next_8_2_3 10 || (next_8_2_3 11 || (next_8_2_3 12 || (next_8_2_3 13 || (next_8_2_3 14 || (next_8_2_3 15 || (next_8_2_3 16 || (next_8_2_3 17 || (next_8_2_3 18 || (next_8_2_3 19 || (next_8_2_3 20 || false))))))))))))))))))))) = false
  rw [d_8_2_3_0, d_8_2_3_1, d_8_2_3_2, d_8_2_3_3, d_8_2_3_4, d_8_2_3_5, d_8_2_3_6, d_8_2_3_7, d_8_2_3_8, d_8_2_3_9, d_8_2_3_10, d_8_2_3_11, d_8_2_3_12, d_8_2_3_13, d_8_2_3_14, d_8_2_3_15, d_8_2_3_16, d_8_2_3_17, d_8_2_3_18, d_8_2_3_19, d_8_2_3_20] <;> rfl
theorem b_8_2_3 : branch 8 2 3 = false := branch_lift 8 2 3 0 state_8_2_3 (by decide +kernel) state_ok_8_2_3
theorem c_8_2 : lane 8 2 = false := branch_join 8 2 b_8_2_0 b_8_2_1 b_8_2_2 b_8_2_3
theorem b_8_3_0 : branch 8 3 0 = false := by decide +kernel
theorem b_8_3_1 : branch 8 3 1 = false := by decide +kernel
theorem b_8_3_2 : branch 8 3 2 = false := by decide +kernel
def state_8_3_3 : List W := [343849721910281216, 809071576521218071, 1152920955840713728, 560697862707653233, 881712051380150656, 17874208644006378, 1134907655299531261]
def next_8_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_8_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_8_3_3_0 : next_8_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_1 : next_8_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_2 : next_8_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_3 : next_8_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_4 : next_8_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_5 : next_8_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_6 : next_8_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_7 : next_8_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_8 : next_8_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_9 : next_8_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_10 : next_8_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_11 : next_8_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_12 : next_8_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_13 : next_8_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_14 : next_8_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_15 : next_8_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_16 : next_8_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_17 : next_8_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_18 : next_8_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_19 : next_8_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_8_3_3_20 : next_8_3_3 20 = false := by decide +kernel
theorem state_ok_8_3_3 : optimized 6 0 state_8_3_3 = false := by
  change ((state_8_3_3 == [goal] || state_8_3_3 == [~~~goal]) || _) = false
  rw [show (state_8_3_3 == [goal] || state_8_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_8_3_3 0 || (next_8_3_3 1 || (next_8_3_3 2 || (next_8_3_3 3 || (next_8_3_3 4 || (next_8_3_3 5 || (next_8_3_3 6 || (next_8_3_3 7 || (next_8_3_3 8 || (next_8_3_3 9 || (next_8_3_3 10 || (next_8_3_3 11 || (next_8_3_3 12 || (next_8_3_3 13 || (next_8_3_3 14 || (next_8_3_3 15 || (next_8_3_3 16 || (next_8_3_3 17 || (next_8_3_3 18 || (next_8_3_3 19 || (next_8_3_3 20 || false))))))))))))))))))))) = false
  rw [d_8_3_3_0, d_8_3_3_1, d_8_3_3_2, d_8_3_3_3, d_8_3_3_4, d_8_3_3_5, d_8_3_3_6, d_8_3_3_7, d_8_3_3_8, d_8_3_3_9, d_8_3_3_10, d_8_3_3_11, d_8_3_3_12, d_8_3_3_13, d_8_3_3_14, d_8_3_3_15, d_8_3_3_16, d_8_3_3_17, d_8_3_3_18, d_8_3_3_19, d_8_3_3_20] <;> rfl
theorem b_8_3_3 : branch 8 3 3 = false := branch_lift 8 3 3 0 state_8_3_3 (by decide +kernel) state_ok_8_3_3
theorem c_8_3 : lane 8 3 = false := branch_join 8 3 b_8_3_0 b_8_3_1 b_8_3_2 b_8_3_3
theorem checked_8 : firstGate 8 = false := lanes_join 8 c_8_0 c_8_1 c_8_2 c_8_3
theorem b_9_0_0 : branch 9 0 0 = false := by decide +kernel
theorem b_9_0_1 : branch 9 0 1 = false := by decide +kernel
theorem b_9_0_2 : branch 9 0 2 = false := by decide +kernel
def state_9_0_3 : List W := [16888979648414080, 881712051380150656, 17874208644006378, 560697862707653233, 809071576521218071, 1134907655299531261, 1152920955840713728]
def next_9_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_9_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_9_0_3_0 : next_9_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_1 : next_9_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_2 : next_9_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_3 : next_9_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_4 : next_9_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_5 : next_9_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_6 : next_9_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_7 : next_9_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_8 : next_9_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_9 : next_9_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_10 : next_9_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_11 : next_9_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_12 : next_9_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_13 : next_9_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_14 : next_9_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_15 : next_9_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_16 : next_9_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_17 : next_9_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_18 : next_9_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_19 : next_9_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_0_3_20 : next_9_0_3 20 = false := by decide +kernel
theorem state_ok_9_0_3 : optimized 6 0 state_9_0_3 = false := by
  change ((state_9_0_3 == [goal] || state_9_0_3 == [~~~goal]) || _) = false
  rw [show (state_9_0_3 == [goal] || state_9_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_9_0_3 0 || (next_9_0_3 1 || (next_9_0_3 2 || (next_9_0_3 3 || (next_9_0_3 4 || (next_9_0_3 5 || (next_9_0_3 6 || (next_9_0_3 7 || (next_9_0_3 8 || (next_9_0_3 9 || (next_9_0_3 10 || (next_9_0_3 11 || (next_9_0_3 12 || (next_9_0_3 13 || (next_9_0_3 14 || (next_9_0_3 15 || (next_9_0_3 16 || (next_9_0_3 17 || (next_9_0_3 18 || (next_9_0_3 19 || (next_9_0_3 20 || false))))))))))))))))))))) = false
  rw [d_9_0_3_0, d_9_0_3_1, d_9_0_3_2, d_9_0_3_3, d_9_0_3_4, d_9_0_3_5, d_9_0_3_6, d_9_0_3_7, d_9_0_3_8, d_9_0_3_9, d_9_0_3_10, d_9_0_3_11, d_9_0_3_12, d_9_0_3_13, d_9_0_3_14, d_9_0_3_15, d_9_0_3_16, d_9_0_3_17, d_9_0_3_18, d_9_0_3_19, d_9_0_3_20] <;> rfl
theorem b_9_0_3 : branch 9 0 3 = false := branch_lift 9 0 3 0 state_9_0_3 (by decide +kernel) state_ok_9_0_3
theorem c_9_0 : lane 9 0 = false := branch_join 9 0 b_9_0_0 b_9_0_1 b_9_0_2 b_9_0_3
theorem b_9_1_0 : branch 9 1 0 = false := by decide +kernel
theorem b_9_1_1 : branch 9 1 1 = false := by decide +kernel
theorem b_9_1_2 : branch 9 1 2 = false := by decide +kernel
def state_9_1_3 : List W := [882697280375742954, 881712051380150656, 17874208644006378, 560697862707653233, 809071576521218071, 1134907655299531261, 1152920955840713728]
def next_9_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_9_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_9_1_3_0 : next_9_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_1 : next_9_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_2 : next_9_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_3 : next_9_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_4 : next_9_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_5 : next_9_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_6 : next_9_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_7 : next_9_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_8 : next_9_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_9 : next_9_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_10 : next_9_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_11 : next_9_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_12 : next_9_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_13 : next_9_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_14 : next_9_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_15 : next_9_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_16 : next_9_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_17 : next_9_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_18 : next_9_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_19 : next_9_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_1_3_20 : next_9_1_3 20 = false := by decide +kernel
theorem state_ok_9_1_3 : optimized 6 0 state_9_1_3 = false := by
  change ((state_9_1_3 == [goal] || state_9_1_3 == [~~~goal]) || _) = false
  rw [show (state_9_1_3 == [goal] || state_9_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_9_1_3 0 || (next_9_1_3 1 || (next_9_1_3 2 || (next_9_1_3 3 || (next_9_1_3 4 || (next_9_1_3 5 || (next_9_1_3 6 || (next_9_1_3 7 || (next_9_1_3 8 || (next_9_1_3 9 || (next_9_1_3 10 || (next_9_1_3 11 || (next_9_1_3 12 || (next_9_1_3 13 || (next_9_1_3 14 || (next_9_1_3 15 || (next_9_1_3 16 || (next_9_1_3 17 || (next_9_1_3 18 || (next_9_1_3 19 || (next_9_1_3 20 || false))))))))))))))))))))) = false
  rw [d_9_1_3_0, d_9_1_3_1, d_9_1_3_2, d_9_1_3_3, d_9_1_3_4, d_9_1_3_5, d_9_1_3_6, d_9_1_3_7, d_9_1_3_8, d_9_1_3_9, d_9_1_3_10, d_9_1_3_11, d_9_1_3_12, d_9_1_3_13, d_9_1_3_14, d_9_1_3_15, d_9_1_3_16, d_9_1_3_17, d_9_1_3_18, d_9_1_3_19, d_9_1_3_20] <;> rfl
theorem b_9_1_3 : branch 9 1 3 = false := branch_lift 9 1 3 0 state_9_1_3 (by decide +kernel) state_ok_9_1_3
theorem c_9_1 : lane 9 1 = false := branch_join 9 1 b_9_1_0 b_9_1_1 b_9_1_2 b_9_1_3
theorem b_9_2_0 : branch 9 2 0 = false := by decide +kernel
theorem b_9_2_1 : branch 9 2 1 = false := by decide +kernel
theorem b_9_2_2 : branch 9 2 2 = false := by decide +kernel
def state_9_2_3 : List W := [864823071731736576, 881712051380150656, 17874208644006378, 560697862707653233, 809071576521218071, 1134907655299531261, 1152920955840713728]
def next_9_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_9_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_9_2_3_0 : next_9_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_1 : next_9_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_2 : next_9_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_3 : next_9_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_4 : next_9_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_5 : next_9_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_6 : next_9_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_7 : next_9_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_8 : next_9_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_9 : next_9_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_10 : next_9_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_11 : next_9_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_12 : next_9_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_13 : next_9_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_14 : next_9_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_15 : next_9_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_16 : next_9_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_17 : next_9_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_18 : next_9_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_19 : next_9_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_2_3_20 : next_9_2_3 20 = false := by decide +kernel
theorem state_ok_9_2_3 : optimized 6 0 state_9_2_3 = false := by
  change ((state_9_2_3 == [goal] || state_9_2_3 == [~~~goal]) || _) = false
  rw [show (state_9_2_3 == [goal] || state_9_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_9_2_3 0 || (next_9_2_3 1 || (next_9_2_3 2 || (next_9_2_3 3 || (next_9_2_3 4 || (next_9_2_3 5 || (next_9_2_3 6 || (next_9_2_3 7 || (next_9_2_3 8 || (next_9_2_3 9 || (next_9_2_3 10 || (next_9_2_3 11 || (next_9_2_3 12 || (next_9_2_3 13 || (next_9_2_3 14 || (next_9_2_3 15 || (next_9_2_3 16 || (next_9_2_3 17 || (next_9_2_3 18 || (next_9_2_3 19 || (next_9_2_3 20 || false))))))))))))))))))))) = false
  rw [d_9_2_3_0, d_9_2_3_1, d_9_2_3_2, d_9_2_3_3, d_9_2_3_4, d_9_2_3_5, d_9_2_3_6, d_9_2_3_7, d_9_2_3_8, d_9_2_3_9, d_9_2_3_10, d_9_2_3_11, d_9_2_3_12, d_9_2_3_13, d_9_2_3_14, d_9_2_3_15, d_9_2_3_16, d_9_2_3_17, d_9_2_3_18, d_9_2_3_19, d_9_2_3_20] <;> rfl
theorem b_9_2_3 : branch 9 2 3 = false := branch_lift 9 2 3 0 state_9_2_3 (by decide +kernel) state_ok_9_2_3
theorem c_9_2 : lane 9 2 = false := branch_join 9 2 b_9_2_0 b_9_2_1 b_9_2_2 b_9_2_3
theorem b_9_3_0 : branch 9 3 0 = false := by decide +kernel
theorem b_9_3_1 : branch 9 3 1 = false := by decide +kernel
theorem b_9_3_2 : branch 9 3 2 = false := by decide +kernel
def state_9_3_3 : List W := [985228995592298, 881712051380150656, 17874208644006378, 560697862707653233, 809071576521218071, 1134907655299531261, 1152920955840713728]
def next_9_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_9_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_9_3_3_0 : next_9_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_1 : next_9_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_2 : next_9_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_3 : next_9_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_4 : next_9_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_5 : next_9_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_6 : next_9_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_7 : next_9_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_8 : next_9_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_9 : next_9_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_10 : next_9_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_11 : next_9_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_12 : next_9_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_13 : next_9_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_14 : next_9_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_15 : next_9_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_16 : next_9_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_17 : next_9_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_18 : next_9_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_19 : next_9_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_9_3_3_20 : next_9_3_3 20 = false := by decide +kernel
theorem state_ok_9_3_3 : optimized 6 0 state_9_3_3 = false := by
  change ((state_9_3_3 == [goal] || state_9_3_3 == [~~~goal]) || _) = false
  rw [show (state_9_3_3 == [goal] || state_9_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_9_3_3 0 || (next_9_3_3 1 || (next_9_3_3 2 || (next_9_3_3 3 || (next_9_3_3 4 || (next_9_3_3 5 || (next_9_3_3 6 || (next_9_3_3 7 || (next_9_3_3 8 || (next_9_3_3 9 || (next_9_3_3 10 || (next_9_3_3 11 || (next_9_3_3 12 || (next_9_3_3 13 || (next_9_3_3 14 || (next_9_3_3 15 || (next_9_3_3 16 || (next_9_3_3 17 || (next_9_3_3 18 || (next_9_3_3 19 || (next_9_3_3 20 || false))))))))))))))))))))) = false
  rw [d_9_3_3_0, d_9_3_3_1, d_9_3_3_2, d_9_3_3_3, d_9_3_3_4, d_9_3_3_5, d_9_3_3_6, d_9_3_3_7, d_9_3_3_8, d_9_3_3_9, d_9_3_3_10, d_9_3_3_11, d_9_3_3_12, d_9_3_3_13, d_9_3_3_14, d_9_3_3_15, d_9_3_3_16, d_9_3_3_17, d_9_3_3_18, d_9_3_3_19, d_9_3_3_20] <;> rfl
theorem b_9_3_3 : branch 9 3 3 = false := branch_lift 9 3 3 0 state_9_3_3 (by decide +kernel) state_ok_9_3_3
theorem c_9_3 : lane 9 3 = false := branch_join 9 3 b_9_3_0 b_9_3_1 b_9_3_2 b_9_3_3
theorem checked_9 : firstGate 9 = false := lanes_join 9 c_9_0 c_9_1 c_9_2 c_9_3
theorem b_10_0_0 : branch 10 0 0 = false := by decide +kernel
theorem b_10_0_1 : branch 10 0 1 = false := by decide +kernel
theorem b_10_0_2 : branch 10 0 2 = false := by decide +kernel
def state_10_0_3 : List W := [864691610833650048, 881712051380150656, 1134907655299531261, 560697862707653233, 809071576521218071, 17874208644006378, 1152920955840713728]
def next_10_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_10_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_10_0_3_0 : next_10_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_1 : next_10_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_2 : next_10_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_3 : next_10_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_4 : next_10_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_5 : next_10_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_6 : next_10_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_7 : next_10_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_8 : next_10_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_9 : next_10_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_10 : next_10_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_11 : next_10_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_12 : next_10_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_13 : next_10_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_14 : next_10_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_15 : next_10_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_16 : next_10_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_17 : next_10_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_18 : next_10_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_19 : next_10_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_0_3_20 : next_10_0_3 20 = false := by decide +kernel
theorem state_ok_10_0_3 : optimized 6 0 state_10_0_3 = false := by
  change ((state_10_0_3 == [goal] || state_10_0_3 == [~~~goal]) || _) = false
  rw [show (state_10_0_3 == [goal] || state_10_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_10_0_3 0 || (next_10_0_3 1 || (next_10_0_3 2 || (next_10_0_3 3 || (next_10_0_3 4 || (next_10_0_3 5 || (next_10_0_3 6 || (next_10_0_3 7 || (next_10_0_3 8 || (next_10_0_3 9 || (next_10_0_3 10 || (next_10_0_3 11 || (next_10_0_3 12 || (next_10_0_3 13 || (next_10_0_3 14 || (next_10_0_3 15 || (next_10_0_3 16 || (next_10_0_3 17 || (next_10_0_3 18 || (next_10_0_3 19 || (next_10_0_3 20 || false))))))))))))))))))))) = false
  rw [d_10_0_3_0, d_10_0_3_1, d_10_0_3_2, d_10_0_3_3, d_10_0_3_4, d_10_0_3_5, d_10_0_3_6, d_10_0_3_7, d_10_0_3_8, d_10_0_3_9, d_10_0_3_10, d_10_0_3_11, d_10_0_3_12, d_10_0_3_13, d_10_0_3_14, d_10_0_3_15, d_10_0_3_16, d_10_0_3_17, d_10_0_3_18, d_10_0_3_19, d_10_0_3_20] <;> rfl
theorem b_10_0_3 : branch 10 0 3 = false := branch_lift 10 0 3 0 state_10_0_3 (by decide +kernel) state_ok_10_0_3
theorem c_10_0 : lane 10 0 = false := branch_join 10 0 b_10_0_0 b_10_0_1 b_10_0_2 b_10_0_3
theorem b_10_1_0 : branch 10 1 0 = false := by decide +kernel
theorem b_10_1_1 : branch 10 1 1 = false := by decide +kernel
theorem b_10_1_2 : branch 10 1 2 = false := by decide +kernel
def state_10_1_3 : List W := [1151928095846031869, 881712051380150656, 1134907655299531261, 560697862707653233, 809071576521218071, 17874208644006378, 1152920955840713728]
def next_10_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_10_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_10_1_3_0 : next_10_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_1 : next_10_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_2 : next_10_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_3 : next_10_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_4 : next_10_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_5 : next_10_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_6 : next_10_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_7 : next_10_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_8 : next_10_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_9 : next_10_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_10 : next_10_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_11 : next_10_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_12 : next_10_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_13 : next_10_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_14 : next_10_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_15 : next_10_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_16 : next_10_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_17 : next_10_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_18 : next_10_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_19 : next_10_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_1_3_20 : next_10_1_3 20 = false := by decide +kernel
theorem state_ok_10_1_3 : optimized 6 0 state_10_1_3 = false := by
  change ((state_10_1_3 == [goal] || state_10_1_3 == [~~~goal]) || _) = false
  rw [show (state_10_1_3 == [goal] || state_10_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_10_1_3 0 || (next_10_1_3 1 || (next_10_1_3 2 || (next_10_1_3 3 || (next_10_1_3 4 || (next_10_1_3 5 || (next_10_1_3 6 || (next_10_1_3 7 || (next_10_1_3 8 || (next_10_1_3 9 || (next_10_1_3 10 || (next_10_1_3 11 || (next_10_1_3 12 || (next_10_1_3 13 || (next_10_1_3 14 || (next_10_1_3 15 || (next_10_1_3 16 || (next_10_1_3 17 || (next_10_1_3 18 || (next_10_1_3 19 || (next_10_1_3 20 || false))))))))))))))))))))) = false
  rw [d_10_1_3_0, d_10_1_3_1, d_10_1_3_2, d_10_1_3_3, d_10_1_3_4, d_10_1_3_5, d_10_1_3_6, d_10_1_3_7, d_10_1_3_8, d_10_1_3_9, d_10_1_3_10, d_10_1_3_11, d_10_1_3_12, d_10_1_3_13, d_10_1_3_14, d_10_1_3_15, d_10_1_3_16, d_10_1_3_17, d_10_1_3_18, d_10_1_3_19, d_10_1_3_20] <;> rfl
theorem b_10_1_3 : branch 10 1 3 = false := branch_lift 10 1 3 0 state_10_1_3 (by decide +kernel) state_ok_10_1_3
theorem c_10_1 : lane 10 1 = false := branch_join 10 1 b_10_1_0 b_10_1_1 b_10_1_2 b_10_1_3
theorem b_10_2_0 : branch 10 2 0 = false := by decide +kernel
theorem b_10_2_1 : branch 10 2 1 = false := by decide +kernel
theorem b_10_2_2 : branch 10 2 2 = false := by decide +kernel
def state_10_2_3 : List W := [17020440546500608, 881712051380150656, 1134907655299531261, 560697862707653233, 809071576521218071, 17874208644006378, 1152920955840713728]
def next_10_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_10_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_10_2_3_0 : next_10_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_1 : next_10_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_2 : next_10_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_3 : next_10_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_4 : next_10_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_5 : next_10_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_6 : next_10_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_7 : next_10_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_8 : next_10_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_9 : next_10_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_10 : next_10_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_11 : next_10_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_12 : next_10_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_13 : next_10_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_14 : next_10_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_15 : next_10_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_16 : next_10_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_17 : next_10_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_18 : next_10_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_19 : next_10_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_2_3_20 : next_10_2_3 20 = false := by decide +kernel
theorem state_ok_10_2_3 : optimized 6 0 state_10_2_3 = false := by
  change ((state_10_2_3 == [goal] || state_10_2_3 == [~~~goal]) || _) = false
  rw [show (state_10_2_3 == [goal] || state_10_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_10_2_3 0 || (next_10_2_3 1 || (next_10_2_3 2 || (next_10_2_3 3 || (next_10_2_3 4 || (next_10_2_3 5 || (next_10_2_3 6 || (next_10_2_3 7 || (next_10_2_3 8 || (next_10_2_3 9 || (next_10_2_3 10 || (next_10_2_3 11 || (next_10_2_3 12 || (next_10_2_3 13 || (next_10_2_3 14 || (next_10_2_3 15 || (next_10_2_3 16 || (next_10_2_3 17 || (next_10_2_3 18 || (next_10_2_3 19 || (next_10_2_3 20 || false))))))))))))))))))))) = false
  rw [d_10_2_3_0, d_10_2_3_1, d_10_2_3_2, d_10_2_3_3, d_10_2_3_4, d_10_2_3_5, d_10_2_3_6, d_10_2_3_7, d_10_2_3_8, d_10_2_3_9, d_10_2_3_10, d_10_2_3_11, d_10_2_3_12, d_10_2_3_13, d_10_2_3_14, d_10_2_3_15, d_10_2_3_16, d_10_2_3_17, d_10_2_3_18, d_10_2_3_19, d_10_2_3_20] <;> rfl
theorem b_10_2_3 : branch 10 2 3 = false := branch_lift 10 2 3 0 state_10_2_3 (by decide +kernel) state_ok_10_2_3
theorem c_10_2 : lane 10 2 = false := branch_join 10 2 b_10_2_0 b_10_2_1 b_10_2_2 b_10_2_3
theorem b_10_3_0 : branch 10 3 0 = false := by decide +kernel
theorem b_10_3_1 : branch 10 3 1 = false := by decide +kernel
theorem b_10_3_2 : branch 10 3 2 = false := by decide +kernel
def state_10_3_3 : List W := [270216044465881213, 881712051380150656, 1134907655299531261, 560697862707653233, 809071576521218071, 17874208644006378, 1152920955840713728]
def next_10_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_10_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_10_3_3_0 : next_10_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_1 : next_10_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_2 : next_10_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_3 : next_10_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_4 : next_10_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_5 : next_10_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_6 : next_10_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_7 : next_10_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_8 : next_10_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_9 : next_10_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_10 : next_10_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_11 : next_10_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_12 : next_10_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_13 : next_10_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_14 : next_10_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_15 : next_10_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_16 : next_10_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_17 : next_10_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_18 : next_10_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_19 : next_10_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_10_3_3_20 : next_10_3_3 20 = false := by decide +kernel
theorem state_ok_10_3_3 : optimized 6 0 state_10_3_3 = false := by
  change ((state_10_3_3 == [goal] || state_10_3_3 == [~~~goal]) || _) = false
  rw [show (state_10_3_3 == [goal] || state_10_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_10_3_3 0 || (next_10_3_3 1 || (next_10_3_3 2 || (next_10_3_3 3 || (next_10_3_3 4 || (next_10_3_3 5 || (next_10_3_3 6 || (next_10_3_3 7 || (next_10_3_3 8 || (next_10_3_3 9 || (next_10_3_3 10 || (next_10_3_3 11 || (next_10_3_3 12 || (next_10_3_3 13 || (next_10_3_3 14 || (next_10_3_3 15 || (next_10_3_3 16 || (next_10_3_3 17 || (next_10_3_3 18 || (next_10_3_3 19 || (next_10_3_3 20 || false))))))))))))))))))))) = false
  rw [d_10_3_3_0, d_10_3_3_1, d_10_3_3_2, d_10_3_3_3, d_10_3_3_4, d_10_3_3_5, d_10_3_3_6, d_10_3_3_7, d_10_3_3_8, d_10_3_3_9, d_10_3_3_10, d_10_3_3_11, d_10_3_3_12, d_10_3_3_13, d_10_3_3_14, d_10_3_3_15, d_10_3_3_16, d_10_3_3_17, d_10_3_3_18, d_10_3_3_19, d_10_3_3_20] <;> rfl
theorem b_10_3_3 : branch 10 3 3 = false := branch_lift 10 3 3 0 state_10_3_3 (by decide +kernel) state_ok_10_3_3
theorem c_10_3 : lane 10 3 = false := branch_join 10 3 b_10_3_0 b_10_3_1 b_10_3_2 b_10_3_3
theorem checked_10 : firstGate 10 = false := lanes_join 10 c_10_0 c_10_1 c_10_2 c_10_3
theorem b_11_0_0 : branch 11 0 0 = false := by decide +kernel
theorem b_11_0_1 : branch 11 0 1 = false := by decide +kernel
theorem b_11_0_2 : branch 11 0 2 = false := by decide +kernel
def state_11_0_3 : List W := [881711569270030336, 881712051380150656, 1152920955840713728, 560697862707653233, 809071576521218071, 17874208644006378, 1134907655299531261]
def next_11_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_11_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_11_0_3_0 : next_11_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_1 : next_11_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_2 : next_11_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_3 : next_11_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_4 : next_11_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_5 : next_11_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_6 : next_11_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_7 : next_11_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_8 : next_11_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_9 : next_11_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_10 : next_11_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_11 : next_11_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_12 : next_11_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_13 : next_11_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_14 : next_11_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_15 : next_11_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_16 : next_11_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_17 : next_11_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_18 : next_11_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_19 : next_11_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_0_3_20 : next_11_0_3 20 = false := by decide +kernel
theorem state_ok_11_0_3 : optimized 6 0 state_11_0_3 = false := by
  change ((state_11_0_3 == [goal] || state_11_0_3 == [~~~goal]) || _) = false
  rw [show (state_11_0_3 == [goal] || state_11_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_11_0_3 0 || (next_11_0_3 1 || (next_11_0_3 2 || (next_11_0_3 3 || (next_11_0_3 4 || (next_11_0_3 5 || (next_11_0_3 6 || (next_11_0_3 7 || (next_11_0_3 8 || (next_11_0_3 9 || (next_11_0_3 10 || (next_11_0_3 11 || (next_11_0_3 12 || (next_11_0_3 13 || (next_11_0_3 14 || (next_11_0_3 15 || (next_11_0_3 16 || (next_11_0_3 17 || (next_11_0_3 18 || (next_11_0_3 19 || (next_11_0_3 20 || false))))))))))))))))))))) = false
  rw [d_11_0_3_0, d_11_0_3_1, d_11_0_3_2, d_11_0_3_3, d_11_0_3_4, d_11_0_3_5, d_11_0_3_6, d_11_0_3_7, d_11_0_3_8, d_11_0_3_9, d_11_0_3_10, d_11_0_3_11, d_11_0_3_12, d_11_0_3_13, d_11_0_3_14, d_11_0_3_15, d_11_0_3_16, d_11_0_3_17, d_11_0_3_18, d_11_0_3_19, d_11_0_3_20] <;> rfl
theorem b_11_0_3 : branch 11 0 3 = false := branch_lift 11 0 3 0 state_11_0_3 (by decide +kernel) state_ok_11_0_3
theorem c_11_0 : lane 11 0 = false := branch_join 11 0 b_11_0_0 b_11_0_1 b_11_0_2 b_11_0_3
theorem b_11_1_0 : branch 11 1 0 = false := by decide +kernel
theorem b_11_1_1 : branch 11 1 1 = false := by decide +kernel
theorem b_11_1_2 : branch 11 1 2 = false := by decide +kernel
def state_11_1_3 : List W := [1152921437950834048, 881712051380150656, 1152920955840713728, 560697862707653233, 809071576521218071, 17874208644006378, 1134907655299531261]
def next_11_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_11_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_11_1_3_0 : next_11_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_1 : next_11_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_2 : next_11_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_3 : next_11_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_4 : next_11_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_5 : next_11_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_6 : next_11_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_7 : next_11_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_8 : next_11_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_9 : next_11_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_10 : next_11_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_11 : next_11_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_12 : next_11_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_13 : next_11_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_14 : next_11_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_15 : next_11_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_16 : next_11_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_17 : next_11_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_18 : next_11_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_19 : next_11_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_1_3_20 : next_11_1_3 20 = false := by decide +kernel
theorem state_ok_11_1_3 : optimized 6 0 state_11_1_3 = false := by
  change ((state_11_1_3 == [goal] || state_11_1_3 == [~~~goal]) || _) = false
  rw [show (state_11_1_3 == [goal] || state_11_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_11_1_3 0 || (next_11_1_3 1 || (next_11_1_3 2 || (next_11_1_3 3 || (next_11_1_3 4 || (next_11_1_3 5 || (next_11_1_3 6 || (next_11_1_3 7 || (next_11_1_3 8 || (next_11_1_3 9 || (next_11_1_3 10 || (next_11_1_3 11 || (next_11_1_3 12 || (next_11_1_3 13 || (next_11_1_3 14 || (next_11_1_3 15 || (next_11_1_3 16 || (next_11_1_3 17 || (next_11_1_3 18 || (next_11_1_3 19 || (next_11_1_3 20 || false))))))))))))))))))))) = false
  rw [d_11_1_3_0, d_11_1_3_1, d_11_1_3_2, d_11_1_3_3, d_11_1_3_4, d_11_1_3_5, d_11_1_3_6, d_11_1_3_7, d_11_1_3_8, d_11_1_3_9, d_11_1_3_10, d_11_1_3_11, d_11_1_3_12, d_11_1_3_13, d_11_1_3_14, d_11_1_3_15, d_11_1_3_16, d_11_1_3_17, d_11_1_3_18, d_11_1_3_19, d_11_1_3_20] <;> rfl
theorem b_11_1_3 : branch 11 1 3 = false := branch_lift 11 1 3 0 state_11_1_3 (by decide +kernel) state_ok_11_1_3
theorem c_11_1 : lane 11 1 = false := branch_join 11 1 b_11_1_0 b_11_1_1 b_11_1_2 b_11_1_3
theorem b_11_2_0 : branch 11 2 0 = false := by decide +kernel
theorem b_11_2_1 : branch 11 2 1 = false := by decide +kernel
theorem b_11_2_2 : branch 11 2 2 = false := by decide +kernel
def state_11_2_3 : List W := [482110120320, 881712051380150656, 1152920955840713728, 560697862707653233, 809071576521218071, 17874208644006378, 1134907655299531261]
def next_11_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_11_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_11_2_3_0 : next_11_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_1 : next_11_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_2 : next_11_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_3 : next_11_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_4 : next_11_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_5 : next_11_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_6 : next_11_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_7 : next_11_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_8 : next_11_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_9 : next_11_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_10 : next_11_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_11 : next_11_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_12 : next_11_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_13 : next_11_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_14 : next_11_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_15 : next_11_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_16 : next_11_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_17 : next_11_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_18 : next_11_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_19 : next_11_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_2_3_20 : next_11_2_3 20 = false := by decide +kernel
theorem state_ok_11_2_3 : optimized 6 0 state_11_2_3 = false := by
  change ((state_11_2_3 == [goal] || state_11_2_3 == [~~~goal]) || _) = false
  rw [show (state_11_2_3 == [goal] || state_11_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_11_2_3 0 || (next_11_2_3 1 || (next_11_2_3 2 || (next_11_2_3 3 || (next_11_2_3 4 || (next_11_2_3 5 || (next_11_2_3 6 || (next_11_2_3 7 || (next_11_2_3 8 || (next_11_2_3 9 || (next_11_2_3 10 || (next_11_2_3 11 || (next_11_2_3 12 || (next_11_2_3 13 || (next_11_2_3 14 || (next_11_2_3 15 || (next_11_2_3 16 || (next_11_2_3 17 || (next_11_2_3 18 || (next_11_2_3 19 || (next_11_2_3 20 || false))))))))))))))))))))) = false
  rw [d_11_2_3_0, d_11_2_3_1, d_11_2_3_2, d_11_2_3_3, d_11_2_3_4, d_11_2_3_5, d_11_2_3_6, d_11_2_3_7, d_11_2_3_8, d_11_2_3_9, d_11_2_3_10, d_11_2_3_11, d_11_2_3_12, d_11_2_3_13, d_11_2_3_14, d_11_2_3_15, d_11_2_3_16, d_11_2_3_17, d_11_2_3_18, d_11_2_3_19, d_11_2_3_20] <;> rfl
theorem b_11_2_3 : branch 11 2 3 = false := branch_lift 11 2 3 0 state_11_2_3 (by decide +kernel) state_ok_11_2_3
theorem c_11_2 : lane 11 2 = false := branch_join 11 2 b_11_2_0 b_11_2_1 b_11_2_2 b_11_2_3
theorem b_11_3_0 : branch 11 3 0 = false := by decide +kernel
theorem b_11_3_1 : branch 11 3 1 = false := by decide +kernel
theorem b_11_3_2 : branch 11 3 2 = false := by decide +kernel
def state_11_3_3 : List W := [271209386570683392, 881712051380150656, 1152920955840713728, 560697862707653233, 809071576521218071, 17874208644006378, 1134907655299531261]
def next_11_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_11_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_11_3_3_0 : next_11_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_1 : next_11_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_2 : next_11_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_3 : next_11_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_4 : next_11_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_5 : next_11_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_6 : next_11_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_7 : next_11_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_8 : next_11_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_9 : next_11_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_10 : next_11_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_11 : next_11_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_12 : next_11_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_13 : next_11_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_14 : next_11_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_15 : next_11_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_16 : next_11_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_17 : next_11_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_18 : next_11_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_19 : next_11_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_11_3_3_20 : next_11_3_3 20 = false := by decide +kernel
theorem state_ok_11_3_3 : optimized 6 0 state_11_3_3 = false := by
  change ((state_11_3_3 == [goal] || state_11_3_3 == [~~~goal]) || _) = false
  rw [show (state_11_3_3 == [goal] || state_11_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_11_3_3 0 || (next_11_3_3 1 || (next_11_3_3 2 || (next_11_3_3 3 || (next_11_3_3 4 || (next_11_3_3 5 || (next_11_3_3 6 || (next_11_3_3 7 || (next_11_3_3 8 || (next_11_3_3 9 || (next_11_3_3 10 || (next_11_3_3 11 || (next_11_3_3 12 || (next_11_3_3 13 || (next_11_3_3 14 || (next_11_3_3 15 || (next_11_3_3 16 || (next_11_3_3 17 || (next_11_3_3 18 || (next_11_3_3 19 || (next_11_3_3 20 || false))))))))))))))))))))) = false
  rw [d_11_3_3_0, d_11_3_3_1, d_11_3_3_2, d_11_3_3_3, d_11_3_3_4, d_11_3_3_5, d_11_3_3_6, d_11_3_3_7, d_11_3_3_8, d_11_3_3_9, d_11_3_3_10, d_11_3_3_11, d_11_3_3_12, d_11_3_3_13, d_11_3_3_14, d_11_3_3_15, d_11_3_3_16, d_11_3_3_17, d_11_3_3_18, d_11_3_3_19, d_11_3_3_20] <;> rfl
theorem b_11_3_3 : branch 11 3 3 = false := branch_lift 11 3 3 0 state_11_3_3 (by decide +kernel) state_ok_11_3_3
theorem c_11_3 : lane 11 3 = false := branch_join 11 3 b_11_3_0 b_11_3_1 b_11_3_2 b_11_3_3
theorem checked_11 : firstGate 11 = false := lanes_join 11 c_11_0 c_11_1 c_11_2 c_11_3
theorem b_12_0_0 : branch 12 0 0 = false := by decide +kernel
theorem b_12_0_1 : branch 12 0 1 = false := by decide +kernel
theorem b_12_0_2 : branch 12 0 2 = false := by decide +kernel
def state_12_0_3 : List W := [547608330728, 17874208644006378, 1134907655299531261, 560697862707653233, 809071576521218071, 881712051380150656, 1152920955840713728]
def next_12_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_12_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_12_0_3_0 : next_12_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_1 : next_12_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_2 : next_12_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_3 : next_12_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_4 : next_12_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_5 : next_12_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_6 : next_12_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_7 : next_12_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_8 : next_12_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_9 : next_12_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_10 : next_12_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_11 : next_12_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_12 : next_12_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_13 : next_12_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_14 : next_12_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_15 : next_12_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_16 : next_12_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_17 : next_12_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_18 : next_12_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_19 : next_12_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_0_3_20 : next_12_0_3 20 = false := by decide +kernel
theorem state_ok_12_0_3 : optimized 6 0 state_12_0_3 = false := by
  change ((state_12_0_3 == [goal] || state_12_0_3 == [~~~goal]) || _) = false
  rw [show (state_12_0_3 == [goal] || state_12_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_12_0_3 0 || (next_12_0_3 1 || (next_12_0_3 2 || (next_12_0_3 3 || (next_12_0_3 4 || (next_12_0_3 5 || (next_12_0_3 6 || (next_12_0_3 7 || (next_12_0_3 8 || (next_12_0_3 9 || (next_12_0_3 10 || (next_12_0_3 11 || (next_12_0_3 12 || (next_12_0_3 13 || (next_12_0_3 14 || (next_12_0_3 15 || (next_12_0_3 16 || (next_12_0_3 17 || (next_12_0_3 18 || (next_12_0_3 19 || (next_12_0_3 20 || false))))))))))))))))))))) = false
  rw [d_12_0_3_0, d_12_0_3_1, d_12_0_3_2, d_12_0_3_3, d_12_0_3_4, d_12_0_3_5, d_12_0_3_6, d_12_0_3_7, d_12_0_3_8, d_12_0_3_9, d_12_0_3_10, d_12_0_3_11, d_12_0_3_12, d_12_0_3_13, d_12_0_3_14, d_12_0_3_15, d_12_0_3_16, d_12_0_3_17, d_12_0_3_18, d_12_0_3_19, d_12_0_3_20] <;> rfl
theorem b_12_0_3 : branch 12 0 3 = false := branch_lift 12 0 3 0 state_12_0_3 (by decide +kernel) state_ok_12_0_3
theorem c_12_0 : lane 12 0 = false := branch_join 12 0 b_12_0_0 b_12_0_1 b_12_0_2 b_12_0_3
theorem b_12_1_0 : branch 12 1 0 = false := by decide +kernel
theorem b_12_1_1 : branch 12 1 1 = false := by decide +kernel
theorem b_12_1_2 : branch 12 1 2 = false := by decide +kernel
def state_12_1_3 : List W := [1152781316335206911, 17874208644006378, 1134907655299531261, 560697862707653233, 809071576521218071, 881712051380150656, 1152920955840713728]
def next_12_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_12_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_12_1_3_0 : next_12_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_1 : next_12_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_2 : next_12_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_3 : next_12_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_4 : next_12_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_5 : next_12_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_6 : next_12_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_7 : next_12_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_8 : next_12_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_9 : next_12_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_10 : next_12_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_11 : next_12_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_12 : next_12_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_13 : next_12_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_14 : next_12_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_15 : next_12_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_16 : next_12_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_17 : next_12_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_18 : next_12_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_19 : next_12_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_1_3_20 : next_12_1_3 20 = false := by decide +kernel
theorem state_ok_12_1_3 : optimized 6 0 state_12_1_3 = false := by
  change ((state_12_1_3 == [goal] || state_12_1_3 == [~~~goal]) || _) = false
  rw [show (state_12_1_3 == [goal] || state_12_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_12_1_3 0 || (next_12_1_3 1 || (next_12_1_3 2 || (next_12_1_3 3 || (next_12_1_3 4 || (next_12_1_3 5 || (next_12_1_3 6 || (next_12_1_3 7 || (next_12_1_3 8 || (next_12_1_3 9 || (next_12_1_3 10 || (next_12_1_3 11 || (next_12_1_3 12 || (next_12_1_3 13 || (next_12_1_3 14 || (next_12_1_3 15 || (next_12_1_3 16 || (next_12_1_3 17 || (next_12_1_3 18 || (next_12_1_3 19 || (next_12_1_3 20 || false))))))))))))))))))))) = false
  rw [d_12_1_3_0, d_12_1_3_1, d_12_1_3_2, d_12_1_3_3, d_12_1_3_4, d_12_1_3_5, d_12_1_3_6, d_12_1_3_7, d_12_1_3_8, d_12_1_3_9, d_12_1_3_10, d_12_1_3_11, d_12_1_3_12, d_12_1_3_13, d_12_1_3_14, d_12_1_3_15, d_12_1_3_16, d_12_1_3_17, d_12_1_3_18, d_12_1_3_19, d_12_1_3_20] <;> rfl
theorem b_12_1_3 : branch 12 1 3 = false := branch_lift 12 1 3 0 state_12_1_3 (by decide +kernel) state_ok_12_1_3
theorem c_12_1 : lane 12 1 = false := branch_join 12 1 b_12_1_0 b_12_1_1 b_12_1_2 b_12_1_3
theorem b_12_2_0 : branch 12 2 0 = false := by decide +kernel
theorem b_12_2_1 : branch 12 2 1 = false := by decide +kernel
theorem b_12_2_2 : branch 12 2 2 = false := by decide +kernel
def state_12_2_3 : List W := [17873661035675650, 17874208644006378, 1134907655299531261, 560697862707653233, 809071576521218071, 881712051380150656, 1152920955840713728]
def next_12_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_12_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_12_2_3_0 : next_12_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_1 : next_12_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_2 : next_12_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_3 : next_12_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_4 : next_12_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_5 : next_12_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_6 : next_12_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_7 : next_12_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_8 : next_12_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_9 : next_12_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_10 : next_12_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_11 : next_12_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_12 : next_12_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_13 : next_12_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_14 : next_12_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_15 : next_12_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_16 : next_12_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_17 : next_12_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_18 : next_12_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_19 : next_12_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_2_3_20 : next_12_2_3 20 = false := by decide +kernel
theorem state_ok_12_2_3 : optimized 6 0 state_12_2_3 = false := by
  change ((state_12_2_3 == [goal] || state_12_2_3 == [~~~goal]) || _) = false
  rw [show (state_12_2_3 == [goal] || state_12_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_12_2_3 0 || (next_12_2_3 1 || (next_12_2_3 2 || (next_12_2_3 3 || (next_12_2_3 4 || (next_12_2_3 5 || (next_12_2_3 6 || (next_12_2_3 7 || (next_12_2_3 8 || (next_12_2_3 9 || (next_12_2_3 10 || (next_12_2_3 11 || (next_12_2_3 12 || (next_12_2_3 13 || (next_12_2_3 14 || (next_12_2_3 15 || (next_12_2_3 16 || (next_12_2_3 17 || (next_12_2_3 18 || (next_12_2_3 19 || (next_12_2_3 20 || false))))))))))))))))))))) = false
  rw [d_12_2_3_0, d_12_2_3_1, d_12_2_3_2, d_12_2_3_3, d_12_2_3_4, d_12_2_3_5, d_12_2_3_6, d_12_2_3_7, d_12_2_3_8, d_12_2_3_9, d_12_2_3_10, d_12_2_3_11, d_12_2_3_12, d_12_2_3_13, d_12_2_3_14, d_12_2_3_15, d_12_2_3_16, d_12_2_3_17, d_12_2_3_18, d_12_2_3_19, d_12_2_3_20] <;> rfl
theorem b_12_2_3 : branch 12 2 3 = false := branch_lift 12 2 3 0 state_12_2_3 (by decide +kernel) state_ok_12_2_3
theorem c_12_2 : lane 12 2 = false := branch_join 12 2 b_12_2_0 b_12_2_1 b_12_2_2 b_12_2_3
theorem b_12_3_0 : branch 12 3 0 = false := by decide +kernel
theorem b_12_3_1 : branch 12 3 1 = false := by decide +kernel
theorem b_12_3_2 : branch 12 3 2 = false := by decide +kernel
def state_12_3_3 : List W := [1134907107691200533, 17874208644006378, 1134907655299531261, 560697862707653233, 809071576521218071, 881712051380150656, 1152920955840713728]
def next_12_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_12_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_12_3_3_0 : next_12_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_1 : next_12_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_2 : next_12_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_3 : next_12_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_4 : next_12_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_5 : next_12_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_6 : next_12_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_7 : next_12_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_8 : next_12_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_9 : next_12_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_10 : next_12_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_11 : next_12_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_12 : next_12_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_13 : next_12_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_14 : next_12_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_15 : next_12_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_16 : next_12_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_17 : next_12_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_18 : next_12_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_19 : next_12_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_12_3_3_20 : next_12_3_3 20 = false := by decide +kernel
theorem state_ok_12_3_3 : optimized 6 0 state_12_3_3 = false := by
  change ((state_12_3_3 == [goal] || state_12_3_3 == [~~~goal]) || _) = false
  rw [show (state_12_3_3 == [goal] || state_12_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_12_3_3 0 || (next_12_3_3 1 || (next_12_3_3 2 || (next_12_3_3 3 || (next_12_3_3 4 || (next_12_3_3 5 || (next_12_3_3 6 || (next_12_3_3 7 || (next_12_3_3 8 || (next_12_3_3 9 || (next_12_3_3 10 || (next_12_3_3 11 || (next_12_3_3 12 || (next_12_3_3 13 || (next_12_3_3 14 || (next_12_3_3 15 || (next_12_3_3 16 || (next_12_3_3 17 || (next_12_3_3 18 || (next_12_3_3 19 || (next_12_3_3 20 || false))))))))))))))))))))) = false
  rw [d_12_3_3_0, d_12_3_3_1, d_12_3_3_2, d_12_3_3_3, d_12_3_3_4, d_12_3_3_5, d_12_3_3_6, d_12_3_3_7, d_12_3_3_8, d_12_3_3_9, d_12_3_3_10, d_12_3_3_11, d_12_3_3_12, d_12_3_3_13, d_12_3_3_14, d_12_3_3_15, d_12_3_3_16, d_12_3_3_17, d_12_3_3_18, d_12_3_3_19, d_12_3_3_20] <;> rfl
theorem b_12_3_3 : branch 12 3 3 = false := branch_lift 12 3 3 0 state_12_3_3 (by decide +kernel) state_ok_12_3_3
theorem c_12_3 : lane 12 3 = false := branch_join 12 3 b_12_3_0 b_12_3_1 b_12_3_2 b_12_3_3
theorem checked_12 : firstGate 12 = false := lanes_join 12 c_12_0 c_12_1 c_12_2 c_12_3
theorem b_13_0_0 : branch 13 0 0 = false := by decide +kernel
theorem b_13_0_1 : branch 13 0 1 = false := by decide +kernel
theorem b_13_0_2 : branch 13 0 2 = false := by decide +kernel
def state_13_0_3 : List W := [17873661035544576, 17874208644006378, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 1134907655299531261]
def next_13_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_13_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_13_0_3_0 : next_13_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_1 : next_13_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_2 : next_13_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_3 : next_13_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_4 : next_13_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_5 : next_13_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_6 : next_13_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_7 : next_13_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_8 : next_13_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_9 : next_13_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_10 : next_13_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_11 : next_13_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_12 : next_13_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_13 : next_13_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_14 : next_13_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_15 : next_13_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_16 : next_13_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_17 : next_13_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_18 : next_13_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_19 : next_13_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_0_3_20 : next_13_0_3 20 = false := by decide +kernel
theorem state_ok_13_0_3 : optimized 6 0 state_13_0_3 = false := by
  change ((state_13_0_3 == [goal] || state_13_0_3 == [~~~goal]) || _) = false
  rw [show (state_13_0_3 == [goal] || state_13_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_13_0_3 0 || (next_13_0_3 1 || (next_13_0_3 2 || (next_13_0_3 3 || (next_13_0_3 4 || (next_13_0_3 5 || (next_13_0_3 6 || (next_13_0_3 7 || (next_13_0_3 8 || (next_13_0_3 9 || (next_13_0_3 10 || (next_13_0_3 11 || (next_13_0_3 12 || (next_13_0_3 13 || (next_13_0_3 14 || (next_13_0_3 15 || (next_13_0_3 16 || (next_13_0_3 17 || (next_13_0_3 18 || (next_13_0_3 19 || (next_13_0_3 20 || false))))))))))))))))))))) = false
  rw [d_13_0_3_0, d_13_0_3_1, d_13_0_3_2, d_13_0_3_3, d_13_0_3_4, d_13_0_3_5, d_13_0_3_6, d_13_0_3_7, d_13_0_3_8, d_13_0_3_9, d_13_0_3_10, d_13_0_3_11, d_13_0_3_12, d_13_0_3_13, d_13_0_3_14, d_13_0_3_15, d_13_0_3_16, d_13_0_3_17, d_13_0_3_18, d_13_0_3_19, d_13_0_3_20] <;> rfl
theorem b_13_0_3 : branch 13 0 3 = false := branch_lift 13 0 3 0 state_13_0_3 (by decide +kernel) state_ok_13_0_3
theorem c_13_0 : lane 13 0 = false := branch_join 13 0 b_13_0_0 b_13_0_1 b_13_0_2 b_13_0_3
theorem b_13_1_0 : branch 13 1 0 = false := by decide +kernel
theorem b_13_1_1 : branch 13 1 1 = false := by decide +kernel
theorem b_13_1_2 : branch 13 1 2 = false := by decide +kernel
def state_13_1_3 : List W := [1152921503449175530, 17874208644006378, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 1134907655299531261]
def next_13_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_13_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_13_1_3_0 : next_13_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_1 : next_13_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_2 : next_13_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_3 : next_13_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_4 : next_13_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_5 : next_13_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_6 : next_13_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_7 : next_13_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_8 : next_13_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_9 : next_13_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_10 : next_13_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_11 : next_13_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_12 : next_13_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_13 : next_13_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_14 : next_13_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_15 : next_13_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_16 : next_13_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_17 : next_13_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_18 : next_13_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_19 : next_13_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_1_3_20 : next_13_1_3 20 = false := by decide +kernel
theorem state_ok_13_1_3 : optimized 6 0 state_13_1_3 = false := by
  change ((state_13_1_3 == [goal] || state_13_1_3 == [~~~goal]) || _) = false
  rw [show (state_13_1_3 == [goal] || state_13_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_13_1_3 0 || (next_13_1_3 1 || (next_13_1_3 2 || (next_13_1_3 3 || (next_13_1_3 4 || (next_13_1_3 5 || (next_13_1_3 6 || (next_13_1_3 7 || (next_13_1_3 8 || (next_13_1_3 9 || (next_13_1_3 10 || (next_13_1_3 11 || (next_13_1_3 12 || (next_13_1_3 13 || (next_13_1_3 14 || (next_13_1_3 15 || (next_13_1_3 16 || (next_13_1_3 17 || (next_13_1_3 18 || (next_13_1_3 19 || (next_13_1_3 20 || false))))))))))))))))))))) = false
  rw [d_13_1_3_0, d_13_1_3_1, d_13_1_3_2, d_13_1_3_3, d_13_1_3_4, d_13_1_3_5, d_13_1_3_6, d_13_1_3_7, d_13_1_3_8, d_13_1_3_9, d_13_1_3_10, d_13_1_3_11, d_13_1_3_12, d_13_1_3_13, d_13_1_3_14, d_13_1_3_15, d_13_1_3_16, d_13_1_3_17, d_13_1_3_18, d_13_1_3_19, d_13_1_3_20] <;> rfl
theorem b_13_1_3 : branch 13 1 3 = false := branch_lift 13 1 3 0 state_13_1_3 (by decide +kernel) state_ok_13_1_3
theorem c_13_1 : lane 13 1 = false := branch_join 13 1 b_13_1_0 b_13_1_1 b_13_1_2 b_13_1_3
theorem b_13_2_0 : branch 13 2 0 = false := by decide +kernel
theorem b_13_2_1 : branch 13 2 1 = false := by decide +kernel
theorem b_13_2_2 : branch 13 2 2 = false := by decide +kernel
def state_13_2_3 : List W := [547608461802, 17874208644006378, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 1134907655299531261]
def next_13_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_13_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_13_2_3_0 : next_13_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_1 : next_13_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_2 : next_13_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_3 : next_13_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_4 : next_13_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_5 : next_13_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_6 : next_13_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_7 : next_13_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_8 : next_13_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_9 : next_13_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_10 : next_13_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_11 : next_13_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_12 : next_13_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_13 : next_13_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_14 : next_13_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_15 : next_13_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_16 : next_13_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_17 : next_13_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_18 : next_13_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_19 : next_13_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_2_3_20 : next_13_2_3 20 = false := by decide +kernel
theorem state_ok_13_2_3 : optimized 6 0 state_13_2_3 = false := by
  change ((state_13_2_3 == [goal] || state_13_2_3 == [~~~goal]) || _) = false
  rw [show (state_13_2_3 == [goal] || state_13_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_13_2_3 0 || (next_13_2_3 1 || (next_13_2_3 2 || (next_13_2_3 3 || (next_13_2_3 4 || (next_13_2_3 5 || (next_13_2_3 6 || (next_13_2_3 7 || (next_13_2_3 8 || (next_13_2_3 9 || (next_13_2_3 10 || (next_13_2_3 11 || (next_13_2_3 12 || (next_13_2_3 13 || (next_13_2_3 14 || (next_13_2_3 15 || (next_13_2_3 16 || (next_13_2_3 17 || (next_13_2_3 18 || (next_13_2_3 19 || (next_13_2_3 20 || false))))))))))))))))))))) = false
  rw [d_13_2_3_0, d_13_2_3_1, d_13_2_3_2, d_13_2_3_3, d_13_2_3_4, d_13_2_3_5, d_13_2_3_6, d_13_2_3_7, d_13_2_3_8, d_13_2_3_9, d_13_2_3_10, d_13_2_3_11, d_13_2_3_12, d_13_2_3_13, d_13_2_3_14, d_13_2_3_15, d_13_2_3_16, d_13_2_3_17, d_13_2_3_18, d_13_2_3_19, d_13_2_3_20] <;> rfl
theorem b_13_2_3 : branch 13 2 3 = false := branch_lift 13 2 3 0 state_13_2_3 (by decide +kernel) state_ok_13_2_3
theorem c_13_2 : lane 13 2 = false := branch_join 13 2 b_13_2_0 b_13_2_1 b_13_2_2 b_13_2_3
theorem b_13_3_0 : branch 13 3 0 = false := by decide +kernel
theorem b_13_3_1 : branch 13 3 1 = false := by decide +kernel
theorem b_13_3_2 : branch 13 3 2 = false := by decide +kernel
def state_13_3_3 : List W := [1135047294805169152, 17874208644006378, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 1134907655299531261]
def next_13_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_13_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_13_3_3_0 : next_13_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_1 : next_13_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_2 : next_13_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_3 : next_13_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_4 : next_13_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_5 : next_13_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_6 : next_13_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_7 : next_13_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_8 : next_13_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_9 : next_13_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_10 : next_13_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_11 : next_13_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_12 : next_13_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_13 : next_13_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_14 : next_13_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_15 : next_13_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_16 : next_13_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_17 : next_13_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_18 : next_13_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_19 : next_13_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_13_3_3_20 : next_13_3_3 20 = false := by decide +kernel
theorem state_ok_13_3_3 : optimized 6 0 state_13_3_3 = false := by
  change ((state_13_3_3 == [goal] || state_13_3_3 == [~~~goal]) || _) = false
  rw [show (state_13_3_3 == [goal] || state_13_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_13_3_3 0 || (next_13_3_3 1 || (next_13_3_3 2 || (next_13_3_3 3 || (next_13_3_3 4 || (next_13_3_3 5 || (next_13_3_3 6 || (next_13_3_3 7 || (next_13_3_3 8 || (next_13_3_3 9 || (next_13_3_3 10 || (next_13_3_3 11 || (next_13_3_3 12 || (next_13_3_3 13 || (next_13_3_3 14 || (next_13_3_3 15 || (next_13_3_3 16 || (next_13_3_3 17 || (next_13_3_3 18 || (next_13_3_3 19 || (next_13_3_3 20 || false))))))))))))))))))))) = false
  rw [d_13_3_3_0, d_13_3_3_1, d_13_3_3_2, d_13_3_3_3, d_13_3_3_4, d_13_3_3_5, d_13_3_3_6, d_13_3_3_7, d_13_3_3_8, d_13_3_3_9, d_13_3_3_10, d_13_3_3_11, d_13_3_3_12, d_13_3_3_13, d_13_3_3_14, d_13_3_3_15, d_13_3_3_16, d_13_3_3_17, d_13_3_3_18, d_13_3_3_19, d_13_3_3_20] <;> rfl
theorem b_13_3_3 : branch 13 3 3 = false := branch_lift 13 3 3 0 state_13_3_3 (by decide +kernel) state_ok_13_3_3
theorem c_13_3 : lane 13 3 = false := branch_join 13 3 b_13_3_0 b_13_3_1 b_13_3_2 b_13_3_3
theorem checked_13 : firstGate 13 = false := lanes_join 13 c_13_0 c_13_1 c_13_2 c_13_3
theorem b_14_0_0 : branch 14 0 0 = false := by decide +kernel
theorem b_14_0_1 : branch 14 0 1 = false := by decide +kernel
theorem b_14_0_2 : branch 14 0 2 = false := by decide +kernel
def state_14_0_3 : List W := [1134907106533572608, 1134907655299531261, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378]
def next_14_0_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_14_0_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_14_0_3_0 : next_14_0_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_1 : next_14_0_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_2 : next_14_0_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_3 : next_14_0_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_4 : next_14_0_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_5 : next_14_0_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_6 : next_14_0_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_7 : next_14_0_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_8 : next_14_0_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_9 : next_14_0_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_10 : next_14_0_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_11 : next_14_0_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_12 : next_14_0_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_13 : next_14_0_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_14 : next_14_0_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_15 : next_14_0_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_16 : next_14_0_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_17 : next_14_0_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_18 : next_14_0_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_19 : next_14_0_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_0_3_20 : next_14_0_3 20 = false := by decide +kernel
theorem state_ok_14_0_3 : optimized 6 0 state_14_0_3 = false := by
  change ((state_14_0_3 == [goal] || state_14_0_3 == [~~~goal]) || _) = false
  rw [show (state_14_0_3 == [goal] || state_14_0_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_14_0_3 0 || (next_14_0_3 1 || (next_14_0_3 2 || (next_14_0_3 3 || (next_14_0_3 4 || (next_14_0_3 5 || (next_14_0_3 6 || (next_14_0_3 7 || (next_14_0_3 8 || (next_14_0_3 9 || (next_14_0_3 10 || (next_14_0_3 11 || (next_14_0_3 12 || (next_14_0_3 13 || (next_14_0_3 14 || (next_14_0_3 15 || (next_14_0_3 16 || (next_14_0_3 17 || (next_14_0_3 18 || (next_14_0_3 19 || (next_14_0_3 20 || false))))))))))))))))))))) = false
  rw [d_14_0_3_0, d_14_0_3_1, d_14_0_3_2, d_14_0_3_3, d_14_0_3_4, d_14_0_3_5, d_14_0_3_6, d_14_0_3_7, d_14_0_3_8, d_14_0_3_9, d_14_0_3_10, d_14_0_3_11, d_14_0_3_12, d_14_0_3_13, d_14_0_3_14, d_14_0_3_15, d_14_0_3_16, d_14_0_3_17, d_14_0_3_18, d_14_0_3_19, d_14_0_3_20] <;> rfl
theorem b_14_0_3 : branch 14 0 3 = false := branch_lift 14 0 3 0 state_14_0_3 (by decide +kernel) state_ok_14_0_3
theorem c_14_0 : lane 14 0 = false := branch_join 14 0 b_14_0_0 b_14_0_1 b_14_0_2 b_14_0_3
theorem b_14_1_0 : branch 14 1 0 = false := by decide +kernel
theorem b_14_1_1 : branch 14 1 1 = false := by decide +kernel
theorem b_14_1_2 : branch 14 1 2 = false := by decide +kernel
def state_14_1_3 : List W := [1152921504606672381, 1134907655299531261, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378]
def next_14_1_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_14_1_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_14_1_3_0 : next_14_1_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_1 : next_14_1_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_2 : next_14_1_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_3 : next_14_1_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_4 : next_14_1_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_5 : next_14_1_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_6 : next_14_1_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_7 : next_14_1_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_8 : next_14_1_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_9 : next_14_1_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_10 : next_14_1_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_11 : next_14_1_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_12 : next_14_1_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_13 : next_14_1_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_14 : next_14_1_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_15 : next_14_1_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_16 : next_14_1_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_17 : next_14_1_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_18 : next_14_1_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_19 : next_14_1_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_1_3_20 : next_14_1_3 20 = false := by decide +kernel
theorem state_ok_14_1_3 : optimized 6 0 state_14_1_3 = false := by
  change ((state_14_1_3 == [goal] || state_14_1_3 == [~~~goal]) || _) = false
  rw [show (state_14_1_3 == [goal] || state_14_1_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_14_1_3 0 || (next_14_1_3 1 || (next_14_1_3 2 || (next_14_1_3 3 || (next_14_1_3 4 || (next_14_1_3 5 || (next_14_1_3 6 || (next_14_1_3 7 || (next_14_1_3 8 || (next_14_1_3 9 || (next_14_1_3 10 || (next_14_1_3 11 || (next_14_1_3 12 || (next_14_1_3 13 || (next_14_1_3 14 || (next_14_1_3 15 || (next_14_1_3 16 || (next_14_1_3 17 || (next_14_1_3 18 || (next_14_1_3 19 || (next_14_1_3 20 || false))))))))))))))))))))) = false
  rw [d_14_1_3_0, d_14_1_3_1, d_14_1_3_2, d_14_1_3_3, d_14_1_3_4, d_14_1_3_5, d_14_1_3_6, d_14_1_3_7, d_14_1_3_8, d_14_1_3_9, d_14_1_3_10, d_14_1_3_11, d_14_1_3_12, d_14_1_3_13, d_14_1_3_14, d_14_1_3_15, d_14_1_3_16, d_14_1_3_17, d_14_1_3_18, d_14_1_3_19, d_14_1_3_20] <;> rfl
theorem b_14_1_3 : branch 14 1 3 = false := branch_lift 14 1 3 0 state_14_1_3 (by decide +kernel) state_ok_14_1_3
theorem c_14_1 : lane 14 1 = false := branch_join 14 1 b_14_1_0 b_14_1_1 b_14_1_2 b_14_1_3
theorem b_14_2_0 : branch 14 2 0 = false := by decide +kernel
theorem b_14_2_1 : branch 14 2 1 = false := by decide +kernel
theorem b_14_2_2 : branch 14 2 2 = false := by decide +kernel
def state_14_2_3 : List W := [548765958653, 1134907655299531261, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378]
def next_14_2_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_14_2_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_14_2_3_0 : next_14_2_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_1 : next_14_2_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_2 : next_14_2_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_3 : next_14_2_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_4 : next_14_2_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_5 : next_14_2_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_6 : next_14_2_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_7 : next_14_2_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_8 : next_14_2_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_9 : next_14_2_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_10 : next_14_2_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_11 : next_14_2_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_12 : next_14_2_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_13 : next_14_2_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_14 : next_14_2_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_15 : next_14_2_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_16 : next_14_2_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_17 : next_14_2_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_18 : next_14_2_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_19 : next_14_2_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_2_3_20 : next_14_2_3 20 = false := by decide +kernel
theorem state_ok_14_2_3 : optimized 6 0 state_14_2_3 = false := by
  change ((state_14_2_3 == [goal] || state_14_2_3 == [~~~goal]) || _) = false
  rw [show (state_14_2_3 == [goal] || state_14_2_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_14_2_3 0 || (next_14_2_3 1 || (next_14_2_3 2 || (next_14_2_3 3 || (next_14_2_3 4 || (next_14_2_3 5 || (next_14_2_3 6 || (next_14_2_3 7 || (next_14_2_3 8 || (next_14_2_3 9 || (next_14_2_3 10 || (next_14_2_3 11 || (next_14_2_3 12 || (next_14_2_3 13 || (next_14_2_3 14 || (next_14_2_3 15 || (next_14_2_3 16 || (next_14_2_3 17 || (next_14_2_3 18 || (next_14_2_3 19 || (next_14_2_3 20 || false))))))))))))))))))))) = false
  rw [d_14_2_3_0, d_14_2_3_1, d_14_2_3_2, d_14_2_3_3, d_14_2_3_4, d_14_2_3_5, d_14_2_3_6, d_14_2_3_7, d_14_2_3_8, d_14_2_3_9, d_14_2_3_10, d_14_2_3_11, d_14_2_3_12, d_14_2_3_13, d_14_2_3_14, d_14_2_3_15, d_14_2_3_16, d_14_2_3_17, d_14_2_3_18, d_14_2_3_19, d_14_2_3_20] <;> rfl
theorem b_14_2_3 : branch 14 2 3 = false := branch_lift 14 2 3 0 state_14_2_3 (by decide +kernel) state_ok_14_2_3
theorem c_14_2 : lane 14 2 = false := branch_join 14 2 b_14_2_0 b_14_2_1 b_14_2_2 b_14_2_3
theorem b_14_3_0 : branch 14 3 0 = false := by decide +kernel
theorem b_14_3_1 : branch 14 3 1 = false := by decide +kernel
theorem b_14_3_2 : branch 14 3 2 = false := by decide +kernel
def state_14_3_3 : List W := [18013849307141120, 1134907655299531261, 1152920955840713728, 560697862707653233, 809071576521218071, 881712051380150656, 17874208644006378]
def next_14_3_3 (idx : Nat) : Bool :=
  let (a, b, r) := (pairs state_14_3_3).getD idx (0, 0, [])
  dispatch 0 (optimized 5) a b r
set_option maxHeartbeats 0 in theorem d_14_3_3_0 : next_14_3_3 0 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_1 : next_14_3_3 1 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_2 : next_14_3_3 2 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_3 : next_14_3_3 3 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_4 : next_14_3_3 4 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_5 : next_14_3_3 5 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_6 : next_14_3_3 6 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_7 : next_14_3_3 7 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_8 : next_14_3_3 8 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_9 : next_14_3_3 9 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_10 : next_14_3_3 10 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_11 : next_14_3_3 11 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_12 : next_14_3_3 12 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_13 : next_14_3_3 13 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_14 : next_14_3_3 14 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_15 : next_14_3_3 15 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_16 : next_14_3_3 16 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_17 : next_14_3_3 17 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_18 : next_14_3_3 18 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_19 : next_14_3_3 19 = false := by decide +kernel
set_option maxHeartbeats 0 in theorem d_14_3_3_20 : next_14_3_3 20 = false := by decide +kernel
theorem state_ok_14_3_3 : optimized 6 0 state_14_3_3 = false := by
  change ((state_14_3_3 == [goal] || state_14_3_3 == [~~~goal]) || _) = false
  rw [show (state_14_3_3 == [goal] || state_14_3_3 == [~~~goal]) = false by decide, Bool.false_or]
  change (next_14_3_3 0 || (next_14_3_3 1 || (next_14_3_3 2 || (next_14_3_3 3 || (next_14_3_3 4 || (next_14_3_3 5 || (next_14_3_3 6 || (next_14_3_3 7 || (next_14_3_3 8 || (next_14_3_3 9 || (next_14_3_3 10 || (next_14_3_3 11 || (next_14_3_3 12 || (next_14_3_3 13 || (next_14_3_3 14 || (next_14_3_3 15 || (next_14_3_3 16 || (next_14_3_3 17 || (next_14_3_3 18 || (next_14_3_3 19 || (next_14_3_3 20 || false))))))))))))))))))))) = false
  rw [d_14_3_3_0, d_14_3_3_1, d_14_3_3_2, d_14_3_3_3, d_14_3_3_4, d_14_3_3_5, d_14_3_3_6, d_14_3_3_7, d_14_3_3_8, d_14_3_3_9, d_14_3_3_10, d_14_3_3_11, d_14_3_3_12, d_14_3_3_13, d_14_3_3_14, d_14_3_3_15, d_14_3_3_16, d_14_3_3_17, d_14_3_3_18, d_14_3_3_19, d_14_3_3_20] <;> rfl
theorem b_14_3_3 : branch 14 3 3 = false := branch_lift 14 3 3 0 state_14_3_3 (by decide +kernel) state_ok_14_3_3
theorem c_14_3 : lane 14 3 = false := branch_join 14 3 b_14_3_0 b_14_3_1 b_14_3_2 b_14_3_3
theorem checked_14 : firstGate 14 = false := lanes_join 14 c_14_0 c_14_1 c_14_2 c_14_3

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem noSmall : search 7 ins = false := by
  have full : ∀ w ∈ ins.sublists, cuts w = -1 → w = ins := by decide +kernel
  have root : optimized 7 2 ins = false := by
    change ((ins == [goal] || ins == [~~~goal]) || _) = false
    rw [show (ins == [goal] || ins == [~~~goal]) = false by decide, Bool.false_or]
    change (firstGate 0 || (firstGate 1 || (firstGate 2 || (firstGate 3 || (firstGate 4 || (firstGate 5 || (firstGate 6 || (firstGate 7 || (firstGate 8 || (firstGate 9 || (firstGate 10 || (firstGate 11 || (firstGate 12 || (firstGate 13 || (firstGate 14 || false))))))))))))))) = false
    rw [checked_0, checked_1, checked_2, checked_3, checked_4, checked_5, checked_6, checked_7, checked_8, checked_9, checked_10, checked_11, checked_12, checked_13, checked_14]
    all_goals rfl
  apply List.any_eq_false.mpr
  intro w hw hyes
  simp only [Bool.and_eq_true, beq_iff_eq] at hyes
  obtain ⟨⟨_, hc⟩, hop⟩ := hyes
  obtain rfl := full w hw hc
  exact Bool.noConfusion (root.symm.trans hop)


def table (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4008372906 * 2 ^ 32 + 3974162432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem sample : ∀ j : Fin 60, table (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val] := by
  decide +kernel

theorem manyBinary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = table x) :
    7 < binaryCost gs := by
  by_contra! low
  have evaluate (k : Fin 60) : (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    have same : List.ofFn (fun i : Fin 6 => bit k (ins.getD i.val 0)) = ins.map (bit k) := by
      apply List.ext_getElem (by simp [ins])
      intro i hi hj
      have hlt : i < ins.length := by simpa using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg ins ins.toFinset
    (fun u hu => .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)) evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) :
      build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.false_ne_true
    (noSmall.symm.trans (search_complete ht 7 ins (by decide +kernel) (lift low run)))

def witness : Circuit := ⟨[⟨.or, [0, 4]⟩, ⟨.and, [6, 3]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [8, 2]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 1]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [12, 0]⟩, ⟨.or, [13, 11]⟩], 14⟩

theorem witnessEval : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) = table x := by
  decide +kernel

theorem monotone_replacement (s : ℕ) (C : Circuit) (hC : MetaComplexity.FanInTwo C)
    (hs : C.size ≤ s) (he : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = table x) :
    ∃ D : Circuit, MetaComplexity.Monotone2 D ∧ D.size ≤ s ∧
      ∀ x : Fin 6 → Bool, D.eval (List.ofFn x) = table x := by
  by_cases present : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, hn⟩ := present
    have cut : binaryCost C.gates < C.size :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, hm, by simp [isBinary, hn]⟩
    have many := manyBinary C.gates C.output hC he
    exact ⟨witness, by simp [MetaComplexity.Monotone2, witness], by change 9 ≤ s; omega, witnessEval⟩
  · exact ⟨C, fun g hg => ⟨(hC g hg).1.imp_right (·.resolve_right fun h => present ⟨g, hg, h⟩),
      (hC g hg).2⟩, hs, he⟩

end PEqualNP.Outside.L_meta_36593

theorem PEqualNP.Outside.L_meta_36593 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372906 * 2 ^ 32 + 3974162432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372906 * 2 ^ 32 + 3974162432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))     := by
  intro s ⟨C, hC, hs, he⟩
  exact PEqualNP.Outside.L_meta_36593.monotone_replacement s C hC hs he
