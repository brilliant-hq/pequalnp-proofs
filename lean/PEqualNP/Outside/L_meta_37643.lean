import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37643

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

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
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

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
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
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
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

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

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
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

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
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
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
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

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
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
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

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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

set_option maxRecDepth 5000 in
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
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
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

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276813032 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x0083121b030ac782#64 ++ 0x10041890d818563c#64 ++ 0xc19f123f071fcf95#64 ++ 0xee0cf891f838fe7c#64 : BitVec 256),
   (0x022806c5096650a8#64 ++ 0xa0114036284b3285#64 ++ 0xc6681fc719e671ef#64 ++ 0xde3340fe38cf338f#64 : BitVec 256),
   (0x2850636861b87a10#64 ++ 0xc142831b430dc3d0#64 ++ 0x7871e3f8e1f87e1f#64 ++ 0xbbc38f1fc70fc3f0#64 : BitVec 256),
   (0x1581b800b6002d43#64 ++ 0x00ac0dc005b0016a#64 ++ 0xbf81fc00fe007fff#64 ++ 0x7dfc0fe007f003ff#64 : BitVec 256),
   (0x1f7c0000dcd5001c#64 ++ 0x00fbe00006e6a800#64 ++ 0xbffe0000ffff801c#64 ++ 0xfdfff00007fffc00#64 : BitVec 256),
   (0x5fffddb600000000#64 ++ 0x02fffeedb0000000#64 ++ 0x5fffffff00000003#64 ++ 0xfafffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [1, 12]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000002000502 0x0000000000100028 0x8000000006004f94 0x040000000030027c

def z1 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f123f071fcf95 0xee0cf891f838fe7c

def z2 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6681fc719e671ef 0xde3340fe38cf338f

def z3 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81fc00fe007fff 0x7dfc0fe007f003ff

def z4 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe0000ffff801c 0xfdfff00007fffc00

def z5 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f87e1f 0xbbc38f1fc70fc3f0

def z6 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff00000003 0xfafffffff8000000

def z7 : W := mkw 0x5f7ccda400000000 0x02fbe66d20000000 0x1e60edc000000002 0x10f3076e00000000

def z8 : W := mkw 0x5ffffdb6b6002d43 0x02ffffedb5b0016a 0xfffffffffe007fff 0xfffffffffff003ff

def z9 : W := mkw 0x0228000008440008 0x0011400000422000 0x8668000019e6000c 0xdc33400000cf3000

def z10 : W := mkw 0x5fffddb608440008 0x02fffeedb0422000 0xdfffffff19e6000f 0xfefffffff8cf3000

def z11 : W := mkw 0x1f7c0485dcd700bc 0x20fbe0242ee6b805 0xbffe1c07ffff81fc 0xfdfff0e03ffffc0f

def z12 : W := mkw 0x1d540000d4910014 0x00eaa00006a48800 0x39960000e6198010 0x21ccb0000730cc00

def z13 : W := mkw 0x42abddb600000000 0x02155eedb0000000 0x4669ffff00000003 0xda334ffff8000000

def z14 : W := mkw 0x1500000094000000 0x00a8000004a00000 0xbf800000fe00001c 0x7dfc000007f00000

def z15 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xffffffffffff801f 0xfffffffffffffc00

def z16 : W := mkw 0x0850000040900010 0x0042800002048000 0x38700000e1f8001c 0xb9c38000070fc000

def z17 : W := mkw 0x0083121bdfdfc79e 0x10041890defefe3c 0xe19f123fffffcf9d 0xef0cf891fffffe7c

def z18 : W := mkw 0x0850412000000000 0x0042820900000000 0x5871e3f800000003 0xbac38f1fc0000000

def z19 : W := mkw 0x57af9c9600000000 0x02bd7ce4b0000000 0x078e1c0700000000 0x403c70e038000000

def z20 : W := mkw 0x02ab149600000000 0x001558a4b0000000 0x47ff1fff00000003 0xfa3ff8fff8000000

def z21 : W := mkw 0x0083101a02088702 0x10041880d0104438 0x0197003806198e10 0x200cb801c030cc70

def z22 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4001ffff00000003 0x02000ffff8000000

def z23 : W := mkw 0x0002021b010ac280 0x10001010d8085614 0x401e023f011f8000 0x8200f011f808fc00

def z24 : W := mkw 0x1fff121bdfdfc79e 0x10fff890defefe3c 0xffff123fffffcf9d 0xfffff891fffffe7c

def z25 : W := mkw 0x0000024001205000 0x8000001200090280 0x406003c001e0700f 0x9a03001e000f0380

def z26 : W := mkw 0x2a7867ed69fe7ab8 0xe153c33f6b4ff3d5 0xfe79fffff9fe7fff 0xfff3cfffffcff3ff

def z27 : W := mkw 0x5dd7d93200000000 0x02eebec990000000 0x59f7e3f800000003 0xbacfbf1fc0000000

def z28 : W := mkw 0x1f7c000000000000 0x00fbe00000000000 0x1ffe000000000000 0xf8fff00000000000

def z29 : W := mkw 0x1583b812b6002d43 0x00ac1dc095b0016a 0xff9ffe3ffe007fff 0xfffcfff1fff003ff

def z30 : W := mkw 0x0083ba1b230aefc3 0x10041dd0d918577e 0xc19ffe3f071ffff7 0xee0cfff1f838ffff

def z31 : W := mkw 0x5fffddb602000502 0x02fffeedb0100028 0xdfffffff06004f97 0xfefffffff830027c

def z32 : W := mkw 0x4a7e45b600000000 0x0253f22db0000000 0x407e03ff00000000 0x8203f01ff8000000

def z33 : W := mkw 0x5fffdfbf030ac782 0x12fffefdf818563c 0xdfffffff071fcf97 0xfefffffff838fe7c

def z34 : W := mkw 0x0000200020002800 0x0000010001000140 0x3801e000e0007e1f 0x39c00f00070003f0

def z35 : W := mkw 0x2850436841b85210 0xc142821b420dc290 0x407003f801f80000 0x8203801fc00fc000

def z36 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc001123f071fcf95 0x06000891f838fe7c

def z37 : W := mkw 0x0083101200000000 0x0004188090000000 0x4001123f00000001 0x02000891f8000000

def z38 : W := mkw 0x172c0000dcd5001c 0x00b9600006e6a800 0xa78e0000ffff801c 0x453c700007fffc00

def z39 : W := mkw 0x022804c408641028 0xa011402620432081 0x06600dc018e0306a 0x1033006e00c70183

def z40 : W := mkw 0x2850616060b03810 0xc142830b030581c0 0x3860e1c0e0e0300a 0x11c3070e07070180

def z41 : W := mkw 0x3f7c6368fdfd7a1c 0xc1fbe31b47efebd0 0xffffe3f8fffffe1f 0xffffff1fc7fffff0

def z42 : W := mkw 0x000006c5012250a0 0xa000003628091285 0x40001fc7000071e3 0x020000fe3800038f

def z43 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3981e000e6007e1f 0x39cc0f00073003f0

def z44 : W := mkw 0x1581980096000543 0x00ac0cc004b0002a 0x87801c001e0001e0 0x443c00e000f0000f

def z45 : W := mkw 0x7ffffffefdfd7a1c 0xc3fffffff7efebd0 0xfffffffffffffe1f 0xfffffffffffffff0

def z46 : W := mkw 0x0083121a01084200 0x00041890d0084210 0x419f123f01184e15 0xea0cf891f808c270

def z47 : W := mkw 0x0000000000000000 0x0000000000000000 0x819e0000071f8014 0xec0cf0000038fc00

def z48 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc7fe1fc71ffff1ff 0xfe3ff0fe38ffff8f

def z49 : W := mkw 0x28d3737b63baff92 0xd1469b9bdb1dd7fc 0xf9fff3ffe7ffff9f 0xffcfff9fff3ffffc

def z50 : W := mkw 0x2000224963baff92 0xd10001124b1dd7fc 0xa0000000e7ffff9c 0x05000000073ffffc

def z51 : W := mkw 0x0000000000000000 0x0000000000000000 0x86001c00180071ef 0x5c3000e000c0038f

def z52 : W := mkw 0x5fffddb696000543 0x02fffeedb4b0002a 0xdfffffff1e0001e3 0xfefffffff8f0000f

def z53 : W := mkw 0x0a7e021b49dfc29c 0x1053f010da4efe14 0x407e023f01ff8000 0x8203f011f80ffc00

def z54 : W := mkw 0x0000020801084200 0x0000001040084210 0x4011023801184e15 0xaa008811c008c270

def z55 : W := mkw 0x0083101302028582 0x100418809810142c 0x818e100706078180 0x440c708038303c0c

def z56 : W := mkw 0x172c04859c4700ac 0x20b960242ce23805 0x878e1c071e0781e0 0x443c70e038f03c0f

def z57 : W := mkw 0x02280485084600a8 0x2011402428423005 0x86081c07180601e0 0x443040e038c0300f

def z58 : W := mkw 0x2850612860982a10 0x414283094304c150 0x3811e038e0180e10 0x21c08f01c700c070

def z59 : W := mkw 0x2000224861b87a10 0xc1000112430dc3d0 0x606003c0e1f87e1f 0x9b03001e070fc3f0

def z60 : W := mkw 0x400245b600000000 0x0200122db0000000 0x400003ff00000000 0x0200001ff8000000

def z61 : W := mkw 0x1ffd9800ded5055f 0x00ffecc006f6a82a 0xbffe1c00ffff81fc 0xfdfff0e007fffc0f

def z62 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x3e600000f8e00008 0x11f3000007c70000

def z63 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0x7ffffffff8e0000b 0xfbffffffffc70000

def z64 : W := mkw 0x000006c5012250a0 0xa000003628091285 0x400003c700000000 0x0200001e38000000

def z65 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7811e3f8e0187e13 0x23c08f1fc700c3f0

def z66 : W := mkw 0x7fffdffe41b85210 0xc3fffefff20dc290 0x5fffffff01f80003 0xfafffffff80fc000

def z67 : W := mkw 0x2850436841b85210 0xc142821b420dc290 0x5871e3f801f80003 0xbac38f1fc00fc000

def z68 : W := mkw 0x2000636821287a00 0xc100031b410943d0 0x4001e3f800007e03 0x02000f1fc00003f0

def z69 : W := mkw 0x0000004000201000 0x8000000200010080 0x006001c000e0300a 0x1003000e00070180

def z70 : W := mkw 0x0000020801084200 0x0000001040084210 0x4010023801180000 0x82008011c008c000

def z71 : W := mkw 0x0083101200000000 0x0004188090000000 0x419f123f00000001 0xea0cf891f8000000

def z72 : W := mkw 0x0083101200000000 0x0004188090000000 0xc19f123f071f8015 0xee0cf891f838fc00

def z73 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xa7801c00fe007ffc 0x453c00e007f003ff

def z74 : W := mkw 0x0000020101024080 0x0000001008081204 0x4000120700004181 0x020000903800020c

def z75 : W := mkw 0x0000000000000000 0x0000000000000000 0x0060000001e0000c 0x98030000000f0000

def z76 : W := mkw 0x3dd1f928f6982f53 0x41ee8fc947b4c17a 0xbf91fc38fe187fff 0x7dfc8fe1c7f0c3ff

def z77 : W := mkw 0x5f7ceda4b4002841 0x02fbe76d25a00142 0x3e60edc0f800306a 0x11f3076e07c00183

def z78 : W := mkw 0x0081b80022002d43 0x00040dc00110016a 0x0001fc0000007fe3 0x00000fe0000003ff

def z79 : W := mkw 0x00002000b6002d43 0x0000010005b0016a 0xa0000000fe007ffc 0x0500000007f003ff

def z80 : W := mkw 0x1581980000000000 0x00ac0cc000000000 0x1f81fc0000000003 0x78fc0fe000000000

def z81 : W := mkw 0x68d3fffe61b87a10 0xc3469ffff30dc3d0 0x7871ffffe1f87e1f 0xbbc38fffff0fc3f0

def z82 : W := mkw 0x4856413200000000 0x0242b20990000000 0x0016003800000000 0x0000b001c0000000

def z83 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x401f123f011fcf81 0x8200f891f808fe7c

def z84 : W := mkw 0x1ffdb800fed52d5f 0x00ffedc007f6a96a 0xbffffc00ffffffff 0xfdffffe007ffffff

def z85 : W := mkw 0x0a7c000048d5001c 0x0053e0000246a800 0x387e0000e1ff801c 0xb9c3f000070ffc00

def z86 : W := mkw 0x4a7e47f7096650a8 0xa253f23fb84b3285 0xc67e1fff19e671ef 0xde33f0fff8cf338f

def z87 : W := mkw 0x5fffddb640900010 0x02fffeedb2048000 0x7fffffffe1f8001f 0xfbffffffff0fc000

def z88 : W := mkw 0x4083dfbf030ac782 0x12041efdf818563c 0xc19fffff071fcf97 0xee0cfffff838fe7c

def z89 : W := mkw 0x1583ba1bb70aefc3 0x10ac1dd0ddb8577e 0xff9ffe3fff1fffff 0xfffcfff1fff8ffff

def z90 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf80fc00fe0031ea 0x55fc07e007f0018f

def z91 : W := mkw 0x0081300022002d02 0x0004098001100168 0xb981f000e6007f9f 0x7dcc0f80073003fc

def z92 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x39fe0000e7ff8010 0xa1cff000073ffc00

def z93 : W := mkw 0x5fffdff7096650a8 0xa2fffeffb84b3285 0xdfffffff19e671ef 0xfefffffff8cf338f

def z94 : W := mkw 0x1581980096000543 0x00ac0cc004b0002a 0xbf801c00fe0001fc 0x7dfc00e007f0000f

def z95 : W := mkw 0x7ffffffe61b87a10 0xc3fffffff30dc3d0 0x7fffffffe1f87e1f 0xfbffffffff0fc3f0

def z96 : W := mkw 0x02ab16df0b6ed7aa 0xb01558b6f85b76bd 0xc7ff1fff1fffffff 0xfe3ff8fff8ffffff

def z97 : W := mkw 0x0002001300028080 0x1000100098001404 0x000e000700078000 0x0000700038003c00

def z98 : W := mkw 0x0850000040900010 0x0042800002048000 0x38100000e0180010 0x21c080000700c000

def z99 : W := mkw 0x022826c5296678a8 0xa0114136294b33c5 0xfe69ffc7f9e67fff 0xfff34ffe3fcf33ff

def z100 : W := mkw 0x4a7e45b648d5001c 0x0253f22db246a800 0x407e03ff01ff8000 0x8203f01ff80ffc00

def z101 : W := mkw 0x2000224861b87a10 0xc1000112430dc3d0 0x20000000e1f87e1c 0x01000000070fc3f0

def z102 : W := mkw 0x0a7c000048d5001c 0x0053e0000246a800 0x81fe000007ff8014 0xec0ff000003ffc00

def z103 : W := mkw 0x0854000040910014 0x0042a00002048800 0x0016000000198000 0x0000b0000000cc00

def z104 : W := mkw 0x1581ba40b7207d43 0x80ac0dd205b903ea 0xffe1ffc0ffe07fff 0xffff0ffe07ff03ff

def z105 : W := mkw 0x0228048400000000 0x0011402420000000 0x46681fc700000003 0xda3340fe38000000

def z106 : W := mkw 0x0850412000000000 0x0042820900000000 0x1860e1c000000002 0x10c3070e00000000

def z107 : W := mkw 0x1fff1012dcd5001c 0x00fff88096e6a800 0xffff123fffff801d 0xfffff891fffffc00

def z108 : W := mkw 0x1500a800b4002841 0x00a8054005a00142 0x3e00ec00f800306a 0x11f0076007c00183

def z109 : W := mkw 0x00000241096650a8 0xa0000012084b3285 0x0000000001e60000 0x00000000000f3000

def z110 : W := mkw 0x00000001084600a8 0x2000000008423005 0x80000000180601e0 0x0400000000c0300f

def z111 : W := mkw 0x4a7e45b600000000 0x0253f22db0000000 0x467e1fff00000003 0xda33f0fff8000000

def z112 : W := mkw 0x172c00009c45000c 0x00b9600004e22800 0x878e00001e078000 0x443c700000f03c00

def z113 : W := mkw 0x1f7c06c5ddf750bc 0xa0fbe0362eefba85 0xfffe1fc7fffff1ff 0xfffff0fe3fffff8f

def z114 : W := mkw 0x1f7e021bdddfc29c 0x10fbf010deeefe14 0xfffe023fffff801c 0xfffff011fffffc00

def z115 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xf9ffe3f8e7fffe1f 0xffcfff1fc73ffff0

def z116 : W := mkw 0x00000209030ac782 0x100000104818563c 0x80000000071fcf94 0x040000000038fe7c

def z117 : W := mkw 0x0228000008440008 0x0011400000422000 0x0068000001e60000 0x80034000000f3000

def z118 : W := mkw 0x20002248f7b87f53 0xc100011247bdc3fa 0xa0000000fff87ffc 0x0500000007ffc3ff

def z119 : W := mkw 0x1f7c0201ddd7409c 0x00fbe0100eeeba04 0xfffe1207ffffc19d 0xfffff0903ffffe0c

def z120 : W := mkw 0x5f7ccda400000000 0x02fbe66d20000000 0x1ffeedc000000002 0xf8fff76e00000000

def z121 : W := mkw 0x1fff1013ded7859e 0x10fff8809ef6bc2c 0xbffe1007ffff819c 0xfdfff0803ffffc0c

def z122 : W := mkw 0x02280485084600a8 0x2011402428423005 0x0008000700060000 0x0000400038003000

def z123 : W := mkw 0x1581bec5b7227de3 0xa0ac0df62db913ef 0xff81ffc7fe007fff 0x7ffc0ffe3ff003ff

def z124 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc181123f06004f95 0x6e0c0891f830027c

def z125 : W := mkw 0x00000000dcd5001c 0x0000000006e6a800 0xa0000000ffff801c 0x0500000007fffc00

def z126 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19e123f071f8180 0xc60cf091f838fc0c

def z127 : W := mkw 0x5583fdb6b6002d43 0x02ac1fedb5b0016a 0xff81fffffe007fff 0x7ffc0ffffff003ff

def z128 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x419fffff00000003 0xea0cfffff8000000

def z129 : W := mkw 0x1f7c06c5ddf750bc 0xa0fbe0362eefba85 0xfffe03c7ffff801c 0xfffff01e3ffffc00

def z130 : W := mkw 0x2a7867ed69fe7ab8 0xe153c33f6b4ff3d5 0x7879e3ffe1fe7e1f 0xbbc3cf1fff0ff3f0

def z131 : W := mkw 0x022804c5086610a8 0xa011402628433085 0x86681dc718e631ea 0x543340ee38c7318f

def z132 : W := mkw 0x00000000dcd5001c 0x0000000006e6a800 0xa19e0000ffff801c 0xed0cf00007fffc00

def z133 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x40681fc701e671e3 0x820340fe380f338f

def z134 : W := mkw 0x0a7c000048d5001c 0x0053e0000246a800 0x007e000001ff8000 0x8003f000000ffc00

def z135 : W := mkw 0x5583ddb600000000 0x02ac1eedb0000000 0x5f81ffff00000003 0x7afc0ffff8000000

def z136 : W := mkw 0x0a78000048d40018 0x0053c0000246a000 0xbe780000f9fe001c 0xfdf3c00007cff000

def z137 : W := mkw 0x4a7e45b600000000 0x0253f22db0000000 0x587fe3ff00000003 0xbac3ff1ff8000000

def z138 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x46601fc718e071eb 0x123300fe38c7038f

def z139 : W := mkw 0x0083101302028582 0x100418809810142c 0x0000100700000180 0x000000803800000c

def z140 : W := mkw 0x1500000094000000 0x00a8000004a00000 0x39800000e6000010 0x21cc000007300000

def z141 : W := mkw 0x0a7c000048d5001c 0x0053e0000246a800 0x867e000019ff800c 0xdc33f00000cffc00

def z142 : W := mkw 0x1d540000d4910014 0x00eaa00006a48800 0x38000000e0000000 0x01c0000007000000

def z143 : W := mkw 0x28d3737a61b87a10 0xc1469b9bd30dc3d0 0x79fff3ffe1f87e1f 0xfbcfff9fff0fc3f0

def z144 : W := mkw 0x1504000094010004 0x00a8200004a00800 0x0186000006018000 0x000c300000300c00

def z145 : W := mkw 0x0228068501024080 0x0011403428081204 0xc6681fc701064187 0xde3340fe3808320c

def z146 : W := mkw 0x1581b800b4002841 0x00ac0dc005a00142 0x3f81fc00f800306b 0x79fc0fe007c00183

def z147 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x406803c701e60000 0x8203401e380f3000

def z148 : W := mkw 0x00000209030ac782 0x100000104818563c 0xc0081207071fcf95 0xce0040903838fe7c

def z149 : W := mkw 0x5fff9c9600000000 0x02fffce4b0000000 0x1ffe1c0700000000 0xf8fff0e038000000

def z150 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x419f123f00004f81 0xea0cf891f800027c

def z151 : W := mkw 0x0081100002000502 0x0004088000100028 0x8181100006004f95 0x6c0c08800030027c

def z152 : W := mkw 0x1fffba1bffdfefdf 0x10fffdd0dffeff7e 0xfffffe3fffffffff 0xfffffff1ffffffff

def z153 : W := mkw 0x0000020801084200 0x0000001040084210 0x4001023800004e01 0x02000811c0000270

def z154 : W := mkw 0x2000636821287a00 0xc100031b410943d0 0x7801e3f8e0007e1f 0x3bc00f1fc70003f0

def z155 : W := mkw 0x2000024841b85210 0xc1000012420dc290 0x0000000001f80000 0x00000000000fc000

def z156 : W := mkw 0x5dd7db3b030ac782 0x12eebed9d818563c 0xd99ff23f071fcf95 0xeeccff91f838fe7c

def z157 : W := mkw 0x57afbc96b6002d43 0x02bd7de4b5b0016a 0xbf8ffc07fe007fff 0x7dfc7fe03ff003ff

def z158 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5e61ffff00000003 0x12f30ffff8000000

def z159 : W := mkw 0x1dd5b800f6912d57 0x00eeadc007b4896a 0x3997e000e6198e10 0x21ccbf000730cc70

def z160 : W := mkw 0x17af121b9f4fc78e 0x10bd7890dcfa7e3c 0xc79f123f1f1fcf95 0xee3cf891f8f8fe7c

def z161 : W := mkw 0x5fffddbe02088702 0x12fffeedf0104438 0x5fffffff06198e13 0xfafffffff830cc70

def z162 : W := mkw 0x5dd7d93200000000 0x02eebec990000000 0x599ff23f00000001 0xeaccff91f8000000

def z163 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f80e10 0xa3c38f1fc70fc070

def z164 : W := mkw 0x00002241bf667deb 0xa00001120dfb33ef 0xa0000000ffe67ffc 0x0500000007ff33ff

def z165 : W := mkw 0x0a7c06c549f750bc 0xa053e0362a4fba85 0xc67e1fc719fff1ef 0xde33f0fe38cfff8f

def z166 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x4001123f00004f81 0x02000891f800027c

def z167 : W := mkw 0x0850000040900010 0x0042800002048000 0xb9fe0000e7ff801c 0xfdcff000073ffc00

def z168 : W := mkw 0x1583981200000000 0x00ac1cc090000000 0x5f9ffe3f00000003 0xfafcfff1f8000000

def z169 : W := mkw 0x3dd1fb68f7b87f53 0xc1ee8fdb47bdc3fa 0x79f1e3f8e7f87e1f 0xbbcf8f1fc73fc3f0

def z170 : W := mkw 0x02ab14970a4685aa 0x301558a4b852342d 0x878e1c071e0781e0 0x443c70e038f03c0f

def z171 : W := mkw 0x1500000094000000 0x00a8000004a00000 0x3e000000f8000008 0x11f0000007c00000

def z172 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xb981e000fe007ffc 0x25cc0f0007f003ff

def z173 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81e000fe000e1c 0x7dfc0f0007f00070

def z174 : W := mkw 0x285067ed61ba7ab0 0xe142833f6b0dd3d5 0x7871ffffe1f87fff 0xbbc38fffff0fc3ff

def z175 : W := mkw 0x28d1fb6863b87f53 0xc1468fdb431dc3fa 0x7871fff8e1f87fff 0xbbc38fffc70fc3ff

def z176 : W := mkw 0x02ab16d70b66d5aa 0xb01558b6b85b36ad 0xc7ee1fc71fe7f1ef 0xde3f70fe38ff3f8f

def z177 : W := mkw 0x5f7ccda4dcd5001c 0x02fbe66d26e6a800 0xbffeedc0ffff801e 0xfdfff76e07fffc00

def z178 : W := mkw 0x5dd7ddb600000000 0x02eebeedb0000000 0x5997ffff00000003 0x22ccbffff8000000

def z179 : W := mkw 0x4affddb600000000 0x0257feedb0000000 0x407fffff00000003 0x8203fffff8000000

def z180 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3f81ec00fe003e7a 0x31fc0f6007f001f3

def z181 : W := mkw 0x02ab16df0b6ed7aa 0xb01558b6f85b76bd 0xc6691fff19e67fef 0xde3348fff8cf33ff

def z182 : W := mkw 0x5fffdfbe01084200 0x02fffefdf0084210 0x5fffffff01184e17 0xfafffffff808c270

def z183 : W := mkw 0x00000241096650a8 0xa0000012084b3285 0x8000000019e671ec 0x0400000000cf338f

def z184 : W := mkw 0x5dd7d93200000000 0x02eebec990000000 0x1997e03800000000 0x20ccbf01c0000000

def z185 : W := mkw 0x000004c400201020 0xa000002620010081 0x00000dc000003062 0x0000006e00000183

def z186 : W := mkw 0x0850020841984210 0x00428010420cc210 0x78710238e1f84e1d 0xbbc38811c70fc270

def z187 : W := mkw 0x0083101200000000 0x0004188090000000 0x018e100700000000 0x400c708038000000

def z188 : W := mkw 0x2000224861b87a10 0xc1000112430dc3d0 0x60110238e1f87e1d 0xab008811c70fc3f0

def z189 : W := mkw 0x0083101202000502 0x0004188090100028 0xc19f123f06004f95 0xee0cf891f830027c

def z190 : W := mkw 0x2850636961ba7a90 0xc142831b4b0dd3d4 0xf879f3ffe1fe7f9f 0xffc3cf9fff0ff3fc

def z191 : W := mkw 0x0000200020002800 0x0000010001000140 0x3801e000e0000e10 0x21c00f0007000070

def z192 : W := mkw 0x42abdff7096650a8 0xa2155effb84b3285 0xc669ffff19e671ef 0xde334ffff8cf338f

def z193 : W := mkw 0x1500880000000000 0x00a8044000000000 0x1e00ec0000000002 0x10f0076000000000

def z194 : W := mkw 0x17af10139e47858e 0x10bd78809cf23c2c 0x878e10071e078180 0x443c708038f03c0c

def z195 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001c00000071e3 0x000000e00000038f

def z196 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3981fc00e6007ff3 0x21cc0fe0073003ff

def z197 : W := mkw 0x5fffddb7084600a8 0x22fffeedb8423005 0xdfffffff180601e3 0xfefffffff8c0300f

def z198 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc18f123f0607cf81 0x460c7891f8303e7c

def z199 : W := mkw 0x0081980000000000 0x00040cc000000000 0x0001fc0000000003 0x00000fe000000000

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000100000004185 0x4c0000800000020c

def z201 : W := mkw 0x1500a800b4002841 0x00a8054005a00142 0xbf80ec00fe00307e 0x7dfc076007f00183

def z202 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3f81fc00e6000e13 0x79fc0fe007300070

def z203 : W := mkw 0x3d50eb68f5b87a51 0xc1ea875b47adc3d2 0x7e71eff8f9f87e7f 0xbbf38f7fc7cfc3f3

def z204 : W := mkw 0x1d540000dcd5001c 0x00eaa00006e6a800 0xb9960000ffff801c 0x25ccb00007fffc00

def z205 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc79f1e3f1f1fffff 0xfe3cf8f1f8f8ffff

def z206 : W := mkw 0x1fff101adedd871e 0x10fff880d6f6ec38 0xbfff0038ffff8e1c 0xfdfff801c7fffc70

def z207 : W := mkw 0x1f7c0208dddd421c 0x00fbe01046eeea10 0xffff0238ffffce1d 0xfffff811c7fffe70

def z208 : W := mkw 0x1ffd1000ded5051e 0x00ffe88006f6a828 0xbfff1000ffffcf9d 0xfdfff88007fffe7c

def z209 : W := mkw 0x5dd7d932d4910014 0x02eebec996a48800 0x3997e038e6198010 0x21ccbf01c730cc00

def z210 : W := mkw 0x0000000800080200 0x0000000040004010 0x0011003800180e10 0x20008801c000c070

def z211 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x59ffe3ff00000000 0xa2cfff1ff8000000

def z212 : W := mkw 0x0081980002000543 0x00040cc00010002a 0x00001c00000001e0 0x000000e00000000f

def z213 : W := mkw 0x0850612020002800 0x0042830901000140 0x7871e3f8e0007e1f 0xbbc38f1fc70003f0

def z214 : W := mkw 0x0000020001004000 0x0000001000080200 0x4000020001004005 0x8a00001000080200

def z215 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7870e3f8e1f8300a 0x93c3871fc70fc180

def z216 : W := mkw 0x2000612820082a00 0x4100030941004150 0x0001e03800000e00 0x00000f01c0000070

def z217 : W := mkw 0x0000200020002800 0x0000010001000140 0x0001e00000007e03 0x00000f00000003f0

def z218 : W := mkw 0x1f7c0209dfdfc79e 0x10fbe0104efefe3c 0xbffe0000ffffcf9c 0xfdfff00007fffe7c

def z219 : W := mkw 0x2850612860982a10 0x414283094304c150 0x7871e3f8e0180e13 0xbbc38f1fc700c070

def z220 : W := mkw 0x1dd7101ad6998716 0x10eeb880d6b4cc38 0x39970038e6198e10 0x21ccb801c730cc70

def z221 : W := mkw 0x0083125b0b6ed7aa 0xb0041892d85b76bd 0xc19f123f1ffffffd 0xee0cf891f8ffffff

def z222 : W := mkw 0x5fffddb694000000 0x02fffeedb4a00000 0xfffffffffe00001f 0xfffffffffff00000

def z223 : W := mkw 0x5fffdfff0b6ed7aa 0xb2fffefff85b76bd 0xdfffffff1fffffff 0xfefffffff8ffffff

def z224 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3e01fc00f8007feb 0x11f00fe007c003ff

def z225 : W := mkw 0x02a9bec52b667deb 0xa0154df6295b33ef 0xc669ffc719e67fef 0xde334ffe38cf33ff

def z226 : W := mkw 0x2a7c436849fd521c 0xc153e21b424fea90 0x407e03f801ff8000 0x8203f01fc00ffc00

def z227 : W := mkw 0x5fffddb69c45000c 0x02fffeedb4e22800 0xdfffffff1e078003 0xfefffffff8f03c00

def z228 : W := mkw 0x57af9c969c45000c 0x02bd7ce4b4e22800 0x878e1c071e078000 0x443c70e038f03c00

def z229 : W := mkw 0x3f7c6368fdfd7a1c 0xc1fbe31b47efebd0 0x7e71e3f8f9f87e1f 0xbbf38f1fc7cfc3f0

def z230 : W := mkw 0x0081b80022002d43 0x00040dc00110016a 0x0001e00000000e00 0x00000f0000000070

def z231 : W := mkw 0x5fffddb6d4910014 0x02fffeedb6a48800 0x7fffffffe6198013 0xfbffffffff30cc00

def z232 : W := mkw 0x6083fffe21287a00 0xc3041ffff10943d0 0x4001ffff00007e03 0x02000ffff80003f0

def z233 : W := mkw 0x17a9bcc4be643d6b 0xa0bd4de625f321eb 0xbfe1fdc0fee07fff 0x7dff0fee07f703ff

def z234 : W := mkw 0x00002000b6002d43 0x0000010005b0016a 0x20000000e6000e10 0x0100000007300070

def z235 : W := mkw 0x00000241012250a0 0xa000001208091285 0x00000000000071e0 0x000000000000038f

def z236 : W := mkw 0x1d54000000000000 0x00eaa00000000000 0x1996000000000000 0x20ccb00000000000

def z237 : W := mkw 0x0083321b230aef82 0x10041990d918577c 0xf99ff23fe71fff9f 0xffccff91ff38fffc

def z238 : W := mkw 0x2850224861b87a10 0xc1428112430dc3d0 0x38700000e1f87e1c 0xb9c38000070fc3f0

def z239 : W := mkw 0x3dd3fb7bf7baffd3 0xd1ee9fdbdfbdd7fe 0xffffffffffffffff 0xffffffffffffffff

def z240 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3981e000e6000e10 0x21cc0f0007300070

def z241 : W := mkw 0x1f7c0241ddf750bc 0xa0fbe0120eefba85 0xbffe0000fffff1fc 0xfdfff00007ffff8f

def z242 : W := mkw 0x5fffddf608641028 0xa2fffeefb0432081 0x5fffffff18e0306b 0xfafffffff8c70183

def z243 : W := mkw 0x1581ba09b70aefc3 0x10ac0dd04db8577e 0xbf81fc00ff1fffff 0x7dfc0fe007f8ffff

def z244 : W := mkw 0x02ab16df0b6ed7aa 0xb01558b6f85b76bd 0xc1ff13ff07ffcf95 0xee0ff89ff83ffe7c

def z245 : W := mkw 0x008316df032ad7a2 0xb00418b6f81956bd 0xc19f1fff071ffff7 0xee0cf8fff838ffff

def z246 : W := mkw 0x3581fb68b7287f43 0xc1ac0fdb45b943fa 0xff81fff8fe007fff 0x7ffc0fffc7f003ff

def z247 : W := mkw 0x3dd1fb68f7b87f53 0xc1ee8fdb47bdc3fa 0xfff1fff8fff87fff 0xffff8fffc7ffc3ff

def z248 : W := mkw 0x57afddb600000000 0x02bd7eedb0000000 0x478fffff00000003 0x423c7ffff8000000

def z249 : W := mkw 0x08d3533b030ac782 0x10469a99d818563c 0xd9fff3ff071fcf97 0xfecfff9ff838fe7c

def z250 : W := mkw 0x0083101b020a8782 0x10041880d810543c 0x819f103f061f8f90 0x640cf881f830fc7c

def z251 : W := mkw 0x0000004008641028 0xa000000200432081 0x0000000018e03068 0x0000000000c70183

def z252 : W := mkw 0x28d3733b639aef92 0x51469b99db1cd77c 0xf99ff23fe71fcf95 0xefccff91ff38fe7c

def z253 : W := mkw 0x008312130302c582 0x100418909818162c 0xc18e12070707c185 0xce0c709038383e0c

def z254 : W := mkw 0x1f7c412000000000 0x00fbe20900000000 0x5fffe3f800000003 0xfaffff1fc0000000

def z255 : W := mkw 0x7dd7f93a60982a10 0x43eebfc9d304c150 0x3997e038e0180e10 0x21ccbf01c700c070

def z256 : W := mkw 0x0a7c000048d5001c 0x0053e0000246a800 0x0060000000e00000 0x0003000000070000

def z257 : W := mkw 0x1dd1f920b6002d43 0x00ee8fc905b0016a 0xfff1fff8fe007fff 0xffff8fffc7f003ff

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x06000c001800306a 0x1030006000c00183

def z259 : W := mkw 0x2850436841b85210 0xc142821b420dc290 0x407103f801f84e15 0xaa03881fc00fc270

def z260 : W := mkw 0x1581980096000543 0x00ac0cc004b0002a 0x0180000006000000 0x000c000000300000

def z261 : W := mkw 0x0000200022002d43 0x000001000110016a 0x0000000000007fe0 0x00000000000003ff

def z262 : W := mkw 0x2083325b63baff92 0xd1041992db1dd7fc 0xe19f123fe7ffff9d 0xef0cf891ff3ffffc

def z263 : W := mkw 0x00002000b6002d43 0x0000010005b0016a 0xb801e000fe007fff 0x3dc00f0007f003ff

def z264 : W := mkw 0x4a7e47bf010ac280 0x1253f23df8085614 0x407e03ff011f8000 0x8203f01ff808fc00

def z265 : W := mkw 0x0000000000000000 0x0000000000000000 0x860000001800000c 0x5c30000000c00000

def z266 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x46681fc701e60003 0xda3340fe380f3000

def z267 : W := mkw 0x02280485084600a8 0x2011402428423005 0xc6681fc7180601e3 0xde3340fe38c0300f

def z268 : W := mkw 0x572c8c8400000000 0x02b9646420000000 0x06000c0000000000 0x0030006000000000

def z269 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x419f023f071f8e10 0xa20cf811f838fc70

def z270 : W := mkw 0x5ffffdb6fed52d5f 0x02ffffedb7f6a96a 0xffffffffffffffff 0xffffffffffffffff

def z271 : W := mkw 0x15839a1b030ac782 0x10ac1cd0d818563c 0xdf9ffe3f071fcf97 0xfefcfff1f838fe7c

def z272 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010000001180014 0xa80080000008c000

def z273 : W := mkw 0x3f7c4368ddfd521c 0xc1fbe21b46efea90 0xfffe03f8ffff801c 0xfffff01fc7fffc00

def z274 : W := mkw 0x172c00009c45000c 0x00b9600004e22800 0x87ee00001fe7800c 0xdc3f700000ff3c00

def z275 : W := mkw 0x00000209010ac280 0x1000001048085614 0x00000000011f8000 0x000000000008fc00

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0x86001c00180001e0 0x443000e000c0000f

def z277 : W := mkw 0x15000000dcd5001c 0x00a8000006e6a800 0xbf800000ffff801c 0x7dfc000007fffc00

def z278 : W := mkw 0x00000209030ac782 0x100000104818563c 0xc0110238071fcf95 0xae008811c038fe7c

def z279 : W := mkw 0x2850632861986a10 0x41428319430cc350 0x7811e238e1184e15 0xabc08f11c708c270

def z280 : W := mkw 0x02ab121b0b4ec78a 0x10155890d85a763c 0xc7ff123f1fffcf9d 0xfe3ff891f8fffe7c

def z281 : W := mkw 0x2000200860982a10 0x410001004304c150 0x20000000e0180e10 0x010000000700c070

def z282 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7861e3f8e0e07e0b 0x13c30f1fc70703f0

def z283 : W := mkw 0x5fffdff7012250a0 0xa2fffeffb8091285 0x5fffffff000071e3 0xfafffffff800038f

def z284 : W := mkw 0x4083dfbf030ac782 0x12041efdf818563c 0x4001ffff00004f83 0x02000ffff800027c

def z285 : W := mkw 0x172c00009c45000c 0x00b9600004e22800 0xbf8e0000fe07801c 0x7dfc700007f03c00

def z286 : W := mkw 0x022a06df096ed2a8 0xb0115036f84b7695 0xc67e1fff19fff1ef 0xde33f0fff8cfff8f

def z287 : W := mkw 0x7fffffff63baff92 0xd3fffffffb1dd7fc 0xffffffffe7ffff9f 0xffffffffff3ffffc

def z288 : W := mkw 0x5ffffdb6b6002d43 0x02ffffedb5b0016a 0x7fffffffe6000e13 0xfbffffffff300070

def z289 : W := mkw 0x1583121b970ac782 0x10ac1890dcb8563c 0xff9f123fff1fcf9d 0xfffcf891fff8fe7c

def z290 : W := mkw 0x1583b81ab608af43 0x10ac1dc0d5b0457a 0x3997e038e6198e10 0x21ccbf01c730cc70

def z291 : W := mkw 0x57af9c9702028582 0x12bd7ce4b810142c 0x878e1c0706078180 0x443c70e038303c0c

def z292 : W := mkw 0x0228048400000000 0x0011402420000000 0xc6681fc7180071ef 0xde3340fe38c0038f

def z293 : W := mkw 0x022806c5ddf750bc 0xa01140362eefba85 0xe6681fc7fffff1ff 0xdf3340fe3fffff8f

def z294 : W := mkw 0x022806c401205000 0x8011403620090280 0x46681fc701e0700f 0xda3340fe380f0380

def z295 : W := mkw 0x1f7c00009c45000c 0x00fbe00004e22800 0x9ffe00001e078000 0xfcfff00000f03c00

def z296 : W := mkw 0x0000024101225080 0x8000001208091284 0xc06813c701e6718f 0xde03409e380f338c

def z297 : W := mkw 0x0083101302028582 0x100418809810142c 0x819e1007071f8194 0xec0cf0803838fc0c

def z298 : W := mkw 0x0083101200000000 0x0004188090000000 0x0197003800000000 0x200cb801c0000000

def z299 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000071f8014 0x040000000038fc00

def z300 : W := mkw 0x0850000040900010 0x0042800002048000 0x38600000e0e00008 0x11c3000007070000

def z301 : W := mkw 0x08500000dcd5001c 0x0042800006e6a800 0xb8700000ffff801c 0xbdc3800007fffc00

def z302 : W := mkw 0x1fff16dfdfffd7be 0xb0fff8b6fefffebd 0xffff1fffffffffff 0xfffff8ffffffffff

def z303 : W := mkw 0x2000436801285200 0xc100021b40094290 0x400003f800000000 0x0200001fc0000000

def z304 : W := mkw 0x0228000008440008 0x0011400000422000 0x0660000018e00008 0x1033000000c70000

def z305 : W := mkw 0x1500a800b4002841 0x00a8054005a00142 0x3e01ec00f8007e7f 0x39f00f6007c003f3

def z306 : W := mkw 0x1f7ca800fcd5285d 0x00fbe54007e6a942 0x3e60ec00f8e0306a 0x11f3076007c70183

def z307 : W := mkw 0x2850636061b07810 0xc142831b030d83c0 0x7860e3c0e1e0700f 0x9bc3071e070f0380

def z308 : W := mkw 0x00002209b70aefc3 0x100001104db8577e 0xa0000000ff1ffffc 0x0500000007f8ffff

def z309 : W := mkw 0x2000636821287a00 0xc100031b410943d0 0x4011e3f801187e17 0xaa008f1fc008c3f0

def z310 : W := mkw 0x3f7c6160fcf5381c 0xc1fbe30b07e7a9c0 0xbffee1c0ffffb01e 0xfdfff70e07fffd80

def z311 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe1c00fffff1ff 0xfdfff0e007ffff8f

def z312 : W := mkw 0x0000020801084200 0x0000001040084210 0xc19f0238071fce15 0xee0cf811c038fe70

def z313 : W := mkw 0x1728acc4bc643869 0xa0b9456625e321c3 0x3e60edc0f8e0306a 0x11f3076e07c70183

def z314 : W := mkw 0x0000024001205000 0x8000001200090280 0x406003c001e00000 0x8203001e000f0000

def z315 : W := mkw 0x2850636821287a00 0xc142831b410943d0 0x5871e3f800007e03 0xbac38f1fc00003f0

def z316 : W := mkw 0x0081100002000502 0x0004088000100028 0x87811c001e007fff 0x7c3c08e000f003ff

def z317 : W := mkw 0x0228024009645008 0x80114012004b2280 0xc66803c019e6700f 0xde33401e00cf3380

def z318 : W := mkw 0x28506368fdfd7a1c 0xc142831b47efebd0 0xf871e3f8fffffe1f 0xbfc38f1fc7fffff0

def z319 : W := mkw 0x172800009c440008 0x00b9400004e22000 0xbfe80000ffe6001c 0xfdff400007ff3000

def z320 : W := mkw 0x0000000048d5001c 0x000000000246a800 0x0000000001ff8000 0x00000000000ffc00

def z321 : W := mkw 0x15002000b6002d43 0x00a8010005b0016a 0xbf800000fe007ffc 0x7dfc000007f003ff

def z322 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001000000004e15 0x2800080000000270

def z323 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbfee0000fee78008 0x55ff700007f73c00

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x001e0000011f8000 0x8000f0000008fc00

def z325 : W := mkw 0x17a9bec5bf667deb 0xa0bd4df62dfb33ef 0xffe9ffc7ffe67fff 0xffff4ffe3fff33ff

def z326 : W := mkw 0x5f7ecdb600000000 0x02fbf66db0000000 0x5e7eefff00000002 0x92f3f77ff8000000

def z327 : W := mkw 0x4000cda400000000 0x0200066d20000000 0x0000edc000000002 0x0000076e00000000

def z328 : W := mkw 0x0083321bb70aefc3 0x10041990ddb8577e 0xe19f123fff1ffffd 0xef0cf891fff8ffff

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000180071ec 0x0400000000c0038f

def z330 : W := mkw 0x0000024001205000 0x8000001200090280 0x0000000001e0700c 0x00000000000f0380

def z331 : W := mkw 0x1583b81ab608af43 0x10ac1dc0d5b0457a 0xbf97fc38fe19ffff 0x7dfcbfe1c7f0cfff

def z332 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc06803c719e671ec 0x8603401e38cf338f

def z333 : W := mkw 0x28506368f7b87f53 0xc142831b47bdc3fa 0xf871e3f8fff87fff 0xbfc38f1fc7ffc3ff

def z334 : W := mkw 0x5f7ccda4dcd5001c 0x02fbe66d26e6a800 0x3e60edc0f8e0000a 0x11f3076e07c70000

def z335 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xfe71fff8f9f87fff 0xfff38fffc7cfc3ff

def z336 : W := mkw 0x022804c408641028 0xa011402620432081 0x006001c000e00000 0x0003000e00070000

def z337 : W := mkw 0x4aff57bf030ac782 0x1257fabdf818563c 0xc1ff13ff071fcf95 0xee0ff89ff838fe7c

def z338 : W := mkw 0x1581980094000000 0x00ac0cc004a00000 0xbf81fc00fe00001f 0x7dfc0fe007f00000

def z339 : W := mkw 0x0850412040900010 0x0042820902048000 0x7871e3f8e1f8001f 0xbbc38f1fc70fc000

def z340 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x3e7e0000f9ff8008 0x91f3f00007cffc00

def z341 : W := mkw 0x1d540000d4910014 0x00eaa00006a48800 0x39f60000e7f9801c 0xb9cfb000073fcc00

def z342 : W := mkw 0x0081120803084702 0x0004089040184238 0xc191123807184f95 0xee0c8891c038c27c

def z343 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z344 : W := mkw 0x2850616060b03810 0xc142830b030581c0 0x7871e3f8e0e0300b 0xbbc38f1fc7070180

def z345 : W := mkw 0x5ffffff7bf667deb 0xa2ffffffbdfb33ef 0xffffffffffe67fff 0xffffffffffff33ff

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x8180000006000014 0x6c0c000000300000

def z347 : W := mkw 0x1ffdbec5fff77dff 0xa0ffedf62fffbbef 0xffffffc7ffffffff 0xfffffffe3fffffff

def z348 : W := mkw 0x4083dff7012250a0 0xa2041effb8091285 0x4001ffff000071e3 0x02000ffff800038f

def z349 : W := mkw 0x40839c9600000000 0x02041ce4b0000000 0x00001c0700000000 0x000000e038000000

def z350 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff180071ef 0xfefffffff8c0038f

def z351 : W := mkw 0x7dd7fb7a61b87a10 0xc3eebfdbd30dc3d0 0x79f7e3f8e1f87e1f 0xbbcfbf1fc70fc3f0

def z352 : W := mkw 0x5d54c92000000000 0x02eaa64900000000 0x1800e00000000000 0x00c0070000000000

def z353 : W := mkw 0x5f7ccfe5096650a8 0xa2fbe67f284b3285 0xde68ffc719e671ef 0xdef347fe38cf338f

def z354 : W := mkw 0x2a78636869fc7a18 0xc153c31b434fe3d0 0xfe79e3f8f9fe7e1f 0xfff3cf1fc7cff3f0

def z355 : W := mkw 0x0083101a02088702 0x10041880d0104438 0x819f0038071f8e14 0xec0cf801c038fc70

def z356 : W := mkw 0x00000209030ac782 0x100000104818563c 0x819e0000071fcf94 0xec0cf0000038fe7c

def z357 : W := mkw 0x0083101302028582 0x100418809810142c 0x818f10070607cf95 0x6c0c788038303e7c

def z358 : W := mkw 0x1f7c4120dcd5001c 0x00fbe20906e6a800 0xffffe3f8ffff801f 0xffffff1fc7fffc00

def z359 : W := mkw 0x0a7c06c549f750bc 0xa053e0362a4fba85 0x407e03c701ff8000 0x8203f01e380ffc00

def z360 : W := mkw 0x00002000fed52d5f 0x0000010007f6a96a 0xa0000000fffffffc 0x0500000007ffffff

def z361 : W := mkw 0x02280485084600a8 0x2011402428423005 0x86681c0719e601ec 0xdc3340e038cf300f

def z362 : W := mkw 0x5ffdfda4b6002d43 0x02ffefed25b0016a 0xbfe1fdc0fe007fff 0x7dff0fee07f003ff

def z363 : W := mkw 0x2083737b232aff82 0xd1041b9bd91957fc 0x4001f3ff00007f83 0x02000f9ff80003fc

def z364 : W := mkw 0x0000000102028582 0x100000000810142c 0x8000000006078180 0x0400000000303c0c

def z365 : W := mkw 0x17a99ec5096650a8 0xa0bd4cf6284b3285 0xdfe9ffc719e671ef 0xfeff4ffe38cf338f

def z366 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xb981f000e6004f95 0x6dcc0f800730027c

def z367 : W := mkw 0x0000000000000000 0x0000000000000000 0x019e000000000000 0xe80cf00000000000

def z368 : W := mkw 0x1500000094000000 0x00a8000004a00000 0x878000001e000000 0x443c000000f00000

def z369 : W := mkw 0x1f7c000048d5001c 0x00fbe0000246a800 0x1ffe000001ff8000 0xf8fff000000ffc00

def z370 : W := mkw 0x5f7ccda400000000 0x02fbe66d20000000 0x5e68ffc700000003 0xdaf347fe38000000

def z371 : W := mkw 0x2000224821287a00 0xc1000112410943d0 0x0000000000007e00 0x00000000000003f0

def z372 : W := mkw 0x5fffdfbfdfdfc79e 0x12fffefdfefefe3c 0xffffffffffffcf9f 0xfffffffffffffe7c

def z373 : W := mkw 0x02280685094640a8 0x20114034284a3205 0xc6081e07190641e5 0xce3040f038c8320f

def z374 : W := mkw 0x5dd7d93a02088702 0x12eebec9d0104438 0x1997e03806198e10 0x20ccbf01c030cc70

def z375 : W := mkw 0x1f7c000000000000 0x00fbe00000000000 0x9ffe0000071f8014 0xfcfff0000038fc00

def z376 : W := mkw 0x0850412000000000 0x0042820900000000 0x407003f800000000 0x8203801fc0000000

def z377 : W := mkw 0x2083737b232aff82 0xd1041b9bd91957fc 0xc19ff3ff071fff97 0xee0cff9ff838fffc

def z378 : W := mkw 0x1581b80020002800 0x00ac0dc001000140 0x3f81fc00e0007e1f 0x79fc0fe0070003f0

def z379 : W := mkw 0x5fffffbfb70aefc3 0x12fffffdfdb8577e 0xffffffffff1fffff 0xfffffffffff8ffff

def z380 : W := mkw 0x0083121b010ac280 0x10041890d8085614 0x419f123f011f8001 0xea0cf891f808fc00

def z381 : W := mkw 0x0083101a02088702 0x10041880d0104438 0x0001003800000e00 0x00000801c0000070

def z382 : W := mkw 0x0081100002000502 0x0004088000100028 0x819f1000071fcf95 0xec0cf8800038fe7c

def z383 : W := mkw 0x2850616060b03810 0xc142830b030581c0 0x3870e1c0e1f8301e 0xb9c3870e070fc180

def z384 : W := mkw 0x000006c5012250a0 0xa000003628091285 0xc0081fc7010671e7 0xce0040fe3808338f

def z385 : W := mkw 0x3ff9ffedfffe7ffb 0xe1ffcfff6ffff3ff 0xfff9fffffffe7fff 0xffffcffffffff3ff

def z386 : W := mkw 0x3dd1f928f6982f53 0x41ee8fc947b4c17a 0x3991e038e6180e10 0x21cc8f01c730c070

def z387 : W := mkw 0x0000020101024080 0x0000001008081204 0x8000000001064184 0x040000000008320c

def z388 : W := mkw 0x0002001a00088200 0x10001000d0004410 0x0016003800198000 0x0000b001c000cc00

def z389 : W := mkw 0x000006c5012250a0 0xa000003628091285 0x40601fc701e071ef 0x9a0300fe380f038f

def z390 : W := mkw 0x1f7c06c5096650a8 0xa0fbe036284b3285 0xdffe1fc719e671ef 0xfefff0fe38cf338f

def z391 : W := mkw 0x0000024001205000 0x8000001200090280 0x400003c000007003 0x0200001e00000380

def z392 : W := mkw 0x4a7e47f7096650a8 0xa253f23fb84b3285 0x407e03ff01e60000 0x8203f01ff80f3000

def z393 : W := mkw 0x08d3513200000000 0x00469a8990000000 0x59fff3ff00000003 0xfacfff9ff8000000

def z394 : W := mkw 0x0081b80022002d43 0x00040dc00110016a 0x3801fc00e0007fff 0x39c00fe0070003ff

def z395 : W := mkw 0x000000009c45000c 0x0000000004e22800 0x800000001e078000 0x0400000000f03c00

def z396 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbe600000ffff801c 0x15f3000007fffc00

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x1801e00000000003 0x38c00f0000000000

def z398 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x1feefdc700000002 0x50ff77ee38000000

def z399 : W := mkw 0x1f7c0000d4910014 0x00fbe00006a48800 0x3ffe0000e6198010 0xf9fff0000730cc00

def z400 : W := mkw 0x0000048400000000 0x0000002420000000 0x40001fc700000003 0x020000fe38000000

def z401 : W := mkw 0x4083d93200000000 0x02041ec990000000 0x0001e03800000000 0x00000f01c0000000

def z402 : W := mkw 0x0000020101024080 0x0000001008081204 0xc008120701064185 0xce0040903808320c

def z403 : W := mkw 0x4083fdb622002d43 0x02041fedb110016a 0x4001ffff00007fe3 0x02000ffff80003ff

def z404 : W := mkw 0x7ffffffe21287a00 0xc3fffffff10943d0 0x5fffffff00007e03 0xfafffffff80003f0

def z405 : W := mkw 0x2850616860b83a10 0xc142830b4305c1d0 0x3871e1f8e0f83e1a 0x31c38f0fc707c1f0

def z406 : W := mkw 0x2000204060b03810 0xc1000102030581c0 0x20000000e0e03008 0x0100000007070180

def z407 : W := mkw 0x1d540000d4910014 0x00eaa00006a48800 0xbf960000fe19801c 0x7dfcb00007f0cc00

def z408 : W := mkw 0x0000000008440008 0x0000000000422000 0x8000000019e6000c 0x0400000000cf3000

def z409 : W := mkw 0x0850200060902810 0x0042810003048140 0x3871e000e1f87e1f 0xb9c38f00070fc3f0

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x818e000006078000 0x440c700000303c00

def z411 : W := mkw 0x00000209010a4280 0x0000001048085214 0xc019123f011e4f95 0xee00c891f808f27c

def z412 : W := mkw 0x0228000008440008 0x0011400000422000 0x86681c0019e671ef 0xdc3340e000cf338f

def z413 : W := mkw 0x0081100002000502 0x0004088000100028 0x0001100000004f81 0x000008800000027c

def z414 : W := mkw 0x2000224969fe7ab8 0xe10001124b4ff3d5 0xa0000000f9fe7ffc 0x0500000007cff3ff

def z415 : W := mkw 0x02280485084600a8 0x2011402428423005 0x86081c07180671ef 0x5c3040e038c0338f

def z416 : W := mkw 0x1500a800b4002841 0x00a8054005a00142 0xbe00fc00f80071ef 0x5df007e007c0038f

def z417 : W := mkw 0x1581980096000543 0x00ac0cc004b0002a 0x87811c001e004ff5 0x6c3c08e000f0027f

def z418 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x8781fc001e007fe3 0x443c0fe000f003ff

def z419 : W := mkw 0x1581ba08b7086f43 0x00ac0dd045b8437a 0xff91fe38ff187fff 0xfffc8ff1c7f8c3ff

def z420 : W := mkw 0x022c00000845000c 0x0011600000422800 0x000e000000078000 0x0000700000003c00

def z421 : W := mkw 0x3dd1fb6861b87a10 0xc1ee8fdb430dc3d0 0x7ff1fff8e1f87e1f 0xfbff8fffc70fc3f0

def z422 : W := mkw 0x1500000000000000 0x00a8000000000000 0x1f80000000000000 0x78fc000000000000

def z423 : W := mkw 0x5fffddb702028582 0x12fffeedb810142c 0xdfffffff06078183 0xfefffffff8303c0c

def z424 : W := mkw 0x2a7867ec69fc7a38 0xe153c33f634fe3d1 0x7e71eff8f9f87e7f 0xbbf38f7fc7cfc3f3

def z425 : W := mkw 0x0a7845a400000000 0x0053c22d20000000 0x5e79ffff00000003 0xfaf3cffff8000000

def z426 : W := mkw 0x1581980000000000 0x00ac0cc000000000 0x9f81fc00180071ef 0x7cfc0fe000c0038f

def z427 : W := mkw 0x3d50e960f4b03851 0xc1ea874b07a581c2 0x3e60edc0f8e0306a 0x11f3076e07c70183

def z428 : W := mkw 0x00000209030ac782 0x100000104818563c 0x0000000000004f80 0x000000000000027c

def z429 : W := mkw 0x1581980096000543 0x00ac0cc004b0002a 0x9f81fc001e0001e3 0x7cfc0fe000f0000f

def z430 : W := mkw 0x17a99ec59f6655eb 0xa0bd4cf62cfb32af 0xc7e81fc71fe671ef 0xde3f40fe38ff338f

def z431 : W := mkw 0x28d3737a63b8ff12 0xd1469b9bd31dc7f8 0x79f7e3f8e7f9fe1f 0xbbcfbf1fc73fcff0

def z432 : W := mkw 0x1f7c048400000000 0x00fbe02420000000 0x5ffe1fc700000003 0xfafff0fe38000000

def z433 : W := mkw 0x02280000dcd5001c 0x0011400006e6a800 0xa6680000ffff801c 0xdd33400007fffc00

def z434 : W := mkw 0x0081100002000502 0x0004088000100028 0x8180100006000180 0x440c00800030000c

def z435 : W := mkw 0x172c00009c45000c 0x00b9600004e22800 0x0600000018000000 0x0030000000c00000

def z436 : W := mkw 0x2a7867e569f678b8 0xe153c33f2b4fb3c5 0xfe68ffc7f9e671ef 0xdff347fe3fcf338f

def z437 : W := mkw 0x0228048400000000 0x0011402420000000 0x06081c0700000000 0x403040e038000000

def z438 : W := mkw 0x6a7e67fe61b87a10 0xc353f33ff30dc3d0 0x787fe3ffe1f87e1f 0xbbc3ff1fff0fc3f0

def z439 : W := mkw 0x02280241096650a8 0xa0114012084b3285 0x8668000019e671ec 0xdc33400000cf338f

def z440 : W := mkw 0x1583b813b602adc3 0x10ac1dc09db0156e 0xbf8ffc07fe07ffff 0x7dfc7fe03ff03fff

def z441 : W := mkw 0x1d500000d4900010 0x00ea800006a48000 0xbff00000fff8001c 0xfdff800007ffc000

def z442 : W := mkw 0x172c000000000000 0x00b9600000000000 0x078e000000000000 0x403c700000000000

def z443 : W := mkw 0x3fff737bffffff9e 0xd1fffb9bdffffffc 0xfffff3ffffffff9f 0xffffff9ffffffffc

def z444 : W := mkw 0x1500a800b6002d43 0x00a8054005b0016a 0xbe00ec00fe007ffe 0x15f0076007f003ff

def z445 : W := mkw 0x00000241096650a8 0xa0000012084b3285 0xc008120719e671ed 0xce00409038cf338f

def z446 : W := mkw 0x5587981200000000 0x02ac3cc090000000 0x0186000000000000 0x000c300000000000

def z447 : W := mkw 0x0850436001205000 0x8042821b00090280 0x5871e3f801e0700f 0xbac38f1fc00f0380

def z448 : W := mkw 0x022826c5bf667deb 0xa01141362dfb33ef 0xe6681fc7ffe67fff 0xdf3340fe3fff33ff

def z449 : W := mkw 0x0228048408440008 0x0011402420422000 0xc6681fc719e6000f 0xde3340fe38cf3000

def z450 : W := mkw 0x57af9ed7096650a8 0xa2bd7cf6b84b3285 0xc7ee1fc719e671ef 0xde3f70fe38cf338f

def z451 : W := mkw 0x0083101a02088702 0x10041880d0104438 0x819710380619cf95 0x6c0cb881c030ce7c

def z452 : W := mkw 0x2a7847ed49fe52b8 0xe153c23f6a4ff295 0x407803ff01fe0000 0x8203c01ff80ff000

def z453 : W := mkw 0x1581ba41bf667deb 0xa0ac0dd20dfb33ef 0xbf81fc00ffe67fff 0x7dfc0fe007ff33ff

def z454 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc66803c719e6000c 0xde33401e38cf3000

def z455 : W := mkw 0x1f7c000008440008 0x00fbe00000422000 0x9ffe000019e6000c 0xfcfff00000cf3000

def z456 : W := mkw 0x5fffddb648d5001c 0x02fffeedb246a800 0x5fffffff01ff8003 0xfafffffff80ffc00

def z457 : W := mkw 0x2a7847ed49fe52b8 0xe153c23f6a4ff295 0xc6781fff19fe71ef 0xde33c0fff8cff38f

def z458 : W := mkw 0x0000020101024080 0x0000001008081204 0xc6081e07190671ef 0xde3040f038c8338f

def z459 : W := mkw 0x1f7c04c4dcf5103c 0xa0fbe02626e7a881 0x3e600dc0f8e0306a 0x11f3006e07c70183

def z460 : W := mkw 0x0850000000000000 0x0042800000000000 0x1870000000000000 0xb8c3800000000000

def z461 : W := mkw 0x02a916c50b6655aa 0xa01548b6285b32ad 0xc7e91fc71fe67fff 0xfe3f48fe38ff33ff

def z462 : W := mkw 0x1f7c06c5ddf750bc 0xa0fbe0362eefba85 0xfe681fc7f9e671ef 0xdff340fe3fcf338f

def z463 : W := mkw 0x0228000008440008 0x0011400000422000 0x8608000018060000 0x4430400000c03000

def z464 : W := mkw 0x2afb77ff6bfeffba 0xf157dbbffb5ff7fd 0xffffffffffffffff 0xffffffffffffffff

def z465 : W := mkw 0x28d3713a6298af12 0x51469b89d314c578 0x3997e038e6198e10 0x21ccbf01c730cc70

def z466 : W := mkw 0x57af9c9600000000 0x02bd7ce4b0000000 0x1f8ffc0700000003 0x78fc7fe038000000

def z467 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81fc00fe000ff0 0x65fc0fe007f0007f

def z468 : W := mkw 0x3f7c6128fcdd2a1c 0x41fbe30947e6e950 0xbfffe038ffff8e1c 0xfdffff01c7fffc70

def z469 : W := mkw 0x57af9c9600000000 0x02bd7ce4b0000000 0x47ee1fc700000003 0xda3f70fe38000000

def z470 : W := mkw 0x0000220821086a00 0x0000011041084350 0x7811e238e1187e1f 0xbbc08f11c708c3f0

def z471 : W := mkw 0x0002021b030ac782 0x10001010d818563c 0xc01e023f071fcf94 0x8600f011f838fe7c

def z472 : W := mkw 0x5f7e45b6dcd5001c 0x02fbf22db6e6a800 0xfffe03ffffff801c 0xfffff01ffffffc00

def z473 : W := mkw 0x1581b80022002d43 0x00ac0dc00110016a 0x1f81fc0000007fe3 0x78fc0fe0000003ff

def z474 : W := mkw 0x3581ba48f7b87f53 0xc1ac0dd247bdc3fa 0xbf81fc00fff87fff 0x7dfc0fe007ffc3ff

def z475 : W := mkw 0x0228000008440008 0x0011400000422000 0x87fe00001fff801c 0xfc3ff00000fffc00

def z476 : W := mkw 0x1d540000d4910014 0x00eaa00006a48800 0xb99e0000e71f8014 0xedccf0000738fc00

def z477 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf9ffc00ff1fffff 0xfdfcffe007f8ffff

def z478 : W := mkw 0x022a06df096ed2a8 0xb0115036f84b7695 0x407e03ff01ff8000 0x8203f01ff80ffc00

def z479 : W := mkw 0x57af9c97084600a8 0x22bd7ce4b8423005 0x878e1c07180601e0 0x443c70e038c0300f

def z480 : W := mkw 0x48d3ddb600000000 0x02469eedb0000000 0x5871ffff00000003 0xbac38ffff8000000

def z481 : W := mkw 0x0228000000000000 0x0011400000000000 0x0668000000000000 0xd833400000000000

def z482 : W := mkw 0x2a7867ec61b87a10 0xc153c33f630dc3d0 0x7e79ffffe1f87e1f 0xfbf3cfffff0fc3f0

def z483 : W := mkw 0x1f7c000094000000 0x00fbe00004a00000 0xbffe0000fe00001c 0xfdfff00007f00000

def z484 : W := mkw 0x00002000b4002841 0x0000010005a00142 0x20000000f8003068 0x0100000007c00183

def z485 : W := mkw 0x7ffffdf660b03810 0xc3ffffefb30581c0 0x7fffffffe0e0300b 0xfbffffffff070180

def z486 : W := mkw 0x2850436841b85210 0xc142821b420dc290 0x407003f801f8700f 0x9a03801fc00fc380

def z487 : W := mkw 0x20002248fdfd7a1c 0xc100011247efebd0 0xa0000000fffffe1c 0x0500000007fffff0

def z488 : W := mkw 0x172c06c59d6750ac 0xa0b960362ceb3a85 0xc7ee1fc71fe7f1ef 0xde3f70fe38ff3f8f

def z489 : W := mkw 0x0a7847e5096650a8 0xa053c23f284b3285 0xde79ffff19e671ef 0xfef3cffff8cf338f

def z490 : W := mkw 0x3f7c2248fdfd7a1c 0xc1fbe11247efebd0 0xbffe0000fffffe1c 0xfdfff00007fffff0

def z491 : W := mkw 0x0000200020002800 0x0000010001000140 0x20000000e0007e1c 0x01000000070003f0

def z492 : W := mkw 0x0000020801084200 0x0000001040084210 0x0000000001184e14 0x000000000008c270

def z493 : W := mkw 0x022806c5012250a0 0xa011403628091285 0x46681fc7000071e3 0xda3340fe3800038f

def z494 : W := mkw 0x200067ed212a7aa0 0xe100033f690953d5 0x4001ffff00007fe3 0x02000ffff80003ff

def z495 : W := mkw 0x17a9bc84b6002d43 0x00bd4de425b0016a 0xffe9ffc7fe007fff 0xffff4ffe3ff003ff

def z496 : W := mkw 0x1dd1d92000000000 0x00ee8ec900000000 0x5ff1fff800000003 0xfaff8fffc0000000

def z497 : W := mkw 0x1f7ca800fcd5285d 0x00fbe54007e6a942 0xbffeec00ffffb07e 0xfdfff76007fffd83

def z498 : W := mkw 0x02ab16d7096650a8 0xa01558b6b84b3285 0xc7ff1fff19e671ef 0xfe3ff8fff8cf338f

def z499 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x3ff60000fef98018 0x31ffb00007f7cc00

def z500 : W := mkw 0x0083121301024080 0x0004189098081204 0xc19f123f01064185 0xee0cf891f808320c

def z501 : W := mkw 0x0000000100020080 0x0000000008001004 0x8008100700060180 0x440040803800300c

def z502 : W := mkw 0x0228048400000000 0x0011402420000000 0x06600dc000000002 0x1033006e00000000

def z503 : W := mkw 0x2a7c636869fd7a1c 0xc153e31b434febd0 0x787fe3f8e1fffe1f 0xbbc3ff1fc70ffff0

def z504 : W := mkw 0x2850616060b03810 0xc142830b030581c0 0x3861e1c0e0e07e1f 0x39c30f0e070703f0

def z505 : W := mkw 0x422e049600000000 0x02117024b0000000 0x000e000700000000 0x0000700038000000

def z506 : W := mkw 0x15839a1b970ac7c3 0x10ac1cd0dcb8563e 0xc79f1e3f1f1fcff5 0xee3cf8f1f8f8fe7f

def z507 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008120700000001 0xca00409038000000

def z508 : W := mkw 0x5fffdff7096650a8 0xa2fffeffb84b3285 0x5fffffff01e60003 0xfafffffff80f3000

def z509 : W := mkw 0x00811209030ac782 0x100408904818563c 0x81811000071fcf95 0x6c0c08800038fe7c

def z510 : W := mkw 0x0081bec523227de3 0xa0040df6291913ef 0x4001ffc700007fe3 0x02000ffe380003ff

def z511 : W := mkw 0x0083125b032ad782 0x90041892d81956bc 0xc1ff13ff07ffff9f 0xfe0ff89ff83ffffc

def z512 : W := mkw 0x2081fb6823287f43 0xc1040fdb411943fa 0x4001fff800007fe3 0x02000fffc00003ff

def z513 : W := mkw 0x2000636861b87a10 0xc100031b430dc3d0 0x6001e3f8e1f87e1f 0x03000f1fc70fc3f0

def z514 : W := mkw 0x1f7c0240ddf5501c 0x80fbe01206efaa80 0xfffe03c0fffff01f 0xfffff01e07ffff80

def z515 : W := mkw 0x0850432801084200 0x0042821940084210 0x5871e3f801184e17 0xbac38f1fc008c270

def z516 : W := mkw 0x4aff55b600000000 0x0257faadb0000000 0x41ff13ff00000001 0xea0ff89ff8000000

def z517 : W := mkw 0x2000616020203800 0xc100030b010101c0 0x0000e1c000003002 0x0000070e00000180

def z518 : W := mkw 0x1ffdb800fed52d5f 0x00ffedc007f6a96a 0xbfe1fc00fee07fff 0x7dff0fe007f703ff

def z519 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x818e1007071fcf94 0x440c70803838fe7c

def z520 : W := mkw 0x00000209dfdfc79e 0x100000104efefe3c 0xa0000000ffffcf9c 0x0500000007fffe7c

def z521 : W := mkw 0x6a7e47fe41b85210 0xc353f23ff20dc290 0x407e03ff01f80000 0x8203f01ff80fc000

def z522 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff071f8017 0xfefffffff838fc00

def z523 : W := mkw 0x00000241ddf750bc 0xa00000120eefba85 0xa0000000fffff1fc 0x0500000007ffff8f

def z524 : W := mkw 0x172806c59d6650a8 0xa0b940362ceb3285 0xffe81fc7ffe671ff 0xffff40fe3fff338f

def z525 : W := mkw 0x15839813960285c3 0x10ac1cc09cb0142e 0x878e1c071e0781e0 0x443c70e038f03c0f

def z526 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x4197123f0619cf91 0x220cb891f830ce7c

def z527 : W := mkw 0x1f7c0484dcd5001c 0x00fbe02426e6a800 0xfffe1fc7ffff801f 0xfffff0fe3ffffc00

def z528 : W := mkw 0x1583ba1bb70aefc3 0x10ac1dd0ddb8577e 0xff81fe3ffe007fff 0x7ffc0ff1fff003ff

def z529 : W := mkw 0x000006c5012250a0 0xa000003628091285 0xc6001fc7180071ef 0x5e3000fe38c0038f

def z530 : W := mkw 0x1581980000000000 0x00ac0cc000000000 0x07801c0000000000 0x403c00e000000000

def z531 : W := mkw 0x5fffdfbf010ac280 0x12fffefdf8085614 0x5fffffff011f8003 0xfafffffff808fc00

def z532 : W := mkw 0x28d1736863b87f12 0xc1468b9b431dc3f8 0xf9f1f3f8e7f87f9f 0xffcf8f9fc73fc3fc

def z533 : W := mkw 0x0aff121b4bdfc79e 0x1057f890da5efe3c 0xc1ff123f07ffcf95 0xee0ff891f83ffe7c

def z534 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x607003f8e1f87e1c 0x8303801fc70fc3f0

def z535 : W := mkw 0x1581b800fed52d5f 0x00ac0dc007f6a96a 0xbf81fc00ffffffff 0x7dfc0fe007ffffff

def z536 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbe680000f9e6000c 0xddf3400007cf3000

def z537 : W := mkw 0x0000412000000000 0x0000020900000000 0x4001e3f800000003 0x02000f1fc0000000

def z538 : W := mkw 0x022806cd096e52a8 0xa0114036684b7295 0xc6791fff19fe7fff 0xfe33c8fff8cff3ff

def z539 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x3860e1c0e1f87e1e 0x11c3070e070fc3f0

def z540 : W := mkw 0x1fff121b030ac782 0x10fff890d818563c 0xdfff123f071fcf95 0xfefff891f838fe7c

def z541 : W := mkw 0x5fffd93200000000 0x02fffec990000000 0x1fffe03800000000 0xf8ffff01c0000000

def z542 : W := mkw 0x0081100002000502 0x0004088000100028 0x0181000006000e10 0x200c080000300070

def z543 : W := mkw 0x0000200020002800 0x0000010001000140 0x3800e000e000300a 0x11c0070007000180

def z544 : W := mkw 0x28d3737b63baff92 0xd1469b9bdb1dd7fc 0x7871f3ffe1f87f9f 0xbbc38f9fff0fc3fc

def z545 : W := mkw 0x2850636963baff92 0xd142831b4b1dd7fc 0xf871e3f8e7ffff9f 0xbfc38f1fc73ffffc

def z546 : W := mkw 0x5f7ccde408641028 0xa2fbe66f20432081 0x1e60edc018e0306a 0x10f3076e00c70183

def z547 : W := mkw 0x0000000000000000 0x0000000000000000 0x0196000006198010 0x200cb0000030cc00

def z548 : W := mkw 0x1dd7121bd79bc796 0x10eeb890debcde3c 0xf99f123fe71fcf95 0xefccf891ff38fe7c

def z549 : W := mkw 0x0850000040900010 0x0042800002048000 0x0070000001f80000 0x80038000000fc000

def z550 : W := mkw 0x5ffffdb620002800 0x02ffffedb1000140 0x7fffffffe0007e1f 0xfbffffffff0003f0

def z551 : W := mkw 0x00000241096650a8 0xa0000012084b3285 0x86001c0019e671ef 0x5c3000e000cf338f

def z552 : W := mkw 0x5ffffdb622002d43 0x02ffffedb110016a 0x5fffffff00007fe3 0xfafffffff80003ff

def z553 : W := mkw 0x222826cd69fe7ab8 0xe11141366b4ff3d5 0xe6681fc7f9fe7fff 0xdf3340fe3fcff3ff

def z554 : W := mkw 0x5ffffdb6b4002841 0x02ffffedb5a00142 0x7ffffffff800306b 0xfbffffffffc00183

def z555 : W := mkw 0x2852437b41bad290 0xd142921bda0dd694 0x407e03ff01ff8000 0x8203f01ff80ffc00

def z556 : W := mkw 0x022806c409645028 0xa0114036204b2281 0x46600fc019e0706f 0x9a33007e00cf0383

def z557 : W := mkw 0x022804c408641028 0xa011402620432081 0x46681fc718e0306b 0xda3340fe38c70183

def z558 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc009123f01064f85 0xce004891f808327c

def z559 : W := mkw 0x57af9e9f030ac782 0x12bd7cf4f818563c 0xc79f1e3f071fcf95 0xee3cf8f1f838fe7c

def z560 : W := mkw 0x1ffdb800b6002d43 0x00ffedc005b0016a 0xbffffc00fe007fff 0xfdffffe007f003ff

def z561 : W := mkw 0x000002490b6ed7aa 0xb0000012485b76bd 0x800000001ffffffc 0x0400000000ffffff

def z562 : W := mkw 0x0002021b010ac280 0x10001010d8085614 0xc01e123f011fc185 0xce00f091f808fe0c

def z563 : W := mkw 0x17adb800be452d4f 0x00bd6dc005f2296a 0xbf8ffc00fe07ffff 0x7dfc7fe007f03fff

def z564 : W := mkw 0x0081b800b6002d43 0x00040dc005b0016a 0xa001fc00fe007fff 0x05000fe007f003ff

def z565 : W := mkw 0x5f7ccda400000000 0x02fbe66d20000000 0x5e71eff800000003 0xbaf38f7fc0000000

def z566 : W := mkw 0x00000485000200a0 0x2000002428001005 0x00001c07000001e0 0x000000e03800000f

def z567 : W := mkw 0x5f7e45b600000000 0x02fbf22db0000000 0x5ffe03ff00000000 0xfafff01ff8000000

def z568 : W := mkw 0x00000000d4910014 0x0000000006a48800 0x20000000e6198010 0x010000000730cc00

def z569 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6681fc719e601e0 0xc63340fe38cf300f

def z570 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x46680fc719e6306a 0x9233407e38cf3183

def z571 : W := mkw 0x08d3121b439ac792 0x10469890da1cd63c 0xf9ff123fe7ffcf9d 0xffcff891ff3ffe7c

def z572 : W := mkw 0x1500a800b4002841 0x00a8054005a00142 0x3800e000e0000000 0x01c0070007000000

def z573 : W := mkw 0x1f7c2000fcd5281c 0x00fbe10007e6a940 0xbfffe000fffffe1f 0xfdffff0007fffff0

def z574 : W := mkw 0x1ffd980000000000 0x00ffecc000000000 0x1ffffc0000000003 0xf8ffffe000000000

def z575 : W := mkw 0x0000000040900010 0x0000000002048000 0x20000000e1f8001c 0x01000000070fc000

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008000001060004 0xcc00400000083000

def z577 : W := mkw 0x5fffd932dcd5001c 0x02fffec996e6a800 0xbfffe038ffff801c 0xfdffff01c7fffc00

def z578 : W := mkw 0x00000241096650a8 0xa0000012084b3285 0xc06003c019e671ef 0x9e03001e00cf338f

def z579 : W := mkw 0x0083ba1b230aefc3 0x10041dd0d918577e 0x4001fe3f00007fe3 0x02000ff1f80003ff

def z580 : W := mkw 0x022804c408641028 0xa011402620432081 0x86601dc018e071ef 0x5c3300ee00c7038f

def z581 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x87fe00001fff8000 0xc43ff00000fffc00

def z582 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x1ff7edf800000002 0x30ffbf6fc0000000

def z583 : W := mkw 0x1581980000000000 0x00ac0cc000000000 0x1981e00000000000 0x20cc0f0000000000

def z584 : W := mkw 0x0850412000000000 0x0042820900000000 0x1811e03800000000 0x20c08f01c0000000

def z585 : W := mkw 0x5fffdfb701024080 0x02fffefdb8081204 0xdfffffff01064187 0xfefffffff808320c

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0x4011023800000001 0xaa008811c0000000

def z587 : W := mkw 0x0000200020002800 0x0000010001000140 0xbe01fc00f8007fff 0x7df00fe007c003ff

def z588 : W := mkw 0x02ab169f030ac782 0x101558b4f818563c 0xc7ff1fff071fcf97 0xfe3ff8fff838fe7c

def z589 : W := mkw 0x7f7cede460b03810 0xc3fbe76f230581c0 0x3e60edc0e0e0300a 0x11f3076e07070180

def z590 : W := mkw 0x17a9b800be442d4b 0x00bd4dc005f2216a 0xbfe9fc00ffe67fff 0xfdff4fe007ff33ff

def z591 : W := mkw 0x7ffffffef7b87f53 0xc3fffffff7bdc3fa 0xfffffffffff87fff 0xffffffffffffc3ff

def z592 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbf9e0000fe1f8010 0x65fcf00007f0fc00

def z593 : W := mkw 0x1581100096000502 0x00ac088004b00028 0xbf811000fe004f9d 0x7dfc088007f0027c

def z594 : W := mkw 0x0850024041b05010 0x80428012020d8280 0x787003c0e1f8701f 0xbbc3801e070fc380

def z595 : W := mkw 0x0000000000000000 0x0000000000000000 0x06001c0000000003 0x583000e000000000

def z596 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x86600dc019e671ee 0x1433006e00cf338f

def z597 : W := mkw 0x5dd7f932b6002d43 0x02eebfc995b0016a 0xbf97fc38fe007fff 0x7dfcbfe1c7f003ff

def z598 : W := mkw 0x3f7c6160fcf5381c 0xc1fbe30b07e7a9c0 0x3e60e1c0f8e0300a 0x11f3070e07c70180

def z599 : W := mkw 0x0002001200000000 0x0000100090000000 0x401e023f00000000 0x8200f011f8000000

def z600 : W := mkw 0x17a9bc85be462deb 0x20bd4de42df2316f 0xbf89fc07fe067fff 0x7dfc4fe03ff033ff

def z601 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x81970038071fcf94 0x240cb801c038fe7c

def z602 : W := mkw 0x1f7c04c4dcf5103c 0xa0fbe02626e7a881 0xbffe0dc0ffffb07e 0xfdfff06e07fffd83

def z603 : W := mkw 0x1583ba1bb70aefc3 0x10ac1dd0ddb8577e 0xf99ff23fe71fcf95 0xefccff91ff38fe7c

def z604 : W := mkw 0x0083121a0308c702 0x10041890d0184638 0x419702380719ce15 0xaa0cb811c038ce70

def z605 : W := mkw 0x1581980002000502 0x00ac0cc000100028 0x9f81fc0006004f97 0x7cfc0fe00030027c

def z606 : W := mkw 0x1500000094000000 0x00a8000004a00000 0xbf801c00fe0071ff 0x7dfc00e007f0038f

def z607 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x3811e038e1f87e1c 0x21c08f01c70fc3f0

def z608 : W := mkw 0x0000000802088702 0x1000000040104438 0x0000000006198e10 0x000000000030cc70

def z609 : W := mkw 0x0228020109464088 0x00114010084a3204 0xc668120719e6418d 0xde33409038cf320c

def z610 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6081fc7180671e3 0x463040fe38c0338f

def z611 : W := mkw 0x2850416040b01010 0xc142820b02058080 0x006001c000e00000 0x0003000e00070000

def z612 : W := mkw 0x1500880094000041 0x00a8044004a00002 0x06000c0018000060 0x0030006000c00003

def z613 : W := mkw 0x2a7865e468f43838 0xe153c32f2347a1c1 0x3e60edc0f8e0306a 0x11f3076e07c70183

def z614 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x3ffe0000f8e00008 0xf9fff00007c70000

def z615 : W := mkw 0x5fffdff7ddf750bc 0xa2fffeffbeefba85 0xfffffffffffff1ff 0xffffffffffffff8f

def z616 : W := mkw 0x28d3537b43bad792 0xd1469a9bda1dd6bc 0xc1ff13ff07ffcf95 0xee0ff89ff83ffe7c

def z617 : W := mkw 0x0083101302028582 0x100418809810142c 0xc19f123f06078181 0xee0cf891f8303c0c

def z618 : W := mkw 0x1728aec5bd6678e9 0xa0b945762deb33c7 0xfe68ffc7f9e671ef 0xdff347fe3fcf338f

def z619 : W := mkw 0x2850412840980210 0x414282094204c010 0x0010003800180000 0x00008001c000c000

def z620 : W := mkw 0x5ffddda400000000 0x02ffeeed20000000 0x1fe1fdc000000003 0x78ff0fee00000000

def z621 : W := mkw 0x5fffdff601205000 0x82fffeffb0090280 0x5fffffff01e0700f 0xfafffffff80f0380

def z622 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x4071e3f801f87e03 0x82038f1fc00fc3f0

def z623 : W := mkw 0x2850612060902810 0x4142830903048140 0x3800e000e0000000 0x01c0070007000000

def z624 : W := mkw 0x0081b80022002d43 0x00040dc00110016a 0x8601fc0018007fef 0x5c300fe000c003ff

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0x38000000e000001c 0x39c0000007000000

def z626 : W := mkw 0x0a7806c549f650b8 0xa053c0362a4fb285 0xfe781fc7f9fe71ff 0xfff3c0fe3fcff38f

def z627 : W := mkw 0x00002000b6002d43 0x0000010005b0016a 0xa6001c00fe007fff 0x5d3000e007f003ff

def z628 : W := mkw 0x2850436841b85210 0xc142821b420dc290 0x787003f8e1f8001c 0xbbc3801fc70fc000

def z629 : W := mkw 0x1f7c2000fed52d5f 0x00fbe10007f6a96a 0xbffe0000fffffffc 0xfdfff00007ffffff

def z630 : W := mkw 0x0000224021207800 0x80000112010903c0 0x7861e3c0e1e07e1f 0xbbc30f1e070f03f0

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x406003c000000003 0x9a03001e00000000

def z632 : W := mkw 0x2852637b61bafa90 0xd142931bdb0dd7d4 0x787fe3ffe1fffe1f 0xbbc3ff1fff0ffff0

def z633 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc06813c701e64185 0xce03409e380f320c

def z634 : W := mkw 0x0081100000000000 0x0004088000000000 0x0181100000000001 0x680c088000000000

def z635 : W := mkw 0x17ad98009e45054f 0x00bd6cc004f2282a 0x878e1c001e0781e0 0x443c70e000f03c0f

def z636 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x406803c701e6700f 0x9a03401e380f3380

def z637 : W := mkw 0x5fffdfbf030ac782 0x12fffefdf818563c 0x5fffffff00004f83 0xfafffffff800027c

def z638 : W := mkw 0x3dd1f960f6b03d53 0xc1ee8fcb07b581ea 0xbfe1fdc0fee07fff 0x7dff0fee07f703ff

def z639 : W := mkw 0x0000000094000000 0x0000000004a00000 0xa0000000fe00001c 0x0500000007f00000

def z640 : W := mkw 0x000006c5096650a8 0xa0000036284b3285 0xc0001fc719e671ef 0x060000fe38cf338f

def z641 : W := mkw 0x222867ed296e7aa8 0xe111433f694b73d5 0xc669ffff19e67fef 0xde334ffff8cf33ff

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000000700f 0x1800000000000380

def z643 : W := mkw 0x7ffffdbe60982a10 0x43ffffedf304c150 0x7fffffffe0180e13 0xfbffffffff00c070

def z644 : W := mkw 0x0000024801285200 0x8000001240094290 0x407103f801f87e1f 0xba03881fc00fc3f0

def z645 : W := mkw 0x2850612860982a10 0x414283094304c150 0x3811e038e0187e1f 0x39c08f01c700c3f0

def z646 : W := mkw 0x0000020101024080 0x0000001008081204 0x4008020701060000 0x8200401038083000

def z647 : W := mkw 0x0000a80020002841 0x0000054001000142 0x0000ec0000003062 0x0000076000000183

def z648 : W := mkw 0x00000000dcd5001c 0x0000000006e6a800 0x20000000f8e00008 0x0100000007c70000

def z649 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x1f9ffc3f00000000 0x60fcffe1f8000000

def z650 : W := mkw 0x1fff101200000000 0x00fff88090000000 0x5fff123f00000001 0xfafff891f8000000

def z651 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x47fe1fff00000000 0xc23ff0fff8000000

def z652 : W := mkw 0x2000224861b87a10 0xc1000112430dc3d0 0x3801e000e1f87e1f 0x39c00f00070fc3f0

def z653 : W := mkw 0x1581ba01b7026dc3 0x00ac0dd00db8136e 0xff89fe07ff067fff 0xfffc4ff03ff833ff

def z654 : W := mkw 0x4a7c45a400000000 0x0253e22d20000000 0x006001c000000000 0x0003000e00000000

def z655 : W := mkw 0x0228048400000000 0x0011402420000000 0x406803c700000000 0x8203401e38000000

def z656 : W := mkw 0x0002021b010ac280 0x10001010d8085614 0x401f023f011fce15 0xaa00f811f808fe70

def z657 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbfe00000fee0001c 0x7dff000007f70000

def z658 : W := mkw 0x1dd5b800f6912d57 0x00eeadc007b4896a 0xbf97fc00fe19ffff 0x7dfcbfe007f0cfff

def z659 : W := mkw 0x15002000b4002800 0x00a8010005a00140 0xbf81e000fe007e1f 0x7dfc0f0007f003f0

def z660 : W := mkw 0x022804c408641028 0xa011402620432081 0x86680dc019e6306e 0xdc33406e00cf3183

def z661 : W := mkw 0x5fff9c96dcd5001c 0x02fffce4b6e6a800 0xbffe1c07ffff801c 0xfdfff0e03ffffc00

def z662 : W := mkw 0x3d546368f5b97a14 0xc1eaa31b47adcbd0 0x79f7e3f8e7f9fe1f 0xbbcfbf1fc73fcff0

def z663 : W := mkw 0x0a7c000000000000 0x0053e00000000000 0x007e000000000000 0x8003f00000000000

def z664 : W := mkw 0x1ffd9800dcd5001c 0x00ffecc006e6a800 0xbffffc00ffff801f 0xfdffffe007fffc00

def z665 : W := mkw 0x0228048408440028 0x2011402420422001 0x06000c0018000060 0x0030006000c00003

def z666 : W := mkw 0x00813000b6002d43 0x0004098005b0016a 0xa1811000fe007ffd 0x6d0c088007f003ff

def z667 : W := mkw 0x2000636821287a00 0xc100031b410943d0 0x4061e3f801e07e0f 0x9a030f1fc00f03f0

def z668 : W := mkw 0x17abbedfbf6effeb 0xb0bd5df6fdfb77ff 0xffffffffffffffff 0xffffffffffffffff

def z669 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x3e700000f9f8001c 0xb9f3800007cfc000

def z670 : W := mkw 0x17a99c859e4605eb 0x20bd4ce42cf2302f 0x87881c071e0601e0 0x443c40e038f0300f

def z671 : W := mkw 0x1f7c000040900010 0x00fbe00002048000 0x3ffe0000e1f8001c 0xf9fff000070fc000

def z672 : W := mkw 0x17a99c8400000000 0x00bd4ce420000000 0x5fe9ffc700000003 0xfaff4ffe38000000

def z673 : W := mkw 0x0002021b010ac280 0x10001010d8085614 0xc19e023f071f8014 0xee0cf011f838fc00

def z674 : W := mkw 0x5dd7f932b6002d43 0x02eebfc995b0016a 0x3997e038e6000e10 0x21ccbf01c7300070

def z675 : W := mkw 0x1500000094000000 0x00a8000004a00000 0xbf9e0000ff1f801c 0xfdfcf00007f8fc00

def z676 : W := mkw 0x0083101202008502 0x1004188090100428 0x0186000006018000 0x000c300000300c00

def z677 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x4011123f01184f95 0xaa008891f808c27c

def z678 : W := mkw 0x2850636969fe7ab8 0xe142831b4b4ff3d5 0xf871e3f8f9fe7fff 0xbfc38f1fc7cff3ff

def z679 : W := mkw 0x1f7c000000000000 0x00fbe00000000000 0x1e60000000000000 0x10f3000000000000

def z680 : W := mkw 0x7f7cefec61b87a10 0xc3fbe77f630dc3d0 0x7e71eff8e1f87e1f 0xbbf38f7fc70fc3f0

def z681 : W := mkw 0x3f7c67edfdff7abc 0xe1fbe33f6feffbd5 0xffffffffffffffff 0xffffffffffffffff

def z682 : W := mkw 0x7fffffff69fe7ab8 0xe3fffffffb4ff3d5 0xfffffffff9fe7fff 0xffffffffffcff3ff

def z683 : W := mkw 0x3d506368f5b87a10 0xc1ea831b47adc3d0 0xfff1e3f8fff87e1f 0xffff8f1fc7ffc3f0

def z684 : W := mkw 0x3ffdfb68fffd7f5f 0xc1ffefdb47ffebfa 0xfffffff8ffffffff 0xffffffffc7ffffff

def z685 : W := mkw 0x0a7c0000dcd5001c 0x0053e00006e6a800 0xa07e0000ffff801c 0x8503f00007fffc00

def z686 : W := mkw 0x1dd1b800f6902d53 0x00ee8dc007b4816a 0xbff1fc00fff87fff 0xfdff8fe007ffc3ff

def z687 : W := mkw 0x3d546128f4992a14 0x41eaa30947a4c950 0x3997e038e6198e10 0x21ccbf01c730cc70

def z688 : W := mkw 0x022806cd0b6ed7aa 0xb0114036685b76bd 0xc6681fc71fffffff 0xde3340fe38ffffff

def z689 : W := mkw 0x57af9c9696000543 0x02bd7ce4b4b0002a 0x878e1c071e0001e0 0x443c70e038f0000f

def z690 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x86081c0719e671ec 0x443040e038cf338f

def z691 : W := mkw 0x172c00009c45000c 0x00b9600004e22800 0x879e00001f1f8014 0xec3cf00000f8fc00

def z692 : W := mkw 0x5dd7d93200000000 0x02eebec990000000 0x1f97fc3800000003 0x78fcbfe1c0000000

def z693 : W := mkw 0x02ab169f0b4ec7aa 0x301558b4f85a763d 0xc79f1e3f1f1fcff5 0xee3cf8f1f8f8fe7f

def z694 : W := mkw 0x1581980096000543 0x00ac0cc004b0002a 0x87801c001e0071ef 0x5c3c00e000f0038f

def z695 : W := mkw 0x0000024001205000 0x8000001200090280 0xc6601fc019e071ef 0xde3300fe00cf038f

def z696 : W := mkw 0x1ffdb800fed52d5f 0x00ffedc007f6a96a 0xbfffe000ffff8e1c 0xfdffff0007fffc70

def z697 : W := mkw 0x3f7c636861b87a10 0xc1fbe31b430dc3d0 0x7fffe3f8e1f87e1f 0xfbffff1fc70fc3f0

def z698 : W := mkw 0x0081b80022002d43 0x00040dc00110016a 0x8181fc0006007ff7 0x6c0c0fe0003003ff

def z699 : W := mkw 0x0081120103024582 0x000408900818122c 0xc189120707064f95 0xee0c48903838327c

def z700 : W := mkw 0x0083101a02088702 0x10041880d0104438 0x419f123f06198e11 0xea0cf891f830cc70

def z701 : W := mkw 0x2850612860982a10 0x414283094304c150 0x3871e038e1f80e1c 0xb9c38f01c70fc070

def z702 : W := mkw 0x0000000096000543 0x0000000004b0002a 0x800000001e0001e0 0x0400000000f0000f

def z703 : W := mkw 0x008316df032ad7a2 0xb00418b6f81956bd 0x40011fff00007fe3 0x020008fff80003ff

def z704 : W := mkw 0x0002021b010ac280 0x10001010d8085614 0x4000023f00000000 0x02000011f8000000

def z705 : W := mkw 0x57af9c9600000000 0x02bd7ce4b0000000 0x479f1e3f00000001 0xea3cf8f1f8000000

def z706 : W := mkw 0x0000020101024080 0x0000001008081204 0xc19e1207071fc195 0xee0cf0903838fe0c

def z707 : W := mkw 0x1fff121bdfdfc79e 0x10fff890defefe3c 0x7e61123ff8e04f89 0x13f30891ffc7027c

def z708 : W := mkw 0x1d5406c5d5b350b4 0xa0eaa0362ead9a85 0x79961fc7e619f1f3 0x23ccb0fe3f30cf8f

def z709 : W := mkw 0x20002249232aff82 0xd1000112491957fc 0x0000000000007f80 0x00000000000003fc

def z710 : W := mkw 0x5fffddb696000543 0x02fffeedb4b0002a 0xfffffffffe0001ff 0xfffffffffff0000f

def z711 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff1800306b 0xfafffffff8c00183

def z712 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f87e13 0xa3c38f1fc70fc3f0

def z713 : W := mkw 0x4a7e65b6b6002d43 0x0253f32db5b0016a 0xe07e03fffe007ffc 0x8703f01ffff003ff

def z714 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xf871f3f8e1f87f9f 0xffc38f9fc70fc3fc

def z715 : W := mkw 0x0081300022002d02 0x0004098001100168 0xbf81fc00fe007fff 0x7dfc0fe007f003ff

def z716 : W := mkw 0x5fffddb602000502 0x02fffeedb0100028 0xdfffffff1e007fff 0xfefffffff8f003ff

def z717 : W := mkw 0x2850636961ba7a90 0xc142831b4b0dd3d4 0xfe79fffff9fe7fff 0xfff3cfffffcff3ff

def z718 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc79f123f1f1fcf9d 0xfe3cf891f8f8fe7c

def z719 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff000071e3 0xfafffffff800038f

def z720 : W := mkw 0x0083101b020a8782 0x10041880d810543c 0x019f003f061f8e10 0x200cf801f830fc70

def z721 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f123f071f8f90 0xe60cf891f838fc7c

def z722 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe0c00ffffb07e 0xfdfff06007fffd83

def z723 : W := mkw 0x1d540000d4910014 0x00eaa00006a48800 0xb9fe0000e7ff801c 0xfdcff000073ffc00

def z724 : W := mkw 0x5f7ccfad030ac782 0x12fbe67d6818563c 0x9e60edc0071fcf96 0x14f3076e0038fe7c

def z725 : W := mkw 0x5dd7ddb600000000 0x02eebeedb0000000 0x5997e3ff00000000 0x22ccbf1ff8000000

def z726 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7861e3f8e0e07e1f 0x3bc30f1fc70703f0

def z727 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc7ee1fc71fe7f1ef 0xde3f70fe38ff3f8f

def z728 : W := mkw 0x57af9c979e4605eb 0x22bd7ce4bcf2302f 0x878e1c071e0601e0 0x443c70e038f0300f

def z729 : W := mkw 0x022806cd096e52a8 0xa0114036684b7295 0xc6691fff19e67fef 0xde3348fff8cf33ff

def z730 : W := mkw 0x08d3513200000000 0x00469a8990000000 0x5871f3ff00000003 0xbac38f9ff8000000

def z731 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff00000000 0xe2fffffff8000000

def z732 : W := mkw 0x1f7c45a4dcd5001c 0x00fbe22d26e6a800 0xffffffffffff801f 0xfffffffffffffc00

def z733 : W := mkw 0x5dd7db73096650a8 0xa2eebedb984b3285 0x9997e03819e671ec 0x24ccbf01c0cf338f

def z734 : W := mkw 0x5f7ceda4fcd5285d 0x02fbe76d27e6a942 0x3e60edc0f8e0306a 0x11f3076e07c70183

def z735 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc7fe1fc719e671ef 0xfe3ff0fe38cf338f

def z736 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe0000ffff8010 0xe5fff00007fffc00

def z737 : W := mkw 0x77afbede61b87a10 0xc3bd7df6f30dc3d0 0x278e1c07e1f87e1c 0x413c70e03f0fc3f0

def z738 : W := mkw 0x0850636021207800 0x8042831b010903c0 0x7871e3f8e1e07e1f 0xbbc38f1fc70f03f0

def z739 : W := mkw 0x0afdb8006ad52d5f 0x0057edc00356a96a 0x007ffc0001ffffe3 0x8003ffe0000fffff

def z740 : W := mkw 0x02ab14de0a6c972a 0xb01558a6f05364b9 0x07f70df81ef9be7a 0x303fb86fc0f7cdf3

def z741 : W := mkw 0x1581b80020002800 0x00ac0dc001000140 0xbf81fc00f8007fff 0x7dfc0fe007c003ff

def z742 : W := mkw 0x0083bedf232affe3 0xb0041df6f91957ff 0x4001ffff00007fe3 0x02000ffff80003ff

def z743 : W := mkw 0x0081b80022002d43 0x00040dc00110016a 0xbe01fc00f8007fff 0x7df00fe007c003ff

def z744 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbfffe000ffff801f 0xfdffff0007fffc00

def z745 : W := mkw 0x1d540000dcd5001c 0x00eaa00006e6a800 0x39960000e7ff8010 0x21ccb000073ffc00

def z746 : W := mkw 0x1500a800b4002841 0x00a8054005a00142 0xbe01fc00f8007fff 0x7df00fe007c003ff

def z747 : W := mkw 0x5dd7ddb600000000 0x02eebeedb0000000 0x59f7ffff00000003 0xbacfbffff8000000

def z748 : W := mkw 0x2000636821287a00 0xc100031b410943d0 0x7861e3f8e1e07e1f 0xbbc30f1fc70f03f0

def z749 : W := mkw 0x5587b812b6002d43 0x02ac3dc095b0016a 0xbf87fc00fe007fff 0x7dfc3fe007f003ff

def z750 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6691fc719e67fff 0xfe3348fe38cf33ff

def z751 : W := mkw 0x20002249ffffff9e 0xd10001124ffffffc 0xa0000000ffffff9c 0x0500000007fffffc

def z752 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6681fc719e671e3 0xc63340fe38cf338f

def z753 : W := mkw 0x372c6368bd6d7a0c 0xc1b9631b45eb6bd0 0xc78fe3f81e07fe03 0x463c7f1fc0f03ff0

def z754 : W := mkw 0x17a9bec5bf667deb 0xa0bd4df62dfb33ef 0x79e9e3c7e7e60e10 0xa3cf4f1e3f3f3070

def z755 : W := mkw 0x0083101202000502 0x0004188090100028 0xc19f123f071fcf95 0xee0cf891f838fe7c

def z756 : W := mkw 0x0002021b030ac782 0x10001010d818563c 0xc19e023f071fcf94 0xee0cf011f838fe7c

def z757 : W := mkw 0x5fffddb608440008 0x02fffeedb0422000 0x5fffffff01e60003 0xfafffffff80f3000

def z758 : W := mkw 0x000045a400000000 0x0000022d20000000 0x4001ffff00000003 0x02000ffff8000000

def z759 : W := mkw 0x5fffddb640900010 0x02fffeedb2048000 0x5fffffff01f80003 0xfafffffff80fc000

def z760 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff00004e17 0xfafffffff8000270

def z761 : W := mkw 0x0a7c000048d5001c 0x0053e0000246a800 0xb9fe0000e7ff801c 0xfdcff000073ffc00

def z762 : W := mkw 0x1fff513200000000 0x00fffa8990000000 0x5ffff3ff00000003 0xfaffff9ff8000000

def z763 : W := mkw 0x3dd1db68d7b85753 0xc1ee8edb46bdc2ba 0xc7f01ff81ff801e0 0xc63f80ffc0ffc00f

def z764 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xfffffffffee7800b 0xfffffffffff73c00

def z765 : W := mkw 0x0083101a02088702 0x10041880d0104438 0xc19f123f071f8e15 0xee0cf891f838fc70

def z766 : W := mkw 0x5fffddb694000041 0x02fffeedb4a00002 0x5fffffff18000063 0xfafffffff8c00003

def z767 : W := mkw 0x5f7ccda4dcd5001c 0x02fbe66d26e6a800 0xffffeff8ffff801f 0xffffff7fc7fffc00

def z768 : W := mkw 0x5fffddb69c440008 0x02fffeedb4e22000 0xffffffffffe6001f 0xffffffffffff3000

def z769 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xfe681fc7f9e671ff 0xfff340fe3fcf338f

def z770 : W := mkw 0x5dd7ddb600000000 0x02eebeedb0000000 0x5f97ffff00000003 0x7afcbffff8000000

def z771 : W := mkw 0x1f7c0484dcd5003c 0x20fbe02426e6a801 0xbffe0c00ffff807c 0xfdfff06007fffc03

def z772 : W := mkw 0x5fffddb694000000 0x02fffeedb4a00000 0x7ffffffff800000b 0xfbffffffffc00000

def z773 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf9ffc00fe007fff 0xfdfcffe007f003ff

def z774 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffe3ff00000000 0xfaffff1ff8000000

def z775 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xa7fe0000ffff801c 0xc53ff00007fffc00

def z776 : W := mkw 0x1f7c4120dcd5001c 0x00fbe20906e6a800 0xfffe03f8ffff801c 0xfffff01fc7fffc00

def z777 : W := mkw 0x48d3ddb600000000 0x02469eedb0000000 0x59ffffff00000003 0xfacffffff8000000

def z778 : W := mkw 0x0a7845a400000000 0x0053c22d20000000 0x5879e3ff00000003 0xbac3cf1ff8000000

def z779 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc67e1fc719fff1ef 0xde33f0fe38cfff8f

def z780 : W := mkw 0x5fffddb696000502 0x02fffeedb4b00028 0xfffffffffe004f9f 0xfffffffffff0027c

def z781 : W := mkw 0x4a7e45b600000000 0x0253f22db0000000 0x5e7fffff00000003 0xfaf3fffff8000000

def z782 : W := mkw 0x5fffddb648d5001c 0x02fffeedb246a800 0x5fffffff00e00003 0xfafffffff8070000

def z783 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f1e3f071ffff7 0xee0cf8f1f838ffff

def z784 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf91fc00ff187fff 0xfdfc8fe007f8c3ff

def z785 : W := mkw 0x57afddb600000000 0x02bd7eedb0000000 0x4601ffff00000003 0x02300ffff8000000

def z786 : W := mkw 0x57afddb600000000 0x02bd7eedb0000000 0x5f8fffff00000003 0x7afc7ffff8000000

def z787 : W := mkw 0x0083121a01084200 0x00041890d0084210 0xc19f123f071fce15 0xee0cf891f838fe70

def z788 : W := mkw 0x2850636961ba7ab0 0xe142831b4b0dd3d5 0x7871e3f8e1f87fff 0xbbc38f1fc70fc3ff

def z789 : W := mkw 0x5fffddb694010004 0x02fffeedb4a00800 0x5fffffff06018003 0xfafffffff8300c00

def z790 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xfffffffffee0001f 0xfffffffffff70000

def z791 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f023f071f8e14 0xee0cf811f838fc70

def z792 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xfffffffff9e6000f 0xffffffffffcf3000

def z793 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81fc00fe007ffc 0x65fc0fe007f003ff

def z794 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff011f8003 0xfafffffff808fc00

def z795 : W := mkw 0x1fff5132dcd5001c 0x00fffa8996e6a800 0xfffff3ffffff801f 0xffffff9ffffffc00

def z796 : W := mkw 0x1d540000dcd5001c 0x00eaa00006e6a800 0xb9f60000ffff801c 0xbdcfb00007fffc00

def z797 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81ec00fe007ffe 0x35fc0f6007f003ff

def z798 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f87e0b 0x93c38f1fc70fc3f0

def z799 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xf871e3f8f9f87fff 0xbfc38f1fc7cfc3ff

def z800 : W := mkw 0x2850616860b83a10 0xc142830b4305c1d0 0x3861e1f8e0e03e0a 0x11c30f0fc70701f0

def z801 : W := mkw 0x5fffddb648d40018 0x02fffeedb246a000 0xfffffffff9fe001f 0xffffffffffcff000

def z802 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff1800000f 0xfefffffff8c00000

def z803 : W := mkw 0x2850636961ba7a90 0xc142831b4b0dd3d4 0x7879e3ffe1fe7e1f 0xbbc3cf1fff0ff3f0

def z804 : W := mkw 0x2850616060b03810 0xc142830b030581c0 0x7871e3f8e0e07e1f 0xbbc38f1fc70703f0

def z805 : W := mkw 0x5fffddb602000502 0x02fffeedb0100028 0xdfffffff071fcf97 0xfefffffff838fe7c

def z806 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xde69ffc719e671ef 0xfef34ffe38cf338f

def z807 : W := mkw 0x48d3ddb640900010 0x02469eedb2048000 0x7871ffffe1f8001f 0xbbc38fffff0fc000

def z808 : W := mkw 0x0083125b032ad7a2 0xb0041892d81956bd 0xc19f123f071ffff5 0xee0cf891f838ffff

def z809 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff00004187 0xfefffffff800020c

def z810 : W := mkw 0x42abddb600000000 0x02155eedb0000000 0x4609ffff00000003 0x42304ffff8000000

def z811 : W := mkw 0x0850432841984210 0x00428219420cc210 0x7871e3f8e1f84e1f 0xbbc38f1fc70fc270

def z812 : W := mkw 0x1f7c8800dcd5001c 0x00fbe44006e6a800 0xbffeec00ffff801e 0xfdfff76007fffc00

def z813 : W := mkw 0x4083ddb6dcd5001c 0x02041eedb6e6a800 0xe001ffffffff801f 0x07000ffffffffc00

def z814 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf97fc00fe19ffff 0x7dfcbfe007f0cfff

def z815 : W := mkw 0x2850224963baff92 0xd14281124b1dd7fc 0xb9fe0000e7ffff9c 0xfdcff000073ffffc

def z816 : W := mkw 0x5fffddb6d4910014 0x02fffeedb6a48800 0xffffffffe71f8017 0xffffffffff38fc00

def z817 : W := mkw 0x5fffddb69c45000c 0x02fffeedb4e22800 0xdfffffff1f1f8017 0xfefffffff8f8fc00

def z818 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f123f1f1ffffd 0xee0cf891f8f8ffff

def z819 : W := mkw 0x1ff9dda400000000 0x00ffceed20000000 0x5ff9ffff00000003 0xfaffcffff8000000

def z820 : W := mkw 0x15002000b4002800 0x00a8010005a00140 0xbf81fc00fe007fff 0x7dfc0fe007f003ff

def z821 : W := mkw 0x5f7e45b600000000 0x02fbf22db0000000 0x5fffe3ff00000003 0xfaffff1ff8000000

def z822 : W := mkw 0x0850412000000000 0x0042820900000000 0x5879f3ff00000003 0xfac3cf9ff8000000

def z823 : W := mkw 0x4a7ecdb600000000 0x0253f66db0000000 0x407eefff00000002 0x8203f77ff8000000

def z824 : W := mkw 0x57afddb600000000 0x02bd7eedb0000000 0x479fffff00000003 0xea3cfffff8000000

def z825 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff0000700f 0xfafffffff8000380

def z826 : W := mkw 0x022806cd096e52a8 0xa0114036684b7295 0xc7ff1fff1fffffff 0xfe3ff8fff8ffffff

def z827 : W := mkw 0x5fffddb640910014 0x02fffeedb2048800 0x5fffffff00198003 0xfafffffff800cc00

def z828 : W := mkw 0x5fffddb60845000c 0x02fffeedb0422800 0x5fffffff00078003 0xfafffffff8003c00

def z829 : W := mkw 0x2850636961ba7a90 0xc142831b4b0dd3d4 0xf871e3f8e1fe7f9f 0xbfc38f1fc70ff3fc

def z830 : W := mkw 0x42abddb608440008 0x02155eedb0422000 0xc669ffff19e6000f 0xde334ffff8cf3000

def z831 : W := mkw 0x2a7865ad68de2ab8 0x6153c32d6b46f155 0xbe19fc3ff81e0ff0 0x65f0cfe1ffc0f07f

def z832 : W := mkw 0x5583ddb696000543 0x02ac1eedb4b0002a 0xc781ffff1e0001e3 0x463c0ffff8f0000f

def z833 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6681fc718e671eb 0x563340fe38c7338f

def z834 : W := mkw 0x57af9c979e47858e 0x12bd7ce4bcf23c2c 0x878e1c071e078180 0x443c70e038f03c0c

def z835 : W := mkw 0x5fffddb696000543 0x02fffeedb4b0002a 0xdfffffff1e0071ef 0xfefffffff8f0038f

def z836 : W := mkw 0x5fffddb69c45000c 0x02fffeedb4e22800 0xfffffffffe07801f 0xfffffffffff03c00

def z837 : W := mkw 0x5dd7f932f6912d57 0x02eebfc997b4896a 0x3997e038e6198e10 0x21ccbf01c730cc70

def z838 : W := mkw 0x1583b812b6002d43 0x00ac1dc095b0016a 0xbf97fc38fe007fff 0x7dfcbfe1c7f003ff

def z839 : W := mkw 0x022804c5086610a8 0xa011402628433085 0x06601dc718e031ea 0x103300ee38c7018f

def z840 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x39fe0000e7ff801c 0xb9cff000073ffc00

def z841 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x46681fc719e671eb 0x923340fe38cf338f

def z842 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x787fe3f8e1fffe1f 0xbbc3ff1fc70ffff0

def z843 : W := mkw 0x2854636861b97a14 0xc142a31b430dcbd0 0x7877e3f8e1f9fe1f 0xbbc3bf1fc70fcff0

def z844 : W := mkw 0x1f7c8800dcd5005d 0x00fbe44006e6a802 0xbffe0c00ffff807c 0xfdfff06007fffc03

def z845 : W := mkw 0x5f7c8c84dcd5001c 0x02fbe46426e6a800 0xbffe0c00ffff801c 0xfdfff06007fffc00

def z846 : W := mkw 0x5f7ccda400000000 0x02fbe66d20000000 0x5e79ffff00000003 0xfaf3cffff8000000

def z847 : W := mkw 0x00839a1b030ac7c3 0x10041cd0d818563e 0xc19f1e3f071fcff5 0xee0cf8f1f838fe7f

def z848 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3f81fc00fe007ffb 0x31fc0fe007f003ff

def z849 : W := mkw 0x2850612860982a10 0x414283094304c150 0x7871e3f8e1f80e1f 0xbbc38f1fc70fc070

def z850 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f84e15 0xabc38f1fc70fc270

def z851 : W := mkw 0x28d3717362b2bd92 0xd1469b8b9b1595ec 0xb9eef1c7e6e7b18a 0x55cf778e3f373d8c

def z852 : W := mkw 0x4a7e45b648d5001c 0x0253f22db246a800 0x787fe3ffe1ff801f 0xbbc3ff1fff0ffc00

def z853 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x401fffff00000003 0x8200fffff8000000

def z854 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc1ff123f07ffcf9d 0xfe0ff891f83ffe7c

def z855 : W := mkw 0x0a7c0000dcd5001c 0x0053e00006e6a800 0xa1fe0000ffff801c 0xed0ff00007fffc00

def z856 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x79f7e3f8e7f9fe1f 0xbbcfbf1fc73fcff0

def z857 : W := mkw 0x4002cdb600000000 0x0200166db0000000 0x4000efff00000002 0x0200077ff8000000

def z858 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xfe71e3f8f9f87e1f 0xfff38f1fc7cfc3f0

def z859 : W := mkw 0x1f7c45a400000000 0x00fbe22d20000000 0x5fffffff00000003 0xfafffffff8000000

def z860 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0x7e61fffff8e0000b 0x13f30fffffc70000

def z861 : W := mkw 0x085045a400000000 0x0042822d20000000 0x5871ffff00000003 0xbac38ffff8000000

def z862 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x79ffe3f8e1f87e1f 0xfbcfff1fc70fc3f0

def z863 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x819f103f071fcf94 0x640cf881f838fe7c

def z864 : W := mkw 0x1583b812b6002d43 0x00ac1dc095b0016a 0xff9ffe3fff1fffff 0xfffcfff1fff8ffff

def z865 : W := mkw 0x2000224961ba7a90 0xc10001124b0dd3d4 0xa0000000e1fe7f9c 0x05000000070ff3fc

def z866 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xfffffffffffff1ff 0xffffffffffffff8f

def z867 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x59ffffff00000003 0xa2cffffff8000000

def z868 : W := mkw 0x02280000dcd5001c 0x0011400006e6a800 0xa7fe0000ffff801c 0xfd3ff00007fffc00

def z869 : W := mkw 0x0852413200000000 0x0042920990000000 0x587fe3ff00000003 0xbac3ff1ff8000000

def z870 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871fff8e1f87fff 0xbbc38fffc70fc3ff

def z871 : W := mkw 0x4affddb600000000 0x0257feedb0000000 0x587fffff00000003 0xbac3fffff8000000

def z872 : W := mkw 0x0083125b032ad782 0x90041892d81956bc 0xc19f13ff071fff97 0xee0cf89ff838fffc

def z873 : W := mkw 0x0850612060902810 0x0042830903048140 0x7871e3f8e1f87e1f 0xbbc38f1fc70fc3f0

def z874 : W := mkw 0x00000000dcd5001c 0x0000000006e6a800 0xa1960000ffff801c 0x250cb00007fffc00

def z875 : W := mkw 0x022806cd096e52a8 0xa0114036684b7295 0xc6681fc719fe7fff 0xde3340fe38cff3ff

def z876 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xdfffffff1fff8003 0xfefffffff8fffc00

def z877 : W := mkw 0x20002249296e7aa8 0xe1000112494b73d5 0x8000000019e67fec 0x0400000000cf33ff

def z878 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4197ffff00000003 0x220cbffff8000000

def z879 : W := mkw 0x5fffddb694000000 0x02fffeedb4a00000 0x7fffffffe6000013 0xfbffffffff300000

def z880 : W := mkw 0x5f7ecdb6dcd5001c 0x02fbf66db6e6a800 0xfffeefffffff801e 0xfffff77ffffffc00

def z881 : W := mkw 0x20002249f7baffd3 0xd10001124fbdd7fe 0xa0000000fffffffc 0x0500000007ffffff

def z882 : W := mkw 0x2000224963baff92 0xd10001124b1dd7fc 0x20000000e1f87f9c 0x01000000070fc3fc

def z883 : W := mkw 0x0a7845a448d40018 0x0053c22d2246a000 0xfe79fffff9fe001f 0xfff3cfffffcff000

def z884 : W := mkw 0x42abddb600000000 0x02155eedb0000000 0x4661ffff00000003 0x12330ffff8000000

def z885 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f80e13 0xbbc38f1fc70fc070

def z886 : W := mkw 0x00839a1b030ac782 0x10041cd0d818563c 0xc19ffe3f071fcf97 0xee0cfff1f838fe7c

def z887 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc79f1e3f1f1fcff5 0xee3cf8f1f8f8fe7f

def z888 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xffe1ffc0fe007fff 0xffff0ffe07f003ff

def z889 : W := mkw 0x57af9c969e45054f 0x02bd7ce4b4f2282a 0x878e1c071e0781e0 0x443c70e038f03c0f

def z890 : W := mkw 0x1500a800b6002d43 0x00a8054005b0016a 0x3e00ec00f8007fea 0x11f0076007c003ff

def z891 : W := mkw 0x5fffddb602000502 0x02fffeedb0100028 0x5fffffff00004f83 0xfafffffff800027c

def z892 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0xc601ffff180071ef 0x5e300ffff8c0038f

def z893 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x46681fc718e071eb 0xda3340fe38c7038f

def z894 : W := mkw 0x5fffddb696000543 0x02fffeedb4b0002a 0xdfffffff1e004ff7 0xfefffffff8f0027f

def z895 : W := mkw 0x022c06c5096750ac 0xa0116036284b3a85 0xc66e1fc719e7f1ef 0xde3370fe38cf3f8f

def z896 : W := mkw 0x1500a800b6002d43 0x00a8054005b0016a 0xbe00fc00fe007fff 0x5df007e007f003ff

def z897 : W := mkw 0x0083513200000000 0x00041a8990000000 0x4001f3ff00000003 0x02000f9ff8000000

def z898 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x59ffe3ff00000003 0xbacfff1ff8000000

def z899 : W := mkw 0x5583ddb600000000 0x02ac1eedb0000000 0x5981ffff00000003 0x22cc0ffff8000000

def z900 : W := mkw 0x4affddb600000000 0x0257feedb0000000 0x4061ffff00000003 0x02030ffff8000000

def z901 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f87e1c 0xa3c38f1fc70fc3f0

def z902 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x5801ffff00000003 0x3ac00ffff8000000

def z903 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf89fc00ff067fff 0xfdfc4fe007f833ff

def z904 : W := mkw 0x5fffddb6d4910014 0x02fffeedb6a48800 0x7fffffffe0000003 0xfbffffffff000000

def z905 : W := mkw 0x5f7ecdb6dcd5001c 0x02fbf66db6e6a800 0x7e7eeffff9ff800a 0x93f3f77fffcffc00

def z906 : W := mkw 0x5fffddb69c45000c 0x02fffeedb4e22800 0x5fffffff18000003 0xfafffffff8c00000

def z907 : W := mkw 0x2000224969fe7ab8 0xe10001124b4ff3d5 0x20000000e1fe7e1c 0x01000000070ff3f0

def z908 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff01e0000f 0xfafffffff80f0000

def z909 : W := mkw 0x172c0000dcd5001c 0x00b9600006e6a800 0xbf8e0000ffff801c 0x7dfc700007fffc00

def z910 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f123f071fcf81 0xc60cf891f838fe7c

def z911 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff06000017 0xfefffffff8300000

def z912 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5ffeffff00000002 0xd2fff7fff8000000

def z913 : W := mkw 0x2850636961bafa90 0xd142831b4b0dd7d4 0x7871e3f8e1fffe1f 0xbbc38f1fc70ffff0

def z914 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbfff0000ffffce1d 0xfdfff80007fffe70

def z915 : W := mkw 0x2a7c47ed49ff52bc 0xe153e23f6a4ffa95 0x407e03ff01ff8000 0x8203f01ff80ffc00

def z916 : W := mkw 0x5fffddb640900010 0x02fffeedb2048000 0x7fffffffe0180013 0xfbffffffff00c000

def z917 : W := mkw 0x1583b812b6002d43 0x00ac1dc095b0016a 0xff81fe3ffe007fff 0x7ffc0ff1fff003ff

def z918 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff01060007 0xfefffffff8083000

def z919 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbff60000ffff801c 0x35ffb00007fffc00

def z920 : W := mkw 0x1583b812b6002d43 0x00ac1dc095b0016a 0xbf8ffc07fe007fff 0x7dfc7fe03ff003ff

def z921 : W := mkw 0x4a7e45b600000000 0x0253f22db0000000 0x587ee3ff00000002 0x92c3f71ff8000000

def z922 : W := mkw 0x1d500000d4900010 0x00ea800006a48000 0xbffe0000ffff801c 0xfdfff00007fffc00

def z923 : W := mkw 0x5f7c45a4dcd5001c 0x02fbe22d26e6a800 0xbffe01c0ffff801c 0xfdfff00e07fffc00

def z924 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7e71fff8e1f87e1f 0xfbf38fffc70fc3f0

def z925 : W := mkw 0x2a78224969fe7ab8 0xe153c1124b4ff3d5 0xbe780000f9fe7ffc 0xfdf3c00007cff3ff

def z926 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xf871e3f8e7fffe1f 0xbfc38f1fc73ffff0

def z927 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7861e3f8e1e07e0f 0x9bc30f1fc70f03f0

def z928 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xf879e3f8e1fe7e1f 0xffc3cf1fc70ff3f0

def z929 : W := mkw 0x15040000dcd5001c 0x00a8200006e6a800 0xa1860000ffff801c 0x050c300007fffc00

def z930 : W := mkw 0x5dd3ddb600000000 0x02ee9eedb0000000 0x5ff1ffff00000003 0xfaff8ffff8000000

def z931 : W := mkw 0x5fffddb6d4910014 0x02fffeedb6a48800 0x7fffffffe7f9801f 0xfbffffffff3fcc00

def z932 : W := mkw 0x0083125b032ad782 0x90041892d81956bc 0xc7ff1fff1fffffff 0xfe3ff8fff8ffffff

def z933 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7861e3f8e1f87e1f 0x13c30f1fc70fc3f0

def z934 : W := mkw 0x0228048408440008 0x0011402420422000 0xc6681fc719e671ef 0xde3340fe38cf338f

def z935 : W := mkw 0x7f7cede4fcf5381c 0xc3fbe76f27e7a9c0 0x3e60edc0f8e0300a 0x11f3076e07c70180

def z936 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf8ffc00fe07ffff 0x7dfc7fe007f03fff

def z937 : W := mkw 0x485245b600000000 0x0242922db0000000 0x5871e3ff00000003 0xbac38f1ff8000000

def z938 : W := mkw 0x4affddb600000000 0x0257feedb0000000 0x41ffffff00000003 0xea0ffffff8000000

def z939 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4011ffff00000003 0xaa008ffff8000000

def z940 : W := mkw 0x3f7c2249ffffff9e 0xd1fbe1124ffffffc 0xbffe0000ffffff9c 0xfdfff00007fffffc

def z941 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffefff00000002 0xb2ffff7ff8000000

def z942 : W := mkw 0x1f7c0484dcd5001c 0x00fbe02426e6a800 0xbffe0dc0ffff801e 0xfdfff06e07fffc00

def z943 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xf99f123fe71fcf9d 0xffccf891ff38fe7c

def z944 : W := mkw 0x5f7ecdb600000000 0x02fbf66db0000000 0x5e60efff00000002 0x12f3077ff8000000

def z945 : W := mkw 0x2850616860b83a10 0xc142830b4305c1d0 0x3871e1f8e1f83e1e 0xb9c38f0fc70fc1f0

def z946 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4009ffff00000003 0xca004ffff8000000

def z947 : W := mkw 0x57abddb600000000 0x02bd5eedb0000000 0x5fe9ffff00000003 0xfaff4ffff8000000

def z948 : W := mkw 0x0083101b020a8782 0x10041880d810543c 0x819f103f071f8f94 0xec0cf881f838fc7c

def z949 : W := mkw 0x2850636961ba7a90 0xc142831b4b0dd3d4 0x7871f3ffe1f87f9f 0xbbc38f9fff0fc3fc

def z950 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81fc00fe007feb 0x55fc0fe007f003ff

def z951 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81fc00ff1fffff 0x7dfc0fe007f8ffff

def z952 : W := mkw 0x1500a800b6002d43 0x00a8054005b0016a 0xbf80ec00fe007ffe 0x7dfc076007f003ff

def z953 : W := mkw 0x2850616860b83a10 0xc142830b4305c1d0 0x3871e1f8e0f87e1f 0x39c38f0fc707c3f0

def z954 : W := mkw 0x5fffddb640900010 0x02fffeedb2048000 0xffffffffe7ff801f 0xffffffffff3ffc00

def z955 : W := mkw 0x5fffddb69e45054f 0x02fffeedb4f2282a 0xdfffffff1e0781e3 0xfefffffff8f03c0f

def z956 : W := mkw 0x5f7ccda4dcd5001c 0x02fbe66d26e6a800 0xfffeffc7ffff801f 0xfffff7fe3ffffc00

def z957 : W := mkw 0x022804c5086610a8 0xa011402628433085 0x86681dc718e671ef 0x5c3340ee38c7338f

def z958 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x86681dc719e671ee 0x543340ee38cf338f

def z959 : W := mkw 0x0083101b020a8782 0x10041880d810543c 0xc19f123f061f8f91 0xee0cf891f830fc7c

def z960 : W := mkw 0x3dd3f93af698af53 0x51ee9fc9d7b4c57a 0x3997e038e6198e10 0x21ccbf01c730cc70

def z961 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4001ffff000071e3 0x02000ffff800038f

def z962 : W := mkw 0x20002249212a7aa0 0xe1000112490953d5 0x0000000000007fe0 0x00000000000003ff

def z963 : W := mkw 0x0083513200000000 0x00041a8990000000 0x419ff3ff00000003 0xea0cff9ff8000000

def z964 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0xc19fffff071f8017 0xee0cfffff838fc00

def z965 : W := mkw 0x0002021b010ac280 0x10001010d8085614 0xc19f023f071fce15 0xee0cf811f838fe70

def z966 : W := mkw 0x5fffddb608440008 0x02fffeedb0422000 0xdfffffff19e671ef 0xfefffffff8cf338f

def z967 : W := mkw 0x5fffddb648d5001c 0x02fffeedb246a800 0x7fffffffe1ff801f 0xfbffffffff0ffc00

def z968 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5ff7ffff00000003 0x32ffbffff8000000

def z969 : W := mkw 0x1500a800b6002d43 0x00a8054005b0016a 0xbe01ec00fe007fff 0x3df00f6007f003ff

def z970 : W := mkw 0x1d540000dcd5001c 0x00eaa00006e6a800 0xb99e0000ffff801c 0xedccf00007fffc00

def z971 : W := mkw 0x4affddb600000000 0x0257feedb0000000 0x407fe3ff00000000 0x8203ff1ff8000000

def z972 : W := mkw 0x1dd3d93200000000 0x00ee9ec990000000 0x5fffffff00000003 0xfafffffff8000000

def z973 : W := mkw 0x08d3513240900010 0x00469a8992048000 0xf9fff3ffe7ff801f 0xffcfff9fff3ffc00

def z974 : W := mkw 0x7dd7f93af6982f53 0x43eebfc9d7b4c17a 0x3997e038e6180e10 0x21ccbf01c730c070

def z975 : W := mkw 0x5fffddb6ded5055f 0x02fffeedb6f6a82a 0xffffffffffff81ff 0xfffffffffffffc0f

def z976 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe1000ffffc19d 0xfdfff08007fffe0c

def z977 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4181ffff00000003 0x6a0c0ffff8000000

def z978 : W := mkw 0x1d540000dcd5001c 0x00eaa00006e6a800 0xbf960000ffff801c 0x7dfcb00007fffc00

def z979 : W := mkw 0x0000224821287a00 0x80000112410943d0 0x7871e3f8e1f87e1f 0xbbc38f1fc70fc3f0

def z980 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc7e81fc71fe671ff 0xfe3f40fe38ff338f

def z981 : W := mkw 0x3f7c65e4fcf5383c 0xe1fbe32f27e7a9c1 0x3e60edc0f8e0306a 0x11f3076e07c70183

def z982 : W := mkw 0x5587ddb600000000 0x02ac3eedb0000000 0x4187ffff00000003 0x020c3ffff8000000

def z983 : W := mkw 0x5dd7ddb600000000 0x02eebeedb0000000 0x5801ffff00000003 0x02c00ffff8000000

def z984 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbe01fc00fe007fff 0x15f00fe007f003ff

def z985 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3f81fc00f8007feb 0x79fc0fe007c003ff

def z986 : W := mkw 0x0afb55b600000000 0x0057daadb0000000 0x5fffffff00000003 0xfafffffff8000000

def z987 : W := mkw 0x00002249bf6effeb 0xb00001124dfb77ff 0xa0000000fffffffc 0x0500000007ffffff

def z988 : W := mkw 0x20002249fdff7abc 0xe10001124feffbd5 0xa0000000fffffffc 0x0500000007ffffff

def z989 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f123f061fcf91 0x660cf891f830fe7c

def z990 : W := mkw 0x5dd7ddb6d4910014 0x02eebeedb6a48800 0x7997ffffe6198013 0x23ccbfffff30cc00

def z991 : W := mkw 0x5fffddb602000502 0x02fffeedb0100028 0x5fffffff06000e13 0xfafffffff8300070

def z992 : W := mkw 0x0000000040900010 0x0000000002048000 0xa19e0000e7ff801c 0xed0cf000073ffc00

def z993 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xb9fe0000e7ff8014 0xedcff000073ffc00

def z994 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7e71eff8f9f87e7f 0xbbf38f7fc7cfc3f3

def z995 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x419f123f071fcf91 0xa20cf891f838fe7c

def z996 : W := mkw 0x1f7c4120dcd5001c 0x00fbe20906e6a800 0xbfffe038ffff801c 0xfdffff01c7fffc00

def z997 : W := mkw 0x022845a400000000 0x0011422d20000000 0x4669ffff00000003 0xda334ffff8000000

def z998 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4001e3ff00000000 0x02000f1ff8000000

def z999 : W := mkw 0x1f7c0484dcd5001c 0x00fbe02426e6a800 0xbffe1c07ffff801c 0xfdfff0e03ffffc00

def z1000 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6681fc719e631ea 0xd63340fe38cf318f

def z1001 : W := mkw 0x022804c5086610a8 0xa011402628433085 0xc6681fc718e631eb 0xde3340fe38c7318f

def z1002 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6791fff19e671ef 0xfe33c8fff8cf338f

def z1003 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbfee0000ffff801c 0x55ff700007fffc00

def z1004 : W := mkw 0x48d3ddb600000000 0x02469eedb0000000 0x5811ffff00000003 0x22c08ffff8000000

def z1005 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x418fffff00000003 0x420c7ffff8000000

def z1006 : W := mkw 0x4a7e45b600000000 0x0253f22db0000000 0x407fe3ff00000003 0x8203ff1ff8000000

def z1007 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6601fc718e071ef 0x5e3300fe38c7038f

def z1008 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff06078003 0xfefffffff8303c00

def z1009 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xff91fe38fe007fff 0xfffc8ff1c7f003ff

def z1010 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5f9fffff00000003 0x62fcfffff8000000

def z1011 : W := mkw 0x1f7c000040900010 0x00fbe00002048000 0xbffe0000e7ff801c 0xfdfff000073ffc00

def z1012 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x3ffe0000e7ff8010 0xf9fff000073ffc00

def z1013 : W := mkw 0x5fffddb608440028 0x22fffeedb0422001 0x5fffffff18000063 0xfafffffff8c00003

def z1014 : W := mkw 0x1f7c4120dcd5001c 0x00fbe20906e6a800 0xbffee1c0ffff801e 0xfdfff70e07fffc00

def z1015 : W := mkw 0x57afddb69c45000c 0x02bd7eedb4e22800 0xc78fffff1e078003 0x463c7ffff8f03c00

def z1016 : W := mkw 0x0000024101225080 0x8000001208091284 0xc6681fc719e671ef 0xde3340fe38cf338f

def z1017 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0x46601fc719e071ef 0x9a3300fe38cf038f

def z1018 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6681fc71ffff1ff 0xde3340fe38ffff8f

def z1019 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4061ffff00000003 0x9a030ffff8000000

def z1020 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0x7ffffffffef9801b 0xfbfffffffff7cc00

def z1021 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5e71ffff00000003 0xbaf38ffff8000000

def z1022 : W := mkw 0x1585b800b6012d47 0x00ac2dc005b0096a 0xbf87fc00fe01ffff 0x7dfc3fe007f00fff

def z1023 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6781fc719fe71ff 0xfe33c0fe38cff38f

def z1024 : W := mkw 0x57afddb600000000 0x02bd7eedb0000000 0x47efffff00000003 0xda3f7ffff8000000

def z1025 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0x7ffffffff9ff800b 0xfbffffffffcffc00

def z1026 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5e69ffff00000003 0xdaf34ffff8000000

def z1027 : W := mkw 0x1f7c0484dcd5001c 0x00fbe02426e6a800 0xfffe03c7ffff801c 0xfffff01e3ffffc00

def z1028 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0x3e01fc00f8007fff 0x39f00fe007c003ff

def z1029 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0x7fffffffe7ff8013 0xfbffffffff3ffc00

def z1030 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xfffffffffe1f8013 0xfffffffffff0fc00

def z1031 : W := mkw 0x5fffddb608440008 0x02fffeedb0422000 0xdfffffff1fff801f 0xfefffffff8fffc00

def z1032 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xb9fe0000ffff801c 0xa5cff00007fffc00

def z1033 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0xffffe3ffffff801c 0xffffff1ffffffc00

def z1034 : W := mkw 0x4aff55b600000000 0x0257faadb0000000 0x59fff3ff00000003 0xfacfff9ff8000000

def z1035 : W := mkw 0x5fffddb602000502 0x02fffeedb0100028 0xdfffffff06000183 0xfefffffff830000c

def z1036 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0x3ffe0000ffff8018 0xb1fff00007fffc00

def z1037 : W := mkw 0x42abddb600000000 0x02155eedb0000000 0x47ffffff00000003 0xfa3ffffff8000000

def z1038 : W := mkw 0x00002000b6002d43 0x0000010005b0016a 0xbe01fc00fe007fff 0x7df00fe007f003ff

def z1039 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbfe1fc00ffe07fff 0xfdff0fe007ff03ff

def z1040 : W := mkw 0x4afbddb600000000 0x0257deedb0000000 0x5e79ffff00000003 0xfaf3cffff8000000

def z1041 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6681fc719e671ec 0xc63340fe38cf338f

def z1042 : W := mkw 0x1502aa1bb50aeac1 0x10a81550dda85756 0x7e1eee3ff91fb06a 0x93f0f771ffc8fd83

def z1043 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0x7ffffffff9f8001f 0xfbffffffffcfc000

def z1044 : W := mkw 0x5f7ecdb600000000 0x02fbf66db0000000 0x587ee3ff00000000 0x82c3f71ff8000000

def z1045 : W := mkw 0x2850636961ba7a90 0xc142831b4b0dd3d4 0xf9fff3ffe7ffff9f 0xffcfff9fff3ffffc

def z1046 : W := mkw 0x2850616860b83a10 0xc142830b4305c1d0 0x7871e3f8e0f83e1b 0xbbc38f1fc707c1f0

def z1047 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5e7fffff00000003 0x92f3fffff8000000

def z1048 : W := mkw 0x1f7c0484dcd5001c 0x00fbe02426e6a800 0xfffe1fc7fffff1ff 0xfffff0fe3fffff8f

def z1049 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fe1ffff00000003 0x7aff0ffff8000000

def z1050 : W := mkw 0x00000209010a4280 0x0000001048085214 0xc19f123f071fcf95 0xee0cf891f838fe7c

def z1051 : W := mkw 0x4083ddb600000000 0x02041eedb0000000 0x4601ffff00000003 0x5a300ffff8000000

def z1052 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x419f023f071fce15 0xaa0cf811f838fe70

def z1053 : W := mkw 0x2850616860b83a10 0xc142830b4305c1d0 0x3871e1f8e0f80e10 0x21c38f0fc707c070

def z1054 : W := mkw 0x4083ddb602000543 0x02041eedb010002a 0x4001ffff000001e3 0x02000ffff800000f

def z1055 : W := mkw 0x2a7a47ff49fed2b8 0xf153d23ffa4ff695 0x407e03ff01ff8000 0x8203f01ff80ffc00

def z1056 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f80e1c 0xbbc38f1fc70fc070

def z1057 : W := mkw 0x172c0000dcd5001c 0x00b9600006e6a800 0xa7ee0000ffff801c 0xdd3f700007fffc00

def z1058 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e1f83e1a 0xb3c38f1fc70fc1f0

def z1059 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0xf9f1e3f8e7f87e1f 0xffcf8f1fc73fc3f0

def z1060 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf81fc00fe007ff3 0x65fc0fe007f003ff

def z1061 : W := mkw 0x022806c5096650a8 0xa0114036284b3285 0xc6601fc719e671ef 0x163300fe38cf338f

def z1062 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e0e07e0b 0xbbc38f1fc70703f0

def z1063 : W := mkw 0x17ab9c979e4685eb 0x30bd5ce4bcf2342f 0x878e1c071e0781e0 0x443c70e038f03c0f

def z1064 : W := mkw 0x0a78000048d40018 0x0053c0000246a000 0xbffe0000ffff801c 0xfdfff00007fffc00

def z1065 : W := mkw 0x0083125b032ad782 0x90041892d81956bc 0xc19f123f07ffff9d 0xee0cf891f83ffffc

def z1066 : W := mkw 0x5f7e45b6dcd5001c 0x02fbf22db6e6a800 0xffffe3ffffff801f 0xffffff1ffffffc00

def z1067 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7871e3f8e0f87e1b 0x33c38f1fc707c3f0

def z1068 : W := mkw 0x5fffddb694000000 0x02fffeedb4a00000 0xfffffffffe0071ff 0xfffffffffff0038f

def z1069 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbf9e0000ffff801c 0x65fcf00007fffc00

def z1070 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe1c00ffff81fc 0xfdfff0e007fffc0f

def z1071 : W := mkw 0x0083101b020a8782 0x10041880d810543c 0x819f103f061fcf95 0x6c0cf881f830fe7c

def z1072 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbf80fc00fe007ffe 0x55fc07e007f003ff

def z1073 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe1c00ffff801f 0xfdfff0e007fffc00

def z1074 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x3871e1f8e1f87e1e 0x31c38f0fc70fc3f0

def z1075 : W := mkw 0x48d7ddb600000000 0x0246beedb0000000 0x4017ffff00000003 0x0200bffff8000000

def z1076 : W := mkw 0x5f7ecdb600000000 0x02fbf66db0000000 0x5e7effff00000003 0xdaf3f7fff8000000

def z1077 : W := mkw 0x48d3ddb600000000 0x02469eedb0000000 0x5861ffff00000003 0x12c30ffff8000000

def z1078 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f123f071fff9f 0xfe0cf891f838fffc

def z1079 : W := mkw 0x4a7e45b600000000 0x0253f22db0000000 0x587fe3ff00000000 0xa2c3ff1ff8000000

def z1080 : W := mkw 0x208377ff232affa2 0xf1041bbff91957fd 0x4001ffff00007fe3 0x02000ffff80003ff

def z1081 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe0000fffff1fc 0xfdfff00007ffff8f

def z1082 : W := mkw 0x5583ddb600000000 0x02ac1eedb0000000 0x5e01ffff00000003 0x12f00ffff8000000

def z1083 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fefffff00000003 0x52ff7ffff8000000

def z1084 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe0000fffff01f 0xfdfff00007ffff80

def z1085 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xd99ff23f071fcf97 0xfeccff91f838fe7c

def z1086 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xff89fe07fe007fff 0xfffc4ff03ff003ff

def z1087 : W := mkw 0x5f7ecdb600000000 0x02fbf66db0000000 0x5ffeefff00000002 0xfafff77ff8000000

def z1088 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19f023f071fcf94 0xa60cf811f838fe7c

def z1089 : W := mkw 0x5fffddb6dcd5001c 0x02fffeedb6e6a800 0x79ffe3ffe7ff8010 0xa3cfff1fff3ffc00

def z1090 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xffff0238ffff801d 0xfffff811c7fffc00

def z1091 : W := mkw 0x5fffddb696000543 0x02fffeedb4b0002a 0x5fffffff06000003 0xfafffffff8300000

def z1092 : W := mkw 0x5fffddb694000000 0x02fffeedb4a00000 0xdfffffff1e000003 0xfefffffff8f00000

def z1093 : W := mkw 0x0083125b032ad782 0x90041892d81956bc 0xc1ff13ff07ffcf95 0xee0ff89ff83ffe7c

def z1094 : W := mkw 0x42afddb600000000 0x02157eedb0000000 0x400fffff00000003 0x02007ffff8000000

def z1095 : W := mkw 0x4083ddb602000502 0x02041eedb0100028 0xc181ffff06004f97 0x6e0c0ffff830027c

def z1096 : W := mkw 0x000006c5012250a0 0xa000003628091285 0xc6601fc719e071ef 0xde3300fe38cf038f

def z1097 : W := mkw 0x2083325b232aff82 0xd1041992d91957fc 0x4001123f00007f81 0x02000891f80003fc

def z1098 : W := mkw 0x08500000dcd5001c 0x0042800006e6a800 0xb9fe0000ffff801c 0xfdcff00007fffc00

def z1099 : W := mkw 0x00000000dcd5001c 0x0000000006e6a800 0xa18e0000ffff801c 0x450c700007fffc00

def z1100 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xfffe03c0ffff801f 0xfffff01e07fffc00

def z1101 : W := mkw 0x4affddb648d5001c 0x0257feedb246a800 0x407fffff01ff8003 0x8203fffff80ffc00

def z1102 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc1ff13ff071fcf97 0xfe0ff89ff838fe7c

def z1103 : W := mkw 0x022804c408641028 0xa011402620432081 0xc6681fc718e071ef 0xde3340fe38c7038f

def z1104 : W := mkw 0x5f7ecdb600000000 0x02fbf66db0000000 0x5e7fefff00000003 0xbaf3ff7ff8000000

def z1105 : W := mkw 0x5fffddb6d4900010 0x02fffeedb6a48000 0xfffffffffff8001f 0xffffffffffffc000

def z1106 : W := mkw 0x5fffddb608440008 0x02fffeedb0422000 0x5fffffff18e0000b 0xfafffffff8c70000

def z1107 : W := mkw 0x5fffddb640900010 0x02fffeedb2048000 0x7fffffffe0e0000b 0xfbffffffff070000

def z1108 : W := mkw 0x6a7e47ff49fe52b8 0xe353f23ffa4ff295 0x407e03ff01fe0000 0x8203f01ff80ff000

def z1109 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc19e123f071fcf94 0xc60cf091f838fe7c

def z1110 : W := mkw 0x17ab9c9600000000 0x00bd5ce4b0000000 0x5fffffff00000003 0xfafffffff8000000

def z1111 : W := mkw 0x48d3ddb600000000 0x02469eedb0000000 0x4071ffff00000003 0x82038ffff8000000

def z1112 : W := mkw 0x4083ddb602000502 0x02041eedb0100028 0x4001ffff00004f83 0x02000ffff800027c

def z1113 : W := mkw 0x2000224961ba7ab0 0xe10001124b0dd3d5 0x20000000e1f87ffc 0x01000000070fc3ff

def z1114 : W := mkw 0x172800009c440008 0x00b9400004e22000 0xbffe0000ffff801c 0xfdfff00007fffc00

def z1115 : W := mkw 0x5583ddb600000000 0x02ac1eedb0000000 0x5f9fffff00000003 0xfafcfffff8000000

def z1116 : W := mkw 0x15000000dcd5001c 0x00a8000006e6a800 0xbf9e0000ffff801c 0xfdfcf00007fffc00

def z1117 : W := mkw 0x2000224961bafa90 0xd10001124b0dd7d4 0x20000000e1fffe1c 0x01000000070ffff0

def z1118 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x47ffffff00000003 0xc23ffffff8000000

def z1119 : W := mkw 0x1583b812b600ad43 0x10ac1dc095b0056a 0xbf87fc00fe01ffff 0x7dfc3fe007f00fff

def z1120 : W := mkw 0x022806cd096e52a8 0xa0114036684b7295 0xc6781fff19fe71ef 0xde33c0fff8cff38f

def z1121 : W := mkw 0x4affddb600000000 0x0257feedb0000000 0x467fffff00000003 0xda33fffff8000000

def z1122 : W := mkw 0x5fffddb608440008 0x02fffeedb0422000 0xdfffffff18060003 0xfefffffff8c03000

def z1123 : W := mkw 0x1581b800b6002d43 0x00ac0dc005b0016a 0xbe01fc00f8007fef 0x5df00fe007c003ff

def z1124 : W := mkw 0x022804c5086610a8 0xa011402628433085 0x86681dc719e631ee 0xdc3340ee38cf318f

def z1125 : W := mkw 0x20002249fffe7ffb 0xe10001124ffff3ff 0xa0000000fffe7ffc 0x0500000007fff3ff

def z1126 : W := mkw 0x3f7c2249fdff7abc 0xe1fbe1124feffbd5 0xbffe0000fffffffc 0xfdfff00007ffffff

def z1127 : W := mkw 0x42abddb600000000 0x02155eedb0000000 0x4069ffff00000003 0x82034ffff8000000

def z1128 : W := mkw 0x6083ffff232aff82 0xd3041ffff91957fc 0x4001ffff00007f83 0x02000ffff80003fc

def z1129 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff06198013 0xfafffffff830cc00

def z1130 : W := mkw 0x5dd7ddb600000000 0x02eebeedb0000000 0x599fffff00000003 0xeaccfffff8000000

def z1131 : W := mkw 0x172c0000dcd5001c 0x00b9600006e6a800 0xa79e0000ffff801c 0xed3cf00007fffc00

def z1132 : W := mkw 0x5fffddb69c45000c 0x02fffeedb4e22800 0xdfffffff1fe7800f 0xfefffffff8ff3c00

def z1133 : W := mkw 0x200022496bfeffba 0xf10001124b5ff7fd 0xa0000000fffffffc 0x0500000007ffffff

def z1134 : W := mkw 0x5fffddb6ded5051e 0x02fffeedb6f6a828 0xffffffffffffcf9f 0xfffffffffffffe7c

def z1135 : W := mkw 0x5fffddb694000000 0x02fffeedb4a00000 0xffffffffff1f801f 0xfffffffffff8fc00

def z1136 : W := mkw 0x2083fb7b232affc3 0xd1041fdbd91957fe 0x4001ffff00007fe3 0x02000ffff80003ff

def z1137 : W := mkw 0x5dd7d93200000000 0x02eebec990000000 0x59fff3ff00000003 0xfacfff9ff8000000

def z1138 : W := mkw 0x5fffddb648d5001c 0x02fffeedb246a800 0xdfffffff07ff8017 0xfefffffff83ffc00

def z1139 : W := mkw 0x5583ddb600000000 0x02ac1eedb0000000 0x4781ffff00000003 0x423c0ffff8000000

def z1140 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0xc79f1e3f071fcf97 0xfe3cf8f1f838fe7c

def z1141 : W := mkw 0x20002249232aff82 0xd1000112491957fc 0x80000000071fff94 0x040000000038fffc

def z1142 : W := mkw 0x0083121b030ac782 0x10041890d818563c 0x419f123f071f8e11 0xea0cf891f838fc70

def z1143 : W := mkw 0x022806cd096ed2a8 0xb0114036684b7695 0xc6681fc719fff1ef 0xde3340fe38cfff8f

def z1144 : W := mkw 0x022806c401205000 0x8011403620090280 0xc6681fc719e071ef 0xde3340fe38cf038f

def z1145 : W := mkw 0x400245b600000000 0x0200122db0000000 0x4001e3ff00000003 0x02000f1ff8000000

def z1146 : W := mkw 0x5fffddb602008502 0x12fffeedb0100428 0x5fffffff06018003 0xfafffffff8300c00

def z1147 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x59fff3ff00000001 0xeacfff9ff8000000

def z1148 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x5fffffff01180017 0xfafffffff808c000

def z1149 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xfffe1207ffff801d 0xfffff0903ffffc00

def z1150 : W := mkw 0x5fffddb6d4910014 0x02fffeedb6a48800 0xfffffffffe19801f 0xfffffffffff0cc00

def z1151 : W := mkw 0x2850636861b87a10 0xc142831b430dc3d0 0x7879f3ffe1f87e1f 0xfbc3cf9fff0fc3f0

def z1152 : W := mkw 0x5f7cc920dcd5001c 0x02fbe64906e6a800 0xbffee000ffff801c 0xfdfff70007fffc00

def z1153 : W := mkw 0x5fffddb648d5001c 0x02fffeedb246a800 0xdfffffff19ff800f 0xfefffffff8cffc00

def z1154 : W := mkw 0x5583ddb694000000 0x02ac1eedb4a00000 0xff81fffffe00001f 0x7ffc0ffffff00000

def z1155 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0x7fffffffe000001f 0xfbffffffff000000

def z1156 : W := mkw 0x1f7c0000dcd5001c 0x00fbe00006e6a800 0xbffe0000ffff8008 0xd5fff00007fffc00

def z1157 : W := mkw 0x5fffddb600000000 0x02fffeedb0000000 0xdfffffff180001e3 0xfefffffff8c0000f

def z1158 : W := mkw 0x5fffddb602000543 0x02fffeedb010002a 0x5fffffff000001e3 0xfafffffff800000f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z7,z8]),(0,[z1,z9,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z11,z5,z6])],[(0,[z1,z2,z3,z12,z4,z5,z13]),(0,[z1,z2,z3,z4,z5,z13,z6]),(0,[z1,z2,z14,z3,z4,z5,z15]),(0,[z1,z2,z16,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z19])],[(0,[z1,z2,z20,z3,z4,z5,z6]),(0,[z21,z1,z2,z3,z4,z5,z22]),(0,[z23,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z24,z5,z22]),(1,[z1,z2,z3,z12,z5,z15]),(0,[z25,z1,z3,z4,z5,z26,z6]),(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z1,z2,z3,z4,z5,z22,z8]),(0,[z1,z2,z3,z28,z4,z5,z22])],[(1,[z1,z2,z29,z4,z5,z6]),(0,[z1,z30,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z31]),(0,[z1,z2,z3,z4,z5,z32,z33]),(0,[z34,z1,z2,z3,z4,z35,z6]),(0,[z36,z1,z2,z3,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z38,z4,z5,z6])],[(0,[z1,z39,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z40,z41,z6]),(0,[z42,z1,z2,z3,z12,z5,z6]),(0,[z1,z2,z43,z3,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z45]),(0,[z46,z1,z2,z3,z4,z5,z6])],[(0,[z47,z1,z48,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z49,z26,z6]),(1,[z1,z2,z3,z4,z50,z5]),(0,[z51,z1,z2,z3,z4,z5,z22]),(1,[z1,z2,z3,z4,z5,z52])],[(0,[z1,z2,z53,z3,z4,z5,z6]),(0,[z54,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z56,z4,z5,z6]),(0,[z1,z57,z2,z3,z4,z26,z6]),(0,[z1,z57,z2,z3,z4,z58,z6]),(0,[z1,z2,z3,z4,z59,z5,z6]),(0,[z1,z2,z3,z4,z5,z60,z6]),(0,[z1,z2,z3,z4,z61,z5,z6])]],
   [[(0,[z1,z2,z3,z62,z4,z5,z63]),(0,[z64,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z66]),(0,[z1,z2,z3,z4,z67,z5,z6]),(0,[z1,z2,z16,z3,z4,z68,z6]),(0,[z1,z2,z3,z28,z5,z6,z15])],[(0,[z69,z1,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z32,z6]),(0,[z72,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z73,z3,z4,z5,z6])],[(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z22]),(0,[z75,z1,z2,z3,z4,z5,z6]),(1,[z1,z57,z3,z4,z58,z6]),(0,[z1,z2,z3,z4,z5,z76,z6]),(0,[z1,z2,z44,z3,z4,z5,z52]),(0,[z1,z2,z3,z4,z5,z77,z6])],[(0,[z54,z1,z2,z3,z4,z5,z15]),(0,[z78,z1,z2,z3,z4,z5,z15]),(0,[z79,z1,z2,z80,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z19,z15]),(0,[z1,z2,z3,z4,z5,z22,z81])],[(0,[z1,z2,z3,z4,z5,z82,z6]),(0,[z83,z1,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z14,z4,z5,z6]),(0,[z1,z2,z3,z4,z84,z5,z6]),(0,[z1,z2,z85,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z86,z6]),(1,[z1,z2,z3,z4,z5,z87]),(0,[z1,z2,z16,z3,z4,z5,z87]),(0,[z1,z2,z3,z4,z5,z22,z88])],[(0,[z1,z2,z3,z89,z4,z5,z15]),(0,[z1,z2,z90,z3,z4,z5,z6]),(0,[z91,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z93]),(0,[z1,z2,z94,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z95])],[(0,[z39,z2,z96,z3,z4,z5,z6]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z98,z3,z4,z5,z6]),(0,[z1,z2,z99,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z100,z15])],[(0,[z1,z2,z3,z4,z101,z5,z19])]],
   [[(0,[z1,z2,z102,z3,z4,z5,z6]),(0,[z1,z2,z103,z3,z4,z5,z6]),(0,[z1,z2,z3,z104,z4,z5,z6]),(0,[z1,z105,z2,z3,z4,z5,z6])],[(0,[z1,z2,z106,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z107,z5,z6]),(0,[z1,z2,z18,z3,z4,z6,z95])],[(0,[z21,z1,z96,z3,z4,z5,z6]),(0,[z21,z1,z2,z3,z4,z5,z15]),(0,[z79,z1,z2,z108,z4,z5,z6]),(0,[z1,z2,z3,z4,z24,z5,z15]),(0,[z109,z1,z2,z3,z4,z5,z6]),(0,[z110,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z44,z4,z35,z5,z6])],[(0,[z1,z2,z108,z4,z5,z6,z8]),(0,[z1,z2,z3,z4,z5,z111,z6]),(0,[z1,z2,z3,z112,z4,z5,z22])],[(0,[z1,z96,z3,z4,z113,z5,z6]),(0,[z1,z2,z3,z4,z114,z5,z6]),(0,[z47,z1,z2,z3,z4,z115,z6]),(0,[z116,z2,z3,z4,z5,z7,z6]),(0,[z1,z117,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z118,z5,z6])],[(0,[z1,z2,z3,z4,z119,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z54,z1,z2,z3,z4,z40,z6]),(0,[z1,z2,z3,z4,z121,z5,z6]),(0,[z1,z122,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z123,z4,z5,z6]),(0,[z124,z1,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z5,z88,z6])],[(0,[z51,z1,z2,z3,z4,z5,z15]),(0,[z25,z1,z2,z3,z4,z5,z22]),(0,[z126,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z68,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z127])],[(0,[z1,z2,z3,z4,z5,z128,z6]),(0,[z1,z2,z3,z4,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z130,z6])]],
   [[(0,[z54,z1,z131,z3,z4,z5,z6]),(1,[z132,z1,z2,z3,z5,z6]),(0,[z1,z133,z2,z3,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z135]),(0,[z1,z2,z3,z4,z5,z15,z45]),(0,[z125,z1,z2,z3,z5,z22,z6])],[(1,[z54,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z113,z84,z5,z6]),(0,[z1,z2,z136,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z137,z6]),(0,[z1,z2,z3,z112,z5,z6,z15])],[(1,[z1,z138,z3,z4,z5,z6]),(0,[z139,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z140,z3,z4,z5,z6])],[(0,[z1,z2,z141,z3,z4,z5,z6])],[(0,[z1,z2,z3,z142,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z115,z6]),(0,[z1,z2,z3,z62,z4,z5,z128]),(0,[z1,z2,z3,z4,z5,z143,z6]),(0,[z1,z2,z144,z3,z4,z5,z6])],[(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z146,z3,z4,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z149,z6]),(0,[z150,z1,z2,z3,z4,z5,z6])],[(0,[z42,z1,z96,z3,z4,z5,z6]),(0,[z23,z151,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z152,z5,z6]),(0,[z153,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z32,z93]),(0,[z1,z2,z3,z4,z154,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6])],[(0,[z132,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z156,z6]),(0,[z1,z2,z3,z4,z5,z157,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z158,z6]),(1,[z1,z9,z3,z113,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z93]),(0,[z1,z2,z3,z159,z4,z5,z6]),(0,[z1,z2,z3,z160,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z161]),(0,[z1,z2,z3,z4,z5,z162,z6]),(0,[z1,z2,z3,z4,z163,z5,z6]),(0,[z164,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z165,z3,z4,z5,z6])],[(0,[z1,z3,z4,z58,z5,z26,z6]),(1,[z1,z2,z3,z28,z5,z15])],[(0,[z166,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z68,z49,z6]),(0,[z1,z2,z167,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z35,z58,z6])],[(0,[z1,z2,z3,z168,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z169,z6]),(0,[z1,z2,z3,z4,z58,z5,z6])],[(0,[z1,z2,z170,z3,z4,z5,z6]),(0,[z1,z2,z171,z3,z4,z5,z6]),(0,[z1,z2,z172,z3,z4,z5,z6]),(0,[z1,z105,z2,z3,z4,z5,z93]),(0,[z125,z1,z2,z3,z4,z5,z15])],[(0,[z1,z2,z173,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z174,z6]),(0,[z25,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z175,z6]),(0,[z1,z2,z3,z112,z4,z41,z6])],[(0,[z1,z2,z176,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z177,z6]),(0,[z1,z9,z2,z3,z4,z5,z178]),(1,[z1,z2,z3,z4,z5,z179])]],
   [[(0,[z1,z2,z180,z3,z4,z5,z6]),(0,[z1,z2,z181,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z182]),(0,[z1,z2,z3,z4,z5,z177,z6]),(0,[z183,z1,z2,z3,z4,z5,z184])],[(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z186,z3,z4,z5,z6]),(0,[z187,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z188,z5,z6]),(0,[z1,z2,z134,z3,z113,z5,z6]),(0,[z34,z1,z2,z3,z4,z5,z6]),(0,[z189,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z190,z6]),(0,[z191,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z192])],[(0,[z1,z2,z193,z3,z4,z5,z6]),(0,[z1,z2,z3,z194,z4,z5,z6]),(0,[z195,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z196,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z197]),(0,[z198,z1,z2,z3,z4,z5,z6]),(0,[z199,z1,z2,z3,z4,z5,z22])],[(0,[z200,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z201,z3,z4,z5,z6]),(0,[z1,z2,z202,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z28,z5,z6])],[(0,[z1,z2,z3,z4,z5,z203,z6]),(1,[z1,z2,z3,z204,z5,z6])],[(0,[z51,z205,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z206,z5,z6]),(0,[z1,z2,z3,z4,z207,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z208,z5,z6]),(0,[z1,z205,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z209,z6])],[(0,[z210,z1,z2,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z68,z5,z6]),(0,[z1,z2,z3,z4,z58,z49,z6]),(0,[z51,z1,z2,z3,z4,z5,z211]),(0,[z212,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z213,z3,z4,z5,z6])],[(0,[z214,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z215,z5,z6]),(0,[z1,z2,z3,z4,z40,z5,z6]),(0,[z1,z2,z3,z4,z216,z5,z6]),(0,[z217,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z41,z22])],[(0,[z71,z2,z3,z4,z5,z6,z33]),(0,[z1,z2,z3,z4,z218,z5,z6]),(0,[z1,z2,z3,z4,z219,z5,z6])],[],[(0,[z1,z2,z3,z220,z4,z5,z6]),(0,[z1,z221,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z5,z222]),(0,[z79,z1,z2,z4,z5,z32,z6])],[(0,[z1,z2,z3,z4,z5,z6,z223]),(0,[z47,z1,z138,z3,z4,z5,z6]),(0,[z1,z2,z224,z3,z4,z5,z6]),(0,[z1,z2,z225,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z226,z6])],[(0,[z21,z2,z3,z89,z4,z5,z6]),(0,[z78,z1,z2,z134,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z227]),(0,[z1,z2,z3,z4,z5,z228,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z229,z6]),(0,[z230,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z12,z4,z5,z231]),(0,[z1,z2,z3,z4,z5,z6,z232])],[(0,[z1,z2,z3,z233,z4,z5,z6]),(0,[z47,z1,z2,z224,z4,z5,z6]),(0,[z234,z1,z2,z3,z4,z5,z6]),(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z236,z4,z5,z6]),(0,[z1,z237,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z238,z5,z6])],[(0,[z1,z2,z3,z4,z5,z239,z6]),(0,[z1,z2,z3,z4,z5,z22,z33]),(1,[z1,z147,z240,z4,z5,z6]),(1,[z1,z105,z3,z4,z5,z93]),(0,[z1,z2,z3,z4,z241,z5,z6]),(0,[z183,z1,z3,z4,z5,z184,z6])],[(0,[z1,z2,z3,z4,z5,z6,z242]),(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z1,z2,z244,z3,z4,z5,z6]),(0,[z1,z245,z2,z3,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z15]),(1,[z183,z1,z3,z4,z5,z184]),(1,[z1,z2,z3,z112,z68,z6]),(0,[z1,z2,z3,z4,z5,z246,z6])],[(0,[z1,z2,z3,z4,z40,z26,z6]),(0,[z1,z2,z3,z4,z5,z7,z6]),(0,[z1,z9,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z6]),(1,[z1,z2,z3,z4,z5,z248]),(0,[z1,z2,z249,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z31]),(0,[z54,z1,z2,z3,z4,z5,z22]),(0,[z250,z1,z2,z3,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z15])],[(0,[z251,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z89,z4,z5,z6,z8]),(0,[z1,z2,z3,z4,z5,z252,z6]),(0,[z253,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z254,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z6]),(1,[z1,z2,z18,z3,z4,z95]),(0,[z1,z2,z3,z4,z5,z6,z255])]],
   [[(0,[z1,z2,z256,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z52]),(0,[z1,z2,z3,z257,z4,z5,z6])],[(0,[z151,z1,z2,z3,z4,z5,z31])],[(0,[z258,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z259,z5,z6]),(0,[z1,z2,z3,z4,z50,z5,z6]),(0,[z1,z2,z260,z3,z4,z5,z6]),(0,[z183,z1,z2,z3,z4,z101,z5]),(0,[z1,z2,z3,z28,z4,z5,z6]),(0,[z261,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z262,z5,z6]),(0,[z263,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z264,z6]),(0,[z265,z1,z2,z3,z4,z5,z6]),(0,[z1,z266,z2,z3,z4,z5,z6]),(0,[z1,z267,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z268,z6]),(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z270]),(0,[z1,z2,z3,z271,z4,z5,z6])],[(0,[z272,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z273,z6])],[(0,[z55,z1,z2,z3,z4,z40,z6]),(0,[z1,z57,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z274,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z87])],[(0,[z275,z1,z2,z3,z4,z5,z6]),(0,[z116,z1,z2,z18,z3,z4,z5]),(0,[z276,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z277,z3,z4,z5,z6]),(0,[z278,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z279,z5,z6]),(0,[z42,z1,z9,z3,z4,z5,z6]),(0,[z1,z2,z134,z4,z84,z5,z6])],[(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z281,z5,z6])],[(0,[z1,z2,z3,z62,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z282,z6]),(0,[z1,z2,z3,z4,z5,z6,z283]),(0,[z183,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z68,z5,z41,z6])],[(0,[z1,z2,z3,z4,z5,z284,z6]),(0,[z1,z2,z3,z285,z4,z5,z6]),(0,[z125,z1,z2,z3,z5,z41,z6]),(1,[z1,z2,z3,z4,z5,z15])],[(0,[z1,z2,z286,z3,z4,z5,z6]),(1,[z250,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z44,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z15])],[],[(0,[z1,z2,z3,z4,z5,z190,z6]),(0,[z1,z2,z3,z4,z5,z6,z287]),(0,[z1,z2,z3,z4,z5,z6,z288]),(0,[z42,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z15])],[(1,[z1,z2,z167,z3,z5,z6]),(0,[z125,z1,z2,z3,z12,z5,z6]),(0,[z1,z2,z3,z289,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z5,z15])]],
   [[(0,[z1,z2,z3,z290,z4,z5,z6]),(1,[z116,z2,z3,z4,z5,z7]),(0,[z79,z1,z2,z3,z4,z5,z32])],[(0,[z1,z2,z3,z4,z5,z291,z6]),(0,[z1,z292,z2,z3,z4,z5,z6]),(0,[z1,z2,z293,z3,z4,z5,z6]),(0,[z1,z294,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z295,z4,z5,z6])],[(0,[z296,z1,z2,z3,z4,z5,z6]),(0,[z1,z147,z2,z240,z4,z5,z6]),(0,[z297,z1,z2,z3,z4,z5,z6])],[(0,[z298,z1,z2,z3,z4,z5,z6]),(0,[z299,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z300,z3,z4,z5,z6]),(0,[z1,z2,z167,z3,z5,z49,z6]),(0,[z71,z1,z2,z29,z4,z5,z6]),(0,[z1,z2,z3,z112,z4,z5,z6]),(0,[z1,z2,z301,z3,z4,z5,z6])],[(0,[z1,z2,z96,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z302,z5,z6]),(1,[z47,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z93]),(0,[z1,z2,z3,z4,z303,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z32])],[(0,[z1,z304,z2,z3,z4,z5,z6]),(0,[z166,z2,z3,z62,z4,z5,z6]),(0,[z1,z2,z305,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z306,z5,z6]),(1,[z1,z2,z16,z3,z41,z6])],[(0,[z1,z2,z3,z4,z307,z5,z6]),(0,[z308,z1,z2,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z309,z5,z6]),(0,[z55,z2,z3,z4,z40,z5,z6]),(0,[z1,z2,z3,z4,z5,z310,z6]),(0,[z51,z1,z2,z3,z311,z5,z6]),(0,[z312,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z19])],[(0,[z47,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z313,z4,z5,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z270]),(0,[z1,z2,z3,z4,z315,z5,z6]),(1,[z125,z1,z2,z3,z5,z22])]],
   [[(0,[z316,z1,z2,z3,z4,z5,z6]),(1,[z1,z131,z3,z4,z5,z6]),(0,[z1,z317,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z318,z6])],[(0,[z1,z2,z3,z319,z4,z5,z6]),(0,[z1,z2,z240,z3,z4,z5,z15]),(0,[z1,z3,z12,z4,z113,z5,z6]),(0,[z1,z57,z3,z4,z58,z5,z6]),(0,[z320,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z248,z6]),(0,[z1,z2,z321,z3,z4,z5,z22])],[(0,[z322,z1,z2,z3,z4,z5,z6]),(0,[z166,z1,z2,z16,z3,z5,z6]),(0,[z1,z2,z3,z323,z4,z5,z6]),(0,[z132,z1,z2,z3,z5,z7,z6]),(0,[z183,z1,z2,z3,z4,z5,z15])],[(0,[z324,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z325,z4,z5,z6]),(1,[z1,z2,z3,z4,z101,z19])],[(0,[z151,z1,z2,z108,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z326,z6]),(0,[z166,z1,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z4,z5,z327,z6]),(0,[z166,z1,z2,z3,z5,z6,z15]),(0,[z1,z328,z2,z3,z4,z5,z6])],[(0,[z1,z57,z39,z3,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z33]),(0,[z329,z1,z2,z3,z4,z5,z6]),(0,[z330,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z1,z332,z2,z3,z4,z5,z6]),(0,[z1,z2,z80,z4,z5,z6,z8]),(0,[z1,z2,z3,z4,z5,z333,z6]),(0,[z1,z2,z3,z4,z5,z334,z6])],[(0,[z51,z1,z2,z3,z4,z335,z6]),(0,[z51,z1,z2,z325,z4,z5,z6])]],
   [[(0,[z1,z336,z2,z3,z4,z5,z6]),(1,[z1,z2,z224,z4,z5,z6]),(0,[z51,z1,z3,z325,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z247,z6]),(0,[z1,z2,z3,z4,z5,z337,z6]),(0,[z1,z2,z338,z3,z4,z5,z6]),(0,[z1,z2,z339,z3,z4,z5,z6])],[(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z34,z1,z147,z2,z4,z5,z6]),(0,[z1,z2,z3,z341,z4,z5,z6])],[(1,[z151,z2,z89,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z6]),(0,[z342,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z35,z5,z15]),(0,[z343,z1,z2,z3,z4,z5,z22])],[(0,[z1,z2,z3,z4,z344,z5,z6]),(1,[z205,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z345])],[(0,[z346,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z108,z4,z84,z5,z6]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z1,z2,z3,z4,z5,z348,z6]),(0,[z1,z2,z3,z4,z5,z32,z184]),(0,[z1,z2,z3,z4,z5,z349,z6])],[(0,[z1,z2,z3,z4,z5,z6,z350]),(0,[z1,z2,z3,z4,z5,z6,z351])],[(0,[z1,z2,z3,z4,z5,z352,z6]),(1,[z166,z1,z2,z3,z5,z15]),(0,[z1,z2,z3,z4,z5,z353,z6]),(0,[z1,z2,z3,z4,z5,z354,z6]),(0,[z355,z1,z2,z3,z4,z5,z6]),(0,[z356,z1,z2,z3,z4,z5,z22])],[(0,[z47,z1,z2,z3,z4,z5,z15]),(0,[z357,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z358,z5,z6])]],
   [[(0,[z1,z2,z359,z3,z4,z5,z6]),(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z358,z5,z6])],[(0,[z1,z361,z2,z3,z4,z5,z6])],[(0,[z1,z2,z108,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z362,z6]),(0,[z1,z2,z3,z4,z5,z26,z22])],[(1,[z1,z2,z3,z363,z5,z6]),(0,[z364,z1,z2,z3,z4,z5,z6]),(1,[z42,z1,z3,z12,z5,z6]),(0,[z1,z105,z2,z3,z4,z5,z184]),(0,[z1,z2,z3,z365,z4,z5,z6]),(0,[z1,z2,z80,z3,z4,z5,z6]),(1,[z79,z1,z2,z4,z5,z32])],[(0,[z1,z2,z366,z3,z4,z5,z6]),(0,[z367,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z363,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z22]),(0,[z1,z2,z368,z3,z4,z5,z6]),(0,[z1,z2,z3,z369,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z370,z6]),(0,[z1,z147,z2,z4,z35,z5,z6]),(0,[z1,z2,z3,z4,z371,z5,z6])],[(0,[z1,z39,z3,z4,z5,z26,z6]),(0,[z2,z108,z3,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z372]),(0,[z1,z373,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z374,z6]),(0,[z1,z2,z3,z375,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z350]),(0,[z1,z2,z3,z12,z4,z5,z6]),(0,[z1,z2,z376,z3,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z377,z5,z6]),(0,[z1,z2,z378,z3,z4,z5,z6])]],
   [[(0,[z2,z96,z3,z89,z4,z5,z6]),(0,[z23,z1,z2,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z379]),(1,[z1,z2,z3,z113,z5,z15]),(0,[z380,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z101,z6])],[(0,[z381,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z282,z6]),(0,[z1,z2,z3,z92,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z5,z15]),(0,[z382,z1,z2,z3,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z22])],[(1,[z47,z1,z2,z3,z5,z15]),(0,[z1,z2,z3,z4,z383,z5,z6]),(0,[z384,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z385,z6]),(0,[z1,z2,z3,z4,z5,z386,z6]),(0,[z1,z2,z3,z4,z5,z41,z6]),(0,[z343,z1,z2,z3,z4,z5,z15])],[(0,[z387,z1,z2,z3,z4,z5,z6]),(0,[z388,z1,z2,z3,z4,z5,z6]),(0,[z55,z21,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z113,z5,z6]),(0,[z389,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z390,z5,z6])],[(0,[z391,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z392,z6]),(0,[z1,z2,z14,z3,z4,z5,z6]),(0,[z79,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z5,z32,z6,z8])],[(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z393,z3,z4,z5,z6]),(0,[z394,z1,z2,z3,z4,z5,z6]),(0,[z395,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z22])],[(0,[z1,z2,z3,z396,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z33,z8]),(0,[z397,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z398,z6]),(0,[z1,z2,z3,z399,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z15]),(0,[z400,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z5,z401,z22])]],
   [[(0,[z402,z1,z2,z3,z4,z5,z15]),(0,[z55,z2,z96,z3,z4,z5,z6]),(0,[z1,z2,z3,z12,z84,z5,z6]),(0,[z1,z2,z134,z3,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z403,z6]),(0,[z1,z2,z16,z3,z112,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z404])],[(1,[z1,z2,z3,z4,z405,z6]),(0,[z78,z1,z2,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z406,z5,z6]),(0,[z1,z2,z3,z407,z4,z5,z6]),(0,[z408,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z178,z6]),(0,[z1,z57,z2,z3,z4,z5,z22]),(0,[z1,z2,z409,z3,z4,z5,z6])],[(0,[z410,z1,z2,z3,z4,z5,z6]),(0,[z1,z240,z3,z325,z4,z5,z6]),(0,[z411,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z15])],[(0,[z1,z2,z3,z4,z405,z5,z6]),(0,[z51,z1,z2,z240,z4,z5,z6]),(0,[z1,z412,z2,z3,z4,z5,z6])],[(0,[z413,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z63]),(0,[z1,z2,z3,z4,z5,z49,z15]),(0,[z1,z2,z3,z4,z414,z5,z6]),(0,[z1,z415,z2,z3,z4,z5,z6]),(0,[z72,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z416,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z326]),(0,[z1,z2,z417,z3,z4,z5,z6]),(0,[z1,z2,z418,z3,z4,z5,z6])],[(0,[z1,z2,z3,z419,z4,z5,z6]),(0,[z2,z3,z4,z40,z5,z49,z6]),(0,[z1,z2,z3,z4,z5,z184,z15]),(0,[z78,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z420,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z421,z6]),(0,[z1,z2,z16,z3,z4,z5,z22]),(1,[z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z5,z19,z6])],[(1,[z166,z2,z3,z62,z5,z6]),(0,[z1,z2,z3,z4,z58,z247,z6]),(0,[z1,z105,z2,z3,z204,z5,z6]),(0,[z1,z2,z422,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z4,z5,z22]),(0,[z1,z2,z3,z4,z19,z6,z95])]],
   [[(0,[z1,z2,z3,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z423]),(0,[z1,z2,z3,z4,z5,z32,z7]),(0,[z1,z2,z16,z3,z4,z5,z248])],[(0,[z1,z2,z3,z4,z5,z424,z6]),(1,[z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z425,z3,z4,z5,z26]),(0,[z1,z2,z426,z3,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z22]),(1,[z34,z1,z2,z4,z247,z6]),(0,[z1,z2,z3,z4,z5,z427,z6]),(0,[z1,z2,z3,z4,z5,z15,z372]),(0,[z428,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z100,z6]),(0,[z1,z2,z429,z3,z4,z5,z6])],[(0,[z78,z1,z2,z134,z3,z5,z6]),(0,[z1,z2,z3,z430,z4,z5,z6]),(0,[z1,z2,z44,z3,z4,z5,z22])],[(0,[z1,z2,z3,z4,z5,z431,z6]),(0,[z71,z1,z2,z3,z4,z101,z5]),(0,[z1,z2,z3,z4,z432,z5,z6]),(0,[z1,z433,z2,z3,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z179,z6]),(0,[z34,z1,z2,z3,z4,z247,z6]),(0,[z1,z2,z3,z4,z5,z60,z22])],[(0,[z21,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z4,z5,z158]),(0,[z1,z2,z3,z4,z24,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z7]),(1,[z1,z2,z3,z92,z5,z6]),(0,[z1,z105,z2,z3,z4,z101,z5]),(0,[z1,z2,z3,z4,z5,z6,z15]),(0,[z1,z2,z3,z4,z101,z5,z15])],[(0,[z434,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z435,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z436,z6]),(1,[z25,z1,z3,z4,z26,z6]),(0,[z1,z437,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z438]),(0,[z1,z439,z2,z3,z4,z5,z22])],[(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z440,z4,z5,z6]),(0,[z1,z2,z3,z441,z4,z5,z6]),(0,[z1,z2,z3,z442,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z127,z6])]],
   [[(0,[z151,z1,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z443,z6]),(0,[z1,z2,z444,z3,z4,z5,z6]),(0,[z445,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z231]),(0,[z1,z2,z3,z4,z5,z446,z6]),(0,[z1,z2,z447,z3,z4,z5,z6]),(0,[z1,z2,z448,z3,z4,z5,z6]),(0,[z1,z449,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z450,z6])],[(0,[z1,z57,z96,z3,z4,z5,z6]),(1,[z1,z2,z393,z3,z4,z5]),(1,[z1,z2,z444,z4,z5,z6]),(0,[z1,z2,z3,z5,z7,z177,z6]),(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z451,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z452,z26,z6]),(0,[z1,z2,z3,z453,z4,z5,z6]),(0,[z1,z2,z3,z4,z84,z5,z22]),(0,[z1,z454,z2,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z32])],[(0,[z1,z2,z3,z455,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z456]),(0,[z1,z2,z3,z4,z5,z457,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z459,z5,z6]),(1,[z1,z2,z3,z4,z414,z5]),(0,[z1,z2,z460,z3,z4,z5,z6])],[(0,[z1,z2,z461,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z462,z5,z6]),(0,[z1,z2,z240,z3,z4,z5,z22])],[(0,[z1,z463,z2,z3,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z456])],[(0,[z1,z2,z3,z4,z5,z464,z6]),(0,[z1,z2,z3,z4,z5,z465,z6]),(0,[z1,z2,z3,z4,z5,z466,z6]),(0,[z1,z2,z16,z3,z4,z5,z15])],[(0,[z402,z1,z39,z3,z4,z5,z6]),(0,[z1,z2,z467,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z468,z6]),(0,[z1,z2,z3,z4,z5,z469,z6])]],
   [[(0,[z1,z2,z89,z4,z84,z5,z6]),(0,[z470,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z128]),(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z472,z6]),(0,[z1,z2,z473,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z474,z6])],[(0,[z1,z475,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z476,z4,z5,z6]),(0,[z47,z2,z3,z4,z24,z5,z6])],[(0,[z1,z39,z2,z3,z4,z5,z15]),(1,[z1,z2,z477,z4,z5,z6])],[(0,[z1,z2,z478,z3,z4,z5,z6]),(0,[z23,z1,z2,z108,z4,z5,z6]),(0,[z166,z1,z2,z3,z62,z5,z6]),(0,[z1,z2,z3,z4,z5,z479,z6]),(0,[z1,z2,z18,z3,z358,z5,z6])],[(1,[z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z112,z4,z5,z480]),(0,[z1,z2,z3,z4,z101,z19,z6])],[(0,[z1,z481,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z482,z6]),(0,[z1,z2,z3,z4,z35,z5,z22]),(0,[z1,z2,z3,z483,z4,z5,z6])],[(0,[z484,z1,z2,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z485]),(0,[z1,z2,z3,z4,z486,z5,z6]),(0,[z1,z2,z3,z4,z5,z32,z15]),(0,[z1,z2,z3,z4,z487,z5,z6]),(0,[z1,z2,z3,z488,z4,z5,z6])],[(0,[z25,z1,z57,z3,z4,z5,z6]),(0,[z1,z2,z489,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z490,z6])]],
   [[(0,[z491,z1,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z15])],[(0,[z492,z1,z2,z3,z4,z5,z6]),(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z1,z105,z3,z4,z5,z6,z93]),(1,[z1,z2,z14,z84,z5,z6]),(0,[z1,z2,z3,z4,z84,z5,z15]),(0,[z1,z493,z2,z3,z4,z5,z6]),(0,[z1,z2,z321,z3,z4,z5,z6])],[(0,[z402,z1,z2,z3,z4,z190,z6]),(0,[z1,z147,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z494,z5,z6]),(1,[z1,z2,z425,z3,z4,z5]),(0,[z1,z2,z3,z495,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z184]),(0,[z1,z2,z134,z14,z3,z5,z6]),(0,[z1,z2,z3,z496,z4,z5,z6])],[(0,[z1,z2,z3,z4,z497,z5,z6]),(1,[z55,z2,z3,z4,z40,z6]),(0,[z1,z2,z498,z3,z4,z5,z6]),(0,[z71,z1,z2,z3,z4,z5,z15])],[(0,[z1,z2,z3,z499,z4,z5,z6]),(0,[z1,z138,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z477,z4,z5,z6]),(0,[z500,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z108,z3,z4,z5,z22]),(0,[z1,z105,z2,z3,z4,z5,z15]),(0,[z1,z2,z44,z3,z4,z35,z6]),(0,[z1,z2,z3,z112,z4,z68,z6])],[(0,[z501,z1,z2,z3,z4,z5,z6]),(0,[z1,z502,z2,z3,z4,z5,z6]),(0,[z47,z166,z2,z3,z4,z5,z6]),(0,[z47,z1,z2,z16,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z503,z6]),(0,[z1,z2,z4,z35,z5,z247,z6])],[(0,[z1,z2,z3,z4,z504,z5,z6]),(0,[z1,z2,z3,z363,z5,z49,z6]),(0,[z1,z2,z3,z4,z5,z505,z6]),(0,[z1,z2,z3,z506,z4,z5,z6])]],
   [[(0,[z507,z1,z2,z3,z4,z5,z6]),(0,[z47,z1,z2,z3,z24,z5,z6]),(0,[z47,z1,z2,z3,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z6,z508]),(0,[z509,z1,z2,z3,z4,z5,z6])],[(1,[z402,z96,z3,z4,z5,z6]),(0,[z510,z1,z2,z3,z4,z5,z6]),(0,[z1,z511,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z58,z5,z22]),(0,[z1,z2,z3,z4,z512,z5,z6]),(0,[z1,z2,z3,z4,z513,z5,z6])],[(0,[z1,z2,z3,z4,z282,z5,z6])],[(0,[z1,z2,z3,z4,z514,z5,z6]),(0,[z1,z2,z3,z4,z68,z5,z15])],[(0,[z1,z2,z515,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z5,z22]),(0,[z25,z1,z2,z3,z4,z58,z6]),(0,[z25,z1,z2,z3,z4,z26,z6])],[(0,[z1,z2,z3,z4,z5,z516,z6]),(0,[z1,z9,z2,z3,z113,z5,z6])],[(0,[z402,z1,z2,z3,z4,z405,z6]),(0,[z21,z2,z3,z4,z5,z49,z6]),(0,[z1,z2,z3,z4,z517,z5,z6]),(0,[z1,z2,z3,z4,z518,z5,z6]),(0,[z519,z1,z2,z3,z4,z5,z6])],[(0,[z520,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z521])]],
   [[(0,[z1,z39,z3,z4,z113,z5,z6]),(0,[z1,z147,z240,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z178])],[(0,[z47,z1,z2,z3,z4,z5,z522]),(1,[z1,z2,z3,z4,z5,z211]),(0,[z523,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z524,z4,z5,z6])],[(0,[z1,z2,z3,z525,z4,z5,z6]),(1,[z51,z1,z325,z4,z5,z6]),(0,[z1,z147,z2,z3,z4,z5,z15]),(0,[z526,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z112,z68,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z22])],[(0,[z402,z1,z2,z3,z4,z5,z22]),(1,[z1,z2,z3,z527,z5,z6])],[(0,[z79,z1,z2,z89,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z158]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z1,z2,z3,z4,z527,z5,z6]),(0,[z529,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z530,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z531]),(0,[z1,z2,z3,z4,z68,z40,z6]),(0,[z1,z2,z18,z3,z4,z5,z8])],[(0,[z47,z1,z2,z477,z4,z5,z6]),(0,[z199,z1,z2,z3,z4,z5,z6])],[(0,[z402,z21,z2,z3,z4,z5,z6]),(0,[z42,z1,z39,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z532,z6]),(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z40,z5,z22]),(0,[z25,z511,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z452,z6]),(0,[z1,z2,z533,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z534,z5,z6]),(0,[z1,z2,z3,z535,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z536,z4,z5,z6]),(0,[z1,z2,z48,z3,z4,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z22])],[(0,[z1,z2,z538,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z539,z5,z6]),(0,[z1,z2,z3,z4,z58,z5,z15]),(0,[z79,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z540,z5,z6])],[(0,[z183,z1,z2,z18,z3,z4,z5])],[(0,[z47,z125,z1,z2,z3,z5,z6]),(0,[z125,z166,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z541,z6]),(0,[z1,z3,z4,z5,z184,z6,z93])],[(0,[z402,z2,z96,z3,z4,z5,z6]),(0,[z542,z1,z2,z3,z4,z5,z6]),(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z93,z8]),(0,[z1,z2,z3,z4,z5,z184,z8]),(0,[z1,z2,z16,z3,z5,z41,z6])],[(0,[z1,z2,z3,z4,z5,z544,z6]),(0,[z1,z2,z3,z4,z5,z545,z6]),(0,[z1,z2,z3,z4,z5,z546,z6]),(0,[z261,z1,z2,z3,z4,z5,z6])],[(0,[z547,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z63]),(0,[z1,z2,z3,z4,z5,z22,z7]),(0,[z1,z2,z3,z548,z4,z5,z6]),(0,[z1,z2,z3,z204,z4,z5,z6]),(0,[z1,z2,z549,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z550]),(0,[z34,z1,z2,z3,z4,z5,z15]),(0,[z551,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z238,z5,z22])],[(0,[z1,z2,z3,z4,z5,z6,z552]),(0,[z1,z2,z3,z4,z553,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z554]),(0,[z1,z2,z3,z4,z5,z335,z6]),(0,[z1,z2,z14,z4,z84,z5,z6]),(0,[z1,z2,z18,z3,z4,z5,z95])],[(0,[z1,z57,z2,z3,z4,z5,z6])],[(0,[z151,z1,z2,z3,z4,z5,z326]),(0,[z1,z2,z3,z4,z5,z555,z6]),(0,[z1,z556,z2,z3,z4,z5,z6]),(0,[z1,z557,z2,z3,z4,z5,z6]),(0,[z558,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z22]),(0,[z1,z2,z3,z4,z5,z559,z6])],[(0,[z402,z1,z96,z3,z4,z5,z6]),(0,[z151,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z58,z40,z6]),(0,[z1,z2,z3,z4,z5,z6,z10]),(0,[z1,z2,z3,z4,z5,z6,z8]),(0,[z1,z2,z3,z4,z101,z5,z8]),(0,[z1,z2,z3,z4,z560,z5,z6])],[(0,[z561,z1,z2,z3,z4,z5,z6]),(0,[z21,z39,z2,z3,z4,z5,z6]),(0,[z562,z1,z2,z3,z4,z5,z6])],[(0,[z125,z1,z2,z3,z113,z5,z6]),(0,[z1,z2,z3,z563,z4,z5,z6]),(0,[z564,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z209,z15])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z565,z6])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z40,z5,z15]),(0,[z566,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z567,z6]),(1,[z1,z2,z3,z38,z5,z6])],[(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z568,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z134,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z84,z5,z6]),(0,[z1,z569,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z137])],[(0,[z1,z570,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z231]),(1,[z1,z2,z3,z4,z5,z222]),(0,[z1,z2,z571,z3,z4,z5,z6]),(1,[z1,z2,z3,z112,z5,z15]),(0,[z1,z2,z3,z5,z22,z6,z15])],[(0,[z1,z2,z3,z4,z5,z15,z33])],[(0,[z1,z2,z572,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z456]),(0,[z1,z2,z3,z4,z573,z5,z6]),(0,[z1,z2,z3,z4,z5,z228,z15]),(0,[z1,z2,z3,z4,z5,z6,z81])],[(0,[z1,z39,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z574,z5,z6]),(0,[z1,z2,z44,z3,z4,z5,z137]),(0,[z575,z1,z2,z3,z4,z5,z6])],[(0,[z576,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z577,z6]),(0,[z235,z1,z2,z3,z4,z5,z15]),(0,[z1,z439,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z101,z5,z95]),(0,[z1,z2,z3,z4,z5,z6,z95]),(0,[z578,z1,z2,z3,z4,z5,z6])],[(0,[z1,z579,z2,z3,z4,z5,z6]),(0,[z1,z580,z2,z3,z4,z5,z6]),(0,[z23,z2,z108,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z522]),(0,[z51,z269,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z581,z4,z5,z6]),(0,[z1,z2,z80,z3,z4,z5,z32])]],
   [[(0,[z1,z2,z3,z4,z5,z582,z6]),(0,[z1,z2,z583,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z50,z5,z49]),(0,[z1,z2,z584,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z585]),(0,[z586,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z7,z15]),(0,[z1,z9,z2,z3,z4,z5,z15]),(1,[z587,z1,z2,z4,z5,z6]),(0,[z1,z2,z588,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z247,z15]),(0,[z1,z2,z3,z4,z5,z6,z589])],[(0,[z1,z2,z3,z590,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z22]),(0,[z78,z1,z2,z3,z84,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z591]),(1,[z1,z2,z3,z5,z22,z15])],[(0,[z1,z2,z240,z3,z4,z5,z6]),(0,[z1,z2,z3,z592,z4,z5,z6]),(0,[z125,z1,z2,z3,z112,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z15])],[(0,[z1,z2,z593,z3,z4,z5,z6]),(0,[z1,z2,z594,z3,z4,z5,z6]),(0,[z183,z1,z2,z3,z4,z5,z6])],[(0,[z54,z1,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z4,z49,z41,z6]),(1,[z1,z2,z3,z311,z5,z6]),(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z8])],[(0,[z1,z131,z2,z3,z4,z5,z6]),(0,[z1,z596,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z311,z5,z6]),(0,[z1,z2,z3,z4,z5,z597,z6]),(0,[z1,z2,z3,z4,z5,z598,z6]),(0,[z1,z2,z3,z28,z4,z5,z15])]],
   [[(0,[z599,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z522]),(0,[z51,z1,z147,z3,z4,z5,z6]),(0,[z1,z2,z3,z600,z4,z5,z6]),(0,[z601,z1,z2,z3,z4,z5,z6]),(0,[z1,z105,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z5,z41,z6,z15])],[(0,[z1,z2,z96,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z602,z5,z6]),(0,[z1,z2,z3,z603,z4,z5,z6])],[(0,[z604,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z135])],[(0,[z1,z2,z605,z3,z4,z5,z6]),(0,[z1,z2,z606,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z607,z5,z6])],[(0,[z608,z1,z2,z3,z4,z5,z6]),(0,[z1,z609,z2,z3,z4,z5,z6]),(1,[z511,z2,z3,z4,z5,z6]),(0,[z1,z610,z2,z3,z4,z5,z6]),(0,[z1,z2,z16,z3,z4,z41,z6])],[(0,[z1,z2,z3,z4,z611,z5,z6]),(0,[z1,z2,z612,z3,z4,z5,z6]),(0,[z1,z2,z3,z113,z5,z6,z15]),(0,[z1,z2,z3,z4,z5,z613,z6]),(0,[z1,z2,z3,z4,z35,z5,z6]),(0,[z1,z2,z3,z112,z4,z5,z227])],[(0,[z1,z2,z3,z614,z4,z5,z6]),(0,[z1,z2,z3,z4,z68,z5,z22])],[(0,[z47,z1,z2,z3,z62,z5,z6]),(0,[z1,z2,z3,z62,z4,z5,z15]),(0,[z2,z3,z4,z5,z7,z6,z33]),(0,[z116,z1,z2,z3,z4,z101,z5]),(1,[z1,z2,z3,z4,z335,z6]),(0,[z1,z2,z3,z4,z5,z6,z615]),(0,[z1,z2,z3,z4,z5,z616,z6]),(0,[z617,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z618,z4,z5,z6]),(0,[z1,z2,z3,z4,z619,z5,z6]),(0,[z1,z2,z3,z325,z4,z5,z22])],[(0,[z1,z2,z3,z4,z5,z620,z6]),(0,[z71,z1,z2,z444,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z7]),(0,[z51,z1,z2,z4,z35,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z95]),(0,[z1,z2,z3,z4,z5,z327,z22])],[(0,[z1,z96,z3,z4,z5,z26,z6]),(0,[z47,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z621]),(0,[z1,z2,z3,z4,z622,z5,z6])],[(0,[z1,z2,z3,z4,z623,z5,z6]),(0,[z116,z71,z2,z3,z4,z5,z6]),(0,[z42,z1,z2,z3,z4,z5,z15]),(1,[z1,z2,z80,z4,z5,z8])],[(0,[z624,z1,z2,z3,z4,z5,z6]),(0,[z625,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z626,z3,z4,z5,z6])],[(0,[z1,z2,z108,z3,z4,z5,z6]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z5,z179]),(0,[z1,z2,z3,z4,z628,z5,z6]),(0,[z1,z2,z3,z4,z629,z5,z6])],[(0,[z630,z1,z2,z3,z4,z5,z6]),(0,[z631,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z32]),(0,[z1,z2,z3,z4,z5,z480,z6])],[(0,[z2,z96,z3,z4,z5,z49,z6]),(0,[z1,z2,z3,z4,z5,z632,z6]),(0,[z1,z633,z2,z3,z4,z5,z6]),(0,[z78,z1,z2,z108,z4,z5,z6]),(0,[z116,z1,z2,z3,z4,z5,z22])]],
   [[(0,[z634,z1,z2,z3,z4,z5,z6]),(0,[z1,z9,z3,z4,z113,z5,z6]),(0,[z1,z2,z3,z4,z35,z26,z6]),(0,[z1,z2,z3,z635,z4,z5,z6]),(0,[z1,z636,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z112,z4,z5,z15])],[(0,[z1,z2,z96,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z6,z637]),(0,[z1,z2,z3,z4,z5,z638,z6]),(0,[z639,z1,z2,z3,z4,z5,z6]),(0,[z34,z1,z2,z4,z5,z247,z6]),(0,[z1,z2,z3,z4,z5,z349,z22])],[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z54,z2,z3,z4,z5,z49,z6]),(0,[z183,z1,z2,z3,z4,z5,z93]),(0,[z640,z1,z2,z3,z4,z5,z6])],[(1,[z21,z39,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z641,z5,z6])],[(0,[z642,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z113,z5,z6]),(0,[z25,z250,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z643])],[(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z644,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z645,z5,z6])],[(0,[z21,z1,z39,z3,z4,z5,z6])],[(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z647,z1,z2,z3,z4,z5,z6]),(0,[z648,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z649,z6])]],
   [[(0,[z1,z2,z3,z4,z650,z5,z6]),(0,[z1,z2,z3,z325,z4,z5,z15]),(1,[z1,z2,z4,z5,z452,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z2,z80,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z652,z5,z6])],[(0,[z34,z1,z2,z3,z4,z5,z22]),(0,[z356,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z653,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z654,z6]),(1,[z1,z48,z3,z4,z5,z6]),(0,[z1,z655,z2,z3,z4,z5,z6]),(0,[z656,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z15,z615]),(0,[z1,z2,z18,z3,z4,z5,z6])],[(0,[z402,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z657,z4,z5,z6]),(1,[z1,z538,z3,z4,z5,z6]),(0,[z1,z2,z3,z658,z4,z5,z6]),(0,[z1,z2,z3,z12,z4,z5,z22]),(0,[z1,z2,z80,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z334,z15])],[(0,[z1,z2,z659,z3,z4,z5,z6]),(0,[z1,z2,z18,z3,z38,z5,z6])],[(0,[z1,z660,z2,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z68,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z6]),(0,[z1,z2,z3,z4,z26,z247,z6]),(0,[z1,z2,z338,z3,z4,z5,z15]),(0,[z1,z2,z339,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z661,z6])],[(0,[z54,z1,z538,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z211,z6]),(0,[z1,z2,z3,z4,z5,z662,z6]),(0,[z1,z2,z663,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z664,z5,z6])],[(0,[z1,z665,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z6]),(1,[z71,z2,z3,z4,z5,z33]),(0,[z116,z1,z2,z3,z4,z5,z15]),(0,[z666,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z151,z2,z3,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z667,z5,z6]),(0,[z537,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z668,z4,z5,z6]),(0,[z51,z34,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z12,z5,z6,z15]),(0,[z183,z1,z105,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z184,z6]),(0,[z1,z2,z14,z3,z4,z5,z22])],[(0,[z23,z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z669,z4,z5,z6])],[(0,[z71,z1,z2,z18,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z33]),(0,[z1,z147,z2,z325,z4,z5,z6]),(0,[z1,z2,z3,z670,z4,z5,z6]),(0,[z587,z1,z2,z4,z5,z26,z6]),(0,[z1,z2,z3,z671,z4,z5,z6])],[(0,[z428,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z672,z4,z5,z6]),(0,[z1,z9,z2,z3,z12,z5,z6]),(0,[z673,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z674,z6])],[(0,[z1,z2,z675,z3,z4,z5,z6]),(0,[z2,z3,z62,z4,z24,z5,z6]),(0,[z42,z1,z3,z12,z4,z5,z6]),(0,[z1,z105,z2,z18,z3,z4,z5])],[(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z23,z21,z2,z3,z4,z5,z6]),(0,[z151,z1,z2,z89,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z350]),(0,[z1,z2,z3,z4,z5,z135,z6]),(0,[z677,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z678,z6])]],
   [[(1,[z1,z2,z3,z4,z115,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z2,z80,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z101,z5,z6])],[(0,[z1,z2,z3,z679,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z680]),(0,[z1,z2,z3,z4,z5,z681,z6]),(0,[z1,z2,z3,z4,z5,z6,z682]),(0,[z1,z2,z3,z4,z5,z683,z6]),(0,[z1,z2,z3,z4,z5,z684,z6]),(0,[z1,z2,z685,z3,z4,z5,z6]),(0,[z1,z2,z3,z686,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z687,z6])],[(0,[z1,z2,z688,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z401,z6]),(0,[z400,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z689,z6]),(0,[z1,z2,z3,z4,z371,z5,z15]),(0,[z1,z2,z3,z4,z5,z192,z6]),(0,[z1,z690,z2,z3,z4,z5,z6])],[(0,[z23,z2,z96,z3,z4,z5,z6]),(0,[z151,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z691,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z692,z6]),(0,[z1,z2,z3,z12,z4,z5,z15]),(0,[z1,z2,z693,z3,z4,z5,z6]),(0,[z1,z2,z694,z3,z4,z5,z6]),(0,[z78,z1,z2,z3,z4,z5,z22]),(0,[z695,z1,z2,z3,z4,z5,z6]),(0,[z1,z449,z2,z3,z4,z5,z6])],[(0,[z1,z2,z393,z3,z4,z5,z49]),(1,[z269,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z4,z696,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z222]),(0,[z1,z2,z3,z4,z5,z697,z6])],[(0,[z1,z2,z3,z89,z4,z5,z22]),(0,[z698,z1,z2,z3,z4,z5,z6]),(0,[z699,z1,z2,z3,z4,z5,z6]),(0,[z1,z9,z2,z3,z4,z5,z22]),(0,[z1,z105,z2,z3,z527,z5,z6]),(0,[z700,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z227])],[(0,[z1,z2,z3,z4,z701,z5,z6]),(0,[z1,z2,z425,z3,z4,z5,z6]),(0,[z702,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z41,z15])],[(0,[z1,z703,z2,z3,z4,z5,z6]),(0,[z704,z1,z2,z3,z4,z5,z6]),(0,[z55,z1,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z4,z5,z705,z6]),(0,[z706,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z414,z5,z26]),(0,[z1,z2,z3,z4,z5,z41,z15]),(1,[z1,z2,z3,z4,z5,z480]),(0,[z1,z2,z3,z4,z5,z22,z22])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[],[(1,[z2,z3,z707,z5,z6]),(0,[z1,z3,z708,z113,z5,z6]),(0,[z1,z2,z3,z455,z5,z15])],[(0,[z1,z2,z80,z4,z5,z8]),(0,[z1,z2,z3,z112,z315,z6])],[(0,[z1,z2,z167,z3,z5,z15]),(0,[z1,z2,z3,z4,z709,z5]),(0,[z116,z2,z3,z4,z262,z5]),(0,[z1,z2,z3,z4,z5,z710])],[(0,[z1,z703,z2,z3,z5,z15]),(0,[z1,z2,z3,z4,z5,z711]),(0,[z1,z2,z224,z4,z5,z22]),(0,[z1,z2,z3,z4,z712,z6]),(0,[z1,z9,z3,z113,z5,z6]),(0,[z25,z250,z3,z4,z26,z6]),(0,[z1,z2,z3,z4,z5,z713])],[(0,[z1,z2,z3,z4,z714,z6]),(0,[z673,z2,z108,z4,z5,z6])],[(0,[z715,z1,z2,z4,z5,z6]),(0,[z151,z2,z89,z4,z5,z22]),(0,[z71,z2,z249,z3,z4,z5]),(0,[z511,z2,z3,z4,z26,z6]),(0,[z511,z2,z3,z4,z58,z6])],[(0,[z1,z2,z3,z4,z5,z716]),(0,[z55,z2,z3,z4,z307,z6]),(0,[z1,z2,z3,z4,z717,z6]),(0,[z47,z2,z3,z24,z5,z522]),(0,[z205,z2,z3,z4,z5,z22]),(0,[z718,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z719]),(0,[z720,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z442,z5,z15])],[(0,[z47,z1,z2,z3,z282,z15]),(0,[z1,z2,z3,z5,z310,z15]),(0,[z721,z2,z3,z4,z5,z6]),(0,[z1,z2,z16,z3,z41,z15])],[(0,[z21,z39,z3,z4,z5,z6]),(0,[z1,z2,z3,z722,z5,z6]),(0,[z1,z2,z3,z723,z5,z6]),(0,[z2,z3,z4,z5,z724,z33]),(0,[z666,z1,z2,z4,z5,z32]),(0,[z1,z2,z14,z84,z5,z15]),(0,[z1,z2,z3,z4,z5,z725])],[(0,[z1,z2,z3,z4,z726,z6]),(0,[z1,z2,z3,z497,z5,z15]),(0,[z1,z727,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z177,z6]),(0,[z538,z3,z4,z5,z49,z6]),(0,[z1,z2,z4,z35,z335,z6]),(0,[z1,z2,z3,z4,z728,z6]),(0,[z1,z105,z3,z527,z5,z93]),(0,[z1,z2,z3,z358,z5,z22])],[(0,[z47,z2,z477,z24,z5,z6]),(0,[z1,z729,z3,z4,z5,z6]),(0,[z1,z2,z730,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z731]),(0,[z1,z2,z3,z732,z5,z26]),(1,[z1,z3,z4,z5,z733]),(0,[z2,z3,z4,z5,z734,z15])],[(0,[z1,z735,z3,z4,z5,z6]),(0,[z1,z2,z3,z736,z5,z6]),(0,[z1,z2,z73,z4,z5,z32]),(0,[z1,z2,z3,z4,z101,z737])],[(0,[z205,z2,z3,z92,z5,z6]),(0,[z1,z2,z738,z3,z4,z6]),(0,[z695,z1,z3,z4,z26,z6]),(0,[z1,z2,z739,z14,z5,z6])],[(0,[z2,z740,z3,z4,z5,z6]),(0,[z1,z2,z3,z68,z544,z6]),(0,[z1,z2,z3,z363,z5,z22]),(0,[z132,z116,z2,z3,z5,z7]),(0,[z51,z1,z325,z4,z163,z6]),(0,[z1,z2,z4,z5,z452,z6]),(0,[z42,z1,z3,z12,z5,z22]),(0,[z1,z2,z741,z4,z5,z6]),(0,[z1,z2,z18,z3,z527,z5])]],
   [[(0,[z1,z742,z2,z3,z5,z6]),(0,[z1,z138,z3,z4,z5,z522]),(0,[z54,z2,z393,z3,z4,z49]),(0,[z743,z1,z2,z4,z5,z6]),(0,[z1,z2,z739,z4,z5,z6]),(0,[z1,z2,z3,z744,z5,z6])],[(0,[z1,z48,z3,z4,z5,z6]),(0,[z1,z2,z3,z745,z5,z6])],[(0,[z402,z96,z3,z4,z5,z15]),(0,[z1,z538,z3,z4,z5,z6]),(0,[z1,z2,z746,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z733]),(0,[z1,z2,z338,z4,z5,z8]),(0,[z79,z1,z2,z4,z5,z713])],[(0,[z501,z96,z3,z4,z5,z6]),(0,[z644,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z4,z5,z747])],[(0,[z1,z2,z3,z4,z5,z724])],[(0,[z1,z138,z477,z4,z5,z6]),(0,[z1,z2,z3,z4,z282,z22]),(0,[z1,z2,z3,z4,z748,z6]),(0,[z587,z1,z2,z425,z4,z5]),(0,[z1,z2,z4,z5,z749,z6])],[(0,[z1,z740,z3,z4,z5,z6]),(0,[z1,z750,z3,z4,z5,z6]),(0,[z151,z2,z89,z4,z5,z15]),(0,[z1,z2,z3,z4,z751,z5]),(0,[z71,z2,z3,z4,z5,z33]),(0,[z1,z752,z3,z4,z5,z6]),(0,[z1,z2,z80,z4,z5,z127]),(0,[z1,z2,z3,z753,z41,z6]),(0,[z1,z2,z3,z68,z753,z6])],[(0,[z47,z1,z2,z3,z5,z87]),(0,[z1,z2,z3,z5,z348,z15])]],
   [[(0,[z2,z538,z3,z4,z49,z6]),(0,[z1,z754,z325,z4,z5,z6]),(0,[z755,z2,z3,z4,z5,z15])],[(0,[z1,z2,z3,z92,z5,z350]),(0,[z1,z449,z3,z4,z5,z93]),(0,[z756,z2,z3,z4,z5,z22])],[(0,[z1,z2,z3,z4,z5,z757]),(0,[z758,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z759])],[(0,[z1,z2,z3,z4,z5,z760]),(0,[z1,z2,z761,z3,z5,z6]),(0,[z1,z2,z3,z4,z762,z5]),(0,[z1,z439,z3,z4,z5,z184]),(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z2,z3,z358,z5,z15])],[(0,[z740,z96,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z2,z3,z527,z5,z15]),(0,[z765,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z405,z22]),(0,[z1,z2,z3,z4,z5,z766])],[(0,[z1,z2,z393,z3,z363,z5]),(0,[z1,z2,z3,z5,z767,z6]),(0,[z297,z2,z3,z4,z40,z6]),(0,[z1,z147,z240,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z768]),(0,[z1,z105,z3,z4,z5,z93]),(0,[z1,z769,z3,z4,z5,z6])],[(0,[z1,z2,z675,z3,z5,z15]),(0,[z1,z2,z3,z4,z115,z6]),(0,[z1,z538,z3,z4,z49,z6]),(0,[z1,z2,z3,z363,z5,z15]),(0,[z1,z2,z3,z311,z5,z350]),(0,[z1,z2,z3,z4,z5,z770]),(0,[z42,z1,z3,z12,z5,z15]),(0,[z1,z2,z3,z4,z238,z349])]],
   [[(0,[z1,z2,z3,z771,z5,z6]),(0,[z1,z2,z3,z4,z5,z772]),(0,[z1,z2,z773,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z774]),(0,[z1,z2,z3,z775,z5,z6]),(0,[z1,z2,z3,z776,z5,z6])],[(0,[z1,z96,z3,z4,z190,z6]),(0,[z166,z2,z3,z62,z5,z63]),(0,[z1,z2,z3,z4,z5,z777]),(0,[z1,z2,z778,z3,z4,z5]),(0,[z1,z2,z3,z38,z5,z22])],[(0,[z1,z779,z3,z4,z5,z6]),(0,[z1,z2,z321,z4,z5,z32])],[(0,[z269,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z780]),(0,[z1,z2,z3,z4,z163,z6]),(0,[z34,z1,z2,z4,z335,z6])],[(0,[z2,z3,z62,z707,z5,z6]),(0,[z1,z2,z3,z4,z5,z781]),(0,[z1,z2,z271,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z227])],[(0,[z1,z2,z3,z4,z5,z782]),(0,[z1,z2,z3,z5,z544,z15]),(0,[z783,z2,z3,z4,z5,z6]),(0,[z42,z1,z3,z12,z5,z13]),(0,[z1,z2,z3,z12,z5,z456]),(0,[z25,z1,z4,z452,z26,z6]),(0,[z34,z1,z2,z4,z247,z22]),(0,[z1,z2,z3,z5,z41,z15])],[(0,[z1,z2,z784,z4,z5,z6]),(0,[z47,z2,z3,z24,z5,z158]),(0,[z1,z2,z3,z4,z5,z785]),(0,[z1,z2,z3,z4,z5,z786]),(0,[z1,z2,z18,z3,z4,z438]),(0,[z787,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z390,z5,z15])],[(0,[z1,z2,z3,z4,z788,z6]),(0,[z1,z415,z3,z4,z58,z6])]],
   [[(0,[z1,z2,z3,z4,z335,z350]),(0,[z1,z2,z3,z4,z5,z789]),(0,[z25,z587,z1,z4,z26,z6])],[(0,[z402,z740,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z790]),(0,[z1,z2,z477,z4,z282,z6]),(0,[z166,z2,z3,z707,z5,z6]),(0,[z1,z2,z3,z92,z5,z22]),(0,[z1,z2,z3,z12,z5,z15]),(0,[z1,z449,z3,z113,z5,z6]),(0,[z1,z2,z14,z84,z5,z179]),(1,[z1,z2,z3,z4,z737])],[(0,[z458,z96,z3,z4,z5,z6]),(0,[z1,z2,z29,z4,z5,z6]),(0,[z54,z538,z3,z4,z49,z6]),(0,[z791,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z56,z5,z15]),(0,[z25,z1,z3,z4,z26,z22])],[(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z3,z113,z5,z209,z15]),(0,[z1,z2,z18,z3,z4,z482]),(0,[z1,z2,z3,z5,z403,z15])],[(0,[z677,z1,z2,z3,z5,z15])],[(0,[z1,z2,z3,z4,z405,z15]),(0,[z1,z2,z3,z4,z50,z5]),(0,[z1,z2,z444,z4,z5,z22]),(0,[z1,z2,z793,z4,z5,z6]),(0,[z183,z1,z3,z4,z5,z209])],[(0,[z316,z2,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z794]),(0,[z1,z2,z3,z4,z795,z5]),(0,[z1,z2,z3,z796,z5,z6]),(0,[z1,z2,z3,z5,z15,z232])],[(0,[z1,z2,z797,z4,z5,z6]),(0,[z1,z2,z3,z4,z798,z6]),(0,[z116,z2,z3,z4,z5,z724]),(0,[z1,z2,z3,z4,z799,z6]),(0,[z1,z2,z3,z4,z800,z6]),(0,[z1,z2,z3,z4,z5,z801])]],
   [[(0,[z250,z2,z3,z4,z5,z6]),(0,[z1,z475,z3,z113,z5,z6]),(0,[z1,z2,z3,z4,z5,z802])],[(0,[z1,z2,z3,z4,z803,z6]),(0,[z1,z2,z3,z4,z804,z6]),(0,[z51,z269,z325,z4,z5,z6]),(0,[z1,z57,z3,z4,z58,z6]),(0,[z1,z2,z3,z4,z5,z805]),(0,[z1,z806,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z807]),(0,[z1,z2,z3,z38,z5,z15])],[(0,[z1,z2,z224,z4,z5,z158]),(0,[z1,z2,z3,z323,z5,z15]),(0,[z205,z2,z3,z4,z5,z211]),(0,[z808,z2,z3,z4,z5,z15])],[(0,[z1,z2,z3,z4,z5,z809]),(0,[z47,z1,z138,z3,z5,z15]),(0,[z166,z2,z3,z62,z5,z15])],[(0,[z296,z1,z3,z4,z26,z6]),(0,[z253,z2,z3,z4,z40,z6]),(0,[z116,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z4,z5,z810]),(0,[z1,z2,z3,z573,z5,z15]),(0,[z1,z2,z811,z3,z4,z15])],[(0,[z1,z2,z3,z812,z5,z6]),(0,[z47,z2,z3,z707,z5,z6]),(0,[z166,z2,z3,z62,z5,z128]),(0,[z34,z1,z2,z4,z247,z15]),(0,[z1,z2,z4,z5,z763,z6]),(0,[z1,z2,z3,z5,z813,z6])],[(0,[z1,z2,z814,z4,z5,z6]),(0,[z1,z2,z477,z4,z5,z22]),(0,[z1,z2,z3,z4,z815,z5]),(0,[z1,z2,z3,z112,z753,z6])],[(0,[z1,z2,z3,z4,z5,z816]),(0,[z1,z2,z3,z4,z5,z817]),(0,[z818,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z819,z5]),(0,[z1,z2,z820,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z821]),(0,[z428,z2,z3,z4,z5,z334])]],
   [[(0,[z1,z2,z822,z3,z4,z190]),(0,[z47,z2,z3,z24,z5,z6]),(0,[z1,z2,z3,z4,z5,z823]),(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z2,z3,z4,z5,z825]),(0,[z1,z2,z3,z4,z335,z22]),(0,[z1,z240,z754,z4,z5,z6]),(0,[z1,z826,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z827]),(0,[z1,z2,z3,z4,z5,z828])],[],[(0,[z1,z2,z3,z4,z829,z6]),(0,[z1,z39,z3,z113,z5,z15]),(0,[z1,z2,z3,z4,z5,z830]),(0,[z125,z1,z2,z3,z5,z22])],[(0,[z1,z131,z3,z4,z5,z6]),(0,[z1,z57,z3,z4,z831,z6]),(0,[z1,z2,z3,z4,z5,z832])],[(0,[z42,z1,z3,z476,z5,z6]),(0,[z1,z833,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z834,z6]),(0,[z1,z2,z606,z84,z5,z6]),(0,[z1,z2,z3,z4,z5,z835]),(0,[z1,z2,z14,z84,z5,z22]),(0,[z1,z2,z3,z4,z5,z836])],[(0,[z1,z2,z3,z49,z41,z15]),(0,[z51,z1,z325,z4,z5,z350]),(0,[z1,z2,z3,z4,z831,z6]),(0,[z1,z3,z4,z5,z837,z6])],[(0,[z132,z1,z2,z3,z5,z6]),(0,[z55,z2,z3,z4,z40,z22]),(0,[z1,z2,z3,z311,z5,z15]),(0,[z537,z1,z2,z3,z4,z81]),(0,[z1,z2,z3,z4,z101,z19])]],
   [[(0,[z402,z96,z3,z4,z405,z6]),(0,[z1,z2,z838,z4,z5,z6]),(0,[z1,z839,z3,z4,z5,z6])],[(0,[z1,z138,z3,z4,z5,z6]),(0,[z1,z2,z3,z602,z5,z15]),(0,[z1,z2,z3,z840,z5,z6]),(0,[z1,z2,z18,z3,z358,z95])],[(0,[z1,z841,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z842,z6]),(0,[z1,z2,z3,z4,z843,z6]),(0,[z1,z2,z3,z5,z468,z15]),(0,[z235,z1,z3,z4,z5,z209])],[(0,[z1,z2,z3,z844,z5,z6]),(0,[z1,z2,z3,z4,z282,z158]),(0,[z1,z2,z3,z5,z845,z6]),(1,[z511,z3,z4,z26,z6])],[(0,[z1,z2,z3,z4,z5,z846]),(0,[z1,z2,z224,z4,z5,z6]),(0,[z847,z2,z3,z4,z5,z6])],[(0,[z1,z2,z848,z4,z5,z6]),(0,[z402,z96,z3,z4,z5,z22]),(0,[z1,z2,z3,z5,z32,z177]),(0,[z1,z2,z3,z4,z849,z6]),(0,[z1,z2,z3,z5,z830,z15])],[(0,[z1,z2,z3,z4,z850,z6]),(0,[z1,z2,z477,z4,z5,z15]),(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z2,z3,z732,z5,z6])],[(0,[z205,z2,z3,z4,z5,z6]),(0,[z1,z2,z168,z4,z5,z8]),(0,[z1,z2,z3,z527,z101,z5]),(0,[z1,z2,z3,z4,z5,z852])]],
   [[(0,[z210,z2,z3,z4,z49,z6]),(0,[z151,z2,z89,z4,z5,z326]),(0,[z166,z2,z3,z5,z334,z6]),(0,[z1,z2,z3,z4,z335,z15]),(0,[z36,z1,z2,z3,z5,z15])],[(0,[z1,z2,z108,z4,z5,z31]),(0,[z1,z2,z3,z4,z5,z853]),(0,[z1,z2,z167,z3,z41,z6]),(0,[z854,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z28,z5,z15])],[(0,[z1,z2,z855,z3,z5,z6]),(0,[z71,z2,z3,z4,z5,z724]),(0,[z37,z1,z2,z3,z5,z177]),(0,[z1,z2,z3,z5,z490,z15])],[(0,[z1,z48,z3,z4,z115,z6]),(0,[z1,z3,z4,z5,z733,z6])],[(0,[z1,z2,z3,z4,z856,z6]),(0,[z1,z2,z3,z4,z5,z857]),(0,[z587,z1,z2,z4,z247,z6])],[(0,[z96,z3,z4,z49,z26,z6]),(0,[z1,z2,z3,z4,z858,z6]),(0,[z1,z2,z3,z4,z859,z5])],[(0,[z1,z2,z3,z4,z5,z860]),(0,[z166,z1,z2,z3,z5,z87]),(0,[z51,z1,z325,z4,z5,z22]),(0,[z1,z2,z861,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z179])],[(0,[z1,z2,z3,z4,z862,z6]),(0,[z55,z2,z3,z4,z40,z15]),(0,[z863,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z527,z5,z22]),(0,[z79,z1,z2,z4,z5,z32])]],
   [[(0,[z1,z2,z864,z4,z5,z15])],[(0,[z1,z2,z3,z4,z190,z6]),(0,[z1,z2,z3,z4,z865,z190]),(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z2,z3,z358,z5,z8])],[(0,[z2,z3,z4,z5,z724,z6]),(0,[z1,z2,z3,z4,z5,z350]),(0,[z1,z2,z3,z4,z5,z867])],[(0,[z1,z868,z2,z3,z5,z6]),(0,[z1,z2,z869,z3,z4,z5]),(0,[z1,z2,z3,z4,z870,z6]),(1,[z1,z2,z3,z732,z5]),(0,[z1,z2,z3,z4,z5,z871])],[(0,[z1,z2,z3,z92,z5,z211]),(0,[z1,z2,z3,z204,z5,z6]),(0,[z872,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z282,z6]),(0,[z51,z1,z325,z92,z5,z6])],[(0,[z47,z1,z2,z3,z5,z15]),(0,[z1,z2,z224,z4,z5,z522]),(0,[z1,z2,z3,z514,z5,z15]),(0,[z1,z2,z873,z3,z4,z15]),(0,[z1,z2,z339,z3,z4,z45])],[(0,[z205,z2,z3,z311,z5,z6])]],
   [[(0,[z874,z1,z2,z3,z5,z6]),(0,[z55,z538,z3,z4,z5,z6]),(0,[z1,z875,z3,z4,z5,z6])],[(0,[z166,z2,z3,z377,z5,z6]),(0,[z1,z3,z4,z5,z831,z6]),(0,[z756,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z876]),(0,[z1,z2,z3,z4,z877,z5])],[(0,[z1,z2,z3,z4,z5,z878]),(0,[z2,z3,z4,z5,z851,z6])],[(0,[z71,z2,z29,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z879]),(0,[z1,z2,z739,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z880]),(0,[z1,z2,z3,z4,z881,z5]),(0,[z42,z1,z3,z12,z5,z231]),(0,[z1,z105,z489,z3,z4,z5]),(0,[z1,z2,z3,z358,z5,z95])],[(0,[z1,z2,z3,z4,z882,z5]),(0,[z1,z2,z883,z3,z4,z5]),(0,[z1,z2,z739,z84,z5,z6])],[(0,[z1,z2,z3,z4,z5,z884]),(0,[z1,z2,z29,z4,z5,z7]),(0,[z1,z2,z3,z4,z885,z6]),(0,[z51,z1,z325,z4,z5,z15]),(0,[z1,z2,z3,z5,z662,z15]),(0,[z1,z2,z4,z763,z247,z6]),(0,[z1,z2,z80,z4,z5,z713]),(0,[z886,z2,z3,z4,z5,z22])],[(0,[z1,z2,z3,z12,z5,z10])]],
   [[(0,[z1,z2,z3,z4,z5,z63]),(0,[z205,z2,z3,z4,z335,z6]),(0,[z887,z2,z3,z4,z5,z6]),(0,[z1,z2,z888,z4,z5,z6]),(0,[z1,z2,z3,z4,z732,z5]),(0,[z1,z3,z4,z5,z733,z93]),(0,[z1,z2,z3,z4,z889,z15]),(0,[z1,z2,z890,z4,z5,z6])],[(0,[z269,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z311,z5,z866]),(0,[z1,z2,z3,z112,z68,z480])],[(0,[z1,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z5,z891]),(0,[z1,z2,z3,z4,z5,z892]),(0,[z1,z2,z3,z407,z5,z15])],[(0,[z1,z893,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z894]),(0,[z1,z2,z3,z4,z335,z211]),(0,[z1,z412,z3,z113,z5,z6]),(0,[z183,z1,z3,z4,z5,z184]),(0,[z1,z2,z3,z5,z22,z577]),(0,[z1,z895,z3,z4,z5,z6]),(0,[z1,z2,z3,z112,z68,z6])],[(0,[z47,z48,z3,z24,z5,z6]),(0,[z1,z2,z477,z4,z5,z158]),(0,[z511,z3,z4,z5,z26,z6]),(0,[z1,z2,z3,z4,z5,z248]),(0,[z1,z2,z18,z3,z4,z81])],[(0,[z1,z2,z3,z707,z5,z6]),(0,[z1,z2,z277,z3,z5,z22]),(0,[z356,z1,z2,z3,z5,z15])],[(0,[z1,z2,z896,z4,z5,z6]),(0,[z1,z538,z3,z4,z40,z6]),(0,[z1,z897,z2,z3,z363,z5]),(0,[z1,z2,z3,z4,z5,z898]),(0,[z1,z2,z3,z4,z5,z899]),(0,[z1,z2,z18,z3,z4,z95]),(0,[z1,z2,z3,z4,z19,z737])],[(0,[z1,z96,z3,z113,z5,z15]),(0,[z21,z580,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z900]),(0,[z1,z2,z3,z4,z282,z522]),(0,[z1,z2,z3,z4,z901,z6]),(0,[z1,z2,z3,z4,z5,z902]),(0,[z1,z2,z3,z112,z5,z87]),(0,[z1,z2,z3,z4,z371,z228]),(0,[z37,z2,z3,z4,z5,z88])]],
   [[(0,[z1,z2,z903,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z904]),(0,[z1,z2,z3,z4,z5,z905]),(0,[z1,z2,z3,z4,z5,z906]),(0,[z1,z2,z3,z4,z907,z5])],[(0,[z125,z1,z2,z3,z5,z158]),(0,[z1,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z4,z5,z908]),(0,[z1,z2,z3,z909,z5,z6])],[(0,[z1,z2,z3,z5,z401,z15]),(0,[z25,z1,z3,z4,z26,z6]),(0,[z910,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z581,z5,z15]),(0,[z1,z2,z3,z5,z192,z15])],[(0,[z1,z2,z3,z4,z5,z911]),(0,[z1,z2,z3,z4,z5,z912]),(0,[z382,z2,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z913,z6]),(0,[z47,z2,z571,z3,z5,z6])],[(0,[z1,z2,z3,z914,z5,z6]),(0,[z1,z2,z605,z4,z5,z8]),(0,[z1,z2,z4,z5,z915,z6]),(0,[z1,z2,z3,z4,z5,z916]),(0,[z1,z2,z3,z5,z697,z15]),(0,[z1,z2,z917,z4,z5,z22])],[(0,[z1,z2,z3,z4,z5,z918]),(0,[z1,z2,z3,z919,z5,z6]),(0,[z1,z2,z393,z3,z4,z5]),(0,[z116,z1,z2,z3,z5,z177]),(0,[z1,z2,z339,z3,z41,z6])],[(0,[z547,z1,z2,z3,z5,z15]),(0,[z1,z2,z3,z115,z6,z15]),(0,[z1,z2,z920,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z921]),(0,[z587,z1,z2,z4,z5,z22]),(0,[z1,z2,z3,z4,z5,z456])],[(0,[z644,z1,z3,z4,z26,z6]),(0,[z1,z2,z3,z5,z22,z813])]],
   [[(0,[z21,z556,z3,z4,z5,z6]),(0,[z1,z2,z3,z922,z5,z6]),(0,[z1,z48,z224,z4,z5,z6])],[(0,[z1,z2,z3,z5,z923,z6]),(0,[z1,z2,z3,z4,z924,z6]),(0,[z1,z2,z3,z5,z13,z15]),(0,[z1,z2,z3,z4,z5,z925]),(0,[z312,z1,z2,z3,z5,z15])],[(0,[z1,z2,z3,z4,z5,z15]),(0,[z47,z2,z3,z24,z115,z6]),(0,[z1,z2,z3,z4,z926,z6]),(0,[z139,z1,z2,z3,z5,z15]),(0,[z1,z2,z3,z311,z5,z22])],[],[(0,[z1,z2,z3,z4,z927,z6]),(1,[z1,z48,z3,z5,z15]),(0,[z1,z2,z3,z50,z363,z5])],[(0,[z1,z2,z3,z4,z928,z6]),(0,[z47,z1,z2,z3,z5,z860]),(0,[z1,z2,z181,z3,z5,z15]),(0,[z1,z2,z3,z40,z41,z15]),(0,[z558,z1,z2,z3,z5,z15]),(0,[z1,z2,z425,z929,z3,z5]),(0,[z627,z1,z2,z4,z5,z32]),(0,[z1,z2,z3,z4,z5,z930])],[(0,[z1,z57,z3,z4,z279,z6]),(0,[z1,z2,z3,z68,z115,z6]),(0,[z1,z2,z167,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z931]),(0,[z932,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z933,z6]),(0,[z1,z292,z3,z4,z5,z93]),(0,[z1,z934,z3,z4,z5,z15]),(0,[z2,z3,z4,z5,z15,z935])]],
   [[(0,[z1,z2,z936,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z13]),(0,[z511,z2,z3,z4,z5,z22]),(0,[z183,z1,z3,z4,z5,z733]),(0,[z1,z2,z3,z4,z5,z937])],[(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z2,z3,z4,z5,z939]),(0,[z1,z2,z3,z4,z5,z940]),(0,[z51,z1,z325,z4,z5,z211]),(0,[z1,z105,z3,z4,z5,z733]),(0,[z1,z2,z3,z112,z41,z15]),(0,[z1,z2,z321,z4,z5,z60])],[(0,[z1,z2,z3,z4,z5,z941]),(0,[z1,z2,z3,z942,z5,z6]),(0,[z1,z2,z48,z3,z5,z15]),(0,[z54,z2,z3,z4,z49,z22]),(0,[z183,z1,z2,z3,z358,z5]),(0,[z943,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z944])],[(0,[z1,z138,z3,z4,z115,z6]),(0,[z1,z2,z3,z5,z22,z177])],[(0,[z1,z2,z3,z4,z945,z6]),(0,[z1,z2,z3,z4,z5,z946]),(0,[z604,z39,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z947]),(0,[z948,z2,z3,z4,z5,z6]),(0,[z1,z2,z16,z3,z41,z6])],[(0,[z1,z2,z167,z3,z68,z6]),(0,[z25,z1,z3,z4,z414,z26]),(0,[z1,z2,z14,z84,z5,z6]),(0,[z1,z2,z18,z3,z4,z737])],[(0,[z1,z2,z3,z4,z949,z6]),(0,[z1,z2,z224,z4,z115,z6]),(0,[z1,z2,z950,z4,z5,z6]),(0,[z1,z2,z951,z4,z5,z6]),(0,[z1,z2,z425,z3,z4,z5]),(0,[z587,z1,z2,z4,z5,z15]),(0,[z1,z2,z952,z4,z5,z22])],[(0,[z2,z3,z4,z5,z734,z6])]],
   [[(0,[z1,z2,z3,z4,z953,z6]),(0,[z1,z2,z167,z3,z5,z954]),(0,[z1,z2,z3,z274,z5,z15])],[(0,[z1,z48,z3,z4,z282,z6]),(0,[z1,z3,z12,z113,z5,z15]),(0,[z1,z2,z14,z84,z5,z222]),(0,[z1,z2,z3,z4,z5,z955])],[(0,[z1,z2,z3,z92,z335,z6])],[(0,[z1,z2,z3,z5,z956,z6]),(0,[z1,z957,z3,z4,z5,z6]),(0,[z1,z958,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z7,z724]),(0,[z959,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z831,z26,z6]),(0,[z34,z1,z2,z4,z763,z6]),(0,[z1,z2,z16,z3,z753,z6])],[(0,[z1,z3,z4,z5,z960,z6]),(0,[z1,z2,z3,z4,z5,z961])],[(0,[z402,z96,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z120,z15]),(0,[z205,z2,z3,z4,z163,z6]),(0,[z1,z2,z3,z4,z962,z5]),(0,[z1,z963,z2,z3,z4,z5])],[(0,[z47,z166,z2,z3,z5,z15]),(0,[z1,z2,z3,z4,z5,z964]),(0,[z965,z2,z3,z4,z5,z6])],[(0,[z21,z39,z3,z4,z5,z22]),(0,[z47,z1,z2,z3,z5,z63]),(0,[z1,z2,z3,z129,z5,z15]),(0,[z1,z2,z3,z4,z5,z966]),(0,[z1,z2,z3,z4,z5,z967]),(0,[z1,z2,z3,z4,z101,z689]),(0,[z1,z2,z16,z3,z41,z87]),(0,[z356,z2,z3,z4,z5,z327])]],
   [[(0,[z1,z2,z3,z4,z5,z968]),(0,[z1,z2,z477,z4,z5,z522]),(0,[z1,z2,z969,z4,z5,z6]),(0,[z71,z1,z2,z3,z5,z177]),(0,[z511,z2,z3,z4,z5,z15]),(0,[z1,z2,z4,z5,z32,z713])],[(0,[z1,z2,z3,z970,z5,z6]),(0,[z151,z2,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z971]),(0,[z551,z1,z3,z4,z5,z184])],[(0,[z411,z96,z3,z4,z5,z6]),(0,[z1,z2,z3,z972,z4,z5]),(0,[z1,z2,z193,z4,z5,z8]),(0,[z54,z2,z3,z4,z49,z15]),(0,[z1,z2,z973,z3,z4,z5]),(0,[z1,z2,z3,z5,z22,z661])],[(0,[z755,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z974])],[(0,[z151,z2,z89,z4,z5,z31]),(0,[z1,z2,z3,z5,z115,z15]),(0,[z1,z2,z3,z4,z5,z178]),(0,[z25,z1,z425,z3,z4,z26]),(0,[z1,z2,z4,z5,z452,z22]),(0,[z1,z2,z3,z4,z5,z975])],[(0,[z1,z2,z3,z976,z5,z6]),(0,[z1,z2,z3,z4,z5,z977]),(0,[z166,z1,z2,z3,z5,z15]),(0,[z1,z2,z3,z4,z5,z211]),(0,[z1,z2,z3,z978,z5,z6]),(0,[z1,z105,z3,z204,z5,z93]),(0,[z1,z2,z3,z4,z101,z678])],[(0,[z1,z48,z3,z4,z5,z22]),(0,[z54,z2,z167,z3,z49,z6]),(0,[z1,z2,z3,z709,z363,z5]),(0,[z1,z2,z3,z358,z5,z6])],[(0,[z2,z3,z707,z24,z5,z6]),(0,[z1,z538,z3,z4,z5,z22]),(0,[z1,z2,z3,z527,z5,z6]),(0,[z72,z2,z3,z4,z5,z372])]],
   [[(0,[z979,z1,z2,z3,z4,z6]),(0,[z39,z740,z3,z4,z5,z6]),(0,[z79,z1,z2,z4,z5,z516]),(0,[z1,z2,z3,z4,z5,z158]),(0,[z47,z1,z2,z3,z115,z15]),(0,[z269,z2,z3,z4,z5,z350]),(0,[z1,z2,z3,z4,z163,z350]),(0,[z1,z2,z3,z629,z5,z15])],[(0,[z1,z980,z3,z4,z5,z6]),(0,[z47,z17,z2,z3,z5,z6]),(0,[z1,z9,z3,z113,z5,z15]),(0,[z2,z3,z4,z5,z981,z6]),(0,[z1,z2,z3,z664,z5,z22]),(0,[z1,z2,z3,z5,z480,z15]),(0,[z1,z2,z3,z671,z5,z15])],[(0,[z1,z2,z3,z363,z5,z6]),(0,[z42,z1,z3,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z982])],[(0,[z1,z2,z3,z113,z5,z456])],[(0,[z1,z2,z3,z4,z5,z983]),(0,[z1,z2,z675,z84,z5,z6]),(0,[z47,z138,z3,z24,z5,z6]),(0,[z1,z2,z984,z4,z5,z6]),(0,[z54,z2,z3,z4,z851,z6]),(0,[z116,z2,z3,z5,z7,z177]),(0,[z125,z1,z2,z3,z5,z13])],[(0,[z96,z3,z4,z5,z190,z6]),(0,[z1,z2,z985,z4,z5,z6])],[],[(0,[z1,z2,z822,z3,z4,z5]),(0,[z1,z2,z986,z3,z4,z5]),(0,[z21,z39,z3,z4,z5,z15]),(0,[z54,z131,z3,z4,z49,z6]),(0,[z1,z373,z3,z4,z58,z6]),(0,[z1,z2,z18,z3,z4,z143]),(0,[z1,z2,z3,z113,z5,z15])]],
   [[(0,[z987,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z177,z15]),(0,[z1,z2,z3,z4,z988,z5]),(0,[z1,z2,z3,z592,z5,z15])],[(0,[z2,z3,z4,z707,z5,z6]),(0,[z989,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z990]),(0,[z183,z1,z3,z4,z553,z5])],[(0,[z1,z2,z3,z4,z5,z991]),(0,[z312,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z369,z5,z15]),(0,[z992,z1,z2,z3,z5,z6])],[(0,[z296,z96,z3,z4,z5,z6]),(0,[z1,z2,z3,z993,z5,z6]),(0,[z1,z2,z3,z4,z994,z6]),(0,[z367,z1,z2,z3,z5,z15]),(0,[z995,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z115,z22]),(0,[z1,z2,z4,z5,z452,z15]),(0,[z1,z2,z3,z996,z5,z6]),(0,[z1,z2,z997,z3,z4,z5])],[(0,[z1,z2,z3,z311,z5,z211]),(0,[z1,z2,z3,z4,z5,z998]),(0,[z1,z2,z3,z999,z5,z6])],[(0,[z1,z1000,z3,z4,z5,z6]),(0,[z1,z48,z3,z4,z5,z15]),(0,[z1,z1001,z3,z4,z5,z6]),(0,[z1,z2,z3,z375,z5,z15]),(0,[z51,z1,z325,z311,z5,z6]),(0,[z1,z2,z425,z3,z732,z5]),(0,[z886,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z115,z15]),(0,[z1,z538,z3,z4,z5,z15]),(0,[z1,z1002,z3,z4,z5,z6]),(0,[z1,z2,z3,z1003,z5,z6]),(0,[z1,z2,z29,z4,z101,z5]),(0,[z1,z2,z3,z4,z5,z1004]),(0,[z1,z2,z3,z5,z753,z6])]],
   [[(0,[z1,z2,z3,z4,z405,z6]),(0,[z1,z138,z224,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1005]),(0,[z269,z2,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z163,z22]),(0,[z1,z2,z425,z4,z5,z452]),(0,[z1,z2,z3,z4,z5,z1006])],[(0,[z1,z1007,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z1,z2,z1009,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z493,z3,z12,z5,z6]),(0,[z199,z1,z2,z4,z5,z127])],[(0,[z1,z2,z3,z1011,z5,z6]),(0,[z1,z2,z3,z1012,z5,z6]),(0,[z1,z2,z3,z112,z68,z227]),(0,[z1,z2,z3,z38,z5,z480])],[(0,[z1,z2,z3,z4,z5,z1013]),(0,[z1,z2,z3,z691,z68,z6]),(0,[z1,z2,z3,z1014,z5,z6]),(0,[z1,z2,z3,z218,z5,z15]),(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z358,z5,z349])],[(0,[z1,z2,z3,z4,z5,z326]),(0,[z1016,z1,z3,z4,z5,z6]),(0,[z1,z2,z4,z414,z5,z452]),(0,[z1,z2,z694,z4,z35,z6]),(0,[z1,z2,z3,z527,z5,z93]),(0,[z1,z2,z3,z38,z5,z6])],[(0,[z808,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z137]),(0,[z1,z2,z3,z488,z5,z15]),(0,[z1,z2,z3,z358,z5,z19])],[(0,[z166,z2,z3,z62,z5,z6]),(0,[z1,z1017,z3,z4,z5,z6]),(0,[z1,z1018,z3,z4,z5,z6]),(0,[z1,z2,z167,z393,z3,z5]),(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z3,z4,z5,z222]),(0,[z1,z2,z3,z112,z5,z15])],[(0,[z1,z2,z3,z4,z5,z1020]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z2,z811,z3,z4,z6]),(0,[z1,z2,z29,z4,z5,z22]),(0,[z269,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z92,z163,z6]),(0,[z51,z1,z325,z4,z335,z6]),(1,[z1,z754,z4,z5,z6]),(0,[z1,z2,z1022,z4,z5,z6]),(0,[z1,z511,z3,z4,z26,z6]),(0,[z2,z3,z4,z5,z6,z935])]],
   [[(0,[z47,z1,z48,z3,z5,z15]),(0,[z1,z1023,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z1,z433,z2,z3,z5,z22]),(0,[z34,z1,z2,z4,z247,z6]),(0,[z1,z2,z3,z112,z5,z807]),(0,[z1,z2,z3,z5,z807,z15])],[(0,[z1,z2,z3,z4,z5,z1025]),(0,[z765,z2,z3,z4,z5,z15])],[(0,[z1,z2,z3,z4,z5,z1026]),(0,[z54,z2,z3,z363,z49,z6]),(0,[z1,z2,z3,z1027,z5,z6]),(0,[z1,z2,z3,z241,z5,z15])],[(0,[z1,z2,z1028,z4,z5,z6]),(0,[z1,z2,z3,z92,z5,z1029]),(0,[z1,z147,z240,z4,z5,z15]),(0,[z1,z3,z12,z708,z5,z6]),(0,[z1,z2,z3,z4,z5,z1030])],[(0,[z1,z2,z3,z4,z5,z1031]),(0,[z1,z2,z3,z4,z115,z15]),(0,[z1,z2,z3,z1032,z5,z6]),(0,[z1,z2,z3,z5,z681,z15]),(1,[z1,z2,z4,z5,z713]),(0,[z1,z2,z3,z5,z687,z15])],[(0,[z1,z2,z3,z311,z5,z998]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z1,z2,z754,z4,z5,z6]),(0,[z250,z2,z3,z4,z5,z22])],[(0,[z1,z57,z3,z4,z58,z22]),(0,[z1,z2,z3,z285,z5,z15]),(0,[z1,z2,z3,z41,z228,z15]),(0,[z1,z439,z3,z4,z5,z401])],[(0,[z1,z2,z3,z4,z5,z1034]),(0,[z1,z2,z3,z4,z5,z231])]],
   [[(0,[z1,z2,z3,z4,z865,z5]),(0,[z1,z2,z444,z4,z5,z6]),(0,[z1,z2,z167,z3,z115,z6]),(1,[z2,z3,z4,z5,z724]),(0,[z269,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z163,z15])],[(0,[z1,z579,z2,z3,z5,z15]),(0,[z1,z138,z3,z4,z282,z6])],[(0,[z1,z2,z3,z4,z5,z1035]),(0,[z2,z3,z4,z851,z49,z6]),(0,[z1,z2,z3,z311,z5,z6]),(0,[z1,z2,z3,z4,z414,z5]),(1,[z1,z2,z3,z753,z6])],[(0,[z1,z2,z3,z1036,z5,z6]),(0,[z1,z2,z3,z4,z5,z1037]),(0,[z189,z2,z89,z4,z5,z6]),(0,[z189,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z11,z5,z15]),(0,[z787,z2,z3,z4,z5,z15])],[(0,[z1,z2,z3,z4,z5,z522]),(0,[z1,z2,z3,z107,z5,z22]),(0,[z1,z2,z3,z396,z5,z22]),(0,[z1038,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z788,z15])],[(0,[z69,z1,z3,z4,z26,z6]),(0,[z356,z2,z3,z4,z5,z7]),(0,[z1,z2,z1039,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1040]),(0,[z1,z1041,z3,z4,z5,z6])],[(0,[z2,z1042,z89,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1043]),(0,[z1,z449,z3,z113,z5,z15])],[(0,[z1,z2,z3,z4,z5,z1044]),(0,[z1,z2,z3,z4,z5,z128]),(0,[z1,z2,z167,z3,z5,z785]),(0,[z1,z2,z29,z4,z5,z15]),(0,[z42,z1,z3,z708,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z1045,z6]),(0,[z1,z2,z3,z236,z5,z15]),(0,[z25,z1,z3,z4,z831,z6]),(0,[z1,z2,z426,z4,z5,z8])],[(0,[z1,z2,z477,z4,z5,z6]),(0,[z47,z1,z2,z224,z5,z15]),(0,[z1,z2,z685,z3,z5,z22])],[(0,[z1,z2,z3,z4,z1046,z6]),(0,[z1,z2,z3,z4,z5,z1047]),(0,[z1,z2,z3,z399,z5,z15]),(0,[z1,z2,z3,z1048,z5,z6])],[(0,[z2,z1042,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1049]),(1,[z538,z3,z4,z49,z6]),(0,[z1,z2,z3,z4,z335,z6]),(1,[z1,z3,z708,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z529,z1,z3,z12,z5,z6])],[(0,[z1,z48,z3,z4,z5,z158]),(0,[z47,z1,z2,z477,z5,z15]),(0,[z132,z1,z2,z3,z5,z22]),(0,[z1,z2,z3,z92,z5,z1051]),(0,[z1052,z2,z3,z4,z5,z6]),(0,[z125,z1,z2,z3,z5,z480])],[(1,[z96,z3,z4,z190,z6]),(0,[z250,z2,z3,z4,z5,z15]),(0,[z1,z2,z4,z5,z713,z8])],[(0,[z1,z2,z3,z4,z1053,z6]),(0,[z1,z138,z3,z4,z5,z22]),(0,[z1,z2,z952,z4,z5,z6]),(0,[z166,z1,z2,z3,z5,z63]),(0,[z1,z2,z167,z3,z50,z5]),(0,[z587,z1,z2,z4,z414,z5]),(0,[z1,z57,z3,z4,z58,z15]),(0,[z1,z105,z2,z3,z358,z5])],[(0,[z1,z2,z3,z4,z5,z1054]),(0,[z1,z2,z3,z4,z753,z6])]],
   [[(0,[z1,z2,z4,z5,z1055,z6]),(0,[z1,z2,z3,z341,z5,z15]),(0,[z1,z2,z3,z527,z5,z401])],[(0,[z37,z1,z2,z3,z5,z15]),(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1,z2,z3,z708,z5,z6]),(0,[z1,z2,z3,z1057,z5,z6]),(0,[z1,z2,z3,z4,z101,z228])],[(0,[z1,z2,z3,z4,z1058,z6]),(0,[z1,z2,z3,z4,z1059,z6]),(0,[z55,z2,z3,z4,z40,z6]),(0,[z1,z2,z1060,z4,z5,z6]),(0,[z1,z3,z4,z5,z184,z733]),(0,[z1,z2,z3,z5,z813,z15])],[(0,[z1,z1061,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1062,z6]),(0,[z51,z1,z754,z4,z5,z6]),(0,[z25,z511,z3,z4,z26,z6]),(0,[z1,z2,z864,z4,z5,z6])],[(0,[z1,z2,z3,z1063,z4,z6]),(0,[z1,z2,z1064,z3,z5,z6]),(0,[z1,z9,z3,z113,z5,z22]),(0,[z1065,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1066])],[(0,[z47,z2,z3,z24,z5,z15]),(0,[z51,z1,z99,z4,z5,z6])],[(0,[z1,z2,z3,z4,z1067,z6]),(0,[z1,z2,z3,z28,z5,z813])],[(0,[z1,z2,z3,z499,z5,z15]),(0,[z411,z2,z3,z4,z49,z6]),(0,[z587,z1,z2,z4,z335,z6]),(0,[z1,z9,z3,z113,z5,z10]),(0,[z1,z2,z18,z3,z38,z95])]],
   [[(0,[z1,z2,z3,z119,z5,z15]),(0,[z1,z2,z3,z4,z5,z1068]),(0,[z1,z2,z3,z1069,z5,z6]),(0,[z125,z1,z2,z3,z5,z813])],[(0,[z1,z131,z3,z4,z5,z15]),(0,[z1,z2,z3,z1070,z5,z6]),(0,[z1071,z2,z3,z4,z5,z6]),(0,[z1,z2,z873,z3,z4,z6])],[(0,[z1,z2,z3,z4,z115,z158]),(0,[z1,z2,z1072,z4,z5,z6]),(0,[z1,z2,z3,z1073,z5,z6]),(0,[z1,z2,z3,z4,z834,z15]),(0,[z1,z2,z3,z4,z5,z737])],[(0,[z1,z2,z3,z4,z1074,z6]),(0,[z269,z2,z3,z4,z5,z211]),(0,[z1,z2,z3,z311,z335,z6]),(0,[z1,z2,z3,z4,z163,z211]),(0,[z1,z2,z3,z4,z5,z1075]),(0,[z1,z3,z4,z5,z837,z15])],[(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z2,z3,z4,z5,z1077]),(0,[z132,z1,z2,z3,z5,z15]),(0,[z1078,z2,z3,z4,z5,z6]),(0,[z587,z1,z2,z4,z35,z6]),(0,[z1,z2,z3,z4,z5,z1079])],[(0,[z1,z2,z3,z1080,z5,z6]),(0,[z125,z1,z48,z3,z5,z6]),(0,[z1,z2,z3,z1081,z5,z6]),(0,[z1,z2,z3,z113,z5,z10])],[(0,[z1,z2,z3,z4,z190,z22]),(0,[z1,z2,z3,z4,z5,z1082]),(0,[z1,z138,z3,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z1083]),(0,[z1,z2,z3,z5,z177,z8]),(0,[z1,z2,z3,z1084,z5,z6]),(0,[z1085,z2,z3,z4,z5,z6])],[(0,[z1,z2,z1086,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z55,z2,z3,z4,z851,z6]),(0,[z1088,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1089])]],
   [[(0,[z1,z2,z3,z1090,z5,z6]),(0,[z54,z2,z3,z4,z50,z49]),(0,[z116,z1,z2,z3,z358,z5]),(0,[z1,z2,z3,z4,z5,z1091]),(0,[z1,z2,z3,z4,z5,z1092])],[(0,[z1,z2,z224,z4,z5,z15]),(0,[z72,z2,z3,z4,z5,z33]),(0,[z51,z1,z325,z4,z5,z6]),(0,[z1093,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z204,z5,z22])],[(0,[z21,z2,z3,z4,z190,z6]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z1,z2,z3,z4,z849,z15])],[(0,[z1,z2,z3,z4,z5,z1095]),(0,[z1,z2,z3,z5,z158,z15]),(0,[z1,z2,z3,z4,z889,z6]),(0,[z1096,z1,z3,z4,z5,z6])],[(0,[z1,z475,z2,z3,z5,z15]),(0,[z1,z2,z3,z476,z5,z15]),(0,[z1,z2,z102,z3,z5,z15]),(0,[z205,z2,z3,z4,z5,z15]),(0,[z1,z2,z3,z5,z349,z15]),(0,[z1,z2,z339,z3,z4,z95]),(0,[z1,z2,z3,z1097,z5,z6])],[(0,[z166,z2,z3,z5,z334,z15])],[(0,[z1,z2,z1098,z3,z5,z6]),(0,[z1099,z1,z2,z3,z5,z6])],[(0,[z2,z96,z3,z4,z190,z6]),(0,[z1,z48,z3,z5,z6,z15]),(0,[z1,z2,z3,z1100,z5,z6]),(0,[z1,z2,z3,z4,z5,z1101])]],
   [[(0,[z79,z1,z2,z4,z5,z100])],[(0,[z706,z96,z3,z4,z5,z6]),(0,[z1102,z2,z3,z4,z5,z6])],[(0,[z21,z740,z3,z4,z5,z6]),(0,[z1,z1103,z3,z4,z5,z6]),(0,[z47,z2,z224,z24,z5,z6]),(0,[z1,z2,z3,z614,z5,z15])],[(0,[z1,z2,z3,z4,z5,z1104]),(0,[z1,z2,z3,z4,z5,z1105])],[(0,[z1,z3,z708,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1106]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z4,z5,z6,z1108]),(0,[z1109,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z190,z15]),(0,[z1,z2,z3,z1110,z4,z5]),(0,[z1,z147,z240,z4,z5,z22]),(0,[z1,z3,z4,z58,z831,z6]),(0,[z1,z2,z3,z4,z5,z1111]),(0,[z1,z2,z3,z483,z5,z15]),(0,[z1,z2,z338,z4,z5,z270]),(0,[z261,z1,z2,z4,z5,z100]),(0,[z1,z2,z3,z4,z238,z19])],[(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z2,z3,z4,z1113,z5])]],
   [[(0,[z1,z2,z3,z1114,z5,z6]),(0,[z1,z2,z3,z4,z5,z1115]),(0,[z1,z2,z1116,z3,z5,z6]),(0,[z1,z2,z3,z4,z1117,z5]),(0,[z1,z48,z3,z4,z5,z522]),(0,[z1,z2,z3,z4,z5,z1118]),(0,[z1,z2,z3,z112,z68,z22]),(0,[z1,z2,z3,z4,z6,z737])],[(0,[z1,z2,z1119,z4,z5,z6]),(0,[z1,z1120,z3,z4,z5,z6]),(0,[z71,z2,z444,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1,z2,z3,z204,z5,z15])],[(0,[z1,z2,z3,z4,z282,z15]),(0,[z1,z2,z3,z207,z5,z15]),(1,[z2,z3,z4,z851,z6]),(0,[z1,z2,z29,z4,z5,z33]),(0,[z1,z2,z3,z4,z101,z545]),(1,[z1,z2,z3,z5,z813])],[(0,[z1,z2,z89,z4,z5,z31]),(0,[z1,z2,z16,z3,z115,z6]),(0,[z1,z2,z3,z4,z5,z480]),(0,[z1,z449,z3,z4,z5,z615])],[(0,[z1,z2,z1123,z4,z5,z6]),(0,[z1,z1124,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1029]),(0,[z1,z2,z3,z4,z1125,z5]),(0,[z1,z2,z3,z4,z5,z1126])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z48,z477,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1127]),(0,[z1,z2,z3,z5,z22,z472])],[(0,[z1,z2,z3,z691,z5,z15]),(0,[z1,z2,z3,z5,z41,z87])],[(0,[z1,z2,z3,z5,z6,z1128]),(0,[z1,z2,z3,z204,z5,z13]),(0,[z1,z2,z3,z295,z5,z15])]],
   [[(0,[z1,z2,z3,z4,z5,z31]),(0,[z71,z2,z3,z4,z5,z88])],[(0,[z1,z2,z3,z4,z5,z1129]),(0,[z1,z2,z3,z4,z5,z1130])],[(0,[z151,z2,z1042,z4,z5,z6]),(0,[z132,z1,z2,z3,z5,z158]),(0,[z72,z166,z2,z3,z5,z15]),(0,[z1,z2,z3,z1131,z5,z6]),(0,[z51,z205,z325,z4,z5,z6]),(0,[z1,z2,z144,z3,z5,z15]),(0,[z1,z2,z3,z527,z5,z184]),(0,[z1,z934,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z52]),(0,[z1,z2,z3,z358,z5,z32])],[(0,[z47,z2,z3,z24,z282,z6]),(0,[z71,z1,z2,z3,z358,z5]),(0,[z1,z2,z3,z4,z5,z1132])],[(0,[z1,z2,z3,z4,z1133,z5]),(0,[z1,z138,z3,z4,z5,z158])],[(0,[z2,z3,z4,z40,z851,z6]),(0,[z706,z1,z2,z3,z5,z15]),(0,[z1,z2,z890,z4,z5,z15])],[(0,[z1,z2,z3,z4,z115,z522]),(0,[z1,z147,z4,z5,z457,z6]),(0,[z1,z9,z3,z113,z5,z178])],[(0,[z1,z2,z3,z4,z5,z1134]),(0,[z1,z2,z3,z4,z5,z1135]),(0,[z1,z2,z917,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z954]),(0,[z509,z2,z3,z4,z5,z7]),(0,[z1,z2,z3,z4,z5,z813])]],
   [[(0,[z1,z2,z3,z1136,z5,z6]),(0,[z269,z2,z3,z311,z5,z6]),(0,[z1,z2,z3,z311,z163,z6]),(0,[z1,z2,z3,z4,z5,z87]),(0,[z1,z2,z3,z112,z68,z15])],[(0,[z402,z96,z3,z4,z190,z6]),(0,[z587,z1,z2,z4,z5,z6]),(0,[z1,z3,z754,z4,z5,z6])],[(0,[z355,z39,z3,z4,z5,z6]),(0,[z116,z2,z3,z4,z5,z334]),(0,[z1,z2,z3,z12,z5,z830]),(0,[z1,z2,z3,z254,z5,z15]),(0,[z1,z2,z3,z5,z22,z15]),(0,[z1,z2,z301,z3,z5,z22]),(0,[z1,z2,z3,z4,z737,z95])],[(0,[z1,z2,z3,z4,z5,z1137]),(0,[z1,z2,z477,z4,z115,z6]),(0,[z1,z2,z167,z3,z5,z22]),(0,[z1,z2,z3,z432,z5,z15])],[(0,[z1,z2,z3,z4,z5,z1138]),(0,[z1,z2,z3,z5,z860,z15]),(0,[z1,z147,z754,z4,z5,z6]),(0,[z1,z105,z3,z4,z5,z192]),(0,[z1,z2,z3,z4,z5,z1139])],[(0,[z1,z39,z3,z4,z190,z6]),(1,[z740,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1051]),(0,[z1140,z2,z3,z4,z5,z6]),(1,[z1,z3,z4,z831,z6]),(0,[z1,z2,z3,z4,z1141,z5])],[(0,[z381,z1,z2,z3,z5,z15]),(0,[z1,z2,z3,z92,z5,z15]),(0,[z1142,z2,z3,z4,z5,z6])],[(0,[z1,z1143,z3,z4,z5,z6]),(0,[z1,z2,z224,z4,z282,z6]),(0,[z205,z2,z3,z4,z5,z350]),(0,[z25,z1,z3,z4,z26,z15]),(0,[z1,z1144,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1145])]],
   [[(0,[z1,z2,z3,z4,z5,z1146]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1,z2,z3,z4,z5,z1148]),(0,[z125,z1,z2,z3,z115,z6]),(0,[z47,z2,z3,z24,z5,z22]),(0,[z1,z897,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z273,z15])],[(0,[z269,z2,z3,z4,z335,z6]),(0,[z511,z57,z3,z4,z5,z6]),(0,[z1,z2,z929,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z135]),(0,[z1,z2,z16,z3,z41,z22])],[(0,[z1,z2,z3,z1149,z5,z6]),(0,[z410,z1,z2,z3,z5,z15]),(0,[z1,z2,z444,z4,z5,z15]),(0,[z1,z2,z3,z4,z5,z1150]),(0,[z78,z1,z2,z134,z5,z15]),(0,[z1,z2,z4,z5,z713,z6]),(0,[z1,z2,z339,z3,z41,z15]),(0,[z400,z1,z3,z4,z5,z192])],[(0,[z1,z2,z3,z4,z1151,z6]),(0,[z511,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z1152,z6]),(0,[z1,z2,z16,z3,z41,z248])],[(0,[z1,z131,z3,z4,z5,z22]),(0,[z1,z2,z3,z4,z5,z1153])],[(0,[z54,z2,z3,z4,z49,z6]),(0,[z1,z2,z3,z4,z5,z1154]),(0,[z1,z2,z3,z5,z15,z81])],[(0,[z1,z2,z1042,z4,z5,z6]),(0,[z1,z2,z18,z29,z4,z5]),(0,[z1,z2,z3,z5,z284,z15]),(0,[z1,z9,z3,z708,z5,z6]),(0,[z1,z2,z3,z4,z5,z1155])],[(0,[z1,z2,z3,z1156,z5,z6]),(0,[z1,z2,z3,z4,z5,z1157]),(0,[z1,z2,z3,z4,z5,z1158]),(0,[z1,z2,z429,z4,z5,z8])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 525) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 525).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1058).take 149) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1207)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [525, 533, 149] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 104).take 94).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 198).take 58).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [104, 94, 58] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_37643

theorem PEqualNP.Outside.L_meta_37643 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276808704) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37643.solve