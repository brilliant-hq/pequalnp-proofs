import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38243

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

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 64 := ((x >>> 64) ^^^ x).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)
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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 64+i.val < 128 := by omega
  have hi' : i.val < 128 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 64) :
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
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
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
  · change reachable av (BitVec.allOnes 128 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 128)
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

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 128) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#128)[k.val] = false; simp
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
  Nat.testBit (4008241856 * 2 ^ 32 + 4007715008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 128,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 128) :
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
  [(0x09023716f0c38e3c#64 ++ 0xaf467f3ff1c79e7c#64 : BitVec 128),
   (0x00188b4e14d8a285#64 ++ 0xffb98fce3ef8e38f#64 : BitVec 128),
   (0x02c150b02b00555a#64 ++ 0xfbc1f0f03f00ffff#64 : BitVec 128),
   (0x10ec00eb436d03e0#64 ++ 0x3dfe00ffc3ff03f0#64 : BitVec 128),
   (0x24f7ed0003b6f800#64 ++ 0x3effff0003fffc00#64 : BitVec 128),
   (0x47fffefdbc000000#64 ++ 0x37fffffffc000000#64 : BitVec 128)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [7, 3]⟩, ⟨.and, [0, 8]⟩, ⟨.or, [9, 1]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [11, 2]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [12, 13]⟩, ⟨.and, [10, 14]⟩], 15⟩

def mkw (a b : BitVec 64) : W := a ++ b

def z0 : W := mkw 0x0000000000000000 0xfb8180c03e00e38f

def z1 : W := mkw 0x00188b4e14d8a285 0xffb98fce3ef8e38f

def z2 : W := mkw 0x02c150b02b00555a 0xfbc1f0f03f00ffff

def z3 : W := mkw 0x09023716f0c38e3c 0xaf467f3ff1c79e7c

def z4 : W := mkw 0x10ec00eb436d03e0 0x047e003fc1ff0070

def z5 : W := mkw 0x24f7ed0003b6f800 0x3effff0003fffc00

def z6 : W := mkw 0x47fffefdbc000000 0x37fffffffc000000

def z7 : W := mkw 0x0800000040030c38 0x0000000001071c70

def z8 : W := mkw 0x10ec00eb436d03e0 0x3dfe00ffc3ff03f0

def z9 : W := mkw 0x24ffef4c17b6f800 0x3fffffce3ffffc00

def z10 : W := mkw 0x020010b02800055a 0xeb4070f03d009fff

def z11 : W := mkw 0x00188a4c14182081 0x77b98fce3e386183

def z12 : W := mkw 0x09022400c0030820 0x00060001c0070000

def z13 : W := mkw 0x091aaf4ed4dbaaa5 0x043e0f0fc0ff0000

def z14 : W := mkw 0x02c140a008000000 0x108180c00c000000

def z15 : W := mkw 0x2436ad0000b6a800 0x043e0f0000ff0000

def z16 : W := mkw 0x34ffedeb43fffbe0 0x3fffffffc3fffff0

def z17 : W := mkw 0x001aaf4e14daaa85 0xffffffce3fffff8f

def z18 : W := mkw 0x10e400a143250160 0x00460031c1070070

def z19 : W := mkw 0x10fc8bef57fda3e5 0xffff8fffffffe3ff

def z20 : W := mkw 0x56fdc8eb4f6d03e0 0x3dff80ffcfff03f0

def z21 : W := mkw 0x02d9dbfe3fd8f7df 0xfff9fffe3ff8ffff

def z22 : W := mkw 0x0000010000808000 0x2e000f0000c08000

def z23 : W := mkw 0x2df7ff16f3f7fe3c 0xbfffff3ff3fffe7c

def z24 : W := mkw 0x02c150b02b00555a 0x0040703001001c70

def z25 : W := mkw 0x453eae4d94000000 0x37bf8fcffc000000

def z26 : W := mkw 0x2437ed0000b6f800 0x063fff0000fffc00

def z27 : W := mkw 0x12ed50fb6b6d57fa 0xfffff0ffffffffff

def z28 : W := mkw 0x26f7fdb02bb6fd5a 0xfffffff03fffffff

def z29 : W := mkw 0x453eae4d94000000 0x043e0f0fc0000000

def z30 : W := mkw 0x4ffffffffcc38e3c 0xbffffffffdc79e7c

def z31 : W := mkw 0x2800010243f7fe3c 0x8800000003fffe7c

def z32 : W := mkw 0x343ead4b40ffaaa0 0x043e0f0fc0ff0000

def z33 : W := mkw 0x091abf5ef4dbaebd 0xffffffffffffffff

def z34 : W := mkw 0x0002270610c28a04 0xaf467f0e31c79e0c

def z35 : W := mkw 0x43189afdbc000000 0x37b98ffffc000000

def z36 : W := mkw 0x09023716f0dbaebd 0xef467f3ff3ffffff

def z37 : W := mkw 0x0000000240410220 0x0406000fc0c70000

def z38 : W := mkw 0x47fffefdbf00555a 0xffffffffff00ffff

def z39 : W := mkw 0x57fffeffff6d57fa 0xffffffffffffffff

def z40 : W := mkw 0x0008004a00480280 0x3db800ce02f80380

def z41 : W := mkw 0x0008024e14480285 0xc10000ce3c00038f

def z42 : W := mkw 0x01023614b0000000 0x27467f3ff0000000

def z43 : W := mkw 0x0000101020000418 0xab40703031009e7c

def z44 : W := mkw 0x47fffefdbc000418 0xbffffffffd009e7c

def z45 : W := mkw 0x0219db5e3cd8f69f 0xffb9ffce3ef8ff8f

def z46 : W := mkw 0x00e4000003240000 0x3cfe000003ff0000

def z47 : W := mkw 0x0800010240c38a24 0x0000000000c70000

def z48 : W := mkw 0x0800010240c38e3c 0x8800000001c79e7c

def z49 : W := mkw 0x09023714b0828c1c 0xae467f0031c79c0c

def z50 : W := mkw 0x00fc8bef14d8a285 0xffff8ffffef8e38f

def z51 : W := mkw 0x67fffffdbfb6f800 0x3ffffffffffffc00

def z52 : W := mkw 0x55feaeefd76d03e0 0x3dfe0fffc3ff03f0

def z53 : W := mkw 0x0000000240410220 0x2d46003fc1c70270

def z54 : W := mkw 0x2413ed000092f800 0x0201ff000000fc00

def z55 : W := mkw 0x12c150b26b6d57fa 0xfbc1f0f03fffffff

def z56 : W := mkw 0x00fc8aed14000000 0x37ff8ffffc000000

def z57 : W := mkw 0x00188b4e14d8a285 0xaf380f0e30f8820c

def z58 : W := mkw 0x46fdc8e90f005142 0x50b980c00e006183

def z59 : W := mkw 0x0000000000000418 0x8800000001009e7c

def z60 : W := mkw 0x10e400a103240140 0x0000000000000000

def z61 : W := mkw 0x00c000a243410360 0x3dc600ffc3c703f0

def z62 : W := mkw 0x00c000a003000140 0x39c000f0030003f0

def z63 : W := mkw 0x19ee37fff3ef8ffc 0xbffe7ffff3ff9ffc

def z64 : W := mkw 0x46fdc8e90c000000 0x10b980c00c000000

def z65 : W := mkw 0x09022706d0c38a24 0x04060f0fc0c70000

def z66 : W := mkw 0x47e774b1a8000000 0x00467031c0000000

def z67 : W := mkw 0x01001214b0000000 0x0100003ff0000000

def z68 : W := mkw 0x09001216f041063c 0xad46003ff1c7027c

def z69 : W := mkw 0x0000030610c08204 0xaf000f0e30c0820c

def z70 : W := mkw 0x02c140a00b005142 0x508180c00e006183

def z71 : W := mkw 0x26f7eda00bb6f942 0x7effffc00ffffd83

def z72 : W := mkw 0x01023614b0000418 0xaf467f3ff1009e7c

def z73 : W := mkw 0x420800e90c000000 0x000000c00c000000

def z74 : W := mkw 0x020010b02b00555a 0xc90000f03f00ffff

def z75 : W := mkw 0x24ffef4e17fefa85 0xffffffce3fffff8f

def z76 : W := mkw 0x24e7640003265800 0x0046700001071c00

def z77 : W := mkw 0x020150102800541a 0xc201f0003c00fc0f

def z78 : W := mkw 0x00188a4c14000000 0x37b98fce3c000000

def z79 : W := mkw 0x47ffffffbcd8a285 0xfffffffffef8e38f

def z80 : W := mkw 0x26e774b02b265d5a 0x0046703001071c70

def z81 : W := mkw 0x10c800eb434903e0 0x39c000ffc30003f0

def z82 : W := mkw 0x001889480498a081 0x7eb98fc00ef8e183

def z83 : W := mkw 0x00188b4e14d8a285 0x04380f0e00f80000

def z84 : W := mkw 0x0000101020000418 0x0040703001001c70

def z85 : W := mkw 0x47037410a8000000 0x0000700000000000

def z86 : W := mkw 0x19ee27efd3ef8be4 0x3dfe0fffc3ff03f0

def z87 : W := mkw 0x00188a4c14000000 0x04380f0e00000000

def z88 : W := mkw 0x24ffed4a03fefa80 0x3fffffce03ffff80

def z89 : W := mkw 0x00c1400003005000 0x3ac1f0000300fc00

def z90 : W := mkw 0x473ebefdbc000000 0x053e0ffffc000000

def z91 : W := mkw 0x000000000300555a 0xc80000000300ffff

def z92 : W := mkw 0x4713fe14bc000000 0x0201ff003c000000

def z93 : W := mkw 0x3000010243fffbe0 0x0800000003fffff0

def z94 : W := mkw 0x001089000090a000 0x3eb98f0002f8e000

def z95 : W := mkw 0x0902270490828804 0x00000f0000000000

def z96 : W := mkw 0x00188b4e14d8a285 0xc5380fce3cf8038f

def z97 : W := mkw 0x47e774b1ab00555a 0x00467031c1001c70

def z98 : W := mkw 0x04f7ed000090a000 0x3effff0002f8e000

def z99 : W := mkw 0x19e634b1e3270d78 0x00467031c1071c70

def z100 : W := mkw 0x04f7ec0003240000 0x3effff0003ff0000

def z101 : W := mkw 0x0000030410808004 0x82000f003000800c

def z102 : W := mkw 0x0908125ef44906bd 0xc10000fffc0003ff

def z103 : W := mkw 0x10ec00eb436d03e0 0x014600ffc10703f0

def z104 : W := mkw 0x102c004b406d02a0 0x2d7e003fc1ff0270

def z105 : W := mkw 0x10000002436d57fa 0xc800000003ffffff

def z106 : W := mkw 0x02c150b028000000 0x33c1f0f03c000000

def z107 : W := mkw 0x011abf5eb4d8a285 0xfffffffffef8e38f

def z108 : W := mkw 0x24f7ec0003347000 0x36ffff0002386000

def z109 : W := mkw 0x4fe777b7f8c38e3c 0xaf467f3ff1c79e7c

def z110 : W := mkw 0x10ec00e9032c01c0 0x10b800c002380180

def z111 : W := mkw 0x100800e9000801c0 0x000000c000000180

def z112 : W := mkw 0x0000000200480280 0x0800000002f80380

def z113 : W := mkw 0x47fffefdbf240000 0x3fffffffffff0000

def z114 : W := mkw 0x34e764a143275960 0x00467031c1071c70

def z115 : W := mkw 0x09ee37fff0c38e3c 0xbffe7ffff1c79e7c

def z116 : W := mkw 0x000000000300555a 0x0000000001001c70

def z117 : W := mkw 0x0002250000828800 0x2e467f0001c79c00

def z118 : W := mkw 0x66ffede90fb6f800 0x3effffc00ffffc00

def z119 : W := mkw 0x47fffefdbc000000 0x047e7f3fc0000000

def z120 : W := mkw 0x0102260490000000 0x04060f0fc0000000

def z121 : W := mkw 0x020150102800541a 0x0000700000001c00

def z122 : W := mkw 0x00c365000382d800 0x3ec7ff0003c7fc00

def z123 : W := mkw 0x0008004a00480280 0xffb980ce3ef8e38f

def z124 : W := mkw 0x102c00eb406d03e0 0x053e00ffc0ff03f0

def z125 : W := mkw 0x020150102b00555a 0xca01f0003f00ffff

def z126 : W := mkw 0x00e400a100000000 0x00460031c0000000

def z127 : W := mkw 0x4713ff14bc90a005 0xc201ff003c00e00f

def z128 : W := mkw 0x04ffece900000000 0x37ffffffc0000000

def z129 : W := mkw 0x0000010203d8f7df 0xc800000003f8ffff

def z130 : W := mkw 0x0018884804182081 0x50b980c00e386183

def z131 : W := mkw 0x47e776b5b8000000 0x27467f3ff0000000

def z132 : W := mkw 0x4d3ebf5ff4c38e3c 0xaf7e7f3ff1c79e7c

def z133 : W := mkw 0x24f5c80003347000 0x10b9800002386000

def z134 : W := mkw 0x09023716f0c38e3c 0x04467f3fc1c71c70

def z135 : W := mkw 0x2436ad0000b6a800 0x3ebf8f0002ffe000

def z136 : W := mkw 0x0201400008005002 0x400180000c006003

def z137 : W := mkw 0x103c8b4f54fda2a5 0x043e0f0fc0ff0000

def z138 : W := mkw 0x091aaf4ed4dbaaa5 0xffbf8fcffeffe38f

def z139 : W := mkw 0x10000000032c01c0 0x0000000002380180

def z140 : W := mkw 0x05f7fe14b0000000 0x37ffff3ff0000000

def z141 : W := mkw 0x000800e900000000 0x010000ffc0000000

def z142 : W := mkw 0x10fc8bef57fda3e5 0x3dfe0fffc3ff03f0

def z143 : W := mkw 0x09023410e0030c38 0x00467031c1071c70

def z144 : W := mkw 0x102c004b406d02a0 0x043e000fc0ff0000

def z145 : W := mkw 0x00188b4c1498a085 0xd2b98fc03e38e18f

def z146 : W := mkw 0x4713fe14bc00541a 0xc201ff003c00fc0f

def z147 : W := mkw 0x09023714f0838c3c 0x82467f31f1079c7c

def z148 : W := mkw 0x10ec10fb636d07f8 0xbffe70fff3ff9ffc

def z149 : W := mkw 0x09c237b6f3c38f7c 0xbfc67ffff3c79ffc

def z150 : W := mkw 0x09023714b0828c1c 0x82007f0030009c0c

def z151 : W := mkw 0x0bc377b6fbc3df7e 0xffc7ffffffc7ffff

def z152 : W := mkw 0x45feaeed94000000 0x35fe0fffc0000000

def z153 : W := mkw 0x02c150b02b000140 0x3bc1f0f03f0003f0

def z154 : W := mkw 0x46fdcbef1cd8a285 0xffb98fce3ef8e38f

def z155 : W := mkw 0x4108024d94000000 0x0000000fc0000000

def z156 : W := mkw 0x10ec00eb436d57fa 0xfdfe00ffc3ffffff

def z157 : W := mkw 0x471bfefdbc000000 0x0301fffffc000000

def z158 : W := mkw 0x09023716f0c38e3c 0xffc7ffffffc7ffff

def z159 : W := mkw 0x000001000090a005 0xc00000000000e00f

def z160 : W := mkw 0x65ffef4d97b6f800 0x3effff0fc3fffc00

def z161 : W := mkw 0x02c140a00b00555a 0xd88180c00f00ffff

def z162 : W := mkw 0x57e774b1eb250160 0x00467031c1070070

def z163 : W := mkw 0x02c151b22bd8f7df 0xfbc1f0f03ff8ffff

def z164 : W := mkw 0x120810fb684907fa 0xc10000fffc0003ff

def z165 : W := mkw 0x00c010b023000558 0xbbc070f033009ffc

def z166 : W := mkw 0x100800eb404903e0 0x010000ffc00003f0

def z167 : W := mkw 0x02c150b028000000 0x0040703000000000

def z168 : W := mkw 0x430812ffbc480285 0xc10000fffc00038f

def z169 : W := mkw 0x47fffefdbc00541a 0xf7fffffffc00fc0f

def z170 : W := mkw 0x46fdc8e90c000000 0x35ff80ffcc000000

def z171 : W := mkw 0x11ee36fff36d03e0 0x3ffe7ffff3ff03f0

def z172 : W := mkw 0x04f7ec0000000000 0x36ffff0000000000

def z173 : W := mkw 0x430812fdbc000000 0x010000fffc000000

def z174 : W := mkw 0x02c150b02800541a 0xf3c1f0f03c00fc0f

def z175 : W := mkw 0x20188b4e17fefa85 0xffb98fce3fffff8f

def z176 : W := mkw 0x0211db143c90f41f 0xc201ff003c00fc0f

def z177 : W := mkw 0x00c000a003000140 0xfbc180f03f00e3ff

def z178 : W := mkw 0x00f4890003b4a000 0x3eff8f0003ffe000

def z179 : W := mkw 0x00108b041490a005 0xc2018f003c00e00f

def z180 : W := mkw 0x0912bf16f0d3ae3c 0xbfffff3ff3fffe7c

def z181 : W := mkw 0x4fffffffffc3df7e 0xffffffffffc7ffff

def z182 : W := mkw 0x00ec00e900000000 0x35fe00ffc0000000

def z183 : W := mkw 0x020150b02800555a 0xc301f0f03c00ffff

def z184 : W := mkw 0x091abf5ef4c38e3c 0xbffffffffdc79e7c

def z185 : W := mkw 0x12c950fb6b4957fa 0xfbc1f0ffff00ffff

def z186 : W := mkw 0x57fffeffff6d03e0 0x3fffffffffff03f0

def z187 : W := mkw 0x47d3feb4bf00555a 0xfbc1fff03f00ffff

def z188 : W := mkw 0x4f13ff16fcc38e3c 0xaf47ff3ffdc79e7c

def z189 : W := mkw 0x02c140a00b005142 0x0000000000000000

def z190 : W := mkw 0x0000101020000000 0x2340703030000000

def z191 : W := mkw 0x0008034e14c88285 0xef000fce3cc0838f

def z192 : W := mkw 0x2413ef041492f805 0xc201ff003c00fc0f

def z193 : W := mkw 0x12ed50f92b2c55da 0xfbf9f0f03f38ffff

def z194 : W := mkw 0x241bef4e14dafa85 0xffb9ffce3ef8ff8f

def z195 : W := mkw 0x020812fe3c4807df 0xc10000fe3c0003ff

def z196 : W := mkw 0x67fffffdbcb6a800 0x37fffffffcff0000

def z197 : W := mkw 0x4f13ff14bc828c1c 0x8201ff003c009c0c

def z198 : W := mkw 0x00188b4e14c08204 0xbfb98fce3cc0820c

def z199 : W := mkw 0x0000010200d8a285 0xc800000002f8e38f

def z200 : W := mkw 0x09023716f0c38e3c 0x86067f0ff0c79c0c

def z201 : W := mkw 0x0ac151b26bc3df7e 0xfbc1f0f03fc7ffff

def z202 : W := mkw 0x10ec00eb436d03e0 0x14be00cfc2ff0180

def z203 : W := mkw 0x47fffefdbc00055a 0xf7fffffffc0003ff

def z204 : W := mkw 0x24f7ed0003b6f800 0x12b9ff000238fc00

def z205 : W := mkw 0x0000000240410220 0x0800000001c70270

def z206 : W := mkw 0x020010b02800055a 0xc10000f03c0003ff

def z207 : W := mkw 0x00188b4e54d9a2a5 0xffff8fffffffe3ff

def z208 : W := mkw 0x430a36fdbc000000 0x27467ffffc000000

def z209 : W := mkw 0x653eaf4d94b6a800 0x043e0f0fc0ff0000

def z210 : W := mkw 0x09023510e0838c38 0x2e467f31c1c79c70

def z211 : W := mkw 0x453ebe5db4000000 0x277e7f3ff0000000

def z212 : W := mkw 0x0000000000000000 0x3cb8000002f80000

def z213 : W := mkw 0x001089000090a000 0x02018f000000e000

def z214 : W := mkw 0x03c376b4bb00555a 0xffc7ffffff00ffff

def z215 : W := mkw 0x24f5c90003b6f800 0x18b9800003fffc00

def z216 : W := mkw 0x10000002436d03e0 0x0800000003ff03f0

def z217 : W := mkw 0x2000010003b6f800 0x0800000003fffc00

def z218 : W := mkw 0x29023716f3f7fe3c 0xaf467f3ff3fffe7c

def z219 : W := mkw 0x53ec12ffff6d03e0 0x3dfe00ffffff03f0

def z220 : W := mkw 0x0000020410000000 0x27000f0e30000000

def z221 : W := mkw 0x10fc88e9073c21c1 0x50b980c00e386183

def z222 : W := mkw 0x102c004b436d03e0 0x0c3e000fc3ff03f0

def z223 : W := mkw 0x0008004a00480280 0x0438000e00f80000

def z224 : W := mkw 0x0bc377b6fbc3df7e 0xaf467f3ff1c79e7c

def z225 : W := mkw 0x102c004b406d02a0 0x3dbe00cfc2ff0380

def z226 : W := mkw 0x02c150b02b00555a 0xc14070f03d001fff

def z227 : W := mkw 0x01023716b0c08204 0xaf467f3ff0c0820c

def z228 : W := mkw 0x45ffee4d94000000 0x36ffff0fc0000000

def z229 : W := mkw 0x00108b0614d0a205 0xef018f0e3cc0e20f

def z230 : W := mkw 0x47fffffdbc828800 0x3ffffffffdc79c00

def z231 : W := mkw 0x1000010243fda3e5 0xc800000003ffe3ff

def z232 : W := mkw 0x1bef77fffbefdffe 0xffffffffffffffff

def z233 : W := mkw 0x0000000003005142 0x4000000002006183

def z234 : W := mkw 0x2de77410e3275c38 0x00467031c1071c70

def z235 : W := mkw 0x10000002404903e0 0x00000000000003f0

def z236 : W := mkw 0x09023716f0c38e3c 0x8a007f0031c79e7c

def z237 : W := mkw 0x000000000300555a 0xfb8180c03f00ffff

def z238 : W := mkw 0x0002250000828800 0x02007f0000009c00

def z239 : W := mkw 0x0000030610d8a285 0xef000f0e32f8e38f

def z240 : W := mkw 0x25f7ff14b3b6f800 0x3fffff3ff3fffc00

def z241 : W := mkw 0x0000030610c08204 0x04000f0e00c00000

def z242 : W := mkw 0x47ef76fdbc000000 0x014670fffc000000

def z243 : W := mkw 0x0b037714b882dc1e 0xc201ff003c00fc0f

def z244 : W := mkw 0x2412ad000092a800 0x00000f0000000000

def z245 : W := mkw 0x10c000a2436d03e0 0x39c000f003ff03f0

def z246 : W := mkw 0x47fffefdbc000000 0xfffffffffe00e38f

def z247 : W := mkw 0x24f7ec0003367800 0x10fff000033f7c00

def z248 : W := mkw 0x47fffeffbc480280 0x3ffffffffef80380

def z249 : W := mkw 0x0b037716f8c3de3e 0xef47ff3ffdc7fe7f

def z250 : W := mkw 0x00188b4e14d8a285 0x3eb98f0e02f8e000

def z251 : W := mkw 0x09001214b000041c 0x800000003000000c

def z252 : W := mkw 0x4ffffefdfc030c38 0x37fffffffd071c70

def z253 : W := mkw 0x09001216f041063c 0x8100003ff000027c

def z254 : W := mkw 0x26f5c8a00b347142 0x50b980c00e386183

def z255 : W := mkw 0x0800010240c38e3c 0xad46003fc1c79e7c

def z256 : W := mkw 0x09023614f0030c38 0x27467f3ff1071c70

def z257 : W := mkw 0x02ed50f928000000 0x37fff0fffc000000

def z258 : W := mkw 0x26d3fdb02b92fd5a 0xfbc1fff03f00ffff

def z259 : W := mkw 0x24d3ed000392f800 0x3ac1ff000300fc00

def z260 : W := mkw 0x4713fe14bc000000 0x2747ff3ffc000000

def z261 : W := mkw 0x2d13ff14b092fc1c 0x8201ff003000fc0c

def z262 : W := mkw 0x43189bffbcd8a285 0xffb98ffffef8e38f

def z263 : W := mkw 0x00188b4e14d8a285 0x37b98fce3cf80000

def z264 : W := mkw 0x10fc88eb477d23e1 0x7dff80ffcfff63f3

def z265 : W := mkw 0x02c150b02b00555a 0x39c070f003001ff0

def z266 : W := mkw 0x02d1d9b02b90f55a 0xfff9fff03ff8ffff

def z267 : W := mkw 0x0008024c14000000 0x010000ce3c000000

def z268 : W := mkw 0x47fffefdbf005000 0x3fffffffff00fc00

def z269 : W := mkw 0x1024000140250020 0x00060001c0070000

def z270 : W := mkw 0x47ffeeed9c000000 0x14bf8fcfcc000000

def z271 : W := mkw 0x2d36bf16f0f7ae3c 0xaf7e7f3ff1ff9e7c

def z272 : W := mkw 0x24f7ed0003b6fd5a 0xfeffff0003ffffff

def z273 : W := mkw 0x0000000240410220 0x0100003fc0000270

def z274 : W := mkw 0x2ff7ffb6fbf7ff7e 0xffffffffffffffff

def z275 : W := mkw 0x10ec02ef576d03e5 0xfdfe00ffffff03ff

def z276 : W := mkw 0x02c140a00b005142 0x79c180f00f0063f3

def z277 : W := mkw 0x10ed40eb436d53e0 0x3ffff0ffc3fffff0

def z278 : W := mkw 0x0000000040010020 0x00460031c1070070

def z279 : W := mkw 0x57fffffffffda3e5 0xffffffffffffe3ff

def z280 : W := mkw 0x02c150b02b00555a 0xc84070300300ffff

def z281 : W := mkw 0x00188b4e14d8a285 0x54b98fce0ef86183

def z282 : W := mkw 0x0008034e14d8a285 0xc90000ce3ef8e38f

def z283 : W := mkw 0x6713ff14bc92f800 0x0201ff003c00fc00

def z284 : W := mkw 0x24e7650003a6d800 0x2e467f0001c79c00

def z285 : W := mkw 0x000000000000541a 0xc00000000000fc0f

def z286 : W := mkw 0x12fddbff7ffdf7ff 0xffffffffffffffff

def z287 : W := mkw 0x57fffefdbf2c01c0 0x37fffffffe380180

def z288 : W := mkw 0x00c000a00300555a 0xf9c000f00300ffff

def z289 : W := mkw 0x46fdcaed1c000000 0x37b98fce3c000000

def z290 : W := mkw 0x0800010243c3df7e 0xc800000003c7ffff

def z291 : W := mkw 0x24f5c90003b4f000 0x3eb98f0002f8e000

def z292 : W := mkw 0x67fffefdbf265800 0x37fffffffd071c00

def z293 : W := mkw 0x0000000000000000 0xc80000000200e38f

def z294 : W := mkw 0x47fffefdbf00555a 0x37fffffffd001c70

def z295 : W := mkw 0x0800010000828c1c 0x8000000000009c0c

def z296 : W := mkw 0x02c150b02b00555a 0x50c1f0f00f007df3

def z297 : W := mkw 0x47fffefdbf005142 0x77fffffffe006183

def z298 : W := mkw 0x24f7ed0003b6f800 0xffffffc03fffff8f

def z299 : W := mkw 0x020010b02800055a 0xfb8180f03e00e3ff

def z300 : W := mkw 0x473ffe5dbc000000 0x063fff0ffc000000

def z301 : W := mkw 0x00188b4e14d8a285 0x3db80fce02f80380

def z302 : W := mkw 0x10ec00eb436d03e0 0x11b800ffc23803f0

def z303 : W := mkw 0x2df7fd10e3b7fc38 0x3effff31c3fffc70

def z304 : W := mkw 0x0018884804182081 0xfbb980c03e38e38f

def z305 : W := mkw 0x67fffefdbf347000 0x37fffffffe386000

def z306 : W := mkw 0x0912bf14b492ac1d 0xc201ff003c00fc0f

def z307 : W := mkw 0x09023616f0430e3c 0x8146703ff1071e7c

def z308 : W := mkw 0x100800eb404903e0 0x3db800ffc2f803f0

def z309 : W := mkw 0x10e400a3436d03e0 0x08460031c3ff03f0

def z310 : W := mkw 0x102c0049002c0080 0x0038000000380000

def z311 : W := mkw 0x10ec00e9032c01c0 0x35fe00ffc2380180

def z312 : W := mkw 0x24f7ed0003b6f800 0x047e7f0001ff1c00

def z313 : W := mkw 0x19ee34fbe36f0ff8 0x3dfe70ffc3ff1ff0

def z314 : W := mkw 0x19ec12fff36d07fc 0xbdfe00fff3ff03fc

def z315 : W := mkw 0x0002240000000000 0x26467f0000000000

def z316 : W := mkw 0x47fffefdbc182081 0x77fffffffe386183

def z317 : W := mkw 0x0008004800080080 0x10b800c002380180

def z318 : W := mkw 0x47ffffffbfd8f7df 0xfffffffffff8ffff

def z319 : W := mkw 0x20e4010003b6f800 0x3cfe000003fffc00

def z320 : W := mkw 0x01023714b0828800 0x2f467f3ff1c79c00

def z321 : W := mkw 0x00c140000300555a 0xfac1f0000300ffff

def z322 : W := mkw 0x243eaf4e14feaa85 0xffbf8fce3effe38f

def z323 : W := mkw 0x00e6250003a68800 0x3efe7f0003ff9c00

def z324 : W := mkw 0x0800010240dbaebd 0xc800000003ffffff

def z325 : W := mkw 0x24f5c80003347000 0x3cff800003ff6000

def z326 : W := mkw 0x0000010000828800 0x0800000001c79c00

def z327 : W := mkw 0x0000000003240000 0x0800000003ff0000

def z328 : W := mkw 0x0002250240c38a20 0x2f467f3fc1c79e70

def z329 : W := mkw 0x4ffffffdbc828c1c 0xb7fffffffc009c0c

def z330 : W := mkw 0x02d9d8f82f1875db 0xfbf9f0f03f38ffff

def z331 : W := mkw 0x0000000200480285 0xc00000000000038f

def z332 : W := mkw 0x00188b4e14d8a285 0xc3018fce3c00e38f

def z333 : W := mkw 0x24e5400003245000 0x0000000000000000

def z334 : W := mkw 0x24e7640003265800 0x3cfe700003ff1c00

def z335 : W := mkw 0x2de77716f3e7de3c 0xaf467f3ff1c79e7c

def z336 : W := mkw 0x46fdd8f92c000000 0x33f9f0f03c000000

def z337 : W := mkw 0x0000000003000140 0x08000000030003f0

def z338 : W := mkw 0x19023716f3ef8ffc 0xaf467f3ff3ff9ffc

def z339 : W := mkw 0x100000a140010160 0x00000031c0000070

def z340 : W := mkw 0x1008004a436d03e0 0x3db800ce03ff03f0

def z341 : W := mkw 0x09e63716f3e78e3c 0xbffe7f3ff3ff9e7c

def z342 : W := mkw 0x0012ad000092a800 0x3effff0003fffc00

def z343 : W := mkw 0x10ec00e943250160 0x35fe00ffc1070070

def z344 : W := mkw 0x0000030610c08204 0xff818fce3ec0e38f

def z345 : W := mkw 0x02c150b02b00555a 0xc241f0303d00fc7f

def z346 : W := mkw 0x24f7eda003b6f940 0x3ffffff003fffff0

def z347 : W := mkw 0x2613fd102892fc1a 0xc201ff003c00fc0f

def z348 : W := mkw 0x10000002406d02a0 0x0000000000ff0000

def z349 : W := mkw 0x47d3feb4bc000000 0x33c1fff03c000000

def z350 : W := mkw 0x0000000000000000 0x2546003fc0000000

def z351 : W := mkw 0x46fdd8f92f00555a 0xfbf9f0f03f00ffff

def z352 : W := mkw 0x0010880000102000 0x10b9800002386000

def z353 : W := mkw 0x0000101260410638 0xaf46703ff1c79e7c

def z354 : W := mkw 0x47e774b1a8000000 0x33c7f0f1fc000000

def z355 : W := mkw 0x47fffefdbf000140 0x3fffffffff0003f0

def z356 : W := mkw 0x2cf7ed0243f7fe3c 0xbeffff0003fffe7c

def z357 : W := mkw 0x01023410a0000000 0x00467031c0000000

def z358 : W := mkw 0x00c000a000000000 0x31c000f000000000

def z359 : W := mkw 0x09023716f0c38a24 0x27467f3ff0c70000

def z360 : W := mkw 0x24ffef4e17fefa85 0x3effff0e03fffc00

def z361 : W := mkw 0x0000000000000000 0x0000000000000000

def z362 : W := mkw 0x090a375ef0cb8ebc 0xbffe7ffff3ff9ffc

def z363 : W := mkw 0x1000000043250160 0x0000000001070070

def z364 : W := mkw 0x57fffefffc6d02a0 0x37fffffffcff0000

def z365 : W := mkw 0x09189b5ef4d9a6bd 0xffb98ffffef8e3ff

def z366 : W := mkw 0x08188b4e54dbaebd 0xffb98fce3fffffff

def z367 : W := mkw 0x0002240000020800 0x0046700001071c00

def z368 : W := mkw 0x09023716f0c38e3c 0x85060f3ff0c7027c

def z369 : W := mkw 0x47fddafdbc000000 0x11b980fffc000000

def z370 : W := mkw 0x02c140a00b005142 0x7ac1f0c00f00fd83

def z371 : W := mkw 0x02c150b028000418 0xbbc1f0f03d009e7c

def z372 : W := mkw 0x0000010200c08204 0x8800000000c0820c

def z373 : W := mkw 0x00c1400003005000 0xfbc1f0c03f00ff8f

def z374 : W := mkw 0x47e774b1ab00555a 0xfbc7f0f1ff00ffff

def z375 : W := mkw 0x0bdbfffeffdbffff 0xffffffffffffffff

def z376 : W := mkw 0x0018884804182081 0x0038000000380000

def z377 : W := mkw 0x02c150b02b00555a 0xd281f0c03e00fd8f

def z378 : W := mkw 0x553eae4fd46d02a0 0x043e0f0fc0ff0000

def z379 : W := mkw 0x10ec00eb404903e0 0x35fe00ffc00003f0

def z380 : W := mkw 0x0000000200400200 0x2d00000e00c00200

def z381 : W := mkw 0x0000101020000418 0xfbc1f0f03f00ffff

def z382 : W := mkw 0x34f7eda143b7f960 0x3effff31c3fffc70

def z383 : W := mkw 0x453eaf4f94d8a285 0xffbf8fcffef8e38f

def z384 : W := mkw 0x192e274fd0ef8aa4 0x043e0f0fc0ff0000

def z385 : W := mkw 0x12ed40eb4b6d53e2 0x7dff80ffcfff63f3

def z386 : W := mkw 0x10ec01eb43fda3e5 0xfdfe00ffc3ffe3ff

def z387 : W := mkw 0x0b0237b6f8c38f7e 0xef467ffffdc79fff

def z388 : W := mkw 0x0000000000000000 0x2c46000001c70000

def z389 : W := mkw 0x67fffffdbc92f800 0x37fffffffc00fc00

def z390 : W := mkw 0x00188b4c1490a000 0x3fb98fce3ef8e000

def z391 : W := mkw 0x00108b041490a005 0x00000f0000000000

def z392 : W := mkw 0x02d1dbb43f90f55f 0xfbc1fff03f00ffff

def z393 : W := mkw 0x4b0812fffc41063c 0x810000fffc00027c

def z394 : W := mkw 0x00188a4c14000000 0xffb98fce3e00e38f

def z395 : W := mkw 0x0000010200d8a285 0x0000000000f80000

def z396 : W := mkw 0x00ec00e900000000 0x10b800c000000000

def z397 : W := mkw 0x00c1400000000000 0x32c1f00000000000

def z398 : W := mkw 0x02e550b02b24555a 0xfffff0f03fffffff

def z399 : W := mkw 0x46e540a108000000 0x0000000000000000

def z400 : W := mkw 0x04ffee4c14000000 0x37ffffce3c000000

def z401 : W := mkw 0x430812fdbc00055a 0xc10000fffc0003ff

def z402 : W := mkw 0x00188b4c1490a005 0xf7b98fce3c00e00f

def z403 : W := mkw 0x00ec00e903240000 0x3dfe00ffc3ff0000

def z404 : W := mkw 0x02d9dbfe3cd8a285 0xfff9fffe3ef8e38f

def z405 : W := mkw 0x00d1c9000390f000 0x3ef9ff0003f8fc00

def z406 : W := mkw 0x26e774b02b265d5a 0xfbc7f0f03f07ffff

def z407 : W := mkw 0x0018884a04582281 0x7db980ce0ef86383

def z408 : W := mkw 0x02ed50f92b00555a 0xfffff0ffff00ffff

def z409 : W := mkw 0x0000000000000000 0x3a8180000200e000

def z410 : W := mkw 0x03c376b4b8000000 0x37c7fffffc000000

def z411 : W := mkw 0x67fffffdbfb6fd5a 0xffffffffffffffff

def z412 : W := mkw 0x4b0a37fffcc38e3c 0xaf467ffffdc79e7c

def z413 : W := mkw 0x0000000000000000 0xc20180003c00e00f

def z414 : W := mkw 0x0008004a404902a0 0x3dfe00ffc3ff03f0

def z415 : W := mkw 0x00189b5e34d8a69d 0xfff9fffe3ff8ffff

def z416 : W := mkw 0x02c150b02800055a 0xf3c1f0f03c0003ff

def z417 : W := mkw 0x30ec01eb43fffbe0 0x3dfe00ffc3fffff0

def z418 : W := mkw 0x19febffff7ffaffd 0xffffffffffffffff

def z419 : W := mkw 0x0413ec0000000000 0x0201ff0000000000

def z420 : W := mkw 0x00c800ea034803c0 0x3df800fe03f803f0

def z421 : W := mkw 0x2000010000b6a800 0x0000000000ff0000

def z422 : W := mkw 0x09023716f3c3df7e 0xef467f3ff3c7ffff

def z423 : W := mkw 0x00fc8b4e17fca285 0xffff8fce3fffe38f

def z424 : W := mkw 0x43c952fdbf00555a 0xfbc1f0ffff00ffff

def z425 : W := mkw 0x00ec00e903000140 0x3dfe00ffc30003f0

def z426 : W := mkw 0x24f7ed0243f7fa20 0x3fffff3fc3fffe70

def z427 : W := mkw 0x01023614b0000000 0x02007f0030000000

def z428 : W := mkw 0x0df7ff16f0c38e3c 0xbfffff3ff1c79e7c

def z429 : W := mkw 0x453eaf4f94d8a285 0x043e0f0fc0f80000

def z430 : W := mkw 0x00188b4e17d8f7df 0xffb98fce3ff8ffff

def z431 : W := mkw 0x43ec12fdbc000000 0x35fe00fffc000000

def z432 : W := mkw 0x00c1400003005000 0x1081800002006000

def z433 : W := mkw 0x09001216f041063c 0xab40703ff1009e7c

def z434 : W := mkw 0x47f7fcb1a8000000 0x36ffff31c0000000

def z435 : W := mkw 0x0912bf16f4d3ae3d 0xef47ff3ffdc7fe7f

def z436 : W := mkw 0x19e637b7f3e78f7c 0xaf467f3ff1c79e7c

def z437 : W := mkw 0x002c004900000000 0x043e000fc0000000

def z438 : W := mkw 0x00ec00eb40410220 0x3dfe00ffc1c70270

def z439 : W := mkw 0x06f7fcb02b00555a 0xfffffff03f00ffff

def z440 : W := mkw 0x10ec00eb436d03e0 0x18b800c003ff03f0

def z441 : W := mkw 0x530812fffc4903e0 0x010000fffc0003f0

def z442 : W := mkw 0x090a375ef4cb8ebd 0xef467ffffdc79fff

def z443 : W := mkw 0x04e7640000000000 0x0046700000000000

def z444 : W := mkw 0x09023512e0c38e3c 0x88467031c1c79e7c

def z445 : W := mkw 0x020150102800541a 0xeb41f0303d00fe7f

def z446 : W := mkw 0x0000000000000000 0xab0000003000820c

def z447 : W := mkw 0x0010880000000000 0x36b98f0000000000

def z448 : W := mkw 0x06f7fcb028000000 0x37fffff03c000000

def z449 : W := mkw 0x47fffefffc410220 0x3ffffffffdc70270

def z450 : W := mkw 0x2436ad0003b6f800 0x0c3e0f0003fffc00

def z451 : W := mkw 0x01ee36fdb0000000 0x37fe7ffff0000000

def z452 : W := mkw 0x4611c8000c000000 0x000180000c000000

def z453 : W := mkw 0x02c150b02b00555a 0xd18180f03e0063ff

def z454 : W := mkw 0x00c140a003005140 0x3bc1f0f00300fff0

def z455 : W := mkw 0x020000a008000142 0x400000c00c000183

def z456 : W := mkw 0x10fc89eb43fda3e0 0x3fff8fffc3ffe3f0

def z457 : W := mkw 0x34f7ed0243fffbe0 0x3effff0003fffff0

def z458 : W := mkw 0x0010890200d8a285 0xfeb98f0002f8e38f

def z459 : W := mkw 0x47fffcf9ac000000 0x10fff0f1cc000000

def z460 : W := mkw 0x67ffffffbffefa85 0xffffffffffffff8f

def z461 : W := mkw 0x00d88bee17d8a3c5 0xfff98ffe3ff8e3ff

def z462 : W := mkw 0x02c150102b00541a 0xfac1f0003f00fc0f

def z463 : W := mkw 0x01023616f0410220 0x2f467f3ff1c70270

def z464 : W := mkw 0x243eaf4e14feaa85 0x043e0f0e00ff0000

def z465 : W := mkw 0x10ee25eb43ef8be0 0x3ffe7fffc3ff9ff0

def z466 : W := mkw 0x0008004804080081 0x400000c00c000183

def z467 : W := mkw 0x001089000090a000 0xffb98fc03ef8e38f

def z468 : W := mkw 0x00e4000003240000 0x10b8000002380000

def z469 : W := mkw 0x47f7fe14bc000000 0x36ffff003c000000

def z470 : W := mkw 0x0000000000000000 0xc10000c03c00038f

def z471 : W := mkw 0x24fdc848073c7081 0x50b980c00e386183

def z472 : W := mkw 0x14ffeceb436d03e0 0x3fffffffc3ff03f0

def z473 : W := mkw 0x011abe5cb4000000 0x37fffffffc000000

def z474 : W := mkw 0x57ef74fbeb6d03e0 0x3dfe70ffc3ff03f0

def z475 : W := mkw 0x0000000000000000 0x2a40700001009c00

def z476 : W := mkw 0x0bc374b0eb035d7a 0xfbc7f0f1ff07ffff

def z477 : W := mkw 0x0008004a00480280 0x010000ce00000380

def z478 : W := mkw 0x57fffefdff250160 0x37fffffffd070070

def z479 : W := mkw 0x0bc377b6f8c38e3c 0xbfc7fffffdc79e7c

def z480 : W := mkw 0x02c150b02b00555a 0xab40703031009e7c

def z481 : W := mkw 0x0018884804000000 0x10b980c00c000000

def z482 : W := mkw 0x4ffffffffcc38a24 0x37fffffffcc70000

def z483 : W := mkw 0x0000030650c18224 0xaf460f3ff1c7827c

def z484 : W := mkw 0x020150102800541a 0xfb81f0c03e00ff8f

def z485 : W := mkw 0x47fffeffbc480285 0xf7fffffffc00038f

def z486 : W := mkw 0x26f7fd102bb6fc1a 0xfeffff003ffffc0f

def z487 : W := mkw 0x10ec00e9032c01c0 0x3cfe00c003ff0180

def z488 : W := mkw 0x2dffff5ef7fffebd 0xffffffffffffffff

def z489 : W := mkw 0x24e7650003b6f800 0x0846700003fffc00

def z490 : W := mkw 0x02d9cbee1fd8f3c7 0xffb98fce3ef8e38f

def z491 : W := mkw 0x0001400000005000 0x0201f0000000fc00

def z492 : W := mkw 0x00108b041490a005 0xfb818fc03e00e38f

def z493 : W := mkw 0x09022706d0c38a24 0x2e467f0fc1c79c00

def z494 : W := mkw 0x00e4000000000000 0x34fe000000000000

def z495 : W := mkw 0x5fffffffffef8ffc 0xbfffffffffff9ffc

def z496 : W := mkw 0x26f5d8b02b34755a 0xfbf9f0f03f38ffff

def z497 : W := mkw 0x0018894a04d8a285 0xd8b980c00ef8e38f

def z498 : W := mkw 0x4d3eaf4fd4c38a24 0x043e0f0fc0c70000

def z499 : W := mkw 0x000010102300555a 0xeb4070303300ffff

def z500 : W := mkw 0x09001316f0c1863c 0xaf000f3ff0c0827c

def z501 : W := mkw 0x190a37fff0cb8ffc 0xaf467ffff1c79ffc

def z502 : W := mkw 0x12e550b16b25557a 0xfbc7f0f1ff07ffff

def z503 : W := mkw 0x09022706d0c38e3c 0x8c060f0fc1c79e7c

def z504 : W := mkw 0x0008024e14480285 0xfdb800ce3ef8038f

def z505 : W := mkw 0x02c150b02b00555a 0x33c1f0f03d001c70

def z506 : W := mkw 0x0000131630c0861c 0xaf407f3e31c09e7c

def z507 : W := mkw 0x2436ad0000b6a800 0x2e7e7f0001ff9c00

def z508 : W := mkw 0x04f7ed0000828800 0x3effff0001c79c00

def z509 : W := mkw 0x10188b4e57fda3e5 0xffb98fce3fffe3ff

def z510 : W := mkw 0x0010880004102001 0x400180000c006003

def z511 : W := mkw 0x10fc8aef576d03e0 0x3fff8fffffff03f0

def z512 : W := mkw 0x10e400a143250160 0x3cfe0031c3ff0070

def z513 : W := mkw 0x1008004b404902a0 0x0000000fc0000000

def z514 : W := mkw 0x09c37716f3c3de3c 0xbfc7ff3ff3c7fe7c

def z515 : W := mkw 0x2413ed000092f800 0x2e47ff0001c7fc00

def z516 : W := mkw 0x00e4000243650220 0x3dfe003fc3ff0270

def z517 : W := mkw 0x36fffdfb6bfffffa 0xffffffffffffffff

def z518 : W := mkw 0x0000000000182081 0x4000000002386183

def z519 : W := mkw 0x47ef74f9a8000000 0x35fe70ffc0000000

def z520 : W := mkw 0x2010890003b6f800 0x3eb98f0003fffc00

def z521 : W := mkw 0x00c000a003000140 0x0040003001000070

def z522 : W := mkw 0x02c950fa2b4857da 0xfff9f0fe3ff8ffff

def z523 : W := mkw 0x02c150b028000000 0xfbc1f0f03e00e38f

def z524 : W := mkw 0x24f7ec0003265800 0x36ffff0001071c00

def z525 : W := mkw 0x6ffffffffff7fe3c 0xbffffffffffffe7c

def z526 : W := mkw 0x09023716f0c38e3c 0x83007f3ff0009e7c

def z527 : W := mkw 0x47ffffffbcc08204 0xbffffffffcc0820c

def z528 : W := mkw 0x47fffffdbc90a000 0x3ffffffffef8e000

def z529 : W := mkw 0x12ed40e90b2c51c2 0x50b980c00e386183

def z530 : W := mkw 0x26f7fdb02bb6fd5a 0x3effff3003fffc70

def z531 : W := mkw 0x02c140a00b005142 0xfb8180c03e00e38f

def z532 : W := mkw 0x09023412e0430e38 0x2d46703fc1c71e70

def z533 : W := mkw 0x10fc8bef17fca3c5 0xffb98fce3ef8e38f

def z534 : W := mkw 0x02d9c8e80f1871c3 0x50b980c00e386183

def z535 : W := mkw 0x24ffede903b6f800 0x3fffffffc3fffc00

def z536 : W := mkw 0x34ef64eb436f5be0 0x3dfe70ffc3ff1ff0

def z537 : W := mkw 0x09023410e0030c38 0xab467031f1079e7c

def z538 : W := mkw 0x09001010e0010438 0x00000031c0000070

def z539 : W := mkw 0x24f7ef0417b6f805 0xfeffff003ffffc0f

def z540 : W := mkw 0x02c150b26b41577a 0xffc7f0ffffc7ffff

def z541 : W := mkw 0x4ffffefffc41063c 0xb7fffffffc00027c

def z542 : W := mkw 0x00188a4e14480280 0x3fb98fce3ef80380

def z543 : W := mkw 0x02c150b02b00555a 0x3ac1f0300300fc70

def z544 : W := mkw 0x67e774b1ab265800 0x00467031c1071c00

def z545 : W := mkw 0x46ffece90c000000 0x36ffffc00c000000

def z546 : W := mkw 0x471bff5ebcd8a285 0xffb9ffce3ef8e38f

def z547 : W := mkw 0x020010102800041a 0xc00000003c00000f

def z548 : W := mkw 0x12ed50fb6b6d03e0 0x3ffff0ffffff03f0

def z549 : W := mkw 0x190812fff04907fc 0x810000fff00003fc

def z550 : W := mkw 0x34fdc8eb437d73e0 0x3dff80ffc3ff63f0

def z551 : W := mkw 0x02c150b02b005142 0x73c1f0f03e006183

def z552 : W := mkw 0x00188a4e14480285 0xf7b98fce3c00038f

def z553 : W := mkw 0x00c000a003000140 0x108000c002000180

def z554 : W := mkw 0x09023714b0828c1c 0xa7467f3ff0009c0c

def z555 : W := mkw 0x0008004800000000 0x35b800ce00000000

def z556 : W := mkw 0x00ec004a036c0280 0x3dfe00ce03ff0380

def z557 : W := mkw 0x2000000003265800 0x0000000001071c00

def z558 : W := mkw 0x2434880000342000 0x0038000000380000

def z559 : W := mkw 0x200001000092f800 0x000000000000fc00

def z560 : W := mkw 0x0000000000000000 0x2940003001000270

def z561 : W := mkw 0x22c151b02bb6fd5a 0xfbc1f0f03fffffff

def z562 : W := mkw 0x0436ac0000000000 0x043e0f0000000000

def z563 : W := mkw 0x26f7fdb02bb6f800 0x3ffffff03ffffc00

def z564 : W := mkw 0x2411c80000107000 0x0001800000006000

def z565 : W := mkw 0x09001316f0c38e3c 0x8900003ff1c79e7c

def z566 : W := mkw 0x10ec00eb436d03e0 0xffff80ffffffe3ff

def z567 : W := mkw 0x02d9dafc3c000000 0x37f9fffe3c000000

def z568 : W := mkw 0x34ffefef57fffbe5 0xffffffffffffffff

def z569 : W := mkw 0x24f5c80003347000 0x3af9f0000338fc00

def z570 : W := mkw 0x2403640000025800 0x0000700000001c00

def z571 : W := mkw 0x103c8b4f54fda2a5 0xffbf8fcffeffe38f

def z572 : W := mkw 0x24fdcb4e17fcf285 0xffb98fce3ef8e38f

def z573 : W := mkw 0x2d13ff16f0d3fe3c 0xaf47ff3ff1c7fe7c

def z574 : W := mkw 0x0008014a00d8a285 0xfdb800ce02f8e38f

def z575 : W := mkw 0x10ec00e9032c01c0 0x39f800f0033803f0

def z576 : W := mkw 0x02189bfe3cd8a7df 0xffb98ffe3ef8e3ff

def z577 : W := mkw 0x34fdc8e9033c71c0 0x10b980c002386180

def z578 : W := mkw 0x2df7ef06d3f7fa24 0x3effff0fc3fffc00

def z579 : W := mkw 0x091abf5eb4daae9d 0xffb9ffce3ef8ff8f

def z580 : W := mkw 0x0000101020000418 0x810000303000027c

def z581 : W := mkw 0x0b0012b6f841077e 0xc10000fffc0003ff

def z582 : W := mkw 0x43c952fdbc000000 0x33c1f0fffc000000

def z583 : W := mkw 0x24f7ed0203fefa85 0xfeffff0003ffff8f

def z584 : W := mkw 0x0802250240c38e3c 0xae467f0001c79e7c

def z585 : W := mkw 0x10e40002436d03e0 0x3cfe000003ff03f0

def z586 : W := mkw 0x24f7fd1023b6fc18 0xbfffff3033fffe7c

def z587 : W := mkw 0x09023714b0828c1c 0xab407f3031009e7c

def z588 : W := mkw 0x57fffefffc4903e0 0x37fffffffc0003f0

def z589 : W := mkw 0x56fdc8e90f2c01c0 0x10b980c00e380180

def z590 : W := mkw 0x02c153b63bc0d75e 0xffc1fffe3fc0ffff

def z591 : W := mkw 0x47ffffffbcd8a285 0x37fffffffcf80000

def z592 : W := mkw 0x47fffffdbc90a005 0xf7fffffffc00e00f

def z593 : W := mkw 0x443c884904000000 0x0038000000000000

def z594 : W := mkw 0x3dfffffff3fffffc 0xbffffffff3fffffc

def z595 : W := mkw 0x0000020414000005 0xc00000003c00000f

def z596 : W := mkw 0x10e400a343650360 0x2d46003fc1c70270

def z597 : W := mkw 0x0000000000000000 0x338180c03c000000

def z598 : W := mkw 0x0008024e14480285 0x0000000e00000000

def z599 : W := mkw 0x12ec10fb6b6d07fa 0xfdfe00ffffff03ff

def z600 : W := mkw 0x02c150b02b005000 0x3bc1f0f03f00fc00

def z601 : W := mkw 0x0000020610400204 0x8100000e3000020c

def z602 : W := mkw 0x2000010003b6fd5a 0xc800000003ffffff

def z603 : W := mkw 0x000000000000055a 0xc0000000000003ff

def z604 : W := mkw 0x4512ae0494000000 0x00000f0000000000

def z605 : W := mkw 0x00188b4e14d8a285 0xcc380f0e02f8e38f

def z606 : W := mkw 0x10ec00eb406d02a0 0x35fe00ffc0ff0000

def z607 : W := mkw 0x2002250003b6f800 0x2e467f0003fffc00

def z608 : W := mkw 0x4fe774b1e8030c38 0x00467031c1071c70

def z609 : W := mkw 0x66fdc8e90f347000 0x10b980c00e386000

def z610 : W := mkw 0x00e5400003245000 0x3efff00003fffc00

def z611 : W := mkw 0x0000010200d8a285 0xfb8180c03ef8e38f

def z612 : W := mkw 0x0018894a00d8a280 0x3fb98fce02f8e380

def z613 : W := mkw 0x0000000000000000 0x508180c00e006183

def z614 : W := mkw 0x4526240180000000 0x00060001c0000000

def z615 : W := mkw 0x04f7ec0003005000 0x3effff000300fc00

def z616 : W := mkw 0x1800010243ef8ffc 0x8800000003ff9ffc

def z617 : W := mkw 0x091abf5ef4dbaebd 0xaf7e7f3ff1ff9e7c

def z618 : W := mkw 0x09023716b0c28e1c 0xaf007f0e30c09e0c

def z619 : W := mkw 0x24f7ed0003b6f800 0x14bf8f0002ff6000

def z620 : W := mkw 0x020010b02800055a 0x0000003000000070

def z621 : W := mkw 0x100800eb404903e0 0x2d4600ffc1c703f0

def z622 : W := mkw 0x00188a4e14582285 0xd1b980ce3e38638f

def z623 : W := mkw 0x00e400a003240140 0x3dfe00f003ff03f0

def z624 : W := mkw 0x080000024041063c 0x800000000000027c

def z625 : W := mkw 0x00108a0414000000 0x02018f003c000000

def z626 : W := mkw 0x24ffed4807bef881 0x7effffc00ffffd83

def z627 : W := mkw 0x09000206d0410224 0x0000000fc0000000

def z628 : W := mkw 0x10ec03ef53ed83e4 0xbffe0ffff3ff83fc

def z629 : W := mkw 0x00c0000003000000 0x38c0000003000000

def z630 : W := mkw 0x0000000000000000 0x398000c002000380

def z631 : W := mkw 0x0002250000828800 0x04060f0000c70000

def z632 : W := mkw 0x67f7fdb1abb6f800 0x3effff31c3fffc00

def z633 : W := mkw 0x00d9cb4e17d8f285 0xfff9ffce3ff8ff8f

def z634 : W := mkw 0x0800111260c38e3c 0xab40703031c79e7c

def z635 : W := mkw 0x10188bef54d9a3e5 0xffb98ffffef8e3ff

def z636 : W := mkw 0x12e550b16b25557a 0x00467031c1071c70

def z637 : W := mkw 0x18ec01eb43ef8ffc 0xbdfe00ffc3ff9ffc

def z638 : W := mkw 0x00108b0614d8a285 0xca018f003ef8e38f

def z639 : W := mkw 0x12ed50fb6b6d57fa 0x3dfe70ffc3ff1ff0

def z640 : W := mkw 0x47f7feb5bc000000 0x0247ff31fc000000

def z641 : W := mkw 0x00e4000003240000 0x0046000001070000

def z642 : W := mkw 0x34ffed4b43fffaa0 0x3effff0fc3fffc00

def z643 : W := mkw 0x04f5c80000000000 0x10b9800000000000

def z644 : W := mkw 0x10000002436d03e0 0x2d46003fc3ff03f0

def z645 : W := mkw 0x000001000090a000 0x0800000002f8e000

def z646 : W := mkw 0x02c952fe3f4857df 0xfbc1f0fe3f00ffff

def z647 : W := mkw 0x09022706d0c38a24 0x2d460f3fc1c70270

def z648 : W := mkw 0x471bfe5cbc000000 0x37b9ffce3c000000

def z649 : W := mkw 0x430010b1a8000000 0x00000031c0000000

def z650 : W := mkw 0x34feadeb43ffabe0 0x3dfe0fffc3ff03f0

def z651 : W := mkw 0x02c010b02b00055a 0xf9c000f03f0003ff

def z652 : W := mkw 0x24f6ad0003b6a800 0x3cfe0f0003ff0000

def z653 : W := mkw 0x2000000003347000 0x0000000002386000

def z654 : W := mkw 0x09023410a0020c18 0x0000700000001c00

def z655 : W := mkw 0x0000000003005000 0x080000000300fc00

def z656 : W := mkw 0x0000101020000418 0x8200700030009c0c

def z657 : W := mkw 0x24f7ed0000b6a800 0x36ffff0000ff0000

def z658 : W := mkw 0x2d36af06d0f7aa24 0x043e0f0fc0ff0000

def z659 : W := mkw 0x24f7ed0003b6f800 0x0247ff000107fc00

def z660 : W := mkw 0x10ec004b436d02a0 0x3cfe000fc3ff0000

def z661 : W := mkw 0x001089000090a000 0x04380f0000f80000

def z662 : W := mkw 0x24f7ef0613f6fa04 0xbfffff0e33fffe0c

def z663 : W := mkw 0x020010b028000000 0x010000f03c000000

def z664 : W := mkw 0x0bc377b4bb82dd5e 0xfbc1fff03f00ffff

def z665 : W := mkw 0x000000a000000140 0x010000f0000003f0

def z666 : W := mkw 0x2413ed0003b6f800 0x0a01ff0003fffc00

def z667 : W := mkw 0x2426240000260800 0x0006000000070000

def z668 : W := mkw 0x2000010203fefa85 0xc800000003ffff8f

def z669 : W := mkw 0x02c375b02b82dd5a 0xffc7fff03fc7ffff

def z670 : W := mkw 0x24f7ed000092f800 0x36ffff000000fc00

def z671 : W := mkw 0x0008024e14480285 0xfb8180ce3e00e38f

def z672 : W := mkw 0x43001214bc000000 0x000000003c000000

def z673 : W := mkw 0x0024000000240000 0x043e000000ff0000

def z674 : W := mkw 0x24e7640003265800 0x3ac7f0000307fc00

def z675 : W := mkw 0x00c1400003005000 0x0040700001001c00

def z676 : W := mkw 0x2413ed000092f800 0x3eb9ff0002f8fc00

def z677 : W := mkw 0x0800030650c38e3c 0xaf000f0e31c79e7c

def z678 : W := mkw 0x0008034e10c88284 0xbfb80fce32f8838c

def z679 : W := mkw 0x10e400a143250160 0x39c600f1c30703f0

def z680 : W := mkw 0x09022706d0c38a24 0xaf060f0ff0c7820c

def z681 : W := mkw 0x4ffffffffcdbaebd 0xffffffffffffffff

def z682 : W := mkw 0x10ec00e9432d01e0 0x10fe00f1c33f01f0

def z683 : W := mkw 0x26fffffe3ffeffdf 0xfffffffe3fffffff

def z684 : W := mkw 0x67f7ff14bfb6f800 0x3effff003ffffc00

def z685 : W := mkw 0x00c1501023005418 0xbbc1f0303300fe7c

def z686 : W := mkw 0x00ec00eb00480280 0x3dfe00ffc2f80380

def z687 : W := mkw 0x192e375ff0ef8ebc 0xaf7e7f3ff1ff9e7c

def z688 : W := mkw 0x100800eb436d03e0 0x090000ffc3ff03f0

def z689 : W := mkw 0x0201501028000000 0x0201f0003c000000

def z690 : W := mkw 0x20c1410003b6f800 0x3ac1f00003fffc00

def z691 : W := mkw 0x0bc152b6fb41577e 0xfbc1f0ffff00ffff

def z692 : W := mkw 0x09023616f041063c 0xa7467f3ff000027c

def z693 : W := mkw 0x0bc374b0eb035d7a 0x00467031c1071c70

def z694 : W := mkw 0x00108b041490a005 0xfeb98f003ef8e00f

def z695 : W := mkw 0x02d9dafc3f00555a 0xfff9fffe3f00ffff

def z696 : W := mkw 0x0002351020828c18 0xaf467f3031c79e7c

def z697 : W := mkw 0x100802ef544903e5 0xc10000fffc0003ff

def z698 : W := mkw 0x47fffefdbc000000 0x12b9ffc03c000000

def z699 : W := mkw 0x2df7ff14b3b6fc1c 0xbeffff0033fffc0c

def z700 : W := mkw 0x04ffef4e14d8a285 0xffffffce3ef8e38f

def z701 : W := mkw 0x10ec00eb036c03c0 0x3db800ce02f80380

def z702 : W := mkw 0x46fdc8e90c182081 0x50b980c00e386183

def z703 : W := mkw 0x00188b4e14d8a285 0xc6398f0e3cf8e00f

def z704 : W := mkw 0x00108b0610d0a204 0xbfb98f0e32f8e20c

def z705 : W := mkw 0x77fffffffffffbe0 0x3ffffffffffffff0

def z706 : W := mkw 0x34ffede903bef9c0 0x3effffc003fffd80

def z707 : W := mkw 0x09001316f0c38e3c 0x8800000031c79e7c

def z708 : W := mkw 0x47fffefdbf005000 0x37fffffffd001c00

def z709 : W := mkw 0x41188a4d94000000 0x37b98fcffc000000

def z710 : W := mkw 0x10ec00eb436d03e0 0x2d7e003fc1ff0270

def z711 : W := mkw 0x47fffefdbc000000 0x057e7ffffc000000

def z712 : W := mkw 0x0800010240c38a24 0x0800000001c79c00

def z713 : W := mkw 0x1800010240ef8aa4 0x0000000000ff0000

def z714 : W := mkw 0x01023614b0000000 0xaf467f3ff000820c

def z715 : W := mkw 0x47fffefdbc000000 0x16bfffcffc000000

def z716 : W := mkw 0x12ed40eb4b6d03e0 0x3dff80ffcfff03f0

def z717 : W := mkw 0x430a36fdbc000000 0x03007ffffc000000

def z718 : W := mkw 0x00188a4e14582285 0xf7b98fce3e38638f

def z719 : W := mkw 0x2cf5c90243f7fe3c 0x98b9800003fffe7c

def z720 : W := mkw 0x471bfe5cbc000000 0x37fffffffc000000

def z721 : W := mkw 0x4efdc9eb4cc38e3c 0x98b980c00dc79e7c

def z722 : W := mkw 0x01ee26ed90000000 0x35fe0fffc0000000

def z723 : W := mkw 0x2636bdb028b6ad5a 0xc53e0ff03cff03ff

def z724 : W := mkw 0x453eae4d9700555a 0xcc3e0f0fc300ffff

def z725 : W := mkw 0x45feae4d94000000 0x34fe0f0fc0000000

def z726 : W := mkw 0x24f7ed0003b6f800 0x36ffff0001ff1c00

def z727 : W := mkw 0x00188a4c14182081 0xffb98fce3e38e38f

def z728 : W := mkw 0x24f7ed0003b6f800 0x7effffc00ffffd83

def z729 : W := mkw 0x67fffefdbf3c7081 0x77fffffffe386183

def z730 : W := mkw 0x0800010240c38a24 0x0800000001c70270

def z731 : W := mkw 0x00e400a243650360 0x3dfe00ffc3ff03f0

def z732 : W := mkw 0x01ee36fdb3000558 0xbffe7ffff3009ffc

def z733 : W := mkw 0x45ffee4d94000000 0x14bf8f0fc0000000

def z734 : W := mkw 0x430236b5b8000000 0x27467f3ff0000000

def z735 : W := mkw 0x6713ff14bc92fc1a 0xc201ff003c00fc0f

def z736 : W := mkw 0x65f7ed0183b6f800 0x3effff01c3fffc00

def z737 : W := mkw 0x00ec00e903240140 0x3dfe00ffc3ff03f0

def z738 : W := mkw 0x07f7feb4b8000000 0x37fffffffc000000

def z739 : W := mkw 0x47fffefdbf005140 0x3fffffffff00fff0

def z740 : W := mkw 0x05fffe5cb4000000 0x37fffffffc000000

def z741 : W := mkw 0x020150b02800555a 0xfb81f0f03e00ffff

def z742 : W := mkw 0x0bc367a6dbc3db66 0x54878fcfcec76183

def z743 : W := mkw 0x473ffe5dbc000000 0x37bfffcffc000000

def z744 : W := mkw 0x10ed40eb436d53e0 0xfffff0ffffffffff

def z745 : W := mkw 0x24f7ed0003b6f800 0x3fffff3003fffe70

def z746 : W := mkw 0x47fffefdbf00055a 0xffffffffff0003ff

def z747 : W := mkw 0x55feaeed972c01c0 0x14be0fcfc2380180

def z748 : W := mkw 0x47fffefdbc000000 0x3ffffffffef80000

def z749 : W := mkw 0x76fdc8e90f3c71c0 0x10b980c00e386180

def z750 : W := mkw 0x20d1c90003b6f800 0x3ef9ff0003fffc00

def z751 : W := mkw 0x0000010240d9a2a5 0xc800000003ffe3ff

def z752 : W := mkw 0x45feae4d97240000 0x3cfe0f0fc3ff0000

def z753 : W := mkw 0x24f7ed0003b6f800 0x3fffff3fc3fffc00

def z754 : W := mkw 0x34ed40eb436d53e0 0x3dfe00ffc3ff03f0

def z755 : W := mkw 0x24e7650003a6d800 0x3efe7f0003ff9c00

def z756 : W := mkw 0x453eae4d94000000 0xffbf8fcffe00e38f

def z757 : W := mkw 0x2df5da16f375763c 0x91b9803ff238627c

def z758 : W := mkw 0x1800010240cb8ffc 0x8800000001c79ffc

def z759 : W := mkw 0x03c376b4bb005142 0x77c7fffffe006183

def z760 : W := mkw 0x34fdc9eb43fffbe0 0x18b980c003fffff0

def z761 : W := mkw 0x03dbfefcbf00555a 0xffffffffff00ffff

def z762 : W := mkw 0x45feaeed94000000 0x047e0f3fc0000000

def z763 : W := mkw 0x67fffefdbf265800 0x3fffffffff07fc00

def z764 : W := mkw 0x10f48ba557b5a165 0xc2478f31fd07e07f

def z765 : W := mkw 0x04f7ed000092a800 0x3effff0003fffc00

def z766 : W := mkw 0x24f7ed0003b6f805 0xfeffff0003fffc0f

def z767 : W := mkw 0x00188a4e14480280 0xffb98fce3ef8e38f

def z768 : W := mkw 0x02c150b02b00555a 0xda81f0c03f00ffff

def z769 : W := mkw 0x0002240000000000 0x27467f3fc0000000

def z770 : W := mkw 0x011aae4c94000000 0x043e0f0fc0000000

def z771 : W := mkw 0x4713fe14bc00541a 0xef47ff3ffd00fe7f

def z772 : W := mkw 0x453eae4d94182081 0x043e0f0fc0380000

def z773 : W := mkw 0x24ef664e176e5a85 0xc14670ce3d071f8f

def z774 : W := mkw 0x10ec00eb436d53e0 0x3dfe00ffc3fffff0

def z775 : W := mkw 0x341bedeb40dbfbe0 0x0301ffffc000fff0

def z776 : W := mkw 0x57fffefdbf2c01c0 0x3fffffffff3803f0

def z777 : W := mkw 0x09023616f0430e3c 0xa7467f3ff1071e7c

def z778 : W := mkw 0x473ebefdbc000000 0x277e7ffffc000000

def z779 : W := mkw 0x122d505b686d56ba 0xc63ff00ffcfffc0f

def z780 : W := mkw 0x0002351260c38e38 0xaf467f3ff1c79e7c

def z781 : W := mkw 0x00188b4c1490a000 0xffb98fce3ef8e38f

def z782 : W := mkw 0x0800010240c38a24 0x8800000000c7820c

def z783 : W := mkw 0x102c004b406d02a0 0x047e003fc1ff0070

def z784 : W := mkw 0x010a365cb4000000 0x27467ffffc000000

def z785 : W := mkw 0x630813fdbfb6f800 0x090000fffffffc00

def z786 : W := mkw 0x09023714f0838c3c 0xa7467f3ff1079c7c

def z787 : W := mkw 0x10ec00eb436d53e2 0x7dfe00ffc3ff63f3

def z788 : W := mkw 0x47fffefdbf005000 0xffffffffff00ff8f

def z789 : W := mkw 0x47e775b3a8d8a285 0xc8467031c2f8e38f

def z790 : W := mkw 0x453eae4d94000000 0x257e0f3fc0000000

def z791 : W := mkw 0x2ac151b26bf7ff7e 0xfbc1f0f03fffffff

def z792 : W := mkw 0x02d9dbfe3fd8f7df 0x04787f3e01f81c70

def z793 : W := mkw 0x46e550b12b00555a 0xfbc1f0f03f00ffff

def z794 : W := mkw 0x473ebefdbc00055a 0xc53e0ffffc0003ff

def z795 : W := mkw 0x57e774b1eb25557a 0x00467031c1071c70

def z796 : W := mkw 0x47fffefdbc00055a 0xfffffffffd009fff

def z797 : W := mkw 0x453eae4d94000000 0x36bf8f0fc0000000

def z798 : W := mkw 0x24f7ed0003b6f800 0x3fffffc003ffff80

def z799 : W := mkw 0x09023716f0c38e3c 0xef47ff3ffdc7fe7f

def z800 : W := mkw 0x47fffefdbc00541a 0xfffffffffe00ff8f

def z801 : W := mkw 0x0ac151b26bc3df7e 0x8840703001c79e7c

def z802 : W := mkw 0x020150102b00555a 0xfb81f0c03f00ffff

def z803 : W := mkw 0x0800010240c38e3c 0xc800000003c7ffff

def z804 : W := mkw 0x04f7ec0000000000 0x37ffff3fc0000000

def z805 : W := mkw 0x00188b4e54d9a2a5 0xffb98fce3fffe3ff

def z806 : W := mkw 0x5713fe16ff6d03e0 0x0a01ff003fff03f0

def z807 : W := mkw 0x43d9dafdbf00555a 0xfff9ffffff00ffff

def z808 : W := mkw 0x10ec004b436d02a0 0x3dfe003fc3ff0270

def z809 : W := mkw 0x43fc9afdbc000000 0x37ff8ffffc000000

def z810 : W := mkw 0x0800010243dbffff 0xc800000003ffffff

def z811 : W := mkw 0x0818894a44dbaebd 0xd8b980c00fffffff

def z812 : W := mkw 0x10ec00eb436d03e0 0x3ffe70ffc3ff9ff0

def z813 : W := mkw 0x2437ed0003b6f800 0x0e3fff0003fffc00

def z814 : W := mkw 0x0a01511268c3de3e 0xca01f0003dc7fe7f

def z815 : W := mkw 0x19ee37fdb3ae8ddc 0x92b87fc032389d8c

def z816 : W := mkw 0x00d3ed000392f800 0x3effff0003fffc00

def z817 : W := mkw 0x09022706d0c38a24 0x2f467f3fc1c79e70

def z818 : W := mkw 0x00188b4e14daaa85 0xffb98fce3fffff8f

def z819 : W := mkw 0x47fffefdbc00541a 0x37fffffffc001c00

def z820 : W := mkw 0x24f7eda003b6f940 0x3effffc003fffd80

def z821 : W := mkw 0x47fffefdbc000000 0x3ffffffffe00e000

def z822 : W := mkw 0x0000010240c18224 0x8800000001c7827c

def z823 : W := mkw 0x2413ed0003b6f800 0x3eb9ff0003fffc00

def z824 : W := mkw 0x2800010243fffebd 0xc800000003ffffff

def z825 : W := mkw 0x2437ed0000b6f800 0x3ebfff0002fffc00

def z826 : W := mkw 0x0912bf14b092ac1c 0x8201ff003000fc0c

def z827 : W := mkw 0x47fffefdbc000000 0x14ffffffcc000000

def z828 : W := mkw 0x453eae4d94000000 0x053e0fcffc000000

def z829 : W := mkw 0x47fffefdbc000418 0xb7fffffffc009c0c

def z830 : W := mkw 0x193eaf4fd4ffaaa5 0x043e0f0fc0ff0000

def z831 : W := mkw 0x010a365cb0000000 0x37fe7ffff0000000

def z832 : W := mkw 0x08c001a243c38f7c 0xb9c000f003c79ffc

def z833 : W := mkw 0x05fffefdb0000000 0x37fffffff0000000

def z834 : W := mkw 0x02fddafd3c000000 0x37fffffffc000000

def z835 : W := mkw 0x430812fdbc000000 0x27000ffffc000000

def z836 : W := mkw 0x4ffffefdbc020c18 0x37fffffffc001c00

def z837 : W := mkw 0x453eae4d94000000 0x267e7f0fc0000000

def z838 : W := mkw 0x43189afdbc00055a 0xffb98ffffe00e3ff

def z839 : W := mkw 0x3000010243fffffa 0xc800000003ffffff

def z840 : W := mkw 0x4526260590000000 0x04060f0fc0000000

def z841 : W := mkw 0x57fffefdbf2c51c2 0x77fffffffe386183

def z842 : W := mkw 0x24f7ed0003b6f800 0x0c7e7f0003fffc00

def z843 : W := mkw 0x473ebefdbc000000 0x37bf8ffffc000000

def z844 : W := mkw 0x57fffefdbf2c01c0 0x3fffffffffff0180

def z845 : W := mkw 0x41188b4f94d8a285 0xffb98fcffef8e38f

def z846 : W := mkw 0x26f7eda00bb6f942 0x7ffffff00ffffff3

def z847 : W := mkw 0x011abe5cb4182081 0x77fffffffe386183

def z848 : W := mkw 0x36e774b16b275d7a 0x00467031c1071c70

def z849 : W := mkw 0x0800010240c3de3e 0xc800000001c7fe7f

def z850 : W := mkw 0x473ebe5dbc000000 0x043e0f0ffc000000

def z851 : W := mkw 0x4512be14b4000000 0x27467f3ff0000000

def z852 : W := mkw 0x67fffefdbf367800 0x37ffffffff3f7c00

def z853 : W := mkw 0x67fffefdbf347000 0x3fffffffffff6000

def z854 : W := mkw 0x47fffefdbc000000 0x77fffffffe006183

def z855 : W := mkw 0x09023716f0c38e3c 0xef467f3ff3c7ffff

def z856 : W := mkw 0x24f7ed0003b6f800 0x1ab9ff0003fffc00

def z857 : W := mkw 0x47fffefdbc240000 0x37fffffffcff0000

def z858 : W := mkw 0x09023614b000041c 0xa7467f3ff000000c

def z859 : W := mkw 0x00f6ad0003b6a800 0x3effff0003fffc00

def z860 : W := mkw 0x24f7eda003b6f940 0x3effff3003fffc70

def z861 : W := mkw 0x343eaf4f54ffaaa5 0x043e0f0fc0ff0000

def z862 : W := mkw 0x47fffefdbf00555a 0x3fffffffff001ff0

def z863 : W := mkw 0x24f7ed0003b6f940 0x3effff0003fffff0

def z864 : W := mkw 0x47fffefdbc000418 0xffffffffff00ffff

def z865 : W := mkw 0x0800010240c38f7e 0xc800000001c79fff

def z866 : W := mkw 0x0024000240650220 0x2d7e003fc1ff0270

def z867 : W := mkw 0x66f7ed000fb6f800 0x3effff000ffffc00

def z868 : W := mkw 0x47fffefdbf000140 0x37fffffffe000180

def z869 : W := mkw 0x1000010240fda2a5 0xc800000002ffe38f

def z870 : W := mkw 0x47dbfefdbc000000 0x33c1fffffc000000

def z871 : W := mkw 0x102c004b436d03e0 0x2d7e003fc3ff03f0

def z872 : W := mkw 0x09023614f0030c38 0xaf467f3ff1079e7c

def z873 : W := mkw 0x47ffeeed9c000000 0x37bf8fcffc000000

def z874 : W := mkw 0x47fffefdbf000558 0xbfffffffff009ffc

def z875 : W := mkw 0x67fffefdbc342000 0x37fffffffc380000

def z876 : W := mkw 0x47febefdbc000000 0x35fe0ffffc000000

def z877 : W := mkw 0x03ef76fdb8000000 0x37fffffffc000000

def z878 : W := mkw 0x0102260490000000 0x25460f3fc0000000

def z879 : W := mkw 0x47fffefdbc000418 0x37fffffffd001c70

def z880 : W := mkw 0x00188b4e14d8a285 0xffff8ffffef8e38f

def z881 : W := mkw 0x41188a4d94000000 0x04380f0fc0000000

def z882 : W := mkw 0x10ec00eb436d03e0 0xfdfe00ffc3ffe3ff

def z883 : W := mkw 0x47fffefdbc000005 0xf7fffffffc00000f

def z884 : W := mkw 0x10ec00eb436d03e5 0xfdfe00ffc3ff03ff

def z885 : W := mkw 0x43cb76fdbf00555a 0xffc7ffffff00ffff

def z886 : W := mkw 0x10c001a243fda3e5 0xfbc180f03fffe3ff

def z887 : W := mkw 0x47fffefdbf24555a 0xffffffffffffffff

def z888 : W := mkw 0x09023716f0c38e3c 0xbfc7fffffdc79e7c

def z889 : W := mkw 0x0008034e10c88284 0xffb98fce3ef8e38f

def z890 : W := mkw 0x09023614f0030c38 0x04467f3fc1071c70

def z891 : W := mkw 0x24f7eda003b6f940 0xfffffff03fffffff

def z892 : W := mkw 0x12fdc8e90f3c71c3 0x50b980c00e386183

def z893 : W := mkw 0x0800010240dbaaa5 0xc800000002ffe38f

def z894 : W := mkw 0x0000000240410220 0x3dfe003fc3ff0270

def z895 : W := mkw 0x45fffe5db4000000 0x37ffff3ff0000000

def z896 : W := mkw 0x09023716f0c38e3c 0xbffe7f3ff3ff9e7c

def z897 : W := mkw 0x1000010243fda3e0 0x0800000003ffe3f0

def z898 : W := mkw 0x1000010243fda3e5 0x0800000003ff03f0

def z899 : W := mkw 0x47fffefdbc102000 0x37fffffffe386000

def z900 : W := mkw 0x2000010243f7fa20 0x0800000003fffe70

def z901 : W := mkw 0x5b0812fffc4907fc 0x810000fffc0003fc

def z902 : W := mkw 0x091abc58e41b2cb9 0x50fff0f1cf3f7df3

def z903 : W := mkw 0x00e7650003a6d800 0x3effff0003fffc00

def z904 : W := mkw 0x2437ed0000b6f800 0x2e7fff0001fffc00

def z905 : W := mkw 0x01023616f0410638 0xaf467f3ff1c79e7c

def z906 : W := mkw 0x24f7ed0003b6f800 0x3fffffc03ffffc00

def z907 : W := mkw 0x00188b4e14d8a285 0xdab98fc03ef8e38f

def z908 : W := mkw 0x471bfefdbc00555a 0xc301fffffc00ffff

def z909 : W := mkw 0x0800111260c38e3c 0x8840703001c79e7c

def z910 : W := mkw 0x57fffefdbc0801c0 0x37fffffffc000180

def z911 : W := mkw 0x003c8a4d14000000 0x37bf8fcffc000000

def z912 : W := mkw 0x47f7fe14bc000000 0x37ffff3ffc000000

def z913 : W := mkw 0x09023716f0c38e3c 0x85467f3ff1c71e7c

def z914 : W := mkw 0x24f7ed0003b6f800 0x2e7e7f0001ff9c00

def z915 : W := mkw 0x43189afdbc000000 0x05380ffffc000000

def z916 : W := mkw 0x00f5c90003b4f000 0x3effff0003fffc00

def z917 : W := mkw 0x02c150b02b00555a 0xc341f0f03d00ffff

def z918 : W := mkw 0x67fffefdbc107000 0x37fffffffc006000

def z919 : W := mkw 0x0800010240dbaaa5 0x0000000000ff0000

def z920 : W := mkw 0x431abefdbc000000 0x37fffffffc000000

def z921 : W := mkw 0x01023714b0828c18 0xaf467f3ff1c79e7c

def z922 : W := mkw 0x0908125ef04906bc 0x810000fff00003fc

def z923 : W := mkw 0x0102260490000000 0x26467f0fc0000000

def z924 : W := mkw 0x102c004b406d02a0 0x053e003fc0ff0270

def z925 : W := mkw 0x1000010240fda2a5 0x0000000000ff0000

def z926 : W := mkw 0x453eae4d94000000 0x14bf8fcfcc000000

def z927 : W := mkw 0x47fffefdbf000000 0x3fffffffff000000

def z928 : W := mkw 0x1000010243ed83e4 0x8800000003ff83fc

def z929 : W := mkw 0x471bfe5dbc000000 0x0201ff0ffc000000

def z930 : W := mkw 0x57fffefdbf2c55da 0xffffffffff38ffff

def z931 : W := mkw 0x56fdc8e90f2c51c2 0x50b980c00e386183

def z932 : W := mkw 0x01023614b0000000 0x04467f3fc0000000

def z933 : W := mkw 0x1be774b1eb275d7a 0x00467031c1071c70

def z934 : W := mkw 0x09023716f0c38e3c 0xbfc67ffff3c79ffc

def z935 : W := mkw 0x00ec00eb404902a0 0x3dfe00ffc3ff03f0

def z936 : W := mkw 0x003c8a4d14000000 0x043e0f0fc0000000

def z937 : W := mkw 0x10ec00eb436d03e0 0x35fe00ffc1ff0070

def z938 : W := mkw 0x473fee4d9c000000 0x043f8f0fcc000000

def z939 : W := mkw 0x000010102300555a 0xfbc1f0f03f00ffff

def z940 : W := mkw 0x2436ad0003b6f800 0x2e7e7f0003fffc00

def z941 : W := mkw 0x2800010240f7aa24 0x0000000000ff0000

def z942 : W := mkw 0x25e77614b3265800 0x27467f3ff1071c00

def z943 : W := mkw 0x102c00eb406d03e0 0x3dbe00ffc2ff03f0

def z944 : W := mkw 0x46ffece90c000000 0x37ffffffcc000000

def z945 : W := mkw 0x00188aed14000000 0x37b98ffffc000000

def z946 : W := mkw 0x00188b4c1498a085 0xfbb98fc03e38e38f

def z947 : W := mkw 0x0800010240c38e3c 0xa940003001c79e7c

def z948 : W := mkw 0x0908125ef44906bd 0x8100003ff000027c

def z949 : W := mkw 0x2800010240f7ae3c 0x8800000001ff9e7c

def z950 : W := mkw 0x10ec00eb436d03e0 0x7dff80ffcfff63f3

def z951 : W := mkw 0x120812ff7c4907ff 0xc10000fffc0003ff

def z952 : W := mkw 0x0002250000828800 0x3efe7f0003ff9c00

def z953 : W := mkw 0x00c010b023000558 0xfbc1f0f03f00ffff

def z954 : W := mkw 0x09023716f0c38e3c 0x86467f3ff1c79c7c

def z955 : W := mkw 0x2012ad0003b6f800 0x3effff0003fffc00

def z956 : W := mkw 0x020150102800541a 0xfbc1f0f03f00ffff

def z957 : W := mkw 0x47ffeeed9c000000 0x35ff8fffcc000000

def z958 : W := mkw 0x0000131670c1863c 0xaf467f3ff1c79e7c

def z959 : W := mkw 0x02c150b02b00555a 0xffc7f0ffff00ffff

def z960 : W := mkw 0x1000010240d9a3e5 0xc800000002f8e3ff

def z961 : W := mkw 0x47fffefdbc080081 0x77fffffffc000183

def z962 : W := mkw 0x47fffefdbc000000 0x3ffffffffd009c00

def z963 : W := mkw 0x00188b4e14d8a285 0xffff8fce3fffe38f

def z964 : W := mkw 0x47fffefdbc000418 0xb7fffffffc00027c

def z965 : W := mkw 0x0000020410000000 0x27460f3ff0000000

def z966 : W := mkw 0x0800010240c38e3c 0x0000000001c71c70

def z967 : W := mkw 0x24f7ed0003b6f800 0xfeffff0003ffff8f

def z968 : W := mkw 0x10ec00eb436d03e0 0x3fff80ffffff03f0

def z969 : W := mkw 0x04f7ec0003245000 0x3effff0003fffc00

def z970 : W := mkw 0x01c37614b3005000 0x3fc7ff3ff300fc00

def z971 : W := mkw 0x47fffefdbf240140 0x3fffffffffff03f0

def z972 : W := mkw 0x530812fffc4907fa 0xc10000fffc0003ff

def z973 : W := mkw 0x0800010243e78e3c 0x8800000003ff9e7c

def z974 : W := mkw 0x030236b4b8000000 0x27467ffffc000000

def z975 : W := mkw 0x08e4010243e78e3c 0xbcfe000003ff9e7c

def z976 : W := mkw 0x01023614b0000418 0x27467f3ff1001c70

def z977 : W := mkw 0x09023716f0dbaebd 0xffc7ffffffffffff

def z978 : W := mkw 0x10ec00eb436d03e0 0xbffe00fff3ff83fc

def z979 : W := mkw 0x473ebefdbc000000 0x043e0f3fc0000000

def z980 : W := mkw 0x28c1511263f7fe3c 0xbbc1f03033fffe7c

def z981 : W := mkw 0x01023614b0000000 0x37c7fffffc000000

def z982 : W := mkw 0x473ffe5dbc000000 0x043e7f0fc0000000

def z983 : W := mkw 0x08188b4e54dbaaa5 0xffb98fce3effe38f

def z984 : W := mkw 0x45263615b0000000 0x27467f3ff0000000

def z985 : W := mkw 0x67fffefdbc260800 0x37fffffffc070000

def z986 : W := mkw 0x10ec00eb436d03e0 0x0c7e003fc3ff03f0

def z987 : W := mkw 0x45feaeed97000140 0x3dfe0fffc30003f0

def z988 : W := mkw 0x47fffefdbc000000 0x0347fffffc000000

def z989 : W := mkw 0x01023614b0000418 0xa7467f3ff0009c0c

def z990 : W := mkw 0x4713fe14bc000000 0x0607ff0ffc000000

def z991 : W := mkw 0x4b023716fcc38e3c 0xaf467f3ffdc79e7c

def z992 : W := mkw 0x12c151b26bfdf7ff 0xfbc1f0f03fffffff

def z993 : W := mkw 0x3000010243fffbe5 0xc800000003ffffff

def z994 : W := mkw 0x45ffee4d97005000 0x3effff0fc300fc00

def z995 : W := mkw 0x47ffeeed9c000000 0x36ffffcfcc000000

def z996 : W := mkw 0x0912bf14b492ac1d 0x82007f0030009c0c

def z997 : W := mkw 0x01023614b300555a 0xef467f3ff300ffff

def z998 : W := mkw 0x2800010240d3fe3c 0x8800000001c7fe7c

def z999 : W := mkw 0x10ec00eb436d03e0 0x3cfe003fc3ff0070

def z1000 : W := mkw 0x2d13ff14b492fc1d 0xc201ff003c00fc0f

def z1001 : W := mkw 0x47fffefdbf00555a 0xf7fffffffe00fd8f

def z1002 : W := mkw 0x3000010243fffaa0 0x0800000003fffc00

def z1003 : W := mkw 0x47fffefdbc00555a 0xf7fffffffc00ffff

def z1004 : W := mkw 0x47fffefdbc000000 0x35fe7fffc0000000

def z1005 : W := mkw 0x10ec00eb436d03e0 0x057e00ffc1ff03f0

def z1006 : W := mkw 0x47fffefdbc000000 0xf7fffffffc00038f

def z1007 : W := mkw 0x00188b4e14d8a285 0xd3b98fce3e38e38f

def z1008 : W := mkw 0x47d3feb4bc000000 0x37c7fffffc000000

def z1009 : W := mkw 0x09023716f0c38e3c 0x83467f3ff1079e7c

def z1010 : W := mkw 0x11ee36fdb32c01c0 0x37fe7ffff2380180

def z1011 : W := mkw 0x43ee36fdbc000000 0x37fe7ffffc000000

def z1012 : W := mkw 0x47fffefdbf240000 0x37fffffffd070000

def z1013 : W := mkw 0x47fffefdbf00555a 0x3fffffffff00fc70

def z1014 : W := mkw 0x03dbfefcbc000000 0x37fffffffc000000

def z1015 : W := mkw 0x47ffeeed9c000000 0x043e0f0fc0000000

def z1016 : W := mkw 0x1800010243ef8be4 0x0800000003ff03f0

def z1017 : W := mkw 0x09023716f0c38e3c 0x27467f3ff1c71c70

def z1018 : W := mkw 0x0000010240c38a20 0x0800000001c79e70

def z1019 : W := mkw 0x0800010240c38e3c 0x8000000000c79c0c

def z1020 : W := mkw 0x12ec00eb4b6d03e2 0x7dfe00ffcfff03f3

def z1021 : W := mkw 0x0010890200d8a285 0xffb98fc03ef8e38f

def z1022 : W := mkw 0x47fffefdbf00555a 0x047e7f3fc1001c70

def z1023 : W := mkw 0x10fc89eb47fda3e5 0xd8b980c00fffe3ff

def z1024 : W := mkw 0x0ac141a24bc3df7e 0xd88180c00fc7ffff

def z1025 : W := mkw 0x453eae4d94182081 0x54bf8fcfce386183

def z1026 : W := mkw 0x102c00eb406d03e0 0x043e003fc0ff0070

def z1027 : W := mkw 0x410a264d94000000 0x04060f0fc0000000

def z1028 : W := mkw 0x34f7eda103b6f940 0x3effff0003fffc00

def z1029 : W := mkw 0x57fffefdbf240140 0x37fffffffc000000

def z1030 : W := mkw 0x47ef76fdb8000000 0x37fe7ffff0000000

def z1031 : W := mkw 0x00fc8aed14000000 0x35fe0fffc0000000

def z1032 : W := mkw 0x0800010240c38e3c 0x8000000000c7027c

def z1033 : W := mkw 0x0536be14b0000000 0x277e7f3ff0000000

def z1034 : W := mkw 0x451aae4d94000000 0x00000f0fc0000000

def z1035 : W := mkw 0x01febefdb4000000 0x37fffffffc000000

def z1036 : W := mkw 0x24f7ed0003b6f800 0x16bfff0002fffc00

def z1037 : W := mkw 0x67fffefdbf347142 0x77fffffffe386183

def z1038 : W := mkw 0x4b0812fffc4906bd 0xc10000fffc0003ff

def z1039 : W := mkw 0x10ec00eb476d03e1 0x7dfe00ffcfff03f3

def z1040 : W := mkw 0x47fffefdbc000140 0x37fffffffc0003f0

def z1041 : W := mkw 0x0800010240dbaebd 0x8800000001ff9e7c

def z1042 : W := mkw 0x47fffefdbf00555a 0x77ffffffff007df3

def z1043 : W := mkw 0x01e636b5b0000000 0x27467f3ff0000000

def z1044 : W := mkw 0x57fffefdbf3c21c1 0x77fffffffe386183

def z1045 : W := mkw 0x453eaeed94000000 0x053e0fffc0000000

def z1046 : W := mkw 0x2f13ff14b892fc1e 0xc201ff003c00fc0f

def z1047 : W := mkw 0x66f7eda10bb6f800 0x3effff0003fffc00

def z1048 : W := mkw 0x0800010240c38e3c 0xaa40700001c79e7c

def z1049 : W := mkw 0x34ffece9033c71c0 0x37ffffffc2386180

def z1050 : W := mkw 0x47fffefdbc000000 0xbffffffffc00820c

def z1051 : W := mkw 0x24f7ed0007b6f801 0x7effff000ffffc03

def z1052 : W := mkw 0x430a36fdbc000000 0x05060ffffc000000

def z1053 : W := mkw 0x67e774b1ab265d5a 0x00467031c1071c70

def z1054 : W := mkw 0x32c151b26bfffffa 0xfbc1f0f03fffffff

def z1055 : W := mkw 0x47fffefdbf00541a 0xffffffffff00fc0f

def z1056 : W := mkw 0x47fffefdbc000000 0x067fff3ffc000000

def z1057 : W := mkw 0x02c150b02b00555a 0xffc7f0f03fc7ffff

def z1058 : W := mkw 0x0012ad000092a800 0x2e7e7f0001ff9c00

def z1059 : W := mkw 0x02c150b02b24555a 0xfbc1f0f03fffffff

def z1060 : W := mkw 0x2436ad0000b6a800 0x047e7f0001ff1c00

def z1061 : W := mkw 0x10e40002436d03e0 0x3dfe003fc3ff03f0

def z1062 : W := mkw 0x0802250240c38e3c 0xaf467f3fc1c79e7c

def z1063 : W := mkw 0x05f7fe14b3005418 0xbfffff3ff300fe7c

def z1064 : W := mkw 0x47fffefdbc020800 0x37fffffffd071c00

def z1065 : W := mkw 0x0026250000a68800 0x2e7e7f0001ff9c00

def z1066 : W := mkw 0x553eae4d942c0080 0x043e0f0fc0380000

def z1067 : W := mkw 0x453ebe5db4000000 0x37fffffffc000000

def z1068 : W := mkw 0x65ffee4d97347000 0x14bf8f0fc2386000

def z1069 : W := mkw 0x47fffefdbc182081 0xfffffffffe38e38f

def z1070 : W := mkw 0x430a36fdbc00055a 0xef467ffffd009fff

def z1071 : W := mkw 0x45feaeed94000000 0x14be0fcfc0000000

def z1072 : W := mkw 0x47e776b5bb00555a 0xaf467f3ff1009e7c

def z1073 : W := mkw 0x04ffec4900000000 0x36ffff0fc0000000

def z1074 : W := mkw 0x02e550b02b24555a 0xfbc7f0f03f07ffff

def z1075 : W := mkw 0x09023716f0dbaebd 0xaf467f3ff1ff9e7c

def z1076 : W := mkw 0x09023616f0430e38 0x2f467f3ff1c71e70

def z1077 : W := mkw 0x473ffe5dbc000000 0x277fff3ffc000000

def z1078 : W := mkw 0x00c140000300555a 0xfbc1f0c03f00ffff

def z1079 : W := mkw 0x47fffefdbc000000 0x13b9fffffc000000

def z1080 : W := mkw 0x01023614b0020800 0x27467f3ff1071c00

def z1081 : W := mkw 0x47fffefdbc182081 0x37fffffffc380000

def z1082 : W := mkw 0x09023714f0838c38 0x2f467f3ff1c79c70

def z1083 : W := mkw 0x00188b4e14d8a285 0xd5b98fce3ef8638f

def z1084 : W := mkw 0x1908125ff04906bc 0x8100003ff000027c

def z1085 : W := mkw 0x26e550b02b24555a 0xfbc1f0f03f00ffff

def z1086 : W := mkw 0x01c37614b0000000 0x37c7ff3ff0000000

def z1087 : W := mkw 0x10fc8aed173c21c1 0x77ff8ffffe386183

def z1088 : W := mkw 0x06fffcf92b00555a 0xffffffffff00ffff

def z1089 : W := mkw 0x24f7ed0003b6f800 0x3cfe7f0003ff1c00

def z1090 : W := mkw 0x47f7feb5b8000000 0x37ffff3ff0000000

def z1091 : W := mkw 0x011abe5cb4000000 0x277e7f3ff0000000

def z1092 : W := mkw 0x453eae4d94000000 0x35be0fcfc0000000

def z1093 : W := mkw 0x47fffefdbc000000 0x3ffffffffd000270

def z1094 : W := mkw 0x47fddafdbc000000 0x37b98ffffc000000

def z1095 : W := mkw 0x04f7ed0003a68800 0x3effff0003ff9c00

def z1096 : W := mkw 0x26f7ed000bb6f802 0x7effff000ffffc03

def z1097 : W := mkw 0x24f7ed0003b6f800 0x067fff0001fffc00

def z1098 : W := mkw 0x4f13ff14bc92ac1d 0xc201ff003c00fc0f

def z1099 : W := mkw 0x30c141a243fffbe0 0x3bc1f0f003fffff0

def z1100 : W := mkw 0x00188b4c1498a085 0xf7b98fce3e38e18f

def z1101 : W := mkw 0x10e400a343650360 0x3dfe003fc3ff0270

def z1102 : W := mkw 0x20e6250003b6f800 0x3efe7f0003fffc00

def z1103 : W := mkw 0x01023614b0000418 0xa7467f3ff000027c

def z1104 : W := mkw 0x020010b02800055a 0xfbc1f0f03f00ffff

def z1105 : W := mkw 0x00fc8aed17000140 0xffff8fffff00e3ff

def z1106 : W := mkw 0x2800010243f7ff7e 0xc800000003ffffff

def z1107 : W := mkw 0x47fffe5dbc000000 0x36ffff0ffc000000

def z1108 : W := mkw 0x0800111260c38e3c 0x8900003031c79e7c

def z1109 : W := mkw 0x47dbfefdbf00555a 0xfbc1ffffff00ffff

def z1110 : W := mkw 0x00188b4e54d9a2a5 0xffbf8fcffeffe38f

def z1111 : W := mkw 0x05f7ee0490000000 0x36ffff0fc0000000

def z1112 : W := mkw 0x67fffefdbf34755a 0xffffffffff38ffff

def z1113 : W := mkw 0x24f7ed0003b6f800 0xbfffff0033fffe0c

def z1114 : W := mkw 0x66fdc8e90f347142 0x50b980c00e386183

def z1115 : W := mkw 0x190812fff44907fd 0xc10000fffc0003ff

def z1116 : W := mkw 0x47fffefdbc080080 0x37fffffffe380180

def z1117 : W := mkw 0x10ec00eb406d02a0 0x3dfe00ffc1ff0270

def z1118 : W := mkw 0x00ec004a436d02a0 0x3dfe00ffc3ff03f0

def z1119 : W := mkw 0x18ec01eb43ef8ffc 0x98b800c003ff9ffc

def z1120 : W := mkw 0x12ed40eb4b6d53e2 0x7ffff0ffcffffff3

def z1121 : W := mkw 0x47fffefdbf005142 0x7fffffffff00fd83

def z1122 : W := mkw 0x34fdc8e9073c71c1 0x50b980c00e386183

def z1123 : W := mkw 0x47fffefdbf00555a 0xf7fffffffe0063ff

def z1124 : W := mkw 0x100800eb404903e0 0x3dfe00ffc3ff03f0

def z1125 : W := mkw 0x10ed40eb436d53e0 0x3dff80ffc3ff63f0

def z1126 : W := mkw 0x07f7feb4bb00555a 0xffffffffff00ffff

def z1127 : W := mkw 0x47e776b5b8000000 0x37c7fffffc000000

def z1128 : W := mkw 0x00108b041490a005 0xffb98fc03ef8e38f

def z1129 : W := mkw 0x24f7ed0003b6f800 0xfeffff003ffffc0f

def z1130 : W := mkw 0x011abe5cb4000418 0xffffffffff00ffff

def z1131 : W := mkw 0x012e365db0000000 0x277e7f3ff0000000

def z1132 : W := mkw 0x47fffefdbc005002 0x77fffffffc006003

def z1133 : W := mkw 0x09023716f0c38e3c 0x8c467f3fc1c79e7c

def z1134 : W := mkw 0x43c150b1ab00555a 0xfbc1f0f1ff00ffff

def z1135 : W := mkw 0x47fffefdbc000000 0x3ffffffffdc70000

def z1136 : W := mkw 0x00ec00eb43650220 0x3dfe00ffc3ff0270

def z1137 : W := mkw 0x46fdcaed1c000000 0x37ff8ffffc000000

def z1138 : W := mkw 0x01023614b0000000 0xffc7fffffe00e38f

def z1139 : W := mkw 0x09023512e0c38e38 0x2f467f3fc1c79e70

def z1140 : W := mkw 0x01c236b4b3000140 0x3fc67ffff30003f0

def z1141 : W := mkw 0x0536ae0490000000 0x043e0f0fc0000000

def z1142 : W := mkw 0x0b0812fefc4907ff 0xc10000fffc0003ff

def z1143 : W := mkw 0x02c150b02b00555a 0xfff9f0f03ff8ffff

def z1144 : W := mkw 0x02c150b02800555a 0xf3c1f0f03c00ffff

def z1145 : W := mkw 0x453eae4d94000000 0x063f8f0ffc000000

def z1146 : W := mkw 0x47fffefdbf005142 0x37fffffffc000000

def z1147 : W := mkw 0x47fffefdbc000000 0xf7fffffffc00e00f

def z1148 : W := mkw 0x453ebe5db4000418 0xaf7e7f3ff1009e7c

def z1149 : W := mkw 0x43189afdbc000000 0x03018ffffc000000

def z1150 : W := mkw 0x0800010240c38e3c 0xfb8180c03fc7ffff

def z1151 : W := mkw 0x0800010240cb8ebc 0x8800000003ff9ffc

def z1152 : W := mkw 0x09023512e0c38e3c 0x8800700001c79e7c

def z1153 : W := mkw 0x1ac151b26befdffe 0xfbc1f0f03fffffff

def z1154 : W := mkw 0x01e63614b3240000 0x3ffe7f3ff3ff0000

def z1155 : W := mkw 0x09023614b0020c18 0x27467f3ff0001c00

def z1156 : W := mkw 0x00ec02ed10000000 0x37fe0ffff0000000

def z1157 : W := mkw 0x0112be14b4000000 0x2747ff3ffc000000

def z1158 : W := mkw 0x453ebe5db4000000 0x053e0f3ff0000000

def z1159 : W := mkw 0x10ed40eb436d03e0 0x3ffff0ffc3ff03f0

def z1160 : W := mkw 0x410a365db4000000 0x27467f3ff0000000

def z1161 : W := mkw 0x01023614b0000000 0x2f467f3ff1c70000

def z1162 : W := mkw 0x05e77614b0000000 0x27467f3ff0000000

def z1163 : W := mkw 0x01023614b0000000 0x06067f0ff0000000

def z1164 : W := mkw 0x09023716f0c38e3c 0xbfc7ff3ff3c7fe7c

def z1165 : W := mkw 0x67fffefdbf265d5a 0x37fffffffd071c70

def z1166 : W := mkw 0x453eae4d94240000 0x043e0f0fc0ff0000

def z1167 : W := mkw 0x02e550b02b00555a 0xfffff0f03f00ffff

def z1168 : W := mkw 0x2ce7650243e7de3c 0x8846700001c79e7c

def z1169 : W := mkw 0x1b0812fff84907fe 0xc10000fffc0003ff

def z1170 : W := mkw 0x02e550b02b24555a 0xfbf9f0f03f38ffff

def z1171 : W := mkw 0x45feaeed94000000 0x37ff8ffffc000000

def z1172 : W := mkw 0x43d9dafdbc000000 0x37f9fffffc000000

def z1173 : W := mkw 0x2fe774b0eb275d7a 0x00467031c1071c70

def z1174 : W := mkw 0x08c1410243c3de3c 0xbac1f00003c7fe7c

def z1175 : W := mkw 0x26f7eda00bb6f942 0x3effff0003fffc00

def z1176 : W := mkw 0x45ffee4d94000000 0x37ffffcffc000000

def z1177 : W := mkw 0x020150b02800555a 0xeb41f0f03d00ffff

def z1178 : W := mkw 0x43023614bc000000 0x27467f3ffc000000

def z1179 : W := mkw 0x00188b4e14d8a285 0xfff98ffe3ff8e3ff

def z1180 : W := mkw 0x36fdc8e90b3c71c2 0x50b980c00e386183

def z1181 : W := mkw 0x030236b4b800055a 0xe7467ffffc0003ff

def z1182 : W := mkw 0x47d3feb4bf00555a 0xffc7ffffff00ffff

def z1183 : W := mkw 0x10ec00eb436d03e0 0x14fe00ffc3ff01f0

def z1184 : W := mkw 0x09023716f0c38e3c 0xef467ffffdc79fff

def z1185 : W := mkw 0x24f7eda103b6f800 0x3effff31c3fffc00

def z1186 : W := mkw 0x0a0011b268c38f7e 0xc90000f03dc79fff

def z1187 : W := mkw 0x471bfefdbc000000 0x2747fffffc000000

def z1188 : W := mkw 0x2d3eaf4ed4ffaaa5 0x043e0f0fc0ff0000

def z1189 : W := mkw 0x0800010240c1863c 0x8800000000c0827c

def z1190 : W := mkw 0x011aae4c94000000 0x37bf8fcffc000000

def z1191 : W := mkw 0x0513fe14b0000000 0x2747ff3ff0000000

def z1192 : W := mkw 0x0800010240cb8ebd 0xc800000001c79fff

def z1193 : W := mkw 0x043eac4900000000 0x043e0f0fc0000000

def z1194 : W := mkw 0x00188a4c14000000 0x37ff8ffffc000000

def z1195 : W := mkw 0x2413ed000092f800 0x3effff0003fffc00

def z1196 : W := mkw 0x02c150b02b00555a 0xd381f0f03e00ffff

def z1197 : W := mkw 0x4ffffefdbc00041c 0xb7fffffffc00000c

def z1198 : W := mkw 0x01023716f0c38a20 0x2f467f3ff1c79e70

def z1199 : W := mkw 0x0102260490000000 0x27060f0ff0000000

def z1200 : W := mkw 0x47037614b8000000 0x27467f3ff0000000

def z1201 : W := mkw 0x26f7eda00bb6f800 0x3effffc00ffffc00

def z1202 : W := mkw 0x2d12bf14b092ac1c 0x82007f0030009c0c

def z1203 : W := mkw 0x09188b4ed4d9a2a5 0xffb98fcffef8e38f

def z1204 : W := mkw 0x04ffece903005140 0x3fffffffc300fff0

def z1205 : W := mkw 0x00188b4c1498a085 0xfeb98fc03ef8e18f

def z1206 : W := mkw 0x0112be14b0000000 0x37ffff3ff0000000

def z1207 : W := mkw 0x0802250240c38e3c 0x8846700001c79e7c

def z1208 : W := mkw 0x24f7ed0000b6f800 0x36ffff0000fffc00

def z1209 : W := mkw 0x3000010240ffaaa0 0x0000000000ff0000

def z1210 : W := mkw 0x471bfefdbc000000 0x37b9fffffc000000

def z1211 : W := mkw 0x01023614b0000000 0x05060f3ff0000000

def z1212 : W := mkw 0x01189a5cb4000000 0x37b98ffffc000000

def z1213 : W := mkw 0x12ed40eb4b6d53e2 0x3dfe00ffc3ff03f0

def z1214 : W := mkw 0x0800010240c38e3c 0x8000000000009e7c

def z1215 : W := mkw 0x26f7eda00bb6f942 0xffffffc03fffff8f

def z1216 : W := mkw 0x09023716f0cb8ebc 0xaf467f3ff3ff9ffc

def z1217 : W := mkw 0x01001214b0000000 0x27000f3ff0000000

def z1218 : W := mkw 0x001889480498a081 0xffb98fc03ef8e38f

def z1219 : W := mkw 0x09023716f0c38e3c 0x2d467f3fc1c71e70

def z1220 : W := mkw 0x0800010243c3de3c 0x8800000003c7fe7c

def z1221 : W := mkw 0x47fffefdbf000140 0x37fffffffd000070

def z1222 : W := mkw 0x12ed40eb4b6d53e2 0xffff80ffffffe3ff

def z1223 : W := mkw 0x4d3eaf4fd4dbaaa5 0x043e0f0fc0ff0000

def z1224 : W := mkw 0x471abefdbc000000 0x01000ffffc000000

def z1225 : W := mkw 0x020150b02b00555a 0xcb01f0f03f00ffff

def z1226 : W := mkw 0x02fddafd3f00555a 0xffffffffff00ffff

def z1227 : W := mkw 0x45febefdb4000000 0x37fe7ffff0000000

def z1228 : W := mkw 0x10ec00e943250160 0x3dfe00ffc3ff0070

def z1229 : W := mkw 0x0800111260c38e3c 0x8a00700031c79e7c

def z1230 : W := mkw 0x47fffefdbf005142 0xfffffffffe00e38f

def z1231 : W := mkw 0x00108b0610d0a204 0xffb98fce3ef8e38f

def z1232 : W := mkw 0x10188b4f54d9a2a5 0xffb98fcffef8e38f

def z1233 : W := mkw 0x01023614b0000000 0x2f467f3ff1009c00

def z1234 : W := mkw 0x1800010240ef8ebc 0x8800000001ff9e7c

def z1235 : W := mkw 0x77fffefdbf3c71c0 0x37fffffffe386180

def z1236 : W := mkw 0x0b13ff14bc92fc1f 0xc201ff003c00fc0f

def z1237 : W := mkw 0x03037614b8000000 0x2747ff3ffc000000

def z1238 : W := mkw 0x0ac151b268c38e3c 0xbbc1f0f03dc79e7c

def z1239 : W := mkw 0x02e550b12b00555a 0xfbc7f0f1ff00ffff

def z1240 : W := mkw 0x47fffefdbc000000 0x277e7f3ff0000000

def z1241 : W := mkw 0x1800010243e78f7c 0x8800000001c79e7c

def z1242 : W := mkw 0x47fffefdbc00541a 0xfffffffffd00fe7f

def z1243 : W := mkw 0x09023716f0cb8ebd 0xef467f3ff1c79fff

def z1244 : W := mkw 0x67fffefdbf265d5a 0xffffffffff07ffff

def z1245 : W := mkw 0x010a36fdb0000000 0x27467ffff0000000

def z1246 : W := mkw 0x3000010243ffabe0 0x0800000003ff03f0

def z1247 : W := mkw 0x47fffcf9a8000000 0x37ffffffc0000000

def z1248 : W := mkw 0x2436ad0000b6a800 0x3effff0003fffc00

def z1249 : W := mkw 0x47fffefdbf00555a 0xbffffffffd009e7c

def z1250 : W := mkw 0x00c800ea434903e0 0x3dfe00ffc3ff03f0

def z1251 : W := mkw 0x20ec01e903b6f800 0x3dfe00ffc3fffc00

def z1252 : W := mkw 0x47fffefdbf240000 0x37fffffffe380000

def z1253 : W := mkw 0x47ffeeed9f005142 0x54bf8fcfce006183

def z1254 : W := mkw 0x4713fe14bc000000 0x0301ff3ffc000000

def z1255 : W := mkw 0x1008004a436d03e0 0x3dfe00ffc3ff03f0

def z1256 : W := mkw 0x24f6ad0003b6a800 0x3efe7f0003ff9c00

def z1257 : W := mkw 0x01e63614b0000000 0x37fe7f3ff0000000

def z1258 : W := mkw 0x47fffefdbf1871c3 0x77fffffffe386183

def z1259 : W := mkw 0x03ef76fdbb00555a 0xffffffffff00ffff

def z1260 : W := mkw 0x09023716f0c38e3c 0x2e467f3fc1c79c70

def z1261 : W := mkw 0x1000010243fdf7ff 0xc800000003ffffff

def z1262 : W := mkw 0x102c004b406d02a0 0x3dfe00ffc3ff03f0

def z1263 : W := mkw 0x67fffefdbf265800 0x3fffffffffff1c00

def z1264 : W := mkw 0x102c00eb406d03e0 0x2d7e00ffc1ff03f0

def z1265 : W := mkw 0x47fffefdbc00041a 0xf7fffffffc00000f

def z1266 : W := mkw 0x102c00eb436d03e0 0x0d3e00ffc3ff03f0

def z1267 : W := mkw 0x473eaeed9c000000 0x043e0fcfcc000000

def z1268 : W := mkw 0x01023614b0000000 0x2f467f3ff1000270

def z1269 : W := mkw 0x47fffefdbf005142 0x7fffffffff0063f3

def z1270 : W := mkw 0x653eae4d94342000 0x043e0f0fc0380000

def z1271 : W := mkw 0x0ac151b26bdbffff 0xfbc1f0f03fffffff

def z1272 : W := mkw 0x012e264d90000000 0x043e0f0fc0000000

def z1273 : W := mkw 0x10ec00eb436d03e0 0xfdfe00ffffff03ff

def z1274 : W := mkw 0x0800010240c38e3c 0xab00000031c79e7c

def z1275 : W := mkw 0x67fffefdbf245000 0x37fffffffc000000

def z1276 : W := mkw 0x2437ed0000b6f800 0x043e7f0000ff1c00

def z1277 : W := mkw 0x47f7feb5bc000000 0x2747ff3ffc000000

def z1278 : W := mkw 0x24f7ed0003b6f942 0x7effff0003fffd83

def z1279 : W := mkw 0x14f7ec02436d03e0 0x3effff0003ff03f0

def z1280 : W := mkw 0x47fffefdbf245000 0x3ffffffffffffc00

def z1281 : W := mkw 0x47fffefdbf00555a 0xf7fffffffd001fff

def z1282 : W := mkw 0x03c376b4bb00555a 0x27467f3ff1001c70

def z1283 : W := mkw 0x24f7ec0003265800 0x3effff0003ff1c00

def z1284 : W := mkw 0x0800010240d3ae3c 0x8800000003fffe7c

def z1285 : W := mkw 0x65ffee4d97265800 0x047e7f0fc1071c00

def z1286 : W := mkw 0x1000010243ef8be0 0x0800000003ff9ff0

def z1287 : W := mkw 0x12e550b12b24555a 0xfbc1f0f03f00ffff

def z1288 : W := mkw 0x47fffefdbf000140 0xffffffffff00e3ff

def z1289 : W := mkw 0x2800010243f7fa24 0x0800000003fffc00

def z1290 : W := mkw 0x1800010243ffaffd 0xc800000003ffffff

def z1291 : W := mkw 0x10ec00eb436d03e0 0x3fff80ffc3ffe3f0

def z1292 : W := mkw 0x0008004a404902a0 0x2d7e003fc1ff0270

def z1293 : W := mkw 0x47ef76fdbc000000 0x27467ffffc000000

def z1294 : W := mkw 0x453ebe5db4000000 0x063e7f0ff0000000

def z1295 : W := mkw 0x47fffefdbc00055a 0xfffffffffe00e3ff

def z1296 : W := mkw 0x47e776b5b8000000 0x04467f3fc0000000

def z1297 : W := mkw 0x0800010240d9a6bd 0xc800000002f8e3ff

def z1298 : W := mkw 0x1800010243efdffe 0xc800000003ffffff

def z1299 : W := mkw 0x67fffefdbf347000 0x3fffffffff38fc00

def z1300 : W := mkw 0x0018894a00d8a280 0xffb98fce3ef8e38f

def z1301 : W := mkw 0x47fffefdbc000000 0x3ffffffffe000380

def z1302 : W := mkw 0x453fee4d94000000 0x063fff0fc0000000

def z1303 : W := mkw 0x453ebe5db4000000 0x047e7f3fc0000000

def z1304 : W := mkw 0x57fffefdbc2c0080 0x37fffffffc380000

def z1305 : W := mkw 0x6f13ff14bc92fc1c 0x8201ff003c00fc0c

def z1306 : W := mkw 0x24f7ed0003b6f800 0x14ffff0003ff7c00

def z1307 : W := mkw 0x10ed40eb436d53e0 0x3dfe70ffc3ff1ff0

def z1308 : W := mkw 0x24f7ed0000b6a800 0x3effff0001ff9c00

def z1309 : W := mkw 0x00188b4e14d8a285 0xfff9ffce3ff8ff8f

def z1310 : W := mkw 0x47fffefdbf005000 0x37fffffffe006000

def z1311 : W := mkw 0x47fffefdbc00055a 0x37fffffffc000070

def z1312 : W := mkw 0x01023614b0000000 0x03007f3ff0000000

def z1313 : W := mkw 0x653eae4d94260800 0x043e0f0fc0070000

def z1314 : W := mkw 0x0800010243c38f7c 0x8800000003c79ffc

def z1315 : W := mkw 0x47fffefdbf005418 0xbfffffffff00fe7c

def z1316 : W := mkw 0x0800010240d3ae3d 0xc800000001c7fe7f

def z1317 : W := mkw 0x10ec00eb406d03e0 0x35fe00ffc0ff03f0

def z1318 : W := mkw 0x02c150b028000418 0xfbc1f0f03f00ffff

def z1319 : W := mkw 0x3800010243fffffc 0x8800000003fffffc

def z1320 : W := mkw 0x10ec00eb436d03e0 0x15be00ffc2ff03f0

def z1321 : W := mkw 0x45ffeeed94000000 0x37ffffffc0000000

def z1322 : W := mkw 0x18c011b263ef8ffc 0xbbc070f033ff9ffc

def z1323 : W := mkw 0x47e776b5bb00555a 0xffc7ffffff00ffff

def z1324 : W := mkw 0x00c140a003005140 0xfbc1f0f03f00ffff

def z1325 : W := mkw 0x00fc88e900000000 0x37ff8fffc0000000

def z1326 : W := mkw 0x09023716f0d3ae3c 0xaf467f3ff3fffe7c

def z1327 : W := mkw 0x45ffee4d94000000 0x047e7f0fc0000000

def z1328 : W := mkw 0x09023716f4c38e3d 0xef467f3ffdc79e7f

def z1329 : W := mkw 0x0800010240c38e3c 0xac46000001c79e7c

def z1330 : W := mkw 0x47fffefdbc000000 0x15bf8ffffc000000

def z1331 : W := mkw 0x67fffefdbc025800 0x37fffffffc001c00

def z1332 : W := mkw 0x4512ae0494000000 0x04060f0fc0000000

def z1333 : W := mkw 0x43cb76fdbc000000 0x37c7fffffc000000

def z1334 : W := mkw 0x473ffefdbc000000 0x073ffffffc000000

def z1335 : W := mkw 0x47fffefdbc000000 0x36ffff3fc0000000

def z1336 : W := mkw 0x453eae4d94000000 0x273e0f0ff0000000

def z1337 : W := mkw 0x06fffcf928000000 0x37fffffffc000000

def z1338 : W := mkw 0x03037614b800541a 0xe747ff3ffc00fc0f

def z1339 : W := mkw 0x0002270650c38a24 0xaf467f3ff1c79e7c

def z1340 : W := mkw 0x00ee24e900000000 0x37fe7fffc0000000

def z1341 : W := mkw 0x52ec00eb4f6d03e0 0x3dfe00ffcfff03f0

def z1342 : W := mkw 0x47fffefdbc000142 0x77fffffffc000183

def z1343 : W := mkw 0x0b023716f8c38e3e 0xef467f3ffdc79e7f

def z1344 : W := mkw 0x00188b4e14d8a285 0xd6b98fce3ef8e18f

def z1345 : W := mkw 0x47fffefdbc005000 0x37fffffffc00fc00

def z1346 : W := mkw 0x04ffeeed14000000 0x37fffffffc000000

def z1347 : W := mkw 0x00188b4e54d9a2a5 0xffb98ffffef8e3ff

def z1348 : W := mkw 0x00c1501023005418 0xfbc1f0f03f00ffff

def z1349 : W := mkw 0x0800010243c3df7e 0x8800000001c79e7c

def z1350 : W := mkw 0x47fffefdbf1875db 0xffffffffff38ffff

def z1351 : W := mkw 0x25f7fe14b3347000 0x37ffff3ff2386000

def z1352 : W := mkw 0x24f7eda003b6f800 0x3ffffff003fffc00

def z1353 : W := mkw 0x04feace900000000 0x35fe0fffc0000000

def z1354 : W := mkw 0x01c236b4b0000000 0x37c67ffff0000000

def z1355 : W := mkw 0x03c376b4b8000000 0x27467f3ff0000000

def z1356 : W := mkw 0x56ed40eb4b6d03e0 0x3dfe00ffc3ff03f0

def z1357 : W := mkw 0x47fffefdbf00555a 0xf7fffffffd00fc7f

def z1358 : W := mkw 0x473ffe5dbc00541a 0xc63fff0ffc00fc0f

def z1359 : W := mkw 0x2436ad0000b6a800 0x063e7f0000ff9c00

def z1360 : W := mkw 0x09023716f0d3ae3d 0xef467f3ff1c7fe7f

def z1361 : W := mkw 0x2800010243e7de3c 0x8800000001c79e7c

def z1362 : W := mkw 0x0800111260dbaebd 0xfbc1f0f03fffffff

def z1363 : W := mkw 0x47fffefdbc102001 0x77fffffffc006003

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z7,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z9,z6]),(0,[z1,z10,z2,z3,z8,z5,z6]),(0,[z11,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z12,z3,z8,z5,z6]),(1,[z1,z3,z13,z8,z5,z6]),(0,[z1,z14,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z15,z16,z6]),(0,[z1,z17,z2,z3,z8,z5,z6])],[(0,[z2,z3,z18,z8,z19,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z20])],[(1,[z0,z21,z3,z8,z5,z6]),(0,[z22,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z23,z6])],[(0,[z1,z24,z2,z3,z8,z5,z25]),(1,[z1,z2,z3,z8,z26,z6]),(0,[z1,z3,z8,z27,z5,z28,z6]),(0,[z1,z2,z3,z8,z5,z29,z30]),(1,[z1,z2,z3,z8,z5,z31]),(0,[z1,z2,z3,z8,z5,z32,z6])],[(0,[z1,z3,z13,z33,z8,z5,z6]),(0,[z1,z2,z3,z18,z8,z5,z6]),(0,[z34,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z35]),(1,[z1,z2,z36,z8,z5,z6]),(0,[z37,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z38,z39]),(0,[z1,z2,z3,z8,z5,z16,z6])],[(0,[z0,z1,z24,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z25]),(0,[z40,z1,z2,z3,z8,z5,z38]),(0,[z41,z1,z42,z2,z3,z8,z5]),(0,[z43,z1,z2,z3,z8,z5,z44]),(0,[z43,z1,z2,z3,z8,z5,z29]),(0,[z1,z45,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z8,z5,z38]),(0,[z1,z2,z47,z48,z3,z8,z5])],[(0,[z1,z2,z49,z3,z8,z5,z6]),(0,[z1,z50,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z38,z51]),(0,[z1,z2,z3,z8,z5,z29,z52]),(0,[z53,z1,z2,z3,z54,z5,z6]),(0,[z1,z2,z3,z8,z55,z5,z6])],[(1,[z1,z56,z2,z3,z8,z5]),(0,[z57,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z58,z6]),(0,[z59,z1,z2,z48,z3,z8,z5])],[(0,[z1,z2,z3,z60,z8,z5,z6]),(0,[z1,z2,z3,z18,z8,z5,z29]),(0,[z1,z61,z2,z3,z8,z5,z6]),(0,[z1,z62,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z63,z5,z38]),(0,[z1,z2,z3,z8,z5,z16,z29]),(0,[z1,z2,z8,z5,z64,z6,z30])],[(0,[z1,z2,z65,z33,z8,z5,z6]),(0,[z1,z2,z48,z3,z18,z8,z5]),(0,[z1,z2,z3,z8,z5,z66,z38]),(0,[z1,z2,z3,z8,z15,z5,z38]),(0,[z1,z67,z2,z3,z8,z5,z6]),(0,[z1,z2,z68,z3,z8,z5,z6])],[(0,[z69,z1,z2,z48,z3,z8,z5]),(0,[z1,z70,z2,z3,z8,z71,z6]),(0,[z1,z2,z3,z8,z5,z28,z29]),(0,[z1,z72,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z73,z6]),(0,[z1,z74,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z4,z8,z5,z6]),(0,[z41,z1,z2,z3,z8,z75,z6]),(1,[z41,z2,z3,z8,z76,z6]),(0,[z1,z77,z2,z3,z8,z5,z6])],[(1,[z78,z2,z3,z8,z5,z79]),(1,[z2,z3,z8,z5,z80,z6]),(0,[z1,z2,z3,z81,z8,z5,z6]),(0,[z82,z1,z2,z3,z8,z5,z6])],[(0,[z83,z1,z21,z3,z8,z5,z6]),(0,[z84,z1,z2,z3,z8,z5,z6]),(0,[z40,z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z85,z6]),(0,[z1,z2,z3,z8,z86,z5,z6]),(0,[z87,z1,z2,z3,z8,z5,z29]),(0,[z1,z46,z2,z48,z3,z8,z5])]],
   [[(0,[z1,z2,z3,z8,z5,z88,z6]),(0,[z1,z89,z2,z3,z8,z5,z90]),(0,[z91,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z48,z3,z8,z5,z92]),(0,[z1,z2,z3,z8,z5,z93,z16])],[(0,[z94,z1,z42,z2,z3,z8,z5])],[(0,[z1,z77,z2,z3,z8,z5,z29])],[(0,[z1,z2,z95,z3,z8,z5,z6]),(0,[z1,z62,z2,z48,z3,z8,z5]),(0,[z96,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z97,z38]),(0,[z1,z42,z2,z8,z5,z6,z30])],[(0,[z1,z2,z98,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z99,z5,z6]),(0,[z1,z2,z100,z3,z8,z5,z6])],[(0,[z101,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z102,z8,z6]),(0,[z1,z2,z3,z103,z8,z5,z6]),(0,[z1,z2,z3,z104,z8,z5,z6]),(0,[z1,z2,z3,z105,z8,z5,z6]),(0,[z1,z106,z2,z3,z8,z5,z6]),(0,[z91,z1,z2,z3,z8,z5,z29]),(0,[z1,z107,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z108,z5,z6]),(1,[z1,z2,z3,z8,z5,z93])],[(0,[z1,z2,z48,z3,z8,z5,z75]),(0,[z1,z2,z3,z8,z5,z6,z109]),(0,[z53,z1,z2,z3,z110,z5,z6]),(0,[z1,z2,z3,z111,z8,z5,z6])],[(0,[z83,z1,z2,z3,z8,z5,z6]),(0,[z112,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z113]),(0,[z1,z2,z3,z8,z5,z114,z6]),(0,[z1,z2,z3,z115,z8,z5,z6])]],
   [[(0,[z0,z1,z65,z3,z8,z5,z6]),(0,[z116,z1,z2,z3,z8,z5,z6]),(0,[z94,z1,z2,z3,z8,z75,z6]),(0,[z117,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z6,z118])],[(0,[z1,z2,z48,z3,z8,z19,z5])],[(0,[z1,z2,z3,z8,z5,z119,z6]),(1,[z1,z120,z2,z3,z8,z5]),(0,[z1,z106,z2,z3,z8,z5,z29])],[(0,[z1,z121,z2,z3,z8,z5,z6]),(0,[z1,z122,z2,z3,z8,z5,z6]),(0,[z123,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z124,z8,z5,z6]),(0,[z1,z2,z48,z3,z8,z63,z5]),(0,[z1,z125,z2,z3,z8,z5,z6])],[(0,[z83,z1,z2,z3,z8,z5,z29]),(0,[z1,z126,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z127,z6]),(0,[z1,z2,z128,z3,z8,z5,z6])],[(0,[z129,z1,z2,z3,z8,z5,z6]),(0,[z130,z1,z2,z3,z8,z5,z131]),(0,[z1,z2,z3,z8,z5,z6,z132]),(0,[z53,z1,z2,z8,z63,z5,z6]),(0,[z1,z2,z48,z3,z8,z133,z5])],[(0,[z1,z2,z134,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z135,z5,z6]),(0,[z1,z2,z3,z8,z15,z76,z6]),(0,[z1,z136,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z137,z8,z5,z6]),(0,[z1,z2,z3,z138,z8,z5,z6]),(0,[z1,z2,z3,z139,z8,z5,z6]),(0,[z1,z2,z140,z3,z8,z5,z6]),(0,[z141,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z142,z5,z6]),(0,[z1,z2,z143,z3,z8,z5,z38]),(0,[z1,z2,z3,z144,z8,z5,z38]),(0,[z145,z1,z2,z3,z8,z5,z6])],[(0,[z69,z130,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z146,z38])],[(0,[z1,z2,z147,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z148,z5,z6]),(0,[z1,z2,z3,z149,z8,z5,z6]),(0,[z1,z2,z48,z150,z3,z8,z5]),(0,[z1,z2,z48,z3,z8,z5,z16])],[(0,[z0,z94,z2,z3,z8,z5,z6]),(0,[z1,z2,z48,z3,z151,z8,z5]),(0,[z1,z77,z2,z3,z8,z5,z152]),(0,[z53,z1,z2,z3,z8,z5,z6]),(0,[z1,z153,z2,z3,z8,z5,z6])],[(1,[z1,z42,z2,z48,z8,z5]),(0,[z1,z2,z3,z8,z5,z154,z6])],[(0,[z1,z2,z3,z8,z19,z5,z6]),(0,[z1,z2,z3,z8,z5,z155,z6]),(0,[z1,z2,z3,z8,z156,z5,z6]),(0,[z1,z2,z3,z8,z5,z157,z6])],[(0,[z0,z1,z2,z158,z8,z5,z6]),(0,[z159,z1,z2,z3,z8,z5,z6]),(0,[z1,z62,z3,z8,z27,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z160]),(0,[z1,z42,z161,z2,z3,z8,z5]),(1,[z1,z2,z48,z8,z5,z64]),(0,[z1,z2,z3,z8,z5,z6,z162])],[(0,[z1,z2,z163,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z164,z5,z6]),(0,[z1,z2,z3,z8,z5,z29,z64]),(0,[z1,z165,z2,z3,z8,z5,z6]),(0,[z117,z1,z2,z3,z166,z8,z6])]],
   [[(0,[z1,z167,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z168,z6]),(1,[z1,z2,z3,z8,z5,z169]),(0,[z53,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z170,z6]),(0,[z1,z42,z2,z3,z8,z171,z5]),(0,[z1,z2,z172,z3,z8,z5,z173])],[(0,[z1,z174,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z175,z5,z6])],[(0,[z1,z176,z2,z3,z8,z5,z6]),(0,[z1,z177,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z19,z5,z29]),(0,[z1,z178,z2,z3,z8,z5,z6]),(0,[z179,z2,z3,z18,z8,z5,z6]),(0,[z1,z2,z3,z180,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z181]),(0,[z1,z2,z3,z8,z27,z5,z29]),(0,[z1,z2,z3,z8,z5,z155,z29]),(0,[z1,z182,z42,z2,z3,z8,z5]),(1,[z1,z183,z3,z8,z5,z6])],[(0,[z1,z2,z3,z184,z8,z5,z6]),(0,[z1,z2,z47,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z185,z5,z6]),(0,[z1,z182,z2,z3,z8,z5,z186]),(0,[z1,z2,z3,z8,z5,z187,z6]),(0,[z1,z2,z3,z8,z5,z6,z188])],[(1,[z1,z2,z3,z8,z5,z119]),(0,[z1,z189,z2,z3,z8,z5,z6]),(0,[z190,z1,z2,z3,z8,z5,z6]),(1,[z53,z1,z2,z63,z5,z6]),(0,[z191,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z192,z5,z6]),(1,[z1,z77,z3,z144,z5,z6]),(0,[z1,z2,z3,z8,z193,z5,z6])],[(0,[z1,z42,z2,z33,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z131]),(0,[z1,z2,z3,z8,z5,z90,z6]),(0,[z1,z2,z3,z8,z194,z5,z6])],[(0,[z1,z195,z2,z3,z8,z5,z6]),(0,[z78,z1,z2,z3,z8,z5,z51]),(0,[z1,z2,z3,z8,z5,z6,z196]),(0,[z1,z2,z3,z8,z5,z6,z197])]],
   [[(0,[z198,z1,z2,z3,z8,z5,z6])],[(0,[z69,z1,z2,z3,z8,z5,z6]),(0,[z2,z143,z3,z33,z8,z5,z6]),(0,[z199,z1,z2,z36,z8,z5,z6]),(0,[z1,z120,z2,z65,z3,z8,z5]),(0,[z1,z2,z200,z3,z8,z5,z6]),(0,[z1,z2,z3,z201,z8,z5,z6])],[(0,[z1,z2,z3,z202,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z203]),(0,[z1,z2,z172,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z173,z38]),(0,[z1,z2,z3,z8,z204,z5,z6]),(0,[z205,z1,z2,z48,z3,z8,z5])],[(0,[z40,z1,z2,z3,z18,z5,z6]),(0,[z1,z206,z2,z48,z3,z8,z5]),(1,[z207,z2,z3,z8,z5,z6])],[(0,[z179,z1,z2,z150,z3,z5,z6]),(0,[z1,z2,z3,z8,z133,z5,z208]),(0,[z1,z2,z3,z8,z5,z6,z209])],[(0,[z0,z1,z2,z3,z8,z5,z119]),(0,[z1,z2,z210,z3,z8,z5,z6]),(1,[z1,z2,z3,z104,z5,z6]),(1,[z1,z2,z3,z8,z5,z211]),(0,[z1,z89,z2,z3,z8,z5,z29]),(0,[z1,z42,z42,z2,z3,z8,z5])],[(0,[z69,z1,z2,z3,z8,z5,z29]),(0,[z130,z1,z2,z3,z8,z5,z38]),(0,[z212,z1,z2,z3,z8,z5,z6]),(0,[z213,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z214,z3,z8,z5]),(0,[z1,z42,z2,z3,z8,z215,z5]),(0,[z1,z42,z2,z3,z8,z5,z186]),(0,[z1,z2,z3,z216,z8,z217,z5]),(0,[z1,z2,z3,z8,z5,z218,z6])],[(0,[z1,z2,z2,z3,z8,z5,z6]),(0,[z53,z1,z2,z8,z133,z5,z6]),(0,[z1,z2,z48,z3,z8,z5,z51]),(0,[z1,z2,z3,z8,z5,z6,z219])]],
   [[(0,[z220,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z221,z5,z6]),(0,[z1,z2,z3,z8,z5,z211,z6]),(0,[z1,z62,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z222,z8,z5,z6]),(0,[z1,z2,z3,z8,z63,z5,z6])],[(0,[z223,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z224,z8,z5,z6]),(0,[z1,z77,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z8,z15,z5,z6]),(0,[z1,z42,z2,z3,z8,z15,z5])],[(0,[z1,z2,z3,z225,z8,z5,z6]),(0,[z1,z226,z2,z3,z8,z5,z6]),(0,[z78,z1,z2,z3,z216,z8,z5]),(0,[z1,z227,z2,z3,z8,z5,z6]),(0,[z1,z206,z2,z3,z8,z5,z228]),(0,[z229,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z230])],[(1,[z1,z2,z3,z231,z8,z5]),(0,[z1,z2,z3,z8,z232,z5,z6]),(0,[z233,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z234,z6]),(0,[z1,z2,z172,z48,z3,z8,z5]),(0,[z1,z2,z3,z166,z8,z16,z6])],[(0,[z179,z1,z2,z48,z3,z8,z5]),(0,[z78,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z29,z66]),(0,[z1,z2,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z208,z6]),(0,[z1,z2,z3,z235,z8,z5,z6]),(0,[z1,z2,z236,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z237,z1,z2,z3,z8,z5,z6]),(1,[z43,z1,z151,z8,z5,z6]),(0,[z1,z62,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z63,z5,z29]),(0,[z238,z1,z2,z3,z8,z5,z6]),(0,[z239,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z166,z8,z54,z6])],[(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z15,z5,z29]),(0,[z1,z42,z2,z3,z8,z5,z240])],[(0,[z241,z1,z2,z3,z8,z5,z6]),(0,[z130,z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z242,z6]),(0,[z1,z2,z3,z243,z8,z5,z6]),(0,[z1,z2,z3,z8,z244,z5,z6]),(0,[z1,z2,z3,z8,z5,z29,z38]),(0,[z1,z2,z3,z245,z8,z5,z6]),(0,[z1,z2,z48,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z8,z16,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z246]),(0,[z1,z2,z3,z8,z247,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z248]),(0,[z1,z2,z3,z249,z8,z5,z6]),(0,[z250,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z110,z8,z5,z29]),(0,[z1,z2,z251,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z113])],[(0,[z1,z2,z3,z8,z5,z6,z252]),(0,[z1,z2,z253,z3,z8,z28,z6]),(0,[z1,z2,z3,z8,z5,z254,z6]),(0,[z1,z2,z255,z3,z8,z5,z6])],[(0,[z1,z2,z256,z3,z8,z5,z6]),(0,[z43,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z257,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z92,z38]),(0,[z1,z2,z48,z3,z110,z8,z5]),(0,[z1,z2,z48,z3,z216,z8,z5]),(0,[z1,z46,z2,z3,z8,z5,z113]),(1,[z1,z46,z2,z3,z16,z6]),(0,[z1,z2,z128,z3,z8,z5,z16]),(0,[z1,z2,z3,z8,z5,z258,z6])],[(0,[z1,z2,z3,z8,z259,z5,z6]),(1,[z1,z2,z3,z8,z5,z260]),(1,[z1,z2,z3,z5,z261,z6]),(0,[z1,z2,z3,z8,z5,z262,z6])],[(0,[z1,z65,z3,z151,z8,z5,z6]),(0,[z263,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z245,z8,z5,z29]),(0,[z1,z2,z48,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z217,z5,z51]),(0,[z1,z2,z3,z8,z5,z6,z51])],[(0,[z1,z24,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z264,z5,z6]),(0,[z1,z265,z2,z3,z8,z5,z6]),(0,[z1,z2,z266,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z75,z28,z6]),(0,[z267,z1,z2,z3,z8,z5,z6]),(0,[z1,z70,z2,z3,z104,z5,z6]),(0,[z1,z70,z2,z3,z8,z5,z211]),(0,[z1,z42,z2,z65,z3,z8,z5]),(0,[z1,z62,z77,z3,z8,z5,z6]),(0,[z1,z89,z2,z3,z124,z5,z6]),(0,[z1,z89,z2,z3,z8,z5,z268]),(0,[z1,z2,z150,z3,z8,z5,z38]),(0,[z1,z2,z3,z166,z8,z5,z38])],[(0,[z1,z2,z3,z269,z8,z5,z6]),(0,[z43,z1,z2,z3,z8,z5,z270]),(0,[z1,z206,z3,z8,z27,z5,z6]),(0,[z1,z2,z3,z8,z5,z271,z6]),(0,[z1,z2,z3,z8,z5,z272,z6]),(0,[z273,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z216,z8,z5,z186]),(1,[z1,z2,z172,z3,z8,z51])],[(0,[z199,z78,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z274,z6]),(1,[z1,z2,z3,z8,z5,z38])]],
   [[(0,[z1,z2,z3,z8,z275,z5,z6]),(0,[z1,z276,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z3,z8,z5,z30])],[(0,[z1,z89,z2,z3,z277,z5,z6]),(0,[z1,z2,z253,z3,z8,z5,z38])],[(0,[z94,z24,z2,z3,z8,z5,z6]),(0,[z1,z42,z24,z2,z3,z8,z5]),(0,[z1,z2,z3,z33,z8,z5,z38]),(0,[z278,z1,z2,z3,z8,z5,z6]),(0,[z40,z1,z2,z150,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z279]),(0,[z1,z280,z2,z3,z8,z5,z6]),(0,[z281,z1,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z150,z3,z5,z6]),(0,[z282,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z283])],[(0,[z1,z2,z3,z8,z284,z5,z6]),(0,[z285,z1,z2,z3,z8,z5,z6]),(1,[z1,z106,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z23,z29])],[(0,[z1,z2,z3,z8,z286,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z6]),(0,[z1,z2,z3,z8,z5,z6,z287]),(0,[z1,z67,z42,z2,z3,z8,z5]),(0,[z1,z288,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z217,z5,z6])],[(0,[z1,z2,z3,z144,z18,z5,z6])],[(0,[z1,z24,z2,z48,z3,z8,z5]),(0,[z1,z2,z143,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z289,z6]),(0,[z1,z2,z3,z8,z76,z5,z6]),(0,[z1,z2,z290,z3,z151,z8,z5]),(0,[z1,z2,z3,z144,z8,z5,z6])],[(0,[z1,z2,z3,z8,z291,z5,z6]),(0,[z53,z1,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z8,z5,z146,z6])]],
   [[(0,[z0,z1,z2,z3,z8,z5,z38]),(1,[z1,z2,z3,z8,z5,z292]),(0,[z1,z2,z110,z8,z63,z5,z6]),(1,[z1,z2,z48,z3,z8,z5])],[(0,[z293,z1,z2,z3,z8,z5,z6]),(0,[z1,z24,z2,z3,z8,z5,z294]),(0,[z1,z2,z3,z102,z33,z8,z6]),(0,[z179,z130,z2,z3,z8,z5,z6]),(0,[z199,z1,z2,z3,z8,z5,z79]),(0,[z43,z1,z70,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z44]),(0,[z91,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z217,z5,z29]),(0,[z1,z2,z295,z48,z3,z8,z5])],[(0,[z1,z296,z2,z3,z8,z5,z6]),(0,[z1,z70,z2,z3,z8,z5,z297]),(0,[z1,z2,z3,z8,z5,z38,z186]),(1,[z91,z1,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z133,z5,z6])],[(1,[z1,z2,z3,z8,z5,z294]),(0,[z1,z2,z143,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z76,z5,z29]),(0,[z1,z2,z3,z144,z8,z5,z29])],[(0,[z1,z2,z3,z8,z5,z298,z6])],[(0,[z1,z299,z2,z3,z8,z5,z6]),(0,[z1,z42,z70,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z300,z6]),(0,[z301,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z277,z5,z6]),(0,[z1,z2,z3,z302,z8,z5,z6]),(0,[z1,z2,z3,z8,z171,z5,z6])],[(0,[z1,z2,z3,z8,z5,z303,z6]),(0,[z304,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z305])],[(0,[z1,z2,z3,z306,z33,z5,z6]),(0,[z1,z42,z2,z143,z3,z8,z5]),(0,[z1,z2,z307,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z75,z38]),(0,[z1,z2,z3,z308,z8,z5,z6]),(0,[z1,z2,z3,z309,z8,z5,z6]),(0,[z1,z2,z3,z310,z8,z5,z6]),(0,[z1,z70,z2,z3,z8,z5,z38]),(0,[z1,z89,z2,z3,z8,z15,z6]),(0,[z1,z2,z3,z8,z133,z5,z29]),(0,[z205,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z311,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z312,z5,z6]),(0,[z83,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z313,z5,z6]),(0,[z1,z206,z2,z3,z8,z5,z6]),(0,[z1,z2,z150,z3,z54,z5,z6]),(0,[z1,z2,z3,z8,z314,z5,z6]),(0,[z1,z2,z3,z166,z54,z5,z6])],[(0,[z0,z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z33,z8,z5,z64,z6]),(0,[z315,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z316]),(1,[z1,z206,z3,z8,z15,z6]),(0,[z1,z206,z3,z8,z15,z5,z6])],[(0,[z317,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z38,z318]),(0,[z1,z2,z3,z8,z319,z5,z6]),(0,[z1,z320,z2,z3,z8,z5,z6]),(0,[z1,z321,z2,z3,z8,z5,z6])],[(0,[z94,z2,z3,z8,z5,z75,z6]),(0,[z1,z2,z3,z8,z322,z5,z6]),(1,[z1,z323,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z133,z5,z305])],[(0,[z1,z2,z324,z3,z33,z8,z5]),(0,[z1,z206,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z325,z5,z6]),(0,[z326,z1,z2,z3,z8,z5,z6]),(0,[z327,z1,z2,z3,z8,z5,z6]),(1,[z328,z1,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z329]),(0,[z1,z182,z2,z3,z8,z217,z5])],[(0,[z1,z2,z330,z3,z8,z5,z6]),(0,[z331,z1,z2,z3,z8,z5,z6]),(0,[z332,z1,z2,z3,z8,z5,z6])]],
   [[(1,[z1,z2,z158,z8,z5,z6]),(0,[z1,z2,z3,z8,z333,z5,z6]),(0,[z40,z2,z3,z8,z19,z5,z6]),(0,[z1,z2,z3,z8,z334,z5,z6]),(0,[z179,z1,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z8,z5,z29,z79]),(0,[z1,z2,z65,z3,z8,z5,z38]),(0,[z1,z2,z172,z3,z8,z5,z6])],[(0,[z1,z2,z33,z151,z8,z5,z6]),(0,[z179,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z335,z6]),(0,[z43,z1,z2,z151,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z336,z6]),(0,[z337,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z268]),(0,[z1,z2,z3,z8,z338,z5,z6])],[(1,[z94,z2,z3,z8,z75,z6]),(0,[z1,z70,z65,z3,z8,z5,z6]),(0,[z53,z1,z2,z3,z63,z5,z6]),(0,[z1,z42,z2,z3,z166,z8,z5])],[(0,[z1,z2,z3,z339,z8,z5,z6]),(0,[z1,z2,z3,z340,z8,z5,z6]),(1,[z1,z2,z3,z201,z8,z5]),(0,[z1,z2,z3,z341,z8,z5,z6])],[(0,[z342,z1,z2,z3,z33,z8,z6]),(0,[z1,z2,z3,z343,z8,z5,z6]),(0,[z344,z1,z2,z3,z8,z5,z6]),(0,[z1,z62,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z8,z5,z152,z6]),(0,[z1,z2,z3,z8,z5,z38,z30]),(0,[z53,z1,z42,z2,z3,z8,z5])],[(0,[z1,z345,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z346,z6]),(0,[z1,z206,z77,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z54,z28,z6]),(0,[z1,z2,z172,z3,z8,z5,z29]),(0,[z53,z1,z2,z150,z8,z5,z6]),(0,[z1,z2,z3,z54,z5,z16,z6])],[(0,[z1,z2,z3,z19,z27,z5,z6]),(0,[z179,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z347,z6]),(0,[z1,z2,z3,z348,z8,z5,z38])],[(0,[z1,z77,z3,z144,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z349,z6]),(0,[z1,z42,z2,z3,z8,z5,z28]),(0,[z1,z2,z172,z3,z8,z6,z51])]],
   [[(0,[z350,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z351,z6])],[(0,[z352,z1,z2,z3,z8,z5,z6]),(0,[z130,z1,z2,z143,z8,z5,z6]),(0,[z199,z1,z2,z3,z8,z5,z173]),(1,[z1,z42,z2,z8,z5,z30]),(0,[z1,z42,z2,z3,z8,z217,z5])],[(1,[z130,z2,z143,z8,z5,z6]),(0,[z41,z94,z2,z3,z8,z5,z6]),(0,[z1,z2,z290,z3,z8,z5,z6]),(0,[z1,z62,z2,z3,z8,z5,z300]),(0,[z353,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z110,z8,z133,z5,z6])],[(0,[z1,z2,z3,z8,z5,z354,z6]),(0,[z69,z1,z2,z33,z8,z5,z6]),(0,[z1,z70,z2,z151,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z355]),(0,[z1,z42,z2,z3,z8,z5,z64])],[(0,[z1,z42,z2,z3,z144,z8,z5]),(0,[z1,z2,z3,z8,z5,z356,z6])],[(0,[z1,z357,z2,z3,z8,z5,z6]),(0,[z1,z358,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z54,z5,z38]),(0,[z1,z2,z359,z3,z8,z5,z6]),(0,[z190,z1,z42,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z360,z6]),(0,[z2,z3,z33,z8,z19,z5,z6]),(0,[z43,z1,z2,z65,z8,z5,z6]),(0,[z361,z1,z2,z3,z8,z5,z38])],[(0,[z1,z2,z3,z362,z8,z5,z6]),(0,[z1,z2,z3,z363,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z364]),(0,[z1,z2,z3,z365,z8,z5,z6]),(0,[z1,z2,z48,z366,z3,z8,z5]),(0,[z1,z2,z3,z8,z217,z173,z6])]],
   [[(0,[z367,z1,z2,z3,z8,z5,z6]),(0,[z199,z1,z2,z3,z8,z5,z66]),(0,[z1,z2,z368,z3,z8,z5,z6]),(0,[z1,z2,z150,z110,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z369,z6]),(0,[z1,z370,z2,z3,z8,z5,z6]),(0,[z1,z371,z2,z3,z8,z5,z6]),(0,[z372,z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z366,z3,z8,z5,z6])],[(0,[z0,z2,z21,z3,z8,z5,z6]),(0,[z1,z373,z2,z3,z8,z5,z6]),(0,[z59,z1,z2,z3,z8,z5,z6]),(0,[z1,z89,z42,z2,z3,z8,z5])],[(0,[z69,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z374,z6]),(0,[z1,z42,z2,z214,z3,z8,z5])],[(0,[z1,z2,z3,z375,z8,z5,z6]),(1,[z342,z1,z2,z3,z8,z6]),(0,[z199,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z150,z3,z8,z5,z6]),(0,[z1,z2,z3,z166,z8,z5,z6])],[(0,[z376,z1,z2,z3,z8,z5,z6]),(0,[z1,z377,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z378]),(0,[z1,z2,z3,z8,z5,z173,z92]),(0,[z1,z2,z3,z379,z8,z5,z6])],[(0,[z380,z1,z2,z3,z8,z5,z6]),(0,[z381,z1,z3,z33,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z382,z6]),(0,[z1,z77,z2,z3,z144,z5,z6]),(0,[z1,z2,z3,z8,z5,z383,z6]),(1,[z1,z2,z3,z8,z5,z287])],[(0,[z0,z1,z21,z3,z8,z5,z6]),(0,[z1,z2,z3,z231,z8,z19,z5]),(0,[z1,z2,z295,z3,z8,z5,z6])],[(0,[z40,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z384,z5,z6]),(0,[z1,z2,z253,z3,z8,z5,z6]),(0,[z361,z1,z2,z48,z3,z8,z5]),(0,[z1,z46,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z33,z8,z5,z6]),(0,[z78,z1,z42,z2,z3,z8,z5]),(1,[z1,z2,z3,z385,z5,z6]),(0,[z1,z70,z2,z65,z8,z5,z6]),(0,[z1,z182,z2,z3,z8,z5,z38]),(0,[z1,z2,z150,z3,z8,z5,z29]),(0,[z1,z2,z3,z166,z8,z5,z29]),(0,[z1,z2,z48,z3,z311,z8,z5])],[(1,[z381,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z386,z5,z6]),(0,[z1,z62,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z387,z8,z5,z6]),(0,[z388,z1,z2,z3,z8,z5,z6]),(0,[z220,z1,z42,z2,z3,z8,z5]),(0,[z1,z42,z2,z3,z8,z5,z173]),(0,[z1,z2,z3,z8,z5,z6,z389]),(0,[z390,z1,z2,z3,z8,z5,z6])],[(0,[z391,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z392,z3,z8,z5,z6]),(0,[z1,z2,z253,z3,z8,z133,z6]),(0,[z1,z2,z3,z8,z215,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z393])],[(0,[z199,z1,z182,z2,z3,z8,z5]),(0,[z394,z1,z2,z3,z8,z5,z38]),(0,[z395,z1,z2,z3,z8,z5,z38]),(0,[z1,z396,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z216,z5,z92,z6])],[(1,[z83,z24,z3,z8,z5,z6]),(0,[z40,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z66,z6]),(0,[z199,z1,z2,z48,z3,z8,z5]),(0,[z1,z397,z2,z3,z8,z5,z6]),(0,[z1,z2,z253,z3,z8,z5,z29]),(0,[z1,z46,z2,z3,z8,z5,z29]),(0,[z1,z2,z398,z3,z8,z5,z6]),(1,[z1,z2,z3,z216,z5,z92])],[(0,[z1,z2,z3,z33,z8,z5,z29]),(0,[z1,z77,z2,z3,z8,z5,z169]),(1,[z1,z2,z253,z8,z133,z6])],[(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z399,z6]),(0,[z1,z2,z400,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z401,z38]),(0,[z1,z182,z2,z3,z5,z6,z186]),(0,[z402,z1,z2,z3,z8,z5,z6]),(0,[z1,z403,z2,z3,z8,z5,z6])],[(0,[z1,z2,z324,z3,z8,z5,z6]),(0,[z1,z206,z2,z3,z8,z15,z6]),(0,[z1,z2,z404,z3,z8,z5,z6])]],
   [[(0,[z1,z405,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z13,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z406,z6]),(0,[z1,z42,z2,z3,z8,z5,z66]),(0,[z1,z42,z206,z2,z3,z8,z5]),(0,[z407,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z253,z3,z8,z23,z6])],[(0,[z1,z2,z3,z8,z15,z75,z6]),(0,[z1,z2,z3,z8,z5,z270,z6]),(0,[z1,z2,z3,z8,z5,z71,z6]),(0,[z1,z2,z3,z8,z5,z29,z132]),(0,[z1,z2,z3,z8,z5,z29,z92]),(0,[z1,z182,z2,z48,z3,z8,z5]),(0,[z1,z2,z48,z3,z8,z5,z186]),(0,[z1,z2,z408,z3,z8,z5,z6])],[(0,[z409,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z410,z3,z151,z8,z5]),(0,[z1,z2,z3,z8,z5,z38,z411]),(0,[z1,z2,z3,z8,z5,z6,z412])],[(0,[z413,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z29]),(1,[z414,z1,z2,z3,z5,z6]),(1,[z1,z42,z2,z143,z8,z5]),(0,[z1,z415,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z3,z8,z5,z38]),(0,[z1,z46,z2,z3,z5,z16,z6]),(0,[z1,z416,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z417,z6])],[(0,[z1,z2,z3,z8,z418,z5,z6]),(0,[z1,z2,z48,z3,z8,z15,z5]),(0,[z1,z2,z3,z8,z5,z97,z6]),(0,[z1,z2,z3,z8,z5,z261,z6]),(0,[z1,z2,z419,z3,z8,z5,z6])],[(0,[z1,z420,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z75,z6]),(0,[z2,z3,z8,z5,z66,z6,z79]),(0,[z1,z2,z3,z8,z421,z5,z38]),(0,[z1,z2,z3,z422,z8,z5,z6]),(0,[z1,z423,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z424,z6])],[(0,[z1,z425,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z426,z6]),(0,[z1,z427,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z428,z8,z5,z6])],[(0,[z0,z1,z2,z134,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z429,z6]),(0,[z1,z430,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z431,z6])]],
   [[(0,[z1,z70,z2,z3,z385,z5,z6]),(0,[z1,z432,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z3,z8,z27,z5]),(0,[z1,z2,z433,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z434,z6]),(0,[z91,z1,z3,z8,z5,z29,z6])],[(0,[z1,z2,z3,z435,z8,z5,z6]),(0,[z1,z2,z3,z8,z436,z5,z6]),(0,[z1,z2,z3,z8,z5,z75,z29]),(0,[z1,z437,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z29,z160]),(0,[z1,z438,z2,z3,z8,z5,z6]),(0,[z1,z2,z439,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z5,z152]),(0,[z53,z1,z2,z3,z144,z5,z6]),(0,[z117,z1,z46,z2,z3,z8,z6]),(0,[z1,z2,z253,z8,z133,z5,z6]),(0,[z1,z42,z2,z3,z440,z8,z5]),(0,[z328,z1,z2,z8,z5,z16,z6]),(0,[z1,z2,z3,z8,z5,z6,z441])],[(0,[z1,z2,z3,z442,z8,z5,z6]),(0,[z1,z42,z2,z48,z3,z8,z5])],[(0,[z179,z1,z2,z3,z19,z5,z6]),(0,[z1,z2,z443,z3,z8,z5,z6]),(0,[z1,z2,z444,z3,z8,z5,z6]),(0,[z1,z445,z2,z3,z8,z5,z6])],[(0,[z446,z1,z2,z3,z8,z5,z6]),(0,[z447,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z448,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z449]),(0,[z1,z2,z3,z8,z5,z6,z186])],[(0,[z1,z42,z2,z3,z33,z8,z5]),(0,[z1,z2,z3,z8,z450,z5,z6]),(0,[z1,z437,z2,z3,z8,z5,z29]),(0,[z53,z145,z2,z3,z8,z5,z6]),(1,[z1,z451,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z452,z6]),(0,[z1,z453,z2,z3,z8,z5,z6]),(0,[z1,z454,z2,z3,z8,z5,z6])]],
   [[(0,[z0,z2,z3,z8,z76,z5,z6]),(0,[z130,z2,z3,z8,z19,z5,z6]),(0,[z41,z1,z2,z253,z3,z8,z6]),(0,[z43,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z48,z65,z3,z8,z5]),(0,[z1,z2,z3,z27,z5,z16,z6])],[(0,[z83,z24,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z102,z8,z5,z6]),(0,[z1,z455,z2,z3,z8,z5,z6]),(0,[z117,z1,z2,z110,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z80,z6]),(0,[z1,z2,z3,z216,z8,z5,z92])],[(0,[z1,z2,z65,z143,z8,z5,z6]),(0,[z1,z2,z3,z8,z456,z5,z6]),(0,[z1,z2,z3,z216,z8,z5,z38]),(0,[z1,z2,z48,z3,z8,z5,z30]),(0,[z1,z2,z3,z8,z5,z457,z6]),(0,[z458,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z459,z6]),(0,[z1,z2,z3,z18,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z6,z460]),(0,[z1,z461,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z217,z173])],[(0,[z372,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z26,z5,z6]),(0,[z1,z42,z2,z3,z3,z8,z5]),(0,[z1,z462,z2,z3,z8,z5,z6]),(0,[z1,z463,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z464,z5,z6]),(0,[z1,z2,z3,z8,z5,z28,z38]),(0,[z1,z2,z3,z8,z465,z5,z6]),(0,[z1,z46,z2,z3,z8,z5,z157])],[(0,[z1,z2,z3,z8,z5,z6,z318]),(0,[z466,z1,z2,z3,z8,z5,z6]),(0,[z41,z1,z2,z3,z8,z5,z38]),(0,[z467,z2,z3,z8,z5,z28,z6]),(0,[z1,z468,z2,z3,z8,z5,z6]),(0,[z117,z1,z2,z3,z8,z133,z6]),(0,[z1,z2,z48,z8,z5,z64,z6]),(0,[z1,z2,z3,z8,z5,z469,z6])]],
   [[(0,[z470,z1,z2,z3,z8,z5,z6]),(1,[z179,z2,z3,z18,z5,z6]),(0,[z1,z2,z3,z8,z5,z471,z6]),(1,[z1,z2,z3,z8,z5,z90]),(0,[z1,z2,z3,z8,z5,z58,z38]),(0,[z1,z2,z3,z8,z472,z5,z6])],[(0,[z1,z473,z2,z3,z33,z8,z5]),(0,[z199,z1,z2,z3,z8,z5,z51]),(0,[z1,z2,z3,z8,z5,z6,z474]),(0,[z475,z1,z2,z3,z8,z5,z6]),(0,[z43,z1,z2,z48,z3,z8,z5]),(0,[z53,z117,z1,z2,z8,z5,z6])],[(0,[z1,z2,z3,z476,z8,z5,z6]),(0,[z477,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z478]),(0,[z1,z62,z2,z3,z8,z5,z355]),(1,[z1,z2,z3,z8,z5,z228]),(0,[z1,z2,z3,z479,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z208]),(0,[z315,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z214,z3,z8,z5,z6]),(0,[z1,z2,z3,z440,z8,z5,z6])],[(0,[z1,z42,z2,z21,z3,z8,z5]),(0,[z1,z480,z2,z3,z8,z5,z6]),(0,[z481,z1,z2,z3,z8,z5,z6]),(0,[z40,z179,z2,z3,z8,z5,z6]),(0,[z94,z1,z2,z253,z3,z8,z6]),(0,[z1,z2,z3,z8,z76,z5,z35]),(0,[z1,z2,z3,z8,z5,z6,z482]),(0,[z1,z2,z3,z8,z54,z5,z6]),(0,[z1,z2,z172,z3,z8,z5,z51])],[(0,[z361,z1,z2,z3,z8,z5,z6]),(0,[z483,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z231,z8,z5,z6]),(0,[z1,z484,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z485]),(1,[z1,z2,z47,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z486,z6]),(0,[z117,z1,z2,z8,z5,z23,z6]),(0,[z1,z2,z3,z487,z8,z5,z6])],[(0,[z1,z120,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z144,z5,z16,z6]),(0,[z1,z182,z2,z172,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z488,z6]),(0,[z1,z2,z3,z8,z489,z5,z6]),(0,[z1,z2,z410,z3,z8,z5,z6]),(1,[z467,z2,z3,z8,z5,z6]),(0,[z1,z2,z253,z3,z8,z15,z6]),(0,[z53,z207,z2,z3,z8,z5,z6])],[(0,[z83,z1,z24,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z25,z6]),(0,[z1,z2,z490,z3,z8,z5,z6]),(0,[z1,z2,z150,z3,z27,z5,z6]),(0,[z1,z2,z3,z166,z27,z5,z6]),(0,[z491,z1,z2,z3,z8,z5,z6]),(0,[z492,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z493,z3,z8,z5,z6]),(0,[z91,z1,z2,z3,z8,z5,z38]),(0,[z1,z494,z2,z3,z8,z5,z6])]],
   [[(0,[z41,z1,z2,z48,z3,z8,z5]),(0,[z1,z62,z2,z3,z144,z5,z6]),(0,[z1,z2,z3,z8,z54,z5,z29]),(0,[z1,z2,z3,z8,z5,z6,z495]),(0,[z1,z2,z3,z8,z5,z496,z6]),(0,[z497,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z498]),(0,[z1,z2,z3,z8,z5,z6,z30]),(0,[z499,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z500,z3,z8,z5,z6]),(0,[z199,z1,z2,z3,z8,z5,z6]),(0,[z117,z1,z2,z3,z8,z28,z6]),(0,[z361,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z501,z5,z6])],[(0,[z1,z2,z48,z143,z3,z8,z5]),(0,[z179,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z502,z5,z6]),(0,[z94,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z503,z3,z8,z5,z6]),(0,[z1,z120,z2,z3,z8,z5,z29]),(0,[z504,z1,z2,z3,z8,z5,z6])],[(0,[z0,z43,z1,z3,z8,z5,z6]),(0,[z40,z1,z2,z3,z19,z5,z6]),(0,[z1,z505,z2,z3,z8,z5,z6]),(0,[z1,z70,z2,z48,z3,z8,z5]),(0,[z1,z62,z2,z3,z8,z346,z6]),(1,[z1,z2,z128,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z173,z6])],[(0,[z506,z1,z2,z3,z8,z5,z6]),(0,[z342,z1,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z3,z8,z5,z79]),(0,[z199,z1,z2,z3,z216,z8,z5]),(0,[z1,z2,z3,z8,z507,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z52]),(0,[z1,z42,z2,z3,z8,z5,z23]),(0,[z1,z2,z508,z3,z8,z5,z6]),(0,[z1,z2,z3,z509,z8,z5,z6])],[(0,[z510,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z511,z5,z6])],[(0,[z1,z2,z3,z512,z8,z5,z6]),(0,[z199,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z513,z8,z5,z6]),(0,[z1,z2,z3,z514,z8,z5,z6]),(0,[z1,z2,z3,z8,z515,z5,z6]),(0,[z1,z516,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z261,z23,z6]),(0,[z1,z182,z2,z3,z8,z5,z6]),(0,[z1,z2,z172,z3,z216,z8,z5])],[(0,[z130,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z300]),(0,[z1,z2,z3,z8,z5,z517,z6])]],
   [[(0,[z518,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z519,z6]),(0,[z1,z2,z3,z8,z520,z5,z6]),(0,[z1,z2,z3,z8,z5,z29,z51]),(0,[z1,z2,z3,z8,z5,z173,z29]),(0,[z1,z42,z2,z172,z3,z8,z5])],[(0,[z1,z521,z2,z3,z8,z5,z6]),(0,[z1,z2,z522,z3,z8,z5,z6]),(0,[z1,z523,z2,z3,z8,z5,z6]),(0,[z117,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z150,z3,z110,z5,z6]),(0,[z350,z1,z42,z2,z3,z8,z5])],[(0,[z41,z1,z2,z3,z8,z76,z6]),(0,[z1,z2,z3,z8,z524,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z525]),(0,[z1,z2,z526,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z527]),(0,[z94,z1,z2,z48,z3,z8,z5]),(0,[z43,z1,z3,z151,z8,z5,z6]),(0,[z1,z89,z206,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z64,z38]),(0,[z1,z2,z3,z8,z5,z92,z51])],[(1,[z1,z2,z3,z8,z5,z246]),(0,[z130,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z6,z528]),(0,[z1,z2,z3,z8,z529,z5,z6]),(0,[z1,z2,z3,z8,z5,z401,z6])],[(0,[z1,z2,z3,z8,z5,z530,z6]),(0,[z1,z531,z2,z3,z8,z5,z6]),(0,[z1,z56,z2,z3,z8,z5,z6]),(0,[z1,z2,z532,z3,z8,z5,z6]),(0,[z1,z2,z48,z3,z166,z8,z5])],[(0,[z1,z2,z3,z8,z5,z29,z383]),(0,[z1,z2,z3,z8,z533,z5,z6]),(0,[z1,z357,z42,z2,z3,z8,z5])],[(0,[z1,z2,z534,z3,z8,z5,z6]),(0,[z1,z183,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z535,z6])]],
   [[(0,[z69,z2,z3,z33,z8,z5,z6]),(1,[z1,z42,z2,z33,z8,z5]),(0,[z414,z1,z2,z3,z33,z5,z6]),(0,[z1,z2,z3,z8,z5,z536,z6]),(0,[z1,z2,z3,z8,z5,z35,z6]),(0,[z1,z2,z3,z8,z5,z29,z6])],[(0,[z1,z2,z537,z3,z8,z5,z6]),(0,[z83,z1,z65,z3,z8,z5,z6]),(0,[z1,z2,z538,z3,z8,z5,z6]),(1,[z1,z516,z2,z3,z5,z6])],[(0,[z1,z2,z3,z8,z5,z539,z6]),(1,[z1,z89,z3,z8,z28,z6]),(0,[z1,z2,z48,z3,z8,z5,z28]),(0,[z1,z2,z540,z3,z8,z5,z6]),(0,[z117,z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z6,z541]),(0,[z542,z1,z2,z3,z8,z5,z6])],[(0,[z1,z543,z2,z3,z8,z5,z6]),(1,[z199,z2,z3,z8,z5,z66]),(0,[z1,z2,z3,z151,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z92,z6]),(0,[z1,z2,z3,z8,z5,z6,z544])],[(0,[z1,z42,z2,z3,z8,z76,z5]),(0,[z1,z2,z3,z8,z27,z5,z38]),(0,[z1,z425,z2,z3,z8,z5,z6]),(0,[z1,z2,z48,z3,z8,z217,z5])],[(0,[z0,z1,z2,z3,z8,z5,z246]),(0,[z130,z1,z2,z3,z8,z5,z316]),(0,[z94,z1,z2,z3,z8,z76,z6]),(0,[z1,z2,z3,z8,z5,z29,z29]),(0,[z1,z2,z3,z8,z5,z545,z6]),(0,[z1,z2,z3,z8,z5,z546,z6])],[(0,[z1,z24,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z143,z8,z5,z6]),(0,[z53,z40,z1,z2,z3,z5,z6]),(0,[z1,z547,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z548,z5,z6]),(0,[z1,z2,z3,z8,z549,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z23]),(0,[z1,z2,z3,z8,z5,z550,z6]),(0,[z1,z2,z48,z3,z8,z5,z64])],[(0,[z1,z2,z48,z3,z144,z8,z5]),(0,[z1,z89,z2,z3,z8,z28,z6]),(0,[z1,z207,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z549,z63,z6]),(0,[z1,z551,z2,z48,z3,z8,z5]),(0,[z1,z2,z172,z3,z8,z217,z6]),(0,[z552,z1,z2,z3,z8,z5,z6])]],
   [[(1,[z1,z2,z3,z8,z5,z6]),(0,[z40,z1,z42,z2,z3,z8,z5]),(0,[z1,z553,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z507,z6]),(1,[z1,z70,z65,z8,z5,z6]),(0,[z1,z46,z42,z2,z3,z8,z5]),(0,[z1,z2,z554,z3,z8,z5,z6])],[(0,[z130,z2,z143,z3,z8,z5,z6]),(0,[z555,z1,z2,z3,z8,z5,z6]),(0,[z1,z556,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z557,z5,z6]),(0,[z1,z2,z3,z8,z558,z5,z6]),(0,[z1,z2,z3,z8,z385,z5,z6]),(1,[z1,z2,z3,z8,z71,z6]),(0,[z1,z2,z3,z8,z559,z5,z6])],[(0,[z560,z1,z2,z3,z8,z5,z6]),(0,[z1,z182,z2,z3,z8,z5,z92]),(0,[z1,z2,z3,z8,z561,z5,z6])],[(0,[z1,z24,z2,z3,z8,z5,z29]),(0,[z1,z2,z562,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z563,z6]),(0,[z1,z2,z3,z8,z564,z5,z6]),(0,[z1,z2,z565,z3,z8,z5,z6])],[(0,[z78,z1,z2,z3,z8,z5,z173]),(0,[z1,z2,z3,z8,z5,z6,z169]),(0,[z1,z46,z398,z3,z8,z5,z6])],[(1,[z1,z2,z3,z566,z5,z6]),(0,[z1,z2,z567,z3,z8,z5,z6]),(0,[z1,z2,z3,z144,z19,z5,z6]),(0,[z1,z2,z3,z8,z5,z568,z6]),(1,[z1,z2,z3,z8,z5,z44]),(0,[z1,z2,z3,z8,z569,z5,z6]),(0,[z1,z89,z3,z8,z5,z28,z6]),(1,[z1,z2,z3,z8,z5,z29])],[(0,[z24,z2,z21,z3,z8,z5,z6]),(0,[z1,z2,z21,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z570,z5,z6]),(0,[z43,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z571,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z411]),(0,[z1,z2,z3,z8,z5,z572,z6]),(0,[z1,z2,z3,z8,z5,z573,z6]),(0,[z574,z1,z2,z3,z8,z5,z6])],[(0,[z0,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z575,z8,z5,z6]),(0,[z1,z2,z47,z65,z3,z8,z5]),(0,[z1,z89,z2,z3,z8,z5,z38]),(0,[z1,z576,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z260,z6]),(0,[z1,z2,z3,z8,z5,z577,z6])]],
   [[(0,[z69,z1,z2,z3,z8,z5,z38]),(0,[z1,z42,z2,z3,z18,z8,z5]),(0,[z1,z2,z3,z8,z5,z38,z79]),(0,[z1,z2,z3,z8,z5,z578,z6]),(0,[z2,z3,z8,z5,z80,z28,z6]),(1,[z1,z3,z8,z5,z29,z38]),(0,[z1,z2,z562,z3,z8,z5,z29]),(0,[z1,z2,z3,z579,z8,z5,z6])],[(1,[z1,z2,z134,z8,z5,z6]),(0,[z199,z1,z2,z256,z8,z5,z6]),(0,[z580,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z581,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z582,z6]),(0,[z1,z2,z3,z216,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z583,z6]),(0,[z1,z2,z3,z8,z54,z15,z6]),(1,[z1,z2,z3,z8,z5,z305]),(0,[z1,z2,z584,z3,z8,z5,z6]),(0,[z1,z2,z3,z585,z8,z5,z6])],[(0,[z78,z1,z2,z3,z8,z5,z66]),(0,[z1,z2,z3,z8,z5,z586,z6]),(0,[z1,z2,z587,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z31,z6]),(0,[z1,z2,z48,z3,z8,z5,z356]),(0,[z1,z2,z3,z8,z5,z6,z588]),(0,[z1,z2,z3,z8,z5,z6,z589])],[(0,[z1,z2,z590,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z28,z6]),(0,[z1,z2,z48,z3,z8,z5,z173]),(0,[z328,z1,z2,z3,z8,z5,z6]),(1,[z1,z182,z2,z3,z5,z186])],[(0,[z1,z2,z3,z8,z5,z6,z591]),(0,[z1,z2,z3,z8,z5,z6,z592]),(0,[z41,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z593,z6]),(1,[z1,z62,z3,z27,z5,z6]),(0,[z1,z2,z3,z8,z28,z16,z6]),(0,[z1,z2,z3,z8,z5,z594,z6]),(0,[z1,z42,z2,z3,z8,z5,z92])],[(0,[z0,z1,z2,z3,z566,z5,z6]),(1,[z1,z2,z3,z8,z5,z316]),(0,[z78,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z6,z203]),(0,[z1,z42,z106,z2,z3,z8,z5]),(0,[z1,z2,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z216,z8,z5,z29]),(0,[z1,z2,z3,z110,z8,z5,z260])],[(0,[z1,z2,z21,z48,z3,z8,z5]),(0,[z87,z1,z2,z3,z8,z5,z6]),(0,[z595,z1,z2,z3,z8,z5,z6]),(0,[z1,z62,z2,z3,z8,z26,z6]),(0,[z1,z2,z253,z3,z166,z8,z6]),(0,[z1,z427,z42,z2,z3,z8,z5])]],
   [[(0,[z1,z2,z3,z596,z8,z5,z6]),(0,[z1,z70,z2,z3,z8,z5,z6]),(0,[z1,z70,z2,z3,z8,z507,z6]),(0,[z1,z89,z2,z48,z3,z8,z5])],[(0,[z597,z1,z2,z3,z8,z5,z6]),(0,[z598,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z599,z5,z6]),(0,[z1,z600,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z173,z6,z51])],[(0,[z601,z1,z2,z3,z8,z5,z6]),(0,[z1,z56,z2,z3,z8,z19,z5]),(0,[z41,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z602,z5,z6]),(0,[z603,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z110,z8,z5,z38]),(1,[z1,z72,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z593,z29])],[(1,[z1,z2,z3,z306,z5,z6]),(0,[z1,z42,z2,z3,z8,z5,z75]),(0,[z1,z2,z48,z3,z8,z5,z66]),(0,[z1,z2,z3,z8,z5,z604,z6])],[(0,[z1,z2,z3,z306,z8,z5,z6]),(0,[z467,z1,z2,z3,z8,z5,z6]),(0,[z605,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z606,z8,z5,z6]),(0,[z1,z2,z3,z8,z607,z5,z6])],[(0,[z117,z94,z1,z2,z3,z8,z6]),(0,[z1,z70,z2,z3,z8,z5,z29]),(1,[z1,z2,z3,z124,z5,z6]),(1,[z1,z2,z3,z8,z5,z268]),(0,[z1,z2,z3,z8,z5,z6,z608]),(0,[z1,z2,z3,z8,z5,z6,z609])],[(0,[z1,z42,z2,z3,z8,z19,z5]),(0,[z78,z1,z182,z2,z3,z8,z5]),(0,[z1,z2,z3,z36,z8,z5,z6]),(0,[z1,z610,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z228,z6]),(0,[z1,z2,z48,z3,z8,z5,z38]),(0,[z611,z1,z2,z3,z8,z5,z6]),(0,[z612,z1,z2,z3,z8,z5,z6])],[(0,[z613,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z298,z6]),(0,[z1,z2,z3,z8,z5,z614,z6]),(0,[z78,z1,z2,z48,z3,z8,z5]),(0,[z1,z42,z77,z2,z3,z8,z5]),(0,[z1,z2,z615,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z616,z5,z6]),(0,[z1,z2,z140,z3,z8,z5,z23])]],
   [[(0,[z1,z2,z3,z617,z8,z5,z6]),(0,[z94,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z604,z29]),(0,[z1,z42,z2,z3,z8,z63,z5])],[(0,[z1,z2,z65,z3,z8,z5,z6]),(1,[z1,z2,z3,z277,z5,z6]),(0,[z91,z1,z106,z3,z8,z5,z6]),(0,[z1,z2,z8,z133,z5,z23,z6]),(0,[z1,z2,z3,z8,z217,z5,z173])],[(0,[z1,z2,z618,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z619,z5,z6]),(0,[z1,z206,z2,z3,z8,z5,z203]),(0,[z1,z42,z2,z3,z8,z133,z5])],[(0,[z1,z2,z48,z3,z8,z27,z5]),(0,[z611,z1,z2,z3,z8,z5,z29])],[(0,[z1,z620,z2,z3,z8,z5,z6]),(1,[z69,z2,z33,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z614,z29]),(0,[z1,z2,z3,z621,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z240,z6])],[(1,[z40,z2,z3,z19,z5,z6]),(0,[z94,z1,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z76,z28,z6]),(0,[z1,z2,z3,z8,z5,z23,z38]),(0,[z622,z1,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z166,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z297]),(0,[z1,z2,z65,z3,z8,z5,z29]),(0,[z1,z623,z2,z3,z8,z5,z6]),(0,[z1,z2,z624,z48,z3,z8,z5])],[(0,[z625,z1,z2,z3,z8,z5,z6]),(0,[z41,z2,z3,z8,z76,z5,z6]),(1,[z1,z2,z3,z8,z5,z355]),(0,[z1,z2,z3,z348,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z16,z38]),(1,[z1,z2,z3,z8,z616,z5]),(0,[z1,z42,z2,z150,z3,z8,z5]),(0,[z117,z1,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z3,z8,z5,z16]),(0,[z1,z2,z48,z48,z3,z8,z5]),(1,[z1,z2,z3,z8,z5,z157])]],
   [[(0,[z0,z1,z2,z3,z8,z298,z6]),(0,[z1,z2,z3,z8,z5,z626,z6]),(1,[z1,z2,z256,z8,z5,z6]),(0,[z1,z42,z2,z3,z151,z8,z5]),(0,[z1,z2,z627,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z628,z5,z6]),(0,[z1,z629,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z64,z6])],[(0,[z630,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z48,z3,z33,z8,z5]),(1,[z1,z2,z290,z3,z8,z5]),(0,[z631,z1,z2,z3,z8,z5,z6])],[(0,[z117,z41,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z5,z6,z632]),(0,[z1,z2,z150,z3,z144,z5,z6]),(0,[z1,z2,z3,z166,z144,z5,z6]),(0,[z1,z633,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z38]),(0,[z1,z2,z3,z8,z217,z5,z38]),(0,[z1,z2,z634,z3,z8,z5,z6]),(0,[z1,z451,z2,z3,z8,z5,z6]),(0,[z11,z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z7,z48,z3,z8,z5]),(0,[z1,z2,z3,z635,z8,z5,z6])],[(0,[z1,z2,z3,z8,z636,z5,z6]),(0,[z117,z1,z2,z3,z8,z5,z29]),(0,[z117,z1,z2,z253,z8,z5,z6]),(0,[z1,z42,z2,z3,z8,z54,z5]),(0,[z1,z551,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z637,z5,z6]),(0,[z638,z1,z2,z3,z8,z5,z6]),(0,[z1,z182,z2,z3,z216,z5,z6])],[(0,[z24,z2,z3,z8,z76,z5,z6]),(0,[z1,z2,z3,z8,z639,z5,z6]),(0,[z1,z2,z3,z8,z5,z640,z6]),(0,[z1,z641,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z76,z5,z38]),(0,[z1,z77,z3,z8,z5,z28,z6]),(0,[z1,z2,z3,z8,z5,z642,z6]),(0,[z1,z42,z2,z253,z3,z8,z5]),(0,[z1,z2,z643,z3,z8,z5,z6]),(0,[z361,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z644,z8,z5,z6]),(0,[z1,z2,z3,z5,z92,z6,z186])],[(0,[z43,z83,z1,z3,z8,z5,z6]),(0,[z645,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z646,z3,z8,z5,z6]),(0,[z1,z2,z647,z3,z8,z5,z6]),(0,[z1,z72,z2,z3,z8,z5,z38]),(0,[z1,z120,z42,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z648,z6]),(0,[z1,z77,z2,z3,z8,z5,z38]),(0,[z1,z206,z2,z3,z8,z28,z6])]],
   [[(0,[z179,z2,z3,z33,z8,z5,z6]),(1,[z1,z2,z324,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z649,z6]),(1,[z1,z2,z3,z8,z346,z6]),(0,[z1,z2,z3,z8,z5,z650,z6]),(0,[z1,z2,z634,z3,z8,z5,z29]),(0,[z117,z1,z2,z3,z8,z23,z6]),(0,[z1,z161,z2,z3,z8,z5,z6]),(0,[z1,z2,z48,z3,z3,z8,z5]),(1,[z1,z2,z3,z166,z54,z6]),(0,[z1,z651,z2,z3,z8,z5,z6])],[(1,[z1,z2,z3,z8,z312,z6]),(0,[z130,z1,z2,z33,z8,z5,z6]),(0,[z199,z2,z3,z8,z5,z66,z6]),(0,[z1,z2,z3,z151,z8,z5,z6]),(0,[z1,z2,z3,z8,z652,z5,z6]),(0,[z1,z2,z3,z8,z133,z5,z38]),(1,[z145,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z653,z5,z6]),(0,[z497,z1,z42,z2,z3,z8,z5])],[(0,[z414,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z654,z3,z8,z5,z6]),(0,[z199,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z27,z5,z6]),(0,[z655,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z38,z38])],[(0,[z656,z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z15,z5,z28,z6])],[(0,[z1,z2,z3,z8,z5,z6,z292]),(1,[z1,z2,z140,z3,z8,z5]),(0,[z1,z2,z48,z3,z8,z54,z5])],[(0,[z53,z1,z46,z2,z3,z5,z6]),(0,[z1,z2,z48,z253,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z173,z186])],[(0,[z1,z2,z3,z158,z8,z5,z6]),(0,[z1,z2,z3,z8,z76,z5,z292]),(0,[z1,z2,z3,z151,z8,z5,z29])],[(0,[z1,z2,z3,z8,z5,z6,z294]),(0,[z78,z1,z2,z3,z8,z5,z79]),(0,[z1,z3,z144,z8,z27,z5,z6]),(0,[z1,z206,z2,z3,z8,z5,z38]),(0,[z1,z106,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z657,z5,z6]),(0,[z1,z323,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z658,z6])]],
   [[(0,[z130,z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z659,z5,z6]),(0,[z1,z77,z2,z48,z3,z8,z5]),(0,[z1,z323,z2,z3,z8,z63,z6])],[(0,[z83,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z143,z8,z5,z64,z6]),(0,[z53,z179,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z660,z8,z5,z6]),(0,[z1,z46,z183,z3,z8,z5,z6])],[(0,[z0,z1,z2,z3,z8,z312,z6]),(0,[z661,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z662,z6]),(0,[z1,z663,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z664,z8,z5,z6]),(0,[z1,z2,z48,z3,z201,z8,z5]),(0,[z1,z2,z3,z8,z5,z93,z6])],[(0,[z665,z1,z2,z3,z8,z5,z6]),(0,[z91,z1,z2,z48,z3,z8,z5]),(0,[z1,z42,z2,z48,z8,z5,z6]),(0,[z1,z2,z3,z8,z666,z5,z6])],[(0,[z1,z2,z21,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z667,z5,z6]),(0,[z395,z1,z2,z3,z8,z5,z6]),(0,[z394,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z634,z3,z8,z5]),(0,[z1,z42,z2,z3,z8,z5,z51]),(0,[z1,z2,z3,z8,z5,z186,z51])],[(0,[z1,z2,z3,z8,z668,z5,z6]),(0,[z1,z89,z2,z3,z8,z5,z6]),(1,[z1,z2,z150,z110,z5,z6]),(0,[z1,z2,z669,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z670,z5,z6])],[(0,[z1,z2,z3,z18,z27,z5,z6]),(0,[z671,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z38,z181]),(0,[z1,z182,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z616,z63,z5]),(0,[z1,z2,z3,z8,z5,z672,z6])],[(0,[z1,z2,z48,z3,z8,z5,z79]),(0,[z1,z673,z2,z3,z8,z5,z6]),(0,[z1,z2,z48,z3,z8,z5,z23])]],
   [[(0,[z1,z2,z3,z8,z674,z5,z6]),(0,[z1,z675,z2,z3,z8,z5,z6]),(0,[z179,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z676,z5,z6]),(0,[z1,z2,z677,z3,z8,z5,z6]),(0,[z1,z106,z2,z48,z3,z8,z5]),(0,[z678,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z21,z3,z8,z5,z29]),(0,[z1,z2,z3,z679,z8,z5,z6]),(0,[z1,z2,z680,z3,z8,z5,z6]),(0,[z381,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z681]),(0,[z1,z2,z3,z8,z5,z131,z6]),(0,[z1,z2,z143,z151,z8,z5,z6]),(1,[z1,z2,z3,z8,z549,z6])],[(0,[z83,z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z29,z186])],[(0,[z69,z1,z2,z143,z8,z5,z6]),(0,[z1,z2,z3,z682,z8,z5,z6]),(0,[z1,z516,z2,z3,z5,z23,z6])],[(0,[z78,z1,z2,z3,z8,z5,z6]),(1,[z117,z1,z2,z8,z23,z6]),(0,[z1,z42,z107,z2,z3,z8,z5]),(0,[z1,z42,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z683,z6]),(0,[z53,z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z150,z3,z63,z5,z6]),(0,[z326,z1,z2,z48,z3,z8,z5])],[(1,[z1,z473,z2,z3,z8,z5]),(0,[z2,z3,z8,z76,z5,z75,z6]),(0,[z1,z2,z3,z8,z421,z5,z6]),(1,[z1,z2,z8,z5,z577,z6]),(0,[z1,z2,z3,z8,z5,z6,z684])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z19,z5,z38]),(0,[z78,z2,z3,z8,z5,z6,z79]),(0,[z1,z42,z2,z3,z110,z8,z5]),(0,[z1,z685,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z3,z216,z8,z5]),(0,[z1,z2,z48,z3,z8,z637,z5])]],
   [[(0,[z1,z686,z2,z3,z8,z5,z6]),(1,[z1,z2,z410,z3,z8,z5]),(0,[z1,z2,z3,z8,z687,z5,z6]),(0,[z1,z2,z3,z110,z8,z5,z6]),(0,[z1,z2,z3,z110,z8,z5,z287]),(0,[z1,z2,z3,z688,z8,z5,z6])],[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z1,z689,z2,z3,z8,z5,z6]),(0,[z1,z42,z2,z3,z8,z5,z29]),(1,[z1,z42,z2,z3,z8,z5]),(0,[z1,z2,z48,z3,z8,z108,z5])],[(0,[z1,z2,z3,z8,z690,z5,z6]),(0,[z1,z451,z2,z3,z8,z63,z5]),(0,[z1,z2,z3,z691,z8,z5,z6]),(0,[z1,z2,z8,z5,z577,z16,z6]),(0,[z1,z2,z692,z3,z8,z5,z6])],[(0,[z1,z2,z3,z693,z8,z5,z6]),(0,[z1,z2,z624,z3,z8,z5,z6]),(0,[z694,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z695,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z79]),(0,[z696,z1,z2,z3,z8,z5,z6]),(0,[z1,z106,z3,z8,z5,z6,z38]),(0,[z1,z3,z8,z5,z29,z6,z38])],[(0,[z0,z83,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z697,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z270]),(0,[z1,z2,z47,z3,z8,z5,z38]),(0,[z1,z2,z615,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z698,z6]),(0,[z1,z2,z3,z8,z5,z699,z6]),(1,[z1,z398,z3,z8,z5,z6]),(0,[z1,z2,z700,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z566,z5,z6]),(0,[z1,z473,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z701,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z702,z6]),(0,[z703,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z39]),(0,[z117,z1,z2,z3,z8,z15,z6]),(0,[z53,z1,z2,z48,z3,z8,z5]),(0,[z704,z1,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z8,z54,z6]),(0,[z1,z2,z3,z8,z5,z6,z705])],[(0,[z1,z2,z48,z3,z8,z76,z5]),(1,[z1,z2,z3,z8,z5,z297]),(0,[z1,z2,z3,z8,z690,z5,z29]),(0,[z1,z2,z3,z8,z5,z706,z6]),(0,[z1,z46,z2,z253,z3,z8,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z381,z1,z151,z8,z5,z6]),(0,[z1,z206,z48,z3,z8,z15]),(0,[z1,z398,z3,z8,z5,z157]),(0,[z1,z2,z707,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z708]),(0,[z1,z2,z3,z8,z5,z709])],[(0,[z1,z2,z3,z710,z5,z6]),(0,[z179,z2,z48,z3,z18,z5]),(0,[z1,z2,z256,z216,z8,z5]),(0,[z1,z42,z2,z3,z277,z5])],[(0,[z1,z2,z3,z8,z5,z711]),(0,[z69,z342,z2,z33,z8,z6]),(0,[z1,z2,z712,z3,z8,z5]),(0,[z1,z2,z3,z8,z713,z5])],[(0,[z1,z714,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z715]),(0,[z1,z2,z3,z716,z5,z6]),(0,[z1,z2,z3,z8,z5,z717]),(0,[z718,z2,z3,z8,z5,z6]),(0,[z117,z1,z516,z2,z3,z6]),(0,[z1,z46,z2,z577,z16,z6])],[(0,[z1,z2,z3,z8,z5,z719])],[(0,[z1,z2,z3,z8,z5,z720]),(0,[z1,z42,z2,z8,z5,z721])],[(0,[z1,z2,z3,z216,z386,z5]),(0,[z1,z722,z2,z3,z8,z5]),(0,[z1,z206,z3,z8,z723,z6]),(0,[z91,z1,z3,z8,z5,z724]),(0,[z1,z183,z3,z8,z5,z725])],[(0,[z1,z2,z3,z8,z726,z6]),(0,[z727,z2,z48,z3,z8,z5])],[],[(0,[z1,z2,z3,z8,z728,z6]),(0,[z1,z62,z3,z27,z5,z355]),(0,[z328,z1,z2,z8,z28,z6]),(0,[z117,z1,z516,z2,z5,z6])],[(0,[z1,z2,z3,z8,z5,z729]),(0,[z1,z42,z70,z65,z8,z5]),(0,[z1,z2,z3,z8,z5,z169]),(0,[z1,z2,z730,z3,z8,z5])],[(0,[z381,z1,z65,z8,z5,z6]),(0,[z414,z1,z42,z2,z3,z5]),(0,[z1,z731,z2,z3,z5,z6]),(0,[z89,z3,z8,z80,z28,z6]),(0,[z1,z732,z2,z3,z8,z5]),(0,[z145,z2,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z733]),(0,[z1,z2,z398,z3,z16,z6])],[(0,[z1,z3,z306,z13,z5,z6]),(0,[z1,z2,z3,z8,z5,z734]),(0,[z1,z2,z3,z5,z38,z735]),(1,[z1,z398,z3,z16,z6])],[(0,[z1,z2,z3,z8,z6,z736]),(0,[z1,z737,z2,z3,z5,z38]),(0,[z53,z1,z42,z2,z63,z5])]],
   [[(0,[z1,z206,z3,z8,z15,z38]),(0,[z1,z72,z2,z110,z8,z5]),(0,[z53,z1,z2,z63,z5,z6])],[(0,[z1,z2,z738,z3,z8,z5]),(0,[z1,z77,z3,z144,z5,z6]),(0,[z1,z46,z398,z3,z16,z6]),(0,[z1,z2,z3,z8,z5,z739])],[(0,[z1,z2,z3,z4,z5,z246]),(0,[z414,z342,z1,z2,z3,z6]),(0,[z1,z2,z740,z3,z8,z5]),(0,[z727,z2,z47,z3,z8,z5]),(0,[z1,z323,z2,z3,z8,z38])],[(0,[z328,z1,z2,z8,z5,z38]),(0,[z1,z2,z3,z216,z5,z146])],[(0,[z1,z42,z2,z3,z8,z298]),(0,[z1,z741,z3,z8,z5,z6]),(0,[z43,z1,z742,z8,z5,z6]),(0,[z117,z1,z516,z2,z23,z6])],[(0,[z611,z2,z3,z8,z5,z614])],[(0,[z1,z2,z158,z8,z5,z38]),(0,[z117,z1,z42,z2,z8,z23])],[(0,[z1,z2,z3,z8,z5,z743]),(0,[z1,z2,z3,z744,z5,z6])],[(0,[z1,z2,z3,z8,z745,z6]),(0,[z1,z2,z3,z8,z5,z746])],[(0,[z1,z2,z8,z5,z93,z577])],[(0,[z1,z2,z214,z3,z8,z5]),(0,[z1,z2,z3,z8,z26,z300]),(0,[z1,z2,z253,z8,z501,z6])],[(0,[z1,z373,z3,z8,z28,z6]),(0,[z117,z1,z2,z8,z271,z6]),(0,[z1,z2,z3,z8,z5,z747]),(0,[z1,z42,z2,z8,z5,z188]),(0,[z1,z2,z3,z216,z5,z417])],[(0,[z1,z2,z3,z8,z5,z748]),(0,[z1,z2,z3,z385,z5,z211]),(0,[z1,z72,z2,z48,z8,z5]),(0,[z207,z2,z3,z8,z5,z29]),(0,[z1,z2,z8,z5,z6,z749])],[(0,[z1,z2,z3,z8,z750,z6]),(0,[z751,z1,z2,z3,z8,z5]),(0,[z1,z2,z8,z5,z577,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z414,z179,z2,z3,z5,z6]),(0,[z1,z106,z214,z3,z8,z5]),(0,[z1,z377,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z752]),(0,[z1,z42,z2,z3,z8,z753])],[(0,[z1,z2,z3,z5,z754,z6]),(0,[z1,z2,z3,z8,z755,z6]),(0,[z1,z62,z48,z3,z27,z5])]],
   [[(0,[z130,z2,z143,z8,z5,z38]),(0,[z117,z1,z2,z8,z23,z29])],[(0,[z1,z2,z48,z134,z8,z5]),(0,[z1,z2,z3,z8,z5,z756]),(0,[z1,z2,z8,z5,z757,z6]),(0,[z1,z2,z3,z8,z758,z5])],[],[(0,[z1,z373,z3,z8,z5,z38]),(0,[z1,z2,z759,z3,z8,z5]),(0,[z1,z2,z48,z422,z8,z5]),(0,[z1,z2,z634,z8,z5,z593])],[(0,[z1,z65,z3,z201,z8,z5]),(0,[z1,z2,z3,z8,z5,z760])],[],[(0,[z1,z2,z761,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z762]),(0,[z1,z2,z3,z8,z5,z297]),(0,[z43,z1,z290,z151,z8,z5]),(0,[z1,z70,z65,z8,z5,z297]),(0,[z1,z46,z2,z3,z16,z6]),(0,[z328,z1,z2,z54,z5,z6])],[(0,[z1,z2,z3,z8,z5,z763]),(1,[z2,z3,z764,z5,z6]),(0,[z199,z2,z36,z8,z5,z66]),(0,[z1,z77,z214,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z260])],[(0,[z1,z3,z13,z8,z5,z6]),(0,[z1,z2,z765,z3,z8,z6]),(0,[z1,z2,z3,z8,z766,z6]),(0,[z767,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z723,z28,z6]),(0,[z1,z768,z3,z8,z5,z6])],[(0,[z342,z1,z2,z3,z8,z38]),(0,[z1,z42,z2,z3,z8,z26]),(0,[z769,z1,z2,z3,z8,z5])],[(0,[z1,z770,z3,z13,z8,z5]),(0,[z1,z2,z3,z8,z5,z771])],[(0,[z1,z2,z3,z8,z5,z772]),(0,[z94,z2,z3,z8,z773,z6])],[(0,[z1,z2,z36,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z35]),(0,[z1,z2,z253,z442,z8,z6])],[(0,[z1,z72,z2,z65,z8,z5])],[(0,[z381,z1,z473,z3,z8,z5]),(0,[z727,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z774,z5,z6]),(0,[z1,z2,z3,z8,z775,z6])],[(0,[z0,z21,z3,z8,z5,z29]),(0,[z381,z1,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z776]),(0,[z1,z106,z3,z8,z5,z38]),(0,[z1,z2,z8,z133,z706,z6])]],
   [[(0,[z1,z2,z777,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z778]),(0,[z1,z2,z3,z779,z5,z6])],[(1,[z1,z3,z779,z5,z6]),(0,[z780,z1,z2,z8,z5,z6]),(0,[z1,z89,z3,z124,z28,z6]),(0,[z1,z46,z2,z3,z93,z16])],[(0,[z781,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z424,z29])],[(0,[z0,z21,z134,z8,z5,z6]),(0,[z1,z2,z782,z3,z8,z5]),(0,[z342,z1,z3,z13,z8,z6]),(0,[z1,z2,z48,z3,z306,z5]),(0,[z304,z2,z143,z8,z5,z6]),(0,[z1,z2,z253,z8,z133,z38])],[(0,[z2,z3,z8,z773,z75,z6])],[(0,[z1,z2,z3,z4,z298,z6]),(0,[z1,z2,z3,z783,z5,z6]),(0,[z1,z784,z2,z3,z8,z5]),(0,[z1,z323,z42,z2,z3,z8]),(0,[z1,z2,z172,z3,z8,z785])],[(0,[z1,z2,z786,z8,z5,z6]),(0,[z1,z2,z3,z787,z5,z6])],[(0,[z1,z2,z3,z8,z5,z294])],[(0,[z1,z2,z3,z8,z5,z788]),(1,[z2,z3,z8,z5,z789]),(0,[z1,z62,z3,z27,z26,z6]),(0,[z1,z2,z3,z8,z5,z790]),(0,[z1,z2,z3,z8,z5,z791]),(0,[z220,z107,z2,z3,z8,z5])],[(1,[z792,z3,z8,z5,z6]),(0,[z414,z1,z2,z3,z5,z38]),(0,[z1,z3,z8,z5,z793,z6]),(0,[z1,z2,z3,z8,z5,z794]),(0,[z2,z3,z8,z5,z38,z795]),(0,[z1,z2,z3,z8,z5,z796])],[(0,[z1,z2,z3,z8,z5,z797])],[],[(0,[z1,z2,z3,z8,z798,z6]),(0,[z1,z2,z799,z8,z5,z6]),(0,[z1,z2,z3,z102,z8,z6]),(0,[z1,z2,z3,z8,z5,z800])],[(0,[z1,z2,z3,z801,z8,z5]),(0,[z1,z802,z3,z8,z5,z6]),(0,[z1,z77,z3,z779,z5,z6])],[(0,[z1,z2,z803,z3,z8,z5])],[(0,[z1,z70,z742,z8,z5,z6]),(0,[z1,z2,z804,z3,z8,z5]),(0,[z805,z2,z3,z8,z5,z6]),(0,[z117,z1,z2,z140,z8,z23]),(0,[z1,z398,z3,z166,z5,z6])]],
   [[(0,[z1,z2,z3,z5,z806,z186])],[(0,[z1,z2,z48,z253,z8,z133])],[(0,[z1,z2,z3,z8,z5,z807]),(0,[z1,z2,z3,z808,z5,z6])],[(0,[z1,z2,z3,z8,z5,z809])],[(0,[z1,z2,z810,z3,z8,z5]),(0,[z43,z1,z410,z151,z8,z5])],[(0,[z1,z42,z2,z811,z8,z5]),(0,[z1,z2,z3,z812,z5,z6]),(0,[z1,z2,z3,z8,z813,z6]),(0,[z1,z2,z3,z814,z8,z5])],[(0,[z53,z1,z2,z815,z5,z6])],[(0,[z1,z816,z2,z3,z8,z6]),(0,[z1,z42,z2,z147,z8,z5]),(0,[z1,z2,z817,z8,z5,z6]),(0,[z818,z2,z48,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z819]),(0,[z1,z2,z3,z8,z820,z6])],[(0,[z1,z2,z158,z8,z5,z29]),(0,[z145,z42,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z26,z355]),(0,[z1,z2,z3,z5,z6,z735]),(0,[z1,z2,z3,z311,z5,z186])],[],[(0,[z1,z2,z3,z8,z5,z821]),(0,[z0,z42,z21,z3,z8,z5]),(0,[z1,z2,z33,z8,z5,z131]),(0,[z342,z1,z42,z2,z3,z8]),(0,[z822,z1,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z823,z6]),(0,[z467,z2,z253,z3,z8,z6]),(0,[z53,z1,z398,z3,z5,z6]),(0,[z1,z2,z48,z8,z5,z589])],[(0,[z1,z2,z3,z8,z5,z824]),(0,[z492,z2,z3,z18,z5,z6]),(0,[z1,z42,z2,z428,z8,z5])],[(0,[z1,z2,z3,z8,z825,z6]),(0,[z1,z2,z3,z826,z5,z6]),(0,[z1,z2,z172,z3,z8,z160]),(0,[z1,z2,z48,z692,z8,z5])]],
   [[(0,[z1,z2,z3,z8,z5,z827]),(0,[z1,z42,z2,z184,z8,z5]),(1,[z1,z2,z8,z757,z6])],[(0,[z1,z2,z3,z8,z5,z828]),(0,[z1,z2,z3,z8,z5,z829])],[(0,[z1,z3,z8,z830,z5,z6]),(0,[z1,z831,z2,z3,z8,z5]),(0,[z1,z484,z3,z8,z5,z38])],[(0,[z1,z2,z3,z8,z5,z119]),(0,[z0,z21,z3,z8,z312,z6]),(0,[z1,z2,z832,z3,z8,z5]),(0,[z1,z125,z3,z8,z5,z29]),(0,[z1,z2,z833,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z725])],[(0,[z130,z2,z532,z8,z5,z6]),(0,[z1,z62,z3,z779,z5,z6]),(0,[z467,z2,z3,z8,z5,z38])],[(0,[z1,z2,z834,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z835]),(0,[z1,z2,z3,z8,z5,z836]),(0,[z78,z50,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z837])],[(0,[z342,z1,z2,z3,z306,z6]),(0,[z1,z2,z3,z8,z5,z838]),(0,[z1,z2,z3,z8,z5,z839]),(0,[z1,z183,z3,z8,z5,z29]),(0,[z1,z2,z110,z5,z550,z6])],[(0,[z1,z2,z3,z8,z5,z840]),(0,[z1,z42,z2,z444,z8,z5]),(0,[z1,z2,z3,z8,z5,z841]),(0,[z2,z3,z8,z5,z80,z709]),(0,[z1,z2,z48,z8,z5,z609])],[(0,[z1,z2,z3,z566,z5,z119]),(0,[z1,z2,z3,z8,z842,z6]),(0,[z1,z2,z3,z8,z5,z843]),(0,[z207,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z844])],[(0,[z1,z42,z2,z3,z8,z346])],[],[(0,[z2,z3,z8,z5,z66,z789]),(0,[z2,z3,z8,z5,z845,z29]),(0,[z117,z1,z2,z8,z426,z6])],[(0,[z1,z2,z3,z104,z5,z6]),(0,[z1,z70,z65,z104,z5,z6]),(0,[z1,z2,z3,z8,z507,z211]),(0,[z1,z2,z3,z8,z846,z6]),(0,[z1,z2,z150,z110,z5,z260])],[(0,[z1,z847,z2,z3,z8,z5]),(0,[z1,z2,z3,z104,z71,z6])],[(0,[z1,z163,z3,z8,z5,z38])],[(0,[z2,z3,z8,z5,z848,z6]),(0,[z117,z1,z2,z261,z23,z6])]],
   [[(0,[z1,z2,z849,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z850])],[(0,[z1,z2,z3,z8,z5,z851]),(0,[z1,z72,z2,z8,z5,z30])],[(0,[z1,z2,z3,z8,z5,z852]),(0,[z381,z1,z3,z8,z5,z29]),(0,[z1,z42,z2,z3,z385,z5]),(0,[z1,z2,z3,z8,z5,z853]),(0,[z1,z2,z3,z775,z16,z6])],[(0,[z1,z2,z3,z8,z5,z854]),(0,[z1,z2,z855,z8,z5,z6])],[(0,[z1,z42,z2,z210,z8,z5]),(0,[z1,z42,z2,z36,z8,z5]),(0,[z1,z42,z2,z3,z8,z856])],[(0,[z83,z24,z3,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z857]),(0,[z1,z2,z3,z8,z757,z6]),(0,[z1,z2,z858,z3,z8,z5])],[(0,[z1,z859,z2,z3,z8,z6]),(0,[z1,z2,z410,z143,z8,z5]),(0,[z1,z695,z3,z8,z5,z29]),(0,[z1,z2,z3,z245,z5,z604])],[(0,[z1,z2,z3,z8,z860,z6]),(0,[z1,z42,z2,z143,z8,z5]),(0,[z1,z3,z8,z5,z861,z6]),(0,[z1,z2,z3,z8,z5,z862]),(0,[z1,z2,z3,z8,z863,z6])],[(0,[z1,z2,z3,z8,z5,z864]),(0,[z1,z2,z324,z3,z102,z8]),(0,[z41,z42,z2,z3,z8,z76]),(0,[z1,z89,z3,z8,z28,z38]),(0,[z1,z2,z48,z8,z338,z5])],[(0,[z43,z1,z158,z8,z5,z6]),(0,[z43,z1,z151,z8,z5,z29]),(0,[z1,z2,z865,z3,z8,z5])],[(0,[z1,z2,z3,z8,z298,z119]),(0,[z1,z2,z3,z8,z71,z297]),(0,[z1,z866,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z6,z867])],[(0,[z381,z414,z1,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z868]),(0,[z1,z62,z42,z3,z27,z5]),(0,[z1,z2,z3,z348,z5,z146]),(0,[z1,z46,z2,z251,z3,z6])],[(0,[z381,z1,z3,z8,z5,z864]),(0,[z1,z2,z3,z869,z8,z5]),(0,[z1,z2,z3,z81,z54,z6]),(0,[z818,z2,z3,z8,z5,z6])],[(0,[z1,z2,z158,z8,z312,z6]),(0,[z1,z2,z3,z8,z5,z870]),(0,[z1,z2,z172,z3,z8,z51])],[(0,[z1,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z871,z5,z6]),(0,[z1,z70,z65,z8,z5,z38])],[(0,[z0,z792,z3,z8,z5,z6]),(0,[z1,z2,z872,z8,z5,z6]),(0,[z1,z2,z3,z8,z71,z38]),(0,[z1,z42,z206,z3,z8,z15]),(0,[z1,z2,z3,z5,z261,z29])]],
   [[(0,[z1,z2,z48,z3,z4,z5]),(0,[z1,z2,z3,z8,z5,z873]),(0,[z1,z120,z70,z65,z8,z5]),(0,[z1,z437,z2,z3,z5,z52]),(0,[z1,z2,z3,z8,z5,z874]),(0,[z1,z183,z3,z8,z5,z157])],[(0,[z1,z2,z3,z8,z5,z875]),(0,[z1,z2,z3,z8,z5,z876])],[(0,[z1,z2,z877,z3,z8,z5]),(0,[z1,z878,z2,z3,z8,z5]),(0,[z1,z42,z2,z8,z5,z412])],[(0,[z1,z2,z3,z566,z5,z38]),(0,[z1,z2,z3,z8,z29,z736]),(0,[z1,z451,z2,z3,z8,z5]),(0,[z326,z1,z2,z3,z8,z356])],[(0,[z1,z2,z3,z8,z5,z879]),(0,[z414,z1,z2,z324,z3,z5]),(0,[z1,z42,z2,z479,z8,z5]),(0,[z880,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z881]),(0,[z199,z2,z3,z8,z5,z97]),(0,[z2,z3,z8,z5,z6,z795])],[],[(0,[z1,z2,z3,z882,z5,z6])],[(0,[z792,z21,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z883]),(0,[z1,z2,z3,z884,z5,z6]),(0,[z1,z2,z3,z166,z259,z6])],[(0,[z1,z2,z3,z8,z5,z885])],[],[(0,[z1,z62,z3,z27,z5,z38]),(0,[z1,z42,z2,z8,z5,z254])],[(0,[z1,z2,z3,z886,z8,z5]),(0,[z1,z2,z615,z3,z8,z411]),(0,[z1,z398,z3,z8,z5,z887])],[(0,[z1,z2,z888,z8,z5,z6]),(0,[z889,z2,z3,z8,z5,z6]),(0,[z1,z2,z890,z8,z5,z29])],[(0,[z381,z1,z42,z33,z8,z5]),(0,[z1,z2,z3,z8,z891,z6]),(0,[z199,z2,z366,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z208])],[(0,[z1,z2,z3,z277,z28,z6])]],
   [[(0,[z1,z2,z8,z892,z5,z6]),(0,[z1,z42,z2,z102,z33,z8]),(0,[z1,z2,z324,z3,z306,z5]),(0,[z1,z2,z893,z3,z8,z5]),(1,[z1,z3,z277,z28,z6]),(0,[z117,z1,z398,z3,z8,z6])],[(0,[z1,z2,z3,z306,z5,z38]),(0,[z41,z2,z3,z8,z76,z35]),(0,[z1,z77,z3,z144,z5,z169]),(0,[z1,z42,z2,z255,z8,z5])],[(0,[z1,z89,z48,z3,z8,z28]),(1,[z53,z1,z323,z2,z6])],[(0,[z894,z1,z2,z3,z5,z6])],[],[(0,[z1,z2,z3,z8,z298,z38]),(0,[z1,z2,z3,z8,z5,z895])],[(0,[z414,z1,z3,z13,z5,z6]),(0,[z1,z2,z896,z8,z5,z6]),(0,[z1,z2,z3,z897,z8,z5]),(0,[z1,z206,z3,z8,z15,z29]),(0,[z1,z2,z253,z8,z133,z208])],[(0,[z1,z2,z3,z898,z8,z5]),(0,[z1,z2,z3,z8,z5,z899]),(0,[z1,z2,z3,z8,z900,z5]),(0,[z1,z2,z3,z8,z6,z901])],[(0,[z130,z2,z902,z8,z5,z6]),(0,[z1,z323,z2,z3,z8,z29]),(0,[z1,z2,z3,z8,z215,z173])],[(0,[z94,z2,z3,z8,z75,z6]),(0,[z1,z903,z2,z3,z8,z6]),(0,[z1,z2,z3,z8,z904,z6]),(0,[z1,z65,z742,z8,z5,z6]),(0,[z1,z905,z2,z8,z5,z38]),(0,[z328,z1,z2,z8,z5,z29])],[(0,[z1,z2,z3,z8,z906,z6]),(0,[z69,z2,z33,z8,z5,z38]),(0,[z1,z227,z2,z48,z8,z5]),(0,[z1,z2,z3,z201,z8,z5]),(0,[z907,z42,z2,z3,z8,z5]),(0,[z1,z2,z3,z216,z637,z5])],[(0,[z40,z2,z3,z19,z5,z38]),(0,[z1,z89,z42,z3,z8,z28]),(0,[z1,z2,z3,z8,z5,z908]),(0,[z1,z46,z183,z3,z16,z6])],[(0,[z1,z2,z909,z3,z8,z5]),(0,[z1,z42,z2,z3,z8,z71])],[(0,[z414,z1,z42,z2,z33,z5]),(0,[z1,z177,z3,z27,z5,z6]),(0,[z1,z2,z3,z8,z5,z910])],[(0,[z1,z2,z256,z8,z5,z38]),(0,[z1,z911,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z912])]],
   [[(0,[z1,z2,z913,z8,z5,z6]),(0,[z2,z3,z18,z764,z5,z6])],[],[(0,[z1,z2,z3,z8,z914,z6]),(0,[z1,z2,z3,z4,z5,z119])],[(0,[z1,z2,z3,z8,z5,z915]),(0,[z328,z1,z2,z48,z8,z5])],[(0,[z1,z42,z2,z3,z8,z312]),(0,[z1,z916,z2,z3,z8,z6])],[(0,[z1,z516,z2,z3,z5,z6]),(0,[z1,z2,z48,z3,z166,z54])],[(0,[z130,z2,z143,z8,z5,z29]),(0,[z1,z917,z3,z8,z5,z6])],[(0,[z344,z2,z33,z8,z5,z6]),(0,[z1,z42,z2,z8,z529,z5]),(0,[z1,z2,z3,z8,z5,z918])],[(0,[z1,z919,z3,z13,z8,z5]),(0,[z1,z2,z3,z8,z5,z920]),(0,[z1,z921,z2,z8,z5,z6])],[(0,[z1,z2,z3,z922,z8,z6]),(0,[z1,z42,z77,z3,z144,z5]),(0,[z1,z923,z2,z3,z8,z5])],[(0,[z1,z2,z3,z924,z5,z6])],[],[(0,[z1,z2,z3,z925,z8,z5]),(0,[z1,z2,z3,z8,z507,z6]),(0,[z1,z2,z48,z3,z277,z5]),(0,[z1,z2,z3,z8,z5,z287])],[],[(0,[z1,z2,z3,z8,z5,z926]),(0,[z1,z2,z3,z8,z5,z927]),(0,[z395,z2,z3,z8,z5,z97])],[(0,[z1,z2,z3,z928,z8,z5]),(0,[z342,z1,z2,z3,z8,z29]),(0,[z1,z2,z3,z385,z5,z6]),(0,[z1,z70,z65,z385,z5,z6]),(0,[z1,z462,z3,z144,z5,z6]),(0,[z1,z2,z3,z8,z5,z929]),(0,[z1,z2,z3,z8,z5,z930]),(0,[z1,z2,z3,z8,z319,z173])]],
   [[(0,[z1,z2,z3,z385,z71,z6]),(0,[z1,z454,z3,z27,z5,z6]),(0,[z1,z2,z8,z5,z38,z931]),(0,[z145,z2,z48,z3,z8,z5]),(1,[z117,z1,z516,z2,z6]),(0,[z1,z2,z48,z554,z8,z5])],[(0,[z1,z2,z3,z8,z5,z29]),(0,[z1,z932,z2,z3,z8,z5]),(0,[z2,z3,z8,z933,z5,z6]),(0,[z1,z70,z65,z8,z5,z29]),(0,[z1,z2,z48,z8,z5,z721])],[(0,[z69,z414,z2,z33,z5,z6])],[(0,[z1,z2,z150,z110,z5,z38]),(0,[z117,z1,z2,z111,z8,z6])],[(0,[z1,z2,z934,z8,z5,z6]),(0,[z1,z935,z2,z3,z5,z6]),(0,[z1,z3,z8,z5,z29,z38]),(0,[z1,z42,z2,z634,z8,z5])],[(0,[z1,z2,z134,z8,z5,z6]),(0,[z1,z936,z2,z3,z8,z5]),(0,[z497,z357,z2,z3,z8,z5])],[(0,[z1,z2,z3,z566,z5,z29]),(0,[z1,z2,z634,z8,z5,z64]),(0,[z1,z2,z3,z8,z5,z305])],[(0,[z1,z2,z3,z937,z5,z6]),(0,[z1,z2,z3,z8,z549,z38]),(0,[z1,z46,z2,z3,z426,z6])],[(0,[z1,z72,z2,z33,z8,z5]),(0,[z1,z77,z48,z3,z144,z5])],[(0,[z1,z2,z253,z8,z133,z29]),(0,[z1,z46,z2,z48,z3,z16])],[(0,[z1,z2,z134,z566,z5,z6]),(0,[z1,z2,z3,z8,z5,z938])],[(0,[z939,z1,z3,z8,z5,z6]),(0,[z328,z1,z2,z8,z15,z6]),(0,[z1,z3,z8,z5,z724,z38]),(0,[z1,z2,z562,z3,z8,z160]),(0,[z1,z398,z3,z8,z54,z6])],[(0,[z1,z2,z3,z8,z940,z6]),(0,[z1,z2,z8,z5,z577,z38]),(0,[z1,z398,z3,z8,z5,z113]),(0,[z1,z2,z3,z5,z92,z806])],[(0,[z1,z2,z3,z4,z5,z38]),(1,[z1,z742,z8,z5,z6]),(0,[z372,z2,z366,z3,z8,z5])],[(0,[z1,z2,z803,z158,z8,z5]),(0,[z1,z2,z48,z3,z8,z298]),(0,[z1,z120,z214,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z941]),(0,[z1,z2,z253,z8,z133,z305])],[(0,[z414,z1,z2,z3,z5,z29]),(0,[z1,z2,z3,z8,z5,z942]),(0,[z1,z551,z47,z3,z8,z5])]],
   [[(0,[z1,z2,z3,z943,z5,z6])],[(0,[z1,z2,z811,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z944]),(0,[z945,z1,z2,z3,z8,z5])],[(0,[z946,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z152]),(0,[z1,z2,z947,z3,z8,z5]),(0,[z1,z453,z3,z8,z15,z6])],[(0,[z1,z2,z3,z948,z8,z6]),(0,[z342,z1,z2,z324,z3,z8]),(0,[z1,z2,z3,z8,z5,z949])],[(0,[z1,z2,z3,z306,z5,z29]),(0,[z1,z42,z2,z115,z8,z5])],[(0,[z1,z2,z3,z950,z5,z6]),(0,[z1,z2,z3,z8,z951,z6]),(0,[z1,z3,z27,z28,z16,z6])],[(0,[z952,z1,z2,z3,z8,z6]),(0,[z1,z206,z3,z277,z5,z6]),(0,[z1,z321,z3,z8,z5,z29]),(0,[z53,z1,z323,z2,z8,z6])],[(0,[z1,z3,z13,z8,z5,z38]),(0,[z1,z953,z3,z8,z5,z6]),(0,[z767,z2,z3,z8,z5,z38])],[(0,[z1,z2,z954,z8,z5,z6]),(0,[z1,z2,z3,z8,z298,z29]),(0,[z40,z2,z3,z764,z5,z6]),(0,[z1,z280,z3,z8,z5,z29])],[(0,[z1,z2,z3,z8,z955,z6]),(0,[z1,z89,z3,z8,z28,z90])],[(0,[z1,z956,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z26,z38])],[(0,[z1,z2,z36,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z957]),(0,[z1,z2,z3,z8,z690,z155]),(0,[z1,z2,z3,z8,z5,z157])],[(0,[z1,z2,z134,z8,z298,z6]),(0,[z1,z398,z48,z3,z8,z5]),(0,[z1,z182,z2,z3,z5,z806])],[(0,[z69,z2,z902,z8,z5,z6]),(0,[z727,z2,z3,z8,z5,z38])],[(0,[z958,z1,z2,z8,z5,z6]),(0,[z1,z523,z3,z8,z5,z38]),(0,[z1,z3,z8,z5,z429,z38]),(0,[z1,z2,z290,z3,z8,z5]),(0,[z1,z182,z2,z3,z5,z52]),(0,[z53,z1,z323,z2,z3,z6]),(0,[z1,z42,z959,z3,z8,z5]),(0,[z1,z2,z3,z960,z8,z5])],[(0,[z1,z2,z3,z8,z5,z961]),(0,[z179,z2,z3,z18,z5,z6]),(0,[z41,z2,z48,z3,z8,z76]),(0,[z1,z2,z3,z8,z5,z962]),(0,[z1,z2,z3,z8,z5,z90])]],
   [[(0,[z963,z2,z3,z8,z5,z6])],[(0,[z78,z2,z3,z8,z5,z789]),(0,[z1,z2,z256,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z964])],[(0,[z965,z1,z2,z3,z8,z5])],[(0,[z41,z2,z3,z8,z76,z38]),(0,[z11,z2,z3,z8,z5,z79]),(0,[z1,z2,z48,z3,z8,z26])],[(0,[z1,z2,z966,z3,z8,z5]),(0,[z1,z42,z2,z3,z566,z5]),(0,[z1,z2,z3,z8,z346,z6]),(0,[z2,z3,z8,z5,z80,z38]),(0,[z1,z2,z3,z166,z54,z6])],[(0,[z1,z2,z3,z8,z312,z6]),(0,[z2,z3,z8,z76,z298,z6]),(0,[z1,z2,z3,z8,z967,z6]),(0,[z1,z3,z102,z13,z8,z6]),(0,[z1,z120,z2,z634,z8,z5]),(0,[z1,z323,z2,z3,z8,z616])],[(0,[z1,z2,z3,z968,z5,z6]),(0,[z1,z2,z3,z124,z5,z38]),(0,[z53,z1,z2,z616,z63,z5])],[(0,[z1,z2,z3,z764,z5,z6]),(0,[z1,z2,z969,z3,z8,z6]),(0,[z1,z970,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z971])],[(0,[z1,z65,z617,z8,z5,z6]),(0,[z1,z2,z3,z8,z38,z972]),(0,[z1,z42,z398,z3,z8,z5]),(0,[z1,z2,z973,z3,z8,z5]),(0,[z328,z1,z2,z128,z8,z5])],[(0,[z1,z2,z3,z8,z773,z6]),(0,[z394,z2,z3,z8,z5,z79]),(0,[z1,z2,z974,z3,z8,z5]),(0,[z1,z174,z3,z8,z5,z38]),(0,[z1,z2,z975,z3,z8,z5])],[(0,[z1,z976,z2,z3,z8,z5]),(0,[z1,z2,z3,z277,z5,z38]),(0,[z467,z2,z3,z8,z5,z29]),(0,[z1,z2,z977,z8,z5,z6])],[(0,[z1,z2,z3,z978,z5,z6]),(0,[z1,z2,z3,z102,z8,z38]),(0,[z1,z120,z2,z143,z8,z5]),(0,[z1,z42,z2,z366,z8,z5]),(0,[z1,z2,z3,z8,z217,z457])],[(0,[z342,z1,z42,z2,z33,z8]),(0,[z1,z2,z3,z8,z5,z979]),(0,[z1,z2,z3,z8,z5,z980])],[(0,[z1,z981,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z982]),(0,[z2,z48,z983,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z984]),(0,[z1,z2,z3,z8,z5,z985])]],
   [[(0,[z1,z2,z3,z986,z5,z6]),(0,[z1,z2,z634,z3,z8,z5]),(0,[z53,z1,z2,z687,z5,z6])],[(0,[z1,z324,z3,z13,z8,z5]),(0,[z1,z77,z3,z8,z346,z6]),(0,[z1,z2,z3,z8,z5,z987]),(0,[z1,z416,z3,z8,z5,z38]),(0,[z1,z2,z150,z110,z5,z287]),(0,[z1,z463,z2,z48,z8,z5])],[(0,[z0,z21,z158,z8,z5,z6]),(0,[z1,z42,z2,z324,z8,z5]),(0,[z1,z2,z3,z8,z5,z988]),(0,[z1,z989,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z990]),(0,[z1,z451,z2,z3,z8,z549]),(0,[z1,z2,z8,z5,z6,z991])],[(0,[z2,z792,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z992,z5]),(0,[z179,z2,z3,z579,z5,z6]),(0,[z1,z2,z150,z529,z5,z6]),(0,[z328,z1,z2,z166,z8,z6])],[(0,[z1,z2,z3,z8,z5,z993])],[(0,[z1,z2,z3,z8,z5,z994]),(0,[z1,z2,z150,z110,z5,z29]),(0,[z53,z1,z2,z564,z5,z6])],[(0,[z1,z182,z2,z3,z511,z5]),(0,[z1,z2,z8,z757,z23,z6]),(0,[z328,z1,z46,z2,z3,z6])],[(0,[z1,z2,z3,z8,z5,z995])],[(0,[z1,z792,z3,z8,z5,z6]),(0,[z1,z2,z3,z996,z5,z6]),(0,[z1,z997,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z690,z173]),(0,[z1,z42,z2,z150,z110,z5]),(0,[z1,z183,z3,z8,z5,z113]),(0,[z1,z2,z3,z8,z5,z998])],[(0,[z1,z2,z3,z999,z5,z6]),(0,[z69,z2,z306,z33,z5,z6]),(0,[z1,z2,z3,z8,z549,z29])],[(0,[z1,z2,z3,z5,z1000,z6]),(0,[z40,z42,z2,z3,z19,z5]),(0,[z1,z2,z3,z8,z5,z1001])],[(0,[z1,z2,z134,z8,z5,z246]),(0,[z1,z2,z410,z3,z8,z5]),(0,[z1,z2,z8,z5,z6,z931]),(0,[z1,z2,z3,z8,z5,z1002])],[(0,[z1,z42,z2,z3,z8,z5])],[(0,[z1,z65,z158,z8,z5,z6]),(0,[z42,z107,z2,z143,z8,z5]),(0,[z1,z89,z3,z8,z28,z29]),(0,[z1,z183,z3,z8,z5,z1003]),(0,[z1,z46,z2,z128,z3,z16])],[(0,[z1,z2,z3,z8,z5,z1004]),(0,[z43,z1,z48,z151,z8,z5]),(0,[z1,z70,z65,z8,z507,z6])]],
   [[(0,[z1,z2,z3,z1005,z5,z6]),(0,[z1,z2,z3,z8,z5,z1006]),(0,[z1,z42,z2,z307,z8,z5]),(0,[z1007,z2,z3,z8,z5,z6])],[(0,[z1,z398,z3,z8,z5,z6])],[(0,[z53,z1,z2,z63,z5,z38])],[(0,[z1,z2,z48,z3,z8,z71]),(0,[z1,z77,z3,z144,z5,z38])],[(0,[z497,z2,z3,z8,z5,z66]),(0,[z1,z2,z3,z8,z5,z1008])],[(0,[z1,z2,z1009,z8,z5,z6]),(0,[z1,z42,z2,z442,z8,z5]),(0,[z1,z2,z3,z8,z71,z29]),(0,[z1,z2,z3,z8,z1010,z5]),(0,[z1,z2,z3,z216,z5,z806])],[(0,[z1,z2,z3,z104,z5,z297]),(0,[z1,z2,z3,z8,z5,z1011]),(0,[z1,z2,z3,z5,z31,z261])],[(0,[z1,z2,z3,z8,z5,z1012]),(0,[z1,z2,z3,z8,z5,z1013])],[(0,[z1,z2,z1014,z3,z8,z5]),(0,[z381,z1,z3,z8,z5,z1015]),(0,[z1,z2,z3,z8,z1016,z5]),(0,[z53,z1,z451,z2,z63,z5]),(0,[z1,z2,z3,z8,z5,z31])],[(0,[z1,z2,z1017,z8,z5,z6]),(0,[z1,z540,z3,z8,z5,z38]),(0,[z1,z183,z48,z3,z8,z5])],[(0,[z1,z2,z295,z3,z311,z5]),(0,[z1018,z328,z1,z2,z8,z5])],[(0,[z179,z2,z3,z764,z5,z6]),(0,[z1,z2,z3,z104,z5,z38]),(0,[z1,z2,z1019,z3,z8,z5]),(0,[z1,z72,z2,z8,z133,z5]),(0,[z1,z72,z2,z8,z5,z181]),(0,[z1,z408,z3,z8,z5,z29])],[(0,[z2,z3,z8,z773,z5,z6]),(0,[z43,z1,z151,z8,z5,z270]),(0,[z1,z2,z3,z1020,z5,z6]),(0,[z1021,z2,z3,z8,z5,z6])],[(0,[z414,z1,z2,z48,z3,z5]),(0,[z2,z143,z902,z8,z5,z6]),(0,[z1,z2,z3,z8,z26,z29])],[(0,[z1,z2,z3,z8,z5,z1022]),(0,[z1,z2,z3,z8,z1023,z5]),(0,[z671,z2,z3,z8,z76,z6]),(0,[z1,z2,z3,z1024,z8,z5]),(0,[z1,z89,z3,z8,z28,z268]),(0,[z117,z467,z2,z3,z8,z6])],[(0,[z1,z2,z3,z8,z5,z1025]),(0,[z1,z2,z3,z1026,z5,z6]),(0,[z1,z2,z742,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1027]),(0,[z53,z1,z2,z48,z63,z5]),(0,[z205,z1,z2,z3,z637,z5])]],
   [[(0,[z1,z2,z3,z27,z346,z6])],[(0,[z1,z2,z3,z8,z1028,z6]),(0,[z1,z2,z3,z8,z5,z1029]),(1,[z1,z3,z27,z346,z6]),(0,[z1,z62,z3,z27,z5,z29]),(0,[z1,z3,z8,z561,z5,z38])],[(0,[z1,z2,z3,z8,z5,z1030]),(0,[z78,z2,z3,z8,z5,z79]),(0,[z1,z3,z8,z779,z5,z6]),(0,[z1,z206,z3,z8,z652,z6]),(0,[z207,z2,z48,z3,z8,z5])],[(0,[z1,z1031,z2,z3,z8,z5]),(0,[z1,z2,z48,z3,z8,z346])],[(0,[z1,z2,z3,z8,z5,z268]),(0,[z1,z2,z1032,z3,z8,z5]),(0,[z53,z145,z2,z63,z5,z6])],[(0,[z350,z1,z2,z3,z171,z5])],[(0,[z342,z1,z473,z2,z3,z8]),(0,[z41,z2,z3,z8,z76,z29]),(0,[z1,z3,z742,z8,z5,z6]),(0,[z1,z2,z3,z8,z346,z300]),(0,[z117,z1,z2,z48,z8,z23])],[(0,[z2,z3,z8,z5,z80,z29]),(0,[z53,z1,z72,z2,z8,z5]),(0,[z1,z398,z150,z3,z5,z6])],[(1,[z2,z902,z8,z5,z6]),(0,[z1,z2,z3,z102,z306,z6]),(0,[z1,z742,z151,z8,z5,z6]),(0,[z1,z2,z1033,z3,z8,z5]),(0,[z1,z46,z2,z3,z16,z38]),(0,[z1,z516,z42,z2,z3,z5])],[(0,[z69,z473,z2,z33,z8,z5]),(0,[z1,z2,z3,z124,z5,z29]),(0,[z53,z1,z2,z341,z5,z6])],[(0,[z414,z1,z473,z2,z3,z5]),(0,[z1,z398,z3,z8,z5,z1034])],[(0,[z1,z1035,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z1036,z6]),(0,[z1,z2,z3,z8,z5,z1037]),(0,[z1,z206,z3,z8,z15,z203])],[(0,[z1,z2,z3,z8,z312,z246]),(0,[z69,z42,z2,z33,z8,z5]),(0,[z1,z2,z3,z8,z6,z1038]),(0,[z1,z2,z3,z1039,z5,z6]),(0,[z1,z2,z48,z3,z385,z5]),(0,[z1,z2,z3,z8,z5,z1040]),(0,[z1,z74,z3,z8,z5,z29]),(1,[z1,z2,z815,z5,z6])],[(0,[z1,z2,z1041,z3,z8,z5]),(0,[z1,z42,z2,z532,z8,z5]),(0,[z1,z2,z3,z277,z5,z29])],[(0,[z1,z2,z3,z8,z5,z1042]),(0,[z1,z1043,z2,z3,z8,z5]),(0,[z1,z2,z48,z36,z8,z5]),(0,[z1,z2,z3,z8,z616,z5]),(0,[z1,z2,z3,z54,z699,z6])],[(0,[z1,z531,z65,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1044])]],
   [[(0,[z69,z2,z33,z8,z5,z29]),(0,[z1,z89,z3,z8,z723,z6]),(0,[z1,z371,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z1045])],[(0,[z40,z2,z3,z19,z5,z29])],[(0,[z1,z2,z3,z5,z1046,z6]),(0,[z1,z2,z615,z3,z8,z51])],[(0,[z83,z3,z138,z8,z5,z6])],[(0,[z1,z2,z3,z8,z6,z972]),(0,[z781,z2,z3,z8,z5,z38]),(0,[z1,z214,z3,z8,z5,z29])],[(0,[z381,z1,z158,z8,z5,z6]),(0,[z0,z21,z48,z3,z8,z5]),(0,[z1,z161,z3,z8,z5,z29])],[(0,[z1,z2,z919,z3,z8,z5]),(0,[z1,z42,z2,z8,z5,z109]),(0,[z467,z42,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z6,z1047]),(0,[z130,z2,z143,z8,z5,z131]),(0,[z53,z1,z323,z2,z5,z6])],[(0,[z145,z2,z3,z8,z5,z6]),(0,[z1,z2,z1048,z3,z8,z5])],[(0,[z1,z2,z3,z124,z5,z268])],[(0,[z1,z3,z277,z5,z28,z6]),(0,[z1,z42,z2,z3,z5,z261])],[(0,[z1,z2,z140,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1049])],[(0,[z1,z2,z3,z8,z5,z1050])],[(0,[z1,z2,z3,z566,z312,z6]),(0,[z1,z2,z3,z8,z1051,z6]),(0,[z467,z2,z3,z8,z75,z6]),(0,[z1,z2,z3,z8,z5,z1052]),(0,[z1,z2,z3,z277,z5,z268]),(0,[z2,z3,z8,z5,z38,z1053]),(0,[z1,z42,z2,z8,z5,z132]),(0,[z1,z42,z2,z8,z5,z577]),(1,[z1,z2,z3,z8,z785])],[(0,[z1,z183,z3,z8,z5,z6]),(0,[z1,z323,z451,z2,z3,z8]),(0,[z1,z42,z2,z584,z8,z5]),(0,[z11,z2,z7,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1054]),(0,[z1,z2,z3,z8,z5,z1055])],[]],
   [[(0,[z1,z2,z3,z8,z5,z1056]),(0,[z53,z1,z2,z362,z5,z6]),(0,[z1,z1057,z3,z8,z5,z6])],[(0,[z1058,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z815,z5,z6]),(0,[z1,z1059,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z131]),(0,[z179,z2,z3,z596,z5,z6]),(0,[z1,z2,z3,z8,z1060,z6]),(0,[z328,z1,z46,z2,z8,z6])],[(0,[z1,z2,z634,z151,z8,z5]),(0,[z1,z2,z3,z1061,z5,z6]),(0,[z1,z2,z1062,z8,z5,z6]),(0,[z1,z2,z3,z54,z775,z6])],[(0,[z1,z2,z214,z33,z8,z5]),(0,[z1,z62,z3,z27,z346,z6]),(0,[z1,z2,z1063,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z1064]),(0,[z2,z3,z764,z19,z5,z6]),(0,[z1,z1065,z2,z3,z8,z6]),(0,[z53,z1,z2,z63,z5,z29]),(0,[z1,z323,z2,z48,z3,z8]),(0,[z1,z2,z3,z8,z5,z1066])],[(0,[z1,z2,z3,z8,z5,z1067]),(0,[z414,z207,z2,z3,z5,z6]),(0,[z1,z77,z3,z144,z5,z29]),(0,[z1,z2,z3,z8,z5,z203])],[(0,[z207,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z124,z5,z90]),(0,[z1,z2,z3,z8,z5,z1068])],[(0,[z94,z2,z3,z8,z75,z38])],[(0,[z1,z2,z3,z8,z5,z211]),(0,[z1,z70,z65,z8,z5,z211])],[(0,[z1,z2,z3,z8,z5,z1069]),(0,[z1,z42,z2,z565,z8,z5])],[(0,[z1,z2,z3,z8,z5,z789]),(0,[z1,z2,z3,z277,z5,z90]),(0,[z1,z2,z3,z8,z5,z1070]),(0,[z1,z2,z3,z8,z616,z549]),(0,[z1,z2,z3,z8,z5,z1071]),(0,[z117,z1,z2,z8,z23,z6])],[],[(0,[z1,z473,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1072]),(0,[z40,z2,z3,z231,z19,z5]),(0,[z1,z610,z2,z3,z16,z6])],[(0,[z0,z21,z3,z8,z5,z246]),(0,[z2,z3,z8,z76,z530,z6]),(0,[z1,z42,z2,z3,z104,z5]),(0,[z1,z610,z3,z8,z28,z6])],[(0,[z1,z2,z1073,z3,z8,z5]),(0,[z1,z2,z3,z277,z15,z6]),(0,[z91,z1,z3,z201,z8,z5]),(0,[z1,z2,z624,z3,z8,z108])]],
   [[(0,[z0,z415,z3,z8,z5,z6]),(0,[z1,z1074,z3,z8,z5,z6]),(0,[z665,z1,z3,z27,z5,z6]),(0,[z1,z2,z3,z8,z856,z6]),(0,[z328,z1,z46,z2,z5,z6])],[(0,[z1,z516,z2,z140,z3,z5])],[(0,[z1,z2,z1075,z8,z5,z6]),(0,[z1,z2,z1076,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1077]),(0,[z1,z2,z3,z8,z750,z29]),(0,[z1,z2,z8,z5,z577,z29])],[(0,[z1,z2,z3,z4,z5,z29]),(0,[z1,z1078,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1079])],[(0,[z1,z2,z3,z8,z5,z270])],[(0,[z1,z1080,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z1081]),(0,[z1,z2,z3,z8,z507,z297]),(0,[z2,z983,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z346,z355])],[(0,[z1,z2,z134,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z1015]),(0,[z1,z77,z3,z144,z5,z152]),(0,[z190,z1,z214,z3,z8,z5])],[(0,[z1,z2,z1082,z8,z5,z6]),(0,[z1083,z2,z3,z8,z5,z6])],[(0,[z1,z42,z2,z435,z8,z5]),(0,[z1,z2,z3,z385,z5,z297]),(0,[z1,z2,z3,z8,z1084,z6]),(0,[z1,z42,z2,z3,z124,z5])],[(0,[z0,z21,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z1085,z6]),(0,[z1,z1086,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z1087,z5]),(0,[z43,z1,z42,z151,z8,z5]),(0,[z1,z46,z2,z3,z16,z29]),(0,[z1,z2,z1088,z3,z8,z5])],[(0,[z1,z2,z3,z8,z1089,z6]),(0,[z342,z1,z2,z48,z3,z8]),(0,[z1,z2,z3,z8,z5,z1090]),(0,[z1,z2,z3,z144,z346,z6]),(0,[z117,z1,z2,z341,z8,z6])],[(0,[z1,z1091,z2,z3,z8,z5]),(0,[z1,z3,z13,z8,z5,z29]),(0,[z1,z2,z3,z8,z5,z1092])],[(0,[z1,z2,z48,z3,z8,z312]),(0,[z1,z2,z3,z385,z5,z38])],[(0,[z0,z21,z3,z566,z5,z6]),(0,[z1,z2,z3,z8,z5,z1093])]],
   [[(0,[z1,z2,z3,z8,z5,z1094]),(0,[z1,z42,z2,z256,z8,z5]),(0,[z1,z2,z1095,z3,z8,z6]),(0,[z1,z2,z3,z8,z108,z51]),(0,[z1,z398,z3,z5,z16,z6])],[(0,[z1,z2,z36,z8,z5,z29]),(0,[z1,z623,z3,z27,z5,z6]),(1,[z1,z3,z8,z5,z724])],[],[],[(0,[z1,z2,z3,z8,z1096,z6]),(0,[z1,z106,z3,z8,z5,z724])],[(0,[z1,z2,z3,z8,z1097,z6]),(0,[z1,z2,z3,z5,z6,z1098]),(0,[z1,z2,z3,z8,z217,z401]),(0,[z1,z2,z3,z8,z5,z1099])],[(0,[z1,z2,z8,z133,z757,z6]),(0,[z1100,z2,z48,z3,z8,z5])],[(0,[z1,z2,z3,z1101,z5,z6]),(0,[z1,z2,z3,z8,z5,z887]),(0,[z1,z2,z3,z8,z1102,z6]),(0,[z1,z2,z3,z440,z5,z92])],[(0,[z381,z1,z48,z3,z8,z5]),(0,[z1,z72,z2,z143,z8,z5]),(0,[z1,z1103,z2,z3,z8,z5]),(0,[z117,z1,z72,z2,z8,z5]),(0,[z1,z2,z140,z3,z5,z261])],[(0,[z1,z1104,z3,z8,z5,z6]),(0,[z1,z1105,z2,z3,z8,z5]),(0,[z41,z2,z3,z8,z773,z6])],[],[(0,[z94,z42,z2,z3,z8,z75])],[],[(0,[z1,z981,z2,z158,z8,z5]),(0,[z1,z2,z3,z8,z5,z1106]),(0,[z1,z2,z3,z8,z5,z1107]),(0,[z1,z737,z2,z3,z5,z6]),(0,[z1,z42,z2,z3,z8,z549])],[(0,[z1,z42,z2,z3,z102,z8]),(0,[z1,z454,z3,z8,z28,z6])],[(0,[z43,z1,z214,z3,z8,z5]),(0,[z1,z2,z1108,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1109])]],
   [[],[(0,[z0,z21,z3,z8,z298,z6]),(0,[z1,z2,z3,z102,z8,z29]),(0,[z1,z120,z2,z3,z8,z5]),(0,[z1110,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z277,z28,z6]),(0,[z1,z2,z872,z8,z5,z38])],[(0,[z78,z107,z2,z3,z8,z5]),(0,[z1,z42,z183,z3,z8,z5])],[(0,[z1,z2,z1111,z3,z8,z5]),(0,[z207,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z8,z5,z1112])],[(0,[z1,z2,z158,z8,z5,z6]),(0,[z1,z2,z3,z8,z1113,z6]),(0,[z1,z2,z8,z5,z38,z1114])],[(0,[z1,z2,z8,z5,z64,z721]),(0,[z1,z2,z3,z5,z6,z806])],[(0,[z1,z2,z3,z8,z1115,z6]),(0,[z1,z70,z48,z65,z8,z5])],[(0,[z1,z2,z3,z4,z312,z6]),(0,[z1,z2,z3,z8,z5,z1116]),(0,[z1,z2,z3,z1117,z5,z6]),(0,[z1,z3,z144,z779,z5,z6])],[(0,[z1,z1118,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z1119,z5]),(0,[z1,z2,z3,z1120,z5,z6])],[(0,[z1,z2,z158,z566,z5,z6]),(0,[z2,z3,z8,z5,z6,z1053]),(0,[z907,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1121])],[(0,[z1,z2,z3,z8,z723,z6])],[(0,[z1,z2,z324,z36,z8,z5]),(0,[z1,z2,z8,z5,z1122,z6]),(1,[z1,z3,z8,z723,z6]),(0,[z696,z1,z42,z2,z8,z5]),(0,[z1,z2,z3,z8,z5,z1123]),(0,[z1,z42,z2,z48,z8,z5])],[],[(0,[z1,z42,z2,z158,z8,z5]),(0,[z1,z425,z2,z3,z5,z186]),(0,[z1,z2,z48,z8,z5,z64])],[(0,[z130,z2,z143,z8,z5,z6]),(0,[z1,z48,z3,z13,z8,z5]),(0,[z1,z770,z2,z3,z8,z5]),(0,[z1,z2,z3,z1124,z5,z6]),(0,[z179,z2,z3,z18,z5,z38])],[(0,[z1,z2,z3,z1125,z5,z6]),(0,[z1,z2,z634,z65,z8,z5]),(0,[z1,z2,z48,z359,z8,z5]),(0,[z1,z2,z1126,z3,z8,z5])]],
   [[(0,[z1,z2,z3,z245,z5,z92])],[],[(0,[z1,z2,z3,z8,z5,z1127])],[(0,[z24,z792,z3,z8,z5,z6]),(0,[z1128,z2,z3,z8,z5,z6]),(0,[z1,z2,z150,z815,z5,z6])],[],[(0,[z1,z3,z27,z5,z346,z6])],[(0,[z1,z2,z3,z8,z1129,z6]),(0,[z1,z1130,z2,z3,z8,z5]),(0,[z1,z1131,z2,z3,z8,z5]),(0,[z2,z3,z8,z5,z845,z6])],[(0,[z1,z2,z3,z8,z489,z173]),(0,[z1,z2,z3,z8,z5,z1132])],[(0,[z94,z2,z3,z8,z298,z6]),(0,[z1,z2,z1133,z8,z5,z6]),(0,[z83,z792,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z1134,z6]),(0,[z1,z2,z3,z8,z5,z1135]),(0,[z59,z1,z3,z201,z8,z5])],[(0,[z1,z1136,z2,z3,z5,z6])],[(0,[z1,z551,z3,z8,z5,z38])],[(0,[z1,z2,z158,z8,z298,z6]),(0,[z1,z2,z3,z8,z5,z1137]),(0,[z1,z42,z2,z7,z8,z5]),(0,[z1,z2,z48,z8,z5,z702]),(0,[z1100,z2,z3,z8,z5,z6])],[(0,[z1,z2,z134,z8,z5,z119]),(0,[z1,z1138,z2,z3,z8,z5]),(0,[z1,z2,z1139,z8,z5,z6]),(0,[z1,z2,z3,z104,z507,z6]),(0,[z1,z1140,z2,z3,z8,z5]),(0,[z1,z2,z1141,z3,z8,z5]),(0,[z1,z403,z2,z3,z5,z186]),(0,[z1,z2,z3,z8,z5,z785])],[(0,[z381,z1,z3,z8,z5,z6]),(0,[z1,z2,z3,z1142,z8,z6]),(0,[z1,z1143,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z71,z211]),(0,[z467,z2,z48,z3,z8,z5]),(0,[z1,z3,z8,z5,z38,z209]),(0,[z1,z516,z2,z133,z5,z6]),(0,[z1,z1144,z3,z8,z5,z6])],[(0,[z1,z2,z48,z3,z566,z5]),(0,[z1,z2,z3,z8,z5,z1145])],[(0,[z24,z3,z8,z5,z406,z6]),(0,[z1,z2,z3,z8,z5,z1146]),(0,[z1,z288,z3,z8,z5,z29]),(0,[z1018,z1,z2,z3,z8,z5])]],
   [[(0,[z83,z24,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1147])],[(0,[z1,z2,z3,z8,z5,z1148]),(0,[z1,z2,z3,z104,z5,z29]),(0,[z1,z516,z2,z253,z3,z6]),(0,[z1,z2,z8,z5,z721,z30])],[(0,[z1,z2,z3,z231,z8,z5]),(0,[z1,z2,z3,z8,z5,z1149]),(0,[z2,z3,z8,z5,z789,z79])],[(0,[z1,z2,z1150,z3,z8,z5]),(0,[z1,z2,z1151,z3,z8,z5]),(0,[z1,z2,z1152,z3,z8,z5]),(0,[z1,z206,z3,z8,z15,z228]),(0,[z1,z2,z3,z8,z1153,z5]),(0,[z1,z1154,z2,z3,z8,z5])],[(0,[z1,z2,z1155,z3,z8,z5]),(0,[z43,z1,z151,z8,z5,z6]),(0,[z394,z2,z3,z8,z5,z318])],[(0,[z1,z1156,z2,z3,z8,z5]),(0,[z1,z1157,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1158])],[(0,[z237,z1,z3,z8,z5,z29]),(0,[z1,z2,z3,z1159,z5,z6])],[(0,[z1,z42,z2,z617,z8,z5]),(0,[z467,z2,z3,z8,z76,z6]),(0,[z1,z2,z3,z8,z5,z1160]),(0,[z1,z516,z2,z3,z5,z38]),(0,[z1,z2,z3,z8,z5,z113]),(0,[z1,z1161,z2,z3,z8,z5])],[(0,[z179,z42,z2,z3,z18,z5]),(0,[z1,z2,z1162,z3,z8,z5]),(0,[z1,z276,z3,z27,z5,z6]),(0,[z1,z3,z201,z8,z5,z38]),(0,[z1,z2,z48,z8,z5,z218])],[(0,[z43,z1,z151,z8,z5,z44]),(0,[z1,z1163,z2,z3,z8,z5])],[(0,[z1,z2,z1164,z8,z5,z6]),(0,[z1,z3,z779,z27,z5,z6]),(0,[z1,z2,z3,z8,z5,z1165]),(0,[z1,z921,z2,z8,z5,z38]),(0,[z1,z2,z3,z5,z261,z6]),(0,[z1,z2,z253,z8,z757,z6]),(0,[z1,z2,z3,z8,z5,z1166])],[(0,[z1,z2,z3,z8,z6,z785])],[(0,[z1,z2,z256,z8,z5,z79]),(0,[z1,z2,z3,z8,z5,z1003]),(0,[z1,z1167,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1168]),(0,[z1,z2,z3,z8,z1169,z6]),(0,[z1,z959,z3,z8,z5,z6]),(0,[z1,z1170,z3,z8,z5,z6])],[(0,[z1,z2,z966,z134,z8,z5]),(0,[z1,z2,z3,z8,z507,z38])],[(0,[z1,z2,z3,z8,z5,z1171]),(0,[z1,z2,z3,z8,z753,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z1172]),(0,[z381,z1,z3,z306,z5,z6]),(0,[z2,z3,z8,z5,z1173,z6]),(0,[z1,z2,z1174,z3,z8,z5])],[(0,[z1,z2,z3,z8,z1175,z6]),(0,[z1,z2,z3,z8,z5,z1176]),(0,[z1,z120,z2,z8,z5,z132]),(0,[z1,z1177,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1178])],[(0,[z94,z17,z2,z3,z8,z6]),(0,[z199,z2,z3,z8,z5,z544]),(0,[z1179,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z1180,z6]),(0,[z1,z2,z1181,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1034])],[(0,[z491,z1,z3,z8,z28,z6]),(0,[z1,z2,z3,z8,z5,z724]),(0,[z1,z2,z48,z150,z110,z5]),(0,[z1,z2,z3,z8,z5,z1182])],[],[(0,[z1,z2,z3,z1183,z5,z6]),(0,[z40,z2,z48,z3,z19,z5]),(0,[z1,z2,z8,z5,z6,z721])],[(0,[z1,z2,z1184,z8,z5,z6]),(0,[z483,z2,z33,z8,z5,z6])],[(0,[z1,z2,z48,z3,z8,z5]),(0,[z1,z2,z134,z8,z5,z38]),(0,[z414,z2,z3,z19,z5,z6]),(0,[z1,z2,z3,z8,z1185,z6]),(0,[z1,z2,z3,z8,z5,z292]),(0,[z1,z2,z3,z1186,z8,z5]),(0,[z1,z2,z3,z8,z5,z1187]),(0,[z1,z2,z3,z8,z217,z356])],[(0,[z1,z3,z8,z5,z1188,z6]),(0,[z1,z2,z890,z8,z5,z6]),(0,[z315,z1,z2,z3,z8,z240])],[(0,[z1,z2,z1189,z3,z8,z5]),(0,[z91,z1,z3,z8,z5,z29])],[(0,[z1,z1190,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z421,z401]),(0,[z1,z2,z1191,z3,z8,z5])],[(0,[z1,z2,z158,z8,z5,z246]),(0,[z1,z2,z1192,z3,z8,z5]),(0,[z1,z2,z1193,z3,z8,z5]),(0,[z1194,z207,z2,z3,z8,z5])],[(0,[z1,z2,z3,z8,z312,z119]),(0,[z1,z2,z3,z8,z1195,z6]),(0,[z1,z1196,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1197]),(0,[z1,z1198,z2,z8,z5,z6])],[(0,[z1,z1199,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1200]),(0,[z1,z2,z3,z8,z1201,z6]),(0,[z1,z2,z3,z5,z1202,z6])],[(0,[z1,z473,z2,z3,z102,z8]),(0,[z2,z3,z1203,z8,z5,z6]),(0,[z1,z47,z3,z201,z8,z5]),(0,[z1,z2,z3,z8,z5,z228]),(0,[z1,z323,z2,z150,z3,z6])],[(0,[z1,z42,z2,z3,z8,z507]),(0,[z207,z2,z3,z144,z5,z6])]],
   [[(0,[z1,z2,z47,z3,z8,z5]),(0,[z1,z2,z8,z5,z6,z1114])],[(0,[z1,z206,z3,z8,z15,z6]),(0,[z1,z2,z1204,z3,z8,z5]),(0,[z1205,z2,z3,z8,z5,z6])],[(0,[z1,z1206,z2,z3,z8,z5]),(0,[z1,z2,z1207,z3,z8,z5]),(0,[z78,z2,z3,z8,z5,z262]),(0,[z1,z2,z3,z8,z1208,z6])],[(0,[z0,z266,z3,z8,z5,z6]),(0,[z78,z2,z3,z8,z5,z383]),(0,[z1,z323,z2,z3,z8,z6])],[(0,[z381,z1,z42,z3,z8,z5]),(0,[z2,z3,z8,z764,z5,z6]),(0,[z1,z2,z256,z8,z5,z173]),(0,[z611,z2,z3,z8,z5,z66]),(0,[z1,z370,z3,z8,z28,z6]),(0,[z1,z42,z2,z503,z8,z5]),(0,[z1,z2,z3,z8,z5,z1209]),(0,[z328,z1,z2,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1210]),(0,[z1,z1211,z2,z3,z8,z5]),(0,[z1,z1212,z2,z3,z8,z5])],[(0,[z1,z2,z3,z1213,z5,z6]),(0,[z1,z182,z2,z256,z8,z5]),(0,[z1,z2,z3,z8,z524,z51]),(0,[z1,z3,z8,z5,z29,z187]),(0,[z1,z2,z1214,z3,z8,z5])],[(0,[z1,z2,z48,z256,z8,z5]),(0,[z1,z2,z128,z3,z8,z5])],[(0,[z1,z2,z3,z8,z1215,z6]),(0,[z1,z2,z1216,z8,z5,z6]),(0,[z1,z1217,z2,z3,z8,z5]),(0,[z1218,z2,z3,z8,z5,z6]),(0,[z1,z46,z2,z3,z16,z157])],[(0,[z1,z2,z1219,z8,z5,z6]),(0,[z381,z342,z1,z3,z8,z6]),(0,[z1,z2,z1220,z3,z8,z5]),(0,[z1,z2,z8,z815,z5,z6])],[(0,[z199,z2,z3,z8,z5,z789])],[(0,[z1,z2,z3,z8,z5,z1221]),(0,[z1,z2,z3,z1222,z5,z6]),(0,[z1,z42,z2,z362,z8,z5]),(0,[z1,z2,z256,z8,z5,z66]),(0,[z1,z2,z3,z8,z5,z300]),(0,[z117,z1,z2,z8,z31,z23])],[(0,[z1,z427,z2,z3,z440,z5]),(0,[z1,z2,z3,z166,z775,z6])],[(0,[z499,z1,z3,z8,z5,z29])],[(0,[z1,z932,z2,z134,z8,z5]),(0,[z94,z2,z3,z8,z75,z29])],[(0,[z1,z3,z8,z5,z6,z1223]),(0,[z1,z3,z8,z15,z723,z6]),(0,[z53,z1,z2,z549,z63,z6]),(0,[z1,z320,z2,z48,z8,z5])]],
   [[(0,[z1,z2,z3,z8,z5,z1224]),(0,[z1,z42,z2,z8,z5,z30]),(0,[z1,z1225,z3,z8,z5,z6])],[(0,[z69,z2,z102,z33,z8,z6])],[(0,[z1,z70,z47,z65,z8,z5])],[(0,[z1,z2,z1226,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1227]),(0,[z1,z214,z65,z3,z8,z5]),(0,[z1,z3,z8,z5,z723,z6])],[(0,[z1,z2,z3,z1228,z5,z6]),(0,[z1,z2,z48,z3,z8,z549])],[(0,[z1,z2,z1229,z3,z8,z5])],[(0,[z69,z2,z48,z33,z8,z5]),(0,[z1,z2,z3,z8,z5,z1230]),(0,[z1231,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z346,z38]),(0,[z2,z3,z1232,z8,z5,z6]),(0,[z1,z1233,z2,z3,z8,z5]),(0,[z1,z2,z3,z166,z54,z38]),(0,[z87,z2,z3,z8,z5,z383])],[(0,[z1,z2,z3,z8,z312,z38]),(0,[z1,z2,z3,z8,z1234,z5]),(0,[z145,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z1235])],[(0,[z1,z2,z902,z8,z5,z6])],[(0,[z1,z2,z3,z1236,z5,z6]),(0,[z1,z42,z2,z3,z306,z5]),(0,[z1,z2,z1237,z3,z8,z5]),(0,[z1,z2,z969,z3,z8,z38])],[(0,[z342,z1,z2,z3,z8,z6]),(0,[z1,z2,z324,z8,z5,z64]),(0,[z130,z42,z2,z143,z8,z5]),(0,[z1,z516,z2,z3,z5,z29]),(0,[z1,z182,z2,z3,z171,z5])],[(0,[z40,z207,z2,z3,z5,z6]),(0,[z1,z2,z3,z1238,z8,z5])],[(0,[z1,z2,z3,z8,z5,z6]),(0,[z1,z70,z65,z8,z5,z6])],[(0,[z1,z3,z8,z5,z38,z378]),(0,[z1,z2,z815,z63,z5,z6]),(0,[z718,z2,z48,z3,z8,z5])],[(0,[z1,z1239,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1240]),(0,[z130,z2,z143,z8,z5,z316]),(0,[z1,z2,z3,z8,z1241,z5]),(0,[z1,z2,z3,z385,z507,z6]),(0,[z1,z2,z3,z8,z5,z1242]),(0,[z1,z46,z2,z3,z465,z6])]],
   [[(0,[z1,z2,z1243,z8,z5,z6]),(0,[z1,z2,z3,z8,z785,z51])],[(0,[z1,z2,z3,z566,z5,z6]),(0,[z1,z2,z3,z8,z5,z1244]),(0,[z1,z1245,z2,z3,z8,z5])],[(0,[z1,z323,z2,z110,z8,z6]),(0,[z1,z42,z768,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z1246]),(0,[z1,z2,z150,z5,z573,z6]),(0,[z1,z2,z3,z216,z5,z92])],[(0,[z1,z42,z2,z306,z33,z5]),(0,[z1,z2,z214,z143,z8,z5]),(0,[z1,z2,z3,z385,z5,z29]),(0,[z1,z2,z253,z8,z133,z6]),(0,[z1,z2,z48,z3,z5,z261])],[(0,[z1,z2,z3,z8,z5,z1247]),(0,[z1,z2,z253,z8,z254,z6]),(0,[z53,z117,z1,z46,z2,z6]),(0,[z1,z120,z161,z3,z8,z5])],[(0,[z1,z2,z3,z8,z1248,z6])],[(0,[z1,z2,z3,z8,z5,z1249]),(0,[z1,z42,z2,z253,z8,z133]),(0,[z1,z42,z2,z236,z8,z5]),(0,[z1,z2,z48,z8,z5,z577])],[(0,[z1,z1250,z2,z3,z5,z6]),(0,[z1,z182,z2,z3,z5,z186])],[(0,[z1,z398,z3,z8,z16,z6])],[(0,[z1,z2,z134,z8,z5,z29]),(0,[z414,z1,z2,z3,z5,z6]),(0,[z117,z1,z2,z8,z23,z38]),(0,[z1,z2,z3,z8,z5,z721]),(0,[z1,z2,z3,z8,z1251,z5])],[(0,[z2,z902,z33,z8,z5,z6]),(0,[z42,z2,z33,z8,z19,z5]),(0,[z1,z2,z811,z33,z8,z5]),(0,[z123,z2,z3,z19,z5,z6]),(0,[z42,z2,z3,z8,z5,z80]),(0,[z1,z2,z3,z8,z5,z1252])],[(0,[z0,z21,z3,z4,z5,z6]),(0,[z1,z2,z3,z166,z314,z6]),(0,[z1,z398,z253,z3,z8,z6])],[],[(0,[z1,z72,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1253]),(0,[z1,z2,z3,z8,z5,z1254])],[(0,[z1,z2,z3,z306,z5,z6]),(0,[z1,z2,z3,z1255,z5,z6]),(0,[z43,z1,z3,z201,z8,z5]),(0,[z1,z2,z3,z8,z1256,z6]),(0,[z1,z1257,z2,z3,z8,z5])]],
   [[(0,[z1,z2,z3,z8,z5,z1258]),(0,[z328,z1,z2,z27,z5,z6]),(0,[z1,z2,z1259,z3,z8,z5])],[(0,[z1,z2,z1260,z8,z5,z6]),(0,[z53,z1,z2,z465,z5,z6]),(1,[z1,z2,z3,z5,z806])],[(0,[z2,z3,z8,z5,z789,z6]),(0,[z1,z3,z8,z27,z346,z6]),(0,[z1,z2,z3,z585,z5,z92])],[(0,[z1,z2,z3,z8,z298,z6]),(0,[z1,z2,z3,z1261,z8,z5]),(0,[z1,z2,z3,z1262,z5,z6]),(0,[z1,z398,z3,z8,z5,z38]),(0,[z328,z1,z42,z2,z8,z5]),(0,[z1,z2,z3,z8,z217,z785])],[(0,[z1,z2,z3,z8,z5,z1263]),(0,[z769,z328,z1,z2,z8,z5])],[(0,[z1,z2,z3,z5,z775,z6])],[(0,[z1,z473,z3,z13,z8,z5]),(0,[z1,z2,z3,z1264,z5,z6]),(0,[z1,z2,z3,z8,z5,z1265])],[(0,[z1,z299,z3,z8,z15,z6]),(0,[z1,z905,z2,z8,z5,z6]),(0,[z1,z2,z128,z8,z5,z577])],[(0,[z1,z2,z48,z3,z104,z5]),(0,[z1,z2,z3,z1266,z5,z6]),(0,[z1,z2,z3,z8,z5,z1267])],[(0,[z1,z42,z3,z13,z8,z5]),(0,[z1,z1268,z2,z3,z8,z5]),(0,[z1,z77,z3,z660,z5,z6]),(0,[z1,z2,z3,z8,z5,z1269]),(0,[z1,z2,z3,z8,z5,z1270])],[(0,[z1,z2,z3,z1271,z8,z5]),(0,[z1,z1272,z2,z3,z8,z5])],[(0,[z1,z2,z3,z1273,z5,z6]),(0,[z1,z2,z1274,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1275]),(0,[z1,z2,z3,z8,z1276,z6]),(0,[z1,z2,z3,z8,z5,z355]),(0,[z1,z2,z3,z8,z217,z173])],[(0,[z1,z2,z256,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1277]),(0,[z1,z3,z8,z5,z29,z374]),(0,[z1,z2,z3,z8,z1278,z6]),(0,[z1,z2,z3,z8,z1279,z5])],[(0,[z1,z42,z2,z537,z8,z5]),(0,[z69,z13,z33,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1280]),(0,[z1,z425,z2,z3,z5,z39]),(0,[z1,z42,z2,z8,z5,z608])],[(0,[z1,z2,z3,z8,z5,z1281])],[(0,[z1,z2,z1282,z3,z8,z5]),(0,[z1,z2,z3,z8,z1283,z6]),(0,[z467,z89,z3,z8,z28,z6]),(0,[z53,z207,z2,z63,z5,z6]),(0,[z1,z2,z172,z3,z8,z240])]],
   [[(0,[z1,z2,z1284,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1285]),(0,[z2,z3,z8,z5,z80,z1165]),(0,[z1,z2,z3,z1286,z8,z5])],[(0,[z1,z3,z8,z1287,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1288]),(0,[z1,z2,z3,z8,z173,z785])],[(0,[z1,z2,z3,z8,z5,z1289]),(0,[z1,z2,z48,z3,z124,z5])],[(0,[z1,z2,z324,z3,z8,z5]),(0,[z1,z2,z3,z8,z1290,z5]),(0,[z179,z2,z3,z18,z5,z29])],[(0,[z1,z2,z3,z1291,z5,z6]),(0,[z467,z2,z3,z8,z5,z6]),(0,[z1292,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z1293]),(0,[z53,z1,z323,z2,z63,z6]),(0,[z1,z2,z3,z8,z5,z1294])],[(0,[z1,z2,z158,z4,z5,z6]),(0,[z1,z2,z3,z8,z5,z1295]),(0,[z1,z2,z3,z8,z5,z1296]),(0,[z1,z2,z1297,z3,z8,z5])],[(0,[z1,z2,z3,z8,z1298,z5])],[(0,[z381,z1,z324,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z1299]),(0,[z1,z2,z3,z8,z346,z29]),(0,[z1,z3,z8,z5,z38,z498]),(0,[z1,z2,z3,z166,z54,z29]),(0,[z1,z46,z42,z2,z3,z16])],[(0,[z1,z42,z2,z134,z8,z5]),(0,[z1,z2,z3,z8,z312,z29]),(0,[z117,z1,z2,z180,z8,z6]),(0,[z199,z2,z3,z509,z8,z5])],[(0,[z1300,z2,z3,z8,z5,z6]),(0,[z1,z2,z110,z815,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1301]),(0,[z239,z2,z33,z8,z5,z6]),(0,[z41,z2,z3,z8,z76,z292]),(0,[z1,z651,z3,z8,z15,z6]),(0,[z1,z600,z3,z8,z5,z38]),(0,[z751,z207,z2,z3,z8,z5]),(0,[z1194,z1,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z1302])],[(0,[z1,z2,z3,z8,z5,z1303]),(0,[z1,z3,z8,z464,z5,z38]),(0,[z1,z2,z3,z8,z5,z1304]),(0,[z1,z2,z3,z5,z6,z1305])],[(0,[z1,z2,z134,z8,z312,z6]),(0,[z179,z207,z2,z3,z5,z6]),(0,[z1,z623,z2,z3,z16,z6])],[(0,[z1,z2,z3,z8,z1306,z6]),(0,[z1,z2,z3,z1307,z5,z6]),(0,[z1,z42,z2,z180,z8,z5]),(0,[z1,z2,z3,z8,z1308,z6]),(0,[z1,z2,z977,z8,z5,z29])]],
   [[(0,[z1309,z2,z3,z8,z5,z6])],[(0,[z1,z42,z2,z677,z8,z5]),(0,[z1,z2,z3,z8,z5,z1310]),(0,[z1,z2,z150,z110,z5,z6])],[(0,[z1,z2,z3,z8,z5,z1311])],[(0,[z1,z2,z3,z8,z5,z246]),(0,[z1,z1312,z2,z3,z8,z5])],[(0,[z1,z2,z143,z8,z5,z131]),(0,[z1,z2,z3,z8,z5,z1313]),(0,[z1,z153,z3,z8,z5,z38])],[(0,[z94,z2,z48,z3,z8,z75]),(0,[z1,z2,z1314,z3,z8,z5]),(0,[z1,z2,z3,z8,z549,z6]),(1,[z328,z1,z46,z2,z6]),(0,[z1,z2,z8,z5,z577,z1235])],[(0,[z1,z42,z2,z3,z4,z5]),(0,[z1,z2,z410,z33,z8,z5]),(0,[z1,z2,z48,z3,z8,z507]),(0,[z1,z214,z3,z8,z27,z5]),(0,[z1,z3,z8,z5,z29,z351]),(0,[z1,z2,z3,z8,z5,z1315])],[(0,[z1,z42,z2,z33,z8,z5]),(0,[z497,z2,z143,z8,z5,z6]),(0,[z1,z2,z48,z8,z5,z58]),(0,[z805,z2,z48,z3,z8,z5])],[(0,[z1,z2,z3,z566,z5,z246]),(0,[z1,z2,z48,z3,z102,z8]),(0,[z1,z2,z1316,z3,z8,z5]),(0,[z1,z2,z3,z1317,z5,z6]),(0,[z1,z516,z2,z48,z3,z5]),(1,[z1,z2,z8,z5,z721])],[(0,[z1,z473,z2,z3,z306,z5]),(0,[z1,z1318,z3,z8,z5,z6]),(0,[z1,z3,z8,z502,z5,z38]),(0,[z1,z2,z3,z104,z5,z211]),(0,[z1,z89,z3,z8,z28,z6]),(0,[z1,z3,z8,z5,z724,z6]),(0,[z1,z2,z3,z8,z5,z1319])],[(0,[z199,z2,z3,z8,z5,z66]),(0,[z1,z2,z3,z1320,z5,z6])],[(0,[z2,z3,z8,z76,z773,z6]),(0,[z1,z62,z3,z27,z5,z300]),(0,[z1,z673,z2,z3,z16,z6]),(0,[z117,z1,z2,z8,z757,z6])],[(0,[z467,z2,z3,z8,z298,z6])],[(0,[z2,z3,z902,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1321])],[(0,[z41,z2,z3,z365,z8,z6]),(0,[z1,z2,z3,z8,z1322,z5])],[(0,[z1,z505,z3,z8,z5,z38])]],
   [[(0,[z497,z42,z2,z143,z8,z5]),(0,[z1,z2,z3,z8,z71,z6]),(0,[z1,z70,z65,z8,z71,z6]),(0,[z1,z2,z47,z8,z5,z58]),(0,[z1,z183,z3,z8,z5,z38])],[(0,[z0,z21,z3,z8,z5,z119]),(0,[z1,z42,z2,z8,z5,z681]),(0,[z1,z2,z3,z8,z5,z1323]),(0,[z1,z516,z2,z3,z5,z31]),(0,[z328,z1,z2,z8,z5,z93]),(0,[z1,z2,z172,z3,z8,z535])],[],[(0,[z69,z2,z324,z33,z8,z5])],[(0,[z1,z2,z3,z8,z5,z44]),(0,[z1,z2,z3,z8,z507,z29])],[(0,[z1,z1324,z3,z8,z5,z6]),(0,[z1,z1325,z2,z3,z8,z5]),(0,[z1,z2,z1326,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1327])],[(0,[z1,z2,z1328,z8,z5,z6]),(1,[z2,z3,z8,z773,z6]),(0,[z1,z398,z3,z8,z5,z29])],[(0,[z1,z2,z48,z158,z8,z5]),(0,[z1,z2,z1329,z3,z8,z5])],[(0,[z1,z484,z3,z144,z5,z6]),(0,[z1,z2,z3,z8,z5,z1330]),(0,[z1,z2,z3,z8,z26,z6]),(0,[z328,z1,z46,z2,z16,z6])],[(0,[z1,z2,z3,z8,z5,z1331]),(0,[z207,z2,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z1332])],[(0,[z1,z2,z3,z8,z5,z25]),(0,[z1,z2,z3,z8,z298,z246]),(0,[z1,z2,z7,z256,z8,z5]),(0,[z1,z2,z3,z8,z5,z1333]),(0,[z1,z2,z3,z8,z5,z1334])],[(0,[z40,z56,z2,z3,z19,z5])],[(0,[z1,z2,z3,z8,z5,z1335]),(0,[z1,z42,z13,z33,z8,z5]),(0,[z1,z62,z3,z27,z5,z6]),(0,[z328,z1,z2,z144,z5,z6]),(0,[z1,z3,z8,z5,z29,z724])],[(0,[z1,z2,z3,z8,z5,z316]),(0,[z1,z2,z3,z8,z5,z1336]),(0,[z1,z56,z2,z3,z8,z5]),(0,[z1,z2,z1337,z3,z8,z5]),(0,[z1,z2,z1338,z3,z8,z5]),(1,[z1,z2,z3,z775,z6])],[(0,[z1,z42,z2,z8,z5,z252]),(0,[z1339,z1,z2,z8,z5,z6])],[(0,[z353,z1,z42,z2,z8,z5]),(0,[z1,z1340,z2,z3,z8,z5]),(0,[z1,z2,z3,z5,z6,z1341])]],
   [[(0,[z1,z46,z2,z3,z775,z6])],[(0,[z83,z24,z3,z8,z5,z25]),(0,[z69,z381,z33,z8,z5,z6]),(0,[z130,z2,z48,z143,z8,z5]),(0,[z41,z2,z3,z8,z76,z6]),(0,[z1,z72,z2,z151,z8,z5]),(0,[z1,z2,z3,z8,z5,z1342]),(0,[z1,z2,z1343,z8,z5,z6]),(0,[z1021,z2,z3,z8,z5,z29]),(0,[z1,z46,z2,z3,z16,z113])],[(0,[z2,z3,z8,z5,z80,z6]),(0,[z1344,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1345]),(0,[z1,z89,z3,z277,z28,z6]),(0,[z1,z2,z8,z5,z577,z1178]),(0,[z1,z2,z3,z8,z5,z806]),(0,[z1,z2,z100,z3,z8,z51])],[(0,[z1,z2,z1346,z3,z8,z5]),(0,[z43,z1,z151,z8,z5,z38]),(0,[z1347,z2,z3,z8,z5,z6])],[(0,[z42,z2,z143,z33,z8,z5]),(0,[z1,z72,z2,z47,z8,z5]),(0,[z1,z2,z3,z124,z5,z6]),(0,[z1,z2,z1075,z8,z5,z38]),(0,[z1,z439,z3,z8,z5,z29])],[(0,[z1,z1348,z3,z8,z5,z6])],[(0,[z2,z48,z3,z8,z5,z80])],[(0,[z1,z2,z1349,z3,z8,z5]),(0,[z1,z2,z256,z8,z5,z51]),(0,[z1,z377,z3,z144,z5,z6])],[(0,[z1,z120,z2,z33,z8,z5]),(0,[z1,z2,z3,z8,z5,z1350]),(0,[z1,z2,z3,z277,z5,z6]),(0,[z2,z983,z3,z8,z5,z38]),(0,[z1,z2,z3,z8,z5,z1351]),(0,[z880,z42,z2,z3,z8,z5]),(0,[z1,z182,z2,z3,z472,z5])],[(0,[z1,z2,z3,z8,z1352,z6]),(0,[z1,z2,z1353,z3,z8,z5]),(0,[z1,z2,z3,z5,z261,z38]),(0,[z1,z2,z3,z8,z5,z93])],[(0,[z199,z2,z256,z8,z5,z66]),(0,[z1,z1354,z2,z3,z8,z5])],[(0,[z1,z2,z158,z8,z5,z119]),(0,[z1,z2,z3,z566,z298,z6]),(0,[z83,z24,z3,z8,z5,z294]),(0,[z1,z2,z1355,z3,z8,z5]),(0,[z69,z2,z33,z8,z5,z6]),(0,[z179,z42,z2,z33,z8,z5]),(0,[z1,z2,z3,z5,z6,z1356]),(0,[z1,z2,z3,z8,z5,z1357]),(0,[z1,z2,z3,z8,z5,z1358]),(0,[z1,z2,z3,z8,z1359,z6]),(0,[z1,z42,z2,z3,z166,z54])],[(0,[z0,z21,z3,z8,z5,z38]),(0,[z40,z2,z3,z19,z5,z6]),(0,[z1,z3,z8,z55,z5,z38])],[(0,[z381,z1,z3,z102,z8,z6]),(0,[z1,z2,z1360,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1361]),(0,[z2,z47,z983,z3,z8,z5]),(0,[z117,z1,z516,z2,z8,z6]),(0,[z1,z67,z2,z3,z8,z215])],[(0,[z1,z2,z1362,z3,z8,z5]),(0,[z1,z2,z150,z435,z5,z6])],[(0,[z414,z1,z2,z3,z102,z6]),(0,[z1,z2,z3,z8,z5,z1363])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 511).take 506) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1017).take 383) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1400)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [511, 506, 383] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 135).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 135).take 141).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 276).take 160).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 436).take 76).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [135, 141, 160, 76] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 128, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
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

end PEqualNP.Outside.L_meta_38243

theorem PEqualNP.Outside.L_meta_38243 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241856 * 2 ^ 32 + 4007715008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241856 * 2 ^ 32 + 4007715008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38243.solve