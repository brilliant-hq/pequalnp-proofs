import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_45842

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
  Nat.testBit (4008372960 * 2 ^ 32 + 4008241344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x08016171818d8de5#64 ++ 0x01002c2e3031b1bc#64 ++ 0x3a27e7f3a39f9fe7#64 ++ 0xc744fcfe7473f3fc#64 : BitVec 256),
   (0x00cb0b140c22a2a9#64 ++ 0x8019616281845455#64 ++ 0xfddb1b1c5c63e3ff#64 ++ 0xffbb63638b8c7c7f#64 : BitVec 256),
   (0x1614140ae0545456#64 ++ 0x02c282815c0a8a8a#64 ++ 0xde1c1c1fe07c7c7f#64 ++ 0x5bc38383fc0f8f8f#64 : BitVec 256),
   (0x27601ea076807b00#64 ++ 0x04ec03d40ed00f60#64 ++ 0xefe01fe07f807f86#64 ++ 0xfdfc03fc0ff00ff0#64 : BitVec 256),
   (0x47bea0007b7b0000#64 ++ 0x08f7d4000f6f6000#64 ++ 0x77ffe0007fff8005#64 ++ 0xeefffc000ffff000#64 : BitVec 256),
   (0x87ffdfdf00000000#64 ++ 0x10fffbfbe0000000#64 ++ 0x87ffffff80000003#64 ++ 0xf0fffffff0000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 5]⟩, ⟨.or, [6, 1]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [0, 11]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [12, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00400a2004802b00 0x0008014400900560 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z1 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z2 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3a27e7f3a39f9fe7 0xc744fcfe7473f3fc

def z3 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z4 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z5 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x77ffe0007fff8005 0xeefffc000ffff000

def z6 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x87ffffff80000003 0xf0fffffff0000000

def z7 : W := mkw 0x00010114000080a9 0x8000202280001015 0x0000001c00000078 0x000000038000000f

def z8 : W := mkw 0x272014a076807b00 0x04e402940ed00f60 0x6a2004e07f807f84 0x0d44009c0ff00ff0

def z9 : W := mkw 0x1e15757be1ddddf7 0x03c2aeaf7c3bbbbe 0xfe3fffffe3ffffff 0xdfc7fffffc7fffff

def z10 : W := mkw 0x1614140a60505012 0x02c282814c0a0a02 0xc418180c40606018 0x18830301880c0c03

def z11 : W := mkw 0x41aaa0001b2b0000 0x0835540003656000 0x33e7e0003f9f8005 0xe67cfc0007f3f000

def z12 : W := mkw 0x80415fdf00000000 0x10082bfbe0000000 0x80001fff80000002 0x100003fff0000000

def z13 : W := mkw 0x809fc15f00000000 0x1013f82be0000000 0x001fe01f80000001 0x0003fc03f0000000

def z14 : W := mkw 0x0000000000000000 0x0000000000000000 0x580000004060607c 0x0b000000080c0c0f

def z15 : W := mkw 0x0000000004002200 0x0000000000800440 0x680000005c006384 0x0d0000000b800c70

def z16 : W := mkw 0xc7ffffdf7f7ba2a9 0x98fffffbefef7455 0xffffffffffffe3ff 0xfffffffffffffc7f

def z17 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x38000000239f9fe4 0x070000000473f3fc

def z18 : W := mkw 0x67febea07ffb7b00 0x0cffd7d40fff6f60 0xffffffe07fffff87 0xfffffffc0ffffff0

def z19 : W := mkw 0x08cb6b750dababa9 0x81196d6ea1b57575 0x21e3e3e01f838380 0xa43c7c7c03f07070

def z20 : W := mkw 0x87ffdfdf0c222208 0x90fffbfbe1844441 0xc7ffffffdc60601b 0xf8fffffffb8c0c03

def z21 : W := mkw 0x4734a00073590000 0x08e694000e6b2000 0x563ce00063fc0005 0x4ac79c000c7f8000

def z22 : W := mkw 0x41ebab141f2ba2a9 0x883d756283e57455 0x21e3e3001f838380 0xa43c7c6003f07070

def z23 : W := mkw 0x00cb0b1400000000 0x0019616280000000 0x85db1b1c00000003 0xf0bb636380000000

def z24 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x0224e4e380000000 0x00449c9c70000000

def z25 : W := mkw 0x2000002072805900 0x040000040e500b20 0x0000000023801c00 0x0000000004700380

def z26 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z27 : W := mkw 0xa774deeb76807b00 0x14ee9bdd6ed00f60 0xefe4ffe3ff807f86 0xfdfc9ffc7ff00ff0

def z28 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xd41c181fc07c6079 0x1a838303f80f8c0f

def z29 : W := mkw 0x0000000000000000 0x0000000000000000 0x2220000023800004 0xc444000004700000

def z30 : W := mkw 0x27601e8076007200 0x04ec03d00ec00e40 0xc5c018005c006000 0x38b803000b800c00

def z31 : W := mkw 0xa7ffdfdf76007200 0x14fffbfbeec00e40 0xc7ffffffdc006003 0xf8fffffffb800c00

def z32 : W := mkw 0x0800002080848de5 0x01000004101091bc 0x0800000000001fe0 0x01000000000003fc

def z33 : W := mkw 0x00010110000080a1 0x0000202200001014 0x08000310000003e2 0x010000620000007c

def z34 : W := mkw 0x2f617ff1f78dffe5 0x05ec2ffe3ef1bffc 0xffe7fff3ff9fffe7 0xfffcfffe7ff3fffc

def z35 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x55dfe0005c7f8001 0x2abbfc000b8ff000

def z36 : W := mkw 0x1614140a60505012 0x02c282814c0a0a02 0xce181c0c60607c1e 0x59c303818c0c0f83

def z37 : W := mkw 0x0000200001090000 0x0000040000212000 0x3227e000239f8005 0xc644fc000473f000

def z38 : W := mkw 0x008a2000092b0000 0x0011440001256000 0x77ffe0007fff8005 0xeefffc000ffff000

def z39 : W := mkw 0x87ffdfdf04002200 0x10fffbfbe0800440 0xefffffffdc006387 0xfdfffffffb800c70

def z40 : W := mkw 0x27611fb47680fba9 0x84ec23f68ed01f75 0xefe01ffc7f807ffe 0xfdfc03ff8ff00fff

def z41 : W := mkw 0x0000000080040444 0x0000000010008088 0x1a040413a01c1c67 0x434080827403838c

def z42 : W := mkw 0x0614140a00000000 0x00c2828140000000 0x8418180c00000000 0x1083030180000000

def z43 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0007e01380000001 0x0000fc0270000000

def z44 : W := mkw 0x67bea0207ffb7b00 0x0cf7d4040fff6f60 0x7fffe0007fffff85 0xeffffc000ffffff0

def z45 : W := mkw 0xa7615fff76807b00 0x14ec2bffeed00f60 0xefe01fffff807f86 0xfdfc03fffff00ff0

def z46 : W := mkw 0x08414b758484afed 0x8108296eb09095fd 0x88001fff80007ffa 0x110003fff0000fff

def z47 : W := mkw 0x08cb6b758dafafed 0x81196d6eb1b5f5fd 0xffffffffffffffff 0xffffffffffffffff

def z48 : W := mkw 0x8fffffff8dafafed 0x91fffffff1b5f5fd 0xffffffffffffffff 0xffffffffffffffff

def z49 : W := mkw 0x81ebcbd500000000 0x103d797aa0000000 0x01e3e3e000000000 0xa03c7c7c00000000

def z50 : W := mkw 0x408aa000092b0000 0x0811540001256000 0x0003e00000038000 0x00007c0000007000

def z51 : W := mkw 0x008a000008220000 0x0011400001044000 0x75db00005c638005 0xeebb60000b8c7000

def z52 : W := mkw 0x0801417180848de5 0x0100282e301091bc 0x080007f380001fe2 0x010000fe700003fc

def z53 : W := mkw 0x0614000060500000 0x00c280000c0a0000 0x561c0000607c0005 0x4ac380000c0f8000

def z54 : W := mkw 0x5734b40af35d5456 0x0ae696815e6baa8a 0x0224e403a39c1c00 0x00449c8074738380

def z55 : W := mkw 0x00ca0a040c222208 0x8019414081844441 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z56 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x23e7e0003f9f8000 0xa47cfc0007f3f000

def z57 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xcdd81b1c5c6063fa 0x39bb03638b8c0c7f

def z58 : W := mkw 0x87ffdfdf72000000 0x10fffbfbee400000 0xe7ffffffff800007 0xfcfffffffff00000

def z59 : W := mkw 0x80dfcb5f0c22a2a9 0x901bf96be1845455 0xfddffb1fdc63e3ff 0xffbbff63fb8c7c7f

def z60 : W := mkw 0x07be800000000000 0x00f7d00000000000 0x07ffe00000000001 0xe0fffc0000000000

def z61 : W := mkw 0x400020007b7b0000 0x080004000f6f6000 0x700000007fff8004 0x0e0000000ffff000

def z62 : W := mkw 0x57beb40afb7f5456 0x0af7d6815f6fea8a 0xfffffc1ffffffc7f 0xffffff83ffffff8f

def z63 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0227e7f380000003 0xc044fcfe70000000

def z64 : W := mkw 0x0720000072000000 0x00e400000e400000 0x45c000005c000000 0x28b800000b800000

def z65 : W := mkw 0x08cb2b348dafafed 0x8119656691b5f5fd 0xfddb1b1c7fffffff 0xffbb63638fffffff

def z66 : W := mkw 0x47aaa0007b2b0000 0x08f554000f656000 0x67e3e0007f838004 0xecfc7c000ff07000

def z67 : W := mkw 0x47bea0001b2b0000 0x08f7d40003656000 0x27ffe0001f838001 0xe4fffc0003f07000

def z68 : W := mkw 0x0720000072000000 0x00e400000e400000 0x67e000007f800004 0xecfc00000ff00000

def z69 : W := mkw 0x00400a0004002200 0x0008014000800440 0xedc01b005c006386 0xfdb803600b800c70

def z70 : W := mkw 0x008b0114082280a9 0x8011602281045015 0x101b001c00638079 0x02036003800c700f

def z71 : W := mkw 0x00010110000080a1 0x0000202200001014 0x38030310000383e7 0xc70060620000707c

def z72 : W := mkw 0x08006061818d0d44 0x01000c0c3031a1a8 0x0224e4e3a39c1c00 0x00449c9c74738380

def z73 : W := mkw 0x0800406180840d44 0x0100080c301081a8 0x000004e380001c00 0x0000009c70000380

def z74 : W := mkw 0x0000002000800900 0x0000000400100120 0x2a2007e023801f86 0xc54400fc047003f0

def z75 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x561c0403e07c1c05 0x4ac380807c0f8380

def z76 : W := mkw 0x47bea000fb7f0444 0x08f7d4001f6fe088 0x7fffe413ffff9c67 0xeffffc827ffff38c

def z77 : W := mkw 0x0600140060005000 0x00c002800c000a00 0xce001c0060007c06 0x59c003800c000f80

def z78 : W := mkw 0x37741eaaf6d47f56 0x06ee83d55eda8fea 0xfffc1ffffffc7fff 0xffff83ffffff8fff

def z79 : W := mkw 0x1000000a80040456 0x020000015000808a 0x0000001f80000078 0x00000003f000000f

def z80 : W := mkw 0x87ffdfdf60500000 0x10fffbfbec0a0000 0xd7ffffffe07c0007 0xfafffffffc0f8000

def z81 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xa7ffffff9c038383 0xf4fffffff3807070

def z82 : W := mkw 0x3f757ffbf7ddfff7 0x07eeafff7efbbffe 0xffffffffffffffff 0xffffffffffffffff

def z83 : W := mkw 0x0614000060500000 0x00c280000c0a0000 0x4418000040600000 0x08830000080c0000

def z84 : W := mkw 0x00cb4b550c22a2a9 0x8019696aa1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z85 : W := mkw 0x4734a00073590000 0x08e694000e6b2000 0x3227e000239f8005 0xc644fc000473f000

def z86 : W := mkw 0x00010110000080a1 0x0000202200001014 0x2003030000038380 0x8400606000007070

def z87 : W := mkw 0x47ffab147f7ba2a9 0x88fff5628fef7455 0xfffffb1c7fffe3ff 0xffffff638ffffc7f

def z88 : W := mkw 0x47ffab147b7b0000 0x08fff5628f6f6000 0xf7fffb1c7fff8007 0xfeffff638ffff000

def z89 : W := mkw 0x0614140a60005000 0x00c282814c000a00 0xce1c1c1fe0007c07 0x59c38383fc000f80

def z90 : W := mkw 0x16df1f1eec76f6ff 0x82dbe3e3dd8ededf 0xffdf1f1ffc7fffff 0xfffbe3e3ff8fffff

def z91 : W := mkw 0x10411f1e8404f6ff 0x820823e3d0809edf 0x88001f1f80007ffa 0x110003e3f0000fff

def z92 : W := mkw 0x27eb1fb47ea2fba9 0x84fd63f68fd45f75 0xfffb1ffc7fe3ffff 0xffff63ff8ffc7fff

def z93 : W := mkw 0x47bfe1517b7b0000 0x08f7fc2a2f6f6000 0x77ffe7f3ffff8007 0xeefffcfe7ffff000

def z94 : W := mkw 0x89ebebf5818d8de5 0x113d7d7eb031b1bc 0x3be7e7f3a39f9fe7 0xe77cfcfe7473f3fc

def z95 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0x981b1b1c0063e3fb 0x13036363800c7c7f

def z96 : W := mkw 0x6ffffff1ffffffe5 0x0dfffffe3ffffffc 0xfffffff3ffffffe7 0xfffffffe7ffffffc

def z97 : W := mkw 0x0000000080040444 0x0000000010008088 0x18000000201c1c64 0x030000000403838c

def z98 : W := mkw 0x2000002076807b00 0x040000040ed00f60 0x680000007f807f84 0x0d0000000ff00ff0

def z99 : W := mkw 0x97ffdfdfe0545456 0x12fffbfbfc0a8a8a 0xdfffffffe07c7c7f 0xfbfffffffc0f8f8f

def z100 : W := mkw 0xa7ffdfff76807b00 0x14fffbffeed00f60 0xefffffffff807f87 0xfdfffffffff00ff0

def z101 : W := mkw 0x00cb4b5500000000 0x0019696aa0000000 0x87ffffff80000003 0xf0fffffff0000000

def z102 : W := mkw 0x00400a0000000000 0x0008014000000000 0x85c01b0000000002 0xf0b8036000000000

def z103 : W := mkw 0x87bfd5df00000000 0x10f7fabbe0000000 0x023fe4ff80000001 0x0047fc9ff0000000

def z104 : W := mkw 0x272014a072805900 0x04e402940e500b20 0x022004e023801c00 0x0044009c04700380

def z105 : W := mkw 0x00010130008089a1 0x0000202600101134 0x3a2307f023839fe7 0xc74460fe047073fc

def z106 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xe5db1b0c5c63e398 0xbcbb63618b8c7c73

def z107 : W := mkw 0x87ffcbd500000000 0x10fff97aa0000000 0x07ffe3e000000001 0xe0fffc7c00000000

def z108 : W := mkw 0x1e14746be1dd5d56 0x03c28e8d7c3babaa 0x0224e4e3a39c1c00 0x00449c9c74738380

def z109 : W := mkw 0x1014000a80540456 0x02028001500a808a 0x1a1c041fa07c1c7f 0x43438083f40f838f

def z110 : W := mkw 0x81ebdfdf00000000 0x103d7bfbe0000000 0x81e3ffff80000002 0xb03c7ffff0000000

def z111 : W := mkw 0xc7ffffdf1b2b0000 0x18fffffbe3656000 0xa7ffffff9f838003 0xf4fffffff3f07000

def z112 : W := mkw 0xc7ffffdf7b7b0000 0x18fffffbef6f6000 0xf7ffffffffff8007 0xfefffffffffff000

def z113 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xc61c1c0fe07c7c18 0x18c38381fc0f8f83

def z114 : W := mkw 0x008b0114082280a9 0x8011602281045015 0x0003000000038000 0x0000600000007000

def z115 : W := mkw 0x41aaa0001b2b0000 0x0835540003656000 0x21e3e0001f838000 0xa43c7c0003f07000

def z116 : W := mkw 0x8fffffff018989a1 0x11ffffffe0313134 0xa7ffffff83838383 0xf4fffffff0707070

def z117 : W := mkw 0x08002000810d84e5 0x010004001021b09c 0x10000000001f8060 0x020000000003f00c

def z118 : W := mkw 0x41ebab141f2ba2a9 0x883d756283e57455 0xfdfbfb1c5fe3e3ff 0xffbf7f638bfc7c7f

def z119 : W := mkw 0x47ffab147f7ba2a9 0x88fff5628fef7455 0x77ffe3007fff8385 0xeefffc600ffff070

def z120 : W := mkw 0x809fc15f00000000 0x1013f82be0000000 0x023fe7ff80000003 0xc047fcfff0000000

def z121 : W := mkw 0x47be80007a720000 0x08f7d0000f4e4000 0x45d800005c600000 0x28bb00000b8c0000

def z122 : W := mkw 0x80415fdf00000000 0x10082bfbe0000000 0x8227ffff80000003 0xd044fffff0000000

def z123 : W := mkw 0x088b617589af8ded 0x81116c2eb135f1bd 0x3a3fe7ffa3ff9fff 0xc747fcfff47ff3ff

def z124 : W := mkw 0xa0415fff04807b00 0x14082bffe0900f60 0x88001fff80007f82 0x110003fff0000ff0

def z125 : W := mkw 0x87ffdfdf08220000 0x10fffbfbe1044000 0xf7ffffffdc638007 0xfefffffffb8c7000

def z126 : W := mkw 0x16df1f1ee0545456 0x02dbe3e3dc0a8a8a 0xdfdf1f1fe07c7c7f 0xfbfbe3e3fc0f8f8f

def z127 : W := mkw 0x00cb0b148c26a6ed 0x801961629184d4dd 0xffdf1f1ffc7fffff 0xfffbe3e3ff8fffff

def z128 : W := mkw 0x08016151810d84e5 0x01002c2a3021b09c 0x1007e013801f8061 0x0200fc027003f00c

def z129 : W := mkw 0x409ea000097b0000 0x0813d400012f6000 0x101fe000007f8001 0x0203fc00000ff000

def z130 : W := mkw 0x20cb0b347ea2fba9 0x841961668fd45f75 0xfddb1b1c7fe3ffff 0xffbb63638ffc7fff

def z131 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc18181c4060607f 0x5b830303880c0c0f

def z132 : W := mkw 0x069e000068720000 0x00d3c0000d0e4000 0x77df00007c7f8005 0xeefbe0000f8ff000

def z133 : W := mkw 0x0614140a00000000 0x00c2828140000000 0x861c1c1f80000003 0x50c38383f0000000

def z134 : W := mkw 0x30401eaa84847f56 0x060803d550908fea 0x88001fff80007ffa 0x110003fff0000fff

def z135 : W := mkw 0x0000002000800900 0x0000000400100120 0x202003e003800380 0x8404007c00700070

def z136 : W := mkw 0x20401ea004807b00 0x040803d400900f60 0x88001fe000007f82 0x110003fc00000ff0

def z137 : W := mkw 0xcffffffffbff8de5 0x19ffffffff7ff1bc 0xffffffffffff9fe7 0xfffffffffffff3fc

def z138 : W := mkw 0x1014000a80540456 0x02028001500a808a 0x101c001f807c0079 0x02038003f00f800f

def z139 : W := mkw 0x67beb4a07bfb5900 0x0cf7d6940f7f6b20 0x77ffe4e07fff9c05 0xeefffc9c0ffff380

def z140 : W := mkw 0x00ca0a040c22a2a9 0x8019414081845455 0xfdd8180c5c63e3fc 0x3fbb03018b8c7c7f

def z141 : W := mkw 0x10000000e0545456 0x020000001c0a8a8a 0x58000000607c7c7c 0x0b0000000c0f8f8f

def z142 : W := mkw 0x80dfdfdf00000000 0x101bfbfbe0000000 0x801fffff80000003 0x1003fffff0000000

def z143 : W := mkw 0x0000002000800900 0x0000000400100120 0x022004e023801c00 0x0044009c04700380

def z144 : W := mkw 0x2f607ee1f78d7f44 0x05ec0fdc3ef1afe8 0xefe4ffe3ff9c7f86 0xfdfc9ffc7ff38ff0

def z145 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0xfe3fffffe3ffffff 0xdfc7fffffc7fffff

def z146 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x02040403a01c1c00 0x0040808074038380

def z147 : W := mkw 0x4fbfe171fbff8de5 0x09f7fc2e3f7ff1bc 0x7fffe7f3ffff9fe7 0xeffffcfe7ffff3fc

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x0227e00000000001 0xc044fc0000000000

def z149 : W := mkw 0x27601e8076007200 0x04ec03d00ec00e40 0xc7e01fe05c006002 0xf8fc03fc0b800c00

def z150 : W := mkw 0x87fe9e8e00000000 0x10ffd3d1c0000000 0x85d8180c00000000 0x30bb030180000000

def z151 : W := mkw 0x20400aa004802b00 0x0408015400900560 0x000003e000000380 0x0000007c00000070

def z152 : W := mkw 0x37601eaaf6847f56 0x06ec03d55ed08fea 0xefe01fffff807ffe 0xfdfc03fffff00fff

def z153 : W := mkw 0x0000000000000000 0x0000000000000000 0x2800030000000386 0xc500006000000070

def z154 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0x21c303001c038380 0xa438606003807070

def z155 : W := mkw 0x2f2175f1f38ddde5 0x05e42ebe3e71bbbc 0x3a27e7f3a39f9fe7 0xc744fcfe7473f3fc

def z156 : W := mkw 0x0720000072000000 0x00e400000e400000 0x0220000023800000 0x0044000004700000

def z157 : W := mkw 0x00cb0b1400000000 0x0019616280000000 0xdddb1b1c4060607f 0xfbbb6363880c0c0f

def z158 : W := mkw 0x00cb0b1404002200 0x0019616280800440 0xeddb1b1c5c006387 0xfdbb63638b800c70

def z159 : W := mkw 0x080020208dafafed 0x8100040411b5f5fd 0x780000007ffffffc 0x0f0000000fffffff

def z160 : W := mkw 0x409ea0007b7b0000 0x0813d4000f6f6000 0x701fe0007fff8005 0x0e03fc000ffff000

def z161 : W := mkw 0x0000000000000000 0x0000000000000000 0x0a00040020001c06 0x4140008004000380

def z162 : W := mkw 0x29616bf11789aba1 0x052c2d7e22f13574 0x21e3e3e01f838380 0xa43c7c7c03f07070

def z163 : W := mkw 0x409ea000097b0000 0x0813d400012f6000 0x323fe00023ff8005 0xc647fc00047ff000

def z164 : W := mkw 0x1615555be0545456 0x02c2aaab7c0a8a8a 0xde3fffffe07c7c7f 0xdbc7fffffc0f8f8f

def z165 : W := mkw 0x1000140a80045456 0x0200028150008a8a 0x88001c1f80007c7a 0x11000383f0000f8f

def z166 : W := mkw 0x00410b140400a2a9 0x8008216280801455 0x88001b1c000063fa 0x1100036380000c7f

def z167 : W := mkw 0x0614140a00000000 0x00c2828140000000 0xde1c1c1fc060607f 0x5bc38383f80c0c0f

def z168 : W := mkw 0x800054cb00000000 0x10000a9960000000 0x000004e380000000 0x0000009c70000000

def z169 : W := mkw 0x0000000080040444 0x0000000010008088 0x10040013801c0061 0x020080027003800c

def z170 : W := mkw 0x1614000ae0540456 0x02c280015c0a808a 0x561c001fe07c007d 0x4ac38003fc0f800f

def z171 : W := mkw 0x8735d5db00000000 0x10e6babb60000000 0x0227e7f380000003 0xc044fcfe70000000

def z172 : W := mkw 0x08016171018989a1 0x01002c2e20313134 0x2023e3e003838380 0x84047c7c00707070

def z173 : W := mkw 0x00ca0a040c222208 0x8019414081844441 0xedd81b0c5c60639e 0xfdbb03618b8c0c73

def z174 : W := mkw 0x06cb1f146c22f2a9 0x80d963e28d845e55 0xffdb1f1c7c63ffff 0xfffb63e38f8c7fff

def z175 : W := mkw 0x97ffdfdf80045456 0x12fffbfbf0008a8a 0x8fffffff80007c7b 0xf1fffffff0000f8f

def z176 : W := mkw 0x1014000ae0545456 0x020280015c0a8a8a 0x581c001fe07c7c7d 0x0b038003fc0f8f8f

def z177 : W := mkw 0x07be800008220000 0x00f7d00001044000 0x77ffe0005c638005 0xeefffc000b8c7000

def z178 : W := mkw 0x809e800e00000000 0x1013d001c0000000 0x0018000c00000000 0x0003000180000000

def z179 : W := mkw 0x07601ea000800900 0x00ec03d400100120 0xafe01fe023801f86 0xf5fc03fc047003f0

def z180 : W := mkw 0x47beb4007b7b5000 0x08f7d6800f6f6a00 0xfffffc007ffffc07 0xffffff800fffff80

def z181 : W := mkw 0xc734f4cb73590000 0x18e69e996e6b2000 0x0224e4e3a39c0000 0x00449c9c74738000

def z182 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x1a040413a01c1c67 0x434080827403838c

def z183 : W := mkw 0x10cb1f1e8c26f6ff 0x821963e3d184dedf 0xfddb1f1fdc63ffff 0xffbb63e3fb8c7fff

def z184 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3807e013a39f9fe5 0x0700fc027473f3fc

def z185 : W := mkw 0x0000404100000000 0x0000080820000000 0x0224e4e380000000 0x00449c9c70000000

def z186 : W := mkw 0x08014171008089a1 0x0100282e20101134 0x000003e000000380 0x0000007c00000070

def z187 : W := mkw 0x67eabea07fab7b00 0x0cfd57d40ff56f60 0xefe3ffe07f83ff86 0xfdfc7ffc0ff07ff0

def z188 : W := mkw 0x969fd55fe0545456 0x12d3faabfc0a8a8a 0xde1ffc1fe07c7c7f 0x5bc3ff83fc0f8f8f

def z189 : W := mkw 0x0000002000800900 0x0000000400100120 0x2800000023801f84 0x05000000047003f0

def z190 : W := mkw 0x0001011000000000 0x0000202200000000 0x0003031000000003 0xc000606200000000

def z191 : W := mkw 0x00cb0b140c222208 0x8019616281844441 0xc5db1b1c5c60601b 0xf8bb63638b8c0c03

def z192 : W := mkw 0x27611fb07680fba1 0x04ec23f60ed01f74 0xffe31ff07f83ffe7 0xfffc63fe0ff07ffc

def z193 : W := mkw 0x008a000008220000 0x0011400001044000 0x21c300001c038000 0xa438600003807000

def z194 : W := mkw 0x4014a00001590000 0x08029400002b2000 0x0004e000001c0000 0x00009c0000038000

def z195 : W := mkw 0x47beb40a7b7b0000 0x08f7d6814f6f6000 0xf7fffc1fffff8007 0xfeffff83fffff000

def z196 : W := mkw 0x8fffffff818d8de5 0x11fffffff031b1bc 0xbfffffffa39f9fe7 0xf7fffffff473f3fc

def z197 : W := mkw 0x21600aa076807b00 0x042c01540ed00f60 0x69e003e07f807f84 0xad3c007c0ff00ff0

def z198 : W := mkw 0x16de1e0eec76765e 0x82dbc3c1dd8ececb 0xdfdc1c1ffc7c7c7f 0x7bfb8383ff8f8f8f

def z199 : W := mkw 0x00400a0004002200 0x0008014000800440 0x21c003001c000380 0xa438006003800070

def z200 : W := mkw 0x4f34e061f3dd0d44 0x09e69c0c3e7ba1a8 0x0224e4e3a39c1c00 0x00449c9c74738380

def z201 : W := mkw 0x4734800072500000 0x08e690000e4a0000 0x0000000000000000 0x0000000000000000

def z202 : W := mkw 0x4734a00073590000 0x08e694000e6b2000 0x67e4e0007f9c0004 0xecfc9c000ff38000

def z203 : W := mkw 0x408a20007b7b0000 0x081144000f6f6000 0x75db00007fff8005 0xeebb60000ffff000

def z204 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x85dff81f80000001 0x30bbff03f0000000

def z205 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xcc181c1fc0607c7a 0x19830383f80c0f8f

def z206 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xcdc01fe05c007f82 0x39b803fc0b800ff0

def z207 : W := mkw 0x1014140a80545456 0x02028281500a8a8a 0x981c1c1f807c7c7b 0x13038383f00f8f8f

def z208 : W := mkw 0x272014a072805900 0x04e402940e500b20 0x67e004e07f801c04 0xecfc009c0ff00380

def z209 : W := mkw 0x0120000012000000 0x0024000002400000 0x21e000001f800000 0xa43c000003f00000

def z210 : W := mkw 0x00410b140400a2a9 0x8008216280801455 0xedc01b1c5c0063fe 0xfdb803638b800c7f

def z211 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x8a041c1fa01c7c7a 0x11408383f4038f8f

def z212 : W := mkw 0x87bed4cb00000000 0x10f7da9960000000 0x07ffe4e380000001 0xe0fffc9c70000000

def z213 : W := mkw 0x8014c04b00000000 0x1002980960000000 0x0004e00380000000 0x00009c0070000000

def z214 : W := mkw 0x9734d4cbe0545456 0x12e69a997c0a8a8a 0xde3cfcffe07c7c7f 0x5bc79f9ffc0f8f8f

def z215 : W := mkw 0x889fe15f810d84e5 0x1113fc2bf021b09c 0x101fe01f801f8061 0x0203fc03f003f00c

def z216 : W := mkw 0x400020007b7b0000 0x080004000f6f6000 0x7227e0007fff8005 0xce44fc000ffff000

def z217 : W := mkw 0x21600aa016802b00 0x042c015402d00560 0x21e003e01f800380 0xa43c007c03f00070

def z218 : W := mkw 0x0f617ff1818d8de5 0x01ec2ffe3031b1bc 0xbfe7fff3a39f9fe7 0xf7fcfffe7473f3fc

def z219 : W := mkw 0x1614140a80045456 0x02c2828150008a8a 0x8e1c1c1f80007c7b 0x51c38383f0000f8f

def z220 : W := mkw 0x0600140000000000 0x00c0028000000000 0x86001c0000000002 0x50c0038000000000

def z221 : W := mkw 0x00ca0a040c222208 0x8019414081844441 0x01c000001c000000 0x2038000003800000

def z222 : W := mkw 0xc7ffffdf73590000 0x18fffffbee6b2000 0x87ffffffa39c0003 0xf0fffffff4738000

def z223 : W := mkw 0xb7ffdffff6d47f56 0x16fffbfffeda8fea 0xfffffffffffc7fff 0xffffffffffff8fff

def z224 : W := mkw 0x08cb6b750dababa9 0x81196d6ea1b57575 0xfdfbfbfc5fe3e3ff 0xffbf7f7f8bfc7c7f

def z225 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0023e3e000000000 0x80047c7c00000000

def z226 : W := mkw 0x088b6155892f84ed 0x81116c2ab125f09d 0x101fe01f807f8079 0x0203fc03f00ff00f

def z227 : W := mkw 0x07601e8000000000 0x00ec03d000000000 0x87e01fe000000002 0xf0fc03fc00000000

def z228 : W := mkw 0x07600a0076002200 0x00ec01400ec00440 0xefe01b007f806386 0xfdfc03600ff00c70

def z229 : W := mkw 0x10000000e0545456 0x020000001c0a8a8a 0x5a040413e07c7c7f 0x4b4080827c0f8f8f

def z230 : W := mkw 0x41bea0001b7b0000 0x0837d400036f6000 0x31ffe0001fff8001 0xa63ffc0003fff000

def z231 : W := mkw 0x67603ea07ffb7b00 0x0cec07d40fff6f60 0xffe01fe07fffff86 0xfffc03fc0ffffff0

def z232 : W := mkw 0x10000000e0545456 0x020000001c0a8a8a 0x00000000201c1c00 0x0000000004038380

def z233 : W := mkw 0xc7bef4cb7b7b0000 0x18f7de996f6f6000 0x77ffe4e3ffff8005 0xeefffc9c7ffff000

def z234 : W := mkw 0x00410b140400a2a9 0x8008216280801455 0xb8031b1c0003e3ff 0xd700636380007c7f

def z235 : W := mkw 0x27741eaa76807b00 0x04ee83d54ed00f60 0xeffc1fffff807f87 0xfdff83fffff00ff0

def z236 : W := mkw 0x2f603ea0f78dffe5 0x05ec07d41ef1bffc 0xffe01fe07f9fffe6 0xfffc03fc0ff3fffc

def z237 : W := mkw 0xc7febe8e7b7b0000 0x18ffd7d1cf6f6000 0xf7fff80c7fff8005 0xfeffff018ffff000

def z238 : W := mkw 0x07601e8072000000 0x00ec03d00e400000 0xe7e01fe07f800006 0xfcfc03fc0ff00000

def z239 : W := mkw 0x0720002072800900 0x00e400040e500120 0x6fe007e07f801f86 0xedfc00fc0ff003f0

def z240 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xdfffffffc060607f 0xfbfffffff80c0c0f

def z241 : W := mkw 0x0000000008220000 0x0000000001044000 0x700000005c638004 0x0e0000000b8c7000

def z242 : W := mkw 0x0801417180848de5 0x0100282e301091bc 0x2a2007f3a3801fe6 0xc54400fe747003fc

def z243 : W := mkw 0x21600aa016802b00 0x042c015402d00560 0x2be007e03f801f86 0xe57c00fc07f003f0

def z244 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x85d81fff80000002 0x30bb03fff0000000

def z245 : W := mkw 0xc7ffdfdf7a720000 0x18fffbfbef4e4000 0xc7ffffffdc600003 0xf8fffffffb8c0000

def z246 : W := mkw 0x27741ea076d07b00 0x04ee83d40eda0f60 0xfffc1fe07ffc7f87 0xffff83fc0fff8ff0

def z247 : W := mkw 0x4fbfe1717bfb89a1 0x09f7fc2e2f7f7134 0x77ffe3e07fff8385 0xeefffc7c0ffff070

def z248 : W := mkw 0x08002020018989a1 0x0100040400313134 0x2000000003838380 0x0400000000707070

def z249 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xa9c31b1c1c03e3fa 0xb538636383807c7f

def z250 : W := mkw 0x409e800008720000 0x0813d000010e4000 0x0018000000600000 0x00030000000c0000

def z251 : W := mkw 0xd7ffffdffb7f5456 0x1afffffbff6fea8a 0xfffffffffffffc7f 0xffffffffffffff8f

def z252 : W := mkw 0x41aaa0007b7b0000 0x083554000f6f6000 0x71e3e0007fff8004 0xae3c7c000ffff000

def z253 : W := mkw 0x27ea1ea47ea27b08 0x84fd43d48fd44f61 0xeff81fec7fe07f9e 0xfdff03fd8ffc0ff3

def z254 : W := mkw 0x41aaa0001b2b0000 0x0835540003656000 0x75fbe0005fe38005 0xeebf7c000bfc7000

def z255 : W := mkw 0x0614140a00000000 0x00c2828140000000 0x0204040380000000 0x0040808070000000

def z256 : W := mkw 0x57beb40a7b7b5012 0x0af7d6814f6f6a02 0xf7fff80c7fffe01d 0xfeffff018ffffc03

def z257 : W := mkw 0x37741e8af6547656 0x06ee83d15eca8eca 0xdfdc1c1ffc7c7c7f 0x7bfb8383ff8f8f8f

def z258 : W := mkw 0x08016151810d84e5 0x01002c2a3021b09c 0x1227e7f3801f8063 0xc244fcfe7003f00c

def z259 : W := mkw 0x0801417180848de5 0x0100282e301091bc 0x380307f380039fe7 0xc70060fe700073fc

def z260 : W := mkw 0x20400a2076807b00 0x040801440ed00f60 0xedc01b007f807f86 0xfdb803600ff00ff0

def z261 : W := mkw 0x1014000a00500012 0x02028001400a0002 0x0018000c00600018 0x00030001800c0003

def z262 : W := mkw 0x47be80007a720000 0x08f7d0000f4e4000 0x67f800007fe00004 0xecff00000ffc0000

def z263 : W := mkw 0x0001415100000000 0x0000282a20000000 0x000007f380000002 0x000000fe70000000

def z264 : W := mkw 0xc7ffffdf097b0000 0x18fffffbe12f6000 0x97ffffff807f8003 0xf2fffffff00ff000

def z265 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0xfffff81c7fffe07f 0xffffff038ffffc0f

def z266 : W := mkw 0x00014151000080a1 0x0000282a20001014 0x3a27e7f3800383e7 0xc744fcfe7000707c

def z267 : W := mkw 0x080161718dafafed 0x81002c2e31b5f5fd 0x7a27e7f3ffffffff 0xcf44fcfe7fffffff

def z268 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xedc31b005c03e386 0xfdb863600b807c70

def z269 : W := mkw 0x272014a072805900 0x04e402940e500b20 0x2a2007e023801f86 0xc54400fc047003f0

def z270 : W := mkw 0x00400a0004002200 0x0008014000800440 0x88001b0000006382 0x1100036000000c70

def z271 : W := mkw 0x81ea8a8400000000 0x103d515080000000 0x01c0000000000000 0x2038000000000000

def z272 : W := mkw 0x80401e8e00000000 0x100803d1c0000000 0x8000180c00000000 0x1000030180000000

def z273 : W := mkw 0x97fe9e8ee0545456 0x12ffd3d1dc0a8a8a 0xdfdc1c1fe07c7c7f 0x7bfb8383fc0f8f8f

def z274 : W := mkw 0x489fe151897f84e5 0x0913fc2a312ff09c 0x101fe013807f8061 0x0203fc02700ff00c

def z275 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xdc18180c607c7c7c 0x1b8303018c0f8f8f

def z276 : W := mkw 0x0720200073090000 0x00e404000e612000 0x77e7e0007f9f8005 0xeefcfc000ff3f000

def z277 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x3a040413a39f9fe7 0x474080827473f3fc

def z278 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x47fce0007ffc0000 0x28ff9c000fff8000

def z279 : W := mkw 0x81ebcbd500000000 0x103d797aa0000000 0x85fbfbfc00000003 0xf0bf7f7f80000000

def z280 : W := mkw 0x07601e8060005000 0x00ec03d00c000a00 0xcfe01fe060007c06 0xf9fc03fc0c000f80

def z281 : W := mkw 0x169f151ee876d4ff 0x82d3e2a3dd0eda9f 0xde1f1c1fe07ffc7f 0x5bc3e383fc0fff8f

def z282 : W := mkw 0x20401ea004807b00 0x040803d400900f60 0xaa201fe023807f86 0xd54403fc04700ff0

def z283 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x2227e7e3a39f9f80 0x8444fcfc7473f3f0

def z284 : W := mkw 0x4734a00073590000 0x08e694000e6b2000 0x0224e000239c0000 0x00449c0004738000

def z285 : W := mkw 0x80415fdf0400a2a9 0x90082bfbe0801455 0x88001fff800063fa 0x110003fff0000c7f

def z286 : W := mkw 0x0000202001890900 0x0000040400312120 0x3a27e7e0239f9f87 0xc744fcfc0473f3f0

def z287 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xc7e01ce07f807c00 0x38fc039c0ff00f80

def z288 : W := mkw 0x87fe9e8e00000000 0x10ffd3d1c0000000 0x87dc1c1f80000003 0x70fb8383f0000000

def z289 : W := mkw 0x87ebdfd500000000 0x10fd7bfaa0000000 0x87e3ffe000000002 0xf0fc7ffc00000000

def z290 : W := mkw 0x21601ea016807b00 0x042c03d402d00f60 0xa9e01fe01f807f82 0xb53c03fc03f00ff0

def z291 : W := mkw 0x18002020e1ddddf7 0x030004041c3bbbbe 0x7800000063fffffc 0x0f0000000c7fffff

def z292 : W := mkw 0x27603ea077897b00 0x04ec07d40ef12f60 0xffe7ffe07f9fff87 0xfffcfffc0ff3fff0

def z293 : W := mkw 0x400000007a720000 0x080000000f4e4000 0x400000005c600000 0x080000000b8c0000

def z294 : W := mkw 0x4fbea020fbff8de5 0x09f7d4041f7ff1bc 0x7fffe0007fff9fe5 0xeffffc000ffff3fc

def z295 : W := mkw 0x8775dfdf00000000 0x10eebbfbe0000000 0x8224ffff80000002 0x10449ffff0000000

def z296 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x380007f3a39f9fe6 0x070000fe7473f3fc

def z297 : W := mkw 0x67fe9ea07ef27b00 0x0cffd3d40fde4f60 0xeff81fe07fe07f86 0xfdff03fc0ffc0ff0

def z298 : W := mkw 0x1614140a60505012 0x02c282814c0a0a02 0x0000000000000000 0x0000000000000000

def z299 : W := mkw 0xa7ffdfff7ea2fba9 0x94fffbffefd45f75 0xffffffffffe3ffff 0xfffffffffffc7fff

def z300 : W := mkw 0x87ff9f9e00000000 0x10fff3f3c0000000 0x85db1b1c00000003 0xf0bb636380000000

def z301 : W := mkw 0x07be800060500000 0x00f7d0000c0a0000 0x57ffe000607c0005 0xeafffc000c0f8000

def z302 : W := mkw 0x61eaaaa01fab2b00 0x0c3d555403f56560 0x21e3e3e01f838380 0xa43c7c7c03f07070

def z303 : W := mkw 0x8f35f5fb818d8de5 0x11e6bebf7031b1bc 0x3a27e7f3a39f9fe7 0xc744fcfe7473f3fc

def z304 : W := mkw 0x27600aa076802b00 0x04ec01540ed00560 0x67e003e07f800384 0xecfc007c0ff00070

def z305 : W := mkw 0x0614000060500000 0x00c280000c0a0000 0xde1c181c607c607f 0x5bc383038c0f8c0f

def z306 : W := mkw 0x16001400e0545456 0x02c002801c0a8a8a 0xde001c00607c7c7e 0x5bc003800c0f8f8f

def z307 : W := mkw 0x00cb0b1408220000 0x0019616281044000 0xf5db1b1c5c638007 0xfebb63638b8c7000

def z308 : W := mkw 0x0014000a00000000 0x0002800140000000 0x001c001f80000001 0x00038003f0000000

def z309 : W := mkw 0x461420007b7b0000 0x08c284000f6f6000 0x761c00007fff8005 0x4ec380000ffff000

def z310 : W := mkw 0x0614140a80040444 0x00c2828150008088 0x9e1c1c1fa01c1c67 0x53c38383f403838c

def z311 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xfff81ffc7fe07fff 0xffff03ff8ffc0fff

def z312 : W := mkw 0x200000207ea2fba9 0x840000040fd45f75 0x780000007fe3fffc 0x0f0000000ffc7fff

def z313 : W := mkw 0x08cb6b75818d8de5 0x01196d6eb031b1bc 0xbfffffffa39f9fe7 0xf7fffffff473f3fc

def z314 : W := mkw 0x0000200001090000 0x0000040000212000 0x2023e00003838000 0x84047c0000707000

def z315 : W := mkw 0x1e14342ae1ddddf7 0x03c286855c3bbbbe 0xfe1c1c1fe3ffffff 0x5fc38383fc7fffff

def z316 : W := mkw 0x57bea000fb7f5456 0x0af7d4001f6fea8a 0x7fffe0007ffffc7d 0xeffffc000fffff8f

def z317 : W := mkw 0x0001417100800900 0x0000282e20100120 0x2a27e7f3a3801f87 0xc544fcfe747003f0

def z318 : W := mkw 0x0000000080040444 0x0000000010008088 0x0800041380001c62 0x010000827000038c

def z319 : W := mkw 0x3614142af6d47f56 0x06c282855eda8fea 0xfe1c1c1ffffc7fff 0x5fc38383ffff8fff

def z320 : W := mkw 0x87fedecf00000000 0x10ffdbd9e0000000 0x87fcfcef80000000 0x30ff9f9df0000000

def z321 : W := mkw 0x20401ea004807b00 0x040803d400900f60 0xedc01fe05c007f86 0xfdb803fc0b800ff0

def z322 : W := mkw 0x00cb0b14000080a1 0x0019616280001014 0xbddb1b1c000383e7 0xf7bb63638000707c

def z323 : W := mkw 0x4734a0007b7b0000 0x08e694000f6f6000 0x7224e0007fff8004 0x0e449c000ffff000

def z324 : W := mkw 0x00012110010980a1 0x0000242200213014 0x3a27e310239f83e7 0xc744fc620473f07c

def z325 : W := mkw 0x1801757b818dddf7 0x03002eaf7031bbbe 0xba27ffffa39fffff 0xd744fffff473ffff

def z326 : W := mkw 0x2000002004807b00 0x0400000400900f60 0x0800000000007f80 0x0100000000000ff0

def z327 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x863cfcff80000003 0x50c79f9ff0000000

def z328 : W := mkw 0x97ffdfdfec76f6ff 0x92fffbfbfd8ededf 0xfffffffffc7fffff 0xffffffffff8fffff

def z329 : W := mkw 0x06140000e0540444 0x00c280001c0a8088 0x5e1c0413e07c1c67 0x4bc380827c0f838c

def z330 : W := mkw 0x07bfc15100000000 0x00f7f82a20000000 0x07ffe7f380000003 0xe0fffcfe70000000

def z331 : W := mkw 0x00410b140400a2a9 0x8008216280801455 0x0000030000000380 0x0000006000000070

def z332 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0x8a201fe023807f82 0x114403fc04700ff0

def z333 : W := mkw 0x1000000060505012 0x020000000c0a0a02 0x4000000040606018 0x08000000080c0c03

def z334 : W := mkw 0x0000000072000000 0x000000000e400000 0x600000007f800004 0x0c0000000ff00000

def z335 : W := mkw 0xa1ebcbf516802b00 0x143d797ea2d00560 0x21e3e3e01f800380 0xa43c7c7c03f00070

def z336 : W := mkw 0x27ea1ea07ea27b00 0x04fd43d40fd44f60 0xfffb1fe07fe3ff87 0xffff63fc0ffc7ff0

def z337 : W := mkw 0x008a000000000000 0x0011400000000000 0x05db000000000001 0xe0bb600000000000

def z338 : W := mkw 0x47bea0007f7ba2a9 0x88f7d4000fef7455 0x7fffe0007fffe3fd 0xeffffc000ffffc7f

def z339 : W := mkw 0x2000002016802b00 0x0400000402d00560 0x200000001f800380 0x0400000003f00070

def z340 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xe5e01be05f806380 0xbcbc037c0bf00c70

def z341 : W := mkw 0x0614140a60500000 0x00c282814c0a0000 0xd61c1c1fe07c0007 0x5ac38383fc0f8000

def z342 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x85fbfbec00000000 0xb0bf7f7d80000000

def z343 : W := mkw 0x0000200001090000 0x0000040000212000 0x30000000239f8004 0x060000000473f000

def z344 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x3a27e000239f9fe5 0xc744fc000473f3fc

def z345 : W := mkw 0x08cb6b758dafafed 0x81196d6eb1b5f5fd 0x3be7e7f3bf9f9fe7 0xe77cfcfe77f3f3fc

def z346 : W := mkw 0x67ffbfb47ffbfba9 0x8cfff7f68fff7f75 0xfffffffc7fffffff 0xffffffff8fffffff

def z347 : W := mkw 0x4000200073590000 0x080004000e6b2000 0x00000000239c0000 0x0000000004738000

def z348 : W := mkw 0x0614000000000000 0x00c2800000000000 0x061c000000000001 0x40c3800000000000

def z349 : W := mkw 0x07be940a00000000 0x00f7d28140000000 0x87fffc1f80000003 0xf0ffff83f0000000

def z350 : W := mkw 0x00ca0a0400000000 0x0019414080000000 0x85d8180c00000000 0x30bb030180000000

def z351 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x75d800007fff8004 0x2ebb00000ffff000

def z352 : W := mkw 0x8774decb00000000 0x10ee9bd960000000 0x87e4ffe380000002 0xf0fc9ffc70000000

def z353 : W := mkw 0x0000200001090000 0x0000040000212000 0x0224e000239c0000 0x00449c0004738000

def z354 : W := mkw 0x2000002076807b00 0x040000040ed00f60 0x6a2007e07f807f86 0xcd4400fc0ff00ff0

def z355 : W := mkw 0x00010110800484e5 0x000020221000909c 0x3a070713a01f9fe7 0xc740e0e27403f3fc

def z356 : W := mkw 0x10000000ec76f6ff 0x820000001d8ededf 0x780000007c7ffffc 0x0f0000000f8fffff

def z357 : W := mkw 0x47be80007a720000 0x08f7d0000f4e4000 0x57dc00007c7c0005 0x6afb80000f8f8000

def z358 : W := mkw 0x21eb0bb41ea2aba9 0x843d617683d45575 0xfdfb1bfc5fe3e3ff 0xffbf637f8bfc7c7f

def z359 : W := mkw 0x4120a00013090000 0x0824140002612000 0x0020e00003800000 0x00041c0000700000

def z360 : W := mkw 0x97ffdfdf60505012 0x12fffbfbec0a0a02 0xc7ffffffc060601b 0xf8fffffff80c0c03

def z361 : W := mkw 0x08016151810d84e5 0x01002c2a3021b09c 0x3227e013a39f8065 0xc644fc027473f00c

def z362 : W := mkw 0x48016171fbff8de5 0x09002c2e3f7ff1bc 0x7a27e7f3ffff9fe7 0xcf44fcfe7ffff3fc

def z363 : W := mkw 0x109f011e887684ff 0x8213e023d10ed09f 0x101f001f807f8079 0x0203e003f00ff00f

def z364 : W := mkw 0x0720148000000000 0x00e4029000000000 0x022004e000000000 0x0044009c00000000

def z365 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3823e3e0239f9fe4 0x87047c7c0473f3fc

def z366 : W := mkw 0xc7bfe15f7b7b0000 0x18f7fc2bef6f6000 0x77ffe01fffff8005 0xeefffc03fffff000

def z367 : W := mkw 0x00cb0b340ca2aba9 0x8019616681945575 0xfffb1ffc7fe3ffff 0xffff63ff8ffc7fff

def z368 : W := mkw 0x47ff8b147e72a2a9 0x88fff1628fce5455 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z369 : W := mkw 0x0000140000005000 0x0000028000000a00 0x88001c0000007c02 0x1100038000000f80

def z370 : W := mkw 0xc1ebebd51b2b0000 0x183d7d7aa3656000 0x21e3e3e01f838000 0xa43c7c7c03f07000

def z371 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0x39c303101c0383e7 0xe73860620380707c

def z372 : W := mkw 0xaffffffff78dffe5 0x15fffffffef1bffc 0xffffffffff9fffe7 0xfffffffffff3fffc

def z373 : W := mkw 0x48002020fbff8de5 0x090004041f7ff1bc 0x780000007fff9fe4 0x0f0000000ffff3fc

def z374 : W := mkw 0x0000000000000000 0x0000000000000000 0x0204041380000003 0x4040808270000000

def z375 : W := mkw 0x1614140a60505012 0x02c282814c0a0a02 0xc61c1c1fc060601b 0x58c38383f80c0c03

def z376 : W := mkw 0x1815617b81dd8df7 0x0302ac2f703bb1be 0x3a3fe7ffa3ff9fff 0xc747fcfff47ff3ff

def z377 : W := mkw 0x26401ea064807b00 0x04c803d40c900f60 0xce001fe060007f86 0x59c003fc0c000ff0

def z378 : W := mkw 0x40002000097b0000 0x08000400012f6000 0x10000000007f8000 0x02000000000ff000

def z379 : W := mkw 0x0615555b00000000 0x00c2aaab60000000 0x863fffff80000003 0xd0c7fffff0000000

def z380 : W := mkw 0x87fe9e8e00000000 0x10ffd3d1c0000000 0x87fff80c00000001 0xf0ffff0180000000

def z381 : W := mkw 0x57be940afa765456 0x0af7d2815f4eca8a 0xdfdc1c1ffc7c7c7f 0x7bfb8383ff8f8f8f

def z382 : W := mkw 0x81ffcbdf00000000 0x103ff97be0000000 0x01ffe3ff80000001 0xa03ffc7ff0000000

def z383 : W := mkw 0x29616bf1978dafe5 0x052c2d7e32f1b5fc 0x3be7e7f3bf9f9fe7 0xe77cfcfe77f3f3fc

def z384 : W := mkw 0xa734d4eb72805900 0x14e69a9d6e500b20 0x0224e4e3a3801c00 0x00449c9c74700380

def z385 : W := mkw 0x0000000080040444 0x0000000010008088 0x02040403a01c1c00 0x0040808074038380

def z386 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x5a040403e07c7c7c 0x0b4080807c0f8f8f

def z387 : W := mkw 0x0000002080840d44 0x00000004101081a8 0x3a2407f3a39c1fe7 0xc74480fe747383fc

def z388 : W := mkw 0x472020007b7b0000 0x08e404000f6f6000 0x77e000007fff8004 0xeefc00000ffff000

def z389 : W := mkw 0x28002020f78dffe5 0x050004041ef1bffc 0x780000007f9fffe4 0x0f0000000ff3fffc

def z390 : W := mkw 0x81ebcbd500000000 0x103d797aa0000000 0x03e7e7f380000003 0xe07cfcfe70000000

def z391 : W := mkw 0x0720140072005000 0x00e402800e400a00 0xefe01c007f807c06 0xfdfc03800ff00f80

def z392 : W := mkw 0x08016151810d84e5 0x01002c2a3021b09c 0x3807e313801f83e7 0xc700fc627003f07c

def z393 : W := mkw 0x0801417180848de5 0x0100282e301091bc 0x1a0407f3a01c1fe7 0x434080fe740383fc

def z394 : W := mkw 0x000000000c22a2a9 0x8000000001845455 0xfc18181c5c63e3ff 0x5f8303038b8c7c7f

def z395 : W := mkw 0x0734800000000000 0x00e6900000000000 0x0224e00000000000 0x00449c0000000000

def z396 : W := mkw 0x77febeaaffff7f56 0x0effd7d55fffefea 0xffffffffffffffff 0xffffffffffffffff

def z397 : W := mkw 0x07fe9e8000000000 0x00ffd3d000000000 0x87ffffe000000003 0xf0fffffc00000000

def z398 : W := mkw 0x00cb0b1400000000 0x0019616280000000 0x01c3030000000000 0xa038606000000000

def z399 : W := mkw 0x80cb5fdf00000000 0x10196bfbe0000000 0x85db1fff80000003 0xf0bb63fff0000000

def z400 : W := mkw 0x97ffdfdf80540456 0x12fffbfbf00a808a 0x97ffffff807c007b 0xf2fffffff00f800f

def z401 : W := mkw 0x0614000060500000 0x00c280000c0a0000 0x02040000201c0000 0x0040800004038000

def z402 : W := mkw 0x809fc15f082280a9 0x9013f82be1045015 0x101fe01f80638079 0x0203fc03f00c700f

def z403 : W := mkw 0x37741eaa76d07b12 0x06ee83d54eda0f62 0xeff81fec7fe07f9e 0xfdff03fd8ffc0ff3

def z404 : W := mkw 0xc09fe15f097b0000 0x1813fc2be12f6000 0x101fe01f807f8001 0x0203fc03f00ff000

def z405 : W := mkw 0x16541e0ae4547656 0x02ca83c15c8a8eca 0xffdc1f1ffc7c7fff 0xfffb83e3ff8f8fff

def z406 : W := mkw 0xa7ffdfff72805900 0x14fffbffee500b20 0x87ffffffa3801c03 0xf0fffffff4700380

def z407 : W := mkw 0x07bea00001090000 0x00f7d40000212000 0x37ffe000239f8005 0xe6fffc000473f000

def z408 : W := mkw 0x08002020818d0d44 0x010004041031a1a8 0x00000000239c1c00 0x0000000004738380

def z409 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3027e3f3839f83e1 0x8604fc7e7073f07c

def z410 : W := mkw 0x0000000060500000 0x000000000c0a0000 0x50000000607c0004 0x0a0000000c0f8000

def z411 : W := mkw 0x1734140af2545456 0x02e682815e4a8a8a 0xfffc1c1ffffc7c7f 0xffff8383ffff8f8f

def z412 : W := mkw 0x27eb1fb476807b00 0x04fd63f68ed00f60 0xeffb1ffc7f807f87 0xfdff63ff8ff00ff0

def z413 : W := mkw 0x9734d4cbe0545456 0x12e69a997c0a8a8a 0x0224e4e3a01c1c00 0x00449c9c74038380

def z414 : W := mkw 0x87fe9e8e00000000 0x10ffd3d1c0000000 0x87f81fec00000002 0xf0ff03fd80000000

def z415 : W := mkw 0x212000a012800900 0x0424001402500120 0x002000e003800000 0x0004001c00700000

def z416 : W := mkw 0x06df1f1e00000000 0x00dbe3e3c0000000 0x87df1f1f80000003 0xf0fbe3e3f0000000

def z417 : W := mkw 0x08416b71858dafe5 0x01082d6e30b1b5fc 0xffe7fff3ff9fffe7 0xfffcfffe7ff3fffc

def z418 : W := mkw 0x2720148072005000 0x04e402900e400a00 0x0000000000000000 0x0000000000000000

def z419 : W := mkw 0x08016171018989a1 0x01002c2e20313134 0x3823e3f0038383e7 0xc7047c7e0070707c

def z420 : W := mkw 0x0600140060005000 0x00c002800c000a00 0xde181c1c60607c7f 0x5bc303838c0c0f8f

def z421 : W := mkw 0x1014000a80540456 0x02028001500a808a 0xdc1c181fc07c607f 0x5b838303f80f8c0f

def z422 : W := mkw 0x1e15557be0d4ddf7 0x03c2aaaf7c1a9bbe 0xde1c1fffe07c7fff 0x5bc383fffc0f8fff

def z423 : W := mkw 0x0720000000000000 0x00e4000000000000 0x07e0000000000000 0xe0fc000000000000

def z424 : W := mkw 0x0000000080040444 0x0000000010008088 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z425 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x2823e7f383839fe2 0x85047cfe707073fc

def z426 : W := mkw 0x00000000000080a1 0x0000000000001014 0x38000000000383e4 0x070000000000707c

def z427 : W := mkw 0x27ea1e847e227208 0x84fd43d08fc44e41 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z428 : W := mkw 0x9fffffffe1ddddf7 0x13fffffffc3bbbbe 0xffffffffe3ffffff 0xfffffffffc7fffff

def z429 : W := mkw 0x1614142ae0d45d56 0x02c282855c1a8baa 0xfe3c1fffe3fc7fff 0xdfc783fffc7f8fff

def z430 : W := mkw 0x88415fff80848de5 0x11082bfff01091bc 0x88001fff80001fe2 0x110003fff00003fc

def z431 : W := mkw 0x49abe1719baf8de5 0x09357c2e3375f1bc 0x3be7e7f3bf9f9fe7 0xe77cfcfe77f3f3fc

def z432 : W := mkw 0x008a00000c22a2a9 0x8011400001845455 0x7ddb00005c63e3fd 0xefbb60000b8c7c7f

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0xc418180c40606018 0x18830301880c0c03

def z434 : W := mkw 0x20401e8004007200 0x040803d000800e40 0x8000180000006000 0x1000030000000c00

def z435 : W := mkw 0x0600000060000000 0x00c000000c000000 0x4600000060000004 0x48c000000c000000

def z436 : W := mkw 0x37ff1fbefef6ffff 0x86ffe3f7dfdedfff 0xffff1fffffffffff 0xffffe3ffffffffff

def z437 : W := mkw 0x41aa80001a220000 0x0835500003444000 0x01c000001c000000 0x2038000003800000

def z438 : W := mkw 0x4fbfe151fb7f84e5 0x09f7fc2a3f6ff09c 0x77ffe013ffff8065 0xeefffc027ffff00c

def z439 : W := mkw 0x08006041810d0444 0x01000c083021a088 0x0004e003801c0000 0x00009c0070038000

def z440 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x03e7e7e380000000 0xa07cfcfc70000000

def z441 : W := mkw 0x27601ea072805900 0x04ec03d40e500b20 0x87e01fe023801c02 0xf0fc03fc04700380

def z442 : W := mkw 0x0001415180040444 0x0000282a30008088 0x1a27e7f3a01c1c67 0xc344fcfe7403838c

def z443 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x3a2007e0239f9fe6 0xc74400fc0473f3fc

def z444 : W := mkw 0x97ffdfdfe0545456 0x12fffbfbfc0a8a8a 0x87ffffffa01c1c03 0xf0fffffff4038380

def z445 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0x23e007e03f801f80 0xa47c00fc07f003f0

def z446 : W := mkw 0x07615fd100000000 0x00ec2bfa20000000 0x87e7fff380000003 0xf0fcfffe70000000

def z447 : W := mkw 0x27615ff176807b00 0x04ec2bfe2ed00f60 0xefe7fff3ff807f87 0xfdfcfffe7ff00ff0

def z448 : W := mkw 0x0000140a00000000 0x0000028140000000 0x80001c1f80000002 0x10000383f0000000

def z449 : W := mkw 0x000101100c22a2a9 0x8000202201845455 0x780303105c63e3ff 0xcf0060620b8c7c7f

def z450 : W := mkw 0x81ebcbd50c22a2a9 0x903d797aa1845455 0xfdfbfbfc5c63e3ff 0xffbf7f7f8b8c7c7f

def z451 : W := mkw 0x1000000080540456 0x02000000100a808a 0x10000000007c0078 0x02000000000f800f

def z452 : W := mkw 0x10cb0b14ec76f6ff 0x821961629d8ededf 0xfddb1b1c7c7fffff 0xffbb63638f8fffff

def z453 : W := mkw 0x8001415f00000000 0x1000282be0000000 0x0000001f80000000 0x00000003f0000000

def z454 : W := mkw 0x47bfa1147b7b80a9 0x88f7f4228f6f7015 0x77ffe01c7fff807d 0xeefffc038ffff00f

def z455 : W := mkw 0x01aa800000000000 0x0035500000000000 0x01e3e00000000000 0xa03c7c0000000000

def z456 : W := mkw 0x28016171f78dffe5 0x05002c2e3ef1bffc 0x7a27e7f3ff9fffe7 0xcf44fcfe7ff3fffc

def z457 : W := mkw 0x00410b140c22a2a9 0x8008216281845455 0xf8001b1c5c63e3fe 0x1f0003638b8c7c7f

def z458 : W := mkw 0x008a000008220000 0x0011400001044000 0xfddb181c5c63e07f 0xffbb63038b8c7c0f

def z459 : W := mkw 0xc7ffebd57b7b0000 0x18fffd7aaf6f6000 0x77ffe3e07fff8005 0xeefffc7c0ffff000

def z460 : W := mkw 0x0800606101890900 0x01000c0c20312120 0x0020e0e003800000 0x00041c1c00700000

def z461 : W := mkw 0xa7ebdff576807b00 0x14fd7bfeaed00f60 0xefe3ffe07f807f86 0xfdfc7ffc0ff00ff0

def z462 : W := mkw 0x6734b4a073d95900 0x0ce696940e7b2b20 0x0224e4e0239c1c00 0x00449c9c04738380

def z463 : W := mkw 0x400020007f7ba2a9 0x880004000fef7455 0x780000007fffe3fc 0x0f0000000ffffc7f

def z464 : W := mkw 0x000000000c22a2a9 0x8000000001845455 0x780000005c63e3fc 0x0f0000000b8c7c7f

def z465 : W := mkw 0x000000000c222208 0x8000000001844441 0x400000005c606018 0x080000000b8c0c03

def z466 : W := mkw 0x1615151ae054d4f7 0x02c2a2a35c0a9a9e 0xfe1f1f1fe07fffff 0xdfc3e3e3fc0fffff

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x8418181c00000003 0x5083030380000000

def z468 : W := mkw 0x49abe1711bab89a1 0x09357c2e23757134 0x21e3e3e01f838380 0xa43c7c7c03f07070

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x022007e000000002 0xc04400fc00000000

def z470 : W := mkw 0x87ff9f9e0c22a2a9 0x90fff3f3c1845455 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z471 : W := mkw 0xa7fe9eae76807b00 0x14ffd3d5ced00f60 0xeff81fec7f807f86 0xfdff03fd8ff00ff0

def z472 : W := mkw 0x87ffdfdf80040444 0x10fffbfbf0008088 0x9fffffffa01c1c67 0xf3fffffff403838c

def z473 : W := mkw 0x28415ff18484ffe5 0x05082bfe30909ffc 0x88001ff380007fe2 0x110003fe70000ffc

def z474 : W := mkw 0x08006061818d0d44 0x01000c0c3031a1a8 0x1a24e4f3a39c1c67 0x43449c9e7473838c

def z475 : W := mkw 0x57beb40afb7f5456 0x0af7d6815f6fea8a 0x77ffe403ffff9c05 0xeefffc807ffff380

def z476 : W := mkw 0x000000000400a2a9 0x8000000000801455 0x08000000000063f8 0x0100000000000c7f

def z477 : W := mkw 0x37601ea0f6d47f56 0x06ec03d41eda8fea 0xffe01fe07ffc7ffe 0xfffc03fc0fff8fff

def z478 : W := mkw 0x17741e8ae0545456 0x02ee83d15c0a8a8a 0xdffc1fffe07c7c7f 0xfbff83fffc0f8f8f

def z479 : W := mkw 0x21eb0bb41ea2aba9 0x843d617683d45575 0x21e303e01f838380 0xa43c607c03f07070

def z480 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0x79c303005c63e3fc 0xaf3860600b8c7c7f

def z481 : W := mkw 0x600020207ffb7b00 0x0c0004040fff6f60 0x780000007fffff84 0x0f0000000ffffff0

def z482 : W := mkw 0x47feaa047f7b2208 0x88ffd5408fef6441 0xf7fff80c7fffe01d 0xfeffff018ffffc03

def z483 : W := mkw 0x00cb2b140d2ba2a9 0x8019656281a57455 0xfffffb1c7fffe3ff 0xffffff638ffffc7f

def z484 : W := mkw 0xa7ffdfff04807b00 0x14fffbffe0900f60 0x8fffffff80007f83 0xf1fffffff0000ff0

def z485 : W := mkw 0x0fbfe171818d8de5 0x01f7fc2e3031b1bc 0x3fffe7f3a39f9fe7 0xe7fffcfe7473f3fc

def z486 : W := mkw 0x2f617ff17789fba1 0x05ec2ffe2ef13f74 0xefe3ffe07f83ff86 0xfdfc7ffc0ff07ff0

def z487 : W := mkw 0x08016151010980a1 0x01002c2a20213014 0x0003e00000038000 0x00007c0000007000

def z488 : W := mkw 0x2feb7ff5ffafffed 0x85fd6ffebff5fffd 0xffffffffffffffff 0xffffffffffffffff

def z489 : W := mkw 0x08012130818d8de5 0x010024261031b1bc 0x38030310239f9fe7 0xc70060620473f3fc

def z490 : W := mkw 0x07eb0b147e22a2a9 0x80fd61628fc45455 0xfffb1b1c7fe3e3ff 0xffff63638ffc7c7f

def z491 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x121c041fa07c1c79 0x02438083f40f838f

def z492 : W := mkw 0x47feaa007f7b2200 0x08ffd5400fef6440 0xfffffb007fffe387 0xffffff600ffffc70

def z493 : W := mkw 0x07601e8004002200 0x00ec03d000800440 0xefe01fe05c006386 0xfdfc03fc0b800c70

def z494 : W := mkw 0x08016171818d0d44 0x01002c2e3031a1a8 0x0227e7f3a39c1c03 0xc044fcfe74738380

def z495 : W := mkw 0x1614140a60505012 0x02c282814c0a0a02 0xd61c180c607c601d 0x5ac383018c0f8c03

def z496 : W := mkw 0x8f34f4eb818d0d44 0x11e69e9d7031a1a8 0x0224e4e3a39c1c00 0x00449c9c74738380

def z497 : W := mkw 0x87ffdfdf60005000 0x10fffbfbec000a00 0xcfffffffe0007c07 0xf9fffffffc000f80

def z498 : W := mkw 0x90415fdf80045456 0x12082bfbf0008a8a 0x88001fff80007c7a 0x110003fff0000f8f

def z499 : W := mkw 0x08416b75858dafed 0x81082d6eb0b1b5fd 0xba27ffffa39fffff 0xd744fffff473ffff

def z500 : W := mkw 0x1000140a80045456 0x0200028150008a8a 0xdc181c1fc0607c7f 0x5b830383f80c0f8f

def z501 : W := mkw 0x16df1f1e6c72f2bb 0x82dbe3e3cd8e5e57 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z502 : W := mkw 0x47be80007a720000 0x08f7d0000f4e4000 0x47ffe0005c600001 0xe8fffc000b8c0000

def z503 : W := mkw 0x1000140ae0545456 0x020002815c0a8a8a 0xd8001c1fe07c7c7e 0x1b000383fc0f8f8f

def z504 : W := mkw 0x0600140060005000 0x00c002800c000a00 0x0200040020001c00 0x0040008004000380

def z505 : W := mkw 0x509ea00a897f0456 0x0a13d401512fe08a 0x101fe01f807f8079 0x0203fc03f00ff00f

def z506 : W := mkw 0x1000140a80045456 0x0200028150008a8a 0x9a041c1fa01c7c7f 0x53408383f4038f8f

def z507 : W := mkw 0x0f216171f38d8de5 0x01e42c2e3e71b1bc 0x7fe7e7f3ff9f9fe7 0xeffcfcfe7ff3f3fc

def z508 : W := mkw 0x0801417180848de5 0x0100282e301091bc 0x0a27e7f380001fe3 0xc144fcfe700003fc

def z509 : W := mkw 0x409fa114097b80a9 0x8813f422812f7015 0x101fe01c007f8079 0x0203fc03800ff00f

def z510 : W := mkw 0x00002000810d0444 0x000004001021a088 0x3a27e413a39f9c67 0xc744fc827473f38c

def z511 : W := mkw 0x27601ea0f6847f44 0x04ec03d41ed08fe8 0xffe41ff3ff9c7fe7 0xfffc83fe7ff38ffc

def z512 : W := mkw 0x87ffffdf01090000 0x10fffffbe0212000 0xb7ffffffa39f8007 0xf6fffffff473f000

def z513 : W := mkw 0x008b0114082280a9 0x8011602281045015 0x75db001c5c63807d 0xeebb60038b8c700f

def z514 : W := mkw 0x0000000000000000 0x0000000000000000 0x1018001c00600079 0x02030003800c000f

def z515 : W := mkw 0x87ffdfdf082280a9 0x90fffbfbe1045015 0x97ffffff8063807b 0xf2fffffff00c700f

def z516 : W := mkw 0x08006061818d0d44 0x01000c0c3031a1a8 0x3227e4e3a39f9c05 0xc644fc9c7473f380

def z517 : W := mkw 0x0000000000000000 0x0000000000000000 0x12040000201c0005 0x4240800004038000

def z518 : W := mkw 0x5734b40af35d5456 0x0ae696815e6baa8a 0xde3cfc1fe3fc7c7f 0x5bc79f83fc7f8f8f

def z519 : W := mkw 0x0614200061590000 0x00c284000c2b2000 0x763fe00063ff8005 0xcec7fc000c7ff000

def z520 : W := mkw 0x2600142076807b00 0x04c002840ed00f60 0xee001c007f807f86 0x5dc003800ff00ff0

def z521 : W := mkw 0x8fffffff818d0d44 0x11fffffff031a1a8 0x87ffffffa39c1c03 0xf0fffffff4738380

def z522 : W := mkw 0x89ebebf5018989a1 0x113d7d7ea0313134 0x21e3e3e003838380 0xa43c7c7c00707070

def z523 : W := mkw 0x86555fdf00000000 0x10caabfbe0000000 0x861c1fff80000003 0x50c383fff0000000

def z524 : W := mkw 0x27601ea004807b00 0x04ec03d400900f60 0x8fe01fe000007f82 0xf1fc03fc00000ff0

def z525 : W := mkw 0x00410b1400000000 0x0008216280000000 0x80001b1c00000002 0x1000036380000000

def z526 : W := mkw 0x08006061818d0d44 0x01000c0c3031a1a8 0x2a24e7e3a39c1f86 0xc5449cfc747383f0

def z527 : W := mkw 0x0000000000000000 0x0000000000000000 0x5418000040600005 0x4a830000080c0000

def z528 : W := mkw 0x27601ea016802b00 0x04ec03d402d00560 0xa7e01fe01f800382 0xf4fc03fc03f00070

def z529 : W := mkw 0x8fffffdf810d84e5 0x11fffffbf021b09c 0x97ffffff801f8063 0xf2fffffff003f00c

def z530 : W := mkw 0x27eb1f947e22f2a9 0x84fd63f28fc45e55 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z531 : W := mkw 0x00cb0b140400a2a9 0x8019616280801455 0x8ddb1b1c000063fb 0xf1bb636380000c7f

def z532 : W := mkw 0x1614140a60505012 0x02c282814c0a0a02 0xdc18181c4060607f 0x5b830303880c0c0f

def z533 : W := mkw 0x400020001b2b0000 0x0800040003656000 0x200000001f838000 0x0400000003f07000

def z534 : W := mkw 0x009e800000000000 0x0013d00000000000 0x001fe00000000001 0x0003fc0000000000

def z535 : W := mkw 0x47febe807b7b0000 0x08ffd7d00f6f6000 0xf7ffffe07fff8007 0xfefffffc0ffff000

def z536 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z537 : W := mkw 0x0e156171e1dd8de5 0x01c2ac2e3c3bb1bc 0x7e3fe7f3e3ff9fe7 0xcfc7fcfe7c7ff3fc

def z538 : W := mkw 0xe7ffffff7ffb7b00 0x1cffffffefff6f60 0xffffffffffffff87 0xfffffffffffffff0

def z539 : W := mkw 0x489fe17189ff8de5 0x0913fc2e313ff1bc 0x3a3fe7f3a3ff9fe7 0xc747fcfe747ff3fc

def z540 : W := mkw 0x008a000008220000 0x0011400001044000 0x45d800005c600000 0x28bb00000b8c0000

def z541 : W := mkw 0x1614140a80540456 0x02c28281500a808a 0x961c1c1f807c007b 0x52c38383f00f800f

def z542 : W := mkw 0x8734948a00000000 0x10e6929140000000 0x0000000000000000 0x0000000000000000

def z543 : W := mkw 0x4fbee061fbff0d44 0x09f7dc0c3f7fe1a8 0x77ffe4e3ffff9c05 0xeefffc9c7ffff380

def z544 : W := mkw 0x06401e0064007200 0x00c803c00c800e40 0xefc01f007c007f86 0xfdf803e00f800ff0

def z545 : W := mkw 0x10000000e0545456 0x020000001c0a8a8a 0xdc18181c607c7c7f 0x5b8303038c0f8f8f

def z546 : W := mkw 0x21600a8016002200 0x042c015002c00440 0x01c000001c000000 0x2038000003800000

def z547 : W := mkw 0x47bea00073590000 0x08f7d4000e6b2000 0x07ffe000239c0001 0xe0fffc0004738000

def z548 : W := mkw 0x889fe17f818d8de5 0x1113fc2ff031b1bc 0x3a3fe7ffa39f9fe7 0xc747fcfff473f3fc

def z549 : W := mkw 0x00010110000080a1 0x0000202200001014 0xfc1b1b1c4063e3ff 0xdf836363880c7c7f

def z550 : W := mkw 0xc7fe9e8e7a720000 0x18ffd3d1cf4e4000 0xc5d8180c5c600000 0x38bb03018b8c0000

def z551 : W := mkw 0x36541eaae4d47f56 0x06ca83d55c9a8fea 0xde1c1fffe07c7fff 0x5bc383fffc0f8fff

def z552 : W := mkw 0x008a000008220000 0x0011400001044000 0x101b000000638001 0x02036000000c7000

def z553 : W := mkw 0x81ebcbd50c22a2a9 0x903d797aa1845455 0x21e3e3e01c038380 0xa43c7c7c03807070

def z554 : W := mkw 0x569eb40ae97f5456 0x0ad3d6815d2fea8a 0xde1ffc1fe07ffc7f 0x5bc3ff83fc0fff8f

def z555 : W := mkw 0x008b0114082280a9 0x8011602281045015 0xdc1b181c4063e07f 0x5b836303880c7c0f

def z556 : W := mkw 0x1e15757be1ddddf7 0x03c2aeaf7c3bbbbe 0x3a27e7f3a39f9fe7 0xc744fcfe7473f3fc

def z557 : W := mkw 0x07aa00007a220000 0x00f540000f444000 0x77fb00007fe38005 0xeeff60000ffc7000

def z558 : W := mkw 0x47fe8a047e722208 0x88ffd1408fce4441 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z559 : W := mkw 0x08016171018989a1 0x01002c2e20313134 0x3227e3e0239f8385 0xc644fc7c0473f070

def z560 : W := mkw 0x00410b140400a2a9 0x8008216280801455 0xdc181b1c406063ff 0x5b830363880c0c7f

def z561 : W := mkw 0x87fe9e8e0c222208 0x90ffd3d1c1844441 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z562 : W := mkw 0x27601e8076007200 0x04ec03d00ec00e40 0xcfc01c007c007c06 0x79f803800f800f80

def z563 : W := mkw 0x169e140ae8765456 0x02d3c2815d0eca8a 0xffdf1c1ffc7ffc7f 0xfffbe383ff8fff8f

def z564 : W := mkw 0x57be940a7a725012 0x0af7d2814f4e4a02 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z565 : W := mkw 0x20401ea076807b00 0x040803d40ed00f60 0xe8001fe07f807f86 0x1d0003fc0ff00ff0

def z566 : W := mkw 0x47bea000097b0000 0x08f7d400012f6000 0x17ffe000007f8001 0xe2fffc00000ff000

def z567 : W := mkw 0x80dfcb5f00000000 0x101bf96be0000000 0x85dffb1f80000003 0xf0bbff63f0000000

def z568 : W := mkw 0x87ffdfdf0400a2a9 0x90fffbfbe0801455 0x8fffffff800063fb 0xf1fffffff0000c7f

def z569 : W := mkw 0x47bea0207bfb0900 0x08f7d4040f7f6120 0x7fffe7e07fff9f87 0xeffffcfc0ffff3f0

def z570 : W := mkw 0xa7fe9e8e76007200 0x14ffd3d1cec00e40 0xc5d8180c5c006000 0x38bb03018b800c00

def z571 : W := mkw 0x96555fdfe0545456 0x12caabfbfc0a8a8a 0xde1c1fffe07c7c7f 0x5bc383fffc0f8f8f

def z572 : W := mkw 0x00010110000080a1 0x0000202200001014 0x1003001000038061 0x020060020000700c

def z573 : W := mkw 0xa7ffdfff16802b00 0x14fffbffe2d00560 0xa7ffffff9f800383 0xf4fffffff3f00070

def z574 : W := mkw 0x08016171018989a1 0x01002c2e20313134 0x2a23e7e023839f86 0xc5447cfc047073f0

def z575 : W := mkw 0x06df1f1e0c22a2a9 0x80dbe3e3c1845455 0xffdf1f1fdc63e3ff 0xfffbe3e3fb8c7c7f

def z576 : W := mkw 0x0014000000500000 0x00028000000a0000 0x101c0000007c0001 0x02038000000f8000

def z577 : W := mkw 0x272014a072805900 0x04e402940e500b20 0xce201ce063807c06 0x59c4039c0c700f80

def z578 : W := mkw 0x08014151800484e5 0x0100282a3000909c 0x0000001380000060 0x000000027000000c

def z579 : W := mkw 0x000000000c22a2a9 0x8000000001845455 0x200000001c038380 0x0400000003807070

def z580 : W := mkw 0x00000000082280a9 0x8000000001045015 0x1000000000638078 0x02000000000c700f

def z581 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xd5db181c5c63e079 0x3abb63038b8c7c0f

def z582 : W := mkw 0x08cb6b558d2fa6ed 0x81196d6ab1a5f4dd 0xfddffb1fdc7fe3ff 0xffbbff63fb8ffc7f

def z583 : W := mkw 0x27eb1fb47ea2fba9 0x84fd63f68fd45f75 0xefe31fe07f83ff86 0xfdfc63fc0ff07ff0

def z584 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x861c1c1fa01c1c03 0x50c38383f4038380

def z585 : W := mkw 0x0600140060005000 0x00c002800c000a00 0xc400180040006000 0x1880030008000c00

def z586 : W := mkw 0x1000140a00005012 0x0200028140000a02 0x8000180c00006018 0x1000030180000c03

def z587 : W := mkw 0x40cb2b147f7ba2a9 0x881965628fef7455 0xfddb1b1c7fffe3ff 0xffbb63638ffffc7f

def z588 : W := mkw 0x2720002076807b00 0x04e400040ed00f60 0x6fe000007f807f84 0xedfc00000ff00ff0

def z589 : W := mkw 0x4f35e171f3dd8de5 0x09e6bc2e3e7bb1bc 0x3a27e7f3a39f9fe7 0xc744fcfe7473f3fc

def z590 : W := mkw 0x0001615101090000 0x00002c2a20212000 0x3227e7f3a39f8007 0xc644fcfe7473f000

def z591 : W := mkw 0x373414aaf2d45d56 0x06e682955e5a8baa 0x022404e3a39c1c00 0x0044809c74738380

def z592 : W := mkw 0x08cb4b758ca6afed 0x8119696eb194d5fd 0xfddb1fffdc63ffff 0xffbb63fffb8c7fff

def z593 : W := mkw 0x47bfa1107b7b80a1 0x08f7f4220f6f7014 0x7fffe3107fff83e7 0xeffffc620ffff07c

def z594 : W := mkw 0x00400a0004002200 0x0008014000800440 0xfdd81b1c5c6063ff 0xffbb03638b8c0c7f

def z595 : W := mkw 0x07741e8a00000000 0x00ee83d140000000 0x87fc1fff80000003 0xf0ff83fff0000000

def z596 : W := mkw 0x16140000e0545456 0x02c280001c0a8a8a 0x5e1c0000607c7c7d 0x4bc380000c0f8f8f

def z597 : W := mkw 0x0000000000000000 0x0000000000000000 0x1800001000000067 0x430000020000000c

def z598 : W := mkw 0x1014000a80540456 0x02028001500a808a 0x00040003801c0000 0x0000800070038000

def z599 : W := mkw 0x1600140ae0045456 0x02c002815c008a8a 0xce001c1fe0007c7e 0x59c00383fc000f8f

def z600 : W := mkw 0x008b01140c22a2a9 0x8011602281845455 0x781b001c5c63e3fd 0x0f0360038b8c7c7f

def z601 : W := mkw 0x27fe9ea076807b00 0x04ffd3d40ed00f60 0xefffffe07f807f87 0xfdfffffc0ff00ff0

def z602 : W := mkw 0x06001400e0045444 0x00c002801c008a88 0xde041c13e01c7c67 0x5bc083827c038f8c

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x65c000005c000004 0xecb800000b800000

def z604 : W := mkw 0x21600aa016802b00 0x042c015402d00560 0xede01be05f806386 0xfdbc037c0bf00c70

def z605 : W := mkw 0x00ca0a040c222208 0x8019414081844441 0xddd8181c5c60607f 0x7bbb03038b8c0c0f

def z606 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xedc018007f807f84 0x3db803000ff00ff0

def z607 : W := mkw 0x40dfab140d7ba2a9 0x881bf56281af7455 0xfddffb1c5c7fe3ff 0xffbbff638b8ffc7f

def z608 : W := mkw 0x87ffdfdf000080a1 0x10fffbfbe0001014 0xbfffffff800383e7 0xf7fffffff000707c

def z609 : W := mkw 0x27601e8076007200 0x04ec03d00ec00e40 0xedc01b005c006386 0xfdb803600b800c70

def z610 : W := mkw 0x08016171018989a1 0x01002c2e20313134 0x2227e7f383838383 0xc444fcfe70707070

def z611 : W := mkw 0x67fe9e807e727200 0x0cffd3d00fce4e40 0xc5d818005c606000 0x38bb03000b8c0c00

def z612 : W := mkw 0x57ffbf1eff7ff6ff 0x8afff7e3dfeffedf 0xffffff1fffffffff 0xffffffe3ffffffff

def z613 : W := mkw 0x97fe9e8e60505012 0x12ffd3d1cc0a0a02 0xc5d8180c40606018 0x38bb0301880c0c03

def z614 : W := mkw 0x00401e8000000000 0x000803d000000000 0x80001fe000000002 0x100003fc00000000

def z615 : W := mkw 0x07be800000000000 0x00f7d00000000000 0x05d8000000000000 0x20bb000000000000

def z616 : W := mkw 0x18016171e1ddddf7 0x03002c2e3c3bbbbe 0x7a27e7f3e3ffffff 0xcf44fcfe7c7fffff

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x3003000000038005 0xc600600000007000

def z618 : W := mkw 0x28417ff1858dffe5 0x05082ffe30b1bffc 0xba27fff3a39fffe7 0xd744fffe7473fffc

def z619 : W := mkw 0x17be940ae0545456 0x02f7d2815c0a8a8a 0xdffffc1fe07c7c7f 0xfbffff83fc0f8f8f

def z620 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xce041c03e01c7c06 0x59c083807c038f80

def z621 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x65fbe0005fe38000 0xacbf7c000bfc7000

def z622 : W := mkw 0x1801557b8084ddf7 0x03002aaf70109bbe 0x88001fff80007ffa 0x110003fff0000fff

def z623 : W := mkw 0x1e14746be1dd5d56 0x03c28e8d7c3babaa 0xde3cfcffe3fc7c7f 0x5bc79f9ffc7f8f8f

def z624 : W := mkw 0x373414aaf2d45d56 0x06e682955e5a8baa 0xde3c1cffe3fc7c7f 0x5bc7839ffc7f8f8f

def z625 : W := mkw 0x2000000076007200 0x040000000ec00e40 0x400000005c006000 0x080000000b800c00

def z626 : W := mkw 0x87615fdf00000000 0x10ec2bfbe0000000 0x87e01fff80000002 0xf0fc03fff0000000

def z627 : W := mkw 0x00ca0a040c222208 0x8019414081844441 0xf5db180c5c63e01d 0xfebb63018b8c7c03

def z628 : W := mkw 0x0000000060005000 0x000000000c000a00 0x4800000060007c04 0x090000000c000f80

def z629 : W := mkw 0x20cb1fb40ca2fba9 0x841963f681945f75 0xfddb1ffc5c63ffff 0xffbb63ff8b8c7fff

def z630 : W := mkw 0x57bea00afb7f0456 0x0af7d4015f6fe08a 0x77ffe01fffff807d 0xeefffc03fffff00f

def z631 : W := mkw 0x0e15757b818d8de5 0x01c2aeaf7031b1bc 0xbe3fffffa39f9fe7 0xd7c7fffff473f3fc

def z632 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xa5db1b1c1c038383 0xf4bb636383807070

def z633 : W := mkw 0x00cb0b14082280a9 0x8019616281045015 0x95db1b1c0063807b 0xf2bb6363800c700f

def z634 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x123fe00023ff8001 0x0247fc00047ff000

def z635 : W := mkw 0x50002000fb7f5456 0x0a0004001f6fea8a 0x780000007ffffc7c 0x0f0000000fffff8f

def z636 : W := mkw 0x00ca0a000c222200 0x0019414001844440 0xfddb1b005c63e387 0xffbb63600b8c7c70

def z637 : W := mkw 0x1614140aec76f6ff 0x82c282815d8ededf 0xfe1c1c1ffc7fffff 0x5fc38383ff8fffff

def z638 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800181c0000607a 0x1100030380000c0f

def z639 : W := mkw 0x07eb1f9400000000 0x00fd63f280000000 0x87fb1ffc00000003 0xf0ff63ff80000000

def z640 : W := mkw 0x08016151810d84e5 0x01002c2a3021b09c 0x1a07e413a01f9c67 0x4340fc827403f38c

def z641 : W := mkw 0x80414bd500000000 0x1008297aa0000000 0x000003e000000000 0x0000007c00000000

def z642 : W := mkw 0x27601ea07ea2fba9 0x84ec03d40fd45f75 0xffe01fe07fe3fffe 0xfffc03fc0ffc7fff

def z643 : W := mkw 0x1815615b815d84f7 0x0302ac2b702bb09e 0x101fe01f807f8079 0x0203fc03f00ff00f

def z644 : W := mkw 0x469ea000697b0000 0x08d3d4000d2f6000 0x561fe000607f8005 0x4ac3fc000c0ff000

def z645 : W := mkw 0x5614340afb7f5456 0x0ac286815f6fea8a 0xfe1c1c1ffffffc7f 0x5fc38383ffffff8f

def z646 : W := mkw 0x2f2074e1f38d5d44 0x05e40e9c3e71aba8 0x0224e4e3a39c1c00 0x00449c9c74738380

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0xcc00180040006006 0x5980030008000c00

def z648 : W := mkw 0x8120c0c100000000 0x1024181820000000 0x0020e0e000000000 0x00041c1c00000000

def z649 : W := mkw 0x008b0110082280a1 0x0011602201045014 0x7ddb03105c6383e7 0xefbb60620b8c707c

def z650 : W := mkw 0x0734000072500000 0x00e680000e4a0000 0x77fc00007ffc0005 0xeeff80000fff8000

def z651 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x1227e4f3a39f9c61 0x0244fc9e7473f38c

def z652 : W := mkw 0x00410b100400a2a1 0x0008216200801454 0xfdc31b105c03e3e7 0xffb863620b807c7c

def z653 : W := mkw 0x008b0114082280a9 0x8011602281045015 0x381b031c006383ff 0xc7036063800c707f

def z654 : W := mkw 0x808bc15500000000 0x1011782aa0000000 0x0003e00000000000 0x00007c0000000000

def z655 : W := mkw 0x37741e8a76507212 0x06ee83d14eca0e42 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z656 : W := mkw 0x0614140060505000 0x00c282800c0a0a00 0xde1c1c00607c7c07 0x5bc383800c0f8f80

def z657 : W := mkw 0x07eb1f940c22a2a9 0x80fd63f281845455 0xfffb1ffc5c63e3ff 0xffff63ff8b8c7c7f

def z658 : W := mkw 0x088b617189af8de5 0x01116c2e3135f1bc 0x7fffe7f3ffff9fe7 0xeffffcfe7ffff3fc

def z659 : W := mkw 0x909fc15f80540456 0x1213f82bf00a808a 0x101fe01f807c0079 0x0203fc03f00f800f

def z660 : W := mkw 0x0000002000800900 0x0000000400100120 0x080007e000001f82 0x010000fc000003f0

def z661 : W := mkw 0x07be800072000000 0x00f7d0000e400000 0x67ffe0007f800005 0xecfffc000ff00000

def z662 : W := mkw 0x00400a000c22a2a9 0x8008014001845455 0xfdc01b005c63e3fe 0xffb803600b8c7c7f

def z663 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x0a24e7f3a39c1fe2 0x01449cfe747383fc

def z664 : W := mkw 0x67feaaa07ffb2b00 0x0cffd5540fff6560 0x77ffe3e07fff8385 0xeefffc7c0ffff070

def z665 : W := mkw 0x16de1e0e6c72721a 0x82dbc3c1cd8e4e43 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z666 : W := mkw 0x008b011400000000 0x0011602280000000 0x001b001c00000001 0x0003600380000000

def z667 : W := mkw 0x1e15755be15dd4f7 0x03c2aeab7c2bba9e 0xde1ffc1fe07ffc7f 0x5bc3ff83fc0fff8f

def z668 : W := mkw 0x67febe807f7b7200 0x0cffd7d00fef6e40 0xf7fff8007fffe005 0xfeffff000ffffc00

def z669 : W := mkw 0x27601e8076007200 0x04ec03d00ec00e40 0xe7e018007f806004 0xfcfc03000ff00c00

def z670 : W := mkw 0x869fd55f00000000 0x10d3faabe0000000 0x861ffc1f80000003 0x50c3ff83f0000000

def z671 : W := mkw 0x07ff8b1400000000 0x00fff16280000000 0x87fffb1c00000003 0xf0ffff6380000000

def z672 : W := mkw 0x6774bea077d97b00 0x0cee97d40efb2f60 0xefe4ffe07f9c7f86 0xfdfc9ffc0ff38ff0

def z673 : W := mkw 0x06df0b146c72a2a9 0x80dbe1628d8e5455 0xffdf1b1c7c7fe3ff 0xfffbe3638f8ffc7f

def z674 : W := mkw 0x20411fb40480fba9 0x840823f680901f75 0x88001ffc00007ffa 0x110003ff80000fff

def z675 : W := mkw 0x0600142060805900 0x00c002840c100b20 0xee201fe063807f86 0xddc403fc0c700ff0

def z676 : W := mkw 0x0000200001090000 0x0000040000212000 0x1007e000001f8001 0x0200fc000003f000

def z677 : W := mkw 0x07601e8000000000 0x00ec03d000000000 0x85c0180000000000 0x30b8030000000000

def z678 : W := mkw 0x1614340ae15d5456 0x02c286815c2baa8a 0xfe3ffc1fe3fffc7f 0xdfc7ff83fc7fff8f

def z679 : W := mkw 0x00400a0004002200 0x0008014000800440 0xc5c018005c006000 0x38b803000b800c00

def z680 : W := mkw 0x008a000408220008 0x8011400081044001 0x0018000c00600018 0x00030001800c0003

def z681 : W := mkw 0x1000140a80045456 0x0200028150008a8a 0x0000040380001c00 0x0000008070000380

def z682 : W := mkw 0x200014a000805900 0x0400029400100b20 0x000004e000001c00 0x0000009c00000380

def z683 : W := mkw 0x16551f1ee454f6ff 0x82caa3e3dc8a9edf 0xde1c1f1fe07c7fff 0x5bc383e3fc0f8fff

def z684 : W := mkw 0x87ffdfff00800900 0x10fffbffe0100120 0xafffffffa3801f87 0xf5fffffff47003f0

def z685 : W := mkw 0x87bfc15f00000000 0x10f7f82be0000000 0x07ffe01f80000001 0xe0fffc03f0000000

def z686 : W := mkw 0x4fffeb75ffffafed 0x89fffd6ebffff5fd 0xffffffffffffffff 0xffffffffffffffff

def z687 : W := mkw 0x00400a0404002208 0x8008014080800441 0x8000180c00006018 0x1000030180000c03

def z688 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0x31db031c1c6383f9 0xa63b6063838c707f

def z689 : W := mkw 0x88417fff818d8de5 0x11082ffff031b1bc 0xba27ffffa39f9fe7 0xd744fffff473f3fc

def z690 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x1807e7f3801f9fe3 0x0300fcfe7003f3fc

def z691 : W := mkw 0x5fbff57bfbffddf7 0x0bf7feaf7f7ffbbe 0xffffffffffffffff 0xffffffffffffffff

def z692 : W := mkw 0x2f615ff1f684ffe5 0x05ec2bfe3ed09ffc 0xefe01ff3ff807fe6 0xfdfc03fe7ff00ffc

def z693 : W := mkw 0x1edf7f7fedffffff 0x83dbefeffdbfffff 0xffffffffffffffff 0xffffffffffffffff

def z694 : W := mkw 0x409ea000097b0000 0x0813d400012f6000 0x75dfe0005c7f8005 0xeebbfc000b8ff000

def z695 : W := mkw 0x80cb5fdf0c22a2a9 0x90196bfbe1845455 0xfddb1fffdc63e3ff 0xffbb63fffb8c7c7f

def z696 : W := mkw 0x08006061818d8de5 0x01000c0c3031b1bc 0x3a24e4e3a39f9fe4 0x07449c9c7473f3fc

def z697 : W := mkw 0x10df0b1e8c76a6ff 0x821be163d18ed4df 0xfddf1b1fdc7fe3ff 0xffbbe363fb8ffc7f

def z698 : W := mkw 0x01600a8000000000 0x002c015000000000 0x01e003e000000000 0xa03c007c00000000

def z699 : W := mkw 0x07ff8b140c22a2a9 0x80fff16281845455 0xfffffb1c5c63e3ff 0xffffff638b8c7c7f

def z700 : W := mkw 0x0e017571e18ddde5 0x01c02eae3c31bbbc 0xfe27fff3e39fffe7 0xdfc4fffe7c73fffc

def z701 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0x75db03005c638385 0xeebb60600b8c7070

def z702 : W := mkw 0x47be80007a720000 0x08f7d0000f4e4000 0x75db00005c638005 0xeebb60000b8c7000

def z703 : W := mkw 0x37741eaaf6d47f56 0x06ee83d55eda8fea 0xefe41fe3ff9c7f86 0xfdfc83fc7ff38ff0

def z704 : W := mkw 0x1000000080045456 0x0200000010008a8a 0x0800000000007c78 0x0100000000000f8f

def z705 : W := mkw 0x8fffdfff80848de5 0x11fffbfff01091bc 0x8fffffff80001fe3 0xf1fffffff00003fc

def z706 : W := mkw 0x30000020f6d47f56 0x060000041eda8fea 0x780000007ffc7ffc 0x0f0000000fff8fff

def z707 : W := mkw 0x07615fd10400a2a1 0x00ec2bfa20801454 0xffe7fff3dc03e3e7 0xfffcfffe7b807c7c

def z708 : W := mkw 0x4fbfc171faf68de5 0x09f7f82e3f5ed1bc 0x4dd807f3dc601fe2 0x29bb00fe7b8c03fc

def z709 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x3a000400239f9fe6 0x474000800473f3fc

def z710 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xffe31fe07f83ff87 0xfffc63fc0ff07ff0

def z711 : W := mkw 0x21601ea016807b00 0x042c03d402d00f60 0x21e007e01f801f80 0xa43c00fc03f003f0

def z712 : W := mkw 0x80415fdf0400a2a9 0x90082bfbe0801455 0xba27ffff8003e3ff 0xd744fffff0007c7f

def z713 : W := mkw 0x08cb2b348dafafed 0x8119656691b5f5fd 0x39c303003f9f9fe4 0xa738606007f3f3fc

def z714 : W := mkw 0x88415fff8484afed 0x91082bfff09095fd 0x88001fff80007ffa 0x110003fff0000fff

def z715 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0227e7e380000000 0x8044fcfc70000000

def z716 : W := mkw 0x80dfdfdf00000000 0x101bfbfbe0000000 0x85dfffff80000003 0xf0bbfffff0000000

def z717 : W := mkw 0x0614544b00000000 0x00c28a8960000000 0x0224e4e380000000 0x00449c9c70000000

def z718 : W := mkw 0x072054c100000000 0x00e40a9820000000 0x0224e4e380000000 0x00449c9c70000000

def z719 : W := mkw 0xc7beb48a7b7b0000 0x18f7d6914f6f6000 0x77ffe0007fff8005 0xeefffc000ffff000

def z720 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x9a1c1c1fa07c7c7b 0x13438383f40f8f8f

def z721 : W := mkw 0x87ffdfdf76002200 0x10fffbfbeec00440 0xefffffffff806387 0xfdfffffffff00c70

def z722 : W := mkw 0x80cbdfdf00000000 0x10197bfbe0000000 0x8003ffff80000002 0x10007ffff0000000

def z723 : W := mkw 0x47bea0047b7b0008 0x88f7d4008f6f6001 0x77ffe00c7fff801d 0xeefffc018ffff003

def z724 : W := mkw 0x272014a072805900 0x04e402940e500b20 0x6fe007e07f801f86 0xedfc00fc0ff003f0

def z725 : W := mkw 0x408a20007b7b0000 0x081144000f6f6000 0x77ffe0007fff8005 0xeefffc000ffff000

def z726 : W := mkw 0x87ffdfdf04002200 0x10fffbfbe0800440 0xffffffffdc6063ff 0xfffffffffb8c0c7f

def z727 : W := mkw 0x21600aa016807b00 0x042c015402d00f60 0x29e003e01f807f80 0xa53c007c03f00ff0

def z728 : W := mkw 0x07755fdb00000000 0x00eeabfb60000000 0x87ffffff80000003 0xf0fffffff0000000

def z729 : W := mkw 0x47beb40a7b7b0000 0x08f7d6814f6f6000 0x77ffe403ffff8005 0xeefffc807ffff000

def z730 : W := mkw 0x08ca6a658daf2f4c 0x81194d4cb1b5e5e9 0xc7fcfceffffc7c18 0x38ff9f9dffff8f83

def z731 : W := mkw 0xa7ffdfdf76007200 0x14fffbfbeec00e40 0xefffffffdc006387 0xfdfffffffb800c70

def z732 : W := mkw 0x07ffcb5500000000 0x00fff96aa0000000 0x87ffffff80000003 0xf0fffffff0000000

def z733 : W := mkw 0x81ffcbdf00000000 0x103ff97be0000000 0x03ffe7ff80000003 0xe07ffcfff0000000

def z734 : W := mkw 0x16df1f1eec76f6ff 0x82dbe3e3dd8ededf 0x23c70703bc1f9f80 0xa478e0e07783f3f0

def z735 : W := mkw 0x51aab40a9b2f5456 0x0a3556815365ea8a 0xa9e3fc1f9f83fc7a 0xb53c7f83f3f07f8f

def z736 : W := mkw 0x00014151000080a1 0x0000282a20001014 0x1227e7f380038063 0xc244fcfe7000700c

def z737 : W := mkw 0x87bed4cb00000000 0x10f7da9960000000 0x03e7e4e380000000 0xa07cfc9c70000000

def z738 : W := mkw 0x0e003420e18ddde5 0x01c006841c31bbbc 0xfe001c00639fffe6 0x5fc003800c73fffc

def z739 : W := mkw 0x07fe9e8a00000000 0x00ffd3d140000000 0x87ffffff80000003 0xf0fffffff0000000

def z740 : W := mkw 0x00400a000c22a2a9 0x8008014001845455 0xfdd81b1c5c63e3ff 0xffbb03638b8c7c7f

def z741 : W := mkw 0x20400a2076807b00 0x040801440ed00f60 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z742 : W := mkw 0x87ffdfdf00005000 0x10fffbfbe0000a00 0x8fffffff80007c03 0xf1fffffff0000f80

def z743 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xafffffff80000387 0xf5fffffff0000070

def z744 : W := mkw 0x008b415100000000 0x0011682a20000000 0x07ffe7f380000003 0xe0fffcfe70000000

def z745 : W := mkw 0xa7749eaa76807b00 0x14ee93d54ed00f60 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z746 : W := mkw 0x8055dfdf00000000 0x100abbfbe0000000 0x8004ffff80000002 0x10009ffff0000000

def z747 : W := mkw 0x07bfd55b00000000 0x00f7faab60000000 0x87ffffff80000003 0xf0fffffff0000000

def z748 : W := mkw 0x1e15757b61d9d9b3 0x03c2aeaf6c3b3b36 0xe43bfbec43e3e398 0x9c877f7d887c7c73

def z749 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xf7ffffffdc638387 0xfefffffffb8c7070

def z750 : W := mkw 0x27ab15b47aa2d9a9 0x84f562b68f545b35 0x123b04fc23e39c79 0x0247609f847c738f

def z751 : W := mkw 0x409ea0007b7b0000 0x0813d4000f6f6000 0x75dfe0007fff8005 0xeebbfc000ffff000

def z752 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x77ffe7e07fff8007 0xeefffcfc0ffff000

def z753 : W := mkw 0x27601ea076d07b00 0x04ec03d40eda0f60 0xffe01fe07ffc7f86 0xfffc03fc0fff8ff0

def z754 : W := mkw 0x0000404100000000 0x0000080820000000 0x0224e7e380000002 0xc0449cfc70000000

def z755 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0224e7f380000002 0x00449cfe70000000

def z756 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xd7ffffffc0600007 0xfafffffff80c0000

def z757 : W := mkw 0x00cb4b550c22a2a9 0x8019696aa1845455 0xfdfbfbfc5c63e3ff 0xffbf7f7f8b8c7c7f

def z758 : W := mkw 0x1014000ae0545456 0x020280015c0a8a8a 0xdc1c181fe07c7c7f 0x5b838303fc0f8f8f

def z759 : W := mkw 0x1615555b60505012 0x02c2aaab6c0a0a02 0xc63fffffc060601b 0xd8c7fffff80c0c03

def z760 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x75fbe0007fff8004 0xaebf7c000ffff000

def z761 : W := mkw 0x0000404100000000 0x0000080820000000 0x0227e4e380000001 0xc044fc9c70000000

def z762 : W := mkw 0x31740aaa96d42f56 0x062e815552da85ea 0x31fc03ff9ffc03f9 0xa63f807ff3ff807f

def z763 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xffe01ff07f807fe7 0xfffc03fe0ff00ffc

def z764 : W := mkw 0x8735d5db000080a1 0x10e6babb60001014 0x3a27e7f3800383e7 0xc744fcfe7000707c

def z765 : W := mkw 0x0800202089af8de5 0x010004041135f1bc 0x780000007fff9fe4 0x0f0000000ffff3fc

def z766 : W := mkw 0x37601eaa76807b12 0x06ec03d54ed00f62 0xefe01fec7f807f9e 0xfdfc03fd8ff00ff3

def z767 : W := mkw 0x87ffdfdf72000000 0x10fffbfbee400000 0xc7ffffffdc000003 0xf8fffffffb800000

def z768 : W := mkw 0xe7ffdfdf7e727200 0x1cfffbfbefce4e40 0xc7ffffffdc606003 0xf8fffffffb8c0c00

def z769 : W := mkw 0x87ffdfdf0c222208 0x90fffbfbe1844441 0xefffffffdc60639f 0xfdfffffffb8c0c73

def z770 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x38000010239f9fe7 0x470000020473f3fc

def z771 : W := mkw 0x8014c04b00000000 0x1002980960000000 0x0224e4e380000000 0x00449c9c70000000

def z772 : W := mkw 0x00415fd100000000 0x00082bfa20000000 0x8227fff380000003 0xd044fffe70000000

def z773 : W := mkw 0x20401ea076807b00 0x040803d40ed00f60 0xedc01fe07f807f86 0xfdb803fc0ff00ff0

def z774 : W := mkw 0x87ffdfdf68720000 0x10fffbfbed0e4000 0xf7fffffffc7f8007 0xfeffffffff8ff000

def z775 : W := mkw 0x87ffdfdf72005000 0x10fffbfbee400a00 0xefffffffff807c07 0xfdfffffffff00f80

def z776 : W := mkw 0x07eb5fd500000000 0x00fd6bfaa0000000 0x87ffffff80000003 0xf0fffffff0000000

def z777 : W := mkw 0x87fedecf00000000 0x10ffdbd9e0000000 0x87fcffef80000002 0xf0ff9ffdf0000000

def z778 : W := mkw 0x0615415100000000 0x00c2a82a20000000 0x063fe7f380000003 0xc0c7fcfe70000000

def z779 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xffdf1f1fdc63e3ff 0xfffbe3e3fb8c7c7f

def z780 : W := mkw 0x0734c04100000000 0x00e6980820000000 0x0224e4e380000000 0x00449c9c70000000

def z781 : W := mkw 0x91ebcbd5e0545456 0x123d797abc0a8a8a 0x59e3e3e0607c7c7c 0xab3c7c7c0c0f8f8f

def z782 : W := mkw 0x57beb40a7b7b5012 0x0af7d6814f6f6a02 0x77ffe0007fff8005 0xeefffc000ffff000

def z783 : W := mkw 0x1734140af2545456 0x02e682815e4a8a8a 0xdfdc1c1ffc7c7c7f 0x7bfb8383ff8f8f8f

def z784 : W := mkw 0x80414bd500000000 0x1008297aa0000000 0x0227e7f380000003 0xc044fcfe70000000

def z785 : W := mkw 0x00410b100400a2a1 0x0008216200801454 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z786 : W := mkw 0x0120200013090000 0x0024040002612000 0x33e7e0003f9f8005 0xe67cfc0007f3f000

def z787 : W := mkw 0x18002020e1dd5d56 0x030004041c3babaa 0x5800000063fc7c7c 0x0b0000000c7f8f8f

def z788 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x87fcffff80000002 0x30ff9ffff0000000

def z789 : W := mkw 0x0615555b000080a1 0x00c2aaab60001014 0xfe3fffffc063e3ff 0xdfc7fffff80c7c7f

def z790 : W := mkw 0x08414b718484afe5 0x0108296e309095fc 0x88001ff380007fe2 0x110003fe70000ffc

def z791 : W := mkw 0x27741ea076807b00 0x04ee83d40ed00f60 0xeffc1fe07f807f87 0xfdff83fc0ff00ff0

def z792 : W := mkw 0x87615fdf00000000 0x10ec2bfbe0000000 0x87e7ffff80000003 0xf0fcfffff0000000

def z793 : W := mkw 0x41aaa0007b7b0000 0x083554000f6f6000 0x21e3e0003f9f8000 0xa43c7c0007f3f000

def z794 : W := mkw 0x0000404100000000 0x0000080820000000 0x0224e4f380000003 0x40449c9e70000000

def z795 : W := mkw 0x97ffdfdf60505012 0x12fffbfbec0a0a02 0xd7ffffffe07c601f 0xfafffffffc0f8c03

def z796 : W := mkw 0x28002020978dafe5 0x0500040412f1b5fc 0x380000003f9f9fe4 0x0700000007f3f3fc

def z797 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x33e7e0003f9f8005 0xe67cfc0007f3f000

def z798 : W := mkw 0x48002020f3dd8de5 0x090004041e7bb1bc 0x38000000239f9fe4 0x070000000473f3fc

def z799 : W := mkw 0x57beb40a7b7b5012 0x0af7d6814f6f6a02 0xf7fffc1fffffe01f 0xfeffff83fffffc03

def z800 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x38000300239f9fe6 0xc70000600473f3fc

def z801 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3227e7e3a39f9f85 0xc644fcfc7473f3f0

def z802 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0xbe3fffffa39f9fe7 0xd7c7fffff473f3fc

def z803 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xfddb1b0c5c63e3fc 0xbfbb63618b8c7c7f

def z804 : W := mkw 0xc734d4cb72500000 0x18e69a996e4a0000 0x0224e4e380000000 0x00449c9c70000000

def z805 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xfffffb1c5c63e3ff 0xffffff638b8c7c7f

def z806 : W := mkw 0x18012130e1ddddf7 0x030024261c3bbbbe 0xfc1b1b1c63ffffff 0xdf8363638c7fffff

def z807 : W := mkw 0x60debea00dfb7b00 0x0c1bd7d401bf6f60 0x981fffe0007fff83 0x1303fffc000ffff0

def z808 : W := mkw 0x87ffdfdf60005000 0x10fffbfbec000a00 0xc7ffffffc0006003 0xf8fffffff8000c00

def z809 : W := mkw 0x0601555160005000 0x00c02aaa2c000a00 0xce27fff3e0007c07 0xd9c4fffe7c000f80

def z810 : W := mkw 0x0001415100000000 0x0000282a20000000 0x863fffff80000003 0xd0c7fffff0000000

def z811 : W := mkw 0xa7ffdfdf76007200 0x14fffbfbeec00e40 0xcffffffffc007c07 0xf9ffffffff800f80

def z812 : W := mkw 0x27741ea076d07b00 0x04ee83d40eda0f60 0xfffc1ffc7ffc7fff 0xffff83ff8fff8fff

def z813 : W := mkw 0x87fedecf00000000 0x10ffdbd9e0000000 0x87fcfcff80000003 0x70ff9f9ff0000000

def z814 : W := mkw 0x1000140ae0545456 0x020002815c0a8a8a 0xdc181c1fe07c7c7f 0x5b830383fc0f8f8f

def z815 : W := mkw 0x889fe15f892f84ed 0x9113fc2bf125f09d 0x101fe01f807f8079 0x0203fc03f00ff00f

def z816 : W := mkw 0x080020208dafafed 0x8100040411b5f5fd 0x380000003f9f9fe4 0x0700000007f3f3fc

def z817 : W := mkw 0x0001617101890900 0x00002c2e20312120 0x3a27e7f3a39f9f87 0xc744fcfe7473f3f0

def z818 : W := mkw 0x06001400e0045444 0x00c002801c008a88 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z819 : W := mkw 0x48002020ffffafed 0x890004041ffff5fd 0x780000007ffffffc 0x0f0000000fffffff

def z820 : W := mkw 0x8735d5df00000000 0x10e6babbe0000000 0x0224e4ff80000000 0x00449c9ff0000000

def z821 : W := mkw 0x49ebeb751fababa9 0x893d7d6ea3f57575 0x21e3e3e01f838380 0xa43c7c7c03f07070

def z822 : W := mkw 0x8735d5db00000000 0x10e6babb60000000 0x0227e7e380000000 0x8044fcfc70000000

def z823 : W := mkw 0x8ffebeae818d8de5 0x11ffd7d5d031b1bc 0xbdd8180c239f9fe4 0x37bb03018473f3fc

def z824 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x30000000039f83e0 0x060000000073f07c

def z825 : W := mkw 0xa09fc17f76807b00 0x1413f82feed00f60 0x681fe01fff807f85 0x0d03fc03fff00ff0

def z826 : W := mkw 0x4734a00073590000 0x08e694000e6b2000 0x77e7e0007f9f8005 0xeefcfc000ff3f000

def z827 : W := mkw 0x27eb5ff57ea2fba9 0x84fd6bfeafd45f75 0xffffffffffe3ffff 0xfffffffffffc7fff

def z828 : W := mkw 0x4775ab147759a2a9 0x88eeb5628eeb3455 0x8a24fb1c239c63fa 0x11449f6384738c7f

def z829 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xedc01fe07f807f86 0x3db803fc0ff00ff0

def z830 : W := mkw 0x41aaa0001b2b0000 0x0835540003656000 0x23e7e0003f9f8000 0xa47cfc0007f3f000

def z831 : W := mkw 0x07601ea072800900 0x00ec03d40e500120 0xefe01fe07f801f86 0xfdfc03fc0ff003f0

def z832 : W := mkw 0x08012130818d8de5 0x010024261031b1bc 0x38030010239f9fe5 0x070060020473f3fc

def z833 : W := mkw 0x81ebcbdf00000000 0x103d797be0000000 0x01e3e3ff80000000 0xa03c7c7ff0000000

def z834 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xede01be07f807f84 0xbdbc037c0ff00ff0

def z835 : W := mkw 0x27749ea076807b00 0x04ee93d40ed00f60 0xefe4ffe07f807f86 0xfdfc9ffc0ff00ff0

def z836 : W := mkw 0x2f603ea0f78dffe5 0x05ec07d41ef1bffc 0xfdc018007f9fffe4 0x3fb803000ff3fffc

def z837 : W := mkw 0x800054cb00000000 0x10000a9960000000 0x0224e4e380000000 0x00449c9c70000000

def z838 : W := mkw 0x97ffdfdf60505012 0x12fffbfbec0a0a02 0xcfffffffe0607c1f 0xf9fffffffc0c0f83

def z839 : W := mkw 0x41aaa0007b7b0000 0x083554000f6f6000 0x75fbe0007fff8005 0xeebf7c000ffff000

def z840 : W := mkw 0x81ebdfdf00000000 0x103d7bfbe0000000 0x83e7ffff80000003 0xf07cfffff0000000

def z841 : W := mkw 0x0721415172000000 0x00e4282a2e400000 0x67e7e7f3ff800007 0xecfcfcfe7ff00000

def z842 : W := mkw 0x8774decb00000000 0x10ee9bd960000000 0x8224ffe380000002 0x10449ffc70000000

def z843 : W := mkw 0xc0417fdf7b7b0000 0x18082ffbef6f6000 0xf0001fffffff8006 0x1e0003fffffff000

def z844 : W := mkw 0x00014151000080a1 0x0000282a20001014 0x0a27e7f3800003e3 0xc144fcfe7000007c

def z845 : W := mkw 0x2f617fd1f70df6e5 0x05ec2ffa3ee1bedc 0xd5c7f813dc1fe061 0x3ab8ff027b83fc0c

def z846 : W := mkw 0x21600aa076807b00 0x042c01540ed00f60 0xede01be07f807f86 0xfdbc037c0ff00ff0

def z847 : W := mkw 0x8134c0cb00000000 0x1026981960000000 0x0024e0e380000000 0x00049c1c70000000

def z848 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0227e4f380000001 0x0044fc9e70000000

def z849 : W := mkw 0x5f34f46bf3dd5d56 0x0be69e8d7e7babaa 0x0224e4e3a39c1c00 0x00449c9c74738380

def z850 : W := mkw 0x0000000000000000 0x0000000000000000 0xde1c1c1fc060607f 0x5bc38383f80c0c0f

def z851 : W := mkw 0x00cb4b550c22a2a9 0x8019696aa1845455 0xfddffb1fdc63e3ff 0xffbbff63fb8c7c7f

def z852 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xfffb1ffc5c63e3ff 0xffff63ff8b8c7c7f

def z853 : W := mkw 0x0001415100000000 0x0000282a20000000 0x2227e7f3a3800007 0xc444fcfe74700000

def z854 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xefe41ff3ff807f87 0xfdfc83fe7ff00ff0

def z855 : W := mkw 0x80cbcb550c22a2a9 0x9019796aa1845455 0xfddbfb1c5c63e3ff 0xffbb7f638b8c7c7f

def z856 : W := mkw 0x87ffdfdf00500000 0x10fffbfbe00a0000 0x97ffffff807c0003 0xf2fffffff00f8000

def z857 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0x2be007e03f801f86 0xe57c00fc07f003f0

def z858 : W := mkw 0x8735d5db00000000 0x10e6babb60000000 0x863fffff80000003 0xd0c7fffff0000000

def z859 : W := mkw 0x27741eaa76807b00 0x04ee83d54ed00f60 0xeff81fec7f807f86 0xfdff03fd8ff00ff0

def z860 : W := mkw 0xc7ffdfdf08720000 0x18fffbfbe10e4000 0x87ffffff80600003 0xf0fffffff00c0000

def z861 : W := mkw 0x47beb40a7b7b5000 0x08f7d6814f6f6a00 0xfffffc1ffffffc07 0xffffff83ffffff80

def z862 : W := mkw 0xc7ffdfdf7a720000 0x18fffbfbef4e4000 0xf7ffffffdc638007 0xfefffffffb8c7000

def z863 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x97ffffffa01c0007 0xf2fffffff4038000

def z864 : W := mkw 0x87fedecf00000000 0x10ffdbd9e0000000 0x03e4e4e380000000 0x207c9c9c70000000

def z865 : W := mkw 0x47bfc1517a720000 0x08f7f82a2f4e4000 0x47ffe7f3dc600003 0xe8fffcfe7b8c0000

def z866 : W := mkw 0x1014000a80540456 0x02028001500a808a 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z867 : W := mkw 0xc7bea00e7b7b0000 0x18f7d401cf6f6000 0x77ffe00c7fff8005 0xeefffc018ffff000

def z868 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0xfc18181c63ffffff 0x5f8303038c7fffff

def z869 : W := mkw 0x87ffdfdf04002200 0x10fffbfbe0800440 0xa7ffffff9c000383 0xf4fffffff3800070

def z870 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xdddb1b1c5c63e3fb 0x3bbb63638b8c7c7f

def z871 : W := mkw 0x3734148af2545456 0x06e682915e4a8a8a 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z872 : W := mkw 0x48002020f3dd0d44 0x090004041e7ba1a8 0x00000000239c1c00 0x0000000004738380

def z873 : W := mkw 0x81ebcbd50c22a2a9 0x903d797aa1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z874 : W := mkw 0x7734b4aaf3dd5d56 0x0ee696955e7babaa 0x0224e4e3a39c1c00 0x00449c9c74738380

def z875 : W := mkw 0x87ffdfdf0400a2a9 0x90fffbfbe0801455 0xbfffffff8003e3ff 0xf7fffffff0007c7f

def z876 : W := mkw 0x00414b5104002200 0x0008296a20800440 0xefe7fff3dc006387 0xfdfcfffe7b800c70

def z877 : W := mkw 0x088a202089af8de5 0x011144041135f1bc 0x7ddb00007fff9fe5 0xefbb60000ffff3fc

def z878 : W := mkw 0x008b0110082280a1 0x0011602201045014 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z879 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0x67e007e07f801f84 0xecfc00fc0ff003f0

def z880 : W := mkw 0x808bc15500000000 0x1011782aa0000000 0x0227e7f380000003 0xc044fcfe70000000

def z881 : W := mkw 0x008a2000092b0000 0x0011440001256000 0x33e7e0003f9f8005 0xe67cfc0007f3f000

def z882 : W := mkw 0x87ffdfdf72500000 0x10fffbfbee4a0000 0xf7fffffffffc0007 0xfeffffffffff8000

def z883 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x77ffe01c7fff807d 0xeefffc038ffff00f

def z884 : W := mkw 0x87bfd5df00000000 0x10f7fabbe0000000 0x07ffe4ff80000001 0xe0fffc9ff0000000

def z885 : W := mkw 0x47ffeb557f7ba2a9 0x88fffd6aafef7455 0xffffffffffffe3ff 0xfffffffffffffc7f

def z886 : W := mkw 0x18415f7f8484ffff 0x83082beff0909fff 0x88001fff80007ffa 0x110003fff0000fff

def z887 : W := mkw 0x08402a20858dafe5 0x0108054410b1b5fc 0xfdc01b007f9fffe6 0xffb803600ff3fffc

def z888 : W := mkw 0xc7ffdfdf7a720000 0x18fffbfbef4e4000 0xe7ffffffffe00007 0xfcfffffffffc0000

def z889 : W := mkw 0x87ffcbdf00000000 0x10fff97be0000000 0x07ffe3ff80000001 0xe0fffc7ff0000000

def z890 : W := mkw 0x28002020f38d5d44 0x050004041e71aba8 0x00000000239c1c00 0x0000000004738380

def z891 : W := mkw 0x07601ea004802b00 0x00ec03d400900560 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z892 : W := mkw 0x81ffcbdf0c22a2a9 0x903ff97be1845455 0x31ffe3ff9c6383f9 0xa63ffc7ff38c707f

def z893 : W := mkw 0x81ebcbd500000000 0x103d797aa0000000 0x03e7e7e380000000 0xa07cfcfc70000000

def z894 : W := mkw 0x08006061818d0d44 0x01000c0c3031a1a8 0x3a27e7e3a39f9f87 0xc744fcfc7473f3f0

def z895 : W := mkw 0x47aaa0007b2b0000 0x08f554000f656000 0x77e7e0007f9f8005 0xeefcfc000ff3f000

def z896 : W := mkw 0xa8415fff8484ffe5 0x15082bfff0909ffc 0x88001fff80007fe2 0x110003fff0000ffc

def z897 : W := mkw 0x27600aa076807b00 0x04ec01540ed00f60 0x6fe003e07f807f84 0xedfc007c0ff00ff0

def z898 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x3a200000239f9fe4 0xc74400000473f3fc

def z899 : W := mkw 0x07bec04100000000 0x00f7d80820000000 0x07ffe4e380000001 0xe0fffc9c70000000

def z900 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x7fe7e7f3ff9f9fe7 0xeffcfcfe7ff3f3fc

def z901 : W := mkw 0x28002020f38ddde5 0x050004041e71bbbc 0x38000000239f9fe4 0x070000000473f3fc

def z902 : W := mkw 0x00014151000080a1 0x0000282a20001014 0x2227e7f380038383 0xc444fcfe70007070

def z903 : W := mkw 0x87ffdfdf0400a2a1 0x10fffbfbe0801454 0xffffffffdc03e3e7 0xfffffffffb807c7c

def z904 : W := mkw 0x37741eaa76d07b12 0x06ee83d54eda0f62 0xfffc1fec7ffc7f9f 0xffff83fd8fff8ff3

def z905 : W := mkw 0x47bea0007b7b5000 0x08f7d4000f6f6a00 0x7fffe0007ffffc05 0xeffffc000fffff80

def z906 : W := mkw 0x87fedecf0c222208 0x90ffdbd9e1844441 0xc7fcfcefdc606018 0x38ff9f9dfb8c0c03

def z907 : W := mkw 0x81ebcbd50c22a2a9 0x903d797aa1845455 0x3be7e7f39c0383e7 0xe77cfcfe7380707c

def z908 : W := mkw 0x47beb40a7b7b0000 0x08f7d6814f6f6000 0xfffffc1fffffe07f 0xffffff83fffffc0f

def z909 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xcfe01fe07f807f82 0x39fc03fc0ff00ff0

def z910 : W := mkw 0x87fedecb00000000 0x10ffdbd960000000 0x87ffffe380000003 0xf0fffffc70000000

def z911 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x8fffffffa0001c07 0xf1fffffff4000380

def z912 : W := mkw 0x00cb4b550c222208 0x8019696aa1844441 0xc7ffffffdc60601b 0xf8fffffffb8c0c03

def z913 : W := mkw 0x47beb4807b7b0000 0x08f7d6900f6f6000 0x77ffe4e07fff8005 0xeefffc9c0ffff000

def z914 : W := mkw 0x00cb4b550c22a2a9 0x8019696aa1845455 0x21e3e3e01c038380 0xa43c7c7c03807070

def z915 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x2a27e7f3a39f9fe2 0x8544fcfe7473f3fc

def z916 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0x9fffffff8063e3fb 0xf3fffffff00c7c7f

def z917 : W := mkw 0x809fc15f00000000 0x1013f82be0000000 0x003fe3ff80000001 0x8007fc7ff0000000

def z918 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x75dfe0007fff8005 0x2ebbfc000ffff000

def z919 : W := mkw 0x87ffdfdf000080a1 0x10fffbfbe0001014 0xffffffffc063e3ff 0xfffffffff80c7c7f

def z920 : W := mkw 0x58002020fbffddf7 0x0b0004041f7ffbbe 0x780000007ffffffc 0x0f0000000fffffff

def z921 : W := mkw 0x37601ea076d07b12 0x06ec03d40eda0f62 0xefe01fe07fe07f9e 0xfdfc03fc0ffc0ff3

def z922 : W := mkw 0x8015c15b00000000 0x1002b82b60000000 0x0227e7f380000003 0xc044fcfe70000000

def z923 : W := mkw 0x77fe9e8a7e727212 0x0effd3d14fce4e42 0xc5d8180c5c606018 0x38bb03018b8c0c03

def z924 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0xfe27fff3e39fffe7 0xdfc4fffe7c73fffc

def z925 : W := mkw 0x00414b5500000000 0x0008296aa0000000 0x8227ffff80000003 0xd044fffff0000000

def z926 : W := mkw 0x27601eaa76807b00 0x04ec03d54ed00f60 0xefe01fffff807f86 0xfdfc03fffff00ff0

def z927 : W := mkw 0x81ebcbd500000000 0x103d797aa0000000 0x87ffffff80000003 0xf0fffffff0000000

def z928 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0xba27ffffa39fffff 0xd744fffff473ffff

def z929 : W := mkw 0x81ebdfdf0c22a2a9 0x903d7bfbe1845455 0xfdfbffffdc63e3ff 0xffbf7ffffb8c7c7f

def z930 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x7fffe0107fff8067 0xeffffc020ffff00c

def z931 : W := mkw 0x088b6151892f84e5 0x01116c2a3125f09c 0x101fe013807f8061 0x0203fc02700ff00c

def z932 : W := mkw 0x87ffdfdf7e22a2a9 0x90fffbfbefc45455 0xffffffffffe3e3ff 0xfffffffffffc7c7f

def z933 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xefffffffdc03e387 0xfdfffffffb807c70

def z934 : W := mkw 0x00cb4b5500000000 0x0019696aa0000000 0x03e7e7f380000003 0xe07cfcfe70000000

def z935 : W := mkw 0x81ebcbd500000000 0x103d797aa0000000 0x01e7e3f380000001 0xa03cfc7e70000000

def z936 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x67ffe0007fff8000 0xacfffc000ffff000

def z937 : W := mkw 0x08414b758484afed 0x8108296eb09095fd 0x080007f380001fe2 0x010000fe700003fc

def z938 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x0227e4e380000001 0xc044fc9c70000000

def z939 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xcfffffffc0006007 0xf9fffffff8000c00

def z940 : W := mkw 0xa7ffdfdf7e22f2a9 0x94fffbfbefc45e55 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z941 : W := mkw 0x1e14342ae1ddddf7 0x03c286855c3bbbbe 0xfc18180c63fffffc 0x1f8303018c7fffff

def z942 : W := mkw 0x2720002076807b00 0x04e400040ed00f60 0x6fe007e07f807f86 0xedfc00fc0ff00ff0

def z943 : W := mkw 0x08016175818d8ded 0x81002c2eb031b1bd 0x3a27e7ffa39f9fff 0xc744fcfff473f3ff

def z944 : W := mkw 0x47beb4007b7b0000 0x08f7d6800f6f6000 0xf7fffc007fff8007 0xfeffff800ffff000

def z945 : W := mkw 0x10000000e0545456 0x020000001c0a8a8a 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z946 : W := mkw 0x8735d5db00000000 0x10e6babb60000000 0x0227e4f380000001 0x0044fc9e70000000

def z947 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x7800000063fffffc 0x0f0000000c7fffff

def z948 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0xf7fff81c7fff8007 0xfeffff038ffff000

def z949 : W := mkw 0x08012130818d8de5 0x010024261031b1bc 0x38030300239f9fe4 0x870060600473f3fc

def z950 : W := mkw 0x87ffdfdf04002208 0x90fffbfbe0800441 0x87ffffff8000601b 0xf0fffffff0000c03

def z951 : W := mkw 0x1800202081dd8df7 0x03000404103bb1be 0x3800000023ff9ffc 0x07000000047ff3ff

def z952 : W := mkw 0x1734148ae0545456 0x02e682915c0a8a8a 0xde3c1cffe07c7c7f 0x5bc7839ffc0f8f8f

def z953 : W := mkw 0x8734d4cb0c22a2a9 0x90e69a9961845455 0x7a24e4e3dc63e3fc 0x0f449c9c7b8c7c7f

def z954 : W := mkw 0x87ffdfdf60500000 0x10fffbfbec0a0000 0xc7ffffffc0600003 0xf8fffffff80c0000

def z955 : W := mkw 0xa7601eae76807b00 0x14ec03d5ced00f60 0xefe01fec7f807f86 0xfdfc03fd8ff00ff0

def z956 : W := mkw 0x0f202020f38d8de5 0x01e404041e71b1bc 0x7fe000007f9f9fe4 0xeffc00000ff3f3fc

def z957 : W := mkw 0x21600aa016802b00 0x042c015402d00560 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z958 : W := mkw 0x08cb2b34818d8de5 0x011965669031b1bc 0xbddb1b1c239f9fe7 0xf7bb63638473f3fc

def z959 : W := mkw 0x97ffdfdf6c72f2bb 0x92fffbfbed8e5e57 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z960 : W := mkw 0x57beb40a7b7b5012 0x0af7d6814f6f6a02 0xfffffc0c7ffffc1f 0xffffff818fffff83

def z961 : W := mkw 0x87ffdfdf000080a1 0x10fffbfbe0001014 0xa7ffffff80038383 0xf4fffffff0007070

def z962 : W := mkw 0x87ffdfdf60000000 0x10fffbfbec000000 0xc7ffffffe0000007 0xf8fffffffc000000

def z963 : W := mkw 0x97ffdfdf60505012 0x12fffbfbec0a0a02 0xdfffffffc060607f 0xfbfffffff80c0c0f

def z964 : W := mkw 0x81ebcbd500000000 0x103d797aa0000000 0x01e3e7f380000002 0xa03c7cfe70000000

def z965 : W := mkw 0x000141510c22a2a9 0x8000282a21845455 0x7a27e7f3dc63e3ff 0xcf44fcfe7b8c7c7f

def z966 : W := mkw 0x41aaa0001b2b0000 0x0835540003656000 0x31e7e0001f9f8001 0xa63cfc0003f3f000

def z967 : W := mkw 0x00ca0a040c22a2a9 0x8019414081845455 0xfddb180c5c63e3fd 0xffbb63018b8c7c7f

def z968 : W := mkw 0x0015415b00000000 0x0002a82b60000000 0x023fe7ff80000003 0xc047fcfff0000000

def z969 : W := mkw 0x27741ea076d07b00 0x04ee83d40eda0f60 0xefe41fe07f9c7f86 0xfdfc83fc0ff38ff0

def z970 : W := mkw 0x87ffdfdf04002200 0x10fffbfbe0800440 0xc7ffffffdc006003 0xf8fffffffb800c00

def z971 : W := mkw 0x0614544b00000000 0x00c28a8960000000 0x863cfcff80000003 0x50c79f9ff0000000

def z972 : W := mkw 0x28002020f78d7f44 0x050004041ef1afe8 0x680000007f9c7f84 0x0d0000000ff38ff0

def z973 : W := mkw 0x87ffdfdf08220000 0x10fffbfbe1044000 0xffffffffdc63e07f 0xfffffffffb8c7c0f

def z974 : W := mkw 0x0800202089af8ded 0x810004041135f1bd 0x3800000023ff9ffc 0x07000000047ff3ff

def z975 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xeddb1b1c5c63e3fa 0xbdbb63638b8c7c7f

def z976 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xffe01fe07fe07ffe 0xfffc03fc0ffc0fff

def z977 : W := mkw 0x47bea0001b7b0000 0x08f7d400036f6000 0x37ffe0001fff8001 0xe6fffc0003fff000

def z978 : W := mkw 0x28002020ffafffed 0x850004041ff5fffd 0x780000007ffffffc 0x0f0000000fffffff

def z979 : W := mkw 0x81bfc1df00000000 0x1037f83be0000000 0x003fe0ff80000001 0x0007fc1ff0000000

def z980 : W := mkw 0x8775dfdf00000000 0x10eebbfbe0000000 0x863cffff80000003 0x50c79ffff0000000

def z981 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x20000000239f9f80 0x040000000473f3f0

def z982 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xe7ffffffdc63e39b 0xfcfffffffb8c7c73

def z983 : W := mkw 0x01614bd100000000 0x002c297a20000000 0x03e7e7f380000003 0xe07cfcfe70000000

def z984 : W := mkw 0x480020209baf8de5 0x090004041375f1bc 0x380000003f9f9fe4 0x0700000007f3f3fc

def z985 : W := mkw 0x81ebdfdf00000000 0x103d7bfbe0000000 0x85fbffff80000003 0xf0bf7ffff0000000

def z986 : W := mkw 0x800155db00000000 0x10002abb60000000 0x0227e7f380000003 0xc044fcfe70000000

def z987 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xc7ffffffc060601b 0xf8fffffff80c0c03

def z988 : W := mkw 0x809fc15f00000000 0x1013f82be0000000 0x023fe4ff80000001 0x0047fc9ff0000000

def z989 : W := mkw 0x87ffdfdf72000000 0x10fffbfbee400000 0x87ffffffa3800003 0xf0fffffff4700000

def z990 : W := mkw 0x87ffdfdf0400a2a9 0x90fffbfbe0801455 0xdfffffffc06063ff 0xfbfffffff80c0c7f

def z991 : W := mkw 0x86555fdf00000000 0x10caabfbe0000000 0x863fffff80000003 0xd0c7fffff0000000

def z992 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0x6be007e07f807f84 0xad7c00fc0ff00ff0

def z993 : W := mkw 0x87ffdfdf0c222200 0x10fffbfbe1844440 0xffffffffdc63e387 0xfffffffffb8c7c70

def z994 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x7fffe0007fffe07d 0xeffffc000ffffc0f

def z995 : W := mkw 0x8734d4cb60005000 0x10e69a996c000a00 0x0224e4e3a0001c00 0x00449c9c74000380

def z996 : W := mkw 0xa7ffdfdf72005000 0x14fffbfbee400a00 0x87ffffff80000003 0xf0fffffff0000000

def z997 : W := mkw 0xa774decb76007200 0x14ee9bd96ec00e40 0xc7e4fce3dc006000 0x38fc9f9c7b800c00

def z998 : W := mkw 0x589fe15b897f84f7 0x0b13fc2b712ff09e 0x101fe01f807f8079 0x0203fc03f00ff00f

def z999 : W := mkw 0x08002020e1dd8de5 0x010004041c3bb1bc 0x7800000063ff9fe4 0x0f0000000c7ff3fc

def z1000 : W := mkw 0x01abc15100000000 0x0035782a20000000 0x03e7e7f380000003 0xe07cfcfe70000000

def z1001 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xde3ffc1fe07c7c7f 0xdbc7ff83fc0f8f8f

def z1002 : W := mkw 0x87ffdfdf6c72a2a9 0x90fffbfbed8e5455 0xfffffffffc7fe3ff 0xffffffffff8ffc7f

def z1003 : W := mkw 0x80cb4bd50c22a2a9 0x9019697aa1845455 0xfddb1bfc5c63e3ff 0xffbb637f8b8c7c7f

def z1004 : W := mkw 0x08002020f38d8de5 0x010004041e71b1bc 0x780000007f9f9fe4 0x0f0000000ff3f3fc

def z1005 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x07ffe7e380000001 0xe0fffcfc70000000

def z1006 : W := mkw 0x1734940ae0545456 0x02e692815c0a8a8a 0xde3cfc1fe07c7c7f 0x5bc79f83fc0f8f8f

def z1007 : W := mkw 0x87ffdfdf60500000 0x10fffbfbec0a0000 0xdfffffffe07c607f 0xfbfffffffc0f8c0f

def z1008 : W := mkw 0x8161dfdf00000000 0x102c3bfbe0000000 0x8020ffff80000002 0x10041ffff0000000

def z1009 : W := mkw 0x189f615f897f84ff 0x8313ec2bf12ff09f 0x101fe01f807f8079 0x0203fc03f00ff00f

def z1010 : W := mkw 0x97ffdfdf60505012 0x12fffbfbec0a0a02 0x87ffffff80000003 0xf0fffffff0000000

def z1011 : W := mkw 0x07600a2076802b00 0x00ec01440ed00560 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z1012 : W := mkw 0x27741eaa76807b00 0x04ee83d54ed00f60 0xefe41fe3ff807f86 0xfdfc83fc7ff00ff0

def z1013 : W := mkw 0x87ebdfdf00000000 0x10fd7bfbe0000000 0x87e3ffff80000002 0xf0fc7ffff0000000

def z1014 : W := mkw 0x27741ea076d07b00 0x04ee83d40eda0f60 0xeff81fe07fe07f86 0xfdff03fc0ffc0ff0

def z1015 : W := mkw 0x0001415100000000 0x0000282a20000000 0x1a27e7f380000067 0xc344fcfe7000000c

def z1016 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x03e7e7f380000003 0xe07cfcfe70000000

def z1017 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xeff81ffc7f807f87 0xfdff03ff8ff00ff0

def z1018 : W := mkw 0xa7ffdfdf7e227208 0x94fffbfbefc44e41 0xc7ffffffdc60601b 0xf8fffffffb8c0c03

def z1019 : W := mkw 0x8734d4cb60500000 0x10e69a996c0a0000 0x563ce4e3e07c0005 0x4ac79c9c7c0f8000

def z1020 : W := mkw 0x088b6155892f84ed 0x81116c2ab125f09d 0x1007e013801f8061 0x0200fc027003f00c

def z1021 : W := mkw 0x80415fdf00000000 0x10082bfbe0000000 0x8023ffff80000002 0x90047ffff0000000

def z1022 : W := mkw 0x87ffcbd500000000 0x10fff97aa0000000 0x07ffe7f380000003 0xe0fffcfe70000000

def z1023 : W := mkw 0x41bea0001b7b0000 0x0837d400036f6000 0x75ffe0005fff8005 0xeebffc000bfff000

def z1024 : W := mkw 0x87ffdfdf000080a9 0x90fffbfbe0001015 0x87ffffff8000007b 0xf0fffffff000000f

def z1025 : W := mkw 0x00cb4b550c22a2a9 0x8019696aa1845455 0xfddb1fffdc63e3ff 0xffbb63fffb8c7c7f

def z1026 : W := mkw 0x87ffdfdf08220000 0x10fffbfbe1044000 0xa7ffffff9c038003 0xf4fffffff3807000

def z1027 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xffdf1b1c7c7fe3ff 0xfffbe3638f8ffc7f

def z1028 : W := mkw 0x06df5f5f0c22a2a9 0x80dbebebe1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z1029 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xbfffffff9c0383e7 0xf7fffffff380707c

def z1030 : W := mkw 0x07ffdfd100000000 0x00fffbfa20000000 0x87fffff380000003 0xf0fffffe70000000

def z1031 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x8624fce380000002 0x50c49f9c70000000

def z1032 : W := mkw 0x70002020ffff7f56 0x0e0004041fffefea 0x780000007ffffffc 0x0f0000000fffffff

def z1033 : W := mkw 0x8775dfdf00000000 0x10eebbfbe0000000 0x0224e7e380000000 0x00449cfc70000000

def z1034 : W := mkw 0x18002020e1dd5d56 0x030004041c3babaa 0x00000000239c1c00 0x0000000004738380

def z1035 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x9fffffff80000067 0xf3fffffff000000c

def z1036 : W := mkw 0x97ffdfdf6c72721a 0x92fffbfbed8e4e43 0xc7ffffffdc60601b 0xf8fffffffb8c0c03

def z1037 : W := mkw 0x9734948ae0545456 0x12e692915c0a8a8a 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z1038 : W := mkw 0x27615fd176007200 0x04ec2bfa2ec00e40 0xc7e7fff3dc006003 0xf8fcfffe7b800c00

def z1039 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xfdd81b1c5c63e3fe 0x3fbb03638b8c7c7f

def z1040 : W := mkw 0x08002020858dafe5 0x0100040410b1b5fc 0x780000007f9fffe4 0x0f0000000ff3fffc

def z1041 : W := mkw 0x8775dfdf00000000 0x10eebbfbe0000000 0x87e4ffff80000002 0xf0fc9ffff0000000

def z1042 : W := mkw 0x81ebdfdf00000000 0x103d7bfbe0000000 0x01e3e7e380000000 0xa03c7cfc70000000

def z1043 : W := mkw 0x07bea000092b0000 0x00f7d40001256000 0x77ffe0007fff8005 0xeefffc000ffff000

def z1044 : W := mkw 0x08002020818d0d44 0x010004041031a1a8 0x28000000239c1f84 0x05000000047383f0

def z1045 : W := mkw 0x87ffdfdf082280a9 0x90fffbfbe1045015 0xbfffffff806383ff 0xf7fffffff00c707f

def z1046 : W := mkw 0x87bed4cb08220000 0x10f7da9961044000 0x77ffe4e3dc638005 0xeefffc9c7b8c7000

def z1047 : W := mkw 0x8014d4cb00000000 0x10029a9960000000 0x0004e4e380000000 0x00009c9c70000000

def z1048 : W := mkw 0x0734200073590000 0x00e684000e6b2000 0x77ffe0007fff8005 0xeefffc000ffff000

def z1049 : W := mkw 0x97ffdfdf00005012 0x12fffbfbe0000a02 0x87ffffff8000601b 0xf0fffffff0000c03

def z1050 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x023ce4ff80000001 0x00479c9ff0000000

def z1051 : W := mkw 0x37741eaa76d07b12 0x06ee83d54eda0f62 0xfff81ffc7fe07fff 0xffff03ff8ffc0fff

def z1052 : W := mkw 0x87ffdfdf0c222208 0x90fffbfbe1844441 0xdfffffffdc60607f 0xfbfffffffb8c0c0f

def z1053 : W := mkw 0x41aaa0001b2b0000 0x0835540003656000 0x31e3e0003f9f8004 0xa63c7c0007f3f000

def z1054 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x2a27e7e3a39f9f86 0xc544fcfc7473f3f0

def z1055 : W := mkw 0x4fbea020fbff8de5 0x09f7d4041f7ff1bc 0x7dd800007fff9fe4 0x2fbb00000ffff3fc

def z1056 : W := mkw 0x87ffdfdf60500000 0x10fffbfbec0a0000 0x87ffffffa01c0003 0xf0fffffff4038000

def z1057 : W := mkw 0x80dfcb5f0c22a2a9 0x901bf96be1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z1058 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x823fffff80000003 0x1047fffff0000000

def z1059 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xde3c1fffe07c7c7f 0xdbc783fffc0f8f8f

def z1060 : W := mkw 0x27741eaa76d07b00 0x04ee83d54eda0f60 0xfffc1ffffffc7f87 0xffff83ffffff8ff0

def z1061 : W := mkw 0x00cb4b550c22a2a9 0x8019696aa1845455 0x23e7e7f39c038383 0xe47cfcfe73807070

def z1062 : W := mkw 0x009fc15100000000 0x0013f82a20000000 0x023fe7f380000003 0xc047fcfe70000000

def z1063 : W := mkw 0x87ffdfdf082280a1 0x10fffbfbe1045014 0xffffffffdc6383e7 0xfffffffffb8c707c

def z1064 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x7fffe3007fff8387 0xeffffc600ffff070

def z1065 : W := mkw 0x21600aa016802b00 0x042c015402d00560 0x29e003e03f801f84 0xa53c007c07f003f0

def z1066 : W := mkw 0x08002020e18ddde5 0x010004041c31bbbc 0x78000000639fffe4 0x0f0000000c73fffc

def z1067 : W := mkw 0x41bea0001b7b0000 0x0837d400036f6000 0x33ffe0003fff8005 0xe67ffc0007fff000

def z1068 : W := mkw 0x18002020818dddf7 0x030004041031bbbe 0x38000000239ffffc 0x070000000473ffff

def z1069 : W := mkw 0x87ffdfdf60505000 0x10fffbfbec0a0a00 0xdfffffffe07c7c07 0xfbfffffffc0f8f80

def z1070 : W := mkw 0x0001415100000000 0x0000282a20000000 0x3227e7f380038007 0xc644fcfe70007000

def z1071 : W := mkw 0x0e142020e1dd8de5 0x01c284041c3bb1bc 0x7e1c000063ff9fe5 0x4fc380000c7ff3fc

def z1072 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xefe7ffe07f807f87 0xfdfcfffc0ff00ff0

def z1073 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xb7ffffff9c6383fb 0xf6fffffff38c707f

def z1074 : W := mkw 0x28cb2b34ffafffed 0x851965669ff5fffd 0xfddb1b1c7fffffff 0xffbb63638fffffff

def z1075 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x75ffe0005fff8001 0xaebffc000bfff000

def z1076 : W := mkw 0x87bed4cb00000000 0x10f7da9960000000 0x07fce4e380000000 0x20ff9c9c70000000

def z1077 : W := mkw 0x41aaa0001b2b0000 0x0835540003656000 0x77ffe0007fff8005 0xeefffc000ffff000

def z1078 : W := mkw 0x68002020ffffffe5 0x0d0004041ffffffc 0x780000007fffffe4 0x0f0000000ffffffc

def z1079 : W := mkw 0x21600aa016802b00 0x042c015402d00560 0x29e007e01f801f82 0xa53c00fc03f003f0

def z1080 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0x23e7e7e39c038380 0xa47cfcfc73807070

def z1081 : W := mkw 0x00002020818d0d44 0x000004041031a1a8 0x3a27e7f3a39f9fe7 0xc744fcfe7473f3fc

def z1082 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x97ffffff8060007b 0xf2fffffff00c000f

def z1083 : W := mkw 0x07ffcb550c22a2a9 0x80fff96aa1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z1084 : W := mkw 0x80415fdf00000000 0x10082bfbe0000000 0x8007ffff80000003 0x1000fffff0000000

def z1085 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xdc1c181fe07c7c7d 0x1b838303fc0f8f8f

def z1086 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x57ffe0007fff8001 0x2afffc000ffff000

def z1087 : W := mkw 0x87ffdfdf64007200 0x10fffbfbec800e40 0xeffffffffc007f87 0xfdffffffff800ff0

def z1088 : W := mkw 0x809fc15f00000000 0x1013f82be0000000 0x001fe7ff80000003 0x0003fcfff0000000

def z1089 : W := mkw 0xc7ffdfdf7a720000 0x18fffbfbef4e4000 0xd7fffffffc7c0007 0xfaffffffff8f8000

def z1090 : W := mkw 0x0001415100000000 0x0000282a20000000 0x2a27e7f380000387 0xc544fcfe70000070

def z1091 : W := mkw 0x47bea00a7b7b0000 0x08f7d4014f6f6000 0x77ffe01fffff8005 0xeefffc03fffff000

def z1092 : W := mkw 0x81ffdfdf00000000 0x103ffbfbe0000000 0x81ffffff80000003 0xb03ffffff0000000

def z1093 : W := mkw 0x0120002012800900 0x0024000402500120 0x2be007e03f801f86 0xe57c00fc07f003f0

def z1094 : W := mkw 0x0614140a80040444 0x00c2828150008088 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z1095 : W := mkw 0x869fd55f00000000 0x10d3faabe0000000 0x863fffff80000003 0xd0c7fffff0000000

def z1096 : W := mkw 0xc7ffdfdf7e72a2a9 0x98fffbfbefce5455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z1097 : W := mkw 0x8774decb00000000 0x10ee9bd960000000 0x87e4fce380000000 0x30fc9f9c70000000

def z1098 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0xf7fff80c7fffe01d 0xfeffff018ffffc03

def z1099 : W := mkw 0xb7ffdfdf76507212 0x16fffbfbeeca0e42 0xc7ffffffdc60601b 0xf8fffffffb8c0c03

def z1100 : W := mkw 0x87ffdfdf0c222208 0x90fffbfbe1844441 0x87ffffff9c000003 0xf0fffffff3800000

def z1101 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x87ffffef80000000 0xb0fffffdf0000000

def z1102 : W := mkw 0x07605ec100000000 0x00ec0bd820000000 0x87e4ffe380000002 0xf0fc9ffc70000000

def z1103 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xf5db1b1c5c63e3f9 0xbebb63638b8c7c7f

def z1104 : W := mkw 0x00414b5100000000 0x0008296a20000000 0x87e7fff380000003 0xf0fcfffe70000000

def z1105 : W := mkw 0x21600aa016802b00 0x042c015402d00560 0x23e007e03f801f80 0xa47c00fc07f003f0

def z1106 : W := mkw 0x07aa20007b2b0000 0x00f544000f656000 0x77ffe0007fff8005 0xeefffc000ffff000

def z1107 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xe7ffffffdc000007 0xfcfffffffb800000

def z1108 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x77ffe413ffff8007 0xeefffc827ffff000

def z1109 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xdc181c1fe07c7c7e 0x1b830383fc0f8f8f

def z1110 : W := mkw 0x0000002000800900 0x0000000400100120 0x6fe007e07f801f86 0xedfc00fc0ff003f0

def z1111 : W := mkw 0x87bfd5df082280a9 0x90f7fabbe1045015 0x123fe4ff80638079 0x0247fc9ff00c700f

def z1112 : W := mkw 0x87ffdfdf08220008 0x90fffbfbe1044001 0x87ffffff8060001b 0xf0fffffff00c0003

def z1113 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x83e7ffff80000002 0xb07cfffff0000000

def z1114 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x38030000239f9fe5 0xc70060000473f3fc

def z1115 : W := mkw 0x07eb5fd50c22a2a9 0x80fd6bfaa1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z1116 : W := mkw 0x069e2000697b0000 0x00d3c4000d2f6000 0x77ffe0007fff8005 0xeefffc000ffff000

def z1117 : W := mkw 0x80dfcb5f00000000 0x101bf96be0000000 0x87ffffff80000003 0xf0fffffff0000000

def z1118 : W := mkw 0x87ebdfd500000000 0x10fd7bfaa0000000 0x87e7fff380000003 0xf0fcfffe70000000

def z1119 : W := mkw 0x87ffdfdf0400a2a9 0x90fffbfbe0801455 0x87ffffff80000383 0xf0fffffff0000070

def z1120 : W := mkw 0x27601ea016802b00 0x04ec03d402d00560 0xafe01fe03f801f86 0xf5fc03fc07f003f0

def z1121 : W := mkw 0x8001415f00000000 0x1000282be0000000 0x0227e7ff80000003 0xc044fcfff0000000

def z1122 : W := mkw 0x80dfdfdf00000000 0x101bfbfbe0000000 0x823fffff80000003 0xd047fffff0000000

def z1123 : W := mkw 0x008a00000c22a2a9 0x8011400001845455 0xfddb181c5c63e3ff 0xffbb63038b8c7c7f

def z1124 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0027e3f380000001 0x8004fc7e70000000

def z1125 : W := mkw 0x87ffdfdf12000000 0x10fffbfbe2400000 0xa7ffffff9f800003 0xf4fffffff3f00000

def z1126 : W := mkw 0x81ffcbdf0c22a2a9 0x903ff97be1845455 0xfdfffbffdc63e3ff 0xffbfff7ffb8c7c7f

def z1127 : W := mkw 0x008b4155082280a9 0x8011682aa1045015 0x123fe7ff8063807b 0xc247fcfff00c700f

def z1128 : W := mkw 0x87ffdfdf08220000 0x10fffbfbe1044000 0xc7ffffffdc600003 0xf8fffffffb8c0000

def z1129 : W := mkw 0x00400a0004002200 0x0008014000800440 0xefe01fe05c006386 0xfdfc03fc0b800c70

def z1130 : W := mkw 0x37741eaa76d07b12 0x06ee83d54eda0f62 0xeffc1fffffe07f9f 0xfdff83fffffc0ff3

def z1131 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xeff81fec7fe07f9e 0xfdff03fd8ffc0ff3

def z1132 : W := mkw 0x08002020818d0d44 0x010004041031a1a8 0x30000000239f9c04 0x060000000473f380

def z1133 : W := mkw 0x27741eaa76807b00 0x04ee83d54ed00f60 0xfffc1fffffe07fff 0xffff83fffffc0fff

def z1134 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x85fffbff80000001 0xb0bfff7ff0000000

def z1135 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0xfffff8007fffe007 0xffffff000ffffc00

def z1136 : W := mkw 0xc7ffdfdf72500000 0x18fffbfbee4a0000 0x87ffffff80000003 0xf0fffffff0000000

def z1137 : W := mkw 0x38415ffb8484fff7 0x07082bff70909ffe 0x88001fff80007ffa 0x110003fff0000fff

def z1138 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x2227e7f3a39f9f83 0xc444fcfe7473f3f0

def z1139 : W := mkw 0x81ffcbdf00000000 0x103ff97be0000000 0x01e7e3e380000000 0xa03cfc7c70000000

def z1140 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x0224e7e380000002 0xc0449cfc70000000

def z1141 : W := mkw 0x8774decf00000000 0x10ee9bd9e0000000 0x8224fcef80000000 0x10449f9df0000000

def z1142 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xffdb1f1c7c63ffff 0xfffb63e38f8c7fff

def z1143 : W := mkw 0x8775dfdb00000000 0x10eebbfb60000000 0x87e7fff380000003 0xf0fcfffe70000000

def z1144 : W := mkw 0x87bfd5df00000000 0x10f7fabbe0000000 0x863ffcff80000003 0x50c7ff9ff0000000

def z1145 : W := mkw 0x48002020fbff0d44 0x090004041f7fe1a8 0x700000007fff9c04 0x0e0000000ffff380

def z1146 : W := mkw 0x1014140a80545456 0x02028281500a8a8a 0xdc1c1c1fc07c7c7f 0x5b838383f80f8f8f

def z1147 : W := mkw 0x48cb2b34ffffafed 0x891965669ffff5fd 0xfddb1b1c7fffffff 0xffbb63638fffffff

def z1148 : W := mkw 0x8735d5db00000000 0x10e6babb60000000 0x0224e7f380000002 0x00449cfe70000000

def z1149 : W := mkw 0x28412b30f78dffe5 0x050825661ef1bffc 0xfdc31b107f9fffe7 0xffb863620ff3fffc

def z1150 : W := mkw 0xa7ffdfdf16002200 0x14fffbfbe2c00440 0x87ffffff9c000003 0xf0fffffff3800000

def z1151 : W := mkw 0x00ca0a040c22a2a9 0x8019414081845455 0xfdd81b0c5c63e3fe 0xffbb03618b8c7c7f

def z1152 : W := mkw 0xc7ffdfdf7e722208 0x98fffbfbefce4441 0xc7ffffffdc60601b 0xf8fffffffb8c0c03

def z1153 : W := mkw 0x07bfc151082280a1 0x00f7f82a21045014 0x7fffe7f3dc6383e7 0xeffffcfe7b8c707c

def z1154 : W := mkw 0x0721415100000000 0x00e4282a20000000 0x07e7e7f380000003 0xe0fcfcfe70000000

def z1155 : W := mkw 0x4800202089ff8de5 0x09000404113ff1bc 0x3800000023ff9fe4 0x07000000047ff3fc

def z1156 : W := mkw 0x8774decb00000000 0x10ee9bd960000000 0x87fcffff80000003 0xf0ff9ffff0000000

def z1157 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x85fbffff80000002 0xb0bf7ffff0000000

def z1158 : W := mkw 0x89ebebf50dababa9 0x913d7d7ea1b57575 0x21e3e3e01f838380 0xa43c7c7c03f07070

def z1159 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xfffb1b1c7fe3e3ff 0xffff63638ffc7c7f

def z1160 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xfe3c1c1fe3fc7c7f 0xdfc78383fc7f8f8f

def z1161 : W := mkw 0x18002020edffffff 0x830004041dbfffff 0x780000007ffffffc 0x0f0000000fffffff

def z1162 : W := mkw 0x67beb4807b7b5000 0x0cf7d6900f6f6a00 0x77ffe0007fff8005 0xeefffc000ffff000

def z1163 : W := mkw 0x80dfcbdf00000000 0x101bf97be0000000 0x001fe3ff80000001 0x0003fc7ff0000000

def z1164 : W := mkw 0x0001555b00000000 0x00002aab60000000 0x8227ffff80000003 0xd044fffff0000000

def z1165 : W := mkw 0x57bea00a7b7b0012 0x0af7d4014f6f6002 0x77ffe00c7fff801d 0xeefffc018ffff003

def z1166 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0023e7f380000002 0x80047cfe70000000

def z1167 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0a27e7f3a0001c07 0xc144fcfe74000380

def z1168 : W := mkw 0x47aaa0007b7b0000 0x08f554000f6f6000 0x77e3e0007fff8004 0xeefc7c000ffff000

def z1169 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x67e7e0007f9f8004 0xecfcfc000ff3f000

def z1170 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x08000000239c1fe0 0x01000000047383fc

def z1171 : W := mkw 0x06401e2064807b00 0x00c803c40c900f60 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z1172 : W := mkw 0x81ffcbdf00000000 0x103ff97be0000000 0x85fffbff80000003 0xf0bfff7ff0000000

def z1173 : W := mkw 0x97ffdfdf00500012 0x12fffbfbe00a0002 0x87ffffff8060001b 0xf0fffffff00c0003

def z1174 : W := mkw 0x0615415160500000 0x00c2a82a2c0a0000 0x563fe7f3e07c0007 0xcac7fcfe7c0f8000

def z1175 : W := mkw 0x08ca2a248dafafed 0x8119454491b5f5fd 0xfdd8180c7ffffffc 0x3fbb03018fffffff

def z1176 : W := mkw 0x0000200001090000 0x0000040000212000 0x77e7e0007f9f8005 0xeefcfc000ff3f000

def z1177 : W := mkw 0x80415fdf00000000 0x10082bfbe0000000 0x8224ffff80000002 0x10449ffff0000000

def z1178 : W := mkw 0x3f3474ebf3dd5d56 0x07e68e9d7e7babaa 0x0224e4e3a39c1c00 0x00449c9c74738380

def z1179 : W := mkw 0x0720142072805900 0x00e402840e500b20 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z1180 : W := mkw 0x57bea0007b7b5012 0x0af7d4000f6f6a02 0x77ffe0007fffe01d 0xeefffc000ffffc03

def z1181 : W := mkw 0x489fe155897f84ed 0x8913fc2ab12ff09d 0x101fe01f807f8079 0x0203fc03f00ff00f

def z1182 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x33ffe0003fff8001 0xa67ffc0007fff000

def z1183 : W := mkw 0x0615555b00000000 0x00c2aaab60000000 0x0227e7f380000003 0xc044fcfe70000000

def z1184 : W := mkw 0x072155d100000000 0x00e42aba20000000 0x0227e7f380000003 0xc044fcfe70000000

def z1185 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xffdc1c1ffc7c7c7f 0xfffb8383ff8f8f8f

def z1186 : W := mkw 0x0001415100000000 0x0000282a20000000 0x0007e7f380000003 0x0000fcfe70000000

def z1187 : W := mkw 0x87bfd5df00000000 0x10f7fabbe0000000 0x0227e4e380000000 0x0044fc9c70000000

def z1188 : W := mkw 0x37741eaa76d07b12 0x06ee83d54eda0f62 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z1189 : W := mkw 0x80cb5fdf0c22a2a9 0x90196bfbe1845455 0xffffffffdc63e3ff 0xfffffffffb8c7c7f

def z1190 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3a27e7e3a39f9fe4 0x8744fcfc7473f3fc

def z1191 : W := mkw 0x472020007b7b0000 0x08e404000f6f6000 0x77e7e0007fff8005 0xeefcfc000ffff000

def z1192 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xfe1c1f1fe07c7fff 0xdfc383e3fc0f8fff

def z1193 : W := mkw 0x8774decb04002200 0x10ee9bd960800440 0xefe4ffe3dc006386 0xfdfc9ffc7b800c70

def z1194 : W := mkw 0x87fedecf00000000 0x10ffdbd9e0000000 0x87fffcef80000001 0xf0ffff9df0000000

def z1195 : W := mkw 0x8774decb00000000 0x10ee9bd960000000 0x03e4e7e380000000 0xa07c9cfc70000000

def z1196 : W := mkw 0x87bed4cf00000000 0x10f7da99e0000000 0x023ce4ef80000000 0x00479c9df0000000

def z1197 : W := mkw 0x0601555100000000 0x00c02aaa20000000 0x8627fff380000003 0xd0c4fffe70000000

def z1198 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xa7e01fe03f801f82 0xf4fc03fc07f003f0

def z1199 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x27ffe0003f9f8001 0xe4fffc0007f3f000

def z1200 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x87fffcff80000001 0x30ffff9ff0000000

def z1201 : W := mkw 0x87bfd5db00000000 0x10f7fabb60000000 0x07ffe7f380000003 0xe0fffcfe70000000

def z1202 : W := mkw 0x67749ea076d07b00 0x0cee93d40eda0f60 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z1203 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xfff81fe07fe07f87 0xffff03fc0ffc0ff0

def z1204 : W := mkw 0x008b415500000000 0x0011682aa0000000 0x023fe7ff80000003 0xc047fcfff0000000

def z1205 : W := mkw 0x87ffdfdf082280a9 0x90fffbfbe1045015 0xdfffffffc063e07f 0xfbfffffff80c7c0f

def z1206 : W := mkw 0x21601ea016807b00 0x042c03d402d00f60 0xede01fe05f807f86 0xfdbc03fc0bf00ff0

def z1207 : W := mkw 0x0001415100000000 0x0000282a20000000 0x1227e7f3a01c0007 0xc244fcfe74038000

def z1208 : W := mkw 0x1000140a80045456 0x0200028150008a8a 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z1209 : W := mkw 0x27600aa076802b00 0x04ec01540ed00560 0x6fe007e07f801f86 0xedfc00fc0ff003f0

def z1210 : W := mkw 0xe7fe9e8e7e727200 0x1cffd3d1cfce4e40 0xc5d8180c5c606000 0x38bb03018b8c0c00

def z1211 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0x00000000201c1c00 0x0000000004038380

def z1212 : W := mkw 0x00414b550400a2a9 0x8008296aa0801455 0x88001fff800063fa 0x110003fff0000c7f

def z1213 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x7e3fe7f3e3ff9fe7 0xcfc7fcfe7c7ff3fc

def z1214 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x7fffe4007fff9c07 0xeffffc800ffff380

def z1215 : W := mkw 0x21601ea016807b00 0x042c03d402d00f60 0xabe01fe03f807f86 0xf57c03fc07f00ff0

def z1216 : W := mkw 0x8734d4cb60005000 0x10e69a996c000a00 0xce24fce3e0007c06 0x59c49f9c7c000f80

def z1217 : W := mkw 0x08002020858dafed 0x8100040410b1b5fd 0x38000000239ffffc 0x070000000473ffff

def z1218 : W := mkw 0x8120c0c100000000 0x1024181820000000 0x0224e4e380000000 0x00449c9c70000000

def z1219 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3a3fe7ffa3ff9fff 0xc747fcfff47ff3ff

def z1220 : W := mkw 0x87ffdfdf000080a1 0x10fffbfbe0001014 0x97ffffff80038063 0xf2fffffff000700c

def z1221 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0xde3cfcffc060607f 0x5bc79f9ff80c0c0f

def z1222 : W := mkw 0x41bea0007b7b0000 0x0837d4000f6f6000 0x71ffe0007fff8005 0xae3ffc000ffff000

def z1223 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xafffffff9c03e3fb 0xf5fffffff3807c7f

def z1224 : W := mkw 0x47bea0007b7b0000 0x08f7d4000f6f6000 0x73e7e0007fff8004 0xae7cfc000ffff000

def z1225 : W := mkw 0x18cb2b34edffffff 0x831965669dbfffff 0xfddb1b1c7fffffff 0xffbb63638fffffff

def z1226 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x8fffffff8000607b 0xf1fffffff0000c0f

def z1227 : W := mkw 0x809fd5df00000000 0x1013fabbe0000000 0x001fe4ff80000001 0x0003fc9ff0000000

def z1228 : W := mkw 0x0735c15100000000 0x00e6b82a20000000 0x0227e7f380000003 0xc044fcfe70000000

def z1229 : W := mkw 0x1014140a80545456 0x02028281500a8a8a 0x9a1c1c1fa07c7c7f 0x53438383f40f8f8f

def z1230 : W := mkw 0x41aaa0001b7b0000 0x08355400036f6000 0x31e3e0001fff8000 0xa63c7c0003fff000

def z1231 : W := mkw 0x00cb0b140c22a2a9 0x8019616281845455 0xfddb181c5c63e3fd 0x3fbb63038b8c7c7f

def z1232 : W := mkw 0x08012130818d8de5 0x010024261031b1bc 0x38000310239f9fe6 0x070000620473f3fc

def z1233 : W := mkw 0x08412b34858dafed 0x8108256690b1b5fd 0xb8001b1c239ffffe 0x170003638473ffff

def z1234 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xd7ffffffdc63e07b 0xfafffffffb8c7c0f

def z1235 : W := mkw 0x1614140a80545456 0x02c28281500a8a8a 0x9e1c1c1f807c7c7b 0x53c38383f00f8f8f

def z1236 : W := mkw 0x28002020858dffe5 0x0500040410b1bffc 0x38000000239fffe4 0x070000000473fffc

def z1237 : W := mkw 0x80cb5fdf00000000 0x10196bfbe0000000 0x87ffffff80000003 0xf0fffffff0000000

def z1238 : W := mkw 0xd7ffdfdf7a725012 0x1afffbfbef4e4a02 0xc7ffffffdc60601b 0xf8fffffffb8c0c03

def z1239 : W := mkw 0x47beb4007b7b5000 0x08f7d6800f6f6a00 0xf7fff8007fffe005 0xfeffff000ffffc00

def z1240 : W := mkw 0x008a000008220000 0x0011400001044000 0x77ffe0005c638005 0xeefffc000b8c7000

def z1241 : W := mkw 0x18002020e1ddddf7 0x030004041c3bbbbe 0x38000000239f9fe4 0x070000000473f3fc

def z1242 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x063ce4e380000001 0x40c79c9c70000000

def z1243 : W := mkw 0x28415ff58484ffed 0x85082bfeb0909ffd 0x88001fff80007ffa 0x110003fff0000fff

def z1244 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xfe1f1c1fe07ffc7f 0xdfc3e383fc0fff8f

def z1245 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xffe41fe07f9c7f87 0xfffc83fc0ff38ff0

def z1246 : W := mkw 0x41aaa0007b7b0000 0x083554000f6f6000 0x73e7e0007fff8005 0xee7cfc000ffff000

def z1247 : W := mkw 0x008b4155082280a9 0x8011682aa1045015 0x101fe01f80638079 0x0203fc03f00c700f

def z1248 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x7a27e7f3e3ffffff 0xcf44fcfe7c7fffff

def z1249 : W := mkw 0x87ffdfdf082280a9 0x90fffbfbe1045015 0x87ffffff80038003 0xf0fffffff0007000

def z1250 : W := mkw 0x27601ea016807b00 0x04ec03d402d00f60 0xafe01fe01f807f82 0xf5fc03fc03f00ff0

def z1251 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x0224e4f380000003 0x40449c9e70000000

def z1252 : W := mkw 0x81ebdfdf0c22a2a9 0x903d7bfbe1845455 0xa9e3ffff9c03e3fa 0xb53c7ffff3807c7f

def z1253 : W := mkw 0x21600aa076807b00 0x042c01540ed00f60 0x21e003e03f801f80 0xa43c007c07f003f0

def z1254 : W := mkw 0x00ca0a040c22a2a9 0x8019414081845455 0xfdd8181c5c63e3ff 0x7fbb03038b8c7c7f

def z1255 : W := mkw 0x80dfdfdf0c22a2a9 0x901bfbfbe1845455 0x981fffff8063e3fb 0x1303fffff00c7c7f

def z1256 : W := mkw 0x87ffdfdf6c22f2a9 0x90fffbfbed845e55 0xfffffffffc63ffff 0xffffffffff8c7fff

def z1257 : W := mkw 0x1014140ae0545456 0x020282815c0a8a8a 0xd81c1c1fe07c7c7f 0x1b038383fc0f8f8f

def z1258 : W := mkw 0x8775dfdf0400a2a9 0x90eebbfbe0801455 0x8a24ffff800063fa 0x11449ffff0000c7f

def z1259 : W := mkw 0x87bfd5df00000000 0x10f7fabbe0000000 0x023fe7ff80000003 0xc047fcfff0000000

def z1260 : W := mkw 0x21601ea076807b00 0x042c03d40ed00f60 0xe9e01fe07f807f86 0xbd3c03fc0ff00ff0

def z1261 : W := mkw 0x29eb6bf51fababa9 0x853d6d7ea3f57575 0x21e3e3e01f838380 0xa43c7c7c03f07070

def z1262 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xdc1c1c1fc07c7c7b 0x1b838383f80f8f8f

def z1263 : W := mkw 0x87ffdfdf60005000 0x10fffbfbec000a00 0xdfffffffe0607c7f 0xfbfffffffc0c0f8f

def z1264 : W := mkw 0xc7bed4cb7a720000 0x18f7da996f4e4000 0x47fce4e3dc600000 0x28ff9c9c7b8c0000

def z1265 : W := mkw 0xa7ffdfdf04007200 0x14fffbfbe0800e40 0x87ffffff80006003 0xf0fffffff0000c00

def z1266 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x10000000239f9c60 0x020000000473f38c

def z1267 : W := mkw 0x008b415108220000 0x0011682a21044000 0x77ffe7f3dc638007 0xeefffcfe7b8c7000

def z1268 : W := mkw 0x9734d4cb60505012 0x12e69a996c0a0a02 0xc63cfcefc0606018 0x18c79f9df80c0c03

def z1269 : W := mkw 0x8120d4cb00000000 0x10241a9960000000 0x0020e4e380000000 0x00041c9c70000000

def z1270 : W := mkw 0x1734140ae0545456 0x02e682815c0a8a8a 0xdffc1c1fe07c7c7f 0xfbff8383fc0f8f8f

def z1271 : W := mkw 0x8734d4cb72000000 0x10e69a996e400000 0x0224e4e3a3800000 0x00449c9c74700000

def z1272 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xb7ffffff80038007 0xf6fffffff0007000

def z1273 : W := mkw 0x272014a072805900 0x04e402940e500b20 0x0000000023801c00 0x0000000004700380

def z1274 : W := mkw 0x06140000e0540444 0x00c280001c0a8088 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z1275 : W := mkw 0x20401ea004807b00 0x040803d400900f60 0xefe01fe07f807f86 0xfdfc03fc0ff00ff0

def z1276 : W := mkw 0x8775dfdf00000000 0x10eebbfbe0000000 0x8227ffff80000003 0xd044fffff0000000

def z1277 : W := mkw 0x8121c1d100000000 0x1024383a20000000 0x0227e7f380000003 0xc044fcfe70000000

def z1278 : W := mkw 0x87ffdfdf082280a9 0x90fffbfbe1045015 0xf7ffffffdc63807f 0xfefffffffb8c700f

def z1279 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x3227e7f3a39f9fe1 0x8644fcfe7473f3fc

def z1280 : W := mkw 0xc89fe15f897f84e5 0x1913fc2bf12ff09c 0x101fe01f807f8061 0x0203fc03f00ff00c

def z1281 : W := mkw 0xa734d4cb72005000 0x14e69a996e400a00 0x0224e4e380000000 0x00449c9c70000000

def z1282 : W := mkw 0x1614140af2545456 0x02c282815e4a8a8a 0xfe1c1c1ffffc7c7f 0x5fc38383ffff8f8f

def z1283 : W := mkw 0x57beb40a7b7b5012 0x0af7d6814f6f6a02 0xfffff81c7fffe07f 0xffffff038ffffc0f

def z1284 : W := mkw 0x4734a00073590000 0x08e694000e6b2000 0x00000000239c0000 0x0000000004738000

def z1285 : W := mkw 0x47beb4007b7b5000 0x08f7d6800f6f6a00 0xfffffc1c7ffffc7f 0xffffff838fffff8f

def z1286 : W := mkw 0x1734140af2545456 0x02e682815e4a8a8a 0xde3c1c1fe3fc7c7f 0x5bc78383fc7f8f8f

def z1287 : W := mkw 0x38002020f7ddfff7 0x070004041efbbffe 0x780000007ffffffc 0x0f0000000fffffff

def z1288 : W := mkw 0xa7ffdfdf76007200 0x14fffbfbeec00e40 0xe7ffffffff806007 0xfcfffffffff00c00

def z1289 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x85dfffff80000003 0x30bbfffff0000000

def z1290 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x07e4e4e380000000 0xe0fc9c9c70000000

def z1291 : W := mkw 0x87ffdfdf0c222208 0x90fffbfbe1844441 0xf7ffffffdc63e01f 0xfefffffffb8c7c03

def z1292 : W := mkw 0x9734d4cb60505012 0x12e69a996c0a0a02 0x0224e4e380000000 0x00449c9c70000000

def z1293 : W := mkw 0x07bea00073090000 0x00f7d4000e612000 0x77ffe0007f9f8005 0xeefffc000ff3f000

def z1294 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0xa7ffffffa3800007 0xf4fffffff4700000

def z1295 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x2800000003839fe0 0x05000000007073fc

def z1296 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xede01fe05f807f82 0xbdbc03fc0bf00ff0

def z1297 : W := mkw 0x80dfdfdf0c22a2a9 0x901bfbfbe1845455 0xfddfffffdc63e3ff 0xffbbfffffb8c7c7f

def z1298 : W := mkw 0x47beb40a7b7b0000 0x08f7d6814f6f6000 0xf7fff80c7fff8005 0xfeffff018ffff000

def z1299 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x18000000001f9fe0 0x030000000003f3fc

def z1300 : W := mkw 0x08002020818d8de5 0x010004041031b1bc 0x3a040000239f9fe5 0x474080000473f3fc

def z1301 : W := mkw 0x0001415100000000 0x0000282a20000000 0xde3fffffc060607f 0xdbc7fffff80c0c0f

def z1302 : W := mkw 0xc7ffdfdf1a220000 0x18fffbfbe3444000 0x87ffffff9c000003 0xf0fffffff3800000

def z1303 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x87e7ffe380000002 0xf0fcfffc70000000

def z1304 : W := mkw 0x87ffdfdf0400a2a9 0x90fffbfbe0801455 0xefffffffdc0063ff 0xfdfffffffb800c7f

def z1305 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xabe01fe03f807f82 0xb57c03fc07f00ff0

def z1306 : W := mkw 0x08016171818d8de5 0x01002c2e3031b1bc 0x1a27e7f3a39f9fe3 0x0344fcfe7473f3fc

def z1307 : W := mkw 0x87ffdfdf08220000 0x10fffbfbe1044000 0x97ffffff80638003 0xf2fffffff00c7000

def z1308 : W := mkw 0x27601ea476807b08 0x84ec03d48ed00f61 0xefe01fec7f807f9e 0xfdfc03fd8ff00ff3

def z1309 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xefe01ffc7f807ffe 0xfdfc03ff8ff00fff

def z1310 : W := mkw 0x87ffdfdf60005000 0x10fffbfbec000a00 0x87ffffffa0001c03 0xf0fffffff4000380

def z1311 : W := mkw 0x28414bf18484afe5 0x0508297e309095fc 0x080007f380001fe2 0x010000fe700003fc

def z1312 : W := mkw 0x088b213489af8ded 0x811164269135f1bd 0x381b001c23ff9ffd 0x07036003847ff3ff

def z1313 : W := mkw 0x47bea0001b2b0000 0x08f7d40003656000 0x37ffe0003f9f8005 0xe6fffc0007f3f000

def z1314 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xce1c1c1fe07c7c7a 0x19c38383fc0f8f8f

def z1315 : W := mkw 0x5734940af2545456 0x0ae692815e4a8a8a 0xde1c1c1fe07c7c7f 0x5bc38383fc0f8f8f

def z1316 : W := mkw 0x06df5f5f00000000 0x00dbebebe0000000 0x87ffffff80000003 0xf0fffffff0000000

def z1317 : W := mkw 0x87ffdfdf000080a1 0x10fffbfbe0001014 0x8fffffff800003e3 0xf1fffffff000007c

def z1318 : W := mkw 0x41bea0001b7b0000 0x0837d400036f6000 0x21e7e0001f9f8000 0xa43cfc0003f3f000

def z1319 : W := mkw 0x8734d4cb72000000 0x10e69a996e400000 0x67e4e4e3ff800004 0xecfc9c9c7ff00000

def z1320 : W := mkw 0x08002020818d0d44 0x010004041031a1a8 0x18000000239c1c64 0x030000000473838c

def z1321 : W := mkw 0x21600aa076807b00 0x042c01540ed00f60 0x6be007e07f807f86 0xed7c00fc0ff00ff0

def z1322 : W := mkw 0x87bed4cb00000000 0x10f7da9960000000 0x023fe4e380000001 0x0047fc9c70000000

def z1323 : W := mkw 0x00ca0a000c222200 0x0019414001844440 0xfddb1b1c5c63e3ff 0xffbb63638b8c7c7f

def z1324 : W := mkw 0x00400a2004802b00 0x0008014400900560 0x2be007e03f801f86 0xe57c00fc07f003f0

def z1325 : W := mkw 0x87bed4cb00000000 0x10f7da9960000000 0x87fffcff80000003 0xf0ffff9ff0000000

def z1326 : W := mkw 0x488b2130fbff8de5 0x091164261f7ff1bc 0x7ddb03107fff9fe7 0xefbb60620ffff3fc

def z1327 : W := mkw 0x87ffdfdf00000000 0x10fffbfbe0000000 0x03ffe7ff80000001 0xa07ffcfff0000000

def z1328 : W := mkw 0x27601ea076807b00 0x04ec03d40ed00f60 0xe7e01fe07f807f80 0xbcfc03fc0ff00ff0

def z1329 : W := mkw 0x47beb4007b7b5000 0x08f7d6800f6f6a00 0x77ffe4007fff9c05 0xeefffc800ffff380

def z1330 : W := mkw 0x16df5f5fec76f6ff 0x82dbebebfd8ededf 0xfffffffffc7fffff 0xffffffffff8fffff

def z1331 : W := mkw 0x86dfdfdf00000000 0x10dbfbfbe0000000 0x861fffff80000003 0x50c3fffff0000000

def z1332 : W := mkw 0x87ffdfdf04002200 0x10fffbfbe0800440 0x8fffffff80006383 0xf1fffffff0000c70

def z1333 : W := mkw 0x87ffdfdf7a220000 0x10fffbfbef444000 0xf7ffffffffe38007 0xfefffffffffc7000

def z1334 : W := mkw 0x409ea000097b0000 0x0813d400012f6000 0x77ffe0007fff8005 0xeefffc000ffff000

def z1335 : W := mkw 0x87bfc15f00000000 0x10f7f82be0000000 0x07ffe7ff80000003 0xe0fffcfff0000000

def z1336 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x863cfcef80000000 0x10c79f9df0000000

def z1337 : W := mkw 0x1614140ae0545456 0x02c282815c0a8a8a 0xd61c1c1fe07c7c79 0x1ac38383fc0f8f8f

def z1338 : W := mkw 0x87ffdfdf0c22a2a9 0x90fffbfbe1845455 0xcfffffffdc6063fb 0xf9fffffffb8c0c7f

def z1339 : W := mkw 0x488be151892f84e5 0x09117c2a3125f09c 0x1007e013801f8061 0x0200fc027003f00c

def z1340 : W := mkw 0x8734d4cb60500000 0x10e69a996c0a0000 0x0224e4e3a01c0000 0x00449c9c74038000

def z1341 : W := mkw 0x809fc15f082280a9 0x9013f82be1045015 0x3a3fe7ff806383ff 0xc747fcfff00c707f

def z1342 : W := mkw 0x00414b550400a2a9 0x8008296aa0801455 0x8a27ffff800063fb 0xd144fffff0000c7f

def z1343 : W := mkw 0x8734d4cb00000000 0x10e69a9960000000 0x8224fcff80000002 0x10449f9ff0000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z8,z4,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z6]),(0,[z1,z2,z10,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z5,z12,z13])],[(0,[z14,z1,z2,z3,z4,z5,z6]),(0,[z15,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z16]),(0,[z1,z17,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z6])],[(1,[z1,z2,z19,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z20]),(0,[z1,z2,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z22,z5,z6]),(0,[z23,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z25,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z6,z27]),(0,[z1,z2,z28,z3,z4,z5,z6]),(0,[z29,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z30,z4,z5,z31]),(0,[z1,z32,z2,z3,z4,z5,z6])],[(0,[z33,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z5,z26]),(0,[z1,z2,z3,z4,z35,z5,z6]),(0,[z1,z2,z36,z3,z4,z5,z6]),(0,[z37,z1,z17,z2,z3,z4,z5])],[(0,[z38,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z40,z5,z6]),(0,[z41,z1,z17,z2,z3,z4,z5]),(0,[z1,z42,z2,z3,z4,z5,z6]),(0,[z43,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z2,z3,z4,z5,z6,z45])],[(0,[z1,z2,z46,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z26,z48]),(0,[z1,z2,z3,z4,z5,z49,z26]),(0,[z1,z2,z3,z4,z50,z5,z6])],[(0,[z51,z1,z52,z2,z3,z4,z6]),(0,[z1,z53,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z54,z6])],[(0,[z55,z1,z2,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z56,z5,z6]),(0,[z57,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z58]),(0,[z1,z2,z3,z4,z5,z59,z6]),(0,[z1,z60,z2,z3,z4,z61,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z62,z26]),(0,[z63,z1,z2,z3,z30,z4,z5]),(0,[z1,z64,z2,z3,z4,z5,z6]),(1,[z1,z2,z65,z3,z4,z5]),(0,[z1,z2,z3,z4,z66,z5,z6]),(0,[z1,z2,z3,z4,z67,z5,z6]),(0,[z1,z68,z2,z3,z4,z5,z58])],[(0,[z69,z70,z2,z3,z4,z5,z6]),(0,[z1,z3,z30,z4,z34,z5,z6]),(0,[z37,z1,z2,z3,z4,z62,z6])],[(0,[z71,z1,z72,z3,z4,z5,z6]),(0,[z1,z73,z2,z3,z4,z5,z6]),(0,[z74,z69,z1,z2,z3,z5,z6]),(0,[z1,z2,z75,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z76,z6]),(0,[z1,z77,z2,z4,z78,z5,z6]),(0,[z1,z2,z79,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z80])],[(0,[z63,z55,z1,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z81]),(0,[z1,z2,z3,z4,z61,z5,z24]),(0,[z1,z2,z3,z4,z82,z5,z6]),(0,[z1,z83,z2,z3,z4,z5,z6]),(0,[z1,z52,z2,z3,z4,z62,z6]),(1,[z84,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z85,z5,z6])],[(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z87,z62,z6]),(0,[z1,z2,z3,z4,z5,z88,z6]),(0,[z1,z89,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z56,z6]),(0,[z1,z17,z2,z3,z90,z4,z5]),(0,[z1,z2,z91,z3,z4,z5,z6]),(0,[z1,z2,z3,z92,z78,z5,z6]),(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z93]),(0,[z1,z2,z3,z4,z5,z6,z94]),(0,[z95,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z96,z6]),(0,[z97,z1,z17,z2,z3,z4,z5]),(0,[z1,z17,z2,z3,z98,z4,z5]),(0,[z1,z2,z3,z4,z5,z99,z100])]],
   [[(1,[z1,z2,z3,z4,z5,z6]),(1,[z1,z101,z2,z3,z4,z5]),(0,[z102,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z103,z6]),(0,[z2,z3,z104,z4,z92,z5,z6]),(0,[z105,z1,z2,z3,z4,z5,z6])],[(0,[z69,z1,z2,z3,z4,z5,z24]),(0,[z106,z1,z2,z3,z4,z5,z6]),(2,[z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z107,z6])],[(0,[z1,z72,z3,z9,z4,z5,z6]),(0,[z1,z2,z3,z108,z4,z5,z6]),(0,[z1,z2,z109,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z110,z6]),(0,[z1,z2,z3,z4,z5,z6,z111]),(0,[z1,z60,z2,z3,z4,z6,z112])],[(0,[z1,z2,z113,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z115,z87,z6]),(0,[z1,z2,z3,z4,z5,z6,z116]),(0,[z37,z1,z68,z2,z3,z4,z6]),(0,[z1,z117,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z118,z5,z6])],[(0,[z1,z2,z3,z4,z5,z119,z6]),(1,[z1,z2,z3,z4,z5,z120]),(0,[z1,z2,z3,z4,z121,z5,z122])],[(0,[z1,z2,z123,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z124])],[(0,[z1,z2,z3,z4,z5,z6,z125]),(0,[z1,z2,z3,z126,z4,z5,z6]),(0,[z1,z127,z2,z3,z4,z5,z6]),(0,[z1,z128,z2,z3,z129,z5,z6]),(1,[z1,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z130,z4,z5,z6])],[(0,[z131,z1,z17,z2,z3,z4,z5]),(0,[z1,z132,z2,z3,z4,z5,z6]),(0,[z1,z133,z2,z3,z4,z5,z26]),(0,[z63,z1,z2,z3,z4,z121,z5]),(0,[z1,z2,z3,z4,z134,z5,z6]),(0,[z1,z2,z3,z4,z61,z5,z6])]],
   [[(0,[z135,z1,z2,z3,z4,z5,z6]),(0,[z37,z1,z2,z3,z136,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z137]),(0,[z1,z2,z138,z3,z78,z5,z6])],[(0,[z1,z2,z3,z4,z5,z139,z6]),(1,[z74,z1,z3,z34,z5,z6]),(1,[z63,z140,z2,z3,z4,z5]),(0,[z1,z17,z2,z141,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z12,z49]),(0,[z1,z68,z2,z3,z4,z5,z142])],[(0,[z143,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z144,z5,z6]),(1,[z1,z145,z3,z4,z5,z6]),(0,[z2,z146,z3,z90,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z147]),(0,[z1,z52,z2,z3,z136,z4,z6]),(0,[z148,z63,z1,z2,z3,z4,z5]),(0,[z1,z17,z2,z3,z149,z4,z5]),(0,[z1,z17,z2,z3,z4,z5,z150]),(0,[z1,z17,z2,z3,z4,z5,z112]),(0,[z1,z2,z3,z151,z4,z5,z6]),(0,[z1,z2,z3,z4,z152,z5,z6])],[(0,[z153,z1,z2,z3,z4,z5,z6]),(0,[z131,z63,z1,z2,z3,z4,z5]),(0,[z41,z154,z1,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6]),(0,[z1,z156,z2,z3,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z5,z26]),(0,[z157,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z4,z5,z6])],[(0,[z1,z159,z2,z47,z3,z4,z5]),(0,[z41,z1,z2,z3,z4,z5,z26]),(0,[z63,z1,z77,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z160,z5,z6])],[(0,[z63,z1,z72,z2,z3,z4,z5]),(0,[z69,z1,z2,z3,z4,z5,z6]),(0,[z1,z52,z2,z3,z4,z5,z26]),(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z162,z5,z6]),(0,[z1,z2,z3,z4,z163,z5,z6]),(0,[z63,z84,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z164,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z18]),(0,[z1,z2,z165,z3,z4,z62,z6])],[(0,[z166,z1,z2,z3,z4,z5,z26]),(0,[z1,z167,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z168,z24]),(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z170,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z61,z12])],[(0,[z55,z1,z2,z3,z4,z5,z171]),(0,[z154,z1,z172,z2,z4,z5,z6]),(0,[z173,z1,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z2,z3,z4,z5]),(0,[z1,z174,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z175]),(0,[z1,z2,z176,z3,z4,z5,z6])]],
   [[(0,[z1,z177,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z178,z6]),(0,[z1,z179,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z180,z6]),(0,[z1,z2,z3,z4,z5,z6,z181])],[(0,[z1,z2,z182,z3,z4,z5,z6]),(0,[z1,z172,z2,z10,z4,z5,z6]),(0,[z1,z2,z183,z3,z4,z5,z6]),(0,[z1,z184,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z92,z5,z26]),(0,[z1,z2,z3,z4,z34,z5,z24]),(0,[z185,z1,z2,z3,z4,z5,z24]),(0,[z1,z186,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z187,z6]),(0,[z1,z2,z3,z4,z5,z6,z188])],[(0,[z189,z1,z2,z3,z4,z5,z6]),(0,[z190,z63,z1,z2,z3,z4,z5]),(0,[z191,z1,z17,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z192,z5,z6]),(0,[z193,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z194,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z24]),(0,[z1,z133,z2,z3,z4,z195,z6]),(1,[z1,z2,z3,z4,z5,z58])],[(1,[z1,z159,z2,z3,z4,z5]),(1,[z69,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z104,z78,z5,z6]),(0,[z1,z53,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z24,z196]),(0,[z63,z1,z53,z2,z3,z4,z5]),(1,[z1,z2,z3,z197,z5,z6]),(0,[z1,z2,z141,z3,z4,z5,z99])],[(0,[z1,z2,z3,z198,z4,z5,z6]),(0,[z199,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z200,z6]),(1,[z1,z53,z2,z4,z62,z6])],[(0,[z1,z2,z3,z4,z201,z5,z6]),(0,[z1,z2,z3,z4,z202,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z24]),(0,[z1,z2,z3,z4,z203,z5,z24]),(0,[z1,z60,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z204,z6]),(0,[z1,z2,z205,z3,z4,z5,z6]),(0,[z1,z2,z3,z206,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z99]),(0,[z1,z68,z2,z207,z4,z5,z6])]],
   [[(0,[z63,z70,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z208,z4,z5,z6]),(0,[z63,z1,z84,z2,z3,z4,z5]),(1,[z140,z2,z3,z4,z5,z6]),(0,[z1,z68,z2,z3,z5,z18,z6])],[(0,[z1,z17,z2,z3,z4,z115,z5]),(0,[z1,z209,z2,z3,z4,z5,z6]),(0,[z210,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z39]),(0,[z1,z2,z211,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z168,z6]),(0,[z166,z1,z2,z3,z4,z5,z212]),(0,[z1,z2,z3,z4,z5,z213,z24]),(0,[z1,z2,z3,z4,z5,z6,z214]),(0,[z1,z172,z2,z9,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z121,z6]),(0,[z1,z2,z3,z4,z5,z6,z215]),(0,[z1,z2,z3,z4,z216,z5,z6]),(0,[z1,z2,z138,z3,z217,z5,z6]),(0,[z1,z2,z218,z3,z4,z5,z6]),(0,[z1,z2,z219,z3,z4,z5,z6])],[(0,[z1,z128,z2,z3,z78,z5,z6]),(0,[z1,z220,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z61,z12,z6])],[(0,[z221,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z222]),(0,[z1,z52,z2,z3,z4,z121,z6]),(0,[z1,z2,z3,z4,z5,z6,z223]),(0,[z1,z2,z3,z136,z4,z18,z6])],[(0,[z1,z2,z3,z25,z4,z5,z6]),(0,[z1,z2,z224,z3,z4,z5,z6]),(0,[z225,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z226,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z34,z5,z6]),(0,[z1,z227,z2,z3,z4,z5,z100])],[(0,[z131,z1,z2,z3,z4,z5,z26]),(0,[z63,z1,z2,z3,z90,z4,z5]),(0,[z1,z228,z2,z3,z4,z5,z6]),(0,[z1,z2,z165,z3,z4,z5,z26]),(0,[z1,z2,z229,z3,z4,z5,z6]),(0,[z1,z77,z2,z3,z4,z230,z6]),(0,[z1,z2,z3,z98,z78,z5,z6]),(0,[z1,z2,z3,z4,z5,z231,z6])]],
   [[(0,[z1,z2,z19,z47,z4,z5,z6]),(0,[z1,z2,z232,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z6,z233]),(0,[z234,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z98,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z80]),(0,[z1,z2,z3,z4,z129,z62,z6]),(0,[z1,z133,z2,z3,z235,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z6]),(0,[z1,z133,z2,z4,z5,z6,z99]),(0,[z1,z2,z3,z4,z61,z5,z112])],[(0,[z1,z2,z3,z4,z5,z6,z81]),(0,[z1,z17,z2,z3,z4,z236,z5]),(0,[z1,z2,z3,z149,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z237]),(0,[z1,z2,z4,z78,z5,z62,z6])],[(0,[z37,z1,z3,z4,z5,z147,z6]),(0,[z1,z52,z3,z4,z121,z5,z6]),(0,[z1,z227,z17,z2,z3,z4,z5]),(0,[z1,z238,z2,z3,z4,z5,z6])],[(0,[z63,z23,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z203,z5,z6]),(0,[z1,z239,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z62,z6]),(0,[z1,z2,z3,z98,z4,z5,z100])],[(0,[z131,z1,z2,z3,z4,z5,z240]),(0,[z131,z1,z172,z2,z4,z5,z6]),(0,[z241,z1,z2,z3,z4,z5,z6]),(0,[z1,z242,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z243,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z244,z6]),(0,[z1,z2,z3,z4,z121,z5,z245]),(0,[z1,z2,z3,z4,z246,z5,z6])],[(0,[z1,z2,z3,z4,z5,z213,z6]),(0,[z1,z133,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z247,z6]),(0,[z1,z248,z2,z3,z4,z5,z6]),(0,[z1,z239,z2,z3,z5,z147,z6]),(0,[z1,z17,z2,z3,z4,z78,z5]),(0,[z249,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z171])]],
   [[(0,[z1,z2,z3,z4,z250,z5,z6]),(0,[z1,z2,z3,z4,z230,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z251]),(0,[z1,z2,z3,z4,z252,z5,z6])],[(0,[z1,z2,z3,z4,z253,z5,z6]),(0,[z1,z2,z3,z4,z254,z5,z6]),(0,[z1,z255,z2,z3,z4,z5,z24]),(1,[z1,z2,z3,z4,z256,z6]),(0,[z1,z2,z3,z4,z257,z5,z6]),(0,[z1,z53,z2,z4,z5,z62,z6]),(0,[z1,z258,z2,z3,z4,z5,z6])],[(0,[z63,z1,z2,z47,z3,z4,z5]),(0,[z37,z1,z2,z3,z4,z5,z24]),(0,[z1,z17,z2,z10,z3,z4,z5]),(0,[z63,z140,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z141,z3,z4,z5]),(0,[z1,z17,z2,z3,z4,z5,z13])],[(0,[z1,z101,z2,z47,z3,z4,z5]),(0,[z1,z259,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z260,z4,z5,z24]),(0,[z1,z2,z261,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z262,z5,z6]),(0,[z263,z63,z1,z2,z3,z4,z5]),(0,[z63,z1,z2,z3,z4,z5,z112]),(0,[z1,z2,z3,z136,z129,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z264])],[(0,[z131,z1,z2,z3,z4,z265,z6]),(0,[z266,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z267,z3,z4,z5,z6]),(0,[z1,z52,z2,z3,z4,z5,z24]),(0,[z1,z17,z52,z2,z3,z4,z5]),(0,[z268,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z269,z4,z5,z6]),(0,[z270,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z150,z26]),(0,[z1,z2,z3,z4,z5,z271,z6]),(0,[z1,z128,z2,z3,z217,z5,z6]),(0,[z1,z2,z3,z4,z5,z272,z6]),(0,[z140,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z273]),(0,[z1,z2,z3,z4,z5,z12,z100])],[(1,[z1,z2,z3,z5,z274,z6]),(0,[z1,z2,z3,z4,z5,z274,z6]),(0,[z63,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z275,z3,z4,z5,z6])],[(0,[z1,z276,z2,z3,z4,z34,z6]),(0,[z1,z277,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z278,z5,z6]),(0,[z1,z2,z3,z4,z5,z279,z6]),(0,[z63,z1,z2,z2,z3,z4,z5]),(0,[z1,z280,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z92,z5,z24]),(0,[z1,z2,z3,z281,z4,z5,z6]),(0,[z74,z1,z2,z3,z4,z5,z6]),(0,[z74,z1,z2,z3,z30,z5,z6]),(0,[z1,z2,z3,z282,z4,z5,z6]),(0,[z1,z2,z3,z98,z217,z5,z6])],[(0,[z131,z1,z283,z3,z4,z5,z6]),(0,[z1,z2,z3,z217,z92,z5,z6]),(0,[z1,z2,z3,z4,z115,z284,z6]),(0,[z1,z2,z3,z4,z129,z5,z26]),(0,[z1,z2,z3,z4,z5,z285,z26]),(0,[z286,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z287,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z288,z6]),(0,[z1,z2,z3,z4,z5,z289,z6]),(0,[z1,z2,z3,z290,z4,z5,z6]),(1,[z1,z2,z207,z4,z5,z6])],[],[(0,[z154,z1,z17,z2,z3,z4,z5]),(0,[z1,z255,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z92,z5,z6]),(1,[z1,z2,z3,z291,z4,z5]),(0,[z1,z2,z3,z4,z292,z5,z6]),(0,[z1,z2,z3,z4,z293,z5,z6])],[(0,[z1,z2,z3,z4,z5,z26,z16]),(0,[z37,z1,z2,z3,z4,z5,z6]),(1,[z37,z1,z3,z4,z147,z6]),(0,[z63,z1,z2,z3,z164,z4,z5]),(0,[z1,z2,z3,z4,z5,z294,z6])],[(0,[z1,z2,z3,z4,z5,z295,z6]),(0,[z1,z2,z3,z260,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z6]),(0,[z1,z296,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z17,z172,z2,z3,z4,z5]),(0,[z1,z52,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z99]),(0,[z1,z53,z2,z3,z4,z5,z110])],[(0,[z166,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z24,z6,z26]),(0,[z1,z2,z3,z4,z5,z297,z6]),(0,[z1,z77,z2,z3,z4,z180,z6]),(1,[z1,z2,z3,z4,z230,z6]),(0,[z1,z2,z3,z4,z5,z49,z112]),(0,[z1,z2,z3,z129,z5,z18,z6]),(0,[z1,z2,z3,z98,z5,z13,z6])],[(0,[z1,z2,z298,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z171,z6]),(0,[z1,z2,z3,z4,z5,z6,z299]),(0,[z1,z227,z2,z3,z4,z5,z26]),(0,[z63,z1,z2,z3,z4,z115,z5])],[(0,[z1,z2,z3,z4,z5,z300,z6]),(0,[z1,z128,z2,z3,z4,z5,z26]),(0,[z1,z60,z2,z3,z4,z5,z26]),(0,[z1,z172,z10,z3,z4,z5,z6]),(1,[z1,z2,z3,z243,z5,z6]),(0,[z1,z301,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z302,z6])],[(0,[z1,z2,z3,z4,z5,z24,z303]),(0,[z1,z2,z3,z30,z4,z5,z6]),(0,[z1,z2,z3,z304,z4,z5,z6])],[(0,[z72,z2,z47,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z92,z5,z6]),(0,[z1,z305,z2,z3,z4,z5,z6]),(1,[z1,z60,z2,z3,z4,z112])],[(0,[z1,z47,z3,z9,z4,z5,z6]),(0,[z38,z1,z2,z47,z3,z4,z6]),(0,[z131,z1,z2,z3,z4,z5,z24]),(0,[z51,z1,z2,z3,z4,z284,z6]),(0,[z1,z2,z165,z3,z4,z5,z24]),(0,[z1,z2,z306,z3,z4,z5,z6]),(0,[z307,z1,z2,z3,z4,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z98,z4,z5,z26]),(0,[z308,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z165,z138,z4,z5,z6]),(0,[z1,z2,z3,z4,z62,z18,z6]),(0,[z1,z2,z3,z4,z309,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z112])]],
   [[(0,[z1,z17,z2,z3,z4,z92,z5]),(0,[z1,z2,z3,z4,z5,z26,z26]),(0,[z1,z2,z3,z30,z4,z5,z120]),(0,[z1,z310,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z78,z5,z6])],[(0,[z1,z2,z3,z4,z311,z5,z6]),(0,[z1,z2,z3,z312,z4,z5,z6]),(0,[z1,z2,z313,z3,z4,z5,z6]),(0,[z314,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z121,z5,z147,z6]),(0,[z1,z2,z3,z315,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z316,z6]),(0,[z1,z2,z141,z3,z4,z5,z49]),(0,[z317,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z265,z6]),(0,[z318,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z195,z6]),(0,[z1,z2,z3,z4,z319,z5,z6])],[(0,[z1,z2,z3,z4,z5,z320,z6]),(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z322,z1,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z49])],[(0,[z69,z1,z2,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z323,z5,z6]),(1,[z1,z52,z3,z4,z121,z6]),(0,[z63,z140,z1,z2,z3,z4,z5]),(0,[z1,z227,z2,z3,z5,z6,z100])],[(0,[z324,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z325,z4,z5,z6]),(0,[z1,z2,z3,z326,z4,z5,z6])],[(0,[z154,z1,z2,z3,z4,z5,z327]),(0,[z51,z1,z17,z2,z3,z4,z5]),(0,[z1,z117,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z122]),(1,[z1,z68,z2,z3,z18,z6])],[(0,[z1,z2,z3,z4,z5,z6,z328]),(0,[z1,z2,z3,z4,z78,z5,z26]),(0,[z1,z2,z138,z3,z4,z5,z24]),(0,[z1,z329,z2,z3,z4,z5,z6]),(1,[z1,z330,z2,z3,z4,z5]),(0,[z63,z1,z2,z3,z4,z78,z5]),(0,[z63,z1,z60,z2,z3,z4,z5])]],
   [[(0,[z331,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z332,z4,z5,z6]),(0,[z1,z2,z333,z3,z4,z5,z6]),(0,[z334,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z335])],[(0,[z70,z1,z128,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z336,z5,z6]),(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z338,z6]),(0,[z148,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z339,z4,z5,z6])],[(0,[z131,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z340,z4,z5,z6]),(0,[z74,z1,z128,z3,z4,z5,z6]),(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z62,z6,z112]),(0,[z1,z341,z2,z3,z4,z5,z6])],[(0,[z1,z2,z232,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z342,z6]),(0,[z63,z1,z2,z10,z3,z4,z5]),(0,[z63,z1,z2,z3,z4,z5,z13]),(0,[z343,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z136,z4,z129,z6]),(0,[z1,z344,z2,z3,z4,z5,z6])],[(0,[z1,z17,z2,z47,z3,z4,z5]),(0,[z1,z2,z345,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z346,z6]),(0,[z2,z3,z4,z284,z5,z87,z6]),(0,[z1,z2,z3,z4,z284,z62,z6]),(0,[z1,z2,z3,z4,z347,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z12]),(0,[z1,z348,z2,z3,z4,z5,z6]),(0,[z1,z349,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z99])],[(0,[z1,z172,z47,z3,z4,z5,z6]),(0,[z350,z1,z2,z3,z4,z5,z6]),(0,[z154,z1,z2,z3,z4,z5,z26]),(0,[z63,z1,z52,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z351,z5,z6])],[(0,[z70,z1,z2,z3,z4,z5,z352]),(1,[z2,z3,z4,z5,z24,z26]),(0,[z1,z2,z3,z217,z5,z6,z100])],[(0,[z353,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z354,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z90,z4,z5,z26]),(0,[z355,z1,z2,z3,z4,z5,z6]),(0,[z154,z2,z146,z3,z4,z5,z6]),(0,[z63,z51,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z121,z5,z26])],[(0,[z1,z2,z356,z3,z4,z5,z6]),(0,[z74,z70,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z129,z5,z24]),(0,[z1,z2,z3,z4,z357,z5,z6]),(0,[z1,z68,z52,z2,z3,z4,z6]),(0,[z63,z1,z2,z275,z3,z4,z5]),(0,[z63,z1,z227,z2,z3,z4,z5]),(0,[z1,z2,z3,z358,z4,z5,z6]),(0,[z1,z2,z3,z4,z115,z18,z6]),(0,[z1,z133,z2,z3,z4,z252,z6])],[(0,[z1,z2,z3,z4,z359,z5,z6]),(0,[z1,z2,z10,z3,z4,z5,z360]),(0,[z1,z2,z3,z136,z217,z5,z6]),(0,[z1,z361,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z362,z6])],[(0,[z1,z2,z363,z3,z4,z5,z6]),(0,[z63,z154,z1,z2,z3,z4,z5]),(0,[z1,z364,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z24,z100]),(0,[z1,z2,z3,z4,z11,z5,z6]),(0,[z37,z1,z52,z3,z4,z5,z6]),(0,[z37,z1,z2,z3,z4,z147,z6]),(0,[z1,z17,z2,z138,z3,z4,z5]),(0,[z1,z365,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z366])],[(0,[z1,z367,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z368,z6]),(0,[z369,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z370])],[(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z1,z52,z2,z3,z4,z147,z6])],[(1,[z1,z2,z3,z4,z5,z352])],[(0,[z266,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z372]),(1,[z1,z2,z3,z4,z5,z373]),(0,[z374,z63,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z17,z2,z375,z3,z4,z5]),(0,[z1,z2,z3,z376,z4,z5,z6]),(0,[z1,z2,z3,z377,z4,z5,z6]),(0,[z1,z2,z3,z4,z378,z5,z6])],[(0,[z1,z227,z2,z3,z4,z5,z24]),(0,[z1,z379,z2,z3,z9,z4,z5]),(0,[z63,z1,z172,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z380,z6]),(0,[z1,z2,z3,z4,z5,z381,z6]),(0,[z1,z77,z2,z3,z4,z5,z382]),(0,[z1,z2,z3,z4,z383,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z384])],[(0,[z385,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z386,z3,z4,z5,z6]),(0,[z1,z128,z2,z3,z4,z5,z24])],[(1,[z154,z2,z146,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z103]),(1,[z41,z1,z9,z4,z5,z6]),(0,[z1,z17,z2,z3,z217,z4,z5]),(0,[z387,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z217,z4,z78,z5,z6]),(0,[z1,z2,z138,z4,z5,z62,z6]),(0,[z1,z2,z3,z4,z388,z5,z6])],[(0,[z185,z1,z72,z2,z3,z4,z5]),(0,[z1,z2,z10,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z389,z34,z5]),(1,[z1,z128,z3,z30,z5,z6]),(0,[z1,z2,z3,z4,z115,z6,z112])],[(0,[z166,z51,z2,z3,z4,z5,z6]),(0,[z1,z172,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z285,z6]),(1,[z1,z2,z3,z4,z5,z390]),(0,[z1,z391,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z129,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z1,z392,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z284,z5,z26]),(0,[z1,z2,z3,z98,z4,z5,z24]),(0,[z1,z2,z165,z4,z78,z5,z6]),(0,[z1,z53,z2,z3,z4,z5,z80]),(0,[z1,z393,z2,z3,z4,z5,z6])],[]],
   [[(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z136,z4,z5,z26]),(0,[z41,z1,z172,z3,z4,z5,z6]),(0,[z394,z1,z2,z3,z4,z5,z6])],[(0,[z185,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z92,z5]),(0,[z1,z2,z3,z4,z5,z13,z26]),(0,[z1,z395,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z396,z6]),(0,[z1,z2,z3,z4,z61,z115,z6]),(0,[z1,z397,z2,z3,z4,z5,z6])],[(0,[z398,z1,z2,z3,z4,z5,z6])],[(0,[z37,z51,z1,z2,z3,z4,z6]),(0,[z166,z1,z52,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z399,z6]),(0,[z1,z2,z3,z5,z274,z147,z6]),(0,[z1,z2,z3,z4,z5,z6,z400])],[(0,[z1,z401,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z402,z26]),(0,[z1,z2,z10,z3,z403,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z49]),(0,[z1,z53,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z404])],[(0,[z0,z1,z2,z47,z3,z5,z6]),(0,[z1,z2,z3,z405,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z406]),(0,[z1,z407,z2,z3,z4,z5,z6]),(0,[z1,z408,z17,z2,z3,z4,z5]),(0,[z1,z409,z2,z3,z4,z5,z6]),(0,[z410,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z411,z4,z5,z6]),(0,[z1,z227,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z412,z5,z6]),(0,[z1,z2,z3,z4,z78,z5,z24]),(0,[z1,z128,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z413]),(0,[z1,z60,z2,z3,z4,z5,z6])],[(0,[z131,z1,z2,z90,z4,z5,z6]),(1,[z51,z2,z3,z4,z87,z6]),(0,[z1,z2,z3,z4,z5,z414,z6]),(1,[z1,z2,z3,z4,z5,z245]),(0,[z1,z17,z2,z3,z4,z5,z100])]],
   [[(0,[z1,z2,z3,z415,z4,z5,z6]),(0,[z1,z416,z2,z3,z4,z5,z6]),(0,[z1,z2,z417,z3,z4,z5,z6]),(0,[z69,z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z12,z24]),(1,[z1,z2,z3,z246,z5,z6])],[(0,[z1,z2,z3,z418,z4,z5,z6]),(0,[z1,z419,z2,z3,z4,z5,z6]),(0,[z1,z420,z2,z3,z4,z5,z6]),(0,[z1,z2,z421,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z422,z4,z5,z6])],[(0,[z263,z1,z2,z3,z4,z5,z6]),(1,[z63,z84,z2,z3,z4,z5]),(0,[z1,z77,z2,z3,z217,z5,z6]),(0,[z1,z423,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z98,z4,z5,z6]),(0,[z1,z2,z3,z5,z13,z6,z100])],[(0,[z424,z1,z2,z47,z4,z5,z6]),(0,[z1,z2,z138,z3,z4,z5,z26]),(0,[z1,z17,z128,z2,z3,z4,z5]),(0,[z1,z17,z17,z2,z3,z4,z5]),(0,[z1,z425,z2,z3,z4,z5,z6])],[(0,[z426,z1,z2,z3,z4,z5,z6]),(0,[z154,z1,z2,z3,z4,z5,z24]),(0,[z69,z2,z3,z4,z92,z5,z6]),(0,[z1,z2,z3,z4,z427,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z428]),(0,[z1,z2,z3,z429,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z196]),(0,[z1,z2,z3,z4,z5,z6,z430]),(0,[z1,z32,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z431,z6]),(0,[z432,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z48]),(0,[z433,z1,z2,z3,z4,z5,z6]),(0,[z1,z395,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z434,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z62]),(0,[z1,z435,z2,z3,z4,z5,z6])],[(0,[z1,z2,z47,z3,z4,z5,z26]),(1,[z1,z2,z46,z3,z4,z6]),(0,[z1,z2,z3,z4,z436,z5,z6]),(0,[z1,z2,z3,z4,z437,z5,z6]),(0,[z1,z2,z3,z291,z9,z4,z5]),(0,[z1,z2,z3,z4,z5,z438,z6]),(0,[z63,z1,z17,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z90,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z24,z26]),(0,[z1,z2,z3,z4,z121,z5,z24])]],
   [[(0,[z1,z439,z2,z3,z4,z5,z6]),(0,[z131,z1,z2,z3,z4,z5,z440]),(0,[z1,z2,z3,z441,z4,z5,z6]),(0,[z63,z1,z133,z2,z3,z4,z5]),(0,[z442,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z115,z5,z24]),(0,[z1,z443,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z444]),(0,[z70,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z78,z5,z6])],[(1,[z1,z2,z3,z445,z5,z6]),(0,[z154,z1,z2,z3,z4,z5,z81]),(0,[z1,z17,z2,z3,z9,z4,z5]),(1,[z1,z2,z3,z4,z5,z382])],[(0,[z1,z17,z2,z3,z4,z284,z5]),(0,[z1,z446,z2,z3,z4,z34,z5]),(0,[z63,z1,z2,z3,z4,z447,z5]),(0,[z63,z1,z2,z138,z3,z4,z5]),(0,[z448,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z19,z3,z4,z5,z6]),(1,[z1,z17,z3,z4,z5,z150]),(0,[z449,z1,z2,z3,z4,z5,z6]),(0,[z1,z133,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z450,z6]),(0,[z1,z68,z2,z3,z4,z18,z6])],[(0,[z1,z2,z451,z3,z4,z5,z6]),(0,[z1,z2,z452,z3,z4,z5,z6])],[(1,[z71,z47,z3,z4,z5,z6]),(1,[z131,z2,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z453,z6])]],
   [[(0,[z1,z72,z2,z3,z4,z5,z26]),(0,[z154,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z454,z6]),(0,[z1,z2,z3,z104,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z87,z26]),(0,[z1,z68,z128,z2,z3,z5,z6])],[(1,[z1,z2,z138,z217,z5,z6]),(0,[z1,z455,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z456,z5,z6]),(0,[z457,z1,z2,z3,z4,z5,z6])],[(0,[z70,z2,z3,z104,z4,z5,z6]),(1,[z1,z17,z2,z3,z4,z5]),(0,[z458,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z459]),(1,[z1,z2,z3,z136,z129,z6])],[(0,[z1,z460,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z10,z3,z4,z5,z24]),(0,[z74,z1,z3,z4,z34,z5,z6]),(0,[z1,z2,z3,z4,z121,z5,z6]),(0,[z1,z53,z2,z3,z4,z115,z6]),(1,[z1,z2,z165,z4,z115,z6]),(0,[z1,z2,z3,z4,z5,z6,z461]),(0,[z1,z2,z3,z4,z5,z462,z6])],[(0,[z166,z1,z2,z3,z4,z87,z6]),(0,[z1,z2,z3,z4,z463,z5,z6]),(0,[z1,z172,z2,z3,z4,z5,z24]),(0,[z63,z1,z2,z3,z217,z4,z5])],[(0,[z1,z2,z3,z4,z5,z352,z6]),(0,[z51,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z284,z5,z24]),(0,[z1,z408,z2,z3,z4,z5,z26])],[(1,[z464,z2,z3,z4,z5,z24]),(1,[z63,z1,z2,z3,z4,z5])],[(0,[z464,z2,z47,z3,z4,z5,z6]),(0,[z465,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z4,z5,z24]),(0,[z1,z17,z2,z3,z4,z129,z5]),(0,[z1,z60,z2,z3,z4,z5,z112])]],
   [[(0,[z1,z2,z3,z466,z4,z5,z6]),(0,[z467,z1,z2,z3,z4,z5,z6]),(0,[z464,z2,z3,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z5,z13,z24]),(0,[z1,z2,z3,z4,z5,z468,z6]),(0,[z469,z63,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z470,z6]),(0,[z1,z2,z3,z4,z5,z6,z471])],[(0,[z1,z2,z3,z217,z104,z5,z6]),(0,[z464,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z472]),(0,[z1,z2,z3,z4,z473,z34,z6]),(0,[z1,z2,z3,z78,z5,z18,z6])],[],[],[(1,[z1,z2,z3,z311,z5,z6]),(0,[z1,z474,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z475,z6]),(0,[z70,z1,z2,z3,z104,z5,z6]),(0,[z476,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z112]),(0,[z1,z2,z3,z4,z477,z5,z6]),(0,[z1,z2,z3,z478,z4,z5,z6]),(0,[z1,z2,z3,z4,z61,z5,z12])],[(0,[z1,z2,z3,z479,z4,z5,z6]),(0,[z464,z63,z1,z2,z3,z4,z5]),(0,[z97,z1,z2,z3,z4,z5,z6]),(0,[z1,z53,z2,z165,z4,z5,z6]),(1,[z1,z2,z3,z290,z5,z6]),(0,[z480,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z481,z6])],[],[(0,[z1,z2,z3,z4,z5,z482,z6]),(0,[z1,z2,z3,z217,z4,z5,z26]),(0,[z1,z2,z10,z3,z4,z5,z6]),(0,[z1,z483,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z172,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z100]),(0,[z1,z2,z3,z4,z236,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z484]),(0,[z1,z2,z485,z3,z4,z5,z6])],[(0,[z51,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z284,z5,z6]),(0,[z1,z2,z3,z4,z5,z212,z6]),(0,[z63,z166,z1,z2,z3,z4,z5]),(1,[z23,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z486,z5,z6]),(0,[z1,z487,z2,z3,z4,z5,z6]),(0,[z1,z53,z2,z3,z246,z5,z6])],[(1,[z1,z2,z3,z4,z5,z320]),(0,[z1,z2,z3,z4,z488,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z26]),(0,[z1,z489,z2,z3,z4,z5,z24]),(0,[z1,z133,z2,z3,z197,z5,z6]),(0,[z1,z490,z2,z3,z4,z5,z6])],[(0,[z131,z1,z2,z3,z4,z56,z6]),(0,[z1,z2,z146,z3,z4,z5,z26]),(0,[z1,z2,z491,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z492,z6]),(0,[z1,z493,z2,z3,z4,z5,z26]),(0,[z1,z494,z2,z3,z4,z5,z6]),(0,[z1,z2,z495,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z26,z328]),(0,[z1,z2,z3,z4,z5,z12,z26]),(0,[z63,z1,z128,z2,z3,z4,z5]),(0,[z63,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z496]),(0,[z1,z77,z2,z3,z4,z5,z497]),(0,[z1,z2,z3,z4,z5,z6,z498]),(0,[z1,z68,z2,z411,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z13,z6])],[(0,[z1,z2,z47,z3,z4,z5,z24]),(0,[z69,z1,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z245]),(0,[z63,z1,z2,z3,z4,z5,z196])],[(0,[z1,z2,z499,z3,z4,z5,z6]),(0,[z1,z2,z500,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z24]),(0,[z1,z2,z3,z4,z5,z24,z214]),(0,[z1,z2,z3,z501,z4,z5,z6]),(0,[z74,z1,z2,z3,z129,z5,z6]),(0,[z343,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z62]),(0,[z1,z2,z3,z4,z502,z5,z6]),(0,[z1,z2,z503,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z402,z6])]],
   [[(1,[z2,z47,z3,z4,z5,z26]),(0,[z1,z504,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z87]),(0,[z37,z1,z2,z3,z4,z115,z6]),(0,[z63,z63,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z505,z6])],[(0,[z51,z2,z3,z4,z5,z87,z6]),(0,[z1,z2,z3,z4,z5,z26,z99]),(0,[z1,z2,z506,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z136,z4,z5]),(0,[z1,z2,z507,z3,z4,z5,z6])],[(0,[z74,z1,z2,z3,z34,z5,z6]),(0,[z1,z52,z2,z3,z4,z115,z6]),(0,[z1,z508,z2,z3,z4,z5,z6])],[(0,[z1,z2,z226,z47,z3,z5,z6]),(0,[z1,z17,z2,z3,z4,z61,z5])],[(0,[z1,z2,z3,z4,z509,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z233]),(0,[z63,z1,z2,z3,z9,z4,z5]),(0,[z1,z276,z2,z3,z4,z5,z6]),(0,[z510,z1,z2,z3,z4,z5,z6])],[(0,[z190,z1,z2,z3,z4,z5,z6]),(0,[z71,z2,z47,z3,z4,z5,z6]),(0,[z154,z1,z2,z90,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z284,z5]),(0,[z1,z2,z3,z4,z5,z147,z26]),(0,[z1,z2,z3,z4,z115,z5,z26]),(0,[z1,z2,z3,z4,z511,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z512]),(0,[z513,z1,z2,z3,z4,z5,z6])],[(1,[z185,z1,z2,z3,z4,z5]),(0,[z514,z1,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z515]),(0,[z1,z516,z2,z3,z4,z5,z6]),(0,[z1,z489,z2,z3,z4,z5,z6]),(0,[z517,z1,z2,z3,z4,z5,z6]),(0,[z374,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z3,z9,z4,z5,z6]),(0,[z1,z2,z3,z4,z447,z5,z6]),(0,[z1,z2,z138,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z49,z100])],[(0,[z71,z1,z17,z2,z3,z4,z5]),(0,[z1,z72,z2,z3,z4,z5,z24]),(0,[z131,z1,z145,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z240]),(0,[z1,z2,z3,z104,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z87,z24]),(0,[z1,z2,z3,z4,z5,z518,z6]),(0,[z1,z519,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z520,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z521]),(0,[z1,z2,z3,z4,z5,z6,z522]),(0,[z1,z77,z2,z138,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z523,z6]),(0,[z1,z2,z3,z524,z4,z5,z6])],[(0,[z1,z2,z47,z3,z4,z5,z6]),(0,[z525,z1,z2,z3,z4,z5,z6]),(0,[z464,z1,z2,z3,z4,z5,z26]),(0,[z191,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z403,z5,z6])],[(0,[z71,z63,z1,z2,z3,z4,z5]),(0,[z1,z526,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z1,z2,z3,z4,z5,z150,z6]),(0,[z1,z77,z2,z3,z78,z5,z6]),(0,[z1,z133,z2,z3,z4,z5,z99])],[(0,[z527,z1,z2,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z295]),(0,[z37,z166,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z528,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z100])],[(0,[z1,z17,z2,z3,z4,z34,z5])],[(1,[z1,z2,z3,z4,z5,z515]),(0,[z1,z2,z3,z4,z5,z6,z529]),(0,[z1,z2,z3,z4,z530,z5,z6]),(0,[z531,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z532,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z265,z6]),(0,[z1,z2,z3,z4,z533,z5,z6]),(0,[z534,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z63,z1,z2,z3,z4,z129,z5]),(0,[z1,z248,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z535,z6]),(0,[z1,z60,z2,z3,z4,z5,z12])],[(0,[z69,z1,z128,z2,z3,z5,z6]),(1,[z63,z1,z17,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z196]),(0,[z536,z1,z17,z2,z3,z4,z5]),(0,[z1,z68,z17,z2,z3,z4,z5]),(0,[z1,z2,z537,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z538]),(0,[z1,z2,z3,z4,z5,z539,z6])],[(0,[z540,z1,z2,z3,z4,z5,z6]),(0,[z1,z364,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z99,z112]),(0,[z1,z2,z541,z3,z4,z5,z6])],[(0,[z1,z72,z2,z3,z4,z5,z6]),(0,[z1,z408,z72,z2,z3,z4,z5]),(0,[z1,z2,z3,z104,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z87,z6]),(0,[z1,z2,z3,z4,z5,z542,z24]),(0,[z74,z1,z2,z3,z78,z5,z6]),(1,[z1,z2,z3,z4,z473,z6]),(0,[z1,z77,z17,z2,z3,z4,z5])],[(1,[z55,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z543,z6]),(0,[z1,z544,z2,z3,z4,z5,z6]),(0,[z1,z2,z545,z3,z4,z5,z24]),(0,[z1,z2,z3,z546,z4,z5,z6]),(0,[z1,z330,z2,z3,z4,z5,z147]),(0,[z1,z2,z165,z3,z4,z115,z6]),(0,[z1,z68,z2,z3,z4,z129,z6]),(1,[z1,z2,z3,z98,z5,z13])],[(0,[z55,z1,z17,z2,z3,z4,z5]),(1,[z1,z283,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z547,z5,z6]),(0,[z536,z63,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z548]),(0,[z1,z2,z3,z4,z5,z13,z112])],[(0,[z1,z17,z2,z3,z104,z4,z5]),(0,[z1,z2,z3,z217,z4,z5,z24]),(0,[z549,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z497]),(0,[z1,z2,z3,z4,z5,z6,z550])],[(0,[z71,z1,z2,z3,z4,z5,z320]),(0,[z1,z2,z3,z4,z551,z5,z6])]],
   [[(0,[z1,z408,z2,z3,z4,z5,z6])],[(0,[z552,z1,z2,z3,z4,z5,z6]),(0,[z70,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z553,z26]),(0,[z1,z2,z3,z4,z5,z24,z27]),(0,[z1,z128,z2,z3,z30,z5,z6])],[(0,[z1,z2,z3,z445,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z327,z6]),(0,[z1,z2,z146,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z554,z6])],[(0,[z1,z2,z46,z3,z4,z5,z6]),(0,[z166,z1,z2,z3,z4,z284,z6]),(0,[z74,z1,z17,z2,z3,z4,z5]),(1,[z1,z2,z3,z235,z5,z6]),(0,[z1,z2,z3,z4,z235,z5,z6])],[(1,[z55,z72,z3,z4,z5,z6]),(0,[z154,z1,z2,z146,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z5,z125]),(0,[z1,z330,z2,z3,z4,z5,z6]),(0,[z555,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z165,z4,z115,z5,z6])],[(0,[z55,z1,z47,z3,z4,z5,z6]),(0,[z55,z72,z2,z3,z4,z5,z6]),(1,[z1,z239,z2,z3,z5,z6]),(0,[z63,z1,z68,z2,z3,z4,z5]),(0,[z1,z2,z65,z3,z4,z5,z6])],[(0,[z1,z2,z3,z556,z4,z5,z6]),(0,[z1,z557,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z558,z6]),(0,[z1,z2,z3,z4,z5,z6,z360]),(0,[z1,z559,z2,z3,z4,z5,z6]),(0,[z560,z1,z2,z3,z4,z5,z6])],[(0,[z71,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z542,z6]),(0,[z1,z2,z3,z4,z5,z561,z26]),(0,[z1,z2,z3,z562,z4,z5,z6]),(0,[z74,z63,z1,z2,z3,z4,z5])]],
   [[(0,[z1,z283,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z563,z4,z5,z6]),(0,[z1,z2,z545,z3,z4,z5,z6]),(0,[z1,z2,z10,z3,z4,z256,z6]),(0,[z1,z2,z3,z4,z389,z5,z6]),(0,[z1,z2,z3,z4,z5,z564,z6]),(0,[z1,z2,z3,z565,z4,z5,z6])],[(0,[z1,z159,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z87]),(1,[z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z141,z4,z5,z49,z6]),(0,[z1,z2,z3,z4,z566,z5,z6])],[(0,[z1,z2,z3,z4,z5,z567,z6]),(1,[z1,z2,z3,z4,z5,z568]),(1,[z1,z172,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z569,z6]),(0,[z63,z1,z2,z3,z136,z4,z5]),(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z1,z2,z4,z115,z5,z62,z6]),(0,[z1,z2,z3,z4,z5,z13,z99]),(0,[z1,z2,z3,z4,z5,z6,z570]),(0,[z1,z2,z3,z4,z5,z6,z571])],[(0,[z572,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z146,z3,z4,z5]),(0,[z166,z1,z17,z2,z3,z4,z5]),(0,[z1,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z24,z150]),(0,[z1,z2,z3,z4,z5,z24,z112]),(0,[z1,z2,z3,z4,z5,z180,z6]),(0,[z1,z2,z3,z4,z5,z6,z573])],[(0,[z131,z154,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z147,z24]),(0,[z37,z63,z1,z2,z3,z4,z5]),(0,[z63,z1,z2,z3,z4,z61,z5]),(0,[z1,z574,z2,z3,z4,z5,z6]),(0,[z1,z575,z2,z3,z4,z5,z6])],[(0,[z70,z1,z2,z3,z4,z5,z6]),(0,[z41,z63,z1,z2,z3,z4,z5]),(0,[z1,z10,z3,z9,z4,z5,z6]),(0,[z74,z1,z2,z3,z217,z5,z6]),(0,[z43,z63,z1,z2,z3,z4,z5]),(0,[z576,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z146,z3,z4,z5,z6]),(0,[z1,z2,z3,z577,z4,z5,z6]),(0,[z1,z493,z2,z3,z4,z5,z6]),(0,[z1,z578,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z31])],[(0,[z579,z1,z2,z3,z4,z5,z6]),(0,[z580,z1,z2,z3,z4,z5,z6]),(0,[z581,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z582,z3,z4,z5,z6]),(0,[z1,z2,z375,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z129,z115,z6]),(0,[z1,z2,z3,z4,z5,z12,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z26]),(0,[z464,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z390,z6]),(0,[z1,z2,z3,z4,z5,z122,z6]),(0,[z1,z17,z3,z4,z5,z150,z6])],[(0,[z1,z2,z3,z4,z583,z5,z6]),(0,[z536,z1,z2,z3,z4,z5,z26]),(0,[z1,z68,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z100,z112])],[(0,[z1,z2,z584,z3,z4,z5,z6]),(0,[z1,z585,z2,z3,z4,z5,z6]),(0,[z1,z2,z586,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z150,z6,z196]),(1,[z1,z2,z141,z4,z5,z49]),(0,[z1,z2,z3,z4,z587,z5,z6]),(0,[z1,z2,z3,z588,z4,z5,z6])],[(1,[z70,z2,z3,z104,z5,z6]),(0,[z464,z23,z2,z3,z4,z5,z6]),(0,[z23,z1,z17,z2,z3,z4,z5]),(0,[z1,z77,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z589,z6]),(0,[z1,z17,z2,z3,z315,z4,z5]),(1,[z1,z77,z2,z78,z5,z6]),(0,[z590,z1,z2,z3,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z26]),(0,[z131,z1,z2,z3,z445,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z240]),(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z591,z5,z6])],[(0,[z63,z1,z2,z3,z4,z34,z5]),(0,[z1,z2,z592,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z593,z6]),(0,[z469,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z373,z147]),(0,[z594,z1,z2,z3,z4,z5,z6]),(0,[z1,z595,z2,z3,z4,z5,z6]),(0,[z1,z2,z596,z3,z4,z5,z6])]],
   [[(0,[z424,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z99]),(0,[z41,z1,z2,z10,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z147,z6]),(0,[z1,z2,z3,z4,z115,z5,z6])],[(0,[z597,z1,z2,z3,z4,z5,z6]),(0,[z131,z1,z2,z146,z4,z5,z6]),(0,[z1,z2,z598,z3,z4,z5,z6]),(0,[z63,z69,z1,z2,z3,z4,z5]),(1,[z1,z276,z2,z3,z4,z6])],[(0,[z55,z2,z3,z4,z5,z6,z26]),(0,[z1,z2,z3,z4,z5,z26,z299]),(0,[z1,z2,z10,z3,z243,z5,z6]),(0,[z1,z17,z2,z165,z3,z4,z5]),(0,[z1,z2,z599,z3,z4,z5,z6]),(0,[z600,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z601,z5,z6])],[(0,[z74,z1,z2,z3,z4,z5,z26]),(0,[z63,z1,z2,z3,z4,z5,z24]),(0,[z1,z602,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z411,z4,z5,z6])],[(0,[z131,z41,z1,z2,z4,z5,z6]),(0,[z603,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z515]),(0,[z464,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z141,z3,z4,z5,z26])],[(0,[z55,z1,z72,z3,z4,z5,z6]),(0,[z1,z2,z3,z604,z4,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z26]),(0,[z605,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z606,z4,z5]),(0,[z1,z2,z3,z4,z607,z5,z6])],[(1,[z1,z2,z3,z4,z5,z608]),(0,[z1,z2,z3,z609,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z26]),(0,[z1,z17,z2,z3,z4,z5,z26]),(0,[z1,z610,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z611,z6])],[(0,[z1,z2,z3,z4,z5,z612,z6]),(0,[z63,z1,z2,z3,z104,z4,z5]),(1,[z266,z1,z2,z3,z4,z5]),(0,[z1,z128,z2,z3,z34,z5,z6]),(0,[z1,z2,z3,z4,z5,z373,z6]),(0,[z1,z133,z2,z3,z4,z5,z49]),(0,[z1,z2,z3,z4,z5,z6,z613])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z303]),(0,[z1,z446,z2,z3,z4,z5,z6]),(0,[z614,z1,z2,z3,z4,z5,z6])],[(0,[z41,z1,z2,z9,z4,z5,z6]),(0,[z1,z615,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z616,z4,z5,z6])],[(0,[z69,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z61,z62,z6]),(0,[z1,z2,z4,z5,z49,z6,z99])],[(0,[z617,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z360]),(0,[z1,z17,z2,z3,z4,z5,z294]),(0,[z1,z2,z3,z4,z618,z5,z6]),(0,[z1,z2,z3,z619,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z20]),(1,[z1,z408,z2,z3,z4,z5]),(0,[z1,z72,z172,z3,z4,z5,z6]),(0,[z1,z2,z620,z3,z4,z5,z6]),(0,[z51,z1,z2,z3,z4,z87,z6]),(0,[z1,z2,z3,z4,z5,z256,z6]),(0,[z1,z2,z3,z4,z5,z6,z497]),(0,[z1,z2,z3,z4,z5,z142,z6])],[(0,[z1,z2,z3,z4,z621,z5,z6]),(0,[z1,z2,z3,z622,z4,z5,z6])],[(0,[z71,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z623,z4,z5,z6]),(0,[z131,z1,z2,z3,z311,z5,z6]),(1,[z1,z2,z3,z4,z5,z327]),(0,[z1,z2,z3,z4,z624,z5,z6]),(0,[z1,z2,z3,z30,z4,z5,z26]),(0,[z1,z128,z3,z30,z4,z5,z6]),(0,[z1,z2,z3,z625,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z626,z6])],[(1,[z166,z2,z3,z4,z284,z6]),(0,[z627,z1,z2,z3,z4,z5,z6]),(0,[z628,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z629,z4,z5,z6]),(1,[z1,z227,z2,z3,z5,z100]),(0,[z1,z2,z3,z4,z12,z6,z112])]],
   [[(0,[z1,z101,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z295]),(0,[z189,z1,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z382,z6]),(0,[z1,z2,z3,z4,z5,z630,z6]),(0,[z1,z2,z631,z3,z4,z5,z6]),(0,[z1,z227,z2,z3,z98,z5,z6])],[(0,[z632,z1,z2,z3,z4,z5,z6]),(0,[z633,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z634,z5,z6]),(0,[z1,z1,z2,z3,z4,z5,z24]),(1,[z1,z379,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z635,z6]),(0,[z636,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z440,z6]),(0,[z23,z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z637,z4,z5,z6]),(0,[z1,z2,z3,z197,z4,z5,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z553,z6]),(1,[z1,z2,z3,z4,z5,z110]),(1,[z1,z133,z2,z4,z5,z99])],[(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z146,z3,z4,z5]),(0,[z1,z639,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z26]),(0,[z1,z640,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z641,z6])],[(1,[z38,z1,z2,z3,z4,z6]),(0,[z464,z55,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z642,z5,z6]),(0,[z1,z2,z3,z643,z4,z5,z6]),(0,[z1,z379,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z30,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z568]),(0,[z23,z2,z3,z4,z5,z6,z26]),(0,[z536,z1,z2,z3,z4,z5,z24]),(0,[z1,z68,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z606,z4,z5,z6]),(0,[z1,z2,z3,z4,z644,z5,z6]),(0,[z1,z2,z3,z4,z5,z645,z6])],[(0,[z1,z2,z3,z4,z646,z5,z6]),(1,[z1,z446,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z389,z5]),(0,[z1,z84,z2,z3,z4,z5,z6])],[(0,[z71,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z561,z6]),(0,[z1,z77,z2,z3,z4,z5,z24])],[(0,[z647,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z648,z24]),(0,[z649,z1,z2,z3,z4,z5,z6]),(1,[z63,z1,z3,z4,z5,z196]),(0,[z1,z650,z2,z3,z4,z5,z6])],[(0,[z55,z1,z2,z3,z4,z5,z24]),(0,[z1,z651,z2,z3,z4,z5,z6]),(0,[z69,z1,z2,z3,z104,z5,z6]),(0,[z1,z2,z3,z4,z61,z5,z26]),(0,[z652,z1,z2,z3,z4,z5,z6]),(0,[z653,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z31]),(0,[z1,z2,z3,z4,z5,z654,z6]),(1,[z1,z2,z3,z4,z252,z6])],[(1,[z1,z2,z3,z403,z5,z6]),(0,[z1,z2,z3,z4,z655,z5,z6]),(0,[z1,z133,z2,z141,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z12,z99]),(0,[z1,z656,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z226,z3,z5,z6]),(0,[z1,z2,z145,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z347,z5,z26]),(0,[z225,z63,z1,z2,z3,z4,z5]),(0,[z1,z53,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z13,z49]),(0,[z1,z657,z2,z3,z4,z5,z6])],[(0,[z1,z2,z658,z3,z4,z5,z6]),(0,[z185,z63,z1,z2,z3,z4,z5]),(0,[z63,z1,z2,z3,z4,z351,z5]),(0,[z63,z1,z3,z4,z5,z6,z196]),(0,[z1,z2,z3,z4,z5,z6,z659])]],
   [[(1,[z1,z2,z3,z4,z5,z125]),(0,[z660,z1,z2,z3,z4,z5,z6]),(0,[z1,z60,z17,z2,z3,z4,z5]),(0,[z1,z661,z2,z3,z4,z5,z6]),(0,[z662,z1,z2,z3,z4,z5,z6])],[(0,[z1,z663,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z212]),(0,[z1,z2,z3,z4,z5,z26,z100]),(0,[z1,z2,z3,z4,z5,z664,z6]),(0,[z1,z68,z2,z3,z136,z5,z6]),(0,[z1,z227,z2,z3,z4,z5,z13])],[(0,[z71,z1,z47,z3,z4,z5,z6]),(0,[z1,z2,z3,z665,z4,z5,z6]),(0,[z69,z1,z2,z3,z4,z5,z26]),(0,[z666,z1,z2,z3,z4,z5,z6]),(0,[z74,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z667,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z668,z6]),(0,[z1,z2,z3,z669,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z670,z6]),(1,[z1,z2,z3,z4,z195,z6]),(1,[z1,z2,z3,z4,z5,z142])],[(0,[z71,z1,z2,z3,z4,z5,z608]),(0,[z2,z47,z3,z4,z5,z6,z26]),(1,[z1,z2,z3,z4,z5,z440]),(0,[z1,z671,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z672,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z167,z2,z3,z4,z5,z26]),(0,[z1,z2,z141,z3,z4,z5,z24]),(0,[z63,z1,z2,z165,z3,z4,z5]),(0,[z1,z673,z2,z3,z4,z5,z6])],[(0,[z536,z1,z2,z3,z4,z5,z6]),(0,[z166,z2,z3,z4,z284,z5,z6]),(0,[z1,z2,z3,z9,z4,z5,z24]),(0,[z1,z2,z10,z3,z4,z5,z390]),(0,[z1,z53,z2,z3,z4,z62,z6]),(0,[z1,z68,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z674,z4,z5,z6]),(0,[z1,z177,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z18,z24]),(0,[z1,z675,z2,z3,z4,z5,z6]),(0,[z676,z1,z2,z3,z4,z5,z6]),(0,[z1,z677,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z678,z4,z5,z6])],[(0,[z679,z1,z2,z3,z4,z5,z6]),(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z681,z3,z4,z5,z6]),(0,[z1,z2,z3,z682,z4,z5,z6]),(0,[z1,z2,z3,z683,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z26,z196]),(0,[z1,z2,z3,z4,z5,z6,z684]),(0,[z74,z1,z68,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z473,z5,z6]),(0,[z1,z17,z2,z3,z4,z121,z5]),(0,[z426,z1,z17,z2,z3,z4,z5]),(0,[z1,z77,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z217,z5,z18,z6]),(0,[z1,z2,z207,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z685,z6]),(0,[z1,z2,z3,z98,z4,z5,z13])],[(0,[z1,z2,z3,z4,z5,z686,z6]),(0,[z687,z1,z2,z3,z4,z5,z6]),(0,[z131,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z648,z6]),(0,[z63,z1,z2,z3,z4,z5,z26]),(0,[z1,z17,z2,z3,z4,z502,z5]),(0,[z688,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z689])]],
   [[(0,[z55,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z150]),(0,[z1,z690,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z691,z6]),(0,[z1,z17,z2,z3,z4,z5,z147]),(0,[z1,z2,z3,z4,z692,z5,z6]),(0,[z1,z17,z2,z65,z3,z4,z5]),(0,[z1,z2,z3,z78,z5,z6,z100]),(0,[z1,z53,z2,z3,z290,z5,z6])],[(0,[z166,z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z93,z6]),(0,[z1,z2,z138,z217,z4,z5,z6])],[(0,[z1,z2,z3,z693,z4,z5,z6]),(0,[z1,z2,z3,z4,z694,z5,z6]),(0,[z166,z1,z2,z3,z4,z5,z568]),(0,[z1,z2,z3,z4,z5,z695,z6])],[(0,[z71,z55,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z608]),(1,[z424,z1,z2,z4,z5,z6]),(0,[z1,z17,z72,z2,z3,z4,z5]),(0,[z1,z696,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z291,z4,z5,z6]),(0,[z1,z2,z697,z3,z4,z5,z6]),(0,[z1,z698,z2,z3,z4,z5,z6]),(0,[z1,z699,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z30,z4,z5,z24]),(0,[z1,z2,z700,z3,z4,z5,z6]),(0,[z701,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z702,z5,z6]),(0,[z1,z2,z3,z4,z703,z5,z6]),(0,[z1,z2,z704,z3,z4,z5,z6])],[(1,[z1,z489,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z6,z705]),(0,[z1,z133,z17,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z706,z5,z6]),(0,[z1,z2,z141,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z707,z2,z3,z4,z5]),(1,[z1,z3,z4,z708,z6]),(0,[z1,z709,z2,z3,z4,z5])],[(0,[z1,z2,z3,z710,z5,z6]),(0,[z1,z2,z3,z711,z5,z6]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z2,z3,z4,z5,z59,z24])],[(0,[z1,z2,z713,z3,z4,z5])],[(0,[z1,z408,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z26,z714]),(0,[z84,z2,z165,z3,z4,z5])],[(0,[z715,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z243,z5,z26]),(0,[z1,z239,z330,z2,z3,z5])],[(0,[z555,z2,z3,z104,z5,z6]),(0,[z1,z2,z3,z4,z5,z716]),(0,[z1,z717,z2,z3,z4,z5]),(0,[z1,z2,z28,z217,z5,z6])],[(0,[z166,z2,z3,z4,z284,z6]),(0,[z1,z718,z2,z3,z4,z5]),(0,[z63,z1,z277,z3,z4,z5]),(0,[z1,z227,z2,z3,z5,z100])],[(0,[z1,z2,z3,z4,z6,z719]),(0,[z1,z2,z720,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z721]),(0,[z1,z2,z500,z4,z115,z6]),(0,[z1,z3,z4,z5,z708,z6])],[(0,[z0,z1,z2,z3,z5,z26]),(0,[z2,z224,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z722]),(0,[z1,z2,z3,z235,z5,z99])],[(0,[z1,z2,z226,z3,z5,z24]),(0,[z1,z2,z3,z4,z723,z6]),(0,[z1,z2,z3,z724,z5,z6]),(0,[z322,z2,z3,z4,z5,z26])],[(0,[z71,z46,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z725,z24]),(0,[z1,z2,z3,z4,z5,z726])],[(0,[z1,z2,z3,z727,z5,z6])],[(0,[z55,z84,z2,z3,z4,z5]),(0,[z1,z283,z3,z445,z5,z6]),(0,[z1,z728,z2,z3,z4,z5]),(0,[z263,z1,z2,z3,z4,z351]),(0,[z1,z17,z508,z3,z4,z5])],[(0,[z38,z1,z2,z3,z4,z6]),(0,[z1,z52,z3,z4,z121,z26]),(0,[z1,z2,z3,z4,z729,z24])],[(0,[z1,z2,z3,z217,z180,z6])],[(0,[z730,z47,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z731])]],
   [[(0,[z1,z732,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z733])],[(1,[z2,z734,z4,z5,z6]),(0,[z1,z2,z3,z4,z735,z6])],[(0,[z736,z1,z2,z3,z4,z5]),(0,[z63,z1,z3,z4,z5,z196]),(0,[z1,z2,z3,z4,z5,z737])],[(0,[z1,z2,z738,z3,z4,z5]),(0,[z1,z739,z2,z3,z4,z5])],[(0,[z1,z2,z375,z4,z5,z99]),(0,[z740,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z741,z5,z6]),(0,[z1,z2,z3,z4,z5,z742])],[(0,[z1,z2,z3,z4,z5,z743]),(0,[z744,z1,z2,z3,z4,z5]),(0,[z1,z17,z2,z3,z243,z5]),(0,[z1,z2,z3,z4,z230,z497])],[(0,[z424,z1,z2,z4,z5,z24]),(0,[z1,z2,z3,z311,z265,z6]),(0,[z1,z2,z3,z4,z5,z125])],[(0,[z1,z2,z3,z5,z6,z745]),(0,[z1,z2,z3,z4,z56,z440]),(0,[z1,z2,z3,z4,z5,z746]),(0,[z266,z1,z3,z4,z5,z196]),(0,[z1,z747,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z142])],[(1,[z1,z748,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z749]),(0,[z1,z2,z3,z411,z18,z6])],[(0,[z1,z2,z3,z4,z5,z171]),(0,[z69,z2,z3,z750,z5,z6]),(0,[z70,z2,z582,z3,z5,z6]),(0,[z1,z2,z3,z4,z751,z6]),(0,[z1,z493,z2,z3,z5,z299]),(0,[z41,z1,z748,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z752]),(0,[z1,z2,z3,z753,z5,z6])],[(0,[z754,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z180,z26]),(0,[z74,z63,z1,z3,z34,z5])],[(0,[z755,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z256,z6])],[(0,[z84,z2,z3,z4,z5,z93])],[(0,[z1,z2,z3,z4,z5,z756]),(0,[z757,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z489,z47,z3,z4,z5]),(0,[z225,z84,z2,z3,z4,z5]),(0,[z63,z140,z17,z3,z4,z5])],[(0,[z1,z2,z3,z4,z230,z24]),(0,[z1,z2,z758,z4,z5,z24]),(0,[z1,z2,z3,z759,z4,z5]),(0,[z43,z84,z2,z3,z4,z5]),(0,[z63,z1,z2,z3,z4,z760]),(0,[z1,z53,z2,z4,z62,z110])],[(0,[z761,z1,z2,z3,z4,z5]),(0,[z1,z2,z138,z762,z5,z6])],[],[(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z2,z3,z4,z5,z764]),(0,[z1,z765,z2,z3,z4,z5]),(0,[z1,z2,z3,z766,z5,z6]),(0,[z1,z2,z3,z4,z5,z767]),(0,[z1,z2,z4,z735,z62,z6]),(0,[z1,z2,z3,z4,z5,z768])],[(0,[z1,z2,z3,z4,z5,z769])],[(0,[z1,z489,z2,z3,z4,z5]),(0,[z55,z408,z72,z3,z4,z5]),(0,[z1,z770,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z771]),(0,[z43,z1,z2,z3,z606,z5]),(0,[z63,z1,z53,z2,z4,z62]),(0,[z1,z595,z2,z3,z5,z100]),(0,[z1,z2,z3,z4,z309,z12]),(0,[z772,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z773,z5,z6]),(0,[z266,z1,z3,z4,z5,z48]),(0,[z1,z2,z207,z4,z5,z6])],[(0,[z1,z2,z3,z197,z252,z6])],[(0,[z1,z2,z3,z4,z5,z774]),(0,[z1,z2,z3,z291,z4,z5]),(0,[z37,z1,z239,z2,z3,z6]),(0,[z1,z2,z3,z4,z5,z775])],[],[(0,[z1,z776,z2,z3,z4,z5]),(0,[z63,z1,z283,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z39])],[(0,[z1,z2,z3,z4,z5,z777]),(0,[z2,z313,z3,z4,z5,z26]),(0,[z1,z778,z2,z3,z4,z5])],[(0,[z63,z779,z2,z3,z4,z5]),(0,[z1,z2,z3,z762,z5,z6]),(0,[z1,z2,z411,z4,z18,z6])],[(0,[z1,z780,z2,z3,z4,z5]),(0,[z1,z2,z4,z5,z49,z781])],[(0,[z1,z2,z3,z4,z782,z6]),(0,[z101,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z243,z5,z6]),(0,[z1,z2,z783,z4,z5,z6]),(0,[z84,z2,z3,z4,z5,z542]),(0,[z1,z2,z3,z4,z5,z784])]],
   [[(0,[z51,z2,z3,z4,z87,z26]),(0,[z785,z2,z3,z4,z5,z6]),(0,[z1,z786,z2,z3,z4,z6])],[(0,[z1,z2,z3,z787,z4,z5]),(0,[z1,z2,z3,z4,z5,z80])],[(0,[z1,z2,z3,z4,z5,z788]),(0,[z1,z789,z2,z3,z4,z5]),(0,[z457,z2,z3,z4,z5,z24])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z1,z17,z2,z3,z4,z195])],[(0,[z23,z84,z2,z3,z4,z5]),(0,[z74,z1,z3,z34,z5,z24]),(0,[z1,z2,z3,z235,z5,z49])],[(0,[z71,z19,z47,z4,z5,z6]),(0,[z1,z145,z3,z4,z5,z24]),(0,[z1,z2,z790,z3,z4,z6]),(0,[z70,z17,z2,z3,z104,z5]),(0,[z84,z53,z2,z3,z4,z5]),(0,[z1,z2,z3,z136,z644,z6]),(0,[z1,z2,z3,z791,z5,z6])],[(0,[z1,z2,z3,z4,z5,z792]),(0,[z1,z17,z2,z207,z4,z5])],[(0,[z1,z101,z2,z3,z4,z5])],[(0,[z63,z1,z2,z3,z4,z265]),(0,[z1,z52,z3,z4,z121,z6])],[(0,[z424,z2,z47,z4,z5,z26]),(0,[z1,z2,z3,z4,z793,z26]),(0,[z1,z17,z2,z411,z4,z5])],[(0,[z1,z52,z499,z3,z4,z6]),(0,[z1,z2,z3,z5,z274,z26]),(0,[z1,z2,z3,z4,z5,z122])],[(0,[z794,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z120]),(0,[z1,z239,z2,z3,z5,z373]),(0,[z1,z2,z3,z4,z5,z795]),(0,[z1,z2,z207,z4,z5,z58])],[(0,[z1,z2,z3,z4,z796,z5]),(0,[z1,z2,z599,z4,z115,z6])],[(0,[z1,z2,z3,z4,z797,z6]),(0,[z1,z2,z3,z4,z5,z798]),(0,[z1,z17,z2,z3,z4,z799])],[(1,[z266,z47,z3,z4,z5]),(0,[z1,z800,z2,z3,z4,z5]),(0,[z469,z84,z2,z3,z4,z5]),(0,[z1,z650,z2,z4,z62,z6])],[(0,[z1,z145,z3,z4,z56,z6]),(0,[z1,z801,z3,z4,z5,z6]),(0,[z84,z2,z3,z90,z4,z5]),(0,[z367,z2,z3,z4,z5,z26]),(0,[z374,z84,z2,z3,z4,z5])]],
   [[(0,[z1,z802,z3,z4,z5,z6]),(0,[z69,z2,z3,z92,z5,z39]),(0,[z1,z2,z3,z197,z5,z24]),(0,[z63,z140,z2,z3,z4,z5]),(0,[z63,z803,z2,z3,z4,z5]),(0,[z1,z2,z3,z520,z5,z13])],[(0,[z38,z1,z2,z226,z3,z6]),(0,[z1,z2,z3,z4,z5,z804]),(0,[z63,z805,z2,z3,z4,z5])],[(0,[z1,z2,z138,z217,z5,z26]),(0,[z1,z2,z3,z806,z4,z5]),(0,[z1,z2,z3,z136,z807,z6])],[(0,[z41,z1,z9,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z808]),(0,[z1,z809,z2,z3,z4,z5]),(0,[z63,z1,z2,z3,z136,z129])],[(0,[z810,z1,z2,z3,z4,z5]),(0,[z1,z128,z3,z30,z5,z24]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z1,z17,z2,z3,z4,z180])],[(0,[z1,z2,z734,z4,z5,z6]),(0,[z1,z2,z3,z4,z807,z6])],[(0,[z1,z77,z2,z78,z180,z6])],[(0,[z424,z1,z9,z4,z5,z6]),(0,[z1,z60,z2,z3,z4,z93]),(0,[z1,z2,z3,z4,z180,z6])],[],[(0,[z1,z2,z3,z812,z5,z6])],[(0,[z1,z2,z3,z4,z5,z813]),(0,[z1,z2,z814,z4,z5,z24]),(0,[z148,z1,z2,z3,z4,z93]),(0,[z84,z2,z141,z3,z4,z5])],[(0,[z1,z2,z3,z5,z6,z815]),(0,[z1,z816,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z373]),(0,[z817,z1,z3,z4,z5,z6])],[(0,[z1,z818,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z819]),(0,[z1,z133,z2,z164,z4,z5])],[(0,[z1,z2,z3,z311,z5,z26]),(0,[z1,z53,z2,z4,z62,z6])],[(0,[z1,z2,z3,z290,z5,z26]),(0,[z1,z2,z3,z4,z5,z820])],[(0,[z140,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z821,z6]),(0,[z1,z2,z3,z4,z5,z103]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z1,z17,z2,z3,z5,z274]),(0,[z1,z3,z4,z5,z150,z823]),(0,[z1,z341,z2,z4,z5,z99])]],
   [[(0,[z1,z2,z3,z246,z5,z24]),(1,[z1,z3,z4,z5,z823]),(0,[z369,z1,z2,z78,z5,z6])],[(0,[z185,z1,z3,z4,z5,z303]),(0,[z1,z2,z3,z4,z5,z390]),(0,[z1,z824,z2,z3,z4,z5]),(0,[z1,z2,z3,z98,z5,z825])],[(0,[z1,z2,z3,z4,z826,z6]),(0,[z1,z2,z3,z311,z5,z240]),(0,[z84,z2,z3,z4,z827,z5])],[(0,[z131,z283,z90,z4,z5,z6])],[(0,[z2,z3,z4,z284,z828,z6]),(0,[z63,z1,z2,z3,z829,z5])],[(0,[z1,z2,z3,z4,z830,z6]),(0,[z1,z60,z2,z3,z4,z233]),(0,[z1,z831,z2,z3,z5,z6]),(0,[z140,z84,z2,z3,z4,z5]),(1,[z1,z2,z246,z62,z6])],[(0,[z1,z832,z2,z3,z4,z5]),(0,[z84,z2,z3,z164,z4,z5]),(0,[z1,z2,z411,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z833])],[(0,[z1,z2,z3,z834,z5,z6])],[(0,[z424,z71,z47,z4,z5,z6]),(0,[z1,z2,z3,z835,z5,z24]),(0,[z1,z17,z2,z3,z4,z11]),(0,[z1,z2,z3,z4,z836,z5])],[(0,[z1,z2,z226,z19,z5,z6]),(0,[z1,z2,z3,z4,z5,z837]),(0,[z1,z2,z3,z4,z5,z838])],[(0,[z1,z2,z3,z4,z839,z24]),(0,[z449,z2,z3,z4,z5,z24])],[(0,[z1,z2,z3,z445,z5,z24]),(0,[z51,z2,z3,z4,z87,z6]),(0,[z1,z276,z2,z3,z4,z389]),(0,[z1,z2,z4,z78,z180,z6])],[(0,[z424,z63,z1,z2,z4,z5]),(0,[z1,z2,z3,z4,z5,z840]),(0,[z1,z2,z411,z4,z129,z6])],[(0,[z71,z17,z47,z3,z4,z5]),(0,[z1,z2,z205,z4,z115,z6]),(0,[z1,z841,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z842])],[(0,[z71,z47,z3,z4,z5,z24]),(0,[z131,z2,z90,z4,z5,z24]),(0,[z63,z1,z2,z3,z197,z5]),(1,[z1,z2,z3,z4,z843])]],
   [[(0,[z844,z1,z2,z3,z4,z5]),(1,[z1,z3,z845,z5,z6]),(0,[z442,z1,z17,z3,z4,z5])],[(0,[z2,z452,z3,z4,z5,z26]),(0,[z37,z1,z3,z4,z147,z24]),(0,[z1,z2,z3,z846,z5,z24]),(0,[z1,z17,z2,z3,z235,z5])],[(0,[z1,z2,z3,z4,z5,z847]),(0,[z63,z1,z2,z138,z217,z5]),(0,[z1,z17,z3,z4,z5,z570])],[(0,[z549,z47,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z793,z6]),(0,[z1,z2,z3,z478,z5,z100])],[(0,[z424,z1,z145,z4,z5,z6]),(0,[z1,z159,z2,z46,z3,z4]),(0,[z1,z2,z3,z445,z56,z6]),(0,[z2,z3,z4,z750,z5,z6]),(0,[z1,z2,z3,z5,z274,z6])],[(0,[z848,z1,z2,z3,z4,z5]),(0,[z1,z77,z2,z78,z5,z382])],[(0,[z71,z0,z47,z3,z5,z6]),(0,[z154,z2,z146,z4,z5,z26]),(0,[z2,z3,z4,z5,z849,z6]),(0,[z850,z84,z2,z3,z4,z5]),(0,[z84,z2,z3,z4,z78,z5]),(0,[z63,z851,z2,z3,z4,z5]),(0,[z84,z60,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z382])],[(0,[z1,z2,z3,z4,z265,z26]),(0,[z852,z2,z3,z4,z5,z6]),(0,[z853,z1,z2,z3,z4,z5])],[(0,[z131,z2,z90,z4,z56,z6]),(0,[z1,z2,z3,z854,z5,z6]),(0,[z63,z1,z2,z3,z834,z5]),(0,[z2,z3,z4,z5,z855,z6]),(0,[z1,z2,z3,z4,z5,z856])],[(0,[z63,z0,z1,z2,z3,z5]),(0,[z1,z2,z141,z315,z4,z5])],[(0,[z1,z101,z2,z226,z3,z5]),(0,[z1,z2,z3,z4,z11,z360]),(0,[z84,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z857,z5,z6]),(0,[z1,z2,z3,z4,z5,z858]),(0,[z1,z2,z3,z4,z473,z26]),(0,[z37,z1,z3,z4,z373,z147]),(0,[z84,z2,z3,z4,z5,z12])],[(0,[z1,z2,z3,z4,z265,z240]),(0,[z1,z2,z3,z859,z5,z6]),(0,[z1,z2,z138,z217,z5,z6])],[(0,[z51,z2,z3,z4,z87,z295]),(0,[z1,z2,z3,z4,z5,z860]),(0,[z1,z2,z3,z4,z861,z6])],[]],
   [[(0,[z1,z2,z3,z4,z5,z862]),(0,[z1,z2,z3,z4,z5,z863]),(0,[z1,z2,z3,z4,z5,z864]),(0,[z1,z128,z3,z655,z5,z6])],[(0,[z1,z2,z411,z4,z5,z26]),(0,[z1,z68,z2,z3,z18,z24]),(0,[z84,z2,z3,z9,z4,z5]),(0,[z1,z2,z3,z4,z5,z865]),(0,[z84,z2,z275,z3,z4,z5]),(0,[z84,z227,z2,z3,z4,z5])],[(0,[z1,z2,z866,z4,z5,z6]),(0,[z84,z2,z3,z4,z284,z5]),(0,[z1,z2,z3,z4,z6,z867]),(0,[z1,z53,z2,z246,z62,z6])],[(0,[z1,z868,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z869]),(0,[z1,z2,z4,z115,z735,z6])],[],[(0,[z2,z47,z3,z4,z5,z608]),(1,[z2,z3,z4,z828,z6]),(0,[z1,z2,z3,z4,z11,z26]),(0,[z870,z2,z3,z4,z5,z6]),(0,[z1,z301,z2,z3,z4,z112]),(0,[z1,z661,z2,z3,z4,z112])],[],[(0,[z1,z2,z4,z871,z5,z6]),(0,[z458,z2,z3,z4,z87,z6]),(0,[z1,z2,z3,z4,z5,z872]),(0,[z1,z2,z3,z4,z5,z873]),(0,[z1,z17,z3,z4,z5,z613]),(0,[z2,z3,z4,z5,z874,z6])],[(0,[z1,z2,z3,z311,z5,z6]),(0,[z1,z17,z3,z4,z5,z561]),(0,[z662,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z875])],[(0,[z2,z3,z4,z828,z87,z6]),(0,[z63,z1,z77,z2,z78,z5]),(0,[z1,z2,z3,z290,z5,z6])],[(0,[z1,z2,z46,z3,z4,z26]),(0,[z715,z1,z283,z3,z4,z5]),(0,[z876,z1,z2,z3,z4,z5]),(0,[z1,z2,z877,z3,z4,z5])],[(0,[z878,z2,z3,z4,z5,z6]),(0,[z74,z1,z3,z383,z5,z6])],[(0,[z1,z2,z3,z879,z5,z6]),(0,[z1,z2,z3,z4,z5,z880])],[(0,[z881,z1,z2,z3,z4,z6]),(0,[z1,z364,z2,z3,z5,z27]),(0,[z1,z2,z3,z4,z5,z882])],[(0,[z1,z2,z3,z4,z883,z6]),(0,[z1,z2,z3,z4,z5,z884]),(0,[z63,z1,z128,z3,z30,z5]),(0,[z84,z2,z3,z4,z5,z885])],[(0,[z2,z3,z4,z5,z450,z24]),(0,[z63,z1,z52,z3,z4,z121]),(0,[z1,z280,z2,z3,z5,z100])]],
   [[(0,[z1,z2,z3,z886,z4,z6]),(0,[z1,z2,z887,z3,z4,z5]),(0,[z1,z2,z421,z217,z5,z6]),(0,[z191,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z606,z5,z13])],[(0,[z63,z1,z239,z2,z3,z5]),(0,[z1,z2,z217,z762,z5,z6])],[(0,[z1,z2,z3,z4,z5,z888]),(0,[z1,z2,z3,z4,z5,z889])],[(0,[z1,z172,z10,z403,z5,z6])],[(0,[z2,z47,z3,z4,z5,z26]),(0,[z63,z1,z2,z3,z311,z5]),(0,[z63,z1,z2,z3,z4,z56]),(0,[z1,z2,z3,z4,z890,z5]),(0,[z1,z891,z2,z3,z5,z26]),(0,[z1,z2,z3,z4,z5,z892])],[(0,[z1,z2,z3,z4,z5,z893]),(0,[z2,z3,z4,z5,z24,z26]),(0,[z1,z17,z2,z3,z4,z252])],[(0,[z1,z172,z345,z4,z5,z6]),(0,[z1,z894,z3,z4,z5,z6]),(0,[z1,z2,z3,z136,z129,z26]),(0,[z1,z2,z3,z4,z895,z6]),(0,[z1,z2,z3,z4,z6,z896]),(0,[z1,z2,z3,z897,z5,z6])],[(0,[z1,z898,z2,z3,z4,z5])],[],[(0,[z424,z1,z2,z226,z5,z6]),(0,[z1,z899,z2,z3,z4,z5]),(0,[z1,z900,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z901,z5]),(0,[z1,z2,z3,z4,z5,z843])],[(0,[z902,z1,z2,z3,z4,z5])],[(0,[z2,z730,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z903]),(0,[z1,z2,z3,z904,z5,z6]),(0,[z1,z2,z3,z4,z905,z6])],[(0,[z1,z2,z3,z4,z5,z906]),(0,[z1,z283,z3,z4,z5,z24]),(0,[z154,z2,z146,z4,z5,z81]),(0,[z1,z2,z3,z4,z5,z352]),(0,[z1,z2,z3,z4,z5,z907]),(0,[z1,z2,z3,z4,z908,z26]),(0,[z286,z1,z68,z2,z3,z6])],[(0,[z1,z2,z3,z909,z5,z6]),(0,[z1,z2,z3,z4,z5,z910]),(0,[z1,z2,z3,z4,z5,z911])],[(0,[z1,z912,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z913,z6]),(0,[z914,z84,z2,z3,z4,z5])]],
   [[(0,[z1,z159,z2,z19,z4,z5]),(0,[z70,z2,z3,z104,z5,z515]),(0,[z173,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z5,z26,z815]),(0,[z84,z133,z2,z3,z4,z5]),(0,[z1,z77,z17,z2,z78,z5]),(0,[z1,z2,z3,z290,z5,z110])],[(0,[z1,z915,z3,z4,z5,z6]),(0,[z1,z748,z9,z4,z5,z6]),(0,[z84,z2,z3,z4,z61,z5]),(0,[z1,z2,z3,z4,z5,z916])],[(0,[z154,z2,z146,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z917])],[(0,[z1,z2,z3,z235,z5,z24]),(0,[z63,z1,z2,z3,z4,z918])],[(0,[z37,z1,z3,z4,z708,z6]),(0,[z84,z2,z138,z3,z4,z5]),(0,[z84,z2,z3,z4,z447,z5]),(0,[z63,z1,z2,z3,z246,z5])],[],[(0,[z1,z2,z3,z4,z5,z919])],[(0,[z63,z1,z2,z3,z403,z5]),(0,[z1,z2,z3,z4,z473,z6]),(0,[z1,z128,z3,z30,z5,z120])],[(0,[z1,z2,z3,z4,z5,z920]),(0,[z1,z2,z3,z98,z5,z13])],[(0,[z1,z2,z545,z4,z5,z648]),(0,[z1,z2,z3,z246,z5,z80])],[(0,[z2,z3,z4,z5,z542,z26]),(0,[z1,z172,z10,z4,z5,z24])],[(0,[z1,z2,z3,z921,z5,z6])],[(0,[z1,z2,z3,z4,z5,z922]),(0,[z84,z2,z3,z217,z4,z5]),(0,[z1,z2,z411,z4,z5,z6])],[(0,[z63,z140,z3,z4,z5,z196]),(0,[z1,z2,z3,z149,z5,z100]),(0,[z1,z3,z4,z5,z923,z6])],[(0,[z1,z924,z3,z4,z5,z6]),(0,[z1,z2,z3,z311,z5,z440])],[(0,[z131,z2,z734,z4,z5,z6]),(0,[z925,z1,z2,z3,z4,z5]),(0,[z74,z1,z2,z411,z5,z6]),(0,[z63,z1,z296,z3,z4,z5])]],
   [[(0,[z55,z47,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z4,z230,z382])],[(0,[z63,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z926,z5,z6])],[(0,[z1,z2,z3,z4,z5,z927]),(0,[z1,z2,z3,z4,z752,z6]),(0,[z1,z2,z3,z129,z438,z6]),(0,[z1,z68,z2,z3,z18,z142])],[(0,[z1,z928,z3,z4,z5,z6]),(0,[z70,z2,z3,z104,z5,z24]),(0,[z1,z2,z3,z4,z5,z929])],[],[(0,[z1,z2,z3,z4,z930,z6]),(0,[z1,z2,z46,z3,z4,z6]),(0,[z1,z2,z931,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z932])],[(0,[z51,z17,z2,z3,z4,z87]),(0,[z190,z84,z2,z3,z4,z5])],[(0,[z74,z1,z417,z3,z5,z6]),(0,[z69,z2,z3,z92,z5,z103]),(0,[z1,z2,z3,z4,z5,z933])],[(0,[z71,z226,z47,z3,z5,z6]),(0,[z55,z730,z3,z4,z5,z6]),(0,[z1,z934,z2,z3,z4,z5]),(0,[z2,z3,z4,z591,z5,z26]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z84,z2,z3,z4,z5,z100]),(0,[z1,z17,z2,z165,z4,z115])],[(0,[z1,z2,z3,z4,z936,z6]),(0,[z1,z2,z937,z3,z4,z6]),(0,[z1,z2,z3,z4,z828,z6]),(0,[z2,z592,z3,z4,z5,z26]),(0,[z1,z276,z2,z3,z4,z24])],[(0,[z1,z2,z3,z4,z5,z31]),(0,[z1,z2,z3,z4,z5,z938])],[(0,[z131,z17,z2,z90,z4,z5]),(0,[z1,z2,z3,z4,z195,z26]),(0,[z63,z1,z344,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z939]),(0,[z84,z17,z2,z3,z4,z5]),(0,[z1,z17,z3,z4,z5,z150])],[(0,[z185,z1,z489,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z940]),(0,[z1,z2,z3,z941,z4,z5]),(0,[z1,z2,z3,z942,z5,z6])],[(0,[z37,z63,z1,z3,z4,z147]),(0,[z84,z2,z3,z4,z5,z62]),(0,[z1,z32,z2,z3,z4,z502]),(0,[z1,z60,z2,z3,z4,z843])],[(0,[z1,z891,z2,z3,z5,z6]),(0,[z154,z2,z734,z4,z5,z6]),(0,[z1,z943,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z944,z6])]],
   [[(0,[z1,z2,z945,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z946]),(0,[z1,z2,z411,z4,z5,z58])],[(0,[z1,z17,z2,z3,z4,z5]),(0,[z1,z947,z145,z3,z4,z5]),(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z949,z2,z3,z4,z5]),(0,[z1,z305,z2,z4,z62,z6]),(0,[z63,z1,z68,z2,z3,z18]),(0,[z1,z2,z3,z136,z129,z6])],[(0,[z1,z2,z3,z4,z5,z950]),(0,[z1,z2,z3,z951,z4,z5])],[(0,[z1,z2,z952,z4,z5,z6]),(0,[z63,z1,z3,z4,z5,z611])],[(0,[z23,z2,z3,z4,z5,z953]),(0,[z2,z3,z4,z5,z26,z384])],[(0,[z1,z2,z3,z4,z5,z954]),(0,[z1,z2,z3,z5,z13,z825])],[(0,[z1,z2,z3,z5,z6,z955]),(0,[z1,z2,z956,z3,z4,z5]),(0,[z1,z2,z3,z246,z115,z6])],[(0,[z1,z2,z3,z957,z5,z6]),(0,[z166,z2,z3,z4,z284,z24]),(0,[z1,z2,z958,z3,z4,z5]),(0,[z1,z698,z2,z3,z5,z100])],[(0,[z166,z2,z3,z4,z284,z568]),(0,[z1,z2,z3,z4,z5,z959]),(0,[z1,z2,z3,z4,z908,z6])],[(0,[z1,z2,z3,z4,z265,z440]),(0,[z1,z239,z2,z3,z5,z26]),(0,[z464,z2,z65,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z608]),(0,[z1,z77,z2,z762,z5,z6])],[(0,[z1,z2,z19,z4,z5,z26]),(0,[z1,z2,z3,z4,z960,z6])],[(0,[z1,z2,z3,z4,z5,z961]),(0,[z605,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z962])],[(0,[z1,z2,z3,z4,z5,z963]),(0,[z1,z2,z3,z4,z5,z964])],[(0,[z38,z1,z2,z3,z4,z24]),(0,[z965,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z235,z252,z6])],[(0,[z1,z2,z3,z4,z5,z360]),(0,[z1,z2,z3,z4,z966,z6])]],
   [[(0,[z63,z967,z2,z3,z4,z5]),(0,[z1,z2,z165,z246,z5,z6])],[(0,[z1,z2,z3,z4,z5,z320]),(0,[z2,z3,z4,z5,z26,z413])],[],[(0,[z0,z1,z2,z46,z3,z6]),(0,[z286,z63,z1,z3,z4,z5])],[(0,[z84,z2,z3,z4,z5,z26]),(0,[z605,z72,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z295]),(0,[z1,z2,z3,z4,z252,z24]),(0,[z63,z84,z17,z3,z4,z5]),(0,[z968,z1,z2,z3,z4,z5])],[(0,[z1,z145,z3,z311,z5,z6]),(0,[z2,z3,z734,z4,z5,z6]),(0,[z1,z2,z3,z969,z5,z6]),(0,[z1,z2,z3,z403,z5,z24]),(0,[z1,z17,z2,z3,z4,z473])],[(0,[z1,z2,z3,z4,z5,z970]),(0,[z1,z971,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z972,z5]),(0,[z1,z2,z3,z260,z5,z213]),(0,[z1,z379,z2,z3,z4,z5]),(0,[z1,z17,z2,z3,z4,z256]),(0,[z1,z2,z3,z4,z5,z973])],[(0,[z1,z974,z2,z3,z4,z5]),(0,[z464,z84,z2,z3,z4,z5]),(0,[z975,z2,z3,z4,z5,z6]),(0,[z374,z1,z2,z164,z4,z5]),(0,[z189,z1,z2,z3,z236,z5])],[(0,[z1,z2,z3,z976,z5,z6]),(0,[z1,z77,z2,z78,z5,z26]),(0,[z1,z2,z3,z4,z977,z6])],[(0,[z1,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z978,z5]),(0,[z1,z2,z3,z4,z5,z979])],[(0,[z1,z2,z3,z4,z5,z980]),(0,[z2,z3,z4,z5,z953,z26])],[(0,[z1,z981,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z982])],[],[(0,[z185,z1,z2,z3,z4,z5]),(0,[z41,z1,z291,z9,z4,z5]),(0,[z1,z446,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z389,z5]),(0,[z1,z983,z2,z3,z4,z5]),(0,[z1,z391,z2,z3,z18,z6]),(0,[z1,z2,z3,z4,z5,z984])],[(0,[z63,z1,z2,z46,z3,z4]),(0,[z1,z2,z3,z4,z5,z240]),(0,[z1,z2,z3,z4,z5,z985]),(0,[z627,z2,z3,z4,z5,z26]),(0,[z158,z2,z3,z4,z5,z26]),(0,[z469,z1,z2,z3,z447,z5]),(0,[z1,z17,z2,z3,z4,z230])],[(0,[z1,z72,z489,z3,z4,z5]),(0,[z594,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z4,z5,z986]),(0,[z1,z2,z4,z762,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z987]),(0,[z1,z2,z3,z4,z5,z988]),(0,[z1,z2,z3,z4,z5,z989]),(0,[z1,z248,z2,z375,z4,z5]),(0,[z1,z349,z2,z3,z4,z112]),(0,[z1,z2,z411,z5,z18,z6])],[(0,[z2,z3,z4,z5,z24,z470]),(0,[z1,z2,z3,z4,z5,z990])],[(0,[z1,z2,z3,z4,z203,z168]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z84,z2,z3,z136,z4,z5])],[(0,[z1,z2,z3,z992,z5,z6]),(0,[z1,z2,z3,z4,z5,z993])],[(0,[z55,z17,z72,z3,z4,z5]),(0,[z1,z2,z3,z136,z692,z6])],[],[(0,[z1,z2,z3,z4,z265,z6]),(0,[z1,z2,z3,z4,z994,z6]),(0,[z63,z1,z276,z2,z3,z4]),(0,[z1,z2,z3,z4,z5,z995]),(0,[z1,z2,z3,z4,z195,z6])],[(0,[z55,z72,z3,z4,z5,z24])],[(0,[z1,z2,z3,z4,z5,z996]),(0,[z350,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z997])],[(0,[z1,z2,z46,z226,z3,z6]),(0,[z1,z2,z3,z5,z998,z6]),(0,[z1,z999,z2,z3,z4,z5]),(0,[z1,z1000,z2,z3,z4,z5])],[(0,[z1,z283,z3,z4,z56,z6]),(0,[z1,z2,z1001,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z823])],[(0,[z1,z2,z3,z4,z5,z1002])],[(0,[z1,z3,z748,z4,z5,z6]),(0,[z2,z3,z4,z5,z1003,z6]),(0,[z1,z1004,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1005]),(0,[z1,z2,z1006,z4,z5,z6]),(0,[z1,z2,z3,z25,z5,z402])],[(0,[z1,z177,z2,z3,z4,z16]),(0,[z84,z2,z3,z4,z34,z5])],[(0,[z1,z17,z2,z3,z445,z5])]],
   [[(0,[z38,z2,z47,z3,z4,z26]),(0,[z2,z46,z47,z3,z4,z26]),(0,[z1,z145,z3,z4,z265,z6]),(0,[z1,z2,z3,z4,z5,z1007]),(0,[z63,z1,z218,z3,z4,z5])],[(0,[z71,z2,z65,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1008]),(0,[z2,z3,z4,z5,z54,z26]),(0,[z1,z172,z10,z243,z5,z6]),(0,[z1,z446,z2,z3,z4,z473]),(0,[z1,z2,z3,z4,z389,z473])],[(0,[z600,z2,z3,z4,z5,z24]),(0,[z1,z52,z3,z4,z121,z245])],[(0,[z1,z2,z3,z1009,z5,z6]),(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z1011,z2,z3,z5,z6]),(0,[z1,z2,z3,z1012,z5,z24]),(0,[z1,z2,z3,z4,z5,z1013])],[(0,[z1,z2,z3,z1014,z5,z6]),(0,[z1,z239,z2,z3,z5,z6])],[(0,[z1,z17,z2,z226,z3,z5]),(0,[z424,z1,z2,z46,z4,z6]),(0,[z1015,z1,z2,z3,z4,z5]),(0,[z37,z1,z2,z411,z4,z6]),(0,[z84,z2,z3,z606,z4,z5]),(1,[z1,z2,z4,z5,z781]),(0,[z1,z2,z3,z129,z807,z6])],[(0,[z1,z2,z19,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1016]),(0,[z63,z55,z72,z3,z4,z5]),(0,[z1,z2,z3,z4,z56,z24]),(0,[z1,z17,z267,z3,z4,z5]),(0,[z74,z1,z17,z3,z34,z5]),(1,[z1,z2,z3,z5,z825])],[(0,[z1,z2,z3,z1017,z5,z6]),(0,[z1,z2,z3,z4,z5,z1018]),(0,[z166,z2,z3,z4,z284,z212]),(0,[z2,z3,z4,z5,z26,z496])],[(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z138,z304,z5,z6]),(0,[z1,z2,z3,z5,z807,z6])],[(0,[z1,z2,z1020,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z2,z3,z4,z5,z1022]),(0,[z84,z77,z2,z3,z4,z5])],[(0,[z1,z2,z226,z3,z5,z26]),(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z3,z4,z5,z1024]),(0,[z266,z84,z2,z3,z4,z5]),(0,[z1025,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z290,z5])],[(0,[z41,z1,z379,z9,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1026]),(0,[z166,z2,z592,z3,z4,z6]),(0,[z1,z2,z141,z4,z5,z553])],[(0,[z1027,z2,z3,z4,z5,z6]),(0,[z1,z1028,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1029]),(0,[z1,z2,z3,z4,z180,z497]),(0,[z1,z133,z2,z4,z195,z99])],[(0,[z1,z17,z172,z10,z4,z5])],[(0,[z71,z84,z2,z3,z4,z5]),(0,[z84,z2,z3,z4,z5,z6]),(0,[z266,z1,z408,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z81]),(0,[z131,z2,z90,z311,z5,z6]),(0,[z1,z1030,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1031]),(0,[z1,z2,z3,z4,z5,z1032])]],
   [[(0,[z74,z1,z276,z3,z34,z6]),(0,[z1,z2,z3,z4,z5,z1033])],[(0,[z127,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z1034,z4,z5]),(0,[z1,z128,z3,z5,z539,z6]),(0,[z1,z2,z141,z4,z5,z49])],[(0,[z1,z2,z3,z4,z5,z1035]),(0,[z71,z38,z47,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1036]),(0,[z1,z2,z4,z5,z24,z1037]),(0,[z1,z2,z3,z4,z1038,z5]),(0,[z63,z1039,z2,z3,z4,z5])],[(0,[z55,z2,z3,z4,z5,z764]),(0,[z1,z1040,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1041]),(0,[z1,z68,z578,z2,z3,z6]),(0,[z1,z77,z2,z78,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z72,z2,z65,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1042]),(0,[z1,z1043,z2,z3,z4,z26])],[(0,[z1,z1044,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z953,z6])],[(0,[z699,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z5,z825,z100])],[(0,[z63,z1,z145,z3,z4,z5]),(0,[z63,z70,z2,z3,z104,z5]),(0,[z1,z2,z3,z4,z5,z1045]),(0,[z1,z17,z3,z4,z456,z5])],[(0,[z71,z159,z47,z3,z4,z5]),(0,[z424,z1,z2,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z1046]),(0,[z1,z53,z17,z2,z4,z62])],[(0,[z63,z1,z2,z19,z4,z5]),(0,[z408,z2,z65,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1047])],[(0,[z1,z2,z232,z4,z5,z553])],[],[(0,[z266,z2,z47,z3,z4,z5]),(0,[z63,z154,z2,z146,z4,z5]),(0,[z1,z2,z3,z4,z195,z99])],[(0,[z1,z1048,z2,z3,z4,z6])],[(0,[z1,z53,z2,z4,z62,z24]),(0,[z1,z2,z3,z4,z5,z1049]),(0,[z1,z2,z3,z829,z5,z6]),(0,[z63,z84,z3,z4,z5,z196]),(0,[z1,z2,z3,z4,z5,z1050])],[(0,[z84,z2,z3,z4,z351,z5])]],
   [[(0,[z140,z2,z3,z4,z5,z24]),(0,[z1,z3,z30,z845,z5,z6])],[(0,[z1,z2,z3,z1051,z5,z6]),(0,[z1,z2,z3,z4,z5,z1052])],[(0,[z1,z2,z3,z4,z230,z26]),(0,[z1,z68,z2,z207,z18,z6]),(0,[z1,z2,z3,z4,z61,z12])],[(0,[z1,z2,z3,z4,z5,z20]),(0,[z1,z172,z10,z4,z5,z390]),(0,[z1,z2,z3,z4,z1053,z6])],[(0,[z0,z1,z17,z2,z3,z5]),(0,[z263,z84,z2,z3,z4,z5])],[(0,[z1,z1054,z3,z4,z5,z6]),(0,[z1,z10,z748,z4,z5,z6]),(0,[z74,z1,z446,z3,z34,z5]),(0,[z1,z2,z3,z4,z5,z1055]),(0,[z1,z209,z2,z3,z18,z6]),(0,[z1,z68,z2,z411,z18,z6])],[(0,[z1,z2,z3,z4,z5,z1056]),(0,[z41,z63,z1,z9,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1057]),(0,[z1,z17,z2,z3,z4,z1053]),(0,[z1,z238,z2,z3,z5,z100])],[(0,[z1,z2,z3,z4,z5,z1058]),(0,[z2,z3,z104,z750,z5,z6]),(0,[z63,z1,z2,z1059,z4,z5]),(0,[z84,z2,z3,z4,z5,z150]),(0,[z84,z2,z3,z4,z5,z112]),(0,[z1,z2,z3,z4,z5,z58])],[(0,[z1,z159,z2,z3,z4,z5]),(1,[z84,z2,z3,z4,z5]),(0,[z458,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z741,z5,z24]),(0,[z1,z239,z52,z2,z3,z6]),(0,[z1,z2,z3,z1060,z5,z6])],[(0,[z55,z72,z3,z4,z5,z171]),(0,[z1,z1061,z2,z3,z4,z5]),(0,[z41,z84,z2,z3,z4,z5]),(0,[z1062,z1,z2,z3,z4,z5])],[(0,[z2,z19,z47,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z1063]),(0,[z1,z2,z3,z4,z5,z110]),(0,[z1,z133,z2,z4,z5,z99])],[(0,[z1,z2,z3,z5,z6,z825])],[(0,[z1,z2,z3,z4,z1064,z6]),(0,[z84,z2,z2,z3,z4,z5]),(0,[z1,z17,z2,z3,z1065,z5]),(0,[z1,z1066,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z6,z843])],[(0,[z1,z2,z3,z4,z1067,z6]),(0,[z1,z2,z3,z1068,z4,z5])],[(0,[z266,z1,z72,z3,z4,z5]),(1,[z2,z3,z750,z5,z6]),(0,[z1,z2,z3,z4,z751,z24]),(0,[z1,z276,z17,z2,z3,z4]),(0,[z1,z2,z3,z4,z5,z1069])]],
   [[(0,[z1,z172,z145,z4,z5,z6]),(0,[z1070,z1,z2,z3,z4,z5]),(0,[z51,z2,z3,z4,z828,z6]),(0,[z1,z2,z1071,z3,z4,z5])],[(0,[z1,z2,z3,z4,z256,z24]),(0,[z1,z2,z3,z1072,z5,z6]),(0,[z1,z2,z3,z4,z5,z1073])],[(0,[z1,z172,z10,z4,z256,z6]),(0,[z1,z2,z3,z4,z1074,z5])],[(0,[z47,z3,z4,z5,z561,z26]),(0,[z1,z2,z3,z4,z1075,z6]),(0,[z1,z2,z3,z4,z5,z1076]),(0,[z1,z17,z3,z4,z5,z550]),(0,[z1,z89,z2,z78,z5,z6]),(0,[z1,z2,z4,z5,z735,z6])],[(0,[z1,z2,z3,z4,z1077,z6]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1,z2,z3,z1079,z5,z6])],[(0,[z1,z2,z226,z3,z5,z6]),(0,[z55,z408,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1080]),(0,[z74,z1,z3,z34,z5,z26]),(0,[z1,z2,z3,z4,z347,z285]),(0,[z84,z2,z3,z4,z5,z99]),(0,[z1081,z1,z3,z4,z5,z6])],[(0,[z1,z145,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z1082]),(0,[z1,z1083,z2,z3,z4,z5]),(0,[z63,z1,z3,z4,z5,z548])],[(0,[z1,z2,z141,z4,z5,z781])],[(0,[z1,z255,z2,z4,z5,z214]),(0,[z1,z2,z3,z4,z5,z1084]),(0,[z84,z2,z3,z30,z4,z5]),(0,[z63,z1,z2,z1085,z4,z5]),(0,[z1,z2,z275,z4,z5,z49])],[(0,[z1,z2,z3,z4,z1086,z6]),(0,[z408,z2,z47,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z3,z4,z729,z6]),(0,[z37,z1,z3,z4,z431,z6]),(0,[z1,z2,z3,z4,z5,z1088])],[(0,[z1,z2,z3,z4,z5,z440]),(0,[z1,z2,z3,z4,z5,z1089]),(0,[z63,z1,z2,z3,z243,z5])],[(0,[z1,z145,z3,z4,z5,z240]),(0,[z1090,z1,z2,z3,z4,z5]),(0,[z1,z2,z207,z4,z5,z24]),(0,[z1,z2,z3,z773,z5,z24]),(0,[z1,z2,z3,z4,z1091,z6]),(0,[z1,z2,z3,z4,z61,z843])],[(0,[z1,z330,z2,z3,z5,z274]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z1093,z2,z3,z5,z6])],[(0,[z1,z283,z3,z311,z5,z6])],[],[(0,[z1,z1043,z2,z3,z4,z6]),(0,[z1,z1094,z2,z4,z5,z26]),(0,[z531,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z1095]),(0,[z1,z2,z3,z246,z62,z6])]],
   [[],[(0,[z69,z2,z3,z92,z5,z26]),(0,[z1,z2,z3,z197,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1096]),(0,[z1,z2,z3,z4,z5,z1097]),(0,[z1,z3,z4,z121,z708,z6]),(0,[z225,z1,z2,z275,z4,z5])],[(0,[z424,z1,z2,z4,z5,z6]),(0,[z2,z3,z4,z5,z26,z303]),(0,[z1,z2,z3,z243,z5,z24])],[(0,[z1,z145,z3,z4,z5,z440]),(0,[z594,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z1098,z6]),(0,[z2,z3,z4,z5,z171,z26]),(0,[z1,z2,z3,z98,z5,z670])],[(0,[z424,z1,z17,z2,z4,z5]),(0,[z1,z2,z3,z4,z5,z1099])],[(0,[z0,z1,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z5,z1100]),(0,[z1,z17,z283,z3,z4,z5]),(0,[z84,z2,z3,z4,z121,z5]),(0,[z1,z17,z3,z4,z5,z823]),(0,[z1,z391,z2,z78,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1101]),(0,[z1,z1102,z2,z3,z4,z5]),(0,[z1103,z2,z3,z4,z5,z6]),(0,[z84,z2,z10,z3,z4,z5]),(0,[z1,z2,z3,z4,z195,z49])],[(0,[z47,z3,z9,z4,z5,z26]),(0,[z1104,z1,z2,z3,z4,z5]),(0,[z70,z84,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1105,z5,z6]),(0,[z84,z2,z3,z4,z5,z147])],[(0,[z1,z1106,z2,z3,z4,z6]),(0,[z2,z3,z4,z5,z764,z26])],[(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z52,z3,z4,z121,z24]),(0,[z63,z1,z2,z3,z4,z1108]),(0,[z63,z1,z2,z1109,z4,z5]),(0,[z1,z77,z2,z78,z230,z6]),(0,[z1,z2,z3,z377,z129,z6])],[(0,[z84,z72,z2,z3,z4,z5]),(0,[z1,z2,z758,z4,z5,z6]),(0,[z1,z2,z3,z4,z230,z6])],[(0,[z1110,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z403,z5,z390]),(0,[z1,z2,z3,z4,z61,z523]),(0,[z1,z2,z3,z197,z195,z6])],[(0,[z1,z2,z65,z3,z4,z5]),(0,[z70,z2,z3,z750,z5,z6])]],
   [[(0,[z1,z172,z532,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1111]),(0,[z632,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1112]),(0,[z1,z2,z3,z4,z5,z1113]),(0,[z1,z1114,z2,z3,z4,z5]),(0,[z1,z2,z3,z246,z5,z26]),(0,[z1,z1115,z2,z3,z4,z5]),(0,[z1,z2,z495,z4,z62,z6])],[(0,[z1,z1116,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z1117]),(1,[z1,z2,z78,z180,z6]),(0,[z1,z2,z165,z4,z735,z6])],[],[(0,[z1,z2,z4,z5,z6,z781])],[(0,[z1,z2,z3,z4,z5,z1118]),(0,[z1,z2,z3,z4,z502,z112])],[(0,[z1,z2,z3,z98,z5,z402]),(0,[z84,z172,z2,z3,z4,z5]),(0,[z1,z2,z165,z4,z66,z6])],[(0,[z63,z1,z2,z3,z4,z195])],[(0,[z71,z47,z3,z4,z5,z320]),(0,[z172,z47,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z708,z6]),(0,[z84,z84,z2,z3,z4,z5]),(0,[z1,z2,z596,z4,z5,z49])],[(0,[z0,z1,z159,z2,z3,z5]),(0,[z63,z1,z3,z4,z5,z303])],[(0,[z1,z2,z3,z4,z5,z1119]),(0,[z1,z2,z3,z1120,z5,z6]),(0,[z63,z1,z2,z207,z4,z5]),(0,[z1,z2,z170,z217,z5,z6]),(0,[z1,z2,z3,z4,z5,z1121])],[(0,[z1,z2,z3,z4,z180,z24]),(0,[z1,z2,z3,z4,z5,z1122]),(0,[z1123,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z445,z5,z26]),(0,[z805,z2,z3,z4,z5,z6]),(0,[z1124,z1,z2,z3,z4,z5])],[(0,[z1,z84,z2,z3,z4,z5]),(0,[z1,z159,z2,z226,z3,z5]),(0,[z1,z2,z3,z403,z256,z6]),(0,[z63,z1,z2,z411,z4,z5]),(0,[z1,z68,z2,z3,z807,z6])],[(0,[z84,z2,z3,z4,z92,z5])],[(0,[z51,z483,z2,z3,z4,z6]),(0,[z63,z1,z2,z1001,z4,z5])]],
   [[(0,[z71,z47,z3,z4,z5,z26]),(0,[z131,z2,z90,z4,z5,z26]),(0,[z74,z1,z3,z34,z5,z6]),(0,[z84,z2,z3,z98,z4,z5]),(0,[z317,z1,z17,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1125])],[(0,[z1,z145,z3,z4,z5,z6]),(0,[z1,z2,z3,z445,z5,z240]),(0,[z84,z2,z3,z4,z5,z49])],[(0,[z37,z1,z3,z4,z147,z26])],[(0,[z154,z2,z146,z4,z5,z24]),(0,[z1,z2,z3,z750,z5,z6]),(0,[z1,z2,z3,z4,z5,z1126])],[(0,[z1127,z1,z2,z3,z4,z5]),(0,[z63,z1,z365,z3,z4,z5]),(0,[z63,z1,z2,z3,z854,z5])],[(0,[z1,z2,z3,z4,z5,z1128]),(0,[z131,z2,z90,z4,z5,z240]),(0,[z1,z3,z845,z34,z5,z6]),(1,[z1,z2,z3,z807,z6])],[(0,[z1129,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z1130,z5,z6]),(0,[z1,z2,z3,z807,z18,z6])],[(0,[z464,z2,z3,z4,z5,z953]),(0,[z1,z53,z2,z4,z62,z80]),(1,[z1,z2,z4,z735,z6])],[(0,[z1,z2,z3,z1131,z5,z6]),(0,[z70,z2,z3,z104,z5,z352]),(0,[z1,z1132,z2,z3,z4,z5]),(0,[z1,z2,z3,z1133,z5,z26]),(0,[z1,z489,z3,z4,z5,z542]),(0,[z63,z1,z2,z3,z4,z180])],[(0,[z0,z2,z47,z3,z5,z26]),(0,[z1,z2,z3,z445,z265,z6]),(0,[z166,z2,z3,z4,z828,z6]),(0,[z1,z128,z3,z30,z5,z31])],[(0,[z84,z2,z47,z3,z4,z5]),(0,[z1,z1094,z2,z4,z5,z6]),(0,[z1,z2,z762,z78,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1134])],[(0,[z1,z2,z3,z4,z1135,z6]),(0,[z69,z2,z3,z92,z5,z6]),(0,[z1,z2,z3,z197,z5,z6]),(0,[z1,z656,z2,z78,z5,z6]),(0,[z1,z2,z207,z4,z5,z142])],[(0,[z424,z0,z1,z2,z5,z6]),(0,[z1,z2,z3,z4,z5,z1136]),(0,[z131,z2,z90,z4,z265,z6]),(0,[z1,z2,z411,z4,z5,z24])],[(0,[z1,z2,z3,z4,z1137,z6]),(0,[z84,z2,z3,z4,z5,z18])],[(0,[z51,z2,z3,z4,z87,z24]),(0,[z1,z2,z3,z78,z5,z497])]],
   [[(0,[z1,z101,z2,z46,z3,z4]),(1,[z1,z2,z411,z18,z6])],[(0,[z38,z1,z2,z19,z4,z6]),(0,[z1,z1138,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1139]),(0,[z1,z2,z3,z4,z11,z24])],[(0,[z1,z68,z2,z3,z18,z26]),(0,[z63,z1,z489,z3,z4,z5]),(0,[z1,z2,z748,z4,z5,z6]),(0,[z1,z172,z10,z4,z11,z6])],[(0,[z1,z2,z3,z4,z5,z1140]),(0,[z1,z128,z2,z411,z5,z6]),(0,[z1,z2,z3,z4,z5,z1141]),(0,[z63,z1,z2,z3,z5,z274]),(0,[z63,z1,z485,z3,z4,z5])],[(0,[z1142,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1143]),(0,[z63,z1,z2,z3,z1072,z5])],[(0,[z1,z2,z46,z3,z4,z24]),(0,[z1,z2,z3,z4,z5,z1144]),(0,[z1,z2,z814,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1145]),(0,[z1,z2,z1146,z4,z5,z6]),(0,[z1,z2,z3,z4,z760,z6])],[(0,[z55,z494,z3,z4,z5,z6]),(0,[z1,z2,z3,z243,z256,z6]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z185,z140,z2,z3,z4,z5]),(0,[z63,z1,z3,z4,z5,z689])],[(0,[z1,z2,z3,z4,z725,z6]),(0,[z157,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z5,z274,z24]),(0,[z1,z2,z3,z4,z5,z1148])],[(0,[z37,z84,z2,z3,z4,z5]),(0,[z84,z2,z3,z4,z115,z5])],[(0,[z424,z1,z159,z2,z4,z5]),(0,[z1,z2,z3,z4,z1149,z5]),(0,[z1,z2,z3,z4,z5,z1150]),(0,[z1151,z2,z3,z4,z5,z6]),(0,[z148,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z799,z6])],[(0,[z1,z2,z3,z4,z5,z1152]),(0,[z1,z1153,z2,z3,z4,z5]),(0,[z1,z227,z2,z3,z5,z27]),(0,[z63,z1,z2,z3,z4,z11]),(0,[z1,z2,z3,z246,z5,z6]),(0,[z1,z1154,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z388,z12])],[(0,[z1,z133,z2,z4,z5,z781])],[(0,[z1,z17,z2,z138,z217,z5]),(0,[z1,z2,z3,z4,z5,z1155])],[]],
   [[(0,[z1,z2,z3,z4,z5,z1156]),(0,[z154,z2,z146,z4,z5,z327]),(0,[z2,z146,z734,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1157])],[(0,[z1,z2,z4,z5,z6,z1158]),(0,[z51,z84,z2,z3,z4,z5]),(0,[z1,z2,z138,z217,z5,z24]),(0,[z1159,z2,z3,z4,z5,z6]),(0,[z1,z2,z1160,z4,z5,z6]),(0,[z1,z52,z3,z4,z564,z6]),(0,[z1,z2,z3,z217,z5,z497])],[],[(0,[z1,z133,z2,z197,z5,z99])],[(0,[z1,z2,z3,z1161,z4,z5]),(0,[z1,z2,z3,z4,z1162,z6]),(0,[z154,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z835,z5,z6]),(0,[z1,z2,z952,z4,z5,z24]),(0,[z1,z53,z2,z4,z735,z6]),(0,[z1,z2,z3,z4,z5,z1163])],[(0,[z63,z1,z2,z3,z235,z5]),(0,[z1,z17,z2,z3,z1130,z5]),(0,[z1,z2,z78,z62,z18,z6])],[(0,[z1,z2,z3,z4,z839,z6])],[(0,[z38,z1,z17,z2,z3,z4]),(0,[z1,z2,z3,z445,z5,z6]),(0,[z41,z1,z9,z4,z5,z26]),(0,[z1164,z1,z2,z3,z4,z5])],[(0,[z1,z128,z3,z30,z5,z26]),(0,[z1,z2,z3,z4,z1165,z6]),(0,[z1166,z1,z2,z3,z4,z5]),(0,[z1,z17,z610,z3,z4,z5]),(0,[z1167,z1,z2,z3,z4,z5])],[(0,[z84,z128,z2,z3,z4,z5])],[(0,[z307,z2,z3,z4,z5,z26]),(0,[z84,z2,z3,z4,z5,z196])],[(0,[z71,z47,z3,z4,z5,z6]),(0,[z131,z2,z90,z4,z5,z6]),(0,[z2,z3,z4,z5,z26,z181]),(0,[z432,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z1168,z6])],[(0,[z1,z2,z3,z311,z5,z24]),(0,[z1,z2,z3,z4,z1169,z6]),(0,[z1,z1170,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z781])],[(0,[z1,z1171,z2,z3,z5,z6]),(0,[z1,z2,z3,z846,z5,z6]),(0,[z1,z2,z3,z290,z5,z24]),(0,[z37,z1,z3,z4,z147,z6]),(0,[z84,z52,z2,z3,z4,z5])],[(0,[z1,z283,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z1172]),(0,[z63,z51,z2,z3,z4,z87])],[(0,[z1,z947,z2,z3,z4,z5]),(0,[z63,z1,z3,z4,z5,z94])]],
   [[(0,[z1,z2,z3,z260,z5,z13]),(0,[z1,z2,z3,z4,z5,z1173]),(0,[z1,z1174,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z351,z12]),(0,[z1,z117,z2,z3,z149,z5])],[(0,[z1,z172,z10,z4,z5,z360]),(0,[z1,z276,z446,z2,z3,z4])],[(0,[z1,z2,z1175,z3,z4,z5]),(0,[z464,z2,z3,z4,z5,z24]),(0,[z483,z2,z3,z4,z5,z26]),(0,[z1,z239,z17,z2,z3,z5])],[(0,[z1,z283,z3,z4,z5,z240]),(0,[z1,z2,z3,z1133,z5,z6]),(0,[z1,z2,z3,z246,z5,z110])],[(0,[z71,z47,z3,z4,z5,z608]),(0,[z1176,z1,z2,z3,z4,z6]),(0,[z1,z60,z2,z3,z4,z112])],[],[(0,[z71,z63,z47,z3,z4,z5]),(0,[z140,z2,z3,z4,z5,z171]),(0,[z1,z2,z3,z311,z56,z6])],[(0,[z1,z17,z2,z3,z4,z265]),(0,[z131,z127,z2,z4,z5,z6]),(0,[z1,z3,z4,z708,z147,z6])],[(0,[z1,z2,z3,z4,z5,z1177]),(0,[z2,z3,z4,z1178,z5,z6]),(0,[z1,z1179,z2,z3,z5,z6]),(0,[z37,z1,z17,z3,z4,z147])],[(0,[z2,z3,z4,z828,z5,z6]),(0,[z2,z3,z4,z5,z24,z953]),(0,[z1,z2,z3,z4,z1180,z6]),(0,[z1,z68,z2,z3,z292,z6])],[(0,[z1,z2,z3,z5,z1181,z6]),(0,[z1,z2,z3,z4,z1182,z6]),(0,[z1,z1183,z2,z3,z4,z5]),(0,[z63,z1,z313,z3,z4,z5]),(0,[z63,z1,z443,z3,z4,z5])],[(0,[z1,z101,z2,z19,z4,z5]),(0,[z1,z283,z3,z4,z265,z6]),(0,[z1,z1184,z2,z3,z4,z5]),(0,[z1,z172,z10,z4,z5,z26]),(0,[z575,z2,z3,z4,z5,z24]),(0,[z1,z172,z748,z4,z5,z6])],[(0,[z1,z2,z1185,z4,z5,z6]),(0,[z1186,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1187])],[(0,[z1,z2,z3,z1188,z5,z6]),(0,[z1,z493,z2,z3,z5,z100]),(0,[z1,z2,z3,z403,z11,z6]),(0,[z1,z2,z3,z4,z5,z1189]),(0,[z1,z68,z2,z3,z18,z6])],[(0,[z266,z47,z3,z4,z5,z26]),(0,[z2,z226,z47,z3,z5,z26]),(0,[z63,z38,z1,z2,z3,z4]),(0,[z1,z2,z4,z5,z6,z1037]),(0,[z37,z1,z658,z3,z4,z6]),(0,[z51,z2,z3,z4,z87,z125]),(0,[z74,z1,z3,z389,z34,z5]),(0,[z1,z330,z2,z3,z4,z5]),(0,[z1,z52,z3,z4,z121,z122]),(0,[z1,z2,z4,z246,z62,z6]),(0,[z1,z2,z411,z4,z5,z142])],[(0,[z1,z1190,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1191,z6])]],
   [[(0,[z1,z17,z2,z3,z311,z5]),(0,[z1,z17,z2,z3,z4,z56])],[(0,[z1,z2,z1192,z4,z5,z6]),(0,[z131,z63,z2,z90,z4,z5]),(0,[z1,z2,z3,z4,z5,z1193])],[(0,[z1,z2,z3,z5,z373,z274]),(0,[z1,z17,z2,z3,z136,z129]),(0,[z1,z2,z4,z5,z781,z99]),(0,[z1,z227,z2,z3,z5,z825])],[(0,[z1,z2,z3,z4,z5,z1194]),(0,[z1,z2,z3,z4,z913,z24]),(0,[z74,z1,z3,z845,z5,z6])],[(0,[z1,z981,z283,z3,z4,z5]),(0,[z70,z2,z3,z104,z5,z26]),(0,[z1,z89,z2,z4,z5,z99])],[(0,[z1,z420,z2,z78,z5,z6])],[(0,[z810,z1,z145,z3,z4,z5]),(0,[z803,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z473]),(0,[z1,z2,z3,z4,z5,z1195])],[(0,[z1,z2,z3,z4,z265,z24]),(0,[z1,z2,z3,z4,z5,z1196]),(0,[z1,z1197,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1198,z5,z6]),(0,[z1,z2,z3,z4,z1199,z6]),(0,[z1,z2,z3,z4,z5,z823])],[(0,[z1,z2,z3,z4,z5,z1200]),(0,[z1,z2,z3,z4,z5,z1201]),(1,[z2,z3,z4,z5,z953]),(0,[z63,z1,z2,z3,z4,z252])],[(0,[z1,z276,z2,z3,z4,z26])],[(0,[z71,z730,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z1202,z6]),(0,[z1,z2,z3,z1203,z5,z6]),(0,[z1,z2,z3,z4,z473,z24]),(0,[z1,z2,z3,z4,z115,z80])],[(0,[z63,z69,z2,z3,z92,z5]),(0,[z1204,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z24,z745]),(0,[z1,z2,z3,z243,z5,z390])],[(0,[z1,z2,z3,z445,z5,z440]),(0,[z63,z1,z184,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1205])],[(0,[z1,z2,z3,z1206,z5,z6]),(0,[z1207,z1,z2,z3,z4,z5])],[(0,[z1,z2,z1208,z4,z5,z6]),(0,[z1,z2,z3,z1209,z5,z6]),(0,[z1,z2,z3,z98,z236,z5]),(0,[z1,z3,z4,z5,z6,z1210])]],
   [[(0,[z84,z2,z1211,z3,z4,z5]),(0,[z1212,z84,z2,z3,z4,z5]),(0,[z1,z17,z2,z3,z246,z5])],[(0,[z131,z2,z90,z4,z5,z440]),(0,[z1,z17,z3,z616,z4,z5]),(0,[z1,z68,z2,z3,z18,z58])],[(0,[z1,z1213,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z515]),(0,[z63,z166,z2,z3,z4,z284]),(0,[z41,z1,z9,z4,z5,z6]),(0,[z1,z2,z3,z4,z1214,z6]),(0,[z1,z2,z3,z1065,z5,z6])],[(0,[z1,z128,z3,z30,z5,z6]),(0,[z1,z2,z1059,z4,z5,z6]),(0,[z1,z2,z3,z4,z918,z6])],[(0,[z1,z2,z3,z1215,z5,z6]),(0,[z590,z1,z17,z3,z4,z5])],[(0,[z424,z38,z1,z2,z4,z6]),(0,[z1,z239,z2,z3,z5,z24]),(0,[z1,z2,z3,z4,z5,z1216]),(0,[z63,z1,z17,z3,z4,z5])],[(0,[z1,z1217,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1218])],[(0,[z1,z1219,z3,z4,z5,z6]),(0,[z131,z84,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1220]),(0,[z2,z65,z3,z4,z5,z26]),(0,[z1,z2,z3,z845,z5,z6]),(0,[z1,z52,z3,z4,z708,z6])],[(0,[z1,z283,z3,z4,z5,z6]),(0,[z1,z77,z2,z78,z5,z497])],[(0,[z166,z84,z2,z3,z4,z5]),(0,[z1,z2,z541,z217,z5,z6])],[],[(0,[z424,z1,z101,z2,z4,z5]),(0,[z38,z1,z159,z2,z3,z4]),(0,[z1,z2,z3,z4,z5,z1221]),(0,[z1,z2,z3,z403,z5,z360]),(0,[z1,z2,z3,z4,z1222,z6])],[(0,[z1,z656,z2,z4,z62,z6])],[(0,[z72,z730,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z245]),(0,[z1,z17,z2,z3,z197,z5]),(0,[z1,z2,z3,z4,z5,z1223]),(0,[z1,z2,z3,z4,z12,z843])],[(0,[z38,z1,z2,z3,z4,z26]),(0,[z1039,z2,z3,z4,z5,z6])]],
   [[],[(0,[z1,z2,z3,z4,z1224,z6])],[(0,[z2,z582,z3,z4,z5,z26]),(0,[z1,z2,z3,z1225,z4,z5]),(0,[z1,z2,z3,z4,z61,z294])],[(0,[z1,z2,z3,z4,z5,z1226]),(0,[z1,z2,z3,z4,z5,z1227]),(0,[z1,z1228,z2,z3,z4,z5]),(0,[z74,z1,z3,z473,z34,z6]),(0,[z74,z1,z507,z3,z5,z6]),(0,[z1,z2,z1229,z4,z5,z6])],[(0,[z967,z2,z3,z4,z5,z6]),(0,[z1,z455,z2,z3,z4,z112]),(0,[z1,z2,z3,z4,z1230,z6])],[(1,[z730,z3,z4,z5,z6]),(0,[z2,z3,z4,z587,z5,z26]),(0,[z1,z2,z3,z4,z252,z26]),(0,[z1,z2,z3,z136,z129,z24]),(0,[z1231,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z568]),(0,[z1,z1232,z2,z3,z4,z5]),(0,[z1,z2,z3,z403,z5,z26]),(0,[z1,z2,z4,z5,z26,z1158]),(0,[z1,z172,z10,z4,z5,z6]),(1,[z1,z2,z762,z5,z6])],[(0,[z1,z2,z1233,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1234]),(0,[z1,z2,z1235,z4,z5,z6]),(0,[z1,z2,z3,z4,z1236,z5])],[(0,[z1,z2,z3,z4,z5,z1237]),(0,[z480,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z1238])],[(0,[z266,z47,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1239,z6]),(0,[z1240,z84,z2,z3,z4,z5]),(0,[z1,z341,z2,z4,z62,z6])],[(0,[z1,z167,z2,z4,z5,z328])],[(0,[z1,z2,z3,z1241,z4,z5]),(0,[z1,z2,z3,z4,z5,z1242])],[(0,[z424,z1,z172,z4,z5,z6]),(0,[z1,z2,z3,z4,z1243,z6]),(0,[z63,z852,z2,z3,z4,z5]),(0,[z63,z1,z2,z165,z4,z115])],[],[(0,[z1,z2,z1244,z4,z5,z6]),(0,[z1,z2,z1085,z4,z5,z6])],[(0,[z2,z734,z90,z4,z5,z6]),(0,[z70,z2,z3,z104,z5,z6]),(0,[z69,z17,z2,z3,z92,z5]),(0,[z1,z167,z2,z4,z5,z99]),(0,[z1,z2,z3,z1245,z5,z6]),(0,[z74,z1,z276,z2,z3,z6])]],
   [[(0,[z41,z1,z145,z4,z5,z6]),(0,[z1,z2,z3,z4,z1246,z6]),(0,[z1247,z84,z2,z3,z4,z5])],[],[(0,[z1,z1248,z3,z4,z5,z6]),(0,[z394,z2,z3,z4,z5,z24]),(0,[z1,z2,z165,z4,z115,z6])],[(0,[z1,z2,z3,z4,z5,z1249]),(0,[z1,z2,z3,z1250,z5,z6])],[(0,[z1,z145,z3,z445,z5,z6]),(0,[z1,z2,z3,z4,z61,z285]),(0,[z1,z2,z3,z4,z5,z1251])],[(0,[z63,z1,z2,z3,z4,z5]),(0,[z63,z1,z696,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1252]),(0,[z1,z2,z3,z1253,z5,z26]),(0,[z1,z276,z2,z3,z4,z6]),(0,[z63,z1254,z2,z3,z4,z5])],[(0,[z0,z38,z1,z2,z3,z6]),(0,[z1,z2,z3,z4,z5,z1255]),(0,[z1,z2,z3,z290,z5,z80]),(0,[z1,z2,z219,z4,z115,z6])],[(0,[z1,z2,z3,z4,z5,z1256]),(0,[z1,z2,z3,z235,z5,z26]),(0,[z1,z2,z1257,z4,z5,z6])],[(0,[z55,z72,z3,z4,z5,z26]),(0,[z131,z145,z90,z4,z5,z6]),(0,[z97,z1,z2,z315,z4,z5])],[(0,[z185,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1258])],[(0,[z0,z1,z2,z19,z5,z6]),(0,[z1,z2,z3,z4,z5,z1259]),(0,[z191,z408,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z180,z382]),(0,[z1,z2,z3,z1260,z5,z6])],[(0,[z266,z1,z2,z3,z4,z5]),(0,[z101,z2,z3,z4,z5,z26]),(0,[z1,z2,z4,z1261,z5,z6]),(0,[z633,z2,z3,z4,z5,z26]),(0,[z1,z2,z1262,z4,z5,z6])],[(0,[z1,z2,z945,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1263])],[(0,[z0,z1,z101,z2,z3,z5]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z3,z4,z5,z1264]),(0,[z1254,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z256,z390]),(0,[z1,z17,z128,z3,z30,z5]),(0,[z1,z2,z3,z4,z5,z1265])],[(0,[z1,z2,z3,z4,z6,z714]),(0,[z1,z2,z3,z4,z24,z719]),(0,[z851,z2,z3,z4,z5,z6]),(0,[z1,z17,z52,z3,z4,z121]),(0,[z536,z84,z2,z3,z4,z5])],[(0,[z1,z283,z3,z4,z5,z440]),(0,[z1,z1266,z2,z3,z4,z5])]],
   [[(0,[z1267,z1,z2,z3,z4,z5]),(0,[z23,z2,z3,z4,z5,z26]),(0,[z84,z2,z3,z4,z129,z5])],[(0,[z464,z101,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1268])],[(0,[z1,z2,z3,z4,z5,z327]),(0,[z1,z17,z494,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1269])],[(0,[z560,z2,z3,z4,z284,z6])],[(0,[z779,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z845,z5,z6]),(0,[z1,z2,z1109,z4,z5,z6]),(0,[z1,z2,z3,z235,z195,z6]),(0,[z1,z2,z1270,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1271])],[(0,[z2,z3,z750,z92,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1272]),(0,[z84,z2,z3,z1273,z4,z5])],[(0,[z1,z2,z3,z4,z56,z26]),(0,[z154,z17,z2,z146,z4,z5]),(0,[z37,z1,z330,z3,z4,z147])],[(0,[z1,z68,z17,z2,z3,z18])],[(0,[z1,z1274,z2,z4,z5,z6]),(0,[z1,z2,z3,z1275,z5,z6]),(0,[z1,z2,z3,z4,z5,z1276]),(0,[z1,z2,z3,z4,z5,z1277]),(0,[z140,z17,z2,z3,z4,z5])],[(0,[z1,z17,z2,z46,z3,z4]),(0,[z1,z408,z3,z4,z5,z561]),(0,[z1,z2,z3,z4,z195,z24]),(0,[z63,z1,z2,z3,z4,z256]),(0,[z1,z2,z3,z4,z5,z1278])],[(0,[z1,z1279,z3,z4,z5,z6]),(0,[z1,z2,z545,z4,z5,z49]),(0,[z1,z2,z3,z5,z6,z1280]),(0,[z1,z2,z246,z5,z62,z6])],[(0,[z55,z2,z3,z4,z5,z608]),(0,[z1,z2,z3,z4,z56,z240]),(0,[z1,z2,z3,z4,z5,z1281]),(0,[z1,z2,z1282,z4,z5,z6])],[(0,[z84,z68,z2,z3,z4,z5]),(0,[z63,z1151,z2,z3,z4,z5]),(0,[z1,z2,z3,z619,z4,z112])],[(0,[z1,z2,z3,z4,z1283,z6])],[]],
   [[(0,[z41,z1,z17,z9,z4,z5]),(0,[z1,z52,z3,z4,z618,z6]),(0,[z84,z2,z3,z4,z1284,z5]),(0,[z1,z2,z3,z4,z252,z6])],[(0,[z1,z2,z3,z4,z1285,z6]),(0,[z1,z2,z1286,z4,z5,z6]),(0,[z84,z2,z3,z4,z5,z87]),(0,[z581,z2,z3,z4,z5,z26]),(0,[z1,z2,z1006,z4,z5,z24]),(0,[z1,z2,z3,z403,z5,z6]),(0,[z1,z2,z3,z4,z1287,z5]),(0,[z1,z2,z3,z4,z5,z1288]),(0,[z1,z17,z3,z4,z5,z362])],[(0,[z69,z84,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1289]),(0,[z63,z1025,z2,z3,z4,z5]),(0,[z63,z1,z2,z3,z4,z230]),(0,[z1,z17,z258,z3,z4,z5]),(0,[z1,z53,z2,z290,z62,z6])],[(0,[z84,z2,z146,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1290])],[(0,[z1,z2,z3,z4,z5,z212]),(0,[z1,z2,z3,z4,z5,z1291])],[(0,[z57,z2,z3,z4,z5,z26]),(0,[z1,z17,z2,z3,z403,z5]),(0,[z1,z650,z2,z3,z18,z6])],[(0,[z1,z2,z3,z4,z5,z1292]),(0,[z1,z1293,z2,z3,z4,z6])],[(0,[z1,z2,z3,z4,z5,z1294]),(0,[z1,z1295,z2,z3,z4,z5])],[(0,[z1,z730,z3,z4,z5,z6]),(0,[z154,z2,z224,z4,z5,z6]),(0,[z1,z133,z2,z4,z5,z214]),(0,[z1,z2,z3,z1296,z5,z6]),(0,[z1,z2,z78,z5,z180,z6])],[(0,[z1,z2,z19,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z1297])],[(0,[z55,z2,z3,z4,z5,z26]),(0,[z266,z55,z2,z3,z4,z5]),(0,[z166,z2,z3,z4,z284,z26]),(0,[z1,z2,z3,z243,z11,z6]),(0,[z1,z2,z3,z4,z1298,z6]),(0,[z1,z1299,z2,z3,z4,z5]),(0,[z1,z2,z306,z4,z5,z49])],[(0,[z63,z1,z631,z3,z4,z5]),(0,[z576,z1,z2,z4,z62,z6]),(0,[z1,z1300,z2,z3,z4,z5])],[(0,[z38,z1,z101,z2,z3,z4]),(0,[z1301,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1302]),(0,[z343,z1,z2,z3,z4,z294]),(0,[z1,z2,z3,z4,z5,z497])],[(0,[z1,z2,z3,z4,z5,z1303]),(0,[z131,z2,z90,z445,z5,z6]),(0,[z266,z1,z17,z3,z4,z5]),(0,[z1,z489,z3,z4,z5,z150]),(0,[z1,z2,z3,z4,z5,z1304])],[(0,[z1,z2,z3,z1305,z5,z6]),(0,[z1,z1306,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1307]),(0,[z1,z53,z2,z4,z62,z26])]],
   [[(0,[z1,z2,z3,z1253,z5,z6])],[(0,[z1,z2,z3,z1308,z5,z6]),(0,[z1,z2,z3,z1309,z5,z6]),(0,[z140,z2,z3,z4,z5,z26])],[(0,[z1,z2,z3,z4,z5,z1310]),(0,[z69,z367,z2,z3,z5,z6]),(0,[z1,z2,z3,z235,z5,z6]),(0,[z1,z2,z3,z4,z1311,z6])],[(0,[z55,z72,z3,z4,z5,z6]),(0,[z71,z101,z47,z3,z4,z5]),(0,[z63,z1,z2,z3,z445,z5]),(0,[z84,z2,z3,z4,z5,z24])],[(0,[z1,z2,z1312,z3,z4,z5]),(0,[z1,z2,z3,z4,z1313,z6]),(0,[z1,z3,z4,z5,z823,z196])],[(0,[z1,z2,z1314,z4,z5,z6]),(0,[z1,z2,z4,z5,z1315,z6]),(0,[z63,z1231,z2,z3,z4,z5])],[(0,[z63,z757,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z825])],[(0,[z1,z1316,z2,z3,z4,z5]),(0,[z84,z2,z3,z104,z4,z5]),(0,[z1,z77,z2,z78,z5,z24]),(0,[z1,z133,z2,z4,z252,z99])],[(0,[z1,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z5,z1317]),(0,[z464,z2,z3,z4,z5,z171]),(0,[z1,z2,z3,z4,z1318,z6]),(0,[z106,z2,z3,z4,z5,z26]),(0,[z1,z2,z3,z4,z5,z1319]),(0,[z657,z2,z3,z4,z5,z24]),(0,[z1,z2,z3,z4,z256,z360]),(0,[z1,z2,z36,z78,z5,z6]),(0,[z63,z1,z3,z4,z5,z823])],[(0,[z63,z1,z2,z226,z3,z5]),(0,[z1,z2,z46,z19,z4,z6]),(0,[z1,z1320,z2,z3,z4,z5]),(0,[z1,z177,z2,z3,z4,z112]),(0,[z1,z2,z3,z1321,z5,z6]),(0,[z74,z84,z2,z3,z4,z5]),(0,[z37,z1,z507,z3,z4,z6]),(0,[z1,z52,z2,z411,z4,z6]),(0,[z1,z2,z3,z4,z5,z1322])],[(0,[z1323,z2,z3,z4,z5,z6])],[],[(0,[z1324,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z1325]),(0,[z1,z2,z3,z4,z5,z1326]),(0,[z37,z1,z239,z3,z147,z6]),(0,[z1,z2,z3,z588,z5,z13])],[(0,[z1,z2,z3,z4,z5,z1327])],[(0,[z63,z1,z2,z3,z290,z5])],[(0,[z1,z2,z3,z1328,z5,z6]),(0,[z1,z2,z3,z4,z1329,z6]),(0,[z1,z2,z3,z1012,z5,z6]),(0,[z1,z2,z3,z4,z1108,z6])]],
   [[],[(0,[z2,z3,z130,z4,z5,z26]),(0,[z1,z2,z3,z4,z203,z12]),(0,[z84,z2,z3,z1330,z4,z5]),(0,[z1,z2,z3,z4,z5,z1331]),(0,[z1,z2,z3,z4,z843,z112])],[(0,[z55,z72,z3,z4,z5,z20]),(0,[z1,z2,z3,z4,z56,z6]),(0,[z1,z128,z123,z3,z5,z6]),(0,[z1,z2,z3,z4,z256,z26]),(0,[z63,z1,z172,z10,z4,z5]),(0,[z1,z227,z2,z3,z447,z5])],[(0,[z1,z17,z145,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1332]),(0,[z1,z2,z3,z4,z5,z1333])],[(0,[z1,z2,z3,z4,z1334,z6]),(0,[z1,z128,z3,z845,z5,z6]),(0,[z1,z2,z3,z4,z5,z1335]),(0,[z1,z2,z3,z4,z62,z80])],[(0,[z1,z17,z2,z19,z4,z5]),(0,[z2,z3,z4,z5,z695,z24])],[(0,[z1,z2,z3,z4,z5,z1336]),(0,[z37,z1,z3,z274,z147,z6])],[(0,[z1,z2,z1337,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1338]),(0,[z1,z2,z3,z5,z1339,z6])],[(0,[z266,z1,z47,z3,z4,z5])],[(0,[z426,z2,z65,z3,z4,z5]),(0,[z1,z2,z138,z4,z180,z6]),(0,[z1,z133,z2,z235,z5,z99])],[(0,[z1,z395,z2,z3,z4,z233]),(0,[z1,z2,z3,z243,z5,z360]),(0,[z1,z2,z3,z4,z5,z1340])],[(0,[z1,z2,z3,z4,z5,z1341]),(0,[z1,z68,z2,z3,z569,z6])],[(0,[z1,z2,z207,z4,z5,z26]),(0,[z1,z276,z128,z2,z3,z6]),(0,[z1,z2,z3,z78,z180,z6])],[(0,[z69,z2,z3,z92,z5,z24]),(0,[z1,z2,z3,z4,z11,z390])],[(0,[z185,z55,z72,z3,z4,z5]),(0,[z166,z17,z2,z3,z4,z284]),(0,[z1342,z1,z2,z3,z4,z5]),(0,[z84,z408,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1343])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 510) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 510).take 502) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1012).take 375) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1387)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [510, 502, 375] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 127).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 127).take 131).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 258).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 371).take 135).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 506).take 6).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [127, 131, 113, 135, 6] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_cons pc4 (windowsF_nil pcend)))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_45842

theorem PEqualNP.Outside.L_meta_45842 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008372960 * 2 ^ 32 + 4008241344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008372960 * 2 ^ 32 + 4008241344) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_45842.solve