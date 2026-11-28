import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41360

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4240476288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x008a8842ae3185ba#64 ++ 0x0008a8842ae3185b#64 ++ 0xc19f98c7ee318ffd#64 ++ 0xec19f98c7ee318ff#64 : BitVec 256),
   (0x422623199016badc#64 ++ 0x0422623199016bad#64 ++ 0xc6666739903ffffb#64 ++ 0xfc6666739903ffff#64 : BitVec 256),
   (0x1858782e16c15c60#64 ++ 0x11858782e16c15c6#64 ++ 0x7878783e1fc1fc77#64 ++ 0xf7878783e1fc1fc7#64 : BitVec 256),
   (0xad807dc01b6a0f00#64 ++ 0x0ad807dc01b6a0f0#64 ++ 0xbf807fc01ffe0f8f#64 ++ 0x7bf807fc01ffe0f8#64 : BitVec 256),
   (0x37ff80000dbde000#64 ++ 0x237ff80000dbde00#64 ++ 0x3fff80001ffff00f#64 ++ 0xa3fff80001ffff00#64 : BitVec 256),
   (0x3f7556b540000000#64 ++ 0x43f7556b54000000#64 ++ 0xffffffffe000000f#64 ++ 0xdffffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [11, 5]⟩, ⟨.and, [12, 7]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0080804028200102 0x0008080402820010 0x018180c060000000 0x0018180c06000000

def z1 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc19f98c7ee318ffd 0xec19f98c7ee318ff

def z2 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7878783e1fc1fc77 0xf7878783e1fc1fc7

def z3 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z4 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffe000000f 0xdffffffffe000000

def z5 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc6666739903ffffb 0xfc6666739903ffff

def z6 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z7 : W := mkw 0x1050000000804000 0x0105000000080400 0x3860000011c07002 0x03860000011c0700

def z8 : W := mkw 0x0000000000000000 0x0000000000000000 0xc006000180000009 0xcc00600018000000

def z9 : W := mkw 0xbffffdee1fffff60 0x3bffffdee1fffff6 0xfffffffe1fffffff 0xffffffffe1ffffff

def z10 : W := mkw 0x3f7576bd50c05840 0x53f7576bd50c0584 0x3e60673811c07002 0x13e60673811c0700

def z11 : W := mkw 0x0224231110020a00 0x00224231110020a0 0xc6666739903e0f8b 0xfc6666739903e0f8

def z12 : W := mkw 0x35d800000da94000 0x035d800000da9400 0x3ff800001ffff00f 0xa3ff800001ffff00

def z13 : W := mkw 0x3ff7d6f5e830819a 0x43ff7d6f5e830819 0xffffffffe030038f 0xdffffffffe030038

def z14 : W := mkw 0x2d0056b540000000 0x42d0056b54000000 0xff807fffe000000f 0x5ff807fffe000000

def z15 : W := mkw 0x105a802ea491d0fa 0x1105a802ea491d0f 0x407f803fe001f070 0x8407f803fe001f07

def z16 : W := mkw 0x1058080206814420 0x0105808020681442 0x787818061fc1fc77 0xe787818061fc1fc7

def z17 : W := mkw 0x127e00000495e000 0x0127e00000495e00 0x3e7e00001ffff00f 0xa3e7e00001ffff00

def z18 : W := mkw 0x77ffa3199dbffadc 0x277ffa3199dbffad 0xffffe7399fffffff 0xfffffe7399ffffff

def z19 : W := mkw 0x2580000009280000 0x0258000000928000 0x3f8000001ffe000f 0x23f8000001ffe000

def z20 : W := mkw 0x3fffd6b54dbde000 0x63fffd6b54dbde00 0xfffffffffffff00f 0xffffffffffffff00

def z21 : W := mkw 0x4224231910063a44 0x04224231910063a4 0x06606738100e7002 0x106606738100e700

def z22 : W := mkw 0x42aeab5bbe37bffe 0x042aeab5bbe37bff 0xc7fffffffe3fffff 0xfc7fffffffe3ffff

def z23 : W := mkw 0x1058000004814000 0x0105800000481400 0x387800001fc1f007 0xa387800001fc1f00

def z24 : W := mkw 0x88007dc012420f00 0x088007dc012420f0 0x80007fc000000f80 0x580007fc000000f8

def z25 : W := mkw 0x0008280a16c15c60 0x10008280a16c15c6 0x000000001fc1fc70 0x2000000001fc1fc7

def z26 : W := mkw 0x3f7d7ebf56c15c60 0x53f7d7ebf56c15c6 0xffffffffffc1fc7f 0xfffffffffffc1fc7

def z27 : W := mkw 0x5a74733d10c67a44 0x15a74733d10c67a4 0x3e60673811ce7002 0x13e60673811ce700

def z28 : W := mkw 0x3f7d782e16c15c60 0x13f7d782e16c15c6 0x7ffff83e1fc1fc7f 0xf7ffff83e1fc1fc7

def z29 : W := mkw 0x022602110014a000 0x0022602110014a00 0xc6666739903ff00b 0xfc6666739903ff00

def z30 : W := mkw 0x25802100192a0a00 0x025802100192a0a0 0xbf8067001ffe0f8f 0x7bf8067001ffe0f8

def z31 : W := mkw 0xad805cc00b680500 0x0ad805cc00b68050 0x3f8018c01ffe000f 0x23f8018c01ffe000

def z32 : W := mkw 0x1850782412400c00 0x01850782412400c0 0x7878783e1fc00c07 0xf7878783e1fc00c0

def z33 : W := mkw 0x27250000010c2000 0x227250000010c200 0x06000000000e0000 0x006000000000e000

def z34 : W := mkw 0xad88fdc23f6b0f22 0x0ad88fdc23f6b0f2 0xbf99ffc67ffe0f8f 0x7bf99ffc67ffe0f8

def z35 : W := mkw 0x4000231990021adc 0x04000231990021ad 0xc000673980000ff0 0x5c000673980000ff

def z36 : W := mkw 0xa58025c0192a0b00 0x0a58025c0192a0b0 0x878067c0103e0f8b 0x7878067c0103e0f8

def z37 : W := mkw 0x000200000014a000 0x0000200000014a00 0x00000000103ff000 0x200000000103ff00

def z38 : W := mkw 0x0800782e12401c60 0x10800782e12401c6 0x4060783e1001fc73 0xf4060783e1001fc7

def z39 : W := mkw 0xbffffdc01fffef00 0x2bffffdc01fffef0 0xbfffffc01fffff8f 0xfbfffffc01fffff8

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000000018c71 0xe4000000000018c7

def z41 : W := mkw 0x000a8002a41180ba 0x0000a8002a41180b 0x401f8007e0018070 0x8401f8007e001807

def z42 : W := mkw 0xad007580114a0a00 0x0ad007580114a0a0 0x3e00670011ce0002 0x13e00670011ce000

def z43 : W := mkw 0x37ff86914dbde000 0x637ff86914dbde00 0xbfff87c1fffff00f 0xabfff87c1fffff00

def z44 : W := mkw 0x5a7e7b3f96d7fefc 0x15a7e7b3f96d7fef 0xfe7e7f3f9fffffff 0xffe7e7f3f9ffffff

def z45 : W := mkw 0xbdd87dee1feb5f60 0x1bdd87dee1feb5f6 0xfff87ffe1fffffff 0xffff87ffe1ffffff

def z46 : W := mkw 0x37ff802e0dbdf060 0x337ff802e0dbdf06 0x7fff803e1ffff07f 0xa7fff803e1ffff07

def z47 : W := mkw 0x0002000080108098 0x0000200008010809 0xc19f98c7e0318ffd 0xec19f98c7e0318ff

def z48 : W := mkw 0x7f7777bdd016badc 0x47f7777bdd016bad 0xfffffffff03fffff 0xffffffffff03ffff

def z49 : W := mkw 0x35d980000da94000 0x235d980000da9400 0x399980000fc00004 0x0399980000fc0000

def z50 : W := mkw 0x37ff8842afbde5ba 0x237ff8842afbde5b 0xffff98c7ffffffff 0xeffff98c7fffffff

def z51 : W := mkw 0x3dd9d8260fe94420 0x33dd9d8260fe9442 0x399998060fc00004 0x0399998060fc0000

def z52 : W := mkw 0xad807dc81b6a1f40 0x0ad807dc81b6a1f4 0xffe07ff81fffffff 0xfffe07ff81ffffff

def z53 : W := mkw 0xbdd87dc01feb4f00 0x0bdd87dc01feb4f0 0xbff87fc01fffff8f 0xfbff87fc01fffff8

def z54 : W := mkw 0x0000210810021a40 0x00000210810021a4 0xc6606738103ffffb 0xfc6606738103ffff

def z55 : W := mkw 0xafa47fd11b6a0f00 0x0afa47fd11b6a0f0 0xffe67ff99ffe0f8f 0xfffe67ff99ffe0f8

def z56 : W := mkw 0x808029401b6a0f00 0x0808029401b6a0f0 0x000000001ffe0f80 0x2000000001ffe0f8

def z57 : W := mkw 0x527e023f8495f0fc 0x1527e023f8495f0f 0x407e003f8001f070 0x8407e003f8001f07

def z58 : W := mkw 0x0008080206010420 0x0000808020601042 0x401818060e018c75 0xe401818060e018c7

def z59 : W := mkw 0x18daf86ebef1ddfa 0x118daf86ebef1ddf 0xf9fff8fffff1ffff 0xff9fff8fffff1fff

def z60 : W := mkw 0x00028000a010809a 0x000028000a010809 0x00078001e0000000 0x000078001e000000

def z61 : W := mkw 0xa58005c0092a0300 0x0a58005c0092a030 0xbf8007c01ffe038f 0x2bf8007c01ffe038

def z62 : W := mkw 0x0000200810c05840 0x10000200810c0584 0x0000000011c07000 0x00000000011c0700

def z63 : W := mkw 0x0002000080108098 0x0000200008010809 0xc006000180318ff9 0xec006000180318ff

def z64 : W := mkw 0x022600000014a000 0x0022600000014a00 0x06660000103ff00b 0xa06660000103ff00

def z65 : W := mkw 0x008008400a200500 0x0008008400a20050 0xc19f98c7ee300f8d 0xec19f98c7ee300f8

def z66 : W := mkw 0x7f7756bdc014b0dc 0x47f7756bdc014b0d 0xffffffffe001f07f 0xdffffffffe001f07

def z67 : W := mkw 0xbff55ef54b680500 0x4bff55ef54b68050 0xffffffffefc0000f 0xdffffffffefc0000

def z68 : W := mkw 0xefa47fd91b6e3f44 0x0efa47fd91b6e3f4 0xbfe07ff81ffe7f8f 0x7bfe07ff81ffe7f8

def z69 : W := mkw 0x3ff556b549280000 0x43ff556b54928000 0xfffffffffffe000f 0xffffffffffffe000

def z70 : W := mkw 0x0226021180108098 0x0022602118010809 0xc666673980318ffb 0xfc666673980318ff

def z71 : W := mkw 0x185af82eb6d1dcfa 0x1185af82eb6d1dcf 0x787ff83fffc1fc77 0xf787ff83fffc1fc7

def z72 : W := mkw 0x00828000093ca000 0x200828000093ca00 0x00000000003e0000 0x000000000003e000

def z73 : W := mkw 0x88007dee12421f60 0x188007dee12421f6 0xc0007ffe00000ff0 0x5c0007ffe00000ff

def z74 : W := mkw 0x2d00548000000000 0x02d0054800000000 0xbf807fc00000000f 0x5bf807fc00000000

def z75 : W := mkw 0x400221089016badc 0x0400221089016bad 0x00000000103ffff0 0x200000000103ffff

def z76 : W := mkw 0x0225021140000000 0x4022502114000000 0x00078001e0000000 0x000078001e000000

def z77 : W := mkw 0x0000200810001840 0x0000020081000184 0x406060381001fc73 0xf406060381001fc7

def z78 : W := mkw 0xad805dc00b6a0700 0x0ad805dc00b6a070 0xbf801fc00ffe038c 0x0bf801fc00ffe038

def z79 : W := mkw 0x7f7777bdd016badc 0x47f7777bdd016bad 0xfe666739903ffffb 0xffe666739903ffff

def z80 : W := mkw 0x022620081014b840 0x0022620081014b84 0x46666038103ffc7b 0xf46666038103ffc7

def z81 : W := mkw 0x35db8842afb9c5ba 0x235db8842afb9c5b 0xf99f98c7eff18ffd 0xef99f98c7eff18ff

def z82 : W := mkw 0x00828040a830819a 0x000828040a830819 0x818780c1e0300388 0x0818780c1e030038

def z83 : W := mkw 0x1850702c10c05840 0x11850702c10c0584 0x3860603811c07002 0x13860603811c0700

def z84 : W := mkw 0x35d980000da94000 0x235d980000da9400 0x39f980001fc1f007 0xa39f980001fc1f00

def z85 : W := mkw 0x1050000000000000 0x0105000000000000 0x3878000000000007 0x8387800000000000

def z86 : W := mkw 0x1850502400000000 0x0185050240000000 0x7878783e00000007 0xd7878783e0000000

def z87 : W := mkw 0x2725069140000000 0x4272506914000000 0x878787c1e0000008 0x0878787c1e000000

def z88 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x381818061fc1fc74 0x2381818061fc1fc7

def z89 : W := mkw 0x0224021100000000 0x0022402110000000 0x4066003980000000 0x8406600398000000

def z90 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0x399998c660000004 0x0399998c66000000

def z91 : W := mkw 0x1858582606c14420 0x11858582606c1442 0x7878783e0fc00007 0xd7878783e0fc0000

def z92 : W := mkw 0x37f5000009280000 0x037f500000928000 0x3fff80001ffe000f 0xa3fff80001ffe000

def z93 : W := mkw 0x422602198014b0dc 0x0422602198014b0d 0x406600398001f070 0x8406600398001f07

def z94 : W := mkw 0xad805cc00b680500 0x0ad805cc00b68050 0x398018c00fc00004 0x0398018c00fc0000

def z95 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0x3e0067001ffe0f82 0x33e0067001ffe0f8

def z96 : W := mkw 0xad8afdc2bf7b8fba 0x0ad8afdc2bf7b8fb 0xbf807fc01fff8fff 0x7bf807fc01fff8ff

def z97 : W := mkw 0x37ff88400fbde500 0x237ff88400fbde50 0xbfff98c01fffff8f 0xebfff98c01fffff8

def z98 : W := mkw 0x008a88422e318522 0x0008a88422e31852 0x019f98c66e31800d 0xa019f98c66e31800

def z99 : W := mkw 0x00000842a20005ba 0x000000842a20005b 0x0000000000000ff0 0x00000000000000ff

def z100 : W := mkw 0x3f7556b5418c6000 0x63f7556b5418c600 0xfffffffff1ce700f 0xdfffffffff1ce700

def z101 : W := mkw 0xad8afdc2bf7b8fba 0x0ad8afdc2bf7b8fb 0xff9fffc7ffff8fff 0xfff9fffc7ffff8ff

def z102 : W := mkw 0x37ff8002adbde0ba 0x237ff8002adbde0b 0x7fff8007fffff07f 0xa7fff8007fffff07

def z103 : W := mkw 0x0800782e12401c60 0x10800782e12401c6 0x4000783e00000c70 0x54000783e00000c7

def z104 : W := mkw 0x27a78000093ca000 0x227a78000093ca00 0x07878000003e0008 0x007878000003e000

def z105 : W := mkw 0x422623199016badc 0x0422623199016bad 0x86666739903e738a 0x186666739903e738

def z106 : W := mkw 0x008a80000c318000 0x0008a80000c31800 0x019f80000e31800d 0xa019f80000e31800

def z107 : W := mkw 0x10da8842aeb1c5ba 0x010da8842aeb1c5b 0xf9ff98c7fff1ffff 0xef9ff98c7fff1fff

def z108 : W := mkw 0x4000231990021adc 0x04000231990021ad 0xc06067399001fff3 0xfc06067399001fff

def z109 : W := mkw 0x1059800004814000 0x2105980000481400 0x0019800000000000 0x0001980000000000

def z110 : W := mkw 0x67a62319993ebadc 0x067a62319993ebad 0xffe667399fffffff 0xfffe667399ffffff

def z111 : W := mkw 0x1275023540000000 0x4127502354000000 0x407f803fe0000000 0x8407f803fe000000

def z112 : W := mkw 0x2725069140000000 0x4272506914000000 0x0600070000000000 0x0060007000000000

def z113 : W := mkw 0x12ff80000cb5e000 0x212ff80000cb5e00 0x01ff80000e31f00d 0xa01ff80000e31f00

def z114 : W := mkw 0x008a80000dbde000 0x2008a80000dbde00 0x000000001ffff000 0x2000000001ffff00

def z115 : W := mkw 0x088adef7ee3185ba 0x4088adef7ee3185b 0xc19fffffee318ffd 0xfc19fffffee318ff

def z116 : W := mkw 0x3f757ebf52401c60 0x53f757ebf52401c6 0xffffffffe0000c7f 0xdffffffffe0000c7

def z117 : W := mkw 0x0808782e16c15c60 0x10808782e16c15c6 0x4000783e1fc1fc70 0x74000783e1fc1fc7

def z118 : W := mkw 0x3ffdd6b54da94000 0x63ffdd6b54da9400 0xffffffffefc0000f 0xdffffffffefc0000

def z119 : W := mkw 0x008a88400e318500 0x0008a88400e31850 0x819f98c00e318f8d 0xe819f98c00e318f8

def z120 : W := mkw 0x888afdc2be738fba 0x0888afdc2be738fb 0xc19fffc7ee318ffd 0xfc19fffc7ee318ff

def z121 : W := mkw 0x008880000c210000 0x0008880000c21000 0x019980000e000004 0x0019980000e00000

def z122 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x3e60673800000002 0x13e6067380000000

def z123 : W := mkw 0x3fffdef7efbde5ba 0x63fffdef7efbde5b 0xffffffffffffffff 0xffffffffffffffff

def z124 : W := mkw 0x12ff8842aeb5e5ba 0x212ff8842aeb5e5b 0xc1ff98c7ee31fffd 0xec1ff98c7ee31fff

def z125 : W := mkw 0x127f80000495e000 0x2127f80000495e00 0x007f80000001f000 0x8007f80000001f00

def z126 : W := mkw 0x12ff8a77ee3185ba 0x412ff8a77ee3185b 0xc1ff98ffee318ffd 0xec1ff98ffee318ff

def z127 : W := mkw 0xbff57dc01b6a0f00 0x0bff57dc01b6a0f0 0xbfffffc01ffe0f8f 0xfbfffffc01ffe0f8

def z128 : W := mkw 0xad807ff55b6a0f00 0x4ad807ff55b6a0f0 0xff807ffffffe0f8f 0x7ff807ffffffe0f8

def z129 : W := mkw 0x377700000014a000 0x0377700000014a00 0x3fff8000103ff00f 0xa3fff8000103ff00

def z130 : W := mkw 0x0008280a16c15c60 0x10008280a16c15c6 0x406060381fc1fc73 0xf406060381fc1fc7

def z131 : W := mkw 0x1858792e16c35e60 0x11858792e16c35e6 0xfe787f3e1fffffff 0xffe787f3e1ffffff

def z132 : W := mkw 0x18d8f86e3ee15d62 0x118d8f86e3ee15d6 0x79f9f8fe7fc1fc77 0xf79f9f8fe7fc1fc7

def z133 : W := mkw 0x008008400a200500 0x0008008400a20050 0x818018c00e300f8d 0x6818018c00e300f8

def z134 : W := mkw 0x422ea31bb417bafe 0x0422ea31bb417baf 0xc67fe73ff03ffffb 0xfc67fe73ff03ffff

def z135 : W := mkw 0x1858582606c14420 0x11858582606c1442 0x381818060fc00004 0x0381818060fc0000

def z136 : W := mkw 0x422603118016a29c 0x0422603118016a29 0x86060701803e0388 0x086060701803e038

def z137 : W := mkw 0x1850782e12401c60 0x11850782e12401c6 0x7878783e00000c77 0xd7878783e00000c7

def z138 : W := mkw 0x0000000000000000 0x0000000000000000 0xc19f98c7e000000d 0xcc19f98c7e000000

def z139 : W := mkw 0x258a80000dbde000 0x2258a80000dbde00 0x3f8000001ffff00f 0x23f8000001ffff00

def z140 : W := mkw 0x5277233dd016badc 0x45277233dd016bad 0xc67fe73ff03ffffb 0xfc67fe73ff03ffff

def z141 : W := mkw 0x0800780012400c00 0x00800780012400c0 0x380078001fc00c07 0x7380078001fc00c0

def z142 : W := mkw 0xfff77ffddb7ebfdc 0x4fff77ffddb7ebfd 0xffffffffffffffff 0xffffffffffffffff

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000300f89 0x68000000000300f8

def z144 : W := mkw 0xad00548001480000 0x0ad0054800148000 0x3800000001c00000 0x03800000001c0000

def z145 : W := mkw 0x1058002e04815060 0x11058002e0481506 0x4078003e0001f070 0x84078003e0001f07

def z146 : W := mkw 0x2725069140000000 0x4272506914000000 0xc79f9fc7e000000d 0xcc79f9fc7e000000

def z147 : W := mkw 0x37750000018c6000 0x237750000018c600 0x3e60000011ce7002 0x03e60000011ce700

def z148 : W := mkw 0x422623199016badc 0x0422623199016bad 0x46666739900ff072 0x946666739900ff07

def z149 : W := mkw 0x377506b540000000 0x4377506b54000000 0xc7ff87ffe0000008 0x8c7ff87ffe000000

def z150 : W := mkw 0x422623119016aa9c 0x0422623119016aa9 0x86066701903e0f8b 0x786066701903e0f8

def z151 : W := mkw 0x67a78311893ea29c 0x267a78311893ea29 0x87878701803e0388 0x087878701803e038

def z152 : W := mkw 0xed827dc89b7ebfdc 0x0ed827dc89b7ebfd 0xbf807fc01fffffff 0x7bf807fc01ffffff

def z153 : W := mkw 0xe7a607d1893ea39c 0x0e7a607d1893ea39 0x878607c1803e0388 0x0878607c1803e038

def z154 : W := mkw 0x3fffdef7ee3185ba 0x43fffdef7ee3185b 0xffffffffee318fff 0xfffffffffee318ff

def z155 : W := mkw 0x3f7756b5c0108098 0x43f7756b5c010809 0xffffffffe0318fff 0xfffffffffe0318ff

def z156 : W := mkw 0x98587dee16c35f60 0x198587dee16c35f6 0xf8787ffe1fc1fff7 0xff8787ffe1fc1fff

def z157 : W := mkw 0x127f8002a495e0ba 0x2127f8002a495e0b 0x407f8007e001f070 0x8407f8007e001f07

def z158 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x000000000e318ff0 0x2000000000e318ff

def z159 : W := mkw 0x10da80000dbde000 0x210da80000dbde00 0x387800001ffff007 0xa387800001ffff00

def z160 : W := mkw 0x0800790012420e00 0x00800790012420e0 0xbe007f001ffe0f8f 0x7be007f001ffe0f8

def z161 : W := mkw 0x3dd9d4a44da94000 0x63dd9d4a44da9400 0x399998c66fc00004 0x0399998c66fc0000

def z162 : W := mkw 0xad82fdc0bb7a8f9a 0x0ad82fdc0bb7a8f9 0xbf87ffc1fffe0f8f 0x7bf87ffc1fffe0f8

def z163 : W := mkw 0x008a8842afbde5ba 0x2008a8842afbde5b 0x000000001ffffff0 0x2000000001ffffff

def z164 : W := mkw 0x080056b540000000 0x4080056b54000000 0xc19fffffe000000d 0xdc19fffffe000000

def z165 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3e6000001ffff002 0x23e6000001ffff00

def z166 : W := mkw 0x127f8237e41180ba 0x4127f8237e41180b 0x407f803fe0018070 0x8407f803fe001807

def z167 : W := mkw 0xbd587dae17cb5e60 0x1bd587dae17cb5e6 0x7e787f3e1fcffc77 0xf7e787f3e1fcffc7

def z168 : W := mkw 0x3ddbdce6ee3185ba 0x43ddbdce6ee3185b 0xf99f98c7ee318ffd 0xef99f98c7ee318ff

def z169 : W := mkw 0x0002000080108098 0x0000200008010809 0x4006000180018070 0x8400600018001807

def z170 : W := mkw 0x00828840aa30859a 0x000828840aa30859 0x818798c1ee300f8d 0x6818798c1ee300f8

def z171 : W := mkw 0xbff57ff55b6a0f00 0x4bff57ff55b6a0f0 0xbfe07ff81ffe0f8f 0x7bfe07ff81ffe0f8

def z172 : W := mkw 0x1275023540000000 0x4127502354000000 0xc1ff98ffe000000d 0xcc1ff98ffe000000

def z173 : W := mkw 0x0224021100000000 0x0022402110000000 0xc66667398000000b 0xdc66667398000000

def z174 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0xbf99ffc66000000f 0x5bf99ffc66000000

def z175 : W := mkw 0x0000200010000800 0x0000020001000080 0x0000600010000c03 0x70000600010000c0

def z176 : W := mkw 0x0000210010020a00 0x00000210010020a0 0x86006700103e0f8b 0x786006700103e0f8

def z177 : W := mkw 0xa58005c0092a0300 0x0a58005c0092a030 0x878007c0003e0388 0x0878007c0003e038

def z178 : W := mkw 0xbdd15ce44b680500 0x4bdd15ce44b68050 0x399998c66fc00004 0x0399998c66fc0000

def z179 : W := mkw 0x3f7577b550020a00 0x43f7577b550020a0 0xfffffffff03e0f8f 0xffffffffff03e0f8

def z180 : W := mkw 0x3775023540000000 0x4377502354000000 0x7fff803fe000000f 0x87fff803fe000000

def z181 : W := mkw 0x1051002440000000 0x4105100244000000 0x0019800660000000 0x0001980066000000

def z182 : W := mkw 0x3775000000000000 0x0377500000000000 0x3e60000000000002 0x03e6000000000000

def z183 : W := mkw 0x6f2677999016badc 0x06f2677999016bad 0xffe67ff9903fffff 0xfffe67ff9903ffff

def z184 : W := mkw 0x42ae8a5bae35b5fe 0x042ae8a5bae35b5f 0xc1ff98ffee31fffd 0xec1ff98ffee31fff

def z185 : W := mkw 0x0808782e16411c60 0x10808782e16411c6 0x4018783e0e018c75 0xf4018783e0e018c7

def z186 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0xffff98c7fffff00f 0xeffff98c7fffff00

def z187 : W := mkw 0x422623199016badc 0x0422623199016bad 0x86060701903ffff8 0x286060701903ffff

def z188 : W := mkw 0x1050002400000000 0x0105000240000000 0x4078003e00000000 0x84078003e0000000

def z189 : W := mkw 0x08007ebf52401c60 0x508007ebf52401c6 0xc0007fffe0000c70 0x5c0007fffe0000c7

def z190 : W := mkw 0xc8007fd992421fdc 0x0c8007fd992421fd 0xc0007ff980000ff0 0x5c0007ff980000ff

def z191 : W := mkw 0x0224221910001840 0x0022422191000184 0xc66667399001fc7b 0xfc66667399001fc7

def z192 : W := mkw 0x3fffd6b54c318000 0x43fffd6b54c31800 0xffffffffee31800f 0xfffffffffee31800

def z193 : W := mkw 0x77752319118e7a44 0x277752319118e7a4 0x3e60673811ce7002 0x13e60673811ce700

def z194 : W := mkw 0x3f7d56bf44815060 0x53f7d56bf4481506 0xffffffffe001f07f 0xdffffffffe001f07

def z195 : W := mkw 0x2d80548009280000 0x02d8054800928000 0xbf807fc01ffe000f 0x7bf807fc01ffe000

def z196 : W := mkw 0x8000294012420f00 0x08000294012420f0 0x0000000000000f80 0x00000000000000f8

def z197 : W := mkw 0x000a8002a41180ba 0x0000a8002a41180b 0xc01f8007e0318ff9 0xec01f8007e0318ff

def z198 : W := mkw 0x0080004008200100 0x0008000400820010 0x818000c000300388 0x0818000c00030038

def z199 : W := mkw 0x2d007c8012400c00 0x02d007c8012400c0 0xbf807fc01fc00c0f 0x7bf807fc01fc00c0

def z200 : W := mkw 0x808aa942bf7b8fba 0x0808aa942bf7b8fb 0x000000001fff8ff0 0x2000000001fff8ff

def z201 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3f9f80000ffe000c 0x03f9f80000ffe000

def z202 : W := mkw 0x1058002e04815060 0x11058002e0481506 0x7878003e1fc1f077 0xa7878003e1fc1f07

def z203 : W := mkw 0x2581800009280000 0x2258180000928000 0x0181800000000000 0x0018180000000000

def z204 : W := mkw 0x2f25569140000000 0x42f2556914000000 0xbf87ffc1e000000f 0x5bf87ffc1e000000

def z205 : W := mkw 0x377d000004814000 0x0377d00000481400 0x3fff80001fc1f00f 0xa3fff80001fc1f00

def z206 : W := mkw 0x58587b3f96c35efc 0x158587b3f96c35ef 0xf8787f3f9fc1fff7 0xff8787f3f9fc1fff

def z207 : W := mkw 0x1a7556b540000000 0x41a7556b54000000 0xc07fffffe0000000 0xdc07fffffe000000

def z208 : W := mkw 0x808aa942bf7b8fba 0x0808aa942bf7b8fb 0xc19f98c7ffff8ffd 0xec19f98c7ffff8ff

def z209 : W := mkw 0x42aea3199c37badc 0x042aea3199c37bad 0xc7ffe7399e3fffff 0xfc7ffe7399e3ffff

def z210 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc7fffffff03fffff 0xfc7fffffff03ffff

def z211 : W := mkw 0x008a8842afbde5ba 0x2008a8842afbde5b 0xc19f98c7fffffffd 0xec19f98c7fffffff

def z212 : W := mkw 0x2580000009280000 0x0258000000928000 0x398000000fc00004 0x0398000000fc0000

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x401f8007e0000000 0x8401f8007e000000

def z214 : W := mkw 0xad8055c0092a0300 0x0ad8055c0092a030 0xbf807fc0003e038f 0x5bf807fc0003e038

def z215 : W := mkw 0xad807cc01b680d00 0x0ad807cc01b680d0 0x398078c01fc00c07 0x7398078c01fc00c0

def z216 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0xf9fff8ffffc1fc7f 0xff9fff8ffffc1fc7

def z217 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x3ff9fffe60000006 0x13ff9fffe6000000

def z218 : W := mkw 0x4000210890021adc 0x04000210890021ad 0x0000000000000ff0 0x00000000000000ff

def z219 : W := mkw 0x0800780812401c40 0x00800780812401c4 0x786078381fc1fc77 0xf786078381fc1fc7

def z220 : W := mkw 0xefa67fd99b7ebfdc 0x0efa67fd99b7ebfd 0xffe67ff99fffffff 0xfffe67ff99ffffff

def z221 : W := mkw 0x127f80000495e000 0x2127f80000495e00 0x067f8000103ff00b 0xa067f8000103ff00

def z222 : W := mkw 0x008008400a200500 0x0008008400a20050 0x000000000e300f80 0x2000000000e300f8

def z223 : W := mkw 0x422602118014a09c 0x0422602118014a09 0x0006000180000000 0x0000600018000000

def z224 : W := mkw 0x1058202e14815860 0x11058202e1481586 0x4078603e1001fc73 0xf4078603e1001fc7

def z225 : W := mkw 0x27a60000093ca000 0x027a60000093ca00 0x3fe600001ffff00f 0xa3fe600001ffff00

def z226 : W := mkw 0x088078401a600d00 0x0088078401a600d0 0xb98078c01ff00f8f 0x7b98078c01ff00f8

def z227 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfe6667398000000b 0xdfe6667398000000

def z228 : W := mkw 0x0002000080108098 0x0000200008010809 0x8006000180300388 0x0800600018030038

def z229 : W := mkw 0xbff57ff55b6a0f00 0x4bff57ff55b6a0f0 0xfffffffffffe0f8f 0xffffffffffffe0f8

def z230 : W := mkw 0x3ff7d6b5493ca000 0x63ff7d6b5493ca00 0xffffffffe03e000f 0xdffffffffe03e000

def z231 : W := mkw 0x408aa1089dbffadc 0x2408aa1089dbffad 0x000000001ffffff0 0x2000000001ffffff

def z232 : W := mkw 0x1858582606c14420 0x11858582606c1442 0x387818061fc1f007 0xa387818061fc1f00

def z233 : W := mkw 0x37ff80008dbde098 0x237ff80008dbde09 0xffff80019fffffff 0xeffff80019ffffff

def z234 : W := mkw 0x088af86ebe719dfa 0x1088af86ebe719df 0xc19ff8ffee318ffd 0xfc19ff8ffee318ff

def z235 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x401818060e318ff5 0xe401818060e318ff

def z236 : W := mkw 0x008208408a308598 0x0008208408a30859 0xc18618c18e318ffd 0xec18618c18e318ff

def z237 : W := mkw 0x1275023540000000 0x4127502354000000 0xc67fe73fe000000b 0xdc67fe73fe000000

def z238 : W := mkw 0x3f75548000000000 0x03f7554800000000 0xbfffffc00000000f 0xdbfffffc00000000

def z239 : W := mkw 0x0000084002000500 0x0000008400200050 0x800018c000000f80 0x4800018c000000f8

def z240 : W := mkw 0x400223199016badc 0x0400223199016bad 0xc0006739903ffff0 0x7c0006739903ffff

def z241 : W := mkw 0x1858502404814000 0x0185850240481400 0x7878783e1fc1f007 0xf7878783e1fc1f00

def z242 : W := mkw 0x0000000000000000 0x0000000000000000 0x860067000000000b 0x5860067000000000

def z243 : W := mkw 0xa58004c009280100 0x0a58004c00928010 0x018000c000000000 0x0018000c00000000

def z244 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0x79f9f8fe60000007 0xd79f9f8fe6000000

def z245 : W := mkw 0x0800782e12401c60 0x10800782e12401c6 0x7800783e1fc00c77 0x77800783e1fc00c7

def z246 : W := mkw 0x0002000080108098 0x0000200008010809 0x0000000000318ff0 0x20000000000318ff

def z247 : W := mkw 0x008888422e210522 0x0008888422e21052 0x019998c66e000004 0x0019998c66e00000

def z248 : W := mkw 0x0800700010400800 0x0080070001040080 0x3800600011c00002 0x13800600011c0000

def z249 : W := mkw 0x408aa94abe37bffe 0x0408aa94abe37bff 0x000000001e3ffff0 0x2000000001e3ffff

def z250 : W := mkw 0x3d587cae16c15c60 0x13d587cae16c15c6 0xfff87ffe1fc1fc7f 0xffff87ffe1fc1fc7

def z251 : W := mkw 0x4000231910021a44 0x04000231910021a4 0x0000673800000000 0x1000067380000000

def z252 : W := mkw 0x35d980000da94000 0x235d980000da9400 0x3f9980001ffe000f 0x23f9980001ffe000

def z253 : W := mkw 0x2d00548000000000 0x02d0054800000000 0x3e00670000000002 0x13e0067000000000

def z254 : W := mkw 0x0008280a16011c60 0x00008280a16011c6 0x4078783e1e01fc77 0xf4078783e1e01fc7

def z255 : W := mkw 0x800005c000020300 0x0800005c00002030 0x800007c000000380 0x0800007c00000038

def z256 : W := mkw 0x4a2677bdd016badc 0x44a2677bdd016bad 0xc6667ffff03ffffb 0xfc6667ffff03ffff

def z257 : W := mkw 0x37f7800009bce000 0x237f7800009bce00 0x3fe7800011fe700a 0x03fe7800011fe700

def z258 : W := mkw 0x0000000000000000 0x0000000000000000 0x019998c660000004 0x0019998c66000000

def z259 : W := mkw 0xef267799915ebadc 0x0ef267799915ebad 0xfe66673991fffffb 0xffe66673991fffff

def z260 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc00018c7ee318ff0 0x6c00018c7ee318ff

def z261 : W := mkw 0x37f78000093ca000 0x237f78000093ca00 0x3fff8000003e000f 0x83fff8000003e000

def z262 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x07ff8000003ff008 0x807ff8000003ff00

def z263 : W := mkw 0x88807dc01b6a0f00 0x088807dc01b6a0f0 0x80007fc01ffe0f80 0x780007fc01ffe0f8

def z264 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc6066739803e0ff8 0x5c6066739803e0ff

def z265 : W := mkw 0x1850702c10001840 0x01850702c1000184 0x7878783e1001fc77 0xf7878783e1001fc7

def z266 : W := mkw 0x0224021100000000 0x0022402110000000 0x0660673800000002 0x1066067380000000

def z267 : W := mkw 0x0000002e00001060 0x10000002e0000106 0x4000003e00000070 0x04000003e0000007

def z268 : W := mkw 0x00080842a60105ba 0x000080842a60105b 0xc01818c7ee018ff5 0xec01818c7ee018ff

def z269 : W := mkw 0x00000842a20005ba 0x000000842a20005b 0xc00018c7e0000ff0 0x4c00018c7e0000ff

def z270 : W := mkw 0x3dd9dce66e210522 0x43dd9dce66e21052 0x399998c66e000004 0x0399998c66e00000

def z271 : W := mkw 0x127f82354495e000 0x6127f82354495e00 0x407f803fe001f000 0x8407f803fe001f00

def z272 : W := mkw 0x008aa84abef1ddfa 0x1008aa84abef1ddf 0x000000001ff1fff0 0x2000000001ff1fff

def z273 : W := mkw 0x0080000008200000 0x0008000000820000 0x018000000e30000d 0x2018000000e30000

def z274 : W := mkw 0x42262b5bb216bffe 0x042262b5bb216bff 0xc6667ffff03ffffb 0xfc6667ffff03ffff

def z275 : W := mkw 0x42aeab5bbe37bffe 0x042aeab5bbe37bff 0xc66667399e3ffffb 0xfc66667399e3ffff

def z276 : W := mkw 0x00000842a20005ba 0x000000842a20005b 0xc19f98c7e0000ffd 0xcc19f98c7e0000ff

def z277 : W := mkw 0x000a8842a61185ba 0x0000a8842a61185b 0xc01f98c7e0018ff0 0xcc01f98c7e0018ff

def z278 : W := mkw 0x37ff82110dbde000 0x237ff82110dbde00 0xffffe7399ffff00f 0xfffffe7399ffff00

def z279 : W := mkw 0x7f7577bd50063a44 0x47f7577bd50063a4 0x3e606738100e7002 0x13e606738100e700

def z280 : W := mkw 0x377d0000058d6000 0x2377d0000058d600 0x3e7800001fcff007 0xa3e7800001fcff00

def z281 : W := mkw 0xa5802dc01b6a0f00 0x0a5802dc01b6a0f0 0x878007c01ffe0f88 0x2878007c01ffe0f8

def z282 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xff9fffc7fffe0f8f 0xfff9fffc7fffe0f8

def z283 : W := mkw 0xbdd07de41b6a0f00 0x0bdd07de41b6a0f0 0xfff87ffe1ffe0f8f 0xffff87ffe1ffe0f8

def z284 : W := mkw 0x0000280012400c00 0x00000280012400c0 0x000000001fc00c00 0x2000000001fc00c0

def z285 : W := mkw 0xad007dc0134a0f00 0x0ad007dc0134a0f0 0xbe007fc011ce0f82 0x5be007fc011ce0f8

def z286 : W := mkw 0x0224000000042000 0x0022400000004200 0x06600000100e7002 0x006600000100e700

def z287 : W := mkw 0xad007580114a0a00 0x0ad007580114a0a0 0xbf807fc011ce000f 0x5bf807fc011ce000

def z288 : W := mkw 0x3ffff82e1ffdfc60 0x33ffff82e1ffdfc6 0x7ffff83e1ffffc7f 0xf7ffff83e1ffffc7

def z289 : W := mkw 0x0a2456b540000000 0x40a2456b54000000 0xc6667fffe000000b 0xdc6667fffe000000

def z290 : W := mkw 0xa58285c0a93a839a 0x0a58285c0a93a839 0x878787c1e03e0388 0x0878787c1e03e038

def z291 : W := mkw 0xbd5075ac11ca5a40 0x1bd5075ac11ca5a4 0x3e60673811ce7002 0x13e60673811ce700

def z292 : W := mkw 0xad8075c0196a0b00 0x0ad8075c0196a0b0 0xbf8067c011fe038a 0x1bf8067c011fe038

def z293 : W := mkw 0x4224031100062204 0x0422403110006220 0x06000700000e0000 0x006000700000e000

def z294 : W := mkw 0xad007d80134a0e00 0x0ad007d80134a0e0 0x3e007f001fce0c07 0x73e007f001fce0c0

def z295 : W := mkw 0x0000000000000000 0x0000000000000000 0x818018c00000000d 0x4818018c00000000

def z296 : W := mkw 0x2725000000000000 0x0272500000000000 0x0787800000000008 0x0078780000000000

def z297 : W := mkw 0x422622199014b8dc 0x0422622199014b8d 0x406660399001fc73 0xf406660399001fc7

def z298 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc00600018e318ff9 0xec00600018e318ff

def z299 : W := mkw 0x1a74523500000000 0x01a7452350000000 0xfe7e7f3f8000000f 0xdfe7e7f3f8000000

def z300 : W := mkw 0xad805cc00b680500 0x0ad805cc00b68050 0xbf807fc00fc0000f 0x5bf807fc00fc0000

def z301 : W := mkw 0x10da80000cb1c000 0x010da80000cb1c00 0x39ff80001ff1f00f 0xa39ff80001ff1f00

def z302 : W := mkw 0xad807580196a0a00 0x0ad807580196a0a0 0x3f8067001ffe000f 0x33f8067001ffe000

def z303 : W := mkw 0x18daf86ebef1ddfa 0x118daf86ebef1ddf 0x7878783e1ff1fff7 0xf7878783e1ff1fff

def z304 : W := mkw 0x42ae8b53ae37a7be 0x042ae8b53ae37a7b 0xc79f9fc7ee3f8ffd 0xec79f9fc7ee3f8ff

def z305 : W := mkw 0x5afefb7fbef7fffe 0x15afefb7fbef7fff 0xffffffffffffffff 0xffffffffffffffff

def z306 : W := mkw 0x422e821ba415b0fe 0x0422e821ba415b0f 0x407f803fe001f070 0x8407f803fe001f07

def z307 : W := mkw 0x127f802e0495f060 0x3127f802e0495f06 0x407f803e0001f070 0x8407f803e0001f07

def z308 : W := mkw 0x48007b3f92421efc 0x148007b3f92421ef 0xc0007f3f80000ff0 0x5c0007f3f80000ff

def z309 : W := mkw 0x080056b540000000 0x4080056b54000000 0xc0007fffe0000000 0x5c0007fffe000000

def z310 : W := mkw 0x37ff88422fbde522 0x237ff88422fbde52 0x3fff98c67ffff00f 0xa3fff98c67ffff00

def z311 : W := mkw 0x37f5000009ac6000 0x237f5000009ac600 0x3fe000001ffe700f 0x23fe000001ffe700

def z312 : W := mkw 0x5277023dc014b0dc 0x45277023dc014b0d 0x407f803fe001f070 0x8407f803fe001f07

def z313 : W := mkw 0x1858502e04815060 0x11858502e0481506 0x7878783e0001f077 0xd7878783e0001f07

def z314 : W := mkw 0x2d8078001b680c00 0x02d8078001b680c0 0x3f8078001ffe0c0f 0x73f8078001ffe0c0

def z315 : W := mkw 0x4a267b3f9256befc 0x14a267b3f9256bef 0xc6667f3f903ffffb 0xfc6667f3f903ffff

def z316 : W := mkw 0xfffe7fff9ffffffc 0x1fffe7fff9ffffff 0xfffe7fff9fffffff 0xffffe7fff9ffffff

def z317 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z318 : W := mkw 0x422603118016a29c 0x0422603118016a29 0xc6666739803e038b 0xdc6666739803e038

def z319 : W := mkw 0x0000080002000400 0x0000008000200040 0x000018000e000c05 0x6000018000e000c0

def z320 : W := mkw 0x5a76733d9016badc 0x05a76733d9016bad 0xfe7e7f3f903fffff 0xffe7e7f3f903ffff

def z321 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbf9f9fc7e000000c 0x0bf9f9fc7e000000

def z322 : W := mkw 0x18dad866aef1c5ba 0x118dad866aef1c5b 0xf99f98c7eff18ffd 0xef99f98c7eff18ff

def z323 : W := mkw 0x3f7d782e17cd7c60 0x33f7d782e17cd7c6 0x7e78783e1fcffc77 0xf7e78783e1fcffc7

def z324 : W := mkw 0x3ffffebf5ffdfc60 0x73ffffebf5ffdfc6 0xfffffffffffffc7f 0xffffffffffffffc7

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x818780c1e0000008 0x0818780c1e000000

def z326 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x386060381fc1fc72 0x3386060381fc1fc7

def z327 : W := mkw 0x2d805cc00a200500 0x02d805cc00a20050 0xbf807fc00e300f8f 0x7bf807fc00e300f8

def z328 : W := mkw 0xad827dc09b7a8f98 0x0ad827dc09b7a8f9 0xff867fc19fff8fff 0xfff867fc19fff8ff

def z329 : W := mkw 0x022621001016aa00 0x0022621001016aa0 0x86666700103fff8b 0xf86666700103fff8

def z330 : W := mkw 0xa5000580010a0200 0x0a5000580010a020 0x06000700000e0000 0x006000700000e000

def z331 : W := mkw 0x3dd9f82e1fe95c60 0x33dd9f82e1fe95c6 0x79f9f83e1fc1fc77 0xf79f9f83e1fc1fc7

def z332 : W := mkw 0xbffd7fff5feb5f60 0x5bffd7fff5feb5f6 0xffffffffffffffff 0xffffffffffffffff

def z333 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0x398018c01ffe0f84 0x2398018c01ffe0f8

def z334 : W := mkw 0x35d988422fa94522 0x235d988422fa9452 0x399998c66fc00004 0x0399998c66fc0000

def z335 : W := mkw 0xbdd85ce60fe94520 0x1bdd85ce60fe9452 0x399818c60fc00004 0x0399818c60fc0000

def z336 : W := mkw 0x5a7c7b3f16c77e64 0x15a7c7b3f16c77e6 0x7e787f3e1fcffc77 0xf7e787f3e1fcffc7

def z337 : W := mkw 0x0000210010020a00 0x00000210010020a0 0x8000670000000f80 0x58000670000000f8

def z338 : W := mkw 0x808029401b6a0f00 0x0808029401b6a0f0 0x860067001ffe0f8b 0x7860067001ffe0f8

def z339 : W := mkw 0x4224231910063a44 0x04224231910063a4 0x86606738103e7f8b 0x786606738103e7f8

def z340 : W := mkw 0xad807dee1b6a1f60 0x1ad807dee1b6a1f6 0xff807ffe1ffe0fff 0x7ff807ffe1ffe0ff

def z341 : W := mkw 0x3551000000000000 0x0355100000000000 0x3999800000000004 0x0399980000000000

def z342 : W := mkw 0xef247799114e3a44 0x0ef247799114e3a4 0x3e60673811ce7002 0x13e60673811ce700

def z343 : W := mkw 0x3ffffefffef1ddfa 0x53ffffefffef1ddf 0xfffffffffff1ffff 0xffffffffffff1fff

def z344 : W := mkw 0xbdd87de61feb4f20 0x1bdd87de61feb4f2 0xbf987fc61ffe0f8f 0x7bf987fc61ffe0f8

def z345 : W := mkw 0x422603198016b2dc 0x0422603198016b2d 0xc6660739803ff3f8 0x8c6660739803ff3f

def z346 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0xf99f98c7e000000d 0xcf99f98c7e000000

def z347 : W := mkw 0x02ae8842ae35a5ba 0x002ae8842ae35a5b 0xc7ff98c7fe3fffff 0xec7ff98c7fe3ffff

def z348 : W := mkw 0x00888842ae2105ba 0x000888842ae2105b 0xc19998c7ee000ff4 0x4c19998c7ee000ff

def z349 : W := mkw 0x98d8796e1feb5f60 0x198d8796e1feb5f6 0x7878783e1ffffff7 0xf7878783e1ffffff

def z350 : W := mkw 0x37ffa80a1ffdfc60 0x337ffa80a1ffdfc6 0x3fff80001ffffc7f 0xa3fff80001ffffc7

def z351 : W := mkw 0x127f80000495e000 0x2127f80000495e00 0x387f80001fc1f007 0xa387f80001fc1f00

def z352 : W := mkw 0x377f80000495e000 0x2377f80000495e00 0x3fff80000001f00f 0x83fff80000001f00

def z353 : W := mkw 0x008a80000dbde000 0x2008a80000dbde00 0x019f80001ffff00d 0xa019f80001ffff00

def z354 : W := mkw 0x77ffa3191dbffa44 0x277ffa3191dbffa4 0x3fffe7381ffff00f 0xb3fffe7381ffff00

def z355 : W := mkw 0x0000021100000000 0x0000002110000000 0xc000673980000000 0x5c00067398000000

def z356 : W := mkw 0xbf757ff552420f00 0x4bf757ff552420f0 0xffffffffe0000f8f 0xdffffffffe0000f8

def z357 : W := mkw 0x000a8802a61184ba 0x0000a8802a61184b 0x401f9807ee018c75 0xe401f9807ee018c7

def z358 : W := mkw 0xbffffff55fffef00 0x6bffffff55fffef0 0xffffffffffffff8f 0xfffffffffffffff8

def z359 : W := mkw 0x0008280a16c15c60 0x10008280a16c15c6 0x401818061fc1fc75 0xe401818061fc1fc7

def z360 : W := mkw 0x008008400a200500 0x0008008400a20050 0x018018c00e000004 0x0018018c00e00000

def z361 : W := mkw 0xbdd17de45b6a0f00 0x4bdd17de45b6a0f0 0xbf99ffc67ffe0f8f 0x7bf99ffc67ffe0f8

def z362 : W := mkw 0x2d8adcc2ae3185ba 0x02d8adcc2ae3185b 0xff9fffc7ee318fff 0xfff9fffc7ee318ff

def z363 : W := mkw 0x1058280a16c15c60 0x11058280a16c15c6 0x387800001fc1fc77 0xa387800001fc1fc7

def z364 : W := mkw 0x4224231910063a44 0x04224231910063a4 0x46606738100ffc73 0xf46606738100ffc7

def z365 : W := mkw 0xad8afdc01fffef00 0x2ad8afdc01fffef0 0xbf807fc01fffff8f 0x7bf807fc01fffff8

def z366 : W := mkw 0x400221089016badc 0x0400221089016bad 0x86006700103ffffb 0x786006700103ffff

def z367 : W := mkw 0x422602198014b0dc 0x0422602198014b0d 0xc66667398001f07b 0xdc66667398001f07

def z368 : W := mkw 0xed807fd99b6a1fdc 0x0ed807fd99b6a1fd 0xff807ff99ffe0fff 0x7ff807ff99ffe0ff

def z369 : W := mkw 0x022600000014a000 0x0022600000014a00 0x006600000001f000 0x8006600000001f00

def z370 : W := mkw 0x3f7fd6b7e41180ba 0x43f7fd6b7e41180b 0xffffffffe001807f 0xdffffffffe001807

def z371 : W := mkw 0x0000000000000000 0x0000000000000000 0x006000001001f003 0xa006000001001f00

def z372 : W := mkw 0x3fffd4a44dbde000 0x63fffd4a44dbde00 0x3fff98c67ffff00f 0xa3fff98c67ffff00

def z373 : W := mkw 0x37fd80000dad6000 0x237fd80000dad600 0x3ff980001fce7006 0x03ff980001fce700

def z374 : W := mkw 0x0000000000000000 0x0000000000000000 0x380000001fc00007 0x2380000001fc0000

def z375 : W := mkw 0x5a76733d90d6fadc 0x15a76733d90d6fad 0xfe66673991fffffb 0xffe66673991fffff

def z376 : W := mkw 0xa5800dc00b2a0700 0x0a5800dc00b2a070 0x87801fc00e3e0f8d 0x687801fc00e3e0f8

def z377 : W := mkw 0x3775000000000000 0x0377500000000000 0xffff98c7e000000f 0xcffff98c7e000000

def z378 : W := mkw 0x1058200814815840 0x0105820081481584 0x787860381fc1fc77 0xf787860381fc1fc7

def z379 : W := mkw 0x1a7ff82e16d5fc60 0x31a7ff82e16d5fc6 0x787ff83e1fc1fc77 0xf787ff83e1fc1fc7

def z380 : W := mkw 0xca267fd99256bfdc 0x0ca267fd99256bfd 0xc6667ff9903ffffb 0xfc6667ff9903ffff

def z381 : W := mkw 0x0002000000108000 0x0000200000010800 0x0006000000318009 0xa000600000031800

def z382 : W := mkw 0x4224231910063a44 0x04224231910063a4 0xc6666739900e700b 0xdc6666739900e700

def z383 : W := mkw 0x888079401b6a0f00 0x0888079401b6a0f0 0x380078001ffe0f87 0x7380078001ffe0f8

def z384 : W := mkw 0xe7a627d9993ebbdc 0x0e7a627d9993ebbd 0xc7e667f9903ffffb 0xfc7e667f9903ffff

def z385 : W := mkw 0x258a80000d398000 0x0258a80000d39800 0x3f9f80001fff800f 0xa3f9f80001fff800

def z386 : W := mkw 0x1850782c12c05c40 0x11850782c12c05c4 0x386078381fc07c07 0x7386078381fc07c0

def z387 : W := mkw 0x3775000000000000 0x0377500000000000 0x3fff80000000000f 0x83fff80000000000

def z388 : W := mkw 0x7ffff7bdddbffadc 0x67ffff7bdddbffad 0xffffffffffffffff 0xffffffffffffffff

def z389 : W := mkw 0x008888422e210522 0x0008888422e21052 0x819998c66e300f8d 0x6819998c66e300f8

def z390 : W := mkw 0x0000200810001840 0x0000020081000184 0x4000603800000c70 0x54000603800000c7

def z391 : W := mkw 0x88007dc012420f00 0x088007dc012420f0 0x86007fc0103e0f8b 0x786007fc0103e0f8

def z392 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x79ff98ffe0000004 0x879ff98ffe000000

def z393 : W := mkw 0x422621089016badc 0x0422621089016bad 0x06660000103ffffb 0xa06660000103ffff

def z394 : W := mkw 0x022600000014a000 0x0022600000014a00 0x06060000003e0008 0x006060000003e000

def z395 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x7e787f3e00000007 0xd7e787f3e0000000

def z396 : W := mkw 0x08005ef7e20005ba 0x408005ef7e20005b 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z397 : W := mkw 0x1858782616c14c20 0x11858782616c14c2 0x381878061fc00c07 0x7381878061fc00c0

def z398 : W := mkw 0x0008000004814000 0x0000800000481400 0x000000001fc1f000 0x2000000001fc1f00

def z399 : W := mkw 0xa58029401b6a0f00 0x0a58029401b6a0f0 0x3f8000001ffe0f8f 0x23f8000001ffe0f8

def z400 : W := mkw 0x0800548000000000 0x0080054800000000 0x80007fc000000000 0x580007fc00000000

def z401 : W := mkw 0x4224021900043044 0x0422402190004304 0x0060003800007000 0x0006000380000700

def z402 : W := mkw 0x18d8786e1ee15d60 0x118d8786e1ee15d6 0xf9f878fe1ff1ffff 0xff9f878fe1ff1fff

def z403 : W := mkw 0x422603118016a29c 0x0422603118016a29 0x86660701903ff38b 0xa86660701903ff38

def z404 : W := mkw 0xbf7577b5514a0a00 0x4bf7577b5514a0a0 0x3e60673811ce0002 0x13e60673811ce000

def z405 : W := mkw 0x77ffab5bbfbffffe 0x277ffab5bbfbffff 0xffffffffffffffff 0xffffffffffffffff

def z406 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x7e7fe73fe0000002 0x97e7fe73fe000000

def z407 : W := mkw 0x1a75523540000000 0x41a7552354000000 0x787ff83fe0000007 0xd787ff83fe000000

def z408 : W := mkw 0xafa7fdc01b7eaf00 0x2afa7fdc01b7eaf0 0xbf87ffc01ffe0f8f 0x7bf87ffc01ffe0f8

def z409 : W := mkw 0x3f757eb552400c00 0x43f757eb552400c0 0xffffffffffc00c0f 0xfffffffffffc00c0

def z410 : W := mkw 0xffffffd99fffffdc 0x2ffffffd99fffffd 0xfffffff99fffffff 0xffffffff99ffffff

def z411 : W := mkw 0x4000231990021adc 0x04000231990021ad 0xc6006739903e0ffb 0x7c6006739903e0ff

def z412 : W := mkw 0x2580000009280000 0x0258000000928000 0x07800000003e0008 0x007800000003e000

def z413 : W := mkw 0x008a8042ac3181ba 0x0008a8042ac3181b 0xc19f80c7e03183f8 0x8c19f80c7e03183f

def z414 : W := mkw 0x008880000da94000 0x2008880000da9400 0x000000000fc00000 0x0000000000fc0000

def z415 : W := mkw 0xbf7577b5514a0a00 0x4bf7577b5514a0a0 0xfffffffff1ce000f 0xdfffffffff1ce000

def z416 : W := mkw 0x1a7c7a3f16c15c60 0x11a7c7a3f16c15c6 0xfe7e7f3f9fc1fc7f 0xffe7e7f3f9fc1fc7

def z417 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x3878783e1fc07006 0x13878783e1fc0700

def z418 : W := mkw 0x4a267b199256bedc 0x04a267b199256bed 0xfe667f399fffffff 0xffe667f399ffffff

def z419 : W := mkw 0x1058282e16c15c60 0x11058282e16c15c6 0x4078003e1fc1fc70 0xa4078003e1fc1fc7

def z420 : W := mkw 0x1850502400000000 0x0185050240000000 0x3860603800000002 0x1386060380000000

def z421 : W := mkw 0xbffff5801dffea00 0x2bffff5801dffea0 0x3fffe7001ffff00f 0xb3fffe7001ffff00

def z422 : W := mkw 0x400200088014b0dc 0x0400200088014b0d 0x000000000001f070 0x0000000000001f07

def z423 : W := mkw 0x0808780216410c20 0x00808780216410c2 0x781878061fc18c77 0xf781878061fc18c7

def z424 : W := mkw 0x7ffffb3f9ffffefc 0x37ffffb3f9ffffef 0xffffff3f9fffffff 0xfffffff3f9ffffff

def z425 : W := mkw 0x8088294a1feb5f60 0x18088294a1feb5f6 0x000000001ffffff0 0x2000000001ffffff

def z426 : W := mkw 0x3ff55ef54a200500 0x43ff55ef54a20050 0xffffffffee300f8f 0xfffffffffee300f8

def z427 : W := mkw 0xbdd9dcc00fe94500 0x2bdd9dcc00fe9450 0x399998c00fc00004 0x0399998c00fc0000

def z428 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x401f8007ee318ff0 0xa401f8007ee318ff

def z429 : W := mkw 0x1858582606010420 0x0185858260601042 0x7878783e0e018c77 0xf7878783e0e018c7

def z430 : W := mkw 0x37750000018c6000 0x237750000018c600 0x3fff800011ce700f 0x83fff800011ce700

def z431 : W := mkw 0x77ff82198dbdf0dc 0x277ff82198dbdf0d 0x7fff80399ffff07f 0xa7fff80399ffff07

def z432 : W := mkw 0x1850702c10c05840 0x11850702c10c0584 0x7878783e11c07007 0xd7878783e11c0700

def z433 : W := mkw 0x422623199016badc 0x0422623199016bad 0x40660039903ffff0 0xa40660039903ffff

def z434 : W := mkw 0x1858582e06c15460 0x11858582e06c1546 0x7878183e0fc1f074 0x87878183e0fc1f07

def z435 : W := mkw 0x422623199016badc 0x0422623199016bad 0x06606738103ffff2 0x306606738103ffff

def z436 : W := mkw 0x4000210810063a44 0x04000210810063a4 0x00000000100e7000 0x000000000100e700

def z437 : W := mkw 0xbf75758011ce6a00 0x2bf75758011ce6a0 0x3e60670011ce7002 0x13e60670011ce700

def z438 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0x3800000000000000 0x0380000000000000

def z439 : W := mkw 0x400221089016badc 0x0400221089016bad 0x40606038103ffff3 0xf40606038103ffff

def z440 : W := mkw 0x008808420e210520 0x0008808420e21052 0xc19818c60e318ffd 0xec19818c60e318ff

def z441 : W := mkw 0x2d00548000000000 0x02d0054800000000 0xff9fffc7e000000f 0xdff9fffc7e000000

def z442 : W := mkw 0xa7a507d1492a0300 0x4a7a507d1492a030 0x878787c1e03e0388 0x0878787c1e03e038

def z443 : W := mkw 0x0082800008308000 0x0008280000830800 0x0187800000300008 0x0018780000030000

def z444 : W := mkw 0x00000000018c6000 0x200000000018c600 0x0000000011ce7000 0x00000000011ce700

def z445 : W := mkw 0x0000000000000000 0x0000000000000000 0x4060603800000003 0xd406060380000000

def z446 : W := mkw 0x7f7757b5c016a29c 0x47f7757b5c016a29 0xffffffffe03e038f 0xdffffffffe03e038

def z447 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x819f98c7ee30038c 0x0819f98c7ee30038

def z448 : W := mkw 0x3ffff02c1dfdf840 0x33ffff02c1dfdf84 0x3fffe0381ffff00f 0xb3fffe0381ffff00

def z449 : W := mkw 0x88807dc01a620f00 0x088807dc01a620f0 0x81807fc00e300f8d 0x781807fc00e300f8

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0x019f80000000000d 0x8019f80000000000

def z451 : W := mkw 0xad8afdc01f7b8f00 0x0ad8afdc01f7b8f0 0xbf9fffc01fff8f8f 0xfbf9fffc01fff8f8

def z452 : W := mkw 0x0224021100000000 0x0022402110000000 0x8606070180000008 0x0860607018000000

def z453 : W := mkw 0x2d00758010020a00 0x02d00758010020a0 0xbf807fc0103e0f8f 0x7bf807fc0103e0f8

def z454 : W := mkw 0x37ff82354dbde000 0x637ff82354dbde00 0x7fff803ffffff00f 0xa7fff803ffffff00

def z455 : W := mkw 0x3f7d56b544814000 0x43f7d56b54481400 0xffffffffffc1f00f 0xfffffffffffc1f00

def z456 : W := mkw 0x185056b540000000 0x4185056b54000000 0xf8787fffe0000007 0xdf8787fffe000000

def z457 : W := mkw 0x1850502400c04000 0x11850502400c0400 0x3800000001c00000 0x03800000001c0000

def z458 : W := mkw 0x1275000000000000 0x0127500000000000 0x007f800000000000 0x8007f80000000000

def z459 : W := mkw 0xb7ffa9401fffef00 0x2b7ffa9401fffef0 0x3fff80001fffff8f 0xa3fff80001fffff8

def z460 : W := mkw 0x37ff8040adbde19a 0x237ff8040adbde19 0xbfff80c1fffff38f 0xabfff80c1fffff38

def z461 : W := mkw 0x3775021100000000 0x0377502110000000 0xffffe7398000000f 0xdffffe7398000000

def z462 : W := mkw 0x40000219800010dc 0x040000219800010d 0x4000003980000070 0x0400000398000007

def z463 : W := mkw 0x0000200810001840 0x0000020081000184 0x000000001001fc70 0x2000000001001fc7

def z464 : W := mkw 0x2500048000000000 0x0250004800000000 0x878007c000000008 0x0878007c00000000

def z465 : W := mkw 0x37770000019ce000 0x237770000019ce00 0x3e66000011fff00b 0xa3e66000011fff00

def z466 : W := mkw 0x1858582606c14420 0x11858582606c1442 0x781818060fc18c75 0xe781818060fc18c7

def z467 : W := mkw 0x422602198014b0dc 0x0422602198014b0d 0xc06600398031fff9 0xec06600398031fff

def z468 : W := mkw 0x7f7f7fbfd6d7fefc 0x57f7f7fbfd6d7fef 0xffffffffffffffff 0xffffffffffffffff

def z469 : W := mkw 0x527f82198495f0dc 0x2527f82198495f0d 0x407f80398001f070 0x8407f80398001f07

def z470 : W := mkw 0x008888422e210522 0x0008888422e21052 0xc19f98c7ee00000d 0xcc19f98c7ee00000

def z471 : W := mkw 0x000a0802861184b8 0x0000a0802861184b 0xc01e18078e318ffd 0xec01e18078e318ff

def z472 : W := mkw 0x0000010000020200 0x0000001000002020 0x86000700003e0388 0x086000700003e038

def z473 : W := mkw 0x088af842be718dba 0x0088af842be718db 0xf99ff8c7fff18fff 0xff99ff8c7fff18ff

def z474 : W := mkw 0xa7a785c0093ea300 0x2a7a785c0093ea30 0x878787c0003e0388 0x0878787c0003e038

def z475 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x019998c66e318ff4 0x2019998c66e318ff

def z476 : W := mkw 0x77772319919efadc 0x277772319919efad 0xfe66673991fffffb 0xffe66673991fffff

def z477 : W := mkw 0x00800842aa2005ba 0x000800842aa2005b 0xc18018c7ee300ffd 0x6c18018c7ee300ff

def z478 : W := mkw 0x1050002c00805040 0x11050002c0080504 0x0060003800007000 0x0006000380000700

def z479 : W := mkw 0x3775069140000000 0x4377506914000000 0xbfff87c1e000000f 0x8bfff87c1e000000

def z480 : W := mkw 0xad007dc012420f00 0x0ad007dc012420f0 0xbf807fc000000f8f 0x5bf807fc000000f8

def z481 : W := mkw 0x022780000014a000 0x2022780000014a00 0x0007800000000000 0x0000780000000000

def z482 : W := mkw 0x008a8002ac3180ba 0x0008a8002ac3180b 0x419f8007ee31807d 0xa419f8007ee31807

def z483 : W := mkw 0xad8adcc2af7985ba 0x0ad8adcc2af7985b 0xf99f98c7eff18ffd 0xef99f98c7eff18ff

def z484 : W := mkw 0xbddafdeebffbdffa 0x1bddafdeebffbdff 0xffffffffffffffff 0xffffffffffffffff

def z485 : W := mkw 0x0800500000000000 0x0080050000000000 0x3800780000000007 0x5380078000000000

def z486 : W := mkw 0x0008080206c14420 0x10008080206c1442 0x000000000fc00000 0x0000000000fc0000

def z487 : W := mkw 0x808008400b680500 0x0808008400b68050 0x000000000fc00000 0x0000000000fc0000

def z488 : W := mkw 0x0224021100000000 0x0022402110000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z489 : W := mkw 0x0008800224010022 0x0000880022401002 0x0019800660000000 0x0001980066000000

def z490 : W := mkw 0x00828842aa3085ba 0x000828842aa3085b 0xc18798c7e0300ff8 0x4c18798c7e0300ff

def z491 : W := mkw 0x27a78000093ca000 0x227a78000093ca00 0x07e78000103ff00b 0xa07e78000103ff00

def z492 : W := mkw 0x0000000000000000 0x0000000000000000 0x06000000103e000b 0x206000000103e000

def z493 : W := mkw 0x42a6a359b836bbde 0x042a6a359b836bbd 0xc7e7e7f9f03ffffb 0xfc7e7e7f9f03ffff

def z494 : W := mkw 0x7f7577bd50063a44 0x47f7577bd50063a4 0xfffffffff00e700f 0xdfffffffff00e700

def z495 : W := mkw 0x008aa84abe319dfa 0x0008aa84abe319df 0xc1fff8fffe31ffff 0xfc1fff8fffe31fff

def z496 : W := mkw 0x1058002604814020 0x1105800260481402 0x0018000600000000 0x0001800060000000

def z497 : W := mkw 0x18daf82e1ffdfc60 0x318daf82e1ffdfc6 0x7878783e1ffffc77 0xf7878783e1ffffc7

def z498 : W := mkw 0x1058000004814000 0x0105800000481400 0x007800000001f000 0x8007800000001f00

def z499 : W := mkw 0x008888422e210522 0x0008888422e21052 0x419998c66e018c75 0xe419998c66e018c7

def z500 : W := mkw 0xb7ff85c00dbfe300 0x2b7ff85c00dbfe30 0xbfff87c01ffff38f 0xabfff87c01ffff38

def z501 : W := mkw 0x2500000000000000 0x0250000000000000 0x3f8000000000000f 0x03f8000000000000

def z502 : W := mkw 0x008a80008c318098 0x0008a80008c31809 0xc19f80018e318ffd 0xec19f80018e318ff

def z503 : W := mkw 0x02ae8a53ae3185ba 0x002ae8a53ae3185b 0xc7ffffffee318fff 0xfc7ffffffee318ff

def z504 : W := mkw 0x4002231990129adc 0x04002231990129ad 0xc006673980318ff9 0xfc006673980318ff

def z505 : W := mkw 0x40002b5bb2021ffe 0x040002b5bb2021ff 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z506 : W := mkw 0x35db80000dbde000 0x235db80000dbde00 0x399980001ffff004 0x2399980001ffff00

def z507 : W := mkw 0x37fd80000da94000 0x237fd80000da9400 0x3fff80000fc0000f 0x83fff80000fc0000

def z508 : W := mkw 0xad887dca1feb5f60 0x1ad887dca1feb5f6 0xbf807fc01fffffff 0x7bf807fc01ffffff

def z509 : W := mkw 0x000a8002a41180ba 0x0000a8002a41180b 0xc19f98c7e001807d 0xcc19f98c7e001807

def z510 : W := mkw 0x02ae80000c35a000 0x002ae80000c35a00 0x07ff80001e3ff00f 0xa07ff80001e3ff00

def z511 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x818018c00e318ffd 0x6818018c00e318ff

def z512 : W := mkw 0x0000069140000000 0x4000006914000000 0x800007c1e0000000 0x0800007c1e000000

def z513 : W := mkw 0x3f7554a440000000 0x43f7554a44000000 0x3fff98c66000000f 0x83fff98c66000000

def z514 : W := mkw 0x42a62b599a36bfdc 0x042a62b599a36bfd 0xc7e67ff99e3fffff 0xfc7e67ff99e3ffff

def z515 : W := mkw 0x37ff8842afbde5ba 0x237ff8842afbde5b 0x3fff80001fffffff 0xa3fff80001ffffff

def z516 : W := mkw 0x408aab5bbe339ffe 0x0408aab5bbe339ff 0xc19fffffee318ffd 0xfc19fffffee318ff

def z517 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x4078783e0001fc70 0xd4078783e0001fc7

def z518 : W := mkw 0x1858702c14c15840 0x11858702c14c1584 0x387860381fc1f007 0xb387860381fc1f00

def z519 : W := mkw 0x18d8d8662ee14522 0x118d8d8662ee1452 0x399998c66fc00004 0x0399998c66fc0000

def z520 : W := mkw 0x00828040a830819a 0x000828040a830819 0xc19f98c7e030038d 0xcc19f98c7e030038

def z521 : W := mkw 0x35db80000db9c000 0x235db80000db9c00 0x399f80000ff1800d 0xa399f80000ff1800

def z522 : W := mkw 0x2f2556b540000000 0x42f2556b54000000 0xc787ffffe0000008 0x5c787ffffe000000

def z523 : W := mkw 0xc08229489b7ebfdc 0x0c08229489b7ebfd 0x000000001ffffff0 0x2000000001ffffff

def z524 : W := mkw 0x3f7576bd50c05840 0x53f7576bd50c0584 0xfffffffff1c0700f 0xdfffffffff1c0700

def z525 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xb9807fc00fc00f84 0x5b9807fc00fc00f8

def z526 : W := mkw 0x1a7d7a3f56c15c60 0x51a7d7a3f56c15c6 0x787ff83fffc1fc77 0xf787ff83fffc1fc7

def z527 : W := mkw 0x808029401b6a0f00 0x0808029401b6a0f0 0x818018c01ffe0f8d 0x6818018c01ffe0f8

def z528 : W := mkw 0x42a68351a836a39e 0x042a68351a836a39 0x878787c1e03e0388 0x0878787c1e03e038

def z529 : W := mkw 0x008aa84abef1ddfa 0x1008aa84abef1ddf 0xc19f98c7fff1fffd 0xec19f98c7fff1fff

def z530 : W := mkw 0x00022008901098d8 0x000022008901098d 0xc06660399031fffb 0xfc06660399031fff

def z531 : W := mkw 0x422603118016a29c 0x0422603118016a29 0xc6060701803f8ff9 0xec6060701803f8ff

def z532 : W := mkw 0x0800582602400420 0x1080058260240042 0x0000180600000000 0x0000018060000000

def z533 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x818780c1ee318ff8 0x2818780c1ee318ff

def z534 : W := mkw 0x37ffa0081dbdf840 0x237ffa0081dbdf84 0x7fffe0381ffffc7f 0xf7fffe0381ffffc7

def z535 : W := mkw 0x185a782e96d1dcf8 0x1185a782e96d1dcf 0xf87e783f9ff1ffff 0xff87e783f9ff1fff

def z536 : W := mkw 0x1850502400000000 0x0185050240000000 0x3818180600000004 0x0381818060000000

def z537 : W := mkw 0x88005cc002400500 0x088005cc00240050 0x000018c000000000 0x0000018c00000000

def z538 : W := mkw 0x3f7d5eb746c14420 0x53f7d5eb746c1442 0xffffffffefc0000f 0xdffffffffefc0000

def z539 : W := mkw 0xbdd07dec1bea5f40 0x1bdd07dec1bea5f4 0xbfe07ff81ffe7f8f 0x7bfe07ff81ffe7f8

def z540 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x3fffe7380000000f 0x93fffe7380000000

def z541 : W := mkw 0x400201008016a29c 0x0400201008016a29 0x00000000003e0380 0x000000000003e038

def z542 : W := mkw 0x3fffd6b54dbde000 0x63fffd6b54dbde00 0x3fffe7381ffff00f 0xb3fffe7381ffff00

def z543 : W := mkw 0x0002210090128a98 0x00002210090128a9 0xc6066701903f8ffb 0xfc6066701903f8ff

def z544 : W := mkw 0xafa67dc01b7eaf00 0x0afa67dc01b7eaf0 0xbfe67fc01fffff8f 0xfbfe67fc01fffff8

def z545 : W := mkw 0xbdd87cee1fe95d60 0x1bdd87cee1fe95d6 0x79f878fe1fc1fc77 0xf79f878fe1fc1fc7

def z546 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfe607fffe0000002 0x5fe607fffe000000

def z547 : W := mkw 0x4224231990063adc 0x04224231990063ad 0xc6606739900e7ff2 0x5c6606739900e7ff

def z548 : W := mkw 0x377f8000059de000 0x2377f8000059de00 0x3e7f800011cff002 0x83e7f800011cff00

def z549 : W := mkw 0x0800502400000000 0x0080050240000000 0x4000783e00000000 0x54000783e0000000

def z550 : W := mkw 0x0008000204010020 0x0000800020401002 0x4018000600018070 0x8401800060001807

def z551 : W := mkw 0x3f7756b54014a000 0x43f7756b54014a00 0xfffffffff03ff00f 0xffffffffff03ff00

def z552 : W := mkw 0x080056b540000000 0x4080056b54000000 0x0000673800000000 0x1000067380000000

def z553 : W := mkw 0xad88dcc22f690522 0x0ad88dcc22f69052 0x399998c66fc00004 0x0399998c66fc0000

def z554 : W := mkw 0x527fa3199497fadc 0x2527fa3199497fad 0xc67fe739903ffffb 0xfc67fe739903ffff

def z555 : W := mkw 0x1275000000846000 0x2127500000084600 0x0060000000007000 0x0006000000000700

def z556 : W := mkw 0x008029401a220f00 0x0008029401a220f0 0x87807fc01e3e0f8f 0x787807fc01e3e0f8

def z557 : W := mkw 0x0000280a12401c60 0x10000280a12401c6 0x0000000000000c70 0x00000000000000c7

def z558 : W := mkw 0x0000023540000000 0x4000002354000000 0x4000003fe0000000 0x04000003fe000000

def z559 : W := mkw 0x1275023540000000 0x4127502354000000 0x0060003800000000 0x0006000380000000

def z560 : W := mkw 0x1858780016c14c00 0x01858780016c14c0 0x387878001fc1fc07 0xf387878001fc1fc0

def z561 : W := mkw 0x008a8040ac31819a 0x0008a8040ac31819 0x819f80c1ee31838d 0xa819f80c1ee31838

def z562 : W := mkw 0x0008080206010420 0x0000808020601042 0xc19f98c7ee018c7d 0xec19f98c7ee018c7

def z563 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x419f98c7ee018074 0x8419f98c7ee01807

def z564 : W := mkw 0x808aa9401fffef00 0x2808aa9401fffef0 0x000000001fffff80 0x2000000001fffff8

def z565 : W := mkw 0x000a80000495e000 0x2000a80000495e00 0x000000000001f000 0x0000000000001f00

def z566 : W := mkw 0x8800758010420a00 0x08800758010420a0 0x0000670000000000 0x1000067000000000

def z567 : W := mkw 0xbff557f5492a0300 0x4bff557f5492a030 0xffffffffe03e038f 0xdffffffffe03e038

def z568 : W := mkw 0x1850782e12c05c60 0x11850782e12c05c6 0x7860783e11c07c72 0x57860783e11c07c7

def z569 : W := mkw 0x80800140092a0300 0x080800140092a030 0x00000000003e0380 0x000000000003e038

def z570 : W := mkw 0x0000000800001040 0x0000000080000104 0x406000380001f070 0x8406000380001f07

def z571 : W := mkw 0x77ffa1089dbffadc 0x277ffa1089dbffad 0x3fff80001fffffff 0xa3fff80001ffffff

def z572 : W := mkw 0x3fffd4800dbde000 0x23fffd4800dbde00 0xbfffffc01ffff00f 0xfbfffffc01ffff00

def z573 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0x3f807fc01fce0006 0x13f807fc01fce000

def z574 : W := mkw 0x127d023f44815060 0x5127d023f4481506 0x407f803fe001f070 0x8407f803fe001f07

def z575 : W := mkw 0x2501048040000000 0x4250104804000000 0x018180c060000000 0x0018180c06000000

def z576 : W := mkw 0x1a7e782e16d5fc60 0x11a7e782e16d5fc6 0x7e7e783e1ffffc7f 0xf7e7e783e1ffffc7

def z577 : W := mkw 0x3f7fd6b54495e000 0x63f7fd6b54495e00 0xffffffffe001f00f 0xdffffffffe001f00

def z578 : W := mkw 0x0000210010020a00 0x00000210010020a0 0x00000000103e0f80 0x200000000103e0f8

def z579 : W := mkw 0x12ff80000dbde000 0x212ff80000dbde00 0x007f80001ffff000 0xa007f80001ffff00

def z580 : W := mkw 0x00020842a21085ba 0x000020842a21085b 0xc00618c7e0318ff9 0xec00618c7e0318ff

def z581 : W := mkw 0x00000002a00000ba 0x000000002a00000b 0x40000007e0000070 0x040000007e000007

def z582 : W := mkw 0x008888422e210522 0x0008888422e21052 0x000000000e000000 0x0000000000e00000

def z583 : W := mkw 0x0080000009280000 0x0008000000928000 0x000000001ffe0000 0x2000000001ffe000

def z584 : W := mkw 0x2d00548000000000 0x02d0054800000000 0x398018c000000004 0x0398018c00000000

def z585 : W := mkw 0x258008400b280500 0x0258008400b28050 0xbf8018c01ffe0f8f 0x6bf8018c01ffe0f8

def z586 : W := mkw 0x422623191016ba44 0x0422623191016ba4 0x06666738103ff00b 0xb06666738103ff00

def z587 : W := mkw 0x008a80000c318000 0x0008a80000c31800 0xc19f98c7ee31800d 0xec19f98c7ee31800

def z588 : W := mkw 0x0000000080000098 0x0000000008000009 0xc000000180000ff0 0x4c000000180000ff

def z589 : W := mkw 0x27af80000dbde000 0x227af80000dbde00 0x078780001ffff008 0x2078780001ffff00

def z590 : W := mkw 0x27a78000093ca000 0x227a78000093ca00 0x3f8780001ffe000f 0x23f8780001ffe000

def z591 : W := mkw 0x0224000000000000 0x0022400000000000 0x066600000000000b 0x8066600000000000

def z592 : W := mkw 0x27af80000d3da000 0x227af80000d3da00 0x079f80000e3f800d 0xa079f80000e3f800

def z593 : W := mkw 0xad807dc2bb6a0fba 0x0ad807dc2bb6a0fb 0xff807fc7fffe0fff 0x7ff807fc7fffe0ff

def z594 : W := mkw 0xbffffff7ff7b8fba 0x4bffffff7ff7b8fb 0xffffffffffff8fff 0xfffffffffffff8ff

def z595 : W := mkw 0x0008080206010420 0x0000808020601042 0x001818060e000004 0x0001818060e00000

def z596 : W := mkw 0x00828040a830819a 0x000828040a830819 0xc18780c1e0318ff9 0xec18780c1e0318ff

def z597 : W := mkw 0x527e233f9497fafc 0x1527e233f9497faf 0xc67e673f903ffffb 0xfc67e673f903ffff

def z598 : W := mkw 0x585a792e96d7fefc 0x1585a792e96d7fef 0x7878783e1ffffff7 0xf7878783e1ffffff

def z599 : W := mkw 0x3f7d7ebf56c15c60 0x53f7d7ebf56c15c6 0x7e787f3e1fc1fc77 0xf7e787f3e1fc1fc7

def z600 : W := mkw 0x3f755ef7e20005ba 0x43f755ef7e20005b 0xffffffffe0000fff 0xdffffffffe0000ff

def z601 : W := mkw 0x3f75702c11cc7840 0x33f75702c11cc784 0x3e60603811ce7002 0x13e60603811ce700

def z602 : W := mkw 0x3d595ca646c14420 0x53d595ca646c1442 0x399998c66fc00004 0x0399998c66fc0000

def z603 : W := mkw 0x022600008014a098 0x0022600008014a09 0xc6660001903ffffb 0xec6660001903ffff

def z604 : W := mkw 0x008aa80a1ffdfc60 0x3008aa80a1ffdfc6 0x000000001ffffc70 0x2000000001ffffc7

def z605 : W := mkw 0xbdd9fdc01feb4f00 0x2bdd9fdc01feb4f0 0xbf99ffc01ffe0f8f 0x7bf99ffc01ffe0f8

def z606 : W := mkw 0x000a8002a41180ba 0x0000a8002a41180b 0x0000000000018070 0x0000000000001807

def z607 : W := mkw 0x42aea3199dbffadc 0x242aea3199dbffad 0xc66667399ffffffb 0xfc66667399ffffff

def z608 : W := mkw 0xbfffdcc00ffde500 0x2bfffdcc00ffde50 0x3fff98c01ffff00f 0xa3fff98c01ffff00

def z609 : W := mkw 0x67a7a319993ebadc 0x267a7a319993ebad 0xc7e7e739903ffffb 0xfc7e7e739903ffff

def z610 : W := mkw 0x88007dc2b2420fba 0x088007dc2b2420fb 0xc0007fc7e0000ff0 0x5c0007fc7e0000ff

def z611 : W := mkw 0x258a8842af3985ba 0x0258a8842af3985b 0xff9f98c7ffff8fff 0xeff9f98c7ffff8ff

def z612 : W := mkw 0x27a78040a93ca19a 0x227a78040a93ca19 0x878780c1e03e0388 0x0878780c1e03e038

def z613 : W := mkw 0xc2a62b599b7ebfdc 0x0c2a62b599b7ebfd 0xc66667399ffffffb 0xfc66667399ffffff

def z614 : W := mkw 0x400a290a96d7fefc 0x1400a290a96d7fef 0x000000001ffffff0 0x2000000001ffffff

def z615 : W := mkw 0x008aa942be338fba 0x0008aa942be338fb 0xc79fffc7fe3f8fff 0xfc79fffc7fe3f8ff

def z616 : W := mkw 0x0000080202000420 0x0000008020200042 0x4000180600000c70 0x44000180600000c7

def z617 : W := mkw 0x00828040a830819a 0x000828040a830819 0x0000000000300380 0x0000000000030038

def z618 : W := mkw 0x3f75502400000000 0x03f7550240000000 0x7ffff83e0000000f 0xd7ffff83e0000000

def z619 : W := mkw 0x77ff83118dbfe29c 0x277ff83118dbfe29 0xbfff87019ffff38f 0xabfff87019ffff38

def z620 : W := mkw 0xefa67fd19b7eaf9c 0x0efa67fd19b7eaf9 0xbf867fc19ffe0f8f 0x7bf867fc19ffe0f8

def z621 : W := mkw 0x4224231990021adc 0x04224231990021ad 0xc666673980000ffb 0xdc666673980000ff

def z622 : W := mkw 0xbffffdc2bfffefba 0x2bffffdc2bfffefb 0xffffffc7ffffffff 0xfffffffc7fffffff

def z623 : W := mkw 0x3ffddef76e210522 0x43ffddef76e21052 0xffffffffee00000f 0xdffffffffee00000

def z624 : W := mkw 0x422602198014b0dc 0x0422602198014b0d 0x46660039903ff07b 0xa46660039903ff07

def z625 : W := mkw 0x1858786eb6c15dfa 0x11858786eb6c15df 0xf87878ffffc1fff7 0xff87878ffffc1fff

def z626 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc06667398001fff0 0xdc06667398001fff

def z627 : W := mkw 0x1058000004814000 0x0105800000481400 0x381800000fc00004 0x0381800000fc0000

def z628 : W := mkw 0x422e2b1b9617befc 0x0422e2b1b9617bef 0xc67e7f3f9e3fffff 0xfc67e7f3f9e3ffff

def z629 : W := mkw 0x80002100114a0a00 0x080002100114a0a0 0x0000000011ce0000 0x00000000011ce000

def z630 : W := mkw 0x18dad866ae3185ba 0x018dad866ae3185b 0xf9fff8ffee318fff 0xff9fff8ffee318ff

def z631 : W := mkw 0x88007ff552420f00 0x488007ff552420f0 0xc0007fffe0000f80 0x5c0007fffe0000f8

def z632 : W := mkw 0xad007580114a0a00 0x0ad007580114a0a0 0xbe00670011fe0f8b 0x7be00670011fe0f8

def z633 : W := mkw 0xafa57fd15b6a0f00 0x4afa57fd15b6a0f0 0xbf87ffc1fffe0f8f 0x7bf87ffc1fffe0f8

def z634 : W := mkw 0x3d5054a400000000 0x03d5054a40000000 0xfff87ffe0000000f 0xdfff87ffe0000000

def z635 : W := mkw 0x0800702c10401840 0x10800702c1040184 0x0000603800000000 0x1000060380000000

def z636 : W := mkw 0x3fffd8260ffde420 0x33fffd8260ffde42 0x3fff98061ffff00f 0xa3fff98061ffff00

def z637 : W := mkw 0x7f7577bdd0021adc 0x47f7577bdd0021ad 0xffffffffe0000fff 0xdffffffffe0000ff

def z638 : W := mkw 0x0000200810001840 0x0000020081000184 0x0060603810007002 0x1006060381000700

def z639 : W := mkw 0x1058082e06815460 0x11058082e0681546 0x4078183e0e01fc75 0xe4078183e0e01fc7

def z640 : W := mkw 0x3fffd0240dbde000 0x23fffd0240dbde00 0x7ffff83e1ffff00f 0xf7ffff83e1ffff00

def z641 : W := mkw 0x0800786eb2401dfa 0x10800786eb2401df 0xc00078ffe0000ff0 0x5c00078ffe0000ff

def z642 : W := mkw 0x3d597cae56c15c60 0x53d597cae56c15c6 0x79f9f8fe7fc1fc77 0xf79f9f8fe7fc1fc7

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018180600000005 0xc401818060000000

def z644 : W := mkw 0x3551000001884000 0x2355100000188400 0x3800000001c00000 0x03800000001c0000

def z645 : W := mkw 0x67272799d016badc 0x467272799d016bad 0xc7e7e7f9f03ffffb 0xfc7e7e7f9f03ffff

def z646 : W := mkw 0x00000040a000019a 0x000000040a000019 0x800000c1e0000380 0x0800000c1e000038

def z647 : W := mkw 0x0000210010020a00 0x00000210010020a0 0x06006700100e0002 0x106006700100e000

def z648 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7818783e0fc00c74 0x57818783e0fc00c7

def z649 : W := mkw 0x27a786d1e830819a 0x427a786d1e830819 0x878787c1e0300388 0x0878787c1e030038

def z650 : W := mkw 0x27af8842af3da5ba 0x227af8842af3da5b 0xc79f98c7ee3f8ffd 0xec79f98c7ee3f8ff

def z651 : W := mkw 0x480077bdd0021adc 0x4480077bdd0021ad 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z652 : W := mkw 0x1850702c10c05840 0x11850702c10c0584 0x7860603811c1fc73 0xf7860603811c1fc7

def z653 : W := mkw 0x0008000a04815060 0x10008000a0481506 0x000000000001f070 0x0000000000001f07

def z654 : W := mkw 0x37ff8842ae3185ba 0x037ff8842ae3185b 0xffff98c7ee318fff 0xeffff98c7ee318ff

def z655 : W := mkw 0x37ffa1001dbfea00 0x237ffa1001dbfea0 0xbfffe7001fffff8f 0xfbfffe7001fffff8

def z656 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x019f80000e318ffd 0xa019f80000e318ff

def z657 : W := mkw 0x0008080206010420 0x0000808020601042 0x000000000e018c70 0x2000000000e018c7

def z658 : W := mkw 0x1850502400000000 0x0185050240000000 0xf9fff8ffe000000f 0xdf9fff8ffe000000

def z659 : W := mkw 0x400221089016badc 0x0400221089016bad 0xc0060001903ffff9 0xec0060001903ffff

def z660 : W := mkw 0xad805cc00b680500 0x0ad805cc00b68050 0xb98018c00ff00f8d 0x6b98018c00ff00f8

def z661 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0x87807fc0003e0f88 0x587807fc0003e0f8

def z662 : W := mkw 0x3dd8782e1fe95c60 0x13dd8782e1fe95c6 0x7ff8783e1ffffc7f 0xf7ff8783e1ffffc7

def z663 : W := mkw 0x37ff80000c318000 0x037ff80000c31800 0x3fff80000e31800f 0xa3fff80000e31800

def z664 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbfe07ff80000000f 0x5bfe07ff80000000

def z665 : W := mkw 0x0800580002400400 0x0080058000240040 0x380018000fc00004 0x0380018000fc0000

def z666 : W := mkw 0x18daf82e1ef1dc60 0x118daf82e1ef1dc6 0x79fff83e1ff1fc7f 0xf79fff83e1ff1fc7

def z667 : W := mkw 0x7ffffffffe37bffe 0x47ffffffffe37bff 0xfffffffffe3fffff 0xffffffffffe3ffff

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00018c7e0000000 0x4c00018c7e000000

def z669 : W := mkw 0x2500000001080000 0x0250000000108000 0x3e00000011ce0002 0x03e00000011ce000

def z670 : W := mkw 0xbff57dc01bee6f00 0x2bff57dc01bee6f0 0xbfe07fc01ffe7f8f 0x7bfe07fc01ffe7f8

def z671 : W := mkw 0x3f7556b5418c6000 0x63f7556b5418c600 0x3e60673811ce7002 0x13e60673811ce700

def z672 : W := mkw 0x27a78691493ca000 0x627a78691493ca00 0x878787c1e03e0008 0x0878787c1e03e000

def z673 : W := mkw 0x3d5156b540000000 0x43d5156b54000000 0xf999ffffe0000004 0x5f999ffffe000000

def z674 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbfe7e7f9e000000a 0x1bfe7e7f9e000000

def z675 : W := mkw 0x3ffff8001ffdec00 0x23ffff8001ffdec0 0x3ffff8001ffffc0f 0xf3ffff8001ffffc0

def z676 : W := mkw 0x3ffff86ebffdfdfa 0x33ffff86ebffdfdf 0xfffff8ffffffffff 0xffffff8fffffffff

def z677 : W := mkw 0x008a88020e318420 0x0008a88020e31842 0x419f98060e318c7d 0xe419f98060e318c7

def z678 : W := mkw 0x0800780012400c00 0x00800780012400c0 0x0000780000000c00 0x50000780000000c0

def z679 : W := mkw 0xa58a8dc2af3b87ba 0x0a58a8dc2af3b87b 0xc79f9fc7ee3f8ffd 0xec79f9fc7ee3f8ff

def z680 : W := mkw 0x008a80000c318000 0x0008a80000c31800 0x000000000e318000 0x2000000000e31800

def z681 : W := mkw 0xefaeffdbbf7fbffe 0x0efaeffdbbf7fbff 0xffffffffffffffff 0xffffffffffffffff

def z682 : W := mkw 0x408aa94abe37bffe 0x0408aa94abe37bff 0xc19f98c7fe3ffffd 0xec19f98c7fe3ffff

def z683 : W := mkw 0x0000084222000522 0x0000008422200052 0x000018c660000000 0x0000018c66000000

def z684 : W := mkw 0x88007dc012420f00 0x088007dc012420f0 0xb8007fc01fc00f87 0x7b8007fc01fc00f8

def z685 : W := mkw 0x10da886eaeb1d5fa 0x110da886eaeb1d5f 0xc1ff98ffee31fffd 0xec1ff98ffee31fff

def z686 : W := mkw 0x67270791c016a29c 0x467270791c016a29 0x878787c1e03e0388 0x0878787c1e03e038

def z687 : W := mkw 0x400003118002029c 0x0400003118002029 0x8000070180000380 0x0800007018000038

def z688 : W := mkw 0x422e2b1b96d7fefc 0x1422e2b1b96d7fef 0xc66667399ffffffb 0xfc66667399ffffff

def z689 : W := mkw 0x3f7576bd50001840 0x43f7576bd5000184 0xfffffffff001fc7f 0xffffffffff001fc7

def z690 : W := mkw 0x18587ebf56c15c60 0x518587ebf56c15c6 0xf8787fffffc1fc77 0xff8787fffffc1fc7

def z691 : W := mkw 0x02ae80000dbde000 0x202ae80000dbde00 0x066600001ffff00b 0xa066600001ffff00

def z692 : W := mkw 0x0008000004010000 0x0000800000401000 0x001800000e018005 0xa001800000e01800

def z693 : W := mkw 0x2725069140000000 0x4272506914000000 0xc7e7e7f9e000000b 0xdc7e7e7f9e000000

def z694 : W := mkw 0x080054a440000000 0x4080054a44000000 0x000018c660000000 0x0000018c66000000

def z695 : W := mkw 0x37ff88020fbde420 0x237ff88020fbde42 0x7fff98061ffffc7f 0xe7fff98061ffffc7

def z696 : W := mkw 0x1858702e14c15860 0x11858702e14c1586 0x7878603e11c1f072 0x97878603e11c1f07

def z697 : W := mkw 0x27af8ed3ee3185ba 0x427af8ed3ee3185b 0xc79f9fc7ee318ffd 0xec79f9fc7ee318ff

def z698 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x39ff80000fc1f004 0x839ff80000fc1f00

def z699 : W := mkw 0x2f24569100000000 0x02f2456910000000 0xffe67ff98000000f 0xdffe67ff98000000

def z700 : W := mkw 0x3f7d5eb746010420 0x43f7d5eb74601042 0xffffffffee018c7f 0xfffffffffee018c7

def z701 : W := mkw 0x527e23199497fadc 0x0527e23199497fad 0xfe7e67399fffffff 0xffe7e67399ffffff

def z702 : W := mkw 0xad887dc21f6b0f20 0x0ad887dc21f6b0f2 0xff987fc61fff8fff 0xfff987fc61fff8ff

def z703 : W := mkw 0x000a800004118000 0x0000a80000411800 0x001f800000018000 0x8001f80000001800

def z704 : W := mkw 0x777723199016badc 0x0777723199016bad 0xffffe739903fffff 0xfffffe739903ffff

def z705 : W := mkw 0x0808780a16c15c60 0x10808780a16c15c6 0x380078001fc1fc77 0x7380078001fc1fc7

def z706 : W := mkw 0x5a7e7a3f96d5fcfc 0x15a7e7a3f96d5fcf 0x787e783f9fc1fc77 0xf787e783f9fc1fc7

def z707 : W := mkw 0x7d5375acd016badc 0x47d5375acd016bad 0x399998c6703ffff4 0x2399998c6703ffff

def z708 : W := mkw 0x1858780816c15c40 0x01858780816c15c4 0x787878381fc1fc77 0xf787878381fc1fc7

def z709 : W := mkw 0x37ff80400dbde100 0x237ff80400dbde10 0xbfff80c01ffff38f 0xabfff80c01ffff38

def z710 : W := mkw 0xc8007fdbb2421ffe 0x0c8007fdbb2421ff 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z711 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc19f98c7ee300ffc 0x4c19f98c7ee300ff

def z712 : W := mkw 0x88007dca12421f60 0x188007dca12421f6 0x80007fc000000ff0 0x580007fc000000ff

def z713 : W := mkw 0x75d9a3199dab5adc 0x275d9a3199dab5ad 0xf999e7398fc00ff4 0x5f999e7398fc00ff

def z714 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7878183e1fc1fc74 0xa7878183e1fc1fc7

def z715 : W := mkw 0xff7577bd514e3a44 0x4ff7577bd514e3a4 0x3e60673811ce7002 0x13e60673811ce700

def z716 : W := mkw 0x2725069140000000 0x4272506914000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z717 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xff867fc19ffe0f8f 0xfff867fc19ffe0f8

def z718 : W := mkw 0x37ff82110dbde000 0x237ff82110dbde00 0xfffffffffffff00f 0xffffffffffffff00

def z719 : W := mkw 0x127f80000495e000 0x2127f80000495e00 0x3e7f80001ffff00f 0xa3e7f80001ffff00

def z720 : W := mkw 0x008a8842aeb5e5ba 0x2008a8842aeb5e5b 0xc19f98c7ee31fffd 0xec19f98c7ee31fff

def z721 : W := mkw 0x258a80000dbde000 0x2258a80000dbde00 0x3f9f80001ffff00f 0xa3f9f80001ffff00

def z722 : W := mkw 0x4224231910063a44 0x04224231910063a4 0xc6606738103ffffb 0xfc6606738103ffff

def z723 : W := mkw 0x272d2e9b56c15c60 0x5272d2e9b56c15c6 0x878787c1ffc1fc78 0x2878787c1ffc1fc7

def z724 : W := mkw 0xe7a787d1893ea39c 0x2e7a787d1893ea39 0x878787c1803e0388 0x0878787c1803e038

def z725 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf99ffc67ffe0f8f 0x7bf99ffc67ffe0f8

def z726 : W := mkw 0xad0af582b55b8aba 0x0ad0af582b55b8ab 0x7e1fe707f1cf8072 0x97e1fe707f1cf807

def z727 : W := mkw 0xad807de45b6a0f00 0x4ad807de45b6a0f0 0xbf807fc67ffe0f8f 0x7bf807fc67ffe0f8

def z728 : W := mkw 0x37750842a38c65ba 0x237750842a38c65b 0xfe6018c7f1ce7ff2 0x4fe6018c7f1ce7ff

def z729 : W := mkw 0x98587dae16c35e60 0x198587dae16c35e6 0x78787f3e1fc1fc77 0xf78787f3e1fc1fc7

def z730 : W := mkw 0xad807dee1b6a1f60 0x1ad807dee1b6a1f6 0xffe07ffe1fffffff 0xfffe07ffe1ffffff

def z731 : W := mkw 0xad8055c0092a0300 0x0ad8055c0092a030 0xbf807fc01ffe038f 0x7bf807fc01ffe038

def z732 : W := mkw 0xad007d80134a0e00 0x0ad007d80134a0e0 0xbe007f001ffe0f8f 0x7be007f001ffe0f8

def z733 : W := mkw 0x9858796e16c35f60 0x19858796e16c35f6 0x7878783e1fc1fff7 0xf7878783e1fc1fff

def z734 : W := mkw 0x0000021100000000 0x0000002110000000 0xc19fffffe000000d 0xdc19fffffe000000

def z735 : W := mkw 0x18d2f06cb8f0d9da 0x118d2f06cb8f0d9d 0xb9e7e0f9f1f0738a 0x1b9e7e0f9f1f0738

def z736 : W := mkw 0x1850782c12c05c40 0x11850782c12c05c4 0x786078381fc1fc77 0xf786078381fc1fc7

def z737 : W := mkw 0x3fffdef7ee3185ba 0x43fffdef7ee3185b 0x3e6067380e318ff2 0x33e6067380e318ff

def z738 : W := mkw 0x5a7e5b3786d7e6bc 0x15a7e5b3786d7e6b 0xbe1e1f078ffe038c 0x0be1e1f078ffe038

def z739 : W := mkw 0x008a80008c318098 0x0008a80008c31809 0xc19f98c7ee318ffd 0xec19f98c7ee318ff

def z740 : W := mkw 0x000a8842a61185ba 0x0000a8842a61185b 0xc19f98c7e0018ffd 0xcc19f98c7e0018ff

def z741 : W := mkw 0xefa65ed98b7cb5dc 0x0efa65ed98b7cb5d 0x79e618f98fc1f074 0x879e618f98fc1f07

def z742 : W := mkw 0xad805dc00b6a0700 0x0ad805dc00b6a070 0xbf801fc00ffe0f8d 0x6bf801fc00ffe0f8

def z743 : W := mkw 0x27ae80000dbde000 0x227ae80000dbde00 0x3fe600001ffff00f 0xa3fe600001ffff00

def z744 : W := mkw 0x008a8842ae35a5ba 0x0008a8842ae35a5b 0xc19f98c7fe3ffffd 0xec19f98c7fe3ffff

def z745 : W := mkw 0x377d0000058d6000 0x2377d0000058d600 0x3fff80001fcff00f 0xa3fff80001fcff00

def z746 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7878603e1fc1fc72 0xb7878603e1fc1fc7

def z747 : W := mkw 0xb5d805ee0dab5360 0x1b5d805ee0dab536 0xc7f807fe003ff3f8 0x8c7f807fe003ff3f

def z748 : W := mkw 0x022602118014a098 0x0022602118014a09 0xc6666739903ffffb 0xfc6666739903ffff

def z749 : W := mkw 0x2f24569100000000 0x02f2456910000000 0xffffffffe000000f 0xdffffffffe000000

def z750 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7878783e1fc1f076 0x97878783e1fc1f07

def z751 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbe007fc01ffe0f82 0x7be007fc01ffe0f8

def z752 : W := mkw 0x37ff82118dbde098 0x237ff82118dbde09 0xffffe7399fffffff 0xfffffe7399ffffff

def z753 : W := mkw 0x88007dc012420f00 0x088007dc012420f0 0xbe007fc01ffe0f8f 0x7be007fc01ffe0f8

def z754 : W := mkw 0xc8007ffdd2421fdc 0x4c8007ffdd2421fd 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z755 : W := mkw 0x3f7556b541884000 0x63f7556b54188400 0xffffffffe1c0000f 0xdffffffffe1c0000

def z756 : W := mkw 0xa58025c0192a0b00 0x0a58025c0192a0b0 0xbf8067c01ffe0f8f 0x7bf8067c01ffe0f8

def z757 : W := mkw 0x37f7000009bce000 0x237f7000009bce00 0x3fe600001ffff00f 0xa3fe600001ffff00

def z758 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc1ff98c7fe31ffff 0xec1ff98c7fe31fff

def z759 : W := mkw 0xe7a687d1a93ea39e 0x0e7a687d1a93ea39 0x878787c1e03e0388 0x0878787c1e03e038

def z760 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbe0067001ffe0f8b 0x7be0067001ffe0f8

def z761 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3fe780001ffff00a 0x23fe780001ffff00

def z762 : W := mkw 0x1859f82e16c15c60 0x31859f82e16c15c6 0x7879f83e1fc1fc77 0xf7879f83e1fc1fc7

def z763 : W := mkw 0x3f7556b541080000 0x43f7556b54108000 0xfffffffff1ce000f 0xdfffffffff1ce000

def z764 : W := mkw 0x1058282e16c15c60 0x11058282e16c15c6 0x7878003e1fc1fc77 0xa7878003e1fc1fc7

def z765 : W := mkw 0x0808780a16c15c60 0x10808780a16c15c6 0x786078381fc1fc77 0xf786078381fc1fc7

def z766 : W := mkw 0x2fa7f82e1b7cbc60 0x32fa7f82e1b7cbc6 0x4787f83e003e0c78 0x54787f83e003e0c7

def z767 : W := mkw 0xad807dec1b6a1f40 0x1ad807dec1b6a1f4 0xbf807ff81ffe0f8f 0x7bf807ff81ffe0f8

def z768 : W := mkw 0x35d980000dad6000 0x235d980000dad600 0x399980001fce7004 0x0399980001fce700

def z769 : W := mkw 0x35db80000dbde000 0x235db80000dbde00 0x380000001ffff000 0x2380000001ffff00

def z770 : W := mkw 0xbdd95ce64fe94520 0x5bdd95ce64fe9452 0x399998c66fc00004 0x0399998c66fc0000

def z771 : W := mkw 0x98587cee16c15d60 0x198587cee16c15d6 0x787878fe1fc1fc77 0xf787878fe1fc1fc7

def z772 : W := mkw 0x37ff8040adbde19a 0x237ff8040adbde19 0xffff80c1ffffffff 0xeffff80c1fffffff

def z773 : W := mkw 0x9a7ffdc016d7ef00 0x29a7ffdc016d7ef0 0x807fffc00001ff80 0xd807fffc00001ff8

def z774 : W := mkw 0x25820000093ca000 0x025820000093ca00 0x3f8000001ffff00f 0x23f8000001ffff00

def z775 : W := mkw 0x92f52b755b6a0f00 0x492f52b755b6a0f0 0x407f803ffffe0f80 0xa407f803ffffe0f8

def z776 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0xf878783e1ff1ffff 0xff878783e1ff1fff

def z777 : W := mkw 0x008a8842af3da5ba 0x2008a8842af3da5b 0xc19f98c7ee3f8ffd 0xec19f98c7ee3f8ff

def z778 : W := mkw 0x088ad6b54dbde000 0x6088ad6b54dbde00 0xc0007ffffffff000 0x7c0007ffffffff00

def z779 : W := mkw 0x37fd00000dad6000 0x237fd00000dad600 0x3ff800001ffff00f 0xa3ff800001ffff00

def z780 : W := mkw 0x88007dec12421f40 0x188007dec12421f4 0x80007ff800000f80 0x580007ff800000f8

def z781 : W := mkw 0x37ff80260dbde020 0x337ff80260dbde02 0x3fff80061ffff00f 0xa3fff80061ffff00

def z782 : W := mkw 0x105a00000495e000 0x0105a00000495e00 0x387800001ffff007 0xa387800001ffff00

def z783 : W := mkw 0xad807dc81b6a1f40 0x0ad807dc81b6a1f4 0xff807ff81ffe0fff 0x7ff807ff81ffe0ff

def z784 : W := mkw 0x37ff82110dbde000 0x237ff82110dbde00 0xbfff87019ffff00f 0xabfff87019ffff00

def z785 : W := mkw 0x0800792e12421e60 0x10800792e12421e6 0xc0007f3e00000ff0 0x5c0007f3e00000ff

def z786 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0xf87878ffffc1fc77 0xff87878ffffc1fc7

def z787 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xc7ffffffe0000008 0xdc7ffffffe000000

def z788 : W := mkw 0x1858792e16c35e60 0x11858792e16c35e6 0xf8787f3e1fc1fff7 0xff8787f3e1fc1fff

def z789 : W := mkw 0x37ff80008dbde098 0x237ff80008dbde09 0xbfff80019ffff38f 0xabfff80019ffff38

def z790 : W := mkw 0x422623199016badc 0x0422623199016bad 0x46666739903ffff2 0xb46666739903ffff

def z791 : W := mkw 0x408aa94abef7fffe 0x1408aa94abef7fff 0x000000001ffffff0 0x2000000001ffffff

def z792 : W := mkw 0x1858702e14c15860 0x11858702e14c1586 0x7878603e1fc1f077 0xb7878603e1fc1f07

def z793 : W := mkw 0xbdd9dce60fe94520 0x3bdd9dce60fe9452 0x399998c60fc00004 0x0399998c60fc0000

def z794 : W := mkw 0x42acab5b3e273f66 0x042acab5b3e273f6 0x07f9fffe7e0e7006 0x107f9fffe7e0e700

def z795 : W := mkw 0x258800000da94000 0x0258800000da9400 0x3f8000001ffff00f 0x23f8000001ffff00

def z796 : W := mkw 0x12fe80000dbde000 0x212fe80000dbde00 0x3e7e00001ffff00f 0xa3e7e00001ffff00

def z797 : W := mkw 0x4a267b119256ae9c 0x04a267b119256ae9 0xbe067f019ffe0f8f 0x7be067f019ffe0f8

def z798 : W := mkw 0x1058202e14815860 0x11058202e1481586 0x7878603e1fc1fc77 0xf7878603e1fc1fc7

def z799 : W := mkw 0x37ff8000adbde09a 0x237ff8000adbde09 0x3fff8001fffff00f 0xa3fff8001fffff00

def z800 : W := mkw 0x3f7556b540846000 0x63f7556b54084600 0xffffffffe000700f 0xdffffffffe000700

def z801 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc79fffc7ee318fff 0xfc79fffc7ee318ff

def z802 : W := mkw 0x35d0000009a84000 0x035d0000009a8400 0x3fe000001ffe700f 0x23fe000001ffe700

def z803 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3fff80001ffe700e 0x03fff80001ffe700

def z804 : W := mkw 0x185056b540000000 0x4185056b54000000 0xf9ffffffe000000f 0xdf9ffffffe000000

def z805 : W := mkw 0x77ff82118dbde09c 0x277ff82118dbde09 0x3fff80019ffff00f 0xa3fff80019ffff00

def z806 : W := mkw 0x258a80000dbde000 0x2258a80000dbde00 0x3e0000001ffff002 0x23e0000001ffff00

def z807 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfffffffff001f00f 0xffffffffff001f00

def z808 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3f9f80001ffff00c 0x23f9f80001ffff00

def z809 : W := mkw 0x1858582606814420 0x0185858260681442 0x7878783e1fc1fc77 0xf7878783e1fc1fc7

def z810 : W := mkw 0x37ff80008dbde098 0x237ff80008dbde09 0x3fff80001fffffff 0xa3fff80001ffffff

def z811 : W := mkw 0x527e02198495f0dc 0x0527e02198495f0d 0x407e00398001f070 0x8407e00398001f07

def z812 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffe0018c7f 0xfffffffffe0018c7

def z813 : W := mkw 0x1858582e06c15460 0x11858582e06c1546 0x7878183e1fc1f077 0xa7878183e1fc1f07

def z814 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbfffffffe000000e 0x1bfffffffe000000

def z815 : W := mkw 0x1058082e06815460 0x11058082e0681546 0x7878183e1fc1fc77 0xe7878183e1fc1fc7

def z816 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x786060381fc1fc73 0xf786060381fc1fc7

def z817 : W := mkw 0x37fd80000dad6000 0x237fd80000dad600 0x3ff980001ffe700f 0x23ff980001ffe700

def z818 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3fe000001ffff00f 0x23fe000001ffff00

def z819 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc67fe73ff03ffffb 0xfc67fe73ff03ffff

def z820 : W := mkw 0x088079401a620f00 0x0088079401a620f0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z821 : W := mkw 0xa5802dc01b6a0f00 0x0a5802dc01b6a0f0 0xbf8007c01ffe0f8f 0x2bf8007c01ffe0f8

def z822 : W := mkw 0x4227a3199016badc 0x24227a3199016bad 0xc667e739903ffffb 0xfc667e739903ffff

def z823 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0xbfffe7001ffff00f 0xfbfffe7001ffff00

def z824 : W := mkw 0xad807dca1b6a1f60 0x1ad807dca1b6a1f6 0xbf807fc01ffe0fff 0x7bf807fc01ffe0ff

def z825 : W := mkw 0x25800100092a0200 0x025800100092a020 0xbf8007001ffe038f 0x2bf8007001ffe038

def z826 : W := mkw 0x00020842a21085ba 0x000020842a21085b 0xc19f98c7e0318ffd 0xec19f98c7e0318ff

def z827 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc6667ffff03ffffb 0xfc6667ffff03ffff

def z828 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0xf87e783f9fc1fc7f 0xff87e783f9fc1fc7

def z829 : W := mkw 0xbdd8dce62fe94522 0x1bdd8dce62fe9452 0x399998c66fc00004 0x0399998c66fc0000

def z830 : W := mkw 0x67a78351a93ea39e 0x267a78351a93ea39 0x878787c1e03e0388 0x0878787c1e03e038

def z831 : W := mkw 0x37ff86d1edbde19a 0x637ff86d1edbde19 0xbfff87c1fffff38f 0xabfff87c1fffff38

def z832 : W := mkw 0x00828040a830819a 0x000828040a830819 0xc19f98c7e0318ffd 0xec19f98c7e0318ff

def z833 : W := mkw 0x48007b1992421edc 0x048007b1992421ed 0xc0007f3980000ff0 0x5c0007f3980000ff

def z834 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0xf9f878fe1fc1fc7f 0xff9f878fe1fc1fc7

def z835 : W := mkw 0x377d0000058d6000 0x2377d0000058d600 0x3e6000001fcff002 0x23e6000001fcff00

def z836 : W := mkw 0x0000200810001840 0x0000020081000184 0x786060381fc1fc77 0xf786060381fc1fc7

def z837 : W := mkw 0x1058002e04815060 0x11058002e0481506 0x7878003e0fc1f074 0x87878003e0fc1f07

def z838 : W := mkw 0x2d007d8012420e00 0x02d007d8012420e0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z839 : W := mkw 0x4226a319b016bade 0x04226a319b016bad 0xc667e739f03ffffb 0xfc667e739f03ffff

def z840 : W := mkw 0x10da80000dbde000 0x210da80000dbde00 0x386000001ffff002 0x2386000001ffff00

def z841 : W := mkw 0x37ff8002adbde0ba 0x237ff8002adbde0b 0x3fff80001ffff07f 0xa3fff80001ffff07

def z842 : W := mkw 0x37ff80008dbde098 0x237ff80008dbde09 0xffff98c7ffffffff 0xeffff98c7fffffff

def z843 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf8067c01ffe0f8a 0x3bf8067c01ffe0f8

def z844 : W := mkw 0x00888842ae2105ba 0x000888842ae2105b 0xc19f98c7ee000ffd 0xcc19f98c7ee000ff

def z845 : W := mkw 0x0a2456b540000000 0x40a2456b54000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z846 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3ff980001ffff006 0x23ff980001ffff00

def z847 : W := mkw 0x7f7577bd518e7a44 0x67f7577bd518e7a4 0x3e60673811ce7002 0x13e60673811ce700

def z848 : W := mkw 0xa58005c0092a0300 0x0a58005c0092a030 0xbf8007c00ffe038c 0x0bf8007c00ffe038

def z849 : W := mkw 0x3dd9dce66fa94522 0x63dd9dce66fa9452 0x399998c66fc00004 0x0399998c66fc0000

def z850 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf87ffc1fffe0f8f 0x7bf87ffc1fffe0f8

def z851 : W := mkw 0x3d5156b540000000 0x43d5156b54000000 0xf99fffffe000000d 0xdf99fffffe000000

def z852 : W := mkw 0x35da80000db9c000 0x035da80000db9c00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z853 : W := mkw 0x48007b3f12421e64 0x148007b3f12421e6 0x40007f3e00000c70 0x540007f3e00000c7

def z854 : W := mkw 0xbf7577bd51ca5a40 0x5bf7577bd51ca5a4 0x3e60673811ce7002 0x13e60673811ce700

def z855 : W := mkw 0x37f5000009ac6000 0x237f5000009ac600 0x3fff80001ffe700f 0xa3fff80001ffe700

def z856 : W := mkw 0x42272319d016badc 0x442272319d016bad 0xc667e739f03ffffb 0xfc667e739f03ffff

def z857 : W := mkw 0xa58025c8192a1b40 0x0a58025c8192a1b4 0xc7e067f8103ffffb 0xfc7e067f8103ffff

def z858 : W := mkw 0x37ff8040adbde19a 0x237ff8040adbde19 0x3fff80001ffff38f 0xa3fff80001ffff38

def z859 : W := mkw 0x527f821ba495f0fe 0x2527f821ba495f0f 0x407f803fe001f070 0x8407f803fe001f07

def z860 : W := mkw 0x888079401b6a0f00 0x0888079401b6a0f0 0xbe007f001ffe0f8f 0x7be007f001ffe0f8

def z861 : W := mkw 0x37ff8002adbde0ba 0x237ff8002adbde0b 0xffff98c7fffff07f 0xeffff98c7fffff07

def z862 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3e6600001ffff00b 0xa3e6600001ffff00

def z863 : W := mkw 0x48007fbfd2421efc 0x548007fbfd2421ef 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z864 : W := mkw 0x67a60311893ea29c 0x067a60311893ea29 0x87860701803e0388 0x087860701803e038

def z865 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x387860381fc1fc77 0xb387860381fc1fc7

def z866 : W := mkw 0x2d8079001b6a0e00 0x02d8079001b6a0e0 0xbf807f001ffe0f8f 0x7bf807f001ffe0f8

def z867 : W := mkw 0x67a78211893ca09c 0x267a78211893ca09 0x07878001803e0008 0x007878001803e000

def z868 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xff807fc7fffe0f8f 0x7ff807fc7fffe0f8

def z869 : W := mkw 0x37ff80008dbde098 0x237ff80008dbde09 0x7fff80019ffff07f 0xa7fff80019ffff07

def z870 : W := mkw 0xad807de41b6a0f00 0x0ad807de41b6a0f0 0xff807ffe1ffe0f8f 0x7ff807ffe1ffe0f8

def z871 : W := mkw 0x67a78791c93ea29c 0x667a78791c93ea29 0x878787c1e03e0388 0x0878787c1e03e038

def z872 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x7fff80001ffffc7f 0xe7fff80001ffffc7

def z873 : W := mkw 0x008a80000dbde000 0x2008a80000dbde00 0x380000001ffff007 0x2380000001ffff00

def z874 : W := mkw 0x1a7556b540000000 0x41a7556b54000000 0xc1ffffffe000000d 0xdc1ffffffe000000

def z875 : W := mkw 0x27af80000dbde000 0x227af80000dbde00 0x3f8780001ffff00f 0x23f8780001ffff00

def z876 : W := mkw 0x377d0000058d6000 0x2377d0000058d600 0x3e7800001fce7006 0x03e7800001fce700

def z877 : W := mkw 0x37ff8042adbde1ba 0x237ff8042adbde1b 0xffff80c7fffff3ff 0xaffff80c7fffff3f

def z878 : W := mkw 0x1058212e14835a60 0x11058212e14835a6 0xc678673e103ffffb 0xfc678673e103ffff

def z879 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x79f9f8fe7fc1fc77 0xf79f9f8fe7fc1fc7

def z880 : W := mkw 0x37ff8040adbde19a 0x237ff8040adbde19 0xffff98c7fffff38f 0xeffff98c7fffff38

def z881 : W := mkw 0x4a267a199254bcdc 0x04a267a199254bcd 0x786678399fc1fc77 0xf786678399fc1fc7

def z882 : W := mkw 0x37ff86b54dbde000 0x637ff86b54dbde00 0xffff87fffffff00f 0xaffff87fffffff00

def z883 : W := mkw 0x37f7800009bce000 0x237f7800009bce00 0x3fe780001ffe700f 0x23fe780001ffe700

def z884 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3e7f80001ffff002 0xa3e7f80001ffff00

def z885 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf801fc01ffe0f8c 0x2bf801fc01ffe0f8

def z886 : W := mkw 0x3f7556b540804000 0x43f7556b54080400 0xfffffffff1c0700f 0xdfffffffff1c0700

def z887 : W := mkw 0x37ff82354dbde000 0x637ff82354dbde00 0x3fff80381ffff00f 0xa3fff80381ffff00

def z888 : W := mkw 0x4000231990021adc 0x04000231990021ad 0xc6606739903ffffb 0xfc6606739903ffff

def z889 : W := mkw 0x527f823dc495f0dc 0x6527f823dc495f0d 0x407f803fe001f070 0x8407f803fe001f07

def z890 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7e78783e1ffffc7f 0xf7e78783e1ffffc7

def z891 : W := mkw 0x808a8842af7985ba 0x0808a8842af7985b 0xc19f98c7eff18ffd 0xec19f98c7eff18ff

def z892 : W := mkw 0x0224231910021a40 0x00224231910021a4 0xc6666739903ffffb 0xfc6666739903ffff

def z893 : W := mkw 0x422623199016badc 0x0422623199016bad 0x46606738103ffff3 0xf46606738103ffff

def z894 : W := mkw 0x27a40000092c2000 0x027a40000092c200 0x3fe000001ffe700f 0x23fe000001ffe700

def z895 : W := mkw 0x37ff84804dbde000 0x637ff84804dbde00 0x3fff80c07ffff00f 0xa3fff80c07ffff00

def z896 : W := mkw 0x12ff80000dbde000 0x212ff80000dbde00 0x387f80001ffff007 0xa387f80001ffff00

def z897 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0xbfff80001fffff8f 0xebfff80001fffff8

def z898 : W := mkw 0x1858792e16c35e60 0x11858792e16c35e6 0x7e787f3e1fcffc77 0xf7e787f3e1fcffc7

def z899 : W := mkw 0x35d980000da94000 0x235d980000da9400 0x3ff980001ffff00f 0xa3ff980001ffff00

def z900 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc67e7f3f903fffff 0xfc67e7f3f903ffff

def z901 : W := mkw 0xad807de61b6a0f20 0x1ad807de61b6a0f2 0xbf807fc61ffe0f8f 0x7bf807fc61ffe0f8

def z902 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc79f98c7fe3f8fff 0xec79f98c7fe3f8ff

def z903 : W := mkw 0xad805dc00b6a0700 0x0ad805dc00b6a070 0xbf801fc01ffe038f 0x2bf801fc01ffe038

def z904 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf807fc00ffe0f8c 0x5bf807fc00ffe0f8

def z905 : W := mkw 0x1058280a16c15c60 0x11058280a16c15c6 0x787860381fc1fc77 0xf787860381fc1fc7

def z906 : W := mkw 0x37ff82354dbde000 0x637ff82354dbde00 0xffff98fffffff00f 0xeffff98fffffff00

def z907 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffffc0000f 0xfffffffffffc0000

def z908 : W := mkw 0xbf7556b541480000 0x4bf7556b54148000 0xffffffffe1c0000f 0xdffffffffe1c0000

def z909 : W := mkw 0x1058280a16815c60 0x01058280a16815c6 0x7878783e1fc1fc77 0xf7878783e1fc1fc7

def z910 : W := mkw 0x2d0056b540000000 0x42d0056b54000000 0xff9fffffe000000f 0xdff9fffffe000000

def z911 : W := mkw 0x48007b7fb2421ffe 0x148007b7fb2421ff 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z912 : W := mkw 0x37ff80240dbde000 0x237ff80240dbde00 0x7fff803e1ffff00f 0xa7fff803e1ffff00

def z913 : W := mkw 0x2580000009280000 0x0258000000928000 0x3fe000001ffff00f 0xa3fe000001ffff00

def z914 : W := mkw 0x1858f82e36c15c62 0x11858f82e36c15c6 0x7879f83e7fc1fc77 0xf7879f83e7fc1fc7

def z915 : W := mkw 0x422623199016badc 0x0422623199016bad 0xfe6667399fffffff 0xffe6667399ffffff

def z916 : W := mkw 0x37fd80000dad6000 0x237fd80000dad600 0x3e6000001fce7002 0x03e6000001fce700

def z917 : W := mkw 0x258a80000dbde000 0x2258a80000dbde00 0x398000001ffff004 0x2398000001ffff00

def z918 : W := mkw 0x3f7556b540042000 0x43f7556b54004200 0xfffffffff00e700f 0xdfffffffff00e700

def z919 : W := mkw 0x10da80000dbde000 0x210da80000dbde00 0x39ff80001ffff00f 0xa39ff80001ffff00

def z920 : W := mkw 0x37ff86914dbde000 0x637ff86914dbde00 0x3fff87001ffff00f 0xa3fff87001ffff00

def z921 : W := mkw 0x3558000005894000 0x0355800000589400 0x3e7800001fcff007 0xa3e7800001fcff00

def z922 : W := mkw 0x0002210890129ad8 0x00002210890129ad 0xc6666739903ffffb 0xfc6666739903ffff

def z923 : W := mkw 0xad805dc00b6a0700 0x0ad805dc00b6a070 0xbf807fc00ffe038f 0x5bf807fc00ffe038

def z924 : W := mkw 0xc8007fff92421ffc 0x1c8007fff92421ff 0xc0007fff80000ff0 0x5c0007fff80000ff

def z925 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7860783e1fc1fc72 0x77860783e1fc1fc7

def z926 : W := mkw 0xa5800dc00b2a0700 0x0a5800dc00b2a070 0xbf801fc01ffe0f8f 0x6bf801fc01ffe0f8

def z927 : W := mkw 0x7f7577bd50021a44 0x47f7577bd50021a4 0x3e60673800000002 0x13e6067380000000

def z928 : W := mkw 0x1058000004814000 0x0105800000481400 0x3e7800001ffff00f 0xa3e7800001ffff00

def z929 : W := mkw 0x400221089016badc 0x0400221089016bad 0xc6606738103ffffb 0xfc6606738103ffff

def z930 : W := mkw 0x37ff86914dbde000 0x637ff86914dbde00 0xffffe7f9fffff00f 0xfffffe7f9fffff00

def z931 : W := mkw 0x10580000058d6000 0x210580000058d600 0x387800001fcff007 0xa387800001fcff00

def z932 : W := mkw 0x008208408a308598 0x0008208408a30859 0xc19f98c7ee318ffd 0xec19f98c7ee318ff

def z933 : W := mkw 0x37f5000009ac6000 0x237f5000009ac600 0x3e6000001ffe7002 0x23e6000001ffe700

def z934 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3e7800001ffff007 0xa3e7800001ffff00

def z935 : W := mkw 0xad807dc81b6a1f40 0x0ad807dc81b6a1f4 0xbf807fc01fffffff 0x7bf807fc01ffffff

def z936 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x7878783e0fc1fc74 0xd7878783e0fc1fc7

def z937 : W := mkw 0x37ff82110dbde000 0x237ff82110dbde00 0x7fff80399ffff00f 0xa7fff80399ffff00

def z938 : W := mkw 0xad817dc05b6a0f00 0x4ad817dc05b6a0f0 0xbf81ffc07ffe0f8f 0x7bf81ffc07ffe0f8

def z939 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x386078381fc1fc77 0x7386078381fc1fc7

def z940 : W := mkw 0x27ae80000d3da000 0x027ae80000d3da00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z941 : W := mkw 0x008a8842aeb1c5ba 0x0008a8842aeb1c5b 0xc19f98c7fff1fffd 0xec19f98c7fff1fff

def z942 : W := mkw 0x37ff86914dbde000 0x637ff86914dbde00 0xffff9fc7fffff00f 0xeffff9fc7fffff00

def z943 : W := mkw 0x408aa94abfbffffe 0x2408aa94abfbffff 0x000000001ffffff0 0x2000000001ffffff

def z944 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc7ffe739903fffff 0xfc7ffe739903ffff

def z945 : W := mkw 0x1858502e04815060 0x11858502e0481506 0x7878783e1fc1f077 0xf7878783e1fc1f07

def z946 : W := mkw 0x35db80000dbde000 0x235db80000dbde00 0x399f80001ffff00d 0xa399f80001ffff00

def z947 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc7e67ff9903fffff 0xfc7e67ff9903ffff

def z948 : W := mkw 0x127f8237e495e0ba 0x6127f8237e495e0b 0x407f803fe001f070 0x8407f803fe001f07

def z949 : W := mkw 0x37750000018c6000 0x237750000018c600 0x3e6000001fce7007 0x23e6000001fce700

def z950 : W := mkw 0x37f70000093ca000 0x037f70000093ca00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z951 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0xffff80019ffff00f 0xeffff80019ffff00

def z952 : W := mkw 0x4800792e92421efc 0x14800792e92421ef 0x4000783e00000ff0 0x54000783e00000ff

def z953 : W := mkw 0xad807dc81b6a1f40 0x0ad807dc81b6a1f4 0xbfe07ff81ffe7f8f 0x7bfe07ff81ffe7f8

def z954 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc19f98c7ee018ff4 0xcc19f98c7ee018ff

def z955 : W := mkw 0xad81fdc01b6a0f00 0x2ad81fdc01b6a0f0 0xbf81ffc01ffe0f8f 0x7bf81ffc01ffe0f8

def z956 : W := mkw 0x27a786d1e93ca19a 0x627a786d1e93ca19 0x878787c1e03e0388 0x0878787c1e03e038

def z957 : W := mkw 0x422623199016badc 0x0422623199016bad 0x86666739903ffffa 0x386666739903ffff

def z958 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc7e7e7f9f03ffffb 0xfc7e7e7f9f03ffff

def z959 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x7fffe0381ffff00f 0xf7fffe0381ffff00

def z960 : W := mkw 0x1858792e16c35e60 0x11858792e16c35e6 0x7878783e1ffffff7 0xf7878783e1ffffff

def z961 : W := mkw 0x37f5000009ac6000 0x237f5000009ac600 0x3fe000001fce7006 0x03fe000001fce700

def z962 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf9fffc01ffe0f8f 0xfbf9fffc01ffe0f8

def z963 : W := mkw 0xad807580196a0a00 0x0ad807580196a0a0 0xbf8067001ffe0f8f 0x7bf8067001ffe0f8

def z964 : W := mkw 0x37fd00000da94000 0x037fd00000da9400 0x3fff80001ffff00f 0xa3fff80001ffff00

def z965 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x787ff83fffc1fc77 0xf787ff83fffc1fc7

def z966 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x7fff98061ffff00f 0xe7fff98061ffff00

def z967 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x3878783e1fc1fc76 0x33878783e1fc1fc7

def z968 : W := mkw 0x1a74523500000000 0x01a7452350000000 0xffffffffe000000f 0xdffffffffe000000

def z969 : W := mkw 0x7f7577bd50c67a44 0x57f7577bd50c67a4 0x3e60673811ce7002 0x13e60673811ce700

def z970 : W := mkw 0x35db80000dbde000 0x235db80000dbde00 0x39f980001ffff007 0xa39f980001ffff00

def z971 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xff807fc01fff8fff 0xfff807fc01fff8ff

def z972 : W := mkw 0x008a8842afb9c5ba 0x2008a8842afb9c5b 0xc19f98c7eff18ffd 0xec19f98c7eff18ff

def z973 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc19f98c7e0318ff8 0xcc19f98c7e0318ff

def z974 : W := mkw 0x808aa94abffbdffa 0x1808aa94abffbdff 0x000000001ffffff0 0x2000000001ffffff

def z975 : W := mkw 0x527f82118495e09c 0x2527f82118495e09 0x007f80018001f000 0x8007f80018001f00

def z976 : W := mkw 0x1858786e36c15d62 0x11858786e36c15d6 0x787878fe7fc1fc77 0xf787878fe7fc1fc7

def z977 : W := mkw 0x37ff80244dbde000 0x637ff80244dbde00 0x3fff80067ffff00f 0xa3fff80067ffff00

def z978 : W := mkw 0x00828842aa3085ba 0x000828842aa3085b 0xc19f98c7e0300ffd 0xcc19f98c7e0300ff

def z979 : W := mkw 0x2d805cc00b280500 0x02d805cc00b28050 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z980 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0xbfff98c01ffff00f 0xebfff98c01ffff00

def z981 : W := mkw 0x37fd80000dad6000 0x237fd80000dad600 0x3fff80001fce700f 0x83fff80001fce700

def z982 : W := mkw 0xad80fdc03b6a0f02 0x0ad80fdc03b6a0f0 0xbf81ffc07ffe0f8f 0x7bf81ffc07ffe0f8

def z983 : W := mkw 0x88007dae12421e60 0x188007dae12421e6 0x40007f3e00000c70 0x540007f3e00000c7

def z984 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xff987fc61ffe0f8f 0xfff987fc61ffe0f8

def z985 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0x3e007f001ffe0f87 0x73e007f001ffe0f8

def z986 : W := mkw 0x3f7556b540c04000 0x53f7556b540c0400 0xffffffffe1c0000f 0xdffffffffe1c0000

def z987 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xff9fffffe000000c 0x5ff9fffffe000000

def z988 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc6666739803ffff8 0xdc6666739803ffff

def z989 : W := mkw 0x408aa94abe339ffe 0x0408aa94abe339ff 0x000000000e318ff0 0x2000000000e318ff

def z990 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0xfe787f3e1fc1fc7f 0xffe787f3e1fc1fc7

def z991 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xffe07ff81ffe0f8f 0xfffe07ff81ffe0f8

def z992 : W := mkw 0x88007fff52421f60 0x588007fff52421f6 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z993 : W := mkw 0xc8007dc892421fdc 0x0c8007dc892421fd 0x80007fc000000ff0 0x580007fc000000ff

def z994 : W := mkw 0x377f8000059de000 0x2377f8000059de00 0x3e7f80001fcff007 0xa3e7f80001fcff00

def z995 : W := mkw 0x1858702c14815840 0x01858702c1481584 0x7878783e1fc1fc77 0xf7878783e1fc1fc7

def z996 : W := mkw 0x37ff80022dbde022 0x237ff80022dbde02 0x3fff80067ffff00f 0xa3fff80067ffff00

def z997 : W := mkw 0x008a8842af3985ba 0x0008a8842af3985b 0xc19f98c7ffff8ffd 0xec19f98c7ffff8ff

def z998 : W := mkw 0x1858582e06c15460 0x11858582e06c1546 0x7878183e0fc1fc75 0xe7878183e0fc1fc7

def z999 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xf99f98c7fff18fff 0xef99f98c7fff18ff

def z1000 : W := mkw 0x37ff82114dbde000 0x637ff82114dbde00 0x3fff8001fffff00f 0xa3fff8001fffff00

def z1001 : W := mkw 0x000a8002a41180ba 0x0000a8002a41180b 0xc19f98c7e0318ffd 0xec19f98c7e0318ff

def z1002 : W := mkw 0xad8075c0196a0b00 0x0ad8075c0196a0b0 0xbf8067c01ffe038f 0x3bf8067c01ffe038

def z1003 : W := mkw 0x1858782e16c15c60 0x11858782e16c15c6 0x79fff83e1fc1fc7f 0xf79fff83e1fc1fc7

def z1004 : W := mkw 0x37ff80402dbde102 0x237ff80402dbde10 0x3fff80c07ffff00f 0xa3fff80c07ffff00

def z1005 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3fff80001fcff006 0x83fff80001fcff00

def z1006 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfffffffff03e000f 0xffffffffff03e000

def z1007 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x419f98c7ee318ff4 0xa419f98c7ee318ff

def z1008 : W := mkw 0x00800842aa2005ba 0x000800842aa2005b 0xc19f98c7ee300ffd 0xec19f98c7ee300ff

def z1009 : W := mkw 0x000a0802861184b8 0x0000a0802861184b 0xc19f98c7ee318ffd 0xec19f98c7ee318ff

def z1010 : W := mkw 0xad807dc21b6a0f20 0x0ad807dc21b6a0f2 0xff807fc61ffe0fff 0x7ff807fc61ffe0ff

def z1011 : W := mkw 0x37fd80000dad6000 0x237fd80000dad600 0x3ff980001fcff007 0xa3ff980001fcff00

def z1012 : W := mkw 0x2f2556b540000000 0x42f2556b54000000 0xc79fffffe000000d 0xdc79fffffe000000

def z1013 : W := mkw 0x12fe80000cb5e000 0x012fe80000cb5e00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z1014 : W := mkw 0x377f00000495e000 0x0377f00000495e00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z1015 : W := mkw 0x37fe00000dbde000 0x037fe00000dbde00 0x3ffe00001ffff00f 0xa3ffe00001ffff00

def z1016 : W := mkw 0x37ff82354dbde000 0x637ff82354dbde00 0xffffe73ffffff00f 0xfffffe73ffffff00

def z1017 : W := mkw 0x1850782c12401c40 0x01850782c12401c4 0x7878783e1fc1fc77 0xf7878783e1fc1fc7

def z1018 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffe0300f8f 0xfffffffffe0300f8

def z1019 : W := mkw 0x1858582e06c15460 0x11858582e06c1546 0x7878783e0fc1f077 0xd7878783e0fc1f07

def z1020 : W := mkw 0xb7ff84c00dbde100 0x2b7ff84c00dbde10 0x3fff80c01ffff00f 0xa3fff80c01ffff00

def z1021 : W := mkw 0x022600000014a000 0x0022600000014a00 0x3e6600001ffff00f 0xa3e6600001ffff00

def z1022 : W := mkw 0x3d5054a400000000 0x03d5054a40000000 0xffffffffe000000f 0xdffffffffe000000

def z1023 : W := mkw 0x88007dc812421f40 0x088007dc812421f4 0xc0007ff800000ff0 0x5c0007ff800000ff

def z1024 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x7fff8007fffff00f 0xa7fff8007fffff00

def z1025 : W := mkw 0x527f023fc495f0fc 0x5527f023fc495f0f 0x407f803fe001f070 0x8407f803fe001f07

def z1026 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xf9ffffffe0000004 0xdf9ffffffe000000

def z1027 : W := mkw 0x37ff8237edbde0ba 0x637ff8237edbde0b 0x7fff803ffffff07f 0xa7fff803ffffff07

def z1028 : W := mkw 0x127c000004856000 0x0127c00000485600 0x3e7800001fcff007 0xa3e7800001fcff00

def z1029 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbfe07fc01fffff8f 0xfbfe07fc01fffff8

def z1030 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x7fffffffe0000006 0x97fffffffe000000

def z1031 : W := mkw 0x3775021100000000 0x0377502110000000 0xffffffffe000000f 0xdffffffffe000000

def z1032 : W := mkw 0x88007deeb2421ffa 0x188007deeb2421ff 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z1033 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0xbfff80c1fffff00f 0xabfff80c1fffff00

def z1034 : W := mkw 0x377f0000059de000 0x2377f0000059de00 0x3e7e00001ffff00f 0xa3e7e00001ffff00

def z1035 : W := mkw 0x37ff8002adbde0ba 0x237ff8002adbde0b 0xffff8007ffffffff 0xeffff8007fffffff

def z1036 : W := mkw 0x35da80000dbde000 0x235da80000dbde00 0x3ff800001ffff00f 0xa3ff800001ffff00

def z1037 : W := mkw 0x0808780a16411c60 0x00808780a16411c6 0x7878783e1fc1fc77 0xf7878783e1fc1fc7

def z1038 : W := mkw 0x527f823f8495f0fc 0x3527f823f8495f0f 0x407f803f8001f070 0x8407f803f8001f07

def z1039 : W := mkw 0x00080842a60105ba 0x000080842a60105b 0xc19f98c7ee018ffd 0xec19f98c7ee018ff

def z1040 : W := mkw 0x27a78000093ca000 0x227a78000093ca00 0x3fe780001ffff00f 0xa3fe780001ffff00

def z1041 : W := mkw 0x422623199016badc 0x0422623199016bad 0xc6606739903ffff2 0x7c6606739903ffff

def z1042 : W := mkw 0x18587cae56c15c60 0x518587cae56c15c6 0x787878fe7fc1fc77 0xf787878fe7fc1fc7

def z1043 : W := mkw 0x1859782e56c15c60 0x51859782e56c15c6 0x7879f83e7fc1fc77 0xf7879f83e7fc1fc7

def z1044 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0xbf807fc01ffe038e 0x1bf807fc01ffe038

def z1045 : W := mkw 0x258029401b2a0f00 0x0258029401b2a0f0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z1046 : W := mkw 0x37ff84800dbde000 0x237ff84800dbde00 0xbfff87c01ffff00f 0xabfff87c01ffff00

def z1047 : W := mkw 0x2580000009ac6000 0x22580000009ac600 0x3f8000001ffe700f 0x23f8000001ffe700

def z1048 : W := mkw 0xc08aa94abf7fbffe 0x0c08aa94abf7fbff 0x000000001ffffff0 0x2000000001ffffff

def z1049 : W := mkw 0x0000000080000098 0x0000000008000009 0xc19f98c7e0000ffd 0xcc19f98c7e0000ff

def z1050 : W := mkw 0x422623199016badc 0x0422623199016bad 0x86606738103ffffb 0x786606738103ffff

def z1051 : W := mkw 0x3f7556b5410c2000 0x63f7556b5410c200 0xffffffffe00e000f 0xdffffffffe00e000

def z1052 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0x3f807fc01ffe0f86 0x33f807fc01ffe0f8

def z1053 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x3fff98c67ffff00f 0xa3fff98c67ffff00

def z1054 : W := mkw 0x1858786e16c15d60 0x11858786e16c15d6 0xf87878fe1fc1fff7 0xff87878fe1fc1fff

def z1055 : W := mkw 0x37ff80020dbde020 0x237ff80020dbde02 0x7fff80061ffff07f 0xa7fff80061ffff07

def z1056 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0xc1fff8ffee318fff 0xfc1fff8ffee318ff

def z1057 : W := mkw 0x0800782e12401c60 0x10800782e12401c6 0x7860783e1fc1fc77 0xf7860783e1fc1fc7

def z1058 : W := mkw 0xad807dc01b6a0f00 0x0ad807dc01b6a0f0 0x3f8067001ffe0f8f 0x33f8067001ffe0f8

def z1059 : W := mkw 0x98587dee16c35f60 0x198587dee16c35f6 0xfe787ffe1fffffff 0xffe787ffe1ffffff

def z1060 : W := mkw 0x35db80000dbde000 0x235db80000dbde00 0x3f9980001ffff00f 0x23f9980001ffff00

def z1061 : W := mkw 0xc8007fd912421f44 0x0c8007fd912421f4 0x80007ff800000f80 0x580007ff800000f8

def z1062 : W := mkw 0x527e823fa495f0fe 0x1527e823fa495f0f 0x407f803fe001f070 0x8407f803fe001f07

def z1063 : W := mkw 0x422623199016badc 0x0422623199016bad 0x06666738103ffffb 0xb06666738103ffff

def z1064 : W := mkw 0xad807dc23b6a0f22 0x0ad807dc23b6a0f2 0xbf807fc67ffe0f8f 0x7bf807fc67ffe0f8

def z1065 : W := mkw 0x37ff82110dbde000 0x237ff82110dbde00 0x3fffe7381ffff00f 0xb3fffe7381ffff00

def z1066 : W := mkw 0x10da80000dbde000 0x210da80000dbde00 0x381800001ffff004 0x2381800001ffff00

def z1067 : W := mkw 0xa58029401b6a0f00 0x0a58029401b6a0f0 0xbf8067001ffe0f8f 0x7bf8067001ffe0f8

def z1068 : W := mkw 0x37ff80000dbde000 0x237ff80000dbde00 0x39ff80001ffff004 0xa39ff80001ffff00

def z1069 : W := mkw 0x008808420e210520 0x0008808420e21052 0xc19f98c7ee318ffd 0xec19f98c7ee318ff

def z1070 : W := mkw 0xe7a707d1c93ea39c 0x4e7a707d1c93ea39 0x878787c1e03e0388 0x0878787c1e03e038

def z1071 : W := mkw 0x1858702c14c15840 0x11858702c14c1584 0x787860381fc1fc77 0xf787860381fc1fc7

def z1072 : W := mkw 0x18587cae16c15c60 0x118587cae16c15c6 0xf8787ffe1fc1fc77 0xff8787ffe1fc1fc7

def z1073 : W := mkw 0x8800796e12421f60 0x18800796e12421f6 0x4000783e00000ff0 0x54000783e00000ff

def z1074 : W := mkw 0x0000210010020a00 0x00000210010020a0 0xbe0067001ffe0f8f 0x7be0067001ffe0f8

def z1075 : W := mkw 0x2d807580192a0a00 0x02d807580192a0a0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z1076 : W := mkw 0x008a8842aef1c5ba 0x1008a8842aef1c5b 0xc19f98c7eff18ffd 0xec19f98c7eff18ff

def z1077 : W := mkw 0x1275023540000000 0x4127502354000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z1078 : W := mkw 0x022621081016ba40 0x0022621081016ba4 0xc6666738103ffffb 0xfc6666738103ffff

def z1079 : W := mkw 0x10d800000da94000 0x010d800000da9400 0x387800001ffff007 0xa387800001ffff00

def z1080 : W := mkw 0x1058000804815040 0x0105800080481504 0x787800381fc1f077 0xa787800381fc1f07

def z1081 : W := mkw 0x008a8842ae3185ba 0x0008a8842ae3185b 0x819f98c7ee318ffc 0x2819f98c7ee318ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z7,z2,z3,z4,z5,z6]),(0,[z8,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z9]),(0,[z1,z2,z3,z4,z10,z5,z6]),(0,[z1,z11,z2,z3,z4,z5,z6])],[(1,[z1,z2,z12,z4,z5,z6])],[(0,[z1,z2,z3,z4,z13,z5,z6]),(0,[z1,z2,z14,z3,z4,z5,z6])],[(0,[z1,z15,z2,z3,z4,z5,z6]),(0,[z1,z16,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z18,z6])],[(0,[z1,z2,z19,z4,z20,z5,z6])],[(0,[z2,z3,z4,z21,z5,z22,z6]),(0,[z1,z23,z2,z4,z5,z24,z6]),(0,[z25,z1,z2,z3,z26,z5,z6]),(0,[z1,z2,z3,z4,z5,z27,z6]),(0,[z1,z2,z3,z4,z28,z5,z6]),(0,[z1,z29,z2,z3,z4,z5,z6]),(0,[z1,z2,z30,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z31,z6]),(0,[z1,z32,z2,z3,z4,z5,z6])],[(0,[z1,z2,z33,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z34]),(0,[z1,z2,z4,z35,z5,z24,z6])],[(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z37,z1,z2,z3,z4,z5,z6]),(0,[z1,z38,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z4,z5,z6,z39])]],
   [[(0,[z40,z1,z2,z3,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z42]),(0,[z1,z2,z3,z43,z4,z5,z6]),(0,[z1,z3,z4,z5,z44,z6,z45]),(0,[z1,z2,z3,z46,z4,z5,z6]),(0,[z47,z2,z3,z4,z5,z48,z6])],[(0,[z1,z2,z49,z50,z4,z5,z6]),(0,[z1,z2,z3,z51,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z52])],[(0,[z1,z2,z3,z4,z5,z6,z53]),(1,[z54,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z5,z6,z55]),(0,[z1,z2,z3,z4,z5,z56,z6])],[(0,[z1,z2,z3,z4,z5,z57,z6])],[(0,[z58,z2,z59,z3,z4,z5,z6]),(0,[z60,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z61]),(0,[z1,z2,z4,z20,z5,z24,z6]),(0,[z1,z2,z49,z3,z4,z35,z6])],[(0,[z62,z1,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z22,z6]),(0,[z1,z64,z2,z49,z4,z5,z6]),(0,[z65,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z66,z6]),(0,[z1,z2,z3,z4,z5,z6,z67])],[(0,[z1,z2,z3,z4,z5,z6,z68]),(0,[z1,z2,z3,z4,z69,z5,z6])],[(0,[z1,z70,z2,z3,z4,z5,z6]),(0,[z1,z2,z71,z3,z4,z5,z6]),(0,[z72,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z73,z6]),(0,[z1,z2,z74,z3,z4,z5,z56])]],
   [[(0,[z1,z2,z3,z4,z75,z22,z6]),(0,[z1,z76,z2,z3,z4,z5,z6]),(0,[z77,z1,z2,z3,z4,z5,z78]),(0,[z1,z2,z4,z5,z73,z6,z45])],[(0,[z1,z2,z3,z4,z5,z79,z6]),(0,[z1,z80,z2,z3,z4,z5,z6]),(0,[z1,z2,z81,z3,z4,z5,z6])],[(0,[z82,z1,z83,z3,z4,z5,z6]),(0,[z1,z2,z84,z3,z4,z5,z6])],[(0,[z1,z85,z2,z3,z4,z5,z6]),(0,[z1,z86,z2,z87,z3,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z6]),(0,[z1,z88,z2,z3,z4,z5,z6]),(0,[z1,z89,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z75,z6]),(0,[z1,z91,z2,z3,z4,z5,z6]),(0,[z1,z2,z92,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z93,z94,z6])],[(0,[z1,z2,z3,z4,z5,z95,z6]),(0,[z1,z2,z3,z4,z5,z6,z96]),(0,[z1,z2,z3,z97,z4,z5,z6]),(0,[z98,z1,z2,z3,z4,z5,z6])],[(0,[z99,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z100,z5,z6]),(0,[z1,z2,z3,z4,z21,z48,z6]),(0,[z2,z3,z4,z5,z42,z6,z101]),(0,[z41,z1,z2,z102,z4,z5,z6]),(0,[z1,z103,z2,z104,z4,z5,z6]),(1,[z1,z64,z2,z4,z18,z6])],[(0,[z1,z2,z3,z4,z105,z5,z6]),(1,[z106,z2,z50,z4,z5,z6]),(0,[z1,z107,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z108,z5,z6]),(0,[z1,z109,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z110,z6]),(1,[z1,z111,z2,z3,z5,z56])],[(0,[z1,z2,z112,z3,z4,z5,z6]),(0,[z1,z113,z2,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z2,z4,z5,z18,z6]),(0,[z1,z115,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z116,z5,z6]),(0,[z1,z117,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z118,z5,z6]),(0,[z119,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z120,z6]),(0,[z47,z1,z2,z3,z4,z5,z6])],[(0,[z121,z1,z2,z3,z4,z5,z6]),(0,[z2,z3,z50,z122,z4,z5,z6]),(0,[z1,z2,z3,z4,z123,z5,z6]),(0,[z1,z124,z2,z3,z4,z5,z6])],[(0,[z1,z125,z2,z3,z4,z5,z6]),(0,[z1,z126,z2,z3,z4,z5,z6])],[(1,[z1,z17,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z127]),(0,[z1,z2,z3,z4,z5,z6,z128]),(0,[z1,z2,z129,z3,z4,z5,z6]),(0,[z130,z1,z2,z3,z4,z5,z6]),(1,[z1,z131,z3,z4,z5,z6])],[(0,[z1,z2,z132,z3,z4,z5,z6]),(0,[z133,z1,z2,z3,z4,z5,z101]),(0,[z1,z2,z3,z4,z5,z134,z6]),(1,[z1,z135,z3,z4,z136,z6]),(0,[z1,z137,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z138,z2,z3,z4,z21,z5,z6]),(0,[z1,z2,z139,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z140,z6])],[(0,[z1,z135,z2,z3,z4,z44,z6]),(0,[z1,z141,z2,z3,z4,z93,z5]),(0,[z1,z2,z3,z4,z5,z6,z142])],[(0,[z143,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z144,z6]),(0,[z1,z23,z145,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z146,z3,z4,z5,z6]),(0,[z1,z2,z19,z147,z4,z5,z6]),(0,[z1,z2,z3,z4,z148,z5,z6]),(0,[z1,z104,z3,z4,z5,z6,z45]),(1,[z1,z2,z43,z4,z5,z6]),(0,[z1,z2,z149,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z150,z5,z6]),(0,[z1,z3,z4,z5,z151,z18,z6])],[(1,[z82,z83,z3,z4,z5,z6]),(0,[z1,z145,z104,z3,z4,z5,z6]),(0,[z1,z135,z3,z4,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z152]),(0,[z1,z2,z3,z4,z5,z6,z153])],[(0,[z2,z3,z122,z4,z154,z5,z6]),(0,[z1,z2,z3,z4,z155,z5,z6]),(1,[z1,z3,z4,z5,z156,z6])],[(0,[z82,z1,z2,z3,z4,z5,z6]),(0,[z1,z157,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z154,z5,z6]),(0,[z1,z159,z2,z87,z4,z5,z6]),(1,[z1,z160,z2,z3,z4,z5]),(0,[z1,z2,z3,z161,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z162]),(0,[z1,z163,z2,z3,z4,z5,z6]),(0,[z1,z164,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z165,z4,z5,z6]),(0,[z1,z166,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z167]),(0,[z1,z2,z3,z168,z4,z5,z6])],[(0,[z138,z2,z3,z50,z4,z5,z6]),(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z170,z1,z2,z3,z4,z5,z6])],[(0,[z1,z103,z2,z4,z20,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z171]),(0,[z1,z172,z2,z3,z4,z5,z6]),(0,[z1,z173,z2,z3,z4,z48,z6]),(0,[z1,z2,z3,z174,z4,z5,z6])]],
   [[(0,[z175,z1,z2,z3,z4,z5,z6]),(0,[z77,z176,z1,z2,z3,z4,z6]),(0,[z1,z145,z2,z3,z4,z5,z177]),(0,[z1,z2,z3,z4,z5,z6,z178]),(0,[z1,z2,z3,z4,z179,z5,z6])],[(0,[z1,z2,z180,z3,z4,z5,z6]),(0,[z1,z181,z2,z3,z4,z5,z6])],[(0,[z1,z2,z182,z3,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z5,z183,z6]),(0,[z1,z2,z3,z4,z5,z184,z6])],[(0,[z1,z2,z50,z4,z20,z5,z6]),(0,[z1,z185,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z186,z4,z5,z6]),(0,[z1,z2,z3,z4,z187,z5,z6]),(0,[z1,z188,z2,z3,z4,z5,z6]),(0,[z1,z189,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z5,z6,z190])],[(0,[z1,z191,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z192,z5,z6]),(0,[z176,z1,z145,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z193,z6])],[(0,[z1,z2,z3,z4,z194,z5,z6]),(0,[z1,z2,z195,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z196,z6]),(0,[z197,z1,z2,z3,z4,z5,z6])]],
   [[(0,[z198,z1,z2,z3,z4,z5,z6]),(0,[z2,z147,z3,z50,z4,z5,z6]),(0,[z138,z1,z2,z3,z4,z5,z6]),(0,[z138,z1,z173,z2,z3,z5,z6]),(0,[z114,z1,z103,z2,z4,z5,z6]),(0,[z1,z2,z199,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z200,z6]),(1,[z25,z1,z87,z3,z5,z6]),(0,[z1,z2,z201,z3,z4,z5,z6]),(0,[z114,z1,z2,z3,z4,z5,z6]),(1,[z1,z202,z3,z4,z5,z6])],[(0,[z133,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z203,z3,z4,z5,z6]),(0,[z1,z2,z204,z3,z4,z5,z6]),(0,[z1,z173,z2,z3,z5,z48,z6])],[(0,[z1,z23,z3,z4,z5,z6,z45])],[(0,[z106,z1,z2,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z20,z5,z6]),(0,[z1,z202,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z147,z3,z100,z5,z6]),(0,[z1,z103,z2,z3,z4,z5,z6]),(1,[z1,z103,z104,z4,z5,z6]),(0,[z1,z2,z205,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z206,z6]),(0,[z1,z2,z207,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z208,z6])],[(0,[z1,z2,z3,z4,z5,z209,z6]),(0,[z1,z2,z3,z4,z5,z210,z6]),(0,[z114,z211,z2,z3,z4,z5,z6]),(0,[z1,z2,z212,z3,z4,z5,z6])],[(0,[z213,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z214,z6]),(0,[z1,z2,z3,z4,z5,z215,z6])]],
   [[(0,[z1,z2,z216,z3,z4,z5,z6]),(0,[z1,z2,z3,z217,z4,z5,z6]),(0,[z1,z2,z3,z4,z218,z5,z6]),(0,[z1,z219,z3,z4,z5,z6,z220]),(0,[z1,z221,z2,z3,z4,z5,z6])],[(1,[z58,z59,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z154,z5,z6]),(0,[z222,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z223,z5,z6]),(0,[z1,z224,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z22,z48,z6]),(0,[z1,z2,z225,z4,z5,z6,z220])],[(0,[z1,z226,z2,z3,z4,z5,z6]),(0,[z1,z2,z147,z4,z5,z18,z6]),(0,[z1,z2,z3,z227,z4,z5,z6]),(0,[z1,z2,z87,z43,z4,z5,z6]),(0,[z1,z3,z4,z136,z5,z177,z6])],[(0,[z228,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z101,z229]),(0,[z1,z2,z3,z4,z230,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z45]),(0,[z1,z2,z3,z4,z231,z5,z6]),(0,[z1,z232,z2,z3,z4,z5,z6])],[],[(0,[z114,z1,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z233,z4,z5,z6]),(0,[z1,z234,z2,z3,z4,z5,z6]),(0,[z235,z1,z2,z3,z4,z5,z6]),(0,[z236,z1,z2,z3,z4,z5,z6]),(0,[z1,z237,z2,z3,z4,z5,z6])],[(0,[z138,z1,z2,z186,z4,z5,z6]),(0,[z1,z2,z3,z238,z4,z5,z6])]],
   [[(0,[z239,z1,z2,z3,z4,z5,z6]),(0,[z1,z159,z2,z3,z4,z5,z6])],[(0,[z106,z1,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z90,z75,z5,z6])],[(0,[z1,z103,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z4,z240,z5,z6]),(0,[z1,z241,z2,z3,z4,z5,z6]),(0,[z242,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z243,z6]),(0,[z1,z2,z3,z244,z4,z5,z6]),(0,[z1,z245,z2,z3,z4,z5,z6])],[(1,[z1,z2,z186,z4,z5,z6]),(0,[z246,z1,z2,z3,z4,z5,z6]),(1,[z247,z2,z3,z4,z21,z6]),(0,[z176,z1,z2,z19,z3,z4,z5]),(1,[z1,z2,z4,z5,z6,z190])],[(0,[z1,z248,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z249,z5,z6]),(0,[z247,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z250,z4,z5,z6])],[(0,[z1,z2,z3,z4,z251,z5,z6]),(0,[z1,z2,z147,z4,z20,z5,z6]),(0,[z77,z1,z2,z3,z4,z44,z6]),(0,[z1,z2,z252,z3,z4,z5,z6])],[(0,[z1,z2,z253,z3,z4,z5,z6])]],
   [[(0,[z254,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z255,z6]),(0,[z1,z141,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z256,z6]),(0,[z176,z1,z2,z3,z4,z6,z220])],[(0,[z1,z2,z257,z3,z4,z5,z6]),(0,[z258,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z259]),(0,[z260,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z261,z3,z4,z5,z6]),(0,[z1,z2,z262,z3,z4,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z177]),(0,[z1,z2,z3,z4,z5,z263,z6])],[(0,[z1,z2,z3,z4,z264,z5,z6]),(0,[z1,z265,z2,z3,z4,z5,z6])],[(0,[z1,z266,z2,z3,z4,z5,z6]),(0,[z63,z1,z2,z233,z4,z5,z6]),(0,[z41,z133,z2,z3,z4,z5,z6]),(0,[z267,z1,z2,z3,z4,z5,z6]),(0,[z268,z1,z2,z3,z4,z5,z6]),(0,[z1,z111,z2,z74,z3,z5,z6])],[(0,[z269,z1,z2,z50,z4,z5,z6]),(0,[z1,z2,z3,z270,z4,z5,z6]),(0,[z1,z64,z103,z2,z4,z5,z6]),(0,[z1,z271,z2,z3,z4,z5,z6])],[(0,[z1,z272,z2,z3,z4,z5,z6]),(0,[z273,z1,z2,z3,z4,z5,z6]),(0,[z1,z64,z2,z3,z4,z5,z6])],[(0,[z114,z1,z23,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z52])]],
   [[(0,[z1,z2,z3,z4,z5,z274,z6]),(0,[z1,z2,z3,z4,z5,z275,z6]),(0,[z1,z2,z87,z3,z4,z5,z6]),(1,[z276,z2,z3,z4,z5,z6]),(0,[z277,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z278,z4,z5,z6]),(1,[z2,z3,z4,z5,z279,z6])],[(0,[z82,z1,z2,z280,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z281,z6])],[(0,[z1,z2,z3,z4,z5,z6,z282]),(0,[z63,z2,z3,z122,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z283]),(0,[z284,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z285,z6]),(0,[z1,z286,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z287,z6]),(0,[z1,z23,z2,z4,z288,z5,z6]),(0,[z1,z289,z2,z3,z4,z5,z6]),(0,[z1,z111,z2,z3,z5,z56,z6])],[(0,[z138,z1,z2,z3,z75,z5,z6]),(0,[z1,z2,z3,z4,z5,z290,z6]),(0,[z1,z2,z3,z4,z5,z6,z291])],[(0,[z1,z2,z3,z4,z5,z292,z6]),(0,[z1,z2,z3,z4,z293,z5,z6]),(0,[z1,z2,z3,z4,z5,z294,z6]),(0,[z1,z2,z147,z3,z4,z5,z6]),(0,[z295,z1,z2,z3,z4,z5,z6]),(0,[z133,z2,z3,z4,z5,z6,z101]),(0,[z1,z2,z296,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z297,z5,z6]),(0,[z298,z1,z2,z3,z4,z5,z6])],[(0,[z41,z1,z2,z3,z4,z5,z101]),(0,[z1,z2,z299,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z300,z6])],[(0,[z1,z301,z2,z3,z4,z5,z6]),(0,[z82,z83,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z302,z6]),(0,[z138,z63,z2,z3,z4,z5,z6]),(0,[z1,z2,z303,z3,z4,z5,z6]),(0,[z1,z23,z2,z19,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z304,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z305,z6]),(0,[z1,z2,z3,z4,z5,z306,z6]),(0,[z1,z307,z2,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z308,z6]),(0,[z1,z2,z19,z3,z4,z5,z177])],[(0,[z138,z1,z309,z2,z3,z5,z6]),(0,[z1,z2,z3,z310,z4,z5,z6]),(1,[z1,z2,z311,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z312,z6]),(0,[z1,z313,z2,z3,z4,z5,z6])],[(0,[z63,z2,z3,z4,z5,z22,z6]),(0,[z1,z2,z314,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z315,z6]),(0,[z1,z2,z3,z4,z5,z6,z316]),(0,[z1,z2,z49,z4,z20,z5,z6]),(0,[z114,z1,z309,z2,z3,z5,z6])],[(0,[z2,z3,z122,z4,z21,z5,z6])],[(0,[z317,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z318,z5,z6]),(0,[z77,z1,z3,z4,z5,z44,z6]),(0,[z1,z160,z2,z3,z4,z5,z44]),(0,[z176,z1,z2,z3,z4,z5,z220])],[],[(0,[z319,z1,z2,z3,z4,z5,z6]),(0,[z1,z104,z3,z4,z288,z5,z6]),(0,[z1,z2,z3,z4,z5,z320,z6]),(0,[z1,z2,z3,z321,z4,z5,z6]),(0,[z1,z2,z322,z3,z4,z5,z6]),(0,[z1,z111,z2,z3,z4,z5,z56])],[(0,[z1,z2,z3,z4,z323,z5,z6]),(1,[z158,z2,z3,z122,z5,z6]),(0,[z1,z2,z3,z4,z324,z5,z6]),(0,[z1,z86,z2,z3,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z5,z177])]],
   [[(0,[z325,z1,z2,z3,z4,z5,z6]),(0,[z138,z1,z326,z3,z4,z5,z6]),(0,[z1,z2,z327,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z328]),(0,[z1,z2,z3,z4,z5,z45,z220]),(1,[z1,z3,z4,z5,z151,z6]),(0,[z1,z329,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z330,z6]),(0,[z1,z145,z2,z3,z4,z5,z45]),(0,[z1,z2,z3,z331,z4,z5,z6]),(0,[z1,z2,z4,z5,z24,z6,z39]),(0,[z1,z202,z3,z4,z5,z24,z6])],[(0,[z1,z2,z3,z4,z5,z6,z332]),(0,[z1,z2,z3,z4,z5,z333,z6])],[(1,[z1,z2,z280,z4,z5,z6]),(0,[z1,z2,z50,z4,z5,z18,z6]),(0,[z1,z2,z334,z3,z4,z5,z6]),(0,[z1,z2,z12,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z335])],[(0,[z1,z2,z3,z4,z5,z336,z6])],[(0,[z77,z1,z2,z3,z4,z5,z52]),(0,[z337,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z39]),(0,[z1,z2,z3,z4,z5,z338,z6]),(0,[z176,z1,z2,z3,z4,z5,z94])],[(0,[z1,z2,z3,z4,z339,z5,z6]),(1,[z1,z2,z3,z4,z5,z340]),(0,[z1,z103,z2,z3,z4,z5,z340]),(0,[z1,z2,z341,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z342])]],
   [[(0,[z1,z2,z3,z4,z343,z5,z6]),(0,[z63,z247,z2,z3,z4,z5,z6]),(0,[z1,z23,z2,z4,z35,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z344]),(0,[z1,z2,z3,z4,z345,z5,z6])],[(0,[z138,z1,z216,z3,z4,z5,z6]),(0,[z1,z2,z3,z346,z4,z5,z6]),(1,[z1,z86,z3,z26,z5,z6]),(0,[z77,z1,z135,z3,z4,z5,z6]),(1,[z77,z1,z3,z4,z44,z6]),(0,[z1,z347,z2,z3,z4,z5,z6]),(0,[z1,z2,z49,z3,z4,z5,z6])],[(0,[z1,z135,z2,z3,z4,z5,z6]),(0,[z348,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z349,z6]),(1,[z1,z2,z225,z4,z5,z6])],[(0,[z1,z2,z3,z350,z4,z5,z6]),(0,[z1,z351,z2,z3,z4,z5,z6])],[(0,[z106,z2,z3,z50,z4,z5,z6]),(1,[z1,z2,z165,z4,z5,z6]),(0,[z41,z1,z2,z3,z4,z5,z6]),(0,[z1,z64,z23,z2,z4,z5,z6]),(0,[z1,z125,z2,z4,z5,z24,z6]),(0,[z1,z2,z352,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z153,z220])],[(0,[z353,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z354,z6]),(0,[z355,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z356]),(0,[z1,z2,z3,z4,z5,z6,z220]),(1,[z1,z2,z3,z4,z93,z94])],[(0,[z357,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z358]),(1,[z1,z2,z74,z3,z5,z229])],[(0,[z359,z1,z2,z3,z4,z5,z6]),(0,[z360,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z361]),(0,[z1,z2,z362,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z249,z5,z22,z6]),(0,[z1,z363,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z364,z5,z6]),(0,[z1,z23,z3,z4,z288,z5,z6]),(0,[z1,z141,z145,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z365]),(0,[z1,z2,z3,z4,z366,z5,z6]),(0,[z1,z2,z3,z4,z367,z5,z6])],[(0,[z1,z2,z3,z4,z21,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z368]),(0,[z1,z2,z74,z3,z5,z6,z229])],[(0,[z1,z103,z104,z3,z4,z5,z6]),(0,[z1,z369,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z370,z5,z6]),(0,[z1,z103,z23,z3,z4,z5,z6]),(0,[z371,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z372,z5,z6])],[(0,[z63,z1,z2,z373,z4,z5,z6]),(0,[z374,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z57]),(0,[z1,z2,z3,z4,z5,z48,z6])],[(0,[z1,z2,z3,z4,z5,z375,z6]),(0,[z1,z2,z3,z4,z5,z376,z6]),(0,[z1,z2,z377,z3,z4,z5,z6]),(0,[z1,z2,z49,z147,z4,z5,z6]),(0,[z25,z1,z87,z3,z4,z5,z6]),(0,[z1,z378,z2,z3,z4,z5,z6]),(0,[z1,z2,z379,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z380])],[(0,[z381,z1,z2,z3,z4,z5,z6]),(0,[z269,z1,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z4,z382,z5,z6]),(0,[z1,z2,z3,z4,z5,z383,z6]),(0,[z1,z2,z3,z4,z6,z335,z45]),(0,[z1,z2,z3,z4,z5,z6,z384]),(0,[z1,z64,z2,z4,z5,z18,z6])]],
   [[(0,[z58,z82,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z94,z45]),(0,[z114,z1,z2,z3,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z229])],[(0,[z138,z1,z2,z3,z4,z5,z95]),(0,[z1,z2,z385,z3,z4,z5,z6]),(0,[z1,z386,z2,z3,z4,z5,z6]),(0,[z114,z1,z2,z387,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z388,z6]),(0,[z389,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z75,z21,z6]),(0,[z1,z2,z3,z4,z288,z5,z6]),(0,[z390,z1,z2,z3,z4,z5,z6]),(0,[z1,z135,z2,z3,z4,z136,z6]),(0,[z1,z2,z3,z4,z5,z391,z6]),(0,[z1,z173,z2,z3,z4,z75,z6]),(0,[z1,z2,z3,z392,z4,z5,z6])],[(0,[z1,z2,z3,z4,z393,z5,z6]),(0,[z1,z125,z2,z19,z4,z5,z6]),(0,[z1,z2,z74,z3,z4,z5,z229])],[(0,[z1,z394,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z395,z4,z5,z6]),(0,[z269,z2,z147,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z122,z5,z6]),(0,[z1,z396,z2,z3,z4,z5,z6]),(1,[z211,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z90,z4,z48,z6]),(0,[z1,z397,z2,z3,z4,z5,z6])],[(0,[z398,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z399,z6]),(0,[z1,z2,z74,z3,z4,z5,z6])],[(0,[z1,z400,z2,z3,z4,z5,z6]),(0,[z1,z64,z2,z3,z4,z18,z6])]],
   [[(0,[z1,z2,z3,z4,z401,z5,z6]),(0,[z1,z2,z402,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z403,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z404])],[(0,[z1,z2,z3,z4,z5,z405,z6]),(1,[z63,z2,z3,z4,z22,z6]),(0,[z1,z2,z3,z406,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z6,z45]),(0,[z1,z2,z407,z3,z4,z5,z6]),(1,[z1,z2,z387,z20,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6,z408]),(0,[z1,z2,z3,z4,z409,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z410]),(0,[z1,z2,z3,z4,z411,z5,z6])],[(0,[z1,z2,z3,z102,z4,z5,z6]),(0,[z1,z2,z412,z3,z4,z5,z6]),(0,[z413,z1,z2,z3,z4,z5,z6]),(0,[z1,z141,z2,z3,z4,z5,z45]),(0,[z1,z2,z3,z4,z5,z177,z94]),(0,[z114,z1,z2,z4,z5,z24,z6]),(0,[z2,z3,z4,z5,z279,z48,z6])],[(0,[z1,z173,z2,z3,z4,z5,z6])],[(0,[z1,z1,z2,z3,z4,z5,z6]),(0,[z77,z1,z141,z3,z4,z5,z6]),(0,[z1,z141,z3,z4,z5,z6,z45])],[(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z414,z1,z2,z3,z4,z5,z6])],[(0,[z1,z103,z2,z4,z5,z24,z6]),(1,[z1,z2,z3,z90,z75,z6]),(0,[z1,z219,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z415]),(0,[z1,z2,z3,z4,z5,z57,z44]),(0,[z1,z309,z2,z387,z3,z5,z6]),(0,[z1,z2,z416,z3,z4,z5,z6])],[(0,[z1,z417,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z418,z6]),(0,[z1,z419,z2,z3,z4,z5,z6])],[(0,[z1,z420,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z421]),(0,[z1,z211,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z422,z5,z6])],[(0,[z1,z423,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z424,z6]),(0,[z1,z2,z3,z4,z5,z425,z6])],[(0,[z1,z2,z50,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z426,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z427]),(0,[z428,z1,z2,z3,z4,z5,z6])],[(0,[z1,z429,z2,z3,z4,z5,z6]),(0,[z1,z2,z430,z3,z4,z5,z6]),(0,[z1,z86,z3,z4,z26,z5,z6]),(0,[z1,z2,z3,z4,z5,z431,z6])],[(0,[z1,z432,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z35,z5,z6]),(0,[z1,z2,z3,z4,z433,z5,z6]),(1,[z1,z434,z3,z4,z5,z6])]],
   [[(0,[z138,z1,z2,z3,z4,z435,z6]),(0,[z1,z2,z3,z4,z436,z5,z6]),(0,[z41,z1,z2,z311,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z437])],[(0,[z1,z2,z3,z438,z4,z5,z6]),(0,[z1,z2,z3,z4,z439,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z45])],[(0,[z58,z1,z59,z3,z4,z5,z6]),(0,[z1,z103,z2,z4,z288,z5,z6]),(0,[z1,z135,z2,z3,z4,z94,z6]),(0,[z440,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z2,z19,z4,z5,z6])],[(0,[z1,z2,z441,z3,z4,z5,z6]),(0,[z176,z1,z131,z3,z4,z5,z6])],[(0,[z138,z1,z2,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z5,z442,z6])],[(0,[z443,z1,z2,z3,z4,z5,z6]),(0,[z444,z1,z2,z3,z4,z5,z6]),(0,[z445,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z446,z6])],[(0,[z1,z23,z2,z50,z4,z5,z6]),(0,[z1,z103,z2,z19,z4,z5,z6]),(0,[z25,z1,z2,z87,z3,z5,z6]),(0,[z447,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z387,z4,z20,z5,z6])],[(0,[z1,z2,z3,z4,z448,z5,z6]),(0,[z1,z2,z3,z4,z5,z449,z6]),(0,[z1,z2,z3,z4,z5,z61,z6]),(1,[z1,z2,z49,z4,z35,z6])]],
   [[(0,[z450,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z451]),(0,[z1,z452,z2,z3,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z5,z45]),(0,[z1,z2,z453,z3,z4,z5,z6]),(0,[z1,z111,z2,z454,z4,z5,z6])],[(1,[z1,z2,z3,z4,z210,z6]),(1,[z1,z2,z233,z4,z5,z6]),(0,[z1,z2,z3,z4,z455,z5,z6]),(0,[z1,z456,z2,z3,z4,z5,z6])],[(0,[z1,z457,z2,z3,z4,z5,z6]),(0,[z1,z104,z3,z4,z136,z5,z6]),(0,[z1,z458,z2,z3,z4,z5,z6]),(0,[z1,z2,z49,z3,z4,z18,z6]),(0,[z1,z2,z4,z35,z5,z18,z6]),(0,[z1,z2,z3,z4,z5,z6,z459]),(1,[z1,z3,z4,z5,z6,z153])],[(0,[z1,z2,z3,z460,z4,z5,z6]),(1,[z1,z2,z102,z4,z5,z6]),(0,[z1,z2,z461,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z462,z5,z6])],[(0,[z463,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z464,z3,z4,z5,z6]),(0,[z1,z111,z2,z139,z4,z5,z6])],[(0,[z1,z2,z465,z3,z4,z5,z6]),(0,[z1,z466,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z467,z5,z6]),(0,[z1,z2,z3,z4,z5,z468,z6]),(1,[z1,z2,z3,z4,z5,z469]),(0,[z1,z173,z2,z3,z90,z5,z6]),(0,[z470,z1,z2,z3,z4,z5,z6])],[(0,[z471,z1,z2,z3,z4,z5,z6]),(0,[z472,z1,z2,z3,z4,z5,z6]),(0,[z1,z473,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z474,z6]),(0,[z475,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z476,z6]),(0,[z477,z1,z2,z3,z4,z5,z6]),(0,[z1,z173,z2,z278,z4,z5,z6])]],
   [[(0,[z1,z478,z2,z3,z4,z5,z6]),(0,[z1,z2,z479,z3,z4,z5,z6]),(0,[z77,z1,z3,z4,z5,z177,z6]),(0,[z1,z2,z3,z4,z5,z480,z6]),(0,[z1,z64,z2,z4,z5,z24,z6]),(0,[z1,z2,z3,z4,z5,z279,z6])],[(0,[z82,z1,z2,z460,z4,z5,z6]),(0,[z1,z481,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z469,z18]),(0,[z482,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z483])],[(0,[z1,z2,z3,z4,z5,z6,z484]),(0,[z1,z2,z165,z3,z4,z5,z6]),(0,[z138,z1,z2,z3,z154,z5,z6]),(0,[z1,z485,z2,z3,z4,z5,z6]),(0,[z486,z1,z2,z3,z4,z5,z6]),(0,[z77,z1,z2,z3,z4,z136,z6]),(0,[z1,z2,z3,z4,z5,z487,z6]),(0,[z1,z2,z131,z3,z4,z5,z6])],[(1,[z1,z488,z2,z3,z5,z6]),(0,[z489,z1,z2,z3,z4,z5,z6]),(0,[z247,z2,z3,z4,z21,z5,z6]),(0,[z490,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z491,z3,z4,z5,z6]),(0,[z1,z309,z2,z4,z20,z5,z6]),(0,[z492,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z493,z6]),(0,[z1,z83,z3,z4,z26,z5,z6]),(0,[z1,z2,z3,z4,z5,z494,z6]),(0,[z1,z495,z2,z3,z4,z5,z6]),(0,[z1,z496,z2,z3,z4,z5,z6]),(0,[z1,z2,z497,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z93,z5,z94])],[(0,[z1,z498,z2,z3,z4,z5,z6]),(0,[z499,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z500]),(0,[z1,z2,z387,z3,z4,z5,z6]),(0,[z1,z2,z501,z3,z4,z5,z6]),(0,[z502,z1,z2,z3,z4,z5,z6]),(0,[z1,z503,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z454,z4,z5,z6])],[(0,[z1,z2,z3,z4,z504,z5,z6]),(0,[z1,z2,z3,z4,z505,z5,z6]),(0,[z1,z2,z3,z4,z5,z42,z229]),(0,[z1,z2,z3,z4,z5,z56,z42]),(1,[z1,z141,z3,z4,z5,z45]),(1,[z1,z2,z19,z4,z5,z39]),(1,[z1,z2,z506,z4,z5,z6])],[(0,[z1,z2,z3,z4,z100,z5,z6]),(0,[z1,z2,z147,z4,z5,z24,z6]),(0,[z1,z103,z2,z4,z35,z5,z6]),(0,[z1,z135,z3,z4,z5,z6,z45]),(0,[z1,z2,z507,z3,z4,z5,z6])]],
   [[(1,[z1,z326,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z101]),(0,[z1,z2,z3,z4,z5,z6,z508]),(0,[z509,z1,z2,z3,z4,z5,z6])],[(0,[z1,z434,z2,z3,z4,z5,z6])],[(0,[z1,z510,z2,z3,z4,z5,z6]),(0,[z511,z1,z2,z3,z4,z5,z6])],[(0,[z269,z106,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z308,z44,z6]),(0,[z1,z2,z30,z3,z4,z5,z18]),(1,[z1,z219,z3,z4,z5,z6])],[(0,[z1,z2,z3,z122,z4,z5,z6]),(0,[z512,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z513,z4,z5,z6])],[(0,[z58,z1,z83,z3,z4,z5,z6]),(0,[z269,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z514,z6]),(0,[z1,z145,z3,z4,z5,z44,z6]),(0,[z176,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z515,z4,z5,z6]),(0,[z1,z2,z3,z4,z516,z5,z6]),(0,[z1,z517,z2,z3,z4,z5,z6])],[(0,[z1,z518,z2,z3,z4,z5,z6]),(0,[z1,z17,z2,z4,z5,z44,z6]),(0,[z1,z64,z2,z19,z4,z5,z6])]],
   [[(0,[z1,z2,z519,z3,z4,z5,z6]),(0,[z25,z1,z86,z3,z4,z5,z6]),(0,[z520,z1,z2,z3,z4,z5,z6])],[(0,[z158,z1,z2,z3,z4,z5,z6]),(1,[z1,z216,z3,z4,z5,z6]),(0,[z158,z1,z173,z2,z3,z5,z6]),(0,[z1,z2,z521,z3,z4,z5,z6])],[(0,[z1,z488,z2,z3,z4,z5,z6]),(0,[z1,z2,z522,z3,z4,z5,z6]),(0,[z1,z309,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z523])],[(0,[z1,z2,z3,z4,z524,z5,z6]),(0,[z1,z2,z19,z50,z4,z5,z6]),(1,[z1,z2,z3,z249,z5,z6]),(1,[z1,z2,z3,z4,z5,z78]),(0,[z1,z2,z3,z4,z5,z525,z6]),(0,[z1,z2,z526,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z527,z6]),(0,[z1,z2,z3,z4,z5,z528,z6]),(0,[z1,z529,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z73,z6])],[(0,[z530,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z531,z5,z6]),(0,[z1,z532,z2,z3,z4,z5,z6]),(0,[z533,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z534,z4,z5,z6]),(0,[z176,z1,z141,z2,z3,z4,z5])],[(0,[z25,z1,z59,z3,z4,z5,z6]),(0,[z247,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z535,z3,z4,z5,z6]),(0,[z1,z536,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z537,z6])],[(0,[z1,z2,z311,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z538,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z6,z539]),(0,[z1,z2,z3,z540,z4,z5,z6]),(0,[z1,z2,z3,z4,z541,z5,z6])],[(0,[z1,z83,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z542,z5,z6]),(0,[z543,z1,z2,z3,z4,z5,z6]),(0,[z1,z145,z2,z3,z4,z93,z5]),(0,[z1,z2,z3,z4,z5,z6,z544])],[(0,[z63,z1,z2,z3,z4,z21,z6]),(0,[z1,z145,z135,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z545])],[(0,[z1,z2,z3,z546,z4,z5,z6]),(0,[z1,z2,z3,z4,z547,z5,z6]),(0,[z1,z2,z548,z3,z4,z5,z6]),(0,[z1,z549,z2,z3,z4,z5,z6])],[(0,[z550,z1,z2,z3,z4,z5,z6]),(1,[z133,z2,z3,z4,z5,z101]),(0,[z1,z2,z3,z4,z5,z177,z220])],[(0,[z1,z2,z3,z50,z4,z5,z6]),(0,[z276,z114,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z551,z5,z6]),(0,[z1,z378,z3,z4,z5,z18,z6]),(1,[z1,z2,z454,z4,z5,z6]),(1,[z176,z1,z2,z3,z4,z220])],[(0,[z58,z1,z2,z3,z4,z5,z6]),(0,[z1,z552,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z87,z3,z4,z26,z5,z6]),(0,[z1,z2,z3,z75,z5,z48,z6])],[(0,[z1,z164,z2,z147,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z553]),(0,[z1,z2,z3,z4,z5,z554,z6])]],
   [[(0,[z1,z23,z2,z147,z4,z5,z6]),(0,[z1,z555,z2,z3,z4,z5,z6]),(0,[z556,z1,z2,z3,z4,z5,z6]),(0,[z557,z1,z2,z3,z4,z5,z6]),(0,[z558,z1,z2,z3,z4,z5,z6])],[(1,[z1,z2,z3,z4,z5,z95]),(0,[z1,z559,z2,z3,z4,z5,z6]),(0,[z1,z560,z2,z3,z4,z5,z6]),(1,[z1,z2,z139,z4,z5,z6])],[(1,[z1,z2,z373,z4,z5,z6]),(0,[z561,z1,z2,z3,z4,z5,z6]),(0,[z562,z1,z2,z3,z4,z5,z6]),(0,[z563,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z564,z6])],[(0,[z138,z1,z2,z3,z4,z5,z282]),(0,[z1,z2,z3,z4,z5,z78,z6]),(0,[z565,z1,z2,z3,z4,z5,z6]),(0,[z176,z1,z434,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z190,z220])],[(0,[z1,z2,z3,z4,z5,z566,z6]),(0,[z1,z86,z2,z3,z26,z5,z6]),(0,[z1,z2,z12,z4,z5,z6,z45]),(0,[z1,z2,z3,z4,z5,z6,z567])],[(0,[z1,z568,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z569,z6]),(0,[z570,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z571,z6]),(0,[z1,z2,z3,z4,z572,z5,z6])],[(0,[z1,z2,z3,z4,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z573,z6]),(0,[z1,z574,z2,z3,z4,z5,z6]),(0,[z1,z2,z575,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z6,z335]),(0,[z1,z2,z576,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z577,z5,z6]),(0,[z578,z1,z2,z3,z4,z5,z6]),(0,[z1,z579,z2,z3,z4,z5,z6])]],
   [[(0,[z580,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z4,z35,z5,z6])],[(0,[z581,z1,z2,z3,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z282]),(0,[z582,z1,z2,z3,z4,z5,z6]),(0,[z1,z103,z2,z3,z4,z5,z61]),(0,[z583,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z584,z3,z4,z5,z6])],[(0,[z1,z2,z585,z3,z4,z5,z6]),(0,[z138,z158,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z177,z6]),(0,[z1,z111,z2,z3,z4,z5,z229])],[(0,[z1,z2,z3,z4,z20,z5,z6]),(0,[z1,z2,z3,z4,z94,z6,z220])],[(0,[z1,z2,z3,z4,z586,z5,z6]),(0,[z587,z1,z2,z3,z4,z5,z6]),(0,[z114,z1,z309,z2,z4,z5,z6])],[(0,[z588,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z435,z5,z6]),(0,[z1,z2,z589,z3,z4,z5,z6]),(0,[z1,z2,z590,z3,z4,z5,z6]),(0,[z1,z591,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z5,z24]),(1,[z47,z2,z3,z4,z5,z6]),(0,[z1,z111,z2,z3,z4,z5,z6])],[(0,[z1,z2,z592,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z593]),(0,[z1,z2,z3,z4,z5,z6,z594]),(0,[z133,z1,z2,z3,z4,z5,z42]),(0,[z1,z2,z3,z4,z5,z6,z39])],[(0,[z595,z1,z2,z3,z4,z5,z6]),(0,[z596,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z597,z6]),(0,[z1,z2,z3,z4,z5,z598,z6])]],
   [[(0,[z83,z2,z59,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z599,z5,z6]),(0,[z77,z1,z104,z3,z4,z5,z6])],[(0,[z25,z1,z83,z3,z4,z5,z6]),(0,[z114,z1,z2,z50,z4,z5,z6]),(1,[z1,z23,z4,z288,z5,z6]),(0,[z77,z1,z23,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z600,z5,z6]),(0,[z1,z2,z3,z4,z5,z5,z6]),(0,[z1,z2,z3,z4,z601,z5,z6]),(0,[z1,z2,z3,z602,z4,z5,z6])],[(0,[z1,z2,z59,z3,z4,z5,z6]),(0,[z1,z603,z2,z3,z4,z5,z6]),(0,[z41,z2,z3,z4,z5,z42,z6]),(0,[z1,z604,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z605])],[(0,[z106,z1,z2,z50,z4,z5,z6]),(0,[z269,z2,z3,z122,z4,z5,z6]),(0,[z606,z1,z2,z3,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z5,z24])],[(0,[z1,z103,z2,z50,z4,z5,z6]),(0,[z158,z1,z2,z3,z75,z5,z6]),(0,[z1,z2,z373,z3,z4,z5,z6]),(0,[z77,z1,z2,z3,z4,z5,z6])],[(0,[z1,z23,z2,z104,z4,z5,z6]),(0,[z1,z3,z4,z5,z177,z6,z45]),(0,[z1,z2,z3,z4,z5,z607,z6]),(0,[z1,z2,z3,z4,z5,z6,z608])],[(0,[z1,z2,z3,z4,z5,z609,z6])]],
   [[(1,[z1,z2,z3,z4,z435,z6]),(0,[z158,z2,z3,z122,z4,z5,z6]),(1,[z1,z173,z2,z3,z48,z6])],[(0,[z138,z269,z2,z3,z4,z5,z6]),(1,[z1,z164,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z610,z6]),(0,[z1,z2,z611,z3,z4,z5,z6])],[(0,[z1,z2,z612,z3,z4,z5,z6]),(0,[z158,z1,z309,z2,z3,z5,z6]),(0,[z1,z2,z3,z90,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z613])],[(0,[z247,z1,z2,z3,z4,z22,z6]),(1,[z41,z2,z3,z4,z5,z42]),(0,[z1,z2,z3,z4,z614,z5,z6]),(0,[z1,z2,z49,z4,z35,z5,z6]),(0,[z1,z615,z2,z3,z4,z5,z6])],[(0,[z616,z1,z2,z3,z4,z5,z6]),(0,[z617,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z618,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z619,z6]),(0,[z1,z2,z3,z4,z5,z6,z620]),(0,[z1,z2,z3,z4,z621,z5,z6])],[(0,[z1,z2,z3,z4,z93,z5,z220])],[(0,[z1,z2,z3,z4,z5,z6,z622]),(0,[z1,z2,z3,z4,z623,z5,z6]),(1,[z1,z2,z30,z3,z4,z5]),(0,[z1,z2,z3,z4,z624,z5,z6])],[(0,[z1,z2,z625,z3,z4,z5,z6]),(0,[z1,z160,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z626,z5,z6]),(0,[z1,z2,z506,z3,z4,z5,z6])]],
   [[],[(0,[z1,z627,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z628,z6]),(0,[z1,z2,z3,z4,z5,z629,z6]),(0,[z1,z488,z2,z3,z5,z22,z6]),(0,[z1,z2,z630,z3,z4,z5,z6]),(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z631,z6])],[(0,[z1,z2,z3,z4,z5,z632,z6]),(0,[z1,z145,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z20,z5,z18,z6])],[(0,[z138,z2,z3,z4,z154,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z633]),(0,[z1,z2,z3,z634,z4,z5,z6])],[(0,[z1,z635,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z636,z5,z6]),(0,[z1,z2,z3,z4,z5,z637,z6])],[(0,[z1,z2,z280,z3,z4,z5,z6]),(0,[z638,z1,z2,z3,z4,z5,z6]),(0,[z1,z639,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z640,z5,z6]),(1,[z1,z145,z3,z4,z5,z177])],[(0,[z1,z641,z2,z3,z4,z5,z6]),(0,[z1,z326,z2,z3,z4,z5,z6]),(0,[z1,z23,z2,z4,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z151,z6]),(0,[z1,z2,z3,z642,z4,z5,z6])]],
   [[(0,[z176,z1,z125,z2,z3,z4,z5])],[(0,[z643,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z644,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z645,z6]),(0,[z276,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z3,z4,z93,z5]),(0,[z176,z1,z2,z3,z4,z93,z6])],[(0,[z646,z1,z2,z3,z4,z5,z6]),(0,[z647,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z26,z5,z6]),(0,[z1,z648,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z24,z156,z6]),(0,[z1,z2,z225,z3,z4,z5,z6])],[(1,[z269,z2,z147,z4,z5,z6]),(0,[z1,z2,z649,z3,z4,z5,z6]),(0,[z1,z2,z650,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z75,z5,z6]),(0,[z1,z2,z3,z4,z5,z651,z6]),(0,[z1,z2,z3,z4,z93,z5,z6])],[(0,[z1,z652,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z42,z6]),(0,[z653,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z654,z4,z5,z6]),(0,[z1,z2,z387,z3,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z156,z6]),(0,[z1,z2,z3,z655,z4,z5,z6])],[(1,[z114,z1,z309,z2,z5,z6]),(0,[z656,z1,z2,z3,z4,z5,z6])],[(0,[z657,z1,z2,z3,z4,z5,z6])],[]],
   [[(0,[z1,z658,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z659,z5,z6]),(0,[z1,z23,z3,z4,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z340]),(0,[z114,z1,z2,z49,z4,z5,z6]),(0,[z1,z125,z2,z3,z4,z93,z5])],[(0,[z1,z2,z3,z4,z5,z660,z6]),(0,[z1,z2,z3,z4,z5,z661,z6]),(0,[z1,z145,z3,z4,z5,z177,z6]),(0,[z1,z64,z2,z3,z4,z35,z6]),(0,[z1,z2,z3,z662,z4,z5,z6])],[(0,[z1,z2,z663,z3,z4,z5,z6]),(0,[z1,z2,z3,z664,z4,z5,z6]),(0,[z1,z665,z2,z3,z4,z5,z6])],[(0,[z1,z2,z666,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z667,z6])],[(0,[z668,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z669,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z670]),(0,[z1,z2,z3,z4,z5,z56,z101]),(0,[z1,z2,z3,z4,z671,z5,z6]),(1,[z1,z378,z3,z4,z5,z6]),(1,[z1,z125,z2,z4,z5,z24])],[(0,[z1,z2,z672,z3,z4,z5,z6]),(0,[z1,z2,z3,z673,z4,z5,z6]),(0,[z1,z2,z3,z278,z4,z5,z6]),(0,[z1,z173,z2,z506,z4,z5,z6])],[(0,[z1,z2,z3,z674,z4,z5,z6]),(1,[z1,z2,z460,z4,z5,z6]),(0,[z1,z23,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z675,z5,z6])],[(0,[z82,z1,z59,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z676,z5,z6]),(1,[z138,z2,z3,z154,z5,z6]),(0,[z1,z2,z3,z4,z5,z22,z6]),(0,[z677,z1,z2,z3,z4,z5,z6]),(0,[z1,z678,z2,z3,z4,z5,z6]),(0,[z1,z3,z4,z136,z5,z44,z6]),(0,[z1,z2,z3,z4,z5,z679,z6])]],
   [[(0,[z680,z1,z2,z3,z4,z5,z6]),(0,[z158,z1,z2,z3,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z681]),(1,[z1,z159,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z682,z5,z6])],[(0,[z683,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z684,z6]),(0,[z1,z685,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z686,z6])],[(0,[z1,z2,z104,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z687,z5,z6]),(0,[z1,z2,z3,z4,z5,z688,z6]),(0,[z1,z2,z3,z4,z689,z5,z6]),(0,[z1,z2,z690,z3,z4,z5,z6]),(0,[z1,z691,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z94,z6])],[(0,[z692,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z693,z3,z4,z5,z6]),(0,[z1,z694,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z469,z6])],[(0,[z1,z2,z3,z695,z4,z5,z6]),(0,[z1,z696,z2,z3,z4,z5,z6]),(0,[z1,z2,z697,z3,z4,z5,z6]),(0,[z1,z2,z3,z5,z56,z6,z229])],[(0,[z1,z59,z3,z4,z26,z5,z6]),(0,[z77,z1,z2,z3,z4,z94,z6]),(0,[z1,z2,z3,z4,z5,z308,z6]),(0,[z1,z2,z698,z3,z4,z5,z6]),(0,[z1,z2,z699,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z700,z5,z6]),(0,[z158,z1,z2,z3,z122,z5,z6]),(0,[z1,z2,z3,z4,z5,z701,z6])],[(0,[z1,z2,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z702]),(0,[z703,z1,z2,z3,z4,z5,z6]),(0,[z176,z1,z135,z2,z3,z4,z6]),(0,[z1,z141,z3,z4,z136,z5,z6]),(0,[z1,z2,z3,z4,z5,z704,z6]),(0,[z1,z705,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z135,z3,z4,z136,z6]),(0,[z54,z1,z2,z19,z3,z4]),(0,[z1,z2,z3,z5,z707,z6])],[(0,[z1,z708,z3,z4,z5,z6])],[(0,[z1,z2,z709,z4,z5,z6]),(0,[z1,z2,z4,z5,z6,z710]),(0,[z711,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z712,z6]),(1,[z1,z2,z4,z713,z6]),(0,[z1,z714,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z715])],[(0,[z1,z2,z716,z3,z5,z6]),(0,[z482,z2,z50,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z717]),(0,[z1,z2,z718,z4,z5,z6]),(0,[z1,z719,z2,z4,z5,z6]),(0,[z720,z2,z3,z4,z5,z6]),(0,[z176,z1,z3,z4,z153,z220])],[(0,[z1,z2,z721,z4,z5,z6]),(0,[z1,z103,z672,z4,z5,z6]),(0,[z1,z2,z3,z4,z93,z554]),(1,[z176,z1,z219,z3,z4])],[(0,[z82,z83,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z722,z6]),(0,[z1,z87,z723,z3,z5,z6]),(0,[z1,z3,z4,z5,z6,z724])],[(0,[z1,z2,z3,z4,z5,z725]),(0,[z2,z3,z4,z5,z42,z726]),(0,[z54,z1,z145,z2,z3,z4]),(0,[z1,z202,z4,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z727])],[(0,[z106,z2,z728,z4,z5,z6])]],
   [[(0,[z1,z103,z4,z5,z156,z6]),(0,[z176,z1,z219,z2,z3,z4])],[(0,[z1,z3,z4,z5,z729,z6]),(0,[z1,z2,z19,z4,z5,z53]),(0,[z1,z2,z3,z4,z5,z730]),(0,[z1,z125,z131,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z731]),(0,[z77,z1,z3,z4,z243,z6]),(0,[z1,z125,z2,z4,z5,z73])],[(0,[z1,z2,z3,z4,z5,z732]),(0,[z1,z3,z4,z5,z733,z6]),(0,[z734,z1,z2,z3,z5,z6])],[(0,[z58,z735,z3,z4,z5,z6]),(0,[z1,z736,z3,z4,z5,z6]),(0,[z54,z1,z125,z2,z3,z4])],[(0,[z580,z2,z147,z4,z5,z6]),(1,[z2,z3,z737,z5,z6]),(0,[z1,z3,z4,z738,z44,z6]),(0,[z1,z219,z3,z4,z5,z45]),(0,[z739,z2,z3,z4,z5,z6]),(0,[z740,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z90,z707,z6]),(0,[z1,z2,z3,z4,z741,z220])],[]],
   [[(0,[z1,z2,z3,z4,z5,z742]),(0,[z114,z1,z2,z207,z5,z6]),(0,[z1,z2,z743,z4,z5,z6])],[(1,[z735,z3,z4,z5,z6]),(0,[z744,z2,z3,z4,z5,z6]),(0,[z1,z329,z2,z19,z4,z5])],[(0,[z1,z2,z745,z4,z5,z6]),(0,[z138,z2,z165,z154,z5,z6]),(0,[z1,z746,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z747]),(0,[z176,z1,z2,z225,z4,z220])],[(0,[z1,z748,z2,z3,z4,z6]),(0,[z1,z2,z100,z5,z18,z6]),(0,[z1,z2,z749,z3,z5,z6]),(1,[z1,z3,z4,z738,z6]),(0,[z176,z1,z131,z3,z4,z220])],[(0,[z1,z750,z3,z4,z5,z6]),(0,[z114,z1,z309,z2,z5,z6])],[(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z2,z752,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z753]),(0,[z1,z2,z3,z4,z94,z52]),(0,[z1,z2,z4,z5,z6,z754])],[(0,[z1,z2,z3,z755,z5,z6]),(0,[z1,z2,z3,z4,z5,z756])],[(0,[z1,z23,z2,z100,z5,z6]),(0,[z1,z2,z757,z4,z5,z6]),(0,[z758,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z707,z48,z6])]],
   [[(0,[z1,z326,z3,z4,z5,z95]),(0,[z1,z3,z4,z5,z6,z759]),(0,[z1,z125,z4,z5,z24,z156]),(0,[z47,z2,z3,z75,z5,z6])],[(0,[z2,z165,z50,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z760]),(0,[z509,z2,z3,z4,z5,z42]),(0,[z1,z103,z104,z4,z5,z6]),(0,[z1,z2,z3,z75,z707,z6])],[],[(0,[z1,z2,z761,z4,z5,z6]),(0,[z1,z2,z3,z737,z5,z6]),(0,[z1,z111,z2,z139,z5,z56])],[(0,[z82,z735,z3,z4,z5,z6])],[(0,[z58,z59,z3,z4,z5,z6]),(0,[z520,z83,z3,z4,z5,z6]),(0,[z1,z4,z5,z73,z156,z6]),(0,[z1,z762,z3,z4,z5,z6])],[],[(0,[z1,z735,z3,z4,z5,z6]),(0,[z1,z2,z3,z763,z5,z6]),(0,[z1,z159,z2,z4,z5,z6]),(0,[z1,z23,z497,z4,z5,z6]),(0,[z1,z764,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z24,z368])]],
   [[(0,[z1,z326,z3,z4,z5,z282]),(0,[z1,z219,z3,z4,z5,z52]),(0,[z1,z2,z3,z4,z738,z6]),(0,[z1,z135,z131,z3,z4,z6]),(0,[z211,z2,z49,z4,z5,z6]),(0,[z1,z765,z3,z4,z5,z6])],[(0,[z1,z216,z3,z4,z5,z95]),(0,[z138,z396,z2,z3,z5,z6]),(0,[z1,z103,z766,z4,z5,z6]),(0,[z77,z1,z3,z4,z44,z52])],[(0,[z1,z2,z3,z4,z5,z767]),(0,[z1,z2,z30,z50,z4,z5]),(0,[z1,z202,z147,z4,z5,z6]),(0,[z1,z723,z3,z4,z5,z6])],[(0,[z1,z2,z768,z4,z5,z6]),(0,[z158,z2,z3,z671,z5,z6]),(0,[z1,z488,z2,z769,z5,z6])],[(0,[z1,z2,z3,z4,z6,z770]),(0,[z25,z1,z159,z87,z5,z6]),(0,[z1,z2,z225,z4,z93,z5])],[(0,[z41,z2,z102,z4,z5,z42]),(0,[z1,z262,z3,z4,z5,z45]),(0,[z1,z2,z4,z713,z18,z6]),(0,[z1,z3,z4,z5,z771,z6])],[(0,[z63,z2,z3,z249,z22,z6]),(0,[z1,z2,z772,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z773]),(0,[z1,z2,z774,z4,z5,z6]),(0,[z1,z2,z74,z3,z5,z775])],[(0,[z158,z2,z3,z682,z5,z6]),(0,[z1,z2,z441,z3,z5,z229]),(0,[z1,z23,z4,z5,z156,z6]),(0,[z54,z1,z3,z4,z44,z6]),(0,[z1,z3,z4,z5,z469,z151])]],
   [[(0,[z1,z776,z3,z4,z5,z6]),(0,[z1,z2,z12,z4,z5,z6])],[(0,[z277,z2,z147,z4,z5,z6]),(0,[z1,z216,z3,z4,z5,z282]),(0,[z54,z1,z23,z3,z4,z6])],[(0,[z1,z488,z2,z3,z48,z6]),(0,[z777,z2,z3,z4,z5,z6])],[(0,[z1,z104,z3,z4,z5,z52]),(0,[z77,z1,z17,z4,z44,z6])],[(0,[z1,z23,z3,z4,z5,z52]),(0,[z1,z778,z2,z4,z5,z6])],[(0,[z1,z2,z779,z4,z5,z6]),(0,[z1,z2,z3,z5,z56,z775])],[(0,[z1,z2,z4,z5,z780,z6]),(0,[z1,z488,z2,z3,z210,z6]),(0,[z2,z3,z4,z5,z726,z101]),(0,[z1,z2,z3,z4,z94,z344]),(0,[z1,z2,z781,z4,z5,z6]),(0,[z1,z782,z2,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z783]),(0,[z1,z2,z784,z4,z5,z6]),(0,[z1,z141,z3,z4,z223,z5]),(0,[z1,z785,z2,z4,z5,z6])]],
   [[(0,[z1,z786,z3,z4,z5,z6]),(0,[z490,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z787,z5,z6]),(0,[z77,z1,z160,z3,z4,z6]),(0,[z1,z2,z180,z20,z5,z6]),(0,[z1,z2,z3,z4,z713,z6]),(0,[z1,z788,z3,z4,z5,z6])],[(0,[z1,z2,z789,z4,z5,z6]),(0,[z1,z2,z3,z4,z790,z6]),(0,[z1,z172,z2,z3,z5,z56]),(0,[z1,z104,z4,z5,z73,z6]),(0,[z54,z1,z2,z3,z4,z6]),(0,[z1,z30,z3,z4,z5,z151])],[(0,[z1,z2,z3,z791,z5,z6]),(0,[z1,z792,z3,z4,z5,z6]),(0,[z138,z2,z3,z436,z5,z6]),(0,[z1,z23,z4,z5,z73,z6]),(0,[z1,z2,z3,z4,z6,z793]),(0,[z1,z29,z2,z4,z18,z6])],[(0,[z82,z83,z280,z4,z5,z6]),(0,[z1,z164,z2,z20,z5,z6]),(0,[z2,z3,z4,z794,z22,z6]),(0,[z1,z23,z534,z4,z5,z6]),(0,[z1,z2,z795,z4,z5,z6]),(0,[z1,z796,z2,z4,z5,z6]),(0,[z1,z3,z4,z5,z797,z6]),(0,[z1,z798,z3,z4,z5,z6])],[(0,[z1,z2,z799,z4,z5,z6]),(0,[z276,z2,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z24,z773])],[(0,[z1,z2,z3,z800,z5,z6]),(0,[z1,z145,z3,z4,z5,z661]),(0,[z1,z2,z4,z5,z73,z6]),(0,[z114,z1,z202,z4,z5,z6]),(0,[z801,z2,z3,z4,z5,z6])],[(0,[z63,z2,z3,z4,z794,z6]),(1,[z1,z766,z4,z5,z6]),(0,[z1,z23,z19,z4,z5,z45])]],
   [[(0,[z1,z2,z802,z4,z5,z6])],[(0,[z138,z70,z2,z3,z5,z6])],[(0,[z1,z2,z803,z4,z5,z6]),(0,[z1,z804,z2,z3,z5,z6]),(0,[z1,z2,z4,z5,z805,z6]),(0,[z1,z19,z3,z4,z5,z156])],[(0,[z1,z103,z2,z100,z5,z6]),(0,[z1,z2,z806,z4,z5,z6]),(0,[z1,z2,z3,z807,z5,z6]),(0,[z1,z2,z808,z4,z5,z6])],[(0,[z1,z2,z3,z100,z5,z6]),(0,[z1,z2,z100,z5,z24,z6]),(0,[z133,z2,z3,z4,z5,z726]),(0,[z1,z64,z2,z4,z18,z6])],[(0,[z1,z2,z311,z4,z5,z6]),(0,[z1,z809,z3,z4,z5,z6]),(0,[z1,z2,z810,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z811]),(0,[z25,z1,z87,z43,z5,z6]),(0,[z1,z135,z3,z4,z150,z6])],[(0,[z1,z2,z3,z812,z5,z6]),(0,[z1,z23,z576,z4,z5,z6]),(0,[z1,z813,z3,z4,z5,z6])],[(0,[z1,z2,z3,z814,z5,z6]),(0,[z1,z815,z3,z4,z5,z6]),(0,[z1,z816,z3,z4,z5,z6]),(0,[z1,z2,z817,z4,z5,z6]),(0,[z1,z86,z723,z3,z5,z6]),(0,[z1,z17,z2,z4,z5,z57])]],
   [[(0,[z1,z2,z818,z4,z5,z6]),(0,[z1,z23,z766,z4,z5,z6]),(0,[z1,z378,z3,z4,z5,z469])],[(0,[z276,z2,z147,z4,z5,z6]),(0,[z1,z2,z3,z4,z819,z6]),(0,[z1,z2,z19,z4,z462,z5])],[(0,[z1,z820,z2,z3,z4,z5]),(0,[z353,z2,z50,z4,z5,z6]),(0,[z1,z17,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z821]),(0,[z1,z2,z3,z4,z822,z6]),(0,[z1,z131,z3,z4,z5,z6]),(0,[z54,z1,z2,z12,z4,z6]),(0,[z1,z2,z823,z4,z5,z6]),(0,[z1,z111,z2,z454,z5,z56])],[(0,[z158,z2,z3,z122,z5,z6]),(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z2,z825,z3,z4,z5]),(0,[z826,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z93,z741])],[(0,[z1,z2,z3,z4,z827,z6]),(0,[z1,z828,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z726,z6]),(0,[z1,z2,z766,z4,z5,z6]),(0,[z1,z3,z4,z5,z151,z6])],[(0,[z1,z2,z3,z4,z6,z829]),(0,[z1,z3,z4,z5,z830,z6]),(0,[z1,z723,z3,z26,z5,z6])],[(0,[z1,z2,z831,z4,z5,z6]),(0,[z832,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z833,z6])],[(0,[z1,z2,z43,z4,z5,z6]),(0,[z1,z245,z3,z4,z5,z45]),(0,[z211,z2,z4,z5,z18,z6])]],
   [[(0,[z163,z2,z3,z122,z5,z6]),(0,[z1,z2,z3,z4,z435,z95]),(0,[z1,z145,z3,z4,z5,z747]),(0,[z1,z2,z49,z4,z621,z6])],[(0,[z2,z728,z3,z4,z5,z6]),(0,[z1,z834,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z156,z6]),(0,[z1,z2,z835,z4,z5,z6]),(0,[z836,z1,z3,z4,z5,z6])],[(0,[z1,z160,z2,z3,z4,z5]),(0,[z1,z378,z4,z35,z5,z6]),(0,[z1,z837,z3,z4,z5,z6]),(1,[z1,z2,z3,z5,z775])],[(0,[z1,z103,z104,z4,z5,z340]),(0,[z1,z2,z838,z3,z4,z5]),(0,[z1,z225,z4,z5,z6,z153])],[(0,[z1,z2,z3,z4,z839,z6]),(0,[z1,z840,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z210,z95]),(0,[z1,z2,z841,z4,z5,z6]),(0,[z1,z2,z842,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z843]),(0,[z247,z2,z3,z4,z794,z6]),(0,[z1,z86,z3,z26,z5,z6]),(0,[z77,z1,z3,z4,z44,z6]),(0,[z844,z2,z3,z4,z5,z6])],[(0,[z138,z326,z3,z154,z5,z6]),(0,[z1,z2,z225,z4,z5,z6])],[(0,[z77,z1,z4,z308,z44,z6]),(0,[z77,z1,z3,z4,z57,z44]),(0,[z1,z145,z131,z3,z4,z5]),(0,[z1,z64,z2,z4,z110,z6])]],
   [[(0,[z1,z2,z165,z4,z5,z6]),(0,[z138,z2,z50,z20,z5,z6]),(0,[z1,z845,z2,z3,z5,z6]),(0,[z1,z2,z846,z4,z5,z6]),(0,[z1,z2,z3,z4,z435,z282]),(0,[z2,z3,z4,z5,z847,z6])],[(0,[z1,z103,z4,z5,z206,z6]),(0,[z1,z2,z3,z4,z5,z848]),(0,[z1,z2,z3,z4,z93,z94])],[],[(0,[z83,z735,z3,z4,z5,z6]),(0,[z176,z1,z219,z3,z4,z220])],[(0,[z1,z2,z3,z849,z4,z6]),(0,[z1,z2,z3,z4,z210,z282]),(0,[z47,z173,z2,z3,z48,z6])],[(0,[z1,z2,z3,z4,z5,z850])],[(0,[z1,z2,z3,z851,z5,z6]),(0,[z1,z2,z4,z35,z315,z6]),(0,[z1,z141,z12,z4,z5,z45]),(0,[z1,z64,z2,z30,z4,z5]),(0,[z1,z173,z2,z278,z48,z6])],[(0,[z1,z2,z852,z4,z5,z6]),(0,[z138,z216,z3,z154,z5,z6])]],
   [[(0,[z47,z2,z3,z4,z210,z6]),(0,[z1,z2,z4,z5,z853,z6]),(0,[z1,z202,z3,z4,z5,z6]),(0,[z25,z1,z87,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z854])],[(0,[z1,z2,z855,z4,z5,z6]),(0,[z1,z104,z4,z5,z619,z6]),(0,[z1,z2,z3,z4,z856,z6]),(0,[z1,z2,z3,z4,z5,z57])],[(0,[z1,z3,z4,z5,z857,z6]),(0,[z176,z1,z2,z3,z4,z741])],[(0,[z1,z2,z858,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z859]),(0,[z1,z766,z3,z4,z5,z6]),(0,[z1,z3,z4,z136,z609,z6]),(0,[z1,z2,z3,z4,z5,z860]),(0,[z114,z1,z2,z30,z4,z5]),(0,[z1,z2,z861,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z862,z4,z5,z6]),(0,[z1,z2,z4,z5,z863,z6]),(0,[z1,z2,z4,z73,z6,z335]),(0,[z1,z271,z2,z4,z5,z24])],[(0,[z2,z3,z4,z737,z5,z6]),(0,[z2,z3,z4,z5,z794,z6]),(0,[z77,z1,z3,z4,z738,z6]),(0,[z276,z309,z2,z3,z5,z6])],[(0,[z1,z3,z4,z5,z864,z6])],[(0,[z1,z603,z2,z4,z18,z6]),(0,[z1,z865,z3,z4,z5,z6]),(0,[z1,z164,z2,z165,z5,z6]),(0,[z138,z2,z3,z75,z21,z6])]],
   [[(0,[z2,z3,z122,z5,z494,z6]),(0,[z470,z2,z3,z4,z21,z6]),(0,[z1,z2,z866,z3,z4,z5]),(0,[z211,z103,z2,z4,z5,z6])],[(0,[z211,z2,z3,z4,z5,z6]),(0,[z1,z2,z19,z4,z5,z500]),(0,[z176,z1,z219,z3,z4,z6])],[(0,[z1,z2,z4,z35,z5,z61]),(0,[z1,z64,z2,z30,z4,z18])],[(0,[z1,z145,z17,z4,z5,z6]),(0,[z1,z3,z4,z5,z867,z6])],[(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z2,z869,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z870]),(1,[z1,z723,z3,z5,z6]),(0,[z1,z3,z4,z5,z418,z45]),(0,[z1,z141,z4,z5,z73,z45]),(0,[z1,z3,z4,z5,z871,z6])],[(0,[z1,z2,z872,z4,z5,z6]),(0,[z1,z219,z3,z4,z93,z5])],[(0,[z269,z164,z2,z3,z5,z6]),(0,[z873,z1,z2,z4,z5,z6]),(0,[z1,z2,z19,z4,z5,z73]),(0,[z1,z64,z4,z151,z18,z6])],[(0,[z1,z2,z874,z3,z5,z6]),(0,[z138,z2,z3,z154,z5,z95]),(0,[z1,z2,z875,z4,z5,z6])]],
   [[(0,[z1,z2,z4,z5,z73,z340]),(0,[z1,z2,z876,z4,z5,z6]),(0,[z1,z2,z877,z4,z5,z6]),(0,[z1,z202,z125,z4,z5,z24])],[(0,[z1,z878,z2,z3,z4,z5])],[(0,[z1,z879,z3,z4,z5,z6]),(0,[z1,z2,z880,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z881])],[(0,[z562,z59,z3,z4,z5,z6]),(0,[z1,z2,z186,z4,z5,z6]),(0,[z276,z2,z165,z4,z5,z6]),(0,[z138,z2,z3,z737,z5,z6]),(0,[z247,z2,z3,z4,z21,z6]),(0,[z1,z2,z882,z4,z5,z6]),(0,[z54,z1,z3,z4,z177,z6]),(0,[z1,z2,z4,z5,z6,z190]),(0,[z1,z2,z3,z90,z75,z6])],[(0,[z1,z2,z883,z4,z5,z6]),(0,[z1,z2,z884,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z885]),(1,[z77,z1,z160,z3,z4])],[(0,[z1,z2,z3,z886,z5,z6])],[(0,[z1,z2,z887,z4,z5,z6]),(0,[z1,z2,z3,z4,z888,z6]),(0,[z1,z2,z3,z4,z5,z889]),(0,[z1,z890,z3,z4,z5,z6])],[(0,[z269,z2,z728,z4,z5,z6]),(0,[z138,z2,z3,z154,z5,z282]),(0,[z1,z23,z662,z4,z5,z6]),(0,[z1,z173,z2,z506,z48,z6])]],
   [[(0,[z1,z2,z3,z346,z75,z6]),(0,[z1,z160,z3,z4,z5,z45]),(0,[z1,z2,z19,z4,z5,z365]),(0,[z1,z309,z778,z2,z5,z6]),(0,[z2,z3,z4,z5,z891,z6])],[(0,[z138,z1,z2,z278,z5,z6]),(0,[z1,z2,z723,z3,z5,z6])],[(0,[z1,z2,z4,z35,z6,z380])],[(0,[z1,z892,z2,z3,z4,z6]),(0,[z1,z434,z3,z4,z5,z6]),(0,[z1,z778,z2,z20,z5,z6])],[(0,[z1,z2,z3,z4,z893,z6]),(0,[z1,z2,z894,z4,z5,z6]),(0,[z1,z2,z895,z4,z5,z6]),(0,[z1,z896,z2,z4,z5,z6])],[(0,[z1,z2,z897,z4,z5,z6]),(1,[z1,z2,z3,z4,z741])],[(0,[z1,z898,z3,z4,z5,z6])],[(0,[z735,z59,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z279,z6]),(0,[z488,z2,z3,z21,z5,z6]),(0,[z77,z1,z17,z4,z5,z6]),(0,[z1,z2,z899,z4,z5,z6]),(0,[z1,z2,z12,z4,z6,z335]),(0,[z54,z1,z2,z4,z73,z6]),(0,[z1,z2,z278,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z378,z50,z4,z5,z6]),(0,[z1,z23,z4,z687,z5,z6]),(0,[z1,z2,z3,z4,z5,z901]),(0,[z902,z2,z3,z4,z5,z6])],[(0,[z1,z2,z430,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z903])],[(0,[z1,z2,z3,z4,z5,z904])],[(0,[z276,z2,z3,z20,z5,z6]),(0,[z1,z905,z3,z4,z5,z6])],[(0,[z1,z2,z4,z5,z308,z57]),(0,[z176,z1,z496,z2,z3,z4])],[(0,[z1,z2,z233,z4,z5,z6]),(0,[z1,z2,z906,z4,z5,z6]),(0,[z1,z2,z3,z907,z5,z6])],[(0,[z138,z2,z3,z154,z435,z6]),(0,[z1,z2,z3,z5,z6,z908]),(0,[z1,z3,z4,z5,z6,z153])],[(0,[z502,z2,z50,z4,z5,z6]),(0,[z1,z909,z3,z4,z5,z6]),(0,[z1,z2,z910,z3,z5,z6]),(0,[z211,z23,z2,z4,z5,z6]),(0,[z1,z2,z4,z5,z308,z6])]],
   [[(0,[z1,z2,z4,z5,z911,z6]),(0,[z1,z2,z912,z4,z5,z6]),(0,[z1,z2,z913,z4,z5,z52]),(0,[z1,z145,z3,z4,z5,z706])],[(0,[z1,z157,z2,z4,z5,z24]),(0,[z1,z914,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z915,z6]),(0,[z1,z378,z30,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z469]),(0,[z47,z2,z916,z4,z5,z6]),(0,[z1,z2,z917,z4,z5,z6])],[(0,[z1,z2,z3,z918,z5,z6]),(0,[z138,z2,z3,z154,z210,z6]),(0,[z1,z104,z766,z4,z5,z6]),(0,[z1,z17,z4,z5,z6,z45]),(0,[z176,z1,z2,z3,z4,z418])],[(0,[z82,z83,z460,z4,z5,z6]),(0,[z47,z2,z3,z4,z21,z6]),(0,[z1,z80,z23,z4,z5,z6]),(0,[z176,z1,z2,z3,z4,z52]),(0,[z176,z1,z2,z3,z4,z110])],[(0,[z1,z919,z2,z4,z5,z6])],[(0,[z1,z2,z920,z4,z5,z6]),(0,[z2,z3,z122,z737,z5,z6]),(0,[z1,z2,z921,z4,z5,z6])],[(0,[z1,z658,z3,z26,z5,z6]),(0,[z1,z23,z46,z4,z5,z6])],[(0,[z922,z1,z2,z3,z4,z6]),(0,[z1,z488,z2,z3,z5,z6]),(0,[z1,z2,z3,z4,z5,z923]),(0,[z1,z2,z4,z5,z6,z924]),(0,[z1,z2,z19,z4,z5,z773])]],
   [[(0,[z2,z3,z4,z21,z79,z6]),(0,[z1,z3,z4,z5,z177,z620])],[(0,[z1,z925,z3,z4,z5,z6]),(0,[z1,z104,z3,z4,z5,z340])],[(0,[z1,z2,z280,z4,z5,z6]),(0,[z138,z2,z233,z4,z5,z6]),(0,[z1,z23,z3,z4,z5,z340]),(0,[z1,z141,z3,z4,z5,z45]),(0,[z1,z2,z506,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z926]),(0,[z2,z3,z4,z5,z927,z6])],[(0,[z1,z326,z3,z4,z5,z6]),(0,[z1,z928,z2,z4,z5,z6])],[(0,[z77,z1,z3,z4,z177,z94])],[(0,[z1,z2,z3,z4,z5,z340]),(0,[z1,z2,z3,z4,z297,z94])],[(0,[z1,z2,z3,z4,z929,z6]),(0,[z1,z219,z3,z4,z5,z6]),(0,[z1,z2,z930,z4,z5,z6]),(0,[z1,z145,z3,z4,z5,z36])]],
   [[(0,[z1,z2,z50,z4,z5,z61]),(0,[z1,z931,z2,z4,z5,z6]),(0,[z932,z2,z3,z4,z5,z6]),(0,[z1,z2,z933,z4,z5,z6])],[(0,[z1,z2,z934,z4,z5,z6]),(1,[z2,z3,z4,z5,z726]),(0,[z1,z2,z3,z4,z5,z935]),(0,[z1,z936,z3,z4,z5,z6]),(0,[z1,z2,z937,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z938])],[(0,[z1,z939,z3,z4,z5,z6]),(0,[z1,z2,z940,z4,z5,z6]),(0,[z941,z2,z3,z4,z5,z6]),(0,[z1,z2,z479,z20,z5,z6]),(0,[z77,z1,z3,z4,z418,z6]),(0,[z1,z2,z225,z4,z5,z177])],[(0,[z1,z2,z942,z4,z5,z6]),(0,[z1,z2,z3,z943,z5,z6])],[(0,[z1,z216,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z944,z6]),(0,[z1,z945,z3,z4,z5,z6]),(0,[z1,z2,z74,z3,z5,z229]),(0,[z1,z2,z3,z5,z775,z229])],[(0,[z1,z2,z946,z4,z5,z6]),(0,[z1,z135,z3,z4,z94,z45])],[(0,[z1,z2,z165,z20,z5,z6]),(0,[z1,z2,z3,z4,z5,z78]),(0,[z1,z64,z2,z4,z469,z18])]],
   [[(0,[z1,z2,z3,z4,z947,z6]),(0,[z1,z3,z4,z5,z747,z45]),(0,[z54,z1,z141,z3,z4,z6]),(1,[z1,z2,z3,z707,z6]),(0,[z1,z2,z3,z5,z775,z6])],[(0,[z2,z735,z3,z4,z5,z6]),(0,[z1,z948,z2,z3,z4,z5]),(0,[z1,z2,z49,z4,z504,z6])],[(0,[z1,z2,z949,z4,z5,z6]),(0,[z1,z2,z950,z4,z5,z6])],[(0,[z1,z326,z186,z4,z5,z6]),(0,[z1,z64,z378,z4,z5,z6])],[(0,[z1,z2,z951,z4,z5,z6]),(0,[z1,z160,z3,z4,z136,z5]),(0,[z1,z2,z4,z5,z952,z6])],[(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z19,z100,z5,z6]),(0,[z1,z2,z4,z5,z24,z340]),(0,[z954,z2,z3,z4,z5,z6])],[(0,[z1,z219,z4,z5,z6,z190])],[(0,[z1,z2,z3,z4,z5,z726]),(0,[z1,z64,z2,z4,z5,z61])]],
   [[(0,[z41,z2,z311,z4,z5,z42]),(0,[z1,z2,z3,z4,z5,z955])],[(0,[z1,z956,z3,z4,z5,z6]),(0,[z269,z164,z2,z147,z5,z6]),(0,[z47,z2,z842,z4,z5,z6]),(0,[z1,z785,z131,z4,z5,z6]),(0,[z176,z1,z2,z3,z4,z220])],[(0,[z1,z2,z4,z35,z713,z6])],[(0,[z54,z1,z131,z3,z4,z6]),(0,[z114,z1,z289,z2,z5,z6])],[(0,[z1,z2,z3,z4,z957,z6]),(0,[z1,z2,z3,z4,z958,z6]),(0,[z1,z216,z186,z4,z5,z6]),(0,[z1,z2,z959,z4,z5,z6]),(0,[z1,z960,z3,z4,z5,z6]),(0,[z1,z2,z961,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z962]),(0,[z1,z2,z3,z4,z5,z95]),(0,[z114,z1,z2,z522,z5,z6])],[(0,[z1,z2,z373,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z963]),(0,[z138,z115,z2,z3,z5,z6])],[(0,[z1,z2,z964,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z775])]],
   [[(0,[z1,z965,z3,z4,z5,z6]),(0,[z63,z2,z3,z4,z22,z6]),(0,[z1,z2,z387,z20,z5,z6])],[(0,[z1,z2,z966,z4,z5,z6]),(0,[z1,z967,z3,z4,z5,z6]),(0,[z41,z2,z3,z4,z5,z726])],[(0,[z1,z2,z4,z5,z773,z6])],[(0,[z1,z2,z968,z3,z5,z6]),(0,[z2,z3,z4,z5,z969,z6]),(0,[z1,z2,z970,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z335]),(0,[z176,z1,z145,z135,z3,z4]),(0,[z276,z114,z309,z2,z5,z6])],[(0,[z1,z2,z3,z4,z5,z971]),(0,[z561,z2,z50,z4,z5,z6]),(0,[z1,z2,z913,z4,z5,z6]),(0,[z972,z2,z3,z4,z5,z6]),(0,[z1,z2,z49,z4,z713,z6])],[(0,[z2,z3,z4,z21,z210,z6]),(0,[z973,z2,z3,z4,z5,z6]),(0,[z77,z1,z160,z3,z4,z44])],[(0,[z1,z2,z3,z5,z974,z6]),(0,[z1,z2,z3,z4,z5,z975])],[(0,[z1,z976,z3,z4,z5,z6]),(0,[z269,z2,z147,z100,z5,z6]),(0,[z1,z141,z3,z4,z335,z45]),(0,[z1,z2,z977,z4,z5,z6])]],
   [[(0,[z978,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z6,z741])],[(0,[z1,z2,z979,z3,z4,z5])],[(0,[z1,z2,z980,z4,z5,z6]),(0,[z1,z2,z981,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z982]),(0,[z138,z503,z2,z3,z5,z6]),(0,[z1,z2,z4,z5,z983,z6]),(0,[z1,z224,z3,z4,z5,z177]),(0,[z211,z2,z4,z5,z24,z6])],[(0,[z1,z2,z3,z4,z5,z984]),(0,[z1,z2,z3,z4,z5,z985]),(0,[z1,z2,z3,z986,z5,z6]),(0,[z1,z2,z186,z4,z5,z95]),(0,[z1,z2,z3,z987,z5,z6]),(0,[z1,z2,z3,z4,z988,z6]),(0,[z1,z135,z3,z4,z738,z6]),(0,[z1,z2,z3,z989,z5,z6])],[(0,[z1,z23,z4,z288,z5,z6])],[(0,[z1,z778,z2,z387,z5,z6])],[(0,[z1,z2,z377,z20,z5,z6]),(0,[z138,z2,z3,z600,z5,z6]),(0,[z1,z3,z4,z5,z44,z52]),(0,[z1,z990,z3,z4,z5,z6]),(0,[z1,z219,z3,z4,z94,z6])]],
   [[(1,[z2,z728,z4,z5,z6]),(0,[z1,z2,z49,z100,z5,z6]),(0,[z1,z488,z2,z718,z5,z6]),(0,[z1,z766,z4,z288,z5,z6]),(0,[z1,z2,z3,z4,z5,z991]),(0,[z1,z2,z4,z5,z992,z6]),(0,[z1,z3,z4,z136,z6,z384]),(0,[z1,z2,z19,z4,z5,z544]),(0,[z1,z2,z4,z5,z6,z993])],[(0,[z1,z2,z994,z4,z5,z6]),(0,[z25,z1,z723,z3,z5,z6]),(0,[z1,z995,z3,z4,z5,z6])],[(0,[z1,z2,z996,z4,z5,z6]),(0,[z1,z778,z2,z3,z5,z6]),(0,[z997,z2,z3,z4,z5,z6]),(0,[z1,z2,z4,z5,z773,z39]),(0,[z176,z1,z2,z225,z4,z5])],[(0,[z138,z2,z3,z123,z5,z6]),(0,[z1,z998,z3,z4,z5,z6]),(0,[z999,z2,z3,z4,z5,z6]),(0,[z1,z160,z145,z3,z4,z5])],[(0,[z1,z2,z3,z4,z435,z6]),(0,[z1,z160,z17,z2,z4,z5]),(0,[z1,z160,z131,z3,z4,z5])],[(0,[z1,z164,z2,z3,z5,z6])],[(0,[z1,z2,z49,z4,z35,z6])],[(1,[z2,z3,z4,z794,z6]),(0,[z41,z2,z3,z4,z5,z42])]],
   [[(0,[z1,z2,z3,z4,z210,z6]),(0,[z1,z173,z2,z3,z210,z6]),(0,[z1,z488,z2,z3,z75,z6]),(0,[z1,z2,z1000,z4,z5,z6]),(0,[z1001,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z1003,z3,z4,z5,z6])],[(0,[z1,z2,z1004,z4,z5,z6]),(0,[z1,z2,z102,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z52]),(0,[z211,z2,z19,z4,z5,z6]),(0,[z1,z2,z30,z3,z4,z5])],[(0,[z1,z326,z165,z4,z5,z6]),(0,[z1,z2,z1005,z4,z5,z6]),(0,[z1,z2,z461,z20,z5,z6])],[(0,[z138,z2,z3,z155,z5,z6]),(0,[z1,z135,z3,z4,z5,z52]),(0,[z1,z2,z3,z4,z5,z741]),(0,[z1,z219,z225,z4,z5,z6])],[(0,[z77,z1,z3,z4,z701,z6]),(0,[z1,z2,z3,z1006,z5,z6]),(0,[z1007,z2,z3,z4,z5,z6])],[(0,[z1,z2,z728,z4,z5,z6]),(0,[z1,z160,z2,z4,z5,z308]),(0,[z1008,z2,z3,z4,z5,z6]),(0,[z1,z125,z3,z4,z5,z156])],[(0,[z1009,z2,z3,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1010]),(0,[z1,z2,z1011,z4,z5,z6]),(0,[z1,z2,z1012,z3,z5,z6]),(0,[z1,z2,z30,z4,z20,z5])],[(0,[z1,z1013,z2,z4,z5,z6]),(0,[z63,z2,z233,z4,z22,z6]),(0,[z77,z1,z131,z3,z4,z6]),(0,[z1,z378,z4,z20,z5,z6]),(0,[z1,z2,z30,z4,z35,z5])],[(0,[z1,z2,z1014,z4,z5,z6]),(0,[z77,z1,z160,z3,z4,z5]),(0,[z1,z2,z1015,z4,z5,z6]),(0,[z1,z145,z3,z4,z5,z177]),(0,[z1,z202,z4,z35,z5,z6]),(0,[z1,z2,z1016,z4,z5,z6])],[(0,[z1,z2,z186,z4,z435,z6]),(0,[z77,z1,z3,z4,z44,z78]),(0,[z1,z1017,z3,z4,z5,z6])],[(0,[z1,z216,z165,z4,z5,z6]),(0,[z1,z2,z225,z4,z5,z45]),(0,[z114,z1,z778,z2,z5,z6]),(0,[z1,z64,z378,z4,z18,z6]),(0,[z1,z125,z2,z4,z5,z431])],[(0,[z1,z2,z3,z1018,z5,z6]),(0,[z1,z2,z3,z4,z794,z6]),(0,[z1,z2,z769,z4,z5,z6]),(0,[z1,z2,z19,z4,z5,z39]),(0,[z1,z1019,z3,z4,z5,z6])],[(0,[z1,z517,z3,z4,z5,z177])],[(0,[z269,z2,z147,z4,z5,z6]),(0,[z1,z2,z186,z4,z210,z6]),(0,[z1,z2,z4,z5,z6,z1020]),(0,[z1,z141,z3,z4,z5,z747])]],
   [[(0,[z1,z1021,z2,z4,z5,z6])],[(0,[z1,z2,z3,z1022,z5,z6]),(0,[z1,z2,z4,z5,z1023,z52])],[(0,[z1,z2,z1024,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1025]),(0,[z1,z2,z3,z1026,z5,z6])],[(0,[z63,z488,z2,z3,z22,z6]),(0,[z374,z1,z3,z4,z5,z45]),(0,[z54,z1,z141,z3,z4,z45])],[(0,[z276,z2,z50,z4,z5,z6]),(0,[z1,z2,z1027,z4,z5,z6]),(0,[z1,z3,z4,z5,z684,z45]),(0,[z1,z219,z3,z4,z5,z177])],[(0,[z1,z1028,z2,z4,z5,z6]),(1,[z54,z1,z141,z3,z4]),(0,[z1,z4,z5,z6,z190,z153])],[(0,[z47,z2,z3,z4,z22,z6]),(0,[z1,z141,z131,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1029]),(0,[z77,z1,z160,z2,z3,z4]),(0,[z1,z3,z4,z136,z738,z6]),(0,[z176,z1,z434,z3,z4,z220])]],
   [[(0,[z1,z2,z3,z1030,z5,z6]),(0,[z1,z378,z3,z4,z5,z6]),(0,[z1,z135,z3,z4,z6,z545]),(0,[z1,z125,z2,z4,z5,z24])],[(0,[z1,z2,z1031,z3,z5,z6]),(0,[z2,z147,z728,z4,z5,z6]),(0,[z54,z1,z135,z3,z4,z6]),(0,[z1,z131,z19,z3,z4,z5])],[(0,[z1,z2,z460,z4,z5,z6]),(0,[z1,z103,z612,z4,z5,z6]),(0,[z1,z2,z3,z249,z5,z6])],[(0,[z1,z2,z4,z5,z1032,z6]),(0,[z1,z2,z1033,z4,z5,z6]),(0,[z1,z2,z1034,z4,z5,z6]),(0,[z138,z2,z3,z154,z5,z6]),(0,[z1,z2,z1035,z4,z5,z6])],[(0,[z1,z2,z165,z4,z5,z95]),(0,[z1,z2,z3,z4,z5,z747]),(0,[z1,z2,z3,z4,z93,z597])],[(0,[z1,z23,z4,z323,z5,z6]),(0,[z114,z1,z164,z2,z5,z6]),(0,[z1,z2,z1036,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z747])],[(0,[z1,z1037,z3,z4,z5,z6]),(0,[z77,z176,z1,z141,z3,z4]),(0,[z1,z64,z2,z4,z713,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z1038]),(0,[z1039,z2,z3,z4,z5,z6]),(0,[z1,z141,z3,z4,z5,z52]),(0,[z1,z2,z1040,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z220])],[(0,[z1,z2,z4,z20,z5,z61])],[(0,[z1,z2,z3,z4,z1041,z6]),(0,[z1,z1042,z3,z4,z5,z6]),(0,[z1,z1043,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1044]),(0,[z1,z2,z1045,z3,z4,z5]),(0,[z133,z2,z3,z4,z5,z101]),(0,[z1,z2,z1046,z4,z5,z6]),(0,[z114,z1,z378,z4,z5,z6])],[(0,[z1,z2,z165,z4,z5,z282]),(0,[z1,z309,z2,z165,z5,z6]),(0,[z1,z2,z3,z75,z210,z6]),(0,[z1,z665,z3,z4,z5,z45]),(0,[z1,z2,z454,z4,z5,z6])],[(0,[z1,z378,z147,z4,z5,z6]),(0,[z1,z2,z1047,z4,z5,z6]),(0,[z1,z2,z3,z5,z6,z1048]),(0,[z1,z2,z4,z5,z713,z6]),(0,[z1049,z2,z3,z4,z5,z6])],[(0,[z25,z1,z146,z3,z5,z6])],[(0,[z63,z2,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z1050,z6]),(0,[z114,z1,z2,z4,z5,z61]),(0,[z1,z2,z19,z655,z4,z5])]],
   [[(0,[z1,z2,z3,z1051,z5,z6]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z2,z1053,z4,z5,z6]),(0,[z1,z2,z139,z4,z5,z6]),(0,[z1,z125,z2,z4,z5,z773]),(0,[z176,z1,z2,z4,z190,z220])],[(0,[z2,z728,z50,z4,z5,z6]),(0,[z164,z2,z3,z50,z5,z6]),(0,[z1,z1054,z3,z4,z5,z6]),(0,[z2,z233,z122,z4,z5,z6]),(0,[z1,z2,z916,z4,z5,z6])],[(0,[z1,z2,z1055,z4,z5,z6]),(0,[z138,z2,z186,z154,z5,z6]),(0,[z1056,z2,z3,z4,z5,z6]),(0,[z54,z1,z2,z3,z4,z94]),(0,[z1,z3,z4,z5,z177,z747]),(1,[z1,z778,z2,z5,z6]),(0,[z1,z1057,z3,z4,z5,z6])],[],[(0,[z1,z2,z3,z4,z5,z1058]),(0,[z1,z326,z3,z4,z435,z6]),(0,[z1,z2,z3,z4,z94,z741])],[(0,[z1,z2,z3,z4,z5,z52])],[(0,[z587,z2,z50,z4,z5,z6]),(0,[z1,z64,z202,z4,z5,z6])],[(0,[z65,z2,z3,z4,z5,z101]),(0,[z1,z2,z19,z4,z5,z340]),(0,[z54,z1,z104,z3,z4,z6]),(0,[z54,z1,z141,z3,z4,z5]),(0,[z1,z3,z4,z5,z1059,z6]),(0,[z173,z2,z3,z279,z48,z6])]],
   [[(0,[z1,z2,z3,z4,z5,z282]),(0,[z1,z326,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z5,z61]),(0,[z1,z103,z104,z4,z5,z61])],[(0,[z63,z488,z2,z3,z5,z6]),(0,[z1,z2,z1060,z4,z5,z6]),(0,[z1,z131,z3,z4,z5,z220])],[(0,[z63,z2,z373,z4,z22,z6]),(0,[z1,z2,z4,z5,z6,z1061])],[(0,[z1,z2,z3,z4,z5,z1062]),(0,[z1,z2,z3,z4,z1063,z6]),(0,[z1,z2,z3,z4,z5,z1064]),(0,[z1,z2,z19,z4,z5,z670]),(0,[z1,z2,z165,z4,z435,z6]),(0,[z2,z3,z737,z154,z5,z6]),(0,[z1,z3,z4,z5,z738,z6])],[(0,[z47,z2,z3,z4,z5,z6]),(0,[z1,z2,z1065,z4,z5,z6]),(0,[z1,z64,z2,z4,z701,z6]),(0,[z47,z173,z2,z3,z5,z6])],[(0,[z1,z216,z3,z4,z435,z6]),(0,[z1,z1066,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1067]),(0,[z1,z2,z1068,z4,z5,z6]),(0,[z1,z173,z2,z3,z707,z6]),(0,[z1,z2,z3,z4,z707,z6])],[(0,[z1069,z2,z3,z4,z5,z6])],[(0,[z1,z2,z165,z4,z210,z6]),(0,[z1,z3,z4,z5,z6,z1070]),(0,[z1,z111,z2,z3,z5,z775])]],
   [[(0,[z1,z202,z50,z4,z5,z6]),(0,[z1,z1071,z3,z4,z5,z6]),(0,[z158,z2,z3,z737,z5,z6]),(0,[z1,z1072,z3,z4,z5,z6]),(1,[z1,z2,z4,z5,z773]),(0,[z1,z2,z4,z5,z1073,z6])],[(0,[z269,z2,z165,z4,z5,z6]),(0,[z1,z216,z3,z4,z210,z6]),(0,[z1074,z1,z2,z3,z4,z5]),(0,[z1,z2,z1075,z3,z4,z5])],[(0,[z106,z2,z50,z4,z5,z6]),(0,[z1076,z2,z3,z4,z5,z6]),(0,[z1,z111,z2,z3,z5,z56])],[(0,[z1,z1077,z2,z3,z5,z6]),(0,[z1,z1078,z2,z3,z4,z6]),(0,[z1,z3,z4,z5,z177,z52]),(0,[z1,z131,z3,z4,z5,z94]),(0,[z176,z1,z219,z3,z4,z5])],[(0,[z1,z17,z4,z136,z5,z6]),(0,[z54,z1,z141,z2,z3,z4]),(0,[z114,z211,z309,z2,z5,z6])],[(0,[z1,z2,z147,z4,z5,z61]),(0,[z1,z2,z30,z147,z4,z5]),(0,[z2,z3,z4,z21,z794,z6]),(0,[z1,z2,z4,z5,z1023,z6]),(0,[z1,z1079,z2,z4,z5,z6]),(0,[z1,z1080,z3,z4,z5,z6])],[(0,[z1,z2,z3,z75,z275,z6]),(0,[z158,z1,z2,z278,z5,z6]),(0,[z1081,z2,z3,z4,z5,z6]),(0,[z1,z928,z131,z4,z5,z6])],[(0,[z1,z2,z186,z4,z5,z282]),(0,[z1,z160,z135,z2,z3,z4]),(0,[z1,z173,z2,z3,z48,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 544) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 544).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1066)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [544, 522] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 133).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 133).take 123).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [133, 123] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_41360

theorem PEqualNP.Outside.L_meta_41360 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4240476288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4240476288) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41360.solve