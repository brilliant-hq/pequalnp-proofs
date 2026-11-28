import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_42980

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
  Nat.testBit (4276677320 * 2 ^ 32 + 4209027584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0008d84e18170d54#64 ++ 0x000236138605c355#64 ++ 0xf019f8fe383f1ffe#64 ++ 0xfc067e3f8e0fc7ff#64 : BitVec 256),
   (0x40e22b22ee336330#64 ++ 0x10388ac8bb8cd8cc#64 ++ 0xe1e63f27fe33e333#64 ++ 0x78798fc9ff8cf8cc#64 : BitVec 256),
   (0x960545c742c1b7c0#64 ++ 0x25815171d0b06df0#64 ++ 0xfe07c7c7c7c3ffc3#64 ++ 0xbf81f1f1f1f0fff0#64 : BitVec 256),
   (0x0b7007b0076802a8#64 ++ 0x42dc01ec01da00aa#64 ++ 0xdff807f807fc03ff#64 ++ 0xf7fe01fe01ff00ff#64 : BitVec 256),
   (0x3dbfb80005bed800#64 ++ 0x8f6fee00016fb600#64 ++ 0x7ffff80007fffc03#64 ++ 0xdffffe0001ffff00#64 : BitVec 256),
   (0x2fdff6fdb0000001#64 ++ 0x0bf7fdbf6c000000#64 ++ 0xaffffffff8000003#64 ++ 0xebfffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [10, 11]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [8, 13]⟩, ⟨.and, [12, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xf019f8fe383f1ffe 0xfc067e3f8e0fc7ff

def z1 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0xdff807f807fc03ff 0xf7fe01fe01ff00ff

def z2 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xaffffffff8000003 0xebfffffffe000000

def z3 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x7ffff80007fffc03 0xdffffe0001ffff00

def z4 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xe1e63f27fe33e333 0x78798fc9ff8cf8cc

def z5 : W := mkw 0x40eafb6efe376f74 0x103abedbbf8ddbdd 0xf1fffffffe3fffff 0xfc7fffffff8fffff

def z6 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe07c7c7c7c3ffc3 0xbf81f1f1f1f0fff0

def z7 : W := mkw 0x0b78d7fc176c0eec 0x42de35ff05db03bb 0xdff9c7f807fc1fff 0xf7fe71fe01ff07ff

def z8 : W := mkw 0x29dab238b0000001 0x0a76ac8e2c000000 0x01f8383838000000 0x407e0e0e0e000000

def z9 : W := mkw 0x3ffffefdb5bed801 0x8fffffbf6d6fb600 0xfffffffffffffc03 0xffffffffffffff00

def z10 : W := mkw 0x0008980208170d54 0x000226008205c355 0x7019f800003f1ffe 0xdc067e00000fc7ff

def z11 : W := mkw 0x00a2280004324000 0x00288a00010c9000 0x61e638000633e003 0x58798e00018cf800

def z12 : W := mkw 0x00c22220a0000000 0x0030888828000000 0xa1e63f27f8000003 0x68798fc9fe000000

def z13 : W := mkw 0x3fbffcdd15bed801 0x8fefff37456fb600 0x7ffff8d807fffc03 0xdffffe3601ffff00

def z14 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x0ff9f8f838000000 0xc3fe7e3e0e000000

def z15 : W := mkw 0x248ff84fb8170d55 0x0923fe13ee05c355 0x2007f807f8031c00 0x0801fe01fe00c700

def z16 : W := mkw 0x400001024a012330 0x10000040928048cc 0x0000000000000330 0x00000000000000cc

def z17 : W := mkw 0x060544c500000000 0x0181513140000000 0xae07c7c7c0000003 0xab81f1f1f0000000

def z18 : W := mkw 0xbfdff7fff2c1b7c1 0x2ff7fdfffcb06df0 0xffffffffffc3ffc3 0xfffffffffff0fff0

def z19 : W := mkw 0x40822000e0006000 0x1020880038001800 0x00060001c000e000 0x0001800070003800

def z20 : W := mkw 0x3db7280005bed800 0x8f6dca00016fb600 0x5fe6000007fffc01 0x17f9800001ffff00

def z21 : W := mkw 0x0b18dcde195f0ddc 0x42c637378657c377 0xfe19f8fe39ff1ffe 0xff867e3f8e7fc7ff

def z22 : W := mkw 0x6ffffffffe336331 0x1bffffffff8cd8cc 0xeffffffffe33e333 0xfbffffffff8cf8cc

def z23 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x9e01c7c7c1c01fc0 0xa78071f1f07007f0

def z24 : W := mkw 0x402009024e376f74 0x10080240938ddbdd 0x50000000063ffffc 0x14000000018fffff

def z25 : W := mkw 0x960544c74081b540 0x25815131d0206d50 0xae07c7c7c003fc03 0xab81f1f1f000ff00

def z26 : W := mkw 0x1605058002c09280 0x0581416000b024a0 0xfe07c7c007c3ffc3 0xbf81f1f001f0fff0

def z27 : W := mkw 0x064546fdb0000001 0x019151bf6c000000 0xae07c7fff8000003 0xab81f1fffe000000

def z28 : W := mkw 0x4bf22fb0af7a42b8 0x52fc8bec2bde90ae 0xdff83ff83ffc03ff 0xf7fe0ffe0fff00ff

def z29 : W := mkw 0x0b10049001480088 0x42c4012400520022 0x0e00000001c00000 0x0380000000700000

def z30 : W := mkw 0x2f5dd6fd10000001 0x0bd775bf44000000 0x8ff9c7f800000003 0xe3fe71fe00000000

def z31 : W := mkw 0x3d9fb00000809000 0x0f67ec0000202400 0x7ffff80007c3fc03 0xdffffe0001f0ff00

def z32 : W := mkw 0x7dffbb22efbffb30 0x9f7feec8bbeffecc 0xffffff27ffffff33 0xffffffc9ffffffcc

def z33 : W := mkw 0x960dddcf5ad7bfd4 0x25837773d6b5eff5 0xfe07ffc7ffc3ffc3 0xbf81fff1fff0fff0

def z34 : W := mkw 0x0008d04c10000000 0x0002341304000000 0xf019f8fe383c03fe 0xfc067e3f8e0f00ff

def z35 : W := mkw 0x1000000000809000 0x0400000000202400 0x5000000007c3fc00 0x1400000001f0ff00

def z36 : W := mkw 0x0f7547f5076802a8 0x43dd51fd41da00aa 0xffffc7ffc7fc03ff 0xfffff1fff1ff00ff

def z37 : W := mkw 0x3d1d9000018c9800 0x8f47640000632600 0x1e19c00001cc1c00 0x8786700000730700

def z38 : W := mkw 0x3fdff6fdb18c9801 0x8ff7fdbf6c632600 0xbffffffff9cc1c03 0xeffffffffe730700

def z39 : W := mkw 0x40eafb6efe336330 0x103abedbbf8cd8cc 0xe1fffffffe33e333 0xf87fffffff8cf8cc

def z40 : W := mkw 0x0008980000160800 0x0002260000058200 0x7019f800003f1c02 0xdc067e00000fc700

def z41 : W := mkw 0x3dbff84e1dbfdd54 0x8f6ffe13876ff755 0xfffff8fe3fffffff 0xfffffe3f8fffffff

def z42 : W := mkw 0x0040023000000028 0x4010008c0000000a 0x000000380000003c 0x0000000e0000000f

def z43 : W := mkw 0x3fdffefdb096d801 0x8ff7ffbf6c25b600 0xaffffffff803fc03 0xebfffffffe00ff00

def z44 : W := mkw 0x060ddccf18170d54 0x01837733c605c355 0xfe1ffffff83f1fff 0xff87fffffe0fc7ff

def z45 : W := mkw 0x0000404c10000000 0x0000101304000000 0x800000fe38000000 0x2000003f8e000000

def z46 : W := mkw 0x0008d04c10040c44 0x0002341304010311 0x1019c0d8000c1ccc 0x8406703600030733

def z47 : W := mkw 0x2fdff6fdb0040c45 0x0bf7fdbf6c010311 0xbffffffff80c1ccf 0xeffffffffe030733

def z48 : W := mkw 0x3dbff84605bfdd40 0x8f6ffe11816ff750 0xfffff8c607ffffc3 0xfffffe3181fffff0

def z49 : W := mkw 0x248ff04db0000001 0x0923fc136c000000 0x2007f807f8000000 0x0801fe01fe000000

def z50 : W := mkw 0xbf1dd5df52c1b7c1 0x2fc77577d4b06df0 0xfe1fc7dfc7c3ffc3 0xbf87f1f7f1f0fff0

def z51 : W := mkw 0x2f9ff4dd10000001 0x0be7fd3744000000 0x2ffff8d800000003 0xcbfffe3600000000

def z52 : W := mkw 0x2fdffeffb8170d55 0x0bf7ffbfee05c355 0xfffffffff83f1fff 0xfffffffffe0fc7ff

def z53 : W := mkw 0x0000080208130110 0x000002008204c044 0x4000000000330330 0x10000000000cc0cc

def z54 : W := mkw 0x0605048100000000 0x0181412040000000 0x0e060701c0000001 0x038181c070000000

def z55 : W := mkw 0x2fd726b1a0000001 0x0bf5c9ac68000000 0x0fe60701c0000001 0x03f981c070000000

def z56 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0x400000000633e330 0x10000000018cf8cc

def z57 : W := mkw 0xbf1dd4dd10c094c1 0x2fc7753744302530 0x1e19c0d801c01cc0 0x8786703600700730

def z58 : W := mkw 0x42e22fa2ee7363b0 0x10b88be8bb9cd8ec 0xffe63fe7fff3e3f3 0xfff98ff9fffcf8fc

def z59 : W := mkw 0x0000010242012300 0x00000040908048c0 0xe0060707c603e303 0x380181c1f180f8c0

def z60 : W := mkw 0x29bab800053e4800 0x8a6eae00014f9200 0x01f83800003c0000 0x407e0e00000f0000

def z61 : W := mkw 0x14a7280004b2d000 0x0529ca00012cb400 0x7fe7f80007f3fc03 0xdff9fe0001fcff00

def z62 : W := mkw 0xd6e76fe7eef3f7f0 0x35b9dbf9fbbcfdfc 0xffe7ffe7fff3fff3 0xfff9fff9fffcfffc

def z63 : W := mkw 0x3d1dd04c118c9c44 0x8f47741304632711 0x1e19c0d801cc1ccc 0x8786703600730733

def z64 : W := mkw 0x0000000818000014 0x0000000206000005 0x000000383800003c 0x0000000e0e00000f

def z65 : W := mkw 0x40c22a22e8136110 0x10308a88ba04d844 0xa1e63f27f803e003 0x68798fc9fe00f800

def z66 : W := mkw 0x208ab008b0000001 0x0822ac022c000000 0x0000380038000000 0x00000e000e000000

def z67 : W := mkw 0x0000404c10000444 0x0000101304000111 0x000000d8000000cc 0x0000003600000033

def z68 : W := mkw 0x2fdfb6b000000000 0x0bf7edac00000000 0xaffffff800000003 0xebfffffe00000000

def z69 : W := mkw 0x3fffbfb007fedaa8 0xcfffefec01ffb6aa 0xfffffff807ffffff 0xfffffffe01ffffff

def z70 : W := mkw 0x4bf227b0e76862a8 0x52fc89ec39da18aa 0x0fe60701c7c0e001 0x03f981c071f03800

def z71 : W := mkw 0x0008d84c10160800 0x0002361304058200 0xf019f8fe383f1c02 0xfc067e3f8e0fc700

def z72 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x2e07c707c7c3fc01 0x0b81f1c1f1f0ff00

def z73 : W := mkw 0x1405404600819540 0x0501501180206550 0xfe07c0c607c3ffc3 0xbf81f03181f0fff0

def z74 : W := mkw 0x40e22320e6206220 0x103888c839881888 0x01e60701c600e001 0x007981c071803800

def z75 : W := mkw 0x0b5006b000000000 0x02d401ac00000000 0x8ff807f800000003 0xe3fe01fe00000000

def z76 : W := mkw 0x2ffff7fdb76802a9 0x4bfffdff6dda00aa 0xfffffffffffc03ff 0xffffffffffff00ff

def z77 : W := mkw 0x4000080248136110 0x100002009204d844 0x000000000003e000 0x000000000000f800

def z78 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xa007c7c7c003ffc0 0x2801f1f1f000fff0

def z79 : W := mkw 0x2d9ff04db0000001 0x0b67fc136c000000 0x2ffff807f8000003 0xcbfffe01fe000000

def z80 : W := mkw 0x940540474081b540 0x25015011d0206d50 0x2007c007c003fc00 0x0801f001f000ff00

def z81 : W := mkw 0x9f7547f747e9b7e8 0x67dd51fdd1fa6dfa 0xffffc7ffc7ffffff 0xfffff1fff1ffffff

def z82 : W := mkw 0x024046fdb0000001 0x009011bf6c000000 0x800007fff8000000 0x200001fffe000000

def z83 : W := mkw 0x4020010046206220 0x1008004011881888 0x000000000600e000 0x0000000001803800

def z84 : W := mkw 0x0b18d4dc114c0ccc 0x42c6353704530333 0x1e19c0d801cc1ccc 0x8786703600730733

def z85 : W := mkw 0xd6efffeffef7fff4 0x35bbfffbffbdfffd 0xffffffffffffffff 0xffffffffffffffff

def z86 : W := mkw 0x940541474281b740 0x25015051d0a06dd0 0xe007c707c603ff03 0x3801f1c1f180ffc0

def z87 : W := mkw 0x6ff727b1e6206221 0x1bfdc9ec79881888 0x0fe60701c600e001 0x03f981c071803800

def z88 : W := mkw 0x00400220a0000000 0x0010008828000000 0x80000727f8000000 0x200001c9fe000000

def z89 : W := mkw 0x1020080005bed800 0x84080200016fb600 0x5000000007fffc00 0x1400000001ffff00

def z90 : W := mkw 0x0008980818160814 0x0002260206058205 0x7019f838383f1c3e 0xdc067e0e0e0fc70f

def z91 : W := mkw 0x0008980818160814 0x0002260206058205 0x00183838383c003c 0x40060e0e0e0f000f

def z92 : W := mkw 0x9605058142c0b280 0x2581416050b02ca0 0x0e060701c7c0e001 0x038181c071f03800

def z93 : W := mkw 0x8000404740012540 0x20001011d0004950 0x00000007c0000000 0x00000001f0000000

def z94 : W := mkw 0x0000000240012100 0x0000000090004840 0x20060007c003e000 0x08018001f000f800

def z95 : W := mkw 0x40400322ea012330 0x101000c8ba8048cc 0x80000727f8000330 0x200001c9fe0000cc

def z96 : W := mkw 0x0008d84c10160c44 0x0002361304058311 0x7019f8d8003f1cce 0xdc067e36000fc733

def z97 : W := mkw 0x2ffff6fdb5280001 0x0bfffdbf6d4a0000 0xfffffffffffc0003 0xffffffffffff0000

def z98 : W := mkw 0x39bab80005bed800 0x8e6eae00016fb600 0x51f8380007fffc00 0x547e0e0001ffff00

def z99 : W := mkw 0x2ddfb220a0000000 0x0b77ec8828000000 0xafffff27f8000003 0xebffffc9fe000000

def z100 : W := mkw 0xbfb765c747e9f7c0 0xafedd971d1fa7df0 0xffe7c7c7c7c3ffc3 0xbff9f1f1f1f0fff0

def z101 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xf001f8c638031fc2 0xbc007e318e00c7f0

def z102 : W := mkw 0x960544c500c094c0 0x2581513140302530 0x7e07c0c007c3fcc3 0x9f81f03001f0ff30

def z103 : W := mkw 0x3fdff6fdb0809001 0x0ff7fdbf6c202400 0xffffffffffc3fc03 0xfffffffffff0ff00

def z104 : W := mkw 0x0008d84c18160c54 0x0002361306058315 0x1019f8f8383c1cfc 0xc4067e3e0e0f073f

def z105 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x2fe7f80007c3fc01 0x0bf9fe0001f0ff00

def z106 : W := mkw 0x0000000200010540 0x0000000080004150 0x5000000000031fc0 0x140000000000c7f0

def z107 : W := mkw 0x0000080208130110 0x000002008204c044 0xe000382638330332 0x78000e098e0cc0cc

def z108 : W := mkw 0x1405000000809000 0x0501400000202400 0x7e07c00007c3fc03 0x9f81f00001f0ff00

def z109 : W := mkw 0x00c22322e2012300 0x003088c8b88048c0 0xe1e63f27fe03e303 0x78798fc9ff80f8c0

def z110 : W := mkw 0x3db7200005a8d000 0x8f6dc800016a3400 0x0fe6000007c0e001 0x03f9800001f03800

def z111 : W := mkw 0x820045c7424127c0 0x20801171d09049f0 0x800007c7c00003c0 0x200001f1f00000f0

def z112 : W := mkw 0x960dddcf5ad7bfd4 0x25837773d6b5eff5 0xfe1fffffffffffff 0xff87ffffffffffff

def z113 : W := mkw 0x160544c500809000 0x0581513140202400 0xfe07c7c7c7c3fc03 0xbf81f1f1f1f0ff00

def z114 : W := mkw 0x0248deffb8170d55 0x009237bfee05c355 0xf019fffff83f1ffe 0xfc067ffffe0fc7ff

def z115 : W := mkw 0x0000404e18010554 0x0000101386004155 0xf001c0fe38031ffe 0xbc00703f8e00c7ff

def z116 : W := mkw 0x02c266fdb0000001 0x00b099bf6c000000 0xa1e63ffff8000003 0x68798ffffe000000

def z117 : W := mkw 0x0000404600010540 0x0000101180004150 0xf001c0c600031fc2 0xbc0070318000c7f0

def z118 : W := mkw 0x0b10049001480088 0x42c4012400520022 0x1e1800d801cc00cc 0x8786003600730033

def z119 : W := mkw 0x2fdff6fdb1480089 0x4bf7fdbf6c520022 0xbffffffff9cc00cf 0xeffffffffe730033

def z120 : W := mkw 0xc24047e7ea4127f0 0x309011f9fa9049fc 0x800007e7f80003f0 0x200001f9fe0000fc

def z121 : W := mkw 0x0020000005280028 0x40080000014a000a 0x00000000003c003c 0x00000000000f000f

def z122 : W := mkw 0x0970023005280028 0x425c008c014a000a 0x5ff8003807fc003f 0xd7fe000e01ff000f

def z123 : W := mkw 0x0008d04c10000000 0x0002341304000000 0x2001f80638000000 0x08007e018e000000

def z124 : W := mkw 0x0008d04c10000000 0x0002341304000000 0xa019f8fe38000002 0xe8067e3f8e000000

def z125 : W := mkw 0x00c22a22a8130110 0x00308a88aa04c044 0xe1e63f27f8330333 0x78798fc9fe0cc0cc

def z126 : W := mkw 0x348fb8000096d800 0x8d23ee000025b600 0x2007f8000003fc00 0x0801fe000000ff00

def z127 : W := mkw 0x0b700fb20f7b03b8 0x42dc03ec83dec0ee 0xfff83ffe3fff03ff 0xfffe0fff8fffc0ff

def z128 : W := mkw 0x2fdffefdb8160815 0x0bf7ffbf6e058205 0xaffffffff83c003f 0xebfffffffe0f000f

def z129 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xa001f8fe38031ffc 0x28007e3f8e00c7ff

def z130 : W := mkw 0x0060022004200020 0x0018008801080008 0x01e0002000300030 0x40780008000c000c

def z131 : W := mkw 0x00600320076802a8 0x401800c801da00aa 0xd1e0072007fc03ff 0x747801c801ff00ff

def z132 : W := mkw 0xb48ff04ff081b541 0x2d23fc13fc206d50 0x2007f807f803fc00 0x0801fe01fe00ff00

def z133 : W := mkw 0x0000404e18010554 0x0000101386004155 0x800000fe380003fc 0x2000003f8e0000ff

def z134 : W := mkw 0x0970023005280028 0x425c008c014a000a 0x01f80038003c003c 0x407e000e000f000f

def z135 : W := mkw 0x00e22a20a4324000 0x00388a88290c9000 0xe1e63f27fe33e003 0x78798fc9ff8cf800

def z136 : W := mkw 0x40e22220a4204020 0x1038888829081008 0x01e0000000000000 0x0078000000000000

def z137 : W := mkw 0xd6e72fa3eef3f3b0 0x35b9cbe8fbbcfcec 0xefe63f27fff3e333 0x7bf98fc9fffcf8cc

def z138 : W := mkw 0x40600b22ee336330 0x101802c8bb8cd8cc 0xc0000727fe33e330 0x300001c9ff8cf8cc

def z139 : W := mkw 0x0008d04e18010554 0x0002341386004155 0xa019f8fe380003fe 0xe8067e3f8e0000ff

def z140 : W := mkw 0x3ffffeffbdbfdd55 0x8fffffbfef6ff755 0xffffffffffffffff 0xffffffffffffffff

def z141 : W := mkw 0x40eabb22ee376b30 0x103aaec8bb8ddacc 0xf1ffff27fe3fff33 0xfc7fffc9ff8fffcc

def z142 : W := mkw 0x240dd04d10000001 0x0903741344000000 0x0001c00000000000 0x0000700000000000

def z143 : W := mkw 0x3f1dd4dd118c9801 0x8fc7753744632600 0x1e19c0d801cc1c00 0x8786703600730700

def z144 : W := mkw 0x2dbfb800053e4800 0x8b6fee00014f9200 0x2ffff800003c0003 0xcbfffe00000f0000

def z145 : W := mkw 0x024007b0024002a8 0x409001ec009000aa 0xde0007f807c003ff 0xb78001fe01f000ff

def z146 : W := mkw 0x0000080208170d54 0x000002008205c355 0x50000000003f1ffc 0x14000000000fc7ff

def z147 : W := mkw 0x960544c500c094c0 0x2581513140302530 0x1e01c0c001c01cc0 0x8780703000700730

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0060707c0000003 0x280181c1f0000000

def z149 : W := mkw 0x0200049000400088 0x4080012400100022 0x000000d8000000cc 0x0000003600000033

def z150 : W := mkw 0x2ffff7fdb6200221 0x0bfffdff6d880088 0xeffffffffe300333 0xfbffffffff8c00cc

def z151 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x0fe0070007c00001 0x03f801c001f00000

def z152 : W := mkw 0x0930000005280000 0x024c0000014a0000 0x5ff8000007fc0003 0xd7fe000001ff0000

def z153 : W := mkw 0x0b78dffe1f7f0ffc 0x42de37ff87dfc3ff 0xfff9fffe3fff1fff 0xfffe7fff8fffc7ff

def z154 : W := mkw 0xd4e76b67eeb3f770 0x3539dad9fbacfddc 0xe1e7ff27fe33ff33 0x7879ffc9ff8cffcc

def z155 : W := mkw 0x9000010242c1b7c0 0x2400004090b06df0 0x5000000007c3ffc0 0x1400000001f0fff0

def z156 : W := mkw 0x0000484608170d54 0x000012118205c355 0xf001c0c6003f1ffe 0xbc007031800fc7ff

def z157 : W := mkw 0x0978da7e1d3f0d7c 0x425e369f874fc35f 0xf1f9f8fe383f1ffe 0xfc7e7e3f8e0fc7ff

def z158 : W := mkw 0x29dab238b0000001 0x0a76ac8e2c000000 0xa1fe3f3ff8000003 0x687f8fcffe000000

def z159 : W := mkw 0x140d980000969800 0x050366000025a600 0x7e1ff80007fffc03 0xdf87fe0001ffff00

def z160 : W := mkw 0x00c22220a0000000 0x0030888828000000 0x01e0382038000000 0x40780e080e000000

def z161 : W := mkw 0x0970023005280028 0x425c008c014a000a 0x01e0000000000000 0x0078000000000000

def z162 : W := mkw 0x024047fdb24002a9 0x409011ff6c9000aa 0x800007fff80003fc 0x200001fffe0000ff

def z163 : W := mkw 0x0060032006200220 0x001800c801880088 0xc1e0072006300333 0x707801c8018c00cc

def z164 : W := mkw 0x4bf22fb2ef7b63b8 0x52fc8becbbded8ee 0xfffe3fffffffe3ff 0xffff8ffffffff8ff

def z165 : W := mkw 0x408af84ef8176d54 0x1022be13be05db55 0xf01ff8fff83ffffe 0xfc07fe3ffe0fffff

def z166 : W := mkw 0x00cafa6eb8170d54 0x0032be9bae05c355 0xf1fffffff83f1fff 0xfc7ffffffe0fc7ff

def z167 : W := mkw 0x0b7006b0056800a8 0x42dc01ac015a002a 0x1ff800f801fc00fc 0xc7fe003e007f003f

def z168 : W := mkw 0x248fb00000000000 0x0923ec0000000000 0x2007f80000000000 0x0801fe0000000000

def z169 : W := mkw 0x9605058342c1b7c0 0x25814160d0b06df0 0x5e060701c7c3ffc1 0x178181c071f0fff0

def z170 : W := mkw 0x1020000005a8d000 0x84080000016a3400 0x0000000007c0e000 0x0000000001f03800

def z171 : W := mkw 0x00c22220a0000000 0x0030888828000000 0x01e60701c0000001 0x007981c070000000

def z172 : W := mkw 0x6ffff7fdf6206221 0x1bfffdff7d881888 0xaffffffffe00e003 0xebffffffff803800

def z173 : W := mkw 0x024007b0024002a8 0x409001ec009000aa 0x800007f8000003fc 0x200001fe000000ff

def z174 : W := mkw 0x2fdff7fdb2400281 0x0bf7fdff6c9000a0 0xffffffffffc003c3 0xfffffffffff000f0

def z175 : W := mkw 0x0020080004324000 0x00080200010c9000 0x400000000633e000 0x10000000018cf800

def z176 : W := mkw 0x80000102424127c0 0x20000040909049f0 0x00000000000003c0 0x00000000000000f0

def z177 : W := mkw 0x09700330076802a8 0x425c00cc01da00aa 0x51f8003807fc03fc 0x547e000e01ff00ff

def z178 : W := mkw 0x0008d94e5a172f54 0x000236539685cbd5 0xf01ffffffe3fffff 0xfc07ffffff8fffff

def z179 : W := mkw 0x29bab800053e4800 0x8a6eae00014f9200 0x61fe3800063fe003 0x587f8e00018ff800

def z180 : W := mkw 0x09389800053e0800 0x024e2600014f8200 0x7ff9f80007ff1c03 0xdffe7e0001ffc700

def z181 : W := mkw 0x3fffbeb005bed800 0x8fffefac016fb600 0xfffffff807fffc03 0xfffffffe01ffff00

def z182 : W := mkw 0x0200058002400280 0x00800160009000a0 0xde0007c007c003c3 0xb78001f001f000f0

def z183 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x5e01c0c007c3ffc0 0x9780703001f0fff0

def z184 : W := mkw 0x0008d84e18130110 0x000236138604c044 0xe019f8fe38330332 0xf8067e3f8e0cc0cc

def z185 : W := mkw 0x9020090247ffffc0 0xa408024091fffff0 0x5000000007ffffc0 0x1400000001fffff0

def z186 : W := mkw 0x0008900810000000 0x0002240204000000 0x0018383838000000 0x40060e0e0e000000

def z187 : W := mkw 0x0930000005280000 0x024c0000014a0000 0xdff800f807fc03ff 0xf7fe003e01ff00ff

def z188 : W := mkw 0x1d35000005a89000 0x074d4000016a2400 0x7fffc00007fffc03 0xdffff00001ffff00

def z189 : W := mkw 0x648ff84ff8136111 0x1923fe13fe04d844 0x2007f807f803e000 0x0801fe01fe00f800

def z190 : W := mkw 0x2fdff7fff2012301 0x0bf7fdfffc8048c0 0xeffffffffe03e303 0xfbffffffff80f8c0

def z191 : W := mkw 0xd6e767e7e6e1f7e0 0x35b9d9f9f9b87df8 0xffe7c7c7c7c3ffc3 0xbff9f1f1f1f0fff0

def z192 : W := mkw 0x00200100076802a8 0x4008004001da00aa 0x5000000007fc03fc 0x1400000001ff00ff

def z193 : W := mkw 0x0000010242012300 0x00000040908048c0 0x80000707c0000300 0x200001c1f00000c0

def z194 : W := mkw 0x40400b22ea132330 0x101002c8ba84c8cc 0xe0003f27f8330332 0x78000fc9fe0cc0cc

def z195 : W := mkw 0x64effb6ffe336331 0x193bfedbff8cd8cc 0xe1e7ff27fe33e333 0x7879ffc9ff8cf8cc

def z196 : W := mkw 0x3fbfbd8007feda80 0x8fefef6001ffb6a0 0xffffffc007ffffc3 0xfffffff001fffff0

def z197 : W := mkw 0x2bdaf6fdb0000001 0x0af6bdbf6c000000 0x81f83ffff8000000 0x607e0ffffe000000

def z198 : W := mkw 0x0b5006b000000000 0x02d401ac00000000 0xdff807f8003c03ff 0xf7fe01fe000f00ff

def z199 : W := mkw 0x0b789fb0077e0aa8 0x42de27ec01df82aa 0xfff9fff807ff1fff 0xfffe7ffe01ffc7ff

def z200 : W := mkw 0x4040436efa012774 0x101010dbbe8049dd 0x800007fff80003fc 0x200001fffe0000ff

def z201 : W := mkw 0x060dd4cd10000000 0x0183753344000000 0xae1ffffff8000003 0xeb87fffffe000000

def z202 : W := mkw 0x40eabb2afe376b34 0x103aaecabf8ddacd 0xe1fe3f3ffe3fe33f 0x787f8fcfff8ff8cf

def z203 : W := mkw 0x100008000096d800 0x840002000025b600 0x000000000003fc00 0x000000000000ff00

def z204 : W := mkw 0x960544c700c195c0 0x25815131c0306570 0xfe01c0c601c31fc2 0xbf8070318070c7f0

def z205 : W := mkw 0x348ff84e1897dd54 0x8d23fe138625f755 0xf01ff8fe383ffffe 0xfc07fe3f8e0fffff

def z206 : W := mkw 0x0b7047fdb76802a9 0x42dc11ff6dda00aa 0xdff807fffffc03ff 0xf7fe01ffffff00ff

def z207 : W := mkw 0x42e26ffffe336331 0x10b89bffff8cd8cc 0xe1e63ffffe33e333 0x78798fffff8cf8cc

def z208 : W := mkw 0x020044c500000000 0x0080113140000000 0x800007c7c0000000 0x200001f1f0000000

def z209 : W := mkw 0x0b7006b005280028 0x42dc01ac014a000a 0x8ff807f8003c003f 0xe3fe01fe000f000f

def z210 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xf1fe3ffffe3fe3ff 0xfc7f8fffff8ff8ff

def z211 : W := mkw 0x0000080208170d54 0x000002008205c355 0xd01800f8003f1ffe 0xf406003e000fc7ff

def z212 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x2001f80638031c00 0x08007e018e00c700

def z213 : W := mkw 0x7dbfb9024fbffb30 0x9f6fee4093effecc 0x7ffff80007ffff33 0xdffffe0001ffffcc

def z214 : W := mkw 0x00a228020c334110 0x00288a00830cd044 0xe1e638263e33e333 0x78798e098f8cf8cc

def z215 : W := mkw 0x0200058242412380 0x00800160909048e0 0xfe0607c7c7c3e3c3 0xbf8181f1f1f0f8f0

def z216 : W := mkw 0x2d9fb00000000000 0x0b67ec0000000000 0x2ffff80000000003 0xcbfffe0000000000

def z217 : W := mkw 0x29faba38b53e4801 0x8a7eae8e2d4f9200 0x01f83838383c0000 0x407e0e0e0e0f0000

def z218 : W := mkw 0x0008d04e10010540 0x0002341384004150 0xf019f8fe38031fc2 0xfc067e3f8e00c7f0

def z219 : W := mkw 0x0970033007280228 0x425c00cc01ca008a 0xc1f80738063c033f 0x707e01ce018f00cf

def z220 : W := mkw 0x40eafb6efe376f74 0x103abedbbf8ddbdd 0xe1e7ff27fe33ff33 0x7879ffc9ff8cffcc

def z221 : W := mkw 0x2fdfb6b9b0000001 0x0bf7edae6c000000 0x0ffe3f39f8000001 0x43ff8fce7e000000

def z222 : W := mkw 0x9200058242c1b7c0 0x2480016090b06df0 0xde0007c007c3ffc3 0xb78001f001f0fff0

def z223 : W := mkw 0x9000010242c1b7c0 0x2400004090b06df0 0xf0060707c7c3ffc3 0x3c0181c1f1f0fff0

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0xd01800f8003c03fe 0xf406003e000f00ff

def z225 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xfffffffff83c03ff 0xfffffffffe0f00ff

def z226 : W := mkw 0x0b7047f6076907e8 0x42dc11fd81da41fa 0xfff9c7fe07ff1fff 0xfffe71ff81ffc7ff

def z227 : W := mkw 0x3d3d900005ac9800 0x8f4f6400016b2600 0x5ff9c00007fc1c03 0xd7fe700001ff0700

def z228 : W := mkw 0x824047fff24127c1 0x209011fffc9049f0 0x800007fff80003c0 0x200001fffe0000f0

def z229 : W := mkw 0x9f7547f507e896e8 0x67dd51fd41fa25ba 0xdff9c7f807fc1fff 0xf7fe71fe01ff07ff

def z230 : W := mkw 0x40e26b66ee336770 0x10389ad9bb8cd9dc 0xf1e7ffe7fe33fff3 0xfc79fff9ff8cfffc

def z231 : W := mkw 0xbf1dd5c743cdbfc0 0xafc77571d0f36ff0 0xfe1fc7c7c7cfffc3 0xbf87f1f1f1f3fff0

def z232 : W := mkw 0x0000000000000000 0x0000000000000000 0x00180038003c003c 0x4006000e000f000f

def z233 : W := mkw 0x2fdfb6b1a0000001 0x0bf7edac68000000 0x2fffff01c0000003 0xcbffffc070000000

def z234 : W := mkw 0x0bf227b0a76802a8 0x42fc89ec29da00aa 0xfffe3ffffffc03ff 0xffff8fffffff00ff

def z235 : W := mkw 0xd6254dc74ef3f7f0 0x35895371d3bcfdfc 0xfe07c7c7c7f3fff3 0xbf81f1f1f1fcfffc

def z236 : W := mkw 0x29bab800053e4800 0x8a6eae00014f9200 0x71f9f800003f1c02 0xdc7e7e00000fc700

def z237 : W := mkw 0x0208ddce1a570fd4 0x008237738695c3f5 0xfe19fffe3fff1fff 0xff867fff8fffc7ff

def z238 : W := mkw 0x2f1dd4dd10000001 0x0bc7753744000000 0x0e19c0d800000000 0x8386703600000000

def z239 : W := mkw 0x2bfabfb0077e4aa8 0xcafeafec01df92aa 0xdff83ff807fc03ff 0xf7fe0ffe01ff00ff

def z240 : W := mkw 0x0000000208010110 0x0000000082004044 0x8000002638000330 0x200000098e0000cc

def z241 : W := mkw 0x9605058142c0b280 0x2581416050b02ca0 0x7e07c701c7c3fc03 0x9f81f1c071f0ff00

def z242 : W := mkw 0x0040022000000000 0x0010008800000000 0x81e0072000000003 0x607801c800000000

def z243 : W := mkw 0x2d1d900000000000 0x0b47640000000000 0x0e19c00000000000 0x8386700000000000

def z244 : W := mkw 0x0200058002400280 0x00800160009000a0 0x0e00070007c00001 0x038001c001f00000

def z245 : W := mkw 0x0000404600010540 0x0000101180004150 0x800000c6000003c0 0x20000031800000f0

def z246 : W := mkw 0x3d1dd84e199f9d54 0x8f4776138667e755 0xfe19f8fe39ff1ffe 0xff867e3f8e7fc7ff

def z247 : W := mkw 0x3dbfb8020dbfd910 0x8f6fee00836ff644 0xfffff8263fffff33 0xfffffe098fffffcc

def z248 : W := mkw 0x6dffbb22ee336330 0x1b7feec8bb8cd8cc 0xefffff27fe33e333 0xfbffffc9ff8cf8cc

def z249 : W := mkw 0x10000000018c9800 0x8400000000632600 0x1000000001cc1c00 0x0400000000730700

def z250 : W := mkw 0x40e22320e6206220 0x103888c839881888 0xa1e63f27fe00e003 0x68798fc9ff803800

def z251 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x3019f8de380f1ccc 0x8c067e378e03c733

def z252 : W := mkw 0x6fdffefff8136111 0x1bf7ffbffe04d844 0xaffffffff803e003 0xebfffffffe00f800

def z253 : W := mkw 0xbfdff6fdb0c094c1 0x2ff7fdbf6c302530 0xbffffffff9c01cc3 0xeffffffffe700730

def z254 : W := mkw 0xbf9ff5c742c1b7c0 0x2fe7fd71d0b06df0 0xffffffc7c7c3ffc3 0xfffffff1f1f0fff0

def z255 : W := mkw 0x3ff726b1a5a8d001 0x8ffdc9ac696a3400 0x0fe60701c7c0e001 0x03f981c071f03800

def z256 : W := mkw 0x00400238b0000001 0x0010008e2c000000 0x0000003838000000 0x0000000e0e000000

def z257 : W := mkw 0x0008980208170910 0x000226008205c244 0xf019f826383f1f32 0xfc067e098e0fc7cc

def z258 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe1fc7ffc7ffffff 0xff87f1fff1ffffff

def z259 : W := mkw 0x29d22230a0000001 0x0a74888c28000000 0x01e0000000000000 0x0078000000000000

def z260 : W := mkw 0x4bf22fb2ee336330 0x12fc8becbb8cd8cc 0xeffe3ffffe33e333 0xfbff8fffff8cf8cc

def z261 : W := mkw 0xbdbfb90247ffffc0 0xaf6fee4091fffff0 0x7ffff80007ffffc3 0xdffffe0001fffff0

def z262 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x81f807f8003c03fc 0x607e01fe000f00ff

def z263 : W := mkw 0x0008d84600170d40 0x000236118005c350 0xf019f8c6003f1fc2 0xfc067e31800fc7f0

def z264 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0xe00038263e33e332 0x78000e098f8cf8cc

def z265 : W := mkw 0x960545cf5ac1b7d4 0x25815173d6b06df5 0xfe07c7ffffc3ffff 0xbf81f1fffff0ffff

def z266 : W := mkw 0x0000080000120000 0x0000020000048000 0x6000380000330002 0x58000e00000cc000

def z267 : W := mkw 0x3dbfb8081dbed814 0x8f6fee02076fb605 0x7ffff8383ffffc3f 0xdffffe0e0fffff0f

def z268 : W := mkw 0x860545c7424127c0 0x21815171d09049f0 0xae07c7c7c00003c3 0xab81f1f1f00000f0

def z269 : W := mkw 0x0000404600010540 0x0000101180004150 0xf019c0fe003f1ffe 0xfc06703f800fc7ff

def z270 : W := mkw 0x40e22a20ac324030 0x10388a882b0c900c 0x01e0382038300030 0x40780e080e0c000c

def z271 : W := mkw 0x3dbfb00005a8d000 0x8f6fec00016a3400 0x2ffff80007c0e003 0xcbfffe0001f03800

def z272 : W := mkw 0x24cff26db0000001 0x0933fc9b6c000000 0xa1e7ff27f8000003 0x6879ffc9fe000000

def z273 : W := mkw 0x3d9fb000018c9800 0x8f67ec0000632600 0x3ffff80001cc1c03 0xcffffe0000730700

def z274 : W := mkw 0x0000080208170d54 0x000002008205c355 0x0000000000031c00 0x000000000000c700

def z275 : W := mkw 0x29daba38b8160815 0x0a76ae8e2e058205 0x01f83838383c003c 0x407e0e0e0e0f000f

def z276 : W := mkw 0x09300100076802a8 0x424c004001da00aa 0x5ff8000007fc03ff 0xd7fe000001ff00ff

def z277 : W := mkw 0x0b5006b001480088 0x42d401ac00520022 0x9ff807f801cc00cf 0xe7fe01fe00730033

def z278 : W := mkw 0x40e22b20ae324230 0x10388ac82b8c908c 0xc1e03f203e300333 0x70780fc80f8c00cc

def z279 : W := mkw 0x960dd5cf52c5bfc4 0x25837573d4b16ff1 0xfe1fc7dfc7cfffcf 0xbf87f1f7f1f3fff3

def z280 : W := mkw 0x40a22902ee336330 0x10288a40bb8cd8cc 0x60063807fe33e330 0x18018e01ff8cf8cc

def z281 : W := mkw 0x0910001001080008 0x4244000400420002 0x00180018000c000c 0x0006000600030003

def z282 : W := mkw 0x0950023000000000 0x0254008c00000000 0x01f8003800000000 0x407e000e00000000

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z284 : W := mkw 0x0bd226b0a0000000 0x02f489ac28000000 0xaffe3ffff8000003 0xebff8ffffe000000

def z285 : W := mkw 0x40e26b6efe336774 0x10389adbbf8cd9dd 0xe1e63ffffe33e3ff 0x78798fffff8cf8ff

def z286 : W := mkw 0x960544c740c1b5c0 0x25815131d0306d70 0x3e07c0c7c1c3fcc0 0x8f81f031f070ff30

def z287 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x41e038203e33e330 0x50780e080f8cf8cc

def z288 : W := mkw 0x2ffffefdb4324001 0x0bffffbf6d0c9000 0xeffffffffe33e003 0xfbffffffff8cf800

def z289 : W := mkw 0x940540474081b540 0x25015011d0206d50 0xf007c0c7c003ffc2 0xbc01f031f000fff0

def z290 : W := mkw 0x00caf26cb0000000 0x0032bc9b2c000000 0xa1fffffff8000003 0xe87ffffffe000000

def z291 : W := mkw 0x940540474081b540 0x25015011d0206d50 0x7e07c007c7c3fc03 0x9f81f001f1f0ff00

def z292 : W := mkw 0x0b5007b0024002a8 0x42d401ec009000aa 0x8ff807f8000003ff 0xe3fe01fe000000ff

def z293 : W := mkw 0xafdff7fff24127c1 0x2bf7fdfffc9049f0 0xaffffffff80003c3 0xebfffffffe0000f0

def z294 : W := mkw 0x2bfab7b8b76802a9 0x4afeadee2dda00aa 0xdff83ff83ffc03ff 0xf7fe0ffe0fff00ff

def z295 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x41e60701c633e331 0x107981c0718cf8cc

def z296 : W := mkw 0x060545c502400280 0x01815171409000a0 0xfe07c7c7c7c003c3 0xbf81f1f1f1f000f0

def z297 : W := mkw 0x0000010002400280 0x00000040009000a0 0x5000000007c003c0 0x1400000001f000f0

def z298 : W := mkw 0x0082200000000000 0x0020880000000000 0x21e6380000000003 0x48798e0000000000

def z299 : W := mkw 0x00600b220e330330 0x001802c8838cc0cc 0xe1e03f263e330333 0x78780fc98f8cc0cc

def z300 : W := mkw 0x1028d84e1dbfdd54 0x840a3613876ff755 0xf019f8fe3ffffffe 0xfc067e3f8fffffff

def z301 : W := mkw 0x40e22b22ef7b63b8 0x50388ac8bbded8ee 0xf1e63f27ffffe3ff 0x7c798fc9fffff8ff

def z302 : W := mkw 0x9f3545c747e9b7c0 0x27cd5171d1fa6df0 0xffffc7c7c7ffffc3 0xfffff1f1f1fffff0

def z303 : W := mkw 0xb68ffdc742d7ffc0 0xada3ff71d0b5fff0 0xfe07ffc7c7c3ffc3 0xbf81fff1f1f0fff0

def z304 : W := mkw 0x3fbfbc9005fed888 0xcfefef24017fb622 0x7ffff8d807fffccf 0xdffffe3601ffff33

def z305 : W := mkw 0x40822802e8136110 0x10208a00ba04d844 0x20063807f803e000 0x08018e01fe00f800

def z306 : W := mkw 0x3fffbfb007fedaa8 0xcfffefec01ffb6aa 0x7fffff0007fffc03 0xdfffffc001ffff00

def z307 : W := mkw 0x9605048100c09080 0x2581412040302420 0x0e00000001c00000 0x0380000000700000

def z308 : W := mkw 0x3dbff84c15bedc44 0x8f6ffe13056fb711 0x7ffff8d807fffccf 0xdffffe3601ffff33

def z309 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xe001f82638331f32 0x78007e098e0cc7cc

def z310 : W := mkw 0xbfbffdc747ffffc0 0xafefff71d1fffff0 0xffffffc7c7ffffc3 0xfffffff1f1fffff0

def z311 : W := mkw 0x0200058002400280 0x00800160009000a0 0xde1807f807fc03ff 0xf78601fe01ff00ff

def z312 : W := mkw 0x69fabb22ef3f6b30 0x9a7eaec8bbcfdacc 0xe1fe3f27fe3fe333 0x787f8fc9ff8ff8cc

def z313 : W := mkw 0x06c766e5a0000000 0x01b1d9b968000000 0xafe7ffe7f8000003 0xebf9fff9fe000000

def z314 : W := mkw 0x2fdffefdb0160801 0x0bf7ffbf6c058200 0xfffffffff83f1c03 0xfffffffffe0fc700

def z315 : W := mkw 0x026007b0076802a8 0x409801ec01da00aa 0xd00007f807fc03fc 0x340001fe01ff00ff

def z316 : W := mkw 0x0000404600010540 0x0000101180004150 0x2001c00600031c00 0x080070018000c700

def z317 : W := mkw 0x9405414742c1b7c0 0x25015051d0b06df0 0x7007c007c7c3ffc0 0x1c01f001f1f0fff0

def z318 : W := mkw 0x0b5046fdb0000001 0x02d411bf6c000000 0x8ff807fff8000003 0xe3fe01fffe000000

def z319 : W := mkw 0x2fffb7b0076802a8 0x4bffedec01da00aa 0xfffffff807fc03ff 0xfffffffe01ff00ff

def z320 : W := mkw 0x000009024a132310 0x000002409284c8c4 0xe0063f27fe33e333 0x78018fc9ff8cf8cc

def z321 : W := mkw 0x0405000000000000 0x0101400000000000 0x2e07c00000000003 0x8b81f00000000000

def z322 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x5019c0d8003f1ffc 0x94067036000fc7ff

def z323 : W := mkw 0x0008900000040800 0x0002240000010200 0x1019c000000c1c00 0x8406700000030700

def z324 : W := mkw 0x408af84ef8176d54 0x1022be13be05db55 0x2007f807f803fc00 0x0801fe01fe00ff00

def z325 : W := mkw 0x40e22b22ee376f74 0x10388ac8bb8ddbdd 0xf1e63f27fe3fffff 0x7c798fc9ff8fffff

def z326 : W := mkw 0x0068db6e1e370f74 0x001a36db878dc3dd 0xf1f9fffe3e3f1fff 0xfc7e7fff8f8fc7ff

def z327 : W := mkw 0x40e22a20ac324030 0x10388a882b0c900c 0x61e638203e33e033 0x58798e080f8cf80c

def z328 : W := mkw 0x0930000005280000 0x024c0000014a0000 0x01f80000003c0000 0x407e0000000f0000

def z329 : W := mkw 0x3f7d97b007ec9aa8 0xcfdf65ec01fb26aa 0xdff9c7f807fc1fff 0xf7fe71fe01ff07ff

def z330 : W := mkw 0x0060032006200220 0x001800c801880088 0x01e0070006000001 0x007801c001800000

def z331 : W := mkw 0x024006b1a0000001 0x009001ac68000000 0x00000701c0000000 0x000001c070000000

def z332 : W := mkw 0x940dd84f5897bd54 0x25037613d625ef55 0xf01ff8fff83ffffe 0xfc07fe3ffe0fffff

def z333 : W := mkw 0x0b700fb20f7f0ffc 0x42dc03ec83dfc3ff 0xdff807f807ff1fff 0xf7fe01fe01ffc7ff

def z334 : W := mkw 0x1405000000809000 0x0501400000202400 0x2007c0000003fc00 0x0801f0000000ff00

def z335 : W := mkw 0x0000484e18170d54 0x000012138605c355 0xd00000fe383f1ffc 0x3400003f8e0fc7ff

def z336 : W := mkw 0x3dbff84db5bed801 0x8f6ffe136d6fb600 0x7ffff807fffffc03 0xdffffe01ffffff00

def z337 : W := mkw 0x9f1545d743c9b7c8 0x67c55175d0f26df2 0xfe1fc7dfc7cfffcf 0xbf87f1f7f1f3fff3

def z338 : W := mkw 0xbffffffff7ffffc1 0xaffffffffdfffff0 0xffffffffffffffc3 0xfffffffffffffff0

def z339 : W := mkw 0x0000404e18010554 0x0000101386004155 0xd01800fe383c03fe 0xf406003f8e0f00ff

def z340 : W := mkw 0x820045c7424127c0 0x20801171d09049f0 0xde0007c7c7c003c3 0xb78001f1f1f000f0

def z341 : W := mkw 0x00822000a0000000 0x0020880028000000 0x20063807f8000000 0x08018e01fe000000

def z342 : W := mkw 0x2f7dd7fd176802a9 0x4bdf75ff45da00aa 0xdff9c7f807fc03ff 0xf7fe71fe01ff00ff

def z343 : W := mkw 0x0b5007b002400280 0x02d401ec009000a0 0xdff807f807c003c3 0xf7fe01fe01f000f0

def z344 : W := mkw 0x0008980a18170914 0x000226028605c245 0xe018383e383f033e 0x78060e0f8e0fc0cf

def z345 : W := mkw 0x0b10049001480088 0x42c4012400520022 0xde1800f801fc03fe 0xf786003e007f00ff

def z346 : W := mkw 0x3fbffcc505bed800 0x8fefff31416fb600 0xffffffc7c7fffc03 0xfffffff1f1ffff00

def z347 : W := mkw 0x96254dc747ffffc0 0xa5895371d1fffff0 0xfe07c7c7c7ffffc3 0xbf81f1f1f1fffff0

def z348 : W := mkw 0xd0e22b22eef3f7f0 0x34388ac8bbbcfdfc 0xf1e63f27fff3fff3 0x7c798fc9fffcfffc

def z349 : W := mkw 0x348720000080d000 0x8d21c80000203400 0x000600000000e000 0x0001800000003800

def z350 : W := mkw 0x3dbfb00005acd800 0x8f6fec00016b3600 0x1fffc00007ccfc01 0x87fff00001f33f00

def z351 : W := mkw 0xbfd727b1e2c0b281 0x2ff5c9ec78b02ca0 0x0fe60701c7c0e001 0x03f981c071f03800

def z352 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x801838fe383c03fc 0x60060e3f8e0f00ff

def z353 : W := mkw 0x002009020f7f0ffc 0x4008024083dfc3ff 0x5000000007ff1ffc 0x1400000001ffc7ff

def z354 : W := mkw 0x1425080005bed800 0x85094200016fb600 0x7e07c00007fffc03 0x9f81f00001ffff00

def z355 : W := mkw 0x748fb802e897f910 0x9d23ee00ba25fe44 0x2007f807f803fc00 0x0801fe01fe00ff00

def z356 : W := mkw 0x4bf22fb2ef7b63b8 0x52fc8becbbded8ee 0xefe63f27fff3e333 0x7bf98fc9fffcf8cc

def z357 : W := mkw 0x964547fff2c1b7c1 0x259151fffcb06df0 0xfe07c7ffffc3ffc3 0xbf81f1fffff0fff0

def z358 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x1ff807d807cc00cd 0x87fe01f601f30033

def z359 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xa019f8fe38031c02 0xe8067e3f8e00c700

def z360 : W := mkw 0x00200800053e4800 0x80080200014f9200 0x00000000003c0000 0x00000000000f0000

def z361 : W := mkw 0x6ff72fb3ee336331 0x1bfdcbecfb8cd8cc 0xefe63f27fe33e333 0x7bf98fc9ff8cf8cc

def z362 : W := mkw 0x9000414642c1b7c0 0x2400105190b06df0 0xf001c0c607c3ffc2 0xbc00703181f0fff0

def z363 : W := mkw 0x0910000000000000 0x0244000000000000 0x0ff8000000000003 0xc3fe000000000000

def z364 : W := mkw 0x74efbb22eeb7fb30 0x9d3beec8bbadfecc 0xe1e7ff27fe33ff33 0x7879ffc9ff8cffcc

def z365 : W := mkw 0x402008000c324030 0x10080200030c900c 0x0000000000300030 0x00000000000c000c

def z366 : W := mkw 0x960544c500c094c0 0x2581513140302530 0xbe07c7c7c1c01cc3 0xaf81f1f1f0700730

def z367 : W := mkw 0x4028d94e5e376f74 0x100a3653978ddbdd 0xf019f8fe3e3ffffe 0xfc067e3f8f8fffff

def z368 : W := mkw 0x96a76dc746f3f7c0 0x25a9db71d1bcfdf0 0xffe7ffc7c7f3ffc3 0xfff9fff1f1fcfff0

def z369 : W := mkw 0x29dafa7eb8170d55 0x0a76be9fae05c355 0xf1f9f8fe383f1ffe 0xfc7e7e3f8e0fc7ff

def z370 : W := mkw 0x820045c7424127c0 0x20801171d09049f0 0xe00607c7c603e3c3 0x380181f1f180f8f0

def z371 : W := mkw 0x2fd726b1a0000001 0x0bf5c9ac68000000 0xafe63f27f8000003 0x6bf98fc9fe000000

def z372 : W := mkw 0x7dffbb20e7befa20 0x9f7feec839efbe88 0x7fffff01c7fffc03 0xdfffffc071ffff00

def z373 : W := mkw 0x4048db6efa172f74 0x101236dbbe85cbdd 0xf019fffff83f1ffe 0xfc067ffffe0fc7ff

def z374 : W := mkw 0x940500014080b000 0x2501400050202c00 0x00060001c000e000 0x0001800070003800

def z375 : W := mkw 0x40e22b20ee326230 0x10388ac83b8c988c 0x01e63f21fe30e031 0x40798fc87f8c380c

def z376 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x21e63f07fe03e001 0x08798fc1ff80f800

def z377 : W := mkw 0x3d15000001889000 0x8f45400000622400 0x0e00000001c00000 0x0380000000700000

def z378 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x7001f806383f1ffc 0x1c007e018e0fc7ff

def z379 : W := mkw 0x40a22802ec336110 0x10288a00bb0cd844 0x61e63807fe33e003 0x58798e01ff8cf800

def z380 : W := mkw 0x2ffffefdb53e4801 0x8bffffbf6d4f9200 0xaffffffff83c0003 0xebfffffffe0f0000

def z381 : W := mkw 0x2ffff7fdb76802a9 0x4bfffdff6dda00aa 0xafffffffffc00003 0xebfffffffff00000

def z382 : W := mkw 0x0020000005280000 0x00080000014a0000 0x5000000007fc0000 0x1400000001ff0000

def z383 : W := mkw 0x96c767e7e2c1b7c0 0x25b1d9f9f8b06df0 0xffe7ffe7ffc3ffc3 0xfff9fff9fff0fff0

def z384 : W := mkw 0x3d1d9000018c9800 0x8f47640000632600 0x7e1fc00007cffc03 0x9f87f00001f3ff00

def z385 : W := mkw 0x7fffbfb2effffbb8 0xdfffefecbbfffeee 0xffffffffffffffff 0xffffffffffffffff

def z386 : W := mkw 0x0000404e18010554 0x0000101386004155 0x0000000638000000 0x000000018e000000

def z387 : W := mkw 0x40822902ea136310 0x10208a40ba84d8c4 0xe0063f07fe03e303 0x38018fc1ff80f8c0

def z388 : W := mkw 0x1b700fb007fedaa8 0xc6dc03ec01ffb6aa 0xdff807f807ffffff 0xf7fe01fe01ffffff

def z389 : W := mkw 0x02200580076802a8 0x4088016001da00aa 0xde0007c007fc03ff 0xb78001f001ff00ff

def z390 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x0ffe380007fce001 0x43ff8e0001ff3800

def z391 : W := mkw 0x026007a0066002a0 0x009801e8019800a8 0xdfe007e007f003f3 0xf7f801f801fc00fc

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000382638000002 0x68000e098e000000

def z393 : W := mkw 0x34afb80004b6d800 0x8d2bee00012db600 0x61e7f8000633fc03 0x5879fe00018cff00

def z394 : W := mkw 0x2f9ff4c500000000 0x0be7fd3140000000 0xafffffc7c0000003 0xebfffff1f0000000

def z395 : W := mkw 0x2fdffeffb8170d55 0x0bf7ffbfee05c355 0xaffffffff8031c03 0xebfffffffe00c700

def z396 : W := mkw 0x024006b000000000 0x009001ac00000000 0x800007f800000000 0x200001fe00000000

def z397 : W := mkw 0x0020010006200220 0x0008004001880088 0x4000000006300330 0x10000000018c00cc

def z398 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x7019f806383f1c02 0xdc067e018e0fc700

def z399 : W := mkw 0xbffff7fff7e9b7e9 0x6ffffdfffdfa6dfa 0xffffffffffffffff 0xffffffffffffffff

def z400 : W := mkw 0x0008900810040804 0x0002240204010201 0x00180018000c000c 0x0006000600030003

def z401 : W := mkw 0x40600322ee212330 0x101800c8bb8848cc 0xc1e00727fe300333 0x707801c9ff8c00cc

def z402 : W := mkw 0x402009024f7b63b8 0x5008024093ded8ee 0x5000000007ffe3fc 0x1400000001fff8ff

def z403 : W := mkw 0x024047fe1a4107fc 0x409011ff869041ff 0x800007fe380003fc 0x200001ff8e0000ff

def z404 : W := mkw 0x3fffbeb1a5bed801 0x8fffefac696fb600 0x7fffff01c7fffc03 0xdfffffc071ffff00

def z405 : W := mkw 0x40e22a22ac334130 0x10388a88ab0cd04c 0xe1e0382638330332 0x78780e098e0cc0cc

def z406 : W := mkw 0x962545c747e9b7e8 0x65895171d1fa6dfa 0xfe07c7c7c7ffffff 0xbf81f1f1f1ffffff

def z407 : W := mkw 0x69faba20ad3e4830 0x9a7eae882b4f920c 0x01f83820383c0030 0x407e0e080e0f000c

def z408 : W := mkw 0xbfdffffffad7bfd5 0x2ff7fffffeb5eff5 0xffffffffffffffff 0xffffffffffffffff

def z409 : W := mkw 0x424007b2ea4123b8 0x509001ecba9048ee 0x800007fff80003fc 0x200001fffe0000ff

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x600600000603e003 0x180180000180f800

def z411 : W := mkw 0x502009024fbffb30 0x9408024093effecc 0x5000000007ffff30 0x1400000001ffffcc

def z412 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0xdfe007c007c003c3 0xb7f801f001f000f0

def z413 : W := mkw 0x140501024281b300 0x0501404090a06cc0 0xfe07c707c7c3ff03 0xbf81f1c1f1f0ffc0

def z414 : W := mkw 0x29189000010c0800 0x8a46240000430200 0x00180000000c0000 0x0006000000030000

def z415 : W := mkw 0x3dbff84e1dbfdd54 0x8f6ffe13876ff755 0x7ffff8063ffffc03 0xdffffe018fffff00

def z416 : W := mkw 0x348ff84e1897dd54 0x8d23fe138625f755 0x2007f8063803fc00 0x0801fe018e00ff00

def z417 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x8fe007f807c003fd 0x23f801fe01f000ff

def z418 : W := mkw 0x0970023005280028 0x425c008c014a000a 0xd1f800f8003c03fe 0xf47e003e000f00ff

def z419 : W := mkw 0x248ff84fb8170d55 0x0923fe13ee05c355 0xf01ff8fff83f1ffe 0xfc07fe3ffe0fc7ff

def z420 : W := mkw 0x9405404500809440 0x2501501140202510 0x0001c00000001c00 0x0000700000000700

def z421 : W := mkw 0x0008980a18170d54 0x000226028605c355 0x50183838383f1ffc 0x54060e0e0e0fc7ff

def z422 : W := mkw 0x40e22320e6206220 0x103888c839881888 0xc1e60721c630e333 0x707981c8718c38cc

def z423 : W := mkw 0x96054dc74ad7bfd4 0x25815371d2b5eff5 0xfe07c7c7c7ffffff 0xbf81f1f1f1ffffff

def z424 : W := mkw 0x2f15049100000001 0x0bc5412440000000 0x0e00000000000000 0x0380000000000000

def z425 : W := mkw 0x7dfffb6effbfff74 0x9f7ffedbbfefffdd 0xffffffffffffffff 0xffffffffffffffff

def z426 : W := mkw 0xd6876dc7ead3f7d0 0x35a1db71fab4fdf4 0xfe07ffc7ffc3ffc3 0xbf81fff1fff0fff0

def z427 : W := mkw 0x0b300590076802a8 0x42cc016401da00aa 0x5e1800d807fc03fc 0x9786003601ff00ff

def z428 : W := mkw 0x40eafa6ebc374d74 0x103abe9baf0dd35d 0xf1f9f8fe383f1ffe 0xfc7e7e3f8e0fc7ff

def z429 : W := mkw 0x2fd726b1a0000001 0x0bf5c9ac68000000 0x8ffe07f9c0000003 0xe3ff81fe70000000

def z430 : W := mkw 0x348fb8000096d800 0x8d23ee000025b600 0x701ff800003ffc02 0xdc07fe00000fff00

def z431 : W := mkw 0x0248d6fdb0000001 0x009235bf6c000000 0xa019fffff8000002 0xe8067ffffe000000

def z432 : W := mkw 0x3dbfb8020dbfdd54 0x8f6fee00836ff755 0x7ffff80007ffffff 0xdffffe0001ffffff

def z433 : W := mkw 0x2ff727b1a76802a9 0x4bfdc9ec69da00aa 0xdffe07f9c7fc03ff 0xf7ff81fe71ff00ff

def z434 : W := mkw 0x2d97200000000000 0x0b65c80000000000 0x0fe6000000000001 0x03f9800000000000

def z435 : W := mkw 0x09789a381d3e083c 0x425e268e074f820f 0x01f83838383c003c 0x407e0e0e0e0f000f

def z436 : W := mkw 0x2fdffeffb8130111 0x0bf7ffbfee04c044 0xeffffffff8330333 0xfbfffffffe0cc0cc

def z437 : W := mkw 0x4b7007b2ef6923b8 0x52dc01ecbbda48ee 0xdff807fffffc03ff 0xf7fe01ffffff00ff

def z438 : W := mkw 0x0200048000400080 0x0080012000100020 0x1e0000c001c000c0 0x8780003000700030

def z439 : W := mkw 0x0008d04c10000000 0x0002341304000000 0x0019c0d800000000 0x8006703600000000

def z440 : W := mkw 0x9000010042c0b280 0x2400004010b02ca0 0x0000000007c0e000 0x0000000001f03800

def z441 : W := mkw 0x3d9fb8000096d800 0x8f67ee000025b600 0x2ffff8000003fc03 0xcbfffe000000ff00

def z442 : W := mkw 0x0b7006b005280000 0x02dc01ac014a0000 0xdff807f807fc0003 0xf7fe01fe01ff0000

def z443 : W := mkw 0x3dffba20a5bed800 0x8f7fee88296fb600 0xffffff27fffffc03 0xffffffc9ffffff00

def z444 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0xe0060707c633e333 0x380181c1f18cf8cc

def z445 : W := mkw 0x0000080008120010 0x0000020002048004 0x0000382038300030 0x40000e080e0c000c

def z446 : W := mkw 0x960545c502c096c0 0x2581517140b025b0 0xde01c7c007c01fc3 0xb78071f001f007f0

def z447 : W := mkw 0xc2e26fe7ee7367f0 0x30b89bf9fb9cd9fc 0xe1e63fe7fe33e3f3 0x78798ff9ff8cf8fc

def z448 : W := mkw 0x820045c7424127c0 0x20801171d09049f0 0xf001c7c7c0031fc2 0xbc0071f1f000c7f0

def z449 : W := mkw 0x0028d94e1f7f0ffc 0x400a365387dfc3ff 0xf019f8fe3fff1ffe 0xfc067e3f8fffc7ff

def z450 : W := mkw 0x1020090007fedaa8 0xc408024001ffb6aa 0x5000000007fffffc 0x1400000001ffffff

def z451 : W := mkw 0x0bf22fb0077a42a8 0x42fc8bec01de90aa 0xfffe3ff807ffe3ff 0xffff8ffe01fff8ff

def z452 : W := mkw 0x40600b224e336330 0x101802c8938cd8cc 0xc1e007200633e333 0x707801c8018cf8cc

def z453 : W := mkw 0x0040032002000220 0x001000c800800088 0x8000072000000330 0x200001c8000000cc

def z454 : W := mkw 0xbdbff84745bffd40 0xaf6ffe11d16fff50 0x7ffff807c7fffc03 0xdffffe01f1ffff00

def z455 : W := mkw 0x0000010242012300 0x00000040908048c0 0x400000000603e300 0x100000000180f8c0

def z456 : W := mkw 0x69fabb3afe336331 0x1a7eaecebf8cd8cc 0xe1fe3f3ffe33e333 0x787f8fcfff8cf8cc

def z457 : W := mkw 0x00200100076802a8 0x4008004001da00aa 0x0000000007c00000 0x0000000001f00000

def z458 : W := mkw 0x0000404400000000 0x0000101100000000 0xa001c0c600000002 0xa800703180000000

def z459 : W := mkw 0x3d1d9800019e9800 0x8f4766000067a600 0x7e19f80001ff1c02 0xdf867e00007fc700

def z460 : W := mkw 0x2ffff6fdb5280029 0x4bfffdbf6d4a000a 0xaffffffff83c003f 0xebfffffffe0f000f

def z461 : W := mkw 0x49f22b32ef3b6338 0x527c8accbbced8ce 0xe1fe3f3ffe3fe33f 0x787f8fcfff8ff8cf

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0xd00000c0000003c2 0xb4000030000000f0

def z463 : W := mkw 0x960dddc742d7bfc0 0x25837771d0b5eff0 0xfe1fffc7c7ffffc3 0xff87fff1f1fffff0

def z464 : W := mkw 0x40400320e2002220 0x101000c838800888 0x00000701c0000000 0x000001c070000000

def z465 : W := mkw 0x0b7007b006200220 0x02dc01ec01880088 0xcff807f806300333 0xf3fe01fe018c00cc

def z466 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x81e03f27f8300330 0x60780fc9fe0c00cc

def z467 : W := mkw 0xfffffffffef3f7f1 0x3fffffffffbcfdfc 0xfffffffffff3fff3 0xfffffffffffcfffc

def z468 : W := mkw 0x40400322ea012330 0x101000c8ba8048cc 0xe0060727fe03e333 0x380181c9ff80f8cc

def z469 : W := mkw 0xd02009024ef3f7f0 0x3408024093bcfdfc 0x5000000007f3fff0 0x1400000001fcfffc

def z470 : W := mkw 0x00aab80004364800 0x002aae00010d9200 0x71fff800063ffc03 0xdc7ffe00018fff00

def z471 : W := mkw 0xbfdff6fff081b541 0x2ff7fdbffc206d50 0xaffffffff803fc03 0xebfffffffe00ff00

def z472 : W := mkw 0x00a2290246336300 0x00288a40918cd8c0 0xe1e63f07c633e303 0x78798fc1f18cf8c0

def z473 : W := mkw 0x7df72320e7a8f220 0x9f7dc8c839ea3c88 0x0fe60701c7c0e001 0x03f981c071f03800

def z474 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x21fff800003ffc00 0x487ffe00000fff00

def z475 : W := mkw 0x0200048000000000 0x0080012000000000 0x8e0007c000000003 0xa38001f000000000

def z476 : W := mkw 0x26cff6fdb0000001 0x09b3fdbf6c000000 0xa007fffff8000000 0x2801fffffe000000

def z477 : W := mkw 0x29faba30053e4828 0xca7eae8c014f920a 0x01f83838003c003c 0x407e0e0e000f000f

def z478 : W := mkw 0x0000484608130550 0x000012118204c154 0xf001f8e638331ff2 0xfc007e398e0cc7fc

def z479 : W := mkw 0x9f7507b147e8b2a8 0x67dd41ec51fa2caa 0x0fe60701c7c0e001 0x03f981c071f03800

def z480 : W := mkw 0x4bf227b0e76862a8 0x52fc89ec39da18aa 0xdffe07f9c7fce3ff 0xf7ff81fe71ff38ff

def z481 : W := mkw 0x0b5007b0034802a8 0x42d401ec00d200aa 0x9e1807f801cc03fc 0xa78601fe007300ff

def z482 : W := mkw 0x820044c5004004c0 0x2080113140100130 0x000000c0000000c0 0x0000003000000030

def z483 : W := mkw 0x0938d84e1d3f0d54 0x024e3613874fc355 0xfff9f8fe3fff1fff 0xfffe7e3f8fffc7ff

def z484 : W := mkw 0x3db7200005a8d000 0x8f6dc800016a3400 0x7fe7c00007c3fc03 0x9ff9f00001f0ff00

def z485 : W := mkw 0x0000010002000200 0x0000004000800080 0xc000070006000303 0x300001c0018000c0

def z486 : W := mkw 0x24872001a0000001 0x0921c80068000000 0x00060001c0000000 0x0001800070000000

def z487 : W := mkw 0x0930000005280000 0x024c0000014a0000 0x0fe0000007c00001 0x03f8000001f00000

def z488 : W := mkw 0xbfd767f7e2c1b7c1 0x2ff5d9fdf8b06df0 0xffe7c7c7c7c3ffc3 0xbff9f1f1f1f0fff0

def z489 : W := mkw 0x0008d04c10040c44 0x0002341304010311 0xd019c0f8003c1ffe 0xf406703e000f07ff

def z490 : W := mkw 0xb48ff8474097fd40 0xad23fe11d025ff50 0x2007f807c003fc00 0x0801fe01f000ff00

def z491 : W := mkw 0x0970032007280220 0x025c00c801ca0088 0xdff8072007fc0333 0xf7fe01c801ff00cc

def z492 : W := mkw 0x00a2280004324000 0x00288a00010c9000 0x01e0380000300000 0x40780e00000c0000

def z493 : W := mkw 0xbfbffcc505fedcc0 0xafefff31417fb730 0x7ffff8c007fffcc3 0xdffffe3001ffff30

def z494 : W := mkw 0x2fffffffbf7f0ffd 0x4bffffffefdfc3ff 0xffffffffffff1fff 0xffffffffffffc7ff

def z495 : W := mkw 0x2fdff6ffb0010541 0x0bf7fdbfec004150 0xfffffffff8031fc3 0xfffffffffe00c7f0

def z496 : W := mkw 0x1f7507b007e892a8 0x47dd41ec01fa24aa 0xffffc7f807ffffff 0xfffff1fe01ffffff

def z497 : W := mkw 0x3db7200005a8d000 0x8f6dc800016a3400 0x5ffe000007fce003 0xd7ff800001ff3800

def z498 : W := mkw 0x49f22b22ef3b6330 0x127c8ac8bbced8cc 0xfffe3f27ffffe333 0xffff8fc9fffff8cc

def z499 : W := mkw 0x3ff727b007e8d2a8 0xcffdc9ec01fa34aa 0xdffe07f807fce3ff 0xf7ff81fe01ff38ff

def z500 : W := mkw 0x40eaba28bc364834 0x103aae8a2f0d920d 0x01f83838383c003c 0x407e0e0e0e0f000f

def z501 : W := mkw 0x9f7507b147e8b2a8 0x67dd41ec51fa2caa 0xdffe07f9c7fce3ff 0xf7ff81fe71ff38ff

def z502 : W := mkw 0x2fdff7fdb24002a9 0x4bf7fdff6c9000aa 0xaffffffff80003ff 0xebfffffffe0000ff

def z503 : W := mkw 0x0000080208130110 0x000002008204c044 0xf01838fe383f03fe 0xfc060e3f8e0fc0ff

def z504 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x8e0607c7c7c0e3c1 0x238181f1f1f038f0

def z505 : W := mkw 0x29daf27cb0000001 0x0a76bc9f2c000000 0xa1f9f8fe38000002 0xe87e7e3f8e000000

def z506 : W := mkw 0x0b10049000000000 0x02c4012400000000 0x0e1800d800000000 0x8386003600000000

def z507 : W := mkw 0x0000404db0000001 0x000010136c000000 0x00000007f8000000 0x00000001fe000000

def z508 : W := mkw 0x0b10059003480288 0x42c4016400d200a2 0xde1807d807cc03cf 0xb78601f601f300f3

def z509 : W := mkw 0x960545c542c0b280 0x2581517150b02ca0 0xae07c7c7c7c0e003 0xab81f1f1f1f03800

def z510 : W := mkw 0x900009024ad7bfd4 0x2400024092b5eff5 0x5000000007fffffc 0x1400000001ffffff

def z511 : W := mkw 0x0200058002400280 0x00800160009000a0 0x800007c0000003c0 0x200001f0000000f0

def z512 : W := mkw 0x4b700fb24f7b63b8 0x52dc03ec93ded8ee 0xdff807f807ffe3ff 0xf7fe01fe01fff8ff

def z513 : W := mkw 0x00200100076802a8 0x4008004001da00aa 0xd01800f807fc03fe 0xf406003e01ff00ff

def z514 : W := mkw 0x1028980005bed800 0x840a2600016fb600 0x7019f80007fffc02 0xdc067e0001ffff00

def z515 : W := mkw 0x960545c542c0b6c0 0x2581517150b02db0 0x1e07c7c1c7c0fcc1 0x8781f1f071f03f30

def z516 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x8ff807f807c00003 0xe3fe01fe01f00000

def z517 : W := mkw 0x34afb80005bed800 0x8d2bee00016fb600 0x7007f80007fffc00 0x1c01fe0001ffff00

def z518 : W := mkw 0x020044dd10000001 0x0080113744000000 0x000000d800000000 0x0000003600000000

def z519 : W := mkw 0x40822802e8136110 0x10208a00ba04d844 0xe0063827f833e332 0x78018e09fe0cf8cc

def z520 : W := mkw 0x40c22b22ea136330 0x10308ac8ba84d8cc 0xa0063f27f803e330 0x28018fc9fe00f8cc

def z521 : W := mkw 0x29fab238b5280029 0x4a7eac8e2d4a000a 0x01f83838383c003c 0x407e0e0e0e0f000f

def z522 : W := mkw 0x9405010242c1b7c0 0x2501404090b06df0 0x7e07c00007c3ffc3 0x9f81f00001f0fff0

def z523 : W := mkw 0x9000000000c094c0 0x2400000000302530 0x1000000001c01cc0 0x0400000000700730

def z524 : W := mkw 0x0008d04c10040c44 0x0002341304010311 0xb019f8fe380c1cce 0xec067e3f8e030733

def z525 : W := mkw 0x6fdff7fffa012331 0x1bf7fdfffe8048cc 0xaffffffff8000333 0xebfffffffe0000cc

def z526 : W := mkw 0x2fdff6ffb8010555 0x0bf7fdbfee004155 0xaffffffff80003ff 0xebfffffffe0000ff

def z527 : W := mkw 0x0000000000000000 0x0000000000000000 0x7001c00000031c02 0x9c0070000000c700

def z528 : W := mkw 0x7fffffffffbffb31 0x9fffffffffeffecc 0xffffffffffffff33 0xffffffffffffffcc

def z529 : W := mkw 0x2f1ddcdf18170d55 0x0bc77737c605c355 0xfe19f8fe383f1ffe 0xff867e3f8e0fc7ff

def z530 : W := mkw 0x2f5dd6fdb0000001 0x0bd775bf6c000000 0x8e19c7fff8000000 0xa38671fffe000000

def z531 : W := mkw 0x060544c700010540 0x01815131c0004150 0xfe07c7c7c0031fc3 0xbf81f1f1f000c7f0

def z532 : W := mkw 0x8200058142402280 0x20800160509008a0 0x00000701c0000000 0x000001c070000000

def z533 : W := mkw 0x0008980000160800 0x0002260000058200 0x2001f80000031c00 0x08007e000000c700

def z534 : W := mkw 0x2d9ff84e18170d54 0x0b67fe138605c355 0xfffff8fe383f1fff 0xfffffe3f8e0fc7ff

def z535 : W := mkw 0x9f7ddfff5fffbffc 0x67df77ffd7ffefff 0xffffffffffffffff 0xffffffffffffffff

def z536 : W := mkw 0xbfbfbd8147fefa80 0xafefef6051ffbea0 0x7fffff01c7fffc03 0xdfffffc071ffff00

def z537 : W := mkw 0x0008d04c10040c44 0x0002341304010311 0x0001c00000001c00 0x0000700000000700

def z538 : W := mkw 0x0008900000000000 0x0002240000000000 0x2019f80000000002 0xc8067e0000000000

def z539 : W := mkw 0x966547e746e1b7e0 0x259951f9d1b86df8 0xffe7c7e7c7f3fff3 0xfff9f1f9f1fcfffc

def z540 : W := mkw 0x0910000001080000 0x0244000000420000 0x1e18000001cc0000 0x8786000000730000

def z541 : W := mkw 0x0f5546f500000000 0x03d551bd40000000 0xafffc7ffc0000003 0xebfff1fff0000000

def z542 : W := mkw 0x7dbfb802edbff910 0x9f6fee00bb6ffe44 0x7ffff807fffffc03 0xdffffe01ffffff00

def z543 : W := mkw 0x3ffffffe1fffdffc 0xcfffffff87fff7ff 0xfffffffe3fffffff 0xffffffff8fffffff

def z544 : W := mkw 0x0000484e18130554 0x000012138604c155 0xe00038fe383303fe 0x78000e3f8e0cc0ff

def z545 : W := mkw 0x2f1dd4dd10000001 0x0bc7753744000000 0xae1fc7dfc0000003 0xab87f1f7f0000000

def z546 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x2fe7ff07f8000001 0x0bf9ffc1fe000000

def z547 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0xfffff8f807ffffff 0xfffffe3e01ffffff

def z548 : W := mkw 0x0000080208130110 0x000002008204c044 0x2000380638030000 0x08000e018e00c000

def z549 : W := mkw 0xbfbffdcf5fffffd4 0xafefff73d7fffff5 0xffffffffffffffff 0xffffffffffffffff

def z550 : W := mkw 0x0b30058007680280 0x02cc016001da00a0 0xdff807c007fc03c3 0xf7fe01f001ff00f0

def z551 : W := mkw 0x0b7007b2476923a8 0x42dc01ec91da48ea 0xfffe07ffc7ffe3ff 0xffff81fff1fff8ff

def z552 : W := mkw 0x0000010042002200 0x0000004010800880 0x00060701c600e001 0x000181c071803800

def z553 : W := mkw 0xbffffff747ffffe8 0xeffffffdd1fffffa 0xffffffffc7ffffff 0xfffffffff1ffffff

def z554 : W := mkw 0x0008980818160814 0x0002260206058205 0xd01838f8383c03fe 0xf4060e3e0e0f00ff

def z555 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x5fe0070007fc03fd 0x17f801c001ff00ff

def z556 : W := mkw 0x424047fffa012331 0x109011fffe8048cc 0x800007fff8000330 0x200001fffe0000cc

def z557 : W := mkw 0x0060032006200220 0x001800c801880088 0xd1f807f8063c03ff 0xf47e01fe018f00ff

def z558 : W := mkw 0x40a229024e336330 0x10288a40938cd8cc 0x61e638000633e333 0x58798e00018cf8cc

def z559 : W := mkw 0x49f22a30ad3a4038 0x527c8a8c2b4e900e 0x01f83838383c003c 0x407e0e0e0e0f000f

def z560 : W := mkw 0x3d3d980005bed800 0x8f4f6600016fb600 0x5e19c00007fffc00 0x9786700001ffff00

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0x101800d8000c00cc 0x8406003600030033

def z562 : W := mkw 0x340d900000849800 0x8d03640000212600 0x0001c00000001c00 0x0000700000000700

def z563 : W := mkw 0x9008d94e5ad7bfd4 0x2402365396b5eff5 0xf019f8fe3ffffffe 0xfc067e3f8fffffff

def z564 : W := mkw 0x9605058142c0b280 0x2581416050b02ca0 0xde0607c1c7c0e3c3 0xb78181f071f038f0

def z565 : W := mkw 0x964547f742c1b7e8 0x659151fdd0b06dfa 0xfe07c7ffc7c3ffff 0xbf81f1fff1f0ffff

def z566 : W := mkw 0xbf1dd4c501cc9cc0 0xafc7753140732730 0x1e19c0c001cc1cc0 0x8786703000730730

def z567 : W := mkw 0x0000414642012740 0x00001051908049d0 0xf007c7c7c603ffc3 0xbc01f1f1f180fff0

def z568 : W := mkw 0xffffffe7effffff0 0xbffffff9fbfffffc 0xffffffe7fffffff3 0xfffffff9fffffffc

def z569 : W := mkw 0x0b78d7fc176802a8 0x42de35ff05da00aa 0xfff9fffe3ffc03ff 0xfffe7fff8fff00ff

def z570 : W := mkw 0x29b2200005284000 0x8a6c8800014a1000 0x01e0000000000000 0x0078000000000000

def z571 : W := mkw 0x820045cf5a4127d4 0x20801173d69049f5 0x800007fff80003fc 0x200001fffe0000ff

def z572 : W := mkw 0x268ff4cdb0000001 0x09a3fd336c000000 0xae07ffc7f8000003 0xab81fff1fe000000

def z573 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x2019f83e383f1c3c 0x48067e0f8e0fc70f

def z574 : W := mkw 0x299ab00000000000 0x0a66ac0000000000 0x01f8380000000000 0x407e0e0000000000

def z575 : W := mkw 0x060545c742012300 0x01815171d08048c0 0xee07c7c7c603e303 0xbb81f1f1f180f8c0

def z576 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x1ff9f80001fc1c00 0xc7fe7e00007f0700

def z577 : W := mkw 0x29bab8081d3e4814 0x8a6eae02074f9205 0x01f83838383c003c 0x407e0e0e0e0f000f

def z578 : W := mkw 0x40e22322e6216320 0x103888c8b98858c8 0xe1e60707c603e303 0x387981c1f180f8c0

def z579 : W := mkw 0xd64547e7eac1b7f0 0x359151f9fab06dfc 0xfe07c7e7ffc3fff3 0xbf81f1f9fff0fffc

def z580 : W := mkw 0x0008d04e10050d44 0x0002341384014351 0xf019c0de000f1fce 0xbc0670378003c7f3

def z581 : W := mkw 0x00000100024002a8 0x40000040009000aa 0x00000000000003fc 0x00000000000000ff

def z582 : W := mkw 0x0008980818160814 0x0002260206058205 0x0000380038000000 0x00000e000e000000

def z583 : W := mkw 0x0248dffe1a570ffc 0x409237ff8695c3ff 0xf019fffe383f1ffe 0xfc067fff8e0fc7ff

def z584 : W := mkw 0x0000080208170d54 0x000002008205c355 0xf0003826383f1ffe 0x7c000e098e0fc7ff

def z585 : W := mkw 0x960dd5cf52c1b7c0 0x25837573d4b06df0 0xfe1fffffffc3ffc3 0xff87fffffff0fff0

def z586 : W := mkw 0x50e22b22efbffb30 0x94388ac8bbeffecc 0xf1e63f27ffffff33 0x7c798fc9ffffffcc

def z587 : W := mkw 0x0008d04e18050d54 0x0002341386014355 0x9019c0fe380c1ffc 0xa406703f8e0307ff

def z588 : W := mkw 0x024007b0024002a8 0x409001ec009000aa 0x0000070000000000 0x000001c000000000

def z589 : W := mkw 0x024046ffb8010555 0x009011bfee004155 0x800007fff80003fc 0x200001fffe0000ff

def z590 : W := mkw 0xbfdff7fdf2c0b281 0x2ff7fdff7cb02ca0 0xafffffffffc0e003 0xebfffffffff03800

def z591 : W := mkw 0x29bab800053e4800 0x8a6eae00014f9200 0x5ff8380007fc0003 0xd7fe0e0001ff0000

def z592 : W := mkw 0x9b7007b247e9b7e8 0x66dc01ec91fa6dfa 0xdff807f807ffffff 0xf7fe01fe01ffffff

def z593 : W := mkw 0x3dbff84c15bed800 0x8f6ffe13056fb600 0xfffff8fe3ffffc03 0xfffffe3f8fffff00

def z594 : W := mkw 0x960dd4cd10c49cc4 0x2583753344312731 0x1e19c0d801cc1ccc 0x8786703600730733

def z595 : W := mkw 0x026007b0066002a8 0x409801ec019800aa 0xc1e007f8063003ff 0x707801fe018c00ff

def z596 : W := mkw 0xd4876847e893f550 0x3521da11fa24fd54 0x2007f807f803fc00 0x0801fe01fe00ff00

def z597 : W := mkw 0x9f7547f747e9b7e8 0x67dd51fdd1fa6dfa 0xffe7c7c7c7c3ffc3 0xbff9f1f1f1f0fff0

def z598 : W := mkw 0x40822800a8124010 0x10208a002a049004 0x0000380038000000 0x00000e000e000000

def z599 : W := mkw 0x0060032246212320 0x001800c8918848c8 0xe1e60727c633e333 0x787981c9f18cf8cc

def z600 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000002000300332 0x70000008000c00cc

def z601 : W := mkw 0x00e22320a6200220 0x003888c829880088 0xe1e63f27fe300333 0x78798fc9ff8c00cc

def z602 : W := mkw 0x2ff727b1a76802a9 0x4bfdc9ec69da00aa 0x0fe60701c7c00001 0x03f981c071f00000

def z603 : W := mkw 0x3dffbb2007beda20 0x8f7feec801efb688 0xffffff2007ffff33 0xffffffc801ffffcc

def z604 : W := mkw 0x060544c500000000 0x0181513140000000 0x0e01c0c000000000 0x8380703000000000

def z605 : W := mkw 0xb68ff5cff2c1b7c1 0x2da3fd73fcb06df0 0xfe07ffc7ffc3ffc3 0xbf81fff1fff0fff0

def z606 : W := mkw 0x140dd84e18979d54 0x050376138625e755 0xfe1ff8fe3fffffff 0xff87fe3f8fffffff

def z607 : W := mkw 0x824047f7424127e8 0x609011fdd09049fa 0x800007ffc00003fc 0x200001fff00000ff

def z608 : W := mkw 0x6ffffefdbc324031 0x1bffffbf6f0c900c 0xaffffffff8300033 0xebfffffffe0c000c

def z609 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x0fffc7d9c0000001 0x83fff1f670000000

def z610 : W := mkw 0x0b58defe18170d54 0x02d637bf8605c355 0xfff9fffe383f1fff 0xfffe7fff8e0fc7ff

def z611 : W := mkw 0x9f5547f742c1b7c0 0x27d551fdd0b06df0 0xffffc7ffc7c3ffc3 0xfffff1fff1f0fff0

def z612 : W := mkw 0x2f1dd4dd11480089 0x4bc7753744520022 0x1e19c0d801cc00cc 0x8786703600730033

def z613 : W := mkw 0x3ff727b007e8d2a8 0xcffdc9ec01fa34aa 0x0fe6070007c0e001 0x03f981c001f03800

def z614 : W := mkw 0x0000080008160814 0x0000020002058205 0x00000000003c003c 0x00000000000f000f

def z615 : W := mkw 0x940dd84f5897bd54 0x25037613d625ef55 0x2007f807f803fc00 0x0801fe01fe00ff00

def z616 : W := mkw 0x3ffffffdb7fedaa9 0xcfffffff6dffb6aa 0xffffffffffffffff 0xffffffffffffffff

def z617 : W := mkw 0x0b5006b000000000 0x02d401ac00000000 0x0fe0070000000001 0x03f801c000000000

def z618 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000f8000003fc 0x2000003e000000ff

def z619 : W := mkw 0x2f1dd4dd10040c45 0x0bc7753744010311 0x1e19c0d8000c1ccc 0x8786703600030733

def z620 : W := mkw 0x00e22b2006324220 0x00388ac8018c9088 0xe1e63f200633e333 0x78798fc8018cf8cc

def z621 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x5ff8070007fc0003 0xd7fe01c001ff0000

def z622 : W := mkw 0x8b7047f7476927e8 0x62dc11fdd1da49fa 0xdff807ffc7fc03ff 0xf7fe01fff1ff00ff

def z623 : W := mkw 0x020045c6024107c0 0x00801171809041f0 0xfe01c7c607c31fc3 0xbf8071f181f0c7f0

def z624 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x0ff8073807fc003d 0x43fe01ce01ff000f

def z625 : W := mkw 0x0008980000160800 0x0002260000058200 0xf019f8f8003f1ffe 0xfc067e3e000fc7ff

def z626 : W := mkw 0x348fb8000096d800 0x8d23ee000025b600 0x7e07f80007c3fc03 0x9f81fe0001f0ff00

def z627 : W := mkw 0x8208ddcf5a572fd4 0x20823773d695cbf5 0xf019fffff83f1ffe 0xfc067ffffe0fc7ff

def z628 : W := mkw 0xbfb7258147e8f280 0xafedc96051fa3ca0 0x0fe60701c7c0e001 0x03f981c071f03800

def z629 : W := mkw 0x3f1d949001cc9888 0xcfc7652400732622 0x1e19c0d801cc1ccc 0x8786703600730733

def z630 : W := mkw 0x40e22a20ac324030 0x10388a882b0c900c 0xa1e63f27f8300033 0x68798fc9fe0c000c

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x801800f800000002 0xe006003e00000000

def z632 : W := mkw 0x0000000000040c44 0x0000000000010311 0x10000000000c1ccc 0x0400000000030733

def z633 : W := mkw 0x024007b0024002a8 0x409001ec009000aa 0xd01807f8003c03fe 0xf40601fe000f00ff

def z634 : W := mkw 0x2f1dd4dd10000001 0x0bc7753744000000 0xae19f8fe38000002 0xeb867e3f8e000000

def z635 : W := mkw 0x9f1544d501c894c8 0x67c5513540722532 0x1e19c0d801cc1ccc 0x8786703600730733

def z636 : W := mkw 0x2d9ff04c10000000 0x0b67fc1304000000 0xaffff8fe38000003 0xebfffe3f8e000000

def z637 : W := mkw 0x9605058342c1b380 0x25814160d0b06ce0 0xee060707c7c3e303 0x3b8181c1f1f0f8c0

def z638 : W := mkw 0xdff76ff7effbf7f8 0x77fddbfdfbfefdfe 0xffffffffffffffff 0xffffffffffffffff

def z639 : W := mkw 0x2ddff27db0000001 0x0b77fc9f6c000000 0x21fff83ff8000000 0x487ffe0ffe000000

def z640 : W := mkw 0x9020010247e9b7e8 0x6408004091fa6dfa 0x5000000007fffffc 0x1400000001ffffff

def z641 : W := mkw 0x0b789fb81f7e0abc 0x42de27ee07df82af 0xdff83ff83ffc03ff 0xf7fe0ffe0fff00ff

def z642 : W := mkw 0x0020000004200000 0x0008000001080000 0x41e0000006300003 0x50780000018c0000

def z643 : W := mkw 0x40e22a22ec336130 0x10388a88bb0cd84c 0x21e63827f833e030 0x48798e09fe0cf80c

def z644 : W := mkw 0x3dffba38b5bed801 0x8f7fee8e2d6fb600 0x7ffff8383ffffc03 0xdffffe0e0fffff00

def z645 : W := mkw 0x3dbfb90247bffb00 0x8f6fee4091effec0 0xffffff07c7ffff03 0xffffffc1f1ffffc0

def z646 : W := mkw 0x46e76fe7ee336330 0x11b9dbf9fb8cd8cc 0xefe7ffe7fe33e333 0xfbf9fff9ff8cf8cc

def z647 : W := mkw 0x3db7280005bad000 0x8f6dca00016eb400 0x6fe6380007f3e003 0x5bf98e0001fcf800

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000003c03fc 0x14000000000f00ff

def z649 : W := mkw 0x7df72b22efbbf330 0x9f7dcac8bbeefccc 0xefe63f27fff3e333 0x7bf98fc9fffcf8cc

def z650 : W := mkw 0x920045c742c1b7c0 0x24801171d0b06df0 0xd00007c7c7c3ffc0 0x340001f1f1f0fff0

def z651 : W := mkw 0x2dbfb80004324000 0x0b6fee00010c9000 0x6ffff8000633e003 0xdbfffe00018cf800

def z652 : W := mkw 0x40400220a8000030 0x101000882a00000c 0x0000002038000030 0x000000080e00000c

def z653 : W := mkw 0x29baf84e1d3f4d54 0x8a6ebe13874fd355 0xf1f9f8fe383f1ffe 0xfc7e7e3f8e0fc7ff

def z654 : W := mkw 0x900000024081b540 0x2400000090206d50 0x000000000003fc00 0x000000000000ff00

def z655 : W := mkw 0x10a2280005bed800 0x84288a00016fb600 0x71e6380007fffc03 0x5c798e0001ffff00

def z656 : W := mkw 0x1405000000809000 0x0501400000202400 0x0e06000007c0e001 0x0381800001f03800

def z657 : W := mkw 0x0b7047fe1f6907fc 0x42dc11ff87da41ff 0xdff807fe3ffc03ff 0xf7fe01ff8fff00ff

def z658 : W := mkw 0x0082280000124000 0x00208a0000049000 0x200638000003e000 0x08018e000000f800

def z659 : W := mkw 0x2ddfb238b0000001 0x0b77ec8e2c000000 0x2ffff83838000003 0xcbfffe0e0e000000

def z660 : W := mkw 0x0000000001480088 0x4000000000520022 0x1000000001cc00cc 0x0400000000730033

def z661 : W := mkw 0x348ff84db096d801 0x8d23fe136c25b600 0x2007f807f803fc00 0x0801fe01fe00ff00

def z662 : W := mkw 0x0000080000160800 0x0000020000058200 0x50000000003f1c00 0x14000000000fc700

def z663 : W := mkw 0x40e22322ee216330 0x103888c8bb8858cc 0x81e60727fe00e331 0x207981c9ff8038cc

def z664 : W := mkw 0x0b30049005680088 0x42cc0124015a0022 0x5ff800d807fc00cf 0xd7fe003601ff0033

def z665 : W := mkw 0x0000404400000440 0x0000101100000110 0x1001c0c000001cc0 0x8400703000000730

def z666 : W := mkw 0x0000000000000000 0x0000000000000000 0x50180000003c0002 0xd4060000000f0000

def z667 : W := mkw 0x2fd766fdb0000001 0x0bf5d9bf6c000000 0x8fe607fff8000001 0x23f981fffe000000

def z668 : W := mkw 0x102008020dbfdd54 0x84080200836ff755 0x5000000007fffffc 0x1400000001ffffff

def z669 : W := mkw 0x2f9ff4ddb0000001 0x0be7fd376c000000 0x2e1ff8dff8000000 0x8b87fe37fe000000

def z670 : W := mkw 0x960ddccf18d79dd4 0x25837733c635e775 0xfe19f8fe39ff1ffe 0xff867e3f8e7fc7ff

def z671 : W := mkw 0x3dffba3005bed828 0xcf7fee8c016fb60a 0x7ffff83807fffc3f 0xdffffe0e01ffff0f

def z672 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0xcfe0072007f00333 0x73f801c801fc00cc

def z673 : W := mkw 0x2fd766f5a0000001 0x0bf5d9bd68000000 0xafe7c7c7c0000003 0xabf9f1f1f0000000

def z674 : W := mkw 0x0008980000160800 0x0002260000058200 0x00183800003c0000 0x40060e00000f0000

def z675 : W := mkw 0x2dbfb00005280000 0x0b6fec00014a0000 0x7ffff80007fc0003 0xdffffe0001ff0000

def z676 : W := mkw 0x6fffffffff7b63b9 0x5bffffffffded8ee 0xffffffffffffe3ff 0xfffffffffffff8ff

def z677 : W := mkw 0x2bdab6b8b0000001 0x0af6adae2c000000 0x8ff83ff838000003 0xe3fe0ffe0e000000

def z678 : W := mkw 0x0008d84c18160814 0x0002361306058205 0xa019f8fe383c003e 0xe8067e3f8e0f000f

def z679 : W := mkw 0x54e72b22eeb3f330 0x1539cac8bbacfccc 0xffe7ff27fff3ff33 0xfff9ffc9fffcffcc

def z680 : W := mkw 0x0000000200010100 0x0000000080004040 0xe000000600030302 0x380000018000c0c0

def z681 : W := mkw 0x3dbfb90007fedaa8 0xcf6fee4001ffb6aa 0x7ffff80007ffffff 0xdffffe0001ffffff

def z682 : W := mkw 0x0405404500000000 0x0101501140000000 0x2007c007c0000000 0x0801f001f0000000

def z683 : W := mkw 0xd6e727a1e6e0f2a0 0x35b9c9e879b83ca8 0x0fe60701c7c0e001 0x03f981c071f03800

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x5e00000007c00003 0x9780000001f00000

def z685 : W := mkw 0x248ff04db0000001 0x0923fc136c000000 0xa01ff8fff8000002 0xe807fe3ffe000000

def z686 : W := mkw 0x42e22fb2ee7363b8 0x50b88becbb9cd8ee 0xe1e63ffffe33e3ff 0x78798fffff8cf8ff

def z687 : W := mkw 0x208ab80000164800 0x8822ae0000059200 0x0000380000000000 0x00000e0000000000

def z688 : W := mkw 0x3d9fb800019ed800 0x8f67ee000067b600 0x3e1ff80001cffc00 0x8f87fe000073ff00

def z689 : W := mkw 0x69faba38bc324031 0x1a7eae8e2f0c900c 0x01f8383838300030 0x407e0e0e0e0c000c

def z690 : W := mkw 0x0b58d6fc10000000 0x02d635bf04000000 0xaff9fffe38000003 0xebfe7fff8e000000

def z691 : W := mkw 0x40000002e8012110 0x10000000ba004844 0x00000007f8000000 0x00000001fe000000

def z692 : W := mkw 0x4bfafffeff7f6ffc 0x52febfffbfdfdbff 0xffffffffffffffff 0xffffffffffffffff

def z693 : W := mkw 0x0000000208010554 0x0000000082004155 0x00000000000003fc 0x00000000000000ff

def z694 : W := mkw 0x3ffff6fdb5a8d001 0x8ffffdbf6d6a3400 0xafffffffffc0e003 0xebfffffffff03800

def z695 : W := mkw 0x09b22800053a4000 0x026c8a00014e9000 0x7ffe380007ffe003 0xdfff8e0001fff800

def z696 : W := mkw 0x00aaf84e1c374d54 0x002abe13870dd355 0xf1fff8fe3e3fffff 0xfc7ffe3f8f8fffff

def z697 : W := mkw 0x1405000000809000 0x0501400000202400 0x1e01c00001c01c00 0x8780700000700700

def z698 : W := mkw 0x7dffba20adbed830 0x9f7fee882b6fb60c 0x7ffff8203ffffc33 0xdffffe080fffff0c

def z699 : W := mkw 0x2d9fb80000160800 0x0b67ee0000058200 0x7ffff800003f1c03 0xdffffe00000fc700

def z700 : W := mkw 0x6ffffffffe376f75 0x1bffffffff8ddbdd 0xfffffffffe3fffff 0xffffffffff8fffff

def z701 : W := mkw 0x00a2200004204000 0x0028880001081000 0x01e600000600e001 0x0079800001803800

def z702 : W := mkw 0x40e22b20e6326220 0x10388ac8398c9888 0x61e63f01c633e003 0x58798fc0718cf800

def z703 : W := mkw 0x96054dc74ad3b7d0 0x25815371d2b4edf4 0xfe07ffe7fff3fff3 0xff81fff9fffcfffc

def z704 : W := mkw 0x1930080005bed800 0x864c0200016fb600 0x5ff8000007fffc03 0xd7fe000001ffff00

def z705 : W := mkw 0x40c22322ea012330 0x103088c8ba8048cc 0xa1e63f27f8000333 0x68798fc9fe0000cc

def z706 : W := mkw 0x2918901810000001 0x0a46240604000000 0x0018001800000000 0x0006000600000000

def z707 : W := mkw 0x424047fefa4127fc 0x509011ffbe9049ff 0x800007fff80003fc 0x200001fffe0000ff

def z708 : W := mkw 0x902009024fffbffc 0x6408024093ffefff 0x5000000007fffffc 0x1400000001ffffff

def z709 : W := mkw 0x3dbfb80815bed804 0x8f6fee02056fb601 0x7ffff81807fffc0f 0xdffffe0601ffff03

def z710 : W := mkw 0xbff727b1e7e8b2a9 0x6ffdc9ec79fa2caa 0x0fe60701c7c0e001 0x03f981c071f03800

def z711 : W := mkw 0x36cfbfb002d6daa8 0xcdb3efec00b5b6aa 0xa007fff80003fffc 0x2801fffe0000ffff

def z712 : W := mkw 0xabbafdc7477f6fc0 0xaaeebf71d1dfdbf0 0x81f83fc7c03c03c0 0x607e0ff1f00f00f0

def z713 : W := mkw 0x0b30049005680088 0x42cc0124015a0022 0xdff800f807fc03ff 0xf7fe003e01ff00ff

def z714 : W := mkw 0x0008980208170910 0x000226008205c244 0xf019f8fe383f1ffe 0xfc067e3f8e0fc7ff

def z715 : W := mkw 0x3dbfb8000dbed810 0x8f6fee00036fb604 0x7ffff8203ffffc33 0xdffffe080fffff0c

def z716 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xe1fe3f3ffe3fe33f 0x787f8fcfff8ff8cf

def z717 : W := mkw 0x3d9fb000018c9800 0x8f67ec0000632600 0x7ffff80007cffc03 0xdffffe0001f3ff00

def z718 : W := mkw 0xbfdff6fdb0c09081 0x2ff7fdbf6c302420 0xaffffffff9c00003 0xebfffffffe700000

def z719 : W := mkw 0x542509024eb3f330 0x1509424093acfccc 0x7e07c00007f3ff33 0x9f81f00001fcffcc

def z720 : W := mkw 0x160545c502c09280 0x0581517140b024a0 0xfe07c7c7c7c3ffc3 0xbf81f1f1f1f0fff0

def z721 : W := mkw 0x3dbfb8000dbed814 0x8f6fee00036fb605 0x7ffff80007fffc3f 0xdffffe0001ffff0f

def z722 : W := mkw 0x0b7007b1a76802a9 0x42dc01ec69da00aa 0xdff807f9c7fc03ff 0xf7fe01fe71ff00ff

def z723 : W := mkw 0x04c76265a0000000 0x0131d89968000000 0xa1e7ff27f8000003 0x6879ffc9fe000000

def z724 : W := mkw 0xd60545c74ac1b7f0 0x35815171d2b06dfc 0xfe07c7c7c7c3fff3 0xbf81f1f1f1f0fffc

def z725 : W := mkw 0x2bdaf6fdb0000001 0x0af6bdbf6c000000 0x8ff83ffff8000003 0xe3fe0ffffe000000

def z726 : W := mkw 0x4b300d924f7b63b8 0x52cc036493ded8ee 0x5e1800d807ffe3fc 0x9786003601fff8ff

def z727 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xa1e63f27fe03e331 0x28798fc9ff80f8cc

def z728 : W := mkw 0x29daf27cb0000001 0x0a76bc9f2c000000 0xa1fffffff8000003 0xe87ffffffe000000

def z729 : W := mkw 0x2fdfb6b9b0000001 0x0bf7edae6c000000 0xaffe3f3ff8000003 0x6bff8fcffe000000

def z730 : W := mkw 0x960d9d895ad6ba94 0x2583676256b5aea5 0x0e1e3f39fffce03d 0x43878fce7fff380f

def z731 : W := mkw 0x40e22b20ee326230 0x10388ac83b8c988c 0xa1e63f27fe30e033 0x68798fc9ff8c380c

def z732 : W := mkw 0x00e22220a4204000 0x0038888829081000 0xa1e63f27fe00e003 0x68798fc9ff803800

def z733 : W := mkw 0x40eaf36cf6246e64 0x103abcdb3d891b99 0x11ffc7d9c60cfccd 0x847ff1f671833f33

def z734 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0xfffe07ffc7fc03ff 0xffff81fff1ff00ff

def z735 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x2fffff3ff8000001 0x4bffffcffe000000

def z736 : W := mkw 0x348ff84fb897dd55 0x8d23fe13ee25f755 0x2007f807f803fc00 0x0801fe01fe00ff00

def z737 : W := mkw 0x40e22a20ac324030 0x10388a882b0c900c 0xe1e63f27fe33e033 0x78798fc9ff8cf80c

def z738 : W := mkw 0x9605058142c0b280 0x2581416050b02ca0 0xfe07c7c1c7c3ffc3 0xbf81f1f071f0fff0

def z739 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x5ff9f80007fffc00 0xd7fe7e0001ffff00

def z740 : W := mkw 0x7d5d9322eb8dbb30 0x9f5764c8bae36ecc 0x9e19c727f9cc1f30 0xa78671c9fe7307cc

def z741 : W := mkw 0x3db7604e1da9d554 0x8f6dd813876a7555 0x8fe600fe3fc0e3fd 0x23f9803f8ff038ff

def z742 : W := mkw 0x960545c542c0b6c0 0x2581517150b02db0 0x7e07c7c1c7c3fcc3 0x9f81f1f071f0ff30

def z743 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x61e63f07fe33e003 0x58798fc1ff8cf800

def z744 : W := mkw 0x00c22a20a0124000 0x00308a8828049000 0xa1e63f27f803e003 0x68798fc9fe00f800

def z745 : W := mkw 0x6f3ddddf5e336331 0x1bcf7777d78cd8cc 0x4e19c0d80633e330 0x93867036018cf8cc

def z746 : W := mkw 0x0b78dffe1f7f0ffc 0x42de37ff87dfc3ff 0x2fe1ff063fc31c01 0x0bf87fc18ff0c700

def z747 : W := mkw 0x9d75427745a9b568 0x675d509dd16a6d5a 0x21ffc03fc03ffc3c 0x487ff00ff00fff0f

def z748 : W := mkw 0x24aff14db76802a9 0x492bfc536dda00aa 0x7007f807fffc03fc 0x1c01fe01ffff00ff

def z749 : W := mkw 0x3dbfb80004b2d000 0x0f6fee00012cb400 0x7ffff80007f3fc03 0xdffffe0001fcff00

def z750 : W := mkw 0x7dbfb8000dbed830 0x9f6fee00036fb60c 0x7ffff80007fffc33 0xdffffe0001ffff0c

def z751 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0xfff83ffe3ffc03ff 0xfffe0fff8fff00ff

def z752 : W := mkw 0x4b7007b0476862a8 0x52dc01ec11da18aa 0xdff807f807fce3ff 0xf7fe01fe01ff38ff

def z753 : W := mkw 0x06cff6edb0000000 0x01b3fdbb6c000000 0xaffffffff8000003 0xebfffffffe000000

def z754 : W := mkw 0xbfdff6fdb0809441 0x2ff7fdbf6c202510 0xaffffffff8001c03 0xebfffffffe000700

def z755 : W := mkw 0x12604efdb5bed801 0x849813bf6d6fb600 0xd00007fffffffc00 0x340001ffffffff00

def z756 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x5e07c7c1c7c3ffc1 0x9781f1f071f0fff0

def z757 : W := mkw 0x0b5006b001480088 0x42d401ac00520022 0xdff807f801fc03ff 0xf7fe01fe007f00ff

def z758 : W := mkw 0x00e22322e6212320 0x003888c8b98848c8 0xe1e63f27fe33e333 0x78798fc9ff8cf8cc

def z759 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x5ff800f807fc03fc 0xd7fe003e01ff00ff

def z760 : W := mkw 0x0970032007280220 0x025c00c801ca0088 0xdff807f807fc03ff 0xf7fe01fe01ff00ff

def z761 : W := mkw 0x00c26264a0000000 0x0030989928000000 0xa1e7ffe7f8000003 0xe879fff9fe000000

def z762 : W := mkw 0x4b922c92e95b6198 0x52e48b24ba56d866 0x3e1e38dff9cfe0cc 0x8f878e37fe73f833

def z763 : W := mkw 0x40e22b22ee336770 0x10388ac8bb8cd9dc 0xf1e63f27fe33fff3 0x7c798fc9ff8cfffc

def z764 : W := mkw 0x2fdff6fdb1080001 0x0bf7fdbf6c420000 0xbffffffff9cc0003 0xeffffffffe730000

def z765 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xaffffffff80003ff 0xebfffffffe0000ff

def z766 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xee07c707c7c3ff03 0x3b81f1c1f1f0ffc0

def z767 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0xfffff8c007ffffc3 0xfffffe3001fffff0

def z768 : W := mkw 0x40e22b22ef7b63b8 0x50388ac8bbded8ee 0xe1e63f27fff3e333 0x78798fc9fffcf8cc

def z769 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xae07c7c7c7c3fc03 0xab81f1f1f1f0ff00

def z770 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xe1e63ffffe33e3ff 0x78798fffff8cf8ff

def z771 : W := mkw 0xbf1dd4cd11cc9cc4 0xafc7753344732731 0x1e19c0d801cc1ccc 0x8786703600730733

def z772 : W := mkw 0x00c22320e2002200 0x003088c838800880 0xa1e63f27fe00e003 0x68798fc9ff803800

def z773 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xe1e63f07fe03e303 0x38798fc1ff80f8c0

def z774 : W := mkw 0x69faba30ad3e4838 0xda7eae8c2b4f920e 0x01f83838383c003c 0x407e0e0e0e0f000f

def z775 : W := mkw 0x29faba20a53e4800 0x8a7eae88294f9200 0x01f83820383c0000 0x407e0e080e0f0000

def z776 : W := mkw 0x3f1dd4dd11889001 0x8fc7753744622400 0x0e19c0d801c00000 0x8386703600700000

def z777 : W := mkw 0x160545c74281b300 0x05815171d0a06cc0 0xfe07c7c7c7c3ff03 0xbf81f1f1f1f0ffc0

def z778 : W := mkw 0x40e22a22ec336110 0x10388a88bb0cd844 0xe1e63f27fe33e003 0x78798fc9ff8cf800

def z779 : W := mkw 0x3dbfb801a5bed801 0x8f6fee00696fb600 0x7ffff801c7fffc03 0xdffffe0071ffff00

def z780 : W := mkw 0x09300100076802a8 0x424c004001da00aa 0xdff800f807fc03ff 0xf7fe003e01ff00ff

def z781 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x8ff9fffff8000000 0xe3fe7ffffe000000

def z782 : W := mkw 0x140541464281b740 0x0501505190a06dd0 0xfe07c7c7c7c3ffc3 0xbf81f1f1f1f0fff0

def z783 : W := mkw 0x2fdff6fdb0000441 0x0bf7fdbf6c000110 0xbffffffff8001cc3 0xeffffffffe000730

def z784 : W := mkw 0x00cab228b0000000 0x0032ac8a2c000000 0xa1fe3f3ff8000003 0x687f8fcffe000000

def z785 : W := mkw 0x402009024f3f6b30 0x9008024093cfdacc 0x40000000063fe330 0x10000000018ff8cc

def z786 : W := mkw 0x40e22b22ee376f74 0x10388ac8bb8ddbdd 0xe1e63f27fe33ff33 0x78798fc9ff8cffcc

def z787 : W := mkw 0x00cab220a0000000 0x0032ac8828000000 0xa1ffff27f8000003 0xe87fffc9fe000000

def z788 : W := mkw 0x4008d84e58176d54 0x100236139605db55 0xf019f8fe383ffffe 0xfc067e3f8e0fffff

def z789 : W := mkw 0x49faba38bd3e483c 0x527eae8e2f4f920f 0x01f83838383c003c 0x407e0e0e0e0f000f

def z790 : W := mkw 0x7dbfb800adbed810 0x9f6fee002b6fb604 0x7ffff8003ffffc03 0xdffffe000fffff00

def z791 : W := mkw 0x40e22b22ef7b63b8 0x50388ac8bbded8ee 0xf1fe3fffffffe3ff 0xfc7f8ffffffff8ff

def z792 : W := mkw 0x09d22230a0000000 0x0274888c28000000 0xa1fe3f3ff8000003 0x687f8fcffe000000

def z793 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0xfffff8263ffffc03 0xfffffe098fffff00

def z794 : W := mkw 0x902009024fffffd4 0xa408024093fffff5 0x5000000007fffffc 0x1400000001ffffff

def z795 : W := mkw 0x0008d04e10010540 0x0002341384004150 0xf019f8fe383f1ffe 0xfc067e3f8e0fc7ff

def z796 : W := mkw 0x402009024f7b63b8 0x5008024093ded8ee 0x4000000007f3e330 0x1000000001fcf8cc

def z797 : W := mkw 0x0b7006b0056800a8 0x42dc01ac015a002a 0xdff800f801fc03fe 0xf7fe003e007f00ff

def z798 : W := mkw 0x40e22322ee216330 0x103888c8bb8858cc 0xa1e63f27fe00e333 0x68798fc9ff8038cc

def z799 : W := mkw 0x96c766e5a0c094c0 0x25b1d9b968302530 0xbfe7ffe7f9c01cc3 0xeff9fff9fe700730

def z800 : W := mkw 0x0000484608130550 0x000012118204c154 0xf019f8fe383f1ffe 0xfc067e3f8e0fc7ff

def z801 : W := mkw 0x40e22b22ef3f6b30 0x90388ac8bbcfdacc 0xe1e63f27fe3fe333 0x78798fc9ff8ff8cc

def z802 : W := mkw 0x2fdff6fdb1480089 0x4bf7fdbf6c520022 0xaffffffff9c00003 0xebfffffffe700000

def z803 : W := mkw 0x2fd72eb3a8170d55 0x0bf5cbacea05c355 0x5fe60701c03f1ffd 0x17f981c0700fc7ff

def z804 : W := mkw 0x40e22b22ef3b6330 0x10388ac8bbced8cc 0xf1e63f27ffffe333 0x7c798fc9fffff8cc

def z805 : W := mkw 0x940541474281b740 0x25015051d0a06dd0 0xfe07c707c7c3ff03 0xbf81f1c1f1f0ffc0

def z806 : W := mkw 0x824047fffa4127d5 0x209011fffe9049f5 0x800007fff80003fc 0x200001fffe0000ff

def z807 : W := mkw 0x40e22b22ee376f74 0x10388ac8bb8ddbdd 0xf1fe3ffffe3fffff 0xfc7f8fffff8fffff

def z808 : W := mkw 0x3fdff6fdb0809001 0x0ff7fdbf6c202400 0xafffffffffc0e003 0xebfffffffff03800

def z809 : W := mkw 0x824047e7424127e0 0x209011f9d09049f8 0x800007e7c00003f0 0x200001f9f00000fc

def z810 : W := mkw 0x960545cf52c1b7c0 0x25815173d4b06df0 0xfe07c7ffffc3ffc3 0xbf81f1fffff0fff0

def z811 : W := mkw 0x502009024eb7fb30 0x9408024093adfecc 0x400000000633ff30 0x10000000018cffcc

def z812 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xfffffffff83c0003 0xfffffffffe0f0000

def z813 : W := mkw 0x14afb80004b6d800 0x052bee00012db600 0x7ffff80007fffc03 0xdffffe0001ffff00

def z814 : W := mkw 0x04c72220a0000000 0x0131c88828000000 0xafe7ff27f8000003 0xebf9ffc9fe000000

def z815 : W := mkw 0x502009024eb3f330 0x1408024093acfccc 0x5000000007f3ff30 0x1400000001fcffcc

def z816 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x7e07c707c7c3ffc1 0x1f81f1c1f1f0fff0

def z817 : W := mkw 0x14a7200004a0d000 0x0529c80001283400 0x7fe7c00007c3fc03 0x9ff9f00001f0ff00

def z818 : W := mkw 0x3dbfb81005bed808 0xcf6fee04016fb602 0x7ffff81807fffc0f 0xdffffe0601ffff03

def z819 : W := mkw 0x3d3d900005ac9800 0x8f4f6400016b2600 0x7fffc00007fffc03 0xdffff00001ffff00

def z820 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xf01ffffff83f1fff 0xfc07fffffe0fc7ff

def z821 : W := mkw 0x00c22220a0000000 0x0030888828000000 0xe1e63f27fe03e003 0x78798fc9ff80f800

def z822 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x3e07c7c7c7c3fcc1 0x8f81f1f1f1f0ff30

def z823 : W := mkw 0x40c22b22ea136310 0x10308ac8ba84d8c4 0xe1e63f27fe03e303 0x78798fc9ff80f8c0

def z824 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xf1fe3f27fe3fe333 0xfc7f8fc9ff8ff8cc

def z825 : W := mkw 0x3dbfb00005a89000 0x0f6fec00016a2400 0x7ffff80007fffc03 0xdffffe0001ffff00

def z826 : W := mkw 0x3dbfb800a5bed800 0x8f6fee00296fb600 0x7ffff807fffffc03 0xdffffe01ffffff00

def z827 : W := mkw 0xd6e76ee5acf2d4f0 0x35b9dbb96b3cb53c 0x1fe1f8e039f01cf0 0xc7f87e380e7c073c

def z828 : W := mkw 0x3d9fb80000969800 0x0f67ee000025a600 0x7ffff80007fffc03 0xdffffe0001ffff00

def z829 : W := mkw 0x140501004280b200 0x0501404010a02c80 0x7e07c701c7c3fc03 0x9f81f1c071f0ff00

def z830 : W := mkw 0xd02009024eb3f770 0x3408024093acfddc 0x400000000633ff30 0x10000000018cffcc

def z831 : W := mkw 0x0f5dd6fd10000000 0x03d775bf44000000 0xaffffffff8000003 0xebfffffffe000000

def z832 : W := mkw 0x40a22902ee336310 0x10288a40bb8cd8c4 0xe1e63f07fe33e303 0x78798fc1ff8cf8c0

def z833 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x5019f8f8383f1ffc 0xd4067e3e0e0fc7ff

def z834 : W := mkw 0x40e22b22ef3b6338 0x50388ac8bbced8ce 0xe1e63f27fe3fe33f 0x78798fc9ff8ff8cf

def z835 : W := mkw 0x402009024e336770 0x10080240938cd9dc 0x500000000633fff0 0x14000000018cfffc

def z836 : W := mkw 0x2fdff6fdb0400089 0x4bf7fdbf6c100022 0xaffffffff80000cf 0xebfffffffe000033

def z837 : W := mkw 0x24c72221a0000001 0x0931c88868000000 0xa1e63f27f8000003 0x68798fc9fe000000

def z838 : W := mkw 0x00c22220a0000000 0x0030888828000000 0xe1e63f27f8300333 0x78798fc9fe0c00cc

def z839 : W := mkw 0xb9dab33af2c1b7c1 0x2e76accebcb06df0 0x51f838383fc3ffc0 0x547e0e0e0ff0fff0

def z840 : W := mkw 0x2fdff6e5a0000000 0x0bf7fdb968000000 0xafffffe7f8000003 0xebfffff9fe000000

def z841 : W := mkw 0x3dbfb81815bed801 0x8f6fee06056fb600 0x7ffff81807fffc03 0xdffffe0601ffff00

def z842 : W := mkw 0x3fdff6fdb080d001 0x8ff7fdbf6c203400 0xaffffffff800e003 0xebfffffffe003800

def z843 : W := mkw 0x0b7007b0a76802a8 0x42dc01ec29da00aa 0xdff807fffffc03ff 0xf7fe01ffffff00ff

def z844 : W := mkw 0xbfdff6fdb1cc9cc1 0xaff7fdbf6c732730 0xbffffffff9cc1cc3 0xeffffffffe730730

def z845 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x6fe7f80007f3fc03 0x5bf9fe0001fcff00

def z846 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xffffffffffc00003 0xfffffffffff00000

def z847 : W := mkw 0xbfdff6fdb1c894c9 0x6ff7fdbf6c722532 0xbffffffff9cc1ccf 0xeffffffffe730733

def z848 : W := mkw 0x0bd226b0a0000000 0x02f489ac28000000 0xafe63f27f8000003 0x6bf98fc9fe000000

def z849 : W := mkw 0x2f9ff4cd10000000 0x0be7fd3344000000 0xaffffffff8000003 0xebfffffffe000000

def z850 : W := mkw 0xbfdff6fdb0c49cc5 0x2ff7fdbf6c312731 0xbffffffff9cc1ccf 0xeffffffffe730733

def z851 : W := mkw 0x1db7280005bad000 0x076dca00016eb400 0x7ffff80007fffc03 0xdffffe0001ffff00

def z852 : W := mkw 0x0008d84e58172d54 0x000236139605cb55 0xf01ff8fff83ffffe 0xfc07fe3ffe0fffff

def z853 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe1fc7c7c7ffffc3 0xff87f1f1f1fffff0

def z854 : W := mkw 0x40e22320e6206220 0x103888c839881888 0xe1e63f27fe30e333 0x78798fc9ff8c38cc

def z855 : W := mkw 0x960544c74081b540 0x25815131d0206d50 0xfe07c7c7c7c3fc03 0xbf81f1f1f1f0ff00

def z856 : W := mkw 0x2fdff6fdb0040c45 0x0bf7fdbf6c010311 0xfffffffff83c1fff 0xfffffffffe0f07ff

def z857 : W := mkw 0x09bab800053e4800 0x026eae00014f9200 0x7ffff80007fffc03 0xdffffe0001ffff00

def z858 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x5fffc00007fffc01 0x97fff00001ffff00

def z859 : W := mkw 0x402009024f3b6338 0x5008024093ced8ce 0x40000000063fe33c 0x10000000018ff8cf

def z860 : W := mkw 0x02c266fdb0000001 0x00b099bf6c000000 0x81e03ffff8000000 0x60780ffffe000000

def z861 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe07ffe7ffc3ffc3 0xff81fff9fff0fff0

def z862 : W := mkw 0x7ff727b0e7e8f2a8 0xdffdc9ec39fa3caa 0x0fe60701c7c0e001 0x03f981c071f03800

def z863 : W := mkw 0x40e22b22ef7f6ffc 0x50388ac8bbdfdbff 0xf1e63f27ffffffff 0x7c798fc9ffffffff

def z864 : W := mkw 0x69faba20a53e4820 0x9a7eae88294f9208 0x01f83800003c0000 0x407e0e00000f0000

def z865 : W := mkw 0x960545cf5ac1b7d4 0x25815173d6b06df5 0xfe1fc7ffffffffff 0xff87f1ffffffffff

def z866 : W := mkw 0x40e22b22ee336774 0x10388ac8bb8cd9dd 0xe1e63f27fe33e3ff 0x78798fc9ff8cf8ff

def z867 : W := mkw 0x2fd766f5a0000001 0x0bf5d9bd68000000 0xafe7ffe7f8000003 0xebf9fff9fe000000

def z868 : W := mkw 0x1487200000809000 0x0521c80000202400 0x7fe7f80007c3fc03 0xdff9fe0001f0ff00

def z869 : W := mkw 0x824047e7e24127c0 0x209011f9f89049f0 0x800007e7f80003c0 0x200001f9fe0000f0

def z870 : W := mkw 0x3f1dd4dd118c9c45 0x8fc7753744632711 0x1e19c0d801cc1ccc 0x8786703600730733

def z871 : W := mkw 0x3dbfb00005acd800 0x8f6fec00016b3600 0x7fffc00007cffc03 0x9ffff00001f3ff00

def z872 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xfffffffff8031c03 0xfffffffffe00c700

def z873 : W := mkw 0x69faba28bd3e4834 0x9a7eae8a2f4f920d 0x01f83838383c003c 0x407e0e0e0e0f000f

def z874 : W := mkw 0x00c22220a0000000 0x0030888828000000 0x81e03f27f8000000 0x60780fc9fe000000

def z875 : W := mkw 0x8b7007b1476822a8 0x62dc01ec51da08aa 0xdff807f9c7fc03ff 0xf7fe01fe71ff00ff

def z876 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xa1e63f27fe03e003 0x68798fc9ff80f800

def z877 : W := mkw 0x3d3d980005bed800 0x8f4f6600016fb600 0x5ff9c00007fffc03 0xd7fe700001ffff00

def z878 : W := mkw 0x00c22222e0012100 0x00308888b8004840 0xa1e63f27f803e003 0x68798fc9fe00f800

def z879 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xaffffffff83c003f 0xebfffffffe0f000f

def z880 : W := mkw 0x0b5007b002400280 0x02d401ec009000a0 0xdff807f807fc03ff 0xf7fe01fe01ff00ff

def z881 : W := mkw 0x3f1dd4dd10849801 0x8fc7753744212600 0x0e19c0d800001c00 0x8386703600000700

def z882 : W := mkw 0x960545df52c1b7c1 0x25815177d4b06df0 0xfe07c7dfc7c3ffc3 0xbf81f1f7f1f0fff0

def z883 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xf1e63f27fe3fe3ff 0x7c798fc9ff8ff8ff

def z884 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x7ffff8d807fffccf 0xdffffe3601ffff33

def z885 : W := mkw 0x960545c74ac1b7d4 0x25815171d2b06df5 0xfe07c7c7c7c3ffff 0xbf81f1f1f1f0ffff

def z886 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x5ff807d807fc03fd 0x97fe01f601ff00ff

def z887 : W := mkw 0x3f1dd4dd10809001 0x0fc7753744202400 0x1e19c0d801c01c00 0x8786703600700700

def z888 : W := mkw 0x3ddfb220a18c9800 0x8f77ec8828632600 0xbfffff27f9cc1c03 0xefffffc9fe730700

def z889 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xf01ff8fe3e3fffff 0xfc07fe3f8f8fffff

def z890 : W := mkw 0x2ddfb238b0000001 0x0b77ec8e2c000000 0xafffff3ff8000003 0xebffffcffe000000

def z891 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0xfff9c7f807ff1fff 0xfffe71fe01ffc7ff

def z892 : W := mkw 0x502009024ffffbb8 0xd408024093fffeee 0x5000000007fffffc 0x1400000001ffffff

def z893 : W := mkw 0x40c22a22e8136110 0x10308a88ba04d844 0xe1e63f27f833e333 0x78798fc9fe0cf8cc

def z894 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe07c7e7c7f3fff3 0xff81f1f9f1fcfffc

def z895 : W := mkw 0x2fdff6fdb0000445 0x0bf7fdbf6c000111 0xaffffffff80000cf 0xebfffffffe000033

def z896 : W := mkw 0x160544c700819540 0x05815131c0206550 0xfe07c7c7c7c3ffc3 0xbf81f1f1f1f0fff0

def z897 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0xfffff82007ffff33 0xfffffe0801ffffcc

def z898 : W := mkw 0x1405000000809000 0x0501400000202400 0xfe07c707c7c3fc03 0xbf81f1c1f1f0ff00

def z899 : W := mkw 0x3db7280005bed800 0x8f6dca00016fb600 0x7fe7c00007fffc03 0x9ff9f00001ffff00

def z900 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0xffffff07c7fffc03 0xffffffc1f1ffff00

def z901 : W := mkw 0x0bd226b0a1480088 0x42f489ac28520022 0xbffe3ffff9cc00cf 0xefff8ffffe730033

def z902 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x7ffff83807fffc3f 0xdffffe0e01ffff0f

def z903 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x3ffff80007cffc01 0x8ffffe0001f3ff00

def z904 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xbffffffff80c00cf 0xeffffffffe030033

def z905 : W := mkw 0x0970023005280028 0x425c008c014a000a 0xdff800f807fc03ff 0xf7fe003e01ff00ff

def z906 : W := mkw 0x1d35080005bed800 0x874d4200016fb600 0x7fffc00007fffc03 0xdffff00001ffff00

def z907 : W := mkw 0x3db7200005a8d000 0x8f6dc800016a3400 0x7fffc00007fffc03 0xdffff00001ffff00

def z908 : W := mkw 0x40e22b22ee376b30 0x10388ac8bb8ddacc 0xf1e63f27fe3fff33 0x7c798fc9ff8fffcc

def z909 : W := mkw 0xd02009024ef3f3b0 0x3408024093bcfcec 0x4000000007f3e330 0x1000000001fcf8cc

def z910 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0x9019f8fe383c1ffc 0xe4067e3f8e0f07ff

def z911 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x61e63f07fe33e331 0x18798fc1ff8cf8cc

def z912 : W := mkw 0x0bd266fdb0000001 0x02f499bf6c000000 0xaffe3ffff8000003 0xebff8ffffe000000

def z913 : W := mkw 0x1d3d980005be9800 0x074f6600016fa600 0x7ffff80007fffc03 0xdffffe0001ffff00

def z914 : W := mkw 0x7d3d99024fbffb30 0x9f4f664093effecc 0x5e19c00007ffff30 0x9786700001ffffcc

def z915 : W := mkw 0x1d35000005a89000 0x074d4000016a2400 0x7fe7c00007c3fc03 0x9ff9f00001f0ff00

def z916 : W := mkw 0x3fdff6fdb18c9c45 0x8ff7fdbf6c632711 0xbffffffff9cc1ccf 0xeffffffffe730733

def z917 : W := mkw 0xafdff6fdb04004c1 0x2bf7fdbf6c100130 0xaffffffff80000c3 0xebfffffffe000030

def z918 : W := mkw 0x24cff26db0000001 0x0933fc9b6c000000 0xa1fffffff8000003 0xe87ffffffe000000

def z919 : W := mkw 0x26cff6fdb0000001 0x09b3fdbf6c000000 0xa1e7fffff8000003 0x6879fffffe000000

def z920 : W := mkw 0x02c226a0a0000000 0x00b089a828000000 0xafe63fe7f8000003 0xebf98ff9fe000000

def z921 : W := mkw 0xc24047fffa4127f1 0x309011fffe9049fc 0x800007fff80003f0 0x200001fffe0000fc

def z922 : W := mkw 0x00c22220a0000000 0x0030888828000000 0xa1fe3ffff8000003 0xe87f8ffffe000000

def z923 : W := mkw 0x2ddff26db0000001 0x0b77fc9b6c000000 0xafffff27f8000003 0xebffffc9fe000000

def z924 : W := mkw 0x824047f7424127e8 0x609011fdd09049fa 0x800007c7c00003c0 0x200001f1f00000f0

def z925 : W := mkw 0x824047fff24127e9 0x609011fffc9049fa 0x800007fff80003fc 0x200001fffe0000ff

def z926 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xeffffffffe03e003 0xfbffffffff80f800

def z927 : W := mkw 0xd02009024ffffff0 0xb408024093fffffc 0x5000000007fffff0 0x1400000001fffffc

def z928 : W := mkw 0xd02009024ffbf7f8 0x7408024093fefdfe 0x5000000007fffffc 0x1400000001ffffff

def z929 : W := mkw 0xd02009024ef7fff4 0x3408024093bdfffd 0x5000000007fffffc 0x1400000001ffffff

def z930 : W := mkw 0x3dbfb808b5bed801 0x8f6fee022d6fb600 0x7ffff8003ffffc03 0xdffffe000fffff00

def z931 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe07c7c7c7ffffff 0xbf81f1f1f1ffffff

def z932 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0xd01800f8063fe3fe 0xf406003e018ff8ff

def z933 : W := mkw 0x40e22b22ee7363b0 0x10388ac8bb9cd8ec 0xf1e63f27fff3e3f3 0x7c798fc9fffcf8fc

def z934 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0xfffe07f807ffe3ff 0xffff81fe01fff8ff

def z935 : W := mkw 0x1938980005bed800 0x864e2600016fb600 0x7ff9f80007fffc03 0xdffe7e0001ffff00

def z936 : W := mkw 0x3fdff6fdb0809001 0x0ff7fdbf6c202400 0xaffffffff803fc03 0xebfffffffe00ff00

def z937 : W := mkw 0x748ff84ef897fd54 0x9d23fe13be25ff55 0x2007f807f803fc00 0x0801fe01fe00ff00

def z938 : W := mkw 0x00caf26cb0000000 0x0032bc9b2c000000 0xa1e7ff27f8000003 0x6879ffc9fe000000

def z939 : W := mkw 0x40e22b20e6326220 0x10388ac8398c9888 0xe1e63f27fe33e003 0x78798fc9ff8cf800

def z940 : W := mkw 0x9605058342c1b380 0x25814160d0b06ce0 0xfe07c707c7c3ff03 0xbf81f1c1f1f0ffc0

def z941 : W := mkw 0x2dd72220a0000000 0x0b75c88828000000 0xafe63f27f8000003 0x6bf98fc9fe000000

def z942 : W := mkw 0x2ddff27db0000001 0x0b77fc9f6c000000 0xa1ffff3ff8000003 0x687fffcffe000000

def z943 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0x7e07c707c7c3fc03 0x9f81f1c1f1f0ff00

def z944 : W := mkw 0x24cff26db0000001 0x0933fc9b6c000000 0x21e7ff07f8000001 0x0879ffc1fe000000

def z945 : W := mkw 0x1605048100809000 0x0581412040202400 0x7e07c701c7c3fc03 0x9f81f1c071f0ff00

def z946 : W := mkw 0x4028d94e5e376f74 0x100a3653978ddbdd 0x5019c0d8063ffffc 0x94067036018fffff

def z947 : W := mkw 0x02c266e5a0000000 0x00b099b968000000 0xa1e63fe7f8000003 0x68798ff9fe000000

def z948 : W := mkw 0x40c22220e0006000 0x1030888838001800 0xa1e63f27f800e003 0x68798fc9fe003800

def z949 : W := mkw 0xd6254dc74ef3f7f0 0x35895371d3bcfdfc 0x5e01c0c007f3fff0 0x9780703001fcfffc

def z950 : W := mkw 0x3dbfb8081dbed814 0x8f6fee02076fb605 0xfffff8f83fffffff 0xfffffe3e0fffffff

def z951 : W := mkw 0x026007a0066002a0 0x009801e8019800a8 0xdff807f807fc03ff 0xf7fe01fe01ff00ff

def z952 : W := mkw 0x3dbfb80005bed828 0xcf6fee00016fb60a 0x7ffff80007fffc3f 0xdffffe0001ffff0f

def z953 : W := mkw 0x960545d742c1b7c8 0x65815175d0b06df2 0xfe07c7dfc7c3ffcf 0xbf81f1f7f1f0fff3

def z954 : W := mkw 0x2bdab6b8b0000001 0x0af6adae2c000000 0xaffe3ffff8000003 0xebff8ffffe000000

def z955 : W := mkw 0x40e22a22ec336130 0x10388a88bb0cd84c 0xa1e63f27f833e033 0x68798fc9fe0cf80c

def z956 : W := mkw 0x14a7280005bed800 0x8529ca00016fb600 0x7fe7f80007fffc03 0xdff9fe0001ffff00

def z957 : W := mkw 0x3dbfb8081dbed814 0x8f6fee02076fb605 0x7ffff8003ffffc03 0xdffffe000fffff00

def z958 : W := mkw 0x9605058142c0b280 0x2581416050b02ca0 0x2e07c701c7c3fc01 0x0b81f1c071f0ff00

def z959 : W := mkw 0x40e22b22ee7363b8 0x50388ac8bb9cd8ee 0xe1e63f27fe33e3ff 0x78798fc9ff8cf8ff

def z960 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x2fffff07f8000003 0xcbffffc1fe000000

def z961 : W := mkw 0x3f1dd4dd11cc9889 0xcfc7753744732622 0x1e19c0d801cc1ccc 0x8786703600730733

def z962 : W := mkw 0x0b300590076802a8 0x42cc016401da00aa 0x5ff800d807fc03ff 0xd7fe003601ff00ff

def z963 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xafe7ffc7f8000003 0xabf9fff1fe000000

def z964 : W := mkw 0x40e22320e6206220 0x103888c839881888 0x21e63f07fe00e001 0x08798fc1ff803800

def z965 : W := mkw 0x960544c500c094c0 0x2581513140302530 0xfe07c7c7c7c3fcc3 0xbf81f1f1f1f0ff30

def z966 : W := mkw 0x24cfb220a0000000 0x0933ec8828000000 0xa1e7ff27f8000003 0x6879ffc9fe000000

def z967 : W := mkw 0x2fdff6fdb0040801 0x0bf7fdbf6c010200 0xbffffffff80c1c03 0xeffffffffe030700

def z968 : W := mkw 0x402009024e336774 0x10080240938cd9dd 0x400000000633e3fc 0x10000000018cf8ff

def z969 : W := mkw 0x3fdff6fdb0809001 0x0ff7fdbf6c202400 0xbffffffff9c01c03 0xeffffffffe700700

def z970 : W := mkw 0x2fdff6fdb0400081 0x0bf7fdbf6c100020 0xbffffffff9c000c3 0xeffffffffe700030

def z971 : W := mkw 0x0008d04c10040c44 0x0002341304010311 0xf019f8fe383c1ffe 0xfc067e3f8e0f07ff

def z972 : W := mkw 0x402009024e376f74 0x10080240938ddbdd 0x400000000633ff30 0x10000000018cffcc

def z973 : W := mkw 0x00600b224e332330 0x001802c8938cc8cc 0xe1e63f27fe33e333 0x78798fc9ff8cf8cc

def z974 : W := mkw 0x29faba38b53e4829 0xca7eae8e2d4f920a 0x01f83838383c003c 0x407e0e0e0e0f000f

def z975 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x9ff807f801fc03fc 0xe7fe01fe007f00ff

def z976 : W := mkw 0x2fdff6fdb10c0801 0x8bf7fdbf6c430200 0xaffffffff80c0003 0xebfffffffe030000

def z977 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xf1e63fe7fe33e3f3 0xfc798ff9ff8cf8fc

def z978 : W := mkw 0x4b7007b0e76822a8 0x52dc01ec39da08aa 0xdff807f9c7fc03ff 0xf7fe01fe71ff00ff

def z979 : W := mkw 0x40e22b32ee336338 0x50388accbb8cd8ce 0xe1e63f3ffe33e33f 0x78798fcfff8cf8cf

def z980 : W := mkw 0xc24047effa4127f4 0x309011fbfe9049fd 0x800007fff80003fc 0x200001fffe0000ff

def z981 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xfe19f8fe3fff1fff 0xff867e3f8fffc7ff

def z982 : W := mkw 0x40c22322ea012330 0x103088c8ba8048cc 0xe1e63f27fe03e333 0x78798fc9ff80f8cc

def z983 : W := mkw 0x00c22220a0000000 0x0030888828000000 0x21e63f07f8000001 0x08798fc1fe000000

def z984 : W := mkw 0x00caf26cb0040c44 0x0032bc9b2c010311 0xb1fffffff80c1ccf 0xec7ffffffe030733

def z985 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe1fc7ffc7c3ffc3 0xff87f1fff1f0fff0

def z986 : W := mkw 0x2fdff6fdb14c0ccd 0x4bf7fdbf6c530333 0xbffffffff9cc1ccf 0xeffffffffe730733

def z987 : W := mkw 0xc24047f7ea4127f8 0x709011fdfa9049fe 0x800007fff80003fc 0x200001fffe0000ff

def z988 : W := mkw 0x3db7200005a8d000 0x8f6dc800016a3400 0x2fe7c00007c3fc01 0x0bf9f00001f0ff00

def z989 : W := mkw 0x020045c6424127c0 0x00801171909049f0 0xfe07c7c7c7c3ffc3 0xbf81f1f1f1f0fff0

def z990 : W := mkw 0x29dab238b0000001 0x0a76ac8e2c000000 0x81f83f3ff8000000 0x607e0fcffe000000

def z991 : W := mkw 0xc02009024e7367f0 0x30080240939cd9fc 0x400000000633e3f0 0x10000000018cf8fc

def z992 : W := mkw 0x00e22a22ac334110 0x00388a88ab0cd044 0xe1e63f27fe33e333 0x78798fc9ff8cf8cc

def z993 : W := mkw 0x06c726a1a0000000 0x01b1c9a868000000 0xafe63f27f8000003 0x6bf98fc9fe000000

def z994 : W := mkw 0x0b30058007680280 0x02cc016001da00a0 0xdff807f807fc03ff 0xf7fe01fe01ff00ff

def z995 : W := mkw 0x0008d84e18170d54 0x000236138605c355 0xa019f8fe383f1ffc 0x68067e3f8e0fc7ff

def z996 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0x50000000063fe3fc 0x14000000018ff8ff

def z997 : W := mkw 0x40e22322e6216320 0x103888c8b98858c8 0xe1e63f27fe03e303 0x78798fc9ff80f8c0

def z998 : W := mkw 0x2fd766fdb0000001 0x0bf5d9bf6c000000 0xafe63ffff8000003 0x6bf98ffffe000000

def z999 : W := mkw 0x40c22b22ea136330 0x10308ac8ba84d8cc 0xa1e63f27f803e333 0x68798fc9fe00f8cc

def z1000 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0x600600000633e333 0x18018000018cf8cc

def z1001 : W := mkw 0x824047f7e24127c1 0x209011fdf89049f0 0x800007c7c00003c0 0x200001f1f00000f0

def z1002 : W := mkw 0x2bdaf6fdb0000001 0x0af6bdbf6c000000 0xa1fe3ffff8000003 0x687f8ffffe000000

def z1003 : W := mkw 0x40c22a22e8136110 0x10308a88ba04d844 0x21e63f07f803e001 0x08798fc1fe00f800

def z1004 : W := mkw 0xbf1dd4dd10c09081 0x2fc7753744302420 0x0e19c0d801c00000 0x8386703600700000

def z1005 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0xc00000200633e332 0x70000008018cf8cc

def z1006 : W := mkw 0x02c226b1a0000001 0x00b089ac68000000 0xa1e63f27f8000003 0x68798fc9fe000000

def z1007 : W := mkw 0x26cff6edb0000001 0x09b3fdbb6c000000 0xafe7ffe7f8000003 0xebf9fff9fe000000

def z1008 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xffe63f27fff3e333 0xfff98fc9fffcf8cc

def z1009 : W := mkw 0x9605058342c1b7c0 0x25814160d0b06df0 0x7e07c701c7c3ffc3 0x9f81f1c071f0fff0

def z1010 : W := mkw 0x2fdff6fdb1480089 0x4bf7fdbf6c520022 0xfffffffff9fc03ff 0xfffffffffe7f00ff

def z1011 : W := mkw 0x40e22b22ee376b34 0x10388ac8bb8ddacd 0xe1e63f27fe3fe33f 0x78798fc9ff8ff8cf

def z1012 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0x000000000603e000 0x000000000180f800

def z1013 : W := mkw 0x29faba30a53e4801 0x8a7eae8c294f9200 0x01f83800003c0000 0x407e0e00000f0000

def z1014 : W := mkw 0x0008d84c18160c54 0x0002361306058315 0xd019f8f8383c1ffe 0xf4067e3e0e0f07ff

def z1015 : W := mkw 0x0b7007b0076802a8 0x42dc01ec01da00aa 0x8ff807f807fc03fd 0x63fe01fe01ff00ff

def z1016 : W := mkw 0x2fd726b1a0000001 0x0bf5c9ac68000000 0x2fe63f07f8000001 0x0bf98fc1fe000000

def z1017 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe1fc7dfc7cfffcf 0xbf87f1f7f1f3fff3

def z1018 : W := mkw 0x402009024e7363b0 0x10080240939cd8ec 0x5000000007f3e3f0 0x1400000001fcf8fc

def z1019 : W := mkw 0x3ff727b1a7e8d2a9 0xcffdc9ec69fa34aa 0x0fe60701c7c0e001 0x03f981c071f03800

def z1020 : W := mkw 0x00c22b22ea132310 0x00308ac8ba84c8c4 0xe1e63f27fe33e333 0x78798fc9ff8cf8cc

def z1021 : W := mkw 0x2fdfb6b1a0000001 0x0bf7edac68000000 0xafffff27f8000003 0xebffffc9fe000000

def z1022 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xafe7ff27f8000003 0x6bf9ffc9fe000000

def z1023 : W := mkw 0x14c72220a0809000 0x0531c88828202400 0xffe7ff27ffc3fc03 0xfff9ffc9fff0ff00

def z1024 : W := mkw 0x00c2626db0000001 0x0030989b6c000000 0xa1e63f27f8000003 0x68798fc9fe000000

def z1025 : W := mkw 0xbf1dd4dd10809441 0x2fc7753744202510 0x0e19c0d800001c00 0x8386703600000700

def z1026 : W := mkw 0x2f9ff4cdb0000001 0x0be7fd336c000000 0xafffffc7f8000003 0xebfffff1fe000000

def z1027 : W := mkw 0xd48ff84ff897fd54 0x3523fe13fe25ff55 0x2007f807f803fc00 0x0801fe01fe00ff00

def z1028 : W := mkw 0x824047ff5a4127fc 0x609011ffd69049ff 0x800007fff80003fc 0x200001fffe0000ff

def z1029 : W := mkw 0x8008d84f58172d54 0x20023613d605cb55 0xf019f8fff83f1ffe 0xfc067e3ffe0fc7ff

def z1030 : W := mkw 0x0bdaf6fcb0000000 0x02f6bdbf2c000000 0xaffffffff8000003 0xebfffffffe000000

def z1031 : W := mkw 0xb48ff84ff897bd55 0x2d23fe13fe25ef55 0x2007f807f803fc00 0x0801fe01fe00ff00

def z1032 : W := mkw 0x1605058242c1b380 0x0581416090b06ce0 0xfe07c7c7c7c3ffc3 0xbf81f1f1f1f0fff0

def z1033 : W := mkw 0x00e22b20a6324220 0x00388ac8298c9088 0xe1e63f27fe33e333 0x78798fc9ff8cf8cc

def z1034 : W := mkw 0x402009024f7f6ffc 0x5008024093dfdbff 0x5000000007fffffc 0x1400000001ffffff

def z1035 : W := mkw 0x824047f7424127c0 0x209011fdd09049f0 0x800007ffc00003c0 0x200001fff00000f0

def z1036 : W := mkw 0x02c226b0a0000000 0x00b089ac28000000 0xa1e63ffff8000003 0x68798ffffe000000

def z1037 : W := mkw 0x3fdff6fdb0849801 0x8ff7fdbf6c212600 0xaffffffff8001c03 0xebfffffffe000700

def z1038 : W := mkw 0x2fdff6fdb1080009 0x4bf7fdbf6c420002 0xaffffffff80c000f 0xebfffffffe030003

def z1039 : W := mkw 0x2fdff6fdb0000029 0x4bf7fdbf6c00000a 0xaffffffff800003f 0xebfffffffe00000f

def z1040 : W := mkw 0x1d15000000809000 0x0745400000202400 0x7fffc00007c3fc03 0xdffff00001f0ff00

def z1041 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xa1fffffff8000000 0x687ffffffe000000

def z1042 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xa1e63f27f833e330 0x68798fc9fe0cf8cc

def z1043 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xafe7fffff8000001 0x2bf9fffffe000000

def z1044 : W := mkw 0x960545cf5ac1b7d4 0x25815173d6b06df5 0xfe07c7c7ffc3ffc3 0xbf81f1f1fff0fff0

def z1045 : W := mkw 0x29dab220a0000000 0x0a76ac8828000000 0xa1fe3f27f8000003 0x687f8fc9fe000000

def z1046 : W := mkw 0x960545cf52c1b7c4 0x25815173d4b06df1 0xfe07c7dfc7c3ffcf 0xbf81f1f7f1f0fff3

def z1047 : W := mkw 0x960545c74ac1b7d0 0x25815171d2b06df4 0xfe07c7e7ffc3fff3 0xbf81f1f9fff0fffc

def z1048 : W := mkw 0x402009024e336330 0x10080240938cd8cc 0x0000000000300330 0x00000000000c00cc

def z1049 : W := mkw 0x00e22b22e6336300 0x00388ac8b98cd8c0 0xe1e63f27fe33e303 0x78798fc9ff8cf8c0

def z1050 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xfe07c7ffc7c3ffff 0xbf81f1fff1f0ffff

def z1051 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x7fe7f80007c3fc03 0x9ff9fe0001f0ff00

def z1052 : W := mkw 0x0008d84c10160800 0x0002361304058200 0xf019f8fe383f1ffe 0xfc067e3f8e0fc7ff

def z1053 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0xfffff8f807fffc03 0xfffffe3e01ffff00

def z1054 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x2ffff80007c3fc03 0xcbfffe0001f0ff00

def z1055 : W := mkw 0x960545c742c1b7c0 0x25815171d0b06df0 0xae07c7c7c7c3ffc1 0x2b81f1f1f1f0fff0

def z1056 : W := mkw 0x402009024e7363b8 0x50080240939cd8ee 0x400000000633e3fc 0x10000000018cf8ff

def z1057 : W := mkw 0x2fdff6fdb0040c45 0x0bf7fdbf6c010311 0xaffffffff8001c03 0xebfffffffe000700

def z1058 : W := mkw 0x2bdaf6fdb0000001 0x0af6bdbf6c000000 0xa1f9fffff8000002 0xe87e7ffffe000000

def z1059 : W := mkw 0x960545c742c1b7e8 0x65815171d0b06dfa 0xfe07c7c7c7c3ffff 0xbf81f1f1f1f0ffff

def z1060 : W := mkw 0x3dbfb00005a8d000 0x8f6fec00016a3400 0x7ffff80007c3fc03 0xdffffe0001f0ff00

def z1061 : W := mkw 0x00c2626cb0000000 0x0030989b2c000000 0xa1e63ffff8000003 0x68798ffffe000000

def z1062 : W := mkw 0x0b7007b0476822a8 0x42dc01ec11da08aa 0xdffe07f9c7fce3ff 0xf7ff81fe71ff38ff

def z1063 : W := mkw 0x9405010242c1b7c0 0x2501404090b06df0 0xfe07c707c7c3ffc3 0xbf81f1c1f1f0fff0

def z1064 : W := mkw 0x3d9fb8000096d800 0x8f67ee000025b600 0x7ffff80007c3fc03 0xdffffe0001f0ff00

def z1065 : W := mkw 0x0b58d6fdb0000001 0x02d635bf6c000000 0xaff9fffff8000003 0xebfe7ffffe000000

def z1066 : W := mkw 0x29d22230a0000001 0x0a74888c28000000 0xa1e63f27f8000003 0x68798fc9fe000000

def z1067 : W := mkw 0xbfdff6fdb0c094c1 0x2ff7fdbf6c302530 0xffffffffffc3fcc3 0xfffffffffff0ff30

def z1068 : W := mkw 0x00c22220a0000000 0x0030888828000000 0xf1fe3ffff83c03ff 0xfc7f8ffffe0f00ff

def z1069 : W := mkw 0x02caf6fdb0000001 0x00b2bdbf6c000000 0xa1fffffff8000003 0xe87ffffffe000000

def z1070 : W := mkw 0x00a229024e336310 0x00288a40938cd8c4 0xe1e63f27fe33e333 0x78798fc9ff8cf8cc

def z1071 : W := mkw 0xc24047e7e24127e0 0x309011f9f89049f8 0x800007c7c00003c0 0x200001f1f00000f0

def z1072 : W := mkw 0x09d22220a0000000 0x0274888828000000 0xaffe3f27f8000003 0xebff8fc9fe000000

def z1073 : W := mkw 0x2fdff6fdb0040805 0x0bf7fdbf6c010201 0xaffffffff80c000f 0xebfffffffe030003

def z1074 : W := mkw 0x3fdff6fdb1889001 0x8ff7fdbf6c622400 0xaffffffff9c00003 0xebfffffffe700000

def z1075 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x81e63f27fe30e331 0x60798fc9ff8c38cc

def z1076 : W := mkw 0x0fd766f5a0000000 0x03f5d9bd68000000 0xaffffffff8000003 0xebfffffffe000000

def z1077 : W := mkw 0x402009024e376b30 0x10080240938ddacc 0x50000000063fff30 0x14000000018fffcc

def z1078 : W := mkw 0x960545c542c0b280 0x2581517150b02ca0 0xfe07c7c7c7c3fc03 0xbf81f1f1f1f0ff00

def z1079 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xeffffffff8300333 0xfbfffffffe0c00cc

def z1080 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x2fffffdff8000001 0x8bfffff7fe000000

def z1081 : W := mkw 0x3db7280005bad000 0x8f6dca00016eb400 0x7fe7f80007f3fc03 0xdff9fe0001fcff00

def z1082 : W := mkw 0x9f1dd4dd11cc9ccc 0x67c7753744732733 0x1e19c0d801cc1ccc 0x8786703600730733

def z1083 : W := mkw 0x20cab228b0000001 0x0832ac8a2c000000 0xa1e63f27f8000003 0x68798fc9fe000000

def z1084 : W := mkw 0x2fd726b1a0000001 0x0bf5c9ac68000000 0xaffe3ffff8000003 0xebff8ffffe000000

def z1085 : W := mkw 0xb48ff84f5897fd54 0xad23fe13d625ff55 0x2007f807f803fc00 0x0801fe01fe00ff00

def z1086 : W := mkw 0x06c766fdb0000001 0x01b1d9bf6c000000 0xafe7fffff8000003 0xebf9fffffe000000

def z1087 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x7fe7f80007fffc01 0x1ff9fe0001ffff00

def z1088 : W := mkw 0x502009024fbfff74 0x9408024093efffdd 0x5000000007fffffc 0x1400000001ffffff

def z1089 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xf1e7ff27fe33ff33 0xfc79ffc9ff8cffcc

def z1090 : W := mkw 0x3d97200000809000 0x0f65c80000202400 0x7fe7c00007c3fc03 0x9ff9f00001f0ff00

def z1091 : W := mkw 0x402009024e376b34 0x10080240938ddacd 0x40000000063fe33c 0x10000000018ff8cf

def z1092 : W := mkw 0x3fdff6fdb18c9801 0x8ff7fdbf6c632600 0xffffffffffcffc03 0xfffffffffff3ff00

def z1093 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x2ffff80007fffc01 0x4bfffe0001ffff00

def z1094 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0xfffffffff80003c3 0xfffffffffe0000f0

def z1095 : W := mkw 0x0008980818160814 0x0002260206058205 0xf019f8f8383f1ffe 0xfc067e3e0e0fc7ff

def z1096 : W := mkw 0x3fdff6fdb1cc9889 0xcff7fdbf6c732622 0xbffffffff9cc1ccf 0xeffffffffe730733

def z1097 : W := mkw 0x69faba38bd3e4831 0x9a7eae8e2f4f920c 0x01f83838383c0030 0x407e0e0e0e0f000c

def z1098 : W := mkw 0xc0e22b22ee7367f0 0x30388ac8bb9cd9fc 0xe1e63f27fe33e3f3 0x78798fc9ff8cf8fc

def z1099 : W := mkw 0x0b7006b005280000 0x02dc01ac014a0000 0xdff807f807fc03ff 0xf7fe01fe01ff00ff

def z1100 : W := mkw 0x502009024fbbf330 0x9408024093eefccc 0x4000000007f3e330 0x1000000001fcf8cc

def z1101 : W := mkw 0x402009024f3b6330 0x1008024093ced8cc 0x5000000007ffe330 0x1400000001fff8cc

def z1102 : W := mkw 0x2fdfb6b0a0000000 0x0bf7edac28000000 0xaffffffff8000003 0xebfffffffe000000

def z1103 : W := mkw 0x2ddff26cb0000000 0x0b77fc9b2c000000 0xaffffffff8000003 0xebfffffffe000000

def z1104 : W := mkw 0xbf1dd4dd11cc9cc1 0xafc7753744732730 0x1e19c0d801cc1cc0 0x8786703600730730

def z1105 : W := mkw 0xbf1dd4dd11c894c9 0x6fc7753744722532 0x1e19c0d801cc1ccc 0x8786703600730733

def z1106 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0xe1fe3ffffe33e333 0xf87f8fffff8cf8cc

def z1107 : W := mkw 0x40e22b22ee336330 0x10388ac8bb8cd8cc 0x21e63f27fe33e031 0x48798fc9ff8cf80c

def z1108 : W := mkw 0x29faba38bd3e4815 0x8a7eae8e2f4f9205 0x01f83838383c003c 0x407e0e0e0e0f000f

def z1109 : W := mkw 0xbf1dd4dd10c49cc5 0x2fc7753744312731 0x1e19c0d801cc1ccc 0x8786703600730733

def z1110 : W := mkw 0x3dbfb80815bed800 0x8f6fee02056fb600 0x7ffff8383ffffc03 0xdffffe0e0fffff00

def z1111 : W := mkw 0x1425000004a09000 0x0509400001282400 0x7fe7c00007f3fc03 0xdff9f00001fcff00

def z1112 : W := mkw 0xdff727b1e7e8f2a8 0x77fdc9ec79fa3caa 0x0fe60701c7c0e001 0x03f981c071f03800

def z1113 : W := mkw 0x34afb80004b6d800 0x8d2bee00012db600 0x7fe7f80007f3fc03 0xdff9fe0001fcff00

def z1114 : W := mkw 0x00c22238b0000001 0x0030888e2c000000 0xa1e63f3ff8000003 0x68798fcffe000000

def z1115 : W := mkw 0x3dbfb80005bed800 0x8f6fee00016fb600 0x7ffff80007ffffff 0xdffffe0001ffffff

def z1116 : W := mkw 0x2fdff6fdb0000001 0x0bf7fdbf6c000000 0x8ffe3ffff8000001 0x63ff8ffffe000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z7,z2,z3,z4,z6]),(0,[z0,z1,z8,z3,z9,z4,z6]),(0,[z10,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z12,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z13,z4,z6]),(0,[z0,z1,z14,z2,z3,z4,z6])],[(0,[z0,z1,z15,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z16,z4,z6]),(0,[z0,z17,z1,z2,z3,z4,z18])],[],[(0,[z0,z1,z2,z3,z19,z4,z6]),(0,[z0,z1,z2,z20,z3,z4,z6]),(0,[z0,z21,z1,z2,z3,z4,z6]),(1,[z0,z12,z1,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z23,z6])],[(0,[z0,z1,z2,z3,z24,z4,z6]),(0,[z0,z1,z2,z3,z4,z25,z6]),(0,[z0,z1,z26,z2,z3,z4,z6]),(0,[z0,z27,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z28,z6])],[(0,[z0,z29,z1,z2,z3,z4,z6]),(0,[z0,z1,z30,z2,z3,z4,z6]),(0,[z0,z17,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z31,z4,z6,z18]),(0,[z0,z11,z1,z2,z3,z32,z6])],[(0,[z0,z1,z2,z3,z4,z6,z33]),(0,[z0,z1,z2,z3,z4,z22,z6])],[(0,[z34,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z35,z2,z3,z4,z6]),(0,[z0,z1,z36,z2,z3,z4,z6]),(0,[z0,z1,z37,z3,z38,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z39,z6]),(0,[z40,z1,z2,z3,z41,z4,z6]),(0,[z0,z42,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z43,z4,z6]),(0,[z0,z44,z1,z2,z3,z4,z6])],[(0,[z45,z0,z1,z2,z3,z4,z6]),(0,[z46,z0,z1,z47,z3,z4,z6]),(0,[z0,z1,z2,z3,z48,z4,z6]),(0,[z0,z12,z1,z49,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z50]),(0,[z0,z1,z51,z2,z3,z4,z6])],[(0,[z0,z12,z1,z52,z3,z4,z6]),(0,[z53,z0,z1,z2,z3,z4,z6]),(0,[z0,z54,z1,z2,z3,z4,z6]),(0,[z0,z1,z55,z3,z56,z4,z6]),(1,[z0,z1,z2,z3,z6,z57])],[(0,[z0,z1,z49,z52,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z58,z6]),(0,[z59,z0,z1,z60,z2,z3,z4]),(0,[z0,z1,z61,z2,z4,z6,z62])],[(0,[z0,z1,z2,z63,z3,z4,z6]),(0,[z64,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z65,z4,z6]),(0,[z0,z1,z66,z2,z3,z4,z6]),(0,[z0,z11,z12,z1,z3,z4,z6])],[(0,[z67,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z68,z2,z3,z4,z6]),(0,[z0,z1,z3,z69,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z70,z6]),(0,[z71,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z9,z4,z6,z18])],[(0,[z0,z1,z2,z3,z4,z72,z6]),(0,[z0,z1,z73,z2,z3,z4,z6]),(1,[z0,z12,z1,z3,z74,z6]),(0,[z0,z75,z2,z76,z3,z4,z6]),(0,[z0,z1,z2,z3,z77,z4,z6]),(0,[z0,z1,z2,z3,z4,z78,z6]),(0,[z0,z1,z79,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z80,z6,z81]),(0,[z0,z82,z1,z2,z9,z4,z6]),(0,[z0,z1,z3,z83,z56,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z18])],[(0,[z0,z84,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z85]),(0,[z0,z1,z2,z3,z4,z86,z6]),(0,[z0,z1,z2,z3,z4,z87,z6])]],
   [[(0,[z0,z88,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z89,z3,z4,z6]),(0,[z90,z0,z1,z2,z3,z4,z6])],[(1,[z91,z1,z2,z3,z4,z92]),(0,[z0,z1,z2,z3,z4,z93,z6]),(0,[z94,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z3,z95,z6]),(0,[z96,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z97,z3,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z6]),(0,[z0,z1,z2,z98,z3,z4,z6]),(0,[z0,z1,z99,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z100]),(0,[z101,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z102,z6])],[(1,[z0,z1,z3,z103,z4,z6]),(0,[z104,z0,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z105,z4,z6]),(0,[z106,z0,z1,z2,z3,z4,z6]),(0,[z107,z0,z1,z3,z56,z4,z6]),(0,[z0,z17,z1,z108,z2,z3,z4]),(1,[z0,z109,z1,z2,z3,z6])],[(0,[z0,z1,z2,z110,z4,z111,z6]),(0,[z0,z1,z3,z24,z4,z5,z6]),(0,[z91,z0,z1,z2,z3,z4,z112]),(0,[z0,z1,z113,z2,z3,z9,z4]),(0,[z0,z114,z1,z2,z3,z4,z6]),(0,[z115,z0,z1,z2,z3,z4,z6])],[(0,[z0,z12,z1,z3,z4,z5,z6]),(1,[z0,z116,z1,z3,z4,z6])]],
   [[(0,[z107,z0,z1,z2,z3,z74,z6]),(0,[z46,z0,z12,z1,z3,z4,z6]),(0,[z117,z0,z1,z2,z3,z4,z6]),(0,[z0,z118,z1,z119,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z120,z62])],[(0,[z0,z121,z1,z2,z3,z4,z6]),(0,[z0,z122,z1,z2,z3,z4,z6])],[(0,[z123,z0,z1,z2,z3,z4,z6]),(0,[z124,z0,z1,z52,z3,z4,z6]),(0,[z0,z125,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z126,z110,z4,z6]),(0,[z0,z1,z127,z2,z3,z4,z6]),(0,[z0,z1,z2,z128,z3,z4,z6]),(0,[z129,z0,z1,z2,z3,z4,z6]),(0,[z0,z130,z1,z2,z3,z4,z6]),(0,[z0,z82,z1,z3,z4,z6,z18]),(0,[z0,z131,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z132]),(0,[z0,z11,z1,z108,z2,z4,z6])],[(1,[z133,z1,z2,z110,z4,z6]),(0,[z0,z12,z134,z1,z3,z4,z6]),(0,[z0,z135,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z136,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z137]),(0,[z0,z1,z2,z3,z138,z4,z6]),(0,[z139,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z140,z4,z6]),(0,[z0,z1,z2,z3,z4,z141,z6]),(0,[z0,z1,z142,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z143,z9,z6]),(0,[z0,z12,z1,z3,z4,z22,z6]),(0,[z0,z1,z144,z2,z3,z4,z6]),(0,[z0,z145,z1,z2,z3,z4,z6])],[(0,[z146,z0,z1,z2,z3,z4,z6]),(1,[z0,z12,z1,z3,z147,z6]),(0,[z148,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z111,z6])],[(0,[z0,z12,z1,z3,z69,z4,z6]),(0,[z0,z149,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z150,z3,z4,z6])]],
   [[(0,[z0,z151,z1,z2,z3,z4,z6]),(0,[z0,z152,z1,z108,z2,z4,z6]),(1,[z0,z11,z12,z1,z3,z6])],[(0,[z0,z12,z1,z153,z3,z4,z6]),(1,[z146,z1,z55,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z154]),(0,[z0,z17,z1,z2,z3,z4,z155]),(0,[z156,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z147,z6])],[(0,[z0,z152,z1,z2,z126,z4,z6]),(0,[z0,z134,z1,z2,z3,z4,z6]),(0,[z0,z157,z1,z2,z3,z4,z6]),(1,[z0,z1,z158,z3,z4,z6])],[(0,[z0,z1,z159,z2,z3,z4,z6]),(0,[z0,z160,z12,z1,z3,z4,z6])],[(0,[z0,z161,z1,z2,z3,z4,z6]),(0,[z0,z162,z1,z2,z3,z4,z6]),(0,[z0,z163,z2,z3,z4,z164,z6]),(0,[z0,z1,z2,z3,z165,z4,z6]),(0,[z0,z166,z1,z2,z3,z4,z6]),(0,[z0,z167,z1,z2,z3,z4,z6])],[(0,[z0,z1,z168,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z169,z6]),(0,[z0,z1,z170,z2,z3,z4,z6]),(0,[z0,z171,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z172,z6]),(0,[z0,z1,z60,z2,z3,z4,z112]),(0,[z0,z173,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z174,z3,z4,z6]),(0,[z0,z175,z1,z3,z56,z4,z6]),(1,[z0,z1,z2,z31,z4,z6])],[(0,[z0,z1,z2,z3,z4,z176,z6])]],
   [[(0,[z0,z177,z1,z2,z3,z4,z6]),(0,[z0,z1,z8,z3,z4,z155,z6]),(0,[z0,z178,z1,z2,z3,z4,z6]),(0,[z0,z1,z179,z2,z3,z4,z6])],[(0,[z0,z180,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z181,z4,z6]),(0,[z0,z12,z1,z108,z3,z4,z6])],[(0,[z0,z12,z182,z1,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z183,z6]),(0,[z184,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z185,z6]),(0,[z0,z1,z60,z2,z4,z111,z6])],[(0,[z186,z0,z1,z2,z3,z4,z6]),(1,[z0,z187,z2,z3,z4,z6]),(1,[z0,z12,z1,z3,z164,z6]),(0,[z0,z1,z188,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z189,z6]),(0,[z0,z1,z2,z31,z3,z4,z6]),(0,[z0,z1,z2,z190,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z4,z6,z191]),(1,[z0,z192,z49,z3,z4,z6]),(0,[z0,z163,z1,z2,z3,z4,z6]),(0,[z193,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z194,z4,z6]),(0,[z0,z1,z2,z3,z4,z195,z6]),(0,[z0,z1,z2,z3,z4,z164,z6]),(0,[z0,z1,z2,z3,z196,z4,z6]),(0,[z0,z1,z8,z2,z3,z4,z155]),(0,[z0,z1,z197,z2,z3,z4,z6])],[(0,[z0,z198,z1,z2,z3,z4,z6]),(0,[z0,z1,z199,z2,z3,z4,z6])]],
   [[(0,[z107,z0,z12,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z200,z4,z6]),(0,[z0,z201,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z202,z6]),(0,[z0,z1,z203,z2,z3,z4,z6]),(0,[z0,z82,z1,z2,z3,z4,z6]),(0,[z0,z1,z89,z3,z56,z4,z6]),(0,[z0,z12,z1,z37,z3,z4,z6])],[(0,[z107,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z204,z6]),(0,[z0,z1,z2,z205,z3,z4,z6]),(0,[z0,z1,z206,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z207,z6]),(0,[z0,z208,z1,z2,z3,z4,z6]),(0,[z0,z209,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z4,z111,z6])],[(0,[z0,z1,z2,z3,z4,z210,z6]),(0,[z46,z0,z1,z2,z3,z5,z6]),(0,[z211,z0,z1,z2,z3,z4,z6])],[(0,[z212,z151,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z47,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z213,z6]),(0,[z0,z17,z1,z60,z2,z3,z4]),(0,[z0,z1,z158,z3,z4,z147,z6])],[(0,[z91,z0,z1,z2,z3,z4,z6]),(0,[z0,z12,z17,z1,z3,z4,z6])],[(0,[z0,z214,z1,z2,z3,z4,z6]),(0,[z0,z215,z1,z2,z3,z4,z6]),(0,[z0,z1,z216,z2,z9,z4,z6]),(0,[z0,z1,z217,z2,z3,z9,z4]),(0,[z218,z0,z1,z2,z3,z4,z6]),(0,[z0,z219,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z220,z6]),(0,[z0,z1,z221,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z222,z6]),(0,[z0,z163,z1,z2,z3,z164,z6]),(0,[z0,z1,z2,z3,z4,z223,z6])],[(0,[z0,z1,z1,z2,z3,z4,z6]),(0,[z224,z0,z1,z225,z3,z4,z6]),(0,[z0,z1,z226,z2,z3,z4,z6]),(0,[z0,z1,z2,z227,z3,z4,z6]),(0,[z0,z1,z2,z4,z228,z6,z18]),(0,[z0,z1,z2,z3,z4,z6,z229])]],
   [[(0,[z0,z1,z2,z3,z4,z230,z6]),(0,[z0,z12,z118,z1,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z147,z6]),(0,[z0,z1,z2,z3,z4,z6,z231])],[(0,[z232,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z233,z2,z3,z4,z6]),(0,[z0,z1,z234,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z6,z235])],[(0,[z133,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z236,z2,z3,z4,z6]),(0,[z0,z237,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z238,z2,z3,z6]),(0,[z0,z1,z239,z2,z3,z4,z6])],[(0,[z0,z12,z1,z55,z3,z4,z6]),(0,[z240,z0,z1,z2,z3,z4,z6]),(0,[z133,z0,z1,z2,z3,z4,z241]),(0,[z0,z1,z3,z56,z4,z6,z112]),(0,[z0,z242,z1,z2,z3,z4,z6]),(0,[z0,z1,z243,z2,z3,z4,z6]),(0,[z0,z1,z2,z37,z95,z4,z6])],[(0,[z0,z244,z1,z2,z3,z4,z6]),(0,[z0,z1,z49,z55,z3,z4,z6]),(0,[z245,z0,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z4,z6]),(0,[z0,z1,z2,z246,z3,z4,z6])],[(0,[z0,z1,z2,z3,z247,z4,z6]),(0,[z0,z1,z2,z3,z4,z248,z6]),(0,[z0,z1,z249,z2,z3,z4,z6])],[(0,[z0,z0,z1,z2,z3,z4,z6]),(1,[z124,z1,z52,z3,z4,z6]),(0,[z1,z55,z2,z52,z3,z4,z6]),(0,[z146,z0,z1,z2,z3,z250,z6]),(0,[z251,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z252,z6]),(0,[z0,z182,z1,z2,z3,z4,z81]),(0,[z0,z182,z1,z3,z56,z4,z6]),(0,[z0,z12,z1,z3,z56,z4,z6]),(0,[z0,z1,z3,z56,z4,z155,z6]),(0,[z0,z1,z2,z3,z4,z6,z253]),(0,[z0,z1,z3,z4,z147,z6,z253])],[(0,[z0,z1,z2,z3,z4,z6,z254]),(0,[z0,z1,z2,z3,z255,z4,z6]),(0,[z0,z256,z1,z2,z3,z4,z6]),(0,[z257,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z258]),(0,[z0,z1,z259,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z41,z4,z6]),(0,[z0,z1,z2,z3,z4,z260,z6]),(0,[z59,z0,z1,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z261]),(0,[z0,z262,z1,z2,z3,z4,z6]),(0,[z263,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z264,z4,z6]),(0,[z133,z0,z1,z2,z3,z4,z265])],[(0,[z266,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z41,z56,z4,z6]),(0,[z0,z1,z2,z3,z267,z4,z6]),(0,[z0,z1,z2,z3,z4,z268,z6])],[(0,[z0,z1,z2,z225,z3,z4,z6]),(0,[z46,z0,z1,z2,z3,z74,z6]),(0,[z269,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z32,z6]),(0,[z0,z1,z108,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z228,z6]),(0,[z0,z1,z2,z3,z270,z4,z147])],[(0,[z0,z1,z2,z271,z3,z4,z6]),(0,[z146,z1,z55,z2,z3,z4,z6]),(0,[z0,z173,z2,z126,z3,z4,z6]),(1,[z0,z1,z272,z3,z4,z6]),(0,[z0,z1,z273,z3,z56,z4,z6])],[(0,[z274,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z275,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z164,z6]),(0,[z0,z1,z216,z3,z9,z4,z6]),(0,[z0,z276,z1,z2,z3,z4,z6]),(0,[z0,z277,z1,z2,z3,z4,z6])],[(0,[z224,z0,z1,z2,z3,z4,z258]),(0,[z224,z0,z152,z2,z3,z4,z6]),(0,[z0,z1,z153,z3,z56,z4,z6]),(0,[z0,z12,z151,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z278,z4,z6]),(1,[z0,z1,z113,z2,z3,z4]),(0,[z0,z1,z2,z3,z270,z4,z62])],[(0,[z0,z1,z2,z3,z4,z6,z279])]],
   [[(0,[z0,z1,z2,z3,z280,z4,z6]),(0,[z0,z192,z1,z76,z3,z4,z6]),(0,[z0,z281,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z147,z6,z62])],[(0,[z1,z2,z3,z4,z92,z6,z112]),(0,[z0,z282,z1,z2,z3,z4,z6]),(0,[z283,z0,z12,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z38,z4,z6])],[(0,[z107,z0,z1,z2,z3,z5,z6]),(0,[z0,z118,z1,z2,z3,z4,z6]),(0,[z0,z1,z284,z3,z4,z164,z6]),(1,[z0,z1,z3,z56,z4,z6])],[(0,[z124,z0,z1,z55,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z285,z6]),(0,[z0,z1,z2,z3,z69,z4,z6]),(0,[z0,z1,z2,z3,z4,z286,z6]),(0,[z0,z1,z2,z3,z143,z4,z6]),(0,[z0,z1,z2,z3,z287,z4,z6]),(0,[z0,z1,z2,z288,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z289,z6]),(0,[z0,z290,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z291,z6]),(0,[z0,z292,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z293]),(0,[z59,z0,z1,z2,z3,z270,z6])],[(0,[z40,z0,z12,z1,z3,z4,z6]),(0,[z0,z12,z166,z1,z3,z4,z6]),(0,[z0,z1,z2,z273,z3,z4,z6]),(0,[z0,z1,z294,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z295,z4,z6]),(0,[z0,z296,z1,z2,z3,z4,z6]),(0,[z297,z0,z1,z2,z3,z4,z6]),(0,[z0,z298,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z6,z62])],[(0,[z0,z299,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z80,z6]),(0,[z0,z1,z300,z2,z3,z4,z6]),(1,[z59,z0,z12,z1,z3,z6]),(0,[z59,z0,z12,z1,z2,z3,z6])]],
   [[(0,[z0,z1,z60,z2,z3,z4,z92]),(0,[z0,z192,z1,z2,z3,z301,z6]),(0,[z0,z1,z2,z3,z4,z6,z302]),(0,[z0,z1,z2,z3,z4,z6,z303]),(0,[z0,z1,z2,z3,z304,z4,z6]),(0,[z0,z1,z3,z56,z305,z4,z6]),(0,[z0,z134,z2,z3,z4,z80,z6]),(0,[z0,z1,z238,z3,z56,z4,z6])],[(0,[z212,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z306,z4,z6]),(0,[z0,z1,z2,z3,z4,z307,z6]),(0,[z0,z1,z2,z3,z308,z4,z6]),(0,[z0,z152,z1,z2,z3,z4,z6]),(0,[z0,z12,z152,z1,z3,z4,z6]),(0,[z309,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z305,z74,z6]),(0,[z0,z1,z3,z56,z4,z6,z310])],[(0,[z0,z311,z1,z2,z3,z4,z6]),(0,[z0,z118,z1,z2,z3,z164,z6]),(0,[z0,z1,z2,z3,z4,z312,z6]),(1,[z0,z313,z1,z3,z4,z6])],[(0,[z0,z1,z2,z314,z3,z4,z6]),(0,[z0,z315,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z267,z4,z6]),(0,[z0,z1,z2,z126,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z6,z18]),(0,[z0,z109,z1,z2,z3,z4,z6])],[(0,[z316,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z47,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z317,z6]),(0,[z0,z1,z2,z3,z4,z301,z6]),(0,[z0,z318,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z319,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z183,z6]),(1,[z0,z1,z2,z4,z228,z6]),(0,[z0,z11,z1,z2,z4,z32,z6])],[(0,[z320,z0,z1,z2,z3,z4,z6]),(0,[z0,z192,z1,z2,z3,z65,z6]),(0,[z0,z2,z3,z305,z4,z164,z6]),(0,[z0,z1,z216,z2,z3,z4,z6]),(0,[z0,z321,z1,z2,z3,z4,z6]),(0,[z322,z0,z12,z1,z3,z4,z6])]],
   [[(0,[z323,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z110,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z324,z4,z6]),(0,[z0,z75,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z81])],[(0,[z146,z0,z1,z2,z3,z325,z6]),(1,[z46,z1,z2,z3,z74,z6]),(0,[z0,z326,z1,z2,z3,z4,z6]),(1,[z0,z118,z2,z3,z305,z6]),(0,[z0,z12,z12,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z327,z4,z6])],[(0,[z0,z328,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z95,z4,z6]),(0,[z0,z1,z2,z3,z329,z4,z6])],[(0,[z0,z330,z1,z2,z3,z4,z6]),(0,[z0,z331,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z332,z6]),(0,[z59,z0,z12,z1,z3,z4,z6])],[(0,[z0,z1,z333,z2,z3,z4,z6]),(0,[z0,z1,z334,z2,z3,z4,z6]),(0,[z335,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z37,z3,z4,z6])],[(0,[z224,z1,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z336,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z337]),(0,[z0,z1,z2,z3,z4,z6,z338])],[(0,[z224,z0,z1,z3,z56,z4,z6]),(0,[z339,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z340,z6]),(0,[z0,z341,z12,z1,z3,z4,z6]),(0,[z0,z1,z342,z2,z3,z4,z6]),(0,[z0,z343,z1,z2,z3,z4,z6]),(0,[z344,z0,z1,z2,z3,z4,z6])],[(0,[z0,z345,z1,z2,z3,z4,z6]),(0,[z59,z0,z1,z2,z3,z4,z147])]],
   [[(0,[z0,z1,z2,z3,z4,z325,z6]),(0,[z0,z1,z2,z3,z346,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z347]),(0,[z0,z1,z2,z3,z4,z6,z348]),(1,[z0,z1,z3,z4,z6,z253])],[(0,[z0,z1,z2,z349,z3,z4,z6]),(0,[z0,z1,z108,z2,z110,z4,z6]),(0,[z0,z1,z2,z350,z3,z4,z6]),(0,[z0,z192,z1,z2,z3,z4,z6]),(1,[z0,z12,z1,z3,z305,z6]),(0,[z0,z1,z2,z3,z4,z6,z351]),(0,[z352,z0,z1,z2,z3,z4,z6]),(0,[z59,z0,z1,z2,z3,z4,z62])],[(0,[z0,z353,z1,z2,z3,z4,z6]),(0,[z0,z1,z354,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z355,z6])],[(0,[z224,z0,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z356,z6]),(0,[z0,z1,z55,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z357])],[(0,[z0,z358,z1,z2,z3,z4,z6]),(0,[z359,z0,z1,z2,z3,z4,z6]),(0,[z0,z152,z2,z3,z69,z4,z6]),(0,[z0,z82,z1,z89,z3,z4,z6]),(0,[z0,z360,z1,z2,z3,z4,z6]),(1,[z0,z12,z1,z3,z4,z6])],[(1,[z0,z1,z225,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z361,z6]),(0,[z0,z1,z2,z3,z4,z362,z6]),(0,[z0,z1,z108,z2,z3,z4,z92]),(0,[z0,z363,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z364,z6]),(1,[z0,z12,z1,z37,z3,z6])],[(0,[z0,z2,z126,z3,z69,z4,z6]),(0,[z0,z1,z3,z365,z56,z4,z6]),(0,[z0,z1,z3,z56,z4,z366,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z4,z6]),(0,[z0,z1,z3,z56,z367,z4,z6]),(0,[z0,z1,z3,z56,z270,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z368]),(0,[z0,z1,z2,z4,z111,z6,z310])],[(1,[z0,z1,z2,z3,z4,z72]),(0,[z124,z0,z12,z1,z3,z4,z6]),(0,[z0,z1,z369,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z370,z6]),(0,[z0,z1,z60,z2,z3,z4,z111])],[(0,[z46,z0,z1,z371,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z372,z6]),(1,[z117,z1,z2,z3,z4,z112]),(0,[z0,z12,z75,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z56,z4,z6]),(0,[z0,z313,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z373,z4,z6])],[(0,[z0,z1,z2,z3,z4,z374,z6]),(0,[z0,z1,z2,z3,z375,z4,z6]),(0,[z0,z12,z1,z126,z3,z4,z6]),(1,[z0,z1,z188,z2,z4,z6]),(0,[z0,z134,z1,z2,z3,z4,z80]),(0,[z0,z12,z1,z2,z3,z56,z6]),(1,[z0,z1,z8,z3,z4,z155]),(1,[z0,z1,z3,z38,z4,z6]),(1,[z0,z1,z108,z2,z4,z310])],[(0,[z0,z1,z2,z3,z376,z4,z6]),(0,[z0,z1,z2,z377,z3,z4,z6]),(0,[z378,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z379,z4,z6]),(0,[z0,z163,z1,z2,z3,z305,z6]),(0,[z0,z1,z2,z380,z3,z4,z6])],[(0,[z0,z1,z2,z381,z3,z4,z6]),(0,[z0,z1,z3,z56,z74,z4,z6]),(0,[z117,z1,z2,z3,z4,z6,z112]),(0,[z0,z382,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z6,z383]),(0,[z0,z1,z2,z384,z3,z4,z6])],[(0,[z212,z0,z2,z126,z3,z4,z6]),(0,[z133,z1,z2,z110,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z385,z6]),(0,[z0,z12,z1,z3,z4,z6,z81]),(0,[z0,z1,z60,z8,z2,z3,z4])]],
   [[],[(0,[z386,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z80,z92]),(0,[z0,z1,z2,z3,z387,z4,z6]),(0,[z0,z1,z388,z2,z3,z4,z6]),(0,[z283,z0,z1,z3,z56,z4,z6]),(0,[z0,z389,z1,z2,z3,z4,z6])],[(0,[z40,z0,z1,z2,z41,z4,z6]),(0,[z0,z1,z2,z390,z3,z4,z6]),(0,[z0,z391,z1,z2,z3,z4,z6])],[(0,[z392,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z52,z76,z3,z4,z6]),(0,[z0,z1,z2,z110,z3,z4,z6]),(0,[z0,z12,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z393,z3,z4,z6]),(1,[z0,z1,z238,z3,z56,z6]),(0,[z0,z1,z394,z2,z3,z4,z6])],[(0,[z0,z1,z2,z395,z3,z4,z6]),(1,[z0,z1,z371,z3,z4,z6]),(1,[z0,z75,z76,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z258]),(0,[z40,z0,z1,z3,z56,z4,z6]),(1,[z107,z1,z2,z3,z5,z6]),(0,[z0,z396,z1,z2,z3,z4,z6]),(0,[z0,z397,z1,z2,z3,z4,z6]),(0,[z398,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z399])],[(0,[z0,z1,z2,z3,z41,z4,z6]),(0,[z400,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z401,z4,z6]),(1,[z0,z1,z3,z402,z4,z6]),(0,[z0,z1,z2,z3,z4,z111,z6])]],
   [[(0,[z0,z403,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z92,z81]),(0,[z0,z1,z89,z3,z9,z4,z6])],[(0,[z224,z0,z12,z1,z3,z4,z6]),(0,[z117,z91,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z92,z6]),(0,[z0,z12,z1,z2,z3,z22,z6])],[(0,[z0,z1,z2,z3,z404,z4,z6]),(0,[z0,z1,z2,z3,z405,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z406]),(1,[z0,z1,z2,z3,z4,z407]),(0,[z0,z1,z2,z3,z4,z6,z62]),(0,[z0,z1,z2,z3,z270,z147,z6])],[(0,[z0,z1,z2,z3,z4,z6,z408]),(0,[z107,z46,z1,z2,z3,z4,z6]),(0,[z117,z0,z1,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z409,z6]),(0,[z410,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z3,z4,z411,z6])],[(0,[z0,z412,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z80,z6]),(0,[z0,z1,z413,z2,z3,z4,z6]),(0,[z0,z1,z414,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z95,z4,z6])],[(0,[z224,z0,z1,z2,z3,z4,z72]),(0,[z0,z1,z2,z3,z415,z4,z6]),(0,[z0,z1,z2,z416,z3,z4,z6])],[(0,[z224,z0,z151,z2,z3,z4,z6]),(0,[z146,z0,z1,z55,z3,z4,z6]),(0,[z0,z417,z1,z2,z3,z4,z6]),(0,[z0,z418,z1,z2,z3,z4,z6]),(0,[z0,z1,z419,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z420,z6]),(0,[z421,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z422,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z423]),(0,[z0,z1,z424,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z425,z6]),(0,[z0,z1,z108,z2,z3,z4,z112]),(0,[z0,z1,z2,z3,z4,z6,z426]),(0,[z0,z427,z1,z2,z3,z4,z6]),(0,[z0,z1,z413,z2,z3,z4,z32]),(0,[z0,z1,z2,z3,z4,z407,z6]),(0,[z0,z1,z2,z3,z4,z428,z6])]],
   [[(0,[z0,z1,z429,z2,z3,z4,z6]),(0,[z0,z1,z2,z430,z3,z4,z6]),(0,[z0,z1,z60,z2,z3,z4,z310])],[(0,[z0,z431,z1,z2,z3,z4,z6]),(0,[z0,z75,z1,z76,z3,z4,z6]),(0,[z0,z1,z60,z2,z3,z270,z4])],[(0,[z0,z1,z2,z3,z432,z4,z6]),(0,[z0,z1,z2,z433,z3,z4,z6]),(0,[z0,z1,z434,z2,z3,z4,z6]),(0,[z0,z1,z49,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z407,z32])],[(0,[z0,z435,z1,z2,z3,z4,z6]),(0,[z0,z151,z1,z3,z56,z4,z6])],[(0,[z0,z1,z2,z436,z3,z4,z6]),(0,[z0,z1,z2,z3,z305,z5,z6]),(0,[z0,z12,z1,z2,z3,z74,z6]),(0,[z0,z1,z2,z3,z4,z437,z6]),(0,[z0,z1,z2,z95,z4,z111,z6])],[(0,[z0,z1,z238,z2,z3,z5,z6]),(0,[z0,z438,z1,z2,z3,z4,z6]),(0,[z0,z134,z1,z2,z3,z4,z81]),(0,[z0,z134,z1,z3,z56,z4,z6])],[(0,[z439,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z440,z6]),(0,[z0,z75,z1,z49,z3,z4,z6]),(0,[z0,z1,z2,z441,z3,z4,z6]),(0,[z0,z442,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z9,z4,z6]),(0,[z0,z1,z2,z3,z443,z4,z6])],[(0,[z0,z12,z1,z8,z3,z4,z6]),(0,[z0,z1,z2,z3,z444,z4,z6]),(0,[z0,z1,z60,z2,z3,z4,z6])]],
   [[(0,[z445,z0,z1,z2,z3,z4,z6]),(0,[z0,z290,z1,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z446,z6]),(0,[z0,z1,z2,z3,z4,z6,z447])],[(0,[z146,z124,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z448,z6]),(0,[z0,z449,z1,z2,z3,z4,z6]),(0,[z0,z1,z450,z2,z3,z4,z6]),(1,[z0,z134,z2,z3,z4,z80]),(0,[z59,z0,z1,z238,z2,z3,z6]),(0,[z0,z1,z451,z2,z3,z4,z6])],[(0,[z0,z2,z416,z3,z41,z4,z6]),(0,[z0,z12,z1,z110,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z80,z112]),(0,[z0,z1,z2,z3,z452,z4,z6]),(0,[z0,z453,z1,z2,z3,z4,z6]),(0,[z0,z118,z1,z2,z3,z305,z6]),(0,[z0,z1,z2,z3,z4,z6,z454]),(0,[z0,z12,z1,z60,z3,z4,z6]),(0,[z0,z1,z3,z16,z56,z4,z6]),(0,[z455,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z456,z6]),(0,[z0,z1,z108,z60,z2,z4,z6])],[(0,[z0,z457,z1,z2,z3,z4,z6]),(0,[z458,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z459,z3,z4,z6]),(0,[z0,z1,z2,z460,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z461,z6]),(0,[z0,z1,z238,z2,z3,z22,z6]),(0,[z0,z1,z2,z3,z4,z6,z57])],[(0,[z0,z1,z2,z3,z4,z213,z6])],[(0,[z462,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z55,z76,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z463]),(0,[z0,z1,z2,z3,z464,z4,z6]),(0,[z0,z1,z2,z3,z74,z164,z6]),(1,[z0,z1,z216,z9,z4,z6]),(0,[z0,z465,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z466,z4,z6])],[(0,[z0,z12,z1,z3,z41,z4,z6]),(0,[z0,z88,z12,z1,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z111,z6]),(0,[z0,z1,z2,z3,z4,z6,z467]),(0,[z0,z11,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z468,z4,z6]),(1,[z0,z1,z3,z4,z6,z469])],[(0,[z0,z470,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z471]),(0,[z0,z472,z1,z2,z3,z4,z6])]],
   [[(0,[z146,z0,z1,z52,z3,z4,z6]),(0,[z0,z192,z1,z49,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z473,z6]),(0,[z0,z1,z2,z37,z3,z32,z6])],[(0,[z124,z0,z1,z3,z56,z4,z6]),(0,[z0,z1,z2,z474,z3,z4,z6])],[(0,[z0,z475,z1,z2,z3,z4,z6]),(0,[z0,z1,z476,z2,z3,z4,z6]),(0,[z0,z1,z477,z2,z3,z4,z6]),(0,[z0,z1,z2,z119,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z235]),(0,[z478,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z479]),(0,[z0,z12,z1,z238,z3,z4,z6]),(0,[z0,z116,z1,z37,z3,z4,z6])],[(0,[z40,z0,z1,z2,z110,z4,z6]),(0,[z0,z1,z2,z3,z4,z480,z6]),(0,[z0,z1,z2,z3,z4,z6,z112]),(0,[z0,z12,z1,z2,z3,z147,z6]),(0,[z0,z481,z1,z2,z3,z4,z6])],[(1,[z0,z82,z1,z89,z4,z6]),(0,[z0,z12,z1,z3,z270,z4,z6]),(0,[z0,z1,z2,z3,z4,z482,z6]),(1,[z0,z1,z2,z3,z270,z147])],[(0,[z0,z1,z238,z2,z3,z74,z6]),(0,[z117,z0,z12,z1,z3,z4,z6]),(0,[z0,z483,z1,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z3,z4,z310])],[(1,[z0,z1,z2,z484,z4,z6]),(0,[z91,z0,z1,z3,z56,z4,z6]),(0,[z485,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z402,z4,z6]),(0,[z0,z1,z108,z2,z3,z270,z4])]],
   [[(0,[z0,z1,z486,z2,z3,z4,z6]),(0,[z0,z487,z1,z2,z3,z4,z6]),(0,[z0,z182,z1,z2,z3,z4,z6]),(1,[z0,z1,z413,z2,z3,z4])],[(0,[z0,z1,z2,z3,z4,z6,z488]),(0,[z0,z1,z371,z2,z3,z4,z6]),(0,[z0,z49,z2,z76,z3,z4,z6]),(0,[z0,z12,z1,z234,z3,z4,z6])],[(0,[z46,z0,z1,z2,z3,z4,z6]),(0,[z489,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z383]),(0,[z0,z1,z2,z3,z4,z6,z490])],[(0,[z0,z12,z1,z3,z74,z4,z6]),(0,[z0,z491,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z411,z6])],[(0,[z0,z492,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z32,z6]),(0,[z0,z1,z2,z3,z4,z6,z493])],[(0,[z0,z1,z2,z494,z3,z4,z6]),(0,[z0,z1,z2,z495,z3,z4,z6]),(0,[z0,z173,z1,z2,z69,z4,z6]),(0,[z0,z12,z1,z3,z443,z4,z6]),(0,[z0,z1,z496,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z3,z4,z6])],[(0,[z0,z1,z2,z497,z3,z4,z6]),(0,[z0,z1,z2,z3,z250,z4,z6]),(0,[z0,z1,z2,z3,z4,z498,z6])],[(0,[z0,z1,z2,z3,z499,z4,z6]),(0,[z0,z1,z2,z3,z4,z500,z6]),(0,[z0,z1,z2,z3,z4,z6,z501]),(0,[z0,z1,z2,z502,z3,z4,z6]),(0,[z503,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z124,z1,z2,z52,z3,z4,z6]),(0,[z0,z1,z2,z3,z83,z4,z6]),(0,[z0,z1,z2,z3,z4,z504,z6]),(0,[z0,z1,z505,z2,z3,z4,z6]),(0,[z0,z506,z1,z2,z3,z4,z6]),(0,[z507,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z469,z62]),(0,[z0,z508,z1,z2,z3,z4,z6])],[(0,[z224,z212,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z509,z6]),(0,[z0,z1,z2,z3,z4,z510,z6]),(0,[z0,z511,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z2,z3,z164,z6]),(0,[z0,z1,z3,z56,z4,z512,z6])],[(0,[z0,z513,z1,z2,z3,z4,z6]),(0,[z0,z1,z514,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z515,z6]),(0,[z91,z0,z1,z2,z267,z4,z6]),(0,[z0,z163,z118,z2,z3,z4,z6])],[(0,[z151,z1,z153,z2,z3,z4,z6]),(0,[z0,z516,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z517,z3,z4,z6]),(0,[z0,z1,z3,z402,z4,z164,z6]),(0,[z0,z12,z1,z216,z3,z4,z6]),(0,[z0,z1,z108,z216,z2,z4,z6]),(0,[z0,z518,z1,z2,z3,z4,z6]),(0,[z0,z82,z1,z89,z2,z4,z6])],[(0,[z0,z1,z2,z3,z519,z4,z6]),(0,[z0,z1,z2,z3,z520,z4,z6]),(0,[z0,z171,z12,z1,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z241]),(0,[z0,z1,z521,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z522,z6]),(0,[z0,z160,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z523,z6]),(0,[z524,z0,z1,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z525,z6])],[(0,[z0,z1,z2,z526,z3,z4,z6]),(1,[z0,z173,z2,z126,z4,z6]),(1,[z0,z135,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z143,z6]),(0,[z0,z1,z238,z2,z3,z147,z6])],[(0,[z527,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z80,z6]),(0,[z0,z1,z2,z3,z4,z528,z6]),(0,[z0,z1,z529,z2,z3,z4,z6]),(0,[z0,z277,z1,z3,z56,z4,z6]),(0,[z0,z1,z530,z2,z3,z4,z6]),(0,[z0,z1,z61,z2,z3,z4,z6])],[(0,[z0,z1,z2,z105,z3,z4,z6]),(0,[z0,z531,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z532,z6]),(1,[z0,z152,z2,z69,z4,z6]),(0,[z0,z1,z2,z95,z4,z32,z6])],[(0,[z0,z1,z2,z3,z4,z112,z81]),(0,[z59,z0,z1,z108,z2,z3,z4])],[(0,[z533,z0,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z6,z112]),(0,[z0,z1,z534,z2,z3,z4,z6]),(0,[z0,z17,z1,z3,z56,z4,z6])],[(1,[z224,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z535]),(0,[z0,z1,z2,z3,z4,z6,z536]),(1,[z0,z11,z1,z2,z32,z6])],[(0,[z537,z0,z1,z2,z3,z4,z6]),(0,[z538,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z539]),(0,[z0,z1,z3,z56,z4,z22,z6])],[(0,[z0,z1,z2,z3,z5,z164,z6]),(0,[z0,z540,z1,z2,z3,z4,z6]),(0,[z0,z1,z541,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z155,z6]),(0,[z0,z1,z2,z3,z4,z6,z18]),(0,[z0,z1,z2,z3,z4,z6,z469])],[(0,[z0,z1,z2,z3,z4,z542,z6]),(0,[z0,z1,z188,z2,z4,z6,z81])]],
   [[(0,[z53,z0,z1,z3,z56,z4,z6])],[(1,[z0,z1,z2,z3,z210,z6]),(0,[z0,z1,z2,z3,z543,z4,z6]),(1,[z0,z182,z2,z3,z4,z81]),(0,[z0,z17,z1,z8,z3,z4,z6]),(0,[z544,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z545,z2,z3,z4,z6])],[(1,[z0,z1,z546,z3,z4,z6]),(0,[z224,z0,z1,z2,z547,z4,z6]),(0,[z548,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z549]),(0,[z107,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z6]),(0,[z91,z0,z12,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z9,z4,z6]),(0,[z0,z550,z1,z2,z3,z4,z6]),(0,[z0,z1,z551,z2,z3,z4,z6])],[(0,[z552,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z553]),(0,[z554,z0,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z32,z6]),(0,[z0,z1,z2,z3,z95,z4,z6])],[(0,[z0,z555,z1,z2,z3,z4,z6]),(0,[z0,z173,z152,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z556,z6])],[(0,[z0,z557,z1,z2,z3,z4,z6]),(1,[z0,z1,z119,z3,z4,z6]),(1,[z0,z1,z2,z37,z95,z6])],[(0,[z0,z1,z2,z3,z558,z4,z6]),(0,[z0,z1,z3,z77,z56,z4,z6]),(1,[z0,z1,z60,z2,z4,z111])],[(0,[z117,z0,z1,z2,z3,z4,z112]),(0,[z0,z1,z2,z3,z4,z559,z6]),(0,[z0,z12,z1,z560,z3,z4,z6]),(0,[z0,z1,z108,z2,z4,z6,z310])]],
   [[(0,[z224,z0,z1,z2,z3,z4,z6]),(0,[z561,z0,z1,z2,z3,z4,z6]),(0,[z133,z0,z12,z1,z3,z4,z6]),(0,[z0,z1,z2,z562,z3,z4,z6]),(0,[z0,z1,z8,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z563,z6])],[(0,[z0,z1,z2,z3,z4,z564,z6]),(0,[z0,z1,z2,z41,z69,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z265]),(0,[z0,z182,z2,z3,z4,z6,z81]),(0,[z0,z1,z113,z2,z3,z4,z6]),(0,[z0,z242,z12,z1,z3,z4,z6]),(1,[z0,z1,z2,z4,z6,z120])],[(0,[z0,z1,z2,z3,z4,z6,z565]),(0,[z0,z1,z2,z3,z4,z6,z566])],[(1,[z0,z1,z217,z2,z3,z4])],[(0,[z0,z82,z1,z108,z2,z4,z6])],[(0,[z567,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z568])],[(0,[z0,z1,z569,z2,z3,z4,z6]),(0,[z0,z1,z570,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z571,z6]),(0,[z0,z1,z572,z2,z3,z4,z6])],[(1,[z0,z1,z284,z3,z4,z6]),(0,[z573,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z12,z1,z3,z305,z4,z6]),(0,[z0,z1,z2,z3,z4,z366,z6])],[(0,[z0,z12,z1,z76,z3,z4,z6]),(0,[z0,z1,z574,z2,z3,z4,z6]),(0,[z0,z1,z238,z2,z3,z56,z6]),(0,[z0,z1,z2,z3,z367,z4,z6]),(0,[z0,z1,z2,z3,z270,z4,z6])],[(0,[z0,z1,z126,z3,z56,z4,z6]),(0,[z0,z12,z1,z3,z4,z6,z310]),(0,[z0,z575,z1,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z3,z4,z111]),(0,[z0,z1,z2,z576,z3,z4,z6])],[(0,[z0,z1,z577,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z578,z4,z6]),(0,[z0,z1,z76,z3,z56,z4,z6]),(0,[z0,z175,z1,z2,z3,z4,z6]),(1,[z0,z1,z99,z3,z4,z6])],[(0,[z0,z1,z2,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z250,z6]),(0,[z146,z0,z1,z3,z56,z4,z6]),(0,[z0,z192,z49,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z411,z32,z6]),(0,[z0,z1,z2,z3,z4,z6,z579]),(0,[z580,z0,z1,z2,z3,z4,z6])],[(0,[z224,z0,z1,z2,z3,z210,z6]),(0,[z581,z0,z1,z2,z3,z4,z6]),(0,[z0,z192,z1,z3,z56,z4,z6]),(0,[z0,z12,z1,z3,z4,z6,z18])],[(0,[z224,z0,z1,z546,z3,z4,z6]),(0,[z582,z0,z1,z2,z3,z4,z6]),(0,[z0,z192,z75,z2,z3,z4,z6]),(0,[z0,z583,z1,z2,z3,z4,z6]),(0,[z584,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z6,z585]),(0,[z0,z1,z2,z3,z74,z4,z6]),(0,[z0,z1,z2,z3,z4,z586,z6]),(0,[z587,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z588,z1,z2,z3,z4,z6]),(0,[z0,z589,z1,z2,z3,z4,z6]),(0,[z91,z1,z2,z3,z4,z92,z6]),(0,[z0,z1,z2,z3,z4,z6,z590]),(0,[z0,z152,z1,z2,z69,z4,z6]),(0,[z0,z1,z591,z2,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z147,z6]),(0,[z0,z1,z108,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z6,z592])],[(0,[z0,z1,z2,z3,z593,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z594]),(0,[z0,z173,z1,z2,z4,z111,z6]),(0,[z0,z1,z3,z9,z56,z4,z6]),(0,[z0,z595,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z596])],[(0,[z0,z1,z2,z3,z4,z6,z597]),(0,[z0,z1,z2,z3,z598,z4,z6]),(0,[z0,z599,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z95,z4,z6]),(0,[z0,z1,z108,z3,z103,z4,z6])],[(0,[z283,z0,z1,z2,z3,z4,z6]),(0,[z600,z0,z1,z2,z3,z4,z6])],[(0,[z0,z173,z1,z3,z56,z4,z6]),(0,[z0,z298,z12,z1,z3,z4,z6]),(0,[z0,z1,z3,z56,z4,z4,z6])],[(0,[z133,z40,z1,z2,z3,z4,z6]),(0,[z0,z601,z1,z2,z3,z4,z6]),(0,[z0,z1,z89,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z547,z4,z6]),(0,[z0,z1,z2,z602,z3,z4,z6]),(0,[z0,z1,z3,z56,z56,z4,z6])],[(0,[z212,z0,z12,z1,z3,z4,z6]),(0,[z40,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z603,z4,z6]),(0,[z0,z604,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z6,z605]),(0,[z0,z1,z606,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z607,z6]),(0,[z0,z1,z2,z3,z4,z608,z6])],[(0,[z0,z1,z609,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z92,z6])],[(1,[z0,z290,z1,z3,z4,z6]),(0,[z0,z610,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z611]),(0,[z0,z1,z612,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z613,z4,z6]),(0,[z0,z163,z1,z3,z56,z4,z6]),(0,[z0,z1,z89,z216,z2,z4,z6]),(0,[z0,z82,z1,z2,z4,z111,z6])],[(0,[z212,z0,z151,z2,z3,z4,z6]),(0,[z614,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z615,z6]),(0,[z0,z1,z2,z3,z616,z4,z6])],[(0,[z0,z617,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z484,z3,z4,z6]),(1,[z0,z1,z2,z3,z301,z6]),(0,[z0,z1,z3,z56,z4,z164,z6])],[(0,[z224,z0,z2,z126,z3,z4,z6]),(0,[z1,z2,z110,z3,z41,z4,z6]),(0,[z0,z82,z1,z3,z56,z4,z6]),(0,[z0,z1,z158,z2,z3,z4,z6])],[(0,[z618,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z1,z619,z2,z3,z4,z6]),(0,[z0,z620,z1,z2,z3,z4,z6]),(0,[z0,z12,z1,z2,z3,z305,z6]),(0,[z0,z1,z217,z2,z3,z4,z6]),(0,[z0,z397,z1,z3,z56,z4,z6])],[(0,[z0,z621,z1,z2,z3,z4,z6]),(0,[z322,z0,z1,z2,z3,z4,z6]),(0,[z0,z11,z1,z2,z37,z4,z6]),(1,[z0,z1,z61,z2,z4,z6])],[(1,[z40,z1,z2,z41,z4,z6]),(0,[z0,z1,z2,z3,z4,z155,z6]),(0,[z0,z1,z2,z3,z4,z622,z6])],[(0,[z0,z623,z1,z2,z3,z4,z6]),(0,[z0,z624,z1,z2,z3,z4,z6]),(0,[z625,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z626,z3,z4,z6]),(0,[z0,z12,z1,z2,z3,z4,z6]),(0,[z0,z1,z108,z197,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z627,z6])],[(0,[z0,z1,z49,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z65,z6]),(0,[z0,z82,z1,z8,z3,z4,z6]),(0,[z0,z12,z1,z2,z37,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z628])],[(0,[z133,z0,z1,z2,z41,z4,z6]),(0,[z59,z0,z1,z2,z3,z4,z6]),(0,[z0,z313,z1,z3,z4,z6,z62])],[(0,[z0,z1,z2,z3,z629,z4,z6]),(0,[z0,z1,z3,z56,z4,z6,z62]),(0,[z0,z109,z1,z2,z3,z6,z18]),(0,[z0,z1,z2,z3,z630,z4,z6])],[(0,[z631,z0,z1,z2,z3,z4,z6]),(0,[z212,z0,z152,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z325,z6]),(0,[z632,z0,z1,z2,z3,z4,z6]),(0,[z146,z0,z12,z1,z3,z4,z6]),(0,[z0,z633,z1,z2,z3,z4,z6]),(0,[z0,z1,z634,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z635]),(0,[z148,z0,z12,z1,z3,z4,z6]),(0,[z0,z1,z2,z37,z3,z95,z6])]],
   [[(0,[z133,z0,z1,z3,z56,z4,z6]),(0,[z46,z1,z2,z3,z74,z4,z6]),(0,[z0,z192,z12,z1,z3,z4,z6]),(0,[z0,z341,z1,z2,z3,z4,z6]),(0,[z0,z1,z284,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z365,z4,z6])],[(1,[z0,z1,z2,z547,z4,z6]),(0,[z117,z0,z1,z2,z3,z4,z92])],[(0,[z0,z1,z636,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z637,z6]),(0,[z0,z1,z2,z3,z4,z6,z638]),(0,[z0,z1,z639,z2,z3,z4,z6]),(0,[z0,z182,z1,z2,z3,z4,z80]),(0,[z0,z1,z2,z3,z4,z640,z6]),(1,[z0,z1,z197,z3,z4,z6]),(1,[z59,z0,z1,z2,z3,z62])],[(0,[z0,z1,z153,z2,z3,z4,z6]),(0,[z0,z1,z641,z2,z3,z4,z6]),(0,[z0,z642,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z643,z4,z6]),(0,[z0,z1,z2,z560,z3,z4,z6]),(0,[z0,z1,z2,z3,z644,z4,z6]),(0,[z0,z1,z2,z3,z645,z4,z6])],[(0,[z0,z1,z2,z3,z4,z241,z6]),(1,[z0,z1,z3,z24,z4,z6]),(0,[z91,z0,z1,z2,z484,z4,z6]),(1,[z0,z1,z2,z4,z607,z6]),(0,[z0,z1,z2,z3,z4,z646,z6])],[(0,[z0,z1,z2,z41,z4,z111,z6]),(0,[z0,z1,z2,z647,z3,z4,z6]),(0,[z0,z1,z37,z3,z56,z4,z6]),(0,[z0,z1,z3,z4,z155,z6,z18])],[(0,[z224,z0,z1,z2,z105,z4,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z648,z0,z1,z2,z3,z4,z6]),(1,[z0,z1,z2,z3,z376,z6]),(0,[z0,z1,z2,z3,z4,z649,z6]),(0,[z0,z1,z2,z3,z4,z650,z6]),(0,[z0,z1,z651,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z652,z4,z6]),(0,[z0,z1,z653,z2,z3,z4,z6])]],
   [[],[(0,[z0,z12,z1,z3,z4,z92,z6]),(0,[z0,z1,z2,z3,z4,z654,z6]),(0,[z0,z1,z655,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z120])],[(1,[z0,z2,z416,z3,z4,z6]),(0,[z0,z1,z2,z110,z69,z4,z6]),(0,[z0,z1,z656,z2,z3,z4,z6]),(0,[z0,z118,z1,z272,z3,z4,z6]),(0,[z0,z1,z238,z2,z3,z305,z6]),(0,[z0,z1,z60,z3,z56,z4,z6]),(0,[z0,z1,z99,z3,z4,z32,z6])],[(0,[z0,z1,z546,z2,z3,z4,z6]),(0,[z124,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z657,z2,z3,z4,z6]),(0,[z0,z658,z1,z2,z3,z4,z6]),(0,[z0,z1,z659,z2,z3,z4,z6])],[(0,[z660,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z305,z4,z6]),(0,[z0,z1,z2,z661,z3,z4,z6])],[(0,[z662,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z663,z4,z6]),(0,[z1,z2,z3,z74,z4,z5,z6]),(0,[z0,z1,z2,z76,z3,z4,z6]),(0,[z0,z135,z1,z2,z3,z9,z6]),(0,[z0,z1,z238,z2,z3,z4,z6]),(0,[z455,z0,z1,z3,z56,z4,z6]),(0,[z0,z664,z1,z2,z3,z4,z6])],[(1,[z0,z1,z2,z3,z4,z265]),(0,[z665,z0,z1,z2,z3,z4,z6]),(0,[z0,z163,z12,z1,z3,z4,z6]),(0,[z0,z12,z427,z1,z3,z4,z6]),(0,[z0,z1,z238,z2,z37,z3,z6]),(0,[z0,z1,z2,z3,z4,z6,z310])],[(0,[z666,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z667,z2,z3,z4,z6]),(0,[z0,z187,z2,z3,z41,z4,z6]),(0,[z0,z1,z668,z2,z3,z4,z6]),(0,[z0,z1,z669,z2,z3,z4,z6]),(0,[z0,z1,z2,z4,z607,z6,z81]),(0,[z0,z12,z82,z1,z3,z4,z6]),(0,[z0,z17,z1,z3,z4,z6,z18]),(0,[z59,z0,z1,z2,z3,z6,z62]),(0,[z0,z1,z2,z3,z4,z6,z670])]],
   [[(0,[z0,z1,z52,z3,z56,z4,z6]),(0,[z0,z118,z1,z3,z56,z4,z6]),(0,[z0,z182,z134,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z671,z4,z6]),(0,[z392,z0,z12,z1,z3,z4,z6]),(0,[z0,z11,z1,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z103,z4,z6])],[(0,[z0,z187,z1,z2,z3,z4,z6]),(0,[z0,z672,z1,z2,z3,z4,z6]),(0,[z0,z1,z673,z2,z3,z4,z6])],[(0,[z0,z1,z2,z52,z3,z4,z6]),(0,[z674,z0,z1,z2,z3,z4,z6])],[(0,[z0,z1,z675,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z676,z6]),(0,[z0,z152,z1,z2,z4,z111,z6]),(0,[z0,z12,z173,z1,z3,z4,z6]),(0,[z0,z1,z272,z2,z3,z4,z6]),(0,[z0,z1,z677,z2,z3,z4,z6]),(0,[z678,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z679,z6])],[(0,[z680,z0,z1,z2,z3,z4,z6]),(0,[z0,z173,z1,z108,z2,z4,z6])],[(0,[z0,z1,z2,z3,z681,z4,z6]),(0,[z0,z682,z1,z2,z3,z4,z6]),(0,[z0,z1,z238,z2,z3,z164,z6]),(1,[z0,z12,z1,z3,z56,z6]),(0,[z0,z1,z2,z3,z4,z6,z683])],[(0,[z212,z0,z1,z3,z56,z4,z6]),(0,[z684,z0,z1,z2,z3,z4,z6]),(0,[z0,z152,z1,z3,z56,z4,z6]),(0,[z0,z173,z1,z2,z126,z4,z6]),(1,[z0,z163,z2,z3,z164,z6]),(0,[z0,z1,z2,z3,z6,z57,z18])]],
   [[(0,[z0,z1,z685,z2,z3,z4,z6]),(0,[z0,z1,z2,z126,z41,z4,z6]),(0,[z0,z1,z2,z3,z4,z686,z6]),(0,[z0,z82,z1,z216,z3,z4,z6])],[(0,[z0,z1,z687,z2,z3,z4,z6]),(0,[z0,z1,z2,z688,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z689,z6]),(1,[z0,z17,z1,z3,z4,z18])],[(0,[z0,z1,z216,z2,z4,z111,z6]),(0,[z0,z1,z2,z3,z4,z512,z6])],[(0,[z224,z0,z1,z2,z3,z376,z6]),(0,[z0,z690,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z691,z4,z6]),(0,[z0,z116,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z692,z6]),(0,[z693,z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z694,z4,z6]),(0,[z0,z695,z1,z2,z3,z4,z6]),(0,[z0,z696,z1,z2,z3,z4,z6]),(0,[z0,z1,z697,z2,z3,z4,z6])],[(0,[z212,z0,z153,z2,z3,z4,z6]),(1,[z0,z12,z1,z3,z5,z6]),(0,[z46,z0,z1,z3,z56,z4,z6]),(0,[z91,z0,z1,z2,z3,z4,z92]),(0,[z0,z1,z216,z3,z56,z4,z6]),(0,[z0,z1,z2,z3,z4,z698,z6])],[(0,[z0,z1,z699,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z700,z6]),(0,[z0,z701,z1,z2,z3,z4,z6]),(0,[z0,z75,z1,z3,z56,z4,z6])],[(0,[z0,z1,z2,z3,z702,z4,z6]),(0,[z133,z0,z1,z2,z110,z4,z6]),(0,[z0,z1,z2,z3,z4,z6,z703]),(0,[z0,z1,z704,z2,z3,z4,z6]),(0,[z0,z118,z2,z3,z305,z4,z6]),(0,[z0,z1,z3,z56,z4,z6,z81]),(0,[z0,z1,z2,z3,z705,z4,z6]),(0,[z0,z1,z706,z2,z3,z4,z6]),(0,[z524,z0,z1,z2,z3,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z4,z707,z6]),(0,[z133,z1,z2,z110,z4,z241])],[(0,[z0,z1,z3,z4,z708,z6]),(0,[z0,z1,z2,z709,z4,z6]),(0,[z1,z2,z3,z4,z6,z710]),(0,[z0,z173,z2,z711,z4,z6]),(1,[z0,z1,z2,z4,z712])],[(0,[z0,z713,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z578,z6]),(0,[z714,z1,z2,z3,z4,z6]),(0,[z0,z173,z2,z4,z622,z6])],[(0,[z0,z1,z105,z56,z4,z6]),(0,[z0,z1,z3,z24,z325,z6]),(0,[z0,z1,z2,z715,z4,z6]),(0,[z12,z1,z3,z74,z5,z6]),(0,[z0,z1,z2,z3,z65,z6]),(0,[z0,z12,z1,z3,z6,z635])],[(0,[z0,z1,z2,z3,z716,z6]),(0,[z40,z2,z416,z41,z4,z6]),(0,[z0,z11,z12,z1,z3,z6]),(0,[z0,z12,z1,z551,z3,z6]),(0,[z0,z1,z3,z56,z4,z407]),(0,[z0,z1,z2,z717,z4,z6])],[(0,[z146,z1,z55,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z718]),(0,[z0,z1,z3,z4,z719,z6])],[(0,[z0,z1,z2,z105,z210,z6]),(0,[z133,z1,z2,z110,z4,z265]),(0,[z352,z1,z2,z3,z4,z92]),(0,[z0,z1,z720,z2,z3,z4])],[(0,[z0,z1,z2,z721,z4,z6]),(0,[z0,z722,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z172,z6]),(0,[z0,z723,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z724])]],
   [[(0,[z0,z1,z2,z547,z376,z6]),(0,[z0,z12,z1,z3,z646,z6]),(0,[z0,z1,z60,z2,z644,z4])],[(0,[z269,z1,z2,z3,z4,z112]),(0,[z0,z1,z725,z3,z4,z6]),(0,[z0,z1,z3,z4,z726,z6]),(0,[z0,z1,z197,z3,z4,z6]),(0,[z53,z1,z3,z367,z4,z6])],[(0,[z0,z1,z2,z3,z727,z6]),(0,[z0,z416,z3,z56,z4,z6]),(0,[z0,z1,z728,z3,z4,z6]),(0,[z0,z1,z729,z3,z4,z6]),(0,[z1,z2,z3,z4,z92,z730]),(0,[z0,z1,z3,z77,z65,z6]),(0,[z0,z1,z113,z3,z56,z4])],[(0,[z0,z1,z3,z24,z4,z6]),(0,[z0,z12,z1,z3,z402,z6]),(0,[z0,z118,z119,z3,z305,z6]),(0,[z0,z135,z1,z216,z9,z6])],[(0,[z0,z1,z2,z3,z731,z6]),(0,[z0,z732,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z733,z6]),(0,[z567,z0,z12,z1,z3,z6]),(0,[z0,z1,z8,z3,z4,z522]),(0,[z0,z12,z734,z3,z4,z6]),(0,[z0,z116,z1,z37,z95,z6])],[(0,[z46,z1,z371,z3,z74,z6]),(0,[z0,z1,z108,z2,z4,z368]),(0,[z0,z1,z2,z95,z6,z447]),(0,[z0,z1,z3,z270,z147,z253])],[(0,[z0,z1,z2,z3,z376,z6]),(0,[z0,z1,z735,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z72]),(0,[z0,z633,z2,z126,z4,z6]),(0,[z0,z12,z1,z227,z3,z6])],[(0,[z0,z1,z225,z3,z4,z72]),(0,[z224,z153,z225,z3,z4,z6]),(0,[z0,z2,z736,z3,z4,z6]),(0,[z117,z12,z1,z3,z4,z112]),(0,[z0,z1,z2,z3,z737,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z738]),(0,[z0,z1,z31,z9,z4,z6]),(0,[z0,z12,z1,z739,z4,z6]),(0,[z0,z17,z1,z2,z31,z4]),(0,[z0,z1,z2,z37,z740,z6])],[(0,[z0,z2,z416,z3,z4,z6]),(0,[z1,z2,z741,z41,z4,z6]),(0,[z0,z1,z2,z3,z4,z742]),(0,[z0,z192,z49,z3,z4,z6]),(0,[z0,z313,z1,z61,z4,z6])],[(0,[z0,z1,z2,z3,z743,z6]),(0,[z0,z12,z1,z3,z629,z6]),(0,[z0,z744,z1,z2,z3,z6]),(0,[z0,z1,z3,z745,z22,z6])],[(0,[z224,z746,z2,z3,z4,z6]),(0,[z0,z134,z2,z3,z4,z747]),(0,[z0,z134,z3,z56,z4,z80]),(0,[z0,z12,z1,z3,z6,z670])],[(1,[z0,z748,z3,z4,z6]),(0,[z0,z1,z2,z749,z4,z6]),(0,[z0,z1,z56,z4,z750,z6]),(0,[z0,z472,z1,z108,z2,z4])],[(0,[z0,z751,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z295,z6]),(0,[z0,z12,z1,z3,z24,z6]),(0,[z0,z12,z1,z3,z452,z6]),(0,[z0,z1,z56,z4,z607,z6]),(0,[z0,z12,z1,z3,z329,z6]),(0,[z0,z1,z61,z56,z4,z6])],[(0,[z0,z2,z3,z4,z752,z6]),(0,[z0,z753,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z754]),(0,[z0,z1,z755,z9,z4,z6]),(0,[z0,z12,z1,z113,z3,z4]),(0,[z0,z12,z1,z3,z4,z756]),(0,[z0,z1,z2,z4,z740,z6])],[(0,[z224,z483,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z220,z6]),(0,[z0,z757,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z702,z6]),(0,[z117,z1,z2,z3,z4,z730]),(0,[z0,z12,z427,z3,z305,z6]),(0,[z0,z12,z1,z179,z3,z6]),(1,[z0,z1,z3,z745,z6])]],
   [[(0,[z46,z1,z2,z3,z733,z6]),(0,[z0,z12,z1,z3,z676,z6])],[(0,[z0,z12,z1,z3,z230,z6]),(0,[z0,z758,z1,z2,z3,z6]),(0,[z0,z192,z3,z4,z512,z6]),(0,[z0,z12,z1,z217,z3,z4]),(0,[z0,z759,z2,z3,z4,z6])],[(0,[z0,z1,z52,z3,z250,z6]),(0,[z0,z12,z416,z3,z4,z6]),(0,[z107,z12,z1,z3,z5,z6]),(0,[z0,z109,z1,z3,z9,z6])],[(0,[z0,z760,z2,z3,z4,z6]),(0,[z0,z761,z1,z3,z4,z6]),(0,[z0,z163,z2,z3,z762,z6]),(0,[z59,z0,z12,z1,z3,z383])],[(0,[z0,z12,z1,z3,z686,z6]),(0,[z0,z109,z1,z3,z56,z6])],[(0,[z0,z1,z2,z3,z763,z6]),(0,[z0,z1,z764,z3,z4,z6]),(1,[z0,z1,z755,z4,z6]),(0,[z0,z256,z1,z108,z2,z4]),(0,[z0,z12,z1,z3,z56,z6])],[(0,[z0,z1,z765,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z766]),(0,[z0,z1,z2,z767,z4,z6]),(0,[z224,z153,z2,z3,z4,z258]),(0,[z0,z214,z12,z1,z3,z6]),(0,[z0,z163,z2,z3,z164,z6]),(0,[z0,z109,z82,z1,z3,z6]),(0,[z0,z82,z1,z108,z8,z4]),(0,[z0,z12,z1,z3,z512,z6])],[(0,[z0,z1,z2,z3,z768,z6]),(0,[z0,z12,z1,z3,z252,z6]),(0,[z0,z135,z1,z3,z6,z18]),(0,[z0,z1,z3,z56,z270,z147])]],
   [[(0,[z0,z1,z2,z3,z4,z769]),(0,[z0,z1,z2,z3,z770,z6]),(0,[z0,z12,z1,z3,z692,z6]),(0,[z0,z1,z2,z3,z6,z771]),(0,[z0,z772,z1,z2,z3,z6]),(0,[z94,z0,z12,z1,z3,z6]),(0,[z0,z1,z217,z216,z9,z4]),(0,[z0,z17,z1,z3,z4,z18]),(0,[z0,z1,z2,z4,z712,z310])],[(0,[z0,z1,z2,z3,z773,z6]),(0,[z0,z1,z2,z3,z4,z774])],[(0,[z0,z12,z1,z3,z700,z6]),(0,[z0,z1,z748,z3,z4,z6]),(0,[z0,z182,z2,z3,z4,z747]),(0,[z0,z11,z1,z2,z443,z6]),(0,[z0,z1,z775,z2,z3,z4])],[(0,[z0,z1,z2,z3,z210,z258]),(0,[z0,z1,z577,z2,z4,z111]),(0,[z0,z1,z2,z3,z776,z6]),(0,[z0,z173,z126,z56,z4,z6]),(0,[z0,z1,z777,z2,z3,z4]),(0,[z0,z12,z1,z61,z4,z6])],[(0,[z0,z1,z546,z3,z4,z258]),(0,[z0,z12,z1,z3,z663,z6]),(0,[z0,z12,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z778,z6]),(0,[z0,z427,z49,z3,z4,z6]),(0,[z0,z12,z1,z697,z3,z6])],[(0,[z0,z1,z2,z779,z4,z6]),(0,[z146,z1,z55,z3,z250,z6]),(0,[z0,z780,z2,z3,z4,z6]),(0,[z1,z2,z110,z741,z4,z6]),(0,[z0,z1,z612,z3,z56,z6]),(0,[z59,z0,z12,z1,z3,z183])],[(0,[z0,z1,z3,z143,z56,z6])],[(0,[z0,z12,z1,z3,z23,z6]),(0,[z0,z1,z781,z3,z4,z6])]],
   [[(0,[z0,z1,z782,z2,z3,z4]),(0,[z0,z1,z783,z3,z4,z6]),(0,[z0,z784,z1,z3,z4,z6]),(0,[z0,z1,z3,z785,z4,z6])],[(0,[z0,z1,z2,z3,z786,z6]),(0,[z0,z787,z1,z3,z4,z6]),(0,[z0,z135,z1,z89,z3,z6]),(0,[z0,z178,z12,z1,z3,z6]),(0,[z1,z3,z788,z56,z4,z6])],[(0,[z0,z345,z2,z3,z305,z6]),(0,[z0,z1,z113,z2,z3,z4]),(0,[z0,z12,z1,z3,z22,z6])],[(0,[z0,z1,z2,z3,z4,z789]),(0,[z0,z1,z2,z4,z790,z6])],[(0,[z0,z1,z2,z3,z791,z6]),(0,[z0,z12,z1,z3,z285,z6]),(0,[z0,z1,z76,z3,z65,z6]),(0,[z0,z792,z1,z3,z4,z6]),(0,[z0,z1,z113,z2,z3,z143]),(0,[z0,z12,z1,z793,z4,z6]),(0,[z0,z12,z1,z3,z367,z6])],[(0,[z0,z513,z49,z3,z4,z6]),(0,[z0,z1,z3,z4,z794,z6]),(0,[z0,z1,z56,z4,z6,z120])],[(0,[z795,z1,z2,z3,z4,z6])],[(0,[z0,z1,z3,z796,z4,z6]),(0,[z40,z1,z41,z56,z4,z6]),(0,[z0,z1,z3,z56,z4,z241]),(0,[z0,z797,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z58,z6])]],
   [[(0,[z0,z1,z2,z3,z798,z6]),(0,[z0,z75,z234,z3,z4,z6])],[(0,[z0,z311,z2,z3,z4,z81]),(0,[z0,z1,z49,z3,z65,z6]),(0,[z0,z1,z272,z3,z164,z6]),(0,[z0,z1,z3,z4,z6,z799])],[(0,[z0,z1,z273,z9,z4,z6]),(0,[z410,z0,z12,z1,z3,z6])],[(0,[z0,z1,z371,z3,z5,z6]),(0,[z800,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z801,z6]),(0,[z0,z313,z1,z3,z147,z6])],[(0,[z0,z1,z802,z3,z4,z6]),(0,[z146,z1,z803,z3,z4,z6]),(0,[z0,z1,z2,z3,z804,z6]),(0,[z0,z12,z1,z3,z312,z6])],[(0,[z0,z1,z3,z56,z4,z265]),(0,[z0,z1,z2,z3,z4,z805]),(0,[z0,z1,z3,z4,z411,z407])],[(0,[z224,z153,z3,z56,z4,z6]),(0,[z0,z1,z2,z4,z806,z6]),(0,[z1,z2,z3,z4,z733,z6]),(0,[z0,z1,z2,z3,z807,z6]),(0,[z0,z2,z3,z4,z6,z747]),(0,[z0,z109,z17,z1,z3,z18])],[(0,[z0,z1,z3,z808,z4,z6]),(0,[z0,z1,z2,z4,z809,z6]),(0,[z0,z313,z1,z3,z4,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z810]),(0,[z0,z152,z69,z56,z4,z6]),(0,[z0,z1,z755,z3,z4,z6])],[(0,[z0,z1,z2,z267,z4,z6]),(0,[z0,z12,z1,z3,z375,z6]),(0,[z0,z1,z3,z4,z811,z6]),(0,[z0,z12,z1,z3,z558,z6]),(0,[z0,z1,z37,z56,z95,z6])],[(0,[z0,z1,z812,z3,z4,z6]),(0,[z0,z1,z47,z3,z4,z6]),(0,[z0,z1,z813,z2,z4,z6]),(0,[z0,z192,z748,z3,z4,z6]),(0,[z0,z1,z2,z4,z228,z6]),(0,[z0,z12,z759,z3,z4,z6]),(0,[z0,z12,z1,z3,z270,z147]),(0,[z0,z109,z17,z1,z3,z6]),(0,[z0,z814,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z815,z6])],[(0,[z0,z1,z2,z3,z4,z816]),(0,[z0,z1,z3,z56,z210,z6]),(0,[z0,z1,z284,z3,z5,z6]),(0,[z0,z1,z817,z2,z4,z6]),(0,[z0,z1,z2,z818,z4,z6]),(0,[z0,z1,z2,z819,z4,z6]),(0,[z0,z182,z3,z56,z4,z81])],[(0,[z0,z1,z2,z105,z376,z6]),(0,[z820,z12,z1,z3,z4,z6]),(0,[z0,z109,z1,z2,z3,z6]),(0,[z0,z1,z3,z56,z630,z6]),(1,[z0,z821,z1,z3,z6])],[(0,[z0,z1,z2,z3,z4,z822]),(0,[z0,z12,z1,z3,z83,z6]),(1,[z1,z2,z741,z4,z6]),(0,[z322,z12,z1,z3,z74,z6]),(0,[z0,z118,z2,z3,z305,z6]),(0,[z0,z1,z2,z3,z745,z6])],[(0,[z0,z277,z76,z3,z4,z6]),(0,[z0,z1,z2,z3,z823,z6]),(0,[z0,z116,z1,z3,z4,z6]),(0,[z0,z17,z1,z3,z57,z18])],[]],
   [[(0,[z0,z1,z2,z3,z824,z6]),(0,[z0,z1,z2,z825,z4,z6])],[(0,[z0,z12,z1,z3,z141,z6]),(0,[z0,z1,z2,z826,z4,z6]),(0,[z0,z1,z8,z3,z103,z4]),(0,[z59,z0,z1,z2,z120,z62]),(0,[z0,z1,z2,z3,z270,z827])],[(0,[z0,z1,z2,z828,z4,z6]),(0,[z0,z192,z49,z3,z301,z6]),(0,[z0,z12,z1,z108,z4,z310])],[(0,[z0,z12,z1,z547,z4,z6]),(0,[z0,z1,z829,z2,z3,z4]),(0,[z0,z2,z3,z305,z762,z6]),(0,[z0,z1,z3,z4,z6,z830])],[(0,[z0,z1,z225,z547,z4,z6]),(0,[z0,z1,z831,z3,z4,z6]),(0,[z0,z1,z371,z3,z74,z6]),(0,[z0,z1,z2,z484,z4,z92]),(0,[z0,z12,z152,z69,z4,z6]),(0,[z0,z11,z1,z413,z2,z4])],[(0,[z40,z187,z2,z41,z4,z6]),(0,[z107,z1,z2,z3,z733,z6]),(0,[z0,z1,z2,z3,z832,z6]),(0,[z0,z1,z238,z3,z402,z6]),(0,[z0,z341,z427,z3,z4,z6]),(0,[z0,z12,z1,z3,z147,z6]),(0,[z833,z1,z2,z3,z4,z6]),(0,[z0,z821,z1,z3,z4,z6])],[(0,[z0,z12,z1,z3,z519,z6]),(0,[z0,z1,z2,z3,z834,z6]),(0,[z0,z12,z695,z1,z3,z6]),(0,[z0,z118,z2,z3,z762,z6]),(0,[z0,z12,z1,z4,z607,z6])],[(0,[z0,z12,z1,z377,z3,z6]),(0,[z0,z1,z3,z835,z4,z6]),(0,[z0,z1,z836,z3,z4,z6])]],
   [[(0,[z59,z0,z1,z2,z3,z827])],[(0,[z0,z12,z1,z3,z4,z6]),(0,[z0,z1,z837,z3,z4,z6]),(0,[z0,z192,z49,z3,z65,z6]),(0,[z0,z1,z158,z3,z4,z6])],[(0,[z0,z1,z225,z3,z4,z6]),(0,[z0,z12,z1,z3,z4,z241]),(0,[z0,z12,z1,z3,z370,z6])],[(0,[z0,z838,z1,z3,z4,z6]),(0,[z0,z1,z55,z3,z250,z6]),(0,[z0,z12,z1,z3,z143,z6]),(0,[z0,z1,z2,z3,z270,z312])],[(0,[z0,z187,z2,z547,z4,z6]),(0,[z0,z1,z284,z3,z74,z6]),(0,[z0,z1,z8,z3,z4,z839]),(0,[z0,z313,z1,z4,z6,z120])],[(0,[z0,z1,z2,z31,z4,z6])],[(0,[z0,z1,z3,z56,z250,z6]),(0,[z0,z1,z2,z110,z4,z241]),(0,[z0,z701,z12,z1,z3,z6]),(0,[z117,z1,z2,z3,z4,z112]),(0,[z0,z12,z1,z3,z6,z799]),(0,[z0,z1,z840,z3,z4,z6])],[(0,[z0,z1,z238,z3,z24,z6]),(0,[z0,z12,z3,z305,z164,z6]),(0,[z0,z12,z1,z3,z189,z6]),(0,[z0,z1,z2,z841,z4,z6]),(0,[z0,z1,z31,z103,z4,z6])]],
   [[(0,[z0,z1,z3,z842,z4,z6]),(0,[z0,z12,z1,z3,z4,z265]),(0,[z0,z1,z3,z38,z4,z6]),(0,[z0,z843,z2,z3,z4,z6]),(0,[z0,z12,z843,z3,z4,z6]),(0,[z0,z1,z8,z3,z4,z155]),(0,[z0,z1,z3,z4,z6,z844])],[(0,[z0,z1,z2,z845,z4,z6]),(0,[z554,z1,z2,z3,z4,z92]),(0,[z0,z1,z108,z2,z4,z536]),(0,[z0,z12,z1,z3,z280,z6]),(0,[z0,z1,z846,z3,z4,z6]),(0,[z0,z12,z620,z1,z3,z6]),(0,[z0,z1,z3,z4,z6,z847])],[(0,[z0,z187,z2,z3,z4,z6]),(0,[z0,z1,z848,z3,z4,z6]),(0,[z0,z1,z849,z3,z4,z6]),(0,[z489,z1,z2,z3,z74,z6]),(0,[z0,z1,z3,z4,z6,z850]),(0,[z0,z12,z1,z3,z195,z6]),(0,[z0,z12,z1,z3,z164,z6]),(0,[z0,z1,z851,z2,z4,z6]),(0,[z852,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z4,z853]),(0,[z0,z1,z2,z547,z4,z258]),(0,[z0,z152,z2,z547,z4,z6]),(0,[z0,z1,z2,z3,z854,z6]),(0,[z0,z1,z2,z3,z4,z855]),(0,[z0,z163,z12,z3,z164,z6]),(0,[z0,z1,z4,z6,z120,z469])],[(0,[z0,z12,z1,z3,z202,z6]),(0,[z0,z1,z856,z3,z4,z6])],[(0,[z224,z153,z2,z3,z4,z72]),(0,[z0,z857,z1,z2,z4,z6]),(0,[z0,z12,z1,z3,z204,z6]),(0,[z0,z12,z1,z3,z77,z6]),(0,[z0,z12,z1,z3,z207,z6]),(0,[z0,z12,z1,z858,z4,z6])],[(0,[z0,z12,z1,z3,z210,z6]),(0,[z0,z12,z187,z3,z4,z6]),(0,[z0,z1,z3,z859,z4,z6]),(0,[z0,z12,z1,z413,z3,z4]),(0,[z0,z11,z1,z2,z740,z6]),(0,[z0,z860,z1,z3,z4,z6])],[(0,[z0,z1,z225,z3,z210,z6]),(0,[z0,z1,z108,z2,z4,z549]),(0,[z0,z12,z1,z3,z324,z6]),(0,[z0,z82,z1,z755,z4,z6]),(0,[z0,z82,z1,z4,z6,z293]),(0,[z0,z11,z12,z1,z443,z6]),(0,[z0,z1,z238,z3,z56,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z861]),(0,[z1,z2,z3,z4,z862,z6]),(0,[z0,z1,z717,z56,z4,z6])],[(0,[z0,z1,z2,z3,z4,z258]),(1,[z1,z2,z3,z733,z6]),(0,[z0,z1,z61,z4,z6,z469])],[(0,[z0,z1,z2,z3,z210,z72]),(0,[z0,z1,z2,z3,z863,z6]),(0,[z0,z1,z803,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z864]),(0,[z0,z152,z496,z2,z4,z6]),(0,[z0,z1,z2,z3,z4,z865]),(0,[z0,z12,z1,z37,z95,z6])],[(0,[z0,z1,z546,z3,z4,z72]),(0,[z224,z153,z546,z3,z4,z6]),(0,[z0,z12,z1,z3,z6,z229]),(0,[z0,z1,z37,z38,z95,z6])],[(0,[z0,z1,z2,z3,z866,z6]),(0,[z0,z1,z867,z3,z4,z6]),(0,[z0,z1,z188,z2,z4,z92]),(0,[z0,z12,z1,z3,z379,z6]),(0,[z0,z12,z1,z868,z4,z6]),(0,[z0,z12,z1,z4,z869,z6]),(0,[z59,z0,z12,z1,z108,z3])],[(0,[z90,z1,z2,z41,z4,z6]),(0,[z0,z1,z2,z484,z4,z112]),(0,[z0,z182,z188,z2,z4,z81]),(0,[z0,z135,z1,z8,z3,z6]),(0,[z0,z82,z1,z354,z4,z6])],[(0,[z0,z1,z2,z3,z870,z6]),(0,[z0,z1,z2,z871,z4,z6]),(0,[z0,z152,z2,z711,z4,z6]),(0,[z0,z2,z3,z4,z747,z81]),(0,[z0,z599,z12,z1,z3,z6]),(0,[z0,z1,z217,z2,z3,z143]),(0,[z0,z12,z1,z4,z6,z120]),(0,[z0,z1,z2,z3,z4,z407])],[(0,[z625,z1,z2,z41,z4,z6]),(0,[z0,z1,z3,z56,z301,z6]),(0,[z0,z12,z1,z3,z420,z6]),(0,[z0,z12,z234,z3,z305,z6]),(0,[z0,z277,z3,z77,z4,z6]),(0,[z0,z1,z2,z3,z6,z827])]],
   [[(0,[z0,z12,z1,z188,z4,z6]),(0,[z0,z242,z234,z3,z4,z6])],[(0,[z0,z1,z872,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z873]),(0,[z320,z0,z12,z1,z3,z6]),(0,[z0,z1,z3,z726,z164,z6]),(0,[z0,z12,z1,z3,z248,z6]),(0,[z0,z82,z1,z31,z4,z6]),(0,[z0,z874,z1,z3,z4,z6])],[(0,[z0,z2,z3,z4,z875,z6]),(0,[z0,z12,z1,z3,z6,z253]),(0,[z0,z11,z1,z411,z32,z6])],[(0,[z0,z1,z2,z3,z876,z6]),(0,[z91,z1,z2,z267,z4,z92]),(0,[z0,z1,z2,z877,z4,z6]),(0,[z0,z878,z1,z2,z3,z6]),(0,[z0,z12,z1,z288,z3,z6]),(0,[z0,z1,z8,z2,z31,z4])],[(0,[z0,z1,z879,z3,z4,z6]),(0,[z0,z880,z2,z3,z4,z6]),(0,[z0,z12,z1,z3,z260,z6]),(0,[z0,z1,z2,z3,z881,z6]),(0,[z0,z1,z2,z3,z4,z882]),(0,[z455,z0,z109,z1,z3,z6]),(0,[z59,z0,z1,z3,z469,z62])],[(0,[z0,z1,z2,z3,z883,z6]),(0,[z0,z1,z2,z884,z4,z6]),(0,[z124,z1,z52,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z885]),(0,[z0,z2,z711,z3,z4,z6]),(0,[z0,z12,z886,z3,z4,z6]),(0,[z0,z1,z2,z3,z887,z6])],[(0,[z0,z1,z3,z56,z65,z6])],[(0,[z0,z1,z3,z888,z4,z6]),(0,[z0,z12,z1,z576,z3,z6]),(0,[z889,z1,z2,z3,z4,z6]),(0,[z0,z1,z890,z3,z4,z6])]],
   [[(0,[z0,z1,z272,z3,z305,z6]),(0,[z0,z12,z1,z246,z3,z6]),(0,[z524,z1,z3,z83,z4,z6])],[(0,[z0,z1,z3,z56,z325,z6]),(0,[z0,z12,z1,z3,z250,z6]),(0,[z0,z1,z8,z3,z4,z183]),(0,[z0,z1,z60,z2,z4,z698])],[(0,[z0,z891,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z892,z6]),(0,[z0,z135,z1,z3,z56,z6]),(0,[z0,z1,z3,z56,z4,z724]),(0,[z0,z1,z3,z56,z6,z348])],[(0,[z0,z1,z2,z3,z893,z6]),(0,[z0,z1,z272,z3,z4,z6]),(0,[z1,z2,z3,z788,z4,z6])],[(0,[z0,z1,z2,z3,z4,z894]),(0,[z0,z1,z895,z3,z4,z6]),(0,[z1,z2,z3,z733,z5,z6]),(0,[z0,z12,z1,z3,z461,z6])],[(0,[z0,z1,z896,z2,z3,z4]),(0,[z552,z0,z12,z1,z3,z6]),(0,[z0,z134,z2,z3,z4,z80])],[(0,[z0,z1,z2,z897,z4,z6]),(0,[z1,z2,z741,z3,z4,z6]),(0,[z0,z12,z1,z898,z3,z4])],[(0,[z0,z1,z2,z41,z4,z241]),(0,[z0,z175,z135,z1,z3,z6])]],
   [[(0,[z0,z1,z2,z899,z4,z6]),(0,[z0,z2,z3,z762,z164,z6]),(0,[z0,z12,z1,z3,z138,z6]),(0,[z0,z12,z1,z900,z4,z6]),(0,[z0,z1,z2,z31,z6,z57])],[(0,[z0,z1,z3,z56,z4,z6]),(0,[z0,z1,z3,z56,z376,z6]),(0,[z0,z1,z901,z3,z4,z6]),(0,[z0,z1,z216,z9,z4,z6])],[(0,[z0,z1,z2,z902,z4,z6]),(0,[z0,z1,z484,z56,z4,z6]),(0,[z0,z1,z2,z740,z32,z6]),(0,[z0,z1,z108,z103,z4,z310])],[(0,[z0,z1,z2,z903,z4,z6]),(0,[z0,z1,z904,z3,z4,z6]),(0,[z91,z12,z1,z3,z4,z92]),(0,[z0,z12,z1,z249,z3,z6])],[(0,[z0,z905,z2,z3,z4,z6]),(0,[z0,z1,z906,z2,z4,z6]),(0,[z0,z1,z8,z380,z3,z4])],[(0,[z0,z1,z2,z907,z4,z6]),(0,[z0,z1,z2,z3,z908,z6]),(0,[z0,z12,z1,z3,z307,z6]),(0,[z0,z1,z188,z2,z4,z112]),(0,[z0,z1,z3,z4,z6,z909]),(0,[z910,z1,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z4,z712])],[(0,[z0,z1,z2,z3,z911,z6]),(0,[z322,z1,z55,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z730]),(0,[z0,z1,z2,z4,z111,z565]),(0,[z0,z1,z912,z3,z4,z6]),(0,[z0,z1,z755,z2,z4,z6]),(0,[z59,z0,z12,z1,z3,z6]),(0,[z0,z397,z3,z4,z512,z6]),(0,[z0,z11,z1,z2,z407,z32])],[(0,[z0,z12,z1,z105,z4,z6]),(0,[z0,z1,z913,z2,z4,z6]),(0,[z1,z803,z2,z3,z4,z6]),(0,[z0,z160,z1,z3,z4,z183]),(0,[z0,z696,z12,z1,z3,z6]),(0,[z0,z1,z3,z4,z914,z6]),(0,[z0,z175,z1,z4,z213,z6]),(0,[z0,z1,z3,z365,z4,z366])]],
   [[(0,[z0,z1,z225,z105,z4,z6]),(0,[z0,z1,z915,z2,z4,z6]),(0,[z0,z1,z3,z916,z4,z6]),(0,[z0,z12,z215,z1,z3,z6]),(0,[z148,z0,z1,z3,z4,z383]),(0,[z0,z1,z3,z4,z6,z917])],[(0,[z0,z1,z918,z3,z4,z6]),(0,[z0,z1,z919,z3,z4,z6]),(0,[z0,z920,z1,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z921]),(0,[z0,z11,z1,z413,z2,z32])],[(0,[z0,z922,z1,z3,z4,z6]),(0,[z0,z12,z1,z3,z301,z6]),(0,[z0,z1,z923,z3,z4,z6]),(1,[z0,z1,z3,z4,z839]),(0,[z0,z1,z108,z2,z645,z4])],[(0,[z0,z1,z2,z484,z4,z6]),(0,[z820,z1,z2,z3,z4,z6]),(0,[z59,z0,z1,z61,z2,z62])],[(0,[z0,z1,z2,z4,z924,z6]),(0,[z0,z1,z2,z4,z925,z6]),(0,[z0,z1,z926,z3,z4,z6]),(0,[z0,z1,z413,z2,z3,z4])],[(0,[z0,z1,z99,z3,z4,z407]),(0,[z0,z1,z3,z4,z6,z927]),(0,[z59,z0,z313,z1,z3,z62])],[(0,[z0,z1,z3,z4,z6,z928])],[(0,[z40,z12,z1,z41,z4,z6]),(0,[z0,z1,z3,z4,z6,z929]),(0,[z0,z1,z2,z930,z4,z6]),(0,[z0,z1,z217,z3,z56,z4])]],
   [[(0,[z1,z55,z803,z3,z4,z6]),(0,[z46,z1,z2,z3,z74,z6]),(0,[z0,z1,z3,z143,z38,z6]),(0,[z0,z1,z2,z4,z111,z579])],[(0,[z0,z1,z2,z3,z4,z931]),(0,[z0,z1,z3,z932,z4,z6]),(0,[z0,z12,z1,z3,z65,z6]),(0,[z0,z1,z2,z3,z933,z6]),(0,[z0,z163,z3,z56,z164,z6]),(0,[z0,z1,z273,z16,z4,z6]),(0,[z0,z1,z108,z2,z4,z628]),(0,[z59,z0,z1,z61,z2,z4])],[(0,[z0,z934,z2,z3,z4,z6])],[(0,[z40,z1,z2,z741,z4,z6]),(0,[z12,z166,z1,z3,z74,z6]),(0,[z0,z298,z1,z443,z4,z6])],[(0,[z0,z1,z935,z2,z4,z6]),(0,[z0,z12,z1,z3,z325,z6]),(0,[z0,z1,z3,z936,z4,z6]),(0,[z0,z1,z2,z4,z750,z6]),(0,[z0,z821,z1,z3,z103,z6])],[(0,[z0,z2,z3,z4,z937,z6]),(0,[z0,z1,z31,z56,z4,z6])],[(0,[z0,z938,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z939,z6]),(0,[z0,z187,z2,z69,z4,z6]),(0,[z0,z1,z2,z3,z4,z940]),(0,[z0,z1,z941,z3,z4,z6]),(0,[z0,z1,z942,z3,z4,z6]),(0,[z0,z1,z2,z228,z6,z57])],[(0,[z0,z1,z2,z3,z4,z943]),(0,[z0,z1,z2,z105,z4,z258]),(0,[z0,z922,z1,z3,z210,z6]),(0,[z0,z1,z944,z3,z4,z6]),(0,[z0,z11,z12,z1,z37,z6])]],
   [[(0,[z0,z12,z1,z3,z356,z6]),(0,[z211,z1,z55,z3,z4,z6]),(0,[z0,z1,z945,z2,z3,z4]),(0,[z107,z290,z1,z3,z5,z6]),(0,[z0,z1,z216,z443,z4,z6]),(0,[z0,z1,z3,z4,z6,z253])],[(0,[z0,z1,z3,z946,z5,z6]),(0,[z0,z12,z1,z3,z305,z6]),(0,[z0,z947,z1,z3,z4,z6])],[(0,[z0,z1,z2,z547,z4,z72]),(0,[z224,z153,z2,z547,z4,z6]),(0,[z0,z12,z1,z3,z361,z6]),(0,[z0,z173,z2,z126,z4,z6]),(0,[z0,z135,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z948,z6]),(0,[z0,z1,z3,z4,z6,z949])],[(0,[z0,z12,z1,z3,z376,z6]),(0,[z0,z1,z3,z402,z301,z6]),(0,[z0,z1,z2,z950,z4,z6]),(0,[z0,z1,z413,z2,z95,z4]),(0,[z0,z1,z2,z4,z111,z712])],[(0,[z0,z1,z225,z3,z376,z6]),(0,[z0,z951,z2,z3,z4,z6]),(0,[z0,z1,z2,z952,z4,z6]),(0,[z0,z152,z2,z69,z4,z6]),(0,[z0,z12,z1,z37,z3,z6])],[(0,[z0,z1,z2,z3,z4,z953]),(0,[z0,z1,z954,z3,z4,z6]),(0,[z0,z11,z12,z1,z108,z6]),(0,[z0,z1,z3,z6,z57,z253])],[(0,[z0,z17,z1,z4,z228,z18])]],
   [[(0,[z0,z1,z2,z3,z4,z72]),(0,[z224,z153,z2,z3,z4,z6]),(0,[z0,z1,z546,z547,z4,z6]),(0,[z0,z1,z2,z3,z376,z72]),(0,[z0,z1,z2,z3,z955,z6]),(0,[z0,z135,z1,z113,z2,z3]),(0,[z0,z1,z956,z2,z4,z6])],[(0,[z0,z418,z2,z3,z4,z80])],[(0,[z0,z2,z126,z415,z4,z6]),(0,[z0,z1,z2,z957,z4,z6]),(0,[z0,z1,z2,z3,z4,z958]),(0,[z0,z1,z2,z739,z4,z6])],[(0,[z1,z2,z3,z4,z730,z112]),(0,[z0,z1,z2,z3,z959,z6]),(0,[z0,z1,z188,z2,z4,z6]),(0,[z0,z135,z1,z217,z2,z3]),(0,[z0,z82,z1,z560,z4,z6]),(0,[z0,z1,z413,z99,z3,z4]),(0,[z0,z1,z108,z2,z4,z310])],[(0,[z0,z12,z1,z3,z264,z6]),(0,[z0,z1,z3,z56,z6,z57])],[(0,[z0,z1,z960,z3,z4,z6]),(0,[z1,z2,z3,z74,z733,z6]),(0,[z0,z1,z2,z3,z961,z6]),(0,[z0,z962,z2,z3,z4,z6])],[(0,[z0,z1,z546,z3,z4,z6]),(0,[z0,z1,z963,z3,z4,z6]),(0,[z0,z1,z2,z3,z964,z6]),(0,[z0,z12,z109,z1,z3,z6]),(0,[z0,z1,z3,z56,z4,z965])],[(0,[z59,z0,z12,z1,z60,z3]),(0,[z0,z1,z3,z887,z103,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z966,z3,z4,z6]),(0,[z0,z1,z755,z216,z4,z6])],[(0,[z0,z1,z967,z3,z4,z6]),(0,[z0,z1,z3,z968,z4,z6]),(0,[z107,z1,z3,z24,z5,z6]),(0,[z0,z1,z119,z3,z4,z6]),(0,[z0,z2,z711,z69,z4,z6]),(0,[z0,z1,z3,z969,z4,z6])],[],[(0,[z0,z1,z371,z3,z4,z6]),(0,[z91,z1,z3,z56,z4,z92]),(0,[z0,z75,z76,z3,z4,z6]),(0,[z0,z12,z173,z126,z4,z6]),(0,[z0,z1,z970,z3,z4,z6]),(0,[z0,z1,z2,z4,z869,z6]),(0,[z971,z1,z3,z56,z4,z6])],[(0,[z0,z1,z2,z3,z376,z258]),(0,[z0,z1,z3,z972,z4,z6]),(0,[z107,z1,z2,z3,z5,z6]),(0,[z0,z12,z1,z562,z3,z6]),(0,[z0,z1,z238,z3,z6,z253])],[(0,[z224,z153,z2,z3,z210,z6]),(0,[z0,z973,z1,z2,z3,z6])],[(0,[z0,z1,z974,z2,z3,z4]),(0,[z0,z1,z3,z402,z4,z6]),(0,[z0,z975,z2,z3,z4,z6]),(0,[z0,z1,z976,z3,z4,z6])],[(0,[z0,z1,z2,z3,z977,z6]),(0,[z0,z2,z3,z4,z978,z6]),(0,[z0,z1,z2,z3,z979,z6]),(0,[z0,z1,z217,z2,z3,z4]),(0,[z0,z1,z413,z3,z56,z4])]],
   [[(0,[z0,z1,z2,z4,z6,z980]),(0,[z981,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z982,z6]),(0,[z0,z11,z12,z1,z111,z6]),(0,[z0,z1,z2,z3,z4,z839]),(1,[z0,z1,z2,z3,z827])],[(0,[z0,z983,z1,z3,z4,z6]),(0,[z0,z983,z1,z3,z376,z6]),(0,[z0,z1,z60,z2,z4,z571]),(0,[z0,z12,z1,z3,z366,z6])],[(0,[z146,z1,z3,z367,z4,z6]),(0,[z133,z1,z2,z741,z4,z6]),(0,[z0,z984,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z411,z6]),(0,[z322,z171,z1,z3,z4,z6]),(0,[z0,z17,z1,z31,z4,z18]),(0,[z0,z1,z108,z394,z2,z4])],[(0,[z0,z1,z2,z3,z4,z985]),(0,[z0,z1,z546,z3,z210,z6]),(0,[z0,z1,z986,z3,z4,z6]),(0,[z0,z1,z284,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z987]),(0,[z0,z1,z2,z988,z4,z6])],[(0,[z0,z109,z1,z2,z228,z6]),(0,[z0,z1,z2,z95,z740,z6])],[(0,[z0,z989,z1,z2,z3,z4]),(0,[z91,z1,z2,z484,z4,z92]),(0,[z0,z1,z990,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z991])],[(0,[z59,z0,z1,z3,z56,z62])],[(1,[z1,z803,z3,z4,z6]),(0,[z0,z992,z1,z2,z3,z6]),(0,[z0,z1,z113,z3,z4,z18]),(0,[z0,z11,z1,z99,z32,z6])]],
   [[(0,[z124,z166,z1,z3,z4,z6]),(0,[z0,z993,z1,z3,z4,z6]),(0,[z0,z1,z113,z216,z2,z4]),(0,[z0,z1,z108,z56,z4,z310])],[(0,[z0,z994,z2,z3,z4,z6]),(0,[z995,z1,z2,z3,z4,z6]),(0,[z0,z109,z1,z2,z31,z6])],[(0,[z0,z1,z3,z996,z210,z6]),(0,[z0,z1,z2,z3,z997,z6]),(0,[z0,z1,z998,z3,z4,z6]),(0,[z0,z1,z2,z3,z999,z6]),(0,[z0,z658,z12,z1,z3,z6]),(0,[z0,z12,z1,z3,z327,z6]),(0,[z0,z1,z3,z1000,z4,z6])],[(0,[z0,z1,z113,z216,z9,z4]),(0,[z0,z12,z1,z60,z4,z111])],[(0,[z0,z1,z2,z4,z1001,z6]),(0,[z0,z12,z1,z3,z446,z6]),(0,[z0,z12,z1,z3,z6,z447])],[(1,[z0,z2,z3,z4,z747]),(0,[z0,z1,z413,z3,z4,z411]),(0,[z0,z1,z1002,z3,z4,z6])],[(0,[z0,z1,z2,z793,z4,z6]),(0,[z0,z1,z2,z3,z1003,z6]),(0,[z0,z557,z2,z3,z164,z6]),(0,[z0,z1,z3,z946,z4,z6]),(0,[z0,z1,z2,z3,z6,z1004]),(0,[z0,z163,z3,z402,z164,z6]),(0,[z0,z12,z1,z3,z888,z6]),(0,[z0,z12,z1,z3,z456,z6])],[(0,[z0,z12,z1,z3,z422,z6]),(0,[z0,z1,z2,z900,z4,z6]),(0,[z0,z12,z1,z3,z6,z57])]],
   [[(0,[z0,z1,z3,z1005,z4,z6]),(0,[z0,z1006,z1,z3,z4,z6]),(0,[z0,z1,z1007,z3,z4,z6])],[],[(0,[z0,z1,z2,z3,z1008,z6])],[(0,[z0,z1,z2,z3,z4,z1009]),(0,[z0,z1,z1010,z3,z4,z6])],[(0,[z0,z1,z2,z3,z1011,z6]),(0,[z0,z290,z1,z3,z305,z6])],[(0,[z0,z1,z3,z1012,z4,z6]),(0,[z0,z1,z1013,z2,z3,z4]),(0,[z0,z187,z3,z56,z4,z6]),(0,[z0,z12,z1,z3,z946,z6]),(0,[z1014,z1,z2,z3,z4,z6]),(0,[z59,z0,z12,z1,z3,z147]),(0,[z0,z1,z3,z4,z6,z469])],[(0,[z0,z12,z135,z1,z3,z6]),(0,[z0,z1,z3,z4,z155,z839])],[(0,[z0,z1,z547,z56,z4,z6]),(0,[z0,z290,z1,z3,z4,z6]),(0,[z0,z1015,z2,z3,z4,z6]),(0,[z0,z12,z1,z267,z4,z6]),(0,[z0,z1,z267,z56,z4,z6]),(0,[z0,z1,z1016,z3,z4,z6]),(0,[z0,z1,z61,z2,z270,z4])]],
   [[(0,[z0,z1,z2,z3,z4,z1017]),(0,[z0,z125,z1,z3,z56,z6]),(0,[z339,z1,z2,z110,z4,z6]),(0,[z0,z1,z108,z2,z4,z100]),(0,[z0,z12,z1,z3,z480,z6]),(0,[z0,z1,z113,z3,z103,z4]),(0,[z0,z1,z89,z4,z213,z6]),(0,[z0,z821,z1,z108,z3,z6])],[(0,[z0,z12,z1,z3,z520,z6]),(0,[z0,z1,z3,z1018,z4,z6])],[(0,[z1,z2,z3,z1019,z4,z6]),(0,[z0,z12,z1,z3,z38,z6]),(0,[z0,z109,z1,z3,z155,z6])],[(0,[z524,z1,z52,z3,z4,z6]),(0,[z0,z1020,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z4,z747]),(0,[z0,z1,z89,z755,z4,z6]),(0,[z0,z12,z1,z3,z745,z6])],[(0,[z0,z1,z1021,z3,z4,z6]),(0,[z0,z82,z1,z89,z4,z6]),(0,[z0,z12,z1,z3,z444,z6]),(0,[z0,z1,z2,z3,z270,z147])],[(0,[z0,z1,z1022,z3,z4,z6]),(0,[z0,z1,z1023,z3,z4,z6]),(0,[z0,z3,z56,z4,z752,z6]),(0,[z0,z757,z3,z56,z4,z6]),(0,[z0,z1,z61,z2,z4,z6])],[(0,[z0,z1,z2,z105,z4,z72]),(0,[z224,z153,z2,z105,z4,z6]),(0,[z40,z1,z2,z41,z4,z6]),(0,[z0,z1024,z1,z3,z4,z6]),(0,[z0,z12,z1,z3,z468,z6]),(0,[z59,z0,z1,z2,z3,z679])],[(0,[z352,z1,z2,z110,z4,z6]),(0,[z322,z1,z2,z3,z74,z6]),(0,[z0,z2,z3,z4,z762,z6]),(0,[z0,z1,z2,z3,z6,z1025]),(0,[z0,z12,z1,z826,z4,z6])]],
   [[(0,[z224,z12,z153,z3,z4,z6]),(0,[z133,z12,z1,z110,z4,z6]),(0,[z0,z290,z1,z3,z164,z6])],[(0,[z0,z1,z1026,z3,z4,z6]),(0,[z0,z131,z2,z3,z164,z6]),(0,[z0,z1,z3,z4,z155,z235])],[(0,[z133,z1,z110,z56,z4,z6]),(0,[z0,z2,z3,z4,z6,z1027]),(0,[z0,z12,z1,z3,z498,z6]),(1,[z0,z2,z711,z4,z6])],[(0,[z0,z1,z2,z4,z1028,z6]),(0,[z0,z1,z2,z3,z325,z6]),(1,[z1,z2,z3,z4,z730]),(1,[z0,z2,z3,z762,z6]),(0,[z833,z12,z1,z3,z4,z6]),(0,[z0,z1,z3,z4,z366,z18])],[(0,[z0,z1,z546,z105,z4,z6]),(0,[z1,z2,z3,z4,z1029,z6])],[(0,[z0,z1,z2,z547,z4,z6]),(0,[z0,z1,z1030,z3,z4,z6]),(0,[z124,z1,z803,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1031]),(0,[z0,z12,z1,z459,z3,z6]),(0,[z0,z1,z1032,z2,z3,z4]),(0,[z0,z82,z1,z113,z2,z4]),(0,[z0,z11,z12,z1,z32,z6]),(0,[z0,z1,z2,z3,z740,z6])],[(0,[z0,z1,z619,z3,z56,z6]),(0,[z0,z1,z898,z2,z3,z4]),(0,[z0,z1,z108,z2,z652,z4]),(0,[z59,z0,z1,z2,z3,z62])],[(0,[z0,z1,z3,z83,z250,z6]),(0,[z0,z12,z1,z63,z3,z6]),(0,[z0,z49,z748,z3,z4,z6]),(0,[z0,z12,z1,z190,z3,z6]),(0,[z0,z1,z2,z4,z6,z712])]],
   [[(0,[z0,z1033,z1,z2,z3,z6]),(0,[z0,z1,z2,z4,z607,z6]),(0,[z0,z1,z37,z3,z888,z6]),(0,[z0,z12,z1,z651,z3,z6])],[(0,[z0,z1,z3,z1034,z4,z6]),(0,[z0,z1,z2,z4,z1035,z6]),(0,[z0,z75,z748,z3,z4,z6]),(0,[z0,z748,z2,z3,z4,z6]),(0,[z0,z1036,z1,z3,z4,z6]),(0,[z0,z1,z3,z1037,z4,z6]),(0,[z0,z1,z1038,z3,z4,z6]),(0,[z0,z17,z1,z3,z4,z383]),(0,[z0,z12,z1,z3,z523,z6])],[(0,[z0,z470,z12,z1,z3,z6]),(0,[z0,z1,z1039,z3,z4,z6]),(0,[z0,z1,z56,z4,z228,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z1040,z2,z4,z6]),(0,[z0,z1,z1041,z3,z4,z6]),(0,[z0,z1,z2,z3,z1042,z6]),(0,[z0,z12,z1,z31,z4,z6])],[(0,[z0,z1,z1043,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1044]),(0,[z0,z1,z2,z3,z4,z241]),(0,[z0,z1,z1045,z3,z4,z6])],[(0,[z0,z1,z2,z3,z143,z6]),(0,[z0,z1,z3,z56,z705,z6])],[(0,[z0,z1,z2,z3,z4,z1046]),(0,[z0,z1,z2,z3,z147,z827])],[(0,[z0,z1,z2,z3,z4,z1047]),(0,[z0,z1,z3,z1048,z4,z6]),(0,[z0,z1,z3,z4,z839,z18])]],
   [[(0,[z0,z1,z2,z711,z4,z6]),(0,[z0,z1049,z1,z2,z3,z6]),(0,[z0,z1,z3,z56,z586,z6])],[(0,[z0,z1,z2,z3,z4,z1050]),(0,[z0,z1,z2,z1051,z4,z6]),(0,[z1052,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z762,z6]),(0,[z0,z1,z3,z4,z6,z839])],[(0,[z0,z1,z2,z547,z210,z6]),(0,[z0,z1,z2,z3,z4,z265]),(0,[z0,z1,z2,z3,z4,z827])],[(0,[z224,z153,z2,z3,z376,z6]),(0,[z0,z601,z1,z3,z56,z6]),(0,[z0,z12,z1,z451,z3,z6]),(0,[z0,z11,z1,z2,z32,z6])],[(0,[z0,z1,z2,z1053,z4,z6]),(0,[z0,z1,z2,z1054,z4,z6]),(0,[z0,z1,z2,z3,z4,z1055]),(0,[z0,z1,z3,z1056,z4,z6])],[(0,[z0,z1,z1057,z3,z4,z6]),(0,[z0,z1,z1058,z3,z4,z6]),(0,[z0,z1,z2,z3,z4,z1059]),(0,[z0,z182,z2,z4,z607,z81]),(0,[z0,z12,z751,z3,z4,z6])],[(0,[z0,z1,z2,z1060,z4,z6]),(0,[z0,z12,z1,z3,z4,z861]),(0,[z0,z1,z60,z2,z4,z712])],[(0,[z0,z12,z1,z3,z4,z258]),(0,[z0,z1,z2,z858,z4,z6]),(0,[z0,z1061,z1,z3,z4,z6]),(0,[z0,z1062,z2,z3,z4,z6]),(0,[z91,z1,z2,z3,z4,z730]),(0,[z0,z1,z2,z3,z4,z1063])]],
   [[(0,[z0,z1,z2,z3,z210,z6]),(0,[z0,z1,z225,z3,z4,z258]),(0,[z0,z1,z2,z1064,z4,z6]),(0,[z0,z182,z2,z3,z4,z81]),(0,[z0,z12,z1,z775,z3,z4]),(0,[z0,z1,z2,z37,z13,z6])],[(0,[z0,z1,z546,z3,z376,z6]),(0,[z0,z12,z1,z273,z3,z6])],[(0,[z0,z1065,z1,z3,z4,z6]),(0,[z0,z1,z1066,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z1067])],[(0,[z0,z1068,z1,z3,z4,z6]),(0,[z0,z1069,z1,z3,z4,z6]),(0,[z0,z1,z2,z3,z147,z50])],[(0,[z0,z1070,z1,z2,z3,z6]),(0,[z0,z1,z2,z4,z6,z1071]),(0,[z0,z1072,z1,z3,z4,z6]),(0,[z0,z1,z216,z143,z9,z6]),(0,[z0,z12,z1,z3,z4,z407]),(0,[z0,z1,z2,z37,z95,z6])],[(0,[z0,z1,z1073,z3,z4,z6]),(0,[z0,z118,z272,z3,z305,z6]),(0,[z0,z12,z134,z3,z4,z80]),(0,[z0,z1,z2,z4,z111,z357]),(0,[z0,z734,z2,z3,z4,z6]),(1,[z0,z1,z2,z740,z6]),(0,[z0,z1,z60,z2,z4,z111])],[(0,[z0,z187,z108,z2,z4,z6]),(0,[z0,z1,z3,z1074,z4,z6]),(0,[z0,z12,z1,z3,z165,z6]),(0,[z0,z12,z1,z3,z6,z566])],[(0,[z0,z1,z2,z3,z1075,z6])]],
   [[(0,[z0,z1,z3,z996,z4,z6]),(0,[z0,z886,z2,z3,z4,z6]),(0,[z0,z187,z2,z126,z4,z6]),(0,[z0,z1,z1076,z3,z4,z6]),(0,[z0,z1,z2,z4,z6,z120])],[(0,[z503,z1,z2,z3,z5,z6]),(0,[z0,z12,z1,z877,z4,z6]),(0,[z0,z88,z1,z560,z4,z6]),(0,[z0,z1,z3,z4,z745,z6])],[(0,[z0,z12,z1,z3,z643,z6])],[(0,[z0,z2,z126,z547,z4,z6]),(0,[z0,z1,z3,z1077,z4,z6]),(0,[z46,z1,z3,z56,z74,z6]),(0,[z0,z12,z1,z3,z726,z6]),(0,[z0,z118,z3,z56,z305,z6]),(0,[z0,z472,z12,z1,z3,z6]),(0,[z0,z1,z3,z56,z745,z6])],[(0,[z0,z1,z2,z3,z4,z1078]),(0,[z0,z1,z108,z2,z4,z254])],[(0,[z0,z1,z1079,z3,z4,z6]),(0,[z0,z12,z575,z1,z3,z6])],[(0,[z59,z0,z1,z2,z3,z383]),(0,[z0,z11,z1,z99,z3,z6])],[(0,[z0,z1,z1080,z3,z4,z6]),(0,[z0,z1,z868,z2,z4,z6])]],
   [[(0,[z0,z1,z2,z1081,z4,z6]),(0,[z0,z175,z12,z1,z3,z6]),(0,[z0,z11,z12,z1,z560,z6]),(0,[z0,z11,z1,z56,z32,z6]),(0,[z0,z1,z108,z2,z346,z4]),(0,[z0,z11,z1,z2,z679,z6])],[(0,[z0,z12,z1,z3,z39,z6]),(0,[z1,z803,z52,z3,z4,z6]),(0,[z0,z2,z3,z4,z80,z747]),(0,[z0,z1,z2,z3,z4,z712])],[(0,[z0,z1,z2,z3,z6,z1082]),(0,[z1,z2,z3,z4,z6,z730]),(0,[z0,z1,z99,z3,z4,z6])],[(0,[z0,z1,z2,z3,z250,z6]),(0,[z0,z1,z188,z56,z4,z6]),(0,[z0,z1,z1083,z3,z4,z6]),(0,[z0,z1,z99,z37,z3,z6])],[(0,[z0,z1,z1084,z3,z4,z6]),(0,[z0,z2,z3,z4,z6,z1085]),(0,[z0,z1086,z1,z3,z4,z6])],[(0,[z0,z12,z1,z3,z6,z594]),(0,[z115,z1,z2,z3,z4,z112]),(0,[z0,z12,z182,z3,z4,z81]),(0,[z0,z12,z1,z3,z287,z6])],[(0,[z0,z2,z126,z711,z4,z6]),(0,[z0,z12,z1,z3,z70,z6]),(0,[z0,z1,z2,z3,z6,z57]),(0,[z0,z17,z1,z3,z103,z4])],[(0,[z0,z12,z1,z3,z19,z6]),(0,[z46,z1,z47,z3,z74,z6]),(0,[z0,z135,z1,z216,z3,z6])]],
   [[(0,[z0,z1,z2,z1087,z4,z6]),(0,[z0,z1,z2,z741,z4,z6]),(0,[z0,z1,z3,z4,z1088,z6]),(0,[z0,z12,z1,z3,z387,z6]),(0,[z0,z1,z2,z3,z4,z965]),(0,[z0,z12,z1,z3,z87,z6])],[(0,[z0,z1,z2,z3,z1089,z6])],[(0,[z0,z1,z2,z1090,z4,z6]),(0,[z0,z12,z1,z3,z74,z6]),(0,[z584,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z1091,z4,z6]),(0,[z0,z748,z76,z3,z4,z6]),(0,[z0,z1,z60,z56,z4,z111]),(0,[z0,z1,z108,z197,z4,z310]),(0,[z0,z1,z3,z1092,z4,z6])],[(0,[z0,z1,z2,z1093,z4,z6]),(0,[z0,z1,z3,z56,z4,z72]),(0,[z1,z746,z2,z3,z4,z6]),(0,[z0,z427,z2,z3,z305,z6]),(0,[z0,z1,z216,z103,z4,z6])],[(0,[z0,z1,z1094,z3,z4,z6]),(0,[z117,z1,z3,z56,z4,z112]),(0,[z1095,z1,z2,z3,z4,z6]),(0,[z392,z166,z1,z3,z4,z6]),(0,[z0,z1,z238,z3,z38,z6])],[(0,[z0,z187,z2,z4,z111,z6]),(0,[z91,z1,z2,z3,z4,z92]),(0,[z971,z1,z2,z3,z4,z6]),(0,[z0,z1,z108,z2,z4,z302]),(0,[z0,z1,z238,z3,z745,z6])],[(0,[z0,z1,z3,z1096,z4,z6]),(0,[z0,z163,z284,z3,z164,z6]),(0,[z0,z821,z1,z2,z3,z6])],[(0,[z0,z1,z2,z3,z4,z1097]),(0,[z0,z1,z2,z3,z6,z1098]),(0,[z455,z0,z1,z3,z4,z235]),(0,[z0,z1,z158,z3,z270,z147])]],
   [[(0,[z0,z1,z3,z1012,z376,z6]),(0,[z0,z1099,z2,z3,z4,z6]),(0,[z0,z1,z3,z4,z1100,z6]),(0,[z0,z1,z3,z1101,z4,z6]),(0,[z0,z1,z1102,z3,z4,z6]),(0,[z0,z1,z3,z103,z4,z6]),(0,[z59,z0,z313,z1,z3,z6])],[(0,[z0,z1,z2,z105,z4,z6]),(0,[z34,z1,z52,z3,z4,z6]),(0,[z0,z1,z1103,z3,z4,z6]),(0,[z0,z12,z1,z484,z4,z6]),(0,[z0,z1,z2,z3,z6,z1104]),(0,[z0,z12,z962,z3,z4,z6]),(0,[z0,z17,z1,z3,z4,z839]),(0,[z0,z1,z2,z3,z827,z62])],[(0,[z0,z746,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z6,z1105])],[(0,[z0,z1,z2,z3,z1106,z6]),(0,[z0,z1,z2,z3,z1107,z6]),(0,[z0,z1,z1108,z2,z3,z4]),(0,[z0,z1,z2,z3,z6,z1109]),(0,[z59,z0,z12,z1,z3,z62]),(0,[z0,z12,z1,z4,z228,z6])],[(0,[z0,z198,z76,z3,z4,z6]),(0,[z0,z1,z2,z3,z301,z6]),(0,[z0,z82,z1,z103,z4,z6])],[(0,[z746,z153,z2,z3,z4,z6]),(0,[z0,z1,z2,z1110,z4,z6]),(0,[z146,z1,z55,z3,z325,z6]),(0,[z0,z1,z113,z8,z3,z4]),(0,[z455,z0,z12,z1,z3,z6])],[(0,[z46,z12,z1,z3,z74,z6]),(0,[z0,z1,z1111,z2,z4,z6]),(0,[z1,z2,z3,z4,z6,z1112]),(0,[z0,z1,z2,z1113,z4,z6]),(0,[z0,z1114,z1,z3,z4,z6])],[(0,[z0,z1,z2,z1115,z4,z6]),(0,[z0,z1,z3,z56,z4,z258]),(0,[z133,z1,z2,z110,z4,z6]),(0,[z0,z1,z1116,z3,z4,z6]),(0,[z107,z1,z3,z56,z5,z6]),(0,[z0,z12,z118,z3,z305,z6]),(0,[z0,z1,z3,z147,z6,z799])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 527) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 527).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1055).take 132) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1187)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [527, 528, 132] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 113).take 129).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 242).take 14).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [113, 129, 14] = true :=
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

end PEqualNP.Outside.L_meta_42980

theorem PEqualNP.Outside.L_meta_42980 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677320 * 2 ^ 32 + 4209027584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677320 * 2 ^ 32 + 4209027584) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_42980.solve