import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37845

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
  Nat.testBit (4277074632 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x400850e3022ac792#64 ++ 0x020042871811563c#64 ++ 0xa058d3e7067ecf9e#64 ++ 0xfd02c69f3833f67c#64 : BitVec 256),
   (0x8083220d18990aa4#64 ++ 0x2404191068c4c855#64 ++ 0x69a7223f39990ffd#64 ++ 0xfb4d3911f9ccc87f#64 : BitVec 256),
   (0x0238143041605158#64 ++ 0x0811c0a1820b028a#64 ++ 0xf6383c38c1e1f1fb#64 ++ 0xd7b1c1e1c60f0f8f#64 : BitVec 256),
   (0x05c02b40ae01ac00#64 ++ 0xb02e015a05700d60#64 ++ 0xf7c03fc0fe01fe17#64 ++ 0xcfbe01fe07f00ff0#64 : BitVec 256),
   (0x07758000f5d40000#64 ++ 0xc03bac0007aea000#64 ++ 0xffffc000fffe000f#64 ++ 0xbffffe0007fff000#64 : BitVec 256),
   (0x0ffeffbe0000001f#64 ++ 0x007ff7fdf0000000#64 ++ 0xefffffff00000000#64 ++ 0x7f7ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [3, 7]⟩, ⟨.or, [3, 7]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [11, 4]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6383c38c1e1f1fb 0xd7b1c1e1c60f0f8f

def z1 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fc0fe01fe17 0xcfbe01fe07f00ff0

def z2 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc000fffe000f 0xbffffe0007fff000

def z3 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x09c7c3c700000000 0x284e3e1e38000000

def z4 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058d3e7067ecf9e 0xfd02c69f3833f67c

def z5 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7223f39990ffd 0xfb4d3911f9ccc87f

def z6 : W := mkw 0x8dc7eb8f18990aa7 0x246e3f5c78c4c855 0x69e7e3ff39990ffd 0xfb4f3f1ff9ccc87f

def z7 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff00000000 0x7f7ffffff8000000

def z8 : W := mkw 0x400850a3002a4392 0x020042851801521c 0x0018c027007e0188 0x3000c6013803f00c

def z9 : W := mkw 0x423854f3436ad7da 0x0a11c2a79a1b56be 0xf678ffffc7ffffff 0xffb3c7fffe3fffff

def z10 : W := mkw 0x40000041022ac780 0x020000020811563c 0x000000000000cf90 0x000000000000067c

def z11 : W := mkw 0x0774800000000000 0x003ba40000000000 0xefffc000067e000e 0xbf7ffe000033f000

def z12 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc1e1f1fb 0xfffffffffe0f0f8f

def z13 : W := mkw 0x8001000118990aa0 0x2400080008c4c855 0x0000000039990ffd 0x8000000001ccc87f

def z14 : W := mkw 0x00000040ae01ac00 0xb000000205700d60 0xf6003c00fe01fe17 0xc7b001e007f00ff0

def z15 : W := mkw 0x00000040ae01ac00 0xb000000205700d60 0x10000000fe01fe17 0x8080000007f00ff0

def z16 : W := mkw 0x0a3ed4be0000001f 0x0051f6a5f0000000 0x083fc03f00000000 0x3041fe01f8000000

def z17 : W := mkw 0x8fffffbf18990abf 0x247ffffdf8c4c855 0xefffffff39990ffd 0xff7ffffff9ccc87f

def z18 : W := mkw 0x0f7cddb20000001b 0x007be6ed90000000 0x8658ddc000000000 0x0432c6ee00000000

def z19 : W := mkw 0x0ffefffeef61fd5f 0xb87ff7fff77b0fea 0xffffffffffe1ffff 0xffffffffffff0fff

def z20 : W := mkw 0x8003000d18990aa4 0x2400180068c4c855 0x0827003f39990ffd 0xb0413801f9ccc87f

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x60202038018101f9 0xd3010101c00c080f

def z22 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x97c01fc0fe00fe06 0x0cbe00fe07f007f0

def z23 : W := mkw 0x8777800df5dc02a4 0xc43bbc006faee015 0xffffc03ffffe01ef 0xbffffe01fffff00f

def z24 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x5fa70000f9800001 0x02fd380007cc0000

def z25 : W := mkw 0x477dd0e3f7fec792 0xc23bee871fbff63c 0xffffd3e7fffecf9f 0xfffffe9f3ffff67c

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x56002c00c0013001 0x02b0016006000980

def z27 : W := mkw 0x0001000010900000 0x0000080000848000 0x69a700003998000d 0xbb4d380001ccc000

def z28 : W := mkw 0x0000000100080280 0x0000000008004014 0x6020223f01990ffd 0xfb010111f80cc87f

def z29 : W := mkw 0x45c87be3022ac792 0x022e43df1811563c 0xe7d8ffe7067ecf9e 0xff3ec7ff3833f67c

def z30 : W := mkw 0xc00b50ef12bac7b6 0x06005a877895d63d 0xa87fd3ff07fecffe 0xfd43fe9ff83ff67f

def z31 : W := mkw 0x05400940a600a400 0x902a004a05300520 0xf7c01dc0fe00f007 0x8fbe00ee07f00780

def z32 : W := mkw 0x8001000118990aa0 0x2400080008c4c855 0x6020203839990ffd 0xd3010101c1ccc87f

def z33 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x96181c00c060f002 0x04b0c0e006030780

def z34 : W := mkw 0x82bb363d59f95bfc 0x2c15d9b1eacfcadf 0xffbf3e3ff9f9ffff 0xfffdf9f1ffcfcfff

def z35 : W := mkw 0x05c22b0c00000004 0x002e115860000000 0xefe73fff00000000 0x7f7f39fff8000000

def z36 : W := mkw 0x80010041be99aea0 0xb40008020df4cd75 0x10000000ff99ffff 0x8080000007fccfff

def z37 : W := mkw 0x0000000100080280 0x0000000008004014 0x0000000000180f9c 0x800000000000c07c

def z38 : W := mkw 0x0000000000000000 0x0000000000000000 0xe6003c0000000000 0x473001e000000000

def z39 : W := mkw 0x0ffefffe0a01ac1f 0x307ff7fff0500d60 0xefffffff0001fe10 0x7f7ffffff8000ff0

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0x00003c000001f010 0x400001e000000f80

def z41 : W := mkw 0x000850a200000012 0x0000428510000000 0xa058d3e700000000 0x7d02c69f38000000

def z42 : W := mkw 0x0000000041400000 0x00000000020a0000 0x10000000c1e0000b 0x80800000060f0000

def z43 : W := mkw 0x0ffefffeae01ac1f 0xb07ff7fff5700d60 0xfffffffffe01fe17 0xfffffffffff00ff0

def z44 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffe038ffff01ff 0xffffff01c7fff80f

def z45 : W := mkw 0x0230000041400000 0x00118000020a0000 0xf6383c00c1e1f01b 0xd7b1c1e0060f0f80

def z46 : W := mkw 0x0000004002008400 0x0000000200100420 0xa058d3c0067ece1e 0xfd02c69e0033f670

def z47 : W := mkw 0x400850a3002a4392 0x020042851801521c 0x0000002700000180 0x000000013800000c

def z48 : W := mkw 0x0002000c00000004 0x0000100060000000 0x0827003f00000000 0x30413801f8000000

def z49 : W := mkw 0x0aba7fbe4160515f 0x0855d3fdf20b028a 0xf6383fffc1e1f1fb 0xd7b1c1fffe0f0f8f

def z50 : W := mkw 0x400850e20222c512 0x0200428710111628 0x000011c00000c000 0x0000008e00000600

def z51 : W := mkw 0x400850e3436ad7d2 0x0a0042871a1b56be 0xb058d3e7c7ffffff 0xfd82c69f3e3fffff

def z52 : W := mkw 0x00000000e5440000 0xc0000000072a2000 0x10000000c6660002 0x0080000006333000

def z53 : W := mkw 0x0ff6af1c0000000d 0x007fb578e0000000 0x4fa72c1800000000 0x027d3960c0000000

def z54 : W := mkw 0x0ff6ef9e0000000f 0x007fb77cf0000000 0x4fe7efdf00000000 0x2a7f3f7ef8000000

def z55 : W := mkw 0x0abeffbe0000001f 0x0055f7fdf0000000 0x083fffff00000000 0x7041fffff8000000

def z56 : W := mkw 0x000850e202008412 0x0000428710100420 0xa058d3e70600ce16 0xfd02c69f38300670

def z57 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058d3e70000cf90 0x7d02c69f3800067c

def z58 : W := mkw 0x07748000e5440000 0xc03ba400072a2000 0x9658c000c6660002 0x04b2c60006333000

def z59 : W := mkw 0x07f5ab40ffd5ac00 0xf03fad5a07fead60 0xffffc3c0fffe0e0f 0xbffffe1e07fff070

def z60 : W := mkw 0x400040c3020a8682 0x0200020618105434 0x0040c3c7061e0e04 0x2802061e3830f070

def z61 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc060f002 0x7ffffffffe030780

def z62 : W := mkw 0x8083220d109802a4 0x040419106884c015 0x69a7223f019801e8 0x7b4d3911f80cc00f

def z63 : W := mkw 0x05400940a600a400 0x902a004a05300520 0x96401dc0c600f002 0x04b200ee06300780

def z64 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf678fc38c7fff1ff 0xffb3c7e1c63fff8f

def z65 : W := mkw 0x0774800041400000 0x003ba400020a0000 0xffffc000c1e0000b 0xbffffe00060f0000

def z66 : W := mkw 0x088a7fbe0000001f 0x004453fdf0000000 0x00003fff00000000 0x400001fff8000000

def z67 : W := mkw 0x07f4ab40ef45ac00 0xf03fa55a077a2d60 0xf7d8ffc0fe67fe17 0xcfbec7fe07f33ff0

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z69 : W := mkw 0x080a54be0000001f 0x004052a5f0000000 0x0000003f00000000 0x00000001f8000000

def z70 : W := mkw 0x023854b24160515a 0x0811c2a5920b028a 0xf678ffffc1e1f1fb 0xffb3c7fffe0f0f8f

def z71 : W := mkw 0x0230000041400000 0x00118000020a0000 0xf6380000c1e0000b 0x97b1c000060f0000

def z72 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x69e7e3ff00000000 0x7b4f3f1ff8000000

def z73 : W := mkw 0x0000000000000000 0x0000000000000000 0xa040000006000006 0x8d02000000300000

def z74 : W := mkw 0x0235800051d40000 0x4011ac00028ea000 0x083fc00001fe0008 0x3041fe00000ff000

def z75 : W := mkw 0x07f5ab40ffd5ac00 0xf03fad5a07fead60 0xffffffc0fffffe1f 0xfffffffe07fffff0

def z76 : W := mkw 0x07f83f30ed617958 0xb83fc1f9876b0bca 0xf7b83c38f9e1f1fb 0xd7bdc1e1c7cf0f8f

def z77 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffe70000ff800007 0x8fff380007fc0000

def z78 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x96381c38c1e0f1ea 0x14b1c0e1c60f078f

def z79 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0xffc7c000fe1e0007 0xaffe3e0007f0f000

def z80 : W := mkw 0x0008143000205158 0x080040a18001028a 0x00003c380001f1f0 0x400001e1c0000f8f

def z81 : W := mkw 0x0fffffbef5d4001f 0xc07ffffdf7aea000 0xfffffffffffe000f 0xfffffffffffff000

def z82 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x200013e70018cf9c 0xf900009f3800c67c

def z83 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x09ffc3ff00000000 0x384ffe1ff8000000

def z84 : W := mkw 0x0230041041401048 0x08118020820a0082 0x56202c18c1813061 0x02b10160c60c0983

def z85 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0xa9dfc0003e7e000e 0xbd4efe0001f3f000

def z86 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x0038003801e001e8 0x1001c001c00f000f

def z87 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x01c003c03e000e04 0x080e001e01f00070

def z88 : W := mkw 0x088a7fbe0020515f 0x084453fdf001028a 0x00003fff0001f1f0 0x400001fff8000f8f

def z89 : W := mkw 0x87f7a20dfddd0aa4 0xe43fbd106feee855 0xffffe23fffff0fff 0xffffff11fffff87f

def z90 : W := mkw 0x05c02b0000000000 0x002e015800000000 0xe7c03fc000000000 0x4f3e01fe00000000

def z91 : W := mkw 0x0000000000000000 0x0000000000000000 0x4020201801810061 0x02010100c00c0803

def z92 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x4fbfec3f00000000 0x327dff61f8000000

def z93 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x56203c38c181f1f1 0x42b101e1c60c0f8f

def z94 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x000013e70000cf90 0x4000009f3800067c

def z95 : W := mkw 0x0001000010900000 0x0000080000848000 0x0827000001980008 0x30413800000cc000

def z96 : W := mkw 0x0000000041605140 0x08000000020b028a 0xf6003c00c1e1f1fb 0xc7b001e0060f0f8f

def z97 : W := mkw 0x4ffeffff022ac79f 0x027ff7fff811563c 0xefffffff067ecf9e 0xff7ffffff833f67c

def z98 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x2987022738180f9c 0xf94c381139c0c07c

def z99 : W := mkw 0x077c943041605158 0x083be4a1820b028a 0xfffffc38c1e1f1fb 0xffffffe1c60f0f8f

def z100 : W := mkw 0x0082220c00000004 0x0004111060000000 0x69a7223f00000000 0x7b4d3911f8000000

def z101 : W := mkw 0xc08a72ef0a2bcfb6 0x2604539778515e7d 0x000033ff0001cff0 0x4000019ff8000e7f

def z102 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0x09c7c0003e1e0004 0x284e3e0001f0f000

def z103 : W := mkw 0x0fffffbeb494001f 0xc07ffffdf5a4a000 0xefffffff3e1e0004 0x7f7ffffff9f0f000

def z104 : W := mkw 0x07f02b40ef41ac00 0xb03f815a077a0d60 0xf7f83fc0ffe1fe1f 0xdfbfc1fe07ff0ff0

def z105 : W := mkw 0x0000000000000000 0x0000000000000000 0x6020000001800009 0x93010000000c0000

def z106 : W := mkw 0x0544800000000000 0x002a240000000000 0x09c7c00000000000 0x284e3e0000000000

def z107 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xffa73e3ff999ffff 0xfffd39f1ffcccfff

def z108 : W := mkw 0x0f7cddb24160515b 0x087be6ed920b028a 0x9658ddc0c060f002 0x04b2c6ee06030780

def z109 : W := mkw 0x40000041022ac780 0x020000020811563c 0x00000000067ecf9e 0x800000000033f67c

def z110 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x5fe7c000ff9e0005 0x2aff3e0007fcf000

def z111 : W := mkw 0x00000040a600a400 0x9000000205300520 0x10000000c600f002 0x0080000006300780

def z112 : W := mkw 0x40000041022ac780 0x020000020811563c 0xa04013c0067ecf9e 0xcd02009e0033f67c

def z113 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x56382c38c1e131e9 0x12b1c161c60f098f

def z114 : W := mkw 0x05c02b4002008400 0x002e015a00100420 0xe7c03fc00600ce16 0xcf3e01fe00300670

def z115 : W := mkw 0x05c02b0000000000 0x002e015800000000 0x01c003c000000000 0x080e001e00000000

def z116 : W := mkw 0x8083220c18910824 0x2404191060c48841 0x49a7201839810061 0x024d3900c1cc0803

def z117 : W := mkw 0x07f5ab00f5d40000 0xc03fad5807aea000 0xffffffc0fffe000f 0xfffffffe07fff000

def z118 : W := mkw 0x8003000d109802a4 0x040018006884c015 0x2827023f01980ffc 0xf9413811f80cc07f

def z119 : W := mkw 0x00010000f5d40000 0xc000080007aea000 0x10000000fffe000f 0x8080000007fff000

def z120 : W := mkw 0x05c02200ac010800 0xa02e011005600840 0xf7c02200fe010e17 0xcfbe011007f00870

def z121 : W := mkw 0x87f7a20cfdd50824 0xe43fbd1067eea841 0x5fa72018f9810061 0x02fd3900c7cc0803

def z122 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xe7c03fc03e000e04 0x4f3e01fe01f00070

def z123 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xe6383c3801e001e8 0x5731c1e1c00f000f

def z124 : W := mkw 0x0000000041605140 0x08000000020b028a 0x10000000c1e1f1fb 0x80800000060f0f8f

def z125 : W := mkw 0x400850e20222c512 0x0200428710111628 0x8058d1c00666c002 0x0402c68e00333600

def z126 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x00383c3801e1f1f8 0x5001c1e1c00f0f8f

def z127 : W := mkw 0x400950e312bac792 0x02004a871895d63c 0xe9ffd3e73ffecf9f 0xff4ffe9f39fff67c

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0xf6003c00c001f013 0xc7b001e006000f80

def z129 : W := mkw 0x07748940e744a400 0xd03ba44a073a2520 0x9658ddc0c666f002 0x04b2c6ee06333780

def z130 : W := mkw 0x0774800000000000 0x003ba40000000000 0xefffc00000000000 0x3f7ffe0000000000

def z131 : W := mkw 0x477cd0e2e766c512 0xc23be687173b3628 0x9658d1c0c666c002 0x04b2c68e06333600

def z132 : W := mkw 0x8082220d08090aa4 0x2404111068404855 0x0000223f00010ff0 0x40000111f800087f

def z133 : W := mkw 0x077d9430f5f45158 0xc83beca187afa28a 0xfffffc38fffff1ff 0xffffffe1c7ffff8f

def z134 : W := mkw 0x4775c0c3f7de8682 0xc23bae061fbef434 0xffffc3c7fffe0e0f 0xbffffe1e3ffff070

def z135 : W := mkw 0x05400940ae01ac00 0xb02a004a05700d60 0x96401dc0fe01fe17 0x84b200ee07f00ff0

def z136 : W := mkw 0x0540000000000000 0x002a000000000000 0xe7c0000000000000 0x0f3e000000000000

def z137 : W := mkw 0x0000004002008400 0x0000000200100420 0x000013c00000ce10 0x4000009e00000670

def z138 : W := mkw 0x0080220008010800 0x2004011000400840 0x6180220038010e15 0xcb0c011001c00870

def z139 : W := mkw 0x85c32b4dbe99aea4 0xb42e195a6df4cd75 0xffe73fffff99ffff 0xffff39fffffccfff

def z140 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x6987220738190e15 0xeb4c391039c0c870

def z141 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xa1c013c03e00ce16 0xcd0e009e01f00670

def z142 : W := mkw 0x8003000d109802a4 0x040018006884c015 0x0827003f019801e8 0x30413801f80cc00f

def z143 : W := mkw 0x82ba363d49695bfc 0x2c15d1b1ea4b4adf 0xf6383e3fc1e1fffb 0xd7b1c1f1fe0f0fff

def z144 : W := mkw 0x0ff6eb8e00000007 0x007fb75c70000000 0xefffc3c700000000 0x3f7ffe1e38000000

def z145 : W := mkw 0x8082220d08090aa4 0x2404111068404855 0x6020223f01810ff9 0xd3010111f80c087f

def z146 : W := mkw 0x808b322d18b94bb4 0x2404599168c5ca5d 0xe9bf323f39f9cfff 0xff4df991f9cfce7f

def z147 : W := mkw 0x0000004002008400 0x0000000200100420 0xa04013c00600ce16 0xcd02009e00300670

def z148 : W := mkw 0x477dd0e2f7f6c512 0xc23bee8717bfb628 0xffffd1c0fffec00f 0xbffffe8e07fff600

def z149 : W := mkw 0x0f7cddb20000001b 0x007be6ed90000000 0xa658dfe700000000 0x7d32c6ff38000000

def z150 : W := mkw 0x400040c3020a8682 0x0200020618105434 0xa058c3c7067e0e0e 0xbd02c61e3833f070

def z151 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7020739980e0d 0xbb4d381039ccc070

def z152 : W := mkw 0x05400000a4000000 0x802a000005200000 0xf7c00000fe000007 0x8fbe000007f00000

def z153 : W := mkw 0x0dca7fbe0000001f 0x006e53fdf0000000 0xe7c03fff00000000 0x4f3e01fff8000000

def z154 : W := mkw 0x05c02b0000000000 0x002e015800000000 0x47802c0000000000 0x023c016000000000

def z155 : W := mkw 0x0238143000000018 0x0011c0a180000000 0xe6383c3800000000 0x5731c1e1c0000000

def z156 : W := mkw 0x08826b8e00000007 0x0044135c70000000 0x000003c700000000 0x0000001e38000000

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0xa058c000067e000e 0xbd02c6000033f000

def z158 : W := mkw 0x0dc6ebceae01ac07 0xb06e375e75700d60 0xffc7ffc7fe01fe17 0xeffe3ffe3ff00ff0

def z159 : W := mkw 0x0000000100080280 0x0000000008004014 0x0000020700180e04 0x280000103800c070

def z160 : W := mkw 0x000850a200000012 0x0000428510000000 0x0018c02700000000 0x3000c60138000000

def z161 : W := mkw 0x8081220118990aa0 0x2404091008c4c855 0x6180220039990ffd 0xcb0c011001ccc87f

def z162 : W := mkw 0x0aba7fbe0000001f 0x0055d3fdf0000000 0xe6383fff00000000 0x5731c1fff8000000

def z163 : W := mkw 0x0f7eddbe0000001f 0x007bf6edf0000000 0x8e7fddff00000000 0x3473feeff8000000

def z164 : W := mkw 0x8239143159f95bf8 0x2c11c8a18acfcadf 0xf6383c38f9f9ffff 0xd7b1c1e1c7cfcfff

def z165 : W := mkw 0x0080220008010800 0x2004011000400840 0xf7803e00f801fe17 0xcfbc01f007c00ff0

def z166 : W := mkw 0x85c7a20dbc9d0aa4 0xe42e3d106de4e855 0x69e7e23f3f9f0ffd 0xfb4f3f11f9fcf87f

def z167 : W := mkw 0x0ffeffbee544001f 0xc07ff7fdf72a2000 0xffffffffc6660002 0x7ffffffffe333000

def z168 : W := mkw 0x088a7ffe0a01ac1f 0x304453fff0500d60 0x00003fff0001fe10 0x400001fff8000ff0

def z169 : W := mkw 0x0f7cddf2a600a41b 0x907be6ef95300520 0x9658ddc0c600f002 0x04b2c6ee06300780

def z170 : W := mkw 0x454859e2a622e512 0x922a42cf15311728 0x9658ddc0c666f002 0x04b2c6ee06333780

def z171 : W := mkw 0x05400940a600a400 0x902a004a05300520 0xb6401fc0c600fe16 0xcdb200fe063007f0

def z172 : W := mkw 0x05c02b00ac012800 0xb02e015805600940 0x0180000038000000 0x000c000001c00000

def z173 : W := mkw 0x00802b400a01ac00 0x3004015a00500d60 0x00003fc00001fe10 0x400001fe00000ff0

def z174 : W := mkw 0x0230041041401048 0x08118020820a0082 0xf6203c18c181f073 0xc7b101e0c60c0f83

def z175 : W := mkw 0x87f7a20cfdd50824 0xe43fbd1067eea841 0xffffe018ffff006f 0xbfffff00c7fff803

def z176 : W := mkw 0x0ffeffbe0020515f 0x087ff7fdf001028a 0xefffffff0001f1f0 0x7f7ffffff8000f8f

def z177 : W := mkw 0x0008102000204110 0x0000408100010208 0xa01810200060c19a 0xd500c0810003060c

def z178 : W := mkw 0x45c87be3ae2bef92 0xb22e43df1d715f7c 0xf7d8ffe7fe7fff9f 0xffbec7ff3ff3fffc

def z179 : W := mkw 0x0235800051d40000 0x4011ac00028ea000 0x69bfc00039fe000d 0xbb4dfe0001cff000

def z180 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7d8ffc0fe7ffe1f 0xffbec7fe07f3fff0

def z181 : W := mkw 0x423854f3436ad7da 0x0a11c2a79a1b56be 0xf6383fffc1e1fffb 0xd7b1c1fffe0f0fff

def z182 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d3e70666cf92 0x4402c69f3833367c

def z183 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x09ffc0003ffe000c 0x384ffe0001fff000

def z184 : W := mkw 0x0000000000000000 0x0000000000000000 0x6020203800000000 0x53010101c0000000

def z185 : W := mkw 0x0dc6ab0c00000005 0x006e355860000000 0x0987000000000000 0x004c380000000000

def z186 : W := mkw 0xc08362cf1a9b8ea6 0x26041b1678d4dc75 0x09c7c3c73e1e0e04 0x284e3e1e39f0f070

def z187 : W := mkw 0x0000041000001048 0x0800002080000082 0x00002c1800013060 0x00000160c0000983

def z188 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffbf0000f9e0000b 0x97fdf80007cf0000

def z189 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7e03ff8ff81ffff 0xdfbf01ffc7fc0fff

def z190 : W := mkw 0x40000041022ac780 0x020000020811563c 0xa058c000067ecf9e 0xbd02c6000033f67c

def z191 : W := mkw 0x05c02b0008010800 0x202e015800400840 0xe7c03fc038010e15 0xcf3e01fe01c00870

def z192 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x9fdfc000fe7e0006 0x2cfefe0007f3f000

def z193 : W := mkw 0x0230041041401048 0x08118020820a0082 0xf6382c18c1e1306b 0x97b1c160c60f0983

def z194 : W := mkw 0x87fb3f7dfff9fffc 0xbc3fd9fbefffcfff 0xffff3ffffff9ffff 0xfffff9ffffffcfff

def z195 : W := mkw 0x0ffeffbea400001f 0x807ff7fdf5200000 0xfffffffffe000007 0xfffffffffff00000

def z196 : W := mkw 0x40000001002a4380 0x020000000801521c 0x00000000007e0188 0x000000000003f00c

def z197 : W := mkw 0x0a3ed4be0000001f 0x0051f6a5f0000000 0xa87fd3ff00000000 0x7d43fe9ff8000000

def z198 : W := mkw 0x07758940f7d4a400 0xd03bac4a07bea520 0xffffddc0fffef00f 0xbffffeee07fff780

def z199 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x000013e7067ecf9e 0xc000009f3833f67c

def z200 : W := mkw 0x0230000041400000 0x00118000020a0000 0x96180000c0600002 0x04b0c00006030000

def z201 : W := mkw 0x077c943000000018 0x003be4a180000000 0xeffffc3800000000 0x7f7fffe1c0000000

def z202 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff018101f9 0xff7ffffff80c080f

def z203 : W := mkw 0x823b143d51f853fc 0x0c11d8a1ea8fc29f 0x083f003f01f801e8 0x3041f801f80fc00f

def z204 : W := mkw 0x0008102000204110 0x0000408100010208 0xe038303801e1c1fb 0xd701c181c00f0e0f

def z205 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x0987020738180e04 0x284c381039c0c070

def z206 : W := mkw 0x0a3ed4be4160515f 0x0851f6a5f20b028a 0x083fc03f01e001e8 0x3041fe01f80f000f

def z207 : W := mkw 0x05400900a4002000 0x902a004805200100 0x16000c00c0003000 0x00b0006006000180

def z208 : W := mkw 0x07781d70e760f558 0x983bc0eb873b07aa 0xf6783df8c7e1f1fb 0xd7b3c1efc63f0f8f

def z209 : W := mkw 0x05c22b4cae01ac04 0xb02e115a65700d60 0xffe73ffffe01fe17 0xffff39fffff00ff0

def z210 : W := mkw 0x85c12b41be99aea0 0xb42e095a0df4cd75 0xf7c03fc0ff99ffff 0xcfbe01fe07fccfff

def z211 : W := mkw 0x8083220c18910824 0x2404191060c48841 0x69a72038398101f9 0xd34d3901c1cc080f

def z212 : W := mkw 0x07f83f70ef61fd58 0xb83fc1fb877b0fea 0xf7f83ff8ffe1ffff 0xdfbfc1ffc7ff0fff

def z213 : W := mkw 0x0234800041440000 0x4011a400020a2000 0x0018c00000660000 0x0000c60000033000

def z214 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x0987223f38190ff4 0x684c3911f9c0c87f

def z215 : W := mkw 0x0000000000000000 0x0000000000000000 0xf6203c38c181f1fb 0xd7b101e1c60c0f8f

def z216 : W := mkw 0x8fffffbf59f95bff 0x2c7ffffdfacfcadf 0xfffffffff9f9ffff 0xffffffffffcfcfff

def z217 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x5fbfc000f9fe0009 0x32fdfe0007cff000

def z218 : W := mkw 0x85c22b4dae09aea4 0xb42e115a6d704d75 0xf7c03ffffe01fff7 0xcfbe01fffff00fff

def z219 : W := mkw 0x0ffefffe0200841f 0x007ff7fff0100420 0xefffffff0600ce16 0xff7ffffff8300670

def z220 : W := mkw 0x0dca7ffeae01ac1f 0xb06e53fff5700d60 0xf7c03ffffe01fe17 0xcfbe01fffff00ff0

def z221 : W := mkw 0x05458000f5d40000 0xc02a2c0007aea000 0x19c7c000fffe000f 0xa8ce3e0007fff000

def z222 : W := mkw 0x0238143000000018 0x0011c0a180000000 0xf6383c38c001f013 0xd7b1c1e1c6000f80

def z223 : W := mkw 0x088a7fbe0000001f 0x004453fdf0000000 0x69a73fff00000000 0x7b4d39fff8000000

def z224 : W := mkw 0x0ff7eb8ef5d40007 0xc07fbf5c77aea000 0xffffc3c7fffe000f 0xbffffe1e3ffff000

def z225 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa04013e70600cf96 0xcd02009f3830067c

def z226 : W := mkw 0x000850a200204112 0x0000428510010208 0xa058d3e70060c19a 0xfd02c69f3803060c

def z227 : W := mkw 0x0000408200000002 0x0000020410000000 0x0040c3c700000000 0x2802061e38000000

def z228 : W := mkw 0x400850a3002a4392 0x020042851801521c 0xa058d3e7007e0188 0x7d02c69f3803f00c

def z229 : W := mkw 0x477dd0a3f5fe4392 0xc23bee851faff21c 0xffffc027fffe018f 0xbffffe013ffff00c

def z230 : W := mkw 0x0ffcffb20000001b 0x007fe7fd90000000 0xe7d8ffc000000000 0x4f3ec7fe00000000

def z231 : W := mkw 0x4ffffffff7fec79f 0xc27fffffffbff63c 0xfffffffffffecf9f 0xfffffffffffff67c

def z232 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xffffffffc001f013 0xfffffffffe000f80

def z233 : W := mkw 0xc08b72ef1abbcfb6 0x26045b9778d5de7d 0xe9fff3ff3fffcfff 0xff4fff9ff9fffe7f

def z234 : W := mkw 0x0000000041401040 0x08000000020a0082 0x10000000c1813061 0x00800000060c0983

def z235 : W := mkw 0x423854f3436ad7da 0x0a11c2a79a1b56be 0xb658dfe7c67eff9e 0xfdb2c6ff3e33f7fc

def z236 : W := mkw 0x0081220018910800 0x2004091000c48840 0x69a7220039990e1d 0xfb4d391001ccc870

def z237 : W := mkw 0x87f7a20dfddd0aa4 0xe43fbd106feee855 0x7fa7223ff9990ffd 0xfbfd3911ffccc87f

def z238 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x96403fc0c601fe12 0x44b201fe06300ff0

def z239 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0xefc7ffc700000000 0x6f7e3ffe38000000

def z240 : W := mkw 0x0230000000000000 0x0011800000000000 0xe638000000000000 0x1731c00000000000

def z241 : W := mkw 0x02310000f5d40000 0xc011880007aea000 0xf6380000fffe000f 0x97b1c00007fff000

def z242 : W := mkw 0x0ff7af1cf5d4000d 0xc07fbd78e7aea000 0xffffec18fffe000f 0xbfffff60c7fff000

def z243 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xcffffdd800000000 0x067fffeec0000000

def z244 : W := mkw 0xc08362cf1a9b8ea6 0x26041b1678d4dc75 0x69e7e3ff3f9f0ffd 0xfb4f3f1ff9fcf87f

def z245 : W := mkw 0x05410000f5d40000 0xc02a080007aea000 0xf7c00000fffe000f 0x8fbe000007fff000

def z246 : W := mkw 0x400850a200224112 0x0200428510011208 0x0018c00000660000 0x0000c60000033000

def z247 : W := mkw 0x088a7fbe0000001f 0x004453fdf0000000 0xa058ffff00000000 0x7d02c7fff8000000

def z248 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x01c03fc03e01fe14 0x480e01fe01f00ff0

def z249 : W := mkw 0x00010000f5f45140 0xc800080007afa28a 0x10000000fffff1ff 0x8080000007ffff8f

def z250 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7221f39990e65 0x2a4d3910f9ccc873

def z251 : W := mkw 0x0008102100284390 0x000040810801421c 0xa01812270078cf9e 0xfd00c0913803c67c

def z252 : W := mkw 0x823b143d51f853fc 0x0c11d8a1ea8fc29f 0xfe3f3c3fc1f9f1fb 0xf7f1f9e1fe0fcf8f

def z253 : W := mkw 0x87f7a20d18990aa4 0x243fbd1068c4c855 0xefffe23f39990ffd 0xff7fff11f9ccc87f

def z254 : W := mkw 0x077cd0a200000012 0x003be68510000000 0xefffd3e700000000 0x7f7ffe9f38000000

def z255 : W := mkw 0x0008143000205158 0x080040a18001028a 0xf6003c38c001f1f3 0xc7b001e1c6000f8f

def z256 : W := mkw 0x423dd0a351fe4392 0x4211ee851a8ff21c 0x083fc02701fe0188 0x3041fe01380ff00c

def z257 : W := mkw 0x47758041f7fec780 0xc23bac020fbff63c 0xffffc000fffecf9f 0xbffffe0007fff67c

def z258 : W := mkw 0x0dcefbae00000017 0x006e77dd70000000 0xa9dfd3e700000000 0x7d4efe9f38000000

def z259 : W := mkw 0x0ff6af1cac01280d 0xb07fb578e5600940 0x5fa72c18f8013001 0x02fd3960c7c00980

def z260 : W := mkw 0x05400000a4000000 0x802a000005200000 0xf7d8c000fe7e000f 0xbfbec60007f3f000

def z261 : W := mkw 0x0f7dddb2f5d4001b 0xc07beeed97aea000 0xffffddc0fffe000f 0xbffffeee07fff000

def z262 : W := mkw 0x45c06bc3ae0bae82 0xb22e035e1d705d74 0xf7c0ffc7fe1ffe17 0xefbe07fe3ff0fff0

def z263 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x0018c027067ecf9e 0xb000c6013833f67c

def z264 : W := mkw 0x02358000f5d40000 0xc011ac0007aea000 0x183fc000fffe000f 0xb0c1fe0007fff000

def z265 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff067e000e 0xff7ffffff833f000

def z266 : W := mkw 0x40004083000a0282 0x0200020418005014 0x0000c007001e0000 0x200006003800f000

def z267 : W := mkw 0x0000000100080280 0x0000000008004014 0x2000022700180f9c 0xf90000113800c07c

def z268 : W := mkw 0x00010000f5d40000 0xc000080007aea000 0x79a70000fffe000f 0xbbcd380007fff000

def z269 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x0018d3e7007ecf98 0x7000c69f3803f67c

def z270 : W := mkw 0x45c06bc3ae0bae82 0xb22e035e1d705d74 0x01c0c3c73e1e0e04 0x280e061e39f0f070

def z271 : W := mkw 0x05c02b00a4000000 0x802e015805200000 0xf7c03fc0fe000007 0xcfbe01fe07f00000

def z272 : W := mkw 0x477cd0e3022ac792 0x023be6871811563c 0xefffd3e7067ecf9e 0xff7ffe9f3833f67c

def z273 : W := mkw 0x8001000118990aa0 0x2400080008c4c855 0x69a7000039990ffd 0xbb4d380001ccc87f

def z274 : W := mkw 0x0008143000205158 0x080040a18001028a 0xa0183c380061f1fa 0xd500c1e1c0030f8f

def z275 : W := mkw 0x00010000f5d40000 0xc000080007aea000 0xb058c000fffe000f 0xbd82c60007fff000

def z276 : W := mkw 0x05c02b00ac012800 0xb02e015805600940 0x57802c00f8013001 0x02bc016007c00980

def z277 : W := mkw 0x0008102000000010 0x0000408100000000 0xa018102000000000 0x5500c08100000000

def z278 : W := mkw 0x05410000b4900000 0x802a080005a48000 0xffe70000ff98000f 0xbfff380007fcc000

def z279 : W := mkw 0x4ffeffff022ac79f 0x027ff7fff811563c 0xefffffff0000cf90 0x7f7ffffff800067c

def z280 : W := mkw 0x0001000010900000 0x0000080000848000 0x69a72038399901fd 0xfb4d3901c1ccc80f

def z281 : W := mkw 0x40000041436ad7c0 0x0a0000020a1b56be 0x10000000c7ffffff 0x80800000063fffff

def z282 : W := mkw 0x07f5ab40ffd5ac00 0xf03fad5a07fead60 0xffe73fc0ff81fe17 0xcfff39fe07fc0ff0

def z283 : W := mkw 0x82bb363c59f1597c 0x2c15d9b1e2cf8acb 0xffbf3c38f9e1f1fb 0xd7fdf9e1c7cf0f8f

def z284 : W := mkw 0x00000040ae01ac00 0xb000000205700d60 0x000000003e000e04 0x0000000001f00070

def z285 : W := mkw 0x0008102000204110 0x0000408100010208 0x801810000060c002 0x0400c08000030600

def z286 : W := mkw 0x8ff7af1c1891082d 0x247fbd78e0c48841 0x4fa72c1839810061 0x027d3960c1cc0803

def z287 : W := mkw 0x0ffcfff2ae01ac1b 0xb07fe7ff95700d60 0xf7d8ffc0fe01fe17 0xcfbec7fe07f00ff0

def z288 : W := mkw 0x0775800051d40000 0x403bac00028ea000 0xefffc00001fe0008 0x3f7ffe00000ff000

def z289 : W := mkw 0x008a72ae00000016 0x0004539570000000 0xe9fff3ff00000000 0x7f4fff9ff8000000

def z290 : W := mkw 0x0775800010900000 0x003bac0000848000 0xefffc0003998000d 0xbf7ffe0001ccc000

def z291 : W := mkw 0x0239143051f05158 0x0811c8a1828f828a 0xffbf3c38f9f9f1ff 0xfffdf9e1c7cfcf8f

def z292 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa01813e70060cf9a 0xd500c09f3803067c

def z293 : W := mkw 0x4ffeffff436ad7df 0x0a7ff7fffa1b56be 0xffffffffc7ffffff 0xfffffffffe3fffff

def z294 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xf658ffe7c67fff9f 0xffb2c7ff3e33fffc

def z295 : W := mkw 0x0000004002008400 0x0000000200100420 0x004003c006000e04 0x0802001e00300070

def z296 : W := mkw 0x82b3220d59d90aa4 0x241599106acec855 0xffbf223ff9f90fff 0xfffdf911ffcfc87f

def z297 : W := mkw 0x0000000000000000 0x0000000000000000 0x00002038000101f0 0x40000101c000080f

def z298 : W := mkw 0x0774800000000000 0x003ba40000000000 0x4fa7000000000000 0x027d380000000000

def z299 : W := mkw 0x0082220c00000004 0x0004111060000000 0x49a7201800000000 0x024d3900c0000000

def z300 : W := mkw 0x8083220d59f95be4 0x2c0419106acfcadf 0x79a7223ff9f9ffff 0xfbcd3911ffcfcfff

def z301 : W := mkw 0x0230000041400000 0x00118000020a0000 0xf6382038c1e101fb 0xd7b1c101c60f080f

def z302 : W := mkw 0x0ff6af1c4140104d 0x087fb578e20a0082 0x5fa72c18c1813061 0x02fd3960c60c0983

def z303 : W := mkw 0x0230041041605148 0x08118020820b028a 0x56202c18c1e1f1fb 0x82b10160c60f0f8f

def z304 : W := mkw 0x0008102041605150 0x08004081020b028a 0xb0181020c1e1f1fb 0xd580c081060f0f8f

def z305 : W := mkw 0x8001000118990aa0 0x2400080008c4c855 0x2000022739990ffd 0xf900001139ccc87f

def z306 : W := mkw 0x423854f24362d55a 0x0a11c2a7921b16aa 0xf678fdf8c7e7f1fb 0xd7b3c7efc63f3f8f

def z307 : W := mkw 0x0ffeffbe0801081f 0x207ff7fdf0400840 0xefffffff38010e15 0xff7ffffff9c00870

def z308 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x0058c3e7067e0f8c 0x3802c61f3833f07c

def z309 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x09a7023f39980fec 0x384d3811f9ccc07f

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000002000000198 0xd10000010000000c

def z311 : W := mkw 0xc00950e31abbcfb2 0x26004a8718d5de7d 0xa058d3e73fffcfff 0xfd02c69f39fffe7f

def z312 : W := mkw 0x400040c3022ac782 0x020002061811563c 0x0040c3c7067ecf9e 0xa802061e3833f67c

def z313 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xefffffff01e001e8 0x7f7ffffff80f000f

def z314 : W := mkw 0x0000000000204100 0x0000000000010208 0x000000000060c19a 0x800000000003060c

def z315 : W := mkw 0x05c5ab40be95ac00 0xf02e2d5a05f4ad60 0x09c7c3c03e1e0e04 0x284e3e1e01f0f070

def z316 : W := mkw 0x00000040ae01ac00 0xb000000205700d60 0xb04013c0fe01fe17 0xcd82009e07f00ff0

def z317 : W := mkw 0x00010000f5d40000 0xc000080007aea000 0x10000000f9800001 0x0080000007cc0000

def z318 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x4fa73fff00000000 0x427d39fff8000000

def z319 : W := mkw 0x0238143000000018 0x0011c0a180000000 0xe6383c38018101f9 0xd731c1e1c00c080f

def z320 : W := mkw 0x07748000e5440000 0xc03ba400072a2000 0xffffc000c6660002 0x3ffffe0006333000

def z321 : W := mkw 0x0000004002008400 0x0000000200100420 0x804011c00600c002 0x0402008e00300600

def z322 : W := mkw 0x05400040a6008400 0x802a000205300420 0xf7c013c0fe00ce17 0xcfbe009e07f00670

def z323 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xfffffc00fffff01f 0xffffffe007ffff80

def z324 : W := mkw 0x0ffeffbe4140105f 0x087ff7fdf20a0082 0xffffffffc1813061 0x7ffffffffe0c0983

def z325 : W := mkw 0x87758001fddd0aa0 0xe43bac000feee855 0xffffc000ffff0fff 0xbffffe0007fff87f

def z326 : W := mkw 0x0000000000000000 0x0000000000000000 0xa04013c000000000 0x4d02009e00000000

def z327 : W := mkw 0x8082220d08090aa4 0x2404111068404855 0x0000020700000e00 0x0000001038000070

def z328 : W := mkw 0x4dcefbef022ac797 0x026e77df7811563c 0xa9dfd3e7067ecf9e 0xfd4efe9f3833f67c

def z329 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d3c7067ece06 0x2c02c69e3833f670

def z330 : W := mkw 0x85c32b4dbe99aea4 0xb42e195a6df4cd75 0x09c703c73e180e04 0x284e381e39f0c070

def z331 : W := mkw 0x4f7cddf3022ac79b 0x027be6ef9811563c 0xa658dfe7067ecf9e 0xfd32c6ff3833f67c

def z332 : W := mkw 0x00802b400a01ac00 0x3004015a00500d60 0xa0403fc00601fe16 0xcd0201fe00300ff0

def z333 : W := mkw 0xc08b72ef1abbcfb6 0x26045b9778d5de7d 0x69a733ff3999cffd 0xfb4d399ff9ccce7f

def z334 : W := mkw 0x0774800000000000 0x003ba40000000000 0x8658c00000000000 0x0432c60000000000

def z335 : W := mkw 0x0ff7af1cf5d4000d 0xc07fbd78e7aea000 0x5fa72c18f9800001 0x02fd3960c7cc0000

def z336 : W := mkw 0x87f7a20dfddd0aa4 0xe43fbd106feee855 0xffffc207fffe0e0f 0xbffffe103ffff070

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018c000007e0008 0x3000c6000003f000

def z338 : W := mkw 0x02381431416853d8 0x0811c0a18a0b429e 0xf6383e3fc1f9ffff 0xffb1c1f1fe0fcfff

def z339 : W := mkw 0x0082220c00000004 0x0004111060000000 0x69a7223f018101f9 0xfb4d3911f80c080f

def z340 : W := mkw 0x0008102000204110 0x0000408100010208 0xf6183c20c061f19b 0xd7b0c1e106030f8c

def z341 : W := mkw 0x8fffffbf18990abf 0x247ffffdf8c4c855 0xefffffff38180e04 0x7f7ffffff9c0c070

def z342 : W := mkw 0x05400000a4000000 0x802a000005200000 0x57800000f8000001 0x02bc000007c00000

def z343 : W := mkw 0x408a72ef022ac796 0x020453977811563c 0xe9fff3ff067ecf9e 0xff4fff9ff833f67c

def z344 : W := mkw 0x0230000041400000 0x00118000020a0000 0x56200000c1800001 0x02b10000060c0000

def z345 : W := mkw 0x0008143000000018 0x000040a180000000 0x00003c3800000000 0x400001e1c0000000

def z346 : W := mkw 0x0001000010900000 0x0000080000848000 0x0987000038180004 0x284c380001c0c000

def z347 : W := mkw 0x07f02f50ef41bc48 0xb83f817a877a0de2 0xf7e03fd8ff81fe77 0xcfbf01fec7fc0ff3

def z348 : W := mkw 0x400850e3ae2bef92 0xb20042871d715f7c 0xb058d3e7fe7fff9f 0xfd82c69f3ff3fffc

def z349 : W := mkw 0x0238143041400018 0x0011c0a1820a0000 0xf6383c38c1e0000b 0xd7b1c1e1c60f0000

def z350 : W := mkw 0x0231000051d00000 0x00118800028e8000 0xffbf0000f9f8000f 0xbffdf80007cfc000

def z351 : W := mkw 0x0a3cd4b20000001b 0x0051e6a590000000 0x0018c00000000000 0x0000c60000000000

def z352 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6183c00c061f013 0xc7b0c1e006030f80

def z353 : W := mkw 0x02391430f5f45158 0xc811c8a187afa28a 0xf6383c38fffff1ff 0xd7b1c1e1c7ffff8f

def z354 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xdfffc000ffe60003 0x06fffe0007ff3000

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0x6180000038000005 0x8b0c000001c00000

def z356 : W := mkw 0x0000000008010800 0x2000000000400840 0x0000000038010e15 0x8000000001c00870

def z357 : W := mkw 0x0ffeffbeac01281f 0xb07ff7fdf5600940 0xfffffffff8013001 0x7fffffffffc00980

def z358 : W := mkw 0x400850e20222c512 0x0200428710111628 0xa058d3c00666ce16 0xcd02c69e00333670

def z359 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c003c0fe000e07 0x8fbe001e07f00070

def z360 : W := mkw 0x0806c08e00000007 0x0040360470000000 0x0807c00700000000 0x20403e0038000000

def z361 : W := mkw 0x0080220008010800 0x2004011000400840 0x61a0223839810ffd 0xdb0d0111c1cc087f

def z362 : W := mkw 0x45c87be2ae23ed12 0xb22e43df15711f68 0xf7d8ffc0fe67fe17 0xcfbec7fe07f33ff0

def z363 : W := mkw 0x8ff7af1d18990aad 0x247fbd78e8c4c855 0x6fa72e3f39990ffd 0xfb7d3971f9ccc87f

def z364 : W := mkw 0x05c02b00ac012800 0xb02e015805600940 0x77802e00f8013e15 0xcbbc017007c009f0

def z365 : W := mkw 0x05400000a4000000 0x802a000005200000 0xf7c03c00fe01f017 0xcfbe01e007f00f80

def z366 : W := mkw 0x05c83b60ae21ed10 0xb02e41db05710f68 0xf7d83fe0fe61ff9f 0xdfbec1ff07f30ffc

def z367 : W := mkw 0x85c32b4dbe99aea4 0xb42e195a6df4cd75 0xffc73fc7fe19fe17 0xeffe39fe3ff0cff0

def z368 : W := mkw 0x0f748d1000000009 0x007ba46880000000 0x06000c0000000000 0x0030006000000000

def z369 : W := mkw 0x40081061022ac790 0x020040830811563c 0xa0181020067ecf9e 0xd500c0810033f67c

def z370 : W := mkw 0x07748000e5440000 0xc03ba400072a2000 0xf678c000c7e6000b 0x97b3c600063f3000

def z371 : W := mkw 0x8002000d000802a4 0x0400100068004015 0x0000003f000001e0 0x00000001f800000f

def z372 : W := mkw 0x400040c3020a8682 0x0200020618105434 0xa040d3c7061ece16 0xed02069e3830f670

def z373 : W := mkw 0x85c32b4dbe99aea4 0xb42e195a6df4cd75 0x69e723ff3f990ffd 0xfb4f391ff9fcc87f

def z374 : W := mkw 0x477dd4f3f7fed7da 0xca3beea79fbff6be 0xffffffffffffffff 0xffffffffffffffff

def z375 : W := mkw 0x0083220c10900004 0x0004191060848000 0x69a7223f3998000d 0xfb4d3911f9ccc000

def z376 : W := mkw 0x40010041f7fec780 0xc20008020fbff63c 0x10000000fffecf9f 0x8080000007fff67c

def z377 : W := mkw 0x0008143041605158 0x080040a1820b028a 0x10003c38c1e1f1fb 0xc08001e1c60f0f8f

def z378 : W := mkw 0x07f6a20c00000004 0x003fb51060000000 0xefffe23f00000000 0x7f7fff11f8000000

def z379 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0x0987000038000000 0x004c380001c00000

def z380 : W := mkw 0x8082220d08090aa4 0x2404111068404855 0x69a7223f00010ff0 0x7b4d3911f800087f

def z381 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000022700000000 0x7900001138000000

def z382 : W := mkw 0x8001000159f95be0 0x2c0008000acfcadf 0x10000000f9f9ffff 0x8080000007cfcfff

def z383 : W := mkw 0x8003000d109802a4 0x040018006884c015 0x69a7003f399801ed 0xbb4d3801f9ccc00f

def z384 : W := mkw 0x0001000051d40000 0x40000800028ea000 0x0000000001fe0008 0x00000000000ff000

def z385 : W := mkw 0x8003000c10900024 0x0400180060848001 0x0827001801800060 0x00413800c00c0003

def z386 : W := mkw 0x80010001fddd0aa0 0xe40008000feee855 0x10000000ffff0fff 0x8080000007fff87f

def z387 : W := mkw 0x400854f3022ad7da 0x0a0042a7981156be 0xa058ffff067ffffe 0xfd02c7fff833ffff

def z388 : W := mkw 0x4a3ed4bf002a439f 0x0251f6a5f801521c 0x083fc03f007e0188 0x3041fe01f803f00c

def z389 : W := mkw 0x0ffffffeffd5ac1f 0xf07ffffff7fead60 0xfffffffffffffe1f 0xfffffffffffffff0

def z390 : W := mkw 0x00802b0008012800 0x3004015800400940 0x00002c0000013000 0x0000016000000980

def z391 : W := mkw 0x0238143000000018 0x0011c0a180000000 0x86181c0000000000 0x0430c0e000000000

def z392 : W := mkw 0x00802b400a01ac00 0x3004015a00500d60 0x61803fc03801fe15 0xcb0c01fe01c00ff0

def z393 : W := mkw 0x0000000041605140 0x08000000020b028a 0x70202038c1e1f1fb 0xd3810101c60f0f8f

def z394 : W := mkw 0x8001000118990aa0 0x2400080008c4c855 0x0000000038180e04 0x0000000001c0c070

def z395 : W := mkw 0x82bb363d18990abc 0x2415d9b1e8c4c855 0xefbf3e3f39990ffd 0xff7df9f1f9ccc87f

def z396 : W := mkw 0x07758410f5d41048 0xc83bac2087aea082 0xffffec18ffff306f 0xbfffff60c7fff983

def z397 : W := mkw 0x0082220c00000004 0x0004111060000000 0x0000223f00000000 0x40000111f8000000

def z398 : W := mkw 0x0ffefffeae01ac1f 0xb07ff7fff5700d60 0xefffffff3e000e04 0x7f7ffffff9f00070

def z399 : W := mkw 0x07748000e5440000 0xc03ba400072a2000 0xf7d8c000fe660007 0x8fbec60007f33000

def z400 : W := mkw 0x488a7fff022ac79f 0x024453fff811563c 0xa058ffff067ecf9e 0xfd02c7fff833f67c

def z401 : W := mkw 0x45c02b41ae2bef80 0xb22e015a0d715f7c 0xf7c03fc0fe7fff9f 0xcfbe01fe07f3fffc

def z402 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x8fdfdfc700000000 0x2c7efefe38000000

def z403 : W := mkw 0x07f83f3041605158 0x083fc1f9820b028a 0xf7f83ff8c1e1f1fb 0xdfbfc1ffc60f0f8f

def z404 : W := mkw 0x05c02b400a01ac00 0x302e015a00500d60 0xe7c03fc00001fe10 0x4f3e01fe00000ff0

def z405 : W := mkw 0x05400940a600a400 0x902a004a05300520 0xf6403dc0c601f013 0xc7b201ee06300f80

def z406 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7223f39810ff1 0x424d3911f9cc087f

def z407 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x8658ffff00000000 0x4432c7fff8000000

def z408 : W := mkw 0x0008143000205158 0x080040a18001028a 0x60203c380181f1f9 0xd30101e1c00c0f8f

def z409 : W := mkw 0xc08a72ef0a2bcfb6 0x2604539778515e7d 0xa058f3ff067fcffe 0xfd02c79ff833fe7f

def z410 : W := mkw 0x8dc7eb8f18990aa7 0x246e3f5c78c4c855 0x09c7c3c738180e04 0x284e3e1e39c0c070

def z411 : W := mkw 0x07758000b4940000 0xc03bac0005a4a000 0xefffc0003e1e0004 0x3f7ffe0001f0f000

def z412 : W := mkw 0x05c83f70ae21fd58 0xb82e41fb85710fea 0xf7c03ff8fe01fff7 0xcfbe01ffc7f00fff

def z413 : W := mkw 0x0d44c98200000003 0x006a264c10000000 0x0040c1c000000000 0x0002060e00000000

def z414 : W := mkw 0x077d9430f5f45158 0xc83beca187afa28a 0xffffdc00fffef00f 0xbffffee007fff780

def z415 : W := mkw 0x0abef6be0000001f 0x0055f7b5f0000000 0x69bfe23f00000000 0x7b4dff11f8000000

def z416 : W := mkw 0x07758001f5dc0280 0xc03bac000faee014 0xffffc227fffe0f9f 0xfffffe113ffff07c

def z417 : W := mkw 0x45c87be3ae2bef92 0xb22e43df1d715f7c 0xa1d8d3e73e7ecf9e 0xfd0ec69f39f3f67c

def z418 : W := mkw 0xc7fff2efffffcfb6 0xe63fff977ffffe7d 0xfffff3ffffffcfff 0xffffff9ffffffe7f

def z419 : W := mkw 0x008022400a018c00 0x2004011200500c60 0xe1c033c03e01ce17 0xcf0e019e01f00e70

def z420 : W := mkw 0x00000000a4000000 0x8000000005200000 0x10000000fe000007 0x8080000007f00000

def z421 : W := mkw 0x0fffffbef5d4001f 0xc07ffffdf7aea000 0xfffffffff9800001 0x7fffffffffcc0000

def z422 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x96181c00c1e1f1fb 0x84b0c0e0060f0f8f

def z423 : W := mkw 0x8000000108090aa0 0x2400000008404855 0x0000000000010ff0 0x000000000000087f

def z424 : W := mkw 0x400850a3002a4392 0x020042851801521c 0x2018c227007e0f9c 0xf900c6113803f07c

def z425 : W := mkw 0x0000000000000000 0x0000000000000000 0x00200038018001e8 0x10010001c00c000f

def z426 : W := mkw 0x488a7fff022ac79f 0x024453fff811563c 0x00003fff0000cf90 0x400001fff800067c

def z427 : W := mkw 0xc00100411abbcfa0 0x2600080208d5de7d 0x000000003fffcfff 0x8000000001fffe7f

def z428 : W := mkw 0x0080220008010800 0x2004011000400840 0x0180020038000e04 0x080c001001c00070

def z429 : W := mkw 0x0000000000205140 0x080000000001028a 0x000000000001f1f0 0x0000000000000f8f

def z430 : W := mkw 0x423dd0e353fec792 0x4211ee871a9ff63c 0xa87fd3e707fecf9e 0xfd43fe9f383ff67c

def z431 : W := mkw 0x0082220d00080284 0x0004111068004014 0x69a7223f00180f9c 0xfb4d3911f800c07c

def z432 : W := mkw 0x0ff6af1c0000000d 0x007fb578e0000000 0x6fa72e3f00000000 0x7b7d3971f8000000

def z433 : W := mkw 0x0230000041605140 0x08118000020b028a 0xf6380000c1e1f1fb 0x97b1c000060f0f8f

def z434 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x57c02fc0fe013e05 0x0abe017e07f009f0

def z435 : W := mkw 0x4ffeffff020a869f 0x027ff7fff8105434 0xefffffff061e0e04 0x7f7ffffff830f070

def z436 : W := mkw 0x0230041041401048 0x08118020820a0082 0x0020001801800060 0x00010000c00c0003

def z437 : W := mkw 0x00802b400a01ac00 0x3004015a00500d60 0x000003c000000e00 0x0000001e00000070

def z438 : W := mkw 0x82b3261c59d1186c 0x2c159930e2ce88c3 0x5fa72c18f9813061 0x02fd3960c7cc0983

def z439 : W := mkw 0x0234800000000000 0x0011a40000000000 0x083fc00000000000 0x3041fe0000000000

def z440 : W := mkw 0x08822f1c0000000d 0x00441178e0000000 0x00002c1800000000 0x00000160c0000000

def z441 : W := mkw 0x42381471436ad7d8 0x0a11c0a38a1b56be 0xf6383c38c7ffffff 0xd7b1c1e1c63fffff

def z442 : W := mkw 0x0dceffbe0000001f 0x006e77fdf0000000 0x09c7ffff00000000 0x684e3ffff8000000

def z443 : W := mkw 0x05c02b0000000000 0x002e015800000000 0xf7c03fc0c001f013 0xcfbe01fe06000f80

def z444 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xe9ffe23f3fff0fff 0xff4fff11f9fff87f

def z445 : W := mkw 0x40000041020a8680 0x0200000208105434 0x00000000061e0e04 0x000000000030f070

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x69a7000000000000 0x3b4d380000000000

def z447 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x11c003c0fe01fe17 0x888e001e07f00ff0

def z448 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xe078f3ff07ffcfff 0xff03c79ff83ffe7f

def z449 : W := mkw 0x0000004102088680 0x0000000208104434 0xa04013e70618cf9e 0xfd02009f3830c67c

def z450 : W := mkw 0x08085db20000001b 0x004042ed90000000 0x00001dc000000000 0x000000ee00000000

def z451 : W := mkw 0x0005800010940000 0x40002c000084a000 0x0807c000001e0000 0x20403e000000f000

def z452 : W := mkw 0x077d9430f5d40018 0xc03beca187aea000 0xfffffc38fffe000f 0xffffffe1c7fff000

def z453 : W := mkw 0x454850e3a62ac792 0x822a42871d31563c 0xf7d8d3e7fe7ecf9f 0xffbec69f3ff3f67c

def z454 : W := mkw 0x47fdfbe3ffffef92 0xf23fefdf1fffff7c 0xffffffe7ffffff9f 0xffffffff3ffffffc

def z455 : W := mkw 0x0235800051d40000 0x4011ac00028ea000 0xfe3fc000c1fe000b 0xb7f1fe00060ff000

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040c000061e0004 0x280206000030f000

def z457 : W := mkw 0x000009400200a400 0x1000004a00100520 0x00001dc00000f000 0x000000ee00000780

def z458 : W := mkw 0x0000000041605140 0x08000000020b028a 0x10000000c060f002 0x0080000006030780

def z459 : W := mkw 0x0230000041400000 0x00118000020a0000 0xf678c000c7fe000f 0xbfb3c600063ff000

def z460 : W := mkw 0x423854f24362d55a 0x0a11c2a7921b16aa 0x9658ddc0c666f002 0x04b2c6ee06333780

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x200000000018000c 0xb90000000000c000

def z462 : W := mkw 0x023854b20000001a 0x0011c2a590000000 0xe678ffff00000000 0x7f33c7fff8000000

def z463 : W := mkw 0x8a3fd4bf109802bf 0x0451fea5f884c015 0x083fc03f019801e8 0x3041fe01f80cc00f

def z464 : W := mkw 0x00802b0000000000 0x0004015800000000 0x00003fc000000000 0x400001fe00000000

def z465 : W := mkw 0x000850a200000012 0x0000428510000000 0xa058d3e7067e000e 0xfd02c69f3833f000

def z466 : W := mkw 0x05c12b40ffd5ac00 0xf02e095a07fead60 0xf7c03fc0fffffe1f 0xcfbe01fe07fffff0

def z467 : W := mkw 0x0238143041401058 0x0811c0a1820a0082 0xf6383c38c1813061 0x57b1c1e1c60c0983

def z468 : W := mkw 0x07700000e5400000 0x803b8000072a0000 0xf7f80000ffe0000f 0x9fbfc00007ff0000

def z469 : W := mkw 0x07f83f3000000018 0x003fc1f980000000 0xe7f83ff800000000 0x5f3fc1ffc0000000

def z470 : W := mkw 0x8003000d109802a4 0x040018006884c015 0x6827203f019901f9 0xf3413901f80cc80f

def z471 : W := mkw 0x0fffffbe51d4001f 0x407ffffdf28ea000 0xefffffff01fe0008 0x7f7ffffff80ff000

def z472 : W := mkw 0x07f5a200fdd50800 0xe03fad1007eea840 0xffffe200ffff0e1f 0xffffff1007fff870

def z473 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x57802c00fe01fe17 0x82bc016007f00ff0

def z474 : W := mkw 0x05c02b40a600a400 0x902e015a05300520 0xf7c03fc0c600f002 0x4fbe01fe06300780

def z475 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xd6383c18c1e1f063 0x06b1c1e0c60f0f83

def z476 : W := mkw 0x85c32b4cbe91ac24 0xb42e195a65f48d61 0xffe73fd8ff81fe77 0xcfff39fec7fc0ff3

def z477 : W := mkw 0x0ffeffbe0020411f 0x007ff7fdf0010208 0xefffffff0060c19a 0xff7ffffff803060c

def z478 : W := mkw 0x0f7ed4be0000001f 0x007bf6a5f0000000 0xefffc03f00000000 0x3f7ffe01f8000000

def z479 : W := mkw 0x0080220008010800 0x2004011000400840 0x4180200038010001 0x020c010001c00800

def z480 : W := mkw 0x0000000000000000 0x0000000000000000 0x8058c00006660002 0x0402c60000333000

def z481 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x5fa70000fffe000f 0x82fd380007fff000

def z482 : W := mkw 0x07748000e5440000 0xc03ba400072a2000 0xb658c000c67e000e 0xbdb2c6000633f000

def z483 : W := mkw 0x400850a3002a4392 0x020042851801521c 0xa018d027007ec19a 0xf500c6813803f60c

def z484 : W := mkw 0x0230041000000008 0x0011802080000000 0x46202c1800000000 0x02310160c0000000

def z485 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x0827223f01990ff8 0x70413911f80cc87f

def z486 : W := mkw 0x0008143000205158 0x080040a18001028a 0x00001c000000f000 0x000000e000000780

def z487 : W := mkw 0x0fffffbef5f4515f 0xc87ffffdf7afa28a 0xfffffffffffff1ff 0xffffffffffffff8f

def z488 : W := mkw 0x0dc6ebceae01ac07 0xb06e375e75700d60 0x09c7c3c73e000e04 0x284e3e1e39f00070

def z489 : W := mkw 0x0082220c00000004 0x0004111060000000 0x0987020700000000 0x284c381038000000

def z490 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000067e000e 0x800000000033f000

def z491 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6381c00c1e0f00b 0x97b1c0e0060f0780

def z492 : W := mkw 0x8ffeffbf08090abf 0x247ff7fdf8404855 0xefffffff00010ff0 0x7f7ffffff800087f

def z493 : W := mkw 0x87ffb63dfdfd5bfc 0xec3ffdb1efefeadf 0xfffffe3fffffffff 0xfffffff1ffffffff

def z494 : W := mkw 0x808b72af18990ab6 0x24045b9578c4c855 0xe9fff3ff39990ffd 0xff4fff9ff9ccc87f

def z495 : W := mkw 0x05c5ab40be95ac00 0xf02e2d5a05f4ad60 0xffc7ffc0fe1ffe17 0xeffe3ffe07f0fff0

def z496 : W := mkw 0x0a3ed4be4160515f 0x0851f6a5f20b028a 0xfe3ffc3fc1e1f1fb 0xf7f1ffe1fe0f0f8f

def z497 : W := mkw 0x4ffeffbf002a439f 0x027ff7fdf801521c 0xefffffff007e0188 0x7f7ffffff803f00c

def z498 : W := mkw 0x0ffebf3c4160515d 0x087ff5f9e20b028a 0xffbf3c38c1e1f1fb 0xd7fdf9e1c60f0f8f

def z499 : W := mkw 0x400000400222c500 0x0200000200111628 0x000000000666c002 0x0000000000333600

def z500 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0x69e7c0003f9e000d 0xbb4f3e0001fcf000

def z501 : W := mkw 0x07748000a4000000 0x803ba40005200000 0xffffc000fe000007 0xbffffe0007f00000

def z502 : W := mkw 0x8082220d08090aa4 0x2404111068404855 0x2000223f00190ffc 0xf9000111f800c87f

def z503 : W := mkw 0x8237800d51dc02a4 0x4411bc006a8ee015 0x083fc03f01fe01e8 0x3041fe01f80ff00f

def z504 : W := mkw 0xc08b72af18bb4bb6 0x26045b9578c5da5d 0x69bfe23f39ff0ffd 0xfb4dff11f9cff87f

def z505 : W := mkw 0x023d943051f45158 0x4811eca1828fa28a 0xfe3ffc38c1fff1fb 0xf7f1ffe1c60fff8f

def z506 : W := mkw 0x077d9430f5f45158 0xc83beca187afa28a 0xffbf3c38f9e1f1fb 0xd7fdf9e1c7cf0f8f

def z507 : W := mkw 0x400040c202028402 0x0200020610101420 0x0040c1c006060000 0x0002060e00303000

def z508 : W := mkw 0x8abff6bf18990abf 0x2455ffb5f8c4c855 0x69bfe23f39990ffd 0xfb4dff11f9ccc87f

def z509 : W := mkw 0x0001000010900000 0x0000080000848000 0x49a7000039800001 0x024d380001cc0000

def z510 : W := mkw 0x0230041041401048 0x08118020820a0082 0x76202c38c18131f9 0xd3b10161c60c098f

def z511 : W := mkw 0x40000041022ac780 0x020000020811563c 0x20000227067ecf9e 0xf90000113833f67c

def z512 : W := mkw 0x07fdbf70fff5fd58 0xf83fedfb87ffafea 0xfffffff8ffffffff 0xffffffffc7ffffff

def z513 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xa038103801e0c1fa 0xd501c081c00f060f

def z514 : W := mkw 0x423854b3416a53da 0x0a11c2a59a0b529e 0xf638fc3fc1fff1fb 0xf7b1c7e1fe0fff8f

def z515 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc000f9800001 0x3ffffe0007cc0000

def z516 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x9658c000fffe000f 0x84b2c60007fff000

def z517 : W := mkw 0x85c32b0d18990aa4 0x242e195868c4c855 0xefe73fff39990ffd 0xff7f39fff9ccc87f

def z518 : W := mkw 0x0000000100080280 0x0000000008004014 0x0000002700180188 0x300000013800c00c

def z519 : W := mkw 0x0dc7eb8eb4940007 0xc06e3f5c75a4a000 0x09c7c3c73e1e0004 0x284e3e1e39f0f000

def z520 : W := mkw 0x400850e20222c512 0x0200428710111628 0xa058d3e70666c002 0x7d02c69f38333600

def z521 : W := mkw 0x05400940a600a400 0x902a004a05300520 0x004001c006000000 0x0002000e00300000

def z522 : W := mkw 0x000850a200000012 0x0000428510000000 0x000013e700000000 0x4000009f38000000

def z523 : W := mkw 0x07f83f70ae01ac18 0xb03fc1fb85700d60 0xf7f83ff8fe01fe17 0xdfbfc1ffc7f00ff0

def z524 : W := mkw 0x423854b3416a53da 0x0a11c2a59a0b529e 0x0038c03f01fe01e8 0x3001c601f80ff00f

def z525 : W := mkw 0x400040c3020a8682 0x0200020618105434 0x2040c3e7061e0f9c 0xf902061f3830f07c

def z526 : W := mkw 0x85c32b0cbc912824 0xb42e195865e48941 0x5fa72c18f9813061 0x02fd3960c7cc0983

def z527 : W := mkw 0x05c02b41ae09ae80 0xb02e015a0d704d74 0xf7c03fe7fe19ff9f 0xffbe01ff3ff0cffc

def z528 : W := mkw 0x07758040ffd5ac00 0xf03bac0207fead60 0xffffc000fffffe1f 0xbffffe0007fffff0

def z529 : W := mkw 0x07781d70e760f558 0x983bc0eb873b07aa 0x96581dc0c660f002 0x04b2c0ee06330780

def z530 : W := mkw 0x82b3261d59d91aec 0x2c159930eacec8d7 0x7fa72e3ff9993ffd 0xfbfd3971ffccc9ff

def z531 : W := mkw 0x82b7a20d59dd0aa4 0x6415bd106acee855 0x69bfe23f39ff0ffd 0xfb4dff11f9cff87f

def z532 : W := mkw 0x0008102000204110 0x0000408100010208 0xa058d020067ec19e 0xfd02c6810033f60c

def z533 : W := mkw 0x0230000041400000 0x00118000020a0000 0x0038000001e00008 0x1001c000000f0000

def z534 : W := mkw 0x0ffeffbe4140001f 0x007ff7fdf20a0000 0xffffffffc1e0000b 0xfffffffffe0f0000

def z535 : W := mkw 0x4dc6ebcf020a8687 0x026e375e78105434 0x09c7c3c7061e0e04 0x284e3e1e3830f070

def z536 : W := mkw 0x8001000018910820 0x2400080000c48841 0x0000000039810061 0x0000000001cc0803

def z537 : W := mkw 0x000810600220c510 0x0000408300110628 0xa05813e00660cf9e 0xdd02c09f0033067c

def z538 : W := mkw 0x00010040ffd5ac00 0xf000080207fead60 0x10000000fffffe1f 0x8080000007fffff0

def z539 : W := mkw 0x0ff6af1c0000000d 0x007fb578e0000000 0xefe73fd800000000 0x4f7f39fec0000000

def z540 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d1c0067ecf9e 0x8402c68e0033f67c

def z541 : W := mkw 0x423854f3436ad7da 0x0a11c2a79a1b56be 0xa078d3ff07fecffe 0xfd03c69ff83ff67f

def z542 : W := mkw 0x400850e3020a8692 0x0200428718105434 0xa058d3e7061e0e04 0x7d02c69f3830f070

def z543 : W := mkw 0x8083220c18910824 0x2404191060c48841 0x0987000038000000 0x004c380001c00000

def z544 : W := mkw 0x07f4ab0000000000 0x003fa55800000000 0xefffffc000000000 0x7f7ffffe00000000

def z545 : W := mkw 0x00000000ac012800 0xb000000005600940 0x10000000f8013001 0x0080000007c00980

def z546 : W := mkw 0x023814704360d558 0x0811c0a3821b06aa 0xf6783ff8c7e1ffff 0xdfb3c1ffc63f0fff

def z547 : W := mkw 0x0f7cddb24160515b 0x087be6ed920b028a 0xf678fdf8c1e1f1fb 0xd7b3c7efc60f0f8f

def z548 : W := mkw 0x077d9020f5f44110 0xc03bec8107afa208 0xffffd020fffec19f 0xfffffe8107fff60c

def z549 : W := mkw 0x00000040ef61fd40 0xb8000002077b0fea 0x10000000ffe1ffff 0x8080000007ff0fff

def z550 : W := mkw 0x8082220d08090aa4 0x2404111068404855 0x6180223f38010ff5 0xcb0c0111f9c0087f

def z551 : W := mkw 0x4545c0c3b69e8682 0xc22a2e061db4f434 0x09c7c3c73e1e0e04 0x284e3e1e39f0f070

def z552 : W := mkw 0xcfffffff1abbcfbf 0x267ffffff8d5de7d 0xefffffff3fffcfff 0xff7ffffff9fffe7f

def z553 : W := mkw 0x0238143000204118 0x0011c0a180010208 0xe6383c380060c19a 0xd731c1e1c003060c

def z554 : W := mkw 0x0a3ed4be0000001f 0x0051f6a5f0000000 0xee3ffc3f00000000 0x7771ffe1f8000000

def z555 : W := mkw 0x07758410f5d41048 0xc83bac2087aea082 0x5fa72c18f9813061 0x02fd3960c7cc0983

def z556 : W := mkw 0x05c02b00ac012800 0xb02e015805600940 0xf7803c00f801f013 0xc7bc01e007c00f80

def z557 : W := mkw 0x0ffebf3c0000001d 0x007ff5f9e0000000 0xefbf3c3800000000 0x577df9e1c0000000

def z558 : W := mkw 0x400850e20222c512 0x0200428710111628 0xa058d1e00666c19a 0xd502c68f0033360c

def z559 : W := mkw 0x8083224d1a998ea4 0x2404191268d4cc75 0xe9e733ff3f99cfff 0xff4f399ff9fcce7f

def z560 : W := mkw 0x8083220c18910824 0x2404191060c48841 0x69a7221839810e75 0xcb4d3910c1cc0873

def z561 : W := mkw 0x0ffefffea600a41f 0x907ff7fff5300520 0xffffffffc600f002 0x7ffffffffe300780

def z562 : W := mkw 0x0000000041605140 0x08000000020b028a 0x0000000001e001e8 0x00000000000f000f

def z563 : W := mkw 0x05c12b40be91ac00 0xb02e095a05f48d60 0xffe73fc0ff99fe1f 0xffff39fe07fccff0

def z564 : W := mkw 0x4f7cddf20222c51b 0x027be6ef90111628 0x8658ddc00666c002 0x0432c6ee00333600

def z565 : W := mkw 0xc083224d1abbcfa4 0x2604191268d5de7d 0x69a7223f3fffcfff 0xfb4d3911f9fffe7f

def z566 : W := mkw 0x808b363d18b95bfc 0x2c0459b1e8c5cadf 0x69a73e3f3999fffd 0xfb4d39f1f9cccfff

def z567 : W := mkw 0x077c9430e5645158 0xc83be4a1872b228a 0xf678fc38c7e7f1fb 0xd7b3c7e1c63f3f8f

def z568 : W := mkw 0x80832b4d1a99aea4 0x3404195a68d4cd75 0x69a73fff3999fffd 0xfb4d39fff9cccfff

def z569 : W := mkw 0x4a3ed4ff022ac79f 0x0251f6a7f811563c 0xa87fd3ff067ecf9e 0xfd43fe9ff833f67c

def z570 : W := mkw 0x05c87ba200000012 0x002e43dd10000000 0xe7d8ffe700000000 0x7f3ec7ff38000000

def z571 : W := mkw 0x477cd0e3e76ec792 0xc23be6871f3b763c 0xb658d3e7c67ecf9e 0xfdb2c69f3e33f67c

def z572 : W := mkw 0x05c02b00ac012800 0xb02e015805600940 0xf7c02c00fe013007 0x8fbe016007f00980

def z573 : W := mkw 0x400854f3022ad7da 0x0a0042a7981156be 0x00003fff0001fff0 0x400001fff8000fff

def z574 : W := mkw 0x0230041041401048 0x08118020820a0082 0x16000c00c0003000 0x00b0006006000180

def z575 : W := mkw 0x02381470ef61fd58 0xb811c0a3877b0fea 0xf6383c38ffe1ffff 0xd7b1c1e1c7ff0fff

def z576 : W := mkw 0x0ffeffbf0008029f 0x007ff7fdf8004014 0xefffffff00180f9c 0xff7ffffff800c07c

def z577 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7223f38180e04 0x7b4d3911f9c0c070

def z578 : W := mkw 0x0008102000204110 0x0000408100010208 0x000010200000c190 0x400000810000060c

def z579 : W := mkw 0x07f5ab00fdd52800 0xf03fad5807eea940 0x5fa72c00f9813001 0x02fd396007cc0980

def z580 : W := mkw 0x0238102041604110 0x0011c081020b0208 0xf6381020c1e0c19b 0xd7b1c081060f060c

def z581 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x57803fc0f801fe11 0x42bc01fe07c00ff0

def z582 : W := mkw 0x0ff6af5cae01ac0d 0xb07fb57ae5700d60 0xffe73fd8fe01fe17 0xcfff39fec7f00ff0

def z583 : W := mkw 0x07f4ab40ae01ac00 0xb03fa55a05700d60 0xffffffc0fe01fe17 0xfffffffe07f00ff0

def z584 : W := mkw 0x0008102000204110 0x0000408100010208 0x0018002000600188 0x1000c0010003000c

def z585 : W := mkw 0x85c3220dbc990aa4 0xa42e19106de4c855 0xffe7223fff990fff 0xffff3911fffcc87f

def z586 : W := mkw 0x4ffeffffae2bef9f 0xb27ff7fffd715f7c 0xfffffffffe7fff9f 0xfffffffffff3fffc

def z587 : W := mkw 0x40000041ae2bef80 0xb20000020d715f7c 0x10000000fe7fff9f 0x8080000007f3fffc

def z588 : W := mkw 0x05c02b40ef61fd40 0xb82e015a077b0fea 0xf7c03fc0ffe1ffff 0xcfbe01fe07ff0fff

def z589 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x9e7fc000c7fe000a 0x34f3fe00063ff000

def z590 : W := mkw 0x454859e3a62ae792 0x922a42cf1d31573c 0xb658dfe7c67eff9e 0xfdb2c6ff3e33f7fc

def z591 : W := mkw 0x000850a200000012 0x0000428510000000 0x8058d1c000000000 0x0402c68e00000000

def z592 : W := mkw 0x80822b4d0a09aea4 0x3404115a68504d75 0x00003fff0001fff0 0x400001fff8000fff

def z593 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x0018000000600000 0x0000c00000030000

def z594 : W := mkw 0x023d943051f45158 0x4811eca1828fa28a 0x083fc03801fe01e8 0x3041fe01c00ff00f

def z595 : W := mkw 0x0235800051d40000 0x4011ac00028ea000 0xa87fc00007fe000e 0xbd43fe00003ff000

def z596 : W := mkw 0x888b7fbf18990abf 0x24445bfdf8c4c855 0x69a73fff39990ffd 0xfb4d39fff9ccc87f

def z597 : W := mkw 0x808a363d08295bfc 0x2c0451b1e8414adf 0x00003e3f0001fff0 0x400001f1f8000fff

def z598 : W := mkw 0x0f7cddb20000001b 0x007be6ed90000000 0xe678fdf800000000 0x5733c7efc0000000

def z599 : W := mkw 0x0000004002008400 0x0000000200100420 0x000000000600ce16 0x8000000000300670

def z600 : W := mkw 0x85c32b0dbc992aa4 0xb42e19586de4c955 0x7fa72e3ff9993ffd 0xfbfd3971ffccc9ff

def z601 : W := mkw 0x0000000000000000 0x0000000000000000 0x2000020000000e14 0xc900001000000070

def z602 : W := mkw 0x0080220108090a80 0x2004011008404854 0x6180222738190f9d 0xfb0c011139c0c87c

def z603 : W := mkw 0x85c7a20dbc9d0aa4 0xe42e3d106de4e855 0x09c7c2073e1e0e04 0x284e3e1039f0f070

def z604 : W := mkw 0x0000000100080280 0x0000000008004014 0xa058c227067e0f9e 0xfd02c6113833f07c

def z605 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7201839990ffd 0x824d3900c1ccc87f

def z606 : W := mkw 0x077d9430f5f45158 0xc83beca187afa28a 0xffffc038fffe01ef 0xbffffe01c7fff00f

def z607 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x0987020739990ffd 0xa84c381039ccc87f

def z608 : W := mkw 0x00010000b4940000 0xc000080005a4a000 0x000000003e1e0004 0x0000000001f0f000

def z609 : W := mkw 0x07f83f70ef61fd58 0xb83fc1fb877b0fea 0xf7d83fc0fe61fe17 0xcfbec1fe07f30ff0

def z610 : W := mkw 0xc5cb7befbebbefb6 0xb62e5bdf7df5df7d 0xffffffffffffffff 0xffffffffffffffff

def z611 : W := mkw 0x0001000010900000 0x0000080000848000 0xe9ffc0003ffe000f 0xbf4ffe0001fff000

def z612 : W := mkw 0x423854f3022ac79a 0x0211c2a79811563c 0xe678ffff067ecf9e 0xff33c7fff833f67c

def z613 : W := mkw 0x00802b40ae01ac00 0xb004015a05700d60 0x10003fc0fe01fe17 0xc08001fe07f00ff0

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0xa058c00000000000 0x3d02c60000000000

def z615 : W := mkw 0x400950e3f7fec792 0xc2004a871fbff63c 0xb058d3e7fffecf9f 0xfd82c69f3ffff67c

def z616 : W := mkw 0xc00b50af10ba43b6 0x06005a857885d21d 0x083fc03f01fe01e8 0x3041fe01f80ff00f

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0xf6000000c0000003 0x87b0000006000000

def z618 : W := mkw 0x0ff6af1c0000000d 0x007fb578e0000000 0xefffec1800000000 0x3f7fff60c0000000

def z619 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xd7c03dc0fe01f003 0x06be01ee07f00f80

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000c001f013 0x8080000006000f80

def z621 : W := mkw 0x07f7a20cf5d40004 0xc03fbd1067aea000 0xffffe23ffffe000f 0xffffff11fffff000

def z622 : W := mkw 0x8003000d109802a4 0x040018006884c015 0x0807000700180000 0x204038003800c000

def z623 : W := mkw 0x8fffffffbe99aebf 0xb47ffffffdf4cd75 0xffffffffff99ffff 0xfffffffffffccfff

def z624 : W := mkw 0x05400040ae01ac00 0xb02a000205700d60 0xf7c00000fe01fe17 0x8fbe000007f00ff0

def z625 : W := mkw 0x0000000000000000 0x0000000000000000 0xa00010000000c012 0xc500008000000600

def z626 : W := mkw 0x05400000a4000000 0x802a000005200000 0x96400000c6000002 0x04b2000006300000

def z627 : W := mkw 0x40887be30a2bef92 0x320443df18515f7c 0xa058ffe7067fff9e 0xfd02c7ff3833fffc

def z628 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x7fa70000f998000d 0xbbfd380007ccc000

def z629 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x96183c38c061f1f2 0x44b0c1e1c6030f8f

def z630 : W := mkw 0x0001000110980280 0x000008000884c014 0x69a7022739980f9d 0xfb4d381139ccc07c

def z631 : W := mkw 0x0f7cddb20000001b 0x007be6ed90000000 0xefffddc000000000 0x3f7ffeee00000000

def z632 : W := mkw 0x07781430e5605158 0x883bc0a1872b028a 0xf7f83c38ffe1f1ff 0xdfbfc1e1c7ff0f8f

def z633 : W := mkw 0x80010001109802a0 0x040008000884c015 0x00000000019801e8 0x00000000000cc00f

def z634 : W := mkw 0x45c87be3ae2bef92 0xb22e43df1d715f7c 0xf7c03fe7fe01ff97 0xcfbe01ff3ff00ffc

def z635 : W := mkw 0x077dd0a2f5d40012 0xc03bee8517aea000 0xffffd3e7fffe000f 0xfffffe9f3ffff000

def z636 : W := mkw 0x0238143000000018 0x0011c0a180000000 0x0038003800000000 0x1001c001c0000000

def z637 : W := mkw 0x05400000a4000000 0x802a000005200000 0x01c000003e000004 0x080e000001f00000

def z638 : W := mkw 0x888a7fbf08090abf 0x244453fdf8404855 0x00003fff00010ff0 0x400001fff800087f

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0xa01800000060000a 0x9500c00000030000

def z640 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x0000223f39990ffd 0xc0000111f9ccc87f

def z641 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xb6181c20c060f19a 0xd5b0c0e10603078c

def z642 : W := mkw 0x8083224dbe99aea4 0xb40419126df4cd75 0x79a7223fff99ffff 0xfbcd3911fffccfff

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x6000200000010011 0xc300010000000800

def z644 : W := mkw 0x07f02f10ed413848 0xb83f8178876a09c2 0x57a02c18f9813061 0x02bd0160c7cc0983

def z645 : W := mkw 0x0235800051d40000 0x4011ac00028ea000 0x0827000001800000 0x00413800000c0000

def z646 : W := mkw 0x07f5ab00fdd52800 0xf03fad5807eea940 0xffffec00ffff300f 0xbfffff6007fff980

def z647 : W := mkw 0x8083220c18910824 0x2404191060c48841 0x69a7223f39810061 0x7b4d3911f9cc0803

def z648 : W := mkw 0x87f7ab4dffddaea4 0xf43fbd5a6ffeed75 0xffffffffffffffff 0xffffffffffffffff

def z649 : W := mkw 0x0a36841c0000000d 0x0051b420e0000000 0x0827001800000000 0x00413800c0000000

def z650 : W := mkw 0x00802b400a01ac00 0x3004015a00500d60 0xf6003fc0c001fe13 0xc7b001fe06000ff0

def z651 : W := mkw 0x07758040f7d48400 0xc03bac0207bea420 0xffffd3c0fffece1f 0xfffffe9e07fff670

def z652 : W := mkw 0x40887be30a2bef92 0x320443df18515f7c 0x00003fe70001ff90 0x400001ff38000ffc

def z653 : W := mkw 0x0000000100080280 0x0000000008004014 0x0000022700000f90 0x400000113800007c

def z654 : W := mkw 0x0fffffbe1090001f 0x007ffffdf0848000 0xefffffff3998000d 0xff7ffffff9ccc000

def z655 : W := mkw 0x423850e3436ac792 0x0211c2871a1b563c 0xf678d3e7c7fecf9f 0xffb3c69f3e3ff67c

def z656 : W := mkw 0x408872e30a2bcf92 0x2204439718515e7c 0xe1d8f3e73e7fcf9f 0xff0ec79f39f3fe7c

def z657 : W := mkw 0x02ba363c4160515c 0x0815d1b1e20b028a 0xffbf3e3fc1e1f1fb 0xfffdf9f1fe0f0f8f

def z658 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x0040d3e7061ecf94 0x6802069f3830f67c

def z659 : W := mkw 0x0008143000205158 0x080040a18001028a 0x00000038000001e0 0x00000001c000000f

def z660 : W := mkw 0xc08b72ef1abbcfb6 0x26045b9778d5de7d 0xa9dfd3e73e7ecf9e 0xfd4efe9f39f3f67c

def z661 : W := mkw 0x0238143000205158 0x0811c0a18001028a 0xe6383c380001f1f0 0x5731c1e1c0000f8f

def z662 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6380038c1e001eb 0x97b1c001c60f000f

def z663 : W := mkw 0x05c87be2ae01ac12 0xb02e43df15700d60 0xf7d8ffe7fe01fe17 0xffbec7ff3ff00ff0

def z664 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x61c023c03e010e15 0xcb0e011e01f00870

def z665 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x10380038c1e1f1fb 0x9081c001c60f0f8f

def z666 : W := mkw 0x4ffefffe0222c51f 0x027ff7fff0111628 0xefffffff0666c002 0x7f7ffffff8333600

def z667 : W := mkw 0x0540090000000000 0x002a004800000000 0x86401dc000000000 0x043200ee00000000

def z668 : W := mkw 0x07748000e5440000 0xc03ba400072a2000 0x16000000c0000000 0x00b0000006000000

def z669 : W := mkw 0x05448000a4040000 0xc02a240005202000 0x0040c00006060000 0x0002060000303000

def z670 : W := mkw 0x0082220c08010804 0x2004111060400840 0x69a7223f38010e15 0xfb4d3911f9c00870

def z671 : W := mkw 0x02b8363049615958 0x2815c1b1824b0aca 0xf7b83e38f9e1ffff 0xdfbdc1f1c7cf0fff

def z672 : W := mkw 0x0000004002008400 0x0000000200100420 0xf6403fc0c601fe17 0xcfb201fe06300ff0

def z673 : W := mkw 0x0001000010900000 0x0000080000848000 0x000000003998000d 0x8000000001ccc000

def z674 : W := mkw 0x05c02b00ac012800 0xb02e015805600940 0xf7c03fc0f8013001 0x4fbe01fe07c00980

def z675 : W := mkw 0x400850a3002a4392 0x020042851801521c 0xa058c027067e018e 0xbd02c6013833f00c

def z676 : W := mkw 0x8fffffbffddd0abf 0xe47ffffdffeee855 0xffffffffffff0fff 0xfffffffffffff87f

def z677 : W := mkw 0x400850e20222c512 0x0200428710111628 0xa058d1c0067ec00e 0xbd02c68e0033f600

def z678 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d1e7067ec18a 0x3402c68f3833f60c

def z679 : W := mkw 0x0a3fd4be51d4001f 0x4051fea5f28ea000 0x083fc03f01fe0008 0x3041fe01f80ff000

def z680 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x6038203801e101f9 0xd301c101c00f080f

def z681 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6383c38c060f002 0x57b1c1e1c6030780

def z682 : W := mkw 0x454dd0e3b6bec792 0xc22a6e871db5f63c 0xa9dfd3e73e7ecf9e 0xfd4efe9f39f3f67c

def z683 : W := mkw 0x00883f700a21fd58 0x380441fb80510fea 0x00003ff80001fff0 0x400001ffc0000fff

def z684 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7203f399901e9 0x324d3901f9ccc80f

def z685 : W := mkw 0x8083220dfddd0aa4 0xe40419106feee855 0x79a7223fffff0fff 0xfbcd3911fffff87f

def z686 : W := mkw 0x07758000f5f45140 0xc83bac0007afa28a 0xffffc000fffff1ff 0xbffffe0007ffff8f

def z687 : W := mkw 0xc2bb76ff5bfbdffe 0x2e15dbb7fadfdeff 0xffffffffffffffff 0xffffffffffffffff

def z688 : W := mkw 0x82bb363d59f95bfc 0x2c15d9b1eacfcadf 0x69bf223f39f90ffd 0xfb4df911f9cfc87f

def z689 : W := mkw 0x077c9430e5645158 0xc83be4a1872b228a 0x9658dc00c666f002 0x04b2c6e006333780

def z690 : W := mkw 0x400040c3020a8682 0x0200020618105434 0x000003c700000e00 0x0000001e38000070

def z691 : W := mkw 0x0f7cddb2e544001b 0xc07be6ed972a2000 0x9658ddc0c6660002 0x04b2c6ee06333000

def z692 : W := mkw 0x00802240ae01ac00 0xb004011205700d60 0x71802200fe01fe17 0xcb8c011007f00ff0

def z693 : W := mkw 0x8082220c08010824 0x2404111060400841 0x0000201800010060 0x00000100c0000803

def z694 : W := mkw 0x8fffffbe1891083f 0x247ffffdf0c48841 0xefffffff39810061 0x7f7ffffff9cc0803

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x96001c00c000f002 0x04b000e006000780

def z696 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000000018101f9 0x80000000000c080f

def z697 : W := mkw 0x02ba363c0000001c 0x0015d1b1e0000000 0xefbf3e3f00000000 0x7f7df9f1f8000000

def z698 : W := mkw 0x02b83f704b61fd58 0x3815c1fb825b0fea 0xf6383ff8c1e1fffb 0xd7b1c1ffc60f0fff

def z699 : W := mkw 0x000000400a01ac00 0x3000000200500d60 0x000000000001fe10 0x0000000000000ff0

def z700 : W := mkw 0x8fffffbf109802bf 0x047ffffdf884c015 0xefffffff019801e8 0x7f7ffffff80cc00f

def z701 : W := mkw 0x0f7fd4bef5d4001f 0xc07bfea5f7aea000 0xffffc03ffffe000f 0xbffffe01fffff000

def z702 : W := mkw 0x47f87ff3ef6bffda 0xba3fc3ff9f7b5ffe 0xf7f8ffffffffffff 0xffbfc7ffffffffff

def z703 : W := mkw 0x0080220008010800 0x2004011000400840 0x0000220000010e10 0x4000011000000870

def z704 : W := mkw 0x0080220000000000 0x0004011000000000 0x6180220000000000 0x4b0c011000000000

def z705 : W := mkw 0x8083220c18910824 0x2404191060c48841 0x69a720183999006d 0xbb4d3900c1ccc803

def z706 : W := mkw 0x000850a300080292 0x0000428518004014 0xa058d3e700180f9c 0xfd02c69f3800c07c

def z707 : W := mkw 0x02b5ab405bd5ac00 0x7015ad5a02dead60 0x083fffc001fffe18 0x7041fffe000ffff0

def z708 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf638fc38c1fff1fb 0xf7b1c7e1c60fff8f

def z709 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6383c38c7fff1ff 0xd7b1c1e1c63fff8f

def z710 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7d8ffc0fe67fe17 0xcfbec7fe07f33ff0

def z711 : W := mkw 0x08826b8e00000007 0x0044135c70000000 0x69a723ff00000000 0x7b4d391ff8000000

def z712 : W := mkw 0x42391061f7fec790 0xc211c8830fbff63c 0xf6381020fffecf9f 0xd7b1c08107fff67c

def z713 : W := mkw 0xc08b72ee1ab3cd36 0x26045b9770d59e69 0xc9fff1d83fe7c063 0x064fff8ec1ff3e03

def z714 : W := mkw 0x0f7eddbe4160515f 0x087bf6edf20b028a 0x9e7fddffc1e0f1ea 0x34f3feeffe0f078f

def z715 : W := mkw 0x0ffeffbea400001f 0x807ff7fdf5200000 0xfffffffff8000001 0x7fffffffffc00000

def z716 : W := mkw 0x0ffeffbe4140001f 0x007ff7fdf20a0000 0xffffffffc1e101fb 0xfffffffffe0f080f

def z717 : W := mkw 0x02ba76be0000001e 0x0015d3b5f0000000 0xefffffff00000000 0x7f7ffffff8000000

def z718 : W := mkw 0x07fcfba200000012 0x003fe7dd10000000 0xefffffe700000000 0x7f7fffff38000000

def z719 : W := mkw 0x0ffeffbe0020515f 0x087ff7fdf001028a 0xefffffff0061f1fa 0xff7ffffff8030f8f

def z720 : W := mkw 0x80010041be99aea0 0xb40008020df4cd75 0xf6203c38ff99ffff 0xd7b101e1c7fccfff

def z721 : W := mkw 0x87f6a20ded4d0aa4 0xe43fb5106f6a6855 0x9658e23fc6670ff2 0x44b2c711fe33387f

def z722 : W := mkw 0x4ff6af5d022ac78d 0x027fb57ae811563c 0x4fa72c18067ecf9e 0x827d3960c033f67c

def z723 : W := mkw 0x0ffeffbe0000105f 0x087ff7fdf0000082 0xefffffff00013060 0x7f7ffffff8000983

def z724 : W := mkw 0x0ff6eb8e00000007 0x007fb75c70000000 0x4fe7c3c700000000 0x2a7f3e1e38000000

def z725 : W := mkw 0x07f6ab0c00000004 0x003fb55860000000 0xefffffff00000000 0x7f7ffffff8000000

def z726 : W := mkw 0x0ffeffbe0020411f 0x007ff7fdf0010208 0xefffffff0000c190 0x7f7ffffff800060c

def z727 : W := mkw 0x0dc6eb8e41605147 0x086e375c720b028a 0x19c7c3c7c1e1f1fb 0xa8ce3e1e3e0f0f8f

def z728 : W := mkw 0x0544c08200000002 0x002a260410000000 0x09c7c3c700000000 0x284e3e1e38000000

def z729 : W := mkw 0x0ffeffbe4144001f 0x407ff7fdf20a2000 0xefffffff00660000 0x7f7ffffff8033000

def z730 : W := mkw 0x0000000041605140 0x08000000020b028a 0xf6203c38c1e1f1fb 0xd7b101e1c60f0f8f

def z731 : W := mkw 0x45c87ba3ac2b6b92 0xb22e43dd1d615b5c 0x5798ec27f87f3189 0x32bcc7613fc3f98c

def z732 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0x89dfc0003e7e0006 0x2c4efe0001f3f000

def z733 : W := mkw 0x0230041041605148 0x08118020820b028a 0xf6203c18c1e1f1fb 0xc7b101e0c60f0f8f

def z734 : W := mkw 0x0dcefbae00000017 0x006e77dd70000000 0x09dfc3e700000000 0x384efe1f38000000

def z735 : W := mkw 0x477dd0e3f7fec792 0xc23bee871fbff63c 0x5fa713e7f980cf91 0x42fd389f3fcc067c

def z736 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xa9ffd3ff00000000 0x7d4ffe9ff8000000

def z737 : W := mkw 0x0ff6ef9e4140104f 0x087fb77cf20a0082 0x5fe7efdfc1813061 0x2aff3f7efe0c0983

def z738 : W := mkw 0x05400940ae01ac00 0xb02a004a05700d60 0x96401dc0fe00fe06 0x04b200ee07f007f0

def z739 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x09c7e3ff00000000 0x684e3f1ff8000000

def z740 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff00010011 0xff7ffffff8000800

def z741 : W := mkw 0x05400940ae01ac00 0xb02a004a05700d60 0xf6403dc0fe01fe17 0xc7b201ee07f00ff0

def z742 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xefffffff01e1f1f8 0x7f7ffffff80f0f8f

def z743 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x09a7223f39990ffc 0x784d3911f9ccc87f

def z744 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x69c7e3c700000000 0x6b4e3f1e38000000

def z745 : W := mkw 0x023854b24160515a 0x0811c2a5920b028a 0xf678ffffc7fff1ff 0xffb3c7fffe3fff8f

def z746 : W := mkw 0x82bb363d59f95bfc 0x2c15d9b1eacfcadf 0x9f9f1e07f878fe06 0x2cfcf8f03fc3c7f0

def z747 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xfffffc38fffff1ff 0xffffffe1c7ffff8f

def z748 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x09dfc3c700000000 0x284efe1e38000000

def z749 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fc0f801fe11 0x4fbe01fe07c00ff0

def z750 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffe038fffe000f 0xffffff01c7fff000

def z751 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xe078f3ff067ecf9e 0xff03c79ff833f67c

def z752 : W := mkw 0x0806c08e00000007 0x0040360470000000 0x0847c3c700000000 0x28423e1e38000000

def z753 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xe9e733ff39990ffd 0xff4f399ff9ccc87f

def z754 : W := mkw 0x0dc6eb8eac012807 0xb06e375c75600940 0x09c7c3c738000000 0x284e3e1e39c00000

def z755 : W := mkw 0x0ffeffbee540001f 0x807ff7fdf72a0000 0xffffffffffe0000f 0xffffffffffff0000

def z756 : W := mkw 0x0ffeffbe0801081f 0x207ff7fdf0400840 0xefffffff38000e04 0x7f7ffffff9c00070

def z757 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xd7c03fc0fe01fe07 0x0ebe01fe07f00ff0

def z758 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d3e7067ecf9e 0xc402c69f3833f67c

def z759 : W := mkw 0x0082224cae01ac04 0xb004111265700d60 0x79a7223ffe01fe17 0xfbcd3911fff00ff0

def z760 : W := mkw 0x088b7fbef5d4001f 0xc0445bfdf7aea000 0x10003ffffffe000f 0xc08001fffffff000

def z761 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x09dfc0003e7e0004 0x284efe0001f3f000

def z762 : W := mkw 0x0ffeffbeac01281f 0xb07ff7fdf5600940 0xfffffffff8013e15 0xffffffffffc009f0

def z763 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xffffffffc0000003 0xfffffffffe000000

def z764 : W := mkw 0x05c22b0c00000004 0x002e115860000000 0x69e723ff00000000 0x7b4f391ff8000000

def z765 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc1e0f1ea 0x7ffffffffe0f078f

def z766 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x0058c3c7067e0e04 0x2802c61e3833f070

def z767 : W := mkw 0x0ff6eb8e00000007 0x007fb75c70000000 0xefffe3ff00000000 0x7f7fff1ff8000000

def z768 : W := mkw 0x40010041b6bec780 0xc20008020db5f63c 0x000000003e7ecf9e 0x8000000001f3f67c

def z769 : W := mkw 0x08826b8e00000007 0x0044135c70000000 0x098703c700000000 0x284c381e38000000

def z770 : W := mkw 0x0ffeffbe4140105f 0x087ff7fdf20a0082 0xffffffffc1e1306b 0xfffffffffe0f0983

def z771 : W := mkw 0x40010041b69e8680 0xc20008020db4f434 0x000000003e1e0e04 0x0000000001f0f070

def z772 : W := mkw 0x80010041be99aea0 0xb40008020df4cd75 0x10000000fe19fe17 0x8080000007f0cff0

def z773 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7203f39990ffd 0xb24d3901f9ccc87f

def z774 : W := mkw 0x0a3ed4feae01ac1f 0xb051f6a7f5700d60 0x183fc03ffe01fe17 0xb0c1fe01fff00ff0

def z775 : W := mkw 0x0ffeffbe4160411f 0x007ff7fdf20b0208 0xffffffffc1e0c19b 0xfffffffffe0f060c

def z776 : W := mkw 0x0008143041605158 0x080040a1820b028a 0xf6003c38c1e1f1fb 0xc7b001e1c60f0f8f

def z777 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x5fffc000fffe000d 0x3afffe0007fff000

def z778 : W := mkw 0x0ffeffbe4140001f 0x007ff7fdf20a0000 0xffffffffc1800001 0x7ffffffffe0c0000

def z779 : W := mkw 0x400854f3022ac79a 0x020042a79811563c 0xa058ffff067ecf9e 0xfd02c7fff833f67c

def z780 : W := mkw 0xc00910611abbcfb0 0x2600488308d5de7d 0xe03830383fffcfff 0xd701c181c1fffe7f

def z781 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6783c38c7e1f1ff 0xdfb3c1e1c63f0f8f

def z782 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf678fc38c1e1f1fb 0xffb3c7e1c60f0f8f

def z783 : W := mkw 0xc08a7bef0a2befb6 0x360453df78515f7d 0x00003fff0001fff0 0x400001fff8000fff

def z784 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0xa9dfc3c700000000 0x3d4efe1e38000000

def z785 : W := mkw 0x05400940ae01ac00 0xb02a004a05700d60 0xb6401fc0fe01fe17 0xcdb200fe07f00ff0

def z786 : W := mkw 0x0ffeffbe0020515f 0x087ff7fdf001028a 0xefffffff0000f000 0x7f7ffffff8000780

def z787 : W := mkw 0xc0010041bebbefa0 0xb60008020df5df7d 0x10000000ffffffff 0x8080000007ffffff

def z788 : W := mkw 0x023854b24160515a 0x0811c2a5920b028a 0xf678fdf8c1e1f1fb 0xd7b3c7efc60f0f8f

def z789 : W := mkw 0x054d9430b4b45158 0xc82a6ca185a5a28a 0x09c7fc383e1ff1f4 0x684e3fe1c1f0ff8f

def z790 : W := mkw 0x07758900f5d42000 0xd03bac4807aea100 0xffffcc00fffe300f 0xbffffe6007fff180

def z791 : W := mkw 0x47748041022ac780 0x023ba4020811563c 0xefffc000067ecf9e 0xbf7ffe000033f67c

def z792 : W := mkw 0x0abeffbe4160515f 0x0855f7fdf20b028a 0xfe3fffffc1e1f1fb 0xf7f1fffffe0f0f8f

def z793 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7223f3fff0fff 0xfb4d3911f9fff87f

def z794 : W := mkw 0x077cd4b24160515a 0x083be6a5920b028a 0xffffffffc1e1f1fb 0xfffffffffe0f0f8f

def z795 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058d3e707ffcfff 0xfd02c69f383ffe7f

def z796 : W := mkw 0x0082628e00000006 0x0004131470000000 0x09c7c3c700000000 0x284e3e1e38000000

def z797 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0xa9c7d3c700000000 0x6d4e3e9e38000000

def z798 : W := mkw 0x05c22b4cae01ac04 0xb02e115a65700d60 0xffe73fffff81ffff 0xffff39fffffc0fff

def z799 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xe1d8d3e73e7ecf9f 0xff0ec69f39f3f67c

def z800 : W := mkw 0x07fef2ae00000016 0x003ff79570000000 0xeffff3ff00000000 0x7f7fff9ff8000000

def z801 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff01800009 0xff7ffffff80c0000

def z802 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7803fc0f801fe13 0xc7bc01fe07c00ff0

def z803 : W := mkw 0x8dc7ebcfbe99aea7 0xb46e3f5e7df4cd75 0x09c7c3c73e180e04 0x284e3e1e39f0c070

def z804 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xf678ffffc7ffffff 0xffb3c7fffe3fffff

def z805 : W := mkw 0x8543094db698a6a4 0x942a184a6db4c535 0x9e671dffc798f1ea 0x34f338effe3cc78f

def z806 : W := mkw 0x05400940ae01ac00 0xb02a004a05700d60 0xf7c01dc0fe01fe17 0x8fbe00ee07f00ff0

def z807 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fc0fe19fe1f 0xffbe01fe07f0cff0

def z808 : W := mkw 0x0dcefbae00000017 0x006e77dd70000000 0x89dfd3c700000000 0x2c4efe9e38000000

def z809 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc060f19a 0xfffffffffe03078c

def z810 : W := mkw 0x0082220c00000004 0x0004111060000000 0xe9e733ff00000000 0x7f4f399ff8000000

def z811 : W := mkw 0x0ffeffbe0801081f 0x207ff7fdf0400840 0xefffffff38010001 0x7f7ffffff9c00800

def z812 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0xe9ffc0003ffe000f 0xbf4ffe0001fff000

def z813 : W := mkw 0x0ffeffbe4140105f 0x087ff7fdf20a0082 0xffffffffc0003000 0x7ffffffffe000180

def z814 : W := mkw 0x07f83f70ef61fd58 0xb83fc1fb877b0fea 0x01f803f83fe00fec 0x180fc01fc1ff007f

def z815 : W := mkw 0x85c7ab4dbe9daea4 0xf42e3d5a6df4ed75 0x09c7c3c73e1e0e04 0x284e3e1e39f0f070

def z816 : W := mkw 0x0ff6eb8e00000007 0x007fb75c70000000 0x09ffc3c700000000 0x384ffe1e38000000

def z817 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xa9ffc0003ffe000e 0xbd4ffe0001fff000

def z818 : W := mkw 0x008022400a018c00 0x2004011200500c60 0xf7c03fc0fe01fe17 0xcfbe01fe07f00ff0

def z819 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff06660002 0x7f7ffffff8333000

def z820 : W := mkw 0x8f7dddb318990abb 0x247beeed98c4c855 0x8658ddc039990ffd 0x8432c6ee01ccc87f

def z821 : W := mkw 0x0ff6eb8e41400007 0x007fb75c720a0000 0xffffc3c7c1e0000b 0xbffffe1e3e0f0000

def z822 : W := mkw 0x0ffeffbe0801081f 0x207ff7fdf0400840 0xfffffffff801fe17 0xffffffffffc00ff0

def z823 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7023f39980fed 0xbb4d3811f9ccc07f

def z824 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc7fff1ff 0xfffffffffe3fff8f

def z825 : W := mkw 0x00010000f5d40000 0xc000080007aea000 0xf9ffc000fffe000f 0xbfcffe0007fff000

def z826 : W := mkw 0x088effbe0000001f 0x004477fdf0000000 0x0807ffff00000000 0x60403ffff8000000

def z827 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffdfc000fe7e0007 0xaffefe0007f3f000

def z828 : W := mkw 0x40010041f7de8680 0xc20008020fbef434 0x10000000fffe0e0f 0x8080000007fff070

def z829 : W := mkw 0x800100411a99aea0 0x3400080208d4cd75 0x000000003999fffd 0x8000000001cccfff

def z830 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xb658dfe7c67eff9e 0xfdb2c6ff3e33f7fc

def z831 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7d83fc0fe61fe1f 0xdfbec1fe07f30ff0

def z832 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0xffdfc000fe7e000f 0xbffefe0007f3f000

def z833 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x69e7c3c700000000 0x3b4f3e1e38000000

def z834 : W := mkw 0x0230041041605148 0x08118020820b028a 0x76202c38c1e1f1fb 0xd3b10161c60f0f8f

def z835 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xe658ffe7067ecf9e 0xff32c7ff3833f67c

def z836 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc1e0f00b 0xfffffffffe0f0780

def z837 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c0ffc0fe1ffe17 0xefbe07fe07f0fff0

def z838 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7223f39810ff9 0xd34d3911f9cc087f

def z839 : W := mkw 0x0ffeffbea400201f 0x907ff7fdf5200100 0xffffffffc0003000 0x7ffffffffe000180

def z840 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x0058c3e7067ecf9e 0xb802c61f3833f67c

def z841 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7e03ff8fe01fe17 0xdfbf01ffc7f00ff0

def z842 : W := mkw 0x0f7eddbe0000001f 0x007bf6edf0000000 0xae7fdfff00000000 0x7d73fefff8000000

def z843 : W := mkw 0xc0010041ffffcfa0 0xe60008020ffffe7d 0x10000000ffffcfff 0x8080000007fffe7f

def z844 : W := mkw 0x008a72ae00000016 0x0004539570000000 0x69a733ff00000000 0x7b4d399ff8000000

def z845 : W := mkw 0x488a7fff0a2bef9f 0x324453fff8515f7c 0x00003fff0001ff90 0x400001fff8000ffc

def z846 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffec00ffff300f 0xbfffff6007fff980

def z847 : W := mkw 0x477cd4f2e766d55a 0xca3be6a7973b36aa 0x9658ddc0c666f002 0x04b2c6ee06333780

def z848 : W := mkw 0x023854b24160515a 0x0811c2a5920b028a 0xf638fc3fc1e1f1fb 0xf7b1c7e1fe0f0f8f

def z849 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xdfffc000fffe000b 0x36fffe0007fff000

def z850 : W := mkw 0x82391471fff9fff8 0xbc11c8a38fffcfff 0xf6383c38fff9ffff 0xd7b1c1e1c7ffcfff

def z851 : W := mkw 0x0abeffbe0000001f 0x0055f7fdf0000000 0xee3fffff00000000 0x7771fffff8000000

def z852 : W := mkw 0x0dceffbe0020515f 0x086e77fdf001028a 0x09c7ffff0001f1f0 0x684e3ffff8000f8f

def z853 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x79a7223ff999ffff 0xfbcd3911ffcccfff

def z854 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc000ffff01ff 0xbffffe0007fff80f

def z855 : W := mkw 0x0ffeffbee544001f 0xc07ff7fdf72a2000 0xffffffffc67e000e 0xfffffffffe33f000

def z856 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xb058d3e7c67fff9f 0xfd82c69f3e33fffc

def z857 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xefffffff00600000 0x7f7ffffff8030000

def z858 : W := mkw 0x05c22b4cae01ac04 0xb02e115a65700d60 0xffc73fc7fe01fe17 0xeffe39fe3ff00ff0

def z859 : W := mkw 0x423044d3434a96ca 0x0a1182269a1a54b6 0x5660efdfc79f3e65 0x2ab3077efe3cf9f3

def z860 : W := mkw 0xc08a72ef0a2bcfb6 0x2604539778515e7d 0x000013e70000cf90 0x4000009f3800067c

def z861 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058d3e7067e0f8c 0x7d02c69f3833f07c

def z862 : W := mkw 0x0dceffbe0000001f 0x006e77fdf0000000 0x09873fff00000000 0x404c39fff8000000

def z863 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x56203c38c1e1f1fb 0xc2b101e1c60f0f8f

def z864 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fe7fe01fe17 0xffbe01ff3ff00ff0

def z865 : W := mkw 0x800100411a998ea0 0x2400080208d4cc75 0x000000003f99cfff 0x8000000001fcce7f

def z866 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xefffffff01e0c1fa 0xff7ffffff80f060f

def z867 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff0001f010 0x7f7ffffff8000f80

def z868 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffe000ffff001f 0xffffff0007fff800

def z869 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xe058f3e7067fcf9f 0xff02c79f3833fe7c

def z870 : W := mkw 0x07fa3f3c0000001c 0x003fd1f9e0000000 0xefff3fff00000000 0x7f7ff9fff8000000

def z871 : W := mkw 0x0ffeffbe4140105f 0x087ff7fdf20a0082 0xefffffff01800060 0x7f7ffffff80c0003

def z872 : W := mkw 0x00000040ae01ac00 0xb000000205700d60 0xf6403fc0fe01fe17 0xcfb201fe07f00ff0

def z873 : W := mkw 0x0dc6eb8ea4000007 0x806e375c75200000 0x09c7c3c73e000004 0x284e3e1e39f00000

def z874 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x96183c38c1e1f1fb 0xc4b0c1e1c60f0f8f

def z875 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x29c7c3e700000000 0x794e3e1f38000000

def z876 : W := mkw 0x05c22b4cae01ac04 0xb02e115a65700d60 0xf7c03ffffe01fe17 0xcfbe01fffff00ff0

def z877 : W := mkw 0x02358000f5d40000 0xc011ac0007aea000 0x79bfc000fffe000f 0xbbcdfe0007fff000

def z878 : W := mkw 0x42391471f7fed7d8 0xca11c8a38fbff6be 0xf6383c38ffffffff 0xd7b1c1e1c7ffffff

def z879 : W := mkw 0xc00100411abbcfa0 0x2600080208d5de7d 0x000000003999cffd 0x8000000001ccce7f

def z880 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc1e1f063 0x7ffffffffe0f0f83

def z881 : W := mkw 0x0231000051d00000 0x00118800028e8000 0xffffc000fffe000f 0xbffffe0007fff000

def z882 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xd6383c38c1e1f1eb 0x16b1c1e1c60f0f8f

def z883 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc038fffe01ef 0xbffffe01c7fff00f

def z884 : W := mkw 0x0f7eddbe4160515f 0x087bf6edf20b028a 0xfe7ffdffc1e1f1fb 0xf7f3ffeffe0f0f8f

def z885 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xffffffffc000f002 0x7ffffffffe000780

def z886 : W := mkw 0x0238143000000018 0x0011c0a180000000 0xf6383c38c181f1fb 0xd7b1c1e1c60c0f8f

def z887 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x19ffc000fffe000f 0xb8cffe0007fff000

def z888 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefbf3fff00000000 0x577df9fff8000000

def z889 : W := mkw 0x0dcefbae00000017 0x006e77dd70000000 0xe9fff3ff00000000 0x7f4fff9ff8000000

def z890 : W := mkw 0xc00100411a9b8ea0 0x2600080208d4dc75 0x000000003f9f0ffd 0x8000000001fcf87f

def z891 : W := mkw 0x00822b0c00000004 0x0004115860000000 0x69a73fff00000000 0x7b4d39fff8000000

def z892 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xe9ffe23f39990ffd 0xff4fff11f9ccc87f

def z893 : W := mkw 0x0dcefbae00000017 0x006e77dd70000000 0x09c7d3e700000000 0x684e3e9f38000000

def z894 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fc0ff81ffff 0xcfbe01fe07fc0fff

def z895 : W := mkw 0x87f7ab0cfdd52824 0xf43fbd5867eea941 0x5fa72c18f9813061 0x02fd3960c7cc0983

def z896 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6783ff8c1e1f1fb 0xdfb3c1ffc60f0f8f

def z897 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x57c03fc0fe01fe15 0x4abe01fe07f00ff0

def z898 : W := mkw 0x0001000110980280 0x000008000884c014 0x69a7223f39990ffd 0xfb4d3911f9ccc87f

def z899 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff38000005 0xff7ffffff9c00000

def z900 : W := mkw 0x05c22b0c00000004 0x002e115860000000 0x09c703c700000000 0x284e381e38000000

def z901 : W := mkw 0x0a3eddbe0000001f 0x0051f6edf0000000 0x083fddff00000000 0x3041feeff8000000

def z902 : W := mkw 0x0ffeffbea404001f 0xc07ff7fdf5202000 0xefffffff06060000 0x7f7ffffff8303000

def z903 : W := mkw 0x088a7fbe0000001f 0x004453fdf0000000 0x49a73fff00000000 0x424d39fff8000000

def z904 : W := mkw 0x40010041ffffef80 0xf20008020fffff7c 0x10000000ffffff9f 0x8080000007fffffc

def z905 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff007e0008 0x7f7ffffff803f000

def z906 : W := mkw 0x000850a200000012 0x0000428510000000 0xe9ffd3e700000000 0x7f4ffe9f38000000

def z907 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc227fffe000f 0xfffffe113ffff000

def z908 : W := mkw 0x0ffeffbe4140001f 0x007ff7fdf20a0000 0xffffffffc1e1f01b 0xfffffffffe0f0f80

def z909 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6203c38c181f1f3 0xc7b101e1c60c0f8f

def z910 : W := mkw 0x0235800051d40000 0x4011ac00028ea000 0xe9ffc0003ffe000f 0xbf4ffe0001fff000

def z911 : W := mkw 0x0ffeffbeac01081f 0xa07ff7fdf5600840 0xfffffffffe010e17 0xfffffffffff00870

def z912 : W := mkw 0x0dc6eb8e08010807 0x206e375c70400840 0x09c7c3c738000e04 0x284e3e1e39c00070

def z913 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc061f013 0xfffffffffe030f80

def z914 : W := mkw 0x0ffefbae00000017 0x007ff7dd70000000 0xefffd3e700000000 0x7f7ffe9f38000000

def z915 : W := mkw 0x05c4ab40ae01ac00 0xb02e255a05700d60 0xffc7ffc0fe01fe17 0xeffe3ffe07f00ff0

def z916 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fe0fe01ff9f 0xdfbe01ff07f00ffc

def z917 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xdfffc000fffe0007 0x2efffe0007fff000

def z918 : W := mkw 0x0ffeffbe0801281f 0x307ff7fdf0400940 0xefffffff00013000 0x7f7ffffff8000980

def z919 : W := mkw 0x05410000b4900000 0x802a080005a48000 0xffffc000fffe000f 0xbffffe0007fff000

def z920 : W := mkw 0x07758410f5d41048 0xc83bac2087aea082 0xfffffc18fffff07f 0xffffffe0c7ffff83

def z921 : W := mkw 0x85c12b0118990aa0 0x242e095808c4c855 0xe7c03fc039990ffd 0xcf3e01fe01ccc87f

def z922 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6383c38c1f9f1ff 0xffb1c1e1c60fcf8f

def z923 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xfffffc00fffe000f 0xffffffe007fff000

def z924 : W := mkw 0x0dcefbae00204117 0x006e77dd70010208 0xa9dfd3e70060c19a 0xfd4efe9f3803060c

def z925 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x4fbfffff00000000 0x727dfffff8000000

def z926 : W := mkw 0x0ffeffbe4140105f 0x087ff7fdf20a0082 0xffffffffc181f073 0xfffffffffe0c0f83

def z927 : W := mkw 0x80010041be99aea0 0xb40008020df4cd75 0x000000003f990ffd 0x8000000001fcc87f

def z928 : W := mkw 0x07758900f5d40000 0xc03bac4807aea000 0xffffddc0fffe000f 0xbffffeee07fff000

def z929 : W := mkw 0x0a3cd4b24160515b 0x0851e6a5920b028a 0xf638fc38c1e1f1fb 0xd7b1c7e1c60f0f8f

def z930 : W := mkw 0x0f7cddf2e760f55b 0x987be6ef973b07aa 0x9658ddc0c660f002 0x04b2c6ee06330780

def z931 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x4fffefff00000000 0x3a7fff7ff8000000

def z932 : W := mkw 0x0ffeffbeed61795f 0xb87ff7fdf76b0bca 0xfffffffff9e1f1fb 0xffffffffffcf0f8f

def z933 : W := mkw 0x0ffeffbe0020411f 0x007ff7fdf0010208 0xefffffff0060c002 0x7f7ffffff8030600

def z934 : W := mkw 0x0a3ed4be4160515f 0x0851f6a5f20b028a 0xfe7fffffc1e1f1fb 0xfff3fffffe0f0f8f

def z935 : W := mkw 0x0ffeffbee564515f 0xc87ff7fdf72b228a 0xffffffffc666f002 0x7ffffffffe333780

def z936 : W := mkw 0x423854b24162515a 0x0a11c2a5920b128a 0xf638fc38c1e7f1fb 0xd7b1c7e1c60f3f8f

def z937 : W := mkw 0x0ffeffbeed41385f 0xb87ff7fdf76a09c2 0xfffffffff9813061 0x7fffffffffcc0983

def z938 : W := mkw 0x080ed0ae00000017 0x0040768570000000 0xa85fd3e700000000 0x7d42fe9f38000000

def z939 : W := mkw 0x400850e3022ad7d2 0x0a004287181156be 0xa058d3e7067ffffe 0xfd02c69f3833ffff

def z940 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0x5fa73fffc181f1f1 0x42fd39fffe0c0f8f

def z941 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a73e3f3999fffd 0xfb4d39f1f9cccfff

def z942 : W := mkw 0x400040c3020a8682 0x0200020618105434 0xa058c3e7067e0f9e 0xfd02c61f3833f07c

def z943 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x57803fc0fe01fe17 0xc2bc01fe07f00ff0

def z944 : W := mkw 0x0abeffbe0000001f 0x0055f7fdf0000000 0x69bfffff00000000 0x7b4dfffff8000000

def z945 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc181f1f1 0x7ffffffffe0c0f8f

def z946 : W := mkw 0x0ffeffbee544001f 0xc07ff7fdf72a2000 0xffffffffc7e6000b 0xfffffffffe3f3000

def z947 : W := mkw 0x0dc6ef9e0000000f 0x006e377cf0000000 0x09c7efdf00000000 0x284e3f7ef8000000

def z948 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7e03fd8ff81fe77 0xcfbf01fec7fc0ff3

def z949 : W := mkw 0x0abeffbe0000001f 0x0055f7fdf0000000 0x08273fff00000000 0x404139fff8000000

def z950 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6383e3fc1e1f1fb 0xffb1c1f1fe0f0f8f

def z951 : W := mkw 0x0ffeffbe4140001f 0x007ff7fdf20a0000 0xffffffffc0600002 0x7ffffffffe030000

def z952 : W := mkw 0x023854b24160515a 0x0811c2a5920b028a 0xf6383fffc1e1f1fb 0xd7b1c1fffe0f0f8f

def z953 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xcfffffff00000000 0x467ffffff8000000

def z954 : W := mkw 0x0aba7fbe4160515f 0x0855d3fdf20b028a 0xffbf3fffc1e1f1fb 0xfffdf9fffe0f0f8f

def z955 : W := mkw 0x0230041041605148 0x08118020820b028a 0xf6382c18c1e1f1fb 0x97b1c160c60f0f8f

def z956 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xd6383c38c1e1f1f3 0x46b1c1e1c60f0f8f

def z957 : W := mkw 0xc5c36bcfbe9baea6 0xb62e1b5e7df4dd75 0x09c7c3c73e1e0e04 0x284e3e1e39f0f070

def z958 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d3e7067ecf9a 0x7402c69f3833f67c

def z959 : W := mkw 0x0230041041605148 0x08118020820b028a 0x56202c18c181f1f1 0x02b10160c60c0f8f

def z960 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7223f39990ff9 0x724d3911f9ccc87f

def z961 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff0060000a 0xff7ffffff8030000

def z962 : W := mkw 0x0dc6ab4cae01ac05 0xb06e355a65700d60 0xffc73fc0fe01fe17 0xcffe39fe07f00ff0

def z963 : W := mkw 0x0008143000205158 0x080040a18001028a 0xf6203c38c181f1fb 0xd7b101e1c60c0f8f

def z964 : W := mkw 0x0ff6eb8ee5440007 0xc07fb75c772a2000 0x9fdfc3c7c6660002 0x2cfefe1e3e333000

def z965 : W := mkw 0x05ca7bae00000016 0x002e53dd70000000 0xefffffff00000000 0x7f7ffffff8000000

def z966 : W := mkw 0x8ffeffbe0801083f 0x247ff7fdf0400841 0xefffffff00010060 0x7f7ffffff8000803

def z967 : W := mkw 0x0ffeffbe4140105f 0x087ff7fdf20a0082 0xffffffffc18131f9 0xfffffffffe0c098f

def z968 : W := mkw 0x07758410f5d40008 0xc03bac2087aea000 0xffffec18fffe000f 0xbfffff60c7fff000

def z969 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x098703c700000000 0x004c381e38000000

def z970 : W := mkw 0x400040c3020a8682 0x0200020618105434 0xa058d3c7067ece1e 0xfd02c69e3833f670

def z971 : W := mkw 0x0ff6ef9e0000000f 0x007fb77cf0000000 0xefffefdf00000000 0x3f7fff7ef8000000

def z972 : W := mkw 0x0ff6ef9e0000000f 0x007fb77cf0000000 0x0fc7cfc700000000 0x287e3e7e38000000

def z973 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff0000c012 0xff7ffffff8000600

def z974 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x8fffdfff00000000 0x3c7ffefff8000000

def z975 : W := mkw 0x0ffeffbea400001f 0x807ff7fdf5200000 0xffffffffc6000002 0x7ffffffffe300000

def z976 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x29a7023f39980ffc 0xf94d3811f9ccc07f

def z977 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x4fc7efc700000000 0x2a7e3f7e38000000

def z978 : W := mkw 0x0ffeffbe4140001f 0x007ff7fdf20a0000 0xefffffff01e00008 0x7f7ffffff80f0000

def z979 : W := mkw 0x0ff6ef9e0000000f 0x007fb77cf0000000 0xefe7ffdf00000000 0x6f7f3ffef8000000

def z980 : W := mkw 0x05400040a6008400 0x802a000205300420 0xf7c03fc0fe01fe17 0xcfbe01fe07f00ff0

def z981 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7223f39990ffd 0xc24d3911f9ccc87f

def z982 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xe9ffd3e7067ecf9e 0xff4ffe9f3833f67c

def z983 : W := mkw 0x0ff7af1cfdd5280d 0xf07fbd78e7eea940 0x5fa72c18f9813001 0x02fd3960c7cc0980

def z984 : W := mkw 0x0a3ed4be0000001f 0x0051f6a5f0000000 0xee7fffff00000000 0x7f73fffff8000000

def z985 : W := mkw 0x077cd4b20000001a 0x003be6a590000000 0xefffffff00000000 0x7f7ffffff8000000

def z986 : W := mkw 0x0a3ed4be0000001f 0x0051f6a5f0000000 0x887fd1ff00000000 0x3443fe8ff8000000

def z987 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xe078d3e707fecf9f 0xff03c69f383ff67c

def z988 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x69e7e3ff018101f9 0xfb4f3f1ff80c080f

def z989 : W := mkw 0x0f7eddbe0000001f 0x007bf6edf0000000 0xefffddff00000000 0x3f7ffeeff8000000

def z990 : W := mkw 0x000a50ae00000016 0x0000528570000000 0xa87fd3ff00000000 0x7d43fe9ff8000000

def z991 : W := mkw 0x0dceffbe0000001f 0x006e77fdf0000000 0xa9dfffff00000000 0x7d4efffff8000000

def z992 : W := mkw 0x0f7eddbe0000001f 0x007bf6edf0000000 0x8e5fddc700000000 0x2472feee38000000

def z993 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xcfffffdf00000000 0x2e7ffffef8000000

def z994 : W := mkw 0x05458000b4940000 0xc02a2c0005a4a000 0x09dfc0003e7e000c 0x384efe0001f3f000

def z995 : W := mkw 0x0ffeffbe0020515f 0x087ff7fdf001028a 0xefffffff000001e0 0x7f7ffffff800000f

def z996 : W := mkw 0x0000004102088680 0x0000000208104434 0xa058d3e7067ecf9e 0xfd02c69f3833f67c

def z997 : W := mkw 0x008a72ae00204116 0x0004539570010208 0xe9fff3ff01e1c1fb 0xff4fff9ff80f0e0f

def z998 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7223f39980fec 0x7b4d3911f9ccc07f

def z999 : W := mkw 0x07758410f5d41048 0xc83bac2087aea082 0xffffcc00fffe300f 0xbffffe6007fff180

def z1000 : W := mkw 0x000850e202008412 0x0000428710100420 0xa058d3e7067ece1e 0xfd02c69f3833f670

def z1001 : W := mkw 0x80010041ffddaea0 0xf40008020ffeed75 0x10000000ffffffff 0x8080000007ffffff

def z1002 : W := mkw 0x400854f3022ad7da 0x0a0042a7981156be 0xe078ffff07ffffff 0xff03c7fff83fffff

def z1003 : W := mkw 0x0dc6eb8ea4000007 0x806e375c75200000 0xffc7c3c7fe000007 0xaffe3e1e3ff00000

def z1004 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xb7c01fc0fe00fe16 0xcdbe00fe07f007f0

def z1005 : W := mkw 0x000850a300080292 0x0000428518004014 0xa058d3e7067e0f9e 0xfd02c69f3833f07c

def z1006 : W := mkw 0x05400940a600a400 0x902a004a05300520 0xf7c01fc0fe00fe17 0xcfbe00fe07f007f0

def z1007 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x7fa72e3ff9993ffd 0xfbfd3971ffccc9ff

def z1008 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x6fa73fff00000000 0x7b7d39fff8000000

def z1009 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69bfe23f39ff0ffd 0xfb4dff11f9cff87f

def z1010 : W := mkw 0x4ffeffbe0022411f 0x027ff7fdf0011208 0xefffffff00660000 0x7f7ffffff8033000

def z1011 : W := mkw 0x088a7fbe0000001f 0x004453fdf0000000 0x08273fff00000000 0x704139fff8000000

def z1012 : W := mkw 0x400040c3022ac782 0x020002061811563c 0xa058c3c7067ecf9e 0xbd02c61e3833f67c

def z1013 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03ff8fe01fff7 0xcfbe01ffc7f00fff

def z1014 : W := mkw 0x0a3ed4be4160515f 0x0851f6a5f20b028a 0xa87fd3ff01e0c1fa 0xfd43fe9ff80f060f

def z1015 : W := mkw 0xc08a76ff0a2bdffe 0x2e0453b7f8515eff 0x00003fff0001fff0 0x400001fff8000fff

def z1016 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffe018ffff006f 0xbfffff00c7fff803

def z1017 : W := mkw 0x00802b40ae01ac00 0xb004015a05700d60 0xf6003fc0fe01fe17 0xc7b001fe07f00ff0

def z1018 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d3c7067ecf9e 0xac02c69e3833f67c

def z1019 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x96383c38c1e1f1fa 0x54b1c1e1c60f0f8f

def z1020 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x8fc7dfc700000000 0x2c7e3efe38000000

def z1021 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x96403fc0fe01fe17 0xc4b201fe07f00ff0

def z1022 : W := mkw 0x0abef6be0000001f 0x0055f7b5f0000000 0xe9fff3ff00000000 0x7f4fff9ff8000000

def z1023 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x8fdfffff00000000 0x6c7efffff8000000

def z1024 : W := mkw 0x80010041be99aea0 0xb40008020df4cd75 0x000000003e180e04 0x0000000001f0c070

def z1025 : W := mkw 0x0dceffbe0000001f 0x006e77fdf0000000 0x69e7ffff00000000 0x7b4f3ffff8000000

def z1026 : W := mkw 0x0ff6af1c0000000d 0x007fb578e0000000 0xefe73fff00000000 0x7f7f39fff8000000

def z1027 : W := mkw 0x07758410f5d41048 0xc83bac2087aea082 0xffffec38ffff31ff 0xffffff61c7fff98f

def z1028 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefdfffc700000000 0x6f7efffe38000000

def z1029 : W := mkw 0x088a7fbe0020515f 0x084453fdf001028a 0x69a73fff0181f1f9 0xfb4d39fff80c0f8f

def z1030 : W := mkw 0x0ffeffbee544001f 0xc07ff7fdf72a2000 0xfffffffffe660007 0xfffffffffff33000

def z1031 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xd7c03fc0fe01fe13 0x46be01fe07f00ff0

def z1032 : W := mkw 0x0ffeffbee544001f 0xc07ff7fdf72a2000 0xffffffffc0000000 0x7ffffffffe000000

def z1033 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf7b83c38f9e1f1ff 0xdfbdc1e1c7cf0f8f

def z1034 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefe73fff00000000 0x4f7f39fff8000000

def z1035 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc000fffff01f 0xbffffe0007ffff80

def z1036 : W := mkw 0x07758410f5d41048 0xc83bac2087aea082 0xffffc018fffe006f 0xbffffe00c7fff003

def z1037 : W := mkw 0x0ffeffbee560515f 0x887ff7fdf72b028a 0xffffffffffe1f1ff 0xffffffffffff0f8f

def z1038 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xffa7223ff9990fff 0xfffd3911ffccc87f

def z1039 : W := mkw 0x0ffeffbeac01281f 0xb07ff7fdf5600940 0xfffffffff801f013 0xffffffffffc00f80

def z1040 : W := mkw 0x4001004112bac780 0x020008020895d63c 0x000000003ffecf9f 0x8000000001fff67c

def z1041 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xd7c03dc0fe01fe17 0x86be01ee07f00ff0

def z1042 : W := mkw 0x0dceffbe0000001f 0x006e77fdf0000000 0xefc7ffff00000000 0x6f7e3ffff8000000

def z1043 : W := mkw 0x023c943041605158 0x0811e4a1820b028a 0xfe3ffc38c1e1f1fb 0xf7f1ffe1c60f0f8f

def z1044 : W := mkw 0x400040c3020a8682 0x0200020618105434 0x8058c3c7067e0e06 0x2c02c61e3833f070

def z1045 : W := mkw 0x0008102000204110 0x0000408100010208 0xf6383c38c1e1f1fb 0xd7b1c1e1c60f0f8f

def z1046 : W := mkw 0x07758000f5d41040 0xc83bac0007aea082 0xffffc000ffff306f 0xbffffe0007fff983

def z1047 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fc0fe7ffe1f 0xcfbe01fe07f3fff0

def z1048 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7223f39810ff1 0x7b4d3911f9cc087f

def z1049 : W := mkw 0x0ffeffbe0020515f 0x087ff7fdf001028a 0xffffffffc001f1f3 0xfffffffffe000f8f

def z1050 : W := mkw 0x0dc6eb8ea4040007 0xc06e375c75202000 0x09c7c3c706060000 0x284e3e1e38303000

def z1051 : W := mkw 0x0ffeffbe0801081f 0x207ff7fdf0400840 0xefffffff39810ffd 0xff7ffffff9cc087f

def z1052 : W := mkw 0x400850e3020a8692 0x0200428718105434 0xa058d3e7067e0e0e 0xfd02c69f3833f070

def z1053 : W := mkw 0x0ff6ef9e0000000f 0x007fb77cf0000000 0x6fe7efff00000000 0x7b7f3f7ff8000000

def z1054 : W := mkw 0x023cd0a200000012 0x0011e68510000000 0xa87fd3e700000000 0x7d43fe9f38000000

def z1055 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x56383c38c1e1f1f9 0x52b1c1e1c60f0f8f

def z1056 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc1e131e9 0x7ffffffffe0f098f

def z1057 : W := mkw 0x400854f3022ad7da 0x0a0042a7981156be 0xa058d3ff067ecffe 0xfd02c69ff833f67f

def z1058 : W := mkw 0x423dd4b351fe53da 0x4a11eea59a8ff29e 0x083fc03f01fe01e8 0x3041fe01f80ff00f

def z1059 : W := mkw 0x0082220c08010804 0x2004111060400840 0x69a7223f39810ffd 0xfb4d3911f9cc087f

def z1060 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x8e7fffff00000000 0x7473fffff8000000

def z1061 : W := mkw 0x02ba76be4160515e 0x0815d3b5f20b028a 0xffffffffc1e1f1fb 0xfffffffffe0f0f8f

def z1062 : W := mkw 0x0774c08200000002 0x003ba60410000000 0xefffc3c700000000 0x3f7ffe1e38000000

def z1063 : W := mkw 0x0ffeffbea400001f 0x807ff7fdf5200000 0xfffffffffe7e000f 0xfffffffffff3f000

def z1064 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff000101f0 0x7f7ffffff800080f

def z1065 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69a7223f39810ff5 0xcb4d3911f9cc087f

def z1066 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d3e7067ecf96 0x6c02c69f3833f67c

def z1067 : W := mkw 0x05c02b0008010800 0x202e015800400840 0xf7c03fc0f801fe17 0xcfbe01fe07c00ff0

def z1068 : W := mkw 0x0f7eddbe0000001f 0x007bf6edf0000000 0xee7ffdff00000000 0x7773ffeff8000000

def z1069 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x4fe7ffff00000000 0x6a7f3ffff8000000

def z1070 : W := mkw 0x0ffeffbe0020411f 0x007ff7fdf0010208 0xefffffff067ec19e 0xff7ffffff833f60c

def z1071 : W := mkw 0x008a72ae00000016 0x0004539570000000 0xa9dfd3e700000000 0x7d4efe9f38000000

def z1072 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x69ffc0003ffe000d 0xbb4ffe0001fff000

def z1073 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff061e0004 0x7f7ffffff830f000

def z1074 : W := mkw 0x0abeffbe0000001f 0x0055f7fdf0000000 0xa87fffff00000000 0x7d43fffff8000000

def z1075 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058f3ff067fcffe 0xfd02c79ff833fe7f

def z1076 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff00000e14 0xff7ffffff8000070

def z1077 : W := mkw 0x0a3ed4be0000001f 0x0051f6a5f0000000 0x083fd3ff00000000 0x7041fe9ff8000000

def z1078 : W := mkw 0x0775800010900000 0x003bac0000848000 0xefffc0003ffe000f 0xbf7ffe0001fff000

def z1079 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x8058d3e7067ecf8e 0x3c02c69f3833f67c

def z1080 : W := mkw 0x054cd0a200000012 0x002a668510000000 0xa9dfd3e700000000 0x7d4efe9f38000000

def z1081 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x97c01fc0fe01fe17 0x8cbe00fe07f00ff0

def z1082 : W := mkw 0x0ffeffbe4961595f 0x287ff7fdf24b0aca 0xfffffffff9e1ffff 0xffffffffffcf0fff

def z1083 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xbfdfc000fe7e000e 0xbdfefe0007f3f000

def z1084 : W := mkw 0x0ffeffbe0020515f 0x087ff7fdf001028a 0xefffffff0181f1f9 0xff7ffffff80c0f8f

def z1085 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0xffc7ffc7c001f013 0xeffe3ffe3e000f80

def z1086 : W := mkw 0x0abeffbe0000001f 0x0055f7fdf0000000 0x083fc3ff00000000 0x3041fe1ff8000000

def z1087 : W := mkw 0xc00100411a9b8ea0 0x2600080208d4dc75 0x000000003e1e0e04 0x0000000001f0f070

def z1088 : W := mkw 0x0dceffbe0000001f 0x006e77fdf0000000 0x09c7dfc700000000 0x284e3efe38000000

def z1089 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x09a7023f39990ffd 0xb84d3811f9ccc87f

def z1090 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x69e7e23f3f9f0ffd 0xfb4f3f11f9fcf87f

def z1091 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6383e38c1e1ffff 0xdfb1c1f1c60f0fff

def z1092 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058c3e7067e0f8e 0xbd02c61f3833f07c

def z1093 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff0018000c 0xff7ffffff800c000

def z1094 : W := mkw 0x400040c3020a8682 0x0200020618105434 0x0058c3c7067e0e0c 0x3802c61e3833f070

def z1095 : W := mkw 0x0230041041401048 0x08118020820a0082 0xf6203c38c181f1fb 0xd7b101e1c60c0f8f

def z1096 : W := mkw 0x05c22b0c00000004 0x002e115860000000 0xffe73fffc181f1fb 0xffff39fffe0c0f8f

def z1097 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xffffffffc181f1fb 0xfffffffffe0c0f8f

def z1098 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0x09ffc3ff01e001e8 0x384ffe1ff80f000f

def z1099 : W := mkw 0x0ffeffbea400001f 0x807ff7fdf5200000 0xefffffff3e000004 0x7f7ffffff9f00000

def z1100 : W := mkw 0x80832b0d18990aa4 0x2404195868c4c855 0x69a73fff39990ffd 0xfb4d39fff9ccc87f

def z1101 : W := mkw 0x0f7cddb20000001b 0x007be6ed90000000 0xefffdfe700000000 0x7f7ffeff38000000

def z1102 : W := mkw 0x80010041fff9ffe0 0xbc0008020fffcfff 0x10000000fff9ffff 0x8080000007ffcfff

def z1103 : W := mkw 0x40010041f7fed7c0 0xca0008020fbff6be 0x10000000ffffffff 0x8080000007ffffff

def z1104 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf6383c38c181f1f1 0x57b1c1e1c60c0f8f

def z1105 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xf678fc38c7e7f1fb 0xd7b3c7e1c63f3f8f

def z1106 : W := mkw 0x0f758d10f5d40009 0xc07bac6887aea000 0xffffcc00fffe000f 0xbffffe6007fff000

def z1107 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7223f39990fed 0x3a4d3911f9ccc87f

def z1108 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0xefe7ffff00000000 0x7f7f3ffff8000000

def z1109 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xe9bf223f39f90fff 0xff4df911f9cfc87f

def z1110 : W := mkw 0x05458000f5d40000 0xc02a2c0007aea000 0xb9dfc000fffe000f 0xbdcefe0007fff000

def z1111 : W := mkw 0x077cd0a241604112 0x003be685120b0208 0xffffd3e7c1e0c19b 0xfffffe9f3e0f060c

def z1112 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xe9a7323f3999cfff 0xff4d3991f9ccce7f

def z1113 : W := mkw 0x0ffeffbe0020411f 0x007ff7fdf0010208 0xefffffff00600188 0x7f7ffffff803000c

def z1114 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058d3c7067ece16 0xed02c69e3833f670

def z1115 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffdfc700000000 0x3f7ffefe38000000

def z1116 : W := mkw 0x088a7fbe0000001f 0x004453fdf0000000 0x09873fff00000000 0x684c39fff8000000

def z1117 : W := mkw 0x000950a2f5d40012 0xc0004a8517aea000 0xb058d3e7fffe000f 0xfd82c69f3ffff000

def z1118 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xd6383c18c1e1f1fb 0x86b1c1e0c60f0f8f

def z1119 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x0058d3e7067ecf9c 0x7802c69f3833f67c

def z1120 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffd000fffec01f 0xfffffe8007fff600

def z1121 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffd3c0fffe000f 0xfffffe9e07fff000

def z1122 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff018001e8 0x7f7ffffff80c000f

def z1123 : W := mkw 0x0ffeffbeac01281f 0xb07ff7fdf5600940 0xefffffff38000000 0x7f7ffffff9c00000

def z1124 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c01fc0fe00fe07 0x8fbe00fe07f007f0

def z1125 : W := mkw 0x0ffeffbe4140001f 0x007ff7fdf20a0000 0xffffffffc7fe000f 0xfffffffffe3ff000

def z1126 : W := mkw 0xc001004112bac7a0 0x060008020895d63d 0x0000000007fecffe 0x80000000003ff67f

def z1127 : W := mkw 0xc23914715bfbdff8 0x2e11c8a38adfdeff 0xf6383c38ffffffff 0xd7b1c1e1c7ffffff

def z1128 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0xa9dfc3c7067e000e 0xbd4efe1e3833f000

def z1129 : W := mkw 0x400850e3022ac792 0x020042871811563c 0x2058c3e7067e0f9c 0xf902c61f3833f07c

def z1130 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058d3c7067ece0e 0xbd02c69e3833f670

def z1131 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7d8ffc0fe01fe17 0xffbec7fe07f00ff0

def z1132 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xefa73e3f39990ffd 0xff7d39f1f9ccc87f

def z1133 : W := mkw 0x00802b400a01ac00 0x3004015a00500d60 0xf7803fc0f801fe17 0xcfbc01fe07c00ff0

def z1134 : W := mkw 0x8a3fd4bf51f853ff 0x0c51fea5fa8fc29f 0x083fc03f01f801e8 0x3041fe01f80fc00f

def z1135 : W := mkw 0x0ffeffbe0801081f 0x207ff7fdf0400840 0xefffffff00010e10 0x7f7ffffff8000870

def z1136 : W := mkw 0x0886eb8e00000007 0x0044375c70000000 0x0807c3c700000000 0x20403e1e38000000

def z1137 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0xffbf3c38c1e1f1fb 0xfffdf9e1c60f0f8f

def z1138 : W := mkw 0x8003000d109802a4 0x040018006884c015 0x69a7023f39980ffd 0xfb4d3811f9ccc07f

def z1139 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff06000006 0xff7ffffff8300000

def z1140 : W := mkw 0x0aba7fbe0000001f 0x0055d3fdf0000000 0xefbf3fff00000000 0x7f7df9fff8000000

def z1141 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x76203c38c181f1f9 0xd3b101e1c60c0f8f

def z1142 : W := mkw 0x0dceffbe0000001f 0x006e77fdf0000000 0x09c7c3ff00000000 0x284e3e1ff8000000

def z1143 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xefffffff01e101f9 0xff7ffffff80f080f

def z1144 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x09ffffff00000000 0x784ffffff8000000

def z1145 : W := mkw 0x07748000a4000000 0x803ba40005200000 0xffffc000fe7e000f 0xbffffe0007f3f000

def z1146 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xafdfdfe700000000 0x7d7efeff38000000

def z1147 : W := mkw 0x0ffeffbea400001f 0x807ff7fdf5200000 0xfffffffffe01f017 0xfffffffffff00f80

def z1148 : W := mkw 0x400854f3022ad7da 0x0a0042a7981156be 0xa058dfe7067eff9e 0xfd02c6ff3833f7fc

def z1149 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff00000198 0xff7ffffff800000c

def z1150 : W := mkw 0x0dcefbae00000017 0x006e77dd70000000 0xefdfffe700000000 0x7f7effff38000000

def z1151 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x97c03fc0fe01fe16 0x4cbe01fe07f00ff0

def z1152 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xf658d3e7c67ecf9f 0xffb2c69f3e33f67c

def z1153 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x5fbfc000fffe000f 0xb2fdfe0007fff000

def z1154 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc200fffe0e1f 0xfffffe1007fff070

def z1155 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xdfffc000fffe000f 0x86fffe0007fff000

def z1156 : W := mkw 0x088a7fbe0000001f 0x004453fdf0000000 0xe9ffffff00000000 0x7f4ffffff8000000

def z1157 : W := mkw 0x0001000010900000 0x0000080000848000 0xa9dfc0003e7e000e 0xbd4efe0001f3f000

def z1158 : W := mkw 0x0f7ed4be0000001f 0x007bf6a5f0000000 0xefffd3ff00000000 0x7f7ffe9ff8000000

def z1159 : W := mkw 0x0ffeffbe0020411f 0x007ff7fdf0010208 0xffffffffc061f19b 0xfffffffffe030f8c

def z1160 : W := mkw 0x05c4ab40ae05ac00 0xf02e255a05702d60 0xf7c0ffc0fe07fe17 0xcfbe07fe07f03ff0

def z1161 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058d3e7067ece06 0x7d02c69f3833f670

def z1162 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc1e001eb 0xfffffffffe0f000f

def z1163 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xffffffffc0013001 0x7ffffffffe000980

def z1164 : W := mkw 0xc00100415bfbdfe0 0x2e0008020adfdeff 0x10000000ffffffff 0x8080000007ffffff

def z1165 : W := mkw 0x0f7eddbe0000001f 0x007bf6edf0000000 0x087fc1ff00000000 0x3043fe0ff8000000

def z1166 : W := mkw 0x400854f3022ad7da 0x0a0042a7981156be 0xf658ffffc67fffff 0xffb2c7fffe33ffff

def z1167 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffc3ff00000000 0x3f7ffe1ff8000000

def z1168 : W := mkw 0x0abeffbe4160515f 0x0855f7fdf20b028a 0x083fffff01e1f1f8 0x7041fffff80f0f8f

def z1169 : W := mkw 0x0230000041400000 0x00118000020a0000 0xf6383c38c1e1f1fb 0xd7b1c1e1c60f0f8f

def z1170 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0x77803fc0f801fe15 0xcbbc01fe07c00ff0

def z1171 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa058ffe7067fff9e 0xfd02c7ff3833fffc

def z1172 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x9fffc000fffe000e 0x3cfffe0007fff000

def z1173 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0x9fdfc000fffe000f 0xacfefe0007fff000

def z1174 : W := mkw 0x0dc6eb8eac012807 0xb06e375c75600940 0x5fc7efc7f8013001 0x2afe3f7e3fc00980

def z1175 : W := mkw 0xc00100411abbcfa0 0x2600080208d5de7d 0x000000003e7ecf9e 0x8000000001f3f67c

def z1176 : W := mkw 0x85c22b4cae01ac24 0xb42e115a65700d61 0xf7c03fd8fe01fe77 0xcfbe01fec7f00ff3

def z1177 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0xe9e7223f3f990fff 0xff4f3911f9fcc87f

def z1178 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xffe73fc0fe01fe17 0xffff39fe07f00ff0

def z1179 : W := mkw 0x07fa3f3c4160515c 0x083fd1f9e20b028a 0xffff3fffc1e1f1fb 0xfffff9fffe0f0f8f

def z1180 : W := mkw 0x8ff7af1cfdd5082d 0xe47fbd78e7eea841 0x5fa72c18f9810061 0x02fd3960c7cc0803

def z1181 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7c03fc0fe00fe06 0x4fbe01fe07f007f0

def z1182 : W := mkw 0x8083220d18990aa4 0x2404191068c4c855 0x49a7223f39990ff5 0x6a4d3911f9ccc87f

def z1183 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0x9fdfdfc7c060f002 0x2cfefefe3e030780

def z1184 : W := mkw 0x80832b0d18992aa4 0x3404195868c4c955 0x69a72e3f39993ffd 0xfb4d3971f9ccc9ff

def z1185 : W := mkw 0x0dc6eb8e08010807 0x206e375c70400840 0x69c7e3c738010e15 0xeb4e3f1e39c00870

def z1186 : W := mkw 0x05c22b4cae01ac04 0xb02e115a65700d60 0xffe73fd8fe01fe17 0xcfff39fec7f00ff0

def z1187 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc000fe7e0006 0x3ffffe0007f3f000

def z1188 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x09c7ffc700000000 0x684e3ffe38000000

def z1189 : W := mkw 0x8003000d18990aa4 0x2400180068c4c855 0x69a7003f39990ffd 0xbb4d3801f9ccc87f

def z1190 : W := mkw 0xc23b54bf51fa53fe 0x0e11daa5fa8fd29f 0x083fc03f01fe01e8 0x3041fe01f80ff00f

def z1191 : W := mkw 0x023c943041645158 0x4811e4a1820b228a 0xf638fc38c1e7f1fb 0xd7b1c7e1c60f3f8f

def z1192 : W := mkw 0x0238143041605158 0x0811c0a1820b028a 0x56382c38c1e1f1fb 0x92b1c161c60f0f8f

def z1193 : W := mkw 0x400850e3022ac792 0x020042871811563c 0xa078d3ff07fecffe 0xfd03c69ff83ff67f

def z1194 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x09e7c3ff00000000 0x384f3e1ff8000000

def z1195 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xcffffdff00000000 0x367fffeff8000000

def z1196 : W := mkw 0x0ffeffbeac01281f 0xb07ff7fdf5600940 0xfffffffffe013007 0xfffffffffff00980

def z1197 : W := mkw 0x0ff6eb8e00000007 0x007fb75c70000000 0x8fdfc3c700000000 0x2c7efe1e38000000

def z1198 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffbf3fffc1e1f1fb 0xd7fdf9fffe0f0f8f

def z1199 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0x69ffe3ff00000000 0x7b4fff1ff8000000

def z1200 : W := mkw 0x4001004153fec780 0x420008020a9ff63c 0x0000000007fecf9e 0x80000000003ff67c

def z1201 : W := mkw 0x0ff6ef9e0000000f 0x007fb77cf0000000 0x09e7c3df00000000 0x284f3e1ef8000000

def z1202 : W := mkw 0x0a3ed4be0000001f 0x0051f6a5f0000000 0x087fc3ff00000000 0x3843fe1ff8000000

def z1203 : W := mkw 0x0ff6ef9e0000000f 0x007fb77cf0000000 0x4fa72fdf00000000 0x027d397ef8000000

def z1204 : W := mkw 0x07758000b4940000 0xc03bac0005a4a000 0xefffc0003e7e000e 0xbf7ffe0001f3f000

def z1205 : W := mkw 0x0d46c98e00000007 0x006a364c70000000 0x0847c1c700000000 0x20423e0e38000000

def z1206 : W := mkw 0xc88a7fff0a2bcfbf 0x264453fff8515e7d 0x00003fff0001cff0 0x400001fff8000e7f

def z1207 : W := mkw 0x0ffeffbe0020411f 0x007ff7fdf0010208 0xefffffff01e1c1fb 0xff7ffffff80f0e0f

def z1208 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x49e7e3df00000000 0x2a4f3f1ef8000000

def z1209 : W := mkw 0x0ffeffbee564515f 0xc87ff7fdf72b228a 0xffffffffc7e7f1fb 0xfffffffffe3f3f8f

def z1210 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0xefc7c3c700000000 0x2f7e3e1e38000000

def z1211 : W := mkw 0x05c02b40ae01ac00 0xb02e015a05700d60 0xf7e03fc0ff81fe1f 0xdfbf01fe07fc0ff0

def z1212 : W := mkw 0x0ffeffbe0000001f 0x007ff7fdf0000000 0xefffffff01810061 0x7f7ffffff80c0803

def z1213 : W := mkw 0x05c22b0c00000004 0x002e115860000000 0xefc73fc700000000 0x6f7e39fe38000000

def z1214 : W := mkw 0x0ff6eb8e00000007 0x007fb75c70000000 0xefffffc700000000 0x7f7ffffe38000000

def z1215 : W := mkw 0x0dc6eb8e00000007 0x006e375c70000000 0x09c7c3c7061e0004 0x284e3e1e3830f000

def z1216 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xefffc0003ffe000c 0x3f7ffe0001fff000

def z1217 : W := mkw 0x0082628e00000006 0x0004131470000000 0x69e7e3ff00000000 0x7b4f3f1ff8000000

def z1218 : W := mkw 0x0ffeffbe4160515f 0x087ff7fdf20b028a 0xffffffffc061f1f2 0x7ffffffffe030f8f

def z1219 : W := mkw 0x0dca7fbe0000001f 0x006e53fdf0000000 0xefe73fff00000000 0x7f7f39fff8000000

def z1220 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffdc00fffef00f 0xbffffee007fff780

def z1221 : W := mkw 0x07758000f5d40000 0xc03bac0007aea000 0xffffc020fffe019f 0xfffffe0107fff00c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z7,z8,z9,z5]),(0,[z0,z1,z2,z7,z10,z4,z5]),(0,[z0,z1,z11,z2,z7,z4,z5])],[(0,[z0,z1,z2,z12,z4,z13,z5]),(0,[z14,z0,z1,z2,z7,z4,z5]),(1,[z15,z0,z2,z16,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z17]),(0,[z0,z1,z2,z18,z4,z13,z5])],[(0,[z0,z1,z2,z12,z19,z4,z5]),(0,[z0,z1,z2,z7,z4,z20,z5])],[(0,[z21,z0,z22,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z23]),(0,[z0,z1,z24,z2,z7,z25,z5])],[(0,[z26,z0,z1,z2,z7,z4,z5]),(0,[z27,z0,z1,z2,z3,z4,z5]),(0,[z28,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z29,z5]),(0,[z0,z1,z2,z7,z4,z5,z30]),(0,[z0,z31,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z3,z4,z32,z5]),(0,[z33,z0,z1,z2,z7,z4,z34]),(0,[z0,z1,z35,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z36,z5]),(0,[z37,z0,z1,z2,z7,z4,z5])],[(0,[z38,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z39,z4,z5])],[(0,[z40,z0,z1,z2,z7,z4,z5]),(0,[z41,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z42,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z3,z43,z4,z5]),(0,[z15,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z44,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z5]),(0,[z45,z0,z1,z2,z7,z4,z5]),(0,[z46,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z47,z4,z5]),(0,[z48,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z49,z7,z4,z5]),(0,[z0,z1,z2,z7,z50,z4,z5])],[(0,[z1,z2,z3,z7,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z51,z5]),(0,[z52,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z53,z7,z4,z5])],[(0,[z0,z1,z2,z54,z7,z4,z5]),(0,[z0,z1,z2,z55,z7,z4,z5]),(0,[z56,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z57,z4,z5]),(0,[z0,z1,z58,z2,z7,z4,z5])],[(0,[z0,z1,z2,z59,z7,z4,z5]),(0,[z0,z1,z24,z2,z7,z60,z5]),(0,[z0,z1,z2,z7,z61,z4,z5]),(0,[z0,z1,z2,z7,z4,z62,z5]),(0,[z15,z0,z63,z2,z7,z4,z5]),(0,[z0,z64,z1,z2,z7,z4,z5])],[(0,[z0,z1,z65,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z60,z4,z5]),(0,[z0,z1,z2,z66,z43,z4,z5]),(0,[z0,z1,z2,z67,z7,z4,z5])],[(0,[z0,z1,z2,z3,z12,z4,z5]),(0,[z68,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z69,z7,z4,z5]),(0,[z41,z70,z1,z2,z7,z4,z5])],[(0,[z71,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z72,z4,z5]),(0,[z73,z0,z1,z2,z7,z4,z5]),(0,[z74,z0,z2,z75,z7,z4,z5]),(0,[z0,z1,z2,z76,z7,z4,z5]),(0,[z0,z1,z77,z2,z7,z4,z5]),(0,[z78,z0,z1,z2,z7,z4,z5])],[(0,[z0,z79,z1,z2,z7,z4,z5]),(0,[z80,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z12,z81,z4,z5]),(0,[z0,z1,z2,z7,z60,z8,z5]),(0,[z0,z1,z2,z7,z82,z4,z5])]],
   [[(1,[z0,z1,z2,z83,z4,z5]),(0,[z84,z0,z1,z2,z7,z4,z5]),(1,[z0,z85,z1,z7,z4,z5])],[(0,[z86,z87,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z88,z12,z4,z5]),(0,[z0,z1,z2,z12,z4,z5,z89]),(0,[z0,z1,z2,z66,z12,z4,z5]),(0,[z0,z90,z1,z2,z3,z4,z5]),(0,[z91,z0,z1,z2,z7,z4,z5]),(0,[z0,z2,z16,z7,z43,z4,z5]),(0,[z0,z1,z2,z92,z7,z4,z5]),(0,[z93,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z24,z2,z7,z94,z5])],[(0,[z95,z0,z1,z2,z7,z4,z5]),(0,[z96,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z97,z5])],[(0,[z0,z1,z2,z12,z4,z9,z5]),(0,[z0,z1,z2,z7,z4,z98,z5]),(0,[z0,z1,z2,z99,z7,z4,z5]),(0,[z100,z0,z1,z2,z18,z4,z5]),(1,[z0,z1,z7,z4,z5,z101])],[(0,[z71,z0,z102,z1,z7,z4,z5]),(0,[z0,z1,z2,z7,z103,z4,z5]),(0,[z74,z0,z102,z1,z7,z4,z5])],[(0,[z0,z1,z2,z104,z7,z4,z5]),(0,[z105,z0,z1,z2,z7,z4,z5]),(0,[z0,z106,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z43,z4,z5,z17]),(0,[z41,z0,z1,z2,z4,z97,z5])],[(0,[z0,z1,z2,z7,z4,z5,z107]),(0,[z0,z1,z2,z108,z12,z4,z5]),(0,[z0,z1,z2,z3,z109,z4,z5]),(0,[z0,z1,z110,z2,z7,z4,z5]),(0,[z0,z63,z2,z7,z43,z4,z5]),(0,[z111,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z112,z4,z5]),(0,[z113,z0,z1,z2,z7,z4,z5]),(0,[z0,z114,z1,z2,z7,z4,z5])],[(0,[z0,z115,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z75,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z116,z5]),(0,[z0,z1,z2,z117,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z118,z5]),(0,[z119,z41,z0,z1,z2,z4,z5]),(0,[z0,z120,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z121])]],
   [[(0,[z119,z0,z1,z2,z12,z4,z5]),(0,[z0,z122,z1,z2,z7,z4,z5]),(0,[z123,z0,z1,z2,z7,z4,z5])],[(0,[z124,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z125,z4,z5]),(0,[z126,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z127,z5])],[(0,[z128,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z129,z2,z7,z4,z5]),(0,[z0,z1,z130,z2,z66,z4,z5]),(0,[z0,z1,z2,z7,z4,z131,z5]),(0,[z0,z1,z58,z2,z7,z4,z132])],[(0,[z71,z0,z1,z133,z7,z4,z5]),(0,[z74,z0,z1,z133,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z134,z5]),(1,[z21,z1,z2,z7,z4,z34]),(1,[z0,z135,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z13,z5])],[(0,[z0,z1,z2,z7,z19,z4,z5]),(0,[z0,z136,z1,z2,z7,z4,z5]),(0,[z137,z0,z1,z2,z7,z4,z5]),(0,[z138,z0,z1,z2,z7,z4,z139])],[(0,[z0,z1,z2,z7,z4,z140,z5]),(0,[z0,z141,z1,z2,z7,z4,z5]),(1,[z0,z63,z2,z7,z4,z142]),(0,[z0,z1,z2,z7,z4,z5,z143])],[(0,[z0,z1,z2,z144,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z145,z5]),(0,[z0,z1,z2,z7,z4,z5,z146]),(0,[z147,z0,z1,z2,z7,z8,z5]),(0,[z41,z0,z1,z2,z7,z97,z5]),(0,[z41,z0,z1,z2,z4,z13,z5]),(0,[z0,z1,z2,z7,z4,z148,z5]),(0,[z0,z1,z2,z149,z7,z4,z5])],[(0,[z86,z0,z1,z2,z3,z4,z5]),(0,[z80,z0,z1,z2,z7,z150,z5]),(0,[z0,z1,z2,z7,z4,z151,z5]),(0,[z0,z1,z2,z3,z53,z4,z5]),(1,[z0,z152,z75,z7,z4,z5]),(0,[z0,z1,z2,z153,z7,z4,z5]),(0,[z0,z154,z1,z2,z7,z4,z5]),(0,[z15,z0,z1,z2,z4,z13,z5])]],
   [[(0,[z1,z2,z133,z7,z4,z9,z5]),(0,[z155,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z156,z3,z4,z5]),(0,[z0,z1,z130,z2,z81,z4,z5]),(0,[z157,z27,z0,z1,z7,z4,z5])],[(0,[z74,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z158,z4,z5]),(0,[z159,z0,z1,z2,z7,z4,z5]),(0,[z74,z0,z152,z1,z7,z4,z5]),(0,[z160,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z161,z5])],[(0,[z0,z1,z2,z162,z7,z4,z5]),(0,[z0,z1,z2,z163,z7,z4,z5]),(0,[z0,z1,z7,z94,z4,z25,z5]),(0,[z0,z1,z2,z7,z4,z5,z164])],[(0,[z165,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z66,z53,z4,z5])],[(0,[z0,z1,z2,z7,z150,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z166]),(1,[z0,z1,z2,z167,z4,z5])],[(0,[z0,z1,z2,z168,z7,z4,z5]),(0,[z0,z1,z2,z169,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z170,z5]),(0,[z0,z171,z1,z2,z7,z4,z5])],[(0,[z0,z172,z1,z2,z7,z4,z5]),(0,[z0,z102,z1,z75,z7,z4,z5]),(1,[z173,z74,z0,z7,z4,z5]),(0,[z174,z0,z1,z2,z7,z4,z5]),(1,[z119,z0,z1,z66,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z175])],[(1,[z0,z1,z2,z176,z4,z5]),(1,[z177,z1,z2,z7,z9,z5]),(0,[z147,z0,z2,z7,z4,z178,z5]),(0,[z179,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z180,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z181,z5]),(0,[z0,z1,z2,z7,z182,z4,z5])]],
   [[(0,[z128,z0,z1,z183,z7,z4,z5]),(0,[z184,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z65,z2,z7,z4,z5]),(0,[z0,z152,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z185,z7,z4,z5])],[(0,[z0,z1,z2,z3,z7,z4,z5]),(0,[z177,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z81,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z186])],[(0,[z187,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z188,z2,z7,z4,z5]),(1,[z0,z189,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z190,z4,z5]),(0,[z0,z191,z1,z2,z7,z4,z5])],[(0,[z80,z0,z1,z2,z7,z4,z5]),(0,[z157,z0,z1,z2,z7,z9,z5]),(1,[z0,z1,z192,z7,z4,z5]),(0,[z193,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z89])],[(0,[z0,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z194]),(0,[z80,z1,z2,z7,z4,z9,z5]),(0,[z0,z152,z1,z2,z195,z4,z5]),(0,[z0,z1,z2,z7,z196,z4,z5]),(1,[z0,z1,z2,z197,z4,z5]),(0,[z0,z1,z2,z198,z7,z4,z5]),(0,[z0,z1,z2,z7,z199,z4,z5]),(1,[z100,z0,z1,z2,z4,z17])],[(0,[z200,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z201,z7,z4,z5]),(0,[z0,z1,z2,z12,z4,z132,z5]),(0,[z0,z1,z2,z88,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z9,z5]),(1,[z0,z1,z2,z202,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z203]),(1,[z0,z1,z2,z195,z4,z5]),(0,[z0,z1,z2,z66,z7,z4,z5]),(0,[z0,z1,z58,z2,z7,z4,z89]),(0,[z204,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z12,z4,z205,z5]),(0,[z0,z1,z2,z206,z7,z4,z5]),(0,[z0,z207,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z208,z7,z4,z5]),(0,[z0,z1,z209,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z210])],[(0,[z0,z1,z2,z7,z4,z211,z5])]],
   [[(0,[z0,z2,z212,z7,z4,z5,z139]),(0,[z213,z0,z1,z2,z7,z4,z5]),(1,[z27,z0,z1,z7,z4,z89])],[(0,[z0,z1,z2,z7,z4,z214,z5]),(0,[z215,z1,z2,z7,z4,z5,z139])],[(0,[z0,z1,z2,z12,z4,z5,z216]),(0,[z0,z1,z2,z108,z7,z4,z5]),(0,[z0,z1,z2,z16,z4,z5,z17]),(0,[z0,z1,z217,z2,z7,z4,z5]),(0,[z0,z63,z1,z2,z7,z4,z139]),(1,[z157,z0,z1,z7,z25,z5]),(0,[z0,z1,z2,z7,z4,z5,z218]),(0,[z100,z0,z1,z2,z109,z4,z5])],[(0,[z0,z1,z2,z133,z12,z4,z5]),(0,[z84,z1,z2,z133,z7,z4,z5]),(0,[z0,z1,z2,z7,z219,z4,z5]),(0,[z0,z63,z1,z2,z7,z4,z142]),(0,[z0,z1,z2,z220,z7,z4,z5])],[(0,[z0,z221,z1,z2,z7,z4,z5]),(0,[z138,z0,z1,z2,z3,z4,z5]),(0,[z222,z0,z1,z2,z7,z4,z5]),(0,[z119,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z58,z2,z223,z4,z5])],[(0,[z0,z1,z2,z3,z224,z4,z5]),(0,[z0,z1,z2,z16,z3,z4,z5]),(0,[z21,z0,z1,z192,z7,z4,z5]),(0,[z0,z1,z2,z7,z225,z4,z5]),(0,[z100,z0,z209,z2,z7,z4,z5])],[(0,[z128,z1,z2,z7,z4,z205,z5]),(0,[z226,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z8,z4,z5]),(0,[z227,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z228,z4,z5]),(0,[z0,z1,z2,z7,z4,z229,z5]),(0,[z0,z1,z2,z230,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z231,z5])],[(0,[z128,z0,z1,z2,z232,z4,z5]),(1,[z0,z1,z2,z144,z4,z5]),(0,[z0,z1,z2,z12,z4,z5,z233]),(0,[z21,z0,z1,z2,z202,z4,z5]),(0,[z33,z0,z1,z2,z7,z4,z205])]],
   [[(0,[z234,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z235,z5])],[(0,[z0,z1,z2,z3,z94,z4,z5]),(0,[z236,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z237]),(0,[z0,z238,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z212,z3,z4,z5]),(0,[z0,z1,z2,z239,z7,z4,z5]),(0,[z240,z0,z1,z2,z7,z4,z5]),(0,[z241,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z242,z7,z4,z5]),(0,[z0,z1,z2,z243,z7,z4,z5])],[(0,[z0,z1,z2,z12,z43,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z244]),(0,[z0,z245,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z246,z4,z5]),(0,[z0,z1,z2,z247,z7,z4,z5])],[(0,[z0,z248,z1,z2,z7,z4,z5]),(0,[z249,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z250,z5]),(0,[z84,z1,z2,z7,z60,z4,z5]),(0,[z21,z1,z2,z7,z4,z5,z34]),(0,[z251,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z43,z81,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z252]),(0,[z0,z1,z2,z7,z4,z5,z253]),(1,[z0,z1,z2,z254,z4,z5])],[(0,[z0,z1,z1,z2,z7,z4,z5]),(0,[z84,z1,z2,z7,z12,z4,z5]),(0,[z255,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z256,z5]),(0,[z0,z1,z2,z7,z4,z257,z5])],[(0,[z0,z1,z2,z12,z60,z4,z5]),(1,[z0,z1,z2,z258,z4,z5]),(0,[z0,z1,z2,z259,z7,z4,z5]),(0,[z0,z260,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z261,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z12,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z262,z5]),(0,[z0,z1,z2,z7,z263,z4,z5])],[(0,[z264,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z265,z4,z5])],[(0,[z157,z0,z102,z1,z7,z4,z5]),(1,[z0,z1,z2,z54,z4,z5])],[(0,[z0,z1,z2,z7,z266,z4,z5]),(0,[z267,z0,z1,z2,z3,z4,z5]),(0,[z268,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z269,z4,z5]),(0,[z0,z1,z2,z7,z4,z270,z5]),(0,[z0,z1,z2,z4,z36,z5,z139]),(0,[z0,z271,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z176,z4,z5]),(0,[z100,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z133,z7,z4,z5,z89]),(0,[z21,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z272,z5]),(0,[z0,z1,z2,z7,z4,z273,z5]),(0,[z274,z0,z1,z2,z7,z4,z5]),(0,[z275,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z183,z2,z7,z4,z5]),(0,[z0,z276,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z132,z5])]],
   [[(0,[z277,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z205,z5]),(0,[z0,z278,z1,z2,z7,z4,z5]),(0,[z27,z0,z1,z7,z94,z4,z5]),(0,[z0,z1,z2,z7,z4,z279,z5])],[(0,[z87,z1,z2,z7,z4,z205,z5]),(0,[z157,z0,z1,z133,z7,z4,z5]),(0,[z280,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z281,z4,z5]),(0,[z33,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z24,z2,z7,z4,z5]),(0,[z0,z1,z2,z282,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z283])],[(0,[z284,z0,z1,z2,z12,z4,z5]),(0,[z0,z63,z1,z2,z3,z4,z5]),(0,[z285,z0,z1,z2,z7,z4,z5]),(0,[z84,z0,z1,z2,z7,z9,z5]),(0,[z0,z1,z2,z7,z4,z5,z286]),(0,[z0,z1,z2,z287,z7,z4,z5])],[(0,[z86,z0,z87,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z202,z4,z5]),(0,[z0,z1,z2,z7,z195,z4,z5]),(0,[z0,z1,z288,z2,z7,z4,z5])],[(0,[z128,z0,z1,z2,z83,z4,z5]),(1,[z71,z1,z133,z7,z4,z5]),(0,[z147,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z216]),(0,[z14,z0,z1,z2,z3,z4,z5]),(0,[z289,z0,z1,z2,z7,z4,z5])],[(0,[z0,z87,z1,z2,z12,z4,z5]),(0,[z0,z85,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z132,z233]),(0,[z0,z1,z290,z2,z7,z4,z5])],[(0,[z155,z1,z2,z7,z12,z4,z5]),(0,[z0,z1,z2,z158,z7,z4,z5]),(0,[z0,z1,z2,z66,z16,z4,z5]),(0,[z0,z291,z1,z2,z7,z4,z5])],[(0,[z157,z0,z1,z2,z12,z4,z5])]],
   [[(0,[z80,z102,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z12,z4,z25,z5]),(0,[z0,z1,z2,z7,z9,z5,z233]),(0,[z0,z1,z58,z2,z167,z4,z5])],[(0,[z0,z102,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z292,z4,z5]),(0,[z0,z1,z2,z12,z4,z293,z5]),(0,[z1,z2,z7,z12,z4,z9,z5]),(0,[z0,z1,z130,z2,z12,z4,z5]),(1,[z0,z90,z2,z43,z4,z5]),(0,[z0,z276,z1,z2,z7,z178,z5]),(0,[z0,z1,z2,z7,z4,z5,z233])],[(0,[z128,z0,z1,z2,z7,z294,z5]),(0,[z295,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z296]),(0,[z297,z0,z1,z2,z7,z4,z5]),(0,[z226,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z32,z5]),(0,[z0,z1,z298,z2,z7,z4,z5]),(0,[z299,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z18,z4,z13])],[(0,[z0,z1,z2,z7,z4,z5,z300]),(0,[z301,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z302,z12,z4,z5]),(0,[z157,z0,z1,z2,z265,z4,z5]),(1,[z303,z1,z2,z7,z4,z5]),(0,[z41,z100,z0,z1,z2,z4,z5]),(0,[z304,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z305,z5]),(0,[z267,z0,z1,z2,z7,z125,z5]),(0,[z0,z1,z2,z7,z4,z306,z5])],[(0,[z0,z1,z58,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z43,z4,z5]),(0,[z0,z1,z2,z7,z307,z4,z5])],[(0,[z128,z0,z1,z2,z7,z308,z5]),(1,[z0,z1,z2,z7,z4,z309]),(0,[z310,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z311]),(0,[z267,z0,z1,z2,z7,z5,z233])],[(0,[z0,z1,z2,z7,z312,z4,z5]),(0,[z0,z1,z2,z72,z7,z4,z5])]],
   [[(0,[z86,z0,z1,z2,z313,z4,z5]),(0,[z314,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z315,z2,z7,z4,z5]),(0,[z316,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z60,z4,z5])],[(0,[z27,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z12,z4,z5]),(0,[z0,z1,z2,z16,z81,z4,z5]),(0,[z317,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z318,z4,z5]),(0,[z0,z1,z58,z7,z4,z132,z5]),(0,[z319,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z320,z2,z7,z4,z5])],[(0,[z84,z0,z1,z2,z3,z4,z5]),(0,[z177,z0,z1,z2,z7,z9,z5]),(0,[z321,z0,z1,z2,z7,z4,z5]),(0,[z0,z322,z1,z2,z7,z4,z5])],[(1,[z0,z1,z323,z7,z4,z5]),(0,[z0,z1,z2,z7,z324,z4,z5]),(1,[z93,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z325])],[(0,[z41,z0,z1,z2,z12,z4,z5]),(0,[z326,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z125,z116,z5])],[(0,[z0,z1,z2,z7,z4,z327,z5]),(0,[z173,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z328,z5]),(0,[z0,z1,z2,z7,z329,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z330]),(0,[z0,z1,z2,z7,z4,z331,z5])],[(0,[z173,z0,z276,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z265,z4,z5]),(0,[z332,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z333])]],
   [[(0,[z0,z106,z1,z2,z3,z4,z5]),(0,[z0,z1,z334,z2,z7,z4,z5]),(0,[z0,z1,z2,z335,z7,z4,z5])],[(0,[z21,z0,z1,z2,z7,z4,z34]),(0,[z0,z90,z1,z2,z16,z4,z5])],[(1,[z0,z1,z2,z313,z4,z5]),(0,[z0,z115,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z336]),(0,[z337,z0,z1,z2,z7,z4,z5]),(0,[z0,z90,z1,z2,z43,z4,z5]),(0,[z0,z338,z1,z2,z7,z4,z5]),(1,[z289,z0,z1,z2,z4,z5])],[(0,[z68,z0,z1,z2,z12,z4,z5]),(0,[z339,z0,z1,z2,z12,z4,z5]),(0,[z340,z0,z1,z2,z7,z4,z5])],[(0,[z71,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z12,z4,z5,z139]),(0,[z0,z1,z2,z7,z4,z5,z341]),(0,[z0,z342,z1,z2,z7,z4,z5]),(0,[z119,z0,z1,z2,z109,z4,z5]),(0,[z0,z1,z2,z7,z4,z343,z5])],[(0,[z128,z0,z1,z2,z3,z4,z5]),(0,[z344,z0,z1,z2,z7,z4,z5]),(0,[z345,z0,z1,z2,z7,z4,z5]),(0,[z33,z1,z2,z7,z4,z205,z5])],[(1,[z0,z1,z2,z7,z4,z107]),(0,[z346,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z347,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z348,z5]),(0,[z349,z0,z1,z2,z7,z4,z5])],[(0,[z0,z90,z1,z2,z12,z4,z5]),(0,[z350,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z351,z7,z4,z5]),(0,[z352,z0,z1,z2,z7,z4,z5])]],
   [[(0,[z147,z0,z1,z2,z7,z4,z5]),(0,[z0,z353,z1,z2,z7,z4,z5]),(0,[z157,z0,z1,z2,z7,z25,z5]),(0,[z0,z1,z2,z223,z7,z4,z5]),(0,[z0,z1,z354,z2,z7,z4,z5])],[(0,[z0,z87,z1,z2,z7,z4,z5]),(0,[z124,z84,z1,z2,z7,z4,z5]),(0,[z355,z0,z1,z2,z7,z4,z5]),(0,[z356,z0,z1,z2,z7,z4,z5]),(0,[z15,z0,z2,z16,z7,z4,z5]),(1,[z147,z0,z2,z7,z178,z5]),(0,[z0,z276,z1,z2,z357,z4,z5]),(0,[z0,z1,z2,z7,z358,z4,z5])],[(0,[z0,z359,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z25,z5])],[(0,[z0,z1,z2,z360,z7,z4,z5]),(0,[z361,z0,z1,z2,z7,z4,z5]),(0,[z155,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z4,z293,z5]),(0,[z0,z152,z2,z75,z7,z4,z5]),(0,[z0,z1,z2,z53,z7,z97,z5]),(0,[z0,z1,z2,z7,z4,z362,z5])],[(0,[z0,z1,z2,z7,z4,z5,z363])],[(0,[z0,z1,z2,z3,z4,z178,z5]),(0,[z157,z0,z1,z2,z318,z4,z5]),(0,[z0,z364,z1,z2,z7,z4,z5])],[(0,[z0,z365,z1,z2,z7,z4,z5]),(0,[z0,z1,z366,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z367]),(0,[z0,z152,z1,z2,z55,z4,z5]),(0,[z0,z1,z2,z368,z7,z4,z5])],[(0,[z0,z1,z2,z3,z369,z4,z5]),(1,[z33,z1,z2,z7,z4,z205]),(0,[z0,z1,z370,z2,z7,z4,z5]),(1,[z0,z1,z2,z55,z4,z5]),(0,[z0,z1,z2,z7,z4,z371,z5]),(0,[z157,z93,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z101])]],
   [[(0,[z0,z1,z2,z7,z372,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z373]),(0,[z0,z1,z2,z7,z4,z374,z5]),(0,[z157,z0,z1,z2,z7,z60,z5]),(0,[z375,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z376,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z17]),(0,[z377,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z378,z7,z4,z5])],[(0,[z0,z379,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z380,z5]),(0,[z381,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z185,z3,z4,z5]),(0,[z0,z1,z2,z7,z4,z382,z5]),(0,[z0,z1,z2,z7,z4,z383,z5]),(0,[z384,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z385,z5]),(0,[z0,z1,z2,z7,z4,z386,z5])],[(0,[z80,z0,z1,z2,z7,z387,z5]),(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z27,z0,z1,z58,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z388,z5])],[(0,[z86,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z4,z142,z5]),(0,[z0,z1,z2,z16,z18,z4,z5]),(0,[z41,z303,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z309,z5]),(0,[z80,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z389,z4,z5]),(0,[z390,z0,z1,z2,z7,z4,z5]),(0,[z157,z0,z1,z2,z7,z94,z5]),(0,[z0,z1,z2,z254,z7,z4,z5])],[(0,[z391,z0,z1,z2,z7,z4,z5]),(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z34]),(0,[z0,z2,z7,z43,z4,z5,z139]),(0,[z0,z1,z2,z81,z4,z97,z5]),(0,[z392,z0,z1,z2,z7,z4,z5]),(0,[z393,z0,z1,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z12,z4,z394,z5]),(1,[z124,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z395]),(0,[z177,z84,z1,z2,z7,z4,z5]),(1,[z0,z1,z396,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z34,z139]),(0,[z0,z1,z2,z53,z81,z4,z5]),(0,[z397,z0,z1,z2,z7,z4,z5])],[(1,[z0,z1,z2,z307,z4,z5]),(1,[z64,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z398,z4,z5]),(0,[z0,z1,z399,z2,z7,z4,z5])],[(1,[z1,z2,z3,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z400,z5]),(0,[z0,z1,z2,z7,z4,z401,z5])],[(0,[z21,z0,z1,z2,z402,z4,z5]),(0,[z0,z1,z2,z403,z7,z4,z5]),(0,[z0,z404,z1,z2,z7,z4,z5]),(0,[z0,z70,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z53,z109,z5])],[(0,[z0,z152,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z142,z34]),(0,[z0,z405,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z18,z43,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z139]),(1,[z0,z1,z2,z7,z4,z406]),(0,[z0,z1,z2,z407,z7,z4,z5]),(0,[z408,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z409]),(0,[z0,z1,z2,z7,z4,z5,z410])],[(1,[z0,z1,z2,z12,z4,z5]),(0,[z177,z0,z1,z2,z12,z4,z5]),(0,[z339,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z411,z2,z7,z4,z5]),(0,[z173,z0,z152,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z313,z4,z5]),(1,[z86,z87,z2,z7,z4,z5]),(0,[z0,z1,z412,z2,z7,z4,z5]),(1,[z80,z102,z1,z7,z4,z5]),(0,[z0,z1,z2,z413,z7,z4,z5]),(0,[z74,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z81,z4,z13,z5]),(0,[z0,z1,z2,z376,z4,z25,z5])],[(0,[z227,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z324,z4,z5]),(0,[z0,z1,z2,z414,z7,z4,z5]),(0,[z0,z1,z2,z415,z7,z4,z5]),(0,[z0,z1,z2,z416,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z417,z5]),(1,[z1,z2,z12,z4,z9,z5]),(0,[z0,z1,z2,z3,z4,z97,z5]),(0,[z0,z1,z2,z7,z4,z5,z418]),(0,[z419,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z18,z12,z4,z5]),(0,[z0,z1,z2,z224,z7,z4,z5]),(0,[z420,z0,z1,z2,z7,z4,z5]),(0,[z0,z90,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z8,z4,z5]),(0,[z0,z63,z2,z7,z4,z142,z5]),(0,[z0,z1,z2,z7,z421,z4,z5]),(0,[z422,z0,z1,z2,z7,z4,z5])],[(0,[z80,z71,z1,z2,z7,z4,z5]),(0,[z80,z0,z1,z2,z144,z4,z5]),(1,[z0,z180,z2,z7,z4,z5])],[(0,[z86,z0,z2,z212,z7,z4,z5]),(0,[z0,z102,z1,z7,z4,z5,z89]),(0,[z177,z0,z1,z2,z54,z4,z5]),(0,[z84,z0,z85,z1,z7,z4,z5]),(0,[z138,z0,z1,z2,z307,z4,z5]),(0,[z0,z1,z2,z7,z4,z423,z5])],[(1,[z0,z1,z2,z163,z4,z5]),(0,[z0,z1,z2,z7,z424,z4,z5])],[(0,[z425,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z116,z89]),(0,[z0,z1,z2,z7,z4,z426,z5]),(1,[z0,z1,z2,z4,z5,z427]),(0,[z0,z1,z2,z7,z125,z4,z116])]],
   [[(0,[z128,z86,z1,z2,z7,z4,z5]),(0,[z428,z0,z1,z2,z7,z4,z5]),(0,[z429,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z430,z5]),(1,[z0,z1,z35,z2,z4,z5]),(0,[z431,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z18,z7,z4,z13]),(0,[z0,z1,z2,z432,z7,z4,z5])],[(0,[z433,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z24,z7,z94,z5])],[(0,[z138,z0,z1,z2,z12,z4,z5]),(0,[z0,z434,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z435,z5]),(0,[z0,z1,z189,z2,z7,z4,z5])],[(0,[z436,z0,z1,z2,z7,z4,z5]),(0,[z437,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z16,z12,z4,z5]),(0,[z0,z1,z2,z3,z4,z13,z5]),(0,[z21,z33,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z402,z7,z4,z5]),(1,[z0,z209,z2,z7,z4,z5])],[(0,[z0,z1,z2,z12,z109,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z438]),(0,[z439,z0,z1,z2,z7,z4,z5]),(0,[z0,z276,z2,z7,z8,z4,z5]),(0,[z0,z1,z2,z440,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z441,z5])],[(1,[z0,z1,z2,z442,z4,z5]),(0,[z0,z443,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z12,z4,z116,z5]),(0,[z157,z64,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z7,z4,z444]),(0,[z100,z0,z1,z2,z4,z5,z17])],[(0,[z0,z1,z2,z12,z445,z4,z5]),(0,[z446,z0,z1,z2,z7,z4,z5])],[(1,[z0,z1,z2,z7,z150,z5]),(0,[z0,z447,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z12,z125,z4,z5]),(0,[z173,z0,z2,z7,z4,z178,z5]),(0,[z0,z1,z2,z66,z4,z13,z5])]],
   [[(0,[z0,z1,z2,z212,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z6]),(0,[z100,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z7,z448,z5]),(0,[z0,z1,z2,z7,z116,z5,z233])],[(0,[z138,z0,z1,z2,z163,z4,z5]),(0,[z449,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z450,z7,z4,z5]),(0,[z157,z0,z1,z24,z7,z4,z5]),(0,[z157,z0,z1,z2,z7,z4,z406])],[(0,[z451,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z133,z7,z4,z5]),(0,[z0,z1,z2,z452,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z394,z5]),(0,[z0,z276,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z396,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z453,z5]),(0,[z0,z1,z2,z7,z4,z454,z5]),(0,[z0,z1,z2,z197,z7,z4,z5])],[(0,[z455,z0,z1,z2,z7,z4,z5]),(0,[z456,z0,z1,z2,z7,z4,z5]),(0,[z21,z0,z1,z2,z7,z4,z205]),(0,[z457,z0,z1,z2,z7,z4,z5]),(0,[z267,z0,z1,z2,z7,z4,z116])],[(0,[z458,z0,z1,z2,z7,z4,z5]),(0,[z33,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z24,z2,z3,z4,z5]),(0,[z459,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z460,z5]),(0,[z461,z0,z1,z2,z7,z4,z5])],[(0,[z0,z462,z1,z2,z7,z4,z5]),(0,[z0,z276,z1,z2,z197,z4,z5]),(1,[z0,z1,z2,z376,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z463])],[(0,[z464,z0,z1,z2,z7,z4,z5]),(0,[z465,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z466,z2,z7,z4,z5]),(0,[z467,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z468,z2,z7,z4,z5]),(0,[z0,z1,z2,z469,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z470,z5]),(1,[z155,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z471,z4,z5]),(0,[z0,z1,z2,z472,z7,z4,z5]),(0,[z157,z0,z180,z2,z7,z4,z5]),(0,[z0,z473,z1,z2,z7,z4,z5]),(0,[z0,z474,z1,z2,z7,z4,z5])]],
   [[(0,[z15,z100,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z18,z7,z4,z17]),(0,[z475,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z476])],[(0,[z0,z1,z2,z7,z308,z4,z5]),(0,[z267,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z81,z4,z5]),(1,[z0,z1,z2,z477,z4,z5]),(0,[z0,z1,z2,z478,z7,z4,z5]),(0,[z479,z0,z1,z2,z7,z4,z5]),(0,[z480,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z481,z2,z7,z4,z5]),(0,[z0,z1,z482,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z483,z4,z5]),(0,[z102,z1,z2,z133,z7,z4,z5]),(0,[z484,z0,z1,z2,z7,z4,z5]),(0,[z21,z0,z1,z2,z7,z448,z5]),(0,[z0,z1,z2,z7,z4,z485,z5]),(0,[z100,z0,z90,z1,z2,z4,z5]),(0,[z41,z0,z1,z2,z16,z4,z5])],[(1,[z0,z1,z2,z7,z4,z5]),(0,[z486,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z12,z487,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z89]),(0,[z33,z0,z1,z2,z61,z4,z5]),(0,[z0,z1,z2,z488,z7,z4,z5]),(0,[z41,z0,z1,z2,z43,z4,z5]),(0,[z15,z0,z1,z2,z16,z4,z5])],[(0,[z0,z102,z1,z2,z3,z4,z5]),(0,[z489,z0,z1,z2,z7,z4,z5]),(0,[z177,z1,z2,z7,z4,z9,z5]),(0,[z15,z0,z1,z2,z43,z4,z5]),(0,[z490,z0,z1,z2,z7,z4,z5]),(0,[z491,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z492])],[(0,[z0,z1,z2,z7,z4,z5,z493]),(0,[z0,z1,z2,z3,z4,z9,z5]),(0,[z0,z1,z130,z2,z109,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z494])],[(0,[z0,z1,z495,z2,z7,z4,z5]),(0,[z0,z1,z2,z496,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z497,z5]),(0,[z0,z1,z2,z498,z7,z4,z5]),(0,[z0,z1,z2,z7,z499,z4,z5])],[(0,[z0,z500,z1,z2,z7,z4,z5]),(0,[z0,z1,z501,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z502,z5]),(0,[z0,z1,z2,z7,z4,z5,z503]),(0,[z0,z1,z2,z18,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z12,z4,z178,z5]),(0,[z0,z63,z1,z2,z12,z4,z5]),(0,[z177,z0,z1,z2,z7,z60,z5]),(0,[z0,z1,z2,z7,z4,z5,z504]),(0,[z41,z0,z1,z130,z2,z4,z5]),(0,[z157,z0,z1,z2,z7,z4,z444])],[(0,[z0,z1,z133,z7,z94,z4,z5]),(0,[z15,z0,z1,z2,z12,z4,z5]),(0,[z0,z505,z1,z2,z7,z4,z5])],[],[(0,[z0,z1,z2,z506,z7,z4,z5])],[(0,[z0,z1,z2,z7,z507,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z508]),(0,[z509,z0,z1,z2,z7,z4,z5]),(0,[z510,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z58,z133,z7,z4,z5]),(0,[z21,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z448,z5]),(0,[z0,z1,z2,z7,z511,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z427])],[(0,[z0,z1,z2,z512,z7,z4,z5]),(0,[z0,z1,z2,z7,z60,z178,z5]),(0,[z138,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z130,z81,z4,z5]),(0,[z303,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z109,z4,z5]),(0,[z0,z135,z1,z2,z7,z4,z5])],[(0,[z513,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z514,z5]),(0,[z0,z1,z515,z2,z7,z4,z5]),(0,[z0,z1,z516,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z116,z5])]],
   [[(0,[z0,z1,z2,z83,z7,z4,z5]),(0,[z0,z1,z2,z12,z4,z142,z5]),(0,[z0,z1,z2,z7,z445,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z517]),(0,[z518,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z519,z7,z4,z5]),(0,[z41,z0,z1,z2,z7,z109,z5]),(0,[z0,z1,z2,z7,z520,z4,z5])],[(0,[z284,z0,z1,z2,z7,z4,z5]),(0,[z0,z521,z1,z2,z7,z4,z5]),(0,[z0,z87,z2,z7,z4,z5,z139]),(0,[z0,z443,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z125,z4,z5])],[(0,[z0,z1,z2,z12,z4,z5,z34]),(0,[z0,z1,z2,z53,z12,z4,z5]),(0,[z0,z2,z7,z4,z142,z5,z139]),(0,[z522,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z318,z7,z4,z5])],[(0,[z0,z1,z2,z523,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z524,z5]),(0,[z84,z0,z1,z396,z7,z4,z5]),(0,[z0,z1,z2,z7,z525,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z526]),(0,[z0,z1,z527,z2,z7,z4,z5])],[(0,[z0,z1,z2,z12,z8,z4,z5]),(1,[z0,z1,z44,z7,z4,z5]),(0,[z0,z1,z2,z528,z7,z4,z5])],[(0,[z0,z1,z2,z529,z7,z4,z5]),(0,[z119,z0,z1,z66,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z5,z530]),(0,[z0,z1,z2,z7,z4,z5,z531]),(0,[z157,z0,z1,z2,z7,z4,z5])],[(0,[z532,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z12,z94,z4,z5]),(0,[z100,z0,z1,z2,z66,z4,z5]),(0,[z0,z1,z2,z7,z125,z4,z233])]],
   [[(0,[z0,z63,z2,z212,z7,z4,z5]),(0,[z533,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z534,z4,z5]),(0,[z0,z1,z2,z75,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z4,z5]),(0,[z0,z1,z2,z7,z4,z142,z205]),(0,[z0,z1,z130,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z406,z5]),(0,[z0,z1,z2,z7,z4,z535,z5]),(0,[z0,z1,z2,z7,z4,z536,z5])],[(0,[z537,z0,z1,z2,z7,z4,z5]),(0,[z84,z0,z1,z2,z12,z4,z5]),(0,[z538,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z539,z7,z4,z5]),(0,[z0,z1,z2,z7,z540,z4,z5])],[(0,[z0,z1,z2,z7,z4,z541,z5]),(0,[z124,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z542,z4,z5]),(0,[z0,z1,z2,z7,z4,z543,z5]),(0,[z0,z152,z1,z75,z7,z4,z5]),(0,[z0,z1,z2,z544,z7,z4,z5]),(0,[z173,z74,z0,z1,z7,z4,z5]),(0,[z545,z0,z1,z2,z7,z4,z5]),(0,[z0,z546,z1,z2,z7,z4,z5]),(0,[z41,z0,z1,z2,z53,z4,z5])],[(0,[z0,z1,z2,z302,z7,z4,z5]),(0,[z84,z0,z1,z2,z324,z4,z5]),(0,[z0,z1,z2,z547,z7,z4,z5])],[(1,[z0,z1,z2,z239,z4,z5]),(0,[z173,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z548,z7,z4,z5]),(0,[z84,z0,z1,z2,z258,z4,z5]),(0,[z147,z0,z276,z2,z7,z4,z5])],[(0,[z549,z0,z1,z2,z7,z4,z5]),(0,[z71,z0,z1,z2,z442,z4,z5]),(0,[z0,z1,z2,z7,z487,z4,z5]),(0,[z0,z1,z2,z7,z60,z125,z5]),(0,[z0,z1,z2,z7,z4,z550,z5]),(0,[z147,z0,z1,z2,z7,z178,z5]),(1,[z215,z1,z2,z7,z4,z5]),(0,[z100,z0,z1,z2,z81,z4,z5]),(0,[z0,z1,z2,z7,z4,z551,z5]),(0,[z0,z1,z2,z7,z4,z5,z552]),(0,[z267,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z387,z5]),(0,[z0,z1,z2,z360,z3,z4,z5]),(0,[z21,z0,z1,z44,z7,z4,z5]),(1,[z0,z1,z2,z402,z4,z5]),(0,[z553,z0,z1,z2,z7,z4,z5])],[(0,[z80,z0,z1,z2,z176,z4,z5]),(0,[z0,z1,z2,z3,z4,z132,z5]),(0,[z0,z1,z2,z7,z477,z4,z5])]],
   [[(0,[z0,z1,z2,z323,z7,z4,z5]),(1,[z0,z1,z2,z232,z4,z5]),(0,[z0,z1,z2,z554,z7,z4,z5]),(0,[z0,z1,z2,z555,z7,z4,z5]),(0,[z0,z556,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z557,z7,z4,z5]),(0,[z0,z1,z2,z7,z558,z4,z5])],[(0,[z0,z63,z87,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z559]),(0,[z0,z1,z2,z7,z4,z560,z5]),(0,[z0,z1,z2,z7,z561,z4,z5]),(0,[z27,z0,z1,z2,z7,z4,z5])],[(0,[z562,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z43,z109,z4,z5]),(0,[z0,z1,z2,z7,z4,z178,z5]),(0,[z0,z1,z563,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z564,z5])],[(0,[z0,z1,z2,z66,z3,z4,z5]),(0,[z157,z0,z1,z7,z4,z132,z5])],[(0,[z33,z0,z1,z2,z72,z4,z5]),(0,[z41,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z565])],[(0,[z0,z1,z2,z7,z4,z5,z566]),(0,[z15,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z357,z4,z5]),(0,[z0,z1,z2,z567,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z205,z139]),(0,[z0,z1,z2,z7,z4,z5,z568]),(0,[z0,z1,z2,z7,z4,z569,z5]),(0,[z0,z1,z570,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z571,z5])],[(0,[z80,z0,z102,z1,z7,z4,z5]),(0,[z0,z22,z1,z2,z7,z4,z5])]],
   [[(0,[z173,z74,z0,z2,z7,z4,z5]),(0,[z0,z572,z1,z2,z7,z4,z5])],[(0,[z155,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z233]),(0,[z0,z1,z2,z7,z4,z573,z5]),(0,[z574,z0,z1,z2,z7,z4,z5]),(0,[z0,z575,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z576,z4,z5]),(0,[z0,z1,z7,z4,z5,z101,z233])],[(0,[z68,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z577,z5]),(0,[z119,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z4,z142,z5])],[(0,[z71,z0,z1,z2,z7,z4,z5]),(0,[z578,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z579,z7,z4,z5])],[(0,[z0,z1,z2,z442,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z34]),(0,[z580,z0,z1,z2,z7,z4,z5])],[(0,[z0,z581,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z223,z4,z5]),(0,[z0,z1,z2,z582,z7,z4,z5]),(0,[z100,z0,z135,z2,z7,z4,z5])],[(0,[z80,z0,z1,z133,z7,z4,z5]),(0,[z80,z84,z1,z2,z7,z4,z5]),(0,[z0,z1,z24,z2,z7,z9,z5]),(0,[z1,z2,z7,z4,z205,z5,z34]),(0,[z0,z1,z2,z583,z7,z4,z5])],[(0,[z0,z1,z2,z4,z13,z5,z17])]],
   [[(0,[z584,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z585]),(0,[z0,z1,z2,z7,z4,z586,z5]),(0,[z0,z1,z2,z7,z587,z4,z5])],[(0,[z0,z102,z1,z58,z7,z4,z5]),(0,[z0,z1,z588,z2,z7,z4,z5]),(0,[z0,z1,z589,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z590,z5]),(0,[z0,z1,z2,z66,z4,z97,z5]),(0,[z0,z1,z2,z7,z94,z4,z5]),(0,[z27,z0,z1,z2,z7,z4,z132]),(0,[z591,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z35,z2,z4,z5,z139])],[(1,[z128,z2,z212,z7,z4,z5]),(0,[z128,z0,z2,z212,z7,z4,z5]),(0,[z124,z1,z2,z3,z7,z4,z5]),(0,[z74,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z413,z3,z4,z5]),(0,[z0,z2,z7,z8,z4,z178,z5]),(0,[z0,z1,z2,z7,z4,z592,z5]),(0,[z0,z1,z66,z7,z81,z4,z5])],[(0,[z593,z0,z1,z2,z7,z4,z5]),(0,[z0,z594,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z75,z7,z4,z5]),(0,[z595,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z596])],[(0,[z0,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z597]),(0,[z0,z1,z2,z598,z7,z4,z5]),(0,[z0,z2,z75,z7,z4,z178,z5]),(0,[z599,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z600]),(1,[z1,z2,z7,z4,z5,z330])],[(0,[z0,z1,z2,z7,z534,z4,z5]),(0,[z124,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z206,z12,z4,z5]),(0,[z124,z1,z2,z7,z4,z9,z5]),(0,[z601,z0,z1,z2,z7,z4,z5]),(0,[z602,z0,z1,z2,z7,z4,z5]),(0,[z119,z0,z1,z130,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z603]),(0,[z604,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z605,z5])]],
   [[(1,[z0,z1,z2,z7,z329,z5]),(0,[z173,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z606,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z607,z5]),(0,[z0,z1,z2,z109,z4,z97,z5])],[(0,[z608,z0,z1,z2,z12,z4,z5]),(0,[z84,z0,z1,z2,z7,z60,z5]),(0,[z0,z1,z2,z609,z7,z4,z5])],[(1,[z0,z1,z2,z7,z294,z5]),(0,[z0,z1,z2,z7,z4,z5,z610]),(0,[z611,z0,z1,z2,z7,z4,z5])],[(0,[z86,z0,z1,z2,z7,z4,z5]),(0,[z128,z0,z87,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z612,z5]),(0,[z613,z0,z1,z2,z7,z4,z5]),(0,[z614,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z615,z5]),(0,[z0,z1,z2,z7,z4,z5,z616])],[(0,[z617,z0,z1,z2,z7,z4,z5]),(0,[z128,z0,z1,z2,z7,z4,z309]),(0,[z0,z1,z2,z156,z7,z4,z5]),(0,[z0,z1,z192,z2,z7,z4,z5]),(0,[z0,z276,z2,z75,z7,z4,z5]),(0,[z0,z1,z2,z618,z7,z4,z5]),(0,[z0,z619,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z7,z125,z116])],[(0,[z0,z1,z2,z7,z232,z4,z5]),(0,[z620,z0,z1,z2,z7,z4,z5]),(1,[z0,z581,z2,z7,z4,z5]),(0,[z0,z1,z2,z621,z7,z4,z5])],[(1,[z0,z1,z2,z7,z308,z5]),(0,[z0,z1,z2,z7,z4,z622,z5]),(1,[z84,z1,z2,z12,z4,z5]),(0,[z15,z0,z90,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z623]),(0,[z0,z1,z2,z16,z109,z4,z5]),(0,[z0,z624,z1,z2,z7,z4,z5])]],
   [[(0,[z625,z0,z1,z2,z7,z4,z5]),(0,[z71,z0,z1,z2,z534,z4,z5]),(0,[z0,z1,z2,z258,z7,z4,z5]),(0,[z0,z626,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z627,z5]),(0,[z0,z1,z24,z7,z94,z4,z5]),(0,[z0,z1,z628,z2,z7,z4,z5])],[(0,[z629,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z3,z4,z25,z5]),(0,[z21,z0,z1,z2,z7,z329,z5]),(0,[z138,z0,z1,z2,z7,z4,z142]),(1,[z138,z0,z2,z7,z4,z139]),(0,[z630,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z631,z7,z4,z5]),(0,[z0,z1,z2,z109,z4,z13,z5])],[(0,[z128,z0,z1,z323,z7,z4,z5]),(0,[z0,z1,z2,z632,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z633,z5]),(0,[z0,z1,z2,z7,z357,z4,z5]),(0,[z1,z2,z7,z4,z5,z330,z139]),(0,[z0,z1,z2,z7,z4,z634,z5]),(0,[z0,z1,z2,z635,z7,z4,z5])],[(0,[z636,z0,z1,z2,z7,z4,z5]),(0,[z0,z637,z1,z2,z7,z4,z5]),(0,[z177,z0,z1,z2,z477,z4,z5]),(0,[z27,z0,z1,z2,z7,z4,z89]),(0,[z0,z1,z2,z7,z4,z5,z638])],[(0,[z128,z1,z2,z212,z7,z4,z5]),(0,[z639,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z133,z3,z4,z5]),(0,[z0,z152,z1,z2,z7,z4,z5]),(0,[z0,z90,z2,z7,z43,z4,z5]),(0,[z0,z1,z2,z7,z4,z640,z5]),(0,[z641,z0,z1,z2,z7,z4,z5])],[(0,[z177,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z642]),(0,[z157,z0,z1,z7,z4,z25,z5])],[(0,[z215,z0,z1,z2,z7,z4,z5])]],
   [[(0,[z643,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z644,z7,z4,z5]),(0,[z0,z102,z1,z7,z94,z4,z5]),(0,[z645,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z646,z7,z4,z5]),(1,[z0,z276,z2,z7,z8,z5]),(1,[z41,z0,z1,z2,z97,z5]),(0,[z0,z1,z2,z7,z4,z647,z5])],[(0,[z21,z128,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z648]),(0,[z119,z0,z1,z2,z66,z4,z5])],[(0,[z21,z87,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z649,z7,z4,z5]),(0,[z0,z1,z130,z7,z81,z4,z5]),(0,[z0,z1,z7,z4,z132,z5,z89]),(0,[z0,z1,z2,z7,z4,z132,z116])],[(0,[z650,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z125,z9,z5]),(0,[z0,z1,z2,z651,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z652,z5]),(0,[z653,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z654,z4,z5]),(1,[z267,z0,z1,z2,z7,z233])],[(0,[z0,z1,z2,z7,z4,z655,z5]),(1,[z0,z1,z2,z7,z387,z5]),(0,[z0,z1,z2,z7,z4,z656,z5]),(0,[z0,z1,z2,z254,z4,z25,z5]),(0,[z0,z657,z1,z2,z7,z4,z5]),(0,[z289,z0,z1,z2,z4,z5,z233])],[(0,[z128,z0,z1,z2,z7,z4,z107]),(0,[z0,z1,z2,z7,z658,z4,z5]),(0,[z0,z90,z1,z2,z4,z13,z5])],[(0,[z659,z0,z1,z2,z7,z4,z5]),(0,[z71,z1,z2,z133,z7,z4,z5]),(0,[z124,z155,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z3,z4,z5]),(0,[z100,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z660]),(0,[z138,z0,z2,z7,z4,z5,z139]),(0,[z661,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z133,z75,z7,z4,z5]),(0,[z0,z1,z2,z12,z4,z5,z17]),(0,[z489,z0,z1,z2,z3,z4,z5]),(0,[z662,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z4,z36,z5]),(0,[z119,z0,z1,z2,z81,z4,z5]),(0,[z0,z1,z663,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z294,z5]),(0,[z0,z276,z1,z2,z12,z4,z5]),(0,[z0,z664,z1,z2,z7,z4,z5]),(0,[z173,z0,z1,z75,z7,z4,z5]),(0,[z665,z0,z1,z2,z7,z4,z5])],[(0,[z157,z0,z581,z2,z7,z4,z5])],[(0,[z33,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z24,z2,z12,z4,z5]),(0,[z0,z1,z2,z16,z7,z4,z5]),(0,[z611,z0,z1,z7,z4,z5,z233]),(0,[z0,z1,z2,z7,z4,z666,z5])],[(0,[z0,z667,z1,z2,z7,z4,z5]),(0,[z0,z1,z668,z2,z7,z4,z5]),(0,[z100,z0,z1,z2,z7,z4,z13])],[(1,[z0,z1,z183,z7,z4,z5]),(0,[z0,z669,z1,z2,z7,z4,z5]),(0,[z670,z0,z1,z2,z7,z4,z5]),(0,[z0,z671,z1,z2,z7,z4,z5]),(1,[z70,z1,z2,z7,z4,z5])],[(0,[z86,z0,z1,z2,z239,z4,z5]),(0,[z672,z0,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z61,z4,z5]),(0,[z673,z0,z1,z2,z7,z4,z5]),(0,[z27,z0,z1,z7,z4,z5,z89])],[(0,[z608,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z58,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z139]),(0,[z0,z1,z2,z7,z4,z328,z5]),(0,[z0,z674,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z212,z7,z4,z5]),(0,[z241,z0,z1,z2,z7,z4,z5]),(0,[z1,z2,z7,z60,z4,z9,z5]),(0,[z0,z1,z2,z7,z675,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z676]),(0,[z0,z1,z2,z7,z677,z4,z5])]],
   [[(0,[z87,z1,z2,z212,z7,z4,z5]),(0,[z21,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z678,z4,z5]),(0,[z0,z1,z2,z679,z7,z4,z5])],[(0,[z21,z0,z189,z2,z7,z4,z5]),(0,[z0,z1,z2,z4,z5,z427,z233])],[(0,[z0,z102,z1,z2,z12,z4,z5]),(0,[z680,z0,z1,z2,z7,z4,z5]),(0,[z681,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z682,z5])],[(0,[z683,z0,z1,z2,z7,z4,z5]),(0,[z138,z0,z63,z2,z7,z4,z5])],[(0,[z0,z1,z2,z53,z7,z109,z5])],[(0,[z147,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z4,z684,z5]),(0,[z0,z1,z2,z7,z4,z5,z685]),(0,[z0,z1,z2,z53,z109,z4,z5])],[(0,[z0,z87,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z2,z7,z4,z5]),(0,[z0,z1,z2,z686,z7,z4,z5]),(0,[z0,z1,z2,z3,z18,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z687])]],
   [[(0,[z0,z1,z2,z12,z4,z97,z5]),(1,[z84,z1,z2,z7,z60,z5])],[(0,[z0,z1,z2,z7,z4,z5,z688]),(0,[z0,z1,z2,z689,z7,z4,z5]),(0,[z157,z0,z1,z2,z3,z4,z5]),(1,[z0,z22,z2,z7,z4,z5]),(1,[z611,z0,z1,z7,z4,z5])],[(0,[z0,z1,z2,z7,z690,z4,z5]),(0,[z0,z1,z2,z7,z60,z5,z233]),(0,[z0,z1,z2,z691,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z444]),(0,[z692,z0,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z3,z4,z205,z5]),(0,[z0,z1,z130,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z4,z693,z5]),(0,[z100,z0,z1,z2,z7,z4,z17]),(0,[z0,z1,z2,z7,z4,z5,z694])],[(0,[z695,z0,z1,z2,z7,z4,z5]),(0,[z696,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z9,z178,z5]),(0,[z0,z697,z1,z2,z7,z4,z5]),(0,[z0,z698,z1,z2,z7,z4,z5]),(0,[z699,z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z5,z700]),(0,[z0,z1,z2,z7,z4,z89,z233])],[(0,[z15,z0,z2,z7,z4,z5,z139]),(0,[z0,z276,z1,z2,z7,z8,z5])],[(0,[z128,z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z701,z7,z4,z5]),(0,[z267,z0,z1,z2,z7,z4,z233])],[(0,[z0,z1,z2,z7,z4,z702,z5]),(0,[z0,z1,z2,z7,z369,z4,z5]),(0,[z703,z0,z1,z2,z7,z4,z5]),(0,[z704,z0,z1,z2,z7,z4,z5]),(0,[z0,z63,z1,z2,z7,z4,z5]),(0,[z0,z1,z7,z94,z4,z132,z5]),(0,[z0,z1,z2,z7,z4,z705,z5]),(0,[z0,z1,z2,z7,z167,z4,z5]),(0,[z706,z0,z1,z2,z7,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z80,z102,z1,z144,z4,z5]),(0,[z319,z1,z2,z12,z4,z5]),(0,[z0,z707,z1,z7,z4,z5]),(0,[z708,z1,z2,z7,z4,z5]),(0,[z709,z1,z2,z7,z4,z5]),(0,[z0,z710,z2,z7,z4,z5]),(0,[z611,z0,z1,z7,z4,z89])],[(0,[z0,z1,z2,z711,z4,z5]),(0,[z0,z1,z2,z3,z150,z5]),(0,[z0,z1,z396,z258,z4,z5]),(0,[z138,z0,z2,z7,z4,z139])],[(0,[z0,z1,z183,z83,z4,z5]),(0,[z0,z1,z2,z3,z448,z5]),(0,[z0,z1,z2,z4,z712,z5]),(0,[z0,z1,z2,z7,z125,z713])],[(0,[z0,z180,z133,z7,z4,z5]),(0,[z0,z1,z2,z714,z4,z5]),(0,[z0,z189,z2,z7,z448,z5]),(0,[z0,z1,z2,z715,z4,z5]),(0,[z0,z1,z2,z716,z4,z5])],[(0,[z45,z1,z133,z7,z4,z5]),(0,[z0,z1,z192,z7,z448,z5]),(0,[z64,z1,z2,z265,z4,z5])],[(0,[z0,z717,z1,z2,z4,z5]),(0,[z0,z1,z2,z718,z4,z5]),(0,[z0,z1,z2,z719,z4,z5])],[(0,[z0,z1,z2,z4,z720,z5]),(0,[z0,z1,z2,z202,z448,z5]),(0,[z0,z1,z7,z4,z5,z721]),(0,[z0,z1,z2,z53,z722,z5])],[(0,[z0,z1,z2,z723,z4,z5]),(0,[z0,z102,z1,z7,z150,z5]),(0,[z0,z1,z2,z724,z4,z5]),(0,[z41,z0,z1,z2,z97,z5]),(0,[z0,z1,z2,z4,z722,z5])]],
   [[(0,[z0,z1,z183,z7,z294,z5]),(0,[z1,z2,z12,z4,z441,z5]),(0,[z0,z1,z44,z7,z329,z5]),(0,[z0,z1,z2,z725,z4,z5]),(0,[z15,z0,z209,z2,z4,z5]),(0,[z0,z1,z2,z167,z4,z5]),(0,[z0,z1,z2,z265,z4,z406]),(0,[z157,z0,z1,z7,z25,z444]),(0,[z157,z0,z1,z7,z127,z5])],[(0,[z0,z1,z2,z726,z4,z5]),(0,[z155,z1,z2,z727,z4,z5]),(0,[z0,z728,z1,z2,z4,z5]),(0,[z204,z1,z2,z7,z9,z5]),(0,[z0,z1,z2,z729,z4,z5])],[(0,[z157,z0,z1,z7,z134,z5]),(0,[z730,z1,z2,z7,z4,z5]),(0,[z0,z2,z7,z8,z731,z5]),(0,[z119,z0,z1,z66,z4,z5]),(0,[z267,z0,z1,z2,z7,z233]),(0,[z0,z732,z1,z7,z4,z5])],[(0,[z650,z74,z0,z7,z4,z5]),(0,[z96,z1,z2,z3,z4,z5]),(0,[z0,z63,z2,z7,z4,z62]),(0,[z733,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z734,z4,z5]),(1,[z0,z1,z7,z735,z5])],[(0,[z0,z1,z183,z7,z308,z5]),(0,[z0,z1,z2,z736,z4,z5]),(0,[z0,z1,z133,z7,z4,z444]),(0,[z0,z1,z2,z737,z4,z5]),(0,[z0,z738,z2,z12,z4,z5]),(0,[z0,z1,z2,z739,z4,z5]),(0,[z611,z0,z1,z4,z5,z427])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z740,z4,z5]),(0,[z0,z741,z2,z7,z4,z5]),(0,[z0,z1,z2,z742,z4,z5])],[(0,[z0,z1,z2,z7,z4,z743]),(0,[z0,z189,z2,z7,z4,z5]),(0,[z0,z1,z133,z7,z150,z5]),(0,[z84,z1,z2,z7,z150,z5]),(0,[z0,z1,z2,z4,z36,z5]),(0,[z0,z1,z2,z744,z4,z5]),(0,[z745,z1,z2,z7,z4,z5]),(0,[z0,z180,z2,z265,z4,z5])],[(0,[z0,z1,z192,z7,z4,z5]),(0,[z459,z1,z133,z7,z4,z5]),(0,[z0,z1,z2,z144,z150,z5]),(0,[z1,z2,z258,z12,z4,z5]),(0,[z0,z276,z2,z3,z8,z5]),(0,[z33,z1,z2,z7,z4,z746])]],
   [[(0,[z0,z1,z2,z197,z4,z5]),(0,[z0,z1,z747,z7,z4,z5]),(0,[z0,z1,z2,z748,z4,z5]),(0,[z0,z749,z2,z7,z4,z5]),(0,[z157,z0,z1,z376,z25,z5]),(0,[z0,z1,z2,z7,z722,z5])],[(0,[z0,z1,z750,z7,z4,z5]),(0,[z0,z1,z2,z7,z751,z5]),(0,[z0,z1,z2,z202,z4,z5]),(0,[z0,z1,z2,z752,z4,z5]),(0,[z0,z1,z2,z7,z4,z753]),(0,[z0,z1,z2,z754,z4,z5])],[(0,[z0,z22,z2,z7,z329,z5]),(0,[z173,z595,z0,z7,z4,z5]),(0,[z0,z276,z2,z197,z8,z5]),(0,[z611,z0,z1,z7,z4,z444])],[(0,[z0,z1,z2,z755,z4,z5]),(0,[z0,z1,z2,z756,z4,z5]),(0,[z0,z1,z2,z3,z387,z5]),(0,[z0,z757,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z758,z5])],[(0,[z71,z1,z133,z12,z4,z5]),(0,[z0,z443,z2,z19,z4,z5]),(0,[z165,z0,z2,z7,z4,z139]),(0,[z27,z0,z1,z7,z4,z89])],[(0,[z629,z1,z2,z12,z4,z5]),(0,[z759,z0,z1,z2,z4,z5]),(0,[z0,z1,z66,z760,z4,z5])],[(0,[z157,z0,z1,z7,z25,z5])],[(0,[z93,z102,z1,z7,z4,z5]),(0,[z215,z1,z761,z7,z4,z5]),(0,[z0,z1,z2,z762,z4,z5])]],
   [[(0,[z0,z1,z2,z763,z4,z5]),(0,[z0,z1,z764,z2,z4,z5]),(0,[z84,z1,z2,z477,z4,z5]),(0,[z0,z1,z2,z765,z4,z5]),(0,[z215,z1,z2,z7,z766,z5])],[],[(0,[z0,z1,z2,z767,z4,z5]),(0,[z510,z1,z2,z12,z4,z5]),(0,[z21,z1,z2,z402,z4,z34])],[(0,[z0,z1,z183,z3,z4,z5]),(0,[z0,z1,z2,z144,z4,z5]),(0,[z0,z1,z2,z768,z4,z5])],[(0,[z157,z1,z133,z7,z9,z5]),(0,[z303,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z769,z4,z5]),(0,[z0,z209,z2,z66,z4,z5]),(0,[z0,z1,z2,z770,z4,z5])],[(0,[z0,z1,z2,z771,z4,z5]),(0,[z0,z1,z2,z4,z772,z5]),(0,[z0,z276,z2,z7,z675,z5]),(0,[z0,z1,z2,z7,z4,z773]),(0,[z64,z1,z2,z318,z4,z5])],[(0,[z0,z1,z2,z12,z4,z309]),(0,[z0,z1,z44,z3,z4,z5]),(0,[z0,z1,z2,z413,z4,z32]),(1,[z1,z2,z7,z4,z746]),(0,[z0,z2,z774,z43,z4,z5]),(0,[z100,z0,z1,z2,z4,z596]),(0,[z0,z1,z2,z775,z4,z5])],[(0,[z0,z189,z44,z7,z4,z5]),(0,[z776,z1,z2,z7,z4,z5]),(0,[z0,z1,z7,z94,z5,z409])]],
   [[(0,[z0,z1,z777,z7,z4,z5]),(0,[z0,z1,z2,z778,z4,z5]),(0,[z0,z1,z2,z7,z779,z5]),(0,[z0,z1,z12,z4,z5,z101]),(0,[z0,z115,z2,z158,z4,z5]),(0,[z0,z1,z2,z4,z5,z780]),(0,[z781,z1,z2,z7,z4,z5]),(0,[z782,z1,z2,z7,z4,z5]),(0,[z611,z0,z1,z7,z4,z5])],[(0,[z0,z1,z2,z144,z387,z5]),(0,[z0,z1,z7,z4,z5,z783]),(0,[z0,z1,z2,z254,z4,z5]),(0,[z0,z1,z2,z784,z4,z5]),(0,[z0,z1,z2,z318,z4,z406]),(0,[z0,z785,z2,z7,z4,z5])],[(0,[z0,z1,z2,z786,z4,z5]),(0,[z0,z1,z44,z202,z4,z5]),(0,[z0,z1,z2,z4,z5,z787]),(0,[z0,z209,z2,z81,z4,z5]),(0,[z788,z1,z2,z7,z4,z5])],[(1,[z789,z1,z7,z4,z5]),(0,[z1,z2,z12,z4,z514,z5]),(0,[z0,z1,z790,z7,z4,z5]),(0,[z0,z1,z2,z4,z791,z5]),(0,[z93,z1,z2,z7,z4,z406])],[(0,[z0,z1,z323,z12,z4,z5]),(0,[z128,z2,z212,z83,z4,z5]),(0,[z1,z2,z302,z12,z9,z5]),(0,[z93,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z792,z4,z5]),(0,[z0,z271,z2,z43,z4,z5]),(0,[z0,z1,z2,z7,z4,z793]),(0,[z0,z1,z2,z794,z4,z5]),(0,[z27,z0,z1,z7,z4,z721])],[(0,[z226,z0,z1,z2,z97,z5]),(0,[z0,z1,z2,z7,z795,z5]),(0,[z796,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z797,z4,z5]),(0,[z119,z0,z1,z4,z257,z5])],[(0,[z680,z87,z2,z7,z4,z5]),(0,[z0,z1,z130,z224,z4,z5]),(0,[z27,z0,z1,z7,z4,z444]),(0,[z0,z1,z7,z4,z132,z333])],[(0,[z0,z798,z2,z12,z4,z5]),(0,[z84,z1,z2,z3,z60,z5]),(0,[z0,z1,z2,z7,z799,z5]),(0,[z0,z180,z2,z318,z4,z5]),(0,[z0,z1,z2,z800,z4,z5]),(0,[z0,z1,z24,z7,z735,z5])]],
   [[(0,[z0,z1,z2,z801,z4,z5]),(0,[z0,z802,z2,z7,z4,z5]),(0,[z433,z1,z2,z3,z4,z5]),(0,[z215,z189,z2,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z803]),(0,[z0,z1,z2,z7,z804,z5])],[(0,[z0,z189,z2,z402,z4,z5]),(0,[z0,z1,z2,z7,z4,z746]),(0,[z0,z1,z2,z7,z4,z805]),(0,[z93,z1,z2,z265,z4,z5])],[(0,[z0,z180,z2,z7,z60,z5]),(0,[z0,z1,z192,z402,z4,z5]),(0,[z0,z806,z2,z7,z4,z5]),(0,[z0,z807,z2,z7,z4,z5]),(0,[z0,z1,z2,z808,z4,z5]),(0,[z0,z1,z2,z809,z4,z5])],[(0,[z0,z707,z152,z7,z4,z5]),(0,[z810,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z811,z4,z5])],[(0,[z0,z1,z2,z83,z294,z5]),(0,[z1,z2,z12,z4,z535,z5]),(0,[z0,z812,z1,z7,z4,z5]),(0,[z0,z1,z2,z813,z4,z5]),(0,[z0,z1,z501,z81,z4,z5]),(0,[z215,z138,z2,z7,z4,z139]),(0,[z0,z1,z130,z635,z4,z5])],[],[(0,[z0,z1,z2,z12,z4,z107]),(0,[z86,z2,z814,z7,z4,z5]),(0,[z0,z789,z1,z7,z4,z5]),(0,[z1,z2,z7,z4,z5,z815]),(0,[z0,z1,z2,z816,z4,z5])],[(0,[z0,z1,z817,z7,z4,z5]),(0,[z241,z0,z1,z156,z4,z5]),(0,[z818,z0,z2,z7,z4,z5]),(0,[z0,z1,z2,z819,z4,z5]),(0,[z0,z1,z2,z18,z4,z820])]],
   [[(0,[z0,z1,z2,z83,z308,z5]),(0,[z0,z1,z2,z821,z4,z5]),(0,[z267,z0,z1,z2,z3,z233]),(0,[z0,z1,z2,z822,z4,z5]),(0,[z0,z1,z2,z318,z4,z444]),(0,[z611,z0,z1,z7,z4,z132])],[(0,[z0,z1,z2,z7,z4,z823]),(0,[z147,z0,z2,z12,z178,z5]),(0,[z64,z1,z2,z824,z4,z5]),(0,[z825,z0,z1,z7,z4,z5])],[(0,[z0,z1,z2,z826,z4,z5]),(0,[z0,z1,z827,z7,z4,z5]),(0,[z0,z1,z2,z828,z4,z5]),(0,[z0,z1,z2,z4,z829,z5]),(0,[z70,z1,z2,z4,z13,z5])],[(0,[z0,z1,z2,z7,z830,z5]),(0,[z80,z102,z1,z176,z4,z5])],[(0,[z93,z1,z2,z7,z150,z5]),(0,[z484,z1,z2,z12,z4,z5]),(0,[z393,z1,z2,z3,z4,z5])],[(0,[z0,z831,z2,z7,z4,z5]),(0,[z0,z1,z2,z72,z4,z5]),(0,[z1,z2,z12,z9,z178,z5]),(0,[z46,z0,z2,z7,z178,z5]),(0,[z138,z0,z2,z7,z4,z805]),(0,[z157,z93,z1,z7,z25,z5]),(0,[z267,z289,z0,z1,z2,z233])],[(0,[z0,z832,z1,z7,z4,z5]),(0,[z74,z0,z707,z7,z4,z5]),(0,[z0,z1,z2,z833,z4,z5]),(0,[z834,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z18,z4,z13])],[(0,[z0,z1,z2,z7,z835,z5]),(0,[z33,z1,z2,z12,z4,z205]),(0,[z0,z1,z130,z760,z4,z5]),(0,[z0,z1,z2,z836,z4,z5])]],
   [[(0,[z0,z837,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z838]),(0,[z303,z1,z2,z7,z4,z5]),(0,[z84,z1,z2,z12,z9,z5]),(0,[z0,z1,z2,z839,z4,z5])],[(0,[z0,z1,z2,z7,z840,z5])],[(0,[z0,z841,z2,z7,z4,z5]),(0,[z0,z1,z2,z842,z4,z5]),(0,[z0,z1,z2,z4,z5,z843]),(0,[z844,z0,z1,z2,z4,z5])],[(0,[z226,z0,z1,z2,z293,z5]),(0,[z510,z1,z2,z7,z60,z5])],[(0,[z0,z1,z2,z774,z4,z5]),(0,[z0,z1,z7,z4,z845,z5])],[(0,[z0,z1,z846,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z847]),(0,[z193,z1,z2,z12,z4,z5]),(0,[z123,z1,z2,z12,z4,z5]),(0,[z0,z209,z2,z18,z4,z5])],[(0,[z0,z1,z323,z7,z4,z309]),(0,[z0,z2,z212,z7,z4,z107]),(0,[z0,z1,z2,z318,z4,z5])],[(0,[z128,z2,z814,z7,z4,z5]),(0,[z0,z1,z65,z487,z4,z5]),(0,[z0,z2,z774,z7,z4,z5]),(0,[z848,z1,z2,z7,z4,z5]),(0,[z0,z1,z849,z7,z4,z5]),(0,[z0,z1,z2,z4,z5,z850])]],
   [[(0,[z0,z1,z2,z851,z4,z5]),(0,[z0,z1,z2,z852,z4,z5]),(0,[z226,z1,z2,z12,z9,z5]),(0,[z124,z1,z2,z727,z4,z5]),(0,[z0,z1,z2,z18,z4,z161]),(0,[z0,z1,z761,z7,z4,z5]),(0,[z1,z35,z2,z4,z5,z330])],[(0,[z0,z1,z2,z7,z4,z853]),(0,[z0,z1,z854,z7,z4,z5]),(0,[z64,z1,z2,z7,z4,z406]),(0,[z0,z1,z2,z7,z5,z713]),(0,[z0,z1,z2,z855,z4,z5])],[(0,[z0,z1,z2,z7,z856,z5]),(0,[z0,z1,z2,z857,z4,z5]),(0,[z0,z1,z2,z176,z150,z5]),(0,[z64,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z3,z329,z5]),(0,[z0,z858,z2,z3,z4,z5]),(0,[z1,z2,z7,z4,z859,z5]),(0,[z21,z1,z2,z7,z4,z34]),(0,[z0,z1,z7,z4,z5,z860]),(0,[z215,z1,z2,z7,z804,z5])],[(0,[z0,z798,z2,z7,z4,z5]),(0,[z0,z1,z396,z324,z4,z5]),(0,[z0,z189,z2,z7,z329,z5])],[(0,[z0,z1,z2,z7,z861,z5]),(0,[z0,z1,z2,z862,z4,z5]),(0,[z0,z63,z2,z7,z4,z142]),(0,[z863,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z735,z5]),(0,[z0,z864,z2,z7,z4,z5])],[(0,[z0,z1,z2,z3,z294,z5]),(0,[z467,z1,z2,z12,z4,z5]),(0,[z93,z1,z2,z7,z60,z5]),(0,[z0,z1,z2,z4,z865,z5]),(0,[z0,z1,z2,z866,z4,z5])],[(0,[z0,z1,z2,z313,z4,z5]),(0,[z0,z1,z2,z867,z4,z5]),(0,[z0,z1,z868,z7,z4,z5]),(0,[z0,z1,z2,z7,z869,z5]),(0,[z1,z2,z7,z4,z205,z373]),(0,[z1,z2,z727,z12,z4,z5]),(0,[z0,z1,z2,z12,z4,z406]),(0,[z0,z1,z2,z202,z329,z5]),(0,[z0,z152,z75,z7,z4,z5]),(0,[z0,z624,z2,z16,z4,z5]),(0,[z147,z0,z2,z7,z731,z5])],[(0,[z0,z87,z2,z7,z4,z107]),(0,[z0,z1,z2,z870,z4,z5]),(0,[z0,z1,z2,z871,z4,z5]),(0,[z475,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z302,z109,z5]),(0,[z0,z1,z2,z3,z125,z116]),(0,[z872,z0,z2,z7,z4,z5]),(0,[z64,z180,z2,z7,z4,z5])]],
   [[(0,[z86,z87,z2,z12,z4,z5]),(0,[z80,z102,z1,z12,z4,z5]),(0,[z0,z102,z1,z7,z4,z444]),(0,[z0,z581,z2,z3,z4,z5]),(0,[z1,z2,z7,z4,z5,z746])],[(0,[z0,z1,z2,z3,z308,z5]),(0,[z0,z1,z2,z873,z4,z5]),(0,[z874,z1,z2,z7,z4,z5]),(0,[z465,z0,z1,z2,z97,z5]),(0,[z0,z1,z2,z875,z4,z5])],[(0,[z215,z2,z212,z7,z4,z5]),(0,[z0,z876,z2,z7,z4,z5])],[(0,[z87,z189,z2,z7,z4,z5]),(0,[z0,z1,z555,z7,z94,z5]),(0,[z877,z0,z1,z7,z4,z5]),(0,[z0,z180,z2,z7,z4,z406]),(0,[z0,z1,z2,z4,z878,z5])],[(0,[z0,z180,z2,z12,z4,z5]),(0,[z138,z0,z2,z3,z4,z139]),(0,[z177,z1,z2,z477,z9,z5]),(0,[z0,z1,z2,z4,z5,z879])],[(0,[z0,z443,z2,z43,z4,z5]),(0,[z489,z0,z1,z2,z4,z6]),(0,[z173,z74,z0,z7,z4,z5]),(0,[z0,z2,z307,z4,z5,z139]),(0,[z138,z0,z2,z4,z36,z139]),(0,[z0,z1,z2,z880,z4,z5])],[(0,[z0,z1,z323,z7,z4,z107]),(0,[z0,z1,z2,z176,z4,z5]),(0,[z177,z1,z2,z7,z9,z5]),(0,[z881,z0,z1,z7,z4,z5]),(0,[z882,z1,z2,z7,z4,z5])],[(0,[z0,z1,z883,z7,z4,z5]),(0,[z0,z1,z2,z884,z4,z5])]],
   [[(0,[z1,z2,z12,z4,z612,z5]),(0,[z0,z106,z1,z224,z4,z5]),(0,[z64,z1,z2,z7,z4,z444])],[(0,[z21,z1,z2,z7,z4,z107]),(0,[z0,z1,z2,z885,z4,z5]),(0,[z0,z1,z24,z12,z94,z5]),(0,[z84,z85,z1,z7,z60,z5]),(0,[z0,z674,z2,z43,z4,z5]),(0,[z886,z1,z2,z7,z4,z5])],[(0,[z0,z1,z887,z7,z4,z5]),(0,[z0,z1,z2,z888,z4,z5]),(0,[z0,z1,z2,z824,z4,z5]),(0,[z0,z1,z2,z889,z4,z5]),(0,[z0,z1,z2,z4,z5,z890]),(0,[z891,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z7,z4,z892]),(0,[z0,z1,z2,z893,z4,z5])],[(0,[z215,z87,z2,z7,z4,z5]),(0,[z102,z789,z1,z7,z4,z5]),(0,[z0,z209,z2,z12,z4,z5]),(0,[z0,z894,z2,z7,z4,z5]),(0,[z21,z1,z44,z7,z4,z34]),(0,[z0,z1,z2,z55,z4,z5]),(0,[z0,z1,z2,z7,z5,z895]),(0,[z896,z1,z2,z7,z4,z5]),(0,[z100,z0,z1,z2,z4,z17])],[(0,[z0,z897,z2,z7,z4,z5]),(0,[z898,z0,z1,z2,z7,z4]),(0,[z0,z1,z2,z176,z387,z5]),(0,[z0,z1,z2,z195,z4,z5]),(1,[z0,z2,z774,z4,z5]),(0,[z0,z1,z2,z7,z677,z116])],[(0,[z0,z1,z2,z12,z4,z444]),(0,[z215,z1,z2,z7,z4,z34]),(0,[z0,z1,z2,z899,z4,z5]),(0,[z0,z1,z2,z109,z5,z311])],[(0,[z1,z2,z3,z547,z4,z5]),(0,[z0,z90,z2,z774,z4,z5])],[(0,[z0,z1,z2,z232,z4,z309]),(0,[z0,z1,z2,z12,z150,z5]),(1,[z0,z2,z7,z731,z5]),(0,[z1,z900,z2,z4,z5,z330])]],
   [[(0,[z0,z1,z2,z12,z448,z5]),(0,[z0,z741,z2,z3,z4,z5]),(0,[z0,z1,z2,z901,z4,z5])],[(0,[z0,z1,z2,z902,z4,z5]),(0,[z0,z189,z2,z3,z4,z5]),(0,[z227,z0,z1,z2,z328,z5]),(0,[z84,z1,z2,z7,z859,z5]),(0,[z41,z0,z1,z2,z343,z5]),(0,[z0,z1,z2,z903,z4,z5])],[(0,[z0,z1,z2,z53,z369,z5]),(0,[z611,z0,z1,z7,z9,z5]),(0,[z0,z1,z2,z904,z4,z5]),(0,[z0,z1,z2,z905,z4,z5]),(0,[z0,z1,z2,z265,z4,z444]),(0,[z906,z0,z1,z2,z4,z5]),(0,[z0,z1,z907,z7,z4,z5])],[(0,[z0,z1,z2,z908,z4,z5]),(0,[z909,z1,z2,z7,z4,z5]),(1,[z0,z1,z2,z7,z713])],[(0,[z226,z1,z2,z7,z9,z5]),(0,[z41,z303,z1,z2,z97,z5])],[(0,[z0,z1,z323,z232,z4,z5]),(0,[z0,z1,z396,z7,z4,z5]),(0,[z21,z22,z2,z7,z4,z34]),(0,[z910,z0,z1,z7,z4,z5]),(0,[z0,z1,z760,z7,z4,z5]),(0,[z0,z1,z2,z911,z4,z5])],[(0,[z64,z1,z2,z7,z4,z5]),(0,[z349,z1,z2,z12,z4,z5]),(0,[z1,z2,z403,z3,z4,z5]),(0,[z70,z1,z2,z3,z4,z5]),(0,[z665,z1,z2,z3,z4,z5]),(1,[z0,z707,z7,z4,z5]),(0,[z0,z1,z2,z307,z4,z5]),(0,[z0,z1,z2,z912,z4,z5])],[(0,[z157,z0,z1,z7,z374,z5]),(0,[z1,z2,z185,z12,z4,z5]),(0,[z1,z2,z12,z125,z9,z5]),(0,[z0,z1,z2,z913,z4,z5])]],
   [[(0,[z0,z1,z2,z914,z4,z5]),(0,[z0,z915,z2,z7,z4,z5]),(0,[z1,z2,z3,z12,z4,z5]),(0,[z0,z916,z2,z7,z4,z5]),(0,[z0,z1,z917,z7,z4,z5]),(0,[z0,z1,z2,z918,z4,z5]),(0,[z0,z919,z1,z7,z4,z5]),(0,[z0,z1,z920,z7,z4,z5]),(0,[z0,z581,z2,z265,z4,z5])],[(0,[z157,z0,z1,z3,z25,z5]),(0,[z0,z1,z2,z4,z5,z921]),(0,[z0,z1,z2,z53,z109,z5]),(0,[z0,z1,z2,z7,z4,z820])],[(0,[z0,z1,z2,z7,z4,z406]),(0,[z922,z1,z2,z7,z4,z5])],[(0,[z0,z1,z2,z12,z4,z5]),(0,[z0,z1,z923,z7,z4,z5]),(1,[z0,z1,z2,z722,z5]),(0,[z0,z1,z2,z4,z820,z17])],[(0,[z215,z1,z2,z7,z4,z107]),(0,[z0,z1,z2,z924,z4,z5]),(0,[z1,z2,z3,z4,z5,z330]),(0,[z0,z1,z2,z925,z4,z5]),(0,[z0,z1,z2,z926,z4,z5])],[(0,[z0,z1,z2,z4,z927,z5]),(0,[z71,z1,z133,z442,z4,z5]),(0,[z157,z1,z2,z12,z9,z5]),(0,[z0,z276,z2,z12,z8,z5]),(0,[z0,z1,z2,z324,z4,z5]),(0,[z0,z1,z928,z7,z4,z5]),(0,[z1,z2,z929,z7,z4,z5])],[(0,[z0,z1,z2,z258,z4,z5]),(0,[z1,z2,z12,z4,z9,z5]),(0,[z0,z1,z2,z930,z12,z4])],[(0,[z0,z1,z2,z931,z4,z5]),(0,[z0,z1,z2,z932,z4,z5]),(0,[z0,z1,z2,z933,z4,z5]),(0,[z0,z191,z2,z43,z4,z5]),(0,[z0,z1,z2,z934,z4,z5])]],
   [[(0,[z0,z1,z2,z935,z4,z5]),(0,[z0,z180,z2,z7,z4,z5]),(0,[z0,z35,z2,z43,z4,z5]),(0,[z0,z245,z1,z66,z4,z5]),(0,[z1,z2,z7,z4,z936,z5]),(0,[z0,z1,z2,z265,z4,z5])],[(0,[z0,z1,z2,z937,z4,z5]),(0,[z0,z1,z2,z54,z4,z5]),(0,[z41,z70,z1,z2,z97,z5])],[(0,[z128,z2,z212,z7,z4,z309]),(0,[z0,z1,z2,z938,z4,z5]),(0,[z0,z1,z2,z7,z939,z5]),(0,[z1,z2,z12,z4,z328,z5])],[(0,[z0,z1,z2,z940,z4,z5]),(0,[z0,z738,z2,z7,z4,z5]),(0,[z0,z22,z2,z3,z4,z5]),(0,[z611,z0,z1,z3,z4,z5]),(0,[z1,z2,z7,z859,z9,z5])],[(0,[z0,z1,z2,z7,z4,z941]),(0,[z0,z1,z2,z7,z942,z5]),(0,[z0,z1,z35,z2,z4,z5]),(0,[z0,z943,z2,z7,z4,z5]),(0,[z93,z180,z2,z7,z4,z5]),(0,[z70,z1,z2,z4,z97,z5])],[(0,[z0,z22,z192,z7,z4,z5]),(0,[z0,z1,z2,z944,z4,z5]),(0,[z93,z1,z2,z945,z4,z5]),(0,[z0,z1,z24,z7,z94,z5])],[(0,[z86,z87,z2,z313,z4,z5]),(0,[z0,z1,z2,z946,z4,z5])],[(0,[z174,z1,z2,z12,z4,z5]),(0,[z340,z1,z2,z7,z9,z5]),(0,[z0,z22,z2,z202,z4,z5]),(0,[z0,z209,z2,z7,z4,z5]),(0,[z0,z1,z2,z947,z4,z5])]],
   [[(1,[z1,z2,z7,z859,z5]),(0,[z0,z948,z2,z7,z4,z5]),(0,[z0,z1,z2,z949,z4,z5]),(0,[z950,z1,z2,z7,z4,z5])],[(0,[z0,z1,z183,z12,z4,z5]),(0,[z0,z1,z2,z951,z4,z5]),(0,[z0,z85,z1,z7,z9,z5])],[(1,[z2,z814,z7,z4,z5]),(0,[z87,z2,z7,z4,z5,z367]),(0,[z952,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z953,z4,z5]),(0,[z0,z1,z2,z954,z4,z5]),(0,[z0,z1,z2,z7,z713,z233])],[(0,[z71,z1,z133,z7,z4,z5]),(0,[z0,z1,z2,z7,z150,z5]),(0,[z84,z85,z1,z12,z4,z5]),(0,[z955,z1,z2,z7,z4,z5]),(0,[z956,z1,z2,z7,z4,z5])],[(0,[z0,z1,z44,z12,z4,z5])],[(0,[z1,z2,z7,z4,z5,z957]),(0,[z93,z1,z2,z7,z4,z444])],[(0,[z0,z1,z2,z7,z308,z309]),(0,[z0,z1,z2,z7,z60,z444]),(0,[z0,z1,z2,z7,z958,z5])],[(0,[z84,z1,z396,z7,z60,z5]),(0,[z21,z1,z2,z7,z329,z34]),(0,[z0,z63,z2,z7,z4,z805]),(0,[z959,z1,z2,z7,z4,z5])]],
   [[(0,[z422,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z7,z4,z960]),(0,[z0,z90,z2,z43,z4,z5])],[(0,[z0,z1,z2,z961,z4,z5]),(0,[z0,z2,z962,z7,z4,z5]),(0,[z0,z1,z2,z376,z4,z5]),(0,[z0,z581,z2,z318,z4,z5])],[(0,[z128,z2,z212,z7,z4,z107]),(0,[z963,z1,z2,z7,z4,z5])],[(0,[z155,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z964,z4,z5]),(0,[z0,z1,z965,z2,z4,z5]),(0,[z93,z581,z2,z7,z4,z5]),(0,[z0,z1,z2,z4,z5,z966]),(0,[z0,z1,z2,z967,z4,z5])],[(0,[z0,z1,z323,z7,z308,z5]),(0,[z0,z1,z968,z7,z4,z5]),(0,[z1,z2,z12,z8,z9,z5]),(0,[z15,z0,z2,z4,z5,z210]),(0,[z64,z1,z2,z969,z4,z5]),(0,[z157,z0,z581,z7,z25,z5])],[(0,[z0,z1,z2,z7,z4,z309]),(0,[z0,z1,z2,z7,z970,z5]),(0,[z0,z1,z2,z971,z4,z5]),(0,[z215,z1,z2,z12,z4,z5]),(0,[z692,z0,z2,z16,z4,z5]),(0,[z0,z1,z2,z972,z4,z5])],[(0,[z0,z1,z2,z973,z4,z5]),(0,[z0,z1,z2,z974,z4,z5]),(0,[z85,z1,z133,z7,z4,z5]),(0,[z0,z1,z2,z975,z4,z5])],[(0,[z87,z2,z7,z4,z205,z139]),(0,[z1,z2,z496,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z976]),(0,[z1,z2,z176,z4,z9,z5]),(0,[z661,z1,z2,z12,z4,z5]),(0,[z84,z1,z2,z258,z60,z5]),(0,[z0,z1,z2,z977,z4,z5])],[(0,[z0,z1,z2,z978,z4,z5]),(0,[z0,z1,z2,z979,z4,z5]),(0,[z0,z980,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z981]),(0,[z0,z1,z2,z7,z982,z5])],[(0,[z428,z0,z2,z7,z4,z139]),(0,[z0,z85,z1,z3,z4,z5]),(0,[z0,z1,z2,z983,z7,z5]),(0,[z0,z1,z2,z7,z731,z5])],[(0,[z0,z1,z323,z7,z4,z5]),(0,[z0,z1,z2,z984,z4,z5]),(0,[z93,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z985,z4,z5]),(0,[z303,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z986,z4,z5])],[(0,[z0,z1,z2,z7,z987,z5]),(0,[z0,z1,z2,z988,z4,z5]),(0,[z377,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z989,z4,z5]),(0,[z990,z0,z1,z2,z4,z5])],[(0,[z0,z1,z2,z930,z7,z4]),(0,[z0,z1,z2,z991,z4,z5]),(0,[z291,z1,z2,z12,z4,z5])],[(0,[z0,z1,z2,z992,z4,z5]),(0,[z284,z0,z2,z206,z4,z5]),(0,[z0,z1,z2,z993,z4,z5]),(0,[z0,z994,z1,z7,z4,z5]),(0,[z215,z1,z35,z2,z4,z5])],[(0,[z0,z1,z2,z995,z4,z5]),(0,[z71,z789,z1,z7,z4,z5]),(0,[z0,z1,z192,z7,z329,z5]),(0,[z215,z1,z2,z7,z4,z205]),(0,[z996,z0,z1,z2,z7,z5])]],
   [[(0,[z128,z323,z212,z7,z4,z5]),(0,[z71,z1,z133,z534,z4,z5]),(0,[z80,z85,z1,z7,z4,z5]),(0,[z997,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z108,z4,z13]),(0,[z1,z2,z7,z4,z205,z746])],[(0,[z0,z1,z2,z7,z4,z998]),(0,[z0,z63,z2,z7,z4,z470]),(0,[z0,z1,z999,z7,z4,z5]),(0,[z289,z0,z1,z2,z4,z5])],[(0,[z1000,z0,z1,z2,z7,z5]),(0,[z0,z1,z2,z4,z1001,z5]),(0,[z0,z35,z209,z2,z4,z5]),(0,[z0,z1,z2,z7,z1002,z5])],[(0,[z0,z1,z183,z7,z4,z309])],[(0,[z0,z1,z2,z1003,z4,z5]),(0,[z0,z1004,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z107]),(0,[z128,z189,z2,z7,z4,z5]),(0,[z1,z2,z12,z4,z306,z5]),(0,[z21,z1,z2,z3,z4,z34]),(0,[z0,z135,z2,z3,z4,z5]),(0,[z1005,z0,z1,z2,z7,z5]),(0,[z0,z1006,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z1007]),(0,[z789,z1,z2,z7,z4,z5]),(0,[z1,z2,z924,z12,z4,z5]),(0,[z21,z189,z2,z7,z4,z34]),(0,[z119,z70,z1,z2,z4,z5]),(0,[z0,z1,z2,z1008,z4,z5])],[(0,[z21,z1,z192,z7,z4,z34]),(0,[z0,z1,z2,z402,z448,z5]),(0,[z0,z1,z2,z7,z4,z1009]),(0,[z0,z1,z2,z4,z1010,z5]),(0,[z0,z1,z2,z1011,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z1012,z5]),(0,[z174,z1,z2,z7,z60,z5]),(0,[z147,z0,z2,z7,z178,z5])],[(0,[z0,z152,z75,z3,z4,z5]),(0,[z0,z90,z2,z158,z4,z5]),(0,[z21,z1,z2,z202,z4,z34])],[(0,[z0,z1013,z2,z7,z4,z5]),(0,[z84,z1,z2,z7,z542,z5])],[(0,[z128,z2,z212,z12,z4,z5]),(0,[z0,z1,z2,z1014,z4,z5]),(0,[z0,z1,z7,z4,z5,z1015]),(0,[z100,z0,z209,z2,z4,z17])],[(0,[z14,z0,z2,z16,z4,z5])],[(0,[z339,z0,z1,z2,z4,z17]),(0,[z1,z2,z7,z4,z746,z34]),(0,[z0,z152,z75,z195,z4,z5])],[(0,[z119,z0,z1,z88,z4,z5]),(0,[z0,z1,z1016,z7,z4,z5]),(0,[z33,z1,z2,z7,z4,z205])],[(0,[z1017,z0,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z1018,z5]),(0,[z1019,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z1020,z4,z5]),(0,[z0,z1021,z2,z7,z4,z5])]],
   [[(0,[z0,z1,z2,z12,z329,z5]),(0,[z173,z74,z0,z3,z4,z5]),(0,[z0,z1,z2,z1022,z4,z5])],[(0,[z215,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z1023,z4,z5]),(0,[z84,z1,z396,z12,z4,z5]),(0,[z338,z1,z2,z12,z4,z5]),(0,[z553,z1,z2,z12,z4,z5]),(0,[z177,z1,z2,z3,z9,z5]),(0,[z1,z2,z4,z1024,z5,z330]),(0,[z64,z581,z2,z7,z4,z5]),(0,[z157,z0,z180,z7,z25,z5])],[(0,[z0,z1,z2,z1025,z4,z5]),(0,[z0,z1,z2,z402,z4,z5]),(0,[z0,z90,z209,z2,z4,z5]),(0,[z0,z1,z2,z1026,z4,z5]),(0,[z0,z1,z1027,z7,z4,z5])],[(0,[z0,z1,z183,z7,z4,z107]),(0,[z0,z1,z2,z12,z294,z5]),(0,[z0,z1,z2,z1028,z4,z5]),(0,[z80,z102,z1,z7,z150,z5]),(0,[z0,z1,z2,z1029,z4,z5]),(0,[z0,z1,z2,z1030,z4,z5]),(0,[z0,z1031,z2,z7,z4,z5]),(0,[z0,z1,z2,z1032,z4,z5])],[(0,[z0,z1,z2,z232,z4,z5]),(0,[z361,z0,z2,z7,z4,z139]),(0,[z1033,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z1034,z4,z5]),(0,[z0,z1,z2,z760,z4,z5])],[(0,[z0,z1,z2,z12,z125,z116]),(0,[z0,z1,z192,z3,z4,z5]),(0,[z0,z1,z2,z969,z4,z5]),(0,[z138,z0,z2,z307,z4,z139]),(0,[z0,z180,z2,z7,z4,z444]),(0,[z0,z581,z2,z7,z4,z406]),(0,[z0,z1,z7,z4,z721,z89]),(0,[z0,z1,z2,z7,z116,z713])],[(0,[z0,z581,z2,z12,z4,z5]),(0,[z1,z2,z12,z4,z5,z164]),(0,[z0,z189,z192,z7,z4,z5]),(0,[z611,z289,z0,z1,z4,z5])],[(0,[z0,z1,z1035,z7,z4,z5]),(0,[z0,z1,z2,z12,z308,z5]),(0,[z0,z1,z1036,z7,z4,z5]),(0,[z124,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z1037,z4,z5]),(0,[z353,z1,z2,z12,z4,z5]),(0,[z611,z0,z1,z7,z60,z5]),(0,[z0,z209,z2,z109,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z4,z1038]),(0,[z0,z1,z2,z1039,z4,z5]),(0,[z0,z189,z2,z202,z4,z5]),(0,[z0,z707,z75,z7,z4,z5]),(0,[z0,z1,z2,z1040,z4,z5]),(0,[z0,z1041,z2,z7,z4,z5])],[(0,[z0,z1,z2,z1042,z4,z5]),(0,[z222,z1,z2,z12,z4,z5]),(0,[z0,z1,z192,z202,z4,z5]),(0,[z1043,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z1044,z5])],[(0,[z138,z0,z2,z12,z4,z139]),(0,[z27,z0,z1,z3,z4,z89]),(0,[z1045,z1,z2,z7,z4,z5])],[(1,[z1,z2,z727,z4,z5]),(0,[z1,z2,z12,z4,z181,z5]),(0,[z0,z1,z1046,z7,z4,z5]),(0,[z0,z1,z2,z7,z125,z211]),(0,[z0,z1047,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z1048])],[(0,[z0,z1,z2,z1049,z4,z5]),(0,[z157,z0,z1,z7,z551,z5]),(0,[z0,z1,z2,z1050,z4,z5])],[(0,[z0,z1,z2,z1051,z4,z5]),(0,[z0,z1,z2,z7,z1052,z5]),(0,[z1,z2,z727,z7,z4,z5]),(0,[z0,z1,z2,z1053,z4,z5]),(0,[z33,z1,z2,z61,z4,z205]),(0,[z0,z1054,z1,z2,z4,z5])],[(0,[z84,z1,z2,z176,z4,z5]),(1,[z0,z1,z760,z4,z5]),(0,[z0,z1,z2,z7,z4,z713])],[(0,[z86,z87,z2,z7,z4,z5]),(0,[z80,z102,z1,z7,z4,z5]),(0,[z0,z556,z2,z7,z8,z5]),(0,[z1055,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z1056,z4,z5])]],
   [[(0,[z0,z1,z2,z7,z1057,z5]),(0,[z0,z2,z7,z4,z1058,z5]),(0,[z255,z102,z1,z7,z4,z5]),(0,[z1059,z0,z1,z2,z12,z4]),(0,[z267,z0,z1,z2,z12,z233]),(0,[z0,z1,z396,z3,z4,z5]),(0,[z0,z1,z2,z1060,z4,z5]),(0,[z0,z1061,z1,z2,z4,z5])],[(0,[z1,z2,z7,z4,z205,z107]),(0,[z64,z1,z2,z3,z4,z5]),(0,[z0,z1,z1062,z2,z4,z5]),(0,[z0,z1,z2,z1063,z4,z5]),(0,[z0,z1,z2,z223,z4,z5])],[(0,[z0,z1,z2,z232,z4,z107]),(0,[z0,z1,z3,z4,z5,z101])],[(0,[z0,z1,z2,z1064,z4,z5]),(0,[z0,z915,z2,z3,z4,z5]),(0,[z0,z1,z2,z18,z4,z32]),(0,[z0,z1,z44,z402,z4,z5])],[(0,[z0,z1,z2,z12,z387,z5]),(0,[z15,z0,z2,z206,z4,z5]),(0,[z0,z1,z2,z7,z4,z1065]),(0,[z0,z63,z2,z307,z4,z5]),(0,[z0,z1,z2,z945,z4,z5])],[(0,[z0,z1,z2,z7,z1066,z5]),(0,[z80,z102,z1,z7,z387,z5]),(0,[z0,z1067,z2,z12,z4,z5]),(0,[z14,z0,z2,z360,z4,z5]),(0,[z0,z1,z2,z163,z4,z5]),(0,[z0,z2,z7,z4,z142,z805]),(0,[z70,z1,z2,z185,z4,z5])],[(0,[z0,z1,z2,z1068,z4,z5]),(0,[z0,z1,z2,z1069,z4,z5]),(0,[z0,z1,z2,z727,z4,z5]),(0,[z0,z1,z2,z4,z5,z427])],[(0,[z128,z2,z212,z7,z4,z5]),(0,[z0,z1,z2,z83,z4,z309]),(0,[z0,z1,z2,z1070,z4,z5]),(0,[z1,z2,z3,z498,z4,z5]),(0,[z1071,z0,z1,z2,z4,z5]),(0,[z70,z1,z2,z43,z4,z5])]],
   [[(0,[z0,z1,z1072,z7,z4,z5]),(0,[z0,z1,z2,z4,z5,z820])],[(0,[z0,z1,z2,z1073,z4,z5]),(0,[z672,z0,z2,z7,z178,z5]),(0,[z0,z1,z2,z1074,z4,z5])],[(0,[z0,z1,z2,z7,z1075,z5]),(0,[z0,z1,z2,z1076,z4,z5]),(0,[z0,z1,z2,z1077,z4,z5]),(0,[z0,z1,z1078,z7,z4,z5])],[(0,[z608,z0,z1,z88,z4,z5]),(0,[z0,z1,z65,z81,z4,z5]),(0,[z41,z0,z1,z2,z569,z5]),(0,[z289,z0,z1,z4,z5,z101])],[(0,[z0,z1,z2,z7,z1079,z5]),(0,[z0,z1,z2,z442,z4,z5]),(0,[z0,z1080,z1,z2,z4,z5]),(0,[z0,z1081,z2,z7,z4,z5]),(0,[z70,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z1082,z4,z5]),(0,[z0,z1,z1083,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z444]),(0,[z0,z1,z2,z1084,z4,z5]),(1,[z0,z1,z2,z4,z820])],[(0,[z0,z1,z323,z83,z4,z5]),(0,[z0,z1,z2,z7,z294,z309]),(0,[z0,z1,z2,z1085,z4,z5]),(0,[z0,z1,z2,z1086,z4,z5]),(0,[z255,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z4,z5,z1087]),(0,[z0,z1,z2,z1088,z4,z5])],[(0,[z0,z1,z2,z7,z4,z1089]),(0,[z0,z1,z24,z7,z573,z5]),(0,[z0,z85,z1,z7,z60,z5]),(0,[z670,z0,z2,z7,z4,z139])],[(0,[z0,z1,z2,z7,z4,z1090]),(0,[z0,z1,z2,z7,z448,z5]),(0,[z173,z0,z707,z7,z4,z5]),(0,[z100,z0,z1,z2,z4,z517]),(0,[z0,z1,z2,z4,z13,z642]),(0,[z1091,z1,z2,z7,z4,z5]),(0,[z0,z209,z2,z4,z5,z17])]],
   [[(0,[z0,z1,z2,z7,z1092,z5]),(0,[z0,z1,z2,z1093,z4,z5]),(0,[z157,z0,z1,z254,z25,z5])],[(0,[z0,z1,z2,z7,z1094,z5]),(0,[z1095,z1,z2,z7,z4,z5])],[(0,[z0,z1,z1096,z2,z4,z5]),(0,[z0,z581,z2,z7,z4,z5]),(0,[z215,z1,z2,z1097,z4,z5]),(0,[z1,z2,z4,z36,z5,z330]),(0,[z0,z1,z7,z4,z735,z5])],[(0,[z0,z1,z2,z7,z308,z5]),(0,[z0,z1,z323,z7,z294,z5]),(0,[z0,z1,z2,z1098,z4,z5]),(0,[z0,z1,z2,z1099,z4,z5])],[(0,[z84,z1,z2,z924,z4,z5]),(0,[z0,z1,z2,z7,z4,z1100]),(0,[z157,z0,z1,z265,z25,z5]),(0,[z0,z1,z2,z1101,z4,z5]),(0,[z100,z0,z135,z2,z4,z17])],[(0,[z0,z1,z2,z4,z1102,z5]),(0,[z93,z1,z2,z7,z9,z5]),(0,[z119,z0,z1,z760,z4,z5])],[(0,[z71,z1,z133,z3,z4,z5]),(0,[z0,z1,z2,z1103,z4,z5]),(0,[z0,z1,z2,z7,z859,z5]),(0,[z1104,z1,z2,z7,z4,z5]),(0,[z1105,z1,z2,z7,z4,z5]),(0,[z0,z1,z1106,z7,z4,z5])],[(0,[z0,z1,z2,z83,z4,z107]),(0,[z0,z1,z2,z7,z4,z1107]),(0,[z0,z1,z2,z1108,z4,z5]),(0,[z0,z1,z2,z7,z4,z1109]),(0,[z0,z1,z2,z302,z445,z5]),(0,[z0,z1,z2,z691,z4,z13])]],
   [[(0,[z0,z2,z814,z7,z4,z5]),(0,[z86,z87,z2,z239,z4,z5]),(0,[z0,z1110,z1,z7,z4,z5]),(0,[z84,z1,z2,z12,z60,z5]),(0,[z0,z1,z2,z1111,z4,z5]),(0,[z0,z1,z2,z477,z4,z5])],[(0,[z0,z1,z2,z7,z4,z1112]),(0,[z0,z1,z2,z1113,z4,z5]),(0,[z0,z22,z2,z12,z4,z5]),(0,[z611,z0,z1,z12,z4,z5]),(0,[z0,z1,z7,z4,z132,z444])],[(0,[z0,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z1114,z5]),(0,[z80,z789,z1,z7,z4,z5]),(0,[z84,z1,z2,z324,z60,z5])],[(0,[z0,z1,z2,z1115,z4,z5]),(0,[z0,z1,z2,z1116,z4,z5]),(0,[z0,z1,z2,z4,z13,z820])],[(0,[z0,z2,z962,z3,z4,z5]),(0,[z15,z0,z2,z774,z4,z5]),(0,[z0,z276,z2,z7,z8,z5]),(0,[z1117,z0,z1,z2,z4,z5]),(0,[z1118,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z722,z97,z5])],[(0,[z0,z1,z2,z7,z1119,z5]),(0,[z0,z1,z1120,z7,z4,z5]),(0,[z0,z1,z2,z7,z294,z107]),(0,[z657,z1,z2,z3,z4,z5]),(0,[z28,z0,z1,z2,z7,z233]),(0,[z0,z1,z1121,z7,z4,z5])],[(0,[z0,z1,z2,z1122,z4,z5]),(0,[z0,z1,z2,z1123,z4,z5]),(0,[z0,z1124,z2,z7,z4,z5]),(0,[z0,z1,z2,z1125,z4,z5]),(0,[z33,z1,z2,z72,z4,z205]),(0,[z0,z1,z2,z259,z109,z5]),(0,[z0,z1,z2,z4,z5,z1126]),(0,[z70,z1,z2,z53,z4,z5]),(0,[z0,z1,z2,z4,z5,z1127])],[(0,[z1059,z0,z1,z2,z7,z4]),(0,[z0,z1,z2,z1128,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z309]),(0,[z0,z1,z2,z7,z387,z5]),(0,[z0,z1,z44,z7,z448,z5])],[(0,[z0,z1,z2,z7,z308,z107]),(0,[z0,z1,z2,z7,z1129,z5]),(0,[z0,z1,z2,z7,z1130,z5]),(0,[z0,z1067,z2,z7,z4,z5]),(0,[z267,z0,z1,z7,z101,z233])],[(0,[z0,z189,z2,z7,z4,z34]),(0,[z0,z2,z7,z4,z805,z139]),(0,[z0,z1131,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z4,z1132]),(0,[z1133,z0,z2,z7,z4,z5]),(0,[z0,z2,z12,z4,z5,z1134]),(0,[z0,z707,z2,z7,z4,z5]),(0,[z0,z1,z2,z1135,z4,z5])],[(0,[z128,z2,z212,z232,z4,z5]),(0,[z1,z2,z12,z9,z5,z233]),(0,[z462,z1,z2,z12,z4,z5])],[(0,[z177,z1,z2,z7,z859,z5]),(0,[z0,z1,z130,z81,z4,z5]),(0,[z0,z1,z760,z81,z4,z5])],[(0,[z0,z1,z323,z3,z4,z5]),(0,[z0,z1,z2,z1136,z4,z5]),(0,[z93,z1,z2,z3,z4,z5]),(0,[z0,z276,z2,z7,z731,z5]),(0,[z1137,z1,z2,z7,z4,z5])],[(0,[z274,z1,z2,z7,z9,z5]),(0,[z0,z1,z2,z402,z329,z5]),(0,[z0,z1,z2,z7,z4,z1138]),(0,[z138,z2,z7,z4,z330,z139]),(0,[z0,z1,z2,z53,z190,z5])]],
   [[(0,[z0,z1,z183,z7,z4,z5]),(0,[z70,z1,z2,z7,z4,z5]),(0,[z0,z1,z2,z1139,z4,z5])],[(0,[z0,z1,z2,z1140,z4,z5]),(0,[z0,z1,z2,z61,z4,z5])],[(0,[z1,z2,z814,z7,z4,z5]),(0,[z1,z2,z488,z12,z4,z5]),(0,[z0,z22,z2,z7,z448,z5]),(0,[z352,z1,z2,z7,z4,z205]),(0,[z1141,z1,z2,z7,z4,z5])],[(0,[z0,z1,z44,z7,z4,z5]),(0,[z0,z1,z2,z1142,z4,z5]),(0,[z0,z1,z2,z109,z615,z5]),(0,[z0,z1,z7,z94,z735,z5])],[(0,[z0,z1,z2,z232,z294,z5]),(0,[z0,z1,z2,z1143,z4,z5])],[(0,[z0,z1,z2,z1144,z4,z5]),(0,[z872,z0,z2,z3,z4,z5]),(0,[z0,z1,z1145,z7,z4,z5]),(0,[z157,z0,z1,z318,z25,z5])],[(0,[z241,z0,z1,z66,z4,z5]),(0,[z0,z1,z2,z1146,z4,z5])],[(0,[z0,z1,z2,z534,z4,z5]),(0,[z0,z152,z75,z55,z4,z5])]],
   [[(0,[z0,z1,z2,z232,z308,z5]),(0,[z0,z1,z2,z3,z4,z107]),(0,[z0,z1,z2,z1147,z4,z5]),(0,[z0,z1,z2,z7,z1148,z5]),(0,[z0,z85,z1,z12,z4,z5]),(0,[z505,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z1149,z4,z5]),(0,[z0,z1,z2,z4,z13,z565])],[(0,[z0,z1,z2,z1150,z4,z5]),(0,[z0,z1151,z2,z7,z4,z5]),(0,[z0,z102,z180,z7,z4,z5])],[(0,[z0,z1,z2,z7,z1152,z5]),(0,[z1,z2,z12,z4,z5,z330]),(0,[z0,z85,z1,z324,z4,z5]),(0,[z0,z1,z1153,z7,z4,z5]),(0,[z0,z1,z1154,z7,z4,z5]),(0,[z0,z1,z4,z5,z427,z101])],[(0,[z0,z1,z2,z239,z4,z5]),(0,[z93,z1,z133,z7,z4,z5]),(0,[z147,z0,z2,z3,z178,z5]),(0,[z0,z85,z1,z258,z4,z5]),(0,[z0,z1,z11,z81,z4,z5]),(0,[z0,z1,z1155,z7,z4,z5])],[(0,[z0,z365,z75,z7,z4,z5]),(0,[z0,z1,z2,z4,z1024,z5]),(0,[z84,z1,z2,z7,z60,z5]),(0,[z303,z1,z2,z258,z4,z5])],[(0,[z0,z22,z2,z7,z4,z5]),(0,[z0,z1,z2,z1156,z4,z5])],[(0,[z681,z1,z2,z12,z4,z5]),(0,[z1157,z0,z1,z7,z4,z5]),(0,[z0,z1,z2,z1158,z4,z5]),(0,[z0,z1,z2,z1159,z4,z5]),(0,[z157,z0,z1,z7,z735,z5])],[(0,[z0,z1160,z2,z7,z4,z5]),(0,[z1,z2,z519,z12,z4,z5]),(0,[z0,z1,z2,z7,z1161,z5]),(0,[z0,z1,z2,z1162,z4,z5])]],
   [[(0,[z0,z1,z2,z1163,z4,z5]),(0,[z280,z0,z1,z7,z4,z89]),(0,[z339,z0,z1,z2,z4,z216]),(0,[z0,z1,z2,z4,z5,z1164]),(0,[z0,z1,z2,z1165,z4,z5]),(0,[z0,z1,z2,z7,z1166,z5])],[(0,[z0,z1,z2,z1167,z4,z5]),(0,[z0,z1,z2,z1168,z4,z5]),(0,[z33,z1,z2,z3,z4,z205]),(0,[z1169,z1,z2,z7,z4,z5]),(0,[z0,z1170,z2,z7,z4,z5])],[(0,[z0,z1,z2,z7,z1171,z5]),(0,[z0,z1,z1172,z7,z4,z5]),(0,[z157,z0,z1,z7,z682,z5]),(0,[z1017,z0,z2,z3,z4,z5]),(0,[z100,z0,z1,z2,z4,z6]),(0,[z93,z1,z2,z784,z4,z5])],[(0,[z0,z1,z1173,z7,z4,z5]),(0,[z21,z1,z2,z12,z4,z34]),(0,[z0,z135,z2,z12,z4,z5]),(0,[z41,z0,z1,z2,z328,z5]),(0,[z0,z1,z2,z1097,z4,z5]),(0,[z157,z64,z1,z7,z25,z5])],[(0,[z215,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z357,z4,z5])],[(0,[z0,z2,z7,z4,z5,z1134]),(0,[z0,z1,z2,z1174,z4,z5]),(0,[z0,z180,z2,z7,z9,z5]),(0,[z15,z0,z2,z16,z4,z5]),(0,[z0,z2,z7,z731,z178,z5]),(0,[z0,z671,z2,z7,z4,z139]),(0,[z215,z1,z2,z4,z36,z5]),(0,[z0,z1,z320,z81,z4,z5]),(0,[z41,z0,z209,z2,z4,z5])],[(0,[z789,z1,z133,z7,z4,z5]),(0,[z304,z1,z2,z3,z4,z5]),(0,[z0,z405,z2,z7,z4,z142]),(0,[z0,z1,z2,z4,z5,z1175]),(0,[z0,z276,z2,z357,z8,z5]),(0,[z275,z0,z1,z66,z4,z5]),(0,[z0,z2,z7,z4,z5,z1176])],[(0,[z128,z2,z212,z7,z294,z5]),(0,[z0,z152,z75,z12,z4,z5]),(0,[z0,z1,z2,z7,z4,z1177]),(0,[z215,z1,z747,z7,z4,z5]),(0,[z215,z1,z2,z748,z4,z5]),(0,[z0,z1178,z2,z7,z4,z5]),(0,[z0,z1,z7,z735,z25,z5])]],
   [[(0,[z0,z2,z16,z774,z4,z5]),(0,[z0,z1,z2,z1179,z4,z5]),(0,[z0,z1,z2,z7,z5,z1180]),(0,[z267,z0,z1,z2,z7,z713])],[(0,[z546,z1,z2,z12,z4,z5]),(0,[z1,z2,z49,z3,z4,z5])],[(0,[z532,z1,z2,z7,z9,z5]),(0,[z0,z1,z900,z2,z4,z5])],[(0,[z128,z2,z212,z7,z308,z5]),(0,[z0,z1,z2,z108,z4,z394]),(0,[z0,z1181,z2,z7,z4,z5]),(0,[z1,z2,z7,z60,z859,z5]),(0,[z267,z0,z1,z2,z427,z233])],[(0,[z0,z1,z2,z7,z4,z1182]),(0,[z0,z1,z2,z1183,z4,z5]),(0,[z0,z260,z75,z7,z4,z5]),(0,[z0,z1,z2,z7,z4,z1184]),(0,[z138,z0,z2,z163,z4,z139]),(0,[z267,z611,z0,z1,z7,z233])],[(0,[z0,z1,z183,z232,z4,z5]),(0,[z0,z1,z2,z1185,z4,z5]),(0,[z21,z1,z2,z7,z4,z746]),(0,[z0,z1186,z2,z7,z4,z5])],[(0,[z173,z74,z0,z12,z4,z5]),(0,[z0,z1,z1187,z7,z4,z5]),(0,[z1,z2,z3,z727,z4,z5]),(0,[z0,z1,z2,z7,z9,z444]),(0,[z0,z22,z44,z7,z4,z5]),(0,[z0,z1,z2,z1188,z4,z5]),(0,[z0,z1,z2,z7,z4,z1189]),(0,[z138,z0,z35,z2,z4,z139])],[(0,[z177,z1,z2,z12,z9,z5]),(0,[z0,z2,z7,z4,z5,z1190]),(0,[z1191,z1,z2,z7,z4,z5]),(0,[z1192,z1,z2,z7,z4,z5]),(0,[z0,z581,z2,z7,z4,z444]),(0,[z100,z0,z1,z2,z4,z494])]],
   [[(0,[z0,z1,z2,z7,z1193,z5]),(0,[z0,z1,z2,z3,z4,z406])],[(0,[z2,z814,z212,z7,z4,z5]),(0,[z70,z1,z2,z16,z4,z5]),(0,[z0,z1,z2,z1194,z4,z5]),(0,[z0,z1,z516,z66,z4,z5])],[(0,[z86,z87,z2,z3,z4,z5]),(0,[z80,z102,z1,z3,z4,z5]),(0,[z0,z189,z2,z12,z4,z5]),(0,[z113,z1,z2,z12,z4,z5]),(0,[z0,z1,z2,z1195,z4,z5]),(0,[z0,z1,z2,z1196,z4,z5]),(0,[z0,z1,z2,z1197,z4,z5])],[(0,[z0,z1,z192,z12,z4,z5]),(0,[z0,z2,z7,z4,z5,z805]),(0,[z0,z1,z2,z1198,z4,z5]),(0,[z41,z0,z1,z2,z722,z5])],[(0,[z0,z1,z2,z83,z4,z5]),(0,[z1,z2,z7,z4,z5,z330]),(0,[z0,z85,z1,z7,z4,z5]),(0,[z193,z1,z133,z7,z4,z5]),(0,[z1,z2,z7,z150,z9,z5]),(0,[z1,z2,z99,z3,z4,z5]),(0,[z21,z1,z2,z7,z448,z34]),(0,[z15,z0,z35,z2,z4,z5]),(0,[z0,z2,z7,z4,z731,z5])],[(0,[z0,z1,z2,z1199,z4,z5]),(0,[z408,z102,z1,z7,z4,z5]),(0,[z177,z1,z2,z54,z9,z5]),(0,[z0,z1,z2,z1200,z4,z5]),(0,[z0,z1,z2,z7,z4,z721])],[(0,[z0,z180,z2,z3,z4,z5]),(0,[z0,z1,z2,z1201,z4,z5]),(0,[z604,z0,z1,z2,z7,z233])],[(0,[z0,z858,z2,z7,z4,z5]),(0,[z0,z1,z2,z7,z329,z5]),(0,[z70,z1,z130,z2,z4,z5]),(0,[z0,z1,z7,z4,z5,z101])]],
   [[(0,[z575,z1,z2,z12,z4,z5]),(0,[z27,z0,z1,z12,z4,z89]),(0,[z124,z1,z2,z258,z4,z5]),(0,[z93,z85,z1,z7,z4,z5]),(0,[z0,z1,z2,z1202,z4,z5]),(0,[z0,z22,z2,z402,z4,z5]),(0,[z0,z667,z2,z43,z4,z5]),(0,[z41,z0,z1,z2,z272,z5])],[(0,[z0,z1,z2,z1203,z4,z5]),(0,[z0,z1,z1204,z7,z4,z5]),(0,[z0,z1,z2,z1205,z4,z5]),(0,[z0,z473,z2,z16,z4,z5]),(0,[z157,z0,z1,z7,z25,z406]),(0,[z0,z1,z7,z4,z5,z1206]),(0,[z100,z0,z1,z2,z4,z820]),(0,[z0,z1,z2,z1207,z4,z5]),(0,[z0,z1,z2,z1208,z4,z5])],[(0,[z0,z1,z2,z7,z294,z5]),(0,[z128,z2,z212,z3,z4,z5]),(0,[z157,z0,z1,z12,z25,z5]),(0,[z0,z1,z2,z1209,z4,z5]),(0,[z1,z2,z12,z4,z5,z410]),(0,[z0,z1,z2,z1210,z4,z5]),(0,[z670,z0,z1,z2,z4,z17]),(0,[z15,z0,z2,z415,z4,z5])],[(0,[z0,z1211,z2,z7,z4,z5]),(0,[z0,z1,z24,z3,z94,z5]),(0,[z0,z1,z2,z1212,z4,z5]),(0,[z0,z1,z1213,z2,z4,z5])],[(0,[z0,z1,z2,z1214,z4,z5]),(0,[z301,z1,z133,z7,z4,z5]),(0,[z0,z189,z2,z7,z4,z205]),(0,[z0,z1,z2,z1215,z4,z5]),(0,[z0,z1,z2,z7,z125,z116])],[(0,[z0,z1,z1216,z7,z4,z5]),(0,[z87,z2,z814,z7,z4,z5]),(0,[z1,z24,z2,z12,z9,z5]),(0,[z0,z209,z2,z3,z4,z5]),(0,[z1217,z0,z1,z2,z4,z5]),(0,[z0,z2,z43,z4,z5,z517]),(0,[z0,z1,z2,z1218,z4,z5]),(0,[z0,z1,z2,z109,z722,z5])],[(0,[z84,z1,z2,z12,z4,z5]),(0,[z0,z1,z396,z12,z4,z5]),(0,[z0,z1,z2,z185,z369,z5]),(0,[z0,z1,z2,z1219,z4,z5]),(1,[z0,z2,z7,z4,z805]),(0,[z0,z1,z2,z7,z766,z5])],[(0,[z128,z183,z212,z7,z4,z5]),(0,[z0,z1,z1220,z7,z4,z5]),(0,[z0,z1,z2,z3,z4,z444]),(0,[z1,z2,z477,z4,z9,z5]),(0,[z0,z1,z1221,z7,z4,z5]),(0,[z0,z135,z2,z7,z4,z5]),(0,[z93,z1,z2,z318,z4,z5]),(0,[z100,z70,z1,z2,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 529) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 529).take 532) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1061).take 168) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1229)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [529, 532, 168] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 114).take 117).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 231).take 25).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [114, 117, 25] = true :=
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

end PEqualNP.Outside.L_meta_37845

theorem PEqualNP.Outside.L_meta_37845 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4276811968) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37845.solve