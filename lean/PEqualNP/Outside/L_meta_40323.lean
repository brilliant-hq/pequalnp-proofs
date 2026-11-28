import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40323

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
  Nat.testBit (4276808936 * 2 ^ 32 + 4276153536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x1021660d88e33cc4#64 ++ 0x21021660d88e33cc#64 ++ 0xf067ee1f89e77cc7#64 ++ 0xdf067ee1f89e77cc#64 : BitVec 256),
   (0x008b00a28a280558#64 ++ 0x4008b00a28a28055#64 ++ 0x719b13e38e388fff#64 ++ 0xb719b13e38e388ff#64 : BitVec 256),
   (0x061418543015d0a2#64 ++ 0x8061418543015d0a#64 ++ 0xde1c1c7c703ff0ff#64 ++ 0x7de1c1c7c703ff0f#64 : BitVec 256),
   (0x0b601f005540ea03#64 ++ 0x00b601f005540ea0#64 ++ 0xbfe01f807fc0ff0e#64 ++ 0xfbfe01f807fc0ff0#64 : BitVec 256),
   (0x2ddfa0006fbe000c#64 ++ 0x02ddfa0006fbe000#64 ++ 0xafffe0007fff000d#64 ++ 0xfafffe0007fff000#64 : BitVec 256),
   (0x4ffedffb00000000#64 ++ 0x04ffedffb0000000#64 ++ 0x4fffffff80000003#64 ++ 0xf4fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 4]⟩, ⟨.or, [6, 1]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [0, 5]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [7, 2]⟩, ⟨.or, [11, 10]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [7, 13]⟩, ⟨.and, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000000000000000 0x0000000000000000 0x318013800e008f0e 0xb318013800e008f0

def z1 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x719b13e38e388fff 0xb719b13e38e388ff

def z2 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde1c1c7c703ff0ff 0x7de1c1c7c703ff0f

def z3 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z4 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067ee1f89e77cc7 0xdf067ee1f89e77cc

def z5 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafffe0007fff000d 0xfafffe0007fff000

def z6 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z7 : W := mkw 0x29cba0004faa000c 0x029cba0004faa000 0xafe3e0007fc0000c 0xfafe3e0007fc0000

def z8 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fffffff80000003 0xf4fffffff8000000

def z9 : W := mkw 0x0415200028b60004 0x00415200028b6000 0xae7fe00079ff000d 0xfae7fe00079ff000

def z10 : W := mkw 0x49eac7ab00000000 0x049eac7ab0000000 0x41e7ef9f80000003 0xd41e7ef9f8000000

def z11 : W := mkw 0x0020460900000000 0x0002046090000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z12 : W := mkw 0x1b617f0ddde3fec7 0x21b617f0ddde3fec 0xffe7ff9fffe7ffcf 0xfffe7ff9fffe7ffc

def z13 : W := mkw 0x44bec6fb00000000 0x044bec6fb0000000 0x407fee7f80000003 0xd407fee7f8000000

def z14 : W := mkw 0x0b4019005540ea03 0x00b4019005540ea0 0xbf8011807fc0ff0c 0x2bf8011807fc0ff0

def z15 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb000000009e77cc4 0x0b000000009e77cc

def z16 : W := mkw 0x4fde99f200000000 0x04fde99f20000000 0x0f9811e000000000 0x20f9811e00000000

def z17 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xfffff3e3ffff8fff 0xffffff3e3ffff8ff

def z18 : W := mkw 0x4ffedfff3015d0a2 0x84ffedfff3015d0a 0xdffffffff03ff0ff 0xfdffffffff03ff0f

def z19 : W := mkw 0x200120006fbe000c 0x0200120006fbe000 0xa00000007fff000c 0x0a00000007fff000

def z20 : W := mkw 0x0614185000000000 0x0061418500000000 0x4e1c1c7c00000003 0x74e1c1c7c0000000

def z21 : W := mkw 0x0940000045000000 0x0094000004500000 0xafe000007fc0000c 0xfafe000007fc0000

def z22 : W := mkw 0x3d75e60dedf73cc4 0x23d75e60dedf73cc 0xfe67ee1ff9e77cc7 0xdfe67ee1ff9e77cc

def z23 : W := mkw 0x008a00a200000000 0x0008a00a20000000 0x419b13e380000003 0xb419b13e38000000

def z24 : W := mkw 0x2d55a0006fbe000c 0x02d55a0006fbe000 0xae64e0007fff000c 0x4ae64e0007fff000

def z25 : W := mkw 0x020018543015d0a2 0x8020018543015d0a 0xd0001c7c703ff0fe 0x0d0001c7c703ff0f

def z26 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x8e600c0071c07000 0x48e600c0071c0700

def z27 : W := mkw 0x10ab66af8aeb3ddc 0x610ab66af8aeb3dd 0xf1ffffff8fffffff 0xff1ffffff8ffffff

def z28 : W := mkw 0x0bea1fa25748eb1b 0x40bea1fa25748eb1 0xbff81fe07fd8ff3e 0xfbff81fe07fd8ff3

def z29 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0x8064ec1c01c77000 0x48064ec1c01c7700

def z30 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x501b1063803880ff 0x3501b1063803880f

def z31 : W := mkw 0x4ffedffb45402a01 0x04ffedffb45402a0 0x6fffffff8fc00f03 0xf6fffffff8fc00f0

def z32 : W := mkw 0x1001600d88a314c4 0x21001600d88a314c 0x4007e01f802700c1 0x04007e01f802700c

def z33 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x401fe07f80000001 0x0401fe07f8000000

def z34 : W := mkw 0x46bedffb00000000 0x046bedffb0000000 0x401fffff80000003 0x0401fffff8000000

def z35 : W := mkw 0x0001200008a20004 0x00001200008a2000 0xa067e00009e70005 0xda067e00009e7000

def z36 : W := mkw 0x3dffe60defff3ccc 0x23dffe60defff3cc 0xffffee1fffff7ccf 0xfffffee1fffff7cc

def z37 : W := mkw 0x1001200488a314c4 0x21001200488a314c 0x00000000002700c0 0x000000000002700c

def z38 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x8e040c1c70077000 0x48e040c1c7007700

def z39 : W := mkw 0x0bca19a25708c31b 0x40bca19a25708c31 0x0f9811e076188338 0x20f9811e07618833

def z40 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e64e00071c70000 0x48e64e00071c7000

def z41 : W := mkw 0x4beadfab00000000 0x04beadfab0000000 0x0fe3ff8380000002 0xf0fe3ff838000000

def z42 : W := mkw 0x0414000020140000 0x0041400002014000 0x8e1c0000703f000d 0x78e1c0000703f000

def z43 : W := mkw 0x2fdfb8547fbfd0ae 0x82fdfb8547fbfd0a 0xfffffc7c7ffff0ff 0xffffffc7c7ffff0f

def z44 : W := mkw 0x49eac7ab00000000 0x049eac7ab0000000 0x01e3e38380000000 0x801e3e3838000000

def z45 : W := mkw 0x0000000000000000 0x0000000000000000 0x10000000003880fc 0x010000000003880f

def z46 : W := mkw 0x0020060000402800 0x0002006000040280 0x80600c0001c07000 0x480600c0001c0700

def z47 : W := mkw 0x19616709cde22e45 0x219616709cde22e4 0x21e3e3838fc00f00 0x821e3e3838fc00f0

def z48 : W := mkw 0x008b20a28aaa055c 0x4008b20a28aaa055 0xf1fff3e38fff8fff 0xff1fff3e38fff8ff

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0x40180060003800f1 0x040180060003800f

def z50 : W := mkw 0x000000a280000550 0x4000000a28000055 0x40000063800000f0 0x040000063800000f

def z51 : W := mkw 0x061418503014c022 0x8061418503014c02 0x5e181060703880ff 0x35e181060703880f

def z52 : W := mkw 0x0f741f547555faa3 0x80f741f547555faa 0xfffc1ffc7fffffff 0xffffc1ffc7ffffff

def z53 : W := mkw 0x02201f541041faa3 0x802201f541041faa 0x50001ffc0000fff2 0x050001ffc0000fff

def z54 : W := mkw 0x0000000000000000 0x0000000000000000 0x40040c1c00000003 0x540040c1c0000000

def z55 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xcffffffff1c07003 0xfcffffffff1c0700

def z56 : W := mkw 0x2dde8000671c0008 0x02dde8000671c000 0x0f98000076180008 0x20f9800007618000

def z57 : W := mkw 0x000000043015d0a2 0x8000000043015d0a 0xd0181060703ff0ff 0x3d0181060703ff0f

def z58 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x0e64ec1c00000000 0x40e64ec1c0000000

def z59 : W := mkw 0x0960070045402a01 0x00960070045402a0 0x21e003800fc00f00 0x821e003800fc00f0

def z60 : W := mkw 0x30012004efff3ccc 0x230012004efff3cc 0xb00000007fff7ccc 0x0b00000007fff7cc

def z61 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x218303838e000f00 0x8218303838e000f0

def z62 : W := mkw 0x2f74bf0075d6ea07 0x02f74bf0075d6ea0 0xbfe4ff807fc7ff0e 0xfbfe4ff807fc7ff0

def z63 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf07ffe7f89fffcff 0xff07ffe7f89fffcf

def z64 : W := mkw 0x39ebe60dcfeb3ccc 0x239ebe60dcfeb3cc 0xf1e7ee1f8fe77cc7 0xdf1e7ee1f8fe77cc

def z65 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x718313e38e008ff2 0x8718313e38e008ff

def z66 : W := mkw 0x2bebbf005feaea0f 0x02bebbf005feaea0 0xbfe3ff807fc0ff0e 0xfbfe3ff807fc0ff0

def z67 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x0f9fe000763f0009 0x20f9fe000763f000

def z68 : W := mkw 0x008b00a20a280008 0x0008b00a20a28000 0x619b13e38e38000f 0xb619b13e38e38000

def z69 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xfffff0607fff80ff 0xffffff0607fff80f

def z70 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xafffe383ffff0f0d 0xfafffe383ffff0f0

def z71 : W := mkw 0x4ffedffb02080118 0x44ffedffb0208011 0x4fffffff8618833b 0xf4fffffff8618833

def z72 : W := mkw 0x0414000020140000 0x0041400002014000 0x0e18000070180008 0x20e1800007018000

def z73 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x401b0063803800f1 0x0401b0063803800f

def z74 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xefffe063ffff00fd 0xfefffe063ffff00f

def z75 : W := mkw 0x0000000080000440 0x0000000008000044 0x5000020380000cc2 0x05000020380000cc

def z76 : W := mkw 0x469ed8fb00000000 0x0469ed8fb0000000 0x4e1ffc7f80000003 0x74e1ffc7f8000000

def z77 : W := mkw 0x02201f001040ea03 0x002201f001040ea0 0x10001f800000ff02 0x010001f800000ff0

def z78 : W := mkw 0x249fa0002abe000c 0x0249fa0002abe000 0x001fe000003f0001 0x0001fe000003f000

def z79 : W := mkw 0x0b613f005de2ea07 0x00b613f005de2ea0 0xbfe7ff807fe7ff0f 0xfbfe7ff807fe7ff0

def z80 : W := mkw 0x000100a288200550 0x4000100a28820055 0x700313e388208ff7 0x9700313e388208ff

def z81 : W := mkw 0x06345e5d3015d0a2 0x806345e5d3015d0a 0xde7ffe7ff03ff0ff 0xfde7ffe7ff03ff0f

def z82 : W := mkw 0x3021660defff3ccc 0x23021660defff3cc 0xf067ee1fffff7ccf 0xdf067ee1fffff7cc

def z83 : W := mkw 0x0dde80a200000000 0x00dde80a20000000 0x4ffff3e380000003 0xf4ffff3e38000000

def z84 : W := mkw 0x1021660988e22c44 0x21021660988e22c4 0x2063e20389c00c00 0x82063e20389c00c0

def z85 : W := mkw 0x0001000088200440 0x0000100008820044 0x701b126388388cff 0xb701b126388388cf

def z86 : W := mkw 0x020018541001d0a2 0x8020018541001d0a 0x50001c7c0000f0f2 0x050001c7c0000f0f

def z87 : W := mkw 0x200120006fbe000c 0x0200120006fbe000 0xa067e0007fff000d 0xda067e0007fff000

def z88 : W := mkw 0x6ffefffb65960004 0x06ffefffb6596000 0xcffffffff1c70003 0xfcffffffff1c7000

def z89 : W := mkw 0x020018001000c002 0x0020018001000c00 0x9e001c007000f00e 0x79e001c007000f00

def z90 : W := mkw 0x2fffbf007ffeea0f 0x02fffbf007ffeea0 0xbfffff807fffff0f 0xfbfffff807fffff0

def z91 : W := mkw 0x4ffedffb00402800 0x04ffedffb0040280 0xffffffff89c07c07 0xfffffffff89c07c0

def z92 : W := mkw 0x0000000000000000 0x0000000000000000 0x0067e00000000001 0xd0067e0000000000

def z93 : W := mkw 0x6ffffffb6fbe000c 0x06ffffffb6fbe000 0xefffffffffff000f 0xfefffffffffff000

def z94 : W := mkw 0x0000200000820004 0x0000020000082000 0x8064e00001c70000 0x48064e00001c7000

def z95 : W := mkw 0x008b00000a280008 0x0008b00000a28000 0x219b00000e38000d 0xb219b00000e38000

def z96 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0x6067e21f89e70cc1 0x86067e21f89e70cc

def z97 : W := mkw 0x49eac7ab45402a01 0x049eac7ab45402a0 0x21e3e3838fc00f00 0x821e3e3838fc00f0

def z98 : W := mkw 0x5fffffff88e33cc4 0x25fffffff88e33cc 0xffffffff89e77cc7 0xfffffffff89e77cc

def z99 : W := mkw 0x4ffedfff7555faa3 0x84ffedfff7555faa 0xffffffffffffffff 0xffffffffffffffff

def z100 : W := mkw 0x4ffedffb45000000 0x04ffedffb4500000 0xefffffffffc0000f 0xfefffffffffc0000

def z101 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x0fffe00000000001 0xf0fffe0000000000

def z102 : W := mkw 0x008a00a282080558 0x4008a00a28208055 0x519813e386188ffa 0x2519813e386188ff

def z103 : W := mkw 0x1000200400c33884 0x21000200400c3388 0x8000000001c77000 0x08000000001c7700

def z104 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xc067ec1f81e770c1 0x4c067ec1f81e770c

def z105 : W := mkw 0x000100008a280558 0x4000100008a28055 0x00000000003800f0 0x000000000003800f

def z106 : W := mkw 0x000100008a280558 0x4000100008a28055 0x300000000e388ffc 0x0300000000e388ff

def z107 : W := mkw 0x42205fff1001d0a2 0x842205fff1001d0a 0x50001fff8000f0f2 0x050001fff8000f0f

def z108 : W := mkw 0x0bcb19a2df28c75b 0x40bcb19a2df28c75 0x7f9b13e3fe388fff 0xb7f9b13e3fe388ff

def z109 : W := mkw 0x069e18f63015d0a2 0x8069e18f63015d0a 0xdf9f1ffff03ff0ff 0xfdf9f1ffff03ff0f

def z110 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xce1c1c7c70077003 0x7ce1c1c7c7007700

def z111 : W := mkw 0x2ddea00065960004 0x02ddea0006596000 0x8fffe00071c70001 0xf8fffe00071c7000

def z112 : W := mkw 0x000000a280000550 0x4000000a28000055 0x501813e380388fff 0x3501813e380388ff

def z113 : W := mkw 0x29cba0004faa000c 0x029cba0004faa000 0x21e3e0000fc00000 0x821e3e0000fc0000

def z114 : W := mkw 0x069f18543a3dd0aa 0x8069f18543a3dd0a 0xff9f1c7c7e3ff0ff 0xfff9f1c7c7e3ff0f

def z115 : W := mkw 0x000000047555faa3 0x8000000047555faa 0xb00000007ffffffc 0x0b00000007ffffff

def z116 : W := mkw 0x16357e5db8f7fce6 0xa16357e5db8f7fce 0xfe7ffe7ff9fffcff 0xffe7ffe7ff9fffcf

def z117 : W := mkw 0x6dffe7ab6fbe000c 0x06dffe7ab6fbe000 0xafffe383ffff000d 0xfafffe383ffff000

def z118 : W := mkw 0x0b40190000000000 0x00b4019000000000 0x0f80118000000000 0x20f8011800000000

def z119 : W := mkw 0x020018541001d0a2 0x8020018541001d0a 0xd0041c7c0027f0f7 0x5d0041c7c0027f0f

def z120 : W := mkw 0x4fffdffbdf68ef5b 0x44fffdffbdf68ef5 0xfffffffffff8ffff 0xffffffffffff8fff

def z121 : W := mkw 0x00ab46ab8a280558 0x400ab46ab8a28055 0x71ffffff8e388fff 0xf71ffffff8e388ff

def z122 : W := mkw 0x0001200008a20004 0x00001200008a2000 0xa000000009e70004 0x0a000000009e7000

def z123 : W := mkw 0x20012000efbe055c 0x420012000efbe055 0xb00000007fff8ffc 0x0b00000007fff8ff

def z124 : W := mkw 0x1001600d88a314c4 0x21001600d88a314c 0xd007ec1f802770c7 0x5d007ec1f802770c

def z125 : W := mkw 0x2dde8000671c0008 0x02dde8000671c000 0xaff800007fd8000c 0xfaff800007fd8000

def z126 : W := mkw 0x02ab1fa29a68ef5b 0x402ab1fa29a68ef5 0x719b1fe38e38ffff 0xb719b1fe38e38fff

def z127 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0x50000e1f80007cc2 0x050000e1f80007cc

def z128 : W := mkw 0x000000005540ea03 0x0000000005540ea0 0x8000000071c07000 0x08000000071c0700

def z129 : W := mkw 0x2ddfa000efbe055c 0x42ddfa000efbe055 0xbfffe0007fff8ffd 0xfbfffe0007fff8ff

def z130 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x4067ffff80000003 0xd4067ffff8000000

def z131 : W := mkw 0x4fffdffb8a280558 0x44fffdffb8a28055 0x6fffffff8e000f03 0xf6fffffff8e000f0

def z132 : W := mkw 0x0f741f507554ea23 0x80f741f507554ea2 0xbff81fe07fd8ff3e 0xfbff81fe07fd8ff3

def z133 : W := mkw 0x0001200408a31084 0x00001200408a3108 0xf067ec1c09e770c7 0xdf067ec1c09e770c

def z134 : W := mkw 0x000000005500c203 0x0000000005500c20 0x0000000076008308 0x0000000007600830

def z135 : W := mkw 0x0beb1fa2df68ef5b 0x40beb1fa2df68ef5 0xfffb1fe3fff8ffff 0xffffb1fe3fff8fff

def z136 : W := mkw 0x0001000088200440 0x0000100008820044 0x7003020388200cc7 0x97003020388200cc

def z137 : W := mkw 0x020018541001d0a2 0x8020018541001d0a 0x00000c1c00007000 0x000000c1c0000700

def z138 : W := mkw 0x4ffedffb1000c002 0x04ffedffb1000c00 0xdffffffff000f00f 0xfdffffffff000f00

def z139 : W := mkw 0x0f5419507514c223 0x80f5419507514c22 0x0f9811e076188338 0x20f9811e07618833

def z140 : W := mkw 0x2fffbf006fbe000c 0x02fffbf006fbe000 0xafffff807fff000f 0xfafffff807fff000

def z141 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xbffff3807fff8f0f 0xfbffff3807fff8f0

def z142 : W := mkw 0x449fc0fb8a280558 0x4449fc0fb8a28055 0x719ff3ff8e388fff 0xb719ff3ff8e388ff

def z143 : W := mkw 0x069f18f6ba3dd5fa 0xc069f18f6ba3dd5f 0xff9f1ffffe3fffff 0xfff9f1ffffe3ffff

def z144 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4e7fec7f80000001 0x44e7fec7f8000000

def z145 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbe600e0079c07c06 0xdbe600e0079c07c0

def z146 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x8e1c0c1c703f700d 0x78e1c0c1c703f700

def z147 : W := mkw 0x0414000000000000 0x0041400000000000 0x0e1c000000000001 0x70e1c00000000000

def z148 : W := mkw 0x0b605f0900000000 0x00b605f090000000 0x4fe7ff9f80000003 0xf4fe7ff9f8000000

def z149 : W := mkw 0x061418503014c022 0x8061418503014c02 0x0e18106070188038 0x20e1810607018803

def z150 : W := mkw 0x0000000400011080 0x0000000040001108 0xd0040c1c002770c7 0x5d0040c1c002770c

def z151 : W := mkw 0x4ffedffb20140000 0x04ffedffb2014000 0xcffffffff03f000f 0xfcffffffff03f000

def z152 : W := mkw 0x000000041001d0a2 0x8000000041001d0a 0x100000000000f0f0 0x0100000000000f0f

def z153 : W := mkw 0x294120006fbe000c 0x0294120006fbe000 0xafe000007fff000c 0xfafe000007fff000

def z154 : W := mkw 0x4dfec7fb00000000 0x04dfec7fb0000000 0x41ffe3ff80000001 0x841ffe3ff8000000

def z155 : W := mkw 0x10012004dde3fec7 0x210012004dde3fec 0xb00000007fe7ffcc 0x0b00000007fe7ffc

def z156 : W := mkw 0x4f74df595540ea03 0x04f74df595540ea0 0x8e64ec1c71c07000 0x48e64ec1c71c0700

def z157 : W := mkw 0x0ddfa00008a20004 0x00ddfa00008a2000 0xafffe00009e70005 0xfafffe00009e7000

def z158 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x0fe7ef9f80000000 0xc0fe7ef9f8000000

def z159 : W := mkw 0x02201fa29040ef53 0x402201fa29040ef5 0x50001fe38000fff2 0x050001fe38000fff

def z160 : W := mkw 0x008a00a200000000 0x0008a00a20000000 0x401b006380000001 0x0401b00638000000

def z161 : W := mkw 0x008a00a202080118 0x4008a00a20208011 0x019811e006188338 0x2019811e00618833

def z162 : W := mkw 0x2ddfa0a26fbe011c 0x42ddfa0a26fbe011 0xaffff1e07fff833d 0xfaffff1e07fff833

def z163 : W := mkw 0x1415605da8b714e4 0xa1415605da8b714e 0x401fe07f803f00f1 0x0401fe07f803f00f

def z164 : W := mkw 0x1021660988e22c44 0x21021660988e22c4 0xa067e20389e70c05 0xda067e20389e70c0

def z165 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0xb064ee1c09c77c06 0xdb064ee1c09c77c0

def z166 : W := mkw 0x4fffdffb8a280558 0x44fffdffb8a28055 0x7fffffff8e388fff 0xf7fffffff8e388ff

def z167 : W := mkw 0x16357e5d88e33cc4 0x216357e5d88e33cc 0xfe7ffe7f89e77cc7 0xffe7ffe7f89e77cc

def z168 : W := mkw 0x0dde800045000000 0x00dde80004500000 0xafffe0007fc0000d 0xfafffe0007fc0000

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x50181060003880ff 0x350181060003880f

def z170 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xa067ee1f89c77c00 0xca067ee1f89c77c0

def z171 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x8e7fe00071ff0001 0x48e7fe00071ff000

def z172 : W := mkw 0x4f74df5d3015d0a2 0x84f74df5d3015d0a 0x8e64ec1c70077000 0x48e64ec1c7007700

def z173 : W := mkw 0x1961660dcde33cc4 0x21961660dcde33cc 0xffe7ee1fffe77ccf 0xfffe7ee1fffe77cc

def z174 : W := mkw 0x4fffdfffba3dd5fa 0xc4fffdfffba3dd5f 0xfffffffffe3fffff 0xffffffffffe3ffff

def z175 : W := mkw 0x0021060088602c40 0x00021060088602c4 0xf0630e0389e07cc7 0xdf0630e0389e07cc

def z176 : W := mkw 0x269fb8543abfd0ae 0x8269fb8543abfd0a 0xde1ffc7c703ff0ff 0x7de1ffc7c703ff0f

def z177 : W := mkw 0x408ac0ab00000000 0x0408ac0ab0000000 0x0003e00380000000 0x00003e0038000000

def z178 : W := mkw 0x0000000400011080 0x0000000040001108 0x90000000002770c4 0x090000000002770c

def z179 : W := mkw 0x4fde99f63015d0a2 0x84fde99f63015d0a 0xdf9c1dfc703ff0ff 0x7df9c1dfc703ff0f

def z180 : W := mkw 0x000000043015d0a2 0x8000000043015d0a 0x90000000703ff0fc 0x090000000703ff0f

def z181 : W := mkw 0x0b601f005500c203 0x00b601f005500c20 0x0fe01f807600830a 0xf0fe01f807600830

def z182 : W := mkw 0x1021660988e22c44 0x21021660988e22c4 0x7063e20389e00cc7 0x97063e20389e00cc

def z183 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0xafe4e0007fc7000c 0xfafe4e0007fc7000

def z184 : W := mkw 0x061418f6b015d5f2 0xc061418f6b015d5f 0xde1c1ffff03fffff 0x7de1c1ffff03ffff

def z185 : W := mkw 0x0ddf80000a280008 0x00ddf80000a28000 0x2fffe0000e38000d 0xf2fffe0000e38000

def z186 : W := mkw 0x1020460980402c40 0x21020460980402c4 0x0000020380000c00 0x00000020380000c0

def z187 : W := mkw 0x200120002abe000c 0x0200120002abe000 0x00000000003f0000 0x000000000003f000

def z188 : W := mkw 0x1001200088e22c44 0x21001200088e22c4 0x2000000009c00c00 0x02000000009c00c0

def z189 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xce1c0c7c703f70f1 0x4ce1c0c7c703f70f

def z190 : W := mkw 0x04140054201510a0 0x804140054201510a 0x401c007c003f00f1 0x0401c007c003f00f

def z191 : W := mkw 0x4beadffb00000000 0x04beadffb0000000 0x41e3ffff80000002 0x841e3ffff8000000

def z192 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xf0040c1c09e77cc7 0x5f0040c1c09e77cc

def z193 : W := mkw 0x041400043015d0a2 0x8041400043015d0a 0x9e1c0000703ff0fd 0x79e1c0000703ff0f

def z194 : W := mkw 0x6ffedffb671c0008 0x06ffedffb671c000 0x4ffffffff618000b 0xf4ffffffff618000

def z195 : W := mkw 0x4fffdffb8a280558 0x44fffdffb8a28055 0x4fffffff803800f3 0xf4fffffff803800f

def z196 : W := mkw 0x100120048aeb3ddc 0x6100120048aeb3dd 0xb00000000ffffffc 0x0b00000000ffffff

def z197 : W := mkw 0x0d54800000000000 0x00d5480000000000 0x0e64e00000000000 0x40e64e0000000000

def z198 : W := mkw 0x6ffffffb4faa000c 0x06ffffffb4faa000 0x6fffffff8fc00003 0xf6fffffff8fc0000

def z199 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0xf0600e1f89c07cc6 0xdf0600e1f89c07cc

def z200 : W := mkw 0x4fde99f200000000 0x04fde99f20000000 0x0ffff1e000000001 0xf0ffff1e00000000

def z201 : W := mkw 0x008a00a202080118 0x4008a00a20208011 0x0180018006000300 0x0018001800600030

def z202 : W := mkw 0x000000a280000550 0x4000000a28000055 0x500013e380008ff2 0x0500013e380008ff

def z203 : W := mkw 0x1000400d800114c0 0x21000400d800114c 0x4000001f800000c0 0x04000001f800000c

def z204 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x501c1c7c003ff0f3 0x0501c1c7c003ff0f

def z205 : W := mkw 0x020018541001d0a2 0x8020018541001d0a 0xde001c7c7000f0fe 0x7de001c7c7000f0f

def z206 : W := mkw 0x0020460900402800 0x0002046090040280 0xf067ee1f89c07c07 0xdf067ee1f89c07c0

def z207 : W := mkw 0x0000000000000000 0x0000000000000000 0x0018106000188038 0x2001810600018803

def z208 : W := mkw 0x12217f0d98e3fec7 0x212217f0d98e3fec 0xf067ff9f89e7ffc7 0xdf067ff9f89e7ffc

def z209 : W := mkw 0x000000005540ea03 0x0000000005540ea0 0xb00000007fc0ff0c 0x0b00000007fc0ff0

def z210 : W := mkw 0x0b605f095540ea03 0x00b605f095540ea0 0xffe7ff9fffc0ff0f 0xfffe7ff9fffc0ff0

def z211 : W := mkw 0x02201f001040ea03 0x002201f001040ea0 0xb0601f8009c0ff06 0xdb0601f8009c0ff0

def z212 : W := mkw 0x2fdfb8547fbfd0ae 0x82fdfb8547fbfd0a 0xafffec1c7fff700d 0xfafffec1c7fff700

def z213 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000020008000c06 0x93000020008000c0

def z214 : W := mkw 0x400040fb00000000 0x0400040fb0000000 0x4000007f80000000 0x04000007f8000000

def z215 : W := mkw 0x020018043015d0a2 0x8020018043015d0a 0x9e001c00703ff0fe 0x79e001c00703ff0f

def z216 : W := mkw 0x0020460d00011080 0x00020460d0001108 0xd067ee1f802770c7 0xdd067ee1f802770c

def z217 : W := mkw 0x7fffffffefff3ccc 0x27fffffffefff3cc 0xffffffffffff7ccf 0xfffffffffffff7cc

def z218 : W := mkw 0x0001200088a20444 0x00001200088a2044 0xf067e20389e70cc7 0xdf067e20389e70cc

def z219 : W := mkw 0x249fa0002abe000c 0x0249fa0002abe000 0x8e1fe000703f000d 0x78e1fe000703f000

def z220 : W := mkw 0x4fde99f200000000 0x04fde99f20000000 0x4f9c1dfc00000003 0x74f9c1dfc0000000

def z221 : W := mkw 0x3ddfe00defbf14cc 0x23ddfe00defbf14c 0xefffe01fffff00cd 0xfefffe01fffff00c

def z222 : W := mkw 0x29eba7004fea2a0d 0x029eba7004fea2a0 0x21e3e3800fc00f00 0x821e3e3800fc00f0

def z223 : W := mkw 0x34bfe60daaff3ccc 0x234bfe60daaff3cc 0xf07fee1f89ff7cc7 0xdf07fee1f89ff7cc

def z224 : W := mkw 0x10012004b8f7fce6 0xa10012004b8f7fce 0xb000000079fffcfc 0x0b000000079fffcf

def z225 : W := mkw 0x061418503014c022 0x8061418503014c02 0x0e00000070000000 0x00e0000007000000

def z226 : W := mkw 0x1001600d88a314c4 0x21001600d88a314c 0x7007e21f88270cc7 0x97007e21f88270cc

def z227 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x318313838e008f0e 0xb318313838e008f0

def z228 : W := mkw 0x008b00000a280008 0x0008b00000a28000 0x319b13800e388f0f 0xb319b13800e388f0

def z229 : W := mkw 0x6ffffffb2abe000c 0x06ffffffb2abe000 0x4fffffff803f0003 0xf4fffffff803f000

def z230 : W := mkw 0x0615385438b7d0a6 0x80615385438b7d0a 0xfe7ffc7c79fff0ff 0xffe7ffc7c79fff0f

def z231 : W := mkw 0x69ebe7ab4faa000c 0x069ebe7ab4faa000 0x21e3e3838fc00000 0x821e3e3838fc0000

def z232 : W := mkw 0x249fa0006fbe000c 0x0249fa0006fbe000 0xa01fe0007fff000d 0x0a01fe0007fff000

def z233 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x40001fff80000002 0x040001fff8000000

def z234 : W := mkw 0x008a00a202080118 0x4008a00a20208011 0x319813e00e188f3e 0xb319813e00e188f3

def z235 : W := mkw 0x54bfe6ff88e33cc4 0x254bfe6ff88e33cc 0xf07fee7f89e77cc7 0xdf07fee7f89e77cc

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x218003800e000f00 0x8218003800e000f0

def z237 : W := mkw 0x3dffe609effe2c4c 0x23dffe609effe2c4 0xafffe203ffff0c0d 0xfafffe203ffff0c0

def z238 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xaf9800007fff000c 0x2af9800007fff000

def z239 : W := mkw 0x0000000000402800 0x0000000000040280 0xb000000009c07c04 0x0b000000009c07c0

def z240 : W := mkw 0x4b605ffb5540ea03 0x04b605ffb5540ea0 0xffe01fffffc0ff0e 0xfffe01fffffc0ff0

def z241 : W := mkw 0x6fffff596fbe000c 0x06fffff596fbe000 0xafffec1c7fff000d 0xfafffec1c7fff000

def z242 : W := mkw 0x6fffffff7fbfd0ae 0x86fffffff7fbfd0a 0xfffffffffffff0ff 0xffffffffffffff0f

def z243 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z244 : W := mkw 0x2fffbf547ffffaaf 0x82fffbf547ffffaa 0xfffffffc7fffffff 0xffffffffc7ffffff

def z245 : W := mkw 0x5fffffffdde3fec7 0x25fffffffdde3fec 0xffffffffffe7ffcf 0xfffffffffffe7ffc

def z246 : W := mkw 0x2ddfa0007ffeea0f 0x02ddfa0007ffeea0 0xbfffe0007fffff0d 0xfbfffe0007fffff0

def z247 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z248 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x9e181060703ff0fc 0x29e181060703ff0f

def z249 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x5fffffff803880ff 0xf5fffffff803880f

def z250 : W := mkw 0x4ffedffb80000550 0x44ffedffb8000055 0x5fffffff80008ff3 0xf5fffffff80008ff

def z251 : W := mkw 0x12205f0d9041fec3 0x212205f0d9041fec 0x50001f9f8000ffc2 0x050001f9f8000ffc

def z252 : W := mkw 0x4dfec7ab00000000 0x04dfec7ab0000000 0x0fffe38380000001 0xf0fffe3838000000

def z253 : W := mkw 0x4ffedffb1040ea03 0x04ffedffb1040ea0 0x5fffffff8000ff03 0xf5fffffff8000ff0

def z254 : W := mkw 0x0020460900000000 0x0002046090000000 0x0064ec1c00000000 0x40064ec1c0000000

def z255 : W := mkw 0x1021660d08e33884 0x21021660d08e3388 0xa067ec1c09e77005 0xda067ec1c09e7700

def z256 : W := mkw 0x0020060000000000 0x0002006000000000 0x00600e0000000002 0xd00600e000000000

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0x50000000002000c7 0x150000000002000c

def z258 : W := mkw 0x2d54800065140000 0x02d5480006514000 0x0e00000070000000 0x00e0000007000000

def z259 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x3fe01f800e008f0e 0xf3fe01f800e008f0

def z260 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb067e00009e77cc5 0xdb067e00009e77cc

def z261 : W := mkw 0x2000200065960004 0x0200020006596000 0x8000000071c70000 0x08000000071c7000

def z262 : W := mkw 0x020018001000c002 0x0020018001000c00 0x0e00100070008008 0x20e0010007000800

def z263 : W := mkw 0x0020060400413880 0x0002006040041388 0xf0640e1c09e77cc7 0xdf0640e1c09e77cc

def z264 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x219b03838e380f0d 0xb219b03838e380f0

def z265 : W := mkw 0x00ab06a28a682d58 0x400ab06a28a682d5 0xf1fb1fe38ff8ffff 0xff1fb1fe38ff8fff

def z266 : W := mkw 0x2ddfa0002abe000c 0x02ddfa0002abe000 0x0fffe000003f0001 0xf0fffe000003f000

def z267 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x319811e00e388ffc 0x2319811e00e388ff

def z268 : W := mkw 0x1dffe60d88e33cc4 0x21dffe60d88e33cc 0xffffee1f89e77cc7 0xfffffee1f89e77cc

def z269 : W := mkw 0x449fc0fb8a280558 0x4449fc0fb8a28055 0x401fe07f803800f1 0x0401fe07f803800f

def z270 : W := mkw 0x1435665da8f73ce4 0xa1435665da8f73ce 0xf07fee7f89ff7cf7 0xdf07fee7f89ff7cf

def z271 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x21ffe0000fff0001 0x821ffe0000fff000

def z272 : W := mkw 0x0414005020140020 0x8041400502014002 0x0018006000180030 0x0001800600018003

def z273 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0x5007ee1f80277cc3 0x05007ee1f80277cc

def z274 : W := mkw 0x049f00002a3c0008 0x0049f00002a3c000 0xaf9f00007e3f000d 0xfaf9f00007e3f000

def z275 : W := mkw 0x008a000000000000 0x0008a00000000000 0x019b000000000001 0xb019b00000000000

def z276 : W := mkw 0x061418503014c022 0x8061418503014c02 0x9e181c607018f03e 0x79e181c607018f03

def z277 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x1f801f807600ff0a 0x21f801f807600ff0

def z278 : W := mkw 0x2940a00045820004 0x02940a0004582000 0x0060e00001c00000 0x00060e00001c0000

def z279 : W := mkw 0x2fdfb8f6ffbfd5fe 0xc2fdfb8f6ffbfd5f 0xffffffffffffffff 0xffffffffffffffff

def z280 : W := mkw 0x4ffedffb3014c022 0x84ffedffb3014c02 0x4ffffffff018803b 0xf4ffffffff018803

def z281 : W := mkw 0x008a00a202080118 0x4008a00a20208011 0x519811e0063883ff 0x3519811e0063883f

def z282 : W := mkw 0x0b4019005500c203 0x00b4019005500c20 0x0f80118076008308 0x20f8011807600830

def z283 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x5e181c7c7018f0fa 0x25e181c7c7018f0f

def z284 : W := mkw 0x52205fff80413cc0 0x252205fff80413cc 0x50001fff80007cc2 0x050001fff80007cc

def z285 : W := mkw 0x06345e5900000000 0x006345e590000000 0x4e7ffe7f80000003 0xf4e7ffe7f8000000

def z286 : W := mkw 0x449e80f200000000 0x0449e80f20000000 0x0018006000000000 0x0001800600000000

def z287 : W := mkw 0x549fe0ff88a314c4 0x2549fe0ff88a314c 0x401fe07f802700c1 0x0401fe07f802700c

def z288 : W := mkw 0x0001000088200440 0x0000100008820044 0x40030003802000c1 0x040030003802000c

def z289 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x2ffbe0007fd80008 0xa2ffbe0007fd8000

def z290 : W := mkw 0x0020060000402800 0x0002006000040280 0xb0600e0009c07c06 0xdb0600e0009c07c0

def z291 : W := mkw 0x04140054201510a0 0x804140054201510a 0xce1c007c703f00fd 0x7ce1c007c703f00f

def z292 : W := mkw 0x16345e5db055fce2 0xa16345e5db055fce 0xde1c1e7ff03ffcff 0x7de1c1e7ff03ffcf

def z293 : W := mkw 0x061418503014c022 0x8061418503014c02 0x4e1c1c7c7018803b 0x74e1c1c7c7018803

def z294 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xfff81fe07ff8ffff 0xffff81fe07ff8fff

def z295 : W := mkw 0x6ddfe0fb6fbe000c 0x06ddfe0fb6fbe000 0xefffe07fffff000d 0xfefffe07fffff000

def z296 : W := mkw 0x2ddfa0a26fbe000c 0x02ddfa0a26fbe000 0xeffff3e3ffff000f 0xfeffff3e3ffff000

def z297 : W := mkw 0x0b601f0000402800 0x00b601f000040280 0xbfe01f8009c07c06 0xfbfe01f8009c07c0

def z298 : W := mkw 0x0614185000000000 0x0061418500000000 0x0e18106000000000 0x20e1810600000000

def z299 : W := mkw 0x028b18f69a29d5fa 0xc028b18f69a29d5f 0x719b1fff8e38ffff 0xb719b1fff8e38fff

def z300 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x419b11e3863883f9 0x2419b11e3863883f

def z301 : W := mkw 0x10ab66af8aeb3ddc 0x610ab66af8aeb3dd 0xf1e7ef9f8fe77fc7 0xdf1e7ef9f8fe77fc

def z302 : W := mkw 0x0414000020140000 0x0041400002014000 0x8e04000070070000 0x48e0400007007000

def z303 : W := mkw 0x0020060000402800 0x0002006000040280 0xb1e01f800fc0ff0e 0xfb1e01f800fc0ff0

def z304 : W := mkw 0x0000400900000000 0x0000040090000000 0x4007e01f80000001 0x04007e01f8000000

def z305 : W := mkw 0x4414c05900000000 0x04414c0590000000 0x0004e01c00000000 0x00004e01c0000000

def z306 : W := mkw 0x0ffe9f005540ea03 0x00ffe9f005540ea0 0xbfffff807fc0ff0f 0xfbfffff807fc0ff0

def z307 : W := mkw 0x0b601fa2d540ef53 0x40b601fa2d540ef5 0xffe01fe3ffc0fffe 0xfffe01fe3ffc0fff

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0x719813e00e388fff 0xb719813e00e388ff

def z309 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x718303838e200fc7 0x9718303838e200fc

def z310 : W := mkw 0x249fa0542abf10ac 0x8249fa0542abf10a 0x401fe07c003f00f1 0x0401fe07c003f00f

def z311 : W := mkw 0x4ddec0fb00000000 0x04ddec0fb0000000 0x4fffe07f80000001 0xf4fffe07f8000000

def z312 : W := mkw 0x000000a280000550 0x4000000a28000055 0x718013e38e008ffe 0xb718013e38e008ff

def z313 : W := mkw 0x094120004da20004 0x0094120004da2000 0xafe7e0007fe7000d 0xfafe7e0007fe7000

def z314 : W := mkw 0x0000000045000000 0x0000000004500000 0xa00000007fc0000c 0x0a00000007fc0000

def z315 : W := mkw 0x008b00008a280448 0x0008b00008a28044 0x719b02038e380ccf 0xb719b02038e380cc

def z316 : W := mkw 0x4ffedf5900000000 0x04ffedf590000000 0x0fffec1c00000001 0xf0fffec1c0000000

def z317 : W := mkw 0x1021660d8aeb3ddc 0x61021660d8aeb3dd 0xf067ee1f8fffffff 0xdf067ee1f8ffffff

def z318 : W := mkw 0x000000003014c022 0x8000000003014c02 0x0000000070188038 0x0000000007018803

def z319 : W := mkw 0x46345fff3015d0a2 0x846345fff3015d0a 0xde1c1ffff03ff0ff 0x7de1c1ffff03ff0f

def z320 : W := mkw 0x49eac7ab00000000 0x049eac7ab0000000 0x41fbf3e380000003 0xb41fbf3e38000000

def z321 : W := mkw 0x12205e5d9041fce2 0xa12205e5d9041fce 0x50001e7f8000fcf2 0x050001e7f8000fcf

def z322 : W := mkw 0x5fffffff8aeb3ddc 0x65fffffff8aeb3dd 0xffffffff8fffffff 0xfffffffff8ffffff

def z323 : W := mkw 0x1435660da8f73cc4 0x21435660da8f73cc 0xfe7fee1ff9ff7ccf 0xffe7fee1ff9ff7cc

def z324 : W := mkw 0x4fded9fb00000000 0x04fded9fb0000000 0x4f9ff1ff80000001 0x24f9ff1ff8000000

def z325 : W := mkw 0x008a00a200000000 0x0008a00a20000000 0x719b13e38e008f0f 0xb719b13e38e008f0

def z326 : W := mkw 0x000100000a280008 0x0000100000a28000 0x200000000e38000c 0x0200000000e38000

def z327 : W := mkw 0x4fde99f200000000 0x04fde99f20000000 0x4f9b13e380000003 0xb4f9b13e38000000

def z328 : W := mkw 0x0940010045000201 0x0094001004500020 0x0180018006000300 0x0018001800600030

def z329 : W := mkw 0x069f18f2ba3cc57a 0xc069f18f2ba3cc57 0x7f9b13e3fe388fff 0xb7f9b13e3fe388ff

def z330 : W := mkw 0x02201f0000000000 0x002201f000000000 0x00001f8000000002 0x000001f800000000

def z331 : W := mkw 0x0001000088200440 0x0000100008820044 0x3000000008200cc4 0x03000000008200cc

def z332 : W := mkw 0x020018f69001d5f2 0xc020018f69001d5f 0x50001fff8000fff2 0x050001fff8000fff

def z333 : W := mkw 0x2ddea000679e000c 0x02ddea000679e000 0x8ffce00077df0008 0x68ffce00077df000

def z334 : W := mkw 0x000000001000c002 0x0000000001000c00 0x900000007000f00c 0x0900000007000f00

def z335 : W := mkw 0x0614185020140000 0x0061418502014000 0xce1c1c7c703f000f 0x7ce1c1c7c703f000

def z336 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0x5067ee1f80007cc3 0xd5067ee1f80007cc

def z337 : W := mkw 0x0fde98543015d0a2 0x80fde98543015d0a 0xdffffc7c703ff0ff 0xfdffffc7c703ff0f

def z338 : W := mkw 0x061418541001d0a2 0x8061418541001d0a 0x5e1c1c7c0000f0f3 0x75e1c1c7c0000f0f

def z339 : W := mkw 0x2dde80a2671c0118 0x42dde80a2671c011 0x0f9811e076188338 0x20f9811e07618833

def z340 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xf003020389e77cc7 0x9f003020389e77cc

def z341 : W := mkw 0x2fdfb8007fbec00e 0x02fdfb8007fbec00 0xbffffc007ffff00f 0xfbffffc007ffff00

def z342 : W := mkw 0x108b20a68aeb3ddc 0x6108b20a68aeb3dd 0xf19b13e38fffffff 0xbf19b13e38ffffff

def z343 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf1e7ff9f8fe7ffcf 0xff1e7ff9f8fe7ffc

def z344 : W := mkw 0x1beb7fafdfebffdf 0x61beb7fafdfebffd 0xffffffffffffffff 0xffffffffffffffff

def z345 : W := mkw 0x200120004faa000c 0x0200120004faa000 0x200000000fc00000 0x0200000000fc0000

def z346 : W := mkw 0x000100008a280558 0x4000100008a28055 0x318013800e388ffe 0xb318013800e388ff

def z347 : W := mkw 0x0dfec60900000000 0x00dfec6090000000 0x4fffee1f80000003 0xf4fffee1f8000000

def z348 : W := mkw 0x1020660900c22804 0x21020660900c2280 0x0060e00001c00000 0x00060e00001c0000

def z349 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x8fe01d8077c0f308 0x68fe01d8077c0f30

def z350 : W := mkw 0x42205f5900000000 0x042205f590000000 0x00000c1c00000000 0x000000c1c0000000

def z351 : W := mkw 0x46345ffb00000000 0x046345ffb0000000 0x4e1c1fff80000003 0x74e1c1fff8000000

def z352 : W := mkw 0x4fde99f25500c203 0x04fde99f25500c20 0x0f9811e076008308 0x20f9811e07600830

def z353 : W := mkw 0x0020060000402800 0x0002006000040280 0x10000e0000007c02 0x010000e0000007c0

def z354 : W := mkw 0x0940000045000000 0x0094000004500000 0x0f80000076000008 0x20f8000007600000

def z355 : W := mkw 0x0ddf80a28a280558 0x40ddf80a28a28055 0x7ffff3e38e388fff 0xf7ffff3e38e388ff

def z356 : W := mkw 0x008a00a200000000 0x0008a00a20000000 0x0183038380000000 0x8018303838000000

def z357 : W := mkw 0x0bea1fa25540ea03 0x00bea1fa25540ea0 0xfffb1fe3ffc0ff0f 0xffffb1fe3ffc0ff0

def z358 : W := mkw 0x0414005000000000 0x0041400500000000 0x401c007c00000001 0x0401c007c0000000

def z359 : W := mkw 0x6fde99f2671c0008 0x06fde99f2671c000 0x0f9811e076180008 0x20f9811e07618000

def z360 : W := mkw 0x0021460988200440 0x0002146098820044 0x7067ee1f88200cc7 0xd7067ee1f88200cc

def z361 : W := mkw 0x0b601f0045000000 0x00b601f004500000 0xafe01f807fc0000e 0xfafe01f807fc0000

def z362 : W := mkw 0x000000005540ea03 0x0000000005540ea0 0xb18013807fc0ff0e 0xbb18013807fc0ff0

def z363 : W := mkw 0x6ffffffb7ffeea0f 0x06ffffffb7ffeea0 0xffffffffffffff0f 0xfffffffffffffff0

def z364 : W := mkw 0x00010004ba3dd5fa 0xc00010004ba3dd5f 0xb00000007e3ffffc 0x0b00000007e3ffff

def z365 : W := mkw 0x29ca800047080008 0x029ca80004708000 0x0180000006000000 0x0018000000600000

def z366 : W := mkw 0x0000000000000000 0x0000000000000000 0x4003020380000003 0x9400302038000000

def z367 : W := mkw 0x0414000020140000 0x0041400002014000 0xde1c1060703f80ff 0x7de1c1060703f80f

def z368 : W := mkw 0x0b4019005500c203 0x00b4019005500c20 0x9f801d807600f30e 0x79f801d807600f30

def z369 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafe7e0007fc70000 0xcafe7e0007fc7000

def z370 : W := mkw 0x008a00a200000000 0x0008a00a20000000 0x019811e000000000 0x2019811e00000000

def z371 : W := mkw 0x2ddfa0046fbf108c 0x02ddfa0046fbf108 0xffffec1c7fff70cf 0xfffffec1c7fff70c

def z372 : W := mkw 0x0b601f0045402a01 0x00b601f0045402a0 0x2fe01f800fc00f02 0xf2fe01f800fc00f0

def z373 : W := mkw 0x00aa46ab00000000 0x000aa46ab0000000 0x41ffffff80000003 0xf41ffffff8000000

def z374 : W := mkw 0x0b601f045541fa83 0x00b601f045541fa8 0xffe41f9c7fe7ffcf 0xfffe41f9c7fe7ffc

def z375 : W := mkw 0x00010004882114c0 0x000010004882114c 0xf0070e1f88277cc7 0xdf0070e1f88277cc

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x90000c0000007006 0x590000c000000700

def z377 : W := mkw 0x4ffedfff00011080 0x04ffedfff0001108 0xdfffffff802770c7 0xfdfffffff802770c

def z378 : W := mkw 0x49ca81a200000000 0x049ca81a20000000 0x0180018000000000 0x0018001800000000

def z379 : W := mkw 0x4ffe9ff200000000 0x04ffe9ff20000000 0x0ff81fe000000002 0xf0ff81fe00000000

def z380 : W := mkw 0x0000000000000000 0x0000000000000000 0x100010000000800e 0x3100010000000800

def z381 : W := mkw 0x0200180000000000 0x0020018000000000 0x0e001c0000000002 0x70e001c000000000

def z382 : W := mkw 0x008b00a68a2915d8 0x4008b00a68a2915d 0xf19f1fff8e3fffff 0xff19f1fff8e3ffff

def z383 : W := mkw 0x3ddfa004efff3ccc 0x23ddfa004efff3cc 0xbfffe0007fff7ccd 0xfbfffe0007fff7cc

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018106000000003 0x3401810600000000

def z385 : W := mkw 0x1000600d00831084 0x21000600d0083108 0x0004e01c00070000 0x00004e01c0007000

def z386 : W := mkw 0x4ffedffb5500c203 0x04ffedffb5500c20 0x4ffffffff600830b 0xf4ffffffff600830

def z387 : W := mkw 0x008b00000a280008 0x0008b00000a28000 0x218300000e000000 0x8218300000e00000

def z388 : W := mkw 0x4ffedfff1001d0a2 0x84ffedfff1001d0a 0x5fffffff8000f0f3 0xf5fffffff8000f0f

def z389 : W := mkw 0x0dde800000000000 0x00dde80000000000 0x0f98000000000000 0x20f9800000000000

def z390 : W := mkw 0x008a00a202080118 0x4008a00a20208011 0x419b13e38618833b 0xb419b13e38618833

def z391 : W := mkw 0x0dde800020140000 0x00dde80002014000 0x8fffe000703f000d 0xf8fffe000703f000

def z392 : W := mkw 0x2dffa6006ffe280c 0x02dffa6006ffe280 0xbfffee007fff7c0f 0xfbfffee007fff7c0

def z393 : W := mkw 0x0001000008200000 0x0000100000820000 0x2003000008200005 0x9200300000820000

def z394 : W := mkw 0x249fa0002abe000c 0x0249fa0002abe000 0xa07fe00009ff0005 0xda07fe00009ff000

def z395 : W := mkw 0x12217e5d98e3fce6 0xa12217e5d98e3fce 0xf067fe7f89e7fcf7 0xdf067fe7f89e7fcf

def z396 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x0fe4ff9c00000002 0xf0fe4ff9c0000000

def z397 : W := mkw 0x2ddfa000efbe044c 0x02ddfa000efbe044 0xffffe203ffff0ccf 0xfffffe203ffff0cc

def z398 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x7fffffff8e008f0f 0xf7fffffff8e008f0

def z399 : W := mkw 0x4fffdffb0a280008 0x04fffdffb0a28000 0x6fffffff8e38000f 0xf6fffffff8e38000

def z400 : W := mkw 0x0940000045000000 0x0094000004500000 0xbfe013807fc08f0e 0xfbfe013807fc08f0

def z401 : W := mkw 0x1f757f5dfdf7fee7 0xa1f757f5dfdf7fee 0xffffffffffffffff 0xffffffffffffffff

def z402 : W := mkw 0x2fde9850771cc02a 0x82fde9850771cc02 0x0f98106076188038 0x20f9810607618803

def z403 : W := mkw 0x0960070045402a01 0x00960070045402a0 0xafe003807fc00f0c 0xfafe003807fc00f0

def z404 : W := mkw 0x008a000002080008 0x0008a00000208000 0x0198000006180008 0x2019800000618000

def z405 : W := mkw 0x008b00a20a280118 0x4008b00a20a28011 0x219b11e00e38833d 0xb219b11e00e38833

def z406 : W := mkw 0x52217fff88e33cc4 0x252217fff88e33cc 0xf067ffff89e77cc7 0xdf067ffff89e77cc

def z407 : W := mkw 0x00000054000110a0 0x800000054000110a 0x4000007c000000f0 0x04000007c000000f

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x001800000038000d 0x3001800000038000

def z409 : W := mkw 0x4f54995000000000 0x04f5499500000000 0x0e00000000000000 0x00e0000000000000

def z410 : W := mkw 0x0b4019005500c203 0x00b4019005500c20 0x3f8013807e008f0e 0xb3f8013807e008f0

def z411 : W := mkw 0x0000000080000550 0x4000000008000055 0x1000000000008ff0 0x01000000000008ff

def z412 : W := mkw 0x2ddfa0004faa000c 0x02ddfa0004faa000 0x2fffe0000fc00001 0xf2fffe0000fc0000

def z413 : W := mkw 0x4f74df5d3015d0a2 0x84f74df5d3015d0a 0xde7cfc7c703ff0ff 0x7de7cfc7c703ff0f

def z414 : W := mkw 0x0b611f00df68ef5b 0x40b611f00df68ef5 0xbfe01f807ff8fffe 0xfbfe01f807ff8fff

def z415 : W := mkw 0x20000000671c0008 0x020000000671c000 0x0000000076180008 0x0000000007618000

def z416 : W := mkw 0x0000000045402a01 0x00000000045402a0 0x200000000fc00f00 0x0200000000fc00f0

def z417 : W := mkw 0x09eb07a2cf682f59 0x409eb07a2cf682f5 0x21e303838fc00f00 0x821e303838fc00f0

def z418 : W := mkw 0x3ffffe5dfffffcee 0xa3ffffe5dfffffce 0xfffffe7ffffffcff 0xffffffe7ffffffcf

def z419 : W := mkw 0x008a00a200000000 0x0008a00a20000000 0x519b13e3803880ff 0xb519b13e3803880f

def z420 : W := mkw 0x0f741f543015d0a2 0x80f741f543015d0a 0xdffc1ffc703ff0ff 0xfdffc1ffc703ff0f

def z421 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0fe01f8000000002 0xf0fe01f800000000

def z422 : W := mkw 0x2b613f007ffeea0f 0x02b613f007ffeea0 0xbfe01f807fffff0e 0xfbfe01f807fffff0

def z423 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xb064ec1c09e77cc4 0x4b064ec1c09e77cc

def z424 : W := mkw 0x020018501000c022 0x8020018501000c02 0x0000106000008030 0x0000010600000803

def z425 : W := mkw 0x2f54b8547597d0a6 0x82f54b8547597d0a 0x8e64ec1c71c77000 0x48e64ec1c71c7700

def z426 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x619b13e38e000f03 0xb619b13e38e000f0

def z427 : W := mkw 0x469ed8ff3015d0a2 0x8469ed8ff3015d0a 0xde1ffc7ff03ff0ff 0x7de1ffc7ff03ff0f

def z428 : W := mkw 0x49ebc7ab8a280558 0x449ebc7ab8a28055 0x21e3e3838e000f00 0x821e3e3838e000f0

def z429 : W := mkw 0x04140054201510a0 0x804140054201510a 0x0004001c00070000 0x00004001c0007000

def z430 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x9e041c1c7007f00e 0x79e041c1c7007f00

def z431 : W := mkw 0x10ab66ab8aea2d5c 0x610ab66ab8aea2d5 0x21e3e3838fc00f00 0x821e3e3838fc00f0

def z432 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0x7063ee1f89c07cc2 0x87063ee1f89c07cc

def z433 : W := mkw 0x1021260488e33cc4 0x21021260488e33cc 0xb0600e0009e77cc6 0xdb0600e0009e77cc

def z434 : W := mkw 0x069e18f2321cc13a 0xc069e18f2321cc13 0x0f9811e076188338 0x20f9811e07618833

def z435 : W := mkw 0x12217e0d98e3fcc6 0x212217e0d98e3fcc 0xfe67fe1ff9e7fccf 0xffe67fe1ff9e7fcc

def z436 : W := mkw 0x09eb07a2cf682f59 0x409eb07a2cf682f5 0x71fb13e38ff88fff 0xb71fb13e38ff88ff

def z437 : W := mkw 0x0960070000000000 0x0096007000000000 0x01e0038000000000 0x801e003800000000

def z438 : W := mkw 0x10ab46af8a693dd8 0x610ab46af8a693dd 0x719b1fff8e38ffff 0xb719b1fff8e38fff

def z439 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e7cfc7c00000003 0x74e7cfc7c0000000

def z440 : W := mkw 0x0960070045402a01 0x00960070045402a0 0x31e013800fc08f0e 0xb31e013800fc08f0

def z441 : W := mkw 0x16347e5d30d7f8a6 0xa16347e5d30d7f8a 0xde7cfc7c71fff0ff 0x7de7cfc7c71fff0f

def z442 : W := mkw 0x0f741f505540ea03 0x00f741f505540ea0 0xfffc1ffc7fc0ff0f 0xffffc1ffc7fc0ff0

def z443 : W := mkw 0x420019f200000000 0x0420019f20000000 0x000011e000000000 0x0000011e00000000

def z444 : W := mkw 0x2fde9854771dd0aa 0x82fde9854771dd0a 0xdf9c1c7c763ff0ff 0x7df9c1c7c763ff0f

def z445 : W := mkw 0x000000043015d0a2 0x8000000043015d0a 0xd0040c1c703ff0ff 0x5d0040c1c703ff0f

def z446 : W := mkw 0x008b00000a280008 0x0008b00000a28000 0x719b10600e3880ff 0xb719b10600e3880f

def z447 : W := mkw 0x02201f005540ea03 0x002201f005540ea0 0xb0001f807fc0ff0e 0x0b0001f807fc0ff0

def z448 : W := mkw 0x2ddfa0047fbfd0ae 0x82ddfa0047fbfd0a 0xbfffe0007ffff0fd 0xfbfffe0007ffff0f

def z449 : W := mkw 0x349fe00daabf14cc 0x2349fe00daabf14c 0x401fe01f803f00c1 0x0401fe01f803f00c

def z450 : W := mkw 0x2ddf80a2ef3c0558 0x42ddf80a2ef3c055 0x7f9b13e3fe388fff 0xb7f9b13e3fe388ff

def z451 : W := mkw 0x000000a200000000 0x0000000a20000000 0x400013e380000002 0x0400013e38000000

def z452 : W := mkw 0x2f54b8547597d0a6 0x82f54b8547597d0a 0xde7cfc7c71fff0ff 0x7de7cfc7c71fff0f

def z453 : W := mkw 0x0021260008e22804 0x00021260008e2280 0xb067ee0009e77c07 0xdb067ee0009e77c0

def z454 : W := mkw 0x2fde9900771cc20b 0x02fde9900771cc20 0x0f98118076188308 0x20f9811807618830

def z455 : W := mkw 0x249fa0a2aabe055c 0x4249fa0a2aabe055 0x719ff3e38e3f8fff 0xb719ff3e38e3f8ff

def z456 : W := mkw 0x0beb1f005f68ea0b 0x00beb1f005f68ea0 0xbffb1f807ff8ff0f 0xfbffb1f807ff8ff0

def z457 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x419b13e3803800f3 0xb419b13e3803800f

def z458 : W := mkw 0x0614185000000000 0x0061418500000000 0x0e040c1c00000000 0x40e040c1c0000000

def z459 : W := mkw 0x102166af88e33dd4 0x6102166af88e33dd 0xf067ffff89e7fff7 0xdf067ffff89e7fff

def z460 : W := mkw 0x0f741f547555faa3 0x80f741f547555faa 0x8e640c1c71c77000 0x48e640c1c71c7700

def z461 : W := mkw 0x008b00a288200440 0x0008b00a28820044 0x719b13e388200cc7 0xb719b13e388200cc

def z462 : W := mkw 0x0000000400011080 0x0000000040001108 0x80040c1c00077000 0x480040c1c0007700

def z463 : W := mkw 0x0f741f547555faa3 0x80f741f547555faa 0xde7c1c7c71fff0ff 0x7de7c1c7c71fff0f

def z464 : W := mkw 0x1020460d00413880 0x21020460d0041388 0x00000c1c00007000 0x000000c1c0000700

def z465 : W := mkw 0x00000004201510a0 0x800000004201510a 0x00000000003f00f0 0x000000000003f00f

def z466 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde041c7c7007f0f2 0x4de041c7c7007f0f

def z467 : W := mkw 0x42aa5ffb00000000 0x042aa5ffb0000000 0x419b1fff80000003 0xb419b1fff8000000

def z468 : W := mkw 0x1000000480413cc0 0x21000000480413cc 0x1000000000007cc0 0x01000000000007cc

def z469 : W := mkw 0x4fdf99f28a280558 0x44fdf99f28a28055 0x7f9b13e38e388fff 0xb7f9b13e38e388ff

def z470 : W := mkw 0x208b20a2efbe055c 0x4208b20a2efbe055 0xf19b13e3ffff8fff 0xbf19b13e3ffff8ff

def z471 : W := mkw 0x0beb1fa2df68ef5b 0x40beb1fa2df68ef5 0xbfe31f83ffc0ff0e 0xfbfe31f83ffc0ff0

def z472 : W := mkw 0x249fa0002abe000c 0x0249fa0002abe000 0x219fe0000e3f000d 0xb219fe0000e3f000

def z473 : W := mkw 0x42205ffb1040ea03 0x042205ffb1040ea0 0x50001fff8000ff02 0x050001fff8000ff0

def z474 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x31e01f800fc0ff02 0x831e01f800fc0ff0

def z475 : W := mkw 0x00010000df68ef5b 0x400010000df68ef5 0xb00000007ff8fffc 0x0b00000007ff8fff

def z476 : W := mkw 0x0b601f001000c002 0x00b601f001000c00 0x9fe01f807000f00e 0xf9fe01f807000f00

def z477 : W := mkw 0x3fffff0dfffffecf 0x23fffff0dfffffec 0xffffff9fffffffcf 0xfffffff9fffffffc

def z478 : W := mkw 0x6fdfb9f26fbe000c 0x06fdfb9f26fbe000 0xaffff1e07fff000d 0xfaffff1e07fff000

def z479 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xff9c1ffc7e3fffff 0xfff9c1ffc7e3ffff

def z480 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x501b13e380388ff3 0x0501b13e380388ff

def z481 : W := mkw 0x0b4019005500c203 0x00b4019005500c20 0xafe011807fc0830c 0xfafe011807fc0830

def z482 : W := mkw 0x2dde8000671c0008 0x02dde8000671c000 0x0fffe00076180009 0xf0fffe0007618000

def z483 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xafe00f807fc07f00 0xcafe00f807fc07f0

def z484 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0xc067ee1f81c77003 0xdc067ee1f81c7700

def z485 : W := mkw 0x0960070045402a01 0x00960070045402a0 0xb1e00f800fc07f06 0xdb1e00f800fc07f0

def z486 : W := mkw 0x200120047fbfd0ae 0x8200120047fbfd0a 0xb00000007ffff0fc 0x0b00000007ffff0f

def z487 : W := mkw 0x29cba0a2cfaa055c 0x429cba0a2cfaa055 0x71fbf3e38ff88fff 0xb71fbf3e38ff88ff

def z488 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x619b00638e3800fd 0xb619b00638e3800f

def z489 : W := mkw 0x0b601f001040ea03 0x00b601f001040ea0 0x1fe01f800000ff02 0xf1fe01f800000ff0

def z490 : W := mkw 0x020018001000c002 0x0020018001000c00 0x8e000c0070007000 0x48e000c007000700

def z491 : W := mkw 0x04140054201510a0 0x804140054201510a 0x501c107c003f80ff 0x3501c107c003f80f

def z492 : W := mkw 0x1021660988e22c44 0x21021660988e22c4 0xb063ee0389c07c06 0xdb063ee0389c07c0

def z493 : W := mkw 0x5ffffffb88e22c44 0x25ffffffb88e22c4 0x6fffffff89c00c03 0xf6fffffff89c00c0

def z494 : W := mkw 0x0001000088200440 0x0000100008820044 0x718313838e208fcf 0xb718313838e208fc

def z495 : W := mkw 0x249e8000221c0008 0x0249e8000221c000 0x0018000000180000 0x0001800000018000

def z496 : W := mkw 0x1021660d88a314c4 0x21021660d88a314c 0x4067ee1f802700c3 0xd4067ee1f802700c

def z497 : W := mkw 0x402047ab00000000 0x0402047ab0000000 0x0000038380000000 0x0000003838000000

def z498 : W := mkw 0x2dffe6096fbe000c 0x02dffe6096fbe000 0xefffee1fffff000f 0xfefffee1fffff000

def z499 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x9e040c1c703ff0fc 0x49e040c1c703ff0f

def z500 : W := mkw 0x020018005540ea03 0x0020018005540ea0 0xbe001c007fc0ff0e 0x7be001c007fc0ff0

def z501 : W := mkw 0x108b60af8aab15dc 0x6108b60af8aab15d 0x719ff3ff8e3f8fff 0xb719ff3ff8e3f8ff

def z502 : W := mkw 0x0ffe9f0000000000 0x00ffe9f000000000 0x0fffff8000000003 0xf0fffff800000000

def z503 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x701b00638e388ffd 0x0701b00638e388ff

def z504 : W := mkw 0x0960060045402800 0x0096006004540280 0xbfe00e007fc07c0e 0xfbfe00e007fc07c0

def z505 : W := mkw 0x1021460d88613cc0 0x21021460d88613cc 0x70030e1f88207cc7 0x970030e1f88207cc

def z506 : W := mkw 0x0b601f545541faa3 0x80b601f545541faa 0xffe01ffc7fc0fffe 0xfffe01ffc7fc0fff

def z507 : W := mkw 0x096007005540ea03 0x0096007005540ea0 0xb1e003807fc0ff0c 0x8b1e003807fc0ff0

def z508 : W := mkw 0x4ffffffb08a20004 0x04ffffffb08a2000 0xefffffff89e70007 0xfefffffff89e7000

def z509 : W := mkw 0x1001600d88e33cc4 0x21001600d88e33cc 0xf007e01f89e77cc5 0x0f007e01f89e77cc

def z510 : W := mkw 0x5ffeffff00c33884 0x25ffeffff00c3388 0xcfffffff81c77003 0xfcfffffff81c7700

def z511 : W := mkw 0x1b607f0d55c3fa87 0x21b607f0d55c3fa8 0xbfe4ff9c7fc7ff0e 0xfbfe4ff9c7fc7ff0

def z512 : W := mkw 0x069f18f6ba3dd5fa 0xc069f18f6ba3dd5f 0xde1f1c7ff03ff0ff 0x7de1f1c7ff03ff0f

def z513 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x419ff3ff80000003 0xb419ff3ff8000000

def z514 : W := mkw 0x0614185000000000 0x0061418500000000 0x5e1c1c7c003880ff 0x75e1c1c7c003880f

def z515 : W := mkw 0x049f00a2aa3c0558 0x4049f00a2aa3c055 0xff9f13e3fe3f8fff 0xfff9f13e3fe3f8ff

def z516 : W := mkw 0x020018001000c002 0x0020018001000c00 0xbf801f807e00ff0e 0xfbf801f807e00ff0

def z517 : W := mkw 0x1021660db8f7fce6 0xa1021660db8f7fce 0xf067ee1ff9fffcff 0xdf067ee1ff9fffcf

def z518 : W := mkw 0x59ebe7af88e33cc4 0x259ebe7af88e33cc 0xf1e7ef9f89e77cc7 0xdf1e7ef9f89e77cc

def z519 : W := mkw 0x069e18f200000000 0x0069e18f20000000 0x4f9f1fff80000003 0xf4f9f1fff8000000

def z520 : W := mkw 0x06151854b835d4e2 0x806151854b835d4e 0xfe1f1e7ff83ffcff 0xffe1f1e7ff83ffcf

def z521 : W := mkw 0x5fffffffb8f7fce6 0xa5fffffffb8f7fce 0xfffffffff9fffcff 0xffffffffff9fffcf

def z522 : W := mkw 0x0000000400011080 0x0000000040001108 0xd01c1c7c003ff0ff 0x7d01c1c7c003ff0f

def z523 : W := mkw 0x069e18f6321dd1ba 0xc069e18f6321dd1b 0xdf9c1dfc763ff3ff 0x7df9c1dfc763ff3f

def z524 : W := mkw 0x16347e5d30d7f8a6 0xa16347e5d30d7f8a 0x8e64ec1c71c77000 0x48e64ec1c71c7700

def z525 : W := mkw 0x10ab66ab8aea2d5c 0x610ab66ab8aea2d5 0x71fbf3e38ff88fff 0xb71fbf3e38ff88ff

def z526 : W := mkw 0x0f5419547515d2a3 0x80f5419547515d2a 0xdf9c1dfc763ff3ff 0x7df9c1dfc763ff3f

def z527 : W := mkw 0x049e800000000000 0x0049e80000000000 0x001fe00000000001 0x0001fe0000000000

def z528 : W := mkw 0x09cb00004f280008 0x009cb00004f28000 0xaffb00007ff8000d 0xfaffb00007ff8000

def z529 : W := mkw 0x4fffdffb88200440 0x04fffdffb8820044 0x7fffffff88200cc7 0xf7fffffff88200cc

def z530 : W := mkw 0x4fde99f202080118 0x44fde99f20208011 0x0f9811e006188338 0x20f9811e00618833

def z531 : W := mkw 0x0000000400011080 0x0000000040001108 0x4004001c002700c1 0x04004001c002700c

def z532 : W := mkw 0x5ffedfff80413cc0 0x25ffedfff80413cc 0x5fffffff80007cc3 0xf5fffffff80007cc

def z533 : W := mkw 0x649fe0fb2abe000c 0x0649fe0fb2abe000 0x401fe07f803f0001 0x0401fe07f803f000

def z534 : W := mkw 0x0940000045000000 0x0094000004500000 0x21e000000fc00000 0x821e000000fc0000

def z535 : W := mkw 0x0001200008a20004 0x00001200008a2000 0x0007e00000270001 0x00007e0000027000

def z536 : W := mkw 0x020018001000c002 0x0020018001000c00 0xde181c607038f0ff 0x7de181c607038f0f

def z537 : W := mkw 0x0bea1fa200000000 0x00bea1fa20000000 0x4ffb1fe380000003 0xf4ffb1fe38000000

def z538 : W := mkw 0x02201e001040e802 0x002201e001040e80 0xbe601e0079c0fc0e 0xfbe601e0079c0fc0

def z539 : W := mkw 0x0001200008a20004 0x00001200008a2000 0x2063e00009c00000 0x82063e00009c0000

def z540 : W := mkw 0x2fdfb9007fbec20f 0x02fdfb9007fbec20 0xaffff1807fff830d 0xfaffff1807fff830

def z541 : W := mkw 0x0414000420151080 0x0041400042015108 0xde1c0c1c703f70cf 0x7de1c0c1c703f70c

def z542 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fe0000000000000 0xf0fe000000000000

def z543 : W := mkw 0x5f75ff5d88e33cc4 0x25f75ff5d88e33cc 0xfe67ee1f89e77cc7 0xdfe67ee1f89e77cc

def z544 : W := mkw 0x6f74ff5965960004 0x06f74ff596596000 0x8e64ec1c71c70000 0x48e64ec1c71c7000

def z545 : W := mkw 0x29cba0a2cfaa055c 0x429cba0a2cfaa055 0x21e3e3838fc00f00 0x821e3e3838fc00f0

def z546 : W := mkw 0x4ffedfff3015d0a2 0x84ffedfff3015d0a 0xcffffffff0077003 0xfcffffffff007700

def z547 : W := mkw 0x008b20000aaa000c 0x0008b20000aaa000 0xa1ffe0000fff000d 0xfa1ffe0000fff000

def z548 : W := mkw 0x1020460d80413cc0 0x21020460d80413cc 0xd0040e1f80277cc7 0x5d0040e1f80277cc

def z549 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x8fe01f8071c07002 0xf8fe01f8071c0700

def z550 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x2fe013807fc08f08 0xa2fe013807fc08f0

def z551 : W := mkw 0x06341f543055faa3 0x806341f543055faa 0xde1c1ffc703fffff 0x7de1c1ffc703ffff

def z552 : W := mkw 0x0960070045402a01 0x00960070045402a0 0x0060000001c00000 0x00060000001c0000

def z553 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180118006008308 0x2018011800600830

def z554 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xafe00c007fc0700c 0xfafe00c007fc0700

def z555 : W := mkw 0x0b4018005500c002 0x00b4018005500c00 0xbfe01c007fc0f00e 0xfbfe01c007fc0f00

def z556 : W := mkw 0x09cb00a2cf280558 0x409cb00a2cf28055 0xfffb13e3fff88fff 0xffffb13e3fff88ff

def z557 : W := mkw 0x4960c70900000000 0x04960c7090000000 0x0060e00000000000 0x00060e0000000000

def z558 : W := mkw 0x0b601f0000000000 0x00b601f000000000 0x0e600c0000000000 0x40e600c000000000

def z559 : W := mkw 0x2fffbfa2fffeef5f 0x42fffbfa2fffeef5 0xffffffe3ffffffff 0xfffffffe3fffffff

def z560 : W := mkw 0x1b617f0d88e33cc4 0x21b617f0d88e33cc 0xffe7ff9f89e77cc7 0xfffe7ff9f89e77cc

def z561 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x0ffcfdfc00000000 0x60ffcfdfc0000000

def z562 : W := mkw 0x0000000000000000 0x0000000000000000 0x300000000e008f0c 0x0300000000e008f0

def z563 : W := mkw 0x1021660988e22c44 0x21021660988e22c4 0x6067ee1f89c00c03 0xd6067ee1f89c00c0

def z564 : W := mkw 0x39ebe609cfea2c4c 0x239ebe609cfea2c4 0x21e3e2038fc00c00 0x821e3e2038fc00c0

def z565 : W := mkw 0x0020460900000000 0x0002046090000000 0x40000e1f80000002 0x040000e1f8000000

def z566 : W := mkw 0x008b00008a280558 0x4008b00008a28055 0x319b00000e388ffd 0xb319b00000e388ff

def z567 : W := mkw 0x16153854b8f7fce6 0xa16153854b8f7fce 0xfe1c1c7c79fffcff 0x7fe1c1c7c79fffcf

def z568 : W := mkw 0x2dffa7006ffe2a0d 0x02dffa7006ffe2a0 0xafffe3807fff0f0d 0xfafffe3807fff0f0

def z569 : W := mkw 0x2fdfb8506fbe000c 0x02fdfb8506fbe000 0xeffffc7c7fff000f 0xfeffffc7c7fff000

def z570 : W := mkw 0x041400543015d0a2 0x8041400543015d0a 0xd01c007c703ff0fd 0x0d01c007c703ff0f

def z571 : W := mkw 0x249fa0a2aabe055c 0x4249fa0a2aabe055 0x401fe063803f00f1 0x0401fe063803f00f

def z572 : W := mkw 0x42ab5ffb8a280558 0x442ab5ffb8a28055 0x719b1fff8e388fff 0xb719b1fff8e388ff

def z573 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e7ce00071ff000d 0x78e7ce00071ff000

def z574 : W := mkw 0x0b601f047555faa3 0x80b601f047555faa 0xbfe01f807ffffffe 0xfbfe01f807ffffff

def z575 : W := mkw 0x049f00f6aa3d15f8 0xc049f00f6aa3d15f 0x401f007f803f00f1 0x0401f007f803f00f

def z576 : W := mkw 0x102046af80413dd0 0x6102046af80413dd 0x50001fff8000fff2 0x050001fff8000fff

def z577 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x4e64ffff80000002 0x44e64ffff8000000

def z578 : W := mkw 0x208ba0000aaa000c 0x0208ba0000aaa000 0x0003e00000000000 0x00003e0000000000

def z579 : W := mkw 0x0fff1ff6ff7dfffb 0xc0fff1ff6ff7dfff 0xffff1fffffffffff 0xfffff1ffffffffff

def z580 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x9e601c0071c0f00e 0x79e601c0071c0f00

def z581 : W := mkw 0x0d54000065140000 0x00d5400006514000 0xaffc00007fff000d 0xfaffc00007fff000

def z582 : W := mkw 0x06141854201510a0 0x806141854201510a 0x4e1c1c7c003f00f3 0x74e1c1c7c003f00f

def z583 : W := mkw 0x10ab660d8aeb3ccc 0x210ab660d8aeb3cc 0xf1ffee1f8fff7ccf 0xff1ffee1f8fff7cc

def z584 : W := mkw 0x42205ffb80000550 0x442205ffb8000055 0x50001fff80008ff2 0x050001fff80008ff

def z585 : W := mkw 0x4b605ffb00000000 0x04b605ffb0000000 0x4fe01fff80000002 0xf4fe01fff8000000

def z586 : W := mkw 0x0020460900000000 0x0002046090000000 0x0063e20380000000 0x80063e2038000000

def z587 : W := mkw 0x000000001040ea03 0x0000000001040ea0 0x100000000000ff00 0x0100000000000ff0

def z588 : W := mkw 0x4beadfab5540ea03 0x04beadfab5540ea0 0xbfe3ff83ffc0ff0e 0xfbfe3ff83ffc0ff0

def z589 : W := mkw 0x094000005540ea03 0x0094000005540ea0 0xbfe000007fc0ff0c 0xfbfe000007fc0ff0

def z590 : W := mkw 0x09ca800000000000 0x009ca80000000000 0x01e3e00000000000 0x801e3e0000000000

def z591 : W := mkw 0x000100008a280558 0x4000100008a28055 0x200000000e000f00 0x0200000000e000f0

def z592 : W := mkw 0x1b613f04dde3fec7 0x21b613f04dde3fec 0xbfe01f807fe7ffce 0xfbfe01f807fe7ffc

def z593 : W := mkw 0x6ffffffbefbe055c 0x46ffffffbefbe055 0xffffffffffff8fff 0xfffffffffffff8ff

def z594 : W := mkw 0x2d55a0006db60004 0x02d55a0006db6000 0xae67e00079e70005 0xdae67e00079e7000

def z595 : W := mkw 0x0f741f5000000000 0x00f741f500000000 0x4ffc1ffc00000003 0xf4ffc1ffc0000000

def z596 : W := mkw 0x261538547fbfd0ae 0x8261538547fbfd0a 0xfe1c1c7c7ffff0ff 0x7fe1c1c7c7ffff0f

def z597 : W := mkw 0x049f00f6aa3d15f8 0xc049f00f6aa3d15f 0x719f13ff8e3f8fff 0xb719f13ff8e3f8ff

def z598 : W := mkw 0x49ebc7ab8a280558 0x449ebc7ab8a28055 0x71fbf3e38e388fff 0xb71fbf3e38e388ff

def z599 : W := mkw 0x16357e5db8f7fce6 0xa16357e5db8f7fce 0xfe67ee1ff9e77cc7 0xdfe67ee1ff9e77cc

def z600 : W := mkw 0x020019001000c203 0x0020019001000c20 0x0000118000008300 0x0000011800000830

def z601 : W := mkw 0x02201f001040ea03 0x002201f001040ea0 0x00000c0000007000 0x000000c000000700

def z602 : W := mkw 0x108b60af8aab15dc 0x6108b60af8aab15d 0x401fe07f803f00f1 0x0401fe07f803f00f

def z603 : W := mkw 0x2ddf80006f3c0008 0x02ddf80006f3c000 0x2f9b00007e38000d 0xb2f9b00007e38000

def z604 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x9e601f8071c0ff02 0x49e601f8071c0ff0

def z605 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbe600c007fc0ff0c 0x4be600c007fc0ff0

def z606 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x701b026388380cf7 0x9701b026388380cf

def z607 : W := mkw 0x02201f001040ea03 0x002201f001040ea0 0x9e001f807000ff0e 0x79e001f807000ff0

def z608 : W := mkw 0x0020060000402800 0x0002006000040280 0x2060020009c00c00 0x82060020009c00c0

def z609 : W := mkw 0x008b00a2df68ef5b 0x4008b00a2df68ef5 0xf19b13e3fff8ffff 0xbf19b13e3fff8fff

def z610 : W := mkw 0x208b20006fbe000c 0x0208b20006fbe000 0xa19b00007fff000d 0xba19b00007fff000

def z611 : W := mkw 0x29cba0006fbe000c 0x029cba0006fbe000 0xa1e3e0007fff000c 0x8a1e3e0007fff000

def z612 : W := mkw 0x1b607f0d55c3fa87 0x21b607f0d55c3fa8 0x8e64ec1c71c77000 0x48e64ec1c71c7700

def z613 : W := mkw 0x200120007ffeea0f 0x0200120007ffeea0 0xb00000007fffff0c 0x0b00000007fffff0

def z614 : W := mkw 0x0b611f00dd60ee43 0x00b611f00dd60ee4 0xffe31f83ffe0ffcf 0xfffe31f83ffe0ffc

def z615 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde040c1c702770c7 0x5de040c1c702770c

def z616 : W := mkw 0x020018541001d0a2 0x8020018541001d0a 0x50181c7c0038f0ff 0x350181c7c0038f0f

def z617 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x318303838e388ffc 0x8318303838e388ff

def z618 : W := mkw 0x008b00a6ba3dd5fa 0xc008b00a6ba3dd5f 0xf19b13e3fe3fffff 0xbf19b13e3fe3ffff

def z619 : W := mkw 0x241520006fbe000c 0x0241520006fbe000 0xae1c00007fff000d 0x7ae1c00007fff000

def z620 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x619b03e38e380ff1 0x8619b03e38e380ff

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004000000270005 0x5800400000027000

def z622 : W := mkw 0x3dffe60d6fff388c 0x23dffe60d6fff388 0xafffec1c7fff700d 0xfafffec1c7fff700

def z623 : W := mkw 0x1001600988a20444 0x21001600988a2044 0x0003e00380000000 0x00003e0038000000

def z624 : W := mkw 0x4fde99f23014c022 0x84fde99f23014c02 0x0f9811e070188038 0x20f9811e07018803

def z625 : W := mkw 0x29cba0004faa000c 0x029cba0004faa000 0x21fbe0000ff8000d 0xb21fbe0000ff8000

def z626 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x8e1c1c7c701ff038 0x68e1c1c7c701ff03

def z627 : W := mkw 0x0000000020140000 0x0000000002014000 0x80000000703f000c 0x080000000703f000

def z628 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf0000e1f89e77cc6 0x0f0000e1f89e77cc

def z629 : W := mkw 0x02201f001040ea03 0x002201f001040ea0 0x31801f800e00ff0e 0xb31801f800e00ff0

def z630 : W := mkw 0x020018001000c002 0x0020018001000c00 0x10001c000000f002 0x010001c000000f00

def z631 : W := mkw 0x1961670dcde33ec5 0x21961670dcde33ec 0xf1e7ef9f8fe77fc7 0xdf1e7ef9f8fe77fc

def z632 : W := mkw 0x061418547555faa3 0x8061418547555faa 0xfe1c1c7c7fffffff 0x7fe1c1c7c7ffffff

def z633 : W := mkw 0x000100008a280558 0x4000100008a28055 0x700302038e388fff 0x9700302038e388ff

def z634 : W := mkw 0x2fdfb8507fbec02e 0x82fdfb8507fbec02 0xaffff0607fff803d 0xfaffff0607fff803

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0xa060000009c00004 0xda060000009c0000

def z636 : W := mkw 0x5fffffff88a314c4 0x25fffffff88a314c 0x4fffffff802700c3 0xf4fffffff802700c

def z637 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x0ffbf3e380000000 0xa0ffbf3e38000000

def z638 : W := mkw 0x2dde8000671c0008 0x02dde8000671c000 0x8f9c0000763f000d 0x78f9c0000763f000

def z639 : W := mkw 0x1020660d80c33cc4 0x21020660d80c33cc 0xd064ee1f81c77cc2 0x4d064ee1f81c77cc

def z640 : W := mkw 0x3d74e60d65d73884 0x23d74e60d65d7388 0x8e64ec1c71c77000 0x48e64ec1c71c7700

def z641 : W := mkw 0x061418503014c022 0x8061418503014c02 0x8e1c1060703f803d 0x78e1c1060703f803

def z642 : W := mkw 0x0000000000000000 0x0000000000000000 0x8e0000007000000c 0x78e0000007000000

def z643 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x4e1c107c703f80f9 0x24e1c107c703f80f

def z644 : W := mkw 0x1b605f0dd541fec3 0x21b605f0dd541fec 0xffe01f9fffc0ffce 0xfffe01f9fffc0ffc

def z645 : W := mkw 0x069f18f28a280558 0x4069f18f28a28055 0x7f9f1fff8e388fff 0xf7f9f1fff8e388ff

def z646 : W := mkw 0x000100008a280558 0x4000100008a28055 0x701810600e388fff 0x3701810600e388ff

def z647 : W := mkw 0x061418501000c002 0x0061418501000c00 0xde1c1c7c7000f00f 0x7de1c1c7c7000f00

def z648 : W := mkw 0x59ebe7ab88e22c44 0x259ebe7ab88e22c4 0x21e3e38389c00c00 0x821e3e38389c00c0

def z649 : W := mkw 0x028b18a29a28c55a 0x4028b18a29a28c55 0xff9b1fe3fe38ffff 0xfff9b1fe3fe38fff

def z650 : W := mkw 0x1b617f09dde2ee47 0x21b617f09dde2ee4 0xbfe3ff83ffc0ff0e 0xfbfe3ff83ffc0ff0

def z651 : W := mkw 0x020018041001d082 0x0020018041001d08 0xde041c1c7027f0cf 0x7de041c1c7027f0c

def z652 : W := mkw 0x0021660908a20004 0x00021660908a2000 0xe067ee1f89e70007 0xde067ee1f89e7000

def z653 : W := mkw 0x449ec0ff201510a0 0x8449ec0ff201510a 0x401fe07f803f00f1 0x0401fe07f803f00f

def z654 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4f981fff80000002 0x24f981fff8000000

def z655 : W := mkw 0x04140054201510a0 0x804140054201510a 0xd01c0c7c003f70f7 0x5d01c0c7c003f70f

def z656 : W := mkw 0x4ffe9ff25540ea03 0x04ffe9ff25540ea0 0xbff81fe07fc0ff0e 0xfbff81fe07fc0ff0

def z657 : W := mkw 0x2fffbf007ffeea0f 0x02fffbf007ffeea0 0xafffec007fff700d 0xfafffec007fff700

def z658 : W := mkw 0x2ddfa0546fbf10ac 0x82ddfa0546fbf10a 0xefffe07c7fff00fd 0xfefffe07c7fff00f

def z659 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0xd064ec1c01e770c7 0x5d064ec1c01e770c

def z660 : W := mkw 0x0940000045000000 0x0094000004500000 0x8e60000071c00000 0x48e60000071c0000

def z661 : W := mkw 0x4ffedfff201510a0 0x84ffedfff201510a 0x4fffffff803f00f3 0xf4fffffff803f00f

def z662 : W := mkw 0x1001600d88a314c4 0x21001600d88a314c 0xe067e01f89e700c5 0xde067e01f89e700c

def z663 : W := mkw 0x1021660ddde3fec7 0x21021660ddde3fec 0xf067ee1fffe7ffcf 0xdf067ee1fffe7ffc

def z664 : W := mkw 0x008a00a280000550 0x4008a00a28000055 0x519b13e380008ff3 0xb519b13e380008ff

def z665 : W := mkw 0x2f74bf0075d6ea07 0x02f74bf0075d6ea0 0x8e64ec0071c77000 0x48e64ec0071c7700

def z666 : W := mkw 0x0b4019005500c203 0x00b4019005500c20 0x0e00000070000000 0x00e0000007000000

def z667 : W := mkw 0x06151854ba3dd5fa 0xc06151854ba3dd5f 0xfe1c1c7c7e3fffff 0x7fe1c1c7c7e3ffff

def z668 : W := mkw 0x16bf7effbafffdfe 0xe16bf7effbafffdf 0xffffffffffffffff 0xffffffffffffffff

def z669 : W := mkw 0x4f74df595540ea03 0x04f74df595540ea0 0xbfe4ff9c7fc0ff0e 0xfbfe4ff9c7fc0ff0

def z670 : W := mkw 0x0f741f007554ea03 0x00f741f007554ea0 0xbffc1f807fffff0f 0xfbffc1f807fffff0

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180138000000002 0xb018013800000000

def z672 : W := mkw 0x3dffe6afefff3ddc 0x63dffe6afefff3dd 0xffffffffffffffff 0xffffffffffffffff

def z673 : W := mkw 0x10ab66af8aeb3ddc 0x610ab66af8aeb3dd 0xf07fee7f89ff7cf7 0xdf07fee7f89ff7cf

def z674 : W := mkw 0x000000a200000110 0x4000000a20000011 0x000011e000008330 0x0000011e00000833

def z675 : W := mkw 0x0fde985000000000 0x00fde98500000000 0x4ffffc7c00000003 0xf4ffffc7c0000000

def z676 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xb063e20389e77cc4 0x8b063e20389e77cc

def z677 : W := mkw 0x0614185400011080 0x0061418540001108 0xde1c1c7c002770c7 0x7de1c1c7c002770c

def z678 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x0003000380000000 0x0000300038000000

def z679 : W := mkw 0x008b00000a280008 0x0008b00000a28000 0x001b000000380001 0x0001b00000038000

def z680 : W := mkw 0x008a00a202080118 0x4008a00a20208011 0x0018006000180030 0x0001800600018003

def z681 : W := mkw 0x000000043015d0a2 0x8000000043015d0a 0x8000000070077000 0x0800000007007700

def z682 : W := mkw 0x0f5418547515d0a2 0x80f5418547515d0a 0xfffc1c7c7ffff0ff 0xffffc1c7c7ffff0f

def z683 : W := mkw 0x0f741f547555faa3 0x80f741f547555faa 0xbfe41f9c7fc7ff0e 0xfbfe41f9c7fc7ff0

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000138000008f02 0x01000138000008f0

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x218000000e00000c 0xb218000000e00000

def z686 : W := mkw 0x2ffe9f00775cea0b 0x02ffe9f00775cea0 0xbff81f807fd8ff0e 0xfbff81f807fd8ff0

def z687 : W := mkw 0x10ab66af88e33cc4 0x210ab66af88e33cc 0xf1ffffff89e77cc7 0xff1ffffff89e77cc

def z688 : W := mkw 0x0414000020140000 0x0041400002014000 0x001c0000003f0001 0x0001c0000003f000

def z689 : W := mkw 0x0000000400011080 0x0000000040001108 0x50000c1c000070c2 0x050000c1c000070c

def z690 : W := mkw 0x5f74ff5d00c33884 0x25f74ff5d00c3388 0x8e64ec1c01c77000 0x48e64ec1c01c7700

def z691 : W := mkw 0x061418003014c002 0x0061418003014c00 0x9e1c1c00703ff00f 0x79e1c1c00703ff00

def z692 : W := mkw 0x0001000088200440 0x0000100008820044 0x2003020388000c00 0x82003020388000c0

def z693 : W := mkw 0x0020070000402a01 0x00020070000402a0 0x0000038000000f00 0x00000038000000f0

def z694 : W := mkw 0x0200185000000000 0x0020018500000000 0x40001c7c00000002 0x040001c7c0000000

def z695 : W := mkw 0x0beb1fa28a280558 0x40beb1fa28a28055 0x7ffb1fe38e388fff 0xf7ffb1fe38e388ff

def z696 : W := mkw 0x000100a28a280558 0x4000100a28a28055 0x700013e38e388ffe 0x0700013e38e388ff

def z697 : W := mkw 0x0000000002080118 0x4000000000208011 0x0000000006188338 0x0000000000618833

def z698 : W := mkw 0x2414a00020960004 0x02414a0002096000 0x0004e00000070000 0x00004e0000007000

def z699 : W := mkw 0x1b617f0ddde3fec7 0x21b617f0ddde3fec 0xfe67ee1ff9e77cc7 0xdfe67ee1ff9e77cc

def z700 : W := mkw 0x002006005540ea03 0x0002006005540ea0 0xb0600e007fc0ff0e 0xdb0600e007fc0ff0

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x50001060000080f2 0x050001060000080f

def z702 : W := mkw 0x29cba0004faa000c 0x029cba0004faa000 0xa1e7e0000fe70005 0xda1e7e0000fe7000

def z703 : W := mkw 0x1615785db8b7d4e6 0xa1615785db8b7d4e 0xde1ffc7ff03ff0ff 0x7de1ffc7ff03ff0f

def z704 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x219b13e38e188f38 0xa219b13e38e188f3

def z705 : W := mkw 0x000000a280000550 0x4000000a28000055 0x0000038380000f00 0x00000038380000f0

def z706 : W := mkw 0x06341e543055f8a2 0x806341e543055f8a 0xfe7c1e7c79fffcff 0xffe7c1e7c79fffcf

def z707 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fe7ffff80000002 0xc4fe7ffff8000000

def z708 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xdf9c1dfc763ff3ff 0x7df9c1dfc763ff3f

def z709 : W := mkw 0x0ffede5900000000 0x00ffede590000000 0x4ffffe7f80000003 0xf4ffffe7f8000000

def z710 : W := mkw 0x2ddea0a2679e011c 0x42ddea0a2679e011 0x8ffcf1e077df8338 0x68ffcf1e077df833

def z711 : W := mkw 0x26bfbf003afeea0f 0x026bfbf003afeea0 0x101fff80003fff03 0x0101fff80003fff0

def z712 : W := mkw 0x4ffedffb1000c002 0x04ffedffb1000c00 0x4ffffffff000800b 0xf4ffffffff000800

def z713 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0x8067ee1f81c77000 0xc8067ee1f81c7700

def z714 : W := mkw 0x49eac7ab00000000 0x049eac7ab0000000 0x01e7ef9f80000000 0xc01e7ef9f8000000

def z715 : W := mkw 0x2d55a000efbe055c 0x42d55a000efbe055 0xbe64e0007fff8ffc 0x4be64e0007fff8ff

def z716 : W := mkw 0x0020460900000000 0x0002046090000000 0x71e7ff9f8e008f0f 0xf71e7ff9f8e008f0

def z717 : W := mkw 0x069f18f6ba3dd5fa 0xc069f18f6ba3dd5f 0xaf870f9ffe077f00 0xcaf870f9ffe077f0

def z718 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0x5ffffffff600ff0b 0xf5ffffffff600ff0

def z719 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x419fe07f80000001 0xb419fe07f8000000

def z720 : W := mkw 0x1001200498e3fec7 0x21001200498e3fec 0xb000000009e7ffc4 0x0b000000009e7ffc

def z721 : W := mkw 0x0020460900000000 0x0002046090000000 0x407ffe7f80000003 0xf407ffe7f8000000

def z722 : W := mkw 0x0020460900000000 0x0002046090000000 0x507ffe7f803880ff 0xf507ffe7f803880f

def z723 : W := mkw 0x0b605f0900000000 0x00b605f090000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z724 : W := mkw 0x0020460900000000 0x0002046090000000 0x4067e21f80000001 0x84067e21f8000000

def z725 : W := mkw 0x2ddfa0a26fbe011c 0x42ddfa0a26fbe011 0xfffff1e07fff83ff 0xffffff1e07fff83f

def z726 : W := mkw 0x1b41790ddda3d6c7 0x21b41790ddda3d6c 0x4f87f19ff62783c9 0x24f87f19ff62783c

def z727 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x5fffffff800080f3 0xf5fffffff800080f

def z728 : W := mkw 0x4fde99f27514c223 0x84fde99f27514c22 0x0f9811e076188338 0x20f9811e07618833

def z729 : W := mkw 0x0414200020960004 0x0041420002096000 0x8e64e00071c70000 0x48e64e00071c7000

def z730 : W := mkw 0x4ffedffb20140000 0x04ffedffb2014000 0xcffffffff0070003 0xfcffffffff007000

def z731 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafffe0007fff0001 0xcafffe0007fff000

def z732 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xd067ec1f81e770c7 0x5d067ec1f81e770c

def z733 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf1ffffff8fffffff 0xff1ffffff8ffffff

def z734 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fffec7f80000001 0xf4fffec7f8000000

def z735 : W := mkw 0x0940200045820004 0x0094020004582000 0x8e64e00071c70000 0x48e64e00071c7000

def z736 : W := mkw 0x4beadffb00000000 0x04beadffb0000000 0x41fbffff80000003 0xb41fbffff8000000

def z737 : W := mkw 0x469ed8fb1000c002 0x0469ed8fb1000c00 0xde1ffc7ff000f00f 0x7de1ffc7ff000f00

def z738 : W := mkw 0x2ddea000679e000c 0x02ddea000679e000 0x8fffe00077df0009 0xf8fffe00077df000

def z739 : W := mkw 0x102126048aeb3ddc 0x6102126048aeb3dd 0xb1e01f800ffffffe 0xfb1e01f800ffffff

def z740 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafffe0007fdf0008 0xeafffe0007fdf000

def z741 : W := mkw 0x4ddec0fb00000000 0x04ddec0fb0000000 0x4e7fe07f80000001 0x44e7fe07f8000000

def z742 : W := mkw 0x12205f0d9041fec3 0x212205f0d9041fec 0x50000e1f80007cc2 0x050000e1f80007cc

def z743 : W := mkw 0x62217ffb6fbe000c 0x062217ffb6fbe000 0xe0001fffffff000e 0x0e0001fffffff000

def z744 : W := mkw 0x2ddea00065960004 0x02ddea0006596000 0xafffe0007fc7000d 0xfafffe0007fc7000

def z745 : W := mkw 0x1b613f04dfebffdf 0x61b613f04dfebffd 0xbfe01f807ffffffe 0xfbfe01f807ffffff

def z746 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xb067ee1f89e77cc4 0xcb067ee1f89e77cc

def z747 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xefffec1c7fff000f 0xfefffec1c7fff000

def z748 : W := mkw 0x0001200488a314c4 0x00001200488a314c 0xf067ee1f89e77cc7 0xdf067ee1f89e77cc

def z749 : W := mkw 0x008a40ab00000000 0x0008a40ab0000000 0x419ff3ff80000003 0xb419ff3ff8000000

def z750 : W := mkw 0x0d74c60900000000 0x00d74c6090000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z751 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x41ffffff80000003 0x841ffffff8000000

def z752 : W := mkw 0x2ddea00065960004 0x02ddea0006596000 0x8e7fe00071c70001 0x48e7fe00071c7000

def z753 : W := mkw 0x020018005540ea03 0x0020018005540ea0 0xbf801f807fc0ff0e 0xfbf801f807fc0ff0

def z754 : W := mkw 0x00aa46ab02080118 0x400aa46ab0208011 0x41ffffff8618833b 0xf41ffffff8618833

def z755 : W := mkw 0x4ffedffb45000000 0x04ffedffb4500000 0xcffffffff1c00003 0xfcffffffff1c0000

def z756 : W := mkw 0x10012004b8f7fce6 0xa10012004b8f7fce 0xb000000079e77cc4 0x0b000000079e77cc

def z757 : W := mkw 0x6ddfa1a26fbe000c 0x06ddfa1a26fbe000 0xafffe1807fff000d 0xfafffe1807fff000

def z758 : W := mkw 0x6ddfa0f26fbe000c 0x06ddfa0f26fbe000 0xafffe0607fff000d 0xfafffe0607fff000

def z759 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbf801f807fc0ff0e 0x2bf801f807fc0ff0

def z760 : W := mkw 0x2ddea000679e000c 0x02ddea000679e000 0x8ffce00077ff000d 0x78ffce00077ff000

def z761 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xaffce0007fff000c 0x6affce0007fff000

def z762 : W := mkw 0x4ffedffb1000c002 0x04ffedffb1000c00 0x5fffffff8000f003 0xf5fffffff8000f00

def z763 : W := mkw 0x449ec0fb5540ea03 0x0449ec0fb5540ea0 0xf01fe07fffc0ff0d 0x0f01fe07fffc0ff0

def z764 : W := mkw 0x4ffedffb1000c002 0x04ffedffb1000c00 0xcffffffff0007003 0xfcffffffff000700

def z765 : W := mkw 0x2ddea000679e000c 0x02ddea000679e000 0x8fe4e00077c70000 0x48fe4e00077c7000

def z766 : W := mkw 0x4fded8fb00000000 0x04fded8fb0000000 0x4ffffc7f80000003 0xf4ffffc7f8000000

def z767 : W := mkw 0x4b605ffb5540ea03 0x04b605ffb5540ea0 0xffe7ffffffc0ff0f 0xfffe7ffffffc0ff0

def z768 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0xf067ee1f89c77c07 0xdf067ee1f89c77c0

def z769 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x501ff07f803880ff 0x3501ff07f803880f

def z770 : W := mkw 0x00aa46ab00000000 0x000aa46ab0000000 0x41e7ef9f80000003 0xd41e7ef9f8000000

def z771 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xbffff383ffff8f0f 0xfbffff383ffff8f0

def z772 : W := mkw 0x0020460900000000 0x0002046090000000 0x41e7ff9f80000003 0xf41e7ff9f8000000

def z773 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x719b13e38e388ff3 0x8719b13e38e388ff

def z774 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8fe4e00071c70000 0xf8fe4e00071c7000

def z775 : W := mkw 0x2ddfa0a26fbe000c 0x02ddfa0a26fbe000 0xafffe383ffff000d 0xfafffe383ffff000

def z776 : W := mkw 0x4960c70900000000 0x04960c7090000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z777 : W := mkw 0x1021660d8aeb3ddc 0x61021660d8aeb3dd 0xf1e7ff9f8fffffff 0xff1e7ff9f8ffffff

def z778 : W := mkw 0x0dde800065140000 0x00dde80006514000 0xafffe0007fff000d 0xfafffe0007fff000

def z779 : W := mkw 0x408ac0ab00000000 0x0408ac0ab0000000 0x4007e01f80000001 0x04007e01f8000000

def z780 : W := mkw 0x42205fff1041faa3 0x842205fff1041faa 0x50001fff8000fff2 0x050001fff8000fff

def z781 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e67e00071c70001 0xd8e67e00071c7000

def z782 : W := mkw 0x241520006fbe000c 0x0241520006fbe000 0xae7fe0007fff000d 0xfae7fe0007fff000

def z783 : W := mkw 0x2d55a0006db60004 0x02d55a0006db6000 0xae67e00079c70000 0xcae67e00079c7000

def z784 : W := mkw 0x44bec6fb00000000 0x044bec6fb0000000 0x41ffffff80000003 0xf41ffffff8000000

def z785 : W := mkw 0x4ffedffb00402800 0x04ffedffb0040280 0xffffffff8fc0ff0f 0xfffffffff8fc0ff0

def z786 : W := mkw 0x0414405900000000 0x0041440590000000 0x401fe07f80000001 0x0401fe07f8000000

def z787 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x8fffe00077ff0009 0x68fffe00077ff000

def z788 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x0007e01f80000000 0x00007e01f8000000

def z789 : W := mkw 0x0020460900000000 0x0002046090000000 0x4067ec1f80000001 0x44067ec1f8000000

def z790 : W := mkw 0x2ddfa000efbe055c 0x42ddfa000efbe055 0xbffff3807fff8fff 0xfbffff3807fff8ff

def z791 : W := mkw 0x06345e591040e802 0x006345e591040e80 0xfe7ffe7ff9c0fc0f 0xffe7ffe7ff9c0fc0

def z792 : W := mkw 0x4ddec0fb00000000 0x04ddec0fb0000000 0x4f9fe07f80000001 0x24f9fe07f8000000

def z793 : W := mkw 0x49eac7af3015d0a2 0x849eac7af3015d0a 0x91e3e383f03ff0fc 0x891e3e383f03ff0f

def z794 : W := mkw 0x2ddfa0a26fbe000c 0x02ddfa0a26fbe000 0xfffff3e3ffff80ff 0xffffff3e3ffff80f

def z795 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0xc067ec1f81c77001 0x4c067ec1f81c7700

def z796 : W := mkw 0x5fdfb9f688e33cc4 0x25fdfb9f688e33cc 0xbf9811e009e77cc4 0x2bf9811e009e77cc

def z797 : W := mkw 0x2d54a0a2e5960554 0x42d54a0a2e596055 0xde64f3e3f1c78ff2 0x4de64f3e3f1c78ff

def z798 : W := mkw 0x2ddfa0506fbe002c 0x82ddfa0506fbe002 0xafffe0607fff003d 0xfafffe0607fff003

def z799 : W := mkw 0x1021660d8aeb3ccc 0x21021660d8aeb3cc 0xf067ee1f8fff7ccf 0xdf067ee1f8fff7cc

def z800 : W := mkw 0x12213f0498e3fec7 0x212213f0498e3fec 0xb0001f8009e7ffc6 0x0b0001f8009e7ffc

def z801 : W := mkw 0x008b20a28aaa055c 0x4008b20a28aaa055 0xf19b13e38fff8fff 0xbf19b13e38fff8ff

def z802 : W := mkw 0x2ddea000679e000c 0x02ddea000679e000 0xaffce0007fdf000c 0xfaffce0007fdf000

def z803 : W := mkw 0x2bcbb8545fabd0ae 0x82bcbb8545fabd0a 0x71e3fc7c0fc0f0f2 0x871e3fc7c0fc0f0f

def z804 : W := mkw 0x16357e59b8f6ec66 0xa16357e59b8f6ec6 0x2e7bf263f9d88c38 0xa2e7bf263f9d88c3

def z805 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb000000009fffcfc 0x0b000000009fffcf

def z806 : W := mkw 0x00aa460900000000 0x000aa46090000000 0x41ffee1f80000003 0xf41ffee1f8000000

def z807 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe7ff807fc0ff0f 0xfbfe7ff807fc0ff0

def z808 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf07fee7f89ff7cf7 0xdf07fee7f89ff7cf

def z809 : W := mkw 0x000000a280000550 0x4000000a28000055 0x719813e38e388fff 0xb719813e38e388ff

def z810 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e64e00071c7000c 0x78e64e00071c7000

def z811 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb18013800fe7ffce 0xbb18013800fe7ffc

def z812 : W := mkw 0x1021260488e33cc4 0x21021260488e33cc 0xb0000e0009e77cc6 0x0b0000e0009e77cc

def z813 : W := mkw 0x0b4019005540ea03 0x00b4019005540ea0 0xbf801d807fc0ff0e 0x7bf801d807fc0ff0

def z814 : W := mkw 0x449ec0fb02080118 0x4449ec0fb0208011 0x401fe07f80180031 0x0401fe07f8018003

def z815 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x5fffffff80008f03 0xf5fffffff80008f0

def z816 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe013807fc0ff0c 0xabfe013807fc0ff0

def z817 : W := mkw 0x49eac7ab00000000 0x049eac7ab0000000 0x41e3ef9f80000002 0x841e3ef9f8000000

def z818 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x5fffffff8000800f 0xf5fffffff8000800

def z819 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x401fec7f80000003 0x5401fec7f8000000

def z820 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0xcffffffff000000f 0xfcffffffff000000

def z821 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xb067ee1f89c77c06 0xdb067ee1f89c77c0

def z822 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x7fffffff88000c07 0xf7fffffff88000c0

def z823 : W := mkw 0x249fa0f6aabf15fc 0xc249fa0f6aabf15f 0x401fe07f803f00f1 0x0401fe07f803f00f

def z824 : W := mkw 0x4ddec0fb00000000 0x04ddec0fb0000000 0x4ffff3ff80000003 0xf4ffff3ff8000000

def z825 : W := mkw 0x2ddfa0006fbe011c 0x42ddfa0006fbe011 0xafffe0007fff833d 0xfafffe0007fff833

def z826 : W := mkw 0x469ed8fb00000000 0x0469ed8fb0000000 0x4e1fec7f80000001 0x44e1fec7f8000000

def z827 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067ec1f89e77cc5 0x4f067ec1f89e77cc

def z828 : W := mkw 0x30012004edf73cc4 0x230012004edf73cc 0xb000000079e77cc4 0x0b000000079e77cc

def z829 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x5fffffff802000c7 0xf5fffffff802000c

def z830 : W := mkw 0x1020660d80c33cc4 0x21020660d80c33cc 0xd067ee1f81c77cc3 0xdd067ee1f81c77cc

def z831 : W := mkw 0x20012004ffbfd5fe 0xc20012004ffbfd5f 0xb00000007ffffffc 0x0b00000007ffffff

def z832 : W := mkw 0x2d55a0006db60004 0x02d55a0006db6000 0x8e67e00071e70001 0x48e67e00071e7000

def z833 : W := mkw 0x2d55a0006fbe000c 0x02d55a0006fbe000 0x8e64e00071ff0000 0x48e64e00071ff000

def z834 : W := mkw 0x0b4019005540ea03 0x00b4019005540ea0 0xbf8013807fc0ff0e 0xbbf8013807fc0ff0

def z835 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xff9c1c7c7e3ff0ff 0xfff9c1c7c7e3ff0f

def z836 : W := mkw 0x061419543015d2a3 0x8061419543015d2a 0xde1c1dfc703ff3ff 0x7de1c1dfc703ff3f

def z837 : W := mkw 0x0960460945000000 0x0096046094500000 0xefe7ee1fffc0000f 0xfefe7ee1fffc0000

def z838 : W := mkw 0x4ffedffb5708c31b 0x44ffedffb5708c31 0x4ffffffff618833b 0xf4ffffffff618833

def z839 : W := mkw 0x0ffedf095540ea03 0x00ffedf095540ea0 0xffffff9fffc0ff0f 0xfffffff9fffc0ff0

def z840 : W := mkw 0x4f75df598a280558 0x44f75df598a28055 0x3e64ec1c0e388ffc 0x43e64ec1c0e388ff

def z841 : W := mkw 0x449ec0fb20140020 0x8449ec0fb2014002 0x401fe07f80180031 0x0401fe07f8018003

def z842 : W := mkw 0x408ac0fb00000000 0x0408ac0fb0000000 0x4003e07f80000000 0x04003e07f8000000

def z843 : W := mkw 0x12ab5faf9a69ffdb 0x612ab5faf9a69ffd 0x719b1fff8e38ffff 0xb719b1fff8e38fff

def z844 : W := mkw 0x30012004efff3ddc 0x630012004efff3dd 0xb00000007ffffffc 0x0b00000007ffffff

def z845 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0xae64e00079c70004 0xdae64e00079c7000

def z846 : W := mkw 0x149f60ffaabf15fc 0xe149f60ffaabf15f 0x401fe07f803f00f1 0x0401fe07f803f00f

def z847 : W := mkw 0x12205e5d1041f8a2 0xa12205e5d1041f8a 0x00000c1c00007000 0x000000c1c0000700

def z848 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x8fffe00071ff0001 0xf8fffe00071ff000

def z849 : W := mkw 0x4ffedffb1040ea03 0x04ffedffb1040ea0 0x7fffffff8e00ff0f 0xf7fffffff8e00ff0

def z850 : W := mkw 0x46345ffb00000000 0x046345ffb0000000 0x4e7fffff80000003 0xf4e7fffff8000000

def z851 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x7fffffff8e388fff 0xf7fffffff8e388ff

def z852 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0x3fe01f807fc0ff0a 0xa3fe01f807fc0ff0

def z853 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xeffff3e3ffff00ff 0xfeffff3e3ffff00f

def z854 : W := mkw 0x2ddfa000efbe044c 0x02ddfa000efbe044 0xefffe003ffff00cd 0xfefffe003ffff00c

def z855 : W := mkw 0x4ffedffb00402800 0x04ffedffb0040280 0xcfffffff81c07003 0xfcfffffff81c0700

def z856 : W := mkw 0x10aa66af02cb399c 0x610aa66af02cb399 0x81fcfdfc07dff338 0x681fcfdfc07dff33

def z857 : W := mkw 0x400040fb00000000 0x0400040fb0000000 0x4007e07f80000001 0x04007e07f8000000

def z858 : W := mkw 0x4ffedffb45000000 0x04ffedffb4500000 0x4ffffffff600000b 0xf4ffffffff600000

def z859 : W := mkw 0x44bec6fb00402800 0x044bec6fb0040280 0xf07fee7f89c07c07 0xdf07fee7f89c07c0

def z860 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xae7fe0007fff000d 0x4ae7fe0007fff000

def z861 : W := mkw 0x6ddec0fb671c0008 0x06ddec0fb671c000 0x4f9fe07ff6180009 0x24f9fe07ff618000

def z862 : W := mkw 0x4ffedffb321cc13a 0xc4ffedffb321cc13 0x4ffffffff618833b 0xf4ffffffff618833

def z863 : W := mkw 0x0020460900402800 0x0002046090040280 0x5067ee1f80007c03 0xd5067ee1f80007c0

def z864 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe00f807fc07f06 0xdbfe00f807fc07f0

def z865 : W := mkw 0x0414200020960004 0x0041420002096000 0x8e7ce00071ff000d 0x78e7ce00071ff000

def z866 : W := mkw 0x4ffedffb20140000 0x04ffedffb2014000 0x4ffffffff018000b 0xf4ffffffff018000

def z867 : W := mkw 0x0b605f095540ea03 0x00b605f095540ea0 0xbfe3ff83ffc0ff0e 0xfbfe3ff83ffc0ff0

def z868 : W := mkw 0x4ffedffb7514c223 0x84ffedffb7514c22 0x4ffffffff618833b 0xf4ffffffff618833

def z869 : W := mkw 0x469ed9fb00000000 0x0469ed9fb0000000 0x401ff1ff80000001 0x0401ff1ff8000000

def z870 : W := mkw 0x12205e5d1041f8a2 0xa12205e5d1041f8a 0x50001c7c0000f0f2 0x050001c7c0000f0f

def z871 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0xdfffffff80007007 0xfdfffffff8000700

def z872 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x719f1fff8e388fff 0xf719f1fff8e388ff

def z873 : W := mkw 0x2d55a0006db60004 0x02d55a0006db6000 0xae7fe00079ff000d 0xfae7fe00079ff000

def z874 : W := mkw 0x4ffedffb5500c002 0x04ffedffb5500c00 0xffffffffffc0f00f 0xfffffffffffc0f00

def z875 : W := mkw 0x6fde99f2771cc20b 0x06fde99f2771cc20 0x0f9811e076188308 0x20f9811e07618830

def z876 : W := mkw 0x19612704cde33ec5 0x219612704cde33ec 0xb1e003800fe77fc4 0x8b1e003800fe77fc

def z877 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe01d807fc0ff0c 0x6bfe01d807fc0ff0

def z878 : W := mkw 0x1b613f0488e33cc4 0x21b613f0488e33cc 0xbfe01f8009e77cc6 0xfbfe01f8009e77cc

def z879 : W := mkw 0x02201e001040e802 0x002201e001040e80 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z880 : W := mkw 0x0dfec60945402800 0x00dfec6094540280 0xffffee1fffc07c0f 0xfffffee1fffc07c0

def z881 : W := mkw 0x12205eff9041fdf2 0xe12205eff9041fdf 0x50001fff8000fff2 0x050001fff8000fff

def z882 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0x8000000001e770c0 0x08000000001e770c

def z883 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0xcfffffff80270007 0xfcfffffff8027000

def z884 : W := mkw 0x2ddfa0006db60004 0x02ddfa0006db6000 0xafffe00079e70005 0xfafffe00079e7000

def z885 : W := mkw 0x0001200008a20004 0x00001200008a2000 0xae67e00079e7000d 0xfae67e00079e7000

def z886 : W := mkw 0x4dfec7fb00000000 0x04dfec7fb0000000 0x4fffe3ff80000001 0xf4fffe3ff8000000

def z887 : W := mkw 0x0ddfa00028b60004 0x00ddfa00028b6000 0xafffe00079ff000d 0xfafffe00079ff000

def z888 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb000020009e77cc6 0x9b000020009e77cc

def z889 : W := mkw 0x09eac60900000000 0x009eac6090000000 0x41e7ee1f80000003 0xd41e7ee1f8000000

def z890 : W := mkw 0x049f20002abe000c 0x0049f20002abe000 0xafffe0007fff000d 0xfafffe0007fff000

def z891 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e64e00071e70005 0x58e64e00071e7000

def z892 : W := mkw 0x2d55a0006db60004 0x02d55a0006db6000 0xae64e00079e70004 0x4ae64e00079e7000

def z893 : W := mkw 0x4ffedffb7554ea03 0x04ffedffb7554ea0 0xffffffffffffff0f 0xfffffffffffffff0

def z894 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe00f807fc0ff0c 0xcbfe00f807fc0ff0

def z895 : W := mkw 0x0b605f095540ea03 0x00b605f095540ea0 0xbfe4ff9c7fc0ff0e 0xfbfe4ff9c7fc0ff0

def z896 : W := mkw 0x1b413904dde3fec7 0x21b413904dde3fec 0xbf8011807fe7ffcc 0x2bf8011807fe7ffc

def z897 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x5e1c1c7c703ff0fb 0x25e1c1c7c703ff0f

def z898 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x6fffffff8e00000f 0xf6fffffff8e00000

def z899 : W := mkw 0x4ffedffb00402800 0x04ffedffb0040280 0x6fffffff89c00c03 0xf6fffffff89c00c0

def z900 : W := mkw 0x1021260488e33cc4 0x21021260488e33cc 0xb060020009e77cc4 0x8b060020009e77cc

def z901 : W := mkw 0x049ec00900000000 0x0049ec0090000000 0x401fe01f80000001 0x0401fe01f8000000

def z902 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xffe31f83ffc0ff0f 0xfffe31f83ffc0ff0

def z903 : W := mkw 0x4beadffb00000000 0x04beadffb0000000 0x01e3ef9f80000000 0x801e3ef9f8000000

def z904 : W := mkw 0x0fde98f200000000 0x00fde98f20000000 0x4fffffff80000003 0xf4fffffff8000000

def z905 : W := mkw 0x10012004dfebffdf 0x610012004dfebffd 0xb00000007ffffffc 0x0b00000007ffffff

def z906 : W := mkw 0x0020460900000000 0x0002046090000000 0x0067ee1f80000000 0xc0067ee1f8000000

def z907 : W := mkw 0x2ddfa0a26fbe000c 0x02ddfa0a26fbe000 0xaffff1e07fff000d 0xfaffff1e07fff000

def z908 : W := mkw 0x2fde98f2771cc13a 0xc2fde98f2771cc13 0x0f9811e076188338 0x20f9811e07618833

def z909 : W := mkw 0x6fde99f2771cc02a 0x86fde99f2771cc02 0x0f9811e076188038 0x20f9811e07618803

def z910 : W := mkw 0x008a00a200000000 0x0008a00a20000000 0x719b13e38e388fff 0xb719b13e38e388ff

def z911 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0x8067ec1f81c77000 0x48067ec1f81c7700

def z912 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb004000009e77cc5 0x5b004000009e77cc

def z913 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e7ffe7f80000003 0xf4e7ffe7f8000000

def z914 : W := mkw 0x1021660d8aeb3ddc 0x61021660d8aeb3dd 0xf067ee1f8fe77fc7 0xdf067ee1f8fe77fc

def z915 : W := mkw 0x46bedffb00000000 0x046bedffb0000000 0x4e1fffff80000003 0x74e1fffff8000000

def z916 : W := mkw 0x0ddec00900000000 0x00ddec0090000000 0x4fffe01f80000001 0xf4fffe01f8000000

def z917 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fffffff8018803b 0xf4fffffff8018803

def z918 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xbfffe0007fff80fd 0xfbfffe0007fff80f

def z919 : W := mkw 0x1001200488e33dd4 0x61001200488e33dd 0xb000000009e7fff4 0x0b000000009e7fff

def z920 : W := mkw 0x1201380498e3fcc6 0x21201380498e3fcc 0xbe001c0079e7fcce 0x7be001c0079e7fcc

def z921 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xffffe263ffff0cff 0xfffffe263ffff0cf

def z922 : W := mkw 0x4b60df095540ea03 0x04b60df095540ea0 0xbfe0ff807fc0ff0e 0xfbfe0ff807fc0ff0

def z923 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb0000c0009e77cc6 0x5b0000c0009e77cc

def z924 : W := mkw 0x0020460900402800 0x0002046090040280 0x6067ee1f89c00c03 0xd6067ee1f89c00c0

def z925 : W := mkw 0x4ffedffb1040ea03 0x04ffedffb1040ea0 0x4fffffff80007003 0xf4fffffff8000700

def z926 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xa000000009c77c00 0x0a000000009c77c0

def z927 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fffffff803800f3 0xf4fffffff803800f

def z928 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x719813e38e388ffe 0x2719813e38e388ff

def z929 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xffe01fe07fc0fffe 0xfffe01fe07fc0fff

def z930 : W := mkw 0x4434c65900000000 0x04434c6590000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z931 : W := mkw 0x4ffedffb20140000 0x04ffedffb2014000 0x4fffffff803f0003 0xf4fffffff803f000

def z932 : W := mkw 0x10012004cde33ec5 0x210012004cde33ec 0xb00000000fe77fc4 0x0b00000000fe77fc

def z933 : W := mkw 0x1021670d88e33ec5 0x21021670d88e33ec 0xf067ef9f89e77fc7 0xdf067ef9f89e77fc

def z934 : W := mkw 0x0beb5fabdf68ef5b 0x40beb5fabdf68ef5 0xfffffffffff8ffff 0xffffffffffff8fff

def z935 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xbfffe383ffff8ffd 0xfbfffe383ffff8ff

def z936 : W := mkw 0x1021260488e33cc4 0x21021260488e33cc 0xb0600c0009e77cc4 0x4b0600c0009e77cc

def z937 : W := mkw 0x0beb1fa2df68ef5b 0x40beb1fa2df68ef5 0xce7b0c63f1f870f1 0x4ce7b0c63f1f870f

def z938 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xce7fec7ff1c07001 0x4ce7fec7ff1c0700

def z939 : W := mkw 0x0d5520006db60004 0x00d5520006db6000 0xafffe0007fff000d 0xfafffe0007fff000

def z940 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x0fffffff80000000 0xe0fffffff8000000

def z941 : W := mkw 0x0960470945402a01 0x00960470945402a0 0x61e7ef9f8fc00f03 0xd61e7ef9f8fc00f0

def z942 : W := mkw 0x10012004fdf7fee7 0xa10012004fdf7fee 0xb00000007ffffffc 0x0b00000007ffffff

def z943 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x71fff3e38e388fff 0xf71fff3e38e388ff

def z944 : W := mkw 0x0ddfa0004da20004 0x00ddfa0004da2000 0xafffe0007fe7000d 0xfafffe0007fe7000

def z945 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xefffe203ffff000f 0xfefffe203ffff000

def z946 : W := mkw 0x349fe0afaabf15dc 0x6349fe0afaabf15d 0x401fe07f803f00f1 0x0401fe07f803f00f

def z947 : W := mkw 0x39612604efff3ccc 0x239612604efff3cc 0xbfe00e007fff7cce 0xfbfe00e007fff7cc

def z948 : W := mkw 0x2ddfa000efbe055c 0x42ddfa000efbe055 0xafffe0007fff00fd 0xfafffe0007fff00f

def z949 : W := mkw 0x2ddfa0a26fbe011c 0x42ddfa0a26fbe011 0xeffff3e3ffff833f 0xfeffff3e3ffff833

def z950 : W := mkw 0x4b605f595540ea03 0x04b605f595540ea0 0xbfe01f9c7fc0ff0e 0xfbfe01f9c7fc0ff0

def z951 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x2fffe0007fff0009 0xa2fffe0007fff000

def z952 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0x2000000009e70cc0 0x02000000009e70cc

def z953 : W := mkw 0x30012004cfeb3ccc 0x230012004cfeb3cc 0xb00000000fe77cc4 0x0b00000000fe77cc

def z954 : W := mkw 0x44bec6fb00000000 0x044bec6fb0000000 0x401fee7f80000003 0x0401fee7f8000000

def z955 : W := mkw 0x44bec6fb00000000 0x044bec6fb0000000 0x407fec7f80000001 0x4407fec7f8000000

def z956 : W := mkw 0x39ebe6abcfea2d5c 0x639ebe6abcfea2d5 0x21e3e3838fc00f00 0x821e3e3838fc00f0

def z957 : W := mkw 0x3dfec60de75d3cc8 0x23dfec60de75d3cc 0x5f980e1ff6187cca 0x25f980e1ff6187cc

def z958 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067fe7f89e7fcf7 0xdf067fe7f89e7fcf

def z959 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xdffffffff1c0ff03 0xfdffffffff1c0ff0

def z960 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xdffffffff1c0f00f 0xfdffffffff1c0f00

def z961 : W := mkw 0x30012004aaff3ccc 0x230012004aaff3cc 0xb000000009ff7cc4 0x0b000000009ff7cc

def z962 : W := mkw 0x2ddea0a265960004 0x02ddea0a26596000 0xcffff3e3f1c70003 0xfcffff3e3f1c7000

def z963 : W := mkw 0x6ffedffb671c0008 0x06ffedffb671c000 0xcffffffff63f000f 0xfcffffffff63f000

def z964 : W := mkw 0x0b4019005540ea03 0x00b4019005540ea0 0xbfe011807fc0ff0c 0xfbfe011807fc0ff0

def z965 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xfffffffff9c07c07 0xffffffffff9c07c0

def z966 : W := mkw 0x4ffedffb3014c022 0x84ffedffb3014c02 0x5ffffffff03880ff 0xf5ffffffff03880f

def z967 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xafffe003ffff000d 0xfafffe003ffff000

def z968 : W := mkw 0x2d55a000edb60444 0x02d55a000edb6044 0xfe67e203f9e70cc7 0xdfe67e203f9e70cc

def z969 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xaffbe0007fff000c 0xaaffbe0007fff000

def z970 : W := mkw 0x0ffedf0900000000 0x00ffedf090000000 0x4fffff9f80000003 0xf4fffff9f8000000

def z971 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xffffe0007fff00cf 0xfffffe0007fff00c

def z972 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067ee1f89c77cc2 0xcf067ee1f89c77cc

def z973 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde1c0c7c703f70f7 0x5de1c0c7c703f70f

def z974 : W := mkw 0x002046ab00000000 0x0002046ab0000000 0x4067ffff80000003 0xd4067ffff8000000

def z975 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x401ff07f80000003 0x3401ff07f8000000

def z976 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0xff9b13e3fe388fff 0xfff9b13e3fe388ff

def z977 : W := mkw 0x6ffedffb65140000 0x06ffedffb6514000 0x4ffffffff0000003 0xf4ffffffff000000

def z978 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xf000000009e77cc7 0x1f000000009e77cc

def z979 : W := mkw 0x0021660908e22804 0x00021660908e2280 0xf067ee1f89e77c07 0xdf067ee1f89e77c0

def z980 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067ee1f89fffcff 0xdf067ee1f89fffcf

def z981 : W := mkw 0x46bedffb1040ea03 0x046bedffb1040ea0 0x501fffff8000ff03 0x0501fffff8000ff0

def z982 : W := mkw 0x12205f0d1041fa83 0x212205f0d1041fa8 0x10001f9c0000ff02 0x010001f9c0000ff0

def z983 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x619b13e38e388ff9 0xa619b13e38e388ff

def z984 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xbfffec007fff700f 0xfbfffec007fff700

def z985 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xfffff063ffff80ff 0xffffff063ffff80f

def z986 : W := mkw 0x3b613f04fffffecf 0x23b613f04fffffec 0xbfe01f807fffffce 0xfbfe01f807fffffc

def z987 : W := mkw 0x02205e091000c002 0x002205e091000c00 0xde67fe1ff000f00f 0xfde67fe1ff000f00

def z988 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x8e7fe00071ff000d 0x78e7fe00071ff000

def z989 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0xbfe4f3807fc78f0e 0xfbfe4f3807fc78f0

def z990 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xfff81fe07fc0ff0f 0xffff81fe07fc0ff0

def z991 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0x8e67e00071c70000 0x48e67e00071c7000

def z992 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xffffe383ffff0fcf 0xfffffe383ffff0fc

def z993 : W := mkw 0x0020460900000000 0x0002046090000000 0x4063ee1f80000002 0x84063ee1f8000000

def z994 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xeffff0607fff000f 0xfeffff0607fff000

def z995 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0x9e1c1c7c703ff0fc 0x69e1c1c7c703ff0f

def z996 : W := mkw 0x094120004da20004 0x0094120004da2000 0xae67e00079e70005 0xdae67e00079e7000

def z997 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x719b13e38e188ffa 0xa719b13e38e188ff

def z998 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xfffffffffff8ffff 0xffffffffffff8fff

def z999 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xbfe7ff9fffc0ff0e 0xfbfe7ff9fffc0ff0

def z1000 : W := mkw 0x008a00a282080558 0x4008a00a28208055 0x719813e38e188ffe 0xb719813e38e188ff

def z1001 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fffffff8600830b 0xf4fffffff8600830

def z1002 : W := mkw 0x6ffedffb671c0118 0x46ffedffb671c011 0x4ffffffff618833b 0xf4ffffffff618833

def z1003 : W := mkw 0x4fded9fb00000000 0x04fded9fb0000000 0x4f9ffdff80000003 0x74f9ffdff8000000

def z1004 : W := mkw 0x19412004cde33cc4 0x219412004cde33cc 0xbfe000007fe77ccc 0xfbfe000007fe77cc

def z1005 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x6fffffff8e000f03 0xf6fffffff8e000f0

def z1006 : W := mkw 0x0bea5fab5540ea03 0x00bea5fab5540ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z1007 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde7ffc7c703ff0ff 0xfde7ffc7c703ff0f

def z1008 : W := mkw 0x10012004dde3fec7 0x210012004dde3fec 0xb000000079e77cc4 0x0b000000079e77cc

def z1009 : W := mkw 0x4ffedffb3014c022 0x84ffedffb3014c02 0xdffffffff018f03f 0xfdffffffff018f03

def z1010 : W := mkw 0x208ba0a28aaa055c 0x4208ba0a28aaa055 0x719bf3e38e388fff 0xb719bf3e38e388ff

def z1011 : W := mkw 0x2d55a0006db60004 0x02d55a0006db6000 0xafe7e0007fe7000d 0xfafe7e0007fe7000

def z1012 : W := mkw 0x2ddfa0a26fbe000c 0x02ddfa0a26fbe000 0xfffff3e3ffff8f0f 0xffffff3e3ffff8f0

def z1013 : W := mkw 0x049f20a2aabe055c 0x4049f20a2aabe055 0xfffff3e3ffff8fff 0xffffff3e3ffff8ff

def z1014 : W := mkw 0x469ed8fb00000000 0x0469ed8fb0000000 0x4e1ff07f80000001 0x24e1ff07f8000000

def z1015 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x401fe27f80000003 0x9401fe27f8000000

def z1016 : W := mkw 0x49eac7ab45402a01 0x049eac7ab45402a0 0xf1e7ef9f8fc07f07 0xdf1e7ef9f8fc07f0

def z1017 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x407fe07f80000001 0xd407fe07f8000000

def z1018 : W := mkw 0x4ffedffb00000110 0x44ffedffb0000011 0x4fffffff80008333 0xf4fffffff8000833

def z1019 : W := mkw 0x42aa5ffb00000000 0x042aa5ffb0000000 0x41ffffff80000003 0xf41ffffff8000000

def z1020 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb060000009e77cc4 0xdb060000009e77cc

def z1021 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4e7ffc7f80000003 0x74e7ffc7f8000000

def z1022 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xb00000000fe7ffcc 0x0b00000000fe7ffc

def z1023 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x419ff1ff80000001 0x2419ff1ff8000000

def z1024 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0x3000000009c07cc0 0x03000000009c07cc

def z1025 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x00180060003800f0 0x000180060003800f

def z1026 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xae7fe00079ff0005 0xdae7fe00079ff000

def z1027 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x0fe7ff9f80000002 0xf0fe7ff9f8000000

def z1028 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fffffff8038000f 0xf4fffffff8038000

def z1029 : W := mkw 0x1021660d08e33884 0x21021660d08e3388 0xe067ee1f89e77007 0xde067ee1f89e7700

def z1030 : W := mkw 0x2ddea00065960004 0x02ddea0006596000 0x8fe7e00071c70000 0xc8fe7e00071c7000

def z1031 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4e7fee7f80000003 0xd4e7fee7f8000000

def z1032 : W := mkw 0x4ffedffb45000000 0x04ffedffb4500000 0xffffffffffc08f0f 0xfffffffffffc08f0

def z1033 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4ffffdff80000001 0x64ffffdff8000000

def z1034 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e64e00071ff000c 0x48e64e00071ff000

def z1035 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xaffff0607fff803d 0xfaffff0607fff803

def z1036 : W := mkw 0x4f74dffb00000000 0x04f74dffb0000000 0x4e67ffff80000003 0xd4e67ffff8000000

def z1037 : W := mkw 0x4dfec7fb00000000 0x04dfec7fb0000000 0x41ffefff80000003 0xd41ffefff8000000

def z1038 : W := mkw 0x020018041001d082 0x0020018041001d08 0xde1c1c7c703ff0ff 0x7de1c1c7c703ff0f

def z1039 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xce1c0c7c703f70fd 0x7ce1c0c7c703f70f

def z1040 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafffe3807fff0f0d 0xfafffe3807fff0f0

def z1041 : W := mkw 0x2d55a0006fbe000c 0x02d55a0006fbe000 0xafe4e0007fff000c 0xfafe4e0007fff000

def z1042 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xfe1c1c7c7e3fffff 0x7fe1c1c7c7e3ffff

def z1043 : W := mkw 0x0414000420151080 0x0041400042015108 0xde1c1c7c703ff0ff 0x7de1c1c7c703ff0f

def z1044 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xefffffffffc0700f 0xfefffffffffc0700

def z1045 : W := mkw 0x19eb67abcfea2f5d 0x619eb67abcfea2f5 0x21e3e3838fc00f00 0x821e3e3838fc00f0

def z1046 : W := mkw 0x0960070045402a01 0x00960070045402a0 0xbfe00f807fc07f0e 0xfbfe00f807fc07f0

def z1047 : W := mkw 0x4ffedffb65140000 0x04ffedffb6514000 0xefffffffffff000f 0xfefffffffffff000

def z1048 : W := mkw 0x52205fff9041fec3 0x252205fff9041fec 0x50001fff8000ffc2 0x050001fff8000ffc

def z1049 : W := mkw 0x2d55a0006fbe000c 0x02d55a0006fbe000 0xae67e0007fff000d 0xdae67e0007fff000

def z1050 : W := mkw 0x096007005540ea03 0x0096007005540ea0 0xbfe003807fc0ff0c 0xfbfe003807fc0ff0

def z1051 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xafe01f807fc07f02 0xfafe01f807fc07f0

def z1052 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4ffbffff80000002 0xa4ffbffff8000000

def z1053 : W := mkw 0x4ffedffb5500c203 0x04ffedffb5500c20 0xdffffffff600f30f 0xfdffffffff600f30

def z1054 : W := mkw 0x46bedffb00000000 0x046bedffb0000000 0x419fffff80000003 0xb419fffff8000000

def z1055 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf07ffe7f89e77cc7 0xff07ffe7f89e77cc

def z1056 : W := mkw 0x108b20a68aeb3ddc 0x6108b20a68aeb3dd 0xb19811e00ffffffc 0x2b19811e00ffffff

def z1057 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xaffff3e3ffff8f3d 0xfaffff3e3ffff8f3

def z1058 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xffe41f9c7fc0ff0f 0xfffe41f9c7fc0ff0

def z1059 : W := mkw 0x1021660d8aeb3ddc 0x61021660d8aeb3dd 0xf07ffe7f8fffffff 0xff07ffe7f8ffffff

def z1060 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xce1c1c7c703f70f3 0x7ce1c1c7c703f70f

def z1061 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e7ce00071c70001 0x78e7ce00071c7000

def z1062 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xfffff3e07fff8fff 0xffffff3e07fff8ff

def z1063 : W := mkw 0x49eac7fb00000000 0x049eac7fb0000000 0x41e3e3ff80000000 0x841e3e3ff8000000

def z1064 : W := mkw 0x1001200498e3fce6 0xa1001200498e3fce 0xb000000009e7fcf4 0x0b000000009e7fcf

def z1065 : W := mkw 0x2ddfa0506fbe000c 0x02ddfa0506fbe000 0xefffe07c7fff000d 0xfefffe07c7fff000

def z1066 : W := mkw 0x10012004a8b714e4 0xa10012004a8b714e 0x00000000003f00f0 0x000000000003f00f

def z1067 : W := mkw 0x0960470900000000 0x0096047090000000 0x41e7ef9f80000003 0xd41e7ef9f8000000

def z1068 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafe7e0007fc7000c 0xfafe7e0007fc7000

def z1069 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xbfffe0007fff8f0d 0xfbfffe0007fff8f0

def z1070 : W := mkw 0x6ffedffb775cea0b 0x06ffedffb775cea0 0xffffffffffd8ff0f 0xfffffffffffd8ff0

def z1071 : W := mkw 0x4f74df595540ea03 0x04f74df595540ea0 0xffe7ff9fffc0ff0f 0xfffe7ff9fffc0ff0

def z1072 : W := mkw 0x0940000045000000 0x0094000004500000 0xafe7e0007fc0000d 0xfafe7e0007fc0000

def z1073 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xbffff1e07fff8ffd 0xfbffff1e07fff8ff

def z1074 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf07fee1f89ff7ccf 0xff07fee1f89ff7cc

def z1075 : W := mkw 0x0434460920140000 0x0043446092014000 0xce7fee1ff03f000f 0xfce7fee1ff03f000

def z1076 : W := mkw 0x29cba0006fbe000c 0x029cba0006fbe000 0xafe3e0007fff000c 0xfafe3e0007fff000

def z1077 : W := mkw 0x4ffedffb00402a01 0x04ffedffb00402a0 0x4fffffff80000f03 0xf4fffffff80000f0

def z1078 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0x6fffffffffc08f0b 0xf6fffffffffc08f0

def z1079 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x401fe07f803800f1 0x0401fe07f803800f

def z1080 : W := mkw 0x0dfec6ab00000000 0x00dfec6ab0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1081 : W := mkw 0x0f745f595540ea03 0x00f745f595540ea0 0xffffffffffc0ff0f 0xfffffffffffc0ff0

def z1082 : W := mkw 0x52205fff9041fce2 0xa52205fff9041fce 0x50001fff8000fcf2 0x050001fff8000fcf

def z1083 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xafe01f807fc0ff08 0xeafe01f807fc0ff0

def z1084 : W := mkw 0x449ec0fb20140000 0x0449ec0fb2014000 0x401fe07f803f0001 0x0401fe07f803f000

def z1085 : W := mkw 0x1001200498e3fcc6 0x21001200498e3fcc 0xb000000079e7fccc 0x0b000000079e7fcc

def z1086 : W := mkw 0x0b605f095540ea03 0x00b605f095540ea0 0xce67ee1ff1c07003 0xdce67ee1ff1c0700

def z1087 : W := mkw 0x49eac7ab00000000 0x049eac7ab0000000 0x41e7e39f80000001 0x841e7e39f8000000

def z1088 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbff81fe07fd8ff3e 0xfbff81fe07fd8ff3

def z1089 : W := mkw 0x0001000088200440 0x0000100008820044 0x719b13e38e388fff 0xb719b13e38e388ff

def z1090 : W := mkw 0x2ddfa1006fbe020d 0x02ddfa1006fbe020 0xafffe1807fff030d 0xfafffe1807fff030

def z1091 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x319b13e38e388ffc 0xa319b13e38e388ff

def z1092 : W := mkw 0x4fded9fb00000000 0x04fded9fb0000000 0x4ffff1ff80000001 0xf4ffff1ff8000000

def z1093 : W := mkw 0x4ffedffb1040ea03 0x04ffedffb1040ea0 0xffffffff89c0ff07 0xfffffffff89c0ff0

def z1094 : W := mkw 0x4ffedffb5500c203 0x04ffedffb5500c20 0x7ffffffffe008f0f 0xf7ffffffffe008f0

def z1095 : W := mkw 0x008a00a282080558 0x4008a00a28208055 0x519b13e386188ffb 0xb519b13e386188ff

def z1096 : W := mkw 0x4ffedf5900000000 0x04ffedf590000000 0x4fffee1f80000003 0xf4fffee1f8000000

def z1097 : W := mkw 0x29cba0004faa000c 0x029cba0004faa000 0xafe7e0007fe7000d 0xfafe7e0007fe7000

def z1098 : W := mkw 0x6ffedffb47080008 0x06ffedffb4708000 0x4fffffff86000003 0xf4fffffff8600000

def z1099 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xaffff1807fff830d 0xfaffff1807fff830

def z1100 : W := mkw 0x0000400900000000 0x0000040090000000 0x4007ec1f80000003 0x54007ec1f8000000

def z1101 : W := mkw 0x0b605f095540ea03 0x00b605f095540ea0 0xffe01f9fffc0ff0e 0xfffe01f9fffc0ff0

def z1102 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xefffffffffc07f03 0xfefffffffffc07f0

def z1103 : W := mkw 0x0415200028b60004 0x00415200028b6000 0xae67e00079e70005 0xdae67e00079e7000

def z1104 : W := mkw 0x0020460900000000 0x0002046090000000 0xe067ee1f89c00007 0xde067ee1f89c0000

def z1105 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xeffff3e3ffff0f0f 0xfeffff3e3ffff0f0

def z1106 : W := mkw 0x6ffedffb221c0008 0x06ffedffb221c000 0x4fffffff80180003 0xf4fffffff8018000

def z1107 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4fe7ff9f80000003 0xf4fe7ff9f8000000

def z1108 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xa067ee1f89e77c05 0xda067ee1f89e77c0

def z1109 : W := mkw 0x1f747f5d75d7faa7 0xa1f747f5d75d7faa 0x8e64ec1c71c77000 0x48e64ec1c71c7700

def z1110 : W := mkw 0x0020460900000000 0x0002046090000000 0x5067ee1f802000c7 0xd5067ee1f802000c

def z1111 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0xde7cf06071ff80ff 0x7de7cf06071ff80f

def z1112 : W := mkw 0x1001200488a314c4 0x21001200488a314c 0xa000000009e700c4 0x0a000000009e700c

def z1113 : W := mkw 0x2ddfa000efbe055c 0x42ddfa000efbe055 0xffffe203ffff8fff 0xfffffe203ffff8ff

def z1114 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde1f1e7ff03ff0ff 0xfde1f1e7ff03ff0f

def z1115 : W := mkw 0x4ffedffb3014c022 0x84ffedffb3014c02 0xcffffffff03f803f 0xfcffffffff03f803

def z1116 : W := mkw 0x06be5efb00000000 0x006be5efb0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1117 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0xf018106009fffcff 0x3f018106009fffcf

def z1118 : W := mkw 0x3ddfa004efff3ccc 0x23ddfa004efff3cc 0xbf9800007fff7ccc 0x2bf9800007fff7cc

def z1119 : W := mkw 0x2ddea00065960004 0x02ddea0006596000 0x8fffe00071ff000d 0xf8fffe00071ff000

def z1120 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x4063ffff80000002 0x84063ffff8000000

def z1121 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x419fe3ff80000001 0x8419fe3ff8000000

def z1122 : W := mkw 0x0bea5fab00000000 0x00bea5fab0000000 0x4fffffff80000003 0xf4fffffff8000000

def z1123 : W := mkw 0x0020460900000000 0x0002046090000000 0x4007ee1f80000003 0x04007ee1f8000000

def z1124 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fe7ef9f80000003 0xd4fe7ef9f8000000

def z1125 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xffe01f807fe0ffcf 0xfffe01f807fe0ffc

def z1126 : W := mkw 0x0000400900000000 0x0000040090000000 0x4007e21f80000003 0x94007e21f8000000

def z1127 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4f9fffff80000003 0x24f9fffff8000000

def z1128 : W := mkw 0x2fffff097ffeea0f 0x02fffff097ffeea0 0xffffff9fffffff0f 0xfffffff9fffffff0

def z1129 : W := mkw 0x100120048aab15dc 0x6100120048aab15d 0x00000000003f00f0 0x000000000003f00f

def z1130 : W := mkw 0x1001200488e33cc4 0x21001200488e33cc 0x1000000000277cc0 0x01000000000277cc

def z1131 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xcffffffff7c0f30b 0xfcffffffff7c0f30

def z1132 : W := mkw 0x4ddec0fb45000000 0x04ddec0fb4500000 0xefffe07fffc0000d 0xfefffe07fffc0000

def z1133 : W := mkw 0x1b613f04dde3fec7 0x21b613f04dde3fec 0xbe600c0079e77cc4 0x4be600c0079e77cc

def z1134 : W := mkw 0x0020460900000000 0x0002046090000000 0xd067ee1f80007007 0xdd067ee1f8000700

def z1135 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0x7fffffff8fc0ff03 0xf7fffffff8fc0ff0

def z1136 : W := mkw 0x12205e5d9041fce2 0xa12205e5d9041fce 0x50000e1f80007cc2 0x050000e1f80007cc

def z1137 : W := mkw 0x00aa46ab00000000 0x000aa46ab0000000 0x407fee7f80000003 0xd407fee7f8000000

def z1138 : W := mkw 0x0020460d00413880 0x00020460d0041388 0xf067ee1f89e77cc7 0xdf067ee1f89e77cc

def z1139 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4fffefff80000001 0xc4fffefff8000000

def z1140 : W := mkw 0x0940200045820004 0x0094020004582000 0xafe4e0007fc7000c 0xfafe4e0007fc7000

def z1141 : W := mkw 0x30012004fffffecf 0x230012004fffffec 0xb00000007fffffcc 0x0b00000007fffffc

def z1142 : W := mkw 0x00aa46ab00402800 0x000aa46ab0040280 0xf1ffffff8fc0ff0f 0xff1ffffff8fc0ff0

def z1143 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0x7067ee1f89e77cc3 0x87067ee1f89e77cc

def z1144 : W := mkw 0x4fded9fb5500c203 0x04fded9fb5500c20 0x4f9ff1fff6008309 0x24f9ff1fff600830

def z1145 : W := mkw 0x0f745f5d7555faa3 0x80f745f5d7555faa 0xffffffffffffffff 0xffffffffffffffff

def z1146 : W := mkw 0x44bec6fb00000000 0x044bec6fb0000000 0x407fe27f80000001 0x8407fe27f8000000

def z1147 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0xefffffff89c00007 0xfefffffff89c0000

def z1148 : W := mkw 0x294120006fbe000c 0x0294120006fbe000 0xafe7e0007fff000d 0xfafe7e0007fff000

def z1149 : W := mkw 0x02205f0900000000 0x002205f090000000 0x4067ff9f80000003 0xd4067ff9f8000000

def z1150 : W := mkw 0x4ffedffb45402a01 0x04ffedffb45402a0 0xffffffff8fc07f07 0xfffffffff8fc07f0

def z1151 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xc067ee1f81e770c3 0xdc067ee1f81e770c

def z1152 : W := mkw 0x0020460900000000 0x0002046090000000 0xc067ee1f80270007 0xdc067ee1f8027000

def z1153 : W := mkw 0x249fa0002abe000c 0x0249fa0002abe000 0xae7fe00079ff000d 0xfae7fe00079ff000

def z1154 : W := mkw 0x2ddfa000efbe044c 0x02ddfa000efbe044 0xbfffe0007fff0ccd 0xfbfffe0007fff0cc

def z1155 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafe7e0007fe70005 0xdafe7e0007fe7000

def z1156 : W := mkw 0x449ec0fb20140000 0x0449ec0fb2014000 0xce1fe07ff03f000d 0x7ce1fe07ff03f000

def z1157 : W := mkw 0x42205ffb1040ea03 0x042205ffb1040ea0 0xf067ffff89c0ff07 0xdf067ffff89c0ff0

def z1158 : W := mkw 0x2ddfa0a26fbe011c 0x42ddfa0a26fbe011 0xbffff3e07fff8f3f 0xfbffff3e07fff8f3

def z1159 : W := mkw 0x42205f5900000000 0x042205f590000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z1160 : W := mkw 0x02205e5900000000 0x002205e590000000 0x4067fe7f80000003 0xd4067fe7f8000000

def z1161 : W := mkw 0x30012004aabf14cc 0x230012004aabf14c 0x00000000003f00c0 0x000000000003f00c

def z1162 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x719ff3ff8e008f0f 0xb719ff3ff8e008f0

def z1163 : W := mkw 0x4ffedffb5500c203 0x04ffedffb5500c20 0x4ffffffff0000003 0xf4ffffffff000000

def z1164 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xdf9c1ffc703ff0ff 0xfdf9c1ffc703ff0f

def z1165 : W := mkw 0x12205f0d1041fa83 0x212205f0d1041fa8 0x00000c1c00007000 0x000000c1c0000700

def z1166 : W := mkw 0x30012004fffffcee 0xa30012004fffffce 0xb00000007ffffcfc 0x0b00000007ffffcf

def z1167 : W := mkw 0x094000005540ea03 0x0094000005540ea0 0xbfe013807fc0ff0e 0xfbfe013807fc0ff0

def z1168 : W := mkw 0x42aadffb00000000 0x042aadffb0000000 0x4003ffff80000002 0x04003ffff8000000

def z1169 : W := mkw 0x4dfec6fb00000000 0x04dfec6fb0000000 0x4fffee7f80000003 0xf4fffee7f8000000

def z1170 : W := mkw 0x0b605f095500c203 0x00b605f095500c20 0x4fe7ff9ff600830b 0xf4fe7ff9ff600830

def z1171 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x0e67ee1f80000000 0xc0e67ee1f8000000

def z1172 : W := mkw 0x4ffedffb45000000 0x04ffedffb4500000 0x6fffffff8fc00003 0xf6fffffff8fc0000

def z1173 : W := mkw 0x1b613f04fdf7fee7 0xa1b613f04fdf7fee 0xbfe01f807ffffffe 0xfbfe01f807ffffff

def z1174 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0xf1fb13e38ff88fff 0xff1fb13e38ff88ff

def z1175 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde181c7c703ff0fe 0x2de181c7c703ff0f

def z1176 : W := mkw 0x09cb20004faa000c 0x009cb20004faa000 0xafffe0007fff000d 0xfafffe0007fff000

def z1177 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e7ce00071ff0001 0x48e7ce00071ff000

def z1178 : W := mkw 0x4fded9fb00000000 0x04fded9fb0000000 0x4f9ff3ff80000003 0xb4f9ff3ff8000000

def z1179 : W := mkw 0x1021660d88e33dd4 0x61021660d88e33dd 0xf067ee1f89e7fff7 0xdf067ee1f89e7fff

def z1180 : W := mkw 0x10012004a8f73ce4 0xa10012004a8f73ce 0xb000000009ff7cf4 0x0b000000009ff7cf

def z1181 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067ee1f8fe7ffcf 0xdf067ee1f8fe7ffc

def z1182 : W := mkw 0x1001200488a314c4 0x21001200488a314c 0x90000000002770c4 0x090000000002770c

def z1183 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x0e67ec1f80000000 0x40e67ec1f8000000

def z1184 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8e7ce00071df0008 0x68e7ce00071df000

def z1185 : W := mkw 0x42205ffb00000000 0x042205ffb0000000 0x4007ffff80000003 0x04007ffff8000000

def z1186 : W := mkw 0x4ffedffb45402a01 0x04ffedffb45402a0 0x7fffffff8fc08f0f 0xf7fffffff8fc08f0

def z1187 : W := mkw 0x4ffedffb3014c022 0x84ffedffb3014c02 0x4ffffffff0000003 0xf4ffffffff000000

def z1188 : W := mkw 0x4ffedffb45402a01 0x04ffedffb45402a0 0xefffffffffc00f0f 0xfefffffffffc00f0

def z1189 : W := mkw 0x2ddfa0a2efbe044c 0x02ddfa0a2efbe044 0xfffff3e3ffff0ccf 0xffffff3e3ffff0cc

def z1190 : W := mkw 0x4beadffb00000000 0x04beadffb0000000 0x41e7ffff80000003 0xd41e7ffff8000000

def z1191 : W := mkw 0x0960460900000000 0x0096046090000000 0x4fe7ee1f80000003 0xf4fe7ee1f8000000

def z1192 : W := mkw 0x4f74df595540ea03 0x04f74df595540ea0 0xfe67ee1ff9c07c07 0xdfe67ee1ff9c07c0

def z1193 : W := mkw 0x10012004b8b7d4e6 0xa10012004b8b7d4e 0x90000000703ff0fc 0x090000000703ff0f

def z1194 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0x519b13e386388ffb 0x2519b13e386388ff

def z1195 : W := mkw 0x008a00a282080558 0x4008a00a28208055 0x519813e386388fff 0x3519813e386388ff

def z1196 : W := mkw 0x4ffedffb02080118 0x44ffedffb0208011 0x7fffffff8e188f3f 0xf7fffffff8e188f3

def z1197 : W := mkw 0x2ddea00065960004 0x02ddea0006596000 0x8ffce00071c70000 0x68ffce00071c7000

def z1198 : W := mkw 0x12205faf9041ffd3 0x612205faf9041ffd 0x50001fff8000fff2 0x050001fff8000fff

def z1199 : W := mkw 0x008b20a28aaa055c 0x4008b20a28aaa055 0x71fbf3e38ff88fff 0xb71fbf3e38ff88ff

def z1200 : W := mkw 0x02205f091040ea03 0x002205f091040ea0 0x50001f9f8000ff02 0x050001f9f8000ff0

def z1201 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe01f807fc0ff02 0xcbfe01f807fc0ff0

def z1202 : W := mkw 0x12215f0d9861fec3 0x212215f0d9861fec 0x71831f9f8e20ffcf 0xb71831f9f8e20ffc

def z1203 : W := mkw 0x10012004a8f73cc4 0x210012004a8f73cc 0xb000000079ff7ccc 0x0b000000079ff7cc

def z1204 : W := mkw 0x4ffedffb02080118 0x44ffedffb0208011 0x5fffffff863883ff 0xf5fffffff863883f

def z1205 : W := mkw 0x4ffedffb1040e802 0x04ffedffb1040e80 0xfffffffff9c0fc0f 0xffffffffff9c0fc0

def z1206 : W := mkw 0x6ffedffb671c0008 0x06ffedffb671c000 0xefffffffffd8000f 0xfefffffffffd8000

def z1207 : W := mkw 0x4f74df5d7555faa3 0x84f74df5d7555faa 0x8e64ec1c71c77000 0x48e64ec1c71c7700

def z1208 : W := mkw 0x4dfec7fb00000000 0x04dfec7fb0000000 0x41fff3ff80000003 0xb41fff3ff8000000

def z1209 : W := mkw 0x46bedffb00000000 0x046bedffb0000000 0x401fec7f80000001 0x0401fec7f8000000

def z1210 : W := mkw 0x4ddec0fb00000000 0x04ddec0fb0000000 0x41ffe07f80000001 0x841ffe07f8000000

def z1211 : W := mkw 0x2ddfa000efbe055c 0x42ddfa000efbe055 0xafffe0007fff0f0d 0xfafffe0007fff0f0

def z1212 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde1c0c7c703ff0fd 0x4de1c0c7c703ff0f

def z1213 : W := mkw 0x0b4018005500c002 0x00b4018005500c00 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z1214 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe01f807ff8fffe 0xfbfe01f807ff8fff

def z1215 : W := mkw 0x2ddfa0a26fbe000c 0x02ddfa0a26fbe000 0xefffe063ffff000d 0xfefffe063ffff000

def z1216 : W := mkw 0x2d55a0006fbe000c 0x02d55a0006fbe000 0xae64e0007fc70000 0x4ae64e0007fc7000

def z1217 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067ff9f89e7ffc7 0xdf067ff9f89e7ffc

def z1218 : W := mkw 0x469ed8fb3014c022 0x8469ed8fb3014c02 0x4e1ff07ff0188039 0x24e1ff07ff018803

def z1219 : W := mkw 0x0960060045402800 0x0096006004540280 0xbfe01f807fc0ff0e 0xfbfe01f807fc0ff0

def z1220 : W := mkw 0x12ab5eff9a69fdfa 0xe12ab5eff9a69fdf 0x719b1fff8e38ffff 0xb719b1fff8e38fff

def z1221 : W := mkw 0x1020660d00c33884 0x21020660d00c3388 0xd067ee1f81e770c7 0xdd067ee1f81e770c

def z1222 : W := mkw 0x02205f091040ea03 0x002205f091040ea0 0x5067ff9f8000ff03 0xd5067ff9f8000ff0

def z1223 : W := mkw 0x2ddfa000efbe055c 0x42ddfa000efbe055 0xfffff0607fff8fff 0xffffff0607fff8ff

def z1224 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbfe41f807fe7ff0f 0xfbfe41f807fe7ff0

def z1225 : W := mkw 0x100120048aeb3ddc 0x6100120048aeb3dd 0xb000000009ff7cf4 0x0b000000009ff7cf

def z1226 : W := mkw 0x12213e04b8f7fce6 0xa12213e04b8f7fce 0xbe601e0079fffcfe 0xfbe601e0079fffcf

def z1227 : W := mkw 0x249fa0002abe000c 0x0249fa0002abe000 0x00180000003f0000 0x000180000003f000

def z1228 : W := mkw 0x02205e0900000000 0x002205e090000000 0x4e67fe1f80000003 0xf4e67fe1f8000000

def z1229 : W := mkw 0x4ffedffb1000c022 0x84ffedffb1000c02 0x4fffffff80008033 0xf4fffffff8000803

def z1230 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xefffe0607fff00fd 0xfefffe0607fff00f

def z1231 : W := mkw 0x100120048aeb3ccc 0x2100120048aeb3cc 0xb00000000fff7ccc 0x0b00000000fff7cc

def z1232 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0xf19f13e38e3f8fff 0xff19f13e38e3f8ff

def z1233 : W := mkw 0x469ed8fb00000000 0x0469ed8fb0000000 0x401ffc7f80000003 0x0401ffc7f8000000

def z1234 : W := mkw 0x4ffedffb00402800 0x04ffedffb0040280 0x5fffffff80007c03 0xf5fffffff80007c0

def z1235 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xe067ee1f89e77cc1 0xce067ee1f89e77cc

def z1236 : W := mkw 0x49eac7ab00000000 0x049eac7ab0000000 0x41ffffff80000003 0xf41ffffff8000000

def z1237 : W := mkw 0x1001200488a314c4 0x21001200488a314c 0x3000000008270cc4 0x03000000008270cc

def z1238 : W := mkw 0x46bedffb00000000 0x046bedffb0000000 0x407fffff80000003 0xd407fffff8000000

def z1239 : W := mkw 0x100120048aab15dc 0x6100120048aab15d 0x300000000e3f8ffc 0x0300000000e3f8ff

def z1240 : W := mkw 0x649ec0fb221c0008 0x0649ec0fb221c000 0x401fe07f80180001 0x0401fe07f8018000

def z1241 : W := mkw 0x4414c05900000000 0x04414c0590000000 0x4007e01f80000001 0x04007e01f8000000

def z1242 : W := mkw 0x09cb20a2cfaa055c 0x409cb20a2cfaa055 0xfffff3e3ffff8fff 0xffffff3e3ffff8ff

def z1243 : W := mkw 0x40aac6ab00000000 0x040aac6ab0000000 0x4067ee1f80000003 0xd4067ee1f8000000

def z1244 : W := mkw 0x04140054201510a0 0x804140054201510a 0xde1c0c7c703f70ff 0x7de1c0c7c703f70f

def z1245 : W := mkw 0x4ffedffb45402a01 0x04ffedffb45402a0 0x4fffffff81c00003 0xf4fffffff81c0000

def z1246 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xefffe3e3ffff0ffd 0xfefffe3e3ffff0ff

def z1247 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0xafe4e0007fc70000 0xcafe4e0007fc7000

def z1248 : W := mkw 0x4dfec7ab00000000 0x04dfec7ab0000000 0x4fffef9f80000003 0xf4fffef9f8000000

def z1249 : W := mkw 0x04140054201510a0 0x804140054201510a 0x00180060003f00f0 0x000180060003f00f

def z1250 : W := mkw 0x4f74df5900000000 0x04f74df590000000 0x4e67ec1f80000001 0x44e67ec1f8000000

def z1251 : W := mkw 0x0d74075465553aa1 0x80d74075465553aa 0x61fc03fc0fff0ff1 0x861fc03fc0fff0ff

def z1252 : W := mkw 0x008b20a28aaa055c 0x4008b20a28aaa055 0x719ff3e38e3f8fff 0xb719ff3e38e3f8ff

def z1253 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xafe7e383ffc70f00 0xcafe7e383ffc70f0

def z1254 : W := mkw 0x14152004a8f73cc4 0x214152004a8f73cc 0xbe1c000079ff7ccd 0x7be1c000079ff7cc

def z1255 : W := mkw 0x30012004efbf14cc 0x230012004efbf14c 0xa00000007fff00cc 0x0a00000007fff00c

def z1256 : W := mkw 0x6ffedffb771cc20b 0x06ffedffb771cc20 0x4ffffffff618830b 0xf4ffffffff618830

def z1257 : W := mkw 0x0000000000000000 0x0000000000000000 0x718313838e008f0f 0xb718313838e008f0

def z1258 : W := mkw 0x44bec7fb00000000 0x044bec7fb0000000 0x401fe3ff80000001 0x0401fe3ff8000000

def z1259 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xbff81f807ff8ff0f 0xfbff81f807ff8ff0

def z1260 : W := mkw 0x16153854b8f7fce6 0xa16153854b8f7fce 0xbe18106079fffcfc 0x2be18106079fffcf

def z1261 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafe7e0007fff000c 0xcafe7e0007fff000

def z1262 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x4e1fe07f80000001 0x74e1fe07f8000000

def z1263 : W := mkw 0x2ddfa000efbe044c 0x02ddfa000efbe044 0xafffe203ffff0c0d 0xfafffe203ffff0c0

def z1264 : W := mkw 0x2dfec609671c0008 0x02dfec609671c000 0x4fffee1ff618000b 0xf4fffee1ff618000

def z1265 : W := mkw 0x10012004cde33cc4 0x210012004cde33cc 0xb00000007fe77ccc 0x0b00000007fe77cc

def z1266 : W := mkw 0x4ffedffb20140000 0x04ffedffb2014000 0xdffffffff03f80ff 0xfdffffffff03f80f

def z1267 : W := mkw 0x4beadffb5540ea03 0x04beadffb5540ea0 0x71e3ffff8fc0ff02 0x871e3ffff8fc0ff0

def z1268 : W := mkw 0x0f745f5900000000 0x00f745f590000000 0x4fffffff80000003 0xf4fffffff8000000

def z1269 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xfe7c1c7c79fff0ff 0xffe7c1c7c79fff0f

def z1270 : W := mkw 0x0614585900000000 0x0061458590000000 0x4e1ffc7f80000003 0x74e1ffc7f8000000

def z1271 : W := mkw 0x4ffedffb1000c203 0x04ffedffb1000c20 0x4fffffff80008303 0xf4fffffff8000830

def z1272 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf1e7ef9f8fe77fc7 0xdf1e7ef9f8fe77fc

def z1273 : W := mkw 0x4ffedffb5540ea03 0x04ffedffb5540ea0 0xafe7ef9fffc07f00 0xcafe7ef9fffc07f0

def z1274 : W := mkw 0x0434465900000000 0x0043446590000000 0x407fee7f80000003 0xd407fee7f8000000

def z1275 : W := mkw 0x0b601f505540ea23 0x80b601f505540ea2 0xbfe01fe07fc0ff3e 0xfbfe01fe07fc0ff3

def z1276 : W := mkw 0x449ec0fb00000000 0x0449ec0fb0000000 0x401ff3ff80000003 0x0401ff3ff8000000

def z1277 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf067fe1f89e7fccf 0xff067fe1f89e7fcc

def z1278 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xafffe0007fc70001 0xfafffe0007fc7000

def z1279 : W := mkw 0x1001600d88a314c4 0x21001600d88a314c 0xf067ec1f89e770c7 0xdf067ec1f89e770c

def z1280 : W := mkw 0x2ddfa000efbe044c 0x02ddfa000efbe044 0xfffff263ffff8cff 0xffffff263ffff8cf

def z1281 : W := mkw 0x020018001000c002 0x0020018001000c00 0xde041c1c7000f00f 0x7de041c1c7000f00

def z1282 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4ffff3ff80000001 0xa4ffff3ff8000000

def z1283 : W := mkw 0x6ffedffb771cc02a 0x86ffedffb771cc02 0x4ffffffff618803b 0xf4ffffffff618803

def z1284 : W := mkw 0x0b601f505540ea03 0x00b601f505540ea0 0xffe01ffc7fc0ff0e 0xfffe01ffc7fc0ff0

def z1285 : W := mkw 0x2d55a0006fbe000c 0x02d55a0006fbe000 0xae7ce0007fff000d 0x7ae7ce0007fff000

def z1286 : W := mkw 0x0020460900402800 0x0002046090040280 0xc067ee1f81c07003 0xdc067ee1f81c0700

def z1287 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xeffff1e3ffff83fd 0xfeffff1e3ffff83f

def z1288 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0x8fe4e00077c70008 0x68fe4e00077c7000

def z1289 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x4e7fffff80000003 0x44e7fffff8000000

def z1290 : W := mkw 0x0021660d08a31084 0x00021660d08a3108 0xf067ee1f89e770c7 0xdf067ee1f89e770c

def z1291 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xe067ee1f89c77c03 0xde067ee1f89c77c0

def z1292 : W := mkw 0x4ffedffb1000c002 0x04ffedffb1000c00 0xdffffffff038f0ff 0xfdffffffff038f0f

def z1293 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xe067ec1f89e770c5 0xde067ec1f89e770c

def z1294 : W := mkw 0x4ffedffb3014c002 0x04ffedffb3014c00 0xdffffffff03ff00f 0xfdffffffff03ff00

def z1295 : W := mkw 0x04bec60900000000 0x004bec6090000000 0x407fee1f80000003 0xd407fee1f8000000

def z1296 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde1c1c7c703ff0f3 0x4de1c1c7c703ff0f

def z1297 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf1e7ff9f89e77cc7 0xff1e7ff9f89e77cc

def z1298 : W := mkw 0x402047ab00000000 0x0402047ab0000000 0x4067ef9f80000003 0xd4067ef9f8000000

def z1299 : W := mkw 0x402046fb00000000 0x0402046fb0000000 0x4067ee7f80000003 0xd4067ee7f8000000

def z1300 : W := mkw 0x2ddea000679e000c 0x02ddea000679e000 0x8e7ce00071df0000 0x48e7ce00071df000

def z1301 : W := mkw 0x4beadfab00000000 0x04beadfab0000000 0x4fe7ff9f80000003 0xf4fe7ff9f8000000

def z1302 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xaffff3807fff000f 0xfaffff3807fff000

def z1303 : W := mkw 0x4ffedffb5748eb1b 0x44ffedffb5748eb1 0xffffffffffd8ff3f 0xfffffffffffd8ff3

def z1304 : W := mkw 0x4ffedffb02080008 0x04ffedffb0208000 0x4fffffff8618000b 0xf4fffffff8618000

def z1305 : W := mkw 0x0020460900000000 0x0002046090000000 0x7067ee1f88000c07 0xd7067ee1f88000c0

def z1306 : W := mkw 0x4ffedffb02080118 0x44ffedffb0208011 0x4fffffff86000303 0xf4fffffff8600030

def z1307 : W := mkw 0x2ddfa0a26fbe011c 0x42ddfa0a26fbe011 0xafffe0607fff003d 0xfafffe0607fff003

def z1308 : W := mkw 0x4fded9fb00000000 0x04fded9fb0000000 0x4e1fe07f80000001 0x04e1fe07f8000000

def z1309 : W := mkw 0x06345e5900000000 0x006345e590000000 0x4e67ee1f80000003 0xd4e67ee1f8000000

def z1310 : W := mkw 0x4ffedffb00000000 0x04ffedffb0000000 0x0fffef9f80000001 0xf0fffef9f8000000

def z1311 : W := mkw 0x0b601f005540ea03 0x00b601f005540ea0 0xafe00f807fc07f0c 0xfafe00f807fc07f0

def z1312 : W := mkw 0x4ffedffb45000201 0x04ffedffb4500020 0x4fffffff86000303 0xf4fffffff8600030

def z1313 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xd067ee1f81e77cc3 0x4d067ee1f81e77cc

def z1314 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0xaffce0007fff000d 0xfaffce0007fff000

def z1315 : W := mkw 0x4ddec1fb00000000 0x04ddec1fb0000000 0x419fe1ff80000001 0x0419fe1ff8000000

def z1316 : W := mkw 0x100120048aeb3ddc 0x6100120048aeb3dd 0xb00000000fe77fc4 0x0b00000000fe77fc

def z1317 : W := mkw 0x4ffedffb45402800 0x04ffedffb4540280 0xffffffffffc07c0f 0xfffffffffffc07c0

def z1318 : W := mkw 0x2d54a000679e000c 0x02d54a000679e000 0x8e64e00077df0008 0x48e64e00077df000

def z1319 : W := mkw 0x12205e0d9041fcc2 0x212205e0d9041fcc 0x50001e1f8000fcc2 0x050001e1f8000fcc

def z1320 : W := mkw 0x12205f5d9041fee3 0xa12205f5d9041fee 0x50001fff8000fff2 0x050001fff8000fff

def z1321 : W := mkw 0x002046095540ea03 0x0002046095540ea0 0xf067ee1fffc0ff0f 0xdf067ee1fffc0ff0

def z1322 : W := mkw 0x008a40ab00000000 0x0008a40ab0000000 0x401fe07f80000001 0x0401fe07f8000000

def z1323 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xbffff0007fff800f 0xfbffff0007fff800

def z1324 : W := mkw 0x469ed8fb00000000 0x0469ed8fb0000000 0x4f9fffff80000003 0xf4f9fffff8000000

def z1325 : W := mkw 0x4ffedffb7554ea23 0x84ffedffb7554ea2 0xffffffffffd8ff3f 0xfffffffffffd8ff3

def z1326 : W := mkw 0x4beadffb5540ea03 0x04beadffb5540ea0 0xffe3ffffffc0ff0e 0xfffe3ffffffc0ff0

def z1327 : W := mkw 0x4ffedffb02080118 0x44ffedffb0208011 0x4fffffff80180033 0xf4fffffff8018003

def z1328 : W := mkw 0x4dfec7fb45402a01 0x04dfec7fb45402a0 0x61ffe3ff8fc00f01 0x861ffe3ff8fc00f0

def z1329 : W := mkw 0x10012004bafffdfe 0xe10012004bafffdf 0xb00000007ffffffc 0x0b00000007ffffff

def z1330 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xde1c1ffc703fffff 0x7de1c1ffc703ffff

def z1331 : W := mkw 0x2ddfa000efbe044c 0x02ddfa000efbe044 0xfffff383ffff8fcf 0xffffff383ffff8fc

def z1332 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xf1e7ee1f8fe77ccf 0xff1e7ee1f8fe77cc

def z1333 : W := mkw 0x4dfec7fb00000000 0x04dfec7fb0000000 0x407fe07f80000001 0x0407fe07f8000000

def z1334 : W := mkw 0x1021660d8aeb3ddc 0x61021660d8aeb3dd 0xf067ee1f89ff7cf7 0xdf067ee1f89ff7cf

def z1335 : W := mkw 0x008b00a28a280558 0x4008b00a28a28055 0xf19b1fe38e38ffff 0xff19b1fe38e38fff

def z1336 : W := mkw 0x4dfec7fb00000000 0x04dfec7fb0000000 0x01e7e39f80000000 0x801e7e39f8000000

def z1337 : W := mkw 0x09412000cda20444 0x009412000cda2044 0xffe7f383ffe78fcf 0xfffe7f383ffe78fc

def z1338 : W := mkw 0x4ffedffb1040ea03 0x04ffedffb1040ea0 0xdffffffff000ff0f 0xfdffffffff000ff0

def z1339 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xffffe063ffff8ffd 0xfffffe063ffff8ff

def z1340 : W := mkw 0x0434460900000000 0x0043446090000000 0x4e7fee1f80000003 0xf4e7fee1f8000000

def z1341 : W := mkw 0x46bedefb00000000 0x046bedefb0000000 0x4e7ffe7f80000003 0xf4e7ffe7f8000000

def z1342 : W := mkw 0x4ffedffb1000c002 0x04ffedffb1000c00 0xfffffffffe00ff0f 0xffffffffffe00ff0

def z1343 : W := mkw 0x2ddfa0a2efbe055c 0x42ddfa0a2efbe055 0xce7fe063f1ff00f1 0x4ce7fe063f1ff00f

def z1344 : W := mkw 0x1021660d88e33cc4 0x21021660d88e33cc 0xfe67ee1ff9e77ccf 0xffe67ee1ff9e77cc

def z1345 : W := mkw 0x449ec0fb02080118 0x4449ec0fb0208011 0x419ff1ff86188339 0x2419ff1ff8618833

def z1346 : W := mkw 0x2d54a00065960004 0x02d54a0006596000 0xae64e0007fc7000c 0x4ae64e0007fc7000

def z1347 : W := mkw 0x4ffedffb20140020 0x84ffedffb2014002 0x4fffffff80180033 0xf4fffffff8018003

def z1348 : W := mkw 0x4beadffb00000000 0x04beadffb0000000 0x4fe3ffff80000002 0xf4fe3ffff8000000

def z1349 : W := mkw 0x4beadfab5540ea03 0x04beadfab5540ea0 0xffe7ff9fffc0ff0f 0xfffe7ff9fffc0ff0

def z1350 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xce1c1c7c703ff0f9 0x6ce1c1c7c703ff0f

def z1351 : W := mkw 0x12215e5d9861fce2 0xa12215e5d9861fce 0x701b1e7f8838fcff 0xb701b1e7f8838fcf

def z1352 : W := mkw 0x2ddfa0006fbe000c 0x02ddfa0006fbe000 0xbfffe2007fff0c0f 0xfbfffe2007fff0c0

def z1353 : W := mkw 0x04152000a8b60444 0x004152000a8b6044 0xfe7ff263f9ff8cff 0xffe7ff263f9ff8cf

def z1354 : W := mkw 0x061418543015d0a2 0x8061418543015d0a 0xfe1c1e7c783ffcff 0xffe1c1e7c783ffcf

def z1355 : W := mkw 0x0000400900000000 0x0000040090000000 0x4067e01f80000001 0xd4067e01f8000000

def z1356 : W := mkw 0x0960470945402a01 0x00960470945402a0 0x21e3e3838fc00f00 0x821e3e3838fc00f0

def z1357 : W := mkw 0x4b605ffb00000000 0x04b605ffb0000000 0x4fe7ffff80000003 0xf4fe7ffff8000000

def z1358 : W := mkw 0x4ffedffb5500c203 0x04ffedffb5500c20 0xefffffffffc0830f 0xfefffffffffc0830

def z1359 : W := mkw 0x2ddfa0a26fbe011c 0x42ddfa0a26fbe011 0xafffe1807fff030d 0xfafffe1807fff030

def z1360 : W := mkw 0x06345e593014c022 0x806345e593014c02 0x4e7ffe7ff018803b 0xf4e7ffe7ff018803

def z1361 : W := mkw 0x0b605f095540ea03 0x00b605f095540ea0 0x8e64ec1c71c07000 0x48e64ec1c71c0700

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z7,z5,z8]),(1,[z1,z9,z2,z3,z4,z8]),(1,[z1,z2,z3,z4,z5,z10]),(0,[z11,z1,z2,z3,z4,z12,z5]),(0,[z1,z2,z3,z4,z5,z13,z8]),(1,[z11,z1,z2,z14,z4,z5]),(0,[z1,z2,z3,z15,z5,z16,z8])],[(0,[z1,z2,z3,z4,z17,z8,z18]),(0,[z1,z2,z3,z4,z19,z17,z8]),(0,[z1,z20,z2,z3,z4,z5,z18]),(0,[z1,z2,z21,z3,z15,z4,z5])],[(0,[z1,z2,z3,z4,z5,z17,z6]),(0,[z1,z2,z3,z4,z5,z22,z8]),(0,[z23,z1,z2,z3,z4,z24,z8]),(0,[z11,z1,z2,z3,z4,z5,z6]),(0,[z1,z25,z2,z3,z4,z5,z8])],[(0,[z1,z2,z26,z3,z4,z5,z6]),(1,[z2,z3,z4,z27,z17,z8]),(0,[z1,z2,z3,z28,z4,z5,z8]),(0,[z1,z2,z3,z29,z5,z16,z8]),(0,[z30,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z31]),(0,[z1,z2,z3,z32,z4,z5,z33]),(1,[z1,z2,z3,z4,z5,z34]),(1,[z35,z1,z2,z3,z36,z8]),(0,[z1,z2,z3,z37,z15,z4,z5])],[(0,[z1,z38,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z39,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z40,z5]),(0,[z1,z2,z3,z4,z5,z41,z8]),(0,[z1,z42,z2,z3,z4,z43,z8]),(0,[z1,z3,z4,z5,z44,z8,z18])],[(0,[z45,z1,z2,z3,z4,z5,z8]),(0,[z46,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z47,z5,z8]),(0,[z1,z48,z2,z3,z4,z5,z8])],[(0,[z49,z1,z2,z3,z4,z5,z8]),(0,[z50,z1,z2,z3,z4,z5,z8]),(0,[z1,z51,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z52,z4,z5,z6]),(0,[z1,z53,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z18]),(0,[z54,z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z15,z15,z4,z5])]],
   [[(0,[z1,z38,z3,z52,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z55]),(0,[z1,z2,z3,z4,z40,z56,z8]),(0,[z57,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z33,z58]),(0,[z1,z2,z59,z3,z4,z5,z33]),(0,[z1,z42,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z56,z5,z36,z8]),(0,[z1,z2,z3,z4,z5,z60,z36])],[(0,[z61,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z40,z62,z8])],[(1,[z1,z2,z3,z63,z5,z8]),(0,[z1,z2,z3,z4,z12,z40,z8]),(0,[z1,z2,z3,z4,z5,z64,z8])],[(0,[z65,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z66,z5,z8]),(0,[z1,z2,z3,z4,z67,z5,z8]),(0,[z68,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z69,z8]),(0,[z1,z2,z3,z4,z5,z70,z8]),(0,[z1,z2,z3,z4,z5,z8,z71]),(0,[z1,z72,z2,z3,z4,z5,z8])],[(0,[z73,z1,z2,z3,z4,z74,z8]),(0,[z75,z1,z2,z3,z4,z5,z8]),(0,[z35,z1,z2,z3,z4,z17,z8]),(1,[z1,z2,z3,z4,z5,z76]),(1,[z1,z77,z2,z4,z78,z8]),(0,[z1,z2,z3,z79,z4,z5,z8]),(0,[z80,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z81,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z82,z8])],[(0,[z1,z20,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z83,z4,z5,z8]),(0,[z1,z2,z3,z84,z4,z5,z8]),(0,[z85,z1,z2,z3,z4,z5,z8]),(0,[z1,z86,z2,z3,z4,z5,z33]),(0,[z35,z1,z86,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z36,z33]),(0,[z1,z2,z3,z4,z87,z5,z8])],[(0,[z1,z2,z3,z4,z40,z36,z8]),(0,[z1,z2,z3,z4,z5,z8,z88]),(1,[z1,z89,z52,z4,z5,z8]),(0,[z11,z1,z2,z3,z15,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z17,z90,z8]),(1,[z1,z2,z3,z4,z5,z91]),(0,[z1,z2,z21,z3,z4,z78,z8]),(0,[z92,z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z15,z4,z5,z93])],[(0,[z94,z1,z2,z3,z4,z5,z8]),(0,[z95,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z58,z8]),(0,[z1,z2,z3,z96,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z97,z6]),(0,[z1,z2,z3,z5,z16,z8,z98]),(0,[z1,z2,z3,z15,z4,z4,z5]),(0,[z1,z2,z3,z15,z4,z19,z5])],[(0,[z1,z2,z3,z4,z5,z8,z99]),(0,[z1,z2,z21,z3,z4,z5,z100]),(0,[z1,z2,z3,z101,z4,z5,z6])],[(0,[z1,z2,z3,z84,z4,z40,z8]),(0,[z1,z89,z2,z59,z4,z5,z8]),(0,[z102,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z16,z8]),(0,[z1,z2,z3,z103,z15,z4,z5]),(1,[z1,z2,z3,z15,z5,z16])],[(0,[z0,z1,z2,z3,z104,z5,z8]),(0,[z105,z1,z2,z3,z4,z5,z8]),(0,[z106,z23,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z107,z8]),(0,[z1,z2,z3,z108,z4,z5,z8])],[(0,[z1,z2,z109,z3,z4,z5,z8]),(0,[z1,z110,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z111,z5,z8]),(0,[z112,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z113,z5]),(0,[z1,z77,z2,z21,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z3,z4,z5,z33])],[(0,[z0,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z114,z3,z4,z5,z8]),(0,[z95,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z58,z8]),(0,[z115,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z116,z5]),(0,[z1,z2,z3,z4,z5,z8,z117]),(0,[z1,z2,z118,z3,z4,z5,z8]),(0,[z1,z119,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z120]),(1,[z1,z86,z3,z4,z113,z8]),(0,[z1,z2,z3,z4,z5,z44,z6]),(0,[z1,z121,z2,z3,z4,z5,z8]),(0,[z122,z1,z2,z3,z15,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z123,z5,z8]),(0,[z1,z2,z3,z124,z4,z5,z8]),(0,[z1,z2,z3,z4,z125,z5,z8]),(1,[z1,z2,z21,z4,z90,z8]),(0,[z1,z126,z2,z3,z4,z5,z8]),(0,[z35,z1,z2,z3,z127,z5,z8])],[(0,[z128,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z17,z8]),(1,[z1,z2,z3,z4,z129,z8]),(0,[z1,z2,z21,z3,z4,z90,z8]),(1,[z1,z2,z3,z4,z5,z130]),(0,[z11,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z131]),(1,[z1,z2,z3,z4,z40,z33]),(0,[z1,z2,z3,z132,z4,z5,z8]),(0,[z133,z1,z2,z3,z4,z5,z8]),(0,[z134,z1,z2,z3,z4,z5,z8])],[(0,[z0,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z135,z52,z4,z5,z8]),(0,[z136,z1,z2,z3,z4,z5,z33]),(0,[z1,z137,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z8,z138]),(0,[z1,z2,z3,z139,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z140,z8])],[(1,[z1,z2,z3,z4,z141,z8]),(0,[z1,z2,z3,z4,z5,z33,z142]),(0,[z1,z2,z3,z4,z5,z33,z33])],[(0,[z61,z1,z143,z3,z4,z5,z8]),(0,[z1,z86,z2,z3,z4,z113,z8]),(0,[z11,z1,z2,z14,z4,z5,z8])],[(0,[z11,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z59,z3,z15,z4,z5])],[(0,[z61,z1,z2,z3,z15,z4,z5]),(1,[z1,z2,z3,z4,z5,z144]),(0,[z1,z2,z26,z3,z4,z40,z8]),(0,[z1,z2,z145,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z12,z17,z8]),(0,[z1,z146,z2,z3,z4,z5,z8]),(0,[z1,z147,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z148,z4,z5]),(0,[z35,z1,z2,z3,z4,z5,z33]),(0,[z11,z1,z2,z3,z4,z5,z98])]],
   [[(0,[z1,z149,z2,z3,z4,z5,z8]),(0,[z150,z11,z1,z2,z3,z4,z5]),(0,[z1,z42,z2,z3,z4,z5,z151]),(0,[z152,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z153,z5,z33])],[(0,[z1,z2,z3,z4,z5,z154,z8]),(0,[z1,z2,z3,z155,z4,z12,z5]),(0,[z1,z2,z3,z4,z5,z156,z6]),(0,[z1,z2,z3,z157,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z158]),(0,[z1,z159,z2,z3,z4,z5,z8]),(0,[z160,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z27,z5,z33]),(0,[z106,z11,z1,z2,z3,z4,z5])],[(0,[z161,z1,z2,z3,z4,z162,z8]),(0,[z1,z2,z3,z4,z163,z5,z8])],[(0,[z1,z2,z3,z4,z5,z58,z18]),(0,[z1,z2,z3,z164,z4,z5,z8]),(0,[z1,z2,z3,z4,z56,z5,z8])],[(0,[z1,z2,z3,z165,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z8,z166]),(0,[z54,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z167,z5,z8]),(0,[z1,z2,z3,z168,z4,z5,z8])],[(0,[z169,z1,z2,z3,z170,z5,z8]),(0,[z1,z2,z3,z4,z5,z33,z166]),(0,[z1,z2,z3,z4,z5,z8,z6])],[(0,[z169,z1,z2,z3,z15,z4,z5]),(1,[z1,z2,z3,z4,z171,z8]),(0,[z11,z1,z2,z3,z4,z5,z17]),(0,[z1,z2,z3,z4,z5,z172,z8]),(0,[z11,z1,z2,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z173,z5,z8]),(0,[z1,z2,z3,z4,z5,z97,z8]),(0,[z1,z2,z3,z4,z5,z60,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z8,z174]),(0,[z175,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z84,z4,z17,z8]),(0,[z1,z2,z3,z4,z17,z44,z8]),(0,[z1,z2,z3,z83,z4,z17,z8]),(0,[z150,z1,z2,z3,z4,z5,z6]),(0,[z1,z3,z84,z4,z116,z5,z8]),(0,[z1,z86,z3,z4,z113,z5,z8]),(0,[z1,z2,z3,z4,z176,z5,z8]),(0,[z1,z2,z3,z4,z5,z177,z33]),(0,[z11,z1,z2,z81,z3,z4,z5]),(0,[z178,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z5,z179,z8]),(0,[z1,z2,z3,z101,z4,z5,z8])],[(0,[z23,z1,z2,z3,z4,z5,z6]),(0,[z180,z1,z2,z3,z4,z5,z8]),(0,[z1,z77,z2,z3,z4,z5,z6]),(0,[z35,z1,z77,z2,z3,z4,z8]),(0,[z1,z2,z181,z3,z15,z4,z5])],[(1,[z1,z2,z3,z170,z5,z8]),(0,[z1,z2,z3,z182,z4,z5,z8]),(1,[z1,z2,z3,z4,z183,z8]),(0,[z1,z2,z184,z3,z4,z5,z8]),(0,[z1,z2,z3,z185,z4,z5,z8]),(0,[z106,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z186,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z13]),(0,[z1,z2,z3,z4,z187,z5,z8]),(0,[z1,z2,z3,z188,z15,z4,z5])],[(0,[z1,z189,z2,z3,z4,z5,z8]),(0,[z95,z1,z2,z3,z4,z17,z8]),(0,[z1,z190,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z191,z8]),(0,[z1,z2,z3,z192,z4,z5,z8]),(0,[z35,z1,z2,z21,z3,z4,z8]),(1,[z1,z2,z3,z15,z4,z5]),(0,[z1,z193,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z40,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z194])],[(0,[z1,z2,z3,z4,z5,z8,z195]),(0,[z2,z3,z29,z4,z27,z5,z8]),(0,[z1,z2,z3,z84,z27,z5,z8]),(0,[z1,z2,z3,z27,z12,z5,z8]),(1,[z1,z2,z3,z196,z4,z5]),(0,[z1,z2,z3,z197,z4,z40,z8]),(0,[z1,z2,z3,z101,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z8,z198]),(0,[z1,z2,z3,z4,z5,z44,z8]),(0,[z1,z2,z3,z199,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z200,z8])],[(0,[z201,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z189,z3,z4,z5,z8]),(0,[z202,z161,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z116,z5,z8]),(0,[z1,z2,z3,z203,z4,z5,z8]),(0,[z1,z204,z2,z3,z4,z5,z8]),(0,[z1,z205,z2,z3,z4,z5,z8]),(0,[z206,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z14,z3,z4,z5,z8])],[(0,[z207,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z17,z33]),(0,[z1,z2,z3,z4,z5,z6,z166]),(0,[z1,z2,z21,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z208,z5,z8]),(0,[z209,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z210,z4,z5,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z135,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z22,z8]),(0,[z1,z211,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z56,z5])],[(0,[z1,z2,z3,z4,z5,z212,z8]),(0,[z213,z1,z2,z3,z4,z5,z8]),(0,[z136,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z12,z5,z33]),(0,[z1,z2,z3,z4,z5,z214,z8]),(0,[z1,z215,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z141,z8]),(1,[z0,z2,z135,z4,z5,z8]),(0,[z1,z2,z3,z4,z123,z17,z8]),(0,[z216,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z217])],[(0,[z11,z1,z2,z3,z4,z17,z8]),(0,[z218,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z116,z40,z8]),(0,[z1,z190,z2,z52,z4,z5,z8]),(0,[z1,z2,z3,z4,z219,z5,z8]),(0,[z1,z2,z3,z4,z5,z220,z8]),(0,[z1,z2,z3,z4,z5,z221,z8]),(0,[z1,z2,z3,z4,z222,z5,z8]),(0,[z1,z2,z3,z4,z5,z223,z8])],[(1,[z1,z2,z3,z224,z4,z5])],[(0,[z1,z225,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z226,z4,z5,z8]),(0,[z227,z1,z2,z3,z4,z5,z8]),(0,[z228,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z229]),(0,[z1,z2,z230,z3,z4,z5,z8]),(0,[z35,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z231])],[(0,[z73,z1,z2,z135,z4,z5,z8]),(1,[z23,z2,z3,z4,z5,z166]),(0,[z1,z20,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z232,z5,z8]),(0,[z1,z2,z3,z15,z127,z4,z5]),(0,[z1,z2,z3,z4,z19,z233,z8])],[(0,[z11,z1,z42,z2,z3,z4,z5]),(0,[z180,z1,z2,z3,z4,z5,z18]),(0,[z234,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z156,z8]),(0,[z1,z2,z3,z4,z5,z233,z6]),(0,[z1,z2,z3,z4,z5,z33,z235])]],
   [[(0,[z11,z1,z2,z143,z3,z4,z5]),(0,[z236,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z27,z5,z8])],[(0,[z1,z2,z26,z3,z4,z5,z55]),(0,[z1,z2,z3,z4,z17,z43,z8]),(0,[z1,z2,z3,z4,z5,z237,z8])],[(0,[z161,z2,z3,z4,z5,z17,z8]),(0,[z11,z1,z2,z3,z4,z238,z5]),(0,[z239,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z5,z240,z8])],[(0,[z1,z2,z3,z4,z5,z8,z241]),(0,[z1,z2,z3,z4,z5,z8,z242]),(0,[z1,z2,z3,z4,z5,z33,z93]),(0,[z11,z1,z121,z2,z3,z4,z5])],[(0,[z161,z1,z2,z3,z4,z5,z243]),(0,[z11,z1,z2,z3,z29,z4,z5]),(0,[z1,z2,z3,z4,z5,z244,z8]),(0,[z1,z2,z3,z4,z5,z6,z245]),(0,[z1,z2,z3,z4,z5,z246,z8]),(0,[z247,z1,z2,z3,z4,z5,z33]),(0,[z11,z1,z248,z2,z3,z4,z5])],[(0,[z169,z1,z2,z3,z4,z5,z249]),(1,[z161,z2,z3,z29,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z250]),(1,[z11,z1,z2,z3,z4,z40]),(1,[z1,z2,z3,z4,z251,z8])],[(0,[z1,z2,z3,z4,z183,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z166]),(0,[z106,z1,z2,z3,z4,z111,z8]),(0,[z1,z2,z3,z4,z5,z43,z8]),(0,[z1,z2,z3,z4,z5,z252,z8]),(1,[z1,z20,z3,z4,z5,z18]),(1,[z1,z2,z3,z4,z5,z253]),(0,[z11,z11,z1,z2,z3,z4,z5])],[(0,[z254,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z255,z4,z5,z8]),(0,[z23,z1,z2,z3,z4,z5,z8]),(0,[z1,z42,z2,z3,z4,z5,z191]),(0,[z256,z1,z2,z3,z4,z5,z8]),(0,[z1,z77,z2,z3,z4,z5,z8])]],
   [[(0,[z257,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z258,z40,z8]),(0,[z1,z2,z3,z4,z40,z16,z8]),(0,[z106,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z259,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z84,z4,z5]),(0,[z1,z2,z3,z260,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z249]),(0,[z1,z2,z3,z4,z261,z5,z8]),(0,[z1,z262,z2,z3,z4,z5,z8]),(0,[z263,z1,z2,z3,z4,z5,z8]),(0,[z1,z190,z2,z3,z15,z4,z5]),(0,[z264,z1,z2,z3,z4,z5,z8]),(0,[z1,z265,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z266,z5,z8])],[(0,[z161,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z101,z4,z17,z8]),(0,[z23,z2,z3,z4,z5,z8,z166]),(0,[z1,z2,z3,z4,z5,z90,z6]),(0,[z11,z267,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z98]),(0,[z1,z2,z3,z4,z268,z5,z8])],[(0,[z150,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z269,z8]),(0,[z1,z2,z3,z4,z5,z58,z6]),(0,[z1,z2,z3,z4,z270,z5,z8]),(1,[z1,z2,z3,z4,z5,z151])],[(0,[z23,z1,z2,z3,z4,z40,z8]),(0,[z1,z77,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z271,z5,z8]),(0,[z1,z272,z2,z3,z4,z5,z8]),(0,[z1,z42,z2,z3,z4,z113,z8]),(0,[z1,z2,z3,z4,z251,z12,z8]),(0,[z1,z2,z3,z273,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z90]),(0,[z206,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z93])],[(0,[z1,z274,z2,z3,z4,z5,z8]),(0,[z275,z1,z2,z3,z4,z5,z8]),(0,[z106,z1,z2,z3,z4,z40,z8]),(0,[z1,z89,z2,z3,z4,z5,z138]),(0,[z1,z276,z2,z3,z4,z5,z8]),(0,[z1,z2,z4,z78,z5,z90,z8]),(0,[z209,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z277,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z278,z5,z8]),(0,[z1,z2,z26,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z17,z279,z8]),(0,[z2,z3,z4,z40,z5,z17,z8]),(0,[z1,z2,z3,z4,z261,z40,z8]),(1,[z1,z2,z3,z4,z5,z280]),(0,[z281,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z113,z5,z8]),(0,[z209,z1,z2,z282,z4,z5,z8]),(0,[z1,z283,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z284])],[(1,[z1,z2,z285,z3,z4,z5]),(0,[z1,z42,z3,z4,z5,z43,z8]),(0,[z1,z2,z3,z4,z5,z286,z33]),(0,[z35,z48,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z287])]],
   [[(0,[z288,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z116,z17,z8]),(0,[z1,z2,z3,z4,z17,z233,z8])],[(0,[z169,z1,z2,z3,z63,z5,z8]),(0,[z0,z1,z2,z3,z4,z141,z8]),(0,[z1,z2,z3,z52,z4,z5,z33]),(0,[z11,z1,z20,z2,z3,z4,z5])],[(0,[z209,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z289,z5,z8]),(0,[z290,z1,z2,z3,z32,z5,z8])],[(0,[z1,z2,z3,z4,z278,z40,z8]),(0,[z1,z2,z3,z4,z5,z8,z100]),(0,[z1,z291,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z292,z5,z8]),(0,[z1,z293,z2,z3,z15,z4,z5])],[(0,[z1,z2,z3,z294,z4,z5,z8]),(0,[z11,z1,z2,z26,z3,z4,z5]),(0,[z209,z1,z2,z4,z5,z33,z8]),(0,[z1,z2,z3,z127,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z33,z295])],[(0,[z218,z1,z2,z3,z4,z17,z8]),(1,[z1,z2,z3,z4,z296,z8]),(0,[z1,z2,z3,z4,z5,z10,z8]),(0,[z1,z149,z2,z3,z4,z5,z6]),(0,[z1,z2,z297,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z233,z8])],[(0,[z1,z2,z26,z52,z4,z5,z8]),(0,[z1,z59,z3,z52,z4,z5,z8]),(0,[z1,z298,z2,z3,z4,z5,z8]),(0,[z1,z299,z2,z3,z4,z5,z8]),(0,[z180,z11,z1,z2,z3,z4,z5]),(0,[z300,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z301,z5,z8]),(0,[z1,z302,z2,z3,z4,z5,z8]),(0,[z303,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z162,z8]),(0,[z1,z2,z282,z3,z32,z5,z8]),(1,[z304,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z305,z33]),(0,[z1,z2,z3,z306,z4,z5,z8])]],
   [[(0,[z61,z1,z38,z3,z4,z5,z8]),(0,[z1,z2,z3,z307,z4,z5,z8]),(0,[z202,z11,z1,z2,z3,z4,z5]),(0,[z1,z89,z2,z3,z4,z5,z6]),(0,[z308,z1,z2,z3,z4,z5,z8]),(0,[z309,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z310,z5,z8]),(0,[z1,z77,z2,z3,z4,z5,z311]),(0,[z312,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z78,z5])],[(0,[z1,z2,z285,z3,z4,z116,z5]),(0,[z1,z2,z313,z3,z4,z5,z8]),(0,[z314,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z56,z5,z6]),(0,[z315,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z243]),(0,[z1,z2,z3,z4,z5,z316,z8]),(0,[z1,z2,z3,z168,z4,z5,z6]),(0,[z247,z1,z2,z3,z15,z4,z5])],[(0,[z73,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z40,z8,z6]),(0,[z1,z2,z3,z4,z317,z5,z8]),(0,[z1,z2,z3,z224,z4,z116,z5]),(0,[z318,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z319,z8])],[(0,[z169,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z320,z8]),(0,[z1,z302,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z321,z116,z8]),(0,[z1,z2,z285,z3,z4,z5,z8]),(0,[z1,z77,z2,z4,z78,z5,z8])],[(0,[z1,z143,z3,z52,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z322]),(0,[z1,z2,z3,z4,z323,z5,z8]),(0,[z290,z1,z2,z3,z4,z5,z324]),(0,[z325,z1,z2,z3,z4,z5,z6])],[(0,[z326,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z224,z4,z5,z8]),(0,[z180,z1,z2,z3,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z327,z8]),(0,[z1,z2,z328,z3,z4,z5,z8]),(0,[z1,z2,z329,z3,z4,z5,z8]),(0,[z1,z330,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z187,z5,z6]),(0,[z1,z2,z3,z4,z19,z5,z33]),(0,[z1,z2,z3,z4,z56,z5,z194]),(0,[z331,z1,z2,z3,z15,z4,z5])]],
   [[(0,[z1,z332,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z333,z5,z8]),(0,[z161,z1,z2,z3,z15,z4,z5]),(0,[z150,z1,z2,z3,z4,z17,z8]),(0,[z202,z1,z2,z3,z4,z5,z6]),(0,[z334,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z90,z8]),(0,[z1,z335,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z336,z4,z5,z8])],[(0,[z23,z1,z2,z3,z4,z17,z8]),(0,[z1,z77,z2,z3,z4,z17,z8]),(0,[z94,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z40,z5,z6]),(0,[z1,z89,z190,z3,z4,z5,z8]),(0,[z1,z2,z282,z3,z4,z5,z6]),(0,[z1,z2,z3,z337,z4,z5,z8]),(0,[z1,z338,z2,z3,z4,z5,z8])],[(0,[z1,z38,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z196,z4,z27,z5]),(0,[z1,z2,z3,z4,z5,z243,z8]),(0,[z106,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z339,z5,z8]),(0,[z1,z2,z3,z340,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z341,z8]),(0,[z1,z248,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z8,z55]),(1,[z11,z1,z2,z3,z4,z17]),(0,[z1,z2,z3,z4,z116,z5,z6]),(0,[z1,z2,z3,z4,z5,z233,z18]),(0,[z1,z2,z3,z15,z4,z342,z5])],[(0,[z1,z2,z3,z4,z343,z5,z8]),(0,[z1,z2,z3,z4,z344,z5,z8]),(0,[z1,z2,z26,z3,z15,z4,z5])],[(0,[z1,z2,z3,z135,z4,z5,z6]),(0,[z11,z95,z1,z2,z3,z4,z5]),(1,[z1,z42,z3,z4,z43,z8]),(0,[z1,z2,z3,z4,z345,z5,z8]),(0,[z346,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z347,z4,z5,z36])],[(0,[z1,z2,z3,z348,z4,z5,z8]),(0,[z1,z2,z349,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z350,z8]),(0,[z1,z2,z3,z4,z5,z351,z8]),(0,[z1,z2,z282,z32,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z352,z6])],[(0,[z209,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z52,z15,z4,z5]),(0,[z353,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z354,z3,z4,z5,z8]),(0,[z1,z2,z3,z355,z4,z5,z8]),(1,[z1,z2,z3,z101,z4,z93])]],
   [[(0,[z356,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z357,z4,z5,z8]),(0,[z1,z358,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z8,z359])],[(0,[z169,z1,z2,z3,z4,z5,z158]),(0,[z360,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z59,z3,z4,z5,z31]),(0,[z1,z2,z361,z3,z4,z5,z8])],[(0,[z1,z2,z3,z29,z116,z5,z8]),(0,[z362,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z191]),(1,[z180,z1,z3,z4,z5,z44]),(0,[z1,z2,z3,z4,z5,z8,z363])],[(0,[z364,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z59,z3,z4,z5]),(0,[z1,z2,z3,z4,z365,z5,z8]),(0,[z1,z20,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z8,z91])],[(0,[z366,z1,z2,z3,z4,z5,z8]),(0,[z1,z367,z2,z3,z4,z5,z8]),(0,[z1,z2,z368,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z5,z44]),(0,[z304,z1,z2,z3,z4,z5,z8]),(0,[z254,z11,z1,z2,z3,z4,z5]),(0,[z256,z11,z1,z2,z3,z4,z5])],[(1,[z1,z2,z3,z4,z369,z8]),(0,[z370,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z33,z8]),(0,[z1,z2,z3,z4,z5,z371,z8]),(0,[z1,z2,z372,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z4,z5])],[(0,[z1,z2,z59,z135,z4,z5,z8]),(0,[z1,z373,z2,z3,z4,z27,z5]),(0,[z1,z89,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z374,z4,z5,z8])],[(0,[z375,z1,z2,z3,z4,z5,z8]),(0,[z161,z1,z2,z3,z29,z5,z8]),(0,[z376,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z377]),(0,[z1,z2,z3,z4,z5,z378,z8]),(0,[z1,z2,z3,z4,z5,z379,z8]),(0,[z1,z2,z3,z4,z5,z130,z8]),(0,[z1,z2,z3,z15,z4,z5,z233])]],
   [[(0,[z380,z1,z2,z3,z4,z5,z8]),(0,[z169,z1,z143,z3,z4,z5,z8]),(0,[z1,z149,z2,z3,z4,z40,z8]),(0,[z1,z381,z2,z3,z4,z5,z8]),(0,[z1,z382,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z383])],[(0,[z384,z1,z2,z3,z4,z5,z8]),(0,[z73,z1,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z26,z4,z5,z8]),(0,[z1,z2,z3,z385,z4,z5,z8]),(1,[z95,z2,z3,z4,z17,z8]),(0,[z1,z190,z2,z59,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z386])],[(0,[z387,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z24,z8]),(0,[z150,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z8,z388]),(0,[z290,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z12,z5]),(0,[z209,z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z389,z4,z5,z8]),(0,[z390,z1,z2,z3,z4,z5,z8])],[(0,[z1,z89,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z43,z6]),(0,[z1,z2,z3,z391,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z392,z8]),(0,[z325,z1,z2,z3,z4,z5,z8]),(2,[z1,z2,z210,z4,z5])],[(0,[z136,z161,z2,z3,z4,z5,z8]),(0,[z393,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z32,z29,z5,z8]),(0,[z150,z1,z3,z4,z116,z5,z8]),(1,[z1,z2,z3,z4,z321,z8]),(0,[z1,z2,z3,z4,z394,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z6]),(0,[z1,z2,z3,z4,z233,z8,z93])],[(0,[z1,z2,z143,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z17,z8,z166]),(0,[z150,z1,z2,z3,z84,z5,z8]),(0,[z1,z2,z3,z4,z395,z5,z8]),(0,[z1,z2,z3,z127,z56,z5,z8])],[(1,[z1,z2,z3,z343,z5,z8]),(0,[z73,z1,z2,z3,z4,z40,z8]),(0,[z202,z1,z2,z3,z4,z5,z8]),(0,[z1,z89,z2,z3,z4,z5,z154])],[(0,[z1,z2,z3,z4,z369,z5,z8]),(0,[z1,z2,z3,z4,z5,z396,z8]),(0,[z202,z2,z3,z4,z27,z5,z8]),(0,[z290,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z40,z8,z98]),(0,[z1,z2,z282,z3,z4,z5,z8])]],
   [[(0,[z1,z38,z2,z3,z15,z4,z5]),(1,[z1,z2,z3,z4,z397,z8])],[(1,[z1,z2,z3,z4,z5,z398]),(0,[z1,z2,z3,z4,z5,z8,z399]),(0,[z1,z2,z400,z3,z4,z5,z8]),(0,[z180,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z401,z5,z8]),(0,[z1,z149,z3,z84,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z402,z8]),(0,[z1,z2,z403,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z60])],[(0,[z404,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z129,z8]),(0,[z1,z2,z21,z4,z5,z90,z8]),(0,[z405,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z406])],[(0,[z169,z2,z143,z3,z4,z5,z8]),(0,[z202,z1,z2,z3,z4,z40,z8]),(0,[z407,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z113,z5,z6])],[(0,[z408,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z409,z8]),(0,[z11,z161,z1,z2,z3,z4,z5]),(0,[z1,z2,z410,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z339,z17,z8]),(0,[z411,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z40,z8]),(0,[z1,z2,z282,z3,z4,z40,z8]),(0,[z11,z1,z2,z3,z4,z5,z58]),(0,[z1,z2,z3,z4,z412,z5,z8]),(0,[z180,z1,z2,z3,z4,z5,z44]),(0,[z1,z2,z3,z4,z5,z352,z8])],[(0,[z1,z2,z3,z4,z5,z413,z8]),(0,[z1,z2,z32,z4,z12,z5,z8])],[(0,[z136,z1,z2,z3,z4,z397,z8]),(0,[z1,z2,z3,z414,z4,z5,z8]),(0,[z1,z2,z3,z127,z4,z56,z8]),(0,[z1,z2,z3,z4,z415,z5,z8]),(0,[z1,z2,z3,z4,z19,z5,z93])],[(0,[z11,z1,z2,z3,z135,z4,z5]),(0,[z1,z2,z3,z4,z40,z8,z18]),(0,[z416,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z170,z4,z5,z8]),(0,[z1,z2,z3,z135,z4,z40,z8]),(0,[z1,z2,z417,z3,z4,z5,z8]),(0,[z95,z2,z3,z4,z5,z17,z8]),(0,[z1,z2,z3,z4,z5,z418,z8]),(0,[z419,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z78,z5,z8]),(0,[z1,z2,z3,z420,z4,z5,z8]),(0,[z1,z2,z421,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z422,z5,z8])],[(0,[z1,z2,z3,z423,z4,z5,z8]),(0,[z1,z424,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z425,z8]),(0,[z11,z1,z2,z3,z4,z5,z43]),(0,[z426,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z386]),(0,[z1,z2,z3,z210,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z427,z8])],[(0,[z1,z2,z3,z4,z5,z428,z8])],[(0,[z1,z429,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z18,z93]),(1,[z1,z2,z3,z155,z4,z5]),(0,[z1,z2,z3,z155,z4,z5,z8]),(0,[z1,z2,z3,z347,z4,z5,z8]),(0,[z1,z2,z3,z101,z4,z19,z8])],[(0,[z1,z430,z2,z3,z4,z5,z8]),(1,[z2,z3,z4,z40,z17,z8]),(0,[z1,z149,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z78,z40,z8]),(0,[z1,z2,z3,z84,z4,z5,z33]),(0,[z1,z2,z3,z127,z4,z36,z8])],[(0,[z1,z2,z3,z4,z431,z5,z8]),(0,[z1,z2,z3,z27,z5,z16,z8]),(0,[z1,z367,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z432,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z113,z5]),(0,[z1,z2,z3,z433,z4,z5,z8])],[(0,[z1,z2,z434,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z8,z88]),(0,[z1,z2,z3,z4,z435,z5,z8]),(0,[z1,z2,z436,z3,z4,z5,z8]),(0,[z1,z2,z437,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z116,z5]),(0,[z1,z2,z3,z37,z4,z5,z8]),(0,[z1,z2,z3,z4,z438,z5,z8]),(0,[z11,z1,z2,z3,z101,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z439,z8]),(0,[z95,z1,z2,z3,z4,z5,z33]),(0,[z1,z89,z2,z3,z4,z17,z8]),(0,[z150,z1,z2,z3,z15,z4,z5])],[(0,[z1,z2,z440,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z441,z5,z8]),(0,[z1,z2,z3,z4,z56,z17,z8]),(0,[z1,z2,z3,z442,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z18]),(1,[z102,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z443,z8]),(0,[z1,z2,z3,z4,z5,z444,z8]),(0,[z445,z1,z2,z3,z4,z5,z8])],[(0,[z1,z190,z143,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z8,z93]),(0,[z106,z1,z2,z3,z15,z4,z5]),(0,[z446,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z5,z8]),(0,[z1,z447,z2,z3,z4,z5,z8])],[(0,[z1,z2,z143,z3,z4,z5,z8]),(0,[z73,z1,z2,z3,z4,z17,z8]),(0,[z136,z1,z2,z3,z29,z5,z8]),(0,[z1,z89,z3,z52,z4,z5,z8]),(0,[z1,z2,z59,z3,z4,z5,z6]),(0,[z1,z42,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z448,z8]),(0,[z1,z2,z3,z4,z5,z449,z8]),(0,[z1,z2,z3,z4,z450,z5,z8]),(1,[z1,z2,z3,z210,z4,z5])],[(0,[z61,z1,z2,z3,z4,z5,z6]),(0,[z290,z1,z2,z3,z4,z17,z8]),(0,[z451,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z452,z8])],[(0,[z0,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z29,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z90,z8]),(0,[z1,z2,z3,z4,z5,z76,z8]),(1,[z150,z1,z3,z116,z5,z8]),(0,[z453,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z454,z8]),(0,[z1,z2,z3,z4,z455,z5,z8]),(1,[z11,z1,z2,z3,z5,z98])],[(0,[z1,z2,z3,z456,z4,z5,z8]),(0,[z180,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z40,z58,z8]),(0,[z457,z1,z2,z3,z4,z5,z8])],[(0,[z1,z458,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z459,z5,z8]),(0,[z1,z2,z3,z15,z4,z40,z8]),(0,[z1,z2,z3,z460,z4,z5,z8]),(0,[z461,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z93])]],
   [[(0,[z1,z2,z143,z3,z4,z40,z8]),(0,[z462,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z463,z4,z5,z8]),(0,[z1,z2,z3,z464,z4,z5,z8]),(0,[z202,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z17,z33]),(0,[z11,z23,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z44,z58]),(1,[z1,z2,z313,z3,z4,z8]),(0,[z11,z1,z2,z3,z32,z4,z5]),(0,[z465,z1,z2,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z5,z33])],[(0,[z1,z466,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z17,z8]),(0,[z1,z2,z282,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z467,z8]),(0,[z1,z86,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z468,z4,z5,z8]),(0,[z366,z11,z1,z2,z3,z4,z5]),(0,[z304,z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z469,z8]),(0,[z1,z2,z3,z4,z470,z5,z8])],[(0,[z1,z2,z3,z471,z4,z5,z8]),(1,[z61,z38,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z472,z5,z8]),(1,[z1,z2,z3,z4,z333,z8]),(0,[z1,z9,z2,z3,z4,z116,z8]),(0,[z1,z2,z3,z4,z5,z473,z8]),(0,[z1,z2,z3,z4,z19,z5,z233])],[(0,[z169,z1,z2,z294,z4,z5,z8]),(1,[z1,z373,z2,z3,z4,z5]),(0,[z1,z2,z474,z3,z4,z5,z8]),(0,[z209,z1,z2,z421,z4,z5,z8]),(0,[z35,z102,z2,z3,z4,z5,z8])],[(0,[z475,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z52,z4,z5]),(0,[z1,z2,z476,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z477,z8]),(0,[z1,z2,z3,z4,z5,z6,z99]),(0,[z35,z1,z2,z3,z4,z56,z8]),(0,[z1,z2,z3,z4,z5,z8,z478])],[(1,[z1,z479,z3,z4,z5,z8]),(0,[z1,z2,z3,z135,z4,z17,z8]),(1,[z1,z2,z3,z4,z74,z8]),(0,[z480,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z481,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z482,z5,z8])],[(1,[z1,z2,z483,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z279,z8]),(0,[z73,z2,z26,z3,z4,z5,z8]),(0,[z1,z2,z3,z103,z4,z5,z8]),(0,[z1,z2,z3,z4,z113,z40,z8]),(1,[z1,z2,z3,z484,z5,z8]),(0,[z1,z2,z485,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z486,z5,z8]),(0,[z1,z2,z3,z4,z487,z5,z8]),(0,[z488,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z421,z3,z4,z5,z8])],[(1,[z1,z2,z294,z4,z5,z8]),(0,[z0,z1,z2,z3,z4,z5,z144]),(0,[z1,z149,z2,z3,z4,z5,z33]),(0,[z290,z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z4,z12,z5,z8,z6]),(0,[z1,z77,z2,z3,z4,z78,z8])]],
   [[(0,[z136,z1,z2,z3,z4,z333,z8]),(0,[z1,z2,z3,z15,z4,z5,z17]),(0,[z1,z2,z3,z15,z4,z5,z18]),(0,[z1,z2,z3,z3,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z5,z16]),(0,[z1,z2,z489,z3,z4,z5,z8])],[(0,[z1,z490,z2,z3,z4,z5,z8]),(0,[z1,z491,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z492,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z493]),(1,[z1,z2,z3,z4,z5,z324]),(0,[z494,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z495,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z253]),(0,[z1,z2,z3,z4,z5,z6,z120]),(0,[z1,z2,z3,z496,z4,z5,z8]),(0,[z160,z1,z2,z3,z4,z5,z33])],[(0,[z1,z2,z3,z4,z78,z17,z8]),(0,[z1,z149,z2,z3,z84,z5,z8]),(0,[z1,z2,z3,z4,z5,z497,z8]),(0,[z122,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z5,z498])],[(0,[z1,z2,z421,z3,z4,z40,z8]),(0,[z1,z499,z2,z3,z4,z5,z8]),(0,[z35,z1,z42,z2,z3,z4,z8]),(0,[z1,z500,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z56,z5,z33]),(0,[z35,z1,z2,z3,z4,z36,z8])],[(0,[z1,z2,z3,z4,z5,z8,z249]),(0,[z0,z2,z3,z135,z4,z5,z8]),(0,[z1,z2,z3,z4,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z27,z5])],[(0,[z1,z2,z3,z32,z4,z5,z8]),(0,[z1,z2,z3,z4,z501,z5,z8]),(0,[z1,z2,z3,z502,z4,z5,z8]),(0,[z503,z1,z2,z3,z4,z5,z8])],[(0,[z136,z1,z2,z3,z4,z5,z6]),(0,[z95,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z151]),(0,[z1,z2,z504,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z238,z5,z8])],[(0,[z0,z1,z2,z3,z4,z171,z8]),(0,[z1,z2,z3,z505,z4,z5,z8]),(0,[z1,z2,z3,z506,z4,z5,z8]),(0,[z1,z2,z507,z3,z4,z5,z8]),(0,[z290,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z251,z5,z8]),(0,[z1,z2,z3,z4,z5,z33,z6]),(0,[z1,z2,z3,z101,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z8,z508]),(0,[z1,z2,z3,z4,z56,z5,z130])]],
   [[(0,[z1,z190,z59,z3,z4,z5,z8]),(0,[z180,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z233,z44]),(0,[z1,z77,z2,z3,z4,z90,z8]),(0,[z1,z2,z3,z509,z4,z5,z8])],[(0,[z1,z2,z3,z27,z116,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z510]),(0,[z1,z2,z59,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z280]),(0,[z180,z1,z3,z4,z5,z44,z8]),(0,[z1,z2,z3,z15,z4,z56,z5])],[(0,[z61,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z36,z8]),(0,[z1,z2,z3,z32,z4,z40,z8]),(0,[z23,z1,z2,z3,z4,z5,z58]),(0,[z1,z89,z2,z52,z4,z5,z8])],[(0,[z169,z1,z38,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z511,z5,z8]),(0,[z1,z2,z3,z4,z40,z5,z33]),(0,[z106,z1,z2,z3,z4,z5,z58])],[(0,[z1,z2,z512,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z513]),(0,[z1,z2,z3,z15,z4,z17,z8]),(0,[z1,z2,z3,z505,z4,z40,z8]),(0,[z11,z1,z2,z3,z4,z40,z5]),(0,[z1,z514,z2,z3,z4,z5,z8]),(0,[z1,z515,z2,z3,z4,z5,z8])],[(0,[z1,z2,z143,z3,z4,z17,z8]),(0,[z1,z516,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z44,z8]),(1,[z1,z2,z3,z15,z4,z40]),(0,[z1,z2,z3,z4,z116,z5,z33]),(0,[z11,z1,z149,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z517,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z518]),(0,[z1,z2,z282,z3,z12,z5,z8])],[(0,[z0,z1,z2,z3,z4,z5,z398]),(0,[z1,z2,z59,z3,z4,z40,z8]),(0,[z465,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z15,z4,z5])],[(0,[z1,z2,z519,z3,z4,z5,z8]),(0,[z61,z1,z2,z3,z4,z40,z8]),(0,[z11,z61,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z135,z4,z5,z33]),(0,[z1,z2,z520,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z521]),(0,[z1,z86,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z36,z8])]],
   [[(0,[z1,z2,z3,z4,z5,z144,z8]),(0,[z0,z1,z2,z135,z4,z5,z8]),(0,[z522,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z484,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z6,z6]),(0,[z1,z215,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z214,z33])],[(0,[z38,z2,z143,z3,z4,z5,z8]),(0,[z1,z2,z523,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z524,z5,z8]),(0,[z1,z2,z3,z4,z525,z5,z8]),(0,[z1,z2,z3,z526,z4,z5,z8]),(0,[z1,z527,z2,z3,z4,z5,z33])],[(0,[z1,z2,z528,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z529]),(1,[z11,z1,z2,z3,z15,z5])],[(0,[z1,z2,z3,z4,z5,z74,z8]),(0,[z1,z2,z3,z4,z113,z17,z8]),(0,[z1,z2,z3,z4,z5,z530,z8])],[(0,[z169,z1,z2,z3,z4,z369,z8]),(0,[z1,z2,z479,z3,z4,z5,z8]),(0,[z1,z86,z2,z3,z4,z40,z8]),(0,[z106,z2,z3,z4,z5,z58,z8]),(0,[z531,z1,z2,z3,z4,z5,z8]),(0,[z209,z1,z2,z4,z12,z5,z8]),(0,[z11,z1,z2,z3,z4,z78,z5]),(0,[z1,z2,z3,z4,z5,z8,z532]),(0,[z1,z2,z181,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z533])],[(0,[z1,z2,z3,z15,z29,z4,z5]),(0,[z1,z2,z534,z3,z4,z5,z8]),(0,[z1,z149,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z188,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z324,z8]),(0,[z535,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z78,z5,z6])],[(1,[z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z3,z4,z5,z8]),(0,[z1,z536,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z537,z4,z5,z8]),(0,[z161,z2,z3,z29,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z350,z8]),(0,[z1,z2,z3,z4,z5,z296,z8]),(0,[z1,z2,z3,z15,z4,z5,z36])],[(0,[z61,z1,z2,z3,z4,z70,z8]),(0,[z1,z538,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z148,z4,z12,z5]),(1,[z1,z2,z3,z127,z56,z8]),(0,[z11,z1,z2,z3,z4,z5,z93])]],
   [[(0,[z11,z73,z1,z2,z3,z4,z5]),(0,[z1,z2,z421,z3,z4,z17,z8]),(1,[z1,z2,z3,z317,z5,z8]),(0,[z11,z1,z2,z3,z4,z19,z5])],[(0,[z539,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z540,z8]),(0,[z1,z541,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z18,z166]),(0,[z1,z2,z542,z3,z4,z5,z8]),(0,[z1,z2,z21,z3,z4,z5,z6]),(1,[z1,z2,z14,z4,z5,z8])],[(1,[z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z8,z543])],[(0,[z136,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z37,z4,z5,z6])],[(0,[z136,z2,z3,z4,z27,z5,z8]),(0,[z1,z2,z3,z4,z5,z43,z33]),(0,[z1,z2,z3,z4,z5,z33,z8]),(0,[z1,z2,z3,z101,z15,z4,z5]),(0,[z1,z2,z3,z4,z5,z8,z544])],[(0,[z1,z2,z3,z4,z545,z5,z8]),(0,[z1,z2,z3,z4,z40,z43,z8]),(0,[z23,z1,z2,z3,z4,z5,z33]),(0,[z180,z1,z2,z3,z15,z4,z5]),(0,[z290,z1,z2,z282,z4,z5,z8]),(0,[z1,z77,z2,z3,z4,z5,z33]),(1,[z209,z1,z2,z4,z5,z33])],[(0,[z1,z2,z3,z4,z5,z8,z546]),(0,[z1,z547,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z32,z4,z17,z8]),(0,[z106,z1,z2,z3,z4,z5,z33]),(0,[z247,z11,z1,z2,z3,z4,z5])]],
   [[(0,[z202,z1,z2,z3,z15,z4,z5]),(0,[z1,z42,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z548,z4,z5,z8]),(0,[z35,z1,z2,z3,z4,z5,z8])],[(0,[z136,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z549,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z31]),(0,[z1,z2,z550,z3,z4,z5,z8]),(0,[z1,z20,z2,z3,z4,z5,z8]),(0,[z1,z2,z282,z3,z15,z4,z5]),(0,[z1,z2,z551,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z153,z5,z8])],[(0,[z1,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z552,z3,z4,z5,z8]),(0,[z553,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z29,z4,z5,z6]),(0,[z1,z2,z554,z3,z4,z5,z8]),(0,[z2,z3,z4,z5,z58,z8,z166]),(0,[z1,z2,z555,z3,z4,z5,z8]),(0,[z11,z1,z86,z2,z3,z4,z5]),(0,[z1,z2,z556,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z69,z8]),(1,[z1,z2,z3,z4,z70,z8]),(0,[z1,z2,z3,z4,z27,z5,z8]),(0,[z1,z2,z59,z3,z4,z17,z8]),(0,[z106,z1,z2,z3,z4,z129,z8]),(1,[z1,z149,z3,z84,z5,z8]),(0,[z180,z1,z20,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z33,z98]),(0,[z1,z2,z3,z15,z4,z482,z5])],[(0,[z1,z2,z3,z4,z5,z557,z8]),(0,[z61,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z558,z3,z4,z5,z8]),(0,[z1,z2,z3,z29,z84,z5,z8]),(0,[z1,z2,z3,z4,z17,z559,z8]),(0,[z1,z2,z3,z4,z560,z5,z8]),(0,[z209,z1,z2,z3,z4,z5,z33])],[(0,[z1,z190,z38,z3,z4,z5,z8]),(0,[z1,z2,z3,z135,z15,z4,z5]),(0,[z1,z2,z3,z4,z5,z561,z8]),(1,[z202,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z8,z166]),(0,[z1,z2,z3,z4,z113,z5,z33]),(0,[z1,z2,z3,z4,z5,z33,z44]),(0,[z239,z1,z2,z3,z4,z5,z8]),(1,[z206,z1,z2,z3,z4,z5])],[(0,[z562,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z101,z4,z5,z93])],[(0,[z1,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z563,z4,z5,z8]),(1,[z1,z2,z3,z4,z5,z311]),(0,[z247,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z473,z6]),(0,[z1,z2,z3,z4,z5,z564,z8])]],
   [[(0,[z11,z1,z38,z2,z3,z4,z5]),(1,[z136,z2,z3,z27,z5,z8]),(0,[z1,z2,z3,z4,z27,z40,z8]),(0,[z1,z77,z2,z3,z127,z4,z8]),(0,[z565,z1,z2,z3,z4,z5,z8]),(0,[z566,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z4,z5,z71]),(0,[z1,z86,z2,z3,z4,z17,z8]),(0,[z106,z1,z2,z3,z4,z5,z166]),(0,[z1,z2,z3,z4,z5,z177,z8]),(0,[z1,z2,z3,z15,z4,z567,z5])],[(0,[z0,z1,z479,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z568,z8]),(0,[z1,z2,z3,z4,z5,z569,z8]),(0,[z1,z570,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z15,z4,z17]),(0,[z1,z2,z3,z4,z571,z5,z8]),(0,[z1,z2,z3,z4,z5,z33,z18]),(0,[z1,z2,z3,z4,z5,z44,z93]),(0,[z1,z2,z3,z4,z5,z572,z8])],[(0,[z1,z2,z3,z4,z573,z5,z8]),(0,[z73,z1,z2,z26,z4,z5,z8]),(0,[z1,z190,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z574,z4,z5,z8]),(0,[z1,z2,z4,z5,z33,z8,z6]),(0,[z1,z2,z3,z4,z5,z6,z98]),(0,[z1,z2,z3,z4,z5,z233,z33]),(1,[z1,z2,z210,z4,z5,z8])],[(0,[z1,z2,z2,z3,z4,z5,z8]),(0,[z1,z575,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z576,z4,z5,z8]),(0,[z161,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z577,z8]),(0,[z1,z2,z3,z4,z40,z233,z8]),(0,[z1,z2,z3,z4,z578,z5,z8]),(0,[z1,z2,z59,z3,z4,z5,z76])],[(0,[z1,z2,z483,z3,z4,z5,z8]),(0,[z1,z2,z3,z579,z4,z5,z8]),(0,[z1,z137,z2,z3,z4,z5,z8]),(1,[z1,z189,z3,z4,z5,z8]),(0,[z1,z149,z2,z3,z4,z5,z10])],[(0,[z1,z2,z580,z3,z4,z5,z8]),(0,[z1,z2,z3,z581,z4,z5,z8]),(0,[z1,z2,z3,z148,z4,z5,z8]),(0,[z1,z582,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z583,z5,z8]),(1,[z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z584,z8]),(0,[z1,z149,z2,z3,z4,z5,z280]),(0,[z1,z2,z21,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z585,z8])],[(0,[z1,z190,z2,z3,z4,z40,z8]),(0,[z586,z1,z2,z3,z4,z5,z8]),(0,[z587,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z588,z8]),(0,[z1,z2,z3,z4,z12,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z245]),(0,[z1,z2,z3,z32,z4,z5,z6]),(0,[z1,z2,z589,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z513,z8]),(1,[z161,z2,z3,z4,z17,z8]),(0,[z1,z2,z590,z3,z4,z5,z8])],[(0,[z591,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z398]),(0,[z23,z1,z2,z3,z15,z4,z5]),(0,[z1,z77,z2,z3,z15,z4,z5])],[(0,[z1,z2,z143,z3,z15,z4,z5]),(0,[z1,z2,z21,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z592,z5,z8])],[(0,[z136,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z17,z8,z593]),(0,[z1,z2,z3,z4,z5,z8,z235]),(0,[z1,z293,z2,z3,z4,z5,z8])],[(0,[z169,z11,z1,z2,z3,z4,z5]),(0,[z0,z73,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z594,z8]),(0,[z1,z2,z3,z595,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z90,z33]),(0,[z1,z2,z3,z127,z4,z5,z6]),(0,[z11,z1,z2,z3,z5,z8,z98])]],
   [[(0,[z1,z2,z3,z4,z545,z17,z8]),(1,[z1,z2,z3,z4,z5,z138]),(0,[z1,z9,z2,z3,z4,z5,z8]),(1,[z11,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z596,z5,z8])],[(0,[z1,z2,z3,z4,z5,z397,z8]),(0,[z1,z597,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z598,z8]),(0,[z290,z1,z2,z4,z12,z5,z8]),(0,[z1,z2,z3,z4,z5,z34,z8])],[(0,[z1,z2,z3,z4,z599,z5,z8]),(0,[z1,z600,z2,z3,z4,z5,z8]),(1,[z1,z2,z282,z32,z5,z8]),(0,[z209,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z101,z4,z5,z233])],[(0,[z1,z601,z2,z3,z4,z5,z8]),(0,[z136,z1,z2,z3,z27,z5,z8]),(0,[z1,z2,z3,z4,z602,z5,z8]),(0,[z1,z2,z3,z4,z603,z5,z8]),(0,[z1,z2,z604,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z16,z8]),(0,[z1,z2,z3,z4,z5,z8,z593]),(0,[z1,z42,z2,z3,z4,z40,z8]),(0,[z1,z2,z421,z4,z5,z8,z6]),(1,[z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z498,z8]),(0,[z1,z2,z3,z15,z4,z5,z98]),(0,[z1,z2,z3,z468,z15,z4,z5])],[(0,[z1,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z605,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z36,z6]),(0,[z346,z1,z2,z3,z4,z5,z33])],[(0,[z247,z1,z2,z3,z4,z5,z8]),(0,[z169,z1,z2,z483,z4,z5,z8]),(0,[z1,z2,z26,z3,z4,z5,z513]),(0,[z1,z2,z3,z4,z27,z17,z8]),(0,[z1,z2,z3,z29,z4,z40,z8]),(0,[z1,z2,z3,z15,z4,z5,z44]),(0,[z606,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z77,z2,z3,z4,z5]),(0,[z11,z1,z2,z3,z127,z4,z5]),(0,[z1,z2,z3,z4,z567,z5,z8])],[(0,[z1,z2,z400,z3,z4,z17,z8]),(0,[z1,z607,z2,z3,z4,z5,z8])],[(0,[z169,z1,z2,z3,z4,z5,z6]),(0,[z2,z26,z3,z135,z4,z5,z8]),(0,[z11,z1,z2,z21,z3,z4,z5])]],
   [[(0,[z169,z61,z2,z3,z4,z5,z8]),(0,[z608,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z421,z3,z15,z4,z5]),(0,[z1,z609,z2,z3,z4,z5,z8])],[(0,[z136,z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z17,z17,z8]),(0,[z1,z2,z3,z4,z610,z5,z8]),(0,[z1,z2,z3,z4,z611,z5,z8]),(0,[z1,z2,z3,z4,z612,z5,z8]),(0,[z1,z2,z3,z4,z613,z5,z8])],[(0,[z1,z2,z3,z4,z5,z158,z8]),(0,[z1,z2,z3,z614,z4,z5,z8]),(0,[z331,z1,z2,z3,z4,z5,z8]),(0,[z1,z615,z2,z3,z4,z5,z8]),(0,[z247,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z19,z5,z6])],[(0,[z61,z38,z2,z3,z4,z5,z8]),(0,[z161,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z594,z5,z8]),(0,[z1,z616,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z24,z5,z8]),(0,[z617,z1,z2,z3,z4,z5,z8]),(0,[z1,z618,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z619,z5,z8]),(0,[z304,z1,z2,z3,z32,z4,z5]),(1,[z1,z2,z3,z4,z5,z6]),(0,[z304,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z383,z8])],[(0,[z202,z95,z2,z3,z4,z5,z8]),(0,[z620,z1,z2,z3,z4,z5,z8]),(0,[z621,z1,z2,z3,z4,z5,z8]),(0,[z1,z86,z42,z3,z4,z5,z8]),(0,[z290,z1,z2,z3,z4,z5,z91]),(1,[z1,z2,z282,z4,z5,z6])],[(0,[z1,z38,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z622,z8]),(0,[z1,z2,z3,z4,z571,z17,z8]),(0,[z11,z1,z2,z3,z4,z5,z166]),(0,[z1,z89,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z623,z4,z5,z8]),(0,[z1,z2,z3,z4,z321,z5,z8]),(0,[z1,z86,z2,z3,z127,z4,z8]),(0,[z1,z2,z3,z4,z5,z624,z8]),(1,[z1,z2,z3,z37,z4,z5]),(0,[z35,z11,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z625,z5,z8]),(0,[z1,z626,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z27,z5,z17,z8]),(0,[z1,z190,z2,z3,z4,z17,z8]),(0,[z627,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z421,z4,z5,z6]),(0,[z1,z2,z3,z628,z4,z5,z8])],[(0,[z1,z2,z26,z3,z4,z5,z8]),(0,[z1,z629,z2,z3,z4,z5,z8]),(0,[z1,z630,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z631,z5,z8]),(0,[z11,z1,z2,z3,z84,z4,z5]),(0,[z1,z77,z2,z3,z4,z5,z253]),(0,[z1,z2,z632,z3,z4,z5,z8]),(0,[z633,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z73,z1,z2,z3,z4,z5,z33]),(0,[z161,z1,z2,z3,z4,z40,z8]),(0,[z1,z616,z2,z3,z4,z40,z8]),(1,[z1,z2,z3,z4,z40,z6]),(0,[z150,z1,z2,z3,z116,z5,z8]),(0,[z1,z2,z3,z4,z5,z634,z8]),(0,[z635,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z286,z8]),(0,[z1,z2,z3,z4,z5,z8,z636]),(0,[z267,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z592,z5])],[(0,[z150,z1,z149,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z637,z8]),(0,[z1,z2,z3,z4,z638,z5,z8]),(0,[z290,z1,z2,z3,z4,z5,z33]),(1,[z1,z2,z3,z4,z5,z194])],[(0,[z1,z2,z3,z639,z4,z5,z8]),(0,[z1,z2,z21,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z40,z33,z8]),(0,[z1,z2,z3,z52,z4,z5,z8]),(1,[z1,z2,z4,z5,z33,z6]),(0,[z1,z2,z3,z4,z5,z640,z8]),(0,[z1,z641,z2,z3,z4,z5,z8])],[(0,[z642,z1,z2,z3,z4,z5,z8]),(0,[z1,z643,z2,z3,z4,z5,z8]),(0,[z290,z1,z2,z3,z12,z5,z8]),(0,[z1,z2,z21,z3,z4,z5,z34]),(0,[z11,z1,z2,z3,z4,z5,z90]),(0,[z1,z2,z3,z4,z5,z8,z295]),(0,[z1,z2,z3,z4,z644,z5,z8])],[(0,[z1,z629,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z62,z8]),(0,[z1,z2,z645,z3,z4,z5,z8]),(0,[z646,z1,z2,z3,z4,z5,z8]),(0,[z1,z647,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z6,z363]),(0,[z1,z2,z3,z4,z5,z8,z648])],[(0,[z202,z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z15,z4,z5,z58]),(0,[z1,z2,z3,z4,z5,z311,z8]),(0,[z35,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z127,z4,z5,z8]),(0,[z565,z11,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z343,z5,z8]),(0,[z1,z2,z3,z4,z17,z8,z6]),(0,[z1,z649,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z650,z5,z8]),(0,[z1,z86,z2,z3,z4,z43,z8]),(0,[z1,z20,z2,z3,z4,z5,z6]),(0,[z1,z651,z2,z3,z4,z5,z8]),(0,[z1,z2,z282,z3,z4,z5,z33]),(0,[z652,z1,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z196,z4,z5,z8]),(0,[z1,z2,z3,z52,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z653,z8]),(0,[z1,z2,z3,z4,z5,z33,z427]),(0,[z1,z2,z3,z4,z5,z654,z8]),(1,[z1,z2,z3,z4,z19,z233])]],
   [[(0,[z61,z1,z2,z3,z4,z573,z8]),(0,[z1,z2,z3,z4,z5,z305,z8]),(0,[z1,z2,z3,z4,z27,z5,z6]),(0,[z1,z42,z2,z3,z4,z17,z8]),(1,[z106,z2,z3,z4,z5,z58])],[(0,[z1,z3,z4,z113,z5,z43,z8]),(0,[z1,z86,z2,z3,z15,z4,z5]),(0,[z1,z655,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z33,z16]),(0,[z1,z2,z3,z4,z5,z656,z8])],[(0,[z1,z2,z3,z4,z5,z657,z8]),(0,[z1,z2,z3,z29,z4,z17,z8]),(0,[z1,z2,z3,z127,z4,z40,z8]),(0,[z1,z2,z3,z15,z4,z5,z43])],[(0,[z1,z2,z3,z4,z5,z658,z8])],[(0,[z1,z2,z3,z659,z4,z5,z8])],[(0,[z169,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z660,z3,z4,z5,z8]),(1,[z11,z1,z2,z3,z29,z5]),(0,[z1,z601,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z464,z4,z17,z8]),(0,[z1,z2,z3,z197,z4,z5,z8]),(0,[z106,z1,z2,z3,z484,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z661]),(0,[z1,z2,z3,z662,z4,z5,z8]),(0,[z1,z2,z3,z4,z663,z5,z8])],[(0,[z161,z1,z2,z3,z4,z5,z71]),(0,[z23,z1,z2,z3,z4,z296,z8]),(0,[z178,z1,z2,z3,z4,z5,z8]),(0,[z586,z11,z1,z2,z3,z4,z5]),(0,[z664,z1,z2,z3,z4,z5,z8])],[(1,[z1,z2,z3,z104,z5,z8]),(0,[z247,z1,z2,z3,z4,z17,z8]),(1,[z1,z2,z3,z4,z111,z8]),(0,[z1,z2,z3,z4,z5,z665,z8]),(0,[z1,z2,z3,z4,z78,z5,z33])]],
   [[(0,[z1,z2,z666,z3,z4,z5,z8]),(0,[z202,z2,z3,z4,z40,z5,z8]),(0,[z1,z2,z667,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z19,z5,z8])],[(0,[z1,z2,z3,z4,z668,z5,z8]),(0,[z1,z2,z3,z4,z5,z44,z166]),(0,[z1,z2,z3,z4,z5,z669,z8]),(0,[z1,z190,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z670,z4,z5,z8])],[(0,[z169,z1,z2,z3,z4,z40,z8]),(0,[z671,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z672,z8]),(0,[z1,z2,z660,z3,z4,z40,z8])],[(0,[z1,z38,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z673,z5,z8]),(0,[z1,z373,z2,z3,z4,z5,z8]),(0,[z674,z1,z2,z3,z4,z5,z8]),(0,[z1,z89,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z675,z4,z5,z8]),(0,[z1,z2,z3,z676,z4,z5,z8]),(1,[z290,z1,z2,z12,z5,z8]),(0,[z92,z1,z2,z3,z4,z5,z8]),(0,[z1,z677,z2,z3,z4,z5,z8])],[(0,[z678,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z573,z8]),(0,[z679,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z59,z26,z4,z5,z8])],[(0,[z1,z2,z3,z4,z171,z5,z8]),(0,[z73,z1,z2,z3,z4,z183,z8]),(1,[z73,z2,z26,z4,z5,z8]),(0,[z161,z1,z2,z3,z4,z17,z8]),(1,[z1,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z4,z19,z40,z8]),(0,[z1,z2,z3,z433,z4,z5,z33])],[(0,[z680,z1,z2,z3,z4,z5,z8]),(0,[z73,z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z37,z32,z4,z5])],[(0,[z1,z2,z3,z4,z5,z672,z8]),(0,[z290,z1,z2,z3,z15,z4,z5]),(1,[z1,z2,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z12,z5,z6]),(0,[z1,z2,z282,z3,z4,z5,z386]),(0,[z1,z2,z282,z4,z5,z8,z6]),(0,[z1,z527,z2,z3,z4,z5,z8]),(0,[z390,z1,z2,z3,z15,z4,z5])]],
   [[(0,[z1,z38,z2,z3,z4,z40,z8]),(0,[z681,z1,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z29,z5,z8]),(0,[z1,z2,z3,z682,z4,z5,z8]),(1,[z1,z2,z3,z347,z4,z5])],[(1,[z169,z143,z3,z4,z5,z8]),(0,[z1,z2,z3,z683,z4,z5,z8]),(0,[z684,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z26,z3,z4,z17,z8]),(1,[z1,z2,z3,z4,z5,z154]),(0,[z1,z358,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z32,z4,z5]),(0,[z1,z2,z3,z15,z4,z5,z33])],[(0,[z169,z1,z2,z3,z4,z69,z8]),(0,[z1,z2,z143,z3,z4,z5,z33]),(0,[z685,z1,z2,z3,z4,z5,z8]),(0,[z161,z1,z2,z3,z27,z5,z8]),(0,[z1,z42,z2,z3,z4,z5,z33]),(0,[z1,z647,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z686,z8])],[(0,[z1,z2,z282,z3,z4,z5,z13]),(0,[z1,z2,z3,z101,z4,z8,z93])],[(0,[z1,z2,z3,z104,z4,z5,z8]),(0,[z161,z1,z2,z3,z4,z594,z8]),(0,[z1,z2,z3,z29,z4,z5,z33]),(0,[z1,z2,z3,z52,z4,z17,z8]),(0,[z1,z2,z3,z4,z40,z452,z8]),(0,[z1,z2,z3,z4,z687,z5,z8]),(0,[z11,z1,z89,z2,z3,z4,z5]),(0,[z1,z688,z2,z3,z4,z5,z8]),(0,[z689,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z8,z690])],[(0,[z11,z1,z190,z2,z3,z4,z5]),(0,[z1,z691,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z433,z4,z5]),(0,[z1,z2,z3,z4,z5,z142,z8])],[(0,[z692,z1,z2,z3,z4,z5,z8]),(1,[z1,z2,z3,z4,z162,z8]),(0,[z1,z2,z3,z29,z12,z5,z8]),(0,[z1,z2,z21,z3,z127,z4,z8]),(0,[z11,z1,z2,z3,z210,z4,z5])],[(0,[z1,z2,z3,z32,z27,z5,z8]),(0,[z1,z2,z3,z127,z4,z17,z8]),(0,[z1,z2,z3,z4,z40,z8,z93]),(0,[z693,z1,z2,z3,z4,z5,z8]),(0,[z1,z694,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z695,z4,z5,z8]),(0,[z696,z1,z2,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z63,z5,z8]),(0,[z0,z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z258,z5,z8]),(0,[z697,z1,z2,z3,z4,z5,z8]),(0,[z35,z1,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z84,z4,z5,z6]),(1,[z1,z2,z3,z4,z5,z100])],[(0,[z1,z20,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z40,z467,z8]),(0,[z1,z2,z3,z4,z5,z8,z8]),(0,[z1,z2,z3,z15,z4,z5,z16])],[(0,[z1,z2,z3,z4,z698,z5,z8]),(0,[z1,z2,z3,z4,z699,z5,z8]),(1,[z11,z1,z2,z3,z27,z5]),(0,[z1,z2,z3,z4,z17,z8,z98]),(0,[z11,z1,z2,z282,z3,z4,z5]),(1,[z48,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z5,z36]),(0,[z700,z1,z2,z3,z4,z5,z8])],[(0,[z701,z1,z2,z3,z4,z5,z8]),(0,[z95,z1,z2,z3,z4,z5,z6]),(0,[z23,z1,z2,z3,z4,z5,z166]),(0,[z150,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z702,z5,z8]),(0,[z1,z20,z3,z4,z5,z8,z18]),(0,[z1,z2,z3,z4,z703,z5,z8])],[(0,[z1,z2,z3,z4,z5,z559,z8]),(0,[z704,z1,z2,z3,z4,z5,z8]),(0,[z1,z42,z2,z3,z127,z4,z8]),(0,[z1,z20,z2,z3,z4,z5,z44]),(0,[z11,z1,z2,z421,z3,z4,z5]),(1,[z1,z2,z3,z4,z592,z5])],[(0,[z705,z1,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z27,z5]),(0,[z1,z149,z2,z3,z116,z5,z8]),(0,[z1,z2,z421,z3,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z16,z6]),(0,[z11,z1,z2,z14,z3,z4,z5]),(0,[z1,z2,z3,z4,z342,z5,z8])],[(0,[z1,z2,z313,z3,z4,z12,z8]),(0,[z105,z1,z2,z3,z4,z5,z6]),(0,[z35,z1,z2,z3,z5,z36,z8]),(0,[z11,z1,z2,z3,z4,z5,z233])],[(0,[z169,z1,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z5,z8]),(0,[z1,z2,z3,z4,z698,z40,z8]),(0,[z106,z1,z2,z3,z317,z5,z8]),(0,[z1,z2,z706,z3,z4,z5,z8])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z5,z707]),(0,[z1,z708,z3,z4,z5,z8]),(0,[z704,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z24,z33]),(0,[z1,z2,z3,z709,z4,z5])],[(0,[z1,z2,z3,z4,z710,z8]),(0,[z1,z2,z3,z168,z4,z93])],[(0,[z169,z143,z3,z4,z5,z6]),(0,[z1,z2,z4,z711,z90,z8])],[(0,[z11,z1,z2,z3,z5,z510]),(0,[z218,z1,z2,z3,z36,z8]),(0,[z1,z2,z3,z4,z5,z712]),(0,[z1,z2,z3,z713,z5,z8]),(0,[z1,z2,z3,z148,z4,z5])],[(0,[z1,z2,z3,z343,z5,z33]),(0,[z303,z1,z2,z12,z5,z8]),(0,[z1,z2,z3,z4,z5,z714]),(0,[z1,z2,z3,z4,z715,z8]),(0,[z228,z2,z3,z4,z17,z8]),(0,[z48,z2,z3,z4,z36,z8]),(0,[z1,z2,z210,z4,z238,z5])],[(0,[z716,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z224,z4,z321])],[(0,[z1,z717,z3,z4,z5,z8]),(0,[z1,z2,z210,z29,z4,z5]),(0,[z2,z3,z15,z4,z342,z17]),(0,[z346,z2,z3,z4,z5,z58]),(0,[z1,z2,z3,z4,z5,z718])],[(0,[z1,z2,z29,z12,z5,z6])],[(0,[z1,z2,z3,z4,z369,z158]),(0,[z2,z3,z4,z594,z17,z8]),(0,[z1,z2,z3,z4,z5,z719])],[(0,[z161,z2,z3,z27,z17,z8]),(0,[z11,z1,z2,z210,z29,z5]),(0,[z133,z11,z1,z2,z3,z5]),(0,[z1,z2,z3,z720,z4,z5])],[],[(0,[z721,z1,z2,z3,z63,z5]),(0,[z722,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z723,z4,z5]),(0,[z724,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z725,z8]),(0,[z1,z2,z4,z726,z5,z8])],[(0,[z1,z2,z3,z4,z5,z727]),(0,[z1,z2,z3,z29,z5,z243]),(0,[z11,z1,z2,z3,z484,z5]),(0,[z11,z1,z2,z3,z340,z5]),(0,[z1,z2,z32,z726,z5,z8]),(0,[z1,z2,z3,z5,z728,z6])],[(0,[z1,z2,z3,z170,z5,z8]),(0,[z1,z2,z294,z4,z5,z249]),(0,[z1,z2,z3,z343,z5,z144]),(0,[z95,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z83,z4,z93]),(0,[z1,z729,z2,z3,z4,z8]),(0,[z1,z2,z3,z101,z4,z88])],[(0,[z1,z2,z3,z4,z5,z730]),(0,[z405,z2,z3,z4,z17,z8])]],
   [[(0,[z1,z2,z3,z170,z369,z8]),(0,[z300,z2,z3,z4,z17,z8]),(0,[z112,z2,z3,z4,z40,z8]),(0,[z1,z2,z605,z4,z5,z33])],[(0,[z1,z2,z3,z4,z731,z8]),(0,[z1,z2,z3,z732,z5,z8]),(0,[z1,z2,z3,z733,z5,z8]),(0,[z1,z2,z3,z391,z4,z93])],[(0,[z1,z2,z3,z4,z5,z734]),(0,[z620,z2,z3,z4,z17,z8]),(0,[z1,z2,z735,z3,z4,z8]),(0,[z1,z2,z476,z4,z5,z6]),(0,[z1,z2,z4,z5,z13,z6]),(0,[z1,z2,z32,z4,z592,z5])],[(0,[z1,z2,z3,z4,z5,z736]),(0,[z649,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z737]),(0,[z1,z2,z148,z4,z5,z6])],[(0,[z494,z2,z3,z27,z5,z8]),(0,[z11,z1,z2,z14,z27,z5]),(0,[z390,z2,z3,z15,z4,z17]),(0,[z1,z2,z3,z15,z517,z5])],[(0,[z1,z2,z3,z4,z738,z8]),(0,[z1,z2,z3,z739,z4,z5]),(0,[z1,z2,z282,z4,z17,z6]),(0,[z11,z1,z2,z3,z5,z543]),(0,[z35,z1,z2,z3,z36,z6])],[(0,[z1,z2,z3,z4,z740,z8]),(0,[z206,z1,z2,z3,z5,z245])],[(0,[z1,z2,z349,z4,z5,z6]),(0,[z1,z2,z421,z4,z17,z6]),(0,[z1,z2,z3,z4,z17,z130]),(0,[z1,z2,z3,z4,z40,z741]),(0,[z362,z1,z2,z4,z5,z33])],[(0,[z1,z2,z3,z4,z742,z8]),(0,[z1,z2,z400,z4,z5,z6]),(0,[z1,z2,z285,z3,z4,z321]),(1,[z1,z2,z3,z4,z743])],[(0,[z1,z2,z483,z63,z5,z8]),(0,[z73,z2,z26,z4,z40,z8]),(0,[z1,z2,z3,z4,z744,z6])],[(0,[z1,z2,z3,z4,z745,z5]),(0,[z1,z2,z3,z4,z261,z467])],[(0,[z1,z2,z3,z63,z5,z6]),(0,[z1,z2,z3,z170,z69,z8]),(0,[z1,z2,z3,z746,z5,z8]),(0,[z1,z2,z4,z12,z40,z6]),(0,[z1,z649,z52,z4,z5,z8]),(0,[z1,z2,z3,z4,z747,z8])],[(0,[z1,z2,z3,z210,z4,z40]),(0,[z1,z2,z3,z433,z4,z5])],[(0,[z748,z1,z2,z3,z5,z8]),(0,[z1,z2,z3,z148,z29,z5]),(0,[z11,z1,z2,z3,z433,z5])],[(0,[z1,z2,z313,z3,z4,z33]),(0,[z749,z1,z2,z3,z4,z5]),(0,[z1,z77,z2,z4,z78,z6]),(0,[z1,z2,z79,z4,z5,z6]),(0,[z48,z2,z3,z4,z258,z8])],[(0,[z1,z2,z3,z750,z4,z5]),(0,[z1,z2,z3,z4,z5,z751]),(0,[z1,z2,z3,z4,z5,z100]),(0,[z1,z2,z3,z4,z752,z33])]],
   [[(0,[z1,z753,z2,z4,z5,z8]),(0,[z61,z38,z3,z4,z5,z33]),(0,[z1,z754,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z40,z755]),(0,[z1,z89,z52,z4,z5,z6]),(0,[z1,z9,z2,z3,z15,z4]),(1,[z1,z2,z210,z4,z5])],[(0,[z0,z2,z135,z343,z5,z8]),(0,[z11,z1,z2,z3,z4,z40]),(0,[z106,z2,z3,z4,z17,z58]),(0,[z1,z86,z3,z15,z4,z113])],[(0,[z1,z2,z3,z756,z4,z5]),(0,[z1,z2,z3,z4,z8,z757]),(0,[z1,z2,z3,z4,z8,z758]),(0,[z11,z1,z2,z282,z32,z5]),(0,[z11,z1,z2,z759,z4,z5])],[(0,[z1,z2,z210,z4,z40,z5]),(0,[z1,z2,z3,z5,z728,z8]),(0,[z1,z2,z3,z15,z4,z251])],[(0,[z1,z2,z483,z4,z5,z33]),(0,[z1,z373,z2,z3,z4,z40]),(0,[z1,z2,z3,z484,z5,z33]),(0,[z180,z1,z2,z210,z4,z5])],[(0,[z1,z2,z3,z4,z760,z8]),(0,[z161,z1,z2,z210,z4,z5])],[(0,[z1,z2,z3,z4,z761,z8]),(0,[z48,z2,z3,z4,z40,z8]),(0,[z106,z2,z3,z4,z5,z156]),(0,[z1,z2,z3,z4,z5,z762]),(0,[z1,z2,z3,z4,z5,z763]),(0,[z1,z447,z2,z4,z5,z33])],[(0,[z1,z2,z3,z4,z5,z764]),(0,[z11,z1,z2,z3,z103,z5]),(0,[z1,z367,z3,z4,z43,z8]),(0,[z1,z20,z3,z4,z40,z18]),(0,[z1,z2,z3,z4,z765,z8])],[(0,[z1,z2,z3,z484,z129,z8]),(0,[z1,z2,z3,z4,z5,z766]),(0,[z1,z86,z3,z4,z113,z6])],[(0,[z169,z11,z143,z3,z4,z5]),(0,[z1,z2,z282,z12,z5,z6])],[(0,[z1,z2,z3,z15,z4,z369]),(0,[z1,z2,z3,z4,z129,z6]),(0,[z1,z2,z3,z4,z5,z280]),(0,[z1,z2,z3,z15,z5,z359])],[(0,[z1,z2,z3,z15,z4,z594]),(0,[z1,z2,z3,z4,z5,z767]),(0,[z11,z1,z2,z3,z4,z747])],[(0,[z290,z1,z2,z12,z17,z8]),(0,[z1,z2,z4,z5,z286,z6]),(0,[z1,z2,z3,z768,z5,z6])],[(0,[z1,z2,z3,z4,z40,z10]),(0,[z1,z2,z4,z5,z33,z763])],[(0,[z1,z2,z3,z4,z5,z769]),(0,[z1,z770,z2,z3,z4,z5]),(0,[z1,z2,z3,z484,z5,z166]),(0,[z1,z2,z3,z4,z771,z8])],[(0,[z1,z2,z3,z4,z5,z55]),(0,[z772,z1,z2,z3,z343,z5]),(0,[z1,z2,z3,z4,z744,z8]),(0,[z1,z2,z4,z644,z5,z6]),(0,[z1,z2,z210,z4,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z162,z71]),(0,[z1,z2,z3,z4,z40,z34]),(0,[z773,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z774,z8])],[(0,[z1,z2,z3,z63,z5,z8]),(0,[z1,z2,z483,z4,z5,z158]),(0,[z11,z1,z2,z3,z4,z141])],[(0,[z1,z2,z400,z4,z17,z6]),(0,[z2,z3,z4,z342,z17,z8]),(0,[z1,z2,z3,z505,z56,z8]),(0,[z206,z1,z149,z2,z3,z5]),(0,[z180,z1,z3,z4,z567,z5])],[(0,[z1,z2,z3,z4,z775,z8]),(0,[z1,z2,z3,z155,z4,z17]),(0,[z1,z2,z4,z5,z653,z6])],[(0,[z1,z2,z3,z4,z5,z776]),(0,[z1,z367,z3,z4,z279,z8]),(0,[z1,z2,z550,z4,z5,z6]),(0,[z254,z267,z2,z3,z4,z5])],[(0,[z206,z1,z2,z3,z12,z5]),(0,[z1,z2,z3,z777,z5,z33]),(0,[z122,z1,z2,z3,z4,z383])],[(0,[z1,z2,z3,z4,z5,z243]),(0,[z1,z89,z52,z4,z5,z8]),(0,[z1,z2,z3,z778,z4,z8]),(0,[z1,z2,z3,z4,z5,z779]),(0,[z1,z2,z3,z4,z780,z6]),(0,[z1,z2,z3,z4,z153,z233]),(0,[z1,z2,z3,z4,z781,z8]),(0,[z1,z2,z3,z4,z743,z93])],[(0,[z748,z1,z2,z3,z17,z8]),(0,[z106,z2,z3,z4,z129,z58]),(0,[z1,z2,z3,z4,z782,z8]),(0,[z1,z2,z3,z4,z783,z8])],[(0,[z1,z2,z3,z4,z5,z784]),(0,[z1,z2,z3,z4,z5,z785]),(0,[z1,z786,z2,z3,z4,z5]),(0,[z11,z1,z77,z2,z4,z78]),(0,[z1,z2,z4,z5,z763,z6])],[(0,[z1,z143,z294,z4,z5,z8]),(0,[z169,z143,z3,z63,z5,z8]),(0,[z1,z479,z3,z343,z5,z8]),(0,[z1,z2,z3,z4,z787,z8]),(0,[z1,z2,z3,z4,z17,z100]),(0,[z23,z1,z2,z210,z4,z5]),(0,[z290,z1,z2,z313,z12,z8])],[(0,[z1,z2,z3,z104,z5,z33]),(1,[z1,z2,z210,z29,z5]),(0,[z480,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z15,z5,z16]),(0,[z1,z2,z3,z4,z8,z743])],[(0,[z1,z2,z294,z4,z5,z788]),(0,[z1,z2,z3,z170,z5,z6]),(0,[z789,z1,z2,z3,z104,z5]),(0,[z11,z1,z2,z3,z29,z40]),(0,[z234,z2,z3,z29,z5,z8]),(0,[z11,z1,z2,z3,z15,z40]),(0,[z1,z2,z259,z4,z5,z6]),(0,[z1,z2,z3,z4,z790,z8])],[(0,[z1,z2,z3,z4,z5,z33]),(0,[z1,z2,z3,z196,z5,z16]),(0,[z1,z2,z3,z4,z40,z91]),(0,[z1,z2,z791,z3,z4,z5]),(0,[z48,z86,z2,z3,z4,z8])],[(0,[z633,z2,z3,z27,z5,z8]),(0,[z1,z2,z3,z127,z56,z33]),(0,[z1,z2,z3,z4,z5,z792])],[(0,[z1,z2,z3,z63,z69,z8]),(0,[z11,z1,z2,z3,z4,z296]),(0,[z1,z86,z3,z4,z113,z8])],[(0,[z38,z717,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z171]),(0,[z1,z335,z3,z4,z5,z18])]],
   [[(0,[z1,z2,z3,z4,z129,z8]),(0,[z1,z42,z3,z4,z43,z191]),(0,[z1,z3,z4,z5,z793,z18]),(0,[z1,z2,z3,z4,z794,z8]),(0,[z1,z2,z3,z795,z5,z8]),(0,[z1,z2,z3,z15,z5,z796])],[],[(0,[z1,z2,z3,z768,z5,z8]),(0,[z2,z3,z4,z797,z5,z8]),(0,[z106,z2,z3,z4,z342,z5])],[(0,[z0,z2,z135,z4,z5,z6]),(0,[z1,z2,z3,z4,z798,z8])],[(0,[z169,z143,z3,z4,z5,z33]),(0,[z11,z1,z479,z3,z4,z5]),(0,[z1,z2,z3,z104,z5,z144]),(0,[z1,z2,z3,z799,z5,z8]),(0,[z106,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z800,z5]),(0,[z801,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z802,z8]),(0,[z1,z42,z3,z4,z803,z8]),(0,[z1,z2,z4,z5,z33,z240])],[(0,[z1,z2,z3,z4,z5,z144]),(0,[z1,z2,z3,z347,z4,z40]),(1,[z1,z3,z804,z5,z8]),(0,[z1,z2,z3,z4,z5,z191])],[(0,[z1,z2,z12,z5,z352,z6])],[(0,[z1,z2,z3,z805,z4,z5]),(0,[z1,z806,z2,z3,z4,z5]),(0,[z11,z1,z2,z807,z4,z5])],[(0,[z1,z2,z3,z4,z5,z158]),(0,[z1,z2,z3,z808,z5,z8]),(0,[z1,z2,z3,z4,z69,z33]),(0,[z1,z2,z3,z4,z70,z33]),(0,[z1,z2,z3,z4,z17,z55]),(0,[z809,z2,z3,z4,z5,z8])],[(0,[z1,z77,z2,z4,z711,z8]),(0,[z1,z2,z4,z5,z33,z656])],[(0,[z1,z2,z3,z63,z17,z8]),(0,[z281,z2,z3,z29,z5,z8]),(0,[z1,z86,z3,z4,z545,z8]),(0,[z202,z2,z3,z4,z40,z33]),(0,[z1,z2,z3,z433,z4,z40]),(0,[z1,z2,z3,z4,z810,z8]),(0,[z1,z3,z4,z803,z5,z8]),(0,[z1,z2,z313,z3,z155,z4])],[(0,[z1,z2,z3,z811,z4,z5]),(0,[z121,z2,z3,z4,z17,z8]),(0,[z35,z1,z2,z3,z22,z8]),(0,[z1,z2,z3,z4,z780,z8]),(0,[z1,z2,z21,z4,z711,z8]),(0,[z1,z2,z3,z812,z4,z5])],[(0,[z1,z2,z813,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z386])],[(0,[z136,z2,z3,z27,z5,z33]),(0,[z1,z2,z3,z4,z5,z814]),(0,[z1,z2,z410,z32,z5,z8]),(0,[z206,z1,z2,z3,z4,z40]),(0,[z1,z2,z4,z5,z763,z8])],[(0,[z308,z143,z3,z4,z5,z8])]],
   [[(0,[z1,z2,z3,z4,z17,z243]),(0,[z1,z89,z52,z4,z17,z8]),(0,[z1,z629,z2,z4,z698,z8]),(0,[z1,z2,z3,z4,z321,z8])],[(0,[z169,z143,z3,z4,z5,z158]),(0,[z1,z2,z3,z4,z5,z815]),(0,[z2,z3,z27,z17,z16,z8]),(0,[z1,z2,z816,z4,z5,z8]),(0,[z1,z42,z230,z3,z4,z8]),(0,[z180,z1,z3,z4,z5,z97]),(0,[z290,z1,z2,z251,z12,z8]),(0,[z700,z1,z2,z4,z5,z33]),(0,[z35,z1,z2,z3,z60,z36]),(0,[z1,z2,z3,z4,z5,z817])],[(0,[z1,z2,z3,z4,z5,z818]),(0,[z1,z2,z3,z4,z5,z819]),(0,[z1,z248,z3,z4,z5,z44]),(0,[z1,z2,z210,z4,z5,z33])],[(0,[z1,z2,z3,z505,z258,z8]),(0,[z1,z2,z3,z15,z4,z129]),(0,[z1,z2,z3,z4,z5,z820]),(0,[z1,z2,z4,z12,z5,z91]),(0,[z465,z1,z3,z4,z5,z97])],[(0,[z1,z2,z3,z821,z5,z8]),(0,[z1,z2,z3,z4,z5,z822]),(0,[z373,z2,z3,z4,z27,z17]),(0,[z1,z2,z3,z15,z17,z16]),(0,[z1,z2,z4,z5,z269,z6]),(0,[z360,z1,z2,z3,z15,z5]),(0,[z1,z9,z2,z3,z4,z33]),(0,[z180,z1,z3,z4,z5,z793]),(0,[z1,z2,z807,z4,z5,z8]),(0,[z35,z1,z2,z3,z15,z36])],[(0,[z1,z536,z52,z4,z5,z8]),(0,[z1,z491,z59,z4,z5,z8]),(0,[z1,z2,z4,z823,z17,z8]),(0,[z1,z2,z14,z4,z5,z13]),(0,[z1,z2,z3,z4,z238,z233])],[(0,[z1,z2,z3,z4,z69,z158]),(0,[z1,z2,z3,z4,z5,z824]),(0,[z1,z2,z3,z4,z825,z8]),(0,[z1,z2,z3,z4,z17,z33]),(0,[z1,z2,z3,z4,z40,z13]),(0,[z1,z3,z4,z113,z803,z8]),(0,[z1,z2,z14,z15,z4,z5])],[(0,[z1,z2,z3,z4,z5,z826]),(0,[z0,z2,z135,z104,z5,z8]),(0,[z1,z2,z3,z4,z594,z243]),(0,[z206,z1,z2,z12,z5,z6]),(0,[z35,z1,z2,z3,z36,z33])],[(0,[z1,z2,z3,z827,z5,z8]),(0,[z136,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z40,z828])],[(0,[z1,z2,z3,z4,z5,z829]),(0,[z169,z143,z3,z170,z5,z8]),(0,[z0,z2,z135,z4,z5,z8]),(0,[z11,z73,z2,z26,z4,z5])],[(0,[z1,z2,z3,z4,z40,z398]),(0,[z1,z2,z285,z3,z27,z5]),(0,[z1,z2,z3,z830,z5,z8]),(0,[z1,z2,z3,z4,z831,z17]),(0,[z1,z2,z3,z4,z40,z60]),(0,[z1,z2,z3,z4,z832,z8]),(0,[z1,z2,z21,z4,z90,z34]),(0,[z1,z2,z3,z4,z833,z6]),(0,[z11,z1,z2,z834,z4,z5])],[(0,[z1,z479,z3,z4,z5,z6]),(0,[z1,z189,z3,z4,z141,z8]),(0,[z11,z1,z2,z3,z167,z5]),(0,[z1,z2,z3,z4,z19,z473])],[(0,[z1,z835,z3,z4,z5,z8]),(0,[z2,z3,z4,z797,z17,z8]),(0,[z1,z2,z210,z4,z5,z166]),(0,[z105,z2,z3,z4,z5,z156])],[(0,[z1,z2,z3,z4,z594,z33]),(0,[z1,z836,z3,z4,z5,z8])],[(0,[z1,z2,z210,z84,z4,z5]),(0,[z1,z2,z837,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z838]),(0,[z1,z2,z3,z839,z4,z5]),(0,[z11,z1,z2,z3,z127,z56])]],
   [[(0,[z1,z2,z3,z4,z17,z144]),(0,[z1,z2,z3,z155,z4,z5]),(0,[z1,z77,z2,z4,z78,z33]),(0,[z178,z1,z3,z4,z567,z5])],[(0,[z11,z1,z2,z210,z4,z40])],[(0,[z2,z3,z27,z12,z17,z8]),(0,[z304,z1,z2,z3,z27,z5]),(0,[z23,z2,z3,z4,z40,z166])],[(0,[z721,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z17,z158]),(0,[z2,z3,z4,z5,z840,z8]),(0,[z1,z2,z3,z4,z5,z841]),(0,[z1,z2,z3,z4,z5,z842]),(0,[z1,z86,z2,z210,z4,z5]),(0,[z1,z647,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z843,z8]),(0,[z1,z2,z3,z778,z4,z6])],[(0,[z161,z2,z3,z29,z5,z8]),(0,[z11,z1,z2,z816,z4,z5])],[(0,[z102,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z15,z4,z333])],[(0,[z1,z2,z3,z15,z4,z573]),(0,[z1,z189,z3,z4,z171,z8]),(0,[z1,z2,z3,z4,z5,z844]),(0,[z1,z302,z3,z4,z452,z8]),(0,[z1,z2,z3,z4,z845,z8])],[(0,[z1,z2,z3,z4,z17,z386]),(0,[z11,z1,z9,z2,z3,z4]),(0,[z1,z2,z4,z5,z6,z235]),(0,[z1,z2,z277,z4,z5,z6])],[(0,[z1,z2,z4,z846,z5,z8]),(0,[z1,z2,z3,z4,z847,z8]),(0,[z315,z2,z3,z4,z17,z8])],[(0,[z1,z2,z3,z4,z848,z8]),(0,[z1,z2,z3,z4,z5,z849])],[(0,[z1,z189,z3,z15,z4,z5]),(0,[z11,z2,z3,z4,z40,z17]),(0,[z1,z2,z3,z4,z40,z253]),(0,[z1,z2,z3,z4,z5,z850])],[(0,[z1,z2,z3,z170,z17,z8]),(0,[z1,z2,z3,z4,z5,z851])],[(0,[z1,z2,z852,z4,z5,z8]),(0,[z1,z2,z421,z4,z5,z763]),(0,[z1,z2,z3,z4,z853,z8]),(0,[z390,z2,z3,z103,z4,z5])],[(0,[z1,z2,z3,z4,z40,z249]),(0,[z1,z189,z3,z4,z5,z398]),(0,[z1,z2,z3,z4,z854,z8]),(0,[z1,z2,z3,z4,z5,z855]),(0,[z2,z3,z856,z27,z5,z8]),(0,[z206,z1,z2,z12,z5,z8]),(0,[z1,z2,z3,z4,z5,z857])],[(0,[z150,z1,z3,z116,z40,z8]),(0,[z1,z2,z3,z4,z5,z858]),(0,[z1,z2,z4,z5,z859,z6]),(0,[z1,z2,z210,z4,z78,z5])],[(0,[z11,z1,z2,z3,z659,z5]),(0,[z1,z479,z3,z104,z5,z8]),(0,[z1,z2,z3,z4,z860,z8]),(0,[z202,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z40,z151])]],
   [[(0,[z57,z1,z3,z4,z5,z44]),(0,[z1,z2,z3,z4,z833,z8]),(0,[z1,z2,z3,z4,z5,z861])],[(0,[z1,z479,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z862]),(0,[z1,z2,z3,z4,z74,z8]),(0,[z863,z1,z2,z3,z4,z5])],[(0,[z1,z2,z864,z4,z5,z8]),(0,[z1,z865,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z866]),(0,[z1,z2,z210,z4,z19,z5])],[(0,[z1,z2,z294,z4,z5,z8]),(0,[z0,z2,z135,z4,z17,z8]),(0,[z488,z2,z3,z4,z17,z8]),(0,[z1,z2,z867,z4,z5,z8]),(0,[z290,z1,z2,z148,z12,z5]),(0,[z11,z1,z2,z813,z4,z5])],[(0,[z312,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z868]),(0,[z1,z2,z3,z4,z5,z869])],[(0,[z1,z2,z294,z4,z369,z8]),(0,[z1,z2,z3,z4,z870,z8]),(0,[z1,z2,z3,z148,z4,z40]),(0,[z1,z2,z3,z433,z12,z5]),(0,[z1,z2,z282,z32,z5,z13])],[(0,[z265,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z871])],[(0,[z872,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z873,z8]),(0,[z1,z2,z3,z4,z5,z874]),(0,[z1,z2,z3,z5,z8,z875])],[(0,[z11,z267,z2,z3,z4,z17]),(0,[z1,z2,z3,z4,z876,z5]),(0,[z11,z453,z1,z2,z3,z5])],[(0,[z95,z2,z3,z4,z17,z6]),(0,[z11,z1,z2,z3,z4,z111])],[(0,[z11,z1,z2,z3,z4,z761]),(0,[z54,z1,z2,z210,z4,z5]),(0,[z239,z1,z2,z4,z592,z5]),(0,[z652,z1,z2,z3,z15,z5])],[(0,[z11,z1,z2,z3,z5,z322])],[(0,[z1,z2,z3,z170,z5,z33]),(0,[z1,z2,z3,z4,z321,z6]),(0,[z11,z1,z2,z877,z4,z5])],[(0,[z161,z2,z3,z29,z17,z8]),(0,[z1,z77,z2,z210,z4,z5])],[(0,[z1,z2,z3,z4,z878,z5])]],
   [[(0,[z1,z2,z294,z4,z69,z8]),(0,[z1,z879,z2,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z844]),(0,[z1,z2,z21,z4,z62,z8]),(0,[z106,z2,z3,z4,z5,z840]),(0,[z1,z2,z21,z210,z4,z5])],[(0,[z1,z2,z3,z4,z397,z6]),(0,[z290,z1,z2,z12,z5,z33]),(0,[z1,z2,z3,z880,z4,z5])],[(0,[z1,z2,z3,z4,z881,z8]),(0,[z1,z2,z3,z882,z4,z5]),(0,[z1,z2,z3,z4,z5,z883]),(0,[z1,z215,z3,z4,z5,z44])],[(0,[z1,z2,z3,z4,z884,z8]),(0,[z299,z2,z3,z4,z17,z8]),(0,[z885,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z886]),(0,[z1,z2,z3,z887,z4,z8])],[(0,[z1,z2,z3,z888,z4,z5]),(0,[z11,z2,z3,z27,z5,z17])],[(0,[z161,z2,z3,z29,z594,z8])],[(0,[z1,z2,z889,z3,z4,z5])],[(0,[z1,z2,z3,z4,z831,z5]),(0,[z1,z2,z3,z4,z17,z280]),(0,[z1,z2,z400,z4,z90,z8]),(0,[z1,z2,z414,z4,z5,z6])],[(0,[z1,z890,z2,z3,z4,z8]),(0,[z1,z2,z210,z4,z12,z5]),(0,[z1,z2,z4,z5,z6,z533]),(0,[z1,z2,z3,z433,z5,z286])],[(0,[z1,z2,z3,z4,z891,z8]),(0,[z1,z20,z3,z4,z5,z427])],[(0,[z1,z2,z3,z4,z892,z8])],[(0,[z1,z479,z3,z4,z17,z8]),(0,[z202,z2,z3,z15,z4,z40]),(0,[z1,z2,z3,z4,z5,z893]),(0,[z1,z2,z4,z78,z711,z8])],[(0,[z1,z2,z894,z4,z5,z8]),(0,[z1,z2,z895,z4,z5,z8]),(0,[z1,z2,z3,z37,z4,z17]),(0,[z1,z2,z3,z4,z896,z5]),(0,[z586,z1,z2,z210,z4,z5])],[(0,[z1,z897,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z898]),(0,[z281,z2,z3,z4,z17,z8]),(0,[z2,z3,z4,z17,z572,z8]),(0,[z180,z1,z3,z4,z40,z44]),(0,[z1,z2,z3,z4,z5,z899]),(0,[z1,z2,z3,z900,z4,z5]),(0,[z1,z901,z2,z3,z4,z5]),(0,[z11,z1,z2,z902,z4,z5])],[(0,[z1,z2,z3,z4,z5,z903]),(0,[z150,z1,z3,z321,z116,z8]),(0,[z11,z1,z2,z3,z676,z5])]],
   [[(0,[z95,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z904,z4,z17]),(0,[z1,z2,z282,z37,z32,z5])],[(0,[z1,z2,z3,z905,z4,z5]),(0,[z1,z2,z3,z750,z4,z40])],[(1,[z1,z2,z210,z4,z40]),(0,[z102,z2,z3,z4,z5,z6])],[(0,[z906,z1,z2,z3,z170,z5]),(0,[z61,z1,z2,z210,z4,z5]),(0,[z11,z1,z2,z3,z639,z5]),(1,[z1,z3,z4,z5,z793])],[(0,[z1,z2,z3,z15,z4,z183]),(0,[z1,z2,z3,z4,z907,z8]),(0,[z1,z2,z3,z17,z908,z8]),(0,[z1,z2,z3,z5,z8,z909]),(0,[z910,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z19,z743])],[(0,[z1,z2,z834,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z31]),(0,[z1,z2,z3,z911,z5,z8]),(0,[z1,z2,z3,z912,z4,z5]),(0,[z11,z48,z2,z3,z4,z5]),(0,[z11,z1,z2,z3,z628,z5])],[(0,[z1,z2,z3,z4,z5,z913]),(0,[z1,z2,z3,z914,z5,z8]),(0,[z1,z2,z3,z210,z27,z5]),(0,[z1,z2,z3,z4,z5,z915]),(0,[z1,z2,z3,z804,z5,z8]),(0,[z1,z2,z759,z4,z5,z8])],[(0,[z1,z2,z3,z4,z397,z8]),(0,[z522,z1,z3,z116,z5,z8]),(0,[z1,z149,z3,z84,z5,z8]),(0,[z1,z2,z3,z916,z4,z5]),(0,[z1,z2,z3,z101,z4,z295])],[(0,[z73,z2,z26,z4,z183,z8])],[(0,[z1,z2,z3,z4,z5,z917]),(0,[z1,z2,z3,z4,z918,z8]),(0,[z73,z2,z26,z15,z4,z5])],[(0,[z1,z2,z3,z343,z40,z8]),(0,[z1,z2,z3,z919,z4,z5]),(0,[z1,z2,z3,z4,z920,z5]),(0,[z1,z149,z3,z15,z84,z5]),(0,[z48,z77,z2,z3,z4,z8])],[(0,[z1,z2,z3,z4,z333,z6]),(0,[z1,z2,z3,z4,z921,z8]),(0,[z1,z2,z210,z4,z5,z286])],[(0,[z11,z1,z2,z3,z4,z321]),(0,[z48,z2,z21,z3,z4,z8])],[(0,[z1,z2,z4,z5,z922,z8]),(0,[z382,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z923,z4,z5]),(0,[z924,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z74,z6]),(0,[z1,z2,z3,z4,z5,z925]),(0,[z65,z2,z3,z4,z40,z8])],[(0,[z1,z2,z3,z926,z170,z5]),(1,[z2,z3,z4,z5,z840]),(0,[z11,z1,z2,z14,z5,z98])]],
   [[(0,[z1,z2,z294,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z927]),(0,[z1,z2,z3,z63,z5,z33]),(0,[z1,z2,z4,z5,z33,z669]),(0,[z928,z2,z3,z4,z5,z8])],[(0,[z1,z2,z929,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z930]),(0,[z1,z2,z3,z196,z317,z5]),(0,[z1,z2,z3,z4,z5,z931]),(0,[z1,z2,z3,z932,z4,z5]),(0,[z1,z2,z313,z4,z12,z6])],[(0,[z1,z616,z3,z4,z113,z8]),(0,[z1,z2,z3,z933,z5,z8]),(0,[z1,z2,z210,z934,z4,z5])],[(0,[z1,z2,z3,z15,z4,z74]),(0,[z1,z2,z3,z4,z17,z191]),(0,[z11,z1,z42,z3,z4,z43]),(0,[z1,z2,z282,z15,z32,z5])],[(0,[z54,z1,z81,z3,z4,z5])],[(0,[z2,z3,z4,z856,z5,z8]),(1,[z11,z2,z3,z27,z17]),(0,[z1,z89,z52,z4,z5,z33]),(0,[z1,z89,z2,z210,z4,z5]),(0,[z11,z1,z2,z3,z5,z402])],[(0,[z30,z2,z26,z4,z5,z8]),(0,[z1,z190,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z935,z8]),(0,[z1,z193,z3,z4,z5,z44]),(0,[z48,z2,z3,z15,z4,z5])],[(0,[z1,z2,z3,z936,z4,z5]),(0,[z161,z2,z3,z4,z17,z8]),(0,[z202,z11,z2,z3,z4,z40]),(0,[z1,z2,z3,z37,z5,z352])],[(1,[z2,z937,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z938]),(0,[z1,z2,z3,z939,z4,z8]),(0,[z11,z928,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z940]),(0,[z136,z2,z3,z27,z397,z8]),(0,[z1,z2,z3,z4,z17,z903]),(0,[z2,z3,z4,z40,z797,z8]),(0,[z1,z2,z941,z3,z4,z5])],[(0,[z1,z2,z3,z942,z4,z5]),(0,[z910,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z790,z33]),(0,[z943,z2,z3,z4,z5,z8])],[(0,[z0,z11,z2,z135,z4,z5]),(0,[z664,z2,z3,z4,z40,z8]),(0,[z1,z2,z3,z944,z4,z6])],[(0,[z1,z2,z3,z15,z170,z5]),(0,[z1,z2,z4,z511,z5,z6]),(0,[z1,z2,z3,z4,z5,z138]),(0,[z304,z1,z2,z14,z4,z5])],[(0,[z1,z2,z3,z63,z5,z158]),(0,[z1,z189,z3,z343,z5,z8]),(0,[z1,z2,z3,z4,z945,z8]),(0,[z1,z86,z3,z4,z113,z33])],[(0,[z1,z2,z4,z5,z946,z8]),(0,[z1,z2,z210,z4,z5,z17]),(0,[z1,z2,z3,z4,z5,z947]),(0,[z1,z2,z14,z210,z4,z5])],[(0,[z1,z2,z3,z4,z129,z33]),(0,[z1,z2,z21,z15,z4,z90]),(0,[z1,z2,z3,z4,z948,z6]),(0,[z1,z2,z3,z795,z5,z33]),(0,[z1,z2,z3,z5,z8,z796]),(0,[z1,z2,z3,z15,z4,z949])]],
   [[(0,[z2,z3,z15,z4,z40,z17]),(0,[z1,z2,z4,z17,z950,z8]),(0,[z1,z2,z3,z4,z951,z8]),(0,[z1,z2,z3,z952,z4,z5]),(0,[z1,z2,z3,z4,z5,z953]),(0,[z1,z2,z3,z4,z5,z954])],[(0,[z1,z2,z3,z4,z333,z8]),(0,[z11,z1,z2,z3,z27,z17]),(0,[z1,z2,z3,z4,z5,z955]),(0,[z1,z149,z3,z84,z17,z8]),(0,[z1,z3,z4,z17,z956,z8]),(0,[z11,z1,z2,z3,z40,z98]),(0,[z1,z2,z3,z127,z957,z8])],[(0,[z1,z2,z3,z958,z5,z8])],[(0,[z1,z2,z3,z4,z5,z959]),(0,[z1,z2,z3,z4,z17,z824]),(0,[z1,z2,z3,z4,z592,z17])],[(0,[z1,z2,z3,z4,z5,z960]),(0,[z2,z3,z4,z438,z17,z8]),(0,[z1,z2,z3,z4,z5,z961]),(0,[z1,z2,z181,z4,z5,z6]),(0,[z304,z1,z2,z3,z5,z235])],[(0,[z1,z2,z3,z4,z962,z8]),(0,[z1,z2,z3,z4,z5,z963]),(0,[z11,z1,z2,z964,z4,z5])],[(0,[z61,z38,z3,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z965]),(0,[z1,z2,z3,z4,z5,z966]),(0,[z267,z2,z3,z4,z5,z58])],[],[(0,[z1,z2,z3,z4,z967,z8]),(0,[z1,z2,z3,z4,z968,z8]),(0,[z1,z2,z3,z4,z17,z925]),(0,[z11,z1,z2,z14,z4,z17]),(0,[z23,z2,z3,z4,z5,z840]),(0,[z1,z2,z3,z4,z969,z8]),(0,[z1,z2,z3,z4,z5,z324]),(0,[z1,z2,z3,z970,z4,z5])],[(0,[z1,z2,z4,z17,z33,z6])],[(0,[z1,z2,z483,z4,z40,z8]),(0,[z2,z3,z4,z17,z665,z8]),(0,[z1,z2,z3,z484,z40,z8]),(0,[z1,z2,z403,z4,z5,z6]),(0,[z290,z1,z2,z12,z5,z324]),(0,[z1,z2,z3,z15,z5,z352]),(0,[z1,z2,z489,z4,z5,z6])],[(0,[z1,z2,z3,z4,z5,z859]),(0,[z1,z2,z14,z4,z5,z6])],[(0,[z1,z2,z3,z4,z971,z8]),(0,[z1,z2,z3,z972,z5,z8]),(0,[z1,z973,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z6]),(0,[z974,z1,z2,z3,z4,z5]),(0,[z515,z2,z3,z4,z40,z8]),(0,[z1,z2,z282,z4,z5,z859]),(0,[z206,z1,z2,z282,z4,z5]),(0,[z209,z1,z2,z4,z592,z5])],[(0,[z1,z2,z3,z904,z4,z5]),(0,[z11,z943,z2,z3,z4,z5])],[(0,[z169,z143,z294,z4,z5,z8]),(0,[z1,z2,z483,z4,z5,z975]),(0,[z1,z2,z4,z5,z33,z588])],[(0,[z976,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z321,z33])]],
   [[(0,[z11,z267,z2,z3,z29,z5]),(0,[z1,z2,z3,z4,z40,z977]),(0,[z216,z1,z2,z3,z15,z5])],[(0,[z1,z2,z3,z978,z4,z5]),(0,[z234,z2,z3,z4,z17,z8]),(0,[z48,z42,z2,z3,z4,z8]),(0,[z1,z2,z3,z944,z4,z8]),(0,[z979,z1,z2,z3,z5,z6])],[(0,[z102,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z40,z194])],[(0,[z1,z2,z3,z980,z5,z8]),(0,[z136,z2,z3,z27,z333,z8]),(0,[z1,z2,z3,z856,z5,z8]),(0,[z11,z1,z2,z3,z4,z251]),(0,[z1,z2,z3,z4,z5,z981]),(0,[z1,z2,z3,z4,z19,z233])],[(0,[z1,z2,z3,z882,z104,z5]),(0,[z1,z2,z3,z4,z982,z8]),(0,[z983,z2,z3,z4,z5,z8]),(0,[z1,z149,z3,z84,z5,z6]),(0,[z35,z1,z2,z3,z957,z8])],[(0,[z1,z2,z3,z4,z948,z8]),(0,[z1,z2,z3,z4,z984,z8]),(0,[z1,z2,z3,z4,z985,z8]),(0,[z35,z1,z2,z3,z173,z8]),(0,[z1,z2,z3,z4,z5,z986])],[(0,[z1,z987,z2,z3,z4,z5]),(0,[z150,z206,z1,z2,z3,z5])],[(0,[z1,z2,z3,z4,z988,z8]),(0,[z1,z2,z3,z4,z989,z8])],[(0,[z0,z2,z135,z4,z5,z33]),(0,[z1,z2,z3,z4,z40,z513]),(0,[z206,z1,z2,z3,z27,z5]),(0,[z161,z2,z3,z255,z5,z8])],[(0,[z1,z2,z990,z4,z5,z8]),(0,[z102,z2,z3,z4,z594,z8]),(0,[z1,z2,z3,z4,z991,z8]),(0,[z1,z2,z3,z4,z992,z8]),(0,[z993,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z5,z16,z796])],[(0,[z11,z1,z2,z3,z4,z369]),(0,[z85,z2,z3,z27,z5,z8]),(0,[z1,z42,z3,z4,z452,z8])],[(0,[z1,z2,z3,z4,z994,z8]),(0,[z1,z2,z3,z4,z141,z398]),(0,[z11,z1,z2,z3,z4,z594]),(0,[z11,z1,z995,z3,z4,z5])],[(0,[z1,z2,z996,z3,z4,z8]),(0,[z1,z629,z2,z4,z78,z8]),(0,[z997,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z5,z454]),(0,[z1,z2,z4,z422,z5,z6]),(0,[z35,z11,z1,z2,z3,z36])],[(0,[z1,z2,z3,z4,z5,z998]),(0,[z1,z2,z3,z170,z5,z158]),(0,[z1,z2,z3,z4,z5,z999]),(0,[z161,z2,z3,z29,z5,z243]),(0,[z1,z2,z3,z317,z111,z8]),(0,[z1000,z2,z3,z4,z5,z8])],[(0,[z169,z717,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1001]),(0,[z2,z3,z27,z116,z17,z8]),(0,[z1,z2,z3,z4,z5,z1002]),(0,[z1,z2,z3,z4,z5,z1003]),(0,[z35,z48,z2,z3,z36,z8])],[(0,[z1,z189,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z741]),(0,[z1,z2,z3,z4,z1004,z5])]],
   [[(0,[z1,z2,z294,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z1005]),(0,[z1,z2,z3,z104,z40,z8]),(0,[z1,z2,z3,z1006,z4,z5]),(0,[z290,z1,z2,z155,z12,z5])],[(0,[z1,z2,z14,z4,z5,z8]),(0,[z11,z1,z1007,z3,z4,z5])],[(0,[z1,z2,z3,z4,z40,z8]),(0,[z0,z2,z135,z4,z5,z144]),(0,[z1,z2,z3,z1008,z4,z5]),(0,[z1,z2,z3,z4,z17,z324]),(0,[z1,z2,z3,z155,z4,z40])],[(0,[z1,z2,z3,z4,z5,z1009])],[(0,[z161,z2,z3,z4,z17,z6]),(0,[z1,z2,z3,z317,z40,z8]),(0,[z102,z2,z3,z4,z5,z33])],[(0,[z1,z2,z3,z15,z4,z162]),(0,[z1,z2,z3,z4,z5,z154]),(0,[z2,z3,z4,z1010,z5,z8])],[(0,[z1,z2,z3,z4,z5,z975]),(0,[z1,z2,z3,z4,z171,z398]),(0,[z2,z3,z4,z525,z17,z8]),(0,[z1,z2,z4,z592,z5,z6])],[(0,[z979,z1,z2,z3,z5,z8])],[(0,[z1,z77,z2,z4,z571,z8]),(0,[z11,z1,z2,z3,z4,z969])],[(0,[z1,z2,z3,z4,z1011,z8]),(0,[z1,z2,z3,z4,z19,z467]),(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z2,z3,z56,z957,z8]),(0,[z1,z2,z81,z210,z4,z5])],[(0,[z169,z143,z3,z4,z40,z8]),(0,[z1,z516,z52,z4,z5,z8]),(0,[z209,z1,z2,z4,z40,z33]),(0,[z1,z2,z3,z15,z5,z624])],[(0,[z1,z1013,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z5,z1014]),(0,[z1,z2,z282,z32,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1015]),(0,[z1,z2,z3,z4,z5,z1016])],[(0,[z1,z2,z3,z4,z5,z1017])],[(0,[z11,z1,z2,z3,z27,z5]),(0,[z1,z2,z3,z4,z5,z1018]),(0,[z1,z2,z3,z4,z5,z311])],[(0,[z11,z1,z2,z3,z4,z171]),(0,[z1,z2,z3,z4,z5,z1019]),(0,[z1,z2,z3,z1020,z4,z5]),(1,[z1,z2,z4,z5,z763])]],
   [[(0,[z1,z2,z3,z4,z5,z1021]),(0,[z1,z479,z3,z4,z5,z33]),(0,[z1,z2,z3,z1022,z4,z5]),(0,[z1,z2,z3,z4,z74,z33]),(0,[z1,z2,z3,z4,z5,z71]),(0,[z1,z2,z3,z4,z5,z1023]),(0,[z1,z2,z3,z1024,z4,z5]),(0,[z1,z2,z3,z4,z592,z5]),(0,[z1025,z1,z2,z210,z4,z5]),(0,[z11,z1,z2,z3,z5,z796])],[(0,[z2,z3,z937,z4,z5,z8]),(0,[z1,z2,z902,z4,z5,z8])],[(0,[z1,z2,z294,z4,z5,z33]),(0,[z1,z2,z3,z4,z1026,z8]),(0,[z1,z2,z3,z15,z4,z17]),(0,[z68,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z15,z317,z5])],[(0,[z1,z2,z3,z4,z5,z1027]),(0,[z1,z189,z3,z104,z5,z8]),(0,[z1,z2,z3,z4,z5,z793]),(0,[z11,z1,z2,z3,z260,z5])],[(0,[z136,z2,z3,z27,z40,z8]),(0,[z1,z2,z3,z196,z4,z17]),(0,[z94,z1,z2,z3,z22,z8]),(0,[z206,z1,z2,z4,z12,z5])],[(0,[z1,z189,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1028]),(0,[z11,z1,z2,z3,z255,z5]),(0,[z1,z2,z3,z1029,z5,z8]),(0,[z1,z2,z3,z4,z1030,z8]),(0,[z35,z206,z1,z2,z3,z5]),(0,[z11,z1,z2,z14,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1031]),(0,[z308,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z1032]),(0,[z11,z102,z2,z3,z4,z5])],[],[(0,[z2,z3,z4,z27,z17,z8]),(0,[z1,z2,z3,z4,z17,z1002]),(0,[z1,z2,z210,z4,z40,z8]),(0,[z1,z42,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z5,z34]),(0,[z1,z77,z2,z4,z644,z8])],[(0,[z1,z2,z143,z210,z4,z5]),(0,[z11,z1,z2,z3,z192,z5])],[(0,[z1,z479,z3,z4,z5,z144]),(0,[z1,z2,z3,z4,z5,z1033]),(0,[z11,z1,z2,z3,z673,z5]),(0,[z1,z2,z3,z4,z123,z350]),(0,[z1,z2,z3,z4,z1034,z8]),(0,[z209,z1,z2,z4,z5,z13])],[(0,[z1,z2,z3,z4,z1035,z8]),(0,[z1,z2,z3,z15,z4,z70]),(0,[z1,z2,z3,z4,z5,z1036]),(0,[z1,z2,z3,z224,z4,z17]),(0,[z1,z2,z14,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z1037])],[(0,[z1,z1038,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z797,z8]),(0,[z1,z121,z2,z210,z4,z5])],[],[(0,[z1,z1039,z3,z4,z5,z8]),(0,[z646,z2,z3,z4,z5,z58]),(0,[z35,z1,z2,z3,z323,z8])],[(0,[z1,z2,z3,z4,z1040,z8]),(0,[z1,z2,z3,z4,z1041,z8]),(0,[z267,z2,z3,z29,z5,z8]),(0,[z1,z2,z3,z4,z17,z154]),(0,[z1,z2,z4,z650,z5,z6]),(0,[z1,z2,z726,z12,z5,z8]),(0,[z1,z2,z3,z4,z1012,z8])]],
   [[(0,[z1,z1042,z3,z4,z5,z8]),(0,[z136,z2,z3,z196,z27,z5]),(0,[z1,z1043,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1044])],[(0,[z1,z3,z4,z1045,z5,z8]),(0,[z11,z1,z2,z3,z4,z183]),(0,[z1,z2,z3,z4,z5,z76]),(0,[z1,z2,z210,z4,z5,z18]),(0,[z1,z2,z282,z32,z5,z8])],[(0,[z1,z2,z3,z4,z17,z31]),(0,[z1,z2,z1046,z4,z5,z8]),(0,[z290,z1,z2,z726,z5,z8])],[(0,[z61,z38,z3,z15,z4,z5]),(0,[z11,z1,z2,z3,z4,z129]),(0,[z1,z2,z3,z4,z5,z1047]),(0,[z1,z2,z3,z4,z8,z1048]),(0,[z267,z1,z2,z210,z4,z5])],[],[(0,[z1,z2,z3,z4,z1049,z8]),(0,[z1,z2,z1050,z4,z5,z8])],[(0,[z1,z2,z1051,z4,z5,z8]),(0,[z1,z2,z3,z484,z111,z8]),(0,[z1,z2,z3,z4,z5,z1052]),(0,[z1,z2,z3,z4,z5,z1053]),(0,[z1,z2,z3,z15,z496,z5])],[(0,[z1,z2,z294,z170,z5,z8]),(0,[z61,z38,z3,z4,z573,z8]),(0,[z1,z2,z3,z4,z5,z1054]),(0,[z290,z1,z2,z4,z592,z5]),(0,[z1,z2,z3,z15,z4,z892])],[(0,[z1,z2,z3,z1055,z5,z8]),(0,[z11,z1,z2,z3,z1056,z5]),(0,[z202,z2,z3,z4,z594,z8]),(0,[z1,z2,z3,z4,z17,z311]),(0,[z1,z2,z3,z4,z111,z6]),(0,[z1,z2,z3,z4,z1057,z8])],[(0,[z1,z2,z3,z15,z4,z24]),(0,[z1,z293,z3,z4,z5,z18])],[(0,[z1,z2,z3,z15,z63,z5]),(0,[z2,z3,z27,z339,z17,z8]),(0,[z1,z2,z3,z4,z17,z71]),(0,[z1,z2,z1058,z4,z5,z8]),(0,[z1,z20,z2,z210,z4,z5]),(0,[z1,z2,z3,z1059,z5,z8]),(0,[z1,z2,z361,z4,z5,z6])],[(0,[z1,z1060,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1061,z8])],[(0,[z1,z2,z3,z4,z1062,z8]),(0,[z1,z3,z804,z116,z5,z8]),(0,[z1,z2,z3,z37,z4,z5]),(0,[z1,z2,z21,z4,z90,z8]),(0,[z1,z2,z3,z4,z5,z1063])],[(0,[z1,z2,z3,z4,z573,z6]),(0,[z0,z479,z135,z4,z5,z8]),(0,[z1,z2,z26,z210,z4,z5]),(0,[z1,z2,z282,z37,z4,z5])],[(0,[z73,z2,z26,z4,z5,z6]),(0,[z1,z2,z285,z3,z4,z17])],[(0,[z1,z189,z3,z4,z17,z8]),(0,[z11,z1,z2,z14,z29,z5]),(0,[z95,z2,z3,z4,z17,z33]),(0,[z11,z1,z2,z3,z459,z5]),(0,[z1,z2,z3,z1064,z4,z5]),(0,[z11,z1,z2,z14,z15,z5])]],
   [[(0,[z2,z937,z135,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z1032]),(0,[z1,z2,z282,z4,z40,z6]),(0,[z1,z2,z3,z4,z1065,z8]),(0,[z1,z2,z210,z4,z5,z43]),(0,[z1,z2,z297,z4,z5,z6])],[(0,[z1,z2,z3,z4,z594,z71]),(0,[z80,z2,z3,z4,z40,z8]),(0,[z1,z2,z118,z4,z5,z6])],[(0,[z1,z2,z210,z27,z5,z8]),(0,[z1,z2,z421,z4,z40,z6]),(0,[z1,z2,z3,z4,z40,z130])],[(0,[z1,z2,z3,z1066,z4,z5])],[(1,[z717,z3,z4,z5,z8]),(0,[z717,z143,z3,z4,z5,z8]),(0,[z23,z2,z3,z4,z296,z166]),(0,[z1,z2,z1067,z3,z4,z5]),(0,[z1,z2,z3,z433,z5,z16])],[(0,[z1,z2,z3,z4,z1068,z8]),(0,[z1,z2,z3,z4,z1069,z8]),(0,[z11,z1,z2,z3,z4,z333]),(0,[z2,z3,z196,z4,z27,z17]),(0,[z419,z2,z3,z4,z5,z166]),(0,[z106,z2,z3,z4,z111,z58]),(0,[z1,z293,z3,z188,z4,z5]),(0,[z1,z2,z3,z15,z336,z5])],[(0,[z11,z1,z2,z3,z4,z573]),(0,[z1,z2,z3,z4,z397,z33]),(0,[z304,z1,z2,z3,z4,z17]),(0,[z1,z149,z3,z84,z5,z33]),(0,[z1,z2,z3,z4,z5,z1070])],[(0,[z1,z2,z3,z4,z162,z6]),(0,[z1,z2,z3,z4,z5,z1071]),(0,[z11,z1,z2,z3,z5,z518]),(0,[z1,z2,z1072,z210,z4,z5]),(0,[z1,z2,z3,z4,z1073,z8]),(0,[z1,z2,z3,z4,z19,z383])],[(0,[z1,z2,z481,z4,z5,z6]),(0,[z1,z527,z2,z3,z4,z295])],[(0,[z1,z2,z3,z1074,z5,z8]),(0,[z1,z2,z3,z4,z17,z138]),(0,[z11,z121,z2,z3,z4,z17])],[(0,[z73,z2,z26,z4,z5,z513]),(0,[z136,z11,z2,z3,z27,z5]),(0,[z1,z1043,z3,z4,z17,z8]),(0,[z1,z1075,z2,z3,z4,z5])],[(0,[z1,z2,z3,z343,z141,z8]),(0,[z1,z2,z3,z4,z17,z76]),(0,[z1,z2,z282,z32,z17,z8]),(0,[z48,z2,z3,z4,z5,z6])],[(0,[z106,z2,z3,z4,z40,z58]),(0,[z1,z2,z3,z4,z1076,z8]),(0,[z1,z2,z3,z4,z5,z1077])],[(0,[z1,z2,z483,z4,z5,z249])],[(0,[z1,z2,z3,z4,z111,z8]),(0,[z11,z1,z89,z52,z4,z5]),(0,[z1,z2,z3,z4,z5,z1078]),(0,[z1,z500,z2,z4,z5,z33]),(1,[z206,z1,z2,z12,z5]),(0,[z1,z2,z3,z4,z482,z93])],[(0,[z1,z2,z3,z4,z5,z1079]),(0,[z1,z2,z3,z1080,z4,z17]),(0,[z1,z2,z3,z1081,z4,z5]),(0,[z1,z2,z3,z4,z8,z1082]),(0,[z1,z2,z210,z32,z4,z5])]],
   [[(0,[z1,z2,z1083,z4,z5,z8]),(0,[z1,z2,z3,z484,z5,z58]),(0,[z1,z2,z3,z4,z5,z1084]),(0,[z1,z2,z574,z4,z5,z6]),(1,[z1,z2,z3,z957,z8]),(0,[z11,z1,z2,z895,z4,z5])],[(0,[z1,z2,z3,z196,z4,z5]),(0,[z1,z2,z3,z1085,z4,z5]),(0,[z160,z2,z3,z4,z5,z142])],[(0,[z2,z26,z937,z4,z5,z8]),(0,[z1,z2,z3,z1086,z4,z5]),(0,[z1,z2,z3,z4,z5,z1087]),(0,[z1,z2,z210,z37,z4,z5])],[(0,[z1,z2,z3,z4,z573,z8]),(0,[z1,z2,z210,z52,z4,z5])],[(0,[z1,z2,z1088,z4,z5,z8]),(0,[z73,z2,z26,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z730]),(0,[z1089,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1090,z8]),(0,[z1091,z2,z3,z4,z5,z8]),(0,[z366,z121,z2,z3,z4,z5])],[(0,[z2,z3,z4,z27,z17,z6]),(0,[z1,z89,z52,z4,z5,z138])],[(0,[z1,z2,z3,z343,z171,z8]),(0,[z161,z2,z3,z4,z17,z33]),(0,[z1,z2,z3,z4,z5,z1092]),(0,[z1,z2,z4,z12,z5,z6]),(0,[z1,z2,z3,z4,z5,z1093])],[(0,[z1,z2,z3,z1022,z343,z5]),(0,[z1,z2,z3,z4,z5,z1094]),(0,[z290,z1,z2,z12,z40,z8]),(0,[z1,z2,z3,z148,z4,z251]),(0,[z1,z2,z210,z4,z5,z16]),(0,[z1095,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z15,z5,z82])],[(0,[z1,z2,z3,z4,z5,z1096]),(0,[z1,z2,z3,z4,z40,z736]),(0,[z1,z2,z3,z4,z1097,z8]),(0,[z1,z2,z3,z224,z4,z5]),(0,[z1,z2,z3,z4,z5,z1098]),(0,[z247,z1,z2,z210,z4,z5])],[(0,[z1,z2,z3,z4,z1099,z8]),(0,[z390,z2,z3,z4,z17,z8]),(0,[z1100,z1,z2,z3,z4,z5]),(0,[z11,z1,z149,z3,z84,z5]),(0,[z1,z2,z1101,z4,z5,z8]),(0,[z1,z2,z210,z4,z5,z498])],[(0,[z1,z2,z294,z63,z5,z8]),(0,[z1,z2,z483,z4,z5,z1102]),(0,[z1,z1103,z2,z3,z4,z8]),(0,[z1104,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z5,z755]),(0,[z1,z2,z3,z4,z1105,z8])],[(0,[z1,z2,z3,z15,z4,z397]),(0,[z1,z2,z3,z4,z5,z1106])],[(0,[z1,z2,z3,z343,z5,z398]),(0,[z1,z2,z3,z4,z5,z1107]),(0,[z1,z2,z3,z4,z162,z8])],[(0,[z11,z1,z2,z210,z27,z5]),(0,[z1,z2,z3,z127,z339,z8]),(0,[z1,z2,z3,z726,z5,z8]),(0,[z1,z2,z3,z4,z187,z473])],[(0,[z1,z2,z3,z1108,z5,z8]),(0,[z1,z2,z3,z4,z1056,z5]),(0,[z2,z3,z4,z5,z840,z166]),(0,[z2,z3,z4,z1109,z5,z8]),(0,[z1,z2,z3,z127,z395,z8]),(0,[z1,z2,z3,z15,z563,z5]),(0,[z1,z2,z282,z726,z5,z8]),(0,[z35,z102,z2,z3,z36,z8])]],
   [[(0,[z1110,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z1111,z8]),(0,[z1,z2,z3,z4,z333,z33]),(0,[z1,z2,z3,z1112,z4,z5]),(0,[z92,z1,z2,z3,z4,z498]),(0,[z1,z2,z3,z4,z1113,z8])],[(0,[z48,z2,z3,z4,z5,z8]),(0,[z23,z2,z3,z4,z24,z166]),(0,[z1,z42,z3,z4,z43,z151])],[(0,[z1,z1114,z3,z4,z5,z8]),(0,[z1,z20,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z1115]),(0,[z92,z1,z2,z210,z4,z5])],[(0,[z1,z2,z1116,z3,z4,z5]),(0,[z1,z20,z81,z3,z4,z5])],[(0,[z0,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z40,z100])],[(0,[z1,z2,z3,z4,z5,z249]),(0,[z1,z2,z3,z1117,z4,z5]),(0,[z1,z2,z3,z197,z4,z88]),(0,[z1,z9,z2,z3,z224,z4]),(0,[z1,z2,z3,z4,z5,z1118]),(0,[z1,z2,z210,z15,z4,z5])],[(0,[z1,z2,z3,z4,z1119,z8]),(0,[z1,z2,z614,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1120])],[(0,[z1,z2,z3,z4,z369,z249]),(0,[z325,z2,z3,z4,z5,z166]),(0,[z1,z2,z3,z4,z5,z151])],[(0,[z404,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z10]),(0,[z1,z2,z3,z101,z4,z743])],[(0,[z1,z2,z3,z4,z5,z1121]),(0,[z1,z2,z3,z1122,z4,z5]),(0,[z1123,z1,z2,z3,z4,z5]),(0,[z1,z2,z21,z4,z90,z6])],[(0,[z1,z2,z3,z4,z5,z1124])],[(0,[z1,z2,z400,z4,z559,z8]),(0,[z1,z2,z285,z3,z4,z5]),(0,[z1,z647,z3,z4,z5,z99])],[(0,[z1,z2,z1125,z4,z5,z8]),(0,[z1126,z1,z2,z3,z4,z5]),(0,[z2,z3,z32,z27,z17,z8]),(0,[z11,z1,z2,z3,z139,z5]),(0,[z1,z2,z3,z4,z5,z1127]),(0,[z206,z1,z2,z3,z32,z5]),(0,[z1,z2,z210,z4,z5,z1128])],[(0,[z1,z2,z3,z4,z141,z6]),(0,[z2,z3,z4,z258,z17,z8]),(0,[z1,z2,z3,z1129,z4,z5])],[(0,[z73,z2,z26,z4,z17,z8]),(0,[z446,z2,z3,z4,z17,z8]),(0,[z1,z2,z4,z40,z33,z6]),(0,[z1,z2,z3,z1130,z4,z5]),(0,[z1,z2,z3,z101,z4,z498])],[(0,[z11,z95,z2,z3,z4,z17])]],
   [[(0,[z1,z2,z3,z4,z5,z1131]),(0,[z1,z2,z4,z12,z17,z6]),(0,[z1,z2,z3,z4,z5,z1132]),(0,[z11,z1,z2,z3,z5,z235]),(0,[z1,z248,z2,z210,z4,z5])],[(0,[z1,z2,z3,z4,z1133,z5]),(0,[z136,z2,z3,z15,z27,z5]),(0,[z1134,z1,z2,z3,z4,z5]),(0,[z1,z149,z3,z804,z5,z8]),(0,[z1,z2,z3,z4,z5,z1135])],[(0,[z1,z2,z294,z4,z5,z158]),(0,[z1,z2,z3,z4,z5,z1102]),(0,[z1,z2,z3,z4,z69,z249]),(0,[z1,z2,z3,z4,z1136,z8]),(0,[z1,z1137,z2,z3,z4,z5]),(0,[z1,z2,z3,z148,z27,z5]),(0,[z1,z3,z4,z5,z793,z8]),(0,[z1,z77,z2,z15,z4,z78]),(0,[z1138,z1,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z5,z1139]),(0,[z218,z2,z3,z27,z5,z8])],[(0,[z61,z717,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z55]),(0,[z1,z2,z1140,z3,z4,z8]),(0,[z1,z514,z3,z4,z5,z18]),(0,[z1,z2,z3,z4,z5,z1141])],[(0,[z1,z1142,z2,z3,z4,z5]),(0,[z11,z1,z86,z3,z4,z113]),(0,[z1,z2,z3,z5,z6,z875])],[(0,[z1,z2,z3,z63,z40,z8]),(0,[z11,z1,z2,z3,z301,z5]),(0,[z1,z2,z3,z4,z123,z233])],[(0,[z1,z2,z3,z1143,z5,z8]),(0,[z1,z149,z3,z84,z5,z280]),(0,[z1,z2,z3,z4,z5,z91])],[(0,[z1,z2,z3,z4,z171,z6]),(0,[z1,z2,z282,z4,z5,z91]),(0,[z1,z2,z3,z4,z5,z1144]),(0,[z1,z2,z210,z1145,z4,z5])],[(0,[z906,z1,z2,z3,z4,z5])],[(0,[z1,z2,z483,z15,z4,z5]),(0,[z1,z2,z3,z210,z4,z17])],[(0,[z1,z2,z3,z4,z183,z6]),(0,[z48,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z40,z243]),(0,[z1,z89,z52,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z1146]),(0,[z1,z2,z3,z4,z5,z1147]),(0,[z1,z2,z3,z4,z1148,z8]),(0,[z1,z1149,z2,z3,z4,z5])],[(0,[z1,z20,z3,z4,z17,z18]),(0,[z11,z1,z2,z3,z342,z5])],[],[(0,[z1,z479,z135,z4,z5,z8]),(0,[z1,z2,z210,z4,z5,z58]),(0,[z1,z89,z52,z4,z5,z154]),(0,[z1,z2,z3,z4,z5,z1150])],[(0,[z1,z2,z3,z15,z40,z16])]],
   [[(0,[z1,z2,z3,z1151,z5,z8]),(0,[z1152,z1,z2,z3,z4,z5]),(0,[z1,z2,z14,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z743])],[(0,[z1,z2,z3,z104,z141,z8]),(0,[z1,z2,z210,z135,z4,z5]),(0,[z1,z2,z3,z4,z40,z33]),(0,[z1,z2,z3,z4,z1153,z8]),(0,[z11,z1,z2,z3,z268,z5])],[(0,[z1,z373,z2,z3,z4,z17]),(0,[z1,z2,z3,z4,z17,z10]),(0,[z1,z2,z3,z15,z4,z1154]),(0,[z1,z2,z3,z468,z4,z482])],[(0,[z1,z2,z3,z4,z1155,z8]),(0,[z227,z38,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z141,z8]),(0,[z11,z1,z2,z3,z4,z74]),(0,[z209,z1,z2,z210,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1156])],[(0,[z1,z2,z3,z926,z4,z5]),(0,[z1,z2,z285,z3,z29,z5]),(0,[z1,z2,z3,z4,z17,z34]),(0,[z1,z77,z2,z4,z78,z311])],[(0,[z1,z2,z3,z15,z343,z5]),(0,[z180,z1,z3,z4,z5,z44]),(0,[z1,z2,z3,z4,z5,z1157])],[(0,[z1,z2,z3,z4,z1158,z8]),(0,[z1,z2,z3,z4,z153,z214])],[(0,[z11,z1,z2,z3,z4,z70]),(0,[z1,z2,z3,z4,z5,z1159]),(0,[z2,z3,z4,z5,z58,z840]),(0,[z263,z11,z1,z2,z3,z5]),(0,[z1138,z1,z2,z3,z5,z8]),(0,[z1,z1160,z2,z3,z4,z5])],[(0,[z1,z2,z3,z15,z4,z69]),(0,[z264,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z957,z8]),(0,[z1,z2,z210,z101,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1161]),(0,[z1,z2,z3,z4,z5,z796])],[(0,[z1,z2,z3,z4,z40,z144]),(0,[z1,z2,z3,z4,z5,z1162])],[(0,[z11,z1,z2,z3,z170,z5]),(0,[z1,z2,z3,z104,z171,z8]),(0,[z1,z2,z3,z4,z5,z1163]),(0,[z2,z3,z4,z17,z425,z8])],[(0,[z218,z2,z3,z27,z17,z8]),(0,[z304,z1,z2,z3,z29,z5]),(0,[z126,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z15,z5,z530])],[(0,[z1,z2,z3,z4,z40,z158]),(0,[z1,z490,z52,z4,z5,z8]),(0,[z1,z2,z3,z4,z171,z8]),(0,[z1,z1164,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z1165,z8]),(0,[z11,z1,z2,z3,z687,z5]),(0,[z1,z149,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z251,z6]),(0,[z1,z2,z21,z4,z90,z100])],[(1,[z1,z2,z210,z27,z5])]],
   [[(0,[z11,z1,z2,z3,z27,z40]),(0,[z11,z121,z2,z3,z29,z5]),(0,[z1,z2,z3,z4,z5,z1166])],[(0,[z1,z2,z3,z4,z183,z8]),(0,[z1,z2,z3,z4,z17,z91]),(0,[z1,z2,z3,z4,z5,z13])],[(0,[z1,z2,z3,z15,z4,z5]),(0,[z1,z2,z3,z4,z5,z788]),(0,[z1,z2,z3,z83,z4,z593]),(0,[z1,z2,z1167,z4,z5,z8]),(0,[z1,z2,z3,z4,z40,z386]),(0,[z1,z2,z3,z4,z592,z40]),(0,[z1,z2,z3,z4,z5,z1168]),(0,[z1,z2,z3,z4,z5,z1169])],[(0,[z1,z2,z3,z104,z5,z398]),(0,[z161,z2,z3,z4,z17,z243]),(0,[z218,z1,z2,z3,z672,z8]),(0,[z1,z2,z3,z4,z5,z828]),(0,[z23,z2,z3,z4,z5,z142]),(0,[z150,z1,z3,z116,z5,z6]),(0,[z1,z3,z4,z5,z44,z793])],[(0,[z2,z717,z3,z4,z5,z8]),(0,[z1,z189,z3,z4,z5,z33]),(0,[z1,z2,z3,z1170,z4,z5]),(1,[z1,z2,z3,z5,z796])],[(0,[z1,z2,z3,z4,z5,z398]),(0,[z1,z2,z3,z103,z484,z5]),(0,[z1,z9,z2,z285,z3,z4]),(0,[z1,z2,z3,z4,z5,z1171]),(0,[z1,z2,z4,z251,z12,z6]),(0,[z1,z2,z3,z4,z5,z60])],[(0,[z1,z2,z3,z170,z40,z8]),(0,[z308,z2,z135,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1172]),(0,[z1,z2,z3,z4,z1173,z5]),(0,[z1174,z2,z3,z4,z5,z8]),(0,[z11,z1,z1175,z3,z4,z5]),(0,[z11,z1,z2,z1101,z4,z5])],[(0,[z1,z2,z1176,z3,z4,z8]),(0,[z161,z2,z3,z4,z397,z8]),(0,[z2,z3,z4,z27,z17,z33]),(0,[z11,z1,z2,z14,z4,z40]),(0,[z1,z2,z3,z4,z1177,z8]),(0,[z1,z190,z59,z4,z5,z6]),(0,[z1,z2,z59,z210,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1178]),(0,[z1,z2,z410,z4,z5,z6]),(0,[z1,z2,z3,z1179,z5,z8])],[(0,[z73,z1,z2,z210,z4,z5]),(0,[z11,z1,z2,z3,z196,z5]),(0,[z1,z2,z3,z464,z339,z8]),(0,[z11,z1,z2,z3,z15,z17]),(0,[z2,z3,z4,z40,z450,z8]),(0,[z1,z2,z3,z1180,z4,z5])],[(0,[z169,z143,z3,z15,z4,z5]),(0,[z1,z2,z442,z4,z5,z33]),(0,[z565,z1,z2,z3,z4,z238])],[(0,[z1,z2,z3,z1181,z5,z8]),(0,[z1,z2,z3,z1182,z4,z5]),(0,[z11,z1,z2,z3,z509,z5])],[(0,[z1,z2,z3,z4,z5,z1183]),(0,[z1,z2,z3,z4,z1184,z8]),(0,[z1,z2,z3,z4,z5,z1185]),(0,[z1,z1175,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1186]),(0,[z23,z2,z3,z4,z5,z166])],[(0,[z1,z2,z3,z4,z5,z1187]),(0,[z1,z189,z3,z4,z5,z144]),(0,[z0,z2,z135,z4,z40,z8]),(0,[z1,z2,z210,z4,z27,z5]),(0,[z1,z2,z660,z4,z62,z8]),(0,[z1,z2,z3,z4,z296,z6]),(0,[z1,z2,z3,z4,z5,z1188]),(0,[z1,z2,z3,z4,z1041,z33]),(0,[z11,z1,z2,z3,z5,z690]),(0,[z1,z2,z3,z4,z1189,z8])],[]],
   [[(0,[z1,z2,z3,z4,z5,z1190]),(0,[z1,z2,z282,z32,z5,z33])],[(0,[z2,z3,z4,z40,z17,z8]),(0,[z1,z2,z1191,z3,z4,z5])],[(0,[z2,z3,z84,z27,z17,z8]),(0,[z11,z2,z3,z4,z27,z17]),(0,[z1,z2,z3,z4,z5,z1192])],[],[(0,[z202,z11,z2,z3,z27,z5]),(0,[z1,z2,z3,z4,z251,z8]),(0,[z1,z2,z3,z1193,z4,z5]),(0,[z206,z1,z2,z3,z56,z5])],[(0,[z1,z137,z3,z4,z545,z8]),(0,[z1194,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z253])],[(0,[z1195,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1196]),(0,[z1,z2,z3,z32,z433,z5]),(0,[z1,z2,z3,z4,z1197,z8])],[(0,[z1,z2,z3,z4,z1198,z8]),(0,[z1199,z2,z3,z4,z5,z8]),(0,[z1,z1200,z2,z210,z4,z5])],[(0,[z1,z38,z2,z210,z4,z5]),(0,[z161,z2,z3,z29,z40,z8]),(0,[z150,z1,z3,z116,z5,z8]),(0,[z1,z42,z3,z15,z4,z43]),(0,[z11,z1,z2,z3,z5,z98])],[(0,[z290,z11,z1,z2,z12,z5])],[(0,[z1,z2,z1201,z4,z5,z8]),(0,[z1,z2,z3,z4,z17,z13]),(0,[z1,z2,z3,z4,z1202,z8]),(0,[z11,z1,z2,z3,z423,z5]),(0,[z1,z2,z3,z1203,z4,z5]),(0,[z1,z2,z21,z4,z90,z33])],[(0,[z1,z38,z294,z4,z5,z8]),(0,[z206,z1,z2,z3,z4,z17]),(0,[z1,z2,z1167,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z1204])],[(0,[z1,z3,z4,z804,z5,z8]),(0,[z1,z2,z3,z4,z5,z1205]),(0,[z1,z20,z3,z4,z5,z793])],[(0,[z1,z2,z3,z37,z4,z40]),(0,[z1,z2,z3,z4,z40,z849]),(0,[z1,z42,z3,z4,z43,z6]),(0,[z1,z2,z3,z4,z5,z1206]),(0,[z2,z3,z4,z5,z1207,z6])],[(0,[z1,z2,z3,z4,z5,z1208]),(0,[z1,z2,z3,z4,z17,z398]),(0,[z1,z2,z3,z4,z17,z60]),(0,[z11,z1,z2,z21,z4,z90]),(0,[z1,z2,z3,z4,z1065,z33])]],
   [[(0,[z169,z143,z3,z4,z5,z249]),(0,[z1,z2,z3,z4,z5,z1209])],[(0,[z0,z189,z135,z4,z5,z8]),(0,[z1,z2,z282,z32,z5,z386]),(0,[z1,z1007,z3,z4,z5,z8]),(0,[z1,z2,z210,z4,z5,z93])],[(0,[z1,z2,z3,z4,z40,z280])],[(0,[z1,z2,z294,z4,z5,z998]),(0,[z136,z2,z3,z856,z5,z8]),(0,[z1,z2,z3,z4,z5,z1210]),(0,[z304,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z5,z796,z98])],[(0,[z1,z2,z483,z4,z369,z8]),(0,[z1,z2,z3,z4,z1211,z8]),(0,[z1,z1212,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z296,z8]),(0,[z11,z1,z2,z313,z3,z4]),(0,[z1,z2,z3,z155,z4,z251])],[(0,[z1,z2,z1213,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z162]),(0,[z267,z2,z3,z4,z17,z8])],[(0,[z1,z2,z3,z4,z369,z6]),(0,[z1,z479,z3,z4,z40,z8]),(0,[z73,z2,z26,z4,z5,z55]),(0,[z304,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z711,z8])],[(0,[z1,z2,z1214,z4,z5,z8]),(0,[z161,z2,z3,z29,z5,z71]),(0,[z1,z2,z210,z29,z5,z8]),(0,[z23,z2,z3,z4,z17,z166])],[(0,[z161,z2,z3,z4,z968,z8]),(0,[z1,z89,z52,z15,z4,z5])],[(0,[z1,z2,z3,z4,z1215,z8]),(0,[z1,z2,z549,z4,z5,z6]),(0,[z1,z2,z3,z4,z1216,z8])],[(0,[z1,z358,z3,z4,z5,z427])],[(0,[z1,z2,z3,z1217,z5,z8]),(0,[z1,z2,z3,z4,z24,z6]),(0,[z1,z2,z3,z4,z5,z1218]),(0,[z1,z2,z3,z4,z1076,z33])],[(0,[z1,z2,z1219,z4,z5,z8]),(0,[z290,z1,z2,z12,z5,z91])],[(0,[z1,z2,z3,z4,z111,z33]),(0,[z1,z2,z3,z4,z1220,z8]),(1,[z1,z3,z4,z803,z8]),(0,[z254,z1,z2,z210,z4,z5])],[(1,[z2,z3,z856,z5,z8]),(0,[z1,z2,z368,z4,z5,z6]),(0,[z290,z1,z2,z210,z4,z5]),(0,[z11,z872,z2,z3,z4,z5])],[(0,[z1,z2,z3,z1221,z5,z8]),(0,[z1,z2,z3,z343,z5,z6]),(0,[z1,z2,z3,z1080,z4,z5]),(0,[z11,z1,z2,z210,z4,z17]),(0,[z1,z2,z3,z4,z17,z253]),(0,[z2,z3,z355,z4,z40,z8]),(0,[z290,z1,z2,z15,z12,z5])]],
   [[(0,[z2,z3,z4,z17,z8,z544]),(0,[z1,z1222,z2,z3,z4,z5])],[(0,[z11,z1,z2,z483,z4,z5]),(0,[z1,z2,z27,z12,z5,z6]),(0,[z1,z2,z3,z15,z4,z40]),(0,[z1,z2,z3,z4,z1223,z8])],[(0,[z1,z2,z3,z4,z17,z249]),(0,[z1,z2,z3,z4,z573,z33]),(0,[z11,z1,z2,z3,z4,z17]),(0,[z11,z1,z2,z3,z317,z5]),(0,[z1,z2,z1224,z4,z5,z8]),(0,[z1,z86,z3,z4,z292,z8])],[(0,[z1,z2,z3,z1225,z4,z5]),(0,[z73,z2,z26,z4,z5,z33]),(0,[z1,z2,z3,z196,z4,z40]),(0,[z161,z2,z3,z856,z5,z8]),(0,[z150,z1,z3,z116,z17,z8]),(0,[z1,z2,z3,z4,z1226,z5])],[(0,[z1,z2,z3,z4,z17,z151]),(0,[z2,z3,z4,z5,z1207,z8]),(0,[z1,z42,z3,z4,z43,z8]),(0,[z1,z2,z210,z4,z1227,z5])],[(0,[z1,z190,z440,z4,z5,z8]),(0,[z1,z1228,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z1229]),(0,[z1,z2,z210,z4,z5,z233])],[(0,[z1,z2,z3,z4,z1230,z8]),(0,[z1,z2,z3,z4,z162,z243]),(0,[z1,z2,z3,z1231,z4,z5]),(0,[z1232,z2,z3,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1233]),(0,[z1,z2,z3,z4,z5,z1234]),(0,[z1,z2,z3,z101,z4,z93])],[(0,[z1,z2,z3,z1235,z5,z8]),(0,[z11,z1,z2,z3,z165,z5])],[(0,[z1,z2,z3,z4,z5,z1236])],[(0,[z1,z2,z3,z63,z5,z249]),(0,[z1,z2,z3,z1237,z4,z5]),(0,[z1,z2,z3,z4,z5,z1238]),(0,[z325,z2,z3,z4,z5,z120]),(0,[z11,z1,z2,z3,z4,z945])],[(0,[z1,z2,z3,z4,z17,z1209]),(0,[z1,z2,z3,z224,z4,z40]),(0,[z366,z1,z2,z210,z4,z5])],[(0,[z95,z2,z3,z15,z4,z17]),(0,[z1,z2,z3,z1239,z4,z5]),(0,[z1,z2,z3,z4,z5,z1240])],[(0,[z1,z2,z3,z4,z369,z8]),(0,[z0,z2,z135,z4,z141,z8]),(0,[z1,z2,z3,z317,z5,z8]),(0,[z1,z2,z3,z4,z5,z1241]),(0,[z1,z2,z3,z4,z162,z33]),(0,[z1,z2,z1242,z3,z4,z8])],[],[(0,[z11,z1,z2,z3,z583,z5]),(0,[z2,z3,z4,z40,z17,z6]),(0,[z1,z2,z3,z4,z40,z191]),(0,[z1,z2,z3,z4,z5,z1243]),(0,[z1,z2,z37,z4,z12,z5]),(0,[z1,z2,z3,z4,z233,z743])],[(0,[z1,z2,z1213,z4,z17,z8])]],
   [[(0,[z11,z2,z3,z27,z17,z8]),(0,[z1,z1244,z3,z4,z5,z8]),(0,[z48,z2,z3,z4,z5,z33])],[(0,[z1,z2,z3,z15,z4,z141]),(0,[z136,z373,z2,z3,z27,z5]),(0,[z1,z2,z3,z4,z24,z8])],[(0,[z1,z575,z2,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1245]),(0,[z1095,z2,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z1246,z8]),(0,[z1,z2,z3,z4,z33,z758])],[(0,[z169,z143,z3,z4,z369,z8]),(0,[z1,z2,z3,z15,z104,z5]),(1,[z1,z2,z726,z5,z8]),(0,[z256,z1,z2,z210,z4,z5])],[(0,[z1,z2,z3,z343,z5,z8]),(0,[z95,z2,z3,z4,z797,z8]),(0,[z566,z2,z3,z4,z17,z8]),(0,[z1,z2,z3,z4,z1247,z8]),(0,[z1,z2,z3,z4,z5,z1248]),(0,[z1,z1249,z2,z210,z4,z5])],[(0,[z2,z3,z29,z856,z5,z8]),(0,[z1,z2,z3,z4,z5,z1250]),(0,[z206,z1,z2,z3,z5,z98])],[(0,[z11,z1,z189,z3,z4,z5]),(0,[z1,z3,z1251,z4,z5,z8]),(0,[z1,z2,z210,z127,z4,z5])],[(0,[z2,z3,z4,z27,z397,z8]),(0,[z1,z2,z3,z27,z5,z243]),(0,[z150,z1,z3,z804,z5,z8]),(0,[z1252,z2,z3,z4,z5,z8]),(0,[z11,z1,z2,z3,z4,z781])],[(0,[z1,z2,z3,z4,z1253,z8]),(0,[z1,z516,z2,z4,z5,z6]),(0,[z11,z1,z2,z3,z4,z24]),(0,[z150,z11,z1,z3,z116,z5]),(0,[z1,z2,z313,z3,z4,z6]),(0,[z1,z2,z3,z168,z4,z363])],[(0,[z11,z1,z2,z3,z63,z5]),(0,[z1,z2,z3,z4,z1254,z5]),(0,[z206,z1,z2,z3,z37,z5])],[(0,[z61,z38,z3,z4,z5,z6]),(0,[z0,z2,z135,z15,z4,z5])],[(0,[z11,z1,z2,z3,z29,z17]),(0,[z1,z149,z3,z84,z40,z8]),(0,[z1,z2,z3,z4,z5,z1255]),(0,[z1,z2,z3,z4,z5,z1256])],[(0,[z1,z2,z285,z3,z4,z40]),(0,[z1257,z1,z2,z210,z4,z5])],[(0,[z1,z2,z3,z15,z4,z296]),(0,[z150,z1,z9,z3,z116,z8]),(0,[z1,z2,z3,z4,z5,z1258])],[(0,[z1,z2,z483,z4,z5,z6]),(0,[z1,z2,z1259,z4,z5,z8]),(0,[z1,z2,z3,z484,z5,z6])]],
   [[(0,[z1,z2,z3,z1056,z27,z5])],[(0,[z1,z2,z3,z4,z1260,z5]),(0,[z304,z1,z2,z3,z433,z5])],[(0,[z161,z2,z3,z15,z4,z17]),(0,[z1,z2,z372,z4,z5,z6])],[(0,[z180,z1,z3,z4,z17,z44]),(0,[z11,z1,z1114,z3,z4,z5]),(0,[z586,z1,z248,z3,z4,z5])],[(0,[z11,z1,z2,z294,z4,z5]),(0,[z1,z2,z3,z4,z1261,z8])],[(0,[z1,z2,z3,z4,z17,z1159]),(0,[z304,z1,z2,z3,z4,z40]),(0,[z2,z3,z4,z455,z40,z8]),(0,[z1,z2,z210,z4,z5,z90]),(0,[z1,z2,z3,z957,z36,z8])],[(0,[z304,z1,z2,z282,z32,z5]),(0,[z1,z215,z3,z4,z5,z177])],[(0,[z11,z61,z38,z3,z4,z5]),(1,[z2,z3,z4,z797,z8]),(0,[z1,z2,z3,z347,z4,z17]),(0,[z1,z2,z3,z4,z5,z1262]),(0,[z1,z2,z313,z3,z15,z4]),(0,[z1,z2,z313,z3,z148,z4])],[(0,[z1,z2,z3,z4,z1263,z8]),(0,[z1,z2,z3,z4,z5,z1264]),(0,[z11,z1,z2,z3,z4,z1073])],[(0,[z1,z2,z3,z170,z5,z249]),(0,[z11,z2,z3,z29,z27,z5]),(0,[z1,z2,z4,z17,z946,z8]),(0,[z2,z3,z4,z470,z40,z8]),(0,[z1,z2,z3,z1265,z4,z5]),(0,[z1,z2,z4,z711,z5,z8]),(0,[z11,z1,z2,z210,z5,z98])],[(0,[z11,z161,z2,z3,z4,z17]),(0,[z1,z2,z3,z4,z5,z1266]),(0,[z1,z2,z3,z4,z5,z1267]),(0,[z1,z2,z3,z210,z4,z5]),(0,[z1,z2,z3,z4,z1148,z33])],[(0,[z1,z2,z3,z1268,z4,z5]),(0,[z1,z1269,z3,z4,z5,z8]),(0,[z1,z2,z282,z210,z4,z5]),(0,[z1,z2,z1270,z3,z4,z5]),(0,[z35,z1,z2,z3,z347,z36])],[(0,[z0,z2,z937,z4,z5,z8]),(0,[z1,z2,z3,z433,z4,z17]),(0,[z106,z2,z3,z484,z5,z58]),(0,[z1,z2,z3,z4,z5,z1271])],[(0,[z1,z2,z3,z1272,z5,z8]),(0,[z102,z2,z3,z4,z40,z8]),(0,[z1,z2,z421,z210,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1273]),(0,[z2,z3,z4,z487,z40,z8]),(0,[z1,z2,z1251,z4,z5,z8])],[(0,[z11,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z343,z17,z8]),(0,[z1,z2,z313,z3,z4,z8])]],
   [[(0,[z1,z2,z3,z15,z484,z5]),(0,[z1,z1274,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z6,z1048]),(0,[z1,z2,z3,z4,z752,z8])],[(0,[z61,z38,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z141,z33]),(0,[z1,z373,z2,z3,z4,z5])],[(0,[z206,z1,z2,z3,z29,z5]),(0,[z1,z2,z1275,z4,z5,z8]),(0,[z206,z1,z2,z3,z15,z5]),(0,[z1,z2,z3,z15,z663,z5])],[(0,[z161,z2,z3,z29,z162,z8]),(0,[z1,z2,z3,z4,z5,z1276]),(0,[z1,z2,z3,z5,z957,z8])],[(0,[z1,z2,z483,z4,z5,z8]),(0,[z1,z2,z3,z1277,z5,z8]),(0,[z1,z2,z3,z4,z1278,z8]),(0,[z1,z2,z3,z104,z5,z6]),(0,[z1,z2,z3,z484,z5,z8]),(0,[z1,z2,z4,z5,z950,z8]),(0,[z1,z2,z3,z1279,z5,z8]),(0,[z150,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z1280,z8])],[(0,[z1,z1281,z2,z210,z4,z5])],[(0,[z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1154,z8]),(0,[z1,z2,z3,z4,z5,z1282]),(0,[z1,z2,z210,z4,z56,z5])],[(0,[z73,z2,z26,z4,z74,z8]),(0,[z1,z2,z3,z4,z5,z1283]),(0,[z1,z2,z1284,z4,z5,z8]),(0,[z1,z2,z3,z127,z56,z6])],[(0,[z1,z2,z3,z317,z5,z6])],[(0,[z1,z2,z3,z4,z1285,z8]),(0,[z161,z2,z3,z4,z17,z71]),(0,[z1,z2,z374,z4,z5,z6]),(0,[z48,z2,z3,z4,z56,z8])],[(0,[z1,z2,z294,z4,z40,z8]),(0,[z1286,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z977]),(0,[z390,z2,z3,z4,z5,z166]),(0,[z1,z2,z282,z496,z5,z8])],[(0,[z1,z2,z3,z4,z141,z144]),(0,[z11,z1,z2,z3,z4,z397]),(0,[z2,z3,z460,z4,z17,z8])],[(0,[z169,z143,z483,z4,z5,z8]),(0,[z1,z2,z3,z4,z171,z33]),(0,[z1,z2,z3,z4,z40,z324]),(0,[z1,z2,z3,z4,z1287,z8]),(0,[z1,z2,z3,z4,z1288,z8]),(0,[z1,z2,z3,z4,z5,z194])],[(0,[z61,z38,z3,z4,z70,z8]),(0,[z1,z2,z3,z4,z5,z1289]),(0,[z1290,z1,z2,z3,z5,z8]),(0,[z1,z2,z4,z5,z33,z6]),(0,[z1,z2,z3,z127,z56,z194])],[(0,[z209,z1,z2,z4,z5,z763]),(0,[z1,z2,z3,z15,z127,z56])]],
   [[(0,[z1,z2,z3,z1291,z5,z8]),(0,[z1,z2,z3,z4,z183,z33]),(0,[z696,z2,z3,z4,z40,z8]),(0,[z1,z86,z3,z4,z803,z8]),(0,[z1,z2,z210,z210,z4,z5])],[],[(0,[z1,z2,z483,z4,z69,z8]),(0,[z1,z2,z3,z4,z5,z1292]),(0,[z150,z1,z3,z15,z116,z5])],[(0,[z1,z2,z3,z4,z5,z513]),(0,[z1,z2,z3,z1293,z5,z8]),(0,[z23,z121,z2,z3,z4,z5]),(0,[z1,z2,z148,z210,z4,z5]),(0,[z1,z2,z3,z4,z5,z1294]),(0,[z1,z1295,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z69,z6]),(0,[z1,z2,z3,z4,z70,z6]),(0,[z1,z479,z26,z4,z5,z8]),(0,[z1,z1296,z3,z4,z5,z8]),(0,[z1,z2,z3,z1297,z5,z8]),(0,[z1,z2,z3,z210,z29,z5]),(0,[z1,z2,z3,z4,z17,z1266]),(0,[z106,z2,z3,z4,z5,z58]),(0,[z1,z2,z210,z4,z5,z36])],[(0,[z1,z2,z3,z4,z5,z1298]),(0,[z1,z2,z3,z4,z5,z1299]),(0,[z1,z2,z4,z560,z5,z6]),(0,[z1,z2,z964,z4,z5,z8])],[(0,[z1,z2,z877,z4,z5,z8]),(0,[z11,z1,z2,z3,z17,z98]),(0,[z202,z2,z3,z4,z40,z6]),(0,[z106,z2,z3,z317,z5,z58]),(0,[z1,z2,z3,z4,z1300,z8]),(0,[z1,z2,z3,z777,z5,z8]),(0,[z11,z1,z2,z210,z15,z5])],[(0,[z1,z2,z3,z4,z171,z144]),(0,[z1,z2,z3,z4,z5,z1301])],[(0,[z1,z2,z3,z4,z1302,z8])],[(0,[z11,z1,z2,z3,z29,z5]),(0,[z136,z2,z3,z27,z5,z6]),(0,[z1,z2,z3,z4,z5,z1303]),(0,[z11,z1,z2,z3,z15,z5]),(0,[z801,z2,z3,z15,z4,z5])],[(0,[z2,z3,z4,z501,z17,z8]),(0,[z11,z1,z2,z1058,z4,z5])],[(0,[z61,z38,z3,z4,z17,z8]),(0,[z1,z2,z3,z104,z5,z8]),(0,[z150,z1,z3,z224,z116,z5])],[(0,[z1,z2,z4,z571,z5,z6]),(0,[z1,z77,z2,z4,z78,z253])],[(0,[z1,z2,z3,z4,z5,z8]),(0,[z2,z3,z4,z968,z17,z8]),(0,[z1,z3,z4,z803,z43,z8]),(0,[z1,z2,z3,z4,z803,z8]),(0,[z1,z2,z210,z4,z5,z6])],[(0,[z1,z2,z3,z127,z56,z8])],[(0,[z1,z2,z483,z4,z17,z8]),(0,[z1,z2,z3,z4,z5,z1304]),(0,[z1,z2,z3,z484,z17,z8]),(0,[z1,z9,z2,z3,z4,z6]),(0,[z290,z1,z2,z12,z5,z8]),(0,[z1,z2,z589,z4,z5,z33])]],
   [[(0,[z1305,z1,z2,z3,z4,z5]),(0,[z1,z51,z3,z84,z5,z8]),(0,[z2,z3,z4,z40,z17,z33])],[(0,[z1,z2,z3,z4,z5,z1306]),(0,[z1,z2,z3,z4,z1307,z8]),(0,[z1,z2,z3,z4,z5,z1308]),(0,[z1,z2,z3,z4,z17,z6])],[(0,[z1,z2,z1309,z3,z4,z5]),(0,[z2,z556,z3,z4,z40,z8])],[(0,[z1,z2,z3,z4,z5,z1310]),(0,[z1,z2,z3,z4,z251,z33])],[(0,[z1,z2,z1311,z4,z5,z8]),(0,[z1,z2,z3,z4,z5,z1312]),(0,[z1,z2,z3,z4,z619,z233]),(0,[z35,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z347,z4,z5]),(0,[z11,z1,z2,z867,z4,z5])],[(0,[z169,z143,z3,z4,z5,z8]),(0,[z1,z2,z3,z1313,z5,z8]),(0,[z209,z1,z2,z4,z5,z33])],[(0,[z1,z2,z3,z4,z1314,z8]),(0,[z1,z995,z3,z4,z5,z8]),(0,[z2,z3,z4,z17,z22,z8]),(0,[z1,z2,z3,z148,z4,z17]),(0,[z1,z2,z14,z4,z40,z8]),(0,[z1,z2,z3,z4,z5,z1315])],[(0,[z1,z2,z3,z4,z17,z194])],[(0,[z1,z2,z3,z1316,z4,z5]),(0,[z1,z2,z3,z4,z594,z6]),(0,[z150,z1,z3,z116,z5,z33]),(0,[z1,z2,z3,z4,z5,z1317])],[(0,[z1,z2,z1219,z4,z17,z8]),(0,[z206,z1,z2,z210,z4,z5]),(0,[z1,z2,z3,z4,z1318,z8])],[(0,[z1,z2,z3,z4,z69,z8]),(0,[z1,z2,z3,z4,z70,z8]),(0,[z0,z2,z135,z4,z171,z8]),(0,[z1,z2,z3,z4,z40,z154]),(0,[z1,z2,z3,z15,z4,z111]),(0,[z1,z2,z3,z4,z1319,z8]),(0,[z1,z2,z3,z4,z1320,z8]),(0,[z1321,z1,z2,z3,z4,z5])],[],[(0,[z1,z2,z3,z5,z908,z8]),(0,[z1322,z1,z2,z3,z4,z5]),(0,[z202,z2,z3,z4,z40,z8]),(0,[z206,z1,z2,z3,z4,z5]),(0,[z11,z1,z2,z3,z5,z406]),(0,[z1,z2,z3,z15,z4,z738])],[(0,[z1,z2,z3,z4,z17,z513]),(0,[z1,z2,z3,z4,z40,z31])],[(0,[z1,z2,z3,z4,z1323,z8]),(0,[z1,z2,z3,z4,z5,z1324]),(0,[z150,z1,z285,z3,z116,z5]),(0,[z1,z2,z3,z4,z5,z1325]),(0,[z1,z2,z3,z4,z5,z1326])],[(0,[z1,z2,z3,z4,z5,z1327]),(0,[z136,z2,z3,z27,z5,z8]),(0,[z1,z2,z210,z4,z113,z5]),(0,[z209,z1,z2,z148,z4,z5])]],
   [[(0,[z1,z2,z3,z4,z5,z1328]),(0,[z1,z2,z210,z4,z116,z5])],[(0,[z1,z2,z3,z1329,z4,z5]),(0,[z0,z2,z135,z4,z5,z398]),(0,[z73,z2,z937,z4,z5,z8])],[(0,[z169,z143,z3,z4,z69,z8]),(0,[z1,z1330,z3,z4,z5,z8])],[(0,[z1,z2,z3,z4,z40,z311]),(0,[z1,z2,z3,z4,z296,z33]),(0,[z1,z89,z1251,z4,z5,z8]),(0,[z1,z2,z3,z4,z1331,z8]),(0,[z1,z2,z210,z4,z5,z8])],[(0,[z547,z2,z3,z4,z17,z8]),(0,[z1,z601,z2,z4,z571,z8]),(0,[z1,z2,z3,z4,z40,z1019]),(0,[z1,z2,z3,z4,z5,z840]),(0,[z331,z2,z3,z4,z342,z5])],[(0,[z1,z2,z3,z104,z17,z8]),(0,[z1,z2,z3,z4,z40,z71]),(0,[z1,z9,z2,z3,z4,z8]),(0,[z1,z2,z306,z4,z5,z33]),(0,[z565,z1,z2,z210,z4,z5])],[(0,[z11,z1,z2,z3,z343,z5]),(0,[z1,z2,z4,z571,z17,z6])],[(0,[z1,z2,z3,z4,z17,z8]),(0,[z1,z479,z3,z4,z141,z8]),(0,[z1,z2,z3,z1332,z5,z8]),(0,[z1,z3,z84,z804,z5,z8])],[(0,[z1,z2,z3,z4,z5,z1333]),(0,[z1,z616,z3,z4,z278,z8]),(0,[z1,z2,z3,z1334,z5,z6]),(0,[z1,z2,z4,z5,z6,z287]),(0,[z1,z2,z3,z4,z1215,z33]),(0,[z35,z1,z2,z3,z36,z8])],[(0,[z11,z1,z2,z3,z4,z69]),(0,[z1,z2,z3,z317,z17,z8]),(0,[z1335,z2,z3,z4,z5,z8]),(0,[z1,z2,z210,z4,z5,z98])],[(0,[z169,z1,z2,z210,z4,z5]),(0,[z1,z189,z3,z4,z40,z8]),(0,[z11,z1,z2,z3,z560,z5]),(0,[z102,z2,z3,z15,z4,z5])],[(0,[z1,z2,z3,z4,z5,z1336]),(0,[z2,z3,z15,z4,z27,z17]),(0,[z1,z2,z1337,z3,z4,z8]),(0,[z1,z1251,z52,z4,z5,z8]),(0,[z1,z2,z506,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z1338]),(0,[z1,z2,z210,z4,z5,z44])],[(1,[z1,z2,z4,z711,z8]),(0,[z1,z2,z21,z79,z4,z8]),(0,[z1,z2,z3,z4,z1339,z8])],[(0,[z1,z2,z937,z4,z5,z8]),(0,[z1,z1340,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z594,z8])],[(0,[z169,z143,z3,z4,z17,z8]),(0,[z209,z1,z2,z4,z17,z33]),(0,[z11,z1,z2,z210,z4,z5])]],
   [[(0,[z1,z2,z3,z805,z63,z5]),(0,[z1,z2,z3,z63,z369,z8]),(0,[z2,z3,z4,z17,z640,z8]),(0,[z1,z2,z3,z4,z5,z1341]),(0,[z1,z2,z3,z127,z208,z8])],[(0,[z11,z1,z2,z3,z104,z5]),(0,[z11,z161,z2,z3,z29,z5]),(0,[z1,z77,z2,z4,z78,z8])],[(0,[z1,z2,z3,z4,z5,z1342]),(0,[z1,z479,z3,z4,z171,z8]),(0,[z1,z2,z3,z4,z1343,z8]),(0,[z1,z2,z3,z1344,z5,z8]),(0,[z1,z149,z3,z84,z5,z10])],[(0,[z1,z2,z3,z4,z5,z1345]),(1,[z1,z2,z210,z4,z17]),(0,[z1,z42,z3,z4,z43,z33]),(0,[z1,z2,z3,z4,z1346,z8])],[(0,[z1,z2,z3,z4,z40,z138]),(0,[z1,z2,z3,z4,z5,z1347]),(0,[z1,z2,z3,z4,z5,z1348]),(0,[z1,z2,z3,z4,z5,z1349])],[(0,[z2,z3,z4,z583,z17,z8])],[(0,[z1,z2,z483,z170,z5,z8]),(0,[z1,z479,z3,z15,z4,z5]),(0,[z1,z1350,z3,z4,z5,z8]),(0,[z202,z2,z3,z4,z797,z8]),(0,[z1,z2,z3,z4,z40,z76]),(0,[z1,z2,z3,z4,z1351,z8]),(0,[z1,z2,z282,z32,z40,z8]),(0,[z1,z2,z357,z4,z5,z33])],[(0,[z1,z2,z3,z4,z1352,z8]),(0,[z1,z1353,z2,z3,z4,z8])],[(0,[z1,z2,z294,z15,z4,z5]),(0,[z1,z2,z4,z823,z5,z8]),(0,[z772,z1,z2,z3,z4,z5])],[(0,[z1,z479,z3,z4,z5,z398]),(0,[z789,z1,z2,z3,z4,z5]),(0,[z136,z2,z3,z27,z17,z8]),(0,[z1,z3,z4,z5,z956,z8]),(0,[z1,z2,z181,z37,z4,z5])],[],[(0,[z1,z2,z3,z4,z369,z33]),(0,[z1,z1354,z3,z4,z5,z8]),(0,[z1,z2,z3,z317,z5,z33]),(0,[z1,z2,z282,z4,z5,z6]),(0,[z11,z1091,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z40,z1054]),(0,[z1,z2,z3,z15,z4,z321]),(0,[z290,z1,z2,z12,z5,z6]),(0,[z1,z2,z37,z4,z592,z5]),(0,[z1355,z1,z2,z3,z4,z5]),(0,[z346,z2,z3,z4,z5,z305])],[(0,[z1,z2,z210,z4,z17,z8]),(0,[z1,z2,z421,z4,z5,z6]),(0,[z1,z2,z3,z4,z5,z130]),(0,[z1,z2,z1356,z210,z4,z5]),(0,[z1,z2,z3,z4,z949,z8])],[(0,[z1,z2,z3,z1334,z5,z8]),(0,[z1,z2,z507,z4,z5,z33]),(0,[z1,z2,z3,z4,z5,z1357]),(0,[z1,z2,z3,z4,z5,z1358]),(0,[z1,z2,z3,z127,z56,z130])],[(0,[z1,z2,z3,z4,z1359,z8]),(0,[z1,z2,z3,z317,z129,z8]),(0,[z1,z2,z1360,z3,z4,z5]),(0,[z1,z2,z1361,z210,z4,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 494).take 496) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 990).take 485) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1475).take 45) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1520)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [494, 496, 485, 45] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 109).take 114).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 223).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 320).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 424).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [109, 114, 97, 104, 88] = true :=
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

end PEqualNP.Outside.L_meta_40323

theorem PEqualNP.Outside.L_meta_40323 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276153536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276153536) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40323.solve