import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39879

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
  Nat.testBit (4276676840 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0018b14590e22e25#64 ++ 0x0000c58a2c871171#64 ++ 0x8039f3cfb1e67e7e#64 ++ 0xec01cf9e7d8f33f3#64 : BitVec 256),
   (0x00c2549296289686#64 ++ 0x000612a494b144b4#64 ++ 0xa1c67cf3de399f9d#64 ++ 0xfd0e33e79ef1ccfc#64 : BitVec 256),
   (0x8e050a2860154148#64 ++ 0x047028514300aa0a#64 ++ 0xde078f3c603fe3fb#64 ++ 0xf6f03c79e301ff1f#64 : BitVec 256),
   (0x37680fc06b41f810#64 ++ 0x09bb407e035a0fc0#64 ++ 0xfff80fc07fc1fc17#64 ++ 0xdfffc07e03fe0fe0#64 : BitVec 256),
   (0x5bb7f0007dbe0000#64 ++ 0x12ddbf8003edf000#64 ++ 0x7ffff0007ffe000f#64 ++ 0xdbffff8003fff000#64 : BitVec 256),
   (0x7dffefff00000000#64 ++ 0x23efff7ff8000000#64 ++ 0x7fffffff8000001f#64 ++ 0xa3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [0, 1]⟩, ⟨.and, [3, 7]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [2, 9]⟩, ⟨.and, [8, 12]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039f3cfb1e67e7e 0xec01cf9e7d8f33f3

def z1 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67cf3de399f9d 0xfd0e33e79ef1ccfc

def z2 : W := mkw 0x00d2f49796aa96a7 0x000697a4bcb554b5 0xa1c7fcffde3f9ffd 0xfd0e3fe7fef1fcff

def z3 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80fc07fc1fc17 0xdfffc07e03fe0fe0

def z4 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0007ffe000f 0xdbffff8003fff000

def z5 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffff8000001f 0xa3fffffffc000000

def z6 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde078f3c603fe3fb 0xf6f03c79e301ff1f

def z7 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c67cf3de199d85 0x190e33e79ef0ccec

def z8 : W := mkw 0x7dffffff90e22e25 0x23effffffc871171 0x7fffffff91c01c1f 0xabfffffffc8e00e0

def z9 : W := mkw 0x4815a00000960000 0x1240ad000004b000 0x0001800000060000 0x00000c0000003000

def z10 : W := mkw 0x0200000060000000 0x0010000003000000 0x5e00000060000003 0xd2f0000003000000

def z11 : W := mkw 0x1320000069000000 0x0099000003480000 0x7ff800007fc00007 0xdbffc00003fe0000

def z12 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80000fc00001fc10 0x0400007e00000fe0

def z13 : W := mkw 0xdbb7f0007dbf4148 0x16ddbf8003edfa0a 0xfffff0007fffe3ef 0xdfffff8003ffff1f

def z14 : W := mkw 0x0000100090e22e25 0x0000008004871171 0x8000000031e67e60 0x4c000000018f33f3

def z15 : W := mkw 0x0000000000000000 0x0000000000000000 0x80060c3040398399 0xf40030618201cc1c

def z16 : W := mkw 0x8e1dbb6df0f76f6d 0x0470eddb6f87bb7b 0xde39f3cfb1e67e7e 0xeef1cf9e7d8f33f3

def z17 : W := mkw 0x0000003f00000000 0x20000001f8000000 0x0000003f80000000 0x20000001fc000000

def z18 : W := mkw 0x0018a14500000000 0x0000c50a28000000 0x0039f3cf8000001e 0xa001cf9e7c000000

def z19 : W := mkw 0x020010007dbe0000 0x1010008003edf000 0x000000007ffe0000 0x5800000003fff000

def z20 : W := mkw 0x35680fc000000000 0x01ab407e00000000 0x7ff80fc000000017 0x83ffc07e00000000

def z21 : W := mkw 0x0000100090200604 0x0000008004810030 0x800070c390201e1c 0xec0003861c8100f0

def z22 : W := mkw 0x0000100010a20000 0x0000008000851000 0x0000000031e60000 0x48000000018f3000

def z23 : W := mkw 0x1328014069402800 0x0099400a034a0140 0xfff803c07fc07c17 0xdfffc01e03fe03e0

def z24 : W := mkw 0x0040049282009686 0x00020024941004b4 0x80000cf380019f90 0x240000679c000cfc

def z25 : W := mkw 0x4897f03f94280686 0x2244bf81fca14034 0x0007f03f80380388 0x20003f81fc01c01c

def z26 : W := mkw 0x8e051a28f035474c 0x047028d14781aa3a 0xde07fffff03fffff 0xfef03fffff81ffff

def z27 : W := mkw 0x0000100094280686 0x0000008004a14034 0x0000000000380380 0x000000000001c01c

def z28 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff803c03fc07c06 0x0bffc01e01fe03e0

def z29 : W := mkw 0x8c050a2800014148 0x0460285140000a0a 0xde078f3c0001e3fb 0xa6f03c79e0000f1f

def z30 : W := mkw 0x0008014580402e25 0x0000400a2c020171 0x800003cf80007e70 0x2400001e7c0003f3

def z31 : W := mkw 0x4897f03f90a20625 0x2244bf81fc851031 0x0007f03f80260268 0x20003f81fc013013

def z32 : W := mkw 0x0040048000000000 0x0002002400000000 0x21c00cc000000015 0x810e006600000000

def z33 : W := mkw 0x2458bfff90e22e25 0x2122c5fffc871171 0x8039ffffb1e67e7e 0xec01cffffd8f33f3

def z34 : W := mkw 0x0c050a2800000000 0x0060285140000000 0x5e078f3c0000001b 0xa2f03c79e0000000

def z35 : W := mkw 0x71fae5d700000000 0x238fd72eb8000000 0x21f870c380000004 0x010fc3861c000000

def z36 : W := mkw 0x00daf5d796eabea7 0x0006d7aebcb755f5 0xa1ffffffffffffff 0xfd0fffffffffffff

def z37 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7fc7f0004e3e0009 0x13fe3f800271f000

def z38 : W := mkw 0x3778bfc5fbe3fe35 0x09bbc5fe2fdf1ff1 0xfff9ffcfffe7fe7f 0xffffcffe7fff3ff3

def z39 : W := mkw 0xbf6d0fe86b55f958 0x0dfb687f435aafca 0xffff8ffc7fffffff 0xfffffc7fe3ffffff

def z40 : W := mkw 0x7fffffff7ffff810 0x3bfffffffbffffc0 0xfffffffffffffc1f 0xffffffffffffffe0

def z41 : W := mkw 0x020000006b41f810 0x08100000035a0fc0 0x800000007fc1fc00 0x5c00000003fe0fe0

def z42 : W := mkw 0xffffefff60154148 0x27ffff7ffb00aa0a 0xffffffffe03fe3ff 0xf7ffffffff01ff1f

def z43 : W := mkw 0x17200a0069014000 0x00b9005003480a00 0xfff80f007fc1e017 0xdfffc07803fe0f00

def z44 : W := mkw 0x4887403a00000000 0x22443a01d0000000 0x0006003000000000 0x0000300180000000

def z45 : W := mkw 0x0200000069960000 0x10100000034cb000 0x0000000021c60000 0x00000000010e3000

def z46 : W := mkw 0x7d3dab6d00000000 0x23e9ed5b68000000 0x5e39830c00000002 0x02f1cc1860000000

def z47 : W := mkw 0x7fffefff69000000 0x23ffff7ffb480000 0x7fffffffffc0001f 0xfbfffffffffe0000

def z48 : W := mkw 0x8200000060154148 0x041000000300aa0a 0x80000000603fe3e0 0x540000000301ff1f

def z49 : W := mkw 0x0018a14500000000 0x0000c50a28000000 0x8039f3cfa026627e 0xe401cf9e7d013313

def z50 : W := mkw 0x02001000ff69fe96 0x0810008007fb4ff4 0x800000007ff9ff80 0x5c00000003ffcffc

def z51 : W := mkw 0x37ea5fd2ff69fe96 0x09bf52fe97fb4ff4 0xfffe7ff3fff9ff9f 0xfffff3ff9fffcffc

def z52 : W := mkw 0x00c2449286089686 0x00061224943044b4 0xa1c60cf3ce199f91 0x350e30679e70ccfc

def z53 : W := mkw 0x0c050a2800000000 0x0060285140000000 0x5e01830c00000002 0x02f00c1860000000

def z54 : W := mkw 0x489ff14594fe2e25 0x1244ff8a2ca7f171 0x803ff3cfb1fe7e7e 0xec01ff9e7d8ff3f3

def z55 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c67c33ce398389 0x310e33e19e71cc1c

def z56 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x003870c391c01c04 0x0801c3861c8e00e0

def z57 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e060c3040198181 0x12f030618200cc0c

def z58 : W := mkw 0x8e051a28f63dd7ce 0x047028d147b1eebe 0xde078f3c7e3ffffb 0xfef03c79e3f1ffff

def z59 : W := mkw 0x06000a0060014000 0x0030005003000a00 0xde000f006001e013 0xd6f0007803000f00

def z60 : W := mkw 0x316805c00b40b810 0x098b402e005a05c0 0x21f800c01fc01c04 0x090fc00600fe00e0

def z61 : W := mkw 0x24400eba00000000 0x21220075d0000000 0x00000c3000000000 0x0000006180000000

def z62 : W := mkw 0x7dffffff96289686 0x23effffffcb144b4 0xffffffffde399f9f 0xfffffffffef1ccfc

def z63 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffffc039839f 0xf7fffffffe01cc1c

def z64 : W := mkw 0x37600e806b01d010 0x09bb007403580e80 0x7fc00c004e018001 0x13fe006002700c00

def z65 : W := mkw 0x8ec75ebaf63dd7ce 0x04763af5d7b1eebe 0xffc67cf3de399f9d 0xfffe33e79ef1ccfc

def z66 : W := mkw 0x13e25492ff289686 0x009f12a497f944b4 0xfffe7cf3fff99f9f 0xfffff3e79fffccfc

def z67 : W := mkw 0x7fe74e806f1dd010 0x1bff3a740378ee80 0x7fc60c004e198001 0x13fe30600270cc00

def z68 : W := mkw 0x84000a2800014148 0x0420005140000a0a 0x80000f3c0001e3f0 0x24000079e0000f1f

def z69 : W := mkw 0x5b35b00079b60000 0x12d9ad8003cdb000 0x5e39f00031e6000e 0xcaf1cf80018f3000

def z70 : W := mkw 0x1330b00079a20000 0x0099858003cd1000 0x7ff9f0007fe6000f 0xdbffcf8003ff3000

def z71 : W := mkw 0x5b3da14569d62821 0x12d9ed0a2b4eb141 0x5e39830c21c66062 0x02f1cc18610e3303

def z72 : W := mkw 0x71faf5d790e22e25 0x238fd7aebc871171 0x21f870c391c01c04 0x090fc3861c8e00e0

def z73 : W := mkw 0x00c2549296eabea7 0x000612a494b755f5 0xa1c67cf3fffffffd 0xfd0e33e79fffffff

def z74 : W := mkw 0x0082501294280686 0x0004128094a14034 0x0006703380380388 0x200033819c01c01c

def z75 : W := mkw 0x0082500014280000 0x0004128000a14000 0x21c670005e38000d 0xd90e338002f1c000

def z76 : W := mkw 0x5b35a00069960000 0x12d9ad00034cb000 0x5e39800021c60002 0x02f1cc00010e3000

def z77 : W := mkw 0x4897e03f00000000 0x2244bf01f8000000 0x0007f03f80000008 0x20003f81fc000000

def z78 : W := mkw 0x5bb7f03f7dbe0000 0x32ddbf81fbedf000 0x7ffff03ffffe000f 0xfbffff81fffff000

def z79 : W := mkw 0x7dffefff0b40b810 0x2befff7ff85a05c0 0x7fffffff9fc01c1f 0xabfffffffcfe00e0

def z80 : W := mkw 0x0000100090200604 0x0000008004810030 0x8000000010201e00 0x4c000000008100f0

def z81 : W := mkw 0x5ba740006d1c0000 0x12dd3a000368e000 0x7fc600004e180001 0x13fe30000270c000

def z82 : W := mkw 0x8200000060154148 0x041000000300aa0a 0x8001830c603fe3fa 0xf4000c186301ff1f

def z83 : W := mkw 0x7fffefff69960000 0x33ffff7ffb4cb000 0x7fffffffa1c6001f 0xa3fffffffd0e3000

def z84 : W := mkw 0x7f3dab4069d76810 0x1bf9ed5a034ebb40 0x5e39830021c66002 0x02f1cc18010e3300

def z85 : W := mkw 0x24480fff0241f810 0x2922407ff8120fc0 0x80000fff8001fc10 0x2400007ffc000fe0

def z86 : W := mkw 0xa4480fe80241f958 0x0d22407f40120fca 0x80000ffc0001fff0 0x2400007fe0000fff

def z87 : W := mkw 0x7ff7fe807fbfd010 0x1bffbff403fdfe80 0x7ffffc007fff800f 0xdbffffe003fffc00

def z88 : W := mkw 0x7de74eba00000000 0x23ef3a75d0000000 0x7fc60c3000000001 0x03fe306180000000

def z89 : W := mkw 0xffffffff7dbf4148 0x37fffffffbedfa0a 0xffffffffffffe3ff 0xffffffffffffff1f

def z90 : W := mkw 0x00c2449206089082 0x0006122490304484 0x21c60c304e198181 0x110e30618270cc0c

def z91 : W := mkw 0x7dffefff06089082 0x23efff7ff8304484 0x7fffffffce19819f 0xb3fffffffe70cc0c

def z92 : W := mkw 0x0000100096289686 0x0000008004b144b4 0x800070c3de399f9c 0xfc0003861ef1ccfc

def z93 : W := mkw 0x316805c00b40b810 0x098b402e005a05c0 0xa1f803c03fc07c16 0xcd0fc01e01fe03e0

def z94 : W := mkw 0x06000a0060014000 0x0030005003000a00 0x5e00030020006002 0x02f0001801000300

def z95 : W := mkw 0x59b7e03f00000000 0x22cdbf01f8000000 0x7ffff03f8000000f 0xa3ffff81fc000000

def z96 : W := mkw 0x0018b14590a20625 0x0000c58a2c851031 0x0039f3cf8026027e 0xa001cf9e7c013013

def z97 : W := mkw 0x7fffefff6b41f810 0x2bffff7ffb5a0fc0 0xffffffffffc1fc1f 0xfffffffffffe0fe0

def z98 : W := mkw 0x59b7f0001dbe0000 0x12cdbf8000edf000 0x21fff0001ffe000c 0x090fff8000fff000

def z99 : W := mkw 0x4a97f00074be0000 0x1254bf8003a5f000 0x5e07f000603e000b 0xd2f03f800301f000

def z100 : W := mkw 0xdfb7ea2860154148 0x06fdbf514300aa0a 0xffffff3c603fe3ff 0xf7fffff9e301ff1f

def z101 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c070c39e001c04 0x090e03861cf000e0

def z102 : W := mkw 0xdfbffb6dfdff6f6d 0x16fdffdb6feffb7b 0xffffffffffffffff 0xffffffffffffffff

def z103 : W := mkw 0x24480fff80402e25 0x2122407ffc020171 0x80000fff80007e70 0x2400007ffc0003f3

def z104 : W := mkw 0xdf35aa2869974148 0x16f9ad51434cba0a 0xde3f8f3c61ffe3fb 0xf6f1fc79e30fff1f

def z105 : W := mkw 0x7d3dbb6d90e22e25 0x23e9eddb6c871171 0xde39f3cfb1e67e7e 0xeef1cf9e7d8f33f3

def z106 : W := mkw 0x37280b4069416810 0x09b9405a034a0b40 0x5e38030021c06002 0x02f1c018010e0300

def z107 : W := mkw 0x132000006b41f810 0x08990000035a0fc0 0xfff800007fc1fc07 0xdfffc00003fe0fe0

def z108 : W := mkw 0x7dffefff00c22821 0x23efff7ff8061141 0x7fffffffa1c6607f 0xa3fffffffd0e3303

def z109 : W := mkw 0x0008014000402800 0x0000400a00020140 0x803803c031c07c16 0xcc01c01e018e03e0

def z110 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffff30c7ffe627f 0xffffff9863fff313

def z111 : W := mkw 0x0058b5c592e2be25 0x0002c5ae2c9715f1 0xa1f9ffcfffe7fe7f 0xfd0fcffe7fff3ff3

def z112 : W := mkw 0x71faf5c01feab810 0x1b8fd7ae00ff55c0 0x21f870c01fc01c04 0x090fc38600fe00e0

def z113 : W := mkw 0x35280b4000000000 0x01a9405a00000000 0x5e38030000000002 0x02f1c01800000000

def z114 : W := mkw 0x0c050a2800000000 0x0060285140000000 0xde078f3c2026627b 0xe6f03c79e1013313

def z115 : W := mkw 0x0018a14500c22821 0x0000c50a28061141 0x8039830c21e6627a 0xe401cc18610f3313

def z116 : W := mkw 0x0000000080402e25 0x0000000004020171 0x8000000000007e60 0x04000000000003f3

def z117 : W := mkw 0x0082401200000000 0x0004120090000000 0x0006703380000008 0x200033819c000000

def z118 : W := mkw 0x0058b5d792e2bea7 0x0002c5aebc9715f5 0x8039ffffb1e7fffe 0xec01cffffd8f3fff

def z119 : W := mkw 0x00c2449200000000 0x0006122490000000 0x21c67cf38000001d 0xa10e33e79c000000

def z120 : W := mkw 0x59b7e00000000000 0x02cdbf0000000000 0x7ffff0000000000f 0x83ffff8000000000

def z121 : W := mkw 0x00c2549214280000 0x000612a490a14000 0x21c67cf3de38001d 0xf90e33e79ef1c000

def z122 : W := mkw 0x0a05000060140000 0x005028000300a000 0x5e078000603e000b 0xd2f03c000301f000

def z123 : W := mkw 0xdfb7fa287dbf4148 0x16fdbfd143edfa0a 0xffffff3c7fffe3ff 0xfffffff9e3ffff1f

def z124 : W := mkw 0x79ffe5d700000000 0x23cfff2eb8000000 0x7ffff0c38000000f 0x83ffff861c000000

def z125 : W := mkw 0x0008014580402e25 0x0000400a2c020171 0x800183cfa0267e7a 0xe4000c1e7d0133f3

def z126 : W := mkw 0x00c2449200000000 0x0006122490000000 0x21c60c3000000001 0x010e306180000000

def z127 : W := mkw 0x0008014000402800 0x0000400a00020140 0x003800c011c01c04 0x0801c006008e00e0

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x8001830c2026627a 0xe4000c1861013313

def z129 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff98fcc7fe7fe7f 0xffffcc7e63ff3ff3

def z130 : W := mkw 0x82001000f0f76f6d 0x041000800787bb7b 0x8000000071ffffe0 0x5c000000038fffff

def z131 : W := mkw 0x8e1dbb6df0f76f6d 0x0470eddb6f87bb7b 0xde3ffffff1ffffff 0xfef1ffffff8fffff

def z132 : W := mkw 0x0000000000000000 0x0000000000000000 0x21c000005e000005 0xd90e000002f00000

def z133 : W := mkw 0x7138a14500000000 0x2389c50a28000000 0x0038000000000000 0x0001c00000000000

def z134 : W := mkw 0x7dffefff0241f810 0x2befff7ff8120fc0 0xffffffff8001fc1f 0xa7fffffffc000fe0

def z135 : W := mkw 0x06000a006b41f810 0x08300050035a0fc0 0xde000f007fc1fc13 0xdef0007803fe0fe0

def z136 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xffc00fc04e01fc11 0x17fe007e02700fe0

def z137 : W := mkw 0x5bb7f000fdfe2e25 0x12ddbf8007eff171 0xfffff0007ffe7e6f 0xdfffff8003fff3f3

def z138 : W := mkw 0x4897f00014be0000 0x1244bf8000a5f000 0x0007f000003e0008 0x00003f800001f000

def z139 : W := mkw 0x7fffefc06b41f810 0x0bffff7e035a0fc0 0xffffffc07fc1fc1f 0xdffffffe03fe0fe0

def z140 : W := mkw 0x00c2449206089082 0x0006122490304484 0x21c67cf3ce19819d 0xb10e33e79e70cc0c

def z141 : W := mkw 0x8ec75ebaf63dd7ce 0x04763af5d7b1eebe 0xffc7fffffe3fffff 0xfffe3ffffff1ffff

def z142 : W := mkw 0x4897f00014be0000 0x1244bf8000a5f000 0x003ff00031fe000e 0xc801ff80018ff000

def z143 : W := mkw 0x48d7e4bf00000000 0x2246bf25f8000000 0x21c7fcff8000001d 0xa10e3fe7fc000000

def z144 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x80067cf380399f98 0x240033e79c01ccfc

def z145 : W := mkw 0x8e0d0b6860556948 0x0470685b4302ab4a 0xde3f8ffc71ffffff 0xfef1fc7fe38fffff

def z146 : W := mkw 0x7fef4ffa6b41f810 0x2bff7a7fd35a0fc0 0xfffe0ff07fc1fc17 0xdffff07f83fe0fe0

def z147 : W := mkw 0x8e450ebae215d7ce 0x04722875d710aebe 0xde078fffe03ffffb 0xf6f03c7fff01ffff

def z148 : W := mkw 0x37681fc0ff69fe96 0x09bb40fe07fb4ff4 0xfff80fc07ff9ff97 0xdfffc07e03ffcffc

def z149 : W := mkw 0x7de74eba06089082 0x23ef3a75d0304484 0x7fc60c304e198181 0x13fe30618270cc0c

def z150 : W := mkw 0x7f7dafed6b41f810 0x2bfbed7f6b5a0fc0 0xfff98fcc7fc1fc17 0xdfffcc7e63fe0fe0

def z151 : W := mkw 0x59b7f0001daa0000 0x12cdbf8000ed5000 0x7ffff0001fc0000f 0x8bffff8000fe0000

def z152 : W := mkw 0x37681fc0fbe3fe35 0x09bb40fe07df1ff1 0xfff80fc07fe7fe77 0xdfffc07e03ff3ff3

def z153 : W := mkw 0x0040048002009000 0x0002002400100480 0xa1c00cc05e019c15 0xdd0e006602f00ce0

def z154 : W := mkw 0x4897f00594be0625 0x1244bf802ca5f031 0x0007f00f803e0268 0x20003f807c01f013

def z155 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffffa026627f 0xe7fffffffd013313

def z156 : W := mkw 0x8815b02d90b6076d 0x0440ad816c85b03b 0x0007f03f803e03e8 0x20003f81fc01f01f

def z157 : W := mkw 0x1b25000069140000 0x00d928000348a000 0x7fff80007ffe000f 0xdbfffc0003fff000

def z158 : W := mkw 0x51baf1459dea2e25 0x128dd78a2cef5171 0xa1f9f3cfbfe67e7e 0xed0fcf9e7dff33f3

def z159 : W := mkw 0x8200000060154148 0x041000000300aa0a 0x0000000040198180 0x100000000200cc0c

def z160 : W := mkw 0x4092f00014aa0000 0x1204978000a55000 0x0000700000000000 0x0000038000000000

def z161 : W := mkw 0x7fbffb407dff6810 0x1bfdffda03effb40 0x7ffff3007ffe600f 0xdbffff9803fff300

def z162 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff80cc05fc19c05 0x1bffc06602fe0ce0

def z163 : W := mkw 0x0000100096289686 0x0000008004b144b4 0x800000005e399f80 0x5c00000002f1ccfc

def z164 : W := mkw 0x136004806b009000 0x009b002403580480 0xfff80cc07fc19c17 0xdfffc06603fe0ce0

def z165 : W := mkw 0x5bf7f492ffbe9686 0x12dfbfa497fdf4b4 0xfffffcf3ffff9f9f 0xffffffe79ffffcfc

def z166 : W := mkw 0x7fffffc07ffff810 0x1bfffffe03ffffc0 0xffffffc07ffffc1f 0xdffffffe03ffffe0

def z167 : W := mkw 0x8a05002860154148 0x045028014300aa0a 0x8007803c603fe3e8 0x74003c01e301ff1f

def z168 : W := mkw 0x00daf5d796eabea7 0x0006d7aebcb755f5 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z169 : W := mkw 0x8e050a286b55f958 0x0c702851435aafca 0xde078f3c7ffffffb 0xfef03c79e3ffffff

def z170 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000030020006012 0xc400001801000300

def z171 : W := mkw 0x3738ab4569c36831 0x09b9c55a2b4e1b41 0x5e39830c21c66062 0x02f1cc18610e3303

def z172 : W := mkw 0x3578bfc590e22e25 0x01abc5fe2c871171 0xfff9ffcfb1e67e7f 0xefffcffe7d8f33f3

def z173 : W := mkw 0x75faefff00000000 0x23afd77ff8000000 0x21f87fff80000014 0x210fc3fffc000000

def z174 : W := mkw 0x53b2f0007dbe0000 0x129d978003edf000 0x21f870007ffe0004 0x590fc38003fff000

def z175 : W := mkw 0xff3dab6d60154148 0x27f9ed5b6b00aa0a 0x5e39830c20066062 0x02f1cc1861003303

def z176 : W := mkw 0x37681fc0fb61fe14 0x09bb40fe07db0ff0 0xfff87fc3ffe1fe1f 0xffffc3fe1fff0ff0

def z177 : W := mkw 0xbf2d0b6869556958 0x0df9685b434aab4a 0x5e39830c21c66062 0x02f1cc18610e3303

def z178 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c070c39e201e1c 0xed0e03861cf100f0

def z179 : W := mkw 0x5be744926f1c9082 0x12df3a249378e484 0x7fc60c304e198181 0x13fe30618270cc0c

def z180 : W := mkw 0x71fae5d700000000 0x238fd72eb8000000 0x21fe7cf38000001d 0xa10ff3e79c000000

def z181 : W := mkw 0x8e875a3af43d47ce 0x04743ad1d7a1ea3e 0xde07ff3fe03fe3fb 0xf6f03ff9ff01ff1f

def z182 : W := mkw 0x0010b00590a20625 0x000085802c851031 0x8001f30fa026627a 0xe4000f987d013313

def z183 : W := mkw 0x0010b00090e22e25 0x0000858004871171 0x8039f00031e67e6e 0xcc01cf80018f33f3

def z184 : W := mkw 0x37ea4fd26f49f892 0x09bf527e937a4fc4 0xfffe0ff07fd9fd97 0xdffff07f83fecfec

def z185 : W := mkw 0x0010b00010a20000 0x0000858000851000 0x0038700011c00004 0x0801c380008e0000

def z186 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e078f3c2006607b 0xa2f03c79e1003303

def z187 : W := mkw 0x8000002800000148 0x040000014000000a 0x0000003c000003e0 0x20000001e000001f

def z188 : W := mkw 0x7f3dab6d69960000 0x33f9ed5b6b4cb000 0x5e39830c21c60002 0x02f1cc18610e3000

def z189 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z190 : W := mkw 0x59f7e49200000000 0x02cfbf2490000000 0x7ffffcf38000001f 0xa3ffffe79c000000

def z191 : W := mkw 0x7fffffffffbe9686 0x33fffffffffdf4b4 0xffffffffffff9f9f 0xfffffffffffffcfc

def z192 : W := mkw 0x00c2549294280686 0x000612a494a14034 0x21c67cf38038039d 0xa10e33e79c01c01c

def z193 : W := mkw 0x0018b14510a20000 0x0000c58a28851000 0x0039f3cfb1e6001e 0xe801cf9e7d8f3000

def z194 : W := mkw 0x0010b00590a20625 0x000085802c851031 0x0001f00f80260268 0x20000f807c013013

def z195 : W := mkw 0x35600e8000000000 0x01ab007400000000 0x7fc00c0000000001 0x03fe006000000000

def z196 : W := mkw 0xffffefff60154148 0x27ffff7ffb00aa0a 0x7fffffffc019819f 0xb3fffffffe00cc0c

def z197 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfffe0ff07ff9ff9f 0xfffff07f83ffcffc

def z198 : W := mkw 0x1120000009000000 0x0089000000480000 0x21f800001fc00004 0x090fc00000fe0000

def z199 : W := mkw 0x37e25e92ff29d696 0x09bf12f497f94eb4 0xffc67cf3de399f9d 0xfffe33e79ef1ccfc

def z200 : W := mkw 0x0200000069000000 0x0010000003480000 0x000000007fc00000 0x5800000003fe0000

def z201 : W := mkw 0x35680fff00000000 0x21ab407ff8000000 0x7ff80fff80000017 0xa3ffc07ffc000000

def z202 : W := mkw 0x204805d700000000 0x2102402eb8000000 0x000000c380000000 0x000000061c000000

def z203 : W := mkw 0x0082500014280000 0x0004128000a14000 0xa1c67c305e39839d 0xfd0e33e182f1cc1c

def z204 : W := mkw 0x8e1dab6d60154148 0x0470ed5b6b00aa0a 0xde3fffffe03fe3ff 0xf6f1ffffff01ff1f

def z205 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffe70005fd80005 0x1bfff38002fec000

def z206 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c070c3de399f84 0x5d0e03861ef1ccfc

def z207 : W := mkw 0x7ffffffffbe3fe35 0x2bffffffffdf1ff1 0xffffffffffe7fe7f 0xffffffffffff3ff3

def z208 : W := mkw 0x0040049200000000 0x0002002490000000 0x00000cf380000010 0x200000679c000000

def z209 : W := mkw 0x0040049282009686 0x00020024941004b4 0x80060cf3c0399f99 0xf40030679e01ccfc

def z210 : W := mkw 0x7df7eebf00000000 0x23efbf75f8000000 0x7fc7fc3f80000009 0x23fe3fe1fc000000

def z211 : W := mkw 0xdfa74a286d1d4148 0x16fd3a514368ea0a 0xffc78f3c6e3fe3fb 0xf7fe3c79e371ff1f

def z212 : W := mkw 0x84000a2800014148 0x0420005140000a0a 0x80060f3c4039e3f9 0xf4003079e201cf1f

def z213 : W := mkw 0x37280b406b41f810 0x09b9405a035a0fc0 0xde3803007fc1fc02 0x5ef1c01803fe0fe0

def z214 : W := mkw 0xff3dab6d60154148 0x27f9ed5b6b00aa0a 0xde3f8f3c603fe3fb 0xf6f1fc79e301ff1f

def z215 : W := mkw 0x8c050a2800154148 0x046028514000aa0a 0x80078f3c003fe3f8 0x24003c79e001ff1f

def z216 : W := mkw 0xae4d0fe86255f958 0x0d72687f4312afca 0xde078ffc603ffffb 0xf6f03c7fe301ffff

def z217 : W := mkw 0x5bb7e00069000000 0x02ddbf0003480000 0x7ffff0007fc0000f 0xdbffff8003fe0000

def z218 : W := mkw 0x7fffffff7dbe0000 0x33fffffffbedf000 0x7ffffffffffe001f 0xfbfffffffffff000

def z219 : W := mkw 0x7dffffff96eabea7 0x23effffffcb755f5 0xffffffffffffffff 0xffffffffffffffff

def z220 : W := mkw 0xbf2d0b6869556958 0x0df9685b434aab4a 0xde3f8f3c61ffe3fb 0xf6f1fc79e30fff1f

def z221 : W := mkw 0x51b2f0001daa0000 0x128d978000ed5000 0x21f870001fc00004 0x090fc38000fe0000

def z222 : W := mkw 0x0000000000402800 0x0000000000020140 0x8000000031c07c00 0x4c000000018e03e0

def z223 : W := mkw 0x37ea4fd26b41f810 0x09bf527e935a0fc0 0xfffe7ff3ffc1fc1f 0xfffff3ff9ffe0fe0

def z224 : W := mkw 0x0018a14500c22821 0x0000c50a28061141 0x0039f3cfa1c6607e 0xa001cf9e7d0e3303

def z225 : W := mkw 0x9f250a2869154148 0x04f928514348aa0a 0xffff8f3c7fffe3ff 0xfffffc79e3ffff1f

def z226 : W := mkw 0x020010007ffff810 0x1810008003ffffc0 0x800000007ffffc00 0x5c00000003ffffe0

def z227 : W := mkw 0x8e450ea86215d148 0x047228754310ae8a 0xffc78ffc7e3fffff 0xfffe3c7fe3f1ffff

def z228 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ff9f3cf80000006 0x03ffcf9e7c000000

def z229 : W := mkw 0x2c4d0fff00000000 0x2162687ff8000000 0x5e078fff8000001b 0xa2f03c7ffc000000

def z230 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803870c3b1e67e64 0x4c01c3861d8f33f3

def z231 : W := mkw 0x37680fc060014000 0x01bb407e03000a00 0xfff80fc06001e017 0xd7ffc07e03000f00

def z232 : W := mkw 0x00d2f49296aa9686 0x000697a494b554b4 0xa1fffcf3ffff9f9f 0xfd0fffe79ffffcfc

def z233 : W := mkw 0x02001000fdfe2e25 0x1010008007eff171 0x800000007ffe7e60 0x5c00000003fff3f3

def z234 : W := mkw 0x8e0d0b6de0556f6d 0x0470685b6f02ab7b 0xde078fffe03ffffb 0xf6f03c7fff01ffff

def z235 : W := mkw 0x7dffffff90e22e25 0x23effffffc871171 0xffffffffb1e67e7f 0xeffffffffd8f33f3

def z236 : W := mkw 0xfdffefff00014148 0x27efff7ff8000a0a 0xffffffff8001e3ff 0xa7fffffffc000f1f

def z237 : W := mkw 0x37680fd2eb41fe96 0x09bb407e975a0ff4 0xfff80ff3ffc1ff97 0xffffc07f9ffe0ffc

def z238 : W := mkw 0x37280b4069416810 0x09b9405a034a0b40 0xde3803c031c07c16 0xcef1c01e018e03e0

def z239 : W := mkw 0x0200000069416810 0x08100000034a0b40 0x0000000021c06000 0x00000000010e0300

def z240 : W := mkw 0x31ea55d29f68be96 0x098f52ae94fb45f4 0xa1fe7cf3dff99f9d 0xfd0ff3e79effccfc

def z241 : W := mkw 0x3f6d0fe86b41f810 0x09fb687f435a0fc0 0xffff8ffc7fc1fc1f 0xfffffc7fe3fe0fe0

def z242 : W := mkw 0x0018a14500c22821 0x0000c50a28061141 0x0039830c21c66062 0x0001cc18610e3303

def z243 : W := mkw 0x51a240000d080000 0x128d120000684000 0x21c000000e000000 0x010e000000700000

def z244 : W := mkw 0xb7680fc06b55f958 0x0dbb407e035aafca 0xfff80fc07ffffff7 0xdfffc07e03ffffff

def z245 : W := mkw 0x02001000fbe3fe35 0x0810008007df1ff1 0x800000007fe7fe60 0x5c00000003ff3ff3

def z246 : W := mkw 0x0000100090200604 0x0000008004810030 0x80067cf3d0399f9d 0xfc0033e79e81ccfc

def z247 : W := mkw 0x51f2f4929faa9686 0x128f97a494fd54b4 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z248 : W := mkw 0x5bbff1457dbe0000 0x12ddff8a2bedf000 0x7ffff3cffffe001f 0xfbffff9e7ffff000

def z249 : W := mkw 0x7dbfeb7f00000000 0x23edff5bf8000000 0x5e3ff33f8000000a 0x22f1ff99fc000000

def z250 : W := mkw 0x0000100090e22e25 0x0000008004871171 0x0000000011c01c00 0x08000000008e00e0

def z251 : W := mkw 0x7dffffff96289686 0x23effffffcb144b4 0x7fffffff9e001c1f 0xabfffffffcf000e0

def z252 : W := mkw 0x5ba740006d1c0000 0x12dd3a000368e000 0x7ffe00007fd80007 0xdbfff00003fec000

def z253 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde060f306019e193 0xd6f030798300cf0c

def z254 : W := mkw 0x7dffefff02009000 0x23efff7ff8100480 0xffffffffde019c1f 0xfffffffffef00ce0

def z255 : W := mkw 0x0018b14596eabea7 0x0000c58a2cb755f5 0x8039f3cffffffffe 0xfc01cf9e7fffffff

def z256 : W := mkw 0x7de74eba00000000 0x23ef3a75d0000000 0x7fc67cf38000001d 0xa3fe33e79c000000

def z257 : W := mkw 0x0010b00010a20000 0x0000858000851000 0x0039f00031e6000e 0xc801cf80018f3000

def z258 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c7fffffe3fffff 0xfd0e3ffffff1ffff

def z259 : W := mkw 0x35680fc002009000 0x01ab407e00100480 0xfff80fc05e019c17 0xdfffc07e02f00ce0

def z260 : W := mkw 0x2458afff00000000 0x2122c57ff8000000 0x0039ffff8000001e 0xa001cffffc000000

def z261 : W := mkw 0x37680fc06b01d010 0x09bb407e03580e80 0x7ff80fc04e018017 0x93ffc07e02700c00

def z262 : W := mkw 0x0082400004080000 0x0004120000204000 0x21c600004e180001 0x110e30000270c000

def z263 : W := mkw 0x0000000000000000 0x0000000000000000 0x000180002026000a 0xc0000c0001013000

def z264 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e07833c203e63ea 0x22f03c19e101f31f

def z265 : W := mkw 0x86000a0060154148 0x043000500300aa0a 0xde000f00603fe3f3 0xd6f000780301ff1f

def z266 : W := mkw 0x0000000006089082 0x0000000000304484 0x000000004e198180 0x100000000270cc0c

def z267 : W := mkw 0x5ba750007dbe0000 0x12dd3a8003edf000 0x7fc600007ffe0001 0x5bfe300003fff000

def z268 : W := mkw 0x37e24e926f09d092 0x09bf127493784e84 0x7fc60c304e198181 0x13fe30618270cc0c

def z269 : W := mkw 0x8e875a28743d4148 0x04743ad143a1ea0a 0xffc7ff3c7e3fe3ff 0xfffe3ff9e3f1ff1f

def z270 : W := mkw 0xbf6d0fe860154148 0x05fb687f4300aa0a 0xffff8ffc603fe3ff 0xf7fffc7fe301ff1f

def z271 : W := mkw 0x02c25492ffbe9686 0x101612a497fdf4b4 0xa1c67cf3ffff9f9d 0xfd0e33e79ffffcfc

def z272 : W := mkw 0x0082401204080082 0x0004120090204004 0x0006003000180180 0x000030018000c00c

def z273 : W := mkw 0x59bfe14500000000 0x02cdff0a28000000 0x7ffff3cf8000001f 0xa3ffff9e7c000000

def z274 : W := mkw 0xce97ea3f60154148 0x2674bf51fb00aa0a 0xde07ff3fe03fe3fb 0xf6f03ff9ff01ff1f

def z275 : W := mkw 0x37681fc07ffff810 0x19bb40fe03ffffc0 0xfff80fc07ffffc17 0xdfffc07e03ffffe0

def z276 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803873cf91c07e74 0x2c01c39e7c8e03f3

def z277 : W := mkw 0x71faf5d796289686 0x238fd7aebcb144b4 0xa1fe7cf3de399f9d 0xfd0ff3e79ef1ccfc

def z278 : W := mkw 0x7def4fff00000000 0x23ef7a7ff8000000 0x7fc60fff80000011 0x23fe307ffc000000

def z279 : W := mkw 0x0a05000060140000 0x005028000300a000 0xde078c30603f839b 0xf6f03c618301fc1c

def z280 : W := mkw 0x5b35b0007dbe0000 0x12d9ad8003edf000 0x5e3980007ffe0002 0x5af1cc0003fff000

def z281 : W := mkw 0x4897f01294be0686 0x1244bf8094a5f034 0x0007f033803e0388 0x20003f819c01f01c

def z282 : W := mkw 0x0000100014be0000 0x1000008000a5f000 0x00000000003e0000 0x000000000001f000

def z283 : W := mkw 0x0cc75eba96289686 0x00663af5d4b144b4 0xffc7ffffde399f9f 0xfffe3ffffef1ccfc

def z284 : W := mkw 0x5be75492ff3c9686 0x12df3aa497f9e4b4 0xffc67cf3de399f9d 0xfffe33e79ef1ccfc

def z285 : W := mkw 0x7de74eba00000000 0x23ef3a75d0000000 0x7fc78f3c0000001b 0xa3fe3c79e0000000

def z286 : W := mkw 0x0082501294280686 0x0004128094a14034 0x0000700380000000 0x000003801c000000

def z287 : W := mkw 0x24480fc58241fe35 0x0922407e2c120ff1 0x80000fcf8001fe70 0x2400007e7c000ff3

def z288 : W := mkw 0x3178b5c59be2be35 0x098bc5ae2cdf15f1 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z289 : W := mkw 0x24080b6d00000000 0x2120405b68000000 0x0000030c00000000 0x0000001860000000

def z290 : W := mkw 0x8200000060154148 0x041000000300aa0a 0x80060c30603fe3f9 0xf40030618301ff1f

def z291 : W := mkw 0x5b35a00069960000 0x12d9ad00034cb000 0x7ff980007fc60007 0xdbffcc0003fe3000

def z292 : W := mkw 0xdf35aa2869974148 0x16f9ad51434cba0a 0x5e39830c21c66062 0x02f1cc18610e3303

def z293 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c67cf39e001c1d 0xa90e33e79cf000e0

def z294 : W := mkw 0x37600e806b41f810 0x09bb0074035a0fc0 0xffc00c007fc1fc01 0x5ffe006003fe0fe0

def z295 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde018f0c6007e073 0xd6f00c7863003f03

def z296 : W := mkw 0x8805002800140148 0x044028014000a00a 0x80078c3c403f83f9 0xf4003c61e201fc1f

def z297 : W := mkw 0x0040048002009000 0x0002002400100480 0x80000cc000019c10 0x0400006600000ce0

def z298 : W := mkw 0x35680fc00241f810 0x09ab407e00120fc0 0xfff80fc00001fc17 0x87ffc07e00000fe0

def z299 : W := mkw 0x77faffc07febf810 0x1bbfd7fe03ff5fc0 0xfff87fc07fc1fc17 0xdfffc3fe03fe0fe0

def z300 : W := mkw 0xbf650ea86b15d158 0x0dfb28754358ae8a 0xffc78f3c6e3fe3fb 0xf7fe3c79e371ff1f

def z301 : W := mkw 0x020801406b41f810 0x0810400a035a0fc0 0x803803c07fc1fc16 0xdc01c01e03fe0fe0

def z302 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x5e3ff00021fe000a 0x02f1ff80010ff000

def z303 : W := mkw 0x820000006b55f958 0x0c100000035aafca 0x800000007fffffe0 0x5c00000003ffffff

def z304 : W := mkw 0x26480fc06241f810 0x0932407e03120fc0 0xde000fc06001fc13 0xd6f0007e03000fe0

def z305 : W := mkw 0xb7680fe86b41f958 0x0dbb407f435a0fca 0xfff80ffc7fc1fff7 0xffffc07fe3fe0fff

def z306 : W := mkw 0x0c1dab6d00000000 0x0060ed5b68000000 0x5e3fffff8000001f 0xa2f1fffffc000000

def z307 : W := mkw 0x0000000002009000 0x0000000000100480 0x800000005e019c00 0x5c00000002f00ce0

def z308 : W := mkw 0x02001000ffbe9686 0x1010008007fdf4b4 0x800000007fff9f80 0x5c00000003fffcfc

def z309 : W := mkw 0x06c25e92f629d686 0x003612f497b14eb4 0xffc67ff3fe39ff9f 0xfffe33ff9ff1cffc

def z310 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c07cf39e019f94 0x2d0e03e79cf00cfc

def z311 : W := mkw 0x5bbff145fdfe2e25 0x12ddff8a2feff171 0xfffff3cffffe7e7f 0xffffff9e7ffff3f3

def z312 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001830c0000001a 0xa0000c1860000000

def z313 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e01830c20066062 0x02f00c1861003303

def z314 : W := mkw 0x8805002800140148 0x044028014000a00a 0x0007803c003e03e8 0x20003c01e001f01f

def z315 : W := mkw 0x75faefd700000000 0x23afd77eb8000000 0x7ff87fc380000017 0x83ffc3fe1c000000

def z316 : W := mkw 0x4c97ea3f00000000 0x2264bf51f8000000 0x5e07ff3f8000001b 0xa2f03ff9fc000000

def z317 : W := mkw 0xdbb7f0287dbe0148 0x16ddbf8143edf00a 0x7ffff03c7ffe03ef 0xfbffff81e3fff01f

def z318 : W := mkw 0x336805c06b40b810 0x099b402e035a05c0 0x7ff800c07fc01c07 0xdbffc00603fe00e0

def z319 : W := mkw 0x0000000080000604 0x0000000004000030 0x800000c380001e10 0x240000061c0000f0

def z320 : W := mkw 0x7fffffd2fffffe96 0x1bfffffe97fffff4 0xfffffff3ffffff9f 0xffffffff9ffffffc

def z321 : W := mkw 0x3578afc500000000 0x01abc57e28000000 0x7ff9ffcf8000001f 0xa3ffcffe7c000000

def z322 : W := mkw 0x7f7dafc06bd7f810 0x1bfbed7e035ebfc0 0xfff98fc07fc7fc17 0xdfffcc7e03fe3fe0

def z323 : W := mkw 0x35ea5fd296289686 0x01af52fe94b144b4 0xfffe7ff3de399f9f 0xfffff3ff9ef1ccfc

def z324 : W := mkw 0x7bfff5d77dbe0000 0x33dfffaebbedf000 0x7ffff0c3fffe000f 0xdbffff861ffff000

def z325 : W := mkw 0x5bb7f012fdbe0686 0x12ddbf8097edf034 0x7ffff033fffe038f 0xfbffff819ffff01c

def z326 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803870c391e01e1c 0xec01c3861c8f00f0

def z327 : W := mkw 0x7fe74eba6b01d010 0x2bff3a75d3580e80 0x7fc60c304e018001 0x13fe306182700c00

def z328 : W := mkw 0x132010007dbe0000 0x1099008003edf000 0x7ff800007ffe0007 0xdbffc00003fff000

def z329 : W := mkw 0x5b25000069140000 0x12d928000348a000 0x5e00000000000000 0x02f0000000000000

def z330 : W := mkw 0x0082500014280000 0x0004128000a14000 0x0006700000380008 0x000033800001c000

def z331 : W := mkw 0x8ec74eba60154148 0x04763a75d300aa0a 0xffc7ffffe03fe3ff 0xf7fe3fffff01ff1f

def z332 : W := mkw 0x5bb7e00060140000 0x02ddbf000300a000 0x7ffff000603e000f 0xd3ffff800301f000

def z333 : W := mkw 0x7d7dafed00000000 0x23ebed7f68000000 0x7ff98fcc00000017 0x83ffcc7e60000000

def z334 : W := mkw 0x71faf5d796289686 0x238fd7aebcb144b4 0x21f870c39e001c04 0x090fc3861cf000e0

def z335 : W := mkw 0x24480fff00000000 0x2122407ff8000000 0x00000fff80000010 0x2000007ffc000000

def z336 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde060c30603fe3e1 0x56f030618301ff1f

def z337 : W := mkw 0xffe74eba60154148 0x27ff3a75d300aa0a 0xffc78f3c603fe3fb 0xf7fe3c79e301ff1f

def z338 : W := mkw 0x59f7f49296289686 0x02cfbfa494b144b4 0xfffffcf3de399f9f 0xffffffe79ef1ccfc

def z339 : W := mkw 0x004805d78240bea7 0x0002402ebc1205f5 0x80000fff8001fff0 0x2400007ffc000fff

def z340 : W := mkw 0x0a05000060140000 0x005028000300a000 0xde07830c603e627b 0xf6f03c186301f313

def z341 : W := mkw 0x35680fc00b40b810 0x09ab407e005a05c0 0x7ff80fc01fc01c17 0x8bffc07e00fe00e0

def z342 : W := mkw 0x0008014500000000 0x0000400a28000000 0x000003cf80000010 0x2000001e7c000000

def z343 : W := mkw 0x5bbff145fdfe2e25 0x12ddff8a2feff171 0x7ffff0c3fffe1c0f 0xdbffff861ffff0e0

def z344 : W := mkw 0x7dffffff94280686 0x23effffffca14034 0x7fffffff8038039f 0xa3fffffffc01c01c

def z345 : W := mkw 0x37ea5fc07f69f810 0x09bf52fe03fb4fc0 0xfffe7fc07ff9fc1f 0xdffff3fe03ffcfe0

def z346 : W := mkw 0x0a0510007dbe0000 0x1050288003edf000 0x5e0780007ffe000b 0xdaf03c0003fff000

def z347 : W := mkw 0x8ec74eba661dd1ca 0x04763a75d330ee8e 0xffc78f3c6e3fe3fb 0xf7fe3c79e371ff1f

def z348 : W := mkw 0x59b7f00014280000 0x02cdbf8000a14000 0x7ffff0005e38000f 0xdbffff8002f1c000

def z349 : W := mkw 0x000000000241f810 0x0800000000120fc0 0x800000000001fc00 0x0400000000000fe0

def z350 : W := mkw 0x7fffffc07dbe0000 0x13fffffe03edf000 0x7fffffc07ffe001f 0xdbfffffe03fff000

def z351 : W := mkw 0x13a250007d280000 0x009d128003e94000 0x7ffe70007ff8000f 0xdbfff38003ffc000

def z352 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803ffffff1ffffff 0xfc01ffffff8fffff

def z353 : W := mkw 0x316805c000000000 0x018b402e00000000 0x21f800c000000004 0x010fc00600000000

def z354 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f0cf91e61e6c 0x2801cf867c8f30f3

def z355 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde01830c603fe3e2 0x56f00c186301ff1f

def z356 : W := mkw 0x0040049282009686 0x00020024941004b4 0xa1c00cf3de019f95 0xfd0e00679ef00cfc

def z357 : W := mkw 0xce97fa2874bf4148 0x1674bfd143a5fa0a 0xde07ff3c603fe3fb 0xf6f03ff9e301ff1f

def z358 : W := mkw 0x0000000000000000 0x0000000000000000 0x0006003000380388 0x200030018001c01c

def z359 : W := mkw 0x0618bb45f0e36e25 0x0030c5da2f871b71 0xde39ffcff1e7fe7f 0xfef1cffe7f8f3ff3

def z360 : W := mkw 0x71faf5d790e22e25 0x238fd7aebc871171 0xa1f9f3cfb1e67e7e 0xed0fcf9e7d8f33f3

def z361 : W := mkw 0x71e2449200000000 0x238f122490000000 0x21c0000000000000 0x010e000000000000

def z362 : W := mkw 0x0008114090602e04 0x0000408a04830170 0x803873c3b1e07e1e 0xec01c39e1d8f03f0

def z363 : W := mkw 0x0010b00090a20604 0x0000858004851030 0x8039f0c3b1e61e1e 0xec01cf861d8f30f0

def z364 : W := mkw 0x024004806b41f810 0x08120024035a0fc0 0xa1c00cc07fc1fc15 0xdd0e006603fe0fe0

def z365 : W := mkw 0x7dffffff90200604 0x23effffffc810030 0xffffffff90201e1f 0xeffffffffc8100f0

def z366 : W := mkw 0x48874000041c0000 0x12443a000020e000 0x0006000000180000 0x000030000000c000

def z367 : W := mkw 0x8e15ba2870b74148 0x0470add14385ba0a 0xde3fff3c71ffe3ff 0xfef1fff9e38fff1f

def z368 : W := mkw 0x0210b0007dbe0000 0x1010858003edf000 0x0039f0007ffe000e 0xd801cf8003fff000

def z369 : W := mkw 0x00daf5d796eabea7 0x0006d7aebcb755f5 0xa1f9f3cfbfe67e7e 0xed0fcf9e7dff33f3

def z370 : W := mkw 0x24480fc000000000 0x0122407e00000000 0x00000fc000000010 0x0000007e00000000

def z371 : W := mkw 0x5bb7f0007ffff810 0x1addbf8003ffffc0 0xfffff0007ffffc0f 0xdfffff8003ffffe0

def z372 : W := mkw 0x37600e806b01d010 0x09bb007403580e80 0xffc00f006e01e013 0xd7fe007803700f00

def z373 : W := mkw 0xdfb7fa287dbf4148 0x16fdbfd143edfa0a 0x7ffff30c7ffe606f 0xdbffff9863fff303

def z374 : W := mkw 0x6cdfefff00000000 0x2366ff7ff8000000 0x0007ffff80000018 0x20003ffffc000000

def z375 : W := mkw 0x8c050a2800140148 0x046028514000a00a 0x5e078f3c003e03fb 0xa2f03c79e001f01f

def z376 : W := mkw 0x06000a0060014000 0x0030005003000a00 0x5e000c0040018001 0x12f0006002000c00

def z377 : W := mkw 0x316805c00b40b810 0x098b402e005a05c0 0xa1f80cc05fc19c15 0xdd0fc06602fe0ce0

def z378 : W := mkw 0x59bff14590e22e25 0x02cdff8a2c871171 0xfffff3cfb1e67e7f 0xefffff9e7d8f33f3

def z379 : W := mkw 0x5bfff5d7fffebea7 0x12dfffaebffff5f5 0xffffffffffffffff 0xffffffffffffffff

def z380 : W := mkw 0x0010a00000000000 0x0000850000000000 0x0039f0000000000e 0x8001cf8000000000

def z381 : W := mkw 0x37680fc069416810 0x09bb407e034a0b40 0x7ff80fc021c06017 0x83ffc07e010e0300

def z382 : W := mkw 0x82001000f63dd7ce 0x0410008007b1eebe 0x800000007e3fffe0 0x5c00000003f1ffff

def z383 : W := mkw 0x7fe74eba6d1c0000 0x33ff3a75d368e000 0x7fc60c304e180001 0x13fe30618270c000

def z384 : W := mkw 0x5bb7f005fdbe0625 0x12ddbf802fedf031 0x7ffff00ffffe026f 0xfbffff807ffff013

def z385 : W := mkw 0x7dffefff82009686 0x23efff7ffc1004b4 0xffffffff80019f9f 0xa7fffffffc000cfc

def z386 : W := mkw 0x5db7ea2800000000 0x02edbf5140000000 0x7fffff3c0000001f 0xa3fffff9e0000000

def z387 : W := mkw 0x820010007dbf4148 0x1410008003edfa0a 0x800000007fffe3e0 0x5c00000003ffff1f

def z388 : W := mkw 0x8e051a28f0f76f6d 0x047028d14787bb7b 0xde078f3c71fffffb 0xfef03c79e38fffff

def z389 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039830c31e67e62 0x4c01cc18618f33f3

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x00060c3040198181 0x100030618200cc0c

def z391 : W := mkw 0x24480fd28241fe96 0x0922407e94120ff4 0x80000ff38001ff90 0x2400007f9c000ffc

def z392 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c670c3de381c0d 0xd90e33861ef1c0e0

def z393 : W := mkw 0x0040048002009000 0x0002002400100480 0xa1c60cf05e399f9d 0xfd0e306782f1ccfc

def z394 : W := mkw 0xdfa74a286d1d4148 0x16fd3a514368ea0a 0x7fc60c304e198181 0x13fe30618270cc0c

def z395 : W := mkw 0x0000100090200604 0x0000008004810030 0x000070c390001c04 0x080003861c8000e0

def z396 : W := mkw 0x37600e806b01d010 0x09bb007403580e80 0x7ff80c007fc18007 0xdbffc06003fe0c00

def z397 : W := mkw 0x2458bfc592e3fe35 0x0922c5fe2c971ff1 0x8039ffcfb1e7fe7e 0xec01cffe7d8f3ff3

def z398 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ff9f0003fc60006 0x0bffcf8001fe3000

def z399 : W := mkw 0x4092e01700000000 0x22049700b8000000 0x0000700380000000 0x000003801c000000

def z400 : W := mkw 0x0040148092209604 0x000200a4049104b0 0xa1c07cc3de219e1d 0xfd0e03e61ef10cf0

def z401 : W := mkw 0x009af14594ea2e25 0x0004d78a2ca75171 0xa1fff3cffffe7e7f 0xfd0fff9e7ffff3f3

def z402 : W := mkw 0x204805c00240b810 0x0902402e001205c0 0x000000c000001c00 0x00000006000000e0

def z403 : W := mkw 0x0040149292209686 0x000200a4949104b4 0x80007cf390219f9c 0xec0003e79c810cfc

def z404 : W := mkw 0x24400e800201d010 0x0922007400100e80 0x00000c0000018000 0x0000006000000c00

def z405 : W := mkw 0x0018a14500000000 0x0000c50a28000000 0x003870c380000004 0x0001c3861c000000

def z406 : W := mkw 0x009af15794ea2ea7 0x0004d78abca75175 0x803ff3ffb1fe7ffe 0xec01ff9ffd8ff3ff

def z407 : W := mkw 0x02c25492ff69fe96 0x081612a497fb4ff4 0xa1c67cf3fff9ff9d 0xfd0e33e79fffcffc

def z408 : W := mkw 0xae4d0fff60154148 0x2572687ffb00aa0a 0xde078fffe03fe3fb 0xf6f03c7fff01ff1f

def z409 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e078f3c4019819b 0xb2f03c79e200cc0c

def z410 : W := mkw 0x51b2f0001daa0000 0x128d978000ed5000 0x21fe70005ff8000d 0xd90ff38002ffc000

def z411 : W := mkw 0x0010b00590e22e25 0x000085802c871171 0x8001f00fb1e67e68 0x6c000f807d8f33f3

def z412 : W := mkw 0x0008014580402e25 0x0000400a2c020171 0x803803cfb1c07e76 0xec01c01e7d8e03f3

def z413 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e00000000000000 0x02f0000000000000

def z414 : W := mkw 0x0018b14590200604 0x0000c58a2c810030 0x8039f3cf90201e1e 0xec01cf9e7c8100f0

def z415 : W := mkw 0x0000100090200604 0x0000008004810030 0x0000700380200208 0x200003801c010010

def z416 : W := mkw 0x8a05000060154148 0x045028000300aa0a 0xde078000603fe3eb 0xd6f03c000301ff1f

def z417 : W := mkw 0x336805c06b41f810 0x099b402e035a0fc0 0xa1f800c07fc1fc04 0x5d0fc00603fe0fe0

def z418 : W := mkw 0x59b7f00010a20000 0x02cdbf8000851000 0x7ffff00031e6000f 0xcbffff80018f3000

def z419 : W := mkw 0x06400e806201d000 0x0032007403100e80 0xffc00fc07e01fc17 0xdffe007e03f00fe0

def z420 : W := mkw 0x0e050a0060154000 0x007028500300aa00 0xde078f00603fe01b 0xd6f03c780301ff00

def z421 : W := mkw 0x71faf5d71daa0000 0x338fd7aeb8ed5000 0x21f870c39fc00004 0x090fc3861cfe0000

def z422 : W := mkw 0x00c2449200000000 0x0006122490000000 0xa1c67cf3c039839d 0xf50e33e79e01cc1c

def z423 : W := mkw 0x7dbfeb6d00000000 0x23edff5b68000000 0x7ffff30c0000000f 0x83ffff9860000000

def z424 : W := mkw 0x71fae5d70b40b810 0x2b8fd72eb85a05c0 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z425 : W := mkw 0xfdffefff00140148 0x27efff7ff800a00a 0x7fffffff803e03ff 0xa3fffffffc01f01f

def z426 : W := mkw 0x8e15ba2df0b7476d 0x0470add16f85ba3b 0xde07ff3fe03fe3fb 0xf6f03ff9ff01ff1f

def z427 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffe7cf380000005 0x03fff3e79c000000

def z428 : W := mkw 0x37680fff6b41f810 0x29bb407ffb5a0fc0 0xfff80fffffc1fc17 0xffffc07ffffe0fe0

def z429 : W := mkw 0x00daf5d796289686 0x0006d7aebcb144b4 0xa1ffffffde399f9f 0xfd0ffffffef1ccfc

def z430 : W := mkw 0x0082501294280686 0x0004128094a14034 0x21c67033de38038d 0xf90e33819ef1c01c

def z431 : W := mkw 0x7df7eeba00000000 0x23efbf75d0000000 0x7ffffc300000000f 0x83ffffe180000000

def z432 : W := mkw 0x00c2449206089082 0x0006122490304484 0xa1c60c304e398399 0xf50e30618271cc1c

def z433 : W := mkw 0x00daf5d790e22e25 0x0006d7aebc871171 0xa1ffffffb1e67e7f 0xed0ffffffd8f33f3

def z434 : W := mkw 0x5fb7fa007dbf4000 0x12fdbfd003edfa00 0xffffff007fffe01f 0xdffffff803ffff00

def z435 : W := mkw 0x3778bfc5fbe3fe35 0x09bbc5fe2fdf1ff1 0xfff87fc3ffc1fc17 0xdfffc3fe1ffe0fe0

def z436 : W := mkw 0x71fae5d700000000 0x238fd72eb8000000 0x21f9f3cf8000001e 0xa10fcf9e7c000000

def z437 : W := mkw 0x1320000069000000 0x0099000003480000 0x5e38000021c00002 0x02f1c000010e0000

def z438 : W := mkw 0x5bf7f4927dbe0000 0x12dfbfa493edf000 0x7ffffcf3fffe001f 0xfbffffe79ffff000

def z439 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803873c3b1c07c16 0xcc01c39e1d8e03e0

def z440 : W := mkw 0x35680fc00b41f810 0x09ab407e005a0fc0 0xa1f80fc01fc1fc14 0x0d0fc07e00fe0fe0

def z441 : W := mkw 0x489fe17f00000000 0x2244ff0bf8000000 0x003ff3ff8000001e 0xa001ff9ffc000000

def z442 : W := mkw 0x26480fc06b41f810 0x0932407e035a0fc0 0x80000fc07fc1fc10 0x5c00007e03fe0fe0

def z443 : W := mkw 0x0040048002009000 0x0002002400100480 0x21c000c01e001c04 0x090e000600f000e0

def z444 : W := mkw 0x0cc74eba00000000 0x00663a75d0000000 0x7fc7ffff8000001f 0xa3fe3ffffc000000

def z445 : W := mkw 0x0018a14580402e25 0x0000c50a2c020171 0x8039f3cf80007e7e 0xa401cf9e7c0003f3

def z446 : W := mkw 0x7dffefff80402e25 0x23efff7ffc020171 0xffffffff80007e7f 0xa7fffffffc0003f3

def z447 : W := mkw 0x0082500014280000 0x0004128000a14000 0x21c070001e000004 0x090e038000f00000

def z448 : W := mkw 0x5935a00000000000 0x02c9ad0000000000 0x5e39800000000002 0x02f1cc0000000000

def z449 : W := mkw 0x7dffffff14be0000 0x33effffff8a5f000 0x7fffffff803e001f 0xa3fffffffc01f000

def z450 : W := mkw 0x8e051a287dbf4148 0x147028d143edfa0a 0xde078f3c7fffe3fb 0xfef03c79e3ffff1f

def z451 : W := mkw 0x24ca5fff96289686 0x212652fffcb144b4 0xa1c67fffde399f9d 0xfd0e33fffef1ccfc

def z452 : W := mkw 0x0082500096289686 0x0004128004b144b4 0xa1c670005e399f8d 0xdd0e338002f1ccfc

def z453 : W := mkw 0x0018a14500c22821 0x0000c50a28061141 0x0038000001c00000 0x0001c000000e0000

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000040398380 0x540000000201cc1c

def z455 : W := mkw 0x24080b4000416810 0x0920405a00020b40 0x0000030000006000 0x0000001800000300

def z456 : W := mkw 0x0040049282009686 0x00020024941004b4 0x000000c380001c00 0x000000061c0000e0

def z457 : W := mkw 0x0008114090e22e25 0x0000408a04871171 0x803803c031e67e76 0xcc01c01e018f33f3

def z458 : W := mkw 0x7ffffffffdfe2e25 0x33ffffffffeff171 0xfffffffffffe7e7f 0xfffffffffffff3f3

def z459 : W := mkw 0xbf650ea86b15d158 0x0dfb28754358ae8a 0x7fc60c304e198181 0x13fe30618270cc0c

def z460 : W := mkw 0x5bb7e0006d9e0000 0x12ddbf00036cf000 0x7fff80006fde0003 0x13fffc00037ef000

def z461 : W := mkw 0x48d7f4bf96289686 0x2246bfa5fcb144b4 0xa1c7fcffde399f9d 0xfd0e3fe7fef1ccfc

def z462 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f3cfb1c67c66 0x0801cf9e7d8e33e3

def z463 : W := mkw 0x0a875000743c0000 0x00543a8003a1e000 0x7fc7f0007e3e000f 0xdbfe3f8003f1f000

def z464 : W := mkw 0x00ca55d29668be86 0x000652ae94b345f4 0xa1fe7ff3fff9ff9f 0xfd0ff3ff9fffcffc

def z465 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e07830c603e606b 0xd2f03c186301f303

def z466 : W := mkw 0x48d7f49296be9686 0x1246bfa494b5f4b4 0xa1c7fcf3de3f9f9d 0xfd0e3fe79ef1fcfc

def z467 : W := mkw 0x59b7f00014be0000 0x12cdbf8000a5f000 0x7ffff000003e000f 0x83ffff800001f000

def z468 : W := mkw 0x79ffe5ff00000000 0x23cfff2ff8000000 0x21fff0ff8000000c 0x210fff87fc000000

def z469 : W := mkw 0x8e1dab6d60d76969 0x0470ed5b6b06bb4b 0x5e39830c21c66062 0x02f1cc18610e3303

def z470 : W := mkw 0x53b2f0007daa0000 0x129d978003ed5000 0x7ff870007fc00007 0xdbffc38003fe0000

def z471 : W := mkw 0x316004800b009010 0x098b002400580480 0x21c000000e000000 0x010e000000700000

def z472 : W := mkw 0x0082500094280604 0x0004128004a14030 0xa1c670c3de381e1d 0xfd0e33861ef1c0f0

def z473 : W := mkw 0x35ea4fd200000000 0x01af527e90000000 0x7ffe7ff38000001f 0xa3fff3ff9c000000

def z474 : W := mkw 0x5b35a00069960000 0x12d9ad00034cb000 0x5e3f800061fe000b 0xd2f1fc00030ff000

def z475 : W := mkw 0xffffefff60154148 0x27ffff7ffb00aa0a 0x7fffffffa006607f 0xa3fffffffd003303

def z476 : W := mkw 0x0000100010200000 0x0000008000810000 0x000070001020000c 0xc800038000810000

def z477 : W := mkw 0x7fef4fc06f5df810 0x1bff7a7e037aefc0 0xfffe0fc07fd9fc17 0xdffff07e03fecfe0

def z478 : W := mkw 0x0000000000000000 0x0000000000000000 0x0006000040380009 0xd00030000201c000

def z479 : W := mkw 0xfffffffff63dd7ce 0x27ffffffffb1eebe 0xfffffffffe3fffff 0xfffffffffff1ffff

def z480 : W := mkw 0x8200000060154148 0x041000000300aa0a 0x0000000020066060 0x0000000001003303

def z481 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e078c3c403f83e9 0x32f03c61e201fc1f

def z482 : W := mkw 0xbfef5ffaff7dffde 0x0dff7affd7fbeffe 0xffffffffffffffff 0xffffffffffffffff

def z483 : W := mkw 0x4897f00014be0000 0x1244bf8000a5f000 0x21c7f0005e3e000d 0xd90e3f8002f1f000

def z484 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000c3000018390 0x2400006180000c1c

def z485 : W := mkw 0x8887503a943c07ce 0x04443a81d4a1e03e 0x0007f03f803e03e8 0x20003f81fc01f01f

def z486 : W := mkw 0x5bf7f492ffbe9686 0x12dfbfa497fdf4b4 0x7ffff0c3fffe1c0f 0xdbffff861ffff0e0

def z487 : W := mkw 0x4a97f0007dbe0000 0x1254bf8003edf000 0x0007f0007ffe0008 0x58003f8003fff000

def z488 : W := mkw 0x82c25492f63dd7ce 0x041612a497b1eebe 0xa1c67cf3fe3ffffd 0xfd0e33e79ff1ffff

def z489 : W := mkw 0x0082501294280686 0x0004128094a14034 0x800670f390381f9c 0xec0033879c81c0fc

def z490 : W := mkw 0x0000100096289686 0x0000008004b144b4 0x80060c305e399f99 0xfc00306182f1ccfc

def z491 : W := mkw 0x0000100090e22e25 0x0000008004871171 0x800070c3b1e67e7c 0xec0003861d8f33f3

def z492 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e078c30603f818b 0xd2f03c618301fc0c

def z493 : W := mkw 0x0008014000402800 0x0000400a00020140 0x0038030021c06002 0x0001c018010e0300

def z494 : W := mkw 0x00c2449206089082 0x0006122490304484 0x21c000000e000000 0x010e000000700000

def z495 : W := mkw 0xffe74eba60154148 0x27ff3a75d300aa0a 0x7fc60c3040198181 0x13fe30618200cc0c

def z496 : W := mkw 0x0010a00000820000 0x0000850000041000 0x0039800021c60002 0x0001cc00010e3000

def z497 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000020266260 0x4400000001013313

def z498 : W := mkw 0x00ca55d79668bea7 0x000652aebcb345f5 0xa1c67fffde39fffd 0xfd0e33fffef1cfff

def z499 : W := mkw 0x000010001daa0000 0x1000008000ed5000 0x000000001fc00000 0x0800000000fe0000

def z500 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f30fa1e6626a 0x2001cf987d0f3313

def z501 : W := mkw 0x8e1dab6d60d76969 0x0470ed5b6b06bb4b 0xde3f8f3c61ffe3fb 0xf6f1fc79e30fff1f

def z502 : W := mkw 0x00c2449202009000 0x0006122490100480 0xa1c67cf3de019c1d 0xfd0e33e79ef00ce0

def z503 : W := mkw 0x0000100014280000 0x0000008000a14000 0x000000005e380000 0x5800000002f1c000

def z504 : W := mkw 0x7d7dafff00000000 0x23ebed7ff8000000 0x5e398fff80000012 0x22f1cc7ffc000000

def z505 : W := mkw 0x8ec74eba661dd1ca 0x04763a75d330ee8e 0x7fc60c304e198181 0x13fe30618270cc0c

def z506 : W := mkw 0x0008014000402800 0x0000400a00020140 0x800003c000007c10 0x0400001e000003e0

def z507 : W := mkw 0x5bb7e0006d1c0000 0x12ddbf000368e000 0x7ffff0004e18000f 0x93ffff800270c000

def z508 : W := mkw 0x31ea55d29f68be96 0x098f52ae94fb45f4 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x00060c3000000019 0xa000306180000000

def z510 : W := mkw 0x5bb7f000fdbe0604 0x12ddbf8007edf030 0xfffff0c3fffe1e1f 0xffffff861ffff0f0

def z511 : W := mkw 0x3778afc56bc3f831 0x09bbc57e2b5e1fc1 0xfff98fcc7fc7fc77 0xdfffcc7e63fe3fe3

def z512 : W := mkw 0x84080b6d80416f6d 0x0420405b6c020b7b 0x80000fff8001fff0 0x2400007ffc000fff

def z513 : W := mkw 0xbf6d0fe86b55f958 0x0dfb687f435aafca 0xfff98fcc7fc7fc77 0xdfffcc7e63fe3fe3

def z514 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8001f3cf80267e78 0x24000f9e7c0133f3

def z515 : W := mkw 0x86000a2860014148 0x0430005143000a0a 0xde000f3c6001e3f3 0xf6f00079e3000f1f

def z516 : W := mkw 0x0200000060140000 0x001000000300a000 0x00000000603e0000 0x500000000301f000

def z517 : W := mkw 0x0040148096289686 0x000200a404b144b4 0xa1c00cc05e399f95 0xdd0e006602f1ccfc

def z518 : W := mkw 0x0000100090a20625 0x0000008004851031 0x0000000000260260 0x0000000000013013

def z519 : W := mkw 0x24480fff82009686 0x2122407ffc1004b4 0x80000fff80019f90 0x2400007ffc000cfc

def z520 : W := mkw 0x0018a14500402800 0x0000c50a28020140 0x8039f3cfb1c07c1e 0xec01cf9e7d8e03e0

def z521 : W := mkw 0x37680fc069000000 0x01bb407e03480000 0x7ff80fc07fc00017 0xdbffc07e03fe0000

def z522 : W := mkw 0x004805c00240b800 0x0002402e001205c0 0xa1f80fc07fc1fc17 0xdd0fc07e03fe0fe0

def z523 : W := mkw 0x0000000000000000 0x0000000000000000 0x0038000031c00006 0xc801c000018e0000

def z524 : W := mkw 0x24ca5fd29669fe96 0x092652fe94b34ff4 0xa1c67ff3de39ff9d 0xfd0e33ff9ef1cffc

def z525 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff80f006fc1e003 0x13ffc078037e0f00

def z526 : W := mkw 0x7d3dab6d00000000 0x23e9ed5b68000000 0x5e39f3cf8000001e 0xa2f1cf9e7c000000

def z527 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000030c00006270 0x2400001860000313

def z528 : W := mkw 0x3778afc56b41f810 0x09bbc57e2b5a0fc0 0xfff9ffcfffc1fc1f 0xffffcffe7ffe0fe0

def z529 : W := mkw 0x06080b4060416800 0x0030405a03020b40 0xde380fc071c1fc17 0xdef1c07e038e0fe0

def z530 : W := mkw 0x0c050a2800000000 0x0060285140000000 0xde078f3c4039839b 0xf6f03c79e201cc1c

def z531 : W := mkw 0x0010b00590a20625 0x000085802c851031 0x0039f00fb1e6026e 0xe801cf807d8f3013

def z532 : W := mkw 0x0805000000140000 0x004028000000a000 0x00078000003e0008 0x00003c000001f000

def z533 : W := mkw 0x881db16d90f62f6d 0x0440ed8b6c87b17b 0x803ff3ffb1fe7ffe 0xec01ff9ffd8ff3ff

def z534 : W := mkw 0x000000000b40b810 0x08000000005a05c0 0x000000001fc01c00 0x0800000000fe00e0

def z535 : W := mkw 0x0008014000402800 0x0000400a00020140 0x803983cc31e67e7e 0xec01cc1e618f33f3

def z536 : W := mkw 0x0e050a2860140000 0x007028514300a000 0x5e078f3c603e001b 0xf2f03c79e301f000

def z537 : W := mkw 0x5bbff1407dfe2800 0x12ddff8a03eff140 0xfffff3c07ffe7c1f 0xdfffff9e03fff3e0

def z538 : W := mkw 0x0a05000060140000 0x005028000300a000 0x5e01800020060002 0x02f00c0001003000

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000c010001c14 0xcc000006008000e0

def z540 : W := mkw 0x5bf7f4927fbe9082 0x12dfbfa493fdf484 0x7ffffc307fff818f 0xdbffffe183fffc0c

def z541 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde01830c2026627a 0xe6f00c1861013313

def z542 : W := mkw 0x06000a0060014000 0x0030005003000a00 0xde018f0c6027e27b 0xf6f00c7863013f13

def z543 : W := mkw 0x51b2e00000000000 0x028d970000000000 0x21f8700000000004 0x010fc38000000000

def z544 : W := mkw 0x00c2549290200604 0x000612a494810030 0xa1c67cf390201e1d 0xed0e33e79c8100f0

def z545 : W := mkw 0x0008114590602e25 0x0000408a2c830171 0x800073cf90207e7c 0xec00039e7c8103f3

def z546 : W := mkw 0x8000000000014148 0x0400000000000a0a 0x800000000001e3e0 0x0400000000000f1f

def z547 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f3cf91c01c1e 0xa801cf9e7c8e00e0

def z548 : W := mkw 0x35680fc000402800 0x01ab407e00020140 0xfff80fc031c07c17 0xcfffc07e018e03e0

def z549 : W := mkw 0x06000a0060014000 0x0030005003000a00 0xde060f306039e39b 0xf6f030798301cf1c

def z550 : W := mkw 0x0010b00590a20625 0x000085802c851031 0x8001f0cf90261e7c 0xec000f867c8130f3

def z551 : W := mkw 0xffffefff6b55f958 0x2fffff7ffb5aafca 0xffffffffffffffff 0xffffffffffffffff

def z552 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c670f39e381f8c 0x290e33879cf1c0fc

def z553 : W := mkw 0x0018a14500000000 0x0000c50a28000000 0x0039830c00000002 0x0001cc1860000000

def z554 : W := mkw 0xdfb7fa287dbf4148 0x16fdbfd143edfa0a 0x7ffffc307fff818f 0xdbffffe183fffc0c

def z555 : W := mkw 0x0018b14010e22800 0x0000c58a00871140 0x8039f3c031e67c1e 0xcc01cf9e018f33e0

def z556 : W := mkw 0x7ff7feba7dbe0000 0x33ffbff5d3edf000 0x7ffffc307ffe000f 0xdbffffe183fff000

def z557 : W := mkw 0x0218b145fdfe2e25 0x1010c58a2feff171 0x8039f3cffffe7e7e 0xfc01cf9e7ffff3f3

def z558 : W := mkw 0x00c2449282009686 0x00061224941004b4 0xa1c67cf380019f9d 0xa50e33e79c000cfc

def z559 : W := mkw 0x0018a14580c22e25 0x0000c50a2c061171 0x803983cfa1c67e72 0x2401cc1e7d0e33f3

def z560 : W := mkw 0x7dffffff90a20625 0x23effffffc851031 0x7fffffff8026027f 0xa3fffffffc013013

def z561 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80380fc031c1fc16 0xcc01c07e018e0fe0

def z562 : W := mkw 0x3738bb45f9e36e35 0x09b9c5da2fcf1b71 0xde39f3cfb1e67e7e 0xeef1cf9e7d8f33f3

def z563 : W := mkw 0x0082501296289686 0x0004128094b144b4 0x80067033de399f88 0x7c0033819ef1ccfc

def z564 : W := mkw 0x0092f01794aa06a7 0x00049780bca55035 0x0007f03f803e03e8 0x20003f81fc01f01f

def z565 : W := mkw 0xdff7febaffbfd7ce 0x16ffbff5d7fdfebe 0xffffffffffffffff 0xffffffffffffffff

def z566 : W := mkw 0x0000000082009686 0x00000000041004b4 0x8000000000019f80 0x0400000000000cfc

def z567 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffffc307fff839f 0xffffffe183fffc1c

def z568 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000200218 0xe400000000010010

def z569 : W := mkw 0x77faefd76b41f810 0x2bbfd77ebb5a0fc0 0xfff87fc3ffc1fc17 0xdfffc3fe1ffe0fe0

def z570 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c60c305e399f81 0x5d0e306182f1ccfc

def z571 : W := mkw 0x7dffefff00402800 0x23efff7ff8020140 0xffffffffb1c07c1f 0xeffffffffd8e03e0

def z572 : W := mkw 0x020000006d1c0000 0x101000000368e000 0x000000004e180000 0x100000000270c000

def z573 : W := mkw 0x51f2f4929faa9686 0x128f97a494fd54b4 0xa1fe7cf3dff99f9d 0xfd0ff3e79effccfc

def z574 : W := mkw 0x0010b00010a20000 0x0000858000851000 0x8039f30c31e6627e 0xec01cf98618f3313

def z575 : W := mkw 0x0000000000000000 0x0000000000000000 0x80078f3c603fe3fb 0xf4003c79e301ff1f

def z576 : W := mkw 0x5bbff1457dfe2821 0x12ddff8a2beff141 0x7ffff30c7ffe606f 0xdbffff9863fff303

def z577 : W := mkw 0x4815a02d00000000 0x2240ad0168000000 0x0001800c00000000 0x00000c0060000000

def z578 : W := mkw 0x37200a0069014010 0x09b9005003480a00 0x5e00000000000000 0x02f0000000000000

def z579 : W := mkw 0x0010a00500000000 0x0000850028000000 0x0001f00f80000008 0x20000f807c000000

def z580 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde018f3c2007e3f2 0x26f00c79e1003f1f

def z581 : W := mkw 0x7fffefff69416810 0x2bffff7ffb4a0b40 0x7fffffffa1c0601f 0xa3fffffffd0e0300

def z582 : W := mkw 0x0000100090200604 0x0000008004810030 0x8001f3cfb0267e7e 0xec000f9e7d8133f3

def z583 : W := mkw 0x5bb7e00069960000 0x12ddbf00034cb000 0x7ffff00021c6000f 0x83ffff80010e3000

def z584 : W := mkw 0x84000a2800014148 0x0420005140000a0a 0x0000030c00006060 0x0000001860000303

def z585 : W := mkw 0x00dae5d700000000 0x0006d72eb8000000 0x21ffffff8000001f 0xa10ffffffc000000

def z586 : W := mkw 0x0000100096eabea7 0x0000008004b755f5 0x800000007fffffe0 0x5c00000003ffffff

def z587 : W := mkw 0x1338b145f9e22e25 0x0099c58a2fcf1171 0xfff9f3cfffe67e7f 0xffffcf9e7fff33f3

def z588 : W := mkw 0x84c25eba9629d7ce 0x042612f5d4b14ebe 0xa1c67fffde39fffd 0xfd0e33fffef1cfff

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001800c00260268 0x20000c0060013013

def z590 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000c0040018011 0xd400006002000c00

def z591 : W := mkw 0x00daf5d796eabea7 0x0006d7aebcb755f5 0xa1fe7cf3dff99f9d 0xfd0ff3e79effccfc

def z592 : W := mkw 0x0200000060014000 0x0010000003000a00 0x800000006001e000 0x5400000003000f00

def z593 : W := mkw 0x84000a2800014148 0x0420005140000a0a 0x00000c3000018180 0x0000006180000c0c

def z594 : W := mkw 0x37280b4069416810 0x09b9405a034a0b40 0x7ff803007fc06007 0xdbffc01803fe0300

def z595 : W := mkw 0x24ca4fff00000000 0x2126527ff8000000 0x21c67fff8000001d 0xa10e33fffc000000

def z596 : W := mkw 0x5bb7f000ffbe9686 0x12ddbf8007fdf4b4 0xfffff0007fff9f8f 0xdfffff8003fffcfc

def z597 : W := mkw 0x1320000069000000 0x0099000003480000 0x7fc000004e000001 0x13fe000002700000

def z598 : W := mkw 0x0218b145fbe3fe35 0x0810c58a2fdf1ff1 0x8039f3cfffe7fe7e 0xfc01cf9e7fff3ff3

def z599 : W := mkw 0x59a7400000000000 0x02cd3a0000000000 0x7fc6000000000001 0x03fe300000000000

def z600 : W := mkw 0x0018a14500c22821 0x0000c50a28061141 0x803983cc31c67c76 0xcc01cc1e618e33e3

def z601 : W := mkw 0x3d6d0fe800000000 0x01eb687f40000000 0x7fff8ffc0000001f 0xa3fffc7fe0000000

def z602 : W := mkw 0x0000000000c22821 0x0000000000061141 0x0000000021c66060 0x00000000010e3303

def z603 : W := mkw 0x00c2449206089082 0x0006122490304484 0xa1c60cf05e199d95 0xdd0e306782f0ccec

def z604 : W := mkw 0x0010b00010a20000 0x0000858000851000 0x0001f00000260008 0x00000f8000013000

def z605 : W := mkw 0x0a15b00070b60000 0x0050ad800385b000 0x5e3ff00071fe000f 0xdaf1ff80038ff000

def z606 : W := mkw 0x0000100096289686 0x0000008004b144b4 0x000000001e001c00 0x0800000000f000e0

def z607 : W := mkw 0x04000a0000014000 0x0020005000000a00 0x80000f000001e010 0x0400007800000f00

def z608 : W := mkw 0x0008014000000000 0x0000400a00000000 0x003803c000000016 0x8001c01e00000000

def z609 : W := mkw 0x51baf1459dea2e25 0x128dd78a2cef5171 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z610 : W := mkw 0x00c2549216289082 0x000612a490b14484 0x21c67c305e39818d 0xd90e33e182f1cc0c

def z611 : W := mkw 0x8805002800140148 0x044028014000a00a 0x0006003000180180 0x000030018000c00c

def z612 : W := mkw 0xffffffe87ffff958 0x1fffffff43ffffca 0xfffffffc7fffffff 0xffffffffe3ffffff

def z613 : W := mkw 0x0e050a2860014000 0x0070285143000a00 0xde078f3c6001e01b 0xf6f03c79e3000f00

def z614 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c07cc3de019c15 0xdd0e03e61ef00ce0

def z615 : W := mkw 0x0000100090e22e25 0x0000008004871171 0x8001830c31e67e7a 0xec000c18618f33f3

def z616 : W := mkw 0x020000006b01d010 0x0810000003580e80 0x000000004e018000 0x1000000002700c00

def z617 : W := mkw 0x3178b5c59be2be35 0x098bc5ae2cdf15f1 0xa1f9f3cfbfe67e7e 0xed0fcf9e7dff33f3

def z618 : W := mkw 0x0008014580402e25 0x0000400a2c020171 0x000000c380001c00 0x000000061c0000e0

def z619 : W := mkw 0x8000000000140148 0x040000000000a00a 0x00000000003e03e0 0x000000000001f01f

def z620 : W := mkw 0x0040149296289686 0x000200a494b144b4 0x80000cf3de399f90 0x7c0000679ef1ccfc

def z621 : W := mkw 0x0c1dbb6d90e22e25 0x0060eddb6c871171 0xde3fffffb1e67e7f 0xeef1fffffd8f33f3

def z622 : W := mkw 0x7fffefff60014000 0x23ffff7ffb000a00 0xffffffffe001e01f 0xf7ffffffff000f00

def z623 : W := mkw 0x7d250a2800000000 0x23e9285140000000 0x5e00000000000000 0x02f0000000000000

def z624 : W := mkw 0x37680fc5eb41fe35 0x09bb407e2f5a0ff1 0xfff80fcfffc1fe77 0xffffc07e7ffe0ff3

def z625 : W := mkw 0x7dffefc000000000 0x03efff7e00000000 0x7fffffc00000001f 0x83fffffe00000000

def z626 : W := mkw 0x0a1db145f0f62e25 0x0050ed8a2f87b171 0xde3ff3cff1fe7e7f 0xfef1ff9e7f8ff3f3

def z627 : W := mkw 0x37280b4069416810 0x09b9405a034a0b40 0xde380f0061c1e013 0xd6f1c078030e0f00

def z628 : W := mkw 0x4897e00000000000 0x0244bf0000000000 0x0007f00000000008 0x00003f8000000000

def z629 : W := mkw 0x0c050a2800000000 0x0060285140000000 0x5e060c3000000001 0x02f0306180000000

def z630 : W := mkw 0x0000000000000000 0x0000000000000000 0x000070c38000001c 0xa00003861c000000

def z631 : W := mkw 0x00c2449200000000 0x0006122490000000 0x21c070c380000004 0x010e03861c000000

def z632 : W := mkw 0x0000000580000625 0x000000002c000031 0x0000000f80000260 0x200000007c000013

def z633 : W := mkw 0x0a05000060140000 0x005028000300a000 0x5e06000040180001 0x12f030000200c000

def z634 : W := mkw 0x8805002800140148 0x044028014000a00a 0x0001800c00060060 0x00000c0060003003

def z635 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xde380fc021c1fc12 0x06f1c07e010e0fe0

def z636 : W := mkw 0x88c754ba963c97ce 0x04463aa5d4b1e4be 0xa1c7fcffde3f9ffd 0xfd0e3fe7fef1fcff

def z637 : W := mkw 0x0008114590e22e25 0x0000408a2c871171 0x800003cfb1e67e70 0x6c00001e7d8f33f3

def z638 : W := mkw 0x00c2548016289000 0x000612a400b14480 0xa1c67cc05e399c1d 0xdd0e33e602f1cce0

def z639 : W := mkw 0x7f3dab6d69416810 0x2bf9ed5b6b4a0b40 0x5e39830c21c06002 0x02f1cc18610e0300

def z640 : W := mkw 0x7fffffffff69fe96 0x2bfffffffffb4ff4 0xfffffffffff9ff9f 0xffffffffffffcffc

def z641 : W := mkw 0x0000001280000686 0x0000000094000034 0x0000003380000380 0x200000019c00001c

def z642 : W := mkw 0xc897e03f00140148 0x2644bf01f800a00a 0x0007f03f803e03e8 0x20003f81fc01f01f

def z643 : W := mkw 0x7dffffff14280000 0x23effffff8a14000 0x7fffffffde38001f 0xfbfffffffef1c000

def z644 : W := mkw 0x0008014500402821 0x0000400a28020141 0x0000030c00006060 0x0000001860000303

def z645 : W := mkw 0x0010b00590a20625 0x000085802c851031 0x0000700380000000 0x000003801c000000

def z646 : W := mkw 0x0010a00500820021 0x0000850028041001 0x0001800c00060060 0x00000c0060003003

def z647 : W := mkw 0x0040048002009000 0x0002002400100480 0x21c00c004e018001 0x110e006002700c00

def z648 : W := mkw 0x7fffefff6b01d010 0x2bffff7ffb580e80 0x7fffffffce01801f 0xb3fffffffe700c00

def z649 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f0c3b1e61c0e 0xc801cf861d8f30e0

def z650 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e078f3c601fe1e3 0x12f03c79e300ff0f

def z651 : W := mkw 0x5fb7fa287dbe0000 0x12fdbfd143edf000 0x7fffff3c7ffe001f 0xfbfffff9e3fff000

def z652 : W := mkw 0x0040049202009082 0x0002002490100484 0x00000c3000018180 0x0000006180000c0c

def z653 : W := mkw 0x8418bb6d90e36f6d 0x0420c5db6c871b7b 0x8039ffffb1e7fffe 0xec01cffffd8f3fff

def z654 : W := mkw 0x5130a00009820000 0x12898500004c1000 0x0038000001c00000 0x0001c000000e0000

def z655 : W := mkw 0x37faffd7ffebfeb7 0x09bfd7febfff5ff5 0xffffffffffffffff 0xffffffffffffffff

def z656 : W := mkw 0x37600e806b01d010 0x09bb007403580e80 0xffc00cc05e019c15 0xdffe006602f00ce0

def z657 : W := mkw 0x4897f03f14be0000 0x3244bf81f8a5f000 0x0007f03f803e0008 0x20003f81fc01f000

def z658 : W := mkw 0x5ba740006d1c0000 0x12dd3a000368e000 0x7fc780006e3e000b 0xd3fe3c000371f000

def z659 : W := mkw 0x0ac75492f63c9686 0x00563aa497b1e4b4 0xffc7fcf3fe3f9f9f 0xfffe3fe79ff1fcfc

def z660 : W := mkw 0x7fffffc5fffffe35 0x1bfffffe2ffffff1 0xffffffcffffffe7f 0xfffffffe7ffffff3

def z661 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fff8f3c00000003 0x03fffc79e0000000

def z662 : W := mkw 0xbf7dbfedfbf7ff7d 0x0dfbedff6fdfbffb 0xffffffffffffffff 0xffffffffffffffff

def z663 : W := mkw 0x7bfff5c07ffeb810 0x1bdfffae03fff5c0 0x7ffff0c07ffe1c0f 0xdbffff8603fff0e0

def z664 : W := mkw 0x5ba750007d3c0000 0x12dd3a8003e9e000 0x7fc670005e38000d 0xdbfe338002f1c000

def z665 : W := mkw 0x7def4ffa00000000 0x23ef7a7fd0000000 0x7ffe0ff000000017 0x83fff07f80000000

def z666 : W := mkw 0x0082400000000000 0x0004120000000000 0x21c670000000000d 0x810e338000000000

def z667 : W := mkw 0x86000a2860154148 0x043000514300aa0a 0x80000f3c603fe3f0 0x74000079e301ff1f

def z668 : W := mkw 0x028250007dbe0000 0x1014128003edf000 0x21c670007ffe000d 0xd90e338003fff000

def z669 : W := mkw 0x489ff17f90e22e25 0x2244ff8bfc871171 0x803ff3ffb1e67e7e 0xec01ff9ffd8f33f3

def z670 : W := mkw 0x84400eba8201d7ce 0x04220075d4100ebe 0x80000fff8001fff0 0x2400007ffc000fff

def z671 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001830c20066062 0x00000c1861003303

def z672 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde060c3040398399 0xf6f030618201cc1c

def z673 : W := mkw 0x0082501294280686 0x0004128094a14034 0x80067c33c0398399 0xf40033e19e01cc1c

def z674 : W := mkw 0x7fffefff60140000 0x23ffff7ffb00a000 0x7fffffffe03e001f 0xf3ffffffff01f000

def z675 : W := mkw 0x51b2f0001daa0000 0x128d978000ed5000 0x21f9f0003fe6000e 0xc90fcf8001ff3000

def z676 : W := mkw 0x0018b14510e22821 0x0000c58a28871141 0x0039f30c31e6606e 0xc801cf98618f3303

def z677 : W := mkw 0x7d3dab6d00c22821 0x23e9ed5b68061141 0x5e39830c21c66062 0x02f1cc18610e3303

def z678 : W := mkw 0x5bf7f4807fbe9000 0x12dfbfa403fdf480 0xfffffcc07fff9c1f 0xdfffffe603fffce0

def z679 : W := mkw 0x04000a2800000000 0x0020005140000000 0x00000f3c00000010 0x20000079e0000000

def z680 : W := mkw 0x7dffffff10a20000 0x23effffff8851000 0x7fffffffb1e6001f 0xebfffffffd8f3000

def z681 : W := mkw 0x84000a2800014148 0x0420005140000a0a 0x80018f3c2027e3fa 0xe4000c79e1013f1f

def z682 : W := mkw 0x0805002800000000 0x0040280140000000 0x0007803c00000008 0x20003c01e0000000

def z683 : W := mkw 0x3778bfc07be3f810 0x09bbc5fe03df1fc0 0xfff9ffc07fe7fc1f 0xdfffcffe03ff3fe0

def z684 : W := mkw 0xfffffffff0f76f6d 0x27ffffffff87bb7b 0xfffffffff1ffffff 0xffffffffff8fffff

def z685 : W := mkw 0x37ea5fd2ff69fe96 0x09bf52fe97fb4ff4 0xfff87fc3ffc1fc17 0xdfffc3fe1ffe0fe0

def z686 : W := mkw 0x1120000000000000 0x0089000000000000 0x7ff8000000000007 0x83ffc00000000000

def z687 : W := mkw 0xa4480fff00014148 0x2522407ff8000a0a 0x80000fff8001e3f0 0x2400007ffc000f1f

def z688 : W := mkw 0x7fffefff6d1c0000 0x33ffff7ffb68e000 0x7fffffffce18001f 0xb3fffffffe70c000

def z689 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0xa1c00fc05e01fc15 0xdd0e007e02f00fe0

def z690 : W := mkw 0x3f6d0fc06b55f810 0x09fb687e035aafc0 0xffff8fc07ffffc1f 0xdffffc7e03ffffe0

def z691 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde060f3c4019e3f1 0x36f03079e200cf1f

def z692 : W := mkw 0x5b3db145f9f62e25 0x12d9ed8a2fcfb171 0xde39f3cfb1e67e7e 0xeef1cf9e7d8f33f3

def z693 : W := mkw 0xc897f02814be0148 0x1644bf8140a5f00a 0x0007f03c003e03e8 0x20003f81e001f01f

def z694 : W := mkw 0x8805002800140148 0x044028014000a00a 0x8007833c203e63fa 0xe4003c19e101f31f

def z695 : W := mkw 0x7dffffff1daa0000 0x33effffff8ed5000 0x7fffffff9fc0001f 0xabfffffffcfe0000

def z696 : W := mkw 0x8edffffff6ffffef 0x0476ffffffb7ffff 0xffffffffffffffff 0xffffffffffffffff

def z697 : W := mkw 0x7de75eba96289686 0x23ef3af5d4b144b4 0xffc67cf3de399f9d 0xfffe33e79ef1ccfc

def z698 : W := mkw 0x8a05002860140148 0x045028014300a00a 0x5e07803c603e03eb 0xf2f03c01e301f01f

def z699 : W := mkw 0x3128014009402810 0x0989400a004a0140 0x0038000001c00000 0x0001c000000e0000

def z700 : W := mkw 0xbf6d0fe86b55f958 0x0dfb687f435aafca 0xfffe0ff07fd9fd97 0xdffff07f83fecfec

def z701 : W := mkw 0x04000a0000000000 0x0020005000000000 0x5e000f0000000013 0x82f0007800000000

def z702 : W := mkw 0x0092f00014aa0000 0x0004978000a55000 0x21fff0007ffe000f 0xd90fff8003fff000

def z703 : W := mkw 0x7fbffb6d7dbe0000 0x33fdffdb6bedf000 0x7ffff30c7ffe000f 0xdbffff9863fff000

def z704 : W := mkw 0x7d3dab6d00000000 0x23e9ed5b68000000 0x5e3f8f3c0000001b 0xa2f1fc79e0000000

def z705 : W := mkw 0x0805000000000000 0x0040280000000000 0x5e0780000000000b 0x82f03c0000000000

def z706 : W := mkw 0x8218b145f0f76f6d 0x0410c58a2f87bb7b 0x8039f3cff1fffffe 0xfc01cf9e7f8fffff

def z707 : W := mkw 0x5baf4145ed5c2e25 0x12dd7a0a2f6ae171 0xffc603cfce187e71 0x37fe301e7e70c3f3

def z708 : W := mkw 0x59b7e01700000000 0x22cdbf00b8000000 0x7ffff0038000000f 0x83ffff801c000000

def z709 : W := mkw 0x3770be85fba3d635 0x09bb85f42fdd1eb1 0x7fc1fc0fce278269 0x33fe0fe07e713c13

def z710 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c7fcffde3f9ffd 0xfd0e3fe7fef1fcff

def z711 : W := mkw 0x5bb7f0057dbe0000 0x12ddbf802bedf000 0x7ffff00ffffe000f 0xfbffff807ffff000

def z712 : W := mkw 0x35681fc090e22e25 0x01ab40fe04871171 0xfff80fc031e67e77 0xcfffc07e018f33f3

def z713 : W := mkw 0x4a97e03f6b41f810 0x2a54bf01fb5a0fc0 0x8007f03fffc1fc08 0x7c003f81fffe0fe0

def z714 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffffb1c0001f 0xebfffffffd8e0000

def z715 : W := mkw 0x336805c06b40b810 0x099b402e035a05c0 0x7ff800c03fc01c06 0x0bffc00601fe00e0

def z716 : W := mkw 0x1320000069000000 0x0099000003480000 0x7ff800003fc00006 0x0bffc00001fe0000

def z717 : W := mkw 0x1320000069140000 0x009900000348a000 0x7ff800007ffe0007 0xdbffc00003fff000

def z718 : W := mkw 0x24480fff8240bea7 0x2122407ffc1205f5 0x80000fff8001fff0 0x2400007ffc000fff

def z719 : W := mkw 0xdbb7f0007dbf4148 0x16ddbf8003edfa0a 0xfffff30c7fffe3ff 0xffffff9863ffff1f

def z720 : W := mkw 0x5bb7f02d7dbe0000 0x32ddbf816bedf000 0x7ffff00c7ffe000f 0xdbffff8063fff000

def z721 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0307ffe038f 0xfbffff8183fff01c

def z722 : W := mkw 0x02001000f0e36e25 0x0010008007871b71 0x8000000071e7fe60 0x5c000000038f3ff3

def z723 : W := mkw 0x336805c06b40b810 0x099b402e035a05c0 0xfff80cc07fc19c17 0xdfffc06603fe0ce0

def z724 : W := mkw 0x1320000069000000 0x0099000003480000 0xfff80c007fc18017 0xdfffc06003fe0c00

def z725 : W := mkw 0x4c97ea3f00000000 0x2264bf51f8000000 0x5e07f33f8000000a 0x22f03f99fc000000

def z726 : W := mkw 0x0218a1456b41f810 0x0810c50a2b5a0fc0 0x8039f3cfffc1fc1e 0xfc01cf9e7ffe0fe0

def z727 : W := mkw 0x24480fff0240b810 0x2922407ff81205c0 0x00000fff80001c10 0x2000007ffc0000e0

def z728 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffffe03fe3ff 0xf7ffffffff01ff1f

def z729 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff98fcc7fc7fc77 0xdfffcc7e63fe3fe3

def z730 : W := mkw 0x7de75eba90e22e25 0x23ef3af5d4871171 0xffc60c3031e67e61 0x4ffe3061818f33f3

def z731 : W := mkw 0x7dffefff0b40b810 0x2befff7ff85a05c0 0xffffffffdfc19c1f 0xfffffffffefe0ce0

def z732 : W := mkw 0x5bb7f0287dbe0000 0x12ddbf8143edf000 0x7ffff03c7ffe000f 0xfbffff81e3fff000

def z733 : W := mkw 0xf3fae5d760154148 0x279fd72ebb00aa0a 0xa1f870c3e03fe3e4 0x550fc3861f01ff1f

def z734 : W := mkw 0x7dffefff0240b800 0x23efff7ff81205c0 0xffffffffffc1fc1f 0xfffffffffffe0fe0

def z735 : W := mkw 0x0c15aa2d00000000 0x0060ad5168000000 0x5e07ff3f8000001b 0xa2f03ff9fc000000

def z736 : W := mkw 0x7de74eba00000000 0x23ef3a75d0000000 0x7fc67c3380000009 0x23fe33e19c000000

def z737 : W := mkw 0x35681fc096289686 0x01ab40fe04b144b4 0xfff80fc05e399f97 0xdfffc07e02f1ccfc

def z738 : W := mkw 0x5330a00069820000 0x12998500034c1000 0x7ff800007fc00007 0xdbffc00003fe0000

def z739 : W := mkw 0x1138a14500000000 0x0089c50a28000000 0x7ff9f3cf8000001f 0xa3ffcf9e7c000000

def z740 : W := mkw 0x59b7e00009000000 0x02cdbf0000480000 0x7ffff0001fc0000f 0x8bffff8000fe0000

def z741 : W := mkw 0x24480fd20241f810 0x0922407e90120fc0 0x80000ff38001fc10 0x2400007f9c000fe0

def z742 : W := mkw 0x35680fc000000000 0x01ab407e00000000 0x7ff87fc38000001f 0xa3ffc3fe1c000000

def z743 : W := mkw 0x5bb7f000fdbe0604 0x12ddbf8007edf030 0x7ffff0c3fffe1c0f 0xdbffff861ffff0e0

def z744 : W := mkw 0x9b25002869140148 0x04d928014348a00a 0x7fff803c7ffe03ef 0xfbfffc01e3fff01f

def z745 : W := mkw 0x37680fd76b41f810 0x29bb407ebb5a0fc0 0xfff80fc3ffc1fc17 0xdfffc07e1ffe0fe0

def z746 : W := mkw 0xca97e03f60154148 0x2654bf01fb00aa0a 0x8007f03fe03fe3e8 0x74003f81ff01ff1f

def z747 : W := mkw 0x7dffefff00402800 0x23efff7ff8020140 0xffffffff80007c1f 0xa7fffffffc0003e0

def z748 : W := mkw 0x37600e806b41f810 0x09bb0074035a0fc0 0xfff80c007fc1fc07 0xdfffc06003fe0fe0

def z749 : W := mkw 0xb7680fc06b55f958 0x0dbb407e035aafca 0xfff98fcc7fffffff 0xffffcc7e63ffffff

def z750 : W := mkw 0x82001000ff7dffde 0x0c10008007fbeffe 0x800000007fffffe0 0x5c00000003ffffff

def z751 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ff870001fc00004 0x0bffc38000fe0000

def z752 : W := mkw 0x37aa5b52fd696e96 0x09bd52da97eb4b74 0x5e3e7333a1f8638a 0x22f1f3999d0fc31c

def z753 : W := mkw 0x37680fed6b41f810 0x29bb407f6b5a0fc0 0xfff80fcc7fc1fc17 0xdfffc07e63fe0fe0

def z754 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffffa006607f 0xa3fffffffd003303

def z755 : W := mkw 0x8ec75ebaf63dd7ce 0x04763af5d7b1eebe 0x7fc1f3cfbe067c66 0x0bfe0f9e7df033e3

def z756 : W := mkw 0x59f7e4bf00000000 0x22cfbf25f8000000 0x7ffffcff8000001f 0xa3ffffe7fc000000

def z757 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffff3f8000000b 0x23fffff9fc000000

def z758 : W := mkw 0xfdffefff00014148 0x27efff7ff8000a0a 0xffffffffa027e3ff 0xe7fffffffd013f1f

def z759 : W := mkw 0x79ffe5d700000000 0x23cfff2eb8000000 0x7ffffcf38000001f 0xa3ffffe79c000000

def z760 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ff9f0007fc60007 0xdbffcf8003fe3000

def z761 : W := mkw 0x02001000ff29d696 0x0810008007f94eb4 0x800000005e399f80 0x5c00000002f1ccfc

def z762 : W := mkw 0x7dffefff02009000 0x23efff7ff8100480 0xffffffff80019c1f 0xa7fffffffc000ce0

def z763 : W := mkw 0x5ba750007d3c0000 0x12dd3a8003e9e000 0x7ffe70007ff8000f 0xdbfff38003ffc000

def z764 : W := mkw 0xa4480fe80241f958 0x0d22407f40120fca 0x80000fcc0001fc70 0x0400007e60000fe3

def z765 : W := mkw 0x35680fc00240b800 0x01ab407e001205c0 0xfff80fc07fc1fc17 0xdfffc07e03fe0fe0

def z766 : W := mkw 0x82001000ffbfd7ce 0x1410008007fdfebe 0x800000007fffffe0 0x5c00000003ffffff

def z767 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803ff3cff1fe7e7f 0xfc01ff9e7f8ff3f3

def z768 : W := mkw 0x59ffe5d700000000 0x02cfff2eb8000000 0x7fffffff8000001f 0xa3fffffffc000000

def z769 : W := mkw 0x5ba750007dbe0000 0x12dd3a8003edf000 0x7ffe00007ffe0007 0xdbfff00003fff000

def z770 : W := mkw 0x0c051a2890e22e25 0x006028d144871171 0xde078f3c31e67e7b 0xeef03c79e18f33f3

def z771 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffffde00001f 0xfbfffffffef00000

def z772 : W := mkw 0xfdffefff00140148 0x27efff7ff800a00a 0xffffffffc03f83ff 0xf7fffffffe01fc1f

def z773 : W := mkw 0x1b35b00079b60000 0x00d9ad8003cdb000 0x7ffff0007ffe000f 0xdbffff8003fff000

def z774 : W := mkw 0x5bb7f03ffdbe0625 0x32ddbf81ffedf031 0x7ffff03ffffe026f 0xfbffff81fffff013

def z775 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffffc007fff801f 0xdfffffe003fffc00

def z776 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffffc038001f 0xf3fffffffe01c000

def z777 : W := mkw 0x5b75a492eb969686 0x12dbad24975cb4b4 0xde398cf3a1c79f92 0x26f1cc679d0e3cfc

def z778 : W := mkw 0x5bb7f000fdbe0604 0x12ddbf8007edf030 0xfffff3cffffe7e7f 0xffffff9e7ffff3f3

def z779 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7fff80007ffe0003 0x5bfffc0003fff000

def z780 : W := mkw 0xdf3dab6d69d76969 0x16f9ed5b6b4ebb4b 0x5e39830c21c66062 0x02f1cc18610e3303

def z781 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffe70007ffe0005 0x5bfff38003fff000

def z782 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f3cfb1e67e6e 0x2801cf9e7d8f33f3

def z783 : W := mkw 0xfdffefff00014148 0x27efff7ff8000a0a 0x7fffffff8000607f 0xa3fffffffc000303

def z784 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80000ff00001ff90 0x2400007f80000ffc

def z785 : W := mkw 0x8e1dbb6df0f76f6d 0x0470eddb6f87bb7b 0x5e3e7cf3d1d99d85 0x1af1f3e79e8eccec

def z786 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0003ffe000e 0x0bffff8001fff000

def z787 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039f3cfb1e67e66 0x4c01cf9e7d8f33f3

def z788 : W := mkw 0x7def4ffa00000000 0x23ef7a7fd0000000 0x7ffe7ff38000001f 0xa3fff3ff9c000000

def z789 : W := mkw 0xb7680fe86b41f958 0x0dbb407f435a0fca 0xfffe0ffc7ff9ffff 0xfffff07fe3ffcfff

def z790 : W := mkw 0x00dae5d706cab8a3 0x0006d72eb83655c5 0x21ff8f3c6fdfe1e3 0x110ffc79e37eff0f

def z791 : W := mkw 0x7d7dafed00000000 0x23ebed7f68000000 0x7ff9ffcf8000001f 0xa3ffcffe7c000000

def z792 : W := mkw 0x02001000fdbe0625 0x1010008007edf031 0x000000007ffe0260 0x5800000003fff013

def z793 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0x5e078f3c603fe3eb 0x32f03c79e301ff1f

def z794 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfffe0ff07fd9fd97 0xdffff07f83fecfec

def z795 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffff8026027f 0xa3fffffffc013013

def z796 : W := mkw 0x24480fd70241f810 0x2922407eb8120fc0 0x80000fc38001fc10 0x0400007e1c000fe0

def z797 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffe7cf38000001d 0xa3fff3e79c000000

def z798 : W := mkw 0x5ba740006d1c0000 0x12dd3a000368e000 0x7fff80007ffe000f 0xdbfffc0003fff000

def z799 : W := mkw 0x24480fd28241fe96 0x0922407e94120ff4 0x80000fc38001fc10 0x0400007e1c000fe0

def z800 : W := mkw 0xa4480fc00241f958 0x0d22407e00120fca 0x80000fc00001fff0 0x0400007e00000fff

def z801 : W := mkw 0x82001000f6ffffef 0x0410008007b7ffff 0x800000007fffffe0 0x5c00000003ffffff

def z802 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffffc307fff818f 0xdbffffe183fffc0c

def z803 : W := mkw 0x59b7e00500000000 0x02cdbf0028000000 0x7ffff00f8000000f 0xa3ffff807c000000

def z804 : W := mkw 0xfdffefff0241f958 0x2fefff7ff8120fca 0xffffffff8001ffff 0xa7fffffffc000fff

def z805 : W := mkw 0x7dffefff00820021 0x23efff7ff8041001 0x7fffffff8006007f 0xa3fffffffc003003

def z806 : W := mkw 0x24480fff8241fe35 0x2922407ffc120ff1 0x80000fff8001fe70 0x2400007ffc000ff3

def z807 : W := mkw 0x37680ffa6b41f810 0x29bb407fd35a0fc0 0xfff80ff07fc1fc17 0xdfffc07f83fe0fe0

def z808 : W := mkw 0x82001000f63dd7ce 0x0410008007b1eebe 0x800000005e399f80 0x5c00000002f1ccfc

def z809 : W := mkw 0x336805c06b41f810 0x099b402e035a0fc0 0xfff800c07fc1fc07 0xdfffc00603fe0fe0

def z810 : W := mkw 0x1320000069014000 0x0099000003480a00 0xfff800007fc1e007 0xdfffc00003fe0f00

def z811 : W := mkw 0x59e7449200000000 0x02cf3a2490000000 0x7fc67cf38000001d 0xa3fe33e79c000000

def z812 : W := mkw 0x13b2f0007daa0000 0x009d978003ed5000 0x7ffff0007ffe000f 0xdbffff8003fff000

def z813 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff98fc07fe7fc1f 0xdfffcc7e03ff3fe0

def z814 : W := mkw 0x5ba7400069000000 0x02dd3a0003480000 0x7ffe00007fc00007 0xdbfff00003fe0000

def z815 : W := mkw 0xb96d05e80b54b958 0x0dcb682f405aa5ca 0x21ff80fc1ffe1fec 0x290ffc07e0fff0ff

def z816 : W := mkw 0x59b7e00000000000 0x02cdbf0000000000 0x7ffff0c38000001f 0xa3ffff861c000000

def z817 : W := mkw 0x132010007d280000 0x0099008003e94000 0x7ff800007ff80007 0xdbffc00003ffc000

def z818 : W := mkw 0x4897f00094be0604 0x1244bf8004a5f030 0x0007f003803e0208 0x20003f801c01f010

def z819 : W := mkw 0x37680fc56b41f831 0x09bb407e2b5a0fc1 0xfff80fcc7fc1fc77 0xdfffc07e63fe0fe3

def z820 : W := mkw 0x00c2549296aa9686 0x000612a494b554b4 0xa1c67cf3ffff9f9d 0xfd0e33e79ffffcfc

def z821 : W := mkw 0x7dffefff0241f810 0x2befff7ff8120fc0 0xffffffffb1c1fc1f 0xeffffffffd8e0fe0

def z822 : W := mkw 0x0008114090602e04 0x0000408a04830170 0x8039f3cfb1e67e7e 0xec01cf9e7d8f33f3

def z823 : W := mkw 0x02001000f0f62e25 0x001000800787b171 0x8000000071fe7e60 0x5c000000038ff3f3

def z824 : W := mkw 0x1120000009000000 0x0089000000480000 0x7ff800001fc00007 0x8bffc00000fe0000

def z825 : W := mkw 0x7de74eba00000000 0x23ef3a75d0000000 0x7fc7ffff8000001f 0xa3fe3ffffc000000

def z826 : W := mkw 0x7dffefff00402800 0x23efff7ff8020140 0x7fffffff91c01c1f 0xabfffffffc8e00e0

def z827 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffe70007fd80007 0xdbfff38003fec000

def z828 : W := mkw 0x8218a14560154148 0x0410c50a2b00aa0a 0x8039f3cfe03fe3fe 0xf401cf9e7f01ff1f

def z829 : W := mkw 0x1330b005f9a20625 0x009985802fcd1031 0x7ff9f00fffe6026f 0xfbffcf807fff3013

def z830 : W := mkw 0x53b2f0007daa0000 0x129d978003ed5000 0x7ff870005fc00005 0x1bffc38002fe0000

def z831 : W := mkw 0x1320000069000000 0x0099000003480000 0x7ffe00007ff8000f 0xdbfff00003ffc000

def z832 : W := mkw 0x6cdfffc016fff810 0x1b66fffe00b7ffc0 0x8007ffc0003ffc18 0x04003ffe0001ffe0

def z833 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff80cc07fc19c07 0xdbffc06603fe0ce0

def z834 : W := mkw 0x02001000fdfe2e25 0x1010008007eff171 0x000000007ffe1c00 0x5800000003fff0e0

def z835 : W := mkw 0x7df7eebf00000000 0x23efbf75f8000000 0x7fc7fcff8000001d 0xa3fe3fe7fc000000

def z836 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c7ffffde399f9f 0xfd0e3ffffef1ccfc

def z837 : W := mkw 0x5bb7e0006d9e0000 0x12ddbf00036cf000 0x7ff980002fc60002 0x03ffcc00017e3000

def z838 : W := mkw 0x5bb7e00069140000 0x02ddbf000348a000 0x7ffff0007ffe000f 0xdbffff8003fff000

def z839 : W := mkw 0xb7680fe86b55f958 0x0dbb407f435aafca 0xfff80ffc7ffffff7 0xffffc07fe3ffffff

def z840 : W := mkw 0x24480fc08241fe14 0x0922407e04120ff0 0x80000fc38001fe10 0x2400007e1c000ff0

def z841 : W := mkw 0x02001000ffebfeb7 0x0810008007ff5ff5 0x800000007fffffe0 0x5c00000003ffffff

def z842 : W := mkw 0x1320000069000000 0x0099000003480000 0x7ff980007fe6000f 0xdbffcc0003ff3000

def z843 : W := mkw 0x02c244926b41f810 0x08161224935a0fc0 0xa1c67cf3ffc1fc1d 0xfd0e33e79ffe0fe0

def z844 : W := mkw 0x02001000fffffe96 0x1810008007fffff4 0x800000007fffff80 0x5c00000003fffffc

def z845 : W := mkw 0x5bb7f00079a20000 0x02ddbf8003cd1000 0x7ffff0007fe6000f 0xdbffff8003ff3000

def z846 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffff8000627f 0xa7fffffffc000313

def z847 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xffffff3c7fffe3ff 0xfffffff9e3ffff1f

def z848 : W := mkw 0x7dffefff00402800 0x23efff7ff8020140 0x7fffffffa1c0601f 0xa3fffffffd0e0300

def z849 : W := mkw 0x5b35a00069960000 0x12d9ad00034cb000 0x7ff980006fc60003 0x13ffcc00037e3000

def z850 : W := mkw 0x1320000069000000 0x0099000003480000 0x7ff800005fc00005 0x1bffc00002fe0000

def z851 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80fc05fc1fc15 0x1fffc07e02fe0fe0

def z852 : W := mkw 0x336805c06b40b810 0x099b402e035a05c0 0xfff803c07fc07c17 0xdfffc01e03fe03e0

def z853 : W := mkw 0x1320000069000000 0x0099000003480000 0xfff803007fc06017 0xdfffc01803fe0300

def z854 : W := mkw 0x3578afc500000000 0x01abc57e28000000 0x7ff87fc380000017 0x83ffc3fe1c000000

def z855 : W := mkw 0x1ba750007d3c0000 0x00dd3a8003e9e000 0x7ffff0007ffe000f 0xdbffff8003fff000

def z856 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ff9ffcf80000017 0x83ffcffe7c000000

def z857 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffff8001839f 0xa7fffffffc000c1c

def z858 : W := mkw 0xb7680fe86b41f958 0x0dbb407f435a0fca 0xfff80fcc7fc1fc77 0xdfffc07e63fe0fe3

def z859 : W := mkw 0x5bb7e0006d1c0000 0x12ddbf000368e000 0x7ffff0007fd8000f 0xdbffff8003fec000

def z860 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffe70005ff8000d 0xdbfff38002ffc000

def z861 : W := mkw 0x59b7f0001daa0000 0x12cdbf8000ed5000 0x7ffe70001fc00005 0x0bfff38000fe0000

def z862 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0xa1f9f3cfffe67e7f 0xfd0fcf9e7fff33f3

def z863 : W := mkw 0x593da14500000000 0x02c9ed0a28000000 0x5e39f3cf8000001e 0xa2f1cf9e7c000000

def z864 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff80fc03fc07c17 0x8bffc07e01fe03e0

def z865 : W := mkw 0x0c050a2800000000 0x0060285140000000 0xde078f3c603fe3fb 0xf6f03c79e301ff1f

def z866 : W := mkw 0x0a97f00074be0000 0x0054bf8003a5f000 0x7ffff0007ffe000f 0xdbffff8003fff000

def z867 : W := mkw 0x6cdfefff0241f810 0x2b66ff7ff8120fc0 0x8007ffff8001fc18 0x24003ffffc000fe0

def z868 : W := mkw 0x5bb7e0006d9e0000 0x12ddbf00036cf000 0x7fff80007fde0007 0xdbfffc0003fef000

def z869 : W := mkw 0x35faefd700000000 0x01afd77eb8000000 0x7fffffff8000001f 0xa3fffffffc000000

def z870 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x00000cc000019c00 0x0000006600000ce0

def z871 : W := mkw 0x13a25012fd280686 0x009d128097e94034 0x7ffe7033fff8038f 0xfbfff3819fffc01c

def z872 : W := mkw 0x7dffefff09820000 0x33efff7ff84c1000 0x7fffffff81c0001f 0xa3fffffffc0e0000

def z873 : W := mkw 0x5bb7f0007daa0000 0x12ddbf8003ed5000 0x7ffff0007fc0000f 0xdbffff8003fe0000

def z874 : W := mkw 0x75faefd700000000 0x23afd77eb8000000 0x7ff9ffcf8000001f 0xa3ffcffe7c000000

def z875 : W := mkw 0x24480ffa0241f810 0x2922407fd0120fc0 0x80000ff00001fc10 0x0400007f80000fe0

def z876 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80000fc02001fc12 0xc400007e01000fe0

def z877 : W := mkw 0xdbb7f0287dbe0148 0x16ddbf8143edf00a 0xfffff33c7ffe63ff 0xffffff99e3fff31f

def z878 : W := mkw 0x336805c06b40b810 0x099b402e035a05c0 0x7ff800c05fc01c05 0x1bffc00602fe00e0

def z879 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80cc07fc1fc05 0x5fffc06603fe0fe0

def z880 : W := mkw 0x37680fc06b40b810 0x09bb407e035a05c0 0x7ff80fc07fc01c17 0xdbffc07e03fe00e0

def z881 : W := mkw 0x1320100079a20000 0x0099008003cd1000 0x7ff800007fe60007 0xdbffc00003ff3000

def z882 : W := mkw 0x7d3dbb6d96289686 0x23e9eddb6cb144b4 0xde39830c5e399f82 0x5ef1cc1862f1ccfc

def z883 : W := mkw 0x24480fc50241f831 0x0922407e28120fc1 0x80000fcc0001fc70 0x0400007e60000fe3

def z884 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803fffffb1e67e7f 0xec01fffffd8f33f3

def z885 : W := mkw 0x1330a00069000000 0x0099850003480000 0x7ff9f0007fc0000f 0xdbffcf8003fe0000

def z886 : W := mkw 0x37680fe86b41f810 0x09bb407f435a0fc0 0xfff80ffc7fc1fc17 0xffffc07fe3fe0fe0

def z887 : W := mkw 0x7dffefc500000000 0x03efff7e28000000 0x7fffffcf8000001f 0xa3fffffe7c000000

def z888 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffe7ff380000017 0x83fff3ff9c000000

def z889 : W := mkw 0x5db7ea3f00000000 0x22edbf51f8000000 0x7fffff3f8000001f 0xa3fffff9fc000000

def z890 : W := mkw 0x9320000069154148 0x049900000348aa0a 0xfff800007fffe3e7 0xdfffc00003ffff1f

def z891 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039ffcff1e7fe7f 0xfc01cffe7f8f3ff3

def z892 : W := mkw 0x7dbfeb7f00000000 0x23edff5bf8000000 0x5e3fff3f8000001b 0xa2f1fff9fc000000

def z893 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80fc07ff9ff97 0xdfffc07e03ffcffc

def z894 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffffc001801f 0xf7fffffffe000c00

def z895 : W := mkw 0xfdffefff00140148 0x27efff7ff800a00a 0x7fffffff8006007f 0xa3fffffffc003003

def z896 : W := mkw 0x7dffefff00c22821 0x23efff7ff8061141 0x7fffffff81c0001f 0xa3fffffffc0e0000

def z897 : W := mkw 0x79ffe5d700000000 0x23cfff2eb8000000 0x7ffe70c380000005 0x03fff3861c000000

def z898 : W := mkw 0xdbb7f02dfdbe076d 0x16ddbf816fedf03b 0x7ffff03ffffe03ef 0xfbffff81fffff01f

def z899 : W := mkw 0x71fae5d700000000 0x238fd72eb8000000 0x7ff870c380000007 0x83ffc3861c000000

def z900 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0c3fffe001f 0xfbffff861ffff000

def z901 : W := mkw 0x5dbfeb6d00000000 0x02edff5b68000000 0x7fffffff8000001f 0xa3fffffffc000000

def z902 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde078f3c203fe3fa 0x26f03c79e101ff1f

def z903 : W := mkw 0x7dffefff0241f810 0x2befff7ff8120fc0 0xffffffffde01fc1f 0xfffffffffef00fe0

def z904 : W := mkw 0x3d7dafed00000000 0x01ebed7f68000000 0x7fffffff8000001f 0xa3fffffffc000000

def z905 : W := mkw 0x5bb7f0127dbe0082 0x12ddbf8093edf004 0x7ffff0307ffe018f 0xdbffff8183fff00c

def z906 : W := mkw 0x1330b00079a20000 0x0099858003cd1000 0x7ff870007fc00007 0xdbffc38003fe0000

def z907 : W := mkw 0x0c1dab6d00000000 0x0060ed5b68000000 0x5e39f3cf8000001e 0xa2f1cf9e7c000000

def z908 : W := mkw 0x8c050a2800154148 0x046028514000aa0a 0xde078f3c003fe3fb 0xa6f03c79e001ff1f

def z909 : W := mkw 0xa6480fc06255f958 0x0d32407e0312afca 0x80000fc0603ffff0 0x5400007e0301ffff

def z910 : W := mkw 0x136805c06b40b800 0x009b402e035a05c0 0xfff80fc07fc1fc17 0xdfffc07e03fe0fe0

def z911 : W := mkw 0x1b25000069140000 0x00d928000348a000 0x7ffe00007fd80007 0xdbfff00003fec000

def z912 : W := mkw 0x82001000f43d47ce 0x0410008007a1ea3e 0x80000000603fe3e0 0x540000000301ff1f

def z913 : W := mkw 0x8e050a2869154148 0x047028514348aa0a 0xde078f3c7fffe3fb 0xfef03c79e3ffff1f

def z914 : W := mkw 0xff3dab6d69556958 0x2ff9ed5b6b4aab4a 0x5e39830c21c66062 0x02f1cc18610e3303

def z915 : W := mkw 0x82001000fbf7ff7d 0x0c10008007dfbffb 0x800000007fffffe0 0x5c00000003ffffff

def z916 : W := mkw 0x37680fd26b41f892 0x09bb407e935a0fc4 0xfff80ff07fc1fd97 0xdfffc07f83fe0fec

def z917 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67ff3fe39ff9f 0xfd0e33ff9ff1cffc

def z918 : W := mkw 0x7d3dab6d00000000 0x23e9ed5b68000000 0x5e39f3cf80000006 0x02f1cf9e7c000000

def z919 : W := mkw 0x24480fc00240b810 0x0922407e001205c0 0x00000fc000001c10 0x0000007e000000e0

def z920 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffffcff8000000d 0x23ffffe7fc000000

def z921 : W := mkw 0x02001000f9e36e35 0x0810008007cf1b71 0x8000000031e67e60 0x4c000000018f33f3

def z922 : W := mkw 0x79ffe5d700000000 0x23cfff2eb8000000 0x7ff9f0c380000006 0x03ffcf861c000000

def z923 : W := mkw 0x24480fe80241f810 0x0922407f40120fc0 0x80000ffc0001fc10 0x2400007fe0000fe0

def z924 : W := mkw 0x5bb7e0006d9e0000 0x12ddbf00036cf000 0x7fff80006ffe000b 0xd3fffc00037ff000

def z925 : W := mkw 0x0cdfefff00000000 0x0066ff7ff8000000 0x7fffffff8000001f 0xa3fffffffc000000

def z926 : W := mkw 0x73fae5d76b41f810 0x2b9fd72ebb5a0fc0 0xa1f870c3ffc1fc04 0x5d0fc3861ffe0fe0

def z927 : W := mkw 0x3578afff00000000 0x21abc57ff8000000 0x7ff9ffff8000001f 0xa3ffcffffc000000

def z928 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff98fcc7fc1fc1f 0xffffcc7e63fe0fe0

def z929 : W := mkw 0xa4480ffa8241ffde 0x0d22407fd4120ffe 0x80000fff8001fff0 0x2400007ffc000fff

def z930 : W := mkw 0x5bb7f0127dbe0000 0x12ddbf8093edf000 0x7ffff033fffe000f 0xfbffff819ffff000

def z931 : W := mkw 0x5bb7f005fdbe0625 0x12ddbf802fedf031 0xfffff0cffffe1e7f 0xffffff867ffff0f3

def z932 : W := mkw 0xb7680fc06b55f958 0x0dbb407e035aafca 0xfffe0ff07fffffff 0xfffff07f83ffffff

def z933 : W := mkw 0x82001000f0f76f6d 0x041000800787bb7b 0x8000000031e67e60 0x4c000000018f33f3

def z934 : W := mkw 0x7dffefff02009000 0x23efff7ff8100480 0x7fffffffce01801f 0xb3fffffffe700c00

def z935 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde07ffffe03fe3ff 0xf6f03fffff01ff1f

def z936 : W := mkw 0x13a240006d080000 0x009d120003684000 0x7ffe00007fd80007 0xdbfff00003fec000

def z937 : W := mkw 0x35e24e9200000000 0x01af127490000000 0x7fc67cf38000001d 0xa3fe33e79c000000

def z938 : W := mkw 0x4cd7eebf00000000 0x2266bf75f8000000 0x7fc7ffff8000001f 0xa3fe3ffffc000000

def z939 : W := mkw 0x26481fff7dbe0000 0x313240fffbedf000 0x00000ffffffe0010 0x7800007ffffff000

def z940 : W := mkw 0x02001000fb61fe14 0x0810008007db0ff0 0x800000007fe1fe00 0x5c00000003ff0ff0

def z941 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ff9f0003fe6000e 0xcbffcf8001ff3000

def z942 : W := mkw 0x5bb7f03a7dbe0000 0x32ddbf81d3edf000 0x7ffff0307ffe000f 0xdbffff8183fff000

def z943 : W := mkw 0x02001000fdbe0686 0x1010008007edf034 0x000000007ffe0380 0x5800000003fff01c

def z944 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff803c07fc07c07 0xdbffc01e03fe03e0

def z945 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80ff07fc1ff97 0xffffc07f83fe0ffc

def z946 : W := mkw 0x7dffefff09000000 0x23efff7ff8480000 0x7fffffff9fc0001f 0xabfffffffcfe0000

def z947 : W := mkw 0x7dffefff02009082 0x23efff7ff8100484 0x7fffffff8001819f 0xa3fffffffc000c0c

def z948 : W := mkw 0x1330b0007dbe0000 0x1099858003edf000 0x7ff9f0007ffe000f 0xdbffcf8003fff000

def z949 : W := mkw 0xfdffefff00140148 0x27efff7ff800a00a 0x7fffffff8018019f 0xa3fffffffc00c00c

def z950 : W := mkw 0x59bfe14500000000 0x02cdff0a28000000 0x7ffff0c38000000f 0x83ffff861c000000

def z951 : W := mkw 0xa4480fff0241f958 0x2d22407ff8120fca 0x80000fff8001fff0 0x2400007ffc000fff

def z952 : W := mkw 0x5b35a00069960000 0x12d9ad00034cb000 0x7ff980003fc60006 0x0bffcc0001fe3000

def z953 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff87fc3ffc1fc1f 0xffffc3fe1ffe0fe0

def z954 : W := mkw 0x5b35b00079b60000 0x12d9ad8003cdb000 0x7ff9f0007fe6000f 0xdbffcf8003ff3000

def z955 : W := mkw 0x0c874a3a00000000 0x00643a51d0000000 0x5e07ff3f8000001b 0xa2f03ff9fc000000

def z956 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffffc019819f 0xb3fffffffe00cc0c

def z957 : W := mkw 0x5bb7f005fdbe0625 0x12ddbf802fedf031 0x7ffff003fffe000f 0xdbffff801ffff000

def z958 : W := mkw 0xdfe74eba6f1dd1ca 0x16ff3a75d378ee8e 0x7fc60c304e198181 0x13fe30618270cc0c

def z959 : W := mkw 0x4897f01294be0686 0x1244bf8094a5f034 0x0007f003803e0008 0x00003f801c01f000

def z960 : W := mkw 0x0a05000060140000 0x005028000300a000 0xde078f3c603fe3fb 0xf6f03c79e301ff1f

def z961 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ff870c380000004 0x03ffc3861c000000

def z962 : W := mkw 0x8897f03f94be07ef 0x0444bf81fca5f03f 0x0007f03f803e03e8 0x20003f81fc01f01f

def z963 : W := mkw 0x5bb7f0057dbe0021 0x12ddbf802bedf001 0x7ffff00c7ffe006f 0xdbffff8063fff003

def z964 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff803c03fc07c16 0xcfffc01e01fe03e0

def z965 : W := mkw 0x4897f03f94be0625 0x3244bf81fca5f031 0x0007f03f803e0268 0x20003f81fc01f013

def z966 : W := mkw 0x35680fc00b40b810 0x09ab407e005a05c0 0xfff80fc03fc07c17 0xcfffc07e01fe03e0

def z967 : W := mkw 0xc897f03a94be07ce 0x1644bf81d4a5f03e 0x0007f03f803e03e8 0x20003f81fc01f01f

def z968 : W := mkw 0x132000006b009000 0x0099000003580480 0xfff800007fc19c07 0xdfffc00003fe0ce0

def z969 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67cf3ce399f99 0x350e33e79e71ccfc

def z970 : W := mkw 0x7dffefff06089082 0x23efff7ff8304484 0xffffffffde199d9f 0xfffffffffef0ccec

def z971 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80fc07fe7fe77 0xdfffc07e03ff3ff3

def z972 : W := mkw 0x13a250007d280000 0x009d128003e94000 0x7ff870007fc00007 0xdbffc38003fe0000

def z973 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67cf3fe3ffffd 0xfd0e33e79ff1ffff

def z974 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffff3ff8000000e 0x23ffff9ffc000000

def z975 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67cf3de399f85 0x5d0e33e79ef1ccfc

def z976 : W := mkw 0x02001000ff289686 0x0010008007f944b4 0x800000007ff99f80 0x5c00000003ffccfc

def z977 : W := mkw 0x0018b14594ea2ea7 0x0000c58a2ca75175 0x8039f3cfb1fe7ffe 0xec01cf9e7d8ff3ff

def z978 : W := mkw 0x53b2f0007daa0000 0x129d978003ed5000 0x7ff870003fc00006 0x0bffc38001fe0000

def z979 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff80fc05fc19c17 0x9bffc07e02fe0ce0

def z980 : W := mkw 0x7dbfeb7f00000000 0x23edff5bf8000000 0x7ffff33f8000000f 0xa3ffff99fc000000

def z981 : W := mkw 0x24480fed0241f810 0x2922407f68120fc0 0x80000fcc0001fc10 0x0400007e60000fe0

def z982 : W := mkw 0x5bb7f0007d280000 0x02ddbf8003e94000 0x7ffff0007ff8000f 0xdbffff8003ffc000

def z983 : W := mkw 0x0c050a2800000000 0x0060285140000000 0x5e07ffff8000001f 0xa2f03ffffc000000

def z984 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff30c7ffe606f 0xdbffff9863fff303

def z985 : W := mkw 0xb7680fc06b55f958 0x0dbb407e035aafca 0xfff80fc07fc7fc77 0xdfffc07e03fe3fe3

def z986 : W := mkw 0x0018a14500402800 0x0000c50a28020140 0x8039f3cfb1e67e7e 0xec01cf9e7d8f33f3

def z987 : W := mkw 0x5bb7f000fdbe0686 0x12ddbf8007edf034 0x7ffff0007ffe038f 0xdbffff8003fff01c

def z988 : W := mkw 0x7df7eebf00000000 0x23efbf75f8000000 0x7fc67c3380000001 0x03fe33e19c000000

def z989 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80fc07fe1fe1f 0xffffc07e03ff0ff0

def z990 : W := mkw 0x59b7e03f00000000 0x22cdbf01f8000000 0x5e3ff03f8000000a 0x22f1ff81fc000000

def z991 : W := mkw 0xd5b2fa281dab4148 0x16ad97d140ed5a0a 0xa1f87f3c1fc1e3f4 0x2d0fc3f9e0fe0f1f

def z992 : W := mkw 0x7def4fff00000000 0x23ef7a7ff8000000 0x7fc67fff8000001d 0xa3fe33fffc000000

def z993 : W := mkw 0x5bb7f03ffdbe0686 0x32ddbf81ffedf034 0x7ffff03ffffe038f 0xfbffff81fffff01c

def z994 : W := mkw 0x5bb7f005fdbe0625 0x12ddbf802fedf031 0xfffff30ffffe627f 0xffffff987ffff313

def z995 : W := mkw 0x4897f00094be0625 0x1244bf8004a5f031 0x0007f000003e0268 0x00003f800001f013

def z996 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x000003c000007c00 0x0000001e000003e0

def z997 : W := mkw 0x11e2449200000000 0x008f122490000000 0x7ffe7cf38000001f 0xa3fff3e79c000000

def z998 : W := mkw 0x4897e03f00000000 0x2244bf01f8000000 0x5e07f03f8000000b 0xa2f03f81fc000000

def z999 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1fe7cf3fff99f9f 0xfd0ff3e79fffccfc

def z1000 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff30c7ffe001f 0xfbffff9863fff000

def z1001 : W := mkw 0x82001000f035474c 0x041000800781aa3a 0x80000000703fffe0 0x5c0000000381ffff

def z1002 : W := mkw 0x0018a14500c22821 0x0000c50a28061141 0x8039f3cfb1c67c7e 0xec01cf9e7d8e33e3

def z1003 : W := mkw 0x59f7e49200000000 0x02cfbf2490000000 0x7ffff0c38000000f 0x83ffff861c000000

def z1004 : W := mkw 0x7dbfeb6d00000000 0x23edff5b68000000 0x7ffff3cf8000001f 0xa3ffff9e7c000000

def z1005 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80000fc04001fc11 0xd400007e02000fe0

def z1006 : W := mkw 0xdbb7f0287dbe0148 0x16ddbf8143edf00a 0x7ffff00c7ffe006f 0xdbffff8063fff003

def z1007 : W := mkw 0x7dffefff00416810 0x2befff7ff8020b40 0x7fffffff8000601f 0xa3fffffffc000300

def z1008 : W := mkw 0xac4d0fe80255f958 0x0d62687f4012afca 0x80078ffc003ffff8 0x24003c7fe001ffff

def z1009 : W := mkw 0x4897f03f94aa06a7 0x2244bf81fca55035 0x0007f03f803e03e8 0x20003f81fc01f01f

def z1010 : W := mkw 0x0cc74eba00000000 0x00663a75d0000000 0x7fc67cf38000001d 0xa3fe33e79c000000

def z1011 : W := mkw 0x3538ab4500000000 0x01a9c55a28000000 0x5e39f3cf8000001e 0xa2f1cf9e7c000000

def z1012 : W := mkw 0xdbb7f0287dbe0148 0x16ddbf8143edf00a 0x7ffff0307ffe018f 0xdbffff8183fff00c

def z1013 : W := mkw 0x53b2f0007daa0000 0x129d978003ed5000 0x7ff9f0007fe6000f 0xdbffcf8003ff3000

def z1014 : W := mkw 0x24480fc08241fe35 0x0922407e04120ff1 0x80000fc00001fe70 0x0400007e00000ff3

def z1015 : W := mkw 0x7dffefff09402810 0x2befff7ff84a0140 0x7fffffff81c0001f 0xa3fffffffc0e0000

def z1016 : W := mkw 0x4897f03f94be0686 0x3244bf81fca5f034 0x0007f03f803e0388 0x20003f81fc01f01c

def z1017 : W := mkw 0x5bb7f000fdbe0604 0x12ddbf8007edf030 0x7ffff003fffe020f 0xfbffff801ffff010

def z1018 : W := mkw 0x37600e806b01d010 0x09bb007403580e80 0xfff80cc07fc19c17 0xdfffc06603fe0ce0

def z1019 : W := mkw 0xbf3dab6d69d76979 0x0df9ed5b6b4ebb4b 0x5e39830c21c66062 0x02f1cc18610e3303

def z1020 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfffe0fc07ff9fc1f 0xdffff07e03ffcfe0

def z1021 : W := mkw 0x13a2400069000000 0x009d120003480000 0x7ffe70007fc0000f 0xdbfff38003fe0000

def z1022 : W := mkw 0x7dffefff0201d010 0x2befff7ff8100e80 0x7fffffff8001801f 0xa3fffffffc000c00

def z1023 : W := mkw 0x0082500094280604 0x0004128004a14030 0xa1c67cf3de399f9d 0xfd0e33e79ef1ccfc

def z1024 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff00c7ffe026f 0xfbffff8063fff013

def z1025 : W := mkw 0x59b7e01200000000 0x02cdbf0090000000 0x7ffff0338000000f 0xa3ffff819c000000

def z1026 : W := mkw 0x17600e806b01d000 0x00bb007403580e80 0xfff80fc07fc1fc17 0xdfffc07e03fe0fe0

def z1027 : W := mkw 0x1b25000069000000 0x00d9280003480000 0x7fff80007fc0000f 0xdbfffc0003fe0000

def z1028 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde078f3c603fe3e3 0x56f03c79e301ff1f

def z1029 : W := mkw 0x51faf5d79feabea7 0x128fd7aebcff55f5 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z1030 : W := mkw 0x7dffefff06089082 0x23efff7ff8304484 0xffffffffce39839f 0xf7fffffffe71cc1c

def z1031 : W := mkw 0x24480fff8241fe96 0x2922407ffc120ff4 0x80000fff8001ff90 0x2400007ffc000ffc

def z1032 : W := mkw 0xb7680fff6b41f958 0x2dbb407ffb5a0fca 0xfff80fffffc1fff7 0xffffc07ffffe0fff

def z1033 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67cf3de199f95 0x3d0e33e79ef0ccfc

def z1034 : W := mkw 0x02001000fdbe0604 0x1010008007edf030 0x800000007ffe1e00 0x5c00000003fff0f0

def z1035 : W := mkw 0x59b7f0001daa0000 0x12cdbf8000ed5000 0x7ffff0003fe6000f 0xcbffff8001ff3000

def z1036 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffff0007fff838f 0xdfffff8003fffc1c

def z1037 : W := mkw 0x59b7f0001daa0000 0x12cdbf8000ed5000 0x7ff9f0001fc00006 0x0bffcf8000fe0000

def z1038 : W := mkw 0x1320000069000000 0x0099000003480000 0xfffe0c307ff9839f 0xfffff06183ffcc1c

def z1039 : W := mkw 0x5bb7e03f69000000 0x22ddbf01fb480000 0x7ffff03fffc0000f 0xfbffff81fffe0000

def z1040 : W := mkw 0x4897f00094be0686 0x1244bf8004a5f034 0x0007f000003e0388 0x00003f800001f01c

def z1041 : W := mkw 0x51b2f0001daa0000 0x128d978000ed5000 0x7ff870001fc00007 0x8bffc38000fe0000

def z1042 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xffff8ffc7fffffff 0xfffffc7fe3ffffff

def z1043 : W := mkw 0x0040148092209604 0x000200a4049104b0 0xa1c67cf3de399f9d 0xfd0e33e79ef1ccfc

def z1044 : W := mkw 0xb7680fe86b41f958 0x0dbb407f435a0fca 0xfff98ffc7fe7ffff 0xffffcc7fe3ff3fff

def z1045 : W := mkw 0x5b35a00069960000 0x12d9ad00034cb000 0x7fff80007ffe000f 0xdbfffc0003fff000

def z1046 : W := mkw 0x82c2449260154148 0x041612249300aa0a 0xa1c67cf3e03fe3fd 0xf50e33e79f01ff1f

def z1047 : W := mkw 0xdbb7f0007dbf4148 0x16ddbf8003edfa0a 0x7ffff0007ffe606f 0xdbffff8003fff303

def z1048 : W := mkw 0xb7680fc06b55f958 0x0dbb407e035aafca 0xfff80fc07fd9fd97 0xdfffc07e03fecfec

def z1049 : W := mkw 0x4c97ea3f00000000 0x2264bf51f8000000 0x5e07fc3f80000009 0x22f03fe1fc000000

def z1050 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x5e3fffff8000001a 0x22f1fffffc000000

def z1051 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039f3cff1fffffe 0xfc01cf9e7f8fffff

def z1052 : W := mkw 0x5bb7f012fdbe0686 0x12ddbf8097edf034 0xfffffc33ffff839f 0xffffffe19ffffc1c

def z1053 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde3f8f3c71ffe3ff 0xfef1fc79e38fff1f

def z1054 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f3cfb1e67c6e 0xc801cf9e7d8f33e3

def z1055 : W := mkw 0x24480fc08241fe96 0x0922407e04120ff4 0x80000fc00001ff90 0x0400007e00000ffc

def z1056 : W := mkw 0x7dffefff04080000 0x23efff7ff8204000 0x7fffffffce18001f 0xb3fffffffe70c000

def z1057 : W := mkw 0x7d7dafff00000000 0x23ebed7ff8000000 0x5e39ffff8000001e 0xa2f1cffffc000000

def z1058 : W := mkw 0x24ca5fd29669fe96 0x092652fe94b34ff4 0x80067ff38039ff98 0x240033ff9c01cffc

def z1059 : W := mkw 0x75faefd700000000 0x23afd77eb8000000 0x7ffe7ff38000001f 0xa3fff3ff9c000000

def z1060 : W := mkw 0x35ea4fd200000000 0x01af527e90000000 0x7ff87fc380000017 0x83ffc3fe1c000000

def z1061 : W := mkw 0x6cdfefff00000000 0x2366ff7ff8000000 0x5e07ffff8000001b 0xa2f03ffffc000000

def z1062 : W := mkw 0x1320100079200000 0x0099008003c90000 0x7ff870007fe0000f 0xdbffc38003ff0000

def z1063 : W := mkw 0x82001000f0b7476d 0x041000800785ba3b 0x80000000603fe3e0 0x540000000301ff1f

def z1064 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0003fc6000f 0x8bffff8001fe3000

def z1065 : W := mkw 0x7dffefff0b41f810 0x2befff7ff85a0fc0 0xffffffff9fc1fc1f 0xaffffffffcfe0fe0

def z1066 : W := mkw 0x37280b4069416810 0x09b9405a034a0b40 0xfff803c07fc07c17 0xdfffc01e03fe03e0

def z1067 : W := mkw 0x53b2f0007daa0000 0x129d978003ed5000 0x7ffe70007ff8000f 0xdbfff38003ffc000

def z1068 : W := mkw 0x4897f01794be06a7 0x1244bf80bca5f035 0x0007f03f803e03e8 0x20003f81fc01f01f

def z1069 : W := mkw 0x7dffefff04080082 0x23efff7ff8204004 0x7fffffff8018019f 0xa3fffffffc00c00c

def z1070 : W := mkw 0x06480fc06241f800 0x0032407e03120fc0 0xfff80fc07fc1fc17 0xdfffc07e03fe0fe0

def z1071 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffffa026001f 0xe3fffffffd013000

def z1072 : W := mkw 0x132000006d1c0000 0x109900000368e000 0x7ff800007fd80007 0xdbffc00003fec000

def z1073 : W := mkw 0x08c7449200000000 0x00463a2490000000 0x7fc7fcf38000001f 0xa3fe3fe79c000000

def z1074 : W := mkw 0x02001000fbe3fe35 0x0810008007df1ff1 0x800000007fc1fc00 0x5c00000003fe0fe0

def z1075 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfffe0ff07fc1fc1f 0xfffff07f83fe0fe0

def z1076 : W := mkw 0x02001000ffbe9686 0x1010008007fdf4b4 0x000000007ffe1c00 0x5800000003fff0e0

def z1077 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c67cf3de399f8d 0x390e33e79ef1ccfc

def z1078 : W := mkw 0x1320000069402800 0x00990000034a0140 0xfff800007fc07c07 0xdfffc00003fe03e0

def z1079 : W := mkw 0xdbb7f0007dbf4148 0x16ddbf8003edfa0a 0xfffffc307fffe3ff 0xffffffe183ffff1f

def z1080 : W := mkw 0x59b7f00014aa0000 0x02cdbf8000a55000 0x7ffff0007ffe000f 0xdbffff8003fff000

def z1081 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80fcc7fc1fe77 0xffffc07e63fe0ff3

def z1082 : W := mkw 0x35680fc00b40b810 0x09ab407e005a05c0 0x7ff803c01fc01c06 0x0bffc01e00fe00e0

def z1083 : W := mkw 0x24480fd78241feb7 0x0922407ebc120ff5 0x80000fff8001fff0 0x2400007ffc000fff

def z1084 : W := mkw 0x7df7eebf00000000 0x23efbf75f8000000 0x7ffffc3f8000000f 0xa3ffffe1fc000000

def z1085 : W := mkw 0x1320000069000000 0x0099000003480000 0xfff9830c7fe6627f 0xffffcc1863ff3313

def z1086 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039f3cfb1c67e76 0x2c01cf9e7d8e33f3

def z1087 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c67cf3de399d8d 0xd90e33e79ef1ccec

def z1088 : W := mkw 0x7dffefff0d080000 0x33efff7ff8684000 0x7fffffff8e00001f 0xa3fffffffc700000

def z1089 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffff0c07ffe1c1f 0xdfffff8603fff0e0

def z1090 : W := mkw 0x7dffefff00c22821 0x23efff7ff8061141 0xffffffffb1c67c7f 0xeffffffffd8e33e3

def z1091 : W := mkw 0x35680fc00b40b810 0x09ab407e005a05c0 0xfff80fc05fc19c17 0xdfffc07e02fe0ce0

def z1092 : W := mkw 0x02001000f9e22e25 0x0010008007cf1171 0x800000007fe67e60 0x5c00000003ff33f3

def z1093 : W := mkw 0x00c2449202009000 0x0006122490100480 0xa1c67cf3de399f9d 0xfd0e33e79ef1ccfc

def z1094 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffff90001c1f 0xeffffffffc8000e0

def z1095 : W := mkw 0x59b7e03f00000000 0x22cdbf01f8000000 0x7fc7f03f80000009 0x23fe3f81fc000000

def z1096 : W := mkw 0x5bb7f0177dbe0000 0x32ddbf80bbedf000 0x7ffff003fffe000f 0xdbffff801ffff000

def z1097 : W := mkw 0x5b25000069140000 0x12d928000348a000 0x7ff800007fc00007 0xdbffc00003fe0000

def z1098 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0007fde0007 0x1bffff8003fef000

def z1099 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80018fcc2027fe7a 0xe4000c7e61013ff3

def z1100 : W := mkw 0x5b35b0007dbe0000 0x12d9ad8003edf000 0x7ff980007ffe0007 0xdbffcc0003fff000

def z1101 : W := mkw 0x5ba740006d1c0000 0x12dd3a000368e000 0x7ffe00005fd80005 0x1bfff00002fec000

def z1102 : W := mkw 0x26480fc06241f810 0x0932407e03120fc0 0x80000fc06001fc10 0x5400007e03000fe0

def z1103 : W := mkw 0x0010b00090a20604 0x0000858004851030 0x8039f3cfb1e67e7e 0xec01cf9e7d8f33f3

def z1104 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffffa000601f 0xe7fffffffd000300

def z1105 : W := mkw 0xfdffefff00154148 0x27efff7ff800aa0a 0xffffffff803fe3ff 0xa7fffffffc01ff1f

def z1106 : W := mkw 0x7dffefff00820000 0x23efff7ff8041000 0x7fffffffa1c6001f 0xa3fffffffd0e3000

def z1107 : W := mkw 0x7dffefff02009000 0x23efff7ff8100480 0xffffffffde399f9f 0xfffffffffef1ccfc

def z1108 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffffc307ffe001f 0xfbffffe183fff000

def z1109 : W := mkw 0x1320000069960000 0x10990000034cb000 0x7ff800007fc60007 0xdbffc00003fe3000

def z1110 : W := mkw 0x081da14500000000 0x0040ed0a28000000 0x5e3ff3cf8000001f 0xa2f1ff9e7c000000

def z1111 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0005ffe000d 0x1bffff8002fff000

def z1112 : W := mkw 0x00c2549296aa96a7 0x000612a494b554b5 0xa1c67cf3de3f9ffd 0xfd0e33e79ef1fcff

def z1113 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde078f3c403fe3f9 0x36f03c79e201ff1f

def z1114 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67fffde39fffd 0xfd0e33fffef1cfff

def z1115 : W := mkw 0x7dffefff0b40b810 0x2befff7ff85a05c0 0xffffffffbfc07c1f 0xeffffffffdfe03e0

def z1116 : W := mkw 0x02001000f63c9686 0x0010008007b1e4b4 0x800000007e3f9f80 0x5c00000003f1fcfc

def z1117 : W := mkw 0x17280b4069416800 0x00b9405a034a0b40 0xfff80fc07fc1fc17 0xdfffc07e03fe0fe0

def z1118 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80000fcc0001fe70 0x2400007e60000ff3

def z1119 : W := mkw 0x59b7f0001daa0000 0x12cdbf8000ed5000 0x7ffff0005ff8000f 0xdbffff8002ffc000

def z1120 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xde078ffc703fffff 0xfef03c7fe381ffff

def z1121 : W := mkw 0x1320000069000000 0x0099000003480000 0xfff800c07fc01c17 0xdfffc00603fe00e0

def z1122 : W := mkw 0x7de74eba00000000 0x23ef3a75d0000000 0x7fc67cf380000005 0x03fe33e79c000000

def z1123 : W := mkw 0x24480fd20241f892 0x0922407e90120fc4 0x80000ff00001fd90 0x0400007f80000fec

def z1124 : W := mkw 0xa4480fed8241ff7d 0x0d22407f6c120ffb 0x80000fff8001fff0 0x2400007ffc000fff

def z1125 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffe7fff80000015 0x23fff3fffc000000

def z1126 : W := mkw 0x5bb7f0007dbf4000 0x12ddbf8003edfa00 0xfffff0007fffe00f 0xdfffff8003ffff00

def z1127 : W := mkw 0x7dffefff02009000 0x23efff7ff8100480 0x7fffffff9e001c1f 0xabfffffffcf000e0

def z1128 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039ffffb1e7fffe 0xec01cffffd8f3fff

def z1129 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0x21c67cf3de199d9d 0xb90e33e79ef0ccec

def z1130 : W := mkw 0x8e050a2860154148 0x047028514300aa0a 0xffc78f3c7e3fe3ff 0xfffe3c79e3f1ff1f

def z1131 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ff9f0007ffe0006 0x5bffcf8003fff000

def z1132 : W := mkw 0x75faefff00000000 0x23afd77ff8000000 0x7ff87fff80000017 0xa3ffc3fffc000000

def z1133 : W := mkw 0x53b2f0007dbe0000 0x129d978003edf000 0x7ff870007ffe0007 0xdbffc38003fff000

def z1134 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffff3007ffe601f 0xdfffff9803fff300

def z1135 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0xffffffff8020021f 0xe7fffffffc010010

def z1136 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c7fcf3fe3f9f9f 0xfd0e3fe79ff1fcfc

def z1137 : W := mkw 0x1328014069402800 0x0099400a034a0140 0x7ff800c07fc01c07 0xdbffc00603fe00e0

def z1138 : W := mkw 0x02001000ff69fe96 0x0810008007fb4ff4 0x800000007fc1fc00 0x5c00000003fe0fe0

def z1139 : W := mkw 0xb7680fc06b41f958 0x0dbb407e035a0fca 0xfff80fc07fc1fff7 0xdfffc07e03fe0fff

def z1140 : W := mkw 0x71faf5d796eabea7 0x238fd7aebcb755f5 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z1141 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff800c01fc01c04 0x0bffc00600fe00e0

def z1142 : W := mkw 0x35680fc00b40b810 0x09ab407e005a05c0 0x7ff80cc01fc01c05 0x0bffc06600fe00e0

def z1143 : W := mkw 0x53a240006d080000 0x129d120003684000 0x7ff800007fc00007 0xdbffc00003fe0000

def z1144 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffff80000007 0x03fffffffc000000

def z1145 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fc7ffff80000019 0x23fe3ffffc000000

def z1146 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0x7ff80fc07fc1fc07 0x1bffc07e03fe0fe0

def z1147 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80cc05fc19c15 0xdfffc06602fe0ce0

def z1148 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0005fd8000f 0x9bffff8002fec000

def z1149 : W := mkw 0x136004806b41f810 0x089b0024035a0fc0 0xfff80cc07fc1fc17 0xdfffc06603fe0fe0

def z1150 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0x7ffff0006ffe000b 0x13ffff80037ff000

def z1151 : W := mkw 0x3def4ffa00000000 0x01ef7a7fd0000000 0x7fffffff8000001f 0xa3fffffffc000000

def z1152 : W := mkw 0x04c24e9200000000 0x0026127490000000 0x7fc67ff38000001f 0xa3fe33ff9c000000

def z1153 : W := mkw 0x7d3dab6d00000000 0x23e9ed5b68000000 0x5e39f30f8000000a 0x22f1cf987c000000

def z1154 : W := mkw 0x75faefd700000000 0x23afd77eb8000000 0x7ff87cc380000005 0x03ffc3e61c000000

def z1155 : W := mkw 0xc897f02d94be076d 0x1644bf816ca5f03b 0x0007f03f803e03e8 0x20003f81fc01f01f

def z1156 : W := mkw 0x0018b14594ea2e25 0x0000c58a2ca75171 0x8039f3cffffe7e7e 0xfc01cf9e7ffff3f3

def z1157 : W := mkw 0x5df7eeba00000000 0x02efbf75d0000000 0x7fffffff8000001f 0xa3fffffffc000000

def z1158 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039f3cfb1c67c76 0xcc01cf9e7d8e33e3

def z1159 : W := mkw 0x37680fc06b55f810 0x09bb407e035aafc0 0xfff80fc07ffffc17 0xdfffc07e03ffffe0

def z1160 : W := mkw 0xdbb7f03f7dbe0148 0x36ddbf81fbedf00a 0x7ffff03ffffe03ef 0xfbffff81fffff01f

def z1161 : W := mkw 0x53b2e00069000000 0x029d970003480000 0x7ff870007fc00007 0xdbffc38003fe0000

def z1162 : W := mkw 0x7dffefff00402821 0x23efff7ff8020141 0x7fffffff8000607f 0xa3fffffffc000303

def z1163 : W := mkw 0x4c9feb7f00000000 0x2264ff5bf8000000 0x5e3fffff8000001f 0xa2f1fffffc000000

def z1164 : W := mkw 0x02001000fffebea7 0x1010008007fff5f5 0x800000007fffffe0 0x5c00000003ffffff

def z1165 : W := mkw 0x5bb7f012fdbe0686 0x12ddbf8097edf034 0x7ffff003fffe000f 0xdbffff801ffff000

def z1166 : W := mkw 0x31faf5d79feabeb7 0x098fd7aebcff55f5 0x21f870c39fc01c04 0x090fc3861cfe00e0

def z1167 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80f007fc1fc03 0x5fffc07803fe0fe0

def z1168 : W := mkw 0x7de75eba96289686 0x23ef3af5d4b144b4 0xffc60c305e399f81 0x5ffe306182f1ccfc

def z1169 : W := mkw 0xffe74eba6b15d158 0x2fff3a75d358ae8a 0x7fc60c304e198181 0x13fe30618270cc0c

def z1170 : W := mkw 0x7db7ea3f00000000 0x23edbf51f8000000 0x5e07f03f80000008 0x22f03f81fc000000

def z1171 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x803ff3ffb1fe7ffe 0xec01ff9ffd8ff3ff

def z1172 : W := mkw 0x5bb7f000fdbe0604 0x12ddbf8007edf030 0xfffff0007ffe1e0f 0xdfffff8003fff0f0

def z1173 : W := mkw 0x13201000f9200604 0x0099008007c90030 0xfff870c3ffe01e1f 0xffffc3861fff00f0

def z1174 : W := mkw 0x7dffefff0240b810 0x2befff7ff81205c0 0x7fffffff80001c1f 0xa3fffffffc0000e0

def z1175 : W := mkw 0x00c2549296289686 0x000612a494b144b4 0xa1c67cf3de199d95 0xdd0e33e79ef0ccec

def z1176 : W := mkw 0x4897f00594be0625 0x1244bf802ca5f031 0x0007f003803e0008 0x00003f801c01f000

def z1177 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x8039f3cfa1e67e7a 0x2401cf9e7d0f33f3

def z1178 : W := mkw 0xdbb7f0287dbe0148 0x16ddbf8143edf00a 0xfffffc3c7fff83ff 0xffffffe1e3fffc1f

def z1179 : W := mkw 0x136004806b009000 0x009b002403580480 0x7ff800c07fc01c07 0xdbffc00603fe00e0

def z1180 : W := mkw 0x7dffefff00960000 0x33efff7ff804b000 0x7fffffff8006001f 0xa3fffffffc003000

def z1181 : W := mkw 0x00c2449206089082 0x0006122490304484 0xa1c67cf3de199d9d 0xfd0e33e79ef0ccec

def z1182 : W := mkw 0x7dbfeb7f00000000 0x23edff5bf8000000 0x5e39f30f80000002 0x02f1cf987c000000

def z1183 : W := mkw 0x7dffefff00014000 0x23efff7ff8000a00 0xffffffff8001e01f 0xa7fffffffc000f00

def z1184 : W := mkw 0x132010007daa0000 0x1099008003ed5000 0x7ff800007fc00007 0xdbffc00003fe0000

def z1185 : W := mkw 0x7dffefff06089082 0x23efff7ff8304484 0x7fffffff8e00001f 0xa3fffffffc700000

def z1186 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7fffffff8038039f 0xa3fffffffc01c01c

def z1187 : W := mkw 0x75faefd700000000 0x23afd77eb8000000 0x7ff873c380000006 0x03ffc39e1c000000

def z1188 : W := mkw 0x17200a006b41f810 0x08b90050035a0fc0 0xfff80f007fc1fc17 0xdfffc07803fe0fe0

def z1189 : W := mkw 0x24480fc58241fe35 0x0922407e2c120ff1 0x80000fc38001fc10 0x0400007e1c000fe0

def z1190 : W := mkw 0x7dffefd200000000 0x03efff7e90000000 0x7ffffff38000001f 0xa3ffffff9c000000

def z1191 : W := mkw 0x5bb7e0006d9e0000 0x12ddbf00036cf000 0x7ffe00004fd80001 0x13fff000027ec000

def z1192 : W := mkw 0xfdffefff00000148 0x27efff7ff800000a 0x7fffffff800003ff 0xa3fffffffc00001f

def z1193 : W := mkw 0x5bb7f017fdbe06a7 0x12ddbf80bfedf035 0x7ffff03ffffe03ef 0xfbffff81fffff01f

def z1194 : W := mkw 0x79ffe5d700000000 0x23cfff2eb8000000 0x7ffff3cf8000001f 0xa3ffff9e7c000000

def z1195 : W := mkw 0xdbb7f0287dbf4148 0x16ddbf8143edfa0a 0xfffff03c7fffe3ef 0xffffff81e3ffff1f

def z1196 : W := mkw 0x59bfe17f00000000 0x22cdff0bf8000000 0x7ffff3ff8000001f 0xa3ffff9ffc000000

def z1197 : W := mkw 0x7d3dab6d00000000 0x23e9ed5b68000000 0x5e3fffff8000001f 0xa2f1fffffc000000

def z1198 : W := mkw 0x5bb7e0006d9e0000 0x12ddbf00036cf000 0x7ffff0006fde000f 0x93ffff80037ef000

def z1199 : W := mkw 0x37680fc06b009000 0x01bb407e03580480 0xfff80fc07fc19c17 0xdfffc07e03fe0ce0

def z1200 : W := mkw 0x35ea4fff00000000 0x21af527ff8000000 0x7ffe7fff8000001f 0xa3fff3fffc000000

def z1201 : W := mkw 0x7dffefd700000000 0x23efff7eb8000000 0x7fffffc38000001f 0x83fffffe1c000000

def z1202 : W := mkw 0x132000006b40b810 0x08990000035a05c0 0x7ff800007fc01c07 0xdbffc00003fe00e0

def z1203 : W := mkw 0x7dffefff041c0000 0x33efff7ff820e000 0x7fffffff8018001f 0xa3fffffffc00c000

def z1204 : W := mkw 0x35680fc00b41f810 0x09ab407e005a0fc0 0xfff80fc01fc1fc17 0x8fffc07e00fe0fe0

def z1205 : W := mkw 0x0018a14580c22e25 0x0000c50a2c061171 0x8039f3cfa1c67e7e 0xa401cf9e7d0e33f3

def z1206 : W := mkw 0x7dffefff00402800 0x23efff7ff8020140 0xffffffffb1e67e7f 0xeffffffffd8f33f3

def z1207 : W := mkw 0x1320000069000000 0x0099000003480000 0x7ff800006fc00003 0x13ffc000037e0000

def z1208 : W := mkw 0x06000a0060014000 0x0030005003000a00 0xde078f3c603fe3fb 0xf6f03c79e301ff1f

def z1209 : W := mkw 0x84480fff8241ffef 0x0422407ffc120fff 0x80000fff8001fff0 0x2400007ffc000fff

def z1210 : W := mkw 0x5bb7f000fdbe0604 0x12ddbf8007edf030 0xfffffcf3ffff9f9f 0xffffffe79ffffcfc

def z1211 : W := mkw 0xa4480fe80241f958 0x0d22407f40120fca 0x80000ff00001fd90 0x0400007f80000fec

def z1212 : W := mkw 0x5bb7f000fdbe0625 0x12ddbf8007edf031 0x7ffff0007ffe026f 0xdbffff8003fff013

def z1213 : W := mkw 0x7dbfeb7f00000000 0x23edff5bf8000000 0x5e3ff3ff8000001e 0xa2f1ff9ffc000000

def z1214 : W := mkw 0x13a250007dbe0000 0x109d128003edf000 0x7ffe70007ffe000f 0xdbfff38003fff000

def z1215 : W := mkw 0xfdffefff00140148 0x27efff7ff800a00a 0xffffffffa03e63ff 0xe7fffffffd01f31f

def z1216 : W := mkw 0x1b2510007dbe0000 0x10d9288003edf000 0x7fff80007ffe000f 0xdbfffc0003fff000

def z1217 : W := mkw 0xfdffefff00014148 0x27efff7ff8000a0a 0x7fffffff8001819f 0xa3fffffffc000c0c

def z1218 : W := mkw 0x316805c00b40b810 0x098b402e005a05c0 0x7ff800c01fc01c07 0x8bffc00600fe00e0

def z1219 : W := mkw 0x02001000fffffe35 0x1810008007fffff1 0x800000007ffffe60 0x5c00000003fffff3

def z1220 : W := mkw 0x02001000f629d686 0x0010008007b14eb4 0x800000007e39ff80 0x5c00000003f1cffc

def z1221 : W := mkw 0x132801406b41f810 0x0899400a035a0fc0 0xfff803c07fc1fc17 0xdfffc01e03fe0fe0

def z1222 : W := mkw 0x02001000f9f62e25 0x1010008007cfb171 0x8000000031e67e60 0x4c000000018f33f3

def z1223 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff803c07fc1fc06 0x5fffc01e03fe0fe0

def z1224 : W := mkw 0x7d3dbb6d90e22e25 0x23e9eddb6c871171 0xde39830c31e67e62 0x4ef1cc18618f33f3

def z1225 : W := mkw 0x0c051a2896289686 0x006028d144b144b4 0xde078f3c5e399f9b 0xfef03c79e2f1ccfc

def z1226 : W := mkw 0x7df7eeba00000000 0x23efbf75d0000000 0x7ffffcf38000001f 0xa3ffffe79c000000

def z1227 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80000fc01001fc14 0xcc00007e00800fe0

def z1228 : W := mkw 0x24481fc09261fe14 0x092240fe04930ff0 0x80007fc39021fe1c 0xec0003fe1c810ff0

def z1229 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffff3cf8000000f 0x83ffff9e7c000000

def z1230 : W := mkw 0x37680fc56b41f810 0x09bb407e2b5a0fc0 0xfff80fcfffc1fc17 0xffffc07e7ffe0fe0

def z1231 : W := mkw 0x02001000ff3c9686 0x1010008007f9e4b4 0x800000005e399f80 0x5c00000002f1ccfc

def z1232 : W := mkw 0x79ffe5ff00000000 0x23cfff2ff8000000 0x7ffff0ff8000000f 0xa3ffff87fc000000

def z1233 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ff9f3cf8000001e 0xa3ffcf9e7c000000

def z1234 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ffffcf38000000f 0x83ffffe79c000000

def z1235 : W := mkw 0x7dffefff00140000 0x23efff7ff800a000 0x7fffffff803e001f 0xa3fffffffc01f000

def z1236 : W := mkw 0x5b35a00069000000 0x02d9ad0003480000 0x7ff980007fc00007 0xdbffcc0003fe0000

def z1237 : W := mkw 0x0418ab4500000000 0x0020c55a28000000 0x5e39ffcf8000001f 0xa2f1cffe7c000000

def z1238 : W := mkw 0x2c5dafff00000000 0x2162ed7ff8000000 0x5e3fffff8000001f 0xa2f1fffffc000000

def z1239 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x80060ff04039ff99 0xf400307f8201cffc

def z1240 : W := mkw 0xdbb7f0007dbe0148 0x16ddbf8003edf00a 0x7ffff0007ffe03ef 0xdbffff8003fff01f

def z1241 : W := mkw 0x5ba740006d1c0000 0x12dd3a000368e000 0x7ffe00006fd80003 0x13fff000037ec000

def z1242 : W := mkw 0x00c2449286089686 0x00061224943044b4 0xa1c67cf3ce199f9d 0xb50e33e79e70ccfc

def z1243 : W := mkw 0x2ccf4fff00000000 0x21667a7ff8000000 0x7fc7ffff8000001f 0xa3fe3ffffc000000

def z1244 : W := mkw 0x7dffefff00c22821 0x23efff7ff8061141 0xffffffffa1e6627f 0xe7fffffffd0f3313

def z1245 : W := mkw 0x82001000fdff6f6d 0x1410008007effb7b 0x800000007fffffe0 0x5c00000003ffffff

def z1246 : W := mkw 0x1330a00069820000 0x00998500034c1000 0x7ff980007fc60007 0xdbffcc0003fe3000

def z1247 : W := mkw 0x7df7eebf00000000 0x23efbf75f8000000 0x7fc7ff3f8000001b 0xa3fe3ff9fc000000

def z1248 : W := mkw 0x7dffefff0b009010 0x2befff7ff8580480 0x7fffffff8e00001f 0xa3fffffffc700000

def z1249 : W := mkw 0xb7680fe86b41f958 0x0dbb407f435a0fca 0xfff80ff07fc1fd97 0xdfffc07f83fe0fec

def z1250 : W := mkw 0xfdffefff00014148 0x27efff7ff8000a0a 0xffffffffc039e3ff 0xf7fffffffe01cf1f

def z1251 : W := mkw 0xdbb7f03afdbe07ce 0x16ddbf81d7edf03e 0x7ffff03ffffe03ef 0xfbffff81fffff01f

def z1252 : W := mkw 0x59b7f0001dbe0000 0x12cdbf8000edf000 0x7ffff0001ffe000f 0x8bffff8000fff000

def z1253 : W := mkw 0x24480fc00241f810 0x0922407e00120fc0 0x00000f000001e000 0x0000007800000f00

def z1254 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffff0007ffe626f 0xdfffff8003fff313

def z1255 : W := mkw 0x7dffefff00000000 0x23efff7ff8000000 0x7ff9ffff80000016 0x23ffcffffc000000

def z1256 : W := mkw 0x24480fc50241f810 0x0922407e28120fc0 0x80000fcf8001fc10 0x2400007e7c000fe0

def z1257 : W := mkw 0x37680fd26b41f810 0x09bb407e935a0fc0 0xfff80ff3ffc1fc17 0xffffc07f9ffe0fe0

def z1258 : W := mkw 0x37280b406b41f810 0x09b9405a035a0fc0 0xfff803007fc1fc07 0xdfffc01803fe0fe0

def z1259 : W := mkw 0x0018b14590e22e25 0x0000c58a2c871171 0x0039f3cfb1c67c7e 0xa801cf9e7d8e33e3

def z1260 : W := mkw 0x2458bfc592e3fe35 0x0922c5fe2c971ff1 0x8001ffcf8027fe78 0x24000ffe7c013ff3

def z1261 : W := mkw 0x37680fc069402800 0x01bb407e034a0140 0xfff80fc07fc07c17 0xdfffc07e03fe03e0

def z1262 : W := mkw 0xdbb7f0007dbf4148 0x16ddbf8003edfa0a 0x7ffff0007fff818f 0xdbffff8003fffc0c

def z1263 : W := mkw 0x37680fc06b41f810 0x09bb407e035a0fc0 0xfff80fc03fc1fc16 0x0fffc07e01fe0fe0

def z1264 : W := mkw 0x5bb7f0007dbe0000 0x12ddbf8003edf000 0xfffff0007ffe021f 0xffffff8003fff010

def z1265 : W := mkw 0x5bb7f012fdbe0686 0x12ddbf8097edf034 0xfffff0f3fffe1f9f 0xffffff879ffff0fc

def z1266 : W := mkw 0xbfe74eba6f1dd1da 0x0dff3a75d378ee8e 0x7fc60c304e198181 0x13fe30618270cc0c

def z1267 : W := mkw 0x5bb7e00069960000 0x12ddbf00034cb000 0x7ffff0007fc6000f 0xdbffff8003fe3000

def z1268 : W := mkw 0x1b25000069140000 0x00d928000348a000 0x7ff980007fc60007 0xdbffcc0003fe3000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z7,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z8,z6]),(0,[z0,z1,z3,z9,z4,z5,z6]),(0,[z0,z1,z10,z11,z3,z5,z6]),(0,[z0,z1,z12,z12,z3,z5,z6]),(1,[z0,z1,z3,z5,z6,z13])],[(0,[z14,z0,z1,z12,z3,z5,z6]),(0,[z15,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z16]),(0,[z17,z0,z1,z3,z4,z5,z6])],[(0,[z18,z0,z1,z19,z3,z4,z6]),(0,[z0,z1,z12,z20,z3,z5,z6])],[(0,[z21,z0,z1,z11,z3,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z23,z3,z4,z5,z6]),(0,[z0,z24,z1,z12,z3,z5,z6]),(0,[z0,z1,z3,z25,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z26]),(0,[z27,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z28,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z29,z6])],[(0,[z30,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z31,z4,z5,z6]),(0,[z0,z32,z1,z3,z4,z5,z6]),(0,[z0,z1,z33,z3,z4,z5,z6]),(0,[z0,z1,z34,z3,z4,z35,z6])],[(0,[z0,z1,z36,z11,z3,z5,z6]),(0,[z0,z1,z3,z37,z4,z5,z6]),(0,[z0,z1,z38,z4,z5,z6,z39]),(0,[z0,z1,z3,z4,z5,z40,z6]),(0,[z0,z1,z41,z3,z4,z6,z42]),(0,[z0,z1,z43,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z44,z4,z5,z6]),(0,[z0,z1,z45,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z46,z5,z6]),(0,[z0,z1,z11,z3,z5,z47,z6]),(0,[z0,z1,z34,z3,z4,z5,z48]),(0,[z49,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z48,z6,z13])]],
   [[(0,[z0,z1,z50,z3,z51,z4,z6])],[(0,[z18,z0,z1,z20,z3,z4,z6])],[(0,[z0,z52,z1,z3,z4,z5,z6]),(0,[z0,z1,z53,z3,z4,z5,z6]),(0,[z0,z1,z19,z12,z3,z5,z6]),(0,[z0,z1,z3,z54,z4,z5,z6])],[(0,[z0,z55,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z46,z6]),(0,[z56,z0,z1,z3,z4,z5,z57]),(0,[z0,z1,z3,z4,z5,z6,z58]),(1,[z0,z1,z59,z4,z5,z39])],[(0,[z0,z1,z60,z38,z4,z5,z6]),(0,[z0,z1,z61,z3,z4,z5,z6]),(0,[z14,z0,z1,z3,z4,z62,z6]),(0,[z0,z1,z3,z4,z5,z63,z6])],[(0,[z0,z1,z64,z4,z5,z6,z39]),(0,[z0,z1,z3,z4,z5,z6,z65]),(0,[z15,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z11,z66,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z67,z6]),(0,[z0,z1,z12,z3,z5,z68,z6])],[(0,[z0,z1,z3,z69,z4,z5,z6]),(0,[z0,z1,z70,z3,z38,z5,z6]),(0,[z0,z1,z3,z71,z4,z5,z6]),(0,[z0,z1,z3,z4,z72,z5,z6]),(0,[z0,z1,z73,z3,z4,z5,z6]),(0,[z0,z74,z1,z3,z4,z5,z6]),(0,[z0,z75,z1,z3,z76,z5,z6]),(0,[z0,z1,z3,z77,z78,z5,z6]),(1,[z0,z1,z3,z4,z79,z6])],[(0,[z80,z0,z1,z3,z4,z5,z6]),(0,[z21,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z11,z3,z81,z5,z6]),(0,[z18,z0,z1,z3,z4,z48,z6]),(0,[z0,z1,z3,z4,z5,z82,z6]),(0,[z0,z1,z3,z4,z5,z83,z6]),(0,[z0,z1,z11,z3,z77,z5,z6]),(0,[z0,z1,z3,z4,z5,z84,z6]),(1,[z0,z1,z85,z3,z5,z6]),(1,[z0,z1,z3,z5,z6,z86]),(0,[z0,z1,z3,z4,z5,z68,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z87,z6]),(0,[z18,z0,z1,z3,z4,z88,z6]),(0,[z0,z1,z3,z4,z5,z6,z89])],[(0,[z0,z90,z1,z3,z4,z91,z6]),(0,[z92,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z93,z3,z4,z5,z6]),(0,[z0,z1,z94,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z95,z4,z6]),(0,[z0,z1,z85,z3,z4,z5,z6]),(0,[z96,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z36,z12,z3,z5,z6]),(1,[z0,z1,z20,z4,z97,z6]),(0,[z0,z1,z3,z98,z4,z5,z6]),(0,[z0,z1,z3,z99,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z100])],[(0,[z0,z101,z36,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z102]),(0,[z0,z1,z103,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z104]),(0,[z0,z1,z3,z4,z105,z5,z6])],[(0,[z0,z1,z11,z106,z3,z5,z6]),(0,[z0,z1,z107,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z108,z6]),(0,[z109,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z110,z5,z6]),(0,[z0,z111,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z112,z5,z6]),(0,[z0,z1,z60,z3,z4,z79,z6])],[(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z0,z74,z1,z11,z3,z5,z6]),(0,[z0,z1,z113,z3,z4,z5,z6]),(0,[z0,z75,z1,z11,z3,z5,z6]),(0,[z0,z1,z11,z3,z76,z5,z6])],[(0,[z0,z1,z114,z3,z4,z5,z6]),(0,[z0,z1,z3,z76,z4,z5,z6]),(0,[z115,z0,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z116,z0,z1,z3,z4,z5,z6]),(0,[z0,z117,z1,z3,z4,z5,z6]),(0,[z0,z118,z1,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z120,z4,z6]),(0,[z0,z121,z1,z3,z4,z5,z6]),(0,[z0,z1,z122,z3,z5,z6,z123])],[(0,[z0,z1,z3,z4,z124,z68,z6])],[(0,[z0,z1,z11,z3,z5,z62,z6]),(0,[z0,z1,z41,z3,z4,z35,z6]),(0,[z125,z0,z1,z3,z4,z5,z6])],[(0,[z0,z126,z1,z3,z4,z5,z6]),(0,[z127,z0,z1,z3,z4,z5,z6]),(0,[z128,z0,z1,z129,z4,z5,z6]),(0,[z0,z1,z3,z4,z130,z6,z131]),(0,[z132,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z133,z5,z6]),(1,[z0,z1,z11,z60,z5,z6]),(0,[z0,z1,z11,z12,z4,z5,z6]),(0,[z0,z1,z12,z3,z4,z134,z6]),(0,[z0,z1,z135,z3,z4,z5,z6])],[(0,[z0,z1,z136,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z137,z5,z6]),(0,[z0,z74,z1,z138,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z139,z6])],[(0,[z109,z0,z1,z11,z3,z5,z6]),(0,[z0,z140,z1,z3,z4,z5,z6]),(1,[z15,z0,z3,z4,z5,z141]),(0,[z0,z1,z34,z3,z4,z97,z6])],[(0,[z0,z1,z3,z142,z4,z5,z6]),(0,[z0,z1,z3,z143,z4,z5,z6]),(0,[z0,z1,z106,z4,z5,z6,z39]),(0,[z0,z144,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z145]),(0,[z0,z1,z3,z4,z5,z146,z6]),(0,[z0,z1,z3,z4,z5,z6,z147]),(0,[z0,z1,z3,z148,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z149,z5,z6]),(0,[z0,z1,z3,z4,z5,z150,z6]),(1,[z0,z1,z122,z3,z5,z123]),(0,[z0,z1,z3,z4,z124,z5,z6]),(1,[z0,z1,z3,z151,z5,z6])],[(1,[z0,z1,z70,z3,z5,z6]),(0,[z0,z1,z3,z152,z4,z5,z6]),(0,[z128,z1,z3,z4,z5,z6,z131]),(0,[z0,z153,z1,z106,z4,z5,z6])],[(0,[z0,z1,z3,z154,z4,z5,z6]),(0,[z18,z0,z1,z34,z3,z4,z6]),(0,[z128,z0,z1,z3,z4,z155,z6]),(0,[z0,z1,z3,z4,z5,z156,z6]),(0,[z0,z74,z1,z12,z3,z5,z6]),(0,[z0,z75,z1,z12,z3,z5,z6]),(1,[z0,z1,z157,z3,z5,z6]),(0,[z0,z1,z3,z158,z4,z5,z6])],[(0,[z109,z0,z1,z138,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z159,z6]),(0,[z0,z1,z3,z95,z4,z5,z6]),(0,[z0,z1,z3,z160,z4,z5,z6])],[(0,[z21,z0,z36,z3,z4,z5,z6]),(0,[z0,z36,z3,z4,z5,z6,z141]),(0,[z30,z1,z3,z81,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z161,z6]),(1,[z0,z1,z11,z5,z6,z39])],[(0,[z0,z1,z162,z3,z4,z5,z6]),(0,[z163,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z5,z6,z141])],[(0,[z0,z1,z60,z64,z4,z5,z6]),(0,[z0,z1,z164,z4,z165,z5,z6]),(0,[z0,z144,z1,z11,z3,z5,z6]),(1,[z0,z1,z11,z5,z166,z6]),(0,[z0,z1,z3,z4,z5,z167,z6])],[(0,[z0,z1,z168,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z169]),(0,[z0,z1,z34,z3,z4,z5,z42])]],
   [[(0,[z170,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z171,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z38,z5,z6]),(0,[z0,z1,z12,z3,z81,z5,z6]),(0,[z0,z1,z12,z3,z77,z5,z6]),(0,[z0,z1,z172,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z173,z5,z6]),(0,[z0,z1,z3,z174,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z175])],[(0,[z0,z1,z3,z176,z4,z5,z6]),(0,[z109,z0,z1,z12,z3,z5,z6]),(1,[z0,z1,z12,z3,z95,z6]),(0,[z0,z1,z3,z4,z5,z6,z177])],[(0,[z0,z178,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z179,z5,z6]),(0,[z0,z1,z3,z4,z180,z5,z6]),(0,[z0,z1,z3,z4,z48,z6,z42])],[(0,[z21,z0,z90,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z181]),(1,[z0,z74,z1,z11,z5,z6]),(0,[z0,z1,z59,z3,z4,z5,z6]),(0,[z182,z0,z1,z3,z4,z5,z6]),(0,[z183,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z184,z4,z5,z6]),(0,[z185,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z11,z5,z97,z6]),(0,[z0,z1,z20,z4,z5,z6,z39])],[(0,[z0,z1,z12,z106,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z186,z6]),(0,[z163,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z187,z6]),(0,[z0,z1,z3,z4,z5,z188,z6])],[(0,[z189,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z190,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z191,z6]),(0,[z0,z1,z11,z3,z5,z6,z39]),(0,[z0,z192,z1,z3,z4,z5,z6]),(0,[z193,z0,z1,z3,z4,z5,z6])],[(0,[z194,z0,z1,z38,z4,z5,z6]),(0,[z0,z1,z195,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z196]),(0,[z0,z1,z12,z3,z76,z5,z6]),(0,[z15,z0,z1,z197,z4,z5,z6]),(0,[z0,z1,z198,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z199,z4,z5,z6]),(0,[z0,z1,z200,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z35,z5,z6]),(0,[z0,z1,z201,z3,z4,z5,z6]),(0,[z0,z1,z202,z3,z4,z5,z6]),(0,[z0,z203,z1,z3,z4,z5,z6])],[(0,[z194,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z204]),(0,[z128,z0,z1,z3,z205,z5,z6]),(0,[z0,z24,z3,z76,z4,z5,z6]),(0,[z0,z1,z19,z3,z4,z97,z6]),(0,[z0,z206,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z207,z6]),(0,[z0,z208,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z76,z5,z6]),(0,[z0,z1,z41,z3,z4,z97,z6]),(0,[z0,z209,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z35,z5,z6])],[(1,[z0,z1,z3,z4,z210,z6]),(0,[z0,z1,z3,z4,z5,z6,z211]),(0,[z0,z1,z3,z4,z5,z212,z6]),(0,[z0,z1,z213,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z5,z62,z6]),(0,[z0,z1,z3,z4,z5,z6,z214]),(0,[z0,z1,z11,z3,z5,z215,z6]),(0,[z0,z1,z12,z3,z5,z6,z216]),(0,[z0,z1,z3,z217,z5,z97,z6]),(0,[z0,z1,z3,z120,z4,z218,z6])],[(0,[z0,z1,z3,z4,z5,z219,z6]),(0,[z0,z1,z3,z4,z5,z6,z220]),(0,[z0,z1,z122,z3,z221,z5,z6])],[(0,[z222,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z62,z6]),(0,[z0,z1,z3,z4,z5,z6,z216])],[(0,[z0,z74,z106,z3,z4,z5,z6]),(0,[z0,z1,z3,z223,z4,z5,z6]),(0,[z189,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z11,z3,z5,z97,z6]),(0,[z0,z1,z3,z138,z4,z5,z6]),(1,[z0,z1,z3,z4,z134,z6])],[(0,[z0,z1,z3,z81,z4,z5,z6]),(0,[z224,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z225]),(0,[z0,z1,z11,z4,z5,z6,z39]),(0,[z0,z1,z226,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z227]),(0,[z15,z0,z1,z3,z4,z228,z6]),(0,[z0,z1,z200,z11,z3,z5,z6]),(0,[z0,z1,z229,z3,z4,z5,z6]),(0,[z230,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z231,z3,z4,z5,z6])],[(0,[z0,z1,z232,z3,z4,z5,z6]),(0,[z0,z1,z233,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z234]),(1,[z18,z1,z3,z4,z235,z6]),(0,[z163,z0,z1,z12,z3,z5,z6]),(1,[z0,z1,z41,z11,z5,z6]),(0,[z0,z1,z11,z4,z5,z166,z6]),(0,[z0,z1,z3,z4,z68,z6,z236])],[(0,[z0,z1,z3,z237,z4,z5,z6])],[(0,[z0,z1,z238,z3,z4,z5,z6]),(0,[z0,z1,z239,z3,z4,z5,z6]),(0,[z0,z1,z240,z3,z4,z5,z6]),(0,[z0,z1,z3,z241,z4,z5,z6])],[(0,[z242,z56,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z243,z4,z5,z6]),(0,[z0,z106,z3,z51,z4,z5,z6]),(0,[z0,z1,z3,z77,z4,z48,z6]),(0,[z0,z1,z4,z5,z48,z6,z244])],[(0,[z0,z1,z245,z3,z38,z4,z6]),(0,[z14,z0,z1,z3,z4,z235,z6]),(0,[z0,z1,z3,z77,z4,z88,z6]),(0,[z246,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z247,z4,z5,z6])],[(0,[z0,z1,z3,z4,z248,z5,z6]),(0,[z0,z153,z1,z3,z4,z249,z6])],[(0,[z250,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z251,z6]),(0,[z0,z1,z11,z4,z5,z97,z6])]],
   [[(1,[z0,z1,z3,z252,z5,z6]),(0,[z0,z1,z3,z4,z5,z253,z6]),(0,[z0,z153,z1,z3,z4,z254,z6]),(0,[z0,z119,z1,z11,z3,z5,z6]),(0,[z0,z255,z1,z3,z4,z5,z6])],[(0,[z242,z0,z1,z3,z4,z256,z6]),(0,[z0,z1,z12,z3,z38,z5,z6]),(0,[z257,z0,z1,z3,z4,z5,z6]),(1,[z0,z258,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z165,z5,z6]),(0,[z0,z1,z259,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z86,z39])],[(0,[z0,z1,z260,z3,z4,z5,z6]),(0,[z0,z1,z261,z3,z4,z5,z6]),(0,[z0,z1,z3,z221,z76,z5,z6]),(0,[z189,z0,z1,z12,z3,z5,z6])],[(0,[z0,z90,z1,z3,z4,z5,z6]),(0,[z0,z262,z1,z3,z4,z5,z6]),(0,[z263,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z264,z6]),(0,[z163,z0,z1,z3,z4,z46,z6]),(0,[z0,z1,z12,z3,z5,z134,z6]),(0,[z0,z1,z3,z4,z5,z265,z6])],[(0,[z266,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z154,z4,z5,z6]),(0,[z0,z1,z3,z267,z4,z5,z6]),(0,[z0,z1,z3,z129,z4,z5,z6]),(0,[z0,z1,z3,z268,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z269]),(0,[z163,z0,z1,z3,z4,z62,z6])],[(0,[z0,z1,z3,z4,z5,z134,z6]),(0,[z0,z1,z3,z4,z5,z6,z270]),(0,[z0,z1,z271,z3,z4,z5,z6])],[(0,[z0,z272,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z273,z4,z5,z6]),(0,[z0,z1,z20,z3,z4,z97,z6]),(0,[z0,z1,z3,z4,z5,z6,z274]),(0,[z0,z1,z3,z275,z4,z5,z6]),(0,[z276,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z277,z5,z6])],[(0,[z0,z1,z3,z4,z278,z5,z6]),(0,[z0,z153,z3,z51,z4,z5,z6]),(0,[z0,z1,z279,z3,z4,z5,z6]),(0,[z0,z1,z3,z280,z4,z5,z6]),(0,[z0,z1,z12,z3,z5,z6,z39]),(0,[z0,z1,z77,z4,z5,z6,z39])]],
   [[(0,[z0,z1,z3,z281,z4,z5,z6]),(0,[z163,z0,z1,z3,z120,z4,z6]),(0,[z282,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z19,z3,z4,z6,z42]),(0,[z0,z1,z283,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z108,z6]),(0,[z194,z0,z1,z64,z4,z5,z6]),(0,[z257,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z284,z5,z6]),(0,[z14,z18,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z88,z6,z42]),(0,[z0,z1,z3,z4,z285,z5,z6]),(0,[z0,z286,z1,z3,z4,z5,z6])],[(1,[z0,z1,z287,z3,z5,z6]),(0,[z0,z1,z288,z3,z4,z5,z6]),(0,[z14,z0,z1,z41,z3,z4,z6]),(0,[z0,z74,z1,z11,z4,z5,z6]),(0,[z0,z1,z289,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z290,z6]),(0,[z0,z101,z1,z3,z4,z5,z141])],[(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z0,z90,z1,z11,z3,z5,z6]),(0,[z0,z1,z11,z3,z5,z235,z6]),(0,[z0,z74,z1,z3,z291,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z292]),(0,[z0,z293,z1,z3,z4,z5,z6])],[(0,[z0,z1,z294,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z295,z6]),(0,[z0,z1,z3,z4,z5,z296,z6]),(0,[z0,z119,z1,z12,z3,z5,z6]),(0,[z0,z297,z1,z12,z3,z5,z6]),(1,[z0,z1,z3,z78,z5,z6]),(0,[z0,z1,z298,z3,z4,z5,z6]),(0,[z0,z1,z122,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z299,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z300]),(0,[z0,z1,z301,z3,z4,z5,z6]),(0,[z0,z1,z3,z302,z4,z5,z6]),(0,[z0,z1,z11,z3,z5,z6,z42]),(0,[z0,z1,z3,z4,z5,z303,z6]),(0,[z0,z1,z304,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z215,z6]),(0,[z0,z1,z3,z4,z5,z6,z305])],[(0,[z0,z1,z306,z3,z4,z5,z6]),(0,[z307,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z308,z3,z4,z165,z6]),(0,[z0,z1,z77,z4,z5,z97,z6]),(0,[z0,z1,z309,z3,z4,z5,z6]),(0,[z0,z310,z1,z3,z4,z5,z6])]],
   [[(0,[z30,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z35,z46,z6])],[(0,[z109,z0,z1,z11,z4,z5,z6]),(1,[z257,z1,z3,z311,z5,z6]),(0,[z0,z1,z11,z3,z311,z5,z6]),(0,[z312,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z35,z62,z6]),(0,[z0,z1,z11,z3,z5,z313,z6]),(0,[z0,z1,z11,z3,z5,z314,z6]),(0,[z0,z1,z60,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z315,z314,z6])],[(0,[z109,z194,z1,z3,z4,z5,z6]),(1,[z109,z1,z38,z4,z5,z6]),(0,[z0,z7,z1,z3,z4,z5,z6]),(1,[z0,z1,z162,z4,z5,z6]),(1,[z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z316,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z317]),(1,[z0,z1,z318,z4,z5,z6])],[(0,[z319,z0,z1,z3,z4,z5,z6]),(0,[z14,z0,z1,z19,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z320,z6]),(0,[z0,z24,z75,z3,z4,z5,z6])],[(0,[z0,z1,z321,z3,z38,z4,z6]),(0,[z0,z1,z3,z4,z5,z322,z6]),(0,[z0,z1,z122,z11,z3,z5,z6]),(0,[z0,z1,z323,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z324,z5,z6])],[(0,[z257,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z41,z77,z4,z5,z6])],[(0,[z0,z74,z1,z51,z4,z5,z6]),(0,[z0,z1,z3,z4,z325,z5,z6]),(0,[z0,z119,z1,z3,z4,z46,z6]),(0,[z326,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z327,z6]),(0,[z0,z1,z328,z3,z4,z5,z6])],[(0,[z0,z1,z3,z329,z4,z5,z6]),(0,[z0,z90,z1,z12,z3,z5,z6]),(0,[z0,z330,z1,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z4,z62,z6]),(0,[z163,z0,z3,z4,z46,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z6,z331]),(1,[z0,z1,z3,z217,z5,z6]),(1,[z0,z1,z34,z3,z4,z42]),(0,[z0,z1,z3,z332,z4,z5,z6])],[(0,[z128,z0,z1,z3,z4,z5,z131]),(0,[z0,z1,z3,z4,z333,z5,z6]),(0,[z0,z1,z3,z4,z334,z5,z6]),(0,[z0,z1,z3,z4,z46,z6,z42]),(0,[z15,z0,z1,z3,z4,z5,z141]),(0,[z0,z1,z335,z3,z5,z6,z123])],[(0,[z0,z1,z3,z4,z5,z336,z6]),(0,[z14,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z337]),(0,[z0,z1,z12,z3,z165,z5,z6]),(1,[z0,z1,z41,z77,z4,z6])],[(0,[z0,z119,z1,z19,z3,z4,z6]),(0,[z0,z3,z4,z46,z5,z62,z6]),(0,[z0,z1,z3,z338,z4,z5,z6]),(0,[z0,z1,z3,z120,z5,z218,z6]),(1,[z0,z1,z3,z4,z35,z48])],[(0,[z0,z339,z1,z3,z4,z5,z6]),(0,[z0,z1,z154,z4,z311,z5,z6]),(0,[z0,z1,z340,z3,z4,z5,z6]),(0,[z30,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z3,z77,z4,z235,z6]),(0,[z0,z1,z51,z4,z5,z6,z39]),(0,[z0,z1,z3,z4,z165,z5,z6]),(0,[z15,z0,z101,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z3,z5,z6]),(0,[z0,z1,z11,z3,z120,z5,z6]),(0,[z0,z1,z11,z3,z5,z6,z123]),(0,[z0,z1,z19,z3,z4,z35,z6]),(0,[z0,z1,z341,z4,z5,z48,z6])],[(0,[z0,z24,z1,z3,z165,z5,z6]),(0,[z0,z1,z20,z3,z4,z6,z42])],[(0,[z342,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z343,z5,z6]),(0,[z0,z1,z3,z4,z5,z344,z6]),(0,[z0,z1,z3,z345,z4,z5,z6]),(0,[z0,z1,z3,z197,z4,z5,z6]),(1,[z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z346,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z347]),(1,[z0,z75,z3,z165,z5,z6]),(0,[z0,z3,z76,z4,z165,z5,z6]),(0,[z0,z1,z3,z348,z4,z5,z6]),(0,[z349,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z60,z138,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z350,z6])]],
   [[(0,[z14,z0,z1,z3,z4,z48,z6]),(0,[z0,z1,z351,z3,z51,z5,z6]),(0,[z0,z1,z122,z12,z3,z5,z6]),(0,[z0,z1,z3,z151,z5,z48,z6])],[(0,[z14,z0,z1,z3,z4,z88,z6]),(0,[z15,z352,z1,z3,z4,z5,z6]),(0,[z0,z1,z353,z3,z4,z5,z6]),(0,[z354,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z11,z3,z5,z6,z131]),(0,[z0,z1,z3,z4,z5,z355,z6]),(0,[z0,z1,z3,z5,z314,z6,z317])],[(0,[z163,z0,z119,z3,z4,z5,z6]),(0,[z0,z356,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z357]),(0,[z0,z1,z3,z221,z5,z68,z6])],[(0,[z0,z1,z12,z3,z5,z235,z6]),(0,[z358,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z359,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z360,z5,z6])],[(0,[z0,z1,z3,z4,z361,z5,z6]),(0,[z362,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z47,z6])],[(0,[z0,z1,z3,z4,z5,z235,z6]),(1,[z0,z1,z129,z4,z5,z6]),(0,[z56,z1,z3,z4,z5,z57,z6]),(0,[z363,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z364,z3,z4,z5,z6]),(0,[z132,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z12,z3,z5,z6,z42])],[(0,[z0,z1,z3,z4,z5,z365,z6]),(0,[z0,z1,z3,z366,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z367])]],
   [[(0,[z0,z1,z368,z3,z4,z5,z6]),(0,[z0,z1,z369,z3,z4,z5,z6]),(0,[z0,z1,z370,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z371,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z42])],[(0,[z21,z242,z1,z3,z4,z5,z6]),(0,[z0,z1,z233,z3,z4,z311,z6]),(0,[z0,z1,z372,z3,z4,z5,z6]),(0,[z0,z1,z351,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z373]),(0,[z0,z1,z11,z3,z374,z5,z6]),(0,[z0,z1,z3,z4,z5,z375,z6])],[(0,[z194,z0,z1,z3,z252,z5,z6]),(0,[z0,z1,z12,z3,z311,z5,z6]),(0,[z56,z0,z1,z3,z4,z5,z131]),(1,[z0,z1,z281,z4,z5,z6]),(0,[z0,z1,z12,z3,z5,z313,z6]),(0,[z0,z1,z12,z3,z5,z314,z6]),(1,[z0,z1,z3,z4,z315,z6])],[(0,[z0,z1,z376,z3,z4,z5,z6]),(0,[z0,z1,z377,z3,z4,z5,z6]),(0,[z0,z1,z3,z378,z4,z5,z6])],[(0,[z0,z1,z3,z4,z379,z5,z6]),(0,[z380,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z311,z5,z6]),(0,[z0,z1,z381,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z313,z6]),(0,[z0,z1,z3,z4,z382,z6,z141]),(0,[z0,z1,z3,z4,z5,z383,z6])],[(0,[z0,z1,z3,z4,z384,z5,z6]),(0,[z0,z1,z3,z4,z5,z385,z6]),(0,[z0,z1,z3,z4,z386,z5,z6])],[(0,[z0,z1,z11,z3,z5,z48,z6]),(0,[z0,z1,z3,z4,z5,z387,z6])],[(0,[z0,z1,z3,z4,z5,z6,z388]),(1,[z0,z1,z3,z325,z5,z6]),(0,[z389,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z95,z4,z6])]],
   [[(0,[z56,z1,z36,z3,z4,z5,z6]),(0,[z390,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z51,z4,z5,z6]),(1,[z0,z1,z391,z3,z5,z6]),(1,[z0,z1,z164,z4,z5,z6]),(1,[z0,z1,z328,z3,z5,z6]),(0,[z0,z392,z1,z3,z4,z5,z6]),(1,[z0,z1,z4,z5,z6,z305])],[(0,[z90,z1,z36,z3,z4,z5,z6]),(0,[z0,z1,z20,z3,z4,z35,z6]),(0,[z0,z393,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z394])],[(0,[z395,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z396,z3,z4,z5,z6]),(0,[z128,z0,z7,z3,z4,z5,z6]),(0,[z0,z1,z397,z3,z4,z5,z6])],[(0,[z14,z0,z1,z34,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z130,z6]),(0,[z0,z1,z3,z398,z4,z5,z6]),(0,[z0,z1,z11,z3,z5,z166,z6]),(0,[z349,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z3,z399,z4,z5,z6])],[(0,[z0,z400,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z64,z3,z5,z6])],[(0,[z0,z1,z3,z4,z88,z97,z6]),(0,[z0,z1,z12,z3,z120,z5,z6]),(0,[z0,z1,z12,z3,z5,z6,z123]),(0,[z0,z1,z34,z3,z77,z4,z6]),(1,[z0,z1,z19,z335,z3,z6])],[(0,[z242,z90,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z273,z4,z311,z6]),(0,[z0,z74,z1,z3,z325,z5,z6]),(0,[z0,z401,z1,z3,z4,z5,z6]),(0,[z0,z1,z59,z11,z3,z5,z6]),(0,[z0,z1,z402,z3,z4,z5,z6])],[(0,[z0,z403,z1,z3,z4,z5,z6]),(0,[z0,z1,z20,z4,z5,z97,z6])]],
   [[],[(1,[z0,z1,z321,z3,z4,z6]),(0,[z0,z1,z404,z3,z4,z5,z6]),(0,[z405,z0,z1,z3,z4,z5,z6]),(1,[z56,z1,z3,z4,z5,z57]),(0,[z0,z406,z1,z3,z4,z5,z6]),(0,[z0,z1,z407,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z408])],[(1,[z0,z1,z3,z273,z4,z6]),(0,[z0,z1,z3,z4,z5,z409,z6]),(0,[z0,z1,z3,z410,z4,z5,z6]),(0,[z0,z1,z198,z11,z3,z5,z6])],[(1,[z0,z1,z12,z138,z5,z6]),(0,[z411,z0,z1,z3,z4,z5,z6])],[(0,[z194,z0,z1,z11,z3,z5,z6]),(0,[z18,z0,z1,z3,z120,z4,z6]),(0,[z0,z1,z3,z4,z5,z155,z6]),(0,[z0,z75,z1,z3,z165,z5,z6]),(0,[z0,z1,z370,z12,z3,z5,z6]),(0,[z412,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z413,z6]),(0,[z414,z0,z1,z3,z4,z5,z6])],[(0,[z415,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z221,z81,z5,z6]),(1,[z0,z1,z11,z12,z5,z6]),(0,[z0,z1,z3,z4,z5,z416,z6]),(0,[z0,z1,z417,z3,z4,z5,z6])],[(0,[z0,z1,z3,z418,z4,z5,z6]),(1,[z0,z153,z51,z4,z5,z6]),(0,[z0,z1,z419,z3,z4,z5,z6]),(0,[z0,z1,z420,z3,z4,z5,z6]),(0,[z0,z1,z19,z3,z120,z5,z6]),(0,[z0,z1,z3,z4,z421,z5,z6]),(0,[z0,z422,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z287,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z423,z5,z6]),(1,[z0,z1,z197,z4,z5,z6]),(0,[z0,z1,z3,z4,z424,z5,z6]),(1,[z0,z1,z3,z4,z6,z425])],[(0,[z0,z1,z3,z4,z5,z6,z426]),(1,[z0,z1,z3,z4,z427,z6]),(0,[z0,z153,z74,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z249,z5,z6]),(0,[z0,z1,z12,z3,z5,z6,z141]),(0,[z0,z101,z3,z4,z5,z313,z6]),(0,[z0,z1,z335,z428,z4,z5,z6])],[(0,[z194,z0,z1,z138,z4,z5,z6]),(0,[z0,z1,z429,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z35,z235,z6]),(0,[z163,z0,z1,z41,z3,z4,z6]),(0,[z0,z1,z59,z12,z3,z5,z6]),(0,[z0,z430,z1,z3,z4,z5,z6]),(0,[z0,z1,z157,z3,z5,z6,z39])],[(0,[z0,z1,z3,z4,z431,z5,z6]),(0,[z0,z432,z1,z3,z4,z5,z6]),(0,[z0,z74,z1,z106,z4,z5,z6]),(0,[z0,z1,z433,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z141]),(0,[z0,z1,z11,z335,z3,z5,z6]),(0,[z0,z1,z3,z4,z434,z5,z6])],[(0,[z30,z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z435,z4,z5,z6]),(0,[z0,z1,z3,z4,z436,z5,z6]),(0,[z0,z1,z437,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z438,z5,z6]),(0,[z439,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z440,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z244])],[(0,[z0,z1,z3,z441,z4,z5,z6]),(0,[z0,z1,z3,z4,z46,z97,z6]),(0,[z0,z1,z442,z3,z4,z5,z6])],[(1,[z0,z1,z23,z4,z5,z6]),(0,[z0,z443,z1,z3,z4,z5,z6]),(1,[z0,z153,z1,z11,z5,z6]),(0,[z0,z1,z444,z3,z4,z5,z6]),(0,[z445,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z446,z6]),(0,[z128,z0,z1,z3,z110,z5,z6]),(0,[z0,z1,z11,z3,z51,z5,z6]),(1,[z0,z1,z3,z291,z5,z6]),(0,[z0,z1,z12,z3,z5,z48,z6])]],
   [[(0,[z194,z0,z1,z12,z3,z5,z6]),(0,[z0,z119,z1,z3,z4,z235,z6]),(1,[z0,z1,z351,z3,z5,z6]),(0,[z0,z447,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z448,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z449,z6]),(0,[z0,z1,z3,z4,z97,z48,z6]),(0,[z0,z1,z3,z4,z5,z6,z450]),(0,[z0,z1,z451,z3,z4,z5,z6]),(0,[z0,z452,z1,z3,z4,z5,z6])],[(0,[z453,z0,z1,z3,z4,z5,z6]),(0,[z14,z1,z3,z4,z88,z5,z6]),(0,[z454,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z228,z6]),(0,[z0,z1,z19,z3,z77,z4,z6]),(0,[z0,z1,z3,z4,z5,z48,z6])],[(0,[z0,z1,z23,z4,z311,z5,z6]),(0,[z0,z1,z455,z3,z4,z5,z6]),(0,[z0,z456,z1,z3,z4,z5,z6]),(0,[z0,z1,z402,z12,z3,z5,z6]),(0,[z0,z1,z41,z3,z77,z4,z6]),(0,[z457,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z311,z165,z5,z6]),(0,[z0,z1,z3,z4,z5,z458,z6]),(0,[z0,z1,z3,z4,z235,z6,z42]),(0,[z163,z0,z1,z19,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z459])],[(0,[z0,z1,z12,z3,z5,z166,z6]),(0,[z0,z1,z3,z4,z5,z6,z39])],[(0,[z21,z0,z1,z3,z460,z5,z6]),(0,[z242,z0,z1,z3,z4,z108,z6]),(0,[z0,z1,z12,z64,z3,z5,z6]),(1,[z163,z0,z3,z4,z46,z6]),(0,[z0,z1,z404,z12,z3,z5,z6]),(1,[z0,z1,z12,z3,z134,z6]),(0,[z0,z1,z3,z217,z4,z5,z6]),(0,[z0,z1,z335,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z166,z6]),(0,[z0,z1,z3,z461,z4,z5,z6])],[(1,[z21,z36,z3,z4,z5,z6]),(0,[z462,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z463,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z425])]],
   [[(0,[z0,z1,z464,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z465,z6]),(0,[z0,z1,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z466,z4,z5,z6]),(0,[z0,z1,z3,z467,z4,z5,z6]),(0,[z0,z1,z3,z4,z468,z5,z6])],[(0,[z0,z1,z245,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z469]),(1,[z0,z1,z3,z470,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z471,z3,z4,z5,z6]),(0,[z0,z472,z1,z3,z4,z5,z6]),(0,[z0,z1,z473,z3,z4,z5,z6]),(0,[z0,z1,z3,z474,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z475]),(0,[z0,z1,z12,z3,z5,z97,z6])],[(0,[z476,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z477,z6]),(0,[z478,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z479]),(0,[z0,z1,z3,z4,z5,z480,z6])],[(0,[z0,z1,z3,z4,z5,z481,z6]),(0,[z0,z1,z3,z4,z5,z6,z482]),(1,[z0,z74,z106,z4,z5,z6]),(0,[z0,z1,z3,z483,z4,z5,z6]),(0,[z484,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z485,z6]),(0,[z0,z1,z3,z4,z486,z5,z6]),(0,[z0,z1,z3,z487,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z97,z6]),(1,[z0,z1,z3,z120,z218,z6]),(0,[z0,z1,z3,z4,z5,z488,z6])],[(0,[z0,z489,z1,z3,z4,z5,z6]),(0,[z257,z1,z3,z4,z311,z5,z6]),(0,[z0,z75,z3,z4,z165,z5,z6]),(0,[z0,z119,z1,z41,z3,z4,z6]),(0,[z490,z0,z1,z3,z4,z5,z6])],[(0,[z242,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z76,z81,z5,z6]),(0,[z1,z3,z4,z5,z57,z6,z131]),(0,[z0,z1,z11,z3,z5,z57,z6]),(0,[z491,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z492,z6])]],
   [[(0,[z493,z0,z1,z3,z4,z5,z6]),(0,[z0,z494,z1,z3,z4,z5,z6]),(0,[z0,z119,z3,z4,z5,z62,z6]),(0,[z163,z0,z1,z3,z4,z48,z6]),(0,[z0,z1,z3,z4,z5,z6,z495])],[(0,[z496,z0,z1,z3,z4,z5,z6]),(0,[z497,z0,z1,z3,z4,z5,z6]),(0,[z163,z0,z1,z3,z4,z88,z6]),(1,[z0,z1,z3,z4,z249,z6]),(0,[z0,z1,z60,z51,z4,z5,z6])],[(0,[z0,z1,z498,z3,z4,z5,z6]),(0,[z0,z1,z59,z60,z4,z5,z6]),(0,[z499,z0,z1,z3,z4,z5,z6])],[(0,[z500,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z60,z20,z4,z5,z6]),(1,[z0,z1,z107,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z501]),(0,[z18,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z12,z335,z3,z5,z6]),(0,[z0,z502,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z470,z5,z314,z6]),(1,[z0,z1,z3,z4,z6,z236])],[(0,[z109,z1,z3,z38,z4,z5,z6]),(0,[z503,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z504,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z505])],[(0,[z21,z1,z36,z3,z4,z5,z6]),(0,[z506,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z507,z4,z5,z6]),(0,[z0,z1,z508,z3,z4,z5,z6]),(0,[z509,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z20,z3,z77,z4,z6])],[(0,[z0,z1,z3,z4,z510,z5,z6]),(0,[z0,z1,z3,z511,z4,z5,z6]),(1,[z194,z1,z64,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z512,z6]),(0,[z0,z1,z34,z3,z4,z5,z6])]],
   [[(1,[z0,z1,z245,z3,z4,z6]),(0,[z0,z1,z12,z3,z51,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z513])],[(0,[z1,z36,z3,z4,z5,z6,z131]),(1,[z109,z0,z1,z11,z5,z6]),(0,[z514,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z515,z6]),(0,[z0,z1,z516,z3,z4,z5,z6])],[(0,[z242,z0,z1,z12,z3,z5,z6]),(0,[z1,z3,z81,z4,z311,z5,z6]),(1,[z0,z101,z3,z4,z5,z313]),(0,[z0,z517,z1,z3,z4,z5,z6])],[(0,[z518,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z519,z3,z4,z5,z6]),(0,[z0,z1,z12,z397,z3,z5,z6]),(0,[z520,z0,z1,z3,z4,z5,z6])],[(0,[z18,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z521,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z13])],[(0,[z0,z522,z1,z3,z4,z5,z6]),(0,[z523,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z81,z165,z5,z6]),(0,[z0,z119,z1,z20,z3,z4,z6]),(0,[z0,z1,z138,z4,z5,z6,z39]),(1,[z0,z1,z3,z4,z124,z6]),(0,[z0,z1,z3,z4,z35,z48,z6])],[(0,[z0,z90,z101,z3,z4,z5,z6]),(0,[z0,z1,z3,z311,z5,z6,z123]),(0,[z0,z1,z3,z4,z35,z88,z6]),(0,[z0,z1,z12,z524,z3,z5,z6]),(1,[z0,z1,z3,z316,z4,z6]),(0,[z0,z1,z19,z335,z3,z5,z6]),(1,[z0,z1,z4,z5,z6,z244])],[(0,[z0,z1,z525,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z526,z6]),(0,[z527,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z528,z4,z5,z6]),(0,[z0,z1,z529,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z130,z6]),(1,[z0,z119,z3,z4,z62,z6]),(0,[z0,z1,z530,z3,z4,z5,z6]),(0,[z15,z0,z3,z4,z5,z6,z141]),(0,[z0,z1,z34,z11,z3,z5,z6]),(0,[z0,z1,z138,z4,z5,z166,z6])]],
   [[(0,[z0,z1,z321,z3,z4,z5,z6]),(0,[z531,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z532,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z533,z6])],[(0,[z0,z1,z64,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z46,z5,z6]),(0,[z534,z0,z1,z3,z4,z5,z6]),(0,[z535,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z536,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z537,z5,z6]),(0,[z14,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z538,z3,z4,z5,z6])],[(0,[z539,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z540,z5,z6]),(0,[z0,z119,z1,z3,z4,z48,z6]),(0,[z163,z0,z1,z34,z3,z4,z6]),(0,[z0,z1,z3,z4,z5,z6,z236])],[(0,[z21,z0,z1,z3,z510,z5,z6]),(0,[z0,z1,z3,z4,z5,z541,z6]),(0,[z0,z1,z542,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z4,z88,z6]),(0,[z0,z153,z1,z3,z4,z5,z6]),(0,[z0,z24,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z63,z6]),(0,[z0,z1,z3,z543,z4,z5,z6])],[(0,[z0,z544,z1,z3,z4,z5,z6]),(0,[z128,z56,z1,z3,z4,z5,z6]),(1,[z0,z1,z308,z3,z4,z6]),(0,[z545,z0,z1,z3,z4,z5,z6]),(0,[z523,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z138,z4,z5,z97,z6]),(0,[z0,z1,z3,z120,z4,z97,z6]),(0,[z0,z1,z60,z3,z316,z4,z6]),(0,[z0,z1,z3,z4,z5,z546,z6]),(0,[z547,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z548,z3,z4,z5,z6]),(0,[z0,z1,z549,z3,z4,z5,z6]),(0,[z550,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z5,z6,z317])],[(0,[z0,z1,z12,z3,z5,z57,z6]),(0,[z0,z1,z281,z4,z165,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z551]),(0,[z0,z552,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z314,z6])]],
   [[(0,[z553,z0,z1,z3,z4,z5,z6]),(0,[z194,z0,z1,z11,z4,z5,z6]),(0,[z18,z0,z1,z12,z3,z5,z6]),(1,[z0,z1,z3,z4,z155,z6]),(0,[z0,z1,z3,z4,z5,z6,z554]),(0,[z0,z1,z3,z221,z165,z5,z6]),(0,[z0,z1,z3,z4,z62,z97,z6]),(0,[z0,z1,z335,z3,z120,z4,z6]),(1,[z0,z1,z3,z221,z5,z68])],[(0,[z555,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z556,z6]),(1,[z352,z1,z3,z4,z5,z6]),(0,[z506,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z557,z3,z4,z5,z6]),(0,[z0,z558,z1,z3,z4,z5,z6]),(0,[z0,z1,z318,z3,z4,z5,z6])],[(0,[z559,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z34,z12,z3,z5,z6]),(0,[z0,z1,z19,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z560,z6]),(0,[z0,z153,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z190,z4,z165,z6]),(0,[z0,z1,z41,z3,z4,z5,z6])],[(0,[z0,z1,z561,z3,z4,z5,z6]),(0,[z0,z1,z562,z3,z4,z5,z6]),(0,[z0,z563,z1,z3,z4,z5,z6])],[(0,[z0,z564,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z165,z5,z6,z123]),(0,[z0,z1,z3,z4,z5,z6,z565]),(0,[z566,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z567,z5,z6])],[(0,[z568,z0,z1,z3,z4,z5,z6]),(0,[z242,z0,z36,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z235,z97,z6]),(0,[z0,z1,z85,z3,z5,z97,z6]),(0,[z0,z1,z19,z3,z4,z218,z6]),(0,[z0,z1,z3,z4,z569,z5,z6])]],
   [[(1,[z0,z1,z3,z510,z5,z6]),(0,[z0,z570,z1,z3,z4,z5,z6]),(0,[z163,z0,z1,z3,z4,z235,z6]),(0,[z0,z1,z3,z291,z4,z5,z6]),(0,[z0,z1,z12,z3,z3,z5,z6]),(0,[z0,z1,z3,z4,z315,z5,z6]),(0,[z0,z1,z335,z3,z221,z5,z6]),(0,[z0,z1,z341,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z571,z6]),(0,[z0,z1,z70,z3,z4,z5,z6]),(0,[z0,z1,z572,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z110,z5,z6]),(0,[z15,z462,z1,z3,z4,z5,z6]),(0,[z0,z1,z335,z3,z5,z218,z6]),(0,[z0,z1,z3,z573,z4,z5,z6])],[(0,[z18,z0,z1,z3,z4,z46,z6]),(0,[z0,z1,z106,z3,z4,z5,z6]),(0,[z0,z153,z1,z138,z4,z5,z6]),(0,[z0,z1,z50,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z95,z5,z6]),(0,[z0,z1,z60,z3,z4,z5,z39]),(0,[z574,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z123]),(0,[z0,z1,z3,z4,z35,z5,z42])],[(0,[z575,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z576,z5,z6]),(0,[z18,z0,z1,z3,z4,z62,z6]),(0,[z0,z1,z3,z577,z4,z5,z6]),(0,[z0,z1,z11,z3,z221,z5,z6])],[(0,[z0,z1,z578,z3,z4,z5,z6]),(0,[z579,z0,z1,z3,z4,z5,z6]),(0,[z128,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z580,z6]),(0,[z0,z1,z41,z11,z3,z5,z6]),(0,[z0,z1,z11,z3,z138,z5,z6]),(0,[z0,z1,z11,z3,z5,z218,z6]),(1,[z0,z1,z341,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z581,z6]),(0,[z582,z0,z1,z3,z4,z5,z6])],[(0,[z242,z0,z90,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z5,z6,z131]),(0,[z0,z119,z1,z34,z3,z4,z6]),(0,[z0,z1,z3,z583,z4,z5,z6])],[(0,[z257,z0,z1,z3,z311,z5,z6]),(1,[z0,z1,z3,z205,z5,z6]),(0,[z0,z1,z3,z4,z5,z584,z6])]],
   [[(0,[z0,z1,z585,z3,z4,z5,z6]),(0,[z586,z0,z1,z3,z4,z5,z6]),(0,[z257,z0,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z221,z311,z5,z6]),(0,[z0,z1,z3,z81,z5,z6,z123]),(0,[z0,z1,z3,z4,z5,z6,z131]),(0,[z0,z153,z1,z12,z3,z5,z6]),(1,[z0,z1,z3,z190,z4,z6]),(0,[z0,z1,z587,z3,z4,z5,z6]),(0,[z0,z1,z3,z221,z4,z5,z68]),(0,[z0,z1,z3,z4,z5,z588,z6])],[(0,[z15,z0,z1,z3,z567,z5,z6])],[(0,[z589,z0,z1,z3,z4,z5,z6]),(0,[z194,z1,z64,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z46,z5,z6]),(0,[z0,z1,z66,z3,z4,z5,z6]),(0,[z0,z1,z41,z138,z4,z5,z6]),(0,[z0,z1,z59,z3,z4,z5,z314])],[(1,[z128,z1,z3,z4,z5,z131]),(0,[z590,z0,z1,z3,z4,z5,z6]),(0,[z0,z352,z1,z3,z4,z5,z6])],[(0,[z128,z0,z1,z162,z4,z5,z6]),(0,[z0,z1,z3,z4,z427,z5,z6]),(0,[z128,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z591,z3,z4,z5,z6]),(1,[z0,z1,z444,z3,z4,z6]),(0,[z0,z1,z592,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z4,z6,z42])],[(1,[z0,z1,z473,z3,z4,z6]),(0,[z0,z3,z4,z5,z313,z6,z141]),(0,[z0,z1,z3,z151,z4,z5,z6])],[(0,[z30,z0,z1,z3,z311,z5,z6]),(0,[z0,z1,z3,z4,z5,z593,z6]),(0,[z0,z1,z60,z106,z4,z5,z6]),(0,[z0,z1,z594,z3,z4,z5,z6]),(0,[z0,z1,z595,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z596,z5,z6])],[(0,[z109,z0,z1,z3,z4,z571,z6]),(0,[z0,z1,z597,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z62,z6,z42]),(1,[z462,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z374,z5,z6]),(0,[z0,z1,z598,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z5,z571,z6]),(1,[z0,z1,z233,z3,z4,z6]),(0,[z0,z1,z3,z599,z4,z5,z6]),(0,[z600,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z41,z12,z3,z5,z6]),(0,[z0,z1,z524,z3,z4,z5,z6]),(0,[z0,z1,z20,z3,z4,z5,z6]),(0,[z0,z1,z3,z601,z4,z5,z6])],[(0,[z602,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z384,z5,z6]),(0,[z0,z1,z308,z3,z4,z5,z6]),(0,[z0,z1,z3,z77,z4,z5,z6])],[(0,[z0,z603,z1,z3,z4,z5,z6]),(0,[z604,z0,z1,z3,z4,z5,z6]),(1,[z30,z1,z3,z81,z5,z6]),(0,[z0,z1,z605,z3,z4,z5,z6]),(0,[z606,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z607,z3,z4,z5,z6]),(0,[z0,z1,z122,z3,z4,z5,z68])],[(0,[z608,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z609,z4,z5,z6]),(0,[z0,z610,z1,z3,z4,z5,z6]),(0,[z0,z75,z1,z3,z4,z5,z6]),(0,[z0,z1,z28,z3,z4,z5,z6]),(0,[z0,z1,z11,z60,z3,z5,z6]),(0,[z0,z1,z3,z221,z120,z5,z6])],[(0,[z0,z1,z3,z4,z5,z611,z6]),(0,[z0,z1,z258,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z612]),(0,[z0,z1,z613,z3,z4,z5,z6])],[(0,[z14,z0,z1,z3,z120,z4,z6]),(0,[z56,z0,z1,z3,z4,z5,z6]),(0,[z0,z614,z1,z3,z4,z5,z6]),(0,[z615,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z616,z3,z4,z5,z6]),(0,[z0,z1,z617,z3,z4,z5,z6])],[(0,[z618,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z567,z5,z6]),(0,[z0,z1,z597,z11,z3,z5,z6]),(0,[z0,z1,z437,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z619,z6]),(0,[z0,z620,z1,z3,z4,z5,z6]),(0,[z0,z1,z621,z3,z4,z5,z6])]],
   [[(0,[z109,z0,z1,z38,z4,z5,z6]),(0,[z128,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z622,z6])],[(0,[z0,z1,z3,z4,z623,z5,z6]),(0,[z30,z257,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z624,z4,z5,z6]),(0,[z0,z1,z3,z4,z625,z5,z6]),(0,[z0,z1,z626,z3,z4,z5,z6])],[(0,[z0,z1,z59,z4,z5,z6,z39]),(0,[z0,z1,z4,z5,z68,z6,z305])],[],[(1,[z194,z0,z1,z11,z5,z6]),(0,[z15,z0,z1,z3,z398,z5,z6]),(0,[z0,z1,z627,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z35,z5,z6]),(0,[z0,z1,z12,z3,z221,z5,z6])],[(1,[z0,z1,z3,z4,z91,z6]),(0,[z0,z1,z287,z3,z38,z5,z6]),(0,[z56,z0,z1,z11,z3,z5,z6]),(0,[z163,z0,z1,z20,z3,z4,z6]),(0,[z0,z1,z12,z3,z138,z5,z6]),(0,[z0,z1,z12,z3,z5,z218,z6]),(0,[z0,z1,z3,z628,z4,z5,z6]),(0,[z0,z1,z328,z3,z77,z5,z6])],[(0,[z0,z1,z629,z3,z4,z5,z6])],[(0,[z630,z0,z1,z3,z4,z5,z6]),(0,[z0,z631,z1,z3,z4,z5,z6]),(0,[z0,z1,z59,z3,z4,z5,z39]),(0,[z0,z1,z3,z4,z5,z218,z6])]],
   [[(0,[z632,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z76,z311,z5,z6]),(0,[z0,z1,z633,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z634,z6]),(0,[z0,z1,z60,z4,z5,z314,z6]),(0,[z0,z1,z3,z120,z4,z35,z6])],[(0,[z0,z1,z635,z3,z4,z5,z6]),(0,[z0,z1,z11,z587,z3,z5,z6]),(0,[z0,z1,z11,z3,z5,z6,z225]),(0,[z0,z430,z1,z12,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z636,z6]),(0,[z0,z1,z3,z428,z4,z5,z6]),(0,[z0,z1,z3,z221,z4,z5,z123])],[(0,[z0,z1,z391,z3,z51,z5,z6]),(0,[z0,z1,z3,z4,z5,z79,z6]),(0,[z637,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z228,z5,z6]),(0,[z0,z1,z11,z11,z3,z5,z6]),(0,[z0,z638,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z639,z6]),(0,[z0,z1,z3,z470,z4,z5,z6])],[(1,[z0,z1,z3,z460,z5,z6]),(0,[z0,z1,z3,z252,z4,z5,z6]),(0,[z0,z1,z11,z3,z88,z5,z6]),(0,[z0,z1,z3,z4,z5,z640,z6]),(0,[z0,z1,z318,z4,z5,z68,z6])],[(0,[z641,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z642]),(0,[z0,z1,z3,z4,z35,z5,z48])],[(1,[z0,z1,z3,z4,z254,z6]),(0,[z0,z1,z3,z4,z5,z643,z6]),(0,[z0,z1,z607,z12,z3,z5,z6])],[(0,[z0,z1,z3,z4,z210,z5,z6]),(0,[z0,z101,z1,z3,z4,z5,z313])]],
   [[(0,[z644,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z256,z5,z6]),(0,[z645,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6]),(0,[z0,z1,z473,z3,z51,z4,z6])],[(0,[z646,z0,z1,z3,z4,z5,z6]),(0,[z56,z0,z1,z12,z3,z5,z6]),(1,[z0,z1,z50,z3,z4,z6]),(0,[z0,z1,z455,z12,z3,z5,z6])],[(0,[z0,z647,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z648,z6]),(1,[z0,z1,z3,z398,z5,z6]),(0,[z649,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z650,z6]),(0,[z0,z90,z1,z3,z4,z526,z6]),(0,[z0,z1,z3,z38,z4,z5,z6]),(0,[z0,z1,z391,z3,z4,z5,z6]),(0,[z0,z1,z3,z76,z5,z6,z123]),(0,[z0,z1,z122,z3,z4,z5,z123])],[(0,[z0,z1,z3,z4,z5,z91,z6]),(0,[z0,z1,z12,z60,z3,z5,z6]),(0,[z0,z1,z157,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z651,z5,z6])],[(0,[z0,z652,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z653,z6])],[(0,[z0,z1,z3,z654,z4,z5,z6]),(1,[z0,z1,z3,z4,z382,z6])],[(0,[z0,z1,z3,z655,z4,z5,z6]),(0,[z0,z1,z656,z3,z4,z5,z6]),(0,[z0,z1,z3,z77,z4,z46,z6]),(0,[z0,z1,z11,z12,z3,z5,z6]),(0,[z0,z1,z3,z657,z4,z5,z6])]],
   [[(1,[z242,z90,z3,z4,z5,z6]),(0,[z0,z1,z3,z658,z4,z5,z6]),(0,[z0,z153,z1,z11,z4,z5,z6]),(0,[z0,z1,z3,z77,z4,z62,z6]),(0,[z0,z1,z60,z3,z4,z5,z314]),(0,[z0,z1,z659,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z660,z6]),(0,[z0,z1,z11,z20,z3,z5,z6]),(0,[z0,z1,z3,z5,z68,z6,z123])],[(0,[z0,z1,z3,z4,z661,z5,z6]),(0,[z109,z0,z1,z64,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z662]),(0,[z18,z1,z3,z4,z5,z235,z6]),(0,[z0,z101,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z663,z5,z6])],[(0,[z0,z1,z3,z664,z4,z5,z6]),(0,[z0,z1,z3,z4,z665,z5,z6]),(0,[z0,z666,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z667,z6])],[(0,[z18,z0,z1,z3,z4,z235,z6]),(1,[z14,z1,z3,z4,z88,z6]),(0,[z0,z1,z668,z3,z4,z5,z6]),(0,[z514,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z12,z3,z4,z5,z6]),(0,[z0,z1,z3,z77,z120,z4,z6])],[(0,[z0,z1,z3,z4,z5,z254,z6]),(0,[z0,z1,z3,z669,z4,z5,z6])],[(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z5,z313]),(0,[z0,z1,z3,z4,z5,z670,z6])],[]],
   [[(0,[z671,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z526,z5,z6]),(0,[z0,z1,z41,z11,z4,z5,z6]),(0,[z0,z1,z3,z4,z78,z5,z6])],[(0,[z0,z1,z3,z4,z5,z672,z6]),(0,[z0,z90,z3,z4,z5,z6,z141]),(0,[z0,z1,z4,z5,z314,z6,z39]),(0,[z0,z673,z1,z3,z4,z5,z6]),(0,[z0,z1,z34,z3,z4,z6,z42])],[(1,[z0,z1,z306,z3,z4,z6]),(0,[z0,z1,z164,z3,z4,z5,z6]),(0,[z0,z101,z1,z11,z3,z5,z6]),(0,[z0,z1,z60,z77,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z674,z6])],[(0,[z242,z1,z3,z4,z5,z6,z131]),(0,[z1,z64,z3,z38,z4,z5,z6]),(0,[z194,z0,z1,z3,z384,z5,z6]),(0,[z128,z0,z1,z3,z4,z427,z6]),(0,[z0,z1,z3,z675,z4,z5,z6]),(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z444,z3,z4,z6,z141])],[(0,[z1,z3,z4,z88,z5,z235,z6]),(0,[z0,z1,z3,z4,z677,z5,z6]),(0,[z0,z1,z3,z4,z5,z57,z6]),(0,[z0,z1,z3,z4,z678,z5,z6]),(0,[z0,z153,z1,z51,z4,z5,z6]),(0,[z0,z1,z11,z3,z5,z68,z6]),(0,[z0,z1,z679,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z680,z6]),(0,[z0,z1,z3,z4,z5,z681,z6]),(0,[z14,z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z12,z3,z88,z5,z6]),(0,[z0,z297,z1,z3,z4,z5,z6]),(0,[z0,z119,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z382,z6]),(0,[z0,z1,z682,z3,z4,z5,z6])],[(0,[z128,z0,z258,z3,z4,z5,z6]),(0,[z15,z0,z1,z28,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z86])],[(0,[z0,z1,z3,z460,z4,z5,z6]),(0,[z0,z1,z3,z683,z4,z5,z6]),(0,[z0,z1,z3,z4,z88,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z684]),(0,[z0,z24,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z685,z4,z5,z6]),(0,[z0,z1,z686,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z687])]],
   [[(0,[z0,z1,z3,z4,z5,z688,z6]),(0,[z0,z1,z689,z3,z4,z5,z6]),(0,[z0,z1,z10,z3,z4,z5,z6]),(0,[z0,z1,z107,z335,z4,z5,z6]),(0,[z0,z1,z3,z690,z4,z5,z6])],[(0,[z18,z0,z1,z41,z3,z4,z6]),(0,[z0,z1,z306,z3,z4,z6,z131]),(0,[z15,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z691,z6]),(0,[z0,z1,z3,z205,z4,z5,z6]),(0,[z128,z0,z1,z3,z4,z5,z57]),(0,[z0,z1,z3,z692,z4,z5,z6]),(0,[z0,z1,z12,z138,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z693])],[(0,[z21,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z694,z6]),(0,[z0,z1,z3,z120,z5,z6,z123]),(1,[z0,z1,z428,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z695,z6])],[(0,[z0,z1,z3,z4,z5,z6,z696]),(0,[z0,z1,z3,z4,z697,z5,z6]),(0,[z0,z1,z12,z3,z5,z698,z6])],[(1,[z0,z1,z3,z4,z256,z6]),(0,[z0,z1,z699,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z63,z6]),(0,[z0,z1,z19,z335,z3,z4,z6])],[(0,[z0,z1,z36,z3,z4,z5,z6]),(0,[z109,z0,z1,z3,z4,z210,z6]),(0,[z0,z1,z3,z4,z5,z6,z700]),(0,[z0,z101,z1,z12,z3,z5,z6]),(0,[z0,z1,z19,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z5,z698,z6]),(0,[z0,z1,z41,z20,z4,z5,z6]),(0,[z0,z1,z701,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z314,z6,z425])],[(0,[z0,z702,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z703,z6]),(0,[z0,z1,z3,z4,z704,z5,z6]),(0,[z0,z1,z686,z11,z3,z5,z6]),(0,[z0,z1,z11,z60,z4,z5,z6]),(0,[z531,z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z705,z3,z4,z5,z6]),(0,[z0,z1,z3,z221,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z706,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(1,[z1,z3,z707,z5,z6]),(0,[z0,z1,z11,z5,z6,z244]),(0,[z0,z1,z3,z708,z6,z86])],[(0,[z0,z1,z709,z4,z5,z6]),(0,[z0,z1,z11,z46,z97,z6]),(0,[z15,z0,z3,z4,z5,z141])],[(1,[z0,z1,z11,z571,z6]),(0,[z0,z710,z3,z4,z5,z6]),(0,[z0,z1,z129,z205,z5,z6]),(0,[z0,z1,z50,z11,z3,z6]),(0,[z0,z1,z50,z12,z3,z6]),(0,[z462,z1,z12,z3,z5,z6]),(0,[z0,z1,z428,z120,z4,z6]),(0,[z0,z1,z318,z5,z6,z123])],[(0,[z0,z1,z3,z711,z5,z6]),(0,[z257,z1,z3,z273,z311,z6]),(0,[z0,z1,z712,z3,z4,z6]),(0,[z0,z1,z12,z28,z5,z6]),(0,[z0,z1,z713,z4,z97,z6]),(0,[z0,z1,z3,z713,z4,z6])],[(0,[z0,z1,z11,z3,z91,z6]),(0,[z0,z1,z245,z12,z3,z6]),(0,[z0,z1,z12,z624,z5,z6]),(0,[z0,z153,z473,z51,z4,z6]),(0,[z0,z1,z11,z3,z714,z6]),(0,[z0,z1,z11,z5,z134,z6]),(0,[z0,z1,z11,z304,z5,z6]),(0,[z0,z192,z1,z11,z5,z6]),(0,[z0,z1,z3,z151,z5,z6]),(0,[z0,z1,z122,z3,z5,z123]),(0,[z0,z1,z3,z124,z6,z123])],[(0,[z242,z90,z3,z4,z256,z6]),(0,[z0,z1,z34,z3,z4,z204]),(0,[z0,z1,z3,z4,z254,z6]),(0,[z0,z1,z279,z3,z5,z123]),(0,[z0,z1,z715,z4,z5,z6]),(0,[z0,z1,z716,z3,z5,z6]),(0,[z0,z1,z717,z3,z5,z6])],[(0,[z128,z1,z129,z4,z5,z131]),(0,[z0,z1,z308,z164,z4,z6]),(0,[z0,z1,z530,z3,z4,z42]),(0,[z0,z1,z28,z398,z5,z6]),(0,[z0,z1,z419,z11,z5,z6]),(0,[z0,z1,z11,z60,z79,z6]),(0,[z0,z1,z3,z120,z47,z6]),(0,[z0,z1,z12,z3,z79,z6])],[(0,[z0,z1,z718,z3,z5,z6]),(0,[z1,z3,z81,z707,z5,z6]),(0,[z0,z1,z3,z5,z6,z719]),(0,[z0,z1,z129,z4,z427,z6]),(0,[z0,z1,z3,z720,z5,z6]),(0,[z0,z1,z3,z721,z5,z6]),(0,[z0,z1,z281,z190,z4,z6]),(0,[z520,z0,z1,z11,z5,z6]),(0,[z0,z1,z34,z11,z97,z6]),(0,[z0,z1,z41,z328,z77,z6]),(0,[z0,z1,z722,z3,z4,z6])]],
   [[(0,[z0,z1,z723,z4,z5,z6]),(0,[z0,z1,z724,z3,z5,z6]),(0,[z0,z1,z3,z725,z4,z6]),(0,[z0,z1,z11,z5,z6,z39])],[(0,[z194,z1,z12,z64,z5,z6]),(0,[z0,z1,z726,z3,z4,z6]),(0,[z224,z1,z3,z4,z235,z6]),(0,[z0,z1,z3,z398,z5,z6]),(0,[z0,z1,z200,z3,z374,z6]),(0,[z0,z1,z3,z4,z375,z42]),(0,[z0,z1,z5,z6,z86,z305]),(0,[z0,z1,z727,z3,z79,z6])],[(0,[z0,z1,z3,z4,z728,z6]),(0,[z0,z1,z729,z4,z5,z6]),(1,[z1,z3,z4,z730,z6]),(0,[z0,z1,z12,z281,z5,z6]),(0,[z0,z1,z3,z4,z731,z6]),(0,[z0,z1,z3,z732,z5,z6]),(0,[z0,z1,z3,z4,z35,z733])],[(0,[z0,z1,z3,z4,z734,z6]),(0,[z0,z1,z735,z3,z4,z6]),(0,[z0,z1,z3,z4,z736,z6]),(0,[z0,z1,z737,z3,z4,z6])],[(0,[z0,z153,z144,z11,z5,z6]),(0,[z0,z1,z11,z5,z303,z6]),(0,[z0,z1,z12,z5,z6,z244]),(0,[z0,z1,z19,z3,z78,z6])],[(0,[z0,z1,z11,z3,z254,z6]),(0,[z0,z1,z164,z190,z4,z6]),(0,[z0,z1,z3,z4,z382,z6]),(0,[z0,z1,z3,z738,z5,z6]),(0,[z0,z1,z739,z3,z4,z6]),(0,[z0,z1,z335,z3,z134,z6]),(0,[z0,z1,z3,z740,z79,z6])],[(0,[z242,z90,z3,z4,z108,z6]),(0,[z257,z1,z233,z3,z311,z6]),(0,[z0,z1,z741,z3,z5,z6])],[(0,[z242,z90,z3,z4,z5,z6]),(0,[z0,z1,z742,z3,z4,z6]),(0,[z0,z1,z3,z743,z5,z6]),(0,[z352,z1,z197,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z744]),(0,[z0,z1,z41,z328,z5,z6])]],
   [[(0,[z415,z0,z1,z11,z5,z6]),(0,[z0,z1,z12,z3,z91,z6]),(0,[z0,z1,z11,z5,z97,z6]),(0,[z0,z1,z745,z4,z5,z6])],[(0,[z0,z1,z70,z60,z5,z6]),(0,[z0,z1,z3,z4,z6,z746])],[(0,[z0,z1,z3,z4,z747,z6]),(0,[z0,z1,z748,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z749]),(0,[z0,z1,z3,z4,z750,z6])],[(0,[z0,z1,z3,z751,z5,z6]),(0,[z0,z1,z306,z11,z3,z6]),(0,[z0,z1,z306,z12,z3,z6]),(0,[z0,z1,z138,z4,z254,z6]),(0,[z0,z106,z752,z4,z5,z6]),(0,[z0,z1,z753,z4,z5,z6]),(0,[z0,z1,z11,z5,z322,z6])],[(0,[z0,z1,z3,z4,z754,z6]),(0,[z0,z1,z3,z221,z273,z6]),(0,[z163,z0,z1,z41,z11,z6]),(0,[z163,z0,z3,z4,z488,z6]),(0,[z0,z3,z4,z5,z6,z755]),(1,[z0,z1,z11,z79,z6]),(0,[z0,z1,z12,z3,z756,z6])],[(0,[z0,z1,z3,z4,z757,z6]),(0,[z0,z101,z3,z4,z5,z541]),(0,[z0,z1,z164,z311,z5,z6]),(0,[z0,z1,z3,z4,z6,z758]),(0,[z0,z1,z3,z4,z759,z6]),(0,[z15,z0,z12,z3,z5,z141]),(0,[z0,z1,z11,z3,z382,z6]),(0,[z0,z1,z3,z221,z5,z215])],[(0,[z242,z432,z3,z4,z5,z6]),(0,[z0,z1,z3,z760,z5,z6]),(0,[z0,z1,z3,z120,z324,z6])],[(0,[z242,z90,z11,z3,z5,z6]),(0,[z0,z1,z3,z4,z210,z6]),(0,[z0,z1,z761,z3,z4,z6]),(0,[z0,z1,z3,z4,z762,z6])]],
   [[(0,[z0,z1,z3,z763,z5,z6]),(0,[z352,z1,z3,z4,z228,z6]),(0,[z0,z1,z3,z5,z6,z764]),(0,[z0,z1,z3,z5,z698,z123]),(0,[z0,z1,z487,z4,z97,z6])],[(0,[z0,z1,z765,z4,z5,z6]),(0,[z0,z1,z12,z3,z254,z6]),(0,[z0,z1,z3,z4,z766,z6])],[(0,[z767,z1,z3,z4,z5,z6]),(0,[z0,z1,z34,z3,z4,z274])],[(0,[z0,z1,z3,z768,z4,z6]),(0,[z0,z1,z3,z769,z5,z6]),(0,[z0,z1,z23,z165,z5,z6]),(0,[z14,z1,z11,z3,z88,z6]),(0,[z0,z153,z752,z4,z5,z6]),(0,[z0,z1,z3,z95,z6,z216]),(0,[z0,z1,z3,z470,z315,z6])],[(0,[z0,z1,z11,z4,z571,z6]),(0,[z0,z1,z11,z561,z5,z6]),(0,[z0,z1,z770,z3,z4,z6]),(0,[z0,z1,z301,z11,z5,z6]),(0,[z0,z1,z3,z4,z771,z6]),(0,[z0,z1,z3,z4,z6,z772]),(0,[z0,z1,z11,z5,z6,z513])],[(0,[z0,z1,z773,z3,z5,z6]),(0,[z18,z1,z3,z4,z235,z6]),(0,[z0,z1,z3,z774,z5,z6]),(0,[z0,z1,z3,z205,z427,z6]),(0,[z0,z1,z3,z775,z5,z6]),(0,[z0,z1,z11,z5,z344,z6]),(0,[z0,z1,z3,z4,z776,z6]),(0,[z0,z3,z777,z165,z5,z6]),(0,[z0,z1,z3,z778,z5,z6])],[(0,[z0,z1,z3,z779,z5,z6]),(0,[z246,z36,z3,z4,z5,z6]),(0,[z109,z1,z70,z38,z5,z6]),(0,[z0,z1,z19,z3,z6,z687])],[(0,[z0,z3,z4,z5,z6,z780]),(0,[z0,z1,z3,z781,z5,z6]),(0,[z782,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z783]),(0,[z0,z1,z784,z197,z5,z6])]],
   [[(0,[z0,z1,z23,z273,z4,z6]),(0,[z0,z1,z164,z5,z6,z123])],[(0,[z128,z1,z3,z4,z427,z131]),(1,[z1,z3,z4,z5,z785]),(0,[z0,z1,z3,z786,z5,z6]),(0,[z787,z1,z3,z4,z5,z6]),(0,[z0,z1,z28,z4,z63,z6]),(0,[z0,z1,z12,z3,z382,z6])],[(0,[z0,z1,z3,z4,z788,z6]),(0,[z0,z153,z74,z11,z5,z6]),(0,[z0,z1,z4,z5,z6,z789])],[(0,[z790,z36,z3,z4,z5,z6]),(0,[z242,z90,z12,z3,z5,z6]),(0,[z0,z1,z3,z4,z791,z6]),(0,[z0,z1,z792,z3,z384,z6]),(0,[z14,z0,z1,z341,z4,z6])],[(0,[z0,z1,z3,z4,z256,z6]),(0,[z0,z1,z3,z4,z5,z793]),(0,[z0,z1,z11,z184,z5,z6]),(0,[z0,z1,z794,z4,z5,z6]),(0,[z0,z1,z3,z252,z5,z6]),(0,[z0,z1,z3,z4,z795,z6]),(0,[z0,z1,z3,z4,z63,z6]),(0,[z462,z1,z197,z4,z5,z6]),(0,[z0,z1,z11,z3,z771,z6]),(0,[z0,z1,z3,z221,z95,z6]),(0,[z0,z1,z796,z3,z5,z6])],[(0,[z0,z1,z3,z4,z797,z6]),(0,[z0,z1,z3,z798,z5,z6]),(0,[z0,z1,z799,z3,z5,z6]),(0,[z0,z1,z402,z3,z5,z698]),(0,[z0,z1,z5,z6,z800,z244])],[(0,[z0,z1,z3,z4,z801,z6]),(0,[z0,z1,z3,z802,z5,z6]),(0,[z0,z1,z3,z803,z4,z6]),(0,[z0,z1,z12,z3,z747,z6]),(0,[z0,z1,z3,z6,z86,z804])],[(0,[z0,z1,z3,z4,z805,z6]),(0,[z0,z1,z806,z3,z5,z6]),(0,[z0,z1,z807,z4,z5,z6]),(0,[z0,z1,z3,z4,z808,z6]),(1,[z0,z1,z11,z254,z6]),(0,[z0,z1,z11,z197,z5,z6]),(0,[z0,z1,z686,z3,z47,z6]),(0,[z0,z1,z19,z3,z374,z6]),(0,[z0,z1,z3,z5,z6,z13]),(0,[z0,z1,z809,z4,z5,z6]),(0,[z0,z1,z810,z3,z5,z6])]],
   [[(0,[z0,z1,z154,z4,z5,z6]),(0,[z0,z1,z3,z811,z4,z6]),(0,[z0,z1,z11,z275,z5,z6]),(0,[z0,z1,z3,z77,z151,z6])],[(0,[z0,z1,z812,z3,z5,z6]),(0,[z0,z1,z813,z4,z5,z6]),(0,[z30,z1,z397,z3,z5,z6]),(0,[z0,z1,z3,z814,z5,z6]),(0,[z0,z101,z3,z4,z5,z755]),(0,[z0,z1,z4,z5,z6,z815])],[(0,[z0,z1,z3,z816,z4,z6]),(0,[z0,z1,z817,z3,z5,z6]),(0,[z0,z1,z4,z6,z305,z236])],[(0,[z0,z1,z3,z816,z510,z6]),(0,[z0,z1,z818,z4,z5,z6]),(0,[z0,z1,z819,z4,z5,z6]),(0,[z0,z1,z12,z3,z210,z6]),(0,[z0,z820,z3,z4,z5,z6]),(0,[z0,z1,z3,z707,z5,z6]),(0,[z0,z1,z3,z4,z821,z6]),(0,[z0,z1,z28,z4,z5,z6]),(0,[z822,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z316,z6]),(0,[z0,z1,z12,z3,z762,z6]),(0,[z0,z1,z3,z95,z134,z6]),(0,[z0,z1,z823,z3,z4,z6]),(0,[z0,z1,z3,z4,z6,z733]),(0,[z0,z1,z824,z341,z5,z6])],[(0,[z0,z1,z11,z3,z256,z6]),(0,[z0,z1,z11,z384,z5,z6]),(0,[z0,z1,z41,z152,z4,z6]),(0,[z0,z1,z34,z3,z4,z331]),(0,[z0,z1,z11,z62,z97,z6]),(0,[z0,z1,z11,z3,z63,z6]),(0,[z349,z0,z1,z107,z5,z6])],[(0,[z0,z1,z3,z4,z108,z6]),(0,[z0,z1,z3,z4,z825,z6]),(0,[z0,z1,z3,z4,z826,z6]),(0,[z0,z1,z3,z827,z5,z6]),(0,[z0,z1,z3,z4,z828,z6]),(0,[z0,z1,z11,z162,z5,z6]),(0,[z0,z153,z1,z351,z5,z6]),(0,[z0,z119,z1,z41,z11,z6]),(0,[z462,z1,z3,z4,z228,z6]),(1,[z0,z1,z713,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z287,z3,z5,z6]),(0,[z0,z603,z1,z11,z5,z6]),(0,[z0,z1,z11,z829,z5,z6]),(0,[z0,z1,z3,z830,z5,z6]),(0,[z0,z1,z752,z4,z5,z6]),(0,[z0,z1,z831,z197,z5,z6]),(0,[z0,z1,z3,z832,z5,z6]),(0,[z0,z1,z3,z4,z5,z815])],[(0,[z0,z1,z833,z4,z5,z6]),(0,[z0,z7,z11,z3,z5,z6]),(0,[z0,z7,z162,z4,z5,z6]),(0,[z0,z1,z834,z3,z4,z6]),(0,[z0,z1,z41,z4,z6,z642]),(0,[z0,z1,z19,z107,z335,z6])]],
   [[(0,[z0,z1,z3,z4,z835,z6]),(0,[z0,z836,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z48,z388]),(0,[z0,z1,z3,z837,z5,z6]),(0,[z0,z1,z3,z78,z5,z6]),(0,[z0,z1,z3,z838,z5,z6]),(0,[z0,z1,z4,z5,z815,z39]),(0,[z0,z1,z4,z5,z6,z839])],[(0,[z0,z1,z840,z3,z5,z6]),(0,[z0,z1,z841,z3,z4,z6]),(0,[z0,z1,z842,z3,z5,z6]),(0,[z0,z1,z843,z3,z4,z6]),(0,[z0,z1,z3,z470,z6,z425])],[(0,[z0,z1,z844,z3,z4,z6])],[(0,[z0,z1,z3,z845,z5,z6]),(0,[z0,z1,z3,z4,z846,z6]),(0,[z0,z1,z11,z235,z97,z6])],[(0,[z0,z1,z3,z847,z5,z6]),(0,[z0,z1,z3,z4,z848,z6]),(0,[z0,z1,z829,z3,z5,z6]),(0,[z0,z1,z3,z849,z5,z6]),(0,[z0,z1,z11,z3,z273,z6]),(0,[z0,z1,z850,z162,z5,z6]),(0,[z163,z0,z1,z3,z151,z6]),(0,[z0,z502,z1,z11,z5,z6]),(0,[z0,z1,z4,z315,z6,z39]),(0,[z0,z1,z3,z315,z6,z317])],[(0,[z0,z1,z11,z3,z108,z6]),(0,[z222,z0,z1,z11,z5,z6]),(0,[z0,z1,z851,z4,z5,z6]),(0,[z0,z1,z852,z4,z5,z6]),(0,[z0,z1,z3,z4,z730,z6]),(0,[z0,z1,z853,z3,z5,z6]),(0,[z0,z1,z854,z3,z4,z6]),(0,[z0,z1,z855,z3,z5,z6]),(0,[z0,z1,z3,z4,z856,z6]),(0,[z0,z1,z3,z4,z857,z6]),(0,[z0,z1,z3,z567,z228,z6]),(0,[z0,z1,z341,z4,z6,z42])],[(0,[z0,z1,z11,z3,z5,z6]),(0,[z0,z1,z4,z5,z6,z858]),(0,[z0,z1,z318,z4,z5,z6]),(0,[z0,z1,z85,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z86]),(0,[z0,z1,z335,z3,z387,z6])],[(0,[z0,z1,z3,z859,z5,z6]),(0,[z0,z1,z114,z3,z4,z42]),(0,[z0,z1,z3,z6,z317,z425])]],
   [[(0,[z0,z1,z12,z3,z256,z6]),(0,[z0,z1,z3,z860,z5,z6]),(0,[z242,z790,z3,z4,z5,z6]),(0,[z0,z1,z3,z861,z5,z6]),(0,[z862,z1,z3,z4,z5,z6]),(0,[z0,z153,z51,z4,z249,z6]),(0,[z0,z1,z3,z863,z4,z6]),(0,[z0,z1,z864,z4,z5,z6]),(0,[z0,z1,z12,z3,z63,z6]),(0,[z0,z1,z85,z428,z5,z6])],[(0,[z0,z1,z865,z3,z4,z5]),(0,[z0,z1,z866,z3,z5,z6]),(0,[z1,z3,z707,z4,z5,z6]),(0,[z0,z1,z12,z162,z5,z6]),(0,[z15,z0,z3,z4,z5,z755]),(0,[z0,z1,z867,z5,z97,z6]),(0,[z0,z430,z455,z3,z5,z6])],[(0,[z0,z1,z3,z868,z5,z6]),(0,[z0,z1,z869,z3,z4,z6]),(0,[z0,z1,z870,z162,z5,z6]),(0,[z0,z153,z51,z4,z254,z6]),(0,[z0,z74,z1,z871,z5,z6]),(0,[z0,z1,z3,z4,z872,z6]),(0,[z0,z1,z11,z28,z5,z6]),(0,[z0,z1,z3,z873,z5,z6])],[(0,[z0,z1,z3,z4,z874,z6]),(0,[z0,z1,z875,z3,z5,z6]),(0,[z0,z7,z12,z3,z5,z6]),(0,[z0,z1,z876,z3,z5,z6]),(0,[z0,z1,z60,z473,z4,z6])],[(0,[z0,z1,z3,z110,z5,z6]),(0,[z0,z1,z11,z635,z5,z6]),(0,[z0,z1,z12,z594,z5,z6]),(0,[z352,z101,z3,z4,z5,z6]),(0,[z0,z1,z3,z217,z5,z6]),(0,[z0,z1,z138,z832,z5,z6]),(0,[z0,z1,z34,z3,z4,z42])],[(0,[z0,z1,z3,z5,z6,z877]),(0,[z574,z1,z3,z311,z5,z6]),(0,[z0,z1,z878,z4,z5,z6]),(0,[z0,z1,z879,z4,z5,z6]),(0,[z56,z1,z3,z4,z5,z785]),(0,[z0,z1,z11,z3,z79,z6]),(0,[z0,z1,z41,z713,z4,z6]),(0,[z0,z1,z880,z4,z5,z6])],[(0,[z194,z1,z709,z4,z5,z6]),(0,[z0,z1,z881,z3,z5,z6]),(0,[z0,z1,z351,z5,z6,z39]),(0,[z27,z0,z1,z11,z5,z6]),(0,[z0,z203,z3,z165,z5,z6]),(1,[z0,z3,z4,z882,z6]),(0,[z0,z1,z11,z377,z5,z6]),(0,[z0,z1,z41,z77,z4,z6])],[(0,[z0,z1,z883,z3,z5,z6]),(0,[z363,z1,z3,z311,z5,z6]),(0,[z884,z1,z3,z4,z5,z6]),(0,[z0,z1,z197,z398,z5,z6]),(0,[z0,z1,z11,z424,z5,z6]),(0,[z0,z1,z3,z4,z35,z48])]],
   [[(0,[z0,z1,z11,z5,z6,z426]),(0,[z194,z1,z11,z64,z5,z6]),(0,[z0,z1,z11,z683,z5,z6]),(0,[z0,z1,z885,z3,z5,z6]),(0,[z862,z1,z11,z3,z5,z6]),(0,[z534,z0,z1,z11,z5,z6]),(0,[z0,z1,z886,z4,z5,z6])],[(0,[z0,z1,z12,z3,z108,z6]),(0,[z0,z1,z3,z4,z887,z6]),(0,[z0,z1,z3,z4,z888,z6]),(0,[z194,z0,z1,z829,z5,z6]),(0,[z0,z1,z11,z4,z254,z6]),(0,[z0,z153,z1,z11,z254,z6]),(0,[z0,z119,z3,z338,z4,z6]),(0,[z0,z1,z3,z4,z889,z6])],[(0,[z0,z1,z12,z3,z5,z6]),(0,[z0,z1,z11,z294,z5,z6]),(0,[z0,z1,z11,z60,z5,z6]),(0,[z0,z1,z3,z5,z6,z890])],[(0,[z0,z1,z12,z396,z5,z6]),(0,[z0,z7,z129,z4,z5,z6]),(0,[z0,z75,z3,z165,z5,z6]),(0,[z0,z638,z1,z11,z5,z6]),(0,[z0,z1,z138,z4,z79,z6])],[(0,[z1,z790,z3,z4,z5,z6]),(0,[z0,z1,z11,z5,z571,z6]),(0,[z0,z1,z162,z110,z5,z6]),(0,[z0,z1,z11,z3,z95,z6]),(0,[z0,z1,z138,z5,z6,z86])],[(0,[z194,z1,z64,z384,z5,z6]),(0,[z14,z1,z3,z4,z706,z6]),(0,[z891,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z892,z6]),(0,[z0,z1,z893,z4,z5,z6]),(0,[z0,z1,z727,z3,z5,z6]),(0,[z0,z1,z3,z120,z421,z6])],[(0,[z0,z1,z3,z4,z894,z6]),(0,[z0,z1,z3,z4,z6,z895]),(0,[z0,z1,z3,z4,z424,z48])],[(0,[z0,z1,z3,z4,z896,z6]),(0,[z109,z1,z287,z38,z5,z6]),(0,[z0,z1,z3,z4,z897,z6]),(0,[z128,z1,z3,z4,z130,z131]),(0,[z0,z1,z3,z5,z6,z898]),(0,[z0,z502,z3,z4,z62,z6]),(0,[z0,z1,z11,z97,z48,z6]),(0,[z0,z1,z3,z4,z35,z167]),(0,[z0,z1,z20,z217,z97,z6])]],
   [[(0,[z21,z36,z3,z460,z5,z6]),(0,[z0,z1,z70,z3,z5,z6]),(0,[z0,z1,z19,z3,z137,z6]),(0,[z0,z1,z3,z398,z228,z6])],[(0,[z109,z194,z1,z11,z5,z6]),(0,[z18,z0,z1,z41,z11,z6]),(0,[z0,z140,z3,z4,z62,z6]),(0,[z0,z1,z157,z3,z5,z6]),(0,[z0,z1,z3,z4,z899,z6]),(0,[z0,z1,z77,z4,z303,z6]),(0,[z0,z1,z3,z740,z5,z6]),(0,[z0,z1,z341,z4,z35,z6])],[(0,[z0,z1,z3,z900,z5,z6]),(0,[z0,z1,z3,z4,z901,z6]),(0,[z0,z1,z739,z11,z3,z6]),(0,[z0,z1,z11,z3,z5,z902]),(0,[z0,z1,z41,z11,z374,z6])],[(0,[z0,z1,z11,z93,z5,z6]),(0,[z0,z1,z3,z4,z903,z6]),(0,[z531,z0,z1,z11,z5,z6]),(0,[z96,z0,z1,z11,z5,z6]),(0,[z0,z1,z19,z3,z95,z6])],[(0,[z0,z1,z3,z904,z4,z6]),(0,[z0,z1,z3,z205,z155,z6]),(0,[z0,z1,z3,z4,z5,z785]),(0,[z0,z1,z164,z12,z5,z6]),(0,[z15,z0,z11,z3,z5,z141])],[(0,[z0,z1,z3,z905,z5,z6]),(0,[z520,z1,z3,z4,z235,z6]),(0,[z0,z1,z906,z3,z5,z6]),(0,[z0,z119,z1,z3,z151,z6]),(0,[z0,z1,z907,z3,z4,z6]),(0,[z0,z1,z11,z5,z166,z6]),(0,[z0,z1,z3,z4,z5,z908]),(0,[z0,z1,z3,z5,z6,z909])],[(0,[z0,z1,z910,z4,z5,z6]),(0,[z109,z1,z709,z4,z5,z6]),(0,[z0,z1,z542,z4,z5,z39]),(0,[z0,z1,z911,z3,z5,z6]),(0,[z0,z153,z11,z51,z5,z6]),(0,[z0,z1,z281,z4,z5,z6]),(0,[z0,z1,z3,z4,z912,z6]),(0,[z0,z1,z3,z4,z5,z913]),(0,[z0,z1,z298,z4,z97,z6])],[(0,[z115,z90,z3,z4,z5,z6]),(0,[z109,z1,z11,z38,z5,z6]),(0,[z535,z1,z38,z4,z5,z6]),(0,[z1,z64,z709,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z914]),(0,[z0,z1,z4,z35,z48,z244])]],
   [[(0,[z0,z1,z3,z4,z915,z6]),(0,[z128,z1,z3,z4,z155,z131]),(0,[z0,z443,z1,z11,z5,z6]),(0,[z0,z1,z12,z3,z95,z6])],[(0,[z0,z1,z916,z4,z5,z6]),(0,[z0,z917,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z918,z6]),(0,[z0,z1,z11,z3,z899,z6]),(0,[z0,z1,z919,z3,z5,z6])],[(0,[z575,z1,z3,z4,z5,z131]),(0,[z0,z1,z3,z4,z920,z6]),(0,[z0,z1,z11,z5,z477,z6]),(0,[z0,z74,z1,z11,z5,z6]),(0,[z0,z1,z921,z3,z4,z6]),(0,[z0,z75,z66,z3,z5,z6]),(0,[z0,z1,z41,z4,z374,z6])],[(0,[z0,z1,z11,z5,z485,z6]),(0,[z0,z1,z3,z95,z4,z6]),(0,[z0,z1,z85,z138,z5,z6]),(0,[z0,z1,z4,z5,z515,z39])],[(0,[z1,z3,z4,z5,z785,z131]),(0,[z0,z1,z164,z4,z5,z6]),(0,[z0,z1,z391,z3,z5,z6]),(0,[z0,z1,z3,z4,z922,z6]),(0,[z0,z1,z4,z5,z6,z305]),(0,[z0,z1,z20,z4,z6,z551]),(0,[z0,z1,z923,z3,z5,z6])],[(0,[z0,z1,z3,z924,z5,z6]),(0,[z0,z1,z925,z3,z4,z6]),(0,[z0,z1,z11,z3,z5,z908]),(0,[z531,z1,z404,z3,z5,z6]),(0,[z0,z1,z3,z4,z926,z6]),(0,[z0,z1,z3,z4,z35,z667])],[(0,[z0,z1,z927,z3,z4,z6]),(0,[z0,z1,z928,z4,z5,z6]),(0,[z0,z119,z283,z3,z4,z6]),(1,[z0,z3,z4,z5,z755]),(0,[z0,z1,z11,z60,z5,z225])],[(0,[z0,z1,z3,z5,z6,z929]),(0,[z0,z1,z3,z930,z5,z6]),(0,[z0,z119,z323,z3,z4,z6]),(0,[z0,z1,z11,z25,z5,z6])]],
   [[(0,[z0,z1,z11,z154,z5,z6]),(0,[z14,z1,z557,z3,z4,z6]),(0,[z0,z1,z3,z931,z5,z6]),(0,[z0,z1,z20,z223,z4,z6]),(0,[z0,z1,z4,z5,z6,z932]),(0,[z0,z1,z3,z4,z933,z6]),(0,[z0,z1,z41,z11,z77,z6]),(1,[z0,z1,z832,z5,z6]),(0,[z0,z1,z402,z3,z95,z6]),(0,[z0,z1,z3,z151,z35,z48])],[(0,[z0,z1,z3,z4,z934,z6]),(0,[z56,z258,z3,z4,z5,z6]),(0,[z0,z1,z308,z281,z4,z6]),(0,[z0,z1,z198,z3,z5,z215]),(0,[z0,z1,z20,z4,z569,z6]),(0,[z0,z1,z19,z335,z3,z6])],[(0,[z0,z1,z3,z4,z5,z935]),(0,[z0,z1,z936,z3,z5,z6]),(0,[z0,z1,z937,z3,z4,z6]),(0,[z0,z153,z12,z51,z5,z6]),(0,[z0,z1,z3,z938,z4,z6]),(0,[z0,z1,z197,z4,z63,z6]),(0,[z0,z1,z43,z12,z5,z6]),(0,[z0,z1,z939,z3,z5,z6])],[(0,[z0,z1,z940,z3,z4,z6]),(0,[z0,z1,z3,z941,z5,z6]),(0,[z109,z1,z12,z38,z5,z6]),(0,[z0,z1,z3,z942,z5,z6])],[(0,[z0,z1,z11,z473,z3,z6]),(0,[z0,z1,z943,z3,z325,z6]),(0,[z0,z1,z944,z4,z5,z6]),(0,[z0,z1,z11,z689,z5,z6]),(0,[z163,z0,z271,z3,z4,z6]),(0,[z0,z1,z370,z3,z134,z6])],[(0,[z0,z1,z321,z3,z4,z6]),(0,[z56,z1,z3,z4,z5,z57]),(0,[z0,z1,z945,z4,z5,z6]),(0,[z0,z3,z4,z5,z313,z755]),(0,[z0,z1,z3,z4,z134,z6]),(0,[z0,z1,z3,z4,z946,z6]),(0,[z0,z1,z59,z157,z5,z39])],[(0,[z0,z1,z3,z4,z947,z6]),(0,[z0,z1,z948,z3,z5,z6]),(0,[z0,z1,z3,z4,z6,z949]),(0,[z0,z7,z3,z4,z427,z6]),(0,[z0,z1,z3,z950,z4,z6]),(0,[z0,z297,z1,z11,z5,z6]),(0,[z352,z1,z3,z567,z5,z6]),(0,[z0,z430,z1,z11,z5,z6]),(0,[z0,z1,z3,z5,z6,z951]),(0,[z0,z1,z3,z952,z5,z6]),(0,[z0,z1,z939,z3,z218,z6]),(0,[z0,z1,z4,z124,z6,z305])],[(0,[z0,z1,z953,z4,z5,z6]),(0,[z0,z1,z11,z656,z5,z6]),(0,[z0,z1,z3,z954,z5,z6]),(0,[z128,z1,z3,z205,z5,z131]),(0,[z163,z0,z1,z341,z4,z6])]],
   [[(0,[z0,z1,z955,z3,z4,z6]),(0,[z0,z1,z41,z11,z5,z6]),(0,[z0,z1,z328,z60,z5,z6])],[(0,[z0,z1,z3,z4,z956,z6]),(0,[z0,z1,z11,z23,z5,z6]),(0,[z0,z1,z3,z957,z5,z6]),(0,[z0,z1,z11,z528,z5,z6]),(0,[z0,z1,z341,z4,z97,z6]),(0,[z0,z1,z318,z221,z5,z6]),(0,[z0,z1,z3,z4,z5,z733])],[(0,[z0,z1,z11,z3,z210,z6]),(0,[z109,z1,z38,z4,z210,z6]),(0,[z258,z3,z4,z5,z6,z131]),(0,[z1,z3,z4,z5,z6,z958]),(0,[z0,z1,z959,z4,z5,z6]),(0,[z0,z1,z11,z12,z5,z6])],[(0,[z0,z1,z960,z3,z4,z5]),(0,[z18,z1,z3,z378,z4,z6]),(0,[z14,z1,z3,z4,z730,z6]),(0,[z457,z1,z3,z4,z88,z6])],[(0,[z0,z1,z3,z4,z961,z6]),(0,[z0,z1,z4,z5,z962,z6]),(0,[z0,z1,z3,z963,z5,z6]),(0,[z0,z1,z964,z4,z5,z6]),(0,[z0,z1,z12,z154,z5,z6]),(0,[z0,z1,z965,z4,z5,z6]),(0,[z18,z1,z172,z3,z4,z6]),(0,[z0,z1,z966,z4,z5,z6]),(0,[z0,z1,z197,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z967]),(0,[z0,z1,z968,z4,z5,z6])],[(0,[z0,z969,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z970,z6]),(0,[z0,z1,z548,z4,z97,z6]),(0,[z0,z1,z971,z4,z5,z6]),(0,[z0,z1,z972,z3,z5,z6]),(0,[z0,z1,z11,z3,z134,z6]),(0,[z0,z1,z85,z3,z134,z6])],[(0,[z0,z973,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z974,z6])],[(0,[z21,z36,z3,z510,z5,z6]),(0,[z0,z1,z340,z3,z5,z123]),(0,[z0,z975,z3,z4,z5,z6]),(0,[z49,z1,z3,z4,z235,z6]),(0,[z0,z75,z308,z3,z165,z6]),(0,[z0,z1,z976,z3,z4,z6])]],
   [[(0,[z0,z258,z3,z4,z5,z6]),(0,[z0,z522,z1,z11,z5,z6]),(0,[z18,z1,z11,z3,z235,z6]),(0,[z0,z1,z12,z473,z3,z6]),(0,[z0,z1,z549,z4,z5,z39]),(0,[z977,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z978,z5,z6])],[(0,[z0,z1,z11,z537,z5,z6]),(0,[z18,z0,z1,z3,z151,z6]),(0,[z0,z1,z11,z5,z254,z6]),(0,[z0,z1,z328,z5,z6,z39])],[(0,[z0,z1,z979,z4,z5,z6]),(0,[z0,z153,z1,z11,z5,z6]),(0,[z0,z1,z3,z4,z980,z6]),(0,[z0,z1,z50,z391,z3,z6]),(0,[z0,z1,z981,z3,z5,z6]),(0,[z0,z1,z28,z4,z228,z6]),(0,[z0,z1,z11,z832,z5,z6])],[(0,[z0,z1,z3,z291,z5,z6]),(0,[z0,z1,z3,z982,z5,z6]),(0,[z0,z1,z3,z4,z882,z6]),(0,[z0,z1,z138,z4,z134,z6])],[(0,[z0,z1,z983,z3,z4,z6]),(0,[z0,z1,z3,z984,z5,z6]),(0,[z0,z153,z391,z51,z5,z6]),(0,[z0,z1,z4,z5,z6,z985]),(0,[z0,z673,z1,z11,z5,z6]),(0,[z986,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z987,z5,z6]),(0,[z0,z75,z1,z164,z5,z6]),(0,[z0,z1,z3,z4,z228,z6]),(0,[z0,z1,z3,z4,z988,z6])],[(0,[z0,z1,z989,z4,z5,z6]),(0,[z0,z1,z3,z990,z4,z6]),(0,[z0,z1,z11,z5,z6,z551]),(0,[z0,z1,z3,z221,z5,z991])],[(0,[z0,z1,z3,z4,z992,z6]),(0,[z30,z1,z3,z707,z5,z6]),(0,[z0,z1,z3,z993,z5,z6]),(0,[z0,z1,z197,z567,z5,z6]),(0,[z0,z1,z3,z994,z5,z6])]],
   [[(0,[z163,z0,z3,z4,z677,z6]),(0,[z0,z1,z995,z4,z5,z6]),(0,[z0,z258,z11,z3,z5,z6]),(0,[z600,z0,z1,z11,z5,z6]),(0,[z0,z1,z996,z3,z5,z6]),(0,[z0,z1,z11,z12,z95,z6]),(0,[z0,z1,z997,z3,z4,z6]),(0,[z0,z1,z3,z998,z4,z6])],[(0,[z0,z999,z3,z4,z5,z6]),(0,[z0,z1,z3,z1000,z5,z6]),(0,[z56,z1,z12,z3,z5,z57]),(0,[z163,z0,z3,z4,z46,z6]),(0,[z352,z1,z3,z398,z5,z6]),(0,[z0,z1,z784,z3,z5,z6]),(0,[z0,z1,z12,z3,z134,z6]),(0,[z0,z1,z11,z4,z79,z6]),(0,[z0,z1,z328,z5,z97,z6]),(0,[z0,z1,z335,z939,z3,z6])],[(0,[z0,z1,z3,z4,z1001,z6]),(0,[z257,z1,z154,z311,z5,z6]),(0,[z1002,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z1003,z4,z6]),(0,[z0,z1,z11,z5,z6,z86]),(0,[z0,z1,z85,z20,z97,z6])],[(0,[z0,z1,z3,z4,z1004,z6]),(0,[z0,z1,z11,z5,z560,z6]),(0,[z14,z1,z598,z3,z4,z6]),(0,[z0,z1,z3,z110,z427,z6]),(0,[z0,z1,z1005,z3,z5,z6])],[(0,[z18,z1,z12,z3,z235,z6]),(0,[z0,z1,z3,z5,z6,z1006]),(0,[z0,z1,z3,z4,z1007,z6]),(0,[z0,z1,z3,z4,z35,z290]),(0,[z0,z1,z996,z28,z5,z6]),(0,[z0,z1,z3,z5,z6,z1008])],[(0,[z0,z1,z1009,z4,z5,z6]),(0,[z0,z1,z1010,z3,z4,z6]),(0,[z0,z1,z1011,z3,z4,z6]),(0,[z0,z1,z3,z221,z124,z68])],[(0,[z395,z36,z3,z4,z5,z6]),(0,[z109,z1,z321,z38,z4,z6]),(0,[z0,z1,z3,z5,z6,z1012]),(0,[z0,z1,z3,z1013,z5,z6]),(0,[z0,z1,z3,z120,z248,z6]),(0,[z0,z1,z1014,z3,z5,z6]),(0,[z0,z258,z3,z110,z5,z6]),(0,[z0,z1,z3,z4,z1015,z6]),(0,[z0,z1,z1016,z4,z5,z6]),(0,[z0,z1,z11,z569,z5,z6]),(0,[z0,z1,z12,z832,z5,z6])],[(0,[z0,z1,z3,z1017,z5,z6]),(0,[z0,z1,z1018,z4,z5,z6]),(0,[z0,z1,z3,z708,z4,z6])]],
   [[(0,[z0,z3,z4,z5,z6,z1019]),(0,[z257,z1,z3,z311,z5,z6]),(0,[z0,z74,z106,z4,z5,z6]),(0,[z0,z1,z351,z60,z5,z6]),(0,[z0,z1,z1020,z4,z5,z6]),(0,[z0,z1,z1021,z3,z5,z6]),(0,[z0,z119,z1,z341,z4,z6]),(0,[z0,z1,z3,z5,z6,z991])],[(0,[z109,z1,z38,z4,z5,z6]),(0,[z0,z1,z162,z4,z5,z6]),(0,[z194,z1,z64,z252,z5,z6]),(0,[z518,z0,z1,z11,z5,z6]),(0,[z0,z1,z3,z4,z1022,z6]),(0,[z0,z1,z23,z5,z6,z123]),(0,[z0,z1023,z3,z4,z5,z6]),(0,[z545,z1,z3,z81,z5,z6]),(0,[z0,z999,z11,z3,z5,z6]),(0,[z0,z1,z34,z11,z3,z42]),(0,[z0,z1,z34,z12,z3,z42])],[(0,[z109,z0,z1,z11,z571,z6]),(0,[z109,z1,z11,z587,z5,z6]),(0,[z0,z1,z3,z1024,z5,z6]),(0,[z0,z1,z11,z5,z6,z700]),(0,[z0,z1,z391,z473,z3,z6]),(0,[z0,z1,z3,z1025,z4,z6]),(0,[z0,z1,z1026,z4,z5,z6]),(0,[z15,z0,z197,z4,z5,z141]),(0,[z0,z1,z1027,z3,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1028]),(0,[z0,z1,z3,z1029,z4,z5]),(0,[z30,z0,z1,z23,z5,z6]),(0,[z0,z1,z11,z428,z5,z6]),(0,[z0,z1,z417,z77,z4,z6])],[(0,[z0,z258,z12,z3,z5,z6]),(0,[z0,z1,z3,z4,z1030,z6]),(0,[z0,z1,z1031,z3,z5,z6]),(0,[z0,z3,z4,z882,z5,z6]),(1,[z0,z1,z3,z5,z991]),(0,[z0,z1,z4,z5,z6,z1032])],[(0,[z0,z564,z1,z11,z5,z6]),(0,[z0,z1033,z3,z4,z5,z6]),(0,[z0,z430,z3,z165,z5,z6])],[(0,[z0,z1,z842,z129,z5,z6]),(0,[z0,z1,z226,z11,z5,z6]),(0,[z0,z1,z12,z3,z980,z6])],[(0,[z0,z1,z287,z321,z3,z6]),(0,[z0,z1,z164,z221,z5,z6]),(1,[z0,z1,z11,z134,z6]),(0,[z0,z1,z20,z4,z79,z6])]],
   [[(0,[z0,z1,z1034,z3,z4,z6]),(0,[z1,z3,z4,z730,z235,z6]),(0,[z0,z1,z3,z1035,z5,z6]),(0,[z0,z1,z850,z3,z5,z6]),(0,[z0,z1,z831,z3,z5,z6])],[(0,[z0,z1,z3,z803,z384,z6]),(0,[z0,z3,z752,z4,z5,z6]),(0,[z0,z1,z3,z1036,z5,z6]),(0,[z0,z1,z3,z1037,z5,z6]),(0,[z0,z1,z12,z3,z228,z6]),(0,[z0,z1,z1038,z3,z5,z6]),(0,[z0,z1,z3,z867,z5,z6]),(0,[z0,z1,z3,z1039,z5,z6]),(0,[z0,z1,z122,z3,z5,z225])],[(0,[z0,z1,z11,z511,z5,z6]),(0,[z0,z1,z50,z351,z3,z6]),(0,[z0,z1,z1040,z4,z5,z6]),(0,[z0,z517,z3,z4,z46,z6]),(0,[z0,z1,z686,z11,z97,z6]),(0,[z0,z1,z3,z1041,z5,z6]),(0,[z0,z1,z3,z151,z97,z6])],[(0,[z0,z1,z1042,z4,z5,z6]),(0,[z194,z1,z64,z4,z5,z6]),(0,[z0,z1,z245,z287,z3,z6]),(0,[z0,z1043,z3,z4,z5,z6]),(0,[z0,z1,z4,z5,z6,z1044]),(0,[z0,z1,z11,z129,z5,z6]),(0,[z0,z1,z3,z1045,z5,z6]),(0,[z0,z1,z3,z4,z1046,z6]),(0,[z0,z1,z3,z5,z6,z1047]),(0,[z15,z0,z3,z4,z228,z141])],[(0,[z0,z1,z4,z5,z6,z1048]),(0,[z0,z1,z3,z1049,z4,z6]),(0,[z0,z1,z3,z4,z1050,z6]),(0,[z0,z153,z351,z51,z5,z6]),(0,[z0,z1,z3,z221,z190,z6])],[(0,[z582,z36,z3,z4,z5,z6]),(0,[z0,z472,z3,z165,z5,z6]),(0,[z1051,z1,z3,z4,z5,z6]),(0,[z163,z0,z12,z3,z46,z6]),(0,[z0,z1,z713,z4,z5,z6]),(0,[z0,z1,z3,z1052,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1053]),(0,[z0,z1,z870,z3,z5,z6]),(0,[z0,z75,z3,z777,z5,z6]),(0,[z0,z101,z3,z4,z5,z313]),(0,[z0,z1,z200,z11,z97,z6]),(0,[z0,z1,z5,z6,z1008,z39]),(0,[z0,z1,z3,z120,z78,z6]),(0,[z0,z1,z3,z4,z5,z991])],[(0,[z352,z3,z4,z5,z6,z141]),(0,[z0,z1,z12,z428,z5,z6])]],
   [[(0,[z1054,z1,z3,z4,z5,z6]),(0,[z0,z1,z1055,z3,z5,z6]),(0,[z0,z1,z12,z3,z1007,z6])],[(0,[z0,z1,z3,z4,z1056,z6]),(0,[z0,z1,z3,z4,z1057,z6])],[(0,[z0,z1,z11,z31,z5,z6]),(0,[z0,z1,z1058,z3,z5,z6]),(0,[z0,z1,z3,z4,z1059,z6]),(0,[z0,z1,z1060,z3,z4,z6]),(0,[z0,z1,z11,z3,z35,z48]),(0,[z0,z1,z686,z4,z97,z6]),(0,[z0,z1,z3,z4,z1061,z6]),(0,[z0,z1,z3,z316,z4,z6]),(0,[z0,z1,z4,z5,z6,z244]),(0,[z0,z1,z3,z5,z991,z123])],[(0,[z0,z1,z1062,z3,z5,z6]),(0,[z0,z1,z3,z4,z130,z6]),(0,[z0,z1,z11,z5,z6,z612])],[(0,[z0,z1,z3,z4,z1063,z6]),(0,[z0,z1,z3,z1064,z5,z6]),(0,[z352,z1,z3,z4,z63,z6]),(0,[z0,z1,z11,z3,z1050,z6]),(0,[z0,z1,z3,z4,z1065,z6])],[(0,[z0,z1,z1066,z4,z5,z6]),(0,[z0,z1,z129,z4,z5,z6]),(0,[z0,z7,z3,z4,z155,z6]),(0,[z0,z1,z3,z1067,z5,z6]),(0,[z0,z1,z11,z871,z5,z6]),(0,[z0,z1,z12,z3,z1022,z6])],[(0,[z0,z1,z1068,z4,z5,z6]),(0,[z0,z1,z3,z4,z1069,z6]),(0,[z0,z1,z11,z3,z5,z1053]),(0,[z0,z1,z107,z5,z6,z123])],[(0,[z0,z1,z1070,z4,z5,z6]),(0,[z127,z0,z1,z11,z5,z6]),(0,[z109,z0,z1,z70,z5,z6]),(0,[z632,z0,z1,z11,z5,z6]),(0,[z0,z1,z3,z4,z1071,z6]),(0,[z0,z1,z3,z221,z5,z681]),(0,[z0,z1,z1072,z3,z5,z6]),(0,[z0,z1,z12,z129,z5,z6]),(0,[z0,z1,z1073,z3,z4,z6])]],
   [[(0,[z194,z1,z54,z4,z5,z6]),(0,[z0,z1,z1074,z3,z4,z6]),(0,[z0,z1,z1075,z4,z5,z6]),(0,[z163,z0,z407,z3,z4,z6]),(0,[z0,z1,z1076,z3,z4,z6]),(0,[z0,z1,z20,z713,z4,z6]),(0,[z0,z1,z3,z5,z6,z800])],[(0,[z0,z1077,z3,z4,z5,z6]),(0,[z0,z1,z1078,z4,z5,z6]),(0,[z0,z1,z308,z3,z4,z6]),(0,[z0,z1,z3,z221,z5,z212]),(0,[z0,z1,z3,z5,z6,z1079]),(0,[z0,z1,z11,z12,z134,z6]),(0,[z0,z1,z12,z341,z5,z6]),(0,[z0,z1,z3,z4,z315,z6])],[(0,[z0,z1,z3,z1080,z5,z6]),(0,[z0,z1,z1081,z4,z5,z6]),(0,[z128,z1,z306,z3,z4,z131]),(0,[z0,z1,z351,z473,z3,z6]),(0,[z0,z673,z106,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z317]),(0,[z0,z1,z59,z5,z86,z39])],[(0,[z0,z1,z12,z321,z3,z6]),(0,[z0,z1,z364,z77,z4,z6]),(0,[z0,z1,z1082,z4,z5,z6]),(0,[z352,z1,z28,z4,z5,z6])],[(0,[z0,z1,z1083,z3,z5,z6]),(0,[z0,z1,z3,z4,z1084,z6]),(0,[z18,z0,z1,z341,z4,z6]),(0,[z0,z1,z3,z4,z155,z6]),(0,[z0,z1,z1085,z3,z5,z6]),(0,[z1086,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z241,z5,z6]),(0,[z349,z0,z1,z3,z95,z6])],[(0,[z0,z1,z23,z221,z5,z6]),(0,[z0,z1087,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1088,z6])],[(0,[z0,z1,z3,z1089,z5,z6]),(0,[z352,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z325,z5,z6]),(0,[z0,z1,z3,z4,z1090,z6]),(0,[z0,z1,z1091,z4,z5,z6]),(0,[z0,z1,z1092,z3,z4,z6]),(0,[z0,z1,z12,z3,z35,z48]),(0,[z0,z1093,z3,z4,z5,z6]),(0,[z0,z1,z19,z428,z4,z6])],[(0,[z0,z1,z3,z4,z1094,z6]),(0,[z0,z1,z3,z1095,z4,z6]),(0,[z15,z352,z3,z4,z5,z141]),(0,[z0,z1,z328,z3,z5,z6]),(0,[z0,z1,z3,z1096,z5,z6])]],
   [[(0,[z0,z1,z3,z1097,z5,z6]),(0,[z0,z1,z11,z5,z139,z6]),(0,[z0,z1,z12,z3,z889,z6]),(0,[z0,z1,z3,z5,z416,z123])],[(0,[z0,z1,z3,z1098,z5,z6]),(0,[z0,z1,z70,z321,z3,z6]),(0,[z0,z1,z11,z3,z5,z913]),(0,[z0,z1,z11,z5,z79,z6]),(0,[z0,z1,z11,z3,z315,z6]),(0,[z0,z1,z11,z4,z134,z6]),(0,[z0,z1,z3,z151,z6,z42]),(0,[z0,z1,z341,z5,z6,z13])],[(0,[z242,z90,z3,z4,z91,z6]),(0,[z0,z1,z1099,z3,z5,z6]),(0,[z0,z1,z3,z1100,z5,z6]),(0,[z0,z1,z3,z1101,z5,z6])],[(0,[z0,z1,z11,z5,z6,z145]),(0,[z0,z1,z154,z273,z4,z6]),(0,[z0,z1,z11,z5,z146,z6]),(0,[z0,z1,z129,z110,z5,z6])],[(0,[z0,z7,z3,z205,z5,z6]),(0,[z0,z1,z1102,z3,z5,z6])],[(0,[z1103,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1104,z6]),(0,[z14,z1,z3,z4,z149,z6]),(0,[z0,z1,z11,z5,z156,z6]),(0,[z535,z0,z1,z11,z5,z6])],[(1,[z790,z3,z4,z5,z6]),(0,[z0,z1,z12,z3,z130,z6]),(0,[z0,z1,z3,z4,z6,z1105]),(0,[z506,z1,z397,z3,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z1106,z6]),(0,[z128,z7,z3,z4,z5,z131]),(0,[z0,z1,z832,z5,z166,z6]),(0,[z0,z1,z3,z95,z6,z123]),(0,[z0,z1,z3,z4,z1107,z6]),(0,[z0,z1,z919,z341,z5,z6])],[(0,[z0,z1,z3,z273,z4,z6]),(0,[z0,z1,z11,z318,z5,z6])],[(0,[z0,z1,z3,z110,z155,z6]),(0,[z0,z1,z12,z138,z5,z6])],[(0,[z0,z1,z3,z205,z5,z6]),(0,[z0,z1,z3,z1108,z5,z6]),(0,[z0,z1,z1109,z3,z5,z6]),(0,[z0,z1,z1110,z3,z4,z6])],[(0,[z0,z1,z3,z1111,z5,z6]),(0,[z0,z1112,z3,z4,z5,z6]),(0,[z0,z1,z138,z325,z5,z6]),(0,[z0,z1,z11,z3,z190,z6]),(0,[z0,z1,z976,z11,z3,z6]),(0,[z0,z1,z19,z11,z97,z6]),(0,[z0,z1,z3,z5,z68,z216]),(0,[z0,z1,z12,z657,z5,z6]),(0,[z0,z1,z3,z4,z29,z42]),(0,[z0,z1,z151,z5,z6,z244])],[(0,[z0,z1,z3,z4,z5,z1113]),(0,[z0,z1,z23,z12,z5,z6]),(0,[z0,z1114,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1115,z6]),(0,[z0,z1,z12,z3,z315,z6]),(0,[z0,z1,z1116,z3,z4,z6])],[(0,[z0,z1,z1117,z4,z5,z6]),(0,[z0,z1,z1118,z3,z5,z6]),(0,[z0,z153,z51,z4,z5,z6]),(0,[z0,z75,z281,z165,z5,z6]),(0,[z0,z1,z3,z1119,z5,z6]),(0,[z0,z1,z135,z11,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1120]),(0,[z0,z1,z1121,z510,z5,z6]),(0,[z128,z1,z3,z4,z5,z131]),(0,[z0,z1,z11,z5,z6,z181]),(0,[z0,z297,z1,z164,z5,z6]),(0,[z0,z1,z3,z4,z1122,z6]),(0,[z132,z0,z66,z3,z5,z6]),(0,[z0,z1,z11,z85,z5,z6]),(0,[z0,z1,z3,z4,z6,z425]),(0,[z0,z1,z341,z4,z79,z6]),(0,[z0,z1,z3,z5,z68,z991])]],
   [[(0,[z0,z1,z1123,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1124]),(0,[z0,z1,z3,z4,z427,z6]),(0,[z56,z1,z11,z3,z5,z57]),(0,[z0,z1,z444,z3,z4,z6]),(0,[z0,z1,z11,z3,z946,z6]),(0,[z0,z1,z12,z3,z1084,z6])],[(0,[z56,z1,z3,z4,z5,z672]),(0,[z0,z1,z60,z321,z4,z6]),(0,[z0,z1,z3,z4,z1125,z6]),(0,[z0,z1,z11,z663,z5,z6]),(0,[z0,z1,z3,z1126,z5,z6]),(0,[z0,z1,z3,z35,z48,z13]),(0,[z0,z1,z5,z6,z244,z13])],[(0,[z0,z1,z3,z4,z1127,z6]),(0,[z0,z1,z12,z237,z5,z6]),(0,[z1128,z1,z3,z4,z5,z6]),(0,[z0,z1,z442,z77,z4,z6])],[(0,[z0,z1129,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z1130]),(0,[z0,z1,z11,z164,z5,z6]),(0,[z0,z1,z3,z1131,z5,z6]),(0,[z0,z1,z11,z60,z5,z39]),(0,[z0,z1,z3,z4,z1132,z6]),(0,[z0,z1,z107,z5,z218,z6])],[(0,[z0,z1,z233,z3,z4,z6]),(0,[z307,z0,z1,z11,z5,z6]),(0,[z0,z75,z164,z165,z5,z6]),(0,[z0,z1,z11,z690,z5,z6]),(0,[z0,z1,z3,z1133,z5,z6])],[(0,[z0,z1,z23,z4,z5,z6]),(0,[z0,z1,z3,z1134,z5,z6]),(0,[z0,z1,z11,z3,z5,z1113]),(0,[z0,z1,z997,z11,z3,z6]),(0,[z0,z1,z12,z318,z5,z6]),(0,[z0,z1,z3,z151,z35,z6])],[(0,[z0,z1,z3,z4,z1135,z6]),(0,[z30,z1,z3,z81,z5,z6]),(0,[z0,z1136,z3,z4,z5,z6]),(0,[z0,z1,z1137,z4,z5,z6]),(0,[z0,z74,z466,z4,z5,z6]),(0,[z0,z1,z1138,z3,z4,z6]),(0,[z0,z1,z4,z5,z6,z1139]),(1,[z0,z1,z3,z4,z733])],[(0,[z0,z1,z3,z4,z1140,z5]),(0,[z0,z1,z1141,z4,z5,z6]),(0,[z242,z90,z3,z4,z526,z6]),(0,[z0,z1,z1142,z4,z5,z6]),(0,[z0,z1,z3,z1143,z5,z6]),(0,[z0,z1,z351,z3,z5,z6]),(0,[z0,z3,z777,z4,z5,z6]),(0,[z0,z1,z41,z11,z47,z6]),(0,[z0,z1,z11,z3,z6,z425])]],
   [[(0,[z0,z1,z321,z4,z6,z39]),(0,[z0,z1,z162,z4,z427,z6]),(0,[z0,z1,z11,z3,z427,z6]),(0,[z0,z1,z12,z3,z190,z6]),(0,[z0,z969,z11,z3,z5,z6]),(0,[z0,z1,z11,z5,z6,z1008]),(0,[z0,z1,z11,z417,z5,z6]),(0,[z0,z1,z12,z138,z95,z6])],[(0,[z0,z1,z3,z4,z1144,z6]),(0,[z0,z1,z3,z4,z1145,z6]),(0,[z109,z0,z1,z11,z210,z6]),(0,[z0,z1,z529,z11,z5,z6]),(0,[z500,z0,z1,z11,z5,z6]),(0,[z0,z752,z51,z4,z5,z6]),(0,[z0,z1,z11,z298,z5,z6]),(0,[z0,z1,z10,z3,z5,z225]),(0,[z0,z1,z3,z120,z6,z89]),(0,[z0,z1,z939,z3,z4,z6])],[(0,[z0,z1,z1146,z4,z5,z6]),(0,[z0,z1,z1147,z4,z5,z6]),(0,[z90,z790,z3,z4,z5,z6]),(0,[z0,z1,z3,z1148,z5,z6]),(0,[z0,z1,z1149,z4,z5,z6]),(0,[z349,z0,z1,z11,z5,z6]),(0,[z0,z1,z41,z11,z6,z42])],[(0,[z0,z258,z162,z4,z5,z6]),(0,[z0,z1,z11,z678,z5,z6]),(0,[z0,z1,z11,z3,z5,z1130])],[(0,[z0,z1,z3,z1150,z5,z6]),(0,[z257,z1,z3,z707,z5,z6]),(0,[z257,z1,z23,z311,z5,z6]),(0,[z0,z1,z3,z1151,z4,z6]),(0,[z0,z1,z11,z120,z97,z6]),(0,[z0,z1,z1152,z3,z4,z6]),(0,[z0,z1,z3,z221,z124,z6])],[(0,[z0,z1,z3,z4,z1153,z6]),(0,[z0,z1,z3,z4,z1154,z6]),(0,[z0,z1,z4,z5,z6,z1155]),(0,[z128,z1,z3,z110,z5,z131]),(0,[z1156,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1157,z6]),(0,[z0,z1,z364,z11,z5,z6]),(0,[z0,z1,z11,z20,z97,z6]),(0,[z0,z1,z402,z318,z5,z6])],[(0,[z21,z36,z3,z4,z5,z6]),(0,[z0,z1,z281,z325,z5,z6]),(0,[z462,z1,z3,z567,z5,z6]),(0,[z0,z1,z41,z77,z78,z6])],[(0,[z1,z3,z707,z311,z5,z6]),(1,[z0,z1,z939,z3,z6])]],
   [[(1,[z0,z1,z1121,z5,z6]),(0,[z194,z0,z1,z11,z5,z6]),(0,[z0,z1,z11,z3,z228,z6]),(0,[z0,z1,z3,z470,z5,z6])],[(0,[z0,z1,z11,z548,z5,z6]),(0,[z0,z1,z341,z77,z4,z6]),(0,[z0,z1,z341,z151,z5,z6])],[(0,[z1158,z1,z3,z4,z5,z6]),(0,[z0,z1,z107,z12,z5,z6]),(0,[z0,z1,z1159,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1160]),(0,[z0,z1,z3,z1161,z5,z6])],[(0,[z36,z3,z4,z5,z6,z26]),(0,[z0,z1,z3,z4,z1162,z6]),(0,[z0,z1,z3,z1163,z4,z6]),(0,[z514,z1,z597,z3,z5,z6]),(0,[z0,z1,z12,z3,z6,z425]),(0,[z0,z1,z3,z120,z218,z6])],[(0,[z109,z514,z1,z11,z5,z6]),(0,[z182,z1,z64,z4,z5,z6]),(0,[z0,z1,z12,z3,z427,z6]),(0,[z641,z0,z1,z11,z5,z6]),(0,[z163,z0,z11,z3,z46,z6])],[(0,[z0,z1,z1164,z3,z4,z6]),(0,[z257,z1,z587,z3,z5,z6]),(0,[z18,z1,z3,z4,z105,z6]),(0,[z0,z1,z3,z1165,z5,z6]),(0,[z0,z75,z3,z190,z165,z6]),(0,[z0,z1,z11,z867,z5,z6]),(0,[z0,z1,z3,z95,z218,z6]),(0,[z0,z1,z60,z4,z315,z6])],[(0,[z21,z36,z11,z3,z5,z6]),(1,[z0,z752,z4,z5,z6]),(0,[z15,z0,z444,z3,z4,z141])],[(0,[z0,z1,z11,z136,z5,z6]),(0,[z531,z1,z3,z311,z5,z6])]],
   [[(0,[z0,z1,z3,z460,z5,z6]),(0,[z0,z1,z1166,z3,z4,z5]),(0,[z257,z0,z1,z23,z5,z6]),(0,[z0,z1,z3,z4,z249,z6]),(0,[z0,z74,z752,z4,z5,z6]),(0,[z0,z1,z3,z756,z4,z6])],[(0,[z0,z1,z1167,z4,z5,z6]),(0,[z0,z1,z245,z11,z3,z6]),(0,[z0,z1,z3,z4,z1168,z6]),(0,[z0,z1,z871,z3,z5,z6]),(0,[z0,z1,z12,z20,z97,z6]),(0,[z1,z3,z4,z5,z6,z1169])],[(0,[z0,z1,z1121,z3,z5,z6]),(0,[z0,z1,z3,z4,z1170,z6]),(0,[z194,z0,z1,z70,z5,z6]),(0,[z1171,z1,z3,z4,z5,z6]),(0,[z0,z1,z107,z4,z5,z6]),(0,[z0,z1,z470,z5,z6,z39])],[(0,[z0,z1,z3,z1172,z5,z6]),(0,[z0,z1,z1173,z3,z5,z6]),(0,[z0,z570,z3,z4,z46,z6]),(0,[z0,z153,z11,z66,z5,z6]),(0,[z0,z1,z3,z4,z1174,z6]),(0,[z0,z1,z3,z4,z6,z236])],[(0,[z0,z1,z1034,z3,z510,z6]),(0,[z0,z1175,z3,z4,z5,z6]),(0,[z0,z119,z3,z4,z697,z6]),(0,[z0,z1,z1176,z4,z5,z6]),(0,[z1177,z1,z3,z4,z5,z6])],[(0,[z0,z1,z50,z3,z4,z6]),(0,[z0,z1,z3,z5,z6,z1178]),(0,[z0,z1,z1179,z4,z5,z6]),(0,[z0,z1,z11,z5,z40,z6]),(0,[z0,z1,z12,z5,z6,z693]),(0,[z0,z1,z122,z3,z5,z991])],[(0,[z0,z1,z20,z528,z4,z6]),(0,[z0,z1,z3,z4,z1180,z6]),(0,[z0,z1,z716,z28,z5,z6]),(0,[z0,z1,z3,z4,z5,z755]),(0,[z0,z1,z41,z11,z35,z6])],[(0,[z0,z1,z245,z3,z4,z6]),(0,[z0,z1181,z3,z4,z5,z6]),(0,[z0,z258,z129,z4,z5,z6]),(0,[z0,z1,z3,z4,z1182,z6])]],
   [[(0,[z109,z0,z1,z11,z5,z6]),(0,[z0,z1,z792,z3,z4,z6]),(0,[z389,z1,z3,z4,z88,z6]),(0,[z0,z1,z3,z4,z35,z82]),(0,[z0,z1,z11,z3,z249,z6]),(0,[z0,z74,z11,z106,z5,z6]),(0,[z0,z1,z11,z341,z5,z6]),(0,[z0,z1,z11,z299,z5,z6]),(0,[z0,z1,z12,z521,z5,z6]),(0,[z0,z1,z3,z4,z1183,z6]),(0,[z0,z1,z1184,z3,z5,z6])],[(0,[z0,z1,z3,z4,z1185,z6]),(0,[z0,z1,z3,z4,z1186,z6]),(0,[z0,z1,z3,z4,z1187,z6]),(0,[z462,z1,z3,z398,z5,z6]),(0,[z15,z0,z3,z567,z5,z141]),(0,[z0,z1,z59,z4,z5,z815]),(0,[z0,z1,z1188,z4,z5,z6])],[(0,[z21,z36,z12,z3,z5,z6]),(0,[z0,z790,z3,z4,z5,z6]),(0,[z0,z1,z11,z321,z3,z6]),(0,[z0,z1,z1189,z3,z5,z6]),(0,[z0,z1,z3,z4,z1190,z6]),(0,[z0,z1,z3,z1191,z5,z6]),(0,[z0,z1,z11,z5,z6,z305])],[(0,[z0,z1,z245,z70,z3,z6]),(0,[z0,z1,z11,z3,z6,z236]),(0,[z0,z1,z3,z4,z6,z1192]),(0,[z0,z1,z607,z3,z5,z216]),(0,[z0,z1,z3,z95,z78,z6]),(0,[z0,z1,z318,z4,z6,z236])],[(0,[z0,z1,z3,z1193,z5,z6]),(0,[z0,z153,z66,z4,z5,z6]),(0,[z0,z1,z3,z4,z48,z58]),(0,[z1177,z1,z11,z3,z5,z6]),(0,[z0,z1,z85,z3,z120,z6]),(0,[z0,z1,z3,z4,z124,z6])],[(0,[z0,z1,z3,z4,z1194,z6]),(0,[z0,z1,z11,z402,z5,z6]),(0,[z0,z1,z3,z5,z6,z1195])],[(0,[z0,z1,z3,z4,z526,z6]),(0,[z1,z3,z709,z4,z5,z6]),(0,[z0,z1,z3,z1196,z4,z6]),(0,[z0,z1,z233,z154,z4,z6]),(0,[z0,z258,z3,z4,z155,z6]),(0,[z0,z1,z308,z11,z3,z6]),(0,[z0,z1,z308,z12,z3,z6]),(0,[z0,z119,z3,z4,z62,z6])],[(0,[z539,z0,z1,z11,z5,z6]),(0,[z0,z1,z3,z4,z1197,z6]),(0,[z0,z286,z1,z11,z5,z6]),(0,[z0,z1,z717,z5,z6,z244])]],
   [[(0,[z0,z1,z3,z1198,z5,z6]),(0,[z575,z0,z3,z4,z5,z141]),(0,[z14,z1,z3,z4,z88,z6]),(0,[z0,z1,z1199,z4,z5,z6]),(0,[z0,z1,z19,z939,z3,z6])],[(0,[z1,z3,z4,z88,z730,z6]),(0,[z1,z3,z4,z5,z6,z785]),(0,[z0,z1,z1200,z3,z4,z6]),(0,[z0,z101,z11,z3,z5,z313]),(0,[z0,z1,z3,z4,z1201,z6]),(0,[z0,z1,z12,z138,z134,z6]),(0,[z0,z1,z19,z335,z428,z6]),(0,[z0,z1,z1202,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1203,z6]),(0,[z0,z74,z1,z351,z5,z6]),(0,[z0,z1,z11,z325,z5,z6]),(0,[z490,z0,z3,z4,z46,z6])],[(0,[z0,z1,z164,z81,z5,z6]),(0,[z163,z0,z3,z4,z882,z6]),(0,[z0,z1,z1092,z11,z3,z6]),(0,[z0,z1,z19,z85,z3,z6])],[(0,[z18,z1,z3,z4,z730,z6]),(0,[z0,z1,z12,z3,z249,z6]),(0,[z0,z74,z12,z106,z5,z6]),(0,[z0,z1,z11,z112,z5,z6]),(0,[z0,z1,z11,z3,z124,z6]),(0,[z0,z1,z1204,z4,z5,z6]),(0,[z0,z1,z318,z4,z124,z6]),(0,[z0,z1,z3,z4,z48,z733])],[(0,[z0,z1,z11,z238,z5,z6]),(0,[z1205,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z1061,z6])],[(0,[z0,z1,z11,z3,z526,z6]),(1,[z1,z709,z4,z5,z6]),(0,[z0,z1,z306,z3,z4,z6]),(0,[z0,z1,z11,z3,z130,z6]),(0,[z0,z119,z11,z3,z62,z6]),(0,[z0,z422,z3,z4,z62,z6]),(0,[z0,z1,z12,z5,z6,z305]),(0,[z0,z1,z77,z4,z79,z6]),(0,[z0,z1,z3,z4,z1206,z6])],[(0,[z0,z1,z1207,z3,z5,z6]),(0,[z0,z1,z1208,z3,z4,z5]),(0,[z0,z1,z3,z5,z1209,z6]),(0,[z0,z1,z70,z5,z6,z39]),(0,[z0,z1,z233,z23,z4,z6]),(0,[z514,z1,z3,z81,z5,z6]),(0,[z0,z1,z3,z1210,z5,z6]),(0,[z0,z1,z3,z5,z6,z1211]),(0,[z523,z1,z587,z3,z5,z6]),(0,[z0,z1,z11,z440,z5,z6]),(0,[z0,z1,z12,z3,z1174,z6]),(0,[z0,z1,z12,z3,z6,z236]),(0,[z0,z1,z3,z221,z5,z667]),(0,[z0,z1,z3,z221,z5,z68]),(0,[z0,z1,z221,z5,z68,z305])]],
   [[(0,[z0,z1,z3,z1212,z5,z6]),(0,[z14,z0,z1,z41,z11,z6]),(0,[z615,z1,z3,z4,z88,z6])],[(0,[z0,z1,z3,z4,z1213,z6]),(0,[z0,z1,z1214,z3,z5,z6]),(0,[z0,z1,z11,z60,z5,z314])],[(0,[z0,z1,z3,z4,z6,z1215]),(0,[z0,z1,z943,z3,z4,z6]),(0,[z0,z1,z3,z221,z68,z236])],[(0,[z0,z1,z1216,z3,z5,z6])],[(0,[z0,z1,z818,z510,z5,z6]),(0,[z0,z1,z3,z4,z6,z1217]),(0,[z15,z0,z3,z398,z5,z141]),(0,[z0,z1,z11,z107,z5,z6]),(0,[z0,z1,z824,z3,z5,z6]),(0,[z0,z1,z12,z3,z1183,z6]),(0,[z0,z1,z1218,z4,z5,z6])],[(0,[z0,z1,z1219,z3,z4,z6]),(0,[z18,z1,z621,z3,z4,z6]),(0,[z0,z258,z3,z205,z5,z6]),(0,[z0,z153,z50,z51,z4,z6]),(0,[z0,z101,z12,z3,z5,z313]),(0,[z0,z1,z1220,z3,z4,z6])],[(0,[z0,z1,z1221,z4,z5,z6]),(0,[z0,z1,z1222,z3,z4,z6]),(0,[z0,z1,z1223,z4,z5,z6]),(0,[z0,z3,z4,z882,z62,z6]),(0,[z0,z1,z41,z11,z97,z6])],[(0,[z0,z1,z3,z510,z5,z6]),(0,[z0,z1,z3,z4,z1224,z6]),(0,[z0,z1,z162,z4,z155,z6]),(0,[z0,z1,z11,z3,z155,z6]),(0,[z0,z1,z3,z777,z5,z6]),(0,[z0,z1,z11,z5,z150,z6]),(0,[z0,z1,z428,z4,z5,z6]),(0,[z0,z1,z3,z120,z695,z6]),(0,[z0,z1,z318,z221,z5,z68])]],
   [[(0,[z0,z1,z3,z4,z571,z6]),(0,[z109,z1,z245,z38,z4,z6]),(0,[z0,z74,z106,z325,z5,z6]),(0,[z0,z3,z4,z46,z882,z6]),(0,[z15,z0,z3,z4,z382,z141]),(0,[z0,z1,z12,z3,z124,z6])],[(0,[z128,z258,z3,z4,z5,z131]),(0,[z0,z24,z1,z164,z5,z6]),(0,[z0,z1,z1225,z3,z4,z6]),(0,[z352,z1,z11,z3,z5,z6])],[(0,[z0,z1,z12,z3,z526,z6]),(0,[z645,z0,z1,z11,z5,z6]),(0,[z0,z258,z3,z4,z427,z6]),(0,[z0,z119,z12,z3,z62,z6])],[(0,[z0,z1,z3,z4,z1226,z6]),(0,[z0,z1,z341,z4,z5,z6]),(0,[z0,z1,z19,z107,z5,z6])],[(0,[z0,z1,z1227,z3,z5,z6]),(0,[z0,z7,z3,z4,z5,z6]),(0,[z14,z1,z12,z3,z88,z6]),(0,[z0,z1,z11,z213,z5,z6]),(0,[z462,z1,z3,z4,z63,z6]),(0,[z0,z1,z11,z371,z5,z6]),(0,[z0,z1,z60,z470,z5,z6])],[(0,[z0,z1,z1228,z3,z5,z6]),(0,[z128,z1,z3,z4,z5,z785]),(0,[z1,z3,z4,z5,z57,z785]),(0,[z0,z1,z3,z4,z1229,z6]),(0,[z0,z1,z11,z259,z5,z6]),(0,[z0,z1,z444,z11,z3,z6]),(0,[z0,z1,z444,z12,z3,z6]),(0,[z0,z1,z20,z4,z424,z6])],[(0,[z21,z790,z3,z4,z5,z6]),(0,[z0,z1,z1230,z4,z5,z6]),(0,[z0,z1,z1231,z3,z4,z6]),(0,[z0,z393,z51,z4,z5,z6]),(0,[z0,z1,z3,z120,z438,z6]),(0,[z0,z1,z197,z4,z228,z6]),(0,[z0,z1,z11,z5,z6,z169]),(0,[z0,z1,z3,z120,z134,z6]),(0,[z0,z1,z3,z4,z1232,z6])],[(0,[z0,z1,z3,z190,z4,z6]),(0,[z0,z1,z11,z442,z5,z6]),(0,[z0,z1,z59,z11,z5,z39]),(0,[z0,z1,z59,z12,z5,z39]),(0,[z0,z1,z77,z713,z4,z6]),(0,[z0,z1,z34,z3,z4,z733])]],
   [[(0,[z0,z1,z11,z3,z571,z6]),(0,[z109,z1,z38,z4,z571,z6])],[(0,[z0,z1,z233,z11,z3,z6]),(0,[z0,z1,z233,z12,z3,z6]),(0,[z0,z1,z259,z4,z97,z6])],[(0,[z0,z1,z3,z4,z1233,z6]),(0,[z0,z1,z154,z384,z5,z6]),(0,[z0,z1,z3,z4,z1234,z6]),(0,[z0,z1,z11,z3,z6,z1105]),(0,[z0,z1,z12,z3,z1196,z6]),(0,[z0,z1,z201,z4,z97,z6]),(0,[z0,z1,z3,z4,z1235,z6]),(0,[z0,z1,z3,z4,z6,z804])],[(0,[z0,z1,z12,z3,z155,z6]),(0,[z0,z1,z19,z3,z596,z6]),(0,[z0,z1,z3,z1236,z5,z6]),(0,[z462,z1,z28,z4,z5,z6]),(0,[z0,z1,z1237,z3,z4,z6])],[(0,[z0,z1,z1238,z3,z4,z6]),(0,[z0,z1,z473,z3,z4,z6]),(0,[z0,z119,z3,z4,z882,z6]),(0,[z0,z1,z3,z567,z63,z6]),(0,[z0,z1,z1239,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1240])],[(0,[z1,z3,z4,z730,z5,z6]),(0,[z0,z1,z3,z1241,z5,z6]),(0,[z352,z1,z12,z3,z5,z6]),(0,[z0,z393,z1,z11,z5,z6]),(0,[z0,z1,z107,z221,z5,z6])],[(0,[z462,z1,z3,z4,z5,z6]),(0,[z0,z1,z138,z4,z571,z6]),(0,[z0,z1242,z3,z4,z5,z6]),(0,[z0,z1,z3,z273,z6,z123]),(0,[z0,z1,z162,z205,z5,z6])],[(0,[z0,z1,z59,z4,z5,z39])]],
   [[(0,[z0,z1,z3,z384,z5,z6]),(0,[z0,z1,z23,z76,z5,z6]),(0,[z0,z1,z1243,z3,z4,z6]),(0,[z0,z1,z12,z197,z5,z6]),(0,[z0,z1,z3,z4,z1244,z6]),(0,[z0,z1,z939,z3,z120,z6]),(0,[z0,z1,z3,z4,z733,z42])],[(0,[z506,z0,z1,z23,z5,z6]),(0,[z0,z1,z11,z88,z97,z6]),(0,[z0,z1,z3,z190,z6,z123]),(0,[z182,z0,z1,z11,z5,z6]),(0,[z555,z0,z1,z11,z5,z6])],[(0,[z506,z0,z1,z11,z5,z6]),(0,[z0,z1,z3,z4,z1245,z6]),(0,[z0,z7,z3,z110,z5,z6]),(0,[z128,z1,z162,z4,z5,z131]),(0,[z128,z1,z11,z3,z5,z131]),(0,[z0,z1,z3,z4,z79,z6])],[(0,[z0,z1,z1246,z3,z5,z6]),(0,[z0,z1,z3,z4,z1247,z6]),(0,[z0,z1,z3,z4,z1248,z6]),(0,[z0,z1,z1118,z129,z5,z6]),(0,[z0,z1,z129,z4,z155,z6]),(0,[z0,z1,z11,z223,z5,z6]),(0,[z0,z1,z28,z567,z5,z6])],[(0,[z0,z1,z12,z3,z571,z6]),(0,[z1,z709,z38,z4,z5,z6]),(0,[z0,z1,z11,z5,z6,z216]),(0,[z0,z1,z11,z60,z316,z6]),(0,[z0,z1,z4,z832,z5,z6]),(0,[z0,z1,z12,z3,z316,z6]),(0,[z0,z1,z341,z4,z35,z48])],[(0,[z0,z1,z4,z5,z6,z1249]),(0,[z0,z1,z3,z4,z6,z1250]),(0,[z0,z3,z4,z5,z755,z141]),(0,[z0,z1,z4,z5,z265,z39])],[(0,[z0,z1,z1121,z4,z5,z6]),(0,[z0,z1,z3,z567,z5,z6]),(0,[z462,z1,z11,z3,z5,z6]),(0,[z0,z1,z3,z5,z6,z1251]),(0,[z0,z1,z20,z4,z97,z6])],[(0,[z0,z1,z11,z5,z6,z227]),(0,[z15,z0,z3,z4,z63,z141])]],
   [[(0,[z109,z1,z587,z4,z5,z6]),(0,[z125,z1,z3,z81,z5,z6]),(0,[z14,z0,z1,z3,z151,z6]),(0,[z0,z74,z106,z291,z5,z6]),(0,[z0,z1,z3,z1252,z5,z6])],[(0,[z0,z1,z1253,z3,z5,z6]),(0,[z0,z1,z3,z1254,z5,z6]),(0,[z0,z1,z11,z345,z5,z6]),(0,[z0,z1,z3,z4,z1255,z6]),(0,[z0,z1,z41,z148,z4,z6])],[(0,[z0,z1,z1256,z3,z5,z6]),(0,[z0,z1,z301,z77,z4,z6]),(0,[z0,z1,z1257,z4,z5,z6]),(0,[z15,z462,z3,z4,z5,z141]),(0,[z0,z1,z12,z3,z1232,z6])],[(0,[z0,z1,z1258,z4,z5,z6]),(0,[z1259,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z91,z6]),(0,[z0,z55,z1,z11,z5,z6]),(0,[z0,z1,z3,z4,z714,z6]),(0,[z0,z153,z1,z11,z249,z6]),(0,[z0,z1,z473,z4,z6,z39]),(0,[z0,z1,z3,z1025,z325,z6]),(0,[z0,z1,z11,z3,z1145,z6])],[(0,[z0,z1,z1260,z3,z5,z6]),(0,[z0,z1,z12,z3,z273,z6]),(0,[z0,z1,z1261,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z1262]),(0,[z0,z1,z1263,z4,z5,z6])],[(0,[z0,z1,z3,z1264,z5,z6]),(0,[z0,z1,z138,z384,z5,z6]),(0,[z0,z1,z3,z1265,z5,z6]),(0,[z128,z1,z12,z3,z5,z131]),(0,[z1,z3,z4,z5,z6,z1266]),(0,[z0,z1,z11,z281,z5,z6]),(0,[z15,z0,z28,z4,z5,z141]),(0,[z0,z1,z11,z60,z5,z215])],[(0,[z21,z0,z1,z1121,z5,z6]),(0,[z0,z1,z3,z4,z5,z902]),(0,[z0,z1,z3,z1267,z5,z6]),(0,[z0,z1,z3,z398,z63,z6]),(0,[z0,z1,z1268,z3,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 511) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 511).take 515) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1026).take 258) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1284)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [511, 515, 258] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 84).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 84).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 174).take 82).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [84, 90, 82] = true :=
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

end PEqualNP.Outside.L_meta_39879

theorem PEqualNP.Outside.L_meta_39879 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276676840 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276676840 * 2 ^ 32 + 4007717088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39879.solve