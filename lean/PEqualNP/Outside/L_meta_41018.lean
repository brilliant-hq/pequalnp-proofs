import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41018

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4270376960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00048985580dbc3a#64 ++ 0x000048985580dbc3#64 ++ 0x408f9f8fd81ffc7d#64 ++ 0xe408f9f8fd81ffc7#64 : BitVec 256),
   (0x433224b32062d5dc#64 ++ 0x0433224b32062d5d#64 ++ 0xc77264f320e3fffb#64 ++ 0xec77264f320e3fff#64 : BitVec 256),
   (0x985c58dc3b038e80#64 ++ 0x0985c58dc3b038e8#64 ++ 0xb87c78fc3f038f87#64 ++ 0xfb87c78fc3f038f8#64 : BitVec 256),
   (0x2d807f000db40b60#64 ++ 0x12d807f000db40b6#64 ++ 0xff807f003ffc0fff#64 ++ 0x7ff807f003ffc0ff#64 : BitVec 256),
   (0x36ff800036db6000#64 ++ 0x236ff800036db600#64 ++ 0x7fff80003ffff00f#64 ++ 0xb7fff80003ffff00#64 : BitVec 256),
   (0x3feb766a80000000#64 ++ 0x43feb766a8000000#64 ++ 0xbfffffffc000000f#64 ++ 0xdbfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 3]⟩, ⟨.and, [6, 4]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [8, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x408f9f8fd81ffc7d 0xe408f9f8fd81ffc7

def z1 : W := mkw 0x2480000004900000 0x0248000000490000 0x7f8000003ffc000f 0x37f8000003ffc000

def z2 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff807f003ffc0fff 0x7ff807f003ffc0ff

def z3 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff80003ffff00f 0xb7fff80003ffff00

def z4 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbfffffffc000000f 0xdbfffffffc000000

def z5 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc77264f320e3fffb 0xec77264f320e3fff

def z6 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c78fc3f038f87 0xfb87c78fc3f038f8

def z7 : W := mkw 0x1848504800000000 0x0184850480000000 0xb87c78fc00000007 0xdb87c78fc0000000

def z8 : W := mkw 0x27a3262280000000 0x427a326228000000 0x07838703c0000008 0x007838703c000000

def z9 : W := mkw 0x0000000000000000 0x0000000000000000 0x008f9f8fc000000d 0xc008f9f8fc000000

def z10 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf8ffffffff1fffff 0xff8ffffffff1ffff

def z11 : W := mkw 0x423200b32042d49c 0x0423200b32042d49 0x007200f30003f000 0x8007200f30003f00

def z12 : W := mkw 0x0014800036db6000 0x20014800036db600 0x400000003ffff000 0x2400000003ffff00

def z13 : W := mkw 0x880058dc09008e80 0x0880058dc09008e8 0x800078fc00000f80 0x4800078fc00000f8

def z14 : W := mkw 0x9858505823020280 0x0985850582302028 0xb870607027000382 0x1b87060702700038

def z15 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0x387c18fc1f038004 0x9387c18fc1f03800

def z16 : W := mkw 0x000480855009b41a 0x0000480855009b41 0x000000000003f000 0x0000000000003f00

def z17 : W := mkw 0x0000000100001018 0x0000000010000101 0x4002040300007078 0x0400204030000707

def z18 : W := mkw 0xbffffffffb0fbeba 0x4bffffffffb0fbeb 0xffffffffff1fffff 0xfffffffffff1ffff

def z19 : W := mkw 0xbffb767aa3020280 0x4bffb767aa302028 0xbfffffffe700038f 0xdbfffffffe700038

def z20 : W := mkw 0x126b006a80000000 0x4126b006a8000000 0x007f80ffc0000000 0x8007f80ffc000000

def z21 : W := mkw 0x7ffb767aa06241c4 0x47ffb767aa06241c 0xbfffffffe0e0038f 0xdbfffffffe0e0038

def z22 : W := mkw 0x0004088418018c00 0x00004088418018c0 0x000c188c18038c05 0xe000c188c18038c0

def z23 : W := mkw 0x800000dc00008480 0x0800000dc0000848 0x000000fc00000000 0x0000000fc0000000

def z24 : W := mkw 0x0800580009000a00 0x00800580009000a0 0xb80078003f000f87 0x7b80078003f000f8

def z25 : W := mkw 0x2580270004b40160 0x12580270004b4016 0x4780070000fc0078 0x04780070000fc007

def z26 : W := mkw 0x67a326238060515c 0x467a326238060515 0x47838703c0e07078 0x047838703c0e0707

def z27 : W := mkw 0x0000090008040820 0x0000009000804082 0x40801f00181c0c7d 0x640801f00181c0c7

def z28 : W := mkw 0x2d84ff855dbdbf7a 0x12d84ff855dbdbf7 0xff8fff8fffffffff 0xfff8fff8ffffffff

def z29 : W := mkw 0x0010009120029498 0x0001000912002949 0xc07264f32003fffb 0xec07264f32003fff

def z30 : W := mkw 0xbddc7edc3b038e80 0x0bddc7edc3b038e8 0xbffc7ffc3f038f8f 0xfbffc7ffc3f038f8

def z31 : W := mkw 0x37ffa40036fb6140 0x237ffa40036fb614 0xffffe4003fffffff 0xfffffe4003ffffff

def z32 : W := mkw 0x37ffa70036ff6160 0x337ffa70036ff616 0x7fff87003ffff07f 0xb7fff87003ffff07

def z33 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbf7fe0ffc0000002 0x9bf7fe0ffc000000

def z34 : W := mkw 0x26b7800036db6000 0x226b7800036db600 0x478380003ffff008 0x2478380003ffff00

def z35 : W := mkw 0x126b006a80000000 0x4126b006a8000000 0x00ff9fffc000000d 0xc00ff9fffc000000

def z36 : W := mkw 0x01002d0008240960 0x001002d000824096 0xc7807f0038fc0fff 0x6c7807f0038fc0ff

def z37 : W := mkw 0x105c000032030000 0x0105c00003203000 0x387c00003f038007 0xb387c00003f03800

def z38 : W := mkw 0x26b2000024d24000 0x026b2000024d2400 0x7ff200003ffff00f 0xb7ff200003ffff00

def z39 : W := mkw 0x927f80dc324be480 0x2927f80dc324be48 0x007f80fc0003f000 0x8007f80fc0003f00

def z40 : W := mkw 0x0000000000000000 0x0000000000000000 0x00838703c0000008 0x000838703c000000

def z41 : W := mkw 0x3fefffefd80dbc3a 0x43fefffefd80dbc3 0xffffffffd81ffc7f 0xfffffffffd81ffc7

def z42 : W := mkw 0x2480000000000000 0x0248000000000000 0x3f8000000000000f 0x13f8000000000000

def z43 : W := mkw 0xd37e24ff3263d5dc 0x0d37e24ff3263d5d 0xc77e64ff20e3fffb 0xec77e64ff20e3fff

def z44 : W := mkw 0x34dd800036db6000 0x234dd800036db600 0x788d80003ffff004 0x3788d80003ffff00

def z45 : W := mkw 0x76ff809136fbf5dc 0x276ff809136fbf5d 0x7fff80003fffffff 0xb7fff80003ffffff

def z46 : W := mkw 0x0000000000000000 0x0000000000000000 0x000c188c00000005 0xc000c188c0000000

def z47 : W := mkw 0x0014800036db6000 0x20014800036db600 0x408f80003ffff00d 0xa408f80003ffff00

def z48 : W := mkw 0x905c00dc32038480 0x0905c00dc3203848 0x007c00fc00038000 0x8007c00fc0003800

def z49 : W := mkw 0x67b3a4b324faf5dc 0x267b3a4b324faf5d 0xc7f3e4f320fffffb 0xec7f3e4f320fffff

def z50 : W := mkw 0x0000008100009418 0x0000000810000941 0x400204830003fc79 0xe400204830003fc7

def z51 : W := mkw 0x985c58dd3b039e98 0x0985c58dd3b039e9 0xf87e7cff3f03ffff 0xff87e7cff3f03fff

def z52 : W := mkw 0xbddc7fdc3fb78fe0 0x1bddc7fdc3fb78fe 0xfffc7ffc3fff8fff 0xffffc7ffc3fff8ff

def z53 : W := mkw 0x2c8058000d900a00 0x02c8058000d900a0 0xff8078003ffc0f8f 0x7ff8078003ffc0f8

def z54 : W := mkw 0x000080014008301a 0x0000080014008301 0x00038003c0007000 0x000038003c000700

def z55 : W := mkw 0x09007fefc8049c3a 0x409007fefc8049c3 0x80007fffc0000c70 0x480007fffc0000c7

def z56 : W := mkw 0x423680b7704bf49e 0x0423680b7704bf49 0x007f80ffc003f000 0x8007f80ffc003f00

def z57 : W := mkw 0x77ffa4b336fbf5dc 0x277ffa4b336fbf5d 0xffffe4f33fffffff 0xfffffe4f33ffffff

def z58 : W := mkw 0x1948766a80000000 0x41948766a8000000 0xb87c7fffc0000007 0xdb87c7fffc000000

def z59 : W := mkw 0x000489855dbdbf7a 0x1000489855dbdbf7 0x400000003ffffff0 0x2400000003ffffff

def z60 : W := mkw 0x801489957b0fbeba 0x0801489957b0fbeb 0x400000003f1ffff0 0x2400000003f1ffff

def z61 : W := mkw 0x3feb766a85b00340 0x53feb766a85b0034 0xbfffffffe7e0038f 0xdbfffffffe7e0038

def z62 : W := mkw 0x1848504800000000 0x0184850480000000 0xb870607000000002 0x1b87060700000000

def z63 : W := mkw 0x3eeb526a80000000 0x43eeb526a8000000 0x38ff9bffc0000004 0x938ff9bffc000000

def z64 : W := mkw 0x2580240004b00140 0x02580240004b0014 0xff8064003ffc0fff 0x7ff8064003ffc0ff

def z65 : W := mkw 0x080059000db40b60 0x1080059000db40b6 0xf80078003ffc0ff7 0x7f80078003ffc0ff

def z66 : W := mkw 0x000480855009b41a 0x0000480855009b41 0x000f808fc003f000 0x8000f808fc003f00

def z67 : W := mkw 0x985858582b020a80 0x0985858582b020a8 0xb87078703f000f87 0x7b87078703f000f8

def z68 : W := mkw 0x184c58cc18018c00 0x0184c58cc18018c0 0xb87c78fc18038c07 0xfb87c78fc18038c0

def z69 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbff3e773c000000a 0x1bff3e773c000000

def z70 : W := mkw 0xbddcffdd7fbfbffa 0x1bddcffdd7fbfbff 0xffffffffffffffff 0xffffffffffffffff

def z71 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x40000000181ffc70 0x240000000181ffc7

def z72 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbf70607000000002 0x1bf7060700000000

def z73 : W := mkw 0x2d80ff014dbc3b7a 0x12d80ff014dbc3b7 0xff83ff03fffc7fff 0x7ff83ff03fffc7ff

def z74 : W := mkw 0x36fb000026d24000 0x236fb000026d2400 0x3f70000027e00002 0x13f70000027e0000

def z75 : W := mkw 0x2d807f810db49f78 0x12d807f810db49f7 0xff827f833fffffff 0xfff827f833ffffff

def z76 : W := mkw 0x0800580009000a00 0x00800580009000a0 0x380018001f000004 0x1380018001f00000

def z77 : W := mkw 0x0900766a80000000 0x40900766a8000000 0x80007fffc0000000 0x480007fffc000000

def z78 : W := mkw 0x126b006a80000000 0x4126b006a8000000 0x0070007000000000 0x0007000700000000

def z79 : W := mkw 0x000009000db40b60 0x1000009000db40b6 0x400000003ffc0ff0 0x2400000003ffc0ff

def z80 : W := mkw 0x2d80760000000000 0x02d8076000000000 0xbf807f000000000f 0x5bf807f000000000

def z81 : W := mkw 0x3feb7f6a8db40b60 0x53feb7f6a8db40b6 0xfffffffffffc0fff 0xffffffffffffc0ff

def z82 : W := mkw 0x3ffff66ab6db6000 0x63ffff66ab6db600 0xfffffffffffff00f 0xffffffffffffff00

def z83 : W := mkw 0x985cd8dc3fdbee80 0x2985cd8dc3fdbee8 0xf87c78fc3fffff87 0xff87c78fc3fffff8

def z84 : W := mkw 0x3ffb766aa6d24000 0x63ffb766aa6d2400 0xbf70607027e00002 0x1bf70607027e0000

def z85 : W := mkw 0x0236800036db6000 0x20236800036db600 0x477200003ffff00b 0xa477200003ffff00

def z86 : W := mkw 0x2d80760005b00340 0x12d80760005b0034 0xbf00600027e00382 0x1bf00600027e0038

def z87 : W := mkw 0x0004800010092000 0x0000480001009200 0x408f8000181ff00d 0xa408f8000181ff00

def z88 : W := mkw 0x36ff89857edffc3a 0x236ff89857edffc3 0x7fff9f8ffffffc7f 0xf7fff9f8ffffffc7

def z89 : W := mkw 0x000009000d940a20 0x1000009000d940a2 0x000000001f1c0000 0x0000000001f1c000

def z90 : W := mkw 0x0000098548049c3a 0x00000098548049c3 0x40021f8fc003fc79 0xe40021f8fc003fc7

def z91 : W := mkw 0x801488943fdbee80 0x2801488943fdbee8 0x400000003fffff80 0x2400000003fffff8

def z92 : W := mkw 0x00048904580d2822 0x000048904580d282 0x008d9b0cd81c0004 0x0008d9b0cd81c000

def z93 : W := mkw 0x9848504803000200 0x0984850480300020 0x3800000007000000 0x1380000000700000

def z94 : W := mkw 0x36eb006a80000000 0x436eb006a8000000 0x3fff80ffc000000f 0x93fff80ffc000000

def z95 : W := mkw 0x2d84ff001dbd2b60 0x12d84ff001dbd2b6 0xff8fff003fffffff 0xfff8fff003ffffff

def z96 : W := mkw 0x0004088418018c00 0x00004088418018c0 0x0000000018038c00 0x20000000018038c0

def z97 : W := mkw 0x3feb76eb80009418 0x43feb76eb8000941 0xffffffffc003fc7f 0xfffffffffc003fc7

def z98 : W := mkw 0x3dc9766a80000000 0x43dc9766a8000000 0xb88dffffc0000004 0x5b88dffffc000000

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001f8fc0000000 0x400001f8fc000000

def z100 : W := mkw 0x3feb7e6a89000a00 0x43feb7e6a89000a0 0xbfffffffff000f8f 0xfbfffffffff000f8

def z101 : W := mkw 0x6fb6ffb77dfffffe 0x16fb6ffb77dfffff 0xffffffffffffffff 0xffffffffffffffff

def z102 : W := mkw 0x0232000020424000 0x0023200002042400 0x007200000003f000 0x8007200000003f00

def z103 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xc7807f0000fc0ff8 0x4c7807f0000fc0ff

def z104 : W := mkw 0x2484800014992000 0x0248480001499200 0x7f8f80003ffff00f 0xb7f8f80003ffff00

def z105 : W := mkw 0x104d800012092000 0x2104d80001209200 0x000d800000000000 0x0000d80000000000

def z106 : W := mkw 0x0000098548049c3a 0x00000098548049c3 0x00001f8fc0000c70 0x400001f8fc0000c7

def z107 : W := mkw 0x985c585c3b030a80 0x0985c585c3b030a8 0xb87c787c3f000386 0x1b87c787c3f00038

def z108 : W := mkw 0x0010001020020080 0x0001000102002008 0x8070607020000382 0x0807060702000038

def z109 : W := mkw 0x2d807f6a8db40b60 0x52d807f6a8db40b6 0xff807ffffffc0fff 0x7ff807ffffffc0ff

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z111 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbf707fffc0000002 0x5bf707fffc000000

def z112 : W := mkw 0x985c584c3b030a00 0x0985c584c3b030a0 0x387c180c3f038007 0xb387c180c3f03800

def z113 : W := mkw 0x40148995786ffdfe 0x040148995786ffdf 0x4000000038fffff0 0x24000000038fffff

def z114 : W := mkw 0x432224a30060d55c 0x0432224a30060d55 0x4702048300e3fc79 0xe4702048300e3fc7

def z115 : W := mkw 0x401000912042d49c 0x0401000912042d49 0x000000000003f000 0x0000000000003f00

def z116 : W := mkw 0x89007fdc09248fe0 0x189007fdc09248fe 0x80007ffc00000ff0 0x480007ffc00000ff

def z117 : W := mkw 0xbffb767aa3020280 0x4bffb767aa302028 0xbf70607027000382 0x1bf7060702700038

def z118 : W := mkw 0xbfff7efebb038e80 0x4bfff7efebb038e8 0xbfffffffff038f8f 0xfbfffffffff038f8

def z119 : W := mkw 0x09007f0009240b60 0x109007f0009240b6 0x80007f0000000ff0 0x480007f0000000ff

def z120 : W := mkw 0x127f8000324b6000 0x2127f8000324b600 0x007f80000003f000 0x8007f80000003f00

def z121 : W := mkw 0x0223002280000000 0x4022300228000000 0x00038003c0000000 0x000038003c000000

def z122 : W := mkw 0x7ffb76fba062d5dc 0x47ffb76fba062d5d 0xffffffffe0e3ffff 0xfffffffffe0e3fff

def z123 : W := mkw 0x3feff66a96992000 0x63feff66a9699200 0xbfffffffdf1c000f 0xdbfffffffdf1c000

def z124 : W := mkw 0x26a3800004d86000 0x226a3800004d8600 0x4783800000fc7008 0x04783800000fc700

def z125 : W := mkw 0x432224230060515c 0x0432224230060515 0x4702040300e07078 0x04702040300e0707

def z126 : W := mkw 0x984c584c1b010a00 0x0984c584c1b010a0 0x380c180c1f000004 0x1380c180c1f00000

def z127 : W := mkw 0x2580270004b40160 0x12580270004b4016 0xc780670020fc0ffb 0x6c780670020fc0ff

def z128 : W := mkw 0x985c50dc33038680 0x0985c50dc3303868 0xb87c60fc27038382 0x9b87c60fc2703838

def z129 : W := mkw 0x0000098548049c3a 0x00000098548049c3 0x0000000000000c70 0x00000000000000c7

def z130 : W := mkw 0xdb7a74fb2362d7dc 0x0db7a74fb2362d7d 0xff7264f327e3fffb 0xfff7264f327e3fff

def z131 : W := mkw 0x3fffff857fffff7a 0x33fffff857fffff7 0xffffff8fffffffff 0xfffffff8ffffffff

def z132 : W := mkw 0x43362cb73863dddc 0x043362cb73863ddd 0xc77e7cff38e3ffff 0xec77e7cff38e3fff

def z133 : W := mkw 0x36eb000000000000 0x036eb00000000000 0x3fff80000000000f 0x93fff80000000000

def z134 : W := mkw 0x67a3a42304f8715c 0x267a3a42304f8715 0x4783840300fc7078 0x04783840300fc707

def z135 : W := mkw 0x2d80760005b00340 0x12d80760005b0034 0xff8060003ffc038f 0x3ff8060003ffc038

def z136 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbf7c78fc00000007 0xdbf7c78fc0000000

def z137 : W := mkw 0x08005b0009040a20 0x108005b0009040a2 0x00001b0000000000 0x000001b000000000

def z138 : W := mkw 0x433224b32042d49c 0x0433224b32042d49 0x877264f30003f00b 0xc877264f30003f00

def z139 : W := mkw 0x7feb76fb802095dc 0x47feb76fb802095d 0xbfffffffc0000fff 0xdbfffffffc0000ff

def z140 : W := mkw 0x490076fb802095dc 0x4490076fb802095d 0x80007fffc0000ff0 0x480007fffc0000ff

def z141 : W := mkw 0x985cd8dd7b0bbe9a 0x0985cd8dd7b0bbe9 0xb87ff8ffff03ff87 0xfb87ff8ffff03ff8

def z142 : W := mkw 0x0800590009040a20 0x00800590009040a2 0xf8807f003f1c0fff 0x7f8807f003f1c0ff

def z143 : W := mkw 0x3ffff66ab24b6000 0x63ffff66ab24b600 0xbfffffffc003f00f 0xdbfffffffc003f00

def z144 : W := mkw 0x000480855009b41a 0x0000480855009b41 0x008f9f8fc003f00d 0xc008f9f8fc003f00

def z145 : W := mkw 0x34c9000000000000 0x034c900000000000 0x388d800000000004 0x1388d80000000000

def z146 : W := mkw 0x185850d820028480 0x0185850d82002848 0xb87c78fc20038f87 0xfb87c78fc20038f8

def z147 : W := mkw 0x3feb7f6a8db40b60 0x53feb7f6a8db40b6 0xfff07f703ffc0fff 0x7fff07f703ffc0ff

def z148 : W := mkw 0x0322242200000000 0x0032224220000000 0x87ffffffc000000f 0xc87ffffffc000000

def z149 : W := mkw 0x0326ada7580dbc3a 0x00326ada7580dbc3 0xc7ffffffd81ffc7f 0xec7ffffffd81ffc7

def z150 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0x3f8f9f0fc000000c 0x13f8f9f0fc000000

def z151 : W := mkw 0x3ffff60037fb6340 0x33ffff60037fb634 0xffffe0003ffff38f 0xbffffe0003ffff38

def z152 : W := mkw 0x0900766a80000000 0x40900766a8000000 0x808fffffc000000d 0xc808fffffc000000

def z153 : W := mkw 0x0100270000240160 0x1010027000024016 0x0000070000000070 0x0000007000000007

def z154 : W := mkw 0x3feb7f000db40b60 0x13feb7f000db40b6 0xffffff003ffc0fff 0xfffffff003ffc0ff

def z155 : W := mkw 0x1b6a746a00000000 0x01b6a746a0000000 0xbf7e7cff0000000f 0xdbf7e7cff0000000

def z156 : W := mkw 0x3feff6efd009b41a 0x43feff6efd009b41 0xbfffffffc003f00f 0xdbfffffffc003f00

def z157 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff8fff8ffffc0fff 0xfff8fff8ffffc0ff

def z158 : W := mkw 0x9858505823020280 0x0985850582302028 0xb87c78fc27000387 0xdb87c78fc2700038

def z159 : W := mkw 0x43322432206241c4 0x043322432206241c 0x8770607020e00382 0x08770607020e0038

def z160 : W := mkw 0x3fffff003fff6b60 0x33fffff003fff6b6 0xffffff003fffffff 0xfffffff003ffffff

def z161 : W := mkw 0x9a7f58febb038e80 0x49a7f58febb038e8 0xb87ff8ffff038f87 0xfb87ff8ffff038f8

def z162 : W := mkw 0x36ef800010092000 0x036ef80001009200 0x7fff8000181ff00f 0xb7fff8000181ff00

def z163 : W := mkw 0xdb7efdff7b6ffffe 0x0db7efdff7b6ffff 0xffffffffffffffff 0xffffffffffffffff

def z164 : W := mkw 0x4322242200604144 0x0432224220060414 0x0700000000e00000 0x00700000000e0000

def z165 : W := mkw 0x5b7a74fb2062d5dc 0x05b7a74fb2062d5d 0xff7e7cff20e3ffff 0xfff7e7cff20e3fff

def z166 : W := mkw 0x2c80520005900200 0x12c8052000590020 0x3800000007000000 0x1380000000700000

def z167 : W := mkw 0x0322242200000000 0x0032224220000000 0x877264f30000000b 0xc877264f30000000

def z168 : W := mkw 0x36ff8000324b6000 0x236ff8000324b600 0x3fff80000003f00f 0x93fff80000003f00

def z169 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x47ff800000fff008 0x847ff800000fff00

def z170 : W := mkw 0xbdd8765827b203c0 0x1bdd8765827b203c 0xbf70607027e00382 0x1bf70607027e0038

def z171 : W := mkw 0xbfff76feb2038480 0x4bfff76feb203848 0xbfffffffc003800f 0xdbfffffffc003800

def z172 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbff07f700000000f 0x5bff07f700000000

def z173 : W := mkw 0x0000006a80000000 0x40000006a8000000 0x000000ffc0000000 0x0000000ffc000000

def z174 : W := mkw 0x3feb766a80200140 0x43feb766a8020014 0xffffffffe0e00fff 0xfffffffffe0e00ff

def z175 : W := mkw 0x0800524880000000 0x4080052488000000 0x00001b0cc0000000 0x000001b0cc000000

def z176 : W := mkw 0x432224b30060d5dc 0x0432224b30060d5d 0xc70264f300e07ff8 0x4c70264f300e07ff

def z177 : W := mkw 0x00148995780fbcba 0x000148995780fbcb 0xc0fffffff81fffff 0xec0fffffff81ffff

def z178 : W := mkw 0x3feff66a90092000 0x43feff66a9009200 0xffffffffd81ff00f 0xfffffffffd81ff00

def z179 : W := mkw 0x4336a4b336fbf5dc 0x24336a4b336fbf5d 0xc77264f33ffffffb 0xec77264f33ffffff

def z180 : W := mkw 0xd95c7cff3b239fdc 0x0d95c7cff3b239fd 0xb87c7cff3f038ff7 0xfb87c7cff3f038ff

def z181 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf87c78fc3f1ffff7 0xff87c78fc3f1ffff

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000600020000f83 0x68000600020000f8

def z183 : W := mkw 0x000480855009b41a 0x0000480855009b41 0x400f848fc003fc79 0xe400f848fc003fc7

def z184 : W := mkw 0x77fb24b32062d5dc 0x077fb24b32062d5d 0xffffe4f320e3ffff 0xfffffe4f320e3fff

def z185 : W := mkw 0x001489857edffc3a 0x2001489857edffc3 0x408f9f8ffffffc7d 0xe408f9f8ffffffc7

def z186 : W := mkw 0x0000000005b00340 0x10000000005b0034 0x0000000027e00380 0x00000000027e0038

def z187 : W := mkw 0x3ccdd24896992000 0x63ccdd2489699200 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z188 : W := mkw 0x2480000004900000 0x0248000000490000 0x3f00000027e00002 0x13f00000027e0000

def z189 : W := mkw 0x2d94ff003fff6b60 0x32d94ff003fff6b6 0xff807f003fffffff 0x7ff807f003ffffff

def z190 : W := mkw 0x3dcdff001fbd2b60 0x33dcdff001fbd2b6 0xff8dff003ffc0fff 0x7ff8dff003ffc0ff

def z191 : W := mkw 0x0b22766a80000000 0x40b22766a8000000 0x87727fffc000000b 0xc87727fffc000000

def z192 : W := mkw 0x89007efe89008e80 0x489007efe89008e8 0x80007fffc0000f80 0x480007fffc0000f8

def z193 : W := mkw 0x34dd8000369b2000 0x234dd8000369b200 0x38fd80003f1f8007 0xb38fd80003f1f800

def z194 : W := mkw 0x905c08dc3a038c80 0x0905c08dc3a038c8 0x007c18fc18038c05 0xe007c18fc18038c0

def z195 : W := mkw 0x8800505801000280 0x0880050580100028 0x8000607000000380 0x0800060700000038

def z196 : W := mkw 0x985c59dd7b079eba 0x0985c59dd7b079eb 0xb87c7fffff038ff7 0xfb87c7fffff038ff

def z197 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87060703f038f82 0x3b87060703f038f8

def z198 : W := mkw 0x00048904580d2822 0x000048904580d282 0x00000000181c0000 0x000000000181c000

def z199 : W := mkw 0x3effd248b6db6000 0x63effd248b6db600 0x7fff9b0cfffff00f 0xb7fff9b0cfffff00

def z200 : W := mkw 0x0100240000200140 0x0010024000020014 0xc700640020e00ffb 0x6c700640020e00ff

def z201 : W := mkw 0x880058dc09008e80 0x0880058dc09008e8 0xb80078fc3f000f87 0x7b80078fc3f000f8

def z202 : W := mkw 0x401000912062d5dc 0x0401000912062d5d 0x4000000020e3fff0 0x24000000020e3fff

def z203 : W := mkw 0x00048101500d303a 0x000048101500d303 0x408f8703d81ff07d 0xa408f8703d81ff07

def z204 : W := mkw 0x7ffb767aa06241c4 0x47ffb767aa06241c 0xbf70607020e00382 0x1bf70607020e0038

def z205 : W := mkw 0x0800500001000200 0x0080050000100020 0xb800600027000382 0x1b80060002700038

def z206 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc7ffffffe0e3ffff 0xec7ffffffe0e3fff

def z207 : W := mkw 0x0000008100009418 0x0000000810000941 0x408f9f8fc003fc7d 0xe408f9f8fc003fc7

def z208 : W := mkw 0x2c805b000d940a20 0x12c805b000d940a2 0x38801b001f1c0004 0x138801b001f1c000

def z209 : W := mkw 0x0232000020424000 0x0023200002042400 0x4772000020e3f00b 0xa4772000020e3f00

def z210 : W := mkw 0x410024b3002095dc 0x0410024b3002095d 0x800064f300000ff0 0x4800064f300000ff

def z211 : W := mkw 0x0900760000000000 0x0090076000000000 0x80007f0000000000 0x480007f000000000

def z212 : W := mkw 0x34cd800016992000 0x234cd80001699200 0x388d80001f1c0004 0x1388d80001f1c000

def z213 : W := mkw 0x36ff808576dbf41a 0x236ff808576dbf41 0x7fff808ffffff00f 0xb7fff808ffffff00

def z214 : W := mkw 0x3cc9524880000000 0x43cc952488000000 0x388d9b0cc0000004 0x1388d9b0cc000000

def z215 : W := mkw 0x995c7efebb038e80 0x4995c7efebb038e8 0xb87c7fffff038f87 0xfb87c7fffff038f8

def z216 : W := mkw 0x984c584c1b010a00 0x0984c584c1b010a0 0xb87c78fc1f000007 0xdb87c78fc1f00000

def z217 : W := mkw 0x26a7800014d96000 0x226a7800014d9600 0x478f800018fff00d 0xa478f800018fff00

def z218 : W := mkw 0x105c800036db6000 0x2105c800036db600 0x787c00003ffff007 0xb787c00003ffff00

def z219 : W := mkw 0x985858dc2b028e80 0x0985858dc2b028e8 0xb87078fc27000f82 0x5b87078fc27000f8

def z220 : W := mkw 0x4336adb7786ffdfe 0x04336adb7786ffdf 0xc7fffffff8ffffff 0xec7fffffff8fffff

def z221 : W := mkw 0x6fb27fb32df6dffc 0x16fb27fb32df6dff 0xfff27ff33fffffff 0xffff27ff33ffffff

def z222 : W := mkw 0x905c00dc32038480 0x0905c00dc3203848 0x387c00fc3f038007 0xb387c00fc3f03800

def z223 : W := mkw 0x00008101400c303a 0x000008101400c303 0x40838703c01c7078 0x040838703c01c707

def z224 : W := mkw 0x3effd04836db6000 0x23effd04836db600 0xfffff8fc3ffff00f 0xffffff8fc3ffff00

def z225 : W := mkw 0x432224230060515c 0x0432224230060515 0xc77264f300e0707b 0xcc77264f300e0707

def z226 : W := mkw 0x26b3800024da6000 0x226b3800024da600 0x47f3800020fff00b 0xa47f3800020fff00

def z227 : W := mkw 0x0004008410018400 0x0000400841001840 0x000c008c00038000 0x8000c008c0003800

def z228 : W := mkw 0x985850d823028680 0x0985850d82302868 0xb87060f027038f83 0xfb87060f027038f8

def z229 : W := mkw 0x000488855809bc1a 0x0000488855809bc1 0x000f988fd803fc05 0xe000f988fd803fc0

def z230 : W := mkw 0x423200b32042d49c 0x0423200b32042d49 0x407204f30003fc79 0xe407204f30003fc7

def z231 : W := mkw 0x36ff89047edf6822 0x236ff89047edf682 0x7fff9b0cfffff00f 0xb7fff9b0cfffff00

def z232 : W := mkw 0x985c59dc3fb78fe0 0x1985c59dc3fb78fe 0xf87c78fc3fff8ff7 0xff87c78fc3fff8ff

def z233 : W := mkw 0xbcdc5bdc3f978ea0 0x1bcdc5bdc3f978ea 0xb8fc7bfc3f1f8f87 0xfb8fc7bfc3f1f8f8

def z234 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff9f8ffffff00f 0xf7fff9f8ffffff00

def z235 : W := mkw 0x67a2272304f4517c 0x167a2272304f4517 0x4782070300fc7078 0x04782070300fc707

def z236 : W := mkw 0x34cd89855e9dbc3a 0x234cd89855e9dbc3 0x788f9f8fdf1ffc7d 0xf788f9f8fdf1ffc7

def z237 : W := mkw 0x6fb27f322df64be4 0x16fb27f322df64be 0xfff07f703ffc0fff 0x7fff07f703ffc0ff

def z238 : W := mkw 0x248489855c9dbc3a 0x0248489855c9dbc3 0x7f8f9f8ffffffc7f 0xf7f8f9f8ffffffc7

def z239 : W := mkw 0x527b00fba042d49c 0x4527b00fba042d49 0x007f80ffc003f000 0x8007f80ffc003f00

def z240 : W := mkw 0x3feb760000000000 0x03feb76000000000 0xbfffff000000000f 0xdbfffff000000000

def z241 : W := mkw 0x185c504832030000 0x0185c50483203000 0xb87c78fc3f038007 0xfb87c78fc3f03800

def z242 : W := mkw 0x0000098548049c3a 0x00000098548049c3 0x008f9f8fc0000c7d 0xc008f9f8fc0000c7

def z243 : W := mkw 0x801408943b038e80 0x0801408943b038e8 0x807060f03f038f83 0xe807060f03f038f8

def z244 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x3ffd80003ffc0006 0x13ffd80003ffc000

def z245 : W := mkw 0x3fefff6ed80d2822 0x43fefff6ed80d282 0xbfffffffd81c000f 0xdbfffffffd81c000

def z246 : W := mkw 0x9a7fd8dc3b4bee80 0x29a7fd8dc3b4bee8 0xb87ff8fc3f03ff87 0xfb87ff8fc3f03ff8

def z247 : W := mkw 0xbeffd8dc3fdbee80 0x2beffd8dc3fdbee8 0xfffff8fc3fffff8f 0xffffff8fc3fffff8

def z248 : W := mkw 0x985cd9dc7b0faea2 0x0985cd9dc7b0faea 0xb8fdfbfcff1f8f87 0xfb8fdfbfcff1f8f8

def z249 : W := mkw 0x411024b32062d5dc 0x0411024b32062d5d 0xc00064f320e3fff0 0x6c00064f320e3fff

def z250 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f808fc0000000 0x8000f808fc000000

def z251 : W := mkw 0x6fb276b325f2d7dc 0x16fb276b325f2d7d 0xff7264f327e3fffb 0xfff7264f327e3fff

def z252 : W := mkw 0x1b6b766a80000000 0x41b6b766a8000000 0x807fffffc0000000 0xc807fffffc000000

def z253 : W := mkw 0x2fb27f002df64b60 0x12fb27f002df64b6 0xfff27f003fffffff 0xffff27f003ffffff

def z254 : W := mkw 0xb6ff88943fdbee80 0x2b6ff88943fdbee8 0x7fff80003fffff8f 0xb7fff80003fffff8

def z255 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc770607020e3fff2 0x2c770607020e3fff

def z256 : W := mkw 0x2d80760005b00340 0x12d80760005b0034 0xbf807f0027e0038f 0x5bf807f0027e0038

def z257 : W := mkw 0x0100240000000000 0x0010024000000000 0x870064000000000b 0x4870064000000000

def z258 : W := mkw 0x37eb266a80000000 0x437eb266a8000000 0x07ff87ffc0000008 0x807ff87ffc000000

def z259 : W := mkw 0x1848504800000000 0x0184850480000000 0xb8ffffffc000000f 0xdb8ffffffc000000

def z260 : W := mkw 0x0010009020028480 0x0001000902002848 0x807060f020038f83 0xe807060f020038f8

def z261 : W := mkw 0x67b224b324f2d5dc 0x067b224b324f2d5d 0xfff264f33fffffff 0xffff264f33ffffff

def z262 : W := mkw 0x105c000032030000 0x0105c00003203000 0x007c000000038000 0x8007c00000003800

def z263 : W := mkw 0x527f80b3324bf49c 0x2527f80b3324bf49 0x007f80f30003f000 0x8007f80f30003f00

def z264 : W := mkw 0x3feb7f6a89240b60 0x53feb7f6a89240b6 0xbfffffffc0000fff 0xdbfffffffc0000ff

def z265 : W := mkw 0x105c009032038480 0x0105c00903203848 0xb87c60f03f038f87 0xfb87c60f03f038f8

def z266 : W := mkw 0x3ddc7f003fb70b60 0x13ddc7f003fb70b6 0xfffc7f003fff8fff 0xffffc7f003fff8ff

def z267 : W := mkw 0x09007f0009240b60 0x109007f0009240b6 0xb8007f003f000ff7 0x7b8007f003f000ff

def z268 : W := mkw 0x3feb766a84900000 0x43feb766a8490000 0xfffffffffffc000f 0xffffffffffffc000

def z269 : W := mkw 0x000489855dbdbf7a 0x1000489855dbdbf7 0x408f9f8ffffffffd 0xe408f9f8ffffffff

def z270 : W := mkw 0x000009000db40b60 0x1000009000db40b6 0x40801f003ffc0ffd 0x640801f003ffc0ff

def z271 : W := mkw 0x410024230020115c 0x0410024230020115 0x0000040300000070 0x0000004030000007

def z272 : W := mkw 0x0010009020028480 0x0001000902002848 0x0000000020038f80 0x20000000020038f8

def z273 : W := mkw 0xdb7e7cff3b63dfdc 0x0db7e7cff3b63dfd 0xff7e7cff3fe3ffff 0xfff7e7cff3fe3fff

def z274 : W := mkw 0x995c7cdc3b238fc0 0x0995c7cdc3b238fc 0xff7c7cfc3fe38fff 0xfff7c7cfc3fe38ff

def z275 : W := mkw 0x3fff766ab2030000 0x43fff766ab203000 0xbfffffffff03800f 0xfbfffffffff03800

def z276 : W := mkw 0x2c84db045d9d2a22 0x12c84db045d9d2a2 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z277 : W := mkw 0x3ffb7f002ff64b60 0x33ffb7f002ff64b6 0xfff07f003ffc0fff 0x7fff07f003ffc0ff

def z278 : W := mkw 0xfffe7fff3ff7dffc 0x1fffe7fff3ff7dff 0xfffe7fff3fffffff 0xffffe7fff3ffffff

def z279 : W := mkw 0x36ff810176df703a 0x236ff810176df703 0x7fff8703fffff07f 0xb7fff8703fffff07

def z280 : W := mkw 0x033224b220028480 0x0033224b22002848 0x877264f320038f8b 0xe877264f320038f8

def z281 : W := mkw 0x537b24fba062d5dc 0x4537b24fba062d5d 0xc77fe4ffe0e3fffb 0xec77fe4ffe0e3fff

def z282 : W := mkw 0xbccc5b4c1f950a20 0x1bccc5b4c1f950a2 0x388c1b0c1f1c0004 0x1388c1b0c1f1c000

def z283 : W := mkw 0x40000091002095dc 0x040000091002095d 0x0000000000000ff0 0x00000000000000ff

def z284 : W := mkw 0x00048904580d2822 0x000048904580d282 0x008f9f8fd81c000d 0xc008f9f8fd81c000

def z285 : W := mkw 0xc9007cff09209fdc 0x0c9007cff09209fd 0x80007cff00000ff0 0x480007cff00000ff

def z286 : W := mkw 0x36fb800026da6000 0x236fb800026da600 0x7ff3800027fc700a 0x17ff3800027fc700

def z287 : W := mkw 0x9058005822020080 0x0905800582202008 0x0070007000000000 0x0007000700000000

def z288 : W := mkw 0x2c805b000d940a20 0x12c805b000d940a2 0x78801f001f1c0c7d 0x778801f001f1c0c7

def z289 : W := mkw 0x2d807f000d940a20 0x12d807f000d940a2 0xbf807f001f1c000f 0x5bf807f001f1c000

def z290 : W := mkw 0x432224b3002095dc 0x0432224b3002095d 0x877264f300000ffb 0xc877264f300000ff

def z291 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x408d9b0cd81ffc74 0x2408d9b0cd81ffc7

def z292 : W := mkw 0x3dc97f488db40b60 0x53dc97f488db40b6 0xff8dff0cfffc0fff 0x7ff8dff0cfffc0ff

def z293 : W := mkw 0x77ffa42336fb715c 0x277ffa42336fb715 0x7fff84033ffff07f 0xb7fff84033ffff07

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x0002048300000009 0xc000204830000000

def z295 : W := mkw 0x9b7e7cfe3b038e80 0x09b7e7cfe3b038e8 0xbf7e7cff3f038f8f 0xfbf7e7cff3f038f8

def z296 : W := mkw 0x801408943b038e80 0x0801408943b038e8 0x000000003f038f80 0x2000000003f038f8

def z297 : W := mkw 0x0004098418058c20 0x00004098418058c2 0x408c1f8c181f8c7d 0xe408c1f8c181f8c7

def z298 : W := mkw 0x800408041b010a00 0x0800408041b010a0 0x000000001f000000 0x0000000001f00000

def z299 : W := mkw 0x0000000000200140 0x0000000000020014 0x4000000020e00ff0 0x24000000020e00ff

def z300 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0x4702040320e3fff8 0x24702040320e3fff

def z301 : W := mkw 0x248009000c940820 0x0248009000c94082 0x7f801f003ffc0c7f 0x77f801f003ffc0c7

def z302 : W := mkw 0x537fa4b3326bf5dc 0x2537fa4b3326bf5d 0xc77fe4f320e3fffb 0xec77fe4f320e3fff

def z303 : W := mkw 0x3feb7f6a8d940a20 0x53feb7f6a8d940a2 0xbfffffffdf1c000f 0xdbfffffffdf1c000

def z304 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x40838703d81ffc78 0x240838703d81ffc7

def z305 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0x877260f320e3f382 0x8877260f320e3f38

def z306 : W := mkw 0x0000008100009418 0x0000000810000941 0x400000000003fc70 0x2400000000003fc7

def z307 : W := mkw 0x127f806ab24b6000 0x6127f806ab24b600 0x007f80ffc003f000 0x8007f80ffc003f00

def z308 : W := mkw 0x0804588419018e00 0x00804588419018e0 0xb80c788c3f038f87 0xfb80c788c3f038f8

def z309 : W := mkw 0x0322242200000000 0x0032224220000000 0x8770607000000002 0x0877060700000000

def z310 : W := mkw 0x27a3262280000000 0x427a326228000000 0x078f9f8fc000000d 0xc078f9f8fc000000

def z311 : W := mkw 0x0800504800000000 0x0080050480000000 0x800078fc00000000 0x4800078fc0000000

def z312 : W := mkw 0x43322db32df6dffc 0x143322db32df6dff 0xc77264f33ffffffb 0xec77264f33ffffff

def z313 : W := mkw 0x49007fb309249ffc 0x149007fb309249ff 0x80007ff300000ff0 0x480007ff300000ff

def z314 : W := mkw 0x27a3a723c00c303a 0x427a3a723c00c303 0x47838703c01c7078 0x047838703c01c707

def z315 : W := mkw 0x1058000022020000 0x0105800002202000 0x3870000027000002 0x1387000002700000

def z316 : W := mkw 0x127f8000324b6000 0x2127f8000324b600 0x477f800020e3f00b 0xa477f800020e3f00

def z317 : W := mkw 0x01102490202285c0 0x001102490202285c 0xc77064f020e38ffb 0xec77064f020e38ff

def z318 : W := mkw 0x105c08843a038c00 0x0105c08843a038c0 0x387c188c3f038c07 0xf387c188c3f038c0

def z319 : W := mkw 0x36ff000036d34000 0x236ff000036d3400 0x3f7c00003fe38007 0xb3f7c00003fe3800

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0x807060f000000003 0xc807060f00000000

def z321 : W := mkw 0xdb7e7cfe3b63cfc4 0x0db7e7cfe3b63cfc 0xbf7c78fc3fe38f87 0xfbf7c78fc3fe38f8

def z322 : W := mkw 0x3cc9524880000000 0x43cc952488000000 0xb8fdfbfcc0000007 0xdb8fdfbfcc000000

def z323 : W := mkw 0xbeffd9dd7fdffeba 0x2beffd9dd7fdffeb 0xffffffffffffffff 0xffffffffffffffff

def z324 : W := mkw 0x0800500000000000 0x0080050000000000 0xb800780000000007 0x5b80078000000000

def z325 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x38ff80001f1ff004 0x938ff80001f1ff00

def z326 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0x877064f320e00ff2 0x4877064f320e00ff

def z327 : W := mkw 0x985c505833030280 0x0985c50583303028 0xb87c60703f038387 0xbb87c60703f03838

def z328 : W := mkw 0x984c58cc1b018e00 0x0984c58cc1b018e0 0x380c188c1f038c05 0xf380c188c1f038c0

def z329 : W := mkw 0x3fef7eee98018c00 0x43fef7eee98018c0 0xbfffffffd8038c0f 0xfbfffffffd8038c0

def z330 : W := mkw 0x2d80766a80000000 0x42d80766a8000000 0xbf807fffc000000f 0x5bf807fffc000000

def z331 : W := mkw 0x0004800016992000 0x2000480001699200 0x000000001f1c0000 0x0000000001f1c000

def z332 : W := mkw 0x801489957b0fbeba 0x0801489957b0fbeb 0x408f9f8fff1ffffd 0xe408f9f8fff1ffff

def z333 : W := mkw 0x0000090008040820 0x0000009000804082 0x00001f0000000c70 0x400001f0000000c7

def z334 : W := mkw 0x0010000026d24000 0x20010000026d2400 0x0000000027e00000 0x00000000027e0000

def z335 : W := mkw 0x0014000032030000 0x0001400003203000 0x000000003f038000 0x2000000003f03800

def z336 : W := mkw 0x0000090448040822 0x0000009044804082 0x00001b0cc0000000 0x000001b0cc000000

def z337 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x40801f00181ffc7d 0x640801f00181ffc7

def z338 : W := mkw 0x2fa3762280000000 0x42fa376228000000 0xbf83ff03c000000f 0x5bf83ff03c000000

def z339 : W := mkw 0x433224232062515c 0x0433224232062515 0x4772040320e3f07b 0xa4772040320e3f07

def z340 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbf7264f30000000b 0xdbf7264f30000000

def z341 : W := mkw 0x4332a5b3606ef5fe 0x04332a5b3606ef5f 0xc7f3e7f3e0fffffb 0xec7f3e7f3e0fffff

def z342 : W := mkw 0x2480000004900000 0x0248000000490000 0x388000001f1c0004 0x1388000001f1c000

def z343 : W := mkw 0x1848504800000000 0x0184850480000000 0x380c180c00000004 0x1380c180c0000000

def z344 : W := mkw 0xbffffefebfdbee80 0x6bffffefebfdbee8 0xffffffffffffff8f 0xfffffffffffffff8

def z345 : W := mkw 0x2fa3ff000dfc6b60 0x32fa3ff000dfc6b6 0xff83ff003ffc7fff 0x7ff83ff003ffc7ff

def z346 : W := mkw 0x0004800010092000 0x0000480001009200 0x40000000181ff000 0x240000000181ff00

def z347 : W := mkw 0x34c9000006900000 0x234c900000690000 0x3800000007000000 0x1380000000700000

def z348 : W := mkw 0x185c58003b030a00 0x0185c58003b030a0 0xb87c78003f038f87 0xfb87c78003f038f8

def z349 : W := mkw 0x0810589029028e80 0x00810589029028e8 0xb87078f03f038f87 0xfb87078f03f038f8

def z350 : W := mkw 0x34dc000036930000 0x034dc00003693000 0x7ffc00003fff800f 0xb7ffc00003fff800

def z351 : W := mkw 0x411024b3202295dc 0x0411024b3202295d 0x807064f320038ff3 0xe807064f320038ff

def z352 : W := mkw 0x25802f000cb40960 0x125802f000cb4096 0x47801f0018fc0c7d 0x647801f0018fc0c7

def z353 : W := mkw 0x423200912062d5dc 0x0423200912062d5d 0x4772000020e3fffb 0xa4772000020e3fff

def z354 : W := mkw 0xd27e00ff3243d49c 0x0d27e00ff3243d49 0x007e00ff0003f000 0x8007e00ff0003f00

def z355 : W := mkw 0x3eeb524880000000 0x43eeb52488000000 0x3fff9b0cc000000f 0x93fff9b0cc000000

def z356 : W := mkw 0x0000010000040020 0x0000001000004002 0x40800700001c0078 0x040800700001c007

def z357 : W := mkw 0x00008901480c383a 0x000008901480c383 0x40839f03d81c7c7d 0x640839f03d81c7c7

def z358 : W := mkw 0x09007f8549249f7a 0x109007f8549249f7 0x80007f8fc0000ff0 0x480007f8fc0000ff

def z359 : W := mkw 0x3ffb766aa6d24000 0x63ffb766aa6d2400 0xbfffffffe7e0000f 0xdbfffffffe7e0000

def z360 : W := mkw 0x67b227b324f6d5fc 0x167b227b324f6d5f 0xc7f267f320fffffb 0xec7f267f320fffff

def z361 : W := mkw 0x2580270004b40160 0x12580270004b4016 0x7f8007003ffc007f 0x37f8007003ffc007

def z362 : W := mkw 0x41002db748249dfe 0x041002db748249df 0x80007fffc0000ff0 0x480007fffc0000ff

def z363 : W := mkw 0x36fb000026d24000 0x236fb000026d2400 0x7f72000027e3f00b 0xb7f72000027e3f00

def z364 : W := mkw 0xbeffd05837db6280 0x2beffd05837db628 0xffffe0703ffff38f 0xbffffe0703ffff38

def z365 : W := mkw 0x36fb000020424000 0x036fb00002042400 0x7fff800020e3f00f 0xb7fff800020e3f00

def z366 : W := mkw 0x0004800010092000 0x0000480001009200 0x000f80000003f000 0x8000f80000003f00

def z367 : W := mkw 0x00008101400c303a 0x000008101400c303 0x40000000001c7070 0x040000000001c707

def z368 : W := mkw 0x0000009000008480 0x0000000900000848 0x800060f000000f80 0x4800060f000000f8

def z369 : W := mkw 0x43322433206251dc 0x043322433206251d 0xc772647320e073fa 0x0c772647320e073f

def z370 : W := mkw 0x423200b32062d5dc 0x0423200b32062d5d 0x407200f320e3fff0 0xa407200f320e3fff

def z371 : W := mkw 0x36ff806ab6db6000 0x636ff806ab6db600 0x7fff80fffffff00f 0xb7fff80fffffff00

def z372 : W := mkw 0xc3362cb73b63dfdc 0x0c3362cb73b63dfd 0xc77264f33fe3fffb 0xec77264f33fe3fff

def z373 : W := mkw 0x41002432002001c4 0x041002432002001c 0x8000607000000380 0x0800060700000038

def z374 : W := mkw 0x2481020080000000 0x4248102008000000 0x00818300c0000000 0x000818300c000000

def z375 : W := mkw 0x0000088408008c00 0x00000088408008c0 0x0000188c00000c00 0x40000188c00000c0

def z376 : W := mkw 0x00008100400c2022 0x000008100400c202 0x00818300c01c0000 0x000818300c01c000

def z377 : W := mkw 0x3eeb504800000000 0x03eeb50480000000 0xbffff8fc0000000f 0xdbffff8fc0000000

def z378 : W := mkw 0x410024b3002095dc 0x0410024b3002095d 0xc00264f30003fff9 0xec00264f30003fff

def z379 : W := mkw 0x3feb766a85b00340 0x53feb766a85b0034 0xbf70607027e00382 0x1bf70607027e0038

def z380 : W := mkw 0x2fa2762200000000 0x02fa276220000000 0xbff27ff30000000f 0xdbff27ff30000000

def z381 : W := mkw 0x2480030004940020 0x1248003000494002 0x00800300001c0000 0x000800300001c000

def z382 : W := mkw 0x985cd8dc3b0bae80 0x0985cd8dc3b0bae8 0xf8fff8fc3f1fff8f 0xff8fff8fc3f1fff8

def z383 : W := mkw 0x995c7fdc3b278fe0 0x1995c7fdc3b278fe 0xb87c7ffc3f038ff7 0xfb87c7ffc3f038ff

def z384 : W := mkw 0x0100262280000000 0x4010026228000000 0x00000703c0000000 0x000000703c000000

def z385 : W := mkw 0x27a3262280000000 0x427a326228000000 0x87f3e7f3c000000b 0xc87f3e7f3c000000

def z386 : W := mkw 0x40148995786ffdfe 0x040148995786ffdf 0x408f9f8ff8fffffd 0xe408f9f8ff8fffff

def z387 : W := mkw 0x400000010060515c 0x0400000010060515 0x4000000000e07070 0x04000000000e0707

def z388 : W := mkw 0x0000090008040820 0x0000009000804082 0x00801b00181c0004 0x000801b00181c000

def z389 : W := mkw 0x880458dc19018e80 0x0880458dc19018e8 0x800c78fc18038f85 0xe800c78fc18038f8

def z390 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb8ffffffff038f8f 0xfb8ffffffff038f8

def z391 : W := mkw 0x0004800450092002 0x0000480045009200 0x000d800cc0000000 0x0000d800cc000000

def z392 : W := mkw 0x126b000000000000 0x0126b00000000000 0x007f800000000000 0x8007f80000000000

def z393 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0x380c180c3f038f84 0x3380c180c3f038f8

def z394 : W := mkw 0x4232003220424084 0x0423200322042408 0x0070007000000000 0x0007000700000000

def z395 : W := mkw 0x3cc9524880000000 0x43cc952488000000 0x3800000000000000 0x1380000000000000

def z396 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0x807c78fc00038f80 0xc807c78fc00038f8

def z397 : W := mkw 0x26a3800004d86000 0x226a3800004d8600 0x7f8380003ffc700f 0x37f8380003ffc700

def z398 : W := mkw 0xad807fdc0db48fe0 0x1ad807fdc0db48fe 0xff807ffc3ffc0fff 0x7ff807ffc3ffc0ff

def z399 : W := mkw 0x2580a70144bc317a 0x12580a70144bc317 0x47838703c0fc7078 0x047838703c0fc707

def z400 : W := mkw 0x411024912062d5dc 0x0411024912062d5d 0xc700640020e3fffb 0x6c700640020e3fff

def z401 : W := mkw 0x2d807f0009240b60 0x12d807f0009240b6 0xbf807f0000000fff 0x5bf807f0000000ff

def z402 : W := mkw 0xbfef7e6e9b010a00 0x4bfef7e6e9b010a0 0xbfffffffdf00000f 0xdbfffffffdf00000

def z403 : W := mkw 0x433224b22062c5c4 0x0433224b22062c5c 0x877060f020e38f83 0xe877060f020e38f8

def z404 : W := mkw 0x0004080418010800 0x0000408041801080 0x000c180c18000004 0x0000c180c1800000

def z405 : W := mkw 0x27a3272284b40160 0x527a3272284b4016 0x47838703c0fc0078 0x047838703c0fc007

def z406 : W := mkw 0x9a7e58dc3b43ce80 0x09a7e58dc3b43ce8 0xff7e78fc3fe3ff8f 0xfff7e78fc3fe3ff8

def z407 : W := mkw 0x3dc87f480db40b60 0x13dc87f480db40b6 0xfffc7ffc3ffc0fff 0xffffc7ffc3ffc0ff

def z408 : W := mkw 0x36ff000032030000 0x036ff00003203000 0x3fff80003f03800f 0xb3fff80003f03800

def z409 : W := mkw 0x023200812042d418 0x0023200812042d41 0x4772048320e3fc7b 0xe4772048320e3fc7

def z410 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff0060003ffc0ff2 0x3ff0060003ffc0ff

def z411 : W := mkw 0x904c004c12010000 0x0904c004c1201000 0x000c000c00000000 0x0000c000c0000000

def z412 : W := mkw 0x0000090008040820 0x0000009000804082 0x40000000181c0c70 0x240000000181c0c7

def z413 : W := mkw 0x985c59dc3b078ea0 0x0985c59dc3b078ea 0xf8fc7ffc3f1f8fff 0xff8fc7ffc3f1f8ff

def z414 : W := mkw 0x02368000304b6000 0x002368000304b600 0x47ff800038fff00f 0xa47ff800038fff00

def z415 : W := mkw 0x0800580009000a00 0x00800580009000a0 0x8000780000000f80 0x48000780000000f8

def z416 : W := mkw 0x984858dc09008e80 0x0984858dc09008e8 0xb87c78fc00000f87 0xdb87c78fc00000f8

def z417 : W := mkw 0x26a3810144dc703a 0x226a3810144dc703 0x47838703c0fc7078 0x047838703c0fc707

def z418 : W := mkw 0x0004800010092000 0x0000480001009200 0x408f9f8fd81ff00d 0xe408f9f8fd81ff00

def z419 : W := mkw 0x0100240000200140 0x0010024000020014 0x8000640000000ff0 0x48000640000000ff

def z420 : W := mkw 0x0014089438038c80 0x00014089438038c8 0x807c78fc38038f87 0xe807c78fc38038f8

def z421 : W := mkw 0x104c000012010000 0x0104c00001201000 0x380c00001f000004 0x1380c00001f00000

def z422 : W := mkw 0x27a3a70004fc6160 0x327a3a70004fc616 0x4783870000fc7078 0x04783870000fc707

def z423 : W := mkw 0x0100248100209558 0x0010024810020955 0xc702648320e3fffb 0xec702648320e3fff

def z424 : W := mkw 0x2494800036db6000 0x22494800036db600 0x7f8000003ffff00f 0x37f8000003ffff00

def z425 : W := mkw 0x127f8085724bf41a 0x2127f8085724bf41 0x007f808fc003f000 0x8007f808fc003f00

def z426 : W := mkw 0x0000080009000a00 0x00000080009000a0 0x000000003f000f80 0x2000000003f000f8

def z427 : W := mkw 0x34cd800016992000 0x234cd80001699200 0x7f8d80003ffc000f 0x37f8d80003ffc000

def z428 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x408f8000181ffc7d 0xa408f8000181ffc7

def z429 : W := mkw 0x43322432206241c4 0x043322432206241c 0xc772607020e3f38b 0xac772607020e3f38

def z430 : W := mkw 0xbfff7ffebfb78fe0 0x5bfff7ffebfb78fe 0xffffffffffff8fff 0xfffffffffffff8ff

def z431 : W := mkw 0x00008101400c303a 0x000008101400c303 0x408f9f8fc01c707d 0xc408f9f8fc01c707

def z432 : W := mkw 0x36eb800004d86000 0x236eb800004d8600 0x7fff800000fc700f 0x97fff800000fc700

def z433 : W := mkw 0x2d80760000000000 0x02d8076000000000 0xbf00600000000002 0x1bf0060000000000

def z434 : W := mkw 0x6fb2763225f243c4 0x16fb2763225f243c 0xbf70607027e00382 0x1bf70607027e0038

def z435 : W := mkw 0xbcddd8dc3f9bae80 0x2bcddd8dc3f9bae8 0xb8fdf8fc3f1f8f87 0xfb8fdf8fc3f1f8f8

def z436 : W := mkw 0x0322242200000000 0x0032224220000000 0x0702040300000008 0x0070204030000000

def z437 : W := mkw 0x0004800010092000 0x0000480001009200 0x008d8000181c0004 0x0008d8000181c000

def z438 : W := mkw 0x985c50dc32038480 0x0985c50dc3203848 0xb87c78fc00038007 0xdb87c78fc0003800

def z439 : W := mkw 0x537e24b33263d5dc 0x0537e24b33263d5d 0xff7e64f33fe3ffff 0xfff7e64f33fe3fff

def z440 : W := mkw 0x8010001023020280 0x0801000102302028 0x0000000027000380 0x0000000002700038

def z441 : W := mkw 0x3febf66a84d86000 0x63febf66a84d8600 0xffffffffc0fc700f 0xdffffffffc0fc700

def z442 : W := mkw 0x3ccddbcdd80dbc3a 0x43ccddbcdd80dbc3 0x788f9f8fd81ffc7d 0xf788f9f8fd81ffc7

def z443 : W := mkw 0x127f8000324b6000 0x2127f8000324b600 0x40ff8000181ff00d 0xa40ff8000181ff00

def z444 : W := mkw 0x3ffb76faa0028480 0x43ffb76faa002848 0xbfffffffe0038f8f 0xfbfffffffe0038f8

def z445 : W := mkw 0x2d84ff855dbdbf7a 0x12d84ff855dbdbf7 0xff807f003fffffff 0x7ff807f003ffffff

def z446 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xb8807f001f1c0ff4 0x5b8807f001f1c0ff

def z447 : W := mkw 0x43322432206241c4 0x043322432206241c 0xc770647020e00ffb 0x6c770647020e00ff

def z448 : W := mkw 0x0000090009240b60 0x10000090009240b6 0x0000000000000ff0 0x00000000000000ff

def z449 : W := mkw 0x2c805b000d940a20 0x12c805b000d940a2 0xb8807b003f1c0f87 0x7b8807b003f1c0f8

def z450 : W := mkw 0xbeff58dc3fd3ce80 0x2beff58dc3fd3ce8 0xbf7c78fc3fe38f87 0xfbf7c78fc3fe38f8

def z451 : W := mkw 0x4336adb7786ffdfe 0x04336adb7786ffdf 0xc77264f338fffffb 0xec77264f338fffff

def z452 : W := mkw 0x7ffff6fbb6fbf5dc 0x67ffff6fbb6fbf5d 0xffffffffffffffff 0xffffffffffffffff

def z453 : W := mkw 0x401000912062d5dc 0x0401000912062d5d 0xc07060f020e3fff3 0xec07060f020e3fff

def z454 : W := mkw 0x0900760001200340 0x1090076000120034 0x8000600000000380 0x0800060000000038

def z455 : W := mkw 0x1848584809000a00 0x01848584809000a0 0xb87c78fc3f000f87 0xfb87c78fc3f000f8

def z456 : W := mkw 0xd85c58dd3b63dfdc 0x0d85c58dd3b63dfd 0xf87c78fc3fe3fff7 0xff87c78fc3fe3fff

def z457 : W := mkw 0x3fffffeffedffc3a 0x63fffffeffedffc3 0xfffffffffffffc7f 0xffffffffffffffc7

def z458 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x400c188c181ffc75 0xe400c188c181ffc7

def z459 : W := mkw 0x37ffa622b6db6000 0x637ffa622b6db600 0x7fff8703fffff00f 0xb7fff8703fffff00

def z460 : W := mkw 0x3ffb760027f24340 0x33ffb760027f2434 0xbf70600027e00382 0x1bf70600027e0038

def z461 : W := mkw 0x000488841809ac00 0x0000488841809ac0 0x408f988c181ffc0d 0xe408f988c181ffc0

def z462 : W := mkw 0x0100240000200140 0x0010024000020014 0x4700040000e00078 0x04700040000e0007

def z463 : W := mkw 0x36ef800016992000 0x236ef80001699200 0x3fff80001f1c000f 0x93fff80001f1c000

def z464 : W := mkw 0x3ffff66ab6db6000 0x63ffff66ab6db600 0xffffe0703ffff00f 0xbffffe0703ffff00

def z465 : W := mkw 0xfffffcff3ffbffdc 0x2fffffcff3ffbffd 0xfffffcff3fffffff 0xffffffcff3ffffff

def z466 : W := mkw 0x0000090008040820 0x0000009000804082 0x408f9f8fd81c0c7d 0xe408f9f8fd81c0c7

def z467 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x40020483181ffc79 0xe40020483181ffc7

def z468 : W := mkw 0x00048984580dac22 0x000048984580dac2 0x008d9b8cd81f8c05 0xe008d9b8cd81f8c0

def z469 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xbf007f0027e00ff2 0x5bf007f0027e00ff

def z470 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7f7000003ffff002 0x37f7000003ffff00

def z471 : W := mkw 0xbccdd84c1f992a00 0x2bccdd84c1f992a0 0x388d980c1f1c0004 0x1388d980c1f1c000

def z472 : W := mkw 0x2d807f854db49f7a 0x12d807f854db49f7 0xff807f8ffffc0fff 0x7ff807f8ffffc0ff

def z473 : W := mkw 0x6d907f912df6dffc 0x16d907f912df6dff 0xff807f003fffffff 0x7ff807f003ffffff

def z474 : W := mkw 0x4326ada7586dfd7e 0x04326ada7586dfd7 0x478f9f8fd8fffc7d 0xe478f9f8fd8fffc7

def z475 : W := mkw 0x4336a4b7706bf5de 0x04336a4b7706bf5d 0xc77fe4ffe0e3fffb 0xec77fe4ffe0e3fff

def z476 : W := mkw 0xda7e58ff3b43de9c 0x0da7e58ff3b43de9 0xb87e78ff3f03ff87 0xfb87e78ff3f03ff8

def z477 : W := mkw 0x2584af855cbdbd7a 0x12584af855cbdbd7 0x478f9f8fd8fffc7d 0xe478f9f8fd8fffc7

def z478 : W := mkw 0x8000089409008e80 0x08000089409008e8 0x0000000000000f80 0x00000000000000f8

def z479 : W := mkw 0x023200902042c480 0x0023200902042c48 0xc77260f020e3ff8b 0xec77260f020e3ff8

def z480 : W := mkw 0x36ff88843edbec00 0x236ff88843edbec0 0x7fff988c3ffffc0f 0xf7fff988c3ffffc0

def z481 : W := mkw 0x422200230040501c 0x0422200230040501 0x0002000300007000 0x0000200030000700

def z482 : W := mkw 0x02368985784ffc3a 0x002368985784ffc3 0x47ff9f8ff8fffc7f 0xe47ff9f8ff8fffc7

def z483 : W := mkw 0x37ffa42236db6000 0x237ffa42236db600 0xffffe4f33ffff00f 0xfffffe4f33ffff00

def z484 : W := mkw 0x127b000022424000 0x2127b00002242400 0x0070000000000000 0x0007000000000000

def z485 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0x807264f30003fff0 0xc807264f30003fff

def z486 : W := mkw 0x7ffb76fba042d49c 0x47ffb76fba042d49 0xbfffffffc003f00f 0xdbfffffffc003f00

def z487 : W := mkw 0x0100242200000000 0x0010024220000000 0x800064f300000000 0x4800064f30000000

def z488 : W := mkw 0x984cd9cd5b0dbe3a 0x0984cd9cd5b0dbe3 0x788f9f8fdf1ffc7d 0xf788f9f8fdf1ffc7

def z489 : W := mkw 0x0000008000008400 0x0000000800000840 0x0000008000038c01 0xe0000008000038c0

def z490 : W := mkw 0x2d907f902db68fe0 0x12d907f902db68fe 0xfff07ff03fff8fff 0xffff07ff03fff8ff

def z491 : W := mkw 0x0000000000000000 0x0000000000000000 0x4700000020e0000b 0x24700000020e0000

def z492 : W := mkw 0x0904ff85592dbf7a 0x10904ff85592dbf7 0xc08fff8fd81ffffd 0xec08fff8fd81ffff

def z493 : W := mkw 0x3dc9764880000000 0x43dc976488000000 0xbf8dff0cc000000f 0x5bf8dff0cc000000

def z494 : W := mkw 0x2d84ff045dbd2b62 0x12d84ff045dbd2b6 0xff8dff0cfffc0fff 0x7ff8dff0cfffc0ff

def z495 : W := mkw 0x2d84ff85580dbc3a 0x02d84ff85580dbc3 0xff8fff8fd81ffc7f 0xfff8fff8fd81ffc7

def z496 : W := mkw 0x2d847f841db58f60 0x12d847f841db58f6 0xff8c7f8c3fff8fff 0xfff8c7f8c3fff8ff

def z497 : W := mkw 0x105c8000320b2000 0x0105c8000320b200 0x78ff80003f1ff00f 0xb78ff80003f1ff00

def z498 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x40001f8fd81ffc70 0x640001f8fd81ffc7

def z499 : W := mkw 0x4b3276fba062d5dc 0x44b3276fba062d5d 0xc7727fffe0e3fffb 0xec7727fffe0e3fff

def z500 : W := mkw 0x0000800004d86000 0x20000800004d8600 0x4000000000fc7000 0x04000000000fc700

def z501 : W := mkw 0x8800584c09000a00 0x08800584c09000a0 0x0000180c00000000 0x00000180c0000000

def z502 : W := mkw 0x984c584c1b010a00 0x0984c584c1b010a0 0xb80c780c3f000f87 0x7b80c780c3f000f8

def z503 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0x7f801f001ffc007c 0x17f801f001ffc007

def z504 : W := mkw 0x34cd800016992000 0x234cd80001699200 0x788f80001f1ff00d 0xb788f80001f1ff00

def z505 : W := mkw 0x0104ad85582dbd7a 0x00104ad85582dbd7 0xc78fff8ff8ffffff 0xec78fff8ff8fffff

def z506 : W := mkw 0x2c805b000d940a20 0x12c805b000d940a2 0x7f801b003ffc000f 0x37f801b003ffc000

def z507 : W := mkw 0x6fa27f230df45b7c 0x16fa27f230df45b7 0xff827f033ffc7fff 0x7ff827f033ffc7ff

def z508 : W := mkw 0xbdd87f582fb60be0 0x1bdd87f582fb60be 0xfff07f703ffc0fff 0x7fff07f703ffc0ff

def z509 : W := mkw 0x905c00dc32038480 0x0905c00dc3203848 0x807c60fc20038f83 0xe807c60fc20038f8

def z510 : W := mkw 0x8014009432038480 0x0801400943203848 0x0000000000038000 0x0000000000003800

def z511 : W := mkw 0x001489003fff6b60 0x3001489003fff6b6 0x400000003ffffff0 0x2400000003ffffff

def z512 : W := mkw 0x0004000010010000 0x0000400001001000 0x000c000018038005 0xa000c00001803800

def z513 : W := mkw 0x401000912062d5dc 0x0401000912062d5d 0x4002048320e3fff9 0xe4002048320e3fff

def z514 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x000f9f8fc003fc70 0xc000f9f8fc003fc7

def z515 : W := mkw 0x0010009020028480 0x0001000902002848 0x007000f000038000 0x8007000f00003800

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x40800000181c000d 0x240800000181c000

def z517 : W := mkw 0x1048004800000000 0x0104800480000000 0x007c00fc00000000 0x8007c00fc0000000

def z518 : W := mkw 0x00008985480cbc3a 0x000008985480cbc3 0x40839f8fc01c7c78 0x440839f8fc01c7c7

def z519 : W := mkw 0x0000800000082000 0x0000080000008200 0x40838000001c7008 0x040838000001c700

def z520 : W := mkw 0x127f89857a4ffc3a 0x2127f89857a4ffc3 0x40ff9f8fd81ffc7d 0xe40ff9f8fd81ffc7

def z521 : W := mkw 0x36fb000026d24000 0x236fb000026d2400 0x7ff000003ffc000f 0x37ff000003ffc000

def z522 : W := mkw 0x3cc9524880000000 0x43cc952488000000 0x388f9f8fc000000d 0xd388f9f8fc000000

def z523 : W := mkw 0x3febf76bc00c303a 0x43febf76bc00c303 0xffffffffc01c707f 0xdffffffffc01c707

def z524 : W := mkw 0x184cd9cd580dbc3a 0x0184cd9cd580dbc3 0xf8ffffffd81ffc7f 0xff8ffffffd81ffc7

def z525 : W := mkw 0x2d807f0008040820 0x02d807f000804082 0xff807f00181c0c7f 0x7ff807f00181c0c7

def z526 : W := mkw 0xbfff7efebb038e80 0x4bfff7efebb038e8 0xbf7c78fc3f038f87 0xfbf7c78fc3f038f8

def z527 : W := mkw 0x36ff808136dbf418 0x236ff808136dbf41 0x7fff84833ffffc7f 0xf7fff84833ffffc7

def z528 : W := mkw 0x127f800036db6000 0x2127f800036db600 0x407f80003ffff000 0xa407f80003ffff00

def z529 : W := mkw 0x2fa3766a80000000 0x42fa3766a8000000 0x8783ffffc0000008 0x48783ffffc000000

def z530 : W := mkw 0x77fb24b326f2d5dc 0x277fb24b326f2d5d 0xff7264f327e3fffb 0xfff7264f327e3fff

def z531 : W := mkw 0x126f80efd009b41a 0x4126f80efd009b41 0x007f80ffc003f000 0x8007f80ffc003f00

def z532 : W := mkw 0x76ff80b336dbf49c 0x276ff80b336dbf49 0x7fff80f33ffff00f 0xb7fff80f33ffff00

def z533 : W := mkw 0x905c89dd7a0fbcba 0x0905c89dd7a0fbcb 0x40ff9fffd81ffc7d 0xe40ff9fffd81ffc7

def z534 : W := mkw 0x27a3262280000000 0x427a326228000000 0x0700000000000000 0x0070000000000000

def z535 : W := mkw 0x36ef8985580dbc3a 0x036ef8985580dbc3 0x7fff9f8fd81ffc7f 0xf7fff9f8fd81ffc7

def z536 : W := mkw 0x1048000000000000 0x0104800000000000 0x387c000000000007 0x9387c00000000000

def z537 : W := mkw 0x0904ffefd80dbc3a 0x40904ffefd80dbc3 0xc08fffffd81ffc7d 0xec08fffffd81ffc7

def z538 : W := mkw 0x36eb000000000000 0x036eb00000000000 0x3fff9f8fc000000f 0xd3fff9f8fc000000

def z539 : W := mkw 0x4b327cb32962dfdc 0x04b327cb32962dfd 0xff727cf33fe3ffff 0xfff727cf33fe3fff

def z540 : W := mkw 0x36ff809036dbe480 0x236ff809036dbe48 0xffffe0f03fffff8f 0xfffffe0f03fffff8

def z541 : W := mkw 0x00048185500db43a 0x000048185500db43 0x408f878fc01ff078 0x8408f878fc01ff07

def z542 : W := mkw 0x3ffb766aa0424000 0x43ffb766aa042400 0xffffffffe0e3f00f 0xfffffffffe0e3f00

def z543 : W := mkw 0x36ef800016d96000 0x236ef800016d9600 0x7f8f80001ffc700c 0x17f8f80001ffc700

def z544 : W := mkw 0x423689b7784ffcbe 0x0423689b7784ffcb 0x40ff9fffd81ffc7d 0xe40ff9fffd81ffc7

def z545 : W := mkw 0x09007c0009200b40 0x009007c0009200b4 0xff007c003fe00fff 0x7ff007c003fe00ff

def z546 : W := mkw 0x3ccddb4cd80d2822 0x43ccddb4cd80d282 0x388d9b0cd81c0004 0x1388d9b0cd81c000

def z547 : W := mkw 0x432224230060515c 0x0432224230060515 0xc702640320e07ffb 0x6c702640320e07ff

def z548 : W := mkw 0x2d80760004900000 0x02d8076000490000 0xff807f003ffc000f 0x7ff807f003ffc000

def z549 : W := mkw 0xbddc7edc3fb38fc0 0x1bddc7edc3fb38fc 0xbf7c78fc3fe38f87 0xfbf7c78fc3fe38f8

def z550 : W := mkw 0x09007f0009240b60 0x109007f0009240b6 0xc0807f00181c0ffd 0x6c0807f00181c0ff

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x008d9b0cc0000004 0x0008d9b0cc000000

def z552 : W := mkw 0x423200b32042d49c 0x0423200b32042d49 0x807260f32003ff83 0xe807260f32003ff8

def z553 : W := mkw 0x905c80dd720bb49a 0x0905c80dd720bb49 0x007f80ffc003f000 0x8007f80ffc003f00

def z554 : W := mkw 0x0332240020624140 0x0033224002062414 0xc772640020e3fffb 0xec772640020e3fff

def z555 : W := mkw 0x7ffb7ffbadf6dffc 0x57ffb7ffbadf6dff 0xffffffffffffffff 0xffffffffffffffff

def z556 : W := mkw 0x27a7afa7d80dbc3a 0x427a7afa7d80dbc3 0x478f9f8fd81ffc7d 0xe478f9f8fd81ffc7

def z557 : W := mkw 0x2d80760000000000 0x02d8076000000000 0xbf8fff8fc000000f 0xdbf8fff8fc000000

def z558 : W := mkw 0x000001014004103a 0x0000001014004103 0x00000703c0000070 0x000000703c000007

def z559 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x008f9b8fd81ff004 0x8008f9b8fd81ff00

def z560 : W := mkw 0xdb7a747a236243c4 0x0db7a747a236243c 0xbf70607027e00382 0x1bf70607027e0038

def z561 : W := mkw 0x127e000032434000 0x0127e00003243400 0x7f7e00003fe3f00f 0xb7f7e00003fe3f00

def z562 : W := mkw 0x09007f6a89240b60 0x509007f6a89240b6 0x80007fffc0000ff0 0x480007fffc0000ff

def z563 : W := mkw 0x2d80770005b40360 0x12d80770005b4036 0xff80670027fc03fa 0x1ff80670027fc03f

def z564 : W := mkw 0x6fb276b32062d5dc 0x06fb276b32062d5d 0xfff27ff320e3ffff 0xffff27ff320e3fff

def z565 : W := mkw 0x6d807fb30db49ffc 0x16d807fb30db49ff 0xff807ff33ffc0fff 0x7ff807ff33ffc0ff

def z566 : W := mkw 0xbcdc58dc3f938e80 0x0bcdc58dc3f938e8 0xfffc78fc3fff8f8f 0xffffc78fc3fff8f8

def z567 : W := mkw 0x00048900180d2820 0x000048900180d282 0x408f9f00181ffc7d 0xe408f9f00181ffc7

def z568 : W := mkw 0x26a3000000000000 0x026a300000000000 0x0783800000000008 0x0078380000000000

def z569 : W := mkw 0x248009000db40b60 0x1248009000db40b6 0x7f8000003ffc0fff 0x37f8000003ffc0ff

def z570 : W := mkw 0x0000008100009418 0x0000000810000941 0x000200830003f000 0x8000200830003f00

def z571 : W := mkw 0x34cd89045e9d2822 0x234cd89045e9d282 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z572 : W := mkw 0x09007f0009240b60 0x109007f0009240b6 0xc7007f0020e00ffb 0x6c7007f0020e00ff

def z573 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbffdfb7cc0000006 0x1bffdfb7cc000000

def z574 : W := mkw 0x7fffffb33ffffffc 0x37fffffb33ffffff 0xfffffff33fffffff 0xffffffff33ffffff

def z575 : W := mkw 0x00048904580d2822 0x000048904580d282 0x408f9b0cd81ff00d 0xa408f9b0cd81ff00

def z576 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0x477204f300e3f078 0x8477204f300e3f07

def z577 : W := mkw 0x801409943fb78fe0 0x1801409943fb78fe 0x400000003fff8ff0 0x2400000003fff8ff

def z578 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x400f808fd81ffc70 0xa400f808fd81ffc7

def z579 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x008d9f8fd81c0c74 0x4008d9f8fd81c0c7

def z580 : W := mkw 0x3ccddb001f9d2a20 0x33ccddb001f9d2a2 0x388d9b001f1c0004 0x1388d9b001f1c000

def z581 : W := mkw 0x77ffadb77efffdfe 0x277ffadb77efffdf 0xffffffffffffffff 0xffffffffffffffff

def z582 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbfffe0700000000f 0x9bfffe0700000000

def z583 : W := mkw 0x400000b30000949c 0x0400000b30000949 0x000000f300000000 0x0000000f30000000

def z584 : W := mkw 0x3dc8764800000000 0x03dc876480000000 0xbffc7ffc0000000f 0xdbffc7ffc0000000

def z585 : W := mkw 0x25802f000db40b60 0x125802f000db40b6 0x478007003ffc0ff8 0x2478007003ffc0ff

def z586 : W := mkw 0x927f00feb2038480 0x4927f00feb203848 0x007f80ffc0038000 0x8007f80ffc003800

def z587 : W := mkw 0x2d80760005b00340 0x12d80760005b0034 0xff00640027e00ffb 0x7ff00640027e00ff

def z588 : W := mkw 0x3effdb003fdf6a20 0x33effdb003fdf6a2 0x7fff9b003ffff00f 0xb7fff9b003ffff00

def z589 : W := mkw 0x3effd8003fdb6a00 0x23effd8003fdb6a0 0xfffff8003fffff8f 0xffffff8003fffff8

def z590 : W := mkw 0x905c08943b038e80 0x0905c08943b038e8 0x387c00003f038f87 0xb387c00003f038f8

def z591 : W := mkw 0x0000000000000000 0x0000000000000000 0x00801f000000000d 0x400801f000000000

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0x400200000003f009 0xa400200000003f00

def z593 : W := mkw 0x127f8000324b6000 0x2127f8000324b600 0x387f80003f03f007 0xb387f80003f03f00

def z594 : W := mkw 0x984c58dc1b018e80 0x0984c58dc1b018e8 0xb80c78fc1f000f84 0x5b80c78fc1f000f8

def z595 : W := mkw 0x0010000020020000 0x0001000002002000 0x0070000020038003 0xa007000002003800

def z596 : W := mkw 0x37eb262280000000 0x437eb26228000000 0x3fff8703c000000f 0x93fff8703c000000

def z597 : W := mkw 0x0000008100009418 0x0000000810000941 0x0000048300000c70 0x40000048300000c7

def z598 : W := mkw 0x0000000004900000 0x0000000000490000 0x400000003ffc0000 0x2400000003ffc000

def z599 : W := mkw 0x881058dc29028e80 0x0881058dc29028e8 0x807078fc20038f83 0xe807078fc20038f8

def z600 : W := mkw 0x2580260004b00140 0x12580260004b0014 0x0700000000e00000 0x00700000000e0000

def z601 : W := mkw 0x00048904580d2822 0x000048904580d282 0x408d9f0cd81c0c7d 0x6408d9f0cd81c0c7

def z602 : W := mkw 0x000000854000941a 0x0000000854000941 0x0000008fc0000000 0x00000008fc000000

def z603 : W := mkw 0x0232000020424000 0x0023200002042400 0x0770000020e00002 0x00770000020e0000

def z604 : W := mkw 0x36ff89003fff6b60 0x336ff89003fff6b6 0x7fff80003fffffff 0xb7fff80003ffffff

def z605 : W := mkw 0x881458943b038e80 0x0881458943b038e8 0xb80078003f038f87 0x7b80078003f038f8

def z606 : W := mkw 0x0222000000000000 0x0022200000000000 0x077200000000000b 0x8077200000000000

def z607 : W := mkw 0x27a3a62284d86000 0x627a3a62284d8600 0x47838703c0fc7008 0x047838703c0fc700

def z608 : W := mkw 0xcb327cff2962dfdc 0x0cb327cff2962dfd 0xc7727cff20e3fffb 0xec7727cff20e3fff

def z609 : W := mkw 0x801408943b038e80 0x0801408943b038e8 0x000c188c3f038f85 0xe000c188c3f038f8

def z610 : W := mkw 0x1049004880000000 0x4104900488000000 0x000d800cc0000000 0x0000d800cc000000

def z611 : W := mkw 0xbcdd5adcbb038e80 0x4bcdd5adcbb038e8 0xb8fdfbfcff038f87 0xfb8fdfbfcff038f8

def z612 : W := mkw 0x77ffa43236fb61c4 0x277ffa43236fb61c 0xffffe0703ffff38f 0xbffffe0703ffff38

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000040000000c79 0x64000040000000c7

def z614 : W := mkw 0x136b246a80000000 0x4136b246a8000000 0x877fe4ffc000000b 0xc877fe4ffc000000

def z615 : W := mkw 0x126f89efd80dbc3a 0x4126f89efd80dbc3 0x40ff9fffd81ffc7d 0xe40ff9fffd81ffc7

def z616 : W := mkw 0x37eb242200000000 0x037eb24220000000 0xbfffe4f30000000f 0xdbfffe4f30000000

def z617 : W := mkw 0x2580260000000000 0x0258026000000000 0x0780070000000008 0x0078007000000000

def z618 : W := mkw 0x905c08dc3b038e80 0x0905c08dc3b038e8 0x007c00fc3f038f80 0xa007c00fc3f038f8

def z619 : W := mkw 0x26a3000004d04000 0x226a3000004d0400 0x0700000000e00000 0x00700000000e0000

def z620 : W := mkw 0x4b327fb32966dffc 0x14b327fb32966dff 0xc7727ff320e3fffb 0xec7727ff320e3fff

def z621 : W := mkw 0x0010000020424000 0x0001000002042400 0x4000000020e3f000 0x24000000020e3f00

def z622 : W := mkw 0xc01408953b63dfdc 0x0c01408953b63dfd 0x400000003fe3fff0 0x2400000003fe3fff

def z623 : W := mkw 0x0100240000200140 0x0010024000020014 0x8700600020e00382 0x08700600020e0038

def z624 : W := mkw 0x36eb000004900000 0x036eb00000490000 0x7fff80003ffc000f 0xb7fff80003ffc000

def z625 : W := mkw 0x0000010004b40160 0x10000010004b4016 0x4000000000fc0070 0x04000000000fc007

def z626 : W := mkw 0x2fa37f228db40b60 0x52fa37f228db40b6 0xff83ff03fffc0fff 0x7ff83ff03fffc0ff

def z627 : W := mkw 0x36eb000000000000 0x036eb00000000000 0x3f70000000000002 0x13f7000000000000

def z628 : W := mkw 0x880059dd49049eba 0x0880059dd49049eb 0x80007fffc0000ff0 0x480007fffc0000ff

def z629 : W := mkw 0x43322db32866ddfc 0x043322db32866ddf 0xc7f27ff338ffffff 0xec7f27ff338fffff

def z630 : W := mkw 0x36fb000026d24000 0x236fb000026d2400 0x3fff800027e0000f 0x93fff800027e0000

def z631 : W := mkw 0x0222000000404000 0x0022200000040400 0x4702000000e07008 0x04702000000e0700

def z632 : W := mkw 0x00008181400cb43a 0x000008181400cb43 0x40838783c01ffc79 0xe40838783c01ffc7

def z633 : W := mkw 0x4336a4b3306bf5dc 0x04336a4b3306bf5d 0xc7ffe4f338ffffff 0xec7ffe4f338fffff

def z634 : W := mkw 0x43322db76866ddfe 0x043322db76866ddf 0xc7727fffe0e3fffb 0xec7727fffe0e3fff

def z635 : W := mkw 0x3feb776a84b40160 0x53feb776a84b4016 0xffffffffc0fc007f 0xdffffffffc0fc007

def z636 : W := mkw 0x09007f000db40b60 0x109007f000db40b6 0xc0007f003ffc0ff0 0x6c0007f003ffc0ff

def z637 : W := mkw 0x881458dc3b038e80 0x0881458dc3b038e8 0x800078fc3f038f80 0x6800078fc3f038f8

def z638 : W := mkw 0x0332242220424000 0x0033224222042400 0xc77264f320e3f00b 0xec77264f320e3f00

def z639 : W := mkw 0x7ffb76fba062d5dc 0x47ffb76fba062d5d 0xff7264f320e3fffb 0xfff7264f320e3fff

def z640 : W := mkw 0x0322242200200140 0x0032224220020014 0xc77264f320e00ffb 0xec77264f320e00ff

def z641 : W := mkw 0x7feb766b8060515c 0x47feb766b8060515 0xffffffffc0e0707f 0xdffffffffc0e0707

def z642 : W := mkw 0xbeffd84c3fdb6a00 0x2beffd84c3fdb6a0 0x7fff980c3ffff00f 0xb7fff980c3ffff00

def z643 : W := mkw 0xbfffffdc3fffefe0 0x3bfffffdc3fffefe 0xfffffffc3fffffff 0xffffffffc3ffffff

def z644 : W := mkw 0x0000098108049c38 0x00000098108049c3 0x40821f83181ffc7d 0xe40821f83181ffc7

def z645 : W := mkw 0xb6ff80dc36dbe480 0x2b6ff80dc36dbe48 0x7fff80fc3ffff00f 0xb7fff80fc3ffff00

def z646 : W := mkw 0x3feb7fefc8049c3a 0x43feb7fefc8049c3 0xbfffffffc0000c7f 0xdbfffffffc0000c7

def z647 : W := mkw 0x0000080008000800 0x0000008000800080 0x0000180018000c05 0x60000180018000c0

def z648 : W := mkw 0x2d80760000200140 0x02d8076000020014 0xff807f0020e00fff 0x7ff807f0020e00ff

def z649 : W := mkw 0x2480000004900000 0x0248000000490000 0x4780000000fc0008 0x04780000000fc000

def z650 : W := mkw 0xffff7effbb63dfdc 0x4ffff7effbb63dfd 0xffffffffffe3ffff 0xfffffffffffe3fff

def z651 : W := mkw 0x0900766a80000000 0x40900766a8000000 0x8000607000000000 0x0800060700000000

def z652 : W := mkw 0x423200b32042d49c 0x0423200b32042d49 0x477200f320e3f00b 0xa477200f320e3f00

def z653 : W := mkw 0x410024b3002095dc 0x0410024b3002095d 0xc70064f320e00ffb 0x6c70064f320e00ff

def z654 : W := mkw 0xbccd5a4c9b010a00 0x4bccd5a4c9b010a0 0x388d9b0cdf000004 0x1388d9b0cdf00000

def z655 : W := mkw 0x3feb7f6a88040820 0x43feb7f6a8804082 0xffffffffd81c0c7f 0xfffffffffd81c0c7

def z656 : W := mkw 0x26a789855cddfc3a 0x226a789855cddfc3 0x478f9f8fd8fffc7d 0xe478f9f8fd8fffc7

def z657 : W := mkw 0x0004088518019c18 0x00004088518019c1 0x400e1c8f1803fc7d 0xe400e1c8f1803fc7

def z658 : W := mkw 0xbdcc7f4c1fb50b60 0x1bdcc7f4c1fb50b6 0xff8c7f0c3ffc0fff 0x7ff8c7f0c3ffc0ff

def z659 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xbf807b003ffc0386 0x1bf807b003ffc038

def z660 : W := mkw 0x2c805b000db40b60 0x12c805b000db40b6 0x78801b003ffc0ff4 0x378801b003ffc0ff

def z661 : W := mkw 0x40100010206241c4 0x040100010206241c 0x0000000020e00380 0x00000000020e0038

def z662 : W := mkw 0x984cd94c5b0d2a22 0x0984cd94c5b0d2a2 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z663 : W := mkw 0x0223800000486000 0x2022380000048600 0x0003800000007000 0x0000380000000700

def z664 : W := mkw 0x67b326b3a062d5dc 0x467b326b3a062d5d 0xc7f3e7f3e0e3fffb 0xec7f3e7f3e0e3fff

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x380000003f000007 0x3380000003f00000

def z666 : W := mkw 0x401009912df6dffc 0x1401009912df6dff 0x400000003ffffff0 0x2400000003ffffff

def z667 : W := mkw 0x0004098558059c3a 0x00004098558059c3 0x000c1f8fd8038c75 0xe000c1f8fd8038c7

def z668 : W := mkw 0x2fa27f220db40b60 0x12fa27f220db40b6 0xfff27ff33ffc0fff 0xffff27ff33ffc0ff

def z669 : W := mkw 0x01002d000db40b60 0x101002d000db40b6 0xc70064003ffc0ffb 0x6c70064003ffc0ff

def z670 : W := mkw 0x001489857edffc3a 0x2001489857edffc3 0x400000003ffffc70 0x2400000003ffffc7

def z671 : W := mkw 0x0000098548049c3a 0x00000098548049c3 0x40801f8fd81c0c7d 0x640801f8fd81c0c7

def z672 : W := mkw 0x2c84db855d9dbe3a 0x12c84db855d9dbe3 0x788f9f8fdf1ffc7d 0xf788f9f8fdf1ffc7

def z673 : W := mkw 0x0004088418018c00 0x00004088418018c0 0x008f9f8fd8038c0d 0xe008f9f8fd8038c0

def z674 : W := mkw 0x43322432206241c4 0x043322432206241c 0x877264f320e0038b 0xc877264f320e0038

def z675 : W := mkw 0x3cc95b488d940a20 0x53cc95b488d940a2 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z676 : W := mkw 0x36ff89857edffc3a 0x236ff89857edffc3 0x7fff80003ffffc7f 0xb7fff80003ffffc7

def z677 : W := mkw 0x3fffff6abfff6b60 0x73fffff6abfff6b6 0xffffffffffffffff 0xffffffffffffffff

def z678 : W := mkw 0x0222002200000000 0x0022200220000000 0x007200f300000000 0x8007200f30000000

def z679 : W := mkw 0x4104adb7582dbdfe 0x04104adb7582dbdf 0xc08fffffd81ffffd 0xec08fffffd81ffff

def z680 : W := mkw 0x2d80770004b40160 0x12d80770004b4016 0xff807f0000fc007f 0x5ff807f0000fc007

def z681 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x3f7f800027e3f002 0x93f7f800027e3f00

def z682 : W := mkw 0x2d807e000db00b40 0x12d807e000db00b4 0xbf0078003fe00f87 0x7bf0078003fe00f8

def z683 : W := mkw 0xbeff58dc3b038e80 0x0beff58dc3b038e8 0xbffff8fc3f038f8f 0xfbffff8fc3f038f8

def z684 : W := mkw 0x2481800004982000 0x2248180000498200 0x00818000001c0000 0x000818000001c000

def z685 : W := mkw 0x3fefffefddbdbf7a 0x53fefffefddbdbf7 0xffffffffffffffff 0xffffffffffffffff

def z686 : W := mkw 0x1a6b506a80000000 0x41a6b506a8000000 0xb87ff8ffc0000007 0xdb87ff8ffc000000

def z687 : W := mkw 0x0000000000000000 0x0000000000000000 0x008f80000000000d 0x8008f80000000000

def z688 : W := mkw 0x2c80520000000000 0x02c8052000000000 0x38801b0000000004 0x138801b000000000

def z689 : W := mkw 0xbfeb7efe89008e80 0x4bfeb7efe89008e8 0xbfffffffc0000f8f 0xdbfffffffc0000f8

def z690 : W := mkw 0x36ff89003edf6820 0x236ff89003edf682 0x7fff9f003ffffc7f 0xf7fff9f003ffffc7

def z691 : W := mkw 0x0804d985590dbe3a 0x00804d985590dbe3 0xf88fff8fff1fffff 0xff88fff8fff1ffff

def z692 : W := mkw 0x000480811009b418 0x0000480811009b41 0x408f8483181ffc7d 0xe408f8483181ffc7

def z693 : W := mkw 0x4014809136fbf5dc 0x24014809136fbf5d 0x400000003ffffff0 0x2400000003ffffff

def z694 : W := mkw 0x00148000324b6000 0x200148000324b600 0x000000000003f000 0x0000000000003f00

def z695 : W := mkw 0xbefb505827d24280 0x2befb505827d2428 0xbf70607027e00382 0x1bf70607027e0038

def z696 : W := mkw 0x8804d9dd590dbeba 0x08804d9dd590dbeb 0xc08fffffd81ffffd 0xec08fffffd81ffff

def z697 : W := mkw 0x00048905580d383a 0x000048905580d383 0x408f9f0fd81c707c 0x0408f9f0fd81c707

def z698 : W := mkw 0x000480855009b41a 0x0000480855009b41 0x408f808fd81ff00d 0xa408f808fd81ff00

def z699 : W := mkw 0x105c89857a0fbc3a 0x0105c89857a0fbc3 0x78ff9f8fff1ffc7f 0xf78ff9f8fff1ffc7

def z700 : W := mkw 0x2d807e0009000a00 0x02d807e0009000a0 0xbf807f003f000f8f 0x7bf807f003f000f8

def z701 : W := mkw 0xad947f943fb78fe0 0x1ad947f943fb78fe 0xff807f003fff8fff 0x7ff807f003fff8ff

def z702 : W := mkw 0x032224a300009418 0x0032224a30000941 0xc77264f30003fc7b 0xec77264f30003fc7

def z703 : W := mkw 0x7ffffffff86ffdfe 0x47ffffffff86ffdf 0xfffffffff8ffffff 0xffffffffff8fffff

def z704 : W := mkw 0x4322a523406c717e 0x04322a523406c717 0x47838703c0fc7078 0x047838703c0fc707

def z705 : W := mkw 0x3ffff60036db6000 0x23ffff60036db600 0xffffff003ffff00f 0xfffffff003ffff00

def z706 : W := mkw 0x77fb243226f241c4 0x277fb243226f241c 0xbf70607027e00382 0x1bf70607027e0038

def z707 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc77260f320e3fff2 0xac77260f320e3fff

def z708 : W := mkw 0x105c8091320bb498 0x0105c8091320bb49 0xf8ffe4f33f1fffff 0xff8ffe4f33f1ffff

def z709 : W := mkw 0x985850d823028680 0x0985850d82302868 0xb87060f027000f82 0x5b87060f027000f8

def z710 : W := mkw 0x985858dc2b028e80 0x0985858dc2b028e8 0xb87078fc3f000f87 0x7b87078fc3f000f8

def z711 : W := mkw 0x09007f8109249f78 0x109007f8109249f7 0x80007f8300000ff0 0x480007f8300000ff

def z712 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xf8fc78fc3f1f8f8f 0xff8fc78fc3f1f8f8

def z713 : W := mkw 0x3feb766a80200140 0x43feb766a8020014 0xbfffffffe0e0038f 0xdbfffffffe0e0038

def z714 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0xc08fff8ff81fffff 0xec08fff8ff81ffff

def z715 : W := mkw 0x1948766a80000000 0x41948766a8000000 0xb8ffffffc000000f 0xdb8ffffffc000000

def z716 : W := mkw 0x984858dc09008e80 0x0984858dc09008e8 0xb87c78fc3f000f87 0xfb87c78fc3f000f8

def z717 : W := mkw 0x26a7800014d96000 0x226a7800014d9600 0x7f8f80003ffff00f 0xb7f8f80003ffff00

def z718 : W := mkw 0x6eb25bb32dd6debc 0x16eb25bb32dd6deb 0x38f21bf31f1ff004 0x938f21bf31f1ff00

def z719 : W := mkw 0x26b3800024da6000 0x226b3800024da600 0x7ff380003ffff00f 0xb7ff380003ffff00

def z720 : W := mkw 0x67a3272384f4517c 0x567a3272384f4517 0x47838703c0fc7078 0x047838703c0fc707

def z721 : W := mkw 0x985c59dc3b078ea0 0x0985c59dc3b078ea 0xb8fc7bfc3f1f8f87 0xfb8fc7bfc3f1f8f8

def z722 : W := mkw 0x985c59dc7b078ea2 0x0985c59dc7b078ea 0xb87c7bfcff038f87 0xfb87c7bfcff038f8

def z723 : W := mkw 0x985c50dc33038680 0x0985c50dc3303868 0xb870607027038382 0x1b87060702703838

def z724 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf8fdfbfcff1ffff7 0xff8fdfbfcff1ffff

def z725 : W := mkw 0x801489957fbfbffa 0x1801489957fbfbff 0x400000003ffffff0 0x2400000003ffffff

def z726 : W := mkw 0x985c58dd3b039e98 0x0985c58dd3b039e9 0xb87c7cff3f038ff7 0xfb87c7cff3f038ff

def z727 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c60fc3f038f82 0xbb87c60fc3f038f8

def z728 : W := mkw 0x3eeb526a80000000 0x43eeb526a8000000 0x3fff9bffc000000f 0x93fff9bffc000000

def z729 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf8fff8fc3f1fffff 0xff8fff8fc3f1ffff

def z730 : W := mkw 0x985850d823028680 0x0985850d82302868 0xb870607027038f82 0x3b870607027038f8

def z731 : W := mkw 0x985859582b060aa0 0x0985859582b060aa 0xf8f07f703f1c0fff 0x7f8f07f703f1c0ff

def z732 : W := mkw 0x985c50d833038680 0x0985c50d83303868 0xb87c60f03f038f87 0xfb87c60f03f038f8

def z733 : W := mkw 0x4336ad36786f69e6 0x04336ad36786f69e 0x87fdfb7cf8fc0386 0x087fdfb7cf8fc038

def z734 : W := mkw 0x985c59dc3b078ea0 0x0985c59dc3b078ea 0xf8ffffffff1f8fff 0xff8ffffffff1f8ff

def z735 : W := mkw 0x3feb766a81000200 0x43feb766a8100020 0xbfffffffe700038f 0xdbfffffffe700038

def z736 : W := mkw 0x1b7fff003b6f6b60 0x31b7fff003b6f6b6 0x807fff000003fff0 0xc807fff000003fff

def z737 : W := mkw 0x2d807f480db40b60 0x12d807f480db40b6 0xff807ffc3ffc0fff 0x7ff807ffc3ffc0ff

def z738 : W := mkw 0x433324b3a062d5dc 0x4433324b3a062d5d 0xc773e4f3e0e3fffb 0xec773e4f3e0e3fff

def z739 : W := mkw 0x0914f66ab6db6000 0x60914f66ab6db600 0xc0007ffffffff000 0x6c0007ffffffff00

def z740 : W := mkw 0x985c50dc33038680 0x0985c50dc3303868 0xb87c78fc27038387 0xdb87c78fc2703838

def z741 : W := mkw 0x36fb09856ed6dc3a 0x236fb09856ed6dc3 0x3f701f8fe7e00c72 0x53f701f8fe7e00c7

def z742 : W := mkw 0x2484800014992000 0x0248480001499200 0x7f8000003ffff00f 0x37f8000003ffff00

def z743 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf87e7cff3f1fffff 0xff87e7cff3f1ffff

def z744 : W := mkw 0xdb6e7c6f1b615b5c 0x0db6e7c6f1b615b5 0x7f0e1c0f1fe0707c 0x17f0e1c0f1fe0707

def z745 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc7f27ff320e3ffff 0xec7f27ff320e3fff

def z746 : W := mkw 0x248009000db40b60 0x1248009000db40b6 0x7f0000003ffc0ff2 0x37f0000003ffc0ff

def z747 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbfffffffe0000f8f 0xfbfffffffe0000f8

def z748 : W := mkw 0x2d807c000db00b40 0x02d807c000db00b4 0xff807c003ffc0fff 0x7ff807c003ffc0ff

def z749 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7f7200003ffff00b 0xb7f7200003ffff00

def z750 : W := mkw 0x136b246a80000000 0x4136b246a8000000 0x87ffffffc000000f 0xc87ffffffc000000

def z751 : W := mkw 0x3cc9524880000000 0x43cc952488000000 0xb8ffffffc000000f 0xdb8ffffffc000000

def z752 : W := mkw 0x985cd8dc3b4bee80 0x2985cd8dc3b4bee8 0xb87c78fc3f03ff87 0xfb87c78fc3f03ff8

def z753 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7f8f80003ffff00c 0x37f8f80003ffff00

def z754 : W := mkw 0x985cd0dd730bb69a 0x0985cd0dd730bb69 0xb87fe0ffe703f382 0x9b87fe0ffe703f38

def z755 : W := mkw 0x985850d823028680 0x0985850d82302868 0xb87c78fc27038f87 0xfb87c78fc27038f8

def z756 : W := mkw 0x0810581029020a80 0x00810581029020a8 0xb87078703f000f87 0x7b87078703f000f8

def z757 : W := mkw 0x985cd8dd7b0bbe9a 0x0985cd8dd7b0bbe9 0xf8fff8ffff1fff8f 0xff8fff8ffff1fff8

def z758 : W := mkw 0x37eb266a80000000 0x437eb266a8000000 0x07ff9fffc000000d 0xc07ff9fffc000000

def z759 : W := mkw 0xc9007fff09249ffc 0x1c9007fff09249ff 0x80007fff00000ff0 0x480007fff00000ff

def z760 : W := mkw 0xaea3d8dc0dd8ee80 0x2aea3d8dc0dd8ee8 0xc783f8fc00fc7f88 0x4c783f8fc00fc7f8

def z761 : W := mkw 0x3fefffefd80dbc3a 0x43fefffefd80dbc3 0xff706070181ffc72 0x3ff706070181ffc7

def z762 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xb8fffbffff1fff87 0xfb8fffbffff1fff8

def z763 : W := mkw 0x527f80fbb24bf49c 0x6527f80fbb24bf49 0x007f80ffc003f000 0x8007f80ffc003f00

def z764 : W := mkw 0xad807f4c0db40b60 0x1ad807f4c0db40b6 0xff807f0c3ffc0fff 0x7ff807f0c3ffc0ff

def z765 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0xc0ffffffd81ffc7f 0xec0ffffffd81ffc7

def z766 : W := mkw 0x433224b76062d5de 0x0433224b76062d5d 0xc77264ffe0e3fffb 0xec77264ffe0e3fff

def z767 : W := mkw 0x7cd952d9a062d5dc 0x47cd952d9a062d5d 0x788d9b0ce0e3fff4 0x3788d9b0ce0e3fff

def z768 : W := mkw 0x2480000004900000 0x0248000000490000 0x7f8200003ffff00f 0xb7f8200003ffff00

def z769 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87078703f038f87 0x7b87078703f038f8

def z770 : W := mkw 0x2d84f68555b9b75a 0x12d84f68555b9b75 0xbf0fe08fe7e3f382 0x9bf0fe08fe7e3f38

def z771 : W := mkw 0x49007fb749249ffe 0x149007fb749249ff 0x80007fffc0000ff0 0x480007fffc0000ff

def z772 : W := mkw 0x00048101500d303a 0x000048101500d303 0x408f9f8fd81ff07d 0xe408f9f8fd81ff07

def z773 : W := mkw 0x985c5bdc3b078ea0 0x1985c5bdc3b078ea 0xb87c7bfc3f038f87 0xfb87c7bfc3f038f8

def z774 : W := mkw 0x1058009022028480 0x0105800902202848 0xb87060f027038f83 0xfb87060f027038f8

def z775 : W := mkw 0x985c59dd7b079eba 0x0985c59dd7b079eb 0xf8fc7fffff1f8fff 0xff8fc7fffff1f8ff

def z776 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xffffffffc0000c7f 0xfffffffffc0000c7

def z777 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff9f003ffff00f 0xf7fff9f003ffff00

def z778 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbffffbffc0000006 0x9bffffbffc000000

def z779 : W := mkw 0x09007d0009240b60 0x009007d0009240b6 0xff807f003ffc0fff 0x7ff807f003ffc0ff

def z780 : W := mkw 0x9858d159630e32ba 0x09858d159630e32b 0xf8f3e773e71c73fa 0x1f8f3e773e71c73f

def z781 : W := mkw 0x0814d995790fbeba 0x00814d995790fbeb 0xf8ffffffff1fffff 0xff8ffffffff1ffff

def z782 : W := mkw 0x985858dc2b028e80 0x0985858dc2b028e8 0xb87078fc27038f83 0xfb87078fc27038f8

def z783 : W := mkw 0x801489957fdffeba 0x2801489957fdffeb 0x400000003ffffff0 0x2400000003ffffff

def z784 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xff7264f33fe3ffff 0xfff7264f33fe3fff

def z785 : W := mkw 0x985858dc2b028e80 0x0985858dc2b028e8 0xb87c78fc27000f87 0xdb87c78fc27000f8

def z786 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbfffffffff00000f 0xfbfffffffff00000

def z787 : W := mkw 0x3feb766a86900000 0x63feb766a8690000 0xbfffffffc700000f 0xdbfffffffc700000

def z788 : W := mkw 0x3dc8764800000000 0x03dc876480000000 0xbfffffffc000000f 0xdbfffffffc000000

def z789 : W := mkw 0x0000098108049c38 0x00000098108049c3 0x408f9f8fd81ffc7d 0xe408f9f8fd81ffc7

def z790 : W := mkw 0x126b096a8db40b60 0x5126b096a8db40b6 0x407f80fffffc0ff0 0xa407f80fffffc0ff

def z791 : W := mkw 0x985c58dd3b039e98 0x0985c58dd3b039e9 0xf8ffffffff03ffff 0xff8ffffffff03fff

def z792 : W := mkw 0x36ff8048b6db6000 0x636ff8048b6db600 0x7fff800cfffff00f 0xb7fff800cfffff00

def z793 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x408f9f0fd81ffc7c 0x2408f9f0fd81ffc7

def z794 : W := mkw 0x985859dd6b069eba 0x0985859dd6b069eb 0xb8707fffe7000ff2 0x5b8707fffe7000ff

def z795 : W := mkw 0x126b006a80000000 0x4126b006a8000000 0x007f9fffc0000000 0xc007f9fffc000000

def z796 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff84833ffff00f 0xf7fff84833ffff00

def z797 : W := mkw 0x34dc8000369b2000 0x034dc8000369b200 0x7fff80003ffff00f 0xb7fff80003ffff00

def z798 : W := mkw 0x985cd9dc7b0faea2 0x0985cd9dc7b0faea 0xf8fdfffcff1f8fff 0xff8fdfffcff1f8ff

def z799 : W := mkw 0x00048985590dbe3a 0x000048985590dbe3 0x408f9f8fff1ffffd 0xe408f9f8fff1ffff

def z800 : W := mkw 0x00148995780fbcba 0x000148995780fbcb 0x40000000381ffff0 0x240000000381ffff

def z801 : W := mkw 0x927f80dd724bf49a 0x2927f80dd724bf49 0x007f80ffc003f000 0x8007f80ffc003f00

def z802 : W := mkw 0x1848594809040a20 0x01848594809040a2 0xf8ffffffff1c0fff 0xff8ffffffff1c0ff

def z803 : W := mkw 0x34dd800036db6000 0x234dd800036db600 0x7f8d80003ffff00f 0x37f8d80003ffff00

def z804 : W := mkw 0xb5dc27dc36b785e0 0x1b5dc27dc36b785e 0x47fc07fc00ff8078 0x847fc07fc00ff807

def z805 : W := mkw 0x36ef800016d96000 0x236ef800016d9600 0x7f8f80001ffff00d 0xb7f8f80001ffff00

def z806 : W := mkw 0x7ffb767aa5f243c4 0x57ffb767aa5f243c 0xbf70607027e00382 0x1bf70607027e0038

def z807 : W := mkw 0x985c505833030280 0x0985c50583303028 0xb87060703f038382 0x3b87060703f03838

def z808 : W := mkw 0x2494800036db6000 0x22494800036db600 0x7f0000003ffff002 0x37f0000003ffff00

def z809 : W := mkw 0x985cd8dc3b0bae80 0x0985cd8dc3b0bae8 0xb8fdf8fc3f1f8f87 0xfb8fdf8fc3f1f8f8

def z810 : W := mkw 0x27a3a72284fc6160 0x727a3a72284fc616 0x47838703c0fc7078 0x047838703c0fc707

def z811 : W := mkw 0x985c505833030280 0x0985c50583303028 0xb87c60703f000386 0x1b87c60703f00038

def z812 : W := mkw 0x09007fefc9249f7a 0x509007fefc9249f7 0x80007fffc0000ff0 0x480007fffc0000ff

def z813 : W := mkw 0x185c58483b030a00 0x0185c58483b030a0 0xb87c78fc3f038f87 0xfb87c78fc3f038f8

def z814 : W := mkw 0x1848504801000200 0x0184850480100020 0xb87c78fc27000387 0xdb87c78fc2700038

def z815 : W := mkw 0x248009000db40b60 0x1248009000db40b6 0x7f801f003ffc0fff 0x77f801f003ffc0ff

def z816 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x408f9f8fd81ff07c 0x8408f9f8fd81ff07

def z817 : W := mkw 0x36ff800476db6002 0x236ff800476db600 0x7fff800cfffff00f 0xb7fff800cfffff00

def z818 : W := mkw 0x34cd800016992000 0x234cd80001699200 0x7f8f80003ffff00f 0xb7f8f80003ffff00

def z819 : W := mkw 0x27a32f228cb40960 0x527a32f228cb4096 0x478f9f8fd8fc0c7d 0xe478f9f8fd8fc0c7

def z820 : W := mkw 0x1a6b526a80000000 0x41a6b526a8000000 0x007f9bffc0000000 0x8007f9bffc000000

def z821 : W := mkw 0x9858505823020280 0x0985850582302028 0xb87c60fc27000382 0x9b87c60fc2700038

def z822 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff007f003ffc0ff2 0x7ff007f003ffc0ff

def z823 : W := mkw 0x67a7a4a314f9f55c 0x267a7a4a314f9f55 0x478f848318fffc7d 0xe478f848318fffc7

def z824 : W := mkw 0xd85c58dd3b43de9c 0x0d85c58dd3b43de9 0xb87c78fc3f03ff87 0xfb87c78fc3f03ff8

def z825 : W := mkw 0x75cda4b316b9b5dc 0x275cda4b316b9b5d 0xb88de4f31f1c0ff4 0x5b88de4f31f1c0ff

def z826 : W := mkw 0x3feb766a84900000 0x43feb766a8490000 0xbfffffffe7e0000f 0xdbfffffffe7e0000

def z827 : W := mkw 0x36ff806ab6db6000 0x636ff806ab6db600 0x7fff9ffffffff00f 0xf7fff9ffffffff00

def z828 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbffdffffc0000006 0x5bffdffffc000000

def z829 : W := mkw 0x1848584809000a00 0x01848584809000a0 0xb87078703f000f87 0x7b87078703f000f8

def z830 : W := mkw 0x985cd9dc7b0faea2 0x0985cd9dc7b0faea 0xb8ffffffff1f8f8f 0xfb8ffffffff1f8f8

def z831 : W := mkw 0x36ff802236db6000 0x236ff802236db600 0x7fff80f33ffff00f 0xb7fff80f33ffff00

def z832 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0x87ffffffc0000008 0xc87ffffffc000000

def z833 : W := mkw 0x3eeb504800000000 0x03eeb50480000000 0xbfffffffc000000f 0xdbfffffffc000000

def z834 : W := mkw 0x2d80760004b00140 0x02d80760004b0014 0xff807f003ffc0fff 0x7ff807f003ffc0ff

def z835 : W := mkw 0xc01489957b6ffffe 0x0c01489957b6ffff 0x400000003ffffff0 0x2400000003ffffff

def z836 : W := mkw 0x2490000024d24000 0x02490000024d2400 0x7f8000003ffff00f 0x37f8000003ffff00

def z837 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb8fc7ffc3f038f8f 0xfb8fc7ffc3f038f8

def z838 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7ff380003ffff00a 0x37ff380003ffff00

def z839 : W := mkw 0x27a3262280000000 0x427a326228000000 0x87ffffffc000000f 0xc87ffffffc000000

def z840 : W := mkw 0xa7b72eb6bb038e80 0x4a7b72eb6bb038e8 0x07838703ff038f88 0x207838703ff038f8

def z841 : W := mkw 0x3feb766a84b00140 0x53feb766a84b0014 0xbfffffffc0e0000f 0xdbfffffffc0e0000

def z842 : W := mkw 0x3feb766a85900200 0x53feb766a8590020 0xbfffffffc700000f 0xdbfffffffc700000

def z843 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0x3fff9fffc000000c 0x93fff9fffc000000

def z844 : W := mkw 0x0814589439038e80 0x00814589439038e8 0xb87c78fc3f038f87 0xfb87c78fc3f038f8

def z845 : W := mkw 0x25802d000db40b60 0x125802d000db40b6 0xff8064003ffc0fff 0x7ff8064003ffc0ff

def z846 : W := mkw 0x9858585c2b020a80 0x09858585c2b020a8 0xb870787c27000382 0x1b870787c2700038

def z847 : W := mkw 0x184cd9cd590dbe3a 0x0184cd9cd590dbe3 0xf8ffffffff1fffff 0xff8ffffffff1ffff

def z848 : W := mkw 0x985c585c3b030a80 0x0985c585c3b030a8 0xb87c78fc3f000387 0xdb87c78fc3f00038

def z849 : W := mkw 0x49007ffb89249ffc 0x549007ffb89249ff 0x80007fffc0000ff0 0x480007fffc0000ff

def z850 : W := mkw 0x3feb766a81200340 0x53feb766a8120034 0xbfffffffc000038f 0xdbfffffffc000038

def z851 : W := mkw 0x9858505823020280 0x0985850582302028 0xb870787027000387 0x5b87078702700038

def z852 : W := mkw 0x3feb766a85b00340 0x53feb766a85b0034 0xfffffffffffc038f 0xffffffffffffc038

def z853 : W := mkw 0x0810501021020280 0x0081050102102028 0xb870607027000382 0x1b87060702700038

def z854 : W := mkw 0xbccdd94c5f9d2a22 0x2bccdd94c5f9d2a2 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z855 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc7727fffe0e3fffb 0xec7727fffe0e3fff

def z856 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff827f833ffc0fff 0xfff827f833ffc0ff

def z857 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf87c7fffff1ffff7 0xff87c7fffff1ffff

def z858 : W := mkw 0x3feb766a84b00140 0x43feb766a84b0014 0xfffffffffffc0fff 0xffffffffffffc0ff

def z859 : W := mkw 0x985858582b020a80 0x0985858582b020a8 0xb87c78fc3f000f87 0xfb87c78fc3f000f8

def z860 : W := mkw 0x67a6afa75cfdfd7e 0x167a6afa75cfdfd7 0x478f9f8fd8fffc7d 0xe478f9f8fd8fffc7

def z861 : W := mkw 0x3ccddb489f9d2a20 0x73ccddb489f9d2a2 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z862 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xb8fdffffff1f8ff7 0xfb8fdffffff1f8ff

def z863 : W := mkw 0x36ff801036db6080 0x236ff801036db608 0xffffe0703ffff38f 0xbffffe0703ffff38

def z864 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff83ff03fffc0fff 0x7ff83ff03fffc0ff

def z865 : W := mkw 0x3feb766a80200140 0x43feb766a8020014 0xffffffffc0e0007f 0xdffffffffc0e0007

def z866 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7f7c00003ffff007 0xb7f7c00003ffff00

def z867 : W := mkw 0x27a7afa7dcbdbd7a 0x527a7afa7dcbdbd7 0x478f9f8fd8fffc7d 0xe478f9f8fd8fffc7

def z868 : W := mkw 0x40148995784ffcbe 0x040148995784ffcb 0x40000000181ffc70 0x240000000181ffc7

def z869 : W := mkw 0x67a2242304f0515c 0x067a2242304f0515 0x4782040300fc7078 0x04782040300fc707

def z870 : W := mkw 0x984c584c1b010a00 0x0984c584c1b010a0 0xb87c78fc3f000f87 0xfb87c78fc3f000f8

def z871 : W := mkw 0x985cd8dd7b0bbe9a 0x0985cd8dd7b0bbe9 0xb8ffffffff03ff8f 0xfb8ffffffff03ff8

def z872 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87ff8ffff038f87 0xfb87ff8ffff038f8

def z873 : W := mkw 0x126b006a80000000 0x4126b006a8000000 0x00ff9bffc0000004 0x800ff9bffc000000

def z874 : W := mkw 0x985c505833030280 0x0985c50583303028 0xb87c607027038382 0x9b87c60702703838

def z875 : W := mkw 0x985c585c3b030a80 0x0985c585c3b030a8 0xb87c787c3f038387 0xbb87c787c3f03838

def z876 : W := mkw 0x2480000004b00140 0x02480000004b0014 0x7f8000003ffc0fff 0x37f8000003ffc0ff

def z877 : W := mkw 0x2d817f008db40b60 0x52d817f008db40b6 0xff81ff00fffc0fff 0x7ff81ff00fffc0ff

def z878 : W := mkw 0x27a3a723c4bc317a 0x527a3a723c4bc317 0x47838703c0fc7078 0x047838703c0fc707

def z879 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc7f264f338ffffff 0xec7f264f338fffff

def z880 : W := mkw 0x985858dc2b028e80 0x0985858dc2b028e8 0xb870607027000f82 0x1b870607027000f8

def z881 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87060f03f038f83 0xfb87060f03f038f8

def z882 : W := mkw 0x89007fdd49249ffa 0x189007fdd49249ff 0x80007fffc0000ff0 0x480007fffc0000ff

def z883 : W := mkw 0x985c59dc3b078ea0 0x0985c59dc3b078ea 0xf87c78fc3f1f8ff7 0xff87c78fc3f1f8ff

def z884 : W := mkw 0x36fb000026d24000 0x236fb000026d2400 0x7ff200003ffff00f 0xb7ff200003ffff00

def z885 : W := mkw 0x985c59dd7b079eba 0x0985c59dd7b079eb 0xb87c78fc3f038ff7 0xfb87c78fc3f038ff

def z886 : W := mkw 0x985858582b020a80 0x0985858582b020a8 0xb870787027000f82 0x5b870787027000f8

def z887 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc7f3e7f3e0e3fffb 0xec7f3e7f3e0e3fff

def z888 : W := mkw 0xb6ff804c36db6000 0x2b6ff804c36db600 0x7fff800c3ffff00f 0xb7fff800c3ffff00

def z889 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0xffffe0f03ffff00f 0xfffffe0f03ffff00

def z890 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xf87e78fc3f03ff8f 0xff87e78fc3f03ff8

def z891 : W := mkw 0x2d807f044db40b62 0x12d807f044db40b6 0xff807f0cfffc0fff 0x7ff807f0cfffc0ff

def z892 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff9b0cfffff00f 0xb7fff9b0cfffff00

def z893 : W := mkw 0xd27f80ff324bf49c 0x2d27f80ff324bf49 0x007f80ff0003f000 0x8007f80ff0003f00

def z894 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff807b003ffc0ff6 0x3ff807b003ffc0ff

def z895 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc77e7cff20e3ffff 0xec77e7cff20e3fff

def z896 : W := mkw 0x881458943b038e80 0x0881458943b038e8 0xb87078f03f038f87 0xfb87078f03f038f8

def z897 : W := mkw 0xd27e80ff724bf49e 0x0d27e80ff724bf49 0x007f80ffc003f000 0x8007f80ffc003f00

def z898 : W := mkw 0xbccddb4c1f9d2a20 0x3bccddb4c1f9d2a2 0x388d9b0c1f1c0004 0x1388d9b0c1f1c000

def z899 : W := mkw 0x0800580009000a00 0x00800580009000a0 0xb87078f03f000f87 0xfb87078f03f000f8

def z900 : W := mkw 0x3ccddb4cdd9d2a22 0x53ccddb4cdd9d2a2 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z901 : W := mkw 0x985c58dd7b039e9a 0x0985c58dd7b039e9 0xb87c78ffff038f87 0xfb87c78ffff038f8

def z902 : W := mkw 0x433226b3a062d5dc 0x4433226b3a062d5d 0xc77267f3e0e3fffb 0xec77267f3e0e3fff

def z903 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xfff07ff03ffc0fff 0xffff07ff03ffc0ff

def z904 : W := mkw 0xbcccdb4c5f9d2a22 0x1bcccdb4c5f9d2a2 0x388d9b0cdf1c0004 0x1388d9b0cdf1c000

def z905 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff808ffffff00f 0xb7fff808ffffff00

def z906 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c60703f038f87 0xbb87c60703f038f8

def z907 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xffffffffe0e0000f 0xfffffffffe0e0000

def z908 : W := mkw 0x1b6b766a80000000 0x41b6b766a8000000 0xb87fffffc0000007 0xdb87fffffc000000

def z909 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf87060703f1ffff2 0x3f87060703f1ffff

def z910 : W := mkw 0x184c58cc19018e00 0x0184c58cc19018e0 0xb87c78fc3f038f87 0xfb87c78fc3f038f8

def z911 : W := mkw 0x985c58583b030a80 0x0985c58583b030a8 0xb87c78703f038f87 0xfb87c78703f038f8

def z912 : W := mkw 0x2d807f6a8db40b60 0x52d807f6a8db40b6 0xff8ffffffffc0fff 0xfff8ffffffffc0ff

def z913 : W := mkw 0x67a2262304f0515c 0x167a2262304f0515 0x4702040300e07078 0x04702040300e0707

def z914 : W := mkw 0x1b6b766a80000000 0x41b6b766a8000000 0x877fffffc000000b 0xc877fffffc000000

def z915 : W := mkw 0x36ef800014992000 0x036ef80001499200 0x7fff80003ffff00f 0xb7fff80003ffff00

def z916 : W := mkw 0x985dd8dc3b0bae80 0x2985dd8dc3b0bae8 0xb87df8fc3f038f87 0xfb87df8fc3f038f8

def z917 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0x7f801f003ffc0ffc 0x37f801f003ffc0ff

def z918 : W := mkw 0x985c585c3b030a80 0x0985c585c3b030a8 0xb87c787c3f000f87 0x7b87c787c3f000f8

def z919 : W := mkw 0xb6ff805836db6080 0x2b6ff805836db608 0x7fff80703ffff00f 0xb7fff80703ffff00

def z920 : W := mkw 0x985cd8dc7b0bae82 0x0985cd8dc7b0bae8 0xb87df8fcff038f87 0xfb87df8fcff038f8

def z921 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xffffffffc003f00f 0xfffffffffc003f00

def z922 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc77064f320e3fff2 0x6c77064f320e3fff

def z923 : W := mkw 0x023200912042d498 0x0023200912042d49 0xc77264f320e3fffb 0xec77264f320e3fff

def z924 : W := mkw 0x1848504801000200 0x0184850480100020 0xb870607027000382 0x1b87060702700038

def z925 : W := mkw 0x9858505823020280 0x0985850582302028 0xb87060703f000387 0x3b87060703f00038

def z926 : W := mkw 0x2c8059000db40b60 0x12c8059000db40b6 0xff8078003ffc0fff 0x7ff8078003ffc0ff

def z927 : W := mkw 0x2580270004b40160 0x12580270004b4016 0xff8067003ffc0fff 0x7ff8067003ffc0ff

def z928 : W := mkw 0x67a7ada75cfdfd7e 0x267a7ada75cfdfd7 0x478f9f8fd8fffc7d 0xe478f9f8fd8fffc7

def z929 : W := mkw 0x27a2272204b40160 0x127a2272204b4016 0x4782070300fc0078 0x04782070300fc007

def z930 : W := mkw 0x985c50dc33038680 0x0985c50dc3303868 0xb87c60fc27038f83 0xfb87c60fc27038f8

def z931 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc772647320e3fffa 0x2c772647320e3fff

def z932 : W := mkw 0x7feb766a80604144 0x47feb766a8060414 0xbfffffffc0e0000f 0xdbfffffffc0e0000

def z933 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc7ffe4f320e3ffff 0xec7ffe4f320e3fff

def z934 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xbf807f003ffc0ff6 0x5bf807f003ffc0ff

def z935 : W := mkw 0x3feb766a85b00340 0x53feb766a85b0034 0xffffffffe7e00fff 0xfffffffffe7e00ff

def z936 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc77060f020e3fff3 0xec77060f020e3fff

def z937 : W := mkw 0x105c89957a0fbcba 0x0105c89957a0fbcb 0xf8ffffffff1fffff 0xff8ffffffff1ffff

def z938 : W := mkw 0x26b6800036db6000 0x226b6800036db600 0x7ff200003ffff00f 0xb7ff200003ffff00

def z939 : W := mkw 0x67a3a42204f86144 0x267a3a42204f8614 0x4783800000fc7008 0x04783800000fc700

def z940 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x408f9f8fc01ffc78 0xc408f9f8fc01ffc7

def z941 : W := mkw 0x3eeb526a80000000 0x43eeb526a8000000 0xb8fffbffc0000007 0xdb8fffbffc000000

def z942 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc772607020e3fffb 0xac772607020e3fff

def z943 : W := mkw 0x27a3262284b00140 0x527a3262284b0014 0x0700000000e00000 0x00700000000e0000

def z944 : W := mkw 0x3feb766a84900000 0x43feb766a8490000 0xbfffffffdf1c000f 0xdbfffffffdf1c000

def z945 : W := mkw 0xc9007dff49249ffe 0x0c9007dff49249ff 0x80007fffc0000ff0 0x480007fffc0000ff

def z946 : W := mkw 0x985c59dd3b079eb8 0x0985c59dd3b079eb 0xf8fe7fff3f1fffff 0xff8fe7fff3f1ffff

def z947 : W := mkw 0x2494800036db6000 0x22494800036db600 0x7f8f80003ffff00f 0xb7f8f80003ffff00

def z948 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7ffd80003ffff006 0x37ffd80003ffff00

def z949 : W := mkw 0x36ff804836db6000 0x236ff804836db600 0x7fff80fc3ffff00f 0xb7fff80fc3ffff00

def z950 : W := mkw 0x985c585c3b030a80 0x0985c585c3b030a8 0xb87060703f000382 0x1b87060703f00038

def z951 : W := mkw 0x36eb006a80000000 0x436eb006a8000000 0x3fff9fffc000000f 0xd3fff9fffc000000

def z952 : W := mkw 0x2d807f228db40b60 0x52d807f228db40b6 0xff807f03fffc0fff 0x7ff807f03fffc0ff

def z953 : W := mkw 0x985cd95c7b0f2aa2 0x0985cd95c7b0f2aa 0xb8fdfb7cff1c0386 0x1b8fdfb7cff1c038

def z954 : W := mkw 0x00008181400cb43a 0x000008181400cb43 0x408f9f8fc01ffc7d 0xe408f9f8fc01ffc7

def z955 : W := mkw 0x985858582b020a80 0x0985858582b020a8 0xb87060703f000f82 0x3b87060703f000f8

def z956 : W := mkw 0x80048995590dbeba 0x080048995590dbeb 0x408f9f8fd81ffffd 0xe408f9f8fd81ffff

def z957 : W := mkw 0x00048995580dbcba 0x000048995580dbcb 0xc08fffffd81ffffd 0xec08fffffd81ffff

def z958 : W := mkw 0x033224902062c5c0 0x0033224902062c5c 0xc77264f020e3fffb 0xec77264f020e3fff

def z959 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff8c7f8c3ffc0fff 0xfff8c7f8c3ffc0ff

def z960 : W := mkw 0x09007f8549249f7a 0x109007f8549249f7 0x80007f0000000ff0 0x480007f0000000ff

def z961 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0x877264f320e3fff2 0xc877264f320e3fff

def z962 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff8060003ffc0fff 0x3ff8060003ffc0ff

def z963 : W := mkw 0x985cd9dc3b0faea0 0x0985cd9dc3b0faea 0xf8fffffc3f1fffff 0xff8fffffc3f1ffff

def z964 : W := mkw 0x185858d829028e80 0x0185858d829028e8 0xb87c78fc3f038f87 0xfb87c78fc3f038f8

def z965 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc77264f300e3fff8 0xcc77264f300e3fff

def z966 : W := mkw 0x26b7800036db6000 0x226b7800036db600 0x7f8380003ffff00f 0x37f8380003ffff00

def z967 : W := mkw 0x9858505823020280 0x0985850582302028 0xb87060f027000383 0xdb87060f02700038

def z968 : W := mkw 0x985cd9dc7b0faea2 0x0985cd9dc7b0faea 0xb87c78fc3f1f8f87 0xfb87c78fc3f1f8f8

def z969 : W := mkw 0x25802f000db40b60 0x125802f000db40b6 0x7f8007003ffc0fff 0x37f8007003ffc0ff

def z970 : W := mkw 0xbfeb766a83000200 0x4bfeb766a8300020 0xbfffffffc700000f 0xdbfffffffc700000

def z971 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff8dff0cfffc0fff 0x7ff8dff0cfffc0ff

def z972 : W := mkw 0x3feb766a80404000 0x43feb766a8040400 0xffffffffc0e0700f 0xdffffffffc0e0700

def z973 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x788f9f8fff1ffc7f 0xf788f9f8fff1ffc7

def z974 : W := mkw 0x67a3242304f0515c 0x267a3242304f0515 0x4702040300e07078 0x04702040300e0707

def z975 : W := mkw 0x27a3262284b00140 0x527a3262284b0014 0x07838703c0e00008 0x007838703c0e0000

def z976 : W := mkw 0x985cd8dc3b0bae80 0x0985cd8dc3b0bae8 0xf8ffffffff1fff8f 0xff8ffffffff1fff8

def z977 : W := mkw 0x905c08943b038e80 0x0905c08943b038e8 0xb87c60f03f038f87 0xfb87c60f03f038f8

def z978 : W := mkw 0x000480811009b418 0x0000480811009b41 0x408f9f8fd81ffc7d 0xe408f9f8fd81ffc7

def z979 : W := mkw 0x9858505823020280 0x0985850582302028 0xb870607027038383 0xbb87060702703838

def z980 : W := mkw 0x9858505823020280 0x0985850582302028 0xb87c607027000387 0x9b87c60702700038

def z981 : W := mkw 0x36ff8200b6db6000 0x636ff8200b6db600 0x7fff8300fffff00f 0xb7fff8300fffff00

def z982 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c78fc3f038386 0x9b87c78fc3f03838

def z983 : W := mkw 0x105c08943a038c80 0x0105c08943a038c8 0xb87c78fc3f038f87 0xfb87c78fc3f038f8

def z984 : W := mkw 0x985c505c33030280 0x0985c505c3303028 0xb87c607c27000382 0x1b87c607c2700038

def z985 : W := mkw 0x25802d000cb40960 0x025802d000cb4096 0xff807f003ffc0fff 0x7ff807f003ffc0ff

def z986 : W := mkw 0x881058dc29028e80 0x0881058dc29028e8 0xb87078fc3f038f87 0xfb87078fc3f038f8

def z987 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf8fc7ffc3f1fffff 0xff8fc7ffc3f1ffff

def z988 : W := mkw 0x2c8059000d940a20 0x02c8059000d940a2 0xff807f003ffc0fff 0x7ff807f003ffc0ff

def z989 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff0064003ffc0ffb 0x7ff0064003ffc0ff

def z990 : W := mkw 0x0010009020028480 0x0001000902002848 0xb87060f03f038f87 0xfb87060f03f038f8

def z991 : W := mkw 0x67a2272204f44164 0x167a2272204f4416 0x4780070000fc0078 0x04780070000fc007

def z992 : W := mkw 0x1058001022020080 0x0105800102202008 0xb870607027000382 0x1b87060702700038

def z993 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x478f9f8ff8fffc7f 0xe478f9f8ff8fffc7

def z994 : W := mkw 0x985c58dc3b43ce80 0x0985c58dc3b43ce8 0xf87c78fc3fe3ff87 0xff87c78fc3fe3ff8

def z995 : W := mkw 0x2d807f488db40b60 0x52d807f488db40b6 0xff807f0cfffc0fff 0x7ff807f0cfffc0ff

def z996 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb8fdfbfcff038f87 0xfb8fdfbfcff038f8

def z997 : W := mkw 0x1b6b766a80000000 0x41b6b766a8000000 0x80ffffffc000000d 0xc80ffffffc000000

def z998 : W := mkw 0x01102491202295d8 0x001102491202295d 0xc77264f320e3fffb 0xec77264f320e3fff

def z999 : W := mkw 0x127e8000324b6000 0x0127e8000324b600 0x7fff80003ffff00f 0xb7fff80003ffff00

def z1000 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb8fff8fc3f038f8f 0xfb8fff8fc3f038f8

def z1001 : W := mkw 0x401489957dfffffe 0x1401489957dfffff 0x400000003ffffff0 0x2400000003ffffff

def z1002 : W := mkw 0x7ffb767aa6f241c4 0x67ffb767aa6f241c 0xbf70607027e00382 0x1bf70607027e0038

def z1003 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87e7cff3f038f8f 0xfb87e7cff3f038f8

def z1004 : W := mkw 0x3feb766a84d04000 0x63feb766a84d0400 0xbfffffffc0e0000f 0xdbfffffffc0e0000

def z1005 : W := mkw 0x09007d000db40b60 0x109007d000db40b6 0xff007c003ffc0fff 0x7ff007c003ffc0ff

def z1006 : W := mkw 0x9858505823020280 0x0985850582302028 0xb8ffffffe700038f 0xdb8ffffffe700038

def z1007 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xff7c78fc3fe38f8f 0xfff7c78fc3fe38f8

def z1008 : W := mkw 0x985cd8dd3b0bbe98 0x0985cd8dd3b0bbe9 0xf8fffcff3f1fffff 0xff8fffcff3f1ffff

def z1009 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xbf7fffffc0000002 0xdbf7fffffc000000

def z1010 : W := mkw 0x2fa2762200000000 0x02fa276220000000 0xbfffffffc000000f 0xdbfffffffc000000

def z1011 : W := mkw 0x3feb766a80200140 0x43feb766a8020014 0xbfffffffc0000fff 0xdbfffffffc0000ff

def z1012 : W := mkw 0x0222002200000000 0x0022200220000000 0x00ff9fffc000000d 0xc00ff9fffc000000

def z1013 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff84003ffffc7f 0xf7fff84003ffffc7

def z1014 : W := mkw 0x67a3a62384f8715c 0x667a3a62384f8715 0x47838703c0fc7078 0x047838703c0fc707

def z1015 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7f7f80003ffff002 0xb7f7f80003ffff00

def z1016 : W := mkw 0x985858d82b028e80 0x0985858d82b028e8 0xb87078f03f038f87 0xfb87078f03f038f8

def z1017 : W := mkw 0x67a3a72304fc717c 0x367a3a72304fc717 0x4783870300fc7078 0x04783870300fc707

def z1018 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xf87ff8ffff1ffff7 0xff87ff8ffff1ffff

def z1019 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc77fe4ffe0e3fffb 0xec77fe4ffe0e3fff

def z1020 : W := mkw 0x67a2a72344fc717e 0x167a2a72344fc717 0x47838703c0fc7078 0x047838703c0fc707

def z1021 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87078fc3f038f82 0x7b87078fc3f038f8

def z1022 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c78fc3f000f86 0x5b87c78fc3f000f8

def z1023 : W := mkw 0x185c58903b038e80 0x0185c58903b038e8 0xb87c78f03f038f87 0xfb87c78f03f038f8

def z1024 : W := mkw 0x985c58dd3b039e98 0x0985c58dd3b039e9 0xf87c78fc3f03fff7 0xff87c78fc3f03fff

def z1025 : W := mkw 0x2d807f6a8db40b60 0x52d807f6a8db40b6 0xff807f703ffc0fff 0x7ff807f703ffc0ff

def z1026 : W := mkw 0x985d58dcbb038e80 0x4985d58dcbb038e8 0xb87df8fcff038f87 0xfb87df8fcff038f8

def z1027 : W := mkw 0x185c50d832038480 0x0185c50d83203848 0xb87c78fc3f038f87 0xfb87c78fc3f038f8

def z1028 : W := mkw 0x2c805b000db40b60 0x12c805b000db40b6 0x7f801b003ffc0fff 0x37f801b003ffc0ff

def z1029 : W := mkw 0x27a3272284b40160 0x527a3272284b4016 0x4780070000fc0078 0x04780070000fc007

def z1030 : W := mkw 0x1b6a746a00000000 0x01b6a746a0000000 0xbfffffffc000000f 0xdbfffffffc000000

def z1031 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c78fc1f038f84 0xdb87c78fc1f038f8

def z1032 : W := mkw 0x00048985580dbc3a 0x000048985580dbc3 0x008f9f8fd81ffc74 0xc008f9f8fd81ffc7

def z1033 : W := mkw 0x36fe000036d34000 0x036fe000036d3400 0x7ffe00003ffff00f 0xb7ffe00003ffff00

def z1034 : W := mkw 0x49007f9109249ffc 0x149007f9109249ff 0x80007f0000000ff0 0x480007f0000000ff

def z1035 : W := mkw 0x37eb242200000000 0x037eb24220000000 0xbfffffffc000000f 0xdbfffffffc000000

def z1036 : W := mkw 0x0b22766a80000000 0x40b22766a8000000 0x87ffffffc000000f 0xc87ffffffc000000

def z1037 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c787c3f038f86 0x3b87c787c3f038f8

def z1038 : W := mkw 0x801489957a0fbcba 0x0801489957a0fbcb 0x40000000181ffc70 0x240000000181ffc7

def z1039 : W := mkw 0x985c59dd7b079eba 0x0985c59dd7b079eb 0xf87e7fffff03ffff 0xff87e7fffff03fff

def z1040 : W := mkw 0x0810509021028680 0x0081050902102868 0xb87060f027038f83 0xfb87060f027038f8

def z1041 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff8fff003ffc0fff 0xfff8fff003ffc0ff

def z1042 : W := mkw 0x984c58dc1b018e80 0x0984c58dc1b018e8 0xb87c78fc1f000f87 0xdb87c78fc1f000f8

def z1043 : W := mkw 0x3feb766a84900000 0x43feb766a8490000 0xffffffffc0fc000f 0xdffffffffc0fc000

def z1044 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff80001ffff00c 0x97fff80001ffff00

def z1045 : W := mkw 0x985c59dd7b079eba 0x0985c59dd7b079eb 0xb8ffffffff038fff 0xfb8ffffffff038ff

def z1046 : W := mkw 0x127e800036db6000 0x2127e800036db600 0x7f7e00003ffff00f 0xb7f7e00003ffff00

def z1047 : W := mkw 0x26b6800034db6000 0x026b6800034db600 0x7fff80003ffff00f 0xb7fff80003ffff00

def z1048 : W := mkw 0x43322432206241c4 0x043322432206241c 0xc772647020e3fffb 0xec772647020e3fff

def z1049 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff8067003ffc0ffa 0x3ff8067003ffc0ff

def z1050 : W := mkw 0x985c58dd3b039e98 0x0985c58dd3b039e9 0xb87e78ff3f03ff87 0xfb87e78ff3f03ff8

def z1051 : W := mkw 0x401489957efffdfe 0x2401489957efffdf 0x400000003ffffff0 0x2400000003ffffff

def z1052 : W := mkw 0x905c00dc32038480 0x0905c00dc3203848 0xb87c60fc3f038f87 0xfb87c60fc3f038f8

def z1053 : W := mkw 0x67a3242204f04144 0x267a3242204f0414 0x0700000000e00000 0x00700000000e0000

def z1054 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x3fff80003ffff006 0x93fff80003ffff00

def z1055 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff827f003fffffff 0xfff827f003ffffff

def z1056 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff807f8ffffc0fff 0x7ff807f8ffffc0ff

def z1057 : W := mkw 0x67a22fa30cf4dd7c 0x167a22fa30cf4dd7 0x47821f8318fffc7d 0xe47821f8318fffc7

def z1058 : W := mkw 0x527f8091324bf49c 0x2527f8091324bf49 0x007f80000003f000 0x8007f80000003f00

def z1059 : W := mkw 0x1048004800000000 0x0104800480000000 0x00ff9fffc000000d 0xc00ff9fffc000000

def z1060 : W := mkw 0x423200912062d5dc 0x0423200912062d5d 0xc77260f020e3fffb 0xec77260f020e3fff

def z1061 : W := mkw 0x985cd8dc3b0bae80 0x0985cd8dc3b0bae8 0xb87ff8fc3f03ff87 0xfb87ff8fc3f03ff8

def z1062 : W := mkw 0x985850d923029698 0x0985850d92302969 0xf87264f32703fffb 0xff87264f32703fff

def z1063 : W := mkw 0x3ffb766aa7f24340 0x73ffb766aa7f2434 0xbf70607027e00382 0x1bf70607027e0038

def z1064 : W := mkw 0x985c5adcbb038e80 0x4985c5adcbb038e8 0xb87c7bfcff038f87 0xfb87c7bfcff038f8

def z1065 : W := mkw 0x985858582b020a80 0x0985858582b020a8 0xb87078703f000386 0x1b87078703f00038

def z1066 : W := mkw 0x0000000000000000 0x0000000000000000 0x80ffffffc000000f 0xc80ffffffc000000

def z1067 : W := mkw 0x411024912062d5dc 0x0411024912062d5d 0xc77064f020e3fffb 0xec77064f020e3fff

def z1068 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c78fc27038f82 0xdb87c78fc27038f8

def z1069 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xf87c7cfc3f038fff 0xff87c7cfc3f038ff

def z1070 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7ff000003ffff00f 0x37ff000003ffff00

def z1071 : W := mkw 0x67a3a52344fc717e 0x267a3a52344fc717 0x47838703c0fc7078 0x047838703c0fc707

def z1072 : W := mkw 0x36ff8022b6db6000 0x636ff8022b6db600 0x7fff8003fffff00f 0xb7fff8003fffff00

def z1073 : W := mkw 0x985850d823028680 0x0985850d82302868 0xb87060f027038382 0x9b87060f02703838

def z1074 : W := mkw 0x032224a300209558 0x0032224a30020955 0xc77264f320e3fffb 0xec77264f320e3fff

def z1075 : W := mkw 0x3eeb526a80000000 0x43eeb526a8000000 0x38ff9fffc000000d 0xd38ff9fffc000000

def z1076 : W := mkw 0x985c59dc3b078ea0 0x0985c59dc3b078ea 0xb87c7ffc3f038ff7 0xfb87c7ffc3f038ff

def z1077 : W := mkw 0x00048905580d383a 0x000048905580d383 0x408f9f0fd81ff07d 0xa408f9f0fd81ff07

def z1078 : W := mkw 0x0332242220624140 0x0033224222062414 0xc77264f320e3fffb 0xec77264f320e3fff

def z1079 : W := mkw 0x2d80760005b00340 0x12d80760005b0034 0xff8064003ffc0fff 0x7ff8064003ffc0ff

def z1080 : W := mkw 0x985850dc23028680 0x0985850dc2302868 0xb87060fc27000382 0x1b87060fc2700038

def z1081 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff988c3ffff00f 0xf7fff988c3ffff00

def z1082 : W := mkw 0x36fb000024d24000 0x036fb000024d2400 0x7fff80003ffff00f 0xb7fff80003ffff00

def z1083 : W := mkw 0x3dc9766a80000000 0x43dc9766a8000000 0xb8fdffffc0000007 0xdb8fdffffc000000

def z1084 : W := mkw 0x1a6b506a80000000 0x41a6b506a8000000 0xb8ffffffc000000f 0xdb8ffffffc000000

def z1085 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0x7fff8703fffff00f 0xb7fff8703fffff00

def z1086 : W := mkw 0x76ff803236db6084 0x276ff803236db608 0x7fff80703ffff00f 0xb7fff80703ffff00

def z1087 : W := mkw 0x9858505823020280 0x0985850582302028 0xb87078fc27000382 0x5b87078fc2700038

def z1088 : W := mkw 0x527f80b7724bf49e 0x2527f80b7724bf49 0x007f80ffc003f000 0x8007f80ffc003f00

def z1089 : W := mkw 0x36ff800036db6000 0x236ff800036db600 0xffffe0003fffff8f 0xfffffe0003fffff8

def z1090 : W := mkw 0x985cd8dc3b0bae80 0x0985cd8dc3b0bae8 0xf87c78fc3f1fff87 0xff87c78fc3f1fff8

def z1091 : W := mkw 0x985cd8dd7b0bbe9a 0x0985cd8dd7b0bbe9 0xb87c78fc3f03ff87 0xfb87c78fc3f03ff8

def z1092 : W := mkw 0x2d807f220db40b60 0x12d807f220db40b6 0xff807ff33ffc0fff 0x7ff807ff33ffc0ff

def z1093 : W := mkw 0x985c58dc3b038e80 0x0985c58dc3b038e8 0xb87c7fffff038f87 0xfb87c7fffff038f8

def z1094 : W := mkw 0x00048185500db43a 0x000048185500db43 0x408f9f8fc01ff07d 0xc408f9f8fc01ff07

def z1095 : W := mkw 0x105c001032030080 0x0105c00103203008 0xb87c60703f038387 0xbb87c60703f03838

def z1096 : W := mkw 0x0810599129069eb8 0x00810599129069eb 0xf8f27ff33f1fffff 0xff8f27ff33f1ffff

def z1097 : W := mkw 0x67a2262204f04144 0x167a2262204f0414 0x0700000000e00000 0x00700000000e0000

def z1098 : W := mkw 0x985cd9dc7b0faea2 0x0985cd9dc7b0faea 0xf8fffbfcff1fff8f 0xff8fffbfcff1fff8

def z1099 : W := mkw 0x985cd8dd7b0bbe9a 0x0985cd8dd7b0bbe9 0xf87ffcffff03ffff 0xff87ffcffff03fff

def z1100 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xffffffffd81c000f 0xfffffffffd81c000

def z1101 : W := mkw 0x985c50dc33038680 0x0985c50dc3303868 0xb87c60fc3f038387 0xbb87c60fc3f03838

def z1102 : W := mkw 0x985cd058330b2280 0x0985cd058330b228 0xf8ffe0703f1ff38f 0xbf8ffe0703f1ff38

def z1103 : W := mkw 0x433224b32062d5dc 0x0433224b32062d5d 0xc770647020e3fffb 0x6c770647020e3fff

def z1104 : W := mkw 0x00048900180d2820 0x000048900180d282 0x408f9f8fd81ffc7d 0xe408f9f8fd81ffc7

def z1105 : W := mkw 0x800489855b0dbe3a 0x0800489855b0dbe3 0x408f9f8fdf1ffc7d 0xe408f9f8fdf1ffc7

def z1106 : W := mkw 0x9858505823020280 0x0985850582302028 0xb87c787c27000386 0x1b87c787c2700038

def z1107 : W := mkw 0x985c505833030280 0x0985c50583303028 0xb87c78fc3f038387 0xfb87c78fc3f03838

def z1108 : W := mkw 0x985cd9dd7b0fbeba 0x0985cd9dd7b0fbeb 0xb87fffffff03fff7 0xfb87fffffff03fff

def z1109 : W := mkw 0x36ff806ab6db6000 0x636ff806ab6db600 0x7fff80703ffff00f 0xb7fff80703ffff00

def z1110 : W := mkw 0x2d807f000db40b60 0x12d807f000db40b6 0xff0078003ffc0ff7 0x7ff0078003ffc0ff

def z1111 : W := mkw 0x9858505823020280 0x0985850582302028 0xb870607027000f83 0x7b870607027000f8

def z1112 : W := mkw 0x3feb766a80000000 0x43feb766a8000000 0xb8ffffffc0000004 0xdb8ffffffc000000

def z1113 : W := mkw 0x34dc800036db6000 0x234dc800036db600 0x7ffc00003ffff00f 0xb7ffc00003ffff00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z8,z2,z3,z5,z6])],[(0,[z9,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z11,z5,z10]),(0,[z0,z12,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z13,z14]),(0,[z0,z2,z3,z4,z5,z15,z6])],[(0,[z16,z0,z2,z3,z4,z5,z6]),(0,[z17,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z18]),(0,[z0,z2,z3,z4,z5,z14,z19])],[(0,[z9,z0,z20,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z21,z6]),(0,[z22,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z23,z6]),(0,[z0,z24,z25,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z26,z6])],[(0,[z27,z0,z28,z3,z4,z5,z6]),(0,[z0,z29,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z30]),(0,[z0,z2,z3,z31,z4,z5,z6]),(0,[z0,z2,z3,z32,z4,z5,z6])],[(0,[z0,z2,z3,z33,z4,z5,z6]),(0,[z0,z34,z2,z3,z4,z5,z6])],[(0,[z0,z35,z2,z3,z4,z5,z6]),(0,[z0,z36,z2,z3,z4,z5,z6]),(0,[z0,z37,z2,z3,z4,z5,z14]),(1,[z0,z38,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z39,z6])],[(0,[z40,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z41,z5,z14]),(0,[z0,z42,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z43]),(0,[z0,z2,z44,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z45,z6])]],
   [[(0,[z46,z0,z2,z3,z4,z5,z6]),(0,[z0,z47,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z48,z14]),(0,[z0,z2,z3,z4,z5,z49,z6])],[(0,[z50,z0,z2,z3,z4,z5,z51]),(0,[z0,z3,z4,z5,z48,z6,z52]),(0,[z0,z53,z2,z3,z4,z5,z6])],[(0,[z54,z0,z2,z3,z4,z5,z6]),(0,[z0,z55,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z56,z5,z6]),(0,[z0,z2,z3,z4,z5,z57,z10]),(0,[z0,z58,z2,z3,z4,z5,z6])],[(0,[z0,z59,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z5,z60,z6])],[(0,[z0,z2,z3,z4,z61,z5,z6]),(0,[z0,z1,z2,z3,z4,z5,z10]),(0,[z0,z62,z2,z3,z4,z5,z14]),(1,[z0,z2,z3,z63,z5,z6]),(0,[z0,z64,z2,z3,z4,z5,z6]),(0,[z0,z65,z2,z3,z4,z5,z6])],[(0,[z27,z66,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z67,z6]),(0,[z0,z68,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z69,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z70])],[(0,[z71,z0,z2,z3,z72,z5,z6]),(0,[z0,z2,z73,z3,z4,z5,z6])],[(0,[z0,z2,z74,z3,z4,z5,z6]),(0,[z9,z2,z3,z4,z41,z5,z6]),(0,[z0,z2,z75,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z10]),(0,[z0,z76,z2,z3,z4,z5,z6]),(0,[z0,z77,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z78,z2,z3,z4,z5,z6]),(0,[z79,z0,z80,z3,z4,z5,z6]),(0,[z0,z2,z3,z81,z82,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z83])],[(0,[z0,z20,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z84,z5,z6]),(0,[z0,z85,z2,z3,z4,z5,z6])],[],[(0,[z0,z86,z2,z3,z4,z5,z10]),(1,[z87,z2,z88,z4,z5,z6]),(0,[z89,z0,z2,z3,z4,z5,z6]),(0,[z90,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z91,z6])],[(0,[z92,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z93,z6]),(0,[z0,z2,z94,z3,z4,z5,z6])],[(0,[z0,z2,z95,z3,z4,z5,z6]),(0,[z96,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z97,z5,z6]),(0,[z0,z1,z3,z4,z81,z5,z6]),(0,[z0,z2,z3,z98,z4,z5,z6])],[(0,[z99,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z100,z5,z6])],[(0,[z0,z2,z3,z4,z5,z101,z6]),(0,[z0,z102,z2,z3,z4,z5,z6]),(0,[z0,z103,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z104,z2,z3,z4,z5,z6]),(0,[z0,z105,z2,z3,z4,z5,z6]),(0,[z0,z25,z2,z3,z4,z5,z48])],[(0,[z0,z104,z2,z28,z4,z5,z6]),(0,[z106,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z107]),(0,[z0,z108,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z10]),(0,[z0,z2,z109,z3,z4,z5,z6])],[(0,[z110,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z111,z4,z5,z6]),(0,[z0,z25,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z112,z6])],[(0,[z0,z2,z74,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z113,z5,z6]),(0,[z0,z2,z3,z4,z114,z5,z6]),(0,[z0,z2,z3,z4,z115,z5,z6]),(0,[z0,z2,z3,z4,z5,z116,z6]),(0,[z0,z2,z3,z4,z5,z6,z117]),(0,[z0,z2,z3,z4,z5,z6,z118])],[(0,[z0,z86,z3,z4,z81,z5,z6]),(0,[z0,z119,z120,z3,z4,z5,z6]),(0,[z0,z121,z2,z3,z4,z5,z6]),(0,[z0,z20,z2,z3,z5,z122,z6]),(0,[z0,z2,z3,z4,z123,z5,z6]),(0,[z0,z124,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z125,z126]),(0,[z0,z127,z2,z3,z4,z5,z6])],[(0,[z27,z0,z2,z3,z4,z5,z128]),(0,[z129,z0,z2,z3,z4,z5,z6]),(0,[z0,z20,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z6,z130])],[(0,[z0,z2,z3,z4,z131,z5,z6]),(0,[z0,z2,z3,z4,z5,z132,z6]),(0,[z0,z2,z133,z3,z82,z5,z6]),(0,[z0,z2,z3,z4,z5,z134,z6])],[(1,[z27,z28,z3,z4,z5,z6]),(0,[z0,z135,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z136,z4,z5,z6]),(0,[z0,z137,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z138,z5,z6]),(0,[z0,z2,z3,z4,z5,z139,z6]),(1,[z0,z124,z2,z4,z5,z13]),(0,[z0,z2,z3,z4,z5,z140,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6,z141]),(0,[z0,z12,z2,z74,z4,z5,z6]),(0,[z0,z142,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z143,z5,z6]),(0,[z144,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z145,z3,z4,z5,z6]),(0,[z0,z146,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z147,z5,z6]),(1,[z0,z148,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z82,z5,z6]),(0,[z0,z149,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z150,z4,z5,z6])],[(0,[z0,z2,z3,z4,z151,z5,z6]),(0,[z0,z152,z2,z3,z4,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z14]),(0,[z0,z153,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z154,z5,z6]),(0,[z0,z155,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z156,z5,z6]),(0,[z0,z2,z157,z3,z4,z5,z6]),(0,[z9,z0,z2,z3,z41,z5,z6]),(1,[z0,z2,z3,z4,z5,z158]),(0,[z92,z2,z3,z4,z159,z5,z6]),(0,[z0,z119,z2,z4,z160,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z161])],[(0,[z0,z2,z162,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z163]),(0,[z0,z2,z3,z4,z164,z5,z10]),(0,[z0,z2,z3,z4,z5,z165,z6])],[(0,[z0,z166,z2,z3,z4,z5,z6]),(0,[z106,z0,z2,z3,z4,z5,z10])],[(0,[z0,z167,z2,z3,z4,z5,z14]),(0,[z0,z20,z3,z4,z81,z5,z6]),(0,[z0,z2,z168,z3,z4,z5,z6]),(0,[z0,z2,z169,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z170]),(0,[z0,z2,z3,z4,z5,z6,z171])],[(0,[z0,z2,z3,z172,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z122,z14]),(0,[z173,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z174,z5,z6]),(0,[z0,z175,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z176,z5,z6]),(0,[z0,z177,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z178,z5,z6]),(0,[z0,z124,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z179,z6]),(0,[z0,z2,z3,z4,z5,z6,z180])],[(0,[z0,z2,z3,z4,z5,z6,z181]),(0,[z0,z2,z3,z4,z5,z14,z52]),(0,[z182,z0,z2,z3,z4,z5,z6]),(0,[z183,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z184,z6]),(0,[z0,z185,z2,z3,z4,z5,z6])],[(0,[z0,z28,z3,z4,z81,z5,z6]),(0,[z186,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z187,z4,z5,z6])],[(0,[z0,z188,z2,z3,z4,z5,z6]),(0,[z0,z80,z2,z3,z4,z5,z14]),(0,[z0,z2,z189,z3,z4,z5,z6]),(0,[z0,z2,z3,z190,z4,z5,z6]),(0,[z0,z191,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z192,z6]),(0,[z0,z2,z193,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z194,z6]),(0,[z0,z2,z3,z4,z5,z195,z6]),(0,[z0,z2,z3,z4,z5,z6,z196]),(1,[z0,z2,z3,z4,z5,z197]),(0,[z198,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z199,z4,z5,z6])],[(0,[z0,z200,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z82,z5,z10]),(0,[z0,z200,z1,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z201,z6]),(0,[z0,z2,z3,z202,z5,z122,z6])],[(0,[z9,z0,z2,z3,z4,z5,z197]),(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z204,z6])],[(0,[z27,z0,z86,z3,z4,z5,z6]),(0,[z86,z2,z28,z3,z4,z5,z6]),(0,[z0,z205,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z206,z6]),(0,[z0,z24,z8,z2,z3,z4,z5]),(0,[z207,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z208,z2,z3,z4,z5,z14]),(0,[z0,z12,z2,z133,z4,z5,z6]),(0,[z0,z209,z2,z3,z4,z210,z6])],[(0,[z71,z0,z20,z2,z3,z5,z6]),(0,[z0,z211,z2,z3,z4,z5,z6]),(0,[z0,z2,z212,z4,z210,z5,z6])],[(0,[z0,z2,z3,z213,z4,z5,z6]),(0,[z66,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z214,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z6,z215]),(0,[z0,z2,z3,z4,z5,z216,z6])],[(0,[z0,z217,z2,z3,z4,z5,z14]),(0,[z0,z218,z2,z3,z4,z5,z6])],[(0,[z87,z0,z2,z3,z4,z5,z219]),(0,[z2,z3,z4,z159,z5,z220,z6]),(0,[z0,z2,z3,z4,z5,z221,z14]),(0,[z0,z2,z3,z4,z5,z222,z6]),(0,[z0,z2,z3,z214,z4,z122,z6]),(0,[z0,z2,z3,z4,z125,z5,z6])],[(0,[z27,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z167,z2,z3,z5,z6]),(1,[z223,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z224,z4,z5,z6]),(0,[z0,z2,z3,z4,z225,z5,z6]),(0,[z0,z226,z2,z3,z4,z5,z6])],[(0,[z227,z0,z2,z3,z4,z5,z6]),(0,[z0,z12,z2,z88,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z228]),(0,[z229,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z230,z5,z6]),(0,[z0,z2,z3,z231,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z232]),(0,[z0,z2,z3,z4,z5,z6,z233])]],
   [[(0,[z66,z0,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z234,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z220,z10]),(0,[z0,z2,z3,z4,z11,z5,z6]),(1,[z0,z2,z3,z4,z5,z235]),(0,[z0,z2,z3,z4,z210,z5,z6]),(0,[z0,z2,z236,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z237,z6]),(0,[z0,z238,z2,z3,z4,z5,z6]),(0,[z0,z124,z2,z3,z4,z125,z5]),(0,[z0,z2,z3,z4,z5,z239,z6])],[(0,[z71,z0,z2,z3,z81,z5,z6]),(0,[z0,z2,z3,z240,z4,z5,z6]),(0,[z0,z2,z133,z4,z82,z5,z6]),(0,[z0,z241,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z160,z5,z14]),(0,[z242,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z212,z3,z4,z57,z6]),(0,[z0,z2,z3,z4,z5,z243,z6])],[(0,[z0,z2,z3,z4,z5,z128,z6]),(0,[z0,z2,z244,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z245,z5,z6]),(0,[z0,z12,z1,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z246]),(0,[z0,z120,z3,z4,z11,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z247])],[(1,[z0,z2,z3,z4,z5,z248]),(0,[z0,z2,z3,z4,z249,z5,z6])],[(0,[z250,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z251,z6]),(0,[z0,z252,z1,z2,z3,z5,z6]),(0,[z0,z2,z253,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z254])],[(0,[z9,z0,z2,z3,z4,z255,z6]),(0,[z0,z256,z2,z3,z4,z5,z6]),(0,[z0,z12,z119,z2,z4,z5,z6]),(0,[z0,z257,z2,z3,z4,z5,z6]),(0,[z0,z208,z2,z3,z4,z221,z6]),(0,[z0,z124,z2,z3,z4,z5,z13])]],
   [[(0,[z0,z2,z3,z258,z4,z5,z6])],[(0,[z27,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z220,z122,z6]),(0,[z0,z259,z2,z3,z5,z6,z10]),(0,[z0,z260,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z261,z6]),(0,[z0,z2,z3,z4,z5,z57,z6])],[(0,[z87,z0,z2,z3,z4,z5,z6]),(1,[z0,z119,z120,z4,z5,z6]),(0,[z0,z262,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z263,z6]),(0,[z0,z37,z2,z4,z5,z6,z247])],[(0,[z0,z24,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z264,z5,z6]),(0,[z0,z209,z119,z2,z4,z5,z6]),(0,[z0,z265,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z266,z4,z5,z6]),(0,[z0,z267,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z210,z5,z10]),(0,[z0,z1,z2,z3,z268,z5,z6]),(0,[z0,z269,z2,z3,z4,z5,z6])],[(0,[z71,z0,z2,z3,z202,z5,z6]),(0,[z270,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z271,z5,z6]),(0,[z0,z272,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z125,z5,z273])],[],[(0,[z0,z2,z3,z4,z5,z6,z274]),(0,[z0,z12,z77,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z275,z5,z6]),(0,[z0,z2,z3,z4,z125,z5,z126])]],
   [[(0,[z0,z276,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z277,z5,z6]),(0,[z0,z2,z3,z4,z5,z126,z14]),(0,[z0,z2,z3,z4,z5,z6,z278])],[(0,[z2,z3,z72,z4,z41,z5,z6]),(0,[z0,z2,z3,z279,z4,z5,z6]),(1,[z0,z80,z3,z81,z5,z6]),(0,[z0,z280,z2,z3,z4,z5,z6])],[(0,[z0,z86,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z141]),(0,[z0,z2,z3,z4,z5,z281,z6]),(0,[z0,z2,z3,z4,z5,z6,z282]),(0,[z0,z2,z3,z4,z283,z5,z6]),(0,[z284,z0,z2,z3,z4,z5,z6])],[(0,[z0,z148,z2,z3,z5,z220,z6]),(0,[z0,z8,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z6,z19]),(1,[z0,z24,z3,z4,z5,z52]),(0,[z0,z2,z3,z4,z5,z6,z285])],[(1,[z0,z2,z3,z61,z5,z6]),(1,[z9,z2,z3,z41,z5,z6]),(0,[z0,z2,z286,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z287,z14])],[(0,[z0,z2,z28,z3,z4,z5,z10]),(0,[z0,z288,z2,z3,z4,z5,z6]),(0,[z0,z2,z212,z3,z4,z5,z6]),(0,[z0,z289,z2,z3,z4,z5,z6])],[(0,[z87,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z290,z5,z6]),(0,[z291,z0,z2,z3,z4,z5,z6])],[(1,[z0,z200,z3,z4,z221,z6]),(0,[z0,z2,z3,z4,z202,z5,z6]),(0,[z0,z2,z3,z292,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z293,z6])]],
   [[(0,[z294,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z81,z5,z10]),(0,[z0,z20,z2,z3,z214,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z295])],[(0,[z0,z119,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z296,z14]),(0,[z0,z25,z2,z3,z4,z5,z6]),(0,[z297,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z298,z6]),(0,[z0,z7,z2,z3,z4,z5,z6])],[(0,[z299,z0,z2,z3,z4,z5,z6]),(0,[z0,z260,z124,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z300,z5,z6])],[(0,[z87,z2,z3,z88,z4,z5,z6]),(0,[z0,z301,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z181]),(0,[z0,z2,z3,z4,z5,z5,z6]),(0,[z50,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z302,z6]),(0,[z0,z200,z2,z3,z4,z11,z6]),(0,[z0,z2,z3,z4,z303,z5,z6]),(0,[z304,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z305,z5,z6]),(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z306,z0,z2,z3,z4,z5,z6]),(0,[z22,z2,z3,z4,z5,z6,z10]),(0,[z223,z2,z3,z4,z5,z14,z6]),(0,[z0,z307,z2,z3,z4,z5,z6])],[(0,[z0,z200,z120,z3,z4,z5,z6]),(1,[z79,z0,z20,z3,z5,z6])],[(0,[z0,z308,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z196]),(0,[z0,z309,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z248]),(0,[z0,z310,z2,z3,z4,z5,z14]),(0,[z0,z311,z2,z3,z4,z5,z6])],[(0,[z92,z0,z2,z3,z4,z5,z228]),(0,[z79,z0,z2,z3,z4,z5,z10]),(0,[z0,z142,z2,z3,z4,z5,z6]),(0,[z79,z0,z1,z3,z4,z5,z6]),(0,[z0,z119,z120,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z312,z6]),(0,[z0,z2,z3,z4,z5,z313,z6])]],
   [[(0,[z0,z314,z2,z3,z4,z5,z6]),(0,[z223,z0,z2,z3,z4,z5,z6]),(0,[z0,z315,z2,z3,z4,z5,z14]),(0,[z0,z200,z208,z3,z4,z5,z6]),(0,[z0,z316,z2,z3,z4,z5,z6]),(0,[z0,z317,z2,z3,z4,z5,z6])],[(0,[z0,z318,z2,z3,z4,z5,z6]),(0,[z0,z2,z212,z3,z4,z5,z10]),(0,[z79,z0,z20,z2,z3,z5,z6]),(0,[z0,z167,z2,z3,z4,z202,z6])],[(0,[z106,z0,z2,z88,z4,z5,z6]),(0,[z0,z2,z319,z3,z4,z5,z6]),(0,[z320,z0,z2,z3,z4,z5,z6])],[(0,[z71,z2,z3,z72,z4,z5,z6]),(1,[z0,z2,z3,z113,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z321]),(0,[z0,z2,z3,z4,z164,z5,z6]),(1,[z22,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z202,z5,z10]),(1,[z0,z167,z2,z3,z122,z6]),(0,[z0,z2,z3,z322,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z323]),(0,[z0,z2,z3,z4,z159,z5,z10]),(1,[z0,z2,z3,z4,z5,z14]),(0,[z0,z324,z2,z3,z4,z5,z6]),(0,[z0,z2,z325,z3,z4,z5,z6])],[(0,[z79,z0,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z326,z5,z6]),(0,[z0,z2,z3,z4,z5,z327,z6]),(0,[z0,z2,z3,z4,z5,z328,z6]),(0,[z0,z2,z3,z4,z329,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z10]),(0,[z0,z330,z2,z3,z4,z5,z6]),(0,[z331,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z332,z6])],[(0,[z333,z0,z2,z3,z4,z5,z6]),(0,[z0,z334,z2,z3,z4,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z14]),(0,[z92,z0,z2,z3,z4,z5,z248]),(0,[z0,z12,z2,z3,z4,z5,z14])],[(0,[z0,z335,z2,z3,z4,z5,z6])]],
   [[(0,[z336,z0,z2,z3,z4,z5,z6]),(0,[z106,z0,z1,z2,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z159,z6]),(0,[z0,z1,z3,z4,z160,z5,z6]),(0,[z337,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z338,z3,z4,z5,z6]),(0,[z0,z124,z2,z4,z5,z13,z6]),(0,[z0,z2,z3,z4,z339,z5,z6])],[(0,[z0,z2,z3,z340,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z273]),(0,[z0,z2,z3,z4,z5,z341,z6]),(0,[z0,z342,z2,z3,z4,z5,z6]),(0,[z0,z343,z2,z3,z4,z5,z6])],[(1,[z71,z2,z3,z72,z5,z6]),(0,[z0,z209,z2,z3,z4,z5,z14]),(0,[z79,z0,z2,z3,z81,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z344]),(0,[z0,z2,z345,z3,z4,z5,z6])],[(0,[z66,z0,z86,z3,z4,z5,z6]),(0,[z346,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z347,z3,z4,z5,z6]),(0,[z0,z348,z2,z3,z4,z5,z6])],[(0,[z223,z0,z2,z3,z4,z5,z10]),(0,[z0,z200,z2,z3,z4,z5,z6]),(1,[z0,z349,z2,z3,z4,z5]),(0,[z0,z2,z350,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z351,z5,z6])],[(0,[z0,z352,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z353,z5,z6])],[(0,[z71,z0,z2,z3,z4,z5,z6]),(0,[z0,z37,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z6,z354])],[(0,[z0,z2,z3,z4,z41,z5,z10]),(0,[z0,z2,z3,z355,z4,z5,z6])]],
   [[(0,[z356,z0,z2,z3,z4,z5,z6]),(0,[z357,z0,z2,z3,z4,z5,z6])],[(0,[z66,z0,z2,z3,z4,z5,z6]),(1,[z0,z358,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z359,z5,z6]),(0,[z0,z1,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z360,z6]),(0,[z0,z361,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z327]),(0,[z0,z2,z3,z4,z362,z5,z6]),(0,[z0,z2,z363,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z14,z364]),(0,[z0,z2,z3,z81,z5,z122,z6]),(0,[z0,z2,z365,z3,z4,z5,z6])],[(0,[z366,z0,z2,z3,z4,z5,z6]),(0,[z367,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z202,z220,z6]),(1,[z0,z2,z212,z4,z210,z6]),(0,[z368,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z369,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z370,z5,z6]),(1,[z0,z2,z371,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z372])],[(0,[z87,z0,z2,z74,z4,z5,z6]),(0,[z9,z0,z2,z3,z5,z296,z6]),(0,[z79,z0,z20,z3,z4,z5,z6]),(0,[z0,z2,z133,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z373,z5,z6]),(0,[z0,z25,z2,z3,z4,z125,z5]),(0,[z0,z374,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z220,z6])]],
   [[(0,[z375,z0,z2,z3,z4,z5,z6]),(0,[z376,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z377,z4,z5,z6])],[(0,[z0,z2,z3,z4,z378,z5,z6]),(0,[z0,z2,z3,z4,z379,z5,z6]),(0,[z0,z2,z380,z3,z4,z5,z6]),(0,[z0,z381,z2,z3,z4,z5,z6])],[(0,[z0,z2,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z382]),(0,[z71,z0,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z4,z5,z51]),(0,[z0,z2,z3,z4,z5,z6,z383]),(0,[z0,z2,z3,z4,z5,z6,z52]),(0,[z0,z384,z2,z3,z4,z5,z6]),(0,[z0,z385,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z386,z5,z6])],[(1,[z0,z2,z3,z4,z5,z67]),(1,[z106,z2,z74,z4,z5,z6]),(0,[z0,z2,z3,z4,z387,z5,z6])],[(0,[z388,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z389,z6]),(0,[z0,z2,z3,z4,z5,z6,z390]),(0,[z50,z2,z3,z4,z5,z220,z6])],[(0,[z391,z0,z2,z3,z4,z5,z6]),(0,[z0,z392,z2,z3,z4,z5,z6]),(0,[z0,z260,z24,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z393,z6])],[(0,[z0,z2,z3,z4,z394,z5,z6]),(0,[z0,z2,z3,z395,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z396,z6]),(0,[z0,z397,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z398])]],
   [[(0,[z0,z399,z2,z3,z4,z5,z6]),(0,[z0,z2,z74,z3,z4,z5,z14]),(0,[z0,z77,z2,z3,z4,z5,z14]),(0,[z0,z260,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z72,z4,z5,z6]),(0,[z0,z2,z133,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z400,z5,z6]),(0,[z0,z401,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z402])],[(0,[z0,z2,z3,z4,z403,z5,z6]),(0,[z0,z20,z2,z3,z4,z5,z14])],[(0,[z0,z2,z3,z4,z5,z6,z18]),(0,[z404,z0,z2,z3,z4,z5,z6]),(0,[z0,z405,z2,z3,z4,z81,z5]),(0,[z0,z2,z3,z4,z5,z6,z406]),(0,[z0,z2,z3,z407,z4,z5,z6]),(0,[z0,z2,z408,z3,z4,z5,z6])],[(0,[z106,z0,z2,z3,z4,z5,z196])],[(0,[z66,z0,z2,z3,z4,z5,z141]),(0,[z0,z409,z2,z3,z4,z5,z6]),(0,[z0,z410,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z93,z14]),(0,[z0,z200,z2,z3,z63,z5,z6]),(0,[z0,z2,z3,z4,z5,z411,z6])],[(0,[z412,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z413]),(0,[z0,z1,z2,z4,z160,z5,z6]),(0,[z0,z25,z3,z4,z5,z48,z6])],[(0,[z9,z0,z7,z2,z3,z5,z6]),(0,[z0,z414,z2,z3,z4,z5,z6]),(0,[z0,z415,z2,z3,z4,z5,z6]),(0,[z79,z0,z120,z3,z4,z5,z6]),(0,[z0,z20,z80,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z235,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z14,z6]),(0,[z0,z2,z3,z4,z5,z10,z247]),(0,[z0,z2,z3,z4,z5,z416,z6])],[(0,[z0,z417,z2,z3,z4,z5,z6]),(0,[z418,z0,z2,z3,z4,z5,z6])],[(0,[z106,z0,z2,z3,z4,z5,z14]),(0,[z0,z120,z2,z3,z4,z5,z10]),(0,[z0,z108,z2,z3,z4,z5,z14]),(0,[z0,z419,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z3,z4,z5,z6])],[(0,[z87,z0,z2,z88,z4,z5,z6]),(0,[z0,z420,z2,z3,z4,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z14]),(0,[z0,z24,z2,z3,z4,z5,z52])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z114,z5,z14]),(0,[z0,z2,z3,z4,z5,z235,z221]),(0,[z0,z421,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z72,z4,z5,z10]),(0,[z0,z124,z2,z3,z4,z5,z14]),(0,[z0,z422,z2,z3,z4,z5,z6]),(1,[z0,z260,z2,z3,z4,z273])],[(0,[z0,z423,z2,z3,z4,z5,z6]),(0,[z0,z167,z2,z3,z4,z5,z10]),(0,[z0,z424,z2,z3,z4,z5,z6])],[(0,[z0,z425,z2,z3,z4,z5,z6]),(0,[z106,z0,z2,z74,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z122,z10]),(0,[z0,z2,z3,z4,z81,z5,z6]),(0,[z426,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z79,z0,z86,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z60,z6]),(0,[z0,z2,z427,z3,z4,z5,z6]),(0,[z428,z0,z2,z3,z4,z5,z6])],[(0,[z87,z0,z1,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z429,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z430]),(0,[z431,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z432,z3,z4,z5,z6]),(0,[z0,z260,z2,z3,z4,z5,z273])],[(0,[z0,z433,z2,z3,z4,z5,z6]),(0,[z50,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z82,z5,z14]),(0,[z0,z20,z2,z371,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z434,z6]),(0,[z0,z2,z3,z4,z5,z6,z435]),(0,[z0,z436,z2,z3,z4,z5,z6])],[(0,[z437,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z51]),(0,[z0,z80,z2,z3,z4,z5,z10]),(0,[z0,z120,z3,z4,z81,z5,z6]),(0,[z0,z260,z2,z3,z4,z5,z126])],[(0,[z87,z0,z119,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z14,z10]),(0,[z0,z2,z3,z4,z5,z438,z6]),(0,[z0,z2,z3,z4,z5,z439,z6])],[(0,[z0,z2,z3,z4,z5,z440,z6]),(0,[z0,z208,z3,z4,z11,z5,z6]),(1,[z0,z64,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z441,z5,z6]),(0,[z0,z2,z3,z442,z4,z5,z6])],[(0,[z0,z443,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z107,z6]),(0,[z79,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z444,z5,z6]),(0,[z0,z260,z2,z3,z4,z125,z6])],[(0,[z0,z148,z2,z3,z4,z5,z6]),(0,[z0,z124,z2,z3,z4,z5,z247])]],
   [[(0,[z106,z0,z2,z3,z4,z5,z327]),(0,[z0,z2,z445,z3,z4,z5,z6]),(0,[z0,z0,z2,z3,z4,z5,z10]),(0,[z0,z208,z2,z3,z4,z5,z10]),(0,[z0,z446,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z14,z273])],[(0,[z0,z2,z3,z4,z447,z5,z6]),(0,[z448,z0,z2,z3,z4,z5,z6]),(0,[z0,z449,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z450]),(0,[z0,z2,z3,z4,z5,z451,z6]),(0,[z0,z2,z3,z4,z159,z5,z6]),(0,[z0,z2,z3,z4,z5,z452,z6]),(0,[z0,z2,z3,z4,z453,z5,z6])],[(1,[z0,z2,z234,z4,z5,z6]),(0,[z71,z0,z2,z3,z41,z5,z6]),(0,[z0,z2,z3,z4,z5,z221,z10]),(0,[z0,z2,z3,z4,z5,z60,z10]),(0,[z0,z80,z3,z4,z81,z5,z6])],[(0,[z0,z454,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z88,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z195,z14])],[(0,[z71,z0,z2,z3,z4,z5,z158]),(0,[z0,z80,z2,z3,z81,z5,z6]),(0,[z0,z455,z2,z3,z4,z81,z5]),(0,[z0,z2,z3,z4,z5,z6,z456])],[(0,[z0,z2,z3,z4,z457,z5,z6]),(1,[z92,z2,z3,z4,z159,z6]),(0,[z458,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z459,z4,z5,z6]),(0,[z0,z2,z3,z4,z126,z6,z273])]],
   [[(0,[z0,z205,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z460,z5,z6]),(0,[z0,z200,z2,z3,z174,z5,z6]),(0,[z0,z2,z3,z4,z5,z13,z6]),(0,[z461,z0,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z296])],[(0,[z0,z462,z2,z3,z4,z5,z6]),(0,[z0,z77,z2,z4,z82,z5,z6])],[(1,[z0,z109,z3,z4,z5,z6]),(0,[z0,z2,z463,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z464,z5,z6]),(0,[z0,z2,z3,z4,z202,z159,z6]),(0,[z0,z2,z3,z4,z160,z5,z10]),(0,[z0,z2,z3,z4,z5,z6,z465])],[(1,[z0,z2,z3,z4,z5,z382]),(0,[z466,z0,z2,z3,z4,z5,z6]),(0,[z467,z0,z2,z3,z4,z5,z6]),(0,[z468,z0,z2,z3,z4,z5,z6])],[(0,[z0,z469,z2,z3,z4,z5,z6]),(1,[z0,z2,z470,z4,z5,z6]),(0,[z9,z0,z2,z3,z72,z5,z6]),(0,[z0,z2,z3,z4,z125,z5,z14]),(0,[z0,z2,z3,z214,z81,z5,z6]),(0,[z0,z37,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z471])],[(0,[z27,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z472,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z41,z5,z6]),(0,[z0,z2,z3,z4,z5,z473,z6]),(0,[z0,z2,z3,z4,z474,z5,z6])],[(0,[z0,z2,z3,z4,z5,z475,z6]),(0,[z9,z0,z2,z470,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z390]),(0,[z0,z2,z3,z4,z5,z6,z476]),(0,[z0,z2,z3,z4,z5,z48,z6]),(0,[z0,z477,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z478,z6]),(0,[z0,z479,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z480,z4,z5,z6]),(1,[z0,z259,z2,z3,z5,z10]),(0,[z0,z2,z3,z4,z481,z5,z6]),(0,[z0,z482,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z483,z4,z5,z6])],[(0,[z0,z484,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z88,z4,z5,z10]),(0,[z9,z0,z2,z3,z4,z5,z390]),(0,[z0,z2,z3,z4,z11,z5,z14]),(0,[z0,z2,z3,z4,z210,z5,z14]),(0,[z0,z2,z3,z4,z485,z5,z6]),(0,[z0,z38,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z486,z6]),(0,[z0,z24,z2,z3,z4,z5,z48]),(0,[z0,z487,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z488,z6])],[(0,[z489,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z118]),(0,[z0,z2,z490,z3,z4,z5,z6])],[(0,[z0,z86,z2,z3,z61,z5,z6]),(0,[z0,z62,z2,z3,z4,z5,z6]),(0,[z0,z24,z2,z3,z4,z5,z10]),(0,[z491,z0,z2,z3,z4,z5,z6]),(0,[z0,z492,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z493,z4,z5,z6]),(0,[z0,z209,z2,z4,z5,z57,z6]),(0,[z0,z7,z2,z3,z4,z5,z118])],[(1,[z0,z157,z3,z4,z5,z6]),(0,[z0,z2,z494,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z13,z10]),(0,[z0,z2,z495,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z174,z5,z6]),(0,[z0,z209,z2,z3,z4,z57,z6])],[(0,[z0,z2,z496,z3,z4,z5,z6]),(0,[z0,z497,z2,z3,z4,z5,z10]),(0,[z498,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z499,z6])],[(0,[z106,z0,z119,z2,z4,z5,z6]),(0,[z71,z0,z167,z2,z3,z5,z6]),(0,[z50,z0,z2,z3,z4,z220,z6]),(0,[z0,z25,z8,z2,z3,z4,z5]),(0,[z0,z12,z2,z3,z82,z5,z6]),(0,[z500,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z501,z6]),(0,[z0,z37,z124,z2,z4,z5,z6])],[(0,[z66,z0,z2,z3,z4,z5,z67]),(0,[z0,z2,z3,z4,z5,z502,z6]),(0,[z0,z503,z2,z3,z4,z5,z6])]],
   [[(1,[z0,z2,z3,z4,z5,z413]),(0,[z0,z2,z504,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z134,z57]),(0,[z0,z2,z3,z214,z4,z202,z6]),(0,[z0,z2,z3,z214,z202,z5,z6])],[(0,[z0,z505,z2,z3,z4,z5,z6]),(0,[z0,z506,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z507,z6])],[(0,[z0,z2,z28,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z14,z508]),(0,[z0,z2,z3,z4,z5,z57,z14]),(0,[z0,z2,z3,z4,z5,z509,z6])],[(0,[z87,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z10,z163]),(0,[z0,z2,z3,z4,z5,z48,z10]),(0,[z0,z2,z3,z4,z5,z510,z6])],[(0,[z0,z511,z2,z3,z4,z5,z6])],[(0,[z512,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z513,z5,z6]),(0,[z514,z0,z2,z3,z4,z5,z6]),(0,[z0,z515,z2,z3,z4,z5,z6])],[(0,[z516,z0,z2,z3,z4,z5,z6]),(0,[z0,z517,z2,z3,z4,z5,z6]),(0,[z518,z0,z2,z3,z4,z5,z6])],[(0,[z519,z0,z2,z3,z4,z5,z6]),(0,[z0,z520,z2,z3,z4,z5,z6])]],
   [[(0,[z50,z0,z2,z3,z4,z5,z107]),(1,[z0,z424,z2,z4,z5,z6]),(1,[z0,z12,z77,z2,z5,z6])],[(0,[z0,z2,z521,z3,z4,z5,z6]),(0,[z0,z2,z88,z4,z82,z5,z6]),(0,[z0,z2,z3,z4,z5,z158,z6]),(0,[z0,z2,z3,z522,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z296,z10]),(0,[z0,z2,z3,z4,z523,z5,z6]),(0,[z0,z119,z1,z3,z4,z5,z6]),(0,[z0,z524,z2,z3,z4,z5,z6])],[(0,[z0,z525,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z526]),(0,[z0,z2,z3,z527,z4,z5,z6]),(0,[z0,z528,z2,z3,z4,z5,z6]),(0,[z0,z2,z529,z3,z4,z5,z6])],[(0,[z0,z86,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z530,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z0,z531,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z364]),(0,[z0,z2,z3,z4,z5,z532,z6]),(0,[z0,z2,z3,z4,z5,z533,z6])],[(0,[z0,z534,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z268,z5,z6]),(0,[z0,z405,z2,z3,z4,z5,z6]),(0,[z0,z2,z535,z3,z4,z5,z6]),(0,[z0,z536,z2,z3,z4,z5,z6]),(0,[z0,z537,z2,z3,z4,z5,z6])],[(0,[z0,z2,z538,z3,z4,z5,z6]),(0,[z0,z119,z2,z4,z82,z5,z6]),(0,[z0,z2,z4,z5,z313,z221,z6]),(0,[z0,z2,z3,z4,z5,z539,z6]),(0,[z0,z2,z3,z540,z4,z5,z6])],[(0,[z0,z358,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z52]),(0,[z0,z2,z212,z3,z4,z5,z14]),(0,[z0,z208,z2,z3,z4,z11,z6]),(0,[z0,z77,z109,z3,z4,z5,z6])],[(0,[z541,z0,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z3,z5,z296,z6])]],
   [[(0,[z0,z2,z3,z4,z202,z5,z14]),(0,[z0,z77,z2,z133,z3,z5,z6]),(0,[z0,z2,z3,z4,z542,z5,z6])],[(0,[z0,z120,z2,z3,z4,z5,z6]),(0,[z0,z167,z2,z3,z214,z5,z6]),(0,[z0,z2,z543,z3,z4,z5,z6])],[(0,[z0,z25,z2,z3,z4,z5,z14]),(0,[z0,z7,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z544,z5,z6]),(0,[z0,z37,z2,z3,z4,z125,z5]),(0,[z0,z545,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z546,z4,z5,z6]),(0,[z0,z2,z3,z4,z159,z122,z6]),(0,[z0,z2,z3,z4,z547,z5,z6]),(0,[z0,z548,z2,z3,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z6,z549]),(0,[z0,z550,z2,z3,z4,z5,z6]),(0,[z0,z120,z1,z2,z4,z5,z6]),(0,[z0,z200,z3,z4,z5,z221,z6]),(0,[z0,z167,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z122,z6])],[(0,[z551,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z552,z5,z6])]],
   [[(0,[z0,z534,z2,z3,z4,z5,z10]),(0,[z0,z37,z2,z3,z4,z5,z13]),(0,[z0,z2,z3,z4,z125,z126,z6])],[(0,[z0,z2,z3,z4,z5,z553,z6]),(0,[z223,z0,z2,z3,z4,z5,z14])],[(0,[z0,z209,z2,z3,z4,z5,z10]),(0,[z0,z554,z2,z3,z4,z5,z6]),(0,[z0,z80,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z555,z6]),(0,[z0,z20,z2,z3,z82,z5,z6]),(0,[z0,z556,z2,z3,z4,z5,z6])],[(0,[z0,z557,z2,z3,z4,z5,z6]),(0,[z558,z0,z2,z3,z4,z5,z6]),(1,[z0,z3,z4,z5,z263,z6])],[(0,[z559,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z560]),(0,[z0,z561,z2,z3,z4,z5,z6])],[(1,[z66,z86,z3,z4,z5,z6]),(0,[z2,z74,z3,z88,z4,z5,z6])],[(0,[z0,z2,z470,z3,z4,z5,z6]),(0,[z71,z0,z2,z3,z4,z5,z181]),(0,[z0,z1,z3,z4,z11,z5,z6]),(0,[z0,z562,z2,z3,z4,z5,z6])],[(0,[z0,z563,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z564,z6]),(0,[z0,z208,z2,z3,z4,z5,z6]),(0,[z0,z24,z7,z2,z3,z4,z5]),(0,[z0,z2,z212,z3,z4,z210,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z565,z6]),(0,[z0,z167,z2,z3,z5,z122,z6])],[(0,[z0,z2,z3,z4,z5,z6,z70]),(0,[z9,z0,z2,z3,z81,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z4,z5,z6,z566]),(0,[z567,z0,z2,z3,z4,z5,z6]),(0,[z0,z7,z25,z2,z3,z4,z5]),(0,[z0,z568,z2,z3,z4,z5,z6]),(1,[z0,z569,z3,z4,z5,z6]),(0,[z0,z2,z3,z214,z4,z5,z6]),(0,[z0,z8,z2,z3,z4,z5,z296])],[(0,[z570,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z571,z3,z4,z5,z6]),(0,[z0,z217,z2,z3,z4,z5,z6]),(0,[z0,z572,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z573,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z574,z6]),(0,[z0,z2,z3,z4,z5,z221,z6]),(0,[z575,z0,z2,z3,z4,z5,z6])],[(0,[z0,z252,z2,z3,z4,z5,z6]),(0,[z0,z119,z2,z4,z210,z5,z6]),(0,[z0,z2,z3,z4,z576,z5,z6]),(0,[z0,z2,z3,z4,z5,z577,z6])],[(0,[z0,z2,z3,z4,z5,z553,z10]),(0,[z0,z29,z2,z3,z4,z5,z10]),(0,[z0,z200,z2,z3,z4,z5,z14]),(0,[z0,z1,z2,z4,z82,z5,z6]),(0,[z578,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z371,z4,z5,z6]),(0,[z579,z0,z2,z3,z4,z5,z6]),(0,[z0,z265,z2,z3,z4,z5,z57]),(0,[z0,z37,z2,z3,z4,z5,z247])],[(1,[z0,z410,z3,z4,z5,z6]),(0,[z0,z2,z3,z580,z4,z5,z6]),(0,[z0,z20,z424,z2,z4,z5,z6]),(0,[z0,z349,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z134]),(1,[z0,z2,z3,z214,z202,z6])],[(0,[z0,z2,z3,z4,z5,z581,z6]),(0,[z0,z2,z3,z582,z4,z5,z6]),(1,[z0,z2,z3,z4,z206,z6]),(0,[z71,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z583,z5,z6]),(1,[z0,z455,z2,z3,z4,z5]),(0,[z0,z455,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z584,z4,z5,z6]),(0,[z0,z585,z2,z3,z4,z5,z6]),(1,[z0,z7,z2,z3,z5,z118]),(0,[z0,z2,z3,z4,z5,z586,z6])]],
   [[(0,[z9,z0,z410,z3,z4,z5,z6]),(0,[z0,z2,z3,z113,z5,z220,z6]),(0,[z0,z587,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z588,z4,z5,z6]),(0,[z0,z2,z3,z589,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z590,z6]),(1,[z0,z37,z2,z4,z5,z247])],[(0,[z591,z0,z2,z3,z4,z5,z6]),(0,[z592,z0,z2,z3,z4,z5,z6]),(0,[z9,z0,z2,z3,z4,z206,z6]),(0,[z0,z593,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z594,z6])],[(0,[z66,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z14,z118]),(0,[z0,z2,z3,z4,z160,z5,z6]),(0,[z0,z595,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z596,z4,z5,z6])],[(0,[z597,z0,z2,z3,z4,z5,z6]),(0,[z598,z0,z2,z3,z4,z5,z6]),(0,[z0,z349,z2,z3,z4,z5,z221]),(0,[z0,z2,z3,z4,z5,z599,z6])],[(0,[z0,z600,z2,z3,z4,z5,z6]),(0,[z9,z0,z2,z3,z202,z5,z6]),(1,[z0,z2,z3,z5,z60,z10]),(0,[z0,z2,z3,z4,z5,z14,z130]),(0,[z601,z0,z2,z3,z4,z5,z6]),(0,[z0,z8,z2,z3,z4,z5,z118])],[(0,[z602,z0,z2,z3,z4,z5,z6]),(0,[z0,z603,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z214,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z6,z10]),(0,[z0,z2,z3,z604,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z605,z6]),(0,[z0,z38,z2,z4,z5,z221,z6]),(0,[z0,z606,z2,z3,z4,z5,z6]),(0,[z0,z607,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z608])],[(0,[z0,z2,z3,z4,z5,z609,z6]),(0,[z50,z0,z2,z3,z4,z159,z6]),(0,[z0,z2,z133,z3,z4,z5,z14]),(0,[z0,z120,z3,z4,z160,z5,z6]),(0,[z0,z610,z2,z3,z4,z5,z6]),(1,[z0,z208,z3,z4,z11,z6])],[(1,[z0,z259,z2,z3,z5,z6]),(1,[z0,z405,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z6,z611])]],
   [[(0,[z0,z2,z3,z4,z5,z220,z14]),(0,[z0,z77,z2,z3,z4,z5,z10])],[(0,[z9,z0,z2,z234,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z612,z6]),(0,[z0,z2,z3,z63,z4,z5,z6]),(0,[z0,z12,z77,z2,z4,z5,z6])],[(0,[z613,z0,z2,z3,z4,z5,z6]),(0,[z0,z77,z20,z2,z3,z5,z6]),(0,[z0,z614,z2,z3,z4,z5,z6]),(0,[z0,z24,z2,z3,z4,z5,z6]),(0,[z0,z24,z3,z4,z5,z6,z52]),(0,[z0,z2,z4,z5,z13,z6,z247]),(0,[z0,z2,z3,z4,z5,z6,z273])],[(1,[z0,z2,z3,z4,z5,z128]),(0,[z0,z2,z3,z4,z5,z197,z6]),(0,[z0,z615,z2,z3,z4,z5,z6]),(0,[z0,z64,z3,z4,z5,z57,z6]),(0,[z0,z2,z3,z616,z4,z5,z6])],[(0,[z0,z2,z74,z4,z82,z5,z6]),(0,[z0,z497,z2,z3,z4,z5,z6]),(0,[z0,z259,z2,z3,z4,z5,z6]),(0,[z0,z617,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z618,z6]),(0,[z0,z200,z2,z3,z4,z221,z6])],[(1,[z0,z104,z2,z4,z5,z6]),(0,[z0,z619,z2,z3,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z620,z6]),(0,[z0,z621,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z622])],[(0,[z0,z623,z2,z3,z4,z5,z6]),(0,[z71,z0,z2,z3,z5,z296,z6]),(0,[z0,z2,z624,z3,z4,z5,z6]),(0,[z625,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z626,z3,z4,z5,z6])],[(0,[z0,z2,z627,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z628,z6]),(1,[z0,z2,z133,z82,z5,z6]),(0,[z0,z3,z4,z5,z263,z57,z6]),(0,[z0,z2,z3,z4,z5,z126,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z629,z6]),(0,[z0,z2,z630,z3,z4,z5,z6]),(0,[z0,z600,z2,z3,z4,z5,z10]),(0,[z0,z631,z2,z3,z4,z5,z6]),(0,[z632,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z633,z6]),(0,[z0,z2,z3,z4,z5,z634,z6]),(0,[z0,z260,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z635,z5,z6]),(0,[z0,z636,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z637,z6]),(0,[z0,z638,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z72,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z639,z6]),(0,[z50,z92,z2,z3,z4,z5,z6]),(0,[z0,z640,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z287,z6]),(1,[z0,z35,z2,z3,z5,z6]),(0,[z110,z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z10,z323]),(0,[z0,z77,z2,z3,z81,z5,z6]),(1,[z0,z25,z3,z4,z5,z48])],[(0,[z0,z1,z2,z4,z210,z5,z6]),(0,[z0,z2,z3,z4,z5,z641,z6]),(0,[z0,z2,z3,z4,z5,z6,z642])],[(1,[z0,z2,z3,z4,z5,z219]),(0,[z0,z2,z3,z4,z5,z6,z643]),(0,[z644,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z645]),(0,[z0,z77,z569,z3,z4,z5,z6]),(0,[z0,z167,z2,z3,z4,z122,z6])],[(0,[z0,z2,z3,z4,z646,z5,z6])],[(0,[z647,z0,z2,z3,z4,z5,z6]),(0,[z106,z2,z74,z3,z4,z5,z6]),(0,[z0,z648,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z259,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z5,z60,z6,z10]),(0,[z0,z119,z2,z3,z4,z5,z6]),(1,[z0,z252,z2,z3,z5,z6]),(0,[z0,z649,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z650]),(0,[z0,z2,z3,z4,z5,z296,z6])],[(0,[z0,z651,z2,z3,z4,z5,z6]),(0,[z9,z0,z157,z3,z4,z5,z6]),(0,[z0,z619,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z14,z14]),(1,[z0,z8,z2,z3,z5,z296])],[(0,[z27,z0,z2,z3,z4,z5,z413]),(0,[z0,z2,z3,z4,z652,z5,z6]),(0,[z0,z2,z3,z4,z653,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z654])],[(0,[z0,z2,z3,z4,z655,z5,z6]),(0,[z87,z0,z2,z3,z4,z5,z382]),(0,[z0,z2,z3,z4,z5,z628,z10]),(0,[z2,z3,z4,z5,z14,z6,z10]),(0,[z0,z2,z3,z4,z5,z126,z10]),(0,[z0,z8,z2,z3,z4,z5,z14]),(0,[z0,z656,z2,z3,z4,z5,z6]),(0,[z657,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z658])],[(0,[z66,z86,z2,z3,z4,z5,z6]),(0,[z0,z35,z86,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z219,z6]),(0,[z0,z659,z2,z3,z4,z5,z6]),(1,[z50,z2,z3,z4,z220,z6]),(0,[z0,z660,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z661,z5,z6]),(0,[z92,z0,z2,z3,z4,z220,z6]),(0,[z0,z2,z3,z4,z5,z662,z6]),(0,[z0,z0,z2,z3,z4,z5,z14]),(0,[z0,z310,z2,z3,z4,z5,z6]),(0,[z0,z663,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z296,z6,z118]),(0,[z0,z2,z3,z4,z5,z664,z6])],[],[(0,[z0,z315,z2,z3,z4,z5,z6]),(0,[z665,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z666,z5,z6]),(0,[z667,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z668,z3,z4,z5,z6]),(0,[z0,z669,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z670,z2,z3,z4,z5,z6]),(0,[z71,z0,z7,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z81,z5,z14]),(0,[z671,z0,z2,z3,z4,z5,z6]),(0,[z0,z672,z2,z3,z4,z5,z6]),(0,[z0,z260,z25,z2,z3,z4,z5]),(0,[z673,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z674,z5,z6])],[(0,[z27,z2,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z675,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z50,z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z6,z508]),(0,[z0,z2,z3,z4,z5,z14,z247])],[(0,[z0,z2,z3,z676,z4,z5,z6]),(0,[z0,z119,z2,z3,z4,z5,z10]),(1,[z0,z2,z3,z268,z5,z6]),(0,[z0,z2,z3,z4,z677,z5,z6]),(0,[z0,z678,z2,z3,z4,z5,z6]),(1,[z0,z265,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z679,z5,z6]),(0,[z0,z680,z2,z3,z4,z5,z6])],[(0,[z0,z2,z681,z3,z4,z5,z6]),(0,[z9,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z255,z5,z6]),(0,[z0,z682,z2,z3,z4,z5,z6]),(0,[z0,z12,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z683]),(0,[z0,z684,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z440,z14]),(1,[z0,z2,z4,z5,z313,z6]),(0,[z0,z260,z37,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z685,z5,z6]),(0,[z223,z22,z2,z3,z4,z5,z6]),(0,[z79,z0,z2,z3,z4,z5,z14]),(1,[z0,z1,z4,z160,z5,z6]),(0,[z0,z24,z2,z3,z4,z125,z5]),(0,[z0,z686,z2,z3,z4,z5,z6]),(0,[z0,z209,z2,z212,z4,z5,z6])]],
   [[(0,[z106,z87,z2,z3,z4,z5,z6])],[(0,[z687,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z662,z10]),(0,[z0,z688,z2,z3,z4,z5,z6]),(0,[z0,z209,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z689])],[(0,[z0,z2,z3,z690,z4,z5,z6]),(0,[z0,z358,z2,z28,z4,z5,z6]),(1,[z0,z2,z3,z4,z255,z6]),(0,[z0,z691,z2,z3,z4,z5,z6]),(0,[z0,z25,z2,z3,z4,z5,z52]),(0,[z0,z569,z2,z3,z4,z5,z6])],[(1,[z2,z3,z4,z5,z14,z10]),(1,[z0,z209,z2,z4,z57,z6]),(0,[z692,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z693,z5,z6])],[(0,[z0,z2,z3,z4,z159,z5,z14]),(0,[z0,z352,z2,z3,z4,z5,z6]),(0,[z0,z694,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z11,z5,z221,z6]),(0,[z0,z2,z4,z210,z5,z57,z6]),(0,[z0,z2,z3,z4,z5,z6,z695]),(0,[z0,z2,z3,z4,z5,z696,z6]),(0,[z0,z7,z2,z3,z5,z6,z118]),(0,[z697,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z125,z5,z10]),(0,[z0,z209,z1,z2,z4,z5,z6]),(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z0,z699,z2,z3,z4,z5,z6]),(0,[z0,z700,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z701])],[(0,[z0,z2,z3,z88,z4,z5,z14]),(0,[z0,z702,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z703,z6]),(0,[z0,z2,z3,z4,z704,z5,z6]),(0,[z0,z2,z3,z4,z5,z228,z6])],[(0,[z9,z71,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z705,z5,z6]),(0,[z0,z2,z3,z4,z5,z706,z6]),(0,[z0,z260,z2,z3,z4,z6,z273])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z2,z3,z4,z707,z6]),(0,[z66,z86,z3,z4,z5,z141]),(0,[z2,z3,z4,z5,z10,z170]),(0,[z0,z708,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z709])],[(0,[z0,z2,z3,z4,z5,z710]),(0,[z0,z711,z2,z4,z5,z6]),(0,[z92,z2,z3,z4,z159,z228])],[(0,[z0,z2,z3,z4,z5,z128]),(0,[z0,z2,z3,z4,z5,z712]),(0,[z0,z2,z3,z713,z5,z6]),(0,[z0,z259,z2,z3,z5,z296]),(0,[z714,z2,z3,z4,z5,z6])],[(0,[z87,z2,z88,z4,z5,z10]),(0,[z0,z715,z2,z3,z5,z10]),(0,[z0,z2,z3,z4,z5,z716])],[(0,[z0,z157,z3,z4,z5,z197]),(0,[z0,z717,z2,z4,z5,z14]),(0,[z0,z2,z3,z4,z114,z93]),(0,[z0,z3,z4,z11,z718,z6])],[(0,[z0,z148,z2,z3,z5,z6]),(0,[z0,z719,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z720])],[(0,[z0,z2,z3,z4,z5,z721]),(0,[z0,z2,z3,z4,z5,z722]),(0,[z0,z2,z3,z4,z5,z723])]],
   [[(0,[z92,z2,z3,z4,z159,z248]),(0,[z505,z2,z3,z4,z5,z10]),(0,[z0,z7,z2,z3,z5,z60])],[(0,[z0,z2,z3,z4,z5,z724])],[(0,[z0,z35,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z725,z6]),(0,[z0,z2,z3,z4,z5,z726])],[(0,[z0,z2,z3,z4,z5,z727]),(0,[z0,z2,z3,z728,z5,z6])],[(0,[z0,z2,z3,z4,z5,z219]),(0,[z9,z2,z3,z41,z206,z6]),(0,[z0,z2,z3,z4,z5,z729]),(0,[z0,z2,z3,z4,z5,z730])],[(0,[z0,z2,z3,z4,z5,z731]),(0,[z0,z7,z2,z3,z5,z390]),(0,[z0,z256,z3,z81,z5,z6]),(0,[z673,z2,z3,z4,z5,z10]),(0,[z0,z259,z2,z3,z5,z118])],[(0,[z0,z2,z3,z4,z5,z732]),(0,[z2,z3,z4,z5,z733,z6]),(0,[z514,z2,z3,z4,z5,z10]),(0,[z0,z352,z3,z4,z5,z287]),(0,[z0,z2,z3,z4,z5,z734])],[(0,[z27,z28,z3,z4,z5,z10]),(0,[z0,z2,z3,z735,z5,z6]),(0,[z0,z252,z2,z82,z5,z6]),(0,[z0,z119,z736,z4,z5,z6]),(0,[z0,z737,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z197]),(0,[z0,z2,z3,z522,z202,z6]),(0,[z0,z3,z4,z5,z263,z14]),(0,[z0,z2,z3,z4,z738,z6]),(0,[z0,z739,z2,z3,z5,z6]),(0,[z0,z8,z2,z3,z5,z296])],[(0,[z0,z2,z3,z4,z5,z740]),(0,[z2,z74,z741,z4,z5,z6]),(0,[z0,z742,z2,z4,z5,z6]),(0,[z0,z148,z2,z3,z5,z10]),(0,[z0,z2,z3,z4,z5,z743]),(0,[z0,z2,z3,z4,z125,z744])],[(0,[z0,z2,z3,z4,z745,z6]),(0,[z0,z746,z3,z4,z5,z6]),(0,[z79,z0,z20,z424,z5,z6]),(0,[z0,z2,z3,z747,z5,z6])],[(0,[z0,z748,z3,z4,z5,z6])],[(0,[z9,z2,z234,z41,z5,z6]),(0,[z0,z2,z749,z4,z5,z6])],[(0,[z0,z750,z2,z3,z5,z6]),(0,[z0,z2,z3,z751,z5,z10]),(0,[z0,z2,z3,z4,z5,z752]),(0,[z0,z2,z753,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z754]),(0,[z0,z2,z3,z4,z5,z755]),(0,[z0,z756,z2,z3,z4,z5]),(0,[z0,z2,z3,z5,z725,z10]),(0,[z0,z534,z2,z3,z5,z60]),(0,[z0,z2,z3,z4,z5,z757])],[(0,[z0,z2,z3,z4,z255,z197]),(0,[z0,z2,z3,z174,z5,z10])]],
   [[(0,[z0,z2,z3,z758,z5,z6]),(0,[z0,z2,z4,z5,z6,z759])],[(0,[z223,z2,z3,z4,z5,z14]),(0,[z2,z3,z4,z5,z332,z14])],[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z37,z2,z4,z5,z760])],[(0,[z9,z2,z3,z761,z5,z6]),(0,[z0,z2,z3,z214,z202,z14]),(0,[z0,z2,z3,z268,z5,z6]),(0,[z0,z1,z4,z583,z5,z6]),(0,[z0,z2,z3,z4,z5,z762]),(0,[z0,z3,z4,z5,z763,z6]),(0,[z0,z265,z2,z3,z4,z5]),(0,[z0,z3,z4,z5,z6,z764]),(0,[z765,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z206,z14]),(0,[z50,z2,z3,z4,z733,z6]),(0,[z0,z554,z1,z4,z5,z6]),(0,[z0,z200,z4,z313,z221,z6])],[(0,[z0,z2,z3,z4,z766,z6]),(0,[z418,z2,z88,z4,z5,z6]),(0,[z0,z2,z3,z214,z767,z6])],[(0,[z0,z768,z2,z4,z5,z6]),(0,[z0,z25,z3,z4,z5,z553]),(0,[z0,z1,z4,z160,z5,z6]),(0,[z0,z167,z2,z3,z767,z6])],[(0,[z0,z2,z3,z4,z5,z769]),(0,[z0,z2,z4,z5,z313,z235])]],
   [[(1,[z770,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z771,z6]),(0,[z772,z2,z3,z4,z5,z6])],[(0,[z0,z557,z3,z81,z5,z6]),(0,[z0,z2,z3,z4,z255,z6]),(0,[z556,z2,z3,z4,z5,z10]),(0,[z0,z1,z604,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z773])],[(0,[z87,z2,z741,z4,z5,z6]),(0,[z0,z774,z2,z3,z4,z5]),(0,[z0,z209,z2,z4,z261,z6]),(0,[z0,z2,z3,z4,z5,z775]),(0,[z0,z200,z3,z4,z718,z6]),(0,[z0,z209,z2,z4,z57,z6])],[(0,[z0,z2,z3,z776,z5,z6]),(0,[z22,z259,z2,z3,z5,z10]),(0,[z0,z315,z2,z4,z5,z364])],[(0,[z0,z2,z777,z4,z5,z6]),(0,[z0,z2,z3,z778,z5,z6]),(0,[z9,z157,z3,z41,z5,z6]),(0,[z0,z2,z234,z4,z5,z14]),(0,[z0,z2,z234,z4,z5,z390]),(0,[z0,z259,z2,z3,z5,z14]),(0,[z0,z779,z3,z4,z5,z10]),(0,[z697,z2,z3,z4,z5,z14])],[(0,[z223,z2,z3,z4,z5,z780]),(0,[z0,z781,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z782]),(0,[z0,z2,z3,z5,z783,z6]),(0,[z0,z7,z2,z3,z5,z19]),(0,[z0,z119,z120,z4,z5,z6]),(0,[z0,z2,z3,z4,z784,z6])],[(0,[z0,z2,z3,z4,z5,z785]),(0,[z0,z2,z3,z786,z5,z6]),(0,[z0,z120,z4,z5,z532,z6])]],
   [[(0,[z0,z2,z3,z787,z5,z6]),(0,[z9,z524,z2,z3,z5,z6]),(0,[z0,z2,z3,z788,z5,z10]),(0,[z0,z455,z80,z3,z81,z5]),(0,[z789,z2,z3,z4,z5,z6]),(0,[z79,z0,z790,z3,z5,z6]),(1,[z0,z3,z4,z718,z6]),(0,[z0,z2,z3,z4,z5,z791])],[(0,[z79,z0,z104,z4,z5,z6]),(0,[z0,z619,z2,z4,z5,z628])],[(0,[z0,z104,z2,z4,z5,z14]),(0,[z66,z86,z3,z4,z5,z67])],[(0,[z106,z492,z2,z4,z5,z6]),(0,[z0,z37,z2,z4,z5,z364]),(0,[z0,z2,z792,z4,z5,z6]),(0,[z793,z2,z3,z4,z5,z6])],[(0,[z87,z2,z88,z4,z5,z219]),(0,[z0,z2,z3,z4,z5,z794]),(0,[z0,z795,z2,z3,z5,z6]),(0,[z0,z2,z796,z4,z5,z6]),(0,[z0,z2,z797,z4,z5,z10]),(0,[z0,z2,z133,z82,z5,z14]),(0,[z0,z2,z3,z4,z5,z798])],[(0,[z0,z12,z152,z2,z5,z6]),(0,[z0,z2,z470,z4,z5,z390]),(0,[z0,z38,z2,z4,z5,z6]),(1,[z0,z736,z4,z5,z6]),(0,[z799,z2,z3,z4,z5,z6]),(0,[z0,z800,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z141]),(0,[z27,z28,z3,z4,z5,z128]),(0,[z0,z3,z4,z5,z801,z10])],[(0,[z0,z802,z2,z3,z4,z5]),(0,[z0,z2,z803,z4,z5,z6]),(0,[z0,z200,z3,z4,z235,z221]),(0,[z0,z24,z3,z4,z5,z52])]],
   [[(0,[z87,z238,z2,z4,z5,z6]),(0,[z0,z1,z253,z4,z5,z6])],[(0,[z0,z2,z624,z82,z5,z6]),(1,[z0,z3,z4,z5,z804])],[(0,[z0,z157,z470,z4,z5,z6]),(0,[z0,z119,z120,z4,z5,z10]),(0,[z0,z2,z805,z4,z5,z14]),(0,[z0,z208,z3,z4,z718,z6])],[(0,[z2,z3,z4,z5,z806,z6]),(0,[z0,z200,z3,z4,z221,z6]),(0,[z0,z25,z626,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z807])],[(0,[z0,z35,z808,z2,z5,z6]),(0,[z0,z2,z3,z4,z5,z809]),(0,[z0,z157,z3,z4,z5,z14]),(0,[z0,z157,z3,z4,z5,z390]),(0,[z9,z615,z2,z3,z5,z6]),(0,[z0,z810,z2,z3,z4,z5]),(0,[z0,z120,z736,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z811])],[(0,[z2,z741,z3,z4,z5,z6]),(0,[z0,z252,z2,z3,z5,z14]),(0,[z632,z2,z3,z4,z5,z14])],[(0,[z0,z812,z2,z4,z5,z6]),(0,[z0,z813,z2,z3,z4,z5])],[(0,[z0,z814,z2,z3,z4,z5]),(0,[z0,z815,z3,z4,z5,z6]),(0,[z0,z20,z410,z3,z5,z6]),(0,[z816,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z817,z4,z5,z6]),(0,[z50,z2,z3,z113,z220,z6]),(0,[z0,z511,z1,z4,z5,z6])],[(0,[z0,z2,z818,z4,z5,z6]),(0,[z0,z2,z3,z202,z451,z6]),(0,[z50,z2,z3,z4,z220,z14]),(0,[z0,z80,z3,z81,z5,z10]),(0,[z0,z819,z2,z3,z4,z5]),(0,[z79,z0,z20,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z196]),(0,[z0,z715,z2,z3,z5,z6]),(0,[z0,z820,z64,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z821])],[(0,[z0,z2,z3,z61,z5,z10]),(0,[z0,z822,z3,z4,z5,z6]),(0,[z9,z2,z3,z41,z5,z10]),(0,[z0,z2,z94,z82,z5,z6])],[(0,[z0,z2,z3,z4,z5,z823]),(0,[z0,z2,z3,z4,z5,z824]),(0,[z0,z2,z212,z4,z825,z6])],[(0,[z0,z2,z3,z826,z5,z6]),(0,[z0,z35,z2,z827,z5,z6]),(0,[z0,z2,z3,z828,z5,z6]),(0,[z0,z829,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z718,z6]),(0,[z0,z2,z3,z4,z5,z830]),(0,[z0,z2,z3,z4,z5,z744])],[(0,[z0,z2,z3,z4,z733,z6]),(0,[z22,z2,z3,z4,z5,z10]),(0,[z0,z200,z3,z4,z221,z10]),(0,[z0,z120,z3,z174,z5,z6]),(0,[z0,z2,z831,z4,z5,z6]),(0,[z0,z2,z3,z4,z825,z6])]],
   [[(0,[z27,z770,z3,z4,z5,z6]),(0,[z0,z424,z2,z4,z5,z14]),(0,[z0,z12,z77,z2,z5,z14]),(0,[z0,z2,z3,z832,z5,z6]),(0,[z0,z1,z4,z677,z5,z6])],[(0,[z0,z349,z2,z4,z5,z313])],[(0,[z0,z2,z3,z833,z5,z6]),(0,[z0,z736,z3,z4,z5,z6]),(0,[z0,z834,z3,z4,z5,z6])],[(0,[z0,z2,z741,z4,z5,z6]),(0,[z0,z2,z3,z5,z10,z835]),(0,[z0,z2,z4,z5,z313,z14]),(0,[z0,z77,z739,z2,z5,z6]),(0,[z0,z836,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z125,z126])],[(0,[z0,z2,z3,z4,z5,z837]),(0,[z0,z2,z838,z4,z5,z6]),(0,[z0,z7,z2,z3,z100,z5])],[(0,[z66,z86,z3,z61,z5,z6]),(0,[z79,z0,z20,z3,z5,z10]),(0,[z0,z839,z2,z3,z5,z14]),(0,[z0,z2,z4,z210,z620,z6]),(0,[z0,z424,z2,z82,z5,z6])],[(0,[z27,z28,z3,z4,z5,z6]),(0,[z0,z124,z2,z4,z5,z13]),(1,[z0,z2,z3,z5,z840])],[(0,[z466,z28,z3,z4,z5,z6]),(0,[z0,z2,z3,z841,z5,z10]),(0,[z0,z2,z3,z4,z5,z804])]],
   [[(0,[z0,z2,z3,z842,z5,z6]),(0,[z2,z3,z4,z5,z14,z780]),(0,[z0,z2,z3,z843,z5,z6]),(0,[z0,z349,z2,z3,z4,z5])],[(0,[z0,z844,z2,z3,z4,z5]),(0,[z0,z1,z95,z4,z5,z6]),(0,[z0,z1,z268,z160,z5,z6]),(0,[z0,z424,z4,z81,z5,z6]),(0,[z0,z845,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z158]),(0,[z656,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z113,z5,z10]),(0,[z259,z2,z3,z5,z14,z10]),(0,[z0,z167,z2,z3,z122,z10]),(0,[z0,z790,z3,z81,z5,z6])],[(0,[z0,z2,z3,z751,z5,z6]),(0,[z0,z2,z3,z4,z5,z780]),(0,[z0,z200,z3,z63,z221,z6]),(0,[z0,z2,z3,z4,z5,z846]),(0,[z0,z64,z3,z4,z5,z134]),(0,[z0,z2,z3,z5,z840,z118])],[(0,[z0,z847,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z327]),(0,[z9,z410,z3,z41,z5,z6]),(0,[z0,z2,z3,z4,z5,z848]),(0,[z2,z3,z4,z159,z733,z6]),(0,[z0,z2,z3,z833,z5,z10]),(0,[z0,z217,z2,z4,z5,z13]),(0,[z0,z2,z3,z174,z5,z6]),(0,[z0,z2,z4,z5,z849,z6])],[(0,[z0,z2,z3,z850,z5,z6]),(0,[z0,z2,z3,z5,z60,z181]),(0,[z0,z2,z3,z4,z5,z851]),(0,[z0,z3,z4,z5,z804,z52]),(0,[z0,z2,z212,z4,z210,z6])]],
   [[(0,[z0,z2,z3,z852,z5,z6]),(0,[z0,z853,z2,z3,z4,z5]),(0,[z0,z1,z31,z4,z5,z6]),(0,[z0,z38,z4,z11,z5,z6])],[(0,[z0,z2,z3,z4,z6,z854]),(0,[z0,z2,z3,z4,z855,z6]),(0,[z0,z856,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z857])],[(0,[z770,z28,z3,z4,z5,z6]),(0,[z71,z2,z3,z72,z5,z10]),(0,[z0,z64,z3,z858,z5,z6])],[(0,[z0,z2,z3,z4,z5,z859]),(0,[z2,z3,z4,z679,z5,z10]),(0,[z0,z2,z3,z4,z5,z860]),(0,[z0,z8,z2,z3,z635,z5]),(0,[z0,z739,z2,z82,z5,z6])],[(0,[z0,z2,z234,z4,z206,z6]),(0,[z0,z497,z2,z4,z5,z323]),(0,[z0,z2,z3,z861,z4,z6]),(0,[z0,z2,z3,z4,z5,z862])],[(0,[z66,z86,z3,z4,z5,z14]),(0,[z0,z2,z863,z4,z5,z14]),(0,[z79,z0,z424,z4,z5,z6]),(0,[z0,z64,z4,z210,z5,z6])],[(0,[z0,z864,z3,z4,z5,z6]),(0,[z0,z2,z3,z865,z5,z6])],[(0,[z0,z2,z866,z4,z5,z6]),(0,[z22,z2,z3,z5,z60,z10]),(0,[z0,z2,z3,z4,z164,z662]),(0,[z468,z2,z3,z4,z5,z10]),(0,[z0,z252,z424,z2,z5,z6]),(0,[z0,z867,z2,z3,z4,z5]),(0,[z0,z2,z3,z868,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z67]),(0,[z106,z2,z74,z4,z5,z6]),(0,[z0,z2,z3,z5,z60,z14]),(0,[z458,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z869]),(0,[z0,z2,z3,z4,z5,z870]),(0,[z0,z2,z3,z4,z5,z871])],[(0,[z0,z358,z2,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z872]),(0,[z0,z873,z2,z3,z5,z6]),(0,[z0,z2,z3,z63,z5,z14]),(0,[z0,z569,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z874]),(0,[z0,z209,z2,z4,z825,z6])],[(0,[z0,z2,z3,z4,z5,z875]),(0,[z2,z3,z4,z5,z780,z6]),(0,[z0,z119,z4,z5,z565,z6])],[(0,[z0,z779,z3,z4,z5,z6]),(0,[z0,z2,z212,z4,z210,z10]),(0,[z0,z876,z3,z4,z5,z6])],[(0,[z0,z35,z410,z3,z5,z6]),(0,[z0,z410,z470,z4,z5,z6]),(0,[z0,z2,z371,z4,z5,z10]),(0,[z0,z1,z81,z82,z5,z6]),(0,[z0,z877,z3,z4,z5,z6])],[(0,[z0,z2,z470,z4,z206,z6]),(0,[z0,z2,z3,z4,z5,z228]),(0,[z559,z2,z3,z4,z5,z10])],[(0,[z0,z878,z2,z3,z4,z5]),(0,[z0,z410,z3,z4,z5,z14]),(0,[z0,z410,z3,z4,z5,z390])],[(0,[z0,z2,z3,z4,z879,z6]),(0,[z0,z2,z3,z788,z5,z6]),(0,[z0,z2,z3,z4,z206,z390]),(0,[z575,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z235])]],
   [[(0,[z87,z2,z88,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z880])],[(0,[z0,z2,z3,z4,z5,z881]),(0,[z0,z2,z4,z5,z882,z10])],[(0,[z0,z2,z3,z4,z5,z883]),(0,[z0,z259,z2,z3,z5,z60]),(0,[z0,z3,z4,z5,z718,z6]),(0,[z0,z200,z38,z4,z5,z6]),(0,[z0,z2,z3,z4,z125,z360]),(0,[z0,z8,z2,z3,z5,z840])],[(0,[z0,z2,z797,z4,z5,z6]),(0,[z0,z2,z884,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z885]),(0,[z0,z2,z3,z4,z5,z886]),(0,[z0,z790,z2,z3,z5,z6])],[(0,[z0,z2,z538,z82,z5,z6]),(0,[z106,z2,z74,z4,z5,z10]),(0,[z0,z157,z3,z4,z206,z6]),(0,[z0,z2,z3,z4,z887,z6]),(0,[z0,z2,z3,z4,z5,z248]),(0,[z0,z252,z569,z3,z5,z6]),(0,[z0,z2,z4,z5,z6,z888]),(1,[z0,z2,z4,z825,z6]),(0,[z0,z2,z889,z4,z5,z6])],[(0,[z0,z3,z4,z5,z801,z6])],[(0,[z0,z2,z3,z4,z5,z890]),(0,[z0,z891,z3,z4,z5,z6]),(0,[z0,z2,z892,z4,z5,z6]),(0,[z2,z3,z4,z5,z780,z10]),(0,[z229,z2,z3,z4,z5,z10]),(0,[z0,z124,z2,z4,z5,z628]),(0,[z0,z208,z3,z4,z11,z14])],[(0,[z0,z259,z2,z3,z5,z390]),(0,[z0,z62,z2,z3,z5,z19]),(0,[z0,z200,z3,z174,z221,z6])]],
   [[(0,[z0,z3,z4,z5,z6,z893])],[(0,[z0,z894,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z895,z6]),(0,[z9,z2,z3,z41,z5,z197])],[(0,[z0,z2,z3,z4,z5,z896])],[(0,[z0,z20,z2,z234,z5,z6]),(0,[z0,z3,z4,z5,z6,z897]),(0,[z0,z2,z3,z4,z6,z898]),(0,[z0,z899,z2,z3,z4,z5])],[(0,[z0,z2,z3,z900,z4,z6]),(0,[z0,z157,z234,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z901]),(0,[z0,z259,z2,z3,z5,z18]),(0,[z524,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z902,z6]),(0,[z0,z2,z3,z4,z5,z760]),(0,[z0,z903,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z6,z904]),(0,[z0,z2,z905,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z906]),(0,[z0,z148,z2,z3,z5,z14]),(0,[z0,z2,z3,z907,z5,z6])],[(0,[z0,z142,z3,z4,z5,z52]),(0,[z2,z3,z4,z5,z533,z14]),(0,[z0,z908,z2,z3,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z909]),(0,[z0,z148,z2,z3,z122,z6]),(0,[z2,z3,z4,z84,z5,z10]),(0,[z0,z8,z2,z3,z5,z60]),(0,[z0,z80,z3,z81,z5,z6]),(0,[z0,z25,z3,z4,z5,z804]),(1,[z0,z2,z3,z4,z744])],[(0,[z0,z910,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z911]),(0,[z0,z912,z3,z4,z5,z6]),(0,[z0,z64,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z913]),(0,[z9,z149,z2,z3,z5,z6]),(0,[z0,z914,z2,z3,z5,z6]),(0,[z0,z38,z2,z4,z5,z235])],[(0,[z0,z2,z3,z61,z5,z6]),(0,[z0,z2,z915,z4,z5,z6]),(0,[z0,z35,z2,z3,z5,z14]),(0,[z9,z2,z3,z41,z5,z6]),(0,[z0,z405,z80,z3,z81,z5])],[(0,[z71,z2,z3,z761,z5,z6]),(0,[z0,z2,z3,z4,z5,z916]),(0,[z0,z790,z80,z3,z5,z6])],[(0,[z0,z108,z2,z3,z4,z130]),(0,[z0,z20,z790,z3,z5,z6]),(0,[z0,z260,z2,z3,z4,z539]),(0,[z0,z917,z3,z4,z5,z6])],[(0,[z0,z104,z4,z81,z5,z6]),(0,[z0,z2,z3,z4,z5,z918]),(0,[z2,z741,z88,z4,z5,z6]),(0,[z0,z2,z4,z5,z14,z919]),(0,[z0,z124,z2,z4,z5,z760])],[(0,[z0,z2,z3,z4,z5,z920]),(0,[z0,z2,z3,z921,z5,z6]),(0,[z0,z790,z3,z4,z5,z6])]],
   [[(0,[z0,z814,z2,z3,z61,z5]),(0,[z0,z2,z3,z4,z922,z6]),(0,[z9,z0,z455,z2,z3,z5]),(0,[z0,z923,z2,z3,z4,z10]),(0,[z0,z924,z2,z3,z4,z5]),(0,[z0,z2,z3,z735,z5,z14]),(0,[z0,z2,z3,z4,z5,z925]),(0,[z0,z926,z3,z4,z5,z6]),(0,[z0,z927,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z928]),(0,[z0,z929,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z181]),(0,[z9,z2,z3,z41,z255,z6])],[(0,[z0,z2,z3,z4,z5,z930]),(0,[z0,z2,z3,z4,z931,z6]),(0,[z92,z2,z3,z4,z159,z6]),(0,[z0,z2,z3,z5,z932,z10])],[(0,[z0,z2,z3,z4,z933,z6]),(0,[z0,z934,z3,z4,z5,z6]),(0,[z0,z2,z3,z935,z5,z6]),(0,[z291,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z936,z6]),(0,[z0,z64,z3,z4,z5,z10]),(0,[z0,z736,z4,z160,z5,z6]),(0,[z0,z648,z3,z81,z5,z6]),(0,[z0,z20,z569,z3,z5,z6]),(0,[z0,z937,z2,z3,z4,z5])],[(0,[z0,z2,z3,z841,z5,z6]),(0,[z0,z20,z2,z3,z206,z6]),(0,[z461,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z114,z126]),(0,[z0,z109,z3,z4,z5,z6]),(0,[z0,z938,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z939]),(0,[z940,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z941,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z942,z6]),(0,[z149,z2,z3,z4,z5,z10]),(1,[z0,z790,z3,z5,z6])],[(0,[z0,z2,z470,z4,z5,z6]),(0,[z0,z2,z3,z758,z5,z14])],[(0,[z0,z2,z3,z113,z5,z6]),(0,[z0,z943,z2,z3,z4,z5]),(0,[z0,z3,z4,z5,z263,z134]),(0,[z0,z167,z2,z3,z122,z6])],[(0,[z0,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z390])],[(0,[z0,z2,z234,z4,z5,z10]),(0,[z0,z2,z3,z268,z5,z14]),(0,[z203,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z944,z5,z6])],[(0,[z0,z2,z4,z5,z10,z945])],[(0,[z0,z2,z3,z4,z5,z946])],[(0,[z0,z947,z2,z4,z5,z6]),(0,[z0,z2,z948,z4,z5,z6]),(0,[z0,z2,z3,z81,z206,z6]),(0,[z92,z2,z3,z4,z159,z10]),(0,[z0,z1,z4,z160,z5,z14]),(0,[z0,z2,z949,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z950])]],
   [[(0,[z0,z2,z470,z4,z255,z6])],[(0,[z0,z2,z951,z3,z5,z6]),(0,[z71,z2,z3,z72,z5,z6]),(1,[z2,z3,z4,z5,z780]),(0,[z0,z952,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z255,z14]),(0,[z0,z2,z3,z4,z255,z390]),(0,[z0,z2,z3,z4,z5,z953]),(0,[z0,z109,z3,z4,z5,z10])],[(0,[z71,z2,z3,z5,z332,z6]),(0,[z0,z209,z2,z4,z57,z14]),(0,[z0,z200,z349,z3,z4,z221]),(0,[z0,z37,z2,z540,z4,z5]),(0,[z954,z2,z3,z4,z5,z6])],[(0,[z0,z310,z2,z3,z5,z296]),(0,[z0,z2,z3,z4,z5,z955]),(0,[z0,z24,z490,z3,z4,z5]),(0,[z2,z3,z4,z5,z956,z6])],[(0,[z0,z2,z470,z4,z5,z10]),(0,[z2,z3,z4,z5,z204,z10]),(0,[z0,z2,z3,z4,z125,z662]),(0,[z0,z352,z3,z4,z5,z48]),(0,[z957,z2,z3,z4,z5,z6])],[(0,[z0,z410,z3,z4,z206,z6]),(0,[z0,z958,z2,z3,z4,z6]),(0,[z0,z349,z38,z2,z4,z5]),(0,[z0,z2,z4,z825,z57,z6])],[(0,[z0,z2,z234,z81,z5,z6]),(0,[z0,z959,z3,z4,z5,z6]),(0,[z0,z960,z2,z4,z5,z6]),(0,[z0,z119,z120,z4,z5,z14]),(0,[z0,z640,z2,z3,z122,z6])]],
   [[(0,[z0,z2,z3,z4,z961,z6]),(0,[z0,z358,z2,z4,z5,z6]),(0,[z0,z962,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z963]),(0,[z0,z964,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z965,z6]),(0,[z0,z966,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z967])],[(0,[z66,z35,z86,z3,z5,z6]),(0,[z0,z2,z3,z202,z206,z6]),(0,[z0,z2,z3,z4,z5,z968]),(0,[z50,z2,z3,z4,z220,z51]),(0,[z207,z2,z3,z4,z5,z10]),(0,[z0,z969,z3,z4,z5,z6])],[(0,[z0,z2,z3,z5,z14,z970]),(0,[z0,z2,z371,z4,z5,z6])],[(0,[z0,z157,z3,z4,z5,z10]),(0,[z0,z971,z3,z4,z5,z6]),(0,[z0,z252,z1,z160,z5,z6])],[(0,[z541,z2,z3,z4,z5,z14])],[(0,[z0,z410,z234,z4,z5,z6]),(0,[z0,z38,z2,z4,z5,z14]),(0,[z0,z2,z3,z972,z5,z6])],[(0,[z92,z2,z3,z4,z733,z6]),(0,[z973,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z4,z5,z882,z6]),(0,[z0,z2,z3,z4,z5,z974]),(0,[z238,z2,z3,z4,z5,z10]),(0,[z0,z124,z2,z4,z5,z293])],[(0,[z0,z975,z2,z3,z4,z5]),(0,[z106,z2,z741,z4,z5,z6]),(0,[z2,z3,z4,z761,z5,z6]),(0,[z0,z2,z3,z4,z5,z51])],[(0,[z0,z2,z3,z4,z5,z976])],[(0,[z0,z717,z2,z4,z5,z6])],[(0,[z0,z200,z3,z4,z221,z14]),(0,[z0,z12,z739,z2,z5,z6]),(0,[z0,z2,z3,z4,z5,z977])],[(0,[z0,z2,z827,z4,z5,z6]),(0,[z0,z3,z4,z11,z302,z6]),(0,[z978,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z979])],[(0,[z2,z3,z4,z5,z10,z560]),(0,[z0,z24,z259,z2,z3,z5]),(0,[z0,z548,z3,z81,z5,z6]),(0,[z79,z0,z20,z371,z5,z6]),(0,[z0,z2,z3,z4,z5,z980]),(0,[z0,z2,z981,z4,z5,z6])],[(0,[z0,z119,z307,z4,z5,z6]),(0,[z0,z265,z64,z3,z4,z5])]],
   [[(0,[z87,z2,z88,z4,z5,z382]),(0,[z0,z424,z2,z4,z5,z10]),(0,[z0,z12,z77,z2,z5,z10]),(0,[z0,z29,z2,z3,z4,z273]),(0,[z2,z3,z4,z5,z488,z14])],[(0,[z0,z2,z3,z4,z5,z982]),(0,[z0,z983,z2,z3,z4,z5]),(0,[z71,z2,z3,z386,z5,z6]),(0,[z0,z148,z2,z3,z202,z6]),(0,[z79,z0,z252,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z984])],[(0,[z0,z985,z3,z4,z5,z6]),(0,[z2,z3,z72,z761,z5,z6]),(0,[z207,z2,z3,z4,z220,z6]),(0,[z79,z0,z20,z3,z5,z14]),(0,[z0,z2,z3,z4,z5,z986]),(0,[z0,z739,z2,z133,z5,z6]),(0,[z0,z739,z2,z4,z5,z6])],[(0,[z269,z2,z3,z4,z5,z10])],[(0,[z667,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z987])],[(0,[z0,z988,z3,z4,z5,z6])],[(0,[z0,z989,z3,z4,z5,z6]),(0,[z0,z990,z2,z3,z4,z5]),(0,[z0,z2,z3,z214,z400,z6]),(0,[z0,z209,z64,z4,z57,z6])],[(0,[z0,z3,z4,z5,z263,z6]),(0,[z0,z260,z2,z3,z4,z439])]],
   [[(0,[z0,z2,z3,z4,z5,z991]),(0,[z22,z2,z3,z4,z5,z780]),(0,[z0,z992,z2,z3,z4,z5]),(0,[z993,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z994]),(0,[z0,z995,z3,z4,z5,z6])],[(0,[z86,z770,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z996]),(0,[z0,z200,z3,z4,z261,z6])],[(0,[z0,z997,z2,z3,z5,z6]),(0,[z0,z998,z2,z3,z4,z10]),(0,[z0,z999,z2,z4,z5,z10]),(0,[z0,z24,z3,z407,z4,z5])],[],[(0,[z0,z2,z3,z4,z5,z1000]),(0,[z0,z12,z569,z4,z5,z6]),(0,[z0,z260,z2,z3,z4,z273])],[(0,[z0,z2,z3,z761,z5,z6])],[(0,[z242,z2,z74,z4,z5,z6]),(0,[z0,z259,z25,z2,z3,z5])],[(0,[z27,z28,z3,z4,z5,z14]),(0,[z0,z923,z2,z3,z4,z6]),(0,[z0,z2,z3,z5,z296,z181]),(0,[z0,z3,z4,z5,z10,z897]),(0,[z0,z2,z3,z767,z122,z6])]],
   [[(0,[z0,z2,z3,z1001,z5,z6]),(0,[z144,z2,z3,z4,z5,z10]),(0,[z0,z24,z3,z4,z5,z508]),(0,[z2,z3,z4,z5,z1002,z6])],[(0,[z0,z2,z234,z4,z5,z197]),(0,[z0,z2,z3,z4,z5,z1003]),(0,[z0,z988,z3,z4,z5,z10]),(0,[z0,z2,z4,z5,z13,z760])],[(0,[z0,z2,z3,z1004,z5,z6]),(0,[z0,z2,z3,z5,z932,z6]),(0,[z0,z2,z3,z4,z10,z904]),(0,[z0,z2,z3,z4,z5,z134]),(0,[z0,z2,z3,z214,z202,z6]),(0,[z0,z1005,z3,z4,z5,z6])],[(0,[z27,z358,z28,z4,z5,z6]),(0,[z0,z2,z3,z4,z206,z6]),(0,[z0,z2,z3,z4,z5,z1006]),(0,[z0,z3,z4,z5,z263,z10]),(0,[z0,z2,z3,z4,z5,z1007]),(0,[z0,z455,z2,z3,z4,z5]),(0,[z0,z209,z4,z263,z57,z6]),(0,[z0,z2,z3,z4,z5,z1008]),(0,[z0,z7,z2,z3,z5,z118]),(0,[z0,z2,z3,z4,z5,z840])],[(0,[z0,z2,z3,z1009,z5,z6]),(0,[z0,z2,z1010,z3,z5,z6]),(0,[z0,z77,z424,z2,z5,z6]),(1,[z0,z2,z3,z767,z6]),(0,[z0,z2,z3,z4,z6,z744])],[(0,[z66,z86,z3,z4,z5,z10]),(0,[z0,z2,z3,z4,z125,z49])],[(0,[z691,z2,z3,z4,z5,z14]),(0,[z0,z820,z2,z3,z5,z6])],[(0,[z0,z2,z3,z174,z5,z14]),(0,[z0,z2,z3,z1011,z5,z6]),(0,[z0,z1012,z2,z3,z5,z6]),(0,[z0,z3,z4,z5,z48,z804])]],
   [[(0,[z0,z2,z1013,z4,z5,z6]),(0,[z0,z2,z3,z5,z296,z390]),(0,[z0,z2,z212,z4,z210,z14]),(0,[z2,z3,z4,z5,z696,z14]),(0,[z0,z1,z189,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1014]),(0,[z0,z2,z3,z858,z5,z6])],[(0,[z0,z2,z1015,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1016]),(0,[z71,z2,z3,z72,z5,z158]),(0,[z0,z569,z3,z4,z5,z10]),(0,[z699,z2,z3,z4,z5,z14]),(0,[z0,z2,z3,z4,z5,z1017]),(0,[z0,z2,z3,z4,z5,z1018])],[(0,[z0,z2,z470,z4,z5,z197]),(0,[z0,z2,z3,z4,z744,z273])],[(0,[z0,z2,z3,z4,z1019,z6]),(0,[z66,z770,z3,z4,z5,z6]),(0,[z0,z2,z234,z4,z5,z6]),(0,[z106,z2,z74,z4,z5,z196]),(0,[z0,z259,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1020]),(0,[z0,z2,z3,z4,z5,z1021]),(0,[z297,z2,z3,z4,z5,z10])],[(0,[z0,z2,z3,z4,z5,z1022]),(0,[z0,z1023,z2,z3,z4,z5]),(0,[z0,z569,z4,z82,z5,z6]),(0,[z0,z2,z3,z202,z767,z6])],[(0,[z0,z410,z3,z4,z5,z10]),(0,[z0,z2,z3,z1004,z5,z10]),(0,[z0,z2,z3,z214,z202,z10])],[(0,[z0,z2,z4,z5,z6,z919]),(0,[z0,z2,z3,z4,z206,z10]),(0,[z0,z2,z3,z4,z5,z1024]),(1,[z2,z3,z4,z733,z6]),(0,[z0,z259,z600,z2,z3,z5]),(0,[z0,z260,z2,z3,z4,z744])]],
   [[(0,[z0,z1025,z3,z4,z5,z6]),(0,[z0,z736,z2,z4,z5,z6])],[(0,[z0,z104,z2,z4,z5,z6]),(0,[z106,z2,z74,z4,z5,z14]),(0,[z0,z7,z2,z3,z5,z181]),(0,[z0,z2,z3,z4,z5,z1026]),(0,[z0,z25,z3,z4,z5,z507]),(0,[z0,z1027,z2,z3,z4,z5]),(0,[z0,z1028,z3,z4,z5,z6]),(0,[z0,z265,z3,z4,z5,z263]),(0,[z0,z2,z3,z5,z767,z6])],[(0,[z0,z2,z234,z4,z255,z6]),(0,[z0,z1029,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z5,z382]),(1,[z2,z741,z4,z5,z6]),(0,[z0,z2,z133,z82,z5,z6])],[(0,[z0,z1030,z2,z3,z5,z10]),(0,[z357,z2,z3,z4,z5,z14]),(0,[z0,z569,z3,z81,z5,z6])],[(0,[z0,z217,z2,z4,z5,z195]),(0,[z0,z2,z3,z4,z5,z1031])],[(0,[z0,z208,z3,z4,z11,z10]),(0,[z0,z142,z3,z4,z5,z70]),(0,[z1032,z2,z3,z4,z5,z6]),(0,[z0,z2,z1033,z4,z5,z6])],[(0,[z0,z259,z2,z3,z5,z10]),(0,[z431,z2,z3,z4,z5,z14]),(0,[z0,z25,z3,z4,z5,z48]),(1,[z0,z739,z2,z5,z6]),(0,[z0,z209,z265,z2,z4,z57])]],
   [[(0,[z2,z3,z4,z733,z220,z6]),(0,[z0,z2,z4,z5,z1034,z6])],[(0,[z0,z2,z3,z1035,z5,z6]),(0,[z0,z1036,z2,z3,z5,z6]),(0,[z0,z410,z3,z81,z5,z6]),(0,[z0,z2,z3,z4,z5,z1037]),(0,[z0,z2,z805,z4,z5,z6]),(0,[z0,z2,z3,z5,z1038,z6]),(0,[z0,z2,z3,z4,z5,z1039]),(0,[z0,z2,z3,z5,z6,z840])],[(0,[z0,z1040,z2,z3,z4,z5]),(0,[z0,z1041,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1042]),(0,[z0,z2,z3,z4,z126,z744])],[(0,[z0,z157,z3,z4,z5,z6]),(0,[z657,z2,z3,z4,z5,z10]),(0,[z0,z2,z3,z1043,z5,z6]),(0,[z0,z2,z1044,z4,z5,z6])],[(0,[z0,z252,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1045]),(0,[z0,z209,z2,z4,z134,z57]),(0,[z0,z1046,z2,z4,z5,z6])],[(0,[z0,z104,z2,z4,z5,z10]),(0,[z0,z562,z120,z4,z5,z6])],[],[(0,[z0,z2,z3,z4,z5,z413]),(0,[z106,z2,z74,z4,z5,z327]),(0,[z0,z2,z133,z82,z5,z10])]],
   [[(0,[z0,z1047,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z1048,z6]),(0,[z0,z1049,z3,z4,z5,z6]),(0,[z50,z2,z3,z4,z220,z6])],[(0,[z2,z770,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1050]),(0,[z71,z0,z455,z2,z3,z5]),(0,[z0,z2,z4,z5,z760,z247])],[(0,[z0,z157,z3,z4,z255,z6])],[(0,[z0,z35,z2,z3,z5,z10]),(0,[z0,z2,z3,z1051,z5,z6])],[(0,[z0,z1,z3,z174,z5,z6]),(0,[z0,z2,z3,z4,z5,z1052]),(0,[z0,z330,z3,z81,z5,z6]),(0,[z0,z3,z4,z718,z221,z6])],[(0,[z518,z2,z3,z4,z5,z14]),(0,[z304,z2,z3,z4,z5,z14]),(1,[z0,z2,z4,z5,z760])],[(0,[z2,z3,z761,z41,z5,z6]),(0,[z0,z2,z3,z4,z5,z1053]),(0,[z2,z3,z4,z5,z10,z695])],[(0,[z0,z2,z1054,z4,z5,z6]),(0,[z0,z1055,z3,z4,z5,z6]),(0,[z0,z424,z2,z4,z5,z6]),(0,[z0,z736,z1,z4,z5,z6]),(0,[z0,z12,z77,z2,z5,z6])]],
   [[(0,[z0,z1056,z3,z4,z5,z6]),(0,[z0,z252,z2,z3,z5,z10]),(0,[z0,z2,z3,z4,z10,z854]),(0,[z0,z2,z3,z4,z5,z1057]),(0,[z0,z3,z4,z5,z1058,z6])],[(0,[z0,z80,z3,z81,z5,z14])],[(0,[z0,z975,z2,z3,z61,z5]),(0,[z9,z2,z470,z41,z5,z6]),(0,[z0,z64,z3,z4,z5,z14]),(0,[z0,z2,z4,z5,z313,z6]),(0,[z0,z200,z38,z4,z221,z6]),(0,[z0,z1059,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z1060,z6])],[(0,[z0,z2,z3,z4,z5,z1061])],[(0,[z0,z2,z3,z61,z5,z14]),(0,[z9,z2,z3,z41,z5,z390]),(0,[z9,z2,z3,z41,z5,z14]),(0,[z50,z2,z3,z4,z220,z10]),(0,[z0,z2,z3,z4,z5,z1062]),(0,[z0,z2,z3,z5,z6,z970]),(0,[z0,z839,z2,z3,z5,z6]),(0,[z2,z3,z4,z1063,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1064])],[(0,[z0,z142,z259,z2,z3,z5]),(0,[z0,z600,z3,z4,z5,z553]),(0,[z0,z2,z3,z4,z767,z6])],[(0,[z2,z3,z4,z5,z14,z10]),(0,[z0,z2,z3,z4,z5,z1065]),(0,[z1066,z0,z2,z3,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z1067,z6]),(0,[z0,z2,z4,z210,z825,z6])],[(0,[z0,z998,z2,z3,z4,z6]),(0,[z144,z86,z3,z4,z5,z6]),(0,[z0,z148,z2,z3,z206,z6]),(0,[z0,z999,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z804])],[(0,[z0,z2,z3,z4,z5,z1068]),(0,[z0,z2,z3,z4,z5,z1069]),(0,[z0,z2,z1070,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1071]),(0,[z71,z2,z3,z379,z5,z6]),(0,[z284,z2,z3,z4,z159,z6]),(0,[z0,z2,z4,z5,z6,z760])],[(0,[z0,z2,z3,z4,z5,z10]),(0,[z0,z770,z3,z4,z5,z6]),(0,[z177,z2,z3,z4,z5,z14]),(0,[z0,z2,z1072,z4,z5,z6])],[(0,[z27,z104,z28,z4,z5,z6]),(0,[z92,z2,z3,z4,z159,z14]),(0,[z0,z2,z3,z268,z5,z10]),(0,[z0,z2,z3,z4,z5,z1073])],[],[(0,[z0,z1074,z2,z3,z4,z6]),(0,[z0,z2,z3,z1075,z5,z6]),(0,[z0,z2,z4,z5,z313,z10])],[(0,[z0,z2,z3,z4,z5,z1076]),(0,[z79,z0,z35,z3,z5,z6]),(0,[z0,z1,z4,z160,z5,z10]),(0,[z0,z109,z3,z4,z5,z14]),(0,[z1077,z2,z3,z4,z5,z6])]],
   [[(0,[z418,z2,z3,z4,z5,z10]),(0,[z0,z1078,z2,z3,z4,z6]),(0,[z0,z2,z3,z5,z296,z840])],[(0,[z0,z1079,z3,z4,z5,z6]),(0,[z71,z2,z3,z72,z5,z181]),(0,[z0,z2,z3,z4,z5,z1080])],[(0,[z0,z2,z470,z4,z5,z14]),(0,[z0,z2,z3,z4,z255,z10]),(0,[z0,z2,z1081,z4,z5,z6]),(1,[z2,z3,z761,z5,z6]),(0,[z0,z29,z2,z3,z4,z163]),(0,[z0,z205,z3,z4,z5,z508]),(0,[z0,z2,z1082,z4,z5,z6]),(0,[z0,z2,z3,z1083,z5,z6])],[(0,[z0,z1084,z2,z3,z5,z6]),(0,[z0,z410,z3,z4,z5,z197]),(0,[z0,z2,z1085,z4,z5,z6]),(0,[z0,z2,z3,z113,z5,z14]),(0,[z0,z209,z2,z4,z57,z10]),(0,[z0,z167,z2,z3,z122,z14]),(0,[z0,z12,z252,z2,z5,z6])],[(0,[z66,z86,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z1086,z6]),(0,[z0,z2,z3,z4,z206,z197]),(0,[z0,z2,z863,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1087])],[(0,[z0,z3,z4,z5,z1088,z6]),(0,[z0,z2,z1089,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1090])],[(0,[z0,z2,z3,z4,z5,z1091]),(0,[z0,z2,z3,z5,z60,z6]),(0,[z0,z2,z3,z5,z783,z10]),(0,[z0,z260,z2,z3,z4,z130])]],
   [[(0,[z0,z569,z3,z4,z5,z6]),(0,[z0,z2,z3,z63,z5,z6]),(0,[z0,z1092,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1093]),(0,[z0,z497,z2,z4,z5,z247])],[(0,[z0,z35,z3,z81,z5,z6]),(0,[z71,z2,z3,z72,z5,z14]),(0,[z2,z3,z5,z60,z14,z10]),(0,[z1094,z2,z3,z4,z5,z6])],[(0,[z0,z167,z2,z3,z206,z6]),(0,[z0,z1095,z2,z3,z4,z5]),(0,[z0,z1096,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z5,z1097]),(0,[z0,z2,z3,z4,z5,z1098])],[],[(0,[z0,z410,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z10,z117])],[(0,[z50,z2,z3,z4,z220,z107]),(0,[z0,z38,z2,z4,z5,z10]),(0,[z0,z2,z3,z4,z5,z1099]),(0,[z0,z24,z3,z4,z5,z804])],[(0,[z0,z2,z3,z1100,z5,z6]),(0,[z0,z2,z3,z4,z5,z1101]),(0,[z87,z2,z88,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1102]),(0,[z0,z1084,z2,z3,z5,z10]),(0,[z0,z252,z3,z81,z5,z6]),(0,[z0,z37,z2,z4,z5,z247])]],
   [[(0,[z0,z2,z3,z4,z1103,z6]),(0,[z1104,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z1105,z6])],[(0,[z0,z358,z2,z4,z5,z14]),(0,[z0,z808,z2,z4,z5,z6]),(0,[z0,z12,z77,z109,z5,z6]),(0,[z0,z12,z77,z569,z5,z6]),(0,[z0,z2,z3,z4,z5,z1106])],[(0,[z0,z2,z3,z4,z5,z1107]),(0,[z0,z7,z2,z3,z5,z840])],[(0,[z27,z28,z3,z4,z5,z413]),(0,[z0,z1030,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z60,z10]),(0,[z0,z2,z3,z4,z5,z1108]),(0,[z0,z2,z4,z5,z825,z6]),(0,[z0,z209,z64,z4,z5,z6])],[(0,[z0,z2,z1109,z4,z5,z6]),(0,[z0,z410,z3,z4,z255,z6]),(0,[z0,z1110,z3,z4,z5,z6]),(0,[z0,z2,z3,z63,z5,z10]),(0,[z0,z2,z371,z4,z5,z14]),(0,[z0,z669,z20,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z1111])],[(0,[z0,z2,z3,z4,z5,z107]),(0,[z2,z3,z4,z474,z5,z10]),(0,[z0,z208,z3,z4,z11,z6])],[(0,[z50,z148,z2,z3,z220,z6]),(0,[z0,z2,z4,z5,z6,z945]),(0,[z477,z2,z3,z4,z5,z10]),(0,[z0,z405,z2,z3,z4,z5])],[(0,[z0,z119,z472,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z835]),(0,[z0,z310,z2,z3,z5,z440]),(0,[z0,z2,z3,z1112,z5,z6]),(0,[z0,z2,z1113,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 542) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 542).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1077).take 97) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1174)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [542, 535, 97] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 138).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 138).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [138, 118] = true :=
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

end PEqualNP.Outside.L_meta_41018

theorem PEqualNP.Outside.L_meta_41018 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4270376960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4270376960) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41018.solve