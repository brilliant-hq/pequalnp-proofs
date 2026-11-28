import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_38999

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
  Nat.testBit (4008241320 * 2 ^ 32 + 4001949832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000c1a14d10d4354#64 ++ 0x00030685344350d5#64 ++ 0xfd1c3e3ff31fc7ff#64 ++ 0xbf470f8ffcc7f1ff#64 : BitVec 256),
   (0x0461c4ca246298a8#64 ++ 0x011871328918a62a#64 ++ 0xfee3c7ce3ce3f8ff#64 ++ 0xffb8f1f38f38fe3f#64 : BitVec 256),
   (0x3302e9634f032d30#64 ++ 0x4cc0ba58d3c0cb4c#64 ++ 0x7703f9f3cf033f32#64 ++ 0xddc0fe7cf3c0cfcc#64 : BitVec 256),
   (0x8bb401bc0ab436c0#64 ++ 0x22ed006f02ad0db0#64 ++ 0xbffc01fc0ffc3fc0#64 ++ 0xefff007f03ff0ff0#64 : BitVec 256),
   (0x53db7e000fdbc000#64 ++ 0x94f6df8003f6f000#64 ++ 0xdbfffe000fffc000#64 ++ 0xf6ffff8003fff000#64 : BitVec 256),
   (0xe3ffb7ffb0000001#64 ++ 0x38ffedffec000000#64 ++ 0xe3fffffff0000000#64 ++ 0xf8fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [9, 4]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [2, 5]⟩, ⟨.or, [12, 3]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z1 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z2 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z3 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z4 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x03fc01f00ffc3f00 0x40ff007c03ff0fc0

def z5 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z6 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xe3fffffff0000000 0xf8fffffffc000000

def z7 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x140000000f033f32 0x0500000003c0cfcc

def z8 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z9 : W := mkw 0xf3ffffffff032d31 0x7cffffffffc0cb4c 0xf7ffffffff033f32 0xfdffffffffc0cfcc

def z10 : W := mkw 0x000000000a900000 0x0000000002a40000 0x180000000ffc0000 0x0600000003ff0000

def z11 : W := mkw 0x43db36000a900000 0x10f6cd8002a40000 0xdbfffe000ffc0000 0xf6ffff8003ff0000

def z12 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xfffffffffffc3fc0 0xffffffffffff0ff0

def z13 : W := mkw 0x8bb001a80ab03480 0x22ec006a02ac0d20 0x37e001f00fe03f00 0xcdf8007c03f80fc0

def z14 : W := mkw 0x0000804200000820 0x0000201080000208 0x240001c200003832 0x0900007080000e0c

def z15 : W := mkw 0x634bb763b0000001 0x18d2edd8ec000000 0x6303fff3f0000000 0xd8c0fffcfc000000

def z16 : W := mkw 0x88b4009c00b412c0 0x222d0027002d04b0 0x88fc000c00fc00c0 0x223f0003003f0030

def z17 : W := mkw 0x2002a04300000000 0x0800a810c0000000 0x4003f803c0000000 0x1000fe00f0000000

def z18 : W := mkw 0x882c1bbcd12d77d4 0x220b06ef344b5df5 0xfd1c3ffff31fffff 0xbf470ffffcc7ffff

def z19 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z20 : W := mkw 0x04004800456fdbfc 0x01001200115bf6ff 0x1c0000000fffffff 0x0700000003ffffff

def z21 : W := mkw 0x000c121490000000 0x0003048524000000 0xe11c3e3ff0000000 0xb8470f8ffc000000

def z22 : W := mkw 0xe3f3a5eb20000001 0x38fce97ac8000000 0x02e3c1c000000000 0x40b8f07000000000

def z23 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0x4003fe03f0000000 0x1000ff80fc000000

def z24 : W := mkw 0x57fbfeca2ffbd8a8 0x95feffb28bfef62a 0xffffffce3ffff8ff 0xfffffff38ffffe3f

def z25 : W := mkw 0x080000000ab436c0 0x0200000002ad0db0 0x1c0000000ffc3fc0 0x0700000003ff0ff0

def z26 : W := mkw 0x0000c04204020820 0x0000301081008208 0x7603c1c20c033832 0xdd80f0708300ce0c

def z27 : W := mkw 0x3763edeb6f63bdb8 0x4dd8fb7adbd8ef6e 0xffe3ffffffe3ffff 0xfff8fffffff8ffff

def z28 : W := mkw 0x8bf545bc0ef6b6c0 0x22fd516f03bdadb0 0xffffc7fc0fffffc0 0xfffff1ff03fffff0

def z29 : W := mkw 0x042080ca202018a8 0x010820328808062a 0x240001ce300038ff 0x090000738c000e3f

def z30 : W := mkw 0x73dbff634fdbed30 0xdcf6ffd8d3f6fb4c 0xfffffff3cfffff32 0xfffffffcf3ffffcc

def z31 : W := mkw 0x039000000a900000 0x00e4000002a40000 0x011c0000031c0000 0x0047000000c70000

def z32 : W := mkw 0xa82481ff40243ff0 0x6a09207fd0090ffc 0x240001ffc0003ff2 0x0900007ff0000ffc

def z33 : W := mkw 0x0441c44224428828 0x011071108910a20a 0x0003c00000000000 0x0000f00000000000

def z34 : W := mkw 0x330269214f032510 0x4cc09a4853c0c944 0x5303f831cf030700 0xd4c0fe0c73c0c1c0

def z35 : W := mkw 0x2000816340002d30 0x48002058d0000b4c 0x240001f3c0003f32 0x0900007cf0000fcc

def z36 : W := mkw 0xc0fd169cb0000001 0x303f45a72c000000 0x80fc060c30000000 0x203f01830c000000

def z37 : W := mkw 0x88b4009c0ab436c0 0x222d002702ad0db0 0x9cfc000c0ffc3fc0 0x273f000303ff0ff0

def z38 : W := mkw 0x0004001400040240 0x0001000500010090 0x2400003c000007c0 0x0900000f000001f0

def z39 : W := mkw 0x00040014d0040354 0x00010005340100d5 0x2400003ff00007ff 0x0900000ffc0001ff

def z40 : W := mkw 0x0004001400040240 0x0001000500010090 0xbd1c003c031c07c0 0xaf47000f00c701f0

def z41 : W := mkw 0xe3f7a5ff20000001 0x38fde97fc8000000 0xa3ffc1fc00000000 0xe8fff07f00000000

def z42 : W := mkw 0x0441c44224428828 0x011071108910a20a 0x7603c7c23c03f83f 0xdd80f1f08f00fe0f

def z43 : W := mkw 0x882401bc002436c0 0x2209006f00090db0 0x240001fc00003fc0 0x0900007f00000ff0

def z44 : W := mkw 0xa02481ffb0000001 0x2809207fec000000 0x200001fff0000000 0x0800007ffc000000

def z45 : W := mkw 0x042480def0241bfc 0x01092037bc0906ff 0x240001fff0003fff 0x0900007ffc000fff

def z46 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x0203c1c000000000 0x4080f07000000000

def z47 : W := mkw 0x83b401bc00000000 0x20ed006f00000000 0xa3fc01fc00000000 0xe8ff007f00000000

def z48 : W := mkw 0x0461048820609088 0x0118412208182422 0x00e0000000e00000 0x0038000000380000

def z49 : W := mkw 0x030001200a002400 0x00c0004802800900 0x0100003003000700 0x0040000c00c001c0

def z50 : W := mkw 0xbbb629bd4bb537d0 0x6eed8a6f52ed4df4 0xbffc39fdcffc3fc0 0xefff0e7f73ff0ff0

def z51 : W := mkw 0x0041440004428000 0x001051000110a000 0xdae3c6000ce3c000 0xf6b8f1800338f000

def z52 : W := mkw 0x539a3a000b994000 0x94e68e8002e65000 0x011c3800031c0000 0x00470e0000c70000

def z53 : W := mkw 0x600a320190000001 0x18028c8064000000 0x00003801c0000000 0x00000e0070000000

def z54 : W := mkw 0x504b7e00054bc000 0x9412df800152f000 0xdae3fe000ce3c000 0xf6b8ff800338f000

def z55 : W := mkw 0xf39e3b359b994001 0xbce78ecd66e65000 0x011c3831c31c0000 0x00470e0c70c70000

def z56 : W := mkw 0x0008120000084000 0x0002048000021000 0x881c0600001cc000 0x2207018000073000

def z57 : W := mkw 0x73d3ed634fd3ad30 0xdcf4fb58d3f4eb4c 0x77e3f9f3cfe33f32 0xddf8fe7cf3f8cfcc

def z58 : W := mkw 0x8bf585fe2ab436c0 0x22fd617f8aad0db0 0xffffc7fe3ffc3fc0 0xfffff1ff8fff0ff0

def z59 : W := mkw 0x0061c4ca24428000 0x001871328910a000 0xfae3c7ce3ce3c000 0xfeb8f1f38f38f000

def z60 : W := mkw 0x0041440004428000 0x001051000110a000 0x02e3c0000ce00000 0x40b8f00003380000

def z61 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xdae3c7c00ce3f800 0xf6b8f1f00338fe00

def z62 : W := mkw 0xe3ff37bdb0000001 0x38ffcdef6c000000 0x81fc3e3df0000000 0x207f0f8f7c000000

def z63 : W := mkw 0x77fbffeb6ffbfdb8 0xddfefffadbfeff6e 0xffffffffffffffff 0xffffffffffffffff

def z64 : W := mkw 0xe3ffb7ffb0201081 0x38ffedffec080420 0xfffffffffce038c0 0xffffffffff380e30

def z65 : W := mkw 0x00081a00d1094114 0x0002068034425045 0x40003e03f003c03f 0x10000f80fc00f00f

def z66 : W := mkw 0x039000000a900000 0x00e4000002a40000 0x9bfc00000ffc0000 0xe6ff000003ff0000

def z67 : W := mkw 0x0000080041010110 0x0000020010404044 0x75003833c3030732 0x9d400e0cf0c0c1cc

def z68 : W := mkw 0x53db76000edac000 0x94f6dd8003b6b000 0x8affc6000cfcc000 0x62bff180033f3000

def z69 : W := mkw 0xbbbefbffdfbf7ff4 0x6eefbefff7efdffd 0xffffffffffffffff 0xffffffffffffffff

def z70 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x411c3e33f31fc73f 0x10470f8cfcc7f1cf

def z71 : W := mkw 0x00081a0001094000 0x0002068000425000 0xd91c3e00031fc000 0xb6470f8000c7f000

def z72 : W := mkw 0x8804013400042640 0x2201004d00010990 0x0000003000000700 0x0000000c000001c0

def z73 : W := mkw 0xe7fff7ffb46298a9 0x39fffdffed18a62a 0xfffffffffce3f8ff 0xffffffffff38fe3f

def z74 : W := mkw 0x9bb449bc0ffff6c0 0xa6ed126f03fffdb0 0xbffc01fc0fffffc0 0xefff007f03fffff0

def z75 : W := mkw 0x230eb37790000000 0x08c3acdde4000000 0xe31ffffff0000000 0xf8c7fffffc000000

def z76 : W := mkw 0x8bb001a80ab03480 0x22ec006a02ac0d20 0x9bfc01c00ffc3800 0xe6ff007003ff0e00

def z77 : W := mkw 0x53d36c000fdbc000 0x94f4db0003f6f000 0x1ae3c0000fffc000 0x46b8f00003fff000

def z78 : W := mkw 0xe3ffbffff10d4355 0x38ffeffffc4350d5 0xfffffffff31fc7ff 0xfffffffffcc7f1ff

def z79 : W := mkw 0x00000800410d4354 0x00000200104350d5 0x1c000000031fc7ff 0x0700000000c7f1ff

def z80 : W := mkw 0x006184ca20201080 0x0018613288080420 0xfee3c7ce3ce038c0 0xffb8f1f38f380e30

def z81 : W := mkw 0xc8fd169cb0b412c1 0x323f45a72c2d04b0 0x88fc060c30fc00c0 0x223f01830c3f0030

def z82 : W := mkw 0x83b001a800000000 0x20ec006a00000000 0x02e001c000000000 0x40b8007000000000

def z83 : W := mkw 0xebffb7ffba942641 0x3affedffeea50990 0xe3fffffff31c0700 0xf8fffffffcc701c0

def z84 : W := mkw 0x9bb669bc0fb736c0 0x26ed9a6f03edcdb0 0xfffff9fc0fff3fc0 0xfffffe7f03ffcff0

def z85 : W := mkw 0x3002e84345030930 0x4c00ba10d140c24c 0x4003f803c0030032 0x1000fe00f000c00c

def z86 : W := mkw 0xebf3a5eb2ab03481 0x3afce97acaac0d20 0x02e3c1c00ce03800 0x40b8f07003380e00

def z87 : W := mkw 0x000c1214900c4244 0x0003048524031091 0x881c060c301cc0cd 0x220701830c073033

def z88 : W := mkw 0x3302e1630e022c20 0x4cc0b858c3808b08 0x0203c1c00c003800 0x4080f07003000e00

def z89 : W := mkw 0x53df7e140fdfc240 0x94f7df8503f7f090 0xfffffe3c0fffc7c0 0xffffff8f03fff1f0

def z90 : W := mkw 0xf7ffffffff63bdb9 0x7dffffffffd8ef6e 0xffffffffffe3ffff 0xfffffffffff8ffff

def z91 : W := mkw 0x0441040020408008 0x0110410008102002 0x000006003000c00d 0x000001800c003003

def z92 : W := mkw 0x8b9401340a942640 0x22e5004d02a50990 0x011c0030031c0700 0x0047000c00c701c0

def z93 : W := mkw 0xa3b6a1ff00000000 0x28eda87fc0000000 0xe3fff9ffc0000000 0xf8fffe7ff0000000

def z94 : W := mkw 0x53d364000ed28000 0x94f4d90003b4a000 0x02e3c0000ce00000 0x40b8f00003380000

def z95 : W := mkw 0x53df7e14dfdfc354 0x94f7df8537f7f0d5 0xfffffe3fffffc7ff 0xffffff8ffffff1ff

def z96 : W := mkw 0x3302e1630e022c20 0x4cc0b858c3808b08 0x3703c1f00f003f00 0xcdc0f07c03c00fc0

def z97 : W := mkw 0x0020008800201080 0x0008002200080420 0xbee001cc0ce038c0 0xefb8007303380e30

def z98 : W := mkw 0x73dbff630fdbc000 0x9cf6ffd8c3f6f000 0xfbfffff3cfffc000 0xfefffffcf3fff000

def z99 : W := mkw 0x802401bc00000000 0x2009006f00000000 0x200001fc00000000 0x0800007f00000000

def z100 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z101 : W := mkw 0x046d169cb06cd2cc 0x011b45a72c1b34b3 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z102 : W := mkw 0x53df7e14dfdfc354 0x94f7df8537f7f0d5 0xdbfffe31cfffc700 0xf6ffff8c73fff1c0

def z103 : W := mkw 0xe3ffbffff10d4355 0x38ffeffffc4350d5 0xe3fffffff31c0700 0xf8fffffffcc701c0

def z104 : W := mkw 0x0000000000000000 0x0000000000000000 0x61003833c0000000 0x98400e0cf0000000

def z105 : W := mkw 0xc0fd169cb0000001 0x303f45a72c000000 0xe1fc3e3ff0000000 0xb87f0f8ffc000000

def z106 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x26e3c1ce3ce038ff 0x49b8f0738f380e3f

def z107 : W := mkw 0x8394013400000000 0x20e5004d00000000 0x011c003000000000 0x0047000c00000000

def z108 : W := mkw 0xebffb7ffbab03481 0x3affedffeeac0d20 0xe3fffffffce03800 0xf8ffffffff380e00

def z109 : W := mkw 0x006184ca20000000 0x0018613288000000 0xe2e3c7ce30000000 0xf8b8f1f38c000000

def z110 : W := mkw 0x0000000000000000 0x0000000000000000 0xfc00060e3003c0ff 0xbf0001838c00f03f

def z111 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z112 : W := mkw 0x330e3b35db0d6754 0x4cc38ecd76c359d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z113 : W := mkw 0x0004001400000000 0x0001000500000000 0xa11c003c00000000 0xa847000f00000000

def z114 : W := mkw 0x8bbc1bbcdbbd77d4 0x22ef06ef36ef5df5 0xfffc3fffffffffff 0xffff0fffffffffff

def z115 : W := mkw 0x0461048820609088 0x0118412208182422 0x88e0060c30e0c0cd 0x223801830c383033

def z116 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x751c3833c31f0732 0x9d470e0cf0c7c1cc

def z117 : W := mkw 0x8fb441bc0ef6bee8 0x23ed106f03bdafba 0xbffc01fc0fffffff 0xefff007f03ffffff

def z118 : W := mkw 0x100048000fdbc000 0x8400120003f6f000 0x180000000fffc000 0x0600000003fff000

def z119 : W := mkw 0x330efb77df0f6f74 0x4cc3beddf7c3dbdd 0xff1fffffff1fffff 0xffc7ffffffc7ffff

def z120 : W := mkw 0x539e3a14db9d4354 0x94e78e8536e750d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z121 : W := mkw 0x544bfe42254bc828 0x9512ff908952f20a 0x4003fe023003c03f 0x1000ff808c00f00f

def z122 : W := mkw 0x3302a9634b012510 0x4cc0aa58d2c04944 0x6303f9f3c3000700 0xd8c0fe7cf0c001c0

def z123 : W := mkw 0x130268000f030000 0x04c09a0003c0c000 0x5303f8000f030000 0xd4c0fe0003c0c000

def z124 : W := mkw 0x8bb001a80ab03480 0x22ec006a02ac0d20 0x02e001c00ce03800 0x40b8007003380e00

def z125 : W := mkw 0x8ff1c5ea2ef2bca8 0x23fc717a8bbcaf2a 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z126 : W := mkw 0x8cf5049c20f492c8 0x233d4127083d24b2 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z127 : W := mkw 0x0004001400040240 0x0001000500010090 0x881c000c001c00c0 0x2207000300070030

def z128 : W := mkw 0x130260000e020000 0x04c0980003808000 0x0203c0000c000000 0x4080f00003000000

def z129 : W := mkw 0xbbb6e9ff4fb73ff0 0x6eedba7fd3edcffc 0xfffff9ffcfff3ff2 0xfffffe7ff3ffcffc

def z130 : W := mkw 0x534b7e000f4bc000 0x94d2df8003d2f000 0x5303fe000f03c000 0xd4c0ff8003c0f000

def z131 : W := mkw 0x030401340a042640 0x00c1004d02810990 0xbf1c01fc0f1c3fc0 0xefc7007f03c70ff0

def z132 : W := mkw 0x1461ccca6f63bdb8 0x451873329bd8ef6e 0xfee3c7ce3fe3ffff 0xffb8f1f38ff8ffff

def z133 : W := mkw 0x1000480045030930 0x440012001140c24c 0x0000000000030032 0x000000000000c00c

def z134 : W := mkw 0x00000800410d4354 0x00000200104350d5 0x00000000031c0700 0x0000000000c701c0

def z135 : W := mkw 0xe3fff7ffb4428001 0x38fffdffed10a000 0xfbfffffffce3c000 0xfeffffffff38f000

def z136 : W := mkw 0x006d9edef10d4354 0x001b67b7bc4350d5 0xfffffffff31fc7ff 0xfffffffffcc7f1ff

def z137 : W := mkw 0x8ff5c5fe2ef6bee8 0x23fd717f8bbdafba 0xffffc7fe3fffffff 0xfffff1ff8fffffff

def z138 : W := mkw 0x0000000000d8c000 0x8000000000363000 0x0800000000fcc000 0x02000000003f3000

def z139 : W := mkw 0x3302e1634e022d30 0x4cc0b858d3808b4c 0x2603c1f3cc003f32 0x4980f07cf3000fcc

def z140 : W := mkw 0x0441c44224428828 0x011071108910a20a 0xfc03c60e3003c0ff 0xbf00f1838c00f03f

def z141 : W := mkw 0x10085a000fdbc000 0x8402168003f6f000 0xd91c3e000fffc000 0xb6470f8003fff000

def z142 : W := mkw 0x0761c5ea2e62bca8 0x01d8717a8b98af2a 0xffe3c7fe3fe3ffff 0xfff8f1ff8ff8ffff

def z143 : W := mkw 0x046ddedef56fdbfc 0x011b77b7bd5bf6ff 0xffffffffffffffff 0xffffffffffffffff

def z144 : W := mkw 0x04004000046298a8 0x010010000118a62a 0x1c0000000ce3f8ff 0x070000000338fe3f

def z145 : W := mkw 0x006d96deb0000000 0x001b65b7ac000000 0xe3fffffff0000000 0xf8fffffffc000000

def z146 : W := mkw 0x00081a0001094000 0x0002068000425000 0x011c3800031c0000 0x00470e0000c70000

def z147 : W := mkw 0xe3ffbffff1010111 0x38ffeffffc404044 0xf7fffffff3030732 0xfdfffffffcc0c1cc

def z148 : W := mkw 0xe39e333590000001 0x38e78ccd64000000 0x011c3831c0000000 0x00470e0c70000000

def z149 : W := mkw 0x43db360000d8c000 0x90f6cd8000363000 0xcbfffe0000fcc000 0xf2ffff80003f3000

def z150 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x8ae3c7cc3ce0f8cd 0x62b8f1f30f383e33

def z151 : W := mkw 0x0461048820609088 0x0118412208182422 0xfce0060e30e3c0ff 0xbf3801838c38f03f

def z152 : W := mkw 0x0008120090084004 0x0002048024021001 0x000006003000c00d 0x000001800c003003

def z153 : W := mkw 0x0400804220000828 0x010020108800020a 0x000000023000003f 0x000000008c00000f

def z154 : W := mkw 0x0000000000000000 0x0000000000000000 0x8800060c3000c0cd 0x220001830c003033

def z155 : W := mkw 0x53db7f200fdbe400 0x94f6dfc803f6f900 0xfffffff00fffff00 0xfffffffc03ffffc0

def z156 : W := mkw 0x0300012000000000 0x00c0004800000000 0x230001f000000000 0xc8c0007c00000000

def z157 : W := mkw 0x00081a00d10d4354 0x00020680344350d5 0x5c003e03f31fc7ff 0x17000f80fcc7f1ff

def z158 : W := mkw 0x0000080041094114 0x0000020010425045 0x000000000003c03f 0x000000000000f00f

def z159 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x4203f9c3cc033832 0x5080fe70f300ce0c

def z160 : W := mkw 0x3002280141010110 0x4c008a0050404044 0x00003801c0000000 0x00000e0070000000

def z161 : W := mkw 0x43db360000000000 0x10f6cd8000000000 0xc3fffe0000000000 0xf0ffff8000000000

def z162 : W := mkw 0x04414400046298a8 0x011051000118a62a 0xdee3c6000ce3f8ff 0xf7b8f1800338fe3f

def z163 : W := mkw 0x0000400004020000 0x0000100001008000 0x5203c0000c030000 0xd480f0000300c000

def z164 : W := mkw 0x030001200a002400 0x00c0004802800900 0x370001f00f003f00 0xcdc0007c03c00fc0

def z165 : W := mkw 0x000c1214900c4244 0x0003048524031091 0xe91c3e3ff01cc0cd 0xba470f8ffc073033

def z166 : W := mkw 0x0000000040040354 0x00000000100100d5 0x04000000000007ff 0x01000000000001ff

def z167 : W := mkw 0xf3fbffeb2fdbc001 0xbcfefffacbf6f000 0xdbffffc00fffc000 0xf6fffff003fff000

def z168 : W := mkw 0x2302212100000000 0x08c0884840000000 0x01003831c0000000 0x00400e0c70000000

def z169 : W := mkw 0x030000000a000000 0x00c0000002800000 0x130000000f000000 0xc4c0000003c00000

def z170 : W := mkw 0x2763e5eb246298a8 0x09d8f97ac918a62a 0xffe3fffffce3f8ff 0xfff8ffffff38fe3f

def z171 : W := mkw 0x504b7e00054bc000 0x9412df800152f000 0x4003fe000003c000 0x1000ff800000f000

def z172 : W := mkw 0xebf7a5ff2ab436c1 0x3afde97fcaad0db0 0xbfffc1fc0ffc3fc0 0xeffff07f03ff0ff0

def z173 : W := mkw 0xebbe33bd9ab436c1 0x3aef8cef66ad0db0 0xbffc39fdcffc3fc0 0xefff0e7f73ff0ff0

def z174 : W := mkw 0x006184ca20000000 0x0018613288000000 0x02e3c1c000000000 0x40b8f07000000000

def z175 : W := mkw 0x40d9160000d8c000 0x9036458000363000 0x88fc060000fcc000 0x223f0180003f3000

def z176 : W := mkw 0xf3fff7ffbed28001 0xbcfffdffefb4a000 0xe3fffffffce00000 0xf8ffffffff380000

def z177 : W := mkw 0x2302a16340002d30 0x48c0a858d0000b4c 0x6703f9f3c0003f32 0xd9c0fe7cf0000fcc

def z178 : W := mkw 0x8bb401bc002436c0 0x22ed006f00090db0 0xa7fc01fc00003fc0 0xe9ff007f00000ff0

def z179 : W := mkw 0xfbffffffbffff6c1 0xbeffffffeffffdb0 0xffffffffffffffc0 0xfffffffffffffff0

def z180 : W := mkw 0x0004001400040240 0x0001000500010090 0x011c0030031c0700 0x0047000c00c701c0

def z181 : W := mkw 0x20048177d0042f74 0x4801205df4010bdd 0x240001fff0003fff 0x0900007ffc000fff

def z182 : W := mkw 0x63dbb76300000000 0x18f6edd8c0000000 0xe3fffff3c0000000 0xf8fffffcf0000000

def z183 : W := mkw 0xc3ff369cb0000001 0x30ffcda72c000000 0xc3fffe0c30000000 0xf0ffff830c000000

def z184 : W := mkw 0xe3ffb7ffb0d8c001 0xb8ffedffec363000 0xebfffffff0fcc000 0xfafffffffc3f3000

def z185 : W := mkw 0xfbffffff4ffffff0 0xfeffffffd3fffffc 0xffffffffcffffff2 0xfffffffff3fffffc

def z186 : W := mkw 0x80b4009c00000000 0x202d002700000000 0x80fc000c00000000 0x203f000300000000

def z187 : W := mkw 0x230081634a002d30 0x48c02058d2800b4c 0x370001f3cf003f32 0xcdc0007cf3c00fcc

def z188 : W := mkw 0x3302e9634fdbed30 0xccc0ba58d3f6fb4c 0x7f03f9f3cfffff32 0xdfc0fe7cf3ffffcc

def z189 : W := mkw 0x53df7e149fdbc000 0x94f7df8527f6f000 0xfbfffe3fffffc000 0xfeffff8ffffff000

def z190 : W := mkw 0x5bdb7e000ffff6c0 0x96f6df8003fffdb0 0xdffffe000fffffc0 0xf7ffff8003fffff0

def z191 : W := mkw 0x100008004b012510 0x4400020012c04944 0x0000000003000700 0x0000000000c001c0

def z192 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x64003e3ff003c7ff 0x19000f8ffc00f1ff

def z193 : W := mkw 0xe3ffb7ffba900001 0x38ffedffeea40000 0xfbfffffffffc0000 0xfeffffffffff0000

def z194 : W := mkw 0x47fbf6ca246298a8 0x11fefdb28918a62a 0xffffffce3ce3f8ff 0xfffffff38f38fe3f

def z195 : W := mkw 0x8bb001a80ab436c0 0x22ec006a02ad0db0 0x1ee001c00ffc3fc0 0x47b8007003ff0ff0

def z196 : W := mkw 0x646bf6cbb46298a9 0x191afdb2ed18a62a 0xfee3ffcffce3f8ff 0xffb8fff3ff38fe3f

def z197 : W := mkw 0x00081a00d1094114 0x0002068034425045 0xd91c3e03f31fc03f 0xb6470f80fcc7f00f

def z198 : W := mkw 0xbff7edff6ff7bff8 0x6ffdfb7fdbfdeffe 0xffffffffffffffff 0xffffffffffffffff

def z199 : W := mkw 0x3322e9eb4f233db0 0x4cc8ba7ad3c8cf6c 0xffe3f9ffcfe33ff2 0xfff8fe7ff3f8cffc

def z200 : W := mkw 0x8bb401bc0a942640 0x22ed006f02a50990 0xa3fc01fc031c0700 0xe8ff007f00c701c0

def z201 : W := mkw 0x0b0001200ab436c0 0x02c0004802ad0db0 0x3f0001f00ffc3fc0 0xcfc0007c03ff0ff0

def z202 : W := mkw 0x882401bc0ab436c0 0x2209006f02ad0db0 0x3c0001fc0ffc3fc0 0x0f00007f03ff0ff0

def z203 : W := mkw 0x8b9401340ab436c0 0x22e5004d02ad0db0 0x1d1c00300ffc3fc0 0x0747000c03ff0ff0

def z204 : W := mkw 0xabb481ffbab436c1 0x2aed207feead0db0 0xbffc01fffffc3fc0 0xefff007fffff0ff0

def z205 : W := mkw 0xe39e3b35d10d4355 0x38e78ecd744350d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z206 : W := mkw 0x140048004f63bdb8 0x4500120013d8ef6e 0x1c0000000fe3ffff 0x0700000003f8ffff

def z207 : W := mkw 0x00000800410d4354 0x00000200104350d5 0xfc00060e331fc7ff 0xbf0001838cc7f1ff

def z208 : W := mkw 0xc8fd169c00fcd2c0 0xb23f45a7003f34b0 0x88fc060c00fcc0c0 0x223f0183003f3030

def z209 : W := mkw 0x139048000fdbc000 0x84e4120003f6f000 0x9bfc00000fffc000 0xe6ff000003fff000

def z210 : W := mkw 0x0000c84245030930 0x000032109140c24c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z211 : W := mkw 0x100008000b994000 0x8400020002e65000 0x00000000031c0000 0x0000000000c70000

def z212 : W := mkw 0x1461ccca2ffbd8a8 0x851873328bfef62a 0xfee3c7ce3ffff8ff 0xffb8f1f38ffffe3f

def z213 : W := mkw 0xe3ffbfffb1094001 0x38ffefffec425000 0xfbfffffff31fc000 0xfefffffffcc7f000

def z214 : W := mkw 0x1302e8420f030820 0x04c0ba1083c0c208 0x7703f9c20f033832 0xddc0fe7083c0ce0c

def z215 : W := mkw 0xdbff7fbc0ffff6c0 0xb6ffdfef03fffdb0 0xfffffffc0fffffc0 0xffffffff03fffff0

def z216 : W := mkw 0xe0ffb6dfb0000001 0x383fedb7ec000000 0xc0fffe0ff0000000 0x303fff83fc000000

def z217 : W := mkw 0xebffb7ffb0b412c1 0x3affedffec2d04b0 0xebfffffff0fc00c0 0xfafffffffc3f0030

def z218 : W := mkw 0xf3ffffffbfdbc001 0xbcffffffeff6f000 0xfbffffffffffc000 0xfefffffffffff000

def z219 : W := mkw 0xe7fff7ffb46298a9 0x39fffdffed18a62a 0xe3fffffffce03800 0xf8ffffffff380e00

def z220 : W := mkw 0xe7ffb7ffb02018a9 0x39ffedffec08062a 0xe7fffffff00038ff 0xf9fffffffc000e3f

def z221 : W := mkw 0x00081a0001094000 0x0002068000425000 0xfd1c3e0e331fc0ff 0xbf470f838cc7f03f

def z222 : W := mkw 0x0000804200000000 0x0000201080000000 0x6203c1c200000000 0xd880f07080000000

def z223 : W := mkw 0x2302a1630a002400 0x08c0a858c2800900 0x7703f9f3cf003f00 0xddc0fe7cf3c00fc0

def z224 : W := mkw 0x00081a00d1094114 0x0002068034425045 0x00003801c0000000 0x00000e0070000000

def z225 : W := mkw 0x0041040000000000 0x0010410000000000 0xc2e3c60000000000 0xf0b8f18000000000

def z226 : W := mkw 0x039001200a902400 0x00e4004802a40900 0xbffc01f00ffc3f00 0xefff007c03ff0fc0

def z227 : W := mkw 0x53db7e004fdbed30 0xd4f6df8013f6fb4c 0xdffffe000fffff32 0xf7ffff8003ffffcc

def z228 : W := mkw 0x04204088046298a8 0x010810220118a62a 0xbee001cc0ce3f8ff 0xefb800730338fe3f

def z229 : W := mkw 0x080c1a14dbbd77d4 0x0203068536ef5df5 0xfd1c3e3fffffffff 0xbf470f8fffffffff

def z230 : W := mkw 0x2363a5eb20000000 0x08d8e97ac8000000 0xe3e3fffff0000000 0xf8f8fffffc000000

def z231 : W := mkw 0xe39eb37790000001 0x38e7acdde4000000 0x631ff9f3c0000000 0xd8c7fe7cf0000000

def z232 : W := mkw 0x0441c44224428828 0x011071108910a20a 0x4003c6023003c03f 0x1000f1808c00f00f

def z233 : W := mkw 0x8b9c1b34db9d6754 0x22e706cd36e759d5 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z234 : W := mkw 0x10414c000fdbc000 0x8410530003f6f000 0xdae3c6000fffc000 0xf6b8f18003fff000

def z235 : W := mkw 0x0008120090000000 0x0002048024000000 0x40003e03f0000000 0x10000f80fc000000

def z236 : W := mkw 0x0020c0ca042218a0 0x0008303281088628 0xfee3c1ce0ce338f2 0xffb8f0738338ce3c

def z237 : W := mkw 0x000c1a14d1094114 0x0003068534425045 0xe11c3e3ff003c03f 0xb8470f8ffc00f00f

def z238 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x8afc01cc0cfc38c0 0x62bf0073033f0e30

def z239 : W := mkw 0x0465c4def4669bfc 0x01197137bd19a6ff 0xfee3c7fffce3ffff 0xffb8f1ffff38ffff

def z240 : W := mkw 0xe3fff7ffb4020821 0x38fffdffed008208 0xf7fffffffc033832 0xfdffffffff00ce0c

def z241 : W := mkw 0x0000000000040240 0x0000000000010090 0x1c000000031c07c0 0x0700000000c701f0

def z242 : W := mkw 0x9bb449bc4fb73ff0 0x66ed126f13edcffc 0xbffc01fc0fff3ff2 0xefff007f03ffcffc

def z243 : W := mkw 0x87f5c5fe246298a8 0x21fd717f8918a62a 0xffffc7fe3ce3f8ff 0xfffff1ff8f38fe3f

def z244 : W := mkw 0xe3fbb7eb20000001 0x38feedfac8000000 0xc3ffffc000000000 0xf0fffff000000000

def z245 : W := mkw 0x40d9160000000000 0x1036458000000000 0x80fc060000000000 0x203f018000000000

def z246 : W := mkw 0x6043a44320000001 0x1810e910c8000000 0x0003c00000000000 0x0000f00000000000

def z247 : W := mkw 0xe3dfb777b0000001 0x38f7edddec000000 0x411ffe33f0000000 0x1047ff8cfc000000

def z248 : W := mkw 0x100048004fdbed30 0xc400120013f6fb4c 0x1c0000000fffff32 0x0700000003ffffcc

def z249 : W := mkw 0x2000816300000000 0x08002058c0000000 0x200001f3c0000000 0x0800007cf0000000

def z250 : W := mkw 0xebffb7ffb02436c1 0x3affedffec090db0 0xe7fffffff0003fc0 0xf9fffffffc000ff0

def z251 : W := mkw 0x000c121490040240 0x0003048524010090 0xfd1c3e3ff31c07c0 0xbf470f8ffcc701f0

def z252 : W := mkw 0xe3fbb7ebb0000001 0x38feedfaec000000 0x42e3ffc3f0000000 0x50b8fff0fc000000

def z253 : W := mkw 0xe3ffbffff1094115 0x38ffeffffc425045 0xe3fffffff003c03f 0xf8fffffffc00f00f

def z254 : W := mkw 0x0004001400040240 0x0001000500010090 0xfd1c063e331fc7ff 0xbf47018f8cc7f1ff

def z255 : W := mkw 0xdbf365a80ef2b480 0xb6fcd96a03bcad20 0x02e3c1c00ce03800 0x40b8f07003380e00

def z256 : W := mkw 0x00040014d0040354 0x00010005340100d5 0x00000031c0000700 0x0000000c700001c0

def z257 : W := mkw 0x2000c16344022d30 0x48003058d1008b4c 0x7603c1f3cc033f32 0xdd80f07cf300cfcc

def z258 : W := mkw 0xf3ffbfffbb994001 0xbcffefffeee65000 0xe3fffffff31c0000 0xf8fffffffcc70000

def z259 : W := mkw 0x00081a0001094000 0x0002068000425000 0x40003e000003c000 0x10000f800000f000

def z260 : W := mkw 0x0000012000002400 0x0000004800000900 0x240001f000003f00 0x0900007c00000fc0

def z261 : W := mkw 0xa326a1ffb0000001 0x28c9a87fec000000 0x6303f9fff0000000 0xd8c0fe7ffc000000

def z262 : W := mkw 0x0020008800201080 0x0008002200080420 0x88e0000c00e000c0 0x2238000300380030

def z263 : W := mkw 0x57db7e000ffbd8a8 0x95f6df8003fef62a 0xdffffe000ffff8ff 0xf7ffff8003fffe3f

def z264 : W := mkw 0x73d3e5630ed2ac20 0xdcf4f958c3b4ab08 0x02e3c1c00ce03800 0x40b8f07003380e00

def z265 : W := mkw 0x63dbb643b0000001 0x18f6ed90ec000000 0xc3fffe03f0000000 0xf0ffff80fc000000

def z266 : W := mkw 0x000c121490000000 0x0003048524000000 0x011c3831c0000000 0x00470e0c70000000

def z267 : W := mkw 0x130049204f032d30 0x44c0124813c0cb4c 0x370001f00f033f32 0xcdc0007c03c0cfcc

def z268 : W := mkw 0x57fbfeca2ffbd8a8 0x95feffb28bfef62a 0xdbffffc00ffff800 0xf6fffff003fffe00

def z269 : W := mkw 0x139268000f930000 0x04e49a0003e4c000 0xdbfff8000fff0000 0xf6fffe0003ffc000

def z270 : W := mkw 0x330e3b35db0d6754 0x4cc38ecd76c359d5 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z271 : W := mkw 0x50d95e000fdbc000 0x9436578003f6f000 0x98fc06000fffc000 0x263f018003fff000

def z272 : W := mkw 0x330afb634f0b6d30 0x4cc2bed8d3c2db4c 0xff1ffff3cf1fff32 0xffc7fffcf3c7ffcc

def z273 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x1603c1c00f033f32 0x4580f07003c0cfcc

def z274 : W := mkw 0x539e3a14db9d4354 0x94e78e8536e750d5 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z275 : W := mkw 0x00081a0041094110 0x0002068010425044 0xfd1c3e33c31fc732 0xbf470f8cf0c7f1cc

def z276 : W := mkw 0x0000000000000000 0x0000000000000000 0xe000060e30000000 0xb80001838c000000

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x991c0000031c0000 0xa647000000c70000

def z278 : W := mkw 0x8024009cb0000001 0x200900272c000000 0x0000000c30000000 0x000000030c000000

def z279 : W := mkw 0x73dbfe43bfdbc001 0x9cf6ff90eff6f000 0xdbfffe03ffffc000 0xf6ffff80fffff000

def z280 : W := mkw 0x0000c04204020820 0x0000301081008208 0x0203c1c00c003800 0x4080f07003000e00

def z281 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xe2e3c7ce3ce03800 0xf8b8f1f38f380e00

def z282 : W := mkw 0x3343ed634f43ad30 0x4cd0fb58d3d0eb4c 0xffe3fff3cfe3ff32 0xfff8fffcf3f8ffcc

def z283 : W := mkw 0xbb96e9774f972f70 0x6ee5ba5dd3e5cbdc 0x771ff9f3cf1f3f32 0xddc7fe7cf3c7cfcc

def z284 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xc8e3c60e30e3c0ff 0x3238f1838c38f03f

def z285 : W := mkw 0x0461ccca656399b8 0x011873329958e66e 0xffe3ffffffe3ffff 0xfff8fffffff8ffff

def z286 : W := mkw 0x3002e04304020820 0x4c00b810c1008208 0x0003c00000000000 0x0000f00000000000

def z287 : W := mkw 0x40491600b0000001 0x101245802c000000 0x0000060030000000 0x000001800c000000

def z288 : W := mkw 0x00081a00d1094114 0x0002068034425045 0xfc003e0ff003c0ff 0xbf000f83fc00f03f

def z289 : W := mkw 0xcbfd17bcbab436c1 0x32ff45ef2ead0db0 0xbffc07fc3ffc3fc0 0xefff01ff0fff0ff0

def z290 : W := mkw 0x04004000046298a8 0x010010000118a62a 0x000000000ce03800 0x0000000003380e00

def z291 : W := mkw 0x53df7e149fdfc244 0x94f7df8527f7f091 0xdbfffe0c3fffc0cd 0xf6ffff830ffff033

def z292 : W := mkw 0x88b4009c00b412c0 0x222d0027002d04b0 0xbdfc003c03fc07c0 0xaf7f000f00ff01f0

def z293 : W := mkw 0x43d3240000000000 0x10f4c90000000000 0x02e3c00000000000 0x40b8f00000000000

def z294 : W := mkw 0x0461448824629088 0x011851220918a422 0xdae3c60c3ce3c0cd 0xf6b8f1830f38f033

def z295 : W := mkw 0xf3ffffffff0f6f75 0x7cffffffffc3dbdd 0xffffffffff1fffff 0xffffffffffc7ffff

def z296 : W := mkw 0x10004800054bc000 0x840012000152f000 0x000000000003c000 0x000000000000f000

def z297 : W := mkw 0x40dd161490dcc244 0x9037458524373091 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z298 : W := mkw 0xbb9629354b952750 0x6ee58a4d52e549d4 0x011c3831c31c0700 0x00470e0c70c701c0

def z299 : W := mkw 0x130269200f032400 0x04c09a4803c0c900 0x7703f9f00f033f00 0xddc0fe7c03c0cfc0

def z300 : W := mkw 0x83b401bc0a002400 0x20ed006f02800900 0xb7fc01fc0f003f00 0xedff007f03c00fc0

def z301 : W := mkw 0x000c1a1491094000 0x0003068524425000 0xf91c3e3ff31fc000 0xbe470f8ffcc7f000

def z302 : W := mkw 0x0000080041010110 0x0000020010404044 0x1400000003030732 0x0500000000c0c1cc

def z303 : W := mkw 0x8b9c1b34db9d6754 0x22e706cd36e759d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z304 : W := mkw 0x43df3e14d10d4354 0x10f7cf85344350d5 0xfffffe3ff31fc7ff 0xffffff8ffcc7f1ff

def z305 : W := mkw 0xbbb2e9eb4fb33db0 0x6eecba7ad3eccf6c 0x77e3f9f3cfe33f32 0xddf8fe7cf3f8cfcc

def z306 : W := mkw 0x2302a96341010110 0x08c0aa58d0404044 0x7703f9f3c3030732 0xddc0fe7cf0c0c1cc

def z307 : W := mkw 0x8bb401bc0ab03480 0x22ed006f02ac0d20 0xa3fc01fc0ce03800 0xe8ff007f03380e00

def z308 : W := mkw 0xe3beb3ffb0000001 0x38efacffec000000 0x211c39fff0000000 0x08470e7ffc000000

def z309 : W := mkw 0xe3be33bd90000001 0x38ef8cef64000000 0xa3fc39fdc0000000 0xe8ff0e7f70000000

def z310 : W := mkw 0xa3b481ffb0000001 0x28ed207fec000000 0xa3fc01fff0000000 0xe8ff007ffc000000

def z311 : W := mkw 0x0420c0ca246298a8 0x010830328918a62a 0x3c0001ce3ce3f8ff 0x0f0000738f38fe3f

def z312 : W := mkw 0x100048004fdfc354 0x8400120013f7f0d5 0x1c0000000fffc7ff 0x0700000003fff1ff

def z313 : W := mkw 0x8bbc13bc9ab436c0 0x22ef04ef26ad0db0 0xfffc3ffffffc3fc0 0xffff0fffffff0ff0

def z314 : W := mkw 0xe3ffb7ffba002401 0x38ffedffee800900 0xf7ffffffff003f00 0xfdffffffffc00fc0

def z315 : W := mkw 0x0004081441050350 0x00010205104140d4 0xfd1c383fc31f07f2 0xbf470e0ff0c7c1fc

def z316 : W := mkw 0xeffff7ffbef6bee9 0x3bfffdffefbdafba 0xffffffffffffffff 0xffffffffffffffff

def z317 : W := mkw 0xdbf765bc0ef6b6c0 0xb6fdd96f03bdadb0 0xbfffc1fc0ffc3fc0 0xeffff07f03ff0ff0

def z318 : W := mkw 0xe3ffb7ffb0040241 0x38ffedffec010090 0xfffffffff31c07c0 0xfffffffffcc701f0

def z319 : W := mkw 0x080000000a942640 0x0200000002a50990 0x00000000031c0700 0x0000000000c701c0

def z320 : W := mkw 0x0c61c4ca2ef6bee8 0x031871328bbdafba 0xfee3c7ce3fffffff 0xffb8f1f38fffffff

def z321 : W := mkw 0x43df361490000000 0x10f7cd8524000000 0xe3fffe3ff0000000 0xf8ffff8ffc000000

def z322 : W := mkw 0x00040014d0040354 0x00010005340100d5 0xfc00063ff003c7ff 0xbf00018ffc00f1ff

def z323 : W := mkw 0x644bf643b4428829 0x1912fd90ed10a20a 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z324 : W := mkw 0x140048000ffbd8a8 0x8500120003fef62a 0x1c0000000ffff8ff 0x0700000003fffe3f

def z325 : W := mkw 0x606bb6cbb0000001 0x181aedb2ec000000 0xe2e3ffcff0000000 0xf8b8fff3fc000000

def z326 : W := mkw 0x882401bcd02437d4 0x2209006f34090df5 0x240001fff0003fff 0x0900007ffc000fff

def z327 : W := mkw 0x53d364000ed28000 0x94f4d90003b4a000 0xdae3c6000ce3c000 0xf6b8f1800338f000

def z328 : W := mkw 0xa82481ffb02436c1 0x2a09207fec090db0 0x240001fff0003fc0 0x0900007ffc000ff0

def z329 : W := mkw 0x8b9401340a942640 0x22e5004d02a50990 0xbd1c003c031c07c0 0xaf47000f00c701f0

def z330 : W := mkw 0x3306e9774f072f70 0x4cc1ba5dd3c1cbdc 0xff1ff9ffcf1f3ff2 0xffc7fe7ff3c7cffc

def z331 : W := mkw 0x604bbe43f1094115 0x1812ef90fc425045 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z332 : W := mkw 0x000c121490000000 0x0003048524000000 0xfd1c3e3ff003c0ff 0xbf470f8ffc00f03f

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0x360001c00c003800 0xcd80007003000e00

def z334 : W := mkw 0x57f3e4ca2ef298a8 0x95fcf9328bbca62a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z335 : W := mkw 0x3363edeb6f032d30 0x4cd8fb7adbc0cb4c 0xf7e3ffffff033f32 0xfdf8ffffffc0cfcc

def z336 : W := mkw 0x8824009c002412c0 0x22090027000904b0 0x0000000c000000c0 0x0000000300000030

def z337 : W := mkw 0xabb6a1ff0ab436c0 0x2aeda87fc2ad0db0 0xfffff9ffcffc3fc0 0xfffffe7ff3ff0ff0

def z338 : W := mkw 0x0041844220000000 0x0010611088000000 0x4003c60230000000 0x1000f1808c000000

def z339 : W := mkw 0x00495e00054bc000 0x001257800152f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z340 : W := mkw 0x000cda56d50f4b74 0x00033695b543d2dd 0xff1fffffff1fffff 0xffc7ffffffc7ffff

def z341 : W := mkw 0x00081a00d1094114 0x0002068034425045 0x75003e33f303c73f 0x9d400f8cfcc0f1cf

def z342 : W := mkw 0x53dbfe420fdbc820 0x94f6ff9083f6f208 0xffffffc20ffff832 0xfffffff083fffe0c

def z343 : W := mkw 0x739afb634f9b6d30 0xdce6bed8d3e6db4c 0x771ff9f3cf1f3f32 0xddc7fe7cf3c7cfcc

def z344 : W := mkw 0xe3f3a5eb20000001 0x38fce97ac8000000 0xe2e3c7ce30000000 0xf8b8f1f38c000000

def z345 : W := mkw 0x100040000e022c20 0x4400100003808b08 0x000000000c003800 0x0000000003000e00

def z346 : W := mkw 0x0000000000201080 0x0000000000080420 0x1c0000000ce038c0 0x0700000003380e30

def z347 : W := mkw 0x046dd6deb46edaec 0x011b75b7ad1bb6bb 0xfeffc7ce3cfff8ff 0xffbff1f38f3ffe3f

def z348 : W := mkw 0x130268004f030110 0x04c09a0013c0c044 0x7703f833cf030732 0xddc0fe0cf3c0c1cc

def z349 : W := mkw 0xf3f3edeb6f032d31 0x7cfcfb7adbc0cb4c 0x77e3f9f3cf033f32 0xddf8fe7cf3c0cfcc

def z350 : W := mkw 0x330229214b012510 0x4cc08a4852c04944 0x01003831c3000700 0x00400e0c70c001c0

def z351 : W := mkw 0x000000000a002400 0x0000000002800900 0x140000000f003f00 0x0500000003c00fc0

def z352 : W := mkw 0x04004000046298a8 0x010010000118a62a 0xfc00060e3ce3f8ff 0xbf0001838f38fe3f

def z353 : W := mkw 0x8b9401340a942640 0x22e5004d02a50990 0x371c01f00f1c3f00 0xcdc7007c03c70fc0

def z354 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x9c1c060c331fc7ff 0x270701830cc7f1ff

def z355 : W := mkw 0x2000804340000930 0x48002010d000024c 0x00000003c0000032 0x00000000f000000c

def z356 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0xff03ffffff03ffff 0xffc0ffffffc0ffff

def z357 : W := mkw 0xf39e3b35db012511 0x7ce78ecd76c04944 0x011c3831c3000700 0x00470e0c70c001c0

def z358 : W := mkw 0x0400400004428828 0x010010000110a20a 0x000000000003c03f 0x000000000000f00f

def z359 : W := mkw 0x604fbe57f10d4355 0x1813ef95fc4350d5 0xfd1ffe3ff31fc7ff 0xbf47ff8ffcc7f1ff

def z360 : W := mkw 0x53db7e004fdbc110 0x94f6df8013f6f044 0xfffffe33cfffc732 0xffffff8cf3fff1cc

def z361 : W := mkw 0x330269214f032d30 0x4cc09a4853c0cb4c 0x15003831cf033f32 0x05400e0c73c0cfcc

def z362 : W := mkw 0xfbffffffffb73ff1 0x7effffffffedcffc 0xffffffffffff3ff2 0xffffffffffffcffc

def z363 : W := mkw 0x3302e1630e022c20 0x4cc0b858c3808b08 0x7603c1c20c033832 0xdd80f0708300ce0c

def z364 : W := mkw 0x0000000000000000 0x0000000000000000 0xbc00000c000000c0 0xaf00000300000030

def z365 : W := mkw 0x5043640004428000 0x9410d9000110a000 0x0003c00000000000 0x0000f00000000000

def z366 : W := mkw 0x73dbfe434fdbc930 0xdcf6ff90d3f6f24c 0xdbfffe03cfffc032 0xf6ffff80f3fff00c

def z367 : W := mkw 0x0800000000b412c0 0x02000000002d04b0 0x0800000000fc00c0 0x02000000003f0030

def z368 : W := mkw 0x230ebb77d10d4354 0x08c3aeddf44350d5 0xff1ffffff31fc7ff 0xffc7fffffcc7f1ff

def z369 : W := mkw 0xe06fb7ffb0000001 0x381bedffec000000 0x6003fffff0000000 0x1800fffffc000000

def z370 : W := mkw 0x539a3a000b994000 0x94e68e8002e65000 0xd91c3e00031fc000 0xb6470f8000c7f000

def z371 : W := mkw 0x604fb657b0000001 0x1813ed95ec000000 0xe11ffe3ff0000000 0xb847ff8ffc000000

def z372 : W := mkw 0x002080ca20000000 0x0008203288000000 0x200001ce30000000 0x080000738c000000

def z373 : W := mkw 0x042080ca202018a8 0x010820328808062a 0x000001c000003800 0x0000007000000e00

def z374 : W := mkw 0x8c2481fe20243ee8 0x2309207f88090fba 0x240001fe30003fff 0x0900007f8c000fff

def z375 : W := mkw 0xabb481ff4ab43ff0 0x6aed207fd2ad0ffc 0xbffc01ffcffc3ff2 0xefff007ff3ff0ffc

def z376 : W := mkw 0x88bc1a9cd1bd53d4 0x222f06a7346f54f5 0xfdfc3e3ff3ffc7ff 0xbf7f0f8ffcfff1ff

def z377 : W := mkw 0x00040814d1050354 0x00010205344140d5 0x7500383ff30307ff 0x9d400e0ffcc0c1ff

def z378 : W := mkw 0x0061448804629080 0x001851220118a420 0xfee3c7cc0ce3f8c0 0xffb8f1f30338fe30

def z379 : W := mkw 0x08000000002436c0 0x0200000000090db0 0x0400000000003fc0 0x0100000000000ff0

def z380 : W := mkw 0x504b7e00d54bc114 0x9412df803552f045 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z381 : W := mkw 0x882001a800203480 0x2208006a00080d20 0x000001c000003800 0x0000007000000e00

def z382 : W := mkw 0x504f7e14d54fc354 0x9413df853553f0d5 0xfd1ffe3ff31fc7ff 0xbf47ff8ffcc7f1ff

def z383 : W := mkw 0xc0fd169cb00c4245 0x303f45a72c031091 0x88fc060c301cc0cd 0x223f01830c073033

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0xd80006000003c000 0xb60001800000f000

def z385 : W := mkw 0x100048004f0f6f74 0x4400120013c3dbdd 0x1c0000000f1fffff 0x0700000003c7ffff

def z386 : W := mkw 0x20008043b0000001 0x08002010ec000000 0x00000003f0000000 0x00000000fc000000

def z387 : W := mkw 0x0020008800201080 0x0008002200080420 0x02e001c00ce03800 0x40b8007003380e00

def z388 : W := mkw 0x53fb7e880ffbd080 0x94fedfa203fef420 0xffffffcc0ffff8c0 0xfffffff303fffe30

def z389 : W := mkw 0x404916000048c000 0x9012458000123000 0x000006000000c000 0x0000018000003000

def z390 : W := mkw 0x8c65c5fe2466bee8 0x2319717f8919afba 0xfee3c7fe3ce3ffff 0xffb8f1ff8f38ffff

def z391 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x26e001fc0ce03fc0 0x49b8007f03380ff0

def z392 : W := mkw 0x330efb77df032d30 0x4cc3beddf7c0cb4c 0xf71fffffff033f32 0xfdc7ffffffc0cfcc

def z393 : W := mkw 0x0000400004428000 0x000010000110a000 0x180000000ce3c000 0x060000000338f000

def z394 : W := mkw 0xc3fd17bcb0000001 0x30ff45ef2c000000 0xa3fc07fc30000000 0xe8ff01ff0c000000

def z395 : W := mkw 0x039c1a14db9d4354 0x00e7068536e750d5 0xfffc3e3fffffc7ff 0xffff0f8ffffff1ff

def z396 : W := mkw 0x00000000000c4244 0x0000000000031091 0x08000000001cc0cd 0x0200000000073033

def z397 : W := mkw 0x8bb4c1fe0eb63ee0 0x22ed307f83ad8fb8 0xffffc1fe0fff3ff2 0xfffff07f83ffcffc

def z398 : W := mkw 0x53db3e000b994000 0x94f6cf8002e65000 0xc3fffe00031c0000 0xf0ffff8000c70000

def z399 : W := mkw 0x50db7e0005dbc000 0x9436df800176f000 0xc8fffe0000ffc000 0x323fff80003ff000

def z400 : W := mkw 0x0469deca256bd8a8 0x011a77b2895af62a 0xffffffce3ffff8ff 0xfffffff38ffffe3f

def z401 : W := mkw 0x43db3e0001094000 0x10f6cf8000425000 0xdbfffe00031fc000 0xf6ffff8000c7f000

def z402 : W := mkw 0x539a7a000f9b4000 0x94e69e8003e6d000 0x531ff8000f1f0000 0xd4c7fe0003c7c000

def z403 : W := mkw 0x130228000b010000 0x04c08a0002c04000 0x0100380003000000 0x00400e0000c00000

def z404 : W := mkw 0x1763ecca2f6398a8 0x05d8fb328bd8e62a 0xffe3ffce3fe3f8ff 0xfff8fff38ff8fe3f

def z405 : W := mkw 0x83bc13bc90000000 0x20ef04ef24000000 0xe3fc3ffff0000000 0xf8ff0ffffc000000

def z406 : W := mkw 0x8ff1c5ea2ef2bca8 0x23fc717a8bbcaf2a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z407 : W := mkw 0x53d36c000fd38000 0x94f4db0003f4e000 0x53e3f8000fe30000 0xd4f8fe0003f8c000

def z408 : W := mkw 0xe3df373590000001 0x38f7cdcd64000000 0xc3fffe31c0000000 0xf0ffff8c70000000

def z409 : W := mkw 0x04614488246298a8 0x011851220918a62a 0x9ce0060c3ce3f8ff 0x273801830f38fe3f

def z410 : W := mkw 0x404b360000000000 0x1012cd8000000000 0x4003fe0000000000 0x1000ff8000000000

def z411 : W := mkw 0x3302a9634b012d30 0x4cc0aa58d2c04b4c 0x250039f3c3003f32 0x09400e7cf0c00fcc

def z412 : W := mkw 0x8bbc1bbc0bbd76c0 0x22ef06ef02ef5db0 0xfffc3ffc0fffffc0 0xffff0fff03fffff0

def z413 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x42e3c7c23ce3f83f 0x50b8f1f08f38fe0f

def z414 : W := mkw 0x130e7a14df0f4354 0x04c39e8537c3d0d5 0xff1ffe3fff1fc7ff 0xffc7ff8fffc7f1ff

def z415 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x0303f9f1cf003f00 0x40c0fe7c73c00fc0

def z416 : W := mkw 0x13436c000f438000 0x04d0db0003d0e000 0xdbe3fe000fe3c000 0xf6f8ff8003f8f000

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x3500003003000700 0x8d40000c00c001c0

def z418 : W := mkw 0x44f9168820f8d088 0x913e45a2083e3422 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z419 : W := mkw 0x00040814410d4354 0x00010205104350d5 0xbd1c003c031fc7ff 0xaf47000f00c7f1ff

def z420 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xfffc07fe3fffffff 0xffff01ff8fffffff

def z421 : W := mkw 0x000c121490000000 0x0003048524000000 0x801c060c30000000 0x200701830c000000

def z422 : W := mkw 0x100048000f030000 0x0400120003c0c000 0x100000000f030000 0x0400000003c0c000

def z423 : W := mkw 0x3002e96345032d30 0x4c00ba58d140cb4c 0x6403f9f3c0033f32 0x1900fe7cf000cfcc

def z424 : W := mkw 0xb326e9ffff032d31 0x6cc9ba7fffc0cb4c 0x7703f9ffff033f32 0xddc0fe7fffc0cfcc

def z425 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x03fff8000ffc0000 0x40fffe0003ff0000

def z426 : W := mkw 0x8bb001a80ab03480 0x22ec006a02ac0d20 0xbee001cc0ce038c0 0xefb8007303380e30

def z427 : W := mkw 0xe7ffb7ffb0609089 0x39ffedffec182422 0xebfffffff0e0c0cd 0xfafffffffc383033

def z428 : W := mkw 0xc4fdd6deb46298a9 0x313f75b7ad18a62a 0xfeffc7ce3ce3f8ff 0xffbff1f38f38fe3f

def z429 : W := mkw 0x0000400004020820 0x0000100001008208 0x140000000c033832 0x050000000300ce0c

def z430 : W := mkw 0x046184ca202018a8 0x011861328808062a 0xe6e3c7ce300038ff 0xf9b8f1f38c000e3f

def z431 : W := mkw 0x039000000a900000 0x00e4000002a40000 0x02e000000ce00000 0x40b8000003380000

def z432 : W := mkw 0x57fb7e882ffbd088 0x95fedfa20bfef422 0xdbfffe0c3fffc0cd 0xf6ffff830ffff033

def z433 : W := mkw 0x0c0040000ef6bee8 0x0300100003bdafba 0x1c0000000fffffff 0x0700000003ffffff

def z434 : W := mkw 0x0302200000000000 0x00c0880000000000 0x4303f80000000000 0xd0c0fe0000000000

def z435 : W := mkw 0x0061c4ca24020820 0x0018713289008208 0xf6e3c7ce3c033832 0xfdb8f1f38f00ce0c

def z436 : W := mkw 0x042080ca202018a8 0x010820328808062a 0xfc0007ce3003f8ff 0xbf0001f38c00fe3f

def z437 : W := mkw 0x3763e5eb2e62bca8 0x4dd8f97acb98af2a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z438 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x411ffe00031fc000 0x1047ff8000c7f000

def z439 : W := mkw 0x040c5a14d56fdbfc 0x01031685355bf6ff 0xfd1c3e3fffffffff 0xbf470f8fffffffff

def z440 : W := mkw 0x3000c9634f032d30 0x4c003258d3c0cb4c 0x340001f3cf033f32 0x0d00007cf3c0cfcc

def z441 : W := mkw 0x2000012140002510 0x4800004850000944 0x00000031c0000700 0x0000000c700001c0

def z442 : W := mkw 0x04000000002018a8 0x010000000008062a 0x04000000000038ff 0x0100000000000e3f

def z443 : W := mkw 0x2461c5eb6462bdb8 0x4918717ad918af6e 0xfee3c7fffce3ffff 0xffb8f1ffff38ffff

def z444 : W := mkw 0x180048004fb73ff0 0x4600120013edcffc 0x1c0000000fff3ff2 0x0700000003ffcffc

def z445 : W := mkw 0x0000080001010000 0x0000020000404000 0x5100380003030000 0x94400e0000c0c000

def z446 : W := mkw 0xc4fd169cb0609089 0x313f45a72c182422 0x88fc060c30e0c0cd 0x223f01830c383033

def z447 : W := mkw 0x130268000fdbc000 0x84c09a0003f6f000 0x5b03f8000fffc000 0xd6c0fe0003fff000

def z448 : W := mkw 0x0390000000000000 0x00e4000000000000 0x83fc000000000000 0xe0ff000000000000

def z449 : W := mkw 0x8bbc13bc9abc76c4 0x22ef04ef26af1db1 0xbffc07fc3ffcffcd 0xefff01ff0fff3ff3

def z450 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xe11c3e3ff31c0700 0xb8470f8ffcc701c0

def z451 : W := mkw 0x8bb401bc00b412c0 0x22ed006f002d04b0 0xabfc01fc00fc00c0 0xeaff007f003f0030

def z452 : W := mkw 0x376fffffff6ffffc 0x4ddbffffffdbffff 0xffffffffffffffff 0xffffffffffffffff

def z453 : W := mkw 0x8b2401bc0a2436c0 0x22c9006f02890db0 0x370001fc0f003fc0 0xcdc0007f03c00ff0

def z454 : W := mkw 0x0000000000000000 0x0000000000000000 0x2400000e300000ff 0x090000038c00003f

def z455 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xfffffffff003c0ff 0xfffffffffc00f03f

def z456 : W := mkw 0x57f3e4ca2ef298a8 0x95fcf9328bbca62a 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z457 : W := mkw 0x0020008800201080 0x0008002200080420 0xfee007ce3ce3f8ff 0xffb801f38f38fe3f

def z458 : W := mkw 0x3443ec4365438938 0x4d10fb10d950e24e 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z459 : W := mkw 0xf3f3e5eb2e022c21 0x7cfcf97acb808b08 0x02e3c1c00c003800 0x40b8f07003000e00

def z460 : W := mkw 0x0b9000000ab436c0 0x02e4000002ad0db0 0x9ffc00000ffc3fc0 0xe7ff000003ff0ff0

def z461 : W := mkw 0x539220000a900000 0x94e4880002a40000 0x0000000000000000 0x0000000000000000

def z462 : W := mkw 0x0000000040002d30 0x4000000010000b4c 0x0400000000003f32 0x0100000000000fcc

def z463 : W := mkw 0x07f1c4ca2ef298a8 0x01fc71328bbca62a 0xffffc7ce3ffff8ff 0xfffff1f38ffffe3f

def z464 : W := mkw 0x3302e9634f0f6f74 0x4cc0ba58d3c3dbdd 0x7f03f9f3cf1fffff 0xdfc0fe7cf3c7ffff

def z465 : W := mkw 0xe7f3e5eb246298a9 0x39fcf97ac918a62a 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z466 : W := mkw 0x00040814d10d4354 0x00010205344350d5 0x3c00003ff31fc7ff 0x0f00000ffcc7f1ff

def z467 : W := mkw 0x0000080041010110 0x0000020010404044 0x01003831c3000700 0x00400e0c70c001c0

def z468 : W := mkw 0x0061048820000000 0x0018412208000000 0x80e0060c30000000 0x203801830c000000

def z469 : W := mkw 0xdbbe3bbc0bbd76c0 0xb6ef8eef02ef5db0 0xbffc39fc0ffc3fc0 0xefff0e7f03ff0ff0

def z470 : W := mkw 0x100040000ed28000 0x8400100003b4a000 0x000000000ce00000 0x0000000003380000

def z471 : W := mkw 0x43db760004428000 0x10f6dd800110a000 0xdbfffe000ce3c000 0xf6ffff800338f000

def z472 : W := mkw 0xa42481ffb02018a9 0x2909207fec08062a 0x240001fff00038ff 0x0900007ffc000e3f

def z473 : W := mkw 0x0024009c002412c0 0x00090027000904b0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z474 : W := mkw 0x8ff5c5fe2ef6bee8 0x23fd717f8bbdafba 0xbfffc1fc0ffc3fc0 0xeffff07f03ff0ff0

def z475 : W := mkw 0x0041440004428000 0x001051000110a000 0x4003c6000003c000 0x1000f1800000f000

def z476 : W := mkw 0x40d1040000d08000 0x9034410000342000 0x00e0000000e00000 0x0038000000380000

def z477 : W := mkw 0x000c1214900c4244 0x0003048524031091 0xbd1c063c331cc7cd 0xaf47018f0cc731f3

def z478 : W := mkw 0xb3b6e9ff4f032d30 0x6cedba7fd3c0cb4c 0xf7fff9ffcf033f32 0xfdfffe7ff3c0cfcc

def z479 : W := mkw 0x504b7e00054bc000 0x9412df800152f000 0xd91ffe00031fc000 0xb647ff8000c7f000

def z480 : W := mkw 0x1000c8424f032d30 0x4400321093c0cb4c 0x7603c1c20f033f32 0xdd80f07083c0cfcc

def z481 : W := mkw 0xf3df7f359fdbc001 0xbcf7dfcd67f6f000 0xdbfffe31cfffc000 0xf6ffff8c73fff000

def z482 : W := mkw 0x300afa43d50b4934 0x4c02be90f542d24d 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z483 : W := mkw 0x0090000000900000 0x0024000000240000 0x88fc000000fc0000 0x223f0000003f0000

def z484 : W := mkw 0x000c1214d0040354 0x00030485340100d5 0xe51c3e3ff00007ff 0xb9470f8ffc0001ff

def z485 : W := mkw 0xa465c5ffb46298a9 0x2919717fed18a62a 0xfee3c7fffce3f8ff 0xffb8f1ffff38fe3f

def z486 : W := mkw 0x40dd1e14d1ddc354 0x90374785347770d5 0xfdfc3e3ff3ffc7ff 0xbf7f0f8ffcfff1ff

def z487 : W := mkw 0x3392e9634f932d30 0x4ce4ba58d3e4cb4c 0xfffff9f3cfff3f32 0xfffffe7cf3ffcfcc

def z488 : W := mkw 0xdbfb7fa80ffbf480 0xb6fedfea03fefd20 0xdbffffc00ffff800 0xf6fffff003fffe00

def z489 : W := mkw 0xe3f3a5eb20000001 0x38fce97ac8000000 0x63e3f9f3c0000000 0xd8f8fe7cf0000000

def z490 : W := mkw 0x330efb77df0f6f74 0x4cc3beddf7c3dbdd 0x771ff9f3cf1f3f32 0xddc7fe7cf3c7cfcc

def z491 : W := mkw 0x2000816300002c20 0x48002058c0000b08 0x000001c000003800 0x0000007000000e00

def z492 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x6403c7ce3003f8ff 0x1900f1f38c00fe3f

def z493 : W := mkw 0x53db7e00054bc000 0x94f6df800152f000 0xc3fffe000003c000 0xf0ffff800000f000

def z494 : W := mkw 0x000c1a14910d4244 0x0003068524435091 0xd91c3e0c331fc0cd 0xb6470f830cc7f033

def z495 : W := mkw 0x3002e84345030930 0x4c00ba10d140c24c 0x7503f833c3030732 0x9d40fe0cf0c0c1cc

def z496 : W := mkw 0x8ffddffefffffffc 0x23ff77ffbfffffff 0xffffffffffffffff 0xffffffffffffffff

def z497 : W := mkw 0x40d9560004dac000 0x903655800136b000 0xdaffc6000cffc000 0xf6bff180033ff000

def z498 : W := mkw 0xc0fd96deb0000001 0x303f65b7ac000000 0xe2ffc7ce30000000 0xf8bff1f38c000000

def z499 : W := mkw 0x039400140a940240 0x00e5000502a50090 0xbffc003c0ffc07c0 0xefff000f03ff01f0

def z500 : W := mkw 0x080008004bbd77d4 0x0200020012ef5df5 0x1c0000000fffffff 0x0700000003ffffff

def z501 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x891c3e3df31cc7cd 0x22470f8f7cc731f3

def z502 : W := mkw 0x330afb63df0b6d34 0x4cc2bed8f7c2db4d 0x7703fff3ff03ff3f 0xddc0fffcffc0ffcf

def z503 : W := mkw 0x03d144000ed28000 0x00f4510003b4a000 0xdbffc6000fffc000 0xf6fff18003fff000

def z504 : W := mkw 0x042c9adef12d5bfc 0x010b26b7bc4b56ff 0xfd1c3ffff31fffff 0xbf470ffffcc7ffff

def z505 : W := mkw 0xf3ffbffffb012511 0x7cffeffffec04944 0xe3fffffff3000700 0xf8fffffffcc001c0

def z506 : W := mkw 0x83bc1bbcd10d4354 0x20ef06ef344350d5 0xfffc3ffff31fc7ff 0xffff0ffffcc7f1ff

def z507 : W := mkw 0x0000080041010110 0x0000020010404044 0xfd003e3ff303c7ff 0xbf400f8ffcc0f1ff

def z508 : W := mkw 0x882401bc002436c0 0x2209006f00090db0 0xbee001fc0ce03fc0 0xefb8007f03380ff0

def z509 : W := mkw 0x130a7a000f0b4000 0x04c29e8003c2d000 0xdb1ffe000f1fc000 0xf6c7ff8003c7f000

def z510 : W := mkw 0x0004001490000000 0x0001000524000000 0x2000003ff0000000 0x0800000ffc000000

def z511 : W := mkw 0x3302e1630e022c20 0x4cc0b858c3808b08 0x6303f9f3cc003800 0xd8c0fe7cf3000e00

def z512 : W := mkw 0x8b9001200a902400 0x22e4004802a40900 0x0000000000000000 0x0000000000000000

def z513 : W := mkw 0x002c1a9cd12d53d4 0x000b06a7344b54f5 0xfffc3fffffffffff 0xffff0fffffffffff

def z514 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xbd1c383dc31c07c0 0xaf470e0f70c701f0

def z515 : W := mkw 0x0000c04204020820 0x0000301081008208 0xfe03c7ce3c03f8ff 0xff80f1f38f00fe3f

def z516 : W := mkw 0x88bc129c90bc52c4 0x222f04a7242f14b1 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z517 : W := mkw 0x0420c0ca242218a8 0x010830328908862a 0x7603c1ce3c0338ff 0xdd80f0738f00ce3f

def z518 : W := mkw 0xdbff7fbcdffff7d4 0xb6ffdfef37fffdf5 0xffffffffffffffff 0xffffffffffffffff

def z519 : W := mkw 0x8ff505bc2af4b6c8 0x23fd416f0abd2db2 0xbffc07fc3ffcffcd 0xefff01ff0fff3ff3

def z520 : W := mkw 0x330221210a002400 0x4cc0884842800900 0x0000000000000000 0x0000000000000000

def z521 : W := mkw 0xe392212100000001 0x38e4884840000000 0x0000000000000000 0x0000000000000000

def z522 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xd91c3e31c31fc700 0xb6470f8c70c7f1c0

def z523 : W := mkw 0x8b9401340a942640 0x22e5004d02a50990 0x9bfc00300ffc0700 0xe6ff000c03ff01c0

def z524 : W := mkw 0x539a3a000b994000 0x94e68e8002e65000 0x9bfc38000ffc0000 0xe6ff0e0003ff0000

def z525 : W := mkw 0xd3ff7e9cbfdbc001 0xb4ffdfa72ff6f000 0xdbfffe0c3fffc000 0xf6ffff830ffff000

def z526 : W := mkw 0x546bfeca256bd8a8 0x951affb2895af62a 0xfee3ffce3ce3f8ff 0xffb8fff38f38fe3f

def z527 : W := mkw 0x704bfe43b54bc001 0x9c12ff90ed52f000 0x4003fe03f003c000 0x1000ff80fc00f000

def z528 : W := mkw 0x704bfe43f5030931 0x5c12ff90fd40c24c 0x4003fe03f0030032 0x1000ff80fc00c00c

def z529 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0000000003c0ff 0x070000000000f03f

def z530 : W := mkw 0xa06585ffb0000001 0x2819617fec000000 0xe2e3c7fff0000000 0xf8b8f1fffc000000

def z531 : W := mkw 0x83f585fe20000000 0x20fd617f88000000 0xe3ffc7fe30000000 0xf8fff1ff8c000000

def z532 : W := mkw 0x000c1214d00c4354 0x00030485340310d5 0xac1c063ff01cc7ff 0x2b07018ffc0731ff

def z533 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x75003833cf033f32 0x9d400e0cf3c0cfcc

def z534 : W := mkw 0xf7ffffffbffbd8a9 0xbdffffffeffef62a 0xfffffffffffff8ff 0xfffffffffffffe3f

def z535 : W := mkw 0x83b401bc0a900000 0x20ed006f02a40000 0xbbfc01fc0ffc0000 0xeeff007f03ff0000

def z536 : W := mkw 0x300efa57d50f4b74 0x4c03be95f543d2dd 0xfd1ffe3ff31fc7ff 0xbf47ff8ffcc7f1ff

def z537 : W := mkw 0xd3ff7fbc0fdbc000 0xb4ffdfef03f6f000 0xfbfffffc0fffc000 0xfeffffff03fff000

def z538 : W := mkw 0x53db7e00dfdbc114 0x94f6df8037f6f045 0xdbfffe03ffffc03f 0xf6ffff80fffff00f

def z539 : W := mkw 0x0420008820201088 0x0108002208080422 0x0000000c300000cd 0x000000030c000033

def z540 : W := mkw 0xebffbffffbbd77d5 0x3affeffffeef5df5 0xffffffffffffffff 0xffffffffffffffff

def z541 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x251c01fc031c3fc0 0x0947007f00c70ff0

def z542 : W := mkw 0xdffffffe2ffffee8 0xb7ffffff8bffffba 0xfffffffe3fffffff 0xffffffff8fffffff

def z543 : W := mkw 0x000c1a14010d4240 0x0003068500435090 0xfd1c3e3c031fc7c0 0xbf470f8f00c7f1f0

def z544 : W := mkw 0x3306e977df072f74 0x4cc1ba5df7c1cbdd 0x7703f9ffff033fff 0xddc0fe7fffc0cfff

def z545 : W := mkw 0xa004013590000001 0x2801004d64000000 0x00000031c0000000 0x0000000c70000000

def z546 : W := mkw 0x57dbfe422fdbc828 0x95f6ff908bf6f20a 0xdbfffe023fffc03f 0xf6ffff808ffff00f

def z547 : W := mkw 0x73dbff634f032d30 0x5cf6ffd8d3c0cb4c 0xf7fffff3cf033f32 0xfdfffffcf3c0cfcc

def z548 : W := mkw 0x40d91e0001d9c000 0x9036478000767000 0xd9fc3e0003ffc000 0xb67f0f8000fff000

def z549 : W := mkw 0xe3ffb7ffb00c4245 0x38ffedffec031091 0xebfffffff01cc0cd 0xfafffffffc073033

def z550 : W := mkw 0x0449de42f54bc93c 0x01127790bd52f24f 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z551 : W := mkw 0x8bbc1bbcdbbd77d4 0x22ef06ef36ef5df5 0xbffc39fdcffc3fc0 0xefff0e7f73ff0ff0

def z552 : W := mkw 0xf3ffffffffdfc355 0xbcfffffffff7f0d5 0xffffffffffffc7ff 0xfffffffffffff1ff

def z553 : W := mkw 0xc0f1048820000001 0x303c412208000000 0x00e0000000000000 0x0038000000000000

def z554 : W := mkw 0x3763e5eb2e62bca8 0x4dd8f97acb98af2a 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z555 : W := mkw 0xe7f3e5eb246298a9 0x39fcf97ac918a62a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z556 : W := mkw 0x439a320000000000 0x10e68c8000000000 0x011c380000000000 0x00470e0000000000

def z557 : W := mkw 0x53db3e000bd9c000 0x94f6cf8002f67000 0x89fc3e0003fcc000 0x227f0f8000ff3000

def z558 : W := mkw 0x130268004f032d30 0x44c09a0013c0cb4c 0x5703f8000f033f32 0xd5c0fe0003c0cfcc

def z559 : W := mkw 0x539a7a000fdbc000 0x94e69e8003f6f000 0x191c38000fffc000 0x06470e0003fff000

def z560 : W := mkw 0xbbb6e1ff0eb63ee0 0x6eedb87fc3ad8fb8 0xbfffc1fc0ffc3fc0 0xeffff07f03ff0ff0

def z561 : W := mkw 0x0441c44224428828 0x011071108910a20a 0xdae3c6023ce3c03f 0xf6b8f1808f38f00f

def z562 : W := mkw 0x0400c042046298a8 0x010030108118a62a 0x7e03c1c20ce3f8ff 0xdf80f0708338fe3f

def z563 : W := mkw 0xa02081eb20000001 0x2808207ac8000000 0x000001c000000000 0x0000007000000000

def z564 : W := mkw 0x180048000ffff6c0 0x8600120003fffdb0 0x1c0000000fffffc0 0x0700000003fffff0

def z565 : W := mkw 0x8bb409bc4bb537d0 0x22ed026f12ed4df4 0xfffc39ffcfff3ff2 0xffff0e7ff3ffcffc

def z566 : W := mkw 0x242081eb60203db8 0x4908207ad8080f6e 0x240001fff0003fff 0x0900007ffc000fff

def z567 : W := mkw 0xe0fd97ffb0000001 0x383f65ffec000000 0xa0fc07fff0000000 0x283f01fffc000000

def z568 : W := mkw 0x000c1a14d1010110 0x0003068534404044 0xf51c3e3ff3030732 0xbd470f8ffcc0c1cc

def z569 : W := mkw 0xf3fff7ffbe022c21 0x7cfffdffef808b08 0xe3fffffffc003800 0xf8ffffffff000e00

def z570 : W := mkw 0x3302e9630f030000 0x0cc0ba58c3c0c000 0x7303f9f3cf030000 0xdcc0fe7cf3c0c000

def z571 : W := mkw 0xe7fffffff56fdbfd 0x39fffffffd5bf6ff 0xffffffffffffffff 0xffffffffffffffff

def z572 : W := mkw 0xe39e333590000001 0x38e78ccd64000000 0xe11c3e3ff0000000 0xb8470f8ffc000000

def z573 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x251c383ff31c07ff 0x09470e0ffcc701ff

def z574 : W := mkw 0x00000000d0000114 0x0000000034000045 0x00000003f000003f 0x00000000fc00000f

def z575 : W := mkw 0x0461ccca656fdbfc 0x01187332995bf6ff 0xfee3c7ce3fffffff 0xffb8f1f38fffffff

def z576 : W := mkw 0xcbfd17bc0afcf6c0 0xb2ff45ef02bf3db0 0xbffc07fc0ffcffc0 0xefff01ff03ff3ff0

def z577 : W := mkw 0x3302e96345030930 0x4cc0ba58d140c24c 0x6303f9f3c0030032 0xd8c0fe7cf000c00c

def z578 : W := mkw 0x3763edeb6f63bdb8 0x4dd8fb7adbd8ef6e 0x77e3f9f3cfe33f32 0xddf8fe7cf3f8cfcc

def z579 : W := mkw 0x53db7e004fdfc354 0x94f6df8013f7f0d5 0xdffffe000fffc7ff 0xf7ffff8003fff1ff

def z580 : W := mkw 0x046184ca20609088 0x0118613288182422 0xeae3c7ce30e0c0cd 0xfab8f1f38c383033

def z581 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x03fff9f1c0000000 0x40fffe7c70000000

def z582 : W := mkw 0x0000c04204020820 0x0000301081008208 0x4003c00200030032 0x1000f0008000c00c

def z583 : W := mkw 0xcbff37bc0ab436c0 0x32ffcdef02ad0db0 0xfffffffc0ffc3fc0 0xffffffff03ff0ff0

def z584 : W := mkw 0x0441c442246298a8 0x011071108918a62a 0x5c03c6023ce3f8ff 0x1700f1808f38fe3f

def z585 : W := mkw 0x83b401bc00040240 0x20ed006f00010090 0xbffc01fc031c07c0 0xefff007f00c701f0

def z586 : W := mkw 0x0020008800000000 0x0008002200000000 0xa2e001cc00000000 0xe8b8007300000000

def z587 : W := mkw 0x100c5a14df0f6f74 0x4403168537c3dbdd 0xfd1c3e3fff1fffff 0xbf470f8fffc7ffff

def z588 : W := mkw 0x0400000000609088 0x0100000000182422 0x0800000000e0c0cd 0x0200000000383033

def z589 : W := mkw 0xf39efb77df032d31 0x7ce7beddf7c0cb4c 0x771ff9f3cf033f32 0xddc7fe7cf3c0cfcc

def z590 : W := mkw 0x734bff63ff032d31 0x5cd2ffd8ffc0cb4c 0x7703fff3ff033f32 0xddc0fffcffc0cfcc

def z591 : W := mkw 0x8bb401bcdab437d4 0x22ed006f36ad0df5 0xbffc01fffffc3fff 0xefff007fffff0fff

def z592 : W := mkw 0x704bfe43454bc930 0xdc12ff90d152f24c 0x4003fe03c003c032 0x1000ff80f000f00c

def z593 : W := mkw 0xeb9e33359a942641 0x3ae78ccd66a50990 0x011c3831c31c0700 0x00470e0c70c701c0

def z594 : W := mkw 0x53d364000ed28000 0x94f4d90003b4a000 0x9bffc0000ffc0000 0xe6fff00003ff0000

def z595 : W := mkw 0x0465c4de24669ae8 0x011971378919a6ba 0xffffc7fe3fffffff 0xfffff1ff8fffffff

def z596 : W := mkw 0x3702e9634f63bdb8 0x4dc0ba58d3d8ef6e 0x7f03f9f3cfe3ffff 0xdfc0fe7cf3f8ffff

def z597 : W := mkw 0x8cf5c4de24f69ae8 0x233d7137893da6ba 0xfeffc7ce3cfff8ff 0xffbff1f38f3ffe3f

def z598 : W := mkw 0x53db76000ed28000 0x94f6dd8003b4a000 0xc3fffe000ce00000 0xf0ffff8003380000

def z599 : W := mkw 0x0461c4ca24428828 0x011871328910a20a 0xe2e3c7ce3003c03f 0xf8b8f1f38c00f00f

def z600 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x1ee3c1c00ce3f8ff 0x47b8f0700338fe3f

def z601 : W := mkw 0x4098120000984000 0x9026048000261000 0x001c0000001c0000 0x0007000000070000

def z602 : W := mkw 0x1002680005030000 0x04009a000140c000 0x4003f80000030000 0x1000fe000000c000

def z603 : W := mkw 0x88b401bc00b436c0 0x222d006f002d0db0 0xacfc01fc00fc3fc0 0x2b3f007f003f0ff0

def z604 : W := mkw 0x0000000000000000 0x0000000000000000 0x400006023003c03f 0x100001808c00f00f

def z605 : W := mkw 0x0020008800201080 0x0008002200080420 0x240001cc000038c0 0x0900007300000e30

def z606 : W := mkw 0xe39e3b35d10d4355 0x38e78ecd744350d5 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z607 : W := mkw 0x00081a00410d4354 0x00020680104350d5 0xdd1c3e00031fc7ff 0xb7470f8000c7f1ff

def z608 : W := mkw 0x000c1214900c4244 0x0003048524031091 0x001c0000001c0000 0x0007000000070000

def z609 : W := mkw 0x080000000ab03480 0x0200000002ac0d20 0x000000000ce03800 0x0000000003380e00

def z610 : W := mkw 0xbb26e9ff4f273ff0 0x6ec9ba7fd3c9cffc 0x7703f9ffcf033ff2 0xddc0fe7ff3c0cffc

def z611 : W := mkw 0x3302e9630f032c20 0x4cc0ba58c3c0cb08 0x5303f9c00f033800 0xd4c0fe7003c0ce00

def z612 : W := mkw 0xa02481fff0040355 0x2809207ffc0100d5 0x240001fff00007ff 0x0900007ffc0001ff

def z613 : W := mkw 0x88b4009c00b412c0 0x222d0027002d04b0 0xbefc01cc0cfc38c0 0xefbf0073033f0e30

def z614 : W := mkw 0x082000880ab436c0 0x0208002202ad0db0 0xbee001cc0ffc3fc0 0xefb8007303ff0ff0

def z615 : W := mkw 0xdb9e3b340b9d6640 0xb6e78ecd02e75990 0x011c3830031c0700 0x00470e0c00c701c0

def z616 : W := mkw 0xa02c93ffb0000001 0x280b24ffec000000 0xe11c3ffff0000000 0xb8470ffffc000000

def z617 : W := mkw 0x8fb481fe2ab43ee8 0x23ed207f8aad0fba 0xbffc01fe3ffc3fff 0xefff007f8fff0fff

def z618 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x82ffc7cc30000000 0x60bff1f30c000000

def z619 : W := mkw 0x73dfff77dfdfef74 0xdcf7ffddf7f7fbdd 0xffffffffffffffff 0xffffffffffffffff

def z620 : W := mkw 0x03981a000b994000 0x00e6068002e65000 0xdbfc3e000fffc000 0xf6ff0f8003fff000

def z621 : W := mkw 0x0000000000000000 0x0000000000000000 0x7400000200030032 0x9d0000008000c00c

def z622 : W := mkw 0x88b0008800b01080 0x222c0022002c0420 0x00e0000000e00000 0x0038000000380000

def z623 : W := mkw 0xdbdf7f340fdfe640 0xb6f7dfcd03f7f990 0xdbfffe300fffc700 0xf6ffff8c03fff1c0

def z624 : W := mkw 0x0041c44204428820 0x001071108110a208 0xfee3c7c20ce3f832 0xffb8f1f08338fe0c

def z625 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x4103f833c3030732 0x1040fe0cf0c0c1cc

def z626 : W := mkw 0x0041440004428000 0x001051000110a000 0xfee3c60e3ce3c0ff 0xffb8f1838f38f03f

def z627 : W := mkw 0xc0fd1e9cf10d4355 0x303f47a73c4350d5 0xfdfc3e3ff31fc7ff 0xbf7f0f8ffcc7f1ff

def z628 : W := mkw 0xc0fd169cb0d8c001 0xb03f45a72c363000 0x88fc060c30fcc000 0x223f01830c3f3000

def z629 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xfffffe0e3fffc0ff 0xffffff838ffff03f

def z630 : W := mkw 0x739a3b214b996510 0xdce68ec852e65944 0x011c3831c31c0700 0x00470e0c70c701c0

def z631 : W := mkw 0x3b02e9634fb73ff0 0x4ec0ba58d3edcffc 0x7f03f9f3cfff3ff2 0xdfc0fe7cf3ffcffc

def z632 : W := mkw 0xe3ffb7fff0040355 0x38ffedfffc0100d5 0xe7fffffff00007ff 0xf9fffffffc0001ff

def z633 : W := mkw 0x3002e84345030930 0x4c00ba10d140c24c 0x7603f9c3cc033832 0xdd80fe70f300ce0c

def z634 : W := mkw 0x0000000040000110 0x0000000010000044 0x24000033c0000732 0x0900000cf00001cc

def z635 : W := mkw 0x030009204b012510 0x00c0024812c04944 0x770039f3cf033f32 0xddc00e7cf3c0cfcc

def z636 : W := mkw 0x3722e9eb6f233db8 0x4dc8ba7adbc8cf6e 0x7703f9ffff033fff 0xddc0fe7fffc0cfff

def z637 : W := mkw 0xe3ffb7fff0002d31 0x78ffedfffc000b4c 0xe7fffffff0003f32 0xf9fffffffc000fcc

def z638 : W := mkw 0x53fbfeca2fdbc000 0x94feffb28bf6f000 0xfbffffce3fffc000 0xfefffff38ffff000

def z639 : W := mkw 0x2000896341012d30 0x48002258d0404b4c 0x750039f3c3033f32 0x9d400e7cf0c0cfcc

def z640 : W := mkw 0x0469decaf56bd9bc 0x011a77b2bd5af66f 0xfee3ffcffce3f8ff 0xffb8fff3ff38fe3f

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0x9ae000000ce00000 0xe6b8000003380000

def z642 : W := mkw 0x882401bc002436c0 0x2209006f00090db0 0xbd1c01fc031c3fc0 0xaf47007f00c70ff0

def z643 : W := mkw 0x03b000880ab01080 0x00ec002202ac0420 0xbffc01cc0ffc38c0 0xefff007303ff0e30

def z644 : W := mkw 0x2302e16304020820 0x08c0b858c1008208 0x7703f9f3cc033832 0xddc0fe7cf300ce0c

def z645 : W := mkw 0x53db7e000f030000 0x14f6df8003c0c000 0xd3fffe000f030000 0xf4ffff8003c0c000

def z646 : W := mkw 0xa02c9bfff10d4355 0x280b26fffc4350d5 0xfd1c3ffff31fc7ff 0xbf470ffffcc7f1ff

def z647 : W := mkw 0x0000080001094000 0x0000020000425000 0x18000000031fc000 0x0600000000c7f000

def z648 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xbee3c1cc0ce038c0 0xefb8f07303380e30

def z649 : W := mkw 0xc09c121490000001 0x3027048524000000 0x001c000000000000 0x0007000000000000

def z650 : W := mkw 0x0041040000408000 0x0010410000102000 0x88e0060000e0c000 0x2238018000383000

def z651 : W := mkw 0x330229214b012510 0x4cc08a4852c04944 0x370039f1cf003f00 0xcdc00e7c73c00fc0

def z652 : W := mkw 0x73db7f214fdbe510 0xdcf6dfc853f6f944 0xdbfffe31cfffc700 0xf6ffff8c73fff1c0

def z653 : W := mkw 0xe7fff7ffb4428829 0x39fffdffed10a20a 0xe3fffffff003c03f 0xf8fffffffc00f00f

def z654 : W := mkw 0xbbb2e1eb0eb23ca0 0x6eecb87ac3ac8f28 0x02e3c1c00ce03800 0x40b8f07003380e00

def z655 : W := mkw 0x3302e8434f030930 0x4cc0ba10d3c0c24c 0x5303f803cf030032 0xd4c0fe00f3c0c00c

def z656 : W := mkw 0x0000080041010110 0x0000020010404044 0x40003803c0030032 0x10000e00f000c00c

def z657 : W := mkw 0x032001a80a203480 0x00c8006a02880d20 0xbfe001fc0fe03fc0 0xeff8007f03f80ff0

def z658 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x1d1c3831c31fc7ff 0x07470e0c70c7f1ff

def z659 : W := mkw 0x3463eccb656399b8 0x4d18fb32d958e66e 0xfee3ffcffce3f8ff 0xffb8fff3ff38fe3f

def z660 : W := mkw 0x0004001490040244 0x0001000524010091 0x0000000c300000cd 0x000000030c000033

def z661 : W := mkw 0x73dbff630fdbec20 0xdcf6ffd8c3f6fb08 0xdbffffc00ffff800 0xf6fffff003fffe00

def z662 : W := mkw 0xe3f7a5ffb0000001 0x38fde97fec000000 0x22e3c1fff0000000 0x48b8f07ffc000000

def z663 : W := mkw 0x43d916000ad8c000 0x90f6458002b63000 0x9bfc06000ffcc000 0xe6ff018003ff3000

def z664 : W := mkw 0x000c1214900c4244 0x0003048524031091 0xfc1c060e301fc0ff 0xbf0701838c07f03f

def z665 : W := mkw 0xc3ff37bc00000000 0x30ffcdef00000000 0xe3fffffc00000000 0xf8ffffff00000000

def z666 : W := mkw 0x0008120000000000 0x0002048000000000 0xc11c3e0000000000 0xb0470f8000000000

def z667 : W := mkw 0x43fbb6ca20000000 0x10feedb288000000 0xe3ffffce30000000 0xf8fffff38c000000

def z668 : W := mkw 0x83b401bc00201080 0x20ed006f00080420 0xbffc01fc0ce038c0 0xefff007f03380e30

def z669 : W := mkw 0x046dd6deb46298a8 0x011b75b7ad18a62a 0xfffffffffce3f8ff 0xffffffffff38fe3f

def z670 : W := mkw 0x046184ca206098a8 0x011861328818262a 0xace007ce30e0f8ff 0x2b3801f38c383e3f

def z671 : W := mkw 0x030c1b34db0d6754 0x00c306cd36c359d5 0xff1c3fffff1fffff 0xffc70fffffc7ffff

def z672 : W := mkw 0x8bb409bc4bbd77d4 0x22ed026f12ef5df5 0xbffc01fc0fffffff 0xefff007f03ffffff

def z673 : W := mkw 0xf3f3e5eb2ed28001 0xbcfcf97acbb4a000 0x02e3c1c00ce00000 0x40b8f07003380000

def z674 : W := mkw 0x0461048820609088 0x0118412208182422 0xbee007cc3ce0f8cd 0xefb801f30f383e33

def z675 : W := mkw 0x500a3a0001094000 0x94028e8000425000 0x0000380000000000 0x00000e0000000000

def z676 : W := mkw 0x00040014d0040354 0x00010005340100d5 0xbd1c003ff31c07ff 0xaf47000ffcc701ff

def z677 : W := mkw 0x100c5a14dfdfc354 0x8403168537f7f0d5 0xfd1c3e3fffffc7ff 0xbf470f8ffffff1ff

def z678 : W := mkw 0x57fffedeffffdbfc 0x95ffffb7bffff6ff 0xffffffffffffffff 0xffffffffffffffff

def z679 : W := mkw 0x080400140ab436c0 0x0201000502ad0db0 0xbd1c003c0ffc3fc0 0xaf47000f03ff0ff0

def z680 : W := mkw 0x046d1e9cf16dd3dc 0x011b47a73c5b74f7 0xfdfc3e3ff3ffc7ff 0xbf7f0f8ffcfff1ff

def z681 : W := mkw 0xa02481fff0002d31 0x6809207ffc000b4c 0x240001fff0003f32 0x0900007ffc000fcc

def z682 : W := mkw 0x734bff634f4bed30 0xdcd2ffd8d3d2fb4c 0x7703fff3cf03ff32 0xddc0fffcf3c0ffcc

def z683 : W := mkw 0x504b7e000fdbc000 0x9412df8003f6f000 0x5803fe000fffc000 0x1600ff8003fff000

def z684 : W := mkw 0x044dde56f54fcb7c 0x01137795bd53f2df 0xfd1ffe3ff31fc7ff 0xbf47ff8ffcc7f1ff

def z685 : W := mkw 0x3002e8434f032d30 0x4c00ba10d3c0cb4c 0x5403f803cf033f32 0x1500fe00f3c0cfcc

def z686 : W := mkw 0xf3fffffff5030931 0x7cfffffffd40c24c 0xe3fffffff0030032 0xf8fffffffc00c00c

def z687 : W := mkw 0x00000800410d4354 0x00000200104350d5 0x7d003833c31fc7ff 0x9f400e0cf0c7f1ff

def z688 : W := mkw 0x330229214b012510 0x4cc08a4852c04944 0x75003833c3030732 0x9d400e0cf0c0c1cc

def z689 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x42e3fe000ce3c000 0x50b8ff800338f000

def z690 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x89fc003c03fc07c0 0x227f000f00ff01f0

def z691 : W := mkw 0x8894001400940240 0x2225000500250090 0x001c0000001c0000 0x0007000000070000

def z692 : W := mkw 0x200c9b77d10d6f74 0x480326ddf4435bdd 0xfd1c3ffff31fffff 0xbf470ffffcc7ffff

def z693 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xc81c3e0ff01fc0ff 0x32070f83fc07f03f

def z694 : W := mkw 0xf3ffffffb54bc001 0xbcffffffed52f000 0xe3fffffff003c000 0xf8fffffffc00f000

def z695 : W := mkw 0x006184ca20000000 0x0018613288000000 0xfee3c7ce3003c0ff 0xffb8f1f38c00f03f

def z696 : W := mkw 0x004d5e14d54fc354 0x001357853553f0d5 0xfffffe3fffffc7ff 0xffffff8ffffff1ff

def z697 : W := mkw 0x030001200a002400 0x00c0004802800900 0x020001c00c003800 0x4080007003000e00

def z698 : W := mkw 0xf3ffffffffdbed31 0xfcfffffffff6fb4c 0xffffffffffffff32 0xffffffffffffffcc

def z699 : W := mkw 0xf3ffffffbf030001 0x3cffffffefc0c000 0xf3ffffffff030000 0xfcffffffffc0c000

def z700 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x76e3c1c20ce33832 0xddb8f0708338ce0c

def z701 : W := mkw 0x0300c1620e022c20 0x00c0305883808b08 0x7703c1f20f033f32 0xddc0f07c83c0cfcc

def z702 : W := mkw 0x3743ed636f43ad38 0x4dd0fb58dbd0eb4e 0x7703fff3ff03ff3f 0xddc0fffcffc0ffcf

def z703 : W := mkw 0x8bb4009c0ab412c0 0x22ed002702ad04b0 0x9bfc000c0ffc00c0 0xe6ff000303ff0030

def z704 : W := mkw 0x042080ca202018a8 0x010820328808062a 0xbee001ce3ce038ff 0xefb800738f380e3f

def z705 : W := mkw 0x44f9d6ca24fad8a8 0x913e75b2893eb62a 0xfeffc7ce3cfff8ff 0xffbff1f38f3ffe3f

def z706 : W := mkw 0xdbff7e9c0fffd2c0 0xb6ffdfa703fff4b0 0xdbfffe0c0fffc0c0 0xf6ffff8303fff030

def z707 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xa3fff9fdc0000000 0xe8fffe7f70000000

def z708 : W := mkw 0x000c121490040240 0x0003048524010090 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z709 : W := mkw 0x100049204f032d30 0x4400124813c0cb4c 0x340001f00f033f32 0x0d00007c03c0cfcc

def z710 : W := mkw 0x604bb64300000000 0x1812ed90c0000000 0x4003fe03c0000000 0x1000ff80f0000000

def z711 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x1703f9f1cf033f32 0x45c0fe7c73c0cfcc

def z712 : W := mkw 0x344bfe43f54bc93c 0x4d12ff90fd52f24f 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z713 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x651c3e3ff31fc7ff 0x19470f8ffcc7f1ff

def z714 : W := mkw 0xe79e7335946298a9 0x39e79ccd6518a62a 0x1d1c3831cce3f8ff 0x07470e0c7338fe3f

def z715 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xe3fffffff003c03f 0xf8fffffffc00f00f

def z716 : W := mkw 0x604fb657b0000001 0x1813ed95ec000000 0x411ffe33f0000000 0x1047ff8cfc000000

def z717 : W := mkw 0x63dfb77790000000 0x18f7eddde4000000 0xe3fffffff0000000 0xf8fffffffc000000

def z718 : W := mkw 0x2002a16340002d30 0x4800a858d0000b4c 0x6403f9f3c0003f32 0x1900fe7cf0000fcc

def z719 : W := mkw 0x40d9160000d8c000 0x9036458000363000 0xcaffc60000fcc000 0xf2bff180003f3000

def z720 : W := mkw 0x139a7a000f9b4000 0x04e69e8003e6d000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z721 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x9efc01cc0ffc3fc0 0x67bf007303ff0ff0

def z722 : W := mkw 0x63db360190000001 0x18f6cd8064000000 0xc3fffe01c0000000 0xf0ffff8070000000

def z723 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x9ee3c7cc3ce3f8ff 0x67b8f1f30f38fe3f

def z724 : W := mkw 0x180048004f972f70 0x4600120013e5cbdc 0x140000000f1f3f32 0x0500000003c7cfcc

def z725 : W := mkw 0x53db3e000bd9c000 0x94f6cf8002f67000 0xcbfffe0003fcc000 0xf2ffff8000ff3000

def z726 : W := mkw 0x2302e1630e022c20 0x08c0b858c3808b08 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z727 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xfffc01fe0fff3ff2 0xffff007f83ffcffc

def z728 : W := mkw 0xf3ffb7ffba002401 0x7cffedffee800900 0xe3fffffff0000000 0xf8fffffffc000000

def z729 : W := mkw 0x53db7e004fdbc110 0x94f6df8013f6f044 0xfffffe3fffffc7ff 0xffffff8ffffff1ff

def z730 : W := mkw 0x40d9560004dac000 0x903655800136b000 0xc8ffc60000ffc000 0x323ff180003ff000

def z731 : W := mkw 0xf3ffb7ffba900001 0xbcffedffeea40000 0xe3fffffff0000000 0xf8fffffffc000000

def z732 : W := mkw 0x00281a88d1295194 0x000a06a2344a5465 0xfee03fcffce3f8ff 0xffb80ff3ff38fe3f

def z733 : W := mkw 0x2763a5eb20609088 0x09d8e97ac8182422 0xebe3fffff0e0c0cd 0xfaf8fffffc383033

def z734 : W := mkw 0x53db7e004fdbc110 0x94f6df8013f6f044 0xdbfffe31cfffc700 0xf6ffff8c73fff1c0

def z735 : W := mkw 0xe3ffb7ffb0201081 0x38ffedffec080420 0xe3fffffffce03800 0xf8ffffffff380e00

def z736 : W := mkw 0x98b4489c4fb73ff0 0x662d122713edcffc 0x9cfc000c0fff3ff2 0x273f000303ffcffc

def z737 : W := mkw 0x2302a16300002400 0x08c0a858c0000900 0x6703f9f3c0003f00 0xd9c0fe7cf0000fc0

def z738 : W := mkw 0x53d36c000fd38000 0x94f4db0003f4e000 0xdbfff8000fff0000 0xf6fffe0003ffc000

def z739 : W := mkw 0x8bb401bc9ab436c0 0x22ed006f26ad0db0 0xbffc01fffffc3fc0 0xefff007fffff0ff0

def z740 : W := mkw 0xe3df373590000001 0x38f7cdcd64000000 0x03fff831c0000000 0x40fffe0c70000000

def z741 : W := mkw 0xb024c9ffbfdbc001 0xac09327feff6f000 0x380001ffffffc000 0x0e00007ffffff000

def z742 : W := mkw 0x43db76000ed28000 0x10f6dd8003b4a000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z743 : W := mkw 0x2063a4cb20000000 0x0818e932c8000000 0xe2e3ffcff0000000 0xf8b8fff3fc000000

def z744 : W := mkw 0x644bfe43f54bc93d 0x1912ff90fd52f24f 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z745 : W := mkw 0x3302e9630f032400 0x0cc0ba58c3c0c900 0x7703f9f3cf033f00 0xddc0fe7cf3c0cfc0

def z746 : W := mkw 0x53d76414ded68354 0x94f5d90537b5a0d5 0x26e3c03ffce007ff 0x49b8f00fff3801ff

def z747 : W := mkw 0x77f3e5eb2ef2bca8 0xddfcf97acbbcaf2a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z748 : W := mkw 0x0000480045030930 0x000012001140c24c 0x140000000f033f32 0x0500000003c0cfcc

def z749 : W := mkw 0x100048004fdbc110 0x8400120013f6f044 0x1c0000000fffc732 0x0700000003fff1cc

def z750 : W := mkw 0xe0ffb6dfb0000001 0x383fedb7ec000000 0xe1fffe3ff0000000 0xb87fff8ffc000000

def z751 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0xe303fffff0000000 0xf8c0fffffc000000

def z752 : W := mkw 0xe392a16300000001 0x38e4a858c0000000 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z753 : W := mkw 0x04004800454fcb7c 0x010012001153f2df 0x1c000000031fc7ff 0x0700000000c7f1ff

def z754 : W := mkw 0x53db7e004fdbc110 0x94f6df8013f6f044 0xdffffe000fffc732 0xf7ffff8003fff1cc

def z755 : W := mkw 0x1000480045032d30 0x440012001140cb4c 0x0400000000033f32 0x010000000000cfcc

def z756 : W := mkw 0x2000c96345032d30 0x48003258d140cb4c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z757 : W := mkw 0xa82481fff02437d5 0x2a09207ffc090df5 0x240001fff0003fff 0x0900007ffc000fff

def z758 : W := mkw 0xa82481fff0243ff1 0x6a09207ffc090ffc 0x240001fff0003ff2 0x0900007ffc000ffc

def z759 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x4303f9f3cf033f32 0x50c0fe7cf3c0cfcc

def z760 : W := mkw 0x3002e96345032d30 0x4c00ba58d140cb4c 0x7503f9f3c3033f32 0x9d40fe7cf0c0cfcc

def z761 : W := mkw 0x8bb621bc0ab436c0 0x22ed886f02ad0db0 0xfffff9fc0ffc3fc0 0xfffffe7f03ff0ff0

def z762 : W := mkw 0xb8b6e8df45b71bf0 0x6e2dba37d16dc6fc 0xc8fff80fc0ff00f2 0x323ffe03f03fc03c

def z763 : W := mkw 0x43db36000ad8c000 0x90f6cd8002b63000 0xdbfffe000ffcc000 0xf6ffff8003ff3000

def z764 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xfffc07fe3ffc3fc0 0xffff01ff8fff0ff0

def z765 : W := mkw 0x8fd5c5762ed6ae68 0x23f5715d8bb5ab9a 0x411fc632331fc73f 0x1047f18c8cc7f1cf

def z766 : W := mkw 0x0bb000880ab436c0 0x02ec002202ad0db0 0xbffc01cc0ffc3fc0 0xefff007303ff0ff0

def z767 : W := mkw 0x53db7e004fdbc930 0xd4f6df8013f6f24c 0xdbfffe000fffc032 0xf6ffff8003fff00c

def z768 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xc3fffe000ffc0000 0xf0ffff8003ff0000

def z769 : W := mkw 0xe04fb777b0000001 0x3813edddec000000 0x4003fe33f0000000 0x1000ff8cfc000000

def z770 : W := mkw 0x43db3e000b994000 0x10f6cf8002e65000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z771 : W := mkw 0x57babaca2bb958a8 0x95eeaeb28aee562a 0x251c39ce331c38ff 0x09470e738cc70e3f

def z772 : W := mkw 0x2302a1630a002400 0x08c0a858c2800900 0x0203c1c00c003800 0x4080f07003000e00

def z773 : W := mkw 0x53db7e000fdbc820 0x94f6df8003f6f208 0xdffffe000ffff832 0xf7ffff8003fffe0c

def z774 : W := mkw 0x50d95e000fdbc000 0x9436578003f6f000 0xdaffc6000fffc000 0xf6bff18003fff000

def z775 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0xfc03fe0ff003c0ff 0xbf00ff83fc00f03f

def z776 : W := mkw 0xe3ffb7ffb0408001 0x38ffedffec102000 0xebfffffff0e0c000 0xfafffffffc383000

def z777 : W := mkw 0xeff3e5eb2ef2bca9 0x3bfcf97acbbcaf2a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z778 : W := mkw 0x2322a1eb00201080 0x08c8a87ac0080420 0xffe3f9ffcce038c0 0xfff8fe7ff3380e30

def z779 : W := mkw 0x634bb763ba002401 0x18d2edd8ee800900 0x7703fff3ff003f00 0xddc0fffcffc00fc0

def z780 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xfbfffffff31c0000 0xfefffffffcc70000

def z781 : W := mkw 0x8fb401bc2ab436c8 0x23ed006f0aad0db2 0xbffc01fc3ffc3fcd 0xefff007f0fff0ff3

def z782 : W := mkw 0x73db7f214fdbed30 0xdcf6dfc853f6fb4c 0xdffffe31cfffff32 0xf7ffff8c73ffffcc

def z783 : W := mkw 0x684bb643bab436c1 0x1a12ed90eead0db0 0x5c03fe03fffc3fc0 0x1700ff80ffff0ff0

def z784 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xffffffffffffffff 0xffffffffffffffff

def z785 : W := mkw 0x43db360000000000 0x10f6cd8000000000 0xe3fffe33c0000000 0xf8ffff8cf0000000

def z786 : W := mkw 0x53db76000edac000 0x94f6dd8003b6b000 0xcbfffe000cfcc000 0xf2ffff80033f3000

def z787 : W := mkw 0xe3beb3ff90000001 0x38efacffe4000000 0xe3fff9ffc0000000 0xf8fffe7ff0000000

def z788 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xfbfffffffce00000 0xfeffffffff380000

def z789 : W := mkw 0x644bb643b0000829 0x1912ed90ec00020a 0x4003fe03f000003f 0x1000ff80fc00000f

def z790 : W := mkw 0x13d14c000fdbc000 0x84f4530003f6f000 0xdbffc6000fffc000 0xf6fff18003fff000

def z791 : W := mkw 0x8bb001a80ab436c0 0x22ec006a02ad0db0 0x9ffc01c00ffc3fc0 0xe7ff007003ff0ff0

def z792 : W := mkw 0x2302a1634a002d30 0x48c0a858d2800b4c 0x7703f9f3cf003f32 0xddc0fe7cf3c00fcc

def z793 : W := mkw 0xabb6a1ffbab436c1 0x2aeda87feead0db0 0xfffff9fffffc3fc0 0xfffffe7fffff0ff0

def z794 : W := mkw 0x53db7f200fdbc000 0x94f6dfc803f6f000 0xfbfffff00fffc000 0xfefffffc03fff000

def z795 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xffe3c7fe3fe3ffff 0xfff8f1ff8ff8ffff

def z796 : W := mkw 0x242481fff0243ffc 0x4909207ffc090fff 0x240001fff0003fff 0x0900007ffc000fff

def z797 : W := mkw 0x53db7e00dfdbc114 0x94f6df8037f6f045 0xfffffe0fffffc0ff 0xffffff83fffff03f

def z798 : W := mkw 0x60d9976340d8ed30 0xd83665d8d0363b4c 0xacfc07f3c0fcff32 0x2b3f01fcf03f3fcc

def z799 : W := mkw 0xe3ffb7ffb0dcc245 0xb8ffedffec373091 0xebfffffff0fcc0cd 0xfafffffffc3f3033

def z800 : W := mkw 0x3392e9634fdbed30 0xcce4ba58d3f6fb4c 0xfffff9f3cfffff32 0xfffffe7cf3ffffcc

def z801 : W := mkw 0x53db7e00dfdbc114 0x94f6df8037f6f045 0xdbfffe01cfffc000 0xf6ffff8073fff000

def z802 : W := mkw 0x63d3a56300000000 0x18f4e958c0000000 0x63e3f9f3c0000000 0xd8f8fe7cf0000000

def z803 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xc1fffe3ff0000000 0x307fff8ffc000000

def z804 : W := mkw 0xe06fb6dfb0000001 0x381bedb7ec000000 0x4003fe0ff0000000 0x1000ff83fc000000

def z805 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x1c0000000f03ffff 0x0700000003c0ffff

def z806 : W := mkw 0x8cfd169cb0fcd2cc 0x233f45a72c3f34b3 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z807 : W := mkw 0x43d956000edac000 0x90f6558003b6b000 0xdbffc6000fffc000 0xf6fff18003fff000

def z808 : W := mkw 0xe3fbb7eb20000001 0x38feedfac8000000 0xe3fffff3c0000000 0xf8fffffcf0000000

def z809 : W := mkw 0x8c2480de20241ae8 0x23092037880906ba 0x240001ce300038ff 0x090000738c000e3f

def z810 : W := mkw 0x3302a9634b012510 0x4cc0aa58d2c04944 0x7703f9f3cf003f00 0xddc0fe7cf3c00fc0

def z811 : W := mkw 0x100048004f030930 0x4400120013c0c24c 0x100000000f030032 0x0400000003c0c00c

def z812 : W := mkw 0x330ef3779e0e6e64 0x4cc3bcdde7839b99 0x8a1fc7cc3c1cf8cd 0x6287f1f30f073e33

def z813 : W := mkw 0xa3b2a1eb00000000 0x28eca87ac0000000 0x63e3f9f3c0000000 0xd8f8fe7cf0000000

def z814 : W := mkw 0x100048004f072f70 0x4400120013c1cbdc 0x1c0000000f1f3ff2 0x0700000003c7cffc

def z815 : W := mkw 0xe3f3adeb610d4355 0x38fceb7ad84350d5 0x1ee3c1c0031fc7ff 0x47b8f07000c7f1ff

def z816 : W := mkw 0x3702e9636f032d38 0x4dc0ba58dbc0cb4e 0x7703f9f3ff033f3f 0xddc0fe7cffc0cfcf

def z817 : W := mkw 0x3302e9634f4bed30 0xccc0ba58d3d2fb4c 0x7703f9f3cf03ff32 0xddc0fe7cf3c0ffcc

def z818 : W := mkw 0xe3ffb7ffb0002c21 0x78ffedffec000b08 0xe3fffffff0003800 0xf8fffffffc000e00

def z819 : W := mkw 0x03b001a80ab03480 0x00ec006a02ac0d20 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z820 : W := mkw 0x180048004ffffff0 0xc600120013fffffc 0x1c0000000ffffff2 0x0700000003fffffc

def z821 : W := mkw 0xebffb7ffb02436c1 0x3affedffec090db0 0xfffffffffce03fc0 0xffffffffff380ff0

def z822 : W := mkw 0xe3ffb7ffb0084005 0x38ffedffec021001 0xe3fffffff000c00d 0xf8fffffffc003003

def z823 : W := mkw 0x039220000a900000 0x00e4880002a40000 0xdbfff8000ffc0000 0xf6fffe0003ff0000

def z824 : W := mkw 0x43ffb6deb0000000 0x10ffedb7ac000000 0xe3fffffff0000000 0xf8fffffffc000000

def z825 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0xffe3f9f3cfe33f32 0xfff8fe7cf3f8cfcc

def z826 : W := mkw 0x53d364000ed28000 0x94f4d90003b4a000 0xdbffc6000fffc000 0xf6fff18003fff000

def z827 : W := mkw 0xe3df373590000001 0x38f7cdcd64000000 0xe3fffe3ff0000000 0xf8ffff8ffc000000

def z828 : W := mkw 0x53db7e004fdbc114 0x94f6df8013f6f045 0xdbfffe000fffc03f 0xf6ffff8003fff00f

def z829 : W := mkw 0xe3dfb77790000001 0x38f7eddde4000000 0xe3fffff3c0000000 0xf8fffffcf0000000

def z830 : W := mkw 0xebffb7ff0ab436c0 0x3affedffc2ad0db0 0xffffffffcffc3fc0 0xfffffffff3ff0ff0

def z831 : W := mkw 0xd0fd5e9cff032d31 0x743f57a73fc0cb4c 0x94fc060c3f033f32 0x253f01830fc0cfcc

def z832 : W := mkw 0xe3ffb7ffb0000821 0x38ffedffec000208 0xe7fffffff0003832 0xf9fffffffc000e0c

def z833 : W := mkw 0xe0ffb6dfb0000001 0x383fedb7ec000000 0xe2ffffcff0000000 0xf8bffff3fc000000

def z834 : W := mkw 0x046ddedef56fdbfc 0x011b77b7bd5bf6ff 0x03fff9f1cffc3f00 0x40fffe7c73ff0fc0

def z835 : W := mkw 0x606bb6cbb0201081 0x181aedb2ec080420 0xfee3ffcffce038c0 0xffb8fff3ff380e30

def z836 : W := mkw 0xe3dbb763b0000001 0x38f6edd8ec000000 0x4003fe03f0000000 0x1000ff80fc000000

def z837 : W := mkw 0x8c2481fef0243ffc 0x2309207fbc090fff 0x240001fff0003fff 0x0900007ffc000fff

def z838 : W := mkw 0x2392a1630a900000 0x08e4a858c2a40000 0xfbfff9f3cffc0000 0xfefffe7cf3ff0000

def z839 : W := mkw 0x200eb25790000000 0x0803ac95e4000000 0xe11ffe3ff0000000 0xb847ff8ffc000000

def z840 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xfffffe020fffc032 0xffffff8083fff00c

def z841 : W := mkw 0x53db7f204fdbed30 0xd4f6dfc813f6fb4c 0xfffffff00fffff32 0xfffffffc03ffffcc

def z842 : W := mkw 0xac2481ff60243ff8 0x6b09207fd8090ffe 0x240001fff0003fff 0x0900007ffc000fff

def z843 : W := mkw 0x2322a1eb00000000 0x08c8a87ac0000000 0xe3e3f9ffc0000000 0xf8f8fe7ff0000000

def z844 : W := mkw 0x102048884f233db0 0x4408122213c8cf6c 0xbee001cc0fe33ff2 0xefb8007303f8cffc

def z845 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x0303f9f1c0000000 0x40c0fe7c70000000

def z846 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xfffc39ffcffc3fc0 0xffff0e7ff3ff0ff0

def z847 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xffffffc00ffff800 0xfffffff003fffe00

def z848 : W := mkw 0xbbb621bd0ab436c0 0x6eed886f42ad0db0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z849 : W := mkw 0x180048004fb33db0 0x4600120013eccf6c 0x140000000fe33f32 0x0500000003f8cfcc

def z850 : W := mkw 0x140048004f233db8 0x4500120013c8cf6e 0x140000000f033fff 0x0500000003c0cfff

def z851 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0xe003fe0ff0000000 0xb800ff83fc000000

def z852 : W := mkw 0x0041c44204428820 0x001071108110a208 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z853 : W := mkw 0xebffb7ffbab03481 0x3affedffeeac0d20 0xfbfffffffffc3800 0xfeffffffffff0e00

def z854 : W := mkw 0x50d95e004fdbed30 0xd436578013f6fb4c 0x9cfc06000fffff32 0x273f018003ffffcc

def z855 : W := mkw 0x10004800454bc930 0xc40012001152f24c 0x000000000003c032 0x000000000000f00c

def z856 : W := mkw 0xe3ffb7ffb0900001 0x38ffedffec240000 0xebfffffff0fc0000 0xfafffffffc3f0000

def z857 : W := mkw 0xebdfb777ba942641 0x3af7edddeea50990 0x411ffe33f31c0700 0x1047ff8cfcc701c0

def z858 : W := mkw 0x73db7f214fdbe510 0xdcf6dfc853f6f944 0xfffffe33cfffc732 0xffffff8cf3fff1cc

def z859 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x3703f9f1cf003f00 0xcdc0fe7c73c00fc0

def z860 : W := mkw 0x73db7f214fdbe510 0xdcf6dfc853f6f944 0xfffffff1cfffff00 0xfffffffc73ffffc0

def z861 : W := mkw 0x83b401bc002412c0 0x20ed006f000904b0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z862 : W := mkw 0xe3ffb7ffb00c4245 0x38ffedffec031091 0xfffffffff01fc0ff 0xfffffffffc07f03f

def z863 : W := mkw 0xccfd169cb0f492c9 0x333f45a72c3d24b2 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z864 : W := mkw 0x0041440004428000 0x001051000110a000 0xdbffc6000fffc000 0xf6fff18003fff000

def z865 : W := mkw 0x8bb81ba8dbb97594 0x22ee06ea36ee5d65 0x42e03fc3fce3f83f 0x50b80ff0ff38fe0f

def z866 : W := mkw 0x9bb049a84fb33db0 0x66ec126a13eccf6c 0x16e001c00fe33f32 0x45b8007003f8cfcc

def z867 : W := mkw 0xbb92e9634f932d30 0x6ee4ba58d3e4cb4c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z868 : W := mkw 0xabb2a1eb0ab03480 0x2aeca87ac2ac0d20 0x63e3f9f3cce03800 0xd8f8fe7cf3380e00

def z869 : W := mkw 0x57db7e002fdbc008 0x95f6df800bf6f002 0xdbfffe003fffc00d 0xf6ffff800ffff003

def z870 : W := mkw 0x100048004f9b6d30 0xc400120013e6db4c 0x140000000f1f3f32 0x0500000003c7cfcc

def z871 : W := mkw 0x04004800454bc93c 0x010012001152f24f 0x000000000003c03f 0x000000000000f00f

def z872 : W := mkw 0xa82481ff002436c0 0x2a09207fc0090db0 0x240001ffc0003fc0 0x0900007ff0000ff0

def z873 : W := mkw 0xe3ffb7ffba203481 0x38ffedffee880d20 0xffffffffffe03fc0 0xfffffffffff80ff0

def z874 : W := mkw 0x00454414d4468354 0x001151053511a0d5 0xfee3c63ffce3c7ff 0xffb8f18fff38f1ff

def z875 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x53fff8000fff0000 0xd4fffe0003ffc000

def z876 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xc2ffffcff0000000 0x70bffff3fc000000

def z877 : W := mkw 0x88b4009c00b412c0 0x222d0027002d04b0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z878 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0xc11ffe03f0000000 0xb047ff80fc000000

def z879 : W := mkw 0xe3fbb7ebb0000001 0x38feedfaec000000 0xc3ffffc3f0000000 0xf0fffff0fc000000

def z880 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0x6203ffc3f0000000 0xd880fff0fc000000

def z881 : W := mkw 0x644bb643b0408009 0x1912ed90ec102002 0x4003fe03f000c00d 0x1000ff80fc003003

def z882 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x6303f9f3cf003f00 0xd8c0fe7cf3c00fc0

def z883 : W := mkw 0xc3ff37bc90000000 0x30ffcdef24000000 0xe3fffffff0000000 0xf8fffffffc000000

def z884 : W := mkw 0x3392e9634f032d30 0x4ce4ba58d3c0cb4c 0xf7fff9f3cf033f32 0xfdfffe7cf3c0cfcc

def z885 : W := mkw 0xe3ffb7ffb0040241 0x38ffedffec010090 0xebfffffff01c00c0 0xfafffffffc070030

def z886 : W := mkw 0x004d161490000000 0x0013458524000000 0xe3fffe3ff0000000 0xf8ffff8ffc000000

def z887 : W := mkw 0xebdf37359a942641 0x3af7cdcd66a50990 0xdbfffe31cffc0700 0xf6ffff8c73ff01c0

def z888 : W := mkw 0x00495600044ac000 0x001255800112b000 0xdaffc6000cffc000 0xf6bff180033ff000

def z889 : W := mkw 0x3302e9634fd3ad30 0xccc0ba58d3f4eb4c 0x7703f9f3cfe33f32 0xddc0fe7cf3f8cfcc

def z890 : W := mkw 0x604fb657b0000001 0x1813ed95ec000000 0x6003fe3ff0000000 0x1800ff8ffc000000

def z891 : W := mkw 0x2322a1eb20000000 0x08c8a87ac8000000 0x6303f9fff0000000 0xd8c0fe7ffc000000

def z892 : W := mkw 0x0b9001200ab436c0 0x02e4004802ad0db0 0xbffc01f00ffc3fc0 0xefff007c03ff0ff0

def z893 : W := mkw 0xa82481ffb02412c1 0x2a09207fec0904b0 0x200001fff00000c0 0x0800007ffc000030

def z894 : W := mkw 0x100048004fdfef74 0xc400120013f7fbdd 0x1c0000000fffffff 0x0700000003ffffff

def z895 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xff1c3fffff1fffff 0xffc70fffffc7ffff

def z896 : W := mkw 0x2392a16300000000 0x08e4a858c0000000 0xe3fff9f3c0000000 0xf8fffe7cf0000000

def z897 : W := mkw 0x006184ca20000000 0x0018613288000000 0xe3e3fffff0000000 0xf8f8fffffc000000

def z898 : W := mkw 0x53db7f200fdbe400 0x94f6dfc803f6f900 0xdbffffc00ffff800 0xf6fffff003fffe00

def z899 : W := mkw 0x43db360000d8c000 0x90f6cd8000363000 0x8affc60000fcc000 0x62bff180003f3000

def z900 : W := mkw 0x2002a04300000000 0x0800a810c0000000 0x6103f833c0000000 0x9840fe0cf0000000

def z901 : W := mkw 0x53db7e0005dbc000 0x94f6df800176f000 0xcbfffe0000ffc000 0xf2ffff80003ff000

def z902 : W := mkw 0x3302e9634f932d30 0x4cc0ba58d3e4cb4c 0x7f03f9f3cfff3f32 0xdfc0fe7cf3ffcfcc

def z903 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x9bfff8000ffc0000 0xe6fffe0003ff0000

def z904 : W := mkw 0x230eb37790000000 0x08c3acdde4000000 0x631ff9f3c0000000 0xd8c7fe7cf0000000

def z905 : W := mkw 0x88b401bc0ab436c0 0x222d006f02ad0db0 0xbcfc01fc0ffc3fc0 0x2f3f007f03ff0ff0

def z906 : W := mkw 0x43df36149a940240 0x10f7cd8526a50090 0xfffffe3ffffc07c0 0xffffff8fffff01f0

def z907 : W := mkw 0x8c2481fe20243ee8 0x2309207f88090fba 0x240001fc00003fc0 0x0900007f00000ff0

def z908 : W := mkw 0xdb9e3b34db9d6754 0xb6e78ecd36e759d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z909 : W := mkw 0x14004800456399b8 0x450012001158e66e 0x1c0000000ce3f8ff 0x070000000338fe3f

def z910 : W := mkw 0xe7ffb7ffb0609089 0x39ffedffec182422 0xfffffffffce0f8cd 0xffffffffff383e33

def z911 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x43fffe000fffc000 0x50ffff8003fff000

def z912 : W := mkw 0xe39e333590000001 0x38e78ccd64000000 0x431ff831c0000000 0xd0c7fe0c70000000

def z913 : W := mkw 0xe7ffb7ffb0609089 0x39ffedffec182422 0xe3fffffff0e00000 0xf8fffffffc380000

def z914 : W := mkw 0xebffb7ffb0b01081 0x3affedffec2c0420 0xe3fffffff0e00000 0xf8fffffffc380000

def z915 : W := mkw 0xebffb7ffb02436c1 0x3affedffec090db0 0xfffffffff31c3fc0 0xfffffffffcc70ff0

def z916 : W := mkw 0x10004800450f4b74 0x440012001143d2dd 0x1c000000031fc7ff 0x0700000000c7f1ff

def z917 : W := mkw 0x006d96deb02412c0 0x001b65b7ac0904b0 0xfffffffffffc3fc0 0xffffffffffff0ff0

def z918 : W := mkw 0xabb621bd0ab436c0 0x2aed886f42ad0db0 0xbffc39fdcffc3fc0 0xefff0e7f73ff0ff0

def z919 : W := mkw 0x100048004f233db0 0x4400120013c8cf6c 0x1c0000000fe33ff2 0x0700000003f8cffc

def z920 : W := mkw 0xabb6a1ff00b412c0 0x2aeda87fc02d04b0 0xebfff9ffc0fc00c0 0xfafffe7ff03f0030

def z921 : W := mkw 0x50db760004dac000 0x9436dd800136b000 0x88ffc60000fcc000 0x223ff180003f3000

def z922 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0x0003f801c0000000 0x0000fe0070000000

def z923 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0xff03fffff003c0ff 0xffc0fffffc00f03f

def z924 : W := mkw 0x53db7e000fdbec20 0xd4f6df8003f6fb08 0xdbfffe000ffff800 0xf6ffff8003fffe00

def z925 : W := mkw 0x3002e9634f032d30 0x4c00ba58d3c0cb4c 0x7403f9f3cf033f32 0x1d00fe7cf3c0cfcc

def z926 : W := mkw 0xa322a1eb20000001 0x28c8a87ac8000000 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z927 : W := mkw 0x604fb657b0000001 0x1813ed95ec000000 0xc01ffe0ff0000000 0x3007ff83fc000000

def z928 : W := mkw 0x100048004fdbc114 0x8400120013f6f045 0x180000000fffc03f 0x0600000003fff00f

def z929 : W := mkw 0x2043a44320000000 0x0810e910c8000000 0x4003fe03f0000000 0x1000ff80fc000000

def z930 : W := mkw 0x3002e96345032d30 0x4c00ba58d140cb4c 0x7603f9f3cc033f32 0xdd80fe7cf300cfcc

def z931 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xfbfffe33cfffc000 0xfeffff8cf3fff000

def z932 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x8bfffe000ffcc000 0x62ffff8003ff3000

def z933 : W := mkw 0xe3f7a5ffb0000001 0x38fde97fec000000 0x63e3f9fff0000000 0xd8f8fe7ffc000000

def z934 : W := mkw 0x2363a5eb2a203480 0x08d8e97aca880d20 0xffe3ffffffe03fc0 0xfff8fffffff80ff0

def z935 : W := mkw 0xac2481ffb0243ee9 0x2b09207fec090fba 0x240001fff0003fff 0x0900007ffc000fff

def z936 : W := mkw 0x0000804200000000 0x0000201080000000 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z937 : W := mkw 0xefffb7ffbab43ee9 0x3bffedffeead0fba 0xfffffffffffc3fff 0xffffffffffff0fff

def z938 : W := mkw 0x704bfe43d54bc934 0xdc12ff90f552f24d 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z939 : W := mkw 0x04004800456bd9bc 0x01001200115af66f 0x1c0000000ce3f8ff 0x070000000338fe3f

def z940 : W := mkw 0x00499642b0000000 0x00126590ac000000 0x4003fe03f0000000 0x1000ff80fc000000

def z941 : W := mkw 0x0424489c456fdbfc 0x01091227115bf6ff 0xbffc01fc0fffffff 0xefff007f03ffffff

def z942 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xbffc01fc0fffffff 0xefff007f03ffffff

def z943 : W := mkw 0xe3f3a5eb20000001 0x38fce97ac8000000 0x03e3f9f1c0000000 0x40f8fe7c70000000

def z944 : W := mkw 0x000cd256940e4a64 0x00033495a5039299 0xfe1fc7ce3c1ff8ff 0xff87f1f38f07fe3f

def z945 : W := mkw 0x53db7e009fdbc000 0x94f6df8027f6f000 0xdbfffe03ffffc000 0xf6ffff80fffff000

def z946 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x7703f9f3cc003800 0xddc0fe7cf3000e00

def z947 : W := mkw 0x882481fe202436c0 0x2209207f88090db0 0x240001fe30003fc0 0x0900007f8c000ff0

def z948 : W := mkw 0x88b4009c0ab436c0 0x222d002702ad0db0 0xbefc01cc0ffc3fc0 0xefbf007303ff0ff0

def z949 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xebfffffffcfc38c0 0xfaffffffff3f0e30

def z950 : W := mkw 0xe3ffb7ffb0201081 0x38ffedffec080420 0xe7fffffff00038c0 0xf9fffffffc000e30

def z951 : W := mkw 0x93b449bc4f032d30 0x64ed126f13c0cb4c 0xb7fc01fc0f033f32 0xedff007f03c0cfcc

def z952 : W := mkw 0x3302e1630e022c20 0x4cc0b858c3808b08 0x7703f9f3cf003f00 0xddc0fe7cf3c00fc0

def z953 : W := mkw 0x1302e8424f030930 0x04c0ba1093c0c24c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z954 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0x6103fe33f0000000 0x9840ff8cfc000000

def z955 : W := mkw 0xebffb7ffb02412c1 0x3affedffec0904b0 0xe3fffffff00000c0 0xf8fffffffc000030

def z956 : W := mkw 0xc8fd169cb02412c1 0x323f45a72c0904b0 0x80fc060c300000c0 0x203f01830c000030

def z957 : W := mkw 0x2306a17700040240 0x08c1a85dc0010090 0xff1ff9ffc31c07c0 0xffc7fe7ff0c701f0

def z958 : W := mkw 0xebffb7ffbab03481 0x3affedffeeac0d20 0xfffffffffce038c0 0xffffffffff380e30

def z959 : W := mkw 0x330269214f032510 0x4cc09a4853c0c944 0x7703f9f1cf033f00 0xddc0fe7c73c0cfc0

def z960 : W := mkw 0x139268000fdbc000 0x84e49a0003f6f000 0xdbfff8000fffc000 0xf6fffe0003fff000

def z961 : W := mkw 0xe0ffb7ffb0000001 0x383fedffec000000 0xe0fffffff0000000 0x383ffffffc000000

def z962 : W := mkw 0x63db372100000000 0x18f6cdc840000000 0xc3fffe31c0000000 0xf0ffff8c70000000

def z963 : W := mkw 0xe3ffb7ffba940241 0x38ffedffeea50090 0xfffffffffffc07c0 0xffffffffffff01f0

def z964 : W := mkw 0x646bb6cbb0609089 0x191aedb2ec182422 0xc8e3fe0ff0e0c0cd 0x3238ff83fc383033

def z965 : W := mkw 0x3392e9634f932d30 0x4ce4ba58d3e4cb4c 0x771ff9f3cf1f3f32 0xddc7fe7cf3c7cfcc

def z966 : W := mkw 0xefffb7ffb0f492c9 0x3bffedffec3d24b2 0xebfffffff0fcc0cd 0xfafffffffc3f3033

def z967 : W := mkw 0x100048004f0f4354 0x0400120013c3d0d5 0x1c0000000f1fc7ff 0x0700000003c7f1ff

def z968 : W := mkw 0x8bb401bcbab436c1 0x22ed006f2ead0db0 0xbffc01fc3ffc3fc0 0xefff007f0fff0ff0

def z969 : W := mkw 0x37632da96b61b598 0x4dd8cb6a5ad86d66 0x89e03e3df3e0c7cd 0x22780f8f7cf831f3

def z970 : W := mkw 0x606bb6cbb0000001 0x181aedb2ec000000 0xc0e3fe0ff0000000 0x3038ff83fc000000

def z971 : W := mkw 0x50db7e0005dbc000 0x9436df800176f000 0xdafffe000cffc000 0xf6bfff80033ff000

def z972 : W := mkw 0x43db360000900000 0x10f6cd8000240000 0xcbfffe0000fc0000 0xf2ffff80003f0000

def z973 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xfffffe300fffc700 0xffffff8c03fff1c0

def z974 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x000000000c033832 0x000000000300ce0c

def z975 : W := mkw 0xbff3e5eb2ef2bca8 0x6ffcf97acbbcaf2a 0x02e3c1c00ce03800 0x40b8f07003380e00

def z976 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xdbfffe023fffc03f 0xf6ffff808ffff00f

def z977 : W := mkw 0xebffb7ffb0b436c1 0x3affedffec2d0db0 0xeffffffff0fc3fc0 0xfbfffffffc3f0ff0

def z978 : W := mkw 0x3302e9634f0b6d30 0x4cc0ba58d3c2db4c 0x7f03f9f3cf1fff32 0xdfc0fe7cf3c7ffcc

def z979 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xc91c3e3ff31fc7ff 0x32470f8ffcc7f1ff

def z980 : W := mkw 0x639ab36300000000 0x18e6acd8c0000000 0x631ff9f3c0000000 0xd8c7fe7cf0000000

def z981 : W := mkw 0x2002a16300000000 0x0800a858c0000000 0x6003f9f3c0000000 0x1800fe7cf0000000

def z982 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xbffc07fc3ffcffcd 0xefff01ff0fff3ff3

def z983 : W := mkw 0xe3ffb7ffb0201081 0x38ffedffec080420 0xfffffffffce3f8ff 0xffffffffff38fe3f

def z984 : W := mkw 0x172049a84f63bdb8 0x45c8126a13d8ef6e 0xbfe001fc0fe3ffff 0xeff8007f03f8ffff

def z985 : W := mkw 0x239081634a902d30 0x48e42058d2a40b4c 0xbffc01f3cffc3f32 0xefff007cf3ff0fcc

def z986 : W := mkw 0x10495e000fdbc000 0x8412578003f6f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z987 : W := mkw 0x53db7e00bfdbc001 0x94f6df802ff6f000 0xdbfffe003fffc000 0xf6ffff800ffff000

def z988 : W := mkw 0x006184ca20201080 0x0018613288080420 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z989 : W := mkw 0x042480de20241ae8 0x01092037880906ba 0x240001fe30003fff 0x0900007f8c000fff

def z990 : W := mkw 0x630ab36390000001 0x18c2acd8e4000000 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z991 : W := mkw 0xa396a17700000000 0x28e5a85dc0000000 0x631ff9f3c0000000 0xd8c7fe7cf0000000

def z992 : W := mkw 0x53db76000edac000 0x94f6dd8003b6b000 0x9bffc6000ffcc000 0xe6fff18003ff3000

def z993 : W := mkw 0x130048004f032d30 0x44c0120013c0cb4c 0x170000000f033f32 0xc5c0000003c0cfcc

def z994 : W := mkw 0xe3ffb7ff00000000 0x38ffedffc0000000 0xe3ffffffc0000000 0xf8fffffff0000000

def z995 : W := mkw 0x2b02a1630ab436c0 0x0ac0a858c2ad0db0 0x7f03f9f3cffc3fc0 0xdfc0fe7cf3ff0ff0

def z996 : W := mkw 0xabf7a5ff2ab436c0 0x2afde97fcaad0db0 0xfffffffffffc3fc0 0xffffffffffff0ff0

def z997 : W := mkw 0x63dbb64300000000 0x18f6ed90c0000000 0xc3fffe03c0000000 0xf0ffff80f0000000

def z998 : W := mkw 0x140048004f43ad38 0x4500120013d0eb4e 0x140000000f03ff3f 0x0500000003c0ffcf

def z999 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x23fff9fff0000000 0x48fffe7ffc000000

def z1000 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xfffffffff00000c0 0xfffffffffc000030

def z1001 : W := mkw 0x6043a44320000001 0x1810e910c8000000 0x4003f803c0000000 0x1000fe00f0000000

def z1002 : W := mkw 0xe86fb7ffb02436c1 0x3a1bedffec090db0 0x6403fffff0003fc0 0x1900fffffc000ff0

def z1003 : W := mkw 0xe3ffb7ffb0084001 0x38ffedffec021000 0xebfffffff01cc000 0xfafffffffc073000

def z1004 : W := mkw 0x404f361490000000 0x1013cd8524000000 0xe11ffe3ff0000000 0xb847ff8ffc000000

def z1005 : W := mkw 0xebb621bd0ab436c1 0x3aed886f42ad0db0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z1006 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x360001c00f033f32 0xcd80007003c0cfcc

def z1007 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xe7fffffff00000ff 0xf9fffffffc00003f

def z1008 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x62e3fffff0000000 0x58b8fffffc000000

def z1009 : W := mkw 0xe06bb7ebb0000001 0x381aedfaec000000 0x4003ffc3f0000000 0x1000fff0fc000000

def z1010 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xfbfffe0e3fffc000 0xfeffff838ffff000

def z1011 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0x03fff9f1cffc3f00 0x40fffe7c73ff0fc0

def z1012 : W := mkw 0x2302e96345030930 0x08c0ba58d140c24c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1013 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x4103f833c0000000 0x1040fe0cf0000000

def z1014 : W := mkw 0x50db7e000fdbc000 0x9436df8003f6f000 0xd8fffe000fffc000 0x363fff8003fff000

def z1015 : W := mkw 0x3000c9634f032d30 0x4c003258d3c0cb4c 0x140001c00f033f32 0x0500007003c0cfcc

def z1016 : W := mkw 0xe3f3a5eb20000001 0x38fce97ac8000000 0xe3e3fffff0000000 0xf8f8fffffc000000

def z1017 : W := mkw 0xe3fbb7ebb0000001 0x38feedfaec000000 0x63e3fff3f0000000 0xd8f8fffcfc000000

def z1018 : W := mkw 0x50db7e0005dbc000 0x9436df800176f000 0xd9fffe0003ffc000 0xb67fff8000fff000

def z1019 : W := mkw 0xe3ffb7ffba000001 0x38ffedffee800000 0xf3ffffffff000000 0xfcffffffffc00000

def z1020 : W := mkw 0x00081a0041094110 0x0002068010425044 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z1021 : W := mkw 0x53db7f200fdbe400 0x94f6dfc803f6f900 0xdbfffe300fffc700 0xf6ffff8c03fff1c0

def z1022 : W := mkw 0xe06fb7ffb0000001 0x381bedffec000000 0xe2e3fffff0000000 0xf8b8fffffc000000

def z1023 : W := mkw 0x50dd5e14dfdfc354 0x9437578537f7f0d5 0x9cfc060c3fffc7ff 0x273f01830ffff1ff

def z1024 : W := mkw 0x40db360000d8c000 0x9036cd8000363000 0xc8fffe0000fcc000 0x323fff80003f3000

def z1025 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xebfffffff3fc07c0 0xfafffffffcff01f0

def z1026 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x1bfff8000fffc000 0x46fffe0003fff000

def z1027 : W := mkw 0xe3ffb7ffb0040241 0x38ffedffec010090 0xe3fffffff31c0700 0xf8fffffffcc701c0

def z1028 : W := mkw 0x14614c886f63bdb8 0x451853221bd8ef6e 0x9ce0060c3fe3ffff 0x273801830ff8ffff

def z1029 : W := mkw 0x73db7f210fdbc000 0x9cf6dfc843f6f000 0xdbfffe31cfffc000 0xf6ffff8c73fff000

def z1030 : W := mkw 0x03d144000ed28000 0x00f4510003b4a000 0x9bffc0000ffc0000 0xe6fff00003ff0000

def z1031 : W := mkw 0x100048004fdbe510 0xc400120013f6f944 0x180000000fffc700 0x0600000003fff1c0

def z1032 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0xc2e3fe03f0000000 0xf0b8ff80fc000000

def z1033 : W := mkw 0xe3ffb7ffba902401 0x38ffedffeea40900 0xfffffffffffc3f00 0xffffffffffff0fc0

def z1034 : W := mkw 0x00004800454fc354 0x000012001153f0d5 0x1c0000000fffc7ff 0x0700000003fff1ff

def z1035 : W := mkw 0xebffb7ffba942641 0x3affedffeea50990 0xfbfffffffffc0700 0xfeffffffffff01c0

def z1036 : W := mkw 0xa306a17790000001 0x28c1a85de4000000 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z1037 : W := mkw 0xebffb7ffb0fcd2c1 0xbaffedffec3f34b0 0xebfffffff0fcc0c0 0xfafffffffc3f3030

def z1038 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x2703f9f3cf003f32 0x49c0fe7cf3c00fcc

def z1039 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x7f03f9f3cf03ffff 0xdfc0fe7cf3c0ffff

def z1040 : W := mkw 0x230eb377900c4244 0x08c3acdde4031091 0xeb1ffffff01cc0cd 0xfac7fffffc073033

def z1041 : W := mkw 0xefffb7ffb0243ee9 0x3bffedffec090fba 0xe7fffffff0003fff 0xf9fffffffc000fff

def z1042 : W := mkw 0xa3b6a1ffb0000001 0x28eda87fec000000 0xe3fff9fff0000000 0xf8fffe7ffc000000

def z1043 : W := mkw 0xc4fd169cb06cd2cd 0x313f45a72c1b34b3 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z1044 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x7703f9f3c3000700 0xddc0fe7cf0c001c0

def z1045 : W := mkw 0xeb9eb3779a942641 0x3ae7acdde6a50990 0x771ff9f3cf1c3f00 0xddc7fe7cf3c70fc0

def z1046 : W := mkw 0xc3ff369cb0000001 0x30ffcda72c000000 0xe3fffe3ff0000000 0xf8ffff8ffc000000

def z1047 : W := mkw 0x006996cab0000000 0x001a65b2ac000000 0xe2e3ffcff0000000 0xf8b8fff3fc000000

def z1048 : W := mkw 0x200ab24390000000 0x0802ac90e4000000 0x4003fe03f0000000 0x1000ff80fc000000

def z1049 : W := mkw 0x63dbb763b0000001 0x18f6edd8ec000000 0xe3fffff3f0000000 0xf8fffffcfc000000

def z1050 : W := mkw 0x8bfd97febab436c0 0x22ff65ffaead0db0 0xfffffffffffc3fc0 0xffffffffffff0ff0

def z1051 : W := mkw 0x53db7e009fdbc004 0x94f6df8027f6f001 0xdbfffe003fffc00d 0xf6ffff800ffff003

def z1052 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xf7fffffffc003800 0xfdffffffff000e00

def z1053 : W := mkw 0x1400480045438938 0x450012001150e24e 0x000000000003c03f 0x000000000000f00f

def z1054 : W := mkw 0x2002a043b0000001 0x0800a810ec000000 0x4003f803f0000000 0x1000fe00fc000000

def z1055 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xcafffe000cffc000 0x72bfff80033ff000

def z1056 : W := mkw 0x0004081441050350 0x00010205104140d4 0xfd1c3e3ff31fc7ff 0xbf470f8ffcc7f1ff

def z1057 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x6503f9f3c3033f32 0x1940fe7cf0c0cfcc

def z1058 : W := mkw 0x646bb6cbb02018a9 0x191aedb2ec08062a 0x6403ffcff00038ff 0x1900fff3fc000e3f

def z1059 : W := mkw 0x57db7e000fdbc828 0x95f6df8003f6f20a 0xdbfffe000fffc03f 0xf6ffff8003fff00f

def z1060 : W := mkw 0x53db7e000f930000 0x14f6df8003e4c000 0xdbfffe000fff0000 0xf6ffff8003ffc000

def z1061 : W := mkw 0x2343a56320000000 0x08d0e958c8000000 0x6303fff3f0000000 0xd8c0fffcfc000000

def z1062 : W := mkw 0x3302e96345032d30 0x4cc0ba58d140cb4c 0x6703f9f3c0033f32 0xd9c0fe7cf000cfcc

def z1063 : W := mkw 0x10004800450b4934 0x440012001142d24d 0x000000000003c03f 0x000000000000f00f

def z1064 : W := mkw 0x53db7e000fdbe400 0x94f6df8003f6f900 0xdffffe000fffff00 0xf7ffff8003ffffc0

def z1065 : W := mkw 0x634bb76300000000 0x18d2edd8c0000000 0x6303fff3c0000000 0xd8c0fffcf0000000

def z1066 : W := mkw 0x404b360090000000 0x1012cd8024000000 0x4003fe03f0000000 0x1000ff80fc000000

def z1067 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x0000000003030732 0x0000000000c0c1cc

def z1068 : W := mkw 0x04614488246298a8 0x011851220918a62a 0x88e0060c30e3c0ff 0x223801830c38f03f

def z1069 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x9bfc01f00ffc3f00 0xe6ff007c03ff0fc0

def z1070 : W := mkw 0x544bfe42f54bc93c 0x9512ff90bd52f24f 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z1071 : W := mkw 0xe3ffb7ffba900001 0x38ffedffeea40000 0xe3fffffffce00000 0xf8ffffffff380000

def z1072 : W := mkw 0x63fbb6cbb0000001 0x18feedb2ec000000 0xe3ffffcff0000000 0xf8fffff3fc000000

def z1073 : W := mkw 0xe3ffb7ffba042641 0x38ffedffee810990 0xffffffffff1c3fc0 0xffffffffffc70ff0

def z1074 : W := mkw 0x0061448804629080 0x001851220118a420 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z1075 : W := mkw 0x53db7f204fdbe510 0x94f6dfc813f6f944 0xfffffff3cfffff32 0xfffffffcf3ffffcc

def z1076 : W := mkw 0x744bfe43654bc938 0xdd12ff90d952f24e 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z1077 : W := mkw 0x1c0048004ff7bff8 0x4700120013fdeffe 0x1c0000000fffffff 0x0700000003ffffff

def z1078 : W := mkw 0xa82481ff202436c1 0x2a09207fc8090db0 0x240001fc00003fc0 0x0900007f00000ff0

def z1079 : W := mkw 0x3002e84345030930 0x4c00ba10d140c24c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1080 : W := mkw 0xe7ffb7ffb0000829 0x39ffedffec00020a 0xe3fffffff000003f 0xf8fffffffc00000f

def z1081 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xe3fffffffffc3f00 0xf8ffffffffff0fc0

def z1082 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x37fc01f00ffc3f00 0xcdff007c03ff0fc0

def z1083 : W := mkw 0xe3dfb777b0000001 0x38f7edddec000000 0x631ffff3f0000000 0xd8c7fffcfc000000

def z1084 : W := mkw 0x004d9656b0000000 0x00136595ac000000 0xe11ffe3ff0000000 0xb847ff8ffc000000

def z1085 : W := mkw 0x180048004f273ff0 0x4600120013c9cffc 0x140000000f033ff2 0x0500000003c0cffc

def z1086 : W := mkw 0x100048004f0b6d34 0x4400120013c2db4d 0x140000000f03ff3f 0x0500000003c0ffcf

def z1087 : W := mkw 0xe3df373590000001 0x38f7cdcd64000000 0x411ffe31c0000000 0x1047ff8c70000000

def z1088 : W := mkw 0xebffb7ffbab03481 0x3affedffeeac0d20 0xf7ffffffffe03f00 0xfdfffffffff80fc0

def z1089 : W := mkw 0x43db3e0001d9c000 0x90f6cf8000767000 0xdbfffe0003ffc000 0xf6ffff8000fff000

def z1090 : W := mkw 0x10004800454fc354 0x840012001153f0d5 0x1c000000031fc7ff 0x0700000000c7f1ff

def z1091 : W := mkw 0x100048004f932d30 0x4400120013e4cb4c 0x1c0000000fff3f32 0x0700000003ffcfcc

def z1092 : W := mkw 0x882401bc002436c0 0x2209006f00090db0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z1093 : W := mkw 0x100048004f0f6f74 0x4400120013c3dbdd 0x140000000f1f3f32 0x0500000003c7cfcc

def z1094 : W := mkw 0xabb401bd9ab436c1 0x2aed006f66ad0db0 0xbffc01fdcffc3fc0 0xefff007f73ff0ff0

def z1095 : W := mkw 0x00d1440004d28000 0x003451000134a000 0xdaffc6000cffc000 0xf6bff180033ff000

def z1096 : W := mkw 0x2722a1eb202018a8 0x09c8a87ac808062a 0x6703f9fff00038ff 0xd9c0fe7ffc000e3f

def z1097 : W := mkw 0x63dbb643b0000001 0x18f6ed90ec000000 0x411ffe03f0000000 0x1047ff80fc000000

def z1098 : W := mkw 0x2343a56300000000 0x08d0e958c0000000 0xe3e3fff3c0000000 0xf8f8fffcf0000000

def z1099 : W := mkw 0x53db76000edac000 0x94f6dd8003b6b000 0xdaffc6000cffc000 0xf6bff180033ff000

def z1100 : W := mkw 0x139260000e920000 0x04e4980003a48000 0x9bffc0000ffc0000 0xe6fff00003ff0000

def z1101 : W := mkw 0x60dbb643b0d8c001 0x9836ed90ec363000 0xc8fffe03f0fcc000 0x323fff80fc3f3000

def z1102 : W := mkw 0x2306a17700000000 0x08c1a85dc0000000 0xe31ff9ffc0000000 0xf8c7fe7ff0000000

def z1103 : W := mkw 0x130049204f032d30 0x44c0124813c0cb4c 0x160001c00f033f32 0x4580007003c0cfcc

def z1104 : W := mkw 0x0824009c0ab436c0 0x0209002702ad0db0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z1105 : W := mkw 0xe3f3a5eb20000001 0x38fce97ac8000000 0x42e3f9c3c0000000 0x50b8fe70f0000000

def z1106 : W := mkw 0xebffb7ffb0940241 0x3affedffec250090 0xe3fffffff01c0000 0xf8fffffffc070000

def z1107 : W := mkw 0x100048004fdfc354 0x8400120013f7f0d5 0x180000000fffc700 0x0600000003fff1c0

def z1108 : W := mkw 0xebffb7ffb0203481 0x3affedffec080d20 0xe3fffffff0003800 0xf8fffffffc000e00

def z1109 : W := mkw 0xe3fbb7ebb0000001 0x38feedfaec000000 0x02e3f9c1c0000000 0x40b8fe7070000000

def z1110 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0xff03f9ffcf033ff2 0xffc0fe7ff3c0cffc

def z1111 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xdffffe000fffc0ff 0xf7ffff8003fff03f

def z1112 : W := mkw 0x53db76000ed28000 0x94f6dd8003b4a000 0xdbfffe000ffc0000 0xf6ffff8003ff0000

def z1113 : W := mkw 0x040c5214946298a8 0x010314852518a62a 0xfd1c3e3ffce3f8ff 0xbf470f8fff38fe3f

def z1114 : W := mkw 0x230eb3779a042640 0x08c3acdde6810990 0xff1fffffff1c3fc0 0xffc7ffffffc70ff0

def z1115 : W := mkw 0x43db760004dac000 0x90f6dd800136b000 0xdbfffe000cffc000 0xf6ffff80033ff000

def z1116 : W := mkw 0xe7ffb7ffb02018a9 0x39ffedffec08062a 0xe3fffffff0003800 0xf8fffffffc000e00

def z1117 : W := mkw 0xc8fd169c90fcd2c4 0xb23f45a7243f34b1 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z1118 : W := mkw 0x73db7e014fdbc110 0xdcf6df8053f6f044 0xdbfffe01cfffc000 0xf6ffff8073fff000

def z1119 : W := mkw 0x604bb643b0000001 0x1812ed90ec000000 0x4003fe03f003c03f 0x1000ff80fc00f00f

def z1120 : W := mkw 0x032401bc0a2436c0 0x00c9006f02890db0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z1121 : W := mkw 0xe7ffb7ffb0609089 0x39ffedffec182422 0xfffffffff0e3c0ff 0xfffffffffc38f03f

def z1122 : W := mkw 0x000c925690000000 0x00032495a4000000 0xe31ffffff0000000 0xf8c7fffffc000000

def z1123 : W := mkw 0x53d364000ed28000 0x94f4d90003b4a000 0x03ffc0000ffc0000 0x40fff00003ff0000

def z1124 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xf7fffffff3000700 0xfdfffffffcc001c0

def z1125 : W := mkw 0x7392e9634f932d30 0xdce4ba58d3e4cb4c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1126 : W := mkw 0x1420c8ca6f233db8 0x450832329bc8cf6e 0x340001ce3f033fff 0x0d0000738fc0cfff

def z1127 : W := mkw 0x03b4009c0ab412c0 0x00ed002702ad04b0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z1128 : W := mkw 0x2306a17790000000 0x08c1a85de4000000 0x6303f9fff0000000 0xd8c0fe7ffc000000

def z1129 : W := mkw 0xe3ffb7ffb0040241 0x38ffedffec010090 0xe7fffffff00007c0 0xf9fffffffc0001f0

def z1130 : W := mkw 0xebffb7ffba2436c1 0x3affedffee890db0 0xf7ffffffff003fc0 0xfdffffffffc00ff0

def z1131 : W := mkw 0x130449344f0f6f74 0x44c1124d13c3dbdd 0xbf1c01fc0f1fffff 0xefc7007f03c7ffff

def z1132 : W := mkw 0xe3beb3ffb0000001 0x38efacffec000000 0x631ff9fff0000000 0xd8c7fe7ffc000000

def z1133 : W := mkw 0xefffb7ffbaf4b6c9 0x3bffedffeebd2db2 0xfffffffffffcffcd 0xffffffffffff3ff3

def z1134 : W := mkw 0x83b401bc0a902400 0x20ed006f02a40900 0xbffc01fc0ffc3f00 0xefff007f03ff0fc0

def z1135 : W := mkw 0xabbeb3ff9ab436c0 0x2aefacffe6ad0db0 0xfffffffffffc3fc0 0xffffffffffff0ff0

def z1136 : W := mkw 0xe3ffb7ffb02412c1 0x38ffedffec0904b0 0xfffffffffffc3fc0 0xffffffffffff0ff0

def z1137 : W := mkw 0xe0fbb6cbb0000001 0x383eedb2ec000000 0x40e3fe03f0000000 0x1038ff80fc000000

def z1138 : W := mkw 0x63dfb657b0000001 0x18f7ed95ec000000 0xe3fffe3ff0000000 0xf8ffff8ffc000000

def z1139 : W := mkw 0x100048004f43ad30 0x4400120013d0eb4c 0x1c0000000fe3ff32 0x0700000003f8ffcc

def z1140 : W := mkw 0x63dbb643b0000001 0x18f6ed90ec000000 0x42e3fe03f0000000 0x50b8ff80fc000000

def z1141 : W := mkw 0x230ab36300000000 0x08c2acd8c0000000 0xe31ffff3c0000000 0xf8c7fffcf0000000

def z1142 : W := mkw 0x0c0048004ffffffc 0x0300120013ffffff 0x1c0000000fffffff 0x0700000003ffffff

def z1143 : W := mkw 0xe39eb37790000001 0x38e7acdde4000000 0xe31ffffff0000000 0xf8c7fffffc000000

def z1144 : W := mkw 0xe3ff37bdb0000001 0x38ffcdef6c000000 0xc3fffe3df0000000 0xf0ffff8f7c000000

def z1145 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xc3fffff1c0000000 0xf0fffffc70000000

def z1146 : W := mkw 0x43df361490dcc244 0x90f7cd8524373091 0xebfffe3ff0fcc0cd 0xfaffff8ffc3f3033

def z1147 : W := mkw 0x0445c45624468a68 0x011171158911a29a 0xfd1fc63e331fc7ff 0xbf47f18f8cc7f1ff

def z1148 : W := mkw 0xeb9e3b35db9d6755 0x3ae78ecd76e759d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z1149 : W := mkw 0xc8fd169cb0bc52c5 0x323f45a72c2f14b1 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z1150 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xbffc01fe3ffc3fff 0xefff007f8fff0fff

def z1151 : W := mkw 0x9b9449344f972f70 0x66e5124d13e5cbdc 0x151c00300f1f3f32 0x0547000c03c7cfcc

def z1152 : W := mkw 0x230ebb77db0d6754 0x08c3aeddf6c359d5 0xff1fffffff1fffff 0xffc7ffffffc7ffff

def z1153 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xfffffe0c0fffc0c0 0xffffff8303fff030

def z1154 : W := mkw 0xa026a1ffb0000001 0x2809a87fec000000 0x6003f9fff0000000 0x1800fe7ffc000000

def z1155 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x740000020f033f32 0x9d00000083c0cfcc

def z1156 : W := mkw 0xe3ffb7ffba900001 0x38ffedffeea40000 0xe3fffffff31c0000 0xf8fffffffcc70000

def z1157 : W := mkw 0x100048004fdbc930 0xc400120013f6f24c 0x180000000fffc032 0x0600000003fff00c

def z1158 : W := mkw 0x50d95e0005dbc000 0x943657800176f000 0x88fc060000ffc000 0x223f0180003ff000

def z1159 : W := mkw 0x3702e9634f43ad38 0x4dc0ba58d3d0eb4e 0x7703f9f3cf03ff3f 0xddc0fe7cf3c0ffcf

def z1160 : W := mkw 0x100048004f072f74 0x4400120013c1cbdd 0x140000000f033fff 0x0500000003c0cfff

def z1161 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xebfffffff000c0cd 0xfafffffffc003033

def z1162 : W := mkw 0xbb9e3b35db9d6754 0x6ee78ecd76e759d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z1163 : W := mkw 0x236fb7ffb0000000 0x08dbedffec000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1164 : W := mkw 0x0302200000000000 0x00c0880000000000 0x6303f833c0000000 0xd8c0fe0cf0000000

def z1165 : W := mkw 0xe39eb37790000001 0x38e7acdde4000000 0x031ff9f1c0000000 0x40c7fe7c70000000

def z1166 : W := mkw 0x2302a9634b012510 0x08c0aa58d2c04944 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1167 : W := mkw 0x3302e9634f0b6d34 0x4cc0ba58d3c2db4d 0x7703f9f3cf03ff3f 0xddc0fe7cf3c0ffcf

def z1168 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0xff03fff3cf03ff32 0xffc0fffcf3c0ffcc

def z1169 : W := mkw 0x180048004fbf7ff4 0x4600120013efdffd 0x1c0000000fffffff 0x0700000003ffffff

def z1170 : W := mkw 0x53d36c000fdbc000 0x94f4db0003f6f000 0x9bffc0000fffc000 0xe6fff00003fff000

def z1171 : W := mkw 0x2302a1630a000000 0x08c0a858c2800000 0x7303f9f3cf000000 0xdcc0fe7cf3c00000

def z1172 : W := mkw 0xebff37bd9ab436c1 0x3affcdef66ad0db0 0xfffffffdcffc3fc0 0xffffffff73ff0ff0

def z1173 : W := mkw 0x63dbb7630a902400 0x18f6edd8c2a40900 0xfffffff3cffc3f00 0xfffffffcf3ff0fc0

def z1174 : W := mkw 0xa326a1ff00000000 0x28c9a87fc0000000 0x6303f9ffc0000000 0xd8c0fe7ff0000000

def z1175 : W := mkw 0x330269214f032d30 0x4cc09a4853c0cb4c 0x140000000f033f32 0x0500000003c0cfcc

def z1176 : W := mkw 0x604bb643b0084005 0x1812ed90ec021001 0x4003fe03f000c00d 0x1000ff80fc003003

def z1177 : W := mkw 0x140048004f63bdb8 0x4500120013d8ef6e 0x140000000fe33f32 0x0500000003f8cfcc

def z1178 : W := mkw 0x0020c0ca042218a0 0x0008303281088628 0xfee3c7ce3ce3f8ff 0xffb8f1f38f38fe3f

def z1179 : W := mkw 0xe3dfb777b0000001 0x38f7edddec000000 0xe11ffe3ff0000000 0xb847ff8ffc000000

def z1180 : W := mkw 0xe3fbb7ebb0000001 0x38feedfaec000000 0xe2e3ffcff0000000 0xf8b8fff3fc000000

def z1181 : W := mkw 0x40d9560004dac000 0x903655800136b000 0x8affc6000cfcc000 0x62bff180033f3000

def z1182 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xe7fffffffce03fc0 0xf9ffffffff380ff0

def z1183 : W := mkw 0xa367a5ffb0000001 0x28d9e97fec000000 0xe3e3fffff0000000 0xf8f8fffffc000000

def z1184 : W := mkw 0xebfbb7ebbab03481 0x3afeedfaeeac0d20 0x42e3ffc3fce03800 0x50b8fff0ff380e00

def z1185 : W := mkw 0x3302e9634f9b6d30 0xccc0ba58d3e6db4c 0x7703f9f3cf1f3f32 0xddc0fe7cf3c7cfcc

def z1186 : W := mkw 0xe7ffb7ffb0201089 0x39ffedffec080422 0xe3fffffff00000cd 0xf8fffffffc000033

def z1187 : W := mkw 0xe3ffb7ffbad8c001 0xb8ffedffeeb63000 0xfbfffffffffcc000 0xfeffffffffff3000

def z1188 : W := mkw 0x03d95e000fdbc000 0x00f6578003f6f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1189 : W := mkw 0xebf7a5ff2ab436c1 0x3afde97fcaad0db0 0xfffff9ffcffc3fc0 0xfffffe7ff3ff0ff0

def z1190 : W := mkw 0x140048004ffbfdb8 0xc500120013feff6e 0x1c0000000fffffff 0x0700000003ffffff

def z1191 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xa3fc01fc0ffc3f00 0xe8ff007f03ff0fc0

def z1192 : W := mkw 0x04610c8861619198 0x0118432218586466 0xfde03e3ff3e3c7ff 0xbf780f8ffcf8f1ff

def z1193 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xc9fffe0003ffc000 0x327fff8000fff000

def z1194 : W := mkw 0x2002a04300000000 0x0800a810c0000000 0x6203f9c3c0000000 0xd880fe70f0000000

def z1195 : W := mkw 0x0300c9624f032d30 0x00c0325893c0cb4c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1196 : W := mkw 0xe7ffb7ffb06cd2cd 0x39ffedffec1b34b3 0xebfffffff0fcc0cd 0xfafffffffc3f3033

def z1197 : W := mkw 0x604b360190000001 0x1812cd8064000000 0x4003fe01c0000000 0x1000ff8070000000

def z1198 : W := mkw 0xebffb7ffb0bc52c5 0x3affedffec2f14b1 0xebfffffff0fcc0cd 0xfafffffffc3f3033

def z1199 : W := mkw 0x53db7e004fdbe510 0xd4f6df8013f6f944 0xdbfffe000fffc700 0xf6ffff8003fff1c0

def z1200 : W := mkw 0x039401340a942640 0x00e5004d02a50990 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z1201 : W := mkw 0x04289aca212958a8 0x010a26b2884a562a 0xfd1c3fce331ff8ff 0xbf470ff38cc7fe3f

def z1202 : W := mkw 0xe3dfb777b0000001 0x38f7edddec000000 0x011ff831c0000000 0x0047fe0c70000000

def z1203 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x6603f9f3cc033f32 0x5980fe7cf300cfcc

def z1204 : W := mkw 0x3302e1634e022d30 0x4cc0b858d3808b4c 0x6703f9f3cc003f32 0xd9c0fe7cf3000fcc

def z1205 : W := mkw 0xab26a1ff002436c0 0x2ac9a87fc0090db0 0x6703f9ffc0003fc0 0xd9c0fe7ff0000ff0

def z1206 : W := mkw 0x83fd97feb0000000 0x20ff65ffac000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1207 : W := mkw 0xab96a1770a942640 0x2ae5a85dc2a50990 0x631ff9f3c31c0700 0xd8c7fe7cf0c701c0

def z1208 : W := mkw 0xd86f7fbc056ff6c0 0xb61bdfef015bfdb0 0x6403fffc0003ffc0 0x1900ffff0000fff0

def z1209 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xffe3fffffce3f8ff 0xfff8ffffff38fe3f

def z1210 : W := mkw 0xebffb7ffbafcf6c1 0xbaffedffeebf3db0 0xfffffffffffcffc0 0xffffffffffff3ff0

def z1211 : W := mkw 0xa3f7a5ff20000000 0x28fde97fc8000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1212 : W := mkw 0x100448144f072f70 0x4401120513c1cbdc 0xbd1c003c0f1f3ff2 0xaf47000f03c7cffc

def z1213 : W := mkw 0x53db7e00dfdbc114 0x94f6df8037f6f045 0xfffffe33ffffc73f 0xffffff8cfffff1cf

def z1214 : W := mkw 0x3302a1630a002400 0x4cc0a858c2800900 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z1215 : W := mkw 0x2363a5eb20000000 0x08d8e97ac8000000 0x63e3f9f3c0000000 0xd8f8fe7cf0000000

def z1216 : W := mkw 0x04004800456399b8 0x010012001158e66e 0x1c0000000fe3ffff 0x0700000003f8ffff

def z1217 : W := mkw 0x3302a9634b012d30 0x4cc0aa58d2c04b4c 0x6703f9f3c3003f32 0xd9c0fe7cf0c00fcc

def z1218 : W := mkw 0xebffb7ffba942641 0x3affedffeea50990 0xfffffffff31c07c0 0xfffffffffcc701f0

def z1219 : W := mkw 0x2302212100000000 0x08c0884840000000 0x4303f831c0000000 0xd0c0fe0c70000000

def z1220 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0x9affc6000fffc000 0x66bff18003fff000

def z1221 : W := mkw 0x604fb657b0040241 0x1813ed95ec010090 0xfd1ffe3ff31c07c0 0xbf47ff8ffcc701f0

def z1222 : W := mkw 0x53db3e000b994000 0x94f6cf8002e65000 0xdbfffe000ffc0000 0xf6ffff8003ff0000

def z1223 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x7703f9ffff033fff 0xddc0fe7fffc0cfff

def z1224 : W := mkw 0x504b7e00054bc000 0x9412df800152f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1225 : W := mkw 0xa42481fff0241bfd 0x2909207ffc0906ff 0x240001fff0003fff 0x0900007ffc000fff

def z1226 : W := mkw 0x3392e9634f932d30 0x4ce4ba58d3e4cb4c 0x77e3f9f3cfe33f32 0xddf8fe7cf3f8cfcc

def z1227 : W := mkw 0x139049204fdbed30 0xc4e4124813f6fb4c 0xbffc01f00fffff32 0xefff007c03ffffcc

def z1228 : W := mkw 0x10004800454bc114 0x840012001152f045 0x000000000003c03f 0x000000000000f00f

def z1229 : W := mkw 0x43d324000a900000 0x10f4c90002a40000 0x9bffc0000ffc0000 0xe6fff00003ff0000

def z1230 : W := mkw 0x704bfe43f54bc931 0xdc12ff90fd52f24c 0x4003fe03f003c032 0x1000ff80fc00f00c

def z1231 : W := mkw 0xe3ffb7ffb0040241 0x38ffedffec010090 0xfffffffff31fc7ff 0xfffffffffcc7f1ff

def z1232 : W := mkw 0x604fb657b00c4245 0x1813ed95ec031091 0xc81ffe0ff01cc0cd 0x3207ff83fc073033

def z1233 : W := mkw 0x9fb449bc4ff7bff8 0x67ed126f13fdeffe 0xbffc01fc0fffffff 0xefff007f03ffffff

def z1234 : W := mkw 0x43db7e00054bc000 0x10f6df800152f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1235 : W := mkw 0x634fb777b0000001 0x18d3edddec000000 0xe31ffffff0000000 0xf8c7fffffc000000

def z1236 : W := mkw 0x634bb763b0000001 0x18d2edd8ec000000 0x4203ffc3f0000000 0x5080fff0fc000000

def z1237 : W := mkw 0x180048004ffff7d4 0x8600120013fffdf5 0x1c0000000fffffff 0x0700000003ffffff

def z1238 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0xff1ff9f3cf1f3f32 0xffc7fe7cf3c7cfcc

def z1239 : W := mkw 0x030e321490000000 0x00c38c8524000000 0xe31ffe3ff0000000 0xf8c7ff8ffc000000

def z1240 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0xfffc07fc0fffffc0 0xffff01ff03fffff0

def z1241 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x1ffc01f00ffc3fc0 0x47ff007c03ff0ff0

def z1242 : W := mkw 0xe8ffb6dfb0b412c1 0x3a3fedb7ec2d04b0 0xc8fffe0ff0fc00c0 0x323fff83fc3f0030

def z1243 : W := mkw 0xe39eb37790000001 0x38e7acdde4000000 0x411ff833c0000000 0x1047fe0cf0000000

def z1244 : W := mkw 0x73db7e019fdbc001 0x9cf6df8067f6f000 0xdbfffe01cfffc000 0xf6ffff8073fff000

def z1245 : W := mkw 0x53db7e004fdbed30 0xd4f6df8013f6fb4c 0xfffffe33cfffff32 0xffffff8cf3ffffcc

def z1246 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xf7fffffff0030032 0xfdfffffffc00c00c

def z1247 : W := mkw 0x8bb401bc9ab436c4 0x22ed006f26ad0db1 0xbffc01fc3ffc3fcd 0xefff007f0fff0ff3

def z1248 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0xfffc3e3fffffc7ff 0xffff0f8ffffff1ff

def z1249 : W := mkw 0x2302a04300000000 0x08c0a810c0000000 0x4303f803c0000000 0xd0c0fe00f0000000

def z1250 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x000000000f003f00 0x0000000003c00fc0

def z1251 : W := mkw 0x43df361490000000 0x10f7cd8524000000 0xc3fffe31c0000000 0xf0ffff8c70000000

def z1252 : W := mkw 0xe3ffb7ffba002401 0x38ffedffee800900 0xe3fffffffc003800 0xf8ffffffff000e00

def z1253 : W := mkw 0x230ab36390000000 0x08c2acd8e4000000 0x6303fff3f0000000 0xd8c0fffcfc000000

def z1254 : W := mkw 0x100048004fd3ad30 0xc400120013f4eb4c 0x140000000fe33f32 0x0500000003f8cfcc

def z1255 : W := mkw 0x882481fe00243ee0 0x2209207f80090fb8 0x240001fe00003ff2 0x0900007f80000ffc

def z1256 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xe7fffffff31c3fc0 0xf9fffffffcc70ff0

def z1257 : W := mkw 0xe7ffb7ffb0f8d089 0xb9ffedffec3e3422 0xebfffffff0fcc0cd 0xfafffffffc3f3033

def z1258 : W := mkw 0xc8fd169cb0fcd2c1 0xb23f45a72c3f34b0 0x88fc060c30fcc0c0 0x223f01830c3f3030

def z1259 : W := mkw 0x43db360090000000 0x10f6cd8024000000 0xc3fffe03f0000000 0xf0ffff80fc000000

def z1260 : W := mkw 0xf3db7f210fdbc001 0xbcf6dfc843f6f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1261 : W := mkw 0x2302a163b0000001 0x08c0a858ec000000 0x6303f9f3f0000000 0xd8c0fe7cfc000000

def z1262 : W := mkw 0x53db7e000fdbc000 0x94f6df8003f6f000 0xdbfffe0c3fffc0cd 0xf6ffff830ffff033

def z1263 : W := mkw 0x63fbb7eb20000000 0x18feedfac8000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1264 : W := mkw 0xa06d97ffb0000001 0x281b65ffec000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1265 : W := mkw 0x1000480045030930 0x440012001140c24c 0x140000000c033832 0x050000000300ce0c

def z1266 : W := mkw 0x40d95e0005dbc000 0x903657800176f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1267 : W := mkw 0xe7ffb7ffb0408009 0x39ffedffec102002 0xe3fffffff000c00d 0xf8fffffffc003003

def z1268 : W := mkw 0x9b2669bc0f2736c0 0x26c99a6f03c9cdb0 0x7703f9fc0f033fc0 0xddc0fe7f03c0cff0

def z1269 : W := mkw 0x636bb7ebb0000001 0x18daedfaec000000 0xe3e3fffff0000000 0xf8f8fffffc000000

def z1270 : W := mkw 0x539a7a000f9b4000 0x94e69e8003e6d000 0xdbfff8000fff0000 0xf6fffe0003ffc000

def z1271 : W := mkw 0xebffb7ffba942641 0x3affedffeea50990 0xf7ffffffff1c3f00 0xfdffffffffc70fc0

def z1272 : W := mkw 0xa3beb3ff90000000 0x28efacffe4000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1273 : W := mkw 0xe36fb7ffb0000001 0x38dbedffec000000 0x6303fffff0000000 0xd8c0fffffc000000

def z1274 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x7703fff3ff03ff3f 0xddc0fffcffc0ffcf

def z1275 : W := mkw 0xdbb621bc0ab436c0 0xb6ed886f02ad0db0 0xbffc01fc0ffc3fc0 0xefff007f03ff0ff0

def z1276 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0x5303f9f1cf033f00 0xd4c0fe7c73c0cfc0

def z1277 : W := mkw 0xebffb7ffbab436c1 0x3affedffeead0db0 0xbffff9fdcffc3fc0 0xeffffe7f73ff0ff0

def z1278 : W := mkw 0xe3ffb7ffb0002401 0x38ffedffec000900 0xe7fffffff0003f00 0xf9fffffffc000fc0

def z1279 : W := mkw 0x2000816300002400 0x08002058c0000900 0x240001f3c0003f00 0x0900007cf0000fc0

def z1280 : W := mkw 0xebffb7ffb0042641 0x3affedffec010990 0xe3fffffff0000700 0xf8fffffffc0001c0

def z1281 : W := mkw 0x00004800450f4b74 0x000012001143d2dd 0x1c0000000f1fffff 0x0700000003c7ffff

def z1282 : W := mkw 0xe3ffb6dfb0000001 0x38ffedb7ec000000 0xc3fffe0ff0000000 0xf0ffff83fc000000

def z1283 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x4203f9c3c0000000 0x5080fe70f0000000

def z1284 : W := mkw 0x604bb643b048c001 0x9812ed90ec123000 0x4003fe03f000c000 0x1000ff80fc003000

def z1285 : W := mkw 0xe0dfb657b0000001 0x3837ed95ec000000 0x401ffe03f0000000 0x1007ff80fc000000

def z1286 : W := mkw 0xdbdb7f200fdbe400 0xb6f6dfc803f6f900 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1287 : W := mkw 0x140048004fffdbfc 0x8500120013fff6ff 0x1c0000000fffffff 0x0700000003ffffff

def z1288 : W := mkw 0xe3ffb7ffb0d08001 0xb8ffedffec342000 0xe3fffffff0e00000 0xf8fffffffc380000

def z1289 : W := mkw 0xe7ffb7ffb02018a9 0x39ffedffec08062a 0xfffffffffce038ff 0xffffffffff380e3f

def z1290 : W := mkw 0x030220000a000000 0x00c0880002800000 0x5303f8000f000000 0xd4c0fe0003c00000

def z1291 : W := mkw 0x63dbb76300d8c000 0x98f6edd8c0363000 0xebfffff3c0fcc000 0xfafffffcf03f3000

def z1292 : W := mkw 0x634bb763b0000001 0x18d2edd8ec000000 0x4103fe33f0000000 0x1040ff8cfc000000

def z1293 : W := mkw 0x6343a56320000001 0x18d0e958c8000000 0x6303f9f3c0000000 0xd8c0fe7cf0000000

def z1294 : W := mkw 0xa82481ffd0243ff4 0x6a09207ff4090ffd 0x240001fff0003fff 0x0900007ffc000fff

def z1295 : W := mkw 0x9bb449bc4ffffff0 0xe6ed126f13fffffc 0xbffc01fc0ffffff2 0xefff007f03fffffc

def z1296 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x611ffffff0000000 0x1847fffffc000000

def z1297 : W := mkw 0xe3ff37bd90000001 0x38ffcdef64000000 0xe3fffffdc0000000 0xf8ffffff70000000

def z1298 : W := mkw 0x44fd169cb0fcd2cc 0x913f45a72c3f34b3 0x88fc060c30fcc0cd 0x223f01830c3f3033

def z1299 : W := mkw 0x2302a1630a002400 0x08c0a858c2800900 0x6303f9f3cc003800 0xd8c0fe7cf3000e00

def z1300 : W := mkw 0xe3ffb7ffb00c4245 0x38ffedffec031091 0xfffffffff31cc7cd 0xfffffffffcc731f3

def z1301 : W := mkw 0x230221210a002400 0x08c0884842800900 0x01003831c3000700 0x00400e0c70c001c0

def z1302 : W := mkw 0xe06fb7ffb0000001 0x381bedffec000000 0xe11ffffff0000000 0xb847fffffc000000

def z1303 : W := mkw 0xab26a1ffba2436c1 0x2ac9a87fee890db0 0x7703f9ffff003fc0 0xddc0fe7fffc00ff0

def z1304 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xcae3c7ce3ce3f8ff 0x72b8f1f38f38fe3f

def z1305 : W := mkw 0xe7ffb7ffb02018a9 0x39ffedffec08062a 0xfffffffff003f8ff 0xfffffffffc00fe3f

def z1306 : W := mkw 0x2302e16344022d30 0x48c0b858d1008b4c 0x7703f9f3cc033f32 0xddc0fe7cf300cfcc

def z1307 : W := mkw 0xebffb7ffb0b412c1 0x3affedffec2d04b0 0xfffffffffcfc38c0 0xffffffffff3f0e30

def z1308 : W := mkw 0x100048004f030110 0x0400120013c0c044 0x140000000f030732 0x0500000003c0c1cc

def z1309 : W := mkw 0xc0fd96deb0000001 0x303f65b7ac000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1310 : W := mkw 0x63dbb643ba900001 0x18f6ed90eea40000 0xdbfffe03fffc0000 0xf6ffff80ffff0000

def z1311 : W := mkw 0x100048004f4bed30 0xc400120013d2fb4c 0x140000000f03ff32 0x0500000003c0ffcc

def z1312 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0xfc00060e3f03ffff 0xbf0001838fc0ffff

def z1313 : W := mkw 0x139448144fdfc354 0x84e5120513f7f0d5 0xbffc003c0fffc7ff 0xefff000f03fff1ff

def z1314 : W := mkw 0x139048004f932d30 0x44e4120013e4cb4c 0x9ffc00000fff3f32 0xe7ff000003ffcfcc

def z1315 : W := mkw 0xe3ffb7ffb00c4245 0x38ffedffec031091 0xe3fffffff01c0000 0xf8fffffffc070000

def z1316 : W := mkw 0xe3ffb7ffba002401 0x38ffedffee800900 0xe3fffffff3000700 0xf8fffffffcc001c0

def z1317 : W := mkw 0x100048004f0b6d30 0x4400120013c2db4c 0x1c0000000f1fff32 0x0700000003c7ffcc

def z1318 : W := mkw 0x600ab24390000001 0x1802ac90e4000000 0x4003f803c0000000 0x1000fe00f0000000

def z1319 : W := mkw 0x100048004f032510 0x4400120013c0c944 0x100000000f030700 0x0400000003c0c1c0

def z1320 : W := mkw 0x982449bc4f273ff0 0x6609126f13c9cffc 0x340001fc0f033ff2 0x0d00007f03c0cffc

def z1321 : W := mkw 0xcbff37bc9ab436c0 0x32ffcdef26ad0db0 0xfffffffffffc3fc0 0xffffffffffff0ff0

def z1322 : W := mkw 0xebbeb3ff9ab436c1 0x3aefacffe6ad0db0 0xfffff9ffcffc3fc0 0xfffffe7ff3ff0ff0

def z1323 : W := mkw 0x2302a16300000820 0x08c0a858c0000208 0x6703f9f3c0003832 0xd9c0fe7cf0000e0c

def z1324 : W := mkw 0x046d5e9cf56fdbfc 0x011b57a73d5bf6ff 0x9cfc060c3fffffff 0x273f01830fffffff

def z1325 : W := mkw 0x2302a96341012d30 0x48c0aa58d0404b4c 0x7703f9f3c3033f32 0xddc0fe7cf0c0cfcc

def z1326 : W := mkw 0x739e3b35db9d6754 0xdce78ecd76e759d5 0x011c3831c31c0700 0x00470e0c70c701c0

def z1327 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0x66e3c7ce3ce3f8ff 0x59b8f1f38f38fe3f

def z1328 : W := mkw 0x8b9401340a942640 0x22e5004d02a50990 0xbffc01f00ffc3f00 0xefff007c03ff0fc0

def z1329 : W := mkw 0xe3ffb7ffb048c001 0xb8ffedffec123000 0xe3fffffff000c000 0xf8fffffffc003000

def z1330 : W := mkw 0x53d364000ed28000 0x94f4d90003b4a000 0x8affc0000cfc0000 0x62bff000033f0000

def z1331 : W := mkw 0x3302e9634f032d30 0x4cc0ba58d3c0cb4c 0xf703ffffff033f32 0xfdc0ffffffc0cfcc

def z1332 : W := mkw 0x8fb449bc4ffffffc 0x23ed126f13ffffff 0xbffc01fc0fffffff 0xefff007f03ffffff

def z1333 : W := mkw 0xe3dfb777b0000001 0x38f7edddec000000 0xc3fffe33f0000000 0xf0ffff8cfc000000

def z1334 : W := mkw 0x2302a16300002c20 0x48c0a858c0000b08 0x6303f9f3c0003800 0xd8c0fe7cf0000e00

def z1335 : W := mkw 0x3302e9634f43ad30 0x4cc0ba58d3d0eb4c 0x7f03f9f3cfe3ff32 0xdfc0fe7cf3f8ffcc

def z1336 : W := mkw 0x8bb001a80ab03480 0x22ec006a02ac0d20 0xbffc01f00ffc3f00 0xefff007c03ff0fc0

def z1337 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x8bfc01fc0ffc3fc0 0x62ff007f03ff0ff0

def z1338 : W := mkw 0xebffb7ffbabc76c5 0x3affedffeeaf1db1 0xfffffffffffcffcd 0xffffffffffff3ff3

def z1339 : W := mkw 0x1000480045030930 0x440012001140c24c 0x1400000003030732 0x0500000000c0c1cc

def z1340 : W := mkw 0x73db7f210fdbe400 0xdcf6dfc843f6f900 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1341 : W := mkw 0xa82481ff00243ee0 0x6a09207fc0090fb8 0x240001fc00003fc0 0x0900007f00000ff0

def z1342 : W := mkw 0x9bb449bc4ffff7d4 0xa6ed126f13fffdf5 0xbffc01fc0fffffff 0xefff007f03ffffff

def z1343 : W := mkw 0x0000000000000000 0x0000000000000000 0x75003833c3000700 0x9d400e0cf0c001c0

def z1344 : W := mkw 0x1000c8424f032d30 0x4400321093c0cb4c 0x340001c20f033f32 0x0d00007083c0cfcc

def z1345 : W := mkw 0xe3ffb7ffbab01081 0x38ffedffeeac0420 0xfffffffffffc38c0 0xffffffffffff0e30

def z1346 : W := mkw 0x0461c4ca246298a8 0x011871328918a62a 0xffffc7ce3ffff8ff 0xfffff1f38ffffe3f

def z1347 : W := mkw 0x0000804200000000 0x0000201080000000 0x7603c1c20c003800 0xdd80f07083000e00

def z1348 : W := mkw 0x9bb449bc4fbf7ff4 0x66ed126f13efdffd 0xbffc01fc0fffffff 0xefff007f03ffffff

def z1349 : W := mkw 0x53db76000edac000 0x94f6dd8003b6b000 0x02ffc0000cfc0000 0x40bff000033f0000

def z1350 : W := mkw 0xe7ffb7ffb06098a9 0x39ffedffec18262a 0xeffffffff0e0f8ff 0xfbfffffffc383e3f

def z1351 : W := mkw 0xebffb7ffbab412c1 0x3affedffeead04b0 0xfbfffffffffc00c0 0xfeffffffffff0030

def z1352 : W := mkw 0x73dbff630fdbe400 0x9cf6ffd8c3f6f900 0xfffffff3cfffff00 0xfffffffcf3ffffc0

def z1353 : W := mkw 0x8bb401bc0ab436c0 0x22ed006f02ad0db0 0x27fc01fc0ffc3fc0 0x49ff007f03ff0ff0

def z1354 : W := mkw 0xa32eb3ffb0000001 0x28cbacffec000000 0xe31ffffff0000000 0xf8c7fffffc000000

def z1355 : W := mkw 0xe3ffb7ffb0201081 0x38ffedffec080420 0xebfffffff0e000c0 0xfafffffffc380030

def z1356 : W := mkw 0x046d96deb06cd2cc 0x011b65b7ac1b34b3 0xebfffffff0fcc0cd 0xfafffffffc3f3033

def z1357 : W := mkw 0x100048004f032d30 0x4400120013c0cb4c 0x350000300f033f32 0x8d40000c03c0cfcc

def z1358 : W := mkw 0x2763e5eb2e62bca8 0x09d8f97acb98af2a 0xffe3ffffffe3ffff 0xfff8fffffff8ffff

def z1359 : W := mkw 0x100c5a14df0f6f74 0x4403168537c3dbdd 0x9c1c060c3f1fffff 0x270701830fc7ffff

def z1360 : W := mkw 0x634bb643b0000001 0x18d2ed90ec000000 0x4303fe03f0000000 0xd0c0ff80fc000000

def z1361 : W := mkw 0x134b7e000f4bc000 0x04d2df8003d2f000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1362 : W := mkw 0xebf3a5eb2ab03481 0x3afce97acaac0d20 0x77e3f9f3cfe03f00 0xddf8fe7cf3f80fc0

def z1363 : W := mkw 0x604bb763b0000001 0x1812edd8ec000000 0x6003fff3f0000000 0x1800fffcfc000000

def z1364 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x43fffff3f0000000 0x50fffffcfc000000

def z1365 : W := mkw 0x042480deb0241aec 0x01092037ac0906bb 0x240001ce300038ff 0x090000738c000e3f

def z1366 : W := mkw 0xebffb7ffb0b412c1 0x3affedffec2d04b0 0xfffffffff3fc07c0 0xfffffffffcff01f0

def z1367 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x83fffffdf0000000 0x60ffffff7c000000

def z1368 : W := mkw 0x606fb6dfb0000001 0x181bedb7ec000000 0xe3fffffff0000000 0xf8fffffffc000000

def z1369 : W := mkw 0x140048004f6ffffc 0x4500120013dbffff 0x1c0000000fffffff 0x0700000003ffffff

def z1370 : W := mkw 0x03d104000a900000 0x00f4410002a40000 0xdbffc6000ffc0000 0xf6fff18003ff0000

def z1371 : W := mkw 0x1000c8424f032d30 0x4400321093c0cb4c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1372 : W := mkw 0x130049204f032d30 0x44c0124813c0cb4c 0x150000300f033f32 0x0540000c03c0cfcc

def z1373 : W := mkw 0x606bb6cbb0000001 0x181aedb2ec000000 0x42e3ffc3f0000000 0x50b8fff0fc000000

def z1374 : W := mkw 0xf392e9634f032d31 0x7ce4ba58d3c0cb4c 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1375 : W := mkw 0xe3ffb7ffb0984001 0xb8ffedffec261000 0xe3fffffff01c0000 0xf8fffffffc070000

def z1376 : W := mkw 0x60dbb643b0000001 0x1836ed90ec000000 0xc0fffe03f0000000 0x303fff80fc000000

def z1377 : W := mkw 0xe3ffb7ffb0040245 0x38ffedffec010091 0xe3fffffff00000cd 0xf8fffffffc000033

def z1378 : W := mkw 0x00618cca610d4354 0x00186332984350d5 0xfee3c7ce331fc7ff 0xffb8f1f38cc7f1ff

def z1379 : W := mkw 0x2302a1630a002400 0x08c0a858c2800900 0x6303f9f3c3000700 0xd8c0fe7cf0c001c0

def z1380 : W := mkw 0xebffb7ffba902401 0x3affedffeea40900 0xe3fffffff0000000 0xf8fffffffc000000

def z1381 : W := mkw 0x53db7e004fdbc110 0x94f6df8013f6f044 0xdbfffe03cfffc032 0xf6ffff80f3fff00c

def z1382 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0x63fff9f3c0000000 0xd8fffe7cf0000000

def z1383 : W := mkw 0xe3f7a5ff20000001 0x38fde97fc8000000 0xe3fff9ffc0000000 0xf8fffe7ff0000000

def z1384 : W := mkw 0x606bb6cbb0000001 0x181aedb2ec000000 0x6003ffcff0000000 0x1800fff3fc000000

def z1385 : W := mkw 0xe3ffb7ffb0000001 0x38ffedffec000000 0xfbfffffff003c000 0xfefffffffc00f000

def z1386 : W := mkw 0x130269204f032510 0x04c09a4813c0c944 0x7703f9f3cf033f32 0xddc0fe7cf3c0cfcc

def z1387 : W := mkw 0x039040000e920000 0x00e4100003a48000 0xdbffc0000fff0000 0xf6fff00003ffc000

def z1388 : W := mkw 0x2302a16300000000 0x08c0a858c0000000 0x7703f9f3c0030032 0xddc0fe7cf000c00c

def z1389 : W := mkw 0x13d36c000fd38000 0x04f4db0003f4e000 0xdbfffe000fffc000 0xf6ffff8003fff000

def z1390 : W := mkw 0x000c1a14d10d4354 0x00030685344350d5 0x881c060c301fc0ff 0x220701830c07f03f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z0,z1,z7,z2,z3,z5]),(1,[z0,z1,z8,z3,z5,z9]),(0,[z10,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z11,z3,z5,z12])],[(0,[z0,z1,z2,z3,z13,z5,z6]),(0,[z14,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z15,z16,z5]),(0,[z0,z1,z17,z8,z2,z3,z5]),(0,[z0,z1,z2,z3,z18,z5,z6])],[(0,[z0,z19,z1,z2,z3,z5,z6]),(1,[z0,z20,z1,z2,z3,z5]),(0,[z21,z0,z1,z2,z3,z5,z22]),(0,[z21,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z24,z5,z6]),(0,[z0,z1,z25,z2,z3,z23,z6])],[(0,[z26,z0,z1,z27,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z28,z6]),(0,[z0,z29,z1,z2,z30,z5,z6]),(0,[z0,z31,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z32,z6]),(1,[z0,z1,z25,z2,z3,z23])],[(0,[z0,z33,z1,z2,z3,z5,z6]),(0,[z0,z1,z34,z2,z3,z5,z6]),(0,[z0,z1,z35,z3,z5,z36,z6]),(0,[z0,z1,z2,z3,z37,z5,z6])],[(0,[z38,z0,z1,z2,z3,z5,z6]),(0,[z39,z0,z1,z8,z2,z3,z5]),(0,[z40,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z5,z41,z6]),(0,[z0,z42,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z43,z5,z44,z6])],[(1,[z0,z45,z1,z2,z5,z6]),(0,[z0,z1,z46,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z47,z5])],[(0,[z0,z48,z1,z2,z3,z5,z6]),(0,[z0,z49,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z50,z6]),(0,[z0,z51,z1,z2,z52,z5,z6]),(0,[z0,z1,z2,z3,z53,z5,z6]),(0,[z0,z1,z2,z54,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z55])]],
   [[(0,[z56,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z57,z5,z6]),(0,[z0,z1,z2,z3,z5,z22,z6]),(0,[z0,z1,z2,z3,z5,z58,z6]),(0,[z0,z59,z1,z2,z3,z5,z6])],[(0,[z0,z60,z1,z2,z3,z5,z6]),(0,[z0,z61,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z62,z6]),(0,[z0,z1,z2,z3,z63,z5,z6]),(0,[z0,z51,z29,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z64])],[(0,[z65,z0,z1,z7,z2,z3,z5]),(0,[z0,z66,z1,z2,z3,z23,z5])],[(0,[z67,z0,z1,z2,z68,z5,z6]),(0,[z0,z1,z2,z3,z5,z69,z6]),(0,[z0,z1,z2,z52,z3,z5,z6]),(0,[z70,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z16,z5]),(0,[z0,z1,z25,z2,z3,z23,z5])],[(0,[z71,z0,z1,z8,z2,z3,z5]),(0,[z0,z1,z2,z3,z72,z5,z6]),(0,[z0,z1,z7,z2,z3,z5,z73]),(0,[z0,z1,z2,z3,z5,z74,z6])],[(1,[z0,z1,z75,z2,z3,z5]),(0,[z0,z1,z2,z3,z76,z5,z6]),(0,[z0,z1,z2,z77,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z78]),(0,[z79,z0,z1,z7,z2,z3,z5]),(0,[z0,z80,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z81,z12])],[(0,[z0,z1,z2,z3,z82,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z83]),(0,[z0,z1,z2,z3,z5,z84,z6]),(1,[z0,z1,z2,z5,z32,z6]),(0,[z0,z1,z85,z3,z16,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z86])],[(0,[z87,z1,z88,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z89,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z90]),(0,[z0,z91,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z92,z5,z83]),(0,[z0,z1,z2,z3,z5,z93,z6])]],
   [[(0,[z67,z0,z1,z88,z3,z5,z6]),(0,[z1,z2,z94,z3,z95,z5,z6]),(0,[z0,z1,z96,z2,z3,z5,z6]),(0,[z0,z51,z1,z2,z3,z5,z6]),(0,[z0,z97,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z98,z5,z6]),(0,[z0,z1,z2,z3,z99,z5,z6])],[(0,[z100,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z101,z3,z5,z6]),(0,[z0,z1,z2,z3,z102,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z103]),(0,[z104,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z105,z6]),(0,[z0,z106,z1,z2,z3,z5,z6]),(0,[z71,z0,z1,z2,z3,z5,z12]),(0,[z39,z0,z1,z2,z94,z5,z6]),(0,[z0,z29,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z107,z5,z6])],[(1,[z0,z1,z2,z3,z5,z108]),(0,[z79,z0,z109,z1,z2,z3,z5]),(0,[z0,z1,z2,z27,z3,z23,z5])],[(0,[z110,z111,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z112,z3,z5,z6]),(0,[z113,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z114]),(0,[z0,z115,z1,z27,z3,z5,z6]),(0,[z116,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z117,z6]),(1,[z0,z1,z118,z2,z5,z44])],[(0,[z67,z0,z1,z119,z3,z5,z6]),(0,[z0,z1,z2,z120,z3,z5,z6]),(0,[z0,z1,z7,z2,z3,z5,z114]),(0,[z21,z0,z1,z2,z3,z5,z12]),(1,[z0,z51,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z121,z5,z6]),(0,[z0,z1,z122,z2,z3,z5,z6]),(0,[z0,z1,z7,z123,z2,z3,z5])],[(0,[z65,z1,z2,z3,z124,z5,z6]),(0,[z0,z1,z2,z3,z5,z125,z6]),(0,[z0,z1,z2,z3,z5,z126,z6]),(0,[z0,z1,z123,z2,z43,z5,z6])],[(0,[z127,z0,z1,z2,z3,z5,z6]),(0,[z87,z0,z115,z1,z3,z5,z6]),(0,[z0,z1,z128,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z129,z12]),(0,[z0,z1,z2,z130,z3,z5,z6])],[(0,[z0,z131,z1,z2,z3,z5,z6]),(0,[z0,z1,z7,z132,z2,z3,z5]),(0,[z0,z1,z133,z2,z3,z5,z12])]],
   [[(0,[z0,z1,z1,z2,z3,z5,z6]),(0,[z134,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z135]),(0,[z0,z136,z1,z2,z3,z5,z6])],[(0,[z0,z97,z2,z3,z5,z137,z6]),(0,[z138,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z139,z2,z3,z5,z6]),(0,[z0,z140,z1,z2,z3,z5,z6]),(0,[z0,z1,z141,z2,z3,z5,z6]),(0,[z0,z1,z35,z8,z3,z5,z6]),(0,[z0,z1,z142,z2,z3,z5,z6])],[(0,[z0,z1,z143,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z124,z5,z12]),(0,[z0,z1,z8,z2,z52,z3,z5]),(0,[z0,z144,z1,z2,z3,z5,z6]),(1,[z0,z1,z8,z3,z16,z5]),(0,[z0,z1,z8,z2,z3,z98,z5]),(0,[z0,z1,z2,z3,z5,z36,z12])],[(0,[z0,z145,z1,z2,z3,z5,z6]),(0,[z146,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z147]),(0,[z39,z71,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z5,z22,z6,z78]),(0,[z0,z1,z7,z2,z52,z3,z5]),(1,[z0,z144,z2,z3,z5,z148]),(0,[z0,z1,z35,z2,z3,z5,z6]),(0,[z0,z1,z85,z2,z3,z5,z6]),(0,[z0,z1,z2,z149,z3,z5,z6]),(0,[z0,z66,z1,z2,z3,z5,z12])],[(0,[z110,z0,z1,z2,z3,z4,z6]),(0,[z0,z150,z1,z2,z3,z5,z6]),(0,[z0,z151,z1,z2,z3,z5,z6]),(1,[z0,z29,z2,z52,z5,z6]),(0,[z0,z1,z123,z2,z3,z23,z5]),(0,[z0,z66,z1,z2,z3,z43,z6])],[(0,[z152,z0,z1,z2,z3,z5,z6]),(0,[z0,z153,z1,z2,z3,z5,z6])],[(0,[z154,z0,z1,z2,z3,z5,z6]),(0,[z65,z0,z1,z2,z3,z124,z6]),(0,[z0,z1,z2,z3,z5,z6,z6]),(0,[z0,z1,z2,z3,z155,z5,z6]),(0,[z0,z156,z1,z2,z3,z5,z6]),(0,[z157,z0,z1,z2,z3,z5,z6]),(0,[z158,z0,z1,z2,z3,z5,z12])]],
   [[(0,[z0,z1,z159,z2,z3,z5,z6]),(0,[z0,z1,z160,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z148]),(0,[z0,z1,z2,z161,z3,z5,z6]),(0,[z0,z162,z1,z2,z3,z5,z6])],[(0,[z0,z1,z8,z2,z3,z5,z22]),(0,[z0,z1,z2,z3,z5,z137,z6]),(0,[z0,z1,z123,z2,z30,z5,z6])],[(0,[z0,z1,z7,z2,z3,z5,z22]),(0,[z0,z115,z1,z2,z3,z5,z6]),(0,[z163,z0,z1,z2,z3,z5,z6]),(0,[z0,z164,z1,z8,z2,z3,z5])],[(0,[z87,z0,z1,z2,z3,z5,z6]),(0,[z165,z0,z1,z2,z3,z5,z6])],[(0,[z166,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z27,z3,z5,z12]),(0,[z0,z144,z1,z2,z3,z5,z148]),(0,[z0,z1,z8,z3,z30,z5,z6])],[(0,[z0,z1,z101,z143,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z167]),(0,[z0,z1,z168,z2,z3,z5,z6]),(0,[z0,z169,z1,z2,z3,z5,z6]),(0,[z0,z1,z170,z2,z3,z5,z6]),(1,[z0,z1,z2,z171,z43,z6])],[(0,[z71,z1,z2,z3,z95,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z172]),(0,[z0,z51,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z173])],[(0,[z0,z174,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z175,z95,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z176]),(0,[z100,z0,z1,z7,z2,z3,z5]),(1,[z0,z1,z177,z3,z5,z6]),(0,[z0,z1,z2,z3,z178,z5,z6]),(0,[z0,z1,z2,z3,z5,z12,z179]),(0,[z0,z1,z3,z5,z81,z6,z12])]],
   [[(0,[z180,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z181,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z182,z5]),(0,[z0,z1,z2,z3,z5,z183,z6]),(1,[z0,z1,z2,z3,z5,z184])],[(0,[z110,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z185]),(0,[z0,z1,z2,z3,z186,z5,z6]),(0,[z0,z1,z187,z2,z3,z5,z6]),(1,[z0,z1,z188,z3,z5,z6]),(0,[z0,z1,z118,z2,z5,z44,z6])],[(0,[z0,z1,z2,z3,z189,z5,z6]),(0,[z0,z1,z2,z3,z23,z92,z5]),(1,[z0,z1,z2,z155,z5,z6]),(0,[z0,z1,z2,z3,z190,z5,z6])],[(0,[z0,z1,z191,z7,z2,z3,z5]),(0,[z192,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z193]),(0,[z0,z1,z2,z194,z3,z5,z6])],[(0,[z0,z1,z2,z3,z195,z5,z6]),(0,[z0,z1,z2,z3,z23,z196,z5])],[(0,[z0,z1,z143,z2,z3,z5,z12]),(0,[z0,z109,z1,z2,z3,z5,z6]),(0,[z0,z1,z3,z30,z5,z129,z6]),(0,[z197,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z198,z6]),(0,[z0,z1,z2,z199,z3,z5,z6]),(0,[z0,z1,z2,z3,z200,z5,z6]),(0,[z0,z1,z201,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z202,z5,z6])],[(0,[z0,z145,z1,z143,z2,z3,z5]),(0,[z0,z1,z2,z3,z203,z5,z6]),(0,[z0,z1,z118,z2,z3,z5,z148]),(0,[z0,z1,z123,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z204,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z205,z6]),(1,[z0,z1,z206,z2,z3,z5]),(0,[z207,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z133,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z208,z6]),(0,[z0,z1,z209,z2,z3,z23,z5])],[(1,[z210,z0,z1,z3,z5,z6]),(0,[z0,z1,z211,z2,z3,z5,z6]),(0,[z0,z1,z212,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z213]),(0,[z0,z1,z214,z2,z3,z5,z6]),(0,[z0,z1,z3,z30,z5,z36,z6]),(0,[z0,z1,z2,z175,z5,z215,z6]),(0,[z0,z1,z2,z3,z5,z216,z6]),(0,[z0,z1,z2,z3,z5,z6,z217]),(0,[z0,z1,z8,z2,z3,z5,z218])],[(0,[z0,z1,z2,z3,z5,z6,z219]),(0,[z0,z29,z1,z2,z3,z5,z220]),(0,[z0,z29,z1,z2,z175,z5,z6]),(0,[z0,z164,z1,z2,z3,z5,z216]),(0,[z0,z1,z8,z2,z3,z37,z5]),(0,[z0,z1,z2,z3,z23,z5,z9])],[(0,[z221,z0,z1,z2,z3,z5,z6]),(0,[z222,z0,z1,z8,z2,z3,z5]),(0,[z0,z1,z223,z2,z3,z5,z6])],[(0,[z224,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z94,z43,z5,z6]),(0,[z0,z225,z1,z2,z3,z5,z6]),(0,[z0,z226,z1,z2,z3,z5,z6]),(0,[z0,z1,z7,z2,z3,z227,z5]),(0,[z0,z1,z2,z3,z5,z44,z12]),(0,[z0,z228,z1,z2,z3,z23,z5])],[(0,[z0,z1,z206,z2,z27,z3,z5]),(0,[z0,z1,z8,z2,z3,z5,z129]),(0,[z0,z1,z229,z2,z3,z5,z6])],[(0,[z0,z1,z230,z2,z27,z3,z5]),(1,[z0,z1,z2,z3,z5,z231]),(0,[z0,z97,z1,z2,z3,z137,z6]),(0,[z0,z1,z7,z2,z3,z5,z129]),(0,[z0,z1,z8,z3,z5,z6,z9]),(0,[z0,z1,z8,z2,z3,z5,z44]),(0,[z0,z1,z177,z2,z3,z5,z6]),(0,[z0,z1,z17,z2,z3,z23,z5])]],
   [[(0,[z39,z0,z51,z1,z2,z5,z6]),(0,[z40,z0,z97,z1,z2,z3,z6]),(0,[z0,z115,z1,z7,z2,z3,z5]),(0,[z0,z232,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z233,z5,z6]),(0,[z0,z1,z234,z2,z3,z5,z6]),(1,[z0,z1,z8,z2,z3,z5]),(0,[z0,z1,z7,z2,z3,z5,z44]),(0,[z0,z1,z2,z161,z5,z6,z218])],[(0,[z87,z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z95,z43,z5,z6]),(0,[z235,z0,z1,z2,z3,z5,z6]),(0,[z0,z236,z1,z2,z3,z5,z6]),(0,[z165,z0,z1,z7,z2,z3,z5]),(0,[z237,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z7,z2,z3,z95,z5]),(0,[z0,z1,z2,z175,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z218])],[(0,[z0,z1,z2,z3,z238,z5,z6]),(0,[z0,z1,z239,z2,z3,z5,z6]),(0,[z39,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z8,z2,z94,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z240]),(0,[z0,z1,z2,z3,z182,z30,z5]),(1,[z0,z1,z2,z149,z5,z6]),(0,[z0,z66,z1,z2,z5,z215,z6])],[(1,[z71,z1,z2,z95,z5,z6]),(0,[z241,z0,z1,z2,z3,z5,z6]),(0,[z0,z66,z29,z1,z2,z5,z6]),(0,[z0,z1,z7,z2,z3,z5,z242])],[(0,[z1,z2,z3,z124,z5,z114,z6]),(0,[z0,z1,z2,z43,z5,z215,z6]),(0,[z0,z1,z2,z3,z243,z5,z6])],[(0,[z0,z1,z2,z3,z5,z244,z6]),(0,[z0,z1,z2,z245,z3,z5,z6]),(0,[z0,z1,z85,z2,z171,z3,z6]),(1,[z0,z1,z2,z3,z23,z12])],[(0,[z110,z0,z1,z7,z2,z3,z5]),(0,[z71,z0,z51,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z246,z5,z6]),(1,[z0,z1,z2,z3,z5,z247]),(1,[z0,z1,z248,z2,z3,z5]),(0,[z0,z1,z249,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z250]),(0,[z251,z0,z1,z2,z3,z5,z12])]],
   [[(1,[z0,z1,z2,z3,z5,z252]),(0,[z0,z1,z2,z3,z5,z6,z253]),(0,[z254,z0,z1,z2,z3,z5,z6]),(0,[z0,z226,z1,z2,z3,z30,z6]),(0,[z0,z1,z2,z3,z5,z255,z6]),(0,[z0,z1,z2,z11,z5,z6,z12])],[(0,[z256,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z88,z27,z3,z5,z6]),(0,[z0,z1,z2,z94,z30,z5,z6]),(0,[z0,z1,z257,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z258]),(0,[z0,z164,z1,z2,z3,z16,z6]),(0,[z0,z1,z118,z2,z3,z5,z218])],[(0,[z259,z0,z1,z2,z3,z5,z6]),(0,[z71,z0,z1,z2,z3,z23,z5]),(0,[z65,z0,z1,z8,z2,z3,z5]),(0,[z260,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z261,z6])],[(0,[z0,z262,z1,z2,z3,z5,z6]),(0,[z0,z109,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z263,z5,z6]),(0,[z0,z1,z2,z3,z264,z5,z6]),(0,[z0,z1,z3,z5,z36,z6,z9]),(0,[z0,z1,z7,z3,z5,z36,z6])],[(0,[z110,z0,z19,z2,z3,z5,z6]),(0,[z65,z0,z1,z2,z3,z114,z6]),(1,[z26,z0,z27,z3,z5,z6]),(0,[z0,z1,z2,z171,z3,z215,z6]),(0,[z0,z1,z2,z3,z265,z43,z5])],[(0,[z266,z0,z1,z2,z3,z5,z6]),(0,[z67,z0,z115,z1,z3,z5,z6]),(0,[z0,z1,z2,z95,z30,z5,z6]),(0,[z79,z0,z1,z8,z2,z3,z5]),(0,[z0,z1,z267,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z23,z5,z73]),(0,[z0,z1,z248,z2,z3,z5,z6]),(0,[z0,z1,z85,z2,z3,z16,z6]),(0,[z0,z66,z1,z2,z5,z44,z6]),(0,[z0,z1,z118,z2,z3,z5,z44])],[(0,[z0,z1,z2,z3,z268,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z108]),(0,[z0,z1,z269,z2,z5,z129,z6]),(2,[z0,z1,z223,z3,z5])]],
   [[(0,[z0,z1,z2,z270,z3,z5,z6]),(0,[z0,z1,z8,z2,z271,z3,z5])],[(0,[z0,z1,z2,z272,z3,z5,z6]),(0,[z0,z1,z273,z2,z3,z5,z6]),(0,[z0,z51,z1,z2,z43,z5,z6]),(0,[z0,z1,z2,z274,z3,z5,z6]),(0,[z275,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z7,z35,z2,z3,z5]),(1,[z0,z1,z2,z3,z5,z216])],[(0,[z276,z0,z1,z2,z3,z5,z6]),(0,[z0,z45,z1,z2,z3,z5,z6]),(0,[z0,z20,z1,z2,z3,z5,z6]),(0,[z277,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z114,z6]),(0,[z0,z1,z2,z3,z278,z5,z6]),(0,[z0,z1,z2,z5,z32,z129,z6]),(0,[z0,z1,z2,z3,z279,z5,z6])],[(0,[z280,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z92,z124,z6]),(0,[z0,z1,z8,z2,z3,z124,z5]),(0,[z0,z281,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z282,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z283,z6]),(0,[z0,z284,z1,z2,z3,z5,z6]),(1,[z0,z1,z223,z2,z3,z5])],[(0,[z111,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z285,z2,z3,z5,z6]),(0,[z0,z1,z286,z2,z3,z5,z6]),(0,[z0,z1,z7,z2,z3,z124,z5]),(0,[z0,z1,z2,z3,z5,z6,z179]),(0,[z0,z1,z223,z3,z5,z6,z12]),(0,[z0,z1,z2,z287,z3,z23,z5])],[(0,[z67,z1,z2,z119,z3,z5,z6]),(0,[z39,z0,z1,z2,z3,z5,z12]),(0,[z288,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z289,z6])],[(0,[z0,z290,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z291,z5,z6]),(0,[z0,z1,z2,z3,z292,z5,z6]),(0,[z0,z1,z2,z293,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z5,z114]),(0,[z0,z232,z1,z7,z2,z3,z5]),(0,[z0,z294,z1,z2,z3,z5,z6]),(1,[z0,z1,z223,z3,z5,z12])],[(0,[z210,z0,z1,z143,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z295]),(0,[z39,z1,z2,z94,z3,z5,z6]),(0,[z0,z1,z2,z94,z3,z5,z12]),(0,[z0,z1,z296,z2,z3,z5,z6])]],
   [[(0,[z0,z19,z1,z8,z2,z3,z5]),(0,[z0,z1,z88,z2,z3,z5,z6]),(0,[z0,z1,z2,z297,z3,z5,z6]),(0,[z0,z1,z2,z3,z95,z23,z5]),(0,[z0,z1,z2,z3,z5,z298,z6]),(0,[z0,z1,z299,z2,z3,z5,z6])],[(0,[z21,z0,z1,z118,z2,z3,z5]),(0,[z0,z1,z123,z2,z175,z5,z6]),(0,[z0,z1,z2,z3,z300,z5,z6]),(0,[z301,z0,z1,z2,z3,z5,z6])],[(0,[z67,z0,z1,z2,z3,z5,z6]),(0,[z302,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z303,z5,z6]),(0,[z0,z1,z2,z304,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z305,z6]),(0,[z0,z1,z306,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z307,z5,z6]),(1,[z0,z1,z7,z2,z227,z5])],[(0,[z0,z1,z2,z3,z5,z308,z6]),(0,[z0,z1,z2,z3,z5,z309,z6]),(0,[z0,z1,z46,z8,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z310,z6])],[(0,[z26,z0,z1,z2,z3,z5,z6]),(0,[z0,z51,z1,z2,z30,z5,z6]),(0,[z0,z2,z3,z92,z5,z137,z6]),(0,[z0,z1,z2,z3,z5,z12,z9])],[(0,[z0,z109,z144,z2,z3,z5,z6]),(0,[z0,z311,z1,z2,z3,z5,z6])],[(0,[z0,z1,z312,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z313,z6]),(0,[z0,z164,z1,z2,z3,z5,z314]),(0,[z315,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z12,z316])]],
   [[(0,[z0,z1,z2,z3,z5,z317,z6]),(1,[z0,z1,z2,z3,z5,z318]),(0,[z0,z1,z319,z2,z3,z5,z6]),(0,[z0,z164,z1,z2,z3,z23,z5]),(0,[z0,z1,z320,z2,z3,z5,z6])],[(1,[z0,z1,z2,z321,z3,z5]),(0,[z322,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z323,z5,z6]),(0,[z0,z1,z7,z8,z3,z5,z6])],[(0,[z0,z1,z324,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z325,z5]),(0,[z0,z1,z248,z2,z3,z30,z5]),(0,[z0,z164,z1,z2,z3,z129,z6]),(0,[z0,z1,z8,z2,z3,z5,z6]),(1,[z0,z1,z3,z5,z81,z12]),(1,[z0,z1,z2,z11,z5,z6])],[(0,[z0,z19,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z326,z5,z6]),(1,[z0,z1,z2,z3,z15,z5]),(0,[z0,z1,z7,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z43,z5,z6])],[(0,[z110,z1,z143,z2,z3,z5,z6]),(0,[z0,z1,z2,z327,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z5,z22]),(0,[z0,z1,z2,z3,z5,z328,z12]),(0,[z0,z1,z2,z3,z23,z23,z5])],[(0,[z0,z20,z1,z143,z2,z3,z5]),(0,[z0,z1,z2,z3,z329,z5,z6]),(0,[z0,z1,z2,z330,z3,z5,z6]),(0,[z0,z1,z2,z3,z331,z5,z6]),(0,[z332,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z85,z2,z3,z23,z5])],[(0,[z333,z0,z1,z2,z3,z5,z6]),(0,[z0,z51,z1,z8,z2,z3,z5]),(0,[z0,z1,z2,z3,z334,z5,z6]),(0,[z0,z1,z2,z335,z3,z5,z6]),(0,[z0,z1,z2,z3,z336,z5,z6]),(0,[z0,z164,z1,z85,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z337]),(0,[z0,z1,z2,z3,z5,z86,z12]),(0,[z0,z338,z1,z2,z3,z23,z5])],[(0,[z0,z339,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z119,z3,z5,z6]),(0,[z0,z340,z1,z2,z3,z5,z6]),(0,[z0,z232,z1,z2,z3,z137,z6]),(0,[z0,z1,z85,z2,z3,z129,z6]),(0,[z341,z0,z1,z2,z3,z5,z6]),(0,[z104,z0,z1,z8,z2,z3,z5]),(0,[z100,z0,z1,z8,z2,z3,z5]),(1,[z0,z1,z2,z161,z5,z218]),(0,[z0,z1,z2,z5,z328,z6,z12])]],
   [[(0,[z0,z1,z2,z3,z342,z5,z6])],[(0,[z0,z1,z2,z3,z343,z5,z6])],[(0,[z0,z1,z2,z3,z5,z344,z6]),(0,[z111,z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z345,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z95,z5,z12]),(0,[z346,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z347,z2,z3,z5,z6]),(0,[z0,z1,z348,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z349]),(0,[z0,z1,z350,z2,z3,z23,z5]),(0,[z0,z51,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z92,z5,z6]),(0,[z0,z1,z123,z3,z30,z5,z6]),(0,[z351,z0,z1,z2,z3,z5,z6]),(0,[z0,z66,z1,z2,z3,z215,z6])],[(0,[z0,z0,z1,z2,z3,z5,z6]),(0,[z79,z0,z144,z1,z2,z3,z5]),(0,[z0,z352,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z353,z5,z6]),(0,[z0,z1,z7,z2,z3,z5,z148]),(0,[z354,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z68,z3,z5,z6]),(0,[z0,z1,z2,z52,z94,z5,z6]),(0,[z40,z65,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z252,z6]),(1,[z40,z1,z2,z3,z114,z6]),(0,[z0,z1,z355,z2,z3,z5,z6]),(0,[z0,z1,z118,z188,z3,z5,z6])],[(0,[z0,z1,z8,z170,z2,z3,z5]),(1,[z0,z1,z2,z3,z265,z5])],[(0,[z0,z1,z2,z356,z3,z5,z6]),(0,[z111,z0,z19,z2,z3,z5,z6]),(0,[z40,z1,z2,z3,z5,z114,z6]),(0,[z0,z1,z2,z3,z23,z5,z78]),(0,[z0,z1,z2,z3,z30,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z357]),(0,[z0,z1,z2,z171,z3,z5,z6]),(0,[z0,z358,z1,z2,z3,z5,z12]),(1,[z0,z1,z2,z5,z328,z12]),(0,[z0,z1,z2,z3,z23,z359,z5])]],
   [[(1,[z0,z1,z2,z360,z5,z6]),(0,[z67,z0,z1,z7,z2,z3,z5]),(0,[z71,z0,z1,z2,z95,z5,z6]),(0,[z0,z1,z361,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z148,z6]),(0,[z0,z2,z3,z5,z148,z6,z73]),(0,[z0,z1,z2,z3,z16,z5,z12]),(0,[z302,z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z12,z362])],[(0,[z0,z1,z363,z2,z3,z5,z6]),(0,[z40,z0,z1,z2,z3,z124,z6]),(0,[z0,z1,z2,z3,z124,z137,z6]),(0,[z0,z97,z1,z7,z2,z3,z5]),(0,[z0,z144,z1,z8,z2,z3,z5]),(0,[z0,z1,z118,z2,z3,z5,z6])],[(0,[z364,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z365,z3,z5,z6]),(0,[z0,z1,z2,z3,z182,z5,z6]),(0,[z0,z1,z35,z8,z2,z3,z5]),(0,[z0,z164,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z366,z5,z6]),(0,[z0,z1,z367,z2,z3,z5,z6]),(0,[z0,z1,z368,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z369,z6]),(0,[z0,z1,z2,z11,z3,z5,z6])],[(0,[z0,z1,z2,z370,z3,z5,z6]),(1,[z0,z1,z2,z3,z371,z5]),(0,[z26,z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z8,z350,z2,z3,z5]),(0,[z0,z372,z1,z2,z3,z5,z6]),(0,[z0,z144,z2,z3,z5,z148,z6])],[(0,[z0,z373,z1,z2,z3,z5,z6]),(0,[z67,z26,z0,z1,z3,z5,z6]),(0,[z0,z1,z7,z350,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z374,z6]),(0,[z0,z1,z2,z3,z5,z375,z6]),(0,[z0,z164,z66,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z376,z5,z6])],[(0,[z67,z87,z1,z2,z3,z5,z6]),(0,[z39,z0,z29,z1,z2,z5,z6]),(0,[z377,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z314]),(0,[z0,z156,z1,z8,z2,z3,z5]),(0,[z0,z378,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z215,z12]),(0,[z0,z1,z379,z2,z3,z5,z6])],[(0,[z0,z1,z2,z380,z3,z5,z6]),(0,[z0,z1,z2,z3,z381,z5,z6]),(0,[z0,z29,z2,z52,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z30,z5]),(0,[z0,z1,z2,z382,z3,z5,z6]),(1,[z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z23,z5,z12])],[(0,[z0,z1,z2,z3,z5,z383,z6]),(0,[z0,z115,z1,z2,z3,z5,z231]),(0,[z0,z1,z7,z2,z3,z30,z5]),(0,[z0,z1,z85,z2,z3,z5,z12])]],
   [[(0,[z384,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z385,z2,z3,z5,z6]),(0,[z0,z115,z1,z8,z2,z3,z5]),(0,[z0,z1,z386,z2,z3,z23,z5])],[(0,[z0,z387,z1,z2,z3,z5,z6]),(0,[z87,z0,z1,z8,z2,z3,z5]),(0,[z0,z1,z2,z3,z388,z5,z6]),(0,[z0,z1,z2,z389,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z390,z6])],[(0,[z0,z1,z2,z3,z391,z5,z6]),(0,[z0,z1,z2,z392,z3,z5,z6]),(0,[z393,z0,z1,z2,z3,z5,z6]),(0,[z0,z29,z1,z2,z52,z5,z6]),(1,[z0,z109,z2,z3,z5,z73]),(0,[z0,z1,z2,z3,z5,z394,z6]),(0,[z0,z395,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z47,z5,z12])],[(0,[z396,z0,z1,z2,z3,z5,z6]),(0,[z0,z66,z1,z2,z95,z5,z6]),(0,[z0,z1,z2,z3,z5,z397,z6]),(0,[z0,z1,z2,z398,z3,z5,z6]),(0,[z0,z1,z2,z399,z3,z5,z6]),(0,[z0,z1,z168,z8,z2,z3,z5]),(0,[z0,z1,z8,z2,z3,z5,z215])],[(0,[z0,z1,z400,z2,z3,z5,z6]),(0,[z71,z0,z29,z1,z2,z5,z6]),(0,[z0,z1,z2,z401,z3,z5,z6]),(0,[z0,z1,z2,z402,z3,z5,z6]),(0,[z0,z1,z403,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z137,z12]),(0,[z0,z144,z1,z7,z2,z3,z5]),(0,[z0,z1,z404,z2,z3,z5,z6]),(0,[z0,z1,z7,z2,z3,z5,z215]),(0,[z0,z1,z2,z3,z5,z6,z250])],[(0,[z0,z1,z2,z3,z405,z5,z6]),(0,[z0,z1,z350,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z406,z6]),(0,[z0,z66,z1,z123,z2,z5,z6])],[(0,[z0,z1,z2,z407,z3,z5,z6]),(0,[z87,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z321,z3,z95,z5]),(0,[z0,z1,z2,z3,z5,z22,z73]),(0,[z0,z1,z2,z3,z5,z408,z6]),(0,[z0,z1,z2,z3,z5,z247,z6]),(0,[z0,z1,z8,z2,z3,z5,z137]),(0,[z0,z409,z1,z2,z3,z5,z6]),(0,[z0,z1,z7,z2,z149,z3,z5]),(0,[z0,z1,z7,z2,z3,z5,z218]),(0,[z0,z1,z2,z410,z3,z23,z5])],[(0,[z110,z0,z1,z8,z2,z3,z5]),(1,[z0,z1,z2,z5,z374,z6]),(0,[z0,z1,z8,z85,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z81,z6])]],
   [[(0,[z0,z1,z8,z2,z119,z3,z5]),(0,[z65,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z411,z2,z3,z5,z6]),(0,[z0,z1,z7,z85,z2,z3,z5]),(0,[z0,z1,z345,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z23,z43,z5])],[(0,[z1,z88,z2,z119,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z412,z6]),(0,[z0,z413,z1,z2,z3,z5,z6]),(1,[z79,z1,z2,z3,z5,z22]),(0,[z0,z1,z2,z30,z5,z44,z6]),(0,[z351,z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z227,z5,z6])],[(0,[z0,z1,z414,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z9])],[(0,[z110,z0,z1,z415,z3,z5,z6]),(0,[z79,z0,z1,z2,z3,z5,z22]),(0,[z79,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z416,z2,z3,z5,z6]),(0,[z0,z29,z1,z2,z3,z5,z6]),(0,[z0,z109,z1,z8,z2,z3,z5])],[(0,[z417,z0,z1,z2,z3,z5,z6]),(0,[z0,z350,z2,z27,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z316]),(1,[z0,z226,z1,z2,z3,z6])],[(0,[z0,z1,z2,z418,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z261]),(0,[z419,z0,z1,z2,z3,z23,z5])],[(1,[z0,z1,z2,z3,z420,z6]),(0,[z421,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z231,z6]),(0,[z0,z1,z422,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z161,z3,z5]),(1,[z0,z1,z423,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z424,z6])],[(1,[z0,z1,z415,z3,z5,z6]),(0,[z0,z1,z2,z425,z3,z5,z6]),(0,[z0,z1,z2,z3,z426,z5,z6]),(0,[z0,z1,z7,z2,z94,z3,z5]),(1,[z0,z1,z2,z3,z5,z427]),(0,[z0,z1,z7,z2,z161,z3,z5]),(0,[z0,z1,z118,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z428,z6])]],
   [[(0,[z0,z1,z2,z94,z3,z23,z5]),(0,[z429,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z129,z6]),(0,[z0,z430,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z12])],[(0,[z0,z431,z1,z2,z3,z5,z6]),(0,[z40,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z432,z5,z6]),(0,[z0,z1,z433,z2,z3,z5,z6]),(0,[z0,z232,z1,z2,z3,z92,z6]),(0,[z0,z434,z1,z2,z3,z5,z6]),(0,[z0,z1,z133,z2,z3,z5,z6]),(0,[z0,z435,z1,z2,z3,z5,z6])],[(0,[z0,z436,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z437,z3,z5,z6]),(0,[z0,z1,z2,z438,z3,z5,z6]),(0,[z0,z439,z1,z2,z3,z5,z6]),(0,[z0,z1,z440,z2,z3,z5,z6])],[(0,[z40,z0,z232,z1,z2,z3,z6]),(0,[z0,z1,z441,z2,z3,z5,z6]),(0,[z0,z442,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z408]),(0,[z0,z232,z2,z3,z92,z5,z6]),(0,[z0,z1,z443,z2,z3,z5,z6]),(1,[z0,z1,z444,z2,z3,z5]),(1,[z0,z1,z2,z3,z5,z369])],[(0,[z0,z1,z415,z2,z3,z5,z6]),(0,[z445,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z446,z6]),(1,[z0,z1,z2,z227,z5,z6]),(0,[z0,z1,z447,z2,z3,z5,z6]),(0,[z0,z448,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z449,z6]),(0,[z26,z87,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z3,z124,z5,z6]),(0,[z0,z51,z1,z2,z175,z5,z6]),(0,[z450,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z171,z3,z5]),(0,[z0,z1,z2,z3,z5,z36,z6]),(0,[z0,z1,z2,z3,z451,z5,z6])],[(0,[z0,z1,z2,z452,z3,z5,z6]),(0,[z0,z19,z1,z2,z3,z23,z5]),(0,[z79,z0,z1,z2,z3,z5,z78]),(0,[z0,z1,z2,z3,z24,z23,z5]),(0,[z0,z232,z1,z8,z2,z3,z5]),(0,[z0,z1,z2,z3,z453,z5,z6]),(0,[z0,z1,z7,z2,z171,z3,z5]),(0,[z0,z66,z1,z2,z3,z5,z6])],[(0,[z454,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z3,z5,z455]),(0,[z0,z1,z2,z3,z456,z5,z6]),(0,[z0,z457,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z458,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z459]),(0,[z0,z1,z460,z2,z3,z5,z6]),(0,[z0,z1,z25,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z2,z461,z3,z5,z6]),(0,[z26,z0,z2,z27,z3,z5,z6]),(0,[z462,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z47,z5]),(1,[z0,z1,z2,z3,z5,z242]),(0,[z0,z1,z463,z2,z3,z5,z6])],[(0,[z158,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z444,z2,z3,z5,z129]),(0,[z0,z1,z7,z2,z3,z47,z5])],[(0,[z65,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z464,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z465]),(0,[z466,z0,z1,z2,z3,z5,z6])],[(0,[z467,z0,z1,z2,z3,z5,z6]),(0,[z0,z468,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z469,z6]),(0,[z0,z1,z2,z3,z53,z23,z5])],[(0,[z0,z1,z470,z2,z3,z5,z6]),(0,[z0,z1,z2,z471,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z472,z6])],[(0,[z0,z473,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z474,z6]),(0,[z79,z0,z1,z2,z3,z5,z12]),(0,[z0,z475,z1,z2,z3,z5,z6]),(1,[z0,z97,z2,z3,z137,z6]),(0,[z0,z1,z2,z3,z5,z6,z362]),(0,[z0,z1,z8,z2,z3,z16,z5]),(0,[z0,z1,z249,z8,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z420,z6]),(1,[z110,z143,z2,z3,z5,z6]),(0,[z0,z1,z2,z476,z3,z5,z6]),(0,[z0,z1,z385,z2,z119,z3,z5]),(0,[z40,z0,z1,z2,z3,z114,z6]),(0,[z0,z1,z2,z27,z3,z5,z6]),(0,[z0,z1,z2,z161,z3,z5,z73]),(0,[z477,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z478,z6])],[(0,[z0,z1,z2,z52,z3,z23,z5]),(1,[z0,z1,z35,z8,z3,z5]),(0,[z0,z164,z1,z8,z3,z5,z6]),(0,[z0,z1,z8,z3,z16,z5,z6])]],
   [[(0,[z0,z1,z2,z479,z3,z5,z6]),(0,[z0,z1,z480,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z481]),(0,[z0,z1,z2,z3,z5,z242,z6]),(0,[z0,z1,z2,z3,z5,z5,z12]),(0,[z0,z1,z2,z3,z5,z12,z12])],[(0,[z0,z1,z482,z2,z3,z5,z6]),(0,[z0,z29,z1,z7,z2,z3,z5]),(1,[z0,z1,z2,z3,z5,z64]),(0,[z0,z483,z1,z2,z3,z5,z6]),(0,[z484,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z485,z6])],[(0,[z0,z1,z2,z486,z3,z5,z6]),(0,[z0,z66,z1,z487,z3,z5,z6])],[(0,[z0,z45,z1,z143,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z488,z6]),(0,[z0,z1,z2,z3,z23,z6,z12])],[(0,[z0,z1,z2,z3,z5,z489,z6]),(0,[z0,z1,z2,z175,z94,z5,z6]),(0,[z40,z0,z1,z2,z3,z5,z252]),(0,[z21,z0,z1,z7,z2,z3,z5]),(0,[z0,z51,z1,z2,z3,z23,z5]),(0,[z0,z97,z1,z2,z3,z23,z5]),(0,[z0,z1,z422,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z23,z279,z5])],[(0,[z0,z1,z2,z490,z3,z5,z6]),(0,[z0,z1,z491,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z27,z3,z5]),(0,[z0,z492,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z493,z3,z5,z6]),(0,[z100,z0,z1,z2,z3,z23,z5])],[(0,[z0,z1,z7,z2,z27,z3,z5]),(0,[z494,z0,z1,z2,z3,z5,z6]),(0,[z429,z0,z1,z7,z2,z3,z5])],[(0,[z0,z1,z143,z2,z3,z5,z6]),(0,[z40,z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z371,z124,z5]),(0,[z26,z0,z115,z2,z3,z5,z6]),(0,[z0,z1,z133,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z47,z6,z12])]],
   [[(0,[z0,z19,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z24,z5,z12]),(1,[z0,z1,z123,z30,z5,z6]),(0,[z0,z1,z35,z2,z43,z5,z6])],[(1,[z0,z473,z1,z2,z3,z6]),(0,[z0,z1,z495,z2,z3,z5,z6]),(0,[z21,z0,z109,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z73,z12]),(0,[z0,z1,z123,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z175,z3,z5]),(0,[z0,z1,z2,z5,z44,z6,z218])],[(0,[z19,z1,z143,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z496,z6]),(0,[z111,z0,z1,z8,z2,z3,z5]),(0,[z0,z1,z350,z2,z497,z5,z6]),(0,[z0,z1,z7,z2,z175,z3,z5]),(0,[z0,z66,z1,z85,z2,z3,z6])],[(0,[z79,z1,z2,z3,z5,z22,z6]),(0,[z0,z1,z2,z3,z5,z498,z6]),(0,[z0,z109,z1,z2,z3,z5,z73]),(0,[z0,z1,z2,z175,z171,z5,z6]),(1,[z0,z1,z2,z3,z5,z93])],[(0,[z0,z97,z1,z2,z3,z92,z6]),(0,[z0,z66,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z161,z43,z5,z6])],[(0,[z0,z1,z2,z2,z3,z5,z6]),(0,[z0,z1,z350,z88,z3,z5,z6]),(0,[z0,z499,z1,z2,z3,z5,z6]),(0,[z0,z1,z500,z2,z3,z5,z6]),(0,[z501,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z25,z7,z2,z3,z5])],[(0,[z87,z0,z1,z88,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z22,z12]),(0,[z0,z29,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z23,z5,z148]),(0,[z0,z1,z133,z85,z2,z3,z5]),(1,[z0,z66,z1,z2,z215,z6]),(0,[z0,z1,z2,z3,z23,z5,z5])],[(0,[z0,z1,z75,z2,z3,z5,z6]),(0,[z0,z1,z2,z502,z3,z5,z6]),(0,[z0,z503,z1,z2,z5,z137,z6]),(0,[z0,z144,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z5,z44,z6])]],
   [[(0,[z0,z1,z2,z3,z360,z5,z6]),(1,[z67,z1,z119,z3,z5,z6]),(0,[z67,z0,z1,z8,z2,z3,z5]),(0,[z0,z115,z1,z350,z3,z5,z6]),(0,[z0,z504,z1,z2,z3,z5,z6]),(0,[z0,z503,z1,z2,z3,z5,z6]),(0,[z0,z1,z35,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z5,z6,z184])],[(0,[z0,z1,z350,z119,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z505]),(0,[z0,z1,z2,z52,z3,z5,z12]),(0,[z0,z97,z1,z8,z2,z3,z5]),(0,[z0,z1,z2,z3,z506,z5,z6])],[(0,[z87,z0,z1,z119,z3,z5,z6]),(0,[z21,z0,z1,z2,z161,z3,z5]),(1,[z0,z1,z2,z3,z5,z220]),(0,[z0,z1,z2,z3,z16,z5,z217])],[(1,[z0,z1,z2,z68,z5,z6]),(0,[z26,z0,z1,z8,z2,z3,z5]),(0,[z507,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z497,z3,z5,z6]),(0,[z0,z1,z2,z3,z508,z5,z6]),(0,[z0,z1,z2,z3,z325,z5,z6]),(0,[z0,z1,z85,z3,z30,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z193])],[(0,[z0,z1,z509,z2,z3,z5,z6]),(0,[z39,z0,z1,z2,z95,z5,z6]),(0,[z510,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z511,z2,z3,z5,z6]),(0,[z0,z1,z35,z2,z30,z5,z6]),(0,[z0,z1,z2,z3,z265,z5,z6]),(0,[z0,z1,z2,z161,z3,z23,z5])],[(0,[z0,z1,z101,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z512,z5,z6]),(0,[z0,z1,z119,z27,z3,z5,z6]),(1,[z0,z1,z2,z497,z5,z6]),(0,[z0,z513,z1,z2,z3,z5,z6]),(0,[z514,z0,z1,z2,z3,z5,z6])],[(0,[z515,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z371,z5,z6]),(0,[z0,z115,z1,z2,z3,z23,z5]),(0,[z0,z97,z1,z2,z3,z5,z12]),(0,[z0,z1,z35,z85,z3,z5,z6]),(0,[z0,z1,z118,z177,z3,z5,z6]),(1,[z0,z1,z267,z2,z3,z5])],[(0,[z87,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z516,z5,z6]),(0,[z0,z517,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z337,z6]),(0,[z100,z0,z1,z2,z3,z5,z12])]],
   [[(0,[z110,z0,z143,z2,z3,z5,z6]),(0,[z0,z339,z1,z143,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z518,z6]),(0,[z0,z1,z2,z3,z5,z519,z6]),(0,[z0,z97,z1,z2,z3,z5,z247]),(0,[z0,z1,z2,z161,z30,z5,z6]),(0,[z0,z1,z8,z8,z2,z3,z5])],[(0,[z0,z164,z1,z2,z399,z5,z6]),(1,[z0,z164,z1,z8,z3,z5]),(0,[z0,z1,z2,z487,z3,z5,z6]),(0,[z251,z0,z1,z2,z3,z5,z6])],[(1,[z0,z115,z350,z3,z5,z6]),(0,[z0,z66,z1,z35,z2,z5,z6])],[(0,[z0,z1,z520,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z521,z6]),(0,[z0,z1,z8,z88,z2,z3,z5]),(0,[z522,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z523,z5,z6]),(0,[z0,z1,z2,z524,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z525,z6]),(0,[z0,z1,z2,z3,z526,z5,z6]),(0,[z0,z1,z2,z3,z527,z5,z6])],[(0,[z0,z1,z7,z88,z2,z3,z5]),(0,[z0,z1,z8,z2,z3,z92,z5]),(0,[z0,z1,z2,z3,z528,z5,z6]),(0,[z0,z1,z7,z2,z149,z5,z6]),(0,[z0,z1,z25,z2,z3,z47,z6]),(0,[z0,z1,z209,z2,z3,z5,z6])],[(0,[z529,z0,z1,z2,z3,z5,z6]),(0,[z110,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z143,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z124,z5,z108]),(0,[z0,z1,z2,z3,z5,z530,z6]),(0,[z0,z1,z2,z3,z531,z5,z6]),(0,[z0,z1,z7,z2,z3,z92,z5]),(0,[z0,z1,z444,z2,z3,z5,z6]),(1,[z0,z1,z2,z11,z5,z12])],[(0,[z0,z1,z2,z3,z5,z6,z78]),(0,[z532,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z533,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z534]),(0,[z0,z1,z2,z3,z535,z5,z6])]],
   [[(0,[z110,z0,z1,z356,z3,z5,z6]),(0,[z0,z1,z536,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z43,z5,z250]),(0,[z0,z1,z2,z3,z23,z5,z218]),(0,[z0,z1,z2,z3,z5,z537,z6])],[(0,[z65,z0,z1,z2,z538,z5,z6]),(0,[z0,z539,z1,z2,z3,z5,z6]),(0,[z0,z109,z1,z2,z3,z23,z5]),(0,[z0,z144,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z30,z5,z215,z6]),(0,[z0,z1,z2,z3,z5,z12,z540]),(0,[z0,z228,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z541,z5,z6]),(0,[z0,z1,z2,z3,z5,z542,z6]),(0,[z0,z1,z2,z3,z325,z92,z5]),(0,[z0,z1,z35,z2,z3,z5,z12]),(0,[z354,z0,z1,z8,z2,z3,z5]),(0,[z543,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z544,z3,z5,z6]),(0,[z0,z1,z2,z3,z92,z114,z6]),(0,[z0,z1,z2,z3,z5,z545,z6]),(0,[z0,z1,z2,z3,z546,z5,z6]),(0,[z0,z1,z17,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z547,z5,z6])],[(1,[z0,z1,z356,z3,z5,z6]),(0,[z0,z1,z2,z548,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z427]),(0,[z0,z1,z2,z3,z23,z5,z129]),(0,[z0,z1,z7,z7,z2,z3,z5])],[(0,[z87,z0,z1,z2,z3,z5,z549]),(0,[z0,z1,z8,z2,z3,z5,z9]),(0,[z0,z1,z2,z3,z23,z5,z44]),(0,[z0,z1,z2,z3,z5,z6,z12])],[(1,[z0,z550,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z551,z6]),(0,[z0,z1,z2,z3,z5,z6,z552]),(0,[z0,z1,z7,z2,z3,z5,z9]),(0,[z0,z1,z2,z161,z3,z5,z12])],[(0,[z0,z1,z2,z3,z5,z553,z6]),(0,[z0,z1,z2,z554,z3,z5,z6]),(0,[z39,z0,z1,z2,z3,z5,z6]),(0,[z0,z115,z1,z2,z3,z5,z427]),(0,[z0,z1,z2,z3,z5,z6,z555]),(0,[z0,z164,z1,z3,z5,z129,z6]),(0,[z0,z1,z118,z8,z2,z3,z5])]],
   [[(0,[z0,z115,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z556,z3,z5,z6]),(1,[z0,z1,z223,z3,z5,z6])],[(0,[z0,z1,z2,z557,z3,z5,z6]),(0,[z0,z1,z175,z3,z30,z5,z6]),(1,[z0,z1,z8,z3,z30,z5]),(0,[z0,z1,z558,z2,z3,z5,z6])],[(0,[z0,z1,z8,z2,z3,z24,z5]),(0,[z0,z1,z7,z2,z3,z5,z137]),(0,[z0,z1,z2,z559,z3,z5,z6]),(0,[z0,z80,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z560,z6]),(0,[z0,z1,z7,z2,z3,z24,z5]),(0,[z0,z1,z2,z175,z3,z5,z184]),(0,[z0,z1,z3,z16,z5,z129,z6]),(0,[z0,z561,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z455]),(0,[z0,z1,z7,z2,z119,z3,z5]),(0,[z0,z232,z1,z2,z3,z23,z5]),(0,[z0,z164,z1,z3,z5,z36,z6])],[(0,[z110,z0,z1,z2,z3,z420,z6]),(0,[z0,z1,z75,z2,z119,z3,z5]),(0,[z0,z562,z1,z2,z3,z5,z6]),(0,[z235,z0,z1,z2,z3,z23,z5])],[(0,[z71,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z563,z6]),(0,[z0,z1,z2,z175,z3,z23,z5]),(0,[z0,z1,z8,z2,z3,z5,z36]),(0,[z0,z1,z7,z2,z3,z451,z5]),(0,[z0,z1,z564,z2,z3,z5,z6])],[(1,[z0,z1,z2,z425,z5,z6]),(0,[z110,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z565,z6]),(1,[z0,z1,z2,z3,z5,z549]),(0,[z0,z1,z566,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z567,z6]),(1,[z0,z1,z2,z399,z5,z6]),(0,[z568,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z7,z2,z3,z5,z36])]],
   [[(0,[z0,z1,z2,z3,z5,z6,z569]),(1,[z21,z1,z2,z3,z5,z78]),(0,[z0,z1,z3,z16,z5,z36,z6]),(0,[z0,z1,z570,z2,z3,z5,z6])],[],[(0,[z0,z1,z2,z3,z5,z6,z571]),(0,[z0,z1,z2,z3,z5,z572,z6]),(0,[z573,z0,z1,z2,z3,z5,z6])],[(1,[z87,z1,z88,z3,z5,z6]),(0,[z574,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z78,z12]),(0,[z0,z1,z575,z2,z3,z5,z6]),(0,[z0,z109,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z576,z6]),(0,[z0,z1,z118,z2,z161,z5,z6]),(0,[z0,z1,z577,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z246,z23,z5])],[(0,[z0,z1,z2,z578,z3,z5,z6]),(0,[z0,z1,z2,z3,z579,z5,z6]),(0,[z0,z409,z1,z8,z2,z3,z5]),(0,[z0,z580,z1,z2,z3,z5,z6]),(1,[z0,z1,z3,z5,z81,z6])],[(0,[z0,z1,z2,z3,z5,z581,z6]),(0,[z582,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z583,z6]),(0,[z0,z584,z1,z2,z3,z5,z6])],[(0,[z110,z0,z1,z2,z3,z5,z455]),(0,[z0,z1,z2,z3,z585,z5,z6]),(0,[z0,z586,z1,z2,z3,z5,z6]),(0,[z0,z1,z587,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z328,z6])],[(1,[z0,z339,z1,z2,z5,z6]),(0,[z0,z588,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z589]),(0,[z0,z66,z1,z2,z3,z5,z193])]],
   [[(0,[z21,z1,z2,z3,z5,z6,z78]),(0,[z0,z1,z8,z2,z3,z5,z73]),(0,[z0,z1,z2,z287,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z590,z5])],[(0,[z87,z0,z1,z2,z3,z5,z489]),(0,[z0,z1,z2,z3,z23,z124,z5]),(0,[z0,z29,z1,z8,z2,z3,z5]),(0,[z0,z1,z267,z2,z3,z23,z5])],[(0,[z79,z0,z1,z118,z2,z3,z5]),(0,[z0,z1,z223,z2,z3,z5,z12])],[(0,[z111,z0,z143,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z591,z6]),(0,[z0,z1,z2,z3,z592,z5,z6]),(0,[z0,z1,z2,z3,z5,z593,z12])],[(0,[z0,z1,z2,z3,z95,z5,z6]),(1,[z0,z1,z2,z594,z5,z6]),(0,[z21,z0,z1,z8,z2,z3,z5]),(0,[z0,z144,z1,z2,z3,z5,z73])],[(0,[z39,z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z595,z2,z3,z5,z6]),(0,[z0,z1,z2,z596,z3,z5,z6]),(0,[z0,z1,z2,z175,z3,z5,z261]),(0,[z0,z1,z2,z3,z5,z597,z6])],[(0,[z0,z1,z2,z598,z3,z5,z6]),(0,[z0,z232,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z15,z5,z6]),(0,[z0,z599,z1,z2,z3,z5,z6])],[(0,[z210,z0,z1,z2,z3,z5,z6]),(0,[z40,z0,z1,z8,z2,z3,z5]),(0,[z0,z600,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z601,z3,z5,z6]),(0,[z0,z1,z602,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z603,z5,z6]),(0,[z0,z434,z1,z8,z2,z3,z5])]],
   [[(0,[z604,z0,z1,z2,z3,z5,z6]),(0,[z111,z0,z1,z2,z3,z23,z5]),(0,[z67,z0,z1,z2,z360,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z318]),(0,[z0,z605,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z73]),(0,[z0,z1,z2,z3,z5,z606,z6]),(0,[z0,z1,z2,z175,z3,z5,z12]),(0,[z0,z1,z17,z85,z2,z3,z5])],[(0,[z0,z29,z1,z2,z3,z5,z408]),(0,[z0,z358,z1,z2,z3,z5,z6]),(0,[z0,z164,z1,z2,z155,z5,z6]),(0,[z0,z1,z7,z2,z3,z16,z5]),(1,[z0,z1,z7,z3,z5,z36]),(0,[z607,z0,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z5,z328,z6])],[(0,[z608,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z609,z2,z3,z5,z6]),(0,[z0,z1,z191,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z16,z5,z6]),(0,[z0,z1,z132,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z610,z6]),(0,[z0,z1,z2,z3,z5,z12,z218]),(0,[z0,z1,z2,z3,z359,z5,z6])],[(1,[z0,z1,z2,z3,z5,z489]),(0,[z0,z1,z611,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z612,z6]),(0,[z26,z0,z1,z350,z3,z5,z6]),(0,[z0,z1,z2,z3,z613,z5,z6]),(0,[z0,z1,z423,z2,z3,z5,z6])],[(0,[z0,z1,z88,z2,z3,z23,z5]),(0,[z71,z0,z1,z7,z2,z3,z5]),(0,[z40,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z614,z2,z3,z5,z6]),(0,[z0,z1,z35,z2,z175,z5,z6]),(0,[z0,z164,z1,z2,z3,z5,z6]),(0,[z0,z66,z1,z8,z2,z3,z5]),(1,[z0,z1,z7,z2,z149,z5]),(0,[z0,z1,z2,z3,z5,z615,z6]),(0,[z0,z1,z2,z3,z5,z6,z593]),(0,[z0,z1,z2,z3,z590,z5,z6])],[(0,[z71,z0,z1,z2,z94,z5,z6]),(0,[z0,z1,z2,z3,z5,z616,z6]),(0,[z0,z1,z2,z3,z5,z617,z6]),(1,[z0,z1,z17,z2,z3,z5]),(0,[z0,z1,z25,z8,z2,z3,z5])],[(0,[z0,z1,z2,z3,z5,z618,z6]),(0,[z67,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z619,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z540]),(0,[z65,z0,z1,z2,z594,z5,z6]),(0,[z0,z1,z2,z3,z592,z30,z6])],[(0,[z0,z620,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z220]),(0,[z0,z97,z232,z2,z3,z5,z6]),(0,[z0,z1,z118,z2,z3,z5,z73]),(0,[z0,z1,z2,z175,z161,z5,z6]),(0,[z0,z66,z1,z423,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z215,z6])]],
   [[(0,[z621,z0,z1,z2,z3,z5,z6]),(0,[z79,z0,z1,z2,z161,z3,z5]),(0,[z0,z1,z2,z3,z23,z5,z6])],[(0,[z0,z550,z1,z2,z3,z5,z6]),(1,[z0,z145,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z622,z5,z6]),(0,[z26,z0,z1,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z5,z623,z6]),(1,[z0,z1,z2,z3,z5,z83])],[(0,[z0,z473,z1,z143,z2,z3,z6]),(0,[z0,z1,z2,z321,z3,z5,z6]),(0,[z0,z338,z1,z2,z3,z5,z6]),(0,[z0,z624,z1,z2,z3,z5,z6]),(0,[z0,z580,z1,z7,z2,z3,z5]),(0,[z0,z1,z25,z2,z3,z5,z12])],[(0,[z0,z1,z625,z2,z3,z5,z6]),(1,[z0,z503,z1,z2,z5,z6])],[(0,[z0,z626,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z94,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z627,z6]),(0,[z0,z66,z1,z2,z3,z5,z369]),(0,[z0,z1,z2,z3,z5,z628,z6]),(0,[z0,z1,z2,z188,z3,z5,z6]),(0,[z0,z1,z2,z3,z47,z5,z6])],[(0,[z0,z1,z2,z3,z629,z5,z6]),(0,[z0,z1,z2,z3,z630,z5,z6]),(0,[z0,z1,z2,z631,z3,z5,z6])],[(1,[z0,z1,z2,z3,z4,z6]),(0,[z0,z1,z2,z3,z5,z6,z632]),(0,[z0,z1,z2,z3,z5,z78,z73]),(0,[z0,z1,z633,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z23,z5])],[(0,[z634,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z3,z5,z6]),(0,[z0,z1,z2,z3,z538,z5,z6]),(0,[z0,z1,z350,z2,z3,z5,z6]),(0,[z0,z1,z7,z2,z3,z23,z5])]],
   [[(0,[z0,z1,z2,z95,z24,z5,z6]),(0,[z0,z66,z1,z2,z94,z5,z6]),(0,[z0,z635,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z114,z12]),(0,[z0,z1,z2,z636,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z637]),(0,[z0,z66,z1,z2,z161,z5,z6])],[(1,[z0,z1,z312,z2,z3,z5]),(0,[z0,z1,z2,z3,z638,z5,z6]),(1,[z0,z1,z85,z3,z16,z6]),(0,[z462,z0,z1,z7,z2,z3,z5])],[(0,[z111,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z639,z2,z3,z5,z6]),(0,[z0,z1,z640,z2,z3,z5,z6]),(0,[z0,z1,z2,z594,z3,z5,z6]),(0,[z641,z0,z1,z2,z3,z5,z6])],[(0,[z0,z550,z1,z143,z2,z3,z6]),(0,[z0,z1,z2,z119,z3,z23,z5]),(0,[z0,z1,z2,z3,z642,z5,z6]),(0,[z0,z643,z1,z2,z3,z5,z6]),(0,[z0,z1,z644,z2,z3,z5,z6]),(0,[z0,z1,z2,z645,z3,z5,z6]),(0,[z0,z1,z2,z171,z43,z5,z6]),(0,[z0,z1,z2,z3,z5,z646,z6])],[(0,[z110,z0,z1,z2,z629,z5,z6]),(0,[z647,z0,z1,z2,z3,z5,z6]),(0,[z0,z648,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z649,z6]),(0,[z0,z650,z1,z2,z3,z5,z6]),(0,[z0,z1,z651,z2,z3,z5,z6])],[(0,[z0,z1,z143,z8,z2,z3,z5]),(0,[z0,z109,z2,z3,z5,z6,z73]),(0,[z0,z1,z2,z3,z5,z6,z314]),(1,[z0,z164,z1,z3,z129,z6]),(1,[z0,z1,z269,z2,z5,z6]),(0,[z0,z1,z296,z2,z3,z5,z12])],[(0,[z0,z1,z88,z2,z3,z5,z12]),(0,[z222,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z350,z2,z652,z5,z6]),(0,[z0,z1,z2,z3,z652,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z653]),(0,[z0,z1,z2,z161,z3,z5,z148]),(0,[z0,z1,z2,z3,z5,z654,z6]),(0,[z0,z1,z655,z2,z3,z5,z6])],[(0,[z656,z0,z1,z2,z3,z5,z6]),(0,[z0,z657,z1,z2,z3,z5,z6]),(0,[z0,z51,z66,z1,z2,z5,z6]),(0,[z0,z1,z123,z8,z2,z3,z5]),(0,[z0,z66,z1,z2,z171,z5,z6])]],
   [[(1,[z0,z1,z2,z629,z5,z6]),(0,[z67,z0,z1,z2,z3,z5,z12]),(0,[z658,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z659,z3,z5,z6]),(1,[z0,z1,z2,z3,z47,z12])],[(0,[z660,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z661,z5,z6]),(0,[z0,z1,z2,z3,z5,z662,z6]),(0,[z0,z1,z8,z2,z3,z5,z78]),(0,[z0,z115,z350,z2,z3,z5,z6]),(0,[z0,z1,z269,z2,z3,z5,z6]),(0,[z0,z1,z2,z663,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z6]),(0,[z111,z19,z1,z2,z3,z5,z6]),(1,[z0,z1,z2,z538,z5,z6]),(0,[z0,z1,z7,z2,z3,z5,z78]),(0,[z664,z0,z1,z2,z3,z5,z6]),(0,[z0,z164,z1,z7,z2,z3,z5]),(0,[z0,z1,z7,z587,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z665,z6])],[(0,[z666,z0,z1,z2,z3,z5,z6]),(0,[z21,z0,z144,z1,z2,z3,z5]),(0,[z26,z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z667,z3,z5,z6]),(0,[z0,z1,z2,z3,z668,z5,z6]),(0,[z0,z1,z2,z3,z5,z93,z129]),(0,[z0,z1,z2,z171,z3,z23,z5])],[(0,[z0,z1,z669,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z148,z22]),(0,[z0,z670,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z30,z5]),(0,[z0,z671,z1,z2,z3,z5,z6]),(0,[z0,z1,z7,z8,z2,z3,z5]),(0,[z0,z1,z386,z2,z3,z5,z6])],[(1,[z0,z1,z385,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z672,z6]),(0,[z0,z1,z8,z2,z2,z3,z5]),(0,[z0,z1,z118,z2,z3,z23,z5])],[(1,[z39,z1,z2,z94,z5,z6]),(0,[z65,z0,z97,z1,z2,z3,z6]),(1,[z0,z1,z2,z3,z5,z337]),(0,[z0,z1,z7,z2,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z6,z673])],[(1,[z111,z19,z2,z3,z5,z6]),(0,[z40,z0,z1,z2,z3,z5,z318]),(0,[z0,z1,z2,z171,z30,z5,z6]),(0,[z0,z674,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z51,z1,z2,z24,z5,z6]),(0,[z0,z1,z2,z675,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z5,z12]),(0,[z676,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z677,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z196,z5,z6])],[(0,[z0,z1,z2,z3,z678,z5,z6]),(0,[z0,z1,z679,z2,z3,z5,z6]),(1,[z0,z1,z2,z652,z5,z6]),(0,[z0,z1,z2,z5,z374,z137,z6]),(0,[z0,z1,z7,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z23,z5,z215]),(0,[z0,z1,z2,z3,z43,z5,z12])],[(0,[z0,z1,z680,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z681,z6]),(0,[z0,z1,z2,z410,z3,z5,z6])],[(0,[z110,z0,z1,z2,z3,z5,z581]),(0,[z0,z1,z312,z2,z3,z95,z5]),(0,[z0,z109,z1,z2,z3,z5,z148]),(0,[z0,z1,z2,z3,z682,z5,z6])],[(0,[z0,z1,z2,z3,z5,z6,z549]),(0,[z65,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z5,z137]),(0,[z0,z1,z123,z35,z3,z5,z6]),(0,[z0,z1,z2,z683,z3,z5,z6])],[(0,[z0,z1,z2,z119,z3,z5,z12]),(0,[z0,z2,z52,z3,z24,z5,z6]),(0,[z0,z684,z1,z2,z3,z5,z6]),(0,[z0,z1,z8,z368,z2,z3,z5]),(0,[z0,z1,z7,z2,z227,z5,z6])],[(0,[z0,z1,z8,z2,z3,z95,z5]),(0,[z65,z0,z232,z1,z2,z3,z6]),(0,[z0,z164,z1,z2,z171,z3,z6]),(1,[z0,z1,z487,z3,z5,z6]),(0,[z0,z1,z685,z2,z3,z5,z6])],[(1,[z0,z1,z2,z3,z5,z581]),(0,[z79,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z148,z78]),(0,[z0,z29,z1,z2,z43,z5,z6]),(1,[z0,z1,z2,z3,z592,z6]),(0,[z0,z1,z2,z3,z5,z6,z686]),(0,[z687,z0,z1,z2,z3,z5,z6])]],
   [[(0,[z0,z1,z688,z2,z3,z5,z6]),(0,[z0,z1,z2,z52,z95,z5,z6]),(0,[z0,z1,z2,z161,z3,z5,z218])],[(0,[z0,z1,z2,z689,z3,z5,z6]),(1,[z65,z1,z2,z3,z124,z6]),(0,[z0,z1,z2,z3,z690,z5,z6]),(0,[z0,z1,z2,z3,z691,z5,z6]),(1,[z0,z1,z230,z2,z3,z5]),(0,[z0,z1,z2,z3,z92,z5,z12]),(0,[z0,z1,z692,z2,z3,z5,z6]),(0,[z693,z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z23,z5,z36]),(0,[z0,z1,z2,z3,z5,z6,z694]),(0,[z419,z0,z1,z2,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z5,z6]),(0,[z0,z695,z1,z2,z3,z5,z6]),(0,[z0,z696,z1,z2,z3,z5,z6]),(0,[z0,z51,z2,z3,z24,z5,z6]),(0,[z0,z97,z1,z2,z3,z5,z64]),(1,[z0,z232,z2,z3,z92,z6]),(0,[z0,z1,z2,z175,z5,z44,z6]),(1,[z0,z1,z7,z8,z3,z5]),(0,[z0,z1,z8,z2,z3,z43,z5])],[(0,[z0,z697,z1,z2,z3,z5,z6]),(0,[z79,z21,z1,z2,z3,z5,z6]),(0,[z0,z1,z206,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z698]),(0,[z0,z1,z7,z2,z3,z43,z5])],[(0,[z0,z1,z2,z94,z3,z5,z6]),(0,[z0,z1,z2,z3,z114,z137,z6]),(0,[z0,z1,z230,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z6,z699]),(0,[z0,z1,z35,z175,z3,z5,z6])],[(0,[z0,z700,z1,z2,z3,z5,z6]),(0,[z0,z701,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z702,z3,z5,z6]),(0,[z0,z1,z2,z3,z30,z5,z12]),(0,[z0,z1,z2,z3,z703,z5,z6]),(1,[z0,z1,z35,z175,z5,z6]),(1,[z0,z1,z2,z3,z5,z217]),(0,[z0,z1,z2,z271,z3,z5,z6]),(0,[z0,z1,z2,z171,z3,z5,z12]),(0,[z0,z1,z2,z161,z3,z5,z44])],[(0,[z110,z0,z1,z2,z425,z5,z6]),(0,[z0,z1,z2,z3,z5,z148,z12]),(0,[z0,z704,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z171,z3,z43,z6])],[(0,[z0,z29,z1,z2,z3,z23,z5]),(0,[z0,z1,z35,z3,z5,z129,z6]),(0,[z0,z1,z2,z705,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z706,z6]),(0,[z0,z1,z118,z2,z3,z5,z12])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z5,z707]),(0,[z0,z145,z1,z2,z3,z5]),(0,[z0,z45,z1,z7,z2,z5]),(0,[z87,z0,z1,z223,z3,z5]),(0,[z708,z1,z2,z3,z5,z6]),(0,[z0,z1,z35,z8,z30,z5]),(0,[z0,z1,z8,z3,z5,z81]),(0,[z0,z1,z709,z2,z3,z5])],[(0,[z0,z1,z101,z7,z3,z5]),(0,[z0,z29,z2,z52,z5,z6]),(0,[z0,z1,z2,z3,z710,z5])],[(0,[z26,z0,z285,z3,z5,z6]),(0,[z67,z1,z119,z360,z5,z6]),(0,[z0,z503,z1,z2,z5,z6]),(0,[z0,z1,z296,z2,z5,z328])],[(0,[z0,z1,z711,z3,z5,z6]),(0,[z0,z1,z2,z712,z3,z6]),(0,[z713,z1,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z5,z374]),(1,[z0,z2,z3,z5,z714])],[(0,[z0,z1,z2,z3,z5,z715]),(0,[z0,z1,z2,z3,z716,z5]),(0,[z0,z1,z2,z3,z717,z5]),(0,[z0,z1,z2,z11,z5,z148])],[(0,[z0,z232,z1,z223,z3,z5]),(0,[z0,z1,z718,z3,z23,z5])],[(0,[z110,z143,z2,z3,z420,z6]),(0,[z0,z51,z1,z487,z5,z6]),(0,[z0,z1,z2,z719,z5,z6]),(0,[z0,z66,z1,z2,z215,z193])],[(0,[z110,z143,z415,z3,z5,z6]),(0,[z0,z1,z720,z2,z5,z6]),(0,[z0,z1,z85,z171,z30,z6])],[(0,[z0,z1,z2,z3,z721,z6]),(0,[z67,z1,z119,z3,z23,z5]),(0,[z0,z29,z2,z630,z5,z6]),(0,[z0,z1,z2,z3,z722,z5]),(0,[z0,z311,z2,z3,z5,z148]),(0,[z0,z1,z85,z3,z16,z6])],[(0,[z0,z723,z2,z3,z5,z6]),(0,[z0,z1,z2,z380,z43,z6]),(0,[z0,z164,z1,z155,z129,z6])],[(0,[z110,z0,z1,z223,z3,z5]),(0,[z0,z1,z724,z2,z3,z5]),(0,[z0,z1,z7,z2,z725,z5]),(0,[z0,z1,z726,z3,z5,z12])],[(0,[z0,z1,z2,z3,z727,z6]),(0,[z0,z1,z2,z3,z5,z728]),(0,[z0,z1,z2,z68,z23,z5]),(0,[z0,z1,z8,z2,z171,z43]),(0,[z0,z1,z2,z171,z23,z43])],[(0,[z0,z1,z2,z729,z5,z6]),(0,[z0,z1,z2,z730,z5,z6]),(0,[z0,z1,z11,z5,z81,z12])],[(0,[z0,z1,z2,z3,z5,z731]),(0,[z0,z1,z143,z223,z3,z5]),(0,[z0,z732,z1,z2,z3,z6]),(0,[z0,z1,z733,z2,z3,z5]),(0,[z0,z1,z30,z5,z567,z6])],[(0,[z0,z1,z2,z734,z5,z6]),(0,[z0,z1,z2,z3,z5,z735]),(0,[z21,z0,z1,z177,z3,z5]),(0,[z0,z164,z1,z8,z3,z337]),(0,[z0,z1,z2,z3,z5,z736]),(0,[z0,z1,z2,z3,z23,z583])],[(0,[z110,z143,z2,z3,z5,z455]),(0,[z0,z1,z2,z5,z44,z184]),(0,[z0,z1,z737,z3,z5,z250])]],
   [[(0,[z0,z1,z602,z30,z5,z6]),(0,[z0,z1,z7,z35,z175,z5]),(0,[z0,z1,z118,z223,z3,z5])],[(0,[z0,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z738,z5,z6]),(0,[z0,z1,z2,z3,z739,z6]),(0,[z0,z1,z2,z3,z5,z740]),(0,[z0,z1,z2,z5,z741,z6]),(0,[z0,z1,z2,z742,z5,z12])],[(0,[z0,z1,z123,z30,z5,z12]),(0,[z0,z1,z743,z2,z3,z5]),(0,[z0,z1,z223,z3,z16,z5]),(0,[z0,z1,z118,z2,z5,z741])],[(0,[z0,z1,z2,z3,z744,z6]),(0,[z0,z1,z2,z321,z43,z5]),(0,[z0,z1,z8,z188,z3,z5]),(0,[z0,z1,z223,z3,z5,z81]),(0,[z0,z1,z745,z3,z5,z12])],[(0,[z0,z1,z385,z2,z3,z5]),(0,[z0,z97,z595,z2,z3,z6]),(0,[z0,z1,z206,z2,z3,z5])],[(0,[z210,z0,z1,z3,z5,z6]),(0,[z0,z1,z2,z746,z5,z6]),(0,[z1,z2,z3,z747,z5,z6]),(0,[z0,z164,z1,z8,z399,z5])],[(0,[z748,z210,z0,z1,z3,z5]),(0,[z0,z1,z749,z2,z360,z5]),(0,[z0,z1,z8,z2,z497,z5]),(0,[z0,z1,z267,z3,z5,z129])],[(0,[z0,z232,z1,z2,z3,z337]),(0,[z0,z226,z1,z8,z3,z6]),(0,[z251,z0,z1,z223,z3,z5])],[(0,[z0,z1,z2,z3,z5,z750]),(0,[z0,z1,z8,z139,z3,z5]),(0,[z0,z1,z2,z652,z5,z6]),(0,[z0,z97,z2,z3,z137,z64]),(0,[z0,z503,z1,z7,z2,z5])],[(0,[z0,z1,z751,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z752]),(0,[z0,z753,z1,z2,z3,z5])],[(0,[z0,z1,z248,z188,z3,z5]),(0,[z0,z1,z7,z2,z754,z5]),(0,[z0,z1,z755,z423,z3,z5])],[(0,[z65,z1,z2,z3,z371,z124]),(0,[z0,z226,z1,z2,z3,z23])],[(0,[z0,z1,z756,z3,z5,z6]),(0,[z0,z1,z35,z5,z610,z6]),(0,[z0,z1,z367,z8,z3,z5]),(0,[z0,z1,z2,z5,z757,z12]),(0,[z0,z1,z2,z5,z758,z12])],[(0,[z0,z1,z759,z3,z5,z6]),(0,[z0,z1,z760,z3,z5,z6]),(0,[z0,z115,z8,z350,z3,z5]),(0,[z0,z1,z2,z3,z761,z6]),(0,[z0,z1,z248,z8,z3,z5])],[(0,[z65,z1,z2,z3,z23,z124]),(0,[z0,z1,z3,z5,z762,z6])],[(0,[z0,z1,z2,z497,z5,z12]),(0,[z0,z1,z7,z2,z763,z5])]],
   [[(0,[z0,z1,z2,z3,z764,z6]),(0,[z0,z2,z3,z5,z765,z6])],[(0,[z210,z0,z1,z7,z3,z5]),(0,[z0,z1,z766,z2,z3,z6]),(0,[z0,z1,z2,z767,z5,z12])],[(0,[z0,z1,z2,z768,z5,z6]),(0,[z39,z504,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z769]),(0,[z0,z1,z2,z770,z5,z12])],[(0,[z192,z1,z2,z94,z5,z6]),(0,[z0,z1,z248,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z250])],[(0,[z0,z20,z1,z101,z3,z5]),(0,[z0,z29,z2,z771,z5,z6]),(0,[z0,z1,z2,z3,z23,z58]),(0,[z0,z1,z772,z223,z3,z5])],[(0,[z0,z1,z2,z360,z5,z12]),(0,[z0,z1,z2,z773,z5,z6]),(0,[z0,z1,z8,z2,z774,z5])],[(0,[z0,z1,z2,z3,z775,z5]),(0,[z0,z1,z177,z3,z5,z218])],[(0,[z0,z1,z2,z3,z5,z776]),(0,[z0,z1,z2,z3,z710,z592]),(0,[z0,z1,z8,z3,z5,z9]),(0,[z1,z2,z3,z5,z12,z777])],[(0,[z0,z1,z778,z2,z3,z5]),(0,[z0,z1,z248,z123,z30,z5]),(0,[z0,z1,z2,z3,z779,z5])],[],[(0,[z0,z226,z1,z8,z3,z30])],[(0,[z87,z1,z88,z3,z23,z5]),(0,[z0,z1,z177,z3,z5,z44])],[(0,[z0,z1,z2,z3,z5,z780]),(0,[z0,z1,z2,z3,z781,z6]),(0,[z0,z1,z2,z782,z5,z6]),(0,[z0,z1,z2,z161,z98,z5])],[(0,[z40,z1,z2,z3,z23,z114]),(0,[z0,z1,z2,z3,z783,z5])],[(0,[z0,z1,z356,z3,z5,z12]),(0,[z0,z1,z2,z3,z420,z784]),(0,[z0,z1,z2,z785,z360,z5]),(0,[z0,z1,z2,z786,z5,z6]),(0,[z0,z1,z2,z3,z5,z787]),(0,[z0,z1,z2,z3,z5,z788]),(0,[z0,z1,z2,z3,z789,z5]),(0,[z260,z0,z1,z8,z3,z5])],[(0,[z221,z1,z2,z95,z5,z6]),(0,[z0,z1,z223,z2,z3,z5]),(0,[z0,z164,z1,z8,z3,z37]),(0,[z0,z1,z790,z2,z23,z5])]],
   [[(0,[z0,z1,z2,z3,z791,z6]),(0,[z0,z1,z639,z8,z3,z5]),(0,[z0,z1,z8,z2,z538,z5]),(0,[z0,z1,z792,z3,z5,z6])],[(0,[z26,z0,z230,z27,z3,z5]),(0,[z0,z97,z8,z2,z3,z137]),(0,[z0,z1,z2,z3,z5,z793]),(0,[z0,z1,z2,z794,z5,z6]),(0,[z0,z164,z66,z1,z8,z3]),(0,[z0,z80,z2,z3,z5,z316])],[(0,[z0,z795,z2,z3,z5,z6]),(0,[z0,z1,z8,z3,z682,z5]),(0,[z0,z1,z223,z3,z5,z12])],[(0,[z0,z164,z1,z3,z337,z6])],[(0,[z0,z1,z796,z2,z5,z6]),(0,[z0,z1,z75,z2,z3,z5]),(0,[z0,z1,z487,z94,z5,z6]),(0,[z0,z1,z8,z2,z652,z5]),(0,[z0,z66,z1,z2,z28,z6]),(0,[z0,z1,z2,z797,z5,z6]),(0,[z0,z1,z123,z798,z5,z6]),(0,[z0,z1,z8,z423,z3,z5])],[(0,[z210,z0,z473,z1,z3,z6]),(0,[z0,z1,z2,z3,z5,z799]),(0,[z0,z1,z2,z23,z5,z374]),(0,[z0,z1,z2,z5,z32,z6]),(0,[z0,z1,z800,z3,z23,z5])],[(0,[z0,z1,z2,z801,z5,z6]),(0,[z0,z1,z2,z3,z802,z5]),(0,[z0,z1,z2,z3,z5,z803]),(0,[z0,z1,z2,z3,z5,z804]),(0,[z0,z1,z7,z3,z5,z628])],[(0,[z0,z1,z805,z2,z3,z5]),(0,[z0,z1,z3,z5,z806,z6]),(0,[z0,z1,z2,z807,z5,z6]),(0,[z0,z1,z8,z2,z155,z5])],[(0,[z0,z1,z101,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z808]),(0,[z26,z0,z7,z27,z3,z5]),(0,[z0,z226,z1,z2,z155,z6]),(0,[z0,z1,z2,z5,z809,z6]),(0,[z0,z1,z227,z5,z36,z6])],[(0,[z0,z339,z20,z1,z2,z5]),(0,[z0,z1,z2,z3,z5,z108]),(0,[z0,z1,z810,z3,z5,z6]),(0,[z0,z1,z811,z2,z3,z5]),(0,[z0,z66,z1,z487,z215,z6])],[(0,[z1,z88,z812,z3,z5,z6]),(0,[z40,z1,z8,z2,z3,z114]),(0,[z0,z1,z2,z3,z5,z813]),(0,[z0,z156,z1,z2,z3,z337]),(0,[z0,z1,z2,z149,z5,z218])],[(0,[z0,z1,z2,z3,z420,z12]),(0,[z0,z1,z814,z2,z3,z5]),(1,[z1,z2,z3,z5,z815]),(0,[z0,z1,z816,z3,z5,z6]),(0,[z0,z29,z1,z487,z5,z6]),(0,[z0,z1,z2,z3,z323,z12]),(0,[z0,z1,z817,z3,z5,z12])],[(0,[z110,z143,z356,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z818]),(0,[z0,z819,z1,z2,z3,z6]),(0,[z0,z109,z2,z3,z196,z5]),(0,[z0,z1,z223,z3,z43,z5])],[(0,[z0,z1,z2,z321,z3,z5]),(0,[z0,z1,z2,z3,z242,z12]),(0,[z0,z1,z2,z3,z535,z12]),(0,[z0,z1,z209,z386,z2,z5])],[(0,[z0,z1,z820,z2,z3,z5]),(0,[z0,z1,z2,z11,z5,z6])],[(0,[z71,z1,z312,z2,z95,z5]),(0,[z0,z1,z223,z3,z24,z5]),(0,[z0,z1,z2,z149,z5,z44])]],
   [[(0,[z0,z1,z101,z3,z5,z752]),(0,[z0,z1,z2,z3,z5,z821])],[(0,[z0,z1,z2,z3,z5,z822]),(0,[z0,z1,z8,z171,z30,z5])],[(0,[z67,z1,z812,z3,z5,z6])],[(0,[z0,z1,z299,z30,z5,z6]),(0,[z0,z1,z2,z161,z5,z218])],[(0,[z1,z2,z746,z3,z5,z6]),(0,[z0,z1,z348,z30,z5,z6])],[(0,[z0,z51,z1,z223,z3,z5]),(0,[z0,z1,z2,z3,z5,z714]),(0,[z0,z1,z2,z399,z5,z216]),(0,[z0,z164,z1,z223,z3,z5]),(0,[z0,z823,z1,z2,z5,z337]),(0,[z0,z1,z755,z2,z3,z5])],[(0,[z0,z1,z2,z824,z3,z5]),(0,[z0,z1,z7,z2,z360,z5]),(0,[z0,z66,z1,z2,z317,z6]),(0,[z0,z1,z2,z594,z5,z12]),(0,[z0,z1,z825,z3,z5,z6])],[(0,[z110,z143,z2,z425,z5,z6]),(0,[z0,z1,z2,z826,z5,z6]),(0,[z0,z1,z2,z3,z5,z827]),(0,[z0,z430,z2,z3,z5,z73])],[(0,[z0,z1,z2,z828,z5,z6]),(0,[z0,z140,z2,z3,z92,z6]),(0,[z0,z1,z2,z3,z5,z829]),(0,[z0,z1,z2,z3,z5,z830]),(0,[z0,z1,z299,z8,z3,z5]),(0,[z0,z1,z8,z3,z5,z831]),(0,[z0,z1,z118,z177,z5,z44])],[(0,[z40,z1,z2,z3,z114,z6]),(0,[z0,z1,z3,z30,z5,z93])],[(0,[z0,z1,z2,z3,z5,z832])],[(0,[z0,z1,z2,z3,z5,z833]),(0,[z0,z1,z85,z3,z762,z6]),(0,[z0,z1,z2,z5,z328,z12])],[(0,[z0,z1,z7,z356,z3,z5]),(0,[z834,z143,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z835,z5]),(0,[z1,z2,z3,z5,z6,z777]),(0,[z0,z2,z3,z5,z6,z714])],[(0,[z0,z473,z1,z2,z3,z836]),(0,[z0,z1,z2,z5,z837,z6]),(0,[z0,z1,z7,z122,z3,z5]),(0,[z0,z1,z269,z2,z23,z5]),(0,[z0,z1,z838,z2,z3,z5]),(0,[z0,z1,z8,z2,z11,z5]),(0,[z0,z1,z2,z763,z5,z12])],[(0,[z0,z1,z839,z2,z3,z5])],[(0,[z0,z1,z2,z840,z5,z6]),(0,[z0,z1,z2,z3,z371,z5]),(0,[z0,z1,z2,z3,z5,z184]),(0,[z0,z1,z2,z3,z182,z5]),(0,[z0,z1,z133,z2,z763,z5]),(0,[z0,z1,z2,z841,z23,z5])]],
   [[(0,[z0,z1,z2,z629,z23,z5]),(0,[z0,z226,z1,z2,z94,z6]),(0,[z0,z1,z2,z5,z842,z6]),(0,[z0,z1,z843,z2,z3,z5]),(0,[z0,z1,z844,z2,z3,z5]),(0,[z0,z1,z3,z798,z5,z6])],[(0,[z0,z1,z845,z2,z3,z5]),(0,[z0,z1,z2,z3,z846,z6]),(0,[z0,z1,z8,z335,z3,z5]),(0,[z0,z1,z8,z3,z336,z5]),(0,[z429,z0,z132,z2,z3,z5])],[(0,[z0,z1,z2,z847,z5,z6])],[(0,[z0,z1,z2,z3,z848,z6]),(0,[z0,z1,z849,z2,z3,z5]),(0,[z0,z1,z679,z2,z3,z23]),(0,[z0,z1,z850,z2,z3,z5])],[(0,[z0,z1,z2,z3,z851,z4]),(0,[z0,z852,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z853]),(0,[z0,z1,z8,z854,z3,z5]),(0,[z0,z1,z855,z2,z3,z592]),(0,[z0,z1,z2,z3,z5,z856])],[(0,[z0,z115,z350,z3,z23,z5]),(0,[z0,z1,z2,z3,z5,z857]),(0,[z351,z0,z1,z2,z3,z242])],[(0,[z0,z1,z2,z858,z5,z6])],[(0,[z0,z1,z859,z3,z5,z6]),(0,[z0,z164,z1,z2,z3,z337]),(0,[z0,z723,z8,z2,z3,z5])],[],[(0,[z0,z19,z1,z223,z3,z5]),(0,[z0,z1,z2,z860,z5,z6])],[],[(0,[z0,z1,z2,z3,z861,z6]),(0,[z0,z1,z639,z175,z5,z6]),(0,[z0,z1,z2,z3,z5,z862]),(0,[z0,z1,z17,z2,z3,z37]),(0,[z0,z1,z267,z3,z5,z36]),(0,[z0,z66,z1,z2,z215,z12]),(1,[z0,z1,z2,z3,z783]),(0,[z0,z1,z223,z223,z3,z5])],[(0,[z0,z1,z8,z2,z629,z5]),(0,[z79,z1,z677,z2,z3,z5]),(0,[z0,z226,z1,z3,z129,z6]),(0,[z0,z1,z3,z5,z863,z12])],[(0,[z0,z1,z223,z52,z3,z5])],[(0,[z71,z1,z7,z2,z95,z5]),(0,[z0,z29,z7,z2,z52,z5]),(0,[z0,z1,z132,z2,z149,z5]),(0,[z0,z1,z487,z3,z5,z193])],[(0,[z0,z1,z8,z2,z3,z5]),(0,[z1,z834,z2,z3,z5,z6]),(0,[z0,z864,z1,z2,z5,z6])]],
   [[(0,[z0,z1,z2,z629,z420,z6]),(1,[z1,z2,z3,z865,z6]),(0,[z0,z1,z2,z3,z5,z866]),(0,[z0,z226,z1,z2,z3,z6]),(0,[z0,z1,z223,z2,z11,z5])],[(0,[z0,z1,z415,z629,z5,z6]),(0,[z0,z1,z2,z3,z5,z261]),(0,[z0,z226,z1,z3,z36,z6]),(0,[z0,z1,z25,z223,z3,z5])],[(0,[z0,z1,z3,z5,z867,z6]),(0,[z0,z1,z2,z3,z5,z868]),(0,[z0,z1,z2,z869,z5,z6]),(0,[z0,z1,z870,z2,z3,z5]),(0,[z0,z1,z267,z85,z3,z5])],[(0,[z0,z1,z415,z3,z5,z6]),(0,[z0,z1,z8,z2,z3,z420]),(0,[z0,z1,z2,z3,z76,z12]),(0,[z0,z1,z3,z47,z81,z12])],[(0,[z0,z145,z45,z1,z2,z5]),(0,[z0,z871,z1,z2,z3,z5]),(0,[z0,z1,z2,z538,z5,z12]),(0,[z0,z1,z2,z5,z872,z6]),(1,[z0,z1,z737,z3,z5])],[(1,[z1,z812,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z873]),(0,[z0,z434,z1,z30,z5,z6]),(0,[z0,z226,z1,z123,z30,z6]),(0,[z0,z1,z8,z3,z5,z698])],[(0,[z110,z143,z2,z3,z4,z6]),(0,[z0,z1,z2,z23,z652,z5]),(0,[z0,z1,z8,z227,z5,z6])],[(0,[z0,z97,z2,z3,z23,z137]),(0,[z0,z1,z2,z3,z5,z369]),(0,[z0,z1,z188,z161,z5,z6])],[(0,[z0,z834,z2,z3,z5,z6]),(0,[z0,z874,z1,z2,z5,z6]),(0,[z39,z1,z2,z94,z5,z12])],[(0,[z0,z1,z2,z875,z5,z6]),(0,[z0,z1,z2,z629,z5,z455]),(0,[z111,z19,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z876]),(0,[z87,z1,z812,z3,z5,z6]),(0,[z0,z1,z35,z798,z5,z6]),(0,[z0,z1,z2,z399,z5,z314])],[(0,[z1,z2,z3,z124,z865,z6]),(0,[z0,z1,z2,z399,z23,z5]),(0,[z0,z1,z8,z3,z5,z681])],[(0,[z0,z339,z145,z1,z2,z5])],[(0,[z0,z1,z2,z3,z877,z6]),(0,[z0,z1,z7,z2,z5,z32])],[(0,[z0,z1,z8,z30,z5,z215]),(1,[z0,z164,z1,z3,z337]),(0,[z0,z1,z17,z85,z3,z16])],[(0,[z0,z45,z1,z2,z23,z5]),(0,[z0,z1,z2,z3,z878,z5]),(0,[z0,z1,z8,z3,z155,z5])],[(0,[z0,z1,z2,z3,z420,z581]),(0,[z210,z0,z45,z1,z5,z6]),(0,[z0,z1,z8,z2,z227,z5])]],
   [[(0,[z0,z1,z415,z3,z5,z581]),(0,[z0,z1,z2,z3,z5,z879]),(0,[z0,z1,z2,z3,z880,z5]),(0,[z0,z1,z2,z3,z881,z5]),(0,[z0,z1,z35,z3,z5,z337]),(0,[z0,z1,z2,z3,z5,z216]),(0,[z0,z1,z487,z3,z5,z12]),(0,[z0,z1,z2,z47,z328,z12])],[(0,[z0,z1,z882,z3,z5,z6]),(0,[z110,z473,z143,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z883]),(0,[z0,z1,z2,z3,z592,z12])],[(0,[z0,z339,z1,z2,z23,z5]),(0,[z87,z1,z8,z88,z3,z5]),(0,[z0,z1,z2,z3,z300,z12]),(0,[z0,z1,z884,z3,z5,z6])],[(0,[z0,z473,z1,z8,z2,z3]),(0,[z0,z1,z2,z3,z5,z885]),(0,[z65,z1,z2,z3,z124,z12]),(0,[z0,z886,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z887]),(0,[z235,z1,z2,z3,z359,z5])],[(0,[z0,z888,z1,z2,z5,z6]),(0,[z0,z1,z889,z3,z5,z6]),(0,[z0,z1,z726,z3,z5,z6]),(0,[z0,z1,z123,z487,z5,z6])],[(0,[z0,z1,z2,z3,z182,z592])],[(0,[z0,z1,z2,z3,z890,z5]),(0,[z0,z1,z891,z2,z3,z5]),(0,[z0,z1,z248,z2,z227,z5]),(0,[z0,z1,z892,z2,z3,z6]),(0,[z0,z1,z2,z5,z893,z6]),(0,[z0,z1,z11,z5,z81,z6])],[(0,[z0,z1,z894,z2,z3,z5]),(0,[z895,z1,z2,z3,z5,z6]),(0,[z0,z1,z35,z175,z5,z12]),(0,[z0,z164,z1,z3,z93,z129]),(0,[z0,z1,z8,z3,z5,z424]),(0,[z0,z1,z896,z487,z3,z5]),(0,[z0,z1,z487,z161,z5,z6]),(0,[z0,z66,z1,z299,z2,z6])],[(0,[z0,z897,z1,z2,z3,z5]),(0,[z0,z1,z2,z898,z5,z6]),(0,[z0,z1,z2,z899,z5,z6]),(0,[z0,z1,z2,z3,z84,z12]),(0,[z0,z1,z223,z3,z5,z129]),(0,[z0,z1,z7,z177,z3,z5])],[(0,[z0,z1,z900,z2,z3,z5]),(0,[z0,z1,z2,z901,z5,z6]),(0,[z0,z1,z902,z3,z5,z6])],[(0,[z0,z1,z2,z903,z5,z6]),(0,[z0,z1,z904,z2,z3,z5]),(0,[z71,z1,z2,z746,z5,z6]),(0,[z0,z29,z1,z223,z3,z5]),(0,[z0,z1,z2,z3,z905,z6])],[(0,[z0,z1,z2,z906,z3,z5]),(0,[z0,z1,z2,z742,z5,z6])],[(0,[z0,z1,z2,z425,z5,z12]),(0,[z0,z1,z2,z5,z907,z6]),(0,[z87,z1,z88,z3,z5,z549]),(0,[z0,z2,z3,z5,z908,z6]),(0,[z288,z1,z2,z3,z124,z6]),(0,[z0,z51,z2,z24,z23,z5]),(0,[z0,z1,z123,z30,z5,z6]),(0,[z0,z226,z1,z2,z215,z6]),(0,[z0,z1,z3,z5,z36,z314]),(0,[z0,z1,z909,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z910])],[(0,[z0,z1,z2,z911,z5,z6]),(0,[z0,z1,z2,z3,z5,z912]),(0,[z0,z1,z745,z3,z5,z6]),(0,[z0,z1,z25,z2,z3,z783])],[(0,[z0,z1,z2,z3,z5,z913]),(0,[z39,z1,z7,z2,z94,z5])],[(0,[z0,z1,z2,z3,z5,z914]),(0,[z0,z1,z2,z43,z204,z6])]],
   [[],[(0,[z0,z1,z2,z3,z5,z915]),(0,[z0,z1,z2,z3,z325,z5]),(0,[z0,z66,z1,z2,z155,z6]),(0,[z0,z1,z916,z2,z3,z5]),(0,[z0,z1,z3,z5,z81,z12])],[(0,[z0,z917,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z918,z6]),(0,[z0,z1,z296,z223,z3,z5])],[(0,[z0,z1,z919,z2,z3,z5]),(0,[z0,z164,z1,z487,z3,z6]),(0,[z0,z1,z3,z16,z5,z920])],[(0,[z0,z1,z2,z921,z5,z6]),(0,[z79,z1,z2,z3,z5,z86]),(0,[z0,z29,z2,z52,z23,z5]),(0,[z0,z1,z8,z2,z3,z592]),(0,[z0,z226,z1,z2,z3,z804])],[(0,[z0,z1,z2,z3,z922,z5]),(0,[z0,z1,z923,z2,z3,z5]),(0,[z0,z1,z2,z5,z757,z6]),(0,[z0,z503,z1,z2,z23,z5]),(0,[z0,z1,z2,z5,z758,z6])],[(0,[z1,z2,z812,z3,z5,z6]),(0,[z0,z1,z7,z2,z924,z5]),(0,[z0,z1,z925,z3,z5,z6])],[(0,[z110,z143,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z926])],[(0,[z0,z1,z2,z3,z927,z5]),(0,[z0,z1,z928,z2,z538,z5]),(0,[z0,z1,z2,z497,z5,z6]),(0,[z0,z1,z929,z2,z3,z5]),(0,[z0,z2,z3,z92,z765,z6]),(0,[z0,z1,z8,z3,z547,z5])],[(0,[z0,z1,z2,z3,z922,z420]),(0,[z0,z1,z8,z95,z30,z5]),(0,[z0,z1,z8,z3,z516,z5]),(0,[z0,z1,z7,z3,z5,z383]),(0,[z79,z439,z1,z2,z3,z5]),(0,[z0,z1,z930,z3,z5,z6])],[(0,[z0,z1,z8,z223,z3,z5]),(0,[z0,z1,z8,z2,z931,z5])],[(0,[z0,z1,z2,z770,z5,z6]),(0,[z0,z1,z2,z3,z307,z12]),(0,[z0,z115,z350,z497,z5,z6]),(0,[z0,z1,z248,z2,z3,z592]),(0,[z0,z1,z35,z8,z43,z5])],[(0,[z0,z1,z223,z3,z124,z5])],[(0,[z0,z1,z2,z932,z5,z6]),(0,[z110,z550,z143,z2,z3,z6]),(0,[z0,z1,z267,z17,z3,z5]),(0,[z0,z580,z191,z2,z3,z5])],[(0,[z0,z1,z2,z360,z5,z6]),(0,[z39,z0,z1,z223,z3,z5]),(0,[z0,z66,z1,z8,z2,z215]),(0,[z0,z1,z7,z2,z5,z328])]],
   [[(0,[z0,z1,z845,z415,z3,z5]),(0,[z0,z550,z1,z8,z2,z3]),(0,[z0,z1,z2,z3,z5,z933]),(0,[z87,z1,z88,z3,z5,z489]),(0,[z0,z1,z934,z2,z3,z5]),(0,[z0,z1,z3,z5,z831,z9])],[(0,[z0,z51,z226,z1,z2,z6]),(0,[z0,z1,z2,z5,z935,z6]),(0,[z0,z232,z8,z2,z3,z92]),(0,[z0,z1,z133,z2,z3,z451])],[(0,[z936,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z937]),(0,[z0,z2,z3,z765,z137,z6]),(0,[z0,z1,z2,z3,z5,z920])],[(0,[z0,z1,z2,z3,z938,z6]),(0,[z0,z939,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z23,z172]),(0,[z0,z1,z223,z11,z3,z5])],[(0,[z0,z940,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z314])],[(0,[z0,z1,z2,z3,z23,z5]),(0,[z0,z941,z1,z2,z3,z5]),(0,[z87,z1,z680,z3,z5,z6]),(0,[z0,z1,z533,z8,z3,z5]),(0,[z0,z2,z3,z5,z148,z714]),(0,[z0,z823,z1,z8,z2,z5])],[(0,[z0,z1,z356,z629,z5,z6]),(0,[z0,z1,z2,z3,z942,z6]),(0,[z0,z232,z640,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z943])],[(0,[z0,z944,z1,z3,z5,z6]),(0,[z0,z1,z2,z945,z5,z6]),(0,[z0,z1,z946,z2,z3,z5]),(0,[z0,z1,z2,z947,z5,z6]),(0,[z0,z1,z2,z3,z783,z47])],[(0,[z0,z1,z356,z3,z5,z6]),(0,[z0,z1,z85,z155,z5,z6])],[(0,[z0,z1,z2,z3,z23,z420]),(0,[z210,z0,z1,z3,z23,z5]),(0,[z210,z0,z20,z1,z3,z5]),(0,[z0,z1,z8,z2,z3,z948])],[(0,[z0,z1,z7,z596,z3,z5]),(0,[z0,z1,z487,z5,z44,z6]),(0,[z0,z66,z1,z423,z215,z6]),(0,[z0,z1,z223,z3,z47,z12])],[(0,[z0,z1,z7,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z12]),(0,[z110,z45,z143,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z949]),(0,[z0,z1,z2,z3,z5,z950]),(0,[z0,z1,z7,z487,z3,z5])],[(0,[z0,z29,z2,z5,z390,z6]),(0,[z0,z1,z223,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z208]),(0,[z0,z1,z2,z3,z5,z951]),(0,[z0,z1,z952,z3,z5,z12])],[(0,[z0,z1,z953,z3,z5,z6]),(0,[z0,z1,z2,z161,z5,z328])],[(0,[z0,z1,z8,z415,z3,z5]),(0,[z0,z1,z2,z3,z5,z836]),(0,[z0,z1,z2,z3,z954,z5]),(0,[z0,z1,z2,z3,z5,z955]),(0,[z0,z1,z3,z5,z956,z6]),(0,[z0,z1,z2,z410,z279,z5])],[(0,[z110,z339,z143,z2,z5,z6]),(0,[z0,z1,z957,z2,z3,z5]),(0,[z0,z1,z2,z171,z43,z12])]],
   [[(0,[z0,z1,z2,z3,z5,z958]),(0,[z79,z1,z2,z3,z5,z22]),(0,[z0,z1,z959,z3,z5,z6]),(0,[z0,z1,z960,z2,z5,z6]),(0,[z0,z1,z8,z3,z300,z5])],[(0,[z0,z1,z2,z3,z5,z961]),(0,[z0,z66,z1,z35,z85,z6])],[(0,[z664,z1,z88,z3,z5,z6]),(0,[z0,z1,z2,z3,z962,z5]),(0,[z0,z409,z2,z3,z5,z148]),(0,[z0,z164,z1,z3,z129,z12]),(0,[z0,z1,z223,z11,z5,z12])],[(0,[z0,z1,z2,z3,z5,z549]),(0,[z0,z1,z423,z3,z5,z193]),(0,[z0,z1,z188,z3,z5,z12])],[(0,[z21,z1,z2,z3,z5,z78]),(0,[z165,z1,z2,z3,z5,z78]),(0,[z0,z1,z2,z155,z5,z12]),(0,[z0,z1,z8,z2,z399,z5])],[(0,[z0,z1,z2,z3,z420,z6]),(0,[z0,z1,z356,z3,z5,z581]),(0,[z0,z1,z2,z3,z5,z963]),(0,[z0,z1,z2,z3,z964,z5]),(0,[z0,z1,z965,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z966]),(0,[z0,z1,z223,z3,z5,z148]),(0,[z0,z1,z967,z2,z3,z5]),(0,[z0,z1,z2,z3,z968,z6]),(0,[z0,z1,z2,z171,z366,z6]),(0,[z0,z1,z8,z2,z3,z761]),(0,[z0,z1,z817,z3,z5,z6])],[(0,[z67,z1,z7,z119,z3,z5]),(0,[z207,z1,z2,z3,z5,z22]),(0,[z26,z0,z969,z3,z5,z6]),(0,[z0,z1,z2,z3,z970,z5]),(0,[z0,z1,z2,z971,z5,z6]),(0,[z0,z1,z2,z972,z5,z6]),(0,[z0,z1,z8,z3,z227,z5])],[(0,[z0,z1,z2,z973,z5,z6]),(0,[z0,z1,z974,z2,z3,z5]),(0,[z1,z2,z3,z5,z975,z6])],[(0,[z110,z210,z143,z3,z5,z6]),(0,[z0,z1,z7,z2,z594,z5])],[(0,[z0,z1,z2,z976,z5,z6]),(0,[z0,z1,z2,z3,z5,z977]),(0,[z0,z1,z35,z487,z5,z6])],[(0,[z0,z1,z978,z3,z5,z6]),(0,[z979,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z980,z5]),(0,[z0,z97,z503,z2,z137,z6]),(0,[z0,z1,z981,z423,z3,z5])],[(0,[z0,z1,z2,z3,z982,z6]),(0,[z0,z626,z2,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z983]),(0,[z0,z1,z984,z2,z3,z5]),(0,[z0,z1,z8,z2,z5,z872])],[(0,[z0,z1,z2,z11,z5,z73]),(0,[z0,z1,z444,z2,z5,z32]),(0,[z0,z1,z2,z161,z5,z193])],[(0,[z79,z0,z1,z223,z3,z5]),(0,[z0,z51,z463,z2,z5,z6]),(0,[z0,z1,z985,z2,z5,z6])],[(0,[z0,z1,z2,z3,z5,z455]),(0,[z0,z1,z986,z2,z5,z6]),(0,[z0,z1,z2,z175,z321,z5]),(0,[z0,z1,z2,z987,z5,z6]),(0,[z0,z1,z8,z2,z3,z918]),(0,[z0,z988,z2,z3,z5,z12])],[(0,[z0,z989,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z990,z5]),(0,[z0,z1,z2,z3,z5,z991]),(0,[z0,z1,z118,z2,z5,z472])]],
   [[(0,[z0,z1,z2,z425,z5,z581]),(0,[z0,z1,z2,z992,z5,z6]),(0,[z0,z1,z2,z594,z5,z6]),(0,[z65,z1,z7,z2,z3,z124]),(0,[z21,z1,z368,z2,z3,z5]),(0,[z21,z1,z2,z304,z3,z5])],[(0,[z110,z145,z143,z2,z3,z5]),(0,[z0,z1,z993,z2,z3,z5])],[(0,[z79,z0,z1,z2,z11,z5]),(0,[z0,z1,z2,z3,z5,z994]),(0,[z0,z1,z995,z2,z3,z5]),(0,[z0,z1,z7,z577,z3,z5])],[(0,[z0,z51,z2,z705,z5,z6]),(0,[z0,z232,z2,z3,z325,z92]),(0,[z0,z144,z132,z2,z3,z5]),(0,[z0,z1,z614,z2,z3,z23]),(0,[z0,z1,z123,z223,z3,z5]),(0,[z0,z66,z1,z2,z583,z6])],[(0,[z0,z145,z550,z1,z2,z3]),(0,[z0,z1,z2,z722,z5,z374])],[(0,[z0,z1,z2,z754,z5,z6]),(0,[z0,z1,z2,z3,z5,z996]),(0,[z0,z1,z2,z774,z5,z6]),(0,[z0,z1,z8,z361,z3,z5]),(0,[z0,z1,z2,z149,z5,z12]),(0,[z0,z1,z223,z3,z5,z215])],[(0,[z71,z1,z2,z95,z5,z12]),(0,[z0,z1,z35,z8,z3,z5]),(0,[z0,z1,z2,z3,z997,z5])],[(0,[z0,z1,z2,z3,z5,z489]),(0,[z0,z1,z998,z2,z3,z5]),(0,[z0,z1,z8,z2,z3,z721])],[(0,[z0,z1,z928,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z64]),(0,[z0,z409,z168,z2,z3,z5])],[(0,[z0,z695,z2,z3,z5,z73])],[(0,[z462,z0,z1,z2,z149,z5])],[(0,[z0,z1,z2,z3,z5,z999]),(0,[z0,z1,z2,z3,z5,z1000]),(0,[z0,z473,z1,z101,z3,z6]),(0,[z0,z1,z2,z3,z1001,z5]),(0,[z0,z1,z2,z3,z23,z592])],[(0,[z0,z1,z8,z2,z425,z5]),(0,[z0,z1,z101,z3,z23,z5]),(0,[z0,z1,z2,z3,z238,z12]),(0,[z0,z1,z2,z3,z5,z1002])],[(0,[z0,z1,z2,z3,z5,z1003]),(0,[z0,z1,z2,z3,z5,z83]),(0,[z0,z1,z2,z1004,z3,z5])],[(0,[z0,z1,z8,z272,z3,z5]),(0,[z26,z0,z27,z3,z5,z12]),(0,[z0,z1,z2,z3,z451,z12])],[(0,[z0,z1,z2,z3,z6,z1005]),(0,[z67,z340,z1,z3,z5,z6]),(0,[z0,z1,z1006,z2,z3,z5]),(0,[z0,z1,z133,z2,z5,z328])]],
   [[(0,[z0,z1,z2,z629,z4,z6]),(0,[z0,z1,z2,z3,z117,z12]),(0,[z0,z1,z558,z8,z3,z5]),(0,[z0,z1,z7,z2,z901,z5]),(0,[z0,z1,z2,z171,z265,z43])],[(0,[z0,z1,z2,z3,z5,z1007]),(0,[z0,z164,z1,z269,z129,z6]),(0,[z0,z1,z2,z3,z762,z6])],[(0,[z0,z2,z969,z3,z5,z6]),(0,[z0,z1,z2,z11,z23,z5])],[(0,[z1,z2,z3,z5,z815,z6]),(0,[z0,z115,z1,z223,z3,z5])],[(0,[z0,z1,z2,z924,z5,z6]),(0,[z0,z51,z7,z2,z24,z5]),(0,[z0,z1,z854,z3,z30,z5]),(0,[z0,z1,z2,z171,z453,z6])],[(0,[z0,z1,z2,z3,z5,z1008]),(0,[z0,z66,z1,z2,z215,z6])],[(0,[z0,z1,z2,z3,z5,z1009]),(0,[z0,z97,z2,z3,z137,z247]),(0,[z0,z1,z3,z5,z863,z6]),(0,[z0,z1,z8,z440,z3,z5])],[(0,[z0,z1,z2,z1010,z5,z6]),(0,[z0,z1,z2,z3,z5,z1011]),(0,[z0,z1,z1012,z3,z5,z6]),(0,[z0,z1,z1013,z2,z3,z5]),(0,[z0,z232,z2,z3,z23,z92]),(0,[z0,z1,z223,z171,z3,z5])],[(0,[z1,z2,z3,z5,z22,z815]),(0,[z0,z1,z8,z2,z1014,z5]),(0,[z0,z1,z7,z3,z5,z81])],[(0,[z65,z0,z1,z223,z3,z5]),(0,[z0,z1,z3,z5,z36,z217])],[(0,[z0,z1,z1015,z2,z3,z5]),(0,[z0,z164,z1,z8,z171,z3])],[(0,[z210,z0,z145,z1,z3,z5]),(0,[z0,z1,z7,z2,z5,z374])],[(0,[z0,z1,z2,z3,z5,z1016]),(0,[z0,z1,z2,z3,z5,z1017]),(0,[z0,z1,z2,z1018,z5,z6]),(0,[z0,z97,z1,z2,z3,z337]),(0,[z0,z1,z2,z3,z5,z1019])],[(0,[z0,z1,z8,z3,z5,z349]),(0,[z1020,z1,z2,z3,z5,z6]),(0,[z0,z1,z2,z1021,z5,z6]),(0,[z0,z1,z2,z3,z5,z1022]),(0,[z0,z232,z2,z3,z92,z83]),(0,[z0,z1,z188,z5,z44,z6])],[(0,[z0,z1,z2,z538,z5,z6]),(0,[z0,z643,z1,z2,z3,z12]),(0,[z0,z1,z2,z767,z5,z6])],[(0,[z0,z1,z2,z3,z4,z581]),(0,[z0,z1,z2,z1023,z3,z5]),(0,[z0,z1,z2,z1024,z5,z6])]],
   [[(0,[z0,z1,z7,z631,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1025])],[],[(0,[z0,z1,z2,z3,z23,z337]),(0,[z0,z1,z7,z2,z171,z43])],[],[(0,[z0,z1,z2,z1026,z5,z6]),(0,[z0,z1,z2,z3,z5,z1027]),(0,[z0,z1,z118,z2,z579,z5]),(0,[z0,z1,z1028,z2,z3,z5]),(0,[z0,z1,z2,z1029,z5,z6]),(0,[z0,z1,z981,z2,z3,z5])],[(0,[z0,z1030,z1,z2,z5,z6]),(0,[z0,z1,z1031,z2,z652,z5])],[(0,[z0,z1,z2,z3,z1032,z5]),(0,[z0,z1,z2,z3,z5,z1033])],[(0,[z0,z550,z1,z101,z3,z6]),(0,[z1034,z0,z1,z2,z3,z5]),(0,[z0,z1,z85,z3,z16,z217])],[(0,[z0,z1,z8,z2,z3,z846])],[(0,[z0,z1,z2,z3,z5,z1035]),(0,[z0,z1,z487,z3,z5,z6]),(0,[z0,z226,z1,z2,z3,z182]),(0,[z0,z1,z35,z3,z5,z93]),(0,[z0,z164,z1,z17,z3,z5]),(0,[z0,z1,z249,z2,z271,z5])],[(0,[z0,z1,z8,z3,z57,z5]),(0,[z0,z1,z2,z3,z5,z1036]),(0,[z0,z1,z2,z3,z592,z6]),(0,[z0,z1,z7,z188,z3,z5])],[(0,[z0,z1,z8,z651,z3,z5]),(0,[z0,z1,z2,z3,z5,z1037])],[(0,[z65,z1,z2,z3,z124,z6]),(0,[z0,z1,z2,z3,z23,z783])],[(0,[z0,z1,z1038,z3,z5,z6]),(0,[z0,z1,z1039,z3,z5,z6]),(0,[z0,z1,z1040,z2,z3,z5]),(0,[z0,z1,z7,z2,z497,z5]),(0,[z0,z1,z2,z5,z374,z1041]),(0,[z0,z1,z2,z3,z5,z1042]),(0,[z0,z1,z7,z8,z3,z5])],[(0,[z0,z1,z3,z5,z1043,z6]),(0,[z0,z1,z1044,z2,z3,z5])]],
   [[(0,[z0,z1,z2,z3,z851,z5]),(0,[z0,z1,z2,z3,z5,z1045])],[(0,[z0,z1,z2,z3,z5,z1046]),(0,[z0,z1047,z1,z2,z3,z5]),(0,[z0,z1,z35,z175,z5,z6]),(0,[z0,z164,z1,z399,z129,z6]),(0,[z0,z1,z2,z3,z5,z217])],[(0,[z0,z1,z1048,z2,z3,z5])],[(0,[z0,z1,z7,z511,z3,z5]),(0,[z0,z1,z2,z3,z1049,z5])],[(0,[z0,z1,z2,z3,z5,z1050]),(0,[z0,z1,z2,z3,z23,z289]),(0,[z0,z1,z177,z3,z5,z12])],[(0,[z0,z115,z7,z350,z3,z5]),(0,[z0,z1,z133,z2,z767,z5])],[(0,[z0,z1,z2,z425,z5,z6]),(0,[z0,z1,z2,z1051,z5,z6]),(0,[z0,z164,z1,z8,z3,z129])],[(0,[z0,z1,z415,z3,z23,z5]),(0,[z0,z1,z2,z3,z585,z12]),(0,[z0,z1,z2,z3,z5,z1052]),(0,[z0,z1,z1053,z2,z3,z5]),(0,[z0,z1,z1054,z2,z3,z5]),(0,[z0,z1,z25,z2,z3,z23])],[(0,[z0,z1,z2,z1055,z5,z6]),(0,[z1056,z1,z2,z3,z5,z6]),(0,[z0,z1,z35,z223,z3,z5]),(0,[z0,z1,z85,z3,z15,z16]),(0,[z0,z1,z5,z328,z81,z12])],[(0,[z0,z339,z1,z101,z5,z6]),(0,[z21,z0,z1,z223,z3,z5]),(0,[z0,z1,z1057,z3,z5,z6]),(0,[z0,z1,z2,z3,z1058,z5]),(0,[z0,z1,z7,z123,z30,z5])],[(0,[z0,z151,z350,z3,z5,z6])],[(0,[z0,z1,z3,z5,z81,z6]),(0,[z0,z1,z2,z3,z23,z202]),(0,[z0,z1,z2,z1059,z5,z12]),(0,[z0,z1,z2,z1060,z5,z12])],[(0,[z0,z457,z2,z3,z137,z6]),(0,[z79,z1,z2,z3,z5,z815]),(0,[z0,z1,z1061,z2,z3,z5]),(0,[z0,z1,z8,z3,z5,z706]),(0,[z0,z1,z8,z3,z451,z5]),(0,[z0,z1,z1062,z3,z5,z6])],[(0,[z0,z1,z1063,z2,z3,z5])],[(0,[z21,z0,z1,z2,z11,z5]),(0,[z0,z226,z1,z123,z2,z6]),(0,[z0,z1,z2,z1064,z5,z6]),(0,[z0,z1,z2,z3,z1065,z5]),(0,[z0,z1,z118,z188,z5,z44])],[(0,[z0,z1,z2,z1066,z3,z5]),(0,[z0,z1,z2,z30,z5,z408]),(0,[z0,z1,z1067,z2,z3,z5]),(0,[z0,z1,z8,z2,z3,z905]),(0,[z0,z1,z7,z2,z773,z5]),(0,[z0,z1,z2,z987,z23,z5])]],
   [[(0,[z0,z109,z669,z2,z3,z5])],[(0,[z0,z164,z1,z2,z3,z242])],[(0,[z0,z473,z1,z7,z2,z3]),(0,[z0,z2,z3,z771,z5,z6]),(0,[z0,z1068,z1,z223,z3,z5])],[(0,[z0,z1,z2,z3,z1069,z6]),(0,[z0,z1,z2,z3,z1070,z6]),(0,[z0,z1,z3,z5,z956,z250]),(0,[z0,z1,z2,z3,z178,z12]),(0,[z0,z1,z2,z11,z5,z593])],[(0,[z0,z1,z2,z3,z5,z1071]),(0,[z0,z1,z2,z3,z1072,z5]),(0,[z0,z109,z170,z2,z3,z5]),(0,[z0,z1,z248,z3,z5,z36]),(0,[z0,z1,z2,z3,z23,z37]),(0,[z100,z0,z1,z223,z3,z5])],[],[(0,[z0,z1,z2,z3,z5,z1073]),(0,[z0,z1074,z2,z3,z5,z6]),(0,[z0,z1,z2,z1075,z5,z6]),(0,[z0,z1,z2,z3,z1076,z6]),(0,[z0,z1,z3,z16,z762,z6])],[(0,[z0,z1,z415,z3,z420,z6]),(0,[z0,z1,z749,z2,z3,z5]),(0,[z0,z1,z1077,z2,z3,z5]),(0,[z0,z226,z1,z2,z171,z6]),(0,[z0,z1,z118,z2,z5,z44])],[(0,[z0,z1,z7,z2,z538,z5]),(0,[z0,z1,z2,z5,z1078,z6]),(0,[z0,z1,z422,z2,z227,z5]),(0,[z0,z1,z7,z2,z767,z5]),(0,[z0,z1,z423,z3,z5,z12]),(0,[z0,z1,z2,z5,z328,z6]),(0,[z0,z1,z133,z3,z5,z81])],[(0,[z0,z97,z7,z2,z3,z137]),(0,[z0,z1,z2,z149,z227,z5])],[(0,[z0,z1,z1079,z3,z5,z6]),(0,[z0,z1,z2,z763,z5,z6])],[(1,[z0,z969,z3,z5,z6]),(0,[z0,z1,z223,z3,z5,z137])],[(0,[z0,z115,z347,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1080]),(1,[z0,z2,z3,z765,z6]),(0,[z0,z66,z1,z2,z84,z6]),(0,[z0,z1,z7,z423,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1081]),(0,[z0,z1,z223,z119,z3,z5]),(0,[z0,z97,z1,z223,z3,z5]),(0,[z0,z1,z2,z3,z783,z12])],[(0,[z0,z1,z2,z3,z1082,z6]),(0,[z0,z1,z2,z3,z5,z1083]),(0,[z0,z1084,z1,z2,z3,z5]),(0,[z0,z1,z558,z30,z5,z6]),(0,[z0,z823,z1,z2,z5,z6]),(0,[z0,z1,z2,z227,z5,z12])],[(0,[z0,z1,z2,z3,z948,z6]),(0,[z0,z1,z7,z2,z155,z5]),(0,[z0,z1,z1085,z2,z3,z5])]],
   [[(0,[z0,z1,z415,z3,z5,z455]),(0,[z110,z101,z143,z3,z5,z6]),(0,[z0,z339,z550,z1,z2,z6]),(0,[z0,z1,z1086,z2,z3,z5]),(0,[z0,z144,z2,z3,z5,z148]),(0,[z0,z1,z2,z149,z5,z242]),(0,[z0,z1,z223,z3,z5,z36])],[(0,[z0,z1,z1031,z2,z3,z5]),(0,[z0,z1,z123,z23,z30,z5]),(0,[z0,z1,z2,z3,z5,z1087])],[(0,[z0,z1,z2,z3,z5,z1088]),(0,[z0,z1,z2,z1089,z5,z6]),(0,[z40,z1,z7,z2,z3,z114]),(0,[z0,z1,z8,z392,z3,z5]),(0,[z0,z1,z1090,z2,z3,z5])],[(0,[z0,z1,z1091,z487,z3,z5]),(0,[z0,z1,z896,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1092,z6]),(0,[z0,z1,z1093,z2,z3,z5]),(0,[z0,z1,z2,z3,z1094,z6]),(0,[z0,z1095,z1,z2,z5,z6])],[(0,[z0,z1,z2,z3,z4,z6]),(0,[z65,z1,z2,z3,z124,z108]),(0,[z0,z232,z2,z3,z765,z6])],[(0,[z0,z1,z952,z3,z5,z6]),(0,[z0,z1,z7,z149,z5,z36])],[(0,[z0,z1,z1096,z2,z3,z5]),(0,[z0,z97,z2,z3,z137,z12]),(0,[z0,z1,z223,z85,z3,z5]),(0,[z0,z1,z3,z16,z5,z337])],[(0,[z110,z143,z2,z3,z5,z12]),(0,[z0,z1,z312,z2,z3,z5]),(0,[z0,z1,z2,z3,z1097,z5])],[(0,[z0,z1,z1098,z2,z3,z5]),(0,[z0,z1,z2,z171,z43,z6])],[(0,[z0,z1,z2,z1099,z5,z6]),(0,[z0,z1,z1100,z2,z5,z6]),(0,[z0,z1,z2,z3,z1101,z5]),(0,[z0,z1,z2,z5,z328,z250]),(0,[z0,z1,z223,z3,z5,z362]),(0,[z0,z1,z267,z2,z1024,z5])],[(0,[z0,z1,z1102,z2,z3,z5]),(0,[z0,z1,z2,z171,z155,z6])],[(0,[z0,z1,z35,z663,z5,z6]),(0,[z0,z164,z1,z3,z129,z6]),(0,[z0,z1,z223,z11,z5,z6])],[(0,[z936,z210,z0,z1,z3,z5]),(0,[z0,z1,z1103,z2,z3,z5]),(0,[z0,z1,z2,z497,z23,z5]),(0,[z0,z1,z188,z3,z5,z6]),(0,[z0,z1,z2,z5,z93,z32]),(0,[z0,z1,z25,z2,z3,z242])],[(0,[z0,z1,z2,z798,z5,z6]),(0,[z0,z1,z2,z155,z5,z6]),(0,[z0,z164,z1,z444,z3,z129]),(0,[z0,z66,z1,z7,z2,z215])],[(0,[z0,z1,z1104,z2,z3,z6]),(0,[z0,z1,z2,z785,z3,z5]),(0,[z0,z1,z7,z464,z3,z5]),(0,[z0,z1,z2,z3,z5,z1105])]],
   [[(0,[z0,z66,z1,z2,z321,z5]),(0,[z40,z0,z1,z223,z3,z5]),(0,[z0,z1,z2,z3,z5,z1106]),(0,[z0,z1,z798,z30,z5,z6]),(0,[z0,z1,z7,z3,z5,z831])],[(0,[z0,z1,z8,z2,z68,z5])],[(0,[z0,z1,z1107,z2,z3,z5]),(0,[z21,z136,z1,z2,z3,z5]),(0,[z0,z164,z1,z269,z2,z6]),(0,[z0,z1,z2,z271,z5,z44]),(0,[z0,z1,z2,z5,z44,z193])],[(0,[z0,z473,z1,z2,z3,z12]),(0,[z0,z1,z2,z360,z23,z5]),(0,[z0,z1,z2,z3,z5,z1108]),(0,[z0,z1,z2,z3,z5,z1109]),(0,[z0,z1,z35,z8,z271,z5]),(0,[z0,z1,z8,z85,z3,z16])],[(0,[z0,z1,z1110,z3,z5,z6]),(0,[z0,z1,z177,z3,z5,z148])],[(0,[z39,z1,z2,z94,z5,z6]),(0,[z0,z1,z2,z3,z331,z12]),(0,[z0,z1,z8,z3,z5,z126]),(0,[z0,z1,z2,z3,z5,z337]),(0,[z0,z1,z7,z2,z11,z5]),(0,[z0,z1,z460,z2,z3,z23])],[(0,[z111,z19,z2,z3,z5,z6]),(0,[z0,z1,z2,z1111,z5,z6]),(0,[z0,z473,z339,z1,z2,z6]),(0,[z0,z1,z8,z96,z3,z5]),(0,[z0,z1,z2,z161,z189,z5]),(0,[z0,z1,z2,z11,z5,z218]),(0,[z0,z1,z2,z1112,z5,z12]),(0,[z0,z1,z17,z3,z590,z5])],[(0,[z0,z1113,z1,z2,z3,z5])],[(0,[z0,z871,z550,z1,z2,z3]),(0,[z0,z1,z1114,z2,z3,z5]),(0,[z0,z988,z2,z3,z5,z6]),(0,[z0,z1,z7,z2,z1115,z5])],[(0,[z0,z1,z2,z3,z5,z1116]),(0,[z0,z1,z3,z5,z1117,z6]),(0,[z0,z1,z2,z1118,z5,z6]),(0,[z0,z1,z223,z5,z328,z12])],[(0,[z0,z1,z2,z3,z1119,z5]),(0,[z67,z1,z119,z3,z5,z12])],[(0,[z0,z1120,z1,z2,z3,z6]),(0,[z0,z1,z2,z3,z5,z1121]),(0,[z0,z1122,z1,z2,z3,z5]),(0,[z0,z66,z1,z2,z215,z369]),(0,[z0,z1,z2,z11,z5,z44]),(0,[z0,z1,z2,z945,z23,z5])],[(0,[z0,z1,z356,z3,z23,z5]),(0,[z322,z1,z2,z94,z5,z6]),(0,[z0,z1,z2,z1123,z5,z6]),(0,[z0,z109,z2,z3,z5,z714])],[(0,[z0,z1,z2,z68,z5,z12]),(0,[z0,z1,z2,z3,z5,z1124]),(0,[z0,z1,z411,z175,z5,z6])],[(0,[z0,z1,z3,z1125,z5,z6]),(0,[z0,z115,z350,z3,z5,z231]),(0,[z0,z1,z1126,z2,z3,z5])],[(0,[z0,z1,z2,z175,z5,z408]),(0,[z0,z1,z257,z8,z3,z5]),(0,[z0,z1,z35,z175,z5,z184])]],
   [[(0,[z0,z1127,z1,z2,z3,z6]),(0,[z71,z1,z2,z95,z5,z6]),(0,[z0,z1,z230,z2,z3,z5]),(0,[z0,z226,z1,z8,z3,z5]),(0,[z0,z1,z2,z161,z5,z741]),(0,[z0,z1,z223,z3,z23,z5])],[(0,[z0,z1,z1128,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1129]),(0,[z0,z1,z2,z3,z5,z1130])],[(0,[z0,z1,z7,z306,z3,z5]),(0,[z0,z1,z187,z8,z3,z5]),(0,[z0,z1,z2,z3,z23,z12])],[(0,[z0,z1,z1131,z2,z3,z5])],[(0,[z0,z1,z7,z2,z629,z5]),(0,[z0,z1,z2,z3,z5,z252]),(0,[z0,z1,z2,z3,z23,z313]),(0,[z0,z1,z2,z3,z5,z815]),(0,[z0,z1,z960,z2,z23,z5])],[(0,[z26,z0,z206,z27,z3,z5]),(0,[z0,z1,z209,z2,z5,z44])],[],[(0,[z0,z1,z7,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1132]),(0,[z0,z1,z2,z161,z279,z5])],[(0,[z0,z45,z1,z101,z5,z6]),(0,[z26,z0,z27,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1133]),(0,[z0,z1,z2,z149,z5,z148])],[(0,[z0,z20,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z565,z12]),(0,[z0,z1,z2,z3,z1134,z6]),(0,[z0,z1,z7,z269,z2,z5]),(0,[z0,z1,z85,z2,z3,z337]),(0,[z0,z1,z2,z23,z328,z12])],[(0,[z0,z1,z2,z3,z5,z1135])],[(0,[z0,z1,z7,z2,z3,z420]),(0,[z0,z473,z1,z2,z3,z1136]),(0,[z0,z1,z2,z3,z5,z1137]),(0,[z0,z1,z2,z3,z1138,z5]),(0,[z0,z1,z223,z3,z5,z78]),(0,[z0,z1,z1139,z2,z3,z5]),(0,[z0,z1,z3,z30,z5,z261])],[(0,[z0,z1,z356,z3,z420,z6]),(1,[z1,z2,z746,z5,z6]),(0,[z0,z1,z7,z2,z1089,z5]),(0,[z0,z1,z2,z5,z741,z218])],[(0,[z65,z1,z2,z3,z865,z6]),(0,[z26,z0,z8,z27,z3,z5])],[(0,[z0,z1,z2,z3,z1140,z5]),(0,[z0,z1,z8,z702,z3,z5])],[(0,[z0,z1,z1141,z2,z3,z5])]],
   [[(0,[z0,z1,z1142,z2,z3,z5]),(0,[z0,z550,z1,z2,z3,z12]),(0,[z0,z1,z2,z3,z5,z1143]),(0,[z0,z1,z2,z3,z5,z1144]),(1,[z0,z1,z3,z762,z6])],[(0,[z0,z1,z2,z3,z5,z1145]),(0,[z1,z2,z746,z95,z5,z6]),(0,[z0,z1,z8,z30,z5,z44]),(0,[z0,z1,z3,z762,z129,z6]),(0,[z0,z1,z7,z8,z227,z5]),(0,[z419,z1,z2,z3,z246,z5])],[(0,[z0,z1,z2,z1146,z3,z5]),(0,[z0,z1147,z1,z2,z3,z6]),(0,[z222,z0,z170,z2,z3,z5]),(0,[z0,z2,z3,z5,z1148,z12]),(0,[z0,z1,z3,z5,z1149,z12])],[(0,[z0,z1,z2,z3,z1150,z6]),(0,[z0,z1,z2,z3,z5,z1151]),(0,[z0,z1,z8,z2,z149,z5]),(0,[z0,z1,z223,z1152,z3,z5]),(0,[z0,z1,z267,z2,z841,z5])],[(0,[z0,z1,z2,z1153,z5,z6]),(0,[z0,z1,z8,z502,z3,z5]),(0,[z0,z1,z2,z594,z23,z5]),(0,[z0,z1,z2,z5,z374,z12]),(0,[z351,z0,z1,z8,z3,z5]),(0,[z0,z1,z2,z3,z5,z1154]),(0,[z0,z1,z2,z3,z527,z12])],[(0,[z0,z1,z356,z3,z5,z455]),(0,[z0,z1,z1155,z2,z3,z5]),(0,[z0,z1,z2,z3,z591,z12]),(0,[z0,z1,z2,z3,z5,z1156]),(0,[z0,z1,z1157,z2,z3,z5]),(0,[z0,z1,z3,z5,z831,z6]),(0,[z0,z1,z223,z1158,z3,z5])],[(0,[z0,z164,z1,z3,z762,z6])],[(0,[z0,z66,z1,z355,z2,z6]),(0,[z0,z1,z7,z2,z227,z5]),(0,[z462,z0,z1,z177,z3,z5]),(0,[z0,z1,z1159,z3,z5,z12])],[(0,[z0,z473,z1,z2,z3,z23]),(0,[z0,z1,z1160,z2,z3,z5]),(0,[z0,z226,z1,z85,z3,z6])],[(0,[z0,z1,z2,z3,z5,z1161])],[(0,[z0,z2,z3,z5,z1162,z6]),(0,[z87,z1,z7,z88,z3,z5]),(0,[z0,z1,z8,z94,z30,z5]),(0,[z0,z1,z17,z3,z30,z5]),(0,[z0,z1,z8,z161,z30,z5]),(0,[z0,z1,z2,z3,z47,z337])],[(0,[z0,z1,z1163,z2,z3,z5]),(0,[z0,z1,z487,z171,z5,z6])],[(0,[z0,z1164,z1,z2,z3,z5])],[(0,[z67,z1,z119,z68,z5,z6]),(0,[z87,z1,z88,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1165]),(0,[z0,z1,z969,z3,z5,z6]),(0,[z0,z1,z34,z30,z5,z6]),(0,[z0,z1,z269,z487,z5,z6]),(0,[z0,z1,z1166,z3,z5,z12]),(0,[z0,z1,z1167,z3,z5,z12])],[(0,[z0,z1,z751,z356,z3,z5]),(0,[z0,z1,z1168,z3,z5,z6]),(0,[z0,z145,z1,z101,z3,z5]),(0,[z0,z45,z1,z8,z2,z5])],[(0,[z0,z45,z550,z1,z2,z6]),(0,[z0,z1,z7,z2,z652,z5])]],
   [[(0,[z0,z1,z1169,z2,z3,z5]),(0,[z0,z1,z133,z223,z3,z5])],[(0,[z0,z1,z2,z1170,z5,z6]),(0,[z0,z1,z1171,z2,z3,z5])],[(0,[z0,z1,z2,z3,z420,z455]),(0,[z0,z339,z1,z8,z2,z5]),(0,[z0,z1,z2,z3,z5,z1172]),(0,[z0,z1,z2,z3,z1173,z5])],[(0,[z515,z0,z27,z3,z5,z6])],[(0,[z0,z226,z1,z2,z44,z6]),(0,[z0,z80,z1,z223,z3,z5])],[(0,[z0,z1,z2,z161,z227,z5]),(0,[z0,z1,z2,z3,z5,z1174]),(0,[z0,z1,z133,z2,z11,z5])],[(0,[z0,z1,z1175,z2,z3,z5]),(0,[z0,z1,z2,z3,z1176,z5]),(0,[z0,z144,z575,z2,z3,z5])],[(0,[z0,z1,z1177,z2,z3,z5]),(0,[z0,z1178,z2,z3,z5,z6]),(0,[z0,z350,z969,z3,z5,z6])],[(0,[z0,z940,z550,z1,z2,z3]),(0,[z0,z1,z2,z3,z5,z1179])],[(0,[z0,z1,z2,z3,z5,z1180]),(0,[z19,z834,z2,z3,z5,z6]),(0,[z0,z1,z2,z1181,z5,z6]),(0,[z0,z1,z2,z3,z5,z1182]),(0,[z0,z1,z2,z3,z865,z6]),(0,[z0,z1,z2,z227,z5,z242])],[(0,[z71,z0,z1,z223,z3,z5]),(0,[z0,z1,z7,z3,z5,z446]),(0,[z0,z1,z2,z3,z265,z5])],[(0,[z0,z1,z2,z725,z5,z6]),(0,[z0,z1,z2,z3,z5,z1183])],[(0,[z0,z1,z2,z3,z5,z1184]),(0,[z0,z1,z1185,z3,z5,z6]),(0,[z0,z1,z118,z2,z5,z328])],[(0,[z0,z1,z2,z3,z5,z1186]),(0,[z0,z1,z223,z3,z5,z73]),(0,[z0,z228,z2,z3,z5,z148]),(0,[z0,z1,z7,z2,z3,z592]),(0,[z0,z1,z2,z3,z5,z1187]),(0,[z0,z1,z8,z3,z5,z920]),(0,[z0,z1,z737,z2,z3,z5])],[(0,[z0,z1188,z1,z2,z5,z6]),(0,[z0,z1,z812,z3,z5,z6]),(0,[z0,z1,z177,z3,z5,z6])],[(0,[z0,z1,z2,z3,z5,z1189]),(0,[z0,z1,z1190,z2,z3,z5]),(0,[z0,z1,z8,z3,z5,z314]),(0,[z0,z1,z7,z227,z5,z36]),(0,[z0,z1,z2,z11,z23,z12])]],
   [[(0,[z0,z1,z2,z3,z1191,z6]),(0,[z0,z1,z123,z182,z30,z5])],[(0,[z0,z1192,z1,z3,z5,z6]),(0,[z0,z1,z2,z1193,z5,z6]),(0,[z0,z1,z2,z3,z5,z1041]),(0,[z0,z1,z1194,z2,z3,z5]),(0,[z0,z1,z223,z3,z5,z593])],[(0,[z0,z1195,z1,z3,z5,z6]),(0,[z0,z550,z1,z7,z2,z3]),(0,[z0,z1,z2,z538,z23,z5]),(0,[z1,z2,z3,z5,z815,z78]),(0,[z0,z1,z2,z3,z5,z193])],[(0,[z0,z1,z2,z3,z5,z1196]),(0,[z0,z1,z2,z3,z613,z12]),(0,[z0,z1,z2,z3,z1197,z5]),(0,[z0,z1,z7,z223,z3,z5]),(0,[z0,z1,z223,z3,z5,z540]),(0,[z0,z1,z2,z1024,z23,z5])],[(0,[z0,z1,z2,z3,z5,z1198]),(0,[z0,z1,z2,z1199,z5,z6])],[(0,[z0,z550,z1,z2,z3,z23]),(0,[z0,z1200,z1,z2,z3,z6]),(0,[z0,z1201,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z1202]),(0,[z0,z1,z223,z3,z5,z114]),(0,[z79,z0,z1,z2,z149,z5]),(0,[z0,z1,z2,z1059,z5,z6]),(0,[z0,z1,z2,z1060,z5,z6])],[(0,[z0,z1,z1203,z3,z5,z6]),(0,[z0,z1,z1204,z3,z5,z6]),(0,[z0,z503,z1,z8,z2,z5]),(0,[z0,z109,z2,z3,z5,z73]),(0,[z0,z1,z2,z854,z3,z5]),(0,[z0,z226,z1,z8,z2,z3]),(0,[z0,z1,z3,z16,z289,z6])],[(0,[z0,z1,z415,z3,z4,z6]),(0,[z0,z1,z133,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1205])],[(0,[z0,z1,z2,z3,z1206,z5]),(0,[z0,z51,z400,z2,z5,z6]),(0,[z0,z109,z1,z223,z3,z5])],[(0,[z377,z1,z2,z94,z5,z6]),(0,[z0,z232,z7,z2,z3,z92])],[(0,[z0,z1,z737,z3,z43,z5])],[(0,[z0,z1,z2,z3,z5,z1207]),(0,[z0,z1,z85,z3,z16,z12])],[(0,[z0,z1,z805,z356,z3,z5]),(0,[z0,z1,z8,z411,z3,z5]),(0,[z0,z1,z30,z5,z84,z6]),(0,[z0,z66,z1,z2,z1208,z6])],[(0,[z0,z1209,z2,z3,z5,z6]),(0,[z1,z2,z3,z865,z114,z6]),(0,[z0,z51,z1,z8,z30,z5]),(0,[z0,z1,z2,z5,z1208,z6])],[(0,[z0,z1,z2,z3,z5,z231]),(0,[z0,z1,z487,z3,z23,z5]),(0,[z0,z1,z2,z171,z43,z250])],[(0,[z210,z0,z1,z8,z3,z5]),(0,[z0,z1,z2,z3,z5,z1210]),(0,[z0,z1,z269,z2,z5,z12]),(0,[z0,z1,z3,z23,z81,z12])]],
   [[(0,[z210,z0,z550,z1,z3,z6]),(0,[z0,z1,z269,z8,z2,z5])],[(0,[z0,z1,z8,z3,z343,z5])],[(0,[z0,z1,z2,z629,z5,z12]),(0,[z0,z1,z2,z3,z5,z1211]),(0,[z0,z1,z423,z3,z5,z6]),(0,[z0,z1,z2,z149,z5,z6]),(0,[z0,z1,z223,z3,z5,z314])],[(0,[z0,z1,z223,z3,z5,z22])],[(0,[z0,z1,z1212,z2,z3,z5]),(0,[z0,z1,z2,z1213,z5,z6]),(1,[z0,z1,z223,z5,z328])],[(0,[z0,z1,z2,z3,z114,z337]),(0,[z0,z1,z8,z282,z3,z5]),(0,[z0,z1,z35,z175,z23,z5]),(0,[z0,z164,z1,z7,z3,z129])],[(0,[z0,z1,z7,z415,z3,z5]),(0,[z0,z1,z1214,z2,z3,z5]),(0,[z0,z1,z1215,z2,z3,z5]),(0,[z0,z1216,z1,z2,z3,z5]),(0,[z0,z115,z350,z3,z5,z427]),(0,[z0,z1,z1217,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z247])],[(0,[z0,z1,z2,z3,z5,z1218]),(0,[z0,z115,z350,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z408]),(0,[z0,z1,z444,z2,z3,z5]),(0,[z0,z1,z133,z2,z227,z5]),(0,[z0,z1,z2,z3,z783,z6])],[(0,[z79,z1,z587,z2,z3,z5]),(0,[z0,z1,z1219,z2,z3,z5]),(0,[z0,z1,z2,z43,z617,z6]),(0,[z0,z1,z2,z227,z5,z6]),(0,[z0,z1,z2,z5,z872,z337]),(0,[z302,z1,z587,z2,z3,z5])],[(0,[z0,z226,z1,z2,z3,z1033]),(0,[z0,z1,z8,z685,z3,z5])],[(0,[z0,z1,z2,z425,z23,z5]),(0,[z0,z473,z20,z1,z2,z3]),(0,[z0,z1,z2,z1220,z5,z6]),(0,[z0,z1,z223,z88,z3,z5]),(0,[z0,z1,z2,z3,z1221,z5]),(0,[z0,z1,z2,z1222,z5,z12])],[(0,[z0,z1,z1223,z3,z5,z6]),(0,[z0,z1,z2,z1224,z5,z6]),(0,[z0,z1,z2,z5,z1225,z6]),(0,[z21,z1,z2,z3,z5,z815]),(0,[z0,z1,z2,z652,z5,z12]),(0,[z0,z164,z1,z3,z129,z216]),(0,[z0,z1,z2,z11,z5,z179])],[(0,[z0,z1,z1226,z3,z5,z6]),(0,[z0,z1,z7,z2,z399,z5])],[(0,[z0,z1,z1227,z2,z3,z5]),(0,[z0,z1,z2,z155,z5,z216])],[(0,[z0,z1,z1228,z2,z3,z5]),(0,[z0,z1,z2,z1229,z5,z6]),(0,[z0,z144,z2,z3,z5,z714])],[(0,[z0,z1,z2,z3,z1230,z6])]],
   [[(0,[z110,z143,z2,z629,z5,z6]),(0,[z0,z1,z2,z11,z5,z328])],[(0,[z332,z1,z2,z3,z5,z78]),(0,[z0,z97,z2,z3,z137,z6]),(0,[z0,z434,z1,z8,z30,z5])],[(0,[z110,z143,z2,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1231])],[(0,[z0,z1,z2,z3,z1232,z5]),(0,[z0,z1,z2,z3,z5,z1233]),(0,[z0,z1,z487,z3,z5,z369])],[(0,[z71,z1,z2,z321,z95,z5]),(0,[z40,z1,z2,z3,z865,z6]),(0,[z0,z232,z2,z3,z92,z12]),(0,[z0,z1,z8,z3,z5,z589]),(0,[z0,z1,z35,z175,z5,z261])],[(0,[z0,z1,z2,z1234,z5,z6]),(0,[z0,z226,z1,z2,z95,z6]),(0,[z0,z1,z3,z5,z36,z831])],[(0,[z0,z1,z2,z3,z1235,z5]),(0,[z0,z436,z2,z52,z5,z6]),(0,[z0,z1,z2,z3,z74,z12])],[],[(0,[z0,z1,z269,z85,z2,z6])],[(0,[z0,z1,z2,z3,z1236,z5]),(0,[z0,z1,z248,z2,z5,z44]),(0,[z0,z1,z223,z3,z5,z44])],[(0,[z0,z1,z2,z425,z420,z6]),(0,[z0,z1,z101,z3,z5,z1196]),(0,[z0,z1,z269,z2,z5,z93])],[(0,[z0,z1,z415,z425,z5,z6]),(0,[z0,z1,z223,z3,z95,z5]),(0,[z0,z358,z1,z223,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1136]),(0,[z0,z1,z2,z399,z5,z12])],[(0,[z0,z473,z1,z2,z3,z6]),(1,[z0,z1,z798,z5,z6])],[(0,[z0,z1,z8,z2,z360,z5]),(0,[z0,z1,z1237,z2,z3,z5]),(0,[z0,z97,z2,z374,z137,z6]),(0,[z0,z1,z249,z8,z30,z5]),(0,[z0,z1,z2,z1014,z5,z6])],[(0,[z110,z143,z2,z3,z5,z581]),(1,[z834,z2,z3,z5,z6]),(0,[z0,z1,z1238,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z318]),(0,[z0,z115,z969,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z93]),(0,[z0,z1,z2,z11,z5,z193])]],
   [[(0,[z0,z45,z1,z2,z5,z12]),(0,[z0,z1,z2,z1112,z5,z6]),(0,[z0,z1,z3,z23,z5,z81])],[(0,[z0,z66,z1,z2,z5,z408]),(0,[z0,z1,z2,z3,z765,z6]),(0,[z0,z1239,z1,z2,z3,z5]),(0,[z0,z1,z269,z35,z5,z6])],[(0,[z0,z1,z101,z8,z3,z5]),(0,[z0,z1,z2,z3,z15,z5])],[(0,[z0,z1,z2,z3,z1240,z6]),(0,[z0,z1,z2,z425,z5,z455]),(0,[z0,z1,z2,z3,z1241,z6]),(0,[z0,z2,z771,z24,z5,z6]),(0,[z0,z1,z2,z3,z5,z1242]),(0,[z0,z1,z2,z3,z5,z1243]),(0,[z0,z1,z223,z5,z328,z6])],[(0,[z0,z1,z8,z356,z3,z5]),(0,[z0,z1,z7,z2,z425,z5]),(0,[z0,z339,z1,z2,z5,z12]),(0,[z67,z1,z119,z3,z5,z6]),(0,[z0,z1,z267,z8,z3,z5]),(0,[z158,z0,z1,z2,z11,z5]),(0,[z0,z1,z2,z23,z1244,z5])],[(0,[z0,z1,z2,z1245,z5,z6]),(0,[z0,z80,z2,z3,z5,z73]),(0,[z0,z1,z2,z3,z1208,z6])],[(0,[z0,z1,z2,z3,z5,z1246]),(0,[z0,z1,z2,z3,z1247,z6]),(0,[z0,z1,z2,z3,z5,z220]),(0,[z1248,z1,z2,z3,z5,z6]),(0,[z0,z1,z1249,z2,z3,z5]),(0,[z0,z1,z2,z5,z44,z741])],[(0,[z0,z1,z1250,z2,z3,z5]),(0,[z0,z1,z2,z1251,z3,z5]),(0,[z0,z1,z2,z68,z5,z6]),(0,[z0,z1,z2,z321,z30,z5])],[(0,[z0,z1,z2,z3,z5,z1252]),(0,[z0,z1,z1253,z2,z3,z5]),(0,[z0,z1,z269,z30,z5,z6]),(0,[z0,z1,z269,z444,z2,z5]),(0,[z0,z1,z2,z5,z32,z12])],[(0,[z0,z1,z2,z5,z893,z217])],[(0,[z0,z1,z1254,z2,z3,z5]),(0,[z0,z1,z2,z1255,z5,z6]),(0,[z0,z1,z2,z3,z5,z1256]),(0,[z0,z1,z267,z2,z3,z5]),(0,[z0,z164,z1,z3,z5,z337])],[(0,[z0,z1,z2,z3,z5,z1257]),(0,[z0,z1,z223,z3,z5,z86]),(0,[z0,z1,z3,z5,z1258,z12])],[(0,[z0,z1,z356,z3,z4,z6]),(0,[z0,z1,z2,z1259,z538,z5])],[(0,[z110,z834,z2,z3,z5,z6]),(0,[z0,z20,z45,z1,z2,z5]),(0,[z0,z1,z2,z5,z6,z1260]),(0,[z0,z1,z8,z3,z5,z637]),(0,[z0,z1,z2,z3,z5,z831]),(0,[z0,z1,z7,z570,z3,z5]),(0,[z0,z1,z201,z2,z3,z23]),(0,[z0,z1,z1261,z2,z3,z5])],[(0,[z0,z1,z2,z1262,z5,z6]),(0,[z419,z1,z2,z3,z5,z22]),(0,[z0,z1,z2,z3,z1263,z5]),(0,[z0,z51,z2,z24,z5,z12])],[(0,[z0,z1,z2,z3,z5,z1264]),(0,[z0,z1,z1265,z2,z3,z5]),(0,[z0,z164,z1,z3,z129,z314]),(0,[z0,z1,z1091,z2,z3,z5]),(0,[z0,z1,z2,z1208,z215,z6])]],
   [[(0,[z0,z1,z2,z1266,z5,z6]),(0,[z0,z1,z35,z271,z5,z6]),(0,[z0,z1,z187,z175,z5,z6])],[(0,[z21,z0,z1,z2,z149,z5]),(0,[z0,z1,z2,z155,z5,z314]),(0,[z165,z0,z1,z2,z149,z5]),(0,[z0,z1,z188,z3,z23,z5])],[(0,[z0,z1,z2,z3,z5,z1267]),(0,[z0,z29,z1,z8,z30,z5]),(0,[z0,z1,z2,z5,z1268,z6]),(0,[z0,z1,z2,z155,z23,z5])],[(0,[z1,z812,z119,z3,z5,z6]),(0,[z67,z1,z385,z119,z3,z5]),(0,[z0,z1,z2,z3,z1269,z5]),(0,[z0,z1,z2,z1270,z5,z6]),(0,[z0,z1,z2,z3,z5,z1271]),(0,[z0,z1,z480,z8,z3,z5]),(0,[z0,z1,z2,z3,z23,z173])],[(0,[z0,z1,z2,z3,z5,z1272]),(0,[z0,z1,z2,z3,z5,z1273])],[(0,[z0,z1,z1274,z3,z5,z6]),(0,[z0,z1,z2,z3,z1275,z6]),(0,[z111,z834,z2,z3,z5,z6]),(0,[z0,z1,z8,z3,z5,z478]),(0,[z0,z1,z5,z328,z81,z6])],[(0,[z0,z1,z1276,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z1277]),(0,[z71,z1,z8,z2,z95,z5]),(0,[z0,z29,z8,z2,z52,z5]),(0,[z0,z1,z2,z3,z5,z1278]),(0,[z708,z1,z2,z3,z5,z12])],[(0,[z0,z29,z2,z52,z5,z12]),(0,[z0,z1,z2,z3,z668,z12]),(0,[z0,z1,z1279,z223,z3,z5]),(0,[z0,z1,z223,z2,z5,z328])],[(0,[z0,z503,z1,z2,z5,z12]),(0,[z302,z0,z1,z2,z149,z5])],[(0,[z39,z1,z2,z94,z23,z5]),(0,[z0,z1,z2,z3,z5,z1280]),(0,[z0,z1,z85,z487,z3,z6])],[(0,[z0,z1,z2,z3,z5,z784]),(0,[z111,z19,z2,z3,z23,z5]),(0,[z0,z1,z2,z3,z672,z12]),(0,[z0,z29,z2,z52,z5,z408]),(0,[z158,z1,z2,z3,z5,z86])],[(0,[z1281,z0,z1,z2,z3,z5]),(0,[z0,z66,z1,z223,z3,z5]),(0,[z0,z1,z2,z828,z5,z12]),(0,[z0,z1,z2,z11,z5,z316])],[(0,[z0,z473,z145,z1,z2,z3]),(0,[z0,z1,z3,z5,z1149,z6]),(0,[z0,z1,z17,z3,z16,z5])],[(0,[z0,z1,z2,z3,z5,z1282]),(0,[z462,z0,z1,z8,z3,z5])],[(0,[z0,z1,z2,z5,z374,z6])],[(0,[z507,z1,z119,z3,z5,z6]),(0,[z0,z1,z1283,z2,z3,z5]),(0,[z40,z1,z2,z3,z114,z252]),(0,[z0,z1,z2,z3,z1284,z5])]],
   [[(0,[z0,z635,z1,z8,z3,z5]),(0,[z0,z1,z2,z3,z5,z1285]),(0,[z0,z1,z248,z2,z161,z5]),(0,[z0,z1,z2,z149,z5,z184]),(0,[z165,z1,z345,z2,z3,z5])],[(0,[z0,z1,z1159,z3,z5,z6])],[(0,[z0,z1,z2,z3,z4,z455]),(0,[z0,z1,z2,z5,z1286,z6]),(1,[z0,z1,z8,z155,z5])],[(0,[z0,z1,z1287,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1288]),(0,[z0,z1,z2,z3,z5,z1289])],[(0,[z210,z0,z339,z1,z5,z6]),(0,[z71,z1,z2,z95,z23,z5]),(0,[z21,z1,z2,z3,z359,z5]),(0,[z0,z1,z440,z175,z5,z6]),(0,[z0,z1,z8,z2,z5,z32]),(0,[z104,z1,z368,z2,z3,z5]),(0,[z0,z1290,z1,z223,z3,z5])],[(0,[z0,z1,z223,z3,z5,z5])],[(0,[z0,z1,z2,z3,z5,z427]),(1,[z0,z2,z771,z5,z6]),(0,[z0,z1,z2,z3,z1291,z5])],[(0,[z0,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z3,z1292,z5])],[(0,[z0,z1,z2,z3,z1293,z5]),(0,[z0,z1,z2,z3,z23,z195]),(0,[z0,z164,z1,z8,z155,z5])],[(0,[z0,z1,z8,z3,z592,z30]),(0,[z0,z1,z2,z161,z5,z184]),(0,[z0,z1,z7,z2,z1064,z5]),(0,[z0,z1,z2,z3,z23,z204]),(0,[z351,z0,z1,z223,z3,z5])],[(0,[z0,z1,z2,z5,z1294,z6]),(0,[z0,z144,z1,z223,z3,z5]),(0,[z0,z1,z2,z3,z5,z1295]),(0,[z0,z434,z1,z2,z98,z5])],[(0,[z210,z0,z1,z3,z5,z12]),(0,[z0,z1,z223,z350,z3,z5]),(0,[z0,z1,z2,z3,z5,z1296]),(0,[z0,z1,z790,z2,z5,z6]),(0,[z0,z1,z175,z798,z5,z6]),(0,[z0,z1209,z8,z2,z3,z5])],[(0,[z354,z1,z2,z3,z5,z22]),(0,[z26,z0,z27,z3,z23,z5]),(0,[z0,z1,z2,z3,z5,z1297]),(0,[z0,z164,z1,z8,z3,z16]),(0,[z0,z1,z2,z3,z43,z337])],[(0,[z0,z1,z1298,z3,z5,z6]),(0,[z1,z2,z94,z746,z5,z6]),(0,[z0,z1,z35,z8,z98,z5])],[],[(0,[z0,z1,z1299,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z242]),(0,[z0,z1,z2,z3,z5,z1300])]],
   [[(0,[z0,z1,z356,z425,z5,z6]),(0,[z0,z1,z223,z3,z30,z5]),(0,[z0,z1,z8,z177,z3,z5])],[(0,[z0,z1,z1301,z223,z3,z5]),(0,[z0,z1,z800,z3,z5,z6])],[(0,[z0,z1,z7,z8,z149,z5]),(0,[z0,z1,z7,z2,z1199,z5])],[(0,[z67,z1,z75,z119,z3,z5]),(0,[z0,z1,z2,z3,z5,z1302]),(0,[z0,z2,z3,z5,z714,z73])],[(0,[z0,z1,z2,z3,z50,z12]),(0,[z0,z1,z2,z3,z5,z1303]),(0,[z0,z1,z3,z16,z5,z93])],[(0,[z0,z1304,z2,z3,z5,z6]),(0,[z0,z1,z8,z2,z794,z5])],[(0,[z39,z1,z8,z2,z94,z5]),(0,[z0,z1,z2,z3,z5,z1305]),(0,[z0,z1,z1306,z3,z5,z6])],[(0,[z40,z1,z2,z3,z114,z318]),(0,[z0,z1,z2,z3,z5,z1307]),(0,[z0,z1,z223,z3,z5,z218]),(0,[z251,z1,z2,z3,z5,z540])],[(0,[z0,z1,z1308,z2,z3,z5]),(0,[z0,z2,z3,z5,z6,z1148])],[(0,[z0,z29,z2,z52,z5,z220]),(0,[z0,z1,z17,z2,z3,z5]),(0,[z0,z1,z2,z972,z5,z217])],[(0,[z0,z1,z2,z3,z5,z1309]),(0,[z0,z97,z2,z3,z765,z6]),(0,[z0,z1,z8,z3,z703,z5]),(0,[z0,z1,z737,z3,z5,z6])],[(0,[z0,z1,z2,z1259,z3,z5]),(0,[z0,z226,z29,z1,z2,z6]),(0,[z0,z1,z447,z30,z5,z6]),(0,[z0,z1,z155,z5,z129,z6]),(0,[z0,z1,z2,z3,z1310,z5]),(0,[z0,z1,z1311,z2,z3,z5])],[(0,[z0,z1,z1312,z2,z3,z5]),(0,[z0,z1,z177,z3,z5,z73]),(0,[z0,z1,z2,z43,z375,z6]),(0,[z0,z1,z35,z3,z5,z261]),(0,[z0,z1,z8,z3,z590,z5])],[(0,[z0,z1,z1313,z2,z3,z5]),(0,[z0,z1,z1314,z2,z3,z5]),(1,[z0,z1,z2,z1208,z6])],[(0,[z0,z1,z2,z3,z5,z1315]),(0,[z0,z1,z2,z3,z5,z1316]),(0,[z0,z66,z1,z35,z8,z5]),(0,[z0,z1,z2,z43,z1208,z6])],[(0,[z39,z1,z2,z746,z5,z6]),(0,[z65,z1,z2,z594,z124,z6]),(0,[z354,z1,z46,z2,z3,z5]),(0,[z0,z66,z1,z2,z23,z215])]],
   [[(0,[z110,z143,z8,z2,z3,z5]),(0,[z0,z1,z1317,z2,z3,z5]),(0,[z0,z1,z223,z94,z3,z5]),(0,[z254,z1,z2,z3,z114,z6]),(0,[z0,z1,z35,z17,z3,z5]),(0,[z0,z1,z155,z5,z36,z6]),(0,[z0,z1,z2,z161,z5,z250]),(0,[z0,z1,z223,z161,z3,z5]),(0,[z0,z358,z2,z3,z5,z593])],[(0,[z0,z339,z1,z7,z2,z5]),(0,[z275,z1,z2,z95,z5,z6])],[(0,[z0,z1,z2,z3,z1318,z5]),(0,[z0,z1,z1319,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1320]),(0,[z158,z0,z1,z223,z3,z5])],[(0,[z0,z1,z85,z3,z703,z6]),(0,[z0,z1,z85,z2,z3,z242])],[(0,[z0,z1,z2,z3,z5,z1321]),(0,[z0,z1,z2,z3,z5,z1322]),(0,[z0,z1,z1323,z2,z3,z5]),(0,[z0,z1,z718,z3,z5,z6])],[(0,[z0,z352,z2,z3,z5,z148]),(0,[z0,z1,z2,z1170,z23,z5])],[(0,[z0,z1,z1250,z415,z3,z5]),(0,[z0,z1,z2,z3,z23,z4]),(0,[z0,z1,z1324,z2,z3,z5]),(0,[z0,z1,z1325,z3,z5,z6]),(0,[z0,z1,z2,z3,z5,z741]),(0,[z0,z1,z792,z3,z5,z12])],[(0,[z0,z1,z487,z95,z5,z6]),(0,[z0,z1,z8,z2,z5,z328])],[(0,[z0,z2,z3,z1326,z5,z6]),(0,[z0,z1327,z2,z3,z5,z6]),(0,[z0,z969,z27,z3,z5,z6]),(0,[z0,z1,z2,z3,z1328,z6]),(0,[z0,z1,z133,z85,z3,z16])],[(0,[z0,z1,z269,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z1329]),(0,[z0,z1,z8,z155,z5,z6]),(0,[z0,z1,z223,z3,z5,z179])],[(0,[z0,z1,z2,z1330,z5,z6]),(0,[z0,z1,z223,z3,z47,z5])],[(0,[z0,z1,z1331,z3,z5,z6]),(0,[z0,z1,z123,z8,z30,z5]),(0,[z0,z1,z2,z841,z5,z6])],[(0,[z0,z1,z2,z629,z5,z6]),(0,[z0,z1,z2,z3,z5,z1332]),(0,[z0,z1,z2,z3,z5,z1333]),(0,[z0,z701,z1,z8,z3,z5]),(0,[z0,z226,z1,z248,z2,z3]),(0,[z0,z1,z2,z3,z47,z12])],[],[(0,[z0,z1,z101,z3,z5,z12]),(0,[z0,z1,z1334,z2,z3,z5]),(0,[z0,z1,z2,z962,z652,z5]),(0,[z0,z1,z223,z3,z5,z328])],[(0,[z111,z0,z1,z223,z3,z5]),(0,[z0,z1,z810,z3,z5,z12])]],
   [[(0,[z0,z29,z239,z2,z5,z6]),(0,[z0,z1,z2,z149,z5,z73]),(0,[z0,z164,z1,z8,z3,z5]),(0,[z0,z164,z1,z32,z129,z6])],[(0,[z0,z115,z350,z3,z5,z6])],[(0,[z251,z1,z2,z3,z5,z78]),(0,[z79,z0,z1,z177,z3,z5]),(0,[z0,z1,z1335,z3,z5,z6]),(0,[z0,z1,z487,z5,z215,z6]),(0,[z0,z1,z177,z3,z23,z5])],[(0,[z0,z1,z8,z2,z3,z4]),(0,[z0,z1,z2,z3,z1336,z6]),(0,[z0,z1,z8,z487,z3,z5])],[(0,[z0,z1,z2,z1222,z5,z6]),(0,[z0,z226,z1,z487,z3,z6]),(0,[z0,z1,z2,z11,z5,z12])],[(0,[z0,z1,z2,z3,z1337,z6]),(0,[z0,z226,z1,z7,z2,z3])],[(0,[z0,z1,z2,z23,z5,z32])],[(0,[z0,z1,z2,z3,z5,z1338]),(0,[z0,z1,z1339,z2,z3,z5]),(0,[z0,z1,z223,z27,z3,z5]),(0,[z0,z1,z2,z3,z337,z215])],[(0,[z0,z1,z2,z1340,z5,z6]),(0,[z0,z115,z350,z652,z5,z6])],[(0,[z0,z1,z2,z629,z5,z581]),(0,[z0,z1,z7,z2,z68,z5]),(0,[z67,z0,z1,z223,z3,z5]),(0,[z0,z1,z2,z5,z1341,z6]),(0,[z251,z0,z1,z2,z11,z5])],[(0,[z0,z1,z2,z425,z4,z6]),(0,[z110,z20,z143,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z1342]),(0,[z0,z1,z2,z3,z121,z12]),(1,[z0,z1,z8,z227,z5]),(0,[z1343,z0,z1,z223,z3,z5])],[(0,[z0,z1,z2,z3,z5,z581]),(0,[z0,z1,z1344,z2,z3,z5]),(0,[z0,z2,z52,z771,z5,z6]),(0,[z0,z1,z223,z175,z3,z5]),(0,[z0,z1,z7,z85,z3,z16])],[(0,[z0,z1,z2,z3,z5,z1345]),(0,[z0,z1,z2,z3,z200,z12]),(0,[z0,z1,z2,z161,z5,z481])],[(0,[z0,z550,z1,z2,z3,z6]),(0,[z0,z20,z550,z1,z2,z3]),(0,[z65,z1,z2,z538,z124,z6]),(0,[z0,z226,z1,z2,z161,z6]),(0,[z0,z164,z1,z3,z23,z129])],[(0,[z748,z0,z1,z2,z3,z5]),(0,[z67,z1,z8,z119,z3,z5]),(0,[z0,z1346,z2,z3,z5,z6]),(0,[z0,z1,z8,z273,z3,z5]),(0,[z0,z232,z2,z3,z92,z6]),(0,[z1347,z0,z1,z223,z3,z5])],[(0,[z0,z1,z2,z3,z5,z1348]),(0,[z1,z2,z3,z5,z865,z6]),(0,[z40,z1,z2,z3,z114,z12]),(0,[z0,z1,z2,z1349,z5,z6]),(0,[z0,z1,z2,z3,z5,z1350]),(0,[z0,z1,z3,z30,z5,z337]),(0,[z0,z1,z2,z3,z5,z1351]),(0,[z0,z1,z8,z3,z5,z217]),(0,[z0,z1,z223,z3,z1352,z5])]],
   [[(0,[z0,z1,z2,z3,z1353,z6]),(0,[z0,z1,z8,z2,z594,z5]),(0,[z65,z684,z1,z2,z3,z6]),(0,[z0,z1,z8,z3,z30,z5])],[(0,[z0,z473,z45,z1,z2,z6])],[(0,[z0,z1,z2,z3,z5,z1354]),(0,[z0,z1,z2,z3,z5,z1355])],[(0,[z0,z1,z2,z43,z5,z408]),(0,[z0,z1,z223,z3,z5,z337]),(0,[z0,z1,z2,z5,z44,z250])],[(0,[z0,z1,z2,z5,z935,z12])],[(0,[z0,z1,z2,z1115,z5,z6]),(0,[z0,z1,z17,z223,z3,z5])],[(0,[z0,z1,z1356,z2,z3,z5]),(0,[z71,z696,z1,z2,z5,z6]),(0,[z0,z1,z2,z399,z5,z6]),(0,[z0,z1,z2,z149,z23,z5]),(0,[z0,z1,z423,z3,z23,z5]),(0,[z0,z1,z2,z171,z1208,z6]),(0,[z0,z1,z267,z287,z3,z5])],[(0,[z197,z1,z2,z95,z5,z6]),(0,[z0,z1,z1357,z2,z3,z5]),(0,[z0,z1,z35,z8,z175,z5]),(0,[z0,z1,z223,z1358,z3,z5])],[(0,[z65,z1,z8,z2,z3,z124]),(0,[z0,z1,z2,z771,z5,z6]),(0,[z0,z1,z133,z2,z149,z5])],[(0,[z0,z1,z1359,z2,z3,z5]),(0,[z0,z1,z2,z3,z1360,z5])],[(0,[z0,z45,z1,z2,z5,z6]),(0,[z0,z1,z1361,z2,z5,z6]),(0,[z87,z1,z88,z3,z5,z6]),(0,[z0,z1,z1166,z3,z5,z6]),(0,[z0,z1,z1167,z3,z5,z6]),(0,[z26,z0,z1,z223,z3,z5]),(0,[z0,z1,z2,z3,z23,z203]),(1,[z0,z1,z223,z11,z5])],[(0,[z0,z1,z2,z931,z5,z6]),(0,[z0,z1,z2,z3,z5,z1362]),(0,[z0,z1,z123,z592,z30,z6]),(0,[z0,z226,z1,z35,z2,z6]),(0,[z0,z1,z855,z2,z3,z5]),(0,[z0,z1,z2,z3,z1363,z5]),(0,[z0,z1,z191,z2,z149,z5])],[(0,[z0,z1,z2,z3,z5,z1364]),(0,[z0,z1,z2,z1244,z5,z6]),(0,[z0,z1,z2,z3,z603,z12]),(0,[z0,z1,z133,z2,z3,z242]),(0,[z0,z1,z8,z2,z1029,z5]),(0,[z0,z1,z2,z227,z23,z5])],[(0,[z0,z1365,z1,z2,z5,z6]),(0,[z0,z1,z2,z3,z5,z1366]),(0,[z40,z513,z1,z2,z3,z6])],[(0,[z0,z339,z1,z2,z5,z6]),(0,[z0,z1,z223,z3,z92,z5])],[(0,[z0,z51,z2,z771,z5,z6]),(0,[z0,z144,z2,z3,z5,z593]),(0,[z0,z338,z2,z3,z196,z5])]],
   [[(0,[z0,z1,z2,z3,z5,z1367]),(0,[z0,z1,z2,z3,z1368,z5]),(0,[z0,z1,z223,z3,z23,z12])],[(0,[z0,z1,z2,z3,z4,z1081]),(0,[z0,z1,z1369,z2,z3,z5]),(0,[z0,z1370,z1,z2,z5,z6])],[(0,[z0,z1,z1371,z3,z5,z6]),(0,[z0,z1,z1372,z2,z3,z5]),(1,[z0,z226,z1,z8,z3])],[(0,[z0,z1,z2,z3,z1373,z5])],[(0,[z0,z164,z1,z3,z5,z93]),(0,[z0,z1,z118,z2,z227,z5])],[(0,[z0,z1,z3,z5,z1258,z6])],[(0,[z110,z143,z2,z3,z23,z5]),(0,[z0,z1,z3,z5,z6,z1374]),(0,[z0,z1,z2,z3,z5,z1375]),(0,[z0,z580,z2,z3,z5,z73]),(0,[z0,z226,z1,z2,z3,z12]),(0,[z0,z1,z2,z3,z1376,z5]),(0,[z0,z1,z7,z2,z786,z5])],[(0,[z0,z1,z2,z3,z5,z1377]),(0,[z0,z1378,z1,z2,z3,z5]),(0,[z0,z1,z1379,z2,z3,z5]),(0,[z0,z1,z17,z2,z3,z337]),(0,[z0,z1,z223,z3,z5,z9])],[(0,[z0,z51,z2,z24,z5,z6]),(0,[z0,z1,z85,z3,z682,z6]),(0,[z0,z1,z7,z3,z5,z36])],[(0,[z0,z1,z415,z3,z5,z12]),(0,[z0,z1,z2,z3,z5,z1380]),(0,[z0,z1,z2,z1381,z5,z6]),(0,[z0,z1,z2,z11,z47,z12]),(0,[z0,z1,z223,z3,z5,z316]),(0,[z0,z1,z2,z23,z5,z328])],[],[(0,[z0,z1,z7,z644,z3,z5]),(0,[z0,z1,z85,z3,z23,z16]),(0,[z0,z1,z7,z2,z149,z5]),(0,[z0,z1,z2,z3,z528,z12]),(0,[z0,z1,z423,z3,z5,z369])],[(0,[z0,z1,z2,z3,z5,z1382]),(0,[z0,z1,z2,z3,z5,z1383]),(0,[z0,z51,z8,z2,z24,z5]),(0,[z0,z1,z2,z3,z1384,z5]),(1,[z0,z1,z223,z3,z5]),(1,[z0,z1,z3,z5,z831])],[(0,[z0,z1,z2,z3,z124,z337]),(0,[z0,z228,z2,z3,z53,z5])],[(0,[z0,z1,z2,z3,z5,z1385]),(0,[z0,z1,z1386,z3,z5,z6]),(0,[z0,z1387,z1,z2,z5,z6]),(0,[z0,z1,z3,z5,z81,z217]),(1,[z0,z1,z2,z5,z741])],[(0,[z0,z1,z1388,z2,z3,z5]),(0,[z0,z1,z1389,z2,z5,z6]),(0,[z0,z1,z8,z3,z16,z5]),(0,[z0,z1,z8,z2,z1220,z5]),(0,[z1390,z0,z1,z223,z3,z5])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 498) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 498).take 493) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 991).take 426) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1417)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [498, 493, 426] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 104).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 104).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 213).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 322).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 424).take 88).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [104, 109, 109, 102, 88] = true :=
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

end PEqualNP.Outside.L_meta_38999

theorem PEqualNP.Outside.L_meta_38999 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008241320 * 2 ^ 32 + 4001949832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008241320 * 2 ^ 32 + 4001949832) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_38999.solve