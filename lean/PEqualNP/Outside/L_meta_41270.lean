import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41270

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
  Nat.testBit (4276809440 * 2 ^ 32 + 4276789248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x001461e18430ab75#64 ++ 0x0000a30f0c21855b#64 ++ 0x827ce3e38471fffe#64 ++ 0xd413e71f1c238fff#64 : BitVec 256),
   (0x04b16c6c45966706#64 ++ 0x08258b63622cb338#64 ++ 0x0db37c7c479e671d#64 ++ 0xd86d9be3e23cf338#64 : BitVec 256),
   (0xb1438036d81b85b8#64 ++ 0x058a1c01b6c0dc2d#64 ++ 0xf1c3807ff81f87fb#64 ++ 0xef8e1c03ffc0fc3f#64 : BitVec 256),
   (0x5a03b6806ee006c0#64 ++ 0x12d01db403770036#64 ++ 0xfe03ff807fe007f7#64 ++ 0xfff01ffc03ff003f#64 : BitVec 256),
   (0x6fe80000334d5000#64 ++ 0x037f4000019a6a80#64 ++ 0xfffc00007ffff80f#64 ++ 0xefffe00003ffffc0#64 : BitVec 256),
   (0x7ffedb5b00000000#64 ++ 0x23fff6dad8000000#64 ++ 0x7fffffff8000001f#64 ++ 0xb3fffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [7, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 5]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [14, 8]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x001441618010a935 0x0000a20b0c008549 0x007c00638011f808 0x0003e0031c008fc0

def z1 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db37c7c479e671d 0xd86d9be3e23cf338

def z2 : W := mkw 0x5a0396006ac00480 0x12d01cb003560024 0x7c031c007b800001 0x2be018e003dc0000

def z3 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe03ff807fe007f7 0xfff01ffc03ff003f

def z4 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfffc00007ffff80f 0xefffe00003ffffc0

def z5 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fffffff8000001f 0xb3fffffffc000000

def z6 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1c3807ff81f87fb 0xef8e1c03ffc0fc3f

def z7 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x827ce3e38471fffe 0xd413e71f1c238fff

def z8 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0x7c03ff807b8007f1 0x3be01ffc03dc003f

def z9 : W := mkw 0x7febbe9a6ee006c0 0x33ff5df4d3770036 0xff83ff9c7fe007f7 0xfffc1ffce3ff003f

def z10 : W := mkw 0x00116c6c44922706 0x08008b6362249138 0x00037c7c00000710 0x10001be3e0000038

def z11 : W := mkw 0x04a0000001044000 0x0025000000082200 0x0db00000479e600d 0xc86d8000023cf300

def z12 : W := mkw 0x001461c18420aa75 0x0000a30e0c210553 0x827ce3838461f8e6 0x1413e71c1c230fc7

def z13 : W := mkw 0x4a00160022c00000 0x125000b001160000 0x0c001c0003800000 0x006000e0001c0000

def z14 : W := mkw 0x9003801648020488 0x04801c00b2401024 0x0003001c00000000 0x00001800e0000000

def z15 : W := mkw 0x00106c4804802206 0x0800836240240110 0x00007c0000000000 0x100003e000000000

def z16 : W := mkw 0x0001242445966706 0x08000921222cb338 0x00000000479e6700 0x48000000023cf338

def z17 : W := mkw 0x7b4e931300000000 0x23da749898000000 0x724c838380000002 0x2392641c1c000000

def z18 : W := mkw 0x80000024901b8138 0x040000012480dc09 0x00000000001f8000 0x000000000000fc00

def z19 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0d831c1c438e0001 0x086c18e0e21c7000

def z20 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x0003ffff80000010 0x10001ffffc000000

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c037c0000000015 0x90601be000000000

def z22 : W := mkw 0x7febb6807fed56c0 0x13ff5db403ff6ab6 0xffffff807fffffff 0xfffffffc03ffffff

def z23 : W := mkw 0x7fffdf5f41864402 0x2bfffefafa0c3220 0x7fffffffc38e001f 0xbbfffffffe1c7000

def z24 : W := mkw 0x5a17f7e1eef0aff5 0x12d0bfbf0f77857f 0xfe7fffe3fff1ffff 0xfff3ffff1fff8fff

def z25 : W := mkw 0x04b16cecc5b6ef77 0x08258b67662db77b 0x8db37c7c47fffffd 0xdc6d9be3e23fffff

def z26 : W := mkw 0x0001240044800600 0x0000092002240030 0x0c037c0047800715 0xd8601be0023c0038

def z27 : W := mkw 0x5a0292802a6000c0 0x12d0149401530006 0xf2008380386000e2 0x2790041c01c30007

def z28 : W := mkw 0xa15461f7943bab7d 0x050aa30fbca1dd5b 0x83fce3ff847ffffe 0xd41fe71ffc23ffff

def z29 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0xfffffffffffff81f 0xffffffffffffffc0

def z30 : W := mkw 0x3142801200000000 0x018a140090000000 0x71c3807f8000001b 0xa38e1c03fc000000

def z31 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0x0e03ff8007e007f4 0x10701ffc003f003f

def z32 : W := mkw 0x7fea9a1a00000000 0x23ff54d0d0000000 0x7d831c1c00000001 0x23ec18e0e0000000

def z33 : W := mkw 0xb153ec7edc9ba7be 0x0d8a9f63f6e4dd3d 0xf1c3fc7ff81f87fb 0xff8e1fe3ffc0fc3f

def z34 : W := mkw 0x0001002440120500 0x0000080122009028 0x00000000401e0700 0x480000000200f038

def z35 : W := mkw 0x000020a08430ab75 0x000001050421855b 0x827c00000471ffee 0xc413e00000238fff

def z36 : W := mkw 0x25fc497b8010a935 0x212fe24bdc008549 0x01fc007f8011f808 0x000fe003fc008fc0

def z37 : W := mkw 0x000124806ee006c0 0x1000092403770036 0x800000007fe007e0 0x4c00000003ff003f

def z38 : W := mkw 0x80010024d81b85b8 0x0400080126c0dc2d 0x80000000781f87e0 0x4c00000003c0fc3f

def z39 : W := mkw 0x25fd6d7f45966706 0x292feb6bfa2cb338 0x0dff7c7fc79e671d 0xd86ffbe3fe3cf338

def z40 : W := mkw 0x6fe8000000000000 0x037f400000000000 0x7ffc00000000000f 0xa3ffe00000000000

def z41 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x8040e3e3801187fa 0xd402071f1c008c3f

def z42 : W := mkw 0x0001002440120500 0x0000080122009028 0x0183007c401e0719 0xc80c1803e200f038

def z43 : W := mkw 0xa140001290098038 0x050a000094804c01 0x0040000380018000 0x000200001c000c00

def z44 : W := mkw 0xb5f3c87ed91fe5be 0x0daf9e43f6c8ff2d 0xf1f3807ff81fe7fb 0xef8f9c03ffc0ff3f

def z45 : W := mkw 0x0000240005846206 0x08000120002c2310 0x0000000007806000 0x00000000003c0300

def z46 : W := mkw 0x04b0486c01166106 0x082582436008b308 0x0db0007c479e600d 0xc86d8003e23cf300

def z47 : W := mkw 0x000124804ca006c0 0x1000092402650036 0x00000000000007e0 0x000000000000003f

def z48 : W := mkw 0x4a1477e1a6f0ab75 0x1250a3bf0d37855b 0x8e7cffe387f1fffe 0xd473e7ff1c3f8fff

def z49 : W := mkw 0x9017db7fc81285b8 0x2480bedbfe40942d 0x0003ffff800007f0 0x10001ffffc00003f

def z50 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x8fffffffc7ffffff 0xdc7ffffffe3fffff

def z51 : W := mkw 0x00000000334d5000 0x00000000019a6a80 0x800000007ffff800 0x4c00000003ffffc0

def z52 : W := mkw 0xb157e1f7dc3baffd 0x058abf0fbee1dd7f 0xf1c3e3fff81f87fb 0xff8e1f1fffc0fc3f

def z53 : W := mkw 0x25e8000000000000 0x012f400000000000 0x01fc000000000008 0x000fe00000000000

def z54 : W := mkw 0x0000000010090000 0x0000000000804800 0x80000000781f8000 0x4c00000003c0fc00

def z55 : W := mkw 0x0000000000000000 0x0000000000000000 0x827c00000471f80e 0xc413e00000238fc0

def z56 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0d837c7c438e0711 0x186c1be3e21c7038

def z57 : W := mkw 0x7ffefbfb8430ab75 0x23fff7dfdc21855b 0xffffffff8471ffff 0xf7fffffffc238fff

def z58 : W := mkw 0x5a17ffdb6ee006c0 0x32d0bffedb770036 0xfe03ffffffe007f7 0xfff01fffffff003f

def z59 : W := mkw 0x7fffff7f45966706 0x2bfffffbfa2cb338 0x7fffffffc79e671f 0xfbfffffffe3cf338

def z60 : W := mkw 0x1003800048000480 0x00801c0002400024 0xf0038000780007f3 0xef801c0003c0003f

def z61 : W := mkw 0xfb43b6b6fefb87f8 0x17da1db5b7f7dc3f 0xffc3ffffffff87ff 0xfffe1ffffffffc3f

def z62 : W := mkw 0x4ea8000023445000 0x02754000011a2280 0x0e3c000007e07804 0x0071e000003f03c0

def z63 : W := mkw 0x0004218184208a71 0x0000210c0c210453 0x824ce38384619ff6 0xd412671c1c230cff

def z64 : W := mkw 0x25fc495b00000000 0x212fe24ad8000000 0x0dff7c7f8000001d 0x906ffbe3fc000000

def z65 : W := mkw 0x04a0000001044000 0x0025000000082200 0x0c30000007806004 0x00618000003c0300

def z66 : W := mkw 0x04b06c4805846206 0x08258362402c2310 0x0c307c0007806004 0x106183e0003c0300

def z67 : W := mkw 0x04a0000001044000 0x0025000000082200 0x0d800000438e0001 0x086c0000021c7000

def z68 : W := mkw 0xb143a0b6dc3b87f8 0x058a1d05b6e1dc3f 0xf3c3e3fffc7f87ff 0xff9e1f1fffe3fc3f

def z69 : W := mkw 0x4eb86c4827c47206 0x0a75c362413e2390 0x0e3c7c0007e07804 0x1071e3e0003f03c0

def z70 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0xffffffff8471f81f 0xf7fffffffc238fc0

def z71 : W := mkw 0x0010486c00122106 0x0800824360009108 0x0000007c00000000 0x00000003e0000000

def z72 : W := mkw 0x4a00000022400000 0x0250000001120000 0xf200000038600002 0x2790000001c30000

def z73 : W := mkw 0x04b0484800000000 0x0025824240000000 0x0c307c0000000004 0x106183e000000000

def z74 : W := mkw 0x7feb96007bcd5480 0x13ff5cb003de6aa4 0x7d831c007b8e0001 0x2bec18e003dc7000

def z75 : W := mkw 0xffffdb7ffb5fd5b8 0x27fffedbffdafead 0xffffffffffffffff 0xffffffffffffffff

def z76 : W := mkw 0x000124a4c5b6ef77 0x08000925262db77b 0x8000000047ffffe0 0x4c000000023fffff

def z77 : W := mkw 0x0000008000200040 0x0000000400010002 0x82008380006000e2 0x0410041c00030007

def z78 : W := mkw 0x0000208004200240 0x0000010400210012 0x0200638004600004 0x1010031c00230000

def z79 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe7fff807ff1ffff 0xfff3fffc03ff8fff

def z80 : W := mkw 0x000020a08430ab75 0x000001050421855b 0x800000000471ffe0 0x4400000000238fff

def z81 : W := mkw 0x6ff96c6c77df7706 0x0b7fcb6363befbb8 0xffff7c7c7fffff1f 0xfffffbe3e3fffff8

def z82 : W := mkw 0x04b16cec6ff667c6 0x18258b67637fb33e 0x8db37c7c7ffe67fd 0xdc6d9be3e3fff33f

def z83 : W := mkw 0x80010024c81285b8 0x040008012640942d 0x00000000000007e0 0x000000000000003f

def z84 : W := mkw 0x801561e5dc3baffd 0x0400ab0f2ee1dd7f 0x827ce3e3fc7ffffe 0xdc13e71f1fe3ffff

def z85 : W := mkw 0x0001248044a00640 0x0000092402250032 0x8e03ff8047e007f7 0xdc701ffc023f003f

def z86 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x0000e3e3800007f0 0x1000071f1c00003f

def z87 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x0db3ffffc79e67fd 0xd86d9ffffe3cf33f

def z88 : W := mkw 0x0014414100000000 0x0000a20a08000000 0x027ce3e38000001e 0x9013e71f1c000000

def z89 : W := mkw 0x14b3feec4db667c6 0x18a59ff7626db33e 0x0db3fffc479e67fd 0xd86d9fffe23cf33f

def z90 : W := mkw 0x4ebc5b4900000000 0x2275e2da48000000 0x0e3c7f8000000004 0x1071e3fc00000000

def z91 : W := mkw 0xffffdb7fd81b85b8 0x27fffedbfec0dc2d 0xfffffffff81f87ff 0xffffffffffc0fc3f

def z92 : W := mkw 0x04b4494900000000 0x0025a24a48000000 0x0fffffff8000001f 0x907ffffffc000000

def z93 : W := mkw 0x04a00c0801844002 0x08250060400c2200 0x0c001c0003800000 0x006000e0001c0000

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0x804000000011800a 0xc402000000008c00

def z95 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0x7d8000007b8e0001 0x2bec000003dc7000

def z96 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0x7ffffffffb8e001f 0xbbffffffffdc7000

def z97 : W := mkw 0x0000002080108130 0x0000000104008409 0x80408063801187fa 0xc40204031c008c3f

def z98 : W := mkw 0xb157e1f7dc3baffd 0x058abf0fbee1dd7f 0xf3ffe3fffc7fffff 0xff9fff1fffe3ffff

def z99 : W := mkw 0x04b0484801044000 0x0025824240082200 0x0db37c7c479e601d 0xd86d9be3e23cf300

def z100 : W := mkw 0xb157c177d81badbd 0x058abe0bbec0dd6d 0xf1ff807ff81ffffb 0xef8ffc03ffc0ffff

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x027c00000000000e 0x8013e00000000000

def z102 : W := mkw 0x8000003680128138 0x04000001b4009409 0x0000007f80000000 0x00000003fc000000

def z103 : W := mkw 0x7b4e931332491000 0x23da749899924880 0xf24c8383b8619802 0x2792641c1dc30cc0

def z104 : W := mkw 0x14b7ff7f45966706 0x28a5bffbfa2cb338 0x0db3ffffc79e671d 0xd86d9ffffe3cf338

def z105 : W := mkw 0x5ebedb5b00000000 0x22f5f6dad8000000 0x0e3fffff80000014 0x1071fffffc000000

def z106 : W := mkw 0x5a03b6006ec00680 0x12d01db003760034 0x7c037c007f800715 0xfbe01be003fc0038

def z107 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0x7dfc00007b9ff809 0x2befe00003dcffc0

def z108 : W := mkw 0x001060e004302344 0x000083070021811a 0x8230e3e0047067fe 0xd411871f0023833f

def z109 : W := mkw 0x25fc495b00000000 0x212fe24ad8000000 0x01fc007f80000008 0x000fe003fc000000

def z110 : W := mkw 0x0011646044902704 0x00008b2302248138 0x0c337c604790671d 0xd8619be3023c8338

def z111 : W := mkw 0xfb429292ba6980f8 0x17da149495d34c07 0xf2408383b86180e2 0x2792041c1dc30c07

def z112 : W := mkw 0x7fffffdb6ee006c0 0x33fffffedb770036 0xffffffffffe007ff 0xffffffffffff003f

def z113 : W := mkw 0x7ffedb7b8010a935 0x23fff6dbdc008549 0x7fffffff8011f81f 0xb3fffffffc008fc0

def z114 : W := mkw 0x5eb3feec6ff667c6 0x1af59ff7637fb33e 0xffb3fffc7ffe67ff 0xfffd9fffe3fff33f

def z115 : W := mkw 0x04b0484800000000 0x0025824240000000 0x0db37c7c0000001d 0x906d9be3e0000000

def z116 : W := mkw 0x6b48000032491000 0x035a400001924880 0xf24c000038619802 0x2792600001c30cc0

def z117 : W := mkw 0x5a02920022400000 0x02d0149001120000 0xfe03ff807fe00017 0xfff01ffc03ff0000

def z118 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf3ff807ffc7fffff 0xef9ffc03ffe3ffff

def z119 : W := mkw 0x0000368004a00240 0x100001b400250012 0x00007f8000000000 0x100003fc00000000

def z120 : W := mkw 0x90038036c81285b8 0x04801c01b640942d 0x0003807f800007f0 0x00001c03fc00003f

def z121 : W := mkw 0x5eb2da4800000000 0x02f596d240000000 0x7fb3fffc0000001f 0xb3fd9fffe0000000

def z122 : W := mkw 0x5eb3fe6c45966706 0x0af59ff3622cb338 0x7fb3fffc479e671f 0xfbfd9fffe23cf338

def z123 : W := mkw 0x0000000023445000 0x00000000011a2280 0x0000000007e07800 0x00000000003f03c0

def z124 : W := mkw 0x7fea801200000000 0x03ff540090000000 0x7fff807f8000001f 0xa3fffc03fc000000

def z125 : W := mkw 0x04b06c4805846206 0x08258362402c2310 0x0db37c7c0780601d 0x906d9be3e03c0300

def z126 : W := mkw 0x6ffc4161b35df935 0x037fe20b0d9aefc9 0xfffc0063fffff80f 0xefffe0031fffffc0

def z127 : W := mkw 0x0004018180208871 0x0000200c0c010443 0x827c83838471f8ee 0xc413e41c1c238fc7

def z128 : W := mkw 0x0000000000000000 0x0000000000000000 0x0183007c00000019 0x800c1803e0000000

def z129 : W := mkw 0x35fedb5b00000000 0x21aff6dad8000000 0x01ffffff80000018 0x100ffffffc000000

def z130 : W := mkw 0x4a00000022400000 0x0250000001120000 0xfe0000007fe00007 0xeff0000003ff0000

def z131 : W := mkw 0x7fea920000000000 0x03ff549000000000 0x7fffff800000001f 0xb3fffffc00000000

def z132 : W := mkw 0x4ea8000000000000 0x0275400000000000 0x0e3c000000000004 0x0071e00000000000

def z133 : W := mkw 0x6ffc61e1b77dfb75 0x037fe30f0dbbefdb 0xfffce3e3ffffffff 0xffffe71f1fffffff

def z134 : W := mkw 0x001461c104202a45 0x0000a30e08210152 0x0000638000000000 0x1000031c00000000

def z135 : W := mkw 0x5a03b6a0eef0aff5 0x12d01db50777857f 0xfe03ff807ff1fff7 0xfff01ffc03ff8fff

def z136 : W := mkw 0x1003a0804c2006c0 0x00801d0402610036 0xf203e3807c6007f7 0xff901f1c03e3003f

def z137 : W := mkw 0x1002801200000000 0x0080140090000000 0x0003807f80000010 0x00001c03fc000000

def z138 : W := mkw 0x00010024c0128530 0x0000080126009429 0x81c3807fc01f87fb 0xcc0e1c03fe00fc3f

def z139 : W := mkw 0x0001040441864402 0x08000820220c3220 0x00000000438e0000 0x08000000021c7000

def z140 : W := mkw 0x04b56ded45b66f47 0x0825ab6f6a2db37a 0x0fbf7ffc47fe7f1d 0xd87dfbffe23ff3f8

def z141 : W := mkw 0x7ffedb5b01044000 0x23fff6dad8082200 0x7fffffffc79e601f 0xfbfffffffe3cf300

def z142 : W := mkw 0x000124806ee006c0 0x1000092403770036 0x8c037c007fe007f5 0xdc601be003ff003f

def z143 : W := mkw 0x3143801248000480 0x018a1c0092400024 0xf1c3807ff80007fb 0xef8e1c03ffc0003f

def z144 : W := mkw 0x25e80000110d5000 0x012f400000886a80 0x01800000000e0000 0x000c000000007000

def z145 : W := mkw 0xfb43b6967eeb06c8 0x17da1db4b3f75836 0xff83ff9c7fee07f7 0xfffc1ffce3ff703f

def z146 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x01b37c7c001e6718 0x100d9be3e000f338

def z147 : W := mkw 0xb1428012980980b8 0x058a140094c04c05 0xf0408003b80180e2 0x278204001dc00c07

def z148 : W := mkw 0x7ffbfe7e45966706 0x2bffdff3f22cb338 0x7db37c7c479e671d 0xfbed9be3e23cf338

def z149 : W := mkw 0x7b43b6807ee906c0 0x13da1db403f74836 0xffc3ff807fff87ff 0xfffe1ffc03fffc3f

def z150 : W := mkw 0x001461c104202a45 0x0000a30e08210152 0x023c638004607804 0x1011e31c002303c0

def z151 : W := mkw 0xb1438016580b0488 0x058a1c00b2c05824 0x7183001c780e0001 0x2b8c1800e3c07000

def z152 : W := mkw 0x25e80000110d5000 0x012f400000886a80 0x01fc0000001ff808 0x000fe0000000ffc0

def z153 : W := mkw 0x5a16db5b00000000 0x22d0b6dad8000000 0x7e03ffff80000017 0xb3f01ffffc000000

def z154 : W := mkw 0x0010604004002204 0x0000830200200110 0x0030600004006004 0x1001830000200300

def z155 : W := mkw 0x6fe90c0c73cf5402 0x0b7f4860639e7aa0 0xffff1c1c7ffff80f 0xeffff8e0e3ffffc0

def z156 : W := mkw 0x3143803640120500 0x018a1c01b2009028 0x71c3807fc01e071b 0xeb8e1c03fe00f038

def z157 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0c337c7c07806714 0x10619be3e03c0338

def z158 : W := mkw 0x0000208004200240 0x0000010400210012 0x8200e380046007f6 0xd410071c0023003f

def z159 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0x7183807ff80e07f1 0x2b8c1c03ffc0703f

def z160 : W := mkw 0x0011646445966706 0x08008b23222cb338 0x00306060479e671c 0xd8018303023cf338

def z161 : W := mkw 0x25fc61e1953dfb75 0x012fe30f0ca9efdb 0x83fce3e3847ffffe 0xd41fe71f1c23ffff

def z162 : W := mkw 0x0014416180108130 0x0000a20b0c008409 0x827ce3e3801187fe 0xd413e71f1c008c3f

def z163 : W := mkw 0xb5e38c3ed99fc5ba 0x0daf1c61f6ccfe2d 0xfdc39c7ffb9f87fb 0xefee1ce3ffdcfc3f

def z164 : W := mkw 0x6ffc495b00000000 0x237fe24ad8000000 0x7ffc007f8000000f 0xa3ffe003fc000000

def z165 : W := mkw 0x4ebc5b4923445000 0x2275e2da491a2280 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z166 : W := mkw 0x04a12c0c45864602 0x08250960622c3230 0x0d837c1c478e0715 0xd86c1be0e23c7038

def z167 : W := mkw 0x04b0486c01166106 0x082582436008b308 0x01b0007c001e6008 0x000d8003e000f300

def z168 : W := mkw 0x7ffedb5b32491000 0x23fff6dad9924880 0xffffffffb861981f 0xb7fffffffdc30cc0

def z169 : W := mkw 0x0014616104102304 0x0000a30b08208118 0x027ce3e38410671e 0xd013e71f1c208338

def z170 : W := mkw 0x5ebedb4900000000 0x22f5f6da48000000 0x7e3fff8000000017 0xb3f1fffc00000000

def z171 : W := mkw 0x04b0484801046006 0x0825824240082300 0x0030000000006000 0x0001800000000300

def z172 : W := mkw 0xb1438016580b0488 0x058a1c00b2c05824 0xf183801c780e07f3 0xef8c1c00e3c0703f

def z173 : W := mkw 0x90028012880080b8 0x0480140094400405 0x00008003800000e0 0x000004001c000007

def z174 : W := mkw 0xffeb9a1e580b0488 0x27ff5cd0f2c05824 0x7d831c1c780e0001 0x2bec18e0e3c07000

def z175 : W := mkw 0x1013feec4cb227c6 0x18809ff76265913e 0x0003fffc000007f0 0x10001fffe000003f

def z176 : W := mkw 0x5eb3fec86fe466c6 0x1af59ff6437f2336 0xfe33ff807fe067f7 0xfff19ffc03ff033f

def z177 : W := mkw 0x5a16f3e18430ab75 0x02d0b79f0c21855b 0xfe7fffe38471ffff 0xf7f3ffff1c238fff

def z178 : W := mkw 0x7fee9b1b00000000 0x23ff74d8d8000000 0x7fcf9f9f80000003 0x23fe7cfcfc000000

def z179 : W := mkw 0xb5f3ec7edd9fe7be 0x0daf9f63f6ecff3d 0xfdf3fc7fff9fe7ff 0xffef9fe3fffcff3f

def z180 : W := mkw 0x0000208004200240 0x0000010400210012 0x827ce3800471fffe 0xd413e71c00238fff

def z181 : W := mkw 0x0001000048000480 0x0000080002400024 0x80000000780007e0 0x4c00000003c0003f

def z182 : W := mkw 0x6fec0181b36dd871 0x037f600c0d9b6ec3 0xfffc8383fffff8ef 0xefffe41c1fffffc7

def z183 : W := mkw 0x3142803280108130 0x018a140194008409 0xf1c3807f801187fb 0xe78e1c03fc008c3f

def z184 : W := mkw 0x6ffc61c1376d7a45 0x037fe30e09bb6bd2 0xfffc63807ffff80f 0xffffe31c03ffffc0

def z185 : W := mkw 0x4ebc5b4900000000 0x2275e2da48000000 0x0e7cffe38000001e 0x9073e7ff1c000000

def z186 : W := mkw 0x7b5edb5b00000000 0x23daf6dad8000000 0x724fffff80000012 0x33927ffffc000000

def z187 : W := mkw 0xa1400036901b8138 0x050a0001b480dc09 0x01c0007f801f8008 0x000e0003fc00fc00

def z188 : W := mkw 0xda03b6b6eef287f8 0x16d01db5b777943f 0xfe03ffffffe007f7 0xfff01fffffff003f

def z189 : W := mkw 0x04b16cec45b66746 0x08258b67622db33a 0x8fb3fffc47fe67ff 0xdc7d9fffe23ff33f

def z190 : W := mkw 0x25e00000110d4000 0x012f000000886a00 0xfdf000007f9fe00f 0xefef800003fcff00

def z191 : W := mkw 0x7feb80007b4d5480 0x03ff5c0003da6aa4 0xffff80007fffffff 0xeffffc0003ffffff

def z192 : W := mkw 0x0010606004102304 0x0000830300208118 0x003060600410671c 0xd001830300208338

def z193 : W := mkw 0x0000000000000000 0x0000000000000000 0x80008000000007f2 0xc40004000000003f

def z194 : W := mkw 0x000020a0b77dfb75 0x0000010505bbefdb 0x800000007fffffe0 0x4c00000003ffffff

def z195 : W := mkw 0x5a03b6a0eef087f0 0x12d01db50777843f 0xfe43ffe3fff187ff 0xfff21fff1fff8c3f

def z196 : W := mkw 0x4ea8000023445000 0x02754000011a2280 0x8e7c000007f1f80e 0xc473e000003f8fc0

def z197 : W := mkw 0x0014495b00000000 0x2000a24ad8000000 0x0000007f80000000 0x00000003fc000000

def z198 : W := mkw 0xfb4396167acb0488 0x17da1cb0b3d65824 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z199 : W := mkw 0x04b06c4805846206 0x08258362402c2310 0x0db07c00479e600d 0xd86d83e0023cf300

def z200 : W := mkw 0x0000200004000200 0x0000010000200010 0x0000600004000714 0xd000030000200038

def z201 : W := mkw 0x04b14c4c41864402 0x08258a62620c3220 0x0db37c7c438e001d 0x986d9be3e21c7000

def z202 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7e7cff8380000006 0x33f3e7fc1c000000

def z203 : W := mkw 0xfb4a8012ba4990b8 0x07da540095d24c85 0xf24c8003b86198e2 0x279264001dc30cc7

def z204 : W := mkw 0x7ffedb5b23445000 0x23fff6dad91a2280 0x7fffffff87e0781f 0xb3fffffffc3f03c0

def z205 : W := mkw 0x5a02920000000000 0x02d0149000000000 0x7c031c0000000001 0x23e018e000000000

def z206 : W := mkw 0x000020a08430ab75 0x000001050421855b 0x804080638471fffa 0xc40204031c238fff

def z207 : W := mkw 0x25fc495b00000000 0x212fe24ad8000000 0x03fce3ff8000001e 0x901fe71ffc000000

def z208 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7d83ffff80000011 0x33ec1ffffc000000

def z209 : W := mkw 0x04a10c2c41964502 0x08250861620cb228 0x0d831c7c439e0719 0xc86c18e3e21cf038

def z210 : W := mkw 0x000124a46ff667c6 0x18000925237fb33e 0x800000007ffe67e0 0x4c00000003fff33f

def z211 : W := mkw 0x4a01240066c00600 0x0250092003360030 0xfe037c007fe00717 0xfff01be003ff0038

def z212 : W := mkw 0x25f8486c111f7106 0x092fc2436088fb88 0x01fc007c001ff808 0x000fe003e000ffc0

def z213 : W := mkw 0x4a00368026e00240 0x125001b401370012 0x0e007f8007e00004 0x107003fc003f0000

def z214 : W := mkw 0x9003b6b6ccb287f8 0x14801db5b665943f 0x0003ffff800007f0 0x10001ffffc00003f

def z215 : W := mkw 0x0000002080108130 0x0000000104008409 0x80000000001187e0 0x4400000000008c3f

def z216 : W := mkw 0x001461c104200240 0x0000a30e08210012 0x827ce3e3846007fe 0xd413e71f1c23003f

def z217 : W := mkw 0x4a00208026600240 0x0250010401330012 0xfe00e3807fe007f7 0xfff0071c03ff003f

def z218 : W := mkw 0x7fea9a1a334d5000 0x23ff54d0d19a6a80 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z219 : W := mkw 0x04a0080c01064002 0x0825004060083200 0x0180001c000e0000 0x000c0000e0007000

def z220 : W := mkw 0x04b0686804102304 0x0025834340208118 0x0db37c7c0410671d 0xd06d9be3e0208338

def z221 : W := mkw 0xb5ffc97fd81b85b8 0x25affe4bfec0dc2d 0xf1ff807ff81f87fb 0xef8ffc03ffc0fc3f

def z222 : W := mkw 0x2140002090198130 0x010a00010480cc09 0xf1c08063f81f87fb 0xef8e04031fc0fc3f

def z223 : W := mkw 0x3142801200000000 0x018a140090000000 0x7183001c00000001 0x238c1800e0000000

def z224 : W := mkw 0x5a02920000000000 0x02d0149000000000 0x7e03ff8000000017 0xb3f01ffc00000000

def z225 : W := mkw 0x000020a08430ab75 0x000001050421855b 0x8200e3800471fff6 0xd410071c00238fff

def z226 : W := mkw 0x001565e1eef0aff5 0x1000ab2f0f77857f 0x827ce3e3fff1fffe 0xdc13e71f1fff8fff

def z227 : W := mkw 0xda03b6a4fefb87f8 0x16d01db527f7dc3f 0xfe03ff807fff87f7 0xfff01ffc03fffc3f

def z228 : W := mkw 0x4ebc7f4905846206 0x2a75e3fa482c2310 0x0e3c7f8007806004 0x1071e3fc003c0300

def z229 : W := mkw 0xa1410024d81b85b8 0x050a080126c0dc2d 0xf1c00000781f87eb 0xef8e000003c0fc3f

def z230 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0x0ffc000007fff80c 0x007fe000003fffc0

def z231 : W := mkw 0x7b42921200000000 0x03da149090000000 0x7fc3ffff8000001f 0xb3fe1ffffc000000

def z232 : W := mkw 0x04b16c6cc596e736 0x08258b63662cb739 0x8df3fc7fc79fe7ff 0xdc6f9fe3fe3cff3f

def z233 : W := mkw 0x1006931300000000 0x2080349898000000 0x0000838380000000 0x0000041c1c000000

def z234 : W := mkw 0x1002920000000000 0x0080149000000000 0x0003ff8000000010 0x10001ffc00000000

def z235 : W := mkw 0x2140001200000000 0x010a000090000000 0x01c0007f80000008 0x000e0003fc000000

def z236 : W := mkw 0x0001242444920700 0x0000092122249038 0x0d837c7c479e071d 0xd86c1be3e23cf038

def z237 : W := mkw 0x00116c6c45966706 0x08008b63622cb338 0x00037c7c479e6710 0x58001be3e23cf338

def z238 : W := mkw 0x5eabb6806fe456c0 0x12f55db4037f22b6 0xfe3fff807fe07ff7 0xfff1fffc03ff03ff

def z239 : W := mkw 0x5eb7ffedeff6eff7 0x1af5bfff6f7fb77f 0xffffffffffffffff 0xffffffffffffffff

def z240 : W := mkw 0x04a0000000000000 0x0025000000000000 0x0db000000000000d 0x806d800000000000

def z241 : W := mkw 0x04bc494900000000 0x2025e24a48000000 0x003c000000000000 0x0001e00000000000

def z242 : W := mkw 0xffeb80167b4f5488 0x07ff5c00b3da7aa4 0x7d83001c7b8e0001 0x2bec1800e3dc7000

def z243 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0x7ffc00007b8e000f 0xabffe00003dc7000

def z244 : W := mkw 0x0001240044800600 0x0000092002240030 0x0000000047800700 0x48000000023c0038

def z245 : W := mkw 0x4ea0000023444000 0x02750000011a2200 0xffb000007ffe600f 0xeffd800003fff300

def z246 : W := mkw 0x7fffffdb7fed56c0 0x33fffffedbff6ab6 0xffffffffffffffff 0xffffffffffffffff

def z247 : W := mkw 0x6ffc5b5b00000000 0x237fe2dad8000000 0x0ffc7fff8000000c 0x107fe3fffc000000

def z248 : W := mkw 0x00000000334d5000 0x00000000019a6a80 0x000000007b8e0000 0x0800000003dc7000

def z249 : W := mkw 0x7fee931300000000 0x23ff749898000000 0x7ffc83838000000f 0xa3ffe41c1c000000

def z250 : W := mkw 0x6fe8000032491000 0x037f400001924880 0xfffc00003861980f 0xa7ffe00001c30cc0

def z251 : W := mkw 0x000020a08430ab75 0x000001050421855b 0x00000000000007e0 0x000000000000003f

def z252 : W := mkw 0x0014414100000000 0x0000a20a08000000 0x0000e3e380000010 0x1000071f1c000000

def z253 : W := mkw 0x0000000000000000 0x0000000000000000 0x003000000410600c 0xc001800000208300

def z254 : W := mkw 0x04a0000001044000 0x0025000000082200 0x8ffc000047fff80f 0xcc7fe000023fffc0

def z255 : W := mkw 0x0000000000000000 0x0000000000000000 0x004080638000001a 0x800204031c000000

def z256 : W := mkw 0xb143a0b6dc3baffd 0x058a1d05b6e1dd7f 0xf1c3807ffc7ffffb 0xef8e1c03ffe3ffff

def z257 : W := mkw 0x04a12c2c45966706 0x08250961622cb338 0x0d831c1c479e6701 0x486c18e0e23cf338

def z258 : W := mkw 0x5a02b2802e6002c0 0x12d0159401730016 0xf200e3803c6007f6 0xf790071c01e3003f

def z259 : W := mkw 0x0001000440020400 0x0000080022001020 0x0183001c400e0001 0x080c1800e2007000

def z260 : W := mkw 0xa5fc497f901b8138 0x252fe24bfc80dc09 0x01fc007f801f8008 0x000fe003fc00fc00

def z261 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xffcc00007bef9803 0x2ffe600003df7cc0

def z262 : W := mkw 0x00116c6c44922706 0x08008b6362249138 0x0c037c7c47800715 0xd8601be3e23c0038

def z263 : W := mkw 0x4a0124806ee006c0 0x1250092403770036 0xfe0000007fe007e7 0xeff0000003ff003f

def z264 : W := mkw 0x7b43b6926ee006c0 0x13da1db493770036 0xffc3ffffffe007ff 0xfffe1fffffff003f

def z265 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200e38000000016 0x9010071c00000000

def z266 : W := mkw 0x7feb9e1e41864402 0x2bff5cf0f20c3220 0x7d831c1c438e0001 0x2bec18e0e21c7000

def z267 : W := mkw 0x5a069381aa6088f1 0x12d0349c0d530447 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z268 : W := mkw 0x0014414100000000 0x0000a20a08000000 0x827ce3e38471f81e 0xd413e71f1c238fc0

def z269 : W := mkw 0x04a1002441164500 0x002508012208b228 0x0db3007c479e671d 0xc86d9803e23cf338

def z270 : W := mkw 0x7ffefbdb04202a45 0x23fff7ded8210152 0x7fffffff8460781f 0xb3fffffffc2303c0

def z271 : W := mkw 0xb14781b7d83b8df9 0x058a3c0dbec1dc6f 0xf3cf83fff87f9ffb 0xef9e7c1fffc3fcff

def z272 : W := mkw 0x04b1486c40120500 0x00258a4362009028 0x0db37c7c401e071d 0xd86d9be3e200f038

def z273 : W := mkw 0x5ea3be8c6fe646c2 0x1af51df4637f3236 0xff83ff9c7fee07f7 0xfffc1ffce3ff703f

def z274 : W := mkw 0x10029a1a00000000 0x208014d0d0000000 0x00031c1c00000000 0x000018e0e0000000

def z275 : W := mkw 0xffeb9a3ed81b85b8 0x27ff5cd1f6c0dc2d 0xfdc39c7ff81f87fb 0xefee1ce3ffc0fc3f

def z276 : W := mkw 0xffeb8036fb5fd5b8 0x07ff5c01b7dafead 0xffff807fffffffff 0xeffffc03ffffffff

def z277 : W := mkw 0x0000000000000000 0x0000000000000000 0x8200000004600006 0xc410000000230000

def z278 : W := mkw 0x7fffdf5b6ac00480 0x33fffefadb560024 0x7ffffffffb80001f 0xbbffffffffdc0000

def z279 : W := mkw 0x6ff8484800000000 0x037fc24240000000 0x7fff7c7c0000001f 0xb3fffbe3e0000000

def z280 : W := mkw 0x94b3ec7ecd96e7be 0x0ca59f63f66cb73d 0x0db3fc7fc79e67fd 0xd86d9fe3fe3cf33f

def z281 : W := mkw 0x00000000110d5000 0x0000000000886a80 0x00000000001ff800 0x000000000000ffc0

def z282 : W := mkw 0x6ff96c6c77df7706 0x0b7fcb6363befbb8 0x7db37c7c7f9e671d 0xfbed9be3e3fcf338

def z283 : W := mkw 0x0001242445966706 0x08000921222cb338 0x0c037c00479e6715 0xd8601be0023cf338

def z284 : W := mkw 0x04a0000001044000 0x0025000000082200 0x01b00000001e6008 0x000d80000000f300

def z285 : W := mkw 0x0004018180208871 0x0000200c0c010443 0x824c8383806198e2 0x0412641c1c030cc7

def z286 : W := mkw 0xfb439636fadb85b8 0x17da1cb1b7d6dc2d 0xfdc39c7ffb9f87fb 0xefee1ce3ffdcfc3f

def z287 : W := mkw 0x800124a4fefb87f8 0x1400092527f7dc3f 0x800000007fff87e0 0x4c00000003fffc3f

def z288 : W := mkw 0x1016fbfb8430ab75 0x2080b7dfdc21855b 0x827fffff8471fffe 0xd413fffffc238fff

def z289 : W := mkw 0x04b46dc905a46a47 0x0825a36e482d2352 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z290 : W := mkw 0xb1438016580b0488 0x058a1c00b2c05824 0x71c3807ff80e001b 0xab8e1c03ffc07000

def z291 : W := mkw 0x04b469ed8536eb77 0x0825a34f6c29b75b 0x83fce3ff847ffffe 0xd41fe71ffc23ffff

def z292 : W := mkw 0x5a03920048000480 0x02d01c9002400024 0xfe03ff80780007f7 0xfff01ffc03c0003f

def z293 : W := mkw 0x800120a4dc3baffd 0x0400090526e1dd7f 0x800000007c7fffe0 0x4c00000003e3ffff

def z294 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z295 : W := mkw 0x04b06c6805946306 0x08258363402ca318 0x0c307c600790671c 0xd06183e3003c8338

def z296 : W := mkw 0x9017e1f7cc32affd 0x0480bf0fbe61957f 0x827fe3ff8471fffe 0xd413ff1ffc238fff

def z297 : W := mkw 0x7ffada5a00000000 0x23ffd6d2d0000000 0x7db37c7c0000001d 0xb3ed9be3e0000000

def z298 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x8fff7c7c47ffff1f 0xdc7ffbe3e23ffff8

def z299 : W := mkw 0x4ebc7bc904202a45 0x2275e3de48210152 0x0e3c7f8004607804 0x1071e3fc002303c0

def z300 : W := mkw 0xffea8012bb4dd0b8 0x07ff540095da6e85 0xfffc8003fffff8ef 0xefffe4001fffffc7

def z301 : W := mkw 0xb1438036fb5fd5b8 0x058a1c01b7dafead 0xf1c3807ffffffffb 0xef8e1c03ffffffff

def z302 : W := mkw 0x6b48000032491000 0x035a400001924880 0xf27c00003c71f80e 0xe793e00001e38fc0

def z303 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0x01c3807f801f87f8 0x000e1c03fc00fc3f

def z304 : W := mkw 0x04b16c6c44922706 0x08258b6362249138 0x0db37c7c0000071d 0x906d9be3e0000038

def z305 : W := mkw 0x001461c104202a45 0x0000a30e08210152 0x827c63800471f80e 0xd413e31c00238fc0

def z306 : W := mkw 0x1003800048000480 0x00801c0002400024 0x7003000078000001 0x2b80180003c00000

def z307 : W := mkw 0x04b56d6d45966706 0x0825ab6b6a2cb338 0x0fffffffc79e671f 0xd87ffffffe3cf338

def z308 : W := mkw 0x1003b6804ca006c0 0x10801db402650036 0x0003ff80000007f0 0x10001ffc0000003f

def z309 : W := mkw 0x25f96c6c559f7706 0x092fcb6362acfbb8 0x0dff7c7c479fff1d 0xd86ffbe3e23cfff8

def z310 : W := mkw 0x7b5ed35300000000 0x23daf69a98000000 0x727ce3e38000001e 0xb393e71f1c000000

def z311 : W := mkw 0x2140000010090000 0x010a000000804800 0xf1c00000781f800b 0xef8e000003c0fc00

def z312 : W := mkw 0x0001240044800600 0x0000092002240030 0x00037c0000000710 0x10001be000000038

def z313 : W := mkw 0x5a02920000000000 0x02d0149000000000 0x7200838000000002 0x2390041c00000000

def z314 : W := mkw 0xb5f3c87ed81b85b8 0x05af9e43f6c0dc2d 0xfdf3fc7ff81f87ff 0xffef9fe3ffc0fc3f

def z315 : W := mkw 0x5a0396006ac00480 0x12d01cb003560024 0x7e03ff807b800017 0xbbf01ffc03dc0000

def z316 : W := mkw 0x5a07b781eee08ef1 0x12d03dbc0f770477 0xfe4fff83ffe19ff7 0xfff27ffc1fff0cff

def z317 : W := mkw 0x1017e1e1cc30aff5 0x0080bf0f0e61857f 0xf27fe3e3fc71ffff 0xff93ff1f1fe38fff

def z318 : W := mkw 0x4a00368026e00240 0x125001b401370012 0xfe007f807fe00007 0xfff003fc03ff0000

def z319 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0x7fbc00007fee7805 0x2bfde00003ff73c0

def z320 : W := mkw 0x2140000010090000 0x010a000000804800 0xf3fc00007c7ff80f 0xef9fe00003e3ffc0

def z321 : W := mkw 0xffeb8036fb5fd5b8 0x07ff5c01b7dafead 0xfdc3807ffb9f87fb 0xefee1c03ffdcfc3f

def z322 : W := mkw 0x0000002080108130 0x0000000104008409 0x00008063800007f0 0x000004031c00003f

def z323 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf183001c781f87e1 0x6f8c1800e3c0fc3f

def z324 : W := mkw 0xa1544177901ba93d 0x050aa20bbc80dd49 0x01fc007f801ff808 0x000fe003fc00ffc0

def z325 : W := mkw 0x7fffff7f44922706 0x2bfffffbfa249138 0x7fffffff8000071f 0xb3fffffffc000038

def z326 : W := mkw 0x7ffefbfbb77dfb75 0x23fff7dfddbbefdb 0xffffffffffffffff 0xffffffffffffffff

def z327 : W := mkw 0x000124806ee006c0 0x1000092403770036 0x8200e3807fe007f6 0xdc10071c03ff003f

def z328 : W := mkw 0x00116c6c44922706 0x08008b6362249138 0x01837c7c401e0719 0xd80c1be3e200f038

def z329 : W := mkw 0x1003b6804ca006c0 0x10801db402650036 0xf003ff80780007f3 0xff801ffc03c0003f

def z330 : W := mkw 0x0001002440120500 0x0000080122009028 0x0003007c00000710 0x00001803e0000038

def z331 : W := mkw 0x7b4a92803a6910c0 0x13da549401d34886 0xf24c8380386198e2 0x2792641c01c30cc7

def z332 : W := mkw 0xffebb6b6ffffd7f8 0x17ff5db5b7fffebf 0xffffffffffffffff 0xffffffffffffffff

def z333 : W := mkw 0x04b56d6dc596ef37 0x0825ab6b6e2cb779 0x0dff7c7fc79fff1d 0xd86ffbe3fe3cfff8

def z334 : W := mkw 0xfb4392b6fa7b85f8 0x17da1c95b7d3dc2f 0xf3c383fff87f87fb 0xef9e1c1fffc3fc3f

def z335 : W := mkw 0x04b14c6c41966506 0x08258a63620cb328 0x0db31c7c439e6009 0x086d98e3e21cf300

def z336 : W := mkw 0x14b6db5b00000000 0x20a5b6dad8000000 0x0db3ffff8000001d 0x906d9ffffc000000

def z337 : W := mkw 0xb143a4b6fefb87f8 0x158a1d25b7f7dc3f 0xf1c3807fffff87fb 0xef8e1c03fffffc3f

def z338 : W := mkw 0x04a1242445966706 0x08250921222cb338 0x0db00000479e670d 0xc86d8000023cf338

def z339 : W := mkw 0x4eb96c6c67d67706 0x0a75cb63633eb3b8 0x0fbf7c7c47fe7f1d 0xd87dfbe3e23ff3f8

def z340 : W := mkw 0x6fe8000010090000 0x037f400000804800 0xfffc0000781f800f 0xefffe00003c0fc00

def z341 : W := mkw 0x00156dedc4b2af77 0x0800ab6f6e25957b 0x0003ffff800007f0 0x10001ffffc00003f

def z342 : W := mkw 0x7ffedb5b110d5000 0x23fff6dad8886a80 0x7fffffff801ff81f 0xb3fffffffc00ffc0

def z343 : W := mkw 0x04b16c6c77df7706 0x08258b6363befbb8 0x8db37c7c7fffff1d 0xdc6d9be3e3fffff8

def z344 : W := mkw 0x00145b4900000000 0x2000a2da48000000 0x00007f8000000000 0x100003fc00000000

def z345 : W := mkw 0x0001242445966706 0x08000921222cb338 0x0183007c479e6719 0xc80c1803e23cf338

def z346 : W := mkw 0x0000240004800200 0x0000012000240010 0x0c007c0007800004 0x106003e0003c0000

def z347 : W := mkw 0x000124807fed56c0 0x1000092403ff6ab6 0x800000007fffffe0 0x4c00000003ffffff

def z348 : W := mkw 0x7ffedb5b10090000 0x23fff6dad8804800 0xfffffffff81f801f 0xffffffffffc0fc00

def z349 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfc031c007fe007e1 0x6fe018e003ff003f

def z350 : W := mkw 0xb1428012980980b8 0x058a140094c04c05 0xf1c3807fb80180fb 0xa78e1c03fdc00c07

def z351 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x007ce3e38011fff8 0x1003e71f1c008fff

def z352 : W := mkw 0x25e80000110d5000 0x012f400000886a80 0xf1fc0000781ff80b 0xef8fe00003c0ffc0

def z353 : W := mkw 0x7febb6806ee006c0 0x13ff5db403770036 0xffffff807fe007ff 0xfffffffc03ff003f

def z354 : W := mkw 0x5a03b6807fed56c0 0x12d01db403ff6ab6 0xfe03ff807ffffff7 0xfff01ffc03ffffff

def z355 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf0408003f81f87e2 0x6f8204001fc0fc3f

def z356 : W := mkw 0xffeb8036d81b85b8 0x07ff5c01b6c0dc2d 0xffff807ff81f87ff 0xeffffc03ffc0fc3f

def z357 : W := mkw 0x25f16c6c559f6706 0x092f8b6362acfb38 0xfdf37c7c7f9fe71f 0xffef9be3e3fcff38

def z358 : W := mkw 0x6ffc4141334d5000 0x037fe20a099a6a80 0xfffce3e3fffff81f 0xffffe71f1fffffc0

def z359 : W := mkw 0x5a16d34100000000 0x02d0b69a08000000 0x7e7fffe38000001f 0xb3f3ffff1c000000

def z360 : W := mkw 0x4a00000022400000 0x0250000001120000 0x7c0000007b800001 0x2be0000003dc0000

def z361 : W := mkw 0x4a0c130100000000 0x2250609808000000 0x020c038000000000 0x0010601c00000000

def z362 : W := mkw 0x4a00120000000000 0x0250009000000000 0x0e007f8000000004 0x107003fc00000000

def z363 : W := mkw 0x6fe9240077cd5600 0x037f492003be6ab0 0xffff7c007fffff1f 0xfffffbe003fffff8

def z364 : W := mkw 0x04a1240045844600 0x00250920022c2230 0x0db37c00479e671d 0xd86d9be0023cf338

def z365 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x807c00638471ffe8 0x4403e0031c238fff

def z366 : W := mkw 0x1017ffdb4ca006c0 0x3080bffeda650036 0x0003ffff800007f0 0x10001ffffc00003f

def z367 : W := mkw 0x6ffd6dedf7ffff77 0x0b7feb6f6fbffffb 0xffffffffffffffff 0xffffffffffffffff

def z368 : W := mkw 0x6fe8000001044000 0x037f400000082200 0x7ffc0000479e600f 0xebffe000023cf300

def z369 : W := mkw 0x001461c104202a45 0x0000a30e08210152 0x823ce38004607ff6 0xd411e71c002303ff

def z370 : W := mkw 0xb157db7fd81b85b8 0x258abedbfec0dc2d 0xf1c3fffff81f87fb 0xff8e1fffffc0fc3f

def z371 : W := mkw 0x6ffc5b4900000000 0x237fe2da48000000 0x7ffc7f800000000f 0xb3ffe3fc00000000

def z372 : W := mkw 0xb5f7edffddbfefff 0x0dafbf6ffeedff7f 0xffffffffffffffff 0xffffffffffffffff

def z373 : W := mkw 0x6ff86c4837cd7206 0x0b7fc36241be6b90 0xfffc7c007ffff80f 0xffffe3e003ffffc0

def z374 : W := mkw 0xefe90024fb5fd5b8 0x077f480127dafead 0xfffc00007fffffef 0xefffe00003ffffff

def z375 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0db31c1c479e600d 0xc86d98e0e23cf300

def z376 : W := mkw 0x5a0392806a6004c0 0x12d01c9403530026 0xf2038380786007f3 0xef901c1c03c3003f

def z377 : W := mkw 0x4a1461e1a670ab75 0x0250a30f0d33855b 0xfe7ce3e3fff1ffff 0xfff3e71f1fff8fff

def z378 : W := mkw 0x6fe90c0c73cf5402 0x0b7f4860639e7aa0 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z379 : W := mkw 0xa5e80036911fd138 0x052f4001b488fe89 0x01fc007f801ff808 0x000fe003fc00ffc0

def z380 : W := mkw 0x7ffff7e1fffdfff5 0x13ffffbf0fffefff 0xffffffe3ffffffff 0xffffffff1fffffff

def z381 : W := mkw 0x04b0686c05166306 0x082583436028b318 0x01b0607c041e671c 0xd00d8303e020f338

def z382 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x824ce3e380619ff2 0x1412671f1c030cff

def z383 : W := mkw 0x0001242444922706 0x0800092122249138 0x0000000000000700 0x0000000000000038

def z384 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfe7c00003fe1f806 0x27f3e00001ff0fc0

def z385 : W := mkw 0x1003b6806ee006c0 0x10801db403770036 0x8003ff807fe007f0 0x5c001ffc03ff003f

def z386 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x823c63800471ffe4 0x5411e31c00238fff

def z387 : W := mkw 0x001461e1b77dfb75 0x0000a30f0dbbefdb 0x827ce3e3fffffffe 0xdc13e71f1fffffff

def z388 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x027fffff8000001e 0x9013fffffc000000

def z389 : W := mkw 0x00000000334d5000 0x00000000019a6a80 0x827c00007ffff80e 0xcc13e00003ffffc0

def z390 : W := mkw 0x25fc495b110d5000 0x212fe24ad8886a80 0x01fc007f801ff808 0x000fe003fc00ffc0

def z391 : W := mkw 0x1017ff7f44922706 0x2880bffbfa249138 0x0003ffff80000710 0x10001ffffc000038

def z392 : W := mkw 0x90038024d81b85b8 0x04801c0126c0dc2d 0xf0038000781f87f3 0xef801c0003c0fc3f

def z393 : W := mkw 0x04b469e98430ab75 0x0025a34f4c21855b 0x8fffffff8471ffff 0xd47ffffffc238fff

def z394 : W := mkw 0x6ff84848334d5000 0x037fc242419a6a80 0xffff7c7c7ffff81f 0xfffffbe3e3ffffc0

def z395 : W := mkw 0x4eb16c6c67d66706 0x0a758b63633eb338 0xffb37c7c7ffe671f 0xfffd9be3e3fff338

def z396 : W := mkw 0x5a03b60044800600 0x02d01db002240030 0x7e03ff8047800717 0xfbf01ffc023c0038

def z397 : W := mkw 0x25e80000334d5000 0x012f4000019a6a80 0x81fc00007ffff808 0x4c0fe00003ffffc0

def z398 : W := mkw 0xa1400016100b0008 0x050a0000b0805800 0x0180001c000e0000 0x000c0000e0007000

def z399 : W := mkw 0x1003b6804ca006c0 0x10801db402650036 0x8203ff80046007f6 0xd4101ffc0023003f

def z400 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xf3fc0000387ff80a 0x279fe00001c3ffc0

def z401 : W := mkw 0x4ebc7fc926e00240 0x3275e3fe49370012 0x0e3c7f8007e00004 0x1071e3fc003f0000

def z402 : W := mkw 0xb1438012d80984b8 0x058a1c0096c04c25 0xf0438003f80187f3 0xef821c001fc00c3f

def z403 : W := mkw 0x1002800008000080 0x0080140000400004 0xf0008000380000e2 0x2780040001c00007

def z404 : W := mkw 0xfb4b8036fa5b95b8 0x07da5c01b7d2dcad 0xf3cf807ff87f9ffb 0xef9e7c03ffc3fcff

def z405 : W := mkw 0x7febb6807fed56c0 0x13ff5db403ff6ab6 0xff83ff807fee07f7 0xfffc1ffc03ff703f

def z406 : W := mkw 0x5ea3b6806fe446c0 0x12f51db4037f2236 0xffb3ff807ffe67ff 0xfffd9ffc03fff33f

def z407 : W := mkw 0x3143800058090480 0x018a1c0002c04824 0xf1c38000781f87fb 0xef8e1c0003c0fc3f

def z408 : W := mkw 0xfffedb5b980980b8 0x27fff6dadcc04c05 0xffffffffb80180ff 0xb7fffffffdc00c07

def z409 : W := mkw 0x001461c104202a45 0x0000a30e08210152 0x027ce3e38460781e 0x9013e71f1c2303c0

def z410 : W := mkw 0x04b0486c01166106 0x082582436008b308 0x0db37c7c001e601d 0x906d9be3e000f300

def z411 : W := mkw 0x80010024fb5fd5b8 0x0400080127dafead 0x800000007fffffe0 0x4c00000003ffffff

def z412 : W := mkw 0x7ffefb7b04102304 0x23fff7dbd8208118 0x7fffffff8410671f 0xf3fffffffc208338

def z413 : W := mkw 0x25e80000110d5000 0x012f400000886a80 0x83fc0000047ff80e 0xc41fe0000023ffc0

def z414 : W := mkw 0x0014414100000000 0x0000a20a08000000 0x023c638000000004 0x1011e31c00000000

def z415 : W := mkw 0x0011606444122704 0x00008b0322209138 0x01b3607c441e671d 0xd80d9b03e220f338

def z416 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7dff1c7f80000009 0x23eff8e3fc000000

def z417 : W := mkw 0x001441e18030a975 0x0000a20f0c01854b 0x827c83e38071f8ea 0x0413e41f1c038fc7

def z418 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x027c63e38471f80c 0x1013e31f1c238fc0

def z419 : W := mkw 0x7fffdb5b48000480 0x23fffedada400024 0xfffffffff80007ff 0xffffffffffc0003f

def z420 : W := mkw 0x90038036d81b85b8 0x04801c01b6c0dc2d 0x8003807ff81f87f0 0x4c001c03ffc0fc3f

def z421 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0x71c3007ff81f8009 0x2b8e1803ffc0fc00

def z422 : W := mkw 0x00156dedc4b2af77 0x0800ab6f6e25957b 0x827fffff8471fffe 0xd413fffffc238fff

def z423 : W := mkw 0x001441618010a935 0x0000a20b0c008549 0x0000006380000000 0x000000031c000000

def z424 : W := mkw 0x7ffedb5b22400000 0x23fff6dad9120000 0xffffffffffe0001f 0xffffffffffff0000

def z425 : W := mkw 0x0000000032491000 0x0000000001924880 0x8000000038619800 0x0400000001c30cc0

def z426 : W := mkw 0x1002800000000000 0x0080140000000000 0x7003800000000013 0xa3801c0000000000

def z427 : W := mkw 0x5a17f7c16ee02ec5 0x12d0bfbe0b770176 0xfe3fff807fe07ff7 0xfff1fffc03ff03ff

def z428 : W := mkw 0x90038036c81285b8 0x04801c01b640942d 0xf003807ff80007f3 0xef801c03ffc0003f

def z429 : W := mkw 0x0000002080108130 0x0000000104008409 0x0040006380118008 0x000200031c008c00

def z430 : W := mkw 0x4ea81a0800000000 0x227540d040000000 0x0c001c0000000000 0x006000e000000000

def z431 : W := mkw 0xb143b6b6dcbb87f8 0x158a1db5b6e5dc3f 0xf1c3fffff81f87fb 0xff8e1fffffc0fc3f

def z432 : W := mkw 0x4a00128022600040 0x1250009401130002 0x0200038000600000 0x0010001c00030000

def z433 : W := mkw 0x0000208004202a45 0x0000010400210152 0x0000000004607800 0x00000000002303c0

def z434 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xf20083807fe007e2 0x6f90041c03ff003f

def z435 : W := mkw 0x04b16c4845846606 0x08258b62422c2330 0x0c337c0047806715 0xd8619be0023c0338

def z436 : W := mkw 0x4ea80000334d5000 0x02754000019a6a80 0x8e3c00007ffff804 0x4c71e00003ffffc0

def z437 : W := mkw 0x6fe8000023445000 0x037f4000011a2280 0x7ffc000007e0780f 0xa3ffe000003f03c0

def z438 : W := mkw 0x04b16c4c45866606 0x08258b62622c3330 0x0db37c1c478e6005 0x186d9be0e23c7300

def z439 : W := mkw 0x0000002400120100 0x0000000120009008 0x0180007c001e0008 0x000c0003e000f000

def z440 : W := mkw 0x000401a180308971 0x0000200d0c01844b 0x824c83e380719ffa 0xc412641f1c038cff

def z441 : W := mkw 0x0010484800000000 0x0000824240000000 0x00037c7c00000010 0x10001be3e0000000

def z442 : W := mkw 0x7fea8012334d5000 0x03ff5400919a6a80 0xffff807ffffff81f 0xeffffc03ffffffc0

def z443 : W := mkw 0x25e8081a00000000 0x212f4040d0000000 0x0180001c00000000 0x000c0000e0000000

def z444 : W := mkw 0x5eb3fec86ee006c0 0x12f59ff643770036 0xffb3fffc7fe007ff 0xfffd9fffe3ff003f

def z445 : W := mkw 0xb1428036901b8138 0x058a1401b480dc09 0x71c3807f801f801b 0xa38e1c03fc00fc00

def z446 : W := mkw 0x3142801210090000 0x018a140090804800 0xf1c3807ff81f801b 0xef8e1c03ffc0fc00

def z447 : W := mkw 0x4ebc7be98430ab75 0x2275e3df4c21855b 0x8e7cffe38471fffe 0xd473e7ff1c238fff

def z448 : W := mkw 0x04b0606005146304 0x002583030028a318 0x0db06060479e671d 0xd86d8303023cf338

def z449 : W := mkw 0x7fea9200334d5000 0x03ff5490019a6a80 0xffffff807ffff81f 0xfffffffc03ffffc0

def z450 : W := mkw 0x4ebd7f6d45966706 0x2a75ebfb6a2cb338 0x0fbf7ffc479e671d 0xd87dfbffe23cf338

def z451 : W := mkw 0x10038020c81085b0 0x00801c010640842d 0xf0438063f81187fb 0xef821c031fc08c3f

def z452 : W := mkw 0x7fffff5b44800600 0x23fffffada240030 0x7fffffffc780071f 0xfbfffffffe3c0038

def z453 : W := mkw 0x5a0292802a6000c0 0x12d0149401530006 0xfe0083807fe000e7 0xeff0041c03ff0007

def z454 : W := mkw 0x7b5ef3f38430ab75 0x23daf79f9c21855b 0xf27ce3e38471fffe 0xf793e71f1c238fff

def z455 : W := mkw 0x7fea9a1a00000000 0x23ff54d0d0000000 0x7fff1c1c0000000f 0xa3fff8e0e0000000

def z456 : W := mkw 0xfffffbffdc3baffd 0x27ffffdffee1dd7f 0xfffffffffc7fffff 0xffffffffffe3ffff

def z457 : W := mkw 0x00010c0c40820402 0x0800086062041020 0x00031c1c00000000 0x000018e0e0000000

def z458 : W := mkw 0x7fea9a1a00000000 0x23ff54d0d0000000 0x7dc39c7f8000001b 0xa3ee1ce3fc000000

def z459 : W := mkw 0x6fe924807fed56c0 0x137f492403ff6ab6 0xfffc00007fffffef 0xefffe00003ffffff

def z460 : W := mkw 0x7b4a921200000000 0x23da549090000000 0x7000000000000000 0x2380000000000000

def z461 : W := mkw 0x25fc69fb8430ab75 0x212fe34fdc21855b 0x83fce3ff8471fffe 0xd41fe71ffc238fff

def z462 : W := mkw 0x0000002080108130 0x0000000104008409 0x827c80638471fffe 0xc413e4031c238fff

def z463 : W := mkw 0xfb4e9313980980b8 0x27da74989cc04c05 0xf24c8383b80180e2 0x2792641c1dc00c07

def z464 : W := mkw 0x4ebc5b4900000000 0x2275e2da48000000 0x0fbf7ffc0000001d 0x907dfbffe0000000

def z465 : W := mkw 0x4ebc61e1a774fb75 0x0275e30f0d3ba7db 0x8e7ce3e387f1fffe 0xd473e71f1c3f8fff

def z466 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xf203ff80386007f2 0x37901ffc01c3003f

def z467 : W := mkw 0xefe80036b35fd138 0x077f4001b59afe89 0xfffc007ffffff80f 0xefffe003ffffffc0

def z468 : W := mkw 0x4ea8000023445000 0x02754000011a2280 0xfe3c00007fe07807 0xeff1e00003ff03c0

def z469 : W := mkw 0x6b48000000000000 0x035a400000000000 0x724c000000000002 0x2392600000000000

def z470 : W := mkw 0x2140000010090000 0x010a000000804800 0x01c00000001f8008 0x000e00000000fc00

def z471 : W := mkw 0x6ffc495b334d5000 0x237fe24ad99a6a80 0xfffc007ffffff80f 0xefffe003ffffffc0

def z472 : W := mkw 0x1017f7e1ccb0aff5 0x1080bfbf0e65857f 0x0003ffe3800007f0 0x10001fff1c00003f

def z473 : W := mkw 0xb1428036981b81b8 0x058a1401b4c0dc0d 0xf1c0807fb81f80ea 0x278e0403fdc0fc07

def z474 : W := mkw 0xa1410036d01b8538 0x050a0801b680dc29 0x01c3007fc01f8719 0xc80e1803fe00fc38

def z475 : W := mkw 0x5a03b6a46ff667c6 0x1ad01db5237fb33e 0xfe03ff807ffe67f7 0xfff01ffc03fff33f

def z476 : W := mkw 0x0004010180008831 0x000020080c000441 0x004c000380019800 0x000260001c000cc0

def z477 : W := mkw 0x21410024501b0500 0x010a08012280d828 0xf1c3007c781f871b 0xef8e1803e3c0fc38

def z478 : W := mkw 0x5ebfffc96ee006c0 0x32f5fffe4b770036 0xfe3fff807fe007f7 0xfff1fffc03ff003f

def z479 : W := mkw 0x6ffc5b49334d5000 0x237fe2da499a6a80 0xfffc7f807ffff80f 0xffffe3fc03ffffc0

def z480 : W := mkw 0x3156c15300000000 0x018ab60a98000000 0x73ffe3ff8000001f 0xb39fff1ffc000000

def z481 : W := mkw 0x5a0292802a6000c0 0x12d0149401530006 0xfe03ff80386000f7 0xb7f01ffc01c30007

def z482 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x8000e3e38471fff0 0x5400071f1c238fff

def z483 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x023ce3e384607ff4 0x1011e71f1c2303ff

def z484 : W := mkw 0x0001000040000400 0x0000080002000020 0x0003000040000711 0xc800180002000038

def z485 : W := mkw 0x4eb07ec827e46246 0x1a7583f6413f2312 0x0e307f8007e06004 0x107183fc003f0300

def z486 : W := mkw 0x1003a4004c800680 0x00801d2002640034 0xfc03fc007f8007f7 0xffe01fe003fc003f

def z487 : W := mkw 0xb1438036c81285b8 0x058a1c01b640942d 0x71c3807f800007fb 0xa38e1c03fc00003f

def z488 : W := mkw 0x4ebc61c127647a45 0x0275e30e093b23d2 0x0e3c638007e07804 0x1071e31c003f03c0

def z489 : W := mkw 0x0000000000000000 0x0000000000000000 0xf000000078000003 0xef80000003c00000

def z490 : W := mkw 0x14b3ec6c4d966786 0x08a59f63626cb33c 0xfdb3fc7c7f9e67ff 0xffed9fe3e3fcf33f

def z491 : W := mkw 0x6b48000032491000 0x035a400001924880 0xfe4c00007fe19807 0xeff2600003ff0cc0

def z492 : W := mkw 0x001441618010a935 0x0000a20b0c008549 0x807c80638011fffa 0xc403e4031c008fff

def z493 : W := mkw 0x25fc4161911df935 0x012fe20b0c88efc9 0x01fc0063801ff808 0x000fe0031c00ffc0

def z494 : W := mkw 0x001461618410ab35 0x0000a30b0c208559 0x007c60638411ff1c 0xd003e3031c208ff8

def z495 : W := mkw 0x5a13f6e06ef027c4 0x12d09fb70377813e 0xfe33ffe07ff067ff 0xfff19fff03ff833f

def z496 : W := mkw 0x04a8000001045000 0x0025400000082280 0x003c000000007800 0x0001e000000003c0

def z497 : W := mkw 0x7b4e93932a6000c0 0x33da749c99530006 0xf24c8383b86000e2 0x2792641c1dc30007

def z498 : W := mkw 0x4a0136806ee006c0 0x125009b403770036 0x8e007f807fe007e4 0x5c7003fc03ff003f

def z499 : W := mkw 0x001565e1c4b0af75 0x0000ab2f0e25857b 0x8e7fffe3c7f1ffff 0xdc73ffff1e3f8fff

def z500 : W := mkw 0xb5eb8036d91fd5b8 0x05af5c01b6c8fead 0xf1ff807ff81ffffb 0xef8ffc03ffc0ffff

def z501 : W := mkw 0x2140000000000000 0x010a000000000000 0x71c000000000000b 0xa38e000000000000

def z502 : W := mkw 0x0010406000102104 0x0000820300008108 0x0030006000106008 0x0001800300008300

def z503 : W := mkw 0x0000000001044000 0x0000000000082200 0x00000000479e6000 0x48000000023cf300

def z504 : W := mkw 0xa1410036d81b85b8 0x050a0801b6c0dc2d 0x81c0007ff81f87e8 0x4c0e0003ffc0fc3f

def z505 : W := mkw 0x04b1486c41166506 0x08258a436208b328 0x01b3007c401e6719 0xc80d9803e200f338

def z506 : W := mkw 0x5a0396806ae004c0 0x12d01cb403570026 0xfe039f807be000e3 0x2ff01cfc03df0007

def z507 : W := mkw 0x6b48000032491000 0x035a400001924880 0xf3cc0000787f980b 0xef9e600003c3fcc0

def z508 : W := mkw 0xb1428032981981b8 0x058a140194c0cc0d 0xf0408063b81187fa 0xe78204031dc08c3f

def z509 : W := mkw 0x7ffedbdb2a6000c0 0x33fff6ded9530006 0xffffffffb86000ff 0xb7fffffffdc30007

def z510 : W := mkw 0x7fffdb7f40120500 0x23fffedbfa009028 0x7fffffffc01e071f 0xfbfffffffe00f038

def z511 : W := mkw 0x04b4496d8116e937 0x0825a24b6c08b749 0x01fc007f801ff808 0x000fe003fc00ffc0

def z512 : W := mkw 0x9017e1f7cc32affd 0x0480bf0fbe61957f 0x0003e3ff800007f0 0x10001f1ffc00003f

def z513 : W := mkw 0x7fffffff6ff667c6 0x3bfffffffb7fb33e 0xfffffffffffe67ff 0xfffffffffffff33f

def z514 : W := mkw 0x5a13feec6ef227c6 0x1ad09ff76377913e 0xfe03fffc7fe007f7 0xfff01fffe3ff003f

def z515 : W := mkw 0x5a0380006a400480 0x02d01c0003520024 0xfe0380007fe007f7 0xeff01c0003ff003f

def z516 : W := mkw 0x0000000000000000 0x0000000000000000 0x0c00000047800005 0xc8600000023c0000

def z517 : W := mkw 0x4a01368066e00640 0x125009b403370032 0x0e037f8047e00715 0xd8701bfc023f0038

def z518 : W := mkw 0xa1400036901b8138 0x050a0001b480dc09 0x81c0807f801f87fa 0xc40e0403fc00fc3f

def z519 : W := mkw 0x7fee9313334d5000 0x23ff7498999a6a80 0xfffc8383fffff80f 0xefffe41c1fffffc0

def z520 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x01b0007c479e6708 0x480d8003e23cf338

def z521 : W := mkw 0x7ffbfeec7fff77c6 0x1bffdff763fffbbe 0xfffffffc7fffffff 0xffffffffe3ffffff

def z522 : W := mkw 0xfffedb7f901b8138 0x27fff6dbfc80dc09 0x7fffffff801f801f 0xb3fffffffc00fc00

def z523 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0x7db000007f9e600d 0xebed800003fcf300

def z524 : W := mkw 0x10029280082000c0 0x1080149400410006 0x00008380000000e0 0x0000041c00000007

def z525 : W := mkw 0x80010024d81b85b8 0x0400080126c0dc2d 0x8183007c781f87f9 0xcc0c1803e3c0fc3f

def z526 : W := mkw 0x6fe8000000000000 0x037f400000000000 0xfffc00000471f80f 0xe7ffe00000238fc0

def z527 : W := mkw 0xb143a436dd9fe7be 0x0d8a1d21b6ecff3d 0xf1c3807fff9fe7fb 0xef8e1c03fffcff3f

def z528 : W := mkw 0x7b4e939380208871 0x23da749c9c010443 0xf24c8383806198e2 0x2792641c1c030cc7

def z529 : W := mkw 0x7fea92803b6d50c0 0x13ff549401db6a86 0xfffc83807ffff8ef 0xefffe41c03ffffc7

def z530 : W := mkw 0x001441618010a935 0x0000a20b0c008549 0x027ce3e38011f81e 0x9013e71f1c008fc0

def z531 : W := mkw 0x6fe9242477df7706 0x0b7f492123befbb8 0xfffc00007fffff0f 0xefffe00003fffff8

def z532 : W := mkw 0x4a00000000000000 0x0250000000000000 0x7e00000000000007 0xa3f0000000000000

def z533 : W := mkw 0x7ffeffdb26e00240 0x33fff7fed9370012 0x7fffffff87e0001f 0xb3fffffffc3f0000

def z534 : W := mkw 0x5a02b6802ee002c0 0x12d015b401770016 0xfe00ff803fe000e6 0x37f007fc01ff0007

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x007c00000011f808 0x0003e00000008fc0

def z536 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfd8000007ffff801 0x6fec000003ffffc0

def z537 : W := mkw 0x35fec95b00000000 0x21aff64ad8000000 0x71ff807f8000001b 0xa38ffc03fc000000

def z538 : W := mkw 0x6fe8000000000000 0x037f400000000000 0x7d80000000000001 0x23ec000000000000

def z539 : W := mkw 0x001441618010a935 0x0000a20b0c008549 0x827c00638471f80e 0xc413e0031c238fc0

def z540 : W := mkw 0x5a02b28004200240 0x02d0159400210012 0xfe03ff80046007f7 0xf7f01ffc0023003f

def z541 : W := mkw 0x80010024d81b85b8 0x0400080126c0dc2d 0x80408063f81f87fa 0xcc0204031fc0fc3f

def z542 : W := mkw 0xffffdb5f580b0488 0x27fffedafac05824 0x7ffffffff80e001f 0xbbffffffffc07000

def z543 : W := mkw 0x1003a4806ee006c0 0x10801d2403770036 0xf00380007fe007f3 0xef801c0003ff003f

def z544 : W := mkw 0x5a17f7e1eef0aff5 0x12d0bfbf0f77857f 0xfe03ffe3ffe007f7 0xfff01fff1fff003f

def z545 : W := mkw 0x7fea9a1a334d5000 0x23ff54d0d19a6a80 0xffff1c1c7ffff80f 0xeffff8e0e3ffffc0

def z546 : W := mkw 0xb1468193982988f9 0x058a340c9cc14c47 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z547 : W := mkw 0x0014414100000000 0x0000a20a08000000 0x007c006380000008 0x0003e0031c000000

def z548 : W := mkw 0x6fe90024735f5500 0x037f4801239afaa8 0xffff007c7fffff1f 0xeffff803e3fffff8

def z549 : W := mkw 0x7ffedb7b80108130 0x23fff6dbdc008409 0xffffffff801187ff 0xf7fffffffc008c3f

def z550 : W := mkw 0x001441c180208871 0x0000a20e0c010443 0x827ce3e3806198fe 0x9413e71f1c030cc7

def z551 : W := mkw 0xffffdb7fc81285b8 0x27fffedbfe40942d 0x7fffffff800007ff 0xb3fffffffc00003f

def z552 : W := mkw 0x6ff8486c335f7106 0x0b7fc243619afb88 0xfffc007c7ffff80f 0xefffe003e3ffffc0

def z553 : W := mkw 0x001561e5c432af75 0x0000ab0f2e21957b 0x83ffe3ffc47fffff 0xdc1fff1ffe23ffff

def z554 : W := mkw 0x0000000000000000 0x0000000000000000 0x824c000000619802 0x0412600000030cc0

def z555 : W := mkw 0x000000208010a935 0x0000000104008549 0x000000000011f800 0x0000000000008fc0

def z556 : W := mkw 0x7b4bb6807ee916c0 0x13da5db403f748b6 0xfe4fff807fe19ff7 0xfff27ffc03ff0cff

def z557 : W := mkw 0xb1438036581b0588 0x058a1c01b2c0d82c 0x7183007c781e0719 0xeb8c1803e3c0f038

def z558 : W := mkw 0x04b461e18534eb75 0x0025a30f0c29a75b 0x8ffce3e3c7ffffff 0xdc7fe71f1e3fffff

def z559 : W := mkw 0x5a02b68026e00240 0x12d015b401370012 0x7e03ff8007e00017 0xb3f01ffc003f0000

def z560 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x73fc83ff8000000a 0x239fe41ffc000000

def z561 : W := mkw 0x04b46de985b4eb77 0x0825a36f4c2da75b 0x8e7cffe387f1fffe 0xd473e7ff1c3f8fff

def z562 : W := mkw 0x04a0080800000000 0x0025004040000000 0x0d831c1c00000001 0x006c18e0e0000000

def z563 : W := mkw 0xb5e38c1e598f448a 0x0daf1c60f2cc7a24 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z564 : W := mkw 0x9013ec7ecc92a7be 0x0c809f63f664953d 0x0003fc7f800007f0 0x10001fe3fc00003f

def z565 : W := mkw 0x4a00000022400000 0x0250000001120000 0x0e00000007e00004 0x00700000003f0000

def z566 : W := mkw 0x0000000080008030 0x0000000004000401 0x80408003800180e2 0x040204001c000c07

def z567 : W := mkw 0x0000000000000000 0x0000000000000000 0x01800000401e0009 0xc80c00000200f000

def z568 : W := mkw 0x0010606004102304 0x0000830300208118 0x827c60600471ff1e 0xd413e30300238ff8

def z569 : W := mkw 0x4a00000022400000 0x0250000001120000 0xfe7c00007ff1f80f 0xeff3e00003ff8fc0

def z570 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x027ce3e3800007fe 0x9013e71f1c00003f

def z571 : W := mkw 0x80010004580b0488 0x0400080022c05824 0x00000000780e0000 0x0800000003c07000

def z572 : W := mkw 0x7fffff7f77df7706 0x2bfffffbfbbefbb8 0xffffffffffffff1f 0xfffffffffffffff8

def z573 : W := mkw 0x7ffedbdb80208871 0x23fff6dedc010443 0xffffffff806198ff 0xb7fffffffc030cc7

def z574 : W := mkw 0xb1438016580b0488 0x058a1c00b2c05824 0xf1c3001c781f800b 0xef8e1800e3c0fc00

def z575 : W := mkw 0x04b0484800000000 0x0025824240000000 0x01b0007c00000008 0x000d8003e0000000

def z576 : W := mkw 0x6ff86060375d7304 0x037fc30301baeb98 0xfffc60607fffff1f 0xffffe30303fffff8

def z577 : W := mkw 0x7fffffffc5b6ef77 0x2bfffffffe2db77b 0xffffffffc7ffffff 0xfffffffffe3fffff

def z578 : W := mkw 0x6fe80020b35dd130 0x037f4001059aee89 0xfffc8063ffffffff 0xefffe4031fffffff

def z579 : W := mkw 0xfff3fefeffffe7fe 0x1fff9ff7f7ffff3f 0xfff3ffffffffe7ff 0xffff9fffffffff3f

def z580 : W := mkw 0x04b06c6c05966306 0x08258363602cb318 0x0db07c7c079e600c 0x106d83e3e03cf300

def z581 : W := mkw 0x21400000334d5000 0x010a0000019a6a80 0xf1c000007ffff80b 0xef8e000003ffffc0

def z582 : W := mkw 0x0000008080208871 0x0000000404010443 0x80000000006198e0 0x0400000000030cc7

def z583 : W := mkw 0x0001242477df7706 0x0800092123befbb8 0x800000007fffff00 0x4c00000003fffff8

def z584 : W := mkw 0x1003800048000480 0x00801c0002400024 0x00038000000007f0 0x00001c000000003f

def z585 : W := mkw 0x001060608410a334 0x0000830304208519 0x8070e0638411e7fe 0xd40387031c208f3f

def z586 : W := mkw 0x1003802448120580 0x00801c012240902c 0xf183807c781e07fb 0xef8c1c03e3c0f03f

def z587 : W := mkw 0x3156db5b00000000 0x218ab6dad8000000 0x71c3ffff8000001b 0xb38e1ffffc000000

def z588 : W := mkw 0x5a0396006ac00480 0x12d01cb003560024 0xfe031c007fe00007 0xeff018e003ff0000

def z589 : W := mkw 0x7b4e931300000000 0x23da749898000000 0x73cf83ff8000001b 0xa39e7c1ffc000000

def z590 : W := mkw 0x0001040040800400 0x0000082002040020 0x0c031c0043800001 0x086018e0021c0000

def z591 : W := mkw 0x4a1477c126e02a45 0x1250a3be09370152 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z592 : W := mkw 0x4a00368026e00240 0x125001b401370012 0x8e00ff8007e007f6 0xd47007fc003f003f

def z593 : W := mkw 0x000421a18430ab75 0x0000210d0c21855b 0x824c83838471ffe2 0x4412641c1c238fff

def z594 : W := mkw 0x5eb3fe6c6fd66786 0x1af59ff3637eb33c 0x7db37c7c7f9e671d 0xfbed9be3e3fcf338

def z595 : W := mkw 0x4ea8000023445000 0x02754000011a2280 0x0c00000003800000 0x00600000001c0000

def z596 : W := mkw 0x1003b6804ca006c0 0x10801db402650036 0x0c03ff80478007f5 0xd8601ffc023c003f

def z597 : W := mkw 0x001060e08430ab75 0x000083070421855b 0x803060600471fffc 0xd401830300238fff

def z598 : W := mkw 0x3142801200000000 0x018a140090000000 0x7040800380000002 0x238204001c000000

def z599 : W := mkw 0x7ffffffbeef0aff5 0x33ffffffdf77857f 0xfffffffffff1ffff 0xffffffffffff8fff

def z600 : W := mkw 0x6fe820a0b77dfb75 0x037f410505bbefdb 0xfffc00007fffffef 0xefffe00003ffffff

def z601 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0x7e037f807fe00005 0x3bf01bfc03ff0000

def z602 : W := mkw 0x7fffffdb4ca006c0 0x33fffffeda650036 0x7fffffff800007ff 0xb3fffffffc00003f

def z603 : W := mkw 0xb156e1f39c39abfd 0x058ab70f9ce1cd5f 0xf27ce3e3bc71fffe 0xf793e71f1de38fff

def z604 : W := mkw 0x0010606004102304 0x0000830300208118 0x0000606000000710 0x1000030300000038

def z605 : W := mkw 0x0000002401166106 0x080000012008b308 0x00000000001e6000 0x000000000000f300

def z606 : W := mkw 0xfb438036fa5b85b8 0x07da1c01b7d2dc2d 0xffc3807fffff87ff 0xeffe1c03fffffc3f

def z607 : W := mkw 0xfb57f7f7fefbaffd 0x17dabfbfbff7dd7f 0xffffffffffffffff 0xffffffffffffffff

def z608 : W := mkw 0x6b5c61e1b679bb75 0x035ae30f0db3cddb 0xf27ce3e3bc71fffe 0xf793e71f1de38fff

def z609 : W := mkw 0x6b480000334d5000 0x035a4000019a6a80 0xf24c00007ffff802 0x6f92600003ffffc0

def z610 : W := mkw 0x7ffeff5b05846206 0x2bfff7fad82c2310 0x7fffffff8780601f 0xb3fffffffc3c0300

def z611 : W := mkw 0x6ff96c6c45966706 0x0b7fcb63622cb338 0x7fff7c7c479e671f 0xfbfffbe3e23cf338

def z612 : W := mkw 0x25e80000110d5000 0x012f400000886a80 0x0dfc0000479ff80d 0xc86fe000023cffc0

def z613 : W := mkw 0x6b48000032491000 0x035a400001924880 0x7000000038000000 0x2380000001c00000

def z614 : W := mkw 0x6fe82080376d5240 0x037f410401bb6a92 0xfffce3807fffffff 0xffffe71c03ffffff

def z615 : W := mkw 0x00116c6c44922706 0x08008b6362249138 0x00337c7c0410671c 0xd0019be3e0208338

def z616 : W := mkw 0x5a17f7c16ee006c0 0x12d0bfbe0b770036 0xfe7fffe3ffe007ff 0xfff3ffff1fff003f

def z617 : W := mkw 0x000124a0eef0aff5 0x100009250777857f 0x800000007ff1ffe0 0x4c00000003ff8fff

def z618 : W := mkw 0xfb4f9337d81b85b8 0x27da7c99bec0dc2d 0xf3cf83fff81f87fb 0xef9e7c1fffc0fc3f

def z619 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xff8000007fee0007 0xeffc000003ff7000

def z620 : W := mkw 0x001565e5c5b6ef77 0x0800ab2f2e2db77b 0x827ce3e3c7fffffe 0xdc13e71f1e3fffff

def z621 : W := mkw 0xa1400036901b8138 0x050a0001b480dc09 0xf1c0007ff81f800b 0xef8e0003ffc0fc00

def z622 : W := mkw 0x7feb9e1a6ac00480 0x33ff5cf0d3560024 0x7d831c1c7b800001 0x2bec18e0e3dc0000

def z623 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfdc000007b9f800b 0xefee000003dcfc00

def z624 : W := mkw 0x0000000022400000 0x0000000001120000 0x800000007fe00000 0x4c00000003ff0000

def z625 : W := mkw 0xb5f3ec7e5d9f678e 0x0daf9f63f2ecfb3c 0x7db37c7c7f9e671d 0xfbed9be3e3fcf338

def z626 : W := mkw 0x4a000000334d5000 0x02500000019a6a80 0xfe0000007ffff807 0xeff0000003ffffc0

def z627 : W := mkw 0x6b40000032490000 0x035a000001924800 0xffc000007fff800f 0xeffe000003fffc00

def z628 : W := mkw 0xb153e076dc1ba7bc 0x058a9f03b6e0dd3d 0xf1f3e07ffc1fe7ff 0xff8f9f03ffe0ff3f

def z629 : W := mkw 0x5a16f3e1ae70abf5 0x12d0b79f0d73855f 0xf27ce3e3bc71fffe 0xf793e71f1de38fff

def z630 : W := mkw 0x0004010100000000 0x0000200808000000 0x024c838380000002 0x0012641c1c000000

def z631 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf043807fb80187f2 0x27821c03fdc00c3f

def z632 : W := mkw 0x80000000980980b8 0x0400000004c04c05 0x80000000380180e0 0x0400000001c00c07

def z633 : W := mkw 0x0010404000000000 0x0000820200000000 0x003060600000001c 0x9001830300000000

def z634 : W := mkw 0x80012424dd9fe7be 0x0c00092126ecff3d 0x800000007f9fe7e0 0x4c00000003fcff3f

def z635 : W := mkw 0xfffbec7effdff7be 0x0fffdf63f7feffbd 0xfffffc7fffffffff 0xffffffe3ffffffff

def z636 : W := mkw 0x0004018100200841 0x0000200c08010042 0x020c038000601800 0x0010601c000300c0

def z637 : W := mkw 0xffffe1f7ff7ffffd 0x07ffff0fbffbffff 0xffffe3ffffffffff 0xffffff1fffffffff

def z638 : W := mkw 0xb157c177d81b85b8 0x058abe0bbec0dc2d 0xf3ffe3fff81f87ff 0xff9fff1fffc0fc3f

def z639 : W := mkw 0x214c011300000000 0x210a600898000000 0x004c000380000000 0x000260001c000000

def z640 : W := mkw 0x25fc497f01166106 0x292fe24bf808b308 0x01fc007f801e6008 0x000fe003fc00f300

def z641 : W := mkw 0x4ea8000023445000 0x02754000011a2280 0x0fbc000047fe780d 0xc87de000023ff3c0

def z642 : W := mkw 0x04b16c4844800600 0x00258b6242240030 0x0db37c7c4780071d 0xd86d9be3e23c0038

def z643 : W := mkw 0xa5f16c7ed59fe73e 0x0d2f8b63f6acff39 0x0df37c7fc79fe71d 0xd86f9be3fe3cff38

def z644 : W := mkw 0x000104006ac00480 0x1000082003560024 0x000000007b800000 0x0800000003dc0000

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000471f800 0x4400000000238fc0

def z646 : W := mkw 0x0004018180208871 0x0000200c0c010443 0x00008383800000e0 0x0000041c1c000007

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x023c000004607804 0x0011e000002303c0

def z648 : W := mkw 0x5a0396006ac00480 0x12d01cb003560024 0xfc039c007b8007f3 0xefe01ce003dc003f

def z649 : W := mkw 0xa5f0487e911fe13e 0x0d2f8243f488ff09 0x01f0007f801fe008 0x000f8003fc00ff00

def z650 : W := mkw 0x001461e104302b45 0x0000a30f0821815a 0x023c63e004707f1c 0xd011e31f002383f8

def z651 : W := mkw 0xb1438016d80b84b8 0x058a1c00b6c05c25 0xf1c3801ff80f80e3 0x2f8e1c00ffc07c07

def z652 : W := mkw 0x7ffefbdb04200240 0x23fff7ded8210012 0xffffffff846007ff 0xf7fffffffc23003f

def z653 : W := mkw 0x000000802a6000c0 0x1000000401530006 0x80000000386000e0 0x0400000001c30007

def z654 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fbf7f9c00000005 0x33fdfbfce0000000

def z655 : W := mkw 0x2148000010091000 0x010a400000804880 0x004c000000019800 0x0002600000000cc0

def z656 : W := mkw 0xb1428012980980b8 0x058a140094c04c05 0xf1c08003f81f80eb 0xef8e04001fc0fc07

def z657 : W := mkw 0x4eb17eec67f66746 0x1a758bf7633fb33a 0x0fb37ffc47fe671d 0xd87d9bffe23ff338

def z658 : W := mkw 0x6fe8368037ed5240 0x137f41b401bf6a92 0xfffc7f807ffff80f 0xffffe3fc03ffffc0

def z659 : W := mkw 0x0000002000100100 0x0000000100008008 0x0000006000100718 0xc000000300008038

def z660 : W := mkw 0x1003960048800480 0x10801cb002440024 0x00031c0000000000 0x000018e000000000

def z661 : W := mkw 0x1016fbfb8430ab75 0x2080b7dfdc21855b 0x0003ffff800007f0 0x10001ffffc00003f

def z662 : W := mkw 0x7ffedb7f01166106 0x2bfff6dbf808b308 0x7fffffff801e601f 0xb3fffffffc00f300

def z663 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x0030e3e3841067fc 0xd001871f1c20833f

def z664 : W := mkw 0xfb43b692fee986f8 0x17da1db497f74c37 0xfe43ff83ffe187f7 0xfff21ffc1fff0c3f

def z665 : W := mkw 0xb142801218090088 0x058a140090c04804 0x7000000038000000 0x2380000001c00000

def z666 : W := mkw 0x0000202004102304 0x0000010100208118 0x0000000004106700 0x4000000000208338

def z667 : W := mkw 0x4ea8368027e45240 0x127541b4013f2292 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z668 : W := mkw 0x35f3ec7e45966706 0x09af9f63f22cb338 0x7df3fc7fc79e671f 0xfbef9fe3fe3cf338

def z669 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0c307c00479e6704 0x586183e0023cf338

def z670 : W := mkw 0x7ffefbfb8430ab75 0x23fff7dfdc21855b 0x7fffffff800007ff 0xb3fffffffc00003f

def z671 : W := mkw 0x04a00000334d5000 0x00250000019a6a80 0x8db000007ffff80d 0xcc6d800003ffffc0

def z672 : W := mkw 0x1017f7e1ccb0aff5 0x1080bfbf0e65857f 0x827fffe38471fffe 0xd413ffff1c238fff

def z673 : W := mkw 0x6fe8000022400000 0x037f400001120000 0xfffc00007fe0000f 0xefffe00003ff0000

def z674 : W := mkw 0xfffffffffefb87f8 0x37fffffffff7dc3f 0xffffffffffff87ff 0xfffffffffffffc3f

def z675 : W := mkw 0x5a0292002a400080 0x12d0149001520004 0x7000000038000000 0x2380000001c00000

def z676 : W := mkw 0x0014414100002805 0x0000a20a08000140 0x003c000000007800 0x0001e000000003c0

def z677 : W := mkw 0x90038036c81285b8 0x04801c01b640942d 0x8043807f801187fa 0xc4021c03fc008c3f

def z678 : W := mkw 0x5ea39e0c6bc64482 0x1af51cf0635e3224 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z679 : W := mkw 0x5a03b6804ca006c0 0x12d01db402650036 0x7e03ff80000007f7 0xb3f01ffc0000003f

def z680 : W := mkw 0x6ffc61e18430ab75 0x037fe30f0c21855b 0xfffce3e38471ffff 0xf7ffe71f1c238fff

def z681 : W := mkw 0x0000208004200240 0x0000010400210012 0x0000e380000007f0 0x1000071c0000003f

def z682 : W := mkw 0x5a03b6a46ef207c0 0x12d01db52377903e 0xff83fffc7ffe07ff 0xfffc1fffe3fff03f

def z683 : W := mkw 0x6fe80000110d5000 0x037f400000886a80 0x7ffc0000001ff80f 0xa3ffe0000000ffc0

def z684 : W := mkw 0x3156e1f38430ab75 0x018ab70f9c21855b 0xf3ffe3ff8471ffff 0xf79fff1ffc238fff

def z685 : W := mkw 0x6ffc414100000000 0x037fe20a08000000 0x7ffce3e38000001f 0xb3ffe71f1c000000

def z686 : W := mkw 0x35f2c85a00000000 0x01af9642d0000000 0x7df3fc7f8000001f 0xb3ef9fe3fc000000

def z687 : W := mkw 0x7b4e931300000000 0x23da749898000000 0x7e4fff8380000017 0xb3f27ffc1c000000

def z688 : W := mkw 0x90038036c81285b8 0x04801c01b640942d 0x0183807fc01e07f9 0xc80c1c03fe00f03f

def z689 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x8200e3e3846007f6 0xd410071f1c23003f

def z690 : W := mkw 0xfb439236d81b85b8 0x07da1c91b6c0dc2d 0xffc3fffff81f87ff 0xfffe1fffffc0fc3f

def z691 : W := mkw 0xb143a436dc9b87b8 0x058a1d21b6e4dc3d 0xfdc3fc7fff9f87ff 0xffee1fe3fffcfc3f

def z692 : W := mkw 0x6b4c0181b2699871 0x035a600c0d934cc3 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z693 : W := mkw 0x2140000010090000 0x010a000000804800 0x71800000780e0001 0x2b8c000003c07000

def z694 : W := mkw 0x0000208004200240 0x0000010400210012 0x80000000046007e0 0x440000000023003f

def z695 : W := mkw 0xb5e38036d91fc5b8 0x05af1c01b6c8fe2d 0xfdf3807fff9fe7ff 0xefef9c03fffcff3f

def z696 : W := mkw 0x4a08000022401000 0x0250400001120080 0x020c000000601800 0x00106000000300c0

def z697 : W := mkw 0x0000248026e00240 0x1000012401370012 0x0000000007e00000 0x00000000003f0000

def z698 : W := mkw 0x000020a084308370 0x000001050421841b 0x8240e3e3847187fe 0xd412071f1c238c3f

def z699 : W := mkw 0x7fea9a1a00000000 0x23ff54d0d0000000 0x7f83ff9c00000017 0xb3fc1ffce0000000

def z700 : W := mkw 0xffeb80167b4f5488 0x07ff5c00b3da7aa4 0xffff001c7ffff80f 0xeffff800e3ffffc0

def z701 : W := mkw 0xffffff7fdd9fe7be 0x2ffffffbfeecff3d 0xffffffffff9fe7ff 0xfffffffffffcff3f

def z702 : W := mkw 0x7b4fb7936ee006c0 0x33da7dbc9b770036 0xfe4fff83ffe007f7 0xfff27ffc1fff003f

def z703 : W := mkw 0x84b16c6cdd9fe7be 0x0c258b6366ecff3d 0x8db37c7c7f9fe7fd 0xdc6d9be3e3fcff3f

def z704 : W := mkw 0x7feb96007bcd5480 0x13ff5cb003de6aa4 0xffff1c007ffff80f 0xeffff8e003ffffc0

def z705 : W := mkw 0x2140000010090000 0x010a000000804800 0xf040000038018002 0x2782000001c00c00

def z706 : W := mkw 0x215461e19439ab75 0x010aa30f0ca1cd5b 0xf3fce3e3fc7fffff 0xff9fe71f1fe3ffff

def z707 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe03ff807ff1fff7 0xfff01ffc03ff8fff

def z708 : W := mkw 0x25e80000334d5000 0x012f4000019a6a80 0xf1fc00007ffff80b 0xef8fe00003ffffc0

def z709 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0xfffffffffbef981f 0xbfffffffffdf7cc0

def z710 : W := mkw 0x04b14c6c41966506 0x08258a63620cb328 0x0db31c7c439e6719 0xc86d98e3e21cf338

def z711 : W := mkw 0x6b40000032490000 0x035a000001924800 0xfffc00007ffff80f 0xefffe00003ffffc0

def z712 : W := mkw 0x00116c6c44922706 0x08008b6362249138 0x0d837c7c479e071d 0xd86c1be3e23cf038

def z713 : W := mkw 0x4a0136806ee006c0 0x125009b403770036 0xfe007f807fe007e7 0xfff003fc03ff003f

def z714 : W := mkw 0x7ffedb5b10090000 0x23fff6dad8804800 0x7ffffffff80e001f 0xbbffffffffc07000

def z715 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x8e7ce3e3c7f1ffff 0xdc73e71f1e3f8fff

def z716 : W := mkw 0x7b4e931300000000 0x23da749898000000 0x7fcfffff8000001f 0xb3fe7ffffc000000

def z717 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0xffffffffffee001f 0xffffffffffff7000

def z718 : W := mkw 0x6b596c6c76db3706 0x0b5acb6363b6d9b8 0xf24f7c7c38619f12 0x37927be3e1c30cf8

def z719 : W := mkw 0x14bedb5b00000000 0x20a5f6dad8000000 0x003fffff80000010 0x1001fffffc000000

def z720 : W := mkw 0x04a12c2c45966706 0x08250961622cb338 0x0db31c1c479e670d 0xc86d98e0e23cf338

def z721 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7dffffff80000019 0x33effffffc000000

def z722 : W := mkw 0x04b14c4c41864402 0x08258a62620c3220 0x0db31c7c438e0009 0x086d98e3e21c7000

def z723 : W := mkw 0xeb4124a4fefb87f8 0x175a092527f7dc3f 0xffc000007fff87ef 0xeffe000003fffc3f

def z724 : W := mkw 0xa5fc497f911fd138 0x252fe24bfc88fe89 0x01fc007f801ff808 0x000fe003fc00ffc0

def z725 : W := mkw 0x800124a4ddbfefff 0x0c00092526edff7f 0x800000007fffffe0 0x4c00000003ffffff

def z726 : W := mkw 0x04b16cecc5b6ef77 0x08258b67662db77b 0x0db37c7c479e67fd 0xd86d9be3e23cf33f

def z727 : W := mkw 0x7ffedb5b32491000 0x23fff6dad9924880 0xffffffffffe1981f 0xffffffffffff0cc0

def z728 : W := mkw 0x7ffedb5b22400000 0x23fff6dad9120000 0x7fffffff87e0001f 0xb3fffffffc3f0000

def z729 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x8df3ffffc79fe7ff 0xdc6f9ffffe3cff3f

def z730 : W := mkw 0x0014494900000000 0x0000a24a48000000 0x0003ffff80000010 0x10001ffffc000000

def z731 : W := mkw 0x5a17d761ead0adb5 0x12d0bebb0f56856d 0x7c7f1c63fb91f809 0x2be3f8e31fdc8fc0

def z732 : W := mkw 0x04b0484801044000 0x0025824240082200 0x0db37c7c438e001d 0x986d9be3e21c7000

def z733 : W := mkw 0x7b4fb73745966706 0x2bda7db9ba2cb338 0x724c8383c79e6702 0x6b92641c1e3cf338

def z734 : W := mkw 0x35ebb6805dad56c0 0x11af5db402ed6ab6 0x01ffff80001ffff8 0x100ffffc0000ffff

def z735 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0xffffffff8061981f 0xb7fffffffc030cc0

def z736 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xffbc00007ffff805 0x6ffde00003ffffc0

def z737 : W := mkw 0xb157e1d75c2b2ecd 0x058abf0ebae15976 0x73bf639c7c6e7805 0x3b9dfb1ce3e373c0

def z738 : W := mkw 0x0004218184208a71 0x0000210c0c210453 0x827ce3838471fffe 0xd413e71c1c238fff

def z739 : W := mkw 0x800124a4ccb287f8 0x140009252665943f 0x00000000000007e0 0x000000000000003f

def z740 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x8fff1c1c47fff80f 0xcc7ff8e0e23fffc0

def z741 : W := mkw 0x04a12c0c45864602 0x08250960622c3230 0x0db37c1c479e671d 0xd86d9be0e23cf338

def z742 : W := mkw 0x800124a4ffffe7fe 0x1c00092527ffff3f 0x800000007fffe7e0 0x4c00000003ffff3f

def z743 : W := mkw 0x25fd6ddb6ee006c0 0x312feb6edb770036 0x81fc007fffe007e8 0x4c0fe003ffff003f

def z744 : W := mkw 0xeb4036b6b6fb8378 0x175a01b5b5b7dc1b 0x0fc07fff87ff800c 0x107e03fffc3ffc00

def z745 : W := mkw 0x04a12cacc5b6ef77 0x08250965662db77b 0x8d831c1c47ffffe1 0x4c6c18e0e23fffff

def z746 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0xffffffff8460001f 0xf7fffffffc230000

def z747 : W := mkw 0x04b16c6c44920700 0x00258b6362249038 0x0db37c7c479e071d 0xd86d9be3e23cf038

def z748 : W := mkw 0x0014416180108130 0x0000a20b0c008409 0x827ce3e38471fffe 0xd413e71f1c238fff

def z749 : W := mkw 0x35f6c95b00000000 0x01afb64ad8000000 0x7fffffff8000001f 0xb3fffffffc000000

def z750 : W := mkw 0x7b5edb5b00000000 0x23daf6dad8000000 0x7003ffff80000010 0x33801ffffc000000

def z751 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x83ffe3ff8471ffff 0xd41fff1ffc238fff

def z752 : W := mkw 0x001461c104200240 0x0000a30e08210012 0x827ce3e38471fffe 0xd413e71f1c238fff

def z753 : W := mkw 0x1017ffedccb2aff7 0x1880bfff6e65957f 0x0003ffff800007f0 0x10001ffffc00003f

def z754 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0db31c1c478e6005 0x086d98e0e23c7300

def z755 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0xffffffffb87ff81f 0xb7fffffffdc3ffc0

def z756 : W := mkw 0x7fea9a1a00000000 0x23ff54d0d0000000 0x7fc3ffff8000001f 0xb3fe1ffffc000000

def z757 : W := mkw 0x7ffedb5b01044000 0x23fff6dad8082200 0x7fffffff8780601f 0xb3fffffffc3c0300

def z758 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0xffffffff800007ff 0xf7fffffffc00003f

def z759 : W := mkw 0xb5f2ec5a9d8de2be 0x0daf9762d4ec6f15 0xfc70fc03bf81e0e6 0x37e387e01dfc0f07

def z760 : W := mkw 0x7b42921232490000 0x03da149091924800 0xffc3ffffffff801f 0xfffe1ffffffffc00

def z761 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe33ff807ff067ff 0xfff19ffc03ff833f

def z762 : W := mkw 0x5eb2daec2b7661c6 0x1af596d7615bb30e 0xf3b083fc387e60ea 0x279d841fe1c3f307

def z763 : W := mkw 0x7ffedb5b32491000 0x23fff6dad9924880 0xffffffffbc71f81f 0xf7fffffffde38fc0

def z764 : W := mkw 0x000124a4f7ffff77 0x0800092527bffffb 0x800000007fffffe0 0x4c00000003ffffff

def z765 : W := mkw 0x7ffedb5b10090000 0x23fff6dad8804800 0x7fffffff801f801f 0xb3fffffffc00fc00

def z766 : W := mkw 0xa1410036d81b85b8 0x050a0801b6c0dc2d 0xf1c0007ff81f87eb 0xef8e0003ffc0fc3f

def z767 : W := mkw 0x04b06c6c05966306 0x08258363602cb318 0x0db37c7c079e601d 0x906d9be3e03cf300

def z768 : W := mkw 0xdeab8036eb56d5b8 0x06f55c01b75ab6ad 0x0e3f807f87e07ff4 0x0071fc03fc3f03ff

def z769 : W := mkw 0x7ffedb5b01044000 0x23fff6dad8082200 0xffffffffc7fff81f 0xfffffffffe3fffc0

def z770 : W := mkw 0x7ffedb5b23445000 0x23fff6dad91a2280 0xffffffffffe0781f 0xffffffffffff03c0

def z771 : W := mkw 0x7ffedb5b01044000 0x23fff6dad8082200 0x7fffffffc38e001f 0xbbfffffffe1c7000

def z772 : W := mkw 0x5a02921200000000 0x02d0149090000000 0x7e03ffff80000017 0xb3f01ffffc000000

def z773 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf3c3807ffc7f87ff 0xef9e1c03ffe3fc3f

def z774 : W := mkw 0x3156db5b00000000 0x218ab6dad8000000 0x01c3ffff80000018 0x100e1ffffc000000

def z775 : W := mkw 0x84b16c6ccd96e7be 0x0c258b63666cb73d 0x0db37c7c479e67fd 0xd86d9be3e23cf33f

def z776 : W := mkw 0x7b5edb5b00000000 0x23daf6dad8000000 0x73cfffff8000001b 0xb39e7ffffc000000

def z777 : W := mkw 0x25fc497b911df935 0x212fe24bdc88efc9 0x01fc007f801ff808 0x000fe003fc00ffc0

def z778 : W := mkw 0x000124a4c4b28770 0x000009252625943b 0x8fc3ffffc7ff87ff 0xdc7e1ffffe3ffc3f

def z779 : W := mkw 0x4ea0000023444000 0x02750000011a2200 0xfffc00007ffff80f 0xefffe00003ffffc0

def z780 : W := mkw 0xfb4292923a6900c8 0x17da149491d34806 0xf2008380386000e2 0x2790041c01c30007

def z781 : W := mkw 0x90038036c81285b8 0x04801c01b640942d 0xf183807ff81e07fb 0xef8c1c03ffc0f03f

def z782 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fffffffc780001f 0xfbfffffffe3c0000

def z783 : W := mkw 0x04b56d6d45966706 0x0825ab6b6a2cb338 0x8fffffffc7ffff1f 0xdc7ffffffe3ffff8

def z784 : W := mkw 0xcebd5b6dd81b85b8 0x2675eadb6ec0dc2d 0x8e3c7f80781f87e4 0x5c71e3fc03c0fc3f

def z785 : W := mkw 0x6fe8081a334d5000 0x237f4040d19a6a80 0xfffc001c7ffff80f 0xefffe000e3ffffc0

def z786 : W := mkw 0x6b480000334d5000 0x035a4000019a6a80 0xf27c00007ffff80e 0xef93e00003ffffc0

def z787 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x0043ffff8000001a 0x90021ffffc000000

def z788 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xf3fc00007ffff80a 0x6f9fe00003ffffc0

def z789 : W := mkw 0x04b0486c01166106 0x082582436008b308 0x0db37c7c479e601d 0xd86d9be3e23cf300

def z790 : W := mkw 0x04b14c4c41864402 0x08258a62620c3220 0x0d837c7c438e0011 0x186c1be3e21c7000

def z791 : W := mkw 0x5ebedb5b00000000 0x22f5f6dad8000000 0x0c03ffff80000010 0x10601ffffc000000

def z792 : W := mkw 0x35f6db5b00000000 0x21afb6dad8000000 0x7df3ffff8000001f 0xb3ef9ffffc000000

def z793 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0x7ffffffffb9ff81f 0xbbffffffffdcffc0

def z794 : W := mkw 0x04b16c6cc596e736 0x08258b63662cb739 0x0df37c7fc79fe71d 0xd86f9be3fe3cff38

def z795 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xfdc3fc7ff81f87ff 0xffee1fe3ffc0fc3f

def z796 : W := mkw 0x7b5ef3f3b679bb75 0x23daf79f9db3cddb 0xf27ce3e3bc71fffe 0xf793e71f1de38fff

def z797 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0x7fffffffff9e601f 0xfbfffffffffcf300

def z798 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db37c7c479e600d 0x186d9be3e23cf300

def z799 : W := mkw 0xfb4a9292ba6990f8 0x17da549495d34c87 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z800 : W := mkw 0x5a02b28026600240 0x02d0159401330012 0xfe03ff807fe007f7 0xfff01ffc03ff003f

def z801 : W := mkw 0x7b4a921232491000 0x23da549091924880 0x7000000038000000 0x2380000001c00000

def z802 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x8db3ffffc7fffffd 0xdc6d9ffffe3fffff

def z803 : W := mkw 0x7ffedb5b01044000 0x23fff6dad8082200 0x7fffffff801e601f 0xb3fffffffc00f300

def z804 : W := mkw 0x7ffedb5b110d5000 0x23fff6dad8886a80 0xfffffffff81ff81f 0xffffffffffc0ffc0

def z805 : W := mkw 0x04b54d6dc196ed37 0x0825aa6b6e0cb769 0x0dff1c7fc39ff809 0x086ff8e3fe1cffc0

def z806 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xff83ff807ffe07ff 0xfffc1ffc03fff03f

def z807 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0dff7c7c479fff1d 0xd86ffbe3e23cfff8

def z808 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x8fb37c7c47fe671f 0xdc7d9be3e23ff338

def z809 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fffffff8011f81f 0xb3fffffffc008fc0

def z810 : W := mkw 0x21400000334d5000 0x010a0000019a6a80 0xf3fc00007ffff80f 0xef9fe00003ffffc0

def z811 : W := mkw 0x7ffedb5b23445000 0x23fff6dad91a2280 0xffffffff87f1f81f 0xf7fffffffc3f8fc0

def z812 : W := mkw 0x7ffedb5b01046006 0x2bfff6dad8082300 0x7fffffff8000601f 0xb3fffffffc000300

def z813 : W := mkw 0xfb4e9313ba4990b8 0x27da74989dd24c85 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z814 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fffffff8410601f 0xf3fffffffc208300

def z815 : W := mkw 0x6fe80808334d5000 0x037f4040419a6a80 0xffff1c1c7ffff80f 0xeffff8e0e3ffffc0

def z816 : W := mkw 0x04a10c2c41966506 0x08250861620cb328 0x0d831c1c439e6001 0x086c18e0e21cf300

def z817 : W := mkw 0x04b16cecc5b6ef77 0x08258b67662db77b 0x8fff7c7c47ffffff 0xdc7ffbe3e23fffff

def z818 : W := mkw 0x04b4494901044000 0x0025a24a48082200 0x8fffffffc7fff81f 0xdc7ffffffe3fffc0

def z819 : W := mkw 0x7b56d35300000000 0x03dab69a98000000 0x7fffffff8000001f 0xb3fffffffc000000

def z820 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe43ff807ff187ff 0xfff21ffc03ff8c3f

def z821 : W := mkw 0x04b14c4c41864402 0x08258a62620c3220 0x0db37c7c479e601d 0xd86d9be3e23cf300

def z822 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0d837c1c438e0015 0x986c1be0e21c7000

def z823 : W := mkw 0x1003a4804ca006c0 0x00801d2402650036 0xfe03ff807fe007f7 0xfff01ffc03ff003f

def z824 : W := mkw 0x04b469e98534eb75 0x0025a34f4c29a75b 0x8fffffffc7ffffff 0xdc7ffffffe3fffff

def z825 : W := mkw 0x04b4494900000000 0x0025a24a48000000 0x0db3ffff8000001d 0x906d9ffffc000000

def z826 : W := mkw 0x3156db5b00000000 0x218ab6dad8000000 0x7183ffff80000011 0x338c1ffffc000000

def z827 : W := mkw 0xb1439236d81b85b8 0x058a1c91b6c0dc2d 0xf1c3fffff81f87fb 0xff8e1fffffc0fc3f

def z828 : W := mkw 0x04a10c2c41964502 0x08250861620cb228 0x0d831c7c439e0009 0x086c18e3e21cf000

def z829 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1c3807ff80f87f3 0x2f8e1c03ffc07c3f

def z830 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db37c7c478e6715 0x186d9be3e23c7338

def z831 : W := mkw 0x7b4e93933a6910c0 0x33da749c99d34886 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z832 : W := mkw 0x04b16c4c45866606 0x08258b62622c3330 0x0db37c7c478e601d 0x986d9be3e23c7300

def z833 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x827ce3e38461fff6 0x1413e71f1c230fff

def z834 : W := mkw 0x04b56d6dc596ef37 0x0825ab6b6e2cb779 0x8dfffc7fc79fffff 0xdc6fffe3fe3cffff

def z835 : W := mkw 0x04a0080801044000 0x0025004040082200 0x0db31c1c479e600d 0xc86d98e0e23cf300

def z836 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x027ce3e38471fffc 0x1013e71f1c238fff

def z837 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x7003ffff80000013 0xb3801ffffc000000

def z838 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fcfffff80000013 0x33fe7ffffc000000

def z839 : W := mkw 0x04b56d6dc596ef37 0x0825ab6b6e2cb779 0x0db37c7fc79e671d 0xd86d9be3fe3cf338

def z840 : W := mkw 0x5a03b6926ee006c0 0x12d01db493770036 0xfe03ffffffe007f7 0xfff01fffffff003f

def z841 : W := mkw 0xa5f4497f911fe93f 0x0d2fa24bfc88ff49 0x01fc007f801ff808 0x000fe003fc00ffc0

def z842 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0fb3fffc479e671f 0xd87d9fffe23cf338

def z843 : W := mkw 0x7ffedb5b110d5000 0x23fff6dad8886a80 0x7fffffff800e001f 0xb3fffffffc007000

def z844 : W := mkw 0x7ff2da5a00000000 0x03ff96d2d0000000 0x7ff3ffff8000001f 0xb3ff9ffffc000000

def z845 : W := mkw 0x04b16c6cc596e736 0x08258b63662cb739 0x8ffffc7fc7ffffff 0xdc7fffe3fe3fffff

def z846 : W := mkw 0x04a50d8dc1a6cc73 0x0825286c6e0d3663 0x8fcf9f9fc3ef98e3 0x0c7e7cfcfe1f7cc7

def z847 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0x71c3807ff80e07fb 0xab8e1c03ffc0703f

def z848 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7dc3ffff8000001b 0xb3ee1ffffc000000

def z849 : W := mkw 0x7b4e931332491000 0x23da749899924880 0x724c8383b8000002 0x2392641c1dc00000

def z850 : W := mkw 0x7ffedb5b10091000 0x23fff6dad8804880 0x7fffffff8001981f 0xb3fffffffc000cc0

def z851 : W := mkw 0x6ffc494900000000 0x037fe24a48000000 0x7fffffff8000001f 0xb3fffffffc000000

def z852 : W := mkw 0x5a16db5b00000000 0x22d0b6dad8000000 0x7203ffff80000012 0x33901ffffc000000

def z853 : W := mkw 0x04b56d6d45966f07 0x0825ab6b6a2cb378 0x0dbf7c7c479e7f1d 0xd86dfbe3e23cf3f8

def z854 : W := mkw 0x04b16c4845844600 0x00258b62422c2230 0x0db37c7c479e671d 0xd86d9be3e23cf338

def z855 : W := mkw 0x5eb6db4900000000 0x02f5b6da48000000 0x7fffffff8000001f 0xb3fffffffc000000

def z856 : W := mkw 0x000124a4eff6eff7 0x18000925277fb77f 0x800000007fffffe0 0x4c00000003ffffff

def z857 : W := mkw 0x1016db5b334d5000 0x2080b6dad99a6a80 0x8003fffffffff810 0x5c001fffffffffc0

def z858 : W := mkw 0x04a10c2c41964502 0x08250861620cb228 0x0d831c7c438e0711 0x086c18e3e21c7038

def z859 : W := mkw 0x7b4e9393b2699871 0x23da749c9d934cc3 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z860 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7f83ffff80000017 0xb3fc1ffffc000000

def z861 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db37c1c479e6705 0x586d9be0e23cf338

def z862 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0d831c7c438e0019 0x886c18e3e21c7000

def z863 : W := mkw 0xffeb96167bcf5488 0x17ff5cb0b3de7aa4 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z864 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1f3807ffc1fe7ff 0xef8f9c03ffe0ff3f

def z865 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1c3807fb81f87fa 0x278e1c03fdc0fc3f

def z866 : W := mkw 0x3143803648120580 0x018a1c01b240902c 0xf1c3807ff81e07fb 0xef8e1c03ffc0f03f

def z867 : W := mkw 0x7ffedb5b22401000 0x23fff6dad9120080 0x7fffffff8060181f 0xb3fffffffc0300c0

def z868 : W := mkw 0x800124a4fefbaffd 0x1400092527f7dd7f 0x800000007fffffe0 0x4c00000003ffffff

def z869 : W := mkw 0x6ffc61e1b77dfb75 0x037fe30f0dbbefdb 0x7d80e3e3fb8e07f1 0x3bec071f1fdc703f

def z870 : W := mkw 0x001465e184b0ab75 0x0000a32f0c25855b 0x8e7cffe387f1fffe 0xd473e7ff1c3f8fff

def z871 : W := mkw 0x04b16cec4db667c6 0x18258b67626db33e 0x0db37c7c479e67fd 0xd86d9be3e23cf33f

def z872 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fbfffff80000015 0x33fdfffffc000000

def z873 : W := mkw 0x000124a4c5b6ef77 0x08000925262db77b 0x00000000479e67e0 0x48000000023cf33f

def z874 : W := mkw 0x14b6db5b01044000 0x20a5b6dad8082200 0x0db3ffffc79e601d 0xd86d9ffffe3cf300

def z875 : W := mkw 0x04b16cecc5b6e776 0x08258b67662db73b 0x8ff3ffffc7ffe7ff 0xdc7f9ffffe3fff3f

def z876 : W := mkw 0x7b5edb5b00000000 0x23daf6dad8000000 0x727fffff8000001e 0xb393fffffc000000

def z877 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x0033ffff8000001c 0x90019ffffc000000

def z878 : W := mkw 0x04b54d4d41864402 0x0825aa6a6a0c3220 0x0fffffffc38e001f 0x987ffffffe1c7000

def z879 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7db3ffff8000001d 0xb3ed9ffffc000000

def z880 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf3c3e3fff81f87ff 0xff9e1f1fffc0fc3f

def z881 : W := mkw 0x04b56d6d45966706 0x0825ab6b6a2cb338 0x0dff7c7fc79e671d 0xd86ffbe3fe3cf338

def z882 : W := mkw 0x3156db5b00000000 0x218ab6dad8000000 0x73ffffff8000001f 0xb39ffffffc000000

def z883 : W := mkw 0xb14b8036d81b95b8 0x058a5c01b6c0dcad 0xf1cf807ff81f9ffb 0xef8e7c03ffc0fcff

def z884 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x0d83ffffc38e07f1 0x186c1ffffe1c703f

def z885 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfc03ff807b8007f3 0xffe01ffc03dc003f

def z886 : W := mkw 0x04a10c2c41964502 0x08250861620cb228 0x0db31c7c479e671d 0xc86d98e3e23cf338

def z887 : W := mkw 0x7ffedb5b01045000 0x23fff6dad8082280 0x7fffffff8000781f 0xb3fffffffc0003c0

def z888 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x007fffff80000018 0x1003fffffc000000

def z889 : W := mkw 0x04b56ded45b66f47 0x0825ab6f6a2db37a 0x0db37ffc479e671d 0xd86d9bffe23cf338

def z890 : W := mkw 0x5a16db5b00000000 0x22d0b6dad8000000 0x0e03ffff80000014 0x10701ffffc000000

def z891 : W := mkw 0x4ebc7fc927e45240 0x3275e3fe493f2292 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z892 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1ff807ff81ffffb 0xef8ffc03ffc0ffff

def z893 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1c3807ffc7ffffb 0xef8e1c03ffe3ffff

def z894 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x8dff7c7fc7fffffd 0xdc6ffbe3fe3fffff

def z895 : W := mkw 0x04a10c2c41964502 0x08250861620cb228 0x0d831c1c439e0701 0x486c18e0e21cf038

def z896 : W := mkw 0x04b16cec45b66746 0x08258b67622db33a 0x8ffffffc47ffffff 0xdc7fffffe23fffff

def z897 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0d831c1c439e0009 0xc86c18e0e21cf000

def z898 : W := mkw 0x04b16cec45b66746 0x08258b67622db33a 0x0fb37ffc47fe671d 0xd87d9bffe23ff338

def z899 : W := mkw 0x04b16c4c45866606 0x08258b62622c3330 0x0db37c1c478e6715 0xd86d9be0e23c7338

def z900 : W := mkw 0x7fea921200000000 0x03ff549090000000 0x7fffffff8000001f 0xb3fffffffc000000

def z901 : W := mkw 0x4ebc5b4900000000 0x2275e2da48000000 0x0fffffff8000001f 0x907ffffffc000000

def z902 : W := mkw 0x0001040440820400 0x0000082022041020 0x0d831c1c438e0001 0x086c18e0e21c7000

def z903 : W := mkw 0x001469e98430ab75 0x0000a34f4c21855b 0x827fffff8471fffe 0xd413fffffc238fff

def z904 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf3ff807ff81f87ff 0xef9ffc03ffc0fc3f

def z905 : W := mkw 0x000124a4c4b2af77 0x080009252625957b 0x00000000000007e0 0x000000000000003f

def z906 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db31c7c479e6709 0x486d98e3e23cf338

def z907 : W := mkw 0x5a03b6806ee02ec5 0x12d01db403770176 0xfe03ff807fe07ff7 0xfff01ffc03ff03ff

def z908 : W := mkw 0x04a12c2c45966706 0x08250961622cb338 0x0d831c1c438e0701 0x086c18e0e21c7038

def z909 : W := mkw 0x04b16c4c45864602 0x08258b62622c3230 0x0db37c7c478e071d 0xd86d9be3e23c7038

def z910 : W := mkw 0x3143801258090480 0x018a1c0092c04824 0xf1c3807ff81f87fb 0xef8e1c03ffc0fc3f

def z911 : W := mkw 0x00146de984b0ab77 0x0800a36f4c25855b 0x827cffe38471fffe 0xd413e7ff1c238fff

def z912 : W := mkw 0x000401a180308971 0x0000200d0c01844b 0x827c83e38471fffe 0xc413e41f1c238fff

def z913 : W := mkw 0x5a16db5b00000000 0x22d0b6dad8000000 0x7e7fffff8000001f 0xb3f3fffffc000000

def z914 : W := mkw 0x7ffedb5b10090000 0x23fff6dad8804800 0xffffffffb801801f 0xb7fffffffdc00c00

def z915 : W := mkw 0x6fe924a4f7ffff77 0x0b7f492527bffffb 0xfffc00007fffffef 0xefffe00003ffffff

def z916 : W := mkw 0x04b56d6d45966706 0x0825ab6b6a2cb338 0x0db3ffffc79e671d 0xd86d9ffffe3cf338

def z917 : W := mkw 0x001441e18030a975 0x0000a20f0c01854b 0x827c83e38071fffa 0xc413e41f1c038fff

def z918 : W := mkw 0x5a0392006a400480 0x02d01c9003520024 0xfe03ff807fe007f7 0xfff01ffc03ff003f

def z919 : W := mkw 0x04b06c4805846206 0x08258362402c2310 0x0db37c7c479e601d 0xd86d9be3e23cf300

def z920 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fff7fff8000000d 0x33fffbfffc000000

def z921 : W := mkw 0x7feb9e1a7bcd5480 0x33ff5cf0d3de6aa4 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z922 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x0dffffffc79ffffd 0xd86ffffffe3cffff

def z923 : W := mkw 0x7b5ed35332491000 0x23daf69a99924880 0xf27ce3e3bc71f81e 0xf793e71f1de38fc0

def z924 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0x7e03ff807b8007f7 0xbbf01ffc03dc003f

def z925 : W := mkw 0x35fedb5b00000000 0x21aff6dad8000000 0x71ffffff8000001b 0xb38ffffffc000000

def z926 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x8fb3ffffc7fe67ff 0xdc7d9ffffe3ff33f

def z927 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf3cf807ff87f9ffb 0xef9e7c03ffc3fcff

def z928 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0x7ffc00007ffff80d 0x2bffe00003ffffc0

def z929 : W := mkw 0x001461e58432ab75 0x0000a30f2c21955b 0x83fce3ff847ffffe 0xd41fe71ffc23ffff

def z930 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0d831c1c438e0711 0xc86c18e0e21c7038

def z931 : W := mkw 0x25fc496d911ff937 0x092fe24b6c88ffc9 0x01fc007f801ff808 0x000fe003fc00ffc0

def z932 : W := mkw 0x4ebc6dc927e47a47 0x0a75e36e493f23d2 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z933 : W := mkw 0x001461c18420aa75 0x0000a30e0c210553 0x827ce3838461fff6 0xd413e71c1c230fff

def z934 : W := mkw 0x7ffedb5b22400000 0x23fff6dad9120000 0xffffffffb860001f 0xb7fffffffdc30000

def z935 : W := mkw 0x3156db5b10090000 0x218ab6dad8804800 0xf1c3fffff81f801b 0xff8e1fffffc0fc00

def z936 : W := mkw 0x35fedb5b00000000 0x21aff6dad8000000 0x0dffffff8000001d 0x906ffffffc000000

def z937 : W := mkw 0x14b6db5b00000000 0x20a5b6dad8000000 0x01b3ffff80000018 0x100d9ffffc000000

def z938 : W := mkw 0x1002921200000000 0x0080149090000000 0x0003ffff80000010 0x10001ffffc000000

def z939 : W := mkw 0x7ffedb5b00002805 0x23fff6dad8000140 0x7fffffff8000781f 0xb3fffffffc0003c0

def z940 : W := mkw 0x7ffedb5b110d5000 0x23fff6dad8886a80 0xffffffff847ff81f 0xf7fffffffc23ffc0

def z941 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0fff7c7c479e671f 0xd87ffbe3e23cf338

def z942 : W := mkw 0x7feababa8430ab75 0x23ff55d5d421855b 0xfd831c1c0471ffe1 0x67ec18e0e0238fff

def z943 : W := mkw 0x6fe81a08334d5000 0x237f40d0419a6a80 0xfffc1c007ffff80f 0xefffe0e003ffffc0

def z944 : W := mkw 0x315edb5b00000000 0x218af6dad8000000 0x004fffff80000010 0x10027ffffc000000

def z945 : W := mkw 0x04a0080801044000 0x0025004040082200 0x0d831c1c438e0001 0x086c18e0e21c7000

def z946 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe43ffe3ffe007ff 0xfff21fff1fff003f

def z947 : W := mkw 0x000124a4c4b2af77 0x080009252625957b 0x800000000471ffe0 0x4400000000238fff

def z948 : W := mkw 0xa5fc497f911fe13e 0x2d2fe24bfc88ff09 0x01fc007f801fe008 0x000fe003fc00ff00

def z949 : W := mkw 0x04b1486c41164500 0x00258a436208b228 0x0db37c7c479e671d 0xd86d9be3e23cf338

def z950 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x827fffff8471f81e 0xd413fffffc238fc0

def z951 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe037f807fe007e5 0x7ff01bfc03ff003f

def z952 : W := mkw 0x04b56ded45b66f47 0x0825ab6f6a2db37a 0x8fbffffc47fe7fff 0xdc7dffffe23ff3ff

def z953 : W := mkw 0x7ffedb5b32491000 0x23fff6dad9924880 0x7fffffffb800001f 0xb3fffffffdc00000

def z954 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0x7e03ff807fe007f5 0x3bf01ffc03ff003f

def z955 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x0183ffff80000019 0x900c1ffffc000000

def z956 : W := mkw 0x800124a4ffffd7f8 0x1400092527fffebf 0x800000007fffffe0 0x4c00000003ffffff

def z957 : W := mkw 0x7ffedb5b10090000 0x23fff6dad8804800 0xfffffffffc7ff81f 0xffffffffffe3ffc0

def z958 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0x7183807ff81e07f9 0xeb8c1c03ffc0f03f

def z959 : W := mkw 0x1003b6804ca006c0 0x10801db402650036 0xfc03ff807f8007f7 0xffe01ffc03fc003f

def z960 : W := mkw 0x04a12c8c45a64642 0x08250964622d3232 0x8f83ff9c47ee07f7 0xdc7c1ffce23f703f

def z961 : W := mkw 0x04b56dcd45a66e47 0x0825ab6e6a2d3372 0x0fbf7f9c47ee7805 0x187dfbfce23f73c0

def z962 : W := mkw 0xefe924a4ffffd7f8 0x177f492527fffebf 0xfffc00007fffffef 0xefffe00003ffffff

def z963 : W := mkw 0x000421a18430ab75 0x0000210d0c21855b 0x827c83838471ffee 0xc413e41c1c238fff

def z964 : W := mkw 0x04a124a4c5b6ef77 0x08250925262db77b 0x8ffc000047ffffef 0xcc7fe000023fffff

def z965 : W := mkw 0x5ebedb5b23445000 0x22f5f6dad91a2280 0x0e3fffff87e07814 0x1071fffffc3f03c0

def z966 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xff83fffc7fe007ff 0xfffc1fffe3ff003f

def z967 : W := mkw 0x7ffedb5b22400000 0x23fff6dad9120000 0x7ffffffffb80001f 0xbbffffffffdc0000

def z968 : W := mkw 0x04b56ded45b66746 0x0825ab6f6a2db33a 0x8fffffffc7fe67ff 0xdc7ffffffe3ff33f

def z969 : W := mkw 0x04b16c4c45866606 0x08258b62622c3330 0x0d837c1c438e0001 0x186c1be0e21c7000

def z970 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x8e7fffe38471ffff 0xd473ffff1c238fff

def z971 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1c3007ff81f87e9 0x6f8e1803ffc0fc3f

def z972 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0d837c7c439e0719 0xd86c1be3e21cf038

def z973 : W := mkw 0x25e00000110d4000 0x012f000000886a00 0xfffc00007ffff80f 0xefffe00003ffffc0

def z974 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x0c03ffff80000015 0x90601ffffc000000

def z975 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf1c0807ff81f87ea 0x6f8e0403ffc0fc3f

def z976 : W := mkw 0x7ffedb5b110d5000 0x23fff6dad8886a80 0x7fffffffc79ff81f 0xfbfffffffe3cffc0

def z977 : W := mkw 0xb1438036d81badbd 0x058a1c01b6c0dd6d 0xf1c3807ff81ffffb 0xef8e1c03ffc0ffff

def z978 : W := mkw 0x7b4a921232491000 0x23da549091924880 0xf24c000038619802 0x2792600001c30cc0

def z979 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0xfffffffff800001f 0xffffffffffc00000

def z980 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe03ff807be007f3 0x3ff01ffc03df003f

def z981 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0x7c03ff807f8007f5 0xfbe01ffc03fc003f

def z982 : W := mkw 0x35fedb5b110d5000 0x21aff6dad8886a80 0x01ffffff801ff818 0x100ffffffc00ffc0

def z983 : W := mkw 0x04b14c6c41966506 0x08258a63620cb328 0x0d831c7c438e0001 0x086c18e3e21c7000

def z984 : W := mkw 0x04b96c6c45967706 0x0825cb63622cb3b8 0x0dbf7c7c479e7f1d 0xd86dfbe3e23cf3f8

def z985 : W := mkw 0x001565e5c4b2af75 0x0000ab2f2e25957b 0x8fffffffc7ffffff 0xdc7ffffffe3fffff

def z986 : W := mkw 0x35fedb5b00000000 0x21aff6dad8000000 0x0183ffff80000010 0x100c1ffffc000000

def z987 : W := mkw 0xfb56f3f3be79abfd 0x17dab79f9df3cd5f 0xf27ce3e3bc71fffe 0xf793e71f1de38fff

def z988 : W := mkw 0x7ffedb5b23445000 0x23fff6dad91a2280 0x7fffffffc7fe781f 0xfbfffffffe3ff3c0

def z989 : W := mkw 0x4ea80000334d5000 0x02754000019a6a80 0xfe3c00007ffff807 0xeff1e00003ffffc0

def z990 : W := mkw 0x04b16c4c45866606 0x08258b62622c3330 0x0db37c1c479e600d 0xd86d9be0e23cf300

def z991 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0fbf7c7c47fe7f1d 0xd87dfbe3e23ff3f8

def z992 : W := mkw 0x5a02b6802ee002c0 0x12d015b401770016 0xfe00ff803fe007f6 0xf7f007fc01ff003f

def z993 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe3fff807fe07ff7 0xfff1fffc03ff03ff

def z994 : W := mkw 0x04a12c0c45864602 0x08250960622c3230 0x0d837c1c478e0005 0x186c1be0e23c7000

def z995 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0xfffffffffb9f801f 0xffffffffffdcfc00

def z996 : W := mkw 0x5a16db5b22400000 0x22d0b6dad9120000 0xfe03ffffffe00017 0xfff01fffffff0000

def z997 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xffff007c7ffff81f 0xeffff803e3ffffc0

def z998 : W := mkw 0xb1428036981b81b8 0x058a1401b4c0dc0d 0xf1c0807fb81f87fa 0xe78e0403fdc0fc3f

def z999 : W := mkw 0x04b14c6c41966506 0x08258a63620cb328 0x0db31c7c479e600d 0xc86d98e3e23cf300

def z1000 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfdfc00007ffff809 0x6fefe00003ffffc0

def z1001 : W := mkw 0x04bd6d6d45966706 0x2825eb6b6a2cb338 0x0dbf7c7c479e671d 0xd86dfbe3e23cf338

def z1002 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x8db3fc7c479e67ff 0xdc6d9fe3e23cf33f

def z1003 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0x7fffffffffee781f 0xbbffffffffff73c0

def z1004 : W := mkw 0x21410024d01b8530 0x010a08012680dc29 0xf1c3807ff81f87fb 0xef8e1c03ffc0fc3f

def z1005 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0xfdb37c7c7f9e671f 0xffed9be3e3fcf338

def z1006 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0d831c1c479e6001 0x486c18e0e23cf300

def z1007 : W := mkw 0x10038024c81285b0 0x00801c012640942d 0xf1c3807ff81f87fb 0xef8e1c03ffc0fc3f

def z1008 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0xffffffff8011801f 0xf7fffffffc008c00

def z1009 : W := mkw 0x7ffedb5b32490000 0x23fff6dad9924800 0xffffffffffff801f 0xfffffffffffffc00

def z1010 : W := mkw 0xfffedb5b18090088 0x27fff6dad8c04804 0x7fffffffb800001f 0xb3fffffffdc00000

def z1011 : W := mkw 0x5a0396006ac00480 0x12d01cb003560024 0xfe03ff807b8007f7 0xfff01ffc03dc003f

def z1012 : W := mkw 0x04b16c6c4d966786 0x08258b63626cb33c 0x8db37c7c7f9e67fd 0xdc6d9be3e3fcf33f

def z1013 : W := mkw 0x3142803290198130 0x018a14019480cc09 0xf1c3807ff81f87fb 0xef8e1c03ffc0fc3f

def z1014 : W := mkw 0x4a01248066e00640 0x0250092403370032 0xfe03ff807fe007f7 0xfff01ffc03ff003f

def z1015 : W := mkw 0xa1400036901b8138 0x050a0001b480dc09 0xf1c0807ff81f87fb 0xef8e0403ffc0fc3f

def z1016 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x83fce3e3c47fffff 0xdc1fe71f1e23ffff

def z1017 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db37c7c079e671c 0x106d9be3e03cf338

def z1018 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fffffff8460781f 0xb3fffffffc2303c0

def z1019 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfc03ff807fe007f1 0x7fe01ffc03ff003f

def z1020 : W := mkw 0x04a12c0c45866606 0x08250960622c3330 0x0d831c1c478e6001 0x086c18e0e23c7300

def z1021 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x8fbf7ffc47fffffd 0xdc7dfbffe23fffff

def z1022 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0x7d83fffffb8e0011 0x3bec1fffffdc7000

def z1023 : W := mkw 0x0001240444820600 0x0000092022241030 0x0d837c1c478e0715 0xd86c1be0e23c7038

def z1024 : W := mkw 0x35fedb5b00000000 0x21aff6dad8000000 0x03ffffff8000001e 0x901ffffffc000000

def z1025 : W := mkw 0x04b56ded45b66f47 0x0825ab6f6a2db37a 0x8fff7ffc47ffff1f 0xdc7ffbffe23ffff8

def z1026 : W := mkw 0x04b0686805146304 0x002583434028a318 0x0db37c7c479e671d 0xd86d9be3e23cf338

def z1027 : W := mkw 0x5eb6db5b00000000 0x22f5b6dad8000000 0x7fb3ffff8000001f 0xb3fd9ffffc000000

def z1028 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7e7fffff80000016 0x33f3fffffc000000

def z1029 : W := mkw 0x6fe80012334d5000 0x037f4000919a6a80 0xfffc007ffffff80f 0xefffe003ffffffc0

def z1030 : W := mkw 0x6fe81200334d5000 0x037f4090019a6a80 0xfffc7f807ffff80f 0xffffe3fc03ffffc0

def z1031 : W := mkw 0x14b6db5b00000000 0x20a5b6dad8000000 0x0d83ffff80000011 0x106c1ffffc000000

def z1032 : W := mkw 0xb1438436d89b85b8 0x058a1c21b6c4dc2d 0xfdc39c7ffb9f87fb 0xefee1ce3ffdcfc3f

def z1033 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x0fffffff8000001c 0x107ffffffc000000

def z1034 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x0fffffffc79e67ff 0xd87ffffffe3cf33f

def z1035 : W := mkw 0x25fc495b00000000 0x212fe24ad8000000 0x0fffffff8000001f 0x907ffffffc000000

def z1036 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0x7fffffff87fff81f 0xb3fffffffc3fffc0

def z1037 : W := mkw 0x6ffc4949334d5000 0x037fe24a499a6a80 0xfffffffffffff81f 0xffffffffffffffc0

def z1038 : W := mkw 0x9017edffccb2afff 0x0c80bf6ffe65957f 0x0003ffff800007f0 0x10001ffffc00003f

def z1039 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x73ffffff8000001a 0x339ffffffc000000

def z1040 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xfdc3807fff9f87ff 0xefee1c03fffcfc3f

def z1041 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0db31c1c439e6009 0x086d98e0e21cf300

def z1042 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfffce3807ffff81f 0xffffe71c03ffffc0

def z1043 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf183807ff81f87f1 0x6f8c1c03ffc0fc3f

def z1044 : W := mkw 0x9017f7f7ccb2affd 0x1480bfbfbe65957f 0x0003ffff800007f0 0x10001ffffc00003f

def z1045 : W := mkw 0xffeb9a1e7b4f5488 0x27ff5cd0f3da7aa4 0x7d831c1c7b8e0001 0x2bec18e0e3dc7000

def z1046 : W := mkw 0xfb469393ba6988f9 0x17da349c9dd34c47 0xf24c8383b86198e2 0x2792641c1dc30cc7

def z1047 : W := mkw 0x04b16cecc5b6ef77 0x08258b67662db77b 0x8df3fc7fc7ffffff 0xdc6f9fe3fe3fffff

def z1048 : W := mkw 0x4eb47fc927e46a47 0x1a75a3fe493f2352 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z1049 : W := mkw 0x04b16cec45b66746 0x08258b67622db33a 0x8db37c7c47fe67fd 0xdc6d9be3e23ff33f

def z1050 : W := mkw 0x5a16db5b00000000 0x22d0b6dad8000000 0x7c03ffff80000011 0x33e01ffffc000000

def z1051 : W := mkw 0x5a03b6846ee206c0 0x12d01db423771036 0xff83ff9c7fee07f7 0xfffc1ffce3ff703f

def z1052 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0d831c1c478e0005 0xc86c18e0e23c7000

def z1053 : W := mkw 0x4ebc7fc927e46246 0x3a75e3fe493f2312 0x0e3c7f8007e06004 0x1071e3fc003f0300

def z1054 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x0203ffff80000016 0x90101ffffc000000

def z1055 : W := mkw 0x7ffedb5b23445000 0x23fff6dad91a2280 0x7fffffff8380001f 0xb3fffffffc1c0000

def z1056 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0x71c3807ff81f87f9 0x2b8e1c03ffc0fc3f

def z1057 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x024fffff80000012 0x10127ffffc000000

def z1058 : W := mkw 0x04b16cec45b66f47 0x08258b67622db37a 0x0db37c7c47fe7f1d 0xd86d9be3e23ff3f8

def z1059 : W := mkw 0x14b6db5b00000000 0x20a5b6dad8000000 0x0c33ffff80000014 0x10619ffffc000000

def z1060 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe7fff807fe007ff 0xfff3fffc03ff003f

def z1061 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0d837c7c479e6711 0x586c1be3e23cf338

def z1062 : W := mkw 0x0001242445966706 0x08000921222cb338 0x0d837c7c479e671d 0xd86c1be3e23cf338

def z1063 : W := mkw 0x04b16cec45b66746 0x08258b67622db33a 0x0db3fffc479e67fd 0xd86d9fffe23cf33f

def z1064 : W := mkw 0x7ffedb5b08000080 0x23fff6dad8400004 0xffffffffb80000ff 0xb7fffffffdc00007

def z1065 : W := mkw 0x7fea9212334d5000 0x03ff5490919a6a80 0xfffffffffffff81f 0xffffffffffffffc0

def z1066 : W := mkw 0x04b14c6c41966506 0x08258a63620cb328 0x0db37c7c439e601d 0x986d9be3e21cf300

def z1067 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe03ff803fe007f6 0x37f01ffc01ff003f

def z1068 : W := mkw 0x7b5edb5b32491000 0x23daf6dad9924880 0xf24fffffb8619812 0x37927ffffdc30cc0

def z1069 : W := mkw 0x04b16c6cc596e736 0x08258b63662cb739 0x8db37c7c479fe7fd 0xdc6d9be3e23cff3f

def z1070 : W := mkw 0x04a12c0c45864602 0x08250960622c3230 0x0d831c1c478e0701 0x486c18e0e23c7038

def z1071 : W := mkw 0x7ffedb5b2a400080 0x33fff6dad9520004 0x7fffffffb800001f 0xb3fffffffdc00000

def z1072 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x0fbfffffc7fe7ffd 0xd87dfffffe3ff3ff

def z1073 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x8df37c7c479fe71f 0xdc6f9be3e23cff38

def z1074 : W := mkw 0x04b56ded45b66f47 0x0825ab6f6a2db37a 0x0fffffffc7fe7f1f 0xd87ffffffe3ff3f8

def z1075 : W := mkw 0x14b6db5b00000000 0x20a5b6dad8000000 0x0fffffff8000001f 0x907ffffffc000000

def z1076 : W := mkw 0x04a12c2c45966706 0x08250961622cb338 0x0d837c1c479e6715 0xd86c1be0e23cf338

def z1077 : W := mkw 0x4a00368026e00240 0x125001b401370012 0xfe00ff807fe007f7 0xfff007fc03ff003f

def z1078 : W := mkw 0xb1438016580b0488 0x058a1c00b2c05824 0xf1c3807ff80e07fb 0xef8e1c03ffc0703f

def z1079 : W := mkw 0x800124a4eef287f8 0x140009252777943f 0x800000007fe007e0 0x4c00000003ff003f

def z1080 : W := mkw 0x04b56d6dc596ef37 0x0825ab6b6e2cb779 0x8fff7c7fc7ffff1f 0xdc7ffbe3fe3ffff8

def z1081 : W := mkw 0x04a10c0c41864402 0x08250860620c3220 0x0db31c1c438e000d 0x886d98e0e21c7000

def z1082 : W := mkw 0x5ebedb5b00000000 0x22f5f6dad8000000 0x0e7fffff8000001e 0x9073fffffc000000

def z1083 : W := mkw 0x3142921200000000 0x018a149090000000 0x71c3ffff8000001b 0xb38e1ffffc000000

def z1084 : W := mkw 0x04b16c6cc596ef37 0x08258b63662cb779 0x0db37c7c479fff1d 0xd86d9be3e23cfff8

def z1085 : W := mkw 0x7b5edb5b00000000 0x23daf6dad8000000 0x7e4fffff80000017 0xb3f27ffffc000000

def z1086 : W := mkw 0x04a12c2c45964702 0x08250961622cb238 0x0d837c7c479e071d 0xd86c1be3e23cf038

def z1087 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db37c7c439e6719 0x186d9be3e21cf338

def z1088 : W := mkw 0xb1439636d89b85b8 0x158a1cb1b6c4dc2d 0xf1c39c7ff81f87fb 0xef8e1ce3ffc0fc3f

def z1089 : W := mkw 0xfb4e9393ba6980f8 0x37da749c9dd34c07 0xf24c8383b86180e2 0x2792641c1dc30c07

def z1090 : W := mkw 0x4ebc7bc927647a45 0x2275e3de493b23d2 0x0e3c7f8007e07804 0x1071e3fc003f03c0

def z1091 : W := mkw 0x04b56d6dc596e736 0x0825ab6b6e2cb739 0x8fffffffc79fe7ff 0xdc7ffffffe3cff3f

def z1092 : W := mkw 0x0011646444922704 0x00008b2322249138 0x0db37c7c479e671d 0xd86d9be3e23cf338

def z1093 : W := mkw 0x5a1edb5b00000000 0x22d0f6dad8000000 0x020fffff80000010 0x10107ffffc000000

def z1094 : W := mkw 0xfb429212ba4980b8 0x17da149095d24c05 0xf0408003b80180e2 0x278204001dc00c07

def z1095 : W := mkw 0x04a1242445964700 0x00250921222cb238 0x0db37c7c479e671d 0xd86d9be3e23cf338

def z1096 : W := mkw 0x4a000000334d5000 0x02500000019a6a80 0xfe7c00007ffff80f 0xeff3e00003ffffc0

def z1097 : W := mkw 0x7ffedb5b32491000 0x23fff6dad9924880 0xfffffffff87f981f 0xffffffffffc3fcc0

def z1098 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0xf27ce3e3fc71ffff 0xff93e71f1fe38fff

def z1099 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x827ce3e38071fffa 0x1413e71f1c038fff

def z1100 : W := mkw 0x800124a4dcbb87f8 0x1400092526e5dc3f 0x80000000781f87e0 0x4c00000003c0fc3f

def z1101 : W := mkw 0xfb4292123a490088 0x17da149091d24804 0x7000000038000000 0x2380000001c00000

def z1102 : W := mkw 0xfb42b2b2be7983f8 0x17da159595f3cc1f 0xf240e3e3bc7187fe 0xf792071f1de38c3f

def z1103 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0d837c7c478e0715 0xd86c1be3e23c7038

def z1104 : W := mkw 0x04b56d6dc596ef37 0x0825ab6b6e2cb779 0x0fffffffc79fff1f 0xd87ffffffe3cfff8

def z1105 : W := mkw 0x0001042440920500 0x0000082122049028 0x0d831c7c439e0719 0xc86c18e3e21cf038

def z1106 : W := mkw 0x04b56d6d45966706 0x0825ab6b6a2cb338 0x0fbf7ffc479e671d 0xd87dfbffe23cf338

def z1107 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfe7c00007ffff806 0x6ff3e00003ffffc0

def z1108 : W := mkw 0x3156db5b00000000 0x218ab6dad8000000 0x7043ffff80000012 0x33821ffffc000000

def z1109 : W := mkw 0x001469ed8432ab77 0x0800a34f6c21955b 0x827ce3ff8471fffe 0xd413e71ffc238fff

def z1110 : W := mkw 0x04a12c2c45966706 0x08250961622cb338 0x0d831c7c479e6719 0xc86c18e3e23cf338

def z1111 : W := mkw 0x7ffedb5b110d4000 0x23fff6dad8886a00 0xffffffffff9fe01f 0xfffffffffffcff00

def z1112 : W := mkw 0x7b56db5b00000000 0x23dab6dad8000000 0x7fc3ffff8000001f 0xb3fe1ffffc000000

def z1113 : W := mkw 0x04a10c2cc196c532 0x08250861660cb629 0x8dc39c7fc39f87fb 0xcc6e1ce3fe1cfc3f

def z1114 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x827c83e38471ffea 0x4413e41f1c238fff

def z1115 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x8db37c7c47ffff1d 0xdc6d9be3e23ffff8

def z1116 : W := mkw 0x5a0bb6806ee016c0 0x12d05db4037700b6 0xfe0fff807fe01ff7 0xfff07ffc03ff00ff

def z1117 : W := mkw 0x5ebedb5b00000000 0x22f5f6dad8000000 0x7e3fffff80000017 0xb3f1fffffc000000

def z1118 : W := mkw 0x6ffc5b5b00000000 0x237fe2dad8000000 0x0fff7fff8000001d 0x907ffbfffc000000

def z1119 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe4fff807fe19ff7 0xfff27ffc03ff0cff

def z1120 : W := mkw 0x04b14c4c41864402 0x08258a62620c3220 0x0db37c1c438e0005 0x186d9be0e21c7000

def z1121 : W := mkw 0x1016db5b00000000 0x2080b6dad8000000 0x023fffff80000014 0x1011fffffc000000

def z1122 : W := mkw 0x7ffedb5b23444000 0x23fff6dad91a2200 0xfffffffffffe601f 0xfffffffffffff300

def z1123 : W := mkw 0x04b14c6c41964502 0x08258a63620cb228 0x0db37c7c439e071d 0xd86d9be3e21cf038

def z1124 : W := mkw 0x04b16c6cc596e736 0x08258b63662cb739 0x0db3fc7fc79e67fd 0xd86d9fe3fe3cf33f

def z1125 : W := mkw 0xda03b6966ee206c8 0x16d01db4b3771036 0xfe03ff9c7fe007f7 0xfff01ffce3ff003f

def z1126 : W := mkw 0x7ffedb5b22400000 0x23fff6dad9120000 0xfffffffffff1f81f 0xffffffffffff8fc0

def z1127 : W := mkw 0xb1438036d81b85b8 0x058a1c01b6c0dc2d 0xf183807ff80e07f3 0xef8c1c03ffc0703f

def z1128 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0df3fc7fc79e671f 0xd86f9fe3fe3cf338

def z1129 : W := mkw 0x0014494900000000 0x0000a24a48000000 0x027fffff8000001e 0x9013fffffc000000

def z1130 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfffc80007fffffff 0xefffe40003ffffff

def z1131 : W := mkw 0x5a03b6004c800680 0x02d01db002640034 0xfe03ff807f8007f7 0xfff01ffc03fc003f

def z1132 : W := mkw 0x7ffedb5b00000000 0x23fff6dad8000000 0x7fffffffc01e001f 0xfbfffffffe00f000

def z1133 : W := mkw 0x5a03b6806ee006c0 0x12d01db403770036 0xfe00ff807fe007e6 0x7ff007fc03ff003f

def z1134 : W := mkw 0x04b16c6c45966706 0x08258b63622cb338 0x0db37c7c438e071d 0x986d9be3e21c7038

def z1135 : W := mkw 0x7ffedb5b334d5000 0x23fff6dad99a6a80 0xffffffffbfe1f81f 0xb7fffffffdff0fc0

def z1136 : W := mkw 0x5ebedb5b00000000 0x22f5f6dad8000000 0x0fbfffff8000001d 0x907dfffffc000000

def z1137 : W := mkw 0x000020a084308370 0x000001050421841b 0x827ce3e38471fffe 0xd413e71f1c238fff

def z1138 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xfffc8063fffff81f 0xefffe4031fffffc0

def z1139 : W := mkw 0x6fe80000334d5000 0x037f4000019a6a80 0xffff7c007ffff81f 0xfffffbe003ffffc0

def z1140 : W := mkw 0x04a12c0c45864602 0x08250960622c3230 0x0d837c1c438e0711 0x186c1be0e21c7038

def z1141 : W := mkw 0x04b56dedc5b6ef77 0x0825ab6f6e2db77b 0x0fff7fffc7ffff1d 0xd87ffbfffe3ffff8

def z1142 : W := mkw 0x001461e18430ab75 0x0000a30f0c21855b 0x827ce3838471ffe6 0x5413e71c1c238fff

def z1143 : W := mkw 0x04b16cecc5b6ef77 0x08258b67662db77b 0x8fb3fffc47ffffff 0xdc7d9fffe23fffff

def z1144 : W := mkw 0x04b14c4c41866406 0x08258a62620c3320 0x0db31c1c438e6001 0x086d98e0e21c7300

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(1,[z7,z1,z8,z4,z5,z6]),(0,[z7,z1,z3,z4,z9,z5,z6]),(0,[z10,z7,z11,z3,z4,z5,z6]),(0,[z12,z7,z1,z3,z4,z5,z6])],[],[(0,[z7,z1,z13,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z14,z6]),(0,[z15,z7,z1,z3,z4,z5,z6]),(0,[z16,z7,z3,z4,z17,z5,z6]),(0,[z7,z1,z3,z4,z5,z18,z6])],[(0,[z7,z19,z20,z3,z4,z5,z6]),(0,[z21,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z22,z5,z6])],[(0,[z7,z19,z3,z4,z5,z23,z6]),(0,[z0,z7,z1,z24,z4,z5,z6]),(0,[z7,z1,z25,z3,z4,z5,z6]),(0,[z26,z7,z1,z27,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z28,z6]),(0,[z7,z1,z3,z4,z5,z29,z6]),(0,[z7,z1,z30,z3,z4,z29,z6]),(0,[z7,z1,z31,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z32,z29,z6]),(0,[z7,z11,z3,z4,z17,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z33]),(0,[z34,z7,z1,z3,z4,z5,z6]),(0,[z35,z7,z1,z3,z4,z5,z6])],[(0,[z0,z7,z1,z2,z4,z5,z6]),(0,[z7,z1,z36,z3,z4,z5,z6]),(0,[z37,z7,z1,z3,z4,z38,z6]),(0,[z7,z1,z39,z3,z4,z5,z6]),(0,[z7,z1,z3,z40,z5,z29,z6]),(0,[z41,z7,z1,z3,z4,z5,z6])],[(0,[z42,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z43,z6]),(0,[z7,z1,z3,z4,z5,z6,z44]),(0,[z45,z7,z1,z3,z4,z5,z6]),(0,[z7,z46,z1,z3,z4,z5,z6]),(0,[z47,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z48,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z49,z6])]],
   [[(0,[z7,z19,z1,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z22,z5,z6]),(0,[z51,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z52]),(0,[z7,z1,z53,z3,z4,z5,z6]),(0,[z54,z7,z1,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z5,z29,z6]),(0,[z55,z7,z56,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z57,z6]),(0,[z7,z1,z3,z58,z4,z5,z6])],[(0,[z7,z1,z3,z4,z29,z59,z6]),(0,[z16,z7,z1,z3,z4,z17,z6]),(1,[z7,z1,z60,z4,z5,z61]),(0,[z7,z1,z20,z62,z3,z4,z6])],[(0,[z63,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z64,z3,z4,z5,z6]),(0,[z7,z65,z1,z3,z4,z5,z6]),(0,[z7,z66,z1,z3,z4,z5,z6])],[(0,[z42,z7,z50,z3,z4,z5,z6]),(0,[z7,z67,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z68]),(0,[z7,z1,z69,z3,z4,z5,z6])],[(0,[z51,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z70,z6]),(0,[z71,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z72,z3,z4,z5,z6]),(0,[z7,z73,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z74,z5,z6]),(0,[z7,z1,z3,z4,z29,z6,z75])],[(0,[z76,z7,z1,z3,z4,z5,z6])],[(0,[z77,z7,z1,z3,z4,z5,z6])]],
   [[(0,[z78,z7,z1,z3,z4,z5,z6]),(0,[z55,z7,z1,z79,z4,z5,z6]),(0,[z80,z7,z1,z3,z4,z32,z6]),(0,[z7,z1,z3,z4,z81,z5,z6]),(0,[z7,z1,z20,z3,z4,z22,z6]),(0,[z7,z1,z82,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z83,z6]),(0,[z7,z1,z3,z4,z5,z84,z6])],[(0,[z85,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z50,z3,z4,z5,z6]),(0,[z86,z7,z87,z3,z4,z5,z6]),(0,[z88,z7,z1,z3,z4,z32,z6]),(0,[z10,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z89,z3,z4,z5,z6]),(0,[z51,z7,z1,z3,z40,z5,z6]),(0,[z7,z1,z3,z4,z29,z38,z6]),(0,[z7,z1,z90,z3,z4,z5,z91])],[(0,[z7,z1,z92,z3,z4,z5,z6]),(0,[z7,z93,z1,z3,z4,z5,z6]),(0,[z94,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z95,z4,z96,z6]),(0,[z97,z7,z1,z3,z4,z5,z98]),(0,[z7,z99,z3,z4,z5,z29,z6])],[(0,[z7,z1,z3,z4,z5,z6,z100]),(0,[z7,z1,z3,z4,z4,z5,z6]),(0,[z101,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z102,z6]),(1,[z7,z3,z4,z103,z5,z6]),(0,[z7,z1,z20,z104,z3,z4,z6]),(1,[z7,z1,z3,z105,z4,z6])],[(0,[z7,z50,z3,z4,z81,z5,z6]),(0,[z7,z1,z106,z3,z4,z5,z6]),(0,[z7,z1,z3,z107,z4,z5,z6]),(0,[z108,z7,z1,z3,z4,z5,z6])],[(0,[z7,z19,z109,z3,z4,z5,z6]),(0,[z110,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z20,z27,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z6,z111])],[(0,[z7,z50,z50,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z5,z112,z6]),(0,[z7,z1,z3,z4,z5,z113,z6]),(0,[z55,z7,z1,z3,z4,z5,z6]),(1,[z26,z7,z114,z4,z5,z6]),(0,[z7,z1,z20,z3,z114,z4,z6]),(0,[z7,z115,z3,z116,z4,z5,z6]),(0,[z7,z1,z117,z3,z4,z5,z6]),(0,[z7,z1,z20,z20,z3,z4,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z6,z118]),(0,[z119,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z120,z6])],[(0,[z7,z67,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z121,z4,z5,z6]),(0,[z42,z7,z27,z3,z4,z5,z6]),(0,[z7,z1,z3,z122,z4,z5,z6]),(0,[z7,z1,z20,z109,z3,z4,z6]),(0,[z123,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z124,z5,z6])],[(0,[z7,z19,z62,z3,z4,z5,z6]),(0,[z7,z3,z116,z4,z17,z5,z6]),(0,[z7,z125,z1,z3,z4,z5,z6])],[(0,[z0,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z24,z4,z29,z6]),(0,[z7,z1,z3,z4,z126,z5,z6]),(0,[z127,z7,z1,z3,z4,z5,z6]),(0,[z128,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z129,z130,z3,z4,z6]),(0,[z7,z1,z3,z4,z131,z5,z6]),(0,[z7,z1,z132,z3,z4,z5,z6])],[(0,[z7,z1,z3,z95,z4,z5,z6]),(0,[z1,z3,z95,z4,z133,z5,z6]),(0,[z134,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z135,z4,z5,z6]),(0,[z7,z1,z136,z3,z4,z5,z6]),(0,[z7,z115,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z17,z5,z6]),(0,[z7,z1,z137,z3,z4,z5,z6])],[(0,[z138,z7,z1,z3,z4,z5,z6]),(0,[z139,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z140,z3,z4,z5,z6]),(0,[z7,z11,z1,z3,z116,z5,z6]),(0,[z7,z1,z3,z4,z5,z141,z6]),(0,[z7,z115,z1,z3,z4,z59,z6]),(0,[z142,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z143,z3,z4,z5,z6])],[(0,[z7,z1,z144,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z145]),(0,[z7,z146,z1,z3,z4,z5,z6])],[(0,[z7,z19,z3,z4,z5,z147,z6]),(0,[z7,z1,z3,z4,z148,z5,z6]),(0,[z7,z1,z27,z3,z4,z5,z6]),(1,[z7,z66,z3,z4,z5,z147]),(0,[z7,z1,z3,z4,z149,z5,z6])]],
   [[(0,[z0,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z133,z5,z6]),(0,[z150,z7,z1,z3,z4,z5,z6]),(0,[z97,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z20,z3,z4,z151,z6])],[(0,[z7,z50,z3,z95,z4,z5,z6]),(1,[z7,z50,z20,z3,z4,z6]),(0,[z7,z50,z3,z4,z17,z5,z6]),(0,[z7,z1,z152,z130,z3,z5,z6]),(1,[z7,z1,z3,z153,z4,z6])],[(0,[z154,z7,z1,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z155,z5,z6]),(0,[z7,z1,z3,z4,z29,z6,z98]),(0,[z7,z1,z156,z3,z4,z5,z6]),(0,[z7,z157,z1,z3,z4,z5,z6])],[(0,[z158,z7,z19,z3,z4,z5,z6]),(0,[z7,z56,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z159,z6]),(0,[z55,z7,z1,z3,z133,z5,z6]),(0,[z160,z7,z1,z3,z4,z5,z6]),(1,[z16,z7,z3,z4,z17,z6]),(0,[z7,z1,z161,z3,z4,z5,z6]),(0,[z162,z7,z1,z3,z4,z5,z6])],[(0,[z7,z50,z27,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z163]),(0,[z26,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z164,z5,z6]),(0,[z7,z1,z165,z3,z4,z29,z6])],[(0,[z7,z50,z3,z4,z133,z5,z6]),(1,[z7,z166,z3,z4,z5,z6]),(0,[z7,z167,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z116,z4,z168,z6]),(0,[z169,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z170,z4,z5,z6])],[(0,[z55,z7,z1,z3,z95,z5,z6]),(0,[z7,z171,z1,z3,z4,z5,z6]),(0,[z7,z1,z152,z3,z4,z5,z6]),(0,[z7,z1,z130,z3,z4,z29,z6]),(1,[z7,z1,z3,z4,z29,z6])],[(0,[z7,z1,z3,z4,z5,z172,z6]),(0,[z7,z1,z3,z4,z5,z173,z6]),(0,[z7,z1,z3,z4,z5,z6,z174])]],
   [[(0,[z158,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z175,z3,z4,z5,z6]),(0,[z7,z1,z3,z176,z4,z5,z6]),(0,[z7,z1,z3,z177,z4,z5,z6])],[(0,[z7,z1,z3,z4,z178,z5,z6]),(0,[z26,z7,z50,z3,z4,z5,z6]),(0,[z86,z7,z1,z20,z3,z4,z6]),(0,[z16,z7,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z147,z6,z179]),(0,[z180,z7,z1,z3,z4,z5,z6]),(0,[z181,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z182,z5,z6]),(0,[z7,z19,z3,z4,z5,z57,z6]),(0,[z7,z1,z183,z3,z4,z5,z6]),(0,[z80,z7,z115,z1,z3,z4,z6]),(0,[z7,z1,z3,z4,z184,z5,z6]),(0,[z7,z1,z185,z3,z4,z5,z6]),(0,[z7,z11,z1,z3,z4,z186,z6]),(0,[z10,z7,z1,z3,z116,z5,z6]),(0,[z16,z7,z1,z3,z4,z59,z6]),(0,[z7,z1,z3,z4,z29,z187,z6]),(0,[z7,z1,z3,z4,z5,z6,z188])],[(0,[z7,z50,z152,z3,z4,z5,z6]),(1,[z7,z189,z3,z4,z5,z6]),(0,[z7,z1,z190,z3,z4,z5,z6]),(0,[z7,z1,z152,z4,z22,z5,z6]),(0,[z7,z1,z3,z4,z191,z5,z6]),(0,[z7,z1,z3,z4,z29,z6,z91])],[(0,[z192,z7,z1,z3,z4,z5,z6]),(0,[z193,z7,z1,z3,z4,z5,z6]),(0,[z194,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z195,z4,z5,z6]),(0,[z7,z1,z196,z3,z4,z5,z6]),(0,[z7,z11,z1,z3,z4,z5,z6]),(0,[z197,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z60,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z6,z198]),(0,[z7,z199,z1,z3,z4,z5,z6]),(0,[z7,z1,z30,z3,z4,z5,z91])],[(0,[z200,z7,z1,z3,z4,z5,z6]),(0,[z7,z201,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z202,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z203]),(0,[z7,z1,z62,z3,z4,z204,z6]),(0,[z7,z1,z62,z3,z5,z120,z6])],[(0,[z7,z1,z205,z3,z4,z5,z6]),(0,[z206,z7,z1,z3,z4,z5,z6])],[(0,[z7,z19,z1,z3,z4,z29,z6]),(0,[z7,z1,z207,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z70,z6]),(0,[z7,z1,z3,z4,z208,z5,z6]),(0,[z150,z7,z209,z3,z4,z5,z6]),(0,[z210,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z211,z3,z4,z5,z6]),(0,[z7,z1,z212,z3,z4,z5,z6]),(0,[z7,z1,z60,z213,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z214,z6])]],
   [[(0,[z215,z7,z1,z3,z4,z5,z6]),(0,[z7,z66,z1,z3,z4,z5,z179]),(0,[z7,z1,z20,z152,z3,z4,z6]),(0,[z216,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z217,z3,z4,z5,z6]),(0,[z7,z11,z115,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z218,z29,z6])],[(0,[z7,z219,z1,z3,z4,z5,z6]),(0,[z7,z220,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z120,z98]),(0,[z7,z66,z1,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z6,z221])],[(0,[z7,z1,z222,z3,z4,z5,z6]),(0,[z7,z1,z223,z3,z4,z5,z6]),(0,[z7,z1,z224,z3,z4,z29,z6]),(0,[z225,z7,z1,z3,z4,z5,z6])],[(0,[z192,z1,z50,z3,z4,z5,z6]),(1,[z51,z7,z1,z20,z3,z6])],[(0,[z7,z226,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z227])],[(0,[z80,z7,z201,z3,z4,z5,z6]),(0,[z7,z1,z228,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z6,z179]),(1,[z7,z99,z3,z4,z29,z6]),(0,[z7,z1,z20,z3,z4,z229,z6])],[(0,[z7,z1,z3,z230,z4,z5,z6]),(1,[z7,z1,z3,z4,z231,z6]),(1,[z7,z1,z30,z3,z4,z91])]],
   [[(0,[z7,z1,z232,z3,z4,z5,z6]),(0,[z26,z7,z167,z3,z4,z5,z6]),(0,[z7,z1,z233,z3,z4,z5,z6]),(0,[z7,z1,z234,z3,z4,z5,z6]),(0,[z7,z1,z235,z3,z4,z5,z6]),(1,[z236,z7,z3,z4,z5,z6]),(0,[z237,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z238,z4,z5,z6])],[(0,[z7,z50,z3,z239,z4,z5,z6]),(0,[z7,z1,z50,z3,z4,z29,z6]),(0,[z7,z11,z19,z3,z4,z5,z6]),(0,[z7,z240,z1,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z112,z6]),(0,[z7,z1,z241,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z242])],[(0,[z7,z1,z3,z79,z4,z5,z6]),(0,[z7,z1,z3,z243,z4,z5,z6]),(0,[z244,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z245,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z246,z6]),(0,[z7,z1,z3,z4,z247,z5,z6])],[(0,[z19,z1,z50,z3,z4,z5,z6]),(0,[z7,z19,z2,z3,z4,z5,z6]),(1,[z7,z87,z3,z4,z5,z6]),(0,[z248,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z249,z5,z6]),(0,[z7,z1,z3,z250,z4,z5,z6]),(0,[z251,z7,z1,z3,z4,z29,z6]),(1,[z7,z3,z4,z103,z29,z6]),(0,[z7,z1,z3,z4,z4,z29,z6]),(0,[z252,z7,z1,z20,z3,z4,z6])],[(0,[z7,z11,z3,z4,z81,z5,z6]),(0,[z7,z1,z3,z4,z231,z5,z6])],[(0,[z253,z7,z1,z3,z4,z5,z6]),(0,[z7,z254,z50,z3,z4,z5,z6]),(0,[z255,z7,z1,z3,z4,z5,z6]),(1,[z88,z1,z3,z4,z57,z6]),(0,[z7,z1,z3,z4,z5,z6,z256]),(0,[z42,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z40,z4,z29,z6]),(0,[z7,z1,z3,z4,z29,z83,z6])],[(0,[z55,z7,z1,z3,z4,z29,z6]),(0,[z88,z7,z257,z3,z4,z5,z6]),(0,[z51,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z23,z6]),(1,[z7,z1,z3,z4,z141,z6])]],
   [[(0,[z7,z19,z258,z3,z4,z5,z6]),(0,[z259,z7,z19,z3,z4,z5,z6]),(0,[z88,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z260,z6])],[(0,[z7,z1,z3,z261,z4,z5,z6]),(0,[z7,z1,z3,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z147,z6]),(0,[z262,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z20,z263,z3,z4,z6]),(0,[z7,z1,z3,z4,z264,z5,z6])],[(0,[z265,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z266,z5,z6])],[(0,[z7,z1,z1,z3,z4,z5,z6]),(0,[z7,z50,z3,z116,z4,z5,z6]),(0,[z85,z7,z1,z3,z4,z5,z6]),(0,[z158,z1,z3,z24,z4,z5,z6]),(0,[z7,z1,z3,z267,z4,z5,z6]),(0,[z7,z1,z3,z4,z17,z29,z6]),(0,[z268,z7,z1,z3,z4,z29,z6]),(0,[z7,z269,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z270,z6]),(0,[z7,z1,z90,z3,z4,z5,z38])],[(0,[z7,z1,z3,z4,z5,z6,z271]),(0,[z7,z19,z90,z3,z4,z5,z6]),(0,[z7,z272,z1,z3,z4,z5,z6])],[(0,[z7,z19,z3,z273,z4,z5,z6]),(0,[z10,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z274,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z275]),(0,[z7,z1,z3,z114,z4,z29,z6]),(0,[z7,z1,z27,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z6,z276])],[(0,[z277,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z278,z6]),(0,[z55,z7,z1,z3,z4,z70,z6]),(0,[z7,z1,z3,z4,z133,z29,z6]),(0,[z150,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z279,z5,z6]),(1,[z7,z1,z224,z4,z112,z6]),(0,[z7,z1,z3,z4,z5,z280,z6])]],
   [[(0,[z281,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z20,z3,z29,z6])],[(0,[z7,z1,z3,z4,z282,z5,z6]),(0,[z283,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z231,z6,z61])],[(0,[z7,z284,z1,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z5,z6,z276]),(0,[z10,z7,z50,z3,z4,z5,z6]),(1,[z285,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z286]),(0,[z7,z209,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z287,z6,z61]),(0,[z7,z1,z288,z3,z4,z5,z6])],[(0,[z7,z289,z50,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z290,z6]),(0,[z7,z1,z291,z3,z4,z5,z6]),(0,[z7,z167,z1,z3,z4,z29,z6]),(0,[z7,z1,z292,z3,z4,z5,z6])],[(0,[z285,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z293,z6]),(0,[z7,z1,z20,z3,z4,z81,z6]),(0,[z294,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z20,z3,z4,z120,z6])],[(0,[z7,z295,z1,z3,z4,z5,z6]),(1,[z37,z7,z1,z109,z4,z6]),(0,[z7,z1,z3,z4,z5,z296,z6])],[(0,[z7,z1,z3,z4,z297,z5,z6]),(1,[z7,z298,z3,z4,z5,z6]),(0,[z7,z1,z299,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z300]),(0,[z7,z1,z3,z4,z5,z6,z301])]],
   [[(0,[z7,z19,z3,z302,z4,z5,z6]),(0,[z7,z166,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z303,z6]),(0,[z7,z304,z1,z3,z4,z5,z6]),(0,[z305,z7,z1,z3,z4,z5,z6])],[(0,[z0,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z306,z3,z4,z5,z6]),(0,[z7,z1,z307,z3,z4,z5,z6]),(0,[z7,z3,z116,z4,z81,z5,z6]),(0,[z7,z1,z308,z3,z22,z5,z6]),(0,[z7,z1,z309,z3,z4,z5,z6]),(0,[z7,z1,z109,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z204,z6])],[(0,[z7,z19,z3,z4,z310,z5,z6]),(0,[z7,z19,z311,z3,z4,z5,z6]),(0,[z312,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z313,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z314]),(1,[z7,z1,z20,z3,z4,z6]),(0,[z7,z99,z1,z3,z4,z5,z6])],[(0,[z192,z7,z1,z3,z4,z29,z6])],[(0,[z97,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z315,z3,z4,z5,z6])],[(0,[z16,z88,z7,z1,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z151,z276])],[(0,[z7,z50,z109,z3,z4,z5,z6]),(0,[z7,z1,z3,z316,z4,z5,z6]),(0,[z7,z1,z317,z3,z4,z5,z6]),(0,[z7,z1,z318,z3,z4,z5,z6])],[(0,[z285,z7,z1,z20,z3,z4,z6]),(0,[z7,z19,z3,z4,z5,z6,z179]),(0,[z7,z1,z3,z319,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z6,z98]),(0,[z7,z1,z320,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z6,z321]),(0,[z7,z1,z60,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z103,z5,z6]),(0,[z7,z3,z4,z103,z5,z29,z6])],[(0,[z97,z7,z50,z3,z4,z5,z6]),(0,[z158,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z6,z61])],[(0,[z322,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z323,z6]),(0,[z26,z7,z1,z3,z4,z5,z6])],[(0,[z7,z19,z1,z20,z3,z4,z6]),(0,[z55,z7,z1,z8,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z324,z6]),(0,[z7,z1,z3,z4,z5,z325,z6]),(0,[z7,z1,z104,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z326,z6]),(0,[z80,z7,z1,z3,z4,z57,z6]),(0,[z327,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z213,z3,z4,z5,z6]),(0,[z328,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z329,z3,z4,z5,z6])],[(0,[z86,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z155,z5,z6]),(0,[z330,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z331,z5,z6])],[(0,[z88,z7,z1,z3,z4,z57,z6]),(0,[z7,z1,z3,z4,z5,z6,z332]),(0,[z7,z1,z30,z3,z4,z5,z38])],[(1,[z7,z19,z20,z3,z4,z6]),(0,[z7,z19,z30,z3,z4,z5,z6]),(1,[z7,z333,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z334]),(0,[z7,z1,z20,z3,z4,z187,z6])]],
   [[(0,[z7,z19,z3,z4,z32,z5,z6]),(0,[z7,z19,z3,z4,z5,z59,z6]),(1,[z7,z335,z3,z4,z5,z6]),(0,[z7,z27,z3,z4,z5,z147,z6]),(0,[z7,z1,z336,z3,z4,z5,z6]),(0,[z7,z1,z224,z4,z5,z112,z6]),(0,[z7,z1,z3,z4,z5,z6,z337]),(0,[z51,z7,z1,z20,z3,z5,z6]),(0,[z7,z338,z1,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z6,z91]),(0,[z7,z1,z339,z3,z4,z5,z6]),(0,[z7,z1,z3,z340,z4,z5,z6])],[(0,[z7,z50,z213,z3,z4,z5,z6]),(0,[z7,z341,z1,z3,z4,z5,z6]),(1,[z7,z201,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z342,z6]),(0,[z7,z1,z343,z3,z4,z5,z6]),(0,[z344,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z105,z4,z5,z6]),(0,[z345,z7,z1,z3,z4,z5,z6])],[(0,[z86,z7,z50,z3,z4,z5,z6]),(0,[z346,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z17,z6]),(0,[z42,z7,z1,z3,z4,z5,z179]),(0,[z7,z1,z308,z3,z4,z5,z6]),(0,[z347,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z311,z3,z4,z348,z6])],[(0,[z7,z1,z349,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z350,z6]),(0,[z351,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z352,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z353,z5,z6]),(0,[z7,z1,z3,z354,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z355,z6]),(0,[z7,z1,z3,z4,z5,z6,z356]),(0,[z7,z1,z357,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z358,z5,z6]),(0,[z7,z1,z3,z4,z5,z57,z6]),(0,[z7,z1,z3,z116,z4,z29,z6]),(0,[z7,z66,z3,z4,z5,z147,z6])],[(0,[z7,z1,z3,z359,z4,z5,z6]),(0,[z7,z1,z360,z3,z4,z5,z6]),(0,[z150,z7,z1,z3,z4,z5,z98]),(0,[z7,z1,z3,z4,z29,z246,z6]),(0,[z7,z1,z311,z3,z4,z5,z276])],[(0,[z7,z50,z308,z3,z4,z5,z6]),(0,[z55,z7,z298,z3,z4,z5,z6]),(1,[z7,z257,z3,z4,z5,z6]),(0,[z7,z1,z361,z3,z4,z5,z6]),(0,[z7,z1,z362,z3,z4,z5,z6]),(0,[z37,z7,z1,z3,z4,z29,z6])]],
   [[(0,[z7,z19,z3,z4,z5,z38,z6]),(0,[z1,z2,z3,z24,z4,z5,z6]),(0,[z7,z1,z3,z4,z363,z5,z6]),(0,[z7,z364,z1,z3,z4,z5,z6]),(0,[z365,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z366,z3,z4,z5,z6]),(0,[z7,z1,z20,z90,z3,z4,z6])],[(0,[z7,z1,z3,z4,z367,z5,z6]),(0,[z7,z1,z3,z368,z4,z5,z6]),(0,[z7,z1,z308,z152,z4,z5,z6]),(0,[z369,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z6,z370]),(0,[z7,z1,z3,z4,z371,z5,z6])],[(0,[z7,z50,z3,z4,z5,z57,z6]),(0,[z7,z1,z3,z4,z5,z6,z372]),(0,[z80,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z373,z5,z6]),(0,[z7,z1,z20,z30,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z6,z374])],[(0,[z86,z7,z375,z3,z4,z5,z6]),(0,[z97,z7,z1,z3,z4,z5,z151]),(0,[z7,z11,z1,z3,z81,z5,z6]),(0,[z7,z1,z376,z3,z4,z5,z6]),(0,[z7,z1,z377,z3,z4,z5,z6])],[(0,[z88,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z378,z5,z6]),(0,[z7,z1,z3,z4,z5,z379,z6])],[(0,[z7,z1,z3,z4,z5,z380,z6]),(0,[z7,z381,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z6]),(0,[z382,z7,z1,z3,z4,z5,z6]),(0,[z383,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z384,z4,z5,z6]),(0,[z7,z1,z3,z4,z22,z29,z6]),(0,[z7,z1,z60,z3,z4,z5,z187]),(0,[z7,z1,z385,z3,z4,z5,z6]),(0,[z386,z7,z1,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z367,z5,z6]),(0,[z7,z254,z1,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z5,z120,z6]),(0,[z1,z3,z4,z5,z151,z6,z98]),(0,[z7,z387,z1,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z5,z6,z372]),(0,[z7,z1,z189,z3,z4,z5,z6]),(0,[z7,z1,z388,z3,z95,z4,z6]),(0,[z88,z7,z115,z1,z3,z4,z6]),(0,[z389,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z390,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z348,z6])]],
   [[(0,[z55,z1,z3,z4,z133,z5,z6]),(1,[z7,z1,z62,z3,z5,z120])],[(0,[z7,z19,z66,z3,z4,z5,z6]),(0,[z26,z7,z3,z4,z5,z147,z6]),(0,[z7,z1,z391,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z392,z6]),(0,[z47,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z62,z3,z4,z5,z276])],[(0,[z7,z1,z393,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z6,z276]),(0,[z7,z1,z3,z4,z5,z204,z6])],[(0,[z7,z1,z3,z4,z394,z5,z6]),(0,[z7,z1,z395,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z29,z6])],[(0,[z88,z1,z3,z4,z5,z57,z6]),(0,[z7,z1,z396,z3,z4,z5,z6]),(0,[z7,z1,z397,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z398,z6]),(0,[z7,z1,z399,z3,z4,z5,z6]),(0,[z7,z1,z3,z400,z4,z5,z6]),(0,[z7,z1,z401,z3,z4,z5,z6])],[(0,[z7,z19,z3,z24,z4,z5,z6]),(0,[z259,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z97,z1,z3,z4,z5,z6,z98]),(0,[z7,z1,z3,z4,z5,z402,z6]),(0,[z7,z1,z403,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z404])],[(0,[z10,z7,z3,z116,z4,z5,z6])]],
   [[(0,[z7,z19,z3,z4,z5,z6,z98]),(0,[z7,z1,z3,z4,z405,z5,z6]),(0,[z1,z3,z4,z32,z5,z57,z6]),(0,[z7,z1,z3,z406,z4,z5,z6]),(0,[z7,z1,z407,z3,z4,z5,z6])],[(0,[z7,z99,z1,z3,z4,z29,z6]),(0,[z294,z7,z1,z20,z3,z4,z6])],[(0,[z7,z1,z3,z4,z81,z29,z6]),(0,[z7,z1,z3,z4,z5,z6,z408]),(0,[z409,z7,z1,z3,z4,z5,z6])],[(0,[z7,z50,z2,z3,z4,z5,z6]),(0,[z7,z1,z258,z3,z4,z5,z6]),(0,[z7,z1,z2,z4,z22,z5,z6]),(0,[z7,z1,z3,z4,z186,z5,z6]),(0,[z7,z410,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z411,z6])],[(0,[z7,z1,z3,z4,z5,z412,z6]),(0,[z7,z1,z413,z3,z4,z5,z6]),(0,[z414,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z151,z6]),(0,[z415,z7,z1,z3,z4,z5,z6]),(0,[z10,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z416,z5,z6]),(0,[z417,z7,z1,z3,z4,z5,z6])],[(0,[z418,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z419,z6]),(0,[z7,z1,z3,z4,z5,z420,z6])],[(0,[z192,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z421,z6]),(0,[z97,z7,z232,z3,z4,z5,z6]),(0,[z7,z66,z1,z3,z4,z5,z147]),(1,[z7,z1,z129,z3,z4,z6])]],
   [[(0,[z7,z19,z3,z4,z5,z187,z6]),(0,[z7,z1,z24,z4,z22,z5,z6]),(0,[z7,z422,z1,z3,z4,z5,z6]),(0,[z7,z1,z90,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z5,z151,z6]),(0,[z7,z19,z130,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z5,z6,z91]),(0,[z7,z1,z3,z273,z4,z5,z6]),(0,[z423,z7,z1,z3,z4,z5,z6]),(0,[z26,z7,z1,z3,z4,z29,z6]),(1,[z7,z1,z3,z4,z424,z6]),(0,[z7,z1,z130,z3,z4,z424,z6]),(0,[z7,z1,z224,z3,z4,z112,z6]),(0,[z7,z1,z20,z3,z4,z5,z6]),(0,[z7,z1,z117,z3,z4,z29,z6])],[(0,[z425,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z336,z3,z116,z4,z6]),(0,[z7,z1,z20,z3,z4,z59,z6]),(0,[z7,z1,z3,z4,z5,z342,z6]),(0,[z7,z1,z426,z3,z4,z5,z6]),(0,[z7,z1,z60,z3,z4,z5,z61])],[(0,[z7,z1,z3,z427,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z428,z6]),(0,[z7,z1,z213,z3,z4,z29,z6])],[(0,[z429,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z430,z3,z4,z5,z6])],[(0,[z7,z50,z90,z3,z4,z5,z6]),(0,[z158,z7,z189,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z431])],[(1,[z192,z50,z3,z4,z5,z6]),(1,[z7,z92,z50,z3,z4,z6]),(0,[z7,z50,z20,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z208,z6]),(0,[z7,z1,z3,z95,z4,z29,z6]),(0,[z7,z1,z432,z3,z4,z5,z6]),(0,[z7,z115,z1,z3,z4,z29,z6]),(0,[z7,z1,z20,z3,z40,z4,z6])],[(0,[z7,z19,z60,z3,z4,z5,z6]),(0,[z433,z7,z1,z3,z4,z5,z6]),(1,[z7,z167,z27,z4,z5,z6]),(0,[z7,z1,z434,z3,z4,z5,z6]),(0,[z7,z3,z4,z17,z5,z59,z6]),(0,[z7,z435,z1,z3,z4,z5,z6]),(0,[z7,z1,z436,z3,z4,z5,z6]),(0,[z7,z1,z3,z437,z4,z5,z6])]],
   [[(0,[z97,z7,z438,z3,z4,z5,z6]),(0,[z439,z7,z1,z3,z4,z5,z6]),(0,[z440,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z326,z6]),(0,[z441,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z442,z5,z6])],[(0,[z7,z1,z443,z3,z4,z5,z6]),(0,[z7,z1,z3,z444,z4,z5,z6]),(0,[z7,z1,z308,z3,z4,z29,z6]),(0,[z7,z1,z109,z224,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z445,z6]),(0,[z7,z1,z446,z3,z4,z5,z6]),(0,[z7,z1,z447,z3,z4,z5,z6]),(0,[z7,z1,z90,z3,z4,z38,z6])],[(0,[z7,z448,z1,z3,z4,z5,z6]),(0,[z97,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z120,z151]),(0,[z7,z1,z3,z4,z449,z5,z6]),(0,[z7,z1,z20,z3,z4,z38,z6]),(0,[z7,z1,z450,z3,z4,z5,z6])],[(1,[z7,z50,z3,z4,z5,z6]),(0,[z285,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z451,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z452,z6]),(0,[z7,z1,z453,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z454,z5,z6]),(0,[z7,z1,z152,z3,z153,z4,z6])],[(0,[z7,z1,z3,z4,z455,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z456]),(0,[z42,z7,z3,z4,z5,z6,z179])],[(0,[z457,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z310,z5,z6]),(0,[z7,z1,z3,z4,z458,z5,z6]),(0,[z7,z1,z3,z4,z459,z5,z6]),(0,[z7,z1,z311,z3,z4,z5,z6]),(0,[z7,z1,z3,z5,z120,z6,z276])],[(0,[z7,z1,z3,z4,z460,z5,z6]),(0,[z7,z19,z224,z3,z4,z5,z6]),(0,[z7,z1,z461,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z6,z61]),(0,[z462,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z463])],[(0,[z7,z1,z464,z3,z4,z5,z6]),(1,[z7,z3,z4,z5,z6,z111])]],
   [[(0,[z7,z1,z152,z3,z4,z29,z6]),(0,[z7,z1,z465,z3,z4,z5,z6])],[(0,[z7,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z57,z6]),(1,[z7,z1,z3,z4,z348,z6])],[(0,[z7,z50,z311,z3,z4,z5,z6]),(0,[z150,z1,z3,z4,z5,z151,z6]),(0,[z7,z1,z466,z3,z4,z5,z6]),(1,[z7,z1,z336,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z6,z179]),(0,[z7,z1,z3,z4,z5,z6,z467]),(0,[z7,z1,z468,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z460,z5,z6]),(0,[z86,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z298,z3,z4,z5,z6]),(0,[z7,z1,z3,z469,z4,z5,z6]),(0,[z16,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z470,z3,z4,z5,z6]),(0,[z37,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z471,z5,z6])],[(0,[z7,z19,z50,z3,z4,z5,z6]),(0,[z7,z1,z472,z3,z4,z5,z6]),(1,[z7,z375,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z473,z6]),(0,[z7,z1,z3,z4,z5,z474,z6]),(0,[z7,z1,z3,z475,z4,z5,z6]),(0,[z383,z7,z1,z3,z4,z29,z6])],[(1,[z7,z1,z92,z3,z4,z6]),(0,[z476,z7,z1,z3,z4,z5,z6]),(0,[z80,z7,z25,z3,z4,z5,z6]),(0,[z7,z1,z477,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z112,z6]),(0,[z37,z7,z1,z109,z3,z4,z6]),(0,[z7,z1,z3,z478,z4,z5,z6]),(0,[z7,z1,z3,z4,z479,z5,z6])],[(0,[z7,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z480,z3,z4,z5,z6]),(0,[z7,z11,z1,z3,z4,z29,z6]),(0,[z7,z1,z481,z3,z4,z5,z6]),(0,[z7,z1,z20,z213,z3,z4,z6]),(0,[z482,z7,z1,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z5,z6,z179]),(0,[z483,z7,z1,z3,z4,z5,z6])]],
   [[(0,[z7,z19,z3,z40,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z133,z6]),(1,[z97,z1,z3,z4,z5,z98]),(0,[z484,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z485,z3,z4,z5,z6]),(0,[z7,z1,z486,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z487,z6]),(0,[z7,z1,z62,z3,z4,z5,z6])],[(0,[z7,z1,z488,z3,z4,z5,z6]),(0,[z489,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z490,z3,z4,z5,z6])],[(0,[z76,z7,z50,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z5,z112,z6]),(0,[z457,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z491,z4,z5,z6]),(0,[z492,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z30,z3,z4,z5,z6])],[(0,[z7,z1,z20,z2,z3,z4,z6]),(0,[z7,z1,z493,z3,z4,z5,z6]),(0,[z494,z7,z1,z3,z4,z5,z6]),(0,[z35,z7,z1,z20,z3,z4,z6])],[(0,[z7,z1,z3,z495,z4,z5,z6]),(0,[z7,z496,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z497,z5,z6]),(0,[z7,z1,z498,z3,z4,z5,z6])],[(0,[z7,z50,z62,z3,z4,z5,z6]),(0,[z7,z499,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z147,z6]),(0,[z7,z1,z308,z152,z3,z5,z6])],[(0,[z80,z7,z19,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z17,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z500]),(0,[z7,z1,z501,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z75])],[(0,[z502,z7,z1,z3,z4,z5,z6]),(0,[z7,z50,z30,z3,z4,z5,z6]),(0,[z86,z7,z1,z3,z133,z5,z6]),(0,[z503,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z504,z6])]],
   [[(0,[z88,z7,z19,z3,z4,z5,z6])],[(0,[z7,z19,z3,z114,z4,z5,z6]),(0,[z7,z19,z27,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z98,z276]),(0,[z7,z66,z1,z20,z3,z4,z6]),(0,[z7,z505,z1,z3,z4,z5,z6])],[(0,[z7,z1,z506,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z5,z147,z6]),(0,[z7,z19,z3,z4,z133,z5,z6]),(0,[z86,z7,z1,z3,z95,z5,z6]),(0,[z7,z1,z3,z507,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z424,z6])],[(0,[z80,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z116,z4,z6])],[(0,[z7,z19,z3,z4,z5,z508,z6]),(0,[z7,z1,z3,z4,z5,z509,z6]),(0,[z7,z1,z3,z4,z5,z510,z6])],[(0,[z88,z7,z50,z3,z4,z5,z6]),(0,[z7,z511,z50,z3,z4,z5,z6]),(0,[z252,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z512,z6]),(0,[z7,z1,z3,z4,z5,z513,z6]),(0,[z7,z1,z3,z514,z4,z5,z6]),(0,[z7,z1,z109,z4,z5,z112,z6])],[(0,[z7,z19,z3,z4,z5,z6,z163]),(0,[z236,z7,z3,z4,z5,z6,z61])],[(0,[z42,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z515,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z50,z20,z3,z4,z6]),(0,[z80,z1,z3,z4,z32,z5,z6]),(0,[z7,z1,z3,z4,z29,z151,z6]),(0,[z516,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z517,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z29,z6]),(0,[z51,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z20,z3,z58,z4,z6])],[(0,[z7,z1,z3,z4,z5,z518,z6]),(0,[z7,z1,z3,z4,z5,z120,z6])],[(1,[z7,z1,z3,z4,z5,z118]),(0,[z7,z1,z3,z4,z519,z5,z6]),(0,[z7,z520,z1,z3,z4,z5,z6]),(1,[z7,z1,z90,z3,z4,z38])],[(0,[z80,z16,z7,z1,z3,z4,z6]),(0,[z7,z1,z3,z4,z521,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z522])],[(0,[z7,z1,z3,z523,z4,z5,z6]),(1,[z86,z1,z3,z95,z5,z6]),(0,[z7,z1,z524,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z525,z6]),(0,[z7,z1,z129,z3,z4,z5,z6])],[(0,[z294,z7,z19,z3,z4,z5,z6]),(0,[z55,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z526,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z527])],[(0,[z7,z50,z3,z4,z5,z120,z6]),(0,[z7,z1,z3,z4,z528,z5,z6]),(0,[z7,z1,z60,z4,z5,z6,z61])],[(0,[z7,z19,z3,z4,z5,z6,z61]),(0,[z7,z1,z3,z4,z529,z5,z6]),(0,[z7,z11,z1,z3,z4,z141,z6])]],
   [[(0,[z530,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z24,z4,z5,z6]),(1,[z7,z232,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z531,z5,z6]),(0,[z42,z7,z1,z3,z4,z5,z147]),(0,[z7,z1,z532,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z533,z6])],[(0,[z294,z7,z50,z3,z4,z5,z6]),(0,[z7,z115,z1,z20,z3,z4,z6]),(0,[z7,z1,z534,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z4,z6]),(0,[z7,z1,z137,z20,z3,z4,z6])],[(0,[z535,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z388,z3,z4,z6]),(0,[z7,z1,z3,z536,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z98]),(0,[z7,z1,z537,z3,z4,z5,z6])],[(0,[z97,z150,z1,z3,z4,z5,z6]),(0,[z7,z1,z311,z3,z4,z29,z6]),(0,[z7,z1,z20,z3,z5,z29,z6])],[(0,[z55,z86,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z538,z4,z5,z6]),(1,[z7,z1,z130,z22,z5,z6]),(0,[z539,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z308,z20,z3,z4,z6]),(0,[z37,z7,z1,z3,z4,z112,z6])],[(0,[z7,z50,z3,z24,z4,z5,z6]),(0,[z7,z1,z540,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z541,z6]),(0,[z150,z7,z1,z20,z3,z4,z6])],[(0,[z7,z1,z3,z4,z5,z6,z542]),(0,[z7,z115,z3,z4,z5,z59,z6]),(0,[z7,z1,z543,z3,z4,z5,z6])]],
   [[(0,[z192,z7,z50,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z5,z6,z98]),(0,[z7,z1,z3,z544,z4,z5,z6]),(0,[z7,z1,z3,z4,z545,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z546]),(0,[z7,z1,z20,z224,z3,z4,z6])],[(0,[z0,z7,z166,z3,z4,z5,z6]),(0,[z547,z7,z1,z3,z4,z5,z6]),(1,[z7,z438,z3,z4,z5,z6]),(0,[z42,z26,z7,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z186,z6]),(0,[z7,z1,z3,z4,z548,z5,z6]),(0,[z7,z1,z3,z4,z5,z287,z6])],[(0,[z0,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z549,z6]),(0,[z7,z167,z1,z20,z3,z4,z6]),(0,[z10,z7,z1,z3,z81,z5,z6]),(0,[z550,z7,z1,z3,z4,z5,z6]),(1,[z42,z7,z3,z4,z5,z179]),(0,[z7,z1,z109,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z187,z6]),(0,[z7,z1,z3,z4,z5,z6,z551])],[(0,[z285,z192,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z552,z5,z6]),(0,[z7,z553,z1,z3,z4,z5,z6]),(0,[z7,z1,z130,z3,z4,z5,z6]),(0,[z7,z1,z30,z3,z4,z6,z91]),(0,[z7,z1,z3,z4,z5,z6,z91])],[(0,[z554,z7,z1,z3,z4,z5,z6]),(0,[z158,z0,z1,z3,z4,z5,z6]),(0,[z555,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z32,z6]),(0,[z7,z438,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z556,z5,z6])],[(0,[z7,z1,z3,z4,z5,z557,z6]),(0,[z150,z7,z1,z3,z4,z5,z151]),(0,[z7,z167,z27,z3,z4,z5,z6]),(0,[z7,z1,z558,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z6,z179]),(0,[z7,z1,z559,z3,z4,z5,z6])],[(0,[z285,z19,z1,z3,z4,z5,z6]),(1,[z80,z1,z3,z4,z32,z6]),(0,[z7,z1,z3,z4,z560,z5,z6]),(0,[z16,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z62,z3,z4,z29,z6]),(0,[z7,z1,z311,z3,z5,z6,z276])]],
   [[(0,[z7,z50,z3,z4,z5,z187,z6]),(0,[z7,z19,z3,z116,z4,z5,z6]),(1,[z7,z25,z3,z4,z5,z6]),(0,[z7,z167,z1,z114,z4,z5,z6]),(0,[z7,z1,z561,z3,z4,z5,z6])],[(0,[z285,z7,z1,z3,z4,z5,z6]),(0,[z7,z50,z130,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z5,z6,z91]),(0,[z7,z562,z19,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z95,z4,z6]),(0,[z7,z1,z130,z4,z22,z5,z6]),(0,[z7,z1,z3,z4,z29,z112,z6])],[(0,[z55,z7,z1,z3,z4,z5,z118]),(0,[z7,z1,z87,z3,z4,z5,z6]),(1,[z7,z11,z3,z81,z5,z6]),(0,[z7,z11,z1,z20,z3,z4,z6]),(1,[z7,z115,z3,z4,z59,z6]),(0,[z7,z1,z3,z4,z5,z6,z563]),(0,[z7,z1,z3,z4,z5,z564,z6]),(0,[z7,z1,z565,z3,z4,z5,z6]),(0,[z7,z1,z60,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z103,z29,z6]),(0,[z197,z7,z1,z20,z3,z4,z6])],[(0,[z566,z7,z1,z3,z4,z5,z6]),(0,[z158,z7,z1,z3,z4,z29,z6]),(0,[z567,z7,z1,z3,z4,z5,z6]),(0,[z568,z7,z1,z3,z4,z5,z6])],[(0,[z7,z1,z511,z3,z4,z5,z6]),(0,[z7,z1,z569,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z168,z6]),(0,[z7,z1,z213,z3,z4,z5,z187]),(0,[z570,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z30,z90,z3,z4,z6])],[(0,[z76,z7,z1,z50,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z571,z6]),(0,[z7,z1,z3,z4,z5,z572,z6]),(0,[z7,z1,z3,z4,z5,z6,z370])],[(0,[z7,z1,z3,z4,z5,z573,z6]),(0,[z7,z1,z3,z4,z5,z574,z6]),(0,[z7,z575,z1,z3,z4,z5,z6])],[(0,[z7,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z576,z5,z6]),(0,[z7,z50,z60,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z577,z6]),(1,[z76,z7,z1,z3,z4,z6]),(0,[z37,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z578,z5,z6]),(1,[z150,z1,z3,z4,z5,z151]),(0,[z7,z1,z3,z4,z5,z6,z579]),(0,[z7,z580,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z218,z5,z6]),(0,[z7,z1,z3,z4,z38,z6,z91]),(0,[z7,z1,z581,z3,z4,z5,z6])]],
   [[(0,[z582,z7,z1,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z22,z5,z6]),(0,[z7,z19,z3,z4,z5,z6,z276]),(0,[z583,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z584,z3,z4,z5,z6])],[(1,[z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z289,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z5,z29,z6]),(0,[z158,z7,z1,z24,z4,z5,z6]),(0,[z585,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z147,z6]),(0,[z7,z1,z224,z3,z4,z5,z6])],[(0,[z7,z1,z92,z50,z3,z4,z6]),(0,[z7,z19,z115,z3,z4,z5,z6]),(1,[z7,z307,z3,z4,z5,z6]),(0,[z7,z1,z586,z3,z4,z5,z6])],[(0,[z158,z7,z1,z2,z4,z5,z6]),(1,[z158,z1,z24,z4,z5,z6]),(1,[z7,z209,z3,z4,z5,z6]),(0,[z7,z1,z152,z3,z4,z342,z6]),(0,[z344,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z587,z62,z3,z4,z6])],[(1,[z19,z50,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z5,z577,z6]),(0,[z37,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z588,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z589,z5,z6]),(1,[z7,z99,z3,z4,z5,z6])],[(0,[z590,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z591,z3,z4,z5,z6]),(0,[z80,z88,z1,z3,z4,z5,z6]),(0,[z7,z1,z592,z3,z4,z5,z6]),(0,[z593,z7,z1,z3,z4,z5,z6])],[(0,[z7,z50,z224,z3,z4,z5,z6]),(0,[z7,z1,z3,z302,z4,z5,z6]),(0,[z7,z1,z3,z594,z4,z5,z6]),(0,[z7,z1,z595,z3,z4,z5,z6]),(0,[z7,z1,z596,z3,z4,z5,z6]),(0,[z597,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z598,z3,z4,z5,z6]),(0,[z7,z1,z233,z20,z3,z4,z6]),(0,[z7,z1,z234,z20,z3,z4,z6])],[(0,[z7,z1,z3,z4,z5,z599,z6]),(0,[z7,z1,z3,z4,z600,z5,z6]),(0,[z7,z167,z1,z27,z4,z5,z6])]],
   [[(0,[z7,z1,z601,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z602,z6]),(0,[z37,z7,z1,z224,z4,z5,z6])],[(0,[z251,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z603])],[(0,[z604,z7,z1,z3,z4,z5,z6]),(0,[z7,z19,z19,z3,z4,z5,z6]),(0,[z7,z1,z308,z24,z4,z5,z6]),(0,[z605,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z606]),(0,[z7,z1,z30,z224,z3,z4,z6]),(0,[z7,z1,z224,z3,z4,z38,z6])],[(0,[z42,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z3,z40,z4,z5,z6]),(0,[z7,z1,z20,z311,z3,z4,z6])],[(0,[z7,z1,z3,z4,z5,z6,z607]),(0,[z7,z1,z308,z2,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z96,z6]),(0,[z80,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z608,z4,z5,z6]),(0,[z7,z1,z3,z609,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z610,z6]),(1,[z7,z1,z213,z4,z5,z187]),(0,[z7,z1,z3,z4,z611,z5,z6]),(0,[z51,z7,z1,z20,z3,z4,z6])],[(0,[z7,z19,z3,z4,z81,z5,z6]),(1,[z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z612,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z229,z6])],[(0,[z7,z1,z3,z613,z4,z5,z6]),(0,[z7,z1,z3,z4,z614,z5,z6]),(0,[z615,z7,z1,z3,z4,z5,z6]),(0,[z88,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z616,z4,z5,z6]),(0,[z7,z1,z213,z4,z5,z187,z6])],[(0,[z617,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z618])]],
   [[(0,[z7,z50,z3,z40,z4,z5,z6]),(0,[z7,z1,z3,z619,z4,z5,z6]),(0,[z7,z620,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z621,z6]),(0,[z7,z1,z3,z4,z622,z5,z6])],[(1,[z7,z140,z3,z4,z5,z6]),(0,[z7,z1,z3,z623,z4,z5,z6]),(0,[z624,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z213,z3,z4,z5,z61]),(0,[z7,z1,z390,z3,z4,z29,z6]),(0,[z268,z7,z1,z3,z4,z5,z6])],[(0,[z7,z66,z50,z3,z4,z5,z6]),(0,[z590,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z625]),(0,[z7,z1,z626,z3,z4,z5,z6]),(0,[z7,z1,z3,z627,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z6,z628]),(0,[z7,z50,z3,z613,z4,z5,z6]),(0,[z7,z257,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z629,z4,z5,z6])],[(0,[z630,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z114,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z631,z6]),(0,[z7,z1,z3,z4,z5,z632,z6]),(0,[z7,z1,z3,z153,z4,z5,z6]),(1,[z7,z1,z3,z4,z287,z6]),(0,[z7,z1,z274,z20,z3,z4,z6])],[(0,[z633,z7,z1,z3,z4,z5,z6]),(0,[z7,z93,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z5,z6]),(0,[z7,z1,z3,z4,z5,z634,z6])],[(0,[z7,z19,z213,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z32,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z635]),(0,[z7,z1,z3,z4,z5,z59,z6])],[(0,[z7,z1,z3,z4,z5,z508,z6])]],
   [[(0,[z7,z1,z2,z3,z4,z29,z6]),(1,[z10,z7,z3,z116,z5,z6])],[(0,[z7,z50,z3,z114,z4,z5,z6]),(0,[z636,z7,z1,z3,z4,z5,z6]),(0,[z55,z7,z19,z3,z4,z5,z6]),(0,[z7,z19,z3,z95,z4,z5,z6]),(0,[z55,z7,z1,z3,z4,z208,z6]),(0,[z7,z1,z3,z4,z5,z6,z637])],[(0,[z7,z27,z3,z114,z4,z5,z6])],[(0,[z294,z7,z1,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z32,z5,z6]),(0,[z7,z50,z3,z4,z5,z59,z6]),(0,[z7,z1,z3,z4,z5,z6,z638]),(0,[z7,z1,z639,z3,z4,z5,z6])],[(0,[z7,z19,z308,z3,z4,z5,z6]),(0,[z88,z7,z307,z3,z4,z5,z6]),(0,[z7,z1,z640,z3,z4,z5,z6]),(0,[z7,z1,z641,z3,z4,z5,z6]),(0,[z7,z642,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z643,z6])],[(0,[z7,z375,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z111,z61]),(0,[z7,z1,z311,z62,z3,z5,z6]),(0,[z7,z1,z311,z3,z105,z4,z6])],[(0,[z55,z7,z50,z3,z4,z5,z6]),(0,[z7,z19,z167,z3,z4,z5,z6]),(0,[z7,z1,z333,z3,z4,z5,z6]),(0,[z644,z7,z1,z3,z4,z5,z6]),(0,[z645,z7,z1,z3,z4,z5,z6]),(0,[z10,z7,z1,z3,z4,z29,z6]),(1,[z7,z1,z3,z4,z168,z6]),(0,[z7,z1,z308,z130,z4,z5,z6]),(0,[z37,z7,z1,z30,z3,z4,z6]),(0,[z7,z1,z263,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z38,z6])],[(0,[z646,z7,z1,z3,z4,z5,z6]),(0,[z139,z7,z19,z3,z4,z5,z6]),(0,[z0,z7,z1,z20,z3,z4,z6]),(0,[z647,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z4,z5,z159]),(0,[z7,z1,z648,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z649,z6]),(0,[z650,z7,z1,z3,z4,z5,z6])]],
   [[(0,[z7,z1,z3,z4,z5,z651,z6]),(0,[z285,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z652,z6]),(0,[z86,z1,z3,z95,z4,z5,z6])],[(0,[z653,z7,z1,z3,z4,z5,z6]),(0,[z42,z7,z66,z3,z4,z5,z6]),(0,[z7,z1,z311,z3,z4,z5,z120])],[(1,[z76,z7,z50,z3,z4,z6]),(0,[z150,z7,z19,z3,z4,z5,z6]),(1,[z55,z1,z3,z133,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z61]),(0,[z7,z1,z90,z3,z4,z29,z6]),(0,[z7,z1,z20,z3,z4,z6,z276])],[(0,[z7,z50,z3,z4,z5,z38,z6]),(0,[z7,z115,z50,z3,z4,z5,z6]),(0,[z7,z19,z152,z3,z4,z5,z6]),(0,[z7,z1,z8,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z654,z5,z6]),(0,[z7,z1,z655,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z656,z6]),(0,[z16,z7,z115,z3,z4,z5,z6])],[(0,[z138,z7,z50,z3,z4,z5,z6]),(0,[z7,z1,z388,z3,z4,z5,z6]),(0,[z7,z1,z657,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z658,z5,z6])],[(0,[z659,z7,z1,z3,z4,z5,z6]),(0,[z7,z341,z50,z3,z4,z5,z6]),(0,[z7,z1,z660,z3,z4,z5,z6]),(0,[z7,z1,z661,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z662,z6]),(0,[z663,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z664]),(0,[z37,z7,z1,z109,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z665,z6]),(0,[z7,z1,z130,z3,z22,z5,z6])],[(0,[z666,z7,z1,z3,z4,z5,z6]),(0,[z150,z7,z50,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z5,z6,z61]),(0,[z158,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z667,z3,z4,z5,z6])]],
   [[(1,[z7,z19,z3,z4,z29,z6]),(0,[z26,z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z20,z130,z3,z4,z6])],[(0,[z7,z1,z3,z239,z4,z5,z6]),(1,[z7,z56,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z572,z6]),(0,[z7,z1,z668,z3,z4,z5,z6]),(0,[z7,z669,z1,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z5,z670,z6]),(0,[z441,z7,z1,z3,z4,z5,z6]),(0,[z7,z671,z1,z3,z4,z5,z6]),(0,[z7,z1,z672,z3,z4,z5,z6]),(0,[z7,z1,z3,z673,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z674])],[(0,[z7,z50,z3,z4,z5,z665,z6]),(0,[z7,z1,z675,z3,z4,z5,z6]),(0,[z16,z7,z19,z3,z4,z5,z6]),(0,[z676,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z677,z6]),(0,[z26,z7,z3,z114,z4,z5,z6]),(0,[z7,z1,z3,z678,z4,z5,z6]),(1,[z7,z1,z308,z152,z5,z6]),(0,[z7,z1,z446,z3,z4,z29,z6]),(0,[z7,z1,z679,z3,z4,z5,z6])],[(0,[z7,z167,z50,z3,z4,z5,z6]),(0,[z0,z7,z333,z3,z4,z5,z6]),(0,[z97,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z680,z5,z6]),(0,[z7,z1,z62,z3,z4,z5,z120])],[(1,[z7,z50,z3,z4,z29,z6]),(0,[z681,z7,z1,z3,z4,z5,z6]),(0,[z26,z7,z1,z114,z4,z5,z6]),(0,[z7,z1,z3,z682,z4,z5,z6]),(0,[z7,z1,z3,z683,z4,z5,z6]),(0,[z7,z1,z684,z3,z4,z5,z6])],[(0,[z192,z7,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z685,z5,z6]),(1,[z7,z1,z3,z4,z96,z6]),(0,[z7,z1,z686,z3,z4,z5,z6]),(0,[z7,z338,z1,z20,z3,z4,z6])],[(0,[z7,z562,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z687,z5,z6]),(0,[z7,z1,z3,z4,z5,z688,z6]),(0,[z689,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z690]),(0,[z7,z1,z20,z288,z3,z4,z6])]],
   [[(0,[z7,z50,z675,z3,z4,z5,z6]),(0,[z16,z7,z50,z3,z4,z5,z6]),(1,[z7,z1,z79,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z691]),(0,[z7,z1,z4,z5,z187,z6,z61])],[(0,[z7,z1,z3,z692,z4,z5,z6]),(0,[z7,z1,z693,z3,z4,z5,z6]),(1,[z7,z1,z311,z3,z5,z276])],[(0,[z694,z7,z1,z3,z4,z5,z6]),(0,[z150,z7,z140,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z695]),(0,[z7,z1,z696,z3,z4,z5,z6]),(0,[z697,z7,z1,z3,z4,z5,z6]),(0,[z698,z7,z1,z3,z4,z5,z6]),(1,[z7,z1,z3,z40,z29,z6]),(1,[z7,z1,z587,z3,z4,z6])],[(0,[z7,z11,z50,z3,z4,z5,z6]),(0,[z7,z335,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z699,z5,z6]),(0,[z80,z7,z1,z3,z4,z29,z6]),(0,[z7,z1,z3,z116,z4,z5,z6])],[(0,[z7,z219,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z6,z700]),(0,[z7,z1,z3,z4,z5,z6,z701]),(0,[z7,z1,z3,z4,z702,z5,z6]),(0,[z7,z1,z3,z4,z5,z703,z6])],[(0,[z158,z7,z335,z3,z4,z5,z6]),(0,[z86,z7,z1,z3,z4,z29,z6]),(0,[z7,z115,z1,z3,z4,z17,z6]),(0,[z37,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z165,z3,z4,z5,z6])],[(0,[z7,z19,z3,z4,z5,z151,z6]),(0,[z7,z1,z20,z3,z24,z4,z6]),(0,[z7,z1,z3,z4,z704,z5,z6]),(0,[z7,z1,z705,z3,z4,z5,z6]),(0,[z7,z1,z706,z3,z4,z5,z6])],[(1,[z7,z1,z3,z4,z5,z6]),(0,[z7,z92,z50,z3,z4,z5,z6]),(0,[z55,z7,z1,z3,z4,z5,z159]),(0,[z236,z7,z1,z3,z4,z5,z6]),(0,[z7,z1,z587,z3,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z50,z60,z4,z5,z61]),(0,[z7,z56,z3,z4,z5,z159]),(0,[z7,z1,z707,z4,z5,z6]),(0,[z7,z1,z3,z578,z29,z6]),(0,[z7,z1,z708,z3,z5,z6])],[(0,[z7,z1,z3,z4,z709,z6]),(0,[z108,z50,z3,z4,z5,z6]),(0,[z7,z710,z3,z4,z5,z6]),(0,[z7,z1,z3,z711,z5,z6]),(0,[z7,z1,z3,z4,z70,z118]),(0,[z712,z7,z3,z4,z5,z6]),(0,[z7,z1,z713,z4,z5,z6])],[(0,[z7,z1,z3,z4,z714,z6]),(0,[z715,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z716,z6]),(0,[z7,z1,z137,z3,z4,z370])],[(0,[z7,z1,z3,z4,z717,z6]),(0,[z55,z56,z3,z133,z5,z6]),(0,[z10,z7,z3,z718,z5,z6]),(0,[z7,z66,z3,z4,z5,z147]),(0,[z7,z1,z130,z22,z29,z6])],[(0,[z7,z1,z20,z79,z4,z6]),(0,[z7,z1,z20,z3,z471,z6]),(0,[z7,z1,z719,z3,z4,z6]),(0,[z7,z720,z20,z3,z4,z6])],[(0,[z7,z19,z3,z105,z4,z6]),(0,[z7,z1,z3,z4,z721,z6]),(0,[z305,z1,z3,z4,z5,z151]),(0,[z42,z7,z3,z4,z5,z691]),(0,[z7,z1,z3,z153,z4,z6]),(0,[z7,z722,z3,z4,z5,z6]),(0,[z7,z1,z109,z263,z4,z6]),(0,[z7,z1,z3,z4,z6,z723]),(0,[z7,z1,z4,z29,z724,z6])],[(0,[z7,z50,z3,z4,z725,z6]),(0,[z7,z92,z307,z3,z4,z6]),(0,[z7,z726,z3,z4,z29,z6])],[(0,[z7,z115,z3,z4,z23,z6]),(0,[z7,z1,z79,z4,z5,z159]),(0,[z7,z1,z20,z3,z358,z6]),(0,[z7,z1,z3,z4,z727,z6]),(0,[z16,z7,z3,z4,z17,z6]),(0,[z7,z1,z3,z4,z728,z6]),(0,[z7,z729,z3,z4,z5,z6])]],
   [[(0,[z730,z7,z50,z3,z4,z6]),(0,[z285,z19,z20,z3,z4,z6]),(0,[z7,z1,z731,z4,z5,z6]),(0,[z7,z732,z3,z4,z5,z6]),(0,[z7,z1,z3,z600,z29,z6]),(0,[z7,z438,z3,z4,z29,z6]),(0,[z7,z1,z3,z319,z29,z6]),(0,[z16,z7,z3,z4,z733,z6])],[(0,[z7,z11,z3,z394,z5,z6]),(0,[z42,z7,z3,z4,z29,z179]),(0,[z7,z1,z308,z734,z5,z6])],[(0,[z138,z7,z3,z4,z5,z372]),(0,[z7,z50,z3,z105,z4,z6]),(0,[z7,z1,z3,z4,z735,z6]),(0,[z55,z1,z79,z133,z5,z6]),(0,[z7,z1,z3,z736,z5,z6]),(0,[z7,z1,z3,z243,z29,z6]),(0,[z7,z1,z3,z4,z5,z737]),(0,[z738,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z739,z6])],[(0,[z7,z740,z3,z4,z5,z6]),(0,[z7,z741,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z742,z6]),(1,[z7,z1,z743,z4,z6]),(0,[z7,z1,z3,z4,z5,z744])],[(0,[z7,z745,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z746,z6])],[(0,[z7,z747,z3,z4,z5,z6]),(0,[z748,z1,z3,z4,z5,z6])],[(0,[z7,z92,z3,z613,z4,z6]),(0,[z7,z50,z749,z3,z4,z6]),(0,[z7,z1,z3,z4,z750,z6]),(0,[z7,z25,z3,z4,z29,z6]),(0,[z751,z1,z3,z4,z5,z6]),(0,[z752,z1,z3,z4,z5,z6]),(0,[z7,z1,z60,z4,z287,z61])],[(0,[z7,z50,z753,z3,z5,z6]),(0,[z7,z189,z3,z4,z5,z6]),(0,[z76,z7,z25,z3,z4,z6]),(0,[z7,z1,z3,z614,z29,z6]),(0,[z7,z1,z8,z4,z5,z159]),(0,[z86,z87,z3,z95,z5,z6]),(0,[z7,z754,z3,z4,z5,z6])]],
   [[(0,[z19,z393,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z755,z6]),(0,[z7,z11,z3,z81,z29,z6])],[(0,[z76,z7,z50,z3,z4,z6]),(0,[z7,z1,z3,z4,z756,z6]),(0,[z7,z56,z79,z4,z5,z6]),(0,[z7,z1,z3,z4,z757,z6]),(0,[z7,z1,z20,z3,z442,z6])],[(0,[z7,z19,z3,z153,z4,z6]),(0,[z7,z1,z3,z4,z758,z6]),(0,[z55,z1,z8,z133,z5,z6])],[(0,[z76,z7,z19,z3,z4,z6]),(0,[z7,z1,z20,z8,z4,z6]),(0,[z42,z7,z3,z4,z5,z759])],[(0,[z50,z3,z678,z4,z5,z6]),(0,[z7,z1,z3,z4,z760,z6])],[(0,[z7,z1,z761,z4,z5,z6]),(0,[z150,z1,z3,z4,z29,z151]),(1,[z7,z762,z4,z5,z6]),(0,[z37,z7,z1,z390,z4,z6]),(0,[z7,z3,z4,z231,z6,z111])],[(0,[z50,z684,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z763,z6])],[(0,[z7,z19,z3,z4,z29,z6]),(0,[z764,z7,z1,z3,z4,z6]),(0,[z7,z1,z3,z4,z765,z6]),(0,[z7,z3,z4,z287,z6,z111])]],
   [[(0,[z50,z20,z288,z3,z4,z6]),(0,[z7,z307,z3,z4,z29,z6]),(0,[z7,z1,z320,z3,z5,z276]),(0,[z7,z1,z3,z4,z5,z766]),(0,[z7,z767,z3,z4,z5,z6]),(0,[z51,z7,z1,z20,z3,z6]),(0,[z7,z1,z3,z4,z5,z768])],[(0,[z7,z50,z3,z4,z769,z6]),(0,[z158,z1,z24,z4,z29,z6]),(0,[z7,z56,z8,z4,z5,z6]),(0,[z7,z1,z3,z4,z770,z6])],[(0,[z19,z50,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z771,z6]),(0,[z7,z99,z3,z4,z29,z6]),(0,[z7,z1,z772,z3,z4,z6])],[(0,[z7,z1,z3,z4,z5,z773]),(0,[z7,z1,z774,z3,z4,z6])],[(0,[z35,z50,z20,z3,z4,z6]),(0,[z7,z333,z20,z3,z4,z6]),(0,[z236,z7,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z775,z6])],[(0,[z7,z335,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z776,z6]),(0,[z7,z1,z777,z4,z29,z6])],[(0,[z16,z7,z25,z3,z4,z6])],[(0,[z365,z50,z3,z4,z5,z6]),(0,[z778,z7,z3,z4,z5,z6]),(0,[z50,z706,z3,z4,z5,z6]),(0,[z650,z50,z3,z4,z5,z6]),(0,[z7,z1,z779,z3,z5,z6]),(0,[z7,z3,z4,z5,z6,z780]),(0,[z7,z1,z3,z4,z5,z781])]],
   [[(0,[z50,z3,z4,z266,z5,z6]),(0,[z7,z19,z3,z4,z70,z6]),(0,[z7,z1,z3,z4,z782,z6]),(0,[z7,z783,z3,z4,z29,z6]),(0,[z7,z1,z90,z3,z4,z784])],[(0,[z7,z1,z3,z785,z5,z6]),(0,[z7,z298,z3,z4,z5,z118]),(0,[z7,z1,z3,z526,z29,z6]),(0,[z7,z3,z40,z103,z29,z6])],[(0,[z7,z19,z3,z786,z5,z6]),(0,[z0,z166,z2,z4,z5,z6]),(0,[z7,z1,z787,z3,z4,z6]),(0,[z7,z1,z3,z788,z5,z6]),(0,[z7,z1,z213,z4,z29,z187]),(0,[z7,z789,z3,z4,z29,z6]),(0,[z7,z790,z3,z4,z5,z6]),(0,[z7,z1,z30,z3,z4,z784])],[(0,[z0,z1,z2,z4,z29,z6]),(0,[z7,z1,z3,z791,z4,z6]),(0,[z7,z1,z792,z3,z4,z6]),(0,[z7,z1,z734,z4,z5,z6]),(0,[z7,z1,z20,z436,z3,z6])],[(0,[z7,z1,z3,z4,z793,z6]),(0,[z7,z794,z3,z4,z5,z6]),(0,[z7,z1,z20,z3,z4,z118]),(0,[z7,z1,z3,z4,z5,z795]),(0,[z7,z1,z308,z152,z153,z6]),(0,[z7,z3,z4,z796,z29,z6])],[(0,[z7,z289,z3,z4,z5,z665]),(0,[z50,z3,z4,z5,z28,z6]),(0,[z7,z1,z3,z302,z29,z6]),(0,[z7,z375,z3,z4,z29,z6]),(0,[z7,z1,z3,z658,z29,z6])],[(0,[z7,z341,z3,z116,z5,z6]),(0,[z7,z1,z3,z4,z797,z6]),(0,[z7,z798,z3,z4,z5,z6]),(1,[z7,z3,z4,z5,z759]),(0,[z7,z3,z4,z5,z6,z799]),(0,[z7,z1,z800,z4,z29,z6])],[(0,[z7,z3,z4,z801,z29,z6]),(0,[z7,z1,z8,z4,z5,z6]),(0,[z7,z140,z3,z4,z29,z6]),(0,[z10,z7,z20,z3,z116,z6]),(0,[z7,z802,z3,z4,z5,z6])]],
   [[(0,[z50,z48,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z231,z6]),(0,[z7,z19,z30,z3,z4,z91]),(0,[z7,z115,z3,z4,z141,z6]),(0,[z7,z671,z1,z20,z3,z6]),(1,[z7,z1,z734,z5,z6])],[(0,[z97,z1,z3,z4,z29,z98]),(0,[z7,z1,z3,z4,z803,z6]),(0,[z7,z11,z3,z81,z141,z6]),(0,[z7,z1,z3,z4,z804,z6])],[(0,[z7,z805,z3,z4,z5,z6])],[(0,[z7,z1,z806,z4,z5,z6]),(0,[z7,z1,z224,z4,z112,z6])],[(0,[z7,z1,z472,z3,z29,z6]),(0,[z7,z807,z3,z4,z5,z6]),(1,[z7,z3,z4,z733,z6]),(0,[z7,z1,z62,z3,z204,z120])],[(0,[z7,z50,z3,z4,z231,z6]),(0,[z7,z50,z30,z3,z4,z91]),(0,[z19,z291,z3,z4,z5,z6]),(0,[z7,z19,z129,z3,z4,z6]),(0,[z7,z808,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z809,z6]),(0,[z7,z1,z810,z3,z5,z6])],[(0,[z50,z3,z4,z74,z5,z6]),(0,[z88,z19,z3,z4,z57,z6]),(0,[z7,z1,z3,z4,z811,z6]),(0,[z7,z1,z3,z4,z812,z6]),(0,[z10,z7,z3,z116,z29,z6]),(0,[z7,z3,z4,z5,z6,z813])],[(0,[z7,z1,z3,z4,z814,z6]),(0,[z7,z19,z3,z815,z5,z6]),(0,[z7,z3,z4,z5,z147,z334]),(0,[z7,z816,z3,z4,z5,z6]),(0,[z7,z817,z3,z4,z5,z6])]],
   [[(0,[z7,z818,z3,z4,z29,z6]),(0,[z7,z19,z3,z4,z141,z6]),(0,[z7,z1,z3,z4,z819,z6]),(0,[z7,z1,z820,z4,z5,z6]),(0,[z7,z821,z3,z4,z5,z6]),(0,[z7,z822,z3,z4,z5,z6]),(0,[z7,z1,z20,z626,z3,z6]),(0,[z7,z1,z234,z58,z4,z6])],[(0,[z42,z7,z3,z4,z5,z163]),(0,[z7,z1,z60,z4,z5,z61]),(0,[z7,z1,z90,z3,z4,z229])],[(0,[z7,z50,z823,z4,z5,z6]),(0,[z7,z50,z129,z3,z4,z6]),(0,[z138,z7,z3,z4,z5,z179]),(0,[z7,z824,z3,z4,z5,z6])],[(0,[z88,z50,z3,z4,z57,z6]),(0,[z7,z298,z3,z4,z5,z6]),(0,[z7,z99,z3,z4,z141,z6])],[(0,[z7,z1,z825,z3,z4,z6]),(0,[z88,z1,z393,z3,z4,z6]),(0,[z7,z438,z20,z3,z4,z6]),(0,[z150,z1,z3,z4,z5,z737]),(0,[z748,z1,z3,z4,z29,z6]),(1,[z7,z1,z3,z4,z784])],[(0,[z7,z1,z3,z4,z29,z159]),(0,[z7,z1,z826,z3,z4,z6]),(0,[z42,z7,z20,z3,z4,z179]),(0,[z7,z1,z3,z4,z5,z827]),(0,[z7,z828,z3,z4,z5,z6]),(0,[z752,z1,z3,z4,z29,z6])],[],[(0,[z7,z1,z3,z4,z5,z829]),(0,[z7,z830,z3,z4,z5,z6]),(1,[z7,z3,z718,z5,z6]),(0,[z7,z3,z4,z831,z5,z6])]],
   [[(0,[z55,z1,z3,z133,z29,z6]),(0,[z7,z115,z104,z3,z4,z6])],[(0,[z7,z254,z3,z81,z5,z6]),(0,[z7,z19,z20,z3,z29,z6]),(0,[z7,z832,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z737,z98]),(0,[z7,z1,z311,z3,z5,z768]),(0,[z7,z1,z3,z4,z5,z784])],[(0,[z764,z7,z50,z3,z4,z6]),(0,[z7,z25,z20,z3,z4,z6]),(0,[z833,z1,z3,z4,z5,z6]),(0,[z7,z834,z3,z4,z5,z6])],[(0,[z76,z7,z3,z4,z17,z6]),(0,[z7,z115,z307,z3,z4,z6]),(0,[z7,z835,z3,z4,z5,z6]),(0,[z836,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z105,z4,z6])],[(0,[z76,z19,z50,z3,z4,z6]),(0,[z7,z1,z837,z3,z4,z6]),(0,[z236,z7,z3,z4,z287,z6]),(0,[z7,z99,z20,z3,z29,z6]),(0,[z7,z338,z233,z3,z4,z6])],[(0,[z7,z1,z3,z4,z838,z6]),(0,[z51,z7,z19,z20,z3,z6]),(0,[z7,z839,z3,z4,z5,z6]),(0,[z7,z1,z308,z413,z5,z6]),(0,[z7,z1,z20,z840,z4,z6]),(0,[z7,z1,z587,z62,z3,z120])],[(0,[z7,z50,z4,z5,z841,z6]),(0,[z7,z50,z20,z3,z29,z6]),(0,[z7,z842,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z843,z6]),(0,[z7,z1,z3,z4,z70,z159]),(0,[z26,z7,z114,z4,z5,z6])],[(0,[z7,z1,z749,z3,z4,z6]),(0,[z1,z3,z731,z4,z5,z6]),(0,[z7,z56,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z844,z6]),(0,[z7,z1,z468,z3,z29,z6])]],
   [[(0,[z7,z11,z92,z3,z4,z6]),(0,[z7,z1,z753,z3,z5,z6]),(0,[z7,z845,z3,z4,z5,z6])],[(0,[z285,z846,z3,z4,z5,z6]),(0,[z7,z1,z569,z3,z29,z6]),(0,[z55,z1,z3,z133,z70,z6]),(0,[z7,z1,z3,z4,z5,z847]),(0,[z7,z1,z3,z4,z848,z6]),(0,[z150,z1,z20,z3,z4,z151]),(0,[z7,z1,z3,z400,z29,z6]),(0,[z7,z1,z308,z152,z29,z6]),(0,[z7,z1,z165,z3,z4,z83]),(0,[z344,z7,z1,z3,z4,z229])],[(0,[z76,z192,z50,z3,z4,z6]),(0,[z7,z19,z3,z4,z204,z6]),(0,[z7,z3,z4,z849,z96,z6]),(0,[z7,z1,z3,z4,z850,z6]),(0,[z7,z1,z165,z3,z4,z38]),(0,[z7,z1,z3,z4,z38,z784])],[(0,[z7,z19,z20,z3,z4,z6]),(0,[z192,z50,z20,z3,z4,z6]),(0,[z7,z19,z92,z3,z4,z6]),(0,[z7,z511,z675,z4,z5,z6]),(0,[z7,z50,z3,z4,z851,z6]),(0,[z7,z1,z20,z3,z536,z6]),(0,[z7,z1,z743,z4,z5,z6])],[(1,[z846,z3,z4,z5,z6]),(0,[z7,z1,z3,z852,z4,z6])],[(0,[z7,z201,z3,z4,z5,z6]),(0,[z7,z50,z336,z3,z4,z6]),(0,[z7,z853,z3,z4,z5,z6]),(0,[z7,z854,z3,z4,z29,z6]),(0,[z7,z1,z3,z29,z49,z6]),(0,[z252,z1,z288,z3,z4,z6])],[(0,[z19,z50,z20,z3,z4,z6]),(0,[z7,z50,z3,z855,z4,z6]),(0,[z856,z7,z50,z3,z4,z6]),(0,[z7,z1,z79,z4,z29,z6]),(0,[z7,z1,z857,z3,z5,z6]),(0,[z7,z858,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z204,z6]),(0,[z7,z27,z762,z4,z5,z6]),(0,[z7,z3,z4,z859,z29,z6]),(0,[z7,z1,z311,z3,z29,z276])]],
   [[(0,[z7,z50,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z860,z6]),(0,[z7,z56,z3,z4,z70,z6]),(0,[z7,z861,z3,z4,z5,z6]),(0,[z80,z201,z3,z4,z32,z6]),(0,[z7,z3,z4,z29,z775,z6]),(0,[z7,z862,z3,z4,z5,z6])],[(0,[z50,z3,z177,z4,z5,z6]),(0,[z7,z167,z762,z4,z5,z6]),(0,[z7,z3,z4,z733,z5,z6]),(0,[z7,z1,z3,z384,z29,z6]),(0,[z1,z3,z4,z5,z6,z863])],[(0,[z7,z1,z3,z4,z5,z864]),(0,[z7,z1,z3,z4,z769,z6]),(0,[z7,z1,z3,z4,z5,z865]),(0,[z7,z1,z866,z3,z4,z5]),(0,[z7,z1,z3,z4,z867,z6]),(0,[z7,z3,z4,z733,z59,z6]),(0,[z7,z1,z117,z4,z112,z6])],[(0,[z7,z257,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z868,z6]),(0,[z1,z3,z4,z869,z5,z6]),(0,[z7,z3,z4,z849,z5,z6]),(0,[z870,z1,z3,z4,z5,z6])],[(0,[z7,z166,z3,z4,z5,z6]),(0,[z386,z50,z3,z4,z5,z6]),(0,[z7,z871,z3,z4,z29,z6])],[(0,[z7,z1,z3,z4,z29,z6])],[(0,[z7,z1,z8,z4,z29,z6])],[(0,[z7,z1,z79,z4,z70,z6]),(0,[z7,z1,z3,z4,z872,z6]),(0,[z873,z7,z87,z3,z4,z6]),(0,[z7,z1,z874,z3,z4,z6])]],
   [[(0,[z462,z50,z3,z4,z5,z6]),(0,[z7,z875,z3,z4,z5,z6]),(0,[z7,z1,z857,z3,z40,z6])],[(0,[z7,z511,z27,z4,z5,z6]),(0,[z7,z19,z3,z4,z876,z6]),(0,[z873,z7,z1,z3,z4,z6]),(0,[z7,z375,z20,z3,z4,z6])],[(0,[z7,z1,z877,z3,z4,z6]),(0,[z7,z19,z3,z4,z342,z6]),(0,[z88,z1,z288,z3,z4,z6]),(0,[z7,z1,z20,z3,z519,z6])],[(0,[z7,z878,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z879,z6]),(0,[z158,z335,z24,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z880]),(0,[z7,z881,z3,z4,z5,z6]),(0,[z1,z3,z95,z869,z5,z6]),(0,[z7,z1,z882,z3,z4,z6]),(0,[z7,z140,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z883])],[(0,[z7,z884,z3,z4,z5,z6]),(0,[z7,z219,z258,z4,z5,z6]),(0,[z7,z1,z885,z4,z5,z6]),(0,[z7,z886,z3,z4,z5,z6]),(0,[z7,z1,z196,z3,z5,z120]),(0,[z7,z1,z3,z4,z887,z6]),(0,[z7,z1,z20,z397,z3,z6])],[(0,[z180,z50,z3,z4,z5,z6]),(0,[z7,z1,z888,z3,z4,z6]),(0,[z7,z889,z3,z4,z5,z6]),(0,[z97,z1,z20,z3,z4,z98]),(0,[z7,z1,z734,z22,z5,z6]),(0,[z7,z1,z3,z890,z4,z6]),(0,[z7,z1,z891,z3,z4,z29])],[(1,[z7,z818,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z892]),(0,[z7,z1,z3,z4,z70,z6]),(0,[z7,z1,z30,z3,z4,z690]),(0,[z197,z7,z1,z263,z4,z6])],[(0,[z7,z50,z3,z4,z342,z6]),(0,[z7,z1,z8,z4,z70,z6]),(0,[z7,z1,z3,z4,z5,z893]),(0,[z26,z7,z682,z4,z5,z6]),(0,[z7,z894,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z784,z91]),(0,[z7,z895,z3,z4,z5,z6])]],
   [[(0,[z483,z50,z3,z4,z5,z6]),(0,[z590,z7,z273,z4,z5,z6]),(0,[z7,z1,z3,z786,z5,z6]),(0,[z7,z1,z3,z4,z208,z118]),(0,[z7,z896,z3,z4,z5,z6])],[(0,[z7,z897,z3,z4,z5,z6])],[(0,[z50,z3,z4,z5,z6,z242]),(0,[z7,z20,z3,z4,z6,z111])],[(0,[z7,z898,z3,z4,z5,z6]),(0,[z7,z899,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z900,z6])],[(0,[z7,z50,z901,z3,z4,z6]),(0,[z902,z7,z3,z4,z5,z6]),(0,[z0,z333,z2,z4,z5,z6]),(0,[z7,z209,z3,z4,z29,z6]),(0,[z903,z1,z20,z3,z4,z6])],[(0,[z7,z50,z3,z4,z5,z118]),(0,[z7,z50,z90,z3,z4,z38]),(0,[z7,z1,z3,z4,z5,z904]),(0,[z97,z1,z3,z4,z5,z737]),(0,[z7,z1,z3,z250,z29,z6])],[(0,[z494,z50,z3,z4,z5,z6]),(0,[z905,z7,z1,z3,z4,z6]),(0,[z7,z298,z3,z4,z5,z159]),(0,[z7,z1,z130,z22,z424,z6]),(0,[z7,z1,z3,z4,z231,z6]),(1,[z7,z1,z4,z5,z744]),(0,[z7,z3,z4,z831,z29,z6]),(0,[z7,z1,z30,z3,z4,z91])],[(0,[z86,z50,z3,z95,z5,z6]),(0,[z7,z341,z3,z613,z5,z6])]],
   [[(0,[z7,z19,z3,z155,z29,z6]),(0,[z7,z906,z3,z4,z5,z6]),(0,[z7,z1,z907,z4,z5,z6]),(0,[z7,z908,z3,z4,z5,z6])],[(0,[z7,z19,z388,z3,z4,z6]),(0,[z7,z19,z62,z3,z5,z120]),(0,[z7,z909,z3,z4,z5,z6]),(0,[z55,z298,z3,z133,z5,z6]),(0,[z7,z1,z20,z3,z4,z159]),(0,[z7,z1,z910,z3,z4,z5]),(0,[z7,z1,z20,z581,z3,z6])],[(0,[z7,z87,z3,z4,z5,z6]),(0,[z911,z1,z3,z4,z5,z6]),(0,[z912,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z103,z29,z6])],[(0,[z7,z1,z823,z4,z5,z6]),(0,[z7,z1,z3,z913,z4,z6]),(0,[z7,z1,z3,z4,z914,z6]),(0,[z7,z1,z129,z3,z4,z6]),(0,[z7,z1,z3,z437,z29,z6])],[(0,[z158,z1,z731,z4,z5,z6]),(0,[z88,z1,z3,z4,z57,z6])],[(0,[z192,z92,z50,z3,z4,z6]),(0,[z7,z1,z3,z815,z5,z6]),(0,[z417,z19,z3,z4,z5,z6]),(0,[z26,z7,z114,z4,z29,z6]),(0,[z7,z1,z352,z3,z29,z6])],[(0,[z7,z50,z388,z3,z4,z6]),(0,[z7,z50,z3,z4,z915,z6]),(0,[z7,z50,z62,z3,z5,z120]),(0,[z422,z19,z3,z4,z5,z6]),(0,[z7,z916,z3,z4,z5,z6]),(0,[z7,z1,z320,z3,z29,z6]),(0,[z917,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z141,z6]),(0,[z7,z1,z918,z4,z5,z6]),(0,[z7,z919,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z920,z6]),(0,[z10,z7,z336,z3,z116,z6]),(0,[z1,z3,z4,z921,z5,z6]),(0,[z7,z1,z30,z3,z4,z370])]],
   [[(0,[z7,z50,z130,z22,z5,z6]),(0,[z86,z375,z3,z95,z5,z6]),(0,[z389,z7,z1,z20,z3,z6]),(0,[z7,z922,z3,z4,z5,z6]),(0,[z7,z1,z734,z130,z5,z6])],[(0,[z7,z3,z4,z923,z29,z6]),(0,[z7,z1,z924,z4,z5,z6]),(0,[z7,z3,z762,z4,z5,z6]),(0,[z7,z1,z925,z3,z4,z6]),(0,[z7,z926,z3,z4,z5,z6])],[(0,[z7,z92,z50,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z927]),(0,[z7,z66,z3,z4,z5,z508]),(0,[z12,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z928,z5,z6]),(0,[z929,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z673,z29,z6]),(0,[z7,z930,z3,z4,z5,z6]),(0,[z236,z7,z60,z4,z5,z61])],[(0,[z7,z50,z931,z4,z5,z6]),(0,[z7,z50,z932,z3,z4,z5]),(0,[z7,z56,z20,z3,z4,z6]),(0,[z7,z1,z762,z4,z5,z6]),(0,[z933,z1,z3,z4,z5,z6]),(0,[z7,z27,z4,z5,z6,z664]),(0,[z7,z1,z3,z4,z934,z6]),(0,[z7,z66,z3,z4,z5,z759]),(0,[z7,z1,z935,z3,z4,z6])],[(0,[z50,z288,z3,z4,z5,z6]),(0,[z0,z1,z731,z4,z5,z6]),(0,[z7,z1,z936,z3,z4,z6])],[(0,[z1,z3,z4,z5,z6,z737]),(0,[z7,z1,z937,z3,z4,z6]),(0,[z7,z115,z3,z4,z103,z6]),(0,[z7,z66,z3,z4,z29,z147]),(0,[z7,z1,z938,z3,z4,z6]),(0,[z7,z1,z857,z3,z29,z6]),(0,[z268,z1,z3,z4,z326,z6])],[(0,[z7,z1,z3,z4,z939,z6]),(0,[z7,z1,z3,z4,z940,z6]),(0,[z7,z941,z3,z4,z5,z6]),(0,[z7,z720,z3,z4,z5,z6]),(0,[z86,z1,z20,z3,z95,z6]),(0,[z80,z1,z3,z4,z942,z6]),(0,[z7,z232,z20,z3,z4,z6])],[(0,[z7,z1,z4,z5,z841,z6]),(0,[z7,z562,z3,z4,z23,z6]),(0,[z7,z298,z79,z4,z5,z6]),(1,[z1,z3,z4,z942,z6]),(0,[z7,z1,z3,z943,z5,z6]),(0,[z7,z1,z944,z3,z4,z6]),(0,[z7,z1,z20,z3,z29,z6])]],
   [[(0,[z663,z50,z3,z4,z5,z6]),(0,[z7,z945,z3,z4,z5,z6]),(0,[z7,z1,z946,z4,z5,z6]),(0,[z947,z7,z1,z3,z4,z6]),(0,[z7,z1,z4,z5,z948,z6]),(0,[z7,z949,z3,z4,z5,z6]),(0,[z7,z1,z62,z3,z5,z768])],[(0,[z7,z1,z950,z3,z4,z6]),(0,[z7,z1,z951,z4,z5,z6]),(0,[z7,z952,z3,z4,z5,z6]),(0,[z7,z1,z20,z857,z3,z6])],[(0,[z285,z19,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z953,z6]),(0,[z7,z19,z3,z4,z424,z6]),(0,[z0,z1,z20,z2,z4,z6]),(0,[z88,z307,z3,z4,z57,z6]),(0,[z7,z1,z891,z3,z4,z5]),(0,[z35,z1,z274,z3,z4,z6])],[(0,[z7,z166,z3,z4,z29,z6]),(0,[z7,z1,z954,z4,z5,z6])],[(0,[z7,z1,z3,z4,z851,z6]),(0,[z7,z3,z116,z519,z5,z6]),(0,[z7,z1,z955,z3,z4,z6]),(0,[z7,z1,z3,z4,z956,z6])],[(0,[z7,z1,z3,z4,z957,z6]),(0,[z37,z7,z1,z109,z4,z6])],[(0,[z268,z1,z3,z4,z57,z6])],[(0,[z192,z846,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z424,z6]),(0,[z7,z1,z3,z855,z4,z6]),(0,[z7,z1,z3,z4,z5,z958]),(0,[z7,z19,z3,z4,z208,z6]),(0,[z7,z298,z8,z4,z5,z6]),(0,[z7,z1,z959,z4,z5,z6]),(0,[z7,z1,z20,z3,z609,z6]),(0,[z7,z1,z857,z3,z4,z6])]],
   [[(0,[z7,z960,z3,z4,z5,z6]),(0,[z7,z961,z3,z4,z5,z6]),(0,[z7,z1,z213,z4,z5,z744]),(0,[z7,z1,z3,z4,z204,z6])],[(0,[z7,z1,z20,z3,z4,z6]),(0,[z7,z1,z92,z3,z4,z6]),(0,[z158,z19,z24,z4,z5,z6]),(0,[z7,z93,z3,z4,z5,z508]),(0,[z7,z189,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z6,z962]),(0,[z963,z1,z20,z3,z4,z6])],[(0,[z150,z50,z3,z4,z5,z151]),(0,[z7,z1,z3,z4,z725,z6]),(0,[z7,z964,z1,z3,z4,z6]),(0,[z19,z846,z3,z4,z5,z6]),(0,[z97,z438,z3,z4,z5,z98]),(0,[z37,z7,z1,z743,z4,z6]),(0,[z7,z1,z4,z5,z6,z744])],[(0,[z1,z3,z4,z32,z942,z6]),(0,[z7,z338,z3,z4,z17,z6])],[(0,[z7,z846,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z208,z6]),(0,[z1,z3,z4,z5,z151,z737]),(0,[z7,z1,z308,z152,z342,z6])],[(0,[z7,z818,z50,z3,z4,z6]),(0,[z80,z620,z1,z3,z4,z6]),(0,[z7,z1,z3,z965,z4,z6])],[(0,[z158,z50,z24,z4,z5,z6]),(0,[z51,z7,z50,z20,z3,z6]),(0,[z169,z50,z3,z4,z5,z6]),(0,[z7,z1,z966,z4,z5,z6])],[(0,[z1,z731,z24,z4,z5,z6]),(0,[z7,z1,z3,z4,z967,z6]),(0,[z7,z968,z3,z4,z5,z6]),(0,[z7,z969,z3,z4,z5,z6])]],
   [[(0,[z1,z3,z4,z942,z57,z6]),(0,[z970,z1,z3,z4,z5,z6])],[(0,[z905,z7,z50,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z971]),(0,[z7,z972,z3,z4,z5,z6])],[(0,[z7,z50,z973,z3,z5,z6]),(0,[z7,z19,z3,z4,z348,z6]),(0,[z7,z1,z974,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z975]),(0,[z7,z1,z3,z4,z976,z6])],[(0,[z0,z19,z2,z4,z5,z6]),(0,[z499,z19,z3,z4,z5,z6]),(0,[z7,z19,z336,z3,z4,z6])],[(0,[z7,z1,z3,z4,z5,z977]),(0,[z7,z3,z4,z978,z5,z6]),(0,[z7,z1,z3,z4,z979,z6]),(0,[z47,z7,z1,z390,z4,z6])],[(0,[z7,z1,z980,z4,z5,z6]),(0,[z7,z1,z981,z4,z5,z6]),(0,[z7,z1,z982,z3,z4,z6]),(0,[z7,z983,z3,z4,z5,z6]),(0,[z7,z984,z3,z4,z5,z6]),(0,[z7,z985,z3,z4,z5,z6])],[(0,[z35,z50,z3,z4,z5,z6]),(0,[z7,z333,z3,z4,z5,z6]),(0,[z236,z7,z3,z4,z29,z6])],[(0,[z7,z335,z3,z4,z5,z6]),(0,[z7,z50,z213,z4,z5,z187]),(0,[z7,z50,z3,z4,z348,z6]),(0,[z7,z1,z3,z4,z876,z6]),(0,[z7,z1,z986,z3,z4,z6]),(0,[z86,z1,z3,z95,z96,z6]),(0,[z7,z307,z20,z3,z4,z6]),(0,[z7,z115,z3,z4,z733,z6]),(0,[z7,z1,z910,z3,z4,z29]),(0,[z51,z7,z1,z857,z3,z6])]],
   [[(0,[z0,z50,z2,z4,z5,z6]),(0,[z593,z19,z3,z4,z5,z6]),(0,[z7,z209,z20,z3,z4,z6]),(0,[z7,z1,z3,z4,z342,z6]),(0,[z7,z1,z4,z5,z744,z61]),(0,[z7,z3,z4,z5,z6,z987])],[(0,[z97,z19,z3,z4,z5,z98]),(0,[z7,z87,z3,z4,z29,z6]),(0,[z7,z99,z20,z3,z4,z6])],[(0,[z7,z1,z3,z4,z988,z6]),(0,[z7,z1,z446,z3,z4,z75])],[(0,[z369,z50,z3,z4,z5,z6]),(0,[z7,z1,z989,z3,z5,z6])],[(0,[z50,z377,z3,z4,z5,z6]),(0,[z7,z115,z3,z4,z168,z6])],[(0,[z50,z3,z4,z378,z5,z6]),(0,[z7,z1,z901,z3,z4,z6]),(0,[z382,z19,z3,z4,z5,z6]),(0,[z1,z3,z869,z133,z5,z6]),(0,[z7,z990,z3,z4,z5,z6]),(0,[z7,z919,z3,z4,z29,z6])],[(0,[z97,z50,z3,z4,z5,z98]),(0,[z16,z7,z3,z4,z310,z6]),(0,[z7,z1,z3,z4,z5,z118]),(0,[z7,z991,z3,z4,z5,z6]),(0,[z1,z3,z4,z921,z29,z6]),(0,[z7,z1,z90,z3,z4,z38])],[(0,[z7,z50,z3,z4,z287,z6]),(0,[z7,z19,z992,z4,z5,z6]),(0,[z7,z1,z993,z4,z5,z6]),(0,[z7,z1,z129,z130,z22,z6]),(0,[z7,z994,z3,z4,z5,z6])]],
   [[(0,[z7,z254,z92,z3,z4,z6]),(0,[z86,z1,z3,z95,z5,z6]),(0,[z7,z1,z3,z4,z995,z6])],[(0,[z7,z1,z3,z996,z4,z6])],[(0,[z7,z254,z3,z367,z5,z6]),(0,[z85,z7,z114,z4,z5,z6]),(0,[z127,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z997,z5,z6])],[(0,[z7,z19,z3,z4,z5,z998]),(0,[z7,z999,z3,z4,z5,z6]),(0,[z7,z1,z3,z1000,z5,z6])],[(0,[z7,z19,z3,z4,z168,z6])],[(0,[z7,z1,z3,z4,z208,z159]),(0,[z7,z1,z20,z62,z3,z120])],[(0,[z7,z1,z3,z155,z29,z6]),(0,[z7,z1,z20,z3,z394,z6]),(0,[z7,z1,z391,z3,z29,z6]),(0,[z7,z1001,z3,z4,z5,z6]),(0,[z7,z1,z4,z5,z724,z6])],[(0,[z351,z50,z3,z4,z5,z6]),(0,[z7,z945,z3,z4,z29,z6]),(0,[z7,z1002,z3,z4,z5,z6]),(0,[z7,z1,z388,z3,z4,z6]),(0,[z7,z1,z3,z4,z1003,z6]),(0,[z7,z11,z3,z718,z5,z6]),(0,[z236,z7,z3,z4,z231,z6]),(0,[z7,z1,z62,z3,z5,z120])]],
   [[(0,[z7,z50,z1004,z3,z4,z5]),(0,[z55,z1,z3,z133,z208,z6]),(0,[z7,z11,z20,z3,z81,z6]),(0,[z7,z1005,z3,z4,z5,z6]),(0,[z7,z1006,z3,z4,z5,z6])],[(0,[z7,z50,z1007,z3,z4,z5]),(0,[z7,z50,z3,z4,z168,z6]),(0,[z285,z19,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z1008,z6]),(0,[z7,z66,z20,z3,z4,z147]),(0,[z7,z1,z3,z4,z1009,z6])],[(0,[z7,z50,z3,z4,z5,z159]),(0,[z7,z50,z3,z4,z6,z1010]),(0,[z7,z1,z661,z3,z29,z6]),(0,[z7,z1,z734,z3,z5,z6]),(0,[z7,z821,z3,z4,z29,z6])],[(0,[z7,z19,z3,z4,z5,z118]),(0,[z7,z19,z90,z3,z4,z38]),(0,[z7,z1,z1011,z4,z5,z6]),(0,[z7,z1012,z3,z4,z5,z6]),(0,[z7,z1,z60,z4,z29,z61])],[(0,[z7,z1,z931,z4,z5,z6]),(0,[z7,z1,z932,z3,z4,z5]),(0,[z7,z1,z1013,z3,z4,z29]),(0,[z7,z824,z3,z4,z29,z6])],[(0,[z55,z50,z3,z133,z5,z6]),(0,[z7,z50,z1014,z4,z5,z6]),(0,[z7,z92,z3,z4,z577,z6]),(0,[z7,z964,z50,z3,z4,z6]),(0,[z86,z19,z3,z95,z5,z6]),(0,[z7,z298,z3,z4,z29,z6]),(0,[z7,z115,z25,z3,z4,z6]),(0,[z7,z3,z4,z29,z6,z813])],[(0,[z7,z438,z3,z4,z5,z6]),(0,[z597,z50,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1015]),(0,[z7,z762,z114,z4,z5,z6]),(0,[z1016,z1,z3,z4,z5,z6]),(0,[z7,z3,z4,z17,z733,z6]),(0,[z7,z1017,z3,z4,z5,z6])],[(0,[z19,z558,z3,z4,z5,z6]),(0,[z7,z56,z3,z4,z208,z6]),(0,[z42,z7,z3,z4,z5,z179]),(0,[z7,z1,z60,z20,z4,z61])]],
   [[(0,[z26,z7,z273,z4,z5,z6]),(0,[z7,z1,z3,z4,z1018,z6]),(0,[z88,z1,z3,z4,z942,z6])],[(0,[z19,z561,z3,z4,z5,z6]),(0,[z7,z19,z308,z152,z5,z6]),(0,[z7,z1,z1019,z4,z5,z6]),(0,[z7,z1,z3,z363,z29,z6]),(0,[z7,z1,z20,z3,z449,z6]),(0,[z7,z1020,z3,z4,z5,z6])],[(0,[z553,z19,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z953,z6]),(0,[z7,z3,z4,z17,z168,z6]),(0,[z7,z1021,z3,z4,z5,z6])],[(0,[z7,z25,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z96,z6]),(0,[z7,z1,z3,z4,z1022,z6]),(0,[z1023,z7,z3,z4,z5,z6]),(0,[z7,z11,z3,z81,z186,z6]),(0,[z251,z7,z99,z3,z4,z6]),(0,[z7,z1,z3,z5,z768,z276])],[(0,[z7,z189,z20,z3,z4,z6]),(0,[z7,z1,z1024,z3,z4,z6]),(0,[z7,z1,z20,z130,z22,z6]),(0,[z7,z1025,z3,z4,z5,z6])],[(0,[z7,z50,z308,z152,z5,z6]),(0,[z7,z19,z130,z22,z5,z6]),(0,[z7,z298,z3,z4,z70,z6]),(0,[z7,z1,z79,z4,z208,z6]),(0,[z7,z1026,z3,z4,z5,z6]),(0,[z7,z1,z3,z1027,z4,z6]),(0,[z7,z11,z3,z81,z5,z6]),(0,[z7,z115,z3,z4,z59,z6]),(0,[z7,z3,z4,z5,z6,z759]),(0,[z7,z1,z224,z4,z264,z6])],[(0,[z85,z7,z239,z4,z5,z6]),(0,[z7,z19,z311,z3,z5,z276]),(0,[z7,z1,z3,z4,z942,z6]),(0,[z80,z25,z3,z4,z32,z6]),(0,[z7,z1,z3,z4,z1028,z6]),(0,[z7,z1,z3,z1029,z5,z6])]],
   [[(0,[z7,z19,z3,z40,z29,z6]),(0,[z7,z19,z587,z3,z4,z6]),(0,[z7,z1,z3,z4,z424,z6]),(0,[z7,z1,z3,z29,z6,z374])],[(0,[z7,z50,z3,z4,z96,z6]),(0,[z7,z1,z3,z1030,z5,z6])],[(0,[z7,z19,z1031,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z1032]),(0,[z158,z1,z20,z24,z4,z6]),(0,[z7,z1,z3,z4,z1033,z6]),(0,[z7,z1034,z3,z4,z5,z6])],[(0,[z19,z92,z50,z3,z4,z6]),(0,[z7,z50,z79,z4,z5,z6]),(0,[z259,z7,z3,z4,z5,z163]),(0,[z7,z19,z3,z4,z186,z6]),(0,[z10,z7,z3,z116,z168,z6])],[(0,[z7,z50,z1035,z3,z4,z6]),(0,[z50,z3,z4,z454,z5,z6]),(0,[z7,z50,z311,z3,z5,z276]),(0,[z7,z1,z3,z4,z1036,z6]),(0,[z7,z1,z60,z4,z231,z61]),(0,[z7,z1,z117,z4,z246,z6])],[(0,[z7,z19,z3,z4,z5,z6]),(0,[z192,z50,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z1037,z6]),(0,[z7,z50,z3,z40,z29,z6]),(0,[z7,z50,z587,z3,z4,z6]),(0,[z7,z333,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z208,z6])],[(0,[z7,z50,z3,z5,z1038,z6]),(0,[z7,z335,z3,z4,z29,z6]),(0,[z7,z1,z8,z4,z208,z6]),(0,[z7,z167,z27,z4,z5,z6]),(0,[z7,z1,z3,z4,z1039,z6]),(0,[z7,z1,z20,z3,z4,z766])],[(0,[z50,z3,z4,z5,z6,z603]),(0,[z158,z1,z24,z4,z5,z6]),(0,[z7,z201,z3,z4,z29,z6]),(0,[z7,z1,z3,z4,z5,z1040]),(0,[z7,z1041,z3,z4,z5,z6])]],
   [[(0,[z19,z50,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z186,z6]),(0,[z7,z1,z3,z1042,z5,z6]),(0,[z7,z1,z3,z4,z5,z1043])],[(0,[z7,z1,z3,z5,z1044,z6]),(0,[z7,z99,z3,z4,z59,z6]),(0,[z1,z3,z4,z5,z6,z1045])],[(0,[z7,z50,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z759,z179]),(0,[z236,z7,z20,z3,z4,z6]),(0,[z7,z1,z311,z3,z348,z276])],[(0,[z7,z1,z973,z3,z5,z6]),(0,[z7,z3,z4,z5,z6,z1046]),(0,[z7,z1,z777,z4,z5,z6]),(0,[z7,z1047,z3,z4,z5,z6])],[(0,[z7,z50,z1048,z3,z4,z5]),(0,[z7,z92,z3,z4,z59,z6]),(0,[z7,z1049,z3,z4,z5,z6]),(0,[z97,z232,z3,z4,z5,z98]),(0,[z7,z167,z20,z27,z4,z6]),(0,[z7,z1,z3,z5,z6,z768])],[(0,[z846,z50,z3,z4,z5,z6]),(0,[z80,z50,z3,z4,z32,z6]),(0,[z440,z19,z3,z4,z5,z6]),(0,[z7,z1,z3,z1050,z4,z6]),(0,[z7,z257,z3,z4,z29,z6]),(0,[z1,z3,z4,z942,z5,z6]),(0,[z7,z1,z20,z311,z3,z276])],[(0,[z80,z7,z99,z3,z4,z6]),(0,[z7,z3,z4,z5,z6,z111]),(0,[z7,z783,z3,z4,z5,z6])],[(0,[z7,z19,z3,z4,z5,z1032]),(0,[z1,z2,z731,z4,z5,z6])]],
   [[(0,[z150,z19,z3,z4,z5,z151]),(0,[z7,z1,z213,z4,z5,z187]),(0,[z7,z1,z3,z4,z348,z6]),(0,[z7,z790,z20,z3,z4,z6]),(0,[z441,z7,z104,z3,z4,z6])],[(0,[z7,z19,z1051,z4,z5,z6]),(0,[z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z1013,z3,z4,z5]),(0,[z7,z1,z336,z3,z4,z6]),(0,[z7,z1052,z3,z4,z5,z6])],[(0,[z63,z19,z3,z4,z5,z6]),(0,[z7,z825,z87,z3,z4,z6]),(0,[z150,z209,z3,z4,z5,z151]),(0,[z7,z1,z1053,z3,z4,z5]),(0,[z37,z7,z1,z4,z6,z227]),(0,[z7,z3,z4,z796,z5,z6])],[(0,[z7,z375,z3,z4,z5,z6]),(0,[z139,z7,z3,z4,z310,z6]),(0,[z7,z1,z1054,z3,z4,z6]),(0,[z7,z1,z3,z4,z1055,z6]),(0,[z7,z99,z3,z4,z103,z6])],[(0,[z16,z7,z92,z3,z4,z6]),(0,[z7,z1,z3,z4,z5,z1056]),(0,[z55,z1,z3,z133,z5,z118]),(0,[z7,z1,z800,z4,z5,z6]),(0,[z16,z7,z307,z3,z4,z6])],[(0,[z7,z3,z4,z801,z5,z6]),(0,[z7,z140,z3,z4,z5,z6])],[(0,[z7,z1,z1057,z3,z4,z6]),(0,[z620,z19,z3,z4,z5,z6]),(0,[z7,z1058,z3,z4,z5,z6]),(0,[z7,z1,z1059,z3,z4,z6]),(0,[z7,z1,z62,z3,z29,z120])],[(0,[z7,z1,z1060,z4,z5,z6]),(0,[z97,z1,z3,z4,z5,z98]),(0,[z7,z1,z3,z4,z5,z759])]],
   [[(0,[z7,z1061,z3,z4,z5,z6]),(0,[z7,z1,z366,z3,z29,z6]),(0,[z7,z1,z3,z4,z287,z6])],[(0,[z7,z1,z3,z683,z29,z6])],[],[(0,[z7,z56,z3,z4,z5,z118]),(0,[z1062,z7,z3,z4,z5,z6])],[(0,[z10,z7,z3,z116,z5,z6])],[(0,[z492,z50,z3,z4,z5,z6]),(0,[z7,z19,z213,z4,z5,z187]),(0,[z7,z1,z992,z4,z5,z6]),(0,[z7,z1063,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z1064,z6]),(0,[z7,z1,z3,z4,z733,z6]),(0,[z7,z60,z4,z5,z111,z61]),(0,[z7,z1,z3,z4,z1065,z6]),(0,[z7,z817,z20,z3,z4,z6])],[(0,[z7,z818,z3,z4,z5,z6]),(1,[z1,z3,z869,z5,z6]),(0,[z903,z1,z3,z4,z5,z6]),(0,[z7,z1,z3,z459,z29,z6])],[(0,[z7,z1066,z3,z4,z5,z6]),(0,[z462,z1,z3,z4,z5,z98]),(0,[z7,z1,z1067,z4,z5,z6])]],
   [[(0,[z150,z140,z3,z4,z5,z151]),(0,[z7,z1,z3,z4,z1068,z6]),(0,[z7,z1,z4,z5,z187,z744]),(0,[z7,z1,z3,z340,z29,z6])],[(0,[z7,z1,z1004,z3,z4,z5]),(0,[z7,z1,z3,z4,z5,z998]),(0,[z7,z298,z20,z3,z4,z6]),(0,[z7,z1069,z3,z4,z5,z6]),(0,[z7,z1070,z3,z4,z5,z6]),(0,[z7,z1,z20,z713,z4,z6]),(0,[z7,z1,z3,z4,z6,z784])],[(0,[z7,z50,z3,z4,z1071,z6]),(0,[z7,z1,z1007,z3,z4,z5]),(0,[z7,z1,z79,z4,z5,z118]),(0,[z7,z1,z3,z4,z168,z6]),(0,[z7,z908,z3,z4,z29,z6]),(0,[z7,z1072,z3,z4,z5,z6])],[(0,[z7,z1,z3,z4,z6,z1010]),(0,[z7,z1,z3,z4,z5,z159]),(0,[z7,z1073,z3,z4,z5,z6]),(0,[z7,z3,z116,z718,z5,z6]),(0,[z251,z1,z3,z4,z218,z6]),(0,[z7,z1,z20,z3,z4,z827])],[(0,[z88,z257,z3,z4,z57,z6]),(0,[z7,z1074,z3,z4,z5,z6])],[(0,[z7,z50,z1075,z3,z4,z6]),(0,[z7,z19,z3,z4,z287,z6]),(0,[z7,z1026,z3,z4,z29,z6])],[(0,[z7,z1,z1014,z4,z5,z6]),(0,[z7,z1076,z3,z4,z5,z6]),(0,[z55,z1,z3,z133,z5,z6]),(0,[z7,z1,z1077,z4,z5,z6]),(0,[z7,z1,z3,z368,z29,z6])],[(0,[z7,z1,z3,z4,z5,z1078]),(0,[z86,z1,z388,z3,z95,z6]),(0,[z7,z20,z3,z103,z29,z6]),(0,[z7,z1,z3,z4,z1079,z6])]],
   [[(1,[z1,z731,z4,z5,z6]),(0,[z7,z1,z3,z718,z5,z6]),(0,[z7,z1080,z3,z4,z5,z6]),(0,[z7,z1,z3,z29,z6,z467]),(0,[z7,z1081,z3,z4,z5,z6]),(0,[z7,z1,z918,z4,z29,z6])],[(0,[z7,z1,z3,z1082,z4,z6])],[(0,[z7,z1,z8,z4,z5,z118]),(1,[z1,z3,z4,z5,z737]),(0,[z7,z1,z1083,z3,z4,z6]),(0,[z7,z1,z20,z213,z4,z187])],[(0,[z457,z7,z3,z302,z5,z6]),(0,[z7,z1084,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z1085,z6])],[(0,[z192,z50,z3,z4,z29,z6]),(0,[z7,z50,z3,z153,z4,z6]),(0,[z7,z1086,z3,z4,z5,z6]),(0,[z539,z1,z2,z4,z5,z6]),(0,[z7,z99,z3,z4,z17,z6])],[(0,[z7,z56,z3,z4,z5,z6]),(0,[z7,z92,z3,z116,z4,z6]),(0,[z7,z1,z569,z22,z5,z6]),(0,[z7,z167,z27,z4,z29,z6])],[(0,[z7,z3,z4,z5,z147,z759]),(1,[z7,z1,z857,z3,z6])],[(0,[z7,z1087,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z5,z1088]),(0,[z7,z1,z308,z152,z5,z6]),(0,[z7,z3,z4,z5,z6,z1089]),(0,[z7,z1,z1090,z3,z4,z29]),(0,[z7,z1,z20,z3,z479,z6]),(0,[z7,z1091,z3,z4,z5,z6])]],
   [[(0,[z7,z232,z3,z4,z5,z6]),(0,[z7,z19,z3,z4,z5,z159])],[(0,[z7,z50,z3,z4,z29,z6])],[(0,[z7,z1,z3,z4,z915,z6]),(0,[z550,z19,z3,z4,z5,z6]),(0,[z1092,z7,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z96,z6]),(0,[z7,z1,z3,z1093,z4,z6]),(0,[z7,z949,z3,z4,z29,z6])],[(0,[z55,z19,z3,z133,z5,z6]),(0,[z158,z189,z24,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z1094]),(0,[z7,z201,z20,z3,z4,z6]),(0,[z7,z854,z3,z4,z5,z6]),(0,[z7,z1095,z3,z4,z5,z6]),(0,[z7,z99,z3,z4,z572,z6])],[(0,[z7,z1,z79,z4,z5,z6]),(0,[z7,z1,z1096,z3,z5,z6]),(0,[z7,z1,z3,z4,z1097,z6]),(0,[z7,z1,z130,z22,z5,z6]),(0,[z1098,z1,z3,z4,z5,z6]),(0,[z7,z1,z152,z734,z5,z6]),(0,[z7,z1,z60,z4,z5,z744])],[(0,[z7,z50,z3,z4,z750,z6]),(0,[z7,z289,z3,z4,z5,z147]),(0,[z7,z1,z1035,z3,z4,z6]),(0,[z55,z1,z3,z869,z5,z6]),(0,[z7,z3,z4,z859,z5,z6]),(0,[z80,z1,z3,z4,z218,z6]),(0,[z1099,z1,z3,z4,z5,z6]),(0,[z7,z1,z224,z58,z4,z6]),(0,[z1,z3,z4,z29,z6,z1045]),(0,[z7,z1,z311,z3,z5,z276])],[(0,[z7,z1,z3,z4,z1037,z6]),(0,[z7,z1,z3,z40,z29,z6]),(0,[z7,z1,z587,z3,z4,z6])],[(0,[z7,z1,z3,z5,z1038,z6]),(0,[z7,z726,z3,z4,z5,z6]),(0,[z86,z1,z3,z869,z5,z6]),(0,[z7,z3,z4,z103,z168,z6]),(0,[z7,z1,z3,z4,z1100,z6]),(0,[z7,z1,z3,z4,z38,z337])]],
   [[(0,[z7,z3,z4,z5,z6,z1101]),(0,[z856,z7,z1,z3,z4,z6]),(0,[z7,z19,z3,z4,z763,z6]),(0,[z7,z1,z1031,z3,z4,z6])],[(0,[z7,z3,z4,z5,z6,z1102]),(0,[z7,z1103,z3,z4,z5,z6]),(0,[z7,z257,z20,z3,z4,z6]),(0,[z7,z1,z20,z3,z545,z6]),(0,[z7,z1,z3,z4,z186,z6]),(0,[z7,z1104,z3,z4,z5,z6])],[(0,[z7,z50,z3,z4,z70,z6]),(0,[z7,z166,z20,z3,z4,z6]),(0,[z1105,z7,z3,z4,z5,z6]),(0,[z7,z1106,z3,z4,z5,z6]),(0,[z7,z1,z3,z1107,z5,z6]),(0,[z7,z871,z3,z4,z5,z6]),(0,[z7,z3,z4,z29,z6,z111]),(0,[z7,z1,z840,z4,z5,z6]),(1,[z7,z1,z3,z5,z768])],[(0,[z7,z1,z3,z4,z5,z6]),(0,[z50,z3,z4,z5,z6,z563]),(0,[z7,z1,z3,z29,z512,z6]),(0,[z963,z1,z3,z4,z5,z6]),(0,[z7,z1,z1108,z3,z4,z6])],[(0,[z7,z19,z3,z4,z771,z6]),(0,[z26,z7,z20,z114,z4,z6])],[(0,[z7,z1,z1048,z3,z4,z5]),(0,[z730,z7,z1,z3,z4,z6]),(0,[z7,z67,z3,z155,z5,z6]),(0,[z1109,z1,z3,z4,z5,z6])],[(0,[z846,z1,z3,z4,z5,z6]),(0,[z80,z1,z3,z4,z32,z6]),(0,[z7,z1110,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z1111,z6]),(0,[z7,z1,z3,z4,z1112,z6]),(0,[z7,z1,z743,z224,z4,z6])],[(0,[z7,z1113,z3,z4,z5,z6]),(0,[z7,z1,z3,z107,z29,z6]),(0,[z1114,z1,z3,z4,z5,z6])]],
   [[(0,[z88,z7,z99,z3,z4,z6]),(0,[z26,z7,z762,z4,z5,z6])],[(0,[z7,z19,z79,z4,z5,z6]),(0,[z7,z20,z3,z4,z103,z6])],[(0,[z7,z1,z3,z531,z29,z6])],[(0,[z7,z167,z258,z4,z5,z6]),(0,[z7,z1115,z3,z4,z5,z6]),(0,[z7,z1,z1116,z4,z5,z6]),(0,[z7,z1,z3,z1117,z4,z6]),(0,[z7,z1,z743,z3,z4,z6]),(0,[z7,z1,z109,z743,z4,z6]),(0,[z7,z1,z446,z3,z4,z91])],[(0,[z7,z1,z3,z4,z1118,z6])],[(0,[z7,z1,z1119,z4,z5,z6]),(0,[z7,z1120,z3,z4,z5,z6])],[(0,[z7,z50,z779,z3,z5,z6]),(0,[z76,z7,z1,z3,z4,z6]),(0,[z76,z7,z115,z3,z4,z6]),(0,[z10,z7,z3,z302,z5,z6]),(0,[z150,z1,z3,z4,z5,z151]),(0,[z7,z1,z1121,z3,z4,z6]),(0,[z7,z1,z3,z4,z1122,z6]),(0,[z16,z7,z3,z4,z103,z6]),(0,[z7,z99,z3,z40,z29,z6]),(0,[z7,z1,z311,z3,z105,z276])],[(0,[z568,z50,z3,z4,z5,z6]),(0,[z7,z1,z818,z3,z4,z6]),(0,[z7,z19,z3,z302,z29,z6]),(0,[z7,z1,z1051,z4,z5,z6]),(0,[z7,z1123,z3,z4,z5,z6])]],
   [[(0,[z76,z7,z92,z3,z4,z6]),(0,[z7,z1124,z3,z4,z5,z6]),(0,[z7,z1,z3,z5,z120,z768])],[(0,[z7,z307,z3,z4,z5,z6]),(0,[z7,z19,z8,z4,z5,z6]),(0,[z7,z1,z4,z5,z6,z1125])],[(0,[z7,z209,z3,z4,z5,z6]),(0,[z7,z50,z3,z4,z141,z6]),(0,[z7,z1,z3,z4,z1126,z6]),(0,[z7,z1,z3,z4,z5,z1127]),(0,[z7,z1128,z3,z4,z5,z6]),(0,[z1129,z7,z1,z3,z4,z6])],[(0,[z7,z11,z3,z155,z5,z6]),(0,[z35,z1,z3,z4,z32,z6]),(0,[z7,z99,z3,z4,z5,z6]),(0,[z7,z1,z3,z548,z29,z6])],[(0,[z7,z1,z3,z1130,z5,z6]),(0,[z7,z1,z1090,z3,z4,z5]),(0,[z7,z1,z1131,z4,z5,z6])],[(0,[z50,z3,z608,z4,z5,z6]),(0,[z7,z19,z224,z4,z112,z6]),(0,[z7,z1,z3,z4,z1132,z6]),(0,[z7,z3,z718,z81,z5,z6])],[(0,[z7,z50,z8,z4,z5,z6]),(0,[z180,z1,z24,z4,z5,z6])],[(0,[z7,z1,z1133,z4,z5,z6])]],
   [[(0,[z7,z1134,z3,z4,z5,z6]),(0,[z7,z1,z3,z4,z29,z118]),(0,[z7,z87,z20,z3,z4,z6]),(0,[z7,z3,z4,z103,z5,z6]),(0,[z7,z1,z3,z4,z1135,z6])],[(0,[z55,z1,z3,z133,z5,z159]),(0,[z7,z3,z718,z4,z5,z6]),(0,[z7,z1,z3,z1136,z4,z6])],[(0,[z7,z50,z224,z4,z112,z6]),(0,[z86,z1,z3,z95,z29,z6]),(0,[z268,z7,z99,z3,z4,z6])],[(0,[z7,z1,z3,z4,z1071,z6]),(0,[z7,z19,z60,z4,z5,z61]),(0,[z55,z1,z20,z3,z133,z6]),(0,[z1137,z1,z3,z4,z5,z6]),(0,[z7,z789,z3,z4,z5,z6]),(0,[z7,z1,z743,z4,z112,z6]),(0,[z383,z7,z3,z4,z103,z6])],[(0,[z50,z3,z629,z4,z5,z6]),(0,[z7,z1,z3,z1138,z5,z6]),(0,[z7,z3,z4,z17,z141,z6]),(0,[z7,z916,z20,z3,z4,z6])],[(0,[z585,z50,z3,z4,z5,z6]),(0,[z7,z298,z3,z4,z208,z6]),(0,[z7,z1,z3,z1139,z5,z6]),(0,[z7,z1140,z3,z4,z5,z6])],[(0,[z76,z7,z3,z4,z460,z6]),(0,[z7,z1,z1075,z3,z4,z6]),(0,[z7,z1,z3,z869,z5,z6]),(0,[z7,z1141,z3,z4,z5,z6])],[(0,[z7,z3,z4,z923,z5,z6]),(0,[z7,z732,z3,z4,z96,z6]),(0,[z7,z232,z3,z4,z29,z6]),(0,[z1142,z1,z3,z4,z5,z6]),(0,[z7,z1143,z3,z4,z5,z6]),(0,[z7,z1144,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 528) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 528).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1054).take 232) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1286)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [528, 526, 232] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 112).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 230).take 26).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [112, 118, 26] = true :=
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

end PEqualNP.Outside.L_meta_41270

theorem PEqualNP.Outside.L_meta_41270 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809440 * 2 ^ 32 + 4276789248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809440 * 2 ^ 32 + 4276789248) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41270.solve