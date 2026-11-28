import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36346

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
  Nat.testBit (4277075690 * 2 ^ 32 + 4277074088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0120000810409129#64 ++ 0x2024000102081225#64 ++ 0xf7d0a418f0c993ff#64 ++ 0xdefa14831e19327f#64 : BitVec 256),
   (0x10c0086341126290#64 ++ 0xc218010c68224c52#64 ++ 0xefb958e74336639f#64 ++ 0xbdf72b1ce866cc73#64 : BitVec 256),
   (0x40826105843824c4#64 ++ 0x88104c20b0870498#64 ++ 0xdd7e63078c387ce5#64 ++ 0x7bafcc60f1870f9c#64 : BitVec 256),
   (0x250582b80bc05b01#64 ++ 0x04a0b05701780b60#64 ++ 0xbcff83f80fc07f04#64 ++ 0xf79ff07f01f80fe0#64 : BitVec 256),
   (0x4607f4000ead0006#64 ++ 0x08c0fe8001d5a000#64 ++ 0x83f7fc000fff8003#64 ++ 0xf07eff8001fff000#64 : BitVec 256),
   (0x7807ffd6e0000000#64 ++ 0x0f00fffadc000000#64 ++ 0x7ff7fffff0000000#64 ++ 0x0ffefffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.or, [6, 2]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [7, 9]⟩, ⟨.or, [7, 9]⟩, ⟨.and, [11, 5]⟩, ⟨.or, [12, 4]⟩, ⟨.and, [8, 13]⟩, ⟨.or, [14, 10]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7d0a418f0c993ff 0xdefa14831e19327f

def z1 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb958e74336639f 0xbdf72b1ce866cc73

def z2 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcff83f80fc07f04 0xf79ff07f01f80fe0

def z3 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd7e63078c387ce5 0x7bafcc60f1870f9c

def z4 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x0067fc000fff8000 0x600cff8001fff000

def z5 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff0000000 0x0ffefffffe000000

def z6 : W := mkw 0x1000084240000000 0x0200010848000000 0x7ff1fcfff0000000 0x0ffe3f9ffe000000

def z7 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0xfff9fcfff3fff3ff 0xffff3f9ffe7ffe7f

def z8 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83f7fc000fff8003 0xf07eff8001fff000

def z9 : W := mkw 0x0120000810409129 0x2024000102081225 0x8000000000c993ff 0xd00000000019327f

def z10 : W := mkw 0x7927ffdef0409129 0x2f24fffbde081225 0xfff7fffff0c993ff 0xdffefffffe19327f

def z11 : W := mkw 0x0000002001004200 0x0000000400200840 0xacb900e003006304 0xb597201c00600c60

def z12 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7ffffffff8003 0xfffefffffffff000

def z13 : W := mkw 0x18001c4260000000 0x030003884c000000 0x02001c0070000000 0x004003800e000000

def z14 : W := mkw 0x3e059ed26a850002 0x07c0b3da4d50a000 0x22819cf873c78002 0x8450339f0e78f000

def z15 : W := mkw 0x0120000810409129 0x2024000102081225 0x1040a418b0c99060 0x420814831619320c

def z16 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x082f03e00f006c00 0x2105e07c01e00d80

def z17 : W := mkw 0x2005829000000000 0x0400b05200000000 0x7ff7a7f8f0000000 0x0ffef4ff1e000000

def z18 : W := mkw 0x0000000000000000 0x0000000000000000 0x83b1580003360003 0xb0762b000066c000

def z19 : W := mkw 0x1000084240000000 0x0200010848000000 0x6fb158e740000000 0x0df62b1ce8000000

def z20 : W := mkw 0x6807f794a0000000 0x0d00fef294000000 0x1046a718b0000000 0x0208d4e316000000

def z21 : W := mkw 0x0000000000000000 0x0000000000000000 0x9c7e03000c007c04 0x738fc06001800f80

def z22 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x208180f803c00300 0x8410301f00780060

def z23 : W := mkw 0x0120000810409129 0x2024000102081225 0xb6d0841870c1931e 0xd6da10830e183263

def z24 : W := mkw 0x4007f40004280004 0x0800fe8000850000 0x83f7fc000c380001 0x707eff8001870000

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0xd5502000800810e5 0x5aaa04001001021c

def z26 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff978e7c33e73ff 0xffff2f1cf867ce7f

def z27 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x6381fcfff0000000 0x0c703f9ffe000000

def z28 : W := mkw 0x1000084240000000 0x0200010848000000 0xefb158e743360003 0xbdf62b1ce866c000

def z29 : W := mkw 0x0100000800401101 0x0020000100080220 0xb4d0801800c01304 0xd69a100300180260

def z30 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffffa7f8ffc9ffff 0xfffff4ff1ff93fff

def z31 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x000000000cc98000 0x4000000001993000

def z32 : W := mkw 0x210002b801405b01 0x0420005700280b60 0x3c0803f800007f04 0x0781007f00000fe0

def z33 : W := mkw 0x38c59ef361126290 0xc718b3de6c224c52 0xefb9dcff7336639f 0xbdf73b9fee66cc73

def z34 : W := mkw 0x4007f40000000000 0x0800fe8000000000 0x03f7fc0000000000 0x007eff8000000000

def z35 : W := mkw 0x0020000010008028 0x2004000002001005 0x43002400f00980fb 0x086004801e01301f

def z36 : W := mkw 0x4727f4081eed912f 0x28e4fe8103ddb225 0xa3f7fc187fff831b 0xf47eff830ffff063

def z37 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x22819cf870000000 0x0450339f0e000000

def z38 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x08275be700000000 0x0104eb7ce0000000

def z39 : W := mkw 0x0080000100102080 0x8010000020020410 0xcd38400700306085 0x39a70800e0060c10

def z40 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7c0003fff0000000 0x0f80007ffe000000

def z41 : W := mkw 0x250582980ac01901 0x04a0b05301580320 0x90f783180fc01c00 0xf21ef06301f80380

def z42 : W := mkw 0x4207f400042d0006 0x0840fe800085a000 0x03f7fc00003f8003 0x007eff800007f000

def z43 : W := mkw 0x4687f5058ebd24c6 0x88d0fea0b1d7a498 0xdfffff078ffffce7 0xfbffffe0f1ffff9c

def z44 : W := mkw 0x38000ad260000000 0x0700015a4c000000 0x200000f870000000 0x0400001f0e000000

def z45 : W := mkw 0x0000000000000000 0x0000000000000000 0x228000004000031a 0x8450000008000063

def z46 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x0046a4000cc98000 0x4008d48001993000

def z47 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x000100e003000000 0x0000201c00600000

def z48 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x77d1bcf8f0000000 0x0efa379f1e000000

def z49 : W := mkw 0x00c0002101126290 0xc018000420224c52 0x800800000336639f 0xb00100000066cc73

def z50 : W := mkw 0x3d059efa6bc05b01 0x07a0b3df4d780b60 0xbeff9ff87fc07f04 0xf7dff3ff0ff80fe0

def z51 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x08275be70f360000 0x2104eb7ce1e6c000

def z52 : W := mkw 0x052000281bc0db29 0x20a4000503781b65 0x800800000fc9ffff 0xf001000001f93fff

def z53 : W := mkw 0x0000000000000000 0x0000000000000000 0x83d0a40000c98003 0xd07a148000193000

def z54 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbfffa7f80fc9ff07 0xf7fff4ff01f93fe0

def z55 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x002758000f360000 0x2004eb0001e6c000

def z56 : W := mkw 0x252582981ac09929 0x24a4b05303581325 0xf7d6a718fcc99fff 0xdefad4e31f9933ff

def z57 : W := mkw 0x212002b81140db29 0x2424005702281b65 0xffd8a7f8f0c9ffff 0xdffb14ff1e193fff

def z58 : W := mkw 0x41a2610d9478b5ed 0xa8344c21b28f16bd 0xfffee71ffcf9ffff 0xffffdce3ff9f3fff

def z59 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7c275bfff0000000 0x0f84eb7ffe000000

def z60 : W := mkw 0x41a2610d9478b5ed 0xa8344c21b28f16bd 0xfd7e631ffc387ffd 0x7fafcc63ff870fff

def z61 : W := mkw 0x250582980ac01901 0x04a0b05301580320 0x104683180cc01c00 0x4208d06301980380

def z62 : W := mkw 0x50c26967c53a66d4 0xca184d2cf8a74cda 0xffff7be7cf3e7fff 0xffffef7cf9e7cfff

def z63 : W := mkw 0x50c26947c43a24d4 0xca184d28f887449a 0x43007807c03e00fb 0x08600f00f807c01f

def z64 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdfff7b078f3e7ce7 0xfbffef60f1e7cf9c

def z65 : W := mkw 0x040580000a800000 0x0080b00001500000 0x80f780000fc00000 0xf01ef00001f80000

def z66 : W := mkw 0x78027fd6e0000000 0x0f004ffadc000000 0x7f007ffff0000000 0x0fe00ffffe000000

def z67 : W := mkw 0x270596b80bc55b03 0x04e0b2d70178ab60 0xbeff9ff80fc7ff06 0xf7dff3ff01f8ffe0

def z68 : W := mkw 0x0000000000000000 0x0000000000000000 0x430000004000009b 0x0860000008000013

def z69 : W := mkw 0x42027400042d0006 0x08404e800085a000 0x83d0fc0000ff8003 0xd07a1f80001ff000

def z70 : W := mkw 0x1040086241024210 0x4208010c48204842 0x228118e04306031a 0x8450231c0860c063

def z71 : W := mkw 0x0000000000000000 0x0000000000000000 0x6790000040000000 0x0cf2000008000000

def z72 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x000600000c000000 0x0000c00001800000

def z73 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x492e63078c386ce1 0x2925cc60f1870d9c

def z74 : W := mkw 0x5607fc424ead0006 0x0ac0ff8849d5a000 0xeff7fce74fff8003 0xfdfeff9ce9fff000

def z75 : W := mkw 0x052580081ac09129 0x20a4b00103581225 0xf7f7a418ffc993ff 0xfefef4831ff9327f

def z76 : W := mkw 0x072000081eed912f 0x20e4000103ddb225 0xf7d0a418ffff93ff 0xfefa14831ffff27f

def z77 : W := mkw 0x0000000000000000 0x0000000000000000 0xe79000004000039f 0x9cf2000008000073

def z78 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x186f83f80fc07c00 0x630df07f01f80f80

def z79 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xeff9fce743ffe39f 0xfdff3f9ce87ffc73

def z80 : W := mkw 0x4727f4081eed912f 0x28e4fe8103ddb225 0xf7f7fc18ffff93ff 0xfefeff831ffff27f

def z81 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d7e63078c306c00 0x2bafcc60f1860d80

def z82 : W := mkw 0x2005829000000000 0x0400b05200000000 0x3cf783f800000000 0x079ef07f00000000

def z83 : W := mkw 0x78c7fff7e1126290 0xcf18fffefc224c52 0x7ffffffff3366000 0x2ffffffffe66cc00

def z84 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0xefb9dcff73f7e39f 0xbdf73b9fee7efc73

def z85 : W := mkw 0x46c7f4210fbf6296 0xc8d8fe8421f7ec52 0x83fffc000fffe39f 0xf07fff8001fffc73

def z86 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x9fffff000ffffc07 0xf3ffffe001ffff80

def z87 : W := mkw 0x6587e3bd8ff87fc5 0x8cb0fc77b1ff0ff8 0xfdffe3ff8ff87fe5 0xffbffc7ff1ff0ffc

def z88 : W := mkw 0x39259eda70409129 0x2724b3db4e081225 0xf7d1bcf8f0c993ff 0xdefa379f1e19327f

def z89 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xacbf03e00f006f04 0xb597e07c01e00de0

def z90 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x082958e703366000 0x21052b1ce066cc00

def z91 : W := mkw 0x0100000800401101 0x0020000100080220 0x2080801800c00300 0x8410100300180060

def z92 : W := mkw 0x58027d46e0000000 0x0b004fa8dc000000 0x43007c07f0000000 0x08600f80fe000000

def z93 : W := mkw 0x7d27fffefbc0db29 0x2fa4ffffdf781b65 0xffffffffffc9ffff 0xfffffffffff93fff

def z94 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x80f7a4000fc98000 0xf01ef48001f93000

def z95 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c08030000007c04 0x0381006000000f80

def z96 : W := mkw 0x6707f6b80fed5b07 0x0ce0fed701fdab60 0xbffffff80fffff07 0xf7ffffff01ffffe0

def z97 : W := mkw 0x42027400042d0006 0x08404e800085a000 0x03007c00003f8003 0x00600f800007f000

def z98 : W := mkw 0x7a07ffd6e42d0006 0x0f40fffadc85a000 0x7ff7fffff03f8003 0x0ffefffffe07f000

def z99 : W := mkw 0x060594000ead0006 0x00c0b28001d5a000 0x82819c000fff8003 0xf050338001fff000

def z100 : W := mkw 0x56c7fc634fbf6296 0xcad8ff8c69f7ec52 0xeffffce74fffe39f 0xfdffff9ce9fffc73

def z101 : W := mkw 0x5e07fd46eead0006 0x0bc0ffa8ddd5a000 0xc3f7fc07ffff8003 0xf87eff80fffff000

def z102 : W := mkw 0x240582900a800800 0x0480b05201500100 0x000603000c000c00 0x0000c06001800180

def z103 : W := mkw 0x50c26967c53a66d4 0xca184d2cf8a74cda 0xdd7f7be78f3e7ce5 0x7bafef7cf1e7cf9c

def z104 : W := mkw 0x0080000100102080 0x8010000020020410 0xefb840074030639f 0xbdf70800e8060c73

def z105 : W := mkw 0x072594081ac5912b 0x20e4b2810358b225 0x22819c1873c7831a 0x845033830e78f063

def z106 : W := mkw 0x00800105801024c0 0x80100020b0020498 0xdc7e03078c007ce4 0x7b8fc060f1800f9c

def z107 : W := mkw 0x4002610484280444 0x08004c2090850088 0x104623008c081c60 0x4208c4601181038c

def z108 : W := mkw 0x4002600000000000 0x08004c0000000000 0x0176600000000000 0x002ecc0000000000

def z109 : W := mkw 0x10c0084340122090 0xc218010868024412 0x430058074036009b 0x08600b00e806c013

def z110 : W := mkw 0x7d07ffdeeac01901 0x0fa0fffbdd580320 0x7ff7fffffcc01c00 0x4ffeffffff980380

def z111 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0xfff7fffffc380001 0x7ffeffffff870000

def z112 : W := mkw 0x00c0002101126290 0xc018000420224c52 0x83b958000336639f 0xb0772b000066cc73

def z113 : W := mkw 0x58027d46e0000000 0x0b004fa8dc000000 0x77d0fc1ff0000000 0x0efa1f83fe000000

def z114 : W := mkw 0x00800001043824c4 0x8010000020870498 0x00000000003800e1 0x000000000007001c

def z115 : W := mkw 0x212002b81140db29 0x2424005702281b65 0x7c0803f8f0007ffc 0x0f81007f1e000fff

def z116 : W := mkw 0x0000000000000000 0x0000000000000000 0x77d0a418f0000000 0x0efa14831e000000

def z117 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff9fcfff336639f 0xbfff3f9ffe66cc73

def z118 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x41006007803800e1 0x08200c00f007001c

def z119 : W := mkw 0x7d07fffeebc05b01 0x0fa0ffffdd780b60 0xffffffffffc07f04 0xfffffffffff80fe0

def z120 : W := mkw 0x6507e2b80fe85b05 0x0ca0fc5701fd0b60 0xbdffe3f80ff87f05 0xf7bffc7f01ff0fe0

def z121 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x02819c0003c78002 0x805033800078f000

def z122 : W := mkw 0x7e07ffd6ea850002 0x0fc0fffadd50a000 0x7ff7fffff3c78002 0x8ffefffffe78f000

def z123 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x1867ffffb0000000 0x030cfffff6000000

def z124 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfffee71ffc387ce5 0x7fffdce3ff870f9c

def z125 : W := mkw 0x4002600004280004 0x08004c0000850000 0x83f778000f3e0003 0xf07eef0001e7c000

def z126 : W := mkw 0x00800001043824c4 0x8010000020870498 0x9c7e03000c387ce5 0x738fc06001870f9c

def z127 : W := mkw 0x6807f794a0000000 0x0d00fef294000000 0x3cf7a7f8b0000000 0x079ef4ff16000000

def z128 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6c2958e74336639c 0x2d852b1ce866cc73

def z129 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7d02000c00813ff 0xdefa04001801027f

def z130 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x6fb1dcff70000000 0x0df63b9fee000000

def z131 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7c46a7fff0000000 0x0f88d4fffe000000

def z132 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfffffffffc007c04 0x7fffffffff800f80

def z133 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d766307803800e1 0x0baecc60f007001c

def z134 : W := mkw 0x4607f5048ead0006 0x08c0fea091d5a000 0xdff7ff078fff8003 0xfbfeffe0f1fff000

def z135 : W := mkw 0x39259eda70409129 0x2724b3db4e081225 0x22819cf870c1831a 0x8450339f0e183063

def z136 : W := mkw 0x35c58afb4bd27b91 0xc6b8b15f697a4f72 0xffffdbff4ff67f9f 0xfffffb7fe9fecff3

def z137 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z138 : W := mkw 0x0000000004280004 0x0000000000850000 0x800000000c380001 0x7000000001870000

def z139 : W := mkw 0x01e000291152f3b9 0xe03c0005222a5e77 0x8008000003fff3ff 0xf0010000007ffe7f

def z140 : W := mkw 0x0100000800401101 0x0020000100080220 0x3400001800001304 0x0680000300000260

def z141 : W := mkw 0x00800105801024c0 0x80100020b0020498 0x5c08030780007ce4 0x0b810060f0000f9c

def z142 : W := mkw 0x00800001043824c4 0x8010000020870498 0x800800000c387ce5 0x7001000001870f9c

def z143 : W := mkw 0x0120000810409129 0x2024000102081225 0x74000018f00013fc 0x0e8000031e00027f

def z144 : W := mkw 0x4002600004280004 0x08004c0000850000 0x004620000c080000 0x4008c40001810000

def z145 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff000039f 0x9ffefffffe000073

def z146 : W := mkw 0x0120000810409129 0x2024000102081225 0x0000000000c1831a 0x8000000000183063

def z147 : W := mkw 0x00800001043824c4 0x8010000020870498 0x000800000c306c00 0x2001000001860d80

def z148 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x082e43070c306c00 0x2105c860e1860d80

def z149 : W := mkw 0x050000080ac01901 0x00a0000101580320 0x000000000cc01c00 0x4000000001980380

def z150 : W := mkw 0x18000946e0000000 0x03000128dc000000 0x40000007f0000000 0x08000000fe000000

def z151 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x6fb75be740000000 0x0df6eb7ce8000000

def z152 : W := mkw 0x78c7fff7e1126290 0xcf18fffefc224c52 0xfffffffff336639f 0xbffffffffe66cc73

def z153 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xacb958e703366304 0xb5972b1ce066cc60

def z154 : W := mkw 0x10c0084340122090 0xc218010868024412 0x4000000740000098 0x08000000e8000013

def z155 : W := mkw 0x1000084240000000 0x0200010848000000 0x4300580740000000 0x08600b00e8000000

def z156 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c76030000000000 0x038ec06000000000

def z157 : W := mkw 0x0120000810409129 0x2024000102081225 0xa280841870c993ff 0xd45010830e19327f

def z158 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcff83f80fc9ffff 0xf79ff07f01f93fff

def z159 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7fffffcc98000 0x4ffeffffff993000

def z160 : W := mkw 0x4002600004280004 0x08004c0000850000 0x0100600000380001 0x00200c0000070000

def z161 : W := mkw 0x7827ffd6f0008028 0x2f04fffade001005 0x7ff7fffff00980fb 0x0ffefffffe01301f

def z162 : W := mkw 0x40a261059438a4ec 0xa8144c20b287149d 0x43006407f03980fb 0x08600c80fe07301f

def z163 : W := mkw 0x4002600004280004 0x08004c0000850000 0x83f6e4000cf98003 0xf07edc80019f3000

def z164 : W := mkw 0x0120000810409129 0x2024000102081225 0x2000001870000318 0x040000030e000063

def z165 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3c2f03f80f007f04 0x2785e07f01e00fe0

def z166 : W := mkw 0x4607f5048ead0446 0x08c0fea091d5a088 0x93f7ff008fff9c63 0xf27effe011fff38c

def z167 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6c0800e74000639c 0x0d81001ce8000c73

def z168 : W := mkw 0x0100000800401101 0x0020000100080220 0xf5d0a01880c813e5 0xdeba14031019027c

def z169 : W := mkw 0x6707f6980eed1907 0x0ce0fed301dda320 0x1046a7180cc99c00 0x4208d4e301993380

def z170 : W := mkw 0x4002600004280004 0x08004c0000850000 0x817660000c380001 0x702ecc0001870000

def z171 : W := mkw 0x4687f4010ebd24c6 0x88d0fe8021d7a498 0x83fffc000ffffce7 0xf07fff8001ffff9c

def z172 : W := mkw 0x7f07fffeefed5b07 0x0fe0ffffddfdab60 0xffffffffffffff07 0xffffffffffffffe0

def z173 : W := mkw 0x51e2696fd57af7fd 0xea3c4d2dfaaf5eff 0xffffffffffffffff 0xffffffffffffffff

def z174 : W := mkw 0x210002b801405b01 0x0420005700280b60 0xbcd883f800c07f04 0xd79b107f00180fe0

def z175 : W := mkw 0x0000000000000000 0x0000000000000000 0x104603000c001c00 0x4208c06001800380

def z176 : W := mkw 0x0120000810409129 0x2024000102081225 0xfffea718fcc9ffff 0xffffd4e31f993fff

def z177 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdffee7078cf9fce7 0xfbffdce0f19f3f9c

def z178 : W := mkw 0x4002610484280444 0x08004c2090850088 0x5d7663078c081c60 0x4baecc60f181038c

def z179 : W := mkw 0x6887f795a43824c4 0x8d10fef2b4870498 0xdd7ee71fbc387ce5 0x7bafdce3f7870f9c

def z180 : W := mkw 0x4727f4081eed912f 0x28e4fe8103ddb225 0x93f7fc18bfff9063 0xf27eff8317fff20c

def z181 : W := mkw 0x2005829000000000 0x0400b05200000000 0x1046831800000000 0x0208d06300000000

def z182 : W := mkw 0x4687f5058ebd24c6 0x88d0fea0b1d7a498 0xdd7ee7078cf9fce5 0x7bafdce0f19f3f9c

def z183 : W := mkw 0x40c26125853a66d4 0xc8184c24b0a74cda 0xdd7e63078f3e7fff 0xfbafcc60f1e7cfff

def z184 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfffe6307cc387fff 0xffffcc60f9870fff

def z185 : W := mkw 0x0120000810409129 0x2024000102081225 0x2280841870c1831a 0x845010830e183063

def z186 : W := mkw 0x7887ffd7e43824c4 0x8f10fffafc870498 0xfffffffffc387ce5 0x7fffffffff870f9c

def z187 : W := mkw 0x0000000000000000 0x0000000000000000 0x2280841870000000 0x045010830e000000

def z188 : W := mkw 0x50026946c0000000 0x0a004d28d8000000 0x7ff77be7c0000000 0x0ffeef7cf8000000

def z189 : W := mkw 0x0000010480000440 0x0000002090000088 0x1000030080001c60 0x020000601000038c

def z190 : W := mkw 0x1040086241024210 0x4208010c48204842 0x6fb158e74306031a 0x8df62b1ce860c063

def z191 : W := mkw 0x7e87ffd7eebd24c6 0x8fd0fffafdd7a498 0xfffffffffffffce7 0xffffffffffffff9c

def z192 : W := mkw 0x0000000000000000 0x0000000000000000 0x83f1fc0003ff8003 0xf07e3f80007ff000

def z193 : W := mkw 0x4002610484280444 0x08004c2090850088 0x9c7e23008c087c64 0x738fc46011810f8c

def z194 : W := mkw 0x56c7fc434ebf2096 0xcad8ff8869d7e412 0xc3f7fc074fff809b 0xf87eff80e9fff013

def z195 : W := mkw 0x6607f6900ead0006 0x0cc0fed201d5a000 0xbff7fff80fff8003 0xf7feffff01fff000

def z196 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x800000000fff8003 0xf000000001fff000

def z197 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7fd0a7fff0000000 0x0ffa14fffe000000

def z198 : W := mkw 0x00c0000100122090 0xc018000020024412 0x000000000036009b 0x000000000006c013

def z199 : W := mkw 0x2805969020000000 0x0500b2d204000000 0x0000841830000000 0x0000108306000000

def z200 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8046a4000fff8003 0xf008d48001fff000

def z201 : W := mkw 0x4707f4280fed5b07 0x08e0fe8501fdab60 0x83fffc000fffff07 0xf07fff8001ffffe0

def z202 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xa08980f80fc07f04 0xf411301f01f80fe0

def z203 : W := mkw 0x4687f5058ebd24c6 0x88d0fea0b1d7a498 0xc3f7fc078fff80e3 0xf87eff80f1fff01c

def z204 : W := mkw 0x258583bd8bd07fc1 0x84b0b077b17a0ff8 0xfcff83ff8fc07fe4 0xff9ff07ff1f80ffc

def z205 : W := mkw 0x4707f4080eed1107 0x08e0fe8101dda220 0xb7f7fc180fff9307 0xf6feff8301fff260

def z206 : W := mkw 0x0080000100102080 0x8010000020020410 0xdd7e43070c307c85 0x7bafc860e1860f90

def z207 : W := mkw 0x4002600004280004 0x08004c0000850000 0xd57660008c3810e5 0x7aaecc001187021c

def z208 : W := mkw 0x4007f40000000000 0x0800fe8000000000 0x77f7fc18f0000000 0x0efeff831e000000

def z209 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3c4e83f80cc07f04 0x4789d07f01980fe0

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7d0a418f0c98003 0xdefa14831e193000

def z211 : W := mkw 0x068000010ebd24c6 0x80d0000021d7a498 0x800800000ffffce7 0xf001000001ffff9c

def z212 : W := mkw 0x1040086241024210 0x4208010c48204842 0xa3b158e04336031b 0xb4762b1c0866c063

def z213 : W := mkw 0x4627f4001ead802e 0x28c4fe8003d5b005 0xc3f7fc00ffff80fb 0xf87eff801ffff01f

def z214 : W := mkw 0x0120000810409129 0x2024000102081225 0x00000000000013fc 0x000000000000027f

def z215 : W := mkw 0x00800001043824c4 0x8010000020870498 0xd55820008c387ce5 0x7aab040011870f9c

def z216 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff3360003 0xbffefffffe66c000

def z217 : W := mkw 0x00800105801024c0 0x80100020b0020498 0xdd38430780307ce5 0x3ba70860f0060f9c

def z218 : W := mkw 0x52c27c63453f6296 0xca584f8c68a7ec52 0xefb97ce7433fe39f 0xbdf72f9ce867fc73

def z219 : W := mkw 0x42827505843d24c6 0x88504ea0b087a498 0x43007c07803f80e3 0x08600f80f007f01c

def z220 : W := mkw 0x00c0002101126290 0xc018000420224c52 0x000800000000639c 0x0001000000000c73

def z221 : W := mkw 0x0000010480000000 0x0000002090000000 0x5c00030780000000 0x0b800060f0000000

def z222 : W := mkw 0x0000002001004200 0x0000000400200840 0xefb900e04300639f 0xbdf7201c08600c73

def z223 : W := mkw 0x7887ffd7e0102080 0x8f10fffafc020410 0xfffffffff0306085 0x3ffffffffe060c10

def z224 : W := mkw 0x4727f4081eed912f 0x28e4fe8103ddb225 0xf7d6a418fcc993ff 0xdefad4831f99327f

def z225 : W := mkw 0x0100000800401101 0x0020000100080220 0xb7d0a41800c99307 0xd6fa148300193260

def z226 : W := mkw 0x0120000810409129 0x2024000102081225 0xf5502018f00813fd 0x5eaa04031e01027f

def z227 : W := mkw 0x6727f6b81feddb2f 0x2ce4fed703fdbb65 0xfffffff8ffffffff 0xffffffff1fffffff

def z228 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xffff5be74f367f9f 0xffffeb7ce9e6cff3

def z229 : W := mkw 0x6e07f794aead0006 0x0dc0fef295d5a000 0x1046a718bcc98000 0x4208d4e317993000

def z230 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x186e63078c387c60 0x630dcc60f1870f8c

def z231 : W := mkw 0x0000000000000000 0x0000000000000000 0x43002400f0000000 0x086004801e000000

def z232 : W := mkw 0x31c00afb41527b91 0xc638015f682a4f72 0x7c0803ff40007f9c 0x0f81007fe8000ff3

def z233 : W := mkw 0x6d07f7bcabc05b01 0x0da0fef795780b60 0xbcffa7f8bfc07f04 0xf79ff4ff17f80fe0

def z234 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x7e819ffff0000000 0x0fd033fffe000000

def z235 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xf7f7fc18ffff8003 0xfefeff831ffff000

def z236 : W := mkw 0x14c588634b926290 0xc298b10c69724c52 0xefffd8e74ff6639f 0xfdfffb1ce9fecc73

def z237 : W := mkw 0x0120000810409129 0x2024000102081225 0xa3d0a41870c9831b 0xd47a14830e193063

def z238 : W := mkw 0x200002b001004a00 0x0400005600200940 0x080803e000006c00 0x0101007c00000d80

def z239 : W := mkw 0x4607f4200fad4206 0x08c0fe8401f5a840 0xaffffce00fffe307 0xf5ffff9c01fffc60

def z240 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7d0a418f00810e5 0x5efa14831e01021c

def z241 : W := mkw 0x65a7e3bd9ff8ffed 0xacb4fc77b3ff1ffd 0xffffe7fffff9ffff 0xfffffcffffff3fff

def z242 : W := mkw 0x4002600004280004 0x08004c0000850000 0x002640000c300000 0x2004c80001860000

def z243 : W := mkw 0x6007f69000000000 0x0c00fed200000000 0x3ff7fff800000000 0x07feffff00000000

def z244 : W := mkw 0x050580280bc05b01 0x00a0b00501780b60 0x80ff80000fc07f04 0xf01ff00001f80fe0

def z245 : W := mkw 0x59227d4ef0409129 0x2b244fa9de081225 0xf7d0fc1ff0c993ff 0xdefa1f83fe19327f

def z246 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x28af83f80fc06f00 0xa515f07f01f80de0

def z247 : W := mkw 0x4122610c9468956d 0x28244c21928d12ad 0x1046a718bcc99c60 0x4208d4e31799338c

def z248 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x897e63070c386c01 0x712fcc60e1870d80

def z249 : W := mkw 0x0005800000000000 0x0000b00000000000 0x00f7800000000000 0x001ef00000000000

def z250 : W := mkw 0x4002600004280004 0x08004c0000850000 0x9d7e63000c387c05 0x73afcc6001870f80

def z251 : W := mkw 0x4002610480000000 0x08004c2090000000 0x5d76630780000000 0x0baecc60f0000000

def z252 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0c98003 0xdffefffffe193000

def z253 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x904e83180fc07f04 0xf209d06301f80fe0

def z254 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x3ef79ff870000000 0x07def3ff0e000000

def z255 : W := mkw 0x78826bd7e43824c4 0x8f104d7afc870498 0xfd7e63fffc387ce5 0x7fafcc7fff870f9c

def z256 : W := mkw 0x258582b90bd07b81 0x84b0b057217a0f70 0xfdffc3ff0ff07f85 0xffbff87fe1fe0ff0

def z257 : W := mkw 0x6807f794a0000000 0x0d00fef294000000 0x13f7ff18b0000000 0x027effe316000000

def z258 : W := mkw 0x0020000010008028 0x2004000002001005 0x77d0a418f00980fb 0x0efa14831e01301f

def z259 : W := mkw 0x1040086241024210 0x4208010c48204842 0xe79118e04306039f 0x9cf2231c0860c073

def z260 : W := mkw 0x58027d46e0000000 0x0b004fa8dc000000 0x6fb17ce7f0000000 0x0df62f9cfe000000

def z261 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xc30858074336639f 0xb8610b00e866cc73

def z262 : W := mkw 0x072594081ac5912b 0x20e4b2810358b225 0xf7d1bc18f3cf93ff 0xdefa37831e79f27f

def z263 : W := mkw 0x040000200b804a00 0x0080000401700940 0x000800000f006c00 0x2001000001e00d80

def z264 : W := mkw 0x35c58afb4bd27b91 0xc6b8b15f697a4f72 0xefb9d8ff43f6639f 0xbdf73b1fe87ecc73

def z265 : W := mkw 0x4607f4000a850002 0x08c0fe800150a000 0x03f7fc0003c78002 0x807eff800078f000

def z266 : W := mkw 0x250582980ac01901 0x04a0b05301580320 0xb4d683180cc01f04 0xd69ad063019803e0

def z267 : W := mkw 0x0120000810409129 0x2024000102081225 0xe790841870c1839f 0x9cf210830e183073

def z268 : W := mkw 0x79e7fffff152f3b9 0xef3cfffffe2a5e77 0xfffffffff3fff3ff 0xfffffffffe7ffe7f

def z269 : W := mkw 0x38459ef261024210 0x4708b3de4c204842 0x22819cf87306031a 0x8450339f0e60c063

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0x082e03000c006c00 0x2105c06001800d80

def z271 : W := mkw 0x7807ffd6e4280444 0x0f00fffadc850088 0x7ff7fffffc081c60 0x4ffeffffff81038c

def z272 : W := mkw 0x77c7fefb4fff7b97 0xcef8ffdf69ffef72 0xffffffff4fffff9f 0xffffffffe9fffff3

def z273 : W := mkw 0x50c26967c53a66d4 0xca184d2cf8a74cda 0x082f5be70f366c00 0x2105eb7ce1e6cd80

def z274 : W := mkw 0x1120084a50409129 0x222401094a081225 0xfff1fcfff0c993ff 0xdffe3f9ffe19327f

def z275 : W := mkw 0x050000280bc05b01 0x00a0000501780b60 0x800800000fc07f04 0xf001000001f80fe0

def z276 : W := mkw 0x0005940000000000 0x0000b28000000000 0x02819c0000000000 0x0050338000000000

def z277 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x080800e700006000 0x0101001ce0000c00

def z278 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff00810e5 0x5ffefffffe01021c

def z279 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x9c7f03e00f007c04 0x738fe07c01e00f80

def z280 : W := mkw 0x6e07f794aead0006 0x0dc0fef295d5a000 0x93f7ff18bfff8003 0xf27effe317fff000

def z281 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x83b158000fff8003 0xf0762b0001fff000

def z282 : W := mkw 0x4127f40810409129 0x2824fe8102081225 0xf7f7fc18f0c993ff 0xdefeff831e19327f

def z283 : W := mkw 0x16c008634fbf6296 0xc2d8010c69f7ec52 0xefb958e74fffe39f 0xfdf72b1ce9fffc73

def z284 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x3cf7dbff00000000 0x079efb7fe0000000

def z285 : W := mkw 0x10c0084340122090 0xc218010868024412 0xe79058074036039f 0x9cf20b00e806c073

def z286 : W := mkw 0x0000000000000000 0x0000000000000000 0xe7b158004336039f 0xbcf62b000866c073

def z287 : W := mkw 0x7f27ffdefeed912f 0x2fe4fffbdfddb225 0xfff7ffffffff93ff 0xfffefffffffff27f

def z288 : W := mkw 0x6787f7bd8ffd7fc7 0x8cf0fef7b1ffaff8 0xffffffff8fffffe7 0xfffffffff1fffffc

def z289 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7ffffff360000 0x2ffeffffffe6c000

def z290 : W := mkw 0x0000002001004200 0x0000000400200840 0xbcff03e00f007f04 0xf79fe07c01e00fe0

def z291 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x88ff83e00fc06c00 0xf11ff07c01f80d80

def z292 : W := mkw 0x0120000810409129 0x2024000102081225 0xb4d0a418b0c99364 0xd69a14831619326c

def z293 : W := mkw 0x4007f40000000000 0x0800fe8000000000 0x83f7fc0003360003 0xb07eff800066c000

def z294 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x0381fc0003ff8003 0x80703f80007ff000

def z295 : W := mkw 0x38c00bf7e1126290 0xc718017efc224c52 0xffb95bfff336639f 0xbff72b7ffe66cc73

def z296 : W := mkw 0x2000029000000000 0x0400005200000000 0x3c0003f800000000 0x0780007f00000000

def z297 : W := mkw 0x00c0002101126290 0xc018000420224c52 0x0008000003366000 0x200100000066cc00

def z298 : W := mkw 0x050000280bc05b01 0x00a0000501780b60 0xb4d880180fc07f04 0xf69b100301f80fe0

def z299 : W := mkw 0x34c58af34b926a90 0xc698b15e69724d52 0x082f5be70f366c00 0x2105eb7ce1e6cd80

def z300 : W := mkw 0x4687f5058ebd24c6 0x88d0fea0b1d7a498 0xdd7f7b078f3e7ce5 0x7bafef60f1e7cf9c

def z301 : W := mkw 0x50826947c43824c4 0x8a104d28f8870498 0xffff7be7cc387ce5 0x7fffef7cf9870f9c

def z302 : W := mkw 0x7d87ffffeff87fc5 0x8fb0fffffdff0ff8 0xfffffffffff87fe5 0xffffffffffff0ffc

def z303 : W := mkw 0x1000084240000000 0x0200010848000000 0xefb158e74000039f 0x9df62b1ce8000073

def z304 : W := mkw 0x4007f40000000000 0x0800fe8000000000 0x83f7fc0000c98003 0xd07eff8000193000

def z305 : W := mkw 0x40826105801024c0 0x88104c20b0020498 0x5d7e630780007ce4 0x0bafcc60f0000f9c

def z306 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7f1fc18f3ff93ff 0xfefe3f831e7ff27f

def z307 : W := mkw 0x4007f40000000000 0x0800fe8000000000 0x0046a40000000000 0x0008d48000000000

def z308 : W := mkw 0x00c0002101126290 0xc018000420224c52 0xacb900e00336639f 0xb597201c0066cc73

def z309 : W := mkw 0x0080000100102080 0x8010000020020410 0x0828400700306000 0x21050800e0060c00

def z310 : W := mkw 0x0000000000000000 0x0000000000000000 0x2cb100e000000000 0x0596201c00000000

def z311 : W := mkw 0x43227408146d912f 0x28644e81028db225 0xf7d0fc18f0ff93ff 0xdefa1f831e1ff27f

def z312 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xd7f7fc008fff90e7 0xfafeff8011fff21c

def z313 : W := mkw 0x4002610484280444 0x08004c2090850088 0x0000200080080060 0x000004001001000c

def z314 : W := mkw 0x4487e1058eb824c4 0x8890fc20b1d70498 0xddffe3078ff87ce5 0xfbbffc60f1ff0f9c

def z315 : W := mkw 0x4002740000000000 0x08004e8000000000 0x03007c0000000000 0x00600f8000000000

def z316 : W := mkw 0x01a000091478b5ed 0xa0340001228f16bd 0x800800000cf9ffff 0xf0010000019f3fff

def z317 : W := mkw 0x7dc7ffffebd27b91 0xcfb8fffffd7a4f72 0xfffffffffff67f9f 0xfffffffffffecff3

def z318 : W := mkw 0x060580000ead0006 0x00c0b00001d5a000 0x80f780000fff8003 0xf01ef00001fff000

def z319 : W := mkw 0x0000000000000000 0x0000000000000000 0xdd7e23008c087ce5 0x7bafc46011810f9c

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0xf7d0a418f000039f 0x9efa14831e000073

def z321 : W := mkw 0x6487e3b58fb86ec4 0x8c90fc76b1f70dd8 0xdd7f63e78f387ce5 0x7bafec7cf1e70f9c

def z322 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0xefb958e743fff3ff 0xfdf72b1ce87ffe7f

def z323 : W := mkw 0x35c58afb4bd27b91 0xc6b8b15f697a4f72 0xfcff83ff4fc07f9c 0xff9ff07fe9f80ff3

def z324 : W := mkw 0x2005829000000000 0x0400b05200000000 0x208180f800000000 0x0410301f00000000

def z325 : W := mkw 0x4002610484280004 0x08004c2090850000 0xdd7663078c380001 0x7baecc60f1870000

def z326 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffff83f84fc07f9f 0xfffff07f09f80ff3

def z327 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5c4e23078c087ce4 0x4b89c460f1810f9c

def z328 : W := mkw 0x0000000000000000 0x0000000000000000 0x1040200080081060 0x420804001001020c

def z329 : W := mkw 0x10e008635112e2b8 0xe21c010c6a225c57 0xefb97ce7f33fe3ff 0xbdf72f9cfe67fc7f

def z330 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x0bf7ffe700000000 0x017efffce0000000

def z331 : W := mkw 0x0000000000000000 0x0000000000000000 0x03b1580000000000 0x00762b0000000000

def z332 : W := mkw 0x040580200b804200 0x0080b00401700840 0xacff80e00fc06304 0xf59ff01c01f80c60

def z333 : W := mkw 0x42827505843d24c6 0x88504ea0b087a498 0xdf7e7f078c3ffce7 0x7befcfe0f187ff9c

def z334 : W := mkw 0x0000000000000000 0x0000000000000000 0x8390000000000003 0x9072000000000000

def z335 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbfffdbf80ff67f07 0xf7fffb7f01fecfe0

def z336 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcffa7f8bfc9ff64 0xf79ff4ff17f93fec

def z337 : W := mkw 0x0100000800401101 0x0020000100080220 0x8000000000c01304 0xd000000000180260

def z338 : W := mkw 0x47a7f50d9efdb5ef 0xa8f4fea1b3dfb6bd 0xffffff1fffffffff 0xffffffe3ffffffff

def z339 : W := mkw 0x070000280fed5b07 0x00e0000501fdab60 0x800800000fffff07 0xf001000001ffffe0

def z340 : W := mkw 0x35e58afb5bd2fbb9 0xe6bcb15f6b7a5f77 0xffffffffffffffff 0xffffffffffffffff

def z341 : W := mkw 0x58027d46e0000000 0x0b004fa8dc000000 0x0000580700000000 0x00000b00e0000000

def z342 : W := mkw 0x7887ffd7e43824c4 0x8f10fffafc870498 0x7ff7fffff03800e1 0x0ffefffffe07001c

def z343 : W := mkw 0x060000000a850002 0x00c000000150a000 0x0000000003c78002 0x800000000078f000

def z344 : W := mkw 0x2005829000000000 0x0400b05200000000 0xbcff83f80c007c04 0x779ff07f01800f80

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x640000004000039c 0x0c80000008000073

def z346 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x882f03e00fc07f04 0xf105e07c01f80fe0

def z347 : W := mkw 0x10c0084340122090 0xc218010868024412 0xcf3858074036609f 0x39e70b00e806cc13

def z348 : W := mkw 0x50c26967c53a66d4 0xca184d2cf8a74cda 0xefb978e7c33e63ff 0xbdf72f1cf867cc7f

def z349 : W := mkw 0x38800bd7e01024c0 0x8710017afc020498 0x7c0803fff0007ce4 0x0f81007ffe000f9c

def z350 : W := mkw 0x35058afa4bc05b01 0x06a0b15f49780b60 0xffffdbff4fc07f04 0xfffffb7fe9f80fe0

def z351 : W := mkw 0x0080000100102080 0x8010000020020410 0xdd786007803870e5 0x7baf0c00f0070e1c

def z352 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x080003e700000000 0x0100007ce0000000

def z353 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xe7f7fc004fff839f 0xfcfeff8009fff073

def z354 : W := mkw 0x0000000000000000 0x0000000000000000 0x54000000800010e4 0x0a8000001000021c

def z355 : W := mkw 0x7ec7fff7efbf6296 0xcfd8fffefdf7ec52 0xffffffffffffe39f 0xfffffffffffffc73

def z356 : W := mkw 0x4007f40000000000 0x0800fe8000000000 0x0027580000000000 0x0004eb0000000000

def z357 : W := mkw 0x78c7ffd7e0122090 0xcf18fffafc024412 0x7ff7fffff036009b 0x0ffefffffe06c013

def z358 : W := mkw 0x7d07fffeebc05b01 0x0fa0ffffdd780b60 0x7ff7fffff3c00300 0x8ffefffffe780060

def z359 : W := mkw 0x0120000810409129 0x2024000102081225 0xb4d0801800c993ff 0xd69a10030019327f

def z360 : W := mkw 0x0120000810409129 0x2024000102081225 0x83d0a40000c993ff 0xd07a14800019327f

def z361 : W := mkw 0x0020000010008028 0x2004000002001005 0x40000000f00000f8 0x080000001e00001f

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0x0280840000c18002 0x8050108000183000

def z363 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6fb958e743366000 0x2df72b1ce866cc00

def z364 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x0000840000c18000 0x0000108000183000

def z365 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3c8983f803c07f04 0x8791307f00780fe0

def z366 : W := mkw 0x41a2610d9478b5ed 0xa8344c21b28f16bd 0xdd7e63078cf9ffff 0xfbafcc60f19f3fff

def z367 : W := mkw 0x4727f4081eed912f 0x28e4fe8103ddb225 0x83f7fc000fff93ff 0xf07eff8001fff27f

def z368 : W := mkw 0x40826125853866c4 0x88104c24b0a70cd8 0xfdff63e78f387fe5 0xffbfec7cf1e70ffc

def z369 : W := mkw 0x210002b801405b01 0x0420005700280b60 0xbcb903f803007f04 0xb797207f00600fe0

def z370 : W := mkw 0x072000081eed912f 0x20e4000103ddb225 0x800000000fff93ff 0xf000000001fff27f

def z371 : W := mkw 0x218003bd81507fc1 0x84300077b02a0ff8 0x7c0803ff80007fe4 0x0f81007ff0000ffc

def z372 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffa7f8ffc07f04 0xfffff4ff1ff80fe0

def z373 : W := mkw 0x210002b801405b01 0x0420005700280b60 0x200000f800000300 0x0400001f00000060

def z374 : W := mkw 0x4087f505843824c4 0x8810fea0b0870498 0xdfffff078c387ce5 0x7bffffe0f1870f9c

def z375 : W := mkw 0x3d058bfeebc05b01 0x07a0b17fdd780b60 0xfcff83ffffc07f04 0xff9ff07ffff80fe0

def z376 : W := mkw 0x0000000000000000 0x0000000000000000 0x34d0801800000000 0x069a100300000000

def z377 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x2aa7dfff70000000 0x0554fbffee000000

def z378 : W := mkw 0x0080000100102080 0x8010000020020410 0x4100400700300081 0x08200800e0060010

def z379 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xacb980f803c06304 0xb597301f00780c60

def z380 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x82f79c000fc78002 0xf05ef38001f8f000

def z381 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xc10860078c387ce5 0x78210c00f1870f9c

def z382 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x0000400700300000 0x00000800e0060000

def z383 : W := mkw 0x040580000a800000 0x0080b00001500000 0x002700000f000000 0x2004e00001e00000

def z384 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x000000000f360000 0x2000000001e6c000

def z385 : W := mkw 0x5647fc624faf4216 0x4ac8ff8c49f5e842 0xa3f7fce04fff831b 0xf47eff9c09fff063

def z386 : W := mkw 0x1000084240000000 0x0200010848000000 0x228118e040000000 0x0450231c08000000

def z387 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0x228184f873c1831a 0x8450309f0e783063

def z388 : W := mkw 0x0120000810409129 0x2024000102081225 0x76808418f0c193fe 0x8ed010831e18327f

def z389 : W := mkw 0x50c26967c53a66d4 0xca184d2cf8a74cda 0xfd7e63e7cc387ffd 0x7fafcc7cf9870fff

def z390 : W := mkw 0x25c582b90bd27b91 0xc4b8b057217a4f72 0xbcff83f80ff67f9f 0xf79ff07f01fecff3

def z391 : W := mkw 0x4407e0000ea80004 0x0880fc0001d50000 0x81f7e0000ff80001 0xf03efc0001ff0000

def z392 : W := mkw 0x0000002001004200 0x0000000400200840 0x082900e003006000 0x2105201c00600c00

def z393 : W := mkw 0x6087e395843824c4 0x8c10fc72b0870498 0xfdffe3ff8c387ce5 0x7fbffc7ff1870f9c

def z394 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5c2e43078c307ce4 0x2b85c860f1860f9c

def z395 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x882e43070c387ce5 0x7105c860e1870f9c

def z396 : W := mkw 0x00c00021053a66d4 0xc018000420a74cda 0x800800000f3e7fff 0xf001000001e7cfff

def z397 : W := mkw 0x0120000810409129 0x2024000102081225 0xd550200080c993ff 0xdaaa04001019327f

def z398 : W := mkw 0x040580000a800000 0x0080b00001500000 0x83f7a4000fc98003 0xf07ef48001f93000

def z399 : W := mkw 0x0000000004280444 0x0000000000850088 0x000000000c081c60 0x400000000181038c

def z400 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6f0858e74036639f 0x0de10b1ce806cc73

def z401 : W := mkw 0x31c00afb41527b91 0xc638015f682a4f72 0xffb95bff43367f9f 0xbff72b7fe866cff3

def z402 : W := mkw 0x10c00967c11266d0 0xc218012cf8224cda 0xffb95be7c3367fff 0xbff72b7cf866cfff

def z403 : W := mkw 0x75c7ebffcffa7fd5 0xceb8fd7ff9ff4ffa 0xfffffbffcffe7fff 0xffffff7ff9ffcfff

def z404 : W := mkw 0x7807fed260000000 0x0f00ffda4c000000 0x23f7fcf870000000 0x047eff9f0e000000

def z405 : W := mkw 0x42027400042d0006 0x08404e800085a000 0x0000580000360000 0x00000b000006c000

def z406 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x2aa958e74336631a 0xa5552b1ce866cc63

def z407 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x8bf7ffe70fff8003 0xf17efffce1fff000

def z408 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xec0800e74336639f 0xbd81001ce866cc73

def z409 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83d6a4000cc98003 0xd07ad48001993000

def z410 : W := mkw 0x0020000010008028 0x2004000002001005 0x020004007001801a 0x004000800e003003

def z411 : W := mkw 0x01e000291152f3b9 0xe03c0005222a5e77 0xf7d8a418f3fff3ff 0xfefb14831e7ffe7f

def z412 : W := mkw 0x0000000000000000 0x0000000000000000 0xd7d0a40080c990e7 0xdafa14801019321c

def z413 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xcd3e43070c306c85 0x39a7c860e1860d90

def z414 : W := mkw 0x38c00bf7e1126290 0xc718017efc224c52 0x7c0803fff000639c 0x0f81007ffe000c73

def z415 : W := mkw 0x240582900a800000 0x0480b05201500000 0xbcf783f80fc00000 0xf79ef07f01f80000

def z416 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xd5506007803810e5 0x5aaa0c00f007021c

def z417 : W := mkw 0x0000000000000000 0x0000000000000000 0x5550200080000000 0x0aaa040010000000

def z418 : W := mkw 0x56c7fc634fbf6296 0xcad8ff8c69f7ec52 0xefbf58e74f36639f 0xbdf7eb1ce9e6cc73

def z419 : W := mkw 0x4727f4081eed912f 0x28e4fe8103ddb225 0x1046a418bcc99060 0x4208d4831799320c

def z420 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x02a7dc000ff78002 0xa054fb8001fef000

def z421 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x882958e70336639f 0xb1052b1ce066cc73

def z422 : W := mkw 0x0080000100102080 0x8010000020020410 0x8008000000306085 0x3001000000060c10

def z423 : W := mkw 0x0020000010008028 0x2004000002001005 0xc3d0a400f0c980fb 0xd87a14801e19301f

def z424 : W := mkw 0x250002b80bc05b01 0x04a0005701780b60 0xbc0803f80fc07f04 0xf781007f01f80fe0

def z425 : W := mkw 0x0020000010008028 0x2004000002001005 0xe7902400f00983ff 0x9cf204801e01307f

def z426 : W := mkw 0x7c07ffd6ea800000 0x0f80fffadd500000 0xfff7ffffffc00000 0xfffefffffff80000

def z427 : W := mkw 0x1000084240000000 0x0200010848000000 0x6c0000e740000000 0x0d80001ce8000000

def z428 : W := mkw 0x0120000810409129 0x2024000102081225 0x0000841830c18000 0x0000108306183000

def z429 : W := mkw 0x0000000000000000 0x0000000000000000 0x80b1000003000000 0xb016200000600000

def z430 : W := mkw 0x460274000ead0006 0x08c04e8001d5a000 0x83007c000fff8003 0xf0600f8001fff000

def z431 : W := mkw 0x4687f5058ebd24c6 0x88d0fea0b1d7a498 0x082f5b070f366c00 0x2105eb60e1e6cd80

def z432 : W := mkw 0x10c00863453a66d4 0xc218010c68a74cda 0xefb958e74f3e7fff 0xfdf72b1ce9e7cfff

def z433 : W := mkw 0x50c7fc6341126290 0xca18ff8c68224c52 0xeffffce74336639f 0xbdffff9ce866cc73

def z434 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x02c7bc000fcf8002 0xc058f78001f9f000

def z435 : W := mkw 0x40a261059438a4ec 0xa8144c20b287149d 0xdf7e6707fc39fcff 0x7befcce0ff873f9f

def z436 : W := mkw 0x4002610484280444 0x08004c2090850088 0x917663008c381c61 0x722ecc601187038c

def z437 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x638158e74336039b 0x8c702b1ce866c073

def z438 : W := mkw 0x0000000000000000 0x0000000000000000 0x0021580003360000 0x20042b000066c000

def z439 : W := mkw 0x7927ffdef0409129 0x2f24fffbde081225 0x7ff7fffff00013fc 0x0ffefffffe00027f

def z440 : W := mkw 0x040580000a800000 0x0080b00001500000 0x004680000cc00000 0x4008d00001980000

def z441 : W := mkw 0x7887ffd7e43824c4 0x8f10fffafc870498 0x082f5be70c306c00 0x2105eb7ce1860d80

def z442 : W := mkw 0x1040086241024210 0x4208010c48204842 0x000118e003060000 0x0000231c0060c000

def z443 : W := mkw 0x0000002001004200 0x0000000400200840 0xafb958e003366307 0xb5f72b1c0066cc60

def z444 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6e8918e74306639e 0x8dd1231ce860cc73

def z445 : W := mkw 0x4182610d847835c5 0x88304c21b08f06b8 0xfdfee31f8cf87fe5 0xffbfdc63f19f0ffc

def z446 : W := mkw 0x0000002001004200 0x0000000400200840 0x208100e003000300 0x8410201c00600060

def z447 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7fb15bfff0000000 0x0ff62b7ffe000000

def z448 : W := mkw 0x0020000010008028 0x2004000002001005 0xd7502400f00990ff 0x5aea04801e01321f

def z449 : W := mkw 0x2125829810409129 0x2424b05302081225 0xfff7a7f8f0c993ff 0xdffef4ff1e19327f

def z450 : W := mkw 0x4002610480000000 0x08004c2090000000 0xdd7e63078c007c04 0x7bafcc60f1800f80

def z451 : W := mkw 0x78026bd6e0000000 0x0f004d7adc000000 0x7d7663fff0000000 0x0faecc7ffe000000

def z452 : W := mkw 0x0120000810409129 0x2024000102081225 0x9040a418b0c993ff 0xd20814831619327f

def z453 : W := mkw 0x0000000000000000 0x0000000000000000 0x8130400000300001 0x3026080000060000

def z454 : W := mkw 0x39000bfee1405b01 0x0720017fdc280b60 0x7c0803fff0007f04 0x0f81007ffe000fe0

def z455 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xa28918e04336639f 0xb451231c0866cc73

def z456 : W := mkw 0x10c0084340122090 0xc218010868024412 0x0000580700360000 0x00000b00e006c000

def z457 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03277c000f3f8003 0x2064ef8001e7f000

def z458 : W := mkw 0x0120000810409129 0x2024000102081225 0xd550a418b0c990e5 0x5aaa14831619321c

def z459 : W := mkw 0x6007e39480000000 0x0c00fc7290000000 0x7df7e3ff80000000 0x0fbefc7ff0000000

def z460 : W := mkw 0x058000290ff87fc5 0x80b0000521ff0ff8 0x800800000ff87fe5 0xf001000001ff0ffc

def z461 : W := mkw 0x7c07fff6eb804a00 0x0f80fffedd700940 0x082f5be70f006c00 0x2105eb7ce1e00d80

def z462 : W := mkw 0x38058bd6e0000000 0x0700b17adc000000 0x7cf783fff0000000 0x0f9ef07ffe000000

def z463 : W := mkw 0x39200bdef0409129 0x2724017bde081225 0xffd0a7fff0c993ff 0xdffa14fffe19327f

def z464 : W := mkw 0x7887ffd7e43824c4 0x8f10fffafc870498 0x7ffffffffc306c00 0x2fffffffff860d80

def z465 : W := mkw 0x0080002101106280 0x8010000420220c50 0xedb940e703306385 0xbdb7281ce0660c70

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0x1040a418b0000000 0x0208148316000000

def z467 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x802758000fff8003 0xf004eb0001fff000

def z468 : W := mkw 0x30058ad240000000 0x0600b15a48000000 0x7ff7dbff40000000 0x0ffefb7fe8000000

def z469 : W := mkw 0x0000000000000000 0x0000000000000000 0x41002000800800e1 0x082004001001001c

def z470 : W := mkw 0x35458afa4bc25b11 0x46a8b15f49784b62 0xbeff9bf84fc67f1e 0xf7dff37f09f8cfe3

def z471 : W := mkw 0x6507e39c8ee81d45 0x0ca0fc7391dd03a8 0x1046a3188cc81c60 0x4208d4631199038c

def z472 : W := mkw 0x052000281bc0db29 0x20a4000503781b65 0xf7d8a418ffc9ffff 0xfefb14831ff93fff

def z473 : W := mkw 0x7e07fed26ead0006 0x0fc0ffda4dd5a000 0xa3f7fcf87fff8003 0xf47eff9f0ffff000

def z474 : W := mkw 0x00800001001024c0 0x8010000020020498 0x0008000000007ce4 0x0001000000000f9c

def z475 : W := mkw 0x6607f6b00fad4a06 0x0cc0fed601f5a940 0x8bffffe00fffec03 0xf17ffffc01fffd80

def z476 : W := mkw 0x0000000000000000 0x0000000000000000 0x0281180003060002 0x805023000060c000

def z477 : W := mkw 0x16459c624b874212 0x42c8b38c4970e842 0x22819ce043c7831a 0x8450339c0878f063

def z478 : W := mkw 0x58c27d47e0122090 0xcb184fa8fc024412 0x43007c07f036009b 0x08600f80fe06c013

def z479 : W := mkw 0x6507f6b80bc05b01 0x0ca0fed701780b60 0xbffffff80fc07f04 0xf7ffffff01f80fe0

def z480 : W := mkw 0x6707f6b80fed5b07 0x0ce0fed701fdab60 0xbcffa7f80fc9ff04 0xf79ff4ff01f93fe0

def z481 : W := mkw 0x0100000800401101 0x0020000100080220 0xf7d0801840c0139f 0xdefa100308180273

def z482 : W := mkw 0x6807f794a4280444 0x0d00fef294850088 0x1046a718bc081c60 0x4208d4e31781038c

def z483 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x32c7bff8f0000000 0x0658f7ff1e000000

def z484 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d08630780387ce5 0x0ba10c60f0070f9c

def z485 : W := mkw 0x57e7fc6b5ffff3bf 0xeafcff8d6bfffe77 0xfffffcfffffff3ff 0xffffff9ffffffe7f

def z486 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x0001180003060000 0x000023000060c000

def z487 : W := mkw 0x0080000100102080 0x8010000020020410 0xcfb9580703366087 0xb9f72b00e066cc10

def z488 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x9c7e43070c307c04 0x738fc860e1860f80

def z489 : W := mkw 0x2105829800401101 0x0420b05300080220 0xbcf783f800c01304 0xd79ef07f00180260

def z490 : W := mkw 0x4082600104382084 0x88104c0020870410 0xcd7e60070c386085 0x79afcc00e1870c10

def z491 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbeff87f87fc1ff1e 0xf7dff0ff0ff83fe3

def z492 : W := mkw 0x5a027d46e42d0006 0x0b404fa8dc85a000 0x43007c07f03f8003 0x08600f80fe07f000

def z493 : W := mkw 0x468261058ebd24c6 0x88d04c20b1d7a498 0xdd7e63078ffffce7 0xfbafcc60f1ffff9c

def z494 : W := mkw 0x10e008435012a0b8 0xe21c01086a025417 0x43007c07f03f80fb 0x08600f80fe07f01f

def z495 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300580000360003 0x00600b000006c000

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x0300240000098003 0x0060048000013000

def z497 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xcd3958e703366085 0x39a72b1ce066cc10

def z498 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x83d1bc0003cf8003 0xd07a37800079f000

def z499 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7900018f00013ff 0x9ef200031e00027f

def z500 : W := mkw 0x210002b801405b01 0x0420005700280b60 0xbc7e03f80c007f04 0x778fc07f01800fe0

def z501 : W := mkw 0x56c7fc634fbf6296 0xcad8ff8c69f7ec52 0x8bfffce70fffe003 0xf17fff9ce1fffc00

def z502 : W := mkw 0x4687f5058ebd24c6 0x88d0fea0b1d7a498 0x8bffff070fffec03 0xf17fffe0e1fffd80

def z503 : W := mkw 0x4002610484280444 0x08004c2090850088 0xd55623008c081ce5 0x5aaac4601181039c

def z504 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xfdffa3f88fc87fe5 0xffbff47f11f90ffc

def z505 : W := mkw 0x39200bdef0409129 0x2724017bde081225 0x7c0003fff00013fc 0x0f80007ffe00027f

def z506 : W := mkw 0x0120000810409129 0x2024000102081225 0x32c0a418f0c9937a 0xc65814831e19326f

def z507 : W := mkw 0x34c58af34b926a90 0xc698b15e69724d52 0xefbf5be74f366f9f 0xbdf7eb7ce9e6cdf3

def z508 : W := mkw 0x78c7fff7e1126290 0xcf18fffefc224c52 0xefbf5be74336639f 0xbdf7eb7ce866cc73

def z509 : W := mkw 0x0000000000000000 0x0000000000000000 0x80d0800000c00000 0xd01a100000180000

def z510 : W := mkw 0x6927f79cb0409129 0x2d24fef396081225 0xf7d6a718f0c993ff 0xdefad4e31e19327f

def z511 : W := mkw 0x040000000a800000 0x0080000001500000 0x800000000fc00000 0xf000000001f80000

def z512 : W := mkw 0x30c58af341126290 0xc618b15e68224c52 0xffffdbff4336639f 0xbffffb7fe866cc73

def z513 : W := mkw 0x0120000810409129 0x2024000102081225 0x5340a418f0c990fb 0x4a6814831e19321f

def z514 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8176e4000cf98001 0x702edc80019f3000

def z515 : W := mkw 0x0000000000000000 0x0000000000000000 0xa490000000000304 0x9492000000000060

def z516 : W := mkw 0x0120000810409129 0x2024000102081225 0x77d0a418f0c99060 0x4efa14831e19320c

def z517 : W := mkw 0x58827d47e43824c4 0x8b104fa8fc870498 0x43007c07f03800e1 0x08600f80fe07001c

def z518 : W := mkw 0x0200140000050002 0x004002800000a000 0x02001c0000078002 0x004003800000f000

def z519 : W := mkw 0x0120000810409129 0x2024000102081225 0x77002418f00993ff 0x0ee004831e01327f

def z520 : W := mkw 0x0100002801405b01 0x0020000500280b60 0x0008000000007f04 0x0001000000000fe0

def z521 : W := mkw 0x4002610480000000 0x08004c2090000000 0x7ff6e71ff0000000 0x0ffedce3fe000000

def z522 : W := mkw 0x5007fc4240000000 0x0a00ff8848000000 0x6ff7fce740000000 0x0dfeff9ce8000000

def z523 : W := mkw 0x050000280bc05b01 0x00a0000501780b60 0xacb900e00fc07f04 0xf597201c01f80fe0

def z524 : W := mkw 0x42027400042d0006 0x08404e800085a000 0x83b17c00033f8003 0xb0762f800067f000

def z525 : W := mkw 0x4687f4010ebd2086 0x88d0fe8021d7a410 0xcffffc070fffe087 0xf9ffff80e1fffc10

def z526 : W := mkw 0x40826001043824c4 0x88104c0020870498 0x817e60000c387ce5 0x702fcc0001870f9c

def z527 : W := mkw 0x6707f6b80fed5b07 0x0ce0fed701fdab60 0xa3f7fcf80fff8303 0xf47eff9f01fff060

def z528 : W := mkw 0x6607f6b00fad4a06 0x0cc0fed601f5a940 0x082f5be00f366c00 0x2105eb7c01e6cd80

def z529 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x514663078c381ce1 0x4a28cc60f187039c

def z530 : W := mkw 0x4002610480000000 0x08004c2090000000 0x4100600780000000 0x08200c00f0000000

def z531 : W := mkw 0x5807fd46e0000000 0x0b00ffa8dc000000 0x43f7fc07f0000000 0x087eff80fe000000

def z532 : W := mkw 0x6807f794a0000000 0x0d00fef294000000 0x77d6a718f0000000 0x0efad4e31e000000

def z533 : W := mkw 0x618263bd85787fc5 0x8c304c77b0af0ff8 0xfd7e63ff8c387fe5 0x7fafcc7ff1870ffc

def z534 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x3cff83f80f006c00 0x279ff07f01e00d80

def z535 : W := mkw 0x41a2610d9478b5ed 0xa8344c21b28f16bd 0xf7d0e41ff0f993ff 0xdefa1c83fe1f327f

def z536 : W := mkw 0x2005829000000000 0x0400b05200000000 0x082703e000000000 0x0104e07c00000000

def z537 : W := mkw 0x0080000100102080 0x8010000020020410 0x4c08000700006084 0x09810000e0000c10

def z538 : W := mkw 0x040580000a800000 0x0080b00001500000 0x9cff83000fc07c04 0xf39ff06001f80f80

def z539 : W := mkw 0x0000000000000000 0x0000000000000000 0x9450000000001004 0x528a000000000200

def z540 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x83d0a4000fff8003 0xf07a148001fff000

def z541 : W := mkw 0x250582980ac01901 0x04a0b05301580320 0x0000801800c00000 0x0000100300180000

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0xe7d0a40040c9839f 0xdcfa148008193073

def z543 : W := mkw 0x6487e3b58fb86ec4 0x8c90fc76b1f70dd8 0x082f43e70f306c00 0x2105e87ce1e60d80

def z544 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x5d777be780000000 0x0baeef7cf0000000

def z545 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x904e23008c387ce5 0x7209c46011870f9c

def z546 : W := mkw 0x58227d46f0008028 0x2b044fa8de001005 0x43007c07f00980fb 0x08600f80fe01301f

def z547 : W := mkw 0x52c27c43443f2096 0xca584f886887e412 0x43007c07403f809b 0x08600f80e807f013

def z548 : W := mkw 0x050000280bc05b01 0x00a0000501780b60 0x9c7e03000fc07f04 0xf38fc06001f80fe0

def z549 : W := mkw 0x412260081468912d 0x28244c01028d1225 0xf7f6e418fcf993ff 0xfefedc831f9f327f

def z550 : W := mkw 0x0020000010008028 0x2004000002001005 0x00002400b0098060 0x000004801601300c

def z551 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x30c783f80fc01f00 0xc618f07f01f803e0

def z552 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfcff83f8ffc07ffc 0xff9ff07f1ff80fff

def z553 : W := mkw 0x7887ffd7e43824c4 0x8f10fffafc870498 0xdd7f7be78c387ce5 0x7bafef7cf1870f9c

def z554 : W := mkw 0x35458afa4bc25b11 0x46a8b15f49784b62 0x228198f843c6031a 0x8450331f0878c063

def z555 : W := mkw 0x0040002001024210 0x4008000400204842 0x000000000306031a 0x800000000060c063

def z556 : W := mkw 0x58827d47e43824c4 0x8b104fa8fc870498 0xdf7e7f07fc387ce5 0x7befcfe0ff870f9c

def z557 : W := mkw 0x00800105801024c0 0x80100020b0020498 0x0808030700006c00 0x01010060e0000d80

def z558 : W := mkw 0x42227400142d802e 0x28444e800285b005 0x43007c00f03f80fb 0x08600f801e07f01f

def z559 : W := mkw 0x250582980ac01901 0x04a0b05301580320 0x3cf783f80cc01c00 0x479ef07f01980380

def z560 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03f7fc000cc98000 0x407eff8001993000

def z561 : W := mkw 0x1160086a5142d339 0x622c010d4a285a67 0x22819cf873c7831a 0x8450339f0e78f063

def z562 : W := mkw 0x012000281140d329 0x2024000502281a65 0xfff9a4f8f3c9f3ff 0xffff349f1e793e7f

def z563 : W := mkw 0x00800001043824c4 0x8010000020870498 0xcd3840070c387ce5 0x79a70800e1870f9c

def z564 : W := mkw 0x050000280bc05b01 0x00a0000501780b60 0x0000000003c00300 0x8000000000780060

def z565 : W := mkw 0x4407f4000a800000 0x0880fe8001500000 0x83f7fc000fc00000 0xf07eff8001f80000

def z566 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xa0f780f80fc00300 0xf41ef01f01f80060

def z567 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x4b277fe7f0000000 0x0964effcfe000000

def z568 : W := mkw 0x252582981ac09929 0x24a4b05303581325 0x1046a718bcc99c60 0x4208d4e31799338c

def z569 : W := mkw 0x1040086241024210 0x4208010c48204842 0x200000e040000318 0x0400001c08000063

def z570 : W := mkw 0x56c7fc634fbf6296 0xcad8ff8c69f7ec52 0x082f58e70f366000 0x2105eb1ce1e6cc00

def z571 : W := mkw 0x0100000800401101 0x0020000100080220 0xf7d0a418f0c01304 0xdefa14831e180260

def z572 : W := mkw 0x79a7ffdff478b5ed 0xaf34fffbfe8f16bd 0xfffffffffcf9ffff 0xffffffffff9f3fff

def z573 : W := mkw 0x050580080ac01101 0x00a0b00101580220 0xb4f780180fc01304 0xf69ef00301f80260

def z574 : W := mkw 0x4082610580102080 0x88104c20b0020410 0xdd7e630780306085 0x3bafcc60f0060c10

def z575 : W := mkw 0x0120000810409129 0x2024000102081225 0xe790000040c993ff 0xdcf200000819327f

def z576 : W := mkw 0x7887ffd7e01024c0 0x8f10fffafc020498 0x7ffffffff0007ce4 0x0ffffffffe000f9c

def z577 : W := mkw 0x15c0086b4bd27b91 0xc2b8010d697a4f72 0xefb958e74ff67f9f 0xfdf72b1ce9fecff3

def z578 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000c98003 0xd000000000193000

def z579 : W := mkw 0x00c0002101126290 0xc018000420224c52 0xcd3840070336639f 0xb9a70800e066cc73

def z580 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x5346ff1ff0000000 0x0a68dfe3fe000000

def z581 : W := mkw 0x0000000000000000 0x0000000000000000 0x4d30400700000000 0x09a60800e0000000

def z582 : W := mkw 0x01a000091050b1a9 0xa0340001220a1635 0xfff8e41ff0f9f3ff 0xffff1c83fe1f3e7f

def z583 : W := mkw 0x6507e3bc8fe85f45 0x0ca0fc7791fd0be8 0xbcffa3f88fc87f64 0xf79ff47f11f90fec

def z584 : W := mkw 0x4007f50480000000 0x0800fea090000000 0x5ff7ff0780000000 0x0bfeffe0f0000000

def z585 : W := mkw 0x0120000810409129 0x2024000102081225 0x77d0a418f0c1831a 0x8efa14831e183063

def z586 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83b758000f360003 0xb076eb0001e6c000

def z587 : W := mkw 0x00c0002101126290 0xc018000420224c52 0xe79800004336639f 0xbcf300000866cc73

def z588 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000003360003 0xb00000000066c000

def z589 : W := mkw 0x7807fff6e1004200 0x0f00fffedc200840 0xfffffffff3006304 0xbffffffffe600c60

def z590 : W := mkw 0x0000000000000000 0x0000000000000000 0x03d0a40000000000 0x007a148000000000

def z591 : W := mkw 0x0000002001004200 0x0000000400200840 0x8008000003006304 0xb001000000600c60

def z592 : W := mkw 0x6807f794a0000000 0x0d00fef294000000 0x0006030000000000 0x0000c06000000000

def z593 : W := mkw 0x41a2610d9478b5ed 0xa8344c21b28f16bd 0xdd7ee71fbcf9fce5 0x7bafdce3f79f3f9c

def z594 : W := mkw 0x6707f6980eed1907 0x0ce0fed301dda320 0x93f7ff180fff9c03 0xf27effe301fff380

def z595 : W := mkw 0x0120000810409129 0x2024000102081225 0x6380a418f0c983fb 0x8c7014831e19307f

def z596 : W := mkw 0x00800105801024c0 0x80100020b0020498 0x40000007800000e0 0x08000000f000001c

def z597 : W := mkw 0x58c27d67e1126290 0xcb184facfc224c52 0xefb97ce7f336639f 0xbdf72f9cfe66cc73

def z598 : W := mkw 0x0120000810409129 0x2024000102081225 0xf4000018f0c993ff 0xde8000031e19327f

def z599 : W := mkw 0x00800105801024c0 0x80100020b0020498 0xdd58230780087ce5 0x5bab0460f0010f9c

def z600 : W := mkw 0x10c0084340122090 0xc218010868024412 0xc3b158074336009b 0xb8762b00e866c013

def z601 : W := mkw 0x1080084340102080 0x8210010868020410 0xefb958e740306085 0x3df72b1ce8060c10

def z602 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0xffb958fff33673ff 0xbff72b1ffe66ce7f

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x80000000000810e5 0x500000000001021c

def z604 : W := mkw 0x0100000800401101 0x0020000100080220 0xbcfe83180cc07f04 0xf79fd06301980fe0

def z605 : W := mkw 0x4582612d8ff87fc5 0x88b04c25b1ff0ff8 0xdd7e63078ff87fe5 0xfbafcc60f1ff0ffc

def z606 : W := mkw 0x11e0084b5052b1b9 0xe23c01096a0a5637 0xf7d0fc1ff0ff93ff 0xdefa1f83fe1ff27f

def z607 : W := mkw 0x4122610c9468956d 0x28244c21928d12ad 0xf7d6a718fcc99fff 0xdefad4e31f9933ff

def z608 : W := mkw 0x1040086241024210 0x4208010c48204842 0xaeb918e04306631e 0xb5d7231c0860cc63

def z609 : W := mkw 0x10c00967c11266d0 0xc218012cf8224cda 0x7c0803e7c0007ffc 0x0f81007cf8000fff

def z610 : W := mkw 0x0120000810409129 0x2024000102081225 0x7440a418f0c993fc 0x4e8814831e19327f

def z611 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x83b1dc0003f78003 0xb0763b80007ef000

def z612 : W := mkw 0x0120000810409129 0x2024000102081225 0x77d0a418f00013fc 0x0efa14831e00027f

def z613 : W := mkw 0x0000000000000000 0x0000000000000000 0x74000018f0000000 0x0e8000031e000000

def z614 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xcd386007803860e5 0x39a70c00f0070c1c

def z615 : W := mkw 0x02000000042d0006 0x004000000085a000 0x00000000003f8003 0x000000000007f000

def z616 : W := mkw 0x0020000010008028 0x2004000002001005 0x00000000000980fb 0x000000000001301f

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c38000000006004 0x3187000000000c00

def z618 : W := mkw 0x1000084240000000 0x0200010848000000 0x082158e700000000 0x01042b1ce0000000

def z619 : W := mkw 0x11c0086b41527391 0xc238010d682a4e72 0xfff9d8ff43f6739f 0xffff3b1fe87ece73

def z620 : W := mkw 0x7d07fffeebc05b01 0x0fa0ffffdd780b60 0xbcffdbff0fc07f04 0xf79ffb7fe1f80fe0

def z621 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x0346fc000cff8003 0x4068df80019ff000

def z622 : W := mkw 0x0100000800401101 0x0020000100080220 0x1040801800c01000 0x4208100300180200

def z623 : W := mkw 0x4002610480000000 0x08004c2090000000 0xdd766307800810e5 0x5baecc60f001021c

def z624 : W := mkw 0x28000394a0000000 0x0500007294000000 0x10000318b0000000 0x0200006316000000

def z625 : W := mkw 0x50c26947c43a24d4 0xca184d28f887449a 0xdf7e7b07cc3e7cff 0x7befcf60f987cf9f

def z626 : W := mkw 0x6587e39d8ef83dc5 0x8cb0fc73b1df07b8 0xdd7ee31f8cf87ce5 0x7bafdc63f19f0f9c

def z627 : W := mkw 0x0000000000000000 0x0000000000000000 0x800800000c007c04 0x7001000001800f80

def z628 : W := mkw 0x460260000ead0006 0x08c04c0001d5a000 0x817660000fff8003 0xf02ecc0001fff000

def z629 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03f7fc000f360000 0x207eff8001e6c000

def z630 : W := mkw 0x200582b001004200 0x0400b05600200840 0xbcff83f803006304 0xb79ff07f00600c60

def z631 : W := mkw 0x270582b80fed5b07 0x04e0b05701fdab60 0xbcff83f80fffff07 0xf79ff07f01ffffe0

def z632 : W := mkw 0x7927ffdef0409129 0x2f24fffbde081225 0x7ff7fffff0c1831a 0x8ffefffffe183063

def z633 : W := mkw 0x58027d46e0000000 0x0b004fa8dc000000 0x5f767f07f0000000 0x0beecfe0fe000000

def z634 : W := mkw 0x258582b90ff87fc5 0x84b0b05721ff0ff8 0xbcff83f80ff87fe5 0xf79ff07f01ff0ffc

def z635 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xf7d1a4f8f3c993ff 0xdefa349f1e79327f

def z636 : W := mkw 0x210582b801405b01 0x0420b05700280b60 0x3cff83f800007f04 0x079ff07f00000fe0

def z637 : W := mkw 0x7c07fff6eb804a00 0x0f80fffedd700940 0x7fffffffff006c00 0x2fffffffffe00d80

def z638 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0xffd8a4fff0c9f3ff 0xdffb149ffe193e7f

def z639 : W := mkw 0x4607f5048ead0446 0x08c0fea091d5a088 0x1046a7008cc99c60 0x4208d4e01199338c

def z640 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xed3840e74030639d 0x3da7081ce8060c73

def z641 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0x7c0800fff00073fc 0x0f81001ffe000e7f

def z642 : W := mkw 0x0000002001004200 0x0000000400200840 0x2c0800e000006304 0x0581001c00000c60

def z643 : W := mkw 0x0120000810409129 0x2024000102081225 0x10000018b0001060 0x020000031600020c

def z644 : W := mkw 0x78c7fff7e53a66d4 0xcf18fffefca74cda 0xffffffffff3e7fff 0xffffffffffe7cfff

def z645 : W := mkw 0x06c000210fbf6296 0xc0d8000421f7ec52 0x800800000fffe39f 0xf001000001fffc73

def z646 : W := mkw 0x4002610480000000 0x08004c2090000000 0x0826430700000000 0x0104c860e0000000

def z647 : W := mkw 0x16c59c634b976292 0xc2d8b38c6972ec52 0xefb9dce743f7e39f 0xbdf73b9ce87efc73

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x8150200000080001 0x502a040000010000

def z649 : W := mkw 0x0000000000000000 0x0000000000000000 0x807600000c000000 0x700ec00001800000

def z650 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xc17660078c3800e1 0x782ecc00f187001c

def z651 : W := mkw 0x0120000810409129 0x2024000102081225 0xc3002400f0c993ff 0xd86004801e19327f

def z652 : W := mkw 0x48027504a0000000 0x09004ea094000000 0x00002400b0000000 0x0000048016000000

def z653 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xb4d180f803c01304 0xd69a301f00780260

def z654 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000000039f 0x9000000000000073

def z655 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x80f7d8000ff60000 0xf01efb0001fec000

def z656 : W := mkw 0x6507e3bc8bc05b01 0x0ca0fc7791780b60 0xfdffe3ff8fc07f04 0xffbffc7ff1f80fe0

def z657 : W := mkw 0x6707f6b80fed5b07 0x0ce0fed701fdab60 0xbcffdbf80ff67f04 0xf79ffb7f01fecfe0

def z658 : W := mkw 0x3d059efa6bc05b01 0x07a0b3df4d780b60 0x22819cf873c00300 0x8450339f0e780060

def z659 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6fb958e74000639c 0x0df72b1ce8000c73

def z660 : W := mkw 0x0000000000000000 0x0000000000000000 0xc510000000000085 0x18a2000000000010

def z661 : W := mkw 0x6927f79cb0409129 0x2d24fef396081225 0x1046a718b0c99060 0x4208d4e31619320c

def z662 : W := mkw 0x040580000a800000 0x0080b00001500000 0x83f7d8000ff60003 0xf07efb0001fec000

def z663 : W := mkw 0x270596b80bc55b03 0x04e0b2d70178ab60 0x22819cf803c78302 0x8450339f0078f060

def z664 : W := mkw 0x42027400042d0006 0x08404e800085a000 0x83767c000c3f8003 0x706ecf800187f000

def z665 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xecb900e74300639c 0xbd97201ce8600c73

def z666 : W := mkw 0x1000086241004200 0x0200010c48200840 0xefb958e743006304 0xbdf72b1ce8600c60

def z667 : W := mkw 0x42027400042d0006 0x08404e800085a000 0x0000240000098000 0x0000048000013000

def z668 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040a40000c98000 0x4008148000193000

def z669 : W := mkw 0x6587e3bd8ff87fc5 0x8cb0fc77b1ff0ff8 0xbcffc3ff0ff07f04 0xf79ff87fe1fe0fe0

def z670 : W := mkw 0x0120000810409129 0x2024000102081225 0xf4d08018f0c013fc 0xde9a10031e18027f

def z671 : W := mkw 0x4002610484280444 0x08004c2090850088 0x000603000c000c00 0x0000c06001800180

def z672 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x8bb958e703366003 0xb1772b1ce066cc00

def z673 : W := mkw 0x2100029800401901 0x0420005300080320 0x1000031800001c00 0x0200006300000380

def z674 : W := mkw 0x01a000091478b5ed 0xa0340001228f16bd 0xf7d8a418fcf9ffff 0xfefb14831f9f3fff

def z675 : W := mkw 0x0120000810409129 0x2024000102081225 0x93d0a418b0c99063 0xd27a14831619320c

def z676 : W := mkw 0x50c26967c1126290 0xca184d2cf8224c52 0xffff7be7c336639f 0xbfffef7cf866cc73

def z677 : W := mkw 0x50c26863453a6294 0xca184d0c68a74c52 0xefff78e74f3e639f 0xfdffef1ce9e7cc73

def z678 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x4b2958e74336609b 0x29652b1ce866cc13

def z679 : W := mkw 0x05c000290bd27b91 0xc0b80005217a4f72 0x800800000ff67f9f 0xf001000001fecff3

def z680 : W := mkw 0x01a0010d9050b5e9 0xa0340021b20a16bd 0x7c08031ff0007ffc 0x0f810063fe000fff

def z681 : W := mkw 0x250582980ac01901 0x04a0b05301580320 0x9c7e83180cc07c04 0x738fd06301980f80

def z682 : W := mkw 0x7847fff6e1024210 0x4f08fffedc204842 0x7ff7fffff306031a 0x8ffefffffe60c063

def z683 : W := mkw 0x1160086a5142d339 0x622c010d4a285a67 0xf7d1bcf8f3cf93ff 0xdefa379f1e79f27f

def z684 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x000118e000000000 0x0000231c00000000

def z685 : W := mkw 0x50c26967c53a66d4 0xca184d2cf8a74cda 0xefbf5be74f366f9f 0xbdf7eb7ce9e6cdf3

def z686 : W := mkw 0x4002610480000000 0x08004c2090000000 0x1046230080000000 0x0208c46010000000

def z687 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3cf783f803c00300 0x879ef07f00780060

def z688 : W := mkw 0x0100002801405301 0x0020000500280a60 0xbcf980f803c07304 0xf79f301f00780e60

def z689 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xef9800e74000639f 0x9df3001ce8000c73

def z690 : W := mkw 0x1040084240020010 0x4208010848004002 0x020018004006001a 0x004003000800c003

def z691 : W := mkw 0x78c7fff7e1126290 0xcf18fffefc224c52 0x7ffffffff000639c 0x0ffffffffe000c73

def z692 : W := mkw 0x35c58afb4bd27b91 0xc6b8b15f697a4f72 0xbcffdbff0ff67f04 0xf79ffb7fe1fecfe0

def z693 : W := mkw 0x040580000a800000 0x0080b00001500000 0x0081800003c00000 0x8010300000780000

def z694 : W := mkw 0x7907ffdee0401101 0x0f20fffbdc080220 0xfff7fffff0c01304 0xdffefffffe180260

def z695 : W := mkw 0x6807f794a0000000 0x0d00fef294000000 0x5d76e71fb0000000 0x0baedce3f6000000

def z696 : W := mkw 0x7907fffee1405b01 0x0f20ffffdc280b60 0x7ffffffff0007f04 0x0ffffffffe000fe0

def z697 : W := mkw 0x6d07f79caac01901 0x0da0fef395580320 0x1046a718bcc01c00 0x4208d4e317980380

def z698 : W := mkw 0x0120000810409129 0x2024000102081225 0x0000000000c99060 0x400000000019320c

def z699 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x817778000f3e0001 0x702eef0001e7c000

def z700 : W := mkw 0x01a0010d9050b5e9 0xa0340021b20a16bd 0xffd8a71ff0c9ffff 0xdffb14e3fe193fff

def z701 : W := mkw 0x4122610c90409129 0x28244c2192081225 0xfff6e71ff0c993ff 0xdffedce3fe19327f

def z702 : W := mkw 0x7927ffdef0409129 0x2f24fffbde081225 0x7ff7fffff0c99060 0x4ffefffffe19320c

def z703 : W := mkw 0x56c7fd67cfbf66d6 0xcad8ffacf9f7ecda 0xffffffe7cfffffff 0xfffffffcf9ffffff

def z704 : W := mkw 0x78c7fff7e1126290 0xcf18fffefc224c52 0x082f5be703366000 0x2105eb7ce066cc00

def z705 : W := mkw 0x10c0084340122090 0xc218010868024412 0x6fb158e74036009b 0x0df62b1ce806c013

def z706 : W := mkw 0x00800105843824c4 0x80100020b0870498 0xdc0803078c387ce5 0x7b810060f1870f9c

def z707 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xcd3958e70336639f 0xb9a72b1ce066cc73

def z708 : W := mkw 0x630276b8056d5b07 0x0c604ed700adab60 0x3f087ff8003fff07 0x07e10fff0007ffe0

def z709 : W := mkw 0x1040086241024210 0x4208010c48204842 0xefb158e74336031b 0xbdf62b1ce866c063

def z710 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfcff83f8ffc9ffff 0xff9ff07f1ff93fff

def z711 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffa7f84fc9ff9f 0xfffff4ff09f93ff3

def z712 : W := mkw 0x4607f5048ead0006 0x08c0fea091d5a000 0x8bf7ff070fff8003 0xf17effe0e1fff000

def z713 : W := mkw 0x38859ed3643824c4 0x8710b3da6c870498 0xa2899cf87c387ce5 0x7451339f0f870f9c

def z714 : W := mkw 0x5007fc4240000000 0x0a00ff8848000000 0x7ff7fcfff0000000 0x0ffeff9ffe000000

def z715 : W := mkw 0x1000084240000000 0x0200010848000000 0xefb158e74336039f 0xbdf62b1ce866c073

def z716 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x897e63070c387ce5 0x712fcc60e1870f9c

def z717 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd5e23078c087ce5 0x5babc460f1810f9c

def z718 : W := mkw 0x4607f4000a850002 0x08c0fe800150a000 0x83f7fc0003f78003 0xb07eff80007ef000

def z719 : W := mkw 0x38058bd6e0000000 0x0700b17adc000000 0x7ff7a7fff0000000 0x0ffef4fffe000000

def z720 : W := mkw 0x78027fd6e0000000 0x0f004ffadc000000 0x7c005bfff0000000 0x0f800b7ffe000000

def z721 : W := mkw 0x060014000ead0006 0x00c0028001d5a000 0x82001c000fff8003 0xf040038001fff000

def z722 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff00010e4 0x0ffefffffe00021c

def z723 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x6fb1fcfff0000000 0x0df63f9ffe000000

def z724 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff978e7c336639f 0xbfff2f1cf866cc73

def z725 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfcffa7f8ffc9fffc 0xff9ff4ff1ff93fff

def z726 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff000009b 0x0ffefffffe000013

def z727 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xd7f7fc008fff8003 0xfafeff8011fff000

def z728 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0c990e7 0xdffefffffe19321c

def z729 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7c215bfff0000000 0x0f842b7ffe000000

def z730 : W := mkw 0x00c0002101126290 0xc018000420224c52 0xf7d8a418f336639f 0xbefb14831e66cc73

def z731 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0000003 0x9ffefffffe000000

def z732 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7cd083fff0000000 0x0f9a107ffe000000

def z733 : W := mkw 0x35c58adb4ad23991 0xc6b8b15b695a4732 0x5346db1f4cf61c9b 0x4a68db63e99ec393

def z734 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x88bf03e00f006c00 0xb117e07c01e00d80

def z735 : W := mkw 0x58826947e43824c4 0x8b104d28fc870498 0x41006007f03800e1 0x08200c00fe07001c

def z736 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbfffa7f80fc9ffff 0xf7fff4ff01f93fff

def z737 : W := mkw 0x7e07ffd6ea850002 0x0fc0fffadd50a000 0x7ff7fffff3060000 0x0ffefffffe60c000

def z738 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcff83f87fc07f1c 0xf79ff07f0ff80fe3

def z739 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x9c7f03e00fc07f04 0xf38fe07c01f80fe0

def z740 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x88ff83e00fc07f04 0xf11ff07c01f80fe0

def z741 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff958e74336739f 0xffff2b1ce866ce73

def z742 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7ffffff3f8003 0x2ffeffffffe7f000

def z743 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x887f03e00f006c00 0x710fe07c01e00d80

def z744 : W := mkw 0x3d259efa7bc0db29 0x27a4b3df4f781b65 0x22819cf873c1831a 0x8450339f0e783063

def z745 : W := mkw 0x7e07ffd6ea850002 0x0fc0fffadd50a000 0xfff7fffff3cf8003 0xdffefffffe79f000

def z746 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x082e43070c387c60 0x6105c860e1870f8c

def z747 : W := mkw 0x3c058bd6ea800000 0x0780b17add500000 0xfcf783ffffc00000 0xff9ef07ffff80000

def z748 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0x1869fcffb3fff060 0x630d3f9ff67ffe0c

def z749 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x7fb1dffff0000000 0x0ff63bfffe000000

def z750 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x2281dcff70000000 0x04503b9fee000000

def z751 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7d777bfff0000000 0x0faeef7ffe000000

def z752 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdc7e23078c087ce4 0x7b8fc460f1810f9c

def z753 : W := mkw 0x068595058a9524c2 0x80d0b2a0b152a498 0x5e899f0783c7fce6 0x8bd133e0f078ff9c

def z754 : W := mkw 0x78027fd6e0000000 0x0f004ffadc000000 0x7f767ffff0000000 0x0feecffffe000000

def z755 : W := mkw 0x50c26947c43a24d4 0xca184d28f887449a 0x41007807803e00e1 0x08200f00f007c01c

def z756 : W := mkw 0x38000ad260000000 0x0700015a4c000000 0x6c0000ff70000000 0x0d80001fee000000

def z757 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03f7fc0003ff8003 0x807eff80007ff000

def z758 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xc3f7fc008fff80e3 0xf87eff8011fff01c

def z759 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x2c2f03e00f006f04 0x2585e07c01e00de0

def z760 : W := mkw 0x50e26947d43aa4fc 0xea1c4d28fa87549f 0x43007c07f03f80fb 0x08600f80fe07f01f

def z761 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff0c98000 0x4ffefffffe193000

def z762 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7fffffff78002 0xaffefffffffef000

def z763 : W := mkw 0x7a07ffd6e42d0006 0x0f40fffadc85a000 0xfff7fffffc3f8003 0x7ffeffffff87f000

def z764 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x28af83f80f006c00 0x2515f07f01e00d80

def z765 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x93f7fc18bfff8003 0xf27eff8317fff000

def z766 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xddfee3078cf87ce5 0xfbbfdc60f19f0f9c

def z767 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8ffffc000fffe007 0xf1ffff8001fffc00

def z768 : W := mkw 0x242582b01b80ca28 0x2484b05603701945 0x4b2f27e0ff09ecfb 0x2965e4fc1fe13d9f

def z769 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8bffff000fffec03 0xf17fffe001fffd80

def z770 : W := mkw 0x2d0596b82bc05b01 0x05a0b2d705780b60 0xbcff87f83fc07f04 0xf79ff0ff07f80fe0

def z771 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbc7e83f80cc07f04 0x778fd07f01980fe0

def z772 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7d0a418f3ff93ff 0xfefa14831e7ff27f

def z773 : W := mkw 0x56c7fc634fbf6296 0xcad8ff8c69f7ec52 0x6c4ea4e74cc9e39c 0x4d89d49ce9993c73

def z774 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbdffc3f80ff07f05 0xf7bff87f01fe0fe0

def z775 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x282958e743366318 0x25052b1ce866cc63

def z776 : W := mkw 0x7807ffd6e4280444 0x0f00fffadc850088 0x7ff7fffffc000c00 0x0ffeffffff800180

def z777 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0300001 0x3ffefffffe060000

def z778 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0xfffffffffc387c05 0x7fffffffff870f80

def z779 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbeff83f84fc07f1e 0xf7dff07f09f80fe3

def z780 : W := mkw 0x78027fd6e0000000 0x0f004ffadc000000 0x7fd0fffff0000000 0x0ffa1ffffe000000

def z781 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x186f03e00f007c00 0x630de07c01e00f80

def z782 : W := mkw 0x0080000100102080 0x8010000020020410 0xdd7e63078c387ce5 0x7bafcc60f1870f9c

def z783 : W := mkw 0x7927ffdef0409129 0x2f24fffbde081225 0x88275be700c993ff 0xd104eb7ce019327f

def z784 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x0281dc0003f78002 0x80503b80007ef000

def z785 : W := mkw 0x40c26105843a24d4 0xc8184c20b087449a 0xdd7e63078c3e7cff 0x7bafcc60f187cf9f

def z786 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6fb958e74336639c 0x2df72b1ce866cc73

def z787 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0x7c4ea7f8fcc9fffc 0x4f89d4ff1f993fff

def z788 : W := mkw 0x4727f4081eed912f 0x28e4fe8103ddb225 0x74275818ff3613fc 0x2e84eb031fe6c27f

def z789 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7f0027fff0000000 0x0fe004fffe000000

def z790 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0001004 0x5ffefffffe000200

def z791 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xfdffa3f88fc07f04 0xffbff47f11f80fe0

def z792 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x9c7e63078c387c64 0x738fcc60f1870f8c

def z793 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83b1fc0003ff8003 0xb0763f80007ff000

def z794 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x82819c0003f78003 0xb0503380007ef000

def z795 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7fffffc000000 0x0ffeffffff800000

def z796 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdc7e43078c307ce4 0x7b8fc860f1860f9c

def z797 : W := mkw 0x41a2610d9478b5ed 0xa8344c21b28f16bd 0x2aaec71f7cf1ef1a 0xa555d8e3ef9e3de3

def z798 : W := mkw 0x3e059fd6ea850002 0x07c0b3fadd50a000 0x7e819ffff3c78002 0x8fd033fffe78f000

def z799 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7fffffcc98003 0xdffeffffff993000

def z800 : W := mkw 0x0120000810409129 0x2024000102081225 0x77d0a418f0c983fb 0x8efa14831e19307f

def z801 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x83f1fc000fff8003 0xf07e3f8001fff000

def z802 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x280003ff70000000 0x0500007fee000000

def z803 : W := mkw 0x2005829000000000 0x0400b05200000000 0xffffa7f8fc087ce5 0x7ffff4ff1f810f9c

def z804 : W := mkw 0x78027fd6e0000000 0x0f004ffadc000000 0x7fb17ffff0000000 0x0ff62ffffe000000

def z805 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xc7f7fc000fff8087 0xf8feff8001fff010

def z806 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3c6f83f80fc07f04 0x678df07f01f80fe0

def z807 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7fb75bfff0000000 0x0ff6eb7ffe000000

def z808 : W := mkw 0x0120000810409129 0x2024000102081225 0x7780a418f0c993ff 0x8ef014831e19327f

def z809 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xabb958e74336631b 0xb5772b1ce866cc63

def z810 : W := mkw 0x270596b80bc55b03 0x04e0b2d70178ab60 0xbfffdff80ff7ff07 0xf7fffbff01feffe0

def z811 : W := mkw 0x3e000bd6eead0006 0x07c0017addd5a000 0xfc0003ffffff8003 0xff80007ffffff000

def z812 : W := mkw 0x210002b801405b01 0x0420005700280b60 0xbcfe83f80cc07f04 0xf79fd07f01980fe0

def z813 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x3c2f03f80f006c00 0x2785e07f01e00d80

def z814 : W := mkw 0x05e000291bd2fbb9 0xe0bc0005237a5f77 0x800800000fffffff 0xf001000001ffffff

def z815 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfffee71ffcf9fce7 0xffffdce3ff9f3f9c

def z816 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xacbf83f80fc06f04 0xb597f07f01f80de0

def z817 : W := mkw 0x6007e39480000000 0x0c00fc7290000000 0x7ff7e7fff0000000 0x0ffefcfffe000000

def z818 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x2a819fff70000000 0x055033ffee000000

def z819 : W := mkw 0x50c26947c43a24d4 0xca184d28f887449a 0x41006007c03800f9 0x08200c00f807001f

def z820 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfeff87f8ffc1fffe 0xffdff0ff1ff83fff

def z821 : W := mkw 0x35658afa5bc2db39 0x66acb15f4b785b67 0x22819cf873c7831a 0x8450339f0e78f063

def z822 : W := mkw 0x0120000810409129 0x2024000102081225 0xfff1a4f8f0c993ff 0xdffe349f1e19327f

def z823 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7fffff3ff8003 0x8ffefffffe7ff000

def z824 : W := mkw 0x210002b801405b01 0x0420005700280b60 0x3c4e03f80c007f04 0x4789c07f01800fe0

def z825 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x9bf7ffffbfff8003 0xf37efffff7fff000

def z826 : W := mkw 0x59a27d4ff478b5ed 0xab344fa9fe8f16bd 0xf7d0fc1ff0f993ff 0xdefa1f83fe1f327f

def z827 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7d0fc18f0ff93ff 0xdefa1f831e1ff27f

def z828 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcde83f80cc07f04 0xd79bd07f01980fe0

def z829 : W := mkw 0x10c00863411266d0 0xc218010c68224cda 0xefb958e743367fff 0xbdf72b1ce866cfff

def z830 : W := mkw 0x7a07ffd6e42d0006 0x0f40fffadc85a000 0x7ff7fffff0360000 0x0ffefffffe06c000

def z831 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7fffffcf98001 0x7ffeffffff9f3000

def z832 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xdd7f23e08f087ce5 0x7bafe47c11e10f9c

def z833 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x882f03e00f006f04 0xb105e07c01e00de0

def z834 : W := mkw 0x7a07ffd6e42d0006 0x0f40fffadc85a000 0xfff7fffff0ff8003 0xdffefffffe1ff000

def z835 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfd7e631ffc387ce5 0x7fafcc63ff870f9c

def z836 : W := mkw 0x78026bd6e0000000 0x0f004d7adc000000 0x7c4623fff0000000 0x0f88c47ffe000000

def z837 : W := mkw 0x38058bd6e0000000 0x0700b17adc000000 0x7c2703fff0000000 0x0f84e07ffe000000

def z838 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6fb958e74336631a 0xadf72b1ce866cc63

def z839 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d7e63078c307ce4 0x2bafcc60f1860f9c

def z840 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0xfff7ffffff3e0003 0xfffeffffffe7c000

def z841 : W := mkw 0x01e000291152f3b9 0xe03c0005222a5e77 0x8008000003f7e39f 0xb0010000007efc73

def z842 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x98ff83f80fc07c00 0xf31ff07f01f80f80

def z843 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x184e23078c087c60 0x4309c460f1810f8c

def z844 : W := mkw 0x00800105801024c0 0x80100020b0020498 0x5c4e03078c007ce4 0x4b89c060f1800f9c

def z845 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xbcff83f80fc06c00 0xf79ff07f01f80d80

def z846 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03f7fc000fff8000 0x607eff8001fff000

def z847 : W := mkw 0x48827505a43824c4 0x89104ea0b4870498 0xdd7e6707bc387ce5 0x7bafcce0f7870f9c

def z848 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7ff1fffff0000000 0x0ffe3ffffe000000

def z849 : W := mkw 0x7a07ffd6e42d0006 0x0f40fffadc85a000 0x7ff7fffff0098000 0x0ffefffffe013000

def z850 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3caf83f80fc07f04 0xa795f07f01f80fe0

def z851 : W := mkw 0x42827505843d24c6 0x88504ea0b087a498 0xdffeff078cfffce7 0xfbffdfe0f19fff9c

def z852 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0xffd0a7fff0c98003 0xdffa14fffe193000

def z853 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03c7fc000fff8003 0xc078ff8001fff000

def z854 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xe38958e74336639f 0xbc712b1ce866cc73

def z855 : W := mkw 0x7a07ffd6e0050002 0x0f40fffadc00a000 0x7ff7fffff0078002 0x0ffefffffe00f000

def z856 : W := mkw 0x6587e3bd8ff87fc5 0x8cb0fc77b1ff0ff8 0x6181e0ff83f803e1 0x8c303c1ff07f007c

def z857 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0x882f03e00fc9ffff 0xf105e07c01f93fff

def z858 : W := mkw 0x060594000ead0006 0x00c0b28001d5a000 0x800118000fff8003 0xf000230001fff000

def z859 : W := mkw 0x460274000ead0006 0x08c04e8001d5a000 0x83767c000fff8003 0xf06ecf8001fff000

def z860 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffff87f87fc1ff9f 0xfffff0ff0ff83ff3

def z861 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xfcff83f84fc07f9c 0xff9ff07f09f80ff3

def z862 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbeff9bf80fc67f06 0xf7dff37f01f8cfe0

def z863 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ffffffff0007c04 0x0ffffffffe000f80

def z864 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcff83f80fc1ff1e 0xf79ff07f01f83fe3

def z865 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7ffffffff90e7 0xfffefffffffff21c

def z866 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbeff87f87fc07f04 0xf7dff0ff0ff80fe0

def z867 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffa7f8ffc07f9f 0xfffff4ff1ff80ff3

def z868 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xffff7b07cf3e7fff 0xffffef60f9e7cfff

def z869 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdf7e6307cc387cff 0x7befcc60f9870f9f

def z870 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x600000fff0000000 0x0c00001ffe000000

def z871 : W := mkw 0x47e7f4291ffff3bf 0xe8fcfe8523fffe77 0x83fffc000ffff3ff 0xf07fff8001fffe7f

def z872 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfffffff8ffffffff 0xffffffff1fffffff

def z873 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd7e63078cf9fce7 0xfbafcc60f19f3f9c

def z874 : W := mkw 0x240582900a800000 0x0480b05201500000 0xbcff83f80fc07c04 0xf79ff07f01f80f80

def z875 : W := mkw 0x42827505843d24c6 0x88504ea0b087a498 0xdd7e7b078c3e7ce5 0x7bafcf60f187cf9c

def z876 : W := mkw 0x42827505843d24c6 0x88504ea0b087a498 0xdd7e67078c39fce5 0x7bafcce0f1873f9c

def z877 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3ccf83f80fc07f04 0xc799f07f01f80fe0

def z878 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdfffff078ffffce7 0xfbffffe0f1ffff9c

def z879 : W := mkw 0x00800105801024c0 0x80100020b0020498 0xdd7e23078c087ce5 0x7bafc460f1810f9c

def z880 : W := mkw 0x30058ad240000000 0x0600b15a48000000 0x7ff7fffff0000000 0x0ffefffffe000000

def z881 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3cff83f80cc07f04 0x479ff07f01980fe0

def z882 : W := mkw 0x272596b81bc5db2b 0x24e4b2d70378bb65 0xffffbff8ffcfffff 0xfffff7ff1ff9ffff

def z883 : W := mkw 0x50c26947c43a24d4 0xca184d28f887449a 0x430058074036009b 0x08600b00e806c013

def z884 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x28af03e00f006f00 0xa515e07c01e00de0

def z885 : W := mkw 0x5d027d6eebc05b01 0x0ba04faddd780b60 0xc3087c07ffc07f04 0xf8610f80fff80fe0

def z886 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x082f83f80fc06c00 0x2105f07f01f80d80

def z887 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x082958e70336639c 0x21052b1ce066cc73

def z888 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcff83f80fc9ff07 0xf79ff07f01f93fe0

def z889 : W := mkw 0x1000084240000000 0x0200010848000000 0x7fb158fff0000000 0x0ff62b1ffe000000

def z890 : W := mkw 0x0120000810409129 0x2024000102081225 0xfff0e41ff0c993ff 0xdffe1c83fe19327f

def z891 : W := mkw 0x7e07ffd6eead0446 0x0fc0fffaddd5a088 0xfff7ffffffff9c63 0xfffefffffffff38c

def z892 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xfdffc3ff0fc07f04 0xffbff87fe1f80fe0

def z893 : W := mkw 0x7e07fed26ead0006 0x0fc0ffda4dd5a000 0xeff7fcff7fff8003 0xfdfeff9feffff000

def z894 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x986f83f80fc07f04 0xf30df07f01f80fe0

def z895 : W := mkw 0x50426966c52a4654 0x4a084d2cd8a548ca 0x32c73be0cf0e1f7a 0xc658e77c19e1c3ef

def z896 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb9dce743f7e39f 0xbdf73b9ce87efc73

def z897 : W := mkw 0x0120000810409129 0x2024000102081225 0xf440a418f0c993ff 0xde8814831e19327f

def z898 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8381fc000fff8003 0xf0703f8001fff000

def z899 : W := mkw 0x4607f5048ead0006 0x08c0fea091d5a000 0xdfffff078ffffc07 0xfbffffe0f1ffff80

def z900 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd7f7b078f3e7ce5 0x7bafef60f1e7cf9c

def z901 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x5d77ffffb0000000 0x0baefffff6000000

def z902 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfdffa3f8ffc87ffd 0xffbff47f1ff90fff

def z903 : W := mkw 0x58827d47e43824c4 0x8b104fa8fc870498 0x43007c07f0300000 0x08600f80fe060000

def z904 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x184e83f80cc07c00 0x4309d07f01980f80

def z905 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6f2958e74336639f 0x2de52b1ce866cc73

def z906 : W := mkw 0x6607f6900ead0006 0x0cc0fed201d5a000 0xbffffff80ffffc07 0xf7ffffff01ffff80

def z907 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xc3f7fc004fff809b 0xf87eff8009fff013

def z908 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcffa7f80fc9ff04 0xf79ff4ff01f93fe0

def z909 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xa8ff83f80fc06f00 0xf51ff07f01f80de0

def z910 : W := mkw 0x6607f6900ead0006 0x0cc0fed201d5a000 0x8bf7ffe00fff8003 0xf17efffc01fff000

def z911 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0x7c2f03f8ff007ffc 0x2f85e07f1fe00fff

def z912 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x3ae7fffff0000000 0x075cfffffe000000

def z913 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfffe6307cc387ce5 0x7fffcc60f9870f9c

def z914 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfffffffffffffc07 0xffffffffffffff80

def z915 : W := mkw 0x7c07ffd6eea80004 0x0f80fffaddd50000 0xfff7fffffff80001 0xfffeffffffff0000

def z916 : W := mkw 0x78026bd6e4280004 0x0f004d7adc850000 0xfd7663fffc380001 0x7faecc7fff870000

def z917 : W := mkw 0x5a827d47e43d24c6 0x8b504fa8fc87a498 0x43007c07f03f80e3 0x08600f80fe07f01c

def z918 : W := mkw 0x39e00bfff152f3b9 0xe73c017ffe2a5e77 0x7c0803fff00073fc 0x0f81007ffe000e7f

def z919 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xaeb958e74336631e 0xb5d72b1ce866cc63

def z920 : W := mkw 0x6607f6900ead0006 0x0cc0fed201d5a000 0x93f7ff180fff8003 0xf27effe301fff000

def z921 : W := mkw 0x7c07ffd6ea800000 0x0f80fffadd500000 0xfff7fffffff60003 0xfffefffffffec000

def z922 : W := mkw 0x6e07f794aead0006 0x0dc0fef295d5a000 0xdff7ff1fbfff8003 0xfbfeffe3f7fff000

def z923 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x28275bff70000000 0x0504eb7fee000000

def z924 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x596e63078c387ce1 0x6b2dcc60f1870f9c

def z925 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x80f7d8000fff8003 0xf01efb0001fff000

def z926 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x7c0087fff0000000 0x0f8010fffe000000

def z927 : W := mkw 0x4002600004280004 0x08004c0000850000 0x83f7fc000fff8003 0xf07eff8001fff000

def z928 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x7ff1fcfff0000000 0x0ffe3f9ffe000000

def z929 : W := mkw 0x200002b001004a00 0x0400005600200940 0x082e03e00c006c00 0x2105c07c01800d80

def z930 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7c40a7fff0000000 0x0f8814fffe000000

def z931 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xdfffff008ffffce7 0xfbffffe011ffff9c

def z932 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x2aa7dfff7ff78002 0xa554fbffeffef000

def z933 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffff83f84fc9ffff 0xfffff07f09f93fff

def z934 : W := mkw 0x7e07ffd6ea850002 0x0fc0fffadd50a000 0x7ff7fffff0c18000 0x0ffefffffe183000

def z935 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7d76e7fff0000000 0x0faedcfffe000000

def z936 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7cf7dbfff0000000 0x0f9efb7ffe000000

def z937 : W := mkw 0x0120000810409129 0x2024000102081225 0xe790a418f0c983ff 0x9cf214831e19307f

def z938 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xe3f7fcffffff8003 0xfc7eff9ffffff000

def z939 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x8bbf5be00f366c03 0xb177eb7c01e6cd80

def z940 : W := mkw 0x7c07ffd6ea800000 0x0f80fffadd500000 0x7ff7ffffff000000 0x2ffeffffffe00000

def z941 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7c7603fff0000000 0x0f8ec07ffe000000

def z942 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xe79158e74336039f 0x9cf22b1ce866c073

def z943 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcff83f80fc07ffc 0xf79ff07f01f80fff

def z944 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffa3f8cfc87fff 0xfffff47f19f90fff

def z945 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff3060002 0x8ffefffffe60c000

def z946 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd7e63078f3e7ce7 0xfbafcc60f1e7cf9c

def z947 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8067fc000fff8003 0xf00cff8001fff000

def z948 : W := mkw 0x7c07ffd6ea800000 0x0f80fffadd500000 0xfff7ffffffc98003 0xfffefffffff93000

def z949 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x080e03e00c006c00 0x0101c07c01800d80

def z950 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83fffc000ffffc07 0xf07fff8001ffff80

def z951 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffffa7f8ffc1ff1e 0xfffff4ff1ff83fe3

def z952 : W := mkw 0x040580000a800000 0x0080b00001500000 0x83f7fc000fff8003 0xf07eff8001fff000

def z953 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5c0e03078c007ce4 0x0b81c060f1800f9c

def z954 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83d1fc0003ff8003 0xd07a3f80007ff000

def z955 : W := mkw 0x0120000810409129 0x2024000102081225 0x76c0a418f0c993fe 0xced814831e19327f

def z956 : W := mkw 0x51e2694fd47ab5fd 0xea3c4d29fa8f56bf 0xf7d0fc1ff0ff93ff 0xdefa1f83fe1ff27f

def z957 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x38ef83f80fc07f00 0xe71df07f01f80fe0

def z958 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d4e63078c387ce5 0x4ba9cc60f1870f9c

def z959 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff000039c 0x0ffefffffe000073

def z960 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb97ce7433fe39f 0xbdf72f9ce867fc73

def z961 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x1846a7ffb0000000 0x0308d4fff6000000

def z962 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0c9839f 0xdffefffffe193073

def z963 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffffc000000 0x7ffeffffff800000

def z964 : W := mkw 0x460274000ead0006 0x08c04e8001d5a000 0x800058000fff8003 0xf0000b0001fff000

def z965 : W := mkw 0x6f27f79cbeed912f 0x2de4fef397ddb225 0x1046a718bcc99060 0x4208d4e31799320c

def z966 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83f7fc000fff839f 0xf07eff8001fff073

def z967 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcff83f80fc87fe5 0xf79ff07f01f90ffc

def z968 : W := mkw 0x68c7f7b5a1126290 0xcd18fef6b4224c52 0x904ea718b336639f 0xb209d4e31666cc73

def z969 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ec7bffff0000000 0x0fd8f7fffe000000

def z970 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcff87f83fc1ff04 0xf79ff0ff07f83fe0

def z971 : W := mkw 0x6e07f6902ead0006 0x0dc0fed205d5a000 0x83f7fc183fff8003 0xf07eff8307fff000

def z972 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb978e7c33e63ff 0xbdf72f1cf867cc7f

def z973 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff9fcfff3ffe39f 0xffff3f9ffe7ffc73

def z974 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7c275bffff360000 0x2f84eb7fffe6c000

def z975 : W := mkw 0x060000000a850002 0x00c000000150a000 0x83b1580003f78003 0xb0762b00007ef000

def z976 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcffa7f8bfc07f04 0xf79ff4ff17f80fe0

def z977 : W := mkw 0x270596b80bc55b03 0x04e0b2d70178ab60 0xbfffbff80fcfff07 0xf7fff7ff01f9ffe0

def z978 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff3360000 0x2ffefffffe66c000

def z979 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7d5023fff0000000 0x0faa047ffe000000

def z980 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7f005bfff0000000 0x0fe00b7ffe000000

def z981 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb9dcff7336639f 0xbdf73b9fee66cc73

def z982 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5c6e63078c387ce4 0x6b8dcc60f1870f9c

def z983 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xacb958e70336639f 0xb5972b1ce066cc73

def z984 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x2bf7ffff70000000 0x057effffee000000

def z985 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0xffb15bfff3360003 0xbff62b7ffe66c000

def z986 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03f7fc000ff78002 0xa07eff8001fef000

def z987 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfdff63e78c387ce5 0x7fbfec7cf1870f9c

def z988 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb958e7433e73ff 0xfdf72b1ce867ce7f

def z989 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x002758000fff8000 0x6004eb0001fff000

def z990 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xcb2958e74336639f 0xb9652b1ce866cc73

def z991 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbc7f03f80f007f04 0x778fe07f01e00fe0

def z992 : W := mkw 0x4607f5048ead0446 0x08c0fea091d5a088 0x9fffff008ffffc67 0xf3ffffe011ffff8c

def z993 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x830058000fff8003 0xf0600b0001fff000

def z994 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7e811bfff0000000 0x0fd0237ffe000000

def z995 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcff83f80ff67f07 0xf79ff07f01fecfe0

def z996 : W := mkw 0x060594000ead0006 0x00c0b28001d5a000 0x83b1dc000fff8003 0xf0763b8001fff000

def z997 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xf7f7fc18ffff90e7 0xfefeff831ffff21c

def z998 : W := mkw 0x31e00afb5152fbb9 0xe63c015f6a2a5f77 0x7c0803fff0007ffc 0x0f81007ffe000fff

def z999 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x0027dc000ff78000 0x2004fb8001fef000

def z1000 : W := mkw 0x5607fc424ead0006 0x0ac0ff8849d5a000 0xfff7fcffffff8003 0xfffeff9ffffff000

def z1001 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbeff87f80fc1ff06 0xf7dff0ff01f83fe0

def z1002 : W := mkw 0x1120084a50409129 0x222401094a081225 0xefb158e740c993ff 0xddf62b1ce819327f

def z1003 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7ffffffcf8002 0xcffefffffff9f000

def z1004 : W := mkw 0x1000084240000000 0x0200010848000000 0x7c0000fff0000000 0x0f80001ffe000000

def z1005 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xf7f7fc00cfff93ff 0xfefeff8019fff27f

def z1006 : W := mkw 0x6607f6900ead0806 0x0cc0fed201d5a100 0x83f7ff000fff8c03 0xf07effe001fff180

def z1007 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffffa7f8ffc07ffc 0xfffff4ff1ff80fff

def z1008 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x2aa1dcff70000000 0x05543b9fee000000

def z1009 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7c0003fff00010e4 0x0f80007ffe00021c

def z1010 : W := mkw 0x0000000000000000 0x0000000000000000 0x83b1580003ff8003 0xf0762b00007ff000

def z1011 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x882f03e00f007c04 0x7105e07c01e00f80

def z1012 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xed3958e74336639d 0x3da72b1ce866cc73

def z1013 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7ffffff360003 0xbffeffffffe6c000

def z1014 : W := mkw 0x2005829000000000 0x0400b05200000000 0x3cff83f80c006c00 0x279ff07f01800d80

def z1015 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffdbf84ff67f9f 0xfffffb7f09fecff3

def z1016 : W := mkw 0x58c27d47e43a24d4 0xcb184fa8fc87449a 0x43007c07f03e00fb 0x08600f80fe07c01f

def z1017 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x08ff83e00f006c00 0x211ff07c01e00d80

def z1018 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x082f03e00fc06f00 0xa105e07c01f80de0

def z1019 : W := mkw 0x270582b80bc55b03 0x04e0b0570178ab60 0xbcff83f80fc7ff06 0xf79ff07f01f8ffe0

def z1020 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0x6c0800ff7000639c 0x0d81001fee000c73

def z1021 : W := mkw 0x7807ffd6e4280444 0x0f00fffadc850088 0xfffffffffc087c64 0x7fffffffff810f8c

def z1022 : W := mkw 0x460274000ead0006 0x08c04e8001d5a000 0x03007c0003ff8003 0x80600f80007ff000

def z1023 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x082e43070c307ce4 0x2105c860e1860f9c

def z1024 : W := mkw 0x7807ffd6e4280444 0x0f00fffadc850088 0xfff7fffffc081ce5 0x5ffeffffff81039c

def z1025 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcbf03f80f007f04 0xb797e07f01e00fe0

def z1026 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0x7ff7fffffc300000 0x2ffeffffff860000

def z1027 : W := mkw 0x4607f5048ead0446 0x08c0fea091d5a088 0xd7f7ff008fff9ce7 0xfafeffe011fff39c

def z1028 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdfff7b078c387ce5 0x7bffef60f1870f9c

def z1029 : W := mkw 0x210002b801405b01 0x0420005700280b60 0xbcff03f80f007f04 0xf79fe07f01e00fe0

def z1030 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x082f03e00f007f04 0x2105e07c01e00fe0

def z1031 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7ffffffff8000 0x6ffefffffffff000

def z1032 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x9c7e43070c387ce5 0x738fc860e1870f9c

def z1033 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7d8a418fcc9ffff 0xfefb14831f993fff

def z1034 : W := mkw 0x40826105801024c0 0x88104c20b0020498 0xdd7e63078c007ce4 0x7bafcc60f1800f9c

def z1035 : W := mkw 0x210582b801405b01 0x0420b05700280b60 0xbcff83f80c007f04 0x779ff07f01800fe0

def z1036 : W := mkw 0x060594000ead0006 0x00c0b28001d5a000 0x82f79c000fff8003 0xf05ef38001fff000

def z1037 : W := mkw 0x4002610480000000 0x08004c2090000000 0xdd7e63078c087ce5 0x7bafcc60f1810f9c

def z1038 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xb0cf83f80fc07f04 0xf619f07f01f80fe0

def z1039 : W := mkw 0x6607f6900ead0006 0x0cc0fed201d5a000 0xfff7fff8ffff8003 0xfffeffff1ffff000

def z1040 : W := mkw 0x2000029000000000 0x0400005200000000 0xbc7e03f80c007c04 0x778fc07f01800f80

def z1041 : W := mkw 0x50826947c43824c4 0x8a104d28f8870498 0x43007807c03800e1 0x08600f00f807001c

def z1042 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xcff7fc070fff8003 0xf9feff80e1fff000

def z1043 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0000304 0x9ffefffffe000060

def z1044 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff3ff8003 0xfffefffffe7ff000

def z1045 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff00800e1 0x0ffefffffe01001c

def z1046 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7d6a718fcc99fff 0xdefad4e31f9933ff

def z1047 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x986e63078c387ce5 0x730dcc60f1870f9c

def z1048 : W := mkw 0x0120000810409129 0x2024000102081225 0xfff8a418f0c9f3ff 0xffff14831e193e7f

def z1049 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x82c7bc000fff8003 0xf058f78001fff000

def z1050 : W := mkw 0x0000000000000000 0x0000000000000000 0x83b1dc0003f78003 0xb0763b80007ef000

def z1051 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbffffff80fffff07 0xf7ffffff01ffffe0

def z1052 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xeff9fce74336639f 0xbdff3f9ce866cc73

def z1053 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x9ff7ff000fff8003 0xf3feffe001fff000

def z1054 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x3ef7dfff70000000 0x07defbffee000000

def z1055 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffa7f8ffc9ff07 0xfffff4ff1ff93fe0

def z1056 : W := mkw 0x060594000ead0006 0x00c0b28001d5a000 0x02819c0003ff8003 0x80503380007ff000

def z1057 : W := mkw 0x6e07f794aead0006 0x0dc0fef295d5a000 0xf7f7ff18ffff8003 0xfefeffe31ffff000

def z1058 : W := mkw 0x0120000810409129 0x2024000102081225 0xfff6a718f0c993ff 0xdffed4e31e19327f

def z1059 : W := mkw 0x210002b801405b01 0x0420005700280b60 0x3c2e03f80c007f04 0x2785c07f01800fe0

def z1060 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdffe63078c387ce7 0xfbffcc60f1870f9c

def z1061 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x1c7f03e00f006c00 0x238fe07c01e00d80

def z1062 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6ba958e74336639b 0xad752b1ce866cc73

def z1063 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xffff7be7cf3e7fff 0xffffef7cf9e7cfff

def z1064 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x0827dfff30000000 0x0104fbffe6000000

def z1065 : W := mkw 0x07e000291ffff3bf 0xe0fc000523fffe77 0x800800000ffff3ff 0xf001000001fffe7f

def z1066 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xfcff83f8ffc07f04 0xff9ff07f1ff80fe0

def z1067 : W := mkw 0x7c07ffd6ea800800 0x0f80fffadd500100 0x7ff7fffffc000c00 0x0ffeffffff800180

def z1068 : W := mkw 0x0120000810409129 0x2024000102081225 0xf4d0a418f0c993fc 0xde9a14831e19327f

def z1069 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbdffa3f80fc87f05 0xf7bff47f01f90fe0

def z1070 : W := mkw 0x0120000810409129 0x2024000102081225 0xd340a418f0c993ff 0xda6814831e19327f

def z1071 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7d3043fff0000000 0x0fa6087ffe000000

def z1072 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3c0e03f80c007f04 0x0781c07f01800fe0

def z1073 : W := mkw 0x6807f794a0000000 0x0d00fef294000000 0x7df7e7ffb0000000 0x0fbefcfff6000000

def z1074 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x9cff83e00fc07c04 0xf39ff07c01f80f80

def z1075 : W := mkw 0x52c27d47c43f24d6 0xca584fa8f887e49a 0x43007c07c03f80fb 0x08600f80f807f01f

def z1076 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0xfd5023fff00810e5 0x5faa047ffe01021c

def z1077 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffff83f8ffc07fff 0xfffff07f1ff80fff

def z1078 : W := mkw 0x7a027fd6e42d0006 0x0f404ffadc85a000 0x7f007ffff03f8003 0x0fe00ffffe07f000

def z1079 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x882f03e00fc06c00 0xf105e07c01f80d80

def z1080 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefbf5be74f366f9f 0xbdf7eb7ce9e6cdf3

def z1081 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x82a7dc000fff8003 0xf054fb8001fff000

def z1082 : W := mkw 0x11e0086b5152f3b9 0xe23c010d6a2a5e77 0x6c0800e7400073fc 0x0d81001ce8000e7f

def z1083 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff0360003 0x0ffefffffe06c000

def z1084 : W := mkw 0x2125829810409129 0x2424b05302081225 0xffffa7f8fcc9ffff 0xfffff4ff1f993fff

def z1085 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xe7f7fc004fff8003 0xfcfeff8009fff000

def z1086 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x182f03f80f007c00 0x2305e07f01e00f80

def z1087 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7cb103fff0000000 0x0f96207ffe000000

def z1088 : W := mkw 0x01e000291152f3b9 0xe03c0005222a5e77 0x00080000000073fc 0x0001000000000e7f

def z1089 : W := mkw 0x00800105801024c0 0x80100020b0020498 0x5c2e03078c007ce4 0x2b85c060f1800f9c

def z1090 : W := mkw 0x58027d46e0000000 0x0b004fa8dc000000 0x7ff1fcfff0000000 0x0ffe3f9ffe000000

def z1091 : W := mkw 0x0120000810409129 0x2024000102081225 0x7740a418f0c993ff 0x4ee814831e19327f

def z1092 : W := mkw 0x250596b80bc05b01 0x04a0b2d701780b60 0xbeff9ff80fc07f04 0xf7dff3ff01f80fe0

def z1093 : W := mkw 0x7c07ffd6ea800000 0x0f80fffadd500000 0x7ff7fffff3c00000 0x8ffefffffe780000

def z1094 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x002758000ff78002 0xa004eb0001fef000

def z1095 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdc4e23078c387ce5 0x7b89c460f1870f9c

def z1096 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0080001 0x5ffefffffe010000

def z1097 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcffdbf80ff67f04 0xf79ffb7f01fecfe0

def z1098 : W := mkw 0x42826105843d24c6 0x88504c20b087a498 0xdd7e63078c3ffce7 0x7bafcc60f187ff9c

def z1099 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb958e743ffe39f 0xfdf72b1ce87ffc73

def z1100 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfffee707ccf9ffff 0xffffdce0f99f3fff

def z1101 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xacbf03e00fc07f04 0xf597e07c01f80fe0

def z1102 : W := mkw 0x270596b80bc55b03 0x04e0b2d70178ab60 0xbcff9bf80fc67f04 0xf79ff37f01f8cfe0

def z1103 : W := mkw 0x4007f40000000000 0x0800fe8000000000 0x83f7fc0003ff8003 0xf07eff80007ff000

def z1104 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcff83f80fc9ff64 0xf79ff07f01f93fec

def z1105 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0c00000 0xdffefffffe180000

def z1106 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfdffa3f88fc9ffff 0xffbff47f11f93fff

def z1107 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7f9003fff0000000 0x0ff2007ffe000000

def z1108 : W := mkw 0x0100002801405301 0x0020000500280a60 0xbcff83f80fc07f04 0xf79ff07f01f80fe0

def z1109 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ffffffffc006c00 0x2fffffffff800d80

def z1110 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0xfff7fffffcf98003 0xfffeffffff9f3000

def z1111 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffa7f8ffc87fe5 0xfffff4ff1ff90ffc

def z1112 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbfffa7f8bfc9ff67 0xf7fff4ff17f93fec

def z1113 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x180003ffb0000000 0x0300007ff6000000

def z1114 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcffa3f88fc87f64 0xf79ff47f11f90fec

def z1115 : W := mkw 0x58827d47e43824c4 0x8b104fa8fc870498 0xf7d0fc1ff03810e5 0x5efa1f83fe07021c

def z1116 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7f1a418f3c993ff 0xfefe34831e79327f

def z1117 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x93f7ff000fff9c03 0xf27effe001fff380

def z1118 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x18275bffb0000000 0x0304eb7ff6000000

def z1119 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfd7e6307cc387ffd 0x7fafcc60f9870fff

def z1120 : W := mkw 0x6607f6900ead0006 0x0cc0fed201d5a000 0xa3f7fcf80fff8003 0xf47eff9f01fff000

def z1121 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfffffffffc087ce5 0x7fffffffff810f9c

def z1122 : W := mkw 0x38058bd6e0000000 0x0700b17adc000000 0x7ff7dbfff0000000 0x0ffefb7ffe000000

def z1123 : W := mkw 0x50026946c0000000 0x0a004d28d8000000 0x7ff7fffff0000000 0x0ffefffffe000000

def z1124 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd7ee7078cf9fce5 0x7bafdce0f19f3f9c

def z1125 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xa7f7fc000fff8307 0xf4feff8001fff060

def z1126 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7ffffffff839f 0xfffefffffffff073

def z1127 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff000031a 0x8ffefffffe000063

def z1128 : W := mkw 0x6e07f794aead0006 0x0dc0fef295d5a000 0xbff7fff8bfff8003 0xf7feffff17fff000

def z1129 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x802158000fff8003 0xf0042b0001fff000

def z1130 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xbcff83f80f006f04 0xb79ff07f01e00de0

def z1131 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8177fc000fff8001 0x702eff8001fff000

def z1132 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x02a1dc0003f78002 0xa0543b80007ef000

def z1133 : W := mkw 0x460274000ead0006 0x08c04e8001d5a000 0x83d0fc000fff8003 0xf07a1f8001fff000

def z1134 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7ff7fffffcff8003 0x4ffeffffff9ff000

def z1135 : W := mkw 0x460274000ead0006 0x08c04e8001d5a000 0x83b17c000fff8003 0xf0762f8001fff000

def z1136 : W := mkw 0x42027400042d0006 0x08404e800085a000 0x83f1fc0003ff8003 0xf07e3f80007ff000

def z1137 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd7ee71fbc387ce5 0x7bafdce3f7870f9c

def z1138 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x6e819cff70000000 0x0dd0339fee000000

def z1139 : W := mkw 0x2005829000000000 0x0400b05200000000 0x9c7f03e00c007c04 0x738fe07c01800f80

def z1140 : W := mkw 0x7a07ffd6e42d0006 0x0f40fffadc85a000 0xfff7fffff33f8003 0xbffefffffe67f000

def z1141 : W := mkw 0x460260000ead0006 0x08c04c0001d5a000 0x83f778000fff8003 0xf07eef0001fff000

def z1142 : W := mkw 0x4607f5048ead0446 0x08c0fea091d5a088 0xdff7ff078fff9c63 0xfbfeffe0f1fff38c

def z1143 : W := mkw 0x38001fd6e0000000 0x070003fadc000000 0x7e001ffff0000000 0x0fc003fffe000000

def z1144 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xffb958e7c33673ff 0xbff72b1cf866ce7f

def z1145 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xa8af83f80fc07f04 0xf515f07f01f80fe0

def z1146 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6ea958e74336639e 0xadd52b1ce866cc73

def z1147 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd3e43078c307ce5 0x3ba7c860f1860f9c

def z1148 : W := mkw 0x4607f5048ead0006 0x08c0fea091d5a000 0xfff7ff1fffff8003 0xfffeffe3fffff000

def z1149 : W := mkw 0x78027fd6e0000000 0x0f004ffadc000000 0x63007cfff0000000 0x0c600f9ffe000000

def z1150 : W := mkw 0x6e07f794aead0446 0x0dc0fef295d5a088 0x93f7ff18bfff9c63 0xf27effe317fff38c

def z1151 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x93f7fc008fff9063 0xf27eff8011fff20c

def z1152 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcff83f8bfc07f64 0xf79ff07f17f80fec

def z1153 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff9d8ff4336639f 0xbfff3b1fe866cc73

def z1154 : W := mkw 0x4e07f504aead0006 0x09c0fea095d5a000 0x83f7fc00bfff8003 0xf07eff8017fff000

def z1155 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0x7ff7fffff0380001 0x0ffefffffe070000

def z1156 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbfffa7f80fc07f04 0xf7fff4ff01f80fe0

def z1157 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffffc001c00 0x4ffeffffff800380

def z1158 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x082f03e00fc07c00 0x6105e07c01f80f80

def z1159 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x8bffa7e00fc9ec03 0xf17ff4fc01f93d80

def z1160 : W := mkw 0x6607f7948ead0006 0x0cc0fef291d5a000 0xfff7ffff8fff8003 0xfffefffff1fff000

def z1161 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff9fcfff33e73ff 0xffff3f9ffe67ce7f

def z1162 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x73c7fffff0000000 0x0e78fffffe000000

def z1163 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xd14e63078c387ce5 0x7a29cc60f1870f9c

def z1164 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffffa7f8ffc9ff64 0xfffff4ff1ff93fec

def z1165 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xffff5be74336639f 0xbfffeb7ce866cc73

def z1166 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x228158e74336031a 0x84502b1ce866c063

def z1167 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7f1fc18f0c993ff 0xdefe3f831e19327f

def z1168 : W := mkw 0x78026bd6e0000000 0x0f004d7adc000000 0x7ff77bfff0000000 0x0ffeef7ffe000000

def z1169 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x83f7dc000ff78003 0xf07efb8001fef000

def z1170 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff0081060 0x4ffefffffe01020c

def z1171 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x3cf7ffffb0000000 0x079efffff6000000

def z1172 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbeff87f87fc9ffff 0xf7dff0ff0ff93fff

def z1173 : W := mkw 0x212002b81140db29 0x2424005702281b65 0xfd7e23f8fc087ffd 0x7fafc47f1f810fff

def z1174 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff0098003 0x0ffefffffe013000

def z1175 : W := mkw 0x0000002001004200 0x0000000400200840 0xacbf03e00f006f04 0xb597e07c01e00de0

def z1176 : W := mkw 0x012000281140d329 0x2024000502281a65 0xffffa7f8ffc9ffff 0xfffff4ff1ff93fff

def z1177 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x7c46a7fffcc98000 0x4f88d4ffff993000

def z1178 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xfff9fce7c3fff3ff 0xffff3f9cf87ffe7f

def z1179 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7f46fffff0000000 0x0fe8dffffe000000

def z1180 : W := mkw 0x4607f4000ead0446 0x08c0fe8001d5a088 0x83f7fc000fff9c63 0xf07eff8001fff38c

def z1181 : W := mkw 0x40827505843824c4 0x88104ea0b0870498 0xdf7e7f078c387ce5 0x7befcfe0f1870f9c

def z1182 : W := mkw 0x1000084240000000 0x0200010848000000 0x6fb1dcff70000000 0x0df63b9fee000000

def z1183 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdc2e43078c387ce5 0x7b85c860f1870f9c

def z1184 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xfdffa7f8bfc9ffe5 0xffbff4ff17f93ffc

def z1185 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x082f5be00f366c00 0x2105eb7c01e6cd80

def z1186 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x186f83f80f006c00 0x230df07f01e00d80

def z1187 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ff7fffff0c18002 0x8ffefffffe183000

def z1188 : W := mkw 0x00800105801024c0 0x80100020b0020498 0xdd7e43078c307ce5 0x7bafc860f1860f9c

def z1189 : W := mkw 0x7e07ffd6ea850002 0x0fc0fffadd50a000 0xfff7fffff3f78003 0xbffefffffe7ef000

def z1190 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0xff9003fff000039f 0x9ff2007ffe000073

def z1191 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xa3f7fc187fff8003 0xf47eff830ffff000

def z1192 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefff58e74f36639f 0xfdffeb1ce9e6cc73

def z1193 : W := mkw 0x212002b81140db29 0x2424005702281b65 0xfffea7f8fcc9ffff 0xffffd4ff1f993fff

def z1194 : W := mkw 0x4607f5048ead0006 0x08c0fea091d5a000 0xc3f7fc078fff8003 0xf87eff80f1fff000

def z1195 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7c0003fff000039c 0x0f80007ffe000073

def z1196 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xbcff83f80f007c04 0x779ff07f01e00f80

def z1197 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbc2f03f80fc07f04 0xf785e07f01f80fe0

def z1198 : W := mkw 0x260596b00b854a02 0x04c0b2d60170a940 0x082f1be00f066c00 0x2105e37c01e0cd80

def z1199 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3cff83f80fc06f00 0xa79ff07f01f80de0

def z1200 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfffee71ffc387fff 0xffffdce3ff870fff

def z1201 : W := mkw 0x0120000810409129 0x2024000102081225 0xf550a418f0c993fd 0x5eaa14831e19327f

def z1202 : W := mkw 0x4607f5048ead0006 0x08c0fea091d5a000 0x93f7ff008fff8003 0xf27effe011fff000

def z1203 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x0367fc000fff8003 0x606cff8001fff000

def z1204 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdffee7078c387ce5 0x7bffdce0f1870f9c

def z1205 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xa3f7fc004fff831b 0xf47eff8009fff063

def z1206 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xffdea7f8fcc9ffff 0xdffbd4ff1f993fff

def z1207 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x7fffa7f8ff006c00 0x2ffff4ff1fe00d80

def z1208 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x97f7fc000fff9007 0xf2feff8001fff200

def z1209 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xacff83e00fc06f04 0xf59ff07c01f80de0

def z1210 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7f277ffff0000000 0x0fe4effffe000000

def z1211 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x6ba7fffff0000000 0x0d74fffffe000000

def z1212 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6fb158e74336039b 0x8df62b1ce866c073

def z1213 : W := mkw 0x260596b00b854a02 0x04c0b2d60170a940 0x0aaf9fe00fc7ec02 0xa155f3fc01f8fd80

def z1214 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xaaa958e74336639f 0xb5552b1ce866cc73

def z1215 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x6381dcff70000000 0x0c703b9fee000000

def z1216 : W := mkw 0x58827d47e43824c4 0x8b104fa8fc870498 0x0000580700300000 0x00000b00e0060000

def z1217 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3cff83f80f007f04 0x279ff07f01e00fe0

def z1218 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xffb95be743367f9f 0xbff72b7ce866cff3

def z1219 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x6381fcfff3ff8003 0x8c703f9ffe7ff000

def z1220 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x83f1fc0003ff8003 0xf07e3f80007ff000

def z1221 : W := mkw 0x060594000ead0006 0x00c0b28001d5a000 0x02819c000ff78002 0xa050338001fef000

def z1222 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x8bb958e70336639f 0xb1772b1ce066cc73

def z1223 : W := mkw 0x060594000ead0006 0x00c0b28001d5a000 0x83d1bc000fff8003 0xf07a378001fff000

def z1224 : W := mkw 0x270596b80bc55b03 0x04e0b2d70178ab60 0xbcff87f80fc1ff04 0xf79ff0ff01f83fe0

def z1225 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffffa7f88fc9ffe7 0xfffff4ff11f93ffc

def z1226 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xabf7ffff7fff8003 0xf57effffeffff000

def z1227 : W := mkw 0x7807fed260000000 0x0f00ffda4c000000 0x6ff7fcff70000000 0x0dfeff9fee000000

def z1228 : W := mkw 0x7807ffd6e4280444 0x0f00fffadc850088 0xfff7fffffc381c61 0x7ffeffffff87038c

def z1229 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x282f03f80f006f00 0x2505e07f01e00de0

def z1230 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb97ce7f336639f 0xbdf72f9cfe66cc73

def z1231 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xddff63078f387ce5 0xfbbfec60f1e70f9c

def z1232 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff336039f 0xbffefffffe66c073

def z1233 : W := mkw 0x4607f5048ead0446 0x08c0fea091d5a088 0x83f7ff000fff8c03 0xf07effe001fff180

def z1234 : W := mkw 0x0120000810409129 0x2024000102081225 0xb2c0a418f0c993ff 0xd65814831e19327f

def z1235 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbfff83f80fc07f07 0xf7fff07f01f80fe0

def z1236 : W := mkw 0x78026bd6e0000000 0x0f004d7adc000000 0x7d0063fff0000000 0x0fa00c7ffe000000

def z1237 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0x2aaf87f87fc1ef1a 0xa555f0ff0ff83de3

def z1238 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x817778000fff8003 0xf02eef0001fff000

def z1239 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0x7ff7fffffc080000 0x4ffeffffff810000

def z1240 : W := mkw 0x040580200b804200 0x0080b00401700840 0xbcff83e00fc07f04 0xf79ff07c01f80fe0

def z1241 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7f81fffff0000000 0x0ff03ffffe000000

def z1242 : W := mkw 0x11e0096fd152f7f9 0xe23c012dfa2a5eff 0x7c0803fff0007ffc 0x0f81007ffe000fff

def z1243 : W := mkw 0x1000084240000000 0x0200010848000000 0xfff1fcfff3ff8003 0xfffe3f9ffe7ff000

def z1244 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xeff978e7433e639f 0xfdff2f1ce867cc73

def z1245 : W := mkw 0x7807ffd6e4280004 0x0f00fffadc850000 0xfff7fffffc3810e5 0x7ffeffffff87021c

def z1246 : W := mkw 0x0120000810409129 0x2024000102081225 0x73c0a418f0c993fb 0xce7814831e19327f

def z1247 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xaff7fce00fff8003 0xf5feff9c01fff000

def z1248 : W := mkw 0x05a000291ff8ffed 0xa0b4000523ff1ffd 0x800800000ff9ffff 0xf001000001ff3fff

def z1249 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xc92e63078c387ce5 0x7925cc60f1870f9c

def z1250 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x62819cfff0000000 0x0c50339ffe000000

def z1251 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xb7f7fc180fff8003 0xf6feff8301fff000

def z1252 : W := mkw 0x0120000810409129 0x2024000102081225 0x77d0a418f0c993fc 0x4efa14831e19327f

def z1253 : W := mkw 0x200582b001004200 0x0400b05600200840 0xbcff83f80f007f04 0xf79ff07f01e00fe0

def z1254 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x80f7fc000fff8000 0xf01eff8001fff000

def z1255 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x1bf7ffffb0000000 0x037efffff6000000

def z1256 : W := mkw 0x01e00029157af7fd 0xe03c000522af5eff 0x800800000fffffff 0xf001000001ffffff

def z1257 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7e8087fff0000000 0x0fd010fffe000000

def z1258 : W := mkw 0x200002b001004a00 0x0400005600200940 0x9c7e03e00c007c04 0x738fc07c01800f80

def z1259 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x63f7fcfff0000000 0x0c7eff9ffe000000

def z1260 : W := mkw 0x0120000810409129 0x2024000102081225 0xe3d0a418f0c983fb 0xdc7a14831e19307f

def z1261 : W := mkw 0x060000000ead0006 0x00c0000001d5a000 0x828118000fff8003 0xf050230001fff000

def z1262 : W := mkw 0x060580000ead0006 0x00c0b00001d5a000 0x83f7d8000fff8003 0xf07efb0001fff000

def z1263 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d7e63078c387c60 0x6bafcc60f1870f8c

def z1264 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x182e43078c307c60 0x2305c860f1860f8c

def z1265 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbcffa7f8bfc9ffff 0xf79ff4ff17f93fff

def z1266 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x082958e70336631a 0xa1052b1ce066cc63

def z1267 : W := mkw 0x38059ed260000000 0x0700b3da4c000000 0x7ff7dfff70000000 0x0ffefbffee000000

def z1268 : W := mkw 0x78027fd6e0000000 0x0f004ffadc000000 0x7c0027fff0000000 0x0f8004fffe000000

def z1269 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7c0603fff0000000 0x0f80c07ffe000000

def z1270 : W := mkw 0x38000bd6e0000440 0x0700017adc000088 0x7c0003fff0001c60 0x0f80007ffe00038c

def z1271 : W := mkw 0x0120000810409129 0x2024000102081225 0xe380a418f0c993ff 0xdc7014831e19327f

def z1272 : W := mkw 0x4607f5048ead0446 0x08c0fea091d5a088 0x83f7fc008fff8063 0xf07eff8011fff00c

def z1273 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x086f83e00fc06c00 0x610df07c01f80d80

def z1274 : W := mkw 0x00800105843824c4 0x80100020b0870498 0xdc7e03078c387ce5 0x7b8fc060f1870f9c

def z1275 : W := mkw 0x38058bd6e0000000 0x0700b17adc000000 0x7c4683fff0000000 0x0f88d07ffe000000

def z1276 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x77d1fcfff0000000 0x0efa3f9ffe000000

def z1277 : W := mkw 0x4607f5048ead0006 0x08c0fea091d5a000 0xdff7ff078fff90e7 0xfbfeffe0f1fff21c

def z1278 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7f0e418f0f993ff 0xfefe1c831e1f327f

def z1279 : W := mkw 0x38000ad260000000 0x0700015a4c000000 0x6fb158ff70000000 0x0df62b1fee000000

def z1280 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xeff9d8e743f6639f 0xfdff3b1ce87ecc73

def z1281 : W := mkw 0x060594000a850002 0x00c0b2800150a000 0x0381dc0003f78003 0x80703b80007ef000

def z1282 : W := mkw 0x4002610484280444 0x08004c2090850088 0xdd7e63078c087c64 0x7bafcc60f1810f8c

def z1283 : W := mkw 0x78026bd6e0000000 0x0f004d7adc000000 0x7c2643fff0000000 0x0f84c87ffe000000

def z1284 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83b758000fff8003 0xf076eb0001fff000

def z1285 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d7e63078c087ce4 0x4bafcc60f1810f9c

def z1286 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbfffa7f87fc9ff1f 0xf7fff4ff0ff93fe3

def z1287 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xefbf03e04f006f9f 0xbdf7e07c09e00df3

def z1288 : W := mkw 0x2105829800401101 0x0420b05300080220 0xbcff83f80cc07f04 0xf79ff07f01980fe0

def z1289 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfdfe63078c387fe5 0xffbfcc60f1870ffc

def z1290 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xffff83f84fc07f04 0xfffff07f09f80fe0

def z1291 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x1c2f03e00f007c04 0x2385e07c01e00f80

def z1292 : W := mkw 0x254582b80bc25b11 0x44a8b05701784b62 0xbcff83f80fc67f1e 0xf79ff07f01f8cfe3

def z1293 : W := mkw 0x6e07f794aead0006 0x0dc0fef295d5a000 0x83f7ff000fff8003 0xf07effe001fff000

def z1294 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x8346fc000fff8003 0xf068df8001fff000

def z1295 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x7ef79ffff0000000 0x0fdef3fffe000000

def z1296 : W := mkw 0x78026bd6e4280444 0x0f004d7adc850088 0x7c4623fffc081c60 0x4f88c47fff81038c

def z1297 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0x6f8958e74336639f 0x8df12b1ce866cc73

def z1298 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0x7c0803fff0007c04 0x0f81007ffe000f80

def z1299 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xffb958fff336639f 0xbff72b1ffe66cc73

def z1300 : W := mkw 0x7807ffd6e0000440 0x0f00fffadc000088 0x7ff7fffff0001c60 0x0ffefffffe00038c

def z1301 : W := mkw 0x42827505843d24c6 0x88504ea0b087a498 0xdfff7f078f3ffce7 0xfbffefe0f1e7ff9c

def z1302 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0xbcff03e00f007f04 0xf79fe07c01e00fe0

def z1303 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff3000000 0xbffefffffe600000

def z1304 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xfdff83f80fc07f85 0xffbff07f01f80ff0

def z1305 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x9c7f83f80fc07c04 0x738ff07f01f80f80

def z1306 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7b15818f33613ff 0xbef62b031e66c27f

def z1307 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x08af83e00fc06c00 0xa115f07c01f80d80

def z1308 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0x1867ffffbfff8000 0x630cfffff7fff000

def z1309 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x5d2e63078c387ce5 0x2ba5cc60f1870f9c

def z1310 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x7c011bfff0000000 0x0f80237ffe000000

def z1311 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xcd3e43070c387ce5 0x79a7c860e1870f9c

def z1312 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83f7fc000fff90e7 0xf07eff8001fff21c

def z1313 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7c67fffff0000000 0x0f8cfffffe000000

def z1314 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7fd6a7fff0000000 0x0ffad4fffe000000

def z1315 : W := mkw 0x50c26947c43a24d4 0xca184d28f887449a 0x0000580700360000 0x00000b00e006c000

def z1316 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x82f7dc000ff78002 0xf05efb8001fef000

def z1317 : W := mkw 0x250582980ac01901 0x04a0b05301580320 0xbcff83f80cc07c04 0x779ff07f01980f80

def z1318 : W := mkw 0x01e000291152f3b9 0xe03c0005222a5e77 0x83f9fc0003fff3ff 0xf07f3f80007ffe7f

def z1319 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x02e7fc000fff8002 0xe05cff8001fff000

def z1320 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdf7e6707fc387ce5 0x7befcce0ff870f9c

def z1321 : W := mkw 0x0000002001004200 0x0000000400200840 0x082f03e00f006c00 0x2105e07c01e00d80

def z1322 : W := mkw 0x272596b81bc5db2b 0x24e4b2d70378bb65 0xbeff9ff87fc7ff1e 0xf7dff3ff0ff8ffe3

def z1323 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfffffffff0006004 0x3ffffffffe000c00

def z1324 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff0000085 0x1ffefffffe000010

def z1325 : W := mkw 0x50c26947c43a24d4 0xca184d28f887449a 0xf7d07807c03e13ff 0xdefa0f00f807c27f

def z1326 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefb958e74f367f9f 0xfdf72b1ce9e6cff3

def z1327 : W := mkw 0x38059fd6e0000000 0x0700b3fadc000000 0x7fd1bffff0000000 0x0ffa37fffe000000

def z1328 : W := mkw 0x58827d47e43824c4 0x8b104fa8fc870498 0x41007807803800e1 0x08200f00f007001c

def z1329 : W := mkw 0x7807ebd6e0000000 0x0f00fd7adc000000 0x7df7e3fff0000000 0x0fbefc7ffe000000

def z1330 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xecb958e74336639c 0xbd972b1ce866cc73

def z1331 : W := mkw 0x78026bd6e0000000 0x0f004d7adc000000 0x7ff6e7fff0000000 0x0ffedcfffe000000

def z1332 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0xbeffa7f8ffc9ff7e 0xf7dff4ff1ff93fef

def z1333 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0x997e63078c387c61 0x732fcc60f1870f8c

def z1334 : W := mkw 0x58a27d47f438a4ec 0xab144fa8fe87149d 0x43007c07f03980fb 0x08600f80fe07301f

def z1335 : W := mkw 0x38058bd6e0000000 0x0700b17adc000000 0x7c8183fff0000000 0x0f90307ffe000000

def z1336 : W := mkw 0x38000bd6e0000000 0x0700017adc000000 0xfc7e03fffc007c04 0x7f8fc07fff800f80

def z1337 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7ffffff3e0001 0x7ffeffffffe7c000

def z1338 : W := mkw 0x00800001043824c4 0x8010000020870498 0xdd7e43070c387ce5 0x7bafc860e1870f9c

def z1339 : W := mkw 0x3e059ed26a850002 0x07c0b3da4d50a000 0xefb1dcff73f78003 0xbdf63b9fee7ef000

def z1340 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdd7e63078c387fff 0xfbafcc60f1870fff

def z1341 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7d1bc18f3cf93ff 0xdefa37831e79f27f

def z1342 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbfffdbf80fc07f04 0xf7fffb7f01f80fe0

def z1343 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x6fb7dfff70000000 0x0df6fbffee000000

def z1344 : W := mkw 0x0000002001004200 0x0000000400200840 0xbc7e03e00c007f04 0x778fc07c01800fe0

def z1345 : W := mkw 0x0000002001004200 0x0000000400200840 0x9c7f03e00f007c04 0x738fe07c01e00f80

def z1346 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x8c3f03e00f006c04 0x3187e07c01e00d80

def z1347 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0xfff7fffff00813ff 0xdffefffffe01027f

def z1348 : W := mkw 0x1000084240000000 0x0200010848000000 0x7fd0a4fff0000000 0x0ffa149ffe000000

def z1349 : W := mkw 0x0000002001004200 0x0000000400200840 0xffff23e0cf087fff 0xffffe47c19e10fff

def z1350 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7fffffff60000 0xfffefffffffec000

def z1351 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbc4e83f80fc07f04 0xf789d07f01f80fe0

def z1352 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xe3b158e74336039b 0xbc762b1ce866c073

def z1353 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xec2958e74336639f 0xbd852b1ce866cc73

def z1354 : W := mkw 0x250002b80bc05b01 0x04a0005701780b60 0xbc7e03f80fc07f04 0xf78fc07f01f80fe0

def z1355 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0x3cff83f80fc07c00 0x679ff07f01f80f80

def z1356 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xfcff83f88fc07fe4 0xff9ff07f11f80ffc

def z1357 : W := mkw 0x0120000810409129 0x2024000102081225 0xf7f6a418fcc993ff 0xfefed4831f99327f

def z1358 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xc3f7fc00ffff8003 0xf87eff801ffff000

def z1359 : W := mkw 0x7e07ffd6eead0446 0x0fc0fffaddd5a088 0x7ff7fffffcc99c60 0x4ffeffffff99338c

def z1360 : W := mkw 0x252582b81bc0db29 0x24a4b05703781b65 0x186fa7f8bfc9fc60 0x630df4ff17f93f8c

def z1361 : W := mkw 0x7e07ffd6eead0006 0x0fc0fffaddd5a000 0xfff7ffffffc98000 0xfffefffffff93000

def z1362 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7cf7a7fff0000000 0x0f9ef4fffe000000

def z1363 : W := mkw 0x050000280bc05b01 0x00a0000501780b60 0xbcff03e00fc07f04 0xf79fe07c01f80fe0

def z1364 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0xf7f7fc18ffff839f 0xfefeff831ffff073

def z1365 : W := mkw 0x7e07ffd6ea850002 0x0fc0fffadd50a000 0xfff7ffffffc78002 0xfffefffffff8f000

def z1366 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x7ea7dffff0000000 0x0fd4fbfffe000000

def z1367 : W := mkw 0x10c0086341126290 0xc218010c68224c52 0xefd8a4e740c9e39f 0xddfb149ce8193c73

def z1368 : W := mkw 0x0000000000000000 0x0000000000000000 0xbcff03e00c007c04 0x779fe07c01800f80

def z1369 : W := mkw 0x7807ffd6e4280444 0x0f00fffadc850088 0x7ff7fffff0080060 0x0ffefffffe01000c

def z1370 : W := mkw 0x01e000291152f3b9 0xe03c0005222a5e77 0x8008000000c9f3ff 0xd001000000193e7f

def z1371 : W := mkw 0x0120000810409129 0x2024000102081225 0xffd8a718f0c9ffff 0xdffb14e31e193fff

def z1372 : W := mkw 0x7c07ffd6ea800000 0x0f80fffadd500000 0xffffffffffc07c04 0xfffffffffff80f80

def z1373 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83277c000fff8003 0xf064ef8001fff000

def z1374 : W := mkw 0x2005829000000000 0x0400b05200000000 0x082f03e00c006c00 0x2105e07c01800d80

def z1375 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x83b7dc000ff78003 0xb076fb8001fef000

def z1376 : W := mkw 0x250582b80bc05b01 0x04a0b05701780b60 0xbcff83f80fc07f9f 0xf79ff07f01f80ff3

def z1377 : W := mkw 0x7847ffd6e0020010 0x4f08fffadc004002 0x7ff7fffff006001a 0x0ffefffffe00c003

def z1378 : W := mkw 0x7c07ffd6ea800000 0x0f80fffadd500000 0x7ff7fffffcc00000 0x4ffeffffff980000

def z1379 : W := mkw 0x4607f4000ead0006 0x08c0fe8001d5a000 0x03a7fc000fff8003 0xa074ff8001fff000

def z1380 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xfdfee31f8c387ce5 0x7fbfdc63f1870f9c

def z1381 : W := mkw 0x240582b00b804a00 0x0480b05601700940 0x2cbf03e00f006c00 0x2597e07c01e00d80

def z1382 : W := mkw 0x7807ffd6e0000000 0x0f00fffadc000000 0x5b67fffff0000000 0x0b6cfffffe000000

def z1383 : W := mkw 0x01e000291152f3b9 0xe03c0005222a5e77 0x80080000033673ff 0xb00100000066ce7f

def z1384 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdf7e67078c39fce7 0x7befcce0f1873f9c

def z1385 : W := mkw 0x40826105843824c4 0x88104c20b0870498 0xdf7e7b078c3e7ce7 0x7befcf60f187cf9c

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z6,z1,z7,z2,z3,z8]),(0,[z9,z0,z1,z2,z3,z8,z10]),(0,[z11,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z13,z2,z3,z8,z5]),(0,[z0,z1,z2,z14,z3,z8,z5])],[(0,[z15,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z17,z2,z3,z8,z5]),(0,[z18,z0,z1,z2,z3,z8,z5]),(0,[z0,z19,z1,z2,z3,z8,z20]),(0,[z21,z0,z1,z22,z3,z8,z5]),(0,[z23,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z24,z3,z8,z5])],[(0,[z25,z0,z26,z2,z3,z8,z5]),(0,[z21,z0,z1,z2,z3,z8,z27]),(0,[z0,z28,z1,z2,z3,z8,z5])],[(0,[z29,z0,z1,z30,z3,z8,z5]),(1,[z18,z0,z1,z2,z3,z12]),(0,[z0,z31,z1,z2,z3,z8,z5]),(0,[z0,z1,z32,z2,z3,z8,z12]),(0,[z0,z1,z2,z33,z3,z8,z5]),(0,[z0,z1,z2,z34,z3,z8,z12])],[(1,[z29,z1,z30,z3,z8,z5]),(0,[z35,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z36,z5]),(0,[z0,z1,z2,z37,z3,z8,z38]),(0,[z39,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z41,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z20,z12]),(0,[z0,z1,z2,z3,z42,z8,z5]),(0,[z0,z1,z2,z3,z8,z43,z12]),(0,[z0,z1,z2,z44,z40,z3,z8])],[(0,[z45,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z46,z8,z5]),(0,[z0,z1,z47,z16,z3,z8,z5]),(0,[z0,z1,z2,z48,z3,z8,z5]),(0,[z49,z9,z0,z1,z2,z3,z8]),(0,[z0,z1,z2,z50,z3,z8,z5]),(0,[z0,z1,z2,z14,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z51])],[(0,[z0,z52,z1,z30,z3,z8,z5]),(0,[z53,z0,z1,z54,z3,z8,z5]),(0,[z53,z0,z1,z2,z3,z55,z5]),(0,[z0,z1,z2,z56,z3,z8,z5]),(0,[z0,z1,z57,z2,z3,z8,z5])],[(0,[z0,z1,z2,z40,z3,z58,z8]),(0,[z53,z0,z1,z2,z3,z8,z59]),(0,[z0,z1,z2,z3,z60,z8,z5]),(0,[z11,z0,z1,z61,z3,z8,z5]),(1,[z39,z0,z2,z8,z62,z5]),(1,[z0,z1,z3,z8,z63,z5]),(0,[z18,z0,z1,z2,z64,z8,z5]),(0,[z0,z65,z1,z2,z3,z8,z66]),(0,[z0,z1,z2,z67,z3,z8,z5])]],
   [[(0,[z68,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z69,z8,z5]),(0,[z0,z1,z16,z2,z40,z3,z8]),(0,[z0,z70,z1,z2,z40,z3,z8])],[(0,[z71,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z72,z8,z5]),(0,[z0,z1,z2,z73,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z74,z5]),(0,[z0,z75,z1,z2,z3,z8,z5]),(0,[z0,z76,z1,z2,z3,z8,z5])],[(0,[z77,z0,z1,z78,z3,z8,z5]),(1,[z0,z79,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z80]),(0,[z0,z1,z2,z81,z3,z8,z5]),(0,[z21,z0,z1,z82,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z5,z83]),(0,[z1,z2,z30,z3,z58,z8,z5]),(0,[z0,z1,z16,z22,z3,z8,z5]),(0,[z0,z1,z84,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z85,z5]),(0,[z0,z1,z2,z3,z8,z86,z5]),(0,[z0,z1,z22,z2,z8,z87,z5]),(0,[z0,z1,z2,z88,z3,z8,z5])],[(1,[z0,z1,z89,z3,z8,z5]),(0,[z15,z90,z1,z2,z3,z8,z5]),(0,[z91,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z92,z5]),(0,[z0,z1,z2,z3,z8,z5,z93]),(0,[z25,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z2,z3,z94,z8,z5]),(0,[z95,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z96,z5]),(0,[z0,z1,z2,z3,z97,z8,z98]),(1,[z0,z99,z1,z2,z3,z5]),(0,[z0,z1,z2,z40,z3,z5,z12])],[(0,[z0,z1,z30,z3,z8,z100,z5]),(0,[z0,z1,z2,z3,z8,z101,z5])],[(0,[z0,z1,z102,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z103,z5]),(0,[z104,z0,z1,z2,z3,z8,z5]),(0,[z0,z105,z1,z2,z3,z8,z5]),(0,[z106,z0,z1,z2,z97,z8,z5])],[(1,[z0,z70,z2,z107,z8,z5]),(1,[z0,z65,z1,z3,z96,z5]),(0,[z0,z1,z2,z108,z3,z8,z5])]],
   [[(1,[z0,z1,z30,z3,z8,z12]),(0,[z0,z109,z1,z30,z3,z8,z5]),(0,[z53,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z2,z3,z8,z5,z110]),(0,[z0,z1,z2,z3,z8,z5,z111]),(0,[z0,z99,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z37,z3,z8,z5]),(0,[z112,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z16,z3,z8,z113,z5]),(0,[z0,z1,z2,z40,z3,z55,z8]),(0,[z21,z0,z1,z3,z8,z87,z5]),(0,[z114,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z30,z30,z3,z8,z5]),(0,[z0,z1,z115,z2,z3,z8,z5]),(0,[z116,z0,z117,z2,z3,z8,z5]),(0,[z0,z1,z118,z3,z8,z96,z5]),(1,[z0,z1,z82,z3,z8,z119]),(0,[z0,z1,z2,z3,z8,z120,z5]),(0,[z0,z121,z1,z2,z3,z8,z122])],[(0,[z0,z1,z16,z34,z3,z8,z5]),(1,[z0,z1,z2,z3,z96,z12])],[(1,[z0,z1,z2,z3,z8,z123]),(0,[z15,z0,z7,z2,z3,z8,z5]),(0,[z116,z0,z1,z2,z124,z8,z5]),(0,[z0,z1,z2,z125,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z62]),(0,[z126,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z127,z5]),(0,[z0,z1,z2,z37,z3,z8,z12])],[(0,[z0,z121,z1,z16,z3,z8,z5]),(1,[z0,z128,z2,z3,z8,z5]),(0,[z129,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z130,z3,z8]),(0,[z18,z0,z1,z2,z3,z8,z131]),(1,[z0,z1,z2,z3,z8,z132]),(0,[z0,z1,z2,z133,z3,z8,z5]),(1,[z0,z1,z2,z3,z134,z5])],[(0,[z0,z1,z2,z135,z3,z8,z5]),(0,[z0,z109,z1,z136,z3,z8,z5]),(0,[z49,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z40,z3,z8])]],
   [[(0,[z137,z0,z1,z2,z3,z8,z5]),(0,[z21,z0,z1,z2,z8,z87,z5]),(0,[z138,z0,z1,z2,z3,z8,z5])],[(1,[z0,z139,z1,z2,z3,z8]),(0,[z0,z90,z1,z16,z3,z8,z5]),(0,[z140,z0,z1,z2,z3,z8,z5]),(0,[z141,z0,z1,z30,z3,z8,z5]),(0,[z9,z0,z1,z16,z3,z8,z5]),(0,[z142,z0,z1,z16,z3,z8,z5]),(0,[z143,z0,z1,z2,z3,z80,z5]),(0,[z0,z1,z117,z2,z3,z8,z5]),(0,[z0,z1,z2,z144,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z5,z145]),(0,[z146,z0,z1,z2,z3,z8,z5]),(0,[z147,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z148,z3,z8,z12]),(0,[z0,z149,z1,z2,z3,z8,z5]),(0,[z0,z1,z150,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z151,z5]),(0,[z0,z90,z2,z3,z8,z5,z152]),(0,[z18,z0,z1,z30,z3,z8,z5]),(0,[z0,z153,z1,z2,z3,z8,z5]),(0,[z0,z154,z1,z2,z3,z8,z5]),(0,[z0,z155,z1,z2,z3,z8,z5]),(0,[z156,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z27]),(0,[z0,z1,z32,z2,z3,z96,z5]),(0,[z157,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z26,z2,z3,z8,z5]),(1,[z0,z1,z158,z3,z8,z5]),(0,[z0,z1,z2,z3,z46,z8,z159]),(0,[z0,z1,z2,z160,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z5,z161]),(0,[z0,z1,z2,z3,z162,z8,z5]),(0,[z0,z1,z2,z163,z3,z8,z5]),(0,[z164,z0,z1,z2,z3,z8,z5]),(0,[z53,z0,z1,z165,z3,z8,z5]),(0,[z0,z1,z2,z3,z55,z46,z5]),(0,[z11,z0,z1,z118,z3,z8,z5]),(0,[z0,z1,z2,z107,z3,z166,z5]),(0,[z18,z0,z167,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z159]),(0,[z168,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z169,z5]),(0,[z141,z0,z1,z2,z170,z8,z5]),(0,[z0,z1,z2,z3,z8,z171,z5]),(0,[z0,z1,z2,z3,z8,z12,z172])],[(0,[z0,z1,z2,z3,z8,z173,z5]),(0,[z0,z1,z174,z2,z3,z8,z5]),(0,[z175,z0,z1,z2,z3,z8,z5]),(0,[z0,z176,z1,z2,z3,z8,z5]),(0,[z0,z1,z3,z97,z8,z96,z5])],[(0,[z53,z0,z1,z2,z177,z8,z5]),(0,[z0,z1,z2,z178,z3,z8,z5]),(1,[z49,z0,z2,z3,z8,z20])]],
   [[(0,[z143,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z179,z5]),(0,[z0,z1,z32,z118,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z96]),(0,[z0,z1,z82,z2,z40,z3,z8])],[(0,[z0,z1,z2,z3,z8,z180,z5]),(0,[z11,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z181,z2,z3,z8,z5]),(0,[z39,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z182,z5]),(0,[z0,z1,z2,z3,z183,z8,z5]),(0,[z0,z1,z2,z44,z3,z8,z5])],[(0,[z77,z15,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z184,z8,z5]),(1,[z185,z1,z30,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z5,z186]),(0,[z0,z167,z1,z16,z3,z8,z5]),(0,[z187,z0,z1,z2,z3,z8,z5])],[(0,[z21,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z188,z5]),(0,[z189,z0,z1,z2,z3,z8,z5]),(0,[z0,z190,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z191])],[(1,[z192,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z40,z148,z3,z8]),(0,[z0,z1,z2,z193,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z194,z5]),(0,[z0,z1,z32,z2,z40,z3,z8]),(0,[z0,z1,z82,z2,z3,z195,z5]),(0,[z0,z196,z1,z2,z34,z3,z5])],[(0,[z77,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z16,z2,z3,z8,z5]),(0,[z0,z1,z16,z37,z3,z8,z5]),(0,[z143,z0,z1,z2,z3,z8,z12]),(1,[z0,z1,z2,z197,z3,z8]),(0,[z198,z0,z1,z2,z3,z8,z5]),(0,[z0,z70,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z199,z3,z8,z5]),(0,[z0,z1,z2,z3,z200,z8,z5]),(0,[z0,z1,z2,z3,z8,z27,z5]),(0,[z0,z1,z2,z3,z97,z43,z5]),(0,[z0,z1,z2,z3,z8,z201,z5]),(0,[z0,z1,z202,z2,z3,z8,z5])],[(0,[z39,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z63,z5]),(0,[z0,z1,z2,z3,z8,z203,z5]),(0,[z0,z1,z2,z204,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z205,z5]),(0,[z53,z143,z1,z2,z3,z8,z5]),(0,[z116,z0,z19,z1,z2,z3,z8]),(0,[z206,z0,z1,z2,z3,z8,z5]),(0,[z39,z0,z2,z3,z8,z62,z5]),(1,[z0,z121,z1,z2,z3,z12])]],
   [[(0,[z0,z1,z2,z3,z8,z123,z5]),(0,[z0,z121,z1,z30,z3,z8,z5]),(0,[z0,z1,z22,z30,z3,z8,z5]),(0,[z0,z1,z2,z207,z3,z8,z5]),(0,[z0,z1,z2,z208,z3,z8,z5]),(0,[z18,z0,z1,z209,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z152,z12]),(0,[z0,z65,z1,z2,z3,z97,z5]),(0,[z210,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z30,z3,z8,z5,z119]),(0,[z25,z0,z1,z2,z3,z8,z5]),(0,[z185,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z92,z12]),(0,[z0,z1,z2,z40,z3,z8,z43]),(0,[z0,z211,z1,z2,z3,z8,z5]),(0,[z0,z212,z1,z2,z3,z8,z5])],[(0,[z0,z1,z30,z3,z55,z8,z5]),(0,[z0,z1,z2,z3,z8,z213,z5]),(0,[z0,z1,z16,z2,z3,z8,z12]),(1,[z25,z1,z2,z58,z8,z5]),(0,[z141,z0,z1,z2,z107,z8,z5]),(0,[z0,z1,z2,z3,z8,z100,z12]),(0,[z214,z0,z1,z2,z3,z8,z12])],[(0,[z9,z0,z1,z30,z3,z8,z5]),(0,[z142,z0,z1,z30,z3,z8,z5]),(0,[z215,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z216]),(0,[z0,z1,z82,z2,z3,z8,z92])],[(1,[z0,z6,z1,z2,z3,z8]),(0,[z0,z1,z115,z30,z3,z8,z5]),(0,[z217,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z218,z5]),(0,[z0,z1,z82,z2,z3,z8,z119]),(0,[z0,z1,z2,z3,z219,z8,z5]),(0,[z220,z0,z1,z2,z3,z8,z12]),(0,[z221,z0,z1,z2,z40,z3,z8])],[(0,[z53,z0,z1,z2,z3,z8,z5]),(0,[z142,z0,z1,z2,z37,z8,z5])],[(0,[z222,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z223]),(0,[z0,z1,z2,z3,z8,z224,z5]),(0,[z225,z0,z1,z2,z3,z8,z5]),(0,[z0,z196,z1,z2,z3,z97,z5]),(0,[z226,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z7,z16,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z227,z5]),(0,[z0,z1,z228,z2,z3,z8,z5]),(0,[z21,z0,z1,z3,z8,z92,z5]),(0,[z0,z1,z2,z3,z8,z229,z5])]],
   [[(0,[z0,z1,z2,z230,z3,z8,z5]),(0,[z231,z0,z1,z2,z3,z8,z5]),(0,[z141,z0,z121,z1,z2,z3,z5])],[(0,[z77,z0,z1,z2,z230,z8,z5]),(0,[z0,z1,z30,z3,z8,z62,z5]),(0,[z49,z0,z1,z30,z3,z8,z5]),(1,[z0,z1,z30,z40,z3,z8]),(0,[z0,z1,z2,z232,z3,z8,z5]),(0,[z0,z1,z3,z8,z63,z62,z5]),(0,[z0,z1,z2,z3,z8,z233,z5]),(1,[z0,z1,z2,z234,z3,z8])],[(0,[z53,z0,z1,z2,z3,z8,z12]),(1,[z0,z1,z2,z3,z235,z5]),(0,[z18,z0,z121,z1,z2,z3,z5]),(0,[z0,z1,z2,z118,z3,z8,z5]),(0,[z0,z1,z236,z2,z3,z8,z5]),(0,[z237,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z238,z2,z3,z8,z5]),(0,[z0,z1,z2,z107,z58,z8,z5]),(0,[z0,z1,z2,z3,z8,z239,z5]),(0,[z0,z1,z2,z3,z46,z8,z5]),(0,[z240,z0,z1,z2,z3,z8,z5])],[(0,[z0,z167,z1,z30,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z241,z5]),(0,[z0,z1,z30,z3,z97,z8,z5]),(0,[z0,z1,z2,z242,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z243,z5]),(0,[z0,z244,z1,z2,z40,z3,z8])],[(0,[z0,z167,z7,z2,z3,z8,z5]),(0,[z21,z0,z1,z30,z3,z8,z5]),(0,[z35,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z245,z5])],[(0,[z0,z1,z246,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z247,z8,z5]),(0,[z0,z1,z2,z248,z3,z8,z5]),(0,[z249,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z250,z3,z8,z5]),(0,[z112,z0,z1,z2,z40,z3,z8])],[(0,[z77,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z30,z251,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z252]),(0,[z0,z1,z253,z2,z3,z8,z5]),(0,[z21,z0,z1,z2,z3,z86,z5]),(0,[z0,z1,z2,z254,z3,z8,z5]),(0,[z0,z1,z2,z118,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z255])]],
   [[(0,[z77,z0,z7,z2,z3,z8,z5]),(0,[z0,z1,z2,z256,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z257,z5]),(1,[z0,z1,z2,z3,z8,z122]),(0,[z0,z1,z2,z3,z8,z186,z12]),(0,[z0,z1,z2,z40,z3,z8,z8])],[(0,[z258,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z43,z5,z12])],[(0,[z0,z1,z2,z3,z184,z8,z5]),(0,[z0,z1,z16,z3,z8,z100,z5]),(0,[z0,z259,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z260,z5]),(1,[z0,z1,z2,z64,z8,z5]),(0,[z0,z1,z2,z3,z97,z5,z12]),(0,[z0,z261,z1,z2,z3,z8,z5]),(0,[z0,z262,z1,z2,z3,z8,z5])],[(0,[z0,z263,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z158,z3,z8,z5]),(0,[z0,z1,z2,z264,z3,z8,z5]),(0,[z0,z1,z2,z3,z265,z8,z5])],[(0,[z0,z1,z266,z2,z3,z8,z5]),(1,[z0,z1,z16,z3,z8,z5]),(0,[z143,z0,z1,z2,z3,z55,z5]),(0,[z18,z143,z0,z1,z2,z3,z5]),(0,[z267,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z5,z268]),(0,[z0,z1,z2,z269,z3,z8,z5]),(0,[z0,z1,z82,z2,z3,z8,z5])],[(0,[z270,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z177,z8,z5]),(0,[z11,z0,z1,z2,z3,z8,z5]),(1,[z0,z167,z1,z2,z3,z12])],[]],
   [[(1,[z0,z1,z2,z3,z8,z271])],[(0,[z15,z0,z90,z2,z3,z8,z5]),(1,[z0,z1,z16,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z272,z5]),(0,[z0,z1,z2,z3,z8,z273,z5]),(0,[z0,z1,z274,z2,z3,z8,z5]),(0,[z0,z2,z3,z8,z20,z5,z152]),(0,[z0,z1,z2,z3,z8,z5,z119]),(0,[z0,z275,z1,z2,z40,z3,z8]),(0,[z276,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z37,z8,z5,z186]),(0,[z0,z1,z2,z34,z3,z8,z5])],[(0,[z0,z277,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z278]),(0,[z0,z1,z279,z2,z3,z8,z5]),(0,[z0,z1,z2,z37,z3,z8,z10]),(0,[z0,z1,z2,z3,z8,z20,z5]),(0,[z0,z1,z2,z3,z20,z280,z5]),(1,[z0,z281,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z8,z43,z5]),(0,[z0,z1,z2,z3,z282,z8,z5]),(0,[z0,z1,z283,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z284,z5]),(0,[z0,z285,z1,z2,z3,z8,z5]),(0,[z286,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z287]),(0,[z0,z1,z2,z3,z8,z288,z5])],[(0,[z0,z1,z2,z3,z43,z80,z5]),(0,[z0,z1,z2,z3,z55,z8,z289]),(0,[z290,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z291,z2,z3,z8,z5]),(0,[z292,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z293,z3,z8,z5]),(0,[z21,z0,z1,z2,z3,z294,z5]),(1,[z0,z1,z2,z40,z3,z12]),(0,[z0,z1,z2,z40,z295,z3,z8]),(0,[z0,z1,z296,z2,z40,z3,z8])],[(0,[z77,z1,z7,z2,z3,z8,z5]),(0,[z297,z0,z1,z2,z3,z8,z5]),(0,[z53,z0,z79,z2,z3,z8,z5]),(0,[z143,z0,z1,z2,z40,z3,z8]),(0,[z0,z298,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z299,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z255])],[(0,[z0,z1,z2,z3,z8,z227,z5]),(0,[z0,z1,z16,z118,z3,z8,z5]),(0,[z185,z1,z2,z148,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z300,z5]),(0,[z9,z1,z2,z3,z8,z38,z5]),(0,[z21,z11,z0,z1,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z301,z5]),(0,[z0,z1,z2,z3,z8,z5,z302]),(0,[z0,z1,z2,z234,z170,z3,z8])]],
   [[(0,[z0,z303,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z304,z3,z8,z5]),(1,[z0,z109,z61,z3,z8,z5])],[(0,[z0,z1,z30,z40,z3,z8,z5]),(0,[z0,z1,z32,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z62,z5]),(1,[z0,z1,z2,z3,z8,z131]),(0,[z0,z1,z2,z3,z8,z87,z5]),(1,[z0,z1,z2,z3,z43,z12]),(0,[z221,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z305,z3,z8,z5])],[(0,[z0,z1,z30,z3,z8,z80,z5]),(0,[z141,z0,z1,z16,z3,z8,z5]),(0,[z185,z0,z1,z2,z40,z3,z8]),(0,[z21,z0,z109,z1,z3,z8,z5]),(0,[z18,z306,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z307,z3,z8,z5]),(0,[z0,z19,z1,z2,z40,z3,z8])],[(0,[z308,z0,z1,z2,z3,z8,z5])],[(0,[z309,z0,z1,z2,z3,z8,z5]),(0,[z18,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z3,z8,z5]),(0,[z310,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z311,z8,z5]),(1,[z106,z0,z1,z2,z8,z5]),(0,[z0,z275,z1,z2,z3,z8,z92])],[(0,[z0,z1,z2,z3,z8,z312,z5]),(0,[z0,z1,z2,z3,z8,z10,z12]),(0,[z0,z1,z2,z313,z3,z8,z5]),(0,[z0,z1,z2,z3,z314,z8,z5]),(0,[z0,z1,z2,z315,z3,z8,z5]),(0,[z0,z275,z1,z2,z3,z8,z119])],[(1,[z0,z1,z30,z3,z8,z5]),(0,[z0,z316,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z148,z8,z43,z5]),(0,[z0,z1,z2,z3,z8,z5,z317]),(0,[z0,z1,z2,z3,z8,z62,z12]),(0,[z0,z1,z2,z3,z8,z87,z12]),(0,[z0,z1,z2,z3,z8,z66,z5]),(0,[z0,z318,z1,z2,z3,z8,z5])],[(0,[z319,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z5,z186]),(0,[z0,z19,z1,z2,z3,z8,z186]),(0,[z0,z1,z2,z3,z8,z92,z186])]],
   [[(0,[z0,z7,z2,z3,z8,z100,z5]),(0,[z0,z1,z2,z30,z40,z3,z8]),(1,[z53,z1,z2,z3,z80,z5]),(0,[z0,z167,z1,z2,z3,z100,z5]),(0,[z320,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z86,z5]),(0,[z0,z1,z2,z40,z3,z8,z119])],[(0,[z0,z1,z16,z3,z8,z321,z5]),(0,[z185,z0,z1,z2,z148,z8,z5]),(0,[z0,z1,z322,z2,z3,z8,z5]),(0,[z0,z65,z1,z3,z8,z96,z5]),(1,[z0,z196,z1,z2,z40,z3]),(0,[z0,z244,z1,z2,z3,z8,z5])],[(0,[z53,z0,z128,z2,z3,z8,z5]),(0,[z0,z1,z2,z323,z3,z8,z5]),(0,[z0,z1,z324,z2,z3,z8,z5]),(0,[z141,z0,z1,z2,z3,z43,z5]),(0,[z0,z1,z2,z325,z3,z8,z5])],[(0,[z77,z0,z1,z326,z3,z8,z5]),(0,[z0,z1,z2,z2,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z38,z5]),(0,[z0,z1,z2,z327,z3,z8,z5])],[(0,[z328,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z329,z2,z3,z8,z5]),(0,[z0,z196,z1,z2,z3,z80,z5]),(0,[z0,z1,z2,z3,z8,z330,z5]),(0,[z0,z1,z2,z3,z8,z5,z289]),(0,[z331,z0,z1,z2,z3,z8,z5]),(0,[z18,z0,z1,z2,z3,z43,z5]),(0,[z0,z332,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z97,z333,z8,z5]),(0,[z0,z1,z2,z251,z3,z8,z12])],[(0,[z334,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z152,z10]),(0,[z0,z1,z2,z40,z3,z8,z38]),(0,[z49,z0,z1,z2,z3,z8,z152])],[(0,[z0,z1,z16,z3,z8,z5,z119]),(0,[z25,z0,z1,z2,z148,z8,z5]),(1,[z0,z1,z335,z3,z8,z5]),(0,[z18,z0,z1,z2,z3,z46,z5]),(0,[z0,z121,z167,z1,z2,z3,z5]),(0,[z0,z1,z2,z40,z37,z3,z8])],[(0,[z15,z0,z1,z336,z3,z8,z5]),(0,[z337,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z20,z5]),(0,[z0,z1,z16,z3,z8,z43,z5]),(0,[z0,z1,z2,z3,z8,z338,z5]),(0,[z0,z1,z61,z3,z8,z96,z5]),(0,[z0,z339,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z325,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z12])]],
   [[(0,[z0,z1,z2,z340,z3,z8,z5]),(0,[z11,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z341,z5]),(0,[z0,z1,z2,z148,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z342]),(0,[z0,z1,z2,z40,z170,z3,z8])],[(0,[z0,z1,z102,z16,z3,z8,z5]),(0,[z0,z343,z1,z2,z3,z8,z5]),(1,[z0,z1,z344,z3,z8,z5])],[(0,[z345,z0,z1,z2,z3,z8,z5]),(1,[z1,z30,z3,z58,z8,z5]),(0,[z53,z1,z2,z3,z8,z80,z5]),(1,[z0,z1,z346,z3,z8,z5]),(0,[z0,z2,z107,z3,z8,z62,z5]),(1,[z0,z19,z2,z3,z8,z152]),(0,[z0,z65,z1,z2,z3,z8,z12])],[(0,[z0,z1,z32,z30,z3,z8,z5]),(1,[z0,z1,z209,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z100]),(0,[z0,z347,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z348,z5]),(0,[z0,z1,z2,z37,z251,z3,z8]),(0,[z0,z1,z2,z349,z3,z8,z5])],[(0,[z185,z1,z2,z30,z3,z8,z5]),(0,[z0,z1,z30,z136,z3,z8,z5]),(0,[z0,z1,z79,z2,z3,z8,z5]),(0,[z1,z2,z3,z55,z8,z80,z5]),(0,[z0,z1,z2,z350,z3,z8,z5]),(0,[z0,z19,z1,z2,z37,z3,z8])],[(0,[z351,z0,z1,z2,z3,z8,z5]),(0,[z18,z0,z196,z1,z2,z3,z5]),(0,[z0,z1,z2,z352,z40,z3,z8])],[(0,[z77,z0,z1,z2,z3,z353,z5]),(0,[z0,z1,z17,z30,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z62,z5]),(0,[z0,z1,z16,z3,z8,z87,z5]),(0,[z354,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z294,z5]),(0,[z0,z275,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z355])],[(0,[z77,z0,z1,z2,z3,z8,z145]),(0,[z0,z1,z2,z356,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z357]),(0,[z0,z1,z2,z3,z8,z5,z358]),(0,[z0,z1,z82,z118,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z58,z8,z43,z5]),(0,[z0,z1,z61,z2,z3,z8,z12]),(0,[z359,z0,z1,z2,z3,z8,z5]),(0,[z0,z196,z1,z2,z3,z8,z12]),(0,[z360,z0,z1,z2,z40,z3,z8])],[(0,[z39,z0,z1,z2,z8,z62,z5])],[(0,[z361,z0,z1,z2,z3,z8,z5]),(0,[z49,z0,z1,z16,z3,z8,z5]),(1,[z0,z1,z16,z40,z3,z8]),(0,[z362,z0,z1,z2,z3,z8,z5]),(0,[z116,z0,z1,z2,z40,z3,z8]),(0,[z0,z363,z1,z2,z3,z8,z5]),(0,[z0,z1,z296,z2,z3,z8,z5])],[(0,[z137,z0,z1,z16,z3,z8,z5]),(0,[z0,z128,z1,z2,z3,z8,z5]),(0,[z0,z364,z1,z2,z3,z8,z5]),(0,[z0,z275,z1,z2,z3,z8,z12]),(0,[z0,z1,z365,z2,z3,z8,z5])],[(1,[z0,z1,z78,z3,z8,z5]),(0,[z0,z1,z2,z3,z366,z8,z5]),(0,[z0,z1,z2,z3,z8,z367,z5]),(0,[z0,z1,z2,z3,z368,z8,z5]),(0,[z0,z1,z369,z2,z3,z8,z5])],[(0,[z77,z0,z90,z2,z3,z8,z5]),(0,[z0,z370,z1,z2,z3,z8,z5]),(0,[z0,z70,z1,z2,z8,z62,z5]),(0,[z0,z1,z2,z40,z107,z3,z8]),(0,[z0,z1,z371,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z186,z119]),(0,[z0,z1,z2,z170,z3,z43,z5])],[(1,[z0,z1,z372,z3,z8,z5]),(0,[z18,z0,z1,z335,z3,z8,z5]),(0,[z0,z1,z373,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z374,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z12]),(0,[z0,z1,z2,z375,z3,z8,z5])],[(1,[z77,z7,z2,z3,z8,z5]),(0,[z376,z0,z1,z2,z3,z8,z5]),(0,[z185,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z377]),(0,[z0,z1,z2,z58,z8,z62,z5]),(0,[z0,z1,z2,z3,z8,z80,z12]),(0,[z378,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z379,z2,z3,z8,z5]),(0,[z0,z19,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z92,z5])]],
   [[(0,[z29,z0,z1,z2,z3,z8,z12]),(0,[z214,z0,z1,z2,z3,z8,z5]),(0,[z0,z70,z2,z107,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z100,z5]),(0,[z0,z380,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z381,z3,z8,z5])],[(0,[z0,z1,z30,z382,z3,z8,z5]),(0,[z0,z383,z1,z2,z3,z8,z5]),(0,[z141,z0,z1,z2,z58,z8,z5]),(0,[z0,z384,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z385,z5]),(0,[z0,z386,z1,z2,z3,z8,z5]),(0,[z18,z0,z1,z2,z3,z5,z12])],[(0,[z1,z7,z2,z3,z8,z80,z5]),(0,[z0,z1,z387,z30,z3,z8,z5]),(1,[z116,z1,z2,z3,z8,z10]),(0,[z220,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z22,z2,z118,z8,z5]),(0,[z388,z0,z1,z2,z3,z8,z5])],[(0,[z35,z1,z2,z3,z58,z8,z5]),(0,[z143,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z389,z5]),(0,[z0,z1,z2,z390,z3,z8,z5]),(0,[z0,z1,z2,z3,z391,z8,z5])],[(0,[z392,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z5,z10]),(0,[z39,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z5,z12]),(0,[z0,z19,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z393,z5])],[(0,[z15,z143,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z30,z3,z8,z5]),(0,[z0,z1,z16,z148,z3,z8,z5]),(0,[z0,z167,z1,z2,z3,z43,z5]),(0,[z0,z1,z118,z3,z8,z92,z5])],[(0,[z0,z1,z30,z107,z3,z8,z5]),(0,[z0,z1,z2,z394,z3,z8,z5]),(1,[z0,z1,z2,z395,z8,z5]),(0,[z396,z0,z1,z2,z3,z8,z5]),(0,[z49,z0,z1,z2,z3,z8,z20]),(1,[z0,z1,z2,z3,z8,z98]),(0,[z0,z1,z82,z3,z8,z5,z119]),(0,[z397,z0,z1,z2,z3,z8,z5])],[(0,[z0,z398,z1,z2,z3,z8,z5]),(0,[z11,z0,z2,z136,z3,z8,z5]),(0,[z399,z0,z1,z2,z3,z8,z5]),(0,[z0,z167,z1,z2,z3,z46,z5]),(0,[z0,z281,z1,z2,z3,z8,z5]),(0,[z0,z400,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z401,z3,z8,z5]),(0,[z0,z1,z402,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z16,z16,z3,z8,z5]),(0,[z0,z70,z1,z16,z3,z8,z5]),(0,[z143,z1,z2,z3,z55,z8,z5]),(0,[z0,z1,z2,z3,z8,z38,z12]),(0,[z0,z1,z2,z3,z8,z403,z5]),(0,[z0,z70,z109,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z404,z5])],[(0,[z0,z1,z30,z3,z405,z8,z5]),(0,[z0,z406,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z407]),(0,[z141,z0,z121,z1,z2,z8,z5])],[(0,[z0,z1,z2,z30,z3,z8,z12]),(0,[z0,z408,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z353,z5]),(0,[z0,z1,z2,z3,z409,z8,z5]),(0,[z410,z0,z1,z2,z3,z8,z5]),(0,[z53,z0,z1,z2,z3,z8,z252]),(0,[z116,z0,z1,z2,z3,z8,z38]),(0,[z0,z411,z1,z2,z3,z8,z5]),(0,[z412,z0,z1,z2,z3,z8,z5])],[(0,[z0,z7,z2,z3,z8,z62,z5]),(0,[z0,z1,z2,z413,z3,z8,z5]),(0,[z0,z1,z30,z170,z3,z8,z5]),(0,[z25,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z20,z10]),(0,[z0,z1,z2,z414,z3,z8,z5]),(0,[z0,z1,z2,z251,z3,z134,z5]),(0,[z0,z1,z415,z2,z3,z8,z5])],[(0,[z49,z0,z7,z2,z3,z8,z5]),(0,[z137,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z416,z3,z8,z5]),(0,[z417,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z418,z5]),(0,[z0,z109,z1,z2,z3,z8,z12]),(1,[z0,z1,z2,z333,z8,z5])],[(0,[z0,z1,z16,z40,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z419,z5]),(0,[z9,z0,z19,z1,z2,z3,z8]),(1,[z0,z1,z22,z118,z8,z5]),(0,[z0,z121,z1,z2,z3,z5,z12])],[(0,[z0,z6,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z80,z5]),(0,[z0,z1,z2,z3,z420,z8,z5]),(0,[z0,z196,z1,z2,z3,z55,z5]),(1,[z0,z421,z2,z3,z8,z5]),(0,[z422,z0,z1,z2,z3,z8,z5]),(0,[z21,z0,z1,z2,z118,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z132]),(0,[z0,z65,z1,z32,z3,z8,z5]),(0,[z423,z0,z1,z2,z3,z8,z5])]],
   [[(0,[z0,z0,z1,z2,z3,z8,z5]),(0,[z15,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z30,z3,z8,z5,z152]),(0,[z53,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z424,z2,z3,z8,z5])],[(0,[z0,z1,z2,z136,z3,z8,z12]),(0,[z425,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z426]),(0,[z0,z1,z415,z2,z3,z8,z12]),(0,[z0,z427,z1,z2,z40,z3,z8])],[(0,[z428,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z352,z3,z8,z5]),(0,[z429,z0,z1,z2,z3,z8,z5]),(0,[z18,z0,z1,z2,z3,z100,z5]),(0,[z0,z1,z2,z3,z430,z8,z5]),(0,[z0,z1,z2,z3,z8,z431,z5]),(0,[z0,z1,z2,z251,z3,z8,z186]),(0,[z0,z1,z432,z2,z3,z8,z5])],[(0,[z142,z0,z1,z2,z58,z8,z5]),(0,[z0,z65,z1,z2,z40,z3,z8]),(0,[z0,z1,z2,z3,z8,z433,z5])],[(0,[z0,z1,z16,z3,z8,z92,z5]),(0,[z0,z109,z1,z61,z3,z8,z5]),(0,[z0,z1,z2,z3,z434,z8,z5]),(0,[z0,z1,z2,z107,z8,z43,z5]),(1,[z0,z1,z2,z34,z3,z12])],[(0,[z143,z0,z1,z30,z3,z8,z5]),(0,[z290,z0,z1,z3,z8,z62,z5]),(1,[z306,z1,z2,z3,z8,z5]),(0,[z0,z1,z32,z3,z97,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z186]),(0,[z360,z0,z1,z2,z3,z8,z5])],[(0,[z39,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z435,z8,z5]),(0,[z0,z1,z238,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z80,z100,z5]),(1,[z0,z1,z2,z327,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z159]),(0,[z21,z176,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z321,z5]),(1,[z0,z1,z279,z3,z8,z5]),(0,[z116,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z436,z3,z8,z5]),(0,[z21,z0,z437,z2,z3,z8,z5]),(0,[z0,z121,z1,z67,z3,z8,z5])]],
   [[],[(0,[z438,z0,z1,z2,z3,z8,z5]),(0,[z185,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z382,z3,z8,z5]),(0,[z0,z121,z1,z2,z3,z80,z5]),(0,[z0,z1,z2,z3,z8,z5,z439]),(0,[z0,z440,z1,z2,z3,z8,z5]),(0,[z0,z1,z61,z2,z40,z3,z8]),(0,[z0,z1,z2,z3,z8,z5,z191]),(0,[z0,z1,z2,z3,z8,z5,z441]),(0,[z0,z196,z1,z2,z40,z3,z8])],[(0,[z0,z442,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z30,z3,z8,z5]),(0,[z0,z70,z1,z30,z3,z8,z5]),(0,[z0,z167,z1,z2,z3,z5,z12]),(0,[z443,z0,z1,z2,z3,z8,z5]),(0,[z0,z444,z1,z2,z3,z8,z5])],[(0,[z0,z70,z7,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z445,z8,z5]),(0,[z1,z16,z2,z30,z3,z8,z5]),(1,[z0,z117,z2,z3,z8,z5]),(0,[z116,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z10]),(0,[z446,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z447,z3,z46,z8]),(0,[z448,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z449,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z55,z8,z5]),(0,[z0,z1,z2,z372,z3,z8,z5]),(0,[z0,z1,z2,z450,z3,z8,z5]),(0,[z0,z121,z1,z2,z3,z8,z451])],[(0,[z0,z1,z1,z2,z3,z8,z5]),(0,[z25,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z197,z3,z8,z5]),(0,[z0,z1,z2,z107,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z166,z5]),(1,[z0,z1,z2,z3,z97,z12])],[(0,[z452,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z40,z3,z8])]],
   [[(0,[z0,z1,z82,z16,z3,z8,z5]),(0,[z453,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z166,z5]),(0,[z0,z1,z2,z454,z3,z8,z5]),(0,[z0,z455,z1,z2,z3,z8,z5])],[(0,[z29,z0,z1,z2,z40,z3,z8]),(0,[z270,z0,z1,z16,z3,z8,z5]),(0,[z11,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z148,z8,z5,z186]),(0,[z11,z0,z109,z2,z3,z8,z5])],[(0,[z53,z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z16,z416,z3,z8,z5]),(0,[z0,z1,z2,z3,z55,z8,z12])],[(1,[z0,z1,z2,z230,z8,z5]),(0,[z192,z0,z1,z7,z2,z3,z5]),(0,[z0,z456,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z457,z8,z5]),(0,[z222,z0,z1,z30,z3,z8,z5]),(0,[z458,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z107,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z459,z5]),(0,[z0,z460,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z461])],[(0,[z143,z1,z7,z2,z3,z8,z5]),(0,[z0,z139,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z462,z3,z8]),(0,[z0,z1,z2,z40,z3,z8,z186]),(0,[z0,z1,z2,z463,z3,z8,z5])],[(1,[z0,z406,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z464]),(0,[z0,z1,z2,z40,z3,z46,z8]),(0,[z465,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z333,z8,z5]),(0,[z0,z1,z2,z170,z3,z8,z111])],[(0,[z466,z0,z1,z2,z3,z8,z5]),(0,[z0,z285,z1,z16,z3,z8,z5]),(1,[z0,z1,z2,z3,z467,z5]),(0,[z0,z1,z2,z468,z3,z8,z5]),(0,[z18,z0,z1,z2,z327,z8,z5]),(1,[z18,z0,z2,z3,z100,z5])],[(0,[z0,z1,z2,z3,z8,z241,z5]),(0,[z469,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z291,z3,z8,z5]),(0,[z39,z0,z1,z2,z107,z8,z5]),(0,[z0,z1,z2,z470,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z471,z5]),(0,[z0,z1,z2,z3,z97,z8,z5])]],
   [[(0,[z0,z90,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z377,z5]),(0,[z0,z1,z2,z3,z294,z8,z5]),(0,[z0,z275,z1,z82,z3,z8,z5]),(0,[z0,z472,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z473]),(0,[z474,z0,z1,z2,z3,z8,z12])],[(0,[z0,z1,z2,z3,z8,z475,z5]),(0,[z476,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z51,z12])],[(0,[z0,z0,z1,z30,z3,z8,z5]),(1,[z0,z1,z2,z3,z312,z5]),(0,[z0,z1,z477,z2,z3,z8,z5]),(0,[z0,z1,z118,z3,z8,z87,z5]),(0,[z0,z1,z2,z40,z3,z8,z92]),(0,[z0,z1,z2,z251,z3,z8,z5])],[(0,[z0,z1,z2,z40,z3,z8,z10]),(0,[z0,z70,z1,z2,z107,z8,z5]),(0,[z0,z1,z2,z3,z8,z478,z5]),(0,[z0,z1,z2,z234,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z479,z5])],[(0,[z0,z1,z2,z3,z97,z8,z12])],[(0,[z0,z1,z2,z3,z8,z5,z5]),(0,[z0,z1,z2,z3,z64,z8,z5]),(0,[z0,z1,z2,z3,z8,z480,z5])],[(0,[z192,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z38,z186]),(0,[z481,z0,z1,z2,z3,z8,z5]),(0,[z0,z109,z1,z2,z40,z3,z8]),(0,[z0,z427,z1,z2,z3,z8,z5]),(0,[z21,z141,z0,z1,z2,z8,z5]),(0,[z0,z1,z2,z40,z118,z3,z8])],[(0,[z35,z1,z16,z2,z3,z8,z5]),(0,[z18,z0,z1,z2,z3,z8,z216]),(0,[z0,z1,z2,z3,z8,z280,z5]),(0,[z0,z1,z2,z3,z8,z482,z5]),(0,[z0,z1,z344,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z148,z8,z62,z5]),(0,[z0,z1,z2,z3,z8,z5,z252]),(0,[z116,z9,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z483,z5]),(1,[z0,z437,z2,z3,z8,z5]),(0,[z0,z65,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z462,z3,z8,z5])],[(0,[z15,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z16,z3,z8,z5,z10]),(0,[z0,z70,z2,z136,z3,z8,z5]),(0,[z0,z1,z2,z484,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z122])],[(0,[z0,z1,z2,z3,z8,z485,z5]),(0,[z0,z1,z82,z30,z3,z8,z5]),(0,[z0,z1,z16,z3,z55,z8,z5]),(0,[z0,z486,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z395,z3,z8,z5]),(0,[z0,z1,z2,z136,z40,z3,z8]),(0,[z0,z1,z3,z8,z92,z5,z119]),(0,[z487,z0,z1,z2,z3,z8,z5])],[(0,[z29,z1,z2,z30,z3,z8,z5]),(0,[z0,z1,z2,z488,z3,z8,z5]),(0,[z0,z1,z16,z107,z3,z8,z5]),(0,[z0,z1,z2,z58,z8,z5,z186]),(0,[z0,z1,z2,z447,z3,z8,z5])],[(0,[z77,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z489,z2,z3,z8,z5]),(0,[z0,z1,z2,z490,z3,z8,z5])],[(1,[z0,z1,z491,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z492,z5]),(0,[z0,z1,z2,z3,z8,z493,z5])],[(0,[z0,z1,z30,z3,z58,z8,z5]),(0,[z0,z1,z2,z3,z467,z8,z5]),(0,[z0,z1,z61,z2,z3,z8,z5]),(1,[z0,z1,z2,z447,z3,z8]),(0,[z0,z121,z1,z2,z3,z97,z5]),(0,[z0,z196,z1,z2,z3,z8,z5])],[(0,[z0,z1,z494,z2,z3,z8,z5]),(0,[z25,z0,z1,z2,z3,z8,z377]),(0,[z495,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z131,z5])]],
   [[(0,[z35,z29,z1,z2,z3,z8,z5]),(0,[z496,z0,z1,z2,z3,z8,z5]),(0,[z0,z497,z1,z2,z3,z8,z5]),(0,[z0,z498,z1,z2,z3,z8,z5]),(0,[z499,z0,z1,z2,z3,z8,z5]),(0,[z0,z121,z1,z500,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z501,z5]),(0,[z0,z1,z2,z3,z8,z502,z5]),(0,[z0,z1,z2,z3,z8,z5,z271]),(1,[z0,z275,z1,z3,z8,z92])],[(0,[z0,z1,z2,z503,z3,z8,z5]),(0,[z49,z0,z90,z2,z3,z8,z5]),(1,[z0,z1,z504,z3,z8,z5]),(0,[z11,z0,z1,z136,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z492,z12])],[(0,[z0,z1,z2,z505,z3,z8,z5]),(0,[z506,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z66]),(0,[z0,z1,z2,z3,z96,z5,z12]),(1,[z0,z1,z32,z3,z97,z5])],[(0,[z0,z1,z16,z507,z3,z8,z5]),(0,[z0,z1,z16,z3,z97,z8,z5]),(0,[z0,z121,z1,z2,z3,z55,z5]),(0,[z0,z1,z2,z3,z8,z5,z508]),(0,[z0,z1,z2,z40,z3,z8,z5])],[(0,[z509,z0,z1,z2,z3,z8,z5]),(0,[z0,z456,z1,z30,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z5,z152]),(0,[z0,z1,z2,z3,z8,z80,z5]),(0,[z0,z1,z32,z136,z3,z8,z5]),(0,[z0,z19,z1,z2,z3,z8,z152]),(0,[z0,z1,z2,z3,z8,z510,z5]),(0,[z0,z511,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z512,z3,z8,z5]),(1,[z0,z1,z2,z170,z43,z5])],[(0,[z77,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z7,z2,z3,z8,z12]),(0,[z29,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z475,z5]),(0,[z513,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z514,z8,z5])],[(0,[z515,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z251,z3,z8,z5]),(0,[z516,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z3,z8,z517,z5])]],
   [[(0,[z18,z53,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z8,z186,z10]),(0,[z0,z518,z1,z2,z3,z8,z5]),(0,[z519,z0,z1,z2,z3,z8,z5]),(0,[z520,z0,z1,z2,z3,z8,z12])],[(0,[z0,z52,z1,z2,z3,z8,z5]),(0,[z0,z275,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z521,z3,z8,z5]),(0,[z0,z1,z2,z130,z3,z8,z5]),(0,[z0,z1,z2,z34,z3,z5,z12])],[(0,[z25,z1,z2,z3,z58,z8,z5]),(0,[z0,z1,z2,z3,z8,z522,z5]),(0,[z0,z523,z1,z2,z3,z8,z5])],[(0,[z143,z0,z167,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z524,z8,z5]),(0,[z0,z1,z2,z3,z8,z525,z5]),(0,[z0,z1,z2,z3,z43,z96,z5])],[(0,[z319,z0,z1,z30,z3,z8,z5]),(0,[z35,z0,z1,z2,z3,z8,z12]),(1,[z0,z1,z2,z3,z80,z12]),(0,[z0,z1,z2,z40,z251,z3,z8]),(0,[z0,z1,z2,z40,z526,z3,z8])],[(1,[z0,z1,z326,z3,z8,z5]),(0,[z0,z1,z2,z130,z107,z3,z8]),(0,[z0,z1,z2,z3,z8,z527,z5]),(0,[z0,z1,z2,z3,z8,z528,z5])],[(1,[z0,z1,z246,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z38,z5]),(0,[z0,z1,z2,z529,z3,z8,z5]),(0,[z0,z1,z22,z2,z40,z3,z8]),(0,[z0,z1,z2,z530,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z531,z5]),(0,[z0,z121,z1,z2,z40,z3,z8])],[(0,[z0,z1,z2,z3,z4,z8,z5]),(0,[z0,z1,z2,z3,z8,z532,z5]),(0,[z0,z421,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z533,z5]),(1,[z0,z1,z2,z3,z8,z111])]],
   [[(0,[z0,z90,z2,z3,z8,z100,z5]),(0,[z0,z1,z2,z3,z80,z5,z12]),(1,[z0,z1,z2,z3,z8,z289]),(0,[z9,z0,z1,z534,z3,z8,z5]),(0,[z0,z1,z2,z3,z535,z8,z5])],[(0,[z0,z90,z1,z2,z40,z3,z8]),(0,[z0,z1,z30,z3,z8,z5,z93]),(0,[z0,z1,z30,z3,z8,z96,z5]),(0,[z0,z1,z536,z2,z3,z8,z5]),(0,[z116,z0,z1,z2,z3,z8,z10]),(0,[z0,z1,z534,z2,z3,z8,z5]),(0,[z537,z0,z1,z2,z3,z8,z5]),(1,[z290,z0,z1,z3,z8,z5]),(0,[z0,z538,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z8,z12])],[(0,[z539,z0,z1,z2,z3,z8,z5]),(0,[z0,z65,z1,z30,z3,z8,z5]),(0,[z185,z0,z1,z16,z3,z8,z5]),(0,[z0,z19,z1,z16,z3,z8,z5]),(0,[z0,z540,z1,z2,z3,z8,z5]),(0,[z0,z1,z541,z2,z3,z8,z5]),(0,[z542,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z543,z5]),(0,[z0,z1,z2,z295,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z544,z5]),(0,[z0,z1,z2,z107,z148,z8,z5]),(0,[z0,z109,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z545,z3,z8,z5])],[(0,[z0,z383,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z546,z5]),(0,[z0,z1,z2,z3,z8,z547,z5]),(0,[z0,z548,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z375,z3,z8])],[(0,[z0,z1,z78,z2,z3,z8,z5]),(0,[z0,z65,z1,z2,z3,z96,z5]),(0,[z0,z275,z1,z3,z8,z92,z5]),(0,[z0,z1,z2,z3,z549,z8,z5])],[(0,[z15,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z119,z12]),(0,[z0,z1,z2,z3,z8,z12,z12])],[(0,[z550,z0,z1,z2,z3,z8,z5]),(0,[z392,z0,z1,z16,z3,z8,z5]),(0,[z1,z2,z148,z3,z58,z8,z5]),(0,[z0,z61,z2,z136,z3,z8,z5]),(0,[z0,z1,z2,z136,z3,z8,z5]),(0,[z0,z1,z551,z2,z3,z8,z5])]],
   [[(1,[z0,z1,z2,z3,z353,z5]),(0,[z0,z196,z1,z30,z3,z8,z5]),(0,[z0,z1,z61,z30,z3,z8,z5]),(0,[z53,z0,z167,z1,z2,z3,z5]),(1,[z0,z1,z552,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z553]),(0,[z0,z1,z2,z554,z3,z8,z5]),(0,[z555,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z335,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z556,z5])],[(1,[z0,z1,z2,z3,z8,z145]),(0,[z557,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z558,z8,z5]),(0,[z0,z109,z2,z3,z8,z62,z5])],[(0,[z77,z0,z1,z2,z3,z8,z123]),(0,[z0,z1,z47,z2,z3,z8,z5]),(0,[z0,z1,z559,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z560,z8,z5]),(1,[z141,z0,z121,z1,z2,z5])],[(0,[z0,z7,z2,z3,z8,z5,z152]),(0,[z0,z1,z561,z2,z3,z8,z5]),(0,[z0,z275,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z58,z8,z12]),(0,[z0,z562,z1,z2,z3,z8,z5]),(0,[z563,z0,z1,z2,z3,z8,z5]),(0,[z21,z0,z1,z2,z40,z3,z8]),(0,[z0,z564,z1,z2,z3,z8,z5]),(0,[z0,z196,z1,z2,z3,z96,z5]),(0,[z0,z1,z2,z3,z565,z8,z5]),(0,[z0,z1,z566,z2,z3,z8,z5])],[(0,[z0,z1,z2,z491,z3,z8,z5]),(1,[z0,z1,z2,z394,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z355]),(0,[z0,z1,z2,z462,z3,z97,z8])],[(0,[z77,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z2,z3,z8,z567,z5]),(0,[z0,z1,z2,z568,z3,z8,z5]),(0,[z0,z569,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z570,z5])],[(0,[z35,z185,z1,z2,z3,z8,z5]),(0,[z143,z0,z1,z291,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z172]),(0,[z571,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z34,z3,z8])],[(0,[z0,z1,z2,z3,z8,z5,z572]),(0,[z0,z573,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z574,z3,z8,z5]),(0,[z575,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z576])]],
   [[(0,[z116,z0,z1,z2,z3,z235,z5]),(0,[z0,z1,z577,z2,z3,z8,z5])],[(0,[z0,z1,z2,z504,z3,z8,z5]),(0,[z578,z0,z1,z2,z3,z8,z5]),(0,[z0,z306,z1,z2,z3,z8,z5]),(0,[z0,z1,z22,z2,z8,z43,z5]),(0,[z0,z121,z1,z2,z8,z43,z5]),(0,[z141,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z344,z3,z8,z5,z186]),(0,[z579,z0,z1,z2,z3,z8,z5])],[(0,[z116,z0,z421,z2,z3,z8,z5]),(0,[z9,z0,z1,z2,z3,z8,z38]),(0,[z0,z1,z2,z3,z8,z580,z5]),(0,[z581,z0,z1,z2,z3,z8,z5]),(0,[z0,z281,z1,z2,z3,z20,z5])],[(0,[z0,z1,z89,z2,z3,z8,z5]),(0,[z0,z0,z1,z16,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z38,z5]),(0,[z18,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z251,z8,z5,z186]),(0,[z142,z0,z1,z2,z37,z3,z8])],[(0,[z0,z19,z1,z30,z3,z8,z5]),(1,[z143,z1,z2,z3,z55,z5]),(0,[z0,z582,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z583,z5]),(0,[z21,z0,z228,z2,z3,z8,z5]),(0,[z0,z1,z2,z584,z3,z8,z5]),(0,[z585,z0,z1,z2,z3,z8,z5]),(0,[z0,z28,z1,z2,z3,z8,z12])],[(0,[z0,z1,z2,z3,z586,z8,z5]),(0,[z25,z0,z406,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z420,z5]),(0,[z587,z0,z1,z2,z3,z8,z5]),(0,[z588,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z170,z8,z43,z5])],[(0,[z0,z1,z2,z3,z8,z5,z589]),(1,[z21,z0,z1,z8,z87,z5]),(1,[z0,z1,z500,z3,z8,z5]),(0,[z142,z0,z1,z2,z251,z8,z5]),(0,[z0,z1,z2,z3,z8,z517,z5])],[(0,[z0,z1,z7,z2,z40,z3,z8]),(0,[z590,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z346,z2,z3,z8,z5]),(0,[z591,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z32,z61,z3,z8,z5]),(0,[z0,z167,z2,z3,z46,z8,z5]),(0,[z0,z99,z1,z2,z251,z3,z5])]],
   [[(0,[z77,z0,z1,z2,z184,z8,z5]),(0,[z0,z1,z2,z3,z8,z592,z5]),(0,[z0,z1,z2,z3,z593,z8,z5]),(0,[z0,z1,z2,z3,z8,z594,z5]),(0,[z21,z595,z1,z2,z3,z8,z5]),(0,[z596,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z97,z8]),(0,[z0,z1,z2,z3,z8,z597,z5])],[(0,[z0,z1,z568,z30,z3,z8,z5]),(1,[z0,z1,z2,z124,z8,z5]),(0,[z49,z0,z1,z2,z37,z3,z8]),(0,[z598,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z526,z3,z8,z5])],[(0,[z116,z0,z1,z16,z3,z8,z5]),(1,[z0,z26,z2,z3,z8,z5]),(0,[z25,z0,z1,z2,z3,z312,z5]),(1,[z0,z1,z54,z3,z8,z5]),(0,[z599,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z216]),(0,[z0,z600,z1,z2,z3,z8,z5]),(0,[z0,z601,z1,z2,z3,z8,z5])],[(0,[z0,z1,z16,z3,z58,z8,z5]),(1,[z0,z1,z2,z3,z8,z59]),(0,[z0,z1,z602,z2,z3,z8,z5]),(0,[z0,z109,z61,z2,z3,z8,z5]),(0,[z0,z1,z22,z2,z3,z8,z5]),(0,[z106,z0,z1,z2,z3,z8,z5]),(0,[z0,z121,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z326,z3,z8,z5]),(0,[z0,z398,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z405,z8,z5]),(0,[z0,z1,z16,z136,z3,z8,z5]),(0,[z603,z0,z1,z2,z3,z8,z5]),(0,[z604,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z605,z8,z5])],[(0,[z35,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z606,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z607,z8,z5]),(0,[z0,z608,z1,z2,z3,z8,z5])],[(0,[z0,z90,z1,z2,z3,z8,z5]),(0,[z9,z0,z1,z2,z3,z8,z5]),(0,[z116,z1,z2,z3,z8,z5,z10]),(0,[z0,z1,z609,z2,z3,z8,z5]),(1,[z610,z1,z2,z3,z8,z5]),(0,[z21,z0,z1,z2,z8,z43,z5]),(0,[z0,z1,z2,z3,z8,z96,z12]),(0,[z474,z0,z1,z2,z3,z8,z5]),(0,[z142,z0,z1,z2,z3,z8,z5])],[(1,[z0,z1,z2,z3,z55,z12]),(0,[z0,z611,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z98]),(0,[z0,z1,z2,z170,z3,z8,z5]),(0,[z0,z196,z121,z1,z2,z3,z5]),(0,[z612,z0,z1,z2,z3,z8,z5])]],
   [[(0,[z15,z0,z1,z30,z3,z8,z5]),(0,[z185,z0,z1,z491,z3,z8,z5]),(0,[z613,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z614,z3,z8,z5]),(0,[z0,z1,z2,z8,z43,z62,z5]),(0,[z0,z1,z22,z2,z3,z8,z12]),(0,[z0,z121,z1,z2,z3,z8,z12])],[(0,[z15,z0,z1,z89,z3,z8,z5]),(0,[z185,z0,z1,z2,z58,z8,z5]),(0,[z39,z0,z70,z2,z3,z8,z5]),(0,[z0,z1,z32,z2,z3,z97,z5]),(0,[z0,z615,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z134,z5]),(1,[z0,z1,z2,z251,z8,z186])],[(0,[z0,z139,z1,z7,z2,z3,z8]),(0,[z616,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z507,z3,z8,z5]),(0,[z617,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z136,z3,z8,z96,z5])],[(0,[z0,z618,z1,z2,z3,z8,z5]),(0,[z0,z1,z619,z2,z3,z8,z5]),(0,[z116,z49,z0,z1,z2,z3,z8]),(1,[z0,z1,z534,z3,z8,z5]),(0,[z9,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z5,z620]),(0,[z0,z1,z2,z3,z621,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z152]),(0,[z49,z0,z2,z3,z8,z20,z5]),(0,[z142,z0,z1,z2,z3,z8,z12])],[(0,[z622,z0,z1,z2,z3,z8,z5]),(0,[z0,z90,z2,z3,z8,z62,z5]),(0,[z0,z1,z2,z623,z3,z8,z5]),(0,[z0,z1,z2,z624,z3,z8,z5]),(0,[z21,z0,z1,z3,z8,z96,z5]),(0,[z0,z1,z2,z170,z3,z8,z12])],[(1,[z0,z1,z336,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z625,z5]),(0,[z0,z109,z1,z118,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z626,z5]),(0,[z0,z1,z2,z107,z3,z8,z271]),(0,[z627,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z628,z8,z5])],[(0,[z25,z0,z1,z2,z3,z8,z278]),(0,[z25,z0,z1,z2,z58,z8,z5]),(0,[z0,z1,z2,z3,z629,z8,z5]),(0,[z0,z1,z630,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z195,z5]),(0,[z0,z1,z2,z631,z3,z8,z5])],[(0,[z0,z1,z30,z118,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z632]),(0,[z0,z1,z2,z552,z3,z8,z5]),(0,[z0,z167,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z633,z5]),(0,[z0,z1,z2,z634,z3,z8,z5])]],
   [[(0,[z0,z1,z30,z3,z46,z8,z5]),(0,[z0,z1,z2,z3,z55,z43,z5]),(0,[z21,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z195,z5])],[(0,[z116,z0,z1,z2,z3,z467,z5]),(0,[z49,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z635,z3,z8,z5]),(0,[z0,z1,z636,z2,z3,z8,z5])],[(0,[z77,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z637]),(0,[z25,z0,z1,z504,z3,z8,z5]),(1,[z176,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z426]),(0,[z137,z0,z1,z2,z3,z8,z12])],[(0,[z0,z1,z638,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z639,z5]),(0,[z0,z640,z1,z2,z3,z8,z5])],[(0,[z0,z1,z641,z7,z2,z3,z5]),(0,[z116,z0,z1,z30,z3,z8,z5]),(0,[z642,z0,z1,z2,z3,z8,z5]),(0,[z0,z167,z1,z2,z3,z8,z12]),(1,[z0,z1,z2,z3,z280,z5])],[(1,[z0,z228,z2,z3,z8,z5]),(0,[z21,z0,z1,z2,z3,z8,z12]),(0,[z0,z65,z1,z2,z3,z8,z426])],[(0,[z643,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z96,z5]),(0,[z18,z610,z1,z2,z3,z8,z5]),(0,[z595,z0,z1,z2,z3,z8,z5]),(0,[z0,z437,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z5,z644]),(0,[z0,z645,z1,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z646,z3,z8,z5]),(1,[z11,z0,z136,z3,z8,z5])],[(1,[z0,z1,z2,z3,z8,z278]),(1,[z0,z1,z165,z3,z8,z5]),(0,[z0,z1,z2,z3,z124,z8,z5]),(1,[z595,z1,z2,z3,z8,z5])],[(0,[z0,z2,z136,z3,z8,z62,z5]),(1,[z0,z611,z1,z2,z3,z5]),(0,[z0,z1,z2,z40,z3,z8,z152]),(0,[z141,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z647,z2,z3,z8,z5])],[(0,[z15,z1,z2,z3,z8,z80,z5]),(0,[z0,z65,z1,z16,z3,z8,z5]),(0,[z648,z0,z1,z2,z3,z8,z5]),(1,[z0,z1,z2,z177,z8,z5]),(0,[z53,z0,z1,z2,z3,z80,z5]),(0,[z1,z2,z3,z8,z38,z5,z10]),(0,[z18,z0,z2,z3,z8,z100,z5])],[(0,[z0,z1,z7,z2,z3,z8,z5]),(0,[z0,z1,z16,z170,z3,z8,z5]),(0,[z18,z0,z1,z2,z40,z3,z8]),(0,[z649,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z387,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z87]),(0,[z0,z1,z2,z650,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z12,z287])],[(0,[z0,z1,z30,z34,z3,z8,z5]),(1,[z35,z1,z16,z3,z8,z5]),(0,[z25,z0,z1,z246,z3,z8,z5]),(0,[z0,z196,z167,z1,z2,z3,z5]),(0,[z520,z0,z1,z2,z3,z8,z5]),(0,[z651,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z641,z2,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z20,z5]),(0,[z0,z1,z30,z3,z8,z43,z5]),(0,[z143,z0,z1,z552,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z652,z5]),(0,[z0,z70,z1,z2,z3,z8,z12])]],
   [[(0,[z0,z90,z1,z30,z3,z8,z5]),(0,[z0,z1,z653,z2,z3,z8,z5]),(0,[z116,z0,z1,z346,z3,z8,z5]),(1,[z0,z167,z2,z3,z46,z5]),(0,[z141,z0,z1,z22,z2,z8,z5]),(0,[z0,z121,z1,z2,z3,z96,z5]),(1,[z0,z1,z67,z3,z8,z5])],[(0,[z654,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z655,z8,z5]),(0,[z0,z196,z1,z16,z3,z8,z5]),(0,[z141,z0,z1,z2,z148,z8,z5]),(0,[z0,z1,z2,z54,z3,z8,z5]),(0,[z0,z1,z2,z3,z46,z80,z5]),(0,[z0,z1,z3,z8,z517,z5,z186])],[(0,[z0,z90,z167,z2,z3,z8,z5]),(0,[z35,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z656,z5]),(0,[z210,z0,z1,z2,z3,z8,z12])],[(0,[z25,z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z657,z5]),(0,[z0,z1,z2,z658,z3,z8,z5]),(0,[z0,z121,z1,z2,z170,z3,z5]),(0,[z0,z659,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z38,z152])],[(0,[z660,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z55,z5,z12]),(0,[z0,z1,z2,z3,z8,z235,z5]),(0,[z0,z1,z2,z3,z8,z661,z5]),(0,[z0,z662,z1,z2,z3,z8,z5]),(0,[z0,z1,z209,z2,z3,z8,z5]),(0,[z0,z2,z3,z46,z8,z100,z5]),(0,[z0,z1,z22,z118,z3,z8,z5]),(0,[z0,z1,z2,z663,z3,z8,z5]),(1,[z0,z1,z2,z3,z430,z5]),(0,[z0,z196,z1,z2,z40,z3,z5])],[(0,[z0,z1,z30,z3,z8,z87,z5]),(0,[z0,z1,z16,z61,z3,z8,z5]),(0,[z0,z1,z2,z3,z664,z8,z5]),(0,[z0,z665,z1,z2,z3,z8,z5]),(0,[z0,z666,z1,z2,z3,z8,z5]),(0,[z0,z1,z500,z2,z3,z8,z5]),(1,[z0,z1,z2,z3,z8,z451])],[(0,[z0,z1,z16,z3,z8,z5,z637]),(0,[z0,z1,z2,z3,z8,z8,z5]),(0,[z0,z1,z2,z3,z8,z59,z5]),(0,[z0,z1,z2,z3,z667,z8,z5])]],
   [[(0,[z668,z0,z1,z2,z3,z8,z5]),(0,[z0,z263,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z669,z5]),(0,[z0,z1,z165,z2,z3,z8,z5]),(0,[z670,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z451,z5])],[(1,[z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z671,z3,z8,z5]),(0,[z29,z0,z1,z16,z3,z8,z5]),(0,[z0,z672,z1,z2,z3,z8,z5]),(0,[z0,z196,z1,z2,z3,z43,z5]),(0,[z0,z1,z2,z3,z8,z229,z12])],[(1,[z185,z1,z2,z148,z8,z5]),(0,[z0,z1,z673,z2,z3,z8,z5]),(0,[z0,z674,z1,z2,z3,z8,z5])],[(0,[z0,z70,z90,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z69,z8,z5]),(0,[z0,z1,z2,z197,z3,z55,z8]),(0,[z0,z1,z2,z3,z8,z20,z38]),(0,[z675,z0,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z336,z3,z8,z5]),(0,[z116,z0,z1,z372,z3,z8,z5]),(0,[z9,z0,z1,z2,z40,z3,z8]),(0,[z0,z1,z2,z3,z8,z676,z5]),(0,[z142,z0,z1,z2,z40,z3,z8])],[(0,[z185,z0,z1,z279,z3,z8,z5]),(0,[z0,z1,z2,z3,z46,z8,z12]),(0,[z0,z1,z2,z3,z8,z677,z5])],[(0,[z0,z678,z1,z2,z3,z8,z5]),(0,[z0,z679,z1,z2,z3,z8,z5]),(0,[z0,z1,z82,z2,z3,z430,z5]),(1,[z0,z1,z2,z3,z8,z12]),(0,[z613,z0,z1,z2,z40,z3,z8])],[(0,[z0,z680,z1,z2,z3,z8,z5]),(0,[z0,z1,z681,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z682]),(0,[z0,z19,z2,z3,z8,z5,z152])]],
   [[(0,[z0,z1,z30,z37,z3,z8,z5]),(0,[z53,z0,z1,z2,z394,z8,z5]),(0,[z0,z1,z683,z2,z3,z8,z5]),(0,[z610,z0,z1,z2,z3,z8,z5])],[(1,[z0,z1,z641,z2,z3,z5]),(0,[z0,z1,z2,z3,z58,z8,z5]),(0,[z0,z1,z2,z684,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z685,z5]),(0,[z9,z0,z1,z158,z3,z8,z5]),(0,[z0,z1,z2,z686,z3,z8,z5]),(0,[z142,z0,z1,z2,z3,z8,z186]),(0,[z0,z1,z687,z2,z3,z8,z5])],[(0,[z688,z0,z1,z2,z3,z8,z5]),(0,[z0,z689,z1,z2,z3,z8,z5]),(0,[z0,z690,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z691]),(0,[z49,z0,z1,z2,z40,z3,z8]),(0,[z21,z0,z1,z32,z3,z8,z5]),(0,[z0,z1,z2,z624,z40,z3,z8])],[(0,[z0,z1,z2,z692,z3,z8,z5]),(1,[z1,z16,z30,z3,z8,z5]),(0,[z142,z0,z1,z2,z148,z8,z5]),(0,[z0,z1,z2,z40,z3,z8,z20]),(0,[z0,z693,z1,z2,z3,z8,z5]),(0,[z137,z0,z1,z2,z40,z3,z8])],[(0,[z0,z1,z2,z3,z8,z5,z694]),(0,[z0,z1,z30,z3,z8,z5,z12]),(0,[z0,z1,z536,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z113,z5]),(0,[z116,z0,z1,z2,z395,z8,z5]),(0,[z141,z0,z1,z2,z8,z62,z5]),(0,[z0,z1,z2,z3,z8,z695,z5]),(0,[z0,z611,z1,z2,z107,z3,z5]),(0,[z0,z1,z2,z3,z8,z5,z696]),(0,[z0,z1,z2,z3,z8,z697,z5]),(1,[z142,z0,z1,z2,z37,z8])],[(0,[z698,z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z30,z148,z3,z8,z5]),(0,[z0,z1,z30,z340,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z341,z5]),(0,[z25,z185,z1,z2,z3,z8,z5]),(0,[z25,z0,z1,z2,z3,z420,z5]),(0,[z0,z1,z2,z3,z699,z8,z5]),(0,[z0,z167,z1,z2,z40,z3,z8]),(0,[z21,z0,z1,z2,z3,z8,z132]),(0,[z0,z700,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z463,z3,z8]),(0,[z0,z1,z150,z2,z40,z3,z8])],[(0,[z0,z1,z7,z30,z3,z8,z5]),(0,[z0,z109,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z55,z100,z5]),(1,[z9,z1,z2,z3,z8,z38]),(0,[z0,z1,z32,z2,z3,z8,z5]),(0,[z0,z1,z2,z37,z3,z8,z92]),(0,[z0,z1,z2,z3,z701,z8,z5])],[(0,[z90,z1,z7,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z702]),(0,[z0,z1,z2,z3,z8,z703,z5]),(0,[z49,z0,z19,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z5,z704]),(0,[z49,z0,z1,z2,z3,z8,z186]),(0,[z0,z1,z82,z2,z3,z8,z12]),(0,[z0,z1,z2,z37,z3,z8,z119]),(0,[z0,z705,z1,z2,z3,z8,z5]),(0,[z141,z0,z1,z2,z3,z8,z5]),(0,[z706,z0,z1,z2,z3,z8,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z707,z2,z3,z8,z5]),(0,[z0,z1,z3,z708,z96,z5]),(0,[z0,z709,z2,z3,z8,z12])],[(0,[z0,z1,z2,z3,z8,z159]),(0,[z0,z1,z710,z3,z8,z5])],[(0,[z0,z1,z711,z3,z8,z5])],[(0,[z143,z1,z638,z2,z3,z5]),(0,[z0,z1,z2,z3,z280,z5]),(0,[z49,z0,z2,z3,z8,z20]),(0,[z49,z0,z2,z3,z20,z280])],[(0,[z0,z1,z16,z3,z312,z5]),(0,[z0,z1,z2,z3,z712,z5]),(0,[z0,z611,z1,z2,z130,z3]),(0,[z0,z1,z32,z3,z97,z98]),(0,[z142,z0,z1,z2,z713,z8])],[(0,[z0,z1,z2,z3,z8,z714]),(0,[z0,z6,z1,z641,z2,z3]),(0,[z143,z1,z30,z3,z55,z5]),(0,[z0,z715,z2,z3,z8,z5]),(0,[z49,z0,z117,z2,z3,z8]),(0,[z0,z1,z2,z40,z716,z8])],[(0,[z0,z1,z2,z184,z8,z5]),(0,[z0,z1,z2,z717,z8,z5]),(0,[z0,z1,z2,z3,z718,z5])],[(0,[z77,z7,z326,z3,z8,z5]),(0,[z0,z1,z2,z3,z4,z123]),(0,[z0,z1,z30,z719,z3,z8]),(0,[z0,z1,z2,z124,z467,z5]),(0,[z9,z1,z534,z3,z8,z38]),(0,[z0,z121,z1,z2,z3,z111])],[(0,[z0,z117,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z720]),(0,[z21,z0,z1,z2,z43,z12])],[(0,[z176,z1,z16,z3,z8,z5]),(0,[z0,z611,z1,z2,z3,z5]),(0,[z0,z721,z1,z2,z3,z5])],[(0,[z0,z437,z16,z3,z8,z5]),(0,[z0,z1,z2,z177,z8,z5]),(0,[z0,z1,z2,z3,z235,z38])],[(0,[z0,z26,z30,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z216]),(0,[z0,z1,z16,z3,z280,z5]),(0,[z49,z0,z1,z2,z124,z8])],[(0,[z1,z30,z3,z445,z8,z5]),(0,[z0,z1,z30,z3,z166,z5]),(0,[z0,z1,z2,z3,z8,z722]),(0,[z210,z1,z2,z3,z80,z12]),(0,[z0,z1,z2,z3,z8,z723]),(0,[z21,z0,z437,z8,z87,z5]),(0,[z21,z0,z1,z43,z96,z5])],[(0,[z192,z0,z167,z2,z3,z5]),(0,[z0,z724,z2,z3,z8,z5]),(0,[z53,z1,z54,z3,z80,z5]),(0,[z0,z1,z2,z177,z8,z252]),(0,[z9,z1,z158,z3,z8,z38]),(0,[z0,z1,z725,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z726]),(0,[z0,z1,z2,z3,z727,z5]),(0,[z53,z1,z2,z3,z80,z59])],[(0,[z142,z1,z30,z58,z8,z5]),(0,[z0,z167,z79,z2,z3,z5]),(0,[z0,z109,z61,z40,z3,z8]),(0,[z141,z0,z228,z2,z8,z5]),(0,[z0,z1,z2,z3,z8,z728])]],
   [[(0,[z0,z1,z2,z729,z3,z8]),(0,[z595,z1,z16,z3,z8,z5]),(0,[z730,z0,z1,z2,z3,z8]),(0,[z0,z318,z1,z2,z40,z3])],[(0,[z668,z1,z2,z3,z80,z5]),(0,[z0,z1,z2,z3,z203,z12]),(0,[z0,z1,z2,z250,z43,z5])],[(0,[z0,z1,z2,z3,z8,z731]),(0,[z77,z7,z2,z3,z353,z5]),(0,[z0,z1,z2,z732,z3,z8]),(0,[z1,z30,z3,z607,z8,z5]),(0,[z0,z1,z30,z251,z8,z186]),(0,[z0,z2,z733,z3,z8,z5]),(0,[z610,z1,z734,z3,z8,z5])],[(0,[z1,z30,z3,z8,z5,z461]),(0,[z0,z1,z40,z3,z8,z735])],[(0,[z0,z79,z2,z40,z3,z8]),(0,[z0,z117,z346,z3,z8,z5]),(0,[z0,z1,z2,z24,z3,z12]),(0,[z0,z1,z736,z40,z3,z8])],[(0,[z0,z1,z16,z3,z8,z66]),(0,[z0,z1,z2,z3,z8,z737]),(0,[z0,z1,z738,z3,z8,z5]),(0,[z0,z1,z739,z3,z8,z5]),(0,[z176,z1,z3,z8,z92,z5]),(0,[z0,z1,z740,z40,z3,z8])],[(0,[z0,z1,z89,z40,z3,z8]),(0,[z0,z741,z2,z3,z8,z5]),(0,[z0,z154,z1,z2,z3,z12])],[(0,[z0,z1,z2,z3,z8,z742]),(0,[z0,z167,z16,z3,z46,z5]),(0,[z0,z1,z743,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z5]),(0,[z0,z1,z30,z744,z8,z5]),(0,[z0,z1,z2,z3,z8,z745]),(0,[z0,z1,z2,z746,z8,z5]),(0,[z0,z1,z2,z747,z3,z8])],[(0,[z77,z748,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z657,z12]),(0,[z0,z1,z2,z97,z333,z12])],[(0,[z0,z1,z2,z352,z3,z235]),(0,[z0,z1,z2,z749,z3,z8])],[(0,[z0,z1,z2,z3,z8,z750]),(0,[z0,z1,z2,z3,z8,z751]),(0,[z0,z1,z2,z3,z8,z252]),(0,[z0,z1,z2,z3,z235,z12]),(0,[z0,z1,z2,z752,z8,z5]),(0,[z141,z0,z753,z1,z2,z5])],[(0,[z610,z1,z209,z3,z8,z5]),(0,[z0,z1,z2,z40,z64,z8]),(0,[z0,z1,z2,z3,z8,z754])],[(0,[z0,z1,z3,z8,z755,z5]),(0,[z0,z1,z16,z3,z8,z451]),(0,[z0,z421,z2,z3,z8,z12]),(0,[z0,z1,z2,z756,z3,z166]),(0,[z0,z1,z2,z3,z757,z5])],[(0,[z0,z1,z2,z3,z758,z5]),(0,[z0,z1,z2,z756,z3,z8]),(0,[z0,z1,z759,z3,z8,z5]),(0,[z0,z1,z2,z3,z451,z12]),(0,[z360,z1,z2,z352,z3,z8])],[(0,[z143,z1,z2,z3,z586,z5]),(0,[z0,z1,z2,z3,z420,z377]),(0,[z0,z1,z344,z3,z8,z132])]],
   [[(0,[z0,z1,z3,z8,z760,z5]),(0,[z0,z128,z2,z40,z3,z8]),(0,[z0,z228,z2,z3,z86,z5])],[(0,[z0,z1,z2,z3,z8,z761]),(0,[z0,z1,z16,z3,z8,z111]),(0,[z0,z1,z2,z3,z8,z762]),(0,[z0,z1,z118,z3,z195,z5]),(0,[z0,z1,z2,z44,z3,z12])],[(0,[z0,z1,z30,z3,z8,z278]),(0,[z0,z406,z504,z3,z8,z5]),(0,[z0,z1,z2,z3,z699,z12]),(0,[z0,z1,z372,z124,z8,z5]),(0,[z0,z1,z209,z40,z3,z8]),(0,[z0,z1,z2,z462,z3,z430])],[(0,[z143,z167,z7,z2,z3,z5]),(0,[z0,z1,z2,z58,z312,z5]),(0,[z0,z79,z2,z177,z8,z5]),(0,[z306,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z64,z8,z12]),(0,[z0,z1,z2,z3,z8,z763]),(0,[z0,z1,z415,z3,z8,z119]),(0,[z0,z1,z764,z3,z8,z5])],[(0,[z0,z1,z2,z3,z765,z5]),(0,[z0,z1,z2,z766,z8,z5]),(0,[z0,z306,z1,z2,z3,z12])],[],[(0,[z53,z1,z2,z177,z80,z5]),(0,[z0,z1,z2,z197,z3,z467]),(0,[z116,z1,z2,z124,z8,z10]),(0,[z0,z1,z2,z3,z767,z5]),(0,[z476,z0,z1,z2,z3,z12])],[(0,[z35,z1,z768,z3,z8,z5]),(0,[z0,z1,z16,z3,z769,z5]),(0,[z0,z1,z504,z3,z312,z5]),(0,[z0,z1,z2,z207,z43,z5]),(0,[z0,z1,z770,z3,z8,z5]),(0,[z0,z1,z771,z3,z8,z5])],[(0,[z142,z0,z1,z2,z48,z8]),(0,[z79,z2,z3,z8,z80,z5]),(0,[z772,z1,z2,z3,z8,z5]),(0,[z0,z2,z3,z773,z100,z5])],[(0,[z0,z1,z774,z3,z8,z5]),(0,[z0,z1,z2,z3,z773,z5]),(0,[z0,z1,z2,z3,z43,z111]),(0,[z0,z775,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z776]),(0,[z0,z1,z2,z3,z8,z777]),(0,[z0,z1,z2,z3,z8,z778])],[(0,[z0,z1,z326,z230,z8,z5]),(0,[z0,z1,z78,z40,z3,z8]),(0,[z0,z281,z1,z2,z3,z12]),(0,[z176,z1,z2,z3,z294,z5]),(0,[z0,z1,z344,z3,z8,z92])],[(0,[z185,z1,z30,z40,z3,z8]),(0,[z0,z109,z61,z3,z8,z5]),(0,[z0,z121,z1,z335,z3,z5]),(0,[z0,z1,z82,z3,z8,z132])],[],[(0,[z0,z1,z779,z3,z8,z5]),(0,[z0,z1,z30,z3,z430,z5]),(0,[z0,z1,z2,z3,z8,z780]),(0,[z0,z406,z246,z3,z8,z5]),(0,[z0,z228,z2,z3,z8,z27]),(0,[z0,z1,z2,z3,z288,z12]),(0,[z0,z262,z1,z2,z3,z12])],[(0,[z0,z128,z2,z177,z8,z5]),(0,[z49,z0,z2,z3,z8,z229])]],
   [[(0,[z176,z109,z1,z3,z8,z5]),(0,[z0,z1,z781,z3,z8,z5]),(0,[z0,z1,z2,z3,z97,z426]),(0,[z0,z1,z3,z492,z96,z12]),(0,[z276,z0,z1,z2,z3,z12])],[(0,[z0,z79,z2,z3,z8,z5]),(0,[z782,z0,z1,z30,z8,z5]),(0,[z1,z2,z3,z8,z38,z783]),(0,[z0,z1,z736,z3,z8,z5])],[(0,[z0,z1,z2,z3,z784,z5]),(0,[z0,z1,z2,z785,z8,z5]),(0,[z176,z1,z47,z3,z8,z5]),(0,[z595,z1,z2,z3,z294,z5]),(0,[z0,z1,z22,z40,z118,z8]),(0,[z0,z1,z3,z8,z92,z342])],[(0,[z0,z1,z89,z3,z8,z5]),(0,[z185,z1,z30,z148,z8,z5]),(0,[z0,z786,z2,z3,z8,z5])],[(0,[z0,z1,z30,z3,z8,z289]),(0,[z0,z1,z787,z3,z8,z5]),(0,[z519,z1,z16,z3,z8,z5]),(0,[z53,z1,z2,z3,z80,z5]),(0,[z0,z79,z2,z3,z8,z252]),(0,[z1,z2,z3,z788,z80,z5]),(0,[z0,z1,z67,z3,z5,z12]),(0,[z0,z1,z2,z713,z251,z8])],[(0,[z0,z1,z2,z789,z3,z8]),(0,[z290,z141,z0,z1,z8,z5]),(0,[z0,z1,z734,z3,z8,z5]),(0,[z106,z0,z1,z2,z8,z12])],[(0,[z0,z1,z78,z184,z8,z5]),(0,[z0,z1,z2,z40,z184,z8]),(0,[z0,z1,z2,z230,z353,z5]),(0,[z0,z1,z2,z3,z8,z790]),(0,[z39,z0,z16,z8,z62,z5]),(0,[z0,z1,z791,z3,z8,z5]),(0,[z0,z70,z2,z107,z8,z5])],[(0,[z0,z1,z2,z792,z8,z5]),(0,[z0,z1,z30,z3,z8,z12]),(0,[z0,z1,z16,z3,z420,z5])],[(0,[z192,z0,z1,z30,z3,z5]),(0,[z0,z1,z2,z3,z55,z122]),(0,[z0,z1,z2,z3,z793,z5]),(0,[z0,z794,z1,z2,z3,z5])],[(0,[z0,z456,z568,z3,z8,z5]),(0,[z360,z1,z2,z3,z8,z38]),(0,[z0,z1,z2,z3,z85,z12]),(0,[z0,z1,z2,z3,z86,z12])],[(0,[z306,z1,z2,z3,z8,z216]),(0,[z0,z1,z2,z64,z8,z216])],[(0,[z0,z1,z2,z3,z8,z795]),(0,[z0,z52,z1,z3,z8,z341]),(0,[z0,z1,z2,z796,z8,z5]),(0,[z25,z1,z2,z797,z8,z5])],[(0,[z215,z0,z1,z2,z37,z8]),(0,[z206,z0,z2,z8,z62,z5]),(0,[z0,z1,z2,z130,z3,z166])],[(0,[z0,z128,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z59]),(0,[z0,z1,z2,z130,z3,z8]),(0,[z0,z1,z2,z40,z3,z166]),(0,[z0,z1,z2,z798,z3,z8])],[(0,[z0,z1,z2,z3,z8,z799]),(0,[z1,z30,z3,z58,z8,z5]),(0,[z0,z19,z2,z3,z8,z152]),(0,[z800,z1,z2,z3,z8,z5])],[(0,[z0,z801,z1,z2,z3,z5]),(0,[z9,z1,z30,z3,z8,z38]),(0,[z0,z1,z209,z3,z8,z5])]],
   [[(0,[z610,z1,z16,z3,z8,z5]),(0,[z0,z128,z2,z3,z8,z252]),(0,[z0,z117,z2,z124,z8,z5])],[(0,[z0,z1,z30,z3,z4,z5]),(0,[z141,z176,z1,z2,z8,z5])],[(0,[z0,z1,z2,z747,z3,z97]),(0,[z210,z1,z2,z3,z8,z287])],[(0,[z1,z30,z3,z701,z8,z5]),(0,[z0,z1,z2,z802,z3,z312]),(0,[z0,z1,z346,z3,z8,z12]),(0,[z0,z1,z2,z125,z3,z12]),(0,[z306,z2,z3,z8,z100,z5]),(0,[z141,z0,z1,z2,z294,z5])],[(0,[z0,z748,z2,z3,z8,z5]),(0,[z782,z0,z1,z2,z8,z5]),(0,[z0,z540,z1,z2,z40,z3]),(0,[z0,z1,z3,z97,z708,z5])],[(0,[z351,z0,z2,z8,z62,z5]),(0,[z0,z1,z803,z3,z8,z5]),(0,[z0,z1,z16,z3,z134,z5]),(0,[z0,z1,z733,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z804])],[(0,[z0,z1,z2,z3,z805,z5]),(0,[z0,z1,z806,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z807]),(0,[z0,z1,z16,z40,z3,z8]),(0,[z143,z1,z291,z3,z55,z5]),(0,[z808,z1,z2,z3,z8,z5])],[(0,[z168,z1,z30,z3,z8,z5]),(0,[z0,z809,z2,z3,z8,z5]),(0,[z0,z611,z1,z810,z3,z5]),(0,[z0,z1,z32,z40,z3,z97]),(0,[z0,z1,z2,z170,z43,z111])],[(0,[z0,z1,z78,z3,z8,z5]),(0,[z0,z1,z2,z811,z3,z12])],[(0,[z7,z2,z3,z80,z100,z5]),(0,[z185,z1,z30,z3,z8,z5]),(0,[z0,z1,z387,z118,z8,z5]),(0,[z0,z1,z812,z3,z8,z5]),(0,[z0,z1,z813,z3,z8,z5])],[(0,[z0,z814,z1,z30,z3,z8]),(0,[z0,z1,z16,z3,z195,z5]),(0,[z0,z1,z2,z521,z8,z186]),(0,[z286,z0,z2,z3,z100,z5]),(0,[z0,z1,z2,z815,z8,z5])],[(0,[z192,z0,z1,z2,z3,z5]),(0,[z0,z1,z816,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z817]),(0,[z0,z1,z2,z818,z3,z8]),(0,[z0,z1,z3,z8,z819,z5]),(0,[z0,z1,z820,z3,z8,z5])],[(0,[z0,z1,z2,z821,z8,z5]),(0,[z0,z1,z16,z3,z8,z159]),(0,[z0,z1,z2,z197,z3,z8]),(0,[z822,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z436,z43,z5]),(0,[z0,z1,z2,z3,z8,z823])],[(0,[z53,z79,z2,z3,z80,z5])],[(0,[z0,z1,z115,z3,z97,z5]),(0,[z49,z0,z16,z3,z8,z20]),(0,[z116,z1,z2,z3,z8,z10])],[(0,[z0,z26,z2,z3,z312,z5]),(0,[z0,z611,z1,z824,z3,z5])]],
   [[(0,[z35,z1,z279,z3,z8,z5]),(0,[z106,z0,z1,z2,z462,z8])],[(0,[z0,z1,z16,z184,z8,z5]),(0,[z0,z1,z2,z3,z8,z825]),(0,[z25,z1,z2,z58,z8,z5]),(0,[z18,z0,z1,z209,z3,z12]),(0,[z18,z0,z1,z2,z3,z159]),(0,[z0,z1,z415,z3,z96,z5])],[(1,[z1,z2,z3,z788,z5]),(0,[z0,z1,z3,z8,z826,z5])],[(0,[z827,z1,z2,z3,z8,z5])],[(0,[z0,z1,z828,z3,z8,z5]),(0,[z0,z1,z30,z3,z96,z12]),(0,[z0,z1,z2,z242,z43,z5]),(0,[z0,z274,z2,z3,z8,z152]),(0,[z0,z829,z2,z3,z8,z5]),(0,[z0,z408,z1,z2,z3,z12])],[(0,[z0,z1,z30,z3,z8,z123]),(0,[z0,z1,z2,z3,z8,z830]),(0,[z0,z1,z16,z177,z8,z5])],[(0,[z0,z1,z2,z3,z8,z831])],[(0,[z192,z143,z1,z2,z3,z5]),(0,[z0,z1,z832,z3,z8,z5]),(0,[z0,z1,z30,z3,z8,z132]),(0,[z0,z1,z833,z3,z8,z5])],[(0,[z0,z1,z2,z3,z213,z12]),(0,[z0,z1,z2,z3,z8,z834]),(0,[z0,z1,z2,z835,z8,z5]),(0,[z0,z611,z1,z2,z3,z836])],[(0,[z0,z1,z326,z3,z8,z145]),(0,[z23,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z837,z3,z8]),(0,[z0,z838,z2,z3,z8,z5]),(0,[z53,z128,z2,z3,z80,z5]),(0,[z0,z1,z2,z839,z8,z5]),(0,[z0,z19,z117,z2,z3,z8]),(0,[z49,z0,z322,z2,z3,z8]),(0,[z0,z1,z2,z3,z86,z132]),(0,[z0,z1,z2,z333,z8,z5])],[(0,[z425,z1,z16,z3,z8,z5]),(0,[z0,z1,z504,z3,z420,z5]),(1,[z1,z2,z797,z8,z5]),(0,[z0,z1,z2,z3,z8,z840]),(0,[z0,z611,z1,z2,z43,z5]),(0,[z610,z1,z335,z3,z8,z5]),(0,[z0,z1,z82,z375,z3,z8])],[],[(0,[z157,z1,z30,z3,z8,z5]),(0,[z0,z841,z1,z2,z3,z8]),(0,[z443,z0,z136,z3,z8,z5]),(0,[z0,z244,z1,z150,z3,z8])],[(0,[z0,z1,z842,z3,z8,z5]),(0,[z0,z814,z1,z2,z3,z8]),(0,[z0,z1,z2,z843,z8,z5]),(0,[z0,z1,z40,z3,z8,z517])],[(0,[z844,z0,z1,z2,z8,z5]),(0,[z0,z1,z2,z3,z86,z27]),(0,[z0,z1,z845,z3,z8,z12])],[(0,[z0,z1,z2,z3,z846,z5]),(0,[z1,z832,z30,z3,z8,z5]),(0,[z0,z1,z22,z118,z8,z12])]],
   [[(0,[z506,z1,z30,z3,z8,z5]),(0,[z141,z0,z121,z1,z16,z5]),(0,[z0,z1,z2,z8,z847,z5]),(0,[z0,z1,z335,z40,z3,z8]),(0,[z0,z244,z1,z3,z8,z92])],[(0,[z0,z1,z2,z848,z3,z8]),(0,[z0,z228,z30,z3,z8,z5]),(0,[z0,z406,z2,z3,z8,z278]),(0,[z0,z1,z2,z3,z8,z849])],[(0,[z0,z1,z2,z3,z243,z12])],[(0,[z0,z1,z16,z3,z8,z5]),(0,[z0,z167,z2,z3,z639,z5]),(0,[z0,z1,z118,z8,z556,z5]),(0,[z0,z1,z2,z67,z3,z12])],[(0,[z0,z7,z2,z184,z8,z5]),(0,[z0,z1,z2,z3,z353,z145]),(0,[z0,z1,z850,z3,z8,z5]),(0,[z0,z70,z2,z130,z107,z8]),(0,[z0,z1,z32,z3,z294,z5])],[(0,[z0,z1,z2,z851,z8,z5]),(0,[z0,z1,z2,z852,z3,z8]),(0,[z0,z1,z2,z3,z853,z5]),(0,[z0,z70,z2,z40,z107,z8]),(0,[z0,z854,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z855])],[(0,[z0,z1,z16,z3,z8,z252]),(0,[z0,z275,z1,z3,z8,z113]),(0,[z0,z1,z2,z3,z312,z278]),(0,[z0,z1,z2,z3,z257,z12]),(0,[z0,z1,z2,z8,z856,z5])],[(0,[z0,z1,z2,z3,z8,z836])],[(0,[z0,z1,z279,z3,z8,z12]),(0,[z0,z1,z2,z3,z560,z12])],[(0,[z0,z1,z857,z3,z8,z5]),(0,[z0,z858,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z859,z5])],[(0,[z0,z1,z2,z208,z3,z12]),(0,[z0,z1,z860,z3,z8,z5]),(0,[z0,z1,z2,z3,z265,z12])],[(0,[z0,z90,z2,z3,z8,z145]),(0,[z345,z7,z2,z3,z8,z5]),(0,[z18,z0,z1,z2,z3,z252]),(0,[z0,z1,z2,z40,z3,z280])],[(0,[z0,z1,z861,z3,z8,z5]),(0,[z0,z1,z862,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z863]),(0,[z0,z1,z2,z40,z3,z12])],[(0,[z0,z1,z864,z3,z8,z5])],[(0,[z0,z1,z238,z3,z69,z5]),(0,[z0,z196,z1,z2,z333,z5])],[(0,[z0,z1,z2,z230,z8,z5]),(0,[z0,z1,z2,z3,z312,z865]),(0,[z0,z1,z866,z3,z8,z5]),(0,[z143,z1,z552,z3,z55,z5]),(0,[z0,z1,z2,z124,z8,z12]),(0,[z0,z1,z867,z3,z8,z5]),(0,[z0,z1,z813,z40,z3,z8])]],
   [[(0,[z0,z1,z2,z868,z8,z5]),(0,[z0,z1,z372,z40,z3,z8]),(0,[z0,z1,z2,z462,z3,z8])],[(0,[z0,z1,z2,z869,z8,z5]),(0,[z77,z7,z2,z40,z3,z8]),(0,[z542,z7,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z327,z8]),(0,[z0,z1,z2,z870,z3,z8])],[(0,[z0,z1,z2,z3,z8,z871]),(0,[z0,z1,z872,z3,z8,z5]),(0,[z0,z1,z30,z234,z3,z8]),(0,[z0,z1,z2,z3,z467,z5]),(0,[z0,z1,z2,z873,z8,z5]),(0,[z320,z1,z2,z3,z8,z10]),(0,[z0,z1,z874,z3,z8,z5])],[(0,[z0,z1,z30,z3,z235,z5]),(0,[z0,z1,z2,z875,z8,z5]),(0,[z0,z1,z2,z876,z8,z5]),(0,[z0,z1,z877,z3,z8,z5])],[(0,[z0,z1,z2,z878,z8,z5])],[(0,[z0,z1,z2,z3,z227,z12]),(0,[z0,z1,z2,z3,z300,z12])],[(0,[z879,z0,z1,z2,z8,z5]),(0,[z0,z406,z2,z3,z8,z12]),(0,[z0,z1,z246,z3,z312,z5]),(0,[z0,z1,z2,z64,z8,z131]),(0,[z0,z1,z3,z97,z96,z12])],[],[(0,[z0,z1,z291,z3,z8,z12]),(0,[z0,z1,z609,z2,z3,z12])],[(0,[z0,z1,z30,z880,z3,z8]),(0,[z0,z1,z30,z3,z8,z122]),(0,[z0,z1,z16,z3,z8,z780]),(0,[z0,z1,z881,z3,z8,z5]),(0,[z0,z167,z2,z3,z229,z12]),(0,[z126,z0,z1,z2,z37,z8])],[(0,[z1,z30,z3,z8,z245,z5]),(0,[z0,z1,z882,z3,z8,z5]),(0,[z0,z1,z3,z8,z883,z5]),(0,[z53,z1,z2,z3,z80,z252]),(0,[z0,z167,z602,z2,z3,z5]),(0,[z0,z1,z2,z197,z3,z12]),(0,[z0,z1,z884,z3,z8,z5]),(0,[z0,z1,z3,z8,z885,z119])],[(0,[z0,z1,z336,z3,z8,z12]),(0,[z0,z1,z30,z64,z8,z5]),(0,[z472,z1,z16,z3,z8,z5]),(0,[z651,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z312,z12]),(0,[z0,z1,z2,z163,z43,z5]),(0,[z0,z1,z886,z3,z8,z5]),(0,[z0,z65,z1,z3,z96,z426]),(0,[z0,z887,z2,z3,z8,z12])],[(0,[z77,z7,z2,z184,z8,z5]),(0,[z0,z79,z16,z3,z8,z5]),(0,[z0,z196,z1,z2,z462,z3])],[(0,[z0,z1,z888,z3,z8,z5]),(0,[z0,z889,z1,z2,z3,z8]),(0,[z0,z1,z335,z3,z8,z5]),(0,[z890,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z891])],[(0,[z0,z1,z892,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z893]),(0,[z0,z281,z1,z2,z3,z131]),(0,[z21,z0,z1,z40,z8,z87]),(0,[z0,z1,z150,z2,z3,z12]),(0,[z106,z0,z121,z1,z2,z5])],[(0,[z0,z1,z894,z3,z8,z5]),(0,[z53,z1,z16,z3,z80,z5]),(0,[z0,z70,z2,z8,z895,z5]),(0,[z0,z611,z1,z2,z327,z5])]],
   [[(0,[z0,z896,z2,z3,z8,z5]),(0,[z897,z1,z2,z3,z8,z5]),(0,[z176,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z898,z5])],[(0,[z0,z1,z30,z3,z8,z271]),(0,[z0,z70,z16,z107,z8,z5]),(0,[z0,z437,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z899,z5])],[(0,[z0,z1,z2,z900,z8,z5]),(0,[z0,z26,z2,z3,z420,z5]),(0,[z610,z1,z2,z327,z8,z5])],[(0,[z0,z1,z2,z3,z8,z901]),(0,[z1,z2,z3,z797,z8,z5]),(0,[z0,z1,z902,z3,z8,z5])],[(0,[z0,z1,z3,z8,z903,z5]),(0,[z0,z1,z904,z3,z8,z5])],[(0,[z0,z1,z2,z3,z294,z5])],[(0,[z77,z641,z7,z2,z3,z5]),(0,[z0,z905,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z906,z5])],[(0,[z487,z0,z1,z2,z3,z12])],[(0,[z0,z1,z2,z3,z907,z5]),(0,[z0,z128,z16,z3,z8,z5]),(0,[z0,z1,z16,z130,z3,z8]),(0,[z0,z1,z118,z8,z856,z5])],[(0,[z0,z1,z908,z3,z8,z5]),(0,[z0,z19,z16,z3,z8,z152]),(0,[z0,z1,z909,z3,z8,z5]),(0,[z0,z1,z2,z747,z3,z12])],[(0,[z0,z1,z30,z3,z8,z131]),(0,[z0,z1,z30,z3,z43,z12]),(1,[z0,z753,z1,z2,z5])],[(0,[z0,z1,z2,z3,z910,z5]),(0,[z412,z1,z2,z3,z80,z5]),(0,[z0,z538,z1,z3,z96,z5]),(0,[z0,z1,z3,z8,z885,z5])],[(0,[z0,z1,z911,z3,z8,z5]),(0,[z0,z1,z2,z3,z405,z12]),(0,[z0,z167,z1,z2,z3,z159]),(0,[z21,z0,z1,z3,z96,z12])],[(0,[z0,z1,z2,z3,z8,z912]),(0,[z0,z1,z2,z913,z8,z5]),(0,[z0,z1,z641,z16,z3,z5]),(0,[z0,z1,z372,z3,z8,z5]),(0,[z11,z0,z733,z3,z8,z5]),(0,[z0,z1,z2,z3,z86,z914]),(0,[z0,z1,z2,z3,z8,z915])],[(0,[z77,z7,z2,z3,z8,z5]),(0,[z0,z1,z387,z382,z8,z5]),(0,[z0,z1,z2,z3,z8,z377]),(0,[z0,z117,z2,z40,z3,z8]),(0,[z0,z167,z2,z3,z46,z12]),(0,[z21,z0,z1,z294,z87,z5]),(0,[z0,z1,z67,z3,z8,z12]),(0,[z0,z1,z2,z3,z916,z12])],[(0,[z0,z1,z82,z3,z8,z637]),(0,[z331,z0,z1,z2,z3,z12]),(0,[z0,z1,z3,z8,z917,z5])]],
   [[(0,[z0,z1,z2,z918,z3,z5]),(0,[z0,z919,z2,z3,z8,z5]),(0,[z142,z0,z1,z16,z37,z8]),(0,[z0,z1,z165,z394,z8,z5]),(0,[z0,z1,z2,z3,z80,z12]),(0,[z0,z1,z2,z3,z920,z5])],[(0,[z1,z30,z3,z311,z8,z5]),(0,[z0,z1,z30,z3,z86,z5]),(0,[z0,z1,z2,z3,z8,z921]),(0,[z0,z1,z2,z3,z922,z5]),(0,[z0,z1,z2,z3,z8,z923])],[(0,[z438,z0,z2,z3,z100,z5]),(0,[z0,z600,z61,z3,z8,z5]),(0,[z0,z569,z1,z2,z3,z12])],[(0,[z0,z1,z2,z924,z8,z5]),(0,[z0,z1,z2,z3,z925,z5]),(0,[z0,z1,z2,z852,z3,z12]),(0,[z0,z1,z2,z926,z3,z8])],[(0,[z0,z1,z2,z927,z3,z5]),(0,[z0,z1,z2,z928,z3,z8]),(0,[z0,z1,z929,z3,z8,z5])],[(0,[z0,z1,z2,z395,z8,z5]),(0,[z0,z1,z2,z293,z3,z12])],[(0,[z0,z1,z326,z3,z8,z12]),(0,[z487,z0,z2,z8,z62,z5])],[(0,[z0,z1,z2,z930,z3,z8]),(0,[z0,z1,z30,z3,z931,z5]),(0,[z0,z1,z16,z197,z3,z8]),(0,[z18,z0,z1,z16,z3,z12]),(0,[z25,z1,z2,z40,z58,z8]),(0,[z0,z1,z2,z3,z8,z932]),(0,[z141,z0,z611,z1,z2,z5]),(0,[z18,z610,z2,z3,z100,z5]),(0,[z0,z1,z933,z3,z8,z5])],[(0,[z192,z0,z2,z3,z100,z5]),(0,[z0,z1,z2,z3,z8,z934]),(0,[z0,z1,z2,z3,z8,z935])],[(0,[z0,z1,z2,z3,z8,z936]),(0,[z116,z1,z16,z3,z8,z10]),(0,[z0,z1,z2,z3,z420,z278]),(0,[z0,z1,z2,z148,z166,z5]),(0,[z937,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z389,z12]),(0,[z0,z1,z2,z3,z8,z938]),(0,[z0,z1,z2,z40,z170,z43])],[(0,[z0,z1,z939,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z940]),(0,[z0,z259,z2,z107,z8,z5]),(0,[z0,z1,z2,z941,z3,z8])],[(0,[z0,z942,z2,z3,z8,z5]),(0,[z0,z1,z943,z3,z8,z5]),(0,[z141,z0,z121,z1,z2,z451])],[(0,[z25,z1,z16,z58,z8,z5]),(0,[z0,z421,z2,z3,z235,z5]),(0,[z0,z1,z944,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z945]),(0,[z0,z1,z2,z946,z8,z5])],[(0,[z0,z1,z2,z3,z8,z145]),(0,[z0,z1,z2,z3,z947,z5]),(0,[z0,z1,z2,z3,z8,z948]),(0,[z0,z733,z136,z3,z8,z5])],[(0,[z320,z7,z2,z3,z8,z5]),(0,[z0,z1,z641,z2,z40,z3]),(0,[z0,z1,z2,z3,z524,z12]),(0,[z0,z1,z2,z178,z8,z186])],[(0,[z0,z1,z78,z230,z8,z5]),(0,[z0,z1,z30,z3,z8,z27]),(0,[z0,z1,z949,z3,z8,z5]),(0,[z0,z1,z165,z3,z8,z59]),(0,[z0,z1,z2,z3,z950,z5]),(0,[z0,z1,z951,z3,z8,z5])]],
   [[(0,[z0,z1,z326,z3,z4,z5]),(0,[z388,z1,z30,z3,z8,z5]),(0,[z0,z99,z1,z16,z3,z5]),(0,[z0,z61,z733,z3,z8,z5]),(0,[z176,z1,z2,z3,z8,z132])],[(0,[z0,z1,z2,z3,z353,z12]),(0,[z0,z952,z1,z2,z3,z5]),(0,[z192,z0,z1,z2,z953,z5]),(0,[z0,z1,z2,z3,z954,z5]),(0,[z0,z1,z552,z3,z8,z12]),(0,[z143,z1,z2,z3,z788,z5]),(0,[z0,z1,z2,z124,z8,z38]),(0,[z290,z0,z109,z3,z8,z5]),(0,[z955,z1,z2,z3,z8,z5]),(0,[z0,z1,z3,z8,z956,z5]),(0,[z0,z19,z2,z295,z3,z8]),(0,[z0,z437,z2,z3,z8,z132])],[(0,[z0,z1,z957,z3,z8,z5]),(0,[z0,z196,z1,z16,z40,z3]),(0,[z0,z19,z1,z2,z124,z8]),(0,[z0,z1,z2,z958,z8,z5])],[(0,[z0,z1,z2,z3,z8,z959]),(0,[z0,z960,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z834])],[(0,[z0,z1,z16,z837,z3,z8]),(0,[z0,z1,z16,z333,z8,z5]),(0,[z0,z1,z2,z3,z8,z961]),(0,[z240,z1,z2,z3,z8,z10]),(0,[z176,z1,z22,z3,z8,z5]),(0,[z0,z1,z3,z8,z708,z5]),(0,[z0,z1,z2,z3,z565,z12]),(0,[z613,z1,z2,z463,z3,z8])],[(0,[z129,z7,z2,z3,z8,z5]),(0,[z0,z1,z2,z394,z8,z12]),(0,[z0,z1,z2,z327,z8,z5]),(0,[z39,z0,z2,z8,z895,z5]),(0,[z0,z65,z1,z3,z96,z66]),(0,[z0,z1,z2,z40,z3,z473])],[(0,[z879,z0,z1,z30,z8,z5]),(0,[z0,z167,z1,z2,z3,z252]),(1,[z1,z2,z3,z8,z783]),(1,[z0,z2,z3,z773,z5]),(0,[z0,z1,z2,z3,z8,z962]),(0,[z0,z1,z2,z3,z8,z963])],[(0,[z0,z1,z491,z40,z3,z8]),(0,[z185,z1,z279,z148,z8,z5]),(0,[z0,z1,z2,z3,z788,z5]),(0,[z116,z1,z274,z2,z3,z8]),(0,[z0,z1,z500,z3,z8,z451])],[(0,[z0,z1,z2,z3,z431,z12])],[(0,[z0,z1,z30,z3,z964,z5]),(0,[z0,z52,z1,z3,z8,z92]),(0,[z0,z1,z246,z3,z420,z5]),(0,[z9,z411,z1,z2,z3,z8]),(1,[z0,z1,z335,z3,z12]),(0,[z0,z2,z3,z8,z965,z12])],[(0,[z0,z1,z2,z3,z966,z5]),(0,[z0,z1,z2,z719,z3,z8]),(0,[z306,z1,z2,z64,z8,z5]),(0,[z176,z228,z2,z3,z8,z5]),(0,[z21,z0,z1,z8,z87,z5]),(0,[z0,z1,z500,z3,z8,z5])],[(0,[z0,z117,z2,z3,z8,z5]),(0,[z49,z0,z6,z2,z3,z8]),(0,[z0,z1,z967,z3,z8,z5])],[(0,[z0,z1,z504,z40,z3,z8]),(0,[z0,z2,z3,z8,z20,z968])],[(0,[z0,z139,z1,z16,z3,z8]),(0,[z0,z1,z2,z3,z8,z969]),(0,[z0,z1,z2,z3,z8,z968]),(0,[z106,z0,z1,z2,z8,z98])],[(0,[z0,z26,z2,z3,z8,z5]),(0,[z0,z1,z970,z3,z8,z5]),(0,[z0,z1,z2,z3,z420,z12]),(0,[z0,z109,z3,z8,z348,z5])],[(0,[z0,z1,z30,z3,z8,z98]),(0,[z0,z1,z2,z797,z8,z5]),(0,[z0,z1,z2,z3,z166,z5]),(0,[z0,z1,z2,z3,z971,z5]),(0,[z214,z1,z2,z3,z8,z51])]],
   [[(0,[z0,z972,z2,z3,z8,z5]),(0,[z0,z1,z16,z851,z8,z5]),(0,[z0,z973,z2,z3,z8,z12]),(0,[z0,z1,z2,z325,z8,z191])],[(0,[z0,z1,z2,z3,z8,z974]),(0,[z595,z228,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z42,z12]),(0,[z0,z99,z1,z2,z40,z3]),(0,[z0,z975,z1,z2,z3,z5])],[(0,[z258,z1,z16,z3,z8,z5]),(0,[z1,z79,z2,z3,z80,z5]),(0,[z0,z1,z2,z40,z333,z8]),(0,[z0,z753,z1,z2,z170,z5]),(0,[z0,z1,z2,z251,z8,z255])],[(0,[z0,z1,z976,z3,z8,z5]),(0,[z185,z1,z30,z58,z8,z5]),(0,[z0,z1,z977,z3,z8,z5]),(0,[z0,z1,z54,z3,z8,z12]),(0,[z0,z1,z2,z3,z594,z12]),(0,[z0,z548,z1,z3,z8,z92])],[(0,[z0,z1,z326,z3,z8,z123]),(0,[z0,z1,z2,z3,z8,z978]),(0,[z0,z1,z2,z979,z3,z8]),(0,[z0,z1,z2,z3,z280,z38]),(0,[z176,z1,z2,z8,z43,z5])],[(0,[z0,z1,z2,z980,z3,z8]),(0,[z18,z0,z2,z3,z100,z5]),(0,[z0,z1,z2,z251,z8,z186])],[(0,[z0,z981,z2,z3,z8,z5])],[(0,[z0,z1,z2,z982,z8,z5]),(0,[z1,z47,z30,z3,z8,z5]),(0,[z1,z387,z30,z58,z8,z5]),(0,[z0,z983,z2,z3,z8,z5]),(0,[z0,z1,z16,z40,z3,z12]),(0,[z0,z1,z2,z3,z8,z984]),(0,[z0,z1,z165,z177,z8,z5]),(0,[z610,z1,z2,z3,z8,z12]),(0,[z0,z1,z2,z985,z3,z8])],[(0,[z0,z421,z30,z3,z8,z5]),(0,[z0,z1,z246,z40,z3,z8]),(0,[z0,z1,z2,z3,z986,z5]),(0,[z0,z1,z2,z987,z8,z5])],[(0,[z1,z504,z3,z58,z8,z5]),(0,[z0,z988,z2,z3,z8,z5]),(0,[z575,z1,z2,z3,z8,z38]),(0,[z0,z1,z2,z43,z62,z12]),(0,[z306,z1,z2,z3,z8,z131]),(0,[z0,z1,z2,z3,z989,z5]),(0,[z0,z1,z2,z3,z294,z823])],[(0,[z0,z1,z16,z230,z8,z5]),(0,[z0,z1,z30,z3,z8,z426]),(0,[z0,z1,z2,z3,z64,z12])],[(0,[z0,z1,z2,z744,z8,z5]),(0,[z1,z16,z56,z3,z8,z5]),(0,[z0,z121,z1,z16,z3,z12]),(0,[z0,z65,z1,z3,z475,z5]),(0,[z0,z1,z16,z462,z3,z8]),(0,[z290,z0,z1,z40,z3,z8]),(0,[z112,z0,z2,z624,z3,z8])],[(0,[z0,z990,z2,z3,z8,z5]),(0,[z0,z1,z991,z3,z8,z5]),(0,[z0,z1,z32,z462,z3,z97])],[(0,[z0,z1,z30,z34,z3,z12]),(0,[z0,z1,z16,z3,z467,z5]),(0,[z0,z1,z2,z3,z992,z5]),(0,[z0,z228,z3,z8,z96,z5])],[(0,[z77,z7,z78,z3,z8,z5]),(0,[z306,z1,z30,z3,z8,z5]),(0,[z0,z993,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z353,z123]),(0,[z0,z1,z2,z3,z475,z12]),(0,[z286,z0,z1,z2,z3,z12]),(0,[z0,z121,z1,z2,z327,z5]),(0,[z0,z1,z2,z663,z3,z12]),(0,[z0,z1,z2,z40,z3,z195])]],
   [[(0,[z0,z6,z1,z16,z3,z8]),(0,[z0,z1,z61,z3,z96,z12]),(0,[z0,z1,z2,z994,z3,z8]),(0,[z306,z167,z2,z3,z8,z5]),(0,[z0,z1,z995,z3,z8,z5])],[(0,[z582,z1,z30,z3,z8,z5]),(0,[z0,z996,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z195,z12]),(0,[z0,z1,z2,z333,z5,z12]),(0,[z0,z1,z2,z3,z997,z5]),(0,[z0,z1,z2,z3,z479,z12])],[(0,[z0,z1,z2,z998,z3,z5]),(0,[z0,z1,z346,z3,z235,z5]),(0,[z0,z1,z2,z713,z8,z5])],[(0,[z116,z1,z372,z3,z8,z10]),(0,[z0,z1,z118,z8,z625,z5])],[(0,[z0,z1,z491,z3,z8,z5]),(0,[z0,z421,z346,z3,z8,z5]),(0,[z11,z0,z136,z3,z8,z5]),(0,[z0,z1,z2,z3,z999,z5])],[(0,[z0,z1,z165,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z278]),(0,[z0,z1,z2,z3,z280,z12])],[],[(0,[z0,z1,z2,z3,z8,z1000]),(0,[z1,z768,z30,z3,z8,z5]),(0,[z25,z1,z2,z58,z8,z377]),(0,[z0,z1,z1001,z3,z8,z5]),(0,[z0,z1,z372,z395,z8,z5]),(0,[z0,z1,z1002,z2,z3,z8]),(0,[z0,z715,z2,z3,z8,z12])],[(0,[z0,z1,z2,z3,z8,z1003])],[(0,[z0,z1,z504,z3,z8,z5]),(0,[z290,z39,z0,z8,z62,z5])],[(0,[z0,z285,z61,z3,z8,z5]),(0,[z0,z109,z681,z3,z8,z5]),(0,[z595,z1,z2,z3,z8,z12]),(0,[z0,z1,z32,z3,z97,z5])],[(0,[z0,z1004,z1,z2,z3,z8]),(0,[z116,z1,z2,z395,z8,z10]),(0,[z0,z611,z1,z2,z3,z12]),(0,[z0,z1,z638,z2,z3,z12])],[(0,[z0,z1,z2,z177,z8,z12]),(0,[z0,z1,z2,z3,z1005,z5]),(0,[z0,z1,z209,z327,z8,z5]),(0,[z0,z196,z1,z2,z3,z131]),(0,[z0,z1,z2,z170,z43,z5])],[(0,[z0,z1,z2,z3,z1006,z5]),(0,[z0,z70,z2,z107,z166,z5]),(0,[z21,z0,z1,z8,z393,z5]),(0,[z0,z1,z1007,z3,z8,z5])],[(0,[z0,z1,z2,z184,z8,z145]),(0,[z0,z1,z2,z1008,z3,z8]),(0,[z0,z406,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z865]),(0,[z610,z1,z2,z3,z8,z216]),(0,[z0,z1,z3,z8,z517,z5])],[(0,[z0,z1,z2,z1009,z3,z8]),(0,[z1010,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z8,z895,z5]),(0,[z0,z121,z753,z1,z2,z5]),(0,[z0,z1,z1011,z3,z8,z5])]],
   [[(0,[z222,z0,z340,z3,z8,z5]),(0,[z0,z1,z32,z3,z69,z5]),(0,[z0,z1,z16,z3,z294,z5]),(0,[z0,z1012,z2,z3,z8,z5]),(0,[z0,z1,z335,z3,z43,z5]),(0,[z0,z1,z500,z40,z3,z8])],[(0,[z0,z6,z2,z3,z8,z152]),(0,[z0,z1,z2,z3,z8,z1013]),(0,[z0,z952,z1,z30,z3,z5]),(0,[z604,z1,z30,z3,z8,z5]),(0,[z104,z0,z2,z8,z62,z5]),(0,[z0,z1,z1014,z3,z8,z5]),(0,[z0,z1,z1015,z3,z8,z5]),(0,[z0,z1,z3,z8,z1016,z5]),(0,[z18,z0,z283,z2,z3,z5]),(0,[z0,z1,z2,z3,z430,z5]),(0,[z0,z1,z1017,z3,z8,z5])],[(0,[z0,z1,z2,z184,z4,z5]),(0,[z0,z167,z1,z16,z3,z12]),(0,[z1,z2,z148,z797,z8,z5]),(0,[z0,z1,z1018,z3,z8,z5])],[(0,[z0,z1,z30,z3,z312,z5]),(0,[z513,z1,z16,z3,z8,z5]),(0,[z0,z109,z733,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z86]),(0,[z0,z1,z1019,z3,z8,z5])],[(0,[z0,z1,z2,z3,z457,z12]),(0,[z0,z1,z16,z170,z43,z5]),(0,[z0,z26,z2,z40,z3,z8]),(0,[z0,z1,z2,z549,z43,z5]),(0,[z0,z1,z2,z325,z43,z5]),(0,[z0,z1,z2,z37,z3,z134])],[(0,[z0,z1,z246,z3,z8,z5]),(0,[z0,z1,z1020,z2,z3,z5]),(0,[z0,z1,z2,z3,z8,z1021])],[(0,[z0,z281,z1,z16,z3,z5]),(0,[z0,z1,z16,z3,z910,z5]),(0,[z0,z1,z2,z40,z3,z420]),(0,[z0,z2,z3,z46,z773,z5]),(0,[z0,z1,z2,z3,z1022,z5]),(0,[z0,z1,z2,z1023,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1024]),(0,[z0,z1,z2,z3,z8,z289])],[(0,[z290,z0,z1,z3,z8,z5]),(0,[z520,z0,z1,z3,z8,z492])],[(0,[z77,z7,z16,z3,z8,z5]),(0,[z0,z437,z30,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z377]),(0,[z0,z1,z2,z3,z525,z12])],[(0,[z0,z1,z2,z3,z8,z12]),(0,[z0,z1,z1025,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1026]),(0,[z306,z1,z2,z3,z100,z5]),(0,[z176,z1,z2,z3,z86,z5]),(0,[z0,z1,z2,z251,z134,z186])],[(0,[z0,z1,z16,z3,z80,z12]),(0,[z0,z26,z2,z148,z8,z5]),(0,[z0,z196,z1,z2,z197,z3]),(0,[z0,z437,z2,z3,z86,z5])],[(0,[z18,z0,z209,z3,z100,z5]),(0,[z49,z0,z1,z2,z3,z280])],[(0,[z0,z1,z2,z3,z1027,z5]),(0,[z0,z117,z2,z3,z8,z10]),(0,[z0,z1,z534,z40,z3,z8]),(0,[z0,z1,z2,z1028,z8,z5]),(0,[z0,z1,z82,z3,z195,z119])],[(0,[z77,z139,z7,z2,z3,z8]),(0,[z0,z79,z165,z3,z8,z5]),(0,[z0,z1,z1029,z3,z8,z5])],[(0,[z0,z1,z30,z447,z3,z8]),(0,[z11,z0,z507,z3,z8,z5]),(0,[z0,z1,z1030,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z3,z8,z1031]),(0,[z49,z0,z2,z3,z8,z532]),(0,[z0,z1,z2,z1032,z8,z5]),(0,[z0,z1,z16,z395,z8,z5]),(0,[z106,z0,z1,z16,z8,z5]),(0,[z1,z2,z3,z55,z80,z12])],[(0,[z1033,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z1034,z8,z5]),(0,[z0,z1,z2,z462,z3,z12]),(0,[z141,z0,z121,z1,z2,z5])],[(0,[z0,z640,z1,z2,z3,z12]),(0,[z0,z1,z2,z3,z134,z186])],[(0,[z0,z1,z2,z177,z55,z5]),(0,[z0,z1,z158,z40,z3,z8]),(0,[z0,z2,z3,z8,z968,z152]),(0,[z0,z228,z32,z3,z8,z5]),(0,[z0,z1,z1035,z3,z8,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z30,z3,z8,z66]),(0,[z0,z1036,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z219,z12])],[(0,[z77,z7,z2,z230,z8,z5]),(0,[z0,z1,z30,z1037,z8,z5]),(0,[z0,z285,z102,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z940]),(0,[z0,z1,z1038,z3,z8,z5]),(0,[z0,z1,z40,z3,z8,z63]),(0,[z0,z1,z335,z3,z5,z12])],[(0,[z0,z1,z30,z3,z1039,z5]),(0,[z0,z942,z16,z3,z8,z5])],[(0,[z0,z1,z2,z3,z586,z12]),(0,[z25,z26,z2,z58,z8,z5]),(0,[z0,z1,z372,z3,z467,z5]),(1,[z0,z1,z2,z64,z12]),(0,[z0,z281,z1,z2,z40,z3]),(0,[z0,z228,z2,z40,z3,z8]),(0,[z0,z1,z32,z3,z708,z5]),(0,[z0,z1,z1040,z40,z3,z8])],[(0,[z0,z1,z16,z3,z8,z145]),(0,[z0,z1,z3,z8,z1041,z5]),(0,[z176,z1,z2,z3,z8,z27]),(0,[z0,z1,z2,z37,z526,z8])],[(0,[z0,z1,z2,z3,z1042,z5]),(0,[z0,z437,z2,z3,z8,z27]),(0,[z0,z518,z1,z2,z3,z12])],[(0,[z0,z1,z2,z3,z8,z1043]),(0,[z192,z0,z1,z2,z3,z1044]),(0,[z0,z1,z2,z3,z8,z1045]),(0,[z0,z128,z165,z3,z8,z5]),(0,[z11,z0,z136,z40,z3,z8]),(0,[z1046,z1,z2,z3,z8,z5]),(0,[z595,z1,z2,z3,z8,z132])],[(0,[z0,z167,z7,z2,z3,z12]),(0,[z143,z1,z2,z3,z55,z5]),(0,[z0,z1,z165,z40,z3,z8]),(0,[z116,z1,z2,z3,z467,z10]),(0,[z0,z1,z3,z8,z63,z5]),(0,[z0,z1,z2,z315,z3,z12])],[(0,[z0,z1,z2,z1047,z8,z5]),(0,[z0,z6,z117,z2,z3,z8]),(0,[z0,z1,z16,z3,z954,z5]),(0,[z1048,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z1049,z5]),(0,[z18,z0,z167,z2,z3,z12])],[(0,[z1050,z0,z1,z2,z3,z5]),(0,[z106,z0,z1,z8,z96,z5]),(0,[z0,z99,z1,z2,z3,z451])],[(0,[z0,z1,z1051,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z817]),(0,[z0,z1052,z2,z3,z8,z5]),(0,[z0,z1,z2,z124,z235,z5]),(0,[z0,z109,z61,z3,z8,z12]),(0,[z39,z0,z2,z40,z8,z62])],[(0,[z1,z30,z58,z8,z62,z5]),(0,[z674,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z395,z467,z5]),(0,[z595,z1,z2,z3,z8,z27]),(0,[z141,z0,z121,z1,z2,z40]),(0,[z0,z427,z2,z295,z3,z8])]],
   [[(0,[z0,z1,z30,z3,z8,z111]),(0,[z35,z1,z16,z40,z3,z8]),(0,[z0,z1,z16,z327,z8,z5]),(0,[z0,z421,z2,z124,z8,z5]),(0,[z0,z70,z2,z193,z8,z5]),(0,[z39,z0,z2,z8,z62,z12]),(0,[z176,z1,z82,z3,z8,z5]),(0,[z0,z1,z2,z3,z1053,z5])],[(0,[z77,z6,z7,z2,z3,z8]),(0,[z0,z1,z2,z3,z8,z1054]),(0,[z0,z105,z1,z2,z3,z12]),(0,[z0,z1,z2,z3,z8,z216])],[(0,[z1,z30,z3,z8,z528,z5]),(0,[z0,z1,z2,z148,z8,z278]),(0,[z11,z176,z1,z3,z8,z5]),(0,[z0,z1,z2,z294,z43,z5]),(0,[z0,z1,z1055,z3,z8,z5])],[(0,[z0,z1,z17,z3,z8,z93]),(0,[z0,z79,z2,z3,z8,z12]),(0,[z0,z65,z1,z3,z96,z5])],[(0,[z129,z1,z2,z58,z8,z5]),(0,[z0,z1,z2,z3,z55,z252]),(0,[z0,z1056,z1,z2,z3,z5])],[(0,[z0,z1,z89,z3,z8,z12]),(0,[z0,z1,z2,z3,z1057,z5]),(0,[z1,z30,z3,z535,z8,z5]),(0,[z1058,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z885])],[(0,[z0,z117,z16,z3,z8,z5]),(0,[z0,z1,z1059,z3,z8,z5]),(0,[z0,z1,z2,z40,z177,z8]),(0,[z0,z1,z2,z40,z395,z8]),(0,[z0,z1,z82,z3,z8,z119])],[(0,[z0,z1,z2,z1060,z8,z5]),(0,[z1,z2,z3,z55,z788,z5]),(0,[z0,z1,z2,z3,z96,z12]),(0,[z0,z1,z2,z14,z43,z12]),(0,[z0,z1,z1061,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z123]),(0,[z0,z70,z2,z107,z8,z12]),(0,[z0,z1,z2,z327,z43,z5])],[(0,[z0,z1,z30,z3,z353,z5]),(0,[z0,z1062,z2,z3,z8,z5]),(0,[z0,z1063,z30,z3,z8,z5]),(0,[z0,z26,z16,z3,z8,z5]),(0,[z423,z1,z16,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1064])],[(0,[z0,z1,z2,z3,z8,z1044]),(0,[z0,z1,z534,z3,z8,z5]),(0,[z0,z1,z16,z3,z166,z5]),(0,[z0,z1,z2,z3,z8,z132]),(0,[z0,z1,z8,z856,z87,z5])],[(0,[z0,z1,z2,z3,z8,z783]),(0,[z0,z380,z1,z2,z3,z12])],[(0,[z0,z1065,z1,z2,z3,z8]),(0,[z0,z1,z251,z8,z517,z186]),(0,[z0,z1,z1066,z40,z3,z8])],[(0,[z0,z1,z30,z394,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1067]),(0,[z25,z1,z2,z58,z8,z278]),(0,[z1068,z1,z2,z3,z8,z5])],[(0,[z0,z1,z1069,z3,z8,z5]),(0,[z0,z128,z2,z3,z8,z12]),(0,[z18,z0,z2,z327,z100,z5]),(0,[z0,z1,z2,z3,z134,z12]),(0,[z0,z1,z2,z3,z255,z12])]],
   [[(0,[z0,z167,z2,z3,z409,z5]),(0,[z1,z30,z3,z58,z8,z12]),(0,[z0,z1,z158,z3,z8,z5]),(0,[z18,z0,z16,z3,z100,z5]),(0,[z0,z1,z16,z251,z8,z186]),(0,[z1070,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z1071,z3,z8]),(0,[z306,z196,z1,z2,z3,z5])],[(0,[z0,z1,z1072,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1073])],[(0,[z25,z1,z504,z58,z8,z5]),(0,[z0,z1,z1074,z3,z8,z5]),(0,[z185,z1,z2,z40,z148,z8]),(0,[z0,z1,z3,z8,z1075,z5]),(0,[z18,z0,z647,z2,z3,z5]),(0,[z0,z275,z1,z3,z8,z492])],[(0,[z11,z0,z228,z3,z8,z5])],[(0,[z0,z1,z2,z1076,z3,z8]),(0,[z0,z228,z2,z3,z8,z5]),(0,[z0,z1,z1077,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1078]),(0,[z141,z0,z121,z1,z500,z5]),(0,[z0,z1,z1040,z3,z8,z5])],[(0,[z1,z16,z30,z40,z3,z8]),(0,[z0,z117,z2,z3,z467,z5]),(0,[z0,z1,z2,z623,z8,z186]),(1,[z0,z733,z3,z8,z5]),(0,[z0,z1,z824,z3,z8,z5]),(0,[z0,z1,z1079,z3,z8,z5])],[(0,[z0,z1,z30,z3,z420,z5]),(0,[z0,z1,z16,z3,z8,z1067]),(0,[z0,z1080,z2,z3,z8,z5]),(0,[z0,z109,z228,z3,z8,z5]),(0,[z0,z1,z2,z870,z3,z86])],[(0,[z438,z0,z1,z2,z3,z12]),(0,[z210,z1,z2,z3,z80,z5]),(1,[z0,z1,z67,z3,z12])],[(0,[z1,z7,z2,z3,z353,z5]),(0,[z0,z121,z1,z2,z3,z289]),(0,[z18,z0,z1,z2,z64,z12]),(0,[z0,z1,z2,z3,z708,z5]),(0,[z106,z0,z1,z2,z97,z12])],[(0,[z0,z1,z2,z3,z1081,z5]),(0,[z0,z1,z1082,z2,z3,z5]),(0,[z0,z1,z2,z3,z8,z1083]),(0,[z0,z1,z3,z8,z92,z885]),(0,[z0,z1,z1084,z3,z8,z5])],[(0,[z0,z1,z78,z3,z8,z12]),(0,[z0,z1,z2,z3,z1085,z5]),(0,[z0,z1,z30,z124,z8,z5]),(0,[z292,z1,z30,z3,z8,z5]),(0,[z0,z1,z30,z3,z97,z12]),(0,[z0,z1,z16,z3,z475,z12]),(0,[z0,z79,z2,z3,z55,z5]),(0,[z0,z1,z335,z327,z8,z5]),(0,[z18,z0,z2,z3,z773,z5]),(0,[z0,z1,z1086,z3,z8,z5]),(0,[z0,z1,z500,z3,z96,z5])],[(0,[z0,z1,z2,z184,z8,z12]),(0,[z185,z1,z30,z3,z8,z12]),(0,[z0,z1,z165,z3,z8,z252]),(0,[z0,z1,z2,z1087,z3,z8])],[(0,[z0,z1,z2,z3,z180,z12]),(0,[z0,z1,z30,z3,z8,z59]),(0,[z0,z1,z2,z815,z8,z12])],[(0,[z0,z1,z641,z30,z3,z5]),(0,[z192,z0,z1,z2,z3,z12]),(0,[z35,z1,z16,z3,z8,z5]),(0,[z18,z0,z1,z335,z3,z12]),(0,[z0,z1,z2,z664,z43,z5])],[(0,[z0,z1088,z1,z2,z3,z8]),(0,[z0,z277,z1,z2,z3,z12]),(0,[z29,z1,z30,z40,z3,z8]),(0,[z1089,z0,z1,z16,z8,z5]),(0,[z25,z1,z246,z58,z8,z5]),(0,[z499,z1,z2,z3,z55,z5])],[(0,[z0,z1,z2,z40,z3,z353]),(0,[z1,z748,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1090]),(0,[z1091,z1,z2,z3,z8,z5]),(0,[z49,z0,z2,z3,z8,z482])]],
   [[(0,[z0,z1,z78,z3,z8,z145]),(0,[z0,z1,z30,z3,z55,z12]),(0,[z142,z0,z1,z30,z37,z8]),(0,[z0,z1,z16,z3,z8,z278]),(0,[z0,z1,z2,z37,z545,z8]),(0,[z21,z0,z1,z8,z533,z5]),(0,[z0,z1,z2,z3,z201,z12])],[(0,[z192,z306,z1,z2,z3,z5]),(0,[z319,z1,z30,z58,z8,z5]),(0,[z0,z1,z1092,z3,z8,z5])],[(0,[z0,z406,z2,z3,z312,z5]),(0,[z0,z2,z107,z8,z895,z5]),(0,[z0,z1,z2,z3,z8,z1093]),(0,[z0,z1,z2,z3,z1094,z5]),(0,[z142,z0,z1,z2,z14,z8])],[(0,[z77,z7,z2,z3,z8,z145]),(0,[z25,z1,z2,z58,z8,z12]),(0,[z495,z0,z1,z2,z3,z12]),(0,[z0,z1,z2,z1095,z8,z5]),(0,[z0,z1,z415,z3,z96,z12]),(0,[z0,z1,z67,z3,z8,z122])],[(0,[z0,z1,z78,z3,z4,z5]),(0,[z0,z1,z2,z3,z8,z1096]),(0,[z9,z1,z2,z3,z8,z783]),(0,[z0,z1,z2,z3,z166,z891]),(0,[z0,z1,z150,z2,z3,z195])],[(0,[z0,z1,z1097,z3,z8,z5]),(0,[z0,z1,z2,z3,z80,z122]),(0,[z290,z0,z136,z3,z8,z5]),(0,[z0,z611,z1,z2,z3,z271]),(0,[z21,z176,z1,z8,z87,z5]),(0,[z0,z1,z2,z1098,z8,z5]),(0,[z0,z1,z2,z234,z3,z8]),(0,[z0,z1,z2,z713,z3,z8])],[(0,[z0,z1,z346,z124,z8,z5]),(0,[z0,z582,z2,z8,z62,z5])],[(0,[z18,z0,z1,z30,z3,z12]),(1,[z306,z2,z3,z100,z5]),(0,[z112,z0,z2,z3,z8,z20]),(0,[z0,z1,z500,z3,z294,z5])],[(0,[z0,z1,z16,z3,z1006,z5]),(0,[z0,z1099,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z783]),(0,[z0,z1,z209,z3,z8,z216])],[(0,[z309,z0,z2,z8,z62,z5]),(0,[z185,z1,z2,z148,z8,z5]),(0,[z0,z1,z1066,z3,z8,z5]),(0,[z143,z306,z1,z2,z3,z5]),(0,[z0,z1,z2,z1100,z8,z5]),(0,[z0,z19,z2,z33,z3,z8]),(0,[z0,z1,z118,z3,z96,z12])],[(0,[z0,z1,z1101,z3,z8,z5]),(0,[z18,z0,z335,z3,z100,z5])],[(0,[z15,z1,z2,z3,z80,z12]),(0,[z91,z1,z30,z3,z8,z5]),(0,[z176,z1,z30,z3,z8,z5]),(0,[z141,z1,z30,z58,z8,z5]),(0,[z267,z1,z30,z3,z8,z5]),(0,[z0,z662,z1,z2,z3,z12]),(0,[z0,z1,z2,z40,z3,z294])],[(0,[z0,z1,z2,z880,z3,z8]),(0,[z0,z1,z16,z3,z430,z5]),(0,[z0,z1,z2,z3,z8,z122])],[(0,[z0,z1,z30,z3,z280,z5]),(0,[z448,z1,z16,z3,z8,z5]),(0,[z0,z1,z1102,z3,z8,z5]),(0,[z0,z1,z2,z3,z55,z159]),(0,[z0,z1,z2,z811,z34,z3])],[(0,[z0,z1,z2,z1103,z3,z5]),(0,[z0,z1,z1104,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1105]),(0,[z237,z1,z30,z3,z8,z5]),(0,[z1,z2,z3,z8,z788,z5]),(0,[z0,z1,z2,z3,z239,z12]),(0,[z0,z1,z1106,z3,z8,z5])],[(0,[z0,z1,z2,z1107,z3,z4]),(0,[z1108,z0,z1,z3,z8,z5]),(0,[z585,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1109]),(0,[z240,z1,z2,z58,z8,z5])]],
   [[(0,[z0,z1,z641,z2,z3,z5]),(0,[z0,z99,z1,z30,z3,z5]),(0,[z0,z1,z2,z3,z8,z1110]),(0,[z18,z0,z1,z2,z177,z5]),(0,[z0,z117,z372,z3,z8,z5]),(0,[z0,z1,z1111,z3,z8,z5]),(0,[z0,z1,z344,z40,z3,z8])],[(0,[z0,z1,z1112,z3,z8,z5])],[(0,[z1,z16,z30,z3,z8,z5]),(0,[z595,z1,z30,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z289]),(0,[z0,z121,z1,z2,z3,z216])],[(0,[z0,z1,z2,z1113,z3,z353]),(0,[z0,z1,z1114,z3,z8,z5]),(0,[z142,z0,z1,z2,z37,z8])],[(0,[z0,z1,z3,z8,z1115,z5]),(0,[z0,z26,z2,z3,z8,z377]),(0,[z53,z1,z165,z3,z80,z5]),(0,[z116,z117,z2,z3,z8,z10]),(0,[z0,z1,z2,z40,z3,z235]),(0,[z0,z1,z2,z3,z8,z271]),(0,[z595,z1,z2,z3,z86,z5])],[(0,[z0,z1,z16,z3,z8,z12]),(0,[z9,z1,z2,z3,z8,z38])],[(0,[z1116,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z1117,z5]),(0,[z0,z1,z2,z3,z8,z1118]),(0,[z21,z0,z228,z8,z87,z5])],[(0,[z0,z1,z2,z1119,z8,z5]),(0,[z0,z1,z2,z3,z1120,z5]),(0,[z0,z1,z2,z462,z333,z8])],[(1,[z1,z768,z3,z8,z5]),(0,[z0,z117,z2,z395,z8,z5])],[(0,[z0,z1,z2,z184,z8,z123]),(0,[z0,z167,z30,z3,z46,z5]),(0,[z0,z1,z30,z3,z8,z1121])],[(0,[z192,z0,z1,z1072,z3,z5]),(0,[z571,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z43,z289]),(0,[z0,z1,z2,z1122,z3,z8]),(0,[z18,z0,z1,z2,z3,z12])],[(0,[z0,z1,z2,z3,z8,z1123]),(0,[z0,z1,z2,z1124,z8,z5]),(0,[z29,z1,z30,z3,z8,z5]),(0,[z185,z1,z832,z3,z8,z5]),(0,[z0,z1,z2,z3,z558,z12])],[(0,[z0,z1,z2,z3,z1125,z5]),(0,[z0,z1,z2,z3,z353,z1126]),(0,[z0,z1,z344,z3,z8,z119])],[(0,[z0,z1,z2,z3,z8,z1127]),(0,[z0,z139,z1,z30,z3,z8]),(0,[z0,z1,z2,z3,z43,z12])],[],[(0,[z0,z1,z16,z3,z4,z5]),(0,[z0,z1,z30,z3,z8,z451]),(0,[z222,z0,z136,z3,z8,z5]),(0,[z0,z1,z2,z3,z1128,z5])]],
   [[(0,[z0,z1129,z1,z2,z3,z5]),(0,[z0,z19,z1,z2,z3,z280]),(0,[z21,z0,z1,z371,z8,z5])],[(0,[z0,z1,z1130,z3,z8,z5]),(0,[z185,z1,z2,z488,z8,z5]),(0,[z0,z1,z2,z802,z3,z8])],[(0,[z0,z1,z2,z3,z36,z12]),(0,[z0,z1,z2,z646,z8,z186])],[(0,[z0,z1,z2,z3,z1131,z5]),(0,[z0,z1132,z1,z2,z3,z5]),(0,[z0,z99,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z467,z12]),(0,[z0,z1,z2,z3,z86,z5]),(0,[z0,z1,z874,z3,z8,z12])],[(0,[z0,z1,z2,z3,z1133,z5]),(0,[z0,z1,z2,z3,z8,z1134]),(0,[z0,z1,z2,z3,z1135,z5]),(0,[z0,z196,z1,z2,z40,z3])],[(0,[z143,z1,z16,z3,z55,z5]),(0,[z0,z1,z32,z97,z333,z5])],[(0,[z0,z1,z2,z230,z8,z145]),(0,[z0,z1,z2,z3,z1136,z5])],[(0,[z0,z1,z2,z1137,z8,z5]),(0,[z0,z1,z2,z1138,z3,z8])],[(0,[z53,z1,z2,z3,z80,z12])],[(0,[z0,z1,z1139,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1140]),(0,[z0,z99,z1,z2,z251,z186])],[(0,[z0,z1,z2,z230,z4,z5]),(0,[z0,z121,z1,z30,z3,z12]),(0,[z49,z0,z281,z2,z3,z20])],[(0,[z0,z1,z16,z3,z8,z216]),(0,[z0,z427,z1,z2,z3,z12]),(1,[z0,z1,z2,z713,z8])],[(0,[z141,z0,z121,z1,z30,z5]),(0,[z0,z1,z2,z3,z1141,z5]),(0,[z0,z1,z2,z3,z1142,z5]),(0,[z0,z1,z344,z3,z8,z5])],[(0,[z0,z7,z2,z3,z8,z145]),(0,[z1,z274,z30,z3,z8,z5]),(0,[z0,z421,z2,z40,z3,z8]),(0,[z610,z1,z2,z64,z8,z5]),(0,[z0,z709,z2,z3,z8,z5])],[(0,[z0,z1,z504,z3,z8,z377]),(0,[z0,z1,z335,z3,z8,z12]),(0,[z0,z1,z2,z1143,z3,z8])]],
   [[(0,[z0,z139,z1,z2,z3,z8]),(0,[z0,z6,z1,z30,z3,z8]),(0,[z0,z1144,z2,z3,z8,z5]),(0,[z0,z689,z1,z2,z3,z12]),(0,[z0,z1,z2,z3,z664,z12])],[(0,[z0,z1,z1145,z3,z8,z5]),(0,[z49,z0,z2,z3,z8,z968])],[(0,[z0,z1,z16,z3,z96,z12]),(0,[z0,z1146,z2,z3,z8,z5]),(0,[z116,z1,z2,z3,z8,z783]),(0,[z0,z70,z2,z107,z8,z271]),(0,[z18,z0,z2,z40,z3,z100]),(0,[z0,z1,z2,z3,z8,z27])],[(0,[z0,z1,z16,z3,z8,z123]),(0,[z0,z1,z47,z416,z8,z5]),(0,[z0,z1,z2,z40,z3,z407]),(0,[z0,z1,z2,z811,z3,z5])],[(0,[z0,z1,z2,z1147,z8,z5]),(0,[z306,z1,z2,z40,z3,z8]),(0,[z0,z1,z209,z3,z8,z12]),(0,[z0,z1,z2,z3,z43,z216])],[(0,[z0,z398,z1,z3,z227,z5]),(0,[z225,z1,z30,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z132]),(0,[z0,z406,z2,z3,z420,z5]),(0,[z0,z1,z2,z3,z1148,z5]),(0,[z0,z167,z2,z3,z773,z5])],[(0,[z0,z753,z1,z2,z8,z5]),(0,[z0,z1,z2,z3,z8,z1149]),(0,[z0,z1,z2,z3,z1150,z5]),(0,[z0,z1,z2,z40,z835,z8])],[(0,[z0,z1,z2,z3,z294,z12])],[(0,[z0,z1,z2,z3,z1151,z5]),(0,[z0,z1,z1152,z3,z8,z5]),(0,[z0,z1153,z2,z3,z8,z5]),(0,[z39,z0,z30,z8,z62,z5]),(0,[z0,z1,z2,z3,z235,z10]),(0,[z0,z1,z2,z3,z1154,z5]),(0,[z0,z1,z2,z3,z8,z1155]),(0,[z0,z753,z1,z2,z3,z5])],[(0,[z0,z1,z1156,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1157])],[(0,[z0,z1,z1158,z3,z8,z5])],[(0,[z0,z79,z30,z3,z8,z5]),(0,[z1,z16,z635,z3,z8,z5]),(0,[z0,z1,z246,z3,z8,z377]),(0,[z18,z0,z2,z3,z100,z216]),(0,[z0,z1,z2,z3,z171,z12])],[(0,[z1,z30,z40,z3,z58,z8]),(0,[z0,z1,z1159,z3,z8,z5]),(0,[z0,z1,z2,z3,z1160,z5]),(0,[z0,z1,z22,z8,z856,z5]),(0,[z106,z0,z1,z2,z40,z8]),(0,[z0,z1161,z2,z3,z8,z5])],[(0,[z610,z1,z2,z3,z8,z131]),(1,[z0,z1,z8,z856,z5]),(0,[z21,z0,z1,z204,z8,z5]),(0,[z0,z121,z1,z500,z3,z12])],[(0,[z0,z1,z2,z716,z8,z5]),(0,[z0,z1,z2,z3,z8,z1162]),(0,[z0,z121,z1,z2,z3,z12])],[(0,[z0,z228,z16,z3,z8,z5]),(0,[z0,z498,z1,z2,z3,z12]),(1,[z79,z2,z3,z80,z5]),(0,[z0,z1,z372,z3,z8,z12]),(0,[z0,z1,z2,z1163,z8,z5]),(0,[z18,z610,z1,z2,z3,z12])]],
   [[(0,[z77,z7,z2,z3,z8,z12]),(0,[z0,z1,z2,z40,z3,z312]),(0,[z53,z1,z2,z3,z788,z5]),(0,[z0,z1,z2,z3,z434,z12]),(0,[z0,z1,z1164,z3,z8,z5]),(0,[z0,z1165,z2,z3,z8,z5])],[(0,[z0,z1166,z30,z3,z8,z5]),(0,[z0,z1080,z16,z3,z8,z5]),(0,[z0,z1,z2,z148,z8,z271]),(0,[z1167,z1,z2,z3,z8,z5]),(0,[z0,z1,z3,z8,z92,z132]),(0,[z0,z380,z1,z3,z96,z5]),(0,[z0,z1,z663,z118,z8,z5]),(0,[z0,z1,z3,z8,z917,z12])],[(0,[z610,z1,z30,z3,z8,z5]),(0,[z0,z167,z1,z30,z3,z12]),(0,[z0,z1,z2,z356,z3,z12]),(0,[z49,z0,z1,z2,z3,z235]),(0,[z0,z1,z2,z3,z8,z1168]),(0,[z0,z1,z2,z3,z8,z98])],[(0,[z0,z6,z1,z2,z3,z8]),(0,[z481,z1,z30,z3,z8,z5]),(0,[z595,z1,z279,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z200])],[(0,[z0,z1169,z1,z2,z3,z5]),(0,[z290,z0,z228,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1170]),(0,[z0,z1,z2,z3,z205,z12])],[(0,[z0,z1,z2,z3,z8,z1171]),(0,[z0,z281,z1,z30,z3,z5]),(0,[z0,z1,z335,z3,z8,z216]),(0,[z106,z0,z1,z32,z8,z5])],[(0,[z0,z128,z30,z3,z8,z5]),(0,[z0,z1,z30,z130,z3,z8]),(0,[z0,z1,z30,z3,z134,z5]),(0,[z0,z1,z2,z395,z8,z12]),(0,[z0,z196,z1,z335,z3,z5]),(0,[z0,z1,z1172,z3,z8,z5])],[(0,[z0,z1,z326,z3,z353,z5]),(0,[z0,z1,z30,z40,z3,z8]),(0,[z0,z1,z1173,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1174]),(0,[z0,z383,z1,z3,z475,z5])],[(0,[z1175,z0,z1,z3,z8,z5]),(0,[z0,z1,z2,z3,z235,z5]),(0,[z0,z1,z2,z3,z629,z12]),(0,[z0,z1176,z1,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1177]),(0,[z0,z1,z22,z2,z43,z12]),(0,[z0,z1178,z2,z3,z8,z5]),(0,[z0,z28,z2,z3,z8,z355]),(0,[z0,z829,z2,z3,z8,z12])],[(0,[z77,z7,z2,z3,z4,z5]),(0,[z0,z1,z16,z3,z8,z1090]),(0,[z0,z1,z2,z148,z43,z12]),(0,[z0,z1,z2,z3,z8,z1179])],[(0,[z0,z421,z2,z3,z8,z5]),(0,[z670,z1,z30,z3,z8,z5]),(0,[z0,z26,z2,z58,z8,z5]),(0,[z0,z486,z1,z2,z3,z12]),(0,[z0,z167,z1,z2,z177,z5]),(0,[z0,z1,z2,z3,z1180,z5])],[(0,[z0,z1,z30,z3,z195,z5]),(0,[z0,z1,z2,z58,z166,z5]),(0,[z0,z117,z2,z3,z8,z38]),(0,[z0,z1,z2,z1181,z8,z5])],[(0,[z0,z1,z943,z3,z8,z12]),(0,[z0,z1,z415,z3,z8,z172])],[(0,[z0,z1,z30,z3,z8,z159]),(0,[z0,z1182,z1,z2,z3,z8]),(0,[z0,z1,z2,z333,z8,z12])],[(0,[z0,z26,z504,z3,z8,z5]),(0,[z0,z1,z2,z1183,z8,z5]),(0,[z0,z2,z8,z895,z62,z5]),(0,[z0,z1,z1184,z3,z8,z5]),(0,[z0,z1,z3,z8,z856,z5])]],
   [[(0,[z49,z0,z30,z3,z8,z20]),(0,[z106,z0,z1,z30,z8,z5]),(0,[z0,z1,z16,z234,z3,z8]),(0,[z0,z1,z1185,z3,z8,z5]),(0,[z0,z167,z2,z447,z3,z46])],[(0,[z306,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z64,z8,z5]),(0,[z0,z1,z1186,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1187]),(0,[z0,z1,z2,z352,z3,z12]),(0,[z1188,z0,z1,z2,z8,z5]),(0,[z0,z611,z1,z2,z3,z1189])],[(0,[z0,z1,z30,z184,z8,z5]),(0,[z0,z1,z2,z1190,z3,z8]),(0,[z0,z1,z2,z3,z1191,z5]),(0,[z0,z1192,z2,z3,z8,z5]),(0,[z0,z1,z1193,z3,z8,z5])],[(0,[z185,z1,z16,z148,z8,z5]),(0,[z0,z1,z346,z40,z3,z8])],[(0,[z0,z1,z2,z3,z8,z1126]),(0,[z0,z1,z30,z3,z8,z720]),(0,[z0,z196,z1,z30,z40,z3]),(0,[z0,z167,z1,z2,z3,z12]),(0,[z176,z437,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z1194,z5])],[(0,[z0,z1,z2,z1195,z3,z8]),(0,[z0,z1,z30,z197,z3,z8]),(0,[z0,z1,z1196,z3,z8,z5]),(0,[z0,z1,z296,z375,z3,z8])],[(0,[z0,z1,z30,z177,z8,z5]),(0,[z0,z1,z16,z3,z8,z122]),(0,[z0,z1,z1197,z3,z8,z5]),(0,[z0,z1,z2,z327,z8,z12]),(0,[z0,z1,z2,z3,z294,z132])],[(0,[z0,z1,z1198,z3,z8,z5])],[(0,[z0,z1,z1199,z3,z8,z5]),(0,[z0,z281,z1,z2,z3,z5]),(0,[z0,z1,z2,z1200,z8,z5]),(0,[z0,z1,z2,z3,z311,z12]),(0,[z0,z1,z2,z325,z8,z186])],[(0,[z0,z90,z2,z3,z353,z5]),(0,[z0,z1,z2,z40,z3,z4]),(0,[z1,z768,z2,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z1109])],[(0,[z0,z1,z78,z3,z8,z123]),(0,[z25,z1,z30,z58,z8,z5]),(0,[z0,z1,z17,z3,z8,z119]),(0,[z0,z26,z246,z3,z8,z5])],[(0,[z1201,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z1202,z5]),(0,[z18,z0,z1,z2,z3,z122]),(0,[z595,z437,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z1203,z5]),(0,[z0,z1,z2,z1107,z3,z8]),(0,[z1,z16,z768,z3,z8,z5]),(0,[z0,z1,z2,z1204,z8,z5]),(0,[z0,z117,z2,z3,z8,z12]),(1,[z0,z2,z3,z8,z968])],[(0,[z0,z1,z2,z3,z1205,z5]),(0,[z77,z7,z2,z3,z8,z123]),(0,[z0,z1,z1206,z3,z8,z5]),(0,[z0,z1,z2,z414,z3,z12])],[(0,[z0,z1,z1207,z3,z8,z5]),(0,[z0,z1,z16,z3,z8,z271]),(0,[z1,z449,z16,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z3,z1208,z5]),(0,[z0,z1,z115,z3,z405,z5]),(0,[z9,z1,z16,z3,z8,z38]),(0,[z0,z1,z2,z3,z8,z131]),(0,[z0,z28,z2,z3,z8,z152])],[(0,[z0,z406,z2,z3,z8,z5]),(0,[z0,z1,z1209,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1210]),(0,[z0,z662,z1,z3,z96,z5]),(0,[z0,z1,z2,z3,z166,z12]),(0,[z0,z1,z2,z3,z8,z1189]),(0,[z0,z228,z2,z3,z294,z5]),(0,[z0,z1,z2,z3,z8,z914]),(0,[z0,z196,z1,z2,z3,z451])],[(0,[z0,z1,z2,z3,z8,z1211]),(0,[z0,z1,z2,z58,z8,z278]),(0,[z0,z1212,z2,z3,z8,z5])],[(0,[z192,z77,z7,z2,z3,z5]),(0,[z0,z1,z291,z3,z8,z5]),(0,[z0,z1,z1213,z3,z8,z5]),(0,[z0,z1214,z2,z3,z8,z5]),(0,[z106,z0,z1,z2,z8,z5])],[(0,[z0,z1,z2,z230,z8,z12]),(0,[z0,z1,z2,z1215,z3,z8]),(0,[z0,z275,z1,z3,z8,z885])],[(0,[z0,z1,z30,z3,z8,z5]),(0,[z0,z1,z3,z8,z1216,z5])],[(0,[z29,z1,z768,z3,z8,z5]),(0,[z359,z1,z30,z3,z8,z5]),(0,[z0,z611,z1,z16,z3,z5]),(0,[z0,z1,z504,z3,z8,z278]),(0,[z0,z1,z1217,z3,z8,z5]),(0,[z53,z1,z2,z40,z3,z80]),(0,[z1,z2,z3,z8,z783,z10]),(0,[z0,z1218,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1219])],[(0,[z0,z1220,z1,z2,z3,z5]),(0,[z0,z1221,z1,z2,z3,z5]),(0,[z18,z0,z2,z3,z100,z12]),(0,[z0,z1,z2,z3,z1177,z12]),(0,[z176,z1,z3,z8,z96,z5]),(0,[z0,z1,z2,z44,z3,z134]),(0,[z0,z1222,z2,z40,z3,z8])],[(0,[z1,z30,z107,z58,z8,z5]),(0,[z0,z1,z30,z3,z8,z252]),(0,[z0,z1,z30,z3,z8,z750]),(0,[z0,z1,z16,z3,z43,z12]),(0,[z0,z1223,z1,z2,z3,z5]),(0,[z0,z1,z2,z505,z3,z12]),(0,[z0,z1,z1224,z3,z8,z5]),(0,[z0,z1,z1225,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1226]),(0,[z0,z1,z54,z394,z8,z5]),(0,[z0,z1,z2,z3,z8,z1227]),(0,[z0,z1,z2,z3,z8,z1228]),(0,[z0,z1,z1229,z3,z8,z5])],[(0,[z0,z1,z2,z394,z8,z59])],[(0,[z0,z1230,z2,z3,z8,z5]),(0,[z0,z1,z2,z1231,z8,z5]),(0,[z18,z306,z2,z3,z100,z5])],[(0,[z141,z0,z498,z1,z2,z5]),(0,[z0,z1,z2,z3,z8,z1232]),(0,[z0,z1,z2,z3,z96,z122]),(0,[z0,z1,z2,z454,z3,z12])],[(0,[z0,z1004,z1,z641,z2,z3]),(0,[z0,z1,z2,z3,z931,z5]),(1,[z0,z1,z2,z333,z12]),(0,[z0,z1,z500,z3,z97,z5])],[(0,[z0,z1,z2,z40,z230,z8]),(0,[z0,z1,z2,z327,z8,z216]),(0,[z0,z427,z1,z2,z3,z280])],[(0,[z0,z1,z2,z3,z1233,z5]),(0,[z0,z1,z16,z3,z86,z5]),(0,[z0,z1,z552,z40,z3,z8]),(0,[z1234,z1,z2,z3,z8,z5])]],
   [[(0,[z0,z1,z1235,z3,z8,z5]),(0,[z0,z1,z16,z3,z1133,z5]),(0,[z0,z1,z2,z3,z8,z1236])],[(0,[z0,z618,z2,z3,z8,z152]),(0,[z0,z1,z346,z3,z8,z5]),(0,[z0,z1,z1237,z3,z8,z5]),(0,[z0,z1,z2,z3,z1238,z5]),(0,[z39,z0,z8,z63,z62,z5]),(0,[z0,z1,z2,z3,z8,z1239]),(0,[z0,z1,z2,z3,z374,z12])],[(0,[z0,z1,z16,z3,z1136,z5]),(0,[z0,z1,z246,z3,z8,z278]),(0,[z412,z1,z2,z58,z8,z5]),(0,[z185,z1,z491,z148,z8,z5]),(0,[z0,z1,z2,z447,z3,z8])],[(0,[z185,z1,z2,z797,z8,z5]),(0,[z210,z1,z2,z3,z8,z10]),(0,[z0,z1240,z1,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1241])],[],[(0,[z0,z1,z1242,z2,z3,z5]),(0,[z0,z1243,z1,z2,z3,z8]),(0,[z0,z1,z2,z3,z338,z12]),(0,[z0,z275,z1,z3,z8,z92])],[(0,[z0,z1,z30,z40,z3,z12]),(0,[z0,z1244,z2,z3,z8,z5]),(0,[z0,z1,z491,z3,z8,z12]),(0,[z0,z1,z67,z3,z8,z451])],[(0,[z0,z1,z2,z3,z8,z1245]),(0,[z1246,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z1247,z5]),(0,[z0,z611,z1,z2,z40,z3]),(0,[z0,z1,z2,z40,z811,z3])],[(0,[z0,z1248,z1,z30,z3,z8]),(0,[z0,z1,z54,z3,z8,z59]),(0,[z306,z1,z209,z3,z8,z5]),(0,[z0,z1,z209,z64,z8,z5])],[(0,[z0,z1,z279,z40,z3,z8]),(0,[z143,z1,z2,z40,z3,z55])],[(0,[z0,z1,z2,z1249,z8,z5]),(0,[z1,z2,z3,z80,z51,z12]),(0,[z0,z1,z2,z3,z131,z12])],[(0,[z0,z1,z504,z3,z8,z12]),(0,[z0,z1,z372,z3,z235,z5]),(0,[z0,z1,z2,z1250,z3,z8])],[(0,[z0,z1,z2,z3,z1251,z5]),(1,[z306,z1,z2,z3,z12]),(0,[z0,z1,z32,z3,z97,z12])],[(0,[z270,z0,z1,z8,z321,z5]),(0,[z0,z1,z16,z3,z8,z27]),(0,[z1252,z1,z2,z3,z8,z5])],[(0,[z0,z1,z2,z953,z8,z5]),(0,[z0,z1,z1253,z3,z8,z5]),(0,[z0,z1,z2,z170,z43,z12])],[(0,[z0,z1,z2,z3,z1254,z5]),(0,[z0,z1,z2,z3,z8,z1255]),(0,[z0,z1,z30,z3,z784,z5]),(0,[z0,z1,z2,z3,z964,z5]),(0,[z0,z1,z2,z979,z3,z420]),(0,[z116,z1,z2,z3,z235,z10]),(1,[z0,z2,z8,z895,z5]),(0,[z0,z121,z1,z67,z3,z12])]],
   [[(0,[z0,z1,z2,z3,z8,z916]),(0,[z0,z1,z3,z8,z517,z12])],[(0,[z0,z1,z326,z3,z8,z5]),(0,[z53,z1,z30,z3,z80,z5])],[(0,[z0,z1,z2,z230,z8,z123]),(0,[z392,z0,z507,z3,z8,z5]),(0,[z0,z1,z2,z3,z367,z12]),(0,[z0,z2,z3,z8,z773,z5])],[(0,[z0,z1256,z1,z2,z3,z8]),(0,[z0,z70,z30,z107,z8,z5]),(0,[z0,z1,z2,z1257,z3,z8]),(0,[z0,z1,z2,z395,z235,z5]),(0,[z0,z1,z2,z3,z333,z12])],[(0,[z0,z1,z1258,z3,z8,z5]),(0,[z0,z1222,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1259]),(0,[z21,z0,z1,z3,z195,z5]),(0,[z220,z0,z2,z3,z8,z229]),(0,[z0,z196,z1,z2,z811,z3])],[(0,[z0,z196,z1,z2,z64,z5])],[(0,[z0,z90,z167,z2,z3,z12])],[(0,[z0,z406,z2,z40,z3,z8]),(0,[z0,z1,z246,z3,z8,z12]),(0,[z0,z1,z209,z3,z8,z131]),(0,[z1260,z1,z2,z3,z8,z5])],[(0,[z0,z1261,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z528,z12]),(0,[z141,z0,z121,z1,z67,z5])],[(0,[z0,z1,z291,z40,z3,z8]),(0,[z0,z1262,z1,z2,z3,z5]),(1,[z0,z1,z3,z8,z885]),(0,[z0,z753,z1,z2,z43,z5]),(0,[z0,z1,z2,z375,z3,z12])],[(0,[z290,z0,z1,z3,z8,z12])],[(0,[z0,z1,z2,z1263,z8,z5]),(0,[z0,z19,z30,z3,z8,z152]),(0,[z0,z1248,z1,z2,z3,z8]),(0,[z0,z1,z2,z107,z43,z12]),(0,[z0,z1,z2,z1264,z8,z5]),(0,[z0,z1,z1265,z3,z8,z5])],[(0,[z0,z1,z2,z3,z353,z5]),(0,[z0,z1,z336,z40,z3,z8]),(0,[z0,z1,z552,z3,z8,z5]),(0,[z0,z1063,z2,z3,z8,z5]),(0,[z0,z1,z845,z3,z8,z5]),(0,[z0,z1266,z2,z3,z8,z5])],[(0,[z0,z1,z16,z3,z8,z98]),(0,[z185,z1,z504,z3,z8,z5]),(0,[z0,z1,z2,z1267,z3,z8]),(0,[z0,z1,z2,z3,z8,z1268]),(0,[z0,z1,z22,z118,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1269]),(0,[z452,z1,z30,z3,z8,z5]),(0,[z0,z26,z2,z3,z8,z278]),(0,[z0,z1,z136,z3,z96,z12]),(0,[z0,z1,z2,z1270,z3,z8])],[(0,[z0,z1,z30,z3,z294,z5]),(0,[z1271,z1,z2,z3,z8,z5]),(0,[z0,z121,z1,z2,z43,z12])]],
   [[(0,[z0,z1,z2,z394,z8,z5]),(0,[z0,z1,z54,z177,z8,z5]),(0,[z18,z0,z1,z2,z327,z12]),(0,[z0,z1,z2,z3,z8,z426]),(0,[z0,z1,z500,z8,z43,z5])],[(0,[z1089,z0,z1,z2,z8,z5]),(0,[z0,z1,z2,z3,z1272,z5]),(0,[z0,z1,z1273,z3,z8,z5]),(0,[z176,z1,z2,z40,z3,z8]),(0,[z0,z1,z1030,z3,z8,z12])],[(0,[z0,z437,z2,z40,z3,z8]),(0,[z1274,z0,z1,z2,z8,z5])],[(0,[z0,z1,z2,z148,z312,z5]),(0,[z0,z1,z2,z1275,z3,z8]),(0,[z141,z0,z121,z1,z2,z12]),(0,[z0,z1,z2,z34,z3,z12])],[(0,[z0,z1,z16,z3,z235,z5]),(0,[z21,z0,z1,z8,z288,z5])],[(1,[z7,z2,z3,z353,z5]),(0,[z1,z30,z58,z8,z43,z5]),(0,[z0,z1,z2,z3,z8,z1276]),(0,[z0,z1,z2,z3,z1277,z5]),(0,[z1278,z1,z2,z3,z8,z5]),(0,[z0,z2,z3,z8,z968,z5]),(0,[z0,z1,z2,z1279,z3,z8])],[(0,[z0,z1,z2,z3,z4,z12]),(0,[z0,z1,z279,z3,z8,z5]),(0,[z0,z1280,z2,z3,z8,z5]),(0,[z0,z421,z16,z3,z8,z5]),(0,[z562,z1,z16,z3,z8,z5]),(0,[z0,z19,z1,z2,z3,z235])],[(0,[z0,z689,z2,z3,z46,z5]),(0,[z0,z1281,z1,z2,z3,z5]),(0,[z0,z1,z2,z1282,z8,z5]),(0,[z0,z167,z1,z2,z3,z122])],[(0,[z0,z1,z30,z3,z8,z377]),(0,[z0,z1,z2,z40,z3,z101])],[(0,[z0,z1,z30,z821,z8,z5]),(0,[z0,z1,z2,z3,z8,z1283]),(0,[z18,z0,z1,z2,z3,z1177])],[(0,[z0,z1,z2,z3,z1284,z5]),(0,[z25,z406,z2,z58,z8,z5]),(0,[z143,z1,z2,z3,z55,z289]),(0,[z0,z1,z2,z1285,z8,z5]),(0,[z0,z1,z2,z713,z8,z186])],[(0,[z116,z1,z30,z3,z8,z10]),(0,[z0,z1,z2,z584,z3,z12]),(0,[z0,z1,z1286,z3,z8,z5]),(0,[z0,z1,z344,z3,z906,z5]),(0,[z0,z973,z2,z3,z8,z5])],[(0,[z0,z1,z2,z3,z4,z1031]),(0,[z0,z1,z2,z3,z4,z145]),(0,[z0,z1,z1287,z3,z8,z5]),(0,[z306,z1,z16,z3,z8,z5]),(0,[z0,z1,z16,z64,z8,z5]),(0,[z0,z1,z1288,z3,z8,z5]),(1,[z0,z1,z3,z708,z5])],[(0,[z0,z1,z2,z1289,z8,z5]),(0,[z0,z1,z2,z124,z8,z5]),(0,[z143,z1,z2,z3,z55,z12]),(0,[z0,z1,z2,z3,z97,z12]),(0,[z0,z1,z2,z40,z3,z430])],[(0,[z0,z1,z54,z3,z8,z5]),(0,[z112,z0,z1,z2,z3,z12])],[(0,[z0,z1,z1290,z3,z8,z5]),(0,[z0,z1,z30,z395,z8,z5]),(0,[z25,z1,z2,z58,z312,z5]),(0,[z0,z306,z2,z3,z100,z5]),(0,[z0,z1,z2,z3,z294,z27]),(0,[z21,z0,z1,z8,z87,z12]),(0,[z0,z1,z1291,z3,z8,z5]),(0,[z0,z1,z67,z40,z3,z8]),(0,[z0,z1,z500,z3,z8,z12])]],
   [[],[(0,[z0,z1,z1292,z3,z8,z5]),(0,[z0,z1,z2,z37,z713,z8])],[(0,[z0,z1,z30,z3,z8,z830]),(0,[z0,z1,z2,z3,z420,z762]),(0,[z0,z1,z2,z701,z8,z186]),(0,[z0,z1,z2,z3,z282,z12])],[(0,[z0,z1,z2,z3,z69,z12]),(0,[z0,z26,z2,z3,z8,z12]),(0,[z0,z1,z2,z3,z55,z12]),(0,[z0,z1,z2,z232,z3,z12]),(0,[z0,z212,z2,z107,z8,z5]),(0,[z0,z1,z2,z234,z170,z43])],[(0,[z748,z7,z2,z3,z8,z5]),(0,[z192,z0,z139,z1,z2,z3]),(0,[z0,z1,z2,z3,z1293,z5]),(0,[z0,z1,z2,z3,z1294,z5]),(0,[z306,z1,z2,z3,z43,z5]),(0,[z0,z1,z2,z1295,z3,z8]),(0,[z0,z1,z1055,z3,z8,z12])],[(0,[z0,z1,z22,z416,z8,z5]),(0,[z0,z421,z2,z3,z467,z5]),(0,[z0,z1,z3,z294,z96,z5]),(0,[z0,z65,z1,z3,z96,z12]),(0,[z0,z1,z2,z40,z3,z628])],[(0,[z0,z1,z30,z333,z8,z5]),(0,[z599,z0,z121,z1,z2,z5]),(0,[z0,z1,z2,z3,z8,z1296]),(0,[z0,z1297,z2,z3,z8,z5]),(0,[z0,z1,z2,z1298,z3,z8])],[(0,[z0,z1,z326,z40,z3,z8]),(0,[z116,z1,z346,z3,z8,z10]),(0,[z0,z167,z2,z3,z229,z5])],[(0,[z192,z0,z1,z16,z3,z5]),(0,[z116,z1,z2,z463,z3,z8]),(0,[z0,z1299,z2,z40,z3,z8])],[(0,[z0,z1,z336,z3,z8,z5]),(0,[z0,z1,z2,z3,z312,z5]),(0,[z0,z79,z2,z394,z8,z5]),(0,[z0,z1,z2,z40,z3,z74]),(0,[z0,z887,z2,z3,z8,z5])],[(0,[z0,z1,z2,z327,z8,z131]),(0,[z0,z1,z2,z941,z3,z294])],[(0,[z0,z1,z16,z3,z8,z131]),(0,[z0,z1,z32,z3,z524,z5]),(0,[z0,z1,z2,z3,z166,z271]),(0,[z0,z1,z2,z3,z8,z1300]),(0,[z306,z1,z872,z3,z8,z5]),(0,[z18,z0,z2,z64,z100,z5])],[(0,[z0,z406,z16,z3,z8,z5]),(0,[z0,z1,z2,z304,z3,z12]),(0,[z0,z1,z534,z3,z8,z12]),(0,[z0,z1,z2,z1301,z8,z5])],[(0,[z0,z1,z1302,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1303]),(0,[z0,z1,z2,z3,z96,z426])],[(0,[z0,z1,z1304,z3,z8,z5]),(0,[z0,z1,z1305,z3,z8,z5]),(0,[z176,z1,z2,z3,z8,z5]),(0,[z0,z1,z636,z3,z97,z5])],[(0,[z0,z1,z30,z327,z8,z5]),(0,[z1306,z0,z1,z2,z3,z5]),(0,[z0,z437,z2,z3,z8,z5]),(0,[z0,z1,z1307,z3,z8,z5])]],
   [[(0,[z0,z1,z2,z3,z8,z1308]),(0,[z192,z1,z2,z3,z80,z5]),(0,[z0,z1088,z1,z641,z2,z3]),(0,[z0,z1,z2,z1309,z8,z5]),(0,[z0,z1,z768,z3,z8,z5]),(0,[z0,z1,z2,z1310,z3,z8]),(0,[z0,z1,z2,z177,z80,z5]),(0,[z226,z1,z2,z3,z55,z5]),(0,[z0,z1,z2,z349,z3,z12])],[(0,[z0,z1,z2,z1311,z8,z5]),(0,[z0,z121,z1,z2,z3,z916])],[(0,[z0,z1,z326,z184,z8,z5]),(0,[z0,z1,z158,z3,z8,z12]),(0,[z0,z1,z2,z335,z3,z12]),(0,[z0,z1,z2,z40,z3,z134])],[(0,[z0,z1,z2,z3,z1312,z5]),(0,[z1,z2,z797,z58,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1313]),(0,[z0,z1,z2,z3,z8,z1314]),(0,[z1,z30,z3,z8,z321,z5]),(0,[z0,z1,z3,z8,z1315,z5]),(0,[z0,z263,z1,z3,z8,z113])],[(0,[z595,z1,z2,z3,z8,z5]),(0,[z0,z1,z2,z3,z1316,z5]),(0,[z0,z128,z2,z394,z8,z5]),(0,[z21,z0,z1,z368,z8,z5])],[(0,[z319,z0,z1,z8,z87,z5]),(0,[z306,z1,z335,z3,z8,z5]),(0,[z0,z1,z335,z64,z8,z5]),(0,[z0,z228,z2,z3,z8,z12]),(0,[z0,z65,z1,z3,z708,z5]),(0,[z106,z0,z1,z2,z43,z5]),(0,[z0,z121,z1,z2,z3,z98])],[(0,[z0,z398,z1,z3,z96,z5]),(0,[z0,z79,z54,z3,z8,z5]),(0,[z0,z1,z1317,z3,z8,z5])],[(0,[z0,z1318,z1,z2,z3,z8]),(0,[z0,z79,z2,z3,z8,z59]),(0,[z53,z306,z1,z2,z3,z5])],[(0,[z0,z1,z2,z3,z1319,z5]),(0,[z192,z0,z1,z2,z40,z3]),(0,[z319,z0,z1,z8,z241,z5]),(0,[z0,z1,z2,z1320,z8,z5]),(0,[z1321,z0,z1,z3,z8,z5]),(0,[z542,z1,z2,z3,z80,z5]),(0,[z0,z1,z1322,z3,z8,z5]),(0,[z0,z1,z2,z3,z8,z1323]),(0,[z11,z0,z136,z3,z8,z12]),(0,[z306,z1,z2,z3,z5,z12]),(0,[z0,z1,z2,z64,z5,z12])],[(0,[z1,z606,z30,z3,z8,z5]),(0,[z0,z1,z165,z3,z8,z12]),(0,[z18,z0,z2,z3,z100,z131]),(0,[z0,z1,z2,z3,z8,z66])],[(0,[z0,z1,z2,z3,z8,z1324]),(0,[z0,z1,z2,z1037,z8,z5]),(0,[z0,z665,z1,z2,z3,z12])],[(0,[z0,z1,z78,z3,z353,z5]),(0,[z0,z1,z30,z230,z8,z5]),(0,[z0,z1,z2,z1113,z3,z8]),(0,[z0,z1,z2,z3,z8,z1121]),(0,[z0,z1,z2,z3,z1039,z5]),(0,[z0,z1,z3,z8,z1325,z5]),(0,[z0,z167,z2,z3,z46,z5]),(0,[z0,z1326,z2,z3,z8,z5]),(0,[z0,z1,z67,z3,z8,z5])],[(0,[z0,z1,z2,z184,z353,z5]),(0,[z192,z0,z1,z1051,z3,z5]),(0,[z192,z0,z6,z1,z2,z3]),(0,[z0,z109,z568,z3,z8,z5]),(0,[z0,z1,z30,z462,z3,z8]),(0,[z0,z1,z16,z447,z3,z8]),(0,[z474,z0,z1,z2,z14,z8])],[(0,[z1,z30,z299,z3,z8,z5]),(0,[z0,z1,z2,z1327,z3,z8]),(0,[z0,z1,z3,z8,z1328,z5]),(0,[z290,z0,z1,z8,z43,z5]),(0,[z0,z1,z2,z3,z8,z1329]),(0,[z0,z1,z2,z44,z526,z8])],[(0,[z0,z1,z30,z3,z467,z5]),(0,[z18,z0,z30,z3,z100,z5]),(0,[z0,z1330,z2,z3,z8,z5]),(0,[z35,z1,z16,z3,z8,z12]),(0,[z0,z1,z2,z3,z8,z1331]),(0,[z0,z1,z2,z3,z502,z12]),(0,[z0,z1,z2,z40,z394,z8]),(0,[z0,z1,z1332,z3,z8,z5]),(0,[z21,z0,z1,z8,z87,z132])]],
   [[(0,[z0,z1,z2,z1333,z8,z5]),(0,[z0,z1,z30,z875,z8,z5]),(0,[z0,z421,z372,z3,z8,z5]),(0,[z0,z1,z2,z323,z3,z12]),(0,[z21,z595,z1,z8,z87,z5])],[(0,[z192,z0,z1,z2,z3,z1269]),(0,[z0,z1,z2,z58,z8,z271]),(0,[z0,z1,z3,z8,z1334,z5]),(0,[z0,z1,z2,z3,z80,z252]),(0,[z0,z1,z2,z1335,z3,z8])],[(0,[z0,z1,z30,z3,z227,z12]),(0,[z0,z1,z2,z125,z43,z5]),(0,[z0,z1,z2,z1336,z3,z8]),(0,[z0,z1,z2,z3,z8,z451])],[(0,[z0,z1,z2,z3,z8,z1337]),(0,[z0,z128,z54,z3,z8,z5]),(0,[z1338,z0,z1,z2,z8,z5]),(0,[z0,z1,z2,z1339,z3,z8])],[(0,[z0,z90,z2,z184,z8,z5]),(0,[z0,z1,z2,z1340,z8,z5]),(0,[z18,z0,z79,z2,z3,z5]),(0,[z0,z128,z2,z3,z8,z59]),(0,[z0,z1,z54,z40,z3,z8]),(0,[z116,z421,z2,z3,z8,z10]),(0,[z1341,z1,z2,z3,z8,z5]),(0,[z21,z0,z1,z8,z87,z27])],[(0,[z0,z1299,z2,z3,z8,z5]),(0,[z0,z1,z2,z40,z3,z467]),(0,[z306,z121,z1,z2,z3,z5]),(0,[z0,z1,z335,z3,z8,z131]),(0,[z0,z1,z1342,z3,z8,z5]),(0,[z141,z0,z1,z500,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1343]),(0,[z1344,z0,z1,z3,z8,z5]),(0,[z0,z1,z2,z333,z8,z98]),(0,[z0,z1,z2,z3,z430,z12]),(0,[z0,z1,z2,z3,z8,z111])],[(0,[z286,z7,z2,z3,z8,z5]),(0,[z0,z1,z2,z811,z3,z8])],[(0,[z0,z421,z2,z395,z8,z5]),(0,[z0,z2,z3,z8,z895,z5]),(0,[z610,z1,z2,z40,z3,z8]),(0,[z0,z19,z2,z3,z8,z968]),(0,[z0,z1,z3,z8,z735,z5])],[(0,[z1345,z0,z1,z3,z8,z5]),(0,[z0,z1,z1346,z3,z8,z5]),(0,[z0,z167,z2,z40,z3,z46]),(0,[z0,z1,z2,z325,z43,z12]),(0,[z0,z121,z1,z2,z305,z5])],[(0,[z0,z1,z2,z58,z43,z12]),(0,[z143,z1,z2,z197,z3,z55]),(0,[z587,z0,z2,z3,z8,z20]),(0,[z0,z1,z2,z3,z8,z1347]),(0,[z0,z1348,z1,z2,z3,z8]),(0,[z0,z1,z344,z251,z8,z186])],[(0,[z1349,z0,z1,z3,z8,z5]),(0,[z185,z1,z2,z148,z8,z12]),(0,[z0,z1,z346,z3,z467,z5]),(0,[z0,z1,z2,z3,z527,z12]),(0,[z0,z1,z2,z1023,z8,z12])],[(0,[z0,z1,z30,z998,z3,z5]),(0,[z0,z1,z2,z3,z769,z5])],[(0,[z0,z1,z2,z3,z8,z1350]),(0,[z0,z1,z2,z40,z124,z8]),(0,[z0,z1,z810,z3,z8,z5])],[(0,[z0,z1,z1351,z3,z8,z5]),(0,[z0,z1352,z2,z3,z8,z5]),(0,[z0,z1,z22,z219,z8,z5])],[(0,[z0,z70,z2,z503,z8,z5]),(0,[z0,z1353,z2,z3,z8,z5]),(0,[z0,z1,z2,z124,z8,z10]),(0,[z0,z1,z1354,z3,z8,z5])]],
   [[(0,[z1,z30,z58,z8,z5,z186]),(0,[z21,z0,z1,z8,z321,z5]),(0,[z176,z1,z32,z3,z8,z5]),(0,[z106,z0,z1,z2,z294,z5])],[(0,[z0,z1,z1355,z3,z8,z5]),(1,[z0,z1,z2,z811,z3])],[(0,[z0,z1,z641,z2,z3,z12]),(0,[z0,z1,z1356,z3,z8,z5]),(0,[z25,z1,z2,z58,z420,z5]),(0,[z0,z28,z167,z2,z3,z12]),(0,[z0,z1,z2,z463,z3,z12])],[(0,[z1357,z1,z2,z3,z8,z5])],[(0,[z15,z1,z2,z3,z353,z5]),(0,[z1,z16,z30,z3,z8,z12]),(0,[z0,z1,z2,z177,z8,z59]),(0,[z9,z1,z2,z3,z8,z51]),(0,[z0,z65,z1,z40,z3,z96]),(0,[z0,z1,z82,z3,z8,z885])],[(0,[z0,z1,z2,z3,z1358,z5]),(0,[z141,z0,z121,z1,z2,z122])],[(0,[z0,z1,z30,z170,z43,z5]),(0,[z0,z1,z2,z394,z8,z252]),(0,[z0,z228,z2,z3,z8,z132]),(0,[z443,z0,z1,z2,z3,z12]),(0,[z106,z0,z1,z32,z97,z5])],[(0,[z0,z1,z16,z3,z353,z5]),(0,[z0,z406,z2,z3,z8,z377]),(0,[z0,z79,z2,z3,z80,z5]),(0,[z0,z2,z3,z8,z965,z5]),(0,[z0,z1,z2,z3,z8,z1359])],[(0,[z143,z79,z2,z3,z8,z5]),(0,[z306,z1,z949,z3,z8,z5]),(0,[z0,z1,z2,z3,z43,z98]),(0,[z0,z1,z2,z3,z92,z195])],[(0,[z0,z1,z1360,z3,z8,z5]),(0,[z0,z1,z30,z3,z405,z12]),(0,[z0,z1,z2,z3,z621,z12]),(0,[z0,z1,z2,z3,z8,z1361]),(0,[z0,z437,z2,z3,z294,z5])],[(0,[z610,z1,z725,z3,z8,z5])],[(0,[z77,z7,z30,z3,z8,z5]),(0,[z0,z1,z16,z394,z8,z5]),(0,[z0,z1,z16,z3,z8,z426]),(0,[z267,z1,z2,z148,z8,z5]),(0,[z0,z1,z2,z3,z8,z1362]),(0,[z39,z0,z2,z8,z62,z5]),(0,[z0,z1363,z1,z3,z8,z5]),(0,[z0,z1,z2,z3,z1364,z5]),(0,[z595,z1,z2,z40,z3,z8])],[(0,[z0,z1,z2,z3,z420,z5]),(0,[z0,z1,z2,z3,z312,z377]),(0,[z0,z117,z2,z3,z235,z5])],[(0,[z29,z1,z30,z3,z8,z12]),(0,[z0,z1,z30,z3,z80,z12]),(0,[z0,z1,z2,z3,z8,z1365]),(0,[z0,z1,z2,z450,z8,z186]),(0,[z221,z0,z1,z2,z8,z255])],[(0,[z0,z1,z16,z34,z3,z12]),(0,[z237,z1,z2,z148,z8,z5]),(0,[z306,z1,z2,z327,z8,z5]),(0,[z0,z1,z2,z3,z195,z119])],[(0,[z0,z1,z2,z3,z8,z1366]),(0,[z585,z1,z2,z148,z8,z5]),(0,[z0,z1,z1367,z2,z3,z5]),(0,[z0,z1,z740,z3,z8,z5]),(0,[z21,z0,z1,z86,z87,z5]),(0,[z0,z1,z2,z3,z97,z122])]],
   [[(0,[z0,z1,z16,z3,z8,z1276]),(0,[z0,z1,z3,z8,z63,z12]),(0,[z18,z306,z1,z2,z3,z12])],[(0,[z1,z57,z16,z3,z8,z5]),(0,[z1368,z0,z1,z3,z8,z5]),(0,[z0,z1,z500,z3,z8,z122])],[(0,[z0,z139,z1,z641,z2,z3]),(0,[z0,z1,z2,z3,z8,z59]),(0,[z0,z1,z2,z3,z280,z10]),(0,[z0,z1,z82,z3,z430,z119])],[(0,[z0,z1,z2,z3,z8,z1369]),(0,[z0,z1370,z1,z2,z3,z8]),(0,[z1371,z1,z2,z3,z8,z5])],[(0,[z0,z1166,z2,z3,z8,z5]),(0,[z75,z1,z16,z3,z8,z5]),(0,[z0,z1,z54,z3,z8,z252]),(0,[z0,z1,z2,z3,z8,z1372])],[(0,[z610,z1,z2,z3,z8,z5]),(0,[z0,z99,z1,z2,z3,z12])],[(0,[z0,z611,z1,z30,z3,z5]),(0,[z0,z303,z2,z3,z8,z152])],[(0,[z0,z1,z2,z3,z1373,z5]),(0,[z1,z30,z3,z8,z543,z5]),(0,[z319,z1,z2,z58,z8,z5]),(0,[z0,z1,z1374,z3,z8,z5]),(0,[z176,z1,z3,z8,z87,z5])],[(0,[z0,z1,z2,z3,z1375,z5]),(0,[z0,z1,z16,z124,z8,z5]),(0,[z0,z1,z536,z3,z8,z637]),(0,[z0,z1,z16,z3,z97,z12]),(0,[z0,z167,z2,z3,z46,z159]),(0,[z0,z196,z1,z67,z3,z5])],[(0,[z0,z1,z2,z852,z3,z55]),(0,[z306,z1,z2,z3,z46,z5])],[(0,[z0,z7,z2,z3,z353,z5]),(0,[z0,z1,z30,z3,z8,z145]),(0,[z0,z1,z1376,z3,z8,z5]),(0,[z192,z0,z79,z2,z3,z5]),(0,[z0,z1,z30,z3,z8,z948]),(0,[z1,z30,z3,z549,z8,z5]),(0,[z700,z1,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z80,z159]),(0,[z0,z1,z2,z3,z8,z1377]),(0,[z0,z228,z2,z8,z43,z5]),(0,[z0,z1,z2,z3,z134,z5])],[(0,[z0,z1,z2,z40,z3,z8]),(0,[z7,z2,z3,z8,z353,z5]),(0,[z397,z1,z2,z3,z8,z38]),(0,[z0,z1,z2,z3,z8,z1378]),(0,[z21,z0,z1,z8,z856,z5]),(0,[z0,z1,z344,z3,z1022,z5])],[(0,[z1,z7,z2,z3,z80,z12]),(0,[z192,z0,z1,z2,z878,z5]),(0,[z0,z1,z2,z3,z1379,z5]),(0,[z0,z1,z2,z1380,z8,z5]),(0,[z1,z279,z30,z3,z8,z5]),(0,[z0,z1,z2,z3,z655,z12]),(0,[z0,z1,z1381,z3,z8,z5])],[(0,[z0,z1,z2,z3,z8,z1382]),(0,[z0,z1383,z1,z2,z3,z8]),(0,[z0,z611,z70,z2,z107,z5])],[(0,[z0,z1,z2,z1384,z8,z5]),(0,[z0,z1,z16,z3,z55,z12]),(0,[z0,z1,z16,z3,z69,z12]),(0,[z0,z1,z346,z395,z8,z5]),(0,[z0,z1,z2,z1385,z8,z5])],[(0,[z53,z1,z2,z394,z80,z5]),(0,[z612,z1,z2,z3,z55,z5]),(0,[z0,z1,z2,z3,z195,z5]),(0,[z0,z1,z344,z3,z8,z12])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 482) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 482).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 971).take 489) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1460).take 15) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1475)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [482, 489, 489, 15] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 122).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 122).take 109).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 231).take 105).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 336).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc4 : chunkOK 5 ((bkB.flatten.drop 448).take 64).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [122, 109, 105, 112, 64] = true :=
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

end PEqualNP.Outside.L_meta_36346

theorem PEqualNP.Outside.L_meta_36346 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277075690 * 2 ^ 32 + 4277074088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277075690 * 2 ^ 32 + 4277074088) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36346.solve