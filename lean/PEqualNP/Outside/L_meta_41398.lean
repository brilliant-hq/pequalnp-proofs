import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41398

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4276142080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x002986158c3c3e2a#64 ++ 0x0000a6185630f0f8#64 ++ 0x04fb8e3f8c7c7e3d#64 ++ 0x9813ee38fe31f1f8#64 : BitVec 256),
   (0x0960b2cc0d8d86cc#64 ++ 0x082582cb3036361b#64 ++ 0x1b64f3cc0f8f8ffb#64 ++ 0xfc6d93cf303e3e3f#64 : BitVec 256),
   (0x62870370b006db70#64 ++ 0x218a1c0dc2c01b6d#64 ++ 0xe38703f0f00ffff7#64 ++ 0xaf8e1c0fc3c03fff#64 : BitVec 256),
   (0xb407dc00d6d00d80#64 ++ 0x16d01f70035b4036#64 ++ 0xfc07fc00fff00fef#64 ++ 0xf7f01ff003ffc03f#64 : BitVec 256),
   (0xdff800006b6b6000#64 ++ 0x477fe00001adad80#64 ++ 0xfff80000fffff01f#64 ++ 0xc7ffe00003ffffc0#64 : BitVec 256),
   (0xffd669aa00000000#64 ++ 0x03ff59a6a8000000#64 ++ 0xffffffff0000003f#64 ++ 0x7bfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [7, 6]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [11, 13]⟩, ⟨.or, [14, 8]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04fb8e3f8c7c7e3d 0x9813ee38fe31f1f8

def z1 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38703f0f00ffff7 0xaf8e1c0fc3c03fff

def z2 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc07fc00fff00fef 0xf7f01ff003ffc03f

def z3 : W := mkw 0xd698000062626000 0x475a600001898980 0xe4980000f0707004 0x0392600003c1c1c0

def z4 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfff80000fffff01f 0xc7ffe00003ffffc0

def z5 : W := mkw 0xdff8b2cc6fefe6cc 0x4f7fe2cb31bfbf9b 0xfffcf3ccffffffff 0xfffff3cf33ffffff

def z6 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xffffffff0000003f 0x7bfffffffc000000

def z7 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b64f3cc0f8f8ffb 0xfc6d93cf303e3e3f

def z8 : W := mkw 0x202f87759c3cbf7a 0x2080be1dd670f2fd 0x04ff8fff8c7c7ffd 0xb813fe3ffe31f1ff

def z9 : W := mkw 0x002800006b6b6000 0x4400a00001adad80 0x00000000fffff000 0x8400000003ffffc0

def z10 : W := mkw 0x0940208800000000 0x0025008220000000 0x1fffffff0000003f 0x787ffffffc000000

def z11 : W := mkw 0x0969b6dd8dbdbeee 0x0825a6db7636f6fb 0x1fffffff8fffffff 0xfc7ffffffe3fffff

def z12 : W := mkw 0xdfd030c863c3c0c4 0x4f7f40c3218f0f03 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z13 : W := mkw 0xdff99400fffb6d80 0x577fe65003ffedb6 0xfff80000ffffffdf 0xc7ffe00003ffffff

def z14 : W := mkw 0xffd669aa63434000 0x47ff59a6a98d0d00 0xfb0471c073838002 0x67ec11c701ce0e00

def z15 : W := mkw 0xfffe69aa6b6b6000 0x47fff9a6a9adad80 0xfffffffffffff03f 0xffffffffffffffc0

def z16 : W := mkw 0xdfd8000063636000 0x477f6000018d8d80 0xff980000f3f3f006 0x47fe600003cfcfc0

def z17 : W := mkw 0x094030c8018180c4 0x082500c320060603 0x1b0471c0038381c2 0x646c11c7000e0e07

def z18 : W := mkw 0x9d50688a00000000 0x027541a228000000 0x1800700000000000 0x406001c000000000

def z19 : W := mkw 0x0001840084100c00 0x0000061002104030 0x04038c008c700e2d 0x90100e300231c038

def z20 : W := mkw 0xb406580052c00180 0x16d01960014b0006 0xf8047000738001c2 0x67e011c001ce0007

def z21 : W := mkw 0xffd7fdaad6d00d80 0x17ff5ff6ab5b4036 0xfffffffffff00fff 0xffffffffffffc03f

def z22 : W := mkw 0x0000000000000000 0x0000000000000000 0x04fb8e3f0000003d 0x1813ee38fc000000

def z23 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfb0471c000000002 0x63ec11c700000000

def z24 : W := mkw 0x62870130b0025930 0x218a1c04c2c00964 0xe0830030f0007004 0x03820c00c3c001c0

def z25 : W := mkw 0xb4074c00d2500900 0x16d01d3003494024 0xe4030c00f0700004 0x03900c3003c1c000

def z26 : W := mkw 0x4bd021aa00000000 0x012f4086a8000000 0x1bfcf3ff0000003b 0x786ff3cffc000000

def z27 : W := mkw 0x9400000042400000 0x0650000001090000 0xfc000000fff0000f 0xc7f0000003ffc000

def z28 : W := mkw 0xf687dd60f6d2cdd0 0x37da1f7583db4b37 0xff07fdc0fff38fef 0xf7fc1ff703ffce3f

def z29 : W := mkw 0xb406480000000000 0x02d0192000000000 0xe4030c0000000004 0x03900c3000000000

def z30 : W := mkw 0x00010250b006db70 0x2000040942c01b6d 0x00000000f00fffc0 0x8400000003c03fff

def z31 : W := mkw 0x9d50688a00000000 0x027541a228000000 0x1c78fc0f00000008 0x5071e3f03c000000

def z32 : W := mkw 0x002984008c382c00 0x0000a6100230e0b0 0x04fb8c008c7c7e3d 0x9013ee300231f1f8

def z33 : W := mkw 0x0968b6cd0dbda6ce 0x0825a2db3436f69b 0x1f7cffcf0fff8ffb 0xfc7df3ff3c3ffe3f

def z34 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe7ff8ffff00fffff 0xbf9ffe3fffc03fff

def z35 : W := mkw 0x0000024000048240 0x0000000900001209 0x00000000000f8fc0 0x8400000000003e3f

def z36 : W := mkw 0xfffe49226b6b6000 0x47fff92489adad80 0xfffb0c33fffff01f 0xc7ffec30cfffffc0

def z37 : W := mkw 0x2006012000000000 0x0080180480000000 0x000703f000000020 0x28001c0fc0000000

def z38 : W := mkw 0x00200204080c0208 0x0000800810203008 0x0060020c000c0010 0x0801800830003000

def z39 : W := mkw 0x00280215082c322a 0x0000a0085420b0c8 0x00f8023f000c7010 0x0803e008fc0031c0

def z40 : W := mkw 0x6bc621a800000000 0x01af1886a0000000 0xfbe7f3fc0000003f 0x7bef9fcff0000000

def z41 : W := mkw 0xdfd0000000000000 0x037f400000000000 0xfff800000000001f 0x43ffe00000000000

def z42 : W := mkw 0x002080040c080408 0x0000820010302010 0x0060800c0c000008 0x1001820030300000

def z43 : W := mkw 0xb42fde15defc3faa 0x16d0bf78577bf0fe 0xfcfffe3ffffc7fff 0xfff3fff8fffff1ff

def z44 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfcf80000fff0700c 0x43f3e00003ffc1c0

def z45 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xe4030c00fff00fc4 0x87900c3003ffc03f

def z46 : W := mkw 0xffd7edaa84100c00 0x03ff5fb6aa104030 0xffffffff8c700e3f 0xfbfffffffe31c038

def z47 : W := mkw 0x0000024000048240 0x0000000900001209 0x030403c0000f8ff3 0xac0c100f00003e3f

def z48 : W := mkw 0x6be7b3fcbd8fdffc 0x29af9ecff2f63f7f 0xfbe7f3fcff8fffff 0xffef9fcff3fe3fff

def z49 : W := mkw 0x0960000009090000 0x0025800000242400 0x1b6000000f8f801b 0xc46d8000003e3e00

def z50 : W := mkw 0xffd669aa42400000 0x07ff59a6a9090000 0xfffffffffff0003f 0xffffffffffffc000

def z51 : W := mkw 0xfff6fbee0d8d86cc 0x0bffdbefb836361b 0xffffffff0f8f8fff 0xfffffffffc3e3e3f

def z52 : W := mkw 0x0940b2cc058586cc 0x082502cb3016161b 0x1b04f3cc03838fe2 0x7c6c13cf300e0e3f

def z53 : W := mkw 0x0000900004800480 0x0000024000120012 0x0004f00000000fe0 0x300013c00000003f

def z54 : W := mkw 0x002092440d8d86cc 0x080082491036361b 0x000000000f8f8fc0 0x84000000003e3e3f

def z55 : W := mkw 0xf696492200000000 0x03da592488000000 0xe49b0c3300000004 0x03926c30cc000000

def z56 : W := mkw 0x428003702006d270 0x210a000dc0801b49 0xe38003f0f00ff017 0x8f8e000fc3c03fc0

def z57 : W := mkw 0x62af0370b82efb70 0x218abc0dc2e0bbed 0xe7ff03f0fc7fffff 0xaf9ffc0fc3f1ffff

def z58 : W := mkw 0x6286012000000000 0x018a180480000000 0xe38703f000000037 0x2b8e1c0fc0000000

def z59 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z60 : W := mkw 0xb406dc0056d00580 0x16d01b70015b4016 0xfc04fc007ff001ca 0x77f013f001ffc007

def z61 : W := mkw 0xdfd0000000000000 0x037f400000000000 0xfffb8e3f0000003f 0x5bffee38fc000000

def z62 : W := mkw 0x0009861584343e2a 0x000026185610d0f8 0x049b8e3f80707e24 0x18126e38fe01c1f8

def z63 : W := mkw 0xf696492200000000 0x03da592488000000 0xe4fb8e3f0000003d 0x1b93ee38fc000000

def z64 : W := mkw 0x002996158cbc3eaa 0x0000a6585632f0fa 0x1cfffe3f8ffc7fff 0xfc73fff8fe3ff1ff

def z65 : W := mkw 0x0000900004800480 0x0000024000120012 0x1804f0000f800feb 0xf46013c0003e003f

def z66 : W := mkw 0xbd67feccdfdd8fcc 0x1ef59ffb337f763f 0xff67ffccffff8fff 0xfffd9fff33fffe3f

def z67 : W := mkw 0x0009041180303822 0x000024104600c0e0 0x049b0c3380707004 0x00126c30ce01c1c0

def z68 : W := mkw 0x628601603002c150 0x218a180580c00b05 0xe30401c0700381c2 0x278c100701c00e07

def z69 : W := mkw 0xffd669ea3002c150 0x23ff59a7a8c00b05 0xffffffff700381ff 0x7ffffffffdc00e07

def z70 : W := mkw 0x0028000008282000 0x0000a0000020a080 0x00f80000000c7010 0x0003e000000031c0

def z71 : W := mkw 0xbd66facc5fcd87cc 0x1ef59beb317f361f 0xfb64f3cc7f8f8ffb 0xffed93cf31fe3e3f

def z72 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x000000008c7c7e00 0x800000000231f1f8

def z73 : W := mkw 0x0960208c0909000c 0x0825808230242400 0x0060000c00000000 0x0001800030000000

def z74 : W := mkw 0x0000000020024000 0x0000000000800900 0x00000000f00ff000 0x8400000003c03fc0

def z75 : W := mkw 0x0960b08c0d89048c 0x082582c230362412 0x1b60f00c0f8f801b 0xd46d83c0303e3e00

def z76 : W := mkw 0x0940b2cc048486cc 0x082502cb3012121b 0x1b64f3cc00000ffb 0x786d93cf3000003f

def z77 : W := mkw 0xdff9b6ddeffffeee 0x4f7fe6db77bffffb 0xffffffffffffffff 0xffffffffffffffff

def z78 : W := mkw 0x9d7800004b692000 0x4675e000012da480 0x1cf800008ffc701d 0xc073e000023ff1c0

def z79 : W := mkw 0xb4074c00d2500900 0x16d01d3003494024 0xe4070c00f0700fe7 0xa7901c3003c1c03f

def z80 : W := mkw 0x4bd021aa00000000 0x012f4086a8000000 0x03f803ff00000010 0x080fe00ffc000000

def z81 : W := mkw 0x002996558dbdbeee 0x0800a6595636f6fb 0x000000008fffffc0 0x84000000023fffff

def z82 : W := mkw 0x0000000000000000 0x0000000000000000 0x00800000800c7015 0x80020000020031c0

def z83 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b0471c00f8f8fc2 0xe46c11c7003e3e3f

def z84 : W := mkw 0xffffefbf8c3c3e2a 0x03ffffbefe30f0f8 0xffffffff8c7c7e3f 0xfbfffffffe31f1f8

def z85 : W := mkw 0xffd76bfab006db70 0x23ff5dafeac01b6d 0xfb8773f0f00ffff7 0xefee1dcfc3c03fff

def z86 : W := mkw 0x096022cc090d824c 0x0825808b30243609 0x036003cc000f8010 0x080d800f30003e00

def z87 : W := mkw 0xfff7ffeedfdd8fcc 0x1fffdfffbb7f763f 0xffffffffffff8fff 0xfffffffffffffe3f

def z88 : W := mkw 0xbd47fc88d6d00d80 0x16f51ff2235b4036 0xff67ffccfff00fff 0xfffd9fff33ffc03f

def z89 : W := mkw 0x62af8775bc3eff7a 0x218abe1dd6f0fbfd 0xe7ff8ffffc7fffff 0xbf9ffe3ffff1ffff

def z90 : W := mkw 0x4280000020024000 0x010a000000800900 0xe300000070038002 0x078c000001c00e00

def z91 : W := mkw 0xfffe01607b6be150 0x67fff80581edaf85 0xfffc01c0fffff1df 0xe7fff00703ffffc7

def z92 : W := mkw 0x0000900004800480 0x0000024000120012 0x1800f0000f800008 0x506003c0003e0000

def z93 : W := mkw 0xbd7fdc00dff92d80 0x56f5ff70037fe4b6 0xfc7ffc00fff00fef 0xf7f1fff003ffc03f

def z94 : W := mkw 0x6bd669aa00000000 0x01af59a6a8000000 0x03ffffff00000030 0x380ffffffc000000

def z95 : W := mkw 0xffd76bfab006db70 0x23ff5dafeac01b6d 0xfffffffff00fffff 0xffffffffffc03fff

def z96 : W := mkw 0x0000000063434000 0x44000000018d0d00 0x0000000073838000 0x0400000001ce0e00

def z97 : W := mkw 0xffd7fdaad6d00d80 0x17ff5ff6ab5b4036 0xff07fdc0fff00fef 0xf7fc1ff703ffc03f

def z98 : W := mkw 0x62870130b0025930 0x218a1c04c2c00964 0xe3830030f00ff017 0x878e0c00c3c03fc0

def z99 : W := mkw 0xffde69aa62626000 0x47ff79a6a9898980 0xfffffffff070703f 0x7bffffffffc1c1c0

def z100 : W := mkw 0x4280000020024000 0x010a000000800900 0xe3800000f00ff017 0x878e000003c03fc0

def z101 : W := mkw 0x002884050c38240a 0x0000a2101430e090 0x04788c0f0c700008 0x1011e2303c31c000

def z102 : W := mkw 0x0960b28c0d8d068c 0x082582ca3036341a 0x1860f20c0f8c0e39 0xd86183c8303e3038

def z103 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfbfc73ff00000012 0x6beff1cffc000000

def z104 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xf8047000fff00fc2 0xe7e011c003ffc03f

def z105 : W := mkw 0x00019400d6d00d80 0x14000650035b4036 0x00000000fff00fc0 0x8400000003ffc03f

def z106 : W := mkw 0x00298615ef7f7e2a 0x4400a61857bdfdf8 0x04fb8e3ffffffe3d 0x9c13ee38fffffff8

def z107 : W := mkw 0x0001021080041a20 0x0000040842001068 0x00000000800c7e00 0x80000000020031f8

def z108 : W := mkw 0x2006492200000000 0x0080192488000000 0x00030c3300000000 0x00000c30cc000000

def z109 : W := mkw 0x002082040c0c0608 0x0000820810303018 0x0060820c0c0c0e39 0x9801820830303038

def z110 : W := mkw 0xdfd0000063434000 0x477f4000018d0d00 0xff000000fff3800f 0xc7fc000003ffce00

def z111 : W := mkw 0x002186158c1c1e2a 0x0000861856307078 0x00638e3f0c0c0e39 0x98018e38fc303038

def z112 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfb07ffff00000022 0x7bec1ffffc000000

def z113 : W := mkw 0xdff98615ef7f7e2a 0x477fe61857bdfdf8 0xfffb8e3ffffffe3f 0xdfffee38fffffff8

def z114 : W := mkw 0x2007dc0094900d80 0x10801f7002524036 0xe007fc00f0000fe7 0xb7801ff003c0003f

def z115 : W := mkw 0x6bff0370b92ffb70 0x61affc0dc2e4bfed 0xe3ff03f0f00ffff7 0xaf8ffc0fc3c03fff

def z116 : W := mkw 0x942800006b6b6000 0x4650a00001adad80 0xfc000000fffff00f 0xc7f0000003ffffc0

def z117 : W := mkw 0x4bd0000021034000 0x412f400000840d00 0x0300000000038000 0x000c000000000e00

def z118 : W := mkw 0x0000b2cc048486cc 0x080002cb3012121b 0x0004f3cc00000fe0 0x380013cf3000003f

def z119 : W := mkw 0xb427de44dfdd8fcc 0x1ed09f79137f763f 0xfc07fc00ffff8fef 0xf7f01ff003fffe3f

def z120 : W := mkw 0x42a800006b6b6000 0x450aa00001adad80 0xe3800000fffff017 0x878e000003ffffc0

def z121 : W := mkw 0x9d6000004b490000 0x06758000012d2400 0xff600000ffff801f 0xc7fd800003fffe00

def z122 : W := mkw 0x4bf822cc292fe24c 0x492fe08b30a4bf89 0x03f803cc000ff010 0x080fe00f30003fc0

def z123 : W := mkw 0x4bf80000292b6000 0x412fe00000a4ad80 0xe3f80000f00ff017 0x878fe00003c03fc0

def z124 : W := mkw 0x94004c0042500000 0x1650013001094000 0x04000c0000700000 0x001000300001c000

def z125 : W := mkw 0xf687dd30f6d25db0 0x37da1f74c3db4976 0xfc87fc30fff07fef 0xf7f21ff0c3ffc1ff

def z126 : W := mkw 0x000022cc0004824c 0x0800008b30001209 0x000003cc00000000 0x0800000f30000000

def z127 : W := mkw 0x9429de15cefc3eaa 0x1650a778573bf0fa 0x1cfbfe3f8ffc7e3d 0xd873eff8fe3ff1f8

def z128 : W := mkw 0x002986558c3cbe6a 0x0000a6195630f2f9 0x07ff8fff8c7fffff 0xbc1ffe3ffe31ffff

def z129 : W := mkw 0xffd6012000000000 0x03ff580480000000 0xffff03f00000003f 0x6bfffc0fc0000000

def z130 : W := mkw 0x0001840084100c00 0x0000061002104030 0x000000008c700e00 0x800000000231c038

def z131 : W := mkw 0xdff800004b692000 0x477fe000012da480 0xfff800000ff0001f 0x43ffe000003fc000

def z132 : W := mkw 0x2007dc0094900d80 0x10801f7002524036 0x0007fc0000000fe0 0x30001ff00000003f

def z133 : W := mkw 0xffffdc00fffb6d80 0x57ffff7003ffedb6 0xfffffc00ffffffff 0xf7fffff003ffffff

def z134 : W := mkw 0xd690000000000000 0x035a400000000000 0xe498000000000004 0x0392600000000000

def z135 : W := mkw 0x002886150c3c362a 0x0000a2185430f0d8 0x04f88e3f0c7c7018 0x1813e238fc31f1c0

def z136 : W := mkw 0xfffe69aa4b692000 0x47fff9a6a92da480 0xffffffff0ff0003f 0x7bfffffffc3fc000

def z137 : W := mkw 0x200669aa00000000 0x008019a6a8000000 0x0007ffff00000020 0x38001ffffc000000

def z138 : W := mkw 0x202fefbf8c3c3e2a 0x0080bfbefe30f0f8 0x04ffffff8c7c7e3d 0xb813fffffe31f1f8

def z139 : W := mkw 0x094020c801018044 0x0825008320040601 0x030001c000038000 0x000c000700000e00

def z140 : W := mkw 0x0028000008282000 0x0000a0000020a080 0x04f800008c7c701d 0x8013e0000231f1c0

def z141 : W := mkw 0x9400900046c00480 0x06500240011b0012 0xfc04f000fff00fef 0xf7f013c003ffc03f

def z142 : W := mkw 0xf6874d30f2525930 0x37da1d34c3c94964 0xe4830c30f0707004 0x03920c30c3c1c1c0

def z143 : W := mkw 0xf687dc00f6d24d80 0x17da1f7003db4936 0xff87fc00ffffffff 0xf7fe1ff003ffffff

def z144 : W := mkw 0x0001940094900d80 0x1000065002524036 0x0000000000000fc0 0x000000000000003f

def z145 : W := mkw 0x9428dc054ef8248a 0x1650a370153be092 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z146 : W := mkw 0x0960a2cc0d0d864c 0x0825828b30343619 0x036083cc0c0f8e39 0x980d820f30303e38

def z147 : W := mkw 0x202f86159c3c3f2a 0x0080be185670f0fc 0xe4ff8e3ffc7c7fff 0xbf93fe38fff1f1ff

def z148 : W := mkw 0x00009240048486c0 0x000002490012121b 0x1b04f3c00f8f8ffb 0xfc6c13cf003e3e3f

def z149 : W := mkw 0x428003702006d270 0x210a000dc0801b49 0x038003f0000ff010 0x080e000fc0003fc0

def z150 : W := mkw 0x9400dc0046d00480 0x16500370011b4012 0x1c00fc000ff00008 0x507003f0003fc000

def z151 : W := mkw 0x0001861584141e2a 0x0000061856105078 0x0000000000000e00 0x0000000000000038

def z152 : W := mkw 0x9d78b2cc4feda6cc 0x4e75e2cb313fb69b 0x1f7cf3cc0fff8ffb 0xfc7df3cf303ffe3f

def z153 : W := mkw 0xb406480000000000 0x02d0192000000000 0xfc07fc000000002f 0x73f01ff000000000

def z154 : W := mkw 0x0029b6dd8cbcbeee 0x0800a6db7632f2fb 0x04ffffff8c7c7ffd 0xb813fffffe31f1ff

def z155 : W := mkw 0x9d78dc004ff92480 0x5675e370013fe492 0x1c78fc000ff00008 0x5071e3f0003fc000

def z156 : W := mkw 0x0001861584141e2a 0x0000061856105078 0x00038e3f00000e20 0x18000e38fc000038

def z157 : W := mkw 0xb42fce158c3c3e2a 0x02d0bf385630f0f8 0xfcfffe3f8c7c7e3f 0xfbf3fff8fe31f1f8

def z158 : W := mkw 0xb40fdc11d6f03da2 0x16d03f70475bc0f6 0xfc9ffc33fff07fef 0xf7f27ff0cfffc1ff

def z159 : W := mkw 0x0028000008282000 0x0000a0000020a080 0x047800000c700008 0x0011e0000031c000

def z160 : W := mkw 0x628603603006c350 0x218a180d80c01b0d 0xe30403c0700f8ff3 0xaf8c100f01c03e3f

def z161 : W := mkw 0xffff8775ff7fff7a 0x67fffe1dd7fdfffd 0xffff8fffffffffff 0xfffffe3fffffffff

def z162 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1fffffff0f8f8fff 0xfc7ffffffc3e3e3f

def z163 : W := mkw 0x4298000020226000 0x410a600000808980 0x0098000000007000 0x00026000000001c0

def z164 : W := mkw 0x002882040c2c2608 0x0000a2081030b098 0x04f8820c8c7c7e3d 0x9813e2083231f1f8

def z165 : W := mkw 0x2007037090049b70 0x20801c0dc240126d 0xe00703f0f0000fe7 0xaf801c0fc3c0003f

def z166 : W := mkw 0xdff820886b6b6000 0x477fe08221adad80 0xfffcf3ccfffff03f 0xfffff3cf33ffffc0

def z167 : W := mkw 0x2007000090000900 0x00801c0002400024 0xe0070000f0000fe7 0xa7801c0003c0003f

def z168 : W := mkw 0xf687df70f6d6dff0 0x37da1f7dc3db5b7f 0xff87fff0ffffffff 0xfffe1fffc3ffffff

def z169 : W := mkw 0x2007037090049b70 0x20801c0dc240126d 0x000703f000000fe0 0x28001c0fc000003f

def z170 : W := mkw 0xffff0370fb6ffb70 0x67fffc0dc3edbfed 0xffff03f0ffffffff 0xeffffc0fc3ffffff

def z171 : W := mkw 0x096092440d8d86cc 0x082582491036361b 0x1b6000000f8f8fdb 0xc46d8000003e3e3f

def z172 : W := mkw 0x9400000042400000 0x0650000001090000 0xf800000073800002 0x47e0000001ce0000

def z173 : W := mkw 0x0009041180303822 0x000024104600c0e0 0x04fb8e3f8070703d 0x1813ee38fe01c1c0

def z174 : W := mkw 0xffff6bfafb6ffb70 0x67fffdafebedbfed 0xffffffffffffffff 0xffffffffffffffff

def z175 : W := mkw 0xffffffff8dbdbeee 0x0bfffffffe36f6fb 0xffffffff8fffffff 0xfffffffffe3fffff

def z176 : W := mkw 0xf697dd22d6d00d80 0x17da5f748b5b4036 0xfc9ffc33fff00fef 0xf7f27ff0cfffc03f

def z177 : W := mkw 0xf6875b70f2c6dbf0 0x37da1d6dc3cb1b6f 0xfb8773f0f38ffff7 0xefee1dcfc3ce3fff

def z178 : W := mkw 0xdfd069aa00000000 0x037f41a6a8000000 0x1ff8ffff00000018 0x587fe3fffc000000

def z179 : W := mkw 0x00290210882c3a20 0x0000a4084220b0e8 0x04fb02308c7c7e3d 0x8813ec08c231f1f8

def z180 : W := mkw 0xdff8688a6b6b6000 0x477fe1a229adad80 0xfff8fc0ffffff01f 0xd7ffe3f03fffffc0

def z181 : W := mkw 0x6befb7fdbdbffffe 0x29afbedff6f6ffff 0xffffffffffffffff 0xffffffffffffffff

def z182 : W := mkw 0x4bd023fa2006d270 0x212f408fe8801b49 0x03f803ff000ff010 0x080fe00ffc003fc0

def z183 : W := mkw 0x0000000000000000 0x0000000000000000 0x049b0c3300000004 0x00126c30cc000000

def z184 : W := mkw 0xbd4678c853c181c4 0x1ef519e3214f0607 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z185 : W := mkw 0xf686492000000000 0x03da192480000000 0xff87fff00000003f 0x7bfe1fffc0000000

def z186 : W := mkw 0xdfd021aa00000000 0x037f4086a8000000 0xfff803ff0000001f 0x4bffe00ffc000000

def z187 : W := mkw 0x0001840084100c00 0x0000061002104030 0x00038c0000000e20 0x10000e3000000038

def z188 : W := mkw 0x0960000009090000 0x0025800000242400 0x03600000000f8010 0x000d800000003e00

def z189 : W := mkw 0xf686596072c2c1d0 0x37da196581cb0b07 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z190 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x049b0c338c7c7e04 0x80126c30ce31f1f8

def z191 : W := mkw 0x0000b08c0480048c 0x080002c230120012 0x0000f00c00000000 0x100003c030000000

def z192 : W := mkw 0xb4074c00d2500900 0x16d01d3003494024 0xfc030c00fff0000f 0xc7f00c3003ffc000

def z193 : W := mkw 0x00019400d6d00d80 0x14000650035b4036 0x1804f000fff00feb 0xf46013c003ffc03f

def z194 : W := mkw 0xfffe01206b6b6000 0x47fff80481adad80 0xffff03f0fffff03f 0xeffffc0fc3ffffc0

def z195 : W := mkw 0xf6974d22d2500900 0x17da5d348b494024 0xe49b0c33f0700004 0x03926c30cfc1c000

def z196 : W := mkw 0xdfd0688a00000000 0x037f41a228000000 0xfff8fc0f0000001f 0x53ffe3f03c000000

def z197 : W := mkw 0x6286012020024000 0x018a180480800900 0xe38703f0f00ff037 0xaf8e1c0fc3c03fc0

def z198 : W := mkw 0x0001000090000900 0x0000040002400024 0x00000000f0000fc0 0x8400000003c0003f

def z199 : W := mkw 0x0961b6ccdfdd8fcc 0x1c2586db337f763f 0x1b64f3ccffff8ffb 0xfc6d93cf33fffe3f

def z200 : W := mkw 0x9d7800004b692000 0x4675e000012da480 0x1c7800000ff00008 0x4071e000003fc000

def z201 : W := mkw 0x6287df70b496dff0 0x318a1f7dc2d25b7f 0xe387fff0f00ffff7 0xbf8e1fffc3c03fff

def z202 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe30703f070038fe2 0x2f8c1c0fc1c00e3f

def z203 : W := mkw 0x0978000009292000 0x4025e0000024a480 0x0078000000000000 0x0001e00000000000

def z204 : W := mkw 0xb4075800d2c00980 0x16d01d60034b0026 0xf8077000f3800fe7 0xe7e01dc003ce003f

def z205 : W := mkw 0xb406480000000000 0x02d0192000000000 0xfcfffe3f0000003f 0x7bf3fff8fc000000

def z206 : W := mkw 0x428003702006d270 0x210a000dc0801b49 0x038403f0000ffff3 0xac0e100fc0003fff

def z207 : W := mkw 0x9d78b08c4fe9248c 0x4e75e2c2313fa492 0x1c78f00c0ff00008 0x5071e3c0303fc000

def z208 : W := mkw 0x9d50000000000000 0x0275400000000000 0x1c78000000000008 0x4071e00000000000

def z209 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xff9f7df300000006 0x63fe7df7cc000000

def z210 : W := mkw 0xdff802406b6fe240 0x477fe00901adbf89 0xfffc03c0ffffffff 0xeffff00f03ffffff

def z211 : W := mkw 0x002996558dbdbeee 0x0800a6595636f6fb 0x04fb8e3f8ffffffd 0x9c13ee38fe3fffff

def z212 : W := mkw 0xb40669aa00000000 0x02d019a6a8000000 0xfc07ffff0000002f 0x7bf01ffffc000000

def z213 : W := mkw 0x002090040d89048c 0x0800824010362412 0x000000000f800000 0x00000000003e0000

def z214 : W := mkw 0x42a80000282a6000 0x010aa00000a0a980 0xe7f80000fc7ff01f 0x879fe00003f1ffc0

def z215 : W := mkw 0xb42fdc00def82d80 0x16d0bf70037be0b6 0xfcfffc00fffc7fff 0xf7f3fff003fff1ff

def z216 : W := mkw 0x2007df7094949ff0 0x30801f7dc252527f 0x0007fff000000fe0 0x38001fffc000003f

def z217 : W := mkw 0x0001021080041a20 0x0000040842001068 0x00830230800c7e35 0x88020c08c20031f8

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x04038c000000002d 0x10100e3000000000

def z219 : W := mkw 0x0000024000048240 0x0000000900001209 0x000403c000000fe0 0x2800100f0000003f

def z220 : W := mkw 0x4290012200000000 0x010a400488000000 0x0098003300000000 0x00026000cc000000

def z221 : W := mkw 0x4bf80370292ff270 0x612fe00dc0a4bfc9 0x03f803f0000ff010 0x080fe00fc0003fc0

def z222 : W := mkw 0x0960208809090000 0x0025808220242400 0x1b64f3cc0f8f803b 0xfc6d93cf303e3e00

def z223 : W := mkw 0xfff6ebae0c0c0608 0x03ffdbaeb8303018 0xffffffff0c0c0e3f 0xfbfffffffc303038

def z224 : W := mkw 0xffffb3fcffeffffc 0x6ffffecff3ffbfff 0xfffff3fcffffffff 0xffffffcff3ffffff

def z225 : W := mkw 0x002884050c38240a 0x0000a2101430e090 0x04f88c0f8c7c701d 0x9013e2303e31f1c0

def z226 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04038c008c7c7e2d 0x90100e300231f1f8

def z227 : W := mkw 0x2007dc0094900d80 0x10801f7002524036 0x0407fc008c700fed 0xb0101ff00231c03f

def z228 : W := mkw 0x2006000000000000 0x0080180000000000 0xe007000000000027 0x23801c0000000000

def z229 : W := mkw 0xffd769aa90000900 0x03ff5da6aa400024 0xfffffffff0000fff 0xffffffffffc0003f

def z230 : W := mkw 0x0000000000000000 0x0000000000000000 0x04788c0f00000008 0x1011e2303c000000

def z231 : W := mkw 0xfffe69aa08282000 0x03fff9a6a820a080 0xffffffff8c7c703f 0xfbfffffffe31f1c0

def z232 : W := mkw 0x9d7800004b692000 0x4675e000012da480 0xfc780000fff0000f 0xc7f1e00003ffc000

def z233 : W := mkw 0x0028000008282000 0x0000a0000020a080 0x04fb8e3f8c7c703d 0x9813ee38fe31f1c0

def z234 : W := mkw 0x4bf80000292b6000 0x412fe00000a4ad80 0x07f800008c7ff01d 0x801fe0000231ffc0

def z235 : W := mkw 0x0028000008282000 0x0000a0000020a080 0x000000008c7c7000 0x800000000231f1c0

def z236 : W := mkw 0x002882150c2c362a 0x0000a2085430b0d8 0x00f8823f0c0c7e39 0x9803e208fc3031f8

def z237 : W := mkw 0x9400580042c00080 0x16500160010b0002 0x1800700003800000 0x406001c0000e0000

def z238 : W := mkw 0xfffeedaf0c38240a 0x03fffbb6bc30e090 0xffffffff0c70003f 0x7bfffffffc31c000

def z239 : W := mkw 0x20074c0090100900 0x10801d3002404024 0x00030c0000000000 0x00000c3000000000

def z240 : W := mkw 0x0029041188383822 0x0000a4104620e0e0 0x04fb0c338c7c701d 0x8013ec30ce31f1c0

def z241 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04788c0f8c7c7e08 0x9011e2303e31f1f8

def z242 : W := mkw 0xf6974932b0025930 0x23da5d24cac00964 0xe49b0c33f0007004 0x03926c30cfc001c0

def z243 : W := mkw 0xd698000062626000 0x475a600001898980 0xe7980000f07ff017 0x879e600003c1ffc0

def z244 : W := mkw 0xd690000062424000 0x475a400001890900 0xe000000070000000 0x0380000001c00000

def z245 : W := mkw 0x4bd021aa00000000 0x012f4086a8000000 0x030001c000000000 0x000c000700000000

def z246 : W := mkw 0xdff8b08c6feb648c 0x4f7fe2c231bfad92 0xfff8f00cfffff01f 0xd7ffe3c033ffffc0

def z247 : W := mkw 0x0940208800000000 0x0025008220000000 0x1b64f3cc0000003b 0x786d93cf30000000

def z248 : W := mkw 0x0001025080049a60 0x0000040942001269 0x038703f0800ffff7 0xac0e1c0fc2003fff

def z249 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfcfffe3ffff00fff 0xfff3fff8ffffc03f

def z250 : W := mkw 0xffd66bea00048240 0x03ff59afa8001209 0xffffffff000f8fff 0xfffffffffc003e3f

def z251 : W := mkw 0x002800004b692000 0x4400a000012da480 0x000000000ff00000 0x00000000003fc000

def z252 : W := mkw 0x628603702006d270 0x218a180dc0801b49 0xe38703f0000ff037 0x2b8e1c0fc0003fc0

def z253 : W := mkw 0xb407de15d6d41faa 0x16d01f78575b507e 0xfc07fe3ffff00fef 0xfff01ff8ffffc03f

def z254 : W := mkw 0x2007000090000900 0x00801c0002400024 0xe0030000f0000004 0x03800c0003c00000

def z255 : W := mkw 0x2007037090049b70 0x20801c0dc240126d 0x030703f0000f8ff3 0xac0c1c0fc0003e3f

def z256 : W := mkw 0x00010250b006db70 0x2000040942c01b6d 0x030403c0f00ffff3 0xac0c100f03c03fff

def z257 : W := mkw 0x0000688a00000000 0x000001a228000000 0x0000fc0f00000000 0x100003f03c000000

def z258 : W := mkw 0x00280215082c322a 0x0000a0085420b0c8 0x00000000000c7000 0x00000000000031c0

def z259 : W := mkw 0x6287b3fcb486dffc 0x298a1ecff2d21b7f 0xe387f3fcf00ffff7 0xbf8e1fcff3c03fff

def z260 : W := mkw 0xffd76bfa90049b70 0x23ff5dafea40126d 0xffffffff00000fff 0x7bfffffffc00003f

def z261 : W := mkw 0x9d7884054f79240a 0x4675e210153de490 0x1c788c0f0ff00008 0x5071e2303c3fc000

def z262 : W := mkw 0xfffffeccffffefcc 0x5ffffffb33ffffbf 0xffffffccffffffff 0xffffffff33ffffff

def z263 : W := mkw 0xd6b800006a6a6000 0x475ae00001a9a980 0xe4f80000fc7c701d 0x8393e00003f1f1c0

def z264 : W := mkw 0xffe7fffcffdfdffc 0x3fff9ffff3ff7f7f 0xffe7fffcffffffff 0xffff9ffff3ffffff

def z265 : W := mkw 0x0960b08c0d89048c 0x082582c230362412 0x1860f00c0f800008 0x506183c0303e0000

def z266 : W := mkw 0x94298615ce7c3e2a 0x0650a6185739f0f8 0xfcfb8e3ffffc7e3f 0xdff3ee38fffff1f8

def z267 : W := mkw 0xffffefffbc3eff7a 0x23ffffbffef0fbfd 0xfffffffffc7fffff 0xfffffffffff1ffff

def z268 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xf807fc0073800fe2 0x77e01ff001ce003f

def z269 : W := mkw 0x0001840084100c00 0x0000061002104030 0x04fb8e3f8c700e3d 0x9813ee38fe31c038

def z270 : W := mkw 0x002884050c38240a 0x0000a2101430e090 0x000000000c700000 0x000000000031c000

def z271 : W := mkw 0x0961b6dd8d9d9eee 0x082586db7636767b 0x1b67ffff0f8f8ffb 0xfc6d9ffffc3e3e3f

def z272 : W := mkw 0x4be0b3fc2d8fd6fc 0x292f82cff0b63f5b 0x1be4f3fc0f8ffffb 0xfc6f93cff03e3fff

def z273 : W := mkw 0x0000820404040608 0x0000020810101018 0x0000820c00000e20 0x1800020830000038

def z274 : W := mkw 0x0940208800000000 0x0025008220000000 0x1b0471c000000002 0x606c11c700000000

def z275 : W := mkw 0x0000000000000000 0x0000000000000000 0x0083023000000035 0x08020c08c0000000

def z276 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b60f3cc0f8f8018 0x586d83cf303e3e00

def z277 : W := mkw 0x0001040080100800 0x0000041002004020 0x04030c0080700004 0x00100c300201c000

def z278 : W := mkw 0xfff6fbee0d8d86cc 0x0bffdbefb836361b 0xfb64f3cc0f8f8ffb 0xffed93cf303e3e3f

def z279 : W := mkw 0x6be6b3ec0d8d86cc 0x09af9acfb036361b 0xfbe7f3fc0f8f8fff 0xffef9fcff03e3e3f

def z280 : W := mkw 0x094022c800048240 0x0025008b20001209 0x1b64f3cc000f8ffb 0xfc6d93cf30003e3f

def z281 : W := mkw 0x0960a28c0c0c0608 0x0025828a30303018 0x1b64f3cc0c0c0e3b 0xf86d93cf30303038

def z282 : W := mkw 0x6bc631e83183c1d4 0x29af18c7a0c60f07 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z283 : W := mkw 0xbd67dc00dfd90d80 0x16f59f70037f6436 0xff67fc00ffff8fff 0xf7fd9ff003fffe3f

def z284 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x008302308c7c7e35 0x88020c08c231f1f8

def z285 : W := mkw 0x0969a6dd8d3dbe6e 0x0825a69b7634f6f9 0x07fb8fff8c7ffe3d 0x981fee3ffe31fff8

def z286 : W := mkw 0x42a80375282ef27a 0x210aa00dd4a0bbc9 0x03f803ff000ff010 0x080fe00ffc003fc0

def z287 : W := mkw 0x0000000000000000 0x0000000000000000 0x00f8023f00000010 0x0803e008fc000000

def z288 : W := mkw 0x628601603002c150 0x218a180580c00b05 0xe38703f0700381f7 0x2f8e1c0fc1c00e07

def z289 : W := mkw 0x002182148c0c1e28 0x0000860852303078 0x00e3823c8c0c7e3d 0x98038e08f23031f8

def z290 : W := mkw 0x09600240090d8240 0x0025800900243609 0x1b6403c00f8f8ffb 0xec6d900f003e3e3f

def z291 : W := mkw 0xffd6480000000000 0x03ff592000000000 0xfffffc000000003f 0x73fffff000000000

def z292 : W := mkw 0x094032c8018582c4 0x082500cb2006160b 0x1b0473c0038f8ff3 0xec6c11cf000e3e3f

def z293 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x00f8023f8c7c7e10 0x8803e008fe31f1f8

def z294 : W := mkw 0xb427de04dedc0f88 0x16d09f78137b703e 0xfc67fe0cfffc0fff 0xfff19ff833fff03f

def z295 : W := mkw 0x62878775b416df7a 0x218a1e1dd6d05b7d 0xe3878ffff00ffff7 0xbf8e1e3fffc03fff

def z296 : W := mkw 0x9400dc0046d00480 0x16500370011b4012 0x1c04fc000ff00feb 0xf47013f0003fc03f

def z297 : W := mkw 0x4bf023ee090d824c 0x092fc08fb8243609 0x03f803ff000f8010 0x080fe00ffc003e00

def z298 : W := mkw 0xbd5669aa00000000 0x02f559a6a8000000 0x1c7fffff00000028 0x7871fffffc000000

def z299 : W := mkw 0xffd70370b006db70 0x23ff5c0dc2c01b6d 0xffff03f0f00fffff 0xeffffc0fc3c03fff

def z300 : W := mkw 0x9400dc0046d00480 0x16500370011b4012 0xfc00fc00fff0000f 0xd7f003f003ffc000

def z301 : W := mkw 0x0000024000048240 0x0000000900001209 0x030003c0000f8010 0x080c000f00003e00

def z302 : W := mkw 0x6bc723f8b006db70 0x21af1c8fe2c01b6d 0xfbe7f3fcf00fffff 0xffef9fcff3c03fff

def z303 : W := mkw 0x2967b3fc9d8d9ffc 0x28a59ecff276367f 0x1b67f3fc0f8f8ffb 0xfc6d9fcff03e3e3f

def z304 : W := mkw 0x4bf80000292b6000 0x412fe00000a4ad80 0x03f80000000ff010 0x000fe00000003fc0

def z305 : W := mkw 0x0940b0c8058184c4 0x082502c320160613 0x1b04f1c00f838feb 0xf46c13c7003e0e3f

def z306 : W := mkw 0x6286012000000000 0x018a180480000000 0xe083003000000004 0x03820c00c0000000

def z307 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xe407fc00f0700fe4 0x33901ff003c1c03f

def z308 : W := mkw 0x0968b2dd0dadb6ee 0x0825a2cb7436b6db 0x1bfcf3ff0f8ffffb 0xfc6ff3cffc3e3fff

def z309 : W := mkw 0xbd46688800000000 0x02f519a220000000 0xff67ffcc0000003f 0x7bfd9fff30000000

def z310 : W := mkw 0xdff98400ef7b6c00 0x477fe61003bdedb0 0xfffb8c00fffffe3f 0xd7ffee3003fffff8

def z311 : W := mkw 0x00299615defc3faa 0x1400a658577bf0fe 0x00000000fffc7fc0 0x8400000003fff1ff

def z312 : W := mkw 0x42a98775ac3efe7a 0x210aa61dd6b0fbf9 0x07fb8fff8c7ffe3d 0x981fee3ffe31fff8

def z313 : W := mkw 0x00280215082c322a 0x0000a0085420b0c8 0x04f8023f8c7c701d 0x8813e008fe31f1c0

def z314 : W := mkw 0x0940000001010000 0x0025000000040400 0x1b00000003838002 0x446c0000000e0e00

def z315 : W := mkw 0x002984158c383c2a 0x0000a6105630e0f0 0x04fb8c3f8c70700c 0x1013ee30fe31c1c0

def z316 : W := mkw 0xf6874f70f256db70 0x37da1d3dc3c95b6d 0xe7870ff0f07ffff7 0xaf9e1c3fc3c1ffff

def z317 : W := mkw 0x4bd0000000000000 0x012f400000000000 0x03f8000000000010 0x000fe00000000000

def z318 : W := mkw 0xffd669aa20024000 0x03ff59a6a8800900 0xfffffffff00ff03f 0xffffffffffc03fc0

def z319 : W := mkw 0x000084050410040a 0x0000021014104010 0x00008c0f00000000 0x100002303c000000

def z320 : W := mkw 0x002092040c8c0688 0x000082481032301a 0x1864f20c0f8c0ffb 0xfc6193c8303e303f

def z321 : W := mkw 0x94019400d6d00d80 0x16500650035b4036 0xfc000000fff00fcf 0xc7f0000003ffc03f

def z322 : W := mkw 0xdff90210eb6f7a20 0x477fe40843adbde8 0xfffb0230fffffe3f 0xcfffec08c3fffff8

def z323 : W := mkw 0x9d50000043410000 0x46754000010d0400 0x1800000003800000 0x40600000000e0000

def z324 : W := mkw 0xdfd0000063434000 0x477f4000018d0d00 0xfb00000073838002 0x47ec000001ce0e00

def z325 : W := mkw 0x0940000000000000 0x0025000000000000 0x1b6000000000001b 0x406d800000000000

def z326 : W := mkw 0x0969a69d8c3c3e2a 0x0025a69a7630f0f8 0x1fffffff8c7c7e3f 0xf87ffffffe31f1f8

def z327 : W := mkw 0xb42fdc00fffb6d80 0x56d0bf7003ffedb6 0xfc07fc00ffffffef 0xf7f01ff003ffffff

def z328 : W := mkw 0x2007037090049b70 0x20801c0dc240126d 0x008703f0800c7ff5 0xa8021c0fc20031ff

def z329 : W := mkw 0xfff66bee090d824c 0x0bffd9afb8243609 0xffffffff000f803f 0x7bfffffffc003e00

def z330 : W := mkw 0x9d60fecc4fdd86cc 0x1e7583fb313f761b 0x1f64ffcc0fff8ffb 0xfc7d93ff303ffe3f

def z331 : W := mkw 0x096022cc090d824c 0x0825808b30243609 0x1b64f3cc000f803b 0x786d93cf30003e00

def z332 : W := mkw 0x0001041180101822 0x0000041046004060 0x00030c3300000000 0x00000c30cc000000

def z333 : W := mkw 0x6be6b3ec3d8fc7dc 0x29af9acfb0f63f1f 0xfb64f3cc7f8f8ffb 0xffed93cf31fe3e3f

def z334 : W := mkw 0x002892446fefe6cc 0x4c00a24911bfbf9b 0x00000000ffffffc0 0x8400000003ffffff

def z335 : W := mkw 0xb406480000000000 0x02d0192000000000 0xf804700000000002 0x63e011c000000000

def z336 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfb000000fffff002 0xc7ec000003ffffc0

def z337 : W := mkw 0xf69669aa00000000 0x03da59a6a8000000 0xe49fffff00000024 0x3b927ffffc000000

def z338 : W := mkw 0xb407de50f6d6dff0 0x36d01f7943db5b7f 0xfc07fc00ffffffef 0xf7f01ff003ffffff

def z339 : W := mkw 0x9410480200000000 0x0250412008000000 0x04180c0300000000 0x001060300c000000

def z340 : W := mkw 0xdff0000009090000 0x037fc00000242400 0xfff800000f8f801f 0xc7ffe000003e3e00

def z341 : W := mkw 0x0000940046d00480 0x14000250011b4012 0x000000000ff00000 0x00000000003fc000

def z342 : W := mkw 0xffd6fdaa46d00480 0x17ff5bf6a91b4012 0xffffffff0ff0003f 0x7bfffffffc3fc000

def z343 : W := mkw 0xffd6580073c34180 0x57ff596001cf0d06 0xfb047000738381c2 0x67ec11c001ce0e07

def z344 : W := mkw 0x6be723fcb90fdb7c 0x29af9c8ff2e43f6d 0xe3e703fcf00ffff7 0xaf8f9c0ff3c03fff

def z345 : W := mkw 0x2007000090000900 0x00801c0002400024 0x0007000000000fe0 0x20001c000000003f

def z346 : W := mkw 0x2967fecc9d9d8fcc 0x18a59ffb3276763f 0x1b67ffcc0f8f8ffb 0xfc6d9fff303e3e3f

def z347 : W := mkw 0xb406480052400100 0x16d0192001490004 0xe000000070000000 0x0380000001c00000

def z348 : W := mkw 0x002082040c0c0608 0x0000820810303018 0x000000000c0c0e00 0x8000000000303038

def z349 : W := mkw 0x0001000080000800 0x0000040002000020 0x0003000080000e25 0x80000c0002000038

def z350 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xff07fdc00000002f 0x73fc1ff700000000

def z351 : W := mkw 0x42810250b006db70 0x210a040942c01b6d 0xe3800000f00fffd7 0x878e000003c03fff

def z352 : W := mkw 0x0001b6dd84949eee 0x080006db7612527b 0x0007ffff00000fe0 0x38001ffffc00003f

def z353 : W := mkw 0x6286036000048240 0x018a180d80001209 0xe38703f0000f8ff7 0xaf8e1c0fc0003e3f

def z354 : W := mkw 0xd680000062424000 0x075a000001890900 0xff800000fffff01f 0xc7fe000003ffffc0

def z355 : W := mkw 0xdff90411eb7b7822 0x477fe41047adede0 0xfffb0c33fffff01f 0xc7ffec30cfffffc0

def z356 : W := mkw 0x2006580010800180 0x1080196000420006 0x00047000000001c0 0x200011c000000007

def z357 : W := mkw 0x9d7800004b692000 0x4675e000012da480 0x1f7800000fff801b 0xc47de000003ffe00

def z358 : W := mkw 0x428002402006c240 0x010a000900801b09 0xe38403c0f00ffff7 0xaf8e100f03c03fff

def z359 : W := mkw 0xd6b800006b6b6000 0x475ae00001adad80 0xe4980000fffff004 0x8792600003ffffc0

def z360 : W := mkw 0xffd7fffaf6d6dff0 0x37ff5fffebdb5b7f 0xffffffffffffffff 0xffffffffffffffff

def z361 : W := mkw 0x0000b2cc048486cc 0x080002cb3012121b 0x1804f3cc0f800feb 0xfc6013cf303e003f

def z362 : W := mkw 0x00019400d6d00d80 0x14000650035b4036 0x04038c00fff00fed 0x94100e3003ffc03f

def z363 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xe7fb0fff00000014 0x0b9fec3ffc000000

def z364 : W := mkw 0xdfd8000062626000 0x477f600001898980 0xfff80000f070701f 0x43ffe00003c1c1c0

def z365 : W := mkw 0x0008000000202000 0x0000200000008080 0x0498000080707004 0x001260000201c1c0

def z366 : W := mkw 0x0940208800000000 0x0025008220000000 0x036003cc00000010 0x080d800f30000000

def z367 : W := mkw 0x9d60fc8c4fd9048c 0x1e7583f2313f6412 0x1c60fc0c0ff00008 0x507183f0303fc000

def z368 : W := mkw 0x002884050c38240a 0x0000a2101430e090 0x04fb8e3f0c70003d 0x1813ee38fc31c000

def z369 : W := mkw 0x0961b2dcbd8fdffc 0x282586cb72f63f7f 0x1b64f3ccff8ffffb 0xfc6d93cf33fe3fff

def z370 : W := mkw 0x4280000020024000 0x010a000000800900 0xe0800000f0007004 0x0382000003c001c0

def z371 : W := mkw 0x000002502006d270 0x2000000940801b49 0x00000000000ff000 0x0000000000003fc0

def z372 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0x1c07fc000ff00fe8 0x70701ff0003fc03f

def z373 : W := mkw 0xffd679ea018180c4 0x0bff59e7a8060603 0xfb0471c0038381c2 0x67ec11c7000e0e07

def z374 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1864f3cc0f800fe8 0x786193cf303e003f

def z375 : W := mkw 0x0000000042400000 0x0400000001090000 0x00000000fff00000 0x8400000003ffc000

def z376 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc03fc00fff0000c 0x53f00ff003ffc000

def z377 : W := mkw 0x00200244090d824c 0x0800800910243609 0x00000000000f8000 0x0000000000003e00

def z378 : W := mkw 0x20076bfa90049b70 0x20801dafea40126d 0x0007ffff00000fe0 0x38001ffffc00003f

def z379 : W := mkw 0x6bd621aa00000000 0x01af5886a8000000 0xe3ff03ff00000037 0x2b8ffc0ffc000000

def z380 : W := mkw 0xf69f4c00f2726900 0x57da7d3003c9c9a4 0xe49b0c00f0707004 0x03926c3003c1c1c0

def z381 : W := mkw 0x096032cc098d82cc 0x082580cb3026360b 0x1b6473cc038f81d2 0x6c6d91cf300e3e07

def z382 : W := mkw 0x0968b2cc0dada6cc 0x0825a2cb3036b69b 0x1ffcf3cc8fffffff 0xfc7ff3cf323fffff

def z383 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe30401c0f00fffc2 0xa78c100703c03fff

def z384 : W := mkw 0x0001861584141e2a 0x0000061856105078 0x04038e3f8c700e2d 0x98100e38fe31c038

def z385 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x036003cc0f8f8fd0 0x8c0d800f303e3e3f

def z386 : W := mkw 0x0008040100302002 0x000020100400c080 0x04180c0300700000 0x001060300c01c000

def z387 : W := mkw 0x0000100052c00180 0x14000040014b0006 0x00000000738001c0 0x0400000001ce0007

def z388 : W := mkw 0xf6974b72b006db70 0x23da5d2dcac01b6d 0xe79f0ff3f00ffff7 0xaf9e7c3fcfc03fff

def z389 : W := mkw 0x62af0370fb6ffb70 0x658abc0dc3edbfed 0xe38703f0fffffff7 0xaf8e1c0fc3ffffff

def z390 : W := mkw 0x0020000008080000 0x0000800000202000 0x006000000c0c0019 0x8001800000303000

def z391 : W := mkw 0x2007840094100d00 0x00801e1002504034 0xe4078c00fc700fef 0xb7901e3003f1c03f

def z392 : W := mkw 0x0969b6dd8dbdbeee 0x0825a6db7636f6fb 0x1b64f3cc8ffffffb 0xfc6d93cf323fffff

def z393 : W := mkw 0x9400000042400000 0x0650000001090000 0xe4000000f0700004 0x0390000003c1c000

def z394 : W := mkw 0x0960b08c0d89048c 0x082582c230362412 0x1864f00c0f800feb 0xf46193c0303e003f

def z395 : W := mkw 0x000021aa00000000 0x00000086a8000000 0x000003ff00000000 0x0800000ffc000000

def z396 : W := mkw 0x42810370b006db70 0x210a040dc2c01b6d 0x038003f0f00fffd0 0x8c0e000fc3c03fff

def z397 : W := mkw 0xb407dc0094900d80 0x12d01f7002524036 0xfc07fc0000000fef 0x73f01ff00000003f

def z398 : W := mkw 0x200669aa00000000 0x008019a6a8000000 0x04ffffff0000003d 0x3813fffffc000000

def z399 : W := mkw 0x42a98615ac3e7e2a 0x010aa61856b0f9f8 0xe7fb8e3ffc7ffe3f 0x9f9fee38fff1fff8

def z400 : W := mkw 0xfffffdaafffb6d80 0x57fffff6abffedb6 0xffffffffffffffff 0xffffffffffffffff

def z401 : W := mkw 0x9d78688a4b692000 0x4675e1a2292da480 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z402 : W := mkw 0xdff830c86bebe0c4 0x4f7fe0c321afaf83 0xfffc71c0fffff1df 0xe7fff1c703ffffc7

def z403 : W := mkw 0x002092440d8d86cc 0x080082491036361b 0x0060820c0f8f8ff9 0x9c018208303e3e3f

def z404 : W := mkw 0xdff986158c3c3e2a 0x037fe6185630f0f8 0xfffb8e3f8c7c7e3f 0xdbffee38fe31f1f8

def z405 : W := mkw 0x00219254bd8fdffc 0x2800864952f63f7f 0x00000000ff8fffc0 0x8400000003fe3fff

def z406 : W := mkw 0xb4074c00d2500900 0x16d01d3003494024 0xfc07fc00f070002f 0x73f01ff003c1c000

def z407 : W := mkw 0xdff8dc006ffb6480 0x577fe37001bfed92 0xfff8fc00fffff01f 0xd7ffe3f003ffffc0

def z408 : W := mkw 0x9d798615cf7d3e2a 0x4675e618573df4f8 0x1cfb8e3f8ffc7e3d 0xd873ee38fe3ff1f8

def z409 : W := mkw 0xfffe69aa6b6b6000 0x47fff9a6a9adad80 0xfffc71c0fffff01f 0xe7fff1c703ffffc0

def z410 : W := mkw 0x00299615defc3faa 0x1400a658577bf0fe 0x04fb8e3ffffc7ffd 0x9c13ee38fffff1ff

def z411 : W := mkw 0xb406d80004800480 0x02d01b6000120012 0xfc07fc000f800fef 0xf7f01ff0003e003f

def z412 : W := mkw 0x0001021080041a20 0x0000040842001068 0x04fb8e3f800c7e3d 0x9813ee38fe0031f8

def z413 : W := mkw 0xbd66facc0d8d86cc 0x0af59beb3036361b 0xff67ffcc0f8f8fff 0xfffd9fff303e3e3f

def z414 : W := mkw 0x000002150004122a 0x0000000854001048 0x0000023f00000000 0x08000008fc000000

def z415 : W := mkw 0x0008000062626000 0x4400200001898980 0x00000000f0707000 0x0000000003c1c1c0

def z416 : W := mkw 0x4bf98615ad3f7e2a 0x412fe61856b4fdf8 0x07fb8e3f8c7ffe3d 0x981fee38fe31fff8

def z417 : W := mkw 0x2966fbee0d8d86cc 0x08a59befb836361b 0x1b67ffff0f8f8ffb 0xfc6d9ffffc3e3e3f

def z418 : W := mkw 0x096822dd092db26e 0x0825a08b7424b6c9 0x03f803ff000ff010 0x080fe00ffc003fc0

def z419 : W := mkw 0xfff669aa09090000 0x03ffd9a6a8242400 0xffffffff0f8f803f 0xfffffffffc3e3e00

def z420 : W := mkw 0xf687dd20d6d00d80 0x17da1f74835b4036 0xff87fff0fff00fff 0xfffe1fffc3ffc03f

def z421 : W := mkw 0xb406480042400000 0x06d0192001090000 0xfc07fc00fff0002f 0xf7f01ff003ffc000

def z422 : W := mkw 0x0020000009090000 0x0000800000242400 0x000000000f8f8000 0x84000000003e3e00

def z423 : W := mkw 0xbd56688a00000000 0x02f559a228000000 0xfc7ffc0f0000002f 0x73f1fff03c000000

def z424 : W := mkw 0xf69f0130f2627930 0x67da7c04c3c989e4 0xe49b0030f0707004 0x03926c00c3c1c1c0

def z425 : W := mkw 0x0020b2cc0c8c86cc 0x080082cb3032321b 0x0064f3cc0c0c0ff9 0xb80193cf3030303f

def z426 : W := mkw 0xfffefbee6fefe6cc 0x4ffffbefb9bfbf9b 0xffffffffffffffff 0xffffffffffffffff

def z427 : W := mkw 0xbd6ffedddffdbfee 0x1ef5bffb777ff6ff 0xffffffffffffffff 0xffffffffffffffff

def z428 : W := mkw 0x6286012000000000 0x018a180480000000 0xe7ff8fff0000003f 0x3b9ffe3ffc000000

def z429 : W := mkw 0xf696492200000000 0x03da592488000000 0xe79f0ff300000037 0x2b9e7c3fcc000000

def z430 : W := mkw 0xffff0000fb6b6900 0x47fffc0003edada4 0xffff0000ffffffff 0xe7fffc0003ffffff

def z431 : W := mkw 0xdff000006b4b4000 0x477fc00001ad2d00 0xfb6000007f8f801b 0xc7ed800001fe3e00

def z432 : W := mkw 0x6bc733f8b187dbf4 0x29af1ccfe2c61f6f 0xfb8773f0f38ffff7 0xefee1dcfc3ce3fff

def z433 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38303f0f00ff014 0x0b8e0c0fc3c03fc0

def z434 : W := mkw 0x0968b48d0db9248e 0x0825a2d23436e492 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z435 : W := mkw 0x0008001100203022 0x00002000440080c0 0x0098003300007000 0x00026000cc0001c0

def z436 : W := mkw 0xdff98615ef7f7e2a 0x477fe61857bdfdf8 0xfff80000fffffe1f 0xc7ffe00003fffff8

def z437 : W := mkw 0xf696492200000000 0x03da592488000000 0xfc9ffc330000002f 0x73f27ff0cc000000

def z438 : W := mkw 0x00290250fb6ffb70 0x6400a40943edbfed 0x00000000ffffffc0 0x8400000003ffffff

def z439 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xe7f80000f07ff014 0x039fe00003c1ffc0

def z440 : W := mkw 0x9d7800006b6b6000 0x4675e00001adad80 0x1c780000fffff008 0xc471e00003ffffc0

def z441 : W := mkw 0x62878770b416df70 0x218a1e1dc2d05b7d 0xe7878ff0fc7fffff 0xbf9e1e3fc3f1ffff

def z442 : W := mkw 0xdff890006feb6480 0x477fe24001bfad92 0xfffcf000ffffffff 0xf7fff3c003ffffff

def z443 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1860f00c0f8f8fc8 0xd46183c0303e3e3f

def z444 : W := mkw 0x62876bfab006db70 0x218a1dafeac01b6d 0xe387fffff00ffff7 0xbf8e1fffffc03fff

def z445 : W := mkw 0x9d50688a00000000 0x027541a228000000 0x1cfbfe3f0000003d 0x5873eff8fc000000

def z446 : W := mkw 0xfffe69aa292b6000 0x43fff9a6a8a4ad80 0xffffffff000ff03f 0x7bfffffffc003fc0

def z447 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfb64f3cc0000003b 0x7bed93cf30000000

def z448 : W := mkw 0xb4070000d2400900 0x06d01c0003490024 0xfc070000fff00fef 0xe7f01c0003ffc03f

def z449 : W := mkw 0x62a78374bc0edf78 0x218a9e0dd2f03b7d 0xe3e783fcfc0fffff 0xbf8f9e0ff3f03fff

def z450 : W := mkw 0xf6870370f246db70 0x27da1c0dc3c91b6d 0xff8703f0ffffffff 0xeffe1c0fc3ffffff

def z451 : W := mkw 0x0001861584141e2a 0x0000061856105078 0x04fb8e3f00000e3d 0x1813ee38fc000038

def z452 : W := mkw 0x2006016010008150 0x2080180580400205 0x000401c0000001c0 0x2000100700000007

def z453 : W := mkw 0x000000403002c150 0x2000000100c00b05 0x00000000700381c0 0x0400000001c00e07

def z454 : W := mkw 0xfffe58007beb6180 0x57fff96001efad86 0xfffc7000fffff1df 0xe7fff1c003ffffc7

def z455 : W := mkw 0x2007dc0094900d80 0x10801f7002524036 0x1807fc000f800feb 0xf4601ff0003e003f

def z456 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000000f0000007 0x8780000003c00000

def z457 : W := mkw 0x4280000020024000 0x010a000000800900 0x03800000000ff010 0x000e000000003fc0

def z458 : W := mkw 0x096022cc090d824c 0x0825808b30243609 0x036403cc000f8ff3 0xac0d900f30003e3f

def z459 : W := mkw 0x0020b2cc0d8d86cc 0x080082cb3036361b 0x0004f3cc0f8f8fe0 0xbc0013cf303e3e3f

def z460 : W := mkw 0xf69e492262626000 0x47da792489898980 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z461 : W := mkw 0x0001021080041a20 0x0000040842001068 0x0003023000000e20 0x08000c08c0000038

def z462 : W := mkw 0x62870000b0024900 0x018a1c0002c00924 0xe3870000f00ffff7 0xa78e1c0003c03fff

def z463 : W := mkw 0x4bf80000292b6000 0x412fe00000a4ad80 0x1bf800000f8ff01b 0xc46fe000003e3fc0

def z464 : W := mkw 0xffffefbfef7f7e2a 0x47ffffbeffbdfdf8 0xfffffffffffffe3f 0xfffffffffffffff8

def z465 : W := mkw 0x4bf8b2cc2dafe6cc 0x492fe2cb30b6bf9b 0x1bfcf3cc0f8ffffb 0xfc6ff3cf303e3fff

def z466 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfffb8e3ffffff03f 0xdfffee38ffffffc0

def z467 : W := mkw 0x002984058c382c0a 0x0000a6101630e0b0 0x047b8c0f8c700e2d 0x9011ee303e31c038

def z468 : W := mkw 0xffd669ea3002c150 0x23ff59a7a8c00b05 0xfb0471c0700381c2 0x67ec11c701c00e07

def z469 : W := mkw 0x00010250b006db70 0x2000040942c01b6d 0x00830230f00ffff5 0x8c020c08c3c03fff

def z470 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe08703f0f0007fe4 0x2b821c0fc3c001ff

def z471 : W := mkw 0xb42fdc05def82d8a 0x16d0bf70177be0b6 0xfc7ffc0ffff00fef 0xf7f1fff03fffc03f

def z472 : W := mkw 0x0001025090049b70 0x200004094240126d 0x0000000000000fc0 0x000000000000003f

def z473 : W := mkw 0xb4075c00d2d00980 0x16d01d70034b4026 0xfc077c00f3f001c6 0x67f01df003cfc007

def z474 : W := mkw 0xffd679aa52c00180 0x17ff59e6a94b0006 0xffffffff738001ff 0x7ffffffffdce0007

def z475 : W := mkw 0x2007024090048b40 0x00801c090240122d 0xe30703c0f00f8ff7 0xaf8c1c0f03c03e3f

def z476 : W := mkw 0xdfd0208800000000 0x037f408220000000 0xfffcf3cc0000003f 0x7bfff3cf30000000

def z477 : W := mkw 0x002082040c0c0608 0x0000820810303018 0x04fb8e3f0c0c0e3d 0x9813ee38fc303038

def z478 : W := mkw 0x9400000042400000 0x0650000001090000 0x1c0000000ff00008 0x40700000003fc000

def z479 : W := mkw 0xffd7fdaa94900d80 0x13ff5ff6aa524036 0xffffffff00000fff 0x7bfffffffc00003f

def z480 : W := mkw 0x0968000009292000 0x0025a0000024a480 0x1ff800008ffff01f 0xc47fe000023fffc0

def z481 : W := mkw 0x4280012000000000 0x010a000480000000 0x038003f000000010 0x080e000fc0000000

def z482 : W := mkw 0x096090000d890480 0x0025824000362412 0x1b64f0000f8f8ffb 0xf46d93c0003e3e3f

def z483 : W := mkw 0xb407fdaad6d00d80 0x16d01ff6ab5b4036 0xfc07fffffff00fef 0xfff01fffffffc03f

def z484 : W := mkw 0xd6b98615ee7e7e2a 0x475ae61857b9f9f8 0xe4fb8e3ffc7c7e3d 0x9b93ee38fff1f1f8

def z485 : W := mkw 0x62870330b0065b30 0x218a1c0cc2c0196c 0xe0830230f00c7e35 0x8b820c08c3c031f8

def z486 : W := mkw 0x00290615883c3a2a 0x0000a4185620f0e8 0x04fb0e3f807c7014 0x0813ec38fe01f1c0

def z487 : W := mkw 0x20079400d6d00d80 0x14801e50035b4036 0xe0070000fff00fe7 0xa7801c0003ffc03f

def z488 : W := mkw 0x0000000000000000 0x0000000000000000 0x0060820c00000039 0x1801820830000000

def z489 : W := mkw 0x0001001080001820 0x0000040042000060 0x0083003080007004 0x00020c00c20001c0

def z490 : W := mkw 0x002800050828200a 0x0000a0001420a080 0x0078000f00000000 0x0001e0003c000000

def z491 : W := mkw 0xffd669aa63434000 0x47ff59a6a98d0d00 0xffffffff7383803f 0x7ffffffffdce0e00

def z492 : W := mkw 0x0969b69d8dbd3eae 0x0825a6da7636f4fa 0x1cfbfe3f8ffc7e3d 0xd873eff8fe3ff1f8

def z493 : W := mkw 0x00010010b0025930 0x2000040042c00964 0x00000000f0007000 0x0000000003c001c0

def z494 : W := mkw 0x9400000000000000 0x0250000000000000 0xfc0000000000000f 0x43f0000000000000

def z495 : W := mkw 0x62af8775bc3eff7a 0x218abe1dd6f0fbfd 0xe38703f0fc7ffff7 0xaf8e1c0fc3f1ffff

def z496 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x0060820c8c7c7e39 0x980182083231f1f8

def z497 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xff7800007ff3800a 0x47fde00001ffce00

def z498 : W := mkw 0xdff8000008282000 0x037fe0000020a080 0xfff800008c7c701f 0xc3ffe0000231f1c0

def z499 : W := mkw 0x096082040d0d0608 0x0025820810343418 0x1b60820c0f8f8e3b 0xdc6d8208303e3e38

def z500 : W := mkw 0x9d78ec8f0c38240a 0x0275e3b23c30e090 0x1c78fc0f0c700008 0x5071e3f03c31c000

def z501 : W := mkw 0x0000000000000000 0x0000000000000000 0x0004000000000fe3 0xa40010000000003f

def z502 : W := mkw 0xdff822cc6b6fe24c 0x4f7fe08b31adbf89 0xfff803ccfffff01f 0xcfffe00f33ffffc0

def z503 : W := mkw 0xffd6fbee048486cc 0x0bff5befb812121b 0xffffffff00000fff 0x7bfffffffc00003f

def z504 : W := mkw 0x4be0b2cc2d8fc6cc 0x092f82cb30b63f1b 0xfbe4f3ccff8fffff 0xffef93cf33fe3fff

def z505 : W := mkw 0x2007dc00d6d00d80 0x14801f70035b4036 0x0007fc00fff00fe0 0xb4001ff003ffc03f

def z506 : W := mkw 0xf6bfcf378c3c3e2a 0x03daff3cde30f0f8 0xe4fb8e3f8c7c7e3d 0x9b93ee38fe31f1f8

def z507 : W := mkw 0x20070370b006db70 0x20801c0dc2c01b6d 0x000703f0f00fffe0 0xac001c0fc3c03fff

def z508 : W := mkw 0x0001940084900c80 0x0000065002124032 0x1c07fc008ff00fef 0xf4701ff0023fc03f

def z509 : W := mkw 0xb406d80056c00580 0x16d01b60015b0016 0xf804f0007f800feb 0xf7e013c001fe003f

def z510 : W := mkw 0xffffde15ffff7faa 0x57ffff7857fffdfe 0xfffffe3fffffffff 0xfffffff8ffffffff

def z511 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x00fb8e3f000c7e30 0x1803ee38fc0031f8

def z512 : W := mkw 0x4bf800006b6b6000 0x452fe00001adad80 0x03f80000fffff010 0x840fe00003ffffc0

def z513 : W := mkw 0x2007b3fc94849ffc 0x28801ecff252127f 0x0007f3fc00000fe0 0x38001fcff000003f

def z514 : W := mkw 0x002800006b6b6000 0x4400a00001adad80 0x04f80000fffff01d 0x8413e00003ffffc0

def z515 : W := mkw 0x0001861584141e2a 0x0000061856105078 0x00838e3f800c7e35 0x98020e38fe0031f8

def z516 : W := mkw 0x4bf0b3ee0d8d86cc 0x092fc2cfb836361b 0x1bfcf3ff0f8f8ffb 0xfc6ff3cffc3e3e3f

def z517 : W := mkw 0x002082440c0c8648 0x0000820910303219 0x036483cc0c0f8ffb 0xbc0d920f30303e3f

def z518 : W := mkw 0xffffdf70fffffff0 0x77ffff7dc3ffffff 0xfffffff0ffffffff 0xffffffffc3ffffff

def z519 : W := mkw 0x0000000000000000 0x0000000000000000 0x180000000f80000b 0xc4600000003e0000

def z520 : W := mkw 0x4bf9a7bf8c3c3e2a 0x012fe69efe30f0f8 0x07fb8fff8c7c7e3d 0x981fee3ffe31f1f8

def z521 : W := mkw 0x428001602002c050 0x210a000580800b01 0x030001c000038000 0x000c000700000e00

def z522 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfffc71c00000001f 0x63fff1c700000000

def z523 : W := mkw 0xffd76bba80041a20 0x03ff5daeea001068 0xffffffff800c7e3f 0xfbfffffffe0031f8

def z524 : W := mkw 0x9d50688a00000000 0x027541a228000000 0x1f7cffcf0000003b 0x787df3ff3c000000

def z525 : W := mkw 0x0000100000800080 0x0000004000020002 0x18047000038001c2 0x646011c0000e0007

def z526 : W := mkw 0x200669aa00000000 0x008019a6a8000000 0x000471c000000000 0x200011c700000000

def z527 : W := mkw 0x62870130b0025930 0x218a1c04c2c00964 0xe38703f0f0007037 0x2b8e1c0fc3c001c0

def z528 : W := mkw 0xdff882046f6f6608 0x477fe20811bdbd98 0xfff8820cfffffe3f 0xdfffe20833fffff8

def z529 : W := mkw 0xb407de40d6d48fc0 0x16d01f79035b523f 0xff07ffc0ffff8fff 0xfffc1fff03fffe3f

def z530 : W := mkw 0x62879370b486dff0 0x218a1e4dc2d21b7f 0xfb87f3f0ff8fffff 0xffee1fcfc3fe3fff

def z531 : W := mkw 0x2967b2cc9d8d8fcc 0x08a59ecb3276363f 0xfb67f3ccff8f8fff 0xffed9fcf33fe3e3f

def z532 : W := mkw 0x9d70face0d8d86cc 0x0a75c3eb3836361b 0x1f7cffcf0f8f8ffb 0xfc7df3ff3c3e3e3f

def z533 : W := mkw 0x00280215082c322a 0x0000a0085420b0c8 0x04fb8e3f000c703d 0x1813ee38fc0031c0

def z534 : W := mkw 0xdff821aa6b6b6000 0x477fe086a9adad80 0xfff803fffffff01f 0xcfffe00fffffffc0

def z535 : W := mkw 0xffdf6dbb80303822 0x03ff7db6ee00c0e0 0xffffffff8070703f 0x7bfffffffe01c1c0

def z536 : W := mkw 0x0000208800000000 0x0000008220000000 0x0004f3cc00000020 0x380013cf30000000

def z537 : W := mkw 0x00019650f6d6dff0 0x3400065943db5b7f 0x00000000ffffffc0 0x8400000003ffffff

def z538 : W := mkw 0x2006000010000100 0x0080180000400004 0xe0040000700001c2 0x2780100001c00007

def z539 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0x038703f0000ffff0 0x280e1c0fc0003fff

def z540 : W := mkw 0x00009244048486cc 0x080002491012121b 0x0000000000000fc0 0x000000000000003f

def z541 : W := mkw 0x094030c8018180c4 0x082500c320060603 0x1b64f3cc038381fb 0x7c6d93cf300e0e07

def z542 : W := mkw 0x00219644dfdd8fcc 0x1c008659137f763f 0x00000000ffff8fc0 0x8400000003fffe3f

def z543 : W := mkw 0x0960b0cc0d8984cc 0x082582c330362613 0x1b64f1cc0f8381ca 0x746d93c7303e0e07

def z544 : W := mkw 0x2007fdaa94900d80 0x10801ff6aa524036 0x0007ffff00000fe0 0x38001ffffc00003f

def z545 : W := mkw 0xffff0130fb6b7930 0x67fffc04c3edade4 0xfffb0030fffff01f 0xc7ffec00c3ffffc0

def z546 : W := mkw 0xf69fdc00f6f26d80 0x57da7f7003dbc9b6 0xfc9ffc00fff07fef 0xf7f27ff003ffc1ff

def z547 : W := mkw 0x2007de1594941faa 0x10801f785652507e 0x0007fe3f00000fe0 0x38001ff8fc00003f

def z548 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfcfbfc3f0000000c 0x53f3eff0fc000000

def z549 : W := mkw 0x4bf821aa292b6000 0x412fe086a8a4ad80 0x03f803ff000ff010 0x080fe00ffc003fc0

def z550 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfbf80000738ff012 0x47efe00001ce3fc0

def z551 : W := mkw 0xbd67fc8cdfd90d8c 0x1ef59ff2337f6436 0xfc67fc0cfff00fef 0xf7f19ff033ffc03f

def z552 : W := mkw 0xb407df70d6d49ff0 0x36d01f7dc35b527f 0xfc07fff0fff00fef 0xfff01fffc3ffc03f

def z553 : W := mkw 0xd6990411e2727822 0x475a64104789c9e0 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z554 : W := mkw 0x4bf80215292f722a 0x412fe00854a4bdc8 0x03f8023f000ff010 0x080fe008fc003fc0

def z555 : W := mkw 0xd698000062626000 0x475a600001898980 0xfc980000fff0700f 0xc7f2600003ffc1c0

def z556 : W := mkw 0x628601603002c150 0x218a180580c00b05 0xe38401c0f00ff1d7 0xa78e100703c03fc7

def z557 : W := mkw 0xf69f4d3380303822 0x03da7d34ce00c0e0 0xe49b0c3380707004 0x03926c30ce01c1c0

def z558 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x047b8e3f0c700e28 0x1811ee38fc31c038

def z559 : W := mkw 0x62af87358c3c3e2a 0x018abe1cd630f0f8 0xe7ff8fff8c7c7e3f 0xbb9ffe3ffe31f1f8

def z560 : W := mkw 0x0961b2dc8d8d9eec 0x082586cb7236367b 0x1be7f3fc8f8fffff 0xfc6f9fcff23e3fff

def z561 : W := mkw 0xffd769bab0025930 0x23ff5da6eac00964 0xfffffffff000703f 0x7bffffffffc001c0

def z562 : W := mkw 0xdfd0000020024000 0x037f400000800900 0xfff80000f00ff01f 0xc7ffe00003c03fc0

def z563 : W := mkw 0xdff884056f7b640a 0x477fe21015bded90 0xfff88c0ffffff01f 0xd7ffe2303fffffc0

def z564 : W := mkw 0x9401dc00c6d00c80 0x16500770031b4032 0x1c03fc008ff00e2d 0xd0700ff0023fc038

def z565 : W := mkw 0x628669aa00000000 0x018a19a6a8000000 0xe387ffff00000037 0x3b8e1ffffc000000

def z566 : W := mkw 0xdff0b2cc0d8d86cc 0x0b7fc2cb3036361b 0xfffcf3cc0f8f8fff 0xfffff3cf303e3e3f

def z567 : W := mkw 0x0000020000040200 0x0000000800001008 0x00000200000c0e31 0x8800000800003038

def z568 : W := mkw 0x42810370a006da70 0x210a040dc2801b69 0x038303f0800ffe35 0x880e0c0fc2003ff8

def z569 : W := mkw 0x62a79374bd8fdffc 0x298a9e4dd2f63f7f 0xe38703f0ff8ffff7 0xaf8e1c0fc3fe3fff

def z570 : W := mkw 0x0000800004000400 0x0000020000100010 0x000080000c000e29 0x9000020000300038

def z571 : W := mkw 0x0000900004800480 0x0000024000120012 0x000000000f800fc0 0x84000000003e003f

def z572 : W := mkw 0xffff4c00fb7b6900 0x57fffd3003ededa4 0xfffb0c00fffff01f 0xc7ffec3003ffffc0

def z573 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0x1ff800000ffff018 0x407fe000003fffc0

def z574 : W := mkw 0x9d70f88e0d89048c 0x0a75c3e238362412 0x1c78fc0f0f800008 0x5071e3f03c3e0000

def z575 : W := mkw 0x096022cc090d824c 0x0825808b30243609 0x1b6003cc0f8f801b 0xcc6d800f303e3e00

def z576 : W := mkw 0xdff802156b6f722a 0x477fe00855adbdc8 0xfff8023ffffff01f 0xcfffe008ffffffc0

def z577 : W := mkw 0x0000000000000000 0x0000000000000000 0x03000000000f8013 0x840c000000003e00

def z578 : W := mkw 0x0009061180343a22 0x000024184600d0e8 0x049b0e33807c7e35 0x88126c38ce01f1f8

def z579 : W := mkw 0xffd6f9aa04800480 0x03ff5be6a8120012 0xffffffff0f800fff 0xfffffffffc3e003f

def z580 : W := mkw 0x0009841184303c22 0x000026104610c0f0 0x049b8c338c707e2d 0x90126e30ce31c1f8

def z581 : W := mkw 0xffd66bfa2006d270 0x23ff59afe8801b49 0xffffffff000ff03f 0x7bfffffffc003fc0

def z582 : W := mkw 0xf69f0370f266fb70 0x67da7c0dc3c99bed 0xe79f03f0f07ffff7 0xaf9e7c0fc3c1ffff

def z583 : W := mkw 0x2007021090041b20 0x00801c084240106c 0xe0870230f00c7ff7 0xaf821c08c3c031ff

def z584 : W := mkw 0x9d60b2cc4fcd86cc 0x0e7582cb313f361b 0xff64f3ccffff8fff 0xfffd93cf33fffe3f

def z585 : W := mkw 0x62870170b002d970 0x218a1c05c2c00b65 0xe38701f0f003f1c6 0x278e1c07c3c00fc7

def z586 : W := mkw 0x0961b6cc8d9d8ecc 0x082586db3236763b 0x1f67ffcc8fff8fff 0xfc7d9fff323ffe3f

def z587 : W := mkw 0xb42fce15de7c3f2a 0x16d0bf385779f0fc 0xe4fb8e3ffc7c7e3d 0x9b93ee38fff1f1f8

def z588 : W := mkw 0xdff892446fefe6cc 0x4f7fe24911bfbf9b 0xfff80000ffffffdf 0xc7ffe00003ffffff

def z589 : W := mkw 0x0940208800000000 0x0025008220000000 0x1860f00c00000008 0x506183c030000000

def z590 : W := mkw 0x4bd021aa00000000 0x012f4086a8000000 0x07fb8fff0000003d 0x181fee3ffc000000

def z591 : W := mkw 0x0960000009090000 0x0025800000242400 0x186000000f800008 0x40618000003e0000

def z592 : W := mkw 0x6bd723fab006db70 0x21af5c8feac01b6d 0xe3ff03fff00ffff7 0xaf8ffc0fffc03fff

def z593 : W := mkw 0x6286012030024110 0x218a180480c00904 0xe000000070000000 0x0380000001c00000

def z594 : W := mkw 0x628f0771b036fb72 0x218a3c1dc6c0dbed 0xe79f0ff3f07ffff7 0xaf9e7c3fcfc1ffff

def z595 : W := mkw 0x0940308801810084 0x082500c220060402 0x1800700003800000 0x406001c0000e0000

def z596 : W := mkw 0x00001040018180c4 0x0800004100060603 0x00000000038381c0 0x04000000000e0e07

def z597 : W := mkw 0x6287033080041a20 0x018a1c0cc2001068 0xe38703f0800c7e37 0xab8e1c0fc20031f8

def z598 : W := mkw 0x4280000000000000 0x010a000000000000 0xe380000000000017 0x038e000000000000

def z599 : W := mkw 0x0000b2cc048486cc 0x080002cb3012121b 0x0304f3cc000f8ff3 0xbc0c13cf30003e3f

def z600 : W := mkw 0x62af0375b82efb7a 0x218abc0dd6e0bbed 0xe3ff03fff00ffff7 0xaf8ffc0fffc03fff

def z601 : W := mkw 0xb42fde15defc3faa 0x16d0bf78577bf0fe 0xfc07fc00fffc7fef 0xf7f01ff003fff1ff

def z602 : W := mkw 0xffffffbfdefc3faa 0x17fffffeff7bf0fe 0xfffffffffffc7fff 0xfffffffffffff1ff

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x00038e3f00000020 0x18000e38fc000000

def z604 : W := mkw 0x2006fbee048486cc 0x08801befb812121b 0x0007ffff00000fe0 0x38001ffffc00003f

def z605 : W := mkw 0x002092440d8d86cc 0x080082491036361b 0x1804f0000f8f8feb 0xf46013c0003e3e3f

def z606 : W := mkw 0xbd47fcc8d7d18dc4 0x1ef51ff3235f4637 0xff07fdc0fff38fef 0xf7fc1ff703ffce3f

def z607 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x00038e3f8c7c7e20 0x98000e38fe31f1f8

def z608 : W := mkw 0x942800004a682000 0x0650a0000129a080 0xfcf80000fffc701f 0xc7f3e00003fff1c0

def z609 : W := mkw 0x00010400d2500900 0x1400041003494024 0x00000000f0700000 0x0000000003c1c000

def z610 : W := mkw 0xffd601607343c150 0x67ff580581cd0f05 0xfb0401c0738381c2 0x67ec100701ce0e07

def z611 : W := mkw 0xb406dc0046d00480 0x16d01b70011b4012 0xfc07fc000ff0002f 0x73f01ff0003fc000

def z612 : W := mkw 0x002092440d8d86cc 0x080082491036361b 0x030403c00f8f8ff3 0xac0c100f003e3e3f

def z613 : W := mkw 0x00280000292b6000 0x4000a00000a4ad80 0x00000000000ff000 0x0000000000003fc0

def z614 : W := mkw 0x62879770f6d6dff0 0x358a1e5dc3db5b7f 0xe38703f0fffffff7 0xaf8e1c0fc3ffffff

def z615 : W := mkw 0x000030c8008080c4 0x080000c320020203 0x000471c0000001c0 0x200011c700000007

def z616 : W := mkw 0xb406580052c00180 0x16d01960014b0006 0xfc07fc00738001ef 0x77f01ff001ce0007

def z617 : W := mkw 0x9418000042602000 0x4650600001098080 0x0418000000700000 0x001060000001c000

def z618 : W := mkw 0x6be70370b90fdb70 0x21af9c0dc2e43f6d 0xfbe703f0ff8fffff 0xefef9c0fc3fe3fff

def z619 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x0364f3cc000f8ff0 0x380d93cf30003e3f

def z620 : W := mkw 0x9d50fc8a46d00480 0x167543f2291b4012 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z621 : W := mkw 0x2007900094800d80 0x00801e4002520036 0xf807f000ff800fef 0xf7e01fc003fe003f

def z622 : W := mkw 0xb407feccd6d48fcc 0x1ed01ffb335b523f 0xfc07ffccfff00fef 0xfff01fff33ffc03f

def z623 : W := mkw 0x0950208a00000000 0x0025408228000000 0x0078000f00000000 0x0001e0003c000000

def z624 : W := mkw 0x20070250b006db70 0x20801c0942c01b6d 0xe0070000f00fffe7 0xa7801c0003c03fff

def z625 : W := mkw 0x2007877594149f7a 0x20801e1dd650527d 0x00078fff00000fe0 0x38001e3ffc00003f

def z626 : W := mkw 0xf696492200000000 0x03da592488000000 0xe000000000000000 0x0380000000000000

def z627 : W := mkw 0x4280013020025030 0x210a0004c0800940 0x0080003000007000 0x00020000c00001c0

def z628 : W := mkw 0xffd6492200000000 0x03ff592488000000 0xfffb0c330000001f 0x43ffec30cc000000

def z629 : W := mkw 0x00298655bc3eff7a 0x2000a61956f0fbfd 0x04fb8e3ffc7ffffd 0x9c13ee38fff1ffff

def z630 : W := mkw 0xf6874b70b006db70 0x23da1d2dc2c01b6d 0xff87fff0f00fffff 0xfffe1fffc3c03fff

def z631 : W := mkw 0xfffe48006b6b6000 0x47fff92001adad80 0xfffffc00fffff03f 0xf7fffff003ffffc0

def z632 : W := mkw 0x62870130b0025930 0x218a1c04c2c00964 0xe0870030f0007fe7 0xa7821c00c3c001ff

def z633 : W := mkw 0xffd76daad2500900 0x17ff5db6ab494024 0xfffffffff070003f 0x7bffffffffc1c000

def z634 : W := mkw 0x202fde159cbc3faa 0x1080bf785672f0fe 0x04fffe3f8c7c7ffd 0xb813fff8fe31f1ff

def z635 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xff7cfdcf0000000a 0x73fdf3f73c000000

def z636 : W := mkw 0xffd679aa52c00180 0x17ff59e6a94b0006 0xfb0471c0738001c2 0x67ec11c701ce0007

def z637 : W := mkw 0xb407de10d6d41fa0 0x16d01f78435b507e 0xfc87fe30fffc7fff 0xfff21ff8c3fff1ff

def z638 : W := mkw 0xdfd0000000000000 0x037f400000000000 0xfb00000000000002 0x43ec000000000000

def z639 : W := mkw 0x294669aa00000000 0x00a519a6a8000000 0x1b67ffff0000003b 0x786d9ffffc000000

def z640 : W := mkw 0x9d79ee9f8c3c3e2a 0x0275e7ba7e30f0f8 0x1cfbfe3f8c7c7e3d 0xd873eff8fe31f1f8

def z641 : W := mkw 0x6287012090000900 0x018a1c0482400024 0xe38703f0f0000ff7 0xaf8e1c0fc3c0003f

def z642 : W := mkw 0x628f0531b0327932 0x218a3c14c6c0c9e4 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z643 : W := mkw 0xfffe6bbf082c322a 0x03fff9aefc20b0c8 0xffffffff000c703f 0x7bfffffffc0031c0

def z644 : W := mkw 0x42810210a0065a20 0x010a040842801968 0xe3830230f00ffe37 0x8f8e0c08c3c03ff8

def z645 : W := mkw 0x4bf823bf082c322a 0x012fe08efc20b0c8 0x03f803ff000c7010 0x080fe00ffc0031c0

def z646 : W := mkw 0x096986158d3d3e2a 0x0025a6185634f4f8 0x1ffb8e3f8ffffe3f 0xdc7fee38fe3ffff8

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x040000008c70000d 0x801000000231c000

def z648 : W := mkw 0xdff0b2cc6fcfc6cc 0x4f7fc2cb31bf3f1b 0xfb64f3cc7f8f8ffb 0xffed93cf31fe3e3f

def z649 : W := mkw 0x0940b08804800480 0x002502c220120012 0x1b64f3cc0f800ffb 0xfc6d93cf303e003f

def z650 : W := mkw 0x0000840004100400 0x0000021000104010 0x04008c000c700008 0x101002300031c000

def z651 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfb8773f000000037 0x6bee1dcfc0000000

def z652 : W := mkw 0xb40f4c11d2703922 0x16d03d304749c0e4 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z653 : W := mkw 0x4be00000290b4000 0x012f800000a42d00 0xfbe00000ff8ff01f 0xc7ef800003fe3fc0

def z654 : W := mkw 0xffd7dc00f7d34d80 0x57ff5f7003df4d36 0xff07fc00fff38fef 0xf7fc1ff003ffce3f

def z655 : W := mkw 0xffd7dc00d6d00d80 0x17ff5f70035b4036 0xfffffc00fff00fff 0xf7fffff003ffc03f

def z656 : W := mkw 0x00290215882c3a2a 0x0000a4085620b0e8 0x00fb023f800c7e35 0x8803ec08fe0031f8

def z657 : W := mkw 0xb407cc0084100c00 0x02d01f3002104030 0xfc07fc008c700e2f 0xf3f01ff00231c038

def z658 : W := mkw 0xfff6f9ae0d89048c 0x0bffdbe6b8362412 0xffffffff0f80003f 0x7bfffffffc3e0000

def z659 : W := mkw 0xdfd0000063434000 0x477f4000018d0d00 0xfb800000f38ff017 0xc7ee000003ce3fc0

def z660 : W := mkw 0x2007013090001930 0x20801c04c2400064 0x0003003000000000 0x00000c00c0000000

def z661 : W := mkw 0xdfd0000042400000 0x077f400001090000 0xfff80000fff0001f 0xc7ffe00003ffc000

def z662 : W := mkw 0x002886050c3c260a 0x0000a2181430f098 0x04788e0f0c7c0e39 0x9811e2383c31f038

def z663 : W := mkw 0x0001861084141e20 0x0000061842105078 0x04838e308c7c7e3d 0x98120e38c231f1f8

def z664 : W := mkw 0xb407480090000900 0x02d01d2002400024 0xfc07fc00f0000fef 0xf7f01ff003c0003f

def z665 : W := mkw 0xdff90250fb6ffb70 0x677fe40943edbfed 0xfff80000ffffffdf 0xc7ffe00003ffffff

def z666 : W := mkw 0x00299400fffb6d80 0x5400a65003ffedb6 0x00000000ffffffc0 0x8400000003ffffff

def z667 : W := mkw 0x94018400c6500c00 0x0650061003194030 0xfc038c00fff00e2f 0xd7f00e3003ffc038

def z668 : W := mkw 0xffd70370f347db70 0x67ff5c0dc3cd1f6d 0xfb8703f0f38ffff7 0xefee1c0fc3ce3fff

def z669 : W := mkw 0xb407cc00d6500d00 0x16d01f3003594034 0xe4038c00fc700e2d 0x93900e3003f1c038

def z670 : W := mkw 0xffd679ea018180c4 0x0bff59e7a8060603 0xffffffff038381ff 0x7ffffffffc0e0e07

def z671 : W := mkw 0x00298615ef7f7e2a 0x4400a61857bdfdf8 0x00000000fffffe00 0x8400000003fffff8

def z672 : W := mkw 0x0009041180303822 0x000024104600c0e0 0x0000000080707000 0x000000000201c1c0

def z673 : W := mkw 0x6287037090049b70 0x218a1c0dc240126d 0xe38703f000000ff7 0x2b8e1c0fc000003f

def z674 : W := mkw 0x62870160b002c950 0x218a1c0582c00b25 0xe30701c0f0038fe7 0xa78c1c0703c00e3f

def z675 : W := mkw 0xdff803706b6ff270 0x677fe00dc1adbfc9 0xfff803f0fffff01f 0xcfffe00fc3ffffc0

def z676 : W := mkw 0xdff80000292b6000 0x437fe00000a4ad80 0xfff80000000ff01f 0x43ffe00000003fc0

def z677 : W := mkw 0xfff7fbfebd8fdffc 0x2bffdfeffaf63f7f 0xffffffffff8fffff 0xfffffffffffe3fff

def z678 : W := mkw 0x0000000000000000 0x0000000000000000 0x1804f0000000002b 0x706013c000000000

def z679 : W := mkw 0x0000021000041220 0x0000000840001048 0x00800230000c7010 0x08020008c00031c0

def z680 : W := mkw 0xffd7efbf84141e2a 0x03ff5fbefe105078 0xffffffff00000e3f 0x7bfffffffc000038

def z681 : W := mkw 0x096800006b6b6000 0x4425a00001adad80 0x1b600000fffff01b 0xc46d800003ffffc0

def z682 : W := mkw 0x9400480000000000 0x0250012000000000 0x1c00fc0000000008 0x507003f000000000

def z683 : W := mkw 0x0968b2cc6fefe6cc 0x4c25a2cb31bfbf9b 0x1b64f3ccfffffffb 0xfc6d93cf33ffffff

def z684 : W := mkw 0xdfd0000063434000 0x477f4000018d0d00 0xfff800007383801f 0x47ffe00001ce0e00

def z685 : W := mkw 0xf6afdf75fefefffa 0x37dabf7dd7fbfbff 0xffffffffffffffff 0xffffffffffffffff

def z686 : W := mkw 0x0000000000000000 0x0000000000000000 0x030403c000000033 0x280c100f00000000

def z687 : W := mkw 0x4be023fc290fd27c 0x292f808ff0a43f49 0x03e003fc000ff010 0x080f800ff0003fc0

def z688 : W := mkw 0x62af8735bc3e7f3a 0x218abe1cd6f0f9fc 0xe4fb8e3ffc7c7e3d 0x9b93ee38fff1f1f8

def z689 : W := mkw 0x0000037000049270 0x2000000dc0001249 0x000003f000000000 0x0800000fc0000000

def z690 : W := mkw 0x9401dc00d6d00d80 0x16500770035b4036 0x1c00fc00fff00fc8 0xd47003f003ffc03f

def z691 : W := mkw 0x0000004000008040 0x0000000100000201 0x030401c0000381c2 0x240c100700000e07

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0x04f800000000001d 0x0013e00000000000

def z693 : W := mkw 0xb406580052c00180 0x16d01960014b0006 0xfc047000fff001cf 0xe7f011c003ffc007

def z694 : W := mkw 0x2007efbf84141e2a 0x00801fbefe105078 0x0007ffff00000e20 0x38001ffffc000038

def z695 : W := mkw 0xbd57fc8ad6d00d80 0x16f55ff22b5b4036 0xfc7ffc0ffff00fef 0xf7f1fff03fffc03f

def z696 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe0830030f00fffc4 0x87820c00c3c03fff

def z697 : W := mkw 0x0960b08c0d89048c 0x082582c230362412 0x1b64f3cc0f80003b 0x786d93cf303e0000

def z698 : W := mkw 0x00298655bc3eff7a 0x2000a61956f0fbfd 0x00000000fc7fffc0 0x8400000003f1ffff

def z699 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04f800008c7c7e1d 0x8013e0000231f1f8

def z700 : W := mkw 0x2007fecc94948fcc 0x18801ffb3252523f 0x0007ffcc00000fe0 0x38001fff3000003f

def z701 : W := mkw 0x628603703006d370 0x218a180dc0c01b4d 0xe38403f0700ff1d2 0x2f8e100fc1c03fc7

def z702 : W := mkw 0x2006480000000000 0x0080192000000000 0x0007fc0000000020 0x30001ff000000000

def z703 : W := mkw 0x6286012000000000 0x018a180480000000 0xe30401c000000002 0x238c100700000000

def z704 : W := mkw 0x096030c8098980c4 0x082580c320262603 0x1b6471c00f8f81db 0xe46d91c7003e3e07

def z705 : W := mkw 0x002186048c1c0e08 0x0000861812307038 0x04638e0c8c7c0e3d 0x98118e383231f038

def z706 : W := mkw 0x0000dc0004900480 0x1000037000124012 0x0000fc0000000000 0x100003f000000000

def z707 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b0473c00f8f8ff3 0xec6c11cf003e3e3f

def z708 : W := mkw 0x6be7b1bcbd8b5dbc 0x29af9ec6f2f62d76 0xf8e3f03cff80700c 0x53e38fc0f3fe01c0

def z709 : W := mkw 0xd698b2cc66e6e6cc 0x4f5a62cb319b9b9b 0xe49cf3ccf0707fe4 0x3b9273cf33c1c1ff

def z710 : W := mkw 0x62870770b016db70 0x218a1c1dc2c05b6d 0xe7870ff0f07ffff7 0xaf9e1c3fc3c1ffff

def z711 : W := mkw 0x200669aa00000000 0x008019a6a8000000 0x047fffff00000028 0x3811fffffc000000

def z712 : W := mkw 0xdff801226b6b6000 0x477fe00489adad80 0xfff80033fffff01f 0xc7ffe000cfffffc0

def z713 : W := mkw 0x002986558d3dbe6e 0x0800a6195634f6f9 0x04fb8e3f8c7ffe3d 0x9813ee38fe31fff8

def z714 : W := mkw 0x002986159c3c3f2a 0x0000a6185670f0fc 0x04fb8e3ffc7c7ffd 0x9c13ee38fff1f1ff

def z715 : W := mkw 0x0960b6cd0d9d86ce 0x082582db3436761b 0x1b64ffcf0f8f8ffb 0xfc6d93ff3c3e3e3f

def z716 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38401c0f00fffd7 0xa78e100703c03fff

def z717 : W := mkw 0x002904158838382a 0x0000a4105620e0e0 0x04fb0c3f80707004 0x0013ec30fe01c1c0

def z718 : W := mkw 0x628603703006d370 0x218a180dc0c01b4d 0xe38403f0700ffff3 0xaf8e100fc1c03fff

def z719 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc03fc00fff00fcc 0xd7f00ff003ffc03f

def z720 : W := mkw 0xdff848006b6b6000 0x477fe12001adad80 0xfff8fc00fffff01f 0xd7ffe3f003ffffc0

def z721 : W := mkw 0x096022c8090d8240 0x0025808b20243609 0x1b64f3cc0f8f8ffb 0xfc6d93cf303e3e3f

def z722 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc67fe0cfff00fff 0xfff19ff833ffc03f

def z723 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfcffffff0000002c 0x7bf3fffffc000000

def z724 : W := mkw 0xf6974d32f2525930 0x37da5d34cbc94964 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z725 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfb600000fffff01b 0xc7ed800003ffffc0

def z726 : W := mkw 0x628669aa00000000 0x018a19a6a8000000 0xe7ffffff0000003f 0x3b9ffffffc000000

def z727 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xffffffff8c70003f 0xfbfffffffe31c000

def z728 : W := mkw 0xdff8688a6b6b6000 0x477fe1a229adad80 0xfffcffcffffff03f 0xfffff3ff3fffffc0

def z729 : W := mkw 0x0960b2dd0d8d96ee 0x082582cb7436365b 0x1b64f3ff0f8f8ffb 0xfc6d93cffc3e3e3f

def z730 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b04f3cc0f8f8fe2 0xfc6c13cf303e3e3f

def z731 : W := mkw 0xb406d80046c00480 0x06d01b60011b0012 0xfc07fc00fff00fef 0xf7f01ff003ffc03f

def z732 : W := mkw 0x002996558cbcbeea 0x0000a6595632f2fb 0x1fffffff8fffffff 0xfc7ffffffe3fffff

def z733 : W := mkw 0x4be823fd292ff27e 0x292fa08ff4a4bfc9 0x03f803ff000ff010 0x080fe00ffc003fc0

def z734 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe79f0ff3f00ffff7 0xaf9e7c3fcfc03fff

def z735 : W := mkw 0x2007df7594949ffa 0x30801f7dd652527f 0x0007ffff00000fe0 0x38001ffffc00003f

def z736 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc07fc00fff00fec 0x73f01ff003ffc03f

def z737 : W := mkw 0xdff848026b6b6000 0x477fe12009adad80 0xfff80c03fffff01f 0xc7ffe0300fffffc0

def z738 : W := mkw 0x002882040c2c2608 0x0000a2081030b098 0x04fb8e3f8c7c7e3d 0x9813ee38fe31f1f8

def z739 : W := mkw 0x002092440c8c86c8 0x000082491032321b 0x1b64f3cc0f8f8ffb 0xfc6d93cf303e3e3f

def z740 : W := mkw 0x2007fffc94949ffc 0x38801ffff252527f 0x0007fffc00000fe0 0x38001ffff000003f

def z741 : W := mkw 0x62970372b006db70 0x218a5c0dcac01b6d 0xe39f03f3f00ffff7 0xaf8e7c0fcfc03fff

def z742 : W := mkw 0x00290210882c3a20 0x0000a4084220b0e8 0x04fb8e3f8c7c7e3d 0x9813ee38fe31f1f8

def z743 : W := mkw 0xf69f4932f2627930 0x67da7d24cbc989e4 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z744 : W := mkw 0x094934d981b1b8e6 0x082524d36606c6e3 0x1f9f7df383f3f1c6 0x647e7df7ce0fcfc7

def z745 : W := mkw 0x00299655effffeee 0x4c00a65957bffffb 0x00000000ffffffc0 0x8400000003ffffff

def z746 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b64f3cc0f838fea 0x7c6d93cf303e0e3f

def z747 : W := mkw 0x9400dc0046d00480 0x16500370011b4012 0xfc04fc00fff00fef 0xf7f013f003ffc03f

def z748 : W := mkw 0xffd669aa62424000 0x47ff59a6a9890900 0xffffffff7000003f 0x7bfffffffdc00000

def z749 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe30701c0f00fffe7 0xa78c1c0703c03fff

def z750 : W := mkw 0xb406dc0056d00580 0x16d01b70015b4016 0xfc04fc007ff00feb 0xf7f013f001ffc03f

def z751 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xe7f80000fffff014 0x879fe00003ffffc0

def z752 : W := mkw 0xdff801206b6b6000 0x477fe00481adad80 0xfff803f0fffff01f 0xcfffe00fc3ffffc0

def z753 : W := mkw 0xdff820886b6b6000 0x477fe08221adad80 0xfffffffffffff03f 0xffffffffffffffc0

def z754 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe3878ffff00ffff7 0xbf8e1e3fffc03fff

def z755 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc07fe3ffff00fef 0xfff01ff8ffffc03f

def z756 : W := mkw 0xbd7f0370db6dbb70 0x66f5fc0dc36db6ed 0x1c7f03f00ff00fe8 0x6871fc0fc03fc03f

def z757 : W := mkw 0xb407dc11d6d01da2 0x16d01f70475b4076 0xfc07fc33fff00fef 0xf7f01ff0cfffc03f

def z758 : W := mkw 0x0001861084141e20 0x0000061842105078 0x04fb8e3f8c7c7e3d 0x9813ee38fe31f1f8

def z759 : W := mkw 0x0968b6cd0dbda6ce 0x0825a2db3436f69b 0x1fffffff0fff8fff 0xfc7ffffffc3ffe3f

def z760 : W := mkw 0x6bffdc00bdbb6d80 0x51afff7002f6edb6 0x03fffc00000ffff0 0x300ffff000003fff

def z761 : W := mkw 0x0009041180303822 0x000024104600c0e0 0x04fb0e3f80707014 0x0813ec38fe01c1c0

def z762 : W := mkw 0xd6b800006b6b6000 0x475ae00001adad80 0xe4f80000fffff01d 0x8793e00003ffffc0

def z763 : W := mkw 0xdff820886b6b6000 0x477fe08221adad80 0xfff8f00cfffff01f 0xd7ffe3c033ffffc0

def z764 : W := mkw 0x002996158cbc3eaa 0x0000a6585632f0fa 0x04fb8e3f8ffc7ffd 0x9c13ee38fe3ff1ff

def z765 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xff980000fffff006 0xc7fe600003ffffc0

def z766 : W := mkw 0x002984158c383c2a 0x0000a6105630e0f0 0x04fb8e3f8c70703d 0x1813ee38fe31c1c0

def z767 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xffffffff0f80003f 0xfffffffffc3e0000

def z768 : W := mkw 0x62ae85653c3ae55a 0x218aba1594f0eb95 0xe77c8dcf7c7381ca 0x379df2373df1ce07

def z769 : W := mkw 0x094030c8018180c4 0x082500c320060603 0x1b0471c003838fe3 0xe46c11c7000e0e3f

def z770 : W := mkw 0xd6b800006b6b6000 0x475ae00001adad80 0xfc980000fffff00f 0xc7f2600003ffffc0

def z771 : W := mkw 0xffd669aa62424000 0x07ff59a6a9890900 0xfffffffffffff03f 0xffffffffffffffc0

def z772 : W := mkw 0xf6874d20f2524910 0x37da1d3483c94924 0xe4030c00f0700004 0x03900c3003c1c000

def z773 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xfb87f3f0f00fffff 0xffee1fcfc3c03fff

def z774 : W := mkw 0xbd676eccdb5d8b4c 0x1ef59dbb336d762d 0xe7630fccf07f8014 0x0b9d8c3f33c1fe00

def z775 : W := mkw 0x0968b6cd0dbda6ce 0x0825a2db3436f69b 0x1ffcffcf8fffffff 0xfc7ff3ff3e3fffff

def z776 : W := mkw 0x4bd1b5aad6d00d80 0x152f46d6ab5b4036 0x03f803fffff00fd0 0x8c0fe00fffffc03f

def z777 : W := mkw 0x2007025090049b60 0x00801c094240126d 0xe38703f0f00ffff7 0xaf8e1c0fc3c03fff

def z778 : W := mkw 0xb42e5a155aec33aa 0x16d0b968556bb0ce 0xf8fc723f738c71d2 0x6fe3f1c8fdce31c7

def z779 : W := mkw 0xdff8208a6b6b6000 0x477fe08229adad80 0xfff8000ffffff01f 0xc7ffe0003fffffc0

def z780 : W := mkw 0x202e69aa6b6b6000 0x4480b9a6a9adad80 0x0007fffffffff020 0xbc001fffffffffc0

def z781 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe7878ff0f00fffff 0xbf9e1e3fc3c03fff

def z782 : W := mkw 0x002984158c383c2a 0x0000a6105630e0f0 0x04fb8c3f8c707e2d 0x9013ee30fe31c1f8

def z783 : W := mkw 0x9d78f88e4fe9248c 0x4e75e3e2393fa492 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z784 : W := mkw 0x0940b0c8058184c4 0x082502c320160613 0x1b64f3cc0f838ffb 0xfc6d93cf303e0e3f

def z785 : W := mkw 0x0009841184303c22 0x000026104610c0f0 0x04fb8e3f8c707e3d 0x9813ee38fe31c1f8

def z786 : W := mkw 0x2007977094949ff0 0x30801e5dc252527f 0x000703f000000fe0 0x28001c0fc000003f

def z787 : W := mkw 0x9d78b48d4ff9248e 0x4e75e2d2353fe492 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z788 : W := mkw 0xffd669aa21034000 0x43ff59a6a8840d00 0xffffffff0003803f 0x7bfffffffc000e00

def z789 : W := mkw 0x002986158d3d3e2a 0x0000a6185634f4f8 0x04fb8e3f8ffffe3d 0x9c13ee38fe3ffff8

def z790 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc9ffc33fff00fef 0xf7f27ff0cfffc03f

def z791 : W := mkw 0xffd669aa20024000 0x03ff59a6a8800900 0xffffffff7003803f 0x7ffffffffdc00e00

def z792 : W := mkw 0x0968b2dd0dadb6ee 0x0825a2cb7436b6db 0x1ffcf3ff8fffffff 0xfc7ff3cffe3fffff

def z793 : W := mkw 0xf686492000000000 0x03da192480000000 0xffffffff0000003f 0x7bfffffffc000000

def z794 : W := mkw 0x094032c8018582c4 0x082500cb2006160b 0x1b64f3cc038f8ffb 0xfc6d93cf300e3e3f

def z795 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1f67ffcc0f8f8fff 0xfc7d9fff303e3e3f

def z796 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfff8023ffffff01f 0xcfffe008ffffffc0

def z797 : W := mkw 0x0000b2cc048486cc 0x080002cb3012121b 0x1b04f3cc0f8f8ffb 0xfc6c13cf303e3e3f

def z798 : W := mkw 0x94019400c6d00c80 0x06500650031b4032 0xfc07fc00fff00fef 0xf7f01ff003ffc03f

def z799 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe3ff03fff00ffff7 0xaf8ffc0fffc03fff

def z800 : W := mkw 0xf6b6db660d8d86cc 0x0bdadb6d9836361b 0xe49b0c330f8f8fc4 0x87926c30cc3e3e3f

def z801 : W := mkw 0x0968b6dd0dbdb6ee 0x0825a2db7436f6db 0x1ffcffff0ffffffb 0xfc7ff3fffc3fffff

def z802 : W := mkw 0x002984008c382c00 0x0000a6100230e0b0 0x04fb8e3f8c7c7e3d 0x9813ee38fe31f1f8

def z803 : W := mkw 0x096032c8098d82c4 0x082580cb2026360b 0x1b6473c00f8f8ffb 0xec6d91cf003e3e3f

def z804 : W := mkw 0x002986558c3cbe6a 0x0000a6195630f2f9 0x04fb8e3f8c7ffffd 0x9c13ee38fe31ffff

def z805 : W := mkw 0x4bf823fc292ff27c 0x692fe08ff0a4bfc9 0x03f803fc000ff010 0x080fe00ff0003fc0

def z806 : W := mkw 0xdff820886b6b6000 0x477fe08221adad80 0xfffc71c0fffff01f 0xe7fff1c703ffffc0

def z807 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfffb0230fffff03f 0xcfffec08c3ffffc0

def z808 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38403f0f00fffd2 0xaf8e100fc3c03fff

def z809 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04fb8e3f807c7e34 0x1813ee38fe01f1f8

def z810 : W := mkw 0x6bd669aa00000000 0x01af59a6a8000000 0x07ffffff0000003d 0x381ffffffc000000

def z811 : W := mkw 0x002986558c3cbe6a 0x0000a6195630f2f9 0x07fb8fff8c7ffe3d 0x981fee3ffe31fff8

def z812 : W := mkw 0x002996558dbdbeee 0x0800a6595636f6fb 0x1cfffe3f8fffffff 0xfc73fff8fe3fffff

def z813 : W := mkw 0x00299655bdbffffe 0x2800a65956f6ffff 0x00000000ffffffc0 0x8400000003ffffff

def z814 : W := mkw 0x9d68fc8d4ff9248e 0x1e75a3f2353fe492 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z815 : W := mkw 0xbd5669aa00000000 0x02f559a6a8000000 0x1cffffff0000003d 0x7873fffffc000000

def z816 : W := mkw 0xbd5669aa00000000 0x02f559a6a8000000 0x1f7fffff0000003b 0x787dfffffc000000

def z817 : W := mkw 0x0009861584343e2a 0x000026185610d0f8 0x04fb8e3f80707e3d 0x1813ee38fe01c1f8

def z818 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xff780000fffff00a 0xc7fde00003ffffc0

def z819 : W := mkw 0xffd669aa20024000 0x03ff59a6a8800900 0xfffffffff000703f 0x7bffffffffc001c0

def z820 : W := mkw 0xd680df7066d6d6f0 0x375a037dc19b5b5b 0x1f80fff00ffff018 0x587e03ffc03fffc0

def z821 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc077c00fff00fc6 0xe7f01df003ffc03f

def z822 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xff07fc00ffff8fff 0xf7fc1ff003fffe3f

def z823 : W := mkw 0x42a800006b6b6000 0x450aa00001adad80 0xe0800000fffff004 0x8782000003ffffc0

def z824 : W := mkw 0xd6a800006b6b6000 0x475aa00001adad80 0xff800000fffff01f 0xc7fe000003ffffc0

def z825 : W := mkw 0x0009041180303822 0x000024104600c0e0 0x04fb8c3f8070700c 0x1013ee30fe01c1c0

def z826 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfff88c0ffffff01f 0xd7ffe2303fffffc0

def z827 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe7ff03f0f00fffff 0xaf9ffc0fc3c03fff

def z828 : W := mkw 0xffffefbf8c3c3e2a 0x03ffffbefe30f0f8 0xfb0471c08c7c7e02 0xe3ec11c70231f1f8

def z829 : W := mkw 0xb40669aa00000000 0x02d019a6a8000000 0xfcffffff0000003f 0x7bf3fffffc000000

def z830 : W := mkw 0x942800006b6b6000 0x4650a00001adad80 0xf8000000fffff002 0xc7e0000003ffffc0

def z831 : W := mkw 0xd698000062626000 0x475a600001898980 0xff980000fffff01f 0xc7fe600003ffffc0

def z832 : W := mkw 0x0940b0c8058184c4 0x082502c320160613 0x1b04f1c003838fe2 0x746c13c7000e0e3f

def z833 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04ff8e3f8c7c7fff 0xbc13fe38fe31f1ff

def z834 : W := mkw 0xb417dc02d6d00d80 0x16d05f700b5b4036 0xfc1ffc03fff00fef 0xf7f07ff00fffc03f

def z835 : W := mkw 0x9d6800006b6b6000 0x4675a00001adad80 0xff600000fffff01f 0xc7fd800003ffffc0

def z836 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfffb8c00fffff03f 0xd7ffee3003ffffc0

def z837 : W := mkw 0x0978b2cc0dada6cc 0x4825e2cb3036b69b 0x1b7cf3cc0f8f8ffb 0xfc6df3cf303e3e3f

def z838 : W := mkw 0xffd679ea72c2c1d0 0x37ff59e7a9cb0b07 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z839 : W := mkw 0x9d516adab006db70 0x227545ab6ac01b6d 0x1c78fc0ff00fffc8 0xd471e3f03fc03fff

def z840 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe30703f0f00fffe2 0xaf8c1c0fc3c03fff

def z841 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x07ff8fff8c7c7e3f 0xb81ffe3ffe31f1f8

def z842 : W := mkw 0x4bf800006b6b6000 0x452fe00001adad80 0xe3f80000fffff017 0x878fe00003ffffc0

def z843 : W := mkw 0x4be800006b6b6000 0x452fa00001adad80 0xfbe00000fffff01f 0xc7ef800003ffffc0

def z844 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x1cfffe3f8c7c7e3f 0xf873fff8fe31f1f8

def z845 : W := mkw 0xffd669aa62424000 0x47ff59a6a9890900 0xfb0471c070000002 0x63ec11c701c00000

def z846 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc7ffc0ffff00fef 0xf7f1fff03fffc03f

def z847 : W := mkw 0x002800006b6b6000 0x4400a00001adad80 0xe0000000fffff007 0x8780000003ffffc0

def z848 : W := mkw 0x00290615883c3a2a 0x0000a4185620f0e8 0x04fb0e3f8c7c701d 0x8813ec38fe31f1c0

def z849 : W := mkw 0x0940b0c8058184c4 0x082502c320160613 0x1b0471c00f838fc2 0xe46c11c7003e0e3f

def z850 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xff000000fffff00f 0xc7fc000003ffffc0

def z851 : W := mkw 0x42810250a006da60 0x010a040942801b69 0xe38703f0f00ffff7 0xaf8e1c0fc3c03fff

def z852 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1be7f3fc0f8f8fff 0xfc6f9fcff03e3e3f

def z853 : W := mkw 0x62870375b006db7a 0x218a1c0dd6c01b6d 0xe38703fff00ffff7 0xaf8e1c0fffc03fff

def z854 : W := mkw 0x094032c8018582c4 0x082500cb2006160b 0x1b0471c0038f8fc2 0xe46c11c7000e3e3f

def z855 : W := mkw 0xdff8688a6b6b6000 0x477fe1a229adad80 0xfff87000fffff01f 0xc7ffe1c003ffffc0

def z856 : W := mkw 0x002986559c3cbf7a 0x2000a6195670f2fd 0x04fb8e3f8c7c7ffd 0x9813ee38fe31f1ff

def z857 : W := mkw 0xdff821aa6b6b6000 0x477fe086a9adad80 0xfffb8ffffffff03f 0xdfffee3fffffffc0

def z858 : W := mkw 0x0968b2cc0dada6cc 0x0825a2cb3036b69b 0x1b64f3cc8ffffffb 0xfc6d93cf323fffff

def z859 : W := mkw 0xdfe000006b4b4000 0x077f800001ad2d00 0xffe00000fffff01f 0xc7ff800003ffffc0

def z860 : W := mkw 0x0000208800000000 0x0000008220000000 0x04ffffff0000003d 0x3813fffffc000000

def z861 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc047000fff00fcf 0xe7f011c003ffc03f

def z862 : W := mkw 0x9d78fc8a4ff92480 0x5675e3f2293fe492 0x1c78fc0f0ff00008 0x5071e3f03c3fc000

def z863 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfff8820cfffff03f 0xdfffe20833ffffc0

def z864 : W := mkw 0xd6a800006a6a6000 0x075aa00001a9a980 0xfff80000fffff01f 0xc7ffe00003ffffc0

def z865 : W := mkw 0xf6874930f2425930 0x37da1d24c3c90964 0xe0830030f0007004 0x03820c00c3c001c0

def z866 : W := mkw 0x0008000000202000 0x0000200000008080 0x04fb8e3f8070703d 0x1813ee38fe01c1c0

def z867 : W := mkw 0xf69f4d22f2726900 0x57da7d348bc9c9a4 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z868 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1be4f3cc8f8fffff 0xfc6f93cf323e3fff

def z869 : W := mkw 0x0960b0c80d8984c4 0x082582c320362613 0x1b64f1c00f8f8ffb 0xf46d93c7003e3e3f

def z870 : W := mkw 0x628603602006c240 0x018a180d80801b09 0xe38703f0f00ffff7 0xaf8e1c0fc3c03fff

def z871 : W := mkw 0xbd5669aa00000000 0x02f559a6a8000000 0xfc7fffff0000002f 0x7bf1fffffc000000

def z872 : W := mkw 0x002996159cbc3faa 0x1000a6585672f0fe 0x04fb8e3f8c7c7ffd 0x9813ee38fe31f1ff

def z873 : W := mkw 0x0940b2c8058586c4 0x082502cb2016161b 0x1b04f3c00f8f8ffb 0xfc6c13cf003e3e3f

def z874 : W := mkw 0xdff8208c6b6b600c 0x4f7fe08231adad80 0xfff8000cfffff01f 0xc7ffe00033ffffc0

def z875 : W := mkw 0x942800006b6b6000 0x4650a00001adad80 0xfcf80000fffff01f 0xc7f3e00003ffffc0

def z876 : W := mkw 0x9d78fc8c4ff9248c 0x5e75e3f2313fe492 0x1c78fc0c0ff00008 0x5071e3f0303fc000

def z877 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xf807fc00fff00fe2 0xf7e01ff003ffc03f

def z878 : W := mkw 0x4be80000292b6000 0x012fa00000a4ad80 0xfff80000fffff01f 0xc7ffe00003ffffc0

def z879 : W := mkw 0x428003702006d270 0x210a000dc0801b49 0xe38403f0f00ffff7 0xaf8e100fc3c03fff

def z880 : W := mkw 0xb407dc05d6d00d8a 0x16d01f70175b4036 0xfc07fc0ffff00fef 0xf7f01ff03fffc03f

def z881 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b67ffff0f8f8ffb 0xfc6d9ffffc3e3e3f

def z882 : W := mkw 0x0960b2dc0d8d96ec 0x082582cb7036365b 0x1be4f3fc0f8ffffb 0xfc6f93cff03e3fff

def z883 : W := mkw 0xffd669aa43410000 0x47ff59a6a90d0400 0xffffffff0380003f 0x7bfffffffc0e0000

def z884 : W := mkw 0xdff821aa6b6b6000 0x477fe086a9adad80 0xfffcf3fffffff03f 0xfffff3cfffffffc0

def z885 : W := mkw 0xffd669aa42400000 0x07ff59a6a9090000 0xffffffff7380003f 0x7ffffffffdce0000

def z886 : W := mkw 0xd6b800006b6b6000 0x475ae00001adad80 0xe7980000fffff017 0x879e600003ffffc0

def z887 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xff07ffc0fff00fff 0xfffc1fff03ffc03f

def z888 : W := mkw 0x0970b2ce0d8d86cc 0x0825c2cb3836361b 0x1b7cf3cf0f8f8ffb 0xfc6df3cf3c3e3e3f

def z889 : W := mkw 0x2007fedd94949fee 0x18801ffb7652527f 0x0007ffff00000fe0 0x38001ffffc00003f

def z890 : W := mkw 0xf69669aa00000000 0x03da59a6a8000000 0xe4ffffff0000003d 0x3b93fffffc000000

def z891 : W := mkw 0xffd679ea63c3c0c4 0x4fff59e7a98f0f03 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z892 : W := mkw 0x42a800006b6b6000 0x450aa00001adad80 0xe7f80000fffff01f 0x879fe00003ffffc0

def z893 : W := mkw 0xffd669aa10000100 0x03ff59a6a8400004 0xffffffff700001ff 0x7ffffffffdc00007

def z894 : W := mkw 0x0940b2cc058586cc 0x082502cb3016161b 0x1b64f3cc03838ffb 0x7c6d93cf300e0e3f

def z895 : W := mkw 0xdff821aa6b6b6000 0x477fe086a9adad80 0xfff801c0fffff01f 0xc7ffe00703ffffc0

def z896 : W := mkw 0xb4079000d6c00d80 0x06d01e40035b0036 0xfc07f000fff00fef 0xf7f01fc003ffc03f

def z897 : W := mkw 0x62874b72b006db70 0x218a1d2dcac01b6d 0xe3870ff3f00ffff7 0xaf8e1c3fcfc03fff

def z898 : W := mkw 0x62870120b0024900 0x018a1c0482c00924 0xe38703f0f00ffff7 0xaf8e1c0fc3c03fff

def z899 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfffc03c0fffff03f 0xeffff00f03ffffc0

def z900 : W := mkw 0x20070250b006db70 0x20801c0942c01b6d 0xe30703c0f00ffff7 0xaf8c1c0f03c03fff

def z901 : W := mkw 0xbd46688800000000 0x02f519a220000000 0xffffffff0000003f 0x7bfffffffc000000

def z902 : W := mkw 0x62870771b016db72 0x218a1c1dc6c05b6d 0xe3870ff3f00ffff7 0xaf8e1c3fcfc03fff

def z903 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1f7cffcf0f8f8ffb 0xfc7df3ff3c3e3e3f

def z904 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1f64f3cc8fff8fff 0xfc7d93cf323ffe3f

def z905 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04fb8e3f0c7c7e38 0x1813ee38fc31f1f8

def z906 : W := mkw 0x42a800006b6b6000 0x450aa00001adad80 0xe3000000fffff002 0x878c000003ffffc0

def z907 : W := mkw 0xdfd18615e7575e2a 0x477f4618579d5d78 0xfb038e3f73838e22 0x5fec0e38fdce0e38

def z908 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfffbffff0000001c 0x5bffeffffc000000

def z909 : W := mkw 0xb407dd22d6d00d80 0x16d01f748b5b4036 0xfc07fc33fff00fef 0xf7f01ff0cfffc03f

def z910 : W := mkw 0x2007fffa94949ff0 0x30801fffea52527f 0x0007ffff00000fe0 0x38001ffffc00003f

def z911 : W := mkw 0x9d50688a00000000 0x027541a228000000 0x1fffffff0000003f 0x787ffffffc000000

def z912 : W := mkw 0x0960b6cc0d9d86cc 0x082582db3036761b 0x1f64ffcc0fff8ffb 0xfc7d93ff303ffe3f

def z913 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfffc0000ffffffff 0xe7fff00003ffffff

def z914 : W := mkw 0x94019400d6d00d80 0x16500650035b4036 0xfc04f000fff00fef 0xf7f013c003ffc03f

def z915 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xf804f000fff00feb 0xf7e013c003ffc03f

def z916 : W := mkw 0xffd669aa63434000 0x47ff59a6a98d0d00 0xfffffffffff3803f 0xffffffffffffce00

def z917 : W := mkw 0x0940b2c8048486c0 0x002502cb2012121b 0x1b64f3cc0f8f8ffb 0xfc6d93cf303e3e3f

def z918 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfcfffc00fff00fff 0xf7f3fff003ffc03f

def z919 : W := mkw 0xd6b800006b6b6000 0x475ae00001adad80 0xe0000000fffff000 0x8780000003ffffc0

def z920 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xf8077000fff00fe7 0xe7e01dc003ffc03f

def z921 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x1cfb8e3f8ffc7e3f 0xdc73ee38fe3ff1f8

def z922 : W := mkw 0xdff869aa6b6b6000 0x477fe1a6a9adad80 0xfff8fffffffff01f 0xdfffe3ffffffffc0

def z923 : W := mkw 0x094032c8018582c4 0x082500cb2006160b 0x1b0473c003838fe2 0x6c6c11cf000e0e3f

def z924 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfffb0c33fffff01f 0xc7ffec30cfffffc0

def z925 : W := mkw 0x00009040048084c0 0x0000024100120213 0x1b04f1c00f838feb 0xf46c13c7003e0e3f

def z926 : W := mkw 0x00280215082c322a 0x0000a0085420b0c8 0x04fb8e3f8c7c703d 0x9813ee38fe31f1c0

def z927 : W := mkw 0xffd669aa52400100 0x17ff59a6a9490004 0xffffffff7000003f 0x7bfffffffdc00000

def z928 : W := mkw 0xdfd069aa00000000 0x037f41a6a8000000 0x1ffbffff0000003d 0x587feffffc000000

def z929 : W := mkw 0xffd669aa01010000 0x03ff59a6a8040400 0xffffffff0383803f 0x7ffffffffc0e0e00

def z930 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b64f3cc0f8f8ff8 0x786d93cf303e3e3f

def z931 : W := mkw 0xb4074800d2400900 0x06d01d2003490024 0xfc07fc00fff00fef 0xf7f01ff003ffc03f

def z932 : W := mkw 0x42810370b006db70 0x210a040dc2c01b6d 0xe38003f0f00fffd7 0x8f8e000fc3c03fff

def z933 : W := mkw 0x002996158cbc3eaa 0x0000a6585632f0fa 0x1cfbfe3f8ffc7e3d 0xd873eff8fe3ff1f8

def z934 : W := mkw 0x62874b70b006db70 0x218a1d2dc2c01b6d 0xe387fff0f00ffff7 0xbf8e1fffc3c03fff

def z935 : W := mkw 0xffd669aa30024110 0x23ff59a6a8c00904 0xffffffff7000003f 0x7bfffffffdc00000

def z936 : W := mkw 0x0960b0cc0d8984cc 0x082582c330362613 0x1b64f1cc0f838feb 0xf46d93c7303e0e3f

def z937 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38703f0700ffff2 0x2f8e1c0fc1c03fff

def z938 : W := mkw 0x0968b2dd0dadb6ee 0x0825a2cb7436b6db 0x1b64f3cc0f8ffffb 0xfc6d93cf303e3fff

def z939 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfffffffff000003f 0xffffffffffc00000

def z940 : W := mkw 0xb4075800d2c00980 0x16d01d60034b0026 0xfc077000fff00fef 0xe7f01dc003ffc03f

def z941 : W := mkw 0x0940b2cc058586cc 0x082502cb3016161b 0x1b04f3cc0f838feb 0xfc6c13cf303e0e3f

def z942 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xffffffff00000fff 0xfffffffffc00003f

def z943 : W := mkw 0x0968b2cc0dada6cc 0x0825a2cb3036b69b 0x1fffffff8fffffff 0xfc7ffffffe3fffff

def z944 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38701f0f00fffc6 0xa78e1c07c3c03fff

def z945 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfff80000fffff01c 0x43ffe00003ffffc0

def z946 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xffffffff000f803f 0xfffffffffc003e00

def z947 : W := mkw 0x002092440d8d86cc 0x080082491036361b 0x1b04f3c00f8f8ffb 0xfc6c13cf003e3e3f

def z948 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc07fc007ff00fea 0x77f01ff001ffc03f

def z949 : W := mkw 0x00001240008482c0 0x000000490002120b 0x1b0473c0038f8ff3 0xec6c11cf000e3e3f

def z950 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xe7ffffff00000034 0x3b9ffffffc000000

def z951 : W := mkw 0x942800006b6b6000 0x4650a00001adad80 0xe4000000fffff004 0x8790000003ffffc0

def z952 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe30403c0f00ffff3 0xaf8c100f03c03fff

def z953 : W := mkw 0x4bf822dd292ff26e 0x492fe08b74a4bfc9 0x03f803ff000ff010 0x080fe00ffc003fc0

def z954 : W := mkw 0xffd669ea7343c150 0x67ff59a7a9cd0f05 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z955 : W := mkw 0x0940b2cc058586cc 0x082502cb3016161b 0x1b0471c003838fc2 0x646c11c7000e0e3f

def z956 : W := mkw 0x6bc621a800000000 0x01af1886a0000000 0xffffffff0000003f 0x7bfffffffc000000

def z957 : W := mkw 0x4bd021aa00000000 0x012f4086a8000000 0x1fffffff0000003f 0x787ffffffc000000

def z958 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xfbffffff00000032 0x7beffffffc000000

def z959 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc87fc00fffc7fff 0xf7f21ff003fff1ff

def z960 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1bfcf3ff0f8f8ffb 0xfc6ff3cffc3e3e3f

def z961 : W := mkw 0x002886150c3c362a 0x0000a2185430f0d8 0x04fb8e3f0c7c703d 0x1813ee38fc31f1c0

def z962 : W := mkw 0xf68f4d31f2727932 0x37da3d34c7c9c9e4 0xe49b0c33f0707004 0x03926c30cfc1c1c0

def z963 : W := mkw 0x002986558c3cbe6a 0x0000a6195630f2f9 0x04ff8fff8c7c7ffd 0xb813fe3ffe31f1ff

def z964 : W := mkw 0xb407dd20d6d00d80 0x16d01f74835b4036 0xfc07fff0fff00fef 0xfff01fffc3ffc03f

def z965 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xffffffff800c703f 0xfbfffffffe0031c0

def z966 : W := mkw 0x00290615883c3a2a 0x0000a4185620f0e8 0x04fb0e3f807c7e35 0x8813ec38fe01f1f8

def z967 : W := mkw 0x4bf823fa292ff270 0x612fe08fe8a4bfc9 0x03f803ff000ff010 0x080fe00ffc003fc0

def z968 : W := mkw 0xdfd0208800000000 0x037f408220000000 0xffffffff0000003f 0x7bfffffffc000000

def z969 : W := mkw 0xdff8688a6b6b6000 0x477fe1a229adad80 0xfffbfe3ffffff03f 0xdfffeff8ffffffc0

def z970 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38703f0f00ffff4 0x2b8e1c0fc3c03fff

def z971 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04fb0e3f8c7c7e14 0x8813ec38fe31f1f8

def z972 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc04fc00fff00fca 0xf7f013f003ffc03f

def z973 : W := mkw 0xffd669aa63434000 0x47ff59a6a98d0d00 0xfffffffff38ff03f 0xffffffffffce3fc0

def z974 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04fb8e3f8c707e2c 0x1813ee38fe31c1f8

def z975 : W := mkw 0x096032cc098d82cc 0x082580cb3026360b 0x1b6473cc038f8ff3 0xec6d91cf300e3e3f

def z976 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfcf80000fffff00c 0xc7f3e00003ffffc0

def z977 : W := mkw 0xdff820886b6b6000 0x477fe08221adad80 0xfff803ccfffff01f 0xcfffe00f33ffffc0

def z978 : W := mkw 0x002884050c38240a 0x0000a2101430e090 0x04fb8e3f8c7c703d 0x9813ee38fe31f1c0

def z979 : W := mkw 0x002996558dbdbeee 0x0800a6595636f6fb 0x07ff8fff8fffffff 0xbc1ffe3ffe3fffff

def z980 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfbf80000fffff012 0xc7efe00003ffffc0

def z981 : W := mkw 0x0968b2cc0dada6cc 0x0825a2cb3036b69b 0x1bfcf3cc0f8ffffb 0xfc6ff3cf303e3fff

def z982 : W := mkw 0x0029041188383822 0x0000a4104620e0e0 0x04fb8e3f8c7c703d 0x9813ee38fe31f1c0

def z983 : W := mkw 0xffd669aa20024000 0x03ff59a6a8800900 0xffffffff000ff03f 0x7bfffffffc003fc0

def z984 : W := mkw 0x9d6800004b692000 0x0675a000012da480 0xfff80000fffff01f 0xc7ffe00003ffffc0

def z985 : W := mkw 0x002984158c383c2a 0x0000a6105630e0f0 0x04fb8c3f8c7c701d 0x9013ee30fe31f1c0

def z986 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xfb8703f0ff8fffff 0xefee1c0fc3fe3fff

def z987 : W := mkw 0x62874f70b016db70 0x318a1d3dc2c05b6d 0xe3870ff0f00ffff7 0xaf8e1c3fc3c03fff

def z988 : W := mkw 0x6bd669aa00000000 0x01af59a6a8000000 0xe3ffffff00000037 0x3b8ffffffc000000

def z989 : W := mkw 0x62870240b006cb40 0x018a1c0902c01b2d 0xe38703c0f00ffff7 0xaf8e1c0f03c03fff

def z990 : W := mkw 0x295669aa00000000 0x00a559a6a8000000 0x007fffff00000020 0x3801fffffc000000

def z991 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b6471c00f8f8fdb 0xe46d91c7003e3e3f

def z992 : W := mkw 0xdfd0000063434000 0x477f4000018d0d00 0xff800000fffff01f 0xc7fe000003ffffc0

def z993 : W := mkw 0x2007b7fd94949ffe 0x28801edff652527f 0x0007ffff00000fe0 0x38001ffffc00003f

def z994 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0xff7fffff0000002a 0x7bfdfffffc000000

def z995 : W := mkw 0x20079400d6d00d80 0x14801e50035b4036 0xf807f000fff00fef 0xf7e01fc003ffc03f

def z996 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0xe4fb8e3ffc7c7e3f 0x9f93ee38fff1f1f8

def z997 : W := mkw 0x9d7800006b6b6000 0x4675e00001adad80 0xfc780000fffff00f 0xc7f1e00003ffffc0

def z998 : W := mkw 0x42810250b006db70 0x210a040942c01b6d 0xe38403c0f00ffff7 0xaf8e100f03c03fff

def z999 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe78703f0fc7fffff 0xaf9e1c0fc3f1ffff

def z1000 : W := mkw 0x62870160b002c950 0x218a1c0582c00b25 0xe38701c0f00ffff7 0xa78e1c0703c03fff

def z1001 : W := mkw 0x0968b2cd0dada6ce 0x0825a2cb3436b69b 0x1b7cf3cf0f8f8ffb 0xfc6df3cf3c3e3e3f

def z1002 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x07fb8e3f8c7ffe3f 0x9c1fee38fe31fff8

def z1003 : W := mkw 0x00290615883c3a2a 0x0000a4185620f0e8 0x04fb8e3f807c703d 0x1813ee38fe01f1c0

def z1004 : W := mkw 0x0960b0880d890480 0x002582c220362412 0x1b64f3cc0f8f8ffb 0xfc6d93cf303e3e3f

def z1005 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b64f1cc0f8f8fca 0xf46d93c7303e3e3f

def z1006 : W := mkw 0xb407dc00d6d00d80 0x16d01f70035b4036 0xfc87fe30fff00fff 0xfff21ff8c3ffc03f

def z1007 : W := mkw 0x0968b6cd0dbda6ce 0x0825a2db3436f69b 0x1b64f3cc0fff8ffb 0xfc6d93cf303ffe3f

def z1008 : W := mkw 0x096092400d8d86c0 0x002582490036361b 0x1b64f3c00f8f8ffb 0xfc6d93cf003e3e3f

def z1009 : W := mkw 0x2007940094900d80 0x00801e5002524036 0xfc07fc00fff00fef 0xf7f01ff003ffc03f

def z1010 : W := mkw 0x628603603006c350 0x218a180d80c01b0d 0xe38403c0f00ffff7 0xaf8e100f03c03fff

def z1011 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfb800000fffff017 0xc7ee000003ffffc0

def z1012 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b04f1c00f8f8feb 0xf46c13c7003e3e3f

def z1013 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04fb8e3f8c7c701c 0x1813ee38fe31f1c0

def z1014 : W := mkw 0x002996158dbd3eae 0x0800a6585636f4fa 0x04fb8e3f8ffc7e3d 0x9813ee38fe3ff1f8

def z1015 : W := mkw 0xb407dd30d6d01db0 0x36d01f74c35b4076 0xfc07fc30fff00fef 0xf7f01ff0c3ffc03f

def z1016 : W := mkw 0x002996158cbc3eaa 0x0000a6585632f0fa 0x04fffe3f8c7c7ffd 0xb813fff8fe31f1ff

def z1017 : W := mkw 0x200669aa00000000 0x008019a6a8000000 0x00ffffff00000030 0x3803fffffc000000

def z1018 : W := mkw 0x2007de5094949ff0 0x30801f794252527f 0x0007fc0000000fe0 0x30001ff00000003f

def z1019 : W := mkw 0x0968b2dd0dadb6ee 0x0825a2cb7436b6db 0x1fffffff0f8fffff 0xfc7ffffffc3e3fff

def z1020 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe3e783fcf00fffff 0xbf8f9e0ff3c03fff

def z1021 : W := mkw 0x00299655fefefffa 0x3400a65957fbfbff 0x00000000ffffffc0 0x8400000003ffffff

def z1022 : W := mkw 0x0968b2cc0dada6cc 0x0825a2cb3036b69b 0x1f7cf3cc0fff8ffb 0xfc7df3cf303ffe3f

def z1023 : W := mkw 0xdff800006b6b6000 0x477fe00001adad80 0xfffcf000fffff03f 0xf7fff3c003ffffc0

def z1024 : W := mkw 0x6bd669aa00000000 0x01af59a6a8000000 0x1bffffff0000003b 0x786ffffffc000000

def z1025 : W := mkw 0xffd669aa42400000 0x07ff59a6a9090000 0xffffffff0ff0003f 0x7bfffffffc3fc000

def z1026 : W := mkw 0xb406d80056c00580 0x16d01b60015b0016 0xfc04f000fff00fef 0xf7f013c003ffc03f

def z1027 : W := mkw 0x002996558cbcbeee 0x0800a6595632f2fb 0x04fb8e3f8c7c7ffd 0x9813ee38fe31f1ff

def z1028 : W := mkw 0x9401dc00d6d00d80 0x16500770035b4036 0xfc00fc00fff00fcf 0xd7f003f003ffc03f

def z1029 : W := mkw 0x4280000062424000 0x050a000001890900 0xe3800000fffff017 0x878e000003ffffc0

def z1030 : W := mkw 0xdff800056b6b600a 0x477fe00015adad80 0xfff8000ffffff01f 0xc7ffe0003fffffc0

def z1031 : W := mkw 0x0009061180343a22 0x000024184600d0e8 0x04fb8e3f807c7e3d 0x9813ee38fe01f1f8

def z1032 : W := mkw 0xffd669aa42400000 0x07ff59a6a9090000 0xfffffffff070003f 0x7bffffffffc1c000

def z1033 : W := mkw 0x002996558cbcbeee 0x0800a6595632f2fb 0x000000008c7c7fc0 0x800000000231f1ff

def z1034 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b64f3cc038f8ff2 0x7c6d93cf300e3e3f

def z1035 : W := mkw 0x002986158c3c3e2a 0x0000a6185630f0f8 0x04fb8c3f8c7c7e0c 0x9013ee30fe31f1f8

def z1036 : W := mkw 0x9400000062424000 0x0650000001890900 0xfc000000fffff00f 0xc7f0000003ffffc0

def z1037 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1ffcf3cc0f8f8fff 0xfc7ff3cf303e3e3f

def z1038 : W := mkw 0xb407dc10d6d01da0 0x16d01f70435b4076 0xfc87fc30fff07fef 0xf7f21ff0c3ffc1ff

def z1039 : W := mkw 0x62870370b006db70 0x218a1c0dc2c01b6d 0xe38303f0f00fffd4 0x8f8e0c0fc3c03fff

def z1040 : W := mkw 0xffd669aa00000000 0x03ff59a6a8000000 0x1fffffff00000038 0x787ffffffc000000

def z1041 : W := mkw 0xdfd0000062424000 0x077f400001890900 0xfff80000fffff01f 0xc7ffe00003ffffc0

def z1042 : W := mkw 0x00299655dffdbfee 0x1c00a659577ff6ff 0x00000000ffffffc0 0x8400000003ffffff

def z1043 : W := mkw 0x0940b2cc058586cc 0x082502cb3016161b 0x1b04f3cc038f8ff3 0xfc6c13cf300e3e3f

def z1044 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0xfb64f3ccff8f8fff 0xffed93cf33fe3e3f

def z1045 : W := mkw 0xf69f4d30f2727930 0x77da7d34c3c9c9e4 0xe49b0c30f0707004 0x03926c30c3c1c1c0

def z1046 : W := mkw 0xffd679aa73c34180 0x57ff59e6a9cf0d06 0xfb0471c0738381c2 0x67ec11c701ce0e07

def z1047 : W := mkw 0x294669aa00000000 0x00a519a6a8000000 0x1fffffff0000003f 0x787ffffffc000000

def z1048 : W := mkw 0x0960b2cc0d8d86cc 0x082582cb3036361b 0x1b6473cc0f8f8fd2 0xec6d91cf303e3e3f

def z1049 : W := mkw 0x4bf823ee292fe24c 0x492fe08fb8a4bf89 0x03f803ff000ff010 0x080fe00ffc003fc0

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z8,z1,z2,z4,z6]),(0,[z9,z0,z7,z1,z2,z4,z6])],[(0,[z0,z10,z7,z11,z1,z2,z4]),(0,[z0,z7,z1,z2,z12,z4,z6]),(0,[z0,z7,z1,z2,z4,z13,z6]),(0,[z7,z1,z2,z4,z6,z14,z15])],[(0,[z0,z7,z1,z2,z16,z4,z6])],[],[(0,[z0,z17,z7,z1,z2,z4,z6]),(0,[z0,z11,z1,z2,z4,z5,z6]),(0,[z0,z7,z1,z18,z2,z4,z6]),(0,[z19,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z20,z4,z6,z21]),(0,[z22,z0,z7,z1,z2,z4,z23]),(0,[z0,z24,z1,z25,z2,z4,z6]),(0,[z0,z7,z26,z1,z2,z4,z6])],[(0,[z0,z7,z1,z27,z2,z4,z6])],[(0,[z0,z7,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z28,z6]),(0,[z0,z7,z1,z29,z2,z4,z6]),(1,[z30,z0,z7,z31,z2,z4]),(0,[z32,z0,z7,z1,z2,z4,z6])],[(1,[z0,z33,z1,z2,z4,z6]),(1,[z0,z7,z34,z2,z4,z6]),(0,[z35,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z36]),(0,[z0,z7,z37,z1,z2,z4,z6])]],
   [[(0,[z38,z0,z7,z1,z2,z4,z6]),(0,[z19,z39,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z40,z2,z4,z6]),(0,[z9,z0,z7,z1,z2,z3,z6]),(0,[z0,z7,z1,z2,z41,z6,z15])],[(0,[z42,z0,z7,z1,z2,z4,z6]),(0,[z7,z11,z1,z2,z43,z4,z6]),(0,[z0,z7,z1,z2,z44,z4,z6]),(0,[z0,z7,z1,z45,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z46]),(0,[z47,z0,z7,z48,z2,z4,z6]),(1,[z0,z49,z1,z2,z5,z6]),(0,[z0,z7,z1,z2,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z6,z50])],[(0,[z0,z17,z1,z2,z4,z6,z51]),(0,[z0,z52,z7,z1,z2,z4,z6]),(0,[z53,z0,z7,z1,z2,z4,z6]),(1,[z54,z0,z1,z2,z4,z55]),(0,[z0,z7,z56,z1,z2,z4,z6])],[(0,[z0,z7,z1,z57,z2,z4,z6]),(0,[z0,z7,z58,z1,z31,z2,z4])],[(0,[z59,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z60,z2,z4,z6]),(0,[z0,z7,z1,z2,z61,z4,z6]),(0,[z62,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z63,z6]),(1,[z64,z7,z1,z2,z4,z6]),(0,[z65,z0,z7,z1,z66,z4,z6])],[(1,[z67,z17,z1,z2,z4,z6]),(0,[z0,z7,z68,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z69]),(0,[z70,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z71,z4,z6]),(0,[z72,z0,z7,z1,z2,z4,z6]),(0,[z0,z73,z7,z1,z2,z4,z6]),(0,[z74,z0,z7,z1,z2,z4,z6]),(0,[z0,z75,z7,z1,z2,z4,z6]),(0,[z0,z76,z7,z1,z2,z4,z6])]],
   [[(0,[z67,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z77,z6]),(0,[z0,z7,z1,z78,z2,z4,z6]),(0,[z0,z7,z1,z79,z2,z4,z6]),(0,[z0,z7,z80,z1,z2,z4,z15])],[(0,[z0,z81,z7,z1,z2,z4,z6]),(0,[z82,z0,z7,z1,z2,z4,z6]),(0,[z22,z0,z83,z1,z2,z4,z6]),(0,[z0,z83,z7,z1,z2,z4,z6]),(0,[z22,z7,z1,z2,z4,z6,z84]),(0,[z0,z7,z1,z2,z4,z6,z85]),(0,[z65,z0,z86,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z87]),(0,[z0,z7,z1,z2,z88,z4,z6])],[(0,[z67,z7,z1,z89,z2,z4,z6]),(0,[z0,z7,z90,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z91]),(0,[z92,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z93,z4,z6]),(0,[z0,z7,z1,z94,z2,z4,z6])],[(0,[z0,z7,z68,z2,z4,z6,z95]),(0,[z96,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z84]),(0,[z0,z7,z1,z2,z4,z6,z97]),(0,[z0,z7,z98,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z99]),(0,[z0,z7,z100,z1,z2,z6,z15]),(0,[z0,z7,z80,z1,z4,z6,z21])],[(0,[z101,z0,z33,z1,z2,z4,z6]),(0,[z0,z102,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z103,z6]),(0,[z22,z0,z7,z1,z104,z4,z6]),(1,[z105,z0,z7,z80,z1,z4]),(0,[z0,z106,z7,z1,z2,z4,z6])],[(0,[z107,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z108,z1,z2,z4,z6])],[(0,[z67,z109,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z110,z4,z6]),(0,[z54,z72,z0,z7,z1,z2,z4]),(0,[z111,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z112,z6]),(0,[z0,z7,z1,z2,z113,z6,z15]),(0,[z0,z7,z114,z1,z2,z4,z6]),(0,[z0,z7,z1,z115,z2,z4,z6]),(1,[z0,z7,z1,z116,z2,z6])]],
   [[(0,[z0,z7,z117,z1,z2,z4,z6]),(0,[z118,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z5,z6,z15]),(0,[z0,z7,z1,z2,z119,z4,z6]),(0,[z0,z7,z120,z1,z2,z4,z6])],[(0,[z101,z0,z7,z89,z2,z4,z6]),(0,[z0,z7,z1,z121,z2,z4,z6]),(1,[z0,z7,z122,z1,z4,z6]),(0,[z0,z7,z123,z1,z2,z4,z6]),(0,[z0,z7,z80,z1,z116,z2,z6])],[(0,[z0,z7,z1,z124,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z125,z6]),(0,[z126,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z127,z2,z4,z6])],[(1,[z128,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z129,z6])],[(0,[z47,z0,z17,z1,z2,z4,z6]),(0,[z130,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z131,z4,z6]),(0,[z0,z7,z132,z1,z2,z6,z133])],[(0,[z19,z7,z1,z2,z43,z4,z6]),(0,[z0,z7,z1,z2,z134,z4,z6]),(0,[z135,z0,z7,z1,z2,z4,z6])],[(0,[z47,z65,z0,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z136]),(0,[z0,z7,z137,z1,z2,z6,z15]),(0,[z0,z7,z138,z1,z2,z4,z6])],[(0,[z0,z139,z7,z1,z2,z4,z6])]],
   [[(0,[z140,z7,z1,z2,z4,z113,z6]),(0,[z0,z7,z1,z2,z3,z4,z6]),(1,[z0,z7,z1,z141,z4,z6]),(0,[z118,z0,z7,z1,z2,z3,z6]),(0,[z0,z7,z1,z2,z4,z142,z6]),(0,[z0,z7,z1,z2,z4,z143,z6]),(0,[z144,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z145,z2,z4,z6]),(0,[z0,z146,z7,z1,z2,z4,z6]),(0,[z0,z7,z147,z1,z2,z4,z6]),(1,[z148,z0,z1,z2,z4,z6]),(0,[z0,z7,z149,z1,z150,z4,z6])],[(0,[z151,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z152,z2,z4,z6]),(0,[z0,z7,z1,z153,z2,z4,z6]),(1,[z0,z7,z1,z153,z4,z21])],[(0,[z0,z154,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z155,z2,z4,z6])],[(0,[z156,z140,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z157,z4,z6]),(0,[z105,z0,z7,z80,z1,z4,z6])],[(0,[z0,z7,z1,z2,z158,z4,z6]),(0,[z159,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z160,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z161]),(0,[z0,z7,z162,z1,z2,z4,z6]),(0,[z0,z7,z1,z104,z2,z4,z6]),(0,[z0,z7,z163,z1,z2,z4,z6]),(0,[z164,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z122,z1,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z55,z6]),(0,[z0,z7,z165,z1,z2,z4,z6])],[(1,[z0,z7,z1,z2,z166,z6]),(1,[z0,z7,z167,z4,z168,z6]),(0,[z0,z7,z169,z1,z2,z6,z170]),(0,[z0,z171,z7,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z172,z2,z4,z6]),(0,[z173,z54,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z174])],[(1,[z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z175]),(0,[z0,z7,z1,z2,z4,z176,z6])],[(0,[z0,z7,z1,z2,z4,z177,z6]),(0,[z0,z7,z1,z2,z178,z4,z6]),(0,[z179,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z180,z6])],[(0,[z0,z7,z1,z181,z2,z4,z6]),(0,[z65,z0,z24,z1,z2,z4,z6]),(0,[z0,z7,z182,z1,z2,z4,z6]),(0,[z0,z7,z80,z1,z2,z4,z6])],[(0,[z183,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z184,z4,z6]),(0,[z0,z7,z1,z2,z4,z185,z6]),(0,[z0,z7,z100,z1,z27,z2,z6]),(0,[z0,z7,z1,z2,z186,z4,z6])],[(0,[z187,z0,z7,z1,z2,z4,z6]),(0,[z0,z188,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z189,z6])],[(0,[z0,z10,z7,z1,z2,z4,z6]),(0,[z190,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z31,z2,z4,z6,z95])],[(0,[z191,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z192,z2,z4,z6]),(0,[z193,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z194]),(0,[z0,z7,z1,z2,z4,z195,z6])]],
   [[(0,[z54,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z196,z4,z6]),(0,[z0,z7,z197,z1,z2,z4,z6])],[(0,[z198,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z199,z1,z2,z4,z6])],[(0,[z0,z7,z169,z1,z200,z2,z6]),(0,[z0,z7,z1,z201,z2,z4,z6])],[(0,[z0,z7,z202,z1,z2,z4,z6]),(0,[z0,z7,z203,z1,z2,z4,z6])],[(0,[z0,z7,z1,z204,z2,z4,z6]),(0,[z0,z7,z1,z205,z2,z4,z6]),(0,[z0,z7,z206,z1,z2,z4,z6]),(0,[z0,z7,z1,z207,z2,z4,z6]),(0,[z0,z7,z1,z208,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z209,z6]),(0,[z7,z11,z1,z89,z2,z4,z6]),(0,[z156,z0,z7,z1,z2,z113,z6]),(0,[z0,z7,z1,z2,z4,z210,z6]),(0,[z0,z211,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z27,z2,z4,z50]),(0,[z0,z7,z1,z212,z2,z4,z6])],[(0,[z101,z0,z7,z1,z2,z4,z6]),(0,[z213,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z27,z2,z6,z133])],[(0,[z22,z67,z7,z1,z2,z4,z6]),(0,[z0,z7,z214,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z215,z4,z6]),(0,[z0,z7,z216,z1,z2,z4,z6])]],
   [[(0,[z217,z0,z7,z89,z2,z4,z6]),(0,[z218,z0,z7,z1,z2,z4,z6])],[(0,[z219,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z220,z1,z2,z4,z6]),(0,[z0,z86,z1,z25,z2,z4,z6]),(0,[z0,z7,z221,z1,z2,z4,z6]),(0,[z105,z0,z7,z1,z2,z4,z21]),(0,[z0,z222,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z223]),(0,[z67,z7,z1,z2,z4,z23,z6]),(0,[z0,z7,z1,z2,z4,z6,z224]),(0,[z225,z0,z7,z1,z2,z4,z6]),(0,[z226,z0,z7,z1,z2,z4,z6])],[(0,[z67,z0,z17,z1,z2,z4,z6]),(0,[z30,z0,z7,z89,z2,z4,z6]),(0,[z0,z7,z227,z1,z2,z4,z6]),(0,[z0,z7,z228,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z229]),(1,[z0,z7,z216,z1,z2,z6])],[(0,[z230,z0,z7,z1,z2,z4,z6]),(0,[z39,z0,z7,z1,z43,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z231]),(0,[z0,z7,z1,z48,z2,z4,z6]),(0,[z0,z7,z1,z232,z2,z4,z6]),(1,[z233,z7,z1,z2,z4,z6])],[(0,[z101,z0,z7,z68,z2,z4,z6]),(0,[z0,z7,z234,z1,z2,z4,z6]),(0,[z235,z0,z7,z1,z2,z4,z6]),(0,[z236,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z237,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z238]),(0,[z0,z7,z239,z1,z2,z4,z6]),(0,[z240,z0,z7,z1,z2,z4,z6]),(0,[z241,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z242,z6])],[(0,[z0,z7,z1,z2,z243,z4,z6]),(0,[z65,z0,z7,z1,z27,z4,z6]),(0,[z0,z86,z7,z1,z66,z4,z6]),(0,[z0,z7,z132,z1,z2,z6,z15])]],
   [[(0,[z0,z7,z1,z2,z244,z4,z6]),(1,[z217,z7,z89,z2,z4,z6]),(0,[z0,z7,z245,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z246,z6]),(0,[z0,z247,z7,z1,z2,z166,z6])],[(0,[z65,z0,z11,z1,z2,z4,z6]),(0,[z248,z0,z7,z1,z2,z4,z6]),(1,[z39,z7,z1,z20,z4,z6]),(0,[z22,z0,z7,z1,z249,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z250]),(0,[z251,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z58,z1,z2,z4,z6]),(0,[z0,z7,z1,z94,z27,z2,z4]),(0,[z0,z7,z252,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z253,z4,z6]),(0,[z0,z7,z254,z1,z2,z4,z6]),(0,[z0,z7,z255,z1,z2,z4,z6]),(0,[z0,z247,z7,z1,z2,z4,z6]),(0,[z256,z0,z7,z1,z2,z4,z6]),(0,[z9,z0,z7,z100,z1,z2,z6]),(0,[z257,z0,z7,z1,z2,z4,z6])],[(0,[z118,z0,z17,z1,z2,z4,z6]),(0,[z258,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z259,z2,z4,z6]),(1,[z0,z1,z2,z4,z142,z6]),(0,[z0,z7,z1,z2,z4,z6,z260])],[],[(0,[z0,z7,z1,z261,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z262]),(0,[z0,z7,z58,z2,z4,z6,z95])],[(0,[z0,z7,z1,z2,z263,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z264])],[(1,[z22,z7,z1,z2,z4,z84]),(0,[z0,z265,z24,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z66,z4,z6]),(0,[z0,z7,z1,z266,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z2,z4,z6,z267]),(0,[z0,z7,z1,z268,z2,z4,z6]),(0,[z72,z0,z7,z1,z2,z4,z84]),(0,[z54,z0,z247,z1,z2,z4,z6]),(0,[z269,z0,z7,z1,z2,z4,z6])],[(1,[z0,z162,z1,z2,z4,z6]),(0,[z0,z247,z1,z2,z4,z6,z51]),(0,[z30,z0,z7,z58,z2,z4,z6]),(0,[z105,z0,z7,z1,z2,z4,z6])],[(0,[z0,z11,z1,z2,z4,z6,z51]),(0,[z270,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z271,z1,z2,z4,z6]),(0,[z65,z64,z7,z1,z2,z4,z6]),(0,[z0,z7,z58,z1,z2,z4,z95])],[(0,[z0,z7,z272,z1,z2,z4,z6])],[(0,[z273,z0,z7,z1,z2,z4,z6]),(0,[z0,z274,z7,z1,z2,z4,z6]),(0,[z275,z0,z7,z1,z2,z4,z6]),(0,[z54,z0,z7,z1,z2,z4,z55]),(0,[z0,z276,z7,z1,z2,z4,z6])],[(0,[z277,z0,z7,z1,z2,z4,z6]),(0,[z22,z54,z0,z7,z1,z2,z4]),(0,[z0,z7,z1,z2,z4,z6,z278]),(0,[z0,z7,z169,z1,z2,z6,z15]),(0,[z0,z7,z1,z279,z2,z4,z6]),(0,[z0,z280,z7,z1,z2,z4,z6])],[(0,[z0,z281,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z282,z2,z4,z6]),(0,[z0,z7,z1,z2,z283,z4,z6]),(0,[z284,z0,z7,z1,z2,z4,z6])]],
   [[(0,[z47,z0,z1,z25,z2,z4,z6]),(0,[z0,z7,z285,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z51]),(0,[z54,z0,z1,z2,z4,z55,z6])],[(0,[z0,z7,z286,z1,z2,z4,z6]),(0,[z287,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z288,z1,z2,z4,z6]),(0,[z289,z0,z7,z1,z2,z4,z6]),(0,[z0,z290,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z291,z6]),(0,[z9,z0,z7,z1,z2,z41,z6])],[],[(0,[z67,z17,z7,z1,z2,z4,z6]),(0,[z0,z292,z7,z1,z2,z4,z6]),(0,[z140,z7,z1,z2,z4,z23,z6]),(0,[z293,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z294,z4,z6]),(0,[z0,z7,z1,z295,z2,z4,z6]),(0,[z0,z7,z1,z296,z2,z4,z6]),(0,[z0,z1,z2,z4,z55,z6,z51]),(0,[z0,z7,z297,z1,z2,z4,z6]),(1,[z0,z7,z1,z2,z298,z4]),(0,[z0,z7,z1,z2,z4,z6,z299])],[(0,[z217,z0,z7,z1,z2,z4,z6])],[(0,[z109,z0,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z41,z4,z15])],[(1,[z0,z52,z1,z2,z4,z6]),(0,[z140,z0,z52,z1,z2,z4,z6]),(0,[z0,z7,z1,z300,z2,z4,z6])]],
   [[(0,[z22,z72,z7,z1,z2,z4,z6]),(0,[z30,z0,z7,z1,z2,z4,z6])],[(1,[z0,z7,z1,z2,z4,z50]),(0,[z0,z7,z1,z27,z2,z6,z15])],[(0,[z67,z101,z7,z1,z2,z4,z6]),(0,[z22,z0,z7,z34,z2,z4,z6]),(0,[z301,z0,z7,z1,z2,z4,z6]),(0,[z0,z49,z7,z1,z2,z4,z6]),(0,[z118,z0,z49,z1,z2,z4,z6]),(0,[z0,z7,z1,z302,z2,z4,z6]),(0,[z0,z7,z303,z1,z2,z4,z6]),(0,[z0,z7,z304,z1,z27,z2,z6])],[(0,[z54,z0,z17,z1,z2,z4,z6]),(0,[z19,z0,z7,z1,z20,z4,z6]),(1,[z0,z305,z1,z2,z4,z6]),(0,[z0,z7,z306,z1,z2,z4,z6]),(0,[z0,z7,z1,z307,z2,z4,z6])],[(0,[z217,z0,z7,z68,z2,z4,z6]),(0,[z39,z0,z308,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z21,z15])],[(0,[z7,z11,z1,z2,z4,z23,z6]),(0,[z0,z7,z1,z2,z309,z4,z6])],[(0,[z0,z7,z1,z2,z4,z310,z6]),(0,[z0,z311,z7,z1,z2,z4,z6]),(0,[z0,z49,z1,z2,z4,z5,z6]),(0,[z0,z7,z312,z1,z2,z4,z6]),(0,[z313,z0,z7,z1,z2,z4,z6])],[(0,[z0,z314,z7,z1,z2,z4,z6]),(0,[z30,z0,z7,z68,z2,z4,z6]),(0,[z0,z7,z1,z20,z2,z4,z6]),(0,[z47,z315,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z316,z6]),(0,[z0,z247,z7,z1,z2,z4,z55]),(0,[z0,z7,z317,z1,z2,z4,z6]),(1,[z0,z7,z1,z2,z41,z15])]],
   [[(0,[z173,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z100,z1,z2,z4,z318])],[(0,[z319,z0,z7,z1,z2,z4,z6]),(0,[z320,z0,z7,z1,z2,z4,z6]),(0,[z22,z0,z7,z1,z2,z4,z15]),(0,[z0,z7,z1,z321,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z322,z6]),(0,[z0,z7,z1,z323,z2,z4,z6]),(0,[z0,z49,z7,z1,z2,z3,z6]),(0,[z30,z0,z7,z1,z2,z4,z95])],[(0,[z0,z17,z1,z25,z2,z4,z6]),(0,[z22,z7,z1,z2,z324,z4,z6]),(0,[z0,z64,z7,z1,z2,z4,z6]),(0,[z0,z325,z7,z1,z2,z4,z6]),(0,[z0,z7,z326,z1,z2,z4,z6]),(0,[z54,z0,z7,z1,z2,z4,z51]),(1,[z0,z7,z169,z200,z2,z6]),(0,[z0,z7,z1,z2,z327,z4,z6])],[(0,[z0,z7,z328,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z329]),(0,[z0,z7,z1,z330,z2,z4,z6]),(0,[z0,z7,z120,z1,z31,z2,z6]),(0,[z0,z331,z7,z1,z2,z4,z6])],[(0,[z332,z0,z7,z1,z2,z4,z6]),(0,[z7,z68,z1,z89,z2,z4,z6]),(0,[z0,z7,z1,z333,z2,z4,z6]),(0,[z0,z7,z1,z2,z324,z4,z6]),(0,[z334,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z335,z2,z4,z6]),(1,[z0,z7,z1,z2,z336,z6]),(0,[z65,z0,z7,z1,z2,z4,z6]),(0,[z30,z0,z7,z1,z31,z2,z4])],[(0,[z0,z7,z1,z2,z4,z337,z6]),(0,[z0,z7,z169,z1,z27,z2,z6]),(0,[z0,z7,z1,z2,z338,z4,z6])]],
   [[(0,[z39,z7,z1,z20,z2,z4,z6]),(0,[z0,z7,z1,z339,z2,z4,z6]),(0,[z0,z7,z1,z2,z340,z4,z6]),(0,[z341,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z166,z6]),(0,[z0,z7,z1,z2,z4,z6,z342]),(0,[z0,z7,z1,z2,z4,z343,z6]),(0,[z233,z0,z7,z1,z2,z4,z6])],[(0,[z65,z0,z7,z1,z25,z4,z6]),(0,[z0,z7,z1,z344,z2,z4,z6])],[(1,[z0,z292,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z4,z6]),(0,[z156,z0,z7,z1,z2,z324,z6]),(0,[z0,z7,z345,z1,z2,z4,z6]),(0,[z0,z7,z346,z1,z2,z4,z6])],[],[(0,[z0,z7,z1,z347,z2,z4,z6])],[(0,[z348,z0,z7,z1,z2,z4,z6]),(0,[z349,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z350,z6])],[(0,[z0,z7,z351,z1,z2,z4,z6])]],
   [[(0,[z352,z0,z7,z1,z2,z4,z6]),(0,[z0,z128,z7,z1,z2,z4,z6]),(0,[z0,z86,z7,z1,z27,z4,z6]),(0,[z0,z7,z353,z1,z2,z4,z6]),(1,[z0,z7,z1,z2,z354,z6])],[(0,[z0,z7,z1,z2,z4,z355,z6]),(0,[z0,z7,z356,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z41,z4,z6])],[],[(0,[z0,z265,z7,z200,z2,z4,z6]),(0,[z0,z7,z1,z357,z2,z4,z6]),(1,[z0,z7,z358,z2,z4,z6]),(1,[z0,z7,z1,z2,z359,z6]),(0,[z0,z7,z1,z2,z4,z6,z360]),(0,[z361,z0,z7,z1,z2,z4,z6])],[(1,[z156,z7,z1,z2,z324,z6]),(0,[z362,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z363,z6]),(0,[z0,z7,z1,z2,z3,z6,z15]),(0,[z0,z7,z1,z2,z364,z4,z6])],[(0,[z365,z0,z7,z1,z2,z4,z6]),(0,[z0,z366,z7,z1,z2,z4,z6]),(0,[z0,z247,z7,z1,z2,z4,z51]),(1,[z0,z7,z149,z150,z4,z6])],[(0,[z140,z0,z7,z1,z2,z113,z6]),(0,[z0,z7,z1,z367,z2,z4,z6]),(0,[z368,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z369,z1,z2,z4,z6])],[(0,[z72,z0,z247,z7,z1,z2,z4]),(0,[z0,z7,z370,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z354,z168,z6]),(0,[z371,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z372,z2,z4,z6]),(0,[z0,z7,z100,z2,z4,z6,z170]),(0,[z0,z7,z137,z1,z2,z4,z21])]],
   [[(0,[z0,z7,z1,z2,z4,z6,z373])],[(0,[z0,z374,z7,z1,z2,z4,z6]),(0,[z375,z0,z7,z1,z2,z4,z6])],[(1,[z101,z7,z68,z2,z4,z6]),(0,[z0,z7,z1,z376,z2,z4,z6]),(0,[z377,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z378,z1,z2,z4,z6]),(0,[z105,z0,z7,z80,z1,z2,z4])],[(0,[z0,z7,z1,z379,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z318]),(0,[z0,z7,z1,z2,z4,z380,z6])],[(0,[z0,z381,z7,z1,z2,z4,z6]),(1,[z0,z382,z1,z2,z4,z6]),(0,[z140,z0,z382,z1,z2,z4,z6]),(0,[z22,z0,z7,z1,z2,z4,z6]),(1,[z0,z7,z383,z2,z4,z6]),(0,[z72,z7,z1,z2,z4,z23,z6]),(0,[z0,z7,z1,z27,z4,z6,z133]),(0,[z384,z0,z7,z1,z2,z4,z6]),(0,[z0,z385,z7,z1,z2,z4,z6])],[(0,[z386,z0,z7,z1,z2,z4,z6]),(0,[z387,z0,z7,z1,z2,z4,z6]),(1,[z0,z7,z207,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z388,z6]),(0,[z0,z7,z1,z389,z2,z4,z6])],[(0,[z0,z0,z7,z1,z2,z4,z6]),(0,[z390,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z391,z1,z2,z4,z6]),(0,[z0,z7,z392,z1,z2,z4,z6]),(0,[z0,z7,z1,z393,z2,z4,z6]),(0,[z0,z1,z2,z4,z142,z168,z6]),(0,[z0,z394,z7,z1,z2,z4,z6]),(0,[z395,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z396,z1,z2,z4,z6]),(0,[z0,z7,z1,z397,z2,z4,z6])],[(0,[z0,z7,z398,z1,z2,z4,z6]),(0,[z0,z7,z399,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z400]),(0,[z0,z7,z1,z401,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z2,z4,z402,z6]),(0,[z0,z7,z89,z2,z4,z6,z95]),(0,[z403,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z404,z6])],[(0,[z405,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z406,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z407,z6]),(0,[z0,z7,z1,z408,z2,z4,z6]),(0,[z0,z7,z132,z1,z27,z4,z6])],[(0,[z0,z11,z24,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z409]),(0,[z0,z265,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z298,z4,z6]),(0,[z0,z410,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z411,z2,z4,z6])],[(0,[z412,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z413,z4,z6])],[(0,[z414,z0,z7,z1,z2,z4,z6]),(0,[z415,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z416,z1,z2,z4,z6]),(0,[z0,z7,z417,z1,z2,z4,z6])],[(0,[z0,z7,z418,z1,z2,z4,z6]),(0,[z0,z17,z24,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z419]),(0,[z0,z7,z1,z2,z4,z420,z6]),(0,[z0,z7,z1,z421,z2,z4,z6])],[(0,[z39,z0,z7,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z24,z1,z2,z4,z6]),(0,[z422,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z423,z4,z6]),(0,[z0,z7,z1,z2,z4,z424,z6])],[(0,[z47,z0,z11,z1,z2,z4,z6]),(0,[z7,z1,z2,z324,z4,z23,z6]),(0,[z425,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z426])],[(0,[z0,z7,z1,z2,z427,z4,z6]),(0,[z0,z7,z428,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z429,z6]),(0,[z0,z7,z1,z2,z4,z6,z430])],[(0,[z0,z7,z1,z2,z431,z4,z6]),(0,[z0,z7,z1,z432,z2,z4,z6]),(0,[z0,z7,z433,z1,z2,z4,z6])],[(0,[z0,z7,z434,z1,z2,z4,z6]),(0,[z435,z0,z7,z1,z2,z4,z6]),(0,[z156,z7,z1,z2,z324,z4,z6]),(0,[z0,z7,z1,z2,z4,z436,z6]),(0,[z0,z7,z1,z2,z4,z437,z6]),(0,[z0,z7,z358,z1,z2,z4,z6]),(0,[z0,z247,z7,z1,z2,z359,z6]),(0,[z438,z0,z7,z1,z2,z4,z6])],[(1,[z72,z7,z1,z2,z4,z23]),(0,[z0,z7,z1,z2,z439,z4,z6]),(0,[z0,z7,z1,z440,z2,z4,z6])],[(0,[z0,z7,z1,z441,z2,z4,z6]),(0,[z0,z305,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z442,z6]),(0,[z0,z443,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z444,z2,z4,z6])],[(0,[z0,z7,z1,z445,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z446])]],
   [[(0,[z0,z7,z1,z2,z4,z447,z6]),(0,[z9,z0,z7,z1,z2,z113,z6]),(0,[z0,z7,z1,z448,z2,z4,z6]),(1,[z7,z1,z2,z4,z6,z14])],[(0,[z0,z7,z1,z449,z2,z4,z6]),(0,[z65,z0,z17,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z450,z6]),(0,[z451,z0,z7,z1,z2,z4,z6])],[],[(0,[z0,z7,z452,z1,z2,z4,z6]),(0,[z453,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z454]),(0,[z0,z7,z455,z1,z2,z4,z6]),(0,[z456,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z457,z1,z2,z4,z6]),(0,[z0,z458,z7,z1,z2,z4,z6]),(0,[z459,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z460,z6])],[(0,[z461,z0,z7,z1,z2,z4,z6]),(0,[z0,z265,z7,z24,z2,z4,z6]),(0,[z0,z7,z462,z1,z2,z4,z6])],[(1,[z0,z86,z1,z25,z4,z6]),(0,[z0,z7,z463,z1,z2,z4,z6]),(0,[z0,z7,z137,z1,z31,z2,z4])],[(0,[z0,z7,z1,z2,z4,z6,z464]),(0,[z0,z1,z25,z2,z66,z4,z6]),(0,[z0,z7,z465,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z43,z4,z6]),(0,[z0,z7,z1,z2,z4,z466,z6]),(0,[z0,z7,z1,z2,z336,z4,z6]),(0,[z72,z0,z7,z1,z2,z4,z23]),(1,[z315,z7,z1,z2,z4,z6]),(0,[z0,z86,z7,z1,z2,z4,z6]),(0,[z0,z7,z167,z1,z2,z4,z6]),(0,[z148,z0,z1,z2,z4,z168,z6]),(0,[z467,z0,z7,z1,z2,z4,z6]),(1,[z0,z7,z100,z2,z6,z170]),(0,[z0,z7,z1,z2,z4,z6,z468])]],
   [[(1,[z0,z7,z1,z2,z466,z6]),(0,[z469,z0,z7,z1,z2,z4,z6]),(0,[z0,z24,z1,z48,z2,z4,z6]),(0,[z0,z7,z470,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z170])],[(0,[z101,z7,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z471,z4,z6]),(0,[z7,z1,z2,z324,z4,z113,z6]),(0,[z47,z0,z265,z1,z2,z4,z6]),(0,[z472,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z473,z2,z4,z6]),(0,[z217,z7,z1,z89,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z474]),(0,[z0,z7,z475,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z476,z4,z6]),(0,[z477,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z478,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z479]),(0,[z0,z7,z137,z1,z2,z41,z4]),(0,[z9,z0,z7,z137,z1,z2,z4])],[(0,[z0,z7,z480,z1,z2,z4,z6]),(0,[z0,z86,z7,z1,z25,z4,z6]),(1,[z118,z0,z1,z2,z3,z6])],[(0,[z22,z7,z11,z1,z2,z4,z6]),(0,[z0,z7,z382,z1,z2,z4,z6]),(0,[z22,z0,z162,z1,z2,z4,z6]),(0,[z0,z7,z481,z1,z2,z4,z6]),(0,[z0,z482,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z133])],[(0,[z65,z0,z7,z304,z1,z4,z6]),(1,[z211,z7,z1,z2,z4,z6]),(0,[z30,z0,z7,z31,z2,z4,z6]),(0,[z0,z7,z1,z2,z483,z4,z6])],[(0,[z0,z7,z11,z1,z2,z4,z6]),(0,[z0,z7,z383,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z484,z4,z6])],[(0,[z0,z7,z485,z1,z2,z4,z6]),(0,[z47,z0,z7,z200,z2,z4,z6]),(1,[z486,z7,z1,z2,z4,z6]),(0,[z9,z0,z7,z1,z2,z5,z6]),(0,[z0,z7,z167,z1,z4,z168,z6]),(0,[z0,z7,z487,z1,z2,z4,z6])]],
   [[(0,[z488,z0,z7,z1,z2,z4,z6]),(0,[z489,z0,z7,z1,z2,z4,z6]),(0,[z490,z0,z7,z1,z2,z4,z6]),(0,[z105,z0,z7,z1,z20,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z491]),(0,[z0,z7,z492,z1,z2,z4,z6])],[(0,[z22,z0,z247,z7,z1,z2,z4]),(0,[z493,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z167,z149,z2,z4,z6]),(0,[z0,z7,z167,z2,z4,z168,z6]),(0,[z0,z7,z1,z31,z2,z180,z6]),(0,[z0,z7,z1,z494,z2,z4,z6])],[(0,[z0,z11,z1,z25,z2,z4,z6]),(0,[z0,z7,z1,z495,z2,z4,z6]),(0,[z496,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z497,z4,z6]),(0,[z0,z7,z1,z2,z498,z4,z6])],[(0,[z0,z499,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z500,z2,z4,z6]),(0,[z501,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z502,z6]),(0,[z0,z7,z1,z2,z4,z6,z503]),(0,[z54,z211,z7,z1,z2,z4,z6]),(0,[z0,z7,z149,z1,z4,z168,z6]),(0,[z0,z7,z504,z1,z2,z4,z6])],[(0,[z156,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z505,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z506,z6]),(0,[z0,z7,z507,z1,z2,z4,z6])],[(0,[z39,z7,z11,z1,z2,z4,z6]),(0,[z508,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z509,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z510]),(0,[z0,z7,z1,z2,z249,z4,z6]),(0,[z0,z7,z1,z2,z4,z168,z6]),(0,[z511,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z304,z1,z4,z6,z133]),(0,[z0,z7,z512,z1,z2,z4,z6])]],
   [[(0,[z67,z0,z11,z1,z2,z4,z6]),(0,[z17,z7,z11,z1,z2,z4,z6]),(0,[z0,z7,z513,z1,z2,z4,z6]),(0,[z0,z7,z1,z25,z2,z4,z6]),(0,[z0,z7,z169,z200,z2,z4,z6])],[(0,[z72,z0,z7,z137,z1,z2,z4]),(0,[z514,z0,z7,z1,z2,z4,z6]),(0,[z515,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z516,z1,z2,z4,z6])],[(0,[z517,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z518])],[(0,[z519,z0,z7,z1,z2,z4,z6])],[(0,[z140,z0,z7,z1,z2,z324,z6]),(1,[z0,z7,z1,z2,z4,z491]),(1,[z0,z7,z1,z94,z2,z4])],[(0,[z0,z7,z150,z2,z4,z168,z6]),(0,[z0,z7,z520,z1,z2,z4,z6])],[(0,[z0,z7,z521,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z522,z6]),(0,[z47,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z523]),(0,[z0,z7,z1,z524,z2,z4,z6])]],
   [[(0,[z118,z0,z11,z1,z2,z4,z6]),(0,[z525,z0,z7,z1,z2,z4,z6]),(0,[z9,z0,z7,z1,z27,z2,z6])],[(1,[z0,z10,z7,z1,z2,z4]),(0,[z0,z7,z526,z1,z2,z4,z6]),(0,[z0,z7,z527,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z528,z6]),(0,[z0,z7,z1,z2,z529,z4,z6]),(0,[z0,z7,z1,z530,z2,z4,z6]),(0,[z0,z7,z531,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z95,z15]),(0,[z0,z7,z1,z532,z2,z4,z6]),(0,[z533,z0,z7,z1,z2,z4,z6]),(1,[z0,z7,z1,z2,z534,z6])],[(0,[z0,z7,z1,z2,z4,z6,z535]),(0,[z536,z0,z7,z1,z2,z4,z6]),(0,[z148,z0,z7,z1,z2,z4,z6]),(0,[z537,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z538,z1,z2,z4,z6]),(0,[z0,z7,z539,z1,z2,z4,z6]),(0,[z0,z7,z80,z1,z2,z534,z6])],[(0,[z22,z0,z7,z1,z2,z4,z84]),(0,[z540,z0,z7,z1,z2,z4,z6])],[(0,[z0,z541,z7,z1,z2,z4,z6]),(0,[z542,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z358,z2,z4,z5,z6]),(0,[z0,z7,z216,z1,z2,z168,z6]),(0,[z0,z7,z132,z304,z1,z2,z6])],[(0,[z0,z543,z7,z1,z2,z4,z6]),(0,[z118,z0,z7,z1,z2,z5,z6]),(1,[z0,z247,z1,z2,z4,z51]),(0,[z0,z7,z169,z1,z2,z4,z6]),(0,[z0,z7,z544,z1,z2,z4,z6]),(0,[z0,z7,z1,z116,z2,z4,z6])]],
   [[(0,[z22,z140,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z113,z6]),(0,[z0,z7,z1,z2,z4,z6,z545]),(0,[z0,z7,z1,z141,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z546,z6])],[(0,[z19,z0,z7,z1,z43,z4,z6]),(0,[z0,z7,z547,z1,z2,z4,z6]),(0,[z39,z0,z305,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z324,z6,z15]),(0,[z22,z0,z7,z1,z2,z336,z6]),(0,[z0,z7,z1,z2,z4,z548,z6]),(0,[z0,z7,z549,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z550,z4,z6]),(0,[z0,z7,z1,z2,z551,z4,z6]),(0,[z0,z7,z1,z2,z552,z4,z6])],[(0,[z101,z0,z292,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z553,z4,z6]),(0,[z0,z7,z554,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z555,z4,z6]),(0,[z0,z7,z200,z2,z4,z6,z170])],[(0,[z0,z7,z556,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z557,z6])],[(0,[z558,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z559,z2,z4,z6])],[(0,[z109,z0,z7,z1,z2,z4,z6]),(1,[z0,z83,z1,z2,z4,z6]),(0,[z0,z7,z1,z34,z2,z4,z6])],[(0,[z0,z7,z100,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z15])]],
   [[(0,[z0,z7,z560,z1,z2,z4,z6]),(0,[z47,z0,z7,z24,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z561]),(0,[z9,z0,z7,z169,z1,z2,z6]),(0,[z0,z7,z1,z2,z562,z4,z6]),(1,[z0,z7,z132,z304,z1,z6])],[(0,[z0,z7,z1,z2,z4,z563,z6]),(0,[z0,z7,z1,z564,z2,z4,z6]),(1,[z0,z7,z1,z104,z4,z6]),(0,[z0,z7,z565,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z566,z4,z6])],[(0,[z567,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z568,z1,z2,z4,z6]),(0,[z0,z7,z1,z569,z2,z4,z6])],[(0,[z570,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z89,z2,z4,z6]),(0,[z0,z265,z7,z100,z2,z4,z6]),(0,[z571,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z572]),(0,[z0,z7,z1,z2,z573,z4,z6])],[(0,[z0,z7,z398,z1,z2,z324,z4]),(0,[z0,z7,z1,z574,z2,z4,z6]),(0,[z0,z575,z7,z1,z2,z4,z6])],[(0,[z0,z17,z1,z2,z4,z5,z6]),(0,[z0,z7,z1,z2,z4,z576,z6]),(0,[z577,z0,z7,z1,z2,z4,z6]),(0,[z578,z0,z7,z1,z2,z4,z6]),(1,[z0,z7,z120,z1,z2,z6])],[(0,[z9,z0,z7,z1,z2,z324,z6]),(0,[z0,z7,z1,z2,z4,z6,z579]),(0,[z580,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z581])],[(1,[z109,z11,z1,z2,z4,z6]),(0,[z101,z7,z68,z1,z2,z4,z6]),(1,[z47,z0,z48,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z582,z6]),(0,[z0,z7,z1,z31,z2,z4,z15]),(0,[z0,z7,z1,z153,z4,z6,z21])]],
   [[(0,[z54,z0,z11,z1,z2,z4,z6]),(0,[z0,z7,z583,z1,z2,z4,z6]),(0,[z486,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z584,z2,z4,z6])],[(0,[z0,z7,z585,z1,z2,z4,z6]),(0,[z0,z7,z586,z1,z2,z4,z6]),(0,[z315,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z587,z4,z6]),(0,[z0,z7,z1,z2,z4,z588,z6])],[(0,[z0,z589,z7,z1,z2,z4,z6]),(1,[z0,z7,z1,z2,z4,z318]),(0,[z0,z7,z1,z2,z4,z6,z21]),(0,[z0,z7,z137,z1,z2,z4,z6])],[(0,[z0,z7,z590,z1,z2,z4,z6])],[],[(0,[z0,z591,z7,z1,z2,z4,z6]),(0,[z0,z7,z80,z1,z153,z2,z4]),(0,[z0,z7,z1,z592,z2,z4,z6])],[(0,[z0,z7,z593,z1,z2,z4,z6]),(0,[z0,z86,z7,z304,z1,z4,z6])],[(0,[z0,z7,z1,z594,z2,z4,z6]),(0,[z0,z595,z7,z1,z2,z4,z6]),(0,[z596,z0,z7,z1,z2,z4,z6]),(0,[z22,z0,z7,z383,z2,z4,z6]),(0,[z0,z7,z1,z153,z2,z4,z21])]],
   [[(0,[z0,z7,z597,z1,z2,z4,z6]),(0,[z0,z7,z598,z1,z2,z4,z6]),(0,[z599,z0,z7,z1,z2,z4,z6])],[(0,[z67,z39,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z200,z2,z4,z6])],[(0,[z0,z7,z1,z600,z2,z4,z6]),(0,[z0,z7,z1,z2,z601,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z602]),(0,[z603,z0,z7,z1,z2,z4,z6]),(0,[z22,z0,z7,z137,z1,z2,z4]),(0,[z0,z7,z604,z1,z2,z4,z6]),(0,[z605,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z359,z4,z6]),(0,[z0,z7,z137,z1,z2,z4,z95])],[(0,[z0,z7,z1,z2,z606,z4,z6]),(0,[z607,z0,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z608,z2,z4,z6]),(0,[z609,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z610,z6]),(0,[z0,z7,z1,z611,z2,z4,z6])],[(0,[z612,z0,z7,z1,z2,z4,z6]),(0,[z613,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z614,z2,z4,z6])]],
   [[(0,[z615,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z616,z2,z4,z6]),(0,[z0,z7,z1,z617,z2,z4,z6]),(0,[z0,z7,z169,z132,z1,z2,z6]),(0,[z105,z0,z7,z1,z153,z4,z6]),(0,[z9,z0,z7,z137,z1,z2,z6])],[(0,[z0,z7,z1,z618,z2,z4,z6]),(1,[z173,z7,z1,z2,z4,z6]),(0,[z0,z7,z167,z1,z150,z4,z6]),(0,[z0,z619,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z620,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z6]),(0,[z0,z7,z621,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z622,z4,z6]),(0,[z0,z623,z7,z1,z2,z4,z6]),(0,[z0,z7,z624,z1,z2,z4,z6])],[(0,[z0,z7,z625,z1,z2,z4,z6]),(0,[z0,z7,z308,z1,z2,z4,z6]),(0,[z0,z7,z207,z2,z4,z5,z6])],[(0,[z0,z7,z1,z2,z4,z626,z6]),(0,[z0,z7,z627,z1,z2,z4,z6]),(0,[z65,z486,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z628,z6]),(0,[z0,z629,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z630,z6]),(0,[z0,z7,z1,z2,z4,z6,z631])],[(0,[z0,z7,z632,z1,z2,z4,z6])],[(0,[z109,z7,z11,z1,z2,z4,z6]),(1,[z19,z7,z1,z43,z4,z6]),(0,[z39,z0,z7,z1,z20,z4,z6]),(0,[z0,z265,z7,z48,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z633]),(0,[z0,z7,z634,z1,z2,z4,z6]),(0,[z9,z0,z7,z132,z1,z2,z6])],[(0,[z0,z7,z1,z2,z4,z635,z6]),(0,[z7,z1,z2,z4,z23,z6,z84]),(0,[z0,z7,z149,z1,z2,z4,z6]),(0,[z0,z7,z132,z304,z1,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z636])]],
   [[(0,[z0,z7,z1,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z637,z4,z6]),(0,[z0,z7,z1,z43,z4,z6,z21]),(0,[z0,z7,z1,z2,z638,z4,z6]),(0,[z0,z7,z1,z141,z4,z5,z6]),(0,[z0,z7,z639,z1,z2,z4,z6]),(0,[z0,z7,z1,z640,z2,z4,z6]),(0,[z0,z7,z641,z1,z2,z4,z6])],[(0,[z0,z7,z1,z642,z2,z4,z6]),(1,[z0,z7,z58,z2,z4,z95])],[(0,[z217,z101,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z2,z4,z6]),(0,[z0,z7,z1,z31,z2,z4,z6])],[(1,[z0,z81,z7,z1,z2,z4]),(0,[z0,z7,z1,z2,z4,z6,z643]),(0,[z0,z7,z644,z1,z2,z4,z6]),(0,[z0,z7,z645,z1,z2,z4,z6]),(0,[z47,z128,z7,z1,z2,z4,z6]),(0,[z0,z7,z646,z1,z2,z4,z6])],[(0,[z0,z81,z7,z11,z1,z2,z4]),(0,[z0,z7,z33,z1,z2,z4,z6]),(0,[z647,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z648,z4,z6]),(0,[z47,z0,z1,z48,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z95]),(0,[z0,z649,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z14]),(0,[z9,z0,z7,z1,z2,z4,z15])],[(0,[z67,z7,z1,z2,z43,z4,z6]),(0,[z650,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z651,z6]),(0,[z0,z7,z1,z2,z652,z4,z6]),(0,[z140,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z653,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z654]),(0,[z0,z7,z1,z2,z4,z6,z655])]],
   [[(0,[z0,z7,z1,z2,z324,z4,z491]),(0,[z656,z0,z7,z1,z2,z4,z6]),(1,[z0,z7,z1,z2,z180,z6])],[(0,[z109,z0,z17,z1,z2,z4,z6]),(0,[z7,z1,z20,z2,z43,z4,z6]),(0,[z0,z7,z1,z657,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z658])],[(0,[z0,z7,z1,z2,z659,z4,z6]),(0,[z0,z7,z660,z1,z2,z4,z6]),(0,[z65,z0,z1,z2,z66,z4,z6]),(0,[z0,z7,z100,z1,z2,z298,z4]),(0,[z0,z7,z132,z100,z1,z2,z6]),(0,[z0,z7,z1,z2,z661,z4,z6])],[(0,[z22,z0,z7,z1,z2,z466,z6]),(0,[z0,z7,z1,z2,z4,z23,z6]),(0,[z662,z0,z7,z1,z2,z4,z6]),(0,[z663,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z149,z150,z2,z4,z6]),(0,[z0,z7,z1,z664,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z665,z6]),(0,[z0,z7,z132,z1,z2,z4,z6])],[(0,[z0,z7,z1,z150,z2,z4,z6]),(0,[z0,z7,z100,z1,z2,z6,z170])],[(0,[z0,z7,z304,z1,z2,z4,z6]),(0,[z0,z666,z7,z1,z2,z4,z6]),(0,[z233,z7,z1,z2,z4,z6,z15])],[(0,[z0,z7,z1,z667,z2,z4,z6]),(1,[z0,z7,z1,z249,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z668]),(0,[z47,z0,z7,z100,z2,z4,z6]),(0,[z118,z0,z1,z2,z3,z4,z6])]],
   [[(0,[z0,z7,z1,z669,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z670]),(0,[z0,z671,z7,z1,z2,z4,z6]),(1,[z0,z7,z1,z27,z6,z133])],[(0,[z672,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z673,z1,z2,z4,z6])],[(0,[z0,z7,z674,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z675,z6]),(0,[z0,z7,z1,z2,z676,z4,z6])],[(0,[z0,z7,z1,z2,z4,z6,z677]),(0,[z678,z0,z7,z1,z2,z4,z6])],[(0,[z679,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z6,z680]),(0,[z72,z0,z7,z1,z2,z4,z15]),(0,[z0,z7,z681,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z534,z6])],[(1,[z140,z7,z1,z2,z113,z6]),(0,[z0,z7,z1,z682,z2,z4,z6]),(0,[z0,z7,z683,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z684,z4,z6])],[(0,[z0,z7,z1,z2,z4,z685,z6]),(0,[z686,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z687,z1,z2,z4,z6]),(0,[z0,z7,z1,z688,z2,z4,z6]),(0,[z689,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z100,z1,z200,z2,z6]),(1,[z9,z0,z7,z137,z1,z2])]],
   [[(0,[z0,z7,z1,z2,z354,z4,z6]),(0,[z0,z7,z169,z100,z2,z4,z6]),(0,[z0,z7,z1,z690,z2,z4,z6])],[(0,[z691,z0,z7,z1,z2,z4,z6]),(0,[z692,z0,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z693,z2,z4,z6]),(0,[z0,z7,z694,z1,z2,z4,z6]),(0,[z0,z49,z7,z1,z2,z5,z6]),(0,[z0,z7,z1,z2,z695,z4,z6])],[(0,[z0,z7,z696,z1,z2,z4,z6]),(0,[z0,z697,z7,z1,z2,z4,z6])],[(0,[z0,z698,z7,z1,z2,z4,z6]),(0,[z0,z7,z137,z80,z1,z2,z4]),(0,[z699,z0,z7,z1,z2,z4,z6])],[(1,[z0,z7,z398,z1,z2,z4]),(0,[z0,z7,z700,z1,z2,z4,z6])],[(0,[z0,z7,z701,z1,z2,z4,z6])],[(0,[z105,z0,z7,z1,z43,z4,z6]),(1,[z0,z308,z1,z2,z4,z6]),(1,[z65,z0,z1,z66,z4,z6]),(0,[z0,z7,z122,z1,z2,z4,z6]),(0,[z0,z7,z702,z1,z2,z4,z6])],[(0,[z0,z7,z703,z1,z2,z4,z6]),(0,[z0,z704,z7,z1,z2,z4,z6]),(0,[z705,z0,z7,z1,z2,z4,z6]),(0,[z706,z0,z7,z1,z2,z4,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z173,z7,z1,z2,z4,z6]),(0,[z315,z292,z1,z2,z4,z6]),(0,[z0,z707,z1,z2,z4,z6]),(0,[z0,z162,z383,z2,z4,z6]),(0,[z47,z0,z708,z2,z4,z6]),(1,[z0,z1,z2,z709,z6]),(0,[z0,z1,z2,z709,z4,z6])],[(0,[z0,z7,z710,z2,z4,z6]),(0,[z0,z7,z711,z1,z2,z4]),(0,[z0,z7,z1,z2,z712,z6]),(0,[z713,z7,z1,z2,z4,z6]),(0,[z714,z7,z1,z2,z4,z6]),(0,[z0,z7,z197,z2,z4,z95])],[(0,[z0,z10,z162,z1,z2,z4]),(0,[z0,z715,z1,z2,z4,z6]),(0,[z0,z7,z716,z2,z4,z6]),(0,[z148,z717,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z196,z15])],[(0,[z486,z7,z1,z2,z4,z6]),(0,[z0,z7,z718,z2,z4,z6]),(0,[z0,z7,z34,z104,z4,z6]),(0,[z0,z7,z1,z719,z4,z6]),(0,[z148,z0,z167,z4,z168,z6]),(0,[z0,z7,z1,z2,z720,z6]),(0,[z0,z721,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z722,z4,z6]),(0,[z0,z480,z1,z2,z5,z6]),(0,[z0,z7,z1,z2,z4,z723]),(0,[z0,z7,z1,z2,z476,z15])],[(0,[z148,z0,z1,z2,z4,z6]),(0,[z0,z7,z122,z207,z4,z6]),(0,[z0,z1,z2,z4,z724,z6])],[(0,[z0,z7,z1,z2,z725,z6]),(0,[z0,z7,z726,z1,z2,z4]),(0,[z0,z7,z169,z401,z2,z6])],[(0,[z0,z7,z1,z2,z4,z727]),(0,[z0,z7,z1,z2,z728,z6]),(0,[z0,z7,z1,z2,z661,z15])]],
   [[(0,[z0,z729,z1,z2,z4,z6]),(0,[z22,z382,z1,z2,z4,z6]),(0,[z0,z730,z1,z2,z4,z6]),(0,[z0,z7,z1,z731,z4,z6]),(0,[z732,z7,z1,z2,z4,z6]),(0,[z0,z7,z58,z2,z4,z95])],[(0,[z0,z7,z733,z1,z4,z6]),(0,[z0,z7,z734,z2,z4,z6]),(0,[z0,z7,z735,z1,z2,z6]),(0,[z0,z7,z1,z736,z4,z6]),(0,[z0,z7,z1,z2,z737,z6]),(0,[z0,z7,z1,z27,z442,z6]),(0,[z738,z7,z1,z2,z4,z6])],[(0,[z65,z0,z1,z529,z4,z6])],[(0,[z739,z0,z1,z2,z4,z6]),(0,[z156,z7,z398,z1,z2,z324]),(0,[z0,z7,z740,z1,z2,z6]),(0,[z0,z7,z741,z2,z4,z6]),(0,[z0,z7,z167,z4,z168,z6]),(0,[z742,z7,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z743,z6])]],
   [[(0,[z0,z7,z137,z120,z1,z2])],[(0,[z0,z7,z1,z2,z4,z6]),(0,[z744,z7,z1,z2,z4,z6]),(0,[z0,z745,z7,z1,z2,z4]),(0,[z0,z746,z1,z2,z4,z6]),(0,[z0,z7,z1,z747,z4,z6])],[(0,[z0,z7,z1,z2,z4,z748]),(0,[z22,z7,z1,z2,z4,z535]),(0,[z0,z7,z1,z205,z4,z21]),(0,[z0,z7,z749,z2,z4,z6]),(0,[z0,z7,z120,z1,z2,z15])],[(0,[z0,z7,z1,z750,z4,z6]),(0,[z54,z0,z162,z1,z2,z4]),(0,[z0,z7,z1,z249,z336,z6]),(0,[z233,z7,z1,z2,z466,z6]),(0,[z0,z7,z1,z2,z180,z6]),(0,[z0,z7,z1,z2,z186,z15])]],
   [[(0,[z320,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z751,z6]),(0,[z0,z7,z1,z2,z752,z6])],[(0,[z0,z7,z1,z2,z753,z6]),(0,[z0,z7,z754,z2,z4,z6]),(0,[z0,z7,z1,z755,z4,z6]),(0,[z0,z83,z1,z2,z466,z6]),(0,[z0,z7,z358,z141,z4,z6]),(0,[z717,z7,z1,z2,z4,z6]),(0,[z0,z7,z2,z756,z6,z170])],[(0,[z0,z292,z1,z2,z4,z6]),(0,[z0,z7,z1,z757,z4,z6]),(0,[z758,z7,z1,z2,z4,z6]),(0,[z0,z759,z1,z2,z4,z6]),(0,[z0,z7,z1,z760,z2,z6]),(0,[z761,z7,z1,z2,z4,z6])],[(0,[z0,z744,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z762,z6]),(0,[z0,z7,z34,z2,z4,z15]),(0,[z0,z7,z137,z1,z249,z4]),(0,[z0,z7,z1,z2,z763,z6]),(0,[z764,z7,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z2,z765,z6]),(0,[z0,z7,z1,z104,z466,z6])],[(0,[z0,z10,z7,z1,z2,z4]),(0,[z173,z83,z1,z2,z4,z6]),(0,[z766,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z767])],[(0,[z39,z7,z1,z509,z4,z6]),(0,[z7,z1,z768,z2,z4,z6]),(0,[z22,z7,z138,z1,z2,z4]),(0,[z0,z769,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z770,z6]),(0,[z0,z7,z141,z207,z4,z6]),(0,[z148,z0,z216,z1,z2,z6]),(0,[z0,z7,z1,z2,z4,z771]),(0,[z0,z7,z1,z27,z6,z133])]],
   [[(0,[z173,z11,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z772,z6]),(0,[z0,z7,z773,z2,z4,z6]),(0,[z0,z1,z25,z774,z4,z6]),(0,[z0,z167,z4,z142,z168,z6]),(0,[z0,z775,z1,z2,z4,z6]),(0,[z0,z7,z776,z1,z4,z21])],[(0,[z109,z744,z1,z2,z4,z6]),(0,[z0,z7,z777,z2,z4,z6]),(0,[z19,z7,z1,z778,z4,z6]),(0,[z0,z7,z1,z778,z4,z6]),(0,[z0,z7,z1,z2,z779,z6]),(0,[z233,z7,z1,z2,z41,z15]),(1,[z0,z7,z780,z1,z2])],[(0,[z39,z305,z1,z20,z4,z6]),(0,[z22,z7,z1,z2,z466,z84]),(0,[z0,z7,z358,z2,z4,z6]),(0,[z0,z7,z1,z2,z359,z6])],[(0,[z0,z7,z781,z2,z4,z6]),(0,[z156,z7,z1,z2,z324,z6]),(0,[z782,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z141,z6,z15]),(0,[z0,z7,z783,z2,z4,z6]),(0,[z0,z7,z1,z27,z143,z6])]],
   [[(0,[z0,z784,z1,z2,z4,z6]),(0,[z140,z7,z1,z2,z113,z6]),(0,[z0,z162,z1,z2,z466,z6]),(0,[z65,z0,z1,z584,z4,z6]),(0,[z785,z7,z1,z2,z4,z6]),(0,[z0,z7,z149,z150,z4,z6]),(0,[z0,z7,z786,z1,z2,z6])],[(0,[z0,z7,z787,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z788]),(0,[z22,z7,z1,z2,z324,z15]),(0,[z0,z7,z34,z2,z466,z6]),(0,[z0,z7,z383,z2,z336,z6]),(0,[z789,z7,z1,z2,z4,z6]),(0,[z148,z732,z1,z2,z4,z6]),(0,[z7,z1,z2,z41,z14,z15]),(0,[z0,z7,z137,z780,z1,z2])],[(0,[z0,z7,z1,z790,z4,z6]),(0,[z0,z7,z1,z2,z4,z791]),(0,[z156,z7,z1,z2,z324,z491]),(0,[z0,z7,z1,z2,z298,z15]),(0,[z30,z0,z7,z120,z31,z2]),(0,[z0,z792,z1,z2,z4,z6]),(0,[z105,z0,z7,z80,z1,z534]),(0,[z9,z0,z7,z137,z1,z2])],[(1,[z744,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z793]),(0,[z0,z794,z1,z2,z4,z6]),(0,[z0,z795,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z796,z6]),(0,[z0,z1,z2,z709,z5,z6]),(0,[z797,z0,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z798,z4,z6]),(0,[z67,z83,z1,z2,z4,z6]),(0,[z0,z7,z799,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z800]),(0,[z0,z801,z1,z2,z4,z6]),(0,[z802,z7,z1,z2,z4,z6])],[(0,[z101,z7,z68,z2,z4,z6]),(0,[z0,z803,z1,z2,z4,z6]),(0,[z804,z7,z1,z2,z4,z6]),(0,[z0,z7,z805,z1,z4,z6]),(0,[z0,z86,z1,z774,z4,z6]),(0,[z0,z7,z2,z756,z4,z6]),(0,[z0,z7,z169,z201,z2,z6])],[(0,[z0,z83,z1,z2,z4,z6]),(0,[z118,z0,z1,z2,z263,z6]),(0,[z0,z7,z1,z2,z806,z6]),(0,[z0,z7,z1,z2,z807,z6]),(0,[z0,z7,z808,z2,z4,z6]),(0,[z0,z83,z1,z2,z336,z6]),(0,[z809,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z94,z27,z133])],[(0,[z0,z382,z1,z2,z4,z6]),(0,[z0,z7,z1,z810,z2,z4]),(0,[z105,z0,z7,z590,z1,z4]),(0,[z0,z7,z398,z1,z2,z4]),(0,[z811,z7,z1,z2,z4,z6]),(0,[z0,z222,z1,z2,z5,z6]),(0,[z812,z7,z1,z2,z4,z6])]],
   [[(0,[z0,z813,z7,z1,z2,z4]),(0,[z0,z7,z814,z2,z4,z6]),(0,[z0,z7,z1,z2,z815,z4]),(0,[z0,z7,z1,z2,z816,z4]),(0,[z0,z1,z774,z66,z4,z6]),(0,[z0,z7,z132,z304,z1,z6]),(0,[z0,z7,z1,z760,z27,z6]),(0,[z0,z7,z776,z1,z153,z4])],[(0,[z744,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z104,z4,z6]),(1,[z7,z1,z778,z4,z6]),(0,[z0,z7,z398,z1,z2,z336]),(0,[z451,z7,z1,z2,z324,z6]),(0,[z0,z7,z383,z249,z4,z6])],[(0,[z817,z7,z1,z2,z4,z6])],[(0,[z508,z7,z1,z43,z4,z6]),(0,[z0,z7,z1,z2,z818,z6]),(0,[z0,z1,z2,z4,z142,z6]),(0,[z0,z7,z1,z2,z4,z819]),(0,[z0,z7,z1,z820,z4,z6]),(0,[z0,z7,z200,z2,z756,z6])]],
   [[(0,[z0,z7,z1,z821,z4,z6]),(0,[z81,z7,z1,z2,z4,z23]),(0,[z54,z0,z1,z2,z4,z63]),(0,[z0,z7,z1,z822,z4,z6]),(0,[z0,z7,z823,z1,z2,z6]),(0,[z0,z49,z1,z141,z5,z6]),(0,[z0,z247,z1,z2,z359,z51]),(0,[z0,z7,z1,z2,z824,z6]),(0,[z0,z7,z1,z27,z327,z6]),(0,[z0,z7,z776,z1,z4,z6])],[(0,[z233,z7,z1,z2,z324,z6]),(0,[z0,z7,z137,z1,z2,z336]),(1,[z0,z1,z2,z4,z800]),(0,[z0,z7,z2,z820,z4,z6]),(0,[z0,z7,z120,z1,z2,z6]),(0,[z825,z7,z1,z2,z4,z6]),(0,[z0,z7,z80,z1,z321,z4])],[(0,[z0,z7,z1,z2,z826,z6]),(0,[z0,z7,z827,z2,z4,z6]),(0,[z7,z1,z2,z4,z6,z828]),(0,[z72,z7,z1,z2,z4,z828]),(0,[z0,z1,z25,z4,z125,z6])],[(0,[z164,z11,z1,z2,z4,z6]),(0,[z173,z17,z1,z2,z4,z6]),(0,[z217,z7,z768,z2,z4,z6]),(0,[z0,z7,z1,z829,z2,z4]),(0,[z0,z7,z1,z830,z2,z6]),(0,[z22,z7,z1,z2,z4,z84]),(0,[z0,z7,z1,z2,z831,z6]),(0,[z0,z832,z1,z2,z4,z6])]],
   [[(0,[z22,z81,z7,z1,z2,z4]),(0,[z833,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z834,z4,z6]),(0,[z0,z7,z1,z835,z2,z6]),(0,[z105,z0,z7,z776,z1,z4])],[(0,[z0,z7,z1,z2,z836,z6]),(0,[z0,z162,z1,z2,z336,z6]),(0,[z0,z837,z1,z2,z4,z6]),(0,[z7,z1,z2,z4,z6,z838]),(0,[z0,z7,z1,z839,z2,z4])],[(0,[z486,z17,z1,z2,z4,z6]),(0,[z0,z7,z34,z2,z4,z6]),(0,[z0,z7,z840,z2,z4,z6]),(0,[z841,z7,z1,z2,z4,z6]),(0,[z0,z7,z842,z1,z2,z6]),(0,[z0,z7,z1,z2,z4,z318])],[(0,[z9,z0,z7,z398,z1,z2]),(0,[z0,z7,z1,z2,z336,z15]),(0,[z0,z7,z843,z1,z2,z6]),(0,[z844,z7,z1,z2,z4,z6]),(0,[z7,z1,z2,z4,z6,z845]),(0,[z0,z7,z31,z839,z2,z4])]],
   [[(0,[z0,z7,z1,z846,z4,z6]),(0,[z233,z7,z1,z2,z113,z6]),(0,[z847,z0,z7,z1,z2,z6])],[(0,[z240,z17,z1,z2,z4,z6]),(0,[z848,z7,z1,z2,z4,z6]),(0,[z0,z7,z358,z2,z6,z15]),(0,[z0,z7,z149,z820,z4,z6]),(0,[z0,z7,z100,z2,z318,z170]),(0,[z0,z849,z1,z2,z4,z6])],[(0,[z0,z11,z358,z2,z4,z6]),(0,[z0,z7,z1,z2,z61,z15]),(0,[z54,z0,z1,z2,z4,z55])],[(0,[z236,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z850,z6]),(0,[z22,z7,z1,z2,z4,z828]),(0,[z0,z7,z150,z820,z4,z6]),(0,[z0,z7,z137,z1,z116,z2])]],
   [[(0,[z0,z7,z851,z2,z4,z6]),(0,[z0,z10,z7,z1,z2,z753]),(0,[z0,z852,z1,z2,z4,z6]),(0,[z0,z7,z853,z2,z4,z6]),(0,[z0,z854,z1,z2,z4,z6])],[(0,[z305,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z855,z6]),(0,[z486,z305,z1,z2,z4,z6]),(0,[z7,z1,z2,z4,z14,z491]),(0,[z0,z7,z132,z1,z552,z6]),(0,[z856,z7,z1,z2,z4,z6])],[(0,[z67,z17,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z857,z6]),(0,[z0,z858,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z859,z6]),(0,[z0,z216,z1,z2,z142,z6]),(0,[z0,z7,z1,z2,z562,z15])],[(0,[z0,z7,z1,z249,z4,z15]),(0,[z22,z211,z7,z1,z2,z4]),(0,[z72,z7,z1,z2,z4,z14]),(0,[z860,z0,z7,z1,z2,z4]),(0,[z0,z7,z100,z2,z450,z6])]],
   [[(0,[z0,z7,z1,z861,z4,z6]),(0,[z22,z7,z1,z2,z4,z491]),(0,[z54,z0,z392,z1,z2,z4]),(0,[z47,z0,z504,z2,z4,z6]),(0,[z0,z7,z100,z2,z298,z170]),(0,[z0,z7,z169,z2,z756,z6]),(0,[z0,z7,z862,z2,z4,z6])],[(0,[z0,z7,z1,z2,z863,z6]),(0,[z0,z7,z1,z2,z864,z6]),(0,[z7,z1,z778,z43,z4,z6]),(0,[z0,z1,z2,z4,z865,z6]),(0,[z866,z7,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z867,z6])],[(0,[z0,z868,z1,z2,z4,z6]),(0,[z0,z869,z1,z2,z4,z6]),(0,[z0,z83,z1,z104,z4,z6]),(0,[z0,z7,z870,z2,z4,z6]),(0,[z0,z7,z1,z2,z871,z4]),(0,[z0,z7,z100,z2,z756,z6]),(0,[z872,z7,z1,z2,z4,z6])],[(0,[z0,z873,z1,z2,z4,z6]),(0,[z533,z7,z1,z20,z4,z6]),(0,[z0,z7,z1,z2,z874,z6]),(0,[z0,z7,z1,z760,z4,z6]),(0,[z105,z0,z7,z80,z1,z4])]],
   [[(0,[z0,z7,z1,z875,z2,z6]),(0,[z0,z7,z876,z2,z4,z6]),(0,[z0,z76,z1,z2,z3,z6])],[(0,[z22,z54,z11,z1,z2,z4]),(0,[z67,z305,z1,z2,z4,z6]),(0,[z47,z0,z432,z2,z4,z6]),(0,[z39,z308,z1,z20,z4,z6]),(0,[z0,z7,z1,z877,z4,z6]),(1,[z0,z7,z820,z4,z6]),(0,[z30,z0,z7,z31,z2,z180]),(0,[z0,z7,z1,z2,z4,z50]),(0,[z0,z7,z780,z1,z2,z4])],[(0,[z315,z7,z1,z2,z4,z6]),(0,[z0,z7,z878,z1,z2,z6]),(0,[z0,z7,z879,z2,z4,z6]),(0,[z0,z7,z100,z2,z6,z170]),(0,[z0,z7,z120,z1,z2,z298]),(0,[z0,z7,z780,z1,z2,z6])],[(0,[z0,z305,z1,z2,z4,z6]),(0,[z0,z7,z1,z880,z4,z6]),(0,[z30,z0,z7,z839,z2,z4])]],
   [[(1,[z7,z768,z2,z4,z6]),(0,[z0,z881,z1,z2,z4,z6]),(0,[z22,z83,z1,z2,z4,z84]),(0,[z0,z7,z122,z1,z4,z6]),(0,[z0,z7,z304,z1,z502,z6]),(0,[z0,z1,z2,z4,z55,z800])],[(0,[z101,z7,z768,z2,z4,z6]),(0,[z0,z7,z1,z249,z466,z6])],[(0,[z128,z7,z1,z2,z4,z6]),(0,[z0,z882,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z883]),(0,[z19,z7,z1,z43,z4,z6]),(0,[z0,z7,z1,z2,z884,z6]),(0,[z118,z0,z1,z2,z3,z6]),(0,[z0,z49,z207,z2,z5,z6]),(0,[z0,z7,z1,z421,z4,z21])],[(0,[z101,z7,z160,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z885]),(0,[z0,z83,z34,z2,z4,z6]),(0,[z22,z7,z1,z104,z4,z84]),(0,[z0,z7,z1,z2,z886,z6]),(1,[z0,z7,z839,z2,z4]),(0,[z0,z7,z1,z2,z41,z15])]],
   [[(0,[z211,z7,z1,z2,z4,z6]),(0,[z662,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z887,z4,z6]),(0,[z0,z888,z1,z2,z4,z6])],[(0,[z0,z7,z889,z1,z2,z6]),(0,[z0,z7,z1,z2,z4,z890]),(0,[z0,z17,z358,z2,z4,z6]),(0,[z7,z68,z768,z2,z4,z6]),(0,[z0,z162,z1,z104,z4,z6]),(0,[z0,z7,z137,z34,z2,z4]),(0,[z7,z1,z2,z4,z6,z891])],[(0,[z0,z7,z892,z1,z2,z6]),(0,[z0,z7,z1,z2,z4,z893]),(0,[z0,z894,z1,z2,z4,z6]),(0,[z0,z7,z398,z1,z2,z15]),(0,[z0,z708,z48,z2,z4,z6])],[(0,[z0,z81,z7,z1,z2,z4]),(0,[z0,z7,z1,z2,z895,z6]),(0,[z0,z7,z1,z896,z4,z6]),(0,[z0,z7,z1,z141,z4,z6]),(0,[z0,z7,z897,z2,z4,z6]),(0,[z0,z7,z169,z200,z2,z6]),(0,[z0,z7,z898,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z2,z899,z6]),(0,[z0,z7,z900,z2,z4,z6])],[(0,[z54,z0,z10,z1,z2,z4]),(0,[z0,z7,z1,z2,z901,z4]),(0,[z0,z7,z902,z2,z4,z6]),(0,[z0,z903,z1,z2,z4,z6]),(0,[z0,z904,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z800,z51]),(0,[z905,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z153,z4,z21])],[(0,[z0,z7,z906,z1,z2,z6]),(0,[z140,z52,z1,z2,z113,z6]),(0,[z0,z7,z1,z2,z336,z6]),(0,[z7,z1,z2,z324,z907,z6]),(0,[z0,z7,z1,z2,z4,z908]),(0,[z0,z7,z1,z909,z4,z6]),(0,[z0,z7,z910,z1,z2,z6]),(1,[z0,z7,z776,z1,z4])],[(0,[z0,z7,z1,z911,z2,z4]),(0,[z0,z912,z1,z2,z4,z6]),(0,[z22,z162,z1,z2,z4,z84]),(0,[z7,z1,z2,z4,z828,z84])]],
   [[(0,[z7,z1,z2,z907,z4,z6]),(0,[z22,z7,z34,z2,z4,z84]),(0,[z0,z7,z1,z2,z913,z6]),(0,[z0,z7,z1,z914,z4,z6]),(0,[z148,z0,z1,z2,z354,z6]),(1,[z0,z7,z2,z756,z6])],[(0,[z0,z7,z1,z915,z4,z6]),(0,[z67,z292,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z916]),(0,[z0,z917,z1,z2,z4,z6])],[(0,[z7,z11,z34,z2,z4,z6]),(0,[z0,z418,z1,z25,z4,z6]),(0,[z67,z744,z1,z2,z4,z6]),(0,[z0,z7,z1,z918,z4,z6]),(0,[z7,z1,z2,z324,z6,z409]),(0,[z0,z162,z34,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z828]),(0,[z0,z7,z1,z2,z166,z6]),(0,[z0,z1,z2,z3,z709,z6])],[(0,[z0,z10,z7,z1,z2,z919]),(0,[z0,z7,z1,z920,z4,z6]),(0,[z0,z7,z383,z2,z466,z6]),(0,[z921,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z922,z6]),(0,[z0,z7,z132,z1,z2,z318]),(0,[z0,z923,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z2,z919,z6]),(0,[z0,z7,z1,z2,z924,z6]),(0,[z67,z7,z1,z249,z4,z6]),(0,[z925,z0,z1,z2,z4,z6]),(0,[z269,z7,z1,z43,z4,z6]),(0,[z926,z7,z1,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z927]),(0,[z0,z7,z1,z2,z928,z4])],[(0,[z0,z7,z1,z2,z4,z929]),(0,[z0,z7,z1,z249,z4,z6]),(0,[z0,z1,z2,z774,z4,z6]),(0,[z9,z0,z7,z1,z141,z6]),(0,[z173,z54,z1,z2,z4,z55]),(0,[z0,z930,z1,z2,z4,z6]),(0,[z0,z7,z1,z931,z4,z6]),(0,[z0,z7,z932,z2,z4,z6])],[(0,[z0,z7,z1,z2,z4,z491]),(0,[z933,z7,z1,z2,z4,z6]),(0,[z0,z7,z200,z2,z246,z6]),(0,[z0,z1,z2,z4,z800,z6]),(0,[z0,z7,z1,z94,z2,z4]),(0,[z0,z7,z934,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z2,z4,z935]),(0,[z0,z936,z1,z2,z4,z6]),(0,[z0,z7,z937,z2,z4,z6]),(0,[z0,z938,z1,z2,z4,z6]),(0,[z22,z7,z1,z2,z4,z231]),(0,[z0,z7,z1,z2,z4,z939]),(0,[z0,z7,z1,z2,z354,z6])],[(0,[z0,z7,z1,z940,z4,z6]),(0,[z0,z941,z1,z2,z4,z6]),(0,[z0,z1,z708,z2,z4,z6]),(0,[z9,z0,z7,z780,z1,z2])],[(0,[z109,z81,z11,z1,z2,z4]),(0,[z315,z11,z1,z2,z4,z6]),(0,[z17,z744,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z942]),(0,[z0,z7,z358,z122,z4,z6]),(0,[z0,z943,z1,z2,z4,z6])],[(0,[z0,z7,z944,z2,z4,z6]),(0,[z47,z315,z48,z2,z4,z6]),(0,[z0,z7,z1,z2,z945,z6]),(0,[z0,z7,z1,z2,z4,z946]),(0,[z947,z0,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z948,z4,z6]),(0,[z949,z0,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z950]),(0,[z0,z7,z1,z951,z2,z6]),(0,[z0,z7,z167,z216,z168,z6]),(0,[z0,z7,z780,z1,z2,z41])],[(0,[z248,z7,z89,z2,z4,z6]),(0,[z0,z7,z952,z2,z4,z6]),(0,[z0,z7,z1,z2,z534,z6])],[(0,[z477,z11,z1,z2,z4,z6]),(0,[z7,z768,z89,z2,z4,z6]),(0,[z39,z7,z1,z778,z4,z6]),(1,[z7,z1,z2,z4,z828])],[(0,[z0,z7,z953,z1,z4,z6]),(0,[z0,z7,z100,z2,z210,z6]),(0,[z65,z486,z1,z66,z4,z6]),(0,[z0,z7,z167,z354,z168,z6]),(0,[z7,z1,z2,z4,z6,z954]),(0,[z0,z7,z58,z839,z2,z4]),(0,[z0,z7,z1,z27,z50,z133]),(0,[z0,z955,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1,z956,z2,z4]),(0,[z0,z7,z957,z1,z2,z4]),(0,[z0,z7,z1,z2,z4,z958]),(0,[z7,z1,z2,z907,z113,z6]),(0,[z0,z247,z1,z2,z166,z51])],[(0,[z0,z7,z1,z959,z4,z6])],[(0,[z486,z11,z1,z2,z4,z6]),(0,[z0,z960,z1,z2,z4,z6]),(0,[z0,z49,z122,z1,z5,z6]),(0,[z0,z247,z1,z2,z4,z51]),(0,[z961,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z354,z771]),(0,[z0,z7,z1,z27,z2,z318])],[(0,[z0,z11,z1,z141,z4,z6]),(0,[z0,z1,z2,z4,z962,z6]),(0,[z963,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z964,z4,z6]),(0,[z0,z7,z1,z94,z116,z2]),(0,[z0,z7,z132,z549,z1,z6])]],
   [[(0,[z517,z11,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z965]),(0,[z0,z7,z383,z2,z4,z6]),(0,[z47,z64,z1,z2,z4,z6]),(0,[z966,z7,z1,z2,z4,z6]),(0,[z0,z7,z167,z820,z4,z6]),(0,[z0,z7,z967,z1,z4,z6]),(0,[z0,z7,z1,z116,z2,z15]),(0,[z0,z7,z780,z1,z2,z15])],[(0,[z109,z10,z11,z1,z2,z4]),(0,[z0,z7,z1,z2,z968,z4]),(0,[z0,z7,z1,z2,z969,z6]),(0,[z0,z7,z207,z2,z4,z6]),(0,[z0,z7,z970,z2,z4,z6]),(0,[z118,z0,z1,z2,z709,z6]),(0,[z0,z7,z839,z2,z4,z6])],[(0,[z403,z11,z1,z2,z4,z6]),(0,[z0,z308,z1,z2,z4,z6]),(0,[z140,z7,z1,z2,z907,z6]),(0,[z0,z247,z162,z1,z2,z4]),(0,[z0,z7,z1,z104,z336,z6]),(0,[z65,z0,z1,z66,z4,z6]),(0,[z971,z7,z1,z2,z4,z6]),(0,[z0,z86,z465,z1,z4,z6]),(0,[z0,z7,z216,z1,z2,z6])],[(0,[z0,z7,z1,z972,z4,z6]),(0,[z101,z292,z68,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z973]),(0,[z233,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z907,z6]),(0,[z7,z1,z2,z324,z466,z6]),(0,[z974,z7,z1,z2,z4,z6])]],
   [[(0,[z0,z975,z1,z2,z4,z6]),(0,[z128,z1,z25,z2,z4,z6]),(0,[z0,z7,z1,z2,z976,z6]),(0,[z47,z0,z530,z2,z4,z6])],[(0,[z81,z211,z7,z1,z2,z4]),(0,[z0,z7,z1,z2,z977,z6]),(0,[z54,z0,z1,z2,z4,z800]),(0,[z978,z7,z1,z2,z4,z6]),(0,[z979,z7,z1,z2,z4,z6]),(0,[z0,z7,z80,z776,z1,z4])],[(0,[z0,z7,z428,z2,z4,z95]),(0,[z65,z0,z1,z774,z4,z6])],[(0,[z217,z7,z89,z2,z4,z6]),(0,[z0,z7,z1,z2,z980,z6]),(0,[z0,z981,z1,z2,z4,z6]),(0,[z0,z83,z1,z249,z4,z6]),(0,[z982,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z983]),(0,[z0,z7,z304,z1,z760,z6])]],
   [[(0,[z0,z7,z1,z984,z2,z6]),(0,[z39,z7,z1,z20,z4,z6]),(0,[z156,z7,z1,z2,z907,z6]),(0,[z22,z7,z1,z2,z336,z84]),(0,[z985,z7,z1,z2,z4,z6]),(0,[z0,z7,z986,z2,z4,z6]),(0,[z0,z7,z987,z2,z4,z6]),(0,[z0,z7,z820,z4,z168,z6]),(0,[z0,z7,z1,z988,z2,z4])],[(0,[z67,z7,z34,z2,z4,z6]),(0,[z315,z17,z1,z2,z4,z6]),(0,[z0,z7,z989,z2,z4,z6]),(0,[z0,z7,z990,z1,z2,z4]),(0,[z233,z943,z1,z2,z4,z6])],[(0,[z0,z991,z1,z2,z4,z6]),(0,[z30,z0,z7,z31,z2,z4])],[(0,[z0,z33,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z992,z6]),(0,[z0,z7,z34,z2,z336,z6]),(0,[z0,z7,z839,z2,z4,z95])]],
   [[(0,[z0,z7,z993,z1,z2,z6]),(0,[z0,z7,z1,z2,z4,z994]),(0,[z47,z128,z48,z2,z4,z6]),(0,[z0,z7,z995,z1,z4,z6]),(0,[z996,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z997,z2,z6]),(0,[z0,z7,z1,z760,z6,z133])],[(0,[z0,z7,z998,z2,z4,z6]),(0,[z54,z211,z1,z2,z4,z55])],[(0,[z109,z11,z1,z2,z4,z6]),(0,[z368,z7,z68,z2,z4,z6]),(0,[z0,z7,z999,z2,z4,z6]),(0,[z72,z0,z7,z1,z2,z166]),(0,[z47,z0,z48,z2,z4,z6]),(0,[z0,z49,z1,z2,z5,z6]),(0,[z233,z955,z1,z2,z4,z6])],[(0,[z0,z7,z1000,z2,z4,z6]),(0,[z140,z382,z1,z2,z113,z6]),(1,[z7,z1,z2,z907,z6]),(0,[z0,z7,z990,z1,z2,z354]),(0,[z9,z0,z7,z1,z2,z298])]],
   [[(0,[z0,z162,z1,z2,z4,z6]),(0,[z65,z0,z1,z606,z4,z6]),(0,[z0,z1001,z1,z2,z4,z6]),(0,[z22,z7,z1,z249,z4,z84]),(0,[z1002,z7,z1,z2,z4,z6]),(1,[z0,z7,z1,z760,z6])],[(0,[z72,z7,z1,z2,z4,z23]),(0,[z72,z211,z7,z1,z2,z4]),(0,[z1003,z7,z1,z2,z4,z6]),(0,[z0,z1004,z1,z2,z4,z6])],[(0,[z64,z7,z1,z2,z4,z6]),(0,[z7,z11,z1,z249,z4,z6]),(0,[z0,z17,z1,z141,z4,z6]),(0,[z0,z1005,z1,z2,z4,z6]),(0,[z0,z7,z1,z1006,z4,z6]),(0,[z0,z1007,z1,z2,z4,z6]),(0,[z0,z162,z1,z249,z4,z6]),(0,[z9,z0,z7,z639,z1,z2]),(0,[z0,z1008,z1,z2,z4,z6]),(0,[z0,z7,z351,z31,z2,z4])],[(0,[z0,z7,z1009,z1,z4,z6]),(0,[z0,z7,z1010,z2,z4,z6]),(0,[z0,z7,z1,z2,z1011,z6]),(0,[z0,z1012,z1,z2,z4,z6]),(0,[z0,z7,z34,z249,z4,z6]),(0,[z1013,z7,z1,z2,z4,z6]),(0,[z1014,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z1015,z4,z6]),(0,[z65,z64,z1,z66,z4,z6]),(0,[z1016,z7,z1,z2,z4,z6])]],
   [[(0,[z0,z7,z1017,z1,z2,z4]),(0,[z7,z1,z2,z4,z6,z14]),(0,[z64,z24,z1,z2,z4,z6]),(0,[z0,z7,z1018,z1,z2,z6]),(0,[z0,z1019,z1,z2,z4,z6])],[(0,[z0,z7,z1020,z2,z4,z6]),(0,[z0,z1021,z7,z1,z2,z4]),(0,[z0,z83,z383,z2,z4,z6])],[(0,[z0,z1022,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z1023,z6]),(0,[z0,z7,z1,z774,z4,z6]),(0,[z0,z7,z1,z1024,z2,z4]),(0,[z0,z49,z1,z2,z709,z6]),(0,[z0,z7,z1,z2,z4,z1025]),(0,[z0,z7,z1,z94,z2,z15])],[(0,[z0,z7,z1,z1026,z4,z6]),(0,[z0,z7,z768,z2,z4,z6]),(0,[z22,z7,z326,z1,z2,z4]),(0,[z22,z0,z7,z1,z2,z166]),(0,[z0,z7,z1,z2,z709,z6]),(0,[z1027,z7,z1,z2,z4,z6]),(0,[z0,z1,z2,z354,z142,z6]),(0,[z0,z7,z1,z1028,z4,z6]),(0,[z0,z7,z1029,z1,z2,z6])]],
   [[(0,[z0,z7,z1,z2,z1030,z6]),(0,[z0,z7,z383,z104,z4,z6]),(0,[z7,z1,z2,z4,z23,z828]),(0,[z1031,z7,z1,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z1032]),(0,[z0,z1033,z7,z1,z2,z4])],[(0,[z30,z0,z7,z445,z2,z4]),(0,[z0,z1034,z1,z2,z4,z6]),(0,[z1035,z7,z1,z2,z4,z6]),(0,[z0,z86,z1,z25,z4,z6]),(0,[z0,z7,z1,z2,z756,z6]),(0,[z0,z7,z1,z1036,z2,z6])],[(0,[z292,z11,z1,z2,z4,z6]),(0,[z7,z1,z20,z778,z4,z6]),(0,[z382,z1,z2,z4,z23,z6]),(0,[z0,z1037,z1,z2,z4,z6]),(0,[z9,z0,z7,z358,z2,z6]),(0,[z0,z7,z100,z389,z2,z6]),(0,[z0,z7,z132,z1,z760,z6])],[(0,[z83,z11,z1,z2,z4,z6]),(0,[z412,z7,z89,z2,z4,z6]),(0,[z140,z7,z1,z2,z466,z6]),(0,[z0,z7,z1,z2,z684,z15]),(0,[z65,z128,z1,z2,z4,z6]),(0,[z0,z7,z708,z2,z4,z6]),(0,[z0,z49,z358,z2,z5,z6]),(0,[z0,z247,z1,z2,z4,z800]),(0,[z0,z7,z1,z2,z298,z4]),(0,[z0,z7,z1,z116,z2,z6])]],
   [[(0,[z0,z7,z1,z1038,z4,z6]),(0,[z0,z7,z1,z2,z466,z6]),(0,[z0,z7,z1039,z2,z4,z6]),(0,[z0,z7,z1,z2,z4,z1040]),(0,[z0,z7,z1,z2,z1041,z6])],[(0,[z7,z1,z2,z778,z4,z6]),(0,[z7,z1,z2,z4,z23,z491]),(0,[z22,z7,z1,z2,z4,z14]),(0,[z0,z7,z169,z1,z2,z50])],[(0,[z0,z52,z1,z2,z4,z6]),(0,[z0,z10,z1,z2,z4,z51]),(0,[z0,z1042,z7,z1,z2,z4]),(0,[z0,z1043,z1,z2,z4,z6]),(0,[z22,z7,z383,z2,z4,z84]),(0,[z0,z1044,z1,z2,z4,z6]),(0,[z0,z1,z2,z4,z1045,z6]),(0,[z7,z1,z2,z4,z6,z1046]),(0,[z0,z7,z776,z1,z2,z4])],[(0,[z0,z7,z1047,z1,z2,z4]),(0,[z101,z33,z68,z2,z4,z6]),(0,[z0,z1048,z1,z2,z4,z6]),(1,[z0,z1,z774,z4,z6]),(0,[z0,z7,z1049,z1,z4,z6]),(0,[z0,z7,z100,z1,z2,z50]),(0,[z9,z0,z7,z1,z94,z2]),(0,[z105,z0,z7,z80,z1,z116])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 4 128 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 554) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 554).take 479) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1033)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [554, 479] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 101).take 27).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [101, 27] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 4) (nb2 := 128) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_41398

theorem PEqualNP.Outside.L_meta_41398 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276142080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276142080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41398.solve