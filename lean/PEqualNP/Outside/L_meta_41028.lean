import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41028

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
  Nat.testBit (4276808426 * 2 ^ 32 + 4274571264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x00244c2b80f0f0ea#64 ++ 0x00009130ae03c3c3#64 ++ 0x027cfc7f81f1f1fd#64 ++ 0x9809f3f1fe07c7c7#64 : BitVec 256),
   (0x0c9125980617574c#64 ++ 0x0832449660185d5d#64 ++ 0x1d9327980e3ffffb#64 ++ 0xfc764c9e6038ffff#64 : BitVec 256),
   (0x6162c6e1b03a3a30#64 ++ 0x15858b1b86c0e8e8#64 ++ 0xe1e3c7e1f03e3e37#64 ++ 0xb7878f1f87c0f8f8#64 : BitVec 256),
   (0xb603f800db402d80#64 ++ 0x22d80fe0036d00b6#64 ++ 0xfe03f801ffc03fef#64 ++ 0xeff80fe007ff00ff#64 : BitVec 256),
   (0xdbfc00016dad8000#64 ++ 0x476ff00005b6b600#64 ++ 0xfffc0001ffffc01f#64 ++ 0xcffff00007ffff00#64 : BitVec 256),
   (0xffdbb35400000000#64 ++ 0x03ff6ecd50000000#64 ++ 0xfffffffe0000003f#64 ++ 0x73fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [3, 4]⟩, ⟨.and, [1, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [8, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [9, 12]⟩, ⟨.or, [13, 5]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9327980e3ffffb 0xfc764c9e6038ffff

def z1 : W := mkw 0x0cb56dbb86f7f7ee 0x0832d5b6ee1bdfdf 0x1fffffff8fffffff 0xfc7ffffffe3fffff

def z2 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3c7e1f03e3e37 0xb7878f1f87c0f8f8

def z3 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe3fffffff1ffffff 0xbf8fffffffc7ffff

def z4 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe03f801ffc03fef 0xeff80fe007ff00ff

def z5 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffc0001ffffc01f 0xcffff00007ffff00

def z6 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffffffe0000003f 0x73fffffff8000000

def z7 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027cfc7f81f1f1fd 0x9809f3f1fe07c7c7

def z8 : W := mkw 0x04256c2b82f0f5ea 0x001095b0ae0bc3d7 0x1e7ffc7f8ff1ffff 0xfc79fff1fe3fc7ff

def z9 : W := mkw 0xfbda935400000000 0x03ef6a4d50000000 0xe3fcdffe00000014 0x138ff37ff8000000

def z10 : W := mkw 0x000005980012524c 0x0800001660004949 0x0000079800000000 0x1000001e60000000

def z11 : W := mkw 0x922400016dad8000 0x4648900005b6b600 0xfe000001ffffc00f 0xcff8000007ffff00

def z12 : W := mkw 0x0401240802105548 0x0010049020084155 0x1c1324180e31fffb 0xfc704c906038c7ff

def z13 : W := mkw 0x0000048000121200 0x0000001200004848 0x01830780003e3e33 0xb4060c1e0000f8f8

def z14 : W := mkw 0x2002c00090002800 0x00800b00024000a0 0xe003c001f0003e27 0xa7800f0007c000f8

def z15 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xe203f801f1c03fe4 0x23880fe007c700ff

def z16 : W := mkw 0x0890000004050000 0x0022400000101400 0x1d9000000e3fc01b 0xcc7640000038ff00

def z17 : W := mkw 0xdffd25996fbfd74c 0x4f7ff49665beff5d 0xffff2799ffffffff 0xfffffc9e67ffffff

def z18 : W := mkw 0x49fc000124ad8000 0x4527f0000492b600 0x01fc0000003fc010 0x0007f0000000ff00

def z19 : W := mkw 0x9200000049000000 0x0248000001240000 0xfe000001ffc0000f 0xcff8000007ff0000

def z20 : W := mkw 0x0000040000101000 0x0000001000004040 0x0000040000303031 0x900000100000c0c0

def z21 : W := mkw 0x0024000124ad8000 0x440090000492b600 0x00000000003fc000 0x000000000000ff00

def z22 : W := mkw 0x49fc00016dad8000 0x4527f00005b6b600 0x01fc0001ffffc010 0x8c07f00007ffff00

def z23 : W := mkw 0x0024042b00b0d06a 0x00009010ac02c341 0x027cfc7e0031c03d 0x1009f3f1f800c700

def z24 : W := mkw 0x9e99311400000000 0x027a64c450000000 0x1e7cfc7e0000003d 0x5079f3f1f8000000

def z25 : W := mkw 0x0cb5259906b7d74c 0x0832d496641adf5d 0x1fff27998fffffff 0xfc7ffc9e663fffff

def z26 : W := mkw 0xfbfac6e1fd3f3a30 0x57efeb1b87f4fce8 0xfde3c7e1fe3e3e37 0xf7f78f1f87f8f8f8

def z27 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1830380700e0e02 0x27860c0e01c03838

def z28 : W := mkw 0x6df3e7f9b63f7f7c 0x1db7cf9fe6d8fdfd 0xfdf3e7f9fe3fffff 0xfff7cf9fe7f8ffff

def z29 : W := mkw 0x2403f80092402d80 0x20900fe0024900b6 0x0203f80181c03fed 0xa8080fe0060700ff

def z30 : W := mkw 0x2403b35400000000 0x00900ecd50000000 0x027ffffe0000003d 0x3009fffff8000000

def z31 : W := mkw 0x00004800db402d80 0x20000120036d00b6 0x0200f801ffc03fed 0x8c0803e007ff00ff

def z32 : W := mkw 0xf74bb35400000000 0x03dd2ecd50000000 0xe26ffffe00000024 0x3389bffff8000000

def z33 : W := mkw 0x41600481203a1200 0x050580120480e848 0xe1e30781f03e3e37 0xb7878c1e07c0f8f8

def z34 : W := mkw 0xffdbf7f490123a30 0x13ff6fdfd24048e8 0xfffffffe00003e3f 0x73fffffff80000f8

def z35 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x01932798003ffff0 0x30064c9e6000ffff

def z36 : W := mkw 0x0024042b00b0d06a 0x00009010ac02c341 0x007c047e0031c010 0x1001f011f800c700

def z37 : W := mkw 0x6142c2c0b00a2a10 0x15850b0b02c028a8 0xe183c381f00e3e27 0xa7860f0e07c038f8

def z38 : W := mkw 0xf763fee1fb7a3fb0 0x37dd8ffb87ede8fe 0xffe3ffe1fffe3fff 0xffff8fff87fff8ff

def z39 : W := mkw 0xb627f823dbe0ada2 0x22d89fe08f6f82b6 0xfe6ff867ffc03fef 0xeff9bfe19fff00ff

def z40 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfc030001ffc03fc2 0xeff00c0007ff00ff

def z41 : W := mkw 0x9a9c00004d858000 0x426a700001361600 0xfe1c0001ffc1c00f 0xcff8700007ff0700

def z42 : W := mkw 0x2403fb5492402d80 0x20900fed524900b6 0x0003fffe00003fe0 0x30000ffff80000ff

def z43 : W := mkw 0xd348000069080000 0x474d200001a42000 0xe000000070000000 0x0380000001c00000

def z44 : W := mkw 0x0020042100301020 0x000080108400c040 0x0060046000300010 0x100180118000c000

def z45 : W := mkw 0x00244c2380f0b0a2 0x000091308e03c2c2 0x026cdc6781f03035 0x9009b3719e07c0c0

def z46 : W := mkw 0x4160000120280000 0x050580000480a000 0xe0600001f0000004 0x0381800007c00000

def z47 : W := mkw 0x0401200002000500 0x0010048000080014 0x1c0320000e003feb 0xec700c80003800ff

def z48 : W := mkw 0x2427fc2b92f0fdea 0x20909ff0ae4bc3f7 0x027ffc7f81f1fffd 0xb809fff1fe07c7ff

def z49 : W := mkw 0xb603b00000000000 0x02d80ec000000000 0xfe03f8000000002f 0x63f80fe000000000

def z50 : W := mkw 0xffdbfb54db402d80 0x23ff6fed536d00b6 0xffffffffffc03fff 0xffffffffffff00ff

def z51 : W := mkw 0x040125980617574c 0x0810049660185d5d 0x000327980e3fffe0 0xbc000c9e6038ffff

def z52 : W := mkw 0x0cb525996fbfd74c 0x4c32d49665beff5d 0x1d932799fffffffb 0xfc764c9e67ffffff

def z53 : W := mkw 0x6142824030080810 0x15850a0900c02020 0xe000000070000000 0x0380000001c00000

def z54 : W := mkw 0x49fc059924bfd24c 0x4d27f0166492ff49 0x01fc0798003fc010 0x1007f01e6000ff00

def z55 : W := mkw 0xb202c000d9002800 0x02c80b00036400a0 0xfe03c001ffc03e2f 0xeff80f0007ff00f8

def z56 : W := mkw 0x00244c2bedfdf0ea 0x44009130afb7f7c3 0x00000001fffff1c0 0x8c00000007ffffc7

def z57 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d8303800e3fffc2 0xec760c0e0038ffff

def z58 : W := mkw 0x0c9121180605454c 0x0832448460181515 0x1c1020180e01c1c8 0x4870408060380707

def z59 : W := mkw 0x6162c261b0282830 0x15858b0986c0a0a0 0xe060c061f0000004 0x0381830187c00000

def z60 : W := mkw 0x04256dbb82f2f7ee 0x081095b6ee0bcbdf 0x027fffff81f1fffd 0xb809fffffe07c7ff

def z61 : W := mkw 0xb202d800d9402880 0x22c80b60036500a2 0xe200d801f1c00004 0x0388036007c70000

def z62 : W := mkw 0x6142c6e0b01a3a30 0x15850b1b82c068e8 0xe183c7e0700e3e22 0x37860f1f81c038f8

def z63 : W := mkw 0x2c93e7f896177f7c 0x18b24f9fe2585dfd 0x1d93e7f80e3ffffb 0xfc764f9fe038ffff

def z64 : W := mkw 0x9e99311400000000 0x027a64c450000000 0x1e1c381e00000008 0x407870e078000000

def z65 : W := mkw 0x0401219002020704 0x081004864008081c 0x0003038000000e00 0x20000c0e00000038

def z66 : W := mkw 0xfffbf77580303020 0x03ffefddd600c0c0 0xffffffff8030303f 0xf3fffffffe00c0c0

def z67 : W := mkw 0x6142824000000000 0x01850a0900000000 0xe3fffffe0000003f 0x338ffffff8000000

def z68 : W := mkw 0xb603b8004b400580 0x22d80ee0012d0016 0xfe03f8000fc001ef 0x6bf80fe0003f0007

def z69 : W := mkw 0xffdbb35449000000 0x03ff6ecd51240000 0xffffffffffc0003f 0xffffffffffff0000

def z70 : W := mkw 0x6162cee1b07a3ab0 0x15858b3b86c1e8ea 0xe3e3ffe1f1fe3fff 0xbf8f8fff87c7f8ff

def z71 : W := mkw 0x2403b00012000d00 0x20900ec000480034 0x0003000000000e00 0x20000c0000000038

def z72 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe1e3c7e1f1fffff7 0xbf878f1f87c7ffff

def z73 : W := mkw 0x2403f800db402d80 0x20900fe0036d00b6 0x0003f801ffc03fe0 0xac000fe007ff00ff

def z74 : W := mkw 0x0000480080402080 0x0000012002010082 0x0200f80181c031ed 0x880803e0060700c7

def z75 : W := mkw 0x0024000100a08000 0x0000900004028200 0x027c000181f1c01d 0x8809f0000607c700

def z76 : W := mkw 0xdbfc4c2bedfdf0ea 0x476ff130afb7f7c3 0xfffcfc7ffffff1ff 0xdffff3f1ffffffc7

def z77 : W := mkw 0x040125980212574c 0x081004966008495d 0x0003279800003fe0 0x30000c9e600000ff

def z78 : W := mkw 0xd36c000169a88000 0x474db00005a6a200 0xe26c0001f1c00004 0x0389b00007c70000

def z79 : W := mkw 0x040125980212574c 0x081004966008495d 0x01832798003e3ff3 0xb4060c9e6000f8ff

def z80 : W := mkw 0x6df7effbb6fffffe 0x1db7dfbfeedbffff 0xffffffffffffffff 0xffffffffffffffff

def z81 : W := mkw 0x6162ceebb07a7afa 0x15858b3baec1e9eb 0xe1e3fffff03e3ff7 0xb7878fffffc0f8ff

def z82 : W := mkw 0x0401200002000500 0x0010048000080014 0x0003200000003fe0 0x20000c80000000ff

def z83 : W := mkw 0x0890040804155048 0x0022401020105541 0x1d9024180e3ff1fb 0xdc7640906038ffc7

def z84 : W := mkw 0xb603b0005b000d00 0x22d80ec0016c0034 0xfc0300007e000e02 0x67f00c0001f80038

def z85 : W := mkw 0xb627fc2bdbf0fdea 0x22d89ff0af6fc3f7 0xfe7ffc7ffff1ffff 0xfff9fff1ffffc7ff

def z86 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1830381f03e3e02 0xa7860c0e07c0f8f8

def z87 : W := mkw 0x2c93b35400000000 0x00b24ecd50000000 0x1d93fffe0000003b 0x70764ffff8000000

def z88 : W := mkw 0x49d8035400000000 0x0127600d50000000 0x01fc07fe00000010 0x1007f01ff8000000

def z89 : W := mkw 0xf34a924400000000 0x03cd2a4910000000 0xe26cd86600000004 0x0389b36198000000

def z90 : W := mkw 0x002044a1b03a3a30 0x1400811286c0e8e8 0x00000001f03e3e00 0x8400000007c0f8f8

def z91 : W := mkw 0x9e9d21184f85c54c 0x4a7a7484613e1715 0x1e1c20180fc1c1c8 0x48787080603f0707

def z92 : W := mkw 0x4164000120a88000 0x050590000482a200 0xe3fc0001f1ffc01f 0x8f8ff00007c7ff00

def z93 : W := mkw 0xdbfc000100a08000 0x036ff00004028200 0xfffc000181f1c01f 0xcbfff0000607c700

def z94 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x0000000181f1f1c0 0x880000000607c7c7

def z95 : W := mkw 0x0c91211000000000 0x0032448440000000 0x1d9327980000003b 0x70764c9e60000000

def z96 : W := mkw 0xffffb3556dad8000 0x47fffecd55b6b600 0xffff0381ffffc01f 0xeffffc0e07ffff00

def z97 : W := mkw 0x4160000120280000 0x050580000480a000 0xe1e00001f03e0017 0x8787800007c0f800

def z98 : W := mkw 0xfbfec6e1fdbfba30 0x57effb1b87f6fee8 0xffffc7e1fffffe3f 0xffffff1f87fffff8

def z99 : W := mkw 0xdbd800006d0d0000 0x476f600001b43400 0xff800001ffce000f 0xcffe000007ff3800

def z100 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027c000181f1f1dd 0x8809f0000607c7c7

def z101 : W := mkw 0x0000040800105048 0x0000001020004141 0x001024180031f1f9 0x980040906000c7c7

def z102 : W := mkw 0x69f2c7f9b43f7a7c 0x1da7cb1fe6d0fde9 0xe1f3c7f9f03ffe37 0xb787cf1fe7c0fff8

def z103 : W := mkw 0x0024000169a88000 0x4400900005a6a200 0x00000001f1c00000 0x0000000007c70000

def z104 : W := mkw 0x416006e1203a1230 0x1505801b8480e848 0x01e007e0003e0010 0x1007801f8000f800

def z105 : W := mkw 0x960138004b400580 0x225804e0012d0016 0x1e0038000fc001c8 0x487800e0003f0007

def z106 : W := mkw 0xf36ed801f9e8a880 0x67cdbb6007e7a2a2 0xe26cd801f1c00004 0x0389b36007c70000

def z107 : W := mkw 0x92004800db402d80 0x22480120036d00b6 0xfe000001ffc03fcf 0xcff8000007ff00ff

def z108 : W := mkw 0xffdbb7dc0617574c 0x0bff6edf70185d5d 0xfffffffe0e3fffff 0xfffffffff838ffff

def z109 : W := mkw 0xffdbb3d4300a0a10 0x17ff6ecf50c02828 0xfffffffe700e0e3f 0x77fffffff9c03838

def z110 : W := mkw 0xffdfb3544d858000 0x43ff7ecd51361600 0xfffffffe0fc1c03f 0x7bfffffff83f0700

def z111 : W := mkw 0x6df3e7f1b63f3f34 0x1db7cf9fc6d8fcfc 0xfde3c7e1fe3e3e37 0xf7f78f1f87f8f8f8

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0x027cfc7e0000003d 0x1009f3f1f8000000

def z113 : W := mkw 0xffffff7f80f0f0ea 0x03fffffdfe03c3c3 0xffffffff81f1f1ff 0xfbfffffffe07c7c7

def z114 : W := mkw 0x6162c261b0282830 0x15858b0986c0a0a0 0xe1e0c061f03e0017 0x8787830187c0f800

def z115 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0000001f0000007 0x8780000007c00000

def z116 : W := mkw 0x9a9c00004d858000 0x426a700001361600 0x1e1c00000fc1c008 0x48787000003f0700

def z117 : W := mkw 0x002400016dad8000 0x4400900005b6b600 0x00000001ffffc000 0x8c00000007ffff00

def z118 : W := mkw 0x2403b35400000000 0x00900ecd50000000 0x0003fffe00000020 0x30000ffff8000000

def z119 : W := mkw 0x0000080000400080 0x0000002000010002 0x0200380001c001c8 0x080800e000070007

def z120 : W := mkw 0x08b44dbb84f7f2ee 0x0822d136ee13dfcb 0x03fcffff81fff1fd 0x980ff3fffe07ffc7

def z121 : W := mkw 0x49fc4c2ba4fdf0ea 0x4527f130ae93f7c3 0x03fcfc7f81fff1fd 0x980ff3f1fe07ffc7

def z122 : W := mkw 0xffffb3556dad8000 0x47fffecd55b6b600 0xffffffffffffc03f 0xffffffffffffff00

def z123 : W := mkw 0x089005980417524c 0x0822401660105d49 0x01902798003ff1f9 0x9806409e6000ffc7

def z124 : W := mkw 0x49d8035400000000 0x0127600d50000000 0x03fcfffe0000003d 0x100ff3fff8000000

def z125 : W := mkw 0x9a9000004d050000 0x026a400001341400 0xff900001ffffc01f 0xcffe400007ffff00

def z126 : W := mkw 0xbe93fd98df577fcc 0x2afa4ff6637d5dff 0xff93ff99ffffffff 0xfffe4ffe67ffffff

def z127 : W := mkw 0xdbfc05996dbfd24c 0x4f6ff01665b6ff49 0xfffc0799ffffc01f 0xdffff01e67ffff00

def z128 : W := mkw 0xfffbb7f5203a1230 0x17ffeedfd480e848 0xfffffffe003e003f 0x73fffffff800f800

def z129 : W := mkw 0x0890019004070204 0x0822400640101c08 0x01800380000e0000 0x0006000e00003800

def z130 : W := mkw 0x0004080a00c0c0ca 0x0000102028030303 0x021c381e01c1c1c8 0x080870e078070707

def z131 : W := mkw 0x9224000149a08000 0x0248900005268200 0xfe7c0001fff1c01f 0xcff9f00007ffc700

def z132 : W := mkw 0x000004880617574c 0x0800001220185d5d 0x000000000e3fffc0 0x8c0000000038ffff

def z133 : W := mkw 0x0024482380e0a0a2 0x000091208e038282 0x0000000181c00000 0x0000000006070000

def z134 : W := mkw 0x0024482380e0a0a2 0x000091208e038282 0x026cd86781c00004 0x0009b3619e070000

def z135 : W := mkw 0xffffb77f00b0d06a 0x03fffeddfc02c341 0xfffffffe0031c03f 0x73fffffff800c700

def z136 : W := mkw 0x089005980417524c 0x0822401660105d49 0x01900798003fc010 0x1006401e6000ff00

def z137 : W := mkw 0x49d80000240d0000 0x4527600000903400 0x01800000000e0000 0x0006000000003800

def z138 : W := mkw 0x000000080605454c 0x0800000020181515 0x000000000e01c1c0 0x0800000000380707

def z139 : W := mkw 0xfffbb35520280000 0x07ffeecd5480a000 0xfffffffff03e003f 0xf7ffffffffc0f800

def z140 : W := mkw 0x2403b00000000000 0x00900ec000000000 0x0003f80000000020 0x20000fe000000000

def z141 : W := mkw 0x0000480092402d80 0x20000120024900b6 0x0000000000003fc0 0x00000000000000ff

def z142 : W := mkw 0xdbfc03556dad8000 0x476ff00d55b6b600 0xfffc07ffffffc01f 0xdffff01fffffff00

def z143 : W := mkw 0x9e9d38004fc58580 0x627a74e0013f1616 0x1e1c38000fc1c1c8 0x487870e0003f0707

def z144 : W := mkw 0xbe93b5980617574c 0x0afa4ed660185d5d 0xff93ff980e3fffff 0xfffe4ffe6038ffff

def z145 : W := mkw 0x0000480080402080 0x0000012002010082 0x027cfc7f81c031fd 0x9809f3f1fe0700c7

def z146 : W := mkw 0x0024480180e0a080 0x0000912006038282 0x027cf80181f1f1fd 0x8809f3e00607c7c7

def z147 : W := mkw 0x2403f80092402d80 0x20900fe0024900b6 0x0003f80000003fe0 0x20000fe0000000ff

def z148 : W := mkw 0x416046e1b03a3a30 0x1505811b86c0e8e8 0x01e007e1f03e3e10 0x9407801f87c0f8f8

def z149 : W := mkw 0xfffffb7780e0a0a2 0x03ffffedde038282 0xffffffff81c0003f 0x73fffffffe070000

def z150 : W := mkw 0x6166ca63b0e8a8b2 0x15859b298ec3a2a2 0xe26cd867f1c00004 0x0389b3619fc70000

def z151 : W := mkw 0xb226d823d9e0a8a2 0x22c89b608f6782a2 0xe26cd867f1c00004 0x0389b3619fc70000

def z152 : W := mkw 0xd36c4823e9e8a0a2 0x474db1208fa7a282 0xe26cd867f1c00004 0x0389b3619fc70000

def z153 : W := mkw 0x49fc042b24bdd06a 0x4527f010ac92f741 0x01fc047e003fc010 0x1007f011f800ff00

def z154 : W := mkw 0xdbd800006d0d0000 0x476f600001b43400 0xfffc00007e0e001f 0x47fff00001f83800

def z155 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0x1e03f8000fc03fe8 0x68780fe0003f00ff

def z156 : W := mkw 0x0890048004171200 0x0022401200105c48 0x1d9307800e3ffe3b 0xfc764c1e0038fff8

def z157 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xffec0001ffce0006 0x47ffb00007ff3800

def z158 : W := mkw 0x0020442180303020 0x000081108600c0c0 0x0060c46180303035 0x900183118600c0c0

def z159 : W := mkw 0x6563e7f9b23a7f7c 0x1d958f9fe6c8e9fd 0xe1e3e7f9f03e3ff7 0xb7878f9fe7c0f8ff

def z160 : W := mkw 0x2002c6e090123a30 0x10800b1b824048e8 0x0003c7e000003e20 0x30000f1f800000f8

def z161 : W := mkw 0x0c91211002000500 0x0032448440080014 0x1d9327980e003ffb 0xfc764c9e603800ff

def z162 : W := mkw 0x00004800db402d80 0x20000120036d00b6 0x00000001ffc03fc0 0x8c00000007ff00ff

def z163 : W := mkw 0xffdbb3545b000d00 0x23ff6ecd516c0034 0xfffffffe7e000e3f 0x77fffffff9f80038

def z164 : W := mkw 0xdbfc000124ad8000 0x476ff0000492b600 0xfffc0000003fc01f 0x43fff0000000ff00

def z165 : W := mkw 0x0020442180303020 0x000081108600c0c0 0x027cfc7f8030303d 0x9009f3f1fe00c0c0

def z166 : W := mkw 0x00244cab80f2f2ea 0x00009132ae03cbcb 0x03ffffff81ffffff 0xbc0ffffffe07ffff

def z167 : W := mkw 0x6162c661b0383830 0x15858b1986c0e0e0 0xe060c461f0303035 0x9381831187c0c0c0

def z168 : W := mkw 0x0cb525bb06b7d76e 0x0832d496ec1adf5d 0x1dff27fe0e3ffffb 0xfc77fc9ff838ffff

def z169 : W := mkw 0xf743b24000000000 0x03dd0ec900000000 0xffe3ffe00000003f 0x73ff8fff80000000

def z170 : W := mkw 0x0c916d98df577fcc 0x283245b6637d5dff 0x1d932799fffffffb 0xfc764c9e67ffffff

def z171 : W := mkw 0x6166c6e1b0baba30 0x15859b1b86c2eae8 0xe3ffc7e1f1fffe3f 0xbf8fff1f87c7fff8

def z172 : W := mkw 0x2002824000000000 0x00800a0900000000 0x0003c7e000000020 0x30000f1f80000000

def z173 : W := mkw 0x0000400080002000 0x0000010002000080 0x0000c00180003025 0x80000300060000c0

def z174 : W := mkw 0x6142824000000000 0x01850a0900000000 0xe1e3c7e000000037 0x33878f1f80000000

def z175 : W := mkw 0x0024442180b0b020 0x000091108602c2c0 0x027cc46181f1f03d 0x9809f3118607c7c0

def z176 : W := mkw 0xfffff7f5fdbfba30 0x57ffffdfd7f6fee8 0xfffffffffffffe3f 0xfffffffffffffff8

def z177 : W := mkw 0x0c91259000121200 0x0032449640004848 0x1d932798003e3e3b 0xf4764c9e6000f8f8

def z178 : W := mkw 0xffffb35524ad8000 0x47fffecd5492b600 0xfffffffe003fc03f 0x73fffffff800ff00

def z179 : W := mkw 0x000000005b000d00 0x20000000016c0034 0x000000007e000e00 0x0400000001f80038

def z180 : W := mkw 0xf34ada44d9402880 0x23cd2b69136500a2 0xe26cd867f1c00004 0x0389b3619fc70000

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z182 : W := mkw 0x2002800010000800 0x00800a0000400020 0xe003000070000e02 0x27800c0001c00038

def z183 : W := mkw 0x69f2c6e1b43f3a30 0x15a7cb1b86d0fce8 0xfdf3c7e1fe3ffe3f 0xfff7cf1f87f8fff8

def z184 : W := mkw 0x08b4000104a58000 0x0022d00004129600 0x1ffc00018fffc01f 0xcc7ff000063fff00

def z185 : W := mkw 0x2403fc2a92507dea 0x20900ff0aa4941f7 0x0003fc7e00003fe0 0x30000ff1f80000ff

def z186 : W := mkw 0x6df3e7f1b03a3a30 0x15b7cf9fc6c0e8e8 0xfdf3e7f9f03e3e3f 0xf7f7cf9fe7c0f8f8

def z187 : W := mkw 0xffdbffdcdf577fcc 0x2bff6fff737d5dff 0xffffffffffffffff 0xffffffffffffffff

def z188 : W := mkw 0x6162c261b0282830 0x15858b0986c0a0a0 0xe1e3c7e1f0000037 0x33878f1f87c00000

def z189 : W := mkw 0x2026ceeb90f2fafa 0x10809b3bae43cbeb 0x027fffff81f1fffd 0xb809fffffe07c7ff

def z190 : W := mkw 0x9e9125984f17574c 0x0a7a4496613c5d5d 0xff932799ffffffff 0xfffe4c9e67ffffff

def z191 : W := mkw 0x0cb56dbb86f7f7ee 0x0832d5b6ee1bdfdf 0x1d9327998ffffffb 0xfc764c9e663fffff

def z192 : W := mkw 0x0000000002000500 0x0000000000080014 0x000000000e003fc0 0x8c000000003800ff

def z193 : W := mkw 0x4160000120280000 0x050580000480a000 0x01e00000003e0010 0x000780000000f800

def z194 : W := mkw 0x0000008000020200 0x0000000200000808 0x01830380000e0e02 0x24060c0e00003838

def z195 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfd800001ffffc002 0xcff6000007ffff00

def z196 : W := mkw 0x9e9d391e00c0c0ca 0x027a74e478030303 0x1e1c381e01c1c1c8 0x487870e078070707

def z197 : W := mkw 0x0c91211004050000 0x0032448440101400 0x1d9327980e3fc03b 0xfc764c9e6038ff00

def z198 : W := mkw 0x0000040800105048 0x0000001020004141 0x00002418000031e0 0x10000090600000c7

def z199 : W := mkw 0x49f807f5203a1230 0x1527e01fd480e848 0x01fc07fe003e0010 0x1007f01ff800f800

def z200 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfd83038000000002 0x63f60c0e00000000

def z201 : W := mkw 0x0000000000000000 0x0000000000000000 0x1c0000000e00000b 0xcc70000000380000

def z202 : W := mkw 0x0cb165b9b63f7f7c 0x1c32c596e6d8fdfd 0x1d932799fe3ffffb 0xfc764c9e67f8ffff

def z203 : W := mkw 0x0c91211000000000 0x0032448440000000 0x1ffffffe0000003f 0x707ffffff8000000

def z204 : W := mkw 0x416006e1203a1230 0x1505801b8480e848 0x01e307e0003e3e33 0xb4078c1f8000f8f8

def z205 : W := mkw 0x2c93b7dc0617574c 0x08b24edf70185d5d 0x1d93fffe0e3ffffb 0xfc764ffff838ffff

def z206 : W := mkw 0xdbd800006d0d0000 0x476f600001b43400 0xfd8000007e0e0002 0x47f6000001f83800

def z207 : W := mkw 0x6162c261b0282830 0x15858b0986c0a0a0 0xe063c061f0003e27 0xa7818f0187c000f8

def z208 : W := mkw 0xf76ff801fbe8ad80 0x67ddbfe007efa2b6 0xfe6ff801ffc03fef 0xeff9bfe007ff00ff

def z209 : W := mkw 0xffdbb0007f0d0d00 0x67ff6ec001fc3434 0xfd8300007e0e0e02 0x67f60c0001f83838

def z210 : W := mkw 0xdbfc4421edbdb020 0x476ff11087b6f6c0 0xfffcc461fffff03f 0xdffff31187ffffc0

def z211 : W := mkw 0x0004000a0080c04a 0x0000100028020301 0x001c001e0001c000 0x0000700078000700

def z212 : W := mkw 0x00004c88df577fcc 0x28000132237d5dff 0x00000001ffffffc0 0x8c00000007ffffff

def z213 : W := mkw 0x04016dba825277ee 0x081005b6ea0949df 0x0003fffe00003fe0 0x30000ffff80000ff

def z214 : W := mkw 0x0024000100a08000 0x0000900004028200 0x0000000181f1c000 0x880000000607c700

def z215 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe7ffc7fffc03fff 0xfff9fff1ffff00ff

def z216 : W := mkw 0xfffbf375b0282830 0x17ffefcdd6c0a0a0 0xfffffffff000003f 0x73ffffffffc00000

def z217 : W := mkw 0x416006e1203a1230 0x1505801b8480e848 0xe1e007e1f03e0017 0x9787801f87c0f800

def z218 : W := mkw 0xb603fb54db402d80 0x22d80fed536d00b6 0xfe03ffffffc03fef 0xfff80fffffff00ff

def z219 : W := mkw 0x9e99311400000000 0x027a64c450000000 0x1c00000000000000 0x4070000000000000

def z220 : W := mkw 0x4140000020080000 0x0505000000802000 0xe1800000700e0002 0x0786000001c03800

def z221 : W := mkw 0x6563e6e1b23a3f30 0x15958f9b86c8e8fc 0xfde3e7e1fe3e3fff 0xfff78f9f87f8f8ff

def z222 : W := mkw 0x6166ce6b80f0f0ea 0x01859b39ae03c3c3 0xe3ffffff81f1f1ff 0xbb8ffffffe07c7c7

def z223 : W := mkw 0x9e99359c0617574c 0x0a7a64d670185d5d 0x1f9f3f9e0e3ffffb 0xfc7e7cfe7838ffff

def z224 : W := mkw 0x9605380a4bc0c5ca 0x225814e0292f0317 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z225 : W := mkw 0x9a9c00004d858000 0x426a700001361600 0x1f9c00000fffc01b 0xcc7e7000003fff00

def z226 : W := mkw 0x000044a090123a30 0x10000112824048e8 0x0000000000003e00 0x00000000000000f8

def z227 : W := mkw 0xdfd9311400000000 0x037f64c450000000 0xfffc381e0000001f 0x43fff0e078000000

def z228 : W := mkw 0xb603b0005b000d00 0x22d80ec0016c0034 0xfc0320007e003feb 0xeff00c8001f800ff

def z229 : W := mkw 0xf767feebfbfafffa 0x37dd9ffbafefebff 0xffffffffffffffff 0xffffffffffffffff

def z230 : W := mkw 0x002004a1203a1230 0x140080128480e848 0x00000000003e0000 0x000000000000f800

def z231 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x007cfc7e0031f1f0 0x1001f3f1f800c7c7

def z232 : W := mkw 0x6162c001b0282800 0x05858b0006c0a0a0 0xe1e3c001f03e3e37 0xa7878f0007c0f8f8

def z233 : W := mkw 0x6142824000000000 0x01850a0900000000 0xe183038000000002 0x23860c0e00000000

def z234 : W := mkw 0xb603b00000000000 0x02d80ec000000000 0xfe7ffc7e0000003f 0x73f9fff1f8000000

def z235 : W := mkw 0x960138004b400580 0x225804e0012d0016 0x1e0338000fc03feb 0xec780ce0003f00ff

def z236 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9307980e3fce12 0x74764c1e6038ff38

def z237 : W := mkw 0x9a9c080a4dc5c0ca 0x426a702029371703 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z238 : W := mkw 0xb603fc2adb507dea 0x22d80ff0ab6d41f7 0xfe03fc7fffc03fef 0xfff80ff1ffff00ff

def z239 : W := mkw 0x9200000049000000 0x0248000001240000 0xe2000001f1c00004 0x0388000007c70000

def z240 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x0060c46181f1f1f5 0x980183118607c7c7

def z241 : W := mkw 0x960130004b000500 0x225804c0012c0014 0x1c0000000e000000 0x4070000000380000

def z242 : W := mkw 0xffdbb3546d0d0000 0x47ff6ecd51b43400 0xfffffffe7e0e003f 0x77fffffff9f83800

def z243 : W := mkw 0xdbd8000000000000 0x036f600000000000 0xfffc00000000001f 0x43fff00000000000

def z244 : W := mkw 0x040121180200454c 0x0810048460080115 0x00002018000001c0 0x0000008060000007

def z245 : W := mkw 0xfbda924400000000 0x03ef6a4910000000 0xfffcd8660000001f 0x43fff36198000000

def z246 : W := mkw 0x2c93fd9896577fcc 0x28b24ff662595dff 0x1d93ff980e3ffffb 0xfc764ffe6038ffff

def z247 : W := mkw 0xb603f80092402d80 0x22d80fe0024900b6 0xfe03f80000003fef 0x63f80fe0000000ff

def z248 : W := mkw 0xfffbf7f5b03a3a30 0x17ffefdfd6c0e8e8 0xfffffffff03e3e3f 0xf7ffffffffc0f8f8

def z249 : W := mkw 0x49fc035524ad8000 0x4527f00d5492b600 0x01fc07fe003fc010 0x1007f01ff800ff00

def z250 : W := mkw 0x6166c6ebb0bafa7a 0x15859b1baec2ebe9 0xe1ffc7fff03ffe37 0xb787ff1fffc0fff8

def z251 : W := mkw 0x2403fd9892527fcc 0x28900ff6624949ff 0x0003ff9800003fe0 0x30000ffe600000ff

def z252 : W := mkw 0x0401380002400580 0x201004e000090016 0x00003800000001c0 0x000000e000000007

def z253 : W := mkw 0x9a9800004d050000 0x426a600001341400 0x1c0000000e000000 0x4070000000380000

def z254 : W := mkw 0xfffffc2bfffdfdea 0x67fffff0affff7f7 0xfffffc7fffffffff 0xfffffff1ffffffff

def z255 : W := mkw 0x2002ceea90527afa 0x10800b3baa4149eb 0x0003fffe00003fe0 0x30000ffff80000ff

def z256 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfde3c7e000000037 0x73f78f1f80000000

def z257 : W := mkw 0x2022c42190303820 0x00808b108640c0e0 0xe063c461f0303e37 0xb7818f1187c0c0f8

def z258 : W := mkw 0xffdbff7e805070ea 0x03ff6ffdfa0141c3 0xfffffffe000031ff 0x73fffffff80000c7

def z259 : W := mkw 0xf74bfa44db402d80 0x23dd2fe9136d00b6 0xfe6ff867ffc03fef 0xeff9bfe19fff00ff

def z260 : W := mkw 0x49fc000124ad8000 0x4527f0000492b600 0xe1fc0001f03fc017 0x8787f00007c0ff00

def z261 : W := mkw 0x0401200002000500 0x0010048000080014 0x1c0300000e000e02 0x64700c0000380038

def z262 : W := mkw 0x002044a1b03a3a30 0x1400811286c0e8e8 0x01830781f03e3e33 0xb4060c1e07c0f8f8

def z263 : W := mkw 0x9601300000000000 0x025804c000000000 0x1e00380000000008 0x407800e000000000

def z264 : W := mkw 0x6563f7f5b03a3a30 0x15958fdfd6c0e8e8 0xe1e3fffff03e3e37 0xb7878fffffc0f8f8

def z265 : W := mkw 0xfbfe82c17daf8a10 0x57effa0b05f6be28 0xffff0381ffffce1f 0xeffffc0e07ffff38

def z266 : W := mkw 0x6162c2e1b02a2a30 0x15858b0b86c0a8a8 0xe1e3c3e1f00e0e06 0x27878f0f87c03838

def z267 : W := mkw 0xf36eda6780e0a0a2 0x03cdbb699e038282 0xe26cd86781c00004 0x0389b3619e070000

def z268 : W := mkw 0x00000080300a0a10 0x1400000200c02828 0x00000000700e0e00 0x0400000001c03838

def z269 : W := mkw 0xd36c00016dad8000 0x474db00005b6b600 0xe26c0001ffffc004 0x8f89b00007ffff00

def z270 : W := mkw 0x0000000000000000 0x0000000000000000 0x026cd86600000004 0x0009b36198000000

def z271 : W := mkw 0x0c91219006070704 0x0832448640181c1c 0x1d8303800e0e0e02 0x64760c0e00383838

def z272 : W := mkw 0xf763f6e1fb3a3f30 0x37dd8fdb87ece8fc 0xfde3c7e1fe3e3e37 0xf7f78f1f87f8f8f8

def z273 : W := mkw 0x2403f80092402d80 0x20900fe0024900b6 0xe003f801f0003fe7 0xa7800fe007c000ff

def z274 : W := mkw 0x6dd3a7d80617574c 0x09b74e9f60185d5d 0xfdf3e7f80e3fffff 0xfff7cf9fe038ffff

def z275 : W := mkw 0x616286e1303a1a30 0x15858a1b84c0e868 0xe1e307e0703e0e12 0x37878c1f81c0f838

def z276 : W := mkw 0xbe93b11000000000 0x02fa4ec440000000 0xff93ff980000003f 0x73fe4ffe60000000

def z277 : W := mkw 0x00244cabb0fafafa 0x14009132aec3ebeb 0x027cfc7ff1fffffd 0x9c09f3f1ffc7ffff

def z278 : W := mkw 0x089005980417524c 0x0822401660105d49 0x1d9007980e3fc01b 0xdc76401e6038ff00

def z279 : W := mkw 0x00004c2a805070ea 0x00000130aa0141c3 0x0200fc7f81c031ed 0x980803f1fe0700c7

def z280 : W := mkw 0xffffffffb0fafafa 0x17fffffffec3ebeb 0xfffffffff1ffffff 0xffffffffffc7ffff

def z281 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfd83fffe00000022 0x73f60ffff8000000

def z282 : W := mkw 0x0890000004050000 0x0022400000101400 0x1c1000000e01c008 0x4870400000380700

def z283 : W := mkw 0x00044c2a80d0f0ea 0x00001130aa0343c3 0x021cfc7e01c1f1e8 0x180873f1f80707c7

def z284 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x0200f80181f1f1ed 0x880803e00607c7c7

def z285 : W := mkw 0x08b44c2b84f5f0ea 0x0022d130ae13d7c3 0x1ffcfc7f8ffff1ff 0xdc7ff3f1fe3fffc7

def z286 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe3fffffff03e3e3f 0xb78fffffffc0f8f8

def z287 : W := mkw 0x0024042b00b0d06a 0x00009010ac02c341 0x007c247e0031f1f9 0x9801f091f800c7c7

def z288 : W := mkw 0x0890000004050000 0x0022400000101400 0x1d8000000e0e0002 0x4476000000383800

def z289 : W := mkw 0x000008004b400580 0x20000020012d0016 0x000000000fc001c0 0x08000000003f0007

def z290 : W := mkw 0xdbd8000049000000 0x036f600001240000 0xfffc0001ffc0001f 0xcffff00007ff0000

def z291 : W := mkw 0x089004880617574c 0x0822401220185d5d 0x1d9000000e3fffdb 0xcc7640000038ffff

def z292 : W := mkw 0x00004c2a805070ea 0x00000130aa0141c3 0x00000000000031c0 0x00000000000000c7

def z293 : W := mkw 0x0024482b80e0e0ea 0x00009120ae038383 0x027cf87f81c1c1cc 0x0809f3e1fe070707

def z294 : W := mkw 0xb202900000000000 0x02c80a4000000000 0xe200d80000000004 0x0388036000000000

def z295 : W := mkw 0x6543b35400000000 0x01950ecd50000000 0xe1e3fffe00000037 0x33878ffff8000000

def z296 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1c1020180e3fffc8 0xcc7040806038ffff

def z297 : W := mkw 0x0000040800105048 0x0000001020004141 0x001004180031c010 0x100040106000c700

def z298 : W := mkw 0xfffff801ffedad80 0x67ffffe007ffb6b6 0xfffff801ffffffff 0xefffffe007ffffff

def z299 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffcfc7fffffc03f 0xdffff3f1ffffff00

def z300 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e0c7e1f03e0014 0x1387831f87c0f800

def z301 : W := mkw 0x00004c2a805070ea 0x00000130aa0141c3 0x0010fc7e0031f1f9 0x980043f1f800c7c7

def z302 : W := mkw 0xb623fc21db703da0 0x22d88ff0876dc0f6 0xfe63fc61fff03fff 0xfff98ff187ffc0ff

def z303 : W := mkw 0x0020442980307068 0x00008110a600c1c1 0x0070e4798031f1fd 0x9801c391e600c7c7

def z304 : W := mkw 0x0890000000000000 0x0022400000000000 0x1d9000000000001b 0x4076400000000000

def z305 : W := mkw 0x6166cee3b0fabab2 0x15859b3b8ec3eaea 0xe3efdfe7f1fe3e37 0xb78fbf7f9fc7f8f8

def z306 : W := mkw 0xf34a924400000000 0x03cd2a4910000000 0xe27cfc7e0000003d 0x1389f3f1f8000000

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x0060c46000000035 0x1001831180000000

def z308 : W := mkw 0x0c91211000000000 0x0032448440000000 0x1c10201800000008 0x4070408060000000

def z309 : W := mkw 0x4dd9235400000000 0x0137648d50000000 0x1dff27fe0000003b 0x7077fc9ff8000000

def z310 : W := mkw 0xb202d800d9402880 0x22c80b60036500a2 0xfe00d801ffc0000f 0xcff8036007ff0000

def z311 : W := mkw 0x0000008006070704 0x0800000200181c1c 0x000000000e0e0e00 0x0400000000383838

def z312 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027cdc7f81f1c014 0x1009f371fe07c700

def z313 : W := mkw 0x4148024400000000 0x0105200910000000 0x006c006600000000 0x0001b00198000000

def z314 : W := mkw 0xb623fca1fb7a3fb0 0x36d88ff287ede8fe 0xfe03f801fffe3fef 0xeff80fe007fff8ff

def z315 : W := mkw 0xffdbb7dc0617574c 0x0bff6edf70185d5d 0xfd9327980e3ffffb 0xfff64c9e6038ffff

def z316 : W := mkw 0x92244c2bc9f0f0ea 0x02489130af27c3c3 0xfe7cfc7ffff1f1ff 0xdff9f3f1ffffc7c7

def z317 : W := mkw 0x2022c4a1b03a3a30 0x14808b1286c0e8e8 0xe003c001f03e3e27 0xa7800f0007c0f8f8

def z318 : W := mkw 0xdbfc080b6dedc0ca 0x476ff0202db7b703 0xfffc381fffffc1df 0xcffff0e07fffff07

def z319 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe060c061f03e3e04 0x8781830187c0f8f8

def z320 : W := mkw 0xffdbfb5492402d80 0x23ff6fed524900b6 0xfffffffe00003fff 0x73fffffff80000ff

def z321 : W := mkw 0x0c95291a06c5c5ce 0x083254a4681b1717 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z322 : W := mkw 0x0000480080402080 0x0000012002010082 0x0000f800000031e0 0x000003e0000000c7

def z323 : W := mkw 0xf34a924400000000 0x03cd2a4910000000 0xe000000000000000 0x0380000000000000

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010241800000039 0x1000409060000000

def z325 : W := mkw 0xd36c000169a88000 0x474db00005a6a200 0xe27c0001f1f1c01d 0x8b89f00007c7c700

def z326 : W := mkw 0x9abc00014da58000 0x426af00005369600 0x1e7c00018ff1c01d 0xc879f000063fc700

def z327 : W := mkw 0x9e99311400000000 0x027a64c450000000 0x1f9f3f9e0000003b 0x707e7cfe78000000

def z328 : W := mkw 0x0898011400000000 0x0022600450000000 0x001c001e00000000 0x0000700078000000

def z329 : W := mkw 0xf36e924569a88000 0x47cdba4915a6a200 0xe26cd867f1c00004 0x0389b3619fc70000

def z330 : W := mkw 0x92004800c9402080 0x0248012003250082 0xfe00f801ffc031ef 0xcff803e007ff00c7

def z331 : W := mkw 0xb202d800d9402880 0x22c80b60036500a2 0xe203d801f1c03e27 0xa7880f6007c700f8

def z332 : W := mkw 0x4140024000000000 0x0105000900000000 0x01e007e000000010 0x1007801f80000000

def z333 : W := mkw 0xbe9bb11400000000 0x02fa6ec450000000 0xfe1ff81e0000002f 0x63f87fe078000000

def z334 : W := mkw 0x4140000000000000 0x0105000000000000 0xe1e0000000000017 0x0387800000000000

def z335 : W := mkw 0x0c91259006171704 0x0832449640185c5c 0x1d8307800e3e3e33 0xf4760c1e0038f8f8

def z336 : W := mkw 0x00244cab86f7f7ee 0x08009132ae1bdfdf 0x027cfc7f8ffffffd 0x9c09f3f1fe3fffff

def z337 : W := mkw 0xf743fac0fb4a2f90 0x37dd0feb03ed28be 0xff83fb81ffce3fef 0xeffe0fee07ff38ff

def z338 : W := mkw 0x00004c2a805070ea 0x00000130aa0141c3 0x0000fc7e000031e0 0x100003f1f80000c7

def z339 : W := mkw 0xfffbf7f5b03a3a30 0x17ffefdfd6c0e8e8 0xfde3c7e1f03e3e37 0xf7f78f1f87c0f8f8

def z340 : W := mkw 0xffffff7fedfdf0ea 0x47fffffdffb7f7c3 0xfffffffffffff1ff 0xffffffffffffffc7

def z341 : W := mkw 0x0024482380e0a0a2 0x000091208e038282 0x027cfc7f81c0003d 0x1009f3f1fe070000

def z342 : W := mkw 0x4df12599263f574c 0x0d37c4966498fd5d 0xfdf32799fe3fffff 0xfff7cc9e67f8ffff

def z343 : W := mkw 0x0000442080103020 0x00000110820040c0 0x0000c46000003020 0x10000311800000c0

def z344 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfc03f8007e003fe2 0x67f00fe001f800ff

def z345 : W := mkw 0x4160026120280030 0x150580098480a000 0x0060006000000000 0x0001800180000000

def z346 : W := mkw 0xb603f800d9402880 0x22d80fe0036500a2 0xfe03f801f1c0002f 0x63f80fe007c70000

def z347 : W := mkw 0x2427ff7f80f0f0ea 0x00909ffdfe03c3c3 0x027fffff81f1f1fd 0xb809fffffe07c7c7

def z348 : W := mkw 0xffffffff86f7f7ee 0x0bfffffffe1bdfdf 0xffffffff8fffffff 0xfffffffffe3fffff

def z349 : W := mkw 0x0c952d9a06d7d7ce 0x083254b6681b5f5f 0x1f9f3f9e0ffffffb 0xfc7e7cfe783fffff

def z350 : W := mkw 0xb603b00000000000 0x02d80ec000000000 0xfc03000000000002 0x63f00c0000000000

def z351 : W := mkw 0x002400016dad8000 0x4400900005b6b600 0x027c0001ffffc01d 0x8c09f00007ffff00

def z352 : W := mkw 0x9e9139184f4545cc 0x2a7a44e4613d1517 0x1e1038180fc1c1c8 0x487840e0603f0707

def z353 : W := mkw 0x6166ce6bb0f8f8fa 0x15859b39aec3e3e3 0xe27cfc7ff1f1f1fd 0x9b89f3f1ffc7c7c7

def z354 : W := mkw 0xb226dc2bd9f0f8ea 0x22c89b70af67c3e3 0xe27cfc7ff1f1f1fd 0x9b89f3f1ffc7c7c7

def z355 : W := mkw 0x960120004b000500 0x02580480012c0014 0xfe032001ffc03fef 0xeff80c8007ff00ff

def z356 : W := mkw 0xf362c6e1f93a3a30 0x17cd8b1b87e4e8e8 0xffe3c7e1fffe3e3f 0xffff8f1f87fff8f8

def z357 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200f8000000002d 0x000803e000000000

def z358 : W := mkw 0xfffffd99ffffffcc 0x6ffffff667ffffff 0xffffff99ffffffff 0xfffffffe67ffffff

def z359 : W := mkw 0x0024080b00e0c0ca 0x000090202c038303 0x027c381f81f1c1dd 0x8809f0e07e07c707

def z360 : W := mkw 0x9a98000000000000 0x026a600000000000 0x1e1c000000000008 0x4078700000000000

def z361 : W := mkw 0x69fac7f5b03a3a30 0x15a7eb1fd6c0e8e8 0xe1ffc7fff03e3e37 0xb787ff1fffc0f8f8

def z362 : W := mkw 0x0000040800105048 0x0000001020004141 0x000000000031f1c0 0x880000000000c7c7

def z363 : W := mkw 0x2403b35400000000 0x00900ecd50000000 0x0003038000000000 0x20000c0e00000000

def z364 : W := mkw 0xdbd800006d0d0000 0x476f600001b43400 0xfd9000007e3fc01b 0xcff6400001f8ff00

def z365 : W := mkw 0x6142c24090002800 0x01850b09024000a0 0xe1e3c7e1f0003e37 0xb7878f1f87c000f8

def z366 : W := mkw 0x0c91219006070704 0x0832448640181c1c 0x1d9303800e3fce1b 0xec764c0e0038ff38

def z367 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe063c7e1f0003e24 0x33818f1f87c000f8

def z368 : W := mkw 0xfffbfff5fb7a3fb0 0x37ffefffd7ede8fe 0xfffffffffffe3fff 0xfffffffffffff8ff

def z369 : W := mkw 0x00244c2bdbf0fdea 0x20009130af6fc3f7 0x027cfc7ffff1fffd 0x9c09f3f1ffffc7ff

def z370 : W := mkw 0xb202d800d9402880 0x22c80b60036500a2 0xe200f801f1c031ed 0x8b8803e007c700c7

def z371 : W := mkw 0xb607f80adbc0edca 0x22d81fe02b6f03b7 0xfe1ff81fffc1ffef 0xeff87fe07fff07ff

def z372 : W := mkw 0x200282c010020a10 0x10800a0b00400828 0x0003038000000e00 0x20000c0e00000038

def z373 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x026cd86781f1f1c4 0x8809b3619e07c7c7

def z374 : W := mkw 0xffffff7fdbf0fdea 0x23fffffdff6fc3f7 0xfffffffffff1ffff 0xffffffffffffc7ff

def z375 : W := mkw 0xb603b0005b000d00 0x22d80ec0016c0034 0xfe030001ffc00e0f 0xeff80c0007ff0038

def z376 : W := mkw 0x0401248002121700 0x001004920008485c 0x1d8327800e3e3ffb 0xfc760c9e0038f8ff

def z377 : W := mkw 0xf362da61f96828b0 0x37cd8b6987e5a0a2 0xe260d861f1c00004 0x0389836187c70000

def z378 : W := mkw 0x0c91200006050500 0x0032448000181414 0x1d9320000e3ffffb 0xec764c800038ffff

def z379 : W := mkw 0x416406eb20bad27a 0x1505901bac82eb49 0x01fc07fe003fc010 0x1007f01ff800ff00

def z380 : W := mkw 0x2403e00092002d00 0x00900f80024800b4 0xfc03e001fe003fef 0xeff00f8007f800ff

def z381 : W := mkw 0x41644eeba0faf2fa 0x1505913bae83ebcb 0x03fcffff81fff1fd 0x980ff3fffe07ffc7

def z382 : W := mkw 0x6ddbb35400000000 0x01b76ecd50000000 0x01fffffe00000030 0x3007fffff8000000

def z383 : W := mkw 0x0024042b00b0d06a 0x00009010ac02c341 0x027c047f81f1c01d 0x9809f011fe07c700

def z384 : W := mkw 0xdfd925980617574c 0x0b7f649660185d5d 0xffff27980e3fffff 0xfffffc9e6038ffff

def z385 : W := mkw 0x00244cab86f7f7ee 0x08009132ae1bdfdf 0x000000018fffffc0 0x8c000000063fffff

def z386 : W := mkw 0xb603fc80db523f80 0x22d80ff2036d48fe 0xff83ff81fffe3fff 0xfffe0ffe07fff8ff

def z387 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x026cfc7f81c031e4 0x1009b3f1fe0700c7

def z388 : W := mkw 0xdfd921906f0f0704 0x4f7f648641bc3c1c 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z389 : W := mkw 0x49f00001242d0000 0x0527c0000490b400 0xfdf00001fe3fc01f 0xcff7c00007f8ff00

def z390 : W := mkw 0xdbdc00006d8d8000 0x476f700001b63600 0xff9c00007fcfc00a 0x4ffe700001ff3f00

def z391 : W := mkw 0x00204021b0282830 0x1400810086c0a0a0 0x00000001f0000000 0x0000000007c00000

def z392 : W := mkw 0xbe93b1905f070f04 0x2afa4ec6417c1c3c 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z393 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1c1327980e01ffe8 0x78704c9e603807ff

def z394 : W := mkw 0x9200000000000000 0x0248000000000000 0xfe0000000000000f 0x43f8000000000000

def z395 : W := mkw 0x0000000000000000 0x0000000000000000 0x00002000000031e9 0x88000080000000c7

def z396 : W := mkw 0x414002c0200a0210 0x1505000b00802808 0x01800380000e0000 0x0006000e00003800

def z397 : W := mkw 0x0000048000121200 0x0000001200004848 0x01800780003e0010 0x1006001e0000f800

def z398 : W := mkw 0x002404896fbfd74c 0x4c00901225beff5d 0x00000001ffffffc0 0x8c00000007ffffff

def z399 : W := mkw 0xdbfc000169a88000 0x476ff00005a6a200 0xfffc0001f1c0001f 0x43fff00007c70000

def z400 : W := mkw 0x00204c2b807070ea 0x00008130ae01c1c3 0x0060fc7f803031f5 0x900183f1fe00c0c7

def z401 : W := mkw 0xb627fc2b80f0f0ea 0x02d89ff0ae03c3c3 0xfe7ffc7f81f1f1ff 0xfbf9fff1fe07c7c7

def z402 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfdfc00007e3fc012 0x47f7f00001f8ff00

def z403 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d8327980e0e3fe2 0x74760c9e603838ff

def z404 : W := mkw 0x6dd3a35000000000 0x01b74e8d40000000 0xfdf3e7f80000003f 0x73f7cf9fe0000000

def z405 : W := mkw 0x69da835400000000 0x01a76a0d50000000 0xe1ffc7fe00000037 0x3387ff1ff8000000

def z406 : W := mkw 0xdbfc4c2bedfdf0ea 0x476ff130afb7f7c3 0xfffc0001fffff1df 0xcffff00007ffffc7

def z407 : W := mkw 0x0004080200c08082 0x0000102008030202 0x020c180601c00000 0x0008306018070000

def z408 : W := mkw 0xfffbf7fdb63f7f7c 0x1fffefdff6d8fdfd 0xfffffffffe3fffff 0xfffffffffff8ffff

def z409 : W := mkw 0x0024482380e0a0a2 0x000091208e038282 0x026cf86781c031ed 0x8809b3e19e0700c7

def z410 : W := mkw 0xfffffb55ffedad80 0x67ffffed57ffb6b6 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x0000035400000000 0x0000000d50000000 0x000007fe00000000 0x1000001ff8000000

def z412 : W := mkw 0x0c9125980212574c 0x083244966008495d 0x1d93279800003ffb 0x70764c9e600000ff

def z413 : W := mkw 0x0024000100a08000 0x0000900004028200 0x027cfc7f81f1c03d 0x9809f3f1fe07c700

def z414 : W := mkw 0xd36c4c2be9f8f0ea 0x474db130afa7e3c3 0xe27cfc7ff1f1f1fd 0x9b89f3f1ffc7c7c7

def z415 : W := mkw 0x0c9121180605454c 0x0832448460181515 0x1c1320180e01ffeb 0xec704c80603807ff

def z416 : W := mkw 0x040125980212574c 0x081004966008495d 0x1c0327980e003feb 0xfc700c9e603800ff

def z417 : W := mkw 0xffffb0016dad8000 0x47fffec005b6b600 0xfffff801ffffc03f 0xefffffe007ffff00

def z418 : W := mkw 0x00244cabb0fafafa 0x14009132aec3ebeb 0x00000001f1ffffc0 0x8c00000007c7ffff

def z419 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfdff07fe00000012 0x73f7fc1ff8000000

def z420 : W := mkw 0x0000000000000000 0x0000000000000000 0x007c047e00000010 0x1001f011f8000000

def z421 : W := mkw 0x0401680082402580 0x001005a002090096 0x1e03f8018fc03fef 0xec780fe0063f00ff

def z422 : W := mkw 0x0024000100a08000 0x0000900004028200 0x007c00000031c010 0x0001f0000000c700

def z423 : W := mkw 0x0000000000000000 0x0000000000000000 0x01800000003e0013 0x840600000000f800

def z424 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1e3c7e0700e0e37 0x37878f1f81c03838

def z425 : W := mkw 0xfbfec261fdada830 0x57effb0987f6b6a0 0xfffcc061ffffc01f 0xcffff30187ffff00

def z426 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xffefdbe600000006 0x63ffbf6f98000000

def z427 : W := mkw 0x0c9121980607474c 0x0832448660181d1d 0x1d9323980e0fcfca 0x6c764c8e60383f3f

def z428 : W := mkw 0x9208100400000000 0x0248204010000000 0x020c180600000000 0x0008306018000000

def z429 : W := mkw 0xffdbb35402000500 0x03ff6ecd50080014 0xfffffffe0e003fff 0xfffffffff83800ff

def z430 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x0010241981f1f1f9 0x980040906607c7c7

def z431 : W := mkw 0xb603b35400000000 0x02d80ecd50000000 0xfe03fffe0000002f 0x73f80ffff8000000

def z432 : W := mkw 0x6142c6e090123a30 0x11850b1b824048e8 0xe1e3c7e000003e37 0x33878f1f800000f8

def z433 : W := mkw 0x6dd3a7d8361f5f5c 0x1db74e9f60d87d7d 0xfd9327987e3ffffb 0xfff64c9e61f8ffff

def z434 : W := mkw 0x2022c6e190323a30 0x10808b1b8640c8e8 0x0063c7e180303e35 0xb0018f1f8600c0f8

def z435 : W := mkw 0x2002c48090123a00 0x00800b12024048e8 0xe183c781f03e3e37 0xb7860f1e07c0f8f8

def z436 : W := mkw 0x0890011000000000 0x0022400440000000 0x0190079800000010 0x1006401e60000000

def z437 : W := mkw 0xf362dee1f97a3ab0 0x37cd8b7b87e5e8ea 0xe3e3dfe1f1fe3e37 0xb78f8f7f87c7f8f8

def z438 : W := mkw 0xf743fa40db402d80 0x23dd0fe9036d00b6 0xffe3ffe1ffc03fff 0xffff8fff87ff00ff

def z439 : W := mkw 0x0cb165b98637776c 0x0832c596e618dddd 0x1df3e7f98e3fffff 0xfc77cf9fe638ffff

def z440 : W := mkw 0x2403ff7e805070ea 0x00900ffdfa0141c3 0x0003fffe000031e0 0x30000ffff80000c7

def z441 : W := mkw 0x2002c00090002800 0x00800b00024000a0 0x0003c00000003e20 0x20000f00000000f8

def z442 : W := mkw 0x0c9125980417524c 0x0832449660105d49 0x1d932798003fc03b 0x70764c9e6000ff00

def z443 : W := mkw 0x0c91211006050504 0x0832448440181414 0x1c0000000e000000 0x4070000000380000

def z444 : W := mkw 0xb627f801dbe0ad80 0x22d89fe0076f82b6 0xfe7ff801fff1ffff 0xeff9ffe007ffc7ff

def z445 : W := mkw 0x614286c0301a1a10 0x15850a1b00c06868 0xe1830780703e3e33 0xb7860c1e01c0f8f8

def z446 : W := mkw 0xfbfeceebfdfffafa 0x57effb3baff7ffeb 0xffffffffffffffff 0xffffffffffffffff

def z447 : W := mkw 0xffdbfb5480402080 0x03ff6fed52010082 0xffffffff81c031ff 0xfbfffffffe0700c7

def z448 : W := mkw 0x41604421a0383020 0x050581108680e0c0 0xe1e0c461f03e3037 0x9787831187c0f8c0

def z449 : W := mkw 0x2002c00090002800 0x00800b00024000a0 0xe000c001f0000004 0x0380030007c00000

def z450 : W := mkw 0xdffd38016fed8580 0x677ff4e005bfb616 0xfffc3801ffffc1df 0xcffff0e007ffff07

def z451 : W := mkw 0xf763f801fb682d80 0x27dd8fe007eda0b6 0xffe3f801fffe3fff 0xefff8fe007fff8ff

def z452 : W := mkw 0x6563fee1b27a3fb0 0x35958ffb86c9e8fe 0xe1e3ffe1f03e3ff7 0xb7878fff87c0f8ff

def z453 : W := mkw 0x416c000120a88000 0x4505b0000482a200 0x006c000000000000 0x0001b00000000000

def z454 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfd9327980000003b 0x73f64c9e60000000

def z455 : W := mkw 0xf763fa61fb682db0 0x37dd8fe987eda0b6 0xfe63f861ffc03fef 0xeff98fe187ff00ff

def z456 : W := mkw 0x6162824120280000 0x05858a090480a000 0xe1e3c7e1f03e0037 0xb7878f1f87c0f800

def z457 : W := mkw 0xb627f801ffedad80 0x66d89fe007ffb6b6 0xfe03f801ffffffef 0xeff80fe007ffffff

def z458 : W := mkw 0xdbfc44a1fdbfba30 0x576ff11287f6fee8 0xfffc0001fffffe1f 0xcffff00007fffff8

def z459 : W := mkw 0x040124880617574c 0x0810049220185d5d 0x1c0320000e3fffeb 0xec700c800038ffff

def z460 : W := mkw 0x0000048800125248 0x0000001220004949 0x01932798003ffffb 0xbc064c9e6000ffff

def z461 : W := mkw 0x2002c6e090123a30 0x10800b1b824048e8 0xe003c7e1f0003e27 0xb7800f1f87c000f8

def z462 : W := mkw 0x0c9125180615554c 0x0832449460185555 0x1c1024180e31f1f9 0xd87040906038c7c7

def z463 : W := mkw 0x6162c66180303020 0x01858b198600c0c0 0xe1e3c7e180303037 0xb3878f1f8600c0c0

def z464 : W := mkw 0xd348000000000000 0x034d200000000000 0xe26c000000000004 0x0389b00000000000

def z465 : W := mkw 0x6162c6e9b03a7a78 0x15858b1ba6c0e9e9 0xe1f3e7f9f03fffff 0xbf87cf9fe7c0ffff

def z466 : W := mkw 0x0401200000000000 0x0010048000000000 0x1c0320000000002b 0x60700c8000000000

def z467 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0x01e3c7e0003e3e30 0x30078f1f8000f8f8

def z468 : W := mkw 0x08b405bb04b7d26e 0x0822d016ec12df49 0x01fc07fe003fc010 0x1007f01ff800ff00

def z469 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xff83fb800000002f 0x63fe0fee00000000

def z470 : W := mkw 0xf36ad265b0282830 0x17cdab4996c0a0a0 0xe26cd867f0000004 0x0389b3619fc00000

def z471 : W := mkw 0x2002c80090402880 0x00800b20024100a2 0xe203f801f1c03fef 0xaf880fe007c700ff

def z472 : W := mkw 0x6dd3a3d0360f0f14 0x1db74e8f40d83c3c 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z473 : W := mkw 0xb603b00002000500 0x02d80ec000080014 0xfe03f8000e003fef 0xeff80fe0003800ff

def z474 : W := mkw 0xdffd6dbbeffff7ee 0x4f7ff5b6efbfffdf 0xffffffffffffffff 0xffffffffffffffff

def z475 : W := mkw 0x0000000000000000 0x0000000000000000 0x021c381e00000008 0x000870e078000000

def z476 : W := mkw 0x002044a9b63f7f7c 0x1c008112a6d8fdfd 0x00000001fe3fffc0 0x8c00000007f8ffff

def z477 : W := mkw 0x0890000004050000 0x0022400000101400 0x01900000003fc010 0x000640000000ff00

def z478 : W := mkw 0xdffd21196fadc54c 0x4f7ff48465beb715 0xfffc2019ffffc1df 0xcffff08067ffff07

def z479 : W := mkw 0x000004880417524c 0x0800001220105d49 0x00000000003fc000 0x000000000000ff00

def z480 : W := mkw 0xb603fc88df577fcc 0x2ad80ff2237d5dff 0xfe03f801ffffffef 0xeff80fe007ffffff

def z481 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9027980e3fc1d8 0x5876409e6038ff07

def z482 : W := mkw 0x00244801ffedad80 0x6400912007ffb6b6 0x00000001ffffffc0 0x8c00000007ffffff

def z483 : W := mkw 0x0004000000808000 0x0000100000020200 0x021c000001c1c008 0x0808700000070700

def z484 : W := mkw 0xdffd21116dad8000 0x477ff48445b6b600 0xffff2799ffffc03f 0xfffffc9e67ffff00

def z485 : W := mkw 0x9200000049000000 0x0248000001240000 0x1e0000000fc00008 0x48780000003f0000

def z486 : W := mkw 0x0004080a00c0c0ca 0x0000102028030303 0x027cfc7e01c1c1fd 0x1809f3f1f8070707

def z487 : W := mkw 0xffdfbb5e00c0c0ca 0x03ff7eed78030303 0xfffffffe01c1c1ff 0x7bfffffff8070707

def z488 : W := mkw 0x2022c6e1b03a3a30 0x14808b1b86c0e8e8 0x0003c7e1f03e3e20 0xb4000f1f87c0f8f8

def z489 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1ffffffe0e3fffff 0xfc7ffffff838ffff

def z490 : W := mkw 0x49fc06e124bf9230 0x5527f01b8492fe48 0x01fc07e0003fc010 0x1007f01f8000ff00

def z491 : W := mkw 0xb603fee0db523fb0 0x32d80ffb836d48fe 0xfe03ffe1ffc03fef 0xfff80fff87ff00ff

def z492 : W := mkw 0x00004c2a805070ea 0x00000130aa0141c3 0x027cfc7e000031fd 0x1009f3f1f80000c7

def z493 : W := mkw 0x0000000000000000 0x0000000000000000 0x001000000031c019 0x880040000000c700

def z494 : W := mkw 0xfbfed801fdeda880 0x67effb6007f7b6a2 0xfffcd801ffffc01f 0xcffff36007ffff00

def z495 : W := mkw 0x00204c21807030a0 0x000081308601c0c2 0x0260fc6181f031fd 0x980983f18607c0c7

def z496 : W := mkw 0x9e913d984f5757cc 0x2a7a44f6613d5d5f 0x1f933f980ffffffb 0xfc7e4cfe603fffff

def z497 : W := mkw 0xffdbbb544b400580 0x23ff6eed512d0016 0xfffffffe0fc001ff 0x7bfffffff83f0007

def z498 : W := mkw 0xbe9ff800dfc5ad80 0x62fa7fe0037f16b6 0xfe1ff801ffc1ffef 0xeff87fe007ff07ff

def z499 : W := mkw 0x6162cee1fb7a3fb0 0x35858b3b87ede8fe 0xe1e3c7e1fffe3ff7 0xbf878f1f87fff8ff

def z500 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe03d801ffc00e06 0x67f80f6007ff0038

def z501 : W := mkw 0x0c9121180605454c 0x0832448460181515 0x1d9020180e3fc1db 0xcc7640806038ff07

def z502 : W := mkw 0xffdbb3546d0d0000 0x47ff6ecd51b43400 0xfd8303807e0e0002 0x67f60c0e01f83800

def z503 : W := mkw 0x96017800cb402580 0x225805e0032d0096 0x1e00f8018fc031ed 0xc87803e0063f00c7

def z504 : W := mkw 0x0401200002000500 0x0010048000080014 0x1c0020000e0001c8 0x4870008000380007

def z505 : W := mkw 0x49d8000000000000 0x0127600000000000 0x01fc000000000010 0x0007f00000000000

def z506 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfe7c0001ffc1c00c 0x4bf9f00007ff0700

def z507 : W := mkw 0x08b400016dad8000 0x4422d00005b6b600 0x1d900001ffffc01b 0xcc76400007ffff00

def z508 : W := mkw 0x0024482380e0a0a2 0x000091208e038282 0x027cd86781f1c01d 0x8809f3619e07c700

def z509 : W := mkw 0x616282c1302a0a10 0x15858a0b04c0a828 0xe1e30381f03e0e17 0xa7878c0e07c0f838

def z510 : W := mkw 0xffdbb3d406070704 0x0bff6ecf50181c1c 0xfd8303800e0e0e02 0x67f60c0e00383838

def z511 : W := mkw 0xffffb35500a08000 0x03fffecd54028200 0xffffffff81f1c03f 0xfbfffffffe07c700

def z512 : W := mkw 0x0000048000121200 0x0000001200004848 0x00000000003e3e00 0x840000000000f8f8

def z513 : W := mkw 0xbe93f910db402d80 0x22fa4fe4436d00b6 0xff93ff99ffc03fff 0xfffe4ffe67ff00ff

def z514 : W := mkw 0x616286e1203a1230 0x15858a1b8480e848 0xe1e3c7e0003e0037 0x33878f1f8000f800

def z515 : W := mkw 0xfbfac6e1b03a3a30 0x17efeb1b86c0e8e8 0xffffc7e1f03e3e3f 0xf7ffff1f87c0f8f8

def z516 : W := mkw 0xffffb35569a88000 0x47fffecd55a6a200 0xfffffffff1c0003f 0x73ffffffffc70000

def z517 : W := mkw 0x2403fee092523fb0 0x30900ffb824948fe 0x0003ffe000003fe0 0x30000fff800000ff

def z518 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x007c047f81f1f1d0 0x9801f011fe07c7c7

def z519 : W := mkw 0xdbfc4801ededa080 0x476ff12007b7b682 0xfffcf801fffff1ff 0xcffff3e007ffffc7

def z520 : W := mkw 0x000000006d0d0000 0x4400000001b43400 0x000000007e0e0000 0x0400000001f83800

def z521 : W := mkw 0x2002c26090002830 0x10800b09824000a0 0x0000c06000000000 0x0000030180000000

def z522 : W := mkw 0x9ebd7d3f80f0f0ea 0x027af5f4fe03c3c3 0x1e7cfc7f81f1f1fd 0xd879f3f1fe07c7c7

def z523 : W := mkw 0xf36ad6e5b03a3a30 0x17cdab5b96c0e8e8 0xe3efdfe7f03e3e37 0xb78fbf7f9fc0f8f8

def z524 : W := mkw 0x0401311400000000 0x001004c450000000 0x0000381e00000000 0x000000e078000000

def z525 : W := mkw 0x0000080a004040ca 0x0000002028010103 0x0000381e000001c0 0x000000e078000007

def z526 : W := mkw 0xdbd8000000000000 0x036f600000000000 0xfffcfc7e0000003f 0x53fff3f1f8000000

def z527 : W := mkw 0xb603fd98db527fcc 0x2ad80ff6636d49ff 0xfe03ff99ffc03fef 0xfff80ffe67ff00ff

def z528 : W := mkw 0xdbfc06e16dbf9230 0x576ff01b85b6fe48 0xfffc07e1ffffc01f 0xdffff01f87ffff00

def z529 : W := mkw 0xdffd21916faf8704 0x4f7ff48645bebe1c 0xffff0381ffffce1f 0xeffffc0e07ffff38

def z530 : W := mkw 0xdfd925986f1f574c 0x4f7f649661bc7d5d 0xfd9327987e3ffffb 0xfff64c9e61f8ffff

def z531 : W := mkw 0x49fc4f7f80f0f0ea 0x0127f13dfe03c3c3 0x03fcffff81f1f1fd 0x980ff3fffe07c7c7

def z532 : W := mkw 0xffdbb35c0605454c 0x0bff6ecd70181515 0xfffffffe0e01c1ff 0x7bfffffff8380707

def z533 : W := mkw 0xffdbb3545b000d00 0x23ff6ecd516c0034 0xfd8303807e000e02 0x67f60c0e01f80038

def z534 : W := mkw 0x0004080a00c0c0ca 0x0000102028030303 0x0000000001c1c1c0 0x0800000000070707

def z535 : W := mkw 0x9200180049400080 0x2248006001250002 0x0200180001c00000 0x0008006000070000

def z536 : W := mkw 0x002444a1fdbfba30 0x5400911287f6fee8 0x00000001fffffe00 0x8c00000007fffff8

def z537 : W := mkw 0x49d8035400000000 0x0127600d50000000 0x0180038000000000 0x0006000e00000000

def z538 : W := mkw 0x96257c2bcbf0f5ea 0x225895f0af2fc3d7 0x1e7cfc7f8ff1f1fd 0xd879f3f1fe3fc7c7

def z539 : W := mkw 0x6166c6e1fdbfba30 0x55859b1b87f6fee8 0xe1e3c7e1fffffe37 0xbf878f1f87fffff8

def z540 : W := mkw 0x0000042a0010506a 0x00000010a8004141 0x0000047e00000000 0x10000011f8000000

def z541 : W := mkw 0x0c91251800105048 0x0032449460004141 0x1d9327980031f1fb 0xf8764c9e6000c7c7

def z542 : W := mkw 0x0024042b00b0d06a 0x00009010ac02c341 0x000000000031c000 0x000000000000c700

def z543 : W := mkw 0x2002c6e090123a30 0x10800b1b824048e8 0x0183c7e0003e3e33 0xb4060f1f8000f8f8

def z544 : W := mkw 0xf36ec261f9a8a830 0x57cdbb0987e6a2a0 0xe26cc061f1c00004 0x0389b30187c70000

def z545 : W := mkw 0x49fc077f00b0d06a 0x0127f01dfc02c341 0x01fc07fe0031c010 0x1007f01ff800c700

def z546 : W := mkw 0xdbf8000120280000 0x076fe0000480a000 0xfffc0001f03e001f 0xc7fff00007c0f800

def z547 : W := mkw 0xffdbf800db402d80 0x23ff6fe0036d00b6 0xfffff801ffc03fff 0xefffffe007ff00ff

def z548 : W := mkw 0xdbd8000000000000 0x036f600000000000 0xfd80000000000002 0x43f6000000000000

def z549 : W := mkw 0xdffd20016fad8500 0x477ff48005beb614 0xffff2001ffffffff 0xeffffc8007ffffff

def z550 : W := mkw 0x0cb56d3b86f5f5ee 0x0832d5b4ee1bd7d7 0x1e7cfc7f8ff1f1fd 0xd879f3f1fe3fc7c7

def z551 : W := mkw 0x0000040800105048 0x0000001020004141 0x027cfc7e0031f1fd 0x9809f3f1f800c7c7

def z552 : W := mkw 0x089005980417524c 0x0822401660105d49 0x01930798003ffe33 0xb4064c1e6000fff8

def z553 : W := mkw 0x4dd927dc0617574c 0x0937649f70185d5d 0x1dff27fe0e3ffffb 0xfc77fc9ff838ffff

def z554 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xe3fc0001f1ffc014 0x038ff00007c7ff00

def z555 : W := mkw 0xfffffee1ffffbfb0 0x77fffffb87fffefe 0xffffffe1ffffffff 0xffffffff87ffffff

def z556 : W := mkw 0x9abc4c2bcdf5f0ea 0x426af130af37d7c3 0x1e7cfc7f8ff1f1fd 0xd879f3f1fe3fc7c7

def z557 : W := mkw 0x49fc000124ad8000 0x4527f0000492b600 0x1dfc00000e3fc01b 0xcc77f0000038ff00

def z558 : W := mkw 0x0024442b80b0f06a 0x00009110ae02c3c1 0x007cc47f8031f035 0x9001f311fe00c7c0

def z559 : W := mkw 0xdbdc00004d858000 0x436f700001361600 0xfffc00000fc1c01f 0x4bfff000003f0700

def z560 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x021c381f81f1f1c8 0x880870e07e07c7c7

def z561 : W := mkw 0xffdbb00000000000 0x03ff6ec000000000 0xfffff8000000003f 0x63ffffe000000000

def z562 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000fc7e00000020 0x100003f1f8000000

def z563 : W := mkw 0x2403b7dc0212574c 0x08900edf7008495d 0x0003fffe00003fe0 0x30000ffff80000ff

def z564 : W := mkw 0x9abc00016dad8000 0x466af00005b6b600 0x1e1c0001ffffc008 0xcc78700007ffff00

def z565 : W := mkw 0x416400016dad8000 0x4505900005b6b600 0xe1e00001ffffc017 0x8f87800007ffff00

def z566 : W := mkw 0x0024000100a08000 0x0000900004028200 0x026c000181c00004 0x0009b00006070000

def z567 : W := mkw 0xb603b00049000000 0x02d80ec001240000 0xfe03f801ffc0002f 0xeff80fe007ff0000

def z568 : W := mkw 0xb603fc08db507dc8 0x22d80ff0236d41f7 0xfe13fc19fff1ffff 0xfff84ff067ffc7ff

def z569 : W := mkw 0x9e9939144b400580 0x227a64e4512d0016 0x1e1c381e0fc001c8 0x487870e0783f0007

def z570 : W := mkw 0xffdbf800ff4d2d80 0x67ff6fe003fd34b6 0xff83f801ffce3fef 0xeffe0fe007ff38ff

def z571 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0x1ffc00000fffc018 0x487ff000003fff00

def z572 : W := mkw 0x0000480080402080 0x0000012002010082 0x0200d80181c00004 0x0008036006070000

def z573 : W := mkw 0xbe93f990df472f84 0x2afa4fe6437d1cbe 0xff83fb81ffce3fef 0xeffe0fee07ff38ff

def z574 : W := mkw 0xdbd8035400000000 0x036f600d50000000 0xfffc07fe0000001f 0x53fff01ff8000000

def z575 : W := mkw 0x00244c2bdbf0fdea 0x20009130af6fc3f7 0x00000001fff1ffc0 0x8c00000007ffc7ff

def z576 : W := mkw 0x2403f80092402d80 0x20900fe0024900b6 0x1c03f8000e003feb 0xec700fe0003800ff

def z577 : W := mkw 0xffdbf35490002800 0x03ff6fcd524000a0 0xfffffffff0003e3f 0xf7ffffffffc000f8

def z578 : W := mkw 0x0020000100200000 0x0000800004008000 0x0060000180300015 0x800180000600c000

def z579 : W := mkw 0x000004880617574c 0x0800001220185d5d 0x001024180e3ffff9 0x9c0040906038ffff

def z580 : W := mkw 0xf36ede6f80f0f0ea 0x03cdbb79be03c3c3 0xe27cfc7f81f1f1fd 0x9b89f3f1fe07c7c7

def z581 : W := mkw 0x4df127f9263f577c 0x1d37c49fe498fd5d 0x1df327f80e3ffffb 0xfc77cc9fe038ffff

def z582 : W := mkw 0x040125980212574c 0x081004966008495d 0x001327980031fff9 0xb8004c9e6000c7ff

def z583 : W := mkw 0xd36c000169a88000 0x474db00005a6a200 0xfe6c0001ffc0000f 0xcff9b00007ff0000

def z584 : W := mkw 0x0401211000000000 0x0010048440000000 0x0003279800000020 0x30000c9e60000000

def z585 : W := mkw 0x2403f7f490123a30 0x10900fdfd24048e8 0x0003fffe00003e20 0x30000ffff80000f8

def z586 : W := mkw 0x0c9121180605454c 0x0832448460181515 0x1d9327980e01c1fb 0x78764c9e60380707

def z587 : W := mkw 0x69fec6e1b4bfba30 0x55a7fb1b86d2fee8 0xe1ffc7e1f03ffe37 0xb787ff1f87c0fff8

def z588 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xffff03800000001f 0x63fffc0e00000000

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0x0183078000000033 0x30060c1e00000000

def z590 : W := mkw 0x089c000004858000 0x4022700000121600 0x001c00000001c000 0x0000700000000700

def z591 : W := mkw 0x089005980617574c 0x0822401660185d5d 0x019007980e3fffd0 0x9c06401e6038ffff

def z592 : W := mkw 0xffdbb35404050000 0x03ff6ecd50101400 0xfffffffe0e3fc03f 0xfffffffff838ff00

def z593 : W := mkw 0x0000000004050000 0x0000000000101400 0x000000000e3fc000 0x8c0000000038ff00

def z594 : W := mkw 0xfbda82c07d0f0a10 0x57ef6a0b01f43c28 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z595 : W := mkw 0x0cb56d3b80f0f0ea 0x0032d5b4ee03c3c3 0x1fffffff81f1f1ff 0xf87ffffffe07c7c7

def z596 : W := mkw 0xfbfec001fdada800 0x47effb0007f6b6a0 0xffffc001fffffe3f 0xefffff0007fffff8

def z597 : W := mkw 0x0000000800004048 0x0000000020000101 0x001020180001c1c8 0x0800408060000707

def z598 : W := mkw 0xf36ec6e1f9baba30 0x57cdbb1b87e6eae8 0xe3efc7e1f1fe3e37 0xb78fbf1f87c7f8f8

def z599 : W := mkw 0x0004480a80c0e0ca 0x000011202a030383 0x021cf81f81c1f1ed 0x880873e07e0707c7

def z600 : W := mkw 0xffdbb75c00105048 0x03ff6edd70004141 0xfffffffe0031f1ff 0xfbfffffff800c7c7

def z601 : W := mkw 0x00004800d9402880 0x20000120036500a2 0x00000001f1c00000 0x0000000007c70000

def z602 : W := mkw 0x960138004b400580 0x225804e0012d0016 0xfe003801ffc001cf 0xcff800e007ff0007

def z603 : W := mkw 0xbe93f918df456dcc 0x2afa4fe4637d15b7 0xfe13f819ffc1ffef 0xeff84fe067ff07ff

def z604 : W := mkw 0xffdbb3d406070704 0x0bff6ecf50181c1c 0xfffffffe0e0e0e3f 0x77fffffff8383838

def z605 : W := mkw 0x0c916d98865777cc 0x083245b662195ddf 0x1f93ff998fffffff 0xfc7e4ffe663fffff

def z606 : W := mkw 0xfff3fff9ff7f7ffc 0x3fffcfffe7fdfdff 0xfff3fff9ffffffff 0xffffcfffe7ffffff

def z607 : W := mkw 0x2002924400000000 0x00800a4910000000 0x0000d86600000000 0x0000036198000000

def z608 : W := mkw 0x00204ca1fb7a3fb0 0x3400813287ede8fe 0x00000001fffe3fc0 0x8c00000007fff8ff

def z609 : W := mkw 0x0000480080402080 0x0000012002010082 0x0000000181c031c0 0x88000000060700c7

def z610 : W := mkw 0xf743b2c07b0a0f10 0x37dd0ecb01ec283c 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z611 : W := mkw 0xdbfc4c2b80f0f0ea 0x036ff130ae03c3c3 0xfffcfc7f81f1f1ff 0xdbfff3f1fe07c7c7

def z612 : W := mkw 0xffdbb7dc0417524c 0x0bff6edf70105d49 0xfffffffe003fc03f 0x73fffffff800ff00

def z613 : W := mkw 0x2002c800db402d80 0x20800b20036d00b6 0xe003c001ffc03fe7 0xaf800f0007ff00ff

def z614 : W := mkw 0x416046e1a03a3230 0x1505811b8680e8c8 0x01e0c7e1803e3035 0x9007831f8600f8c0

def z615 : W := mkw 0xffdbb7dc0212574c 0x0bff6edf7008495d 0xfffffffe00003fff 0x73fffffff80000ff

def z616 : W := mkw 0x49d807dc0417524c 0x0927601f70105d49 0x01fc07fe003fc010 0x1007f01ff800ff00

def z617 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xff9f3b9e0000000a 0x63fe7cee78000000

def z618 : W := mkw 0xdbf800016d2d0000 0x476fe00005b4b400 0xfde00001fe3e0017 0xc7f7800007f8f800

def z619 : W := mkw 0xb603b0005b000d00 0x22d80ec0016c0034 0xfe03f8007e000e2f 0x67f80fe001f80038

def z620 : W := mkw 0x002044a1b03a3a30 0x1400811286c0e8e8 0x0060c461f03e3e35 0x9401831187c0f8f8

def z621 : W := mkw 0x9e9d31144d858000 0x427a74c451361600 0x1e1c381e0fc1c008 0x487870e0783f0700

def z622 : W := mkw 0x0020442180303020 0x000081108600c0c0 0x0000000180303000 0x800000000600c0c0

def z623 : W := mkw 0xf763f6e1b03a3a30 0x17dd8fdb86c0e8e8 0xffe3ffe1f03e3e3f 0xf7ff8fff87c0f8f8

def z624 : W := mkw 0xbe93b5985f175f4c 0x2afa4ed6617c5d7d 0xfd9327987e3ffffb 0xfff64c9e61f8ffff

def z625 : W := mkw 0xbe93f800df452d80 0x22fa4fe0037d14b6 0xff93f801ffffffff 0xeffe4fe007ffffff

def z626 : W := mkw 0x416044a1b03a3a30 0x1505811286c0e8e8 0xe1e00001f03e3e17 0x8787800007c0f8f8

def z627 : W := mkw 0xd36c000169a88000 0x474db00005a6a200 0xe3ec0001f1fe0017 0x878fb00007c7f800

def z628 : W := mkw 0x6162c6e9b63f7f7c 0x1d858b1ba6d8fdfd 0xe1e3c7e1fe3ffff7 0xbf878f1f87f8ffff

def z629 : W := mkw 0x0000000049000000 0x0000000001240000 0x00000001ffc00000 0x8c00000007ff0000

def z630 : W := mkw 0xdbfc04096dbdd048 0x476ff01025b6f741 0xfffc2419fffff1ff 0xdffff09067ffffc7

def z631 : W := mkw 0x0000000000000000 0x0000000000000000 0x0200000181c0000d 0x8808000006070000

def z632 : W := mkw 0x2403e7f892127f7c 0x18900f9fe24849fd 0x0003e7f800003fe0 0x30000f9fe00000ff

def z633 : W := mkw 0xf74bb24400000000 0x03dd2ec910000000 0xfe6ff8660000002f 0x63f9bfe198000000

def z634 : W := mkw 0x2002d80090402880 0x20800b60024100a2 0x0000d80000000000 0x0000036000000000

def z635 : W := mkw 0xffdbfb54d9402880 0x23ff6fed536500a2 0xfffffffff1c0003f 0x73ffffffffc70000

def z636 : W := mkw 0x49f007f9243f527c 0x1d27c01fe490fd49 0x01f007f8003fc010 0x1007c01fe000ff00

def z637 : W := mkw 0x96017800db402d80 0x225805e0036d00b6 0x1e003801ffc03fc8 0xcc7800e007ff00ff

def z638 : W := mkw 0x2002800000000000 0x00800a0000000000 0xe003c00000000027 0x23800f0000000000

def z639 : W := mkw 0xdbfc042b6dbdd06a 0x476ff010adb6f741 0xfffc047fffffc01f 0xdffff011ffffff00

def z640 : W := mkw 0x6142824000000000 0x01850a0900000000 0xe060c06000000004 0x0381830180000000

def z641 : W := mkw 0x0024002300a08022 0x000090008c028200 0x006c006600000000 0x0001b00198000000

def z642 : W := mkw 0x9200000049000000 0x0248000001240000 0xfc0000007e000002 0x47f0000001f80000

def z643 : W := mkw 0x2026cc2b90f0f8ea 0x00809b30ae43c3e3 0xe27ffc7ff1f1ffff 0xbf89fff1ffc7c7ff

def z644 : W := mkw 0xdffd31156dad8000 0x477ff4c455b6b600 0xfffc381fffffc01f 0xcffff0e07fffff00

def z645 : W := mkw 0x00004822804020a2 0x000001208a010082 0x0000d86600000000 0x0000036198000000

def z646 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfe7cf87e0000000c 0x43f9f3e1f8000000

def z647 : W := mkw 0x04016800db402d80 0x201005a0036d00b6 0x1c032001ffc03feb 0xec700c8007ff00ff

def z648 : W := mkw 0x9e9d25984f97d74c 0x4a7a7496613e5f5d 0x1f9f27980ffffffb 0xfc7e7c9e603fffff

def z649 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x0000fc7f81f1f1e0 0x980003f1fe07c7c7

def z650 : W := mkw 0x0020402180202020 0x0000810086008080 0x0060c06180000004 0x0001830186000000

def z651 : W := mkw 0xb603f80080402080 0x02d80fe002010082 0xfe03f80181c031ef 0xebf80fe0060700c7

def z652 : W := mkw 0xffffe7f9ffbfff7c 0x5fffff9fe7fefffd 0xffffe7f9ffffffff 0xffffff9fe7ffffff

def z653 : W := mkw 0x0000400090002800 0x00000100024000a0 0x00000001f0003e00 0x8400000007c000f8

def z654 : W := mkw 0xfbfe82416dad8000 0x47effa0905b6b600 0xffffc7e1ffffc03f 0xffffff1f87ffff00

def z655 : W := mkw 0x089001180405404c 0x0822400460101501 0x001000180001c000 0x0000400060000700

def z656 : W := mkw 0x000004880617574c 0x0800001220185d5d 0x018307800e3ffff3 0xbc060c1e0038ffff

def z657 : W := mkw 0xdbfc4801ffedad80 0x676ff12007ffb6b6 0xfffc0001ffffffdf 0xcffff00007ffffff

def z658 : W := mkw 0x00040c0a00d0d0ca 0x0000103028034343 0x021c3c1e01f1f1f9 0x980870f07807c7c7

def z659 : W := mkw 0x0020000120280000 0x040080000480a000 0x00000001f03e0000 0x8400000007c0f800

def z660 : W := mkw 0xb603f000db002d00 0x22d80fc0036c00b4 0xfc03c001fe003e27 0xe7f00f0007f800f8

def z661 : W := mkw 0x0000000000000000 0x0000000000000000 0x027c00000000001d 0x0009f00000000000

def z662 : W := mkw 0x0024040900b0d048 0x000090102402c341 0x027c241981f1f1fd 0x9809f0906607c7c7

def z663 : W := mkw 0xdfd9211000000000 0x037f648440000000 0xffff27980000003f 0x73fffc9e60000000

def z664 : W := mkw 0x41644c2ba0f8f0ea 0x05059130ae83e3c3 0xe3fcfc7ff1fff1ff 0x9f8ff3f1ffc7ffc7

def z665 : W := mkw 0xffdbb3d4300a0a10 0x17ff6ecf50c02828 0xfd830380700e0e02 0x67f60c0e01c03838

def z666 : W := mkw 0x0000048000121200 0x0000001200004848 0x0003078000003e20 0x30000c1e000000f8

def z667 : W := mkw 0xffdbb7d400121200 0x03ff6edf50004848 0xfffffffe003e3e3f 0xf7fffffff800f8f8

def z668 : W := mkw 0x2c93e59896177f4c 0x08b24f9662585dfd 0xfd93e799fe3fffff 0xfff64f9e67f8ffff

def z669 : W := mkw 0xb603b8005b400d80 0x22d80ee0016d0036 0xfe0338007fc00fca 0x6ff80ce001ff003f

def z670 : W := mkw 0x614286c000121200 0x01850a1b00004848 0xe1e3c7e0003e3e37 0xb7878f1f8000f8f8

def z671 : W := mkw 0xfbfe92456dad8000 0x47effa4915b6b600 0xfffcd867ffffc01f 0xcffff3619fffff00

def z672 : W := mkw 0x4dfd259926bfd74c 0x4d37f496649aff5d 0x1dff27980e3ffffb 0xfc77fc9e6038ffff

def z673 : W := mkw 0xffffb0017fad8d00 0x67fffec005feb634 0xffff0001ffffce1f 0xeffffc0007ffff38

def z674 : W := mkw 0x00004c08805070c8 0x00000130220141c3 0x0210fc1981f1f1fd 0x980843f06607c7c7

def z675 : W := mkw 0xb202d800db402d80 0x22c80b60036d00b6 0xe200d801ffc03fc4 0x8f88036007ff00ff

def z676 : W := mkw 0x00240c2b00f0d0ea 0x00009030ac03c343 0x027c3c7e01f1c1d8 0x1809f0f1f807c707

def z677 : W := mkw 0xbeb7fdbbdff7ffee 0x2afadff6ef7fdfff 0xffffffffffffffff 0xffffffffffffffff

def z678 : W := mkw 0x0c916dba865777ee 0x083245b6ea195ddf 0x1d93fffe0e3ffffb 0xfc764ffff838ffff

def z679 : W := mkw 0xdbfc04896fbfd74c 0x4f6ff01225beff5d 0xfffc0001ffffffdf 0xcffff00007ffffff

def z680 : W := mkw 0xbe9bb35400000000 0x02fa6ecd50000000 0x1e1ffffe00000028 0x70787ffff8000000

def z681 : W := mkw 0xb627fc2bdbf0fdea 0x22d89ff0af6fc3f7 0xfe03f801fff1ffef 0xeff80fe007ffc7ff

def z682 : W := mkw 0xdbfc4823ededa0a2 0x476ff1208fb7b682 0xfffcd867ffffc01f 0xcffff3619fffff00

def z683 : W := mkw 0x0c91219006070704 0x0832448640181c1c 0x1d8323800e0e3feb 0xec760c8e003838ff

def z684 : W := mkw 0xffdbfb54db402d80 0x23ff6fed536d00b6 0xff83fb81ffc03fef 0xeffe0fee07ff00ff

def z685 : W := mkw 0xdbfc04816dbf9200 0x476ff01205b6fe48 0xffff0781fffffe3f 0xfffffc1e07fffff8

def z686 : W := mkw 0x000400004d858000 0x4000100001361600 0x000000000fc1c000 0x08000000003f0700

def z687 : W := mkw 0xb202900059000800 0x22c80a4001640020 0xe000000070000000 0x0380000001c00000

def z688 : W := mkw 0xb603f00090002800 0x02d80fc0024000a0 0xfe03f801f0003e2f 0xe7f80fe007c000f8

def z689 : W := mkw 0x0c91219006070704 0x0832448640181c1c 0x1d9327980e0e0e3b 0x74764c9e60383838

def z690 : W := mkw 0xffffb7dd6fbfd74c 0x4ffffedf75beff5d 0xffffffffffffffff 0xffffffffffffffff

def z691 : W := mkw 0xfbda824000000000 0x03ef6a0900000000 0xffffc7e00000003f 0x73ffff1f80000000

def z692 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe00f801ffc001cc 0x4bf803e007ff0007

def z693 : W := mkw 0xdfd9335400000000 0x037f64cd50000000 0x1ffc3ffe00000018 0x507ff0fff8000000

def z694 : W := mkw 0x00244c2bedfdf0ea 0x44009130afb7f7c3 0x027cfc7ffffff1fd 0x9c09f3f1ffffffc7

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003000000003e23 0xa4000c00000000f8

def z696 : W := mkw 0x920c000049808000 0x4248300001260200 0x020c000001c00000 0x0008300000070000

def z697 : W := mkw 0xf34a924400000000 0x03cd2a4910000000 0xe3efdfe600000037 0x338fbf7f98000000

def z698 : W := mkw 0x002044a180323220 0x000081128600c8c8 0x01e3c7e1803e3e37 0xb4078f1f8600f8f8

def z699 : W := mkw 0x0c91211000000000 0x0032448440000000 0x1d83038000000002 0x60760c0e00000000

def z700 : W := mkw 0x49fc000124ad8000 0x4527f0000492b600 0x03fc000181ffc01d 0x880ff0000607ff00

def z701 : W := mkw 0xdbd8000004050000 0x036f600000101400 0xfffc00000e3fc01f 0xcffff0000038ff00

def z702 : W := mkw 0x000004880212574c 0x080000122008495d 0x0000000000003fc0 0x00000000000000ff

def z703 : W := mkw 0x9e99311c0605454c 0x0a7a64c470181515 0x1e1c381e0e01c1c8 0x487870e078380707

def z704 : W := mkw 0x000006e000121230 0x1000001b80004848 0x000007e000000000 0x1000001f80000000

def z705 : W := mkw 0xd360000169280000 0x074d800005a4a000 0xffe00001fffe001f 0xcfff800007fff800

def z706 : W := mkw 0xbe9bf914db402d80 0x22fa6fe4536d00b6 0xfe1ff81fffc03fef 0xeff87fe07fff00ff

def z707 : W := mkw 0x2022c4a1b03a3a30 0x14808b1286c0e8e8 0xe183c781f03e3e37 0xb7860f1e07c0f8f8

def z708 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe1fffffff03ffff7 0xb787ffffffc0ffff

def z709 : W := mkw 0x69da835400000000 0x01a76a0d50000000 0xe3fffffe0000003f 0x338ffffff8000000

def z710 : W := mkw 0x616286c1203a1200 0x05858a1b0480e848 0xe1e3c7e1f03e3e37 0xb7878f1f87c0f8f8

def z711 : W := mkw 0xba9ec6e0dd97ba30 0x52ea7b1b83765ee8 0x1e1fc7e00fc1fe28 0x78787f1f803f07f8

def z712 : W := mkw 0xdbd84c2aed5d70ea 0x476f6130abb575c3 0xfd80fc7e7e0e31e2 0x57f603f1f9f838c7

def z713 : W := mkw 0x2403effa92527ffe 0x18900fbfea4949ff 0x0003fffe00003fe0 0x30000ffff80000ff

def z714 : W := mkw 0x49fc07f924bfd27c 0x5d27f01fe492ff49 0x01fc07f8003fc010 0x1007f01fe000ff00

def z715 : W := mkw 0x6162c6e9b03a7a78 0x15858b1ba6c0e9e9 0xe1e3c7e1f03ffff7 0xbf878f1f87c0ffff

def z716 : W := mkw 0x922400016dad8000 0x4648900005b6b600 0xfe7c0001ffffc01f 0xcff9f00007ffff00

def z717 : W := mkw 0x00040c0a00d0d0ca 0x0000103028034343 0x027cfc7e01f1f1fd 0x9809f3f1f807c7c7

def z718 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffffffe00003e3f 0xf7fffffff80000f8

def z719 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffffffe003e003f 0xf7fffffff800f800

def z720 : W := mkw 0x9eb57d3bcff5f5ee 0x2a7ad5f4ef3fd7d7 0x1e7cfc7f8ff1f1fd 0xd879f3f1fe3fc7c7

def z721 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe1f3e7f9f1ffffff 0xbf87cf9fe7c7ffff

def z722 : W := mkw 0xffdbb35430080810 0x17ff6ecd50c02020 0xfffffffe7000003f 0x73fffffff9c00000

def z723 : W := mkw 0x00244cab80f2f2ea 0x00009132ae03cbcb 0x03fcffff81fff1fd 0x980ff3fffe07ffc7

def z724 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xffff0781ffffc03f 0xfffffc1e07ffff00

def z725 : W := mkw 0xffdbb35420080000 0x07ff6ecd50802000 0xfffffffe700e003f 0x77fffffff9c03800

def z726 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfdfc0001ffffc012 0xcff7f00007ffff00

def z727 : W := mkw 0x6166cee3b0fabab2 0x15859b3b8ec3eaea 0xe3ffdfe7f1fffe3f 0xbf8fff7f9fc7fff8

def z728 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1df3e7f80e3fffff 0xfc77cf9fe038ffff

def z729 : W := mkw 0xffdbb3544b000500 0x23ff6ecd512c0014 0xfffffffe0e00003f 0x73fffffff8380000

def z730 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe030001ffc03fcf 0xeff80c0007ff00ff

def z731 : W := mkw 0x6142c2c0b00a2a10 0x15850b0b02c028a8 0xe183c381f00e0e06 0x27860f0e07c03838

def z732 : W := mkw 0xd7613ee16b7a17b0 0x375d84fb85ade85e 0x1fe03fe00ffe01d8 0x587f80ff803ff807

def z733 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe3ffc7e1f1ffffff 0xbf8fff1f87c7ffff

def z734 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffcc461ffffc03f 0xdffff31187ffff00

def z735 : W := mkw 0x6162cee1b07a3ab0 0x15858b3b86c1e8ea 0xe1e3ffe1f03e3ff7 0xb7878fff87c0f8ff

def z736 : W := mkw 0x6142c6e0b01a3a30 0x15850b1b82c068e8 0xe183c7e1f00e3e27 0xb7860f1f87c038f8

def z737 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1e30380700e0e17 0x27878c0e01c03838

def z738 : W := mkw 0xb60bf804db402d80 0x22d82fe0136d00b6 0xfe0ff807ffc03fef 0xeff83fe01fff00ff

def z739 : W := mkw 0x6166c6ebb0bafa7a 0x15859b1baec2ebe9 0xe3fffffff03ffe3f 0xb78fffffffc0fff8

def z740 : W := mkw 0x2427b3556dad8000 0x44909ecd55b6b600 0x0003ffffffffc020 0xbc000fffffffff00

def z741 : W := mkw 0x6142c6c0b01a3a10 0x15850b1b02c068e8 0xe183c781f03e3e37 0xb7860f1e07c0f8f8

def z742 : W := mkw 0xdbfc10056dad8000 0x476ff04015b6b600 0xfffc1807ffffc01f 0xcffff0601fffff00

def z743 : W := mkw 0x616282c1302a0a10 0x15858a0b04c0a828 0xe1e30381f00e0e06 0x27878c0e07c03838

def z744 : W := mkw 0x9eb975b5b03a3a30 0x167ae5d6d6c0e8e8 0x1e1c381ff03e3e08 0xc47870e07fc0f8f8

def z745 : W := mkw 0x6162c2e1b02a2a30 0x15858b0b86c0a8a8 0xe1e3c3e1f03e0e17 0xa7878f0f87c0f838

def z746 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffc047fffffc01f 0xdffff011ffffff00

def z747 : W := mkw 0x96017800db402d80 0x225805e0036d00b6 0xfe003801ffc03fcf 0xcff800e007ff00ff

def z748 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffffffe0031c03f 0xfbfffffff800c700

def z749 : W := mkw 0x616286c1303a1a10 0x15858a1b04c0e868 0xe1e30781f03e3e37 0xb7878c1e07c0f8f8

def z750 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfde00001ffffc017 0xcff7800007ffff00

def z751 : W := mkw 0xb603f914db402d80 0x22d80fe4536d00b6 0xfe03f81fffc03fef 0xeff80fe07fff00ff

def z752 : W := mkw 0xffdbb35469080000 0x47ff6ecd51a42000 0xfffffffe7000003f 0x73fffffff9c00000

def z753 : W := mkw 0xf366da63f9e8a8b2 0x37cd9b698fe7a2a2 0xe26cd867f1c00004 0x0389b3619fc70000

def z754 : W := mkw 0x2002808010020a00 0x00800a0200400828 0xe1830380700e0e02 0x27860c0e01c03838

def z755 : W := mkw 0x0024482b80e0e0ea 0x00009120ae038383 0x027cf87f81c1f1ed 0x8809f3e1fe0707c7

def z756 : W := mkw 0x49f400016dad8000 0x4527d00005b6b600 0xfdf00001ffffc01f 0xcff7c00007ffff00

def z757 : W := mkw 0xd76d25996bbad74c 0x4f5db49665aeeb5d 0xe26f2799f1c03fe4 0x3389bc9e67c700ff

def z758 : W := mkw 0xd36400016dad8000 0x474d900005b6b600 0xffe00001ffffc01f 0xcfff800007ffff00

def z759 : W := mkw 0xffdbb35459000800 0x23ff6ecd51640020 0xfffffffe7000003f 0x73fffffff9c00000

def z760 : W := mkw 0x0000000000000000 0x0000000000000000 0x03fffffe0000003f 0x300ffffff8000000

def z761 : W := mkw 0xffdbb35406050500 0x03ff6ecd50181414 0xfffffffe0e3fffff 0xfffffffff838ffff

def z762 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xffffdffe00000016 0x73ffff7ff8000000

def z763 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe03f801ffc03fe6 0x67f80fe007ff00ff

def z764 : W := mkw 0x6162cee3b07a3ab2 0x15858b3b8ec1e8ea 0xe1e3dfe7f03e3e37 0xb7878f7f9fc0f8f8

def z765 : W := mkw 0x0c91359c0617574c 0x083244d670185d5d 0x1d933f9e0e3ffffb 0xfc764cfe7838ffff

def z766 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3e7e1f03e3fff 0xbf878f9f87c0f8ff

def z767 : W := mkw 0x0c9125ba0617576e 0x08324496e8185d5d 0x1d9327fe0e3ffffb 0xfc764c9ff838ffff

def z768 : W := mkw 0x2002848010121a00 0x00800a1200404868 0xe1830780703e3e33 0xb7860c1e01c0f8f8

def z769 : W := mkw 0x9e99391c4f4545cc 0x2a7a64e4713d1517 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z770 : W := mkw 0xdbfc02456dad8000 0x476ff00915b6b600 0xfffc0067ffffc01f 0xcffff0019fffff00

def z771 : W := mkw 0xffdbb3d46f0f0704 0x4fff6ecf51bc3c1c 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z772 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe3e3ffe1f03e3e3f 0xb78f8fff87c0f8f8

def z773 : W := mkw 0x6df3e379b62d6d7c 0x1db7cf8de6d8b5b5 0xfc70e079fe01c1cc 0x4bf1c381e7f80707

def z774 : W := mkw 0x0004080a00c0c0ca 0x0000102028030303 0x027cf87e01c1c1cc 0x0809f3e1f8070707

def z775 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe03d801ffc03fc6 0xeff80f6007ff00ff

def z776 : W := mkw 0x9e9d21104f858504 0x4a7a7484413e1614 0x1e1c00000fc1c008 0x48787000003f0700

def z777 : W := mkw 0xdbfc03556dad8000 0x476ff00d55b6b600 0xfffcffffffffc03f 0xdffff3ffffffff00

def z778 : W := mkw 0xffdbb3d45f070f04 0x2bff6ecf517c1c3c 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z779 : W := mkw 0xdbfc01156dad8000 0x476ff00455b6b600 0xfffc001fffffc01f 0xcffff0007fffff00

def z780 : W := mkw 0x49f407fb24bfd27e 0x1d27d01fec92ff49 0x01fc07fe003fc010 0x1007f01ff800ff00

def z781 : W := mkw 0xfbda824000000000 0x03ef6a0900000000 0xfffffffe0000003f 0x73fffffff8000000

def z782 : W := mkw 0xf34a96cc0617574c 0x0bcd2a5b30185d5d 0xe26cd8660e3fffc4 0x8f89b3619838ffff

def z783 : W := mkw 0xfbda935400000000 0x03ef6a4d50000000 0xe3fcfffe0000003d 0x138ff3fff8000000

def z784 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9303800e3fffdb 0xec764c0e0038ffff

def z785 : W := mkw 0xdbfc00236dad8022 0x476ff0008db6b600 0xfffc0067ffffc01f 0xcffff0019fffff00

def z786 : W := mkw 0x49f4000124ad8000 0x0527d0000492b600 0xfffc0001ffffc01f 0xcffff00007ffff00

def z787 : W := mkw 0x00244cabfbfafffa 0x34009132afefebff 0x00000001ffffffc0 0x8c00000007ffffff

def z788 : W := mkw 0xf36eca63f9e8a8b2 0x57cdbb298fe7a2a2 0xe26cd867f1c00004 0x0389b3619fc70000

def z789 : W := mkw 0xbe93b11000000000 0x02fa4ec440000000 0xfffffffe0000003f 0x73fffffff8000000

def z790 : W := mkw 0xb603f822db402da2 0x22d80fe08b6d00b6 0xfe03f867ffc03fef 0xeff80fe19fff00ff

def z791 : W := mkw 0x00244c2b90f0f8ea 0x00009130ae43c3e3 0x027cfc7ff1f1fffd 0x9c09f3f1ffc7c7ff

def z792 : W := mkw 0x6162c481b03a3a00 0x05858b1206c0e8e8 0xe1e3c781f03e3e37 0xb7878f1e07c0f8f8

def z793 : W := mkw 0x2403b35400000000 0x00900ecd50000000 0x026ffffe00000024 0x3009bffff8000000

def z794 : W := mkw 0x4140024000000000 0x0105000900000000 0x03fcfffe0000003d 0x100ff3fff8000000

def z795 : W := mkw 0x9e9921104f050504 0x4a7a6484413c1414 0x1c0000000e000000 0x4070000000380000

def z796 : W := mkw 0xffffff7f80f0f0ea 0x03fffffdfe03c3c3 0xfd83038181f1f1c2 0xebf60c0e0607c7c7

def z797 : W := mkw 0x654bb35400000000 0x01952ecd50000000 0x006ffffe00000020 0x3001bffff8000000

def z798 : W := mkw 0xbe9bb35400000000 0x02fa6ecd50000000 0x1e7ffffe0000003d 0x7079fffff8000000

def z799 : W := mkw 0x2403ffdc92527fcc 0x28900fff724949ff 0x0003fffe00003fe0 0x30000ffff80000ff

def z800 : W := mkw 0x00244cab80f2f2ea 0x00009132ae03cbcb 0x0000000181ffffc0 0x8c0000000607ffff

def z801 : W := mkw 0x49d84b54db402d80 0x2127612d536d00b6 0x01fc07ffffc03fd0 0x9c07f01fffff00ff

def z802 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe03f801ffc03fec 0x6bf80fe007ff00ff

def z803 : W := mkw 0x6ddbb35400000000 0x01b76ecd50000000 0xe1fffffe00000037 0x3387fffff8000000

def z804 : W := mkw 0x41600081202a0200 0x050580020480a808 0xe1e30381f03e0e17 0xa7878c0e07c0f838

def z805 : W := mkw 0xf74bb35400000000 0x03dd2ecd50000000 0xe3effffe00000037 0x338fbffff8000000

def z806 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfe7ffffe0000002c 0x73f9fffff8000000

def z807 : W := mkw 0x6142cac0b04a2a90 0x15850b2b02c128aa 0xe383fb81f1ce3fef 0xaf8e0fee07c738ff

def z808 : W := mkw 0xffdbb3544d050000 0x43ff6ecd51341400 0xfffffffe0e00003f 0x73fffffff8380000

def z809 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe1ff81fffc03fef 0xeff87fe07fff00ff

def z810 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xfde3c7e1fe3e3e3f 0xfff78f1f87f8f8f8

def z811 : W := mkw 0x00004c08805070c8 0x00000130220141c3 0x027cfc7f81f1f1fd 0x9809f3f1fe07c7c7

def z812 : W := mkw 0x0c99259c0617574c 0x0832649670185d5d 0x1d9f279e0e3ffffb 0xfc767c9e7838ffff

def z813 : W := mkw 0x96016800cb402580 0x025805a0032d0096 0xfe03f801ffc03fef 0xeff80fe007ff00ff

def z814 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe1830381f1ffffc2 0xaf860c0e07c7ffff

def z815 : W := mkw 0x616286e1303a1a30 0x15858a1b84c0e868 0xe1830380703e0e02 0x27860c0e01c0f838

def z816 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfc032001ffc03feb 0xeff00c8007ff00ff

def z817 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe03fc7fffc03fef 0xfff80ff1ffff00ff

def z818 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xff83f801fffe3fff 0xeffe0fe007fff8ff

def z819 : W := mkw 0x6162c2e1b02a2a30 0x15858b0b86c0a8a8 0xe1830381f00e0e02 0x27860c0e07c03838

def z820 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1f9327998fffffff 0xfc7e4c9e663fffff

def z821 : W := mkw 0xffdbb35449000000 0x03ff6ecd51240000 0xfffffffff1c0003f 0x73ffffffffc70000

def z822 : W := mkw 0xb202d800db402d80 0x22c80b60036d00b6 0xfe00d801ffc03fcf 0xcff8036007ff00ff

def z823 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1830781f03e3e33 0xb7860c1e07c0f8f8

def z824 : W := mkw 0xffdbb35402000500 0x03ff6ecd50080014 0xfffffffe0e000e3f 0x77fffffff8380038

def z825 : W := mkw 0xffdbb35404050000 0x03ff6ecd50101400 0xfffffffe0e01c03f 0x7bfffffff8380700

def z826 : W := mkw 0x9e99311400000000 0x027a64c450000000 0x1ffffffe0000003f 0x707ffffff8000000

def z827 : W := mkw 0x49fc05bb24bfd26e 0x4d27f016ec92ff49 0x01fc07fe003fc010 0x1007f01ff800ff00

def z828 : W := mkw 0x6dd3a35000000000 0x01b74e8d40000000 0xfffffffe0000003f 0x73fffffff8000000

def z829 : W := mkw 0x922400016dad8000 0x4648900005b6b600 0xfc000001ffffc002 0xcff0000007ffff00

def z830 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe1ffc7fff1fffff7 0xbf87ff1fffc7ffff

def z831 : W := mkw 0xffdbb35410000800 0x03ff6ecd50400020 0xfffffffe70000e3f 0x77fffffff9c00038

def z832 : W := mkw 0xdbd8035400000000 0x036f600d50000000 0xfffcfffe0000003f 0x53fff3fff8000000

def z833 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe3ffdffff1fffe37 0xb78fff7fffc7fff8

def z834 : W := mkw 0x49fc048924bfd24c 0x4d27f0122492ff49 0x01fc0000003fc010 0x0007f0000000ff00

def z835 : W := mkw 0x9a9c00004d858000 0x426a700001361600 0xff9c0001ffffc01f 0xcffe700007ffff00

def z836 : W := mkw 0x6166c6e9b0bafa78 0x15859b1ba6c2ebe9 0xe3ffe7f9f1ffffff 0xbf8fff9fe7c7ffff

def z837 : W := mkw 0x00244caba0faf2fa 0x14009132ae83ebcb 0x027cfc7f81fff1fd 0x9809f3f1fe07ffc7

def z838 : W := mkw 0x9e9d39144fc58580 0x627a74e4513f1616 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z839 : W := mkw 0x49fc06eb24bfd27a 0x5527f01bac92ff49 0x01fc07fe003fc010 0x1007f01ff800ff00

def z840 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d8327980e3fffe2 0xfc760c9e6038ffff

def z841 : W := mkw 0x0024080b00e0c0ca 0x000090202c038303 0x027cfc7f81f1c1fd 0x9809f3f1fe07c707

def z842 : W := mkw 0x9e9d311c4f85c54c 0x4a7a74c4713e1715 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z843 : W := mkw 0x6dfff801b6edad80 0x65b7ffe006dbb6b6 0x01fff800003ffff0 0x2007ffe00000ffff

def z844 : W := mkw 0x9e95391a4fc5c5ce 0x2a7a54e4693f1717 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z845 : W := mkw 0x960138004b400580 0x225804e0012d0016 0xfe033801ffc03fef 0xeff80ce007ff00ff

def z846 : W := mkw 0xba92dd98dd577acc 0x2aea4b7663755deb 0xe390df99f1ffc014 0x138e437e67c7ff00

def z847 : W := mkw 0x0cb569b386e7a7a6 0x0832d5a6ce1b9e9e 0x1fefdbe78fce0e06 0x647fbf6f9e3f3838

def z848 : W := mkw 0x6162cee1b07a3ab0 0x15858b3b86c1e8ea 0xe1e3c7e1f1fe3ff7 0xbf878f1f87c7f8ff

def z849 : W := mkw 0x0004480a80c0e0ca 0x000011202a030383 0x027cfc7f81c1f1fd 0x9809f3f1fe0707c7

def z850 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0xfd932799fe3fffff 0xfff64c9e67f8ffff

def z851 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3c7e1f00e3e26 0x37878f1f87c038f8

def z852 : W := mkw 0xb603b0004b000500 0x02d80ec0012c0014 0xfe03f801ffc03fef 0xeff80fe007ff00ff

def z853 : W := mkw 0x6166c6ebb0bafa7a 0x15859b1baec2ebe9 0xe3ffc7fff1fffe3f 0xbf8fff1fffc7fff8

def z854 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffc2419ffffc03f 0xdffff09067ffff00

def z855 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3fffff03e3e37 0xb7878fffffc0f8f8

def z856 : W := mkw 0x6162c6e9b03a7a78 0x15858b1ba6c0e9e9 0xe1e3e7f9f03e3ff7 0xb7878f9fe7c0f8ff

def z857 : W := mkw 0xdfd9335400000000 0x037f64cd50000000 0x1ffcfffe0000003d 0x507ff3fff8000000

def z858 : W := mkw 0x9e9d39184fc5c5cc 0x6a7a74e4613f1717 0x1e1c38180fc1c1c8 0x487870e0603f0707

def z859 : W := mkw 0x614286e0301a1a30 0x15850a1b80c06868 0xe18307e0700e0e02 0x37860c1f81c03838

def z860 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe183c7e0700e0e22 0x37860f1f81c03838

def z861 : W := mkw 0x9e9139104f450584 0x2a7a44e4413d1416 0x1e0038000fc001c8 0x487800e0003f0007

def z862 : W := mkw 0x2403b35400000000 0x00900ecd50000000 0x007ffffe00000030 0x3001fffff8000000

def z863 : W := mkw 0x6142c6e0b01a3a30 0x15850b1b82c068e8 0xe1830380700e3e02 0x27860c0e01c038f8

def z864 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe3efdfe7f03e3e37 0xb78fbf7f9fc0f8f8

def z865 : W := mkw 0x9e917d18cf5575cc 0x2a7a45f4633d55d7 0x1e10fc198ff1f1fd 0xd87843f0663fc7c7

def z866 : W := mkw 0x614286c0301a1a10 0x15850a1b00c06868 0xe1830780703e0e12 0x37860c1e01c0f838

def z867 : W := mkw 0x6142c2c0b00a2a10 0x15850b0b02c028a8 0xe183c380700e3e22 0x27860f0e01c038f8

def z868 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe7ff801ffc03fff 0xeff9ffe007ff00ff

def z869 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x1e7cfc7f8ff1f1ff 0xdc79f3f1fe3fc7c7

def z870 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1830380703e0e13 0xa7860c0e01c0f838

def z871 : W := mkw 0x6166cee3b0fabab2 0x15859b3b8ec3eaea 0xe3fffffff1fe3e3f 0xb78fffffffc7f8f8

def z872 : W := mkw 0x61468aca30cacada 0x15851a2b28c32b2b 0xe39f3b9e71cfcfca 0x2f8e7cee79c73f3f

def z873 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffcfffe0000001c 0x53fff3fff8000000

def z874 : W := mkw 0x2403e80092402d80 0x00900fa0024900b6 0xfe03f801ffc03fef 0xeff80fe007ff00ff

def z875 : W := mkw 0xb627b42b5bb0dd6a 0x22d89ed0ad6ec375 0xfc7f047e7e31ce12 0x77f1fc11f9f8c738

def z876 : W := mkw 0x9abc00016dad8000 0x466af00005b6b600 0xfe1c0001ffffc00f 0xcff8700007ffff00

def z877 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3c7e0703e3e32 0x37878f1f81c0f8f8

def z878 : W := mkw 0x616ac6e5b03a3a30 0x1585ab1b96c0e8e8 0xe1efc7e7f03e3e37 0xb787bf1f9fc0f8f8

def z879 : W := mkw 0x616282c1302a0a10 0x15858a0b04c0a828 0xe1830381f03e0e02 0xa7860c0e07c0f838

def z880 : W := mkw 0xdbfc02616dad8030 0x576ff00985b6b600 0xfffc0061ffffc01f 0xcffff00187ffff00

def z881 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe3e3c7e1f1fe3e3f 0xbf8f8f1f87c7f8f8

def z882 : W := mkw 0x6162c6ebb03a7a7a 0x15858b1baec0e9e9 0xe1e3c7fff03e3e37 0xb7878f1fffc0f8f8

def z883 : W := mkw 0xb603b35400000000 0x02d80ecd50000000 0xfe7ffffe0000003f 0x73f9fffff8000000

def z884 : W := mkw 0x00244cab82f2f7ee 0x08009132ae0bcbdf 0x0000000181f1ffc0 0x880000000607c7ff

def z885 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe63fc61ffc03fff 0xfff98ff187ff00ff

def z886 : W := mkw 0x416006e1203a1230 0x1505801b8480e848 0xe1e307e1f03e3e37 0xb7878c1f87c0f8f8

def z887 : W := mkw 0x6162ceebb07a7afa 0x15858b3baec1e9eb 0xe3e3fffff1fe3fff 0xbf8f8fffffc7f8ff

def z888 : W := mkw 0x4164048920bad248 0x050590122482eb49 0xe3ff2799f1ffffff 0xbf8ffc9e67c7ffff

def z889 : W := mkw 0x6162ceebb07a7afa 0x15858b3baec1e9eb 0xe1f3fffff03fffff 0xbf87cfffffc0ffff

def z890 : W := mkw 0x41644caba0faf2ea 0x05059132ae83ebcb 0xe3fffffff1ffffff 0xbf8fffffffc7ffff

def z891 : W := mkw 0x616686eb30bada7a 0x15859a1bacc2eb69 0xe1ff07fe703fce12 0x3787fc1ff9c0ff38

def z892 : W := mkw 0x6543b35400000000 0x01950ecd50000000 0xe3fffffe0000003f 0x338ffffff8000000

def z893 : W := mkw 0xb603fa44db402d80 0x22d80fe9136d00b6 0xfe03f867ffc03fef 0xeff80fe19fff00ff

def z894 : W := mkw 0x416044a1a03a3220 0x050581128680e8c8 0xe1e3c7e1f03e3e37 0xb7878f1f87c0f8f8

def z895 : W := mkw 0x0890011000000000 0x0022400440000000 0x03fcfffe0000003d 0x100ff3fff8000000

def z896 : W := mkw 0x614286c0301a1a10 0x15850a1b00c06868 0xe1830380703e3e02 0xa7860c0e01c0f8f8

def z897 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe183c380700e0e27 0x27860f0e01c03838

def z898 : W := mkw 0x9e9921184f05454c 0x4a7a6484613c1515 0x1c1020180e01c1c8 0x4870408060380707

def z899 : W := mkw 0x0000048000121200 0x0000001200004848 0xe1830781f03e3e37 0xb7860c1e07c0f8f8

def z900 : W := mkw 0x6142c2c0b00a2a10 0x15850b0b02c028a8 0xe1830381f00e3e02 0xa7860c0e07c038f8

def z901 : W := mkw 0x0890048804175248 0x0022401220105d49 0x1d9327980e3ffffb 0xfc764c9e6038ffff

def z902 : W := mkw 0x616286e1303a1a30 0x15858a1b84c0e868 0xe1e3c7e0703e0e37 0x37878f1f81c0f838

def z903 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e307e1f03e3e12 0xb7878c1f87c0f8f8

def z904 : W := mkw 0x6162c2e1b02a2a30 0x15858b0b86c0a8a8 0xe1e3c7e1f00e0e37 0x37878f1f87c03838

def z905 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffcd867ffffc01f 0xcffff3619fffff00

def z906 : W := mkw 0xf36eda45f9e8a880 0x67cdbb6917e7a2a2 0xe26cd867f1c00004 0x0389b3619fc70000

def z907 : W := mkw 0xffdbb35402000500 0x03ff6ecd50080014 0xfffffffe00003fff 0x73fffffff80000ff

def z908 : W := mkw 0xdfd9211000000000 0x037f648440000000 0xfffffffe0000003f 0x73fffffff8000000

def z909 : W := mkw 0x2403fff892527ffc 0x38900fffe24949ff 0x0003fff800003fe0 0x30000fffe00000ff

def z910 : W := mkw 0xffdbb35406050504 0x0bff6ecd50181414 0xfffffffe0e00003f 0x73fffffff8380000

def z911 : W := mkw 0x6166c6ebb0bafa7a 0x15859b1baec2ebe9 0xe1e3c7e1f03ffe37 0xb7878f1f87c0fff8

def z912 : W := mkw 0x416044a1b03a3a30 0x1505811286c0e8e8 0xe1e30781f03e3e37 0xb7878c1e07c0f8f8

def z913 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027ffc7f81f1ffff 0xbc09fff1fe07c7ff

def z914 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe3e3ffe1f1ffffff 0xbf8f8fff87c7ffff

def z915 : W := mkw 0x6162d6e5b03a3a30 0x15858b5b96c0e8e8 0xe1e3dfe7f03e3e37 0xb7878f7f9fc0f8f8

def z916 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe3fffffe700e0e3f 0x378ffffff9c03838

def z917 : W := mkw 0x2002c6e090123a30 0x10800b1b824048e8 0xe183c7e1f03e3e37 0xb7860f1f87c0f8f8

def z918 : W := mkw 0xb603f910db402d80 0x22d80fe4436d00b6 0xfe03ff99ffc03fef 0xfff80ffe67ff00ff

def z919 : W := mkw 0x920000004d050000 0x0248000001341400 0xfe000001ffffc00f 0xcff8000007ffff00

def z920 : W := mkw 0x6166c6e1b0baba30 0x15859b1b86c2eae8 0xe3fffffff1fffe3f 0xbf8fffffffc7fff8

def z921 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3c7e1f03e3e34 0x33878f1f87c0f8f8

def z922 : W := mkw 0x00244cabb6fffffe 0x1c009132aedbffff 0x00000001ffffffc0 0x8c00000007ffffff

def z923 : W := mkw 0x6166cee3b0fabab2 0x15859b3b8ec3eaea 0xe3efffe7f1fe3fff 0xbf8fbfff9fc7f8ff

def z924 : W := mkw 0x2002824000000000 0x00800a0900000000 0x027ffffe0000003d 0x3009fffff8000000

def z925 : W := mkw 0x4dd9235400000000 0x0137648d50000000 0x1ffffffe0000003f 0x707ffffff8000000

def z926 : W := mkw 0x6162dee1b07a3ab0 0x35858b7b86c1e8ea 0xe1e3dfe1f03e3e37 0xb7878f7f87c0f8f8

def z927 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfc03f801ffc03fe2 0xeff00fe007ff00ff

def z928 : W := mkw 0x2026ccab90f2faea 0x00809b32ae43cbeb 0xe3fffffff1ffffff 0xbf8fffffffc7ffff

def z929 : W := mkw 0x6142c6e0b01a3a30 0x15850b1b82c068e8 0xe1e3c7e0700e3e37 0x37878f1f81c038f8

def z930 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1830381f00e0e07 0xa7860c0e07c03838

def z931 : W := mkw 0x6162c241b0282800 0x05858b0906c0a0a0 0xe1e3c7e1f03e3e37 0xb7878f1f87c0f8f8

def z932 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d8307800e3ffff3 0xfc760c1e0038ffff

def z933 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffffffe0e00003f 0xfffffffff8380000

def z934 : W := mkw 0x6162cee1b07a3ab0 0x15858b3b86c1e8ea 0xe3e3dfe1f1fe3e37 0xb78f8f7f87c7f8f8

def z935 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0xe27cfc7ff1f1f1ff 0x9f89f3f1ffc7c7c7

def z936 : W := mkw 0x6162c2e1b02a2a30 0x15858b0b86c0a8a8 0xe1e3c3e1f00e3e27 0xa7878f0f87c038f8

def z937 : W := mkw 0x9e9131104f050504 0x2a7a44c4413c1414 0x1c0000000e000000 0x4070000000380000

def z938 : W := mkw 0x616286e1303a1a30 0x15858a1b84c0e868 0xe1e307e1f03e0e17 0xb7878c1f87c0f838

def z939 : W := mkw 0x616282c1302a0a10 0x15858a0b04c0a828 0xe1e3c7e1f03e0e37 0xb7878f1f87c0f838

def z940 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xe3fffffe00000034 0x338ffffff8000000

def z941 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e30381f03e3e17 0xa7878c0e07c0f8f8

def z942 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x03fcfc7f81fff1ff 0x9c0ff3f1fe07ffc7

def z943 : W := mkw 0x00244cab84f7f2ee 0x08009132ae13dfcb 0x0000000181fff1c0 0x880000000607ffc7

def z944 : W := mkw 0x2022c4a190323a20 0x00808b128640c8e8 0xe1e3c7e1f03e3e37 0xb7878f1f87c0f8f8

def z945 : W := mkw 0x6162c2c1b02a2a10 0x15858b0b06c0a8a8 0xe1e3c381f03e3e37 0xa7878f0e07c0f8f8

def z946 : W := mkw 0xffdbb35449000000 0x03ff6ecd51240000 0xfffffffe7e00003f 0x77fffffff9f80000

def z947 : W := mkw 0x6162cee9b07a7af8 0x15858b3ba6c1e9eb 0xe3f3fff9f1ffffff 0xbf8fcfffe7c7ffff

def z948 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe13fc19ffc03fff 0xfff84ff067ff00ff

def z949 : W := mkw 0x00244c2ba0f8f0ea 0x04009130ae83e3c3 0x027cfc7ff1fff1fd 0x9c09f3f1ffc7ffc7

def z950 : W := mkw 0x9ab400014da58000 0x026ad00005369600 0xfffc0001ffffc01f 0xcffff00007ffff00

def z951 : W := mkw 0xb603fb54db402d80 0x22d80fed536d00b6 0xfe7fffffffc03fff 0xfff9ffffffff00ff

def z952 : W := mkw 0x00244cab90f2fafa 0x10009132ae43cbeb 0x0000000181f1ffc0 0x880000000607c7ff

def z953 : W := mkw 0x6162c6e9b03a7a78 0x15858b1ba6c0e9e9 0xe3fffffff03fffff 0xbf8fffffffc0ffff

def z954 : W := mkw 0x9ebd25194fb5d54c 0x4a7af494653ed755 0x1e7c24198ff1f1fd 0xd879f090663fc7c7

def z955 : W := mkw 0xffdbb3544b000500 0x03ff6ecd512c0014 0xffffffffffc03fff 0xffffffffffff00ff

def z956 : W := mkw 0x9e9121184f05454c 0x0a7a4484613c1515 0x1e1020180fc1c1c8 0x48784080603f0707

def z957 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xffff0001fffffe3f 0xeffffc0007fffff8

def z958 : W := mkw 0x00244cab80f2f2ea 0x00009132ae03cbcb 0x027cfc7f81fffffd 0x9c09f3f1fe07ffff

def z959 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1f3c7e1f03ffe3f 0xbf87cf1f87c0fff8

def z960 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027cfc7f81f1f1f4 0x1009f3f1fe07c7c7

def z961 : W := mkw 0xdbd800004d050000 0x036f600001341400 0xfffc0001ffffc01f 0xcffff00007ffff00

def z962 : W := mkw 0x9ebd6d3bcff5f5ee 0x4a7af5b4ef3fd7d7 0x1e7cfc7f8ff1f1fd 0xd879f3f1fe3fc7c7

def z963 : W := mkw 0x920000004b000500 0x02480000012c0014 0xfe000001ffc03fcf 0xcff8000007ff00ff

def z964 : W := mkw 0xf34a935400000000 0x03cd2a4d50000000 0xe26cdffe00000004 0x1389b37ff8000000

def z965 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0x1ffffffe00000038 0x707ffffff8000000

def z966 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027cfc7f81f1c1dc 0x1809f3f1fe07c707

def z967 : W := mkw 0xb202c800db402d80 0x22c80b20036d00b6 0xfe03c001ffc03fef 0xeff80f0007ff00ff

def z968 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1f3e7f9f03e3e3f 0xb787cf9fe7c0f8f8

def z969 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9307980e3fffd2 0xfc764c1e6038ffff

def z970 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1e3c3e0700e0e06 0x27878f0f81c03838

def z971 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe3ffc7e1f03e3e3f 0xb78fff1f87c0f8f8

def z972 : W := mkw 0xb603fa60db402db0 0x32d80fe9836d00b6 0xfe03f861ffc03fef 0xeff80fe187ff00ff

def z973 : W := mkw 0xffdbb3547f0d0d00 0x67ff6ecd51fc3434 0xfffffffe7e0e0e3f 0x77fffffff9f83838

def z974 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xffeffffe00000026 0x73ffbffff8000000

def z975 : W := mkw 0xf34a924400000000 0x03cd2a4910000000 0xe3fffffe0000003f 0x338ffffff8000000

def z976 : W := mkw 0x614286c0301a1a10 0x15850a1b00c06868 0xe1e3c7e0703e3e37 0xb7878f1f81c0f8f8

def z977 : W := mkw 0x00240c2b00f0d0ea 0x00009030ac03c343 0x027cfc7e01f1c1fd 0x1809f3f1f807c707

def z978 : W := mkw 0x00244cabb0fafafa 0x14009132aec3ebeb 0x03fffffff1ffffff 0xbc0fffffffc7ffff

def z979 : W := mkw 0x6142c2c0b00a2a10 0x15850b0b02c028a8 0xe1e3c7e1f00e3e37 0xb7878f1f87c038f8

def z980 : W := mkw 0xd36c00016dad8000 0x474db00005b6b600 0xfe6c0001ffffc00f 0xcff9b00007ffff00

def z981 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027cfc7e01f1f1f8 0x1809f3f1f807c7c7

def z982 : W := mkw 0x6162ceebb07a7afa 0x15858b3baec1e9eb 0xe3fffffff03e3fff 0xb78fffffffc0f8ff

def z983 : W := mkw 0xb202c800d9402880 0x02c80b20036500a2 0xfe03f801ffc03fef 0xeff80fe007ff00ff

def z984 : W := mkw 0xdbf000016d2d0000 0x076fc00005b4b400 0xfff00001ffffc01f 0xcfffc00007ffff00

def z985 : W := mkw 0x6166c6e1b0baba30 0x15859b1b86c2eae8 0xe1e3c7e1f1fffe37 0xbf878f1f87c7fff8

def z986 : W := mkw 0x2c93b35400000000 0x00b24ecd50000000 0x1ffffffe0000003f 0x707ffffff8000000

def z987 : W := mkw 0x2403fdba92527fee 0x28900ff6ea4949ff 0x0003fffe00003fe0 0x30000ffff80000ff

def z988 : W := mkw 0xb603fb54db402d80 0x22d80fed536d00b6 0xfe03fb81ffc03fef 0xeff80fee07ff00ff

def z989 : W := mkw 0x6142ceeab05a7afa 0x15850b3baac169eb 0xe183fffe700e3fe2 0x37860ffff9c038ff

def z990 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffcf801ffffc03f 0xcffff3e007ffff00

def z991 : W := mkw 0x00244cab80f2f2ea 0x00009132ae03cbcb 0x027fffff81f1fffd 0xb809fffffe07c7ff

def z992 : W := mkw 0x00044c2a80d0f0ea 0x00001130aa0343c3 0x027cfc7e01c1f1fd 0x1809f3f1f80707c7

def z993 : W := mkw 0x2403fc8892527fcc 0x28900ff2224949ff 0x0003f80000003fe0 0x20000fe0000000ff

def z994 : W := mkw 0xdbfc01116dad8000 0x476ff00445b6b600 0xfffc0799ffffc01f 0xdffff01e67ffff00

def z995 : W := mkw 0xf36eda61f9e8a8b0 0x77cdbb6987e7a2a2 0xe26cd861f1c00004 0x0389b36187c70000

def z996 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe1e3fffff1fffff7 0xbf878fffffc7ffff

def z997 : W := mkw 0xffdbb354240d0000 0x47ff6ecd50903400 0xfffffffe000e003f 0x73fffffff8003800

def z998 : W := mkw 0x00244cabeffff7ee 0x4c009132afbfffdf 0x00000001ffffffc0 0x8c00000007ffffff

def z999 : W := mkw 0xf74bb35400000000 0x03dd2ecd50000000 0xe27ffffe0000003d 0x3389fffff8000000

def z1000 : W := mkw 0x2403feea92527ffa 0x30900ffbaa4949ff 0x0003fffe00003fe0 0x30000ffff80000ff

def z1001 : W := mkw 0xffdbb3546d0d0000 0x47ff6ecd51b43400 0xfffffffe7e3fc03f 0xfffffffff9f8ff00

def z1002 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe3efdfe7f1fffff7 0xbf8fbf7f9fc7ffff

def z1003 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1830780700e0e33 0x37860c1e01c03838

def z1004 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xff9c0001ffffc00a 0xcffe700007ffff00

def z1005 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfdfffffe00000032 0x73f7fffff8000000

def z1006 : W := mkw 0xffdbb35404050000 0x03ff6ecd50101400 0xfffffffe003fc03f 0x73fffffff800ff00

def z1007 : W := mkw 0xffdbb3545b000d00 0x23ff6ecd516c0034 0xfffffffe7e003fff 0xfffffffff9f800ff

def z1008 : W := mkw 0x49fc07dd24bfd24c 0x4d27f01f7492ff49 0x01fc07fe003fc010 0x1007f01ff800ff00

def z1009 : W := mkw 0xdbfc03556dad8000 0x476ff00d55b6b600 0xfffc0381ffffc01f 0xcffff00e07ffff00

def z1010 : W := mkw 0x0c91211006050500 0x0032448440181414 0x1d9327980e3ffffb 0xfc764c9e6038ffff

def z1011 : W := mkw 0x96016800db402d80 0x225805a0036d00b6 0xfe032001ffc03fef 0xeff80c8007ff00ff

def z1012 : W := mkw 0x6166ceebb0fafafa 0x15859b3baec3ebeb 0xe3effffff1fe3ff7 0xb78fbfffffc7f8ff

def z1013 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d8323800e3fffeb 0xec760c8e0038ffff

def z1014 : W := mkw 0x6ddbb35400000000 0x01b76ecd50000000 0x03fffffe0000003d 0x300ffffff8000000

def z1015 : W := mkw 0x6166cee3b0fabab2 0x15859b3b8ec3eaea 0xe1e3c7e1f1fe3e37 0xb7878f1f87c7f8f8

def z1016 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe00f801ffc03fcc 0xcff803e007ff00ff

def z1017 : W := mkw 0xb603e000db002d00 0x02d80f80036c00b4 0xfe03e001ffc03fef 0xeff80f8007ff00ff

def z1018 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xff800001ffffc00f 0xcffe000007ffff00

def z1019 : W := mkw 0xffdbb35412000d00 0x23ff6ecd50480034 0xfffffffe00000e3f 0x73fffffff8000038

def z1020 : W := mkw 0xffdbb3547f0d0d00 0x67ff6ecd51fc3434 0xfd8303807e0e0e02 0x67f60c0e01f83838

def z1021 : W := mkw 0x614286c8301a5a58 0x15850a1b20c06969 0xe1932798703ffffb 0xbf864c9e61c0ffff

def z1022 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfc03c001ffc03fe7 0xeff00f0007ff00ff

def z1023 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffffffe000031ff 0xfbfffffff80000c7

def z1024 : W := mkw 0x6166c6e3b0baba32 0x15859b1b8ec2eae8 0xe1efc7e7f03e3e37 0xb787bf1f9fc0f8f8

def z1025 : W := mkw 0xf743b24000000000 0x03dd0ec900000000 0xfffffffe0000003f 0x73fffffff8000000

def z1026 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfe7c0001ffffc00c 0xcff9f00007ffff00

def z1027 : W := mkw 0x00244c2bb0f8f8fa 0x14009130aec3e3e3 0x027cfc7ff1f1f1fd 0x9809f3f1ffc7c7c7

def z1028 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027cf87f81f1f1cc 0x8809f3e1fe07c7c7

def z1029 : W := mkw 0xffdbb35449000000 0x03ff6ecd51240000 0xfffffffe0fc0003f 0x7bfffffff83f0000

def z1030 : W := mkw 0x49d8035400000000 0x0127600d50000000 0x01fcfffe00000030 0x1007f3fff8000000

def z1031 : W := mkw 0xf74bb35400000000 0x03dd2ecd50000000 0xfe6ffffe0000002f 0x73f9bffff8000000

def z1032 : W := mkw 0x6166c6ebb0bafa7a 0x15859b1baec2ebe9 0xe1ffe7fff03fffff 0xbf87ff9fffc0ffff

def z1033 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3c7e1f03e0e16 0x37878f1f87c0f838

def z1034 : W := mkw 0x49d8035400000000 0x0127600d50000000 0x03fcdffe00000014 0x100ff37ff8000000

def z1035 : W := mkw 0x00244cabfdfffafa 0x54009132aff7ffeb 0x00000001ffffffc0 0x8c00000007ffffff

def z1036 : W := mkw 0x2403e800db402d80 0x20900fa0036d00b6 0xfc03e001ffc03fef 0xeff00f8007ff00ff

def z1037 : W := mkw 0x0401211000000000 0x0010048440000000 0x027ffffe0000003d 0x3009fffff8000000

def z1038 : W := mkw 0x616ec6e1b0baba30 0x5585bb1b86c2eae8 0xe1efc7e1f03e3e37 0xb787bf1f87c0f8f8

def z1039 : W := mkw 0x6142c2e0b00a2a30 0x15850b0b82c028a8 0xe183c3e0700e0e02 0x27860f0f81c03838

def z1040 : W := mkw 0x00244cab90f2fafa 0x10009132ae43cbeb 0x027cfc7f81f1fffd 0x9809f3f1fe07c7ff

def z1041 : W := mkw 0x089004880617574c 0x0822401220185d5d 0x1d9307800e3ffffb 0xfc764c1e0038ffff

def z1042 : W := mkw 0x6ddbb35400000000 0x01b76ecd50000000 0x1dfffffe0000003b 0x7077fffff8000000

def z1043 : W := mkw 0x614286c0301a1a10 0x15850a1b00c06868 0xe1830780700e3e22 0x37860c1e01c038f8

def z1044 : W := mkw 0x00244caba0faf2fa 0x14009132ae83ebcb 0x0000000181fff1c0 0x880000000607ffc7

def z1045 : W := mkw 0x6142c6e0b01a3a30 0x15850b1b82c068e8 0xe183c7e0703e3e33 0xb7860f1f81c0f8f8

def z1046 : W := mkw 0xb603b0005b000d00 0x22d80ec0016c0034 0xfe032001ffc03fef 0xeff80c8007ff00ff

def z1047 : W := mkw 0x2002c08090022a00 0x00800b02024008a8 0xe183c381f00e3e27 0xa7860f0e07c038f8

def z1048 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe033801ffc03fca 0xeff80ce007ff00ff

def z1049 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1830380700e3e23 0xa7860c0e01c038f8

def z1050 : W := mkw 0x616282e1302a0a30 0x15858a0b84c0a828 0xe1e303e0700e0e02 0x27878c0f81c03838

def z1051 : W := mkw 0x6162c6e9b03a7a78 0x15858b1ba6c0e9e9 0xe1f3c7f9f03ffe37 0xb787cf1fe7c0fff8

def z1052 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9323980e3fffca 0xec764c8e6038ffff

def z1053 : W := mkw 0x0c91248006171700 0x0032449200185c5c 0x1d9327800e3ffffb 0xfc764c9e0038ffff

def z1054 : W := mkw 0x9ab400016dad8000 0x466ad00005b6b600 0xff900001ffffc01f 0xcffe400007ffff00

def z1055 : W := mkw 0xb603fa40db402d80 0x22d80fe9036d00b6 0xfe03ffe1ffc03fef 0xfff80fff87ff00ff

def z1056 : W := mkw 0x2002cc8890527ac8 0x00800b32224149eb 0xe393ff99f1ffffff 0xbf8e4ffe67c7ffff

def z1057 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe183c7e1f03e3e22 0xb7860f1f87c0f8f8

def z1058 : W := mkw 0x6162ceebb07a7afa 0x15858b3baec1e9eb 0xe1e3c7e1f03e3ff7 0xb7878f1f87c0f8ff

def z1059 : W := mkw 0x616282c1302a0a10 0x15858a0b04c0a828 0xe1e30380703e0e12 0x27878c0e01c0f838

def z1060 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffc2001fffff1ff 0xcffff08007ffffc7

def z1061 : W := mkw 0x616286e1303a1a30 0x15858a1b84c0e868 0xe1e307e0703e3e33 0xb7878c1f81c0f8f8

def z1062 : W := mkw 0xffdbb3546d0d0000 0x47ff6ecd51b43400 0xffffffffffce003f 0xffffffffffff3800

def z1063 : W := mkw 0x9e9131184f05454c 0x2a7a44c4613c1515 0x1c1020180e01c1c8 0x4870408060380707

def z1064 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x027cfc7f81c1f1ec 0x1809f3f1fe0707c7

def z1065 : W := mkw 0xffdbb3544d050000 0x03ff6ecd51341400 0xffffffffffffc03f 0xffffffffffffff00

def z1066 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1ffc7fff03e3e37 0xb787ff1fffc0f8f8

def z1067 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1fff27980e3fffff 0xfc7ffc9e6038ffff

def z1068 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d93fffe0e3ffffb 0xfc764ffff838ffff

def z1069 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfd900001ffffc01b 0xcff6400007ffff00

def z1070 : W := mkw 0x6166cae3b0eaaab2 0x15859b2b8ec3aaaa 0xe3efdbe7f1ce0e06 0x278fbf6f9fc73838

def z1071 : W := mkw 0x9e9d291a4fc5c5ce 0x4a7a74a4693f1717 0x1e1c381e0fc1c1c8 0x487870e0783f0707

def z1072 : W := mkw 0x92004800db402d80 0x22480120036d00b6 0xfc000001ffc03fc2 0xcff0000007ff00ff

def z1073 : W := mkw 0x0000035400000000 0x0000000d50000000 0x027cfffe0000003d 0x1009f3fff8000000

def z1074 : W := mkw 0x6162cee1b07a3ab0 0x15858b3b86c1e8ea 0xe3fffffff1fe3fff 0xbf8fffffffc7f8ff

def z1075 : W := mkw 0x0024482b80e0e0ea 0x00009120ae038383 0x027cf87f81f1c1dd 0x8809f3e1fe07c707

def z1076 : W := mkw 0x69da935400000000 0x01a76a4d50000000 0x01fcdffe00000010 0x1007f37ff8000000

def z1077 : W := mkw 0x00244cabdff7ffee 0x28009132af7fdfff 0x00000001ffffffc0 0x8c00000007ffffff

def z1078 : W := mkw 0xfbda935400000000 0x03ef6a4d50000000 0xe3ffdffe00000037 0x338fff7ff8000000

def z1079 : W := mkw 0x040124880617574c 0x0810049220185d5d 0x1d8327800e3ffffb 0xfc760c9e0038ffff

def z1080 : W := mkw 0xd364000169a88000 0x074d900005a6a200 0xfffc0001ffffc01f 0xcffff00007ffff00

def z1081 : W := mkw 0xffdbb3545b000d00 0x23ff6ecd516c0034 0xffffffffffc00e3f 0xffffffffffff0038

def z1082 : W := mkw 0x6142c6c090123a00 0x01850b1b024048e8 0xe1e3c7e1f03e3e37 0xb7878f1f87c0f8f8

def z1083 : W := mkw 0x616682c130aa8a10 0x15859a0b04c2aa28 0xe3ff0381f1ffce1f 0xaf8ffc0e07c7ff38

def z1084 : W := mkw 0xfbda935400000000 0x03ef6a4d50000000 0xfffcdffe0000001f 0x53fff37ff8000000

def z1085 : W := mkw 0x0024040900b0d048 0x000090102402c341 0x027cfc7f81f1f1fd 0x9809f3f1fe07c7c7

def z1086 : W := mkw 0x0c91219006070704 0x0832448640181c1c 0x1d9323800e3ffffb 0xec764c8e0038ffff

def z1087 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe1e3c3e1f03e3e06 0xa7878f0f87c0f8f8

def z1088 : W := mkw 0x0024480180e0a080 0x0000912006038282 0x027cfc7f81f1f1fd 0x9809f3f1fe07c7c7

def z1089 : W := mkw 0x92004800db402d80 0x22480120036d00b6 0xfe00f801ffc03fef 0xcff803e007ff00ff

def z1090 : W := mkw 0x00244c2b80f0f0ea 0x00009130ae03c3c3 0x03ffffff81f1f1ff 0xb80ffffffe07c7c7

def z1091 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe13f801fff1ffff 0xeff84fe007ffc7ff

def z1092 : W := mkw 0x41400080200a0200 0x0505000200802808 0xe1830380700e0e02 0x27860c0e01c03838

def z1093 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9327980e3ffff2 0x74764c9e6038ffff

def z1094 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1f9f3f9e0e3ffffb 0xfc7e7cfe7838ffff

def z1095 : W := mkw 0x0024482b80e0e0ea 0x00009120ae038383 0x027cfc7f81c1c1fd 0x1809f3f1fe070707

def z1096 : W := mkw 0x614282c0300a0a10 0x15850a0b00c02828 0xe1e307e0700e0e12 0x37878c1f81c03838

def z1097 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xffec0001ffffc006 0xcfffb00007ffff00

def z1098 : W := mkw 0xffdbb35404050000 0x03ff6ecd50101400 0xfffffffe0e0e003f 0x77fffffff8383800

def z1099 : W := mkw 0x41400480201a1200 0x0505001200806848 0xe1830780703e3e33 0xb7860c1e01c0f8f8

def z1100 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xffffffff81c0003f 0xfbfffffffe070000

def z1101 : W := mkw 0xdbfc02416dad8000 0x476ff00905b6b600 0xfffc07e1ffffc01f 0xdffff01f87ffff00

def z1102 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffc0001ffffc016 0x47fff00007ffff00

def z1103 : W := mkw 0x6162c6e1b03a3a30 0x15858b1b86c0e8e8 0xe183c381f03e3e27 0xa7860f0e07c0f8f8

def z1104 : W := mkw 0x0401248802125748 0x001004922008495d 0x1d9327980e3ffffb 0xfc764c9e6038ffff

def z1105 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1d9327980e3ffff8 0x78764c9e6038ffff

def z1106 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xfe6ff867ffc03fef 0xeff9bfe19fff00ff

def z1107 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffc381fffffc01f 0xcffff0e07fffff00

def z1108 : W := mkw 0x6166c6e1b0baba30 0x15859b1b86c2eae8 0xe3efc7e1f1fe3e37 0xb78fbf1f87c7f8f8

def z1109 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1f93ff980e3fffff 0xfc7e4ffe6038ffff

def z1110 : W := mkw 0xdbfc00016dad8000 0x476ff00005b6b600 0xfffc0001ffffc01c 0x4bfff00007ffff00

def z1111 : W := mkw 0xb603f800db402d80 0x22d80fe0036d00b6 0xff83ff81ffc03fff 0xfffe0ffe07ff00ff

def z1112 : W := mkw 0xffdbb35402000500 0x03ff6ecd50080014 0xfffffffe0e0001ff 0x7bfffffff8380007

def z1113 : W := mkw 0x6166c6e1b0baba30 0x15859b1b86c2eae8 0xe1ffc7e1f03ffe37 0xb787ff1f87c0fff8

def z1114 : W := mkw 0xdbd800006d0d0000 0x476f600001b43400 0xff900001ffffc01f 0xcffe400007ffff00

def z1115 : W := mkw 0x0c9125980617574c 0x0832449660185d5d 0x1dff27fe0e3ffffb 0xfc77fc9ff838ffff

def z1116 : W := mkw 0xffdbb35400000000 0x03ff6ecd50000000 0xfffffffff000003f 0xf7ffffffffc00000

def z1117 : W := mkw 0x6166cee1b0fabab0 0x15859b3b86c3eaea 0xe3ffffe1f1ffffff 0xbf8fffff87c7ffff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z8,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z9,z6]),(0,[z10,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z2,z11,z4,z6])],[(1,[z7,z0,z3,z4,z5,z6]),(0,[z7,z12,z0,z2,z4,z5,z6]),(0,[z13,z7,z0,z14,z4,z5,z6]),(0,[z7,z0,z2,z15,z4,z5,z6]),(1,[z7,z16,z2,z4,z17,z6]),(0,[z7,z0,z18,z2,z19,z4,z6])],[(0,[z20,z7,z0,z2,z4,z5,z6]),(0,[z7,z16,z0,z3,z4,z5,z6]),(0,[z21,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z22,z2,z4,z5,z6]),(0,[z23,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z24,z4,z5,z6]),(0,[z7,z0,z25,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z26,z6])],[(0,[z7,z0,z27,z28,z4,z5,z6]),(0,[z7,z0,z29,z2,z4,z5,z6]),(0,[z7,z0,z30,z2,z4,z5,z6]),(0,[z31,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z2,z4,z5,z32]),(0,[z7,z0,z33,z4,z5,z17,z6]),(0,[z7,z0,z2,z4,z5,z6,z34]),(0,[z7,z35,z0,z2,z4,z5,z6])],[(0,[z36,z7,z0,z37,z4,z5,z6]),(0,[z7,z16,z0,z2,z4,z5,z32]),(0,[z7,z0,z2,z4,z5,z38,z6])],[(0,[z7,z0,z2,z4,z39,z5,z6]),(0,[z7,z0,z2,z40,z4,z5,z6]),(0,[z7,z0,z2,z41,z4,z5,z6]),(0,[z7,z0,z42,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z43,z5,z6]),(0,[z44,z7,z0,z2,z4,z5,z6]),(0,[z45,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z46,z2,z4,z5,z6]),(0,[z7,z47,z0,z2,z19,z5,z6]),(0,[z7,z0,z48,z2,z4,z5,z6]),(1,[z7,z0,z2,z49,z5,z50]),(0,[z7,z51,z0,z2,z4,z5,z6]),(0,[z7,z0,z52,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z53,z27,z4,z5,z6]),(0,[z7,z0,z54,z2,z4,z5,z6]),(0,[z7,z0,z2,z55,z4,z5,z6])],[(0,[z36,z7,z0,z2,z4,z5,z6]),(0,[z7,z56,z0,z2,z4,z5,z6]),(1,[z7,z57,z2,z4,z5,z6]),(1,[z7,z58,z59,z4,z5,z6]),(0,[z7,z60,z0,z2,z4,z5,z6])],[(0,[z7,z0,z3,z61,z4,z5,z6]),(1,[z7,z0,z62,z4,z5,z6]),(0,[z7,z16,z0,z2,z4,z5,z6]),(0,[z7,z0,z63,z2,z4,z5,z6]),(0,[z7,z0,z2,z64,z4,z5,z6])],[(0,[z7,z65,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z66]),(1,[z7,z0,z67,z2,z4,z5]),(0,[z7,z0,z2,z68,z4,z5,z6]),(0,[z7,z0,z2,z19,z4,z5,z69]),(0,[z7,z0,z2,z4,z5,z6,z69])],[(1,[z7,z0,z70,z4,z5,z6]),(0,[z7,z0,z71,z2,z4,z5,z6]),(0,[z7,z0,z2,z72,z4,z5,z6]),(0,[z7,z0,z73,z2,z4,z5,z6])],[(0,[z74,z7,z0,z2,z4,z5,z6]),(1,[z75,z0,z2,z4,z76,z6]),(1,[z7,z77,z2,z4,z78,z6]),(0,[z7,z79,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z80,z4,z5,z6]),(1,[z7,z0,z81,z4,z5,z6]),(0,[z7,z82,z0,z2,z4,z5,z6])],[(0,[z7,z0,z27,z61,z4,z5,z6]),(0,[z7,z83,z0,z2,z4,z5,z6])]],
   [[(0,[z0,z2,z84,z4,z85,z5,z6]),(1,[z7,z0,z86,z4,z5,z6]),(0,[z7,z58,z59,z2,z4,z5,z6]),(0,[z7,z47,z0,z2,z4,z5,z9]),(0,[z7,z77,z0,z2,z4,z5,z6]),(0,[z7,z0,z87,z2,z4,z5,z6]),(0,[z7,z0,z88,z2,z4,z5,z89]),(0,[z90,z7,z0,z64,z4,z5,z6]),(0,[z7,z0,z2,z49,z4,z5,z6])],[(1,[z7,z0,z91,z4,z5,z6])],[(0,[z7,z0,z92,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z93,z5,z6]),(0,[z94,z7,z95,z0,z2,z4,z5]),(0,[z7,z0,z2,z4,z5,z6,z96]),(0,[z7,z0,z33,z2,z4,z5,z6]),(0,[z7,z0,z97,z2,z4,z98,z6])],[(0,[z7,z0,z2,z4,z99,z5,z6]),(1,[z7,z0,z54,z2,z5,z6]),(0,[z100,z7,z0,z2,z4,z5,z6])],[(1,[z101,z1,z2,z4,z5,z6]),(0,[z7,z0,z2,z102,z4,z5,z6]),(0,[z103,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z104,z105,z5,z6]),(0,[z7,z0,z2,z4,z5,z106,z6]),(0,[z7,z0,z2,z107,z4,z5,z6])],[(0,[z7,z0,z3,z4,z5,z6,z108]),(0,[z7,z0,z2,z4,z5,z6,z109]),(0,[z7,z0,z2,z4,z5,z6,z110])],[(0,[z7,z0,z2,z111,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z5,z113]),(0,[z7,z0,z114,z2,z4,z5,z6]),(0,[z115,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z97,z2,z116,z4,z6]),(0,[z117,z7,z0,z118,z2,z4,z6])],[(0,[z119,z7,z0,z2,z4,z5,z6]),(0,[z7,z120,z0,z2,z4,z5,z6]),(0,[z7,z0,z121,z2,z4,z5,z6]),(0,[z7,z0,z88,z2,z4,z5,z122])]],
   [[(0,[z7,z123,z0,z2,z4,z5,z6]),(1,[z7,z0,z124,z2,z4,z5]),(0,[z7,z0,z2,z125,z4,z126,z6]),(0,[z7,z0,z2,z4,z5,z127,z6]),(0,[z7,z0,z2,z4,z5,z6,z128])],[(0,[z7,z129,z0,z2,z4,z5,z6]),(0,[z130,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z131,z4,z5,z6]),(0,[z132,z7,z2,z4,z5,z89,z6])],[(0,[z133,z7,z0,z2,z4,z5,z6]),(0,[z130,z134,z0,z2,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z6,z108])],[(0,[z7,z0,z104,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z135]),(0,[z7,z0,z2,z4,z5,z89,z122])],[(0,[z7,z136,z0,z27,z4,z5,z6]),(0,[z7,z0,z137,z2,z4,z5,z6]),(0,[z138,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z139]),(0,[z7,z0,z97,z4,z5,z98,z6]),(0,[z7,z0,z140,z2,z4,z5,z6]),(0,[z141,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z88,z2,z4,z142,z6])],[(0,[z132,z94,z7,z0,z2,z4,z5]),(0,[z7,z16,z0,z2,z19,z4,z6]),(0,[z7,z0,z2,z143,z4,z5,z6]),(0,[z7,z0,z2,z4,z144,z5,z6]),(0,[z145,z7,z0,z2,z4,z5,z6])],[(0,[z146,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z147,z18,z2,z6]),(0,[z7,z0,z148,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z6,z149]),(0,[z7,z0,z2,z150,z4,z5,z6]),(0,[z7,z0,z27,z116,z4,z5,z6]),(0,[z7,z0,z2,z151,z4,z5,z6]),(0,[z7,z0,z2,z4,z152,z5,z6]),(0,[z7,z0,z153,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z154,z5,z6]),(0,[z7,z0,z2,z155,z4,z5,z6]),(0,[z7,z156,z0,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z157,z5,z6]),(1,[z158,z0,z3,z4,z5,z6]),(1,[z7,z0,z2,z4,z5,z9]),(0,[z7,z0,z2,z159,z4,z5,z6]),(0,[z7,z0,z160,z97,z4,z5,z6]),(0,[z7,z161,z0,z2,z4,z5,z6]),(0,[z162,z7,z0,z2,z4,z5,z50])],[(0,[z7,z0,z3,z4,z5,z6,z113]),(0,[z7,z0,z2,z84,z4,z5,z163]),(0,[z7,z0,z2,z4,z164,z5,z6])],[(0,[z7,z0,z118,z3,z4,z5,z6]),(0,[z165,z7,z0,z2,z4,z5,z6])],[(0,[z13,z166,z0,z2,z4,z5,z6])],[(0,[z7,z0,z167,z2,z4,z5,z6]),(0,[z7,z0,z168,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z169,z6]),(0,[z7,z0,z170,z2,z4,z5,z6])],[(0,[z75,z7,z0,z171,z4,z5,z6]),(0,[z7,z0,z172,z2,z4,z5,z6])],[(0,[z173,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z98,z6]),(0,[z7,z0,z174,z3,z4,z5,z6]),(1,[z7,z0,z33,z4,z5,z6]),(0,[z175,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z176]),(0,[z7,z177,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z178])],[(0,[z7,z0,z27,z4,z5,z6,z50]),(0,[z179,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z76,z6,z122]),(0,[z7,z0,z2,z4,z5,z180,z6])]],
   [[(0,[z181,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z182,z27,z4,z5,z6]),(0,[z7,z0,z2,z183,z4,z5,z6]),(0,[z7,z16,z0,z147,z2,z4,z6]),(0,[z7,z77,z2,z4,z78,z5,z6])],[(0,[z7,z184,z0,z2,z4,z5,z6]),(0,[z7,z0,z185,z2,z4,z5,z6]),(0,[z75,z0,z2,z4,z5,z76,z6]),(0,[z7,z0,z2,z4,z5,z6,z6]),(0,[z7,z0,z2,z186,z4,z5,z6]),(0,[z7,z0,z2,z19,z4,z5,z6])],[(1,[z7,z0,z67,z3,z4,z5]),(0,[z13,z7,z2,z28,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z187]),(0,[z7,z0,z188,z2,z4,z5,z6]),(0,[z7,z0,z189,z2,z4,z5,z6]),(0,[z7,z0,z2,z190,z4,z5,z6])],[(0,[z7,z0,z27,z4,z5,z98,z6]),(0,[z7,z0,z191,z2,z4,z5,z6]),(0,[z192,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z193,z2,z4,z5,z6])],[(0,[z194,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z18,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z195,z5,z6]),(0,[z7,z0,z2,z196,z4,z5,z6]),(0,[z7,z47,z0,z18,z2,z5,z6]),(0,[z7,z197,z0,z2,z4,z5,z6])],[(0,[z198,z7,z0,z2,z4,z5,z6]),(0,[z134,z7,z0,z3,z4,z5,z6]),(0,[z7,z95,z0,z3,z4,z5,z6]),(1,[z13,z7,z28,z4,z5,z6]),(0,[z7,z0,z199,z2,z4,z5,z6])],[(0,[z7,z0,z3,z4,z78,z5,z6]),(0,[z90,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z84,z4,z5,z6]),(0,[z94,z7,z0,z2,z4,z5,z200]),(1,[z166,z0,z2,z4,z5,z6]),(0,[z201,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z174,z2,z4,z5,z6]),(0,[z7,z0,z202,z2,z4,z5,z6])],[(0,[z7,z203,z0,z1,z2,z4,z5]),(0,[z7,z0,z204,z2,z4,z5,z6]),(0,[z117,z7,z0,z118,z2,z4,z5]),(0,[z7,z0,z205,z2,z4,z5,z6])]],
   [[(0,[z181,z7,z0,z2,z4,z5,z6])],[(0,[z134,z0,z2,z3,z4,z5,z6]),(0,[z117,z7,z0,z2,z4,z206,z6]),(0,[z7,z0,z207,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z208,z6]),(0,[z7,z0,z2,z4,z5,z209,z6])],[(0,[z7,z0,z2,z4,z5,z210,z6]),(0,[z211,z7,z0,z2,z4,z5,z6]),(0,[z212,z7,z0,z2,z4,z5,z6])],[(0,[z7,z213,z0,z2,z4,z5,z6]),(0,[z7,z0,z88,z27,z4,z5,z6]),(0,[z214,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z2,z215,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z216]),(0,[z132,z7,z95,z2,z4,z5,z6]),(0,[z7,z0,z104,z105,z4,z5,z6]),(0,[z7,z0,z217,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z218,z5,z6])],[(0,[z7,z47,z0,z3,z4,z5,z6]),(0,[z7,z0,z160,z3,z4,z5,z6]),(0,[z7,z0,z2,z219,z4,z5,z6]),(0,[z7,z0,z220,z2,z4,z5,z6]),(0,[z7,z0,z2,z221,z4,z5,z6]),(0,[z7,z95,z2,z4,z5,z6,z108]),(0,[z7,z0,z2,z222,z4,z5,z6]),(0,[z7,z0,z2,z223,z4,z5,z6])],[(0,[z134,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z224,z4,z5,z6]),(1,[z94,z0,z2,z4,z5,z200]),(0,[z7,z58,z0,z116,z4,z5,z6]),(0,[z7,z0,z2,z225,z4,z5,z6]),(0,[z7,z95,z0,z2,z4,z5,z6]),(0,[z226,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z227,z6])],[(0,[z7,z0,z147,z27,z4,z5,z6]),(0,[z36,z7,z0,z2,z85,z5,z6]),(0,[z13,z7,z58,z2,z4,z5,z6]),(0,[z7,z0,z104,z2,z5,z38,z6])],[(0,[z7,z0,z2,z228,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z229,z6]),(0,[z7,z0,z2,z85,z5,z6,z50])]],
   [[(0,[z7,z0,z3,z4,z126,z5,z6]),(0,[z230,z7,z0,z2,z4,z5,z6]),(0,[z231,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z232,z2,z4,z5,z6])],[(1,[z0,z3,z4,z5,z200,z6]),(0,[z7,z0,z233,z2,z4,z5,z6]),(0,[z7,z0,z2,z234,z4,z5,z6]),(0,[z7,z0,z2,z235,z4,z5,z6]),(0,[z7,z0,z14,z2,z5,z38,z6])],[(0,[z7,z0,z3,z4,z5,z17,z6]),(0,[z74,z7,z0,z2,z85,z5,z6]),(0,[z94,z7,z0,z88,z2,z4,z5])],[(0,[z158,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z76,z6]),(0,[z7,z0,z3,z4,z206,z5,z6]),(0,[z7,z236,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z237,z4,z5,z6]),(0,[z7,z0,z2,z4,z238,z5,z6]),(0,[z7,z0,z2,z239,z4,z5,z6]),(0,[z240,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z160,z2,z4,z5,z6])],[(0,[z7,z0,z2,z241,z4,z5,z6]),(0,[z7,z0,z27,z4,z126,z5,z6]),(0,[z7,z0,z2,z4,z206,z5,z242]),(0,[z7,z0,z2,z19,z4,z6,z122]),(0,[z7,z0,z2,z4,z243,z5,z6])],[(1,[z7,z0,z2,z40,z5,z6]),(0,[z7,z244,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z245,z6]),(0,[z7,z0,z14,z4,z5,z38,z6]),(0,[z7,z0,z246,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z50]),(0,[z7,z0,z2,z247,z4,z5,z6])],[(0,[z134,z7,z1,z2,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z17,z6]),(1,[z7,z0,z2,z4,z5,z163]),(1,[z7,z0,z171,z4,z5,z6]),(0,[z7,z0,z174,z2,z4,z5,z248]),(0,[z7,z0,z249,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z3,z3,z4,z5,z6]),(0,[z7,z0,z27,z4,z206,z5,z6]),(0,[z7,z77,z0,z2,z4,z78,z6]),(0,[z7,z0,z88,z2,z4,z5,z108]),(0,[z7,z0,z2,z105,z4,z5,z6])],[(1,[z7,z0,z250,z4,z5,z6]),(1,[z7,z0,z251,z2,z4,z6]),(0,[z7,z252,z0,z2,z4,z5,z6])],[],[(0,[z7,z0,z2,z253,z4,z5,z6]),(0,[z74,z0,z2,z4,z85,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z254]),(0,[z7,z2,z4,z78,z5,z17,z6])],[(0,[z7,z0,z255,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z256,z6]),(0,[z7,z0,z257,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z258]),(0,[z7,z0,z2,z4,z5,z259,z6]),(0,[z7,z0,z105,z4,z5,z38,z6]),(0,[z7,z0,z260,z2,z4,z5,z6])],[(1,[z134,z0,z3,z4,z5,z6]),(0,[z7,z261,z0,z2,z4,z5,z6]),(0,[z7,z0,z27,z3,z4,z5,z6]),(1,[z132,z7,z2,z4,z5,z89]),(0,[z262,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z263,z4,z5,z6]),(0,[z7,z0,z2,z264,z4,z5,z6])],[],[(0,[z36,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z265,z6]),(0,[z7,z58,z0,z97,z4,z5,z6])]],
   [[(1,[z7,z0,z266,z4,z5,z6]),(1,[z7,z0,z37,z4,z5,z6])],[(0,[z162,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z267,z6]),(1,[z7,z0,z2,z125,z4,z6])],[(0,[z132,z7,z0,z3,z4,z5,z6]),(0,[z268,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z269,z5,z6])],[(0,[z270,z7,z0,z2,z4,z5,z6]),(0,[z134,z271,z0,z2,z4,z5,z6]),(0,[z74,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z124,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z122])],[(1,[z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z255,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z272,z6]),(0,[z90,z7,z0,z2,z64,z4,z5])],[(0,[z7,z77,z0,z27,z4,z5,z6]),(0,[z7,z0,z273,z2,z4,z5,z6]),(0,[z7,z0,z2,z274,z4,z5,z6])],[(0,[z94,z7,z0,z3,z4,z5,z6]),(0,[z74,z7,z0,z275,z4,z5,z6]),(0,[z7,z0,z2,z4,z276,z5,z6]),(1,[z277,z0,z2,z4,z5,z6]),(0,[z7,z278,z0,z2,z4,z5,z6]),(0,[z7,z0,z147,z2,z4,z6,z122]),(0,[z279,z7,z0,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z3,z4,z5,z6,z280]),(0,[z7,z0,z2,z4,z5,z281,z6]),(0,[z7,z282,z0,z2,z4,z5,z6]),(0,[z283,z7,z0,z2,z4,z5,z6]),(0,[z284,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z118,z88,z2,z4,z5])],[(0,[z36,z0,z2,z84,z4,z5,z6]),(0,[z7,z285,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z89,z50]),(1,[z7,z0,z160,z116,z4,z6])],[(0,[z112,z7,z0,z286,z4,z5,z6]),(0,[z0,z2,z4,z5,z200,z6,z113]),(0,[z287,z7,z0,z2,z4,z5,z6])],[(0,[z7,z288,z0,z2,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z5,z200]),(0,[z7,z59,z2,z28,z4,z5,z6]),(0,[z289,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z290,z5,z6]),(0,[z7,z291,z0,z2,z4,z5,z6])],[(0,[z292,z7,z0,z2,z4,z5,z6]),(0,[z13,z293,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z294,z4,z5,z6]),(0,[z7,z0,z104,z2,z105,z5,z6]),(0,[z7,z0,z2,z295,z4,z5,z6]),(0,[z7,z296,z0,z2,z4,z5,z6])],[(0,[z297,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z6,z298]),(0,[z7,z0,z2,z4,z5,z299,z6]),(0,[z7,z0,z300,z2,z4,z5,z6]),(0,[z301,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z302,z5,z6]),(0,[z303,z7,z0,z2,z4,z5,z6]),(0,[z7,z304,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z305,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z306,z6]),(0,[z307,z7,z0,z2,z4,z5,z6]),(0,[z130,z7,z0,z27,z4,z5,z6]),(0,[z94,z7,z0,z2,z4,z5,z6]),(0,[z7,z308,z0,z2,z4,z5,z6]),(0,[z7,z0,z309,z2,z4,z5,z6]),(0,[z7,z0,z2,z310,z4,z5,z6]),(0,[z7,z0,z14,z2,z105,z5,z6])]],
   [[(0,[z311,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z27,z59,z4,z5,z6])],[],[(0,[z7,z0,z27,z4,z5,z6,z298]),(0,[z7,z0,z62,z2,z4,z5,z6]),(0,[z312,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z313,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z314,z5,z6])],[(1,[z7,z203,z0,z2,z4,z5]),(0,[z7,z0,z2,z4,z5,z6,z315]),(0,[z7,z0,z2,z316,z4,z5,z6]),(0,[z7,z0,z317,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z318,z6]),(0,[z7,z0,z319,z2,z4,z5,z6]),(0,[z7,z0,z116,z4,z5,z98,z6]),(0,[z7,z0,z2,z4,z5,z6,z320])],[(0,[z7,z0,z30,z2,z4,z206,z5]),(0,[z7,z58,z0,z28,z4,z5,z6])],[(0,[z7,z0,z2,z28,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z142,z6])],[(0,[z7,z0,z321,z2,z4,z5,z6]),(0,[z322,z7,z0,z2,z4,z5,z6]),(1,[z293,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z243,z5,z122])]],
   [[(0,[z7,z0,z2,z4,z5,z323,z6]),(0,[z7,z0,z124,z2,z84,z4,z5])],[(0,[z324,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z325,z5,z6]),(0,[z7,z0,z27,z326,z4,z5,z6]),(0,[z7,z0,z14,z27,z4,z5,z6]),(0,[z7,z0,z2,z327,z4,z5,z6]),(0,[z7,z328,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z329,z6])],[(0,[z7,z0,z266,z2,z4,z5,z6]),(0,[z7,z0,z2,z330,z4,z5,z6]),(0,[z7,z0,z2,z331,z4,z5,z6]),(0,[z7,z0,z332,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z333,z5,z6]),(0,[z7,z0,z334,z2,z4,z5,z6])],[(0,[z117,z7,z0,z3,z4,z5,z6]),(0,[z7,z335,z0,z2,z4,z5,z6]),(0,[z7,z336,z0,z2,z4,z5,z6])],[(0,[z7,z0,z27,z4,z5,z337,z6])],[(0,[z130,z0,z2,z4,z5,z200,z6]),(0,[z338,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z339]),(1,[z7,z0,z14,z5,z38,z6])],[(0,[z7,z0,z2,z4,z5,z6,z340]),(0,[z7,z136,z0,z2,z19,z5,z6]),(0,[z341,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z342,z2,z4,z5,z6])],[(0,[z343,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z344,z4,z5,z6]),(0,[z338,z7,z0,z2,z4,z206,z6]),(0,[z7,z0,z345,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z3,z64,z4,z5,z6]),(0,[z7,z0,z2,z346,z4,z5,z6]),(0,[z7,z0,z2,z49,z4,z5,z50]),(0,[z7,z0,z347,z2,z4,z5,z6])],[(0,[z7,z0,z27,z4,z5,z6,z113]),(0,[z7,z0,z2,z61,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z6,z348]),(0,[z7,z0,z349,z2,z4,z5,z6]),(0,[z7,z0,z2,z350,z4,z5,z6]),(0,[z351,z7,z0,z2,z4,z5,z6]),(0,[z7,z47,z0,z2,z61,z5,z6]),(0,[z7,z47,z0,z2,z126,z5,z6]),(0,[z7,z0,z2,z352,z4,z5,z6])],[(0,[z7,z0,z2,z353,z4,z5,z6]),(0,[z7,z0,z2,z354,z4,z5,z6]),(0,[z7,z0,z2,z355,z5,z17,z6]),(0,[z7,z0,z2,z4,z5,z356,z6])],[(0,[z357,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z358]),(0,[z359,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z360,z4,z5,z6]),(1,[z7,z0,z174,z4,z5,z248]),(0,[z7,z0,z2,z361,z4,z5,z6])],[(0,[z362,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z363,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z50,z122]),(0,[z7,z0,z118,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z364,z5,z6]),(0,[z7,z271,z0,z3,z4,z5,z6]),(0,[z112,z7,z0,z2,z40,z5,z6]),(1,[z7,z0,z72,z4,z5,z6]),(0,[z7,z58,z0,z59,z4,z5,z6]),(0,[z162,z7,z0,z2,z49,z5,z6])],[(0,[z7,z0,z365,z2,z4,z5,z6])]],
   [[(0,[z75,z7,z0,z27,z4,z5,z6]),(0,[z7,z366,z0,z2,z4,z5,z6]),(0,[z7,z0,z367,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z368]),(0,[z7,z369,z0,z2,z4,z5,z6])],[(0,[z7,z16,z2,z4,z5,z17,z6]),(1,[z7,z0,z2,z4,z5,z69])],[(0,[z7,z0,z2,z370,z4,z5,z6]),(0,[z7,z0,z2,z4,z371,z5,z6]),(0,[z7,z0,z220,z27,z4,z5,z6]),(0,[z7,z0,z372,z2,z4,z5,z6]),(0,[z75,z7,z0,z2,z4,z206,z6]),(0,[z373,z7,z0,z2,z4,z5,z6])],[(0,[z271,z0,z1,z2,z4,z5,z6]),(0,[z7,z1,z2,z4,z5,z6,z108]),(0,[z7,z0,z2,z4,z5,z6,z374]),(0,[z7,z0,z2,z375,z4,z5,z6]),(1,[z7,z0,z2,z4,z195,z6]),(0,[z7,z376,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z377,z6]),(0,[z7,z378,z0,z2,z4,z5,z6])],[(0,[z112,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z379,z3,z4,z5,z6]),(0,[z7,z0,z380,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z108]),(0,[z7,z0,z14,z104,z4,z5,z6]),(0,[z7,z0,z381,z2,z4,z5,z6]),(0,[z7,z0,z2,z382,z19,z4,z5]),(0,[z383,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z384,z6])],[(0,[z7,z0,z0,z2,z4,z5,z6]),(0,[z7,z385,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z386,z5,z6]),(0,[z387,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z388,z6]),(0,[z162,z7,z0,z18,z2,z5,z6])],[(0,[z7,z0,z27,z4,z78,z5,z6]),(0,[z7,z0,z389,z2,z4,z5,z6]),(0,[z7,z0,z88,z2,z49,z4,z5])],[(0,[z7,z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z390,z5,z6]),(0,[z7,z0,z233,z27,z4,z5,z6]),(0,[z112,z132,z7,z0,z2,z4,z5]),(0,[z391,z7,z0,z2,z4,z5,z6])]],
   [[(0,[z112,z0,z2,z3,z4,z5,z6]),(0,[z90,z94,z7,z0,z2,z4,z5]),(0,[z7,z0,z2,z4,z392,z5,z6]),(0,[z7,z0,z2,z125,z4,z5,z6]),(1,[z7,z95,z2,z4,z5,z108]),(0,[z7,z393,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z394,z4,z5,z6])],[(0,[z395,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z97,z3,z4,z5,z6]),(0,[z7,z0,z396,z2,z4,z5,z6]),(0,[z94,z7,z0,z72,z4,z5,z6]),(0,[z94,z7,z0,z2,z4,z5,z122]),(0,[z397,z7,z0,z2,z4,z5,z6]),(0,[z398,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z116,z4,z5,z6]),(1,[z117,z7,z0,z118,z2,z4])],[(0,[z101,z0,z1,z2,z4,z5,z6]),(0,[z7,z0,z3,z4,z85,z5,z6]),(0,[z112,z7,z95,z0,z2,z4,z5]),(0,[z7,z0,z2,z4,z399,z5,z6]),(0,[z400,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z401,z5,z6])],[(0,[z7,z0,z2,z4,z402,z5,z6]),(0,[z7,z403,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z404,z4,z5,z6]),(1,[z7,z47,z2,z126,z5,z6]),(0,[z7,z0,z2,z405,z4,z5,z6])],[(0,[z7,z0,z379,z2,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z5,z6]),(0,[z112,z7,z57,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z406,z6])],[(0,[z407,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z286,z4,z5,z6]),(0,[z7,z16,z0,z2,z4,z78,z6])],[(0,[z7,z0,z2,z4,z5,z6,z408]),(0,[z7,z2,z61,z4,z126,z5,z6]),(0,[z409,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z355,z4,z5,z6]),(1,[z7,z0,z97,z4,z98,z6]),(0,[z7,z0,z174,z4,z5,z6,z248]),(0,[z7,z0,z2,z4,z5,z6,z410]),(0,[z411,z7,z0,z2,z4,z5,z6]),(0,[z7,z412,z0,z2,z4,z5,z6])],[(0,[z7,z0,z1,z2,z4,z5,z6]),(0,[z13,z7,z0,z27,z4,z5,z6]),(0,[z7,z47,z0,z2,z4,z5,z6]),(0,[z413,z7,z0,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z414,z5,z6]),(0,[z7,z0,z18,z2,z5,z6,z50])],[(0,[z7,z415,z0,z2,z4,z5,z6]),(0,[z7,z0,z97,z2,z4,z5,z6]),(0,[z7,z416,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z417])],[(1,[z7,z418,z0,z2,z4,z5])],[(0,[z7,z0,z27,z4,z5,z76,z6]),(0,[z7,z0,z2,z4,z5,z419,z6]),(0,[z420,z7,z0,z2,z4,z5,z6]),(0,[z112,z7,z0,z86,z4,z5,z6]),(0,[z94,z7,z0,z174,z2,z4,z5])],[(0,[z7,z421,z0,z2,z4,z5,z6]),(0,[z422,z7,z0,z2,z4,z5,z6]),(0,[z423,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z67,z3,z4,z5,z6]),(0,[z7,z0,z424,z2,z4,z5,z6]),(0,[z7,z166,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z98,z6])],[(0,[z7,z0,z37,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z425,z6]),(0,[z7,z136,z0,z2,z126,z5,z6])],[(0,[z134,z7,z271,z2,z4,z5,z6]),(0,[z7,z0,z3,z19,z4,z5,z6]),(0,[z7,z0,z88,z2,z5,z6,z50])]],
   [[(0,[z7,z0,z2,z4,z5,z426,z6]),(0,[z7,z427,z0,z2,z4,z5,z6]),(0,[z268,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z428,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z429]),(0,[z430,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z431,z4,z5,z6]),(0,[z7,z0,z432,z2,z4,z5,z6])],[(0,[z7,z0,z27,z433,z4,z5,z6]),(0,[z7,z0,z434,z2,z4,z5,z6]),(0,[z7,z0,z435,z4,z126,z5,z6]),(0,[z7,z436,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z437,z6]),(0,[z7,z0,z2,z4,z5,z438,z6]),(0,[z7,z0,z2,z11,z4,z5,z6])],[(0,[z7,z0,z439,z2,z4,z5,z6]),(1,[z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z440,z2,z4,z5,z6]),(0,[z7,z0,z441,z2,z4,z5,z6]),(0,[z7,z442,z0,z2,z4,z5,z6])],[(0,[z7,z16,z0,z27,z4,z5,z6]),(0,[z74,z36,z0,z2,z4,z5,z6]),(0,[z7,z136,z0,z18,z2,z5,z6]),(0,[z7,z0,z2,z382,z4,z5,z6])],[(0,[z7,z0,z3,z84,z4,z5,z6]),(0,[z7,z443,z0,z3,z4,z5,z6])],[(0,[z7,z0,z67,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z444,z5,z6]),(0,[z162,z7,z0,z88,z2,z5,z6])],[(1,[z7,z0,z445,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z446,z6]),(1,[z7,z0,z275,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z447]),(0,[z7,z0,z448,z2,z4,z5,z6]),(0,[z112,z94,z0,z2,z4,z5,z6]),(0,[z7,z0,z449,z2,z4,z5,z6]),(1,[z7,z0,z435,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z450,z6]),(0,[z7,z0,z2,z4,z5,z451,z6]),(0,[z7,z0,z2,z452,z4,z5,z6])],[(0,[z7,z0,z453,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z5,z454,z6]),(0,[z7,z0,z27,z2,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z200,z6]),(0,[z7,z0,z2,z4,z5,z455,z6]),(0,[z7,z0,z2,z4,z5,z108,z122]),(0,[z7,z0,z456,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z457,z5,z6]),(1,[z7,z0,z2,z218,z5,z6])],[(0,[z7,z0,z2,z4,z5,z458,z6]),(0,[z7,z459,z0,z2,z4,z5,z6])],[(0,[z460,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z461,z2,z4,z5,z6])],[(0,[z7,z136,z0,z3,z4,z5,z6]),(0,[z7,z462,z0,z2,z4,z5,z6]),(0,[z7,z0,z463,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z464,z5,z6]),(0,[z7,z95,z0,z2,z4,z5,z89]),(0,[z162,z7,z0,z2,z19,z5,z6]),(0,[z7,z0,z118,z2,z4,z243,z5])],[(1,[z7,z0,z465,z4,z5,z6]),(0,[z7,z443,z0,z2,z4,z5,z6]),(0,[z7,z0,z59,z3,z4,z5,z6]),(0,[z7,z466,z0,z2,z4,z5,z6]),(0,[z7,z0,z467,z2,z4,z5,z6]),(1,[z7,z0,z2,z19,z6,z298]),(0,[z7,z0,z2,z4,z243,z6,z122])],[(0,[z7,z468,z0,z2,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z229,z6]),(0,[z94,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z200,z6]),(0,[z7,z0,z2,z4,z5,z469,z6]),(0,[z132,z7,z0,z2,z4,z5,z6])],[(0,[z101,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z470,z6])],[(0,[z7,z0,z471,z3,z4,z5,z6]),(0,[z117,z7,z0,z2,z4,z76,z6]),(0,[z13,z7,z0,z105,z4,z5,z6]),(0,[z7,z0,z2,z472,z4,z5,z6]),(0,[z7,z0,z2,z4,z126,z5,z6]),(0,[z7,z0,z2,z473,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z5,z474,z6]),(0,[z7,z0,z3,z4,z5,z6,z248]),(0,[z475,z7,z0,z2,z4,z5,z6])],[(0,[z476,z7,z0,z2,z4,z5,z6]),(0,[z7,z47,z136,z2,z4,z5,z6]),(0,[z7,z0,z435,z2,z4,z5,z6]),(0,[z7,z477,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z17,z6])],[(0,[z101,z7,z0,z266,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z89,z6]),(0,[z460,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z206,z5,z6]),(0,[z7,z0,z2,z4,z5,z478,z6]),(0,[z479,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z480,z5,z6]),(0,[z7,z481,z0,z2,z4,z5,z6]),(0,[z482,z7,z0,z2,z4,z5,z6])],[(0,[z7,z7,z0,z3,z4,z5,z6])],[(0,[z483,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z250,z4,z5,z6]),(0,[z112,z0,z2,z4,z5,z6,z113]),(0,[z7,z0,z2,z4,z5,z484,z6]),(0,[z7,z0,z2,z485,z4,z5,z6]),(1,[z486,z0,z2,z4,z5,z6])],[(0,[z7,z0,z27,z4,z5,z6,z248])],[(0,[z101,z7,z0,z2,z4,z5,z6]),(0,[z7,z58,z0,z3,z4,z5,z6]),(0,[z7,z0,z3,z105,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z487]),(1,[z7,z0,z30,z2,z4,z5]),(0,[z7,z0,z488,z2,z4,z5,z6]),(1,[z7,z0,z2,z107,z5,z6])],[(0,[z132,z7,z1,z2,z4,z5,z6]),(1,[z134,z271,z2,z4,z5,z6]),(0,[z7,z0,z2,z3,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z89,z6])]],
   [[(1,[z7,z489,z2,z4,z5,z6]),(0,[z7,z0,z490,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z491,z5,z6]),(0,[z492,z7,z0,z2,z4,z5,z6])],[(0,[z493,z7,z0,z2,z4,z5,z6]),(1,[z7,z418,z0,z3,z4,z5]),(0,[z7,z47,z2,z4,z126,z5,z6]),(0,[z7,z0,z2,z4,z5,z494,z6]),(0,[z7,z0,z2,z4,z5,z32,z6]),(0,[z495,z7,z0,z2,z4,z5,z6])],[(0,[z112,z130,z0,z2,z4,z5,z6]),(0,[z112,z7,z0,z88,z2,z4,z5]),(0,[z7,z0,z2,z496,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z497]),(0,[z7,z0,z2,z4,z498,z5,z6]),(0,[z7,z0,z2,z49,z5,z6,z50]),(0,[z7,z0,z2,z499,z4,z5,z6])],[(0,[z7,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z500,z4,z5,z6]),(0,[z94,z0,z2,z4,z5,z200,z6]),(0,[z7,z501,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z502])],[(0,[z132,z7,z271,z2,z4,z5,z6]),(0,[z7,z0,z27,z503,z4,z5,z6]),(0,[z7,z504,z0,z2,z4,z5,z6]),(0,[z7,z0,z505,z2,z4,z5,z6])],[(0,[z90,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z506,z5,z6]),(0,[z7,z507,z0,z2,z4,z5,z6]),(0,[z7,z0,z147,z18,z2,z5,z6])],[(0,[z7,z0,z3,z4,z5,z38,z6]),(0,[z338,z7,z0,z81,z4,z5,z6]),(0,[z112,z7,z0,z2,z215,z5,z6]),(0,[z7,z58,z0,z2,z4,z5,z6]),(0,[z508,z7,z0,z2,z4,z5,z6]),(0,[z7,z277,z0,z2,z4,z5,z6])],[(0,[z338,z7,z0,z509,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z510])]],
   [[(0,[z101,z7,z1,z2,z4,z5,z6]),(0,[z0,z27,z2,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z511]),(0,[z112,z7,z0,z174,z2,z4,z5])],[(0,[z7,z0,z3,z4,z5,z6,z122]),(0,[z7,z0,z27,z24,z4,z5,z6]),(0,[z512,z7,z0,z2,z4,z5,z6]),(0,[z7,z58,z0,z14,z4,z5,z6]),(0,[z7,z0,z2,z4,z513,z5,z6]),(0,[z7,z0,z514,z2,z4,z5,z6]),(0,[z7,z0,z88,z2,z11,z4,z6]),(0,[z7,z0,z2,z4,z5,z515,z6])],[(0,[z7,z0,z88,z3,z4,z5,z6]),(0,[z7,z0,z2,z70,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z516]),(0,[z7,z0,z517,z2,z4,z5,z6]),(0,[z518,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z118,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z519,z6]),(0,[z520,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z521,z2,z4,z5,z6]),(1,[z7,z0,z2,z4,z5,z429]),(0,[z7,z0,z2,z522,z4,z5,z6]),(0,[z162,z7,z0,z88,z2,z4,z5])],[(0,[z7,z0,z2,z4,z4,z5,z6]),(0,[z7,z0,z2,z81,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z523,z6]),(0,[z7,z524,z0,z2,z4,z5,z6])],[(0,[z7,z0,z147,z3,z4,z5,z6]),(0,[z525,z7,z0,z2,z4,z5,z6]),(0,[z194,z7,z0,z27,z4,z5,z6]),(0,[z75,z7,z0,z62,z4,z5,z6]),(0,[z7,z0,z2,z4,z526,z5,z6]),(1,[z7,z0,z2,z4,z299,z6]),(0,[z7,z0,z2,z4,z527,z5,z6])],[(0,[z0,z2,z4,z206,z5,z76,z6]),(0,[z7,z0,z2,z4,z5,z528,z6]),(0,[z117,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z529,z6]),(0,[z7,z0,z3,z80,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z280]),(0,[z7,z0,z174,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z530,z6]),(0,[z94,z7,z0,z2,z4,z5,z50]),(0,[z7,z0,z2,z91,z4,z5,z6]),(1,[z7,z0,z2,z355,z5,z6]),(0,[z7,z0,z531,z2,z4,z5,z6])]],
   [[(0,[z7,z418,z0,z3,z4,z5,z6]),(1,[z130,z0,z27,z4,z5,z6]),(0,[z7,z0,z372,z27,z4,z5,z6]),(0,[z7,z0,z27,z64,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z532]),(0,[z7,z0,z2,z4,z5,z6,z533])],[(0,[z7,z0,z3,z49,z4,z5,z6]),(0,[z7,z418,z0,z2,z3,z4,z5]),(0,[z534,z7,z0,z2,z4,z5,z6]),(0,[z181,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z275,z2,z4,z5,z6]),(0,[z7,z0,z118,z2,z218,z5,z6])],[(0,[z158,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z86,z2,z4,z5,z6]),(0,[z7,z0,z251,z2,z4,z126,z6]),(0,[z486,z90,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z535,z4,z5,z6]),(0,[z536,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z537,z2,z4,z5,z6]),(0,[z7,z0,z2,z538,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z298]),(0,[z7,z0,z2,z539,z4,z5,z6])],[(0,[z540,z7,z0,z2,z4,z5,z6]),(0,[z7,z541,z0,z2,z4,z5,z6]),(0,[z13,z7,z0,z28,z4,z5,z6]),(0,[z7,z77,z0,z2,z4,z17,z6])],[(0,[z134,z7,z0,z27,z4,z5,z6]),(0,[z158,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z200,z6]),(0,[z7,z95,z0,z27,z4,z5,z6]),(0,[z7,z0,z27,z49,z4,z5,z6]),(0,[z542,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z543,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z544,z6]),(1,[z7,z0,z2,z4,z142,z6])],[(0,[z7,z0,z545,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z546,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z547])]],
   [[(0,[z7,z271,z2,z4,z5,z6,z108]),(0,[z7,z418,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z548,z5,z6]),(0,[z7,z0,z2,z4,z5,z549,z6]),(0,[z7,z0,z118,z2,z4,z5,z108]),(0,[z7,z0,z147,z2,z4,z6,z298])],[(0,[z7,z271,z0,z2,z4,z5,z6]),(1,[z7,z0,z305,z4,z5,z6]),(0,[z7,z0,z550,z2,z4,z5,z6]),(0,[z551,z7,z0,z2,z4,z5,z6]),(0,[z7,z552,z0,z2,z4,z5,z6]),(0,[z7,z0,z553,z2,z4,z5,z6])],[(0,[z134,z7,z0,z445,z4,z5,z6]),(0,[z158,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z554,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z555]),(0,[z7,z0,z2,z556,z4,z5,z6])],[(0,[z7,z0,z27,z4,z5,z6,z109]),(0,[z7,z0,z2,z326,z4,z5,z6]),(0,[z7,z0,z557,z2,z4,z5,z6]),(0,[z7,z0,z2,z19,z5,z6,z50]),(0,[z117,z7,z0,z2,z4,z243,z6])],[(0,[z558,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z1,z27,z4,z5,z6]),(0,[z7,z385,z0,z1,z2,z4,z5]),(0,[z7,z47,z0,z27,z4,z5,z6]),(0,[z7,z0,z160,z27,z4,z5,z6]),(0,[z36,z7,z0,z2,z84,z5,z6]),(0,[z7,z0,z2,z4,z559,z5,z6])],[(0,[z36,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z337,z6]),(0,[z90,z7,z0,z2,z4,z5,z248]),(1,[z7,z0,z2,z4,z243,z122])],[(0,[z7,z0,z97,z27,z4,z5,z6]),(0,[z162,z7,z0,z2,z84,z5,z6]),(0,[z560,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z561,z6]),(0,[z7,z0,z118,z2,z107,z5,z6])]],
   [[(0,[z162,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z84,z5,z6,z50]),(0,[z562,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z563,z2,z4,z5,z6]),(0,[z7,z0,z2,z564,z4,z5,z6]),(0,[z7,z0,z565,z2,z4,z5,z6])],[(0,[z566,z7,z0,z2,z4,z5,z6]),(0,[z74,z7,z0,z2,z84,z5,z6]),(1,[z36,z0,z2,z84,z5,z6]),(0,[z117,z7,z0,z2,z19,z4,z6]),(0,[z7,z0,z2,z567,z4,z5,z6])],[(0,[z7,z0,z2,z4,z568,z5,z6]),(0,[z74,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z27,z4,z85,z5,z6]),(0,[z7,z0,z2,z569,z4,z5,z6])],[(0,[z130,z0,z27,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z570]),(0,[z7,z0,z2,z4,z5,z6,z113]),(0,[z7,z95,z0,z2,z4,z5,z108]),(0,[z7,z0,z2,z4,z571,z5,z6]),(0,[z7,z0,z147,z2,z19,z5,z6])],[(0,[z572,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z573,z5,z6]),(0,[z7,z0,z2,z4,z574,z5,z6]),(0,[z7,z0,z118,z2,z4,z6,z122])],[(0,[z7,z77,z0,z3,z4,z5,z6]),(0,[z7,z575,z0,z2,z4,z5,z6]),(0,[z7,z0,z576,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z577]),(0,[z7,z0,z118,z2,z4,z5,z50])],[(0,[z578,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z424,z4,z5,z6]),(0,[z579,z7,z0,z2,z4,z5,z6]),(0,[z13,z7,z0,z59,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z108,z50]),(0,[z7,z0,z2,z4,z5,z580,z6]),(0,[z7,z0,z581,z2,z4,z5,z6])],[(0,[z7,z0,z92,z3,z4,z5,z6]),(0,[z7,z582,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z583,z5,z6]),(0,[z7,z584,z0,z2,z4,z5,z6]),(0,[z7,z0,z585,z2,z4,z5,z6]),(0,[z7,z586,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z587,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z5,z588,z6]),(0,[z589,z7,z0,z2,z4,z5,z6]),(0,[z7,z590,z0,z2,z4,z5,z6]),(0,[z162,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z67,z2,z3,z4,z5]),(0,[z7,z0,z489,z2,z4,z5,z6]),(0,[z7,z136,z0,z2,z61,z5,z6]),(0,[z7,z591,z0,z2,z4,z5,z6])],[(0,[z7,z0,z53,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z592]),(0,[z593,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z594,z6])],[(0,[z7,z0,z595,z2,z4,z5,z6]),(0,[z7,z0,z118,z2,z4,z5,z89]),(0,[z7,z0,z2,z4,z5,z596,z6]),(0,[z7,z0,z160,z116,z4,z5,z6])],[(0,[z597,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z150,z3,z4,z5,z6]),(1,[z7,z0,z509,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z242]),(1,[z7,z0,z352,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z598,z6]),(0,[z599,z7,z0,z2,z4,z5,z6]),(0,[z117,z7,z0,z147,z2,z4,z6])],[(0,[z7,z0,z2,z4,z5,z6,z600]),(0,[z74,z7,z0,z70,z4,z5,z6]),(0,[z338,z7,z0,z2,z4,z76,z6]),(0,[z601,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z160,z2,z4,z98,z6]),(0,[z7,z0,z2,z602,z4,z5,z6])],[(0,[z130,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z27,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z603,z5,z6]),(0,[z7,z0,z174,z2,z64,z4,z5])],[(0,[z7,z0,z27,z19,z4,z5,z6]),(0,[z7,z0,z251,z2,z4,z5,z6]),(0,[z7,z0,z91,z4,z5,z17,z6])]],
   [[(0,[z7,z0,z2,z4,z5,z6,z604]),(0,[z7,z0,z605,z2,z4,z5,z6]),(0,[z112,z7,z489,z2,z4,z5,z6]),(0,[z13,z7,z0,z116,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z606]),(0,[z7,z0,z2,z4,z78,z5,z6]),(0,[z7,z0,z607,z2,z4,z5,z6]),(0,[z608,z7,z0,z2,z4,z5,z6]),(0,[z117,z7,z0,z2,z4,z5,z122])],[(0,[z7,z462,z0,z27,z4,z5,z6]),(0,[z609,z7,z0,z2,z4,z5,z6]),(0,[z94,z7,z0,z424,z4,z5,z6]),(0,[z293,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z610,z6]),(0,[z7,z0,z160,z2,z116,z4,z6]),(0,[z7,z0,z2,z4,z5,z611,z6])],[(0,[z7,z0,z2,z4,z5,z6,z612]),(0,[z7,z136,z2,z61,z4,z5,z6]),(0,[z7,z0,z613,z2,z4,z5,z6])],[(0,[z132,z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z614,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z615]),(0,[z7,z0,z616,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z617,z6]),(0,[z7,z0,z2,z4,z618,z5,z6]),(0,[z7,z0,z27,z84,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z5,z50]),(0,[z7,z0,z2,z619,z4,z5,z6]),(0,[z620,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z621,z4,z5,z6])],[(0,[z7,z0,z445,z2,z4,z5,z6]),(0,[z7,z0,z3,z219,z4,z5,z6]),(0,[z7,z0,z104,z3,z4,z5,z6])],[(0,[z622,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z215,z5,z6]),(1,[z112,z0,z2,z4,z5,z113])],[(0,[z7,z0,z3,z116,z4,z5,z6]),(0,[z7,z0,z64,z4,z5,z6,z248])]],
   [[(0,[z7,z0,z14,z3,z4,z5,z6]),(0,[z75,z7,z0,z2,z4,z76,z6]),(0,[z94,z7,z0,z118,z2,z4,z5]),(0,[z7,z0,z2,z4,z5,z623,z6])],[(0,[z7,z0,z2,z4,z85,z5,z6]),(0,[z7,z0,z2,z4,z624,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z163]),(0,[z7,z0,z352,z4,z126,z5,z6]),(0,[z7,z0,z2,z4,z625,z5,z6])],[],[(0,[z338,z0,z2,z4,z206,z5,z6]),(0,[z7,z0,z626,z2,z4,z5,z6])],[(0,[z101,z7,z0,z27,z4,z5,z6]),(0,[z338,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z627,z5,z6]),(0,[z7,z0,z2,z628,z4,z5,z6]),(0,[z629,z7,z0,z2,z4,z5,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z2,z171,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z76,z6]),(0,[z7,z0,z509,z2,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z299,z6]),(0,[z7,z77,z16,z2,z4,z5,z6]),(0,[z7,z0,z104,z2,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z630,z6]),(0,[z7,z0,z3,z241,z4,z5,z6]),(0,[z7,z0,z3,z4,z243,z5,z6]),(0,[z631,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z632,z2,z4,z5,z6]),(0,[z7,z136,z0,z2,z4,z5,z6]),(0,[z7,z47,z0,z2,z4,z5,z429])],[(1,[z7,z385,z0,z2,z4,z5]),(0,[z7,z0,z3,z4,z5,z6,z50]),(1,[z7,z0,z286,z4,z5,z6]),(0,[z7,z0,z59,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z633,z6]),(0,[z7,z0,z634,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z635])]],
   [[(0,[z7,z0,z636,z2,z4,z5,z6]),(0,[z7,z77,z0,z2,z19,z4,z6]),(0,[z132,z7,z0,z2,z4,z5,z108]),(0,[z7,z0,z14,z2,z4,z5,z6])],[(0,[z7,z7,z0,z27,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z5,z122]),(0,[z7,z0,z2,z637,z4,z5,z6])],[(0,[z101,z134,z0,z2,z4,z5,z6]),(0,[z7,z0,z471,z2,z4,z5,z6]),(0,[z13,z7,z0,z97,z4,z5,z6]),(0,[z7,z0,z638,z2,z4,z5,z6])],[(0,[z7,z0,z27,z4,z243,z5,z6]),(0,[z7,z0,z2,z433,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z639,z6]),(0,[z7,z0,z640,z2,z4,z5,z6])],[(0,[z641,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z3,z253,z4,z5,z6]),(0,[z7,z58,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z642,z4,z5,z6]),(0,[z338,z7,z0,z2,z4,z5,z6])],[(0,[z134,z7,z0,z305,z4,z5,z6]),(0,[z7,z0,z643,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z644,z6])],[(0,[z101,z7,z0,z465,z4,z5,z6]),(0,[z7,z0,z18,z3,z4,z5,z6]),(0,[z7,z0,z27,z105,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z195,z6])],[(0,[z7,z203,z0,z2,z4,z5,z6]),(0,[z645,z7,z0,z2,z4,z5,z6]),(0,[z75,z7,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z646,z6]),(0,[z7,z647,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z648,z4,z5,z6]),(0,[z649,z7,z0,z2,z4,z5,z6])]],
   [[(0,[z650,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z651,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z652]),(0,[z653,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z654,z6])],[(0,[z7,z0,z2,z19,z4,z6,z298])],[(0,[z7,z0,z2,z2,z4,z5,z6]),(0,[z7,z0,z182,z2,z4,z5,z6]),(0,[z112,z90,z7,z0,z2,z4,z5]),(0,[z7,z655,z0,z2,z4,z5,z6]),(0,[z7,z2,z4,z5,z89,z6,z108]),(0,[z656,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z657,z6])],[(0,[z658,z7,z0,z2,z4,z5,z6]),(0,[z7,z77,z0,z147,z2,z4,z6]),(0,[z659,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z660,z4,z5,z6]),(0,[z117,z7,z0,z27,z4,z5,z6]),(0,[z661,z7,z0,z2,z4,z5,z6]),(0,[z662,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z663,z6]),(0,[z7,z0,z664,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z665])],[(0,[z7,z0,z2,z4,z5,z446,z6]),(0,[z7,z0,z27,z4,z5,z265,z6]),(0,[z666,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z667]),(1,[z7,z0,z2,z4,z5,z592]),(0,[z7,z0,z668,z2,z4,z5,z6]),(0,[z7,z0,z147,z18,z2,z4,z6])],[(0,[z7,z0,z2,z669,z4,z5,z6]),(1,[z0,z27,z3,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z38,z6]),(0,[z7,z16,z0,z2,z4,z5,z592]),(0,[z7,z0,z670,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z671,z6]),(0,[z7,z0,z18,z2,z4,z5,z6]),(0,[z7,z0,z2,z19,z5,z6,z298]),(0,[z7,z0,z672,z2,z4,z5,z6])],[(0,[z7,z0,z2,z465,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z673]),(0,[z75,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z2,z4,z5,z242]),(0,[z7,z0,z2,z4,z5,z200,z6]),(0,[z674,z7,z0,z2,z4,z5,z6])]],
   [[(0,[z101,z7,z271,z2,z4,z5,z6]),(0,[z7,z0,z2,z675,z4,z5,z6]),(0,[z676,z7,z0,z2,z4,z5,z6]),(0,[z90,z7,z0,z2,z4,z5,z6]),(1,[z7,z0,z2,z382,z4,z5])],[(0,[z7,z0,z2,z4,z677,z5,z6]),(1,[z112,z0,z3,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z6,z122]),(0,[z7,z0,z678,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z206,z6,z122]),(0,[z94,z7,z0,z2,z4,z5,z113]),(0,[z7,z0,z2,z4,z5,z679,z6]),(0,[z7,z0,z2,z4,z680,z5,z6])],[(0,[z7,z0,z2,z4,z681,z5,z6]),(0,[z7,z16,z0,z2,z4,z17,z6])],[(0,[z7,z0,z2,z4,z5,z682,z6]),(0,[z7,z683,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z684]),(0,[z7,z0,z2,z4,z5,z685,z6]),(0,[z132,z7,z0,z2,z4,z5,z89]),(0,[z686,z7,z0,z2,z4,z5,z6]),(0,[z90,z277,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z687,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z5,z6]),(0,[z7,z0,z2,z688,z4,z5,z6]),(1,[z162,z7,z0,z88,z2,z5])],[(0,[z130,z0,z1,z2,z4,z5,z6]),(0,[z130,z158,z0,z2,z4,z5,z6]),(0,[z162,z7,z0,z2,z85,z5,z6]),(0,[z7,z689,z0,z2,z4,z5,z6]),(0,[z7,z0,z54,z2,z5,z17,z6]),(0,[z7,z0,z2,z4,z5,z6,z690]),(0,[z7,z0,z2,z4,z5,z691,z6]),(0,[z7,z0,z88,z2,z4,z5,z6])],[(0,[z13,z7,z0,z3,z4,z5,z6]),(0,[z7,z57,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z692,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z693,z6]),(0,[z7,z0,z18,z2,z5,z6,z298])],[(0,[z7,z271,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z6,z248]),(0,[z7,z694,z0,z2,z4,z5,z6])]],
   [[(0,[z695,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z696,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z697,z6]),(0,[z7,z0,z147,z2,z4,z5,z6])],[(0,[z698,z7,z0,z2,z4,z5,z6]),(0,[z7,z699,z0,z2,z4,z5,z6]),(1,[z338,z0,z2,z4,z206,z6]),(0,[z7,z0,z2,z4,z5,z89,z6])],[(0,[z7,z0,z396,z27,z4,z5,z6]),(0,[z7,z0,z700,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z701,z5,z6]),(1,[z90,z7,z0,z64,z4,z5])],[(0,[z702,z7,z0,z2,z4,z5,z6])],[(0,[z7,z58,z0,z105,z4,z5,z6]),(0,[z7,z0,z2,z703,z4,z5,z6])],[(0,[z112,z7,z0,z27,z4,z5,z6]),(1,[z74,z0,z2,z85,z5,z6]),(0,[z112,z7,z0,z118,z2,z4,z5]),(0,[z704,z7,z0,z2,z4,z5,z6]),(0,[z486,z7,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z503,z4,z5,z6]),(0,[z36,z7,z0,z250,z4,z5,z6]),(0,[z13,z7,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z705,z5,z6])],[(0,[z7,z0,z3,z28,z4,z5,z6]),(0,[z338,z75,z0,z2,z4,z5,z6]),(0,[z90,z7,z0,z174,z4,z5,z6]),(0,[z7,z0,z2,z4,z706,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z0,z92,z4,z446,z6]),(0,[z7,z0,z707,z4,z5,z6]),(0,[z7,z0,z355,z91,z5,z6])],[(0,[z175,z0,z3,z4,z5,z6]),(0,[z486,z0,z27,z4,z5,z6]),(0,[z7,z0,z18,z2,z127,z6]),(0,[z7,z0,z708,z4,z5,z6]),(0,[z7,z0,z2,z567,z5,z50])],[(0,[z341,z271,z2,z4,z5,z6]),(0,[z0,z3,z4,z5,z617,z6]),(0,[z7,z0,z3,z709,z4,z5]),(0,[z7,z0,z14,z5,z337,z6]),(0,[z7,z0,z118,z2,z215,z5]),(0,[z7,z16,z33,z4,z17,z6]),(0,[z7,z0,z710,z4,z5,z6]),(0,[z7,z0,z2,z218,z5,z108]),(0,[z7,z0,z97,z4,z711,z6]),(0,[z7,z0,z147,z18,z2,z6])],[(0,[z7,z0,z27,z107,z5,z6]),(0,[z0,z2,z4,z712,z5,z6]),(0,[z7,z0,z2,z4,z526,z122])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z7,z0,z713,z2,z4,z6]),(0,[z134,z271,z27,z4,z5,z6]),(0,[z158,z0,z3,z4,z5,z6]),(0,[z413,z0,z2,z4,z76,z6]),(0,[z7,z0,z2,z4,z5,z9])],[(0,[z7,z489,z27,z4,z5,z6]),(0,[z7,z489,z118,z2,z4,z5]),(0,[z7,z0,z714,z2,z5,z6]),(0,[z7,z47,z2,z190,z5,z6])],[(0,[z7,z0,z715,z4,z5,z6]),(0,[z7,z385,z0,z2,z4,z5]),(0,[z7,z0,z2,z716,z4,z6]),(0,[z717,z0,z2,z4,z5,z6])],[(0,[z620,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z718]),(0,[z7,z0,z2,z4,z5,z719]),(0,[z7,z0,z720,z4,z5,z6]),(0,[z7,z0,z721,z4,z5,z6])]],
   [[(0,[z134,z271,z445,z4,z5,z6]),(0,[z117,z7,z0,z2,z382,z4])],[(0,[z7,z0,z2,z4,z5,z722]),(0,[z723,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z724,z6])],[(0,[z166,z0,z3,z4,z5,z6]),(0,[z112,z0,z3,z40,z5,z6]),(0,[z7,z0,z2,z709,z4,z5]),(0,[z7,z0,z27,z4,z5,z725]),(0,[z7,z0,z2,z4,z726,z6]),(0,[z90,z7,z0,z286,z4,z5]),(0,[z7,z0,z727,z4,z5,z6])],[(0,[z7,z728,z2,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z729]),(0,[z7,z0,z2,z730,z5,z6]),(0,[z7,z0,z174,z286,z4,z5]),(0,[z7,z0,z731,z4,z5,z6]),(1,[z7,z0,z732,z5,z6]),(0,[z7,z0,z733,z4,z5,z6])],[(0,[z7,z0,z2,z4,z734,z6]),(0,[z7,z0,z735,z4,z5,z6]),(0,[z7,z0,z736,z4,z5,z6]),(0,[z94,z0,z2,z4,z5,z533]),(0,[z7,z47,z2,z125,z126,z6]),(0,[z7,z0,z2,z4,z574,z122]),(0,[z7,z0,z737,z4,z5,z6])],[],[(0,[z7,z0,z67,z3,z4,z5]),(0,[z7,z0,z251,z27,z4,z6]),(0,[z112,z489,z2,z4,z5,z113]),(0,[z90,z7,z0,z72,z4,z5]),(0,[z7,z0,z2,z738,z5,z6]),(0,[z7,z0,z2,z473,z5,z50]),(0,[z7,z0,z2,z382,z5,z50]),(0,[z7,z0,z739,z4,z5,z6]),(0,[z7,z0,z740,z2,z4,z122])],[(0,[z7,z0,z741,z4,z5,z6]),(0,[z7,z0,z3,z215,z5,z6]),(0,[z7,z0,z2,z4,z742,z6]),(0,[z7,z0,z743,z4,z5,z6]),(0,[z7,z0,z744,z4,z5,z248])]],
   [[(0,[z7,z0,z745,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z429])],[(0,[z0,z3,z433,z4,z5,z6]),(0,[z94,z0,z3,z4,z5,z200]),(0,[z7,z0,z2,z4,z746,z6]),(0,[z7,z0,z30,z2,z4,z122]),(0,[z7,z0,z2,z747,z5,z6]),(0,[z7,z0,z2,z4,z290,z122])],[(0,[z7,z0,z2,z4,z5,z748]),(0,[z7,z507,z0,z118,z2,z4])],[(0,[z7,z0,z749,z4,z5,z6]),(0,[z413,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z750,z6]),(0,[z7,z0,z97,z4,z685,z6]),(0,[z7,z0,z2,z751,z5,z6])],[(0,[z7,z0,z2,z4,z5,z752]),(0,[z418,z0,z3,z4,z5,z200]),(0,[z7,z2,z4,z5,z753,z6]),(0,[z7,z0,z754,z4,z5,z6]),(0,[z7,z0,z27,z355,z5,z6]),(0,[z7,z0,z160,z4,z711,z6]),(0,[z117,z7,z0,z740,z2,z4])],[(0,[z460,z1,z3,z4,z5,z6]),(0,[z7,z0,z2,z234,z5,z50]),(0,[z166,z0,z14,z4,z5,z6]),(0,[z755,z0,z2,z4,z5,z6]),(0,[z7,z0,z756,z2,z4,z6]),(0,[z7,z16,z2,z4,z757,z6]),(0,[z7,z0,z2,z218,z5,z89]),(0,[z7,z0,z2,z4,z758,z6])],[(0,[z7,z0,z2,z4,z5,z759]),(0,[z7,z0,z54,z3,z5,z6]),(0,[z303,z0,z3,z4,z5,z6]),(0,[z45,z0,z3,z4,z5,z6]),(0,[z145,z0,z2,z85,z5,z6]),(0,[z760,z166,z0,z2,z4,z5]),(0,[z7,z0,z2,z4,z5,z761])],[(0,[z7,z0,z2,z4,z5,z762]),(0,[z7,z0,z2,z763,z5,z6]),(0,[z7,z0,z764,z4,z5,z6]),(0,[z7,z489,z286,z4,z5,z6]),(0,[z7,z57,z2,z215,z5,z6]),(0,[z7,z765,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z766,z4,z5,z6]),(0,[z112,z0,z3,z4,z5,z6]),(0,[z7,z767,z2,z4,z5,z6]),(0,[z7,z0,z768,z4,z5,z6]),(0,[z7,z0,z769,z4,z5,z6]),(0,[z7,z0,z2,z4,z770,z6]),(0,[z0,z2,z4,z5,z6,z771]),(0,[z7,z0,z2,z382,z19,z298])],[(0,[z7,z418,z0,z72,z4,z5]),(0,[z7,z0,z772,z4,z5,z6]),(0,[z94,z0,z2,z4,z5,z200]),(0,[z7,z59,z773,z4,z5,z6]),(0,[z774,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z775,z5,z6]),(0,[z7,z0,z776,z4,z5,z6]),(0,[z7,z0,z3,z40,z5,z6]),(0,[z0,z3,z4,z5,z6,z665]),(0,[z130,z0,z86,z4,z5,z6]),(0,[z7,z0,z2,z4,z777,z6]),(0,[z0,z2,z4,z5,z6,z778]),(0,[z7,z0,z2,z4,z779,z6])],[(0,[z7,z0,z3,z4,z5,z163]),(0,[z7,z0,z124,z3,z4,z5]),(0,[z7,z0,z780,z3,z5,z6]),(0,[z7,z0,z2,z4,z5,z781]),(0,[z338,z0,z27,z4,z206,z6]),(0,[z112,z0,z2,z4,z299,z113])],[(0,[z418,z0,z2,z4,z5,z200]),(0,[z13,z7,z773,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z782])],[(0,[z460,z1,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z783]),(0,[z0,z3,z4,z5,z200,z6]),(0,[z7,z784,z2,z4,z5,z6]),(0,[z166,z0,z59,z4,z5,z6]),(0,[z7,z647,z0,z88,z2,z5])],[(0,[z7,z0,z2,z4,z785,z6]),(0,[z7,z0,z86,z215,z5,z6])],[(0,[z7,z0,z786,z2,z4,z6]),(0,[z7,z787,z0,z2,z4,z5]),(0,[z7,z2,z4,z5,z788,z6]),(0,[z74,z0,z27,z85,z5,z6]),(0,[z7,z0,z732,z5,z38,z6])]],
   [[(0,[z7,z58,z496,z4,z5,z6]),(0,[z7,z0,z2,z382,z4,z122])],[(0,[z7,z0,z2,z4,z789,z5]),(0,[z7,z0,z2,z790,z5,z6]),(0,[z132,z7,z3,z4,z5,z89]),(0,[z791,z0,z2,z4,z5,z6])],[(0,[z112,z0,z88,z3,z4,z5]),(0,[z231,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z40,z5,z6]),(0,[z7,z57,z2,z40,z5,z6]),(0,[z7,z0,z792,z4,z5,z6]),(0,[z7,z0,z2,z732,z5,z6])],[(0,[z7,z0,z713,z3,z4,z6]),(0,[z508,z0,z3,z4,z5,z6]),(0,[z460,z7,z28,z4,z5,z6]),(0,[z74,z0,z275,z85,z5,z6]),(0,[z7,z0,z2,z4,z5,z163])],[(0,[z7,z0,z793,z2,z4,z5]),(0,[z117,z7,z0,z118,z27,z4]),(0,[z7,z0,z97,z4,z265,z6]),(0,[z7,z0,z286,z4,z299,z6]),(0,[z112,z0,z2,z4,z195,z113]),(0,[z7,z2,z773,z4,z5,z6]),(0,[z7,z2,z4,z757,z5,z6]),(0,[z7,z0,z794,z2,z4,z5])],[(0,[z7,z385,z0,z3,z4,z5]),(0,[z7,z0,z3,z125,z4,z6]),(0,[z7,z0,z250,z4,z5,z6]),(0,[z117,z7,z0,z30,z2,z4]),(0,[z7,z0,z14,z732,z5,z6])],[(0,[z7,z0,z67,z4,z5,z248]),(0,[z36,z0,z27,z84,z5,z6])],[(0,[z7,z0,z795,z4,z5,z6]),(0,[z75,z0,z171,z4,z76,z6]),(0,[z0,z2,z4,z5,z6,z796]),(0,[z112,z0,z595,z2,z4,z5]),(0,[z7,z0,z2,z797,z4,z5]),(0,[z7,z0,z4,z732,z5,z6]),(0,[z117,z7,z0,z118,z2,z218])]],
   [[(0,[z7,z0,z3,z4,z5,z6]),(0,[z7,z203,z0,z27,z4,z5]),(0,[z7,z0,z2,z4,z798,z5]),(0,[z7,z0,z2,z4,z142,z108]),(0,[z7,z197,z2,z4,z5,z108])],[(0,[z134,z0,z3,z4,z5,z6]),(0,[z203,z0,z3,z4,z5,z6]),(0,[z698,z0,z3,z4,z5,z6]),(0,[z7,z0,z799,z2,z4,z6]),(0,[z132,z7,z2,z4,z5,z89]),(0,[z7,z0,z2,z11,z6,z50])],[(0,[z132,z7,z203,z2,z4,z5]),(0,[z7,z800,z0,z2,z4,z5]),(0,[z7,z0,z2,z19,z69,z298]),(1,[z7,z0,z801,z2,z5])],[(0,[z277,z0,z3,z4,z5,z6]),(0,[z400,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z32])],[(0,[z7,z0,z266,z4,z5,z6]),(0,[z7,z0,z37,z4,z5,z6]),(0,[z7,z418,z0,z64,z4,z5]),(0,[z800,z166,z0,z2,z4,z5]),(0,[z7,z0,z2,z802,z5,z6]),(0,[z7,z0,z2,z803,z4,z5])],[(0,[z7,z0,z804,z4,z5,z6]),(0,[z158,z0,z67,z3,z4,z5]),(0,[z7,z0,z286,z4,z195,z6]),(0,[z7,z0,z2,z4,z5,z805]),(0,[z7,z0,z2,z4,z701,z122])],[(0,[z387,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z806]),(0,[z13,z7,z342,z4,z5,z6]),(0,[z7,z0,z2,z49,z5,z50])],[(0,[z7,z0,z807,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z808]),(0,[z7,z0,z2,z809,z5,z6]),(0,[z7,z0,z810,z4,z5,z6]),(0,[z811,z0,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z5,z6]),(0,[z7,z57,z2,z4,z5,z6]),(0,[z112,z277,z0,z2,z4,z5]),(0,[z0,z2,z4,z5,z200,z796])],[(0,[z0,z3,z24,z4,z5,z6]),(0,[z7,z812,z2,z4,z5,z6])],[(0,[z101,z385,z1,z2,z4,z5]),(0,[z7,z462,z59,z4,z5,z6])],[(0,[z101,z1,z3,z4,z5,z6]),(0,[z134,z1,z3,z4,z5,z6]),(0,[z134,z271,z305,z4,z5,z6]),(0,[z277,z0,z2,z4,z5,z6]),(0,[z7,z0,z70,z4,z5,z6])],[(0,[z7,z0,z2,z813,z5,z6]),(0,[z7,z443,z150,z4,z5,z6]),(0,[z7,z0,z54,z91,z5,z6])],[(0,[z90,z277,z0,z64,z4,z5])],[(0,[z0,z814,z3,z4,z5,z6]),(0,[z7,z0,z124,z2,z5,z50]),(0,[z7,z77,z246,z2,z4,z6]),(1,[z7,z0,z744,z4,z5]),(0,[z7,z0,z815,z4,z5,z6])],[(0,[z101,z1,z266,z4,z5,z6]),(0,[z0,z86,z3,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z816,z5,z6]),(0,[z0,z189,z27,z4,z5,z6]),(0,[z7,z0,z2,z817,z5,z6]),(0,[z7,z0,z2,z818,z5,z6]),(0,[z7,z0,z91,z4,z5,z6]),(0,[z7,z0,z819,z4,z5,z6]),(0,[z7,z0,z118,z2,z11,z4])],[(0,[z132,z7,z2,z4,z5,z306])],[(0,[z112,z0,z3,z4,z5,z122]),(0,[z7,z0,z255,z116,z4,z6]),(0,[z7,z820,z2,z4,z5,z6])],[(0,[z101,z1,z2,z4,z5,z6]),(0,[z293,z0,z3,z4,z5,z6]),(0,[z112,z0,z27,z4,z5,z113]),(0,[z7,z0,z2,z4,z5,z821]),(0,[z7,z0,z2,z822,z5,z6])],[(0,[z7,z0,z823,z4,z5,z6]),(0,[z7,z2,z4,z5,z782,z6])],[(0,[z7,z0,z2,z4,z5,z824]),(0,[z112,z95,z0,z3,z4,z5]),(0,[z338,z0,z30,z2,z4,z206]),(0,[z7,z0,z2,z4,z5,z825])],[(0,[z7,z0,z2,z826,z4,z5]),(0,[z7,z0,z827,z2,z5,z6]),(0,[z7,z0,z786,z3,z4,z6]),(0,[z7,z0,z3,z828,z4,z5]),(0,[z0,z550,z3,z4,z5,z6]),(0,[z7,z787,z0,z3,z4,z5]),(0,[z7,z0,z2,z829,z4,z6])],[(0,[z7,z0,z830,z4,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z5,z831]),(0,[z7,z0,z2,z4,z832,z5]),(0,[z132,z7,z489,z2,z4,z5]),(0,[z7,z0,z833,z4,z5,z6]),(0,[z7,z0,z33,z54,z5,z6]),(0,[z7,z0,z834,z2,z5,z6])],[(0,[z132,z7,z191,z2,z4,z5]),(0,[z7,z0,z2,z835,z4,z6]),(0,[z7,z0,z836,z4,z5,z6]),(0,[z7,z0,z744,z4,z5,z6])],[(0,[z7,z0,z27,z4,z5,z9]),(0,[z837,z0,z2,z4,z5,z6]),(0,[z7,z0,z838,z4,z5,z6])],[(0,[z7,z0,z839,z2,z5,z6]),(0,[z7,z840,z2,z4,z5,z6]),(0,[z7,z95,z489,z2,z4,z5]),(0,[z112,z7,z0,z2,z218,z5]),(0,[z841,z0,z2,z4,z5,z6])],[(0,[z7,z0,z182,z5,z337,z6]),(0,[z560,z0,z27,z4,z5,z6]),(0,[z7,z47,z2,z126,z5,z429]),(0,[z7,z0,z842,z4,z5,z6]),(1,[z7,z0,z2,z843,z6])],[(0,[z7,z0,z844,z4,z5,z6]),(0,[z7,z0,z251,z352,z4,z6])],[(0,[z7,z0,z2,z828,z4,z5])],[(0,[z117,z7,z0,z118,z3,z4]),(0,[z7,z0,z27,z4,z5,z722]),(0,[z7,z0,z2,z845,z5,z6]),(0,[z7,z47,z251,z2,z126,z6])]],
   [[(0,[z7,z489,z86,z4,z5,z6]),(0,[z7,z16,z2,z355,z17,z6]),(0,[z7,z0,z2,z4,z757,z6]),(0,[z7,z0,z118,z740,z2,z4])],[(0,[z112,z0,z814,z4,z5,z6]),(0,[z7,z0,z2,z846,z5,z6]),(0,[z277,z0,z233,z4,z5,z6]),(0,[z7,z0,z2,z11,z4,z122])],[(0,[z101,z847,z2,z4,z5,z6]),(0,[z90,z7,z0,z67,z4,z5]),(0,[z7,z0,z848,z4,z5,z6]),(0,[z849,z0,z2,z4,z5,z6]),(1,[z7,z0,z4,z711,z6]),(0,[z7,z0,z88,z801,z2,z5])],[(0,[z7,z850,z2,z4,z5,z6])],[(0,[z7,z0,z851,z4,z5,z6]),(0,[z7,z0,z88,z2,z4,z299]),(0,[z7,z0,z2,z852,z5,z6]),(0,[z7,z0,z853,z4,z5,z6]),(0,[z7,z0,z18,z2,z843,z6])],[(0,[z7,z0,z2,z4,z854,z6]),(0,[z7,z0,z3,z4,z5,z69]),(0,[z7,z0,z855,z4,z5,z6]),(0,[z7,z0,z33,z4,z5,z6]),(0,[z7,z0,z2,z744,z4,z5])],[(0,[z7,z0,z856,z4,z5,z6]),(0,[z0,z489,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z857]),(0,[z7,z57,z2,z4,z299,z6]),(0,[z7,z0,z858,z4,z5,z6]),(0,[z7,z0,z859,z4,z5,z6])],[(0,[z847,z1,z2,z4,z5,z6]),(0,[z0,z53,z3,z4,z5,z6]),(0,[z7,z418,z0,z27,z4,z5]),(0,[z7,z0,z3,z4,z195,z6]),(0,[z7,z0,z860,z4,z5,z6])]],
   [[(0,[z7,z0,z861,z4,z5,z6]),(0,[z0,z595,z3,z4,z5,z6]),(0,[z7,z0,z862,z2,z4,z5]),(0,[z760,z7,z0,z2,z4,z5]),(0,[z7,z0,z174,z4,z5,z248]),(0,[z7,z0,z863,z4,z5,z6])],[(0,[z7,z0,z864,z4,z5,z6]),(0,[z7,z0,z865,z4,z5,z6]),(0,[z7,z0,z866,z4,z5,z6]),(0,[z7,z0,z867,z4,z5,z6])],[(0,[z134,z0,z67,z3,z4,z5]),(0,[z7,z0,z27,z4,z5,z592]),(0,[z7,z0,z2,z868,z5,z6]),(0,[z94,z277,z0,z2,z4,z5]),(0,[z869,z0,z2,z4,z5,z6]),(0,[z7,z0,z870,z4,z5,z6]),(0,[z7,z0,z871,z4,z5,z6])],[(0,[z0,z27,z872,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z873]),(0,[z13,z7,z668,z4,z5,z6]),(0,[z277,z0,z64,z4,z5,z6])],[(0,[z0,z1,z465,z4,z5,z6]),(0,[z7,z0,z874,z2,z5,z6]),(0,[z7,z95,z3,z4,z5,z108]),(0,[z7,z0,z27,z4,z5,z242]),(0,[z7,z0,z2,z875,z5,z6]),(0,[z13,z7,z28,z4,z5,z6]),(0,[z7,z136,z0,z2,z125,z6]),(0,[z7,z0,z2,z876,z4,z6])],[(0,[z166,z0,z2,z4,z5,z6]),(0,[z418,z277,z0,z2,z4,z5]),(0,[z7,z0,z27,z382,z4,z5]),(0,[z7,z0,z877,z4,z5,z6]),(0,[z7,z0,z86,z4,z299,z6]),(1,[z7,z773,z4,z5,z6]),(0,[z7,z0,z878,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z69]),(0,[z7,z0,z879,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z729]),(0,[z7,z0,z124,z2,z40,z5]),(0,[z7,z0,z2,z4,z880,z6])],[(0,[z7,z0,z881,z4,z5,z6]),(0,[z7,z57,z2,z4,z195,z6])]],
   [[(0,[z1,z150,z3,z4,z5,z6])],[(0,[z7,z0,z814,z4,z5,z6]),(0,[z7,z0,z882,z4,z5,z6]),(0,[z7,z0,z2,z382,z107,z5])],[(0,[z650,z0,z3,z4,z5,z6]),(0,[z0,z445,z3,z4,z5,z6]),(0,[z7,z0,z2,z215,z5,z6]),(0,[z7,z0,z2,z883,z4,z5]),(0,[z7,z884,z0,z2,z4,z5]),(0,[z7,z0,z2,z843,z6,z298])],[(0,[z7,z0,z2,z885,z5,z6]),(0,[z7,z0,z886,z4,z5,z6]),(0,[z7,z77,z0,z2,z355,z6])],[(0,[z7,z95,z2,z4,z5,z108]),(0,[z7,z0,z887,z4,z5,z6])],[(0,[z7,z0,z255,z253,z4,z6]),(0,[z0,z2,z4,z875,z5,z6]),(0,[z7,z0,z124,z2,z829,z4]),(0,[z112,z0,z347,z2,z4,z5]),(0,[z7,z2,z4,z5,z89,z782]),(0,[z117,z7,z0,z118,z2,z4])],[(0,[z0,z847,z2,z4,z5,z6]),(0,[z7,z0,z888,z4,z5,z6]),(1,[z0,z2,z875,z5,z6]),(0,[z23,z0,z2,z84,z5,z6]),(0,[z7,z0,z86,z4,z195,z6])],[(0,[z271,z847,z2,z4,z5,z6]),(0,[z112,z132,z0,z3,z4,z5]),(0,[z23,z0,z3,z4,z5,z6]),(0,[z166,z0,z53,z4,z5,z6]),(0,[z7,z0,z889,z4,z5,z6]),(0,[z7,z0,z4,z711,z98,z6])]],
   [[(0,[z7,z2,z4,z78,z757,z6])],[(0,[z7,z0,z27,z4,z5,z163]),(0,[z7,z0,z2,z4,z711,z6])],[(0,[z7,z0,z839,z3,z5,z6]),(0,[z7,z0,z890,z4,z5,z6]),(0,[z7,z0,z97,z4,z98,z6])],[(0,[z409,z0,z3,z4,z5,z6])],[],[(0,[z130,z203,z0,z2,z4,z5]),(0,[z7,z0,z27,z11,z4,z6]),(0,[z94,z7,z0,z2,z218,z5]),(0,[z7,z0,z116,z4,z478,z6]),(0,[z7,z58,z648,z4,z5,z6]),(0,[z7,z47,z352,z126,z5,z6]),(0,[z7,z0,z435,z251,z4,z6])],[(0,[z7,z0,z872,z4,z5,z6]),(0,[z7,z0,z171,z4,z5,z6]),(0,[z7,z16,z27,z4,z17,z6])],[(0,[z7,z0,z891,z4,z5,z6]),(0,[z7,z0,z3,z892,z4,z5]),(0,[z90,z7,z0,z24,z4,z5]),(0,[z7,z489,z88,z2,z4,z5]),(0,[z7,z0,z2,z893,z5,z6])]],
   [[(0,[z7,z0,z251,z2,z4,z6])],[(0,[z385,z0,z1,z3,z4,z5]),(0,[z7,z0,z27,z4,z5,z32])],[(0,[z7,z0,z894,z4,z5,z6]),(0,[z7,z895,z0,z2,z4,z5])],[(0,[z112,z0,z174,z3,z4,z5]),(0,[z7,z0,z30,z27,z4,z5])],[(0,[z112,z489,z3,z4,z5,z6]),(0,[z7,z0,z3,z218,z5,z6]),(0,[z7,z0,z27,z49,z5,z50])],[(0,[z203,z0,z2,z3,z4,z5]),(0,[z359,z0,z27,z4,z5,z6]),(0,[z112,z0,z2,z222,z4,z5]),(0,[z7,z0,z896,z4,z5,z6]),(0,[z7,z0,z64,z744,z4,z5])],[(0,[z7,z57,z27,z4,z5,z6]),(0,[z7,z0,z174,z4,z5,z109]),(0,[z7,z0,z897,z4,z5,z6])],[(0,[z7,z0,z2,z892,z4,z5]),(0,[z7,z0,z898,z4,z5,z6]),(0,[z7,z0,z435,z125,z4,z6]),(0,[z899,z7,z0,z4,z5,z6]),(0,[z7,z0,z900,z4,z5,z6])]],
   [[(0,[z112,z0,z3,z4,z5,z50]),(0,[z7,z0,z3,z19,z6,z298]),(0,[z7,z0,z2,z125,z4,z6])],[(0,[z7,z0,z2,z843,z19,z6])],[(0,[z7,z0,z275,z4,z5,z6]),(0,[z7,z901,z3,z4,z5,z6]),(0,[z75,z0,z27,z4,z76,z6]),(0,[z7,z77,z27,z4,z78,z6]),(0,[z7,z0,z902,z4,z5,z6]),(0,[z7,z0,z435,z4,z5,z6]),(0,[z7,z0,z147,z2,z527,z6]),(0,[z7,z0,z2,z431,z5,z50])],[(0,[z0,z872,z3,z4,z5,z6]),(0,[z7,z0,z874,z3,z5,z6]),(0,[z7,z0,z903,z4,z5,z6])],[(0,[z7,z0,z904,z4,z5,z6]),(0,[z132,z1,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z905,z6]),(0,[z418,z277,z0,z3,z4,z5]),(0,[z75,z0,z2,z4,z712,z6]),(0,[z7,z0,z2,z19,z50,z122]),(0,[z7,z2,z4,z5,z906,z6])],[(0,[z7,z0,z372,z326,z4,z6]),(0,[z7,z0,z233,z4,z5,z109]),(0,[z7,z0,z2,z4,z5,z907]),(0,[z7,z0,z147,z2,z843,z6]),(0,[z162,z7,z0,z801,z2,z5])],[(0,[z7,z0,z2,z4,z5,z908]),(0,[z112,z90,z0,z3,z4,z5]),(0,[z7,z489,z2,z40,z5,z6]),(0,[z7,z0,z909,z2,z4,z6]),(0,[z7,z47,z2,z126,z5,z9])],[(0,[z7,z0,z2,z19,z625,z6])]],
   [[(0,[z7,z0,z465,z4,z5,z6]),(0,[z486,z0,z3,z4,z5,z6]),(0,[z7,z0,z105,z732,z5,z6]),(0,[z7,z0,z160,z116,z4,z6])],[(0,[z101,z1,z27,z4,z5,z6]),(0,[z112,z0,z3,z4,z299,z6]),(0,[z7,z0,z3,z4,z5,z910])],[(0,[z7,z0,z3,z107,z5,z6]),(0,[z7,z0,z2,z4,z5,z808]),(0,[z7,z0,z2,z40,z5,z50]),(0,[z7,z0,z42,z18,z2,z6])],[(0,[z0,z3,z4,z5,z454,z6]),(0,[z134,z271,z3,z4,z5,z6]),(0,[z0,z872,z2,z4,z5,z6]),(0,[z0,z233,z3,z4,z5,z6]),(0,[z7,z0,z911,z4,z5,z6]),(0,[z7,z0,z912,z4,z5,z6]),(0,[z162,z7,z0,z2,z11,z6])],[(0,[z7,z489,z3,z4,z5,z6]),(0,[z694,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z215,z5,z122]),(0,[z913,z0,z2,z4,z5,z6])],[(0,[z7,z3,z4,z5,z788,z6]),(0,[z7,z418,z0,z219,z4,z5]),(0,[z486,z90,z0,z64,z4,z5])],[(0,[z7,z0,z471,z5,z229,z6]),(0,[z7,z0,z27,z4,z5,z831]),(0,[z94,z0,z72,z4,z5,z200]),(0,[z7,z0,z914,z4,z5,z6])],[(0,[z7,z0,z18,z2,z5,z429]),(0,[z7,z0,z915,z4,z5,z6])]],
   [[(0,[z7,z0,z916,z4,z5,z6]),(0,[z676,z0,z27,z4,z5,z6]),(0,[z338,z0,z2,z4,z206,z242]),(0,[z7,z2,z4,z846,z5,z6]),(0,[z7,z0,z917,z4,z5,z6]),(0,[z7,z0,z2,z918,z5,z6]),(0,[z7,z0,z2,z919,z4,z6])],[(0,[z658,z0,z27,z4,z5,z6]),(0,[z7,z0,z2,z215,z195,z6])],[(0,[z7,z203,z0,z2,z4,z5]),(0,[z112,z0,z3,z4,z195,z6]),(0,[z0,z381,z27,z4,z5,z6]),(0,[z7,z0,z2,z107,z5,z6])],[(0,[z134,z271,z2,z4,z5,z6]),(0,[z101,z1,z465,z4,z5,z6]),(0,[z7,z0,z2,z40,z299,z6]),(0,[z7,z0,z920,z4,z5,z6])],[(0,[z7,z489,z2,z4,z5,z6]),(0,[z7,z0,z921,z4,z5,z6])],[(0,[z7,z922,z0,z2,z4,z5]),(0,[z158,z0,z872,z4,z5,z6]),(0,[z8,z0,z3,z4,z5,z6]),(0,[z165,z0,z3,z4,z5,z6]),(0,[z112,z0,z72,z4,z5,z6]),(0,[z0,z2,z4,z5,z796,z113]),(0,[z7,z0,z923,z4,z5,z6]),(0,[z277,z0,z174,z4,z5,z6]),(0,[z7,z0,z2,z19,z6,z410])],[(0,[z293,z0,z2,z4,z5,z6]),(1,[z489,z3,z4,z5,z6]),(0,[z7,z16,z2,z4,z17,z592])],[(0,[z7,z0,z3,z4,z5,z429]),(0,[z7,z0,z251,z3,z4,z6]),(0,[z486,z0,z86,z4,z5,z6]),(0,[z7,z2,z4,z5,z782,z108]),(0,[z7,z0,z924,z2,z4,z5])]],
   [[(0,[z7,z0,z925,z2,z4,z5])],[(0,[z7,z0,z3,z4,z299,z6]),(0,[z0,z3,z4,z5,z6,z315]),(0,[z0,z3,z316,z4,z5,z6]),(0,[z7,z0,z926,z4,z5,z6]),(0,[z7,z0,z147,z249,z2,z6])],[(0,[z7,z0,z2,z927,z5,z6])],[(0,[z7,z0,z3,z355,z5,z6]),(0,[z7,z0,z928,z4,z5,z6])],[(0,[z7,z847,z2,z4,z5,z6]),(0,[z130,z0,z872,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z857]),(0,[z7,z0,z929,z4,z5,z6]),(0,[z7,z0,z2,z40,z195,z6]),(0,[z7,z0,z14,z5,z38,z6]),(0,[z7,z0,z930,z4,z5,z6]),(0,[z7,z0,z931,z4,z5,z6])],[(0,[z134,z847,z2,z4,z5,z6]),(0,[z7,z932,z2,z4,z5,z6]),(0,[z7,z0,z2,z619,z5,z50]),(0,[z7,z0,z2,z4,z5,z933]),(0,[z7,z0,z801,z2,z49,z5])],[(0,[z0,z3,z4,z5,z323,z6]),(0,[z7,z0,z934,z4,z5,z6]),(0,[z60,z0,z3,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z502])],[(0,[z7,z0,z471,z5,z38,z6]),(0,[z935,z0,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z936,z4,z5,z6]),(0,[z7,z0,z937,z4,z5,z6]),(0,[z7,z0,z938,z4,z5,z6]),(0,[z112,z0,z286,z4,z5,z113])],[(0,[z7,z0,z2,z4,z299,z6]),(0,[z7,z0,z939,z4,z5,z6]),(0,[z112,z0,z2,z4,z5,z796]),(0,[z7,z0,z2,z4,z5,z940]),(0,[z7,z0,z801,z2,z5,z6])],[(0,[z7,z0,z3,z4,z142,z6]),(0,[z7,z0,z941,z4,z5,z6]),(0,[z942,z0,z2,z4,z5,z6]),(0,[z7,z943,z0,z2,z4,z5])],[(0,[z7,z0,z944,z4,z5,z6]),(0,[z285,z0,z3,z4,z5,z6]),(0,[z166,z0,z27,z4,z5,z6]),(0,[z7,z0,z27,z4,z5,z69]),(0,[z7,z0,z945,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z946]),(0,[z0,z2,z4,z206,z712,z6]),(0,[z7,z0,z2,z355,z5,z6]),(0,[z7,z0,z947,z4,z5,z6])],[(0,[z7,z0,z2,z948,z5,z6]),(0,[z130,z0,z27,z4,z5,z6]),(0,[z0,z67,z27,z3,z4,z5]),(0,[z7,z0,z379,z241,z5,z6]),(0,[z112,z0,z531,z2,z4,z5])],[(0,[z7,z0,z72,z4,z5,z6]),(0,[z283,z0,z27,z4,z5,z6]),(0,[z949,z0,z2,z4,z5,z6])],[(1,[z847,z2,z4,z5,z6]),(0,[z7,z0,z2,z950,z4,z6]),(0,[z13,z7,z433,z4,z5,z6]),(0,[z7,z0,z2,z951,z5,z6]),(0,[z7,z952,z0,z2,z4,z5])],[(0,[z7,z203,z489,z2,z4,z5]),(0,[z307,z0,z3,z4,z5,z6]),(0,[z7,z16,z0,z2,z355,z6])]],
   [[(0,[z130,z0,z445,z4,z5,z6]),(0,[z551,z0,z3,z4,z5,z6]),(0,[z7,z418,z0,z67,z4,z5]),(0,[z495,z0,z3,z4,z5,z6]),(0,[z7,z0,z92,z4,z98,z6]),(0,[z7,z0,z27,z215,z5,z6]),(0,[z36,z0,z2,z84,z5,z163]),(0,[z162,z7,z0,z2,z382,z5]),(0,[z7,z0,z88,z2,z107,z5])],[(0,[z270,z0,z3,z4,z5,z6]),(0,[z112,z418,z0,z2,z4,z5]),(0,[z7,z0,z953,z4,z5,z6])],[(0,[z7,z47,z3,z126,z5,z6]),(0,[z7,z0,z3,z4,z243,z122]),(0,[z94,z0,z27,z4,z5,z200]),(0,[z7,z0,z954,z4,z5,z6]),(0,[z7,z95,z27,z4,z5,z108]),(0,[z36,z0,z250,z84,z5,z6]),(0,[z7,z0,z2,z4,z195,z6]),(0,[z7,z0,z2,z4,z5,z955]),(0,[z7,z0,z956,z4,z5,z6]),(0,[z7,z0,z2,z843,z5,z6]),(0,[z7,z0,z2,z4,z142,z6])],[(0,[z7,z0,z2,z4,z957,z6]),(0,[z958,z0,z2,z4,z5,z6])],[(0,[z120,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z712,z6])],[(0,[z7,z0,z959,z4,z5,z6]),(0,[z36,z0,z3,z84,z5,z6]),(0,[z7,z58,z150,z4,z5,z6]),(0,[z7,z0,z2,z19,z5,z429]),(0,[z7,z161,z2,z4,z5,z108])],[(0,[z145,z0,z3,z4,z5,z6]),(0,[z7,z0,z67,z286,z4,z5]),(0,[z0,z27,z353,z4,z5,z6]),(0,[z960,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z4,z961,z6]),(0,[z7,z0,z962,z4,z5,z6]),(0,[z7,z0,z2,z963,z5,z6]),(0,[z90,z7,z0,z744,z4,z5]),(0,[z7,z0,z2,z382,z11,z4]),(0,[z7,z0,z2,z4,z5,z964])],[(0,[z162,z7,z0,z88,z27,z5]),(0,[z338,z0,z81,z4,z206,z6]),(0,[z7,z0,z30,z2,z951,z5]),(0,[z7,z0,z2,z4,z5,z965]),(0,[z7,z0,z174,z744,z4,z5])]],
   [[(0,[z338,z0,z509,z4,z206,z6]),(0,[z7,z0,z740,z2,z4,z243])],[(0,[z1,z3,z4,z5,z6,z108]),(0,[z7,z203,z0,z3,z4,z5]),(0,[z36,z0,z37,z84,z5,z6]),(0,[z7,z0,z2,z4,z5,z796]),(0,[z966,z0,z2,z4,z5,z6]),(0,[z7,z0,z2,z797,z125,z4]),(0,[z7,z0,z2,z967,z5,z6])],[(0,[z7,z0,z968,z4,z5,z6]),(0,[z7,z0,z124,z27,z4,z5]),(0,[z7,z47,z2,z126,z5,z6]),(0,[z162,z7,z0,z88,z2,z142]),(0,[z7,z0,z2,z4,z243,z122])],[(0,[z7,z0,z27,z40,z5,z6]),(0,[z7,z969,z2,z4,z5,z6]),(0,[z112,z7,z0,z2,z4,z142])],[(0,[z158,z418,z0,z3,z4,z5]),(0,[z7,z922,z0,z3,z4,z5]),(0,[z0,z233,z67,z3,z4,z5]),(0,[z7,z0,z396,z503,z5,z6]),(0,[z7,z58,z773,z4,z5,z6])],[(0,[z36,z0,z2,z84,z5,z6]),(0,[z7,z773,z28,z4,z5,z6]),(0,[z7,z0,z970,z4,z5,z6])],[(0,[z7,z0,z971,z4,z5,z6]),(0,[z7,z489,z2,z4,z5,z122]),(0,[z7,z0,z2,z972,z5,z6]),(0,[z10,z7,z0,z2,z19,z6]),(0,[z7,z0,z2,z4,z5,z973])],[(0,[z7,z0,z2,z4,z5,z974]),(0,[z7,z0,z3,z4,z5,z975]),(0,[z240,z0,z3,z4,z5,z6])]],
   [[(0,[z341,z0,z3,z4,z5,z6]),(0,[z7,z0,z104,z503,z5,z6])],[(0,[z7,z0,z976,z4,z5,z6]),(0,[z373,z0,z3,z4,z5,z6]),(0,[z7,z418,z0,z2,z4,z5]),(0,[z194,z7,z433,z4,z5,z6]),(0,[z7,z0,z27,z4,z798,z5]),(0,[z977,z0,z2,z4,z5,z6])],[(0,[z551,z1,z2,z4,z5,z6]),(0,[z7,z0,z424,z4,z5,z6]),(0,[z130,z489,z2,z4,z5,z6]),(0,[z132,z7,z27,z4,z5,z89]),(0,[z0,z27,z222,z4,z5,z6]),(0,[z978,z0,z2,z4,z5,z6])],[(1,[z203,z0,z3,z4,z5]),(0,[z7,z0,z979,z4,z5,z6]),(0,[z166,z0,z105,z4,z5,z6]),(0,[z7,z0,z2,z4,z980,z6]),(0,[z981,z0,z2,z4,z5,z6]),(0,[z7,z0,z982,z4,z5,z6])],[(0,[z418,z0,z1,z3,z4,z5]),(0,[z7,z385,z0,z27,z4,z5]),(0,[z7,z0,z3,z983,z5,z6]),(0,[z7,z0,z2,z4,z984,z6]),(0,[z7,z16,z54,z2,z17,z6])],[(0,[z7,z0,z985,z4,z5,z6])],[(0,[z101,z203,z1,z2,z4,z5]),(0,[z7,z0,z986,z2,z4,z5]),(0,[z7,z0,z27,z125,z4,z6]),(0,[z7,z489,z2,z215,z5,z6]),(0,[z7,z0,z2,z4,z154,z122])],[(0,[z7,z0,z987,z2,z4,z6]),(0,[z7,z0,z2,z4,z5,z975]),(0,[z75,z0,z62,z4,z76,z6]),(0,[z7,z0,z2,z988,z5,z6]),(0,[z94,z336,z0,z2,z4,z5]),(0,[z7,z0,z773,z4,z5,z6])]],
   [[(0,[z7,z203,z2,z4,z5,z108]),(0,[z7,z0,z989,z4,z5,z6]),(0,[z0,z643,z27,z4,z5,z6]),(0,[z7,z0,z2,z4,z990,z6]),(0,[z7,z0,z88,z2,z40,z5]),(0,[z991,z0,z2,z4,z5,z6]),(0,[z7,z0,z33,z355,z5,z6]),(0,[z992,z0,z2,z4,z5,z6])],[(0,[z7,z0,z27,z4,z5,z6]),(0,[z7,z0,z993,z2,z4,z6])],[(0,[z112,z0,z3,z4,z5,z113]),(0,[z7,z0,z2,z4,z994,z6]),(0,[z7,z2,z4,z5,z995,z6]),(0,[z7,z0,z996,z4,z5,z6])],[(1,[z0,z872,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z997]),(0,[z94,z0,z2,z4,z5,z796])],[(0,[z7,z998,z0,z2,z4,z5]),(0,[z7,z0,z2,z4,z5,z999]),(0,[z7,z0,z1000,z2,z4,z6]),(0,[z277,z0,z27,z4,z5,z6])],[(0,[z7,z0,z445,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z1001]),(0,[z7,z3,z4,z5,z753,z6])],[(0,[z7,z0,z1002,z4,z5,z6]),(0,[z7,z0,z1003,z4,z5,z6]),(0,[z7,z0,z104,z732,z5,z6]),(0,[z482,z7,z0,z2,z19,z6])],[(0,[z7,z0,z2,z4,z1004,z6]),(0,[z7,z462,z53,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z1005]),(0,[z7,z0,z2,z4,z5,z1006]),(0,[z132,z7,z2,z4,z5,z782]),(0,[z7,z0,z2,z218,z5,z6])]],
   [[(0,[z7,z0,z2,z4,z5,z1007]),(0,[z112,z418,z0,z3,z4,z5]),(0,[z492,z0,z2,z4,z206,z6]),(0,[z7,z0,z1008,z2,z5,z6])],[(0,[z7,z0,z2,z4,z1009,z6]),(0,[z7,z1010,z2,z4,z5,z6])],[(0,[z112,z0,z2,z4,z5,z113]),(0,[z112,z57,z2,z4,z5,z113]),(0,[z7,z0,z2,z1011,z5,z6]),(0,[z7,z95,z2,z4,z5,z782])],[(0,[z7,z0,z2,z215,z299,z6]),(0,[z7,z2,z846,z126,z5,z6]),(0,[z7,z0,z1012,z4,z5,z6]),(0,[z7,z0,z2,z19,z6,z298])],[(0,[z134,z0,z465,z4,z5,z6]),(0,[z7,z0,z2,z4,z195,z122]),(0,[z94,z0,z2,z4,z5,z502])],[(0,[z7,z901,z2,z4,z5,z6]),(0,[z7,z1013,z2,z4,z5,z6]),(0,[z7,z0,z2,z1014,z4,z5])],[(0,[z0,z72,z4,z5,z200,z6])],[(0,[z7,z0,z1015,z4,z5,z6]),(0,[z418,z0,z27,z3,z4,z5]),(0,[z7,z0,z27,z826,z4,z5]),(0,[z7,z0,z2,z1016,z5,z6]),(0,[z7,z0,z2,z1017,z5,z6]),(0,[z7,z0,z2,z19,z549,z6])]],
   [[(0,[z112,z0,z118,z3,z4,z5]),(0,[z7,z0,z2,z4,z1018,z6]),(0,[z7,z0,z2,z4,z5,z1019]),(0,[z0,z2,z4,z5,z6,z1020])],[(0,[z112,z0,z86,z4,z5,z113]),(0,[z7,z0,z118,z2,z4,z195]),(0,[z7,z47,z0,z2,z125,z6])],[(0,[z162,z7,z0,z88,z3,z5]),(1,[z7,z2,z4,z5,z782]),(0,[z7,z0,z740,z2,z4,z5])],[(0,[z0,z1021,z3,z4,z5,z6]),(0,[z486,z0,z2,z4,z5,z6]),(0,[z7,z0,z286,z4,z5,z6]),(0,[z7,z0,z2,z1022,z5,z6]),(0,[z7,z57,z286,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z910]),(0,[z293,z0,z27,z4,z5,z6])],[(0,[z7,z0,z2,z4,z5,z1023]),(0,[z7,z0,z1024,z4,z5,z6]),(0,[z0,z3,z472,z4,z5,z6]),(0,[z7,z0,z3,z4,z5,z1025]),(0,[z599,z0,z27,z4,z5,z6]),(0,[z7,z0,z30,z2,z4,z5]),(0,[z94,z7,z0,z2,z4,z142])],[(0,[z338,z0,z2,z4,z712,z6])],[(0,[z7,z0,z2,z4,z1026,z6]),(0,[z7,z0,z2,z19,z457,z6])]],
   [[(0,[z293,z0,z445,z4,z5,z6]),(0,[z134,z335,z2,z4,z5,z6]),(0,[z7,z418,z0,z3,z4,z5]),(0,[z1027,z0,z2,z4,z5,z6])],[(0,[z134,z418,z0,z3,z4,z5]),(0,[z7,z0,z3,z4,z5,z592]),(0,[z7,z0,z147,z18,z27,z6]),(0,[z166,z0,z28,z4,z5,z6]),(0,[z1028,z0,z2,z4,z5,z6]),(0,[z7,z2,z4,z757,z17,z6]),(0,[z7,z0,z2,z4,z5,z1029])],[(0,[z7,z0,z1030,z2,z4,z5]),(0,[z7,z0,z2,z4,z5,z1031]),(0,[z7,z0,z1032,z4,z5,z6])],[(0,[z7,z0,z3,z4,z5,z242])],[(0,[z7,z0,z1033,z4,z5,z6]),(0,[z7,z0,z1034,z2,z4,z5]),(0,[z0,z439,z3,z4,z5,z6]),(0,[z7,z1035,z0,z3,z4,z5]),(0,[z7,z0,z3,z382,z4,z5]),(0,[z7,z0,z2,z4,z5,z725]),(0,[z7,z0,z174,z72,z4,z5]),(0,[z13,z293,z28,z4,z5,z6]),(0,[z7,z0,z1036,z2,z5,z6]),(0,[z7,z1037,z0,z2,z4,z5])],[(0,[z7,z0,z2,z4,z5,z1025]),(1,[z7,z0,z740,z2,z4])],[(0,[z7,z0,z1038,z4,z5,z6]),(0,[z7,z0,z1039,z4,z5,z6]),(0,[z7,z0,z4,z711,z5,z6]),(0,[z1040,z0,z2,z4,z5,z6])],[(0,[z7,z0,z27,z4,z299,z6]),(0,[z7,z1041,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z3,z4,z5,z781]),(0,[z36,z0,z124,z2,z84,z5]),(0,[z7,z47,z2,z846,z5,z6])],[(0,[z7,z0,z2,z1042,z4,z5]),(0,[z7,z0,z2,z4,z5,z592]),(0,[z7,z0,z1043,z4,z5,z6]),(0,[z7,z1044,z0,z2,z4,z5])],[(0,[z7,z0,z1045,z4,z5,z6]),(0,[z7,z0,z2,z1046,z5,z6]),(0,[z7,z0,z1047,z4,z5,z6]),(0,[z0,z27,z3,z4,z5,z6]),(0,[z7,z0,z2,z1048,z5,z6]),(0,[z36,z0,z2,z875,z5,z6]),(0,[z7,z0,z1049,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z429]),(0,[z7,z0,z1050,z4,z5,z6])],[(0,[z7,z0,z1051,z4,z5,z6]),(0,[z7,z1052,z2,z4,z5,z6]),(0,[z460,z7,z80,z4,z5,z6]),(0,[z7,z0,z1000,z3,z4,z6]),(0,[z7,z0,z2,z4,z5,z242]),(0,[z7,z1053,z2,z4,z5,z6])],[(0,[z7,z0,z2,z1054,z4,z6]),(0,[z7,z0,z2,z1055,z5,z6]),(0,[z7,z0,z2,z382,z4,z5])],[(0,[z338,z0,z3,z4,z206,z6]),(0,[z112,z57,z3,z4,z5,z6]),(0,[z7,z0,z1056,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z510]),(0,[z7,z0,z1057,z4,z5,z6]),(0,[z7,z0,z1058,z4,z5,z6]),(0,[z7,z0,z30,z2,z4,z195]),(0,[z7,z0,z1059,z4,z5,z6])],[(0,[z7,z0,z2,z4,z1060,z6]),(0,[z7,z0,z1061,z4,z5,z6]),(0,[z94,z0,z424,z4,z5,z200]),(0,[z7,z16,z2,z190,z4,z6])],[(0,[z558,z0,z3,z4,z5,z6]),(0,[z13,z166,z28,z4,z5,z6]),(0,[z162,z7,z0,z88,z2,z11])]],
   [[(0,[z7,z0,z67,z27,z4,z5]),(0,[z112,z0,z2,z4,z5,z487]),(0,[z7,z0,z27,z4,z195,z6]),(0,[z7,z0,z27,z4,z142,z6]),(0,[z74,z0,z2,z875,z5,z6]),(0,[z7,z0,z2,z4,z5,z1062]),(0,[z7,z0,z1063,z4,z5,z6]),(0,[z1064,z0,z2,z4,z5,z6]),(0,[z162,z7,z0,z88,z2,z5])],[(0,[z74,z0,z3,z85,z5,z6]),(0,[z0,z3,z522,z4,z5,z6]),(0,[z7,z0,z2,z125,z4,z1065]),(0,[z7,z77,z2,z4,z757,z6]),(0,[z7,z0,z2,z107,z6,z122])],[(0,[z7,z0,z1066,z4,z5,z6]),(0,[z7,z1067,z2,z4,z5,z6]),(0,[z7,z1068,z2,z4,z5,z6]),(0,[z7,z0,z2,z107,z5,z50])],[(0,[z203,z0,z1,z3,z4,z5]),(0,[z7,z0,z2,z4,z1069,z6]),(0,[z117,z7,z0,z118,z2,z107])],[(0,[z7,z0,z1070,z4,z5,z6]),(0,[z7,z0,z1071,z4,z5,z6]),(0,[z7,z0,z3,z11,z4,z6]),(0,[z7,z0,z2,z1072,z5,z6]),(0,[z7,z489,z2,z4,z5,z50]),(0,[z7,z0,z2,z4,z5,z1065]),(0,[z1073,z7,z0,z2,z4,z5])],[(0,[z7,z16,z3,z4,z17,z6]),(0,[z338,z0,z2,z4,z206,z6]),(0,[z7,z0,z1074,z4,z5,z6])],[(0,[z7,z0,z67,z4,z5,z280]),(0,[z0,z3,z4,z5,z6,z533]),(0,[z489,z2,z3,z4,z5,z6]),(0,[z1075,z0,z2,z4,z5,z6]),(0,[z90,z7,z0,z64,z4,z5])],[(0,[z0,z2,z84,z875,z5,z6]),(0,[z7,z0,z2,z1076,z4,z5])]],
   [[(0,[z7,z0,z305,z4,z5,z6]),(0,[z7,z1077,z0,z2,z4,z5]),(0,[z7,z0,z3,z4,z5,z32]),(0,[z7,z47,z27,z126,z5,z6]),(0,[z7,z0,z54,z27,z5,z6]),(0,[z7,z0,z27,z4,z243,z122]),(0,[z7,z16,z2,z4,z17,z32])],[(0,[z74,z0,z2,z85,z5,z6]),(0,[z0,z2,z875,z85,z5,z6]),(0,[z7,z0,z30,z2,z1072,z5]),(0,[z7,z0,z2,z4,z5,z1078]),(0,[z7,z1079,z2,z4,z5,z6])],[(0,[z0,z3,z538,z4,z5,z6]),(0,[z7,z0,z220,z4,z265,z6]),(0,[z7,z0,z125,z352,z4,z6]),(0,[z7,z0,z2,z843,z4,z6])],[(0,[z7,z0,z3,z49,z5,z50])],[(0,[z7,z0,z30,z3,z4,z5]),(0,[z7,z0,z3,z4,z1080,z6]),(0,[z74,z0,z70,z85,z5,z6]),(0,[z112,z0,z2,z215,z5,z113]),(0,[z166,z0,z116,z4,z5,z6]),(0,[z7,z47,z435,z126,z5,z6]),(0,[z7,z0,z2,z19,z4,z592]),(0,[z7,z0,z2,z11,z4,z6])],[(0,[z7,z57,z3,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z1081]),(0,[z7,z489,z2,z4,z299,z6]),(0,[z7,z0,z1082,z4,z5,z6]),(0,[z7,z16,z2,z4,z17,z6])],[(0,[z7,z0,z1083,z4,z5,z6]),(0,[z162,z7,z0,z124,z2,z5]),(0,[z7,z0,z86,z40,z5,z6]),(0,[z7,z0,z2,z4,z5,z1084]),(0,[z1085,z0,z2,z4,z5,z6])],[(0,[z7,z1086,z2,z4,z5,z6])]],
   [[(0,[z7,z0,z1087,z4,z5,z6]),(0,[z336,z0,z3,z4,z5,z6]),(0,[z0,z3,z556,z4,z5,z6]),(0,[z7,z0,z124,z2,z4,z777])],[(0,[z75,z0,z3,z4,z76,z6]),(0,[z0,z67,z3,z4,z5,z200]),(0,[z7,z77,z3,z4,z78,z6]),(0,[z7,z418,z0,z174,z4,z5]),(1,[z0,z2,z4,z712,z6]),(0,[z7,z0,z2,z4,z299,z50]),(0,[z1088,z0,z2,z4,z5,z6]),(0,[z7,z0,z801,z2,z5,z50]),(0,[z117,z7,z0,z2,z107,z6])],[(0,[z0,z1,z67,z3,z4,z5]),(0,[z492,z0,z3,z4,z5,z6]),(0,[z7,z0,z2,z1089,z5,z6]),(0,[z1090,z0,z2,z4,z5,z6])],[(0,[z7,z0,z2,z1091,z5,z6]),(0,[z7,z0,z1092,z4,z5,z6]),(0,[z7,z1093,z2,z4,z5,z6]),(0,[z7,z0,z105,z603,z5,z6])],[(0,[z7,z0,z147,z18,z3,z6]),(0,[z7,z0,z2,z4,z1080,z6]),(0,[z7,z1094,z2,z4,z5,z6]),(0,[z0,z2,z4,z712,z76,z6]),(0,[z7,z378,z0,z2,z19,z6]),(0,[z7,z0,z740,z2,z4,z6])],[(0,[z7,z0,z379,z105,z5,z6]),(0,[z7,z0,z286,z215,z5,z6]),(0,[z7,z58,z59,z4,z5,z6]),(0,[z1095,z0,z2,z4,z5,z6]),(0,[z7,z16,z91,z4,z17,z6]),(0,[z7,z0,z1096,z4,z5,z6])],[(0,[z7,z0,z62,z4,z5,z6]),(0,[z312,z0,z3,z4,z5,z6]),(0,[z7,z489,z2,z4,z195,z6]),(1,[z0,z2,z4,z5,z796]),(1,[z7,z2,z4,z757,z6])],[(0,[z7,z0,z2,z4,z1097,z6]),(0,[z7,z0,z2,z4,z5,z1098]),(0,[z112,z0,z3,z4,z5,z200]),(0,[z7,z0,z67,z2,z4,z5]),(0,[z7,z0,z1099,z4,z5,z6]),(0,[z112,z0,z2,z40,z5,z113]),(0,[z7,z0,z147,z2,z4,z592]),(0,[z7,z0,z2,z1076,z355,z5])]],
   [[(0,[z7,z1035,z0,z2,z4,z5]),(0,[z7,z0,z116,z4,z711,z6])],[(0,[z75,z0,z2,z4,z76,z6]),(0,[z7,z77,z2,z4,z78,z6]),(0,[z7,z291,z2,z4,z5,z89]),(0,[z7,z0,z2,z19,z657,z6])],[(0,[z7,z0,z81,z4,z5,z6]),(0,[z7,z0,z2,z4,z5,z1100]),(0,[z7,z0,z801,z2,z4,z5])],[(0,[z7,z0,z509,z4,z5,z6]),(0,[z7,z0,z352,z4,z5,z6]),(0,[z7,z459,z2,z4,z5,z89]),(0,[z7,z0,z2,z4,z1101,z6])],[(0,[z7,z0,z2,z4,z1102,z6]),(0,[z7,z0,z86,z4,z5,z6]),(0,[z7,z0,z1103,z4,z5,z6]),(0,[z7,z57,z86,z4,z5,z6])],[(0,[z7,z1104,z3,z4,z5,z6]),(0,[z369,z0,z3,z4,z5,z6]),(0,[z7,z0,z27,z218,z5,z6]),(0,[z7,z0,z160,z326,z4,z6]),(0,[z7,z1105,z2,z4,z5,z6])],[(0,[z7,z0,z2,z1106,z5,z6]),(0,[z166,z0,z97,z4,z5,z6])],[(0,[z7,z0,z2,z983,z5,z6]),(0,[z7,z0,z54,z2,z5,z6])]],
   [[(0,[z0,z3,z4,z5,z594,z6]),(0,[z7,z0,z2,z4,z1107,z6]),(0,[z7,z0,z286,z40,z5,z6]),(0,[z7,z0,z2,z4,z142,z89]),(0,[z7,z0,z104,z105,z5,z6])],[(0,[z7,z0,z1108,z4,z5,z6]),(0,[z7,z0,z27,z19,z6,z298]),(0,[z7,z1109,z2,z4,z5,z6])],[(0,[z0,z664,z27,z4,z5,z6]),(0,[z268,z7,z0,z24,z4,z5]),(0,[z7,z0,z2,z4,z1110,z6])],[(0,[z7,z0,z2,z1111,z5,z6]),(0,[z7,z0,z2,z4,z5,z1112])],[(0,[z7,z0,z780,z2,z5,z6]),(0,[z7,z0,z3,z4,z5,z9]),(0,[z7,z0,z124,z2,z4,z5]),(0,[z7,z0,z1113,z4,z5,z6]),(0,[z7,z0,z14,z386,z5,z6])],[(0,[z7,z0,z1021,z4,z5,z6]),(0,[z7,z0,z2,z4,z1114,z6]),(0,[z7,z1104,z2,z4,z5,z6]),(0,[z7,z0,z2,z355,z5,z955])],[(0,[z134,z0,z1021,z4,z5,z6]),(0,[z112,z0,z67,z3,z4,z5]),(0,[z7,z1115,z2,z4,z5,z6])],[(0,[z112,z0,z3,z215,z5,z6]),(0,[z0,z3,z4,z5,z610,z6]),(0,[z7,z0,z2,z4,z5,z1116]),(0,[z7,z0,z1117,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 535) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 535).take 526) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1061).take 132) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1193)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [535, 526, 132] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 118).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 118).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 230).take 26).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [118, 112, 26] = true :=
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

end PEqualNP.Outside.L_meta_41028

theorem PEqualNP.Outside.L_meta_41028 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4274571264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4274571264) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41028.solve