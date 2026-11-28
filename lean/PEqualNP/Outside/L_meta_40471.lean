import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_40471

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x000010c2a430ae1c#64 ++ 0x20000218548615c3#64 ++ 0xa813b1c7ec71fe3f#64 ++ 0xd5027638fd8e3fc7#64 : BitVec 256),
   (0x08251659859666c1#64 ++ 0x4104a2cb30b2ccd8#64 ++ 0xf86d5e79979e67c7#64 ++ 0xbf0dabcf32f3ccf8#64 : BitVec 256),
   (0x138a606e181b8369#64 ++ 0x82714c0dc303706d#64 ++ 0xd78e607e181f87ff#64 ++ 0x7af1cc0fc303f0ff#64 : BitVec 256),
   (0x25d07b801ee005b6#64 ++ 0x04ba0f7003dc00b6#64 ++ 0xfff07f801fe007fe#64 ++ 0xfffe0ff003fc00ff#64 : BitVec 256),
   (0x06ff80001b4d5000#64 ++ 0x00dff0000369aa00#64 ++ 0x9fff80001ffff805#64 ++ 0xf3fff00003ffff00#64 : BitVec 256),
   (0x077fed3540000000#64 ++ 0x00effda6a8000000#64 ++ 0xe7ffffffe0000003#64 ++ 0xfcfffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.and, [6, 4]⟩, ⟨.and, [7, 5]⟩, ⟨.or, [0, 8]⟩, ⟨.or, [6, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 11]⟩, ⟨.or, [12, 9]⟩, ⟨.or, [10, 5]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xa813b1c7ec71fe3f 0xd5027638fd8e3fc7

def z1 : W := mkw 0x022f8477e010aa08 0x2045f08efc021541 0x000f807fe011f801 0x0001f00ffc023f00

def z2 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fff80001ffff805 0xf3fff00003ffff00

def z3 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z4 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86d5e79979e67c7 0xbf0dabcf32f3ccf8

def z5 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78e607e181f87ff 0x7af1cc0fc303f0ff

def z6 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff07f801fe007fe 0xfffe0ff003fc00ff

def z7 : W := mkw 0x028a000018090000 0x0051400003012000 0x978e0000181f8005 0x72f1c0000303f000

def z8 : W := mkw 0x1100606e00128369 0x82200c0dc002506d 0x4000607e000007fa 0x08000c0fc00000ff

def z9 : W := mkw 0x032fed3540000000 0x0065fda6a8000000 0x600fffffe0000003 0x0c01fffffc000000

def z10 : W := mkw 0x1b8a726e9d9fe7e9 0xc3714e4dd3b3fcfd 0xdf8e607e1f9fe7ff 0x7bf1cc0fc3f3fcff

def z11 : W := mkw 0x0825161185846480 0x4104a2c230b08c90 0x28611e0187806000 0x850c23c030f00c00

def z12 : W := mkw 0x138a602618098128 0x82714c04c3013025 0x0782200608018038 0x40f04400c1003007

def z13 : W := mkw 0x067f8000034d5000 0x00cff0000069aa00 0x087f800007fff801 0x810ff00000ffff00

def z14 : W := mkw 0x008000001a491000 0x0010000003492200 0x0000000008619800 0x00000000010c3300

def z15 : W := mkw 0x1baf767f9d9fe7e9 0xc375eecff3b3fcfd 0xffef7e7f9f9fe7ff 0xfffdefcff3f3fcff

def z16 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87fffffffffffff 0xff0fffffffffffff

def z17 : W := mkw 0x000000822020881c 0x2000001044041103 0x0012a18668619838 0x40025430cd0c3307

def z18 : W := mkw 0x25d07bc2bef0afbe 0x24ba0f7857de15f7 0xfff3ffc7fff1ffff 0xfffe7ff8fffe3fff

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0x800020000800063e 0x50000400010000c7

def z20 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x17ef8000139ff801 0x22fdf0000273ff00

def z21 : W := mkw 0x27ffffb55ee005b6 0x04fffff6abdc00b6 0xffffffffffe007ff 0xfffffffffffc00ff

def z22 : W := mkw 0x00000042a010aa08 0x2000000854021541 0x00038047e011f801 0x00007008fc023f00

def z23 : W := mkw 0x08251619058644c1 0x4104a2c320b0c898 0xf86c5e38178e07c6 0xbf0d8bc702f1c0f8

def z24 : W := mkw 0x04758d1143445000 0x008eb1a228688a00 0x28719f81e7e07800 0x850e33f03cfc0f00

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0x900c0000101e0005 0x320180000203c000

def z26 : W := mkw 0x0000120004800480 0x0000024000900090 0xf8605e00178007c6 0xbf0c0bc002f000f8

def z27 : W := mkw 0x2df57fd99ff667f7 0x45beaffb33feccfe 0xfffd7ff99ffe67ff 0xffffafff33ffccff

def z28 : W := mkw 0x030a606600108208 0x00614c0cc0021041 0xc78e607e0811863f 0x78f1cc0fc10230c7

def z29 : W := mkw 0x0eff96599fdf76c1 0x41dff2cb33fbeed8 0xffffde799fffffc7 0xfffffbcf33fffff8

def z30 : W := mkw 0x08001659849226c1 0x410002cb309244d8 0x60005e79800007c2 0x0c000bcf300000f8

def z31 : W := mkw 0x04d000001a400000 0x009a000003480000 0x9ff000001fe00004 0xf3fe000003fc0000

def z32 : W := mkw 0x27fffb801fed55b6 0x04ffff7003fdaab6 0xffffff801fffffff 0xfffffff003ffffff

def z33 : W := mkw 0x24501bc2a6f0ae9e 0x248a037854de15d3 0xa873bfc7eff1fe3f 0xd50e77f8fdfe3fc7

def z34 : W := mkw 0x24500b0002c00082 0x048a016000580010 0x00600e0003800000 0x000c01c000700000

def z35 : W := mkw 0x0000004800120241 0x0000000900024048 0xd00c4078101e07c7 0x3a01880f0203c0f8

def z36 : W := mkw 0x24501b8006e00496 0x048a037000dc0092 0x28701f8007e00000 0x850e03f000fc0000

def z37 : W := mkw 0x2df57f919fe465b6 0x45beaff233fc8cb6 0xfff17f819fe067fe 0xfffe2ff033fc0cff

def z38 : W := mkw 0x075ae92440000000 0x00eb5d2488000000 0x0792a18660000000 0x40f25430cc000000

def z39 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0x506c4e38138e01c0 0x2a0d89c70271c038

def z40 : W := mkw 0x1080004a181b8369 0x821000094303706d 0xd00c4078181f87ff 0x3a01880f0303f0ff

def z41 : W := mkw 0x020a802440000000 0x0041500488000000 0x0002800660000000 0x00005000cc000000

def z42 : W := mkw 0x06ff84355b4d5000 0x00dff086ab69aa00 0x9fff807ffffff805 0xf3fff00fffffff00

def z43 : W := mkw 0x0000004080102200 0x0000000810020440 0x0001004180106001 0x0000200830020c00

def z44 : W := mkw 0x138a60ee383b8b7d 0xa2714c1dc707716f 0xd79ee1fe787f9fff 0x7af3dc3fcf0ff3ff

def z45 : W := mkw 0x0180604218108328 0x00300c0843021065 0xd7826046181187ff 0x7af04c08c30230ff

def z46 : W := mkw 0x0825145985166641 0x4104a28b30a2ccc8 0xa80d1079841e6607 0x9501a20f3083ccc0

def z47 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x880220460c71fe3f 0x51004408c18e3fc7

def z48 : W := mkw 0x37da6b2c1acb01e3 0x86fb4d658359603c 0x57ec4e38138e01c0 0x2afd89c70271c038

def z49 : W := mkw 0x00001080a4202c14 0x2000021014840582 0xa811b181ec607e3e 0xd50236303d8c0fc7

def z50 : W := mkw 0x0eff96599fdf76c1 0x41dff2cb33fbeed8 0xffed5e79979e67c7 0xbffdabcf32f3ccf8

def z51 : W := mkw 0x077ffdf7e430ae1c 0x20efffbefc8615c3 0xefffffffec71fe3f 0xfdfffffffd8e3fc7

def z52 : W := mkw 0x07ffed355b4d5000 0x00fffda6ab69aa00 0xfffffffffffff807 0xffffffffffffff00

def z53 : W := mkw 0x080012caa5b6eedd 0x6100025954b6dddb 0x180000001ffffffc 0x0300000003ffffff

def z54 : W := mkw 0x000010428410a608 0x00000208508214c1 0xa80330478c11e63f 0xd5006608f1823cc7

def z55 : W := mkw 0x27ffeb001bcd51a2 0x04fffd600379aa34 0x57ec4e00138e01c0 0x2afd89c00271c038

def z56 : W := mkw 0x37da69a61a69813e 0x86fb4d34c34d3027 0x0792218608618038 0x40f24430c10c3007

def z57 : W := mkw 0x37da7bee1efb87ff 0x86fb4f7dc3df70ff 0xfffe7ffe1fff87ff 0xffffcfffc3fff0ff

def z58 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x17ec0000138e0000 0x22fd80000271c000

def z59 : W := mkw 0x01006d3540000000 0x00200da6a8000000 0x60007fffe0000002 0x0c000ffffc000000

def z60 : W := mkw 0x0f7fff7dc59666c1 0x41efffefb8b2ccd8 0xfffffffff79e67c7 0xfffffffffef3ccf8

def z61 : W := mkw 0x208012801ee005b6 0x0410025003dc00b6 0xf8605e001fe007fe 0xbf0c0bc003fc00ff

def z62 : W := mkw 0x110070eea432af7d 0xa2200e1dd48655ef 0x600071ffe00007fa 0x0c000e3ffc0000ff

def z63 : W := mkw 0x07dae9245a491000 0x00fb5d248b492200 0x0792a18668619800 0x40f25430cd0c3300

def z64 : W := mkw 0x0000000001044000 0x0000000000208800 0x18000000179e6004 0x0300000002f3cc00

def z65 : W := mkw 0x0450800002401000 0x008a100000480200 0x0010800000601800 0x00021000000c0300

def z66 : W := mkw 0x0180600018000120 0x00300c0003000024 0xd7806000180007fe 0x7af00c00030000ff

def z67 : W := mkw 0x120a006e001b8249 0x8241400dc0037049 0x000e007e001f8001 0x0001c00fc003f000

def z68 : W := mkw 0x0025041100000000 0x0004a08220000000 0xe07fffffe0000003 0xfc0ffffffc000000

def z69 : W := mkw 0x0025041100000000 0x0004a08220000000 0xe06d5e7980000003 0xbc0dabcf30000000

def z70 : W := mkw 0x0000108004200414 0x0000021000840082 0xa81031800c60063e 0xd5020630018c00c7

def z71 : W := mkw 0x09a576599d9667e1 0x4134aecb33b2ccfc 0xffed7e799f9e67ff 0xfffdafcf33f3ccff

def z72 : W := mkw 0x000000822020881c 0x2000001044041103 0x0000218660000038 0x00000430cc000007

def z73 : W := mkw 0x0025000001044000 0x0004a00000208800 0x986d0000179e6005 0xb30da00002f3cc00

def z74 : W := mkw 0x075aed3540000000 0x00eb5da6a8000000 0x6792ffffe0000002 0x4cf25ffffc000000

def z75 : W := mkw 0x02af80001b4d5000 0x0055f0000369aa00 0x180f80001ffff805 0x0301f00003ffff00

def z76 : W := mkw 0x05756d1100000000 0x00aeada220000000 0xe7fd7ff980000003 0xfcffafff30000000

def z77 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0xbfffb1c7fffff807 0xf7fff638ffffff00

def z78 : W := mkw 0x0000108004200414 0x0000021000840082 0xa813b1800c71fe3f 0xd5027630018e3fc7

def z79 : W := mkw 0x208012c2bef0afbe 0x2410025857de15f7 0xb813b1c7fff1ffff 0xd7027638fffe3fff

def z80 : W := mkw 0x31007bee04b287ff 0x86200f7dc09650ff 0x60007ffe000007fa 0x0c000fffc00000ff

def z81 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xdf9fe07e1c7fffff 0xfbf3fc0fc38fffff

def z82 : W := mkw 0x2df57fdbbff6efff 0x65beaffb77feddff 0xffffffffffffffff 0xffffffffffffffff

def z83 : W := mkw 0x1080004a181b8369 0x821000094303706d 0x10000000181f87fc 0x020000000303f0ff

def z84 : W := mkw 0x120a002600098008 0x82414004c0013001 0x0002000600018000 0x00004000c0003000

def z85 : W := mkw 0x0000004800120241 0x0000000900024048 0x40004078000007c2 0x0800080f000000f8

def z86 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x68615e79878067c2 0x8d0c2bcf30f00cf8

def z87 : W := mkw 0x00000042a010aa08 0x2000000854021541 0x88138047ec71f805 0xd1027008fd8e3f00

def z88 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002000008118005 0x5000400001023000

def z89 : W := mkw 0x075ae9a66020881c 0x20eb5d34cc041103 0x0792a18668619838 0x40f25430cd0c3307

def z90 : W := mkw 0x37da7beebefbafff 0xa6fb4f7dd7df75ff 0xffffffffffffffff 0xffffffffffffffff

def z91 : W := mkw 0x20001b8004a00496 0x0400037000940092 0x20001f8000000000 0x040003f000000000

def z92 : W := mkw 0x00001082a420ac1c 0x2000021054841583 0x2813b187ec61f838 0xc5027630fd8c3f07

def z93 : W := mkw 0x082514dba536ee5d 0x6104a29b74a6ddcb 0xa81fb1ffec7ffe3f 0xd503f63ffd8fffc7

def z94 : W := mkw 0x24d01b801ee00496 0x049a037003dc0092 0xbff01f801fe00004 0xf7fe03f003fc0000

def z95 : W := mkw 0x338a7bee1cbb87ff 0x86714f7dc39770ff 0xf78e7ffe181f87ff 0x7ef1cfffc303f0ff

def z96 : W := mkw 0x04758d1140000000 0x008eb1a228000000 0x20719f81e0000000 0x840e33f03c000000

def z97 : W := mkw 0x07ffed3558000120 0x00fffda6ab000024 0xf7fffffff80007ff 0xfeffffffff0000ff

def z98 : W := mkw 0x27fffbc2bffdffbe 0x24ffff7857ffbff7 0xffffffc7ffffffff 0xfffffff8ffffffff

def z99 : W := mkw 0x0000000000000000 0x0000000000000000 0xa013b1c7e0000003 0xd4027638fc000000

def z100 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff3ffc7ffe007ff 0xfffe7ff8fffc00ff

def z101 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0xd78e607e100e01c3 0x7af1cc0fc201c038

def z102 : W := mkw 0x0f7fef3d418640c1 0x41effde7a830c818 0xf7fffffff38e01c3 0xfefffffffe71c038

def z103 : W := mkw 0x0825165b8596e6c9 0x4104a2cb70b2dcd9 0xf86f7e7f9f9fe7ff 0xff0defcff3f3fcff

def z104 : W := mkw 0x0475800003445000 0x008eb00000688a00 0x887380000ff1f805 0xd10e700001fe3f00

def z105 : W := mkw 0x0450000000000000 0x008a000000000000 0x87f0000000000000 0xf0fe000000000000

def z106 : W := mkw 0x288012c89ff667f7 0x4510025913feccfe 0x180000001ffe67fc 0x0300000003ffccff

def z107 : W := mkw 0x00001080a4202c14 0x2000021014840582 0x28119181e4607800 0x850232303c8c0f00

def z108 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0x578c4038100e01c0 0x2af188070201c038

def z109 : W := mkw 0x082516d985b666d5 0x4104a2db30b6ccda 0xf87d7ff99ffe67ff 0xff0fafff33ffccff

def z110 : W := mkw 0x08250659819662c1 0x4104a0cb3032cc58 0x506d4e79939e61c1 0x2a0da9cf3273cc38

def z111 : W := mkw 0x067f800000000000 0x00cff00000000000 0x87ff800000000001 0xf0fff00000000000

def z112 : W := mkw 0x0000004200108208 0x0000000840021041 0x000020460000063a 0x00000408c00000c7

def z113 : W := mkw 0x06ff90409f5d7600 0x00dff20813ebaec0 0xbfff90419ffffe07 0xf7fff20833ffffc0

def z114 : W := mkw 0x25d069801a600136 0x04ba0d30034c0026 0x0790218008600038 0x40f20430010c0007

def z115 : W := mkw 0x177fed7f40128369 0x82effdafe802506d 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z116 : W := mkw 0x27ffffb55ee005b6 0x04fffff6abdc00b6 0xfffc7fb81fe007fe 0xffff8ff703fc00ff

def z117 : W := mkw 0x022f843540000000 0x0045f086a8000000 0x000f807fe0000001 0x0001f00ffc000000

def z118 : W := mkw 0x030a6d3540000000 0x00614da6a8000000 0xe78e7fffe0000003 0x7cf1cffffc000000

def z119 : W := mkw 0x0000104084102600 0x00000208108204c0 0xa813b1c7e4106607 0xd5027638fc820cc0

def z120 : W := mkw 0x0550690000000000 0x00aa0d2000000000 0xe7f07f8000000002 0xfcfe0ff000000000

def z121 : W := mkw 0x018072001c8005a0 0x00300e40039000b4 0xffe07e001f8007fe 0xfffc0fc003f000ff

def z122 : W := mkw 0x077fed3543445000 0x00effda6a8688a00 0xefffffffe7e07803 0xfdfffffffcfc0f00

def z123 : W := mkw 0x08001659849226c1 0x410002cb309244d8 0xf00c5e79901e07c7 0x3e018bcf3203c0f8

def z124 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x47ec4e3800000000 0x28fd89c700000000

def z125 : W := mkw 0x0000104084102600 0x00000208108204c0 0xa801104184106607 0x9500220830820cc0

def z126 : W := mkw 0x138a6d7f581b8369 0x82714dafeb03706d 0xf78e7ffff81f87ff 0x7ef1cfffff03f0ff

def z127 : W := mkw 0x022f8000010d5000 0x0045f0000021aa00 0x000f8000001ff801 0x0001f0000003ff00

def z128 : W := mkw 0x05506d3540000000 0x00aa0da6a8000000 0xe7f07fffe0000002 0xfcfe0ffffc000000

def z129 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x2811b1c7e4607e3a 0x85023638fc8c0fc7

def z130 : W := mkw 0x0000108004200414 0x0000021000840082 0x200031800000063a 0x04000630000000c7

def z131 : W := mkw 0x030a602400000000 0x00614c0480000000 0xc78e607e00000003 0x78f1cc0fc0000000

def z132 : W := mkw 0x17ffed7f581b8369 0x82fffdafeb03706d 0xf7fffffff81f87ff 0xfeffffffff03f0ff

def z133 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x080000000c71fe3c 0x01000000018e3fc7

def z134 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x0ff380000fe1f800 0xc1fe700001fc3f00

def z135 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0x57e04e00138001c0 0x2afc09c002700038

def z136 : W := mkw 0x17ffed7f5b5fd369 0x82fffdafeb6bfa6d 0xffffffffffffffff 0xffffffffffffffff

def z137 : W := mkw 0x27dae9801a691136 0x04fb5d30034d2226 0x0792a18008619838 0x40f25430010c3307

def z138 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x67ec7fffe0000002 0x2cfd8ffffc000000

def z139 : W := mkw 0x01006d3540000000 0x00200da6a8000000 0xe013ffffe0000003 0xdc027ffffc000000

def z140 : W := mkw 0x208012801ee005b6 0x0410025003dc00b6 0x180000001fe007fc 0x0300000003fc00ff

def z141 : W := mkw 0x27ffef355ac001a2 0x04fffde6ab580034 0xf7fffffff38001c3 0xfefffffffe700038

def z142 : W := mkw 0x0825045981166241 0x4104a08b3022cc48 0x000d0079801e6001 0x0001a00f3003cc00

def z143 : W := mkw 0x022f843540000000 0x0045f086a8000000 0x000c003800000000 0x0001800700000000

def z144 : W := mkw 0x25507b8006e005b6 0x04aa0f7000dc00b6 0x68707f8007e007fa 0x8d0e0ff000fc00ff

def z145 : W := mkw 0x0000108004200414 0x0000021000840082 0x080000000c60063c 0x01000000018c00c7

def z146 : W := mkw 0x08250659019642c1 0x4104a0cb2032c858 0xd06c4e78139e07c7 0x3a0d89cf0273c0f8

def z147 : W := mkw 0x17ffe06e181b8369 0x82fffc0dc303706d 0xd7ffe07e181f87ff 0xfafffc0fc303f0ff

def z148 : W := mkw 0x130a606e00128369 0x82614c0dc002506d 0xc78e607e000007fb 0x78f1cc0fc00000ff

def z149 : W := mkw 0x0800161184802480 0x410002c230900490 0x20001e0180000000 0x040003c030000000

def z150 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x28119181ec71fe3c 0x850232303d8e3fc7

def z151 : W := mkw 0x0080000018000120 0x0010000003000024 0x10000000180007fc 0x02000000030000ff

def z152 : W := mkw 0x06ff90c2bf7dfe1c 0x20dff21857efbfc3 0xbfffb1c7fffffe3f 0xf7fff638ffffffc7

def z153 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xf06d5e79938e01c3 0xbe0dabcf3271c038

def z154 : W := mkw 0x1baf667f199fc3e9 0xc375eccfe333f87d 0xd7ee6e7e1b9f87ff 0x7afdcdcfc373f0ff

def z155 : W := mkw 0x0080000018090000 0x0010000003012000 0x10000000181f8004 0x020000000303f000

def z156 : W := mkw 0x01256d3540000000 0x0024ada6a8000000 0xe06d7fffe0000003 0xbc0daffffc000000

def z157 : W := mkw 0x0475800003445000 0x008eb00000688a00 0x0871800007e07800 0x810e300000fc0f00

def z158 : W := mkw 0x067f843540000000 0x00cff086a8000000 0x87ff807fe0000001 0xf0fff00ffc000000

def z159 : W := mkw 0x01007df7e430ae1c 0x20200fbefc8615c3 0x60007fffe000063a 0x0c000ffffc0000c7

def z160 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0xd78c6038180e07fe 0x7af18c070301c0ff

def z161 : W := mkw 0x08001248859666c1 0x4100024910b2ccd8 0x18000000179e67c4 0x0300000002f3ccf8

def z162 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x706c5e79938e07c2 0x2e0d8bcf3271c0f8

def z163 : W := mkw 0x008000001b4d5000 0x001000000369aa00 0x10000000138e0000 0x020000000271c000

def z164 : W := mkw 0x0000000000000000 0x0000000000000000 0x20119181e0000000 0x840232303c000000

def z165 : W := mkw 0x0000004200108208 0x0000000840021041 0x0002004600118001 0x00004008c0023000

def z166 : W := mkw 0x138a606eb81bab69 0xa2714c0dd703756d 0xd78fe07ff81fffff 0x7af1fc0fff03ffff

def z167 : W := mkw 0x008000001b4d5000 0x001000000369aa00 0x180000001ffff804 0x0300000003ffff00

def z168 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x38611e01979e67c4 0x870c23c032f3ccf8

def z169 : W := mkw 0x138a70eebc3baf7d 0xa2714e1dd78775ef 0xff9ff1fffc7fffff 0xfff3fe3fff8fffff

def z170 : W := mkw 0x077fe02400000000 0x00effc0480000000 0xc7ffe07e00000003 0xf8fffc0fc0000000

def z171 : W := mkw 0x25d07b801fed55b6 0x04ba0f7003fdaab6 0xfff07f801ffffffe 0xfffe0ff003ffffff

def z172 : W := mkw 0x138a606c181b0361 0x82714c0d8303606c 0xd78c4078101e07c7 0x3af1880f0203c0f8

def z173 : W := mkw 0x002510c2a534ee1c 0x2004a21854a69dc3 0xb87fb1c7fffffe3f 0xf70ff638ffffffc7

def z174 : W := mkw 0x25d07bc81ef207f7 0x04ba0f7903de40fe 0xfffc7ff81ffe07ff 0xffff8fff03ffc0ff

def z175 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578c607e100e07fa 0x2af18c0fc201c0ff

def z176 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x17fe80001bef9800 0x62ffd000037df300

def z177 : W := mkw 0x0825061101844080 0x4104a0c220308810 0x00600e0003800000 0x000c01c000700000

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0xa813b1c7ec71f807 0xd5027638fd8e3f00

def z179 : W := mkw 0x07ffed3558090000 0x00fffda6ab012000 0xf7fffffff81f8007 0xfeffffffff03f000

def z180 : W := mkw 0x24759f9146e00496 0x048eb3f228dc0092 0x28719f81e7e00000 0x850e33f03cfc0000

def z181 : W := mkw 0x0f7fff7dc59666c1 0x41efffefb8b2ccd8 0xffed5e79979e67c7 0xbffdabcf32f3ccf8

def z182 : W := mkw 0x25d069001a400122 0x04ba0d2003480024 0x0780000000000000 0x00f0000000000000

def z183 : W := mkw 0x21007b8004a005b6 0x04200f70009400b6 0x60007f80000007fa 0x0c000ff0000000ff

def z184 : W := mkw 0x25d069823a60893e 0x24ba0d30474c1127 0x0792a18668619838 0x40f25430cd0c3307

def z185 : W := mkw 0x16ff804a1b5fd369 0x82dff009436bfa6d 0x9fff80001ffffffd 0xf3fff00003ffffff

def z186 : W := mkw 0x08251659849226c1 0x4104a2cb309244d8 0xe06d5e79800007c3 0xbc0dabcf300000f8

def z187 : W := mkw 0x11006d7f40128369 0x82200dafe802506d 0x60007fffe00007fa 0x0c000ffffc0000ff

def z188 : W := mkw 0x138a60a63829893c 0xa2714c14c7053127 0x0792a18668619838 0x40f25430cd0c3307

def z189 : W := mkw 0x06ff80001a491000 0x00dff00003492200 0x87ff800008619801 0xf0fff000010c3300

def z190 : W := mkw 0x218072801ee005b6 0x04300e5003dc00b6 0xdf8060001fe007fe 0x7bf00c0003fc00ff

def z191 : W := mkw 0x06ff90c2bf7dfe1c 0x20dff21857efbfc3 0x9fff80001ffffe3d 0xf3fff00003ffffc7

def z192 : W := mkw 0x032f643500000000 0x0065ec86a0000000 0xe7ef7e7f80000003 0xfcfdefcff0000000

def z193 : W := mkw 0x020a800000091000 0x0041500000012200 0x0002800000019800 0x0000500000003300

def z194 : W := mkw 0x2dd07fd99ef227f7 0x45ba0ffb33de44fe 0xfff07ff99fe007fe 0xfffe0fff33fc00ff

def z195 : W := mkw 0x06ff80001a400000 0x00dff00003480000 0x9fff80001fe00005 0xf3fff00003fc0000

def z196 : W := mkw 0x06ff80481b5f5241 0x00dff009036bea48 0xdfffc0781fffffc7 0xfbfff80f03fffff8

def z197 : W := mkw 0x0000004200108208 0x0000000840021041 0x800220460811863f 0x50004408c10230c7

def z198 : W := mkw 0x08251619858664c1 0x4104a2c330b0cc98 0x786d5e39978e61c0 0xaf0dabc732f1cc38

def z199 : W := mkw 0x00a500001b4d5000 0x0014a0000369aa00 0x986d00001ffff805 0xb30da00003ffff00

def z200 : W := mkw 0x2100698000200136 0x04200d3000040026 0x0000218000000038 0x0000043000000007

def z201 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0004000100007c6 0x3a000800020000f8

def z202 : W := mkw 0x0000000000000000 0x0000000000000000 0x0811800004607800 0x81023000008c0f00

def z203 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x280031c7ec71fe3e 0x05000638fd8e3fc7

def z204 : W := mkw 0x122f847f401b8249 0x8245f08fe8037049 0x000f807fe01f8001 0x0001f00ffc03f000

def z205 : W := mkw 0x177fed7f401b8249 0x82effdafe8037049 0xe7ffffffe01f8003 0xfcfffffffc03f000

def z206 : W := mkw 0x1100602600008128 0x82200c04c0001025 0x0000200600000038 0x00000400c0000007

def z207 : W := mkw 0x27da7ba41ee005b6 0x04fb4f7483dc00b6 0xfffe7ffe1fe007ff 0xffffcfffc3fc00ff

def z208 : W := mkw 0x120a10eea43bae5d 0xa241421dd48775cb 0xa81fb1ffec7ffe3f 0xd503f63ffd8fffc7

def z209 : W := mkw 0x0825045981166241 0x4104a08b3022cc48 0xd00d4079901e67c7 0x3a01a80f3203ccf8

def z210 : W := mkw 0x0000000000000000 0x0000000000000000 0x200031c7e0000002 0x04000638fc000000

def z211 : W := mkw 0x37da7bac1eeb05f7 0x86fb4f7583dd60be 0xfffc7fb81fee07fe 0xffff8ff703fdc0ff

def z212 : W := mkw 0x0450000002400000 0x008a000000480000 0x0870000007e00000 0x810e000000fc0000

def z213 : W := mkw 0x120a006e001b8249 0x8241400dc0037049 0xd00e407e101f87c7 0x3a01c80fc203f0f8

def z214 : W := mkw 0x04758d1140000000 0x008eb1a228000000 0x00600e0000000000 0x000c01c000000000

def z215 : W := mkw 0x06da80001b4d5000 0x00db50000369aa00 0x1f9280001ffff804 0x43f2500003ffff00

def z216 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x17822006181f87fc 0x42f04400c303f0ff

def z217 : W := mkw 0x2c751f9187e46496 0x458ea3f230fc8c92 0x28711f8187e06000 0x850e23f030fc0c00

def z218 : W := mkw 0x0000000000000000 0x0000000000000000 0x881380000c71f805 0xd1027000018e3f00

def z219 : W := mkw 0x04d000001a400000 0x009a000003480000 0x17e0000013800000 0x22fc000002700000

def z220 : W := mkw 0x27fffb801fed55b6 0x04ffff7003fdaab6 0xfffc7f801fee07fe 0xffff8ff003fdc0ff

def z221 : W := mkw 0x0000104084102600 0x00000208108204c0 0x0800000004106604 0x0100000000820cc0

def z222 : W := mkw 0x06da80001a491000 0x00db500003492200 0x9ff280001fe19804 0xf3fe500003fc3300

def z223 : W := mkw 0x25d07bc09ef027b6 0x04ba0f7813de04f6 0xfff17fc19ff067ff 0xfffe2ff833fe0cff

def z224 : W := mkw 0x022f90c2a53dfe1c 0x2045f21854a7bfc3 0xa81fb1c7ec7ffe3f 0xd503f638fd8fffc7

def z225 : W := mkw 0x2ffffffddff667f7 0x45ffffffbbfeccfe 0xfffffffffffe67ff 0xffffffffffffccff

def z226 : W := mkw 0x338a72ee1efb87ff 0x86714e5dc3df70ff 0xdf8e607e1fff87ff 0x7bf1cc0fc3fff0ff

def z227 : W := mkw 0x0a2f967dc59666c1 0x4145f2cfb8b2ccd8 0xf86fde7ff79e67c7 0xbf0dfbcffef3ccf8

def z228 : W := mkw 0x0475800003445000 0x008eb00000688a00 0x987d800017fe7805 0xb30fb00002ffcf00

def z229 : W := mkw 0x0180604818120361 0x00300c090302406c 0xd78c6078181e07ff 0x7af18c0f0303c0ff

def z230 : W := mkw 0x000000c220308a1c 0x2000001844061143 0x8012a1c668719e3f 0x50025438cd0e33c7

def z231 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x77e07f80138007fa 0x2efc0ff0027000ff

def z232 : W := mkw 0x075ae92440000000 0x00eb5d2488000000 0x0780000000000000 0x00f0000000000000

def z233 : W := mkw 0x0000004200108208 0x0000000840021041 0xa013b1c7e811863f 0xd4027638fd0230c7

def z234 : W := mkw 0x25d07bc2bef0afbe 0x24ba0f7857de15f7 0xfff07f801ff1fffe 0xfffe0ff003fe3fff

def z235 : W := mkw 0x37fffbee1fffd7ff 0x86ffff7dc3fffaff 0xfffffffe1fffffff 0xffffffffc3ffffff

def z236 : W := mkw 0x0b2f767d859666c1 0x4165eecfb0b2ccd8 0xffef7e7f979e67c7 0xfffdefcff2f3ccf8

def z237 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x586c4e38179e67c4 0x2b0d89c702f3ccf8

def z238 : W := mkw 0x020a000000000000 0x0041400000000000 0x878e000000000001 0x70f1c00000000000

def z239 : W := mkw 0x1180606e18128369 0x82300c0dc302506d 0xd780607e180007fe 0x7af00c0fc30000ff

def z240 : W := mkw 0x0825041181046000 0x4104a08230208c00 0x0001000180006000 0x0000200030000c00

def z241 : W := mkw 0x1fffff7fdd9fe7e9 0xc3ffffeffbb3fcfd 0xffffffffff9fe7ff 0xfffffffffff3fcff

def z242 : W := mkw 0x0825045ba116ea49 0x6104a08b7422dd49 0x000f807fe01ff801 0x0001f00ffc03ff00

def z243 : W := mkw 0x25d07b001ec005a2 0x04ba0f6003d800b4 0xffe05e00178007c6 0xbffc0bc002f000f8

def z244 : W := mkw 0x0000108004200414 0x0000021000840082 0xa813b1c7ec60063f 0xd5027638fd8c00c7

def z245 : W := mkw 0x138a602418090120 0x82714c0483012024 0x0780000000000000 0x00f0000000000000

def z246 : W := mkw 0x000000822020881c 0x2000001044041103 0x8813a1866c71f83d 0xd1027430cd8e3f07

def z247 : W := mkw 0x06ff8d115b4d5000 0x00dff1a22b69aa00 0xbfff9f81fffff805 0xf7fff3f03fffff00

def z248 : W := mkw 0x0c759f59c59666c1 0x418eb3eb38b2ccd8 0xf87ddff9f79e67c7 0xbf0fbbff3ef3ccf8

def z249 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x079f8000087ff801 0x40f3f000010fff00

def z250 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1ffd800017ee7800 0xa3ffb00002fdcf00

def z251 : W := mkw 0x008000001a400000 0x0010000003480000 0x180000001fe00004 0x0300000003fc0000

def z252 : W := mkw 0x00000d1140000000 0x000001a228000000 0x20001f81e0000000 0x040003f03c000000

def z253 : W := mkw 0x06ff84111b4d5000 0x00dff0822369aa00 0xffffde799ffff807 0xfffffbcf33ffff00

def z254 : W := mkw 0x0d757f59859666c1 0x41aeafeb30b2ccd8 0xfffd7ff9979e67c7 0xffffafff32f3ccf8

def z255 : W := mkw 0x07fffdf7ff7dfe1c 0x20ffffbeffefbfc3 0xfffffffffffffe3f 0xffffffffffffffc7

def z256 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x200031c7e000063a 0x04000638fc0000c7

def z257 : W := mkw 0x0000000000000000 0x0000000000000000 0xa001104180000003 0x9400220830000000

def z258 : W := mkw 0x0000008000200014 0x0000001000040002 0x0010218008600038 0x40020430010c0007

def z259 : W := mkw 0x0000043540000000 0x00000086a8000000 0x0000007fe0000000 0x0000000ffc000000

def z260 : W := mkw 0x077fed35410d5000 0x00effda6a821aa00 0xe7ffffffe01ff803 0xfcfffffffc03ff00

def z261 : W := mkw 0x030a602400000000 0x00614c0480000000 0x478c403800000000 0x28f1880700000000

def z262 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0xd7e06e001b8007fe 0x7afc0dc0037000ff

def z263 : W := mkw 0x29257fd985b667f7 0x4524affb30b6ccfe 0xf86d7ff9979e67ff 0xbf0dafff32f3ccff

def z264 : W := mkw 0x108010cabc3baf7d 0xa2100219578775ef 0xb813b1c7fc7fffff 0xd7027638ff8fffff

def z265 : W := mkw 0x0f7fffffe5b6eedd 0x61effffffcb6dddb 0xffffffffffffffff 0xffffffffffffffff

def z266 : W := mkw 0x25d079801e600536 0x04ba0f3003cc00a6 0xaf9031800c60063e 0xd5f20630018c00c7

def z267 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86d7ffff79e67ff 0xbf0daffffef3ccff

def z268 : W := mkw 0x080016dba4b2aedd 0x610002db749655db 0xe813ffffec71ffff 0xdd027ffffd8e3fff

def z269 : W := mkw 0x0000004200108208 0x0000000840021041 0x8813a0460c71fe3f 0xd1027408c18e3fc7

def z270 : W := mkw 0x08001248859666c1 0x4100024910b2ccd8 0xf8605e00179e67c6 0xbf0c0bc002f3ccf8

def z271 : W := mkw 0x0000000000000000 0x0000000000000000 0x080000000c71f804 0x01000000018e3f00

def z272 : W := mkw 0x06da80001a491000 0x00db500003492200 0x0792800008619800 0x40f25000010c3300

def z273 : W := mkw 0x075ae92440000000 0x00eb5d2488000000 0xe7f2ff8660000002 0xfcfe5ff0cc000000

def z274 : W := mkw 0x0180600018000120 0x00300c0003000024 0x57804000100001c0 0x2af0080002000038

def z275 : W := mkw 0x077ffdb544200414 0x00efffb6a8840082 0xefffffffec60063f 0xfdfffffffd8c00c7

def z276 : W := mkw 0x0475800003445000 0x008eb00000688a00 0x0060000003800000 0x000c000000700000

def z277 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86d5e799fffffff 0xbf0dabcf33ffffff

def z278 : W := mkw 0x067f90c2a430ae1c 0x20cff218548615c3 0xafffb1c7ec71fe3f 0xf5fff638fd8e3fc7

def z279 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x2012b1c7e8619e3a 0x44025638fd0c33c7

def z280 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xf79ff1fff81f87ff 0xfef3fe3fff03f0ff

def z281 : W := mkw 0x29007fd984b227f7 0x45200ffb309644fe 0x60007ff9800007fa 0x0c000fff300000ff

def z282 : W := mkw 0x00000000a0002800 0x2000000014000500 0x00018001e0007800 0x000030003c000f00

def z283 : W := mkw 0x06ff800018090000 0x00dff00003012000 0x97ff8000181f8005 0xf2fff0000303f000

def z284 : W := mkw 0x25d07b80bee02db6 0x24ba0f7017dc05b6 0xfff1ff81ffe07ffe 0xfffe3ff03ffc0fff

def z285 : W := mkw 0x0c75961187c47480 0x418eb2c230f88e90 0x28719e0187e07800 0x850e33c030fc0f00

def z286 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x97ff8000138e0001 0xf2fff0000271c000

def z287 : W := mkw 0x06da80001a491000 0x00db500003492200 0x8f9380000c71f805 0xd1f27000018e3f00

def z288 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff3ff801ff1ffff 0xfffe7ff003fe3fff

def z289 : W := mkw 0x1900767f8492a7e9 0xc3200ecff09254fd 0x60007e7f800007fa 0x0c000fcff00000ff

def z290 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x5fe04e001fe007fc 0x2bfc09c003fc00ff

def z291 : W := mkw 0x0f7fff7dc49226c1 0x41efffefb89244d8 0xe7ffffffe00007c3 0xfcfffffffc0000f8

def z292 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87ffffff79e67c7 0xff0ffffffef3ccf8

def z293 : W := mkw 0x21807b801ca005b6 0x04300f70039400b6 0xf7807f80180007fe 0x7ef00ff0030000ff

def z294 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x600d5e79801e67c3 0x0c01abcf3003ccf8

def z295 : W := mkw 0x08000208018640c1 0x410000410030c818 0x10000000138e01c0 0x020000000271c038

def z296 : W := mkw 0x10800008180b0161 0x821000010301602c 0x10000000100e01c0 0x020000000201c038

def z297 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x27f3bf87e0000000 0xc4fe77f0fc000000

def z298 : W := mkw 0x0f7fef3d418640c1 0x41effde7a830c818 0x57ec4e38138e01c0 0x2afd89c70271c038

def z299 : W := mkw 0x17ffed3758098128 0x82fffda6eb013025 0xe7ffffffe801803b 0xfcfffffffd003007

def z300 : W := mkw 0x000000c2a030aa1c 0x2000001854061543 0x0013a1c7e871f839 0x40027438fd0e3f07

def z301 : W := mkw 0x16ff806e1b5fd249 0x82dff00dc36bfa49 0x9fff807e1ffff805 0xf3fff00fc3ffff00

def z302 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87fde799fffffc7 0xff0ffbcf33fffff8

def z303 : W := mkw 0x208012801ee005b6 0x0410025003dc00b6 0xb81031801fe007fe 0xd702063003fc00ff

def z304 : W := mkw 0x06ff90801f6d5414 0x00dff21003edaa82 0xbfffb1801ffffe3f 0xf7fff63003ffffc7

def z305 : W := mkw 0x138a602618098128 0x82714c04c3013025 0x978e2006181f803d 0x72f1c400c303f007

def z306 : W := mkw 0x13afe06e191fd369 0x8275fc0dc323fa6d 0xd78fe07e181fffff 0x7af1fc0fc303ffff

def z307 : W := mkw 0x17dae96e581b8369 0x82fb5d2dcb03706d 0xd79ee1fe781f87ff 0x7af3dc3fcf03f0ff

def z308 : W := mkw 0x04f580001b445000 0x009eb00003688a00 0x9ff180001fe07804 0xf3fe300003fc0f00

def z309 : W := mkw 0x26ff9b801fed5496 0x04dff37003fdaa92 0xbfff9f801ffff805 0xf7fff3f003ffff00

def z310 : W := mkw 0x25d07b823ee08dbe 0x24ba0f7047dc11b7 0xfff2ff867fe19ffe 0xfffe5ff0cffc33ff

def z311 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x47efce7fe0000001 0x28fdf9cffc000000

def z312 : W := mkw 0x0825165ba596eec9 0x6104a2cb74b2ddd9 0xf86fde7ff79fffc7 0xbf0dfbcffef3fff8

def z313 : W := mkw 0x0025041100000000 0x0004a08220000000 0x000d007980000001 0x0001a00f30000000

def z314 : W := mkw 0x06ff8042bb5dfa08 0x20dff008576bbf41 0x9fff8047fffff805 0xf3fff008ffffff00

def z315 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xa81031800c71fe3e 0xd5020630018e3fc7

def z316 : W := mkw 0x07ffe0001b4d5120 0x00fffc000369aa24 0xdfffe0001fffffff 0xfbfffc0003ffffff

def z317 : W := mkw 0x1100606e00128369 0x82200c0dc002506d 0xd00c607e101e07ff 0x3a018c0fc203c0ff

def z318 : W := mkw 0x1000006e00128249 0x8200000dc0025049 0x0000007e00000000 0x0000000fc0000000

def z319 : W := mkw 0x0c759f11c5846480 0x418eb3e238b08c90 0x28719f81e7806000 0x850e33f03cf00c00

def z320 : W := mkw 0x0000000000000000 0x0000000000000000 0xa010318000000002 0xd402063000000000

def z321 : W := mkw 0x0000004200108208 0x0000000840021041 0x000000000811863c 0x00000000010230c7

def z322 : W := mkw 0x0eff86191bcf50c1 0x41dff0c32379ea18 0xdfffce381ffff9c5 0xfbfff9c703ffff38

def z323 : W := mkw 0x06da80001a491000 0x00db500003492200 0x979e8000187f9805 0x72f3d000030ff300

def z324 : W := mkw 0x0550690000000000 0x00aa0d2000000000 0x47e04e0000000000 0x28fc09c000000000

def z325 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x97ee00001b9f8005 0x72fdc0000373f000

def z326 : W := mkw 0x08001248849226c1 0x41000249109244d8 0x00000000000007c0 0x00000000000000f8

def z327 : W := mkw 0x17ffe06e1b5fd369 0x82fffc0dc36bfa6d 0xdfffe07e1fffffff 0xfbfffc0fc3ffffff

def z328 : W := mkw 0x022f8000010d5000 0x0045f0000021aa00 0x986f8000179ff805 0xb30df00002f3ff00

def z329 : W := mkw 0x0cf516599fd666c1 0x419ea2cb33faccd8 0xfffd5e799ffe67c7 0xffffabcf33ffccf8

def z330 : W := mkw 0x17da606e1a5b8369 0x82fb4c0dc34b706d 0xdffe607e1fff87ff 0xfbffcc0fc3fff0ff

def z331 : W := mkw 0x37ffffff5efb87ff 0x86ffffffebdf70ff 0xffffffffffff87ff 0xfffffffffffff0ff

def z332 : W := mkw 0x1a2f047f811fe249 0xc345e08ff023fc49 0x000f007f801fe001 0x0001e00ff003fc00

def z333 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z334 : W := mkw 0x2450098002600016 0x048a0130004c0002 0x0010018000600000 0x00020030000c0000

def z335 : W := mkw 0x0025041100000000 0x0004a08220000000 0x406c4e3800000000 0x280d89c700000000

def z336 : W := mkw 0x138a606618198328 0x82714c0cc3033065 0x878220460811863f 0x50f04408c10230c7

def z337 : W := mkw 0x00001248049206c1 0x00000249009240d8 0xf86c5e78179e07c7 0xbf0d8bcf02f3c0f8

def z338 : W := mkw 0x1000004a00128369 0x820000094002506d 0x00000000000007f8 0x00000000000000ff

def z339 : W := mkw 0x000010caa432ae5d 0x20000219548655cb 0xf81ff1fffc7fffff 0xff03fe3fff8fffff

def z340 : W := mkw 0x27ffedb55a600136 0x04fffdb6ab4c0026 0xe7ffffffe860003b 0xfcfffffffd0c0007

def z341 : W := mkw 0x0000000000000000 0x0000000000000000 0x0012800008619800 0x40025000010c3300

def z342 : W := mkw 0x08251691a5a46c94 0x6104a2d234b48d92 0x28719f81e7e07800 0x850e33f03cfc0f00

def z343 : W := mkw 0x028a10c2bc39ae1c 0x20514218578735c3 0xbf9fb1c7fc7ffe3f 0xf7f3f638ff8fffc7

def z344 : W := mkw 0x37da69ee1a7b837f 0x86fb4d3dc34f706f 0xd79e61fe187f87ff 0x7af3cc3fc30ff0ff

def z345 : W := mkw 0x21006b00008001a2 0x04200d6000100034 0x40004e00000001c0 0x080009c000000038

def z346 : W := mkw 0x0000000800020041 0x0000000100004008 0x500c4038100e01c0 0x2a0188070201c038

def z347 : W := mkw 0x00000042a010aa08 0x2000000854021541 0x8003a047e811fe3f 0x50007408fd023fc7

def z348 : W := mkw 0x07ffed355b4d5000 0x00fffda6ab69aa00 0xdfffce381ffff805 0xfbfff9c703ffff00

def z349 : W := mkw 0x06da80001a491000 0x00db500003492200 0x0780000000000000 0x00f0000000000000

def z350 : W := mkw 0x022f800000000000 0x0045f00000000000 0x000f800000000001 0x0001f00000000000

def z351 : W := mkw 0x020a002400000000 0x0041400480000000 0x000e007e00000001 0x0001c00fc0000000

def z352 : W := mkw 0x080016dba4b2aedd 0x610002db749655db 0x60007fffe00007fa 0x0c000ffffc0000ff

def z353 : W := mkw 0x077fed3541044000 0x00effda6a8208800 0xfffffffff79e6007 0xfffffffffef3cc00

def z354 : W := mkw 0x138a602e180b8169 0x82714c05c301702d 0x578e603e180f81f8 0x6af1cc07c301f03f

def z355 : W := mkw 0x0a2f847dc1166241 0x4145f08fb822cc48 0x000f807fe01e6001 0x0001f00ffc03cc00

def z356 : W := mkw 0x128a006e181b8369 0x8251400dc303706d 0x100e007e181f87fd 0x0201c00fc303f0ff

def z357 : W := mkw 0x25d079c2be70af3e 0x24ba0f3857ce15e7 0xaf93b1c7ec71fe3f 0xd5f27638fd8e3fc7

def z358 : W := mkw 0x0025000001044000 0x0004a00000208800 0x987f80001ffff805 0xf30ff00003ffff00

def z359 : W := mkw 0x0000120004800480 0x0000024000900090 0x28601e0007800000 0x850c03c000f00000

def z360 : W := mkw 0x138a70ee1c3b877d 0x82714e1dc38770ef 0xff9e71fe1c7f87ff 0xfff3ce3fc38ff0ff

def z361 : W := mkw 0x07ffe9245b4d5000 0x00fffd248b69aa00 0x9fffa1867ffff805 0xf3fff430cfffff00

def z362 : W := mkw 0x138a70e6bc39af3c 0xa2714e1cd78735e7 0xaf93b1c7ec71fe3f 0xd5f27638fd8e3fc7

def z363 : W := mkw 0x0000000220008808 0x2000000044001101 0x0002800660019800 0x00005000cc003300

def z364 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578e407e101f81c1 0x2af1c80fc203f038

def z365 : W := mkw 0x067f8d1140000000 0x00cff1a228000000 0xa7ff9f81e0000001 0xf4fff3f03c000000

def z366 : W := mkw 0x0180600018000120 0x00300c0003000024 0x0780200008000038 0x40f0040001000007

def z367 : W := mkw 0x17ffed3d580b0161 0x82fffda7ab01602c 0x57ec4e38100e01c0 0x2afd89c70201c038

def z368 : W := mkw 0x3fff7fff9fffe7ff 0xc7ffeffff3fffcff 0xffff7fff9fffe7ff 0xffffeffff3fffcff

def z369 : W := mkw 0x138a70eebc3baf7d 0xa2714e1dd78775ef 0xdf8e607e1c7fffff 0x7bf1cc0fc38fffff

def z370 : W := mkw 0x04d000001b4d5000 0x009a00000369aa00 0x9ff000001ffff804 0xf3fe000003ffff00

def z371 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x2ff03f800fe00038 0xc5fe07f001fc0007

def z372 : W := mkw 0x077ffd75c4102600 0x00efffaeb88204c0 0xefffffffe4106607 0xfdfffffffc820cc0

def z373 : W := mkw 0x25d069801a600136 0x04ba0d30034c0026 0x9ff021801fe0003c 0xf3fe043003fc0007

def z374 : W := mkw 0x09007f7dc49226c1 0x41200fefb89244d8 0x60007fffe00007c2 0x0c000ffffc0000f8

def z375 : W := mkw 0x0550690000000000 0x00aa0d2000000000 0x0790218000000000 0x40f2043000000000

def z376 : W := mkw 0x0100600000000000 0x00200c0000000000 0xc780600000000002 0x78f00c0000000000

def z377 : W := mkw 0x0eff96119fcd7480 0x41dff2c233f9ae90 0xbfff9e019ffff805 0xf7fff3c033ffff00

def z378 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ed5e7980000003 0xbcfdabcf30000000

def z379 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xc7ee6e7e00000003 0x78fdcdcfc0000000

def z380 : W := mkw 0x17ffe02c1b4f5161 0x82fffc058369ea2c 0x57ec4038138e01c0 0x2afd88070271c038

def z381 : W := mkw 0x028a00001b4d5000 0x005140000369aa00 0x9f8e00001ffff805 0x73f1c00003ffff00

def z382 : W := mkw 0x1080004a181b8369 0x821000094303706d 0x90022046181f87ff 0x52004408c303f0ff

def z383 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x4782607e080187fa 0x48f04c0fc10030ff

def z384 : W := mkw 0x277fffb546e00496 0x04effff6a8dc0092 0xefffffffe7e00003 0xfdfffffffcfc0000

def z385 : W := mkw 0x0800045980122241 0x4100008b30024448 0x0000007980000000 0x0000000f30000000

def z386 : W := mkw 0x110070eea432af7d 0xa2200e1dd48655ef 0xe813f1ffec71ffff 0xdd027e3ffd8e3fff

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00c407800000003 0x3801880f00000000

def z388 : W := mkw 0x05507b0004800480 0x00aa0f6000900090 0xfff07f80178007c6 0xfffe0ff002f000f8

def z389 : W := mkw 0x077fed7740108208 0x00effdaee8021041 0xe7ffffffe811863f 0xfcfffffffd0230c7

def z390 : W := mkw 0x0c75965987d676c1 0x418eb2cb30faced8 0xf87dde7997fe7fc7 0xbf0fbbcf32ffcff8

def z391 : W := mkw 0x04758d1140000000 0x008eb1a228000000 0xe07ddff9e0000003 0xbc0fbbff3c000000

def z392 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578c4038181f87fc 0x2af188070303f0ff

def z393 : W := mkw 0x0000100004000400 0x0000020000800080 0xa800100004000606 0x95000200008000c0

def z394 : W := mkw 0x022f94f7e430ae1c 0x2045f29efc8615c3 0xa81fb1ffec71fe3f 0xd503f63ffd8e3fc7

def z395 : W := mkw 0x0825045981166241 0x4104a08b3022cc48 0xe06d5e79801e6003 0xbc0dabcf3003cc00

def z396 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fed0000179e6005 0xb3fda00002f3cc00

def z397 : W := mkw 0x04d000001a400000 0x009a000003480000 0x0790000008600000 0x40f20000010c0000

def z398 : W := mkw 0x0025000001044000 0x0004a00000208800 0x0861000007806000 0x810c200000f00c00

def z399 : W := mkw 0x0000108004200414 0x0000021000840082 0x2810118004600000 0x85020230008c0000

def z400 : W := mkw 0x008010c2bf7dfe1c 0x2010021857efbfc3 0xb813b1c7fffffe3f 0xd7027638ffffffc7

def z401 : W := mkw 0x2fffffd99fff77f7 0x45fffffb33ffeefe 0xfffffff99fffffff 0xffffffff33ffffff

def z402 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xa80131c7e410663f 0x95002638fc820cc7

def z403 : W := mkw 0x05d060001a400120 0x00ba0c0003480024 0xdff060001fe007fe 0xfbfe0c0003fc00ff

def z404 : W := mkw 0x24d01b801ee005b6 0x049a037003dc00b6 0x38701f801fe007fc 0x870e03f003fc00ff

def z405 : W := mkw 0x0000041100000000 0x0000008220000000 0x60005e7980000002 0x0c000bcf30000000

def z406 : W := mkw 0x17dae92658098128 0x82fb5d24cb013025 0x0792a18668018038 0x40f25430cd003007

def z407 : W := mkw 0x075ae92440000000 0x00eb5d2488000000 0xa793b1c7e0000003 0xd4f27638fc000000

def z408 : W := mkw 0x128a006e181b8249 0x8251400dc3037049 0x978e007e181f8005 0x72f1c00fc303f000

def z409 : W := mkw 0x028a004218198208 0x0051400843033041 0x978e2046181f863f 0x72f1c408c303f0c7

def z410 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x2003b1c7e011fe3b 0x04007638fc023fc7

def z411 : W := mkw 0x067f800000000000 0x00cff00000000000 0xa7ffb1c7e0000003 0xf4fff638fc000000

def z412 : W := mkw 0x21007bc2a4b0afbe 0x24200f78549615f7 0x60007fc7e00007fa 0x0c000ff8fc0000ff

def z413 : W := mkw 0x020a000000090000 0x0041400000012000 0x000e0000001f8001 0x0001c0000003f000

def z414 : W := mkw 0x27dafba45ee005b6 0x04fb5f748bdc00b6 0xfff2ff867fe007fe 0xfffe5ff0cffc00ff

def z415 : W := mkw 0x21007fb544a005b6 0x04200ff6a89400b6 0x60007fffe00007fa 0x0c000ffffc0000ff

def z416 : W := mkw 0x120a002c000b0041 0x8241400580016008 0x000c0038000e0000 0x000180070001c000

def z417 : W := mkw 0x067f841100000000 0x00cff08220000000 0xe7ffde7980000003 0xfcfffbcf30000000

def z418 : W := mkw 0x0825161185846480 0x4104a2c230b08c90 0xb86d1e01979e6005 0xb70da3c032f3cc00

def z419 : W := mkw 0x032fe43540000000 0x0065fc86a8000000 0xc78fe07fe0000003 0x78f1fc0ffc000000

def z420 : W := mkw 0x1100602c00020161 0x82200c058000402c 0x40004038000001c0 0x0800080700000038

def z421 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xa80110418c71fe3f 0x95002208318e3fc7

def z422 : W := mkw 0x2dd07bc89ff667f7 0x45ba0f7913feccfe 0xfff07f801ffe67fe 0xfffe0ff003ffccff

def z423 : W := mkw 0x0025041101044000 0x0004a08220208800 0xf86d5e79979e6007 0xbf0dabcf32f3cc00

def z424 : W := mkw 0x128a004a181b8369 0x825140094303706d 0x978e0000181f87fd 0x72f1c0000303f0ff

def z425 : W := mkw 0x25d07fb55ee005b6 0x04ba0ff6abdc00b6 0xfff07fffffe007fe 0xfffe0ffffffc00ff

def z426 : W := mkw 0x0025000001044000 0x0004a00000208800 0x106c0000138e0000 0x220d80000271c000

def z427 : W := mkw 0x17da696e181b8369 0x82fb4d2dc303706d 0xf7fe7ffe181f87ff 0xfeffcfffc303f0ff

def z428 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xefffffffec71f807 0xfdfffffffd8e3f00

def z429 : W := mkw 0x0100692440000000 0x00200d2488000000 0x0000218660000000 0x00000430cc000000

def z430 : W := mkw 0x21007b8004a005b6 0x04200f70009400b6 0xf8607f80178007fe 0xbf0c0ff002f000ff

def z431 : W := mkw 0x077fe90000000000 0x00effd2000000000 0xe7ffff8000000003 0xfcfffff000000000

def z432 : W := mkw 0x0450090000000000 0x008a012000000000 0x20701f8000000000 0x840e03f000000000

def z433 : W := mkw 0x0000000000000000 0x0000000000000000 0x00038047e0000001 0x00007008fc000000

def z434 : W := mkw 0x0f7fed7dc1166241 0x41effdafb822cc48 0xe7ffffffe01e6003 0xfcfffffffc03cc00

def z435 : W := mkw 0x06da00001a490000 0x00db400003492000 0x9ffe00001fff8005 0xf3ffc00003fff000

def z436 : W := mkw 0x01006d3540000000 0x00200da6a8000000 0x40004e3800000000 0x080009c700000000

def z437 : W := mkw 0x108010cabc3baf7d 0xa2100219578775ef 0x180000001c7ffffc 0x03000000038fffff

def z438 : W := mkw 0x0025000000000000 0x0004a00000000000 0x806d000000000001 0xb00da00000000000

def z439 : W := mkw 0x075af9e6e430ae1c 0x20eb5f3cdc8615c3 0xaf93b1c7ec71fe3f 0xd5f27638fd8e3fc7

def z440 : W := mkw 0x06da80823a69981c 0x20db5010474d3303 0x0792a18668619838 0x40f25430cd0c3307

def z441 : W := mkw 0x08000619008200c1 0x410000c320104018 0x40004e38000001c0 0x080009c700000038

def z442 : W := mkw 0x2df57f599fd667e3 0x45beafeb33faccfc 0xffed5e79979e67c7 0xbffdabcf32f3ccf8

def z443 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xa81031c7ec60063e 0xd5020638fd8c00c7

def z444 : W := mkw 0x0000020000800080 0x0000004000100010 0x50604e00138001c0 0x2a0c09c002700038

def z445 : W := mkw 0x37da6b6e1adb83eb 0x86fb4d6dc35b707d 0xd7ee6e7e1b9f87ff 0x7afdcdcfc373f0ff

def z446 : W := mkw 0x0025145184102600 0x0004a28a308204c0 0xe86d5e7984106607 0xbd0dabcf30820cc0

def z447 : W := mkw 0x082516d9a5b66ed5 0x6104a2db34b6cdda 0xf87ddff9f7fe7fc7 0xbf0fbbff3effcff8

def z448 : W := mkw 0x24501b8006e00496 0x048a037000dc0092 0xa8703f800fe0063e 0xd50e07f001fc00c7

def z449 : W := mkw 0x0000004000100200 0x0000000800020040 0x8000004000100607 0x10000008000200c0

def z450 : W := mkw 0x2000128004a005b6 0x04000250009400b6 0x00000000000007f8 0x00000000000000ff

def z451 : W := mkw 0x0025800001045000 0x0004b00000208a00 0x0001800000007800 0x0000300000000f00

def z452 : W := mkw 0x04759dd3e430ae1c 0x208eb3ba7c8615c3 0xa873bfc7ec71fe3f 0xd50e77f8fd8e3fc7

def z453 : W := mkw 0x0000000200008008 0x0000000040001001 0x0002200608018038 0x40004400c1003007

def z454 : W := mkw 0x04d010c2be70ae1c 0x209a021857ce15c3 0xbff3b1c7fff1fe3f 0xf7fe7638fffe3fc7

def z455 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0xf7f07f80138001c2 0xfefe0ff002700038

def z456 : W := mkw 0x07ffe0241b4d5000 0x00fffc048369aa00 0xdfffe07e1ffff807 0xfbfffc0fc3ffff00

def z457 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1fec00001ffff804 0x23fd800003ffff00

def z458 : W := mkw 0x130a606e001b8369 0x82614c0dc003706d 0x400e607e001f87fb 0x0801cc0fc003f0ff

def z459 : W := mkw 0x0000004a00128249 0x0000000940025049 0xd00e607e181f87ff 0x7a01cc0fc303f0ff

def z460 : W := mkw 0x07ffed355a400000 0x00fffda6ab480000 0xffffffffffe00007 0xfffffffffffc0000

def z461 : W := mkw 0x000010c0a4302e14 0x20000218148605c2 0xa81191c1e4707e07 0x950232383c8e0fc0

def z462 : W := mkw 0x0825041901064041 0x4104a0832020c808 0x000c0038000e0000 0x000180070001c000

def z463 : W := mkw 0x0825165185946680 0x4104a2ca30b28cd0 0xa8611e4187906607 0x950c23c830f20cc0

def z464 : W := mkw 0x030a602400000000 0x00614c0480000000 0x0782200600000000 0x40f04400c0000000

def z465 : W := mkw 0x0000004800120241 0x0000000900024048 0x10000000101e07c4 0x020000000203c0f8

def z466 : W := mkw 0x0000000000000000 0x0000000000000000 0x8801000004106005 0x9100200000820c00

def z467 : W := mkw 0x138a602618098128 0x82714c04c3013025 0xc78e607e0801803b 0x78f1cc0fc1003007

def z468 : W := mkw 0x0000000000000000 0x0000000000000000 0x000380000011f801 0x0000700000023f00

def z469 : W := mkw 0x120a006ea01baa49 0xa241400dd4037549 0x000f807fe01ff801 0x0001f00ffc03ff00

def z470 : W := mkw 0x208012801fed55b6 0x0410025003fdaab6 0x180000001ffffffc 0x0300000003ffffff

def z471 : W := mkw 0x022f843540000000 0x0045f086a8000000 0xe06fde7fe0000003 0xbc0dfbcffc000000

def z472 : W := mkw 0x067f8d3540000000 0x00cff1a6a8000000 0x207f9fffe0000001 0x840ff3fffc000000

def z473 : W := mkw 0x0025041100000000 0x0004a08220000000 0x20611e0180000000 0x840c23c030000000

def z474 : W := mkw 0x04f580001b4d5000 0x009eb0000369aa00 0x187180001ffff804 0x830e300003ffff00

def z475 : W := mkw 0x06ff80823b6dd81c 0x20dff010476dbb03 0x9fffa1867ffff83d 0xf3fff430cfffff07

def z476 : W := mkw 0x25507b8004a005b6 0x04aa0f70009400b6 0xe7f07f80000007fa 0xfcfe0ff0000000ff

def z477 : W := mkw 0x27fffb801ee005b6 0x04ffff7003dc00b6 0xffffff801fe007ff 0xfffffff003fc00ff

def z478 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x0812a1866c71fe3c 0x41025430cd8e3fc7

def z479 : W := mkw 0x0025161104800480 0x0004a2c220900090 0xf86d5e79978007c7 0xbf0dabcf32f000f8

def z480 : W := mkw 0x06ff9080bf6d7c14 0x20dff21017edaf82 0xbfff9181fffff805 0xf7fff2303fffff00

def z481 : W := mkw 0x0100602400000000 0x00200c0480000000 0x4000607e00000002 0x08000c0fc0000000

def z482 : W := mkw 0x028a000018090000 0x0051400003012000 0x0782000008018000 0x40f0400001003000

def z483 : W := mkw 0x27ffef355ac001a2 0x04fffde6ab580034 0x57ec4e38138001c0 0x2afd89c702700038

def z484 : W := mkw 0x28a516d99ff667f7 0x4514a2db33feccfe 0xf86d5e799ffe67ff 0xbf0dabcf33ffccff

def z485 : W := mkw 0x0fffff7ddfdf76c1 0x41ffffefbbfbeed8 0xffffffffffffffc7 0xfffffffffffffff8

def z486 : W := mkw 0x0000000000000000 0x0000000000000000 0x0012a18660000000 0x40025430cc000000

def z487 : W := mkw 0x022f8000010d5000 0x0045f0000021aa00 0x881f80000c7ff805 0xd103f000018fff00

def z488 : W := mkw 0x0025000001044000 0x0004a00000208800 0x000d0000001e6001 0x0001a0000003cc00

def z489 : W := mkw 0x25f57f911ee005b6 0x04beaff223dc00b6 0xfffd7ff99fe007ff 0xffffafff33fc00ff

def z490 : W := mkw 0x030a70e6a430ae1c 0x20614e1cd48615c3 0xef9ff1ffec71fe3f 0xfdf3fe3ffd8e3fc7

def z491 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9ffc00001fee0004 0xf3ff800003fdc000

def z492 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x1f9021801fe007fc 0x43f2043003fc00ff

def z493 : W := mkw 0x077fed77e010aa08 0x20effdaefc021541 0xe7ffffffe011f803 0xfcfffffffc023f00

def z494 : W := mkw 0x02af8000190d5000 0x0055f0000321aa00 0x978f8000181ff805 0x72f1f0000303ff00

def z495 : W := mkw 0x120a006e001b8249 0x8241400dc0037049 0x800e207e081f863f 0x5001c40fc103f0c7

def z496 : W := mkw 0x0000000000000000 0x0000000000000000 0x881000000c600004 0xd1020000018c0000

def z497 : W := mkw 0x25d06b801ae001b6 0x04ba0d70035c0036 0x57f06f801be001f8 0x6afe0df0037c003f

def z498 : W := mkw 0x018070c2bc30af3c 0x20300e18578615e7 0xff93f1c7fc71ffff 0xfff27e38ff8e3fff

def z499 : W := mkw 0x0575ed1140000000 0x00aebda228000000 0xe7f1ff81e0000002 0xfcfe3ff03c000000

def z500 : W := mkw 0x047590c2a774fe1c 0x208eb21854ee9fc3 0xa873b1c7eff1fe3f 0xd50e7638fdfe3fc7

def z501 : W := mkw 0x077ffdf7e430ae1c 0x20efffbefc8615c3 0xe7ffffffe000063b 0xfcfffffffc0000c7

def z502 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0xd78e4038181f81c5 0x7af1c8070303f038

def z503 : W := mkw 0x00001080a4202c14 0x2000021014840582 0x0800000004607800 0x01000000008c0f00

def z504 : W := mkw 0x21007bc2a4b0afbe 0x24200f78549615f7 0xe813ffc7ec71ffff 0xdd027ff8fd8e3fff

def z505 : W := mkw 0x030a606c00120241 0x00614c0d80024048 0xd78e607e101e07c7 0x7af1cc0fc203c0f8

def z506 : W := mkw 0x130a606e001b8249 0x82614c0dc0037049 0xc78e607e001f8003 0x78f1cc0fc003f000

def z507 : W := mkw 0x1baf663d198f41e1 0xc375ecc7a331e83c 0x57ec4e38138e01c0 0x2afd89c70271c038

def z508 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0xdff04e001fe001c4 0xfbfe09c003fc0038

def z509 : W := mkw 0x04f500001b444000 0x009ea00003688800 0x9ffd00001ffe6005 0xf3ffa00003ffcc00

def z510 : W := mkw 0x25d07bc21ef087be 0x04ba0f7843de10f7 0xfff27fc61ff187ff 0xfffe4ff8c3fe30ff

def z511 : W := mkw 0x08a516599fdf76c1 0x4114a2cb33fbeed8 0xf86d5e799fffffc7 0xbf0dabcf33fffff8

def z512 : W := mkw 0x35d07bca1efb87ff 0x86ba0f7943df70ff 0xfff07f801fff87fe 0xfffe0ff003fff0ff

def z513 : W := mkw 0x13afe47f581b8369 0x8275fc8feb03706d 0xd78fe07ff81f87ff 0x7af1fc0fff03f0ff

def z514 : W := mkw 0x022f843540000000 0x0045f086a8000000 0xa01fb1ffe0000003 0xd403f63ffc000000

def z515 : W := mkw 0x0e7f9659859666c1 0x41cff2cb30b2ccd8 0xffffde79979e67c7 0xfffffbcf32f3ccf8

def z516 : W := mkw 0x1b8a767f9c9ba7e9 0xc3714ecff39374fd 0xf78e7e7f981f87ff 0x7ef1cfcff303f0ff

def z517 : W := mkw 0x25507b8006e00496 0x04aa0f7000dc0092 0xeff07f8007e00002 0xfdfe0ff000fc0000

def z518 : W := mkw 0x075ae92440000000 0x00eb5d2488000000 0xc79ee1fe60000003 0x78f3dc3fcc000000

def z519 : W := mkw 0x1080004a1b5fd369 0x82100009436bfa6d 0x180000001ffffffc 0x0300000003ffffff

def z520 : W := mkw 0x038a602418000120 0x00714c0483000024 0xd78e607e180007ff 0x7af1cc0fc30000ff

def z521 : W := mkw 0x138a70eebc3baf7d 0xa2714e1dd78775ef 0xf78e71fff81f87ff 0x7ef1ce3fff03f0ff

def z522 : W := mkw 0x17fffdfffc3baf7d 0xa2ffffbfff8775ef 0xfffffffffc7fffff 0xffffffffff8fffff

def z523 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x47feefbe60000000 0x68ffddf7cc000000

def z524 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x67fddfb9e0000000 0xacffbbf73c000000

def z525 : W := mkw 0x208012c2bef0afbe 0x2410025857de15f7 0x180000001ff1fffc 0x0300000003fe3fff

def z526 : W := mkw 0x1180606e181b8369 0x82300c0dc303706d 0x5000607e181f87fe 0x0a000c0fc303f0ff

def z527 : W := mkw 0x038a602418090000 0x00714c0483012000 0xd78e607e181f8007 0x7af1cc0fc303f000

def z528 : W := mkw 0x0825161185846480 0x4104a2c230b08c90 0xe86d5e7987806003 0xbd0dabcf30f00c00

def z529 : W := mkw 0x07ffe9001b4d5000 0x00fffd200369aa00 0xffffff801ffff807 0xfffffff003ffff00

def z530 : W := mkw 0x000012c2a4b0ae9c 0x20000258549615d3 0xf873ffc7fff1ffff 0xff0e7ff8fffe3fff

def z531 : W := mkw 0x0000000000000000 0x0000000000000000 0x8013800000000001 0xd002700000000000

def z532 : W := mkw 0x04d010801e600414 0x009a021003cc0082 0xbff031801fe0063e 0xf7fe063003fc00c7

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0xe0605e0000000002 0xbc0c0bc000000000

def z534 : W := mkw 0x07ffed355b4d5000 0x00fffda6ab69aa00 0xf7fffffff38e0003 0xfefffffffe71c000

def z535 : W := mkw 0x0000000000000000 0x0000000000000000 0x9860000017800004 0xb30c000002f00000

def z536 : W := mkw 0x1ffff67f9fdff7e9 0xc3fffecff3fbfefd 0xfffffe7f9fffffff 0xffffffcff3ffffff

def z537 : W := mkw 0x122f806e011fd249 0x8245f00dc023fa49 0x000f807e001ff801 0x0001f00fc003ff00

def z538 : W := mkw 0x067f800000000000 0x00cff00000000000 0x8fff80000c71f805 0xf1fff000018e3f00

def z539 : W := mkw 0x17fff0eebf7fff7d 0xa2fffe1dd7efffef 0xfffff1ffffffffff 0xfffffe3fffffffff

def z540 : W := mkw 0x0000120004800480 0x0000024000900090 0x60005e00000007c2 0x0c000bc0000000f8

def z541 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x180d0079979e67c5 0x0301a00f32f3ccf8

def z542 : W := mkw 0x0100600000000120 0x00200c0000000024 0x40006000000007fa 0x08000c00000000ff

def z543 : W := mkw 0x067f800003445000 0x00cff00000688a00 0x8fff800007e07801 0xf1fff00000fc0f00

def z544 : W := mkw 0x0000128004a00494 0x0000025000940092 0xf8707f801fe007fe 0xff0e0ff003fc00ff

def z545 : W := mkw 0x0a2f9659859f76c1 0x4145f2cb30b3eed8 0xf86fde79979fffc7 0xbf0dfbcf32f3fff8

def z546 : W := mkw 0x25d069801a600136 0x04ba0d30034c0026 0xe7f07f800860003a 0xfcfe0ff0010c0007

def z547 : W := mkw 0x000010c084302614 0x00000218108604c2 0xa81131c18c70663f 0xd5022638318e0cc7

def z548 : W := mkw 0x075a692400000000 0x00eb4d2480000000 0xe7fe7ffe00000003 0xfcffcfffc0000000

def z549 : W := mkw 0x077ffdb5e4202c14 0x20efffb6bc840582 0xefffffffe4607803 0xfdfffffffc8c0f00

def z550 : W := mkw 0x055079c2a430ae1c 0x20aa0f38548615c3 0xeff3ffc7ec71fe3f 0xfdfe7ff8fd8e3fc7

def z551 : W := mkw 0x138a706e9c1ba769 0x82714e0dd38374ed 0xff8f707f9c1fe7ff 0xfff1ee0ff383fcff

def z552 : W := mkw 0x0000124084902680 0x00000248109204d0 0xf8615e41979067c7 0xbf0c2bc832f20cf8

def z553 : W := mkw 0x022f8435410d5000 0x0045f086a821aa00 0x000f807fe01ff801 0x0001f00ffc03ff00

def z554 : W := mkw 0x277fffb544a005b6 0x04effff6a89400b6 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z555 : W := mkw 0x37da7ba61ee985be 0x86fb4f74c3dd30b7 0xfff27f861fe187fe 0xfffe4ff0c3fc30ff

def z556 : W := mkw 0x24501b8006e00496 0x048a037000dc0092 0xf8705f8017e007c6 0xbf0e0bf002fc00f8

def z557 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x079fa1ffe0000001 0x40f3f43ffc000000

def z558 : W := mkw 0x022f8042a11dfa08 0x2045f0085423bf41 0x000f8047e01ff801 0x0001f008fc03ff00

def z559 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x0000000000000638 0x00000000000000c7

def z560 : W := mkw 0x077fedb76020881c 0x20effdb6ec041103 0xe7ffffffe861983b 0xfcfffffffd0c3307

def z561 : W := mkw 0x2df56f191bc641e3 0x45beade32378c83c 0x57ec4e38138e01c0 0x2afd89c70271c038

def z562 : W := mkw 0x04d012001ec00480 0x009a024003d80090 0xfff05e001fe007c6 0xfffe0bc003fc00f8

def z563 : W := mkw 0x0eff84599b5f7241 0x41dff08b336bee48 0x9fff80799ffff805 0xf3fff00f33ffff00

def z564 : W := mkw 0x25d07bc2bef0afbe 0x24ba0f7857de15f7 0xfff07fc7ffe007fe 0xfffe0ff8fffc00ff

def z565 : W := mkw 0x077fe92440000000 0x00effd2488000000 0x87ffa18660000001 0xf0fff430cc000000

def z566 : W := mkw 0x06ff92001fcd5480 0x00dff24003f9aa90 0xffffde001fffffc7 0xfffffbc003fffff8

def z567 : W := mkw 0x08001248859666c1 0x4100024910b2ccd8 0xb8011041979e67c7 0x9700220832f3ccf8

def z568 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xc7ffce3800000001 0xf8fff9c700000000

def z569 : W := mkw 0x08251248859666c1 0x4104a24910b2ccd8 0x986d0000179e67c5 0xb30da00002f3ccf8

def z570 : W := mkw 0x0000120004800480 0x0000024000900090 0x18000000178007c4 0x0300000002f000f8

def z571 : W := mkw 0x26ff92801fed55b6 0x04dff25003fdaab6 0x9fff80001ffffffd 0xf3fff00003ffffff

def z572 : W := mkw 0x0000000000000000 0x0000000000000000 0x8002204600000003 0x50004408c0000000

def z573 : W := mkw 0x2df57f991fe645f7 0x45beaff323fcc8be 0xfffc7fb81fee07fe 0xffff8ff703fdc0ff

def z574 : W := mkw 0x00000042a010aa08 0x2000000854021541 0xa013b1c7e011f803 0xd4027638fc023f00

def z575 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xd86d4e38179e61c5 0xbb0da9c702f3cc38

def z576 : W := mkw 0x018070801c200534 0x00300e10038400a6 0xff9071801c6007fe 0xfff20e30038c00ff

def z577 : W := mkw 0x04758d1140000000 0x008eb1a228000000 0xa073bfc7e0000003 0xd40e77f8fc000000

def z578 : W := mkw 0x028a000018090000 0x0051400003012000 0x178c0000100e0000 0x22f180000201c000

def z579 : W := mkw 0x27dafb801ee915b6 0x04fb5f7003dd22b6 0xfff2ff801fe19ffe 0xfffe5ff003fc33ff

def z580 : W := mkw 0x208002001ac001a2 0x0410004003580034 0x10000000138001c0 0x0200000002700038

def z581 : W := mkw 0x17ffed3d580b0161 0x82fffda7ab01602c 0xf7fffffff00e01c3 0xfefffffffe01c038

def z582 : W := mkw 0x00001080a4202c14 0x2000021014840582 0xa813b1c7e4607803 0xd5027638fc8c0f00

def z583 : W := mkw 0x18a5165b9d9fe7e9 0xc314a2cb73b3fcfd 0xf86d5e799f9fe7ff 0xbf0dabcf33f3fcff

def z584 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x08038047ec71fe3d 0x01007008fd8e3fc7

def z585 : W := mkw 0x0000000003445000 0x0000000000688a00 0x0800000007e07800 0x0100000000fc0f00

def z586 : W := mkw 0x038a600018090120 0x00714c0003012024 0xd78e6000181f87ff 0x7af1cc000303f0ff

def z587 : W := mkw 0x082516d3a5b4ee9c 0x6104a2da74b69dd3 0xa873bfc7eff1fe3f 0xd50e77f8fdfe3fc7

def z588 : W := mkw 0x138a726e1c9b87e9 0x82714e4dc39370fd 0xffee7e7e1f9f87ff 0xfffdcfcfc3f3f0ff

def z589 : W := mkw 0x24501b80a6e02c96 0x248a037014dc0592 0x28719f81e7e07800 0x850e33f03cfc0f00

def z590 : W := mkw 0x07ffed355b4d5000 0x00fffda6ab69aa00 0x57ec4e38138e0000 0x2afd89c70271c000

def z591 : W := mkw 0x17dae06e1a5b9369 0x82fb5c0dc34b726d 0xd79ee07e187f9fff 0x7af3dc0fc30ff3ff

def z592 : W := mkw 0x17ffe0261b4dd128 0x82fffc04c369ba25 0x9fffa0061ffff83d 0xf3fff400c3ffff07

def z593 : W := mkw 0x06ff80421b5dd208 0x00dff008436bba41 0x9fffa0461ffffe3f 0xf3fff408c3ffffc7

def z594 : W := mkw 0x09257f7dc59666c1 0x4124afefb8b2ccd8 0xf86d7ffff79e67c7 0xbf0daffffef3ccf8

def z595 : W := mkw 0x25f5fb801fe455b6 0x04bebf7003fc8ab6 0xfff1ff801fe07ffe 0xfffe3ff003fc0fff

def z596 : W := mkw 0x080012caa5b6eedd 0x6100025954b6dddb 0xb813b1c7ffffffff 0xd7027638ffffffff

def z597 : W := mkw 0x1180604a181b8369 0x82300c094303706d 0xd7806000181f87fe 0x7af00c000303f0ff

def z598 : W := mkw 0x1baf647f991fe369 0xc375ec8ff323fc6d 0xd78f607f981fe7ff 0x7af1ec0ff303fcff

def z599 : W := mkw 0x000000822020881c 0x2000001044041103 0x0000000008619838 0x00000000010c3307

def z600 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7fc7fb800000002 0xfcff8ff700000000

def z601 : W := mkw 0x028a000018090000 0x0051400003012000 0x9f9f80001c7ff805 0xf3f3f000038fff00

def z602 : W := mkw 0x27ffeb001bcd51a2 0x04fffd600379aa34 0xdfffce001ffff9c5 0xfbfff9c003ffff38

def z603 : W := mkw 0x08001659849226c1 0x410002cb309244d8 0xf8605e79978007c6 0xbf0c0bcf32f000f8

def z604 : W := mkw 0x00000000010d5000 0x000000000021aa00 0x00000000001ff800 0x000000000003ff00

def z605 : W := mkw 0x0575ed3540000000 0x00aebda6a8000000 0x6071ffffe0000002 0x8c0e3ffffc000000

def z606 : W := mkw 0x0025004801164241 0x0004a0090022c848 0xd86d4078179e67c7 0xbb0da80f02f3ccf8

def z607 : W := mkw 0x00001080a4202c14 0x2000021014840582 0xa8139181ec71f805 0xd50272303d8e3f00

def z608 : W := mkw 0x24759b8007e45496 0x048eb37000fc8a92 0x28719f8007e07800 0x850e33f000fc0f00

def z609 : W := mkw 0x02af0000190d4000 0x0055e0000321a800 0x9fef00001f9fe005 0xf3fde00003f3fc00

def z610 : W := mkw 0x27ffe9801b6d5136 0x04fffd30036daa26 0x9fffa1801ffff83d 0xf3fff43003ffff07

def z611 : W := mkw 0x002514d3a430ae1c 0x2004a29a748615c3 0xe87fffffec71fe3f 0xfd0ffffffd8e3fc7

def z612 : W := mkw 0x05d0690018000120 0x00ba0d2003000024 0xf7f07f80180007fe 0xfefe0ff0030000ff

def z613 : W := mkw 0x07ffed355a491000 0x00fffda6ab492200 0xe7ffffffe8619803 0xfcfffffffd0c3300

def z614 : W := mkw 0x21807b801ee005b6 0x04300f7003dc00b6 0x78007f801fe007fe 0x0f000ff003fc00ff

def z615 : W := mkw 0x24d012801ee005b6 0x049a025003dc00b6 0x9ff000001fe007fc 0xf3fe000003fc00ff

def z616 : W := mkw 0x0f7fff35c5846480 0x41efffe6b8b08c90 0xefffffffe7806003 0xfdfffffffcf00c00

def z617 : W := mkw 0x27dae9a45a600136 0x04fb5d348b4c0026 0x0792a18668600038 0x40f25430cd0c0007

def z618 : W := mkw 0x27ffffb55fed55b6 0x04fffff6abfdaab6 0xffffffffffffffff 0xffffffffffffffff

def z619 : W := mkw 0x00000042a010aa08 0x2000000854021541 0x00000047e0000000 0x00000008fc000000

def z620 : W := mkw 0x04759d91e4202c14 0x208eb3b23c840582 0x28719f81e4607800 0x850e33f03c8c0f00

def z621 : W := mkw 0x030a602400000000 0x00614c0480000000 0xe79ff1ffe0000003 0xfcf3fe3ffc000000

def z622 : W := mkw 0x000010c20430861c 0x00000218408610c3 0xa81231c60c71863f 0xd5024638c18e30c7

def z623 : W := mkw 0x0000104084102600 0x00000208108204c0 0xa81390418c71fe07 0xd5027208318e3fc0

def z624 : W := mkw 0x0eff92489fdf76c1 0x41dff24913fbeed8 0x9fff80001fffffc5 0xf3fff00003fffff8

def z625 : W := mkw 0x067f8000010d5000 0x00cff0000021aa00 0x87ff8000001ff801 0xf0fff0000003ff00

def z626 : W := mkw 0x077fff3544800480 0x00efffe6a8900090 0xfffffffff78007c7 0xfffffffffef000f8

def z627 : W := mkw 0x0825161185846480 0x4104a2c230b08c90 0xf8615e01978067c6 0xbf0c2bc032f00cf8

def z628 : W := mkw 0x0550798004200414 0x00aa0f3000840082 0xeff07f800c60063e 0xfdfe0ff0018c00c7

def z629 : W := mkw 0x138a606e1b5fd369 0x82714c0dc36bfa6d 0xdf8e607e1fffffff 0x7bf1cc0fc3ffffff

def z630 : W := mkw 0x067f800001044000 0x00cff00000208800 0x9fff8000179e6005 0xf3fff00002f3cc00

def z631 : W := mkw 0x1080000218098128 0x8210000043013025 0x0000000008018038 0x0000000001003007

def z632 : W := mkw 0x0080000018000000 0x0010000003000000 0x9780000018000004 0x72f0000003000000

def z633 : W := mkw 0x0825045981166241 0x4104a08b3022cc48 0x986d0079979e6005 0xb30da00f32f3cc00

def z634 : W := mkw 0x022f8000010d5000 0x0045f0000021aa00 0x000c0000000e0000 0x000180000001c000

def z635 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xa013b1c7e000063b 0xd4027638fc0000c7

def z636 : W := mkw 0x08001248859666c1 0x4100024910b2ccd8 0xd80c4078179e67c7 0x3b01880f02f3ccf8

def z637 : W := mkw 0x0000004800120241 0x0000000900024048 0x000c0078001e0001 0x0001800f0003c000

def z638 : W := mkw 0x00001080a4202c14 0x2000021014840582 0x20001181e0000000 0x040002303c000000

def z639 : W := mkw 0x0000008020200814 0x2000001004040102 0x0010818060601800 0x000210300c0c0300

def z640 : W := mkw 0x17ffe02c1b4f5161 0x82fffc058369ea2c 0xdfffc0381ffff9c5 0xfbfff80703ffff38

def z641 : W := mkw 0x13af647f181b8369 0x8275ec8fe303706d 0xf7ef7e7f981f87ff 0xfefdefcff303f0ff

def z642 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x078e207e081f8039 0x40f1c40fc103f007

def z643 : W := mkw 0x2c751fd987f666d7 0x458ea3fb30feccda 0xf87d5ff997fe67c7 0xbf0fabff32ffccf8

def z644 : W := mkw 0x0000108224208c1c 0x2000021044841183 0xa812b1866c619e3e 0xd5025630cd8c33c7

def z645 : W := mkw 0x0eff96dbbffffedd 0x61dff2db77ffffdb 0xffffffffffffffff 0xffffffffffffffff

def z646 : W := mkw 0x0450890040000000 0x008a112008000000 0x0010818060000000 0x000210300c000000

def z647 : W := mkw 0x00001042a410ae08 0x20000208548215c1 0xa8039047e411fe07 0x95007208fc823fc0

def z648 : W := mkw 0x0025104085146600 0x0004a20810a28cc0 0xb86d1041979e6607 0xb70da20832f3ccc0

def z649 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x7ff05f8017e001c0 0xaffe0bf002fc0038

def z650 : W := mkw 0x077fed7d40120241 0x00effdafa8024048 0xf7fffffff01e07c7 0xfefffffffe03c0f8

def z651 : W := mkw 0x1a2f167f859fe6c9 0xc345e2cff0b3fcd9 0xf86f5e7f979fe7c7 0xbf0debcff2f3fcf8

def z652 : W := mkw 0x0aaf16599d9f66c1 0x4155e2cb33b3ecd8 0xffef5e799f9fe7c7 0xfffdebcf33f3fcf8

def z653 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x281391c7e471f801 0x85027238fc8e3f00

def z654 : W := mkw 0x0000104084102600 0x00000208108204c0 0x2000104180000602 0x04000208300000c0

def z655 : W := mkw 0x0800120085846480 0x4100024010b08c90 0x0800000007806000 0x0100000000f00c00

def z656 : W := mkw 0x00000042a010aa08 0x2000000854021541 0x000000000011f800 0x0000000000023f00

def z657 : W := mkw 0x01007df7e430ae1c 0x20200fbefc8615c3 0xe813ffffec71fe3f 0xdd027ffffd8e3fc7

def z658 : W := mkw 0x06da90c2be79be1c 0x20db521857cf37c3 0xaf93b1c7ec71fe3f 0xd5f27638fd8e3fc7

def z659 : W := mkw 0x1925767f8596e7e9 0xc324aecff0b2dcfd 0xf86d7e7f979e67ff 0xbf0dafcff2f3ccff

def z660 : W := mkw 0x2000128006e00496 0x0400025000dc0092 0x0800000007e00000 0x0100000000fc0000

def z661 : W := mkw 0x008000001b4d5000 0x001000000369aa00 0x981380001ffff805 0xd302700003ffff00

def z662 : W := mkw 0x17ffed7f581b8369 0x82fffdafeb03706d 0xd7ee6e7e181f87ff 0x7afdcdcfc303f0ff

def z663 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x67907f80086007fa 0x4cf20ff0010c00ff

def z664 : W := mkw 0x0025120005844480 0x0004a24000b08890 0xf86d5e00179e67c7 0xbf0dabc002f3ccf8

def z665 : W := mkw 0x1100606e00128369 0x82200c0dc002506d 0xc002607e081187ff 0x58004c0fc10230ff

def z666 : W := mkw 0x25d069801a600136 0x04ba0d30034c0026 0xd7906180186007fe 0x7af20c30030c00ff

def z667 : W := mkw 0x1baf767d9d9f67e1 0xc375eecfb3b3ecfc 0xffed5e79979e67c7 0xbffdabcf32f3ccf8

def z668 : W := mkw 0x13af606e191fc369 0x8275ec0dc323f86d 0xdfef607e1f9fe7ff 0xfbfdec0fc3f3fcff

def z669 : W := mkw 0x1baf76ffbdbfeffd 0xe375eedff7b7fdff 0xffffffffffffffff 0xffffffffffffffff

def z670 : W := mkw 0x0a2f8459811f7241 0x4145f08b3023ee48 0x000f8079801ff801 0x0001f00f3003ff00

def z671 : W := mkw 0x35d07bee1ef287ff 0x86ba0f7dc3de50ff 0xfff07ffe1fe007fe 0xfffe0fffc3fc00ff

def z672 : W := mkw 0x008010c2bf7dfe1c 0x2010021857efbfc3 0x180000001ffffe3c 0x0300000003ffffc7

def z673 : W := mkw 0x17ffe06e1b5fd369 0x82fffc0dc36bfa6d 0xd7ee607e1b9f87ff 0x7afdcc0fc373f0ff

def z674 : W := mkw 0x0000100084002400 0x0000020010800480 0x2801100184006000 0x8500220030800c00

def z675 : W := mkw 0x065a800000000000 0x00cb500000000000 0x0792800000000000 0x40f2500000000000

def z676 : W := mkw 0x0100690000000000 0x00200d2000000000 0x60007f8000000002 0x0c000ff000000000

def z677 : W := mkw 0x1000004a001b8249 0x8200000940037049 0x00000000001f8000 0x000000000003f000

def z678 : W := mkw 0x04759080a7647c14 0x208eb21014ec8f82 0x28719181e7e07800 0x850e32303cfc0f00

def z679 : W := mkw 0x27fffff7fef0afbe 0x24fffffeffde15f7 0xfffffffffff1ffff 0xfffffffffffe3fff

def z680 : W := mkw 0x138a602618098128 0x82714c04c3013025 0xd7826006180187fe 0x7af04c00c30030ff

def z681 : W := mkw 0x0eff86191bcf50c1 0x41dff0c32379ea18 0x57ec4e38138e01c0 0x2afd89c70271c038

def z682 : W := mkw 0x0000104884122641 0x00000209108244c8 0xf80d5079941e67c7 0xbf01aa0f3283ccf8

def z683 : W := mkw 0x0550690000000000 0x00aa0d2000000000 0xe7f3ffc7e0000003 0xfcfe7ff8fc000000

def z684 : W := mkw 0x208000801a600136 0x04100010034c0026 0x0000000008600038 0x00000000010c0007

def z685 : W := mkw 0x000000822020881c 0x2000001044041103 0xa013b1c7e861983b 0xd4027638fd0c3307

def z686 : W := mkw 0x0800004881166241 0x410000091022cc48 0x00000000001e6000 0x000000000003cc00

def z687 : W := mkw 0x067f800000000000 0x00cff00000000000 0x07ec000000000000 0x20fd800000000000

def z688 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x881380000c71fe3d 0xd1027000018e3fc7

def z689 : W := mkw 0x0025045900120241 0x0004a08b20024048 0xf06d5e79901e07c7 0xbe0dabcf3203c0f8

def z690 : W := mkw 0x25f5ff915ee005b6 0x04bebff22bdc00b6 0xfff1ff81ffe007fe 0xfffe3ff03ffc00ff

def z691 : W := mkw 0x0025841140000000 0x0004b08228000000 0x00018001e0000000 0x000030003c000000

def z692 : W := mkw 0x1880124a9d9fe7e9 0xc310024953b3fcfd 0x180000001f9fe7fc 0x0300000003f3fcff

def z693 : W := mkw 0x21007b8004a005b6 0x04200f70009400b6 0xe8107f800c6007fe 0xdd020ff0018c00ff

def z694 : W := mkw 0x27da7b801ee905b6 0x04fb4f7003dd20b6 0xfffe7f801fff87ff 0xffffcff003fff0ff

def z695 : W := mkw 0x17dae0261a499128 0x82fb5c04c3493225 0x0792a00608619838 0x40f25400c10c3307

def z696 : W := mkw 0x05d069001a400000 0x00ba0d2003480000 0xfff07f801fe00006 0xfffe0ff003fc0000

def z697 : W := mkw 0x028a0048181b0241 0x0051400903036048 0xd78e4078181f87c7 0x7af1c80f0303f0f8

def z698 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xa00231c7e811863f 0x54004638fd0230c7

def z699 : W := mkw 0x308012ca1efb87ff 0x8610025943df70ff 0x180000001fff87fc 0x0300000003fff0ff

def z700 : W := mkw 0x08001659859666c1 0x410002cb30b2ccd8 0x78005e79979e67c6 0x0f000bcf32f3ccf8

def z701 : W := mkw 0x0475800000000000 0x008eb00000000000 0x0071800000000000 0x800e300000000000

def z702 : W := mkw 0x25f57b801fe445b6 0x04beaf7003fc88b6 0xfffd7f801ffe67ff 0xffffaff003ffccff

def z703 : W := mkw 0x088012489fdf76c1 0x4110024913fbeed8 0x180000001fffffc4 0x0300000003fffff8

def z704 : W := mkw 0x08001659849226c1 0x410002cb309244d8 0xe8015e79841067c7 0x9d002bcf30820cf8

def z705 : W := mkw 0x04d000001a400000 0x009a000003480000 0x9ff380001ff1f805 0xf3fe700003fe3f00

def z706 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x286d1e79879e6001 0x850da3cf30f3cc00

def z707 : W := mkw 0x0f5afb6cc59666c1 0x41eb5f6d98b2ccd8 0x1f92a186779e67c4 0x43f25430cef3ccf8

def z708 : W := mkw 0x077ffdf7e430ae1c 0x20efffbefc8615c3 0x4fec4e380c71fe3c 0x29fd89c7018e3fc7

def z709 : W := mkw 0x028a00001b4d5000 0x005140000369aa00 0x1f8200001ffff804 0x43f0400003ffff00

def z710 : W := mkw 0x088012cabffffedd 0x6110025957ffffdb 0x180000001ffffffc 0x0300000003ffffff

def z711 : W := mkw 0x1a2f047fa11fea49 0xe345e08ff423fd49 0x000f807fe01ff801 0x0001f00ffc03ff00

def z712 : W := mkw 0x06ff80001b4d5120 0x00dff0000369aa24 0x9fff80001ffffffd 0xf3fff00003ffffff

def z713 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xf06c5e38138e01c2 0xbe0d8bc70271c038

def z714 : W := mkw 0x08259659c59666c1 0x4104b2cb38b2ccd8 0xf86dde79f79e67c7 0xbf0dbbcf3ef3ccf8

def z715 : W := mkw 0x077fed3541045000 0x00effda6a8208a00 0xe7ffffffe0007803 0xfcfffffffc000f00

def z716 : W := mkw 0x05756d1100000000 0x00aeada220000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z717 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ed7fffe0000003 0xbcfdaffffc000000

def z718 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x706d5e79939e67c3 0x2e0dabcf3273ccf8

def z719 : W := mkw 0x0825069b21a6c8dd 0x6104a0d36434d91b 0x507eefbe7bef99f8 0x6a0fddf7cf7df33f

def z720 : W := mkw 0x077fed35410d5000 0x00effda6a821aa00 0xefffffffec7ff807 0xfdfffffffd8fff00

def z721 : W := mkw 0x128a004a181b8369 0x825140094303706d 0xd78e4078181f87ff 0x7af1c80f0303f0ff

def z722 : W := mkw 0x232ffb8005ad55b6 0x0465ff7000b5aab6 0x600fff80001ffffb 0x0c01fff00003ffff

def z723 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x0813a1c7ec71fe3d 0x41027438fd8e3fc7

def z724 : W := mkw 0x37dae9a65a69813e 0x86fb5d34cb4d3027 0x0792a18668618038 0x40f25430cd0c3007

def z725 : W := mkw 0x25d07b001ec005a2 0x04ba0f6003d800b4 0xffe07e001f8007fe 0xfffc0fc003f000ff

def z726 : W := mkw 0x02af0000190d4000 0x0055e0000321a800 0x9fff80001ffff805 0xf3fff00003ffff00

def z727 : W := mkw 0x00001082a420ac1c 0x2000021054841583 0xa813b1c7ec61f83b 0xd5027638fd8c3f07

def z728 : W := mkw 0x0825165b8596e6c9 0x4104a2cb70b2dcd9 0xf87fffffff9fe7ff 0xff0ffffffff3fcff

def z729 : W := mkw 0x1baf76379d8de5a8 0xc375eec6f3b1bcb5 0x2fe33e078f81e038 0xc5fc67c0f1f03c07

def z730 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7fc7fffe0000002 0xfcff8ffffc000000

def z731 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xf86d5e79979e61c7 0xbf0dabcf32f3cc38

def z732 : W := mkw 0x0eda96599edb36c1 0x41db52cb33db66d8 0x6792de7988619fc2 0x4cf25bcf310c33f8

def z733 : W := mkw 0x000012caa4b2aedd 0x20000259549655db 0xf87fffffffffffff 0xff0fffffffffffff

def z734 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86fde79979fffc7 0xbf0dfbcf32f3fff8

def z735 : W := mkw 0x08251619858664c1 0x4104a2c330b0cc98 0xf86d5e39979e61c5 0xbf0dabc732f3cc38

def z736 : W := mkw 0x25d06b42bad0abaa 0x24ba0d68575a1575 0x57e3ce47f391f9c1 0x2afc79c8fe723f38

def z737 : W := mkw 0x05d07b001c8005a0 0x00ba0f60039000b4 0xfff07f801f8007fe 0xfffe0ff003f000ff

def z738 : W := mkw 0x06ff8d115b4d5000 0x00dff1a22b69aa00 0xffffdff9fffff807 0xfffffbff3fffff00

def z739 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff07f801ff1fffe 0xfffe0ff003fe3fff

def z740 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfffc7f801ffe07ff 0xffff8ff003ffc0ff

def z741 : W := mkw 0x1575e06e0356d369 0x82aebc0dc06ada6d 0x4871e07e07e07ffa 0x890e3c0fc0fc0fff

def z742 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfffc7ff81fe007ff 0xffff8fff03fc00ff

def z743 : W := mkw 0x08251619858664c1 0x4104a2c330b0cc98 0xf86d5e79978e61c3 0xbf0dabcf32f1cc38

def z744 : W := mkw 0x04f500001b444000 0x009ea00003688800 0x9fff80001ffff805 0xf3fff00003ffff00

def z745 : W := mkw 0x08250659819662c1 0x4104a0cb3032cc58 0xd06d4e79939e67c7 0x3a0da9cf3273ccf8

def z746 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x67ffdfffe0000001 0xacfffbfffc000000

def z747 : W := mkw 0x067f8d3540000000 0x00cff1a6a8000000 0xa7ff9fffe0000001 0xf4fff3fffc000000

def z748 : W := mkw 0x0825065b0196c2c9 0x4104a0cb6032d859 0xd06e6e7e1b9f87ff 0x7a0dcdcfc373f0ff

def z749 : W := mkw 0x000012ca04b286dd 0x00000259409650db 0xf87e7ffe1fff87ff 0xff0fcfffc3fff0ff

def z750 : W := mkw 0x138a696e581b8369 0x82714d2dcb03706d 0xd78e61fe781f87ff 0x7af1cc3fcf03f0ff

def z751 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x7ff07f8017e007fa 0xaffe0ff002fc00ff

def z752 : W := mkw 0x06ff84111b4d5000 0x00dff0822369aa00 0xdfffce381ffff805 0xfbfff9c703ffff00

def z753 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fffa0461ffff807 0xf3fff408c3ffff00

def z754 : W := mkw 0x37da69241a490122 0x86fb4d2483492024 0x0780000000000000 0x00f0000000000000

def z755 : W := mkw 0x2c751f91a7e46c96 0x658ea3f234fc8d92 0x28719f81e7e07800 0x850e33f03cfc0f00

def z756 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ffffffe800063f 0xfcfffffffd0000c7

def z757 : W := mkw 0x08251619058644c1 0x4104a2c320b0c898 0x706c5e38138e07c2 0x2e0d8bc70271c0f8

def z758 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x786c5e79979e67c6 0x2f0d8bcf32f3ccf8

def z759 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x7fe07f801fe007fe 0x2ffc0ff003fc00ff

def z760 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xf79e71fe181f87ff 0xfef3ce3fc303f0ff

def z761 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff2ff801fe19ffe 0xfffe5ff003fc33ff

def z762 : W := mkw 0x0825165b8596e6c9 0x4104a2cb70b2dcd9 0xf86d5e799f9fe7ff 0xbf0dabcf33f3fcff

def z763 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x679fffffe0000003 0x4cf3fffffc000000

def z764 : W := mkw 0x1a2f047f011fc249 0xc345e08fe023f849 0x000e007e001f8001 0x0001c00fc003f000

def z765 : W := mkw 0x138a70acbc2b2d75 0xa2714e15978565ae 0x7f9dd1b9f46e79c0 0xaff3ba373e8dcf38

def z766 : W := mkw 0x077fed3541044000 0x00effda6a8208800 0xe7ffffffe01e6003 0xfcfffffffc03cc00

def z767 : W := mkw 0x075aed3540000000 0x00eb5da6a8000000 0xe793ffffe0000003 0xdcf27ffffc000000

def z768 : W := mkw 0x138a606eb81bab69 0xa2714c0dd703756d 0xd78e607e181fffff 0x7af1cc0fc303ffff

def z769 : W := mkw 0x000010caa432ae5d 0x20000219548655cb 0xb813b1c7fc7fffff 0xd7027638ff8fffff

def z770 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x67fdffffe0000002 0xacffbffffc000000

def z771 : W := mkw 0x000000c2a030aa1c 0x2000001854061543 0xa013b1c7e871f83b 0xd4027638fd0e3f07

def z772 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff27f801ff187ff 0xfffe4ff003fe30ff

def z773 : W := mkw 0x06ff8d115b4d5000 0x00dff1a22b69aa00 0xbfffbfc7fffff807 0xf7fff7f8ffffff00

def z774 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xb873b1c7fff1fe3f 0xf70e7638fffe3fc7

def z775 : W := mkw 0x05506d3540000000 0x00aa0da6a8000000 0x67e07fffe0000002 0x2cfc0ffffc000000

def z776 : W := mkw 0x08250659819662c1 0x4104a0cb3032cc58 0x506c4e38139e61c0 0x2a0d89c70273cc38

def z777 : W := mkw 0x06ff90c2bf7dfe1c 0x20dff21857efbfc3 0x37ec31c7f38e063a 0x26fd8638fe71c0c7

def z778 : W := mkw 0x05507b8004a00494 0x00aa0f7000940092 0xfff07f801fe007fe 0xfffe0ff003fc00ff

def z779 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xd06c4e38138e07c6 0x3a0d89c70271c0f8

def z780 : W := mkw 0x130a606e00128369 0x82614c0dc002506d 0xd78e607e101e07ff 0x7af1cc0fc203c0ff

def z781 : W := mkw 0x05506d3540000000 0x00aa0da6a8000000 0x67907fffe0000002 0x4cf20ffffc000000

def z782 : W := mkw 0x25d0fb801ee015b6 0x04ba1f7003dc02b6 0xfff0ff801fe01ffe 0xfffe1ff003fc03ff

def z783 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78fe07ff81f87ff 0x7af1fc0fff03f0ff

def z784 : W := mkw 0x188012cabdbfeffd 0xe310025957b7fdff 0x180000001ffffffc 0x0300000003ffffff

def z785 : W := mkw 0x22af96b55ee005b6 0x0455f2d6abdc00b6 0x180f807fffe007fd 0x0301f00ffffc00ff

def z786 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xd86d4e38179e67c5 0xbb0da9c702f3ccf8

def z787 : W := mkw 0x25d07b809ee025b6 0x04ba0f7013dc04b6 0xfff17f819fe067fe 0xfffe2ff033fc0cff

def z788 : W := mkw 0x075aed3540000000 0x00eb5da6a8000000 0xe79effffe0000003 0x7cf3dffffc000000

def z789 : W := mkw 0x25d07b80bee02db6 0x24ba0f7017dc05b6 0xfff3ff81fff1ffff 0xfffe7ff03ffe3fff

def z790 : W := mkw 0x067f8000034d5000 0x00cff0000069aa00 0x8fff800007fff801 0xf1fff00000ffff00

def z791 : W := mkw 0x077fed35434d5000 0x00effda6a869aa00 0xefffffffe7fff803 0xfdfffffffcffff00

def z792 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78e4038181f87fd 0x7af1c8070303f0ff

def z793 : W := mkw 0x0825165ba596eec9 0x6104a2cb74b2ddd9 0xf86d5e7ff79e67c7 0xbf0dabcffef3ccf8

def z794 : W := mkw 0x04d000001b4d5000 0x009a00000369aa00 0x9ff380001ffff805 0xf3fe700003ffff00

def z795 : W := mkw 0x077fed3540000120 0x00effda6a8000024 0xe7ffffffe00007fb 0xfcfffffffc0000ff

def z796 : W := mkw 0x08251619058644c1 0x4104a2c320b0c898 0x786c5e38178e01c0 0xaf0d8bc702f1c038

def z797 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86d5e79979e67ff 0xbf0dabcf32f3ccff

def z798 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x2813b1c7ec61fe3a 0xc5027638fd8c3fc7

def z799 : W := mkw 0x028a00001b4d5000 0x005140000369aa00 0x1f8c00001ffff804 0x23f1800003ffff00

def z800 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xfffffffff7800007 0xfffffffffef00000

def z801 : W := mkw 0x08250659019642c1 0x4104a0cb2032c858 0x506c4e78138e07c2 0x2a0d89cf0271c0f8

def z802 : W := mkw 0x06ff84111b4d5000 0x00dff0822369aa00 0x9fff80799ffff805 0xf3fff00f33ffff00

def z803 : W := mkw 0x000000c2a030aa1c 0x2000001854061543 0x8013a1c7e871fe3f 0x50027438fd0e3fc7

def z804 : W := mkw 0x365a1bee06fb86df 0x86cb437dc0df70db 0x287e1ffe07ff8001 0x850fc3ffc0fff000

def z805 : W := mkw 0x25d07b80bee02db6 0x24ba0f7017dc05b6 0xfff07f801fe07ffe 0xfffe0ff003fc0fff

def z806 : W := mkw 0x0180604a18128369 0x00300c094302506d 0xd78e607e181f87ff 0x7af1cc0fc303f0ff

def z807 : W := mkw 0x077fed3543445000 0x00effda6a8688a00 0xefffffffeff1f807 0xfdfffffffdfe3f00

def z808 : W := mkw 0x04f580001b4d5000 0x009eb0000369aa00 0x9ff180001ffff804 0xf3fe300003ffff00

def z809 : W := mkw 0x25d07b80bee02db6 0x24ba0f7017dc05b6 0xfff07f81ffe007fe 0xfffe0ff03ffc00ff

def z810 : W := mkw 0x288012cabff6efff 0x6510025957feddff 0x180000001ffffffc 0x0300000003ffffff

def z811 : W := mkw 0x06ff84111b4d5000 0x00dff0822369aa00 0xbfff9e019ffff805 0xf7fff3c033ffff00

def z812 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd79ee07e187f9fff 0x7af3dc0fc30ff3ff

def z813 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0x706c7ffff38e07fa 0x2e0d8ffffe71c0ff

def z814 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff2ff867fe007fe 0xfffe5ff0cffc00ff

def z815 : W := mkw 0x06da80001b4d5000 0x00db50000369aa00 0x9f9380001ffff805 0xd3f2700003ffff00

def z816 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x586d4e79979e67c5 0x2b0da9cf32f3ccf8

def z817 : W := mkw 0x01806200188001a0 0x00300c4003100034 0xd7e06e001b8007fe 0x7afc0dc0037000ff

def z818 : W := mkw 0x08251659a5966ec1 0x6104a2cb34b2cdd8 0xf86dde79f79e7fc7 0xbf0dbbcf3ef3cff8

def z819 : W := mkw 0x2c751f9107e44496 0x458ea3f220fc8892 0x28701f8007e00000 0x850e03f000fc0000

def z820 : W := mkw 0x00001248849226c1 0x00000249109244d8 0xf86d5e79979e67c7 0xbf0dabcf32f3ccf8

def z821 : W := mkw 0x0825165b8596e6c9 0x4104a2cb70b2dcd9 0xf86d7e7f979e67ff 0xbf0dafcff2f3ccff

def z822 : W := mkw 0x01806d355b4d5000 0x00300da6ab69aa00 0x78007ffffffff806 0x0f000fffffffff00

def z823 : W := mkw 0x130a606e001b8369 0x82614c0dc003706d 0xc78e607e001f87fb 0x78f1cc0fc003f0ff

def z824 : W := mkw 0x0825165b8596e6c9 0x4104a2cb70b2dcd9 0xf86f5e7f979fe7c7 0xbf0debcff2f3fcf8

def z825 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x6ff07f800fe007fa 0xcdfe0ff001fc00ff

def z826 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf06c5e79939e07c7 0x3e0d8bcf3273c0f8

def z827 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xdfe06e001fe007fe 0x7bfc0dc003fc00ff

def z828 : W := mkw 0x08251699a5a66cd5 0x6104a2d334b4cd9a 0x787ddfb9f7ee79c0 0xaf0fbbf73efdcf38

def z829 : W := mkw 0x077fed3540090000 0x00effda6a8012000 0xe7ffffffe01f8003 0xfcfffffffc03f000

def z830 : W := mkw 0x06ff89001b4d5000 0x00dff1200369aa00 0xbfff9f801ffff805 0xf7fff3f003ffff00

def z831 : W := mkw 0x08251619858664c1 0x4104a2c330b0cc98 0x586c4e38178e61c0 0x2b0d89c702f1cc38

def z832 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87ddff9ffffffff 0xbf0fbbff3fffffff

def z833 : W := mkw 0x25507b8004a005b6 0x04aa0f70009400b6 0xfff07f80178007fe 0xfffe0ff002f000ff

def z834 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87d7ff99fffffff 0xff0fafff33ffffff

def z835 : W := mkw 0x2df56dd99b766377 0x45beadbb336ecc6e 0x079d21f9887e6039 0x40f3a43f310fcc07

def z836 : W := mkw 0x04d012801ee00494 0x009a025003dc0092 0xfff07f801fe007fe 0xfffe0ff003fc00ff

def z837 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578e603e181f87fc 0x6af1cc07c303f0ff

def z838 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0xdfffc0781ffff807 0xfbfff80f03ffff00

def z839 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0x706d5e39938e01c0 0xae0dabc73271c038

def z840 : W := mkw 0x06da80001b4d5000 0x00db50000369aa00 0x9ff280001ffff804 0xf3fe500003ffff00

def z841 : W := mkw 0x01006d3540000000 0x00200da6a8000000 0xe7807fffe0000002 0x7cf00ffffc000000

def z842 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86c5e38179e67c6 0xbf0d8bc702f3ccf8

def z843 : W := mkw 0x000012c2a4b0ae9c 0x20000258549615d3 0xe813ffc7ec71ffff 0xdd027ff8fd8e3fff

def z844 : W := mkw 0x25d06b801ae001b6 0x04ba0d70035c0036 0xd7f06f801be007fe 0x7afe0df0037c00ff

def z845 : W := mkw 0x04f500001b4d5000 0x009ea0000369aa00 0x9ffd00001ffff805 0xf3ffa00003ffff00

def z846 : W := mkw 0x08251619058644c1 0x4104a2c320b0c898 0x586c4e38178e07c4 0x2b0d89c702f1c0f8

def z847 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ffffffe8118007 0xfcfffffffd023000

def z848 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xdf9e607e1c7f87ff 0xfbf3cc0fc38ff0ff

def z849 : W := mkw 0x0825169905a644d5 0x4104a2d320b4c89a 0xf87c7fb81fee07fe 0xff0f8ff703fdc0ff

def z850 : W := mkw 0x138ae06e181b9369 0x82715c0dc303726d 0xd78ee07e181f9fff 0x7af1dc0fc303f3ff

def z851 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0xffffde001ffff807 0xfffffbc003ffff00

def z852 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xf7fffffff00007c7 0xfefffffffe0000f8

def z853 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff17fc19fe007ff 0xfffe2ff833fc00ff

def z854 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x5ff06f801fe007fc 0x6bfe0df003fc00ff

def z855 : W := mkw 0x00001082a420ac1c 0x2000021054841583 0xa813b187ec71f83d 0xd5027630fd8e3f07

def z856 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0x57e04e001b8007fc 0x2afc09c0037000ff

def z857 : W := mkw 0x06ff84111b4d5000 0x00dff0822369aa00 0xfffffffffffff807 0xffffffffffffff00

def z858 : W := mkw 0x06ff84355b4d5000 0x00dff086ab69aa00 0xbfffb1fffffff807 0xf7fff63fffffff00

def z859 : W := mkw 0x000012c2a4b0ae9c 0x20000258549615d3 0xa873bfc7eff1fe3f 0xd50e77f8fdfe3fc7

def z860 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xdf8e607e1c7fffff 0x7bf1cc0fc38fffff

def z861 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78c6038181f87fe 0x7af18c070303f0ff

def z862 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0xf7f07f801b8007fe 0xfefe0ff0037000ff

def z863 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0x578c4038180e07fc 0x2af188070301c0ff

def z864 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87ddff9f79e67c7 0xbf0fbbff3ef3ccf8

def z865 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87d7ff9979e67c7 0xff0fafff32f3ccf8

def z866 : W := mkw 0x075a6d3540000000 0x00eb4da6a8000000 0xe7fe7fffe0000003 0xfcffcffffc000000

def z867 : W := mkw 0x082516d985b666d5 0x4104a2db30b6ccda 0xf87ffffffffe67ff 0xff0fffffffffccff

def z868 : W := mkw 0x0000004200108208 0x0000000840021041 0xa813b1c7ec71fe3f 0xd5027638fd8e3fc7

def z869 : W := mkw 0x37da79e61e79873e 0x86fb4f3cc3cf30e7 0xaf9231c60c71863f 0xd5f24638c18e30c7

def z870 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87ffffff79e67ff 0xff0ffffffef3ccff

def z871 : W := mkw 0x1a2f847f811ff249 0xc345f08ff023fe49 0x000f807f801ff801 0x0001f00ff003ff00

def z872 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xffe07f80178007fe 0xbffc0ff002f000ff

def z873 : W := mkw 0x04d000001b4d5000 0x009a00000369aa00 0x1fe000001ffff804 0x23fc000003ffff00

def z874 : W := mkw 0x0825165ba596eec9 0x6104a2cb74b2ddd9 0xf87fde7fffffffc7 0xff0ffbcffffffff8

def z875 : W := mkw 0x27dae9a45a691136 0x04fb5d348b4d2226 0x0792a18668619838 0x40f25430cd0c3307

def z876 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87fde799fffffff 0xff0ffbcf33ffffff

def z877 : W := mkw 0x25d0fb805ee005b6 0x04ba1f700bdc00b6 0xfff0ff807fe007fe 0xfffe1ff00ffc00ff

def z878 : W := mkw 0x08250619818660c1 0x4104a0c33030cc18 0x506d4e39938e61c0 0x2a0da9c73271cc38

def z879 : W := mkw 0x06da00001b4d5000 0x00db40000369aa00 0x9ffe00001ffff805 0xf3ffc00003ffff00

def z880 : W := mkw 0x04d000001b4d5000 0x009a00000369aa00 0x1f9000001ffff804 0x43f2000003ffff00

def z881 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0xbfff9181fffff805 0xf7fff2303fffff00

def z882 : W := mkw 0x077fed35410d5000 0x00effda6a821aa00 0xfffffffff79ff807 0xfffffffffef3ff00

def z883 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ffffffe8619803 0xfcfffffffd0c3300

def z884 : W := mkw 0x25507b8006e005b6 0x04aa0f7000dc00b6 0xeff07f8007e007fa 0xfdfe0ff000fc00ff

def z885 : W := mkw 0x37da79e6be79af3e 0xa6fb4f3cd7cf35e7 0xaf93b1c7ec71fe3f 0xd5f27638fd8e3fc7

def z886 : W := mkw 0x25d07b80bee02db6 0x24ba0f7017dc05b6 0xfff3ffc7ffe07fff 0xfffe7ff8fffc0fff

def z887 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fffa0001ffffe3f 0xf3fff40003ffffc7

def z888 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87dfffff7fe7fff 0xbf0fbffffeffcfff

def z889 : W := mkw 0x08250659019642c1 0x4104a0cb2032c858 0xd86d4e78179e67c7 0xbb0da9cf02f3ccf8

def z890 : W := mkw 0x14f58d5b581b8369 0x829eb1ab6b03706d 0x30719f81f81f87fc 0x860e33f03f03f0ff

def z891 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87fdffff7ffffc7 0xbf0ffbfffefffff8

def z892 : W := mkw 0x08259659859676c1 0x4104b2cb30b2ced8 0xf86dde79979e7fc7 0xbf0dbbcf32f3cff8

def z893 : W := mkw 0x0025045901164241 0x0004a08b2022c848 0xf86d5e79979e67c7 0xbf0dabcf32f3ccf8

def z894 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9ffc00001ffff804 0xf3ff800003ffff00

def z895 : W := mkw 0x082516d985b666d5 0x4104a2db30b6ccda 0xf86d5e799ffe67ff 0xbf0dabcf33ffccff

def z896 : W := mkw 0x122f847f411fd249 0x8245f08fe823fa49 0x000f807fe01ff801 0x0001f00ffc03ff00

def z897 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ee7fffe0000003 0x7cfdcffffc000000

def z898 : W := mkw 0x0000108004200414 0x0000021000840082 0xa813b1c7ec71fe3f 0xd5027638fd8e3fc7

def z899 : W := mkw 0x032f6d3540000000 0x0065eda6a8000000 0xe7ef7fffe0000003 0xfcfdeffffc000000

def z900 : W := mkw 0x077fed3540091000 0x00effda6a8012200 0xe7ffffffe0019803 0xfcfffffffc003300

def z901 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1ff380001ffff804 0xc3fe700003ffff00

def z902 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fed00001ffff805 0xb3fda00003ffff00

def z903 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86f7fffff9fe7ff 0xff0deffffff3fcff

def z904 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0x506d4e38139e61c1 0x2a0da9c70273cc38

def z905 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xf07ffffff38e01c3 0xfe0ffffffe71c038

def z906 : W := mkw 0x08250659019642c1 0x4104a0cb2032c858 0x506c4e78139e01c1 0x2a0d89cf0273c038

def z907 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87fde79979e67c7 0xff0ffbcf32f3ccf8

def z908 : W := mkw 0x030a606e00128249 0x00614c0dc0025049 0xd78e607e181f87ff 0x7af1cc0fc303f0ff

def z909 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0x578c6038100e07fa 0x2af18c070201c0ff

def z910 : W := mkw 0x077fed3541044000 0x00effda6a8208800 0xf7fffffff38e0003 0xfefffffffe71c000

def z911 : W := mkw 0x0825165b8596e6c9 0x4104a2cb70b2dcd9 0xf87ffe7f9fffffff 0xff0fffcff3ffffff

def z912 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0xdff06e001fe007fe 0xfbfe0dc003fc00ff

def z913 : W := mkw 0x06ff8d115b4d5000 0x00dff1a22b69aa00 0x9fff8e001ffff805 0xf3fff1c003ffff00

def z914 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x2813b187ec71fe3c 0xc5027630fd8e3fc7

def z915 : W := mkw 0x138a606e381b8b69 0xa2714c0dc703716d 0xd78ee07e781f9fff 0x7af1dc0fcf03f3ff

def z916 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf06d5e79938e07c3 0xbe0dabcf3271c0f8

def z917 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x67f3ffffe0000002 0xccfe7ffffc000000

def z918 : W := mkw 0x077fed3541044000 0x00effda6a8208800 0xefffffffe7806003 0xfdfffffffcf00c00

def z919 : W := mkw 0x030a6d3540000000 0x00614da6a8000000 0xe79fffffe0000003 0xfcf3fffffc000000

def z920 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87dde7997fe7fc7 0xbf0fbbcf32ffcff8

def z921 : W := mkw 0x138a606e1a5b8369 0x82714c0dc34b706d 0xdf8e607e1fff87ff 0x7bf1cc0fc3fff0ff

def z922 : W := mkw 0x077fed3542401000 0x00effda6a8480200 0xe7ffffffe0601803 0xfcfffffffc0c0300

def z923 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0xd78e607e180e07ff 0x7af1cc0fc301c0ff

def z924 : W := mkw 0x190076ffa4b2affd 0xe3200edff49655ff 0x60007fffe00007fa 0x0c000ffffc0000ff

def z925 : W := mkw 0x0825165ba596eec9 0x6104a2cb74b2ddd9 0xf87ffffff79fffc7 0xff0ffffffef3fff8

def z926 : W := mkw 0x0c759f91e5a46c94 0x618eb3f23cb48d92 0x28719f81e7e07800 0x850e33f03cfc0f00

def z927 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0x586c4e38179e61c4 0x2b0d89c702f3cc38

def z928 : W := mkw 0x030a6d3540000000 0x00614da6a8000000 0x67827fffe0000002 0x4cf04ffffc000000

def z929 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86d7e799f9e67ff 0xff0dafcf33f3ccff

def z930 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86f5e799f9fe7c7 0xff0debcf33f3fcf8

def z931 : W := mkw 0x06da80001b4d5000 0x00db50000369aa00 0x1f8000001ffff804 0x03f0000003ffff00

def z932 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x67feffffe0000002 0x6cffdffffc000000

def z933 : W := mkw 0x06ff80245b4d5000 0x00dff0048b69aa00 0x9fff80067ffff805 0xf3fff000cfffff00

def z934 : W := mkw 0x008000001b4d5000 0x001000000369aa00 0x9f8000001ffff804 0x73f0000003ffff00

def z935 : W := mkw 0x075aed3540000000 0x00eb5da6a8000000 0xe7f2ffffe0000002 0xfcfe5ffffc000000

def z936 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xff9ff1fffc7fffff 0xfff3fe3fff8fffff

def z937 : W := mkw 0x2c759f91c7e46496 0x458eb3f238fc8c92 0x28719f81e7e06000 0x850e33f03cfc0c00

def z938 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fff8047fffff805 0xf3fff008ffffff00

def z939 : W := mkw 0x08251619858664c1 0x4104a2c330b0cc98 0xf86d5e39978e67c6 0xbf0dabc732f1ccf8

def z940 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff3ffc7fff1ffff 0xfffe7ff8fffe3fff

def z941 : W := mkw 0x17ffed3d5b4f5161 0x82fffda7ab69ea2c 0x57ec4e38138e01c0 0x2afd89c70271c038

def z942 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86c5e79978e07c6 0xbf0d8bcf32f1c0f8

def z943 : W := mkw 0x00000208008200c1 0x0000004100104018 0x506c4e38138e01c0 0x2a0d89c70271c038

def z944 : W := mkw 0x27ffef355bcd51a2 0x04fffde6ab79aa34 0x57ec4e38138e01c0 0x2afd89c70271c038

def z945 : W := mkw 0x082516d985b666d5 0x4104a2db30b6ccda 0xf86d7ff9979e67ff 0xbf0dafff32f3ccff

def z946 : W := mkw 0x000000822020881c 0x2000001044041103 0xa813b1c7ec71f83f 0xd5027638fd8e3f07

def z947 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xefffffffec600007 0xfdfffffffd8c0000

def z948 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xe873ffc7ec71fe3f 0xfd0e7ff8fd8e3fc7

def z949 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x2013b1c7e871fe3b 0x44027638fd0e3fc7

def z950 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x786d5e39979e67c4 0xaf0dabc732f3ccf8

def z951 : W := mkw 0x08251619858664c1 0x4104a2c330b0cc98 0x706c5e39938e01c0 0x2e0d8bc73271c038

def z952 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x178e207e181f87fd 0x42f1c40fc303f0ff

def z953 : W := mkw 0x0825165ba596eec9 0x6104a2cb74b2ddd9 0xf86d5e79979fffc7 0xbf0dabcf32f3fff8

def z954 : W := mkw 0x2c759f9187e47496 0x458eb3f230fc8e92 0x28719f8187e07800 0x850e33f030fc0f00

def z955 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x786d5e79978e67c2 0xaf0dabcf32f1ccf8

def z956 : W := mkw 0x138a606eb81bab69 0xa2714c0dd703756d 0xd78e607ff81f87ff 0x7af1cc0fff03f0ff

def z957 : W := mkw 0x138a606eb81bab69 0xa2714c0dd703756d 0xf79ff1fff81fffff 0xfef3fe3fff03ffff

def z958 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd79ee1fe781f87ff 0x7af3dc3fcf03f0ff

def z959 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86fde7fffffffff 0xbf0dfbcfffffffff

def z960 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff07fc7ffe007fe 0xfffe0ff8fffc00ff

def z961 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0xbfff90419ffff807 0xf7fff20833ffff00

def z962 : W := mkw 0x25d07b801ee905b6 0x04ba0f7003dd20b6 0xfff07f801fff87fe 0xfffe0ff003fff0ff

def z963 : W := mkw 0x00251248059646c1 0x0004a24900b2c8d8 0xf86d5e78179e67c7 0xbf0dabcf02f3ccf8

def z964 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86f7e7f9fffffff 0xff0defcff3ffffff

def z965 : W := mkw 0x0c759691a7e47c94 0x618eb2d234fc8f92 0x28719f81e7e07800 0x850e33f03cfc0f00

def z966 : W := mkw 0x1a2f847fc11fe249 0xc345f08ff823fc49 0x000f807fe01fe001 0x0001f00ffc03fc00

def z967 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xf78e71fff81f87ff 0x7ef1ce3fff03f0ff

def z968 : W := mkw 0x08251619058644c1 0x4104a2c320b0c898 0xf86d5e38179e67c7 0xbf0dabc702f3ccf8

def z969 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x77f07f801be007fa 0x6efe0ff0037c00ff

def z970 : W := mkw 0x018072801ca005b4 0x00300e50039400b6 0xfff07f801fe007fe 0xfffe0ff003fc00ff

def z971 : W := mkw 0x37da69a63a69893e 0xa6fb4d34c74d3127 0x0792a18668619838 0x40f25430cd0c3307

def z972 : W := mkw 0x000000c2a030aa1c 0x2000001854061543 0x8813a1c7ec71f83d 0xd1027438fd8e3f07

def z973 : W := mkw 0x08251659059646c1 0x4104a2cb20b2c8d8 0xf86c5e78179e07c7 0xbf0d8bcf02f3c0f8

def z974 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xe7ffffffe011f803 0xfcfffffffc023f00

def z975 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1ffd80001ffff804 0xa3ffb00003ffff00

def z976 : W := mkw 0x000012c2a4b0ae9c 0x20000258549615d3 0xb813b1c7fff1ffff 0xd7027638fffe3fff

def z977 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0xdfffc0001fffffc7 0xfbfff80003fffff8

def z978 : W := mkw 0x0180600818020161 0x00300c010300402c 0xd78c6038180e07fe 0x7af18c070301c0ff

def z979 : W := mkw 0x25d06b001ac001a2 0x04ba0d6003580034 0x57e06e00138007fa 0x2afc0dc0027000ff

def z980 : W := mkw 0x128a006e181b8369 0x8251400dc303706d 0x978e007e181f87fd 0x72f1c00fc303f0ff

def z981 : W := mkw 0x00251659049206c1 0x0004a2cb209240d8 0xf86d5e79979e07c7 0xbf0dabcf32f3c0f8

def z982 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff1ff801fe07ffe 0xfffe3ff003fc0fff

def z983 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff27fc61fe007ff 0xfffe4ff8c3fc00ff

def z984 : W := mkw 0x077fed3541044000 0x00effda6a8208800 0xfffffffffffff807 0xffffffffffffff00

def z985 : W := mkw 0x24759f9147e45496 0x048eb3f228fc8a92 0x28719f81e7e07800 0x850e33f03cfc0f00

def z986 : W := mkw 0x06ff89005b4d5000 0x00dff1200b69aa00 0x9fff81807ffff805 0xf3fff0300fffff00

def z987 : W := mkw 0x138a696e181b8369 0x82714d2dc303706d 0xf78e7ffe181f87ff 0x7ef1cfffc303f0ff

def z988 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff17f801ff067ff 0xfffe2ff003fe0cff

def z989 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78c607e180e07fe 0x7af18c0fc301c0ff

def z990 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86fde7ff79e67c7 0xbf0dfbcffef3ccf8

def z991 : W := mkw 0x08250659819662c1 0x4104a0cb3032cc58 0x506c4e79938e01c0 0x2a0d89cf3271c038

def z992 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86f7e7f979e67c7 0xff0defcff2f3ccf8

def z993 : W := mkw 0x29007fdba4b2afff 0x65200ffb749655ff 0x60007fffe00007fa 0x0c000ffffc0000ff

def z994 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0x586c4e381ffffffc 0x2b0d89c703ffffff

def z995 : W := mkw 0x24d01b801ee005b6 0x049a037003dc00b6 0xbff01f801fe007fc 0xf7fe03f003fc00ff

def z996 : W := mkw 0x02af00001b4d5000 0x0055e0000369aa00 0x9fef00001ffff805 0xf3fde00003ffff00

def z997 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fee00001ffff805 0x73fdc00003ffff00

def z998 : W := mkw 0x25d07ba45ee005b6 0x04ba0f748bdc00b6 0xfff07f867fe007fe 0xfffe0ff0cffc00ff

def z999 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xd06c4e38139e01c5 0x3a0d89c70273c038

def z1000 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd79fe07e181f87ff 0xfaf3fc0fc303f0ff

def z1001 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xd06c4e78138e01c3 0x3a0d89cf0271c038

def z1002 : W := mkw 0x082516d9a5b66ed5 0x6104a2db34b6cdda 0xf87dfff9fffe7fff 0xff0fbfff3fffcfff

def z1003 : W := mkw 0x077fed35410d5000 0x00effda6a821aa00 0xe7ffffffe00e0003 0xfcfffffffc01c000

def z1004 : W := mkw 0x08250659819662c1 0x4104a0cb3032cc58 0xf06d5e79939e61c3 0xbe0dabcf3273cc38

def z1005 : W := mkw 0x25d07b803ee00db6 0x24ba0f7007dc01b6 0xfff0ff807fe01ffe 0xfffe1ff00ffc03ff

def z1006 : W := mkw 0x082516d9a5b66ed5 0x6104a2db34b6cdda 0xf87fdff9ffffffc7 0xff0ffbff3ffffff8

def z1007 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xf78f707f981f87ff 0xfef1ee0ff303f0ff

def z1008 : W := mkw 0x08001659849226c1 0x410002cb309244d8 0xf86c5e79979e07c7 0xbf0d8bcf32f3c0f8

def z1009 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xdff04e001fe007fc 0xfbfe09c003fc00ff

def z1010 : W := mkw 0x030a6d3540000000 0x00614da6a8000000 0x678c7fffe0000002 0x2cf18ffffc000000

def z1011 : W := mkw 0x31007beea4b2afff 0xa6200f7dd49655ff 0x60007fffe00007fa 0x0c000ffffc0000ff

def z1012 : W := mkw 0x077fed3542400000 0x00effda6a8480000 0xefffffffe7e00003 0xfdfffffffcfc0000

def z1013 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff3ff801fe007ff 0xfffe7ff003fc00ff

def z1014 : W := mkw 0x37da69261a49812a 0x86fb4d24c3493025 0x0782200608018038 0x40f04400c1003007

def z1015 : W := mkw 0x038a6048181b0361 0x00714c090303606c 0xd78e6078181f87ff 0x7af1cc0f0303f0ff

def z1016 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78fe07e181fffff 0x7af1fc0fc303ffff

def z1017 : W := mkw 0x0025161105844480 0x0004a2c220b08890 0xf86d5e79979e67c7 0xbf0dabcf32f3ccf8

def z1018 : W := mkw 0x08250659019642c1 0x4104a0cb2032c858 0xf06d5e79939e07c7 0xbe0dabcf3273c0f8

def z1019 : W := mkw 0x0575ed3540000000 0x00aebda6a8000000 0xe7f1ffffe0000002 0xfcfe3ffffc000000

def z1020 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xe81ff1ffec71fe3f 0xfd03fe3ffd8e3fc7

def z1021 : W := mkw 0x028a00001b4d5000 0x005140000369aa00 0x9f9f80001ffff805 0xf3f3f00003ffff00

def z1022 : W := mkw 0x06da80001b4d5000 0x00db50000369aa00 0x9f9e80001ffff805 0x73f3d00003ffff00

def z1023 : W := mkw 0x038a606c18120361 0x00714c0d8302406c 0xd78e607e181e07ff 0x7af1cc0fc303c0ff

def z1024 : W := mkw 0x077fed3543445000 0x00effda6a8688a00 0xfffffffff7fe7807 0xfffffffffeffcf00

def z1025 : W := mkw 0x075aed3540000000 0x00eb5da6a8000000 0x67807fffe0000002 0x0cf00ffffc000000

def z1026 : W := mkw 0x028a004a181b8249 0x0051400943037049 0xd78e607e181f87ff 0x7af1cc0fc303f0ff

def z1027 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xffe05e001fe007fe 0xbffc0bc003fc00ff

def z1028 : W := mkw 0x032f643500000000 0x0065ec86a0000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1029 : W := mkw 0x082516d9a5b66ed5 0x6104a2db34b6cdda 0xf86d5ff9f79e67c7 0xbf0dabff3ef3ccf8

def z1030 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578c607e181f87fe 0x2af18c0fc303f0ff

def z1031 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86d7fffffffffff 0xbf0dafffffffffff

def z1032 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87fffffffffffc7 0xff0ffffffffffff8

def z1033 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578e607e180f87fa 0x6af1cc0fc301f0ff

def z1034 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1fff800017fff801 0xa3fff00002ffff00

def z1035 : W := mkw 0x082516d985b666d5 0x4104a2db30b6ccda 0xf87ffff99fffffff 0xff0fffff33ffffff

def z1036 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xefffffffe4106007 0xfdfffffffc820c00

def z1037 : W := mkw 0x067f841100000000 0x00cff08220000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1038 : W := mkw 0x038a602418090120 0x00714c0483012024 0xd78e607e181f87ff 0x7af1cc0fc303f0ff

def z1039 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x67efffffe0000003 0x2cfdfffffc000000

def z1040 : W := mkw 0x032fed3540000000 0x0065fda6a8000000 0xe78fffffe0000003 0x7cf1fffffc000000

def z1041 : W := mkw 0x138a602e180b8169 0x82714c05c301702d 0xd78e603e180f87fe 0x7af1cc07c301f0ff

def z1042 : W := mkw 0x0a2f845ba11ffa49 0x6145f08b7423ff49 0x000f807fe01ff801 0x0001f00ffc03ff00

def z1043 : W := mkw 0x0a2f847fe116ea49 0x6145f08ffc22dd49 0x000f807fe01ff801 0x0001f00ffc03ff00

def z1044 : W := mkw 0x138a606eb81bab69 0xa2714c0dd703756d 0xdf9fe07ffc7fffff 0xfbf3fc0fff8fffff

def z1045 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xdf8f607e1c1fe7ff 0xfbf1ec0fc383fcff

def z1046 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xf7ee7e7e181f87ff 0xfefdcfcfc303f0ff

def z1047 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x7ff05f801fe007fc 0xaffe0bf003fc00ff

def z1048 : W := mkw 0x067f800001044000 0x00cff00000208800 0x9fff80001ffff805 0xf3fff00003ffff00

def z1049 : W := mkw 0x08001248859666c1 0x4100024910b2ccd8 0xf86c5e78179e67c7 0xbf0d8bcf02f3ccf8

def z1050 : W := mkw 0x00001082a420ac1c 0x2000021054841583 0xa813b187ec61fe3e 0xd5027630fd8c3fc7

def z1051 : W := mkw 0x09007fffe4b2aedd 0x61200ffffc9655db 0x60007fffe00007fa 0x0c000ffffc0000ff

def z1052 : W := mkw 0x0825065ba196eac9 0x6104a0cb7432dd59 0x506fce7ff39ff9c1 0x2a0df9cffe73ff38

def z1053 : W := mkw 0x00001208048204c1 0x0000024100904098 0xf86c5e38178e07c6 0xbf0d8bc702f1c0f8

def z1054 : W := mkw 0x05d069001a400120 0x00ba0d2003480024 0xfff07f801fe007fe 0xfffe0ff003fc00ff

def z1055 : W := mkw 0x138a606c181b0361 0x82714c0d8303606c 0xd78c6078181e07ff 0x7af18c0f0303c0ff

def z1056 : W := mkw 0x138a606e1a5b9369 0x82714c0dc34b726d 0xd78e607e187f9fff 0x7af1cc0fc30ff3ff

def z1057 : W := mkw 0x05756d3540000000 0x00aeada6a8000000 0xe7fd7fffe0000003 0xfcffaffffc000000

def z1058 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86d7ffff79e67c7 0xbf0daffffef3ccf8

def z1059 : W := mkw 0x37dae9a61a69913e 0x86fb5d34c34d3227 0x0792a18608619838 0x40f25430c10c3307

def z1060 : W := mkw 0x138a606e981ba369 0x82714c0dd303746d 0xd78f607f981fe7ff 0x7af1ec0ff303fcff

def z1061 : W := mkw 0x082516d9a5b66ed5 0x6104a2db34b6cdda 0xf87ffffff7fe7fc7 0xff0ffffffeffcff8

def z1062 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0x706c5e79938e01c2 0x2e0d8bcf3271c038

def z1063 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xf7fffffff01e0007 0xfefffffffe03c000

def z1064 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf86d5e799fffffc7 0xbf0dabcf33fffff8

def z1065 : W := mkw 0x25d07ba41ee005b6 0x04ba0f7483dc00b6 0xfff07ffe1fe007fe 0xfffe0fffc3fc00ff

def z1066 : W := mkw 0x1180606e18128369 0x82300c0dc302506d 0xd78c607e181e07ff 0x7af18c0fc303c0ff

def z1067 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1ffe80001ffff804 0x63ffd00003ffff00

def z1068 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578e407e181f87fd 0x2af1c80fc303f0ff

def z1069 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xf813f1c7fc71ffff 0xff027e38ff8e3fff

def z1070 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78c607e101e07ff 0x3af18c0fc203c0ff

def z1071 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x786d5e79979e61c1 0xaf0dabcf32f3cc38

def z1072 : W := mkw 0x08251619058644c1 0x4104a2c320b0c898 0xf86d5e79978e07c7 0xbf0dabcf32f1c0f8

def z1073 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1fef80001ffff805 0x23fdf00003ffff00

def z1074 : W := mkw 0x075a692400000000 0x00eb4d2480000000 0xe7ffffffe0000003 0xfcfffffffc000000

def z1075 : W := mkw 0x37da69a41a690136 0x86fb4d34834d2026 0x0790218008600038 0x40f20430010c0007

def z1076 : W := mkw 0x06ff84115b4d5000 0x00dff0822b69aa00 0x9fff8001fffff805 0xf3fff0003fffff00

def z1077 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x57e04e00138007f8 0x2afc09c0027000ff

def z1078 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78e607e100e07fb 0x7af1cc0fc201c0ff

def z1079 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0xefffffffe4607803 0xfdfffffffc8c0f00

def z1080 : W := mkw 0x077fed3543445000 0x00effda6a8688a00 0xe7ffffffe3800003 0xfcfffffffc700000

def z1081 : W := mkw 0x00000248009202c1 0x0000004900124058 0xd06c4e78139e07c7 0x3a0d89cf0273c0f8

def z1082 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x1f9f80001ffff805 0x43f3f00003ffff00

def z1083 : W := mkw 0x138ae06e581b8369 0x82715c0dcb03706d 0xd78ee07e781f87ff 0x7af1dc0fcf03f0ff

def z1084 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xf7f07f80138007fa 0xfefe0ff0027000ff

def z1085 : W := mkw 0x06da00001a490000 0x00db400003492000 0x9fff80001ffff805 0xf3fff00003ffff00

def z1086 : W := mkw 0x06ff80241b4d5000 0x00dff0048369aa00 0x9fff807e1ffff805 0xf3fff00fc3ffff00

def z1087 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x0fff80000ffff801 0xc1fff00001ffff00

def z1088 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf87d7ffffffe67ff 0xff0fafffffffccff

def z1089 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xd06d4e38138e01c1 0xba0da9c70271c038

def z1090 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xf7e07f801b8007fe 0x7efc0ff0037000ff

def z1091 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xd87fce381ffff9c5 0xfb0ff9c703ffff38

def z1092 : W := mkw 0x08250659819662c1 0x4104a0cb3032cc58 0xd86d4e79979e61c5 0xbb0da9cf32f3cc38

def z1093 : W := mkw 0x21807b801ca005b6 0x04300f70039400b6 0xffe07f801f8007fe 0xfffc0ff003f000ff

def z1094 : W := mkw 0x00000082a020a81c 0x2000001054041503 0x0013a187e861f838 0x40027430fd0c3f07

def z1095 : W := mkw 0x082516d9a5b66ed5 0x6104a2db34b6cdda 0xf86d5e7997fe7fc7 0xbf0dabcf32ffcff8

def z1096 : W := mkw 0x24d012801ee005b6 0x049a025003dc00b6 0xfff05e001fe007fe 0xfffe0bc003fc00ff

def z1097 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xdfee607e1f9f87ff 0xfbfdcc0fc3f3f0ff

def z1098 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0xd78c4078181f87ff 0x3af1880f0303f0ff

def z1099 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0x9fffa1867ffff805 0xf3fff430cfffff00

def z1100 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0xb81fb1c7fc7ffe3f 0xf703f638ff8fffc7

def z1101 : W := mkw 0x218072801ee005b6 0x04300e5003dc00b6 0xffe07e001fe007fe 0xfffc0fc003fc00ff

def z1102 : W := mkw 0x077fed3540000000 0x00effda6a8000000 0x27ffbfffe0000001 0xc4fff7fffc000000

def z1103 : W := mkw 0x17dae9265a499128 0x82fb5d24cb493225 0x0792a18668619838 0x40f25430cd0c3307

def z1104 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0xfff1ff81ffe007fe 0xfffe3ff03ffc00ff

def z1105 : W := mkw 0x06ff8d355b4d5000 0x00dff1a6ab69aa00 0xbfff9ffffffff805 0xf7fff3ffffffff00

def z1106 : W := mkw 0x06ff84355b4d5000 0x00dff086ab69aa00 0x9fff80381ffff805 0xf3fff00703ffff00

def z1107 : W := mkw 0x08250659019642c1 0x4104a0cb2032c858 0x506c4e38139e07c4 0x2a0d89c70273c0f8

def z1108 : W := mkw 0x05d072001ec005a0 0x00ba0e4003d800b4 0xfff07e001fe007fe 0xfffe0fc003fc00ff

def z1109 : W := mkw 0x138a602c180b0161 0x82714c058301602c 0xd78e6038181f87ff 0x7af1cc070303f0ff

def z1110 : W := mkw 0x25d07b801ee005b6 0x04ba0f7003dc00b6 0x3ff03f801fe007fc 0xc7fe07f003fc00ff

def z1111 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0x506c4e38138e07c0 0x2a0d89c70271c0f8

def z1112 : W := mkw 0x000010caa432ae5d 0x20000219548655cb 0xe813f1ffec71ffff 0xdd027e3ffd8e3fff

def z1113 : W := mkw 0x0825165ba596eec9 0x6104a2cb74b2ddd9 0xf86ffe7fff9fffff 0xff0dffcffff3ffff

def z1114 : W := mkw 0x05506d3540000000 0x00aa0da6a8000000 0xe7f3ffffe0000003 0xfcfe7ffffc000000

def z1115 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x478e607e081f87fb 0x48f1cc0fc103f0ff

def z1116 : W := mkw 0x25d07b801ee915b6 0x04ba0f7003dd22b6 0xfff07f801fe19ffe 0xfffe0ff003fc33ff

def z1117 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578e607e101f87fb 0x2af1cc0fc203f0ff

def z1118 : W := mkw 0x06ff80001b4d5000 0x00dff0000369aa00 0xbfffb1801ffff807 0xf7fff63003ffff00

def z1119 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0x506d4e79938e01c1 0x2a0da9cf3271c038

def z1120 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0xd86c4e38178e01c4 0xbb0d89c702f1c038

def z1121 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xf87d5e799ffe67c7 0xff0fabcf33ffccf8

def z1122 : W := mkw 0x06ff84355b4d5000 0x00dff086ab69aa00 0xffffde7ffffff807 0xfffffbcfffffff00

def z1123 : W := mkw 0x082516db85b6e6dd 0x4104a2db70b6dcdb 0xf87f7fff9fffe7ff 0xff0feffff3fffcff

def z1124 : W := mkw 0x08251659859666c1 0x4104a2cb30b2ccd8 0xd86c4e78179e67c7 0x3b0d89cf02f3ccf8

def z1125 : W := mkw 0x138a606e181b8369 0x82714c0dc303706d 0x578c4038100e07f8 0x2af188070201c0ff

def z1126 : W := mkw 0x080012caa4b2aedd 0x61000259549655db 0xa813b1c7ec71ffff 0xd5027638fd8e3fff

def z1127 : W := mkw 0x000010c2a430ae1c 0x20000218548615c3 0x2813b1c7ec71f839 0xc5027638fd8e3f07

def z1128 : W := mkw 0x308012cabefbafff 0xa610025957df75ff 0x180000001ffffffc 0x0300000003ffffff

def z1129 : W := mkw 0x082516dba5b6eedd 0x6104a2db74b6dddb 0xf86ffffff79fffff 0xbf0dfffffef3ffff

def z1130 : W := mkw 0x1180604a181b8369 0x82300c094303706d 0xd78c6078181f87ff 0x7af18c0f0303f0ff

def z1131 : W := mkw 0x08250619018640c1 0x4104a0c32030c818 0x586d4e38178e61c0 0xab0da9c702f1cc38

def z1132 : W := mkw 0x082516d985b666d5 0x4104a2db30b6ccda 0xf87d5ff997fe67c7 0xbf0fabff32ffccf8

def z1133 : W := mkw 0x02af80001b4d5000 0x0055f0000369aa00 0x9f8f80001ffff805 0x73f1f00003ffff00

def z1134 : W := mkw 0x000010caa432ae5d 0x20000219548655cb 0xa81fb1ffec7ffe3f 0xd503f63ffd8fffc7

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z8,z6]),(0,[z0,z9,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z10,z6]),(0,[z0,z2,z3,z11,z12,z5,z6]),(0,[z0,z13,z2,z3,z4,z5,z6])],[(0,[z0,z14,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z12,z5,z15,z6])],[(0,[z0,z2,z3,z16,z12,z5,z6]),(0,[z17,z2,z3,z4,z5,z6,z18]),(0,[z19,z0,z2,z3,z4,z5,z6]),(0,[z0,z20,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z18,z21]),(0,[z22,z0,z2,z3,z23,z5,z6]),(0,[z0,z24,z2,z3,z4,z5,z6]),(0,[z25,z0,z2,z3,z4,z5,z6]),(0,[z0,z26,z2,z3,z4,z5,z27])],[(0,[z0,z28,z2,z3,z4,z5,z6])],[(1,[z22,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z16,z29,z5,z6]),(0,[z0,z2,z3,z30,z4,z5,z6]),(1,[z0,z31,z3,z4,z5,z32]),(0,[z0,z2,z3,z4,z5,z33,z6])],[(0,[z0,z2,z3,z4,z5,z34,z6]),(0,[z35,z0,z2,z3,z4,z36,z6]),(0,[z0,z2,z3,z4,z5,z6,z37])],[(0,[z0,z2,z3,z16,z8,z5,z6]),(0,[z0,z2,z38,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z40,z5,z6]),(0,[z0,z41,z2,z3,z4,z5,z6]),(1,[z0,z42,z3,z4,z5,z6])],[(0,[z43,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z44,z6]),(0,[z0,z45,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z46,z4,z5,z6]),(0,[z47,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z48]),(0,[z49,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z50,z5,z6]),(0,[z0,z2,z51,z52,z4,z5,z6]),(0,[z0,z2,z3,z53,z16,z5,z6]),(0,[z54,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z55]),(1,[z0,z2,z3,z5,z6,z56]),(0,[z0,z2,z3,z4,z5,z6,z57])],[(0,[z0,z58,z3,z52,z4,z5,z6]),(0,[z0,z59,z2,z4,z60,z5,z6]),(0,[z0,z2,z3,z4,z5,z61,z6])],[(0,[z0,z2,z3,z4,z62,z5,z6]),(0,[z0,z2,z3,z63,z4,z5,z6]),(0,[z64,z0,z2,z3,z4,z5,z6]),(0,[z0,z65,z2,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z67,z6])],[(0,[z0,z68,z2,z3,z4,z5,z6]),(0,[z0,z59,z2,z3,z39,z5,z6]),(0,[z0,z69,z2,z4,z60,z5,z6])],[(0,[z70,z2,z3,z4,z5,z6,z18]),(0,[z0,z2,z3,z4,z71,z5,z6])],[(0,[z72,z0,z2,z3,z4,z5,z6]),(0,[z17,z0,z2,z3,z16,z5,z6]),(0,[z0,z69,z2,z3,z39,z5,z6]),(0,[z0,z73,z2,z74,z4,z5,z6]),(0,[z0,z75,z2,z3,z4,z5,z6]),(0,[z0,z76,z2,z3,z4,z5,z6])],[(1,[z0,z77,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z16,z5,z6]),(0,[z78,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z79,z6]),(1,[z0,z26,z2,z3,z5,z27]),(0,[z0,z2,z3,z4,z5,z6,z80])]],
   [[(0,[z0,z2,z3,z4,z5,z81,z6]),(0,[z0,z2,z3,z4,z5,z6,z82]),(0,[z0,z59,z2,z4,z83,z5,z6]),(0,[z0,z31,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z84,z5,z6])],[(0,[z22,z70,z2,z3,z4,z5,z6]),(0,[z85,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z86,z4,z5,z6]),(0,[z87,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z56])],[(0,[z88,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z89,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z90]),(0,[z0,z2,z3,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z91,z6]),(1,[z92,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z93,z4,z5,z6])],[(0,[z0,z58,z2,z3,z4,z5,z6]),(0,[z0,z59,z2,z38,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z94,z6]),(0,[z0,z2,z3,z4,z5,z6,z95]),(1,[z0,z96,z2,z4,z83,z6]),(0,[z0,z2,z3,z97,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z98]),(0,[z99,z0,z77,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z100]),(0,[z0,z2,z3,z4,z101,z5,z6]),(0,[z0,z73,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z102,z5,z6]),(1,[z0,z2,z3,z103,z5,z6]),(0,[z0,z104,z2,z3,z4,z5,z6]),(0,[z0,z105,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z106])],[(0,[z107,z0,z2,z3,z4,z108,z6]),(1,[z0,z2,z3,z109,z5,z6]),(0,[z70,z0,z2,z3,z110,z5,z6]),(0,[z0,z111,z2,z52,z4,z5,z6]),(0,[z0,z69,z2,z38,z4,z5,z6])],[(0,[z112,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z113,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z114,z6]),(0,[z0,z2,z52,z4,z60,z5,z6]),(0,[z0,z2,z3,z4,z5,z115,z6])],[(0,[z0,z2,z3,z4,z5,z6,z116]),(0,[z70,z0,z2,z3,z4,z5,z18]),(0,[z0,z117,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z118,z2,z3,z4,z5,z6]),(0,[z119,z0,z2,z3,z4,z5,z6]),(0,[z0,z120,z2,z4,z5,z6,z21]),(1,[z0,z121,z2,z3,z4,z5])],[(0,[z70,z0,z2,z3,z16,z5,z6]),(0,[z0,z59,z3,z52,z4,z5,z6]),(0,[z0,z2,z3,z122,z4,z5,z6]),(0,[z0,z2,z3,z123,z4,z5,z6])],[(0,[z0,z2,z124,z3,z16,z5,z6]),(0,[z125,z0,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z126,z6]),(0,[z0,z127,z128,z2,z4,z5,z6])],[(0,[z0,z2,z3,z16,z5,z6,z82]),(0,[z0,z66,z2,z3,z4,z108,z6]),(0,[z129,z0,z2,z3,z4,z5,z6])],[(0,[z130,z0,z2,z3,z4,z5,z6]),(0,[z17,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z103,z5,z6]),(0,[z0,z2,z38,z3,z4,z5,z6]),(0,[z0,z131,z2,z3,z4,z132,z6])],[(0,[z133,z2,z124,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z39,z5,z6])],[(0,[z0,z134,z2,z3,z4,z5,z6])],[(0,[z0,z66,z2,z3,z4,z5,z135]),(0,[z0,z2,z3,z4,z5,z136,z6]),(0,[z0,z127,z2,z3,z4,z5,z32]),(0,[z0,z2,z3,z4,z5,z6,z137])]],
   [[(1,[z0,z2,z138,z4,z5,z6]),(0,[z0,z139,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z140,z6]),(0,[z0,z2,z3,z4,z5,z6,z141]),(0,[z0,z2,z3,z142,z4,z5,z114])],[(0,[z0,z143,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z144,z6])],[(0,[z145,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z6,z21]),(0,[z0,z2,z3,z146,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z147,z6]),(0,[z0,z2,z3,z4,z148,z5,z6]),(0,[z0,z2,z3,z149,z4,z5,z6]),(0,[z0,z127,z31,z3,z4,z5,z6]),(0,[z150,z0,z2,z3,z4,z5,z6])],[(0,[z0,z31,z3,z4,z5,z6,z32]),(0,[z0,z151,z2,z3,z4,z5,z6])],[(0,[z58,z2,z152,z3,z4,z5,z6]),(0,[z0,z2,z3,z153,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z154,z6]),(0,[z0,z155,z2,z3,z4,z5,z6]),(0,[z0,z156,z2,z3,z4,z5,z6]),(0,[z0,z118,z157,z2,z4,z5,z6]),(0,[z0,z158,z2,z3,z4,z5,z6])],[(0,[z0,z159,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z6,z27]),(1,[z0,z2,z3,z4,z160,z6]),(0,[z0,z157,z2,z3,z4,z8,z6]),(1,[z0,z2,z38,z161,z5,z6])],[(1,[z0,z2,z3,z162,z5,z6]),(0,[z0,z163,z2,z3,z4,z5,z6]),(0,[z164,z0,z2,z3,z4,z5,z6]),(0,[z165,z0,z2,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z166,z6]),(0,[z0,z167,z7,z3,z4,z5,z6]),(0,[z0,z2,z3,z168,z4,z5,z6]),(0,[z0,z26,z66,z2,z3,z4,z5])],[(0,[z70,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z169,z36,z6]),(0,[z0,z2,z170,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z124,z3,z39,z5,z6]),(0,[z125,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z171]),(0,[z35,z0,z2,z3,z5,z15,z6])],[(0,[z0,z26,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z172,z5,z6]),(0,[z0,z173,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z174])],[],[(1,[z0,z2,z3,z4,z175,z6]),(1,[z133,z2,z124,z4,z5,z6]),(0,[z0,z176,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z36,z6]),(0,[z0,z2,z3,z177,z4,z5,z6]),(0,[z178,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z179,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z180,z6]),(0,[z0,z2,z3,z142,z5,z114,z6])],[(0,[z0,z2,z3,z162,z4,z5,z6]),(0,[z0,z2,z3,z4,z181,z5,z6]),(0,[z0,z2,z3,z53,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z182,z6]),(0,[z0,z2,z3,z39,z5,z183,z6])],[(0,[z107,z2,z3,z4,z16,z5,z6]),(0,[z0,z2,z3,z4,z83,z169,z6]),(0,[z0,z2,z3,z4,z5,z184,z6]),(0,[z0,z2,z3,z4,z5,z185,z6])],[(0,[z0,z2,z3,z186,z4,z5,z6]),(0,[z0,z69,z2,z3,z161,z5,z6]),(0,[z0,z2,z3,z4,z187,z5,z6])],[(0,[z0,z2,z3,z4,z5,z188,z6]),(0,[z0,z2,z3,z110,z4,z5,z6]),(0,[z0,z189,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z190,z6]),(0,[z0,z96,z2,z3,z4,z83,z6])]],
   [[(0,[z0,z2,z191,z3,z4,z5,z6]),(0,[z0,z31,z2,z3,z4,z5,z183]),(0,[z0,z192,z2,z3,z4,z5,z6])],[(0,[z0,z193,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z194]),(0,[z0,z195,z2,z3,z4,z5,z6]),(0,[z0,z2,z196,z3,z4,z5,z6])],[(0,[z0,z2,z3,z3,z4,z5,z6]),(0,[z197,z0,z2,z3,z198,z5,z6]),(0,[z0,z199,z2,z3,z4,z5,z6])],[(0,[z17,z2,z3,z4,z5,z169,z6]),(0,[z0,z2,z3,z4,z5,z200,z6]),(0,[z201,z0,z2,z3,z4,z5,z6])],[(0,[z202,z0,z2,z3,z4,z5,z6]),(0,[z203,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z204,z5,z6])],[(0,[z0,z2,z3,z4,z108,z36,z6]),(0,[z0,z111,z2,z3,z4,z5,z6]),(0,[z0,z3,z30,z4,z29,z5,z6]),(0,[z0,z2,z3,z4,z5,z205,z6])],[(0,[z0,z117,z2,z3,z16,z5,z6]),(0,[z17,z107,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z206,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z207]),(0,[z0,z2,z3,z4,z208,z5,z6])],[(0,[z0,z2,z3,z16,z5,z182,z6]),(1,[z0,z2,z74,z4,z5,z6]),(0,[z0,z2,z3,z209,z4,z5,z6])]],
   [[(0,[z210,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z211]),(0,[z0,z73,z2,z3,z4,z5,z6]),(0,[z0,z212,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z213,z5,z6])],[(0,[z0,z214,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z6,z32]),(0,[z0,z69,z215,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z216,z5,z6]),(0,[z0,z96,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z217,z27])],[(0,[z218,z0,z2,z138,z4,z5,z6]),(0,[z0,z219,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z220]),(0,[z99,z0,z2,z51,z4,z5,z6]),(0,[z221,z0,z2,z3,z4,z5,z6]),(0,[z0,z222,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z223]),(0,[z0,z224,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z225]),(0,[z0,z2,z3,z4,z5,z6,z226])],[(1,[z125,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z227,z5,z6]),(0,[z35,z92,z2,z3,z4,z5,z6]),(0,[z0,z228,z2,z3,z4,z5,z6]),(0,[z0,z229,z2,z3,z4,z6,z27])],[(0,[z0,z31,z2,z3,z39,z5,z6]),(0,[z230,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z67,z5,z36])],[(0,[z0,z2,z3,z4,z5,z231,z6]),(0,[z0,z2,z232,z3,z16,z5,z6]),(0,[z233,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z234]),(0,[z0,z2,z3,z4,z5,z6,z235]),(0,[z0,z2,z3,z4,z236,z5,z6])]],
   [[(0,[z218,z0,z2,z3,z162,z5,z6]),(0,[z0,z2,z3,z237,z4,z5,z6]),(0,[z0,z238,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z239,z5,z6]),(0,[z0,z2,z3,z240,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z241,z6])],[],[(0,[z0,z2,z77,z3,z4,z5,z6]),(0,[z0,z2,z3,z242,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z243,z6]),(0,[z244,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z245,z5,z6]),(0,[z0,z117,z2,z3,z39,z5,z6]),(0,[z246,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z38,z161,z4,z5,z6]),(0,[z0,z96,z247,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z248,z5,z6])],[(0,[z218,z0,z2,z3,z4,z175,z6]),(0,[z0,z2,z3,z4,z16,z5,z6]),(0,[z17,z2,z3,z39,z4,z5,z6]),(1,[z0,z111,z52,z4,z5,z6]),(0,[z0,z167,z59,z2,z4,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z140]),(0,[z0,z249,z2,z3,z4,z5,z6])],[(0,[z0,z250,z2,z3,z4,z5,z6]),(0,[z0,z251,z2,z3,z4,z5,z6]),(0,[z252,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z253,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z254,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z217])]],
   [[(0,[z0,z2,z3,z255,z4,z5,z6]),(0,[z256,z0,z58,z3,z4,z5,z6]),(1,[z0,z2,z122,z4,z5,z6])],[(0,[z257,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z67,z5,z6]),(0,[z258,z0,z2,z3,z4,z5,z6]),(0,[z259,z0,z2,z3,z4,z5,z6]),(0,[z0,z127,z2,z260,z4,z5,z6])],[(0,[z0,z261,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z6,z18]),(0,[z107,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z262,z6]),(0,[z0,z31,z3,z52,z4,z5,z6]),(1,[z0,z73,z3,z29,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z263]),(0,[z0,z2,z3,z4,z264,z5,z6])],[(0,[z0,z2,z3,z4,z265,z5,z6]),(0,[z0,z2,z3,z39,z5,z266,z6])],[(1,[z0,z2,z3,z267,z5,z6]),(0,[z0,z2,z3,z268,z4,z5,z6]),(0,[z269,z0,z2,z3,z4,z5,z6]),(1,[z0,z127,z3,z4,z5,z183]),(0,[z0,z2,z3,z270,z4,z5,z6])],[(0,[z271,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z108,z5,z6]),(0,[z0,z59,z111,z2,z4,z5,z6]),(0,[z0,z272,z2,z3,z30,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z21]),(0,[z0,z26,z2,z3,z4,z5,z6]),(0,[z0,z2,z273,z3,z4,z5,z6])],[(0,[z0,z2,z3,z11,z16,z5,z6]),(0,[z0,z274,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z275,z4,z5,z6])],[(0,[z0,z276,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z277,z5,z6]),(0,[z0,z2,z3,z16,z245,z5,z6]),(0,[z0,z278,z2,z3,z4,z5,z6]),(0,[z0,z69,z253,z3,z4,z5,z6]),(1,[z0,z117,z2,z4,z5,z140])]],
   [[(0,[z0,z2,z3,z16,z16,z5,z6]),(0,[z279,z0,z2,z3,z4,z5,z6]),(0,[z0,z215,z2,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z280,z6]),(0,[z0,z2,z3,z4,z5,z135,z6]),(0,[z0,z2,z3,z4,z5,z6,z281])],[(0,[z282,z0,z2,z3,z4,z5,z6]),(0,[z0,z283,z2,z3,z4,z5,z6])],[(0,[z197,z0,z2,z3,z103,z5,z6]),(0,[z107,z0,z2,z3,z4,z5,z284]),(0,[z0,z2,z3,z4,z285,z5,z6])],[(0,[z218,z0,z58,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z267,z5,z6]),(0,[z0,z286,z2,z3,z4,z5,z6]),(0,[z0,z111,z2,z3,z16,z5,z6]),(0,[z0,z287,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z288]),(0,[z0,z2,z3,z39,z5,z15,z6]),(0,[z0,z2,z3,z4,z5,z166,z6]),(0,[z0,z2,z3,z4,z5,z289,z6]),(0,[z0,z2,z3,z142,z4,z67,z5])],[(0,[z0,z2,z3,z4,z5,z290,z6]),(0,[z0,z2,z3,z16,z265,z5,z6]),(0,[z0,z2,z3,z4,z291,z5,z6])],[(0,[z0,z2,z3,z4,z292,z5,z6]),(0,[z0,z2,z3,z4,z277,z5,z6]),(0,[z0,z2,z3,z16,z5,z6,z57]),(0,[z107,z0,z2,z3,z4,z169,z6]),(0,[z0,z2,z3,z4,z5,z293,z6]),(0,[z0,z2,z3,z294,z4,z5,z6]),(0,[z92,z0,z2,z3,z4,z5,z6])]],
   [[(0,[z133,z0,z2,z51,z4,z5,z6]),(0,[z0,z2,z3,z295,z4,z5,z6]),(0,[z0,z2,z3,z4,z296,z5,z6]),(0,[z0,z96,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z177,z39,z5,z6]),(0,[z0,z2,z297,z3,z4,z5,z6])],[(0,[z0,z73,z3,z4,z29,z5,z6]),(0,[z0,z2,z3,z4,z298,z5,z6]),(0,[z0,z2,z3,z11,z4,z15,z6]),(0,[z0,z2,z3,z4,z5,z299,z6]),(0,[z300,z26,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z301,z6])],[(0,[z0,z2,z3,z4,z302,z5,z6]),(0,[z256,z0,z2,z3,z267,z5,z6]),(0,[z0,z2,z3,z4,z5,z303,z6]),(0,[z0,z2,z304,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z305,z5,z6]),(0,[z0,z2,z3,z4,z5,z306,z6]),(0,[z0,z2,z3,z4,z5,z307,z6]),(0,[z0,z308,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z309])],[(1,[z0,z2,z3,z153,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z310]),(0,[z0,z2,z311,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z312,z5,z6]),(0,[z0,z313,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z16,z5,z135,z6]),(1,[z70,z2,z3,z4,z5,z18]),(0,[z0,z2,z314,z3,z4,z5,z6]),(0,[z315,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z316,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z290]),(0,[z0,z66,z2,z3,z4,z169,z6]),(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z60,z5,z6])],[(0,[z0,z2,z3,z4,z5,z135,z32]),(0,[z0,z2,z3,z4,z317,z5,z6]),(1,[z0,z2,z3,z4,z67,z36])],[(0,[z0,z2,z52,z4,z83,z5,z6]),(0,[z0,z2,z3,z4,z318,z5,z6]),(0,[z0,z2,z3,z4,z319,z5,z6])]],
   [[(0,[z320,z0,z2,z3,z4,z5,z6]),(0,[z321,z0,z2,z3,z4,z5,z6]),(0,[z0,z31,z2,z3,z4,z5,z32]),(0,[z0,z2,z3,z4,z5,z132,z6])],[(1,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z322,z5,z6]),(0,[z0,z323,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z36,z6,z57])],[(0,[z99,z0,z2,z3,z4,z5,z290]),(0,[z0,z2,z232,z3,z4,z5,z6]),(0,[z0,z324,z2,z3,z4,z5,z6]),(0,[z0,z111,z2,z3,z39,z5,z6]),(0,[z0,z325,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z326,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z327,z6]),(0,[z0,z328,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z329,z5,z6]),(0,[z0,z2,z3,z4,z5,z330,z6]),(0,[z0,z2,z3,z4,z83,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z331]),(0,[z0,z2,z3,z4,z5,z332,z15])],[(0,[z333,z0,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z334,z6])],[(0,[z0,z335,z2,z3,z39,z5,z6]),(0,[z0,z73,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z336,z5,z6]),(0,[z0,z337,z2,z3,z5,z6,z57])],[(0,[z99,z0,z2,z3,z4,z5,z6]),(0,[z0,z96,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z338,z5,z6]),(0,[z0,z7,z3,z4,z5,z327,z6])],[(0,[z0,z2,z3,z242,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z16,z60,z5,z6]),(0,[z0,z2,z3,z4,z160,z5,z6]),(1,[z339,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z340])],[(0,[z341,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z4,z5,z6]),(0,[z107,z0,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z342,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z183,z135]),(0,[z0,z343,z2,z3,z4,z5,z6]),(0,[z0,z157,z2,z122,z4,z5,z6]),(0,[z0,z2,z38,z3,z161,z5,z6]),(0,[z0,z339,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z344]),(0,[z0,z2,z3,z4,z67,z5,z57])],[(0,[z0,z2,z3,z4,z5,z345,z6]),(0,[z0,z2,z3,z4,z342,z5,z6]),(0,[z346,z0,z2,z3,z39,z5,z6]),(0,[z197,z0,z2,z3,z4,z169,z6]),(1,[z0,z2,z3,z4,z5,z284]),(0,[z0,z96,z2,z4,z83,z5,z6]),(0,[z347,z0,z2,z3,z4,z5,z6])],[(1,[z99,z2,z51,z4,z5,z6]),(0,[z0,z2,z3,z348,z4,z5,z6]),(0,[z0,z349,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z16,z5,z132,z6]),(0,[z197,z0,z2,z3,z4,z108,z6]),(0,[z0,z350,z2,z3,z4,z5,z6]),(0,[z0,z351,z2,z3,z4,z5,z6])],[(0,[z0,z167,z3,z4,z5,z183,z6]),(1,[z0,z247,z3,z4,z5,z6])],[(0,[z0,z2,z3,z352,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z5,z18]),(0,[z0,z2,z3,z353,z4,z5,z6]),(1,[z0,z337,z2,z3,z5,z6]),(0,[z0,z2,z3,z5,z6,z56,z57])],[(0,[z0,z2,z3,z4,z354,z5,z6]),(0,[z0,z2,z3,z16,z83,z5,z6]),(0,[z0,z2,z3,z4,z355,z5,z6]),(0,[z0,z2,z3,z4,z356,z5,z6]),(0,[z0,z2,z3,z4,z5,z357,z6])],[(0,[z256,z0,z2,z3,z4,z5,z6]),(0,[z218,z0,z2,z3,z4,z5,z288]),(0,[z0,z358,z2,z3,z16,z5,z6]),(0,[z0,z66,z2,z3,z16,z5,z6]),(0,[z0,z111,z3,z52,z4,z5,z6]),(0,[z0,z167,z272,z3,z4,z5,z6]),(0,[z0,z359,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z59,z2,z51,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z360,z6]),(0,[z0,z2,z3,z361,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z362,z6])],[(0,[z363,z0,z2,z3,z4,z5,z6])],[(0,[z133,z0,z2,z3,z277,z5,z6]),(0,[z0,z2,z3,z4,z364,z5,z6]),(0,[z0,z365,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z11,z4,z5,z6]),(0,[z35,z0,z2,z3,z4,z15,z6]),(0,[z0,z366,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z39,z5,z327,z6]),(1,[z107,z2,z3,z4,z108,z6]),(0,[z0,z73,z2,z353,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z367,z6]),(0,[z0,z2,z3,z4,z5,z6,z368])],[(0,[z0,z2,z3,z4,z5,z369,z6]),(0,[z0,z2,z3,z4,z5,z183,z18]),(0,[z0,z370,z2,z3,z4,z5,z6])],[(0,[z256,z0,z152,z3,z4,z5,z6]),(1,[z256,z58,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z371,z6])],[(0,[z0,z2,z3,z372,z4,z5,z6]),(1,[z17,z2,z3,z39,z5,z6]),(0,[z107,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z373,z6]),(0,[z0,z2,z3,z4,z374,z5,z6]),(0,[z0,z375,z2,z3,z4,z5,z6]),(0,[z0,z376,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z377,z5,z6]),(0,[z0,z26,z2,z3,z5,z6,z27])]],
   [[(0,[z0,z2,z378,z3,z4,z5,z6]),(0,[z0,z2,z379,z3,z4,z5,z6]),(0,[z0,z131,z2,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z380,z6]),(0,[z0,z381,z96,z3,z4,z5,z6]),(1,[z300,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z382,z5,z6]),(0,[z0,z2,z3,z161,z16,z5,z6]),(0,[z0,z2,z3,z4,z383,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z384])],[(0,[z0,z26,z2,z3,z39,z5,z6]),(0,[z0,z272,z2,z3,z29,z5,z6]),(0,[z0,z2,z3,z385,z4,z5,z6]),(0,[z0,z2,z3,z4,z386,z5,z6]),(0,[z387,z0,z2,z3,z4,z5,z6]),(0,[z0,z388,z2,z3,z4,z5,z6])],[(0,[z218,z0,z2,z3,z4,z5,z6]),(0,[z0,z335,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z169,z6]),(0,[z0,z2,z3,z389,z4,z5,z6]),(0,[z0,z2,z3,z4,z390,z5,z6]),(0,[z0,z391,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z392,z6]),(0,[z393,z0,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z16,z5,z6]),(1,[z0,z2,z3,z110,z5,z6]),(0,[z0,z394,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z395,z4,z5,z6])],[(0,[z0,z396,z2,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z39,z5,z6]),(0,[z0,z397,z2,z3,z4,z5,z6]),(0,[z0,z2,z42,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z6,z57])],[(0,[z133,z0,z2,z3,z153,z5,z6]),(0,[z0,z398,z2,z3,z4,z5,z6])],[(0,[z0,z59,z2,z4,z5,z140,z6]),(0,[z0,z26,z2,z3,z142,z5,z6])]],
   [[(1,[z0,z2,z3,z16,z5,z6]),(0,[z346,z0,z2,z3,z4,z5,z6]),(0,[z399,z0,z2,z3,z4,z5,z6]),(1,[z0,z229,z2,z3,z4,z6])],[(0,[z218,z0,z152,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z4,z392,z6]),(0,[z0,z0,z2,z3,z16,z5,z6]),(0,[z0,z287,z2,z3,z39,z5,z6]),(0,[z0,z400,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z401]),(0,[z402,z0,z2,z3,z4,z5,z6]),(0,[z0,z403,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z404,z6])],[(0,[z405,z0,z2,z3,z4,z5,z6]),(0,[z0,z157,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z406,z6]),(0,[z0,z2,z3,z142,z4,z5,z27])],[(0,[z0,z167,z58,z3,z4,z5,z6]),(0,[z0,z2,z407,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z8,z108,z6]),(0,[z0,z2,z3,z4,z408,z5,z6])],[(0,[z0,z409,z2,z3,z4,z5,z6]),(0,[z133,z0,z2,z3,z4,z5,z6]),(0,[z410,z0,z2,z3,z4,z5,z6]),(0,[z35,z0,z26,z2,z3,z5,z6]),(0,[z0,z2,z3,z4,z5,z114,z6])],[(0,[z0,z411,z2,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z295,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z412,z6]),(0,[z0,z59,z120,z2,z4,z5,z6]),(0,[z0,z413,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z414]),(0,[z0,z2,z3,z4,z5,z415,z6])],[(0,[z0,z2,z3,z4,z416,z5,z6]),(0,[z0,z417,z2,z3,z4,z5,z6]),(0,[z0,z157,z2,z3,z4,z327,z6]),(0,[z0,z2,z3,z418,z4,z5,z6]),(0,[z0,z419,z2,z3,z4,z5,z6])]],
   [[(0,[z333,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z420,z5,z6]),(0,[z0,z3,z52,z4,z5,z183,z6]),(0,[z421,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z39,z12,z5,z6]),(1,[z197,z2,z3,z4,z169,z6]),(0,[z0,z2,z161,z4,z60,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z422])],[(0,[z0,z7,z2,z3,z39,z5,z6]),(0,[z0,z167,z2,z52,z4,z5,z6]),(0,[z0,z423,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z424,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z425]),(0,[z0,z2,z74,z3,z4,z5,z6])],[(1,[z0,z2,z3,z4,z5,z231]),(0,[z0,z426,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z29,z5,z6]),(0,[z0,z2,z3,z4,z5,z427,z6]),(0,[z35,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z352,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z332,z6])],[(0,[z0,z2,z3,z428,z4,z5,z6]),(0,[z0,z2,z3,z39,z8,z5,z6]),(0,[z0,z429,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z430,z6]),(0,[z0,z2,z431,z3,z4,z5,z6]),(0,[z0,z432,z2,z3,z4,z5,z6])],[(0,[z256,z0,z2,z3,z16,z5,z6]),(0,[z433,z0,z2,z3,z4,z5,z6]),(1,[z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z434,z5,z6]),(0,[z0,z435,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z288]),(0,[z0,z436,z2,z3,z4,z5,z6]),(0,[z0,z349,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z114,z6]),(0,[z0,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z437,z5,z6]),(0,[z0,z438,z2,z3,z4,z5,z6]),(0,[z0,z2,z439,z3,z4,z5,z6]),(0,[z0,z121,z2,z3,z4,z5,z15])]],
   [[(0,[z0,z440,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z441,z4,z5,z6]),(0,[z22,z2,z3,z4,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z442]),(0,[z443,z0,z2,z3,z4,z5,z6])],[(0,[z444,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z312,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z445])],[(1,[z0,z2,z3,z292,z5,z6]),(0,[z0,z446,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z447,z5,z6]),(0,[z0,z2,z3,z4,z5,z448,z6]),(0,[z35,z339,z2,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z5,z36])],[(0,[z99,z0,z2,z3,z39,z5,z6]),(0,[z449,z0,z2,z3,z4,z5,z6]),(0,[z0,z358,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z27])],[(0,[z0,z2,z3,z4,z5,z450,z6]),(0,[z0,z451,z2,z3,z4,z5,z6]),(0,[z0,z452,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z302,z5,z6]),(1,[z0,z2,z3,z4,z81,z6]),(0,[z453,z0,z2,z3,z4,z5,z6]),(0,[z0,z454,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z455,z6]),(0,[z0,z2,z3,z456,z4,z5,z6])],[(0,[z0,z457,z2,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z292,z5,z6]),(0,[z0,z7,z3,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z458,z5,z6]),(0,[z0,z131,z96,z2,z4,z5,z6]),(0,[z35,z0,z66,z2,z3,z4,z6])]],
   [[(0,[z459,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z460,z4,z5,z6]),(0,[z461,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z407,z3,z4,z5,z6]),(0,[z0,z2,z3,z462,z4,z5,z6]),(0,[z0,z2,z3,z463,z4,z5,z6]),(0,[z0,z464,z2,z3,z4,z5,z6]),(0,[z465,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z36,z6])],[(0,[z466,z0,z2,z3,z4,z5,z6]),(0,[z218,z0,z2,z3,z16,z5,z6]),(0,[z0,z120,z2,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z183,z6]),(0,[z0,z2,z3,z4,z467,z5,z6]),(0,[z0,z2,z3,z11,z4,z12,z6])],[(0,[z0,z2,z152,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z6,z21]),(0,[z0,z73,z2,z3,z30,z5,z6])],[(0,[z256,z0,z2,z3,z39,z5,z6]),(0,[z22,z2,z3,z4,z5,z135,z6]),(1,[z0,z2,z353,z4,z5,z6])],[(0,[z468,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z469,z5,z6]),(0,[z0,z2,z3,z4,z5,z470,z6]),(0,[z0,z2,z3,z161,z4,z5,z6]),(0,[z0,z471,z2,z3,z4,z5,z6]),(0,[z0,z472,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z16,z5,z6,z27]),(0,[z0,z117,z370,z3,z4,z5,z6])],[(0,[z0,z473,z2,z3,z4,z5,z6]),(0,[z0,z474,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z475,z3,z4,z5,z6]),(0,[z197,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z18,z32]),(0,[z0,z2,z3,z4,z5,z476,z6]),(0,[z0,z26,z2,z3,z4,z5,z114])],[(0,[z0,z157,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z140,z135]),(0,[z0,z2,z3,z4,z5,z6,z477]),(0,[z478,z0,z2,z3,z4,z5,z6]),(0,[z0,z479,z2,z3,z4,z5,z6])],[(0,[z0,z2,z480,z3,z4,z5,z6]),(0,[z0,z481,z2,z3,z4,z5,z6]),(0,[z0,z117,z2,z3,z4,z5,z140])],[(0,[z133,z0,z2,z3,z16,z5,z6]),(0,[z107,z2,z3,z4,z108,z5,z6]),(0,[z0,z482,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z483]),(0,[z0,z2,z3,z4,z5,z6,z484])],[(0,[z0,z2,z3,z16,z5,z36,z6]),(0,[z0,z2,z3,z4,z5,z6,z284]),(0,[z0,z2,z3,z4,z485,z5,z6]),(1,[z0,z2,z3,z11,z12,z6])],[(0,[z0,z0,z2,z3,z4,z5,z6]),(0,[z218,z0,z2,z3,z4,z5,z231]),(0,[z486,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z183,z6]),(0,[z0,z487,z2,z3,z4,z5,z6]),(0,[z0,z488,z2,z3,z4,z5,z6]),(0,[z0,z157,z3,z4,z8,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z489]),(0,[z0,z490,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z39,z102,z5,z6]),(0,[z0,z491,z2,z3,z4,z5,z6]),(1,[z0,z157,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z492,z6]),(0,[z35,z0,z2,z3,z11,z5,z6]),(0,[z35,z0,z2,z3,z5,z114,z6])],[(0,[z0,z2,z3,z39,z5,z140,z6]),(0,[z444,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z493,z4,z5,z6]),(0,[z0,z272,z2,z3,z4,z5,z6]),(0,[z0,z494,z2,z3,z4,z5,z6])]],
   [[(0,[z218,z0,z2,z3,z39,z5,z6]),(0,[z0,z152,z3,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z495,z5,z6])],[(0,[z0,z2,z138,z3,z4,z5,z6]),(0,[z496,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z497,z6]),(0,[z0,z128,z2,z3,z4,z5,z6]),(0,[z0,z498,z2,z3,z4,z5,z6]),(0,[z0,z499,z2,z3,z4,z5,z6])],[(0,[z35,z0,z2,z3,z16,z5,z6]),(0,[z0,z167,z2,z3,z4,z5,z6]),(0,[z0,z500,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z501,z4,z5,z6])],[(0,[z0,z2,z3,z4,z502,z5,z6]),(0,[z503,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z260,z4,z5,z6]),(1,[z0,z128,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z504,z6]),(0,[z0,z505,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z506,z5,z6]),(0,[z0,z2,z3,z4,z5,z507,z6])],[(0,[z0,z2,z3,z5,z114,z6,z27])],[(0,[z0,z2,z3,z4,z5,z508,z6]),(0,[z70,z0,z2,z3,z109,z5,z6]),(0,[z0,z509,z2,z3,z4,z5,z6])],[(0,[z218,z0,z2,z3,z302,z5,z6]),(0,[z218,z0,z2,z3,z4,z81,z6]),(0,[z0,z157,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z510]),(0,[z0,z120,z2,z3,z4,z5,z21])]],
   [[(0,[z0,z167,z152,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z511,z5,z6])],[(0,[z133,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z512]),(0,[z0,z2,z3,z4,z5,z513,z6]),(0,[z300,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z169,z327,z6]),(0,[z0,z514,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z515,z5,z6]),(0,[z0,z2,z3,z4,z5,z516,z6])],[(0,[z0,z2,z3,z4,z5,z517,z6]),(0,[z35,z0,z2,z3,z4,z12,z6]),(0,[z0,z2,z518,z3,z4,z5,z6])],[(0,[z218,z2,z152,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z160,z6]),(1,[z22,z2,z3,z4,z5,z135]),(0,[z0,z2,z3,z4,z519,z5,z6]),(0,[z0,z520,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z521,z6]),(0,[z0,z2,z3,z4,z5,z522,z6]),(0,[z0,z2,z523,z3,z4,z5,z6]),(0,[z333,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z524,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z525,z6]),(0,[z0,z2,z3,z4,z526,z5,z6]),(0,[z0,z527,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z528,z4,z5,z6]),(0,[z0,z2,z3,z529,z4,z5,z6]),(0,[z26,z530,z2,z3,z4,z5,z6])],[(0,[z218,z256,z2,z3,z4,z5,z6]),(0,[z531,z0,z2,z3,z4,z5,z6]),(0,[z0,z532,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z16,z5,z6,z18]),(0,[z0,z2,z3,z39,z5,z154,z6]),(0,[z107,z0,z2,z3,z447,z5,z6]),(1,[z0,z2,z3,z23,z5,z6]),(0,[z533,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z534,z4,z5,z6]),(0,[z0,z131,z2,z3,z16,z5,z6]),(0,[z459,z0,z2,z3,z16,z5,z6]),(0,[z2,z3,z4,z108,z5,z169,z6]),(0,[z535,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z536,z6]),(0,[z0,z2,z3,z4,z537,z5,z6])]],
   [[(0,[z0,z426,z2,z3,z39,z5,z6]),(0,[z35,z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z18]),(0,[z0,z121,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z67,z36,z6])],[(0,[z0,z538,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z266,z6]),(0,[z0,z2,z38,z52,z4,z5,z6]),(1,[z0,z118,z2,z4,z5,z6]),(1,[z0,z215,z3,z4,z5,z6]),(1,[z0,z120,z2,z4,z5,z21])],[(0,[z0,z2,z152,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z539,z6]),(0,[z0,z540,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z541,z4,z5,z6])],[(0,[z0,z59,z2,z3,z16,z5,z6]),(0,[z2,z3,z39,z4,z16,z5,z6]),(0,[z0,z2,z3,z4,z108,z5,z6]),(0,[z0,z542,z2,z3,z4,z5,z6]),(0,[z0,z543,z2,z3,z4,z5,z6])],[(1,[z0,z2,z428,z4,z5,z6]),(0,[z0,z544,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z545,z5,z6]),(0,[z0,z2,z3,z4,z5,z546,z6]),(0,[z0,z117,z42,z3,z4,z5,z6]),(0,[z547,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z548,z3,z4,z5,z6])],[(0,[z0,z69,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z441,z39,z5,z6]),(0,[z0,z2,z3,z549,z4,z5,z6]),(0,[z0,z96,z2,z3,z4,z132,z6]),(0,[z0,z550,z2,z3,z4,z5,z6]),(0,[z0,z117,z120,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z551,z6]),(0,[z0,z552,z2,z3,z4,z5,z6]),(0,[z0,z553,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z554]),(0,[z0,z2,z3,z4,z5,z6,z555]),(0,[z0,z2,z3,z4,z5,z556,z6]),(1,[z530,z2,z3,z4,z5,z6]),(0,[z0,z2,z557,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z5,z57])],[(0,[z0,z558,z2,z3,z4,z5,z6]),(0,[z559,z0,z2,z3,z4,z5,z6]),(0,[z197,z0,z2,z3,z16,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z135]),(0,[z0,z530,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z39,z5,z6,z32]),(0,[z0,z2,z3,z4,z108,z327,z6]),(0,[z0,z2,z3,z4,z5,z135,z21])],[(0,[z99,z0,z2,z124,z4,z5,z6]),(0,[z0,z2,z3,z560,z4,z5,z6])],[(1,[z2,z3,z16,z5,z6,z18]),(0,[z0,z2,z3,z12,z5,z114,z6]),(0,[z0,z2,z3,z4,z5,z6,z561])],[(0,[z0,z2,z3,z51,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z6,z18]),(0,[z0,z562,z2,z3,z4,z5,z6]),(0,[z0,z3,z4,z8,z5,z327,z6]),(0,[z0,z2,z3,z4,z5,z15,z6]),(0,[z0,z2,z3,z4,z563,z5,z6])],[(0,[z0,z2,z3,z4,z5,z6,z564]),(0,[z0,z2,z565,z3,z4,z5,z6])],[(0,[z0,z131,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z8,z169,z6]),(0,[z0,z2,z566,z3,z4,z5,z6]),(0,[z0,z337,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z392,z5,z6]),(0,[z0,z2,z3,z567,z4,z5,z6]),(0,[z0,z2,z3,z16,z108,z5,z6]),(0,[z0,z272,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z462,z39,z5,z6]),(0,[z0,z131,z2,z4,z5,z132,z6]),(0,[z0,z66,z2,z3,z142,z4,z5])],[(0,[z0,z2,z568,z3,z4,z5,z6]),(0,[z99,z2,z3,z51,z4,z5,z6]),(1,[z107,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z569,z4,z5,z6]),(0,[z0,z570,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z571])]],
   [[(0,[z0,z2,z152,z3,z39,z5,z6]),(0,[z572,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z6,z573]),(0,[z0,z73,z2,z3,z29,z5,z6]),(0,[z574,z0,z2,z3,z4,z5,z6]),(0,[z0,z229,z2,z3,z4,z5,z6])],[(1,[z0,z2,z3,z575,z5,z6]),(0,[z0,z167,z2,z3,z16,z5,z6]),(0,[z70,z0,z2,z3,z4,z5,z135]),(0,[z0,z2,z4,z83,z5,z132,z6]),(0,[z0,z117,z2,z3,z4,z5,z21])],[(0,[z0,z2,z3,z161,z39,z5,z6]),(0,[z0,z576,z2,z3,z4,z5,z6]),(0,[z0,z577,z2,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z18]),(0,[z0,z2,z3,z4,z67,z5,z135])],[(0,[z0,z578,z2,z3,z4,z5,z6]),(0,[z0,z167,z3,z4,z29,z5,z6])],[(1,[z0,z2,z3,z312,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z579]),(1,[z0,z272,z3,z30,z5,z6]),(1,[z0,z2,z3,z4,z6,z217])],[(0,[z0,z2,z3,z4,z5,z580,z6]),(0,[z197,z0,z2,z3,z39,z5,z6]),(1,[z0,z2,z3,z447,z5,z6]),(0,[z0,z2,z3,z4,z5,z581,z6]),(0,[z0,z167,z3,z4,z8,z5,z6]),(0,[z0,z2,z38,z3,z60,z5,z6]),(0,[z582,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z583,z6]),(0,[z584,z0,z2,z3,z4,z5,z6]),(1,[z35,z0,z2,z3,z15,z6]),(0,[z0,z2,z3,z142,z4,z5,z6])],[(0,[z0,z2,z3,z16,z5,z15,z6]),(0,[z0,z2,z52,z4,z5,z140,z6]),(0,[z585,z0,z2,z3,z4,z5,z6]),(0,[z0,z586,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z587,z5,z6]),(0,[z0,z2,z3,z4,z5,z588,z6])],[(0,[z0,z2,z3,z4,z5,z589,z6]),(0,[z0,z2,z3,z590,z4,z5,z6]),(0,[z0,z127,z2,z3,z4,z5,z6]),(1,[z0,z253,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z39,z67,z5,z6]),(0,[z0,z2,z3,z4,z5,z591,z6]),(0,[z0,z2,z3,z4,z5,z592,z6])],[(1,[z218,z152,z3,z4,z5,z6]),(0,[z0,z2,z593,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z594,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z595]),(0,[z0,z2,z3,z596,z4,z5,z6]),(0,[z0,z131,z2,z3,z4,z83,z6]),(0,[z0,z2,z3,z4,z597,z5,z6]),(0,[z0,z2,z3,z4,z5,z598,z6])],[(0,[z599,z0,z2,z3,z4,z5,z6]),(0,[z107,z0,z2,z3,z4,z5,z262]),(0,[z0,z2,z600,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z140,z6])],[(0,[z0,z2,z3,z39,z11,z5,z6]),(0,[z0,z601,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z602]),(0,[z0,z272,z3,z30,z4,z5,z6]),(0,[z0,z2,z3,z603,z4,z5,z6])],[(0,[z0,z272,z2,z3,z39,z5,z6]),(0,[z604,z0,z2,z3,z4,z5,z6]),(0,[z0,z605,z2,z3,z4,z5,z6]),(0,[z0,z606,z2,z3,z4,z5,z6]),(0,[z607,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z608,z6]),(0,[z0,z127,z3,z4,z5,z183,z6]),(0,[z0,z609,z2,z3,z4,z5,z6])],[(0,[z99,z133,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z67,z5,z18]),(0,[z0,z69,z2,z3,z60,z5,z6]),(0,[z0,z26,z2,z3,z4,z67,z5]),(0,[z0,z2,z3,z4,z5,z6,z610])],[(0,[z218,z0,z2,z428,z4,z5,z6]),(1,[z0,z2,z3,z4,z280,z6]),(1,[z2,z3,z39,z16,z5,z6]),(0,[z0,z611,z2,z3,z4,z5,z6]),(0,[z0,z612,z2,z3,z4,z5,z6])],[(0,[z256,z0,z2,z3,z575,z5,z6]),(1,[z0,z2,z3,z237,z5,z6]),(0,[z0,z2,z3,z39,z16,z5,z6]),(0,[z0,z167,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z613,z4,z5,z6])]],
   [[(0,[z0,z2,z2,z3,z4,z5,z6]),(1,[z0,z457,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z614,z6]),(0,[z0,z2,z3,z4,z5,z615,z6]),(0,[z0,z2,z3,z4,z616,z5,z6])],[(0,[z0,z120,z2,z3,z16,z5,z6]),(0,[z22,z17,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z617])],[(1,[z0,z2,z3,z4,z5,z100]),(0,[z0,z2,z3,z4,z109,z5,z6]),(1,[z0,z2,z3,z4,z166,z6]),(0,[z0,z2,z3,z4,z5,z6,z618]),(1,[z0,z2,z3,z4,z5,z332])],[(0,[z619,z0,z2,z3,z4,z5,z6]),(0,[z99,z0,z2,z3,z4,z280,z6]),(0,[z0,z620,z2,z3,z4,z5,z6]),(0,[z0,z2,z124,z52,z4,z5,z6]),(0,[z0,z621,z2,z3,z4,z5,z6]),(0,[z0,z167,z59,z3,z4,z5,z6]),(1,[z0,z2,z260,z4,z5,z6]),(0,[z0,z131,z2,z3,z4,z5,z6]),(0,[z0,z26,z2,z3,z12,z5,z6]),(1,[z0,z66,z2,z3,z4,z57]),(0,[z622,z0,z2,z3,z4,z5,z6])],[(0,[z99,z0,z2,z3,z237,z5,z6]),(0,[z0,z2,z3,z4,z5,z5,z6]),(1,[z0,z167,z59,z4,z5,z6]),(0,[z623,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z624,z5,z6]),(0,[z0,z625,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z626,z4,z5,z6]),(0,[z0,z2,z3,z627,z4,z5,z6])],[(0,[z256,z58,z2,z3,z4,z5,z6]),(0,[z99,z0,z457,z3,z4,z5,z6]),(0,[z0,z2,z4,z5,z140,z6,z21])],[(0,[z0,z628,z2,z3,z4,z5,z6]),(0,[z125,z2,z3,z4,z16,z5,z6]),(0,[z0,z2,z3,z39,z5,z6,z57]),(0,[z0,z2,z3,z4,z5,z6,z6]),(0,[z0,z2,z3,z4,z5,z629,z6]),(0,[z0,z630,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z631,z5,z6])],[(0,[z99,z0,z2,z3,z4,z5,z100]),(0,[z133,z0,z2,z124,z4,z5,z6]),(0,[z0,z59,z2,z3,z4,z5,z6]),(0,[z0,z632,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z633,z4,z5,z6])]],
   [[(0,[z0,z634,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z30,z16,z5,z6]),(0,[z0,z544,z2,z3,z4,z5,z6]),(0,[z635,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z636,z4,z5,z6]),(0,[z637,z0,z2,z3,z4,z5,z6])],[(0,[z638,z0,z2,z3,z4,z5,z6]),(0,[z0,z272,z3,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z327,z6]),(0,[z0,z69,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z51,z16,z5,z6]),(0,[z639,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z640,z6]),(1,[z0,z7,z3,z4,z327,z6]),(0,[z0,z2,z3,z4,z5,z641,z6]),(0,[z0,z66,z2,z3,z11,z4,z6]),(0,[z0,z2,z3,z4,z642,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z643])],[(0,[z2,z124,z3,z51,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z135,z6]),(0,[z0,z2,z247,z3,z4,z5,z6]),(0,[z0,z381,z2,z3,z4,z5,z6]),(0,[z644,z0,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z645,z5,z6]),(0,[z197,z2,z3,z4,z5,z169,z6]),(0,[z0,z646,z2,z3,z4,z5,z6]),(0,[z647,z0,z2,z3,z4,z5,z6])],[(0,[z0,z648,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z649,z6]),(0,[z107,z0,z2,z3,z146,z5,z6])],[(0,[z0,z2,z3,z650,z4,z5,z6]),(1,[z0,z2,z3,z142,z5,z114]),(0,[z0,z2,z3,z4,z5,z651,z6])],[(0,[z2,z3,z4,z16,z5,z169,z6]),(0,[z0,z120,z2,z3,z39,z5,z6]),(0,[z197,z107,z2,z3,z4,z5,z6]),(0,[z0,z3,z52,z4,z29,z5,z6]),(0,[z0,z2,z3,z4,z652,z5,z6])]],
   [[(0,[z0,z68,z2,z3,z16,z5,z6]),(1,[z0,z370,z3,z4,z5,z6]),(0,[z653,z0,z2,z3,z4,z5,z6])],[(0,[z654,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z169,z6]),(1,[z0,z2,z3,z4,z5,z262]),(0,[z0,z3,z52,z4,z8,z5,z6]),(0,[z0,z59,z131,z2,z4,z5,z6]),(0,[z0,z2,z3,z655,z4,z5,z6])],[(0,[z656,z0,z2,z3,z4,z5,z6]),(0,[z0,z657,z2,z3,z4,z5,z6]),(0,[z0,z658,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z659,z6]),(0,[z0,z2,z3,z4,z5,z660,z6])],[(0,[z0,z2,z3,z4,z175,z5,z6]),(0,[z0,z661,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z662,z6]),(0,[z0,z2,z3,z4,z83,z108,z6]),(0,[z0,z2,z3,z4,z5,z663,z6]),(0,[z0,z2,z3,z4,z5,z6,z32]),(0,[z0,z664,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z665,z5,z6]),(0,[z0,z2,z3,z16,z5,z327,z6]),(0,[z0,z31,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z142,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z666,z6]),(0,[z0,z2,z3,z11,z4,z36,z6])],[(0,[z0,z2,z3,z4,z5,z667,z6]),(0,[z0,z2,z3,z4,z5,z668,z6])],[(0,[z17,z125,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z52,z16,z5,z6]),(0,[z0,z127,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z669,z6]),(0,[z0,z2,z3,z30,z39,z5,z6]),(0,[z0,z2,z3,z4,z169,z132,z6]),(0,[z0,z2,z3,z4,z670,z5,z6])],[(0,[z0,z58,z2,z3,z16,z5,z6]),(0,[z17,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z645,z5,z6]),(0,[z0,z2,z3,z39,z60,z5,z6]),(0,[z0,z2,z3,z4,z5,z140,z18]),(0,[z0,z2,z3,z4,z5,z6,z671]),(0,[z0,z127,z2,z3,z4,z5,z183]),(1,[z0,z131,z2,z4,z132,z6])]],
   [[(0,[z0,z672,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z673,z6]),(0,[z0,z2,z3,z51,z39,z5,z6]),(0,[z674,z0,z2,z3,z4,z5,z6]),(0,[z22,z0,z2,z3,z4,z5,z6]),(0,[z0,z675,z2,z3,z4,z5,z6]),(0,[z0,z676,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z677,z5,z6])],[(0,[z0,z678,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z679]),(0,[z0,z167,z111,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z680,z5,z6])],[(0,[z0,z2,z3,z39,z5,z132,z6]),(0,[z0,z2,z3,z23,z4,z5,z6]),(0,[z0,z2,z3,z4,z681,z5,z6])],[(1,[z2,z3,z16,z5,z169,z6]),(0,[z0,z2,z3,z39,z322,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z573]),(1,[z0,z2,z3,z198,z5,z6]),(0,[z682,z0,z2,z3,z4,z5,z6]),(0,[z0,z683,z2,z3,z4,z5,z6]),(1,[z0,z69,z2,z60,z5,z6]),(0,[z0,z2,z3,z4,z5,z684,z6]),(0,[z685,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z686,z4,z5,z6])],[(0,[z0,z687,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z169,z6])],[(0,[z0,z2,z3,z575,z4,z5,z6]),(0,[z0,z2,z3,z39,z83,z5,z6]),(0,[z688,z0,z2,z3,z4,z5,z6]),(0,[z0,z689,z2,z3,z4,z5,z6]),(1,[z0,z381,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z690])],[(0,[z0,z691,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z692,z6])],[(0,[z0,z2,z3,z4,z5,z693,z6]),(0,[z0,z59,z2,z124,z4,z5,z6]),(0,[z0,z2,z3,z39,z336,z5,z6]),(0,[z0,z2,z3,z4,z12,z5,z6])]],
   [[(0,[z0,z2,z38,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z694]),(0,[z0,z2,z3,z4,z5,z695,z6])],[(0,[z0,z2,z3,z16,z5,z669,z6]),(0,[z0,z696,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z29,z5,z6]),(0,[z0,z697,z2,z3,z4,z5,z6]),(0,[z698,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z699])],[(0,[z0,z2,z3,z142,z39,z5,z6]),(0,[z70,z0,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z135,z6,z18]),(0,[z0,z117,z2,z4,z5,z140,z6])],[(0,[z0,z2,z124,z3,z4,z5,z6]),(0,[z125,z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z4,z5,z6]),(0,[z0,z2,z3,z4,z8,z5,z6]),(0,[z0,z3,z4,z5,z183,z6,z32]),(0,[z0,z2,z3,z4,z67,z5,z6])],[(0,[z0,z2,z3,z52,z39,z5,z6]),(0,[z0,z127,z2,z3,z39,z5,z6]),(1,[z0,z2,z3,z146,z5,z6]),(0,[z0,z2,z3,z4,z108,z132,z6]),(0,[z0,z2,z3,z700,z4,z5,z6]),(0,[z0,z701,z2,z3,z4,z5,z6])],[(0,[z0,z58,z2,z3,z39,z5,z6]),(0,[z0,z167,z31,z3,z4,z5,z6]),(0,[z0,z73,z272,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z6,z702]),(0,[z0,z2,z3,z4,z703,z5,z6]),(0,[z0,z120,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z704,z4,z5,z6])],[(0,[z0,z2,z3,z198,z4,z5,z6]),(0,[z0,z705,z2,z3,z4,z5,z6]),(0,[z0,z7,z157,z3,z4,z5,z6]),(0,[z0,z2,z3,z706,z4,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z131,z2,z39,z132,z6]),(0,[z0,z2,z4,z707,z5,z6])],[(0,[z0,z2,z3,z4,z5,z100]),(0,[z2,z3,z708,z4,z5,z6]),(0,[z0,z709,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z588])],[(0,[z0,z2,z16,z710,z5,z6]),(0,[z0,z2,z3,z16,z5,z711]),(0,[z0,z2,z260,z4,z5,z6]),(0,[z0,z712,z3,z4,z5,z6]),(0,[z0,z2,z3,z713,z5,z6]),(0,[z339,z2,z3,z177,z5,z6]),(0,[z0,z66,z2,z3,z4,z57])],[(0,[z0,z2,z3,z4,z175,z288]),(0,[z0,z66,z2,z3,z16,z57]),(0,[z22,z2,z3,z312,z5,z135]),(0,[z0,z2,z3,z714,z5,z6])],[(0,[z0,z2,z138,z4,z5,z6]),(0,[z0,z2,z715,z4,z5,z6]),(0,[z0,z381,z96,z4,z83,z6])],[(0,[z178,z152,z3,z4,z5,z6]),(0,[z22,z2,z3,z16,z5,z18]),(0,[z0,z716,z2,z4,z5,z6])],[(0,[z2,z3,z16,z67,z5,z18]),(0,[z0,z381,z3,z39,z5,z6])],[(0,[z0,z2,z717,z4,z5,z6]),(0,[z0,z2,z3,z718,z5,z6]),(0,[z0,z31,z3,z16,z5,z32])]],
   [[(0,[z2,z3,z719,z16,z5,z6]),(0,[z279,z2,z3,z39,z5,z6]),(0,[z246,z2,z3,z39,z5,z6]),(0,[z0,z2,z720,z4,z5,z6]),(0,[z0,z2,z3,z4,z721,z6]),(0,[z0,z31,z3,z4,z5,z722]),(0,[z723,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z724])],[(0,[z0,z42,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z725]),(0,[z0,z2,z3,z4,z160,z6]),(0,[z339,z2,z3,z4,z36,z6])],[(0,[z0,z538,z52,z4,z5,z6]),(0,[z0,z726,z3,z16,z5,z6]),(0,[z0,z514,z2,z4,z5,z140]),(0,[z727,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z728,z5,z6]),(0,[z0,z2,z3,z5,z729,z6])],[],[(0,[z0,z2,z730,z4,z5,z6]),(0,[z0,z2,z3,z731,z5,z6]),(0,[z584,z2,z3,z16,z5,z6]),(0,[z478,z2,z3,z39,z5,z6]),(0,[z0,z3,z4,z732,z5,z6]),(0,[z337,z733,z2,z3,z5,z6])],[(0,[z0,z2,z3,z734,z5,z6])],[(0,[z0,z77,z3,z4,z392,z6]),(0,[z653,z2,z3,z4,z108,z6]),(0,[z0,z131,z247,z4,z5,z6]),(0,[z35,z0,z121,z2,z3,z6]),(0,[z0,z337,z2,z3,z36,z6])],[(0,[z0,z2,z3,z4,z175,z6]),(0,[z0,z2,z3,z735,z5,z6]),(0,[z133,z2,z124,z4,z5,z6]),(0,[z70,z2,z3,z4,z5,z736]),(0,[z0,z370,z3,z4,z5,z6]),(0,[z0,z737,z2,z3,z4,z5]),(0,[z0,z738,z3,z4,z5,z6])]],
   [[(0,[z218,z152,z428,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z739]),(0,[z0,z2,z3,z4,z5,z262]),(0,[z0,z2,z3,z4,z5,z740]),(0,[z0,z3,z4,z8,z741,z6]),(0,[z0,z2,z3,z4,z5,z742])],[(0,[z0,z2,z3,z743,z5,z6]),(0,[z0,z744,z3,z4,z5,z6]),(0,[z0,z335,z2,z102,z5,z6]),(0,[z22,z2,z3,z4,z166,z135]),(0,[z0,z158,z52,z4,z5,z6]),(0,[z35,z0,z121,z2,z3,z4])],[(0,[z0,z77,z3,z16,z5,z6]),(0,[z2,z3,z16,z5,z154,z6]),(0,[z35,z0,z2,z3,z154,z6]),(0,[z0,z2,z3,z745,z5,z6]),(0,[z653,z2,z3,z4,z5,z135]),(0,[z0,z31,z260,z4,z5,z6])],[(0,[z0,z2,z746,z4,z5,z6]),(0,[z0,z747,z2,z4,z5,z6])],[(0,[z674,z2,z3,z16,z5,z6]),(0,[z2,z3,z748,z16,z5,z6]),(0,[z2,z3,z39,z93,z5,z6])],[(0,[z2,z3,z16,z169,z36,z6]),(0,[z129,z2,z3,z16,z5,z6]),(0,[z0,z749,z2,z3,z5,z6]),(0,[z92,z2,z3,z16,z5,z6]),(0,[z0,z31,z3,z39,z5,z32]),(0,[z0,z2,z3,z4,z750,z6])],[(0,[z0,z2,z3,z4,z5,z751]),(0,[z0,z96,z2,z16,z83,z6]),(0,[z0,z752,z3,z39,z5,z6]),(0,[z0,z131,z2,z4,z132,z6])],[(0,[z0,z753,z3,z4,z5,z6]),(0,[z0,z42,z3,z39,z5,z6])]],
   [[(0,[z0,z2,z3,z5,z6,z754]),(0,[z0,z2,z3,z4,z6,z755])],[(0,[z2,z3,z268,z39,z5,z6]),(0,[z0,z2,z756,z4,z5,z6]),(0,[z0,z2,z3,z757,z5,z6])],[(0,[z0,z2,z3,z758,z5,z6]),(0,[z0,z2,z3,z4,z5,z759]),(0,[z0,z2,z3,z4,z760,z6]),(0,[z0,z2,z3,z198,z5,z6]),(1,[z2,z3,z16,z5,z284])],[(0,[z0,z2,z3,z4,z5,z761]),(0,[z459,z0,z2,z3,z15,z6]),(0,[z347,z2,z3,z4,z169,z6]),(0,[z0,z3,z732,z29,z5,z6])],[(0,[z0,z2,z3,z762,z5,z6]),(0,[z66,z2,z3,z16,z169,z6]),(0,[z0,z381,z3,z4,z5,z6]),(0,[z0,z2,z763,z4,z5,z6])],[(0,[z107,z2,z3,z748,z5,z6]),(0,[z0,z2,z3,z4,z5,z764]),(0,[z0,z2,z3,z4,z765,z6]),(0,[z0,z2,z766,z4,z5,z6])],[(0,[z0,z2,z767,z4,z5,z6]),(0,[z0,z2,z3,z4,z768,z6]),(0,[z178,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z342,z245,z6]),(0,[z769,z2,z3,z4,z5,z6])],[(0,[z0,z2,z770,z4,z5,z6]),(0,[z771,z2,z3,z4,z5,z6])]],
   [[(0,[z0,z77,z3,z39,z5,z6]),(0,[z125,z2,z3,z16,z5,z6]),(0,[z0,z26,z229,z2,z3,z6])],[(0,[z0,z2,z3,z4,z5,z772]),(1,[z2,z708,z4,z5,z6]),(0,[z0,z2,z3,z729,z15,z6])],[(0,[z0,z773,z3,z4,z5,z6]),(0,[z774,z2,z3,z4,z5,z6])],[(0,[z0,z2,z138,z16,z5,z6]),(0,[z0,z2,z3,z146,z5,z6]),(0,[z2,z3,z16,z681,z5,z6]),(0,[z0,z253,z3,z39,z5,z6]),(0,[z0,z775,z2,z4,z5,z6]),(0,[z0,z2,z3,z776,z5,z6]),(0,[z0,z26,z229,z2,z3,z4])],[(0,[z0,z777,z3,z4,z5,z6]),(0,[z0,z77,z3,z292,z5,z6]),(0,[z0,z778,z2,z3,z4,z5]),(0,[z2,z3,z16,z5,z6,z573]),(0,[z2,z3,z146,z16,z5,z6]),(0,[z0,z2,z3,z779,z5,z6])],[(0,[z0,z778,z2,z3,z16,z5]),(0,[z0,z2,z3,z4,z780,z6]),(0,[z0,z31,z3,z4,z5,z171]),(0,[z0,z2,z3,z12,z729,z6])],[(0,[z0,z2,z3,z4,z5,z711]),(1,[z0,z26,z229,z2,z3]),(0,[z0,z781,z2,z4,z5,z6])],[(0,[z682,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z782])]],
   [[(0,[z0,z2,z3,z4,z783,z6]),(0,[z0,z2,z3,z16,z160,z6]),(0,[z343,z2,z3,z16,z5,z6]),(0,[z0,z2,z4,z5,z784,z6]),(0,[z0,z120,z2,z4,z5,z785])],[(0,[z0,z2,z3,z786,z5,z6]),(0,[z0,z2,z3,z4,z5,z787]),(0,[z2,z3,z16,z5,z6,z223]),(0,[z444,z0,z2,z3,z5,z573]),(0,[z0,z2,z3,z312,z166,z6])],[(0,[z0,z2,z3,z4,z81,z288]),(0,[z0,z2,z3,z11,z336,z6]),(0,[z0,z2,z788,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z789]),(0,[z0,z253,z38,z4,z5,z6]),(0,[z0,z790,z3,z4,z5,z6]),(0,[z530,z2,z3,z4,z67,z5]),(0,[z0,z2,z791,z4,z5,z6])],[(0,[z0,z2,z3,z4,z792,z6]),(0,[z0,z2,z3,z793,z5,z6]),(0,[z0,z794,z3,z4,z5,z6]),(0,[z0,z2,z795,z4,z5,z6]),(0,[z0,z2,z3,z796,z5,z6])],[(0,[z0,z2,z3,z797,z5,z6]),(0,[z66,z2,z3,z16,z5,z18]),(0,[z0,z2,z407,z295,z5,z6]),(0,[z798,z2,z3,z4,z5,z6])],[(0,[z2,z3,z177,z16,z5,z6]),(0,[z347,z2,z3,z16,z5,z6]),(0,[z0,z544,z2,z3,z5,z27]),(0,[z0,z42,z3,z4,z5,z6])],[(0,[z0,z2,z138,z4,z5,z231]),(0,[z0,z2,z3,z16,z175,z6]),(0,[z0,z799,z3,z4,z5,z6]),(0,[z0,z2,z800,z4,z5,z6]),(0,[z0,z2,z3,z801,z5,z6])],[(0,[z0,z802,z3,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z237,z280,z6]),(0,[z0,z127,z3,z4,z5,z183]),(0,[z0,z2,z707,z60,z5,z6]),(0,[z0,z2,z3,z5,z6,z56]),(0,[z803,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z804,z57]),(0,[z0,z337,z66,z2,z3,z5])],[(0,[z0,z2,z138,z39,z5,z6]),(0,[z0,z457,z3,z4,z280,z6]),(0,[z0,z2,z3,z4,z5,z805]),(0,[z2,z3,z4,z16,z5,z284]),(0,[z0,z806,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z5,z736])],[(0,[z0,z457,z3,z237,z5,z6]),(0,[z0,z806,z2,z3,z16,z6]),(0,[z0,z2,z3,z242,z5,z182])],[(0,[z107,z2,z3,z16,z5,z262]),(0,[z2,z3,z16,z5,z18,z21]),(0,[z0,z2,z16,z5,z784,z6]),(0,[z2,z3,z4,z108,z765,z6]),(0,[z574,z2,z3,z4,z5,z135]),(0,[z0,z117,z2,z4,z5,z140])],[(0,[z0,z2,z3,z162,z5,z231]),(0,[z0,z2,z3,z237,z5,z100]),(0,[z0,z3,z4,z5,z741,z6]),(0,[z0,z2,z161,z707,z5,z6])],[(0,[z0,z457,z3,z4,z5,z100]),(0,[z2,z3,z16,z5,z33,z6]),(0,[z0,z2,z3,z242,z5,z114]),(0,[z0,z2,z807,z4,z5,z6]),(0,[z0,z808,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z809]),(0,[z0,z2,z3,z39,z160,z6]),(0,[z0,z26,z2,z3,z5,z27])],[(0,[z0,z2,z3,z16,z6,z755]),(0,[z0,z2,z4,z5,z6,z810]),(0,[z17,z2,z3,z719,z5,z6]),(0,[z17,z2,z3,z4,z5,z284]),(0,[z0,z811,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z67,z598])]],
   [[(0,[z0,z2,z138,z302,z5,z6]),(0,[z0,z2,z138,z4,z81,z6]),(0,[z0,z2,z3,z4,z812,z6]),(0,[z0,z2,z3,z813,z5,z6]),(0,[z0,z2,z3,z4,z5,z814]),(0,[z2,z3,z16,z264,z5,z6]),(0,[z197,z2,z3,z4,z765,z6]),(0,[z0,z2,z3,z4,z5,z804])],[(0,[z0,z2,z3,z4,z5,z288]),(0,[z0,z2,z3,z4,z175,z231]),(0,[z92,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z765,z169,z6]),(0,[z0,z2,z3,z447,z5,z262])],[(0,[z0,z2,z74,z16,z5,z6]),(0,[z0,z815,z3,z39,z5,z6]),(0,[z0,z96,z2,z4,z83,z6])],[(0,[z0,z2,z3,z816,z5,z6]),(0,[z0,z2,z3,z103,z5,z6]),(0,[z0,z817,z2,z3,z4,z5]),(0,[z0,z2,z3,z142,z5,z266]),(0,[z0,z2,z3,z818,z5,z6])],[(0,[z0,z2,z3,z39,z175,z6]),(0,[z582,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z109,z5,z6]),(0,[z0,z370,z3,z39,z5,z6]),(0,[z0,z2,z3,z39,z6,z819]),(0,[z0,z820,z2,z3,z5,z6]),(0,[z0,z353,z4,z29,z5,z6])],[(0,[z607,z2,z3,z16,z5,z6]),(0,[z0,z167,z9,z4,z5,z6])],[(0,[z0,z2,z3,z162,z81,z6]),(1,[z2,z3,z719,z5,z6])],[(0,[z0,z2,z3,z821,z5,z6]),(0,[z0,z2,z3,z153,z5,z6]),(0,[z0,z822,z111,z4,z5,z6]),(0,[z0,z2,z3,z4,z823,z6]),(0,[z0,z121,z2,z3,z4,z5]),(0,[z733,z2,z3,z5,z6,z57])]],
   [[(0,[z0,z121,z2,z3,z16,z5]),(0,[z0,z2,z3,z824,z5,z6]),(0,[z0,z2,z3,z4,z5,z825]),(0,[z0,z272,z3,z732,z5,z6]),(0,[z0,z2,z38,z707,z5,z6]),(0,[z0,z66,z2,z3,z56,z57])],[],[(0,[z0,z2,z3,z826,z5,z6]),(0,[z0,z2,z3,z4,z5,z827])],[(0,[z0,z2,z3,z302,z175,z6]),(0,[z0,z2,z3,z828,z5,z6]),(0,[z2,z3,z16,z5,z6,z90]),(0,[z2,z3,z242,z16,z5,z18]),(0,[z2,z3,z16,z5,z166,z6]),(0,[z2,z3,z39,z587,z5,z6]),(0,[z0,z2,z829,z4,z5,z6]),(0,[z0,z830,z3,z4,z5,z6])],[(0,[z256,z58,z3,z267,z5,z6]),(0,[z0,z167,z139,z4,z5,z6]),(0,[z0,z358,z3,z645,z5,z6]),(0,[z644,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z831,z5,z6]),(0,[z0,z66,z2,z3,z4,z804])],[(0,[z0,z2,z3,z832,z5,z6]),(0,[z339,z26,z2,z3,z5,z6])],[(0,[z459,z0,z2,z3,z669,z6]),(0,[z0,z2,z3,z4,z5,z833]),(0,[z0,z272,z3,z186,z5,z6]),(0,[z0,z2,z3,z834,z5,z6]),(0,[z35,z0,z26,z66,z2,z3]),(0,[z0,z26,z2,z3,z5,z835])],[(0,[z0,z836,z2,z3,z4,z5]),(0,[z0,z2,z3,z4,z837,z6]),(0,[z2,z3,z16,z298,z5,z6]),(0,[z0,z73,z74,z29,z5,z6]),(0,[z0,z838,z3,z4,z5,z6])]],
   [[(0,[z0,z111,z52,z16,z5,z6]),(0,[z0,z836,z2,z3,z16,z5]),(0,[z0,z2,z74,z39,z5,z6]),(0,[z0,z2,z3,z839,z5,z6]),(0,[z0,z120,z42,z4,z5,z6])],[],[(0,[z0,z2,z3,z39,z5,z764]),(0,[z0,z840,z3,z4,z5,z6]),(0,[z0,z841,z2,z4,z5,z6])],[(0,[z0,z2,z3,z842,z5,z6]),(0,[z99,z2,z51,z4,z5,z290]),(0,[z0,z2,z122,z16,z5,z6]),(0,[z119,z2,z3,z16,z5,z6]),(0,[z0,z2,z767,z39,z5,z6]),(0,[z0,z2,z3,z4,z67,z589]),(0,[z843,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z844]),(0,[z402,z2,z3,z16,z5,z6]),(0,[z22,z2,z3,z4,z5,z243]),(0,[z0,z2,z38,z161,z5,z6])],[(0,[z0,z2,z3,z162,z5,z6]),(0,[z125,z2,z3,z719,z5,z6]),(0,[z0,z2,z3,z462,z5,z266]),(0,[z0,z845,z3,z4,z5,z6]),(0,[z0,z2,z3,z846,z5,z6]),(0,[z300,z26,z2,z3,z5,z27]),(0,[z0,z2,z3,z4,z5,z835])],[(0,[z0,z2,z847,z4,z5,z6]),(0,[z0,z2,z3,z4,z848,z6]),(0,[z0,z77,z124,z4,z5,z6]),(0,[z0,z2,z3,z849,z5,z6]),(0,[z2,z439,z3,z16,z5,z6])],[(0,[z777,z152,z3,z4,z5,z6]),(0,[z99,z2,z51,z4,z5,z6]),(0,[z0,z127,z3,z16,z5,z183]),(0,[z2,z3,z109,z5,z6,z18]),(0,[z0,z2,z3,z4,z850,z6]),(0,[z0,z851,z3,z4,z5,z6])]],
   [[(0,[z688,z2,z124,z4,z5,z6]),(0,[z0,z815,z3,z4,z5,z6]),(0,[z0,z2,z852,z4,z5,z6]),(0,[z0,z229,z2,z3,z142,z4])],[(0,[z0,z2,z3,z4,z5,z853]),(0,[z35,z0,z2,z3,z332,z15])],[(0,[z0,z2,z3,z4,z5,z854]),(0,[z0,z117,z2,z16,z5,z140]),(0,[z0,z2,z3,z4,z6,z819]),(0,[z0,z822,z52,z4,z5,z6]),(0,[z0,z24,z2,z4,z83,z6]),(0,[z0,z59,z474,z4,z5,z6]),(0,[z855,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z856]),(0,[z35,z0,z2,z3,z334,z6])],[],[(0,[z0,z857,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z765,z6]),(0,[z0,z858,z3,z4,z5,z6])],[(0,[z0,z2,z3,z16,z81,z6]),(0,[z859,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z860,z6]),(0,[z0,z2,z3,z4,z861,z6]),(0,[z0,z2,z3,z4,z5,z862]),(0,[z0,z111,z52,z39,z5,z6]),(0,[z0,z2,z3,z4,z863,z6]),(0,[z0,z26,z2,z3,z84,z5])],[(0,[z2,z777,z3,z4,z5,z6]),(0,[z0,z2,z3,z864,z5,z6]),(0,[z0,z287,z3,z441,z5,z6]),(0,[z107,z2,z3,z4,z108,z6])]],
   [[(0,[z0,z2,z3,z16,z5,z288]),(0,[z0,z2,z3,z865,z5,z6]),(0,[z0,z2,z866,z4,z5,z6])],[(0,[z256,z58,z3,z4,z5,z6]),(0,[z2,z3,z342,z16,z169,z6]),(0,[z0,z358,z3,z29,z5,z6]),(0,[z0,z2,z122,z39,z5,z6]),(0,[z35,z530,z2,z3,z5,z6])],[(0,[z0,z2,z3,z867,z5,z6])],[(0,[z17,z2,z3,z39,z5,z6]),(0,[z70,z2,z3,z110,z5,z18]),(0,[z868,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z392,z290]),(0,[z2,z3,z16,z5,z357,z6]),(0,[z22,z2,z3,z4,z160,z135]),(0,[z0,z2,z4,z5,z785,z21]),(0,[z733,z2,z3,z4,z5,z6])],[(0,[z0,z127,z3,z39,z5,z183]),(0,[z0,z2,z3,z5,z6,z869]),(0,[z0,z2,z3,z870,z5,z6]),(0,[z0,z2,z3,z4,z5,z871])],[(0,[z2,z3,z16,z83,z169,z6]),(0,[z2,z3,z4,z16,z166,z6]),(0,[z0,z2,z3,z23,z160,z6]),(0,[z0,z2,z74,z4,z5,z6]),(0,[z0,z52,z4,z515,z5,z6])],[(0,[z0,z2,z3,z4,z5,z872]),(0,[z256,z777,z3,z4,z5,z6]),(0,[z70,z2,z3,z16,z5,z18]),(0,[z0,z873,z3,z4,z5,z6]),(0,[z0,z2,z3,z874,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z81,z231]),(0,[z0,z2,z3,z16,z5,z290]),(0,[z0,z2,z3,z110,z5,z6]),(0,[z0,z117,z2,z39,z5,z140]),(0,[z107,z2,z3,z4,z108,z284]),(0,[z0,z2,z3,z5,z6,z875]),(0,[z0,z2,z3,z876,z5,z6]),(0,[z0,z2,z3,z4,z5,z877])],[(0,[z22,z2,z3,z16,z166,z6]),(0,[z0,z2,z3,z16,z67,z36]),(0,[z0,z52,z4,z526,z5,z6]),(0,[z35,z0,z2,z3,z71,z6]),(0,[z0,z2,z3,z878,z5,z6])],[(0,[z653,z2,z3,z16,z5,z6]),(0,[z0,z879,z3,z4,z5,z6]),(0,[z0,z880,z3,z4,z5,z6])],[(0,[z197,z2,z3,z103,z169,z6]),(0,[z0,z337,z66,z2,z3,z6])],[(0,[z0,z2,z3,z16,z5,z6]),(0,[z0,z881,z3,z4,z5,z6]),(0,[z107,z2,z3,z4,z765,z6])],[(0,[z0,z2,z428,z162,z5,z6]),(0,[z0,z2,z4,z5,z140,z785]),(0,[z0,z2,z882,z4,z5,z6])],[(0,[z0,z2,z883,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z288]),(0,[z92,z2,z3,z39,z5,z6]),(0,[z0,z229,z2,z3,z39,z6]),(0,[z0,z2,z3,z4,z5,z884]),(0,[z0,z2,z3,z11,z6,z643]),(0,[z0,z2,z3,z5,z6,z885])],[(0,[z2,z3,z16,z208,z5,z6]),(0,[z0,z96,z2,z39,z83,z6]),(0,[z0,z69,z2,z707,z5,z6]),(0,[z0,z2,z3,z4,z5,z886]),(0,[z339,z2,z3,z11,z5,z6])]],
   [[(0,[z0,z77,z3,z4,z280,z6]),(0,[z0,z887,z3,z4,z5,z6]),(0,[z0,z2,z3,z888,z5,z6])],[(0,[z0,z2,z3,z889,z5,z6]),(0,[z0,z77,z3,z237,z5,z6]),(0,[z0,z7,z3,z4,z741,z6]),(0,[z0,z2,z4,z5,z890,z6]),(0,[z0,z2,z3,z891,z5,z6])],[(0,[z0,z2,z428,z4,z175,z6]),(0,[z99,z2,z51,z4,z392,z6]),(0,[z0,z423,z2,z60,z5,z6]),(0,[z0,z2,z3,z892,z5,z6])],[(0,[z339,z2,z3,z16,z5,z6]),(0,[z0,z893,z2,z3,z5,z6])],[(0,[z0,z77,z3,z4,z5,z100]),(0,[z0,z894,z3,z4,z5,z6]),(0,[z0,z2,z3,z895,z5,z6]),(0,[z0,z111,z52,z4,z5,z6]),(0,[z0,z2,z3,z4,z896,z5]),(0,[z0,z2,z3,z4,z36,z37])],[(0,[z0,z2,z3,z302,z5,z288]),(0,[z0,z2,z897,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z284]),(0,[z70,z2,z3,z39,z5,z18]),(0,[z898,z2,z3,z4,z5,z6]),(0,[z0,z899,z2,z4,z5,z6]),(0,[z0,z2,z900,z4,z5,z6]),(0,[z0,z901,z3,z4,z5,z6])],[(0,[z0,z2,z3,z39,z5,z290]),(0,[z99,z2,z51,z16,z5,z6]),(0,[z35,z339,z2,z3,z15,z6])],[(0,[z0,z2,z3,z4,z5,z231]),(0,[z0,z902,z3,z4,z5,z6]),(0,[z0,z247,z3,z16,z5,z6]),(0,[z0,z2,z3,z39,z67,z36]),(0,[z0,z2,z122,z4,z5,z6]),(0,[z0,z2,z3,z903,z5,z6]),(0,[z0,z2,z3,z904,z5,z6]),(0,[z0,z2,z3,z11,z729,z6])]],
   [[(0,[z0,z2,z3,z905,z5,z6])],[(0,[z0,z73,z3,z29,z5,z6]),(0,[z0,z157,z122,z4,z8,z6]),(0,[z0,z2,z3,z906,z5,z6])],[(0,[z0,z2,z3,z907,z5,z6]),(0,[z0,z2,z3,z292,z5,z290]),(0,[z0,z908,z2,z3,z4,z6]),(0,[z78,z2,z3,z4,z5,z18]),(0,[z0,z2,z3,z4,z909,z6])],[(0,[z0,z2,z3,z267,z5,z6]),(0,[z0,z857,z3,z16,z5,z6]),(0,[z0,z908,z2,z3,z16,z6]),(0,[z0,z2,z910,z39,z5,z6]),(1,[z0,z3,z732,z5,z6]),(0,[z0,z2,z3,z911,z5,z6]),(0,[z0,z96,z247,z4,z83,z6]),(0,[z530,z2,z3,z12,z5,z6])],[(0,[z218,z152,z138,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z912]),(0,[z0,z2,z708,z4,z5,z6]),(0,[z0,z913,z3,z4,z5,z6]),(0,[z282,z2,z3,z16,z5,z6]),(0,[z459,z2,z3,z4,z169,z6]),(0,[z0,z2,z3,z312,z160,z6]),(0,[z914,z2,z3,z4,z5,z6])],[(0,[z0,z2,z407,z161,z5,z6])],[(0,[z0,z2,z3,z292,z5,z6]),(0,[z0,z2,z3,z277,z5,z6]),(0,[z0,z2,z3,z4,z280,z100]),(0,[z107,z2,z3,z16,z108,z6]),(0,[z0,z2,z3,z4,z915,z6]),(0,[z0,z118,z157,z4,z8,z6])],[(0,[z0,z365,z52,z4,z5,z6]),(0,[z0,z3,z4,z5,z183,z722])]],
   [[(0,[z0,z2,z3,z916,z5,z6]),(0,[z256,z58,z3,z16,z5,z6])],[(0,[z0,z2,z3,z302,z5,z6]),(0,[z0,z2,z3,z4,z81,z6]),(0,[z0,z58,z428,z4,z5,z6]),(0,[z339,z2,z3,z39,z5,z6]),(0,[z244,z2,z3,z4,z5,z18]),(0,[z0,z2,z917,z4,z5,z6]),(0,[z0,z69,z253,z60,z5,z6])],[(0,[z218,z152,z3,z162,z5,z6]),(0,[z43,z2,z3,z16,z5,z6]),(0,[z0,z2,z918,z4,z5,z6])],[(0,[z0,z919,z2,z4,z5,z6]),(0,[z0,z2,z232,z53,z5,z6]),(0,[z623,z2,z3,z16,z5,z6]),(0,[z300,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z39,z5,z284]),(0,[z0,z96,z2,z4,z890,z6]),(0,[z530,z66,z2,z3,z4,z5])],[(0,[z99,z2,z51,z39,z5,z6]),(0,[z421,z2,z3,z16,z5,z6])],[(0,[z0,z2,z3,z920,z5,z6]),(0,[z552,z2,z3,z16,z5,z6]),(0,[z0,z247,z3,z39,z5,z6]),(0,[z0,z2,z3,z4,z921,z6]),(0,[z0,z2,z922,z4,z5,z6])],[(0,[z0,z2,z3,z4,z923,z6]),(1,[z0,z822,z4,z5,z6]),(0,[z0,z260,z4,z5,z183,z6])],[(0,[z218,z152,z3,z4,z175,z6]),(0,[z0,z2,z3,z16,z392,z6]),(0,[z0,z68,z2,z265,z5,z6]),(0,[z0,z2,z3,z142,z5,z835])]],
   [[(0,[z99,z2,z51,z292,z5,z6]),(0,[z0,z3,z4,z5,z924,z6]),(0,[z0,z127,z3,z4,z5,z722]),(0,[z0,z2,z3,z925,z5,z6])],[(0,[z0,z2,z3,z4,z926,z6]),(0,[z0,z675,z52,z4,z5,z6])],[(0,[z107,z2,z3,z103,z5,z6]),(0,[z0,z2,z3,z927,z5,z6]),(0,[z0,z2,z3,z4,z5,z785]),(0,[z0,z928,z2,z4,z5,z6])],[(0,[z574,z2,z3,z16,z5,z6]),(0,[z17,z2,z3,z23,z5,z6]),(0,[z0,z2,z3,z929,z5,z6]),(0,[z70,z2,z3,z4,z5,z18])],[(0,[z0,z2,z3,z930,z5,z6]),(0,[z0,z2,z3,z4,z5,z290]),(0,[z0,z931,z3,z4,z5,z6]),(0,[z107,z2,z3,z39,z108,z6]),(0,[z0,z52,z4,z5,z614,z6]),(0,[z0,z543,z52,z4,z5,z6])],[(0,[z0,z2,z932,z4,z5,z6]),(0,[z0,z2,z16,z5,z6,z810]),(0,[z0,z2,z3,z4,z67,z36])],[(0,[z256,z58,z3,z39,z5,z6]),(0,[z0,z933,z3,z4,z5,z6]),(0,[z0,z934,z3,z4,z5,z6])],[(0,[z0,z2,z935,z4,z5,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z936,z6]),(0,[z0,z272,z353,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z937]),(0,[z0,z2,z3,z11,z12,z6])],[(0,[z0,z2,z910,z4,z5,z6]),(0,[z0,z938,z3,z4,z5,z6]),(0,[z0,z2,z3,z939,z5,z6]),(0,[z0,z2,z3,z4,z5,z940])],[(1,[z2,z3,z16,z166,z6]),(0,[z54,z2,z3,z16,z5,z6]),(0,[z0,z66,z2,z3,z4,z445]),(0,[z2,z3,z4,z5,z941,z6])],[(0,[z0,z2,z3,z942,z5,z6]),(0,[z2,z3,z16,z469,z5,z6]),(0,[z943,z0,z2,z3,z5,z6]),(0,[z2,z3,z4,z5,z6,z944])],[(0,[z0,z661,z59,z4,z5,z6]),(0,[z197,z2,z3,z16,z169,z6])],[(0,[z0,z2,z3,z945,z5,z6]),(0,[z0,z2,z3,z39,z392,z6]),(0,[z0,z621,z2,z4,z132,z6]),(0,[z0,z705,z3,z4,z5,z32]),(0,[z946,z2,z3,z4,z5,z6])],[(0,[z0,z2,z947,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z231]),(0,[z218,z777,z3,z4,z5,z6]),(0,[z410,z2,z3,z16,z5,z6]),(0,[z0,z69,z2,z102,z5,z6]),(0,[z0,z167,z605,z4,z5,z6]),(0,[z948,z2,z3,z4,z5,z6])],[(0,[z339,z2,z3,z4,z5,z6]),(0,[z949,z2,z3,z4,z5,z6]),(0,[z0,z157,z3,z4,z741,z6])]],
   [[(0,[z0,z117,z42,z4,z5,z140])],[(0,[z0,z2,z3,z292,z392,z6]),(0,[z0,z2,z3,z950,z5,z6]),(0,[z0,z2,z3,z719,z5,z6]),(0,[z0,z68,z2,z60,z5,z6]),(0,[z0,z2,z3,z4,z5,z284]),(0,[z0,z2,z3,z951,z5,z6]),(0,[z0,z2,z3,z4,z952,z6])],[(0,[z58,z777,z3,z4,z5,z6]),(0,[z0,z2,z3,z953,z5,z6]),(0,[z0,z2,z3,z4,z6,z954])],[(0,[z0,z2,z3,z955,z5,z6]),(0,[z0,z2,z3,z4,z956,z6]),(0,[z459,z2,z3,z16,z169,z6]),(0,[z0,z247,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z957,z6])],[(0,[z0,z2,z428,z4,z5,z288]),(0,[z0,z2,z3,z4,z958,z6]),(0,[z0,z2,z3,z959,z5,z6]),(0,[z0,z337,z2,z3,z5,z6])],[(0,[z0,z2,z3,z4,z5,z960]),(0,[z0,z961,z3,z4,z5,z6]),(0,[z0,z24,z3,z4,z8,z6]),(0,[z0,z2,z3,z4,z5,z962]),(0,[z0,z963,z2,z3,z5,z6]),(0,[z0,z2,z3,z964,z5,z6]),(0,[z0,z229,z2,z3,z114,z6])],[(0,[z0,z2,z3,z4,z965,z6]),(0,[z0,z2,z3,z4,z5,z966])],[(0,[z0,z2,z3,z4,z967,z6]),(0,[z0,z2,z3,z968,z5,z6]),(0,[z454,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z729,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z969]),(0,[z0,z970,z2,z3,z4,z5]),(0,[z0,z2,z3,z5,z6,z971]),(0,[z0,z2,z3,z4,z108,z262]),(0,[z972,z2,z3,z4,z5,z6]),(0,[z35,z0,z121,z2,z3,z5])],[(0,[z0,z970,z2,z3,z16,z5]),(0,[z0,z2,z3,z973,z5,z6]),(1,[z733,z2,z3,z5,z6])],[(0,[z0,z2,z974,z4,z5,z6]),(0,[z0,z975,z3,z4,z5,z6]),(0,[z0,z2,z3,z23,z5,z6]),(0,[z197,z2,z3,z39,z169,z6]),(0,[z0,z426,z3,z322,z5,z6])],[(0,[z2,z3,z462,z16,z5,z6]),(0,[z0,z272,z3,z352,z5,z6]),(0,[z339,z66,z2,z3,z4,z6])],[(0,[z0,z2,z3,z39,z5,z231]),(0,[z976,z2,z3,z4,z5,z6]),(0,[z0,z977,z3,z4,z5,z6])],[(0,[z544,z2,z3,z4,z5,z18]),(0,[z0,z215,z3,z4,z5,z6]),(0,[z0,z118,z2,z4,z5,z6]),(0,[z0,z121,z2,z3,z11,z4]),(0,[z0,z2,z3,z142,z5,z651])],[(0,[z0,z978,z2,z3,z39,z6]),(0,[z0,z2,z3,z4,z5,z979])],[(0,[z300,z2,z3,z4,z5,z6]),(0,[z0,z2,z353,z16,z5,z6]),(0,[z0,z2,z3,z4,z980,z6]),(0,[z0,z981,z2,z3,z5,z6])]],
   [[(0,[z0,z2,z428,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z982]),(0,[z0,z687,z52,z4,z5,z6]),(0,[z133,z2,z708,z4,z5,z6]),(0,[z2,z3,z16,z169,z327,z6]),(0,[z0,z2,z3,z16,z926,z6]),(0,[z0,z625,z52,z4,z5,z6]),(0,[z0,z167,z822,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z983]),(0,[z2,z3,z16,z5,z362,z6]),(0,[z0,z2,z984,z4,z5,z6]),(0,[z0,z2,z3,z4,z985,z6]),(0,[z0,z986,z3,z4,z5,z6]),(1,[z0,z2,z4,z5,z785])],[(0,[z0,z7,z3,z16,z327,z6]),(0,[z530,z2,z3,z4,z5,z6]),(0,[z35,z0,z121,z2,z3,z15]),(0,[z0,z26,z2,z3,z71,z5])],[(0,[z0,z2,z3,z302,z5,z231]),(0,[z0,z2,z3,z4,z392,z6]),(0,[z0,z931,z3,z16,z5,z6]),(0,[z0,z2,z3,z12,z6,z344])],[],[(0,[z2,z3,z16,z5,z183,z18]),(0,[z0,z2,z3,z4,z987,z6]),(0,[z0,z26,z2,z3,z217,z27])],[(0,[z0,z152,z428,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z988]),(0,[z0,z2,z3,z39,z81,z6]),(0,[z0,z2,z3,z4,z989,z6]),(0,[z0,z2,z3,z990,z5,z6]),(0,[z2,z3,z16,z5,z6,z18]),(0,[z2,z3,z4,z5,z736,z6]),(0,[z0,z2,z3,z991,z5,z6])],[(0,[z0,z2,z3,z992,z5,z6]),(0,[z490,z2,z3,z16,z5,z6]),(0,[z17,z2,z3,z4,z166,z6]),(0,[z0,z3,z30,z732,z5,z6]),(0,[z0,z229,z2,z3,z4,z6])]],
   [[(0,[z2,z708,z51,z4,z5,z6]),(0,[z2,z3,z849,z16,z5,z6]),(0,[z0,z229,z2,z3,z16,z6]),(0,[z0,z3,z4,z5,z6,z993]),(0,[z0,z7,z122,z4,z5,z6])],[(0,[z218,z152,z3,z4,z5,z288]),(0,[z0,z2,z3,z994,z5,z6]),(0,[z658,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z995]),(0,[z0,z996,z3,z4,z5,z6]),(0,[z0,z337,z66,z2,z3,z4])],[(0,[z0,z997,z3,z4,z5,z6]),(0,[z99,z2,z708,z4,z5,z6]),(0,[z0,z544,z2,z3,z5,z82]),(0,[z230,z2,z3,z39,z5,z6]),(0,[z0,z553,z2,z4,z5,z140]),(0,[z0,z2,z3,z4,z5,z998]),(0,[z0,z2,z3,z999,z5,z6]),(0,[z0,z127,z260,z4,z5,z183]),(0,[z0,z2,z4,z5,z785,z6]),(0,[z339,z2,z3,z5,z114,z6]),(0,[z0,z26,z229,z2,z3,z5])],[(0,[z0,z2,z3,z4,z1000,z6]),(0,[z107,z2,z3,z16,z5,z6]),(0,[z2,z3,z16,z386,z5,z6]),(0,[z498,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z146,z5,z262]),(0,[z0,z199,z59,z4,z5,z6]),(0,[z0,z3,z4,z5,z722,z6]),(0,[z0,z2,z3,z5,z114,z835])],[(0,[z2,z3,z16,z5,z551,z6]),(0,[z22,z2,z3,z16,z160,z6]),(0,[z0,z73,z353,z29,z5,z6]),(0,[z0,z2,z3,z1001,z5,z6]),(0,[z0,z2,z3,z1002,z5,z6])],[(0,[z0,z2,z3,z302,z81,z6]),(0,[z0,z2,z1003,z4,z5,z6]),(0,[z0,z2,z3,z1004,z5,z6]),(0,[z0,z2,z3,z4,z5,z1005]),(0,[z0,z2,z353,z39,z5,z6]),(0,[z0,z2,z3,z1006,z5,z6]),(1,[z0,z3,z4,z5,z722]),(0,[z0,z69,z215,z60,z5,z6]),(0,[z0,z121,z2,z3,z12,z5])],[(0,[z0,z2,z3,z4,z1007,z6]),(0,[z0,z2,z3,z1008,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1009]),(0,[z0,z128,z2,z16,z5,z6]),(0,[z0,z1010,z2,z4,z5,z6])]],
   [[(0,[z197,z2,z3,z4,z169,z6]),(0,[z233,z2,z3,z4,z169,z6]),(0,[z0,z3,z4,z5,z6,z1011]),(0,[z0,z272,z3,z30,z5,z6]),(0,[z0,z2,z1012,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1013]),(0,[z0,z2,z3,z447,z5,z6]),(0,[z300,z2,z3,z23,z5,z6]),(0,[z87,z2,z3,z4,z5,z135]),(0,[z0,z2,z3,z5,z6,z1014]),(0,[z35,z0,z2,z3,z15,z6])],[(0,[z0,z487,z3,z4,z5,z183]),(0,[z0,z1015,z2,z3,z4,z6]),(0,[z0,z2,z3,z4,z36,z804])],[(0,[z0,z2,z3,z4,z1016,z6]),(0,[z2,z3,z16,z8,z169,z6]),(0,[z0,z349,z3,z352,z5,z6]),(0,[z547,z2,z3,z16,z5,z6])],[(0,[z107,z2,z3,z16,z5,z284]),(0,[z0,z1017,z2,z3,z5,z6])],[(0,[z218,z152,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z16,z965,z6]),(0,[z22,z2,z3,z4,z5,z736]),(0,[z0,z822,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z722])],[(0,[z0,z2,z3,z1018,z5,z6]),(0,[z0,z1019,z2,z4,z5,z6]),(0,[z1020,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z237,z5,z290]),(0,[z0,z1021,z3,z4,z5,z6]),(0,[z22,z2,z3,z16,z5,z135]),(0,[z0,z577,z2,z4,z83,z6])]],
   [[(0,[z0,z457,z3,z4,z5,z290]),(0,[z107,z2,z3,z16,z169,z6]),(0,[z0,z3,z4,z5,z722,z32]),(0,[z0,z1022,z3,z4,z5,z6]),(0,[z0,z1023,z2,z3,z4,z6]),(0,[z0,z2,z1024,z4,z5,z6])],[(0,[z0,z2,z1025,z16,z5,z6]),(0,[z0,z3,z4,z741,z327,z6])],[(0,[z0,z1026,z2,z3,z4,z6]),(0,[z99,z77,z51,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1027]),(0,[z2,z3,z39,z16,z5,z6]),(0,[z0,z1028,z2,z4,z5,z6]),(0,[z0,z2,z3,z447,z5,z284])],[(0,[z0,z2,z3,z237,z5,z6]),(0,[z0,z1026,z2,z3,z16,z6]),(0,[z0,z2,z3,z4,z469,z36])],[(0,[z0,z457,z3,z4,z5,z6]),(0,[z0,z2,z3,z1029,z5,z6]),(0,[z544,z2,z3,z16,z5,z18]),(0,[z0,z118,z2,z16,z5,z6]),(0,[z0,z120,z2,z16,z5,z21]),(0,[z0,z215,z3,z16,z5,z6]),(0,[z2,z3,z103,z5,z169,z6]),(0,[z0,z630,z52,z4,z5,z6]),(0,[z35,z0,z2,z3,z588,z6])],[(0,[z0,z2,z3,z4,z1030,z6]),(0,[z2,z3,z16,z5,z589,z6]),(0,[z0,z128,z2,z39,z5,z6]),(0,[z0,z2,z3,z1031,z5,z6]),(0,[z0,z238,z52,z4,z5,z6]),(0,[z0,z2,z3,z5,z835,z27]),(0,[z0,z66,z2,z3,z4,z48])],[(0,[z87,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z166,z6]),(0,[z0,z59,z75,z4,z5,z6]),(0,[z0,z2,z3,z732,z5,z6]),(0,[z0,z2,z3,z4,z5,z332])],[(0,[z0,z2,z428,z16,z5,z6]),(0,[z550,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z890,z6])]],
   [[(0,[z0,z2,z984,z16,z5,z6]),(0,[z22,z2,z3,z109,z5,z6]),(0,[z0,z167,z59,z4,z5,z6]),(0,[z0,z2,z3,z1032,z5,z6])],[(0,[z0,z2,z3,z4,z1033,z6]),(0,[z256,z58,z3,z575,z5,z6]),(0,[z530,z2,z3,z16,z5,z6]),(0,[z0,z66,z2,z3,z39,z57]),(0,[z685,z2,z3,z39,z5,z6]),(0,[z0,z1034,z3,z4,z5,z6]),(0,[z0,z2,z3,z1035,z5,z6])],[(0,[z0,z2,z1036,z4,z5,z6]),(0,[z0,z1037,z2,z4,z5,z6]),(0,[z0,z1038,z2,z3,z4,z6]),(0,[z0,z2,z3,z5,z6,z835])],[(0,[z0,z2,z1039,z4,z5,z6]),(0,[z346,z0,z2,z3,z154,z6]),(0,[z107,z2,z3,z447,z108,z6]),(0,[z2,z3,z4,z5,z736,z18]),(0,[z0,z2,z353,z4,z5,z6]),(0,[z0,z7,z3,z4,z629,z6]),(0,[z0,z122,z4,z8,z5,z6]),(0,[z0,z1040,z2,z4,z5,z6])],[(0,[z99,z2,z51,z4,z280,z6]),(0,[z0,z2,z3,z4,z1041,z6]),(0,[z0,z247,z4,z83,z5,z6])],[(0,[z99,z2,z51,z237,z5,z6]),(0,[z0,z2,z3,z16,z1042,z5]),(0,[z22,z2,z3,z39,z5,z135]),(0,[z0,z2,z3,z177,z336,z6])],[(0,[z99,z457,z51,z4,z5,z6]),(0,[z0,z2,z3,z4,z1043,z5]),(0,[z133,z2,z124,z153,z5,z6]),(0,[z0,z7,z3,z4,z327,z6]),(0,[z0,z2,z3,z5,z114,z555])],[(0,[z0,z77,z51,z4,z5,z6]),(0,[z0,z2,z3,z4,z1044,z6]),(1,[z0,z2,z3,z5,z835])]],
   [[(0,[z99,z2,z51,z4,z5,z100]),(0,[z0,z66,z2,z3,z4,z90]),(1,[z0,z337,z66,z2,z3])],[(0,[z0,z2,z138,z162,z5,z6]),(0,[z0,z2,z3,z4,z1045,z6]),(0,[z17,z2,z3,z146,z5,z6]),(0,[z0,z2,z3,z4,z1046,z6]),(0,[z0,z2,z3,z707,z5,z6]),(0,[z0,z131,z2,z4,z890,z6])],[(0,[z0,z2,z428,z4,z5,z231]),(0,[z0,z2,z3,z4,z5,z1047]),(0,[z2,z124,z708,z4,z5,z6]),(0,[z0,z1048,z3,z16,z5,z6]),(0,[z0,z118,z2,z39,z5,z6]),(0,[z0,z120,z2,z39,z5,z21]),(0,[z0,z215,z3,z39,z5,z6]),(1,[z2,z3,z4,z765,z6]),(0,[z0,z2,z3,z1049,z5,z6]),(0,[z1050,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z142,z5,z114])],[(0,[z0,z3,z4,z1051,z5,z6]),(0,[z0,z2,z3,z1052,z5,z6])],[(0,[z300,z2,z3,z39,z5,z6]),(0,[z0,z1053,z2,z3,z5,z6]),(0,[z0,z1054,z2,z3,z4,z5]),(0,[z0,z26,z2,z3,z5,z174]),(0,[z530,z2,z3,z5,z6,z27])],[(0,[z0,z2,z428,z39,z5,z6]),(0,[z0,z2,z3,z4,z1055,z6]),(0,[z0,z104,z3,z4,z8,z6]),(0,[z0,z278,z52,z4,z5,z6]),(0,[z0,z157,z3,z4,z8,z6]),(0,[z0,z42,z4,z5,z140,z6]),(0,[z0,z66,z2,z3,z240,z4])],[(0,[z0,z2,z138,z4,z175,z6]),(0,[z0,z3,z16,z5,z924,z6]),(0,[z0,z2,z3,z4,z1056,z6]),(0,[z0,z1057,z2,z4,z5,z6]),(1,[z0,z2,z3,z729,z6])],[(0,[z0,z2,z3,z1058,z5,z6]),(0,[z0,z2,z3,z16,z6,z217]),(0,[z530,z2,z3,z39,z5,z6]),(0,[z0,z2,z3,z5,z6,z1059])]],
   [[(0,[z0,z2,z3,z4,z1060,z6]),(0,[z0,z2,z3,z23,z166,z6]),(0,[z0,z131,z2,z4,z126,z6]),(0,[z0,z2,z3,z1061,z5,z6])],[(1,[z777,z3,z4,z5,z6]),(0,[z2,z3,z16,z5,z18,z32]),(0,[z2,z3,z590,z16,z5,z6]),(0,[z647,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z1062,z5,z6]),(0,[z0,z2,z1063,z4,z5,z6]),(0,[z0,z337,z66,z2,z3,z57])],[(0,[z0,z2,z3,z1064,z5,z6]),(0,[z22,z2,z3,z849,z5,z6]),(0,[z0,z253,z3,z16,z5,z6])],[(0,[z178,z2,z51,z4,z5,z6]),(0,[z150,z2,z3,z16,z5,z6]),(0,[z0,z128,z2,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1065]),(0,[z0,z2,z3,z4,z1066,z6]),(1,[z35,z0,z121,z2,z3])],[(0,[z0,z2,z428,z302,z5,z6]),(0,[z0,z2,z428,z4,z81,z6]),(0,[z0,z2,z3,z162,z175,z6]),(0,[z218,z152,z3,z16,z5,z6]),(0,[z92,z2,z3,z146,z5,z6]),(0,[z0,z73,z3,z732,z5,z6]),(0,[z530,z2,z3,z142,z5,z6])],[(0,[z0,z1067,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1068,z6]),(0,[z2,z3,z16,z5,z6,z284]),(0,[z0,z553,z3,z4,z5,z183]),(0,[z1069,z2,z3,z4,z5,z6]),(0,[z0,z26,z229,z2,z3,z27])],[(0,[z0,z2,z3,z4,z1070,z6]),(0,[z0,z2,z3,z237,z392,z6]),(0,[z0,z2,z3,z748,z5,z6]),(0,[z0,z3,z16,z1051,z5,z6]),(0,[z0,z2,z3,z1071,z5,z6])],[(0,[z0,z411,z52,z4,z5,z6]),(0,[z0,z457,z3,z4,z392,z6]),(0,[z0,z2,z3,z1072,z5,z6]),(0,[z2,z3,z16,z5,z169,z6]),(0,[z0,z69,z2,z60,z5,z6])]],
   [[(0,[z0,z1073,z3,z4,z5,z6]),(0,[z0,z2,z1074,z4,z5,z6]),(0,[z0,z2,z3,z5,z6,z1075]),(0,[z0,z2,z3,z4,z160,z135]),(0,[z0,z1076,z3,z4,z5,z6])],[(0,[z0,z2,z3,z16,z280,z6]),(0,[z0,z2,z3,z4,z392,z100]),(0,[z0,z1028,z2,z16,z5,z6]),(0,[z0,z73,z3,z322,z5,z6]),(0,[z0,z26,z2,z3,z5,z573]),(0,[z0,z2,z3,z4,z5,z1077]),(0,[z35,z0,z2,z3,z729,z6]),(0,[z0,z337,z2,z3,z67,z5])],[(0,[z0,z2,z3,z4,z1078,z6]),(0,[z0,z2,z1079,z4,z5,z6]),(0,[z0,z2,z1080,z4,z5,z6]),(0,[z0,z2,z3,z4,z169,z262]),(0,[z1081,z0,z2,z3,z5,z6]),(0,[z0,z417,z52,z4,z5,z6]),(0,[z0,z120,z2,z4,z5,z425])],[(0,[z0,z457,z3,z16,z5,z6]),(0,[z22,z2,z3,z4,z5,z135]),(0,[z0,z1082,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z1083,z6])],[(0,[z2,z3,z16,z169,z132,z6]),(0,[z0,z822,z2,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z1084]),(0,[z635,z58,z3,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z100]),(0,[z2,z3,z16,z5,z140,z18]),(0,[z0,z2,z3,z16,z166,z6]),(0,[z2,z3,z16,z5,z504,z6]),(0,[z2,z3,z16,z5,z507,z6]),(0,[z0,z2,z1025,z4,z5,z6]),(0,[z0,z2,z3,z16,z5,z332]),(0,[z0,z2,z3,z39,z6,z217]),(0,[z0,z1085,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z135,z736]),(0,[z0,z1086,z3,z4,z5,z6])],[(0,[z0,z2,z260,z16,z5,z6]),(1,[z2,z3,z4,z5,z736]),(0,[z0,z253,z4,z60,z5,z6]),(1,[z0,z2,z4,z890,z6]),(0,[z0,z1087,z3,z4,z5,z6])],[(0,[z218,z152,z3,z4,z5,z231]),(0,[z0,z167,z59,z16,z5,z6]),(0,[z0,z978,z2,z3,z4,z6]),(0,[z107,z2,z3,z4,z108,z262]),(0,[z0,z423,z3,z29,z5,z6]),(0,[z0,z2,z3,z1088,z5,z6]),(0,[z0,z66,z2,z3,z4,z174])]],
   [[(0,[z0,z2,z3,z1089,z5,z6]),(0,[z0,z120,z2,z4,z5,z21]),(0,[z35,z92,z2,z3,z15,z6])],[(0,[z0,z2,z3,z4,z5,z1090]),(0,[z0,z2,z3,z1091,z5,z6]),(0,[z0,z2,z3,z1092,z5,z6]),(0,[z0,z1037,z2,z16,z5,z6]),(0,[z0,z716,z2,z16,z5,z6]),(0,[z2,z3,z596,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z1093]),(0,[z1094,z2,z3,z4,z5,z6])],[(0,[z218,z152,z3,z39,z5,z6]),(0,[z0,z2,z3,z1095,z5,z6]),(0,[z0,z2,z3,z4,z5,z1096]),(0,[z0,z2,z38,z569,z5,z6]),(0,[z0,z2,z3,z4,z1097,z6])],[(0,[z269,z2,z3,z4,z169,z6]),(0,[z0,z2,z3,z4,z160,z18])],[(0,[z0,z2,z3,z4,z1098,z6])],[(0,[z0,z2,z3,z16,z1043,z5]),(1,[z0,z3,z4,z741,z6]),(0,[z0,z2,z4,z890,z132,z6]),(0,[z0,z117,z2,z4,z5,z785])],[(0,[z0,z1099,z3,z4,z5,z6]),(0,[z611,z2,z3,z39,z5,z6]),(0,[z1100,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z5,z1101]),(0,[z0,z2,z1102,z4,z5,z6]),(0,[z530,z2,z3,z462,z5,z6]),(1,[z0,z2,z3,z4,z804])],[(0,[z0,z2,z3,z39,z280,z6]),(0,[z2,z3,z39,z719,z5,z6]),(0,[z0,z2,z3,z5,z1103,z6])]],
   [[(0,[z0,z2,z3,z4,z5,z1104]),(0,[z22,z2,z3,z16,z5,z6]),(0,[z582,z2,z3,z4,z108,z6]),(0,[z0,z31,z3,z4,z5,z32]),(1,[z0,z2,z707,z5,z6]),(0,[z0,z1105,z3,z4,z5,z6])],[(0,[z218,z152,z3,z302,z5,z6]),(0,[z218,z152,z3,z4,z81,z6]),(0,[z0,z2,z3,z4,z1042,z5]),(0,[z0,z457,z3,z39,z5,z6]),(0,[z0,z752,z3,z4,z5,z6]),(0,[z0,z1106,z3,z4,z5,z6]),(0,[z2,z3,z719,z4,z5,z6]),(0,[z0,z2,z3,z146,z5,z284]),(0,[z607,z2,z3,z4,z108,z6]),(0,[z0,z2,z3,z1107,z5,z6]),(0,[z339,z2,z3,z5,z15,z6])],[(0,[z0,z167,z156,z4,z5,z6]),(0,[z0,z1108,z2,z3,z4,z5])],[(0,[z0,z2,z3,z4,z1109,z6]),(0,[z0,z2,z3,z292,z280,z6]),(0,[z0,z2,z3,z39,z5,z100]),(0,[z133,z2,z124,z16,z5,z6]),(0,[z0,z370,z3,z16,z5,z6]),(0,[z0,z726,z3,z4,z5,z6]),(0,[z0,z2,z3,z39,z166,z6]),(0,[z0,z2,z3,z39,z5,z332])],[(0,[z0,z2,z3,z16,z5,z262]),(0,[z0,z2,z260,z39,z5,z6]),(0,[z0,z2,z3,z4,z5,z1110]),(0,[z0,z733,z2,z3,z5,z6])],[(0,[z0,z457,z3,z292,z5,z6]),(0,[z0,z744,z3,z16,z5,z6]),(0,[z0,z167,z59,z39,z5,z6]),(0,[z0,z601,z3,z4,z327,z6]),(0,[z22,z2,z3,z23,z5,z135]),(0,[z0,z2,z3,z4,z741,z6]),(0,[z1094,z337,z2,z3,z5,z6])],[(0,[z0,z1048,z3,z4,z5,z6]),(0,[z0,z66,z2,z3,z4,z211]),(0,[z49,z2,z3,z4,z5,z18]),(0,[z0,z2,z3,z1111,z5,z6]),(0,[z1112,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z1113,z5,z6])],[(0,[z0,z1114,z2,z4,z5,z6]),(0,[z0,z77,z3,z4,z5,z290]),(0,[z0,z2,z3,z292,z5,z100]),(0,[z0,z287,z3,z30,z5,z6]),(0,[z0,z2,z3,z4,z1115,z6])]],
   [[(0,[z0,z2,z3,z575,z5,z6]),(0,[z49,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z4,z5,z1116]),(0,[z0,z2,z4,z83,z890,z6])],[(0,[z0,z2,z3,z4,z1117,z6])],[(0,[z0,z1118,z3,z4,z5,z6]),(0,[z0,z131,z2,z16,z132,z6]),(0,[z107,z2,z3,z146,z108,z6]),(0,[z0,z2,z3,z1119,z5,z6])],[(0,[z0,z77,z3,z4,z5,z6]),(0,[z2,z3,z16,z5,z6,z561]),(0,[z0,z2,z3,z312,z5,z6]),(0,[z0,z7,z3,z39,z327,z6]),(0,[z0,z105,z52,z4,z5,z6]),(0,[z0,z2,z3,z1120,z5,z6]),(0,[z0,z2,z3,z4,z6,z217]),(0,[z0,z2,z3,z4,z67,z804])],[(0,[z0,z2,z3,z1121,z5,z6]),(0,[z2,z3,z23,z16,z5,z6]),(0,[z0,z2,z3,z342,z12,z6]),(0,[z70,z2,z3,z109,z5,z18]),(0,[z0,z1122,z3,z4,z5,z6]),(0,[z0,z2,z3,z1123,z5,z6])],[(0,[z0,z2,z3,z1124,z5,z6]),(0,[z0,z2,z3,z4,z1125,z6])],[(0,[z0,z3,z16,z5,z6,z993]),(0,[z173,z2,z3,z39,z5,z6]),(0,[z0,z253,z3,z4,z5,z6]),(0,[z2,z3,z1126,z4,z5,z6]),(0,[z0,z127,z128,z4,z5,z183])],[(0,[z0,z2,z4,z710,z5,z6]),(0,[z0,z2,z38,z53,z5,z6]),(0,[z1127,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z6,z804])]],
   [[(0,[z0,z2,z138,z4,z5,z288]),(0,[z0,z381,z3,z16,z5,z6]),(0,[z0,z2,z4,z5,z6,z1128]),(0,[z0,z2,z3,z1129,z5,z6]),(0,[z0,z2,z3,z4,z1130,z6])],[(0,[z0,z2,z3,z4,z280,z290]),(0,[z107,z2,z3,z4,z172,z6]),(0,[z0,z117,z370,z4,z5,z140])],[(0,[z461,z2,z3,z16,z5,z6]),(0,[z0,z2,z3,z39,z5,z262]),(0,[z0,z817,z2,z3,z39,z5]),(0,[z0,z59,z822,z4,z5,z6])],[(0,[z0,z2,z3,z1131,z5,z6])],[],[(0,[z0,z2,z3,z4,z280,z6]),(0,[z133,z2,z124,z277,z5,z6]),(0,[z2,z3,z16,z5,z79,z6]),(0,[z0,z683,z2,z4,z5,z21])],[(0,[z0,z2,z3,z162,z5,z288]),(0,[z0,z121,z2,z3,z39,z5]),(0,[z0,z2,z3,z1132,z5,z6]),(0,[z26,z530,z2,z3,z5,z27])],[(0,[z197,z2,z3,z198,z169,z6]),(0,[z0,z1133,z3,z4,z5,z6]),(0,[z1134,z2,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 523) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 531) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1054).take 146) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1200)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 531, 146] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 103).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 103).take 101).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 204).take 52).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [103, 101, 52] = true :=
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

end PEqualNP.Outside.L_meta_40471

theorem PEqualNP.Outside.L_meta_40471 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4008370176) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_40471.solve