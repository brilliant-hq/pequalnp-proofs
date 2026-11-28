import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37563

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4276666560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0001308ac431bcc8#64 ++ 0x40001308ac431bcc#64 ++ 0xe04f719fc473fccf#64 ++ 0xae04f719fc473fcc#64 : BitVec 256),
   (0x0094162605845554#64 ++ 0x8009416260584555#64 ++ 0xb1b49e66078c7fff#64 ++ 0x7b1b49e66078c7ff#64 : BitVec 256),
   (0x2628e058580a8aa9#64 ++ 0x02628e058580a8aa#64 ++ 0xee38e078780f8ffe#64 ++ 0xfee38e078780f8ff#64 : BitVec 256),
   (0x1b40fb806ed00f0e#64 ++ 0x01b40fb806ed00f0#64 ++ 0x5fc0ff807ff00f0d#64 ++ 0xf5fc0ff807ff00f0#64 : BitVec 256),
   (0x4dff0000336f6000#64 ++ 0x04dff0000336f600#64 ++ 0x6fff00007ffff00b#64 ++ 0xf6fff00007ffff00#64 : BitVec 256),
   (0x8ffecd7500000000#64 ++ 0x08ffecd750000000#64 ++ 0x9fffffff80000007#64 ++ 0xe9fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.and, [2, 4]⟩, ⟨.or, [1, 7]⟩, ⟨.and, [8, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [8, 3]⟩, ⟨.and, [11, 4]⟩, ⟨.or, [12, 5]⟩, ⟨.and, [10, 13]⟩, ⟨.or, [6, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe04f719fc473fccf 0xae04f719fc473fcc

def z1 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b49e66078c7fff 0x7b1b49e66078c7ff

def z2 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z3 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee38e078780f8ffe 0xfee38e078780f8ff

def z4 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff00007ffff00b 0xf6fff00007ffff00

def z5 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fffffff80000007 0xe9fffffff8000000

def z6 : W := mkw 0x0094042401044010 0x8009404240104401 0x00300060000c0030 0x000300060000c003

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x804f719f80000007 0xa804f719f8000000

def z8 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xdfcfff9ffff00f0f 0xfdfcfff9ffff00f0

def z9 : W := mkw 0x84bf047f8021b0c0 0x484bf047f8021b0c 0xa03f007f8003f0c2 0x0a03f007f8003f0c

def z10 : W := mkw 0x1b40e9806a500a0a 0x01b40e9806a500a0 0x4e40e18078700f0c 0xf4e40e18078700f0

def z11 : W := mkw 0x8ffecd7501044000 0x08ffecd750104400 0xbfffffff878c700f 0xfbfffffff878c700

def z12 : W := mkw 0x4097000001256000 0x0409700000125600 0x0007000000007000 0x0000700000000700

def z13 : W := mkw 0x2200e05848008aa9 0x02200e05848008aa 0x8000e07800000ff4 0x08000e07800000ff

def z14 : W := mkw 0x49d7000023656000 0x049d700002365600 0x01c7000007f07001 0x001c7000007f0700

def z15 : W := mkw 0x09d4162627c45554 0x809d4162627c4555 0xfff49e667ffc7fff 0xffff49e667ffc7ff

def z16 : W := mkw 0x4001308af77ffcc8 0x44001308af77ffcc 0xe04f719ffffffccf 0xbe04f719ffffffcc

def z17 : W := mkw 0x19401b8026d00506 0x019401b8026d0050 0x11c01f8007f00001 0x011c01f8007f0000

def z18 : W := mkw 0x1b40cb002ac00306 0x01b40cb002ac0030 0x1f808e003b800300 0x51f808e003b80030

def z19 : W := mkw 0x0094042601045050 0x8009404260104505 0xa0340066000c70f2 0x0a0340066000c70f

def z20 : W := mkw 0x44bf0000112f6000 0x044bf0000112f600 0x203f0000000ff002 0x0203f0000000ff00

def z21 : W := mkw 0x1b40db802ed00706 0x01b40db802ed0070 0x1fc09f803ff00301 0x51fc09f803ff0030

def z22 : W := mkw 0x2200f0dacc109ee9 0x42200f0dacc109ee 0x8000f1ff80000ff4 0x08000f1ff80000ff

def z23 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x11c71f8780000001 0x011c71f878000000

def z24 : W := mkw 0xaffeed7d580a8aa9 0x0affeed7d580a8aa 0xfffffffff80f8fff 0xffffffffff80f8ff

def z25 : W := mkw 0x3f68cb503aca0327 0x03f68cb503aca032 0x1fb08e603b8c0330 0x51fb08e603b8c033

def z26 : W := mkw 0x0940000022400000 0x0094000002240000 0x4fc000007ff00009 0xf4fc000007ff0000

def z27 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x4e38e078780f8330 0xd4e38e078780f833

def z28 : W := mkw 0x24280058100a80a1 0x024280058100a80a 0xa0388078000f8ffe 0x7a0388078000f8ff

def z29 : W := mkw 0x000120084021a888 0x0000120084021a88 0xe04f60184473fccf 0xae04f60184473fcc

def z30 : W := mkw 0x0094042400000000 0x0009404240000000 0xb1b49e66000c0fff 0x7b1b49e66000c0ff

def z31 : W := mkw 0x4dff1002376f7440 0x04dff1002376f744 0xefff10067ffffccf 0xfefff10067ffffcc

def z32 : W := mkw 0x1200fb804c900f0e 0x01200fb804c900f0 0x1000ff8000000f04 0x01000ff8000000f0

def z33 : W := mkw 0x8ffeed7d40008888 0x08ffeed7d4000888 0xffffffffc0038ccf 0xeffffffffc0038cc

def z34 : W := mkw 0x0b40c90022400000 0x00b40c9002240000 0x5fc0ff807ff0000d 0xf5fc0ff807ff0000

def z35 : W := mkw 0x2628c050180a0221 0x02628c050180a022 0x0e308060380c0330 0x50e308060380c033

def z36 : W := mkw 0x0000120004800504 0x0000012000480050 0x11809e0007800f0d 0x711809e0007800f0

def z37 : W := mkw 0x8ffec95100000000 0x08ffec9510000000 0x0fff619980000003 0xe0fff61998000000

def z38 : W := mkw 0x300032887eda8faf 0x0300032887eda8fa 0x600000007fff8ff8 0x1600000007fff8ff

def z39 : W := mkw 0xc9d70d2523656000 0x0c9d70d252365600 0x11c71f8787f07001 0x011c71f8787f0700

def z40 : W := mkw 0x40010000336f6000 0x040010000336f600 0x600000007ffff008 0x1600000007ffff00

def z41 : W := mkw 0x8200cd7500000000 0x08200cd750000000 0x9000ffff80000004 0x09000ffff8000000

def z42 : W := mkw 0x44bf0000112f6000 0x044bf0000112f600 0x607f0000447ff00b 0xa607f0000447ff00

def z43 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fb000007ffff008 0x56fb000007ffff00

def z44 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x600000004473fcc8 0x0600000004473fcc

def z45 : W := mkw 0x26bce47e590edaf9 0x826bce47e590edaf 0xee3ce07e780ffffe 0xfee3ce07e780ffff

def z46 : W := mkw 0x2200e058580a8aa9 0x02200e058580a8aa 0xe000e078780f8ffc 0x1e000e078780f8ff

def z47 : W := mkw 0x1bd5ffaeeff5ffde 0xc1bd5ffaeeff5ffd 0xffffffffffffffff 0xffffffffffffffff

def z48 : W := mkw 0x40950000336f6000 0x040950000336f600 0x61b400007ffff00b 0x761b400007ffff00

def z49 : W := mkw 0x8bd6cd7500000000 0x08bd6cd750000000 0x91c7ffff80000005 0x091c7ffff8000000

def z50 : W := mkw 0x0094042400000000 0x0009404240000000 0x91b49e6600000007 0x691b49e660000000

def z51 : W := mkw 0x4d6b0000336f6000 0x04d6b0000336f600 0x6e4b00007ffff008 0x96e4b00007ffff00

def z52 : W := mkw 0x19401b8026d00506 0x019401b8026d0050 0x5fc01f807ff00009 0xf5fc01f807ff0000

def z53 : W := mkw 0x4d6b0000326b2000 0x04d6b0000326b200 0x6e4f00007c73f00b 0xa6e4f00007c73f00

def z54 : W := mkw 0x5bd7fb806ff56f0e 0x05bd7fb806ff56f0 0x5fc7ff807ff07f0d 0xf5fc7ff807ff07f0

def z55 : W := mkw 0x0094042400000000 0x0009404240000000 0x91ffffff80000007 0xe91ffffff8000000

def z56 : W := mkw 0x4dff062433ef6114 0x84dff062433ef611 0x7fff8e607ffff33b 0xf7fff8e607ffff33

def z57 : W := mkw 0x0000100204001440 0x0000010020400144 0xa0349066040c7fff 0x7a0349066040c7ff

def z58 : W := mkw 0x5f6bfb807efb2f0e 0x05f6bfb807efb2f0 0x5fcbff807ff38f0d 0xf5fcbff807ff38f0

def z59 : W := mkw 0x0000162604801554 0x8000016260480155 0x91809e6607800ffd 0x791809e6607800ff

def z60 : W := mkw 0x2628f05a5c0a9ee9 0x02628f05a5c0a9ee 0xee3cf07e7c0fffff 0xfee3cf07e7c0ffff

def z61 : W := mkw 0x0dfe000000000000 0x00dfe00000000000 0x0fb0000000000000 0x40fb000000000000

def z62 : W := mkw 0x0094162605845554 0x8009416260584555 0x11841e0607807001 0x011841e060780700

def z63 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x4e08601878038000 0x84e0860187803800

def z64 : W := mkw 0x0940120026c00504 0x00940120026c0050 0x5fc09e007ff00f0d 0xf5fc09e007ff00f0

def z65 : W := mkw 0xaf6ae959580a8aa9 0x0af6ae959580a8aa 0x4e4b6199f8038000 0x84e4b6199f803800

def z66 : W := mkw 0x8fffcd7f8021b0c0 0x48fffcd7f8021b0c 0xbfffffff8003f0c7 0xebfffffff8003f0c

def z67 : W := mkw 0x0628c05000000000 0x00628c0500000000 0x8e7ff1ff80000007 0xe8e7ff1ff8000000

def z68 : W := mkw 0x0094162605845554 0x8009416260584555 0x91b09e66038c0ff4 0x591b09e66038c0ff

def z69 : W := mkw 0x40010000336f6000 0x040010000336f600 0x604f00007ffff00b 0xb604f00007ffff00

def z70 : W := mkw 0x100032826fd45f5e 0x8100032826fd45f5 0x600000007ffc7ff8 0x1600000007ffc7ff

def z71 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91cf7f9f80000007 0xa91cf7f9f8000000

def z72 : W := mkw 0x009534aec535fcd8 0xc009534aec535fcd 0xe07f71ffc47ffcff 0xae07f71ffc47ffcf

def z73 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0x4e00e00078000f0c 0xf4e00e00078000f0

def z74 : W := mkw 0x3f68fbd87eda8faf 0x03f68fbd87eda8fa 0xfff8fff87fff8fff 0xffff8fff87fff8ff

def z75 : W := mkw 0x0628c05000000000 0x00628c0500000000 0x8e38e07800000006 0xe8e38e0780000000

def z76 : W := mkw 0x20002008580a8aa9 0x020002008580a8aa 0x60000000780f8ff8 0x160000000780f8ff

def z77 : W := mkw 0x0628c050100a0000 0x00628c050100a000 0xee38e078780f800e 0xfee38e078780f800

def z78 : W := mkw 0x9ffefff56ed00f0e 0x09ffefff56ed00f0 0xdffffffffff00f0f 0xfdffffffffff00f0

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0300060000c00f2 0x0a0300060000c00f

def z80 : W := mkw 0x0094000001044000 0x0009400000104400 0x21b40000078c700b 0x721b40000078c700

def z81 : W := mkw 0x4dff162637ef7554 0x84dff162637ef755 0xffff9e667fffffff 0xfffff9e667ffffff

def z82 : W := mkw 0x0000000022400000 0x0000000002240000 0x400000007ff00008 0x1400000007ff0000

def z83 : W := mkw 0x8ffecd75100a0000 0x08ffecd75100a000 0xfffffffff80f800f 0xffffffffff80f800

def z84 : W := mkw 0x0094162605845554 0x8009416260584555 0x31841e06078c7ff9 0x131841e06078c7ff

def z85 : W := mkw 0x8201fdffc431bcc8 0x48201fdffc431bcc 0xf04fffffc473fccf 0xaf04fffffc473fcc

def z86 : W := mkw 0x26bcf67e5d8edffd 0x826bcf67e5d8edff 0xffbcfe7e7f8fffff 0xfffbcfe7e7f8ffff

def z87 : W := mkw 0x0000000000000000 0x0000000000000000 0xa0308060000c0ffe 0x7a0308060000c0ff

def z88 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff80607fffffff 0xfefff80607ffffff

def z89 : W := mkw 0x8ffedd7704001440 0x08ffedd770400144 0xbfffffff84007ccf 0xebfffffff84007cc

def z90 : W := mkw 0x1b41fb8aeef1bfce 0x41b41fb8aeef1bfc 0xffcfff9ffff3ffcf 0xfffcfff9ffff3ffc

def z91 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5f808e007ff00f08 0x55f808e007ff00f0

def z92 : W := mkw 0x0094120205845554 0x8009412020584555 0x21b40000078c7ffb 0x721b40000078c7ff

def z93 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1fb08e6000000000 0x41fb08e600000000

def z94 : W := mkw 0x8ffedf7705845554 0x88ffedf770584555 0xbfffffff878c7fff 0xfbfffffff878c7ff

def z95 : W := mkw 0xcfffcd75336f6000 0x0cfffcd75336f600 0xfffffffffffff00f 0xffffffffffffff00

def z96 : W := mkw 0x20002008580a8aa9 0x020002008580a8aa 0xe0308060780f8ffe 0x7e0308060780f8ff

def z97 : W := mkw 0x8ffecd7522400000 0x08ffecd752240000 0xdffffffffff0000f 0xfdffffffffff0000

def z98 : W := mkw 0x8628cd7500000000 0x08628cd750000000 0x9e38ffff80000006 0xe9e38ffff8000000

def z99 : W := mkw 0x009536aec5b5fddc 0xc009536aec5b5fdd 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z100 : W := mkw 0x0094042400000000 0x0009404240000000 0x11841e0600000001 0x011841e060000000

def z101 : W := mkw 0x0940000022400000 0x0094000002240000 0x01c0000007f00001 0x001c0000007f0000

def z102 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x404f719fc473f001 0x8404f719fc473f00

def z103 : W := mkw 0x1b40fb826fd45f5e 0x81b40fb826fd45f5 0x7fc0ff807ffc7ffd 0xf7fc0ff807ffc7ff

def z104 : W := mkw 0x2f68e958580a8aa9 0x02f68e958580a8aa 0xfff8fff8780f8fff 0xffff8fff8780f8ff

def z105 : W := mkw 0x0001000a8021b0c0 0x40001000a8021b0c 0xa00f001f8003f0c2 0x0a00f001f8003f0c

def z106 : W := mkw 0x4943000022612000 0x0494300002261200 0x0043000000700000 0x0004300000070000

def z107 : W := mkw 0x1294ffa64d945f5e 0x81294ffa64d945f5 0xb1b4ffe6078c7fff 0x7b1b4ffe6078c7ff

def z108 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x2fbf00003b8ff002 0x52fbf00003b8ff00

def z109 : W := mkw 0x04290000102b2000 0x004290000102b200 0x6e7f00007c7ff00b 0xf6e7f00007c7ff00

def z110 : W := mkw 0x0000120205845554 0x8000012020584555 0x0000000007807000 0x0000000000780700

def z111 : W := mkw 0x0000162604801554 0x8000016260480155 0xb0309e66000c0ffe 0x7b0309e66000c0ff

def z112 : W := mkw 0x06bcc47400000000 0x006bcc4740000000 0x9fbcfe7e00000007 0xe9fbcfe7e0000000

def z113 : W := mkw 0x8f6acd7500000000 0x08f6acd750000000 0x9e4bffff80000004 0x89e4bffff8000000

def z114 : W := mkw 0x8f6ac95100000000 0x08f6ac9510000000 0x0e4b619980000000 0x80e4b61998000000

def z115 : W := mkw 0x00012088c031a888 0x400012088c031a88 0x404b6199c0738000 0x8404b6199c073800

def z116 : W := mkw 0x0000308ac4109cc8 0x40000308ac4109cc 0x8000719f80000cc4 0x08000719f80000cc

def z117 : W := mkw 0x0094162605845554 0x8009416260584555 0x31b08e60078c7ff8 0x531b08e60078c7ff

def z118 : W := mkw 0x24280058100a80a1 0x024280058100a80a 0x0008001800038000 0x0000800180003800

def z119 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x4fcf00007ff3f001 0x84fcf00007ff3f00

def z120 : W := mkw 0x2000320a5d8edffd 0x82000320a5d8edff 0x600000007f8ffff8 0x1600000007f8ffff

def z121 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1ff79fe780000001 0x41ff79fe78000000

def z122 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000719f80000004 0x08000719f8000000

def z123 : W := mkw 0x5f6be9807a7b2a0a 0x05f6be9807a7b2a0 0x4e4b618078738000 0x84e4b61807873800

def z124 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x0ff700003ffc7001 0x50ff700003ffc700

def z125 : W := mkw 0x0dfe000000000000 0x00dfe00000000000 0x0fff000000000003 0xe0fff00000000000

def z126 : W := mkw 0x0000200840008888 0x0000020084000888 0xe038e078400f8ffe 0xfe038e078400f8ff

def z127 : W := mkw 0x0000000000000000 0x0000000000000000 0x0047118780000001 0x0004711878000000

def z128 : W := mkw 0x0200c00008000200 0x00200c0000800020 0x0e00800038000300 0x50e0080003800030

def z129 : W := mkw 0x1b40e9806a500a0a 0x01b40e9806a500a0 0x4fc061807ff00009 0xf4fc061807ff0000

def z130 : W := mkw 0x4dff0424336f6000 0x04dff0424336f600 0xffff9e667ffff00f 0xfffff9e667ffff00

def z131 : W := mkw 0x19403b806ed00f0e 0x019403b806ed00f0 0x51c01f807ff00f09 0x151c01f807ff00f0

def z132 : W := mkw 0x0000308044100c08 0x00000308044100c0 0x0000718000000c04 0x00000718000000c0

def z133 : W := mkw 0x1200cb0008800306 0x01200cb000880030 0x10008e0000000300 0x010008e000000030

def z134 : W := mkw 0x4dfe0000334e4000 0x04dfe0000334e400 0x0fff00003b8c0003 0xf0fff00003b8c000

def z135 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x6e386018780f800a 0xf6e386018780f800

def z136 : W := mkw 0x04280000100a0000 0x004280000100a000 0x6e380000780f800a 0xf6e380000780f800

def z137 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xce38e07878038006 0xece38e0787803800

def z138 : W := mkw 0x0941000022612000 0x0094100002261200 0x6fcf00007ff3f00b 0xf6fcf00007ff3f00

def z139 : W := mkw 0x0001308044312c08 0x00001308044312c0 0x604f71804473fc0f 0xa604f71804473fc0

def z140 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0xee30e060780c0ffe 0xfee30e060780c0ff

def z141 : W := mkw 0x8dfe0d2500000000 0x08dfe0d250000000 0x1fff1f8780000003 0xe1fff1f878000000

def z142 : W := mkw 0x2629f0dadc3bbee9 0x42629f0dadc3bbee 0xee7ff1fffc7fffff 0xfee7ff1fffc7ffff

def z143 : W := mkw 0x0094362e4584dddc 0x80094362e4584ddd 0xf1bcfe7e478fffff 0xff1bcfe7e478ffff

def z144 : W := mkw 0x00013088c431ac88 0x400013088c431ac8 0x404b7199c4738c0d 0xa404b7199c4738c0

def z145 : W := mkw 0x49d7000023656000 0x049d700002365600 0x21f7000007fc700b 0x721f7000007fc700

def z146 : W := mkw 0x4fffc900336f6000 0x04fffc900336f600 0x7fffff807ffff00f 0xf7fffff807ffff00

def z147 : W := mkw 0x0000308ac4109cc8 0x40000308ac4109cc 0xe008719fc0038cce 0xae008719fc0038cc

def z148 : W := mkw 0x0b40c90000000000 0x00b40c9000000000 0x1fc0ff8000000005 0xe1fc0ff800000000

def z149 : W := mkw 0x0000100204001440 0x0000010020400144 0xa004100604007ccf 0x2a004100604007cc

def z150 : W := mkw 0x0000162604801554 0x8000016260480155 0x90009e6600000ff4 0x090009e6600000ff

def z151 : W := mkw 0x0094120005844504 0x0009412000584450 0x31b49e00078c7f0f 0x731b49e00078c7f0

def z152 : W := mkw 0x84be047500000000 0x084be04750000000 0x803f007f80000002 0x0803f007f8000000

def z153 : W := mkw 0xc4bf0475112f6000 0x0c4bf0475112f600 0xa03f007f800ff002 0x0a03f007f800ff00

def z154 : W := mkw 0x0628c05000000000 0x00628c0500000000 0xae38e078000c0ffe 0xfae38e078000c0ff

def z155 : W := mkw 0x89d61f2705845554 0x889d61f270584555 0x11c71f8787807001 0x011c71f878780700

def z156 : W := mkw 0x8dfe047500000000 0x08dfe04750000000 0x8fff007f80000003 0xe8fff007f8000000

def z157 : W := mkw 0x194032806ed00f0e 0x0194032806ed00f0 0x4fc000007ff00f09 0xf4fc000007ff00f0

def z158 : W := mkw 0x0001328ac5b5fddc 0xc0001328ac5b5fdd 0x6000000047fffff8 0x16000000047fffff

def z159 : W := mkw 0x0000308044100c08 0x00000308044100c0 0x4040718044700c0d 0xa4040718044700c0

def z160 : W := mkw 0x4dfe0000334e4000 0x04dfe0000334e400 0x6fb800007b8f800a 0xf6fb800007b8f800

def z161 : W := mkw 0x9ffeedf56a500a0a 0x09ffeedf56a500a0 0xdffffffff8700007 0xedffffffff870000

def z162 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xbfffffff800c0fff 0xfbfffffff800c0ff

def z163 : W := mkw 0x26bce058590ecaa9 0x026bce058590ecaa 0xefbce0787f8fffff 0xfefbce0787f8ffff

def z164 : W := mkw 0x1b40e9806a500a0a 0x01b40e9806a500a0 0x5fc0ff8078700005 0xe5fc0ff807870000

def z165 : W := mkw 0x24280058100a80a1 0x024280058100a80a 0xa0380078000f80f2 0x0a0380078000f80f

def z166 : W := mkw 0x4fffc050336f6000 0x04fffc050336f600 0xefffe0787ffff00f 0xfefffe0787ffff00

def z167 : W := mkw 0x0dff308ac431bcc8 0x40dff308ac431bcc 0xefff719fc473fccf 0xeefff719fc473fcc

def z168 : W := mkw 0x0001108284313440 0x4000110828431344 0x0047118784707001 0x0004711878470700

def z169 : W := mkw 0x2628e05848008aa9 0x02628e05848008aa 0x8e38e07800000ff6 0xe8e38e07800000ff

def z170 : W := mkw 0x44bf0426112f7050 0x844bf0426112f705 0xa03f0066000ff0f2 0x0a03f0066000ff0f

def z171 : W := mkw 0x4dfe0000334e4000 0x04dfe0000334e400 0x4ff000007ffc0009 0xf4ff000007ffc000

def z172 : W := mkw 0x0001328ac4b1bdcc 0x40001328ac4b1bdc 0xf1cfff9fc7f3ffcf 0xff1cfff9fc7f3ffc

def z173 : W := mkw 0x0200f2004c800f0c 0x00200f2004c800f0 0x5f80fe007f800f0d 0xf5f80fe007f800f0

def z174 : W := mkw 0x4d6b0000326b2000 0x04d6b0000326b200 0x4e4b000078738000 0x84e4b00007873800

def z175 : W := mkw 0x0ffec90000000000 0x00ffec9000000000 0x1fffff8000000007 0xe1fffff800000000

def z176 : W := mkw 0x0000000000000000 0x0000000000000000 0x004b619980000000 0x8004b61998000000

def z177 : W := mkw 0x0000020001844114 0x8000002000184411 0x00000000038c0330 0x100000000038c033

def z178 : W := mkw 0x2629f0dadc3bbee9 0x42629f0dadc3bbee 0xee38e0787c7ffffe 0xfee38e0787c7ffff

def z179 : W := mkw 0x0000120205845554 0x8000012020584555 0xa0041006078c7fff 0x3a0041006078c7ff

def z180 : W := mkw 0x1ffefb806ed00f0e 0x01ffefb806ed00f0 0x5fffff807ff00f0f 0xf5fffff807ff00f0

def z181 : W := mkw 0x1b40e9806a500a0a 0x01b40e9806a500a0 0x4e40618078700000 0x84e4061807870000

def z182 : W := mkw 0x2628f0dadc1a9ee9 0x42628f0dadc1a9ee 0xee38f1fff80f8ffe 0xfee38f1fff80f8ff

def z183 : W := mkw 0x6f6be0587a6baaa9 0x06f6be0587a6baaa 0xee7be078787f8ffe 0xfee7be078787f8ff

def z184 : W := mkw 0x6dff20087b6feaa9 0x06dff20087b6feaa 0x6fff00007ffffffb 0xf6fff00007ffffff

def z185 : W := mkw 0x8fffcd7500212000 0x08fffcd750021200 0xffffffffc473f00f 0xeffffffffc473f00

def z186 : W := mkw 0x0094042601045050 0x8009404260104505 0xa0348066000c7ffe 0x7a0348066000c7ff

def z187 : W := mkw 0x0001008080312000 0x4000100808031200 0x0043018180700000 0x0004301818070000

def z188 : W := mkw 0x0001000000212000 0x0000100000021200 0x604f00004473f00b 0xa604f00004473f00

def z189 : W := mkw 0x4dff308af77ffcc8 0x44dff308af77ffcc 0xefff719ffffffccf 0xfefff719ffffffcc

def z190 : W := mkw 0x3f68e9d87a5a8aab 0x03f68e9d87a5a8aa 0x4e48619878738000 0x84e4861987873800

def z191 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1fcf7f9f80000001 0x81fcf7f9f8000000

def z192 : W := mkw 0x8f6ac95100000000 0x08f6ac9510000000 0x8e7be1f980000006 0xe8e7be1f98000000

def z193 : W := mkw 0x26bce47c580a8aa9 0x026bce47c580a8aa 0xffbcfe7e780f8fff 0xfffbcfe7e780f8ff

def z194 : W := mkw 0x0094000001044000 0x0009400000104400 0x01b00000038c0000 0x501b00000038c000

def z195 : W := mkw 0x9f6afbd16ed00f0e 0x09f6afbd16ed00f0 0x5fcbff99fff00f0d 0xf5fcbff99fff00f0

def z196 : W := mkw 0x6fffe0587b6feaa9 0x06fffe0587b6feaa 0xefffe0787fffffff 0xfefffe0787ffffff

def z197 : W := mkw 0x0001000000212000 0x0000100000021200 0x404b000040738000 0x8404b00004073800

def z198 : W := mkw 0x2628c050180a0221 0x02628c050180a022 0x0e00000038000000 0x00e0000003800000

def z199 : W := mkw 0x24280050100a0021 0x024280050100a002 0x00300060000c0030 0x000300060000c003

def z200 : W := mkw 0x0094162605845554 0x8009416260584555 0x11b49e66078c7331 0x511b49e66078c733

def z201 : W := mkw 0x0000120205845554 0x8000012020584555 0x20000000078c7ff8 0x120000000078c7ff

def z202 : W := mkw 0x0000120004800504 0x0000012000480050 0xb1b09e60078c0fff 0x7b1b09e60078c0ff

def z203 : W := mkw 0xcfffcd75112f6000 0x0cfffcd75112f600 0xbfffffff800ff007 0xebfffffff800ff00

def z204 : W := mkw 0x44bf0000112f6000 0x044bf0000112f600 0x21bf0000078ff00b 0x721bf0000078ff00

def z205 : W := mkw 0x8bd6cd2500000000 0x08bd6cd250000000 0x1fc7ff8780000005 0xe1fc7ff878000000

def z206 : W := mkw 0x0094062601845154 0x8009406260184515 0xb1b48e66038c73f2 0x5b1b48e66038c73f

def z207 : W := mkw 0x009536aec5b5fddc 0xc009536aec5b5fdd 0xf1b49e6647ffffff 0x7f1b49e6647fffff

def z208 : W := mkw 0x0001108a8431b4c0 0x40001108a8431b4c 0xa04f119f8473f0c3 0x0a04f119f8473f0c

def z209 : W := mkw 0x24282058580a8aa9 0x024282058580a8aa 0xe0380078780f8ffa 0x1e0380078780f8ff

def z210 : W := mkw 0x0000200840008888 0x0000020084000888 0xe008601840038cce 0xae008601840038cc

def z211 : W := mkw 0x4dfe0000334e4000 0x04dfe0000334e400 0x0fb000003b8c0000 0x50fb000003b8c000

def z212 : W := mkw 0x8200cd7500000000 0x08200cd750000000 0x904fffff80000007 0xa904fffff8000000

def z213 : W := mkw 0x99d61fa526d00506 0x099d61fa526d0050 0x11c71f8787f00001 0x011c71f8787f0000

def z214 : W := mkw 0x1b40c9002a400202 0x01b40c9002a40020 0x0e00000038000000 0x00e0000003800000

def z215 : W := mkw 0x0094062401844114 0x8009406240184411 0x11b08e60038c0330 0x511b08e60038c033

def z216 : W := mkw 0x2001308adc3bbee9 0x42001308adc3bbee 0x600000007c7ffff8 0x1600000007c7ffff

def z217 : W := mkw 0xcfffdf7737ef7554 0x8cfffdf7737ef755 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x66bfe058592feaa9 0x066bfe058592feaa 0xee3fe078780ffffe 0xfee3fe078780ffff

def z219 : W := mkw 0x1001328aeef1bfce 0x41001328aeef1bfc 0xe04f719ffff3ffcf 0xbe04f719ffff3ffc

def z220 : W := mkw 0x26bcc674198e4335 0x826bcc674198e433 0x1fb08e603b8c0330 0x51fb08e603b8c033

def z221 : W := mkw 0x100032806ed00f0e 0x0100032806ed00f0 0x51809e007ff00f0d 0x751809e007ff00f0

def z222 : W := mkw 0x0000308ac4109cc8 0x40000308ac4109cc 0x0000000000000cc0 0x00000000000000cc

def z223 : W := mkw 0x0201f08acc31bec8 0x40201f08acc31bec 0xee4ff19ffc73ffcf 0xfee4ff19ffc73ffc

def z224 : W := mkw 0x1200fb8acc909fce 0x41200fb8acc909fc 0x9000ff9f80000fc4 0x09000ff9f80000fc

def z225 : W := mkw 0x100032806ed00f0e 0x0100032806ed00f0 0x400000007ff00f08 0x1400000007ff00f0

def z226 : W := mkw 0xcffecd75334e4000 0x0cffecd75334e400 0x9fffffffbb8c0007 0xf9fffffffbb8c000

def z227 : W := mkw 0x4dff0426336f7050 0x84dff0426336f705 0xefff00667ffff0fb 0xfefff00667ffff0f

def z228 : W := mkw 0x1b40cb002ac00306 0x01b40cb002ac0030 0x5fc08e007ff00309 0xf5fc08e007ff0030

def z229 : W := mkw 0x0b40c90000000000 0x00b40c9000000000 0x0e40618000000000 0x80e4061800000000

def z230 : W := mkw 0x0000000001044000 0x0000000000104400 0x20000000078c7008 0x120000000078c700

def z231 : W := mkw 0x4dfe062433ce4114 0x84dfe062433ce411 0x1fb08e603b8c0330 0x51fb08e603b8c033

def z232 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xc04b719fc0738cc4 0x8c04b719fc0738cc

def z233 : W := mkw 0x5ffffb807fff6f0e 0x05ffffb807fff6f0 0x7fffff807fffff0f 0xf7fffff807fffff0

def z234 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe000719fc473fccc 0x0e000719fc473fcc

def z235 : W := mkw 0x1b40eb806ad00b0e 0x01b40eb806ad00b0 0x5fc0ef807bf00300 0xd5fc0ef807bf0030

def z236 : W := mkw 0x0000000000000000 0x0000000000000000 0x0040718000000005 0xa004071800000000

def z237 : W := mkw 0x0094042601045050 0x8009404260104505 0x0004000600007000 0x0000400060000700

def z238 : W := mkw 0x2f68e0587a4a8aa9 0x02f68e0587a4a8aa 0xeff8e0787fff8fff 0xfeff8e0787fff8ff

def z239 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x60471187c473fcc9 0x060471187c473fcc

def z240 : W := mkw 0x8ffecf7501844114 0x88ffecf750184411 0x9fffffff838c0337 0xf9fffffff838c033

def z241 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee7ff1fff80f8fff 0xfee7ff1fff80f8ff

def z242 : W := mkw 0x0ffec05000000000 0x00ffec0500000000 0x8fffe07800000007 0xe8fffe0780000000

def z243 : W := mkw 0x0000208040100808 0x0000020804010080 0x4040618040700000 0x8404061804070000

def z244 : W := mkw 0x64bf0058112fe0a1 0x064bf0058112fe0a 0xa03f0078000ff0f2 0x0a03f0078000ff0f

def z245 : W := mkw 0x0000108004100400 0x0000010800410040 0x0040118004700001 0x0004011800470000

def z246 : W := mkw 0x0000200840008888 0x0000020084000888 0x8000601800000cc4 0x08000601800000cc

def z247 : W := mkw 0x1200e98048100a0a 0x01200e98048100a0 0x0000618000000000 0x0000061800000000

def z248 : W := mkw 0x0000308044100c08 0x00000308044100c0 0xc04f719fc4700c0f 0xac04f719fc4700c0

def z249 : W := mkw 0x0095000001256000 0x0009500000125600 0x61ff000047fff00b 0xf61ff000047fff00

def z250 : W := mkw 0x49d7162627e57554 0x849d7162627e5755 0x11c71e0607f07001 0x011c71e0607f0700

def z251 : W := mkw 0xaffecd75180a0221 0x0affecd75180a022 0x1fb08e60380c0330 0x51fb08e60380c033

def z252 : W := mkw 0x8f6ac95100000000 0x08f6ac9510000000 0x8e4f719f80000007 0xa8e4f719f8000000

def z253 : W := mkw 0x44be0000110e4000 0x044be0000110e400 0x00300000000c0000 0x000300000000c000

def z254 : W := mkw 0x86becd7500000000 0x086becd750000000 0x903fffff80000006 0x0903fffff8000000

def z255 : W := mkw 0x500132807fff6f0e 0x0500132807fff6f0 0x600000007fffff08 0x1600000007fffff0

def z256 : W := mkw 0x49410000336f6000 0x049410000336f600 0x6fc000007ffff009 0xf6fc000007ffff00

def z257 : W := mkw 0x8ffffdffc431bcc8 0x48ffffdffc431bcc 0xffffffffc473fccf 0xeffffffffc473fcc

def z258 : W := mkw 0x1bd4ffa66fd45f5e 0x81bd4ffa66fd45f5 0xfff4ffe67ffc7fff 0xffff4ffe67ffc7ff

def z259 : W := mkw 0x4001120237ef7554 0x84001120237ef755 0x600000007ffffff8 0x1600000007ffffff

def z260 : W := mkw 0x2628c058100a80a1 0x02628c058100a80a 0xae38e078000f80f6 0xeae38e078000f80f

def z261 : W := mkw 0x44bf000a912ff0c0 0x444bf000a912ff0c 0xa03f001f800ff0c2 0x0a03f001f800ff0c

def z262 : W := mkw 0x2628c050180a0221 0x02628c050180a022 0x6e388060780f833a 0xf6e388060780f833

def z263 : W := mkw 0xcdff0475336f6000 0x0cdff0475336f600 0xefff007ffffff00b 0xfefff007ffffff00

def z264 : W := mkw 0x0001108284313440 0x4000110828431344 0x804f719f84707007 0xa804f719f8470700

def z265 : W := mkw 0x4d6a0000324a0000 0x04d6a0000324a000 0x0e00000038000000 0x00e0000003800000

def z266 : W := mkw 0x0001000000212000 0x0000100000021200 0x200f00000003f002 0x0200f00000003f00

def z267 : W := mkw 0x1940098022500002 0x0194009802250000 0x0040018000700000 0x0004001800070000

def z268 : W := mkw 0x0095042e8125f0d0 0xc0095042e8125f0d 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z269 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fb49e6600000007 0x69fb49e660000000

def z270 : W := mkw 0x00012088c031a888 0x400012088c031a88 0xc04f719fc0738007 0xac04f719fc073800

def z271 : W := mkw 0x000100088021a080 0x4000100088021a08 0x000b001980038000 0x0000b00198003800

def z272 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fb8ee7800000006 0xe9fb8ee780000000

def z273 : W := mkw 0x44290000336f6000 0x044290000336f600 0x6e3800007ffff00a 0xf6e3800007ffff00

def z274 : W := mkw 0x0000100204001440 0x0000010020400144 0x0004100604007001 0x0000410060400700

def z275 : W := mkw 0x40000000334e4000 0x040000000334e400 0x000000003b8c0000 0x1000000003b8c000

def z276 : W := mkw 0x4001308af77ffcc8 0x44001308af77ffcc 0x600000007ffffcc8 0x1600000007ffffcc

def z277 : W := mkw 0x009436aec594dddc 0xc009436aec594ddd 0xb1b4ffff878c7fff 0x7b1b4ffff878c7ff

def z278 : W := mkw 0x100032804c900f0e 0x0100032804c900f0 0x0000000000000f00 0x00000000000000f0

def z279 : W := mkw 0x1001328aeef1bfce 0x41001328aeef1bfc 0x600000007ff3ffc8 0x1600000007ff3ffc

def z280 : W := mkw 0x0200c90000000000 0x00200c9000000000 0x1000ff8000000004 0x01000ff800000000

def z281 : W := mkw 0x6f6be0587a6baaa9 0x06f6be0587a6baaa 0x4e4b601878738000 0x84e4b60187873800

def z282 : W := mkw 0x1200ffa64c901f5e 0x81200ffa64c901f5 0x9000ffe600000ff4 0x09000ffe600000ff

def z283 : W := mkw 0x0095162605a57554 0x80095162605a5755 0xf1ff9e6647ffffff 0xff1ff9e6647fffff

def z284 : W := mkw 0x0000120004800504 0x0000012000480050 0x0000000007800f08 0x10000000007800f0

def z285 : W := mkw 0x8200c95100000000 0x08200c9510000000 0x0000619980000000 0x0000061998000000

def z286 : W := mkw 0x04280000100a0000 0x004280000100a000 0xee388060780f8ffe 0xfee388060780f8ff

def z287 : W := mkw 0x00000000100a0000 0x000000000100a000 0x60000000780f8008 0x160000000780f800

def z288 : W := mkw 0x0bd4df2605845554 0x80bd4df260584555 0xbff4ffe6078c7fff 0xfbff4ffe6078c7ff

def z289 : W := mkw 0x9f6ae9d16a500a0a 0x09f6ae9d16a500a0 0x4e4b6199f8700000 0x84e4b6199f870000

def z290 : W := mkw 0x1b40cb002ac00306 0x01b40cb002ac0030 0x1fc0ff803b800305 0xf1fc0ff803b80030

def z291 : W := mkw 0x00013082c4313c48 0x400013082c4313c4 0x40477187c4707c0d 0xa40477187c4707c0

def z292 : W := mkw 0x2001308adc3bbee9 0x42001308adc3bbee 0xe04f719ffc7fffff 0xbe04f719ffc7ffff

def z293 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xa00f719f8003fcc6 0x0a00f719f8003fcc

def z294 : W := mkw 0x2294f67e4d84dffd 0x82294f67e4d84dff 0xb1b4fe7e078c7fff 0x7b1b4fe7e078c7ff

def z295 : W := mkw 0x0940308066500c08 0x00940308066500c0 0x4fc071807ff00c0d 0xf4fc071807ff00c0

def z296 : W := mkw 0x0000308844108c88 0x00000308844108c8 0xe048719844738ccf 0xae048719844738cc

def z297 : W := mkw 0x44bf0000336f6000 0x044bf0000336f600 0x603f00007ffff00a 0x1603f00007ffff00

def z298 : W := mkw 0x3b40fbd86ed08faf 0x03b40fbd86ed08fa 0xdfc0fff87ff00ffd 0xfdfc0fff87ff00ff

def z299 : W := mkw 0x49d7308ae775fcc8 0x449d7308ae775fcc 0xe1cf719fc7f3fccf 0xae1cf719fc7f3fcc

def z300 : W := mkw 0x0200e00848008a88 0x00200e00848008a8 0xee08e01878038fce 0xfee08e01878038fc

def z301 : W := mkw 0x19403b8066d00d0e 0x019403b8066d00d0 0x51c07f8047f00c0d 0xa51c07f8047f00c0

def z302 : W := mkw 0x8ffedf7704801554 0x88ffedf770480155 0x9fffffff80000ff7 0xe9fffffff80000ff

def z303 : W := mkw 0x0b40c90000000000 0x00b40c9000000000 0x9fcfff9f80000007 0xe9fcfff9f8000000

def z304 : W := mkw 0x1bd4ffa46ed00f0e 0x01bd4ffa46ed00f0 0xdff4ffe67ff00f0f 0xfdff4ffe67ff00f0

def z305 : W := mkw 0x0628e000580a0a08 0x00628e000580a0a0 0x6e38e000780f8f0e 0xf6e38e000780f8f0

def z306 : W := mkw 0x59d71b8027f56506 0x059d71b8027f5650 0x11c71f8007f07001 0x011c71f8007f0700

def z307 : W := mkw 0x1b40db8026d00506 0x01b40db8026d0050 0x1fc0ff8007f00005 0xe1fc0ff8007f0000

def z308 : W := mkw 0x0000100004000400 0x0000010000400040 0x0000100004000c0d 0x20000100004000c0

def z309 : W := mkw 0x0094162405844514 0x8009416240584451 0x11b09e60078c0f3d 0x711b09e60078c0f3

def z310 : W := mkw 0x2629e058582baaa9 0x02629e058582baaa 0xee7fe0787c7fffff 0xfee7fe0787c7ffff

def z311 : W := mkw 0x0094162605845554 0x8009416260584555 0x11849e0607807f0d 0x711849e0607807f0

def z312 : W := mkw 0x2ffee058580a8aa9 0x02ffee058580a8aa 0xefffe078780f8fff 0xfefffe078780f8ff

def z313 : W := mkw 0x0094142605045450 0x8009414260504545 0xa0341066040c7cff 0x2a0341066040c7cf

def z314 : W := mkw 0x2429005a902bb0e1 0x42429005a902bb0e 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z315 : W := mkw 0x8200df7704801554 0x88200df770480155 0x9000ffff80000ff4 0x09000ffff80000ff

def z316 : W := mkw 0x86bec47500000000 0x086bec4750000000 0x8e3fe07f80000006 0xe8e3fe07f8000000

def z317 : W := mkw 0x4dff2088f37fe888 0x44dff2088f37fe88 0x6fff6199fffff00b 0xf6fff6199fffff00

def z318 : W := mkw 0x0000308044100c08 0x00000308044100c0 0x4000000044700c08 0x04000000044700c0

def z319 : W := mkw 0x0094062401844114 0x8009406240184411 0xb1b08e60038c0ffe 0x7b1b08e60038c0ff

def z320 : W := mkw 0x2201f0dacc31bee9 0x42201f0dacc31bee 0xe04ff1ffc473ffff 0xae04ff1ffc473fff

def z321 : W := mkw 0x6fffc0503b6f6221 0x06fffc0503b6f622 0x6fff80607ffff33b 0xf6fff80607ffff33

def z322 : W := mkw 0x24bc047e110ed0f1 0x824bc047e110ed0f 0xa03c007e000ff0f2 0x0a03c007e000ff0f

def z323 : W := mkw 0x00012088c031a888 0x400012088c031a88 0x604f6199c473f00b 0xa604f6199c473f00

def z324 : W := mkw 0x0000200840008888 0x0000020084000888 0x4008601840038000 0x8400860184003800

def z325 : W := mkw 0x3628fbd85c9a8faf 0x03628fbd85c9a8fa 0xfe38fff8780f8ffe 0xffe38fff8780f8ff

def z326 : W := mkw 0xcffecd75334e4000 0x0cffecd75334e400 0x1fb08e603b8c0000 0x51fb08e603b8c000

def z327 : W := mkw 0x19d41fa627d45556 0x819d41fa627d4555 0xb1f49fe607fc7fff 0x7b1f49fe607fc7ff

def z328 : W := mkw 0x2200e05848008aa9 0x02200e05848008aa 0xce00e07878000ffc 0xfce00e07878000ff

def z329 : W := mkw 0x0dfe0000100a0000 0x00dfe0000100a000 0x6fff0000780f800b 0xf6fff0000780f800

def z330 : W := mkw 0x1bd4cf242bc44316 0x81bd4cf242bc4431 0x1fb08e603b8c0330 0x51fb08e603b8c033

def z331 : W := mkw 0x1200fb804c900f0e 0x01200fb804c900f0 0x5e00ff8078000f0c 0xf5e00ff8078000f0

def z332 : W := mkw 0xcfffcd7523656000 0x0cfffcd752365600 0x9fffffff87f07007 0xe9fffffff87f0700

def z333 : W := mkw 0x00012088c031a888 0x400012088c031a88 0x4000000040738000 0x0400000004073800

def z334 : W := mkw 0x2200f67e4c809ffd 0x82200f67e4c809ff 0x9000fe7e00000ff4 0x09000fe7e00000ff

def z335 : W := mkw 0x0094000001044000 0x0009400000104400 0x0184000007807001 0x0018400000780700

def z336 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b41e66078c70f3 0x0b1b41e66078c70f

def z337 : W := mkw 0xaffecd75180a0221 0x0affecd75180a022 0x9fffffffb80c0337 0xf9fffffffb80c033

def z338 : W := mkw 0x0628c05000000000 0x00628c0500000000 0x0e08601800000000 0x80e0860180000000

def z339 : W := mkw 0x0000200048000a08 0x00000200048000a0 0x4000000078000f08 0x14000000078000f0

def z340 : W := mkw 0x49d7000023656000 0x049d700002365600 0x61cf000047f3f00b 0xa61cf000047f3f00

def z341 : W := mkw 0x5ffefb807fde4f0e 0x05ffefb807fde4f0 0x5ff0ff807ffc0f0d 0xf5ff0ff807ffc0f0

def z342 : W := mkw 0x0000000201045050 0x8000000020104505 0x20000000000c70f0 0x020000000000c70f

def z343 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xfff0ffe07ffc0fff 0xffff0ffe07ffc0ff

def z344 : W := mkw 0x0200c05000000000 0x00200c0500000000 0x8000e07800000004 0x08000e0780000000

def z345 : W := mkw 0x4dff36aef7fffddc 0xc4dff36aef7fffdd 0xffffffffffffffff 0xffffffffffffffff

def z346 : W := mkw 0x8200fdffc4109cc8 0x48200fdffc4109cc 0x9000ffff80000cc4 0x09000ffff80000cc

def z347 : W := mkw 0x8ffedf7705845554 0x88ffedf770584555 0x9fffffff87807007 0xe9fffffff8780700

def z348 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1ffffff878c7fff 0xfb1ffffff878c7ff

def z349 : W := mkw 0xcdff0d25336f6000 0x0cdff0d25336f600 0x7fff1f87fffff00b 0xf7fff1f87fffff00

def z350 : W := mkw 0x4095162637ef7554 0x84095162637ef755 0xf1b49e667fffffff 0x7f1b49e667ffffff

def z351 : W := mkw 0x8ffeed7548000a08 0x08ffeed7548000a0 0xdffffffff8000f0f 0xfdffffffff8000f0

def z352 : W := mkw 0x0000000000000000 0x0000000000000000 0x800f001f80000002 0x0800f001f8000000

def z353 : W := mkw 0x80000d2500000000 0x080000d250000000 0x10001f8780000000 0x010001f878000000

def z354 : W := mkw 0x0094062401844114 0x8009406240184411 0x11800e0003800000 0x011800e000380000

def z355 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x1f80ff803b800f04 0x51f80ff803b800f0

def z356 : W := mkw 0x84be047500000000 0x084be04750000000 0x0030006000000000 0x0003000600000000

def z357 : W := mkw 0x3f68eb587aca8baf 0x03f68eb587aca8ba 0xffb8ee787b8f8ffe 0xfffb8ee787b8f8ff

def z358 : W := mkw 0x0000120004800504 0x0000012000480050 0x10009e0000000f04 0x010009e0000000f0

def z359 : W := mkw 0x20002008580a8aa9 0x020002008580a8aa 0x4000000078038000 0x0400000007803800

def z360 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe07ff1ffc47fffff 0xfe07ff1ffc47ffff

def z361 : W := mkw 0x0000100204001440 0x0000010020400144 0xa04f719f84007ccf 0xaa04f719f84007cc

def z362 : W := mkw 0x0f68c95000000000 0x00f68c9500000000 0x9ff8fff800000007 0xe9ff8fff80000000

def z363 : W := mkw 0x1b41fb82eef13f4e 0x41b41fb82eef13f4 0x5fc7ff87fff07f0d 0xf5fc7ff87fff07f0

def z364 : W := mkw 0x8000047500000000 0x0800004750000000 0x8000007f80000000 0x08000007f8000000

def z365 : W := mkw 0x3f69fbdafefbbfef 0x43f69fbdafefbbfe 0xffffffffffffffff 0xffffffffffffffff

def z366 : W := mkw 0x0000200840008888 0x0000020084000888 0xe04f719fc0038ccf 0xae04f719fc0038cc

def z367 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff719ffffff00f 0xfefff719ffffff00

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000800000000f0c 0x70000800000000f0

def z369 : W := mkw 0x0001108284313440 0x4000110828431344 0xa047118784707ccf 0x2a047118784707cc

def z370 : W := mkw 0x0dfe042400000000 0x00dfe04240000000 0x9fff9e6600000007 0xe9fff9e660000000

def z371 : W := mkw 0x84bf34ffc431bcc8 0x484bf34ffc431bcc 0xe07f71ffc473fccf 0xae07f71ffc473fcc

def z372 : W := mkw 0x0000100204001440 0x0000010020400144 0x8000100600000cc4 0x08000100600000cc

def z373 : W := mkw 0x0094042400000000 0x0009404240000000 0x8034006600000002 0x0803400660000000

def z374 : W := mkw 0x1bd4ffa66fd45f5e 0x81bd4ffa66fd45f5 0x5fc4ff867ff07f0d 0xf5fc4ff867ff07f0

def z375 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fbf8e7f80000002 0x49fbf8e7f8000000

def z376 : W := mkw 0x0000120004800504 0x0000012000480050 0x11801e0007800001 0x011801e000780000

def z377 : W := mkw 0x8f6be9d9c031a888 0x48f6be9d9c031a88 0x4e4b6199c0738000 0x84e4b6199c073800

def z378 : W := mkw 0x0001100204213440 0x0000110020421344 0xe04f10064473fccf 0xae04f10064473fcc

def z379 : W := mkw 0x0001000a8021b0c0 0x40001000a8021b0c 0xa04f719f8003f0c7 0xaa04f719f8003f0c

def z380 : W := mkw 0x9ffecf752ac00306 0x09ffecf752ac0030 0x9fffffffbb800307 0xf9fffffffbb80030

def z381 : W := mkw 0x0000120204801554 0x8000012020480155 0x0000000000000ff0 0x00000000000000ff

def z382 : W := mkw 0x4fffe0007b6f6a08 0x04fffe0007b6f6a0 0x6fffe0007fffff0f 0xf6fffe0007fffff0

def z383 : W := mkw 0x0001208ac031b8c8 0x40001208ac031b8c 0xe04f619fc073f0c2 0x8e04f619fc073f0c

def z384 : W := mkw 0x842a005100000000 0x0842a00510000000 0x000b001980000000 0x0000b00198000000

def z385 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x4e4061807ff00f08 0x94e4061807ff00f0

def z386 : W := mkw 0x1f68fb807eda0f0e 0x01f68fb807eda0f0 0x7ff8ff807fff8f0f 0xf7ff8ff807fff8f0

def z387 : W := mkw 0x600120087b6feaa9 0x0600120087b6feaa 0x600000007ffffff8 0x1600000007ffffff

def z388 : W := mkw 0x2000200848008aa9 0x02000200848008aa 0x0000000000000ff0 0x00000000000000ff

def z389 : W := mkw 0x06bcd67605845554 0x806bcd6760584555 0xbfbcfe7e078c7fff 0xfbfbcfe7e078c7ff

def z390 : W := mkw 0x9fffffffeef1bfce 0x49fffffffeef1bfc 0xfffffffffff3ffcf 0xffffffffffff3ffc

def z391 : W := mkw 0x009516a685b57554 0xc009516a685b5755 0xb1f79fe787fc7fff 0x7b1f79fe787fc7ff

def z392 : W := mkw 0x4dff162637ef7554 0x84dff162637ef755 0x7fff1e067ffff00b 0xf7fff1e067ffff00

def z393 : W := mkw 0x2629e0d8d83baaa9 0x42629e0d8d83baaa 0xee7be1f9f87f8ffe 0xfee7be1f9f87f8ff

def z394 : W := mkw 0x0001000280213040 0x4000100028021304 0x0007000780007000 0x0000700078000700

def z395 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xce08e07878038ff4 0x8ce08e07878038ff

def z396 : W := mkw 0x1b40fb8aeed09fce 0x41b40fb8aeed09fc 0xdfc0ff9ffff00fcd 0xfdfc0ff9ffff00fc

def z397 : W := mkw 0x0000000000000000 0x0000000000000000 0x4040000044700009 0xa404000004470000

def z398 : W := mkw 0x89d71da784313440 0x489d71da78431344 0x11c71f8784707001 0x011c71f878470700

def z399 : W := mkw 0x9200fff54c900f0e 0x09200fff54c900f0 0x9000ffff80000f04 0x09000ffff80000f0

def z400 : W := mkw 0x0000000800008080 0x0000000080000808 0xa0080018000380c2 0x0a0080018000380c

def z401 : W := mkw 0x04282008500a8888 0x004282008500a888 0xee386018780f8cce 0xfee386018780f8cc

def z402 : W := mkw 0x1201fb8accb1bfce 0x41201fb8accb1bfc 0xf04fff9fc473ffcf 0xaf04fff9fc473ffc

def z403 : W := mkw 0x0094162605845554 0x8009416260584555 0x31b41e06078c700b 0x731b41e06078c700

def z404 : W := mkw 0x0094162605845554 0x8009416260584555 0x91849e6607807ff5 0x091849e6607807ff

def z405 : W := mkw 0x1f68fbd06ed00f0e 0x01f68fbd06ed00f0 0xdff8fff87ff00f0f 0xfdff8fff87ff00f0

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0x8004100600000007 0x2800410060000000

def z407 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x6e308060780f8ff8 0x56e308060780f8ff

def z408 : W := mkw 0x1b41e988ea71aa8a 0x41b41e988ea71aa8 0x4e4b6199f8738000 0x84e4b6199f873800

def z409 : W := mkw 0x0094062401844114 0x8009406240184411 0x31b48e60078c733b 0x731b48e60078c733

def z410 : W := mkw 0x8ffecd7701045050 0x88ffecd770104505 0xbfffffff800c70f7 0xebfffffff800c70f

def z411 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5e40ff8078700f04 0x85e40ff8078700f0

def z412 : W := mkw 0x44bf0000112f6000 0x044bf0000112f600 0x6e3f0000780ff00a 0xf6e3f0000780ff00

def z413 : W := mkw 0x0dfe000001044000 0x00dfe00000104400 0x2fff0000078c700b 0xf2fff0000078c700

def z414 : W := mkw 0xa6bee47d580a8aa9 0x0a6bee47d580a8aa 0xee3fe07ff80f8ffe 0xfee3fe07ff80f8ff

def z415 : W := mkw 0x4dff3080777f6c08 0x04dff3080777f6c0 0x6fff71807ffffc0f 0xf6fff71807ffffc0

def z416 : W := mkw 0x00012088c031a888 0x400012088c031a88 0xe04b6199c0738cce 0xae04b6199c0738cc

def z417 : W := mkw 0xcffffdfff77ffcc8 0x4cffffdfff77ffcc 0xfffffffffffffccf 0xffffffffffffffcc

def z418 : W := mkw 0x0000308244101c48 0x00000308244101c4 0xe044718644707ccf 0xae044718644707cc

def z419 : W := mkw 0x5b41fb807fff6f0e 0x05b41fb807fff6f0 0x7fc0ff807fffff0d 0xf7fc0ff807fffff0

def z420 : W := mkw 0x8fffffffc5b5fddc 0xc8fffffffc5b5fdd 0xffffffffc7ffffff 0xfffffffffc7fffff

def z421 : W := mkw 0x04280000100a0000 0x004280000100a000 0x0e300000380c0000 0x50e300000380c000

def z422 : W := mkw 0x4dff120237ef7554 0x84dff120237ef755 0x6fff00007ffffffb 0xf6fff00007ffffff

def z423 : W := mkw 0x0000120205845554 0x8000012020584555 0x31809e00078c7ffd 0x731809e00078c7ff

def z424 : W := mkw 0x0000200840008888 0x0000020084000888 0x6000000040038cc8 0x06000000040038cc

def z425 : W := mkw 0x8942090100000000 0x0894209010000000 0x0043018180000000 0x0004301818000000

def z426 : W := mkw 0x2628f67e5c8a9ffd 0x82628f67e5c8a9ff 0xfe38fe7e780f8ffe 0xffe38fe7e780f8ff

def z427 : W := mkw 0x3628f2d87eda8faf 0x03628f2d87eda8fa 0xee38e0787fff8ffe 0xfee38e0787fff8ff

def z428 : W := mkw 0x1b40eb006ac00b0e 0x01b40eb006ac00b0 0x5f80ee007b800f0c 0xf5f80ee007b800f0

def z429 : W := mkw 0x0001328ac5b5fddc 0xc0001328ac5b5fdd 0xe04f719fc7ffffff 0xbe04f719fc7fffff

def z430 : W := mkw 0x1200fb806ed00f0e 0x01200fb806ed00f0 0x5000ff807ff00f0c 0x15000ff807ff00f0

def z431 : W := mkw 0x8294df7705845554 0x88294df770584555 0xb1b4ffff878c7fff 0x7b1b4ffff878c7ff

def z432 : W := mkw 0x0000162605845554 0x8000016260584555 0xb0009e66078c7ffc 0x1b0009e66078c7ff

def z433 : W := mkw 0x4dff0000326b2000 0x04dff0000326b200 0x4fff000078738003 0xe4fff00007873800

def z434 : W := mkw 0x0dfe000022400000 0x00dfe00002240000 0x4fff00007ff0000b 0xf4fff00007ff0000

def z435 : W := mkw 0xa628ed7d580a8aa9 0x0a628ed7d580a8aa 0xfe38fffff80f8ffe 0xffe38fffff80f8ff

def z436 : W := mkw 0x0dfe000000000000 0x00dfe00000000000 0x8fff719f80000007 0xe8fff719f8000000

def z437 : W := mkw 0x8ffedf7705845554 0x88ffedf770584555 0xbfb49e66078c7fff 0x7bfb49e66078c7ff

def z438 : W := mkw 0x04280000100a0000 0x004280000100a000 0x4e08000078038000 0x84e0800007803800

def z439 : W := mkw 0x0000000000000000 0x0000000000000000 0x4e00000078000008 0xf4e0000007800000

def z440 : W := mkw 0x0001108284313440 0x4000110828431344 0x604f1187c473f00b 0xa604f1187c473f00

def z441 : W := mkw 0x0094100205045440 0x0009410020504544 0xa1b41006078c7ccf 0x7a1b41006078c7cc

def z442 : W := mkw 0x0001100a8421b4c0 0x40001100a8421b4c 0xa00f101f8403fccf 0x2a00f101f8403fcc

def z443 : W := mkw 0x5fffe9807b7f6a0a 0x05fffe9807b7f6a0 0x6fff61807ffff00b 0xf6fff61807ffff00

def z444 : W := mkw 0x0000020000800104 0x0000002000080010 0x11808e0003800300 0x511808e000380030

def z445 : W := mkw 0x0dfe162605845554 0x80dfe16260584555 0xbfff9e66078c7fff 0xfbfff9e66078c7ff

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x8008601800000006 0xa800860180000000

def z447 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe00f001fc473fcca 0x0e00f001fc473fcc

def z448 : W := mkw 0x0940000022400000 0x0094000002240000 0x0f8000003b800000 0x50f8000003b80000

def z449 : W := mkw 0x19400b0022c00106 0x019400b0022c0010 0x11800e0003800000 0x011800e000380000

def z450 : W := mkw 0x0000000000000000 0x0000000000000000 0x004f000000000003 0xa004f00000000000

def z451 : W := mkw 0x0094000001044000 0x0009400000104400 0xa1b48060078c7fff 0x7a1b48060078c7ff

def z452 : W := mkw 0x0000000000000000 0x0000000000000000 0x200400000400700b 0x2200400000400700

def z453 : W := mkw 0x4dff308af77ffcc8 0x44dff308af77ffcc 0x6fff00007ffffccb 0xf6fff00007ffffcc

def z454 : W := mkw 0x1200f2806ed00f0e 0x01200f2806ed00f0 0x4e00e0007ff00f0c 0xf4e00e0007ff00f0

def z455 : W := mkw 0x20002008580a8aa9 0x020002008580a8aa 0xe0086018780f8ffe 0xbe0086018780f8ff

def z456 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x604b6199c473fcc8 0x8604b6199c473fcc

def z457 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x8e30e078380c0ff4 0x58e30e078380c0ff

def z458 : W := mkw 0xcfffcd75336f6000 0x0cfffcd75336f600 0x7fff8e607ffff00b 0xf7fff8e607ffff00

def z459 : W := mkw 0x20000008100a80a1 0x020000008100a80a 0x20000000000f80f0 0x020000000000f80f

def z460 : W := mkw 0x1b40fb826ed01f4e 0x01b40fb826ed01f4 0xffc4ff867ff07fcf 0xfffc4ff867ff07fc

def z461 : W := mkw 0x44bf162615af7554 0x844bf162615af755 0xb1bf9e66078fffff 0x7b1bf9e66078ffff

def z462 : W := mkw 0x4dff000ab36ff0c0 0x44dff000ab36ff0c 0xefff001ffffff0cb 0xfefff001ffffff0c

def z463 : W := mkw 0x24282058500a88a9 0x024282058500a88a 0xe0386078400f8cfe 0xae0386078400f8cf

def z464 : W := mkw 0x1bd4fb806fd44f0e 0x01bd4fb806fd44f0 0x7ff4ff807ffc7f0f 0xf7ff4ff807ffc7f0

def z465 : W := mkw 0x0b40e90048000a08 0x00b40e90048000a0 0x5fc0ff8078000f0d 0xf5fc0ff8078000f0

def z466 : W := mkw 0x4dfe0000334e4000 0x04dfe0000334e400 0x2fb400003f8c700b 0x72fb400003f8c700

def z467 : W := mkw 0x0000000000000000 0x0000000000000000 0x11809e0000000005 0x611809e000000000

def z468 : W := mkw 0x5fffffa67fff7f5e 0x85fffffa67fff7f5 0xffffffe67fffffff 0xfffffffe67ffffff

def z469 : W := mkw 0x04bc0000110e4000 0x004bc0000110e400 0x6fbc00007f8ff00b 0xf6fbc00007f8ff00

def z470 : W := mkw 0x2629e05ad82bbae9 0x42629e05ad82bbae 0xee3fe07ff80ffffe 0xfee3fe07ff80ffff

def z471 : W := mkw 0x242930dad43bbce9 0x4242930dad43bbce 0xe07f71ffc47ffcff 0xae07f71ffc47ffcf

def z472 : W := mkw 0x5fffcb003bef6306 0x05fffcb003bef630 0x7fff8e007ffff30b 0xf7fff8e007ffff30

def z473 : W := mkw 0x0200c00000000000 0x00200c0000000000 0x0e00e00000000004 0xe0e00e0000000000

def z474 : W := mkw 0x0000200040000808 0x0000020004000080 0x4000600040000c0c 0xa4000600040000c0

def z475 : W := mkw 0x2200e008580a8aa9 0x02200e008580a8aa 0x6e00e000780f8ffc 0xf6e00e000780f8ff

def z476 : W := mkw 0x2200e05848008aa9 0x02200e05848008aa 0xe008e07840038ffe 0xae008e07840038ff

def z477 : W := mkw 0x0b40f98044100c08 0x00b40f98044100c0 0x5fc0ff8044700c0d 0xe5fc0ff8044700c0

def z478 : W := mkw 0x0dff000000212000 0x00dff00000021200 0x6fff00004473f00b 0xe6fff00004473f00

def z479 : W := mkw 0x0000000000000000 0x0000000000000000 0x20000000000c0ff8 0x120000000000c0ff

def z480 : W := mkw 0x0000162604801554 0x8000016260480155 0x10001e0600000000 0x010001e060000000

def z481 : W := mkw 0x4d6b0000326b2000 0x04d6b0000326b200 0x6e7b0000787f800a 0xf6e7b0000787f800

def z482 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x21ff000007fff003 0x021ff000007fff00

def z483 : W := mkw 0x6dff0058336fe0a1 0x06dff0058336fe0a 0xefff00787ffff0fb 0xfefff00787ffff0f

def z484 : W := mkw 0x20000058000080a1 0x020000058000080a 0x80000078000000f0 0x080000078000000f

def z485 : W := mkw 0xcf6bc951326b2000 0x0cf6bc951326b200 0x4e4b6199f8738000 0x84e4b6199f873800

def z486 : W := mkw 0x00002088c0108888 0x400002088c010888 0x0000619980000000 0x0000061998000000

def z487 : W := mkw 0x0000062400800114 0x8000006240080011 0x10008e6000000330 0x010008e600000033

def z488 : W := mkw 0x100032806ed00f0e 0x0100032806ed00f0 0x404071807ff00f0d 0xb404071807ff00f0

def z489 : W := mkw 0x0094042400000000 0x0009404240000000 0x11b08e6000000000 0x411b08e600000000

def z490 : W := mkw 0x2628c050180a0221 0x02628c050180a022 0x8e38e078380c0336 0xf8e38e078380c033

def z491 : W := mkw 0xdffffff57fff6f0e 0x0dffffff57fff6f0 0xffffffffffffff0f 0xfffffffffffffff0

def z492 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0x4e00600078000000 0x84e0060007800000

def z493 : W := mkw 0x0000300a44009cc8 0x00000300a44009cc 0xe00c701e4403fccf 0xae00c701e4403fcc

def z494 : W := mkw 0xaf6ae959580a8aa9 0x0af6ae959580a8aa 0xee7be1f9f80f8ffe 0xfee7be1f9f80f8ff

def z495 : W := mkw 0x24bc167e158ed5f5 0x824bc167e158ed5f 0xb1bc9e7e078fffff 0x7b1bc9e7e078ffff

def z496 : W := mkw 0x0001108284313440 0x4000110828431344 0x0000000004707000 0x0000000000470700

def z497 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc07f807ff00001 0x85fc07f807ff0000

def z498 : W := mkw 0x49d6000023444000 0x049d600002344400 0x0180000003800000 0x0018000000380000

def z499 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x11800e0000000000 0x011800e000000000

def z500 : W := mkw 0x009534aec431bcc8 0x4009534aec431bcc 0xf1ffffffc473fccf 0xef1ffffffc473fcc

def z501 : W := mkw 0x04280000100a0000 0x004280000100a000 0x20380000000f8002 0x020380000000f800

def z502 : W := mkw 0x04bc1626158e5554 0x804bc1626158e555 0xffbc9e667f8fffff 0xfffbc9e667f8ffff

def z503 : W := mkw 0xefffed7d7b6feaa9 0x0efffed7d7b6feaa 0xffffffffffffffff 0xffffffffffffffff

def z504 : W := mkw 0x9bd6ffa56ed00f0e 0x09bd6ffa56ed00f0 0x5fc7ff87fff00f0d 0xf5fc7ff87fff00f0

def z505 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe00410064473fccf 0x2e00410064473fcc

def z506 : W := mkw 0x0429308ad43bbcc8 0x40429308ad43bbcc 0xee7f719ffc7ffccf 0xfee7f719ffc7ffcc

def z507 : W := mkw 0x26bce67c598ecbbd 0x826bce67c598ecbb 0xffb8ee787b8f8ffe 0xfffb8ee787b8f8ff

def z508 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fb0ffff80000004 0x49fb0ffff8000000

def z509 : W := mkw 0x8ffefdffc4109cc8 0x48ffefdffc4109cc 0x9fffffff80000cc7 0xe9fffffff80000cc

def z510 : W := mkw 0x0094162605845554 0x8009416260584555 0xb0349e66000c7ff6 0x0b0349e66000c7ff

def z511 : W := mkw 0x1b40fb886ed08f8e 0x01b40fb886ed08f8 0xffc8ff987ff38fcf 0xfffc8ff987ff38fc

def z512 : W := mkw 0x3b40fb887eda8faf 0x03b40fb887eda8fa 0x7fc0ff807fff8ffd 0xf7fc0ff807fff8ff

def z513 : W := mkw 0xaffeff7f5d8edffd 0x8affeff7f5d8edff 0xffffffffff8fffff 0xfffffffffff8ffff

def z514 : W := mkw 0x5dff1b8037ff6506 0x05dff1b8037ff650 0x7fff1f807ffff00b 0xf7fff1f807ffff00

def z515 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x604071804473fccd 0xa604071804473fcc

def z516 : W := mkw 0x89d73dafc431bcc8 0x489d73dafc431bcc 0xf1cf7f9fc473fccf 0xaf1cf7f9fc473fcc

def z517 : W := mkw 0x26bdf6feddbffffd 0xc26bdf6feddbffff 0xffffffffffffffff 0xffffffffffffffff

def z518 : W := mkw 0x4dff1082b77f7440 0x44dff1082b77f744 0x6fff1187fffff00b 0xf6fff1187fffff00

def z519 : W := mkw 0x0000328044900d0c 0x00000328044900d0 0x51c0ff8047f00f0d 0xf51c0ff8047f00f0

def z520 : W := mkw 0x2628f2585c8a8fad 0x02628f2585c8a8fa 0xffb8fe787f8f8fff 0xfffb8fe787f8f8ff

def z521 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x8e7f61ff80000002 0x88e7f61ff8000000

def z522 : W := mkw 0x0094162605845554 0x8009416260584555 0x91b49e6607807007 0x691b49e660780700

def z523 : W := mkw 0x10001b8004900506 0x010001b800490050 0x10001f8000000000 0x010001f800000000

def z524 : W := mkw 0xaffecd7d100a80a1 0x0affecd7d100a80a 0xbfffffff800f80f7 0xebfffffff800f80f

def z525 : W := mkw 0x0628e05048000a08 0x00628e05048000a0 0xce38e07878000f0e 0xfce38e07878000f0

def z526 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x4ffb00007bff8000 0xd4ffb00007bff800

def z527 : W := mkw 0x0941308ae671bcc8 0x40941308ae671bcc 0xefcf719ffff3fccf 0xfefcf719ffff3fcc

def z528 : W := mkw 0x0000000200001040 0x0000000020000104 0xa0040006000070c2 0x0a0040006000070c

def z529 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1ff0ffe000000005 0xe1ff0ffe00000000

def z530 : W := mkw 0x100020806a500a0a 0x0100020806a500a0 0x4000000078700000 0x0400000007870000

def z531 : W := mkw 0x19413b8ae6f1bdce 0x419413b8ae6f1bdc 0xf1cf7f9fc7f3fccf 0xaf1cf7f9fc7f3fcc

def z532 : W := mkw 0xcfffc951336f6000 0x0cfffc951336f600 0x6fff6199fffff00b 0xf6fff6199fffff00

def z533 : W := mkw 0x0094162604801554 0x8009416260480155 0x91b49e6600000ff7 0x691b49e6600000ff

def z534 : W := mkw 0x8b40cd7500000000 0x08b40cd750000000 0x9fc0ffff80000005 0xe9fc0ffff8000000

def z535 : W := mkw 0x3f68e9d87a5a8aab 0x03f68e9d87a5a8aa 0xee78e1f8787f8ffe 0xfee78e1f8787f8ff

def z536 : W := mkw 0x8096042500000000 0x0809604250000000 0x0007000780000000 0x0000700078000000

def z537 : W := mkw 0x0001000a8021b0c0 0x40001000a8021b0c 0xe04f001fc473f0cb 0xae04f001fc473f0c

def z538 : W := mkw 0x04be000000000000 0x004be00000000000 0x003f000000000002 0x0003f00000000000

def z539 : W := mkw 0x0094162605845554 0x8009416260584555 0xa0340066078c7ffa 0x1a0340066078c7ff

def z540 : W := mkw 0x84be167705845554 0x884be16770584555 0xb1bf9e7f878c7fff 0x7b1bf9e7f878c7ff

def z541 : W := mkw 0x6ffec0503b4e4221 0x06ffec0503b4e422 0x0fb080603b8c0330 0x50fb080603b8c033

def z542 : W := mkw 0x3f68fbd07eda0f2f 0x03f68fbd07eda0f2 0x5ff0ffe07ffc0f3d 0xf5ff0ffe07ffc0f3

def z543 : W := mkw 0x0428005000000000 0x0042800500000000 0x8038007800000002 0x0803800780000000

def z544 : W := mkw 0x09d6000000000000 0x009d600000000000 0x01c7000000000001 0x001c700000000000

def z545 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe00860184473fcce 0xae00860184473fcc

def z546 : W := mkw 0x0001000000212000 0x0000100000021200 0xe04f719fc473f00f 0xae04f719fc473f00

def z547 : W := mkw 0x2629f0dadc3bbee9 0x42629f0dadc3bbee 0xee4f719ffc73fccf 0xaee4f719ffc73fcc

def z548 : W := mkw 0xcfffcd75326b2000 0x0cfffcd75326b200 0xdffffffff8738007 0xedffffffff873800

def z549 : W := mkw 0x1bd4df262fc45756 0x81bd4df262fc4575 0xbfb49e663f8c7fff 0x7bfb49e663f8c7ff

def z550 : W := mkw 0x4dff2008736fe888 0x04dff2008736fe88 0xefff60187ffffccf 0xfefff60187ffffcc

def z551 : W := mkw 0x2200e05848008aa9 0x02200e05848008aa 0xa030e078000c0ffe 0x7a030e078000c0ff

def z552 : W := mkw 0x0294f6264d845f5c 0x80294f6264d845f5 0xffb4fe667f8c7fff 0xfffb4fe667f8c7ff

def z553 : W := mkw 0x19411b82a6f13546 0x419411b82a6f1354 0x11c71f8787f07001 0x011c71f8787f0700

def z554 : W := mkw 0x8f6ac95100000000 0x08f6ac9510000000 0x1fcbff9980000005 0xe1fcbff998000000

def z555 : W := mkw 0x0094142604001440 0x0009414260400144 0xb1b49e6604007ccf 0x6b1b49e6604007cc

def z556 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000806000000ff4 0x08000806000000ff

def z557 : W := mkw 0x40010000326b2000 0x040010000326b200 0x4000000078738000 0x0400000007873800

def z558 : W := mkw 0x4dff000023656000 0x04dff00002365600 0x0fff000007f07003 0xe0fff000007f0700

def z559 : W := mkw 0xaffeed7d580a8aa9 0x0affeed7d580a8aa 0xffb8ee78780f8ffe 0xfffb8ee78780f8ff

def z560 : W := mkw 0x8ffecf7501844114 0x88ffecf750184411 0x1fb08e60038c0330 0x51fb08e60038c033

def z561 : W := mkw 0x0000000000000000 0x0000000000000000 0xa000000000000cce 0x2a000000000000cc

def z562 : W := mkw 0x0d6a000000000000 0x00d6a00000000000 0x0e4b000000000000 0x80e4b00000000000

def z563 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee386078780f80f2 0x8ee386078780f80f

def z564 : W := mkw 0x0000000000000000 0x0000000000000000 0x0180000007800009 0x7018000000780000

def z565 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x6e086018780f8ff8 0x96e086018780f8ff

def z566 : W := mkw 0x9ffefff54c900f0e 0x09ffefff54c900f0 0x9fffffff80000f07 0xe9fffffff80000f0

def z567 : W := mkw 0x8294cd7500000000 0x08294cd750000000 0x91b4ffff80000007 0x691b4ffff8000000

def z568 : W := mkw 0x0d680000324a0000 0x00d680000324a000 0x6ff800007fff800b 0xf6ff800007fff800

def z569 : W := mkw 0x8fffedfdc031a888 0x48fffedfdc031a88 0xdfffffffc0738007 0xedfffffffc073800

def z570 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1fff8e6000000003 0xe1fff8e600000000

def z571 : W := mkw 0x6fffe0587b6feaa9 0x06fffe0587b6feaa 0x6fff60187ffff00b 0xf6fff60187ffff00

def z572 : W := mkw 0x84be047701045050 0x884be04770104505 0xa03f007f800c70f2 0x0a03f007f800c70f

def z573 : W := mkw 0xaffeed7d48008aa9 0x0affeed7d48008aa 0x9fffffff80000ff7 0xe9fffffff80000ff

def z574 : W := mkw 0x1b40db002ec00706 0x01b40db002ec0070 0x1f809e003f800f0d 0x71f809e003f800f0

def z575 : W := mkw 0x2628f25a5d8edffd 0x82628f25a5d8edff 0xee38e0787f8ffffe 0xfee38e0787f8ffff

def z576 : W := mkw 0xa200ed7d48008aa9 0x0a200ed7d48008aa 0x9000ffff80000ff4 0x09000ffff80000ff

def z577 : W := mkw 0x89d61f2705845554 0x889d61f270584555 0xb1f79fe7878c7fff 0x7b1f79fe7878c7ff

def z578 : W := mkw 0x109436a66fd45f5e 0x8109436a66fd45f5 0xf1b49e667ffc7fff 0x7f1b49e667ffc7ff

def z579 : W := mkw 0x1b41fb88eef1af8e 0x41b41fb88eef1af8 0x5fcbff99fff38f0d 0xf5fcbff99fff38f0

def z580 : W := mkw 0x0628e05840008888 0x00628e0584000888 0xee38e07840038cce 0xeee38e07840038cc

def z581 : W := mkw 0x8ffefdf544100c08 0x08ffefdf544100c0 0xdfffffffc4700c0f 0xedfffffffc4700c0

def z582 : W := mkw 0x0b40db0004800504 0x00b40db000480050 0x1fc0ff8007800f0d 0xf1fc0ff8007800f0

def z583 : W := mkw 0x49d7162627e57554 0x849d7162627e5755 0xb1f79e6607fc7fff 0x7b1f79e6607fc7ff

def z584 : W := mkw 0x49d70000336f6000 0x049d70000336f600 0x61c700007ffff009 0x161c700007ffff00

def z585 : W := mkw 0x1b40fb804c900f0e 0x01b40fb804c900f0 0x1fc0ff8000000f05 0xe1fc0ff8000000f0

def z586 : W := mkw 0x0000000000000000 0x0000000000000000 0x00308060000c0330 0x500308060000c033

def z587 : W := mkw 0x009436a645945d5c 0x8009436a645945d5 0xf1f4ffe647fc7fff 0xff1f4ffe647fc7ff

def z588 : W := mkw 0x8200cd7500000000 0x08200cd750000000 0x10008e6000000000 0x010008e600000000

def z589 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1841e0607807ccf 0x2b1841e0607807cc

def z590 : W := mkw 0x4dff0000112f6000 0x04dff0000112f600 0x2fff0000000ff003 0xe2fff0000000ff00

def z591 : W := mkw 0x0000100204001440 0x0000010020400144 0x2000000004007cc8 0x02000000004007cc

def z592 : W := mkw 0x0094000001044000 0x0009400000104400 0x20340000000c7002 0x020340000000c700

def z593 : W := mkw 0x0000000000000000 0x0000000000000000 0x20300000000c000a 0x720300000000c000

def z594 : W := mkw 0x0b40e0006a400a08 0x00b40e0006a400a0 0x4fc0e0007ff00f0d 0xf4fc0e0007ff00f0

def z595 : W := mkw 0x24282008580a8aa9 0x024282008580a8aa 0x6e380000780f8ffa 0xf6e380000780f8ff

def z596 : W := mkw 0x6ffff67e7feffffd 0x86ffff67e7feffff 0xfffffe7e7fffffff 0xffffffe7e7ffffff

def z597 : W := mkw 0x0000308ac4109cc8 0x40000308ac4109cc 0xc040719fc4700ccd 0xac040719fc4700cc

def z598 : W := mkw 0x4d6b0000326b2000 0x04d6b0000326b200 0x4fcb00007ff38009 0xf4fcb00007ff3800

def z599 : W := mkw 0x2200e05848008aa9 0x02200e05848008aa 0x0000601800000000 0x0000060180000000

def z600 : W := mkw 0x0000108284101440 0x4000010828410144 0x0000118780000000 0x0000011878000000

def z601 : W := mkw 0xaffffdffdc3bbee9 0x4affffdffdc3bbee 0xfffffffffc7fffff 0xffffffffffc7ffff

def z602 : W := mkw 0x8fffddf784313440 0x48fffddf78431344 0x9fffffff84707007 0xe9fffffff8470700

def z603 : W := mkw 0x0628c05000000000 0x00628c0500000000 0x0e30806000000000 0x40e3080600000000

def z604 : W := mkw 0x1200fb804c900f0e 0x01200fb804c900f0 0x1180ff8007800f0d 0x71180ff8007800f0

def z605 : W := mkw 0x0094162404800504 0x0009416240480050 0x91b49e6607800f0f 0x791b49e6607800f0

def z606 : W := mkw 0x0001000a8021b0c0 0x40001000a8021b0c 0x200000000003f0c0 0x0200000000003f0c

def z607 : W := mkw 0x0001200ac021b8c8 0x40001200ac021b8c 0xe00f601fc003fcce 0xae00f601fc003fcc

def z608 : W := mkw 0x0095308ac535fcc8 0x40095308ac535fcc 0xe1ff719fc7fffccf 0xfe1ff719fc7fffcc

def z609 : W := mkw 0x0000120204801544 0x0000012020480154 0xb1849e0607807fcf 0x7b1849e0607807fc

def z610 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xa038e078000f8ff6 0x0a038e078000f8ff

def z611 : W := mkw 0x8ffedf7504800504 0x08ffedf750480050 0x9fffffff87800f0f 0xf9fffffff87800f0

def z612 : W := mkw 0x4dff120037ef6504 0x04dff120037ef650 0x7fff9e007fffff0f 0xf7fff9e007fffff0

def z613 : W := mkw 0x19401b8026d00506 0x019401b8026d0050 0x11c09f8007f00f0d 0x711c09f8007f00f0

def z614 : W := mkw 0xbffefffd7eda8faf 0x0bffefffd7eda8fa 0xffffffffffff8fff 0xfffffffffffff8ff

def z615 : W := mkw 0x9ffedff526d00506 0x09ffedff526d0050 0x9fffffff87f00007 0xe9fffffff87f0000

def z616 : W := mkw 0x0095162e85a5f5d4 0xc0095162e85a5f5d 0xb1bf9e7f878fffff 0x7b1bf9e7f878ffff

def z617 : W := mkw 0x0000000000000000 0x0000000000000000 0x600800004003800a 0xa600800004003800

def z618 : W := mkw 0x0094000000000000 0x0009400000000000 0x01b4000000000003 0x601b400000000000

def z619 : W := mkw 0xa4be047d100a80a1 0x0a4be047d100a80a 0xa03f007f800f80f2 0x0a03f007f800f80f

def z620 : W := mkw 0x0b40c90000000000 0x00b40c9000000000 0x1f808e0000000000 0x41f808e000000000

def z621 : W := mkw 0x1b41f98aee71beca 0x41b41f98aee71bec 0xee4f719ffc73fccf 0xaee4f719ffc73fcc

def z622 : W := mkw 0x1b40ffa66ed01f5e 0x81b40ffa66ed01f5 0xdfc0ffe67ff00ffd 0xfdfc0ffe67ff00ff

def z623 : W := mkw 0x0000120205845554 0x8000012020584555 0xa0308060078c7ffe 0x7a0308060078c7ff

def z624 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1ffbeff980000000 0xc1ffbeff98000000

def z625 : W := mkw 0x100002002ac00306 0x0100002002ac0030 0x000000003b800300 0x1000000003b80030

def z626 : W := mkw 0x3200fbd84c908faf 0x03200fbd84c908fa 0x9000fff800000ff4 0x09000fff800000ff

def z627 : W := mkw 0x8f6ac95100000000 0x08f6ac9510000000 0x0e00000000000000 0x00e0000000000000

def z628 : W := mkw 0x2628c050180a0221 0x02628c050180a022 0xae308060380c0ffe 0x7ae308060380c0ff

def z629 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee08601878038cce 0xaee08601878038cc

def z630 : W := mkw 0x84be047500000000 0x084be04750000000 0x807f71ff80000007 0xa807f71ff8000000

def z631 : W := mkw 0x9ffefff56ed00f0e 0x09ffefff56ed00f0 0x5ff0ffe07ff00f0d 0xf5ff0ffe07ff00f0

def z632 : W := mkw 0x6ffee0587b4ecaa9 0x06ffee0587b4ecaa 0xefb8e0787b8f8ffe 0xfefb8e0787b8f8ff

def z633 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x4e08e01878038f0c 0xf4e08e01878038f0

def z634 : W := mkw 0x6629e0587b6feaa9 0x06629e0587b6feaa 0xee38e0787ffffffe 0xfee38e0787ffffff

def z635 : W := mkw 0x19d41fa627d45556 0x819d41fa627d4555 0x11c41f8607f07001 0x011c41f8607f0700

def z636 : W := mkw 0x3f68fbd87eda8faf 0x03f68fbd87eda8fa 0x5fc8ff987ff38f0d 0xf5fc8ff987ff38f0

def z637 : W := mkw 0x0000042400000000 0x0000004240000000 0x90009e6600000004 0x090009e660000000

def z638 : W := mkw 0x1000128026d00506 0x01000128026d0050 0x0000000007f00000 0x00000000007f0000

def z639 : W := mkw 0x0094042601045050 0x8009404260104505 0xb1b49e66000c70f7 0x6b1b49e66000c70f

def z640 : W := mkw 0x1b41fb806ef12f0e 0x01b41fb806ef12f0 0x7fcfff807ff3ff0f 0xf7fcfff807ff3ff0

def z641 : W := mkw 0x8f6bf9dbc431bcc8 0x48f6bf9dbc431bcc 0xee4f719fc473fccf 0xaee4f719fc473fcc

def z642 : W := mkw 0x3ffcfffe7fdedfff 0x83ffcfffe7fdedff 0xfffcfffe7fffffff 0xffffcfffe7ffffff

def z643 : W := mkw 0x0000308ac4109cc8 0x40000308ac4109cc 0x804f719f80000cc7 0xa804f719f80000cc

def z644 : W := mkw 0x0000162604801554 0x8000016260480155 0xb0049e6604007fff 0x2b0049e6604007ff

def z645 : W := mkw 0x0000308ac4109cc8 0x40000308ac4109cc 0xa004719f84007ccf 0x2a004719f84007cc

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z647 : W := mkw 0x1bd4ffa46fd44f1e 0x81bd4ffa46fd44f1 0x5ff0ffe07ffc0f3d 0xf5ff0ffe07ffc0f3

def z648 : W := mkw 0xaffeed7d580a8aa9 0x0affeed7d580a8aa 0xdffffffff8038007 0xedffffffff803800

def z649 : W := mkw 0x0940090000000000 0x0094009000000000 0x11c01f8000000001 0x011c01f800000000

def z650 : W := mkw 0x0200f0804c100e08 0x00200f0804c100e0 0x4e40f1807c700f0d 0xf4e40f1807c700f0

def z651 : W := mkw 0x1200fb804c900f0e 0x01200fb804c900f0 0x5040ff8044700f0d 0xa5040ff8044700f0

def z652 : W := mkw 0x49d7000023656000 0x049d700002365600 0x4fc700007ff07009 0xf4fc700007ff0700

def z653 : W := mkw 0x2628c058180a82a1 0x02628c058180a82a 0xae388078380f83f2 0x5ae388078380f83f

def z654 : W := mkw 0x442b0000102b2000 0x0442b0000102b200 0x000b000000038000 0x0000b00000003800

def z655 : W := mkw 0x4001000023656000 0x0400100002365600 0x0000000007f07000 0x00000000007f0700

def z656 : W := mkw 0x1b41fb8aeef1bfce 0x41b41fb8aeef1bfc 0x7fc0ff807ff3ffcd 0xf7fc0ff807ff3ffc

def z657 : W := mkw 0x0000042600001050 0x8000004260000105 0x80000066000000f0 0x080000066000000f

def z658 : W := mkw 0x0000000000000000 0x0000000000000000 0x8030806000000006 0x6803080600000000

def z659 : W := mkw 0x84be047500000000 0x084be04750000000 0x91bf9e7f80000007 0x691bf9e7f8000000

def z660 : W := mkw 0x0940000022400000 0x0094000002240000 0x4e40000078700000 0x84e4000007870000

def z661 : W := mkw 0x0428000000000000 0x0042800000000000 0x0e38000000000002 0xe0e3800000000000

def z662 : W := mkw 0x49d71082a7757440 0x449d71082a775744 0x01c7118787f07001 0x001c7118787f0700

def z663 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6e7f0000787ff002 0x86e7f0000787ff00

def z664 : W := mkw 0x0940000000000000 0x0094000000000000 0x0fc0000000000001 0xe0fc000000000000

def z665 : W := mkw 0x0094042601045050 0x8009404260104505 0xa1b40066078c70fb 0x7a1b40066078c70f

def z666 : W := mkw 0x0629f0dac431bcc8 0x40629f0dac431bcc 0xee7ff1ffc473fccf 0xeee7ff1ffc473fcc

def z667 : W := mkw 0x9b40fff56ed00f0e 0x09b40fff56ed00f0 0xdfc0fffffff00f0d 0xfdfc0fffffff00f0

def z668 : W := mkw 0x000036aec4909ddc 0xc000036aec4909dd 0x9000ffff80000ff4 0x09000ffff80000ff

def z669 : W := mkw 0x2628f0d85c1a8ea9 0x02628f0d85c1a8ea 0xee78f1f87c7f8fff 0xfee78f1f87c7f8ff

def z670 : W := mkw 0x20000000180a0221 0x020000000180a022 0x00000000380c0330 0x100000000380c033

def z671 : W := mkw 0x9ffefff76fd45f5e 0x89ffefff76fd45f5 0xfffffffffffc7fff 0xffffffffffffc7ff

def z672 : W := mkw 0x24280058100a80a1 0x024280058100a80a 0xee380078780f80fa 0xfee380078780f80f

def z673 : W := mkw 0x009536aec5b5fddc 0xc009536aec5b5fdd 0xf1cf7f9fc7f3fccf 0xaf1cf7f9fc7f3fcc

def z674 : W := mkw 0x5ffecb003bce4306 0x05ffecb003bce430 0x1fb08e003b8c0300 0x51fb08e003b8c030

def z675 : W := mkw 0x9ffecf752ac00306 0x09ffecf752ac0030 0x1fb08e603b800300 0x51fb08e603b80030

def z676 : W := mkw 0x0200e00048000a08 0x00200e00048000a0 0x0000e00000000f04 0x00000e00000000f0

def z677 : W := mkw 0x0001000000212000 0x0000100000021200 0x0047000004707001 0x0004700000470700

def z678 : W := mkw 0x0001000000212000 0x0000100000021200 0x600000004473f008 0x0600000004473f00

def z679 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x11c0ff8007f00f05 0x011c0ff8007f00f0

def z680 : W := mkw 0x0000000a800090c0 0x40000000a800090c 0x8000001f800000c0 0x08000001f800000c

def z681 : W := mkw 0x0bd4cd2400000000 0x00bd4cd240000000 0x9ff4ffe600000007 0xe9ff4ffe60000000

def z682 : W := mkw 0x0b41f98ac431bcc8 0x40b41f98ac431bcc 0xffcfff9fc473fccf 0xeffcfff9fc473fcc

def z683 : W := mkw 0x5ffffb8affffffce 0x45ffffb8affffffc 0xffffff9fffffffcf 0xfffffff9fffffffc

def z684 : W := mkw 0x0094062401844114 0x8009406240184411 0x91b49e66038c0337 0x791b49e66038c033

def z685 : W := mkw 0x09d4000023444000 0x009d400002344400 0x6ff400007ffc700b 0xf6ff400007ffc700

def z686 : W := mkw 0x26bcd6761d8e5775 0x826bcd6761d8e577 0xbfb49e663f8c7fff 0x7bfb49e663f8c7ff

def z687 : W := mkw 0x8dfe0d7500000000 0x08dfe0d750000000 0x91ff1fff80000003 0x091ff1fff8000000

def z688 : W := mkw 0x2094362e5d8edffd 0x82094362e5d8edff 0xf1b49e667f8fffff 0x7f1b49e667f8ffff

def z689 : W := mkw 0x2200c05008000221 0x02200c0500800022 0x0000806000000330 0x0000080600000033

def z690 : W := mkw 0x40010000112f6000 0x040010000112f600 0x20000000000ff000 0x020000000000ff00

def z691 : W := mkw 0x2628e050580a0a29 0x02628e050580a0a2 0x4e30e060780c0f3c 0xf4e30e060780c0f3

def z692 : W := mkw 0x000136aec4b1bddc 0xc000136aec4b1bdd 0xf04fffffc473ffff 0xaf04fffffc473fff

def z693 : W := mkw 0x009516a685b57554 0xc009516a685b5755 0x11c71f8787f07001 0x011c71f8787f0700

def z694 : W := mkw 0x2629e0d8d83baaa9 0x42629e0d8d83baaa 0x4e4b6199f8738000 0x84e4b6199f873800

def z695 : W := mkw 0x4dfe162637ce5554 0x84dfe162637ce555 0xbfb49e663f8c7fff 0x7bfb49e663f8c7ff

def z696 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91f79fe780000007 0x691f79fe78000000

def z697 : W := mkw 0x7ffffbd87fffefaf 0x07ffffbd87fffefa 0xfffffff87fffffff 0xffffffff87ffffff

def z698 : W := mkw 0x44bf308ad53ffcc8 0x444bf308ad53ffcc 0xe07f719fc47ffccf 0xae07f719fc47ffcc

def z699 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x604f00004473fccb 0xa604f00004473fcc

def z700 : W := mkw 0x6ffff0daff7ffee9 0x46ffff0daff7ffee 0xeffff1ffffffffff 0xfeffff1fffffffff

def z701 : W := mkw 0x4d6b308af67bbcc8 0x44d6b308af67bbcc 0xee4f719ffc73fccf 0xaee4f719ffc73fcc

def z702 : W := mkw 0x5dff32807fff6f0e 0x05dff32807fff6f0 0x6fff00007fffff0b 0xf6fff00007fffff0

def z703 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x8047719f84707cc5 0x08047719f84707cc

def z704 : W := mkw 0x1b40f9806e500e0a 0x01b40f9806e500e0 0x4e4071807c700c0d 0xa4e4071807c700c0

def z705 : W := mkw 0x4d6b2088f27ba888 0x44d6b2088f27ba88 0x4e4b6199f8738000 0x84e4b6199f873800

def z706 : W := mkw 0x0094042401044000 0x0009404240104400 0xb1b49e66078c700f 0x7b1b49e66078c700

def z707 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x7fc0ff807ffc0ffd 0xf7fc0ff807ffc0ff

def z708 : W := mkw 0x0001208ac031b8c8 0x40001208ac031b8c 0xe04f619fc473f0cb 0xae04f619fc473f0c

def z709 : W := mkw 0x4dfe308af75edcc8 0x44dfe308af75edcc 0x8fb0719fbb8c0cc4 0x58fb0719fbb8c0cc

def z710 : W := mkw 0x1b40fb826ed01f4e 0x01b40fb826ed01f4 0xdfc0ff867ff00fcd 0xfdfc0ff867ff00fc

def z711 : W := mkw 0xcdff0d25336f6000 0x0cdff0d25336f600 0x7fff0e007ffff00b 0xf7fff0e007ffff00

def z712 : W := mkw 0x4dff0050336f6000 0x04dff0050336f600 0xefff00787ffff00b 0xfefff00787ffff00

def z713 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xbfffffff80000ccf 0xebfffffff80000cc

def z714 : W := mkw 0x84be047500000000 0x084be04750000000 0x91ffffff80000007 0xe91ffffff8000000

def z715 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fb800007ffff00a 0xf6fb800007ffff00

def z716 : W := mkw 0x8ffecd7523444000 0x08ffecd752344400 0xfffffffffffc700f 0xffffffffffffc700

def z717 : W := mkw 0x0940090000000000 0x0094009000000000 0x91cf7f9f80000007 0xa91cf7f9f8000000

def z718 : W := mkw 0xa9d62d2d580a8aa9 0x0a9d62d2d580a8aa 0x71c71f87f80f8ff9 0x171c71f87f80f8ff

def z719 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b09e66078c7ffc 0x5b1b09e66078c7ff

def z720 : W := mkw 0x8200cd7500000000 0x08200cd750000000 0x9047ffff80000005 0x09047ffff8000000

def z721 : W := mkw 0x1b40eb806ad00b0e 0x01b40eb806ad00b0 0x5fc0ef807bf00f0c 0xf5fc0ef807bf00f0

def z722 : W := mkw 0x4001328af7fffddc 0xc4001328af7fffdd 0x600000007ffffff8 0x1600000007ffffff

def z723 : W := mkw 0x1b41cb0aaae1b3c6 0x41b41cb0aaae1b3c 0xbf8f8e1fbb83f3c2 0x5bf8f8e1fbb83f3c

def z724 : W := mkw 0x8bd6cd7500000000 0x08bd6cd750000000 0x11c77f9f80000001 0x011c77f9f8000000

def z725 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee388078780f8ffa 0x5ee388078780f8ff

def z726 : W := mkw 0x1b40fb8aeed09fce 0x41b40fb8aeed09fc 0x5fc0ff807ff00fcd 0xf5fc0ff807ff00fc

def z727 : W := mkw 0x0940120026c00504 0x00940120026c0050 0x5fc01e007ff00009 0xf5fc01e007ff0000

def z728 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee308060780f8ffe 0x7ee308060780f8ff

def z729 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff80607ffff00f 0xfefff80607ffff00

def z730 : W := mkw 0x1b40cb802ad00306 0x01b40cb802ad0030 0x1fc08f803bf00300 0x51fc08f803bf0030

def z731 : W := mkw 0x1b40db802ed00706 0x01b40db802ed0070 0x1fc09f803ff00f0d 0x71fc09f803ff00f0

def z732 : W := mkw 0x1b40fb886ed08f8e 0x01b40fb886ed08f8 0x7fc0ff807ff38fcd 0xf7fc0ff807ff38fc

def z733 : W := mkw 0x26bcf67e5d8edffd 0x826bcf67e5d8edff 0x5f8c7e1e7f83f001 0x85f8c7e1e7f83f00

def z734 : W := mkw 0x0001328ac5b5fddc 0xc0001328ac5b5fdd 0x6000000047f3fcc8 0x06000000047f3fcc

def z735 : W := mkw 0x0001328ac4b1bdcc 0x40001328ac4b1bdc 0xf1ffffffc7ffffff 0xff1ffffffc7fffff

def z736 : W := mkw 0xc201cd75336f6000 0x0c201cd75336f600 0xf000fffffffff00c 0x1f000fffffffff00

def z737 : W := mkw 0x3d681bd836da85a7 0x03d681bd836da85a 0xb1f81ff807ff80f3 0x0b1f81ff807ff80f

def z738 : W := mkw 0x8bd6cd7500000000 0x08bd6cd750000000 0x9fc7ffff80000005 0xe9fc7ffff8000000

def z739 : W := mkw 0x1001328accb1bfce 0x41001328accb1bfc 0x600000004473ffc8 0x0600000004473ffc

def z740 : W := mkw 0x009526acc1b5e99c 0xc009526acc1b5e99 0x51fbeff9c3ff8330 0xd51fbeff9c3ff833

def z741 : W := mkw 0x2629d0d29c3b3661 0x42629d0d29c3b366 0x0e7791e7bc7c7331 0x50e7791e7bc7c733

def z742 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee386078780f8ffa 0x9ee386078780f8ff

def z743 : W := mkw 0x1b40cb002ac00306 0x01b40cb002ac0030 0x5f808e007ff00308 0x55f808e007ff0030

def z744 : W := mkw 0x3b40fbd06ed00f2f 0x03b40fbd06ed00f2 0x5fc0ffe07ff00f3d 0xf5fc0ffe07ff00f3

def z745 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1ff9e66078c7fff 0xfb1ff9e66078c7ff

def z746 : W := mkw 0x24280058100a80a1 0x024280058100a80a 0xee388078780f8ffe 0xfee388078780f8ff

def z747 : W := mkw 0x0000042400000000 0x0000004240000000 0x904fffff80000007 0xa904fffff8000000

def z748 : W := mkw 0x8ffecd75100a0000 0x08ffecd75100a000 0xbfffffff800f8007 0xebfffffff800f800

def z749 : W := mkw 0x0200c90000000000 0x00200c9000000000 0x904fff9f80000007 0xa904fff9f8000000

def z750 : W := mkw 0x000120084021a888 0x0000120084021a88 0xe04f719fc473fccf 0xae04f719fc473fcc

def z751 : W := mkw 0x44bf0426112f7050 0x844bf0426112f705 0x203f0006000ff002 0x0203f0006000ff00

def z752 : W := mkw 0x8bd6cd7500000000 0x08bd6cd750000000 0x91f7ffff80000007 0x691f7ffff8000000

def z753 : W := mkw 0x0001108a8431b4c0 0x40001108a8431b4c 0xa04f719f8473f0c7 0xaa04f719f8473f0c

def z754 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee3fe07ff80f8ffe 0xfee3fe07ff80f8ff

def z755 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x11cf7f9f80000001 0x811cf7f9f8000000

def z756 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee30e078780f8ffc 0x5ee30e078780f8ff

def z757 : W := mkw 0x2628c050180a0221 0x02628c050180a022 0xee388060780f8ffe 0xfee388060780f8ff

def z758 : W := mkw 0xc4bf0425112f6000 0x0c4bf0425112f600 0x203f0007800ff002 0x0203f0007800ff00

def z759 : W := mkw 0x0000000000000000 0x0000000000000000 0x91cfff9f80000007 0xe91cfff9f8000000

def z760 : W := mkw 0x1b40cb002ac00306 0x01b40cb002ac0030 0x1fc08e003ff00301 0x51fc08e003ff0030

def z761 : W := mkw 0x4dff0424336f6000 0x04dff0424336f600 0x7fff1e067ffff00b 0xf7fff1e067ffff00

def z762 : W := mkw 0x3b40fbd86ed08faf 0x03b40fbd86ed08fa 0xffc8fff87ff38fff 0xfffc8fff87ff38ff

def z763 : W := mkw 0x86becd7500000000 0x086becd750000000 0x9e3fffff80000006 0xe9e3fffff8000000

def z764 : W := mkw 0x8200cd7500000000 0x08200cd750000000 0x904bffff80000004 0x8904bffff8000000

def z765 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b08e60078c7ffe 0x7b1b08e60078c7ff

def z766 : W := mkw 0x0001208ac031b8c8 0x40001208ac031b8c 0xe04f719fc073f0c7 0xae04f719fc073f0c

def z767 : W := mkw 0x1b40fb826ed01f5e 0x81b40fb826ed01f5 0x5fc0ff807ff00ffd 0xf5fc0ff807ff00ff

def z768 : W := mkw 0xaffecd7508000221 0x0affecd750800022 0x9fffffff80000337 0xe9fffffff8000033

def z769 : W := mkw 0x19400b0022c00106 0x019400b0022c0010 0x5fc00e007ff00009 0xf5fc00e007ff0000

def z770 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff1187fffff00b 0xf6fff1187fffff00

def z771 : W := mkw 0x80000d2500000000 0x080000d250000000 0x904f7f9f80000007 0xa904f7f9f8000000

def z772 : W := mkw 0x1b40eb806ad00b0e 0x01b40eb806ad00b0 0x5fc0ef807ff00309 0xf5fc0ef807ff0030

def z773 : W := mkw 0x009416a685945554 0xc009416a68594555 0xb1b49fe7878c7fff 0x7b1b49fe7878c7ff

def z774 : W := mkw 0x6bd7e0586b65eaa9 0x06bd7e0586b65eaa 0x81c7e07807f07ff5 0x081c7e07807f07ff

def z775 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc0ff807bf00f04 0xd5fc0ff807bf00f0

def z776 : W := mkw 0x44290000336f6000 0x044290000336f600 0x6e3000007ffff008 0x56e3000007ffff00

def z777 : W := mkw 0xc4bf0475112f6000 0x0c4bf0475112f600 0x203f0060000ff002 0x0203f0060000ff00

def z778 : W := mkw 0xcdff0475336f6000 0x0cdff0475336f600 0xffff9e7ffffff00f 0xfffff9e7ffffff00

def z779 : W := mkw 0x1b40e9806a500a0a 0x01b40e9806a500a0 0x5fc0ff807ff0000d 0xf5fc0ff807ff0000

def z780 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91ffffff80000007 0xe91ffffff8000000

def z781 : W := mkw 0x0d690000326b2000 0x00d690000326b200 0x6fff00007ffff00b 0xf6fff00007ffff00

def z782 : W := mkw 0x9200ffffcc909fce 0x49200ffffcc909fc 0x9000ffff80000fc4 0x09000ffff80000fc

def z783 : W := mkw 0x8ffecd7508000200 0x08ffecd750800020 0x9fffffffb8000307 0xf9fffffffb800030

def z784 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc0ff807ff00f05 0x85fc0ff807ff00f0

def z785 : W := mkw 0x0ffec90000000000 0x00ffec9000000000 0x9fffff9f80000007 0xe9fffff9f8000000

def z786 : W := mkw 0x3200fffe4c909fff 0x83200fffe4c909ff 0x9000fffe00000ff4 0x09000fffe00000ff

def z787 : W := mkw 0x862acd7500000000 0x0862acd750000000 0x900bffff80000004 0x0900bffff8000000

def z788 : W := mkw 0x56bffb805dbf6f0e 0x056bffb805dbf6f0 0x303fff80000fff06 0x0303fff80000fff0

def z789 : W := mkw 0x8628cd7500000000 0x08628cd750000000 0x9e7fffff80000007 0xe9e7fffff8000000

def z790 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff00007ffffffb 0xf6fff00007ffffff

def z791 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fff7fff80000003 0x89fff7fff8000000

def z792 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1fff7f9f80000003 0xe1fff7f9f8000000

def z793 : W := mkw 0x8ffecd75324a0000 0x08ffecd75324a000 0xffffffffffff800f 0xfffffffffffff800

def z794 : W := mkw 0x94be36f56ed00f0e 0x094be36f56ed00f0 0xc03f007ffff00f0a 0x1c03f007ffff00f0

def z795 : W := mkw 0x8bd6cd2500000000 0x08bd6cd250000000 0x9fcfff9f80000007 0xe9fcfff9f8000000

def z796 : W := mkw 0x8ffecd7522400000 0x08ffecd752240000 0x9fffffffbb800007 0xf9fffffffbb80000

def z797 : W := mkw 0x0001328ac4b1bddc 0xc0001328ac4b1bdd 0xe04f719fc473ffff 0xae04f719fc473fff

def z798 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xce38e078780f8ff4 0xdce38e078780f8ff

def z799 : W := mkw 0x0094042400000000 0x0009404240000000 0x91cf7f9f80000007 0xa91cf7f9f8000000

def z800 : W := mkw 0xcdff0d75336f6000 0x0cdff0d75336f600 0xffff1ffffffff00b 0xfffff1ffffffff00

def z801 : W := mkw 0x4d6b0000336f6000 0x04d6b0000336f600 0x6e4f00007ffff00b 0xb6e4f00007ffff00

def z802 : W := mkw 0x1b40fb8aeed09fce 0x41b40fb8aeed09fc 0xffc8ff9ffff38fcf 0xfffc8ff9ffff38fc

def z803 : W := mkw 0xcffecd75334e4000 0x0cffecd75334e400 0xbfffffffbf8c700f 0xfbfffffffbf8c700

def z804 : W := mkw 0x0940020022c00104 0x00940020022c0010 0x5fc08e007ff00309 0xf5fc08e007ff0030

def z805 : W := mkw 0x44bf0000336f6000 0x044bf0000336f600 0x6e3f00007ffff00a 0xf6e3f00007ffff00

def z806 : W := mkw 0x0bd4cd2400000000 0x00bd4cd240000000 0x9fffffff80000007 0xe9fffffff8000000

def z807 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9ff7ffff80000005 0x49ff7ffff8000000

def z808 : W := mkw 0x3b40fb886ed08faf 0x03b40fb886ed08fa 0x5fc0ff807ff00ffd 0xf5fc0ff807ff00ff

def z809 : W := mkw 0x0dfe042400000000 0x00dfe04240000000 0x9fffffff80000007 0xe9fffffff8000000

def z810 : W := mkw 0x4d6b0000336f6000 0x04d6b0000336f600 0x6fcb00007ffff009 0xf6fcb00007ffff00

def z811 : W := mkw 0x44bf0424112f6000 0x044bf0424112f600 0xa03f0066000ff002 0x0a03f0066000ff00

def z812 : W := mkw 0x0000120204801544 0x0000012020480154 0xb1b49e66078c7fff 0x7b1b49e66078c7ff

def z813 : W := mkw 0x0094162605845554 0x8009416260584555 0x31b49e66078c7ff9 0x531b49e66078c7ff

def z814 : W := mkw 0xa62ae059580a8aa9 0x0a62ae059580a8aa 0xee3be079f80f8ffe 0xfee3be079f80f8ff

def z815 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xdfc0ffe07ff00ffd 0xfdfc0ffe07ff00ff

def z816 : W := mkw 0x8096162705845554 0x8809616270584555 0xb1b79e67878c7fff 0x7b1b79e67878c7ff

def z817 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc0ff807ff00005 0xe5fc0ff807ff0000

def z818 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc08e007ff00f09 0xf5fc08e007ff00f0

def z819 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fcf00007ff3f00b 0xa6fcf00007ff3f00

def z820 : W := mkw 0x8f6acd7500000000 0x08f6acd750000000 0x9e4fffff80000007 0xa9e4fffff8000000

def z821 : W := mkw 0x4d690000336f6000 0x04d690000336f600 0x6ff800007ffff00b 0xf6ff800007ffff00

def z822 : W := mkw 0x1b40fb8aeed09fce 0x41b40fb8aeed09fc 0xdfcfff9ffff00fcf 0xfdfcfff9ffff00fc

def z823 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6ff700007ffff009 0x56ff700007ffff00

def z824 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc0ff807ff00301 0xd5fc0ff807ff0030

def z825 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc09f807ff00f09 0x55fc09f807ff00f0

def z826 : W := mkw 0x0001328ac4b1bdcc 0x40001328ac4b1bdc 0xf1cf7f9fc7f3fccf 0xaf1cf7f9fc7f3fcc

def z827 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x7fff9e007ffff00f 0xf7fff9e007ffff00

def z828 : W := mkw 0x1b40fb886ed08f8e 0x01b40fb886ed08f8 0xffcfff9ffff38fcf 0xfffcfff9ffff38fc

def z829 : W := mkw 0x4dff0900336f6000 0x04dff0900336f600 0x7fff1f807ffff00b 0xf7fff1f807ffff00

def z830 : W := mkw 0x8ffecd7501044000 0x08ffecd750104400 0x9fffffff838c0007 0xf9fffffff838c000

def z831 : W := mkw 0x3200fbdacc909fef 0x43200fbdacc909fe 0x9000ffff80000ff4 0x09000ffff80000ff

def z832 : W := mkw 0x1b40fb826ed01f4e 0x01b40fb826ed01f4 0xfff4ffe67ffc7fff 0xffff4ffe67ffc7ff

def z833 : W := mkw 0xaffecd75100a0021 0x0affecd75100a002 0x9fffffff800c0037 0xe9fffffff800c003

def z834 : W := mkw 0x8ffecd7501044000 0x08ffecd750104400 0xbfffffff878c7fff 0xfbfffffff878c7ff

def z835 : W := mkw 0x0dfc0000334e4000 0x00dfc0000334e400 0x6ffc00007ffff00b 0xf6ffc00007ffff00

def z836 : W := mkw 0x9b42fb816ed00f0e 0x09b42fb816ed00f0 0x5fc3ff81fff00f0d 0xf5fc3ff81fff00f0

def z837 : W := mkw 0x8ffecd75100a0000 0x08ffecd75100a000 0x9fffffffb80c0007 0xf9fffffffb80c000

def z838 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9e7fffff80000006 0x89e7fffff8000000

def z839 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fbf00007ffff00a 0x56fbf00007ffff00

def z840 : W := mkw 0x1bd4eda66b545a5a 0x81bd4eda66b545a5 0xee7461e6787c70f2 0x8ee7461e6787c70f

def z841 : W := mkw 0x0094162605845554 0x8009416260584555 0x31b48e60078c7ffb 0x731b48e60078c7ff

def z842 : W := mkw 0x06bcc47400000000 0x006bcc4740000000 0x9fffffff80000007 0xe9fffffff8000000

def z843 : W := mkw 0x8f6adb5305845554 0x88f6adb530584555 0x2e4b6199878c7ff8 0x92e4b6199878c7ff

def z844 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc0ef807ff00f08 0xd5fc0ef807ff00f0

def z845 : W := mkw 0x4dff0424336f6000 0x04dff0424336f600 0x7fff8e607ffff00b 0xf7fff8e607ffff00

def z846 : W := mkw 0x0f68c95000000000 0x00f68c9500000000 0x9fffffff80000007 0xe9fffffff8000000

def z847 : W := mkw 0x5001328affffffce 0x45001328affffffc 0x600000007fffffc8 0x1600000007fffffc

def z848 : W := mkw 0x1b40db002ec00706 0x01b40db002ec0070 0x5fc09e007ff00f0d 0xf5fc09e007ff00f0

def z849 : W := mkw 0x8ffecd75100a0000 0x08ffecd75100a000 0xfffffffff80f8fff 0xffffffffff80f8ff

def z850 : W := mkw 0x2628c058180a82a1 0x02628c058180a82a 0xae388078380f8ffe 0x7ae388078380f8ff

def z851 : W := mkw 0x49410000336f6000 0x049410000336f600 0x6fcf00007ffff00b 0xf6fcf00007ffff00

def z852 : W := mkw 0xc4bf0477112f7050 0x8c4bf0477112f705 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z853 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x7fc4ff807ff07f0f 0xf7fc4ff807ff07f0

def z854 : W := mkw 0x19401b8026d00506 0x019401b8026d0050 0x5fc09f807ff00f0d 0xf5fc09f807ff00f0

def z855 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xbfffffff8400700f 0xebfffffff8400700

def z856 : W := mkw 0xe4bf047d112fe0a1 0x0e4bf047d112fe0a 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z857 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x4fff00007ffff001 0xd4fff00007ffff00

def z858 : W := mkw 0x8294cd7500000000 0x08294cd750000000 0x91ffffff80000007 0xe91ffffff8000000

def z859 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fcbff99fff00f0d 0xf5fcbff99fff00f0

def z860 : W := mkw 0xcdff0475336f6000 0x0cdff0475336f600 0xefff71fffffff00f 0xfefff71fffffff00

def z861 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff00607ffff0fb 0xfefff00607ffff0f

def z862 : W := mkw 0x8f6ac95100000000 0x08f6ac9510000000 0x9fcfff9f80000007 0xe9fcfff9f8000000

def z863 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1f79fe7878c7fff 0x7b1f79fe7878c7ff

def z864 : W := mkw 0x3b40fbdaeed09fef 0x43b40fbdaeed09fe 0xdfc0fffffff00ffd 0xfdfc0fffffff00ff

def z865 : W := mkw 0x1b40db802ed00706 0x01b40db802ed0070 0x5fc09f807ff00309 0xf5fc09f807ff0030

def z866 : W := mkw 0x0628c050100a0000 0x00628c050100a000 0xee38e078780f8ffe 0xfee38e078780f8ff

def z867 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee3ce0787c0fffff 0xfee3ce0787c0ffff

def z868 : W := mkw 0x8ffecd75110e4000 0x08ffecd75110e400 0xffffffffff8ff00f 0xfffffffffff8ff00

def z869 : W := mkw 0x0001108284313440 0x4000110828431344 0xe04f719fc473f00f 0xae04f719fc473f00

def z870 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xffffffffc003800f 0xeffffffffc003800

def z871 : W := mkw 0x0001328ac4b1bdcc 0x40001328ac4b1bdc 0x6000000047f3ffc8 0x16000000047f3ffc

def z872 : W := mkw 0x86becd7500000000 0x086becd750000000 0x91bfffff80000007 0x691bfffff8000000

def z873 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee78f1f8780f8fff 0xfee78f1f8780f8ff

def z874 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee38f1fff80f8ffe 0xfee38f1fff80f8ff

def z875 : W := mkw 0xaffecd75180a0221 0x0affecd75180a022 0xbfffffffb80c0fff 0xfbfffffffb80c0ff

def z876 : W := mkw 0x0001328ac4b1bdcc 0x40001328ac4b1bdc 0xf04fff9fc473ffcf 0xaf04fff9fc473ffc

def z877 : W := mkw 0xcffecf7533ce4114 0x8cffecf7533ce411 0x1fb08e603b8c0330 0x51fb08e603b8c033

def z878 : W := mkw 0xc9d71f2727e57554 0x8c9d71f2727e5755 0x11c71f8787f07001 0x011c71f8787f0700

def z879 : W := mkw 0x8ffffdffc431bcc8 0x48ffffdffc431bcc 0x7fb08e604473fcc8 0x47fb08e604473fcc

def z880 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xf1cfff9fc473fccf 0xef1cfff9fc473fcc

def z881 : W := mkw 0x0628e000580a0a08 0x00628e000580a0a0 0xee38e060780f8ffe 0xfee38e060780f8ff

def z882 : W := mkw 0x1b40fb8a6ed09fce 0x01b40fb8a6ed09fc 0xffccff9e7ff3ffcf 0xfffccff9e7ff3ffc

def z883 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fffffff80000ff7 0xe9fffffff80000ff

def z884 : W := mkw 0x4d6b0000336f6000 0x04d6b0000336f600 0x6e0000007ffff008 0x16e0000007ffff00

def z885 : W := mkw 0x8bd6cd7500000000 0x08bd6cd750000000 0x91cfffff80000007 0xa91cfffff8000000

def z886 : W := mkw 0x4d6b162636eb3554 0x84d6b162636eb355 0xde4b9e6678738ff4 0x8de4b9e6678738ff

def z887 : W := mkw 0xdffecf753bce4306 0x0dffecf753bce430 0x1fb08e603b8c0300 0x51fb08e603b8c030

def z888 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff001ffffff00b 0xfefff001ffffff00

def z889 : W := mkw 0x89d60d2500000000 0x089d60d250000000 0x91c77f9f80000005 0x091c77f9f8000000

def z890 : W := mkw 0x8ffecd7522400000 0x08ffecd752240000 0xdffffffff8700007 0xedffffffff870000

def z891 : W := mkw 0x194032806ed00f0e 0x0194032806ed00f0 0x5fc09e007ff00f0d 0xf5fc09e007ff00f0

def z892 : W := mkw 0x44bf0424112f6010 0x844bf0424112f601 0x203f0060000ff032 0x0203f0060000ff03

def z893 : W := mkw 0x0940090022400000 0x0094009002240000 0x5fc01f807ff00009 0xf5fc01f807ff0000

def z894 : W := mkw 0x8200cd7500000000 0x08200cd750000000 0x900fffff80000006 0x0900fffff8000000

def z895 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xefb8e0787f8f8fff 0xfefb8e0787f8f8ff

def z896 : W := mkw 0x0000120205845554 0x8000012020584555 0xb1b09e60078c7fff 0x7b1b09e60078c7ff

def z897 : W := mkw 0x4d6b0000336f6000 0x04d6b0000336f600 0x4e4b00007ff3f000 0x84e4b00007ff3f00

def z898 : W := mkw 0x19401b8026d00506 0x019401b8026d0050 0x5fc01f807ff00001 0x85fc01f807ff0000

def z899 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1bcfe7e078c7fff 0xfb1bcfe7e078c7ff

def z900 : W := mkw 0x0940000022400000 0x0094000002240000 0x5fc09e007ff0000d 0xf5fc09e007ff0000

def z901 : W := mkw 0x8ffecd7501044000 0x08ffecd750104400 0x9fffffff87807007 0xe9fffffff8780700

def z902 : W := mkw 0x40010000336f6000 0x040010000336f600 0x6e0000007ffff008 0xf6e0000007ffff00

def z903 : W := mkw 0x0b40e9006a400a08 0x00b40e9006a400a0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z904 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xdfc0ff9ffff00f0d 0xfdfc0ff9ffff00f0

def z905 : W := mkw 0x44bf042e912ff0d0 0xc44bf042e912ff0d 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z906 : W := mkw 0x1b40fb826ed01f4e 0x01b40fb826ed01f4 0x7fc0ff807ff07fcd 0xf7fc0ff807ff07fc

def z907 : W := mkw 0x4dff0424336f6010 0x84dff0424336f601 0x6fff00607ffff03b 0xf6fff00607ffff03

def z908 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee38e078780f8ff6 0x8ee38e078780f8ff

def z909 : W := mkw 0x44290000336f6000 0x044290000336f600 0x6e0800007ffff008 0x96e0800007ffff00

def z910 : W := mkw 0x19403b806ed00f0e 0x019403b806ed00f0 0x5fc01f807ff00f09 0xf5fc01f807ff00f0

def z911 : W := mkw 0x1b40fb826ed01f4e 0x01b40fb826ed01f4 0x5fc4ff867ff07f0d 0xf5fc4ff867ff07f0

def z912 : W := mkw 0x3f69e9d8fa7baaab 0x43f69e9d8fa7baaa 0x4e4b6199f8738000 0x84e4b6199f873800

def z913 : W := mkw 0xcffecd75334e4000 0x0cffecd75334e400 0xfffffffffb8f800f 0xffffffffffb8f800

def z914 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6e7f00007ffff00a 0x96e7f00007ffff00

def z915 : W := mkw 0x8f6acd7500000000 0x08f6acd750000000 0x9fcbffff80000005 0xe9fcbffff8000000

def z916 : W := mkw 0x1b40fb88eed08f8e 0x41b40fb88eed08f8 0x5fc0ff99fff00f0d 0xf5fc0ff99fff00f0

def z917 : W := mkw 0x0094162605845554 0x8009416260584555 0x31b09e60078c7ffd 0x731b09e60078c7ff

def z918 : W := mkw 0x0200f2804c900f0c 0x00200f2804c900f0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z919 : W := mkw 0x2628e0d8d81a8aa9 0x42628e0d8d81a8aa 0xee38e1f9f80f8ffe 0xfee38e1f9f80f8ff

def z920 : W := mkw 0xcffecd75334e4000 0x0cffecd75334e400 0xdffffffffffc000f 0xfdffffffffffc000

def z921 : W := mkw 0x8ffecd7522400000 0x08ffecd752240000 0x9fffffff87f00007 0xe9fffffff87f0000

def z922 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6ffb00007ffff008 0xd6ffb00007ffff00

def z923 : W := mkw 0x0200e00848008a88 0x00200e00848008a8 0xee38e078780f8ffe 0xfee38e078780f8ff

def z924 : W := mkw 0x0b40c90022400000 0x00b40c9002240000 0x5fc08e007ff00009 0xf5fc08e007ff0000

def z925 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe04f619fc473fcca 0x8e04f619fc473fcc

def z926 : W := mkw 0xcdff0d25336f6000 0x0cdff0d25336f600 0xffff9fe7fffff00f 0xfffff9fe7fffff00

def z927 : W := mkw 0x1b40fb82eed01f4e 0x41b40fb82eed01f4 0x5fc0ff87fff00f0d 0xf5fc0ff87fff00f0

def z928 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5f809e007ff00f0d 0x75f809e007ff00f0

def z929 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fffffff800c0337 0xf9fffffff800c033

def z930 : W := mkw 0xcdff0051336f6000 0x0cdff0051336f600 0x6fff0019fffff00b 0xf6fff0019fffff00

def z931 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1fcfff9f80000005 0xe1fcfff9f8000000

def z932 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fcfffff80000005 0x89fcfffff8000000

def z933 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff60187ffff00f 0xfefff60187ffff00

def z934 : W := mkw 0x0094162605845554 0x8009416260584555 0xf1f49e6647fc7fff 0xff1f49e6647fc7ff

def z935 : W := mkw 0x4dff0424336f6000 0x04dff0424336f600 0xffff9e667fffffff 0xfffff9e667ffffff

def z936 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9ffbffff80000004 0xc9ffbffff8000000

def z937 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x7ff0ff807ffc0f0f 0xf7ff0ff807ffc0f0

def z938 : W := mkw 0x009416a605945554 0x8009416a60594555 0xb1f49fe607fc7fff 0x7b1f49fe607fc7ff

def z939 : W := mkw 0x8dfe0d2500000000 0x08dfe0d250000000 0x9fff7f9f80000007 0xe9fff7f9f8000000

def z940 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x91ffffff80000007 0x091ffffff8000000

def z941 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee3cf07e780f8fff 0xfee3cf07e780f8ff

def z942 : W := mkw 0x49410000336f6000 0x049410000336f600 0x6f8000007ffff008 0x56f8000007ffff00

def z943 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xa04f719f8473fcc7 0x0a04f719f8473fcc

def z944 : W := mkw 0x1b40db8026d00506 0x01b40db8026d0050 0x5fc0ff807ff0000d 0xf5fc0ff807ff0000

def z945 : W := mkw 0x1b40fb886ed08f8e 0x01b40fb886ed08f8 0xfff8fff87fff8fff 0xffff8fff87fff8ff

def z946 : W := mkw 0xcffecd7523444000 0x0cffecd752344400 0x9fffffff83800007 0xe9fffffff8380000

def z947 : W := mkw 0x0001328ac4b1bdcc 0x40001328ac4b1bdc 0xe04f719fc7f3ffcf 0xbe04f719fc7f3ffc

def z948 : W := mkw 0x19d51fa6a7f57556 0xc19d51fa6a7f5755 0x11c71f8787f07001 0x011c71f8787f0700

def z949 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc7ff87fff00f0d 0xf5fc7ff87fff00f0

def z950 : W := mkw 0x0941000022612000 0x0094100002261200 0x6fc000007ff3f009 0xf6fc000007ff3f00

def z951 : W := mkw 0x9b40fbd16ed00f0e 0x09b40fbd16ed00f0 0x5fc0ff99fff00f0d 0xf5fc0ff99fff00f0

def z952 : W := mkw 0x1b40fbd06ed00f0e 0x01b40fbd06ed00f0 0xdfc0fff87ff00f0d 0xfdfc0fff87ff00f0

def z953 : W := mkw 0x1b40cb002ac00306 0x01b40cb002ac0030 0x5fc08e007bf00300 0xd5fc08e007bf0030

def z954 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xdffffffff800000f 0xfdffffffff800000

def z955 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff6199fffff00b 0xf6fff6199fffff00

def z956 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee78e0787c7f8fff 0xfee78e0787c7f8ff

def z957 : W := mkw 0x0094162605845554 0x8009416260584555 0x91b49e66078c7ff5 0x591b49e66078c7ff

def z958 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe1cf719fc7f3fccf 0xfe1cf719fc7f3fcc

def z959 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe04f719fc47fffff 0xbe04f719fc47ffff

def z960 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5f80ee007ff00f0c 0xf5f80ee007ff00f0

def z961 : W := mkw 0xcffecd75324a0000 0x0cffecd75324a000 0x9fffffffb8000007 0xe9fffffffb800000

def z962 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xee4f719ffc73fccf 0xfee4f719ffc73fcc

def z963 : W := mkw 0x09d5000023656000 0x009d500002365600 0x6fff00007ffff00b 0xf6fff00007ffff00

def z964 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5f80ff807ff00f0c 0x55f80ff807ff00f0

def z965 : W := mkw 0xcdff0d25336f6000 0x0cdff0d25336f600 0xffff7f9ffffff00f 0xfffff7f9ffffff00

def z966 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff00007ffff003 0x86fff00007ffff00

def z967 : W := mkw 0x0094042401044000 0x0009404240104400 0xb1b49e66078c7fff 0x7b1b49e66078c7ff

def z968 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xdfc8ff987ff00f0f 0xfdfc8ff987ff00f0

def z969 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fffffff80000f0f 0xf9fffffff80000f0

def z970 : W := mkw 0x0001308acc31bec8 0x40001308acc31bec 0xe04f719ffc73ffcf 0xbe04f719ffc73ffc

def z971 : W := mkw 0xcdff0475336f6000 0x0cdff0475336f600 0x6fff00607ffff00b 0xf6fff00607ffff00

def z972 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xbfffffff800c00f7 0xebfffffff800c00f

def z973 : W := mkw 0x24282008580a8aa9 0x024282008580a8aa 0xee388060780f8ffe 0xfee388060780f8ff

def z974 : W := mkw 0x0001000a8021b0c0 0x40001000a8021b0c 0xe04f719fc473f0cf 0xae04f719fc473f0c

def z975 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x1fc0ff803ff00f05 0x51fc0ff803ff00f0

def z976 : W := mkw 0x7f6be9d87a7baaab 0x07f6be9d87a7baaa 0x4e4b619878738000 0x84e4b61987873800

def z977 : W := mkw 0x3b40fbd86ed08faf 0x03b40fbd86ed08fa 0x5fc0ff987ff00f0d 0xf5fc0ff987ff00f0

def z978 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b49e66078c7ff7 0x0b1b49e66078c7ff

def z979 : W := mkw 0x4dff0424336f6000 0x04dff0424336f600 0xfffffffffffff00f 0xffffffffffffff00

def z980 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xdfffffffc470000f 0xedfffffffc470000

def z981 : W := mkw 0x44290000336f6000 0x044290000336f600 0x6e7f00007ffff00b 0xf6e7f00007ffff00

def z982 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fffffff8780000f 0xf9fffffff8780000

def z983 : W := mkw 0x24282058580a8aa9 0x024282058580a8aa 0xee380078780f8ffa 0xfee380078780f8ff

def z984 : W := mkw 0x19403b8066d00d0e 0x019403b8066d00d0 0x5fc07f807ff00c0d 0xf5fc07f807ff00c0

def z985 : W := mkw 0xcdff0425336f6000 0x0cdff0425336f600 0x6fff0007fffff00b 0xf6fff0007fffff00

def z986 : W := mkw 0xcffecd75110e4000 0x0cffecd75110e400 0x9fffffff800c0007 0xe9fffffff800c000

def z987 : W := mkw 0x1001328accb1bfce 0x41001328accb1bfc 0xe04f719fc473ffcf 0xae04f719fc473ffc

def z988 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff80607ffff33b 0xf6fff80607ffff33

def z989 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x7fc8ff807ff38f0f 0xf7fc8ff807ff38f0

def z990 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x6e388060780f8ffa 0xf6e388060780f8ff

def z991 : W := mkw 0x19401b8026d00506 0x019401b8026d0050 0x1fc01f803ff00001 0x51fc01f803ff0000

def z992 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x604f719fc473fcc9 0x8604f719fc473fcc

def z993 : W := mkw 0x1b40eb806ad00b0e 0x01b40eb806ad00b0 0x5fc0ff807bf00305 0xf5fc0ff807bf0030

def z994 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1f4ffe6078c7fff 0xfb1f4ffe6078c7ff

def z995 : W := mkw 0x2001328addbffffd 0xc2001328addbffff 0x600000007ffffff8 0x1600000007ffffff

def z996 : W := mkw 0x0001328ac4b1bddc 0xc0001328ac4b1bdd 0x600000004473fff8 0x0600000004473fff

def z997 : W := mkw 0x0001208ac031b8c8 0x40001208ac031b8c 0x404f619fc073f000 0x8404f619fc073f00

def z998 : W := mkw 0x1001328aeff5ffde 0xc1001328aeff5ffd 0x600000007ffffff8 0x1600000007ffffff

def z999 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc07f807ff00009 0xf5fc07f807ff0000

def z1000 : W := mkw 0x0b40f2006ec00f0c 0x00b40f2006ec00f0 0x5fc0fe007ff00f0d 0xf5fc0fe007ff00f0

def z1001 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fb400007ffff00b 0x76fb400007ffff00

def z1002 : W := mkw 0x0940328066d00d0c 0x00940328066d00d0 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z1003 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fcfff807ff00f0f 0xf5fcfff807ff00f0

def z1004 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x6e38e078780f8ff8 0xd6e38e078780f8ff

def z1005 : W := mkw 0x9ffecd752a400202 0x09ffecd752a40020 0x9fffffffb8000007 0xe9fffffffb800000

def z1006 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b4ffff878c7fff 0x7b1b4ffff878c7ff

def z1007 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe04ff19fc473ffcf 0xfe04ff19fc473ffc

def z1008 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0x6e30e060780f8ffc 0xf6e30e060780f8ff

def z1009 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b49e66038c7ff6 0x5b1b49e66038c7ff

def z1010 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff00007ffffccf 0xfefff00007ffffcc

def z1011 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x4fff00007ff3f003 0xe4fff00007ff3f00

def z1012 : W := mkw 0x2628e958580a8aa9 0x02628e958580a8aa 0xfe38fff8780f8ffe 0xffe38fff8780f8ff

def z1013 : W := mkw 0x49d7000023656000 0x049d700002365600 0x6fcf00007ff3f00b 0xf6fcf00007ff3f00

def z1014 : W := mkw 0xaffecd75180a0221 0x0affecd75180a022 0xfffffffff80f833f 0xffffffffff80f833

def z1015 : W := mkw 0x1200fb8acc909fce 0x41200fb8acc909fc 0x1000ff8000000fc4 0x01000ff8000000fc

def z1016 : W := mkw 0x49410000336f6000 0x049410000336f600 0x6e4000007ffff008 0x96e4000007ffff00

def z1017 : W := mkw 0x1b40db802ed00706 0x01b40db802ed0070 0x1fc0ff803ff00305 0xf1fc0ff803ff0030

def z1018 : W := mkw 0x8b40cd7500000000 0x08b40cd750000000 0x9fcfffff80000007 0xe9fcfffff8000000

def z1019 : W := mkw 0x86becd7500000000 0x086becd750000000 0x907fffff80000007 0xa907fffff8000000

def z1020 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xdff0ffe07ff00f0f 0xfdff0ffe07ff00f0

def z1021 : W := mkw 0x3b40fbd86ed08faf 0x03b40fbd86ed08fa 0xfff0fff87ffc0fff 0xffff0fff87ffc0ff

def z1022 : W := mkw 0x1b40eb806ad00b0e 0x01b40eb806ad00b0 0x5f808e007bf00300 0x55f808e007bf0030

def z1023 : W := mkw 0x04bd0000112f6000 0x004bd0000112f600 0x6fff00007ffff00b 0xf6fff00007ffff00

def z1024 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe04f719fc473f0c3 0x8e04f719fc473f0c

def z1025 : W := mkw 0x44bd0000336f6000 0x044bd0000336f600 0x6fbc00007ffff00b 0xf6fbc00007ffff00

def z1026 : W := mkw 0x8ffecd7501044010 0x88ffecd750104401 0x9fffffff800c0037 0xe9fffffff800c003

def z1027 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xc04f719fc473fcc5 0x8c04f719fc473fcc

def z1028 : W := mkw 0x64bf047e112ff0f1 0x864bf047e112ff0f 0xa03f007e000ff0f2 0x0a03f007e000ff0f

def z1029 : W := mkw 0x8ffecd75100a0000 0x08ffecd75100a000 0xdffffffff8038007 0xedffffffff803800

def z1030 : W := mkw 0x49d70000336f6000 0x049d70000336f600 0x6fc700007ffff009 0xf6fc700007ffff00

def z1031 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xae38e078380f8ff6 0x5ae38e078380f8ff

def z1032 : W := mkw 0x0dff000022612000 0x00dff00002261200 0x6fff00007ff3f00b 0xf6fff00007ff3f00

def z1033 : W := mkw 0x0b40f98066500c08 0x00b40f98066500c0 0x5fc0ff807ff00c0d 0xf5fc0ff807ff00c0

def z1034 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe07f71ffc47ffcff 0xae07f71ffc47ffcf

def z1035 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xffb8fe78780f8fff 0xfffb8fe78780f8ff

def z1036 : W := mkw 0x2200e008580a8aa9 0x02200e008580a8aa 0xee30e060780f8ffe 0xfee30e060780f8ff

def z1037 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0xefff10067ffff00f 0xfefff10067ffff00

def z1038 : W := mkw 0x1b40fb886ed08f8e 0x01b40fb886ed08f8 0x5fc8ff987ff38f0d 0xf5fc8ff987ff38f0

def z1039 : W := mkw 0x8dfe0d7500000000 0x08dfe0d750000000 0x91ff7fff80000007 0xa91ff7fff8000000

def z1040 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fcf00007ffff009 0x96fcf00007ffff00

def z1041 : W := mkw 0x0001308044312c08 0x00001308044312c0 0xe04f719fc473fc0f 0xae04f719fc473fc0

def z1042 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1b48e66078c7ffa 0x5b1b48e66078c7ff

def z1043 : W := mkw 0x1b40eb006ac00b0e 0x01b40eb006ac00b0 0x5fc0ee007ff00f0d 0xf5fc0ee007ff00f0

def z1044 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee7fe078780f8fff 0xfee7fe078780f8ff

def z1045 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x604f719fc473f00b 0xa604f719fc473f00

def z1046 : W := mkw 0x49d50000336f6000 0x049d50000336f600 0x6ff400007ffff00b 0xf6ff400007ffff00

def z1047 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0x404f719fc473fc0d 0xa404f719fc473fc0

def z1048 : W := mkw 0x00012088c031a888 0x400012088c031a88 0xe04f719fc473f00f 0xae04f719fc473f00

def z1049 : W := mkw 0x1b40fb8aeed09fce 0x41b40fb8aeed09fc 0xffc4ff9ffff07fcf 0xfffc4ff9ffff07fc

def z1050 : W := mkw 0x2200f6fecc909ffd 0xc2200f6fecc909ff 0x9000ffff80000ff4 0x09000ffff80000ff

def z1051 : W := mkw 0x0001208ac031b8c8 0x40001208ac031b8c 0xe04f619fc073fcce 0xae04f619fc073fcc

def z1052 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fcf7f9f80000007 0xa9fcf7f9f8000000

def z1053 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff80007fffff0f 0xf6fff80007fffff0

def z1054 : W := mkw 0x8b42cd7500000000 0x08b42cd750000000 0x9043ffff80000004 0x09043ffff8000000

def z1055 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xffc0ff807ff00fcf 0xfffc0ff807ff00fc

def z1056 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x1fffffff80000001 0xc1fffffff8000000

def z1057 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0xdfc4ff867ff00f0f 0xfdfc4ff867ff00f0

def z1058 : W := mkw 0x0094162605845554 0x8009416260584555 0xb1bf9e7f878c7fff 0x7b1bf9e7f878c7ff

def z1059 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0xbfffffff800c000f 0xfbfffffff800c000

def z1060 : W := mkw 0x1200ffaecc909fde 0xc1200ffaecc909fd 0x9000ffff80000ff4 0x09000ffff80000ff

def z1061 : W := mkw 0xaffecd75180a0221 0x0affecd75180a022 0x9fffffffb8000007 0xe9fffffffb800000

def z1062 : W := mkw 0x6dff0050336f6021 0x06dff0050336f602 0x6fff00607ffff03b 0xf6fff00607ffff03

def z1063 : W := mkw 0x1b40db802ed00706 0x01b40db802ed0070 0x1f808e003ff00300 0x51f808e003ff0030

def z1064 : W := mkw 0x8ffecd7500000000 0x08ffecd750000000 0x9fbfffff80000006 0x49fbfffff8000000

def z1065 : W := mkw 0x1b40eb806ad00b0e 0x01b40eb806ad00b0 0x5fc06f807bf00000 0x85fc06f807bf0000

def z1066 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc07f807ff00c0d 0xa5fc07f807ff00c0

def z1067 : W := mkw 0x1200f2806ed00f0e 0x01200f2806ed00f0 0x5f80fe007ff00f0d 0xf5f80fe007ff00f0

def z1068 : W := mkw 0x4d6b0000336f6000 0x04d6b0000336f600 0x6e7b00007ffff00a 0xf6e7b00007ffff00

def z1069 : W := mkw 0x0094062601845154 0x8009406260184515 0xb1b48e66038c7ffe 0x7b1b48e66038c7ff

def z1070 : W := mkw 0x3628e9d8581a8aab 0x03628e9d8581a8aa 0xee38e1f8780f8ffe 0xfee38e1f8780f8ff

def z1071 : W := mkw 0x2001308acc31bee9 0x42001308acc31bee 0xe04f719fc473ffff 0xae04f719fc473fff

def z1072 : W := mkw 0x1b40db802ed00706 0x01b40db802ed0070 0x1fc01f803ff00001 0x01fc01f803ff0000

def z1073 : W := mkw 0x49d716a6a7f57554 0xc49d716a6a7f5755 0x11c71f8787f07001 0x011c71f8787f0700

def z1074 : W := mkw 0x4dff0424336f6000 0x04dff0424336f600 0xefff00667ffff00b 0xfefff00667ffff00

def z1075 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe07f719fc47ffccf 0xfe07f719fc47ffcc

def z1076 : W := mkw 0x0001100204213440 0x0000110020421344 0xe04f719fc473fccf 0xae04f719fc473fcc

def z1077 : W := mkw 0x24bd047e912ff0f1 0xc24bd047e912ff0f 0xa03f007f800ff0f2 0x0a03f007f800ff0f

def z1078 : W := mkw 0x0b40db0026c00504 0x00b40db0026c0050 0x5fc0ff807ff00f0d 0xf5fc0ff807ff00f0

def z1079 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5fc07f807ff00f09 0x95fc07f807ff00f0

def z1080 : W := mkw 0x0094062401844114 0x8009406240184411 0xb1b48e60078c7fff 0x7b1b48e60078c7ff

def z1081 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe04f719fc073fcc6 0x8e04f719fc073fcc

def z1082 : W := mkw 0x2628e058580a8aa9 0x02628e058580a8aa 0xee7be1f9f80f8ffe 0xfee7be1f9f80f8ff

def z1083 : W := mkw 0x4d6b0000326b2000 0x04d6b0000326b200 0x6fcf00007ff3f00b 0xf6fcf00007ff3f00

def z1084 : W := mkw 0xa628e959580a8aa9 0x0a628e959580a8aa 0xee38e1f9f80f8ffe 0xfee38e1f9f80f8ff

def z1085 : W := mkw 0xeffecd753b4e4221 0x0effecd753b4e422 0x1fb08e603b8c0330 0x51fb08e603b8c033

def z1086 : W := mkw 0x1b40fb806ed00f0e 0x01b40fb806ed00f0 0x5ff0ffe07ffc0f3d 0xf5ff0ffe07ffc0f3

def z1087 : W := mkw 0xcdff0901336f6000 0x0cdff0901336f600 0x6fff0181fffff00b 0xf6fff0181fffff00

def z1088 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe04ff1ffc473ffff 0xae04ff1ffc473fff

def z1089 : W := mkw 0x04282008500a8888 0x004282008500a888 0xee38e078780f8ffe 0xfee38e078780f8ff

def z1090 : W := mkw 0x8ffecd7501044000 0x08ffecd750104400 0xbfffffff800c7007 0xebfffffff800c700

def z1091 : W := mkw 0x8f6acd7500000000 0x08f6acd750000000 0x1e4b7f9f80000000 0x81e4b7f9f8000000

def z1092 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xc04f719fc473f007 0xac04f719fc473f00

def z1093 : W := mkw 0x0094162605845554 0x8009416260584555 0xffb49e667f8c7fff 0xfffb49e667f8c7ff

def z1094 : W := mkw 0x1001328ae6f1bdce 0x41001328ae6f1bdc 0x6000000047f3fcc8 0x06000000047f3fcc

def z1095 : W := mkw 0x1b40fb826ed01f4e 0x01b40fb826ed01f4 0xffcfff9ffff07fcf 0xfffcfff9ffff07fc

def z1096 : W := mkw 0xc4bf047f912ff0c0 0x4c4bf047f912ff0c 0xa03f007f800ff0c2 0x0a03f007f800ff0c

def z1097 : W := mkw 0x59d71fa627f57556 0x859d71fa627f5755 0x11c71f8607f07001 0x011c71f8607f0700

def z1098 : W := mkw 0x3001328afefbbfef 0x43001328afefbbfe 0x600000007ffffff8 0x1600000007ffffff

def z1099 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x4fcf00007ff3f009 0xf4fcf00007ff3f00

def z1100 : W := mkw 0x0001308ac431bcc8 0x40001308ac431bcc 0xe07ff1ffc473fccf 0xee07ff1ffc473fcc

def z1101 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6ff000007ffff009 0xf6ff000007ffff00

def z1102 : W := mkw 0xef6be9597a6baaa9 0x0ef6be9597a6baaa 0x4e4b6199f8738000 0x84e4b6199f873800

def z1103 : W := mkw 0x0094162605845554 0x8009416260584555 0xf1bc9e66478fffff 0xff1bc9e66478ffff

def z1104 : W := mkw 0x0094120005844504 0x0009412000584450 0xb1b49e60078c7fff 0x7b1b49e60078c7ff

def z1105 : W := mkw 0xeffecd753b4e4221 0x0effecd753b4e422 0x9fffffffbb8c0337 0xf9fffffffbb8c033

def z1106 : W := mkw 0x2628e0d8581a8aa9 0x02628e0d8581a8aa 0xee78e1f8787f8ffe 0xfee78e1f8787f8ff

def z1107 : W := mkw 0x1b40cb002ac00306 0x01b40cb002ac0030 0x5fc0ff807ff0030d 0xf5fc0ff807ff0030

def z1108 : W := mkw 0x8296cd7500000000 0x08296cd750000000 0x9007ffff80000004 0x09007ffff8000000

def z1109 : W := mkw 0x4dff0000336f6000 0x04dff0000336f600 0x6fff71807ffff00f 0xf6fff71807ffff00

def z1110 : W := mkw 0x1b40fb886ed08f8e 0x01b40fb886ed08f8 0xdfc0ff987ff00fcd 0xfdfc0ff987ff00fc

def z1111 : W := mkw 0x8f6acd7500000000 0x08f6acd750000000 0x9e7bffff80000006 0xe9e7bffff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(1,[z0,z1,z2,z3,z4,z5]),(0,[z0,z6,z1,z2,z3,z4,z5]),(0,[z7,z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z9,z5]),(0,[z0,z1,z10,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z11]),(0,[z0,z1,z2,z3,z12,z4,z5]),(0,[z0,z1,z2,z13,z3,z14,z5])],[(0,[z0,z1,z15,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z16,z4,z5])],[(0,[z0,z1,z17,z18,z3,z4,z5]),(0,[z0,z19,z1,z3,z20,z4,z5])],[(1,[z0,z1,z21,z3,z4,z5]),(0,[z0,z1,z2,z22,z3,z4,z5]),(0,[z0,z1,z2,z4,z23,z5,z24])],[(0,[z0,z1,z2,z3,z25,z4,z5]),(0,[z0,z1,z26,z2,z3,z20,z5])],[(0,[z0,z1,z2,z27,z3,z4,z5]),(0,[z0,z1,z2,z28,z3,z4,z5]),(0,[z29,z0,z1,z2,z3,z4,z5]),(0,[z0,z30,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z31,z5]),(0,[z0,z1,z32,z2,z3,z20,z5])],[(0,[z0,z1,z2,z3,z4,z5,z33]),(1,[z0,z1,z34,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z35,z4,z5,z24]),(0,[z36,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z37,z5]),(0,[z0,z1,z2,z3,z38,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z39]),(1,[z0,z1,z2,z3,z40,z41])],[(0,[z0,z1,z2,z3,z42,z4,z5]),(0,[z7,z0,z1,z2,z3,z43,z5]),(0,[z44,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z45,z4,z5]),(0,[z0,z1,z2,z46,z3,z4,z5])],[(0,[z0,z1,z2,z47,z3,z4,z5]),(0,[z0,z1,z2,z3,z48,z4,z5]),(0,[z0,z1,z2,z3,z4,z49,z5])],[(0,[z0,z50,z1,z2,z3,z51,z5]),(1,[z0,z1,z52,z3,z4,z5])],[(0,[z0,z1,z2,z3,z53,z4,z5]),(0,[z0,z1,z2,z13,z14,z4,z5]),(0,[z0,z1,z2,z3,z4,z54,z5])],[(1,[z0,z55,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z56,z5]),(0,[z57,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z58,z5]),(0,[z59,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z60,z4,z5]),(0,[z0,z1,z61,z2,z3,z4,z5]),(0,[z0,z62,z2,z63,z3,z4,z5]),(1,[z0,z1,z64,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z65])],[(0,[z0,z1,z2,z3,z4,z5,z66]),(0,[z0,z1,z67,z2,z3,z4,z5]),(0,[z0,z68,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z69,z4,z5]),(0,[z36,z0,z1,z3,z20,z4,z5]),(0,[z0,z1,z70,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z40,z4,z5])],[(0,[z0,z1,z2,z3,z4,z71,z5]),(0,[z0,z1,z72,z2,z3,z4,z5]),(0,[z0,z1,z73,z2,z74,z4,z5]),(0,[z0,z1,z75,z2,z3,z4,z24]),(0,[z0,z1,z2,z76,z4,z23,z5]),(0,[z0,z1,z77,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z4,z41])],[(0,[z0,z1,z18,z3,z4,z5,z78]),(0,[z79,z0,z1,z2,z3,z4,z5]),(0,[z0,z80,z2,z3,z4,z81,z5]),(0,[z82,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z83]),(0,[z0,z84,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z85,z5])],[(0,[z0,z1,z2,z3,z86,z4,z5])],[(0,[z87,z0,z1,z2,z3,z88,z5])],[(0,[z0,z1,z2,z3,z4,z5,z89]),(0,[z0,z1,z90,z3,z74,z4,z5]),(0,[z0,z1,z91,z2,z3,z4,z5]),(0,[z0,z92,z1,z2,z3,z4,z5])],[(0,[z44,z1,z2,z3,z4,z93,z5]),(0,[z0,z1,z2,z3,z4,z94,z95]),(0,[z0,z1,z2,z96,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z97]),(0,[z0,z1,z2,z3,z4,z98,z5])],[(0,[z0,z55,z1,z99,z2,z3,z4]),(0,[z0,z100,z1,z2,z3,z4,z5]),(0,[z0,z1,z101,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z91,z3,z4,z5]),(0,[z102,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z103,z3,z4,z5]),(0,[z0,z1,z2,z3,z104,z4,z5]),(0,[z0,z1,z2,z3,z4,z41,z23])],[(0,[z105,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z106,z4,z5]),(0,[z0,z1,z107,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z108,z4,z5]),(0,[z0,z1,z109,z2,z3,z4,z5]),(0,[z110,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z81,z5]),(0,[z111,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z112,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z113,z5]),(0,[z0,z2,z3,z4,z114,z5,z94])],[(0,[z115,z1,z2,z90,z3,z4,z5]),(0,[z116,z0,z1,z26,z2,z3,z5]),(0,[z7,z0,z117,z2,z3,z4,z5]),(0,[z0,z1,z2,z118,z3,z4,z5]),(0,[z0,z1,z2,z3,z119,z4,z5]),(0,[z0,z1,z2,z120,z3,z4,z5]),(0,[z0,z1,z32,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z121,z5]),(0,[z122,z0,z1,z2,z3,z4,z5]),(0,[z87,z0,z2,z3,z86,z4,z5]),(0,[z0,z1,z2,z3,z4,z123,z5])],[(0,[z0,z1,z26,z18,z3,z4,z5]),(0,[z0,z1,z2,z3,z124,z4,z5]),(0,[z0,z1,z125,z2,z3,z4,z5])],[(0,[z126,z0,z1,z2,z3,z4,z5]),(0,[z127,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z125,z2,z3,z4,z41])]],
   [[(0,[z0,z1,z128,z2,z3,z4,z5]),(0,[z0,z1,z129,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z130,z5]),(0,[z0,z1,z131,z2,z3,z4,z5])],[(0,[z132,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z133,z2,z3,z4,z5]),(0,[z0,z1,z21,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z134,z4,z5]),(0,[z87,z0,z1,z2,z63,z4,z5]),(0,[z0,z1,z2,z135,z3,z4,z5])],[(0,[z87,z0,z62,z2,z3,z4,z5]),(0,[z87,z0,z1,z136,z2,z4,z5]),(0,[z0,z1,z2,z137,z3,z4,z5])],[(0,[z0,z1,z138,z2,z3,z4,z5]),(0,[z139,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z32,z3,z20,z4,z5])],[(0,[z0,z1,z140,z2,z3,z4,z5]),(0,[z0,z62,z1,z2,z14,z4,z5]),(1,[z0,z50,z2,z3,z4,z94]),(0,[z0,z1,z2,z3,z4,z141,z5])],[(0,[z1,z99,z2,z3,z142,z4,z5]),(0,[z0,z1,z143,z2,z3,z4,z5]),(0,[z144,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z145,z4,z5]),(0,[z0,z1,z2,z3,z4,z146,z5]),(0,[z147,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z148,z2,z3,z4,z78])],[(0,[z149,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z43,z4,z5]),(0,[z150,z0,z80,z2,z3,z4,z5]),(0,[z0,z151,z1,z2,z3,z4,z5]),(0,[z0,z1,z148,z2,z3,z4,z152]),(1,[z0,z1,z3,z4,z5,z153])]],
   [[(0,[z0,z1,z154,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z155,z5])],[(0,[z0,z1,z2,z3,z4,z156,z5]),(0,[z0,z1,z157,z2,z3,z4,z5])],[(0,[z0,z158,z1,z99,z2,z3,z4]),(0,[z159,z1,z2,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z160,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z161]),(0,[z87,z0,z1,z2,z3,z4,z162]),(0,[z0,z1,z2,z3,z163,z4,z5]),(0,[z0,z1,z64,z3,z4,z81,z5]),(0,[z0,z1,z164,z2,z3,z4,z5]),(0,[z0,z1,z17,z165,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z166,z5]),(0,[z0,z1,z167,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z152,z5]),(1,[z0,z1,z2,z13,z14,z5])],[(1,[z168,z1,z2,z35,z4,z5]),(0,[z0,z1,z2,z3,z51,z4,z5]),(0,[z0,z1,z2,z169,z3,z4,z5])],[(0,[z0,z1,z2,z3,z170,z4,z5])],[(0,[z0,z1,z90,z3,z4,z5,z78]),(0,[z0,z1,z2,z3,z171,z4,z5]),(0,[z0,z172,z1,z2,z3,z4,z5]),(0,[z0,z1,z173,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z14,z174,z5]),(0,[z0,z1,z175,z2,z3,z4,z5])],[(0,[z176,z0,z1,z2,z3,z4,z5]),(0,[z177,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z178,z4,z5]),(0,[z179,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z180,z3,z4,z5]),(1,[z0,z1,z125,z2,z3,z95])]],
   [[(0,[z0,z1,z18,z181,z3,z4,z5]),(0,[z168,z0,z1,z2,z35,z4,z5]),(0,[z0,z1,z2,z3,z182,z4,z5]),(0,[z7,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z2,z3,z4,z183,z5]),(0,[z0,z1,z2,z3,z4,z184,z5])],[(0,[z0,z1,z2,z3,z4,z5,z185]),(0,[z0,z186,z1,z2,z3,z4,z5])],[(0,[z187,z0,z1,z2,z3,z4,z5]),(0,[z116,z0,z1,z2,z3,z4,z5]),(0,[z188,z1,z2,z3,z4,z189,z5]),(0,[z150,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z190,z4,z5])],[(1,[z0,z1,z8,z3,z4,z5]),(0,[z0,z1,z181,z3,z74,z4,z5]),(0,[z0,z1,z2,z3,z4,z191,z5]),(0,[z0,z1,z2,z3,z4,z192,z5]),(0,[z0,z1,z2,z3,z193,z4,z5]),(0,[z0,z1,z2,z76,z3,z4,z5]),(0,[z0,z1,z2,z76,z3,z4,z24])],[(0,[z0,z194,z1,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z119,z5]),(0,[z0,z1,z2,z3,z4,z5,z195]),(0,[z0,z1,z17,z2,z165,z4,z5]),(0,[z0,z1,z2,z3,z4,z196,z5])],[(0,[z197,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z136,z2,z3,z40,z5])],[(0,[z0,z1,z2,z198,z3,z4,z5]),(0,[z0,z1,z2,z199,z3,z4,z5]),(0,[z0,z200,z1,z2,z3,z4,z5]),(0,[z201,z0,z2,z3,z4,z114,z5]),(0,[z202,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z203])],[(0,[z0,z1,z2,z76,z142,z4,z5]),(0,[z0,z1,z2,z3,z204,z4,z5]),(0,[z0,z1,z2,z3,z4,z205,z5])]],
   [[(0,[z0,z206,z1,z2,z3,z4,z5]),(0,[z0,z1,z18,z3,z20,z4,z5]),(0,[z0,z1,z207,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z41,z94]),(0,[z208,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z73,z2,z3,z4,z5]),(0,[z0,z1,z2,z209,z3,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z210,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z211,z4,z212]),(0,[z0,z1,z2,z3,z4,z5,z213])],[(0,[z0,z1,z214,z2,z3,z4,z5]),(1,[z115,z215,z2,z3,z4,z5]),(0,[z0,z1,z2,z216,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z217]),(0,[z0,z1,z2,z3,z4,z218,z5]),(0,[z0,z1,z219,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z220,z4,z5]),(0,[z0,z1,z221,z2,z3,z4,z5])],[(0,[z222,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z43,z5]),(0,[z150,z0,z1,z2,z3,z81,z5]),(0,[z0,z1,z223,z2,z3,z4,z5]),(0,[z0,z1,z136,z2,z3,z196,z5])],[(0,[z0,z215,z1,z2,z3,z4,z5]),(1,[z0,z1,z224,z2,z3,z5]),(0,[z0,z1,z225,z18,z3,z4,z5]),(0,[z210,z0,z1,z2,z142,z4,z5]),(0,[z0,z1,z2,z3,z4,z189,z5]),(0,[z0,z1,z2,z3,z211,z4,z226]),(0,[z0,z1,z2,z3,z4,z227,z5])],[(0,[z0,z1,z2,z3,z189,z5,z95]),(0,[z0,z1,z228,z2,z3,z4,z5]),(0,[z0,z19,z1,z2,z3,z4,z5]),(0,[z0,z1,z229,z2,z3,z4,z5])],[(0,[z105,z0,z1,z90,z3,z4,z5]),(0,[z0,z1,z2,z35,z3,z4,z5]),(0,[z230,z0,z1,z2,z3,z4,z5]),(0,[z0,z80,z1,z2,z3,z4,z113]),(0,[z0,z1,z2,z3,z231,z4,z5])]],
   [[(0,[z188,z0,z1,z2,z3,z189,z5]),(0,[z87,z102,z1,z2,z3,z4,z5]),(0,[z232,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z233,z5])],[(0,[z7,z1,z2,z3,z211,z4,z5]),(0,[z0,z1,z17,z2,z3,z4,z5]),(0,[z234,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z235,z3,z4,z5]),(1,[z159,z1,z90,z3,z4,z5]),(0,[z7,z0,z1,z148,z2,z3,z4])],[(0,[z236,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z226]),(0,[z0,z237,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z238,z4,z5]),(0,[z239,z0,z1,z2,z3,z4,z5])],[(0,[z115,z0,z215,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z240]),(0,[z7,z0,z1,z2,z241,z4,z5]),(0,[z0,z1,z242,z2,z3,z4,z5])],[(0,[z243,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z1,z2,z3,z4,z93]),(0,[z44,z0,z50,z1,z2,z3,z4]),(0,[z36,z172,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z244,z5]),(0,[z0,z1,z2,z3,z4,z24,z95])],[(0,[z245,z0,z1,z2,z3,z4,z5]),(0,[z246,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z247,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z130,z5]),(0,[z248,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z249,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z250,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z251])]],
   [[(0,[z0,z1,z2,z3,z4,z252,z5]),(0,[z0,z1,z2,z3,z253,z4,z5]),(0,[z0,z1,z17,z3,z20,z4,z5]),(0,[z0,z1,z26,z2,z3,z4,z254]),(0,[z0,z1,z2,z3,z4,z255,z5]),(1,[z0,z1,z2,z3,z256,z5])],[(0,[z7,z1,z2,z3,z4,z5,z257]),(0,[z0,z1,z258,z3,z74,z4,z5]),(0,[z0,z1,z2,z3,z259,z4,z5]),(0,[z0,z1,z2,z260,z3,z4,z5])],[(0,[z0,z1,z2,z3,z261,z4,z5]),(0,[z0,z1,z2,z262,z3,z4,z5]),(0,[z0,z1,z2,z3,z152,z5,z263]),(0,[z264,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z99,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z265,z4,z5]),(0,[z266,z0,z1,z2,z3,z4,z5]),(0,[z44,z0,z1,z2,z3,z4,z5]),(0,[z44,z0,z1,z2,z3,z4,z24]),(0,[z36,z0,z1,z258,z3,z4,z5]),(0,[z0,z1,z267,z2,z3,z4,z5]),(0,[z0,z80,z1,z2,z3,z174,z5]),(0,[z0,z1,z165,z3,z74,z4,z5]),(0,[z0,z1,z75,z2,z76,z4,z5])],[(0,[z0,z1,z268,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z269,z5]),(0,[z270,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z95])],[(0,[z271,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z272,z5]),(0,[z44,z0,z1,z2,z3,z4,z257]),(0,[z0,z1,z2,z3,z273,z23,z5])],[(0,[z274,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z275,z4,z5])],[(0,[z0,z1,z2,z3,z276,z4,z5]),(0,[z0,z1,z277,z2,z3,z4,z5]),(1,[z0,z117,z2,z3,z4,z5]),(0,[z0,z1,z26,z3,z4,z152,z5]),(0,[z0,z1,z278,z2,z3,z4,z5])]],
   [[(1,[z0,z1,z279,z2,z3,z4]),(0,[z0,z1,z280,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z152,z5,z78]),(0,[z0,z1,z2,z3,z4,z281,z5])],[(0,[z0,z1,z282,z2,z3,z4,z5])],[(0,[z0,z1,z283,z2,z3,z4,z5]),(0,[z284,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z285,z5])],[(0,[z0,z19,z181,z2,z3,z4,z5]),(0,[z0,z80,z1,z2,z3,z4,z11]),(0,[z0,z1,z286,z2,z3,z4,z5]),(0,[z287,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z88,z5]),(0,[z0,z1,z288,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z289]),(0,[z0,z1,z136,z2,z3,z5,z95])],[(0,[z0,z1,z290,z2,z3,z4,z5]),(0,[z291,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z292,z3,z4,z5])],[(0,[z293,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z294,z3,z4,z5])],[(0,[z201,z0,z1,z2,z3,z4,z94])]],
   [[(0,[z0,z1,z295,z2,z3,z4,z5]),(0,[z296,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z297,z4,z5]),(0,[z0,z1,z13,z3,z298,z4,z5]),(0,[z0,z1,z2,z3,z299,z4,z5])],[(0,[z0,z1,z300,z2,z3,z4,z5]),(0,[z0,z1,z301,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z302])],[(0,[z0,z1,z303,z2,z3,z4,z5]),(0,[z0,z1,z2,z304,z3,z4,z5]),(0,[z0,z1,z305,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z306,z5]),(0,[z0,z1,z3,z20,z4,z152,z5]),(0,[z0,z1,z148,z225,z3,z4,z5]),(0,[z0,z1,z307,z2,z3,z4,z5])],[(0,[z308,z0,z1,z2,z3,z4,z5]),(0,[z1,z18,z2,z90,z3,z4,z5]),(0,[z0,z309,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z310,z4,z5]),(0,[z0,z1,z286,z2,z4,z81,z5]),(0,[z0,z50,z1,z2,z3,z4,z5]),(0,[z0,z311,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z312,z4,z5])],[(0,[z0,z1,z303,z2,z90,z3,z4]),(0,[z0,z313,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z314,z3,z4,z5]),(0,[z0,z1,z2,z3,z241,z4,z5]),(0,[z0,z1,z2,z3,z4,z315,z5]),(0,[z0,z1,z2,z3,z4,z316,z5])],[(0,[z0,z1,z2,z3,z4,z317,z5]),(0,[z318,z0,z1,z2,z3,z4,z5]),(0,[z0,z319,z1,z2,z3,z4,z5]),(0,[z0,z1,z17,z2,z74,z4,z5]),(0,[z0,z1,z26,z2,z3,z4,z5]),(0,[z0,z1,z2,z320,z3,z4,z5])],[(0,[z0,z1,z2,z3,z14,z4,z5])],[(0,[z0,z1,z2,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z321,z5]),(0,[z87,z0,z1,z2,z14,z4,z5]),(0,[z0,z1,z2,z322,z3,z4,z5]),(0,[z323,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z115,z0,z99,z2,z3,z4,z5]),(0,[z324,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z325,z4,z5]),(0,[z1,z2,z3,z4,z5,z326,z95]),(0,[z0,z1,z2,z3,z4,z5,z153])],[(0,[z0,z1,z327,z2,z3,z4,z5]),(0,[z0,z1,z2,z328,z3,z4,z5]),(0,[z0,z1,z329,z2,z3,z4,z5])],[(0,[z0,z1,z2,z330,z3,z4,z5]),(1,[z0,z1,z2,z250,z4,z5]),(0,[z0,z1,z331,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z332])],[(0,[z333,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z334,z3,z4,z5]),(0,[z0,z335,z1,z2,z3,z4,z5]),(0,[z0,z336,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z337]),(0,[z0,z1,z338,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z211,z4,z5]),(0,[z0,z1,z2,z3,z40,z211,z5]),(0,[z339,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z340,z4,z5]),(0,[z7,z188,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z341,z5]),(0,[z342,z0,z1,z2,z3,z4,z5]),(0,[z87,z0,z1,z343,z3,z4,z5]),(0,[z0,z1,z32,z2,z3,z40,z5]),(0,[z0,z1,z136,z2,z13,z4,z5]),(0,[z0,z1,z344,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z345,z5]),(0,[z0,z1,z17,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z346,z5]),(0,[z0,z1,z2,z3,z4,z5,z347])]],
   [[(0,[z0,z62,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z14,z81,z5]),(0,[z0,z1,z125,z2,z3,z40,z5])],[(0,[z149,z0,z1,z235,z3,z4,z5]),(0,[z0,z1,z348,z2,z3,z4,z5]),(0,[z201,z44,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z250,z4,z81,z5])],[(0,[z201,z0,z215,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z5]),(1,[z44,z1,z2,z3,z4,z93]),(1,[z36,z0,z258,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z24]),(0,[z0,z1,z2,z3,z23,z5,z349]),(0,[z0,z1,z2,z3,z350,z4,z5])],[(0,[z0,z55,z1,z2,z3,z4,z5]),(1,[z105,z1,z18,z3,z4,z5]),(0,[z0,z1,z2,z8,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z351])],[(0,[z0,z1,z2,z142,z4,z5,z24]),(0,[z7,z0,z1,z225,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z5,z257]),(0,[z0,z1,z2,z3,z4,z254,z5]),(0,[z0,z1,z2,z3,z273,z4,z5]),(0,[z0,z1,z34,z2,z3,z4,z5])],[(0,[z352,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z73,z74,z4,z5]),(0,[z0,z1,z225,z3,z4,z152,z5]),(0,[z0,z1,z2,z3,z4,z353,z5])],[(0,[z0,z354,z1,z2,z3,z4,z5]),(0,[z0,z1,z355,z2,z3,z4,z5]),(1,[z87,z0,z2,z86,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z356,z5]),(0,[z0,z1,z2,z3,z357,z4,z5]),(0,[z358,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z359,z3,z4,z5]),(0,[z150,z0,z2,z3,z174,z4,z5])],[(0,[z87,z360,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z88,z5])],[(0,[z361,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z362,z2,z3,z4,z5])],[(0,[z105,z1,z99,z2,z3,z4,z5]),(0,[z0,z1,z2,z363,z3,z4,z5]),(1,[z0,z1,z228,z3,z4,z5]),(0,[z0,z1,z26,z2,z3,z4,z97]),(0,[z0,z1,z2,z3,z4,z364,z5])],[(0,[z0,z1,z18,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z365,z4,z5]),(0,[z1,z2,z3,z211,z4,z189,z5]),(0,[z7,z201,z0,z1,z2,z3,z4]),(0,[z0,z1,z75,z2,z3,z4,z23]),(0,[z366,z0,z1,z2,z3,z4,z5])],[(0,[z7,z0,z1,z2,z3,z367,z5]),(0,[z368,z0,z1,z2,z3,z4,z5]),(0,[z369,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z370,z2,z3,z4,z5]),(0,[z201,z0,z50,z2,z3,z4,z5]),(0,[z0,z1,z73,z17,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z371,z5])],[(0,[z372,z0,z1,z2,z3,z4,z5]),(1,[z210,z1,z2,z142,z4,z5]),(0,[z0,z373,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z374,z3,z4,z5]),(0,[z0,z1,z64,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z375,z5]),(1,[z0,z1,z2,z241,z4,z5]),(0,[z376,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z377,z5]),(0,[z378,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z94,z24]),(0,[z379,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z380]),(0,[z0,z1,z2,z3,z4,z212,z5]),(0,[z381,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z382,z5]),(0,[z0,z1,z32,z2,z3,z233,z5])],[(0,[z383,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z384,z5]),(0,[z0,z1,z385,z2,z3,z4,z5]),(0,[z0,z1,z2,z386,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z387,z5]),(0,[z0,z1,z2,z388,z3,z4,z5]),(0,[z0,z1,z389,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z390]),(0,[z0,z1,z2,z35,z3,z4,z71]),(0,[z0,z80,z1,z2,z3,z4,z5])],[(0,[z0,z1,z391,z2,z3,z4,z5]),(0,[z0,z1,z2,z258,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z392,z5])],[(0,[z0,z1,z2,z3,z393,z4,z5]),(0,[z159,z0,z1,z18,z3,z4,z5]),(0,[z394,z0,z1,z2,z3,z4,z5]),(0,[z36,z0,z19,z2,z3,z4,z5]),(0,[z0,z1,z2,z395,z3,z4,z5]),(0,[z0,z1,z136,z2,z4,z196,z5])],[(1,[z0,z1,z396,z3,z4,z5])],[(0,[z397,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z224,z2,z90,z3,z5]),(0,[z210,z0,z1,z21,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z398,z5]),(0,[z0,z1,z2,z3,z4,z78,z95]),(0,[z0,z1,z2,z3,z4,z5,z399])]],
   [[(0,[z400,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z401,z2,z3,z4,z5]),(0,[z0,z1,z402,z2,z3,z4,z5]),(0,[z0,z403,z1,z2,z3,z4,z5]),(0,[z0,z1,z34,z3,z4,z5,z95])],[(0,[z149,z1,z99,z2,z3,z4,z5]),(0,[z0,z19,z1,z258,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z97]),(0,[z0,z404,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z405,z3,z4,z5])],[(0,[z406,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z407,z3,z4,z5])],[(0,[z168,z115,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z408,z3,z4,z5]),(0,[z0,z1,z26,z90,z3,z4,z5]),(0,[z0,z2,z63,z3,z86,z4,z5])],[(1,[z0,z158,z1,z2,z3,z4]),(0,[z0,z1,z2,z76,z35,z4,z5]),(0,[z0,z409,z1,z2,z3,z4,z5]),(0,[z0,z1,z17,z258,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z410]),(0,[z0,z1,z411,z2,z3,z4,z5])],[(0,[z0,z80,z1,z2,z3,z81,z5]),(0,[z0,z50,z1,z2,z3,z4,z114]),(0,[z0,z1,z2,z3,z412,z4,z5]),(0,[z0,z1,z32,z2,z3,z5,z95])],[(0,[z201,z0,z99,z2,z3,z4,z5]),(0,[z1,z2,z35,z3,z142,z4,z5]),(0,[z0,z1,z413,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z414])],[(0,[z0,z1,z2,z3,z4,z415,z5]),(0,[z116,z0,z1,z2,z3,z211,z5]),(1,[z0,z1,z2,z3,z4,z162]),(0,[z416,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z225,z3,z4,z152]),(0,[z0,z1,z125,z2,z3,z5,z95])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z417]),(0,[z418,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z3,z298,z4,z5]),(0,[z0,z1,z2,z3,z4,z419,z5])],[(0,[z0,z1,z2,z3,z4,z5,z420]),(0,[z0,z1,z2,z3,z4,z23,z94])],[(0,[z0,z1,z421,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z422,z5]),(0,[z423,z0,z1,z2,z3,z4,z5])],[(0,[z424,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z367,z5]),(0,[z0,z1,z2,z3,z4,z425,z5]),(0,[z0,z1,z2,z3,z426,z4,z5]),(0,[z0,z1,z2,z3,z427,z4,z5])],[(0,[z0,z1,z428,z2,z3,z4,z5]),(0,[z116,z0,z1,z2,z3,z189,z5]),(0,[z0,z429,z1,z2,z3,z4,z5]),(0,[z0,z1,z430,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z431,z5])],[(1,[z0,z1,z136,z2,z196,z5]),(0,[z432,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z433,z4,z5]),(0,[z0,z1,z434,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z435])],[(0,[z0,z1,z436,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z437]),(0,[z0,z1,z438,z2,z3,z4,z5]),(0,[z439,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z26,z32,z3,z4,z5]),(0,[z440,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z441,z1,z2,z3,z4,z5]),(0,[z442,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z443,z5])],[(0,[z444,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z212]),(1,[z0,z1,z2,z3,z119,z5]),(0,[z0,z1,z445,z2,z3,z4,z5])],[(1,[z0,z1,z138,z2,z3,z5]),(0,[z446,z0,z1,z2,z3,z4,z5]),(0,[z447,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z448,z2,z3,z4,z5]),(0,[z0,z1,z2,z13,z3,z4,z5])],[(0,[z0,z1,z449,z2,z3,z4,z5]),(0,[z450,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z174,z4,z5]),(0,[z0,z451,z1,z2,z3,z4,z5])],[(0,[z452,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z453,z5]),(0,[z87,z0,z1,z2,z3,z4,z191]),(1,[z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z2,z3,z81,z196,z5]),(0,[z0,z1,z454,z2,z3,z4,z5])],[(0,[z0,z1,z2,z455,z3,z4,z5]),(0,[z0,z62,z1,z2,z86,z4,z5]),(0,[z456,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z76,z3,z4,z23])],[(0,[z0,z1,z90,z3,z20,z4,z5]),(0,[z0,z1,z2,z457,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z458]),(0,[z0,z1,z2,z459,z3,z4,z5]),(0,[z0,z1,z75,z2,z4,z5,z24])]],
   [[(1,[z0,z1,z460,z3,z4,z5]),(0,[z0,z1,z2,z3,z461,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z462,z5]),(0,[z0,z1,z2,z463,z3,z4,z5]),(0,[z0,z1,z2,z464,z3,z4,z5]),(0,[z0,z1,z465,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z466,z4,z5]),(0,[z467,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z468,z5]),(0,[z0,z1,z469,z2,z3,z4,z5]),(0,[z0,z1,z26,z17,z3,z4,z5]),(0,[z0,z1,z2,z13,z3,z40,z5])],[(0,[z1,z99,z2,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z470,z4,z5]),(0,[z0,z19,z1,z26,z3,z4,z5]),(0,[z0,z1,z2,z471,z3,z4,z5]),(0,[z0,z1,z148,z3,z4,z5,z78]),(0,[z0,z1,z136,z2,z3,z14,z5])],[(0,[z105,z1,z18,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z472,z5]),(0,[z0,z1,z473,z2,z3,z4,z5])],[(0,[z474,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z348,z2,z3,z4,z5]),(1,[z102,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z475,z3,z4,z5]),(0,[z0,z1,z2,z14,z4,z196,z5])],[(0,[z0,z1,z2,z476,z3,z4,z5]),(0,[z0,z1,z477,z2,z3,z4,z5]),(0,[z0,z1,z478,z2,z3,z4,z5]),(0,[z479,z0,z1,z2,z3,z4,z5]),(0,[z480,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z481,z4,z5]),(0,[z0,z1,z2,z3,z482,z4,z5]),(0,[z0,z1,z2,z3,z4,z483,z5]),(0,[z0,z1,z2,z484,z3,z4,z5]),(1,[z0,z1,z148,z3,z4,z78]),(0,[z0,z1,z2,z3,z4,z5,z485])],[(1,[z383,z1,z2,z3,z4,z5])]],
   [[(0,[z486,z0,z1,z2,z3,z4,z5]),(0,[z487,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z488,z2,z3,z4,z5])],[(0,[z0,z1,z2,z13,z3,z196,z5])],[(0,[z0,z489,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z490,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z491])],[(0,[z0,z1,z2,z35,z3,z4,z337]),(0,[z188,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z492,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z3,z4,z5]),(0,[z493,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z494]),(0,[z0,z1,z2,z495,z3,z4,z5])],[(0,[z496,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z497,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z23,z95])],[(0,[z0,z1,z2,z3,z498,z4,z5]),(0,[z0,z1,z2,z3,z4,z499,z5]),(0,[z188,z0,z1,z32,z2,z3,z5]),(0,[z116,z0,z1,z228,z3,z4,z5]),(0,[z0,z1,z500,z2,z3,z4,z5]),(0,[z0,z1,z501,z2,z3,z4,z5]),(0,[z0,z1,z502,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z503]),(0,[z0,z1,z2,z3,z4,z5,z504])],[(0,[z115,z1,z2,z3,z142,z4,z5]),(0,[z116,z1,z2,z3,z211,z4,z5]),(0,[z505,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z506,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z507,z4,z5]),(0,[z0,z1,z2,z3,z4,z508,z5]),(0,[z0,z1,z2,z3,z4,z5,z509]),(0,[z0,z510,z1,z2,z3,z4,z5]),(0,[z0,z1,z26,z3,z4,z233,z5]),(0,[z0,z1,z26,z2,z3,z40,z5]),(1,[z0,z1,z2,z3,z4,z83])]],
   [[(1,[z0,z1,z2,z3,z367,z5]),(0,[z44,z0,z1,z225,z2,z3,z4]),(0,[z36,z0,z1,z26,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z254]),(1,[z0,z1,z2,z3,z5,z263])],[(1,[z0,z1,z511,z3,z4,z5]),(0,[z0,z1,z2,z3,z512,z4,z5])],[(0,[z215,z1,z99,z2,z3,z4,z5]),(0,[z159,z105,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z513]),(0,[z0,z1,z2,z3,z4,z514,z5]),(0,[z515,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z516,z5])],[(0,[z0,z1,z2,z3,z517,z4,z5]),(0,[z0,z1,z2,z3,z4,z518,z5]),(1,[z0,z1,z2,z3,z273,z5])],[(0,[z519,z0,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z93,z5,z257]),(0,[z0,z1,z2,z3,z520,z4,z5]),(0,[z0,z1,z2,z3,z4,z521,z5]),(0,[z0,z522,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z40,z189,z5]),(0,[z0,z1,z2,z3,z81,z5,z95]),(0,[z0,z1,z523,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z524]),(0,[z0,z1,z525,z2,z3,z4,z5])],[(0,[z115,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z526,z4,z5]),(0,[z7,z0,z1,z2,z3,z4,z95]),(0,[z44,z0,z1,z2,z3,z4,z23]),(0,[z0,z1,z181,z2,z3,z4,z5])],[(0,[z0,z1,z527,z2,z3,z4,z5])]],
   [[(0,[z528,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z529,z5]),(0,[z116,z0,z1,z396,z3,z4,z5]),(0,[z0,z1,z530,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z51,z5]),(0,[z0,z1,z531,z2,z3,z4,z5])],[(0,[z188,z1,z2,z3,z4,z93,z5])],[(0,[z0,z1,z138,z2,z90,z3,z5]),(0,[z0,z1,z2,z3,z4,z5,z532]),(0,[z0,z1,z3,z20,z4,z233,z5]),(0,[z0,z533,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z534,z5])],[(0,[z0,z1,z2,z3,z535,z4,z5]),(0,[z0,z1,z2,z3,z4,z536,z5]),(0,[z537,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z538,z2,z3,z4,z5]),(0,[z0,z539,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z540,z5]),(0,[z0,z1,z2,z3,z4,z541,z5])],[(0,[z0,z1,z2,z3,z542,z4,z5]),(0,[z0,z1,z543,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z41,z24]),(0,[z0,z1,z2,z3,z4,z41,z5])],[(0,[z0,z1,z544,z2,z3,z4,z5]),(0,[z545,z0,z1,z2,z3,z4,z5]),(1,[z546,z1,z2,z3,z4,z5])],[(0,[z0,z1,z18,z258,z3,z4,z5]),(0,[z0,z1,z2,z396,z3,z4,z5]),(0,[z0,z1,z2,z3,z547,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z548])]],
   [[(0,[z0,z1,z2,z549,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z550,z5]),(0,[z0,z1,z2,z551,z3,z4,z5])],[(0,[z0,z1,z279,z2,z3,z4,z5]),(0,[z0,z1,z552,z2,z3,z4,z5]),(0,[z0,z1,z2,z13,z3,z5,z95])],[(0,[z0,z1,z553,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z554,z5]),(1,[z0,z1,z26,z3,z233,z5]),(0,[z0,z1,z26,z2,z3,z233,z5])],[(0,[z0,z1,z279,z2,z90,z3,z4]),(0,[z0,z555,z1,z2,z3,z4,z5]),(0,[z556,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z557,z4,z5]),(0,[z0,z1,z2,z3,z558,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z326])],[(0,[z159,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z559]),(1,[z0,z80,z2,z3,z81,z5]),(0,[z0,z1,z2,z3,z4,z5,z560])],[(0,[z149,z0,z215,z2,z3,z4,z5]),(0,[z561,z0,z1,z2,z3,z4,z5]),(0,[z105,z115,z1,z2,z3,z4,z5]),(1,[z0,z1,z286,z2,z4,z5]),(0,[z0,z1,z73,z3,z74,z4,z5])],[(0,[z0,z1,z562,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z130,z5]),(0,[z0,z1,z2,z3,z74,z4,z5])],[(0,[z149,z0,z1,z460,z3,z4,z5]),(0,[z0,z1,z2,z563,z3,z4,z5]),(0,[z564,z0,z1,z2,z3,z4,z5]),(0,[z0,z360,z1,z2,z3,z4,z5]),(0,[z150,z0,z1,z2,z3,z174,z5]),(0,[z0,z1,z2,z565,z3,z4,z5]),(0,[z0,z1,z225,z2,z3,z4,z5])]],
   [[(0,[z7,z44,z1,z2,z3,z4,z5]),(0,[z44,z0,z1,z148,z2,z3,z4]),(0,[z87,z0,z1,z497,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z566]),(0,[z0,z1,z148,z3,z20,z4,z5]),(0,[z0,z1,z2,z3,z298,z4,z5])],[(0,[z0,z158,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z567,z5]),(0,[z0,z1,z568,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z569]),(0,[z0,z1,z2,z3,z4,z570,z5]),(0,[z44,z0,z1,z2,z3,z4,z93]),(1,[z0,z1,z343,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z571,z5]),(0,[z0,z1,z2,z3,z4,z23,z5])],[(0,[z36,z0,z1,z181,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z113]),(0,[z0,z1,z2,z3,z4,z572,z5]),(0,[z0,z1,z2,z3,z4,z5,z573])],[(0,[z0,z1,z574,z2,z3,z4,z5]),(1,[z0,z1,z2,z407,z4,z5]),(0,[z0,z1,z2,z3,z575,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z576]),(0,[z0,z1,z2,z3,z4,z577,z5])],[(1,[z116,z1,z2,z3,z211,z5]),(0,[z0,z1,z26,z2,z3,z5,z95]),(0,[z0,z1,z578,z2,z3,z4,z5])],[(0,[z0,z1,z2,z579,z3,z4,z5]),(0,[z7,z0,z50,z1,z2,z3,z4]),(0,[z0,z1,z580,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z153,z95])]],
   [[],[(0,[z0,z1,z2,z3,z4,z5,z581]),(0,[z0,z1,z582,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z152,z95]),(0,[z0,z1,z136,z2,z3,z4,z49]),(0,[z0,z1,z2,z3,z583,z4,z5]),(0,[z0,z1,z2,z3,z584,z4,z5]),(0,[z0,z1,z585,z2,z3,z4,z5])],[(0,[z586,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z587,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z588,z5]),(0,[z0,z1,z52,z2,z3,z4,z5]),(1,[z1,z2,z3,z4,z5,z326])],[(0,[z149,z115,z1,z2,z3,z4,z5]),(0,[z0,z99,z2,z3,z4,z5,z94]),(0,[z0,z589,z1,z2,z3,z4,z5]),(0,[z116,z188,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z590,z4,z5])],[(0,[z591,z0,z1,z2,z3,z4,z5]),(0,[z0,z592,z1,z2,z3,z4,z5]),(0,[z593,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z594,z2,z3,z4,z5]),(0,[z0,z1,z2,z595,z3,z4,z5])],[(0,[z210,z0,z1,z2,z35,z4,z5]),(0,[z7,z0,z1,z2,z3,z4,z5]),(0,[z7,z0,z1,z2,z3,z4,z24]),(0,[z0,z1,z2,z3,z4,z596,z5]),(0,[z597,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z211,z5,z95]),(0,[z7,z0,z1,z2,z3,z4,z41]),(0,[z0,z1,z2,z3,z598,z4,z5]),(1,[z360,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z263]),(0,[z0,z1,z75,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z337]),(0,[z7,z0,z1,z2,z3,z4,z257]),(0,[z0,z1,z2,z599,z3,z4,z5])]],
   [[(0,[z600,z0,z1,z2,z3,z4,z5]),(0,[z188,z0,z1,z26,z2,z3,z5]),(1,[z0,z348,z2,z3,z4,z5]),(0,[z0,z181,z2,z258,z3,z4,z5])],[(0,[z0,z1,z2,z460,z3,z4,z5]),(0,[z210,z168,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z601]),(0,[z0,z1,z2,z3,z4,z5,z602]),(0,[z0,z1,z603,z2,z3,z4,z5]),(0,[z87,z0,z1,z2,z86,z4,z5]),(0,[z0,z1,z604,z2,z3,z4,z5]),(0,[z0,z605,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z349])],[(0,[z606,z0,z1,z2,z3,z4,z5]),(0,[z607,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z26,z148,z3,z4,z5])],[(0,[z0,z1,z90,z258,z3,z4,z5]),(0,[z0,z1,z608,z2,z3,z4,z5])],[(0,[z0,z1,z181,z90,z3,z4,z5]),(0,[z609,z0,z1,z2,z3,z4,z5]),(0,[z201,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z610,z3,z4,z5])],[(1,[z149,z99,z2,z3,z4,z5]),(0,[z0,z215,z2,z3,z4,z5,z94]),(0,[z7,z0,z1,z2,z407,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z611]),(0,[z0,z1,z136,z2,z3,z4,z83])],[(1,[z7,z1,z2,z3,z4,z257]),(0,[z0,z1,z2,z3,z4,z612,z5]),(0,[z0,z1,z613,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z614]),(0,[z0,z1,z2,z3,z4,z5,z615])],[(0,[z0,z1,z616,z2,z3,z4,z5]),(0,[z617,z0,z1,z2,z3,z4,z5]),(0,[z0,z618,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z78]),(0,[z0,z1,z2,z3,z4,z5,z619])]],
   [[(1,[z0,z1,z2,z3,z4,z226])],[(0,[z149,z0,z99,z2,z3,z4,z5]),(0,[z0,z1,z620,z2,z3,z4,z5]),(0,[z0,z1,z2,z621,z3,z4,z5]),(0,[z0,z1,z2,z622,z3,z4,z5]),(1,[z0,z1,z32,z3,z20,z5]),(0,[z623,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z41,z5,z95])],[(0,[z105,z0,z1,z18,z3,z4,z5]),(1,[z0,z1,z497,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z624,z5]),(0,[z0,z1,z625,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z626,z4,z5])],[(0,[z0,z1,z2,z3,z4,z627,z5]),(0,[z0,z1,z2,z628,z3,z4,z5]),(0,[z0,z1,z2,z629,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z630,z5]),(0,[z0,z1,z2,z3,z4,z5,z631]),(0,[z0,z1,z2,z3,z4,z114,z95]),(0,[z546,z0,z1,z2,z3,z4,z5])],[],[(0,[z0,z50,z1,z2,z3,z4,z94]),(0,[z0,z1,z2,z3,z4,z41,z78]),(0,[z0,z1,z2,z3,z256,z4,z5]),(1,[z0,z1,z2,z3,z4,z49])],[(0,[z168,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z632,z5]),(0,[z0,z1,z2,z633,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z41,z114]),(0,[z0,z1,z2,z165,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z41,z152]),(1,[z0,z1,z75,z2,z4,z24]),(0,[z0,z1,z2,z3,z4,z634,z5])]],
   [[(0,[z0,z117,z1,z2,z3,z4,z5]),(0,[z0,z1,z635,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z636,z4,z5]),(0,[z637,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z174,z5]),(0,[z0,z1,z638,z2,z3,z4,z5]),(0,[z0,z639,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z76,z4,z23])],[(0,[z0,z1,z2,z640,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z641,z5]),(0,[z0,z1,z52,z13,z3,z4,z5])],[(0,[z159,z0,z1,z90,z3,z4,z5]),(0,[z210,z0,z1,z511,z3,z4,z5]),(0,[z0,z1,z2,z511,z3,z4,z5]),(0,[z0,z1,z2,z3,z642,z4,z5]),(0,[z0,z1,z26,z3,z74,z4,z5]),(0,[z643,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z41,z5])],[(0,[z168,z0,z1,z2,z142,z4,z5]),(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z644,z0,z1,z2,z3,z4,z5]),(0,[z645,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z256,z152,z5])],[(0,[z646,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z647,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z648]),(0,[z0,z1,z649,z2,z3,z4,z5])],[(0,[z0,z1,z225,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z0,z1,z650,z2,z3,z4,z5]),(0,[z7,z0,z1,z91,z3,z4,z5]),(0,[z0,z1,z2,z3,z174,z196,z5])],[(0,[z0,z1,z651,z2,z3,z4,z5]),(0,[z0,z62,z1,z2,z63,z4,z5]),(0,[z0,z1,z2,z3,z652,z4,z5])],[(0,[z0,z62,z1,z136,z2,z4,z5])]],
   [[(0,[z0,z1,z235,z2,z3,z4,z5]),(0,[z0,z1,z2,z653,z3,z4,z5]),(0,[z0,z1,z2,z3,z654,z4,z5]),(0,[z0,z1,z73,z2,z165,z4,z5]),(0,[z0,z1,z225,z2,z3,z4,z78]),(0,[z0,z1,z2,z3,z655,z4,z5])],[(0,[z0,z1,z2,z3,z142,z4,z5]),(0,[z0,z1,z2,z656,z3,z4,z5]),(0,[z44,z0,z1,z2,z3,z4,z95]),(0,[z657,z0,z1,z2,z3,z4,z5]),(0,[z658,z0,z1,z2,z3,z4,z5]),(0,[z0,z2,z3,z174,z4,z81,z5]),(0,[z0,z1,z225,z2,z3,z4,z152])],[(0,[z168,z1,z2,z35,z3,z4,z5]),(0,[z36,z383,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z659,z5])],[(1,[z0,z1,z303,z2,z3,z4]),(0,[z36,z0,z2,z258,z3,z4,z5]),(0,[z0,z1,z660,z2,z3,z4,z5]),(0,[z0,z1,z136,z2,z3,z4,z5]),(0,[z0,z1,z661,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z662,z4,z5]),(0,[z0,z1,z2,z3,z663,z4,z5])],[(0,[z0,z1,z2,z3,z4,z81,z5]),(0,[z0,z1,z2,z3,z4,z23,z114]),(0,[z0,z1,z3,z74,z20,z4,z5]),(1,[z0,z1,z17,z165,z4,z5]),(0,[z0,z1,z664,z2,z3,z4,z5]),(0,[z0,z665,z1,z2,z3,z4,z5]),(0,[z0,z1,z666,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z667])],[(0,[z668,z0,z1,z2,z3,z4,z5]),(0,[z210,z1,z2,z3,z142,z4,z5]),(1,[z0,z19,z181,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z94]),(1,[z0,z1,z2,z3,z5,z349])],[]],
   [[(0,[z0,z1,z2,z3,z669,z4,z5]),(0,[z0,z1,z224,z2,z3,z4,z5]),(0,[z0,z1,z2,z670,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z671]),(0,[z0,z1,z2,z672,z3,z4,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z116,z0,z1,z32,z2,z3,z5]),(0,[z0,z1,z673,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z674,z5]),(0,[z0,z1,z2,z3,z4,z5,z675]),(0,[z0,z1,z2,z3,z40,z4,z95])],[(0,[z0,z1,z2,z3,z4,z5,z162]),(1,[z0,z1,z2,z3,z4,z191]),(0,[z0,z1,z676,z2,z3,z4,z5])],[(0,[z677,z0,z1,z2,z3,z4,z5]),(0,[z678,z0,z1,z2,z3,z4,z5]),(1,[z188,z1,z2,z3,z189,z5]),(0,[z1,z2,z3,z211,z4,z93,z5]),(0,[z0,z50,z2,z3,z4,z5,z94]),(0,[z0,z1,z679,z2,z3,z4,z5])],[(1,[z0,z1,z3,z170,z4,z5]),(0,[z546,z1,z2,z3,z4,z5,z95])],[(0,[z680,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z681,z2,z3,z4,z5]),(0,[z0,z1,z682,z2,z3,z4,z5])],[(0,[z168,z1,z99,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z683,z5]),(0,[z0,z684,z1,z2,z3,z4,z5]),(0,[z0,z1,z685,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z686,z4,z5]),(0,[z0,z1,z2,z3,z4,z687,z5]),(0,[z0,z1,z2,z688,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z689,z3,z4,z5]),(0,[z188,z0,z1,z2,z3,z211,z5]),(0,[z0,z1,z2,z3,z690,z4,z5])],[(0,[z0,z1,z2,z691,z3,z4,z5]),(0,[z0,z1,z18,z3,z74,z4,z5]),(1,[z0,z1,z2,z3,z4,z71])],[(0,[z115,z215,z1,z2,z3,z4,z5]),(1,[z172,z1,z2,z3,z4,z5]),(0,[z0,z19,z1,z181,z3,z4,z5]),(0,[z0,z692,z1,z2,z3,z4,z5])],[(0,[z0,z1,z693,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z694,z4,z5]),(0,[z0,z1,z2,z3,z695,z4,z5]),(0,[z0,z1,z2,z3,z4,z696,z5]),(0,[z0,z1,z2,z3,z4,z114,z5]),(0,[z0,z1,z2,z3,z4,z114,z24]),(0,[z0,z1,z2,z3,z4,z697,z5]),(0,[z0,z1,z2,z3,z698,z4,z5]),(0,[z699,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z700,z5]),(0,[z0,z1,z2,z343,z3,z4,z5]),(0,[z0,z1,z2,z63,z3,z4,z5])],[(0,[z0,z1,z17,z181,z3,z4,z5]),(1,[z0,z62,z2,z63,z4,z5]),(0,[z0,z1,z2,z3,z174,z5,z95]),(0,[z0,z1,z2,z3,z20,z4,z5]),(0,[z0,z1,z148,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z701,z4,z5]),(0,[z201,z0,z1,z2,z3,z4,z114]),(0,[z0,z1,z2,z3,z4,z702,z5]),(0,[z703,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z704,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z705,z4,z5]),(0,[z0,z1,z2,z3,z4,z93,z5]),(0,[z0,z1,z3,z170,z4,z81,z5]),(0,[z0,z1,z125,z2,z3,z4,z95]),(0,[z0,z706,z1,z2,z3,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z211,z367,z5]),(0,[z0,z1,z707,z3,z4,z5]),(0,[z0,z1,z32,z3,z20,z5])],[(0,[z0,z1,z2,z3,z43,z95]),(0,[z0,z1,z497,z3,z4,z5]),(0,[z708,z1,z2,z3,z4,z5]),(0,[z0,z1,z34,z3,z4,z97]),(0,[z0,z1,z26,z3,z5,z153])],[(0,[z0,z1,z2,z3,z40,z212]),(0,[z0,z1,z8,z3,z367,z5]),(0,[z0,z1,z3,z20,z227,z5])],[(0,[z0,z1,z34,z125,z3,z95])],[(0,[z116,z1,z2,z3,z709,z5]),(0,[z0,z1,z91,z407,z4,z5]),(0,[z546,z1,z3,z4,z5,z153])],[(0,[z0,z1,z710,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z711]),(0,[z7,z1,z2,z407,z4,z257]),(0,[z0,z1,z2,z3,z712,z5])],[(0,[z0,z1,z2,z3,z4,z713]),(0,[z0,z1,z2,z3,z4,z714]),(0,[z0,z1,z2,z3,z141,z95]),(0,[z0,z1,z75,z2,z4,z24])],[(0,[z0,z1,z2,z3,z715,z5]),(0,[z1,z2,z3,z211,z709,z5]),(0,[z0,z1,z2,z3,z4,z716]),(0,[z0,z1,z717,z2,z3,z4]),(0,[z0,z1,z2,z76,z4,z718])]],
   [[(0,[z243,z1,z90,z3,z4,z5]),(0,[z0,z1,z303,z224,z2,z3]),(0,[z0,z719,z2,z3,z4,z5]),(0,[z0,z451,z2,z3,z81,z5]),(0,[z0,z1,z413,z2,z3,z95]),(0,[z0,z1,z26,z3,z514,z5])],[],[(0,[z0,z1,z2,z3,z4,z720])],[(0,[z0,z1,z721,z3,z4,z5]),(0,[z0,z1,z2,z3,z722,z4]),(0,[z1,z18,z723,z3,z4,z5]),(0,[z0,z1,z286,z2,z4,z724]),(0,[z0,z1,z2,z3,z4,z724]),(0,[z0,z1,z2,z3,z156,z95])],[(0,[z0,z1,z2,z725,z4,z5]),(0,[z0,z1,z726,z3,z4,z5]),(0,[z1,z2,z3,z211,z5,z458]),(0,[z0,z1,z727,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z49]),(0,[z546,z1,z125,z2,z3,z95])],[(0,[z0,z1,z2,z728,z4,z5]),(0,[z0,z1,z2,z3,z729,z5]),(0,[z0,z1,z2,z3,z256,z95])],[(0,[z0,z1,z730,z3,z4,z5])],[(0,[z0,z1,z731,z3,z4,z5]),(0,[z0,z1,z732,z3,z4,z5]),(0,[z0,z62,z2,z733,z4,z5]),(0,[z0,z1,z2,z13,z14,z5])]],
   [[(0,[z168,z1,z2,z35,z4,z5]),(0,[z0,z734,z1,z2,z3,z4]),(0,[z735,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z718]),(0,[z0,z1,z2,z3,z40,z736])],[(0,[z0,z1,z2,z14,z88,z5]),(0,[z0,z1,z737,z74,z4,z5])],[(0,[z0,z1,z2,z3,z4,z738]),(0,[z0,z1,z739,z2,z3,z4])],[(0,[z115,z740,z2,z3,z4,z5]),(0,[z44,z0,z1,z2,z3,z130]),(0,[z0,z1,z125,z2,z3,z95])],[(0,[z168,z1,z2,z741,z4,z5]),(0,[z0,z1,z125,z2,z3,z736])],[(0,[z7,z1,z91,z3,z4,z257]),(0,[z0,z19,z181,z3,z4,z5]),(0,[z0,z1,z2,z742,z4,z5]),(0,[z0,z1,z286,z64,z4,z5]),(0,[z0,z1,z562,z2,z3,z95]),(0,[z0,z1,z743,z3,z4,z5])],[(0,[z0,z1,z3,z744,z4,z5]),(0,[z87,z0,z343,z86,z4,z5])],[(0,[z0,z1,z2,z3,z256,z254])]],
   [[(0,[z0,z745,z2,z3,z4,z5]),(0,[z0,z1,z8,z3,z4,z41]),(0,[z0,z1,z2,z746,z4,z5]),(0,[z0,z1,z343,z3,z88,z5]),(0,[z747,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z748]),(0,[z0,z1,z749,z2,z3,z4]),(0,[z750,z1,z2,z3,z4,z5])],[(0,[z0,z1,z3,z751,z4,z5]),(0,[z0,z1,z2,z3,z4,z752]),(0,[z753,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z254])],[(0,[z0,z1,z2,z754,z4,z5]),(0,[z188,z1,z527,z2,z3,z5])],[(0,[z0,z55,z2,z3,z4,z94]),(0,[z0,z1,z2,z3,z4,z755]),(0,[z0,z1,z2,z756,z4,z5]),(0,[z0,z1,z26,z396,z3,z5])],[(0,[z0,z1,z2,z757,z4,z5]),(0,[z0,z1,z3,z5,z758,z349])],[(0,[z759,z172,z1,z2,z3,z4]),(0,[z0,z1,z760,z3,z4,z5])],[(0,[z115,z215,z2,z3,z4,z5]),(0,[z0,z117,z2,z3,z367,z5]),(0,[z0,z1,z2,z3,z761,z5])],[(0,[z0,z1,z3,z762,z4,z5]),(0,[z0,z1,z8,z407,z4,z5]),(0,[z44,z429,z1,z2,z3,z4]),(0,[z0,z2,z3,z733,z4,z5]),(0,[z0,z1,z2,z3,z4,z763])]],
   [[(0,[z115,z1,z460,z3,z4,z5]),(0,[z0,z1,z90,z3,z4,z97]),(0,[z0,z1,z2,z3,z4,z71]),(0,[z0,z1,z2,z3,z43,z5])],[(0,[z172,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z764]),(0,[z0,z765,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z43,z41]),(0,[z172,z1,z258,z3,z4,z5]),(1,[z0,z1,z737,z4,z5]),(0,[z0,z1,z2,z595,z4,z23])],[(0,[z766,z1,z2,z3,z4,z5]),(0,[z0,z1,z767,z3,z4,z5])],[(0,[z360,z1,z2,z3,z88,z5])],[(0,[z0,z1,z2,z3,z4,z768])],[(0,[z0,z1,z303,z8,z3,z4]),(0,[z0,z1,z769,z3,z4,z5]),(0,[z0,z1,z2,z3,z770,z5]),(0,[z188,z1,z2,z3,z367,z5]),(0,[z0,z1,z2,z3,z4,z771])],[(0,[z0,z1,z235,z3,z4,z5]),(0,[z0,z1,z772,z3,z4,z5]),(0,[z0,z773,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z774,z5])],[(0,[z0,z1,z775,z3,z4,z5]),(0,[z0,z1,z2,z3,z776,z71]),(0,[z0,z1,z3,z4,z5,z777]),(0,[z0,z1,z2,z3,z5,z778]),(0,[z87,z0,z2,z86,z119,z5])]],
   [[(0,[z126,z1,z2,z142,z4,z5]),(0,[z0,z1,z2,z407,z4,z71]),(0,[z116,z1,z396,z3,z211,z5]),(0,[z0,z1,z2,z407,z43,z5]),(0,[z0,z1,z779,z3,z4,z5]),(0,[z0,z1,z328,z74,z4,z5])],[(0,[z0,z1,z2,z3,z4,z780]),(0,[z0,z1,z781,z2,z3,z5]),(0,[z0,z1,z2,z3,z5,z782]),(0,[z0,z1,z26,z3,z419,z5])],[(0,[z0,z1,z21,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z783]),(0,[z0,z348,z8,z3,z4,z5]),(0,[z0,z1,z784,z3,z4,z5])],[(0,[z0,z1,z785,z2,z3,z4]),(0,[z0,z1,z2,z3,z786,z5]),(0,[z0,z1,z2,z3,z4,z787]),(0,[z0,z1,z2,z3,z788,z5])],[(0,[z0,z740,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z789]),(0,[z188,z1,z2,z3,z709,z5]),(0,[z87,z102,z2,z86,z4,z5]),(0,[z0,z1,z2,z3,z790,z5]),(0,[z0,z1,z2,z3,z256,z5]),(0,[z0,z1,z26,z3,z5,z263]),(0,[z0,z1,z125,z3,z153,z95])],[(0,[z1,z2,z3,z741,z4,z5]),(0,[z7,z0,z1,z34,z3,z4]),(0,[z0,z1,z2,z3,z4,z791]),(0,[z0,z1,z2,z3,z4,z792]),(0,[z0,z1,z2,z3,z256,z41])],[(0,[z0,z1,z303,z225,z3,z4]),(0,[z0,z1,z343,z3,z4,z162]),(0,[z0,z1,z286,z2,z40,z5]),(0,[z0,z1,z2,z3,z4,z793]),(1,[z0,z1,z3,z4,z794])],[(0,[z0,z1,z2,z3,z4,z795]),(0,[z0,z1,z2,z3,z4,z796]),(0,[z116,z1,z402,z2,z3,z5]),(0,[z0,z1,z2,z407,z4,z24]),(0,[z797,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z40,z41])]],
   [[(0,[z0,z1,z2,z798,z4,z5]),(0,[z7,z1,z8,z3,z4,z257]),(0,[z0,z1,z225,z656,z3,z4])],[(0,[z7,z1,z2,z3,z211,z95]),(0,[z0,z1,z3,z4,z5,z758])],[(0,[z0,z1,z2,z3,z367,z23]),(0,[z0,z799,z1,z2,z3,z4]),(0,[z0,z1,z52,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z800])],[(0,[z0,z1,z2,z3,z801,z5]),(0,[z0,z348,z2,z3,z43,z5]),(0,[z0,z1,z802,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z803]),(0,[z0,z1,z804,z3,z4,z5]),(0,[z0,z1,z279,z2,z3,z4]),(0,[z0,z1,z17,z463,z4,z5]),(0,[z0,z1,z26,z3,z612,z5]),(0,[z0,z80,z64,z3,z81,z5]),(0,[z0,z1,z2,z3,z805,z5])],[(0,[z0,z1,z26,z224,z3,z5]),(0,[z0,z1,z64,z3,z4,z5]),(0,[z102,z1,z2,z3,z88,z5]),(0,[z0,z1,z286,z2,z196,z5])],[(0,[z0,z1,z806,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z807]),(0,[z0,z2,z63,z733,z4,z5]),(0,[z0,z1,z3,z808,z4,z5])],[(0,[z0,z1,z809,z2,z3,z4]),(0,[z546,z1,z2,z3,z189,z5])]],
   [[(0,[z296,z1,z90,z3,z4,z5]),(0,[z1,z2,z741,z142,z4,z5]),(0,[z0,z1,z91,z3,z43,z5]),(0,[z0,z1,z2,z3,z810,z5]),(0,[z0,z1,z3,z811,z130,z5])],[(0,[z812,z0,z2,z3,z4,z5]),(0,[z0,z813,z2,z3,z4,z5]),(0,[z7,z1,z2,z3,z43,z257]),(0,[z7,z1,z2,z3,z4,z516]),(0,[z0,z1,z2,z4,z5,z814]),(0,[z360,z1,z2,z3,z4,z162]),(0,[z0,z1,z2,z14,z392,z5])],[(0,[z0,z1,z2,z774,z196,z5])],[(0,[z0,z1,z225,z3,z4,z630]),(0,[z0,z117,z2,z407,z4,z5]),(0,[z0,z1,z8,z3,z4,z95])],[(0,[z0,z1,z2,z241,z4,z95]),(0,[z0,z1,z815,z3,z4,z5]),(0,[z0,z1,z2,z3,z48,z41]),(0,[z0,z2,z3,z4,z816,z5])],[(0,[z7,z1,z500,z2,z3,z4]),(0,[z0,z1,z817,z3,z4,z5])],[(0,[z149,z99,z235,z3,z4,z5]),(0,[z0,z1,z300,z74,z4,z5]),(0,[z0,z1,z818,z3,z4,z5])],[(0,[z0,z1,z2,z3,z819,z5]),(0,[z0,z1,z2,z3,z4,z820]),(0,[z0,z1,z2,z3,z119,z162]),(0,[z0,z1,z2,z3,z821,z5]),(0,[z0,z1,z822,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z823,z5]),(0,[z546,z1,z2,z3,z4,z23])],[(0,[z36,z383,z258,z3,z4,z5]),(0,[z0,z1,z2,z4,z718,z24])],[(0,[z0,z1,z824,z3,z4,z5]),(0,[z0,z1,z825,z3,z4,z5]),(0,[z826,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z827,z5]),(0,[z0,z1,z828,z3,z4,z5])],[(0,[z360,z1,z2,z3,z119,z5]),(0,[z0,z1,z2,z3,z829,z5])],[(0,[z0,z1,z2,z3,z4,z830]),(0,[z0,z1,z2,z3,z831,z5]),(0,[z0,z1,z832,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z833]),(0,[z87,z0,z2,z86,z4,z191]),(0,[z0,z80,z2,z250,z81,z5]),(0,[z0,z1,z73,z737,z4,z5])],[(0,[z210,z1,z511,z142,z4,z5]),(0,[z0,z1,z2,z241,z367,z5]),(0,[z0,z1,z2,z250,z4,z5]),(0,[z0,z1,z2,z3,z4,z834])],[(0,[z0,z1,z835,z2,z3,z5]),(0,[z0,z1,z2,z3,z88,z191]),(0,[z0,z1,z3,z4,z5,z836]),(0,[z0,z62,z2,z583,z4,z5]),(0,[z0,z1,z2,z3,z130,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z337])],[(0,[z0,z1,z2,z3,z174,z11])],[(0,[z1,z2,z3,z709,z4,z5])],[(0,[z0,z1,z2,z3,z4,z837]),(0,[z7,z1,z2,z3,z4,z326]),(0,[z102,z1,z2,z3,z4,z162]),(0,[z0,z50,z2,z3,z4,z94])],[(0,[z168,z1,z2,z35,z4,z71]),(0,[z44,z0,z1,z34,z3,z4]),(0,[z0,z1,z2,z3,z4,z838])],[(0,[z0,z1,z2,z3,z839,z5]),(0,[z7,z0,z1,z2,z3,z349]),(0,[z0,z1,z286,z2,z5,z95])],[(0,[z36,z0,z840,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z153]),(0,[z0,z1,z2,z3,z5,z736])],[(0,[z0,z1,z2,z407,z4,z23]),(0,[z201,z0,z207,z2,z3,z4]),(0,[z0,z1,z2,z3,z254,z95])]],
   [[(0,[z361,z99,z2,z3,z4,z5]),(0,[z105,z1,z18,z3,z4,z5]),(0,[z0,z1,z2,z3,z736,z95])],[(0,[z105,z1,z574,z3,z4,z5])],[(0,[z0,z1,z436,z2,z3,z95]),(0,[z0,z841,z2,z3,z4,z5]),(0,[z0,z1,z73,z74,z4,z5])],[(0,[z0,z1,z842,z2,z3,z4]),(0,[z0,z1,z2,z4,z71,z24]),(0,[z87,z0,z2,z86,z4,z5]),(0,[z0,z2,z3,z4,z843,z5])],[(0,[z0,z1,z844,z3,z4,z5])],[(0,[z102,z1,z2,z3,z119,z5]),(0,[z0,z1,z2,z3,z88,z5]),(0,[z0,z1,z286,z2,z88,z5])],[(0,[z0,z1,z2,z3,z845,z5]),(0,[z0,z1,z846,z2,z3,z4]),(0,[z0,z2,z733,z86,z4,z5])],[(0,[z0,z1,z228,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z847]),(0,[z643,z1,z2,z3,z211,z5]),(0,[z0,z1,z34,z3,z4,z78])]],
   [[(0,[z0,z1,z848,z3,z4,z5]),(0,[z0,z1,z140,z74,z4,z5]),(0,[z0,z19,z840,z3,z4,z5]),(0,[z0,z1,z286,z2,z4,z849]),(0,[z0,z1,z2,z3,z4,z849]),(0,[z0,z1,z34,z3,z4,z152]),(0,[z0,z1,z52,z3,z5,z95])],[(0,[z0,z1,z2,z850,z4,z5]),(0,[z0,z1,z2,z3,z851,z5])],[(0,[z0,z1,z8,z3,z4,z5]),(0,[z210,z1,z2,z142,z4,z5]),(0,[z0,z348,z2,z3,z4,z23]),(0,[z0,z1,z3,z4,z5,z852])],[(0,[z0,z1,z853,z3,z4,z5]),(0,[z0,z1,z2,z241,z4,z5]),(0,[z0,z1,z2,z3,z212,z95]),(0,[z0,z1,z854,z3,z4,z5]),(0,[z0,z1,z136,z2,z196,z83])],[(0,[z0,z1,z2,z3,z4,z855]),(0,[z201,z0,z348,z2,z3,z4]),(0,[z0,z1,z2,z241,z4,z41]),(0,[z0,z1,z3,z737,z4,z5]),(0,[z0,z1,z3,z4,z5,z856])],[(0,[z0,z1,z2,z3,z857,z5]),(0,[z0,z1,z2,z3,z4,z858]),(0,[z0,z1,z859,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z860]),(0,[z0,z1,z2,z3,z861,z5]),(0,[z0,z1,z32,z3,z788,z5]),(0,[z0,z1,z52,z13,z14,z5])],[],[(0,[z0,z1,z2,z3,z4,z862]),(0,[z0,z1,z136,z2,z634,z5])]],
   [[(0,[z116,z1,z228,z3,z211,z5]),(0,[z0,z1,z2,z13,z774,z5])],[],[(0,[z0,z1,z396,z3,z4,z5]),(0,[z0,z863,z2,z3,z4,z5]),(0,[z0,z30,z2,z3,z4,z94]),(0,[z0,z1,z2,z3,z114,z349])],[(0,[z519,z1,z90,z3,z4,z5]),(0,[z0,z1,z3,z864,z4,z5])],[(0,[z0,z1,z224,z2,z3,z5]),(0,[z418,z1,z90,z3,z4,z5]),(0,[z0,z1,z865,z3,z4,z5]),(0,[z0,z1,z866,z2,z4,z5]),(0,[z0,z1,z136,z2,z774,z5])],[(0,[z0,z1,z2,z867,z4,z5])],[(0,[z149,z55,z99,z2,z3,z4]),(0,[z0,z313,z181,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z868]),(0,[z869,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z870]),(0,[z871,z172,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z872])]],
   [[(0,[z0,z158,z1,z2,z3,z4]),(0,[z0,z1,z2,z873,z4,z5]),(0,[z0,z1,z2,z874,z4,z5])],[(0,[z159,z1,z90,z3,z4,z5]),(0,[z0,z1,z138,z17,z3,z5]),(0,[z0,z1,z75,z2,z4,z718])],[(0,[z0,z1,z2,z3,z4,z875]),(0,[z44,z1,z2,z3,z4,z326]),(0,[z876,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z5,z877]),(0,[z0,z1,z26,z3,z152,z95])],[(0,[z0,z1,z2,z3,z4,z162]),(0,[z0,z1,z2,z4,z5,z878]),(0,[z0,z1,z2,z3,z40,z567])],[(0,[z1,z2,z3,z4,z93,z879]),(0,[z44,z0,z1,z2,z3,z349]),(0,[z0,z1,z3,z298,z4,z5]),(0,[z0,z1,z3,z4,z152,z794]),(0,[z1,z3,z4,z5,z153,z326])],[(0,[z201,z0,z55,z2,z3,z4]),(0,[z0,z1,z279,z224,z2,z3]),(0,[z880,z1,z2,z3,z4,z5]),(0,[z0,z1,z881,z2,z4,z5]),(0,[z0,z1,z882,z3,z4,z5]),(0,[z0,z1,z2,z3,z273,z49])],[(0,[z0,z1,z224,z396,z3,z5]),(0,[z0,z348,z2,z241,z4,z5]),(0,[z0,z1,z2,z3,z4,z883])],[(0,[z0,z1,z2,z3,z884,z5]),(0,[z0,z1,z148,z3,z4,z97]),(0,[z0,z1,z2,z76,z273,z23])]],
   [[(0,[z0,z1,z2,z3,z4,z885]),(0,[z87,z0,z497,z86,z4,z5]),(0,[z0,z80,z2,z3,z886,z5]),(0,[z0,z1,z3,z626,z20,z5]),(0,[z0,z1,z2,z3,z273,z95])],[(0,[z0,z1,z2,z3,z130,z114]),(0,[z1,z2,z3,z4,z5,z887])],[(0,[z0,z1,z2,z3,z888,z5]),(0,[z293,z1,z18,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z889]),(0,[z0,z1,z2,z3,z4,z890]),(0,[z0,z1,z497,z3,z88,z5]),(0,[z0,z1,z891,z3,z4,z5])],[(0,[z0,z1,z91,z241,z4,z5])],[(0,[z0,z1,z3,z892,z4,z5]),(0,[z168,z1,z2,z35,z4,z337]),(0,[z7,z1,z2,z241,z4,z257])],[(0,[z7,z1,z2,z3,z4,z879]),(0,[z0,z1,z17,z28,z4,z5]),(0,[z360,z1,z343,z3,z4,z5]),(0,[z0,z50,z2,z3,z4,z843]),(0,[z0,z1,z3,z4,z794,z78]),(0,[z0,z1,z893,z3,z5,z349])],[(0,[z0,z117,z2,z3,z4,z5]),(0,[z0,z1,z138,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z894]),(0,[z105,z1,z723,z3,z4,z5]),(0,[z0,z1,z2,z895,z4,z5]),(0,[z896,z0,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z897,z5])]],
   [[(0,[z215,z740,z2,z3,z4,z5]),(0,[z0,z80,z2,z3,z81,z11]),(0,[z0,z1,z898,z3,z4,z5])],[(0,[z0,z55,z1,z2,z3,z884]),(0,[z0,z899,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z11]),(0,[z0,z1,z900,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z794])],[(0,[z0,z1,z343,z3,z119,z5]),(0,[z0,z1,z2,z3,z886,z5])],[(0,[z0,z1,z460,z3,z4,z5]),(0,[z740,z99,z2,z3,z4,z5]),(0,[z0,z1,z2,z741,z4,z5]),(0,[z0,z1,z2,z3,z4,z901]),(0,[z0,z1,z2,z3,z902,z5]),(0,[z0,z1,z903,z3,z4,z5]),(0,[z0,z1,z52,z3,z40,z5]),(0,[z0,z1,z77,z2,z4,z24])],[(0,[z0,z1,z904,z3,z4,z5])],[(0,[z0,z1,z3,z905,z4,z5]),(0,[z0,z1,z224,z3,z20,z5]),(0,[z116,z1,z2,z3,z211,z212]),(0,[z172,z1,z26,z3,z4,z5])],[(0,[z0,z1,z906,z3,z4,z5]),(0,[z0,z55,z348,z2,z3,z4]),(0,[z0,z1,z2,z3,z907,z5]),(0,[z0,z1,z2,z908,z4,z5]),(0,[z0,z1,z64,z3,z40,z5])]],
   [[(0,[z0,z1,z2,z3,z909,z5]),(0,[z0,z1,z910,z3,z4,z5])],[(0,[z0,z1,z911,z3,z4,z5]),(1,[z740,z2,z3,z4,z5])],[(0,[z159,z1,z224,z90,z3,z5]),(0,[z0,z2,z3,z912,z4,z5]),(0,[z0,z1,z2,z3,z4,z913]),(0,[z0,z1,z148,z3,z4,z78])],[(0,[z0,z1,z2,z3,z914,z5]),(0,[z0,z2,z840,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z915]),(0,[z0,z1,z2,z3,z81,z11]),(0,[z0,z2,z3,z886,z4,z5])],[(0,[z0,z1,z916,z3,z4,z5]),(0,[z0,z917,z2,z3,z4,z5]),(0,[z0,z1,z2,z13,z5,z39])],[(0,[z546,z1,z2,z3,z367,z5])],[(0,[z0,z1,z918,z3,z4,z5])],[(0,[z0,z1,z2,z919,z4,z5]),(0,[z0,z1,z2,z3,z4,z920]),(0,[z102,z1,z343,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z921]),(0,[z0,z1,z893,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z922,z5]),(0,[z0,z1,z923,z2,z4,z5]),(0,[z115,z319,z2,z3,z4,z5]),(0,[z0,z1,z924,z3,z4,z5]),(0,[z925,z1,z2,z3,z4,z5]),(0,[z0,z1,z497,z3,z4,z162]),(0,[z0,z1,z26,z3,z788,z5])],[(0,[z0,z1,z2,z3,z5,z926]),(0,[z0,z1,z26,z3,z233,z254])],[(0,[z0,z1,z927,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z718])],[(0,[z0,z1,z3,z788,z233,z5])],[(0,[z0,z1,z928,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z929]),(0,[z0,z1,z2,z3,z367,z5])],[(0,[z609,z0,z258,z3,z4,z5]),(0,[z1,z2,z3,z4,z879,z257]),(0,[z202,z0,z258,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z930]),(0,[z0,z1,z2,z3,z4,z931]),(0,[z0,z1,z2,z3,z4,z932]),(0,[z0,z2,z3,z886,z81,z5])],[(0,[z0,z1,z2,z3,z933,z5]),(1,[z1,z2,z741,z4,z5]),(0,[z0,z117,z91,z3,z4,z5])],[(0,[z0,z934,z2,z3,z4,z5]),(0,[z7,z117,z2,z3,z4,z257]),(0,[z0,z1,z2,z3,z273,z5]),(0,[z0,z1,z2,z3,z935,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z936]),(0,[z0,z1,z2,z3,z273,z41])],[],[(0,[z149,z740,z2,z3,z4,z5]),(0,[z44,z1,z2,z3,z4,z93]),(0,[z36,z0,z258,z3,z4,z5]),(0,[z0,z1,z497,z3,z119,z5]),(0,[z0,z1,z937,z3,z4,z5]),(0,[z0,z1,z136,z2,z196,z49])],[(0,[z0,z1,z2,z3,z709,z5]),(0,[z0,z1,z3,z20,z5,z263])],[(0,[z149,z99,z460,z3,z4,z5]),(0,[z0,z938,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z939]),(0,[z0,z1,z2,z407,z367,z5]),(0,[z44,z1,z2,z3,z4,z879]),(0,[z0,z1,z286,z2,z14,z5]),(0,[z0,z1,z2,z3,z4,z940])],[(0,[z0,z1,z2,z941,z4,z5]),(0,[z159,z1,z279,z90,z3,z4]),(0,[z0,z1,z26,z303,z3,z4]),(0,[z0,z1,z2,z3,z942,z5]),(0,[z0,z348,z2,z3,z4,z95]),(0,[z943,z1,z2,z3,z4,z5])],[(0,[z0,z1,z8,z3,z43,z5]),(0,[z0,z1,z944,z3,z4,z5])],[(0,[z0,z1,z2,z241,z43,z5]),(0,[z0,z1,z64,z250,z4,z5])]],
   [[(0,[z0,z1,z945,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z946]),(0,[z947,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z96,z4,z23]),(0,[z0,z1,z2,z3,z41,z736])],[(0,[z0,z1,z948,z2,z4,z5]),(0,[z0,z1,z949,z3,z4,z5]),(0,[z0,z1,z950,z2,z3,z5]),(0,[z0,z1,z343,z3,z4,z191]),(0,[z0,z1,z3,z4,z5,z951]),(0,[z0,z1,z165,z737,z4,z5]),(0,[z0,z1,z17,z610,z4,z5]),(0,[z0,z1,z952,z3,z4,z5]),(1,[z0,z1,z2,z4,z718])],[(0,[z172,z1,z181,z3,z4,z5]),(0,[z0,z1,z953,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z954])],[(0,[z0,z1,z2,z3,z955,z5]),(0,[z0,z1,z2,z956,z4,z5]),(0,[z0,z957,z2,z3,z4,z5]),(0,[z958,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z326,z226]),(0,[z0,z1,z2,z3,z94,z349]),(1,[z0,z1,z3,z788,z5]),(0,[z546,z1,z32,z2,z3,z5]),(0,[z0,z1,z445,z2,z3,z95])],[(0,[z0,z1,z2,z76,z4,z71]),(0,[z959,z1,z2,z3,z4,z5])],[(0,[z0,z1,z960,z3,z4,z5]),(0,[z102,z1,z497,z3,z4,z5]),(0,[z0,z1,z64,z3,z5,z95])],[(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z348,z2,z3,z367,z5])]],
   [[(0,[z210,z1,z21,z142,z4,z5])],[(0,[z0,z1,z2,z3,z4,z879]),(0,[z962,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z152,z203]),(0,[z0,z1,z2,z14,z774,z5])],[(0,[z0,z1,z963,z2,z3,z5]),(0,[z0,z1,z964,z3,z4,z5])],[(0,[z168,z1,z2,z628,z4,z5]),(0,[z0,z1,z2,z3,z71,z965]),(0,[z0,z1,z2,z3,z966,z5]),(0,[z0,z967,z2,z3,z4,z5])],[(0,[z1,z2,z3,z709,z189,z5]),(0,[z0,z1,z91,z3,z367,z5]),(0,[z360,z1,z2,z3,z4,z191])],[(0,[z0,z1,z968,z3,z4,z5]),(0,[z7,z1,z2,z3,z367,z257])],[(0,[z607,z1,z18,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z969])],[(0,[z0,z1,z343,z3,z4,z5]),(0,[z0,z80,z2,z3,z81,z113]),(0,[z970,z1,z2,z3,z4,z5]),(0,[z0,z1,z157,z3,z4,z152]),(0,[z0,z1,z2,z76,z23,z349])]],
   [[(0,[z0,z1,z2,z3,z5,z971]),(0,[z0,z1,z2,z3,z4,z113])],[(0,[z0,z117,z8,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z972]),(0,[z0,z1,z2,z973,z4,z5]),(0,[z974,z1,z2,z3,z4,z5])],[(0,[z0,z1,z975,z3,z4,z5]),(0,[z116,z1,z2,z3,z211,z5]),(0,[z0,z186,z181,z3,z4,z5]),(0,[z0,z1,z2,z3,z119,z191]),(0,[z0,z2,z3,z4,z976,z5])],[(0,[z0,z1,z2,z4,z23,z718])],[(0,[z0,z1,z3,z4,z5,z794])],[(0,[z87,z360,z2,z86,z4,z5]),(0,[z0,z1,z3,z977,z4,z5]),(0,[z0,z1,z370,z2,z3,z95]),(0,[z0,z978,z2,z3,z4,z5])],[(0,[z0,z55,z1,z2,z3,z979]),(0,[z597,z1,z90,z3,z4,z5]),(0,[z0,z50,z2,z3,z130,z94]),(0,[z0,z1,z225,z3,z4,z152])],[(0,[z0,z1,z2,z3,z4,z980]),(0,[z0,z1,z2,z3,z981,z5]),(0,[z0,z50,z348,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z982])]],
   [[(0,[z0,z1,z2,z737,z4,z5])],[(0,[z442,z1,z18,z3,z4,z5]),(0,[z0,z1,z2,z983,z4,z5]),(1,[z0,z1,z2,z774,z5])],[(0,[z360,z1,z2,z3,z4,z5]),(0,[z115,z309,z2,z3,z4,z5]),(0,[z0,z1,z984,z3,z4,z5]),(0,[z0,z117,z2,z3,z43,z5]),(0,[z0,z1,z2,z3,z5,z985])],[(1,[z1,z2,z3,z4,z879]),(0,[z0,z1,z2,z490,z4,z24]),(0,[z0,z706,z2,z3,z4,z94])],[(0,[z0,z1,z2,z3,z4,z986]),(0,[z0,z1,z26,z3,z233,z97]),(0,[z1,z987,z2,z3,z4,z5]),(0,[z0,z1,z136,z2,z196,z5])],[(0,[z0,z1,z2,z3,z988,z5]),(0,[z0,z1,z989,z3,z4,z5]),(0,[z0,z1,z2,z990,z4,z5]),(0,[z0,z1,z991,z3,z4,z5]),(0,[z0,z348,z2,z3,z4,z41]),(0,[z992,z1,z2,z3,z4,z5])],[(0,[z0,z1,z993,z3,z4,z5]),(0,[z102,z1,z2,z3,z4,z191])],[(0,[z0,z994,z2,z3,z4,z5]),(0,[z111,z0,z2,z3,z174,z5])]],
   [[(0,[z0,z1,z2,z995,z3,z4]),(0,[z248,z1,z90,z3,z4,z5]),(0,[z264,z1,z2,z35,z4,z5]),(0,[z0,z1,z2,z3,z4,z212]),(0,[z0,z19,z3,z461,z4,z5]),(0,[z0,z1,z2,z3,z119,z5]),(0,[z0,z996,z1,z2,z3,z4])],[],[(0,[z0,z1,z2,z3,z5,z965]),(0,[z997,z1,z2,z3,z4,z5])],[(0,[z0,z1,z998,z2,z3,z4]),(0,[z0,z1,z18,z3,z4,z97]),(0,[z0,z1,z999,z3,z4,z5])],[(0,[z0,z348,z2,z407,z4,z5])],[],[(0,[z0,z1,z67,z2,z4,z24]),(0,[z0,z1,z1000,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1001,z5]),(0,[z366,z1,z2,z142,z4,z5])]],
   [[],[(0,[z0,z1,z1002,z3,z4,z5]),(0,[z0,z1,z1003,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z185])],[(0,[z0,z1,z170,z250,z4,z5]),(0,[z0,z1,z2,z3,z4,z49])],[(0,[z0,z1,z2,z1004,z4,z5]),(0,[z0,z1,z2,z3,z4,z1005]),(0,[z0,z1006,z2,z3,z4,z5]),(0,[z1007,z1,z2,z3,z4,z5]),(0,[z87,z0,z502,z2,z4,z5])],[(0,[z102,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z1008,z4,z5]),(0,[z87,z0,z2,z86,z88,z5]),(0,[z0,z1,z2,z76,z4,z23]),(1,[z0,z1,z2,z3,z736])],[(0,[z0,z1009,z2,z3,z4,z5]),(0,[z116,z1,z2,z3,z211,z226])],[(0,[z383,z1,z2,z3,z4,z5]),(0,[z0,z1,z138,z279,z2,z3]),(0,[z0,z1,z26,z640,z3,z5]),(0,[z0,z1,z26,z3,z146,z5]),(0,[z0,z1,z2,z3,z4,z736])],[(0,[z0,z1,z2,z3,z1010,z5]),(0,[z0,z840,z258,z3,z4,z5]),(0,[z0,z1,z2,z3,z1011,z5]),(0,[z546,z1,z26,z2,z3,z5]),(0,[z0,z1,z2,z1012,z4,z5])]],
   [[(0,[z44,z1,z219,z2,z3,z4])],[(0,[z0,z1,z154,z2,z4,z24])],[(0,[z57,z99,z2,z3,z4,z5]),(0,[z1,z2,z35,z741,z4,z5]),(0,[z1,z2,z3,z4,z93,z226]),(0,[z0,z1,z2,z3,z130,z94]),(0,[z0,z1,z13,z298,z14,z5])],[(0,[z0,z1,z723,z3,z4,z5]),(0,[z0,z1,z2,z3,z1013,z5]),(0,[z379,z1,z18,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1014]),(0,[z0,z1,z1015,z2,z3,z5]),(0,[z0,z1,z2,z3,z1016,z5])],[(0,[z0,z1,z138,z303,z2,z3]),(0,[z0,z1,z1017,z3,z4,z5]),(0,[z0,z348,z91,z3,z4,z5]),(0,[z36,z172,z258,z3,z4,z5]),(0,[z0,z1,z329,z2,z3,z95])],[(0,[z7,z348,z2,z3,z4,z257])],[(0,[z0,z1,z2,z3,z4,z1018]),(0,[z0,z1,z2,z3,z4,z1019]),(0,[z0,z1,z1020,z3,z4,z5]),(0,[z0,z1,z3,z1021,z4,z5]),(0,[z0,z1,z1022,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z83])],[(0,[z0,z1,z303,z2,z3,z4]),(0,[z0,z1,z2,z3,z367,z24]),(0,[z360,z1,z497,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z254]),(0,[z0,z1,z2,z3,z5,z263])]],
   [[(0,[z0,z1,z1023,z2,z3,z5]),(0,[z1,z2,z723,z3,z4,z5]),(0,[z0,z1,z511,z3,z4,z5]),(0,[z1024,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1025,z5])],[(0,[z0,z1,z2,z3,z4,z1026]),(0,[z0,z1,z8,z241,z4,z5]),(0,[z7,z1,z2,z3,z4,z85]),(0,[z0,z871,z1,z2,z3,z4]),(0,[z1027,z1,z2,z3,z4,z5]),(0,[z87,z0,z2,z733,z4,z5]),(0,[z0,z1,z3,z4,z1028,z5]),(0,[z0,z1,z2,z3,z4,z1029]),(0,[z0,z1,z286,z170,z4,z5]),(0,[z0,z1,z17,z165,z4,z5]),(0,[z0,z1,z2,z3,z1030,z5])],[(0,[z0,z1,z2,z1031,z4,z5]),(0,[z0,z1,z1032,z2,z3,z5]),(0,[z0,z1,z1033,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z349])],[(0,[z7,z1,z2,z3,z4,z226]),(0,[z1034,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z733,z4,z5])],[(0,[z1,z740,z2,z3,z4,z5]),(0,[z0,z1,z2,z1035,z4,z5]),(0,[z0,z1,z2,z1036,z4,z5]),(0,[z0,z1,z136,z2,z88,z5]),(0,[z0,z1,z2,z3,z4,z843])],[(0,[z0,z1,z2,z3,z1037,z5]),(0,[z0,z1,z1038,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1039]),(0,[z0,z1,z2,z3,z1040,z5]),(0,[z0,z1,z3,z811,z4,z5]),(0,[z0,z1,z3,z4,z788,z5]),(0,[z1041,z1,z2,z3,z4,z5])],[(0,[z1,z99,z460,z3,z4,z5]),(0,[z0,z1042,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z191]),(0,[z0,z1,z2,z551,z14,z5]),(0,[z0,z2,z3,z4,z843,z94]),(0,[z0,z1,z32,z3,z5,z153])],[(0,[z270,z215,z2,z3,z4,z5]),(0,[z159,z1,z138,z90,z3,z5]),(0,[z0,z1,z1043,z3,z4,z5]),(0,[z188,z1,z2,z3,z189,z5]),(0,[z0,z1,z2,z1044,z4,z5]),(0,[z1045,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z51,z5]),(0,[z0,z80,z3,z170,z81,z5]),(0,[z0,z1,z225,z3,z4,z794])]],
   [[(0,[z1,z2,z3,z4,z5,z879]),(0,[z0,z1,z3,z170,z4,z5]),(0,[z0,z1,z2,z3,z1046,z5]),(0,[z1047,z1,z2,z3,z4,z5]),(0,[z1048,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1049,z3,z4,z5])],[(0,[z0,z1,z2,z1050,z3,z5]),(0,[z0,z1,z225,z8,z3,z4]),(0,[z1051,z1,z2,z3,z4,z5]),(0,[z87,z0,z2,z86,z4,z162])],[(0,[z0,z1,z2,z3,z4,z1052])],[(0,[z0,z1,z138,z3,z74,z5]),(0,[z0,z1,z2,z3,z1053,z5]),(0,[z0,z1,z2,z3,z88,z162]),(0,[z0,z1,z900,z3,z130,z5])],[(0,[z149,z158,z99,z2,z3,z4]),(1,[z1,z723,z3,z4,z5]),(0,[z546,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1054]),(0,[z546,z1,z2,z3,z4,z24])],[(0,[z0,z1,z2,z3,z134,z95])],[(0,[z0,z1,z1055,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1056])]],
   [[(0,[z1,z125,z2,z3,z326,z95])],[(0,[z0,z1,z1057,z3,z4,z5]),(0,[z0,z1058,z2,z3,z4,z5]),(0,[z0,z62,z2,z63,z4,z5]),(0,[z0,z1,z2,z3,z4,z1059]),(0,[z0,z1,z26,z3,z233,z5])],[(0,[z1,z34,z3,z4,z5,z326])],[(0,[z0,z1,z1060,z2,z3,z5]),(0,[z0,z1,z2,z3,z4,z1061]),(0,[z1,z587,z90,z3,z4,z5]),(0,[z0,z1,z2,z3,z1062,z5]),(0,[z759,z0,z1,z2,z3,z4]),(0,[z0,z1,z840,z3,z4,z5]),(0,[z36,z0,z15,z3,z4,z5]),(0,[z0,z80,z2,z3,z81,z5]),(0,[z0,z80,z286,z2,z81,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z1,z723,z90,z3,z4,z5]),(0,[z0,z1,z286,z2,z4,z5]),(0,[z0,z1,z1063,z3,z4,z5]),(0,[z546,z1,z34,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1064]),(0,[z0,z1,z1065,z3,z4,z5]),(0,[z172,z1,z3,z20,z4,z5]),(0,[z0,z1,z2,z3,z774,z5])],[(0,[z0,z1,z1066,z3,z4,z5]),(0,[z0,z1,z1067,z3,z4,z5]),(0,[z0,z1,z2,z3,z1068,z5])],[(0,[z0,z1069,z2,z3,z4,z5]),(0,[z159,z1,z723,z3,z4,z5]),(0,[z0,z1,z2,z1070,z4,z5])]],
   [[(1,[z1,z2,z3,z709,z5]),(0,[z0,z1,z434,z2,z3,z95]),(0,[z1,z2,z1071,z3,z4,z5])],[(0,[z0,z1,z1072,z3,z4,z5]),(0,[z0,z1,z2,z1073,z4,z5]),(0,[z0,z1,z303,z3,z20,z4]),(0,[z0,z1,z2,z3,z1074,z5]),(0,[z1075,z1,z2,z3,z4,z5]),(0,[z1076,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1077,z3,z4,z5]),(0,[z0,z1,z1078,z3,z4,z5])],[(0,[z0,z1,z2,z3,z776,z5]),(0,[z0,z1,z1079,z3,z4,z5]),(1,[z0,z2,z733,z4,z5]),(0,[z0,z1,z34,z3,z4,z5])],[(0,[z0,z1,z2,z407,z4,z5]),(0,[z0,z1080,z2,z3,z4,z5]),(0,[z1081,z1,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z152,z97]),(0,[z0,z1,z225,z3,z152,z263]),(0,[z0,z1,z2,z3,z49,z95])],[(0,[z0,z1,z2,z1082,z4,z5]),(0,[z0,z1,z2,z3,z1083,z5]),(0,[z159,z1,z303,z90,z3,z4]),(0,[z0,z117,z2,z241,z4,z5]),(0,[z7,z1,z682,z2,z3,z4]),(0,[z0,z1,z2,z4,z5,z1084]),(0,[z0,z1,z17,z737,z4,z5])],[(0,[z210,z1,z2,z741,z4,z5]),(0,[z1,z2,z3,z4,z5,z1085])],[(0,[z0,z1,z1086,z3,z4,z5]),(0,[z546,z1,z2,z3,z211,z5]),(0,[z0,z1,z2,z3,z5,z1087]),(0,[z0,z1,z3,z20,z788,z5]),(0,[z0,z1,z148,z3,z4,z794])]],
   [[(0,[z0,z1,z32,z396,z3,z5]),(0,[z1088,z1,z2,z3,z4,z5])],[(0,[z0,z55,z1,z2,z3,z4]),(0,[z0,z1,z1089,z2,z4,z5]),(0,[z1,z2,z3,z4,z5,z326]),(0,[z0,z1,z2,z3,z4,z1090]),(0,[z0,z1,z2,z3,z4,z1091])],[(0,[z0,z1,z148,z8,z3,z4])],[(0,[z0,z1,z497,z3,z4,z191]),(0,[z1092,z1,z2,z3,z4,z5]),(0,[z0,z1093,z2,z3,z4,z5]),(0,[z0,z1,z1094,z2,z3,z4])],[(0,[z0,z1,z2,z3,z43,z212]),(0,[z7,z0,z1,z2,z3,z130])],[(0,[z0,z1,z1095,z3,z4,z5])],[(0,[z609,z99,z2,z3,z4,z5]),(0,[z44,z1,z2,z3,z4,z251]),(0,[z0,z1,z225,z3,z256,z152])],[(0,[z0,z348,z2,z3,z4,z5]),(0,[z0,z1,z3,z4,z5,z1096]),(0,[z0,z348,z2,z3,z4,z24]),(0,[z0,z1,z2,z4,z1097,z5]),(0,[z0,z706,z2,z3,z81,z5]),(0,[z0,z1,z3,z5,z153,z263])]],
   [[(0,[z0,z1,z303,z3,z4,z78]),(0,[z0,z181,z840,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1098,z4]),(0,[z0,z1,z2,z3,z1099,z5]),(0,[z1100,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z1101,z5]),(0,[z0,z1,z26,z3,z472,z5]),(0,[z0,z1,z2,z3,z4,z97])],[(1,[z0,z840,z3,z4,z5]),(0,[z0,z50,z2,z3,z51,z94]),(0,[z0,z2,z3,z4,z5,z1102])],[(0,[z149,z99,z2,z3,z4,z5]),(0,[z0,z1,z91,z3,z4,z5]),(0,[z0,z1103,z2,z3,z4,z5]),(0,[z0,z1104,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1105])],[(0,[z0,z1,z2,z1106,z4,z5]),(0,[z0,z1,z1107,z3,z4,z5]),(0,[z7,z1,z2,z3,z4,z257]),(0,[z0,z1,z2,z3,z4,z1108])],[(0,[z0,z1,z2,z3,z979,z5]),(0,[z0,z1,z2,z3,z1109,z5])],[(0,[z0,z1,z1110,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z226]),(0,[z0,z1,z2,z3,z4,z1111])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 547) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 547).take 533) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1080)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [547, 533] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 159).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 159).take 97).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [159, 97] = true :=
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

end PEqualNP.Outside.L_meta_37563

theorem PEqualNP.Outside.L_meta_37563 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4276666560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4276666560) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37563.solve