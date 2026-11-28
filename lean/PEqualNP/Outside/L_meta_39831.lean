import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39831

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
  Nat.testBit (4008373480 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x041133036438c6f2#64 ++ 0x81044cc0d90e31bc#64 ++ 0x9d33f707ec79cff3#64 ++ 0xe74cfdc1fb1e73fc#64 : BitVec 256),
   (0x00448068a1835154#64 ++ 0xc011201a2860d455#64 ++ 0xfecc89f8f38ff1ff#64 ++ 0xffb3227e3ce3fc7f#64 : BitVec 256),
   (0x030b0c151c0c2a2b#64 ++ 0x00c2c30547030a8a#64 ++ 0xd70f0e1f1c0e3e3f#64 ++ 0xb5c3c387c7038f8f#64 : BitVec 256),
   (0x0bb00fa01ad03d80#64 ++ 0x02ec03e806b40f60#64 ++ 0xeff00fe01ff03fc3#64 ++ 0x7bfc03f807fc0ff0#64 : BitVec 256),
   (0x23efd0001f6f8000#64 ++ 0x08fbf40007dbe000#64 ++ 0xabfff0001fffc002#64 ++ 0xeafffc0007fff000#64 : BitVec 256),
   (0x13feefdec0000000#64 ++ 0x04ffbbf7b0000000#64 ++ 0xf3ffffffe0000001#64 ++ 0xfcfffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 3]⟩, ⟨.or, [6, 5]⟩, ⟨.or, [0, 3]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [9, 1]⟩, ⟨.and, [1, 7]⟩, ⟨.or, [11, 4]⟩, ⟨.and, [8, 12]⟩, ⟨.or, [2, 13]⟩, ⟨.and, [10, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000002021835154 0xc00000080860d455 0x0c000000138ff1fe 0x0300000004e3fc7f

def z1 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xfecc89f8f38ff1ff 0xffb3227e3ce3fc7f

def z2 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z3 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x9d33f707ec79cff3 0xe74cfdc1fb1e73fc

def z4 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z5 : W := mkw 0x1bfeeffedad03d80 0x06ffbbffb6b40f60 0xfffffffffff03fc3 0xfffffffffffc0ff0

def z6 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xabfff0001fffc002 0xeafffc0007fff000

def z7 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xfacc89f8e381c1c1 0xfeb3227e38e07070

def z8 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z9 : W := mkw 0x041033036030c6f2 0x81040cc0d80c31bc 0x1c30f707e071cff1 0x470c3dc1f81c73fc

def z10 : W := mkw 0x08100fa000903d80 0x020403e800240f60 0x44000fe000003fc1 0x110003f800000ff0

def z11 : W := mkw 0x204fd000052f8000 0x0813f400014be000 0x000ff000000fc000 0x8003fc000003f000

def z12 : W := mkw 0x030a0c1418042809 0x00c2830506010a02 0x420c08181006300c 0x1083020604018c03

def z13 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0x28f0f00003f1c000 0x4a3c3c0000fc7000

def z14 : W := mkw 0x081003a000901580 0x020400e800240560 0x000001e0000001c0 0x0000007800000070

def z15 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xfffffe1f1ffffe3f 0xffffff87c7ffff8f

def z16 : W := mkw 0x10102fdec0000000 0x04040bf7b0000000 0x50000fffe0000001 0x140003fff8000000

def z17 : W := mkw 0x0000002021835154 0xc00000080860d455 0x9c008100f38ff1ff 0xe70020403ce3fc7f

def z18 : W := mkw 0x080000201ad03d80 0x0200000806b40f60 0x0c0000001ff03fc2 0x0300000007fc0ff0

def z19 : W := mkw 0x104ee05ec0000000 0x0413b817b0000000 0x100ff01fe0000000 0x8403fc07f8000000

def z20 : W := mkw 0x23a110001f6f8000 0x08e8440007dbe000 0xabf000001fffc002 0x6afc000007fff000

def z21 : W := mkw 0x33eeccdc9b470000 0x0cfbb33726d1c000 0x62cc08f813860000 0x18b3023e04e18000

def z22 : W := mkw 0x200110001f6f8000 0x0800440007dbe000 0x080000001fffc002 0x0200000007fff000

def z23 : W := mkw 0x23ab50001e6c8000 0x08ead400079b2000 0x013370000c700000 0x004cdc00031c0000

def z24 : W := mkw 0x0ba00ca01ad03d80 0x02e8032806b40f60 0x6ec008e01ff03fc2 0x1bb0023807fc0ff0

def z25 : W := mkw 0x17bb7f97443886a2 0x05eedfe5d10e21a8 0x013376070c700e00 0x004cdd81c31c0380

def z26 : W := mkw 0x0bb11fa01ef8bd80 0x02ec47e807be2f60 0xeff3ffe01ff9ffc3 0xfbfcfff807fe7ff0

def z27 : W := mkw 0x0001100004288000 0x00004400010a2000 0x8933f0000c79c002 0xe24cfc00031e7000

def z28 : W := mkw 0x27fff3037f7fc6f2 0x89fffcc0dfdff1bc 0xbffff707ffffcff3 0xeffffdc1fffff3fc

def z29 : W := mkw 0x0445b04be52bc276 0xc1116c12f94af09d 0x100ff01fe00fc03c 0x8403fc07f803f00f

def z30 : W := mkw 0x0044800001030000 0x001120000040c000 0xaacc8000138fc002 0xeab3200004e3f000

def z31 : W := mkw 0x13feefdec1030000 0x04ffbbf7b040c000 0xfbfffffff38fc003 0xfefffffffce3f000

def z32 : W := mkw 0x000b0015040c022b 0x0002c0054103008a 0x100f001f000e003c 0x8403c007c003800f

def z33 : W := mkw 0x13ffefdedc0c0000 0x04fffbf7b7030000 0xf3fffffffc0e0003 0xfcffffffff038000

def z34 : W := mkw 0x0fb13f835e78aea2 0x03ec4fe0d79e2ba8 0x013376070c700e00 0x004cdd81c31c0380

def z35 : W := mkw 0x0010230240000000 0x000408c090000000 0x9133f707e0000001 0xe44cfdc1f8000000

def z36 : W := mkw 0x03a000001a400000 0x00e8000006900000 0xabf000001ff00002 0x6afc000007fc0000

def z37 : W := mkw 0x105eefdec0000000 0x0417bbf7b0000000 0x500fffffe0000001 0x9403fffff8000000

def z38 : W := mkw 0x0000002000801100 0x0000000800200440 0x0c000000138031c2 0x0300000004e00c70

def z39 : W := mkw 0x0455b34be438c6f2 0x81156cd2f90e31bc 0xffffffffec79cff3 0xfffffffffb1e73fc

def z40 : W := mkw 0x13ba6f9640000000 0x04ee9be590000000 0x0133760700000000 0x004cdd81c0000000

def z41 : W := mkw 0x1bba6fb65ad03d80 0x06ee9bed96b40f60 0xeff37fe71ff03fc3 0x7bfcdff9c7fc0ff0

def z42 : W := mkw 0x031a2f1640000000 0x00c68bc590000000 0xd33fff1fe0000001 0xf4cfffc7f8000000

def z43 : W := mkw 0x030a0c1400000000 0x00c2830500000000 0x420c081800000000 0x1083020600000000

def z44 : W := mkw 0x041033026030c4d0 0x81040cc0980c3134 0x9933f707e071c1c1 0xe64cfdc1f81c7070

def z45 : W := mkw 0x17ffffdfe438c6f2 0x85fffff7f90e31bc 0xffffffffec79cff3 0xfffffffffb1e73fc

def z46 : W := mkw 0x0bff8ffdbfdf7fff 0xc2ffe3ff6ff7dfff 0xffff8fffffffffff 0xffffe3ffffffffff

def z47 : W := mkw 0x0410236be09057f6 0xc10408daf82415fd 0x54000fffe0003ffd 0x150003fff8000fff

def z48 : W := mkw 0x0000004880000000 0x0000001220000000 0x500009f8e0000001 0x1400027e38000000

def z49 : W := mkw 0x041033026030c4d0 0x81040cc0980c3134 0x0830f100e071c1c0 0x420c3c40381c7070

def z50 : W := mkw 0x030a000000000000 0x00c2800000000000 0x830f000000000000 0xa0c3c00000000000

def z51 : W := mkw 0x00448c7da1837b7f 0xc011231f6860dedf 0xfecc8ffff38fffff 0xffb323fffce3ffff

def z52 : W := mkw 0x1054affee1835154 0xc4152bffb860d455 0xfecc8ffff38ff1ff 0xffb323fffce3fc7f

def z53 : W := mkw 0x00459000052b8000 0x00116400014ae000 0xabfff0001fffc002 0xeafffc0007fff000

def z54 : W := mkw 0x0010030000100480 0x000400c000040120 0x013006000c700e00 0x004c0180031c0380

def z55 : W := mkw 0x0000002000801100 0x0000000800200440 0x440009e0000031c1 0x1100027800000c70

def z56 : W := mkw 0x00448048a1034054 0xc01120122840d015 0x100c8018e00fc03c 0x840320063803f00f

def z57 : W := mkw 0x040130036428c272 0x81004c00d90a309c 0x1003f007e009c030 0x8400fc01f802700c

def z58 : W := mkw 0x03eec00001030000 0x00fbb0000040c000 0xabfff000138fc002 0xeafffc0004e3f000

def z59 : W := mkw 0x03b00f8018002800 0x00ec03e006000a00 0xe7f00fe01c003e03 0x79fc03f807000f80

def z60 : W := mkw 0x0454b36ae1b3d5d4 0xc1152cdab86cf575 0x28f0f1e0e3f1c1c0 0x4a3c3c7838fc7070

def z61 : W := mkw 0x0455b36be5bbd7f6 0xc1156cdaf96ef5fd 0xffffffffffffffff 0xffffffffffffffff

def z62 : W := mkw 0x0401102125bbd7f6 0xc1004408496ef5fd 0x0c0000001ffffffe 0x0300000007ffffff

def z63 : W := mkw 0x0000100000208000 0x0000040000082000 0x0830f0000071c000 0x420c3c00001c7000

def z64 : W := mkw 0x030b0c153c0c6a7b 0x80c2c3054f031a9e 0xdf0f8f1ffc0fffff 0xf7c3e3c7ff03ffff

def z65 : W := mkw 0x10f4e3cac0000000 0x043d38f2b0000000 0x20f0f1e0e0000000 0x483c3c7838000000

def z66 : W := mkw 0x13feeffee1835154 0xc4ffbbffb860d455 0xfffffffff38ff1ff 0xfffffffffce3fc7f

def z67 : W := mkw 0x0044806881831104 0x4011201a2060c441 0xeecc09f8138631cf 0x7bb3027e04e18c73

def z68 : W := mkw 0x0010032000901580 0x000400c800240560 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z69 : W := mkw 0x2bf4dfa01bf3bd80 0x0afd37e806fcef60 0xeff0ffe01ff1ffc3 0x7bfc3ff807fc7ff0

def z70 : W := mkw 0x03000c0018002800 0x00c0030006000a00 0xd70c0e181c0e3e3f 0xb5c3038607038f8f

def z71 : W := mkw 0x08100fe8a0907dd4 0xc20403fa28241f75 0x54000ff8e0003ffd 0x150003fe38000fff

def z72 : W := mkw 0x23efd068bfefd154 0xc8fbf41a2ffbf455 0xfffff9f8fffff1ff 0xfffffe7e3ffffc7f

def z73 : W := mkw 0x0001000104080222 0x0000400041020088 0x950306070c080e33 0xa540c181c302038c

def z74 : W := mkw 0x071b3f177c3ceefb 0x81c6cfc5df0f3bbe 0xdf3fff1ffc7fffff 0xf7cfffc7ff1fffff

def z75 : W := mkw 0x24f5f303677bc6f2 0x893d7cc0d9def1bc 0xbdf3f707eff9cff3 0xef7cfdc1fbfe73fc

def z76 : W := mkw 0x0c102fa360907ff2 0x83040be8d8241ffc 0x54000fe7e0003ff1 0x150003f9f8000ffc

def z77 : W := mkw 0x0ba00ca01ac03900 0x02e8032806b00e40 0xebf008e01ff03002 0x7afc023807fc0c00

def z78 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x28c081e0e381c1c0 0x4a30207838e07070

def z79 : W := mkw 0x13feefdee1034054 0xc4ffbbf7b840d015 0xf3ffffffe00fc03d 0xfcfffffff803f00f

def z80 : W := mkw 0x03100f0018102c80 0x00c403c006040b20 0xcf300f001c703fc3 0x73cc03c0071c0ff0

def z81 : W := mkw 0x08b003a002d01580 0x022c00e800b40560 0x28f001e003f001c0 0x4a3c007800fc0070

def z82 : W := mkw 0x0bbb0fb51edc3fab 0x02eec3ed47b70fea 0xffff0fff1ffe3fff 0xffffc3ffc7ff8fff

def z83 : W := mkw 0x040110012438c6f2 0x81004400490e31bc 0x0c0000000c79cff2 0x03000000031e73fc

def z84 : W := mkw 0x0fb13f837e78eef2 0x83ec4fe0df9e3bbc 0x9d33f707ec79cff3 0xe74cfdc1fb1e73fc

def z85 : W := mkw 0x0044804880000000 0x0011201220000000 0xf2cc89f8e0000001 0xfcb3227e38000000

def z86 : W := mkw 0x000100011c0c2a2b 0x0000400047030a8a 0xd60c08181c0e3e3f 0xb583020607038f8f

def z87 : W := mkw 0x03b003001a500480 0x00ec00c006940120 0xaff007001ff00fc3 0x6bfc01c007fc03f0

def z88 : W := mkw 0x23efdc141f6f8000 0x08fbf70507dbe000 0xfbfffe1f1fffc003 0xfeffff87c7fff000

def z89 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xaacc81e0f38fc1c2 0xeab320783ce3f070

def z90 : W := mkw 0x0fb13fa37ef8fff2 0x83ec4fe8dfbe3ffc 0xfff3ffe7fff9fff3 0xfffcfff9fffe7ffc

def z91 : W := mkw 0x10fee3dec0000000 0x043fb8f7b0000000 0x30fff1ffe0000000 0xcc3ffc7ff8000000

def z92 : W := mkw 0x03b00f8000000000 0x00ec03e000000000 0xe3f00fe000000001 0x78fc03f800000000

def z93 : W := mkw 0x034e8c7c9987390d 0x40d3a31f2661ce43 0x62cc08f81386300c 0x18b3023e04e18c03

def z94 : W := mkw 0x034f8c5dbd0f6a7f 0xc0d3e3176f43da9f 0xd70f8e1ffc0ffe3f 0xb5c3e387ff03ff8f

def z95 : W := mkw 0x23efd0489f6f8000 0x08fbf41227dbe000 0xfbfff9f8ffffc003 0xfefffe7e3ffff000

def z96 : W := mkw 0x04102303601046f2 0x810408c0d80411bc 0x14000707e0000ff1 0x050001c1f80003fc

def z97 : W := mkw 0x23eed00003638000 0x08fbb40000d8e000 0xabfff00003f1c000 0xeafffc0000fc7000

def z98 : W := mkw 0x00a0000002400000 0x0028000000900000 0x28f0000003f00000 0x4a3c000000fc0000

def z99 : W := mkw 0x230b1c151f6faa2b 0x08c2c70547dbea8a 0xdf0f0e1f1ffffe3f 0xb7c3c387c7ffff8f

def z100 : W := mkw 0x0411336be4b8d7f6 0xc1044cdaf92e35fd 0xdd33ffffec79ffff 0xf74cfffffb1e7fff

def z101 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x6acc89f8f387f1cc 0x5ab3227e3ce1fc73

def z102 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x6af009e013f031c0 0x5abc027804fc0c70

def z103 : W := mkw 0x0001000104080222 0x0000400041020088 0x040000000c080e32 0x010000000302038c

def z104 : W := mkw 0x33feffdec3638000 0x0cffbff7b0d8e000 0xfbffffffe3f1c001 0xfefffffff8fc7000

def z105 : W := mkw 0x2bffdfa01fffbd80 0x0afff7e807ffef60 0xefffffe01fffffc3 0xfbfffff807fffff0

def z106 : W := mkw 0x04102303601046f2 0x810408c0d80411bc 0x9d300707ec700ff3 0x674c01c1fb1c03fc

def z107 : W := mkw 0x23ab50001e6c8000 0x08ead400079b2000 0xabf370001ff00002 0x6afcdc0007fc0000

def z108 : W := mkw 0x2bffdf801f7fac80 0x0afff7e007dfeb20 0xabfff6001fffce02 0xeafffd8007fff380

def z109 : W := mkw 0x0010030000100480 0x000400c000040120 0x8d3007000c700fc3 0x634c01c0031c03f0

def z110 : W := mkw 0x13ffefdfdc0c2a2b 0x04fffbf7f7030a8a 0xf7fffffffc0e3e3f 0xfdffffffff038f8f

def z111 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1403f707e009cff1 0x8500fdc1f80273fc

def z112 : W := mkw 0x33ffffdedf6f8000 0x0cfffff7b7dbe000 0xfbffffffffffc003 0xfefffffffffff000

def z113 : W := mkw 0x23ab50001e6c8000 0x08ead400079b2000 0x833f70001c7e0002 0xa0cfdc00071f8000

def z114 : W := mkw 0x0bba0fb41ad03d80 0x02ee83ed06b40f60 0xffff0fff1ff03fc3 0xffffc3ffc7fc0ff0

def z115 : W := mkw 0x200110011f6faa2b 0x0800440047dbea8a 0x0c0000001ffffe3e 0x0300000007ffff8f

def z116 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x23ff70001ff60000 0x08ffdc0007fd8000

def z117 : W := mkw 0x03000c0018002800 0x00c0030006000a00 0xc7000e001c003e03 0x31c0038007000f80

def z118 : W := mkw 0x13feefdeda400000 0x04ffbbf7b6900000 0xfbfffffffff00003 0xfefffffffffc0000

def z119 : W := mkw 0x030a0c1400000000 0x00c2830500000000 0x0103060700000000 0x0040c181c0000000

def z120 : W := mkw 0x03000c0018002800 0x00c0030006000a00 0x4200080010003000 0x1080020004000c00

def z121 : W := mkw 0x08b00fa002d03d80 0x022c03e800b40f60 0x6cf00fe003f03fc1 0x5b3c03f800fc0ff0

def z122 : W := mkw 0x10f4efdec0000000 0x043d3bf7b0000000 0x70f0ffffe0000001 0x5c3c3ffff8000000

def z123 : W := mkw 0x03eec00000000000 0x00fbb00000000000 0xa3fff00000000000 0xe8fffc0000000000

def z124 : W := mkw 0x0bf48fe8bbd37dd4 0xc2fd23fa2ef4df75 0xeff08fe0fff1ffc3 0x7bfc23f83ffc7ff0

def z125 : W := mkw 0x0bb00f801a502c80 0x02ec03e006940b20 0xc7300e001c703e03 0x31cc0380071c0f80

def z126 : W := mkw 0x00000068a1835154 0xc000001a2860d455 0x5c0009f8f38ff1ff 0x1700027e3ce3fc7f

def z127 : W := mkw 0x100a601640000000 0x0402980590000000 0x0003700700000000 0x0000dc01c0000000

def z128 : W := mkw 0x00000048a0004054 0xc000001228001015 0x10000018e000003c 0x040000063800000f

def z129 : W := mkw 0x000b0015040c022b 0x0002c0054103008a 0xd60f081f100e303f 0xb583c207c4038c0f

def z130 : W := mkw 0x07113f037c38eef2 0x81c44fc0df0e3bbc 0xdf33ff07fc79fff3 0xf7ccffc1ff1e7ffc

def z131 : W := mkw 0x030a0c1418042809 0x00c2830506010a02 0xd30f0e1f1006300d 0xb4c3c387c4018c03

def z132 : W := mkw 0x000b0c15040c2a2b 0x0002c30541030a8a 0x540f0e1f000e3e3d 0x9503c387c0038f8f

def z133 : W := mkw 0x0044806881831104 0x4011201a2060c441 0x62cc08f81386300c 0x18b3023e04e18c03

def z134 : W := mkw 0x0bb00f801a502c80 0x02ec03e006940b20 0x013006000c700e00 0x004c0180031c0380

def z135 : W := mkw 0x000100011c0c2a2b 0x0000400047030a8a 0x040000001c0e3e3e 0x0100000007038f8f

def z136 : W := mkw 0x20e4d068a3e3d154 0xc839341a28f8f455 0xfefcf9f8f3fff1ff 0xffbf3e7e3cfffc7f

def z137 : W := mkw 0x08100fa000903d80 0x020403e800240f60 0xcd300fe00c703fc3 0x734c03f8031c0ff0

def z138 : W := mkw 0x3bfffffedfffbd80 0x0effffffb7ffef60 0xffffffffffffffc3 0xfffffffffffffff0

def z139 : W := mkw 0x280110201fffbd80 0x0a00440807ffef60 0x0c0000001fffffc2 0x0300000007fffff0

def z140 : W := mkw 0x0000000020004050 0x8000000008001014 0x9c008100e009c1f3 0xe70020403802707c

def z141 : W := mkw 0x0bb00f801a502c80 0x02ec03e006940b20 0x8d3007000c700fc3 0x634c01c0031c03f0

def z142 : W := mkw 0x04102f1760106efb 0x81040bc5d8041bbe 0x54000f1fe0003ffd 0x150003c7f8000fff

def z143 : W := mkw 0x23efdc001f6fa800 0x08fbf70007dbea00 0xeffffe001ffffe03 0xfbffff8007ffff80

def z144 : W := mkw 0x0000000000100480 0x0000000000040120 0x0c0000000c700fc2 0x03000000031c03f0

def z145 : W := mkw 0x10102fdec0000000 0x04040bf7b0000000 0xd133ffffe0000001 0xf44cfffff8000000

def z146 : W := mkw 0x23eec0001b470000 0x08fbb00006d1c000 0x22cc000013860000 0x08b3000004e18000

def z147 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xfffc0ff81ffe3fff 0xffff03fe07ff8fff

def z148 : W := mkw 0x0bf48fe8bbd37dd4 0xc2fd23fa2ef4df75 0xfffc8ff8ffffffff 0xffff23fe3fffffff

def z149 : W := mkw 0x13feef9640000000 0x04ffbbe590000000 0xa3fff60700000000 0xe8fffd81c0000000

def z150 : W := mkw 0x0300000018000000 0x00c0000006000000 0x830000001c000002 0x20c0000007000000

def z151 : W := mkw 0x23eec0001b470000 0x08fbb00006d1c000 0xabfc00001ff60002 0x6aff000007fd8000

def z152 : W := mkw 0x27bb73037e7cc6f2 0x89eedcc0df9f31bc 0x9d33f707ec79cff3 0xe74cfdc1fb1e73fc

def z153 : W := mkw 0x244ff003652fc272 0x8913fc00d94bf09c 0x100ff007e00fc030 0x8403fc01f803f00c

def z154 : W := mkw 0x234fdc151d2faa2b 0x08d3f705474bea8a 0xd70ffe1f1c0ffe3f 0xb5c3ff87c703ff8f

def z155 : W := mkw 0x04113303443886a2 0x01044cc0d10e21a8 0x8d3377070c700fc3 0x634cddc1c31c03f0

def z156 : W := mkw 0x13ffffdec4288000 0x04fffff7b10a2000 0xfbffffffec79c003 0xfefffffffb1e7000

def z157 : W := mkw 0x245ff303653fc6f2 0x8917fcc0d94ff1bc 0x9d3ff707ec7fcff3 0xe74ffdc1fb1ff3fc

def z158 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x010306070c000e00 0x0040c181c3000380

def z159 : W := mkw 0x0000000020004050 0x8000000008001014 0x0c0000000009c1f2 0x030000000002707c

def z160 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xeec089e0f381f1c3 0x7bb022783ce07c70

def z161 : W := mkw 0x0000000020004050 0x8000000008001014 0xde0c8918f00ff1ff 0xf78322463c03fc7f

def z162 : W := mkw 0x034f8068bd8f5154 0xc0d3e01a2f63d455 0xffcf89f8ff8ff1ff 0xfff3e27e3fe3fc7f

def z163 : W := mkw 0x08a000a002c01100 0x0228002800b00440 0x20c000e003800000 0x0830003800e00000

def z164 : W := mkw 0x034e8c7cb987795d 0xc0d3a31f2e61de57 0xfecc89f8f38ff1ff 0xffb3227e3ce3fc7f

def z165 : W := mkw 0x0044806881831104 0x4011201a2060c441 0xf6cc08f8138e303f 0xbdb3023e04e38c0f

def z166 : W := mkw 0x13ffefdfdc0c2a2b 0x04fffbf7f7030a8a 0xf3ffffffec000e01 0xfcfffffffb000380

def z167 : W := mkw 0x13feeffec1831104 0x44ffbbffb060c441 0xf3fffffff386300d 0xfcfffffffce18c03

def z168 : W := mkw 0x0044800001030000 0x001120000040c000 0x000c8000000fc000 0x800320000003f000

def z169 : W := mkw 0x0000000000000000 0x0000000000000000 0x850006000c000e03 0x2140018003000380

def z170 : W := mkw 0x23efd0001e6c8000 0x08fbf400079b2000 0xa3fff0000c700000 0xe8fffc00031c0000

def z171 : W := mkw 0x20e5d0001f6f8000 0x0839740007dbe000 0x28f0f0001fffc002 0x4a3c3c0007fff000

def z172 : W := mkw 0x13bb6f975c0c2a2b 0x04eedbe5d7030a8a 0x013376070c000e00 0x004cdd81c3000380

def z173 : W := mkw 0x23efd0011f6faa2b 0x08fbf40047dbea8a 0xaffff0001ffffe3e 0xebfffc0007ffff8f

def z174 : W := mkw 0x0044804881030000 0x001120122040c000 0xfacc89f8f38fc003 0xfeb3227e3ce3f000

def z175 : W := mkw 0x10f4e3eae1835154 0xc43d38fab860d455 0x28f0f1e0e381c1c0 0x4a3c3c7838e07070

def z176 : W := mkw 0x0455b36be5bbd7f6 0xc1156cdaf96ef5fd 0xbdf3f7e7eff9cff3 0xef7cfdf9fbfe73fc

def z177 : W := mkw 0x0000002000801100 0x0000000800200440 0x28c001e0038001c0 0x4a30007800e00070

def z178 : W := mkw 0x00000c1500002a2b 0x0000030540000a8a 0x54000e1f00003e3d 0x15000387c0000f8f

def z179 : W := mkw 0x0ba00ca01ac03900 0x02e8032806b00e40 0x62c008e013803000 0x18b0023804e00c00

def z180 : W := mkw 0x00000068a0805154 0xc000001a28201455 0x540009f8e00031fd 0x1500027e38000c7f

def z181 : W := mkw 0x13eeccdc80000000 0x04fbb33720000000 0xf3cf0eff00000001 0xbcf3c3bfc0000000

def z182 : W := mkw 0x0010230240100480 0x000408c090040120 0x9d33f707ec700fc3 0xe74cfdc1fb1c03f0

def z183 : W := mkw 0x00000c1500002a2b 0x0000030540000a8a 0xd60c0e1f100e3e3f 0xb5830387c4038f8f

def z184 : W := mkw 0x030a0c1418042809 0x00c2830506010a02 0x0000000000000000 0x0000000000000000

def z185 : W := mkw 0x0001100104288222 0x00004400410a2088 0x9d33f6070c79ce33 0xe74cfd81c31e738c

def z186 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x72cc88f8f38ff03c 0x9cb3223e3ce3fc0f

def z187 : W := mkw 0x2beecca01bc73900 0x0afbb32806f1ce40 0x62cc08e013863000 0x18b3023804e18c00

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0xd60c0818100e303f 0xb583020604038c0f

def z189 : W := mkw 0x00100300201044d0 0x800400c008041134 0x9d308700ec79cff3 0xe74c21c03b1e73fc

def z190 : W := mkw 0x08b003a01ad03d80 0x022c00e806b40f60 0x2cf001e01ff03fc2 0x4b3c007807fc0ff0

def z191 : W := mkw 0x03b02f8240000000 0x00ec0be090000000 0xf3f3ffe7e0000001 0xfcfcfff9f8000000

def z192 : W := mkw 0x2bfecfa01bd73d80 0x0affb3e806f5cf60 0xeffc0fe01ff63fc3 0x7bff03f807fd8ff0

def z193 : W := mkw 0x0001000104080222 0x0000400041020088 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z194 : W := mkw 0x03efc0001c0c0000 0x00fbf00007030000 0xa3fff0001c0e0002 0xe8fffc0007038000

def z195 : W := mkw 0x03a110001e688000 0x00e84400079a2000 0xabf3f0001ff9c002 0xeafcfc0007fe7000

def z196 : W := mkw 0x10000cdc80000000 0x0400033720000000 0x400008f800000000 0x1000023e00000000

def z197 : W := mkw 0x08100fa01ad03d80 0x020403e806b40f60 0x4c000fe01ff03fc3 0x130003f807fc0ff0

def z198 : W := mkw 0x0054a34ac0000000 0x001528d2b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z199 : W := mkw 0x105ee35ec0000000 0x0417b8d7b0000000 0x913ff71fe0000001 0xe44ffdc7f8000000

def z200 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xc7030e071c003e03 0x31c0c381c7000f80

def z201 : W := mkw 0x1beeccfc9ac03900 0x06fbb33f26b00e40 0x62cc08f813803000 0x18b3023e04e00c00

def z202 : W := mkw 0x03ab0c151e4c2a2b 0x00eac30547930a8a 0xffff0e1f1ffe3e3f 0xffffc387c7ff8f8f

def z203 : W := mkw 0x23efc0001f4f0000 0x08fbf00007d3c000 0xa3cf00001f8e0002 0xa8f3c00007e38000

def z204 : W := mkw 0x034f8c7dbd8f7b7f 0xc0d3e31f6f63dedf 0xffcf8fffff8fffff 0xfff3e3ffffe3ffff

def z205 : W := mkw 0x13ba6f9640000000 0x04ee9be590000000 0x9133f707e0000001 0xe44cfdc1f8000000

def z206 : W := mkw 0x0ba00ca01ac03900 0x02e8032806b00e40 0xeec009e0138031c3 0x7bb0027804e00c70

def z207 : W := mkw 0x23efd0203fefd154 0xc8fbf4080ffbf455 0xaffff0001ffff1fe 0xebfffc0007fffc7f

def z208 : W := mkw 0x080000201ad03d80 0x0200000806b40f60 0xeec009e01ff03fc3 0x7bb0027807fc0ff0

def z209 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x45300fe00c703fc1 0x114c03f8031c0ff0

def z210 : W := mkw 0x13eeccdc80000000 0x04fbb33720000000 0x62cc08f800000000 0x18b3023e00000000

def z211 : W := mkw 0x10e4c0c880000000 0x0439303220000000 0x20c000e000000000 0x0830003800000000

def z212 : W := mkw 0x03eec00000000000 0x00fbb00000000000 0x22cc000000000000 0x08b3000000000000

def z213 : W := mkw 0x2bbb5f801e7cac80 0x0aeed7e0079f2b20 0x013376000c700e00 0x004cdd80031c0380

def z214 : W := mkw 0x0bb00fa01ac03900 0x02ec03e806b00e40 0xe3f00fe013803001 0x78fc03f804e00c00

def z215 : W := mkw 0x27efd0013f7fc6f2 0x89fbf4004fdff1bc 0xaffff0001fffcff2 0xebfffc0007fff3fc

def z216 : W := mkw 0x041113012438c6f2 0x810444c0490e31bc 0x8d3007000c79cff3 0x634c01c0031e73fc

def z217 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x29f3f0000ff1c000 0x4a7cfc0003fc7000

def z218 : W := mkw 0x13eeccdc98042809 0x04fbb33726010a02 0x62cc08f81006300c 0x18b3023e04018c03

def z219 : W := mkw 0x20a0500002608000 0x0828140000982000 0x0030700000700000 0x000c1c00001c0000

def z220 : W := mkw 0x23efd068bfefd154 0xc8fbf41a2ffbf455 0xabfff1e0ffffc1c2 0xeafffc783ffff070

def z221 : W := mkw 0x13feefded8002800 0x04ffbbf7b6000a00 0xf7fffffffc003e03 0xfdffffffff000f80

def z222 : W := mkw 0x204fd015052f822b 0x0813f405414be08a 0x100ff01f000fc03c 0x8403fc07c003f00f

def z223 : W := mkw 0x0001000104080222 0x0000400041020088 0x010306070c000e00 0x0040c181c3000380

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x880080000009c002 0xe200200000027000

def z225 : W := mkw 0x23efd0201fef9100 0x08fbf40807fbe440 0xeffff9e01ffff1c3 0xfbfffe7807fffc70

def z226 : W := mkw 0x33ffff965f6f8000 0x0cffffe597dbe000 0xabfff6071fffc002 0xeafffd81c7fff000

def z227 : W := mkw 0x0bb02fa25ad03d80 0x02ec0be896b40f60 0xfff3ffe7fff03fc3 0xfffcfff9fffc0ff0

def z228 : W := mkw 0x134fec5fdc0c2a2b 0x04d3fb17f7030a8a 0xd70ffe1ffc0e3e3f 0xb5c3ff87ff038f8f

def z229 : W := mkw 0x0000002000801100 0x0000000800200440 0xeec009e0138031c3 0x7bb0027804e00c70

def z230 : W := mkw 0x0000000021034054 0xc00000000840d015 0x00000000000fc03c 0x000000000003f00f

def z231 : W := mkw 0x080100211edc3fab 0x0200400847b70fea 0x0c0000001ffe3ffe 0x0300000007ff8fff

def z232 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x21f3f7e7e0000000 0x487cfdf9f8000000

def z233 : W := mkw 0x23efd0003f6fc050 0x88fbf4000fdbf014 0xbffff100ffffc1f3 0xeffffc403ffff07c

def z234 : W := mkw 0x04102302601044d0 0x810408c098041134 0x00000100e00001c0 0x0000004038000070

def z235 : W := mkw 0x030b1c151c2caa2b 0x00c2c705470b2a8a 0xdf3ffe1f1c7ffe3f 0xf7cfff87c71fff8f

def z236 : W := mkw 0x075fbf7ffdbfffff 0xc1d7efdfff6fffff 0xffffffffffffffff 0xffffffffffffffff

def z237 : W := mkw 0x04011001043886a2 0x01004400410e21a8 0x000000000c700e00 0x00000000031c0380

def z238 : W := mkw 0x13f4efcac0000000 0x04fd3bf2b0000000 0xe3f0ffe0e0000001 0x78fc3ff838000000

def z239 : W := mkw 0x03eecc1400000000 0x00fbb30500000000 0xf3fffe1f00000001 0xfcffff87c0000000

def z240 : W := mkw 0x070b3c177c2cea7b 0x81c2cf05df0b3a9e 0xd70ffe1ffc0ffe3f 0xb5c3ff87ff03ff8f

def z241 : W := mkw 0x0001100004288000 0x00004400010a2000 0x080000000c79c002 0x02000000031e7000

def z242 : W := mkw 0x0000002021835154 0xc00000080860d455 0xeec009e0138ff1ff 0x7bb0027804e3fc7f

def z243 : W := mkw 0x23ab50001f6f8000 0x08ead40007dbe000 0x093370001fffc002 0x024cdc0007fff000

def z244 : W := mkw 0x000a001400000000 0x0002800500000000 0x100f001f00000000 0x8403c007c0000000

def z245 : W := mkw 0x23ab5c151e6caa2b 0x08ead705479b2a8a 0xd73f7e1f1c7e3e3f 0xb5cfdf87c71f8f8f

def z246 : W := mkw 0x034f8c5d9c0c2a2b 0x00d3e31767030a8a 0xf7cf8ffffc0e3e3f 0xfdf3e3ffff038f8f

def z247 : W := mkw 0x23eecc141b472809 0x08fbb30506d1ca02 0x62cc08181386300c 0x18b3020604e18c03

def z248 : W := mkw 0x041133036428c272 0x81044cc0d90a309c 0x9133f707e009c031 0xe44cfdc1f802700c

def z249 : W := mkw 0x2bb11fa01fffbd80 0x0aec47e807ffef60 0xeff00fe01fffffc3 0x7bfc03f807fffff0

def z250 : W := mkw 0x23ab50001e6c8000 0x08ead400079b2000 0x8933f0000c79c002 0xe24cfc00031e7000

def z251 : W := mkw 0x0010030000000000 0x000400c000000000 0x8130070000000001 0x604c01c000000000

def z252 : W := mkw 0x04113303443886a2 0x01044cc0d10e21a8 0x013376070c700e00 0x004cdd81c31c0380

def z253 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x113ff61fe0000000 0x844ffd87f8000000

def z254 : W := mkw 0x0044804880000000 0x0011201220000000 0x100c8018e0000000 0x8403200638000000

def z255 : W := mkw 0x1bfeeffec2d01580 0x06ffbbffb0b40560 0xfbffffffe3f001c1 0xfefffffff8fc0070

def z256 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x430f0e1f1c063e0c 0x10c3c387c7018f83

def z257 : W := mkw 0x041b3317643cc6fb 0x8106ccc5d90f31be 0x9d3ff71fec7fcfff 0xe74ffdc7fb1ff3ff

def z258 : W := mkw 0x30f4f3cac3638000 0x0c3d3cf2b0d8e000 0x28f0f1e0e3f1c000 0x4a3c3c7838fc7000

def z259 : W := mkw 0x04102303601046f2 0x810408c0d80411bc 0x9533f707e0000ff1 0xe54cfdc1f80003fc

def z260 : W := mkw 0x27fff3027f7fc4d0 0x89fffcc09fdff134 0xabfff100ffffc1c2 0xeafffc403ffff070

def z261 : W := mkw 0x13feefdec0100480 0x04ffbbf7b0040120 0xffffffffec700fc3 0xfffffffffb1c03f0

def z262 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xfffff8181ffff03f 0xfffffe0607fffc0f

def z263 : W := mkw 0x27fff3035f7f86a2 0x09fffcc0d7dfe1a8 0xabfff6071fffce02 0xeafffd81c7fff380

def z264 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x76cc09f8f38631fd 0x1db3027e3ce18c7f

def z265 : W := mkw 0x0044804880000000 0x0011201220000000 0xf6cc89f8f00e303f 0xfdb3227e3c038c0f

def z266 : W := mkw 0x2bffdfb51fffbfab 0x0afff7ed47ffefea 0xffffffff1fffffff 0xffffffffc7ffffff

def z267 : W := mkw 0x10102f9640000000 0x04040be590000000 0x0000060700000000 0x00000181c0000000

def z268 : W := mkw 0x0bbb0f951e5c2eab 0x02eec3e547970baa 0x013306070c700e00 0x004cc181c31c0380

def z269 : W := mkw 0x03ba0f9400000000 0x00ee83e500000000 0xf3ff0fff00000001 0xfcffc3ffc0000000

def z270 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x520f081f100e303c 0x9483c207c4038c0f

def z271 : W := mkw 0x0c0110213ef8fff2 0x830044084fbe3ffc 0x0c0000001ff9fff2 0x0300000007fe7ffc

def z272 : W := mkw 0x03a00c8000000000 0x00e8032000000000 0x62c008e000000000 0x18b0023800000000

def z273 : W := mkw 0x230b10001f6f8000 0x08c2c40007dbe000 0x8b0f00001fffc002 0xa2c3c00007fff000

def z274 : W := mkw 0x1bb02ffedad03d80 0x06ec0bffb6b40f60 0xfff00ffffff03fc3 0x7ffc03fffffc0ff0

def z275 : W := mkw 0x0010230240000000 0x000408c090000000 0x0133760700000000 0x004cdd81c0000000

def z276 : W := mkw 0x030b0c1504080222 0x00c2c30541020088 0xd70f0e1f0c080e33 0xb5c3c387c302038c

def z277 : W := mkw 0x2bffdfe8bffffdd4 0xcafff7fa2fffff75 0xfffffff8ffffffff 0xfffffffe3fffffff

def z278 : W := mkw 0x13bb6f975c0c2a2b 0x04eedbe5d7030a8a 0xd73f7e1f1c0e3e3f 0xb5cfdf87c7038f8f

def z279 : W := mkw 0x071b3f175c3caeab 0x01c6cfc5d70f2baa 0x013376070c700e00 0x004cdd81c31c0380

def z280 : W := mkw 0x2044d00001238000 0x081134000048e000 0x0000f0000001c000 0x00003c0000007000

def z281 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x72cc0fffe0000001 0x1cb303fff8000000

def z282 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf7fffffff00e303f 0xfdfffffffc038c0f

def z283 : W := mkw 0x040110012438c6f2 0x81004400490e31bc 0x9c008100ec79cff3 0xe70020403b1e73fc

def z284 : W := mkw 0x10f4e3eae1835154 0xc43d38fab860d455 0xfefcf9f8f38ff1ff 0xffbf3e7e3ce3fc7f

def z285 : W := mkw 0x0c113fa364b8fff2 0x83044fe8d92e3ffc 0xdd33ffe7ec79fff3 0xf74cfff9fb1e7ffc

def z286 : W := mkw 0x0b100fa018903d80 0x02c403e806240f60 0xc7000fe01c003fc3 0x31c003f807000ff0

def z287 : W := mkw 0x131a2fdec0000000 0x04c68bf7b0000000 0xd30f0fffe0000001 0xb4c3c3fff8000000

def z288 : W := mkw 0x0445b06be5abd376 0xc1116c1af96af4dd 0xfecff9fff38ff1ff 0xffb3fe7ffce3fc7f

def z289 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x0d3376070c79cff2 0x034cdd81c31e73fc

def z290 : W := mkw 0x03a00c001a402800 0x00e8030006900a00 0xeff00e001ff03e03 0x7bfc038007fc0f80

def z291 : W := mkw 0x33efdcdc9f6f8000 0x0cfbf73727dbe000 0xebfff8f81fffc002 0xfafffe3e07fff000

def z292 : W := mkw 0x04113303443886a2 0x01044cc0d10e21a8 0x953376070c780e33 0xa54cdd81c31e038c

def z293 : W := mkw 0x03000c0018002800 0x00c0030006000a00 0x010006000c000e00 0x0040018003000380

def z294 : W := mkw 0x13feeffee0805154 0xc4ffbbffb8201455 0xf7ffffffe00031fd 0xfdfffffff8000c7f

def z295 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x460c08181c0e3e3e 0x1183020607038f8f

def z296 : W := mkw 0x17ffffffe5bbd7f6 0xc5fffffff96ef5fd 0xffffffffffffffff 0xffffffffffffffff

def z297 : W := mkw 0x0411332364b8d7f2 0x81044cc8d92e35fc 0xfff3ffe7fff9fff3 0xfffcfff9fffe7ffc

def z298 : W := mkw 0x030b00011c0c2a2b 0x00c2c00047030a8a 0x870f00001c0e3e3e 0xa1c3c00007038f8f

def z299 : W := mkw 0x2bbb5fa01efcbd80 0x0aeed7e807bf2f60 0xeff37fe01ff03fc3 0x7bfcdff807fc0ff0

def z300 : W := mkw 0x030a0c1400000000 0x00c2830500000000 0xd30f0e1f00000001 0xb4c3c387c0000000

def z301 : W := mkw 0x20e4c00003430000 0x0839300000d0c000 0x20c0000003800000 0x0830000000e00000

def z302 : W := mkw 0x13eeecdec0000000 0x04fbbb37b0000000 0x72cff8ffe0000000 0x9cb3fe3ff8000000

def z303 : W := mkw 0x0000000000000000 0x0000000000000000 0x8133f00000000000 0xe04cfc0000000000

def z304 : W := mkw 0x03efd00004288000 0x00fbf400010a2000 0xabfff0000c79c002 0xeafffc00031e7000

def z305 : W := mkw 0x04459069a5bbd7f6 0xc111641a696ef5fd 0xfecc89f8ffffffff 0xffb3227e3fffffff

def z306 : W := mkw 0x0044800001030000 0x001120000040c000 0x28c080000381c000 0x4a30200000e07000

def z307 : W := mkw 0x000b0015040c022b 0x0002c0054103008a 0x0003000700000000 0x0000c001c0000000

def z308 : W := mkw 0x0000000000000000 0x0000000000000000 0x8c000100000001c3 0x6300004000000070

def z309 : W := mkw 0x07b133037e78c6f2 0x81ec4cc0df9e31bc 0xbff3f707fff9cff3 0xeffcfdc1fffe73fc

def z310 : W := mkw 0x13feeffec0801100 0x04ffbbffb0200440 0xfffffffff38031c3 0xfffffffffce00c70

def z311 : W := mkw 0x040030026020c050 0x81000c0098083014 0x0000f000e001c000 0x00003c0038007000

def z312 : W := mkw 0x000b0000040c0000 0x0002c00001030000 0x000f0000000e0000 0x8003c00000038000

def z313 : W := mkw 0x004f807da58f537f 0xc013e01f6963d4df 0xfecf89fff38ff1ff 0xffb3e27ffce3fc7f

def z314 : W := mkw 0x23efd0151f6f822b 0x08fbf40547dbe08a 0xbbfff01f1fffc03e 0xeefffc07c7fff00f

def z315 : W := mkw 0x00448048a1034054 0xc01120122840d015 0xd60c8818f00ff03f 0xb58322063c03fc0f

def z316 : W := mkw 0x20011000052f8000 0x08004400014be000 0x00000000000fc000 0x000000000003f000

def z317 : W := mkw 0x0000002020805154 0xc000000808201455 0x04000000000031fc 0x0100000000000c7f

def z318 : W := mkw 0x0011130004388480 0x000444c0010e2120 0x8d33f7000c79cfc3 0xe34cfdc0031e73f0

def z319 : W := mkw 0x23efd0689fef9104 0x48fbf41a27fbe441 0xebfff8f81ffff00e 0xfafffe3e07fffc03

def z320 : W := mkw 0x23e4d0001b638000 0x08f9340006d8e000 0xabf0f0001ff1c002 0x6afc3c0007fc7000

def z321 : W := mkw 0x03010c011c082a22 0x00c0430047020a88 0xd7030e071c083e33 0xb5c0c381c7020f8c

def z322 : W := mkw 0x030a0c1518042a2b 0x00c2830546010a8a 0x560c0e1f10063e3d 0x15830387c4018f8f

def z323 : W := mkw 0x030b00001c0c0000 0x00c2c00007030000 0xd70f08181c0e303f 0xb5c3c20607038c0f

def z324 : W := mkw 0x040010002030c4d0 0x81000400080c3134 0x080000000071c1c0 0x02000000001c7070

def z325 : W := mkw 0x14f5f3cbe438c6f2 0x853d7cf2f90e31bc 0xbdf3f7e7ec79cff3 0xef7cfdf9fb1e73fc

def z326 : W := mkw 0x00000068a0805154 0xc000001a28201455 0xfec009f8f38031ff 0x7fb0027e3ce00c7f

def z327 : W := mkw 0x07fff3036438c6f2 0x81fffcc0d90e31bc 0xbffff707ec79cff3 0xeffffdc1fb1e73fc

def z328 : W := mkw 0x0001000124084272 0x800040004902109c 0x9d038707ec09cff3 0xe740e1c1fb0273fc

def z329 : W := mkw 0x0000000020004050 0x8000000008001014 0x08008100e001c1c0 0x4200204038007070

def z330 : W := mkw 0x23efd048bf6fc054 0xc8fbf4122fdbf015 0xbbfff018ffffc03e 0xeefffc063ffff00f

def z331 : W := mkw 0x20efd000076f8000 0x083bf40001dbe000 0x28fff00003ffc000 0xca3ffc0000fff000

def z332 : W := mkw 0x0bbb0fa01edc3d80 0x02eec3e807b70f60 0xefff0fe01ffe3fc3 0xfbffc3f807ff8ff0

def z333 : W := mkw 0x03e48068bbc35154 0xc0f9201a2ef0d455 0xfffc89f8fffff1ff 0xffff227e3ffffc7f

def z334 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x55030e1f0c003e3d 0x1540c387c3000f8f

def z335 : W := mkw 0x20e4d068a3e3d154 0xc839341a28f8f455 0x28f0f1e0e3f1c1c0 0x4a3c3c7838fc7070

def z336 : W := mkw 0x14113fdfe438c6f2 0x85044ff7f90e31bc 0xdd33ffffec79cff3 0xf74cfffffb1e73fc

def z337 : W := mkw 0x030b00001c0c0000 0x00c2c00007030000 0x830f00001c0e0002 0xa0c3c00007038000

def z338 : W := mkw 0x1bfeeffedac03900 0x06ffbbffb6b00e40 0xf3fffffff3803001 0xfcfffffffce00c00

def z339 : W := mkw 0x0044806881831104 0x4011201a2060c441 0xf2cc89f8f386300d 0xfcb3227e3ce18c03

def z340 : W := mkw 0x0fb11fa13ef8fff2 0x83ec47e84fbe3ffc 0xeff00fe01ff9fff3 0x7bfc03f807fe7ffc

def z341 : W := mkw 0x131b2fdfdc0c2a2b 0x04c6cbf7f7030a8a 0xd70f0ffffc0e3e3f 0xb5c3c3ffff038f8f

def z342 : W := mkw 0x23efd0011f6f8222 0x08fbf40047dbe088 0xbffff6071fffce33 0xeffffd81c7fff38c

def z343 : W := mkw 0x0010230240000000 0x000408c090000000 0x0030f100e0000000 0x400c3c4038000000

def z344 : W := mkw 0x0011230344080222 0x000448c0d1020088 0x9533f707ec080e33 0xe54cfdc1fb02038c

def z345 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x050306071c0e3e3e 0x0140c181c7038f8f

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z347 : W := mkw 0x14102fdfe01046f2 0x85040bf7f80411bc 0x54000fffe0000ff1 0x150003fff80003fc

def z348 : W := mkw 0x0fb13fa35ef8bfa2 0x03ec4fe8d7be2fe8 0xeff37fe71ff03fc3 0x7bfcdff9c7fc0ff0

def z349 : W := mkw 0x13eeccdc80000000 0x04fbb33720000000 0xf2cc89f8e0000001 0xfcb3227e38000000

def z350 : W := mkw 0x03000c0000000000 0x00c0030000000000 0xc3000e0000000001 0x30c0038000000000

def z351 : W := mkw 0x0cb133a366f8d7f2 0x832c4ce8d9be35fc 0xbdf3f7e7eff9cff3 0xef7cfdf9fbfe73fc

def z352 : W := mkw 0x33ffffdfdf6faa2b 0x0cfffff7f7dbea8a 0xfffffffffffffe3f 0xffffffffffffff8f

def z353 : W := mkw 0x08548fe8a1937dd4 0xc21523fa2864df75 0xfecc8ff8f38fffff 0xffb323fe3ce3ffff

def z354 : W := mkw 0x071b3f175c3caeab 0x01c6cfc5d70f2baa 0xd73f7e1f1c7e3e3f 0xb5cfdf87c71f8f8f

def z355 : W := mkw 0x08b003a002d01580 0x022c00e800b40560 0xadf007e00ff00fc3 0x6b7c01f803fc03f0

def z356 : W := mkw 0x08448068bbd37dd4 0xc211201a2ef4df75 0xfecc89f8ffffffff 0xffb3227e3fffffff

def z357 : W := mkw 0x0044802001831100 0x001120080060c440 0xeecc89e0138ff1c3 0xfbb3227804e3fc70

def z358 : W := mkw 0x200b5000042c8000 0x0802d400010b2000 0x0003700000000000 0x0000dc0000000000

def z359 : W := mkw 0x0044800000000000 0x0011200000000000 0xa2cc800000000000 0xe8b3200000000000

def z360 : W := mkw 0x10f4e3cac0000000 0x043d38f2b0000000 0xb1f3f7e7e0000001 0xec7cfdf9f8000000

def z361 : W := mkw 0x0bb00fb51ad03fab 0x02ec03ed46b40fea 0xfff00fff1ff03fff 0x7ffc03ffc7fc0fff

def z362 : W := mkw 0x33feefdedb470000 0x0cffbbf7b6d1c000 0xf3fffffff3860001 0xfcfffffffce18000

def z363 : W := mkw 0x040130036438c6f2 0x81004c00d90e31bc 0x1c03f007ec79cff2 0x8700fc01fb1e73fc

def z364 : W := mkw 0x0fbb3fb77efcfffb 0x83eecfeddfbf3ffe 0xffffffffffffffff 0xffffffffffffffff

def z365 : W := mkw 0x00000c1400000000 0x0000030500000000 0x50000e1f00000001 0x14000387c0000000

def z366 : W := mkw 0x03eec0001a400000 0x00fbb00006900000 0xabfff0001ff00002 0xeafffc0007fc0000

def z367 : W := mkw 0x204fd000052f8000 0x0813f400014be000 0x893ff0000c7fc002 0xe24ffc00031ff000

def z368 : W := mkw 0x145ff35fe438c6f2 0x8517fcd7f90e31bc 0x9d3ff71fec79cff3 0xe74ffdc7fb1e73fc

def z369 : W := mkw 0x03a000001a400000 0x00e8000006900000 0x013000000c700000 0x004c0000031c0000

def z370 : W := mkw 0x0bba0fb41ad43d89 0x02ee83ed06b50f62 0xeffc0ff81ff63fcf 0x7bff03fe07fd8ff3

def z371 : W := mkw 0x104fe05fc40c022b 0x0413f817f103008a 0x100ff01fe00e003c 0x8403fc07f803800f

def z372 : W := mkw 0x00000068a0805154 0xc000001a28201455 0xd60c09f8f00e31ff 0xb583027e3c038c7f

def z373 : W := mkw 0x204fd0001f6f8000 0x0813f40007dbe000 0x080ff0001fffc002 0x8203fc0007fff000

def z374 : W := mkw 0x33eff05edf6f8000 0x0cfbfc17b7dbe000 0xbbfff01fffffc002 0xeefffc07fffff000

def z375 : W := mkw 0x0000000000000000 0x0000000000000000 0x9400000000080033 0xa50000000002000c

def z376 : W := mkw 0x0be48ce89bc33904 0x42f9233a26f0ce41 0x62cc08f81386300c 0x18b3023e04e18c03

def z377 : W := mkw 0x33ffffdede6c8000 0x0cfffff7b79b2000 0xf3ffffffec700001 0xfcfffffffb1c0000

def z378 : W := mkw 0x00000c1400002809 0x0000030500000a02 0x400008180000300c 0x1000020600000c03

def z379 : W := mkw 0x0000000100002a2b 0x0000000040000a8a 0x0400000000003e3c 0x0100000000000f8f

def z380 : W := mkw 0x2000100003638000 0x0800040000d8e000 0x0800000003f1c000 0x0200000000fc7000

def z381 : W := mkw 0x00010c1504082a2b 0x0000430541020a8a 0xd5030e1f0c083e3f 0xb540c387c3020f8f

def z382 : W := mkw 0x03f48fe8a1835154 0xc0fd23fa2860d455 0xfffc8ff8f38ff1ff 0xffff23fe3ce3fc7f

def z383 : W := mkw 0x071b3f177c3ceefb 0x81c6cfc5df0f3bbe 0x9d33f707ec79cff3 0xe74cfdc1fb1e73fc

def z384 : W := mkw 0x0010230260004050 0x800408c098001014 0x9d33f707e009c1f3 0xe74cfdc1f802707c

def z385 : W := mkw 0x104ee05ee1034054 0xc413b817b840d015 0x100ff01fe00fc03c 0x8403fc07f803f00f

def z386 : W := mkw 0x23ab5c151e6caa2b 0x08ead705479b2a8a 0x013376070c700e00 0x004cdd81c31c0380

def z387 : W := mkw 0x1bba6f965a502c80 0x06ee9be596940b20 0x013376070c700e00 0x004cdd81c31c0380

def z388 : W := mkw 0x204fd000052f8000 0x0813f400014be000 0xaacff000138fc002 0xeab3fc0004e3f000

def z389 : W := mkw 0x03010c011c0c2a2b 0x00c0430047030a8a 0xc7000e001c0e3e3f 0x31c0038007038f8f

def z390 : W := mkw 0x0000000000000000 0x0000000000000000 0x540008180000303d 0x1500020600000c0f

def z391 : W := mkw 0x0bbb0f951e5c2eab 0x02eec3e547970baa 0xd73f0e1f1c7e3e3f 0xb5cfc387c71f8f8f

def z392 : W := mkw 0x13ba6fdec0000000 0x04ee9bf7b0000000 0x51337fffe0000001 0x144cdffff8000000

def z393 : W := mkw 0x2bffd3a01fff9580 0x0afff4e807ffe560 0xabfff1e01fffc1c2 0xeafffc7807fff070

def z394 : W := mkw 0x0010030000100480 0x000400c000040120 0x0400070000000fc1 0x010001c0000003f0

def z395 : W := mkw 0x204ec00001070000 0x0813b0000041c000 0x000c000000060000 0x0003000000018000

def z396 : W := mkw 0x33fffffeffefd154 0xccffffffbffbf455 0xfffffffffffff1ff 0xfffffffffffffc7f

def z397 : W := mkw 0x04113303443886a2 0x01044cc0d10e21a8 0x8933f6070c79ce02 0xe24cfd81c31e7380

def z398 : W := mkw 0x000a001400040009 0x0002800500010002 0x000c00180006000c 0x0003000600018003

def z399 : W := mkw 0x20e5d000076b8000 0x0839740001dae000 0xa9f3f0000ff9c002 0xea7cfc0003fe7000

def z400 : W := mkw 0x071b3f176438c6f2 0x81c6cfc5d90e31bc 0xdf3fff1fec79cff3 0xf7cfffc7fb1e73fc

def z401 : W := mkw 0x000b0015040c022b 0x0002c0054103008a 0x950f061f0c0e0e3f 0xa543c187c303838f

def z402 : W := mkw 0x23efdc141f6fa809 0x08fbf70507dbea02 0xebfff8181ffff00e 0xfafffe0607fffc03

def z403 : W := mkw 0x0054a36ae1835154 0xc01528dab860d455 0xfffffffff38ff1ff 0xfffffffffce3fc7f

def z404 : W := mkw 0x17ffffdfc43886a2 0x05fffff7f10e21a8 0xf3ffffffec700e01 0xfcfffffffb1c0380

def z405 : W := mkw 0x080000201ac03900 0x0200000806b00e40 0x0000000013803000 0x0000000004e00c00

def z406 : W := mkw 0x200110001f6f8000 0x0800440007dbe000 0x8933f0001fffc002 0xe24cfc0007fff000

def z407 : W := mkw 0x23ffdf801f6f8000 0x08fff7e007dbe000 0xebffffe01fffc003 0xfafffff807fff000

def z408 : W := mkw 0x004ec00000000000 0x0013b00000000000 0x000ff00000000000 0x8003fc0000000000

def z409 : W := mkw 0x23eed0001b678000 0x08fbb40006d9e000 0x2afcf00013f7c000 0x4abf3c0004fdf000

def z410 : W := mkw 0x37ffffdfff7fc6f2 0x8dfffff7ffdff1bc 0xffffffffffffcff3 0xfffffffffffff3fc

def z411 : W := mkw 0x240110013f7fc6f2 0x890044004fdff1bc 0x0c0000001fffcff2 0x0300000007fff3fc

def z412 : W := mkw 0x034f80001d0f0000 0x00d3e0000743c000 0xabcf80001f8fc002 0xeaf3e00007e3f000

def z413 : W := mkw 0x08100f8000102c80 0x020403e000040b20 0x0000060000000e00 0x0000018000000380

def z414 : W := mkw 0x00010001040c022b 0x000040004103008a 0x00000000000e003c 0x000000000003800f

def z415 : W := mkw 0x0be48ce8bbc37954 0xc2f9233a2ef0de55 0xfecc89f8f38ff1ff 0xffb3227e3ce3fc7f

def z416 : W := mkw 0x13fee3cac0000000 0x04ffb8f2b0000000 0xa3fff1e0e0000000 0xe8fffc7838000000

def z417 : W := mkw 0x08f483e8a3d355d4 0xc23d20fa28f4d575 0x28f081e0e3f1c1c0 0x4a3c207838fc7070

def z418 : W := mkw 0x080000001a502c80 0x0200000006940b20 0x000000000c700e00 0x00000000031c0380

def z419 : W := mkw 0x13feefded8042809 0x04ffbbf7b6010a02 0xf3fffffff006300d 0xfcfffffffc018c03

def z420 : W := mkw 0x0baa0cb41ac43909 0x02ea832d06b10e42 0x62cc08f81386300c 0x18b3023e04e18c03

def z421 : W := mkw 0x00448048a1034054 0xc01120122840d015 0xbacc8018f38fc03e 0xeeb320063ce3f00f

def z422 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x29f007e00ff00fc0 0x4a7c01f803fc03f0

def z423 : W := mkw 0x0bf48fe89ad03d80 0x02fd23fa26b40f60 0xfffc8ff8fff03fc3 0xffff23fe3ffc0ff0

def z424 : W := mkw 0x0bb00fe8bad07dd4 0xc2ec03fa2eb41f75 0xfff00ff8fff03fff 0x7ffc03fe3ffc0fff

def z425 : W := mkw 0x17feffdee030c4d0 0x85ffbff7b80c3134 0xfbffffffe071c1c1 0xfefffffff81c7070

def z426 : W := mkw 0x0000002021835154 0xc00000080860d455 0x080000000381c1c0 0x0200000000e07070

def z427 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0xaafcf00013ffc002 0xeabf3c0004fff000

def z428 : W := mkw 0x0455b34be53bc6f6 0xc1156cd2f94ef1bd 0x9d3ff71fec7fcfff 0xe74ffdc7fb1ff3ff

def z429 : W := mkw 0x0bb00f801a502c80 0x02ec03e006940b20 0xe3f00fe00c700e01 0x78fc03f8031c0380

def z430 : W := mkw 0x00000c0000002800 0x0000030000000a00 0x44000e0000003e01 0x1100038000000f80

def z431 : W := mkw 0x2befdca01fefb900 0x0afbf72807fbee40 0xebfff8e01ffff002 0xfafffe3807fffc00

def z432 : W := mkw 0x00448048a1034054 0xc01120122840d015 0xf2cc89f8e00fc03d 0xfcb3227e3803f00f

def z433 : W := mkw 0x000110002428c050 0x80004400090a3014 0x9d33f100ec79c1f3 0xe74cfc403b1e707c

def z434 : W := mkw 0x0fb03fa27af0fdd0 0x83ec0fe89ebc3f74 0xeff0ffe0fff1ffc3 0x7bfc3ff83ffc7ff0

def z435 : W := mkw 0x0800002002d01580 0x0200000800b40560 0x0800000003f001c0 0x0200000000fc0070

def z436 : W := mkw 0x101023cac0000000 0x040408f2b0000000 0x000001e0e0000000 0x0000007838000000

def z437 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x15337707ec700ff1 0x054cddc1fb1c03fc

def z438 : W := mkw 0x04113f176438eefb 0x81044fc5d90e3bbe 0xdd33ff1fec79ffff 0xf74cffc7fb1e7fff

def z439 : W := mkw 0x030a0c1500002a2b 0x00c2830540000a8a 0xd70f0e1f00003e3d 0xb5c3c387c0000f8f

def z440 : W := mkw 0x13feeffee1835154 0xc4ffbbffb860d455 0xfbffffffe381c1c1 0xfefffffff8e07070

def z441 : W := mkw 0x0044804880000000 0x0011201220000000 0x62cc08f800000000 0x18b3023e00000000

def z442 : W := mkw 0x03b00f8000000000 0x00ec03e000000000 0x0130060000000000 0x004c018000000000

def z443 : W := mkw 0x1044e04ac0000000 0x04113812b0000000 0x0000f000e0000000 0x00003c0038000000

def z444 : W := mkw 0x0bb00fa002d01580 0x02ec03e800b40560 0xebf00fe003f001c1 0x7afc03f800fc0070

def z445 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x0933f707ec71cfc0 0x424cfdc1fb1c73f0

def z446 : W := mkw 0x00458069a58b5376 0xc011601a6962d4dd 0xffcf8fffff8fffff 0xfff3e3ffffe3ffff

def z447 : W := mkw 0x0bb10fa11ed83fa2 0x02ec43e847b60fe8 0xfff30fe71ff83ff3 0xfffcc3f9c7fe0ffc

def z448 : W := mkw 0x27fff36bffffd7f6 0xc9fffcdafffff5fd 0xffffffffffffffff 0xffffffffffffffff

def z449 : W := mkw 0x031b2f175c0c2a2b 0x00c6cbc5d7030a8a 0xd73fff1ffc0e3e3f 0xf5cfffc7ff038f8f

def z450 : W := mkw 0x1bffefffdedc3fab 0x06fffbfff7b70fea 0xfffffffffffe3fff 0xffffffffffff8fff

def z451 : W := mkw 0x00000068a0805154 0xc000001a28201455 0x000001e0e00001c0 0x0000007838000070

def z452 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x0c30f100ec79cff2 0x430c3c403b1e73fc

def z453 : W := mkw 0x104ee05ec0000000 0x0413b817b0000000 0xf2cff9ffe0000001 0xfcb3fe7ff8000000

def z454 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xbcc081e0e389c1f3 0xef30207838e2707c

def z455 : W := mkw 0x0044804880000000 0x0011201220000000 0x20c081e0e0000000 0x4830207838000000

def z456 : W := mkw 0x0001000104080222 0x0000400041020088 0x1003000700080030 0x8400c001c002000c

def z457 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x013ff0000c7fc000 0x804ffc00031ff000

def z458 : W := mkw 0x20459068bfefd154 0xc811641a2ffbf455 0xfecc89f8fffff1ff 0xffb3227e3ffffc7f

def z459 : W := mkw 0x041133026438c4d0 0x81044cc0990e3134 0x8933f100ec79c1c2 0xe24cfc403b1e7070

def z460 : W := mkw 0x00548368a19355d4 0xc01520da2864d575 0xfffc8ff8ffffffff 0xffff23fe3fffffff

def z461 : W := mkw 0x031b0f151c1c2eab 0x00c6c3c547070baa 0xdf3f0f1f1c7e3fff 0xf7cfc3c7c71f8fff

def z462 : W := mkw 0x030b00011c0c0222 0x00c2c00047030088 0x970f06071c0e0e33 0xa5c3c181c703838c

def z463 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x7cc089f8e381f1fd 0x5f30227e38e07c7f

def z464 : W := mkw 0x0454a36be19357f6 0xc11528daf864d5fd 0xfecc8ffff38fffff 0xffb323fffce3ffff

def z465 : W := mkw 0x0044806880801100 0x0011201a20200440 0xfecc89f8f38031c3 0xffb3227e3ce00c70

def z466 : W := mkw 0x144ff05fe428c272 0x8513fc17f90a309c 0x100ff01fe009c030 0x8403fc07f802700c

def z467 : W := mkw 0x00459068a5abd154 0xc011641a296af455 0xfffff9f8fffff1ff 0xfffffe7e3ffffc7f

def z468 : W := mkw 0x23aa40001a440000 0x08ea900006910000 0x0000000000000000 0x0000000000000000

def z469 : W := mkw 0x0000006880801104 0x4000001a20200441 0x400008f80000300c 0x1000023e00000c03

def z470 : W := mkw 0x23efd000052f8000 0x08fbf400014be000 0xa3fff000000fc000 0xe8fffc000003f000

def z471 : W := mkw 0x034f8c7d9d8f3b2f 0x40d3e31f6763cecb 0xf7cf0eff1f8e3e3f 0xbdf3c3bfc7e38f8f

def z472 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x22cff000138fc000 0x88b3fc0004e3f000

def z473 : W := mkw 0x000100011c0c2a2b 0x0000400047030a8a 0x000000000c000e00 0x0000000003000380

def z474 : W := mkw 0x0011330244288000 0x00044cc0910a2000 0x9933f707ec79c003 0xe64cfdc1fb1e7000

def z475 : W := mkw 0x03448c68b9837954 0xc0d1231a2e60de55 0xffcc8ff8ff8fffff 0xfff323fe3fe3ffff

def z476 : W := mkw 0x00e4c00000000000 0x0039300000000000 0x20f0f00000000000 0x483c3c0000000000

def z477 : W := mkw 0x034e8c7ca1835154 0xc0d3a31f2860d455 0xffcf8ffff38ff1ff 0xfff3e3fffce3fc7f

def z478 : W := mkw 0x10102fdfc0002a2b 0x04040bf7f0000a8a 0x54000fffe0003e3d 0x150003fff8000f8f

def z479 : W := mkw 0x23fff3025f6f8000 0x08fffcc097dbe000 0xbbfff707ffffc003 0xeefffdc1fffff000

def z480 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x2acc00001fffc002 0x0ab3000007fff000

def z481 : W := mkw 0x1bfeeffec0903d80 0x06ffbbffb0240f60 0xf7ffffffe0003fc1 0xfdfffffff8000ff0

def z482 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xabfff6071fffce02 0xeafffd81c7fff380

def z483 : W := mkw 0x1bfeefdeda502c80 0x06ffbbf7b6940b20 0xf3ffffffec700e01 0xfcfffffffb1c0380

def z484 : W := mkw 0x23efdc7dbfeffb7f 0xc8fbf71f6ffbfedf 0xffffffffffffffff 0xffffffffffffffff

def z485 : W := mkw 0x1ffffffffef8fff2 0x87ffffffffbe3ffc 0xfffffffffff9fff3 0xfffffffffffe7ffc

def z486 : W := mkw 0x10b0638240000000 0x042c18e090000000 0x0030700000000000 0x000c1c0000000000

def z487 : W := mkw 0x23eec0001b470000 0x08fbb00006d1c000 0xaacc8000138fc002 0xeab3200004e3f000

def z488 : W := mkw 0x0ba00ca01ac03900 0x02e8032806b00e40 0xe7c00ee01f803e03 0x39f003b807e00f80

def z489 : W := mkw 0x030b00151c0c022b 0x00c2c0054703008a 0x930f001f1c0e003e 0xa4c3c007c703800f

def z490 : W := mkw 0x0000000020004050 0x8000000008001014 0x14000100e00001f1 0x050000403800007c

def z491 : W := mkw 0x071b2f177c1c6efb 0x81c6cbc5df071bbe 0xd70f0f1ffc0e3fff 0xb5c3c3c7ff038fff

def z492 : W := mkw 0x04102303401006a2 0x010408c0d00401a8 0x0000060700000e00 0x00000181c0000380

def z493 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xd30f0e1f0c000e01 0xb4c3c387c3000380

def z494 : W := mkw 0x08f483e8a3d355d4 0xc23d20fa28f4d575 0xfefc89f8f3fff1ff 0xffbf227e3cfffc7f

def z495 : W := mkw 0x00458069bd8f7b7f 0xc011601a6f63dedf 0xfecc89f8ff8fffff 0xffb3227e3fe3ffff

def z496 : W := mkw 0x04112303641846f2 0x810448c0d90611bc 0x95030707ec080ff3 0xa540c1c1fb0203fc

def z497 : W := mkw 0x0bb00fa03ad07dd0 0x82ec03e80eb41f74 0xfff08fe0fff9fff3 0xfffc23f83ffe7ffc

def z498 : W := mkw 0x0bb003a01ad01580 0x02ec00e806b40560 0xabf001e01ff001c2 0x6afc007807fc0070

def z499 : W := mkw 0x304ff05ec52f8000 0x0c13fc17b14be000 0x100ff01fe00fc000 0x8403fc07f803f000

def z500 : W := mkw 0x030b0c353d8f7b7f 0xc0c2c30d4f63dedf 0xdf0f0e1f1f8fffff 0xb7c3c387c7e3ffff

def z501 : W := mkw 0x0000000000000000 0x0000000000000000 0x9103060700000001 0xa440c181c0000000

def z502 : W := mkw 0x0000000018002800 0x0000000006000a00 0x040000001c003e02 0x0100000007000f80

def z503 : W := mkw 0x1bf4efeadad03d80 0x06fd3bfab6b40f60 0xeff0ffe0fff03fc3 0x7bfc3ff83ffc0ff0

def z504 : W := mkw 0x0bab0cb51ecc3b2b 0x02eac32d47b30eca 0xf7cf0eff1f8e3e3f 0xbdf3c3bfc7e38f8f

def z505 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x1c0c8018f38ff1fe 0x870320063ce3fc7f

def z506 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x0d3006001ff03fc2 0x034c018007fc0ff0

def z507 : W := mkw 0x17feefdfe01046f2 0x85ffbbf7f80411bc 0xf7ffffffe0000ff1 0xfdfffffff80003fc

def z508 : W := mkw 0x0000002000801100 0x0000000800200440 0x62c008e013803000 0x18b0023804e00c00

def z509 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x830f06071c0e0e02 0xa0c3c181c7038380

def z510 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x540c89f8e00ff1fd 0x9503227e3803fc7f

def z511 : W := mkw 0x040130036428c272 0x81004c00d90a309c 0x9933f007ec79c032 0xe64cfc01fb1e700c

def z512 : W := mkw 0x234fd0001d2f8000 0x08d3f400074be000 0x830ff0001c0fc002 0xa0c3fc000703f000

def z513 : W := mkw 0x040110012428c272 0x81004400490a309c 0x000000000009c030 0x000000000002700c

def z514 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0xdf3fff1ffc7fffff 0xf7cfffc7ff1fffff

def z515 : W := mkw 0x0001100004288000 0x00004400010a2000 0x013370000c700000 0x004cdc00031c0000

def z516 : W := mkw 0x070b1c153c3ceefb 0x81c2c7054f0f3bbe 0xdf0f0e1f1c7fffff 0xb7c3c387c71fffff

def z517 : W := mkw 0x030b0c15040c022b 0x00c2c3054103008a 0xd30f0e1f000e003d 0xb4c3c387c003800f

def z518 : W := mkw 0x241133037f7fc6f2 0x89044cc0dfdff1bc 0x9d33f707ffffcff3 0xe74cfdc1fffff3fc

def z519 : W := mkw 0x27ffff177f7feefb 0x89ffffc5dfdffbbe 0xffffff1fffffffff 0xffffffc7ffffffff

def z520 : W := mkw 0x33bb7f965e6c8000 0x0ceedfe5979b2000 0x013376070c700000 0x004cdd81c31c0000

def z521 : W := mkw 0x000100213d8f7b7f 0xc00040084f63dedf 0x0c0000001f8ffffe 0x0300000007e3ffff

def z522 : W := mkw 0x000100001c0c0000 0x0000400007030000 0x000000001c0e0002 0x0000000007038000

def z523 : W := mkw 0x2fffffa37ffffff2 0x8bffffe8dffffffc 0xffffffe7fffffff3 0xfffffff9fffffffc

def z524 : W := mkw 0x03efcc151c0c2a2b 0x00fbf30547030a8a 0xf7fffe1f1c0e3e3f 0xfdffff87c7038f8f

def z525 : W := mkw 0x000000150000022b 0x000000054000008a 0x1000001f0000003c 0x04000007c000000f

def z526 : W := mkw 0x03b00f8000100480 0x00ec03e000040120 0xeff00fe00c700fc3 0x7bfc03f8031c03f0

def z527 : W := mkw 0x18102ffec0903d80 0x06040bffb0240f60 0x54000fffe0003fc1 0x150003fff8000ff0

def z528 : W := mkw 0x0044806881831104 0x4011201a2060c441 0x20c000e003800000 0x0830003800e00000

def z529 : W := mkw 0x0bfecfa01ad03d80 0x02ffb3e806b40f60 0xefffffe01ff03fc3 0xfbfffff807fc0ff0

def z530 : W := mkw 0x0000000000000000 0x0000000000000000 0x100c0018000e003c 0x840300060003800f

def z531 : W := mkw 0x00448048a0004050 0x8011201228001014 0xfecc89f8e009c1f3 0xffb3227e3802707c

def z532 : W := mkw 0x030b00001c0c0000 0x00c2c00007030000 0x010300000c000000 0x0040c00003000000

def z533 : W := mkw 0x03f48fc880000000 0x00fd23f220000000 0xf3fc8ff8e0000001 0xfcff23fe38000000

def z534 : W := mkw 0x0010230240000000 0x000408c090000000 0x10000707e0000001 0x040001c1f8000000

def z535 : W := mkw 0x000b00151c0c2a2b 0x0002c00547030a8a 0x140f001f1c0e3e3e 0x8503c007c7038f8f

def z536 : W := mkw 0x08b0038002500480 0x022c00e000940120 0x0030000000700000 0x000c0000001c0000

def z537 : W := mkw 0x08100fb500903fab 0x020403ed40240fea 0x54000fff00003ffd 0x150003ffc0000fff

def z538 : W := mkw 0x0000000000000000 0x0000000000000000 0xd20c081800000001 0xb483020600000000

def z539 : W := mkw 0x04102303601046f2 0x810408c0d80411bc 0x9c008707e009cff3 0xe70021c1f80273fc

def z540 : W := mkw 0x0000002000801100 0x0000000800200440 0xfecc09f8138e31ff 0xffb3027e04e38c7f

def z541 : W := mkw 0x030b0c001c0c2800 0x00c2c30007030a00 0xc70f0e001c0e3e03 0xb1c3c38007038f80

def z542 : W := mkw 0x03fecf8000000000 0x00ffb3e000000000 0xe3ffffe000000001 0xf8fffff800000000

def z543 : W := mkw 0x00000c1500002a2b 0x0000030540000a8a 0x0000060700000e00 0x00000181c0000380

def z544 : W := mkw 0x030b0c7dbc8c7b7f 0xc0c2c31f6f231edf 0xd70f0ffffc0e3fff 0xb5c3c3ffff038fff

def z545 : W := mkw 0x0044800001030000 0x001120000040c000 0xfecc8818138ff03f 0xffb3220604e3fc0f

def z546 : W := mkw 0x13efccdd9c0c2a2b 0x04fbf33767030a8a 0xf7cf0eff1c0e3e3f 0xbdf3c3bfc7038f8f

def z547 : W := mkw 0x081003201ad03d80 0x020400c806b40f60 0x8d3007001ff03fc3 0x634c01c007fc0ff0

def z548 : W := mkw 0x27bb73035e7c86a2 0x09eedcc0d79f21a8 0x013376070c700e00 0x004cdd81c31c0380

def z549 : W := mkw 0x0bbb0fb51edc3fab 0x02eec3ed47b70fea 0xeff30fe71ff03fc3 0x7bfcc3f9c7fc0ff0

def z550 : W := mkw 0x17bb7f976438c6f2 0x85eedfe5d90e31bc 0x9d33f707ec79cff3 0xe74cfdc1fb1e73fc

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x90008100e0000001 0xe400204038000000

def z552 : W := mkw 0x13eeccfc81831104 0x44fbb33f2060c441 0x62cc08f81386300c 0x18b3023e04e18c03

def z553 : W := mkw 0x13b02fdec0000000 0x04ec0bf7b0000000 0xf3f00fffe0000001 0x7cfc03fff8000000

def z554 : W := mkw 0x0000000100000222 0x0000000040000088 0x1400060700000e31 0x05000181c000038c

def z555 : W := mkw 0x041033026030c4d0 0x81040cc0980c3134 0x8d30f700ec71cfc3 0x634c3dc03b1c73f0

def z556 : W := mkw 0x00000068a0805154 0xc000001a28201455 0xdc0089f8e009f1ff 0xf700227e38027c7f

def z557 : W := mkw 0x03eec068a1835154 0xc0fbb01a2860d455 0xfffff9f8f38ff1ff 0xfffffe7e3ce3fc7f

def z558 : W := mkw 0x0cb033a262f0d5d0 0x832c0ce898bc3574 0x28f0f1e0e3f1c1c0 0x4a3c3c7838fc7070

def z559 : W := mkw 0x030b0c141c0c2809 0x00c2c30507030a02 0xc30f08181c0e300e 0xb0c3c20607038c03

def z560 : W := mkw 0x10102ffee0805154 0xc4040bffb8201455 0x54000fffe00031fd 0x150003fff8000c7f

def z561 : W := mkw 0x18f4e3eac2d01580 0x063d38fab0b40560 0x28f0f1e0e3f001c0 0x4a3c3c7838fc0070

def z562 : W := mkw 0x00b0038000000000 0x002c00e000000000 0x20f001e000000000 0x483c007800000000

def z563 : W := mkw 0x23efcc151f4f2a2b 0x08fbf30547d3ca8a 0xf7cf0e1f1f8e3e3f 0xbdf3c387c7e38f8f

def z564 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x950306070c080e33 0xa540c181c302038c

def z565 : W := mkw 0x03a000001a400000 0x00e8000006900000 0x22c0000013800000 0x08b0000004e00000

def z566 : W := mkw 0x24f4f3026373c4d0 0x893d3cc098dcf134 0x28f0f100e3f1c1c0 0x4a3c3c4038fc7070

def z567 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x63f00ee01ff03e00 0x18fc03b807fc0f80

def z568 : W := mkw 0x03e480001b430000 0x00f9200006d0c000 0xabfc80001fffc002 0xeaff200007fff000

def z569 : W := mkw 0x1054afdec0000000 0x04152bf7b0000000 0xf2cc8fffe0000001 0xfcb323fff8000000

def z570 : W := mkw 0x13fecfdc80000000 0x04ffb3f720000000 0xe3fc0ff800000001 0x78ff03fe00000000

def z571 : W := mkw 0x03b00f801a400000 0x00ec03e006900000 0xebf00fe01ff00003 0x7afc03f807fc0000

def z572 : W := mkw 0x13eeccfca1835154 0xc4fbb33f2860d455 0xfecc89f8f38ff1ff 0xffb3227e3ce3fc7f

def z573 : W := mkw 0x134eec5ec0000000 0x04d3bb17b0000000 0xd30ffe1fe0000001 0xb4c3ff87f8000000

def z574 : W := mkw 0x0000200240000000 0x0000080090000000 0x1003f007e0000000 0x8400fc01f8000000

def z575 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x38cc81f8e38fc1fc 0xce33207e38e3f07f

def z576 : W := mkw 0x0400200360004272 0x81000800d800109c 0x10000007e0000030 0x04000001f800000c

def z577 : W := mkw 0x000100011c0c2a2b 0x0000400047030a8a 0x950306071c0e3e3f 0xa540c181c7038f8f

def z578 : W := mkw 0x0000000020004050 0x8000000008001014 0x10008000e009c030 0x840020003802700c

def z579 : W := mkw 0x204fd068a5afd154 0xc813f41a296bf455 0xfecff9f8f38ff1ff 0xffb3fe7e3ce3fc7f

def z580 : W := mkw 0x13eeccdc80000000 0x04fbb33720000000 0xe3fff8f800000000 0xf8fffe3e00000000

def z581 : W := mkw 0x13ffeffffd8f7b7f 0xc4fffbffff63dedf 0xffffffffff8fffff 0xffffffffffe3ffff

def z582 : W := mkw 0x0455b303653bc6f2 0x81156cc0d94ef1bc 0xbffff707ffffcff3 0xeffffdc1fffff3fc

def z583 : W := mkw 0x0000002020805150 0x8000000808201454 0xfec089e0f389f1f3 0xffb022783ce27c7c

def z584 : W := mkw 0x33ffffdec52f8000 0x0cfffff7b14be000 0xf3ffffffe00fc001 0xfcfffffff803f000

def z585 : W := mkw 0x0044802021835154 0xc01120080860d455 0xaecc8000138ff1fe 0xebb3200004e3fc7f

def z586 : W := mkw 0x03aa400000000000 0x00ea900000000000 0x0133700000000000 0x004cdc0000000000

def z587 : W := mkw 0x040110012438c6f2 0x81004400490e31bc 0x8d33f0000c79cff2 0xe34cfc00031e73fc

def z588 : W := mkw 0x0ff5bfebfffbfff6 0xc3fd6ffafffefffd 0xffffffffffffffff 0xffffffffffffffff

def z589 : W := mkw 0x13feefdfc0002a2b 0x04ffbbf7f0000a8a 0xf7ffffffe0003e3d 0xfdfffffff8000f8f

def z590 : W := mkw 0x03000c2018803900 0x00c0030806200e40 0xefc00fe01f803fc3 0x7bf003f807e00ff0

def z591 : W := mkw 0x1bfeeffefbd37dd4 0xc6ffbbffbef4df75 0xffffffffffffffff 0xffffffffffffffff

def z592 : W := mkw 0x13eee05ec0000000 0x04fbb817b0000000 0xb3fff01fe0000000 0xecfffc07f8000000

def z593 : W := mkw 0x0044804881030004 0x401120122040c001 0x000c00180006000c 0x0003000600018003

def z594 : W := mkw 0x0000000000000000 0x0000000000000000 0x04000000100e303e 0x0100000004038c0f

def z595 : W := mkw 0x08100fa000903d80 0x020403e800240f60 0xeec00fe013803fc3 0x7bb003f804e00ff0

def z596 : W := mkw 0x030b10001c2c8000 0x00c2c400070b2000 0x8b3ff0001c7fc002 0xe2cffc00071ff000

def z597 : W := mkw 0x07b13f836438c6f2 0x81ec4fe0d90e31bc 0xfff3ffe7ec79cff3 0xfffcfff9fb1e73fc

def z598 : W := mkw 0x034e8c5c80000000 0x00d3a31720000000 0xf3cf8fffe0000001 0xfcf3e3fff8000000

def z599 : W := mkw 0x0401300344288222 0x01004c00d10a2088 0x0003700700000000 0x0000dc01c0000000

def z600 : W := mkw 0x03bb0f951c0c2a2b 0x00eec3e547030a8a 0xf7ff0fff1c0e3e3f 0xfdffc3ffc7038f8f

def z601 : W := mkw 0x0800002000903d80 0x0200000800240f60 0x0400000000003fc0 0x0100000000000ff0

def z602 : W := mkw 0x0000000000000000 0x0000000000000000 0xc600080010003003 0x3180020004000c00

def z603 : W := mkw 0x030b0c351c8c3b2b 0x00c2c30d47230eca 0xffcf0fff1f8e3fff 0xfff3c3ffc7e38fff

def z604 : W := mkw 0x03ab00001e4c0000 0x00eac00007930000 0xabff00001ffe0002 0xeaffc00007ff8000

def z605 : W := mkw 0x0bb00fa000903d80 0x02ec03e800240f60 0xe7f00fe000003fc1 0x79fc03f800000ff0

def z606 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x110f061f0c0e0e3c 0x8443c187c303838f

def z607 : W := mkw 0x030a0c1418002800 0x00c2830506000a00 0xd70f0e1f1c003e03 0xb5c3c387c7000f80

def z608 : W := mkw 0x0411332365bbd7f6 0xc1044cc8d96ef5fd 0x9d33f707ffffffff 0xe74cfdc1ffffffff

def z609 : W := mkw 0x13ba6f9640000000 0x04ee9be590000000 0xd33f7e1f00000001 0xb4cfdf87c0000000

def z610 : W := mkw 0x13ffefdfc40c022b 0x04fffbf7f103008a 0xf3ffffffe00e003d 0xfcfffffff803800f

def z611 : W := mkw 0x030a0c1400000000 0x00c2830500000000 0xd70f0e1f100e303f 0xb5c3c387c4038c0f

def z612 : W := mkw 0x03a0000000000000 0x00e8000000000000 0xa3f0000000000000 0x68fc000000000000

def z613 : W := mkw 0x1bfecffc9ad03d80 0x06ffb3ff26b40f60 0xeffc0ff81ff03fc3 0x7bff03fe07fc0ff0

def z614 : W := mkw 0x0044800001030000 0x001120000040c000 0x22cc000013860000 0x08b3000004e18000

def z615 : W := mkw 0x200110203fefd154 0xc80044080ffbf455 0x0c0000001ffff1fe 0x0300000007fffc7f

def z616 : W := mkw 0x23ffd3001f7f8480 0x08fff4c007dfe120 0xaffff7001fffcfc3 0xebfffdc007fff3f0

def z617 : W := mkw 0x00010c151c0c2a2b 0x0000430547030a8a 0x54000e1f1c0e3e3f 0x15000387c7038f8f

def z618 : W := mkw 0x040b3017642cc27b 0x8102cc05d90b309e 0x100ff01fe00fc03c 0x8403fc07f803f00f

def z619 : W := mkw 0x040130036428c272 0x81004c00d90a309c 0x9503f607ec09ce33 0xa540fd81fb02738c

def z620 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x6ecc08f8138ff1fe 0x1bb3023e04e3fc7f

def z621 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1133f607ec79ce30 0x844cfd81fb1e738c

def z622 : W := mkw 0x33fff3cadf6f8000 0x0cfffcf2b7dbe000 0xabfff1e0ffffc002 0xeafffc783ffff000

def z623 : W := mkw 0x23eec0001b470000 0x08fbb00006d1c000 0xa3fff00013860000 0xe8fffc0004e18000

def z624 : W := mkw 0x104ee07ee1835154 0xc413b81fb860d455 0xfecff9fff38ff1ff 0xffb3fe7ffce3fc7f

def z625 : W := mkw 0x0410330240308480 0x01040cc0900c2120 0x0030700000700000 0x000c1c00001c0000

def z626 : W := mkw 0x13ba6f9640000000 0x04ee9be590000000 0xe3f37fe700000001 0x78fcdff9c0000000

def z627 : W := mkw 0x2befd0201fffbd80 0x0afbf40807ffef60 0xaffff0001fffffc2 0xebfffc0007fffff0

def z628 : W := mkw 0x03000c1518002a2b 0x00c0030546000a8a 0xd7000e1f1c003e3f 0x35c00387c7000f8f

def z629 : W := mkw 0x040130036428c272 0x81004c00d90a309c 0x9c03f107e009c1f3 0xe700fc41f802707c

def z630 : W := mkw 0x03a000201ac01100 0x00e8000806b00440 0xeff009e01ff031c3 0x7bfc027807fc0c70

def z631 : W := mkw 0x204fd048a52fc054 0xc813f412294bf015 0x100ff018e00fc03c 0x8403fc063803f00f

def z632 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1833f107e079c1f0 0xc60cfc41f81e707c

def z633 : W := mkw 0x00448048a1034054 0xc01120122840d015 0x00008000e001c000 0x0000200038007000

def z634 : W := mkw 0x040110013c3ceefb 0x810044004f0f3bbe 0x0c0000001c7ffffe 0x03000000071fffff

def z635 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x2cc081e0f38ff1fe 0x4b3020783ce3fc7f

def z636 : W := mkw 0x040110012438c6f2 0x81004400490e31bc 0x9d0306070c79cff3 0xa740c181c31e73fc

def z637 : W := mkw 0x03fee30240000000 0x00ffb8c090000000 0xb3fff707e0000001 0xecfffdc1f8000000

def z638 : W := mkw 0x080000203bd37dd4 0xc20000080ef4df75 0x0c0000001ffffffe 0x0300000007ffffff

def z639 : W := mkw 0x0c1133237ef8fff2 0x83044cc8dfbe3ffc 0x9d33f707fff9fff3 0xe74cfdc1fffe7ffc

def z640 : W := mkw 0x17ffffdfe428c272 0x85fffff7f90a309c 0xf3ffffffe009c031 0xfcfffffff802700c

def z641 : W := mkw 0x23eec068bbc75154 0xc8fbb01a2ef1d455 0xfecc89f8f38ff1ff 0xffb3227e3ce3fc7f

def z642 : W := mkw 0x0000002001831104 0x400000080060c441 0x000000001386300c 0x0000000004e18c03

def z643 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x66c00fe013803fc1 0x19b003f804e00ff0

def z644 : W := mkw 0x00000c7da0807b7f 0xc000031f68201edf 0x54000fffe0003ffd 0x150003fff8000fff

def z645 : W := mkw 0x071b33037c3cc6f2 0x81c6ccc0df0f31bc 0x9f3ff707fc7fcff3 0xe7cffdc1ff1ff3fc

def z646 : W := mkw 0x030a0c1418042809 0x00c2830506010a02 0xc70c0e181c063e0f 0x31c3038607018f83

def z647 : W := mkw 0x0bf48fe89bd33d84 0x42fd23fa26f4cf61 0xeffc0ff81ff63fcf 0x7bff03fe07fd8ff3

def z648 : W := mkw 0x04000001201046f2 0x81000000480411bc 0x0400000000000ff0 0x01000000000003fc

def z649 : W := mkw 0x00448068a0805154 0xc011201a28201455 0xf6cc89f8e00031fd 0xfdb3227e38000c7f

def z650 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1c000707ec79cff3 0x070001c1fb1e73fc

def z651 : W := mkw 0x0bb00f801a502c80 0x02ec03e006940b20 0xabf006001ff00e02 0x6afc018007fc0380

def z652 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x62fcf9f8e0000000 0x58bf3e7e38000000

def z653 : W := mkw 0x0454b36ae1b3d5d4 0xc1152cdab86cf575 0xfefcf9f8f3fff1ff 0xffbf3e7e3cfffc7f

def z654 : W := mkw 0x28f4d3a003f39580 0x0a3d34e800fce560 0x28f0f1e003f1c1c0 0x4a3c3c7800fc7070

def z655 : W := mkw 0x030a0c1418042809 0x00c2830506010a02 0xd60c0818100e303f 0xb583020604038c0f

def z656 : W := mkw 0x04113303443886a2 0x01044cc0d10e21a8 0x9133f707ec700e01 0xe44cfdc1fb1c0380

def z657 : W := mkw 0x0000000001030000 0x000000000040c000 0x08000000138fc002 0x0200000004e3f000

def z658 : W := mkw 0x08000ca000803900 0x0200032800200e40 0x400008e000003000 0x1000023800000c00

def z659 : W := mkw 0x0b1b0fb51c9c3fab 0x02c6c3ed47270fea 0xd70f0fff1c0e3fff 0xb5c3c3ffc7038fff

def z660 : W := mkw 0x03eec04880000000 0x00fbb01220000000 0xf3fff9f8e0000001 0xfcfffe7e38000000

def z661 : W := mkw 0x200000001b470000 0x0800000006d1c000 0x0000000013860000 0x0000000004e18000

def z662 : W := mkw 0x0ba00c801a402800 0x02e8032006900a00 0x0000000000000000 0x0000000000000000

def z663 : W := mkw 0x030b0c141c0c0000 0x00c2c30507030000 0xd30f0e1f1c0e0003 0xb4c3c387c7038000

def z664 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x63ff7eff00000000 0x18ffdfbfc0000000

def z665 : W := mkw 0x041033026030c4d0 0x81040cc0980c3134 0x9c30f100e079c1f3 0xe70c3c40381e707c

def z666 : W := mkw 0x0000000000000000 0x0000000000000000 0xaac0000013800002 0x6ab0000004e00000

def z667 : W := mkw 0x041133037c3ceefb 0x81044cc0df0f3bbe 0x9d33f707fc7fffff 0xe74cfdc1ff1fffff

def z668 : W := mkw 0x00448048a1034054 0xc01120122840d015 0x9c0c8118e00fc1ff 0xe70320463803f07f

def z669 : W := mkw 0x004f805da50f427f 0xc013e0176943d09f 0x100f801fe00fc03c 0x8403e007f803f00f

def z670 : W := mkw 0x0000000000000000 0x0000000000000000 0xe2c009e000000001 0x78b0027800000000

def z671 : W := mkw 0x03b00fa000801100 0x00ec03e800200440 0xeff00fe0138031c3 0x7bfc03f804e00c70

def z672 : W := mkw 0x034f8c151d0f2a2b 0x00d3e3054743ca8a 0xffcf8e1f1f8ffe3f 0xfff3e387c7e3ff8f

def z673 : W := mkw 0x0000000000000000 0x0000000000000000 0x893000000c700002 0x624c0000031c0000

def z674 : W := mkw 0x0001100004288000 0x00004400010a2000 0x0003f0000009c000 0x8000fc0000027000

def z675 : W := mkw 0x14f4f3cae030c4d0 0x853d3cf2b80c3134 0x28f0f1e0e071c1c0 0x4a3c3c78381c7070

def z676 : W := mkw 0x0044806881831104 0x4011201a2060c441 0xeacc88f8138ff00e 0xfab3223e04e3fc03

def z677 : W := mkw 0x0ba000201ad03d80 0x02e8000806b40f60 0xaff000001ff03fc2 0x6bfc000007fc0ff0

def z678 : W := mkw 0x0b000c201ad03d80 0x02c0030806b40f60 0xcf000e001ff03fc3 0x33c0038007fc0ff0

def z679 : W := mkw 0x00100f8000000000 0x000403e000000000 0x40000fe000000001 0x100003f800000000

def z680 : W := mkw 0x23eec0689bc71104 0x48fbb01a26f1c441 0x62cc08f81386300c 0x18b3023e04e18c03

def z681 : W := mkw 0x1000205ec0000000 0x04000817b0000000 0x1000001fe0000000 0x04000007f8000000

def z682 : W := mkw 0x08b003a002d01580 0x022c00e800b40560 0xeef009e013f031c3 0x7bbc027804fc0c70

def z683 : W := mkw 0x0b0b0c351edc3fab 0x02c2c30d47b70fea 0xdf0f0e1f1ffe3fff 0xb7c3c387c7ff8fff

def z684 : W := mkw 0x200110001e6c8000 0x08004400079b2000 0x000000000c700000 0x00000000031c0000

def z685 : W := mkw 0x27eff0037f6fc272 0x89fbfc00dfdbf09c 0xbbfff007ffffc032 0xeefffc01fffff00c

def z686 : W := mkw 0x0044800021034050 0x801120000840d014 0xbecc8100f38fc1f3 0xefb320403ce3f07c

def z687 : W := mkw 0x0010030000100480 0x000400c000040120 0x08300100007001c0 0x420c0040001c0070

def z688 : W := mkw 0x00110301041806a2 0x000440c0410601a8 0x9d3307070c780ff3 0xe74cc1c1c31e03fc

def z689 : W := mkw 0x0000000000000000 0x0000000000000000 0x820c0000100e0002 0xa083000004038000

def z690 : W := mkw 0x13ffefdfc4080222 0x04fffbf7f1020088 0xf7ffffffec080e33 0xfdfffffffb02038c

def z691 : W := mkw 0x0bb10fa11edc3fab 0x02ec43e847b70fea 0xeff00fe01ffe3fff 0x7bfc03f807ff8fff

def z692 : W := mkw 0x104ec05c80000000 0x0413b01720000000 0x000c001800000000 0x0003000600000000

def z693 : W := mkw 0x0001000004080000 0x0000400001020000 0x810300000c080002 0xa040c00003020000

def z694 : W := mkw 0x0fb02fa37ad07ff2 0x83ec0be8deb41ffc 0xfff00fe7fff03ff3 0x7ffc03f9fffc0ffc

def z695 : W := mkw 0x000000001a400000 0x0000000006900000 0x080000001ff00002 0x0200000007fc0000

def z696 : W := mkw 0x13aa4c9400000000 0x04ea932500000000 0x0000000000000000 0x0000000000000000

def z697 : W := mkw 0x0bb00fa03bd37dd4 0xc2ec03e80ef4df75 0xeff00fe01fffffff 0x7bfc03f807ffffff

def z698 : W := mkw 0x204590001f6f8000 0x0811640007dbe000 0xaacc80001fffc002 0xeab3200007fff000

def z699 : W := mkw 0x0bf48fa01bd33d80 0x02fd23e806f4cf60 0xeffc8fe01fffffc3 0xfbff23f807fffff0

def z700 : W := mkw 0x0000002021835154 0xc00000080860d455 0xde0c0818138ff1ff 0xb783020604e3fc7f

def z701 : W := mkw 0x0000000000000000 0x0000000000000000 0x420c08181006300c 0x1083020604018c03

def z702 : W := mkw 0x13feefdee0004050 0x84ffbbf7b8001014 0xffffffffe009c1f3 0xfffffffff802707c

def z703 : W := mkw 0x17ffffdffc3ceefb 0x85fffff7ff0f3bbe 0xfffffffffc7fffff 0xffffffffff1fffff

def z704 : W := mkw 0x0000000018042809 0x0000000006010a02 0x000000001006300c 0x0000000004018c03

def z705 : W := mkw 0x030a000018040000 0x00c2800006010000 0x020c000010060000 0x0083000004018000

def z706 : W := mkw 0x10f4e3cac0000000 0x043d38f2b0000000 0xf2fcf9f8e0000001 0xfcbf3e7e38000000

def z707 : W := mkw 0x144ff05fe52bc276 0xc513fc17f94af09d 0x100ff01fe00fc03c 0x8403fc07f803f00f

def z708 : W := mkw 0x33feefdedb470000 0x0cffbbf7b6d1c000 0xfbfffffff38fc003 0xfefffffffce3f000

def z709 : W := mkw 0x030a0c1418002800 0x00c2830506000a00 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z710 : W := mkw 0x13feefdec0100480 0x04ffbbf7b0040120 0xfbffffffe07001c1 0xfefffffff81c0070

def z711 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x9d33f707fc7fffff 0xe74cfdc1ff1fffff

def z712 : W := mkw 0x184ee07edad03d80 0x0613b81fb6b40f60 0x1c0ff01ffff03fc2 0x8703fc07fffc0ff0

def z713 : W := mkw 0x105eefdec0000000 0x0417bbf7b0000000 0xf2cfffffe0000001 0xfcb3fffff8000000

def z714 : W := mkw 0x0000002000901580 0x0000000800240560 0xeec009e01ff03fc3 0x7bb0027807fc0ff0

def z715 : W := mkw 0x04459049a52bc276 0xc1116412694af09d 0x100c8018e00fc03c 0x840320063803f00f

def z716 : W := mkw 0x00102302601044d0 0x800408c098041134 0x9d33f707ec79cff3 0xe74cfdc1fb1e73fc

def z717 : W := mkw 0x230b5c151c2caa2b 0x08c2d705470b2a8a 0xd70f7e1f1c0e3e3f 0xb5c3df87c7038f8f

def z718 : W := mkw 0x071a3f167834ecd9 0x81c68fc59e0d3b36 0x4a3cf918f077f1cc 0x528f3e463c1dfc73

def z719 : W := mkw 0x04113303643cc6fb 0x81044cc0d90f31be 0x9d33f707ec7fcfff 0xe74cfdc1fb1ff3ff

def z720 : W := mkw 0x285fdfa005bfbd80 0x0a17f7e8016fef60 0x440fffe0000fffc1 0x9103fff80003fff0

def z721 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf7ffffffe0080033 0xfdfffffff802000c

def z722 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x8d33f707ec71cfc3 0x634cfdc1fb1c73f0

def z723 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1d33f707ec71cff1 0x474cfdc1fb1c73fc

def z724 : W := mkw 0x03a010001a608000 0x00e8040006982000 0xabf0f0001ff1c002 0x6afc3c0007fc7000

def z725 : W := mkw 0x33efd05c9f6f8000 0x0cfbf41727dbe000 0xabfff0181fffc002 0xeafffc0607fff000

def z726 : W := mkw 0x03ab1c151e6caa2b 0x00eac705479b2a8a 0xfffffe1f1ffffe3f 0xffffff87c7ffff8f

def z727 : W := mkw 0x1bb06fa25ad03d80 0x06ec1be896b40f60 0xeff07fe01ff03fc3 0x7bfc1ff807fc0ff0

def z728 : W := mkw 0x000110012428c272 0x80004400490a309c 0x9d33f707ec79cff3 0xe74cfdc1fb1e73fc

def z729 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xebf00fe00ff00fc1 0x7afc03f803fc03f0

def z730 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xabf007e01ff00fc2 0x6afc01f807fc03f0

def z731 : W := mkw 0x03eecc5c80000000 0x00fbb31720000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z732 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xfffc89f8fffff1ff 0xffff227e3ffffc7f

def z733 : W := mkw 0x030b0c15040c2a2b 0x00c2c30541030a8a 0xd70f0e1f000e3e3d 0xb5c3c387c0038f8f

def z734 : W := mkw 0x0001100004288000 0x00004400010a2000 0xabf3f0001ff9c002 0xeafcfc0007fe7000

def z735 : W := mkw 0x0bf48fc8bb536cd4 0xc2fd23f22ed4db35 0x113c8618ec7fce3c 0x844f21863b1ff38f

def z736 : W := mkw 0x20e5d001076b8222 0x0839740041dae088 0xbdf3f6070ff9ce33 0xef7cfd81c3fe738c

def z737 : W := mkw 0x13ba6fdec0000000 0x04ee9bf7b0000000 0xf3f37fffe0000001 0x7cfcdffff8000000

def z738 : W := mkw 0x10f5e3cbdc0c2a2b 0x043d78f2f7030a8a 0x24f0f1e0fc0e3e3e 0x493c3c783f038f8f

def z739 : W := mkw 0x23efd0001f6fa809 0x08fbf40007dbea02 0xabfff0001ffff00e 0xeafffc0007fffc03

def z740 : W := mkw 0x23efd0151f6f822b 0x08fbf40547dbe08a 0xbffff61f1fffce3f 0xeffffd87c7fff38f

def z741 : W := mkw 0x030b1c151c2caa2b 0x00c2c705470b2a8a 0xd73f7e1f1c7e3e3f 0xb5cfdf87c71f8f8f

def z742 : W := mkw 0x1bfeefdec0102c80 0x06ffbbf7b0040b20 0xf3ffffffe0000e01 0xfcfffffff8000380

def z743 : W := mkw 0x13ba6fb661835154 0xc4ee9bed9860d455 0x0d337607138ff1fe 0x034cdd81c4e3fc7f

def z744 : W := mkw 0x13feefdeda402800 0x04ffbbf7b6900a00 0xfffffffffff03e03 0xfffffffffffc0f80

def z745 : W := mkw 0x13feefdedb430000 0x04ffbbf7b6d0c000 0xfbffffffffffc003 0xfefffffffffff000

def z746 : W := mkw 0x00b0238240000000 0x002c08e090000000 0xb1f3f7e7e0000001 0xec7cfdf9f8000000

def z747 : W := mkw 0x034f8c7dbd8f7b7f 0xc0d3e31f6f63dedf 0x29c387e7ef81cfc0 0x4a70e1f9fbe073f0

def z748 : W := mkw 0x000b0015040c022b 0x0002c0054103008a 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z749 : W := mkw 0x03b00fa000901580 0x00ec03e800240560 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z750 : W := mkw 0x20e4d0001b638000 0x0839340006d8e000 0x28f0f0001ff1c002 0x4a3c3c0007fc7000

def z751 : W := mkw 0x0010032000901580 0x000400c800240560 0xadf007e00ff00fc3 0x6b7c01f803fc03f0

def z752 : W := mkw 0x13fee3cac0000000 0x04ffb8f2b0000000 0xb3fff7e7e0000001 0xecfffdf9f8000000

def z753 : W := mkw 0x33feefdedb472809 0x0cffbbf7b6d1ca02 0xf3fffffff386300d 0xfcfffffffce18c03

def z754 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0xa8f0f00003f9c002 0xea3c3c0000fe7000

def z755 : W := mkw 0x0bab0c951e4c2a2b 0x02eac32547930a8a 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z756 : W := mkw 0x1beeccfc9bc33904 0x46fbb33f26f0ce41 0x62cc08f81386300c 0x18b3023e04e18c03

def z757 : W := mkw 0x23ab5068beecd154 0xc8ead41a2fbb3455 0x553379f8ec7031fd 0x154cde7e3b1c0c7f

def z758 : W := mkw 0x13feefdec2400000 0x04ffbbf7b0900000 0xfbffffffe3f00001 0xfefffffff8fc0000

def z759 : W := mkw 0x0bba0fb41ad43d89 0x02ee83ed06b50f62 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z760 : W := mkw 0x131a2fdec0000000 0x04c68bf7b0000000 0xd33fffffe0000001 0xf4cffffff8000000

def z761 : W := mkw 0x20e4dc150363aa2b 0x0839370540d8ea8a 0x7cf0fe1f03f1fe3d 0x5f3c3f87c0fc7f8f

def z762 : W := mkw 0x23efdc141f6f8000 0x08fbf70507dbe000 0xabfff6071fffc002 0xeafffd81c7fff000

def z763 : W := mkw 0x13eeecdec0000000 0x04fbbb37b0000000 0xf2cff9ffe0000001 0xfcb3fe7ff8000000

def z764 : W := mkw 0x10fee3dec0000000 0x043fb8f7b0000000 0xb1fff7ffe0000001 0xec7ffdfff8000000

def z765 : W := mkw 0x33efdcdc9f6f8000 0x0cfbf73727dbe000 0xfbfff9f8ffffc003 0xfefffe7e3ffff000

def z766 : W := mkw 0x0bba2fb65ad03d80 0x02ee8bed96b40f60 0xfffffffffff03fc3 0xfffffffffffc0ff0

def z767 : W := mkw 0x07b11f812438c6f2 0x81ec47e0490e31bc 0xeff00fe00c79cff3 0x7bfc03f8031e73fc

def z768 : W := mkw 0x23efdc151f6f822b 0x08fbf70547dbe08a 0xfbfffe1f1fffc03f 0xfeffff87c7fff00f

def z769 : W := mkw 0x1bfeefdeda502c80 0x06ffbbf7b6940b20 0xffffffffec700fc3 0xfffffffffb1c03f0

def z770 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xfbfff8181fffc003 0xfefffe0607fff000

def z771 : W := mkw 0x034f90001d2f8000 0x00d3e400074be000 0xabfff0001fffc002 0xeafffc0007fff000

def z772 : W := mkw 0x204590001f6f8000 0x0811640007dbe000 0xabfff0001fffc002 0xeafffc0007fff000

def z773 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0xfff3ffe7ec79cff3 0xfffcfff9fb1e73fc

def z774 : W := mkw 0x08b00fa002d03d80 0x022c03e800b40f60 0xedf00fe00ff03fc3 0x7b7c03f803fc0ff0

def z775 : W := mkw 0x00a0100002608000 0x0028040000982000 0x28f0f00003f1c000 0x4a3c3c0000fc7000

def z776 : W := mkw 0x27fee3037b5746f2 0x89ffb8c0ded5d1bc 0x36cc0707f3860ff1 0x0db301c1fce183fc

def z777 : W := mkw 0x23e4dc001b63a800 0x08f9370006d8ea00 0xeff0fe001ff1fe03 0x7bfc3f8007fc7f80

def z778 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xeffff8181ffffe3e 0xfbfffe0607ffff8f

def z779 : W := mkw 0x30e4d0c883638000 0x0c39343220d8e000 0x28f0f0e003f1c000 0x4a3c3c3800fc7000

def z780 : W := mkw 0x0010234ac0000000 0x000408d2b0000000 0xd133ffffe0000001 0xf44cfffff8000000

def z781 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xa3fff7e7e0000000 0xe8fffdf9f8000000

def z782 : W := mkw 0x08bb03b506dc17ab 0x022ec0ed41b705ea 0x38ff01ff03fe01fc 0xce3fc07fc0ff807f

def z783 : W := mkw 0x17efdcdda438c6f2 0x85fbf737690e31bc 0x6ecc08f80c79cff2 0x1bb3023e031e73fc

def z784 : W := mkw 0x23efd0151f6f822b 0x08fbf40547dbe08a 0xfffff81f1ffff03f 0xfffffe07c7fffc0f

def z785 : W := mkw 0x23efd0011f6f8222 0x08fbf40047dbe088 0xbbfff0071fffc032 0xeefffc01c7fff00c

def z786 : W := mkw 0x000b0c15040c2a2b 0x0002c30541030a8a 0xd50f0e1f0c0e3e3f 0xb543c387c3038f8f

def z787 : W := mkw 0x20e5d0001f6f8000 0x0839740007dbe000 0xaafcf0001fffc002 0xeabf3c0007fff000

def z788 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x23fff0001fffc000 0x88fffc0007fff000

def z789 : W := mkw 0x080000201ad03d80 0x0200000806b40f60 0x6ec008e01ff03fc2 0x1bb0023807fc0ff0

def z790 : W := mkw 0x20e4d04883638000 0x0839341220d8e000 0x28f0f1e0e3f1c000 0x4a3c3c7838fc7000

def z791 : W := mkw 0x0bba4fa01ad03d80 0x02ee93e806b40f60 0xeff37fe01ff03fc3 0x7bfcdff807fc0ff0

def z792 : W := mkw 0x135eefdec0000000 0x04d7bbf7b0000000 0xd30fffffe0000001 0xb4c3fffff8000000

def z793 : W := mkw 0x23efd0011f6f8222 0x08fbf40047dbe088 0xfffffe1f1ffffe3f 0xffffff87c7ffff8f

def z794 : W := mkw 0x0401102125abd376 0xc1004408496af4dd 0x0c000000138ff1fe 0x0300000004e3fc7f

def z795 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x7ecc09f8f38ff1ff 0x1fb3027e3ce3fc7f

def z796 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xffcf8ffff38ff1ff 0xfff3e3fffce3fc7f

def z797 : W := mkw 0x0fa13ca37ee8fb72 0x83e84f28dfba3edc 0x72c3f8e7f389f030 0x9cb0fe39fce27c0c

def z798 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xfbffffffe009c003 0xfefffffff8027000

def z799 : W := mkw 0x0ba00ca01ad03d80 0x02e8032806b40f60 0xeec009e01ff03fc3 0x7bb0027807fc0ff0

def z800 : W := mkw 0x20e5d0001f6f8000 0x0839740007dbe000 0x28f0f0000ff1c000 0x4a3c3c0003fc7000

def z801 : W := mkw 0x0044900001238000 0x001124000048e000 0xaafcf00013ffc002 0xeabf3c0004fff000

def z802 : W := mkw 0x03efd000052b8000 0x00fbf400014ae000 0xabfff0001fffc002 0xeafffc0007fff000

def z803 : W := mkw 0x20a0500003638000 0x0828140000d8e000 0x0830700003f1c000 0x020c1c0000fc7000

def z804 : W := mkw 0x104ee05ec0000000 0x0413b817b0000000 0x500ff9ffe0000001 0x9403fe7ff8000000

def z805 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0xdf33ff07fc79fff3 0xf7ccffc1ff1e7ffc

def z806 : W := mkw 0x13feefdec1030000 0x04ffbbf7b040c000 0xfbffffffe381c001 0xfefffffff8e07000

def z807 : W := mkw 0x23efdc011f6faa22 0x08fbf70047dbea88 0xfffffe071ffffe33 0xffffff81c7ffff8c

def z808 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xfff30fe71ff03fc3 0xfffcc3f9c7fc0ff0

def z809 : W := mkw 0x13feefdeda500480 0x04ffbbf7b6940120 0xfffffffffff00fc3 0xfffffffffffc03f0

def z810 : W := mkw 0x03a00c201ac03900 0x00e8030806b00e40 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z811 : W := mkw 0x13ba6fdec0000000 0x04ee9bf7b0000000 0xd133ffffe0000001 0xf44cfffff8000000

def z812 : W := mkw 0x03010c011c082a22 0x00c0430047020a88 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z813 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x7acc89f8f38ff1fc 0xdeb3227e3ce3fc7f

def z814 : W := mkw 0x0c102fa260907dd0 0x83040be898241f74 0x44000fe0e0003fc1 0x110003f838000ff0

def z815 : W := mkw 0x200110001f6f8000 0x0800440007dbe000 0x0830f0001fffc002 0x420c3c0007fff000

def z816 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0xa9f0f0000ff1c002 0x6a7c3c0003fc7000

def z817 : W := mkw 0x0bb003a01ad01580 0x02ec00e806b40560 0xaff007e01ff00fc3 0x6bfc01f807fc03f0

def z818 : W := mkw 0x23ab5c151f6faa2b 0x08ead70547dbea8a 0x0d3376071ffffe3e 0x034cdd81c7ffff8f

def z819 : W := mkw 0x230b1c151e6caa2b 0x08c2c705479b2a8a 0xd70f0e1f1c7e3e3f 0xb5c3c387c71f8f8f

def z820 : W := mkw 0x000b0c15040c2a2b 0x0002c30541030a8a 0xd60f0e1f100e3e3f 0xb583c387c4038f8f

def z821 : W := mkw 0x23eed0001b678000 0x08fbb40006d9e000 0x28f0f00003f1c000 0x4a3c3c0000fc7000

def z822 : W := mkw 0x030a0c1518042a2b 0x00c2830546010a8a 0xd60c0e1f100e3e3f 0xb5830387c4038f8f

def z823 : W := mkw 0x08b003a01ad03d80 0x022c00e806b40f60 0xeef009e01ff03fc3 0x7bbc027807fc0ff0

def z824 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x2afff00013ffc000 0xcabffc0004fff000

def z825 : W := mkw 0x13feefdec0002800 0x04ffbbf7b0000a00 0xf7ffffffe0003e01 0xfdfffffff8000f80

def z826 : W := mkw 0x10f4e3cac0000000 0x043d38f2b0000000 0x21f3f7e7e0000000 0x487cfdf9f8000000

def z827 : W := mkw 0x23eed0001b678000 0x08fbb40006d9e000 0xabfff00013f7c000 0xeafffc0004fdf000

def z828 : W := mkw 0x23eedc1403638000 0x08fbb70500d8e000 0xfbfffe1f03f1c001 0xfeffff87c0fc7000

def z829 : W := mkw 0x030a0c1518042a2b 0x00c2830546010a8a 0xd70c0e1f1c063e3f 0x35c30387c7018f8f

def z830 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x6bf00fe01ff03fc0 0x5afc03f807fc0ff0

def z831 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x0d33f707ec79cff2 0x434cfdc1fb1e73fc

def z832 : W := mkw 0x23efdc001f6fa800 0x08fbf70007dbea00 0xfffffe181ffffe3f 0xffffff8607ffff8f

def z833 : W := mkw 0x13feefdec1030000 0x04ffbbf7b040c000 0xfffffffff38ff03f 0xfffffffffce3fc0f

def z834 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xeffc0ff81ff63fcf 0x7bff03fe07fd8ff3

def z835 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x2bff70001fffc002 0x0affdc0007fff000

def z836 : W := mkw 0x23efd0011f6f8222 0x08fbf40047dbe088 0xaffff0001fffce32 0xebfffc0007fff38c

def z837 : W := mkw 0x0f112fa37c987ff2 0x83c44be8df261ffc 0xd7030fe7fc083ff3 0xb5c0c3f9ff020ffc

def z838 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xfff08fe0fff03fc3 0xfffc23f83ffc0ff0

def z839 : W := mkw 0x1bb02fb65ad03d80 0x06ec0bed96b40f60 0xeff00fe71ff03fc3 0x7bfc03f9c7fc0ff0

def z840 : W := mkw 0x23efd0151f6faa2b 0x08fbf40547dbea8a 0xbffff01f1ffffe3e 0xeffffc07c7ffff8f

def z841 : W := mkw 0x30113fdedf6f8000 0x0c044ff7b7dbe000 0x58000fffffffc003 0x160003fffffff000

def z842 : W := mkw 0x000b00151c0c2a2b 0x0002c00547030a8a 0x950f061f1c0e3e3f 0xa543c187c7038f8f

def z843 : W := mkw 0x23eed00003638000 0x08fbb40000d8e000 0xabfff00013ffc002 0xeafffc0004fff000

def z844 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x570f0e1f1c063e3d 0x15c3c387c7018f8f

def z845 : W := mkw 0x0401102124b8d7f2 0x81004408492e35fc 0x0c0000001ff9fff2 0x0300000007fe7ffc

def z846 : W := mkw 0x23ab5c151e6caa2b 0x08ead705479b2a8a 0xffff7e1f1ffe3e3f 0xffffdf87c7ff8f8f

def z847 : W := mkw 0x33efdc941f6f8000 0x0cfbf72507dbe000 0xabfff0001fffc002 0xeafffc0007fff000

def z848 : W := mkw 0x23efd0489f6f8000 0x08fbf41227dbe000 0xfffff9f8fffff03f 0xfffffe7e3ffffc0f

def z849 : W := mkw 0x33efdcdd9f6faa2b 0x0cfbf73767dbea8a 0xfffffeff1ffffe3f 0xffffffbfc7ffff8f

def z850 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x72cfffffe0000001 0x9cb3fffff8000000

def z851 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xdf0f8e1f1c0ffe3f 0xf7c3e387c703ff8f

def z852 : W := mkw 0x0cf4b3eae3f3d5d4 0xc33d2cfab8fcf575 0x28f0f1e0e3f1c1c0 0x4a3c3c7838fc7070

def z853 : W := mkw 0x23eecc7c9bc7390d 0x48fbb31f26f1ce43 0x62cc08f81386300c 0x18b3023e04e18c03

def z854 : W := mkw 0x03feef8240000000 0x00ffbbe090000000 0xf3ffffe7e0000001 0xfcfffff9f8000000

def z855 : W := mkw 0x08b003a002d01580 0x022c00e800b40560 0x2cf001e00ff00fc2 0x4b3c007803fc03f0

def z856 : W := mkw 0x071b2f7ffc9c7fff 0xc1c6cbdfff271fff 0xd70f0ffffc0e3fff 0xb5c3c3ffff038fff

def z857 : W := mkw 0x00000c1500002a2b 0x0000030540000a8a 0x560c0e1f10063e3d 0x15830387c4018f8f

def z858 : W := mkw 0x23efdc5d9f6faa2b 0x08fbf71767dbea8a 0xfffffffffffffe3f 0xffffffffffffff8f

def z859 : W := mkw 0x0455b36bc5bb97a6 0x41156cdaf16ee5e9 0x63ff7eff1ff63e0c 0x18ffdfbfc7fd8f83

def z860 : W := mkw 0x0bba0fb41ad43d89 0x02ee83ed06b50f62 0xfffc0ff81ffe3fff 0xffff03fe07ff8fff

def z861 : W := mkw 0x2c0110213ffffff2 0x8b0044084ffffffc 0x0c0000001ffffff2 0x0300000007fffffc

def z862 : W := mkw 0x04102323609057f6 0xc10408c8d82415fd 0x14000707e0003ffd 0x050001c1f8000fff

def z863 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x530f0e1f1c0e3e3c 0x94c3c387c7038f8f

def z864 : W := mkw 0x13eeecdec0000000 0x04fbbb37b0000000 0xf3fff8ffe0000000 0xfcfffe3ff8000000

def z865 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0x29f3f6070ff1ce00 0x4a7cfd81c3fc7380

def z866 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x513fffffe0000001 0x944ffffff8000000

def z867 : W := mkw 0x00102f8240000000 0x00040be090000000 0xd133ffe7e0000001 0xf44cfff9f8000000

def z868 : W := mkw 0x200110213feffb7f 0xc80044084ffbfedf 0x0c0000001ffffffe 0x0300000007ffffff

def z869 : W := mkw 0x1bba6fb65ad03d80 0x06ee9bed96b40f60 0xffff7fff1ff03fc3 0xffffdfffc7fc0ff0

def z870 : W := mkw 0x23ab5c151f6faa2b 0x08ead70547dbea8a 0xdf3f7e1f1ffffe3f 0xb7cfdf87c7ffff8f

def z871 : W := mkw 0x33eedcdc83638000 0x0cfbb73720d8e000 0x6afcf8f803f1c000 0x5abf3e3e00fc7000

def z872 : W := mkw 0x03ab0c951c0c2a2b 0x00eac32547030a8a 0xf7cf0eff1c0e3e3f 0xbdf3c3bfc7038f8f

def z873 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xb1f3f7e7e0000001 0xec7cfdf9f8000000

def z874 : W := mkw 0x044fb05fe52fc27f 0xc113ec17f94bf09f 0x100ff01fe00fc03c 0x8403fc07f803f00f

def z875 : W := mkw 0x23efdc001f6f8000 0x08fbf70007dbe000 0xebfffe001fffc003 0xfaffff8007fff000

def z876 : W := mkw 0x0bb003a01ad03d80 0x02ec00e806b40f60 0xaff001e01ff03fc2 0x6bfc007807fc0ff0

def z877 : W := mkw 0x0ba00ca01ad03d80 0x02e8032806b40f60 0xeff008e01ff03fc2 0x7bfc023807fc0ff0

def z878 : W := mkw 0x23efdc141f6fa809 0x08fbf70507dbea02 0xfbfffe1f1ffff00f 0xfeffff87c7fffc03

def z879 : W := mkw 0x23efd0151f6f822b 0x08fbf40547dbe08a 0xabfff0071fffc002 0xeafffc01c7fff000

def z880 : W := mkw 0x13feefded8002800 0x04ffbbf7b6000a00 0xf7fffffffc0e3e3f 0xfdffffffff038f8f

def z881 : W := mkw 0x10102fdec0000000 0x04040bf7b0000000 0x5003ffffe0000001 0x9400fffff8000000

def z882 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x2bfff0001ff7c000 0x4afffc0007fdf000

def z883 : W := mkw 0x104ee05ec0000000 0x0413b817b0000000 0x72cff8ffe0000000 0x9cb3fe3ff8000000

def z884 : W := mkw 0x105eefdec0000000 0x0417bbf7b0000000 0xd13fffffe0000001 0xf44ffffff8000000

def z885 : W := mkw 0x23efd000076f8000 0x08fbf40001dbe000 0xabfff00003ffc000 0xeafffc0000fff000

def z886 : W := mkw 0x034f9c151d2faa2b 0x00d3e705474bea8a 0xfffffe1f1ffffe3f 0xffffff87c7ffff8f

def z887 : W := mkw 0x0bb00fa002d01580 0x02ec03e800b40560 0xeff00fe00ff00fc3 0x7bfc03f803fc03f0

def z888 : W := mkw 0x1bfeefdeda502c80 0x06ffbbf7b6940b20 0xfbfffffffff00e03 0xfefffffffffc0380

def z889 : W := mkw 0x13ba6fdec0000000 0x04ee9bf7b0000000 0x013377e7e0000000 0x004cddf9f8000000

def z890 : W := mkw 0x0bba0fa01ad43d80 0x02ee83e806b50f60 0xeffc0fe01ff63fc3 0x7bff03f807fd8ff0

def z891 : W := mkw 0x0bba0fb41ad03d80 0x02ee83ed06b40f60 0xeff30fe71ff03fc3 0x7bfcc3f9c7fc0ff0

def z892 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xffffffffe00001c3 0xfffffffff8000070

def z893 : W := mkw 0x0454a36ae19355d4 0xc11528dab864d575 0x28c081e0e381c1c0 0x4a30207838e07070

def z894 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x71f3ffffe0000001 0x5c7cfffff8000000

def z895 : W := mkw 0x03100f2018903d80 0x00c403c806240f60 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z896 : W := mkw 0x03e590001f6b8000 0x00f9640007dae000 0xabfff0001fffc002 0xeafffc0007fff000

def z897 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0xbff3f707fff9cff3 0xeffcfdc1fffe73fc

def z898 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xfffff9f8f38ff1ff 0xfffffe7e3ce3fc7f

def z899 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1533f707ec79cff1 0x854cfdc1fb1e73fc

def z900 : W := mkw 0x00a1100006688000 0x00284400019a2000 0xa9f3f0000ff9c002 0xea7cfc0003fe7000

def z901 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xfff00ff81ff03fff 0x7ffc03fe07fc0fff

def z902 : W := mkw 0x0ba000201ad03d80 0x02e8000806b40f60 0xeff009e01ff03fc3 0x7bfc027807fc0ff0

def z903 : W := mkw 0x23efd0141f6f8009 0x08fbf40507dbe002 0xabfff0181fffc00e 0xeafffc0607fff003

def z904 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xeff00fe01ffe3fff 0x7bfc03f807ff8fff

def z905 : W := mkw 0x33feefdeda440000 0x0cffbbf7b6910000 0xf3ffffffe0000001 0xfcfffffff8000000

def z906 : W := mkw 0x030b0c151e4c2a2b 0x00c2c30547930a8a 0xdf0f0e1f1ffe3e3f 0xb7c3c387c7ff8f8f

def z907 : W := mkw 0x105ee3dec0000000 0x0417b8f7b0000000 0x100ff1ffe0000000 0x8403fc7ff8000000

def z908 : W := mkw 0x20011000076b8000 0x0800440001dae000 0x8933f0000ff9c002 0xe24cfc0003fe7000

def z909 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0xaafcf00003f1c000 0xeabf3c0000fc7000

def z910 : W := mkw 0x030a0c1518042a2b 0x00c2830546010a8a 0xd70f0e1f10063e3d 0xb5c3c387c4018f8f

def z911 : W := mkw 0x24f4f36ae3f3d5d4 0xc93d3cdab8fcf575 0x28f0f1e0e3f1c1c0 0x4a3c3c7838fc7070

def z912 : W := mkw 0x03000c1518002a2b 0x00c0030546000a8a 0xd70c0e1f1c0e3e3f 0xb5c30387c7038f8f

def z913 : W := mkw 0x13feefdeda400000 0x04ffbbf7b6900000 0xf3ffffffec700001 0xfcfffffffb1c0000

def z914 : W := mkw 0x13feefded8002800 0x04ffbbf7b6000a00 0xf3fffffff0003001 0xfcfffffffc000c00

def z915 : W := mkw 0x200110011f6faa2b 0x0800440047dbea8a 0x9d33f6071ffffe3f 0xe74cfd81c7ffff8f

def z916 : W := mkw 0x101023cac0000000 0x040408f2b0000000 0x9133f7e7e0000001 0xe44cfdf9f8000000

def z917 : W := mkw 0x000110001e688000 0x00004400079a2000 0x8933f0001ff9c002 0xe24cfc0007fe7000

def z918 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf7ffffffec000e03 0xfdfffffffb000380

def z919 : W := mkw 0x20efd015076f822b 0x083bf40541dbe08a 0x38fff01f03ffc03c 0xce3ffc07c0fff00f

def z920 : W := mkw 0x23efdc001f6fa800 0x08fbf70007dbea00 0xabfff6001fffce02 0xeafffd8007fff380

def z921 : W := mkw 0x03b003201ad01580 0x00ec00c806b40560 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z922 : W := mkw 0x13feefdec1030004 0x44ffbbf7b040c001 0xf3ffffffe006000d 0xfcfffffff8018003

def z923 : W := mkw 0x204fd05da52fc27f 0xc813f417694bf09f 0x100ff01fe00fc03c 0x8403fc07f803f00f

def z924 : W := mkw 0x23efdc141f6fa809 0x08fbf70507dbea02 0xeffffe181ffffe0f 0xfbffff8607ffff83

def z925 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xa9f3f0000ff9c002 0xea7cfc0003fe7000

def z926 : W := mkw 0x03eec0001b430000 0x00fbb00006d0c000 0xabfff0001fffc002 0xeafffc0007fff000

def z927 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x2df007e01ff03fc2 0x4b7c01f807fc0ff0

def z928 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xbbfff6071fffc003 0xeefffd81c7fff000

def z929 : W := mkw 0x33efd0c89f6f8000 0x0cfbf43227dbe000 0xabfff0e01fffc002 0xeafffc3807fff000

def z930 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x76cc89f8f38ff1fd 0x9db3227e3ce3fc7f

def z931 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf3fffffff006300d 0xfcfffffffc018c03

def z932 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x73ff7fffe0000001 0x1cffdffff8000000

def z933 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xaffff6071ffffe3e 0xebfffd81c7ffff8f

def z934 : W := mkw 0x0bba0fb41ad03d80 0x02ee83ed06b40f60 0xeffc0ff81ff03fc3 0x7bff03fe07fc0ff0

def z935 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0xaaf0f00013f1c002 0x6abc3c0004fc7000

def z936 : W := mkw 0x13ba6fdec0000000 0x04ee9bf7b0000000 0xd33f7fffe0000001 0xb4cfdffff8000000

def z937 : W := mkw 0x23efdc801f6f8000 0x08fbf72007dbe000 0xebfff8e01fffc002 0xfafffe3807fff000

def z938 : W := mkw 0x23efd0489f6f8000 0x08fbf41227dbe000 0xabfff1e0ffffc002 0xeafffc783ffff000

def z939 : W := mkw 0x0410236ae09055d4 0xc10408dab8241575 0x000001e0e00001c0 0x0000007838000070

def z940 : W := mkw 0x23efd0001f6fa800 0x08fbf40007dbea00 0xaffff0001ffffe02 0xebfffc0007ffff80

def z941 : W := mkw 0x23efdc141f6fa809 0x08fbf70507dbea02 0xfffff8181ffff03f 0xfffffe0607fffc0f

def z942 : W := mkw 0x035eaf5ec0000000 0x00d7abd7b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z943 : W := mkw 0x23eed0001b678000 0x08fbb40006d9e000 0xaafcf00013ffc002 0xeabf3c0004fff000

def z944 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x73fffeffe0000000 0x9cffffbff8000000

def z945 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xeff08fe01ff9ffc3 0xfbfc23f807fe7ff0

def z946 : W := mkw 0x23efd0011f6faa2b 0x08fbf40047dbea8a 0xfffff8181ffffe3f 0xfffffe0607ffff8f

def z947 : W := mkw 0x03ab10001e6c8000 0x00eac400079b2000 0xabfff0001fffc002 0xeafffc0007fff000

def z948 : W := mkw 0x2000100003638000 0x0800040000d8e000 0x0830f00003f1c000 0x420c3c0000fc7000

def z949 : W := mkw 0x10f4e3cac0000000 0x043d38f2b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z950 : W := mkw 0x13feefded8042809 0x04ffbbf7b6010a02 0xf7fffffff00e303f 0xfdfffffffc038c0f

def z951 : W := mkw 0x00459000052b8000 0x00116400014ae000 0xa9f3f0000ff9c002 0xea7cfc0003fe7000

def z952 : W := mkw 0x13feefdeda400000 0x04ffbbf7b6900000 0xf3fffffff3800001 0xfcfffffffce00000

def z953 : W := mkw 0x00010c151c0c2a2b 0x0000430547030a8a 0xd60c0e1f1c0e3e3f 0xb5830387c7038f8f

def z954 : W := mkw 0x33feefdec3430000 0x0cffbbf7b0d0c000 0xf3ffffffe3800001 0xfcfffffff8e00000

def z955 : W := mkw 0x03f4afcac0000000 0x00fd2bf2b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z956 : W := mkw 0x0401102124b8d7f6 0xc1004408492e35fd 0x0c0000000c79fffe 0x03000000031e7fff

def z957 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf3ffffffe00e003d 0xfcfffffff803800f

def z958 : W := mkw 0x33feefdec1070000 0x0cffbbf7b041c000 0xf3ffffffe0060001 0xfcfffffff8018000

def z959 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0xfefcf81813fff03f 0xffbf3e0604fffc0f

def z960 : W := mkw 0x13feefdec1030000 0x04ffbbf7b040c000 0xf3fffffff3860001 0xfcfffffffce18000

def z961 : W := mkw 0x10102fdec0000000 0x04040bf7b0000000 0x51337fffe0000001 0x144cdffff8000000

def z962 : W := mkw 0x23efdc001f6fa800 0x08fbf70007dbea00 0xebfff8001ffff002 0xfafffe0007fffc00

def z963 : W := mkw 0x0c1023a2609055d0 0x830408e898241574 0x000001e0e00001c0 0x0000007838000070

def z964 : W := mkw 0x23efdc151f6f8222 0x08fbf70547dbe088 0xfffffe1f1fffce33 0xffffff87c7fff38c

def z965 : W := mkw 0x105ee35ec0000000 0x0417b8d7b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z966 : W := mkw 0x0c102febe0907ff6 0xc3040bfaf8241ffd 0x54000fffe0003ffd 0x150003fff8000fff

def z967 : W := mkw 0x23ab50001e6c8000 0x08ead400079b2000 0xabf3f0001ff9c002 0xeafcfc0007fe7000

def z968 : W := mkw 0x23ab50001f6f8000 0x08ead40007dbe000 0x093370000ff1c000 0x024cdc0003fc7000

def z969 : W := mkw 0x10fee3dec0000000 0x043fb8f7b0000000 0x20f3f1e7e0000000 0x483cfc79f8000000

def z970 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xadf007e00ff00fc3 0x6b7c01f803fc03f0

def z971 : W := mkw 0x13feefdec0002809 0x04ffbbf7b0000a02 0xf3ffffffe000300d 0xfcfffffff8000c03

def z972 : W := mkw 0x23ab50001f6f8000 0x08ead40007dbe000 0x8933f0001fffc002 0xe24cfc0007fff000

def z973 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xfffc0ff81ff03fc3 0xffff03fe07fc0ff0

def z974 : W := mkw 0x23e4d0001b638000 0x08f9340006d8e000 0xabfcf0001fffc002 0xeaff3c0007fff000

def z975 : W := mkw 0x20e5d000076f8000 0x0839740001dbe000 0x28f0f00003ffc000 0x4a3c3c0000fff000

def z976 : W := mkw 0x13fee3dec0000000 0x04ffb8f7b0000000 0xb3fff1ffe0000000 0xecfffc7ff8000000

def z977 : W := mkw 0x23e4d0001b638000 0x08f9340006d8e000 0x2af0f00013f1c000 0x4abc3c0004fc7000

def z978 : W := mkw 0x000a0c1500042a2b 0x0002830540010a8a 0x540c0e1f00063e3d 0x15030387c0018f8f

def z979 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x9933f707ec71cfc1 0xe64cfdc1fb1c73f0

def z980 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xeffc0fe01ffe3fc3 0xfbff03f807ff8ff0

def z981 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1d33f607ec79cff2 0x874cfd81fb1e73fc

def z982 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xaffff6001fffce03 0xebfffd8007fff380

def z983 : W := mkw 0x20efd0001f6f8000 0x083bf40007dbe000 0x28fff0001fffc002 0xca3ffc0007fff000

def z984 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xfbffffffec700003 0xfefffffffb1c0000

def z985 : W := mkw 0x23e4d0001b638000 0x08f9340006d8e000 0x29f0f0000ff1c000 0x4a7c3c0003fc7000

def z986 : W := mkw 0x0bba0fb41ad03d80 0x02ee83ed06b40f60 0xffff0fff1ffe3fff 0xffffc3ffc7ff8fff

def z987 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x2afcf0001fffc002 0x4abf3c0007fff000

def z988 : W := mkw 0x0c0110213efcfffb 0x830044084fbf3ffe 0x0c0000001ffffffe 0x0300000007ffffff

def z989 : W := mkw 0x03b00f801a500480 0x00ec03e006940120 0xeff00fe01ff00fc3 0x7bfc03f807fc03f0

def z990 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xffcf0e1f1f8e3e3f 0xfff3c387c7e38f8f

def z991 : W := mkw 0x0000000100000222 0x0000000040000088 0xd60c0e1f100e3e3f 0xb5830387c4038f8f

def z992 : W := mkw 0x0401102125bbd7f6 0xc1004408496ef5fd 0x0c0000000ff9cff2 0x0300000003fe73fc

def z993 : W := mkw 0x030a0c1500002a2b 0x00c2830540000a8a 0xd70f0e1f100e3e3f 0xb5c3c387c4038f8f

def z994 : W := mkw 0x1c102fffe0907ff2 0x87040bfff8241ffc 0x54000fffe0003ff1 0x150003fff8000ffc

def z995 : W := mkw 0x33feefdedb470000 0x0cffbbf7b6d1c000 0xfbfffffffff60003 0xfefffffffffd8000

def z996 : W := mkw 0x104ee05ec0000000 0x0413b817b0000000 0x30cff1ffe0000000 0xcc33fc7ff8000000

def z997 : W := mkw 0x13feefded8002800 0x04ffbbf7b6000a00 0xf3ffffffec000e01 0xfcfffffffb000380

def z998 : W := mkw 0x13eee05ec0000000 0x04fbb817b0000000 0xf3fff9ffe0000001 0xfcfffe7ff8000000

def z999 : W := mkw 0x0f1b2fb77c9c7ffb 0x83c6cbeddf271ffe 0xd70f0ffffc0e3fff 0xb5c3c3ffff038fff

def z1000 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xbffff0001fffc033 0xeffffc0007fff00c

def z1001 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf7ffffffe000303d 0xfdfffffff8000c0f

def z1002 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x72fff9ffe0000000 0xdcbffe7ff8000000

def z1003 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x550f0e1f0c0e3e3d 0x9543c387c3038f8f

def z1004 : W := mkw 0x0fbb3f975e7caeab 0x03eecfe5d79f2baa 0x013376070c700e00 0x004cdd81c31c0380

def z1005 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xbffff6071fffce33 0xeffffd81c7fff38c

def z1006 : W := mkw 0x08b003a002d01580 0x022c00e800b40560 0x29f007e00ff00fc0 0x4a7c01f803fc03f0

def z1007 : W := mkw 0x33efdcdc9f6fa809 0x0cfbf73727dbea02 0xebfff8f81ffff00e 0xfafffe3e07fffc03

def z1008 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xebfff9e01fffc003 0xfafffe7807fff000

def z1009 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xfbfffffff3800003 0xfefffffffce00000

def z1010 : W := mkw 0x230b1c151f6faa2b 0x08c2c70547dbea8a 0xdf3ffe1f1ffffe3f 0xf7cfff87c7ffff8f

def z1011 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x470f0e1f1c0e3e3e 0x11c3c387c7038f8f

def z1012 : W := mkw 0x13feefded8000000 0x04ffbbf7b6000000 0xf3fffffffc000003 0xfcffffffff000000

def z1013 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xeffff8001ffff003 0xfbfffe0007fffc00

def z1014 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xbbfff100ffffc003 0xeefffc403ffff000

def z1015 : W := mkw 0x08b00fa01ad03d80 0x022c03e806b40f60 0x6cf00fe01ff03fc3 0x5b3c03f807fc0ff0

def z1016 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xaffff1001fffc1c3 0xebfffc4007fff070

def z1017 : W := mkw 0x134eec5ec0000000 0x04d3bb17b0000000 0xf3cfffffe0000001 0xfcf3fffff8000000

def z1018 : W := mkw 0x00459001052b8222 0x00116400414ae088 0xfffffe1f1ffffe3f 0xffffff87c7ffff8f

def z1019 : W := mkw 0x20e5d000076b8000 0x0839740001dae000 0x28f3f00003f9c000 0xca3cfc0000fe7000

def z1020 : W := mkw 0x10f4e3cac0000000 0x043d38f2b0000000 0x30f3f1e7e0000000 0xcc3cfc79f8000000

def z1021 : W := mkw 0x03fee34ac0000000 0x00ffb8d2b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z1022 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xeffffe071ffffe03 0xfbffff81c7ffff80

def z1023 : W := mkw 0x081023225ad03d80 0x020408c896b40f60 0x9d33f707fff03fc3 0xe74cfdc1fffc0ff0

def z1024 : W := mkw 0x20e5d0001f6f8000 0x0839740007dbe000 0xa9f3f0001fffc002 0xea7cfc0007fff000

def z1025 : W := mkw 0x23efdc141f6fa809 0x08fbf70507dbea02 0xabfff0001fffc002 0xeafffc0007fff000

def z1026 : W := mkw 0x14f4f3eae1b3d5d4 0xc53d3cfab86cf575 0x28f0f1e0e3f1c1c0 0x4a3c3c7838fc7070

def z1027 : W := mkw 0x1bba4fb41ad03d80 0x06ee93ed06b40f60 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z1028 : W := mkw 0x23efd0011f6faa2b 0x08fbf40047dbea8a 0xabfff0001fffce02 0xeafffc0007fff380

def z1029 : W := mkw 0x23e5d0001f6f8000 0x08f9740007dbe000 0xabf0f0001fffc002 0x6afc3c0007fff000

def z1030 : W := mkw 0x240110213fffd7f6 0xc90044084ffff5fd 0x0c0000001ffffffe 0x0300000007ffffff

def z1031 : W := mkw 0x23ab5c151e6caa2b 0x08ead705479b2a8a 0xdf3ffe1f1c7ffe3f 0xf7cfff87c71fff8f

def z1032 : W := mkw 0x23ab50001f6f8000 0x08ead40007dbe000 0xabf370001fffc002 0x6afcdc0007fff000

def z1033 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0x6ecc89f8f38ff1fe 0x5bb3227e3ce3fc7f

def z1034 : W := mkw 0x20efd000076f8000 0x083bf40001dbe000 0xa9fff0000fffc002 0xea7ffc0003fff000

def z1035 : W := mkw 0x23eed0001b638000 0x08fbb40006d8e000 0xabfff0001ff1c002 0xeafffc0007fc7000

def z1036 : W := mkw 0x0bba0fa01ad03d80 0x02ee83e806b40f60 0xefff0fe01ff03fc3 0xfbffc3f807fc0ff0

def z1037 : W := mkw 0x030b1c151c2caa2b 0x00c2c705470b2a8a 0xdf0f0e1f1c7ffe3f 0xb7c3c387c71fff8f

def z1038 : W := mkw 0x000b0c151c0c2a2b 0x0002c30547030a8a 0x540f0e1f1c0e3e3f 0x9503c387c7038f8f

def z1039 : W := mkw 0x0bb00fa01ad43d89 0x02ec03e806b50f62 0xeff00fe01ff63fcf 0x7bfc03f807fd8ff3

def z1040 : W := mkw 0x13feefdec0100480 0x04ffbbf7b0040120 0xf7ffffffe0000fc1 0xfdfffffff80003f0

def z1041 : W := mkw 0x1bba6fb65ad03d80 0x06ee9bed96b40f60 0xfff3ffe7fff03fc3 0xfffcfff9fffc0ff0

def z1042 : W := mkw 0x23efd0141f6f8000 0x08fbf40507dbe000 0xbbfff01f1fffc002 0xeefffc07c7fff000

def z1043 : W := mkw 0x04102f7fe0907fff 0xc1040bdff8241fff 0x54000fffe0003ffd 0x150003fff8000fff

def z1044 : W := mkw 0x1bfeefdeda402800 0x06ffbbf7b6900a00 0xf3ffffffe0000001 0xfcfffffff8000000

def z1045 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0x28fcf00003ffc000 0xca3f3c0000fff000

def z1046 : W := mkw 0x13ab4c951c0c2a2b 0x04ead32547030a8a 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z1047 : W := mkw 0x00010c1504082a2b 0x0000430541020a8a 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z1048 : W := mkw 0x030b1c151c2caa2b 0x00c2c705470b2a8a 0xd70ffe1f1c0ffe3f 0xb5c3ff87c703ff8f

def z1049 : W := mkw 0x10f4efdec0000000 0x043d3bf7b0000000 0xf1f3ffffe0000001 0xfc7cfffff8000000

def z1050 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xdf3f0e1f1c7e3e3f 0xf7cfc387c71f8f8f

def z1051 : W := mkw 0x03efd0001e688000 0x00fbf400079a2000 0xabfff0001ff9c002 0xeafffc0007fe7000

def z1052 : W := mkw 0x20e4d0001b678000 0x0839340006d9e000 0x28f0f00013f7c000 0x4a3c3c0004fdf000

def z1053 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xaffff0001ffff03e 0xebfffc0007fffc0f

def z1054 : W := mkw 0x101a6fdec0000000 0x04069bf7b0000000 0x50037fffe0000001 0x1400dffff8000000

def z1055 : W := mkw 0x10eee0dec0000000 0x043bb837b0000000 0x30cff0ffe0000000 0x8c33fc3ff8000000

def z1056 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x31fff7ffe0000000 0xcc7ffdfff8000000

def z1057 : W := mkw 0x23a110001f6f8000 0x08e8440007dbe000 0xabf3f0001fffc002 0xeafcfc0007fff000

def z1058 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x6df00fe00ff03fc1 0x5b7c03f803fc0ff0

def z1059 : W := mkw 0x03ab0c151e4c2a2b 0x00eac30547930a8a 0xf7cf0e1f1f8e3e3f 0xbdf3c387c7e38f8f

def z1060 : W := mkw 0x23efdc5c9f6f8000 0x08fbf71727dbe000 0xfbffffffffffc003 0xfefffffffffff000

def z1061 : W := mkw 0x0445b04be52bc276 0xc1116c12f94af09d 0x1003f007e009c030 0x8400fc01f802700c

def z1062 : W := mkw 0x204fd0001f6f8000 0x0813f40007dbe000 0x893ff0001fffc002 0xe24ffc0007fff000

def z1063 : W := mkw 0x23efdc141f6fa800 0x08fbf70507dbea00 0xfffffe1f1ffffe03 0xffffff87c7ffff80

def z1064 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0x28f0f00013ffc002 0x4a3c3c0004fff000

def z1065 : W := mkw 0x20eed00003678000 0x083bb40000d9e000 0x28fcf00003f7c000 0x4a3f3c0000fdf000

def z1066 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xeff3ffe01ff03fc3 0xfbfcfff807fc0ff0

def z1067 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xd73ffe1f1c0e3e3f 0xf5cfff87c7038f8f

def z1068 : W := mkw 0x13b02fdec0000000 0x04ec0bf7b0000000 0xf3f3ffffe0000001 0xfcfcfffff8000000

def z1069 : W := mkw 0x0bb02fa25ad03d80 0x02ec0be896b40f60 0xfff00fe7fff03fc3 0x7ffc03f9fffc0ff0

def z1070 : W := mkw 0x03ab0c151c0c2a2b 0x00eac30547030a8a 0xf7ff0e1f1c0e3e3f 0xfdffc387c7038f8f

def z1071 : W := mkw 0x3beeccfc9bc73900 0x0efbb33f26f1ce40 0x62cc08f813863000 0x18b3023e04e18c00

def z1072 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x8933f707ec79cfc2 0xe24cfdc1fb1e73f0

def z1073 : W := mkw 0x08b003a01ad03d80 0x022c00e806b40f60 0xadf007e01ff03fc3 0x6b7c01f807fc0ff0

def z1074 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xabfff0000ff1c000 0xeafffc0003fc7000

def z1075 : W := mkw 0x08100fa01ad03d80 0x020403e806b40f60 0xeec00fe01ff03fc3 0x7bb003f807fc0ff0

def z1076 : W := mkw 0x23e5d0001f6b8000 0x08f9740007dae000 0xabf3f0001ff9c002 0xeafcfc0007fe7000

def z1077 : W := mkw 0x000100011c0c2a2b 0x0000400047030a8a 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z1078 : W := mkw 0x0410236ae09055d4 0xc10408dab8241575 0x540009f8e00031fd 0x1500027e38000c7f

def z1079 : W := mkw 0x23ab50001f6f8000 0x08ead40007dbe000 0x8b3f70001fffc002 0xa2cfdc0007fff000

def z1080 : W := mkw 0x13ba6f9640000000 0x04ee9be590000000 0xf3f3ffe7e0000001 0xfcfcfff9f8000000

def z1081 : W := mkw 0x23efd0489f6f8004 0x48fbf41227dbe001 0xabfff0181fffc00e 0xeafffc0607fff003

def z1082 : W := mkw 0x2bba4fa01ad43d80 0x0aee93e806b50f60 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z1083 : W := mkw 0x23efd000076b8000 0x08fbf40001dae000 0xabfff0000ff9c002 0xeafffc0003fe7000

def z1084 : W := mkw 0x0000002020805150 0x8000000808201454 0xfecc89f8f38ff1ff 0xffb3227e3ce3fc7f

def z1085 : W := mkw 0x00448068a1835154 0xc011201a2860d455 0xffcc8ff8ff8fffff 0xfff323fe3fe3ffff

def z1086 : W := mkw 0x230b10001f6f8000 0x08c2c40007dbe000 0x8b3ff0001fffc002 0xe2cffc0007fff000

def z1087 : W := mkw 0x23efd0011f6faa2b 0x08fbf40047dbea8a 0xbffff6071ffffe3f 0xeffffd81c7ffff8f

def z1088 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xabf3f0001ff1c002 0x6afcfc0007fc7000

def z1089 : W := mkw 0x20e5d0011f6faa2b 0x0839740047dbea8a 0x2cf0f0001ffffe3e 0x4b3c3c0007ffff8f

def z1090 : W := mkw 0x1bfeefdeda502c80 0x06ffbbf7b6940b20 0xf7fffffffc703e03 0xfdffffffff1c0f80

def z1091 : W := mkw 0x204fd000052f8000 0x0813f400014be000 0xabfff0001fffc002 0xeafffc0007fff000

def z1092 : W := mkw 0x0044900001238000 0x001124000048e000 0x28f0f00003f1c000 0x4a3c3c0000fc7000

def z1093 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xd70f8f1ffc0e3e3f 0xf5c3e3c7ff038f8f

def z1094 : W := mkw 0x18102ffee0907dd4 0xc6040bffb8241f75 0x54000fffe0003ffd 0x150003fff8000fff

def z1095 : W := mkw 0x20eed00003638000 0x083bb40000d8e000 0x28fff00003f1c000 0xca3ffc0000fc7000

def z1096 : W := mkw 0x00000c1500002a2b 0x0000030540000a8a 0x540c0e1f000e3e3d 0x95030387c0038f8f

def z1097 : W := mkw 0x03ba2f9640000000 0x00ee8be590000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z1098 : W := mkw 0x23efdc141f6f8000 0x08fbf70507dbe000 0xebfff8181fffc002 0xfafffe0607fff000

def z1099 : W := mkw 0x0bba0fb41ad43d89 0x02ee83ed06b50f62 0xffff0fff1ff63fcf 0xffffc3ffc7fd8ff3

def z1100 : W := mkw 0x23eed00003638000 0x08fbb40000d8e000 0x2afcf00003f1c000 0x4abf3c0000fc7000

def z1101 : W := mkw 0x13feefdec1030000 0x04ffbbf7b040c000 0xf3ffffffe00fc001 0xfcfffffff803f000

def z1102 : W := mkw 0x080000201ad03d80 0x0200000806b40f60 0x2cc001e01ff03fc2 0x4b30007807fc0ff0

def z1103 : W := mkw 0x23eed0001b678000 0x08fbb40006d9e000 0xabfcf0001ff7c002 0x6aff3c0007fdf000

def z1104 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x560c0e1f1c0e3e3f 0x15830387c7038f8f

def z1105 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xe3f3ffe7e0000001 0x78fcfff9f8000000

def z1106 : W := mkw 0x08b003a002d01580 0x022c00e800b40560 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z1107 : W := mkw 0x03ab0c151e4c2a2b 0x00eac30547930a8a 0xd73f0e1f1c7e3e3f 0xb5cfc387c71f8f8f

def z1108 : W := mkw 0x13feefded8042809 0x04ffbbf7b6010a02 0xf7fffffffc063e0f 0xfdffffffff018f83

def z1109 : W := mkw 0x030b0c1504080222 0x00c2c30541020088 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z1110 : W := mkw 0x13feefdec0100480 0x04ffbbf7b0040120 0xf3ffffffec700e01 0xfcfffffffb1c0380

def z1111 : W := mkw 0x0c01102124b8fff2 0x83004408492e3ffc 0x0c0000000c79fff2 0x03000000031e7ffc

def z1112 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xf7cf0fff1c0e3e3f 0xfdf3c3ffc7038f8f

def z1113 : W := mkw 0x04102323609057f2 0x810408c8d82415fc 0x54000fe7e0003ff1 0x150003f9f8000ffc

def z1114 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0xdf3fff1fec79cff3 0xf7cfffc7fb1e73fc

def z1115 : W := mkw 0x23efd0011f6f8222 0x08fbf40047dbe088 0xabfff6071fffce02 0xeafffd81c7fff380

def z1116 : W := mkw 0x1054afdec0000000 0x04152bf7b0000000 0xf3ffffffe0000001 0xfcfffffff8000000

def z1117 : W := mkw 0x0c1023a3609057f2 0x830408e8d82415fc 0x140007e7e0000ff1 0x050001f9f80003fc

def z1118 : W := mkw 0x0010230240000000 0x000408c090000000 0xf3f3ffe7e0000001 0xfcfcfff9f8000000

def z1119 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x093ff0001fffc002 0x824ffc0007fff000

def z1120 : W := mkw 0x0054a34ac0000000 0x001528d2b0000000 0xb1f3f7e7e0000001 0xec7cfdf9f8000000

def z1121 : W := mkw 0x2befdc801f6fa800 0x0afbf72007dbea00 0xabfff0001fffc002 0xeafffc0007fff000

def z1122 : W := mkw 0x23efd0011f6f822b 0x08fbf40047dbe08a 0xabfff0001fffc03e 0xeafffc0007fff00f

def z1123 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x9f3ff707fc7fcff3 0xe7cffdc1ff1ff3fc

def z1124 : W := mkw 0x13feefded8102c80 0x04ffbbf7b6040b20 0xfffffffffc703fc3 0xffffffffff1c0ff0

def z1125 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x6ec00fe01ff03fc3 0x1bb003f807fc0ff0

def z1126 : W := mkw 0x0c01102126f8d7f2 0x8300440849be35fc 0x0c0000000ff9cff2 0x0300000003fe73fc

def z1127 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xfbfffe1f1fffce03 0xfeffff87c7fff380

def z1128 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0xa9f3f00003f1c000 0xea7cfc0000fc7000

def z1129 : W := mkw 0x0b000c201ad03d80 0x02c0030806b40f60 0xefc00fe01ff03fc3 0x7bf003f807fc0ff0

def z1130 : W := mkw 0x20efd000076f8000 0x083bf40001dbe000 0xaafff00013ffc002 0xeabffc0004fff000

def z1131 : W := mkw 0x13feefded8040000 0x04ffbbf7b6010000 0xf3fffffff0060001 0xfcfffffffc018000

def z1132 : W := mkw 0x10feefdec0000000 0x043fbbf7b0000000 0x70ffffffe0000001 0xdc3ffffff8000000

def z1133 : W := mkw 0x23e4d00003638000 0x08f9340000d8e000 0xabf0f00003f1c000 0x6afc3c0000fc7000

def z1134 : W := mkw 0x0bb02fa25ad03d80 0x02ec0be896b40f60 0xeff37fe71ff03fc3 0x7bfcdff9c7fc0ff0

def z1135 : W := mkw 0x200110001f6f8000 0x0800440007dbe000 0x093370001fffc002 0x024cdc0007fff000

def z1136 : W := mkw 0x14102fffe09057f6 0xc5040bfff82415fd 0x54000fffe0003ffd 0x150003fff8000fff

def z1137 : W := mkw 0x0044a04ac0000000 0x00112812b0000000 0xf2cff9ffe0000001 0xfcb3fe7ff8000000

def z1138 : W := mkw 0x23efdc011f6faa2b 0x08fbf70047dbea8a 0xeffffe001ffffe3f 0xfbffff8007ffff8f

def z1139 : W := mkw 0x20efd000076f8000 0x083bf40001dbe000 0x28f3f00003f1c000 0x4a3cfc0000fc7000

def z1140 : W := mkw 0x104eecdec0000000 0x0413bb37b0000000 0x500ff8ffe0000000 0x9403fe3ff8000000

def z1141 : W := mkw 0x03a11c011e68aa22 0x00e84700479a2a88 0xfff3fe071ff9fe33 0xfffcff81c7fe7f8c

def z1142 : W := mkw 0x20a150001f6f8000 0x0828540007dbe000 0x083070001fffc002 0x020c1c0007fff000

def z1143 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf3fffffff00e0003 0xfcfffffffc038000

def z1144 : W := mkw 0x08a000a01ad03d80 0x0228002806b40f60 0x2cc000e01ff03fc2 0x0b30003807fc0ff0

def z1145 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0xfff00fe01ff83ff3 0xfffc03f807fe0ffc

def z1146 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0x63ffffffe0000000 0x58fffffff8000000

def z1147 : W := mkw 0x1bfeefdec2500480 0x06ffbbf7b0940120 0xf3ffffffe0700001 0xfcfffffff81c0000

def z1148 : W := mkw 0x23efdc141f6f8000 0x08fbf70507dbe000 0xfffffe1f1ffff03f 0xffffff87c7fffc0f

def z1149 : W := mkw 0x13f4efcac0000000 0x04fd3bf2b0000000 0xf3f3ffe7e0000001 0xfcfcfff9f8000000

def z1150 : W := mkw 0x20e5d000076b8000 0x0839740001dae000 0x28f0f0000ff9c002 0x4a3c3c0003fe7000

def z1151 : W := mkw 0x244ff04be52fc276 0xc913fc12f94bf09d 0x100ff01fe00fc03c 0x8403fc07f803f00f

def z1152 : W := mkw 0x00011000052b8000 0x00004400014ae000 0x8933f0001fffc002 0xe24cfc0007fff000

def z1153 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x6ef009e01ff03fc2 0x5bbc027807fc0ff0

def z1154 : W := mkw 0x23eedc141b67a809 0x08fbb70506d9ea02 0x6afcf81813f7f00c 0x5abf3e0604fdfc03

def z1155 : W := mkw 0x0410236be09057f6 0xc10408daf82415fd 0x140007e7e0000ff1 0x050001f9f80003fc

def z1156 : W := mkw 0x33efdcdc9f6f8000 0x0cfbf73727dbe000 0xfbfffeff1fffc003 0xfeffffbfc7fff000

def z1157 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xbbfff0181fffc03e 0xeefffc0607fff00f

def z1158 : W := mkw 0x081003201ad03d80 0x020400c806b40f60 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z1159 : W := mkw 0x20e5d000076b8000 0x0839740001dae000 0xabfff0001fffc002 0xeafffc0007fff000

def z1160 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x150f061f1c0e3e3e 0x8543c187c7038f8f

def z1161 : W := mkw 0x040110213dbfffff 0xc10044084f6fffff 0x0c0000001ffffffe 0x0300000007ffffff

def z1162 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x67f00fe01ff03fc1 0x19fc03f807fc0ff0

def z1163 : W := mkw 0x030b00011c0c0222 0x00c2c00047030088 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z1164 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x9d3ff71fec7fcfff 0xe74ffdc7fb1ff3ff

def z1165 : W := mkw 0x13feefded8042809 0x04ffbbf7b6010a02 0xf3ffffffe0000001 0xfcfffffff8000000

def z1166 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xbbfff61f1fffce3e 0xeefffd87c7fff38f

def z1167 : W := mkw 0x0bb02fa25ad03d80 0x02ec0be896b40f60 0xeff0ffe0fff03fc3 0x7bfc3ff83ffc0ff0

def z1168 : W := mkw 0x0011330244388480 0x00044cc0910e2120 0x9d33f707ec79cfc3 0xe74cfdc1fb1e73f0

def z1169 : W := mkw 0x0411236be49857f6 0xc10448daf92615fd 0xd70f0ffffc0e3fff 0xb5c3c3ffff038fff

def z1170 : W := mkw 0x23efd0489f6f8000 0x08fbf41227dbe000 0xebfff8f81fffc002 0xfafffe3e07fff000

def z1171 : W := mkw 0x20e5d000076b8000 0x0839740001dae000 0x29f3f0000ff1c000 0x4a7cfc0003fc7000

def z1172 : W := mkw 0x0bb00fb41ad03d80 0x02ec03ed06b40f60 0xfff00fff1ff03fc3 0x7ffc03ffc7fc0ff0

def z1173 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0xdf0f0f1f1c0e3fff 0xf7c3c3c7c7038fff

def z1174 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0x1933f707ec79cff0 0xc64cfdc1fb1e73fc

def z1175 : W := mkw 0x344ff05fe52fc272 0x8d13fc17f94bf09c 0x100ff01fe00fc030 0x8403fc07f803f00c

def z1176 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0xebfff8181ffff00e 0xfafffe0607fffc03

def z1177 : W := mkw 0x0c0110213ffbfff6 0xc30044084ffefffd 0x0c0000001ffffffe 0x0300000007ffffff

def z1178 : W := mkw 0x13feefdec0040009 0x04ffbbf7b0010002 0xf3ffffffe006000d 0xfcfffffff8018003

def z1179 : W := mkw 0x030b0c151c0c2a2b 0x00c2c30547030a8a 0x560f0e1f100e3e3d 0x9583c387c4038f8f

def z1180 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x29fff0000fffc000 0xca7ffc0003fff000

def z1181 : W := mkw 0x23efd0489f6f8000 0x08fbf41227dbe000 0xbbfff018ffffc002 0xeefffc063ffff000

def z1182 : W := mkw 0x10fee3dec0000000 0x043fb8f7b0000000 0xf2fff9ffe0000001 0xfcbffe7ff8000000

def z1183 : W := mkw 0x08100fa000903d80 0x020403e800240f60 0xeff00fe01ff03fc3 0x7bfc03f807fc0ff0

def z1184 : W := mkw 0x20e4d04883638000 0x0839341220d8e000 0xfafcf9f8e3f1c001 0xfebf3e7e38fc7000

def z1185 : W := mkw 0x08b003a01ad03d80 0x022c00e806b40f60 0x28f001e00ff00fc0 0x4a3c007803fc03f0

def z1186 : W := mkw 0x0bb00fb41ad03d89 0x02ec03ed06b40f62 0xeff00ff81ff03fcf 0x7bfc03fe07fc0ff3

def z1187 : W := mkw 0x03ab4c151c0c2a2b 0x00ead30547030a8a 0xd73f7e1f1c0e3e3f 0xb5cfdf87c7038f8f

def z1188 : W := mkw 0x13eeecdec0000000 0x04fbbb37b0000000 0xf3cffeffe0000001 0xbcf3ffbff8000000

def z1189 : W := mkw 0x0ba00ca01ad03d80 0x02e8032806b40f60 0xefc00ee01ff03fc3 0x3bf003b807fc0ff0

def z1190 : W := mkw 0x0c10232360907ff2 0x830408c8d8241ffc 0x14000707e0003ff1 0x050001c1f8000ffc

def z1191 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xebfffe1f1ffffe0e 0xfaffff87c7ffff83

def z1192 : W := mkw 0x041033026030c4d0 0x81040cc0980c3134 0x9d33f707ec71cfc3 0xe74cfdc1fb1c73f0

def z1193 : W := mkw 0x041133036438c6f2 0x81044cc0d90e31bc 0xdd33ff1fec79ffff 0xf74cffc7fb1e7fff

def z1194 : W := mkw 0x20e4d00003638000 0x0839340000d8e000 0x2afcf00013f7c000 0x4abf3c0004fdf000

def z1195 : W := mkw 0x0c102fb760907ffb 0x83040bedd8241ffe 0x54000fffe0003ffd 0x150003fff8000fff

def z1196 : W := mkw 0x13feefdec0000000 0x04ffbbf7b0000000 0xf7fffffff0003003 0xfdfffffffc000c00

def z1197 : W := mkw 0x18f4e3eae3d355d4 0xc63d38fab8f4d575 0x28f0f1e0e3f1c1c0 0x4a3c3c7838fc7070

def z1198 : W := mkw 0x23ab4c151e4c2a2b 0x08ead30547930a8a 0xd70f0e1f1c0e3e3f 0xb5c3c387c7038f8f

def z1199 : W := mkw 0x23eed00003638000 0x08fbb40000d8e000 0x29f3f00003f1c000 0x4a7cfc0000fc7000

def z1200 : W := mkw 0x23efd0001f6f8000 0x08fbf40007dbe000 0x29f3f0001fffc002 0x4a7cfc0007fff000

def z1201 : W := mkw 0x0bb00fa01ad03d80 0x02ec03e806b40f60 0x6ff00ee01ff03fc2 0x1bfc03b807fc0ff0

def z1202 : W := mkw 0x23efdc151f6faa2b 0x08fbf70547dbea8a 0xfbfff81f1ffff03e 0xfefffe07c7fffc0f

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z9,z3,z4,z8,z6])],[(0,[z1,z2,z3,z10,z8,z11,z6])],[(0,[z1,z12,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z14,z4,z8,z15]),(0,[z1,z2,z3,z4,z16,z8,z13]),(0,[z17,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z18,z19,z6]),(0,[z1,z2,z3,z4,z8,z20,z6]),(0,[z1,z2,z3,z4,z8,z6,z21])],[(0,[z1,z2,z3,z4,z8,z22,z23]),(1,[z1,z2,z3,z24,z8,z6]),(0,[z1,z2,z3,z4,z8,z25,z6]),(0,[z1,z2,z3,z4,z26,z8,z6]),(0,[z27,z1,z2,z3,z4,z8,z28])],[(0,[z1,z2,z3,z29,z4,z8,z6]),(0,[z30,z1,z2,z3,z4,z31,z6]),(0,[z32,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z33,z6]),(0,[z1,z2,z3,z18,z4,z8,z15]),(0,[z1,z2,z3,z4,z34,z8,z6]),(0,[z35,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z36,z3,z4,z37,z6])],[(1,[z1,z2,z3,z29,z8,z6]),(0,[z38,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z39,z4,z8,z6]),(0,[z1,z2,z3,z40,z8,z41,z6]),(0,[z1,z2,z42,z3,z4,z8,z6]),(0,[z1,z43,z2,z3,z4,z8,z6]),(0,[z1,z2,z44,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z45,z13]),(0,[z1,z2,z3,z4,z37,z8,z6])],[(0,[z1,z2,z3,z4,z46,z8,z6]),(1,[z1,z2,z47,z3,z4,z8]),(0,[z48,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z49,z3,z4,z8,z6]),(0,[z1,z50,z2,z3,z4,z8,z6]),(0,[z1,z51,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z52,z8,z6])],[(0,[z1,z53,z2,z3,z4,z8,z6]),(0,[z54,z1,z2,z3,z4,z8,z6]),(0,[z55,z1,z2,z3,z4,z8,z6]),(0,[z56,z1,z2,z57,z3,z8,z6]),(0,[z1,z2,z58,z3,z4,z8,z6]),(0,[z1,z2,z59,z3,z4,z8,z6])]],
   [[(0,[z1,z3,z60,z61,z4,z8,z6]),(0,[z1,z2,z62,z3,z4,z8,z6]),(0,[z63,z1,z2,z3,z4,z8,z13])],[(0,[z1,z2,z64,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z65,z66,z6]),(0,[z67,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z10,z4,z8,z6])],[(0,[z68,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z69])],[(0,[z1,z70,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z71,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z72]),(0,[z73,z1,z2,z74,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z75]),(1,[z1,z2,z3,z4,z76,z8]),(0,[z1,z2,z3,z77,z4,z8,z6])],[(0,[z78,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z79,z6]),(0,[z1,z2,z80,z3,z4,z8,z6]),(0,[z1,z3,z81,z4,z82,z8,z6]),(0,[z1,z2,z83,z3,z4,z45,z6])],[(0,[z1,z2,z3,z4,z84,z8,z6]),(0,[z85,z1,z2,z3,z4,z8,z15]),(0,[z86,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z87,z3,z4,z8,z6])],[(0,[z85,z1,z2,z83,z3,z4,z6]),(1,[z1,z2,z3,z4,z8,z88]),(1,[z1,z3,z4,z8,z13,z15]),(0,[z89,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z18,z90,z8,z6])],[(0,[z1,z2,z3,z4,z91,z8,z6]),(1,[z35,z1,z2,z4,z45,z6]),(0,[z1,z2,z92,z3,z4,z19,z6])]],
   [[(0,[z1,z2,z93,z3,z4,z8,z6]),(0,[z1,z2,z94,z3,z4,z8,z6]),(0,[z85,z1,z2,z3,z4,z8,z95]),(0,[z1,z2,z3,z4,z8,z31,z6]),(0,[z1,z2,z3,z4,z8,z6,z88]),(0,[z1,z2,z96,z3,z10,z4,z8]),(0,[z1,z2,z3,z4,z16,z22,z6])],[(1,[z1,z2,z3,z4,z8,z97]),(0,[z1,z98,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z99,z6])],[(0,[z1,z2,z3,z100,z4,z8,z6]),(0,[z101,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z102,z4,z8,z6]),(0,[z103,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z104]),(0,[z1,z2,z36,z3,z4,z8,z105]),(1,[z1,z2,z3,z10,z8,z11]),(0,[z1,z2,z106,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z107,z6]),(0,[z1,z2,z3,z4,z8,z6,z108]),(0,[z109,z1,z2,z3,z82,z8,z6]),(0,[z1,z2,z3,z4,z8,z110,z13]),(0,[z1,z2,z96,z3,z4,z8,z13]),(0,[z1,z2,z111,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z112])],[(0,[z1,z2,z3,z4,z8,z113,z6]),(0,[z1,z2,z3,z4,z114,z8,z6]),(0,[z1,z2,z3,z4,z8,z115,z15])],[(0,[z1,z2,z3,z4,z8,z116,z6]),(0,[z85,z1,z2,z3,z4,z66,z6]),(0,[z1,z117,z2,z3,z4,z8,z13]),(0,[z35,z1,z2,z3,z4,z16,z6]),(1,[z1,z2,z3,z4,z118,z6])],[(0,[z1,z119,z2,z3,z4,z8,z6]),(0,[z1,z120,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z121,z4,z8,z6]),(0,[z1,z2,z3,z4,z122,z8,z6]),(0,[z1,z2,z3,z4,z19,z8,z13]),(0,[z1,z2,z123,z3,z4,z8,z22])],[(0,[z1,z2,z3,z4,z124,z8,z6]),(0,[z1,z2,z3,z125,z4,z8,z6]),(0,[z1,z2,z92,z3,z4,z5,z6]),(0,[z126,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z123,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z127,z8,z6]),(0,[z128,z1,z2,z3,z4,z8,z6]),(0,[z129,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z130,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z15]),(0,[z1,z131,z2,z3,z4,z8,z6]),(0,[z132,z1,z36,z3,z4,z8,z6])],[(0,[z133,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z81,z134,z8,z6]),(0,[z135,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z136,z6]),(0,[z1,z2,z3,z137,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z138]),(0,[z1,z2,z3,z4,z8,z6,z139])],[(0,[z1,z2,z3,z4,z8,z5,z6])],[(0,[z140,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z141,z4,z8,z6]),(0,[z1,z2,z142,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z143]),(0,[z144,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z145,z146,z6])],[(0,[z1,z2,z3,z4,z147,z8,z6]),(0,[z1,z2,z3,z4,z148,z8,z15]),(0,[z1,z2,z3,z4,z8,z22,z72]),(0,[z1,z2,z3,z4,z149,z8,z6]),(0,[z1,z150,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z151,z6])],[(0,[z1,z2,z3,z4,z8,z6,z152]),(0,[z1,z12,z3,z4,z8,z6,z15]),(0,[z1,z2,z3,z18,z82,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z153]),(0,[z1,z2,z3,z4,z8,z154,z6])],[(0,[z1,z2,z155,z3,z4,z8,z6]),(0,[z1,z2,z3,z82,z8,z5,z6]),(0,[z1,z2,z83,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z156,z6]),(0,[z1,z2,z3,z4,z22,z6,z112])],[(0,[z1,z2,z3,z18,z4,z19,z6]),(0,[z1,z2,z3,z4,z8,z6,z157])]],
   [[(0,[z1,z158,z2,z3,z4,z8,z6]),(0,[z159,z1,z2,z3,z4,z8,z6]),(0,[z160,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z8,z6]),(0,[z161,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z162,z3,z4,z8,z6]),(0,[z27,z1,z2,z3,z4,z8,z112])],[(0,[z1,z2,z3,z163,z4,z8,z6]),(0,[z1,z2,z164,z3,z4,z8,z6]),(0,[z165,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z166,z6]),(0,[z1,z2,z3,z4,z8,z167,z6]),(0,[z168,z1,z2,z3,z4,z8,z6]),(0,[z169,z1,z2,z3,z4,z8,z6])],[(1,[z85,z2,z3,z4,z66,z6])],[(0,[z56,z1,z2,z3,z134,z8,z6]),(0,[z1,z2,z3,z4,z8,z170,z6]),(0,[z1,z12,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z171,z6]),(0,[z1,z2,z3,z4,z172,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z173]),(0,[z174,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z175,z8,z6])],[(0,[z1,z2,z3,z18,z4,z5,z6])]],
   [[(0,[z1,z2,z3,z176,z4,z8,z6]),(0,[z177,z1,z2,z3,z4,z8,z6]),(0,[z85,z1,z2,z3,z4,z19,z6]),(0,[z178,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z45,z15]),(0,[z1,z2,z3,z179,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z11,z6])],[(0,[z180,z1,z2,z3,z4,z8,z6]),(1,[z1,z12,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z181,z8,z6]),(0,[z1,z2,z3,z4,z76,z90,z8]),(1,[z1,z2,z57,z179,z8,z6]),(0,[z182,z1,z2,z3,z4,z8,z6])],[(0,[z183,z1,z2,z3,z4,z8,z6]),(0,[z178,z32,z1,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z15,z15]),(0,[z1,z2,z57,z3,z4,z8,z6])],[(0,[z1,z184,z2,z3,z4,z8,z6]),(0,[z178,z1,z3,z4,z82,z8,z6]),(0,[z1,z2,z3,z4,z65,z8,z6]),(0,[z185,z1,z2,z3,z4,z8,z15]),(0,[z186,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z187])],[(1,[z188,z1,z3,z4,z8,z15]),(0,[z189,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z190,z4,z8,z6]),(1,[z1,z2,z191,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z6,z192])],[(0,[z193,z1,z3,z61,z4,z8,z6]),(0,[z1,z2,z194,z3,z4,z8,z6]),(0,[z1,z2,z195,z3,z4,z90,z8]),(0,[z1,z2,z3,z4,z196,z8,z6]),(0,[z1,z2,z3,z18,z4,z8,z6]),(0,[z1,z2,z3,z8,z11,z6,z105]),(0,[z1,z2,z3,z197,z4,z8,z6])],[(0,[z1,z198,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z81,z4,z8,z13]),(0,[z1,z2,z3,z4,z199,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z4,z8,z6]),(0,[z1,z200,z2,z3,z4,z8,z6]),(0,[z85,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z8,z13,z105]),(0,[z1,z2,z3,z4,z8,z201,z6]),(1,[z1,z202,z3,z4,z8,z6])],[(0,[z0,z2,z3,z4,z40,z8,z6]),(0,[z1,z2,z3,z4,z8,z203,z6]),(0,[z1,z2,z3,z10,z4,z8,z11])],[(0,[z78,z1,z204,z3,z4,z8,z6]),(0,[z133,z1,z2,z61,z4,z8,z6]),(0,[z1,z2,z3,z4,z205,z8,z6]),(0,[z1,z2,z3,z206,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z207]),(1,[z1,z2,z3,z208,z8,z6]),(0,[z1,z2,z3,z209,z4,z8,z6]),(0,[z1,z12,z2,z49,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z210,z6])],[(0,[z1,z2,z3,z4,z211,z8,z6]),(0,[z1,z2,z212,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z13,z146]),(0,[z1,z2,z3,z4,z8,z6,z213])],[(1,[z1,z2,z3,z8,z41,z6]),(0,[z35,z1,z2,z3,z4,z45,z6]),(0,[z1,z2,z3,z214,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z215]),(0,[z1,z2,z216,z3,z4,z8,z6])],[(1,[z1,z12,z49,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z110,z15]),(0,[z1,z2,z96,z3,z4,z8,z15])],[(0,[z1,z2,z3,z4,z40,z110,z6]),(0,[z73,z1,z12,z3,z4,z8,z6])]],
   [[(0,[z188,z1,z2,z3,z4,z8,z217]),(0,[z1,z117,z2,z3,z4,z8,z15]),(0,[z32,z1,z2,z3,z81,z8,z6]),(0,[z1,z2,z3,z4,z218,z8,z6]),(0,[z1,z2,z3,z4,z8,z219,z13]),(0,[z35,z1,z2,z3,z24,z8,z6]),(0,[z1,z2,z92,z83,z3,z4,z6])],[(0,[z1,z2,z3,z4,z8,z6,z220]),(0,[z78,z1,z49,z3,z4,z8,z6]),(0,[z1,z117,z2,z3,z4,z221,z6]),(0,[z1,z2,z3,z4,z19,z8,z15]),(0,[z1,z2,z3,z4,z8,z222,z6])],[(0,[z223,z1,z2,z3,z4,z8,z6]),(0,[z224,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z225]),(0,[z1,z2,z3,z4,z8,z6,z226]),(1,[z1,z2,z3,z227,z8,z6]),(0,[z1,z2,z3,z4,z228,z8,z6]),(0,[z1,z2,z202,z3,z4,z8,z6])],[(0,[z229,z1,z2,z3,z18,z8,z6]),(0,[z230,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z231,z4,z8,z6])],[(0,[z188,z1,z2,z3,z4,z232,z6]),(0,[z1,z2,z3,z4,z8,z6,z233]),(0,[z133,z1,z2,z3,z4,z8,z15]),(1,[z73,z1,z74,z4,z8,z6]),(0,[z1,z2,z234,z3,z4,z8,z15]),(0,[z27,z1,z235,z3,z4,z8,z6])],[(0,[z1,z2,z3,z236,z4,z8,z6]),(0,[z1,z2,z237,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z238,z8,z6]),(0,[z1,z2,z239,z3,z4,z8,z15]),(0,[z1,z2,z3,z240,z4,z8,z6]),(0,[z241,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z47,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z115,z6]),(0,[z242,z1,z2,z3,z4,z8,z6])],[(0,[z2,z3,z134,z4,z148,z8,z6]),(0,[z85,z1,z2,z3,z4,z8,z243]),(0,[z244,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z3,z4,z8,z23,z245,z6]),(1,[z1,z2,z3,z4,z8,z171])],[(0,[z78,z1,z158,z3,z4,z8,z6]),(0,[z1,z2,z246,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z247,z6]),(0,[z1,z2,z248,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z249])],[(0,[z1,z2,z3,z4,z8,z250,z6]),(0,[z251,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z217,z6]),(0,[z188,z1,z3,z4,z8,z6,z15]),(0,[z133,z1,z2,z252,z4,z8,z6]),(0,[z1,z2,z3,z4,z253,z8,z6]),(0,[z254,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z255,z6]),(0,[z35,z1,z2,z83,z4,z8,z6])],[(0,[z1,z256,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z257,z4,z8,z6]),(0,[z1,z2,z83,z3,z18,z4,z6]),(0,[z1,z2,z3,z4,z8,z6,z258]),(0,[z1,z2,z259,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z260]),(1,[z1,z2,z3,z4,z261,z6])],[(0,[z1,z53,z2,z3,z61,z4,z8]),(0,[z1,z2,z252,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z148,z8,z6])],[(0,[z188,z1,z2,z3,z4,z8,z262]),(1,[z1,z198,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z6,z263]),(0,[z109,z1,z2,z3,z90,z8,z6]),(0,[z264,z1,z2,z3,z4,z8,z6])]],
   [[(1,[z32,z1,z3,z81,z8,z6]),(0,[z265,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z16,z5,z6]),(0,[z1,z36,z202,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z266]),(0,[z1,z2,z2,z3,z4,z8,z13])],[(0,[z1,z2,z3,z82,z148,z8,z6]),(0,[z0,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z267,z8,z6]),(0,[z1,z2,z3,z74,z4,z8,z13]),(0,[z1,z2,z3,z4,z268,z8,z6]),(0,[z1,z2,z269,z3,z4,z8,z6]),(0,[z1,z270,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z271,z90,z6]),(0,[z1,z2,z272,z3,z4,z8,z6])],[(0,[z188,z1,z2,z3,z4,z8,z15]),(1,[z78,z158,z3,z4,z8,z6]),(1,[z193,z1,z3,z4,z8,z6]),(0,[z133,z2,z252,z3,z4,z8,z6]),(0,[z1,z2,z83,z3,z4,z65,z6]),(0,[z1,z2,z3,z4,z8,z273,z6]),(0,[z1,z2,z92,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z8,z274,z6])],[(0,[z275,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z82,z8,z13]),(0,[z1,z276,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z232,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z277])],[(0,[z1,z2,z3,z61,z4,z8,z6]),(0,[z1,z2,z3,z4,z278,z8,z6]),(0,[z1,z2,z3,z279,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z280,z6]),(0,[z1,z2,z3,z4,z281,z8,z6])],[(1,[z1,z2,z3,z4,z282,z6]),(0,[z1,z2,z283,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z284,z8,z6]),(0,[z27,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z285,z8,z6])]],
   [[(0,[z1,z2,z3,z286,z4,z8,z13]),(0,[z1,z2,z3,z4,z287,z8,z13]),(0,[z1,z2,z3,z288,z4,z8,z6])],[(0,[z1,z2,z289,z3,z4,z8,z6]),(0,[z1,z117,z2,z3,z82,z8,z6]),(0,[z1,z2,z290,z3,z4,z8,z15]),(1,[z1,z2,z3,z4,z8,z291])],[(0,[z1,z2,z292,z3,z4,z8,z6]),(0,[z1,z293,z2,z3,z4,z8,z6]),(0,[z229,z1,z2,z3,z148,z8,z6]),(0,[z1,z2,z3,z81,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z22,z13]),(0,[z1,z2,z3,z4,z8,z45,z6]),(0,[z27,z1,z2,z4,z8,z6,z28]),(0,[z1,z2,z96,z3,z4,z8,z146])],[(0,[z1,z2,z62,z3,z61,z4,z6]),(0,[z1,z2,z3,z4,z8,z41,z6]),(0,[z1,z2,z3,z4,z8,z294,z6]),(0,[z1,z295,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z291])],[(0,[z1,z2,z3,z4,z8,z296,z6]),(0,[z1,z2,z3,z297,z4,z8,z6]),(0,[z1,z2,z3,z134,z4,z8,z13]),(0,[z1,z2,z191,z3,z4,z90,z6]),(0,[z1,z298,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z299]),(0,[z1,z117,z2,z3,z4,z91,z6]),(0,[z1,z300,z3,z4,z8,z110,z6]),(0,[z1,z2,z3,z4,z8,z301,z13]),(0,[z1,z2,z3,z4,z302,z8,z6]),(0,[z303,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z304,z3,z4,z8,z6]),(0,[z1,z2,z3,z305,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z6,z112])],[(0,[z306,z1,z2,z3,z4,z8,z6]),(0,[z307,z1,z2,z3,z4,z8,z6]),(0,[z308,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z309,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z310,z6]),(0,[z1,z2,z311,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z75])]],
   [[(0,[z30,z1,z2,z3,z4,z8,z6]),(0,[z312,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z19,z8,z5,z6])],[(0,[z1,z313,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z314]),(0,[z315,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z316,z6]),(0,[z1,z2,z123,z3,z4,z8,z112])],[(0,[z180,z27,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z210,z8,z13]),(1,[z132,z1,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z314]),(0,[z135,z1,z2,z3,z4,z8,z97]),(1,[z135,z1,z3,z4,z65,z6]),(1,[z1,z2,z123,z3,z4,z112])],[(0,[z317,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z72,z112]),(0,[z1,z2,z3,z4,z8,z23,z15]),(0,[z318,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z6,z319]),(1,[z1,z2,z3,z4,z8,z320]),(0,[z1,z2,z83,z3,z4,z110,z6]),(0,[z1,z321,z2,z3,z4,z8,z6]),(0,[z27,z1,z322,z3,z4,z8,z6])],[(0,[z78,z158,z2,z3,z4,z8,z6]),(0,[z56,z1,z2,z3,z4,z8,z15]),(0,[z1,z323,z2,z3,z4,z8,z6]),(0,[z1,z2,z324,z3,z4,z8,z6]),(0,[z1,z2,z57,z3,z81,z8,z6]),(0,[z1,z2,z3,z4,z8,z325,z6]),(0,[z326,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z327,z4,z8,z6])],[(0,[z328,z1,z2,z3,z4,z8,z6]),(0,[z329,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z330]),(0,[z1,z2,z3,z4,z8,z331,z6]),(0,[z1,z2,z3,z4,z332,z8,z6]),(1,[z1,z2,z3,z4,z271,z6]),(0,[z1,z2,z333,z3,z4,z8,z6])]],
   [[(0,[z1,z334,z2,z3,z4,z8,z6]),(0,[z27,z30,z1,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z335,z6]),(0,[z1,z2,z57,z179,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z336,z6])],[(0,[z1,z300,z2,z3,z4,z8,z15]),(0,[z1,z337,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z338,z6]),(0,[z339,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z92,z3,z4,z8,z6])],[(0,[z1,z117,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z18,z81,z8,z6]),(0,[z1,z2,z3,z4,z340,z8,z6]),(0,[z1,z2,z3,z4,z341,z8,z6])],[(0,[z1,z2,z3,z4,z66,z6,z112]),(0,[z73,z1,z2,z3,z4,z8,z342]),(1,[z1,z3,z74,z4,z8,z15]),(0,[z343,z1,z2,z3,z4,z8,z6]),(0,[z344,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z8,z6])],[(0,[z1,z345,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z15])],[(0,[z1,z117,z3,z4,z82,z8,z6]),(0,[z1,z2,z3,z90,z8,z5,z6]),(0,[z1,z2,z3,z4,z145,z8,z6])],[(0,[z73,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z234,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z173]),(0,[z346,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z347,z6])],[(0,[z1,z2,z3,z4,z348,z8,z6]),(0,[z1,z2,z3,z4,z349,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z95]),(0,[z180,z2,z3,z4,z8,z23,z6]),(0,[z1,z350,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z351,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z352]),(0,[z1,z2,z239,z3,z4,z8,z6]),(0,[z109,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z36,z3,z4,z8,z6]),(0,[z1,z2,z3,z353,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z40,z8,z13]),(0,[z1,z2,z3,z4,z16,z8,z15])],[(0,[z1,z2,z3,z354,z4,z8,z6]),(1,[z1,z2,z3,z355,z8,z6]),(0,[z1,z2,z3,z356,z4,z8,z6]),(0,[z357,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z358,z6]),(0,[z359,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z360,z8,z6]),(0,[z1,z2,z3,z4,z8,z146,z15]),(0,[z1,z2,z3,z4,z361,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z362])],[(0,[z1,z2,z3,z29,z61,z8,z6]),(0,[z135,z1,z3,z4,z65,z8,z6]),(0,[z1,z2,z363,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z364,z8,z6]),(0,[z365,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z136]),(0,[z1,z2,z3,z4,z210,z8,z291]),(0,[z1,z2,z366,z3,z4,z8,z6])],[(0,[z1,z2,z3,z74,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z367,z6]),(0,[z35,z1,z2,z3,z18,z4,z6]),(0,[z1,z2,z3,z4,z8,z368,z6])],[(0,[z1,z2,z369,z3,z4,z8,z6]),(1,[z1,z2,z3,z370,z8,z6]),(0,[z1,z2,z3,z4,z371,z8,z6]),(0,[z372,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z373,z6]),(0,[z1,z2,z3,z4,z8,z6,z374])],[(0,[z375,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z204,z3,z4,z8,z13]),(1,[z78,z1,z3,z4,z8,z15]),(1,[z68,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z376,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z377]),(0,[z378,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z14,z4,z8,z6]),(0,[z1,z300,z2,z3,z114,z8,z6]),(0,[z379,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z380,z13]),(1,[z1,z235,z3,z4,z8,z6]),(0,[z381,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z252,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z16,z66,z6]),(0,[z1,z2,z382,z3,z4,z8,z6])],[(0,[z1,z2,z3,z383,z4,z8,z6]),(0,[z68,z1,z2,z3,z61,z8,z6]),(0,[z384,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z385,z8,z6]),(0,[z1,z2,z3,z4,z8,z386,z15]),(0,[z1,z2,z3,z4,z8,z387,z6])],[(1,[z133,z2,z252,z4,z8,z6]),(0,[z56,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z8,z388,z6]),(0,[z27,z1,z2,z3,z4,z8,z15]),(0,[z1,z389,z2,z3,z4,z8,z6])],[(0,[z390,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z391,z8,z6]),(1,[z1,z2,z3,z4,z392,z6]),(0,[z1,z2,z3,z4,z8,z6,z393]),(0,[z178,z1,z337,z3,z4,z8,z6]),(0,[z394,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z395,z6])],[(0,[z1,z2,z3,z4,z8,z6,z396]),(0,[z1,z2,z397,z3,z4,z8,z6]),(0,[z398,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z399]),(0,[z1,z2,z3,z400,z4,z8,z6]),(0,[z35,z1,z2,z3,z4,z65,z6]),(0,[z401,z1,z2,z3,z4,z8,z6])],[(0,[z188,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z243,z6]),(0,[z1,z2,z3,z4,z65,z40,z6]),(0,[z1,z12,z2,z3,z4,z8,z402]),(0,[z1,z2,z3,z4,z8,z22,z15]),(0,[z1,z403,z2,z3,z4,z8,z6])],[(0,[z1,z2,z61,z74,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z404,z6]),(0,[z1,z2,z49,z3,z4,z8,z13]),(0,[z1,z2,z3,z405,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z406]),(0,[z1,z2,z3,z4,z8,z6,z407]),(0,[z1,z408,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z134,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z409,z6]),(0,[z1,z2,z3,z4,z8,z6,z410]),(0,[z1,z2,z3,z4,z8,z6,z411])]],
   [[(0,[z1,z2,z412,z3,z4,z8,z6]),(0,[z229,z1,z2,z57,z3,z8,z6]),(0,[z1,z2,z3,z413,z4,z8,z6]),(0,[z414,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z15,z28]),(0,[z1,z2,z3,z4,z415,z8,z6]),(1,[z1,z2,z92,z3,z5,z6])],[(0,[z30,z1,z2,z3,z4,z8,z23]),(0,[z1,z300,z2,z3,z190,z8,z6]),(0,[z1,z2,z3,z4,z416,z8,z6]),(0,[z1,z2,z3,z10,z4,z8,z13]),(0,[z1,z2,z235,z3,z4,z8,z6])],[(0,[z1,z198,z2,z3,z61,z4,z6]),(0,[z1,z2,z3,z417,z4,z8,z6]),(0,[z1,z2,z3,z418,z4,z8,z6]),(0,[z85,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z419,z6]),(0,[z1,z2,z3,z420,z4,z8,z6]),(0,[z421,z1,z2,z3,z4,z8,z6])],[(0,[z188,z1,z2,z3,z422,z8,z6]),(0,[z1,z2,z3,z4,z423,z8,z6]),(1,[z1,z2,z3,z4,z31,z6]),(0,[z1,z2,z3,z4,z424,z8,z6]),(0,[z1,z2,z3,z4,z8,z425,z6])],[(0,[z426,z1,z2,z3,z4,z8,z6]),(0,[z78,z1,z2,z3,z4,z8,z13]),(1,[z1,z2,z3,z4,z8,z427]),(0,[z1,z2,z3,z428,z4,z8,z6]),(0,[z1,z2,z3,z429,z4,z8,z6]),(0,[z430,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z431]),(0,[z432,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z105])],[(0,[z73,z78,z1,z3,z4,z8,z6]),(0,[z1,z2,z47,z3,z61,z4,z8]),(0,[z433,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z434,z8,z6]),(0,[z1,z2,z3,z435,z4,z8,z6]),(0,[z1,z2,z3,z4,z436,z8,z15])],[(0,[z1,z2,z437,z3,z4,z8,z6]),(0,[z1,z2,z3,z438,z4,z8,z6]),(0,[z1,z439,z2,z3,z4,z8,z6])],[(0,[z158,z2,z204,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z440,z6]),(0,[z441,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z442,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z342]),(0,[z1,z2,z3,z4,z443,z8,z6]),(0,[z1,z2,z3,z444,z4,z8,z6])]],
   [[(0,[z188,z1,z2,z445,z4,z8,z6]),(0,[z1,z446,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z447,z8,z6]),(0,[z1,z2,z3,z4,z90,z8,z13])],[(0,[z1,z2,z3,z4,z8,z6,z448]),(0,[z1,z2,z3,z4,z8,z6,z342]),(0,[z1,z2,z449,z3,z4,z8,z6])],[(0,[z1,z2,z3,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z450,z6]),(1,[z1,z2,z3,z4,z8,z13]),(0,[z451,z1,z2,z3,z4,z8,z15])],[(0,[z1,z2,z452,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z16,z19,z6])],[(0,[z1,z2,z3,z4,z453,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z112])],[(0,[z1,z2,z252,z74,z4,z8,z6]),(0,[z454,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z6])],[(0,[z455,z1,z2,z3,z4,z8,z6]),(0,[z456,z1,z2,z3,z4,z8,z6]),(0,[z35,z1,z2,z3,z4,z110,z6]),(0,[z1,z2,z83,z4,z210,z8,z6])],[(0,[z1,z2,z3,z4,z8,z457,z6]),(0,[z1,z117,z2,z3,z4,z8,z331]),(0,[z1,z2,z123,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z146,z6,z362]),(0,[z1,z2,z3,z4,z8,z458,z6])]],
   [[(0,[z56,z1,z2,z3,z4,z8,z6]),(0,[z32,z1,z117,z3,z4,z8,z6]),(0,[z1,z2,z459,z3,z4,z8,z6]),(0,[z1,z460,z2,z3,z4,z8,z6]),(0,[z1,z2,z461,z3,z4,z8,z6]),(0,[z1,z462,z2,z3,z4,z8,z6])],[(0,[z73,z1,z2,z3,z4,z8,z15]),(0,[z135,z1,z2,z3,z4,z65,z6]),(0,[z463,z1,z2,z3,z4,z8,z6]),(0,[z346,z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z464,z4,z8,z6]),(0,[z465,z1,z2,z3,z4,z8,z6])],[(0,[z188,z73,z1,z3,z4,z8,z6]),(0,[z229,z56,z2,z3,z4,z8,z6]),(0,[z1,z3,z4,z82,z8,z6,z15]),(0,[z1,z2,z3,z4,z8,z5,z13]),(0,[z1,z2,z3,z4,z8,z466,z6]),(0,[z1,z467,z2,z3,z4,z8,z6]),(0,[z132,z1,z2,z3,z4,z8,z6])],[(0,[z1,z1,z2,z3,z4,z8,z6]),(0,[z140,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z468,z6]),(0,[z469,z1,z2,z3,z4,z8,z6]),(0,[z35,z85,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z40,z8,z15]),(0,[z1,z300,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z470,z6])],[(0,[z1,z2,z471,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z370,z8,z6]),(0,[z1,z2,z3,z4,z8,z472,z6])],[(0,[z180,z1,z2,z3,z4,z8,z23])],[(0,[z473,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z208,z40,z8,z6]),(0,[z32,z1,z2,z3,z4,z8,z314]),(0,[z1,z2,z3,z179,z4,z8,z15]),(0,[z1,z3,z4,z8,z13,z6,z15]),(0,[z1,z2,z83,z3,z4,z8,z13]),(0,[z27,z1,z2,z3,z4,z8,z146]),(0,[z474,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z475,z3,z4,z8,z6]),(0,[z1,z476,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z76,z8,z6]),(0,[z27,z1,z2,z3,z10,z4,z8]),(0,[z1,z2,z36,z3,z4,z8,z11])]],
   [[(0,[z1,z158,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z134,z82,z8,z6]),(0,[z1,z2,z477,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z478,z8,z6]),(1,[z1,z322,z3,z4,z8,z6])],[(0,[z178,z1,z3,z4,z8,z13,z6]),(0,[z1,z2,z3,z4,z8,z6,z479]),(0,[z1,z2,z3,z4,z8,z480,z6]),(0,[z1,z2,z3,z4,z210,z8,z406]),(0,[z1,z2,z3,z4,z8,z481,z6])],[(1,[z1,z2,z3,z4,z8,z217]),(0,[z1,z2,z204,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z6,z482]),(1,[z1,z2,z3,z4,z483,z6]),(0,[z30,z1,z2,z3,z4,z8,z72]),(0,[z1,z12,z2,z3,z4,z8,z6]),(0,[z32,z1,z2,z3,z4,z8,z320]),(0,[z1,z2,z3,z4,z8,z15,z484]),(0,[z1,z2,z3,z4,z8,z485,z6]),(0,[z1,z2,z3,z4,z16,z8,z6])],[(0,[z1,z2,z3,z4,z486,z8,z6]),(0,[z1,z2,z3,z4,z8,z487,z6]),(0,[z1,z2,z3,z488,z4,z8,z6]),(0,[z1,z489,z2,z3,z4,z8,z6])],[(0,[z490,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z243]),(0,[z0,z1,z2,z3,z4,z40,z6]),(1,[z1,z2,z195,z3,z4,z8]),(0,[z1,z2,z195,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z45,z6]),(0,[z1,z2,z3,z491,z4,z8,z6])],[(0,[z1,z2,z492,z3,z4,z8,z6]),(0,[z1,z493,z2,z3,z4,z8,z6]),(0,[z30,z2,z3,z4,z8,z6,z72]),(0,[z1,z2,z3,z494,z4,z8,z6]),(0,[z1,z495,z2,z3,z4,z8,z6]),(0,[z1,z2,z496,z3,z4,z8,z13])],[(1,[z1,z2,z3,z4,z232,z6]),(0,[z1,z2,z3,z4,z497,z8,z6]),(0,[z229,z1,z2,z3,z134,z8,z6]),(0,[z73,z1,z2,z49,z4,z8,z6]),(0,[z1,z117,z2,z3,z81,z8,z6]),(0,[z1,z2,z3,z4,z8,z15,z112]),(0,[z1,z2,z3,z498,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z499])],[(0,[z1,z2,z500,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z245,z6]),(0,[z501,z1,z2,z3,z4,z8,z6]),(0,[z502,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z503,z6]),(0,[z1,z2,z3,z504,z4,z8,z6]),(0,[z505,z1,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z506,z4,z8,z6]),(0,[z63,z1,z2,z3,z4,z8,z6]),(0,[z185,z1,z2,z3,z4,z8,z6]),(0,[z178,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z11,z13]),(1,[z27,z1,z2,z4,z8,z28]),(0,[z1,z2,z3,z4,z8,z507,z6])],[(0,[z508,z1,z2,z3,z4,z8,z6]),(0,[z1,z509,z2,z3,z4,z8,z6]),(1,[z1,z2,z96,z4,z8,z146]),(0,[z510,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z511,z3,z4,z8,z6])],[(0,[z1,z2,z3,z355,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z512,z6]),(0,[z1,z2,z57,z3,z4,z8,z13]),(0,[z1,z2,z513,z3,z4,z8,z6]),(1,[z1,z2,z83,z4,z210,z6])],[(0,[z188,z1,z2,z514,z4,z8,z6]),(0,[z188,z1,z204,z3,z4,z8,z6]),(0,[z140,z2,z3,z61,z4,z8,z6]),(0,[z515,z1,z2,z3,z4,z8,z6]),(0,[z109,z1,z2,z3,z81,z8,z6]),(0,[z135,z1,z2,z3,z4,z110,z6]),(0,[z1,z2,z3,z4,z65,z8,z13]),(0,[z1,z2,z3,z4,z227,z8,z6]),(0,[z1,z2,z3,z516,z4,z8,z6]),(0,[z1,z517,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z399,z6]),(0,[z1,z2,z3,z4,z110,z5,z6]),(0,[z1,z2,z3,z10,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z6,z518])],[],[(0,[z56,z2,z3,z134,z4,z8,z6]),(0,[z1,z12,z2,z3,z4,z360,z6]),(0,[z1,z2,z3,z4,z8,z15,z519]),(0,[z1,z2,z3,z4,z8,z6,z520])],[(0,[z521,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z22,z6])]],
   [[(0,[z1,z2,z445,z3,z4,z8,z6]),(0,[z522,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z523]),(0,[z1,z2,z3,z4,z210,z5,z6]),(0,[z1,z2,z524,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z8,z262]),(0,[z1,z98,z2,z3,z4,z8,z6])],[(0,[z188,z1,z49,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z301,z6]),(0,[z525,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z179,z8,z5,z6]),(0,[z1,z2,z526,z3,z4,z8,z6]),(0,[z1,z2,z96,z3,z4,z8,z22]),(0,[z1,z2,z3,z4,z8,z527,z6])],[(0,[z1,z2,z3,z4,z8,z6,z262]),(0,[z528,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z110,z6]),(0,[z1,z2,z3,z4,z90,z8,z15]),(0,[z1,z2,z96,z3,z4,z8,z6]),(0,[z1,z2,z92,z3,z18,z8,z6]),(0,[z1,z2,z3,z4,z529,z8,z6])],[(0,[z188,z1,z2,z3,z147,z8,z6]),(0,[z530,z1,z2,z3,z4,z8,z6]),(0,[z140,z1,z2,z61,z4,z8,z6]),(0,[z1,z2,z3,z4,z271,z8,z6]),(0,[z531,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z18,z19,z8,z6])],[(0,[z1,z532,z2,z3,z4,z8,z6]),(0,[z1,z2,z533,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z15]),(1,[z1,z2,z3,z4,z302,z6]),(0,[z534,z1,z2,z3,z4,z8,z6]),(0,[z535,z1,z2,z3,z4,z8,z6])],[(0,[z188,z2,z204,z3,z4,z8,z6]),(0,[z1,z2,z3,z536,z4,z8,z6]),(0,[z180,z1,z2,z3,z4,z8,z72]),(0,[z1,z2,z3,z4,z8,z13,z23]),(1,[z1,z2,z3,z4,z221,z6]),(0,[z1,z2,z3,z537,z4,z8,z6])],[(0,[z538,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z134,z4,z483,z6]),(0,[z1,z2,z3,z4,z40,z6,z112]),(0,[z1,z2,z539,z3,z4,z8,z6]),(0,[z1,z12,z2,z74,z4,z8,z6]),(0,[z540,z1,z2,z3,z4,z8,z6]),(1,[z32,z1,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z436,z8,z6]),(0,[z1,z541,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z514,z4,z8,z6]),(1,[z1,z2,z3,z4,z8,z95]),(1,[z1,z3,z4,z82,z8,z15])],[(0,[z133,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z81,z8,z5,z6]),(0,[z1,z2,z3,z4,z8,z13,z28]),(0,[z1,z2,z542,z3,z4,z8,z6])],[(0,[z188,z1,z158,z3,z4,z8,z6]),(0,[z1,z2,z123,z3,z4,z8,z15]),(0,[z1,z2,z83,z3,z4,z210,z6]),(0,[z1,z2,z3,z4,z8,z118,z6])],[(0,[z543,z1,z2,z3,z4,z8,z6]),(0,[z85,z2,z3,z4,z8,z66,z6]),(0,[z1,z2,z544,z3,z4,z8,z6]),(0,[z545,z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z546,z8,z6]),(0,[z1,z2,z3,z547,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z548])],[(0,[z451,z1,z2,z3,z4,z8,z6]),(0,[z229,z1,z2,z3,z4,z8,z13]),(0,[z178,z1,z12,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z549,z8,z6]),(0,[z1,z2,z3,z4,z8,z550,z6]),(0,[z1,z2,z3,z4,z8,z5,z15]),(0,[z1,z2,z36,z3,z4,z118,z6])],[(0,[z551,z1,z2,z3,z4,z8,z6]),(0,[z140,z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z552,z8,z6]),(0,[z1,z117,z2,z3,z4,z8,z143]),(0,[z1,z2,z191,z3,z4,z8,z6]),(0,[z1,z2,z4,z8,z146,z6,z28]),(0,[z1,z2,z3,z4,z553,z8,z6])],[(1,[z1,z2,z3,z4,z453,z6]),(0,[z554,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z555,z3,z4,z8,z6]),(0,[z1,z2,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z5,z6,z112]),(1,[z1,z2,z3,z4,z37,z6])]],
   [[(0,[z135,z1,z2,z3,z4,z8,z173]),(0,[z556,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z557,z3,z4,z8,z6])],[(0,[z1,z2,z83,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z558,z8,z6])],[(0,[z1,z2,z3,z4,z8,z66,z13]),(0,[z1,z2,z3,z4,z82,z8,z15]),(0,[z109,z1,z2,z4,z90,z8,z6]),(0,[z35,z1,z2,z3,z227,z8,z6]),(0,[z1,z559,z2,z3,z4,z8,z6])],[(0,[z1,z158,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z560,z8,z6]),(0,[z2,z3,z4,z8,z23,z6,z72]),(0,[z73,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z114,z8,z6]),(0,[z1,z2,z3,z24,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z561,z6]),(0,[z1,z2,z36,z3,z8,z6,z105])],[(0,[z229,z2,z3,z4,z148,z8,z6]),(0,[z73,z1,z3,z74,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z402]),(0,[z1,z562,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z563,z6]),(0,[z1,z2,z3,z10,z4,z8,z105])],[(0,[z140,z1,z2,z252,z4,z8,z6]),(0,[z1,z564,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z40,z8,z6]),(0,[z1,z2,z565,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z566])],[(0,[z1,z2,z3,z567,z4,z8,z6]),(0,[z1,z2,z568,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z569,z8,z6]),(0,[z1,z2,z3,z4,z570,z8,z6]),(0,[z1,z2,z571,z3,z4,z8,z6])],[(0,[z32,z1,z2,z3,z4,z8,z13]),(0,[z35,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z572,z8,z6]),(0,[z27,z1,z2,z96,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z573,z8,z6]),(0,[z1,z2,z3,z179,z4,z8,z6]),(0,[z574,z1,z2,z3,z4,z8,z6])],[(0,[z193,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z57,z3,z179,z8,z6]),(0,[z1,z322,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z422,z4,z8,z6]),(0,[z0,z1,z2,z3,z4,z8,z13]),(0,[z575,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z576,z3,z4,z8,z6]),(0,[z577,z1,z2,z3,z4,z8,z6])],[(0,[z188,z178,z1,z3,z4,z8,z6]),(0,[z578,z1,z2,z3,z4,z8,z6]),(0,[z178,z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z579,z6])],[(0,[z188,z78,z2,z3,z4,z8,z6]),(0,[z30,z1,z2,z96,z3,z4,z8])],[(1,[z1,z2,z3,z190,z8,z6]),(0,[z1,z2,z57,z3,z4,z8,z15]),(0,[z1,z2,z3,z18,z179,z8,z6]),(0,[z1,z2,z3,z4,z580,z8,z6])],[(0,[z1,z2,z3,z4,z8,z581,z6]),(1,[z1,z3,z60,z4,z8,z6]),(0,[z1,z2,z3,z61,z4,z8,z13]),(0,[z1,z2,z3,z582,z4,z8,z6]),(1,[z180,z2,z3,z4,z8,z23]),(0,[z1,z2,z3,z4,z65,z8,z15]),(0,[z1,z2,z290,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z69]),(0,[z1,z2,z3,z4,z8,z280,z13]),(0,[z583,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z584]),(0,[z585,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z586,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z13,z72]),(0,[z1,z12,z49,z3,z4,z8,z6]),(0,[z1,z2,z3,z81,z4,z8,z6]),(0,[z1,z2,z587,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z588,z8,z6]),(0,[z1,z2,z3,z4,z210,z8,z15]),(0,[z1,z2,z3,z4,z8,z589,z6])],[(0,[z1,z590,z2,z3,z4,z8,z6]),(0,[z0,z85,z2,z3,z4,z8,z6]),(0,[z73,z1,z2,z3,z4,z8,z409])],[(1,[z1,z53,z2,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z591,z6]),(1,[z1,z2,z3,z4,z91,z6]),(0,[z1,z2,z3,z4,z592,z8,z6])],[(0,[z593,z1,z2,z3,z4,z8,z6])],[(0,[z594,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z134,z4,z453,z6]),(0,[z85,z1,z2,z3,z4,z40,z6]),(0,[z1,z2,z3,z595,z4,z8,z6]),(0,[z1,z2,z596,z3,z4,z8,z6]),(0,[z1,z2,z3,z597,z4,z8,z6])],[(0,[z1,z2,z598,z3,z4,z8,z6])],[(0,[z1,z2,z599,z3,z4,z8,z6]),(0,[z1,z2,z3,z208,z4,z8,z6]),(0,[z306,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z13,z104]),(0,[z1,z2,z600,z3,z4,z8,z6]),(0,[z1,z2,z3,z601,z4,z8,z6]),(0,[z1,z2,z123,z3,z4,z6,z112])],[(0,[z602,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z57,z3,z90,z8,z6]),(0,[z1,z2,z96,z3,z4,z8,z28])]],
   [[(0,[z1,z2,z3,z4,z8,z219,z6]),(0,[z1,z2,z3,z60,z4,z8,z6]),(0,[z1,z2,z603,z3,z4,z8,z6]),(0,[z30,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z23,z112]),(0,[z1,z2,z604,z3,z4,z8,z6]),(0,[z1,z3,z4,z65,z8,z110,z6]),(1,[z178,z1,z3,z4,z8,z13]),(0,[z1,z2,z3,z605,z4,z8,z6])],[(0,[z1,z606,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z23,z6]),(1,[z30,z2,z3,z4,z8,z72]),(0,[z1,z607,z2,z3,z4,z8,z6])],[(0,[z56,z1,z2,z3,z18,z8,z6]),(0,[z1,z300,z2,z3,z4,z8,z88]),(0,[z1,z300,z2,z3,z4,z110,z6])],[(0,[z1,z2,z3,z608,z4,z8,z6]),(0,[z1,z2,z36,z96,z3,z4,z8])],[(0,[z1,z2,z3,z4,z8,z6,z484]),(0,[z1,z2,z3,z4,z609,z8,z6]),(0,[z1,z2,z3,z4,z8,z419,z6]),(0,[z1,z2,z3,z4,z8,z610,z6]),(0,[z135,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z15,z266]),(0,[z1,z2,z3,z4,z8,z222,z15])],[(0,[z1,z158,z2,z3,z4,z8,z427]),(0,[z1,z2,z3,z4,z90,z8,z6]),(0,[z1,z2,z83,z3,z4,z6,z112])],[],[(1,[z1,z2,z3,z4,z8,z6]),(0,[z229,z1,z2,z3,z4,z8,z15]),(0,[z1,z611,z2,z3,z4,z8,z6]),(0,[z27,z1,z2,z36,z3,z4,z8]),(0,[z1,z2,z612,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z427,z6]),(0,[z180,z1,z2,z96,z3,z4,z8]),(1,[z1,z3,z4,z8,z245,z6]),(0,[z1,z2,z3,z4,z8,z613,z6])],[(0,[z614,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z6]),(0,[z1,z2,z3,z4,z8,z615,z6]),(1,[z183,z1,z3,z4,z8,z6]),(0,[z1,z337,z2,z3,z4,z8,z13]),(0,[z1,z2,z92,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z6,z616]),(0,[z1,z2,z179,z4,z90,z8,z6])],[(0,[z1,z2,z49,z61,z4,z8,z6]),(0,[z2,z3,z4,z40,z8,z66,z6]),(0,[z32,z1,z3,z4,z8,z6,z15]),(0,[z617,z1,z2,z3,z4,z8,z6])],[(1,[z1,z2,z3,z4,z8,z482]),(0,[z1,z49,z3,z74,z4,z8,z6]),(0,[z1,z2,z618,z3,z4,z8,z6]),(0,[z1,z2,z619,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z65,z6]),(0,[z620,z1,z2,z3,z4,z8,z6]),(0,[z35,z1,z2,z3,z4,z210,z6])],[(0,[z1,z2,z621,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z622]),(0,[z1,z2,z3,z4,z8,z247,z15]),(0,[z35,z1,z2,z4,z8,z45,z6]),(0,[z1,z2,z3,z4,z8,z623,z6]),(0,[z1,z2,z3,z4,z624,z8,z6]),(0,[z1,z2,z3,z4,z16,z8,z112]),(0,[z1,z2,z3,z4,z16,z8,z22])],[(1,[z1,z2,z3,z422,z8,z6]),(0,[z1,z2,z3,z81,z148,z8,z6]),(0,[z1,z2,z3,z4,z8,z66,z15]),(1,[z1,z300,z3,z4,z110,z6]),(0,[z545,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z6,z362]),(1,[z1,z2,z36,z3,z8,z105])],[(0,[z1,z2,z625,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z626,z8,z6]),(0,[z1,z2,z57,z3,z82,z8,z6])],[(0,[z183,z1,z3,z4,z8,z23,z6]),(0,[z109,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z36,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z146,z6]),(0,[z1,z2,z3,z4,z8,z6,z627]),(0,[z1,z628,z2,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z629,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z519])],[(0,[z1,z2,z2,z3,z4,z8,z6]),(0,[z2,z252,z3,z61,z4,z8,z6]),(0,[z1,z2,z630,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z631,z6]),(0,[z1,z3,z74,z4,z8,z6,z15]),(0,[z1,z2,z632,z3,z4,z8,z6])],[(1,[z1,z2,z445,z4,z8,z6]),(0,[z633,z1,z2,z3,z4,z8,z6]),(0,[z78,z1,z3,z4,z8,z6,z15]),(0,[z1,z2,z3,z74,z4,z8,z6]),(0,[z1,z2,z634,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z143]),(0,[z32,z1,z2,z3,z4,z8,z15]),(0,[z635,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z636,z3,z4,z8,z6]),(0,[z35,z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z261,z6]),(0,[z1,z2,z637,z3,z4,z8,z6])],[(0,[z1,z2,z3,z638,z4,z8,z6]),(1,[z1,z2,z3,z4,z360,z6]),(0,[z35,z1,z2,z92,z3,z4,z6]),(0,[z1,z2,z3,z4,z639,z8,z6])],[(0,[z1,z2,z3,z4,z16,z40,z6]),(0,[z180,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z49,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z82,z8,z6]),(0,[z1,z476,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z640,z6]),(0,[z1,z2,z3,z4,z8,z641,z6])],[(1,[z140,z2,z61,z4,z8,z6]),(0,[z642,z1,z2,z3,z4,z8,z6]),(0,[z0,z1,z2,z3,z4,z8,z15]),(1,[z1,z2,z3,z4,z8,z409]),(0,[z109,z1,z2,z3,z4,z261,z6]),(0,[z1,z2,z3,z643,z4,z8,z6]),(1,[z1,z2,z3,z4,z145,z6])],[(0,[z644,z1,z2,z3,z4,z8,z6]),(0,[z0,z1,z2,z83,z3,z4,z6]),(0,[z1,z2,z3,z645,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z386,z6]),(0,[z372,z1,z2,z3,z4,z8,z13]),(0,[z1,z646,z2,z3,z4,z8,z6]),(0,[z27,z1,z2,z3,z4,z8,z22])],[(0,[z1,z2,z3,z4,z8,z406,z6]),(0,[z27,z1,z2,z3,z4,z8,z6]),(1,[z1,z2,z3,z4,z16,z22])]],
   [[(0,[z1,z2,z3,z4,z647,z8,z6]),(0,[z1,z2,z252,z3,z4,z8,z13]),(0,[z135,z1,z300,z3,z4,z8,z6]),(0,[z1,z2,z3,z286,z4,z8,z6]),(0,[z1,z2,z3,z4,z287,z8,z6]),(0,[z1,z2,z648,z3,z4,z8,z6]),(0,[z649,z1,z2,z3,z4,z8,z6])],[(0,[z1,z158,z2,z3,z4,z8,z482]),(0,[z140,z133,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z61,z4,z8,z15]),(0,[z56,z1,z2,z3,z148,z8,z6]),(0,[z109,z56,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z65,z5,z6]),(0,[z1,z2,z3,z18,z4,z8,z13]),(0,[z1,z2,z650,z3,z4,z8,z6])],[(0,[z78,z1,z2,z3,z4,z8,z15]),(1,[z229,z2,z3,z148,z8,z6]),(0,[z1,z2,z3,z651,z4,z8,z6]),(0,[z1,z2,z3,z4,z652,z8,z6]),(0,[z1,z2,z496,z3,z4,z8,z6])],[(0,[z1,z2,z49,z252,z4,z8,z6]),(0,[z229,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z653,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z6,z654])],[(0,[z1,z2,z3,z4,z8,z282,z6]),(0,[z1,z655,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z134,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z483,z6]),(0,[z1,z2,z656,z3,z4,z8,z6]),(0,[z657,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z658,z4,z8,z6]),(0,[z1,z2,z3,z659,z4,z8,z6])],[(0,[z188,z1,z2,z3,z4,z8,z13]),(0,[z0,z1,z2,z3,z4,z66,z6]),(0,[z1,z2,z660,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z19,z110,z6]),(0,[z1,z2,z3,z4,z8,z661,z6]),(0,[z1,z2,z96,z3,z4,z8,z112]),(0,[z1,z2,z123,z3,z4,z16,z6])],[(0,[z1,z2,z3,z662,z4,z8,z6]),(0,[z178,z1,z3,z74,z4,z8,z6]),(0,[z1,z663,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z664,z8,z6])]],
   [[(0,[z1,z2,z665,z3,z4,z8,z6]),(0,[z666,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z667,z4,z8,z6]),(0,[z668,z1,z2,z3,z4,z8,z6])],[(0,[z180,z30,z2,z3,z4,z8,z6]),(0,[z1,z12,z2,z3,z355,z8,z6])],[(0,[z1,z669,z2,z3,z4,z8,z6]),(0,[z670,z1,z2,z3,z4,z8,z6]),(0,[z85,z1,z2,z3,z4,z8,z13]),(0,[z1,z2,z671,z3,z4,z8,z6]),(0,[z1,z2,z672,z3,z4,z8,z6]),(0,[z32,z1,z3,z81,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z15,z352]),(0,[z673,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z210,z8,z6]),(0,[z1,z2,z4,z210,z8,z45,z6])],[(0,[z30,z1,z2,z3,z4,z8,z15]),(0,[z674,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z675,z6])],[(0,[z1,z337,z3,z4,z8,z6,z15]),(0,[z1,z2,z83,z3,z4,z16,z6])],[(1,[z0,z2,z3,z4,z40,z6]),(0,[z676,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z677,z4,z8,z6])],[(0,[z1,z12,z2,z3,z370,z8,z6]),(0,[z1,z2,z3,z4,z8,z97,z6]),(0,[z1,z2,z3,z678,z4,z8,z6]),(0,[z679,z1,z2,z3,z4,z8,z6])],[(1,[z1,z2,z62,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z680,z6]),(0,[z135,z1,z2,z3,z4,z8,z15]),(0,[z109,z1,z2,z57,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z72,z15]),(1,[z1,z337,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z681,z8,z6])],[(0,[z0,z35,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z45,z5,z6])],[(0,[z178,z78,z1,z3,z4,z8,z6]),(0,[z1,z2,z3,z682,z4,z8,z6]),(0,[z1,z2,z3,z683,z4,z8,z6])],[(0,[z1,z2,z3,z4,z66,z110,z6]),(0,[z1,z2,z3,z4,z8,z684,z6]),(0,[z32,z1,z2,z3,z82,z8,z6])],[(0,[z1,z12,z2,z3,z4,z8,z399]),(1,[z1,z2,z3,z4,z8,z331]),(0,[z1,z337,z2,z3,z4,z8,z15]),(0,[z1,z2,z92,z3,z4,z8,z15])],[(1,[z1,z2,z514,z4,z8,z6]),(0,[z188,z1,z2,z3,z4,z282,z6]),(1,[z1,z2,z3,z4,z8,z402]),(0,[z1,z2,z3,z4,z8,z13,z13]),(0,[z1,z2,z3,z4,z8,z6,z685]),(0,[z1,z2,z3,z4,z8,z6,z28])],[(0,[z346,z1,z2,z3,z4,z8,z6]),(0,[z109,z1,z2,z3,z179,z8,z6]),(0,[z35,z1,z2,z3,z4,z6,z112]),(0,[z686,z1,z2,z3,z4,z8,z6])],[(0,[z687,z1,z2,z3,z4,z8,z6]),(0,[z688,z1,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z320,z6])]],
   [[(0,[z689,z1,z2,z3,z4,z8,z6]),(0,[z56,z1,z2,z3,z4,z8,z13]),(0,[z0,z1,z2,z3,z4,z19,z6]),(0,[z1,z2,z3,z4,z8,z690,z6]),(0,[z1,z2,z3,z4,z8,z221,z6]),(0,[z1,z2,z3,z4,z691,z8,z6]),(0,[z1,z2,z3,z4,z692,z8,z6]),(0,[z1,z2,z96,z4,z8,z146,z6])],[(1,[z188,z204,z3,z4,z8,z6]),(0,[z229,z1,z2,z3,z4,z8,z6]),(0,[z229,z109,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z4,z148,z8,z13])],[(0,[z693,z1,z2,z3,z4,z8,z6]),(0,[z1,z12,z2,z3,z4,z419,z6]),(0,[z109,z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z36,z3,z4,z8,z15]),(0,[z109,z1,z2,z3,z4,z302,z6]),(0,[z1,z2,z3,z4,z694,z8,z6]),(0,[z695,z1,z2,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z696,z8,z6]),(0,[z1,z2,z3,z4,z697,z8,z6]),(0,[z1,z2,z3,z4,z8,z698,z6]),(0,[z1,z2,z3,z4,z699,z8,z6]),(0,[z1,z300,z2,z3,z4,z65,z6]),(0,[z1,z300,z2,z3,z4,z8,z13]),(0,[z700,z1,z2,z3,z4,z8,z6]),(1,[z109,z1,z2,z90,z8,z6])],[(0,[z701,z1,z2,z3,z4,z8,z6]),(0,[z30,z1,z2,z3,z4,z392,z6]),(0,[z1,z300,z2,z3,z4,z8,z171]),(0,[z1,z2,z36,z3,z10,z8,z6])],[(0,[z1,z2,z3,z4,z8,z702,z6]),(1,[z56,z2,z3,z134,z8,z6]),(0,[z1,z2,z3,z4,z392,z8,z6]),(0,[z1,z2,z3,z4,z8,z703,z6]),(0,[z704,z1,z2,z3,z4,z8,z6])],[(1,[z1,z2,z3,z147,z8,z6]),(0,[z1,z705,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z11,z15])],[(0,[z1,z2,z204,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z706,z8,z6]),(0,[z1,z2,z3,z4,z8,z66,z6]),(0,[z180,z1,z2,z3,z4,z8,z15]),(1,[z1,z117,z3,z82,z8,z6]),(0,[z1,z2,z3,z4,z8,z380,z6]),(0,[z1,z2,z3,z4,z8,z15,z105])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z530,z1,z3,z4,z8,z15]),(0,[z1,z2,z3,z8,z707,z6]),(0,[z1,z2,z3,z4,z6,z708]),(0,[z1,z709,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z710,z6]),(0,[z1,z2,z83,z4,z210,z291])],[(0,[z1,z2,z445,z4,z8,z6]),(0,[z1,z2,z711,z4,z8,z6]),(0,[z1,z198,z2,z3,z4,z15]),(0,[z32,z1,z3,z4,z8,z143]),(0,[z1,z2,z3,z81,z221,z6]),(0,[z63,z1,z2,z4,z8,z75]),(0,[z35,z1,z2,z4,z336,z6]),(0,[z1,z2,z3,z712,z5,z6])],[(0,[z1,z2,z3,z4,z713,z6]),(0,[z1,z2,z3,z4,z360,z6]),(0,[z1,z3,z4,z82,z8,z143]),(0,[z32,z1,z3,z81,z8,z15]),(0,[z1,z2,z191,z3,z18,z6]),(0,[z714,z1,z2,z3,z8,z6]),(0,[z1,z2,z3,z715,z8,z6]),(0,[z1,z202,z3,z4,z8,z105])],[(0,[z188,z204,z514,z4,z8,z6]),(0,[z716,z1,z2,z4,z8,z6]),(0,[z1,z3,z4,z8,z717,z6]),(0,[z73,z1,z718,z4,z8,z6]),(0,[z1,z2,z3,z4,z419,z399]),(0,[z1,z2,z3,z4,z37,z13]),(0,[z1,z235,z3,z10,z4,z8])],[(0,[z140,z2,z61,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z409]),(0,[z1,z2,z719,z4,z8,z6]),(0,[z1,z2,z496,z4,z8,z301]),(0,[z1,z2,z3,z4,z145,z6]),(0,[z1,z2,z96,z4,z285,z8]),(0,[z1,z2,z3,z8,z11,z720])],[(0,[z1,z2,z3,z4,z721,z6]),(0,[z1,z2,z722,z4,z8,z6]),(0,[z1,z2,z723,z4,z8,z6]),(0,[z78,z158,z3,z4,z8,z15]),(0,[z193,z1,z3,z4,z8,z15]),(0,[z1,z2,z724,z3,z4,z8]),(0,[z1,z628,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z725]),(0,[z1,z726,z3,z4,z8,z6])],[(0,[z1,z2,z3,z8,z727,z6]),(0,[z68,z1,z2,z3,z8,z13]),(0,[z1,z2,z3,z18,z253,z6]),(0,[z1,z2,z3,z4,z31,z23]),(0,[z728,z1,z2,z4,z8,z15]),(0,[z1,z235,z3,z4,z8,z13]),(0,[z1,z3,z4,z8,z13,z99]),(0,[z1,z2,z3,z4,z271,z76]),(0,[z1,z2,z3,z4,z16,z22])],[(0,[z1,z2,z3,z729,z8,z6]),(0,[z1,z2,z3,z730,z8,z6]),(0,[z1,z3,z4,z8,z113,z15]),(0,[z1,z2,z731,z3,z4,z15]),(0,[z617,z1,z3,z4,z8,z13]),(0,[z732,z2,z3,z4,z8,z6]),(0,[z1,z733,z3,z4,z8,z6])]],
   [[(0,[z734,z1,z2,z3,z4,z8]),(0,[z2,z3,z735,z148,z8,z6]),(0,[z1,z2,z3,z4,z8,z736]),(0,[z1,z117,z3,z82,z8,z331])],[(0,[z133,z2,z252,z4,z8,z13]),(0,[z1,z2,z3,z4,z737,z6]),(0,[z1,z3,z4,z738,z110,z6])],[(0,[z1,z3,z4,z124,z8,z15]),(0,[z1,z2,z3,z4,z392,z13]),(0,[z1,z2,z3,z4,z8,z739]),(0,[z1,z2,z3,z4,z8,z740])],[(0,[z1,z741,z3,z4,z8,z6]),(0,[z2,z3,z4,z735,z8,z6]),(0,[z1,z2,z3,z4,z742,z6]),(0,[z2,z3,z4,z743,z66,z6]),(0,[z1,z2,z3,z4,z744,z15]),(0,[z372,z2,z3,z4,z8,z219])],[(0,[z188,z204,z3,z147,z8,z6]),(0,[z1,z131,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z720])],[(0,[z1,z606,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z745,z6]),(0,[z1,z12,z3,z4,z8,z15]),(0,[z1,z746,z2,z3,z4,z6]),(0,[z1,z2,z59,z3,z5,z6]),(0,[z1,z2,z57,z179,z8,z6]),(0,[z1,z202,z3,z4,z8,z280])],[(0,[z1,z747,z3,z4,z8,z6]),(0,[z748,z1,z3,z4,z8,z6]),(0,[z1,z2,z749,z3,z8,z6]),(0,[z1,z2,z3,z4,z8,z750])],[(0,[z1,z3,z4,z147,z8,z15]),(0,[z751,z1,z2,z3,z8,z6]),(0,[z229,z1,z2,z3,z261,z6]),(0,[z30,z467,z2,z3,z4,z8]),(0,[z1,z607,z3,z82,z8,z6]),(0,[z1,z3,z4,z332,z8,z15]),(0,[z1,z2,z92,z3,z5,z13]),(0,[z381,z1,z3,z4,z8,z13])]],
   [[(0,[z188,z1,z3,z4,z8,z15]),(0,[z1,z53,z2,z62,z3,z4]),(0,[z85,z2,z3,z4,z66,z243]),(0,[z1,z3,z4,z8,z335,z15]),(0,[z1,z2,z3,z4,z752,z6]),(0,[z1,z2,z3,z4,z6,z753]),(0,[z1,z2,z3,z227,z6,z112])],[(0,[z1,z2,z3,z4,z8,z754]),(0,[z1,z3,z755,z4,z8,z6]),(0,[z1,z2,z4,z8,z756,z6]),(0,[z30,z2,z3,z4,z8,z757]),(0,[z1,z2,z3,z4,z419,z13]),(0,[z1,z462,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z758,z13]),(0,[z1,z2,z191,z3,z4,z6]),(0,[z1,z2,z600,z3,z5,z6])],[(0,[z188,z747,z3,z4,z8,z6]),(0,[z1,z2,z3,z759,z8,z6]),(0,[z193,z1,z49,z4,z8,z6]),(0,[z1,z2,z3,z4,z31,z13]),(0,[z1,z2,z3,z4,z760,z6]),(0,[z109,z1,z3,z82,z8,z15]),(0,[z1,z2,z3,z190,z8,z171]),(1,[z1,z3,z4,z8,z761]),(0,[z1,z3,z4,z341,z8,z15])],[(0,[z1,z2,z3,z4,z8,z762]),(0,[z1,z2,z3,z4,z763,z6]),(0,[z1,z2,z3,z4,z764,z6])],[(0,[z1,z2,z3,z4,z8,z765]),(0,[z0,z2,z3,z4,z40,z6]),(0,[z1,z2,z3,z14,z8,z222]),(0,[z132,z1,z3,z4,z8,z15])],[(0,[z1,z2,z3,z766,z8,z6]),(0,[z135,z1,z3,z4,z65,z15]),(0,[z1,z2,z3,z767,z4,z6]),(0,[z1,z2,z3,z4,z8,z768])],[(0,[z188,z1,z3,z422,z8,z15]),(0,[z1,z3,z29,z60,z8,z6]),(0,[z1,z2,z3,z208,z8,z6]),(0,[z1,z2,z3,z4,z91,z13])],[(0,[z188,z446,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z769,z6]),(0,[z1,z337,z3,z4,z8,z15])]],
   [[(0,[z1,z2,z3,z4,z8,z770]),(0,[z188,z51,z3,z4,z8,z6]),(0,[z1,z2,z771,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z772]),(0,[z1,z2,z773,z4,z8,z6]),(0,[z0,z2,z3,z305,z4,z6]),(0,[z1,z2,z3,z774,z8,z6]),(0,[z1,z775,z2,z3,z4,z8]),(0,[z1,z2,z4,z8,z6,z776])],[(0,[z2,z747,z3,z4,z8,z6]),(0,[z1,z3,z354,z4,z8,z15]),(0,[z1,z2,z3,z4,z40,z95]),(0,[z1,z12,z3,z4,z360,z15]),(0,[z1,z322,z3,z4,z8,z399]),(0,[z1,z3,z4,z8,z777,z15]),(0,[z1,z2,z3,z114,z110,z6]),(0,[z1,z2,z3,z114,z8,z88]),(0,[z1,z2,z3,z4,z271,z15]),(0,[z1,z2,z3,z4,z8,z778]),(0,[z1,z2,z3,z4,z8,z779])],[(0,[z86,z1,z3,z4,z8,z15]),(0,[z780,z1,z2,z3,z4,z6]),(0,[z1,z12,z49,z4,z8,z6]),(0,[z1,z290,z3,z82,z8,z15]),(0,[z401,z1,z3,z4,z8,z15])],[(0,[z188,z1,z445,z4,z8,z15]),(0,[z1,z2,z3,z4,z781,z6]),(0,[z1,z49,z718,z4,z8,z6]),(0,[z32,z1,z3,z782,z8,z6]),(0,[z1,z2,z4,z210,z783,z6])],[(0,[z1,z2,z514,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z784]),(0,[z1,z2,z3,z4,z8,z785]),(0,[z1,z3,z4,z364,z8,z15]),(0,[z786,z1,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z8,z787]),(0,[z1,z2,z3,z4,z8,z788]),(0,[z1,z2,z3,z789,z8,z6]),(0,[z1,z2,z3,z4,z8,z790]),(0,[z1,z2,z3,z791,z8,z6]),(0,[z1,z2,z3,z4,z792,z13]),(0,[z1,z2,z96,z4,z146,z362])],[(0,[z1,z2,z3,z4,z743,z6]),(0,[z1,z2,z4,z8,z146,z776]),(0,[z132,z1,z3,z4,z37,z6])],[(0,[z193,z1,z3,z4,z8,z793]),(0,[z1,z2,z794,z3,z4,z6]),(0,[z35,z1,z2,z3,z4,z291]),(0,[z505,z1,z2,z3,z5,z6])]],
   [[(0,[z180,z183,z3,z4,z8,z23]),(0,[z73,z1,z74,z4,z8,z6])],[(0,[z140,z2,z29,z61,z8,z6]),(0,[z27,z1,z2,z4,z8,z75]),(0,[z795,z2,z3,z4,z8,z6])],[(0,[z796,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z797,z8,z6])],[(0,[z1,z2,z3,z4,z798,z6]),(0,[z1,z2,z3,z799,z8,z6]),(0,[z1,z2,z3,z4,z8,z800]),(0,[z1,z2,z3,z65,z41,z6]),(0,[z1,z2,z3,z355,z8,z15]),(0,[z1,z801,z2,z3,z4,z8]),(0,[z1,z2,z3,z190,z8,z88]),(0,[z1,z2,z3,z18,z227,z6])],[(0,[z1,z2,z802,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z803]),(0,[z1,z2,z3,z4,z804,z6]),(0,[z1,z2,z3,z4,z8,z171]),(0,[z1,z2,z36,z3,z8,z720])],[(0,[z1,z2,z3,z147,z8,z6]),(0,[z1,z2,z805,z4,z8,z6]),(0,[z68,z1,z3,z60,z8,z6]),(0,[z1,z2,z57,z428,z8,z6]),(0,[z185,z1,z74,z4,z8,z6]),(0,[z1,z2,z3,z4,z806,z13]),(0,[z1,z2,z3,z4,z8,z807]),(0,[z1,z2,z83,z4,z210,z406])],[(0,[z1,z2,z3,z808,z8,z6]),(0,[z1,z12,z49,z4,z360,z6]),(0,[z1,z117,z3,z82,z8,z6]),(0,[z1,z2,z3,z4,z19,z291])],[(0,[z1,z2,z3,z429,z5,z6]),(0,[z35,z1,z2,z24,z45,z6]),(0,[z1,z2,z3,z4,z809,z6])]],
   [[(0,[z161,z2,z61,z4,z8,z6]),(0,[z1,z47,z3,z60,z4,z8]),(0,[z1,z2,z3,z370,z8,z15])],[(0,[z1,z2,z810,z3,z8,z6]),(0,[z68,z1,z2,z3,z8,z15]),(0,[z1,z2,z3,z4,z811,z6]),(0,[z229,z2,z3,z356,z8,z6]),(0,[z1,z2,z3,z4,z483,z13]),(0,[z1,z235,z3,z4,z8,z15]),(0,[z1,z2,z83,z4,z218,z6])],[(0,[z1,z812,z3,z4,z8,z6]),(0,[z1,z3,z417,z4,z8,z15]),(0,[z1,z2,z3,z41,z6,z112]),(0,[z30,z1,z3,z4,z8,z245]),(0,[z1,z12,z3,z4,z8,z342]),(0,[z813,z2,z3,z4,z8,z6]),(0,[z1,z718,z74,z4,z8,z6]),(0,[z1,z2,z3,z4,z814,z8]),(0,[z1,z2,z3,z4,z8,z815]),(0,[z1,z3,z420,z4,z8,z15]),(0,[z1,z300,z3,z4,z110,z171]),(0,[z1,z2,z3,z4,z8,z816]),(0,[z1,z2,z3,z24,z8,z6])],[(0,[z85,z2,z3,z4,z624,z6]),(0,[z1,z2,z3,z817,z8,z6])],[(0,[z133,z2,z252,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z818]),(0,[z1,z3,z4,z8,z819,z6]),(0,[z32,z1,z3,z81,z8,z6])],[(0,[z1,z2,z3,z4,z232,z13]),(0,[z188,z1,z3,z4,z8,z342]),(0,[z1,z2,z3,z4,z392,z15]),(0,[z182,z1,z2,z4,z45,z6])],[(0,[z165,z2,z252,z4,z8,z6]),(0,[z820,z1,z3,z4,z8,z6]),(0,[z73,z1,z74,z4,z8,z409]),(0,[z1,z2,z3,z4,z5,z291])],[(0,[z78,z158,z3,z4,z8,z6]),(0,[z193,z1,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z821]),(0,[z1,z12,z718,z4,z8,z6]),(0,[z1,z117,z3,z82,z8,z143])]],
   [[(0,[z1,z2,z445,z147,z8,z6]),(0,[z1,z822,z3,z4,z8,z6]),(0,[z1,z3,z240,z4,z8,z15])],[(0,[z73,z1,z514,z4,z8,z6]),(0,[z1,z2,z731,z3,z4,z6]),(0,[z1,z449,z3,z4,z8,z15]),(0,[z1,z2,z83,z4,z210,z13])],[(0,[z1,z2,z3,z823,z8,z6]),(0,[z1,z2,z3,z4,z8,z824]),(0,[z1,z2,z3,z4,z825,z6]),(0,[z1,z2,z92,z3,z5,z15]),(0,[z1,z489,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z76,z8])],[(0,[z78,z158,z3,z4,z8,z482]),(0,[z56,z1,z2,z3,z483,z6])],[(0,[z1,z2,z3,z4,z826,z6]),(0,[z315,z2,z3,z134,z8,z6]),(0,[z0,z2,z3,z208,z40,z6]),(0,[z1,z2,z3,z4,z8,z827]),(0,[z1,z2,z3,z4,z419,z15]),(0,[z1,z2,z3,z4,z8,z828]),(0,[z1,z829,z3,z4,z8,z6]),(0,[z27,z1,z202,z3,z4,z8])],[(0,[z1,z2,z3,z830,z8,z6]),(0,[z1,z2,z831,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z832]),(0,[z1,z2,z3,z370,z8,z402]),(0,[z1,z2,z3,z4,z8,z88]),(0,[z1,z3,z4,z8,z13,z15]),(0,[z1,z2,z3,z4,z833,z6])],[(0,[z1,z2,z3,z834,z8,z6]),(0,[z1,z2,z3,z4,z8,z835]),(0,[z229,z2,z3,z148,z8,z13]),(0,[z1,z2,z3,z4,z8,z836]),(0,[z1,z2,z3,z18,z573,z6]),(0,[z1,z2,z3,z4,z837,z8])],[(0,[z1,z2,z3,z838,z8,z6]),(0,[z1,z2,z3,z8,z839,z6]),(0,[z30,z1,z235,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z840]),(0,[z1,z2,z3,z4,z8,z841])]],
   [[(0,[z180,z1,z3,z4,z8,z245]),(0,[z1,z461,z3,z4,z8,z15]),(0,[z842,z1,z3,z4,z8,z6])],[(0,[z1,z2,z3,z422,z282,z6]),(0,[z1,z2,z3,z4,z282,z217]),(0,[z1,z2,z3,z4,z8,z843]),(0,[z1,z298,z3,z4,z8,z15]),(0,[z27,z1,z2,z3,z4,z118])],[(0,[z1,z844,z3,z4,z8,z6]),(0,[z1,z2,z62,z3,z29,z6]),(0,[z1,z2,z845,z3,z4,z6]),(0,[z1,z3,z4,z8,z846,z6]),(0,[z56,z2,z3,z735,z8,z6]),(0,[z2,z3,z4,z8,z757,z6]),(0,[z1,z389,z3,z4,z65,z6]),(0,[z109,z1,z2,z195,z90,z8])],[(0,[z1,z2,z3,z4,z8,z847]),(0,[z1,z300,z3,z4,z110,z88]),(0,[z109,z1,z2,z76,z90,z8]),(1,[z1,z2,z4,z783,z6])],[(0,[z1,z3,z4,z370,z8,z15]),(0,[z1,z2,z3,z4,z8,z848]),(0,[z1,z2,z3,z4,z8,z761]),(0,[z1,z2,z3,z4,z8,z849]),(0,[z1,z2,z3,z4,z850,z6]),(0,[z1,z2,z3,z4,z118,z6])],[(0,[z1,z2,z3,z4,z232,z217]),(0,[z1,z2,z3,z4,z221,z13])],[(0,[z188,z1,z3,z4,z8,z482]),(0,[z1,z851,z3,z4,z8,z6]),(0,[z1,z3,z4,z852,z8,z6]),(0,[z180,z2,z3,z464,z4,z8]),(0,[z132,z1,z3,z4,z8,z6]),(0,[z1,z270,z3,z81,z8,z6]),(0,[z1,z2,z4,z8,z853,z15]),(0,[z1,z2,z854,z3,z4,z6]),(0,[z1,z2,z3,z855,z8,z6])],[(0,[z188,z1,z3,z147,z8,z15]),(0,[z135,z1,z3,z4,z65,z6]),(0,[z1,z2,z239,z3,z4,z352])]],
   [[(0,[z1,z2,z3,z856,z4,z8]),(0,[z857,z1,z3,z4,z8,z6]),(0,[z1,z3,z134,z82,z8,z15]),(0,[z1,z2,z3,z4,z8,z858]),(0,[z1,z12,z49,z4,z8,z402]),(0,[z1,z2,z557,z3,z4,z112])],[(0,[z545,z78,z3,z4,z8,z15]),(0,[z1,z62,z3,z60,z4,z6]),(0,[z2,z252,z859,z4,z8,z6]),(0,[z1,z2,z3,z860,z8,z6]),(0,[z1,z2,z3,z4,z16,z698]),(0,[z1,z517,z3,z81,z8,z6]),(0,[z1,z2,z3,z4,z6,z861])],[(0,[z1,z53,z198,z2,z3,z4]),(0,[z1,z2,z3,z4,z5,z95]),(0,[z1,z2,z862,z3,z4,z8]),(0,[z35,z1,z2,z4,z325,z6]),(0,[z1,z2,z3,z4,z261,z15]),(0,[z1,z2,z96,z3,z4,z362]),(0,[z1,z2,z96,z4,z8,z21]),(0,[z1,z2,z36,z3,z118,z105])],[(0,[z1,z863,z3,z4,z8,z6]),(0,[z2,z859,z61,z4,z8,z6]),(0,[z1,z2,z62,z3,z4,z13]),(0,[z229,z460,z2,z3,z8,z6]),(0,[z1,z3,z370,z8,z6,z15]),(0,[z1,z2,z3,z4,z864,z6]),(0,[z1,z2,z3,z4,z271,z6]),(0,[z1,z235,z36,z3,z4,z8])],[(0,[z188,z1,z3,z4,z8,z865]),(0,[z1,z2,z3,z4,z866,z6]),(0,[z132,z1,z36,z3,z8,z105]),(0,[z867,z1,z2,z3,z4,z6])],[(0,[z188,z78,z3,z4,z8,z15]),(0,[z180,z1,z235,z3,z4,z8]),(0,[z1,z2,z3,z4,z868,z15]),(0,[z1,z235,z3,z4,z8,z146]),(0,[z1,z2,z3,z677,z19,z6])],[(0,[z1,z2,z3,z8,z869,z6]),(0,[z1,z2,z3,z4,z453,z13])],[(0,[z78,z3,z653,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z870]),(0,[z1,z2,z3,z4,z8,z871]),(0,[z1,z2,z36,z3,z8,z69]),(0,[z1,z872,z3,z4,z8,z6])]],
   [[(0,[z1,z2,z3,z4,z873,z6]),(0,[z1,z2,z3,z4,z282,z262]),(0,[z1,z2,z3,z874,z8,z6]),(0,[z2,z3,z4,z40,z743,z6]),(0,[z1,z2,z3,z4,z8,z875]),(0,[z1,z2,z3,z876,z8,z6]),(1,[z1,z2,z3,z8,z720]),(0,[z1,z2,z3,z4,z16,z841])],[(0,[z1,z49,z514,z4,z8,z6]),(0,[z1,z2,z3,z877,z8,z6]),(0,[z1,z2,z3,z4,z8,z878])],[(0,[z1,z2,z3,z4,z8,z879]),(0,[z1,z2,z3,z4,z880,z6]),(0,[z1,z2,z3,z4,z8,z173]),(0,[z1,z2,z3,z114,z65,z6]),(0,[z1,z2,z3,z114,z8,z13]),(0,[z1,z322,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z881,z6])],[(0,[z1,z2,z3,z4,z8,z882]),(0,[z1,z2,z514,z147,z8,z6]),(0,[z1,z3,z4,z8,z865,z15]),(0,[z85,z2,z3,z4,z66,z6]),(0,[z1,z2,z3,z114,z8,z171]),(0,[z1,z3,z516,z4,z8,z15])],[(0,[z1,z2,z3,z4,z282,z15]),(0,[z1,z2,z3,z4,z232,z262]),(0,[z1,z2,z3,z4,z883,z6]),(0,[z1,z2,z3,z4,z483,z15]),(0,[z2,z3,z4,z8,z23,z757]),(0,[z1,z2,z3,z90,z261,z6])],[(0,[z1,z2,z3,z355,z8,z6]),(0,[z1,z2,z3,z4,z884,z6]),(0,[z1,z2,z92,z3,z712,z6])],[(0,[z1,z2,z83,z608,z4,z6]),(0,[z1,z2,z3,z4,z8,z885])],[(0,[z193,z1,z62,z3,z4,z6]),(0,[z1,z2,z886,z3,z4,z8]),(0,[z1,z439,z3,z4,z8,z13]),(0,[z1,z2,z83,z3,z4,z291])]],
   [[(0,[z1,z2,z3,z4,z232,z15]),(0,[z1,z53,z2,z3,z29,z8]),(0,[z1,z2,z3,z887,z8,z6])],[(0,[z1,z2,z47,z3,z29,z8]),(0,[z1,z2,z586,z3,z4,z112]),(0,[z30,z2,z3,z4,z392,z72]),(0,[z1,z2,z3,z4,z8,z757]),(0,[z1,z2,z3,z4,z888,z6]),(1,[z1,z2,z4,z8,z776])],[(0,[z1,z2,z3,z626,z5,z6]),(0,[z1,z2,z3,z370,z8,z6]),(0,[z1,z2,z3,z4,z889,z15]),(0,[z1,z2,z4,z8,z783,z6]),(0,[z1,z2,z3,z597,z5,z6])],[(0,[z78,z1,z3,z4,z8,z15]),(0,[z306,z1,z3,z4,z8,z15]),(0,[z2,z3,z859,z4,z8,z6]),(0,[z1,z235,z3,z4,z8,z6]),(0,[z1,z2,z3,z890,z8,z6]),(0,[z1,z2,z269,z3,z5,z6]),(0,[z372,z1,z3,z4,z8,z15]),(0,[z1,z2,z290,z3,z8,z105]),(0,[z1,z2,z3,z18,z199,z6])],[(0,[z1,z2,z3,z891,z8,z6]),(0,[z1,z2,z3,z4,z892,z6]),(0,[z1,z2,z3,z190,z8,z13]),(0,[z1,z2,z83,z4,z210,z15]),(0,[z1,z3,z893,z4,z8,z6])],[(0,[z1,z2,z3,z4,z894,z6]),(0,[z1,z2,z895,z3,z8,z6]),(0,[z78,z747,z3,z4,z8,z6]),(0,[z1,z3,z60,z4,z8,z13]),(0,[z1,z2,z896,z3,z4,z8]),(0,[z1,z2,z897,z4,z8,z6]),(0,[z1,z3,z4,z8,z15,z566])],[(0,[z670,z1,z2,z3,z5,z6]),(0,[z1,z2,z3,z286,z8,z11]),(0,[z898,z2,z3,z4,z8,z6])],[(0,[z1,z2,z899,z4,z8,z6]),(0,[z1,z202,z3,z4,z8,z6]),(0,[z1,z900,z2,z3,z4,z8]),(0,[z1,z2,z797,z90,z8,z6]),(0,[z1,z2,z526,z3,z5,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z399]),(0,[z1,z2,z179,z797,z8,z6])],[(0,[z1,z2,z3,z901,z8,z6]),(0,[z30,z2,z3,z4,z31,z72]),(0,[z1,z2,z3,z355,z360,z6]),(0,[z312,z1,z3,z4,z8,z15])],[(0,[z1,z2,z3,z902,z8,z6]),(0,[z30,z2,z3,z4,z8,z136]),(0,[z1,z2,z3,z4,z8,z903]),(0,[z1,z117,z3,z782,z8,z6]),(0,[z1,z2,z3,z4,z16,z115]),(0,[z1,z2,z3,z4,z712,z6])],[(0,[z1,z2,z3,z82,z261,z6]),(0,[z1,z2,z191,z3,z227,z6])],[(0,[z1,z2,z3,z904,z8,z6]),(0,[z1,z2,z859,z4,z8,z6]),(0,[z193,z1,z53,z3,z4,z8]),(0,[z1,z2,z3,z4,z6,z905]),(0,[z229,z1,z2,z3,z483,z6]),(0,[z1,z70,z3,z4,z8,z15]),(0,[z1,z2,z3,z8,z41,z6]),(0,[z109,z1,z2,z271,z90,z6]),(0,[z1,z2,z92,z3,z5,z6]),(0,[z1,z906,z3,z4,z8,z6])],[(0,[z188,z204,z3,z4,z282,z6]),(0,[z1,z611,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z907,z6])],[(0,[z372,z2,z3,z4,z8,z23]),(0,[z1,z2,z3,z4,z419,z6]),(0,[z1,z2,z3,z370,z360,z6]),(0,[z1,z2,z3,z4,z8,z908])],[(0,[z1,z2,z3,z4,z8,z909]),(0,[z1,z2,z3,z4,z302,z15]),(0,[z1,z2,z3,z4,z16,z480]),(0,[z1,z910,z3,z4,z8,z6])]],
   [[(0,[z158,z747,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z221,z15]),(0,[z1,z476,z2,z3,z4,z104])],[(1,[z747,z3,z4,z8,z6]),(0,[z68,z1,z2,z62,z3,z6]),(0,[z1,z3,z4,z8,z6,z911]),(0,[z1,z912,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z913,z6]),(0,[z1,z2,z3,z4,z914,z6]),(0,[z1,z2,z3,z4,z8,z915]),(0,[z1,z2,z3,z4,z916,z6]),(0,[z1,z2,z3,z227,z8,z6]),(0,[z917,z1,z2,z3,z4,z8])],[(0,[z178,z1,z514,z4,z8,z6]),(0,[z180,z3,z4,z8,z23,z245]),(0,[z1,z2,z3,z4,z569,z22]),(0,[z1,z2,z3,z4,z918,z6]),(0,[z1,z2,z3,z4,z8,z919])],[(0,[z1,z2,z3,z4,z8,z920]),(0,[z140,z198,z2,z61,z4,z6]),(0,[z1,z2,z921,z3,z8,z6]),(0,[z1,z2,z3,z4,z922,z6]),(0,[z229,z2,z3,z735,z8,z6]),(0,[z1,z2,z83,z3,z4,z95]),(0,[z1,z2,z3,z8,z923,z15]),(0,[z1,z2,z3,z4,z8,z924])],[(0,[z1,z2,z3,z4,z8,z925]),(0,[z1,z2,z926,z3,z4,z8]),(0,[z1,z3,z74,z4,z8,z342]),(0,[z1,z2,z3,z4,z360,z399])],[(0,[z1,z2,z3,z927,z8,z6]),(0,[z193,z1,z3,z29,z8,z6]),(0,[z133,z2,z859,z4,z8,z6]),(0,[z1,z2,z3,z82,z483,z6]),(0,[z1,z12,z74,z4,z8,z15])],[(0,[z1,z2,z3,z4,z8,z13]),(0,[z193,z1,z47,z3,z4,z8]),(0,[z1,z3,z4,z391,z8,z15]),(0,[z1,z2,z3,z4,z8,z928]),(0,[z1,z2,z3,z4,z8,z929]),(0,[z451,z2,z3,z4,z8,z386]),(0,[z930,z2,z3,z4,z8,z6]),(0,[z1,z2,z4,z783,z45,z6]),(0,[z27,z1,z2,z4,z8,z518])],[(0,[z1,z2,z3,z4,z931,z6]),(0,[z1,z2,z3,z4,z932,z6]),(0,[z1,z2,z3,z4,z8,z933]),(0,[z1,z2,z3,z934,z8,z6]),(0,[z1,z295,z3,z4,z65,z6]),(0,[z1,z663,z3,z4,z8,z15])]],
   [[(0,[z1,z2,z3,z4,z8,z935]),(0,[z183,z1,z3,z4,z8,z13]),(0,[z1,z2,z234,z4,z8,z247]),(0,[z1,z2,z3,z4,z936,z13])],[(0,[z1,z3,z147,z8,z6,z15]),(0,[z1,z61,z74,z4,z8,z15]),(0,[z1,z2,z3,z4,z453,z15]),(0,[z1,z2,z57,z420,z8,z6]),(0,[z1,z2,z3,z4,z37,z15]),(0,[z1,z2,z3,z4,z8,z937])],[(0,[z747,z204,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z938]),(0,[z1,z2,z939,z3,z4,z8]),(0,[z1,z2,z3,z4,z66,z95]),(0,[z1,z2,z3,z4,z8,z940]),(0,[z1,z2,z3,z4,z792,z6])],[(0,[z178,z1,z3,z147,z8,z6]),(0,[z1,z2,z3,z4,z8,z941])],[(0,[z1,z2,z3,z422,z8,z13]),(0,[z1,z2,z942,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z943]),(0,[z1,z2,z3,z4,z944,z6]),(0,[z1,z2,z3,z945,z8,z6]),(0,[z1,z2,z3,z4,z8,z946]),(0,[z1,z2,z947,z3,z4,z8]),(0,[z1,z300,z3,z4,z738,z6]),(0,[z1,z300,z3,z4,z110,z13]),(0,[z1,z2,z3,z4,z8,z948]),(0,[z1,z2,z3,z4,z261,z6])],[(0,[z1,z2,z3,z4,z949,z6]),(0,[z1,z2,z3,z4,z950,z6])],[(0,[z1,z951,z2,z3,z4,z8]),(0,[z1,z198,z2,z3,z4,z6]),(0,[z1,z541,z3,z4,z8,z15]),(0,[z109,z1,z2,z797,z8,z6]),(0,[z1,z2,z3,z4,z952,z6]),(0,[z27,z1,z2,z4,z8,z776])],[(0,[z1,z2,z3,z4,z868,z6]),(0,[z540,z2,z3,z148,z8,z6]),(0,[z540,z1,z3,z4,z8,z15])]],
   [[(0,[z78,z1,z3,z4,z8,z342]),(0,[z2,z3,z4,z743,z8,z6]),(0,[z953,z1,z3,z4,z8,z6]),(0,[z1,z524,z3,z4,z8,z13]),(0,[z1,z2,z195,z191,z3,z4]),(0,[z1,z2,z3,z10,z694,z8])],[(0,[z1,z2,z445,z4,z8,z13]),(1,[z2,z3,z4,z743,z6]),(0,[z1,z12,z49,z355,z8,z6]),(0,[z1,z2,z3,z4,z13,z954])],[(0,[z1,z2,z955,z3,z4,z6]),(0,[z1,z334,z3,z4,z8,z13]),(0,[z1,z2,z956,z3,z4,z6]),(0,[z1,z2,z3,z4,z360,z13]),(0,[z1,z2,z3,z227,z16,z6])],[(0,[z1,z2,z3,z4,z957,z6]),(0,[z728,z1,z2,z4,z8,z6]),(0,[z1,z2,z3,z355,z8,z402]),(0,[z1,z2,z3,z4,z6,z958])],[(0,[z140,z2,z61,z4,z8,z13]),(0,[z2,z3,z4,z8,z757,z72]),(0,[z1,z322,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z145,z13]),(0,[z109,z1,z2,z191,z90,z6])],[(0,[z1,z2,z3,z4,z8,z959]),(0,[z1,z2,z3,z4,z960,z6]),(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z70,z3,z82,z8,z6]),(0,[z1,z2,z3,z4,z8,z962]),(0,[z1,z2,z3,z4,z963,z8]),(0,[z1,z2,z3,z4,z8,z964])],[(0,[z1,z2,z3,z4,z282,z6]),(0,[z193,z68,z1,z3,z8,z6]),(0,[z1,z2,z3,z4,z965,z6]),(0,[z35,z1,z2,z3,z4,z95]),(0,[z1,z12,z49,z370,z8,z6]),(0,[z1,z600,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z436,z115])],[(0,[z1,z2,z3,z4,z966,z8]),(0,[z1,z2,z3,z4,z8,z967]),(0,[z1,z2,z3,z190,z8,z15]),(0,[z1,z2,z3,z4,z8,z968])]],
   [[(0,[z183,z1,z3,z4,z8,z217]),(0,[z1,z3,z60,z4,z8,z15]),(0,[z1,z53,z3,z60,z4,z8]),(0,[z1,z252,z74,z4,z8,z15]),(0,[z1,z603,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z31,z15]),(0,[z1,z604,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z744,z6]),(0,[z1,z2,z195,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z291])],[(0,[z188,z1,z514,z4,z8,z15]),(0,[z1,z2,z3,z4,z969,z6]),(0,[z1,z2,z3,z82,z221,z6]),(0,[z109,z1,z2,z351,z8,z6]),(1,[z1,z726,z3,z4,z8])],[(0,[z1,z2,z3,z4,z232,z6]),(0,[z1,z2,z3,z970,z8,z6]),(0,[z1,z2,z3,z4,z971,z6]),(0,[z32,z1,z3,z82,z8,z15]),(0,[z1,z2,z650,z3,z4,z112])],[(0,[z1,z2,z3,z4,z8,z972]),(1,[z1,z3,z4,z738,z6]),(0,[z1,z3,z4,z8,z13,z154])],[(0,[z1,z2,z3,z422,z8,z217]),(0,[z1,z2,z3,z973,z8,z6]),(0,[z1,z2,z3,z4,z8,z974]),(0,[z1,z2,z3,z4,z91,z15]),(0,[z1,z2,z3,z4,z8,z975])],[(0,[z1,z939,z3,z60,z4,z8]),(0,[z1,z2,z3,z4,z19,z95]),(0,[z1,z2,z3,z4,z976,z6]),(0,[z1,z2,z3,z4,z8,z977])],[(0,[z978,z1,z195,z3,z4,z8]),(0,[z1,z2,z83,z4,z210,z6])],[(0,[z1,z2,z979,z4,z8,z6]),(0,[z1,z2,z3,z980,z8,z6]),(0,[z129,z1,z3,z81,z8,z6]),(0,[z1,z2,z3,z4,z15,z362])]],
   [[(0,[z1,z2,z3,z422,z232,z6]),(0,[z1,z2,z981,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z982]),(0,[z1,z2,z3,z4,z8,z314]),(0,[z1,z2,z3,z4,z8,z983])],[(0,[z1,z2,z445,z4,z282,z6]),(0,[z78,z1,z3,z4,z8,z482]),(0,[z0,z2,z3,z40,z41,z6]),(0,[z135,z1,z3,z4,z65,z97]),(0,[z1,z2,z123,z3,z4,z104]),(0,[z1,z2,z3,z4,z984,z6]),(0,[z1,z2,z123,z3,z4,z841])],[(0,[z1,z2,z62,z47,z3,z4]),(0,[z1,z2,z3,z4,z8,z985]),(0,[z178,z1,z3,z4,z8,z761]),(0,[z1,z2,z123,z3,z4,z112])],[(0,[z1,z2,z3,z986,z8,z6]),(0,[z1,z2,z3,z4,z8,z987]),(0,[z1,z2,z3,z4,z988,z6]),(0,[z1,z3,z4,z8,z15,z654]),(0,[z1,z2,z989,z3,z8,z6])],[(0,[z1,z990,z3,z4,z8,z6]),(0,[z85,z1,z2,z3,z227,z6]),(0,[z0,z2,z3,z4,z40,z13]),(0,[z1,z2,z3,z4,z419,z402]),(0,[z1,z2,z3,z4,z8,z320]),(0,[z991,z1,z3,z4,z8,z6])],[(0,[z1,z2,z445,z4,z232,z6]),(0,[z1,z2,z992,z3,z4,z6]),(0,[z1,z993,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z994]),(0,[z1,z2,z3,z4,z6,z995]),(0,[z303,z1,z2,z3,z4,z112])],[(0,[z1,z49,z176,z4,z8,z6])],[(0,[z1,z2,z3,z4,z996,z6]),(0,[z1,z2,z3,z4,z997,z6]),(0,[z193,z1,z74,z4,z8,z6]),(0,[z1,z2,z3,z4,z998,z6]),(0,[z1,z290,z3,z82,z8,z6]),(0,[z1,z337,z3,z4,z8,z761]),(0,[z1,z3,z491,z4,z8,z15]),(0,[z1,z2,z3,z4,z999,z8])]],
   [[(0,[z1,z2,z3,z4,z8,z1000]),(0,[z85,z1,z2,z3,z41,z6]),(0,[z27,z1,z2,z3,z4,z31]),(0,[z1,z98,z2,z3,z8,z69])],[(0,[z1,z2,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z1001,z6]),(0,[z700,z2,z3,z4,z40,z6]),(0,[z1,z2,z3,z4,z1002,z6]),(0,[z1,z2,z3,z4,z302,z6]),(0,[z1,z2,z195,z3,z4,z271]),(0,[z1,z2,z3,z4,z16,z20])],[(0,[z1,z3,z4,z8,z245,z15]),(0,[z1,z2,z3,z16,z41,z6]),(0,[z1,z3,z74,z4,z8,z15]),(0,[z1,z12,z49,z4,z8,z13]),(0,[z1,z3,z504,z4,z8,z15]),(0,[z1,z2,z248,z179,z8,z6])],[(0,[z1,z2,z3,z422,z8,z262]),(0,[z1,z1003,z3,z4,z8,z6]),(0,[z183,z1,z3,z4,z8,z15]),(0,[z2,z3,z4,z1004,z8,z6])],[(0,[z1,z2,z514,z4,z8,z13]),(0,[z1,z2,z3,z4,z8,z1005]),(0,[z1,z2,z3,z1006,z8,z6]),(0,[z1,z2,z3,z4,z8,z95]),(0,[z35,z1,z2,z39,z4,z6]),(0,[z1,z12,z3,z4,z8,z736]),(0,[z1,z3,z782,z82,z8,z6]),(0,[z1,z3,z4,z82,z8,z15]),(0,[z32,z1,z3,z498,z8,z6]),(0,[z1,z2,z3,z4,z8,z1007])],[(0,[z1,z2,z3,z4,z8,z777])],[(1,[z1,z3,z147,z8,z15]),(0,[z1,z2,z3,z4,z8,z1008]),(0,[z1,z2,z3,z4,z1009,z6]),(0,[z1,z3,z645,z4,z8,z15]),(0,[z1,z2,z3,z8,z712,z6])],[(0,[z1,z2,z3,z422,z8,z15]),(0,[z265,z2,z3,z4,z66,z6]),(0,[z1,z3,z4,z8,z399,z15]),(0,[z32,z1,z3,z4,z8,z777]),(0,[z1,z300,z3,z4,z110,z15]),(0,[z1,z559,z3,z4,z8,z15]),(0,[z35,z1,z2,z597,z4,z6]),(0,[z1,z2,z3,z4,z8,z1010])]],
   [[(0,[z188,z204,z3,z4,z8,z13]),(0,[z1,z1011,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z562,z2,z3,z5,z6])],[(0,[z1,z2,z3,z4,z8,z1013]),(0,[z1,z2,z3,z4,z8,z1014]),(0,[z1,z2,z3,z1015,z8,z6]),(0,[z109,z1,z2,z90,z8,z13]),(0,[z1,z2,z3,z227,z45,z6])],[(0,[z1,z2,z3,z4,z8,z1016]),(0,[z68,z1,z198,z2,z3,z6]),(0,[z1,z3,z4,z8,z13,z245]),(0,[z463,z1,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z15,z753]),(0,[z1,z2,z3,z4,z37,z6])],[(0,[z1,z2,z445,z4,z8,z15]),(0,[z1,z2,z3,z4,z1017,z6]),(0,[z1,z1018,z2,z3,z4,z8]),(0,[z0,z2,z3,z4,z387,z6]),(0,[z1,z3,z659,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z1019])],[(0,[z1,z2,z3,z147,z8,z13]),(0,[z85,z2,z3,z4,z743,z6]),(0,[z1,z3,z4,z8,z301,z15]),(0,[z1,z705,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z1020,z6]),(0,[z1,z235,z3,z4,z8,z112]),(0,[z1,z235,z3,z4,z8,z22])],[(0,[z68,z1,z2,z3,z8,z6]),(0,[z1,z2,z1021,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z1022]),(0,[z1,z117,z3,z82,z8,z13]),(0,[z1,z2,z3,z1023,z4,z6])],[(0,[z140,z2,z61,z4,z8,z15]),(0,[z1,z3,z718,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1024]),(0,[z1,z2,z3,z4,z145,z15])]],
   [[(0,[z193,z1,z514,z4,z8,z6]),(0,[z178,z1,z3,z370,z8,z6]),(0,[z109,z1,z2,z90,z261,z6])],[(0,[z1,z2,z3,z4,z8,z1025]),(0,[z133,z2,z252,z4,z8,z6]),(0,[z1,z3,z4,z8,z1026,z6]),(0,[z1,z2,z3,z8,z1027,z6]),(0,[z1,z2,z3,z18,z19,z13]),(0,[z1,z2,z36,z3,z37,z105])],[(0,[z1,z2,z3,z4,z8,z1028]),(0,[z1,z2,z3,z4,z392,z6]),(0,[z1,z2,z3,z4,z8,z1029]),(0,[z1,z2,z3,z24,z8,z13]),(0,[z27,z1,z322,z4,z8,z28]),(1,[z1,z2,z3,z4,z841])],[(0,[z1,z3,z514,z4,z8,z15]),(0,[z1,z2,z3,z4,z6,z1030]),(0,[z1,z2,z36,z3,z26,z8])],[(0,[z1,z2,z514,z4,z282,z6]),(0,[z1,z2,z3,z29,z8,z13]),(0,[z1,z3,z4,z8,z1031,z6]),(0,[z229,z2,z3,z148,z8,z15]),(0,[z1,z2,z3,z4,z8,z1032]),(0,[z1033,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1034]),(0,[z1,z2,z3,z18,z712,z6])],[(0,[z1,z3,z782,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1035]),(0,[z1,z2,z3,z1036,z8,z6]),(0,[z1,z2,z3,z4,z8,z406]),(0,[z1,z1037,z3,z4,z8,z6]),(0,[z1038,z1,z3,z4,z8,z6]),(0,[z1,z202,z3,z4,z118,z6])],[(0,[z140,z2,z859,z4,z8,z6]),(0,[z174,z2,z3,z4,z66,z6]),(0,[z0,z1,z2,z3,z227,z6]),(0,[z1,z544,z3,z4,z8,z15]),(0,[z1,z2,z3,z1039,z8,z6]),(0,[z178,z1,z3,z4,z8,z399]),(0,[z1,z2,z3,z4,z1040,z6])],[(0,[z78,z158,z3,z4,z8,z13]),(0,[z1,z726,z3,z4,z90,z8])]],
   [[(0,[z1,z2,z514,z4,z232,z6]),(0,[z188,z204,z3,z4,z8,z217]),(0,[z1,z2,z3,z8,z1041,z6]),(0,[z1,z2,z3,z4,z8,z1042]),(0,[z1,z2,z3,z81,z261,z6]),(0,[z1,z2,z3,z227,z110,z6])],[(0,[z1,z2,z1043,z3,z4,z8]),(0,[z1,z2,z3,z4,z1044,z6]),(0,[z1,z2,z3,z4,z8,z1045]),(0,[z1,z2,z3,z4,z758,z6]),(0,[z1,z195,z726,z3,z4,z8]),(0,[z35,z1,z2,z227,z45,z6])],[(0,[z1,z2,z3,z4,z31,z6]),(0,[z180,z2,z3,z4,z8,z23]),(0,[z1,z607,z3,z4,z110,z6]),(0,[z1,z2,z496,z4,z8,z146])],[(0,[z1,z2,z3,z4,z8,z427]),(0,[z1,z2,z3,z4,z8,z793]),(0,[z1,z3,z4,z1046,z8,z6]),(0,[z1047,z1,z3,z4,z8,z6]),(0,[z1,z2,z96,z4,z8,z247]),(0,[z1,z2,z726,z3,z4,z8])],[(0,[z188,z204,z3,z4,z232,z6]),(0,[z56,z2,z3,z134,z483,z6]),(1,[z2,z3,z4,z8,z757]),(0,[z1,z1048,z3,z4,z8,z6])],[(0,[z1,z2,z3,z147,z282,z6]),(0,[z1,z2,z3,z4,z1049,z6]),(0,[z1,z2,z3,z4,z738,z6]),(0,[z1,z3,z4,z8,z13,z761]),(0,[z1,z1050,z3,z4,z8,z6]),(0,[z1,z2,z1051,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1052]),(0,[z27,z1,z2,z309,z4,z8])],[(0,[z1,z2,z3,z4,z8,z1053]),(0,[z68,z1,z2,z47,z3,z8]),(0,[z1,z2,z3,z4,z1054,z6]),(0,[z180,z2,z3,z4,z8,z386]),(0,[z1,z2,z3,z4,z8,z342]),(0,[z1,z2,z3,z4,z1055,z6]),(0,[z1,z2,z3,z4,z91,z6]),(0,[z160,z1,z3,z4,z8,z15]),(0,[z35,z1,z2,z4,z45,z13])],[(0,[z1,z2,z3,z4,z1056,z6]),(0,[z1,z256,z3,z4,z8,z15]),(0,[z0,z2,z3,z4,z40,z15]),(0,[z1,z12,z3,z355,z8,z15]),(0,[z1,z3,z4,z8,z320,z15]),(0,[z1,z300,z3,z190,z110,z6]),(0,[z1,z2,z3,z4,z8,z1057]),(0,[z1,z235,z3,z4,z8,z301])]],
   [[(0,[z1,z2,z3,z1058,z8,z6]),(0,[z1,z3,z4,z8,z736,z15]),(0,[z1,z2,z239,z3,z4,z112]),(0,[z1,z1059,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z841,z112])],[(0,[z1,z2,z3,z147,z232,z6]),(0,[z1,z2,z3,z4,z8,z1060]),(0,[z1,z2,z3,z1061,z8,z6]),(0,[z1,z2,z62,z3,z4,z15]),(0,[z1,z2,z3,z735,z8,z6]),(0,[z1,z2,z3,z4,z8,z1062]),(0,[z1,z2,z3,z4,z8,z1063])],[(0,[z1,z2,z3,z4,z8,z1064]),(0,[z1,z3,z4,z8,z15,z69]),(0,[z1,z2,z3,z4,z8,z1065]),(0,[z1,z2,z3,z1066,z8,z6])],[(0,[z1,z2,z4,z8,z853,z6]),(0,[z193,z1,z3,z4,z8,z821])],[(0,[z1,z12,z3,z370,z8,z15]),(1,[z1,z3,z782,z8,z6]),(0,[z178,z1,z3,z4,z8,z13]),(0,[z1,z2,z3,z4,z118,z13]),(0,[z1,z1067,z3,z4,z8,z6])],[(0,[z1,z514,z4,z8,z6,z15]),(0,[z30,z2,z3,z4,z8,z72]),(0,[z1,z2,z3,z4,z1068,z6]),(0,[z1,z2,z3,z1069,z8,z6]),(0,[z1,z2,z3,z8,z6,z720])],[(0,[z528,z1,z3,z4,z8,z15]),(0,[z1,z1070,z3,z4,z8,z6]),(0,[z1,z2,z4,z8,z6,z1071])],[(0,[z1,z2,z514,z4,z8,z15]),(0,[z188,z204,z3,z4,z8,z262]),(0,[z1,z2,z1072,z4,z8,z6]),(1,[z2,z859,z4,z8,z6]),(0,[z0,z2,z3,z4,z743,z6]),(0,[z1,z2,z3,z4,z221,z331]),(0,[z1,z2,z3,z4,z91,z143]),(0,[z1,z2,z83,z4,z783,z6]),(0,[z1,z2,z96,z3,z4,z118])]],
   [[(0,[z85,z403,z2,z3,z4,z6]),(0,[z1,z2,z3,z1073,z8,z6]),(0,[z1,z2,z3,z114,z8,z15]),(0,[z1,z2,z3,z4,z13,z362])],[(0,[z306,z1,z3,z4,z8,z245]),(0,[z1,z2,z3,z4,z287,z380])],[(0,[z1,z2,z3,z4,z8,z1074]),(0,[z1,z2,z3,z1075,z8,z6]),(0,[z1,z509,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z1076]),(0,[z1,z2,z3,z4,z287,z22]),(0,[z1,z2,z3,z547,z19,z6])],[(0,[z188,z204,z3,z4,z8,z15]),(0,[z1077,z1,z3,z4,z8,z6]),(0,[z1,z2,z1078,z3,z4,z8]),(0,[z1,z2,z3,z4,z783,z6]),(0,[z1,z2,z83,z4,z639,z6])],[(0,[z1,z3,z4,z8,z245,z6]),(0,[z1,z2,z3,z4,z8,z1079]),(0,[z86,z1,z3,z4,z65,z6])],[(0,[z183,z1,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z806,z6]),(0,[z161,z1,z3,z4,z8,z15]),(0,[z109,z1,z2,z90,z8,z15]),(0,[z109,z1,z2,z90,z302,z6]),(0,[z1,z2,z3,z4,z22,z841])],[(0,[z1,z2,z3,z4,z1080,z6]),(0,[z1,z2,z3,z4,z8,z1081]),(0,[z109,z1,z2,z297,z8,z6]),(0,[z1,z646,z3,z4,z8,z15])],[(0,[z1,z2,z3,z4,z8,z482]),(0,[z1,z2,z3,z8,z6,z1082]),(0,[z1,z596,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z1083])]],
   [[(0,[z1,z2,z3,z147,z8,z15]),(0,[z185,z1,z74,z4,z8,z15]),(0,[z1084,z2,z3,z4,z8,z6]),(0,[z1,z12,z3,z4,z419,z15]),(0,[z1,z131,z3,z4,z110,z6]),(0,[z1,z3,z4,z8,z761,z15])],[(0,[z1,z2,z3,z422,z8,z6]),(0,[z1,z2,z3,z4,z8,z217]),(0,[z1,z2,z3,z4,z483,z6]),(0,[z1085,z2,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z8,z1086]),(0,[z1,z117,z3,z82,z8,z15]),(0,[z978,z1,z3,z4,z8,z6]),(0,[z1,z2,z36,z3,z8,z105])],[(0,[z1,z672,z3,z4,z8,z13]),(0,[z32,z1,z3,z81,z8,z320]),(0,[z1,z2,z3,z4,z8,z1087]),(0,[z1,z235,z3,z4,z8,z28])],[(0,[z1,z2,z3,z4,z8,z1088]),(0,[z1,z2,z3,z4,z8,z243]),(0,[z85,z2,z3,z4,z66,z13]),(0,[z1,z2,z3,z4,z8,z1089]),(0,[z1,z202,z96,z3,z4,z8])],[(0,[z1,z2,z3,z4,z1090,z6]),(0,[z1,z2,z3,z4,z8,z1091]),(0,[z1,z3,z81,z782,z8,z6]),(0,[z1,z2,z3,z18,z19,z15])],[(0,[z1,z2,z3,z4,z8,z865]),(0,[z1,z2,z3,z4,z6,z954]),(0,[z1,z2,z3,z355,z8,z13]),(0,[z1,z2,z3,z24,z8,z15])],[(0,[z701,z1,z3,z4,z8,z15]),(0,[z1,z1092,z3,z60,z4,z8])],[(0,[z1,z2,z3,z29,z8,z15]),(0,[z2,z3,z134,z735,z8,z6]),(0,[z1,z12,z49,z4,z8,z399]),(0,[z1,z2,z3,z4,z889,z6]),(0,[z27,z1,z2,z4,z8,z28])]],
   [[(0,[z1,z2,z57,z179,z8,z13]),(0,[z1,z2,z96,z4,z8,z146])],[(0,[z1,z1093,z3,z4,z8,z6]),(0,[z56,z2,z3,z134,z453,z6]),(0,[z135,z1,z3,z4,z738,z6]),(0,[z1,z2,z3,z4,z580,z112])],[(0,[z1,z2,z3,z4,z8,z1094]),(0,[z1,z2,z3,z370,z8,z13]),(0,[z35,z1,z2,z4,z783,z6]),(0,[z27,z1,z235,z4,z8,z28]),(0,[z1,z2,z3,z4,z8,z1095]),(0,[z1,z202,z3,z4,z8,z11])],[(0,[z1,z2,z3,z10,z8,z222])],[(0,[z1,z2,z445,z422,z8,z6]),(0,[z1,z2,z445,z4,z8,z217]),(0,[z649,z2,z3,z4,z8,z23]),(1,[z1,z718,z4,z8,z6]),(0,[z1,z2,z191,z3,z4,z13]),(0,[z1,z2,z571,z3,z5,z6])],[(0,[z1096,z1,z3,z4,z8,z6]),(0,[z1,z2,z1097,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z1098]),(0,[z1,z12,z49,z4,z419,z6]),(0,[z1,z2,z3,z4,z760,z13]),(0,[z1,z2,z3,z1099,z8,z6]),(0,[z1,z2,z3,z4,z8,z1100])],[(0,[z229,z2,z3,z148,z8,z6]),(0,[z1,z2,z3,z506,z19,z6]),(0,[z1,z611,z3,z4,z110,z6]),(0,[z1,z618,z3,z4,z8,z15])],[(0,[z1,z2,z3,z4,z1101,z6]),(0,[z1,z202,z3,z4,z8,z13]),(0,[z132,z1,z3,z4,z118,z6])]],
   [[(0,[z1,z2,z3,z4,z8,z262]),(1,[z1,z514,z4,z8,z15]),(0,[z1,z2,z3,z1102,z8,z6]),(0,[z140,z2,z62,z61,z4,z6]),(0,[z56,z2,z3,z8,z387,z6]),(0,[z1,z2,z3,z4,z8,z1103]),(0,[z1,z2,z3,z4,z833,z15]),(0,[z1,z1104,z3,z4,z8,z6])],[(0,[z1,z2,z3,z4,z1105,z6]),(0,[z1,z2,z3,z1106,z8,z6]),(0,[z1,z1107,z3,z4,z8,z6]),(0,[z1,z2,z3,z208,z8,z13]),(0,[z1,z57,z3,z82,z8,z15]),(0,[z35,z1,z2,z4,z45,z15]),(0,[z185,z1,z2,z4,z8,z519]),(0,[z535,z1,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z776])],[(0,[z178,z1,z3,z4,z8,z320]),(0,[z1,z3,z4,z738,z8,z6]),(0,[z1,z2,z3,z4,z1108,z6])],[(0,[z1,z1109,z3,z4,z8,z6]),(0,[z1,z2,z3,z4,z1110,z6]),(0,[z1,z2,z3,z4,z91,z331]),(0,[z1,z2,z3,z4,z1111,z6])],[(0,[z1,z1112,z3,z4,z8,z6]),(0,[z1,z2,z3,z8,z41,z13]),(0,[z132,z1,z3,z4,z8,z320]),(0,[z27,z1,z2,z3,z4,z362])],[(0,[z1,z2,z1113,z3,z4,z8]),(0,[z1,z2,z3,z4,z221,z6]),(0,[z1,z3,z18,z82,z8,z15]),(0,[z1,z295,z3,z4,z8,z15])],[(0,[z1,z2,z1114,z4,z8,z6]),(0,[z193,z1,z198,z3,z4,z6]),(0,[z32,z1,z3,z4,z8,z15]),(0,[z1,z3,z82,z8,z5,z15]),(0,[z1,z2,z96,z4,z145,z146])],[(0,[z1,z646,z3,z82,z8,z6]),(0,[z1,z2,z3,z4,z118,z15])]],
   [[(0,[z689,z1,z3,z4,z8,z15]),(0,[z1,z2,z3,z8,z923,z6]),(0,[z73,z1,z74,z4,z8,z342]),(0,[z1,z2,z4,z797,z8,z6]),(0,[z1,z2,z3,z19,z712,z6])],[(0,[z1,z2,z3,z4,z8,z1115]),(0,[z1,z2,z3,z4,z1116,z6]),(0,[z1,z2,z3,z4,z1117,z8]),(0,[z1,z2,z3,z227,z65,z6]),(0,[z1,z2,z3,z227,z8,z13])],[(0,[z1118,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z8,z1119])],[(0,[z1,z2,z445,z4,z8,z262]),(0,[z188,z1,z3,z4,z282,z15]),(0,[z1,z1120,z2,z3,z4,z6]),(0,[z1,z2,z62,z3,z4,z6]),(0,[z73,z1,z74,z4,z8,z13]),(0,[z398,z1,z3,z4,z8,z15]),(0,[z1,z2,z83,z4,z6,z21])],[(0,[z1,z2,z191,z3,z4,z76]),(0,[z1,z2,z92,z3,z227,z6])],[(0,[z78,z3,z4,z8,z386,z15]),(0,[z1,z198,z2,z3,z29,z6]),(0,[z1,z2,z3,z4,z8,z1121])],[(0,[z1,z2,z3,z4,z453,z6]),(0,[z1,z3,z4,z175,z8,z15]),(0,[z1,z2,z3,z4,z221,z143]),(0,[z1,z117,z3,z82,z91,z6]),(0,[z1,z2,z3,z782,z8,z6]),(0,[z1,z2,z3,z4,z8,z1122]),(0,[z135,z1,z3,z4,z65,z173]),(0,[z1,z3,z4,z8,z13,z563])],[(0,[z188,z1,z3,z4,z232,z15]),(0,[z1,z2,z1123,z4,z8,z6]),(0,[z1,z2,z3,z4,z1124,z6]),(0,[z1,z2,z3,z1125,z8,z6]),(0,[z1,z2,z3,z18,z340,z6]),(0,[z1,z2,z4,z8,z776,z28])]],
   [[(0,[z1,z3,z176,z4,z8,z15]),(0,[z1,z2,z3,z4,z360,z15]),(0,[z1,z2,z3,z4,z8,z331]),(0,[z1,z2,z3,z4,z1126,z6])],[(0,[z1,z2,z3,z4,z8,z1127]),(0,[z1,z2,z3,z4,z8,z402]),(0,[z1,z2,z3,z4,z8,z1128]),(1,[z1,z2,z3,z712,z6])],[(0,[z1,z2,z3,z1129,z8,z6]),(0,[z1,z2,z3,z4,z8,z1130]),(0,[z1,z198,z2,z47,z3,z4]),(0,[z1,z2,z3,z4,z1131,z6]),(0,[z1,z2,z3,z114,z8,z6])],[],[(0,[z78,z158,z3,z4,z8,z427]),(0,[z1,z2,z3,z4,z31,z72]),(0,[z180,z2,z3,z4,z8,z757]),(0,[z1,z2,z3,z4,z1132,z6]),(0,[z1,z2,z3,z4,z261,z13]),(0,[z182,z1,z2,z90,z8,z6]),(0,[z1,z2,z3,z4,z8,z1133])],[(0,[z188,z204,z3,z4,z8,z6]),(0,[z1,z2,z3,z1134,z8,z6]),(0,[z1,z2,z3,z4,z8,z1135]),(0,[z56,z2,z3,z288,z8,z6]),(0,[z1,z2,z290,z3,z8,z266])],[(0,[z140,z53,z2,z61,z4,z8]),(0,[z1,z198,z2,z3,z4,z13]),(0,[z68,z1,z53,z2,z3,z8]),(0,[z129,z1,z3,z4,z8,z15]),(0,[z85,z2,z3,z4,z66,z15]),(0,[z1,z2,z3,z110,z41,z6])],[(0,[z1,z2,z514,z422,z8,z6]),(0,[z1,z2,z514,z4,z8,z217]),(0,[z140,z2,z47,z61,z4,z8]),(0,[z1,z2,z3,z4,z8,z1136]),(0,[z1,z2,z660,z3,z4,z112]),(0,[z32,z1,z3,z81,z8,z13]),(0,[z109,z1,z2,z90,z8,z6]),(0,[z1,z1137,z2,z3,z4,z6]),(0,[z1,z2,z272,z3,z5,z6]),(0,[z1,z2,z3,z4,z8,z1138])]],
   [[(0,[z1,z2,z3,z4,z8,z1139]),(0,[z1,z300,z3,z114,z110,z6]),(0,[z1,z270,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z1140,z6])],[(0,[z56,z2,z3,z134,z8,z6]),(0,[z85,z2,z3,z4,z66,z95]),(0,[z1,z2,z1141,z3,z4,z8]),(0,[z306,z2,z3,z4,z8,z136])],[(0,[z1,z2,z3,z4,z8,z1142]),(0,[z193,z1,z3,z4,z8,z13]),(0,[z1,z3,z4,z8,z761,z6])],[(0,[z188,z204,z3,z422,z8,z6]),(0,[z1,z2,z3,z4,z1143,z6]),(0,[z1,z74,z4,z8,z247,z15]),(0,[z1,z2,z57,z179,z8,z15]),(0,[z1,z517,z3,z4,z8,z15]),(0,[z1,z2,z191,z3,z5,z6])],[(0,[z140,z60,z61,z4,z8,z6]),(0,[z1,z2,z3,z1144,z8,z6]),(0,[z1,z2,z3,z190,z8,z6]),(0,[z1,z3,z4,z8,z15,z258]),(0,[z1,z2,z3,z286,z8,z280]),(0,[z1,z322,z3,z4,z8,z13]),(0,[z1,z2,z96,z4,z8,z776]),(0,[z1,z2,z3,z10,z8,z720])],[(0,[z1,z2,z3,z1145,z8,z6]),(0,[z1,z2,z3,z4,z1146,z6]),(0,[z1,z3,z60,z4,z8,z6]),(0,[z1,z2,z3,z4,z1147,z6]),(0,[z1,z2,z3,z4,z8,z1148]),(0,[z0,z1,z2,z3,z41,z6]),(0,[z1,z2,z3,z4,z1149,z6]),(0,[z1,z2,z3,z4,z360,z402]),(0,[z1,z3,z683,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z1150]),(0,[z1,z36,z202,z3,z8,z105])],[(0,[z1,z2,z3,z4,z282,z13]),(0,[z1,z2,z3,z8,z6,z1151]),(0,[z56,z1,z2,z3,z261,z6]),(0,[z1152,z1,z2,z3,z4,z8]),(0,[z185,z1,z2,z4,z8,z28]),(0,[z1,z2,z3,z18,z19,z6])],[(0,[z1,z2,z3,z1153,z8,z6]),(0,[z1,z2,z3,z4,z8,z1154]),(0,[z1,z2,z191,z3,z4,z15]),(0,[z1,z2,z3,z4,z6,z841])]],
   [[(0,[z188,z204,z445,z4,z8,z6]),(0,[z1,z2,z3,z147,z8,z217]),(0,[z1,z2,z1155,z3,z4,z8]),(0,[z454,z1,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z1156])],[(0,[z1,z2,z3,z4,z8,z1157]),(0,[z1,z2,z3,z29,z8,z6]),(0,[z1,z53,z2,z3,z4,z8]),(0,[z1,z2,z3,z1158,z8,z6])],[(0,[z1,z2,z3,z4,z8,z1159]),(0,[z1,z2,z47,z3,z4,z8]),(0,[z1,z1160,z3,z4,z8,z6]),(0,[z1,z202,z3,z4,z8,z15]),(0,[z1,z2,z366,z3,z4,z112])],[(0,[z1,z2,z1161,z3,z4,z6]),(0,[z1,z2,z3,z1162,z8,z6]),(0,[z1,z2,z3,z4,z623,z112])],[(0,[z1,z1092,z2,z3,z4,z8]),(0,[z1,z1163,z3,z4,z8,z6]),(0,[z1,z2,z3,z208,z8,z15])],[(0,[z1,z2,z1164,z4,z8,z6]),(0,[z1,z2,z3,z4,z1165,z6]),(0,[z1,z2,z3,z4,z8,z1166]),(0,[z1,z2,z3,z81,z483,z6]),(0,[z545,z2,z3,z4,z8,z72]),(0,[z1,z3,z82,z8,z222,z15]),(1,[z1,z2,z797,z8,z6]),(0,[z1,z2,z57,z797,z8,z6]),(0,[z1,z2,z3,z227,z210,z6])],[(0,[z1,z2,z514,z4,z8,z262]),(0,[z1,z323,z3,z4,z8,z15]),(0,[z1,z2,z718,z4,z8,z6]),(0,[z1,z2,z3,z1167,z8,z6]),(0,[z1168,z1,z2,z4,z8,z6])],[(0,[z1,z655,z3,z4,z8,z15]),(0,[z1,z2,z3,z8,z41,z15])]],
   [[(0,[z1,z2,z1169,z3,z4,z8]),(0,[z1,z2,z3,z4,z8,z1170]),(0,[z1,z2,z3,z4,z8,z1171]),(0,[z1,z2,z58,z3,z4,z112]),(0,[z1,z3,z4,z8,z22,z245]),(0,[z1,z12,z49,z4,z8,z15]),(0,[z1,z2,z3,z1172,z8,z6]),(0,[z1,z2,z3,z4,z907,z15])],[(0,[z1,z1173,z3,z4,z8,z6]),(0,[z545,z2,z3,z4,z8,z484]),(0,[z132,z1,z3,z4,z8,z13])],[(0,[z1,z2,z1174,z4,z8,z6]),(0,[z1,z2,z3,z355,z8,z399]),(0,[z1,z2,z3,z8,z6,z1175])],[(0,[z1,z2,z3,z4,z8,z1176]),(0,[z1,z3,z4,z8,z217,z15]),(0,[z1,z2,z3,z4,z1177,z6]),(0,[z585,z2,z3,z4,z40,z6]),(0,[z1,z2,z3,z4,z1178,z6]),(0,[z1,z1179,z3,z4,z8,z6]),(0,[z35,z1,z2,z4,z45,z6])],[(0,[z1,z2,z3,z4,z8,z1180]),(0,[z633,z1,z3,z4,z8,z15]),(0,[z1,z2,z3,z4,z8,z1181]),(0,[z1,z3,z257,z4,z8,z15]),(0,[z1,z2,z3,z227,z8,z15]),(0,[z1,z2,z3,z4,z916,z15]),(0,[z1,z202,z3,z4,z37,z6])],[(0,[z1,z2,z3,z4,z1182,z6]),(0,[z1,z2,z3,z1183,z8,z6]),(0,[z1,z2,z3,z4,z8,z1184]),(0,[z1,z2,z3,z1185,z8,z6]),(0,[z1,z2,z3,z1186,z8,z6]),(0,[z1,z2,z3,z4,z8,z97])],[(0,[z1,z2,z3,z4,z8,z6]),(0,[z1,z1187,z3,z4,z8,z6]),(0,[z1,z3,z4,z8,z245,z112]),(0,[z73,z1,z74,z4,z8,z15]),(0,[z1,z2,z3,z4,z1188,z6]),(0,[z1,z2,z3,z1189,z8,z6]),(0,[z1,z2,z3,z4,z271,z13]),(0,[z1,z2,z3,z4,z1190,z8]),(0,[z1,z2,z3,z10,z8,z11])],[(0,[z1,z2,z3,z147,z8,z262]),(0,[z1,z2,z3,z4,z8,z1191]),(0,[z1,z2,z3,z370,z8,z399]),(0,[z1,z2,z1192,z4,z8,z6]),(0,[z1,z3,z4,z65,z738,z6]),(0,[z1,z3,z4,z8,z15,z75])]],
   [[(0,[z1,z2,z1193,z4,z8,z6]),(0,[z1,z2,z3,z4,z936,z6]),(0,[z140,z68,z2,z61,z8,z6]),(0,[z1,z2,z3,z4,z8,z1194]),(0,[z1,z2,z96,z100,z4,z8]),(0,[z1,z2,z3,z4,z1195,z8]),(0,[z1,z2,z3,z355,z419,z6]),(0,[z1,z2,z3,z678,z19,z6]),(0,[z1,z2,z3,z4,z281,z22]),(0,[z1,z2,z3,z8,z720,z105])],[(0,[z1,z2,z3,z4,z1196,z6]),(0,[z27,z1,z2,z582,z4,z8]),(0,[z32,z1,z3,z81,z8,z314]),(0,[z1,z2,z3,z4,z302,z13])],[(0,[z1,z3,z82,z148,z8,z15]),(0,[z174,z2,z3,z4,z8,z72])],[(0,[z140,z193,z61,z4,z8,z6]),(0,[z1,z3,z4,z8,z1197,z6]),(0,[z1,z2,z3,z179,z261,z6]),(0,[z1,z2,z216,z4,z210,z6])],[(0,[z1,z64,z3,z4,z8,z15]),(0,[z1,z3,z4,z8,z1198,z6]),(0,[z1,z655,z49,z4,z8,z6]),(1,[z2,z3,z735,z8,z6]),(0,[z1,z2,z3,z4,z8,z1199]),(0,[z1,z12,z459,z4,z8,z6]),(0,[z1,z300,z3,z4,z110,z6]),(0,[z1,z2,z3,z4,z6,z362])],[(0,[z1,z2,z3,z4,z8,z1200]),(0,[z1,z2,z3,z1201,z8,z6]),(0,[z1,z198,z3,z60,z4,z6]),(0,[z1,z2,z3,z370,z419,z6]),(0,[z1,z117,z3,z82,z221,z6])],[(0,[z1,z3,z4,z278,z8,z15]),(0,[z1,z2,z96,z3,z4,z31]),(1,[z1,z3,z370,z8,z15]),(0,[z1,z3,z4,z8,z280,z15])],[(0,[z178,z1,z3,z4,z8,z217]),(0,[z78,z3,z4,z8,z386,z6]),(0,[z1,z2,z3,z4,z8,z143]),(0,[z1,z2,z810,z3,z8,z15]),(0,[z1,z2,z3,z4,z8,z1202])]]]

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
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 523).take 521) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1044).take 206) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1250)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [523, 521, 206] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 89).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 89).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 184).take 72).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [89, 95, 72] = true :=
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

end PEqualNP.Outside.L_meta_39831

theorem PEqualNP.Outside.L_meta_39831 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373480 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373480 * 2 ^ 32 + 4006144192) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39831.solve