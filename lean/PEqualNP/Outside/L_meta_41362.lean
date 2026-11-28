import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41362

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
  Nat.testBit (4276809450 * 2 ^ 32 + 4240482432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x008a8842ac7185ba#64 ++ 0x0008a8842ac7185b#64 ++ 0xc19f98c7ec718ffd#64 ++ 0xec19f98c7ec718ff#64 : BitVec 256),
   (0x42262b199036bc5c#64 ++ 0x042262b199036bc5#64 ++ 0xc6666f39907ffc7b#64 ++ 0xfc6666f39907ffc7#64 : BitVec 256),
   (0x1858702e15815ae0#64 ++ 0x11858702e15815ae#64 ++ 0x7878703e1f81fff7#64 ++ 0xf7878703e1f81fff#64 : BitVec 256),
   (0xad807dc01ada0f00#64 ++ 0x0ad807dc01ada0f0#64 ++ 0xbf807fc01ffe0f8f#64 ++ 0x7bf807fc01ffe0f8#64 : BitVec 256),
   (0x37ff80000f6de000#64 ++ 0x237ff80000f6de00#64 ++ 0x3fff80001ffff00f#64 ++ 0xa3fff80001ffff00#64 : BitVec 256),
   (0x3f7556b540000000#64 ++ 0x43f7556b54000000#64 ++ 0xffffffffe000000f#64 ++ 0xdffffffffe000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [0, 2]⟩, ⟨.or, [6, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [0, 10]⟩, ⟨.or, [10, 8]⟩, ⟨.and, [11, 5]⟩, ⟨.and, [12, 7]⟩, ⟨.or, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x000000000c718ff0 0x2000000000c718ff

def z1 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc19f98c7ec718ffd 0xec19f98c7ec718ff

def z2 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7878703e1f81fff7 0xf7878703e1f81fff

def z3 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z4 : W := mkw 0x400229089036bc5c 0x0400229089036bc5 0x00000000107ffc70 0x200000000107ffc7

def z5 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc6666f39907ffc7b 0xfc6666f39907ffc7

def z6 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z7 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x019f80000c718ffd 0xa019f80000c718ff

def z8 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffe000000f 0xdffffffffe000000

def z9 : W := mkw 0x0080004008400100 0x0008000400840010 0x018010c00c000384 0x0018010c00c00038

def z10 : W := mkw 0x422eab1bb437bcfe 0x0422eab1bb437bcf 0xc67fef3ff07ffc7b 0xfc67fef3ff07ffc7

def z11 : W := mkw 0x1850702e11805ae0 0x11850702e11805ae 0x7860703e13807ff2 0x57860703e13807ff

def z12 : W := mkw 0x022600000024a000 0x0022600000024a00 0x06660000107ff00b 0xa06660000107ff00

def z13 : W := mkw 0x88007dc010920f00 0x088007dc010920f0 0x80007fc000000f80 0x580007fc000000f8

def z14 : W := mkw 0x0224021100000000 0x0022402110000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z15 : W := mkw 0xad807dee1ada1fe0 0x1ad807dee1ada1fe 0xff807ffe1ffe0fff 0x7ff807ffe1ffe0ff

def z16 : W := mkw 0x3775021100000000 0x0377502110000000 0xffffef398000000f 0xdffffef398000000

def z17 : W := mkw 0x37ff8840af7de51a 0x237ff8840af7de51 0xbfff88c1fffff00f 0xabfff88c1fffff00

def z18 : W := mkw 0x7ffffffffc77bdfe 0x47ffffffffc77bdf 0xfffffffffc7fffff 0xffffffffffc7ffff

def z19 : W := mkw 0x2500048000000000 0x0250004800000000 0x87800fc000000008 0x087800fc00000000

def z20 : W := mkw 0x3fffd0260fede2a0 0x33fffd0260fede2a 0x3fff90061ffff38f 0xa3fff90061ffff38

def z21 : W := mkw 0x37750000030c6000 0x237750000030c600 0x3e600000138e7002 0x03e600000138e700

def z22 : W := mkw 0x37ff80000c618000 0x037ff80000c61800 0x3fff80000c71800f 0xa3fff80000c71800

def z23 : W := mkw 0x0800702e10801ae0 0x10800702e10801ae 0x4000703e00000ff0 0x54000703e00000ff

def z24 : W := mkw 0x27a780000a6ca000 0x227a780000a6ca00 0x07878000007e0008 0x007878000007e000

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0x4060603800000003 0xd406060380000000

def z26 : W := mkw 0x258180000a480000 0x2258180000a48000 0x0181800000000000 0x0018180000000000

def z27 : W := mkw 0x880054c000800300 0x0880054c00080030 0x000010c000000380 0x0000010c00000038

def z28 : W := mkw 0x42aeab5bbc77bdfe 0x042aeab5bbc77bdf 0xc7fffffffc7fffff 0xfc7fffffffc7ffff

def z29 : W := mkw 0x1058002e050150e0 0x11058002e050150e 0x4078103e0c01fff5 0xe4078103e0c01fff

def z30 : W := mkw 0x3775069140000000 0x4377506914000000 0xbfff8fc1e000000f 0x8bfff8fc1e000000

def z31 : W := mkw 0xefa67fd19afeaf1c 0x0efa67fd19afeaf1 0xbf867fc19ffe0f8f 0x7bf867fc19ffe0f8

def z32 : W := mkw 0x0000000000000000 0x0000000000000000 0x019f80000000000d 0x8019f80000000000

def z33 : W := mkw 0xbffffdee1fffffe0 0x3bffffdee1fffffe 0xfffffffe1fffffff 0xffffffffe1ffffff

def z34 : W := mkw 0x27a786914a6ca000 0x627a786914a6ca00 0x87878fc1e07e0008 0x087878fc1e07e000

def z35 : W := mkw 0x35d980000f494000 0x235d980000f49400 0x399980000f800004 0x0399980000f80000

def z36 : W := mkw 0x40002b1990121c5c 0x040002b1990121c5 0xc0006f3980000c70 0x5c0006f3980000c7

def z37 : W := mkw 0x3d5874ae15815ae0 0x13d5874ae15815ae 0xfff87ffe1f81ffff 0xffff87ffe1f81fff

def z38 : W := mkw 0x3f7576bd51805a40 0x53f7576bd51805a4 0xfffffffff380700f 0xdfffffffff380700

def z39 : W := mkw 0x0002290090328c18 0x00002290090328c1 0xc6066f01907f8c7b 0xfc6066f01907f8c7

def z40 : W := mkw 0x0800500000800200 0x0080050000080020 0x380010000f800384 0x0380010000f80038

def z41 : W := mkw 0x42260b118036a41c 0x042260b118036a41 0x86060f01807e0008 0x086060f01807e000

def z42 : W := mkw 0xa5800dc00a5a0500 0x0a5800dc00a5a050 0x87800fc0007e0008 0x087800fc0007e000

def z43 : W := mkw 0x80000dc000120500 0x080000dc00012050 0x80000fc000000000 0x080000fc00000000

def z44 : W := mkw 0x88007dc010920f00 0x088007dc010920f0 0xb8007fc01f800f87 0x7b8007fc01f800f8

def z45 : W := mkw 0x42260b198036b45c 0x042260b198036b45 0xc6660f39807ff078 0x8c6660f39807ff07

def z46 : W := mkw 0x0080084008500500 0x0008008400850050 0xc19f98c7ec700f8d 0xec19f98c7ec700f8

def z47 : W := mkw 0x1858702615814aa0 0x11858702615814aa 0x381870061f800f87 0x7381870061f800f8

def z48 : W := mkw 0x00088002240100a2 0x000088002240100a 0x0019800660000000 0x0001980066000000

def z49 : W := mkw 0x527e023f8525f0fc 0x1527e023f8525f0f 0x407e003f8001f070 0x8407e003f8001f07

def z50 : W := mkw 0x5a7e7b3f95b7fefc 0x15a7e7b3f95b7fef 0xfe7e7f3f9fffffff 0xffe7e7f3f9ffffff

def z51 : W := mkw 0x3f7fd6b54525e000 0x63f7fd6b54525e00 0xffffffffe001f00f 0xdffffffffe001f00

def z52 : W := mkw 0x5a767b3d91b6fe5c 0x15a767b3d91b6fe5 0xfe666f3993fffc7b 0xffe666f3993fffc7

def z53 : W := mkw 0x42a68b51a876a51e 0x042a68b51a876a51 0x87878fc1e07e0008 0x087878fc1e07e000

def z54 : W := mkw 0x37ff8002af6de0ba 0x237ff8002af6de0b 0x7fff8007fffff07f 0xa7fff8007fffff07

def z55 : W := mkw 0x0000200810001840 0x0000020081000184 0x000000001001fc70 0x2000000001001fc7

def z56 : W := mkw 0x0000000000000000 0x0000000000000000 0x06000000107e000b 0x206000000107e000

def z57 : W := mkw 0x008a88008c718418 0x0008a88008c71841 0xc19f88018c718c7d 0xec19f88018c718c7

def z58 : W := mkw 0x258000000a480000 0x0258000000a48000 0x3f8000001ffe000f 0x23f8000001ffe000

def z59 : W := mkw 0xbffffdc01fffef00 0x2bffffdc01fffef0 0xbfffffc01fffff8f 0xfbfffffc01fffff8

def z60 : W := mkw 0x2d00548000000000 0x02d0054800000000 0xbf807fc00000000f 0x5bf807fc00000000

def z61 : W := mkw 0xbff57ff55ada0f00 0x4bff57ff55ada0f0 0xfffffffffffe0f8f 0xffffffffffffe0f8

def z62 : W := mkw 0x77ffa3191f6ff844 0x277ffa3191f6ff84 0x3fffe7381ffff00f 0xb3fffe7381ffff00

def z63 : W := mkw 0x7f757fbdd0121c5c 0x47f757fbdd0121c5 0xffffffffe0000c7f 0xdffffffffe0000c7

def z64 : W := mkw 0x00080002040100a0 0x000080002040100a 0x401810060c018ff5 0xe401810060c018ff

def z65 : W := mkw 0x18daf86ebdf1dffa 0x118daf86ebdf1dff 0xf9fff8fffff1ffff 0xff9fff8fffff1fff

def z66 : W := mkw 0xa5800dc00a5a0500 0x0a5800dc00a5a050 0xbf800fc01ffe000f 0x2bf800fc01ffe000

def z67 : W := mkw 0x422622199024b85c 0x0422622199024b85 0x406660399001fc73 0xf406660399001fc7

def z68 : W := mkw 0x37ff8842ac7185ba 0x037ff8842ac7185b 0xffff98c7ec718fff 0xeffff98c7ec718ff

def z69 : W := mkw 0x3f7756b54024a000 0x43f7756b54024a00 0xfffffffff07ff00f 0xffffffffff07ff00

def z70 : W := mkw 0xbf757ff550920f00 0x4bf757ff550920f0 0xffffffffe0000f8f 0xdffffffffe0000f8

def z71 : W := mkw 0x008aa84abdf1dffa 0x1008aa84abdf1dff 0x000000001ff1fff0 0x2000000001ff1fff

def z72 : W := mkw 0x00000000030c6000 0x200000000030c600 0x00000000138e7000 0x000000000138e700

def z73 : W := mkw 0x3fffd6b54f6de000 0x63fffd6b54f6de00 0xfffffffffffff00f 0xffffffffffffff00

def z74 : W := mkw 0x0000000000000000 0x0000000000000000 0xc19f98c7e000000d 0xcc19f98c7e000000

def z75 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x386060381f81fff2 0x3386060381f81fff

def z76 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x3e60673800000002 0x13e6067380000000

def z77 : W := mkw 0x1058000005014000 0x0105800000501400 0x387800001f81f007 0xa387800001f81f00

def z78 : W := mkw 0x088af86ebcf19ffa 0x1088af86ebcf19ff 0xc19ff8ffec718ffd 0xfc19ff8ffec718ff

def z79 : W := mkw 0x0008200a15815ae0 0x10008200a15815ae 0x000000001f81fff0 0x2000000001f81fff

def z80 : W := mkw 0x1850502400000000 0x0185050240000000 0x7878703e00000007 0xd7878703e0000000

def z81 : W := mkw 0x88007dee10921fe0 0x188007dee10921fe 0xc0007ffe00000ff0 0x5c0007ffe00000ff

def z82 : W := mkw 0x3d5054a400000000 0x03d5054a40000000 0xfff87ffe0000000f 0xdfff87ffe0000000

def z83 : W := mkw 0x1a7e702e15a5fae0 0x11a7e702e15a5fae 0x7e7e703e1fffffff 0xf7e7e703e1ffffff

def z84 : W := mkw 0x000a8002a42180ba 0x0000a8002a42180b 0x401f8007e0018070 0x8401f8007e001807

def z85 : W := mkw 0x0080084008500500 0x0008008400850050 0x818018c00c700f8d 0x6818018c00c700f8

def z86 : W := mkw 0x4a267b3f90b6befc 0x14a267b3f90b6bef 0xc6667f3f907ffffb 0xfc6667f3f907ffff

def z87 : W := mkw 0x3f7d76bf55815ae0 0x53f7d76bf55815ae 0xffffffffff81ffff 0xfffffffffff81fff

def z88 : W := mkw 0x527e2b3f9537fcfc 0x1527e2b3f9537fcf 0xc67e6f3f907ffc7b 0xfc67e6f3f907ffc7

def z89 : W := mkw 0xafa47fd11ada0f00 0x0afa47fd11ada0f0 0xffe67ff99ffe0f8f 0xfffe67ff99ffe0f8

def z90 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0x398010c01ffe0f84 0x2398010c01ffe0f8

def z91 : W := mkw 0x808029401ada0f00 0x0808029401ada0f0 0x000000001ffe0f80 0x2000000001ffe0f8

def z92 : W := mkw 0x008a80000f6de000 0x2008a80000f6de00 0x000000001ffff000 0x2000000001ffff00

def z93 : W := mkw 0x3775000000000000 0x0377500000000000 0x3fff80000000000f 0x83fff80000000000

def z94 : W := mkw 0x1a7c723f15815ae0 0x11a7c723f15815ae 0xfe7e7f3f9f81ffff 0xffe7e7f3f9f81fff

def z95 : W := mkw 0x0800500000000000 0x0080050000000000 0x3800700000000007 0x5380070000000000

def z96 : W := mkw 0x2725069140000000 0x4272506914000000 0x87878fc1e0000008 0x087878fc1e000000

def z97 : W := mkw 0x48007fbdd0121c5c 0x448007fbdd0121c5 0xc0007fffe0000c70 0x5c0007fffe0000c7

def z98 : W := mkw 0x400229089036bc5c 0x0400229089036bc5 0x86006f00107ffc7b 0x786006f00107ffc7

def z99 : W := mkw 0x127f80000525e000 0x2127f80000525e00 0x067f8000107ff00b 0xa067f8000107ff00

def z100 : W := mkw 0x00000042200001a2 0x000000042200001a 0x000010c660000380 0x0000010c66000038

def z101 : W := mkw 0x080076bf50801ae0 0x5080076bf50801ae 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z102 : W := mkw 0x18585026058142a0 0x118585026058142a 0x381810060f800384 0x0381810060f80038

def z103 : W := mkw 0xfffe7fff9ffffffc 0x1fffe7fff9ffffff 0xfffe7fff9fffffff 0xffffe7fff9ffffff

def z104 : W := mkw 0x0000090000120400 0x0000009000012040 0x86000f00007e0008 0x086000f00007e000

def z105 : W := mkw 0x18d8f06e3dc15be2 0x118d8f06e3dc15be 0x79f9f0fe7f81fff7 0xf79f9f0fe7f81fff

def z106 : W := mkw 0xefa47fd91ade3f44 0x0efa47fd91ade3f4 0xbfe07ff81ffe7f8f 0x7bfe07ff81ffe7f8

def z107 : W := mkw 0xad007580128a0a00 0x0ad007580128a0a0 0x3e006700138e0002 0x13e006700138e000

def z108 : W := mkw 0x7f7577bd50063844 0x47f7577bd5006384 0x3e606738100e7002 0x13e606738100e700

def z109 : W := mkw 0x0082084088708518 0x0008208408870851 0xc18618c18c718ffd 0xec18618c18c718ff

def z110 : W := mkw 0x008880422c4101a2 0x0008880422c4101a 0x019990c66c000384 0x0019990c66c00038

def z111 : W := mkw 0x4224231910063844 0x0422423191006384 0x06606738100e7002 0x106606738100e700

def z112 : W := mkw 0x1850702c11805a40 0x11850702c11805a4 0x386070381f807f87 0x7386070381f807f8

def z113 : W := mkw 0x35db80000f6de000 0x235db80000f6de00 0x399980001ffff004 0x2399980001ffff00

def z114 : W := mkw 0x408aa94abc77bdfe 0x0408aa94abc77bdf 0x000000001c7ffff0 0x2000000001c7ffff

def z115 : W := mkw 0xad8afdc2befb8fba 0x0ad8afdc2befb8fb 0xff9fffc7ffff8fff 0xfff9fffc7ffff8ff

def z116 : W := mkw 0x10da8842ad71c5ba 0x010da8842ad71c5b 0xf9ff98c7fff1ffff 0xef9ff98c7fff1fff

def z117 : W := mkw 0x1858792e15935ee0 0x11858792e15935ee 0xfe787f3e1fffffff 0xffe787f3e1ffffff

def z118 : W := mkw 0x400229089036bc5c 0x0400229089036bc5 0x40606038107ffc73 0xf40606038107ffc7

def z119 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0xf9fff8ffff81ffff 0xff9fff8ffff81fff

def z120 : W := mkw 0x7f7577bd50063844 0x47f7577bd5006384 0xfffffffff00e700f 0xdfffffffff00e700

def z121 : W := mkw 0x3f75502400000000 0x03f7550240000000 0x7ffff03e0000000f 0xd7ffff03e0000000

def z122 : W := mkw 0x0224221910001840 0x0022422191000184 0xc6666f399001fc7b 0xfc6666f399001fc7

def z123 : W := mkw 0x77ffa9089f7ffc5c 0x277ffa9089f7ffc5 0x3fff80001ffffc7f 0xa3fff80001ffffc7

def z124 : W := mkw 0x35d980000f494000 0x235d980000f49400 0x3f9980001ffe000f 0x23f9980001ffe000

def z125 : W := mkw 0xad007580128a0a00 0x0ad007580128a0a0 0xbf807fc0138e000f 0x5bf807fc0138e000

def z126 : W := mkw 0x400a290a95b7fefc 0x1400a290a95b7fef 0x000000001ffffff0 0x2000000001ffffff

def z127 : W := mkw 0x0800790010920e00 0x00800790010920e0 0xbe007f001ffe0f8f 0x7be007f001ffe0f8

def z128 : W := mkw 0x0224021100000000 0x0022402110000000 0xc6666f398000000b 0xdc6666f398000000

def z129 : W := mkw 0x7f777fbdd036bc5c 0x47f777fbdd036bc5 0xfffffffff07ffc7f 0xffffffffff07ffc7

def z130 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0x3e0067001ffe0f82 0x33e0067001ffe0f8

def z131 : W := mkw 0x37ff802e0f6df0e0 0x337ff802e0f6df0e 0x7fff803e1ffff07f 0xa7fff803e1ffff07

def z132 : W := mkw 0xbdd9fdc01fdb4f00 0x2bdd9fdc01fdb4f0 0xbf99ffc01ffe0f8f 0x7bf99ffc01ffe0f8

def z133 : W := mkw 0x1858700015814a00 0x01858700015814a0 0x387870001f81ff87 0xf387870001f81ff8

def z134 : W := mkw 0x27a78840aa7ca51a 0x227a78840aa7ca51 0x878788c1e07e0008 0x0878788c1e07e000

def z135 : W := mkw 0x37fd80000f4d6000 0x237fd80000f4d600 0x3ff980001f8e7006 0x03ff980001f8e700

def z136 : W := mkw 0x0800700010800a00 0x00800700010800a0 0x380070001f800f87 0x7380070001f800f8

def z137 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x07ff8000007ff008 0x807ff8000007ff00

def z138 : W := mkw 0x1850702410800a00 0x01850702410800a0 0x7878703e1f800f87 0xf7878703e1f800f8

def z139 : W := mkw 0x37f780000a6ca000 0x237f780000a6ca00 0x3fff8000007e000f 0x83fff8000007e000

def z140 : W := mkw 0x0225021140000000 0x4022502114000000 0x00078001e0000000 0x000078001e000000

def z141 : W := mkw 0x0224000000000000 0x0022400000000000 0x066600000000000b 0x8066600000000000

def z142 : W := mkw 0x1275023540000000 0x4127502354000000 0x407f803fe0000000 0x8407f803fe000000

def z143 : W := mkw 0x3f7576b550800a00 0x43f7576b550800a0 0xffffffffff800f8f 0xfffffffffff800f8

def z144 : W := mkw 0x10da80000f6de000 0x210da80000f6de00 0x387800001ffff007 0xa387800001ffff00

def z145 : W := mkw 0x008a80000c618000 0x0008a80000c61800 0x019f80000c71800d 0xa019f80000c71800

def z146 : W := mkw 0x1050000000000000 0x0105000000000000 0x3878000000000007 0x8387800000000000

def z147 : W := mkw 0x00000842a01005ba 0x000000842a01005b 0xc19f98c7e0000ffd 0xcc19f98c7e0000ff

def z148 : W := mkw 0x0224021100000000 0x0022402110000000 0x4066003980000000 0x8406600398000000

def z149 : W := mkw 0xef267f9992bebe5c 0x0ef267f9992bebe5 0xfe666f3993fffc7b 0xffe666f3993fffc7

def z150 : W := mkw 0x42260b118036a41c 0x042260b118036a41 0x86660f01907ff00b 0xa86660f01907ff00

def z151 : W := mkw 0xbff57dc01ada0f00 0x0bff57dc01ada0f0 0xbfffffc01ffe0f8f 0xfbfffffc01ffe0f8

def z152 : W := mkw 0xad807ff55ada0f00 0x4ad807ff55ada0f0 0xff807ffffffe0f8f 0x7ff807ffffffe0f8

def z153 : W := mkw 0x888afdc2bcf38fba 0x0888afdc2bcf38fb 0xc19fffc7ec718ffd 0xfc19fffc7ec718ff

def z154 : W := mkw 0x3f757fb550120c00 0x43f757fb550120c0 0xfffffffff07e0c0f 0xffffffffff07e0c0

def z155 : W := mkw 0x0008000005014000 0x0000800000501400 0x000000001f81f000 0x2000000001f81f00

def z156 : W := mkw 0xad805dc00ada0700 0x0ad805dc00ada070 0xbf801fc00ffe038c 0x0bf801fc00ffe038

def z157 : W := mkw 0x0000290010120c00 0x00000290010120c0 0x86006f00107e0c0b 0x786006f00107e0c0

def z158 : W := mkw 0x00828840a870851a 0x000828840a870851 0x818788c1e0700008 0x0818788c1e070000

def z159 : W := mkw 0x1850702c11805a40 0x11850702c11805a4 0x3860603813807002 0x1386060381380700

def z160 : W := mkw 0x0080000008400000 0x0008000000840000 0x018000000c70000d 0x2018000000c70000

def z161 : W := mkw 0xbdd87dee1fdb5fe0 0x1bdd87dee1fdb5fe 0xfff87ffe1fffffff 0xffff87ffe1ffffff

def z162 : W := mkw 0xbff55ff54a5a0500 0x4bff55ff54a5a050 0xffffffffe07e000f 0xdffffffffe07e000

def z163 : W := mkw 0x1850702e10801ae0 0x11850702e10801ae 0x7878703e00000ff7 0xd7878703e00000ff

def z164 : W := mkw 0x3ffff02e1fedfae0 0x33ffff02e1fedfae 0x7ffff03e1fffffff 0xf7ffff03e1ffffff

def z165 : W := mkw 0x00080842a41105ba 0x000080842a41105b 0xc01818c7ec018ff5 0xec01818c7ec018ff

def z166 : W := mkw 0x808009400a5a0500 0x0808009400a5a050 0x00000000007e0000 0x000000000007e000

def z167 : W := mkw 0x888079401ada0f00 0x0888079401ada0f0 0x380070001ffe0f87 0x7380070001ffe0f8

def z168 : W := mkw 0x1850502400000000 0x0185050240000000 0x3818100600000004 0x0381810060000000

def z169 : W := mkw 0x10580026050140a0 0x110580026050140a 0x0018000600000000 0x0001800060000000

def z170 : W := mkw 0x008a8842af7de5ba 0x2008a8842af7de5b 0xc19f98c7fffffffd 0xec19f98c7fffffff

def z171 : W := mkw 0xbffffff55fffef00 0x6bffffff55fffef0 0xffffffffffffff8f 0xfffffffffffffff8

def z172 : W := mkw 0x0000000000000000 0x0000000000000000 0x86006f000000000b 0x586006f000000000

def z173 : W := mkw 0x0000000000000000 0x0000000000000000 0xc006080180000009 0xcc00608018000000

def z174 : W := mkw 0x37ff80422f6de1a2 0x237ff80422f6de1a 0x3fff90c67ffff38f 0xa3fff90c67ffff38

def z175 : W := mkw 0x008a8840ac71851a 0x0008a8840ac71851 0x819f88c1ec71800d 0xa819f88c1ec71800

def z176 : W := mkw 0x2d0056b540000000 0x42d0056b54000000 0xff807fffe000000f 0x5ff807fffe000000

def z177 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfe607fffe0000002 0x5fe607fffe000000

def z178 : W := mkw 0x37750000030c6000 0x237750000030c600 0x3fff8000138e700f 0x83fff8000138e700

def z179 : W := mkw 0x18585026058142a0 0x118585026058142a 0x781810060f818ff5 0xe781810060f818ff

def z180 : W := mkw 0x008a88400c718500 0x0008a88400c71850 0x819f98c00c718f8d 0xe819f98c00c718f8

def z181 : W := mkw 0x1275023540000000 0x4127502354000000 0xc67fef3fe000000b 0xdc67fef3fe000000

def z182 : W := mkw 0x27250000020c2000 0x227250000020c200 0x06000000000e0000 0x006000000000e000

def z183 : W := mkw 0x42aeab199c77bc5c 0x042aeab199c77bc5 0xc7ffef399c7ffc7f 0xfc7ffef399c7ffc7

def z184 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3e6000001ffff002 0x23e6000001ffff00

def z185 : W := mkw 0xad8afdc01fffef00 0x2ad8afdc01fffef0 0xbf807fc01fffff8f 0x7bf807fc01fffff8

def z186 : W := mkw 0xed807fd99ada1f5c 0x0ed807fd99ada1f5 0xff807ff99ffe0fff 0x7ff807ff99ffe0ff

def z187 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0x399990c660000004 0x0399990c66000000

def z188 : W := mkw 0x0800502400000000 0x0080050240000000 0x4000703e00000000 0x54000703e0000000

def z189 : W := mkw 0x3fffd6b54f6de000 0x63fffd6b54f6de00 0x3fffe7381ffff00f 0xb3fffe7381ffff00

def z190 : W := mkw 0x77ffab199f7ffc5c 0x277ffab199f7ffc5 0xffffef399ffffc7f 0xfffffef399ffffc7

def z191 : W := mkw 0x000a8002a42180ba 0x0000a8002a42180b 0xc19f98c7e001807d 0xcc19f98c7e001807

def z192 : W := mkw 0x00080002040100a0 0x000080002040100a 0x001810060c000384 0x0001810060c00038

def z193 : W := mkw 0x18daf02e1de1dae0 0x118daf02e1de1dae 0x79fff03e1ff1ffff 0xf79fff03e1ff1fff

def z194 : W := mkw 0xbff57ff55ada0f00 0x4bff57ff55ada0f0 0xbfe07ff81ffe0f8f 0x7bfe07ff81ffe0f8

def z195 : W := mkw 0xefaeffdbbeffbffe 0x0efaeffdbbeffbff 0xffffffffffffffff 0xffffffffffffffff

def z196 : W := mkw 0x37f500000b4c6000 0x237f500000b4c600 0x3fe000001ffe700f 0x23fe000001ffe700

def z197 : W := mkw 0x008880422c4101a2 0x0008880422c4101a 0x419990c66c018ff5 0xe419990c66c018ff

def z198 : W := mkw 0x37ff82354f6de000 0x637ff82354f6de00 0x7fff803ffffff00f 0xa7fff803ffffff00

def z199 : W := mkw 0x422602198024b05c 0x0422602198024b05 0x406600398001f070 0x8406600398001f07

def z200 : W := mkw 0xad8054c00ac80300 0x0ad8054c00ac8030 0x398010c00f800384 0x0398010c00f80038

def z201 : W := mkw 0x00000842a01005ba 0x000000842a01005b 0xc00018c7e0000ff0 0x4c00018c7e0000ff

def z202 : W := mkw 0x27a78ed1e870851a 0x427a78ed1e870851 0x87878fc1e0700008 0x087878fc1e070000

def z203 : W := mkw 0x1058000005014000 0x0105800000501400 0x381800000f800004 0x0381800000f80000

def z204 : W := mkw 0x1058002e050150e0 0x11058002e050150e 0x7878003e1f81f077 0xa7878003e1f81f07

def z205 : W := mkw 0x0000023540000000 0x4000002354000000 0x4000003fe0000000 0x04000003fe000000

def z206 : W := mkw 0x3dd9f02e1fc95ae0 0x33dd9f02e1fc95ae 0x79f9f03e1f81fff7 0xf79f9f03e1f81fff

def z207 : W := mkw 0x008a8842af7de5ba 0x2008a8842af7de5b 0x000000001ffffff0 0x2000000001ffffff

def z208 : W := mkw 0x080056b540000000 0x4080056b54000000 0xc19fffffe000000d 0xdc19fffffe000000

def z209 : W := mkw 0xad00548002880200 0x0ad0054800288020 0x3800000003800000 0x0380000000380000

def z210 : W := mkw 0xffffffd99fffff5c 0x2ffffffd99fffff5 0xfffffff99fffffff 0xffffffff99ffffff

def z211 : W := mkw 0x37ff80020f6de0a0 0x237ff80020f6de0a 0x7fff90061fffffff 0xe7fff90061ffffff

def z212 : W := mkw 0xa58004c00a480100 0x0a58004c00a48010 0x018000c000000000 0x0018000c00000000

def z213 : W := mkw 0xad8074c01ac80b00 0x0ad8074c01ac80b0 0x398070c01f800f87 0x7398070c01f800f8

def z214 : W := mkw 0x8088294a1fdb5fe0 0x18088294a1fdb5fe 0x000000001ffffff0 0x2000000001ffffff

def z215 : W := mkw 0xafa67dc01afeaf00 0x0afa67dc01afeaf0 0xbfe67fc01fffff8f 0xfbfe67fc01fffff8

def z216 : W := mkw 0x5277023dc024b05c 0x45277023dc024b05 0x407f803fe001f070 0x8407f803fe001f07

def z217 : W := mkw 0x1050002c01005040 0x11050002c0100504 0x0060003800007000 0x0006000380000700

def z218 : W := mkw 0x37770000032ce000 0x237770000032ce00 0x3e66000013fff00b 0xa3e66000013fff00

def z219 : W := mkw 0xbdd17de45ada0f00 0x4bdd17de45ada0f0 0xbf99ffc67ffe0f8f 0x7bf99ffc67ffe0f8

def z220 : W := mkw 0xe7a60fd18a7ea51c 0x0e7a60fd18a7ea51 0x87860fc1807e0008 0x087860fc1807e000

def z221 : W := mkw 0x8800758010820a00 0x08800758010820a0 0x0000670000000000 0x1000067000000000

def z222 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xff9fffc7fffe0f8f 0xfff9fffc7fffe0f8

def z223 : W := mkw 0x1275023540000000 0x4127502354000000 0xc1ff98ffe000000d 0xcc1ff98ffe000000

def z224 : W := mkw 0x000a80000525e000 0x2000a80000525e00 0x000000000001f000 0x0000000000001f00

def z225 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7818703e0f800ff4 0x57818703e0f800ff

def z226 : W := mkw 0x408aab5bbc739dfe 0x0408aab5bbc739df 0xc19fffffec718ffd 0xfc19fffffec718ff

def z227 : W := mkw 0x0002080080308418 0x0000208008030841 0x8006080180700008 0x0800608018070000

def z228 : W := mkw 0x18dad866ac7185ba 0x018dad866ac7185b 0xf9fff8ffec718fff 0xff9fff8ffec718ff

def z229 : W := mkw 0xad007dc010920f00 0x0ad007dc010920f0 0xbf807fc000000f8f 0x5bf807fc000000f8

def z230 : W := mkw 0x0080084008500500 0x0008008400850050 0x000000000c700f80 0x2000000000c700f8

def z231 : W := mkw 0x0000000800001040 0x0000000080000104 0x406000380001f070 0x8406000380001f07

def z232 : W := mkw 0x35d800000f494000 0x035d800000f49400 0x3ff800001ffff00f 0xa3ff800001ffff00

def z233 : W := mkw 0x1058002e050150e0 0x11058002e050150e 0x4078003e0001f070 0x84078003e0001f07

def z234 : W := mkw 0x3f7556b5430c6000 0x63f7556b5430c600 0x3e606738138e7002 0x13e606738138e700

def z235 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc0666f398001fc70 0xdc0666f398001fc7

def z236 : W := mkw 0x1051002440000000 0x4105100244000000 0x0019800660000000 0x0001980066000000

def z237 : W := mkw 0x527e2b199537fc5c 0x0527e2b199537fc5 0xfe7e6f399ffffc7f 0xffe7e6f399ffffc7

def z238 : W := mkw 0x37ff82110f6de000 0x237ff82110f6de00 0xffffef399ffff00f 0xfffffef399ffff00

def z239 : W := mkw 0x42242b1990163c5c 0x042242b1990163c5 0xc6606f39900e7c72 0x5c6606f39900e7c7

def z240 : W := mkw 0xbd5875ae178b5ae0 0x1bd5875ae178b5ae 0x7e78773e1f8ffff7 0xf7e78773e1f8ffff

def z241 : W := mkw 0x1058000005014000 0x0105800000501400 0x007800000001f000 0x8007800000001f00

def z242 : W := mkw 0x808000400ac80300 0x0808000400ac8030 0x000000000f800380 0x0000000000f80038

def z243 : W := mkw 0x00000002a00000ba 0x000000002a00000b 0x40000007e0000070 0x040000007e000007

def z244 : W := mkw 0x1050002400000000 0x0105000240000000 0x4078003e00000000 0x84078003e0000000

def z245 : W := mkw 0x00000002000000a0 0x000000002000000a 0x4000100600000ff0 0x44000100600000ff

def z246 : W := mkw 0x35db80000f69c000 0x235db80000f69c00 0x399f80000ff1800d 0xa399f80000ff1800

def z247 : W := mkw 0x080056b540000000 0x4080056b54000000 0xc0007fffe0000000 0x5c0007fffe000000

def z248 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x019990c66c718ff4 0x2019990c66c718ff

def z249 : W := mkw 0x3fffd4800f6de000 0x23fffd4800f6de00 0xbfffffc01ffff00f 0xfbfffffc01ffff00

def z250 : W := mkw 0xef247799128e3a44 0x0ef247799128e3a4 0x3e606738138e7002 0x13e606738138e700

def z251 : W := mkw 0x422e2b1b9437bcfc 0x0422e2b1b9437bcf 0xc67e7f3f9c7fffff 0xfc67e7f3f9c7ffff

def z252 : W := mkw 0x27af8842ae7da5ba 0x227af8842ae7da5b 0xc79f98c7ec7f8ffd 0xec79f98c7ec7f8ff

def z253 : W := mkw 0x37ffa9001f7fec00 0x237ffa9001f7fec0 0xbfffef001ffffc0f 0xfbfffef001ffffc0

def z254 : W := mkw 0x0082800008608000 0x0008280000860800 0x0187800000700008 0x0018780000070000

def z255 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x818788c1ec718ff8 0x2818788c1ec718ff

def z256 : W := mkw 0x2725069140000000 0x4272506914000000 0x0600070000000000 0x0060007000000000

def z257 : W := mkw 0x37ff8842af7de5ba 0x237ff8842af7de5b 0x3fff80001fffffff 0xa3fff80001ffffff

def z258 : W := mkw 0xad887dca1fdb5fe0 0x1ad887dca1fdb5fe 0xbf807fc01fffffff 0x7bf807fc01ffffff

def z259 : W := mkw 0x37ffa0081f6df840 0x237ffa0081f6df84 0x7fffe0381ffffc7f 0xf7fffe0381ffffc7

def z260 : W := mkw 0x42a6ab59b876bd5e 0x042a6ab59b876bd5 0xc7e7eff9f07ffc7b 0xfc7e7eff9f07ffc7

def z261 : W := mkw 0x3fffd0240f6de000 0x23fffd0240f6de00 0x7ffff03e1ffff00f 0xf7ffff03e1ffff00

def z262 : W := mkw 0x022600000024a000 0x0022600000024a00 0x006600000001f000 0x8006600000001f00

def z263 : W := mkw 0x1858502e050150e0 0x11858502e050150e 0x7878703e0001f077 0xd7878703e0001f07

def z264 : W := mkw 0x377700000024a000 0x0377700000024a00 0x3fff8000107ff00f 0xa3fff8000107ff00

def z265 : W := mkw 0xbdd07dec1bda5f40 0x1bdd07dec1bda5f4 0xbfe07ff81ffe7f8f 0x7bfe07ff81ffe7f8

def z266 : W := mkw 0x0000000000000000 0x0000000000000000 0x019990c660000004 0x0019990c66000000

def z267 : W := mkw 0x0002080080308418 0x0000208008030841 0xc006080180718c79 0xec006080180718c7

def z268 : W := mkw 0xad805cc00ad80700 0x0ad805cc00ad8070 0xb98018c00ff00f8d 0x6b98018c00ff00f8

def z269 : W := mkw 0x400200088024b05c 0x0400200088024b05 0x000000000001f070 0x0000000000001f07

def z270 : W := mkw 0x0000200810001840 0x0000020081000184 0x406060381001fc73 0xf406060381001fc7

def z271 : W := mkw 0x422602198024b05c 0x0422602198024b05 0xc6666f398001f07b 0xdc6666f398001f07

def z272 : W := mkw 0x88807dc018d20f00 0x088807dc018d20f0 0x81807fc00c700f8d 0x781807fc00c700f8

def z273 : W := mkw 0x258a80000e698000 0x0258a80000e69800 0x3f9f80001fff800f 0xa3f9f80001fff800

def z274 : W := mkw 0x3ddbdce6ec7185ba 0x43ddbdce6ec7185b 0xf99f98c7ec718ffd 0xef99f98c7ec718ff

def z275 : W := mkw 0x2725069140000000 0x4272506914000000 0xc79f9fc7e000000d 0xcc79f9fc7e000000

def z276 : W := mkw 0xbffffff7fefb8fba 0x4bffffff7fefb8fb 0xffffffffffff8fff 0xfffffffffffff8ff

def z277 : W := mkw 0xefa67fd99afebf5c 0x0efa67fd99afebf5 0xffe67ff99fffffff 0xfffe67ff99ffffff

def z278 : W := mkw 0x40022b1990329c5c 0x040022b1990329c5 0xc0066f3980718c79 0xfc0066f3980718c7

def z279 : W := mkw 0xad827dc09afa8f18 0x0ad827dc09afa8f1 0xff867fc19fff8fff 0xfff867fc19fff8ff

def z280 : W := mkw 0x00080002040100a0 0x000080002040100a 0xc19f98c7ec018ffd 0xec19f98c7ec018ff

def z281 : W := mkw 0x37ffa00a1fedfae0 0x337ffa00a1fedfae 0x3fff80001fffffff 0xa3fff80001ffffff

def z282 : W := mkw 0xfff77ffddafebf5c 0x4fff77ffddafebf5 0xffffffffffffffff 0xffffffffffffffff

def z283 : W := mkw 0x0808700a15815ae0 0x10808700a15815ae 0x380070001f81fff7 0x7380070001f81fff

def z284 : W := mkw 0x3fffdef7ec7185ba 0x43fffdef7ec7185b 0xffffffffec718fff 0xfffffffffec718ff

def z285 : W := mkw 0xad8afdc2befb8fba 0x0ad8afdc2befb8fb 0xbf807fc01fff8fff 0x7bf807fc01fff8ff

def z286 : W := mkw 0x127d023f450150e0 0x5127d023f450150e 0x407f803fe001f070 0x8407f803fe001f07

def z287 : W := mkw 0x0800702e10801ae0 0x10800702e10801ae 0x7800703e1f800ff7 0x77800703e1f800ff

def z288 : W := mkw 0x40002b1990121c5c 0x040002b1990121c5 0xc6006f39907e0c7b 0x7c6006f39907e0c7

def z289 : W := mkw 0x7ffffb3f9ffffefc 0x37ffffb3f9ffffef 0xffffff3f9fffffff 0xfffffff3f9ffffff

def z290 : W := mkw 0x3ffdd6f76c4101a2 0x43ffdd6f76c4101a 0xffffffffec00038f 0xdffffffffec00038

def z291 : W := mkw 0x3f7576bf50801ae0 0x53f7576bf50801ae 0xffffffffe0000fff 0xdffffffffe0000ff

def z292 : W := mkw 0xed827dc89afebf5c 0x0ed827dc89afebf5 0xbf807fc01fffffff 0x7bf807fc01ffffff

def z293 : W := mkw 0x37ff8842af7de5ba 0x237ff8842af7de5b 0xffff98c7ffffffff 0xeffff98c7fffffff

def z294 : W := mkw 0x2d00748010800a00 0x02d00748010800a0 0xbf807fc01f800f8f 0x7bf807fc01f800f8

def z295 : W := mkw 0x0000200a10801ae0 0x10000200a10801ae 0x0000000000000ff0 0x00000000000000ff

def z296 : W := mkw 0x10da886ead71d5fa 0x110da886ead71d5f 0xc1ff98ffec71fffd 0xec1ff98ffec71fff

def z297 : W := mkw 0xad82fdc0bafa8f1a 0x0ad82fdc0bafa8f1 0xbf87ffc1fffe0f8f 0x7bf87ffc1fffe0f8

def z298 : W := mkw 0x0808700214810aa0 0x00808700214810aa 0x781870061f818ff7 0xf781870061f818ff

def z299 : W := mkw 0x27af8ed3ec7185ba 0x427af8ed3ec7185b 0xc79f9fc7ec718ffd 0xec79f9fc7ec718ff

def z300 : W := mkw 0xca267fd990b6bf5c 0x0ca267fd990b6bf5 0xc6667ff9907ffffb 0xfc6667ff9907ffff

def z301 : W := mkw 0x42262b5bb036bdfe 0x042262b5bb036bdf 0xc6667ffff07ffffb 0xfc6667ffff07ffff

def z302 : W := mkw 0x3775023540000000 0x4377502354000000 0x7fff803fe000000f 0x87fff803fe000000

def z303 : W := mkw 0x377f8000072de000 0x2377f8000072de00 0x3e7f8000138ff002 0x83e7f8000138ff00

def z304 : W := mkw 0x88807dc01ada0f00 0x088807dc01ada0f0 0x80007fc01ffe0f80 0x780007fc01ffe0f8

def z305 : W := mkw 0xbdd87dc01fdb4f00 0x0bdd87dc01fdb4f0 0xbff87fc01fffff8f 0xfbff87fc01fffff8

def z306 : W := mkw 0x1275000001046000 0x2127500000104600 0x0060000000007000 0x0006000000000700

def z307 : W := mkw 0x0800700010800a00 0x00800700010800a0 0x0000700000000f80 0x50000700000000f8

def z308 : W := mkw 0x0000290810121c40 0x00000290810121c4 0xc6606f38107ffc7b 0xfc6606f38107ffc7

def z309 : W := mkw 0x0000021100000000 0x0000002110000000 0xc0006f3980000000 0x5c0006f398000000

def z310 : W := mkw 0x0800702e10801ae0 0x10800702e10801ae 0x4060703e1001fff3 0xf4060703e1001fff

def z311 : W := mkw 0xbf7577b5528a0a00 0x4bf7577b5528a0a0 0x3e606738138e0002 0x13e606738138e000

def z312 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbfe7eff9e000000a 0x1bfe7eff9e000000

def z313 : W := mkw 0xad887dc21edb0fa0 0x0ad887dc21edb0fa 0xff987fc61fff8fff 0xfff987fc61fff8ff

def z314 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x06606738107ffc72 0x306606738107ffc7

def z315 : W := mkw 0xb7ffa9401fffef00 0x2b7ffa9401fffef0 0x3fff80001fffff8f 0xa3fff80001fffff8

def z316 : W := mkw 0x1858786eb5915ffa 0x11858786eb5915ff 0xf87878ffff81fff7 0xff87878ffff81fff

def z317 : W := mkw 0x377d000005014000 0x0377d00000501400 0x3fff80001f81f00f 0xa3fff80001f81f00

def z318 : W := mkw 0x105a802ea521d0fa 0x1105a802ea521d0f 0x407f803fe001f070 0x8407f803fe001f07

def z319 : W := mkw 0x0000200810001840 0x0000020081000184 0x0060603810007002 0x1006060381000700

def z320 : W := mkw 0x1850502401804200 0x1185050240180420 0x3800000003800000 0x0380000000380000

def z321 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfe666f398000000b 0xdfe666f398000000

def z322 : W := mkw 0x27af80000f6de000 0x227af80000f6de00 0x078780001ffff008 0x2078780001ffff00

def z323 : W := mkw 0x3f7576bd51805a40 0x53f7576bd51805a4 0x3e60673813807002 0x13e6067381380700

def z324 : W := mkw 0xad807dc81ada1f40 0x0ad807dc81ada1f4 0xffe07ff81fffffff 0xfffe07ff81ffffff

def z325 : W := mkw 0xbdd854e60fc943a0 0x1bdd854e60fc943a 0x399810c60f800384 0x0399810c60f80038

def z326 : W := mkw 0x1058200a15815ae0 0x11058200a15815ae 0x387800001f81fff7 0xa387800001f81fff

def z327 : W := mkw 0x3ffff86ebffdfffa 0x33ffff86ebffdfff 0xfffff8ffffffffff 0xffffff8fffffffff

def z328 : W := mkw 0x42260b118036a41c 0x042260b118036a41 0xc6060f01807f8c79 0xec6060f01807f8c7

def z329 : W := mkw 0x0080294018520d00 0x00080294018520d0 0x87807fc01c7e0f8f 0x787807fc01c7e0f8

def z330 : W := mkw 0x27a780000a6ca000 0x227a780000a6ca00 0x3f8780001ffe000f 0x23f8780001ffe000

def z331 : W := mkw 0x4000290890121c5c 0x04000290890121c5 0x0000000000000c70 0x00000000000000c7

def z332 : W := mkw 0x0002080080308418 0x0000208008030841 0xc19f98c7e0718c7d 0xec19f98c7e0718c7

def z333 : W := mkw 0x000a8002a42180ba 0x0000a8002a42180b 0x0000000000018070 0x0000000000001807

def z334 : W := mkw 0xbdd07de41ada0f00 0x0bdd07de41ada0f0 0xfff87ffe1ffe0f8f 0xffff87ffe1ffe0f8

def z335 : W := mkw 0x77752319130e7844 0x277752319130e784 0x3e606738138e7002 0x13e606738138e700

def z336 : W := mkw 0x3f755ef7e01005ba 0x43f755ef7e01005b 0xffffffffe0000fff 0xdffffffffe0000ff

def z337 : W := mkw 0x98587dee15935fe0 0x198587dee15935fe 0xf8787ffe1f81fff7 0xff8787ffe1f81fff

def z338 : W := mkw 0xad88fdc23edb0fa2 0x0ad88fdc23edb0fa 0xbf99ffc67ffe0f8f 0x7bf99ffc67ffe0f8

def z339 : W := mkw 0xbf7577b5528a0a00 0x4bf7577b5528a0a0 0xfffffffff38e000f 0xdfffffffff38e000

def z340 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc00018c7ec718ff0 0x6c00018c7ec718ff

def z341 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x401f8007ec718ff0 0xa401f8007ec718ff

def z342 : W := mkw 0x0800700810801a40 0x00800700810801a4 0x786070381f81fff7 0xf786070381f81fff

def z343 : W := mkw 0xbddafdeebffbdffa 0x1bddafdeebffbdff 0xffffffffffffffff 0xffffffffffffffff

def z344 : W := mkw 0x00828840a870851a 0x000828840a870851 0xc19f98c7e070000d 0xcc19f98c7e070000

def z345 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x381810061f81fff4 0x2381810061f81fff

def z346 : W := mkw 0x0224000000042000 0x0022400000004200 0x06600000100e7002 0x006600000100e700

def z347 : W := mkw 0x0a2456b540000000 0x40a2456b54000000 0xc6667fffe000000b 0xdc6667fffe000000

def z348 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbfe07ff80000000f 0x5bfe07ff80000000

def z349 : W := mkw 0x58587b3f95935efc 0x158587b3f95935ef 0xf8787f3f9f81fff7 0xff8787f3f9f81fff

def z350 : W := mkw 0x2725069140000000 0x4272506914000000 0xc7e7eff9e000000b 0xdc7e7eff9e000000

def z351 : W := mkw 0x0808702e15815ae0 0x10808702e15815ae 0x4000703e1f81fff0 0x74000703e1f81fff

def z352 : W := mkw 0x008a80000f6de000 0x2008a80000f6de00 0x019f80001ffff00d 0xa019f80001ffff00

def z353 : W := mkw 0x3d5954a6458142a0 0x53d5954a6458142a 0x399990c66f800384 0x0399990c66f80038

def z354 : W := mkw 0x000a8802a43184ba 0x0000a8802a43184b 0xc01f8807e0718c79 0xec01f8807e0718c7

def z355 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00018c7e0000000 0x4c00018c7e000000

def z356 : W := mkw 0x3d5156b540000000 0x43d5156b54000000 0xf999ffffe0000004 0x5f999ffffe000000

def z357 : W := mkw 0x5a767b3d9036bc5c 0x05a767b3d9036bc5 0xfe7e7f3f907ffc7f 0xffe7e7f3f907ffc7

def z358 : W := mkw 0x00080002058142a0 0x100080002058142a 0x000000000f800380 0x0000000000f80038

def z359 : W := mkw 0x022620081024b840 0x0022620081024b84 0x46666038107ffc7b 0xf46666038107ffc7

def z360 : W := mkw 0x00080002040100a0 0x000080002040100a 0x4018000600018070 0x8401800060001807

def z361 : W := mkw 0x42ae8b53ac77a5be 0x042ae8b53ac77a5b 0xc79f9fc7ec7f8ffd 0xec79f9fc7ec7f8ff

def z362 : W := mkw 0x3ffdd6b54f494000 0x63ffdd6b54f49400 0xffffffffef80000f 0xdffffffffef80000

def z363 : W := mkw 0x2f24569100000000 0x02f2456910000000 0xffe67ff98000000f 0xdffe67ff98000000

def z364 : W := mkw 0xa5828dc0aa7a851a 0x0a5828dc0aa7a851 0x87878fc1e07e0008 0x087878fc1e07e000

def z365 : W := mkw 0x127e00000525e000 0x0127e00000525e00 0x3e7e00001ffff00f 0xa3e7e00001ffff00

def z366 : W := mkw 0x1a75523540000000 0x41a7552354000000 0x787ff03fe0000007 0xd787ff03fe000000

def z367 : W := mkw 0x008a80422c6181a2 0x0008a80422c6181a 0x019f90c66c71838d 0xa019f90c66c71838

def z368 : W := mkw 0x008a8042ac6181ba 0x0008a8042ac6181b 0x419f90c7ec0183f4 0x8419f90c7ec0183f

def z369 : W := mkw 0x3f7576bd50001840 0x43f7576bd5000184 0xfffffffff001fc7f 0xffffffffff001fc7

def z370 : W := mkw 0x3ff556b54a480000 0x43ff556b54a48000 0xfffffffffffe000f 0xffffffffffffe000

def z371 : W := mkw 0x0002280890309c58 0x00002280890309c5 0xc06668399071fc7b 0xfc06668399071fc7

def z372 : W := mkw 0x0000200811805a40 0x10000200811805a4 0x0000000013807000 0x0000000001380700

def z373 : W := mkw 0x18585026040100a0 0x018585026040100a 0x7878703e0c018ff7 0xf7878703e0c018ff

def z374 : W := mkw 0x3f75548000000000 0x03f7554800000000 0xbfffffc00000000f 0xdbfffffc00000000

def z375 : W := mkw 0x080054a440000000 0x4080054a44000000 0x000010c660000000 0x0000010c66000000

def z376 : W := mkw 0x00020842a03085ba 0x000020842a03085b 0xc00618c7e0718ff9 0xec00618c7e0718ff

def z377 : W := mkw 0x10da80000d61c000 0x010da80000d61c00 0x39ff80001ff1f00f 0xa39ff80001ff1f00

def z378 : W := mkw 0x185a782e95b1def8 0x1185a782e95b1def 0xf87e783f9ff1ffff 0xff87e783f9ff1fff

def z379 : W := mkw 0x88007dc2b0920fba 0x088007dc2b0920fb 0xc0007fc7e0000ff0 0x5c0007fc7e0000ff

def z380 : W := mkw 0x5a74733d11867a44 0x15a74733d11867a4 0x3e606738138e7002 0x13e606738138e700

def z381 : W := mkw 0x008880000f494000 0x2008880000f49400 0x000000000f800000 0x0000000000f80000

def z382 : W := mkw 0x00888842ac5105ba 0x000888842ac5105b 0xc19998c7ec000ff4 0x4c19998c7ec000ff

def z383 : W := mkw 0x12ff8842ad75e5ba 0x212ff8842ad75e5b 0xc1ff98c7ec71fffd 0xec1ff98c7ec71fff

def z384 : W := mkw 0x008888422c5105a2 0x0008888422c5105a 0x819998c66c700f8d 0x6819998c66c700f8

def z385 : W := mkw 0x1058202e15815ae0 0x11058202e15815ae 0x4078003e1f81fff0 0xa4078003e1f81fff

def z386 : W := mkw 0x008aa942bc738dba 0x0008aa942bc738db 0xc79fffc7fc7f8fff 0xfc79fffc7fc7f8ff

def z387 : W := mkw 0x00828842a87085ba 0x000828842a87085b 0xc18798c7e0700ff8 0x4c18798c7e0700ff

def z388 : W := mkw 0x422e821ba425b0fe 0x0422e821ba425b0f 0x407f803fe001f070 0x8407f803fe001f07

def z389 : W := mkw 0x42260a198034b45c 0x042260a198034b45 0xc06608398071fc79 0xec06608398071fc7

def z390 : W := mkw 0x127f80000525e000 0x2127f80000525e00 0x007f80000001f000 0x8007f80000001f00

def z391 : W := mkw 0x6f267f999036bc5c 0x06f267f999036bc5 0xffe67ff9907ffc7f 0xfffe67ff9907ffc7

def z392 : W := mkw 0x02242b1110120c00 0x002242b1110120c0 0xc6666f39907e0c0b 0xfc6666f39907e0c0

def z393 : W := mkw 0x258a80000f6de000 0x2258a80000f6de00 0x3f8000001ffff00f 0x23f8000001ffff00

def z394 : W := mkw 0x27a600000a6ca000 0x027a600000a6ca00 0x3fe600001ffff00f 0xa3fe600001ffff00

def z395 : W := mkw 0x008aa84abdf1dffa 0x1008aa84abdf1dff 0xc19f98c7fff1fffd 0xec19f98c7fff1fff

def z396 : W := mkw 0xbfffd4c00fede300 0x2bfffd4c00fede30 0x3fff90c01ffff38f 0xa3fff90c01ffff38

def z397 : W := mkw 0x127f8002a525e0ba 0x2127f8002a525e0b 0x407f8007e001f070 0x8407f8007e001f07

def z398 : W := mkw 0x1a7ff02e15a5fae0 0x31a7ff02e15a5fae 0x787ff03e1f81fff7 0xf787ff03e1f81fff

def z399 : W := mkw 0x98d8796e1fdb5fe0 0x198d8796e1fdb5fe 0x7878703e1ffffff7 0xf7878703e1ffffff

def z400 : W := mkw 0x88007ff550920f00 0x488007ff550920f0 0xc0007fffe0000f80 0x5c0007fffe0000f8

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000000018c71 0xe4000000000018c7

def z402 : W := mkw 0x258029001a5a0c00 0x0258029001a5a0c0 0xbf806f001ffe0c0f 0x7bf806f001ffe0c0

def z403 : W := mkw 0x3d5974ae55815ae0 0x53d5974ae55815ae 0x79f9f0fe7f81fff7 0xf79f9f0fe7f81fff

def z404 : W := mkw 0x0080084008500500 0x0008008400850050 0x818008c000700008 0x0818008c00070000

def z405 : W := mkw 0x127f80000525e000 0x2127f80000525e00 0x387f80001f81f007 0xa387f80001f81f00

def z406 : W := mkw 0x3f7fd6b7e42180ba 0x43f7fd6b7e42180b 0xffffffffe001807f 0xdffffffffe001807

def z407 : W := mkw 0x4a267b1990b6be5c 0x04a267b1990b6be5 0xfe667f399fffffff 0xffe667f399ffffff

def z408 : W := mkw 0x400002198000105c 0x0400002198000105 0x4000003980000070 0x0400000398000007

def z409 : W := mkw 0x0800700010800a00 0x00800700010800a0 0x3800600013800002 0x1380060001380000

def z410 : W := mkw 0x42a62b599876bd5c 0x042a62b599876bd5 0xc7e67ff99c7fffff 0xfc7e67ff99c7ffff

def z411 : W := mkw 0x02ae8842ac75a5ba 0x002ae8842ac75a5b 0xc7ff98c7fc7fffff 0xec7ff98c7fc7ffff

def z412 : W := mkw 0x42242b1910163c44 0x042242b1910163c4 0x86606f38107e7c0b 0x786606f38107e7c0

def z413 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0x87807fc0007e0f88 0x587807fc0007e0f8

def z414 : W := mkw 0x2725000000000000 0x0272500000000000 0x0787800000000008 0x0078780000000000

def z415 : W := mkw 0x008000000a480000 0x0008000000a48000 0x000000001ffe0000 0x2000000001ffe000

def z416 : W := mkw 0x527fab199537fc5c 0x2527fab199537fc5 0xc67fef39907ffc7b 0xfc67fef39907ffc7

def z417 : W := mkw 0x1a74523500000000 0x01a7452350000000 0xfe7e7f3f8000000f 0xdfe7e7f3f8000000

def z418 : W := mkw 0x408aa94abc77bdfe 0x0408aa94abc77bdf 0xc19f98c7fc7ffffd 0xec19f98c7fc7ffff

def z419 : W := mkw 0xbff57dc01bde6f00 0x2bff57dc01bde6f0 0xbfe07fc01ffe7f8f 0x7bfe07fc01ffe7f8

def z420 : W := mkw 0xc8007fd990921f5c 0x0c8007fd990921f5 0xc0007ff980000ff0 0x5c0007ff980000ff

def z421 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc7fffffff07ffc7f 0xfc7fffffff07ffc7

def z422 : W := mkw 0x37ff86914f6de000 0x637ff86914f6de00 0xbfff8fc1fffff00f 0xabfff8fc1fffff00

def z423 : W := mkw 0xa58a8dc2ae7b85ba 0x0a58a8dc2ae7b85b 0xc79f9fc7ec7f8ffd 0xec79f9fc7ec7f8ff

def z424 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x4078703e0001fff0 0xd4078703e0001fff

def z425 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x39ff80000f81f004 0x839ff80000f81f00

def z426 : W := mkw 0x4000231910021844 0x0400023191002184 0x0000673800000000 0x1000067380000000

def z427 : W := mkw 0x42aeab199f7ffc5c 0x242aeab199f7ffc5 0xc6666f399ffffc7b 0xfc6666f399ffffc7

def z428 : W := mkw 0x0000000000000000 0x0000000000000000 0x000010000c000f85 0x6000010000c000f8

def z429 : W := mkw 0x0008000a050150e0 0x10008000a050150e 0x000000000001f070 0x0000000000001f07

def z430 : W := mkw 0x585a792e95b7fefc 0x1585a792e95b7fef 0x7878703e1ffffff7 0xf7878703e1ffffff

def z431 : W := mkw 0xad007dc0129a0f00 0x0ad007dc0129a0f0 0xbe007fc0138e0f82 0x5be007fc0138e0f8

def z432 : W := mkw 0x808aa9401fffef00 0x2808aa9401fffef0 0x000000001fffff80 0x2000000001fffff8

def z433 : W := mkw 0x0002080080308418 0x0000208008030841 0x0000000000718c70 0x20000000000718c7

def z434 : W := mkw 0x0224021100000000 0x0022402110000000 0x86060f0180000008 0x086060f018000000

def z435 : W := mkw 0x185876bf55815ae0 0x5185876bf55815ae 0xf8787fffff81fff7 0xff8787fffff81fff

def z436 : W := mkw 0x0000290010120c00 0x00000290010120c0 0x00000000107e0c00 0x200000000107e0c0

def z437 : W := mkw 0x5a7e723f95a5fafc 0x15a7e723f95a5faf 0x787e703f9f81fff7 0xf787e703f9f81fff

def z438 : W := mkw 0x000200000024a000 0x0000200000024a00 0x00000000107ff000 0x200000000107ff00

def z439 : W := mkw 0xa58029401ada0f00 0x0a58029401ada0f0 0x3f8000001ffe0f8f 0x23f8000001ffe0f8

def z440 : W := mkw 0x42ae8a5bac75b5fe 0x042ae8a5bac75b5f 0xc1ff98ffec71fffd 0xec1ff98ffec71fff

def z441 : W := mkw 0x0808702e14811ae0 0x10808702e14811ae 0x4018703e0c018ff5 0xf4018703e0c018ff

def z442 : W := mkw 0x000a0802843184b8 0x0000a0802843184b 0xc01e18078c718ffd 0xec01e18078c718ff

def z443 : W := mkw 0x18585026058142a0 0x118585026058142a 0x387810061f81f387 0xa387810061f81f38

def z444 : W := mkw 0x377506b540000000 0x4377506b54000000 0xc7ff8fffe0000008 0x8c7ff8fffe000000

def z445 : W := mkw 0x008808420c5105a0 0x0008808420c5105a 0xc19818c60c718ffd 0xec19818c60c718ff

def z446 : W := mkw 0x0000000000000000 0x0000000000000000 0x818788c1e0000008 0x0818788c1e000000

def z447 : W := mkw 0x00828840a870851a 0x000828840a870851 0x0000000000700000 0x0000000000070000

def z448 : W := mkw 0xad8adcc2aef987ba 0x0ad8adcc2aef987b 0xf99f98c7eff18ffd 0xef99f98c7eff18ff

def z449 : W := mkw 0x77ffab5bbf7ffdfe 0x277ffab5bbf7ffdf 0xffffffffffffffff 0xffffffffffffffff

def z450 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbf9f9fc7e000000c 0x0bf9f9fc7e000000

def z451 : W := mkw 0x67272f99d036bc5c 0x467272f99d036bc5 0xc7e7eff9f07ffc7b 0xfc7e7eff9f07ffc7

def z452 : W := mkw 0x377f80000525e000 0x2377f80000525e00 0x3fff80000001f00f 0x83fff80000001f00

def z453 : W := mkw 0x3fffd6b54c618000 0x43fffd6b54c61800 0xffffffffec71800f 0xfffffffffec71800

def z454 : W := mkw 0x0800548000000000 0x0080054800000000 0x80007fc000000000 0x580007fc00000000

def z455 : W := mkw 0x008aa00a1fedfae0 0x3008aa00a1fedfae 0x000000001ffffff0 0x2000000001ffffff

def z456 : W := mkw 0x008a8002ac6180ba 0x0008a8002ac6180b 0x419f8007ec71807d 0xa419f8007ec71807

def z457 : W := mkw 0x008a80020c6180a0 0x0008a80020c6180a 0x419f90060c718ffd 0xe419f90060c718ff

def z458 : W := mkw 0x3551000000000000 0x0355100000000000 0x3999800000000004 0x0399980000000000

def z459 : W := mkw 0xa7a50fd14a5a0500 0x4a7a50fd14a5a050 0x87878fc1e07e0008 0x087878fc1e07e000

def z460 : W := mkw 0x4224031100062004 0x0422403110006200 0x06000700000e0000 0x006000700000e000

def z461 : W := mkw 0xa5000580020a0000 0x0a5000580020a000 0x06000700000e0000 0x006000700000e000

def z462 : W := mkw 0xad007580128a0a00 0x0ad007580128a0a0 0x3e0077001f8e0f87 0x73e0077001f8e0f8

def z463 : W := mkw 0x2500000002080000 0x0250000000208000 0x3e000000138e0002 0x03e000000138e000

def z464 : W := mkw 0x400229089036bc5c 0x0400229089036bc5 0xc0060801907ffc79 0xec0060801907ffc7

def z465 : W := mkw 0x0000069140000000 0x4000006914000000 0x80000fc1e0000000 0x080000fc1e000000

def z466 : W := mkw 0x4a267fbdd036bc5c 0x44a267fbdd036bc5 0xc6667ffff07ffc7b 0xfc6667ffff07ffc7

def z467 : W := mkw 0x808aa942befb8fba 0x0808aa942befb8fb 0x000000001fff8ff0 0x2000000001fff8ff

def z468 : W := mkw 0x40002b1990121c5c 0x040002b1990121c5 0xc0606f399001fc73 0xfc0606f399001fc7

def z469 : W := mkw 0xb7ff8dc00f7fe500 0x2b7ff8dc00f7fe50 0xbfff8fc01ffff00f 0xabfff8fc01ffff00

def z470 : W := mkw 0x88007dc010920f00 0x088007dc010920f0 0x86007fc0107e0f8b 0x786007fc0107e0f8

def z471 : W := mkw 0x022608008034a418 0x0022608008034a41 0xc6660801907ffc7b 0xec6660801907ffc7

def z472 : W := mkw 0x3775000000000000 0x0377500000000000 0x3e60000000000002 0x03e6000000000000

def z473 : W := mkw 0x022629001036ac00 0x0022629001036ac0 0x86666f00107ffc0b 0xf86666f00107ffc0

def z474 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0xf99f98c7e000000d 0xcf99f98c7e000000

def z475 : W := mkw 0x088af842bcf18fba 0x0088af842bcf18fb 0xf99ff8c7fff18fff 0xff99ff8c7fff18ff

def z476 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0xbf99ffc66000000f 0x5bf99ffc66000000

def z477 : W := mkw 0x1850502400000000 0x0185050240000000 0x3860603800000002 0x1386060380000000

def z478 : W := mkw 0xad805dc00a5a0500 0x0ad805dc00a5a050 0xbf807fc0007e000f 0x5bf807fc0007e000

def z479 : W := mkw 0x808aa942befb8fba 0x0808aa942befb8fb 0xc19f98c7ffff8ffd 0xec19f98c7ffff8ff

def z480 : W := mkw 0xbffffdc2bfffefba 0x2bffffdc2bfffefb 0xffffffc7ffffffff 0xfffffffc7fffffff

def z481 : W := mkw 0x3ffff6bf5fedfae0 0x73ffff6bf5fedfae 0xffffffffffffffff 0xffffffffffffffff

def z482 : W := mkw 0x00028000a020801a 0x000028000a020801 0x00078001e0000000 0x000078001e000000

def z483 : W := mkw 0x3f7d76bf55815ae0 0x53f7d76bf55815ae 0x7e78773e1f81fff7 0xf7e78773e1f81fff

def z484 : W := mkw 0x3f775eb5c0308418 0x43f775eb5c030841 0xffffffffe0718c7f 0xfffffffffe0718c7

def z485 : W := mkw 0x18daf02e1fedfae0 0x318daf02e1fedfae 0x7878703e1ffffff7 0xf7878703e1ffffff

def z486 : W := mkw 0x258008400a580500 0x0258008400a58050 0xbf8018c01ffe0f8f 0x6bf8018c01ffe0f8

def z487 : W := mkw 0x3f7556b5430c6000 0x63f7556b5430c600 0xfffffffff38e700f 0xdfffffffff38e700

def z488 : W := mkw 0x127f802e0525f0e0 0x3127f802e0525f0e 0x407f803e0001f070 0x8407f803e0001f07

def z489 : W := mkw 0x3f7d56b7458142a0 0x53f7d56b7458142a 0xffffffffef80038f 0xdffffffffef80038

def z490 : W := mkw 0x67270f91c036a41c 0x467270f91c036a41 0x87878fc1e07e0008 0x087878fc1e07e000

def z491 : W := mkw 0x27af80000e6da000 0x227af80000e6da00 0x079f80000c7f800d 0xa079f80000c7f800

def z492 : W := mkw 0x0224021100000000 0x0022402110000000 0x0660673800000002 0x1066067380000000

def z493 : W := mkw 0x35d980000f494000 0x235d980000f49400 0x39f980001f81f007 0xa39f980001f81f00

def z494 : W := mkw 0x2f25569140000000 0x42f2556914000000 0xbf87ffc1e000000f 0x5bf87ffc1e000000

def z495 : W := mkw 0x42242b1990121c5c 0x042242b1990121c5 0xc6666f3980000c7b 0xdc6666f3980000c7

def z496 : W := mkw 0x00800842a85005ba 0x000800842a85005b 0xc18018c7ec700ffd 0x6c18018c7ec700ff

def z497 : W := mkw 0x008880422c4101a2 0x0008880422c4101a 0xc19f98c7ec00038d 0xcc19f98c7ec00038

def z498 : W := mkw 0x3775000000000000 0x0377500000000000 0xffff98c7e000000f 0xcffff98c7e000000

def z499 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc19f88c7e0718078 0x8c19f88c7e071807

def z500 : W := mkw 0x0800786eb0901ffa 0x10800786eb0901ff 0xc00078ffe0000ff0 0x5c00078ffe0000ff

def z501 : W := mkw 0x5afefb7fbdf7fffe 0x15afefb7fbdf7fff 0xffffffffffffffff 0xffffffffffffffff

def z502 : W := mkw 0x18d8786e1dd15fe0 0x118d8786e1dd15fe 0xf9f878fe1ff1ffff 0xff9f878fe1ff1fff

def z503 : W := mkw 0x1a7556b540000000 0x41a7556b54000000 0xc07fffffe0000000 0xdc07fffffe000000

def z504 : W := mkw 0x258000000a480000 0x0258000000a48000 0x07800000007e0008 0x007800000007e000

def z505 : W := mkw 0x127f82354525e000 0x6127f82354525e00 0x407f803fe001f000 0x8407f803fe001f00

def z506 : W := mkw 0x18585026058142a0 0x118585026058142a 0x7878703e0f800387 0xd7878703e0f80038

def z507 : W := mkw 0x185af02eb5a1dafa 0x1185af02eb5a1daf 0x787ff03fff81fff7 0xf787ff03fff81fff

def z508 : W := mkw 0x77772b199036bc5c 0x077772b199036bc5 0xffffef39907ffc7f 0xfffffef39907ffc7

def z509 : W := mkw 0xad88d4c22ec903a2 0x0ad88d4c22ec903a 0x399990c66f800384 0x0399990c66f80038

def z510 : W := mkw 0x258a8842ae7985ba 0x0258a8842ae7985b 0xff9f98c7ffff8fff 0xeff9f98c7ffff8ff

def z511 : W := mkw 0xa5800dc00a5a0500 0x0a5800dc00a5a050 0x87801fc00c7e0f8d 0x687801fc00c7e0f8

def z512 : W := mkw 0x3f75702c138c7a40 0x33f75702c138c7a4 0x3e606038138e7002 0x13e606038138e700

def z513 : W := mkw 0xbf757580138e6a00 0x2bf757580138e6a0 0x3e606700138e7002 0x13e606700138e700

def z514 : W := mkw 0x422623199026b85c 0x0422623199026b85 0x46666739900ff072 0x946666739900ff07

def z515 : W := mkw 0xbdd9d4c00fc94300 0x2bdd9d4c00fc9430 0x399990c00f800384 0x0399990c00f80038

def z516 : W := mkw 0x3fffdef7ef7de5ba 0x63fffdef7ef7de5b 0xffffffffffffffff 0xffffffffffffffff

def z517 : W := mkw 0x37ff88008f7de418 0x237ff88008f7de41 0xffff88019ffffc7f 0xeffff88019ffffc7

def z518 : W := mkw 0x185056b540000000 0x4185056b54000000 0xf8787fffe0000007 0xdf8787fffe000000

def z519 : W := mkw 0x67a62b199a7ebc5c 0x067a62b199a7ebc5 0xffe66f399ffffc7f 0xfffe66f399ffffc7

def z520 : W := mkw 0x0000000000000000 0x0000000000000000 0x401f8007e0000000 0x8401f8007e000000

def z521 : W := mkw 0x0008200a140118e0 0x00008200a140118e 0x4078703e1c01fff7 0xf4078703e1c01fff

def z522 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7878603e1381f072 0x97878603e1381f07

def z523 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x819f98c7ec70038c 0x0819f98c7ec70038

def z524 : W := mkw 0x80002100128a0a00 0x080002100128a0a0 0x00000000138e0000 0x000000000138e000

def z525 : W := mkw 0x1059800005014000 0x2105980000501400 0x0019800000000000 0x0001980000000000

def z526 : W := mkw 0x2d007d8010120c00 0x02d007d8010120c0 0xbf807fc0107e0c0f 0x7bf807fc0107e0c0

def z527 : W := mkw 0x00000842a01005ba 0x000000842a01005b 0x0000000000000ff0 0x00000000000000ff

def z528 : W := mkw 0xbd5075ac138a5a40 0x1bd5075ac138a5a4 0x3e606738138e7002 0x13e606738138e700

def z529 : W := mkw 0x4224231910063844 0x0422423191006384 0x46606738100ffc73 0xf46606738100ffc7

def z530 : W := mkw 0x4224021900043044 0x0422402190004304 0x0060003800007000 0x0006000380000700

def z531 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x7e7fe73fe0000002 0x97e7fe73fe000000

def z532 : W := mkw 0x0008000004010000 0x0000800000401000 0x001800000c018005 0xa001800000c01800

def z533 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0xffff98c7fffff00f 0xeffff98c7fffff00

def z534 : W := mkw 0x3ff55ef548500500 0x43ff55ef54850050 0xffffffffec700f8f 0xfffffffffec700f8

def z535 : W := mkw 0xa5802dc01ada0f00 0x0a5802dc01ada0f0 0x87800fc01ffe0f88 0x287800fc01ffe0f8

def z536 : W := mkw 0x2d00548000000000 0x02d0054800000000 0x3e00670000000002 0x13e0067000000000

def z537 : W := mkw 0x022780000024a000 0x2022780000024a00 0x0007800000000000 0x0000780000000000

def z538 : W := mkw 0x0002000080208018 0x0000200008020801 0x4006000180018070 0x8400600018001807

def z539 : W := mkw 0x3dd9d4e66c4101a2 0x43dd9d4e66c4101a 0x399990c66c000384 0x0399990c66c00038

def z540 : W := mkw 0x7f777fbdd036bc5c 0x47f777fbdd036bc5 0xfe666f39907ffc7b 0xffe666f39907ffc7

def z541 : W := mkw 0x0880784018d00f00 0x00880784018d00f0 0xb98078c01ff00f8f 0x7b98078c01ff00f8

def z542 : W := mkw 0x008aa84abc719dfa 0x0008aa84abc719df 0xc1fff8fffc71ffff 0xfc1fff8fffc71fff

def z543 : W := mkw 0x02ae8a53ac7185ba 0x002ae8a53ac7185b 0xc7ffffffec718fff 0xfc7ffffffec718ff

def z544 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x79ff90ffe0000004 0x879ff90ffe000000

def z545 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x86666f39907e700a 0x186666f39907e700

def z546 : W := mkw 0x0000080080100418 0x0000008008010041 0xc000080180000c70 0x4c000080180000c7

def z547 : W := mkw 0x08005ef7e01005ba 0x408005ef7e01005b 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z548 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x3ff9f7fe60000006 0x13ff9f7fe6000000

def z549 : W := mkw 0x3f7d56b545014000 0x43f7d56b54501400 0xffffffffff81f00f 0xfffffffffff81f00

def z550 : W := mkw 0x008a80000c618000 0x0008a80000c61800 0xc19f98c7ec71800d 0xec19f98c7ec71800

def z551 : W := mkw 0x27a780000a6ca000 0x227a780000a6ca00 0x07e78000107ff00b 0xa07e78000107ff00

def z552 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x7e78773e00000007 0xd7e78773e0000000

def z553 : W := mkw 0x2d805cc008500500 0x02d805cc00850050 0xbf807fc00c700f8f 0x7bf807fc00c700f8

def z554 : W := mkw 0xad8075c01aca0b00 0x0ad8075c01aca0b0 0x3f8077c01f8e0386 0x13f8077c01f8e038

def z555 : W := mkw 0x2d00548000000000 0x02d0054800000000 0xff9fffc7e000000f 0xdff9fffc7e000000

def z556 : W := mkw 0x40000b118012041c 0x040000b118012041 0x80000f0180000000 0x080000f018000000

def z557 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3f9f80000ffe000c 0x03f9f80000ffe000

def z558 : W := mkw 0x808029401ada0f00 0x0808029401ada0f0 0x818018c01ffe0f8d 0x6818018c01ffe0f8

def z559 : W := mkw 0x0008200a15815ae0 0x10008200a15815ae 0x401810061f81fff5 0xe401810061f81fff

def z560 : W := mkw 0x48007b3f90921efc 0x148007b3f90921ef 0xc0007f3f80000ff0 0x5c0007f3f80000ff

def z561 : W := mkw 0x1850702c10001840 0x01850702c1000184 0x7878703e1001fc77 0xf7878703e1001fc7

def z562 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x818018c00c718ffd 0x6818018c00c718ff

def z563 : W := mkw 0x1058202e150158e0 0x11058202e150158e 0x4078603e1001fc73 0xf4078603e1001fc7

def z564 : W := mkw 0x1858702c15815a40 0x11858702c15815a4 0x387860381f81f007 0xb387860381f81f00

def z565 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0x3800000000000000 0x0380000000000000

def z566 : W := mkw 0x3ff7d6b54a6ca000 0x63ff7d6b54a6ca00 0xffffffffe07e000f 0xdffffffffe07e000

def z567 : W := mkw 0xbdd154e44ac80300 0x4bdd154e44ac8030 0x399990c66f800384 0x0399990c66f80038

def z568 : W := mkw 0x35d980422f4941a2 0x235d980422f4941a 0x399990c66f800384 0x0399990c66f80038

def z569 : W := mkw 0xad007d80129a0e00 0x0ad007d80129a0e0 0xbe006f0013fe0c0b 0x7be006f0013fe0c0

def z570 : W := mkw 0x08005026008002a0 0x108005026008002a 0x0000100600000380 0x0000010060000038

def z571 : W := mkw 0xa5802dc01a5a0d00 0x0a5802dc01a5a0d0 0x87806fc0107e0c0b 0x787806fc0107e0c0

def z572 : W := mkw 0x422629089036bc5c 0x0422629089036bc5 0x06660000107ffc7b 0xa06660000107ffc7

def z573 : W := mkw 0x52772b3dd036bc5c 0x452772b3dd036bc5 0xc67fef3ff07ffc7b 0xfc67fef3ff07ffc7

def z574 : W := mkw 0x2d8054800a480000 0x02d8054800a48000 0xbf807fc01ffe000f 0x7bf807fc01ffe000

def z575 : W := mkw 0x377d0000070d6000 0x2377d0000070d600 0x3e7800001f8ff007 0xa3e7800001f8ff00

def z576 : W := mkw 0x18daf86ebdf1dffa 0x118daf86ebdf1dff 0x7878703e1ff1fff7 0xf7878703e1ff1fff

def z577 : W := mkw 0x258000000a480000 0x0258000000a48000 0x398000000f800004 0x0398000000f80000

def z578 : W := mkw 0x42262b119036ac1c 0x042262b119036ac1 0x86066f01907e0c0b 0x786066f01907e0c0

def z579 : W := mkw 0x2d8adcc2ac7185ba 0x02d8adcc2ac7185b 0xff9fffc7ec718fff 0xfff9fffc7ec718ff

def z580 : W := mkw 0x00080002040100a0 0x000080002040100a 0x000000000c018ff0 0x2000000000c018ff

def z581 : W := mkw 0x3d5154a440000000 0x43d5154a44000000 0x79f9f0fe60000007 0xd79f9f0fe6000000

def z582 : W := mkw 0x12ff80000d65e000 0x212ff80000d65e00 0x01ff80000c71f00d 0xa01ff80000c71f00

def z583 : W := mkw 0x8000294010920f00 0x08000294010920f0 0x0000000000000f80 0x00000000000000f8

def z584 : W := mkw 0x1058200815015840 0x0105820081501584 0x787860381f81fc77 0xf787860381f81fc7

def z585 : W := mkw 0x0000000000000000 0x0000000000000000 0x818018c00000000d 0x4818018c00000000

def z586 : W := mkw 0x18dad866adf1c7ba 0x118dad866adf1c7b 0xf99f98c7eff18ffd 0xef99f98c7eff18ff

def z587 : W := mkw 0x808029401ada0f00 0x0808029401ada0f0 0x86006f001ffe0f8b 0x786006f001ffe0f8

def z588 : W := mkw 0x37f780000b6ce000 0x237f780000b6ce00 0x3fe7800013fe700a 0x03fe7800013fe700

def z589 : W := mkw 0x3ffffefffdf1dffa 0x53ffffefffdf1dff 0xfffffffffff1ffff 0xffffffffffff1fff

def z590 : W := mkw 0x000a800004218000 0x0000a80000421800 0x001f800000018000 0x8001f80000001800

def z591 : W := mkw 0x3ffff0001fedea00 0x23ffff0001fedea0 0x3ffff0001fffff8f 0xf3ffff0001fffff8

def z592 : W := mkw 0xad8054c00ac80300 0x0ad8054c00ac8030 0x3f8010c01ffe038f 0x23f8010c01ffe038

def z593 : W := mkw 0x008880422c4101a2 0x0008880422c4101a 0x000000000c000380 0x0000000000c00038

def z594 : W := mkw 0x3551000003084000 0x2355100000308400 0x3800000003800000 0x0380000000380000

def z595 : W := mkw 0x5a7c733f15877ae4 0x15a7c733f15877ae 0x7e78773e1f8ffff7 0xf7e78773e1f8ffff

def z596 : W := mkw 0x77ff8b118f7fe41c 0x277ff8b118f7fe41 0xbfff8f019ffff00f 0xabfff8f019ffff00

def z597 : W := mkw 0x080056b540000000 0x4080056b54000000 0x0000673800000000 0x1000067380000000

def z598 : W := mkw 0x4000210810063844 0x0400021081006384 0x00000000100e7000 0x000000000100e700

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z600 : W := mkw 0x2500000000000000 0x0250000000000000 0x3f8000000000000f 0x03f8000000000000

def z601 : W := mkw 0x7fffffbddf7ffc5c 0x67fffffbddf7ffc5 0xfffffffffffffc7f 0xffffffffffffffc7

def z602 : W := mkw 0x4224231910063844 0x0422423191006384 0xc6666f39900e700b 0xdc6666f39900e700

def z603 : W := mkw 0x3fffd4a44f6de000 0x63fffd4a44f6de00 0x3fff90c67ffff00f 0xa3fff90c67ffff00

def z604 : W := mkw 0xad8afdc01efb8f00 0x0ad8afdc01efb8f0 0xbf9fffc01fff8f8f 0xfbf9fffc01fff8f8

def z605 : W := mkw 0x1275023540000000 0x4127502354000000 0x0060003800000000 0x0006000380000000

def z606 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x86060f01907ffc78 0x286060f01907ffc7

def z607 : W := mkw 0x3f7d702e15815ae0 0x13f7d702e15815ae 0x7ffff03e1f81ffff 0xf7ffff03e1f81fff

def z608 : W := mkw 0x10580002050140a0 0x010580002050140a 0x787810061f81fff7 0xe787810061f81fff

def z609 : W := mkw 0x02260a1180308418 0x002260a118030841 0xc6666f3980718c7b 0xfc6666f3980718c7

def z610 : W := mkw 0x008280000a6ca000 0x2008280000a6ca00 0x00000000007e0000 0x000000000007e000

def z611 : W := mkw 0x02ae80000c65a000 0x002ae80000c65a00 0x07ff80001c7ff00f 0xa07ff80001c7ff00

def z612 : W := mkw 0x022600000024a000 0x0022600000024a00 0x06060000007e0008 0x006060000007e000

def z613 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x3878703e1f807386 0x13878703e1f80738

def z614 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x40660039907ffc70 0xa40660039907ffc7

def z615 : W := mkw 0xbff556f54ac80300 0x4bff556f54ac8030 0xffffffffef80038f 0xdffffffffef80038

def z616 : W := mkw 0x00000840a010051a 0x000000840a010051 0x800008c1e0000000 0x0800008c1e000000

def z617 : W := mkw 0xad807dc2bada0fba 0x0ad807dc2bada0fb 0xff807fc7fffe0fff 0x7ff807fc7fffe0ff

def z618 : W := mkw 0x0000084000100500 0x0000008400010050 0x800018c000000f80 0x4800018c000000f8

def z619 : W := mkw 0x3dd9d0260fc942a0 0x33dd9d0260fc942a 0x399990060f800384 0x0399990060f80038

def z620 : W := mkw 0x2f2556b540000000 0x42f2556b54000000 0xc787ffffe0000008 0x5c787ffffe000000

def z621 : W := mkw 0x02ae80000f6de000 0x202ae80000f6de00 0x066600001ffff00b 0xa066600001ffff00

def z622 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x401810060c718ff5 0xe401810060c718ff

def z623 : W := mkw 0x35db8842af79c5ba 0x235db8842af79c5b 0xf99f98c7eff18ffd 0xef99f98c7eff18ff

def z624 : W := mkw 0x0000200010000800 0x0000020001000080 0x0000600010000c03 0x70000600010000c0

def z625 : W := mkw 0x0080804028400102 0x0008080402840010 0x018180c060000000 0x0018180c06000000

def z626 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc00608018c718ff9 0xec00608018c718ff

def z627 : W := mkw 0xc08229489afebf5c 0x0c08229489afebf5 0x000000001ffffff0 0x2000000001ffffff

def z628 : W := mkw 0x3ffff02c1fedfa40 0x33ffff02c1fedfa4 0x3fffe0381ffff00f 0xb3fffe0381ffff00

def z629 : W := mkw 0x0008200a15815ae0 0x10008200a15815ae 0x406060381f81fff3 0xf406060381f81fff

def z630 : W := mkw 0xbdd874ee1fc95be0 0x1bdd874ee1fc95be 0x79f870fe1f81fff7 0xf79f870fe1f81fff

def z631 : W := mkw 0x7f775fb5c036a41c 0x47f775fb5c036a41 0xffffffffe07e000f 0xdffffffffe07e000

def z632 : W := mkw 0x3dd9d4a44f494000 0x63dd9d4a44f49400 0x399990c66f800004 0x0399990c66f80000

def z633 : W := mkw 0xbffff5801fefea00 0x2bffff5801fefea0 0x3fffe7001ffff00f 0xb3fffe7001ffff00

def z634 : W := mkw 0x422602198024b05c 0x0422602198024b05 0x46660039907ff07b 0xa46660039907ff07

def z635 : W := mkw 0x0000000000000000 0x0000000000000000 0x4018100600000005 0xc401810060000000

def z636 : W := mkw 0x422e2b1b95b7fefc 0x1422e2b1b95b7fef 0xc6666f399ffffffb 0xfc6666f399ffffff

def z637 : W := mkw 0x0000290010120c00 0x00000290010120c0 0x80006f0000000c00 0x580006f0000000c0

def z638 : W := mkw 0x008a80000c618000 0x0008a80000c61800 0x000000000c718000 0x2000000000c71800

def z639 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0x3fffe7380000000f 0x93fffe7380000000

def z640 : W := mkw 0x0000000000000000 0x0000000000000000 0x006000001001f003 0xa006000001001f00

def z641 : W := mkw 0x40022b199036bc5c 0x040022b199036bc5 0xc0006f39907ffc70 0x7c0006f39907ffc7

def z642 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf806fc013fe000a 0x1bf806fc013fe000

def z643 : W := mkw 0x3f7d56bf450150e0 0x53f7d56bf450150e 0xffffffffe001f07f 0xdffffffffe001f07

def z644 : W := mkw 0x088adef7ec7185ba 0x4088adef7ec7185b 0xc19fffffec718ffd 0xfc19fffffec718ff

def z645 : W := mkw 0x408aa9089f7ffc5c 0x2408aa9089f7ffc5 0x000000001ffffc70 0x2000000001ffffc7

def z646 : W := mkw 0x7f7756bdc024b05c 0x47f7756bdc024b05 0xffffffffe001f07f 0xdffffffffe001f07

def z647 : W := mkw 0x3f7d702e178d7ae0 0x33f7d702e178d7ae 0x7e78703e1f8ffff7 0xf7e78703e1f8ffff

def z648 : W := mkw 0x37ff88400f7de500 0x237ff88400f7de50 0xbfff98c01fffff8f 0xebfff98c01fffff8

def z649 : W := mkw 0x37f500000a480000 0x037f500000a48000 0x3fff80001ffe000f 0xa3fff80001ffe000

def z650 : W := mkw 0x422623191026b844 0x0422623191026b84 0x06666738107ff00b 0xb06666738107ff00

def z651 : W := mkw 0x3f7554a440000000 0x43f7554a44000000 0x3fff90c66000000f 0x83fff90c66000000

def z652 : W := mkw 0x12ff80000f6de000 0x212ff80000f6de00 0x007f80001ffff000 0xa007f80001ffff00

def z653 : W := mkw 0x12ff8a77ec7185ba 0x412ff8a77ec7185b 0xc1ff98ffec718ffd 0xec1ff98ffec718ff

def z654 : W := mkw 0x2d8070001ac80a00 0x02d8070001ac80a0 0x3f8070001ffe0f8f 0x73f8070001ffe0f8

def z655 : W := mkw 0x0000200810001840 0x0000020081000184 0x4000603800000c70 0x54000603800000c7

def z656 : W := mkw 0x000a8002a42180ba 0x0000a8002a42180b 0x401f9007ec018ff5 0xe401f9007ec018ff

def z657 : W := mkw 0xe7a62fd99a7ebd5c 0x0e7a62fd99a7ebd5 0xc7e66ff9907ffc7b 0xfc7e66ff9907ffc7

def z658 : W := mkw 0x1275000000000000 0x0127500000000000 0x007f800000000000 0x8007f80000000000

def z659 : W := mkw 0x3ff7def5e870851a 0x43ff7def5e870851 0xffffffffe070000f 0xdffffffffe070000

def z660 : W := mkw 0x1850702c11805a40 0x11850702c11805a4 0x786060381381fc73 0xf786060381381fc7

def z661 : W := mkw 0x67a7ab199a7ebc5c 0x267a7ab199a7ebc5 0xc7e7ef39907ffc7b 0xfc7e7ef39907ffc7

def z662 : W := mkw 0x7f7f7fbfd5b7fefc 0x57f7f7fbfd5b7fef 0xffffffffffffffff 0xffffffffffffffff

def z663 : W := mkw 0xafa57fd15ada0f00 0x4afa57fd15ada0f0 0xbf87ffc1fffe0f8f 0x7bf87ffc1fffe0f8

def z664 : W := mkw 0x18d8d0662dc143a2 0x118d8d0662dc143a 0x399990c66f800384 0x0399990c66f80038

def z665 : W := mkw 0x0000000000000000 0x0000000000000000 0x380000001f800007 0x2380000001f80000

def z666 : W := mkw 0xad8054c00ac80300 0x0ad8054c00ac8030 0xbf807fc00f80038f 0x5bf807fc00f80038

def z667 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc6066f39807e0c78 0x5c6066f39807e0c7

def z668 : W := mkw 0x2501048040000000 0x4250104804000000 0x018180c060000000 0x0018180c06000000

def z669 : W := mkw 0x37fd80000f494000 0x237fd80000f49400 0x3fff80000f80000f 0x83fff80000f80000

def z670 : W := mkw 0x0000200010800a00 0x00000200010800a0 0x000000001f800f80 0x2000000001f800f8

def z671 : W := mkw 0x527f82198525f05c 0x2527f82198525f05 0x407f80398001f070 0x8407f80398001f07

def z672 : W := mkw 0x127f8237e42180ba 0x4127f8237e42180b 0x407f803fe0018070 0x8407f803fe001807

def z673 : W := mkw 0x1850702c11805a40 0x11850702c11805a4 0x7878703e13807007 0xd7878703e1380700

def z674 : W := mkw 0x00828840a870851a 0x000828840a870851 0xc18788c1e0718c79 0xec18788c1e0718c7

def z675 : W := mkw 0x422602118024a01c 0x0422602118024a01 0x0006000180000000 0x0000600018000000

def z676 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xb9807fc00f800f84 0x5b9807fc00f800f8

def z677 : W := mkw 0x2d00548000000000 0x02d0054800000000 0x398010c000000004 0x0398010c00000000

def z678 : W := mkw 0x1858502e058152e0 0x11858502e058152e 0x7878103e0f81f3f4 0x87878103e0f81f3f

def z679 : W := mkw 0x77ff82198f6df05c 0x277ff82198f6df05 0x7fff80399ffff07f 0xa7fff80399ffff07

def z680 : W := mkw 0x0000210010020800 0x0000021001002080 0x06006700100e0002 0x106006700100e000

def z681 : W := mkw 0x1858502405014000 0x0185850240501400 0x7878703e1f81f007 0xf7878703e1f81f00

def z682 : W := mkw 0xa7a78dc00a7ea500 0x2a7a78dc00a7ea50 0x87878fc0007e0008 0x087878fc0007e000

def z683 : W := mkw 0xc2a62b599afebf5c 0x0c2a62b599afebf5 0xc6666f399ffffffb 0xfc6666f399ffffff

def z684 : W := mkw 0x0800702c10801a40 0x10800702c10801a4 0x0000603800000000 0x1000060380000000

def z685 : W := mkw 0x0002000000208000 0x0000200000020800 0x0006000000718009 0xa000600000071800

def z686 : W := mkw 0xad8075801aca0a00 0x0ad8075801aca0a0 0x3f8067001ffe000f 0x33f8067001ffe000

def z687 : W := mkw 0x022602110024a000 0x0022602110024a00 0xc6666f39907ff00b 0xfc6666f39907ff00

def z688 : W := mkw 0x008880000c410000 0x0008880000c41000 0x019980000c000004 0x0019980000c00000

def z689 : W := mkw 0x77772b19933efc5c 0x277772b19933efc5 0xfe666f3993fffc7b 0xffe666f3993fffc7

def z690 : W := mkw 0x0000002e000010e0 0x10000002e000010e 0x4000003e00000070 0x04000003e0000007

def z691 : W := mkw 0xbffd7fff5fdb5fe0 0x5bffd7fff5fdb5fe 0xffffffffffffffff 0xffffffffffffffff

def z692 : W := mkw 0x3dd8702e1fc95ae0 0x13dd8702e1fc95ae 0x7ff8703e1fffffff 0xf7ff8703e1ffffff

def z693 : W := mkw 0x40002b5bb0121dfe 0x040002b5bb0121df 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z694 : W := mkw 0x3f7d56b7440100a0 0x43f7d56b7440100a 0xffffffffec018fff 0xfffffffffec018ff

def z695 : W := mkw 0x42aeab5bbc77bdfe 0x042aeab5bbc77bdf 0xc6666f399c7ffffb 0xfc6666f399c7ffff

def z696 : W := mkw 0x0000080000100400 0x0000008000010040 0x8000080000700c09 0x68000080000700c0

def z697 : W := mkw 0xafa7fdc01afeaf00 0x2afa7fdc01afeaf0 0xbf87ffc01ffe0f8f 0x7bf87ffc01ffe0f8

def z698 : W := mkw 0x67a78b118a7ea41c 0x267a78b118a7ea41 0x87878f01807e0008 0x087878f01807e000

def z699 : W := mkw 0x000a8842a43185ba 0x0000a8842a43185b 0xc01f98c7e0018ff0 0xcc01f98c7e0018ff

def z700 : W := mkw 0x1050000001004000 0x0105000000100400 0x3860000013807002 0x0386000001380700

def z701 : W := mkw 0x400209008036a41c 0x0400209008036a41 0x00000000007e0000 0x000000000007e000

def z702 : W := mkw 0x00828840a870851a 0x000828840a870851 0x818798c1ec700f8d 0x6818798c1ec700f8

def z703 : W := mkw 0x1850502400000000 0x0185050240000000 0xf9fff8ffe000000f 0xdf9fff8ffe000000

def z704 : W := mkw 0x1a7d723f55815ae0 0x51a7d723f55815ae 0x787ff03fff81fff7 0xf787ff03fff81fff

def z705 : W := mkw 0x42260b118036a41c 0x042260b118036a41 0xc6666f39807e000b 0xdc6666f39807e000

def z706 : W := mkw 0xbdd87de61fdb4fa0 0x1bdd87de61fdb4fa 0xbf987fc61ffe0f8f 0x7bf987fc61ffe0f8

def z707 : W := mkw 0x4226ab19b036bc5e 0x04226ab19b036bc5 0xc667ef39f07ffc7b 0xfc667ef39f07ffc7

def z708 : W := mkw 0x67a78b51aa7ea51e 0x267a78b51aa7ea51 0x87878fc1e07e0008 0x087878fc1e07e000

def z709 : W := mkw 0x42262b599036bd5c 0x042262b599036bd5 0xc6667ff9907ffffb 0xfc6667ff9907ffff

def z710 : W := mkw 0x400229089036bc5c 0x0400229089036bc5 0xc6606f38107ffc7b 0xfc6606f38107ffc7

def z711 : W := mkw 0xad805dc00ada0700 0x0ad805dc00ada070 0xbf801fc00ffe0f8d 0x6bf801fc00ffe0f8

def z712 : W := mkw 0x48007b1990921e5c 0x048007b1990921e5 0xc0007f3980000ff0 0x5c0007f3980000ff

def z713 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfffffffff07e000f 0xffffffffff07e000

def z714 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3e7800001ffff007 0xa3e7800001ffff00

def z715 : W := mkw 0x3fffdef7ec7185ba 0x43fffdef7ec7185b 0x3e6067380c718ff2 0x33e6067380c718ff

def z716 : W := mkw 0xad807dc81ada1f40 0x0ad807dc81ada1f4 0xbf807fc01fffffff 0x7bf807fc01ffffff

def z717 : W := mkw 0x42260b198036b45c 0x042260b198036b45 0xc6666f39807ff07b 0xdc6666f39807ff07

def z718 : W := mkw 0x008a8842ac75a5ba 0x0008a8842ac75a5b 0xc19f98c7fc7ffffd 0xec19f98c7fc7ffff

def z719 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7878703e0f81fff4 0xd7878703e0f81fff

def z720 : W := mkw 0x37ff82110f6de000 0x237ff82110f6de00 0x7fff80399ffff00f 0xa7fff80399ffff00

def z721 : W := mkw 0x92f52b755ada0f00 0x492f52b755ada0f0 0x407f803ffffe0f80 0xa407f803ffffe0f8

def z722 : W := mkw 0xad817dc05ada0f00 0x4ad817dc05ada0f0 0xbf81ffc07ffe0f8f 0x7bf81ffc07ffe0f8

def z723 : W := mkw 0x9a7ffdc015b7ef00 0x29a7ffdc015b7ef0 0x807fffc00001ff80 0xd807fffc00001ff8

def z724 : W := mkw 0x10da80000f6de000 0x210da80000f6de00 0x386000001ffff002 0x2386000001ffff00

def z725 : W := mkw 0x40002b1990121c5c 0x040002b1990121c5 0xc6606f39907ffc7b 0xfc6606f39907ffc7

def z726 : W := mkw 0x88007dca10921fe0 0x188007dca10921fe 0x80007fc000000ff0 0x580007fc000000ff

def z727 : W := mkw 0x1858700815815a40 0x01858700815815a4 0x787870381f81fff7 0xf787870381f81fff

def z728 : W := mkw 0x37ff86914f6de000 0x637ff86914f6de00 0xffff9fc7fffff00f 0xeffff9fc7fffff00

def z729 : W := mkw 0x35d000000b484000 0x035d000000b48400 0x3fe000001ffe700f 0x23fe000001ffe700

def z730 : W := mkw 0x008880422c4101a2 0x0008880422c4101a 0xc19f98c7ec018ffd 0xec19f98c7ec018ff

def z731 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc7ffef39907ffc7f 0xfc7ffef39907ffc7

def z732 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbe007fc01ffe0f82 0x7be007fc01ffe0f8

def z733 : W := mkw 0x422602198024b05c 0x0422602198024b05 0xc6666f39907ff07b 0xfc6666f39907ff07

def z734 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc19f98c7ec018ff4 0xcc19f98c7ec018ff

def z735 : W := mkw 0x1a74523500000000 0x01a7452350000000 0xffffffffe000000f 0xdffffffffe000000

def z736 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x46666739907ffc72 0xb46666739907ffc7

def z737 : W := mkw 0x35db80000f6de000 0x235db80000f6de00 0x399f80001ffff00d 0xa399f80001ffff00

def z738 : W := mkw 0xa5800dc00a5a0500 0x0a5800dc00a5a050 0xbf801fc01ffe0f8f 0x6bf801fc01ffe0f8

def z739 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc1ff98c7fc71ffff 0xec1ff98c7fc71fff

def z740 : W := mkw 0x77ff82118f6de01c 0x277ff82118f6de01 0x3fff80019ffff00f 0xa3fff80019ffff00

def z741 : W := mkw 0x00080842a41105ba 0x000080842a41105b 0xc19f98c7ec018ffd 0xec19f98c7ec018ff

def z742 : W := mkw 0xc8007fdbb0921ffe 0x0c8007fdbb0921ff 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z743 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbfe07fc01fffff8f 0xfbfe07fc01fffff8

def z744 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3fe780001ffff00a 0x23fe780001ffff00

def z745 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x06666738107ffc7b 0xb06666738107ffc7

def z746 : W := mkw 0x37fd80000f4d6000 0x237fd80000f4d600 0x3ff980001ffe700f 0x23ff980001ffe700

def z747 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x46606738107ffc73 0xf46606738107ffc7

def z748 : W := mkw 0x18d2f86cb9f0df5a 0x118d2f86cb9f0df5 0xb9e7e8f9f3f0700a 0x1b9e7e8f9f3f0700

def z749 : W := mkw 0xad807dc81ada1f40 0x0ad807dc81ada1f4 0xbfe07ff81ffe7f8f 0x7bfe07ff81ffe7f8

def z750 : W := mkw 0x37ff80008f6de018 0x237ff80008f6de01 0x7fff80019ffff07f 0xa7fff80019ffff07

def z751 : W := mkw 0x42aca35b3c4739e6 0x042aca35b3c4739e 0x07f9f7fe7c0e7386 0x107f9f7fe7c0e738

def z752 : W := mkw 0xbf7577bd538a5a40 0x5bf7577bd538a5a4 0x3e606738138e7002 0x13e606738138e700

def z753 : W := mkw 0x127f80000525e000 0x2127f80000525e00 0x3e7f80001ffff00f 0xa3e7f80001ffff00

def z754 : W := mkw 0x3f7556b540800200 0x43f7556b54080020 0xffffffffef80038f 0xdffffffffef80038

def z755 : W := mkw 0x1859f02e15815ae0 0x31859f02e15815ae 0x7879f03e1f81fff7 0xf7879f03e1f81fff

def z756 : W := mkw 0x1850702c11805a40 0x11850702c11805a4 0x786070381f81fff7 0xf786070381f81fff

def z757 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc19f98c7e0718ff8 0xcc19f98c7e0718ff

def z758 : W := mkw 0x37ff82110f6de000 0x237ff82110f6de00 0xbfff8f019ffff00f 0xabfff8f019ffff00

def z759 : W := mkw 0x888079401ada0f00 0x0888079401ada0f0 0xbe007f001ffe0f8f 0x7be007f001ffe0f8

def z760 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x387860381f81fff7 0xb387860381f81fff

def z761 : W := mkw 0xc8007fff90921ffc 0x1c8007fff90921ff 0xc0007fff80000ff0 0x5c0007fff80000ff

def z762 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc67e7f3f907ffc7f 0xfc67e7f3f907ffc7

def z763 : W := mkw 0xad81fdc01ada0f00 0x2ad81fdc01ada0f0 0xbf81ffc01ffe0f8f 0x7bf81ffc01ffe0f8

def z764 : W := mkw 0x0082084088708518 0x0008208408870851 0xc19f98c7ec718ffd 0xec19f98c7ec718ff

def z765 : W := mkw 0xe7a70fd1ca7ea51c 0x4e7a70fd1ca7ea51 0x87878fc1e07e0008 0x087878fc1e07e000

def z766 : W := mkw 0x0808700a15815ae0 0x10808700a15815ae 0x786070381f81fff7 0xf786070381f81fff

def z767 : W := mkw 0x0800792e10921ee0 0x10800792e10921ee 0xc0007f3e00000ff0 0x5c0007f3e00000ff

def z768 : W := mkw 0x18585026050140a0 0x018585026050140a 0x7878703e1f81fff7 0xf7878703e1f81fff

def z769 : W := mkw 0x00828842a87085ba 0x000828842a87085b 0xc19f98c7e0700ffd 0xcc19f98c7e0700ff

def z770 : W := mkw 0xad807dec1ada1f40 0x1ad807dec1ada1f4 0xbf807ff81ffe0f8f 0x7bf807ff81ffe0f8

def z771 : W := mkw 0xad0af582b6ab8aba 0x0ad0af582b6ab8ab 0x7e1fe707f38f8072 0x97e1fe707f38f807

def z772 : W := mkw 0x2fa7f02e1aecbae0 0x32fa7f02e1aecbae 0x4787f03e007e0ff8 0x54787f03e007e0ff

def z773 : W := mkw 0xc8007ffdd0921f5c 0x4c8007ffdd0921f5 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z774 : W := mkw 0x1058002e050150e0 0x11058002e050150e 0x7878103e1f81fff7 0xe7878103e1f81fff

def z775 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x86666f39907ffc7a 0x386666f39907ffc7

def z776 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc7e7eff9f07ffc7b 0xfc7e7eff9f07ffc7

def z777 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x7fffe0381ffff00f 0xf7fffe0381ffff00

def z778 : W := mkw 0x37f500000b4c6000 0x237f500000b4c600 0x3fe0000013fe700a 0x03fe0000013fe700

def z779 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc6606f39907ffc72 0x7c6606f39907ffc7

def z780 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf9fffc01ffe0f8f 0xfbf9fffc01ffe0f8

def z781 : W := mkw 0x1859702e55815ae0 0x51859702e55815ae 0x7879f03e7f81fff7 0xf7879f03e7f81fff

def z782 : W := mkw 0x022622191024b840 0x0022622191024b84 0xc6666f39907ffc7b 0xfc6666f39907ffc7

def z783 : W := mkw 0x008808420c5105a0 0x0008808420c5105a 0xc19f98c7ec718ffd 0xec19f98c7ec718ff

def z784 : W := mkw 0x3f7556b5420c2000 0x63f7556b5420c200 0xffffffffe00e000f 0xdffffffffe00e000

def z785 : W := mkw 0xad807de41ada0f00 0x0ad807de41ada0f0 0xff807ffe1ffe0f8f 0x7ff807ffe1ffe0f8

def z786 : W := mkw 0x008a8842af79c5ba 0x2008a8842af79c5b 0xc19f98c7eff18ffd 0xec19f98c7eff18ff

def z787 : W := mkw 0xa58029401ada0f00 0x0a58029401ada0f0 0xbf806f001ffe0f8f 0x7bf806f001ffe0f8

def z788 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x7fff80001ffffc7f 0xe7fff80001ffffc7

def z789 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x787ff03fff81fff7 0xf787ff03fff81fff

def z790 : W := mkw 0x1275023540000000 0x4127502354000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z791 : W := mkw 0x27a780000a6ca000 0x227a780000a6ca00 0x3fe780001ffff00f 0xa3fe780001ffff00

def z792 : W := mkw 0x75d9ab199f5b5c5c 0x275d9ab199f5b5c5 0xf999ef398f800c74 0x5f999ef398f800c7

def z793 : W := mkw 0xefa656d98aecb35c 0x0efa656d98aecb35 0x79e610f98f81f3f4 0x879e610f98f81f3f

def z794 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x3878703e1f81fff6 0x33878703e1f81fff

def z795 : W := mkw 0x3f7576bd538c7a40 0x73f7576bd538c7a4 0x3e606738138e7002 0x13e606738138e700

def z796 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x419f90c7ec718ff4 0xa419f90c7ec718ff

def z797 : W := mkw 0x37f500000b4c6000 0x237f500000b4c600 0x3e6000001ffe7002 0x23e6000001ffe700

def z798 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3fff800013fff00a 0x83fff800013fff00

def z799 : W := mkw 0x422623191026b844 0x0422623191026b84 0x46666738107ffc7b 0xf46666738107ffc7

def z800 : W := mkw 0x37ff8000af6de01a 0x237ff8000af6de01 0x3fff8001fffff00f 0xa3fff8001fffff00

def z801 : W := mkw 0x127600000124e000 0x0127600000124e00 0x3e66000013fff00b 0xa3e66000013fff00

def z802 : W := mkw 0x35db80000f6de000 0x235db80000f6de00 0x39f980001ffff007 0xa39f980001ffff00

def z803 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xff807fc01fff8fff 0xfff807fc01fff8ff

def z804 : W := mkw 0xb5d80dee0f5b55e0 0x1b5d80dee0f5b55e 0xc7f80ffe007ff078 0x8c7f80ffe007ff07

def z805 : W := mkw 0x7d537dacd036bc5c 0x47d537dacd036bc5 0x399990c6707ffc74 0x2399990c6707ffc7

def z806 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0xf87878ffff81fff7 0xff87878ffff81fff

def z807 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x79f9f0fe7f81fff7 0xf79f9f0fe7f81fff

def z808 : W := mkw 0x5a7e5b3785b7e6bc 0x15a7e5b3785b7e6b 0xbe1e1f078ffe038c 0x0be1e1f078ffe038

def z809 : W := mkw 0x022600000024a000 0x0022600000024a00 0x3e6600001ffff00f 0xa3e6600001ffff00

def z810 : W := mkw 0xe7a78fd18a7ea51c 0x2e7a78fd18a7ea51 0x87878fc1807e0008 0x087878fc1807e000

def z811 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3e7f80001ffff002 0xa3e7f80001ffff00

def z812 : W := mkw 0x2d8074801ac80a00 0x02d8074801ac80a0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z813 : W := mkw 0x88007dc010920f00 0x088007dc010920f0 0xbe007fc01ffe0f8f 0x7be007fc01ffe0f8

def z814 : W := mkw 0x37ff80244f6de000 0x637ff80244f6de00 0x3fff80067ffff00f 0xa3fff80067ffff00

def z815 : W := mkw 0x0002290890329c58 0x00002290890329c5 0xc6666f39907ffc7b 0xfc6666f39907ffc7

def z816 : W := mkw 0x48007b3d90921e5c 0x148007b3d90921e5 0xc0006f3980000c70 0x5c0006f3980000c7

def z817 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0xbfffef001ffff00f 0xfbfffef001ffff00

def z818 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffff80000f 0xfffffffffff80000

def z819 : W := mkw 0x37f780000b6ce000 0x237f780000b6ce00 0x3e60000013fe7002 0x03e60000013fe700

def z820 : W := mkw 0x808a8942ae7b85ba 0x0808a8942ae7b85b 0xc19f98c7ec7f8ffd 0xec19f98c7ec7f8ff

def z821 : W := mkw 0xad80fdc03ada0f02 0x0ad80fdc03ada0f0 0xbf81ffc07ffe0f8f 0x7bf81ffc07ffe0f8

def z822 : W := mkw 0x2f2556b540000000 0x42f2556b54000000 0xc79fffffe000000d 0xdc79fffffe000000

def z823 : W := mkw 0x3f7576bd50801a40 0x53f7576bd50801a4 0x3e60673800000002 0x13e6067380000000

def z824 : W := mkw 0x000a8842a43185ba 0x0000a8842a43185b 0xc19f98c7e0018ffd 0xcc19f98c7e0018ff

def z825 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xff987fc61ffe0f8f 0xfff987fc61ffe0f8

def z826 : W := mkw 0x3f7556b542080000 0x43f7556b54208000 0xfffffffff38e000f 0xdfffffffff38e000

def z827 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xff9fffffe000000c 0x5ff9fffffe000000

def z828 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc6666f39807ffc78 0xdc6666f39807ffc7

def z829 : W := mkw 0x000a8002a42180ba 0x0000a8002a42180b 0xc19f98c7ec018ffd 0xec19f98c7ec018ff

def z830 : W := mkw 0x008a8842ae7da5ba 0x2008a8842ae7da5b 0xc19f98c7ec7f8ffd 0xec19f98c7ec7f8ff

def z831 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc79fffc7ec718fff 0xfc79fffc7ec718ff

def z832 : W := mkw 0x3f7556b541046000 0x63f7556b54104600 0xffffffffe000700f 0xdffffffffe000700

def z833 : W := mkw 0x37ff8002af6de0ba 0x237ff8002af6de0b 0x7fff9007ffffffff 0xe7fff9007fffffff

def z834 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7e78703e1fffffff 0xf7e78703e1ffffff

def z835 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xffe07ff81ffe0f8f 0xfffe07ff81ffe0f8

def z836 : W := mkw 0x527f023fc525f0fc 0x5527f023fc525f0f 0x407f803fe001f070 0x8407f803fe001f07

def z837 : W := mkw 0x37ff80260f6de0a0 0x337ff80260f6de0a 0x3fff80061ffff00f 0xa3fff80061ffff00

def z838 : W := mkw 0x185874ae15815ae0 0x1185874ae15815ae 0xf8787ffe1f81fff7 0xff8787ffe1f81fff

def z839 : W := mkw 0x37ff82354f6de000 0x637ff82354f6de00 0xffffef3ffffff00f 0xfffffef3ffffff00

def z840 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x7fff90061ffff00f 0xe7fff90061ffff00

def z841 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3fff80001ffe700e 0x03fff80001ffe700

def z842 : W := mkw 0x1858502e058152e0 0x11858502e058152e 0x7878103e0f81fff5 0xe7878103e0f81fff

def z843 : W := mkw 0x258a80000f6de000 0x2258a80000f6de00 0x3e0000001ffff002 0x23e0000001ffff00

def z844 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xfffffffff001f00f 0xffffffffff001f00

def z845 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3f9f80001ffff00c 0x23f9f80001ffff00

def z846 : W := mkw 0x12ff80000f6de000 0x212ff80000f6de00 0x387f80001ffff007 0xa387f80001ffff00

def z847 : W := mkw 0x1058200a15815ae0 0x11058200a15815ae 0x787860381f81fff7 0xf787860381f81fff

def z848 : W := mkw 0x3dd9d4a64fc942a0 0x73dd9d4a64fc942a 0x399990c66f800384 0x0399990c66f80038

def z849 : W := mkw 0x10da80000f6de000 0x210da80000f6de00 0x381800001ffff004 0x2381800001ffff00

def z850 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffe0018c7f 0xfffffffffe0018c7

def z851 : W := mkw 0x422623199026b85c 0x0422623199026b85 0x46666739907ff07b 0xb46666739907ff07

def z852 : W := mkw 0x37750842a31c65ba 0x237750842a31c65b 0xfe6018c7f38e7ff2 0x4fe6018c7f38e7ff

def z853 : W := mkw 0x088ad6b54f6de000 0x6088ad6b54f6de00 0xc0007ffffffff000 0x7c0007ffffffff00

def z854 : W := mkw 0xc2262b5990b6bf5c 0x0c2262b5990b6bf5 0xc6666f39907ffffb 0xfc6666f39907ffff

def z855 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc7e67ff9907ffc7f 0xfc7e67ff9907ffc7

def z856 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3fe000001ffff00f 0x23fe000001ffff00

def z857 : W := mkw 0x2d007d8010920e00 0x02d007d8010920e0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z858 : W := mkw 0x37fd00000f494000 0x037fd00000f49400 0x3fff80001ffff00f 0xa3fff80001ffff00

def z859 : W := mkw 0x37ff82114f6de000 0x637ff82114f6de00 0x3fff8001fffff00f 0xa3fff8001fffff00

def z860 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x79fff03e1f81ffff 0xf79fff03e1f81fff

def z861 : W := mkw 0x408aa94abf7ffdfe 0x2408aa94abf7ffdf 0x000000001ffffff0 0x2000000001ffffff

def z862 : W := mkw 0x527f821ba525f0fe 0x2527f821ba525f0f 0x407f803fe001f070 0x8407f803fe001f07

def z863 : W := mkw 0xe7a68fd1aa7ea51e 0x0e7a68fd1aa7ea51 0x87878fc1e07e0008 0x087878fc1e07e000

def z864 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0x819f98c7ec718ffc 0x2819f98c7ec718ff

def z865 : W := mkw 0x4227ab199036bc5c 0x24227ab199036bc5 0xc667ef39907ffc7b 0xfc667ef39907ffc7

def z866 : W := mkw 0x008a8942ac7385ba 0x0008a8942ac7385b 0xc79f9fc7ec7f8ffd 0xec79f9fc7ec7f8ff

def z867 : W := mkw 0x008a80020c6180a0 0x0008a80020c6180a 0xc19f98c7ec718ffd 0xec19f98c7ec718ff

def z868 : W := mkw 0x00800842a85005ba 0x000800842a85005b 0xc19f98c7ec700ffd 0xec19f98c7ec700ff

def z869 : W := mkw 0x3775021100000000 0x0377502110000000 0xffffffffe000000f 0xdffffffffe000000

def z870 : W := mkw 0x00000002000000a0 0x000000002000000a 0xc19f98c7e0000ffd 0xcc19f98c7e0000ff

def z871 : W := mkw 0x008a8042ac6181ba 0x0008a8042ac6181b 0x419f90c7ec018ff5 0xe419f90c7ec018ff

def z872 : W := mkw 0x37ff8042af6de1ba 0x237ff8042af6de1b 0x7fff90c7fffff3ff 0xa7fff90c7fffff3f

def z873 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0x3e0077001ffe0f87 0x73e0077001ffe0f8

def z874 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc19f98c7ec700ffc 0x4c19f98c7ec700ff

def z875 : W := mkw 0x7f7577bd51867a44 0x57f7577bd51867a4 0x3e606738138e7002 0x13e606738138e700

def z876 : W := mkw 0x377506b540000000 0x4377506b54000000 0xc7ffefffe000000b 0xdc7ffefffe000000

def z877 : W := mkw 0x37fd00000f4d6000 0x237fd00000f4d600 0x3ff800001ffff00f 0xa3ff800001ffff00

def z878 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xff867fc19ffe0f8f 0xfff867fc19ffe0f8

def z879 : W := mkw 0x527f823f8525f0fc 0x3527f823f8525f0f 0x407f803f8001f070 0x8407f803f8001f07

def z880 : W := mkw 0x000a0802843184b8 0x0000a0802843184b 0xc19f98c7ec718ffd 0xec19f98c7ec718ff

def z881 : W := mkw 0x37ff80020f6de0a0 0x237ff80020f6de0a 0x3fff80001fffffff 0xa3fff80001ffffff

def z882 : W := mkw 0xad8054c00ac80300 0x0ad8054c00ac8030 0xbf807fc01ffe038f 0x7bf807fc01ffe038

def z883 : W := mkw 0x00888842ac5105ba 0x000888842ac5105b 0xc19f98c7ec000ffd 0xcc19f98c7ec000ff

def z884 : W := mkw 0x105a00000525e000 0x0105a00000525e00 0x387800001ffff007 0xa387800001ffff00

def z885 : W := mkw 0xad807de45ada0f00 0x4ad807de45ada0f0 0xbf807fc67ffe0f8f 0x7bf807fc67ffe0f8

def z886 : W := mkw 0x37fe00000f6de000 0x037fe00000f6de00 0x3ffe00001ffff00f 0xa3ffe00001ffff00

def z887 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc6667f399c7fffff 0xfc6667f399c7ffff

def z888 : W := mkw 0x10da80000f6de000 0x210da80000f6de00 0x39ff80001ffff00f 0xa39ff80001ffff00

def z889 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbe006f001ffe0f8b 0x7be006f001ffe0f8

def z890 : W := mkw 0x10d800000f494000 0x010d800000f49400 0x387800001ffff007 0xa387800001ffff00

def z891 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffefffe000000a 0x9ffffefffe000000

def z892 : W := mkw 0x37ff8002af6de0ba 0x237ff8002af6de0b 0x3fff80001ffff07f 0xa3fff80001ffff07

def z893 : W := mkw 0x258800000f494000 0x0258800000f49400 0x3f8000001ffff00f 0x23f8000001ffff00

def z894 : W := mkw 0x37750000030c6000 0x237750000030c600 0x3e60000013fe700b 0x23e60000013fe700

def z895 : W := mkw 0x35db80000f6de000 0x235db80000f6de00 0x380000001ffff000 0x2380000001ffff00

def z896 : W := mkw 0x272d269b55815ae0 0x5272d269b55815ae 0x87878fc1ff81fff8 0x287878fc1ff81fff

def z897 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0xffff88019ffff00f 0xeffff88019ffff00

def z898 : W := mkw 0x37ff80422f6de1a2 0x237ff80422f6de1a 0x7fff90c67fffffff 0xe7fff90c67ffffff

def z899 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3ff980001ffff006 0x23ff980001ffff00

def z900 : W := mkw 0x2d8079001ada0e00 0x02d8079001ada0e0 0xbf807f001ffe0f8f 0x7bf807f001ffe0f8

def z901 : W := mkw 0x4800792e90921efc 0x14800792e90921ef 0x4000703e00000ff0 0x54000703e00000ff

def z902 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3fff90001fffff8f 0xe3fff90001fffff8

def z903 : W := mkw 0x3d5054a400000000 0x03d5054a40000000 0xffffffffe000000f 0xdffffffffe000000

def z904 : W := mkw 0x1a7556b540000000 0x41a7556b54000000 0xc1ffffffe000000d 0xdc1ffffffe000000

def z905 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7878603e1f81fff2 0xb7878603e1f81fff

def z906 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x7fff8007fffff00f 0xa7fff8007fffff00

def z907 : W := mkw 0x377f8000072de000 0x2377f8000072de00 0x3e7f800013fff00b 0xa3e7f800013fff00

def z908 : W := mkw 0x37ff84800f6de000 0x237ff84800f6de00 0xbfff8fc01ffff00f 0xabfff8fc01ffff00

def z909 : W := mkw 0x1058292e15135ce0 0x11058292e15135ce 0xc6786f3e107ffc7b 0xfc6786f3e107ffc7

def z910 : W := mkw 0xed807dc89ada1f5c 0x0ed807dc89ada1f5 0xbf807fc01ffe0fff 0x7bf807fc01ffe0ff

def z911 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xf9ffffffe0000004 0xdf9ffffffe000000

def z912 : W := mkw 0x35d980000f494000 0x235d980000f49400 0x3ff980001ffff00f 0xa3ff980001ffff00

def z913 : W := mkw 0x27ae80000f6de000 0x227ae80000f6de00 0x3fe600001ffff00f 0xa3fe600001ffff00

def z914 : W := mkw 0x37ff8237ef6de0ba 0x637ff8237ef6de0b 0x7fff803ffffff07f 0xa7fff803ffffff07

def z915 : W := mkw 0x12fe80000d65e000 0x012fe80000d65e00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z916 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf87ffc1fffe0f8f 0x7bf87ffc1fffe0f8

def z917 : W := mkw 0x27a400000a4c2000 0x027a400000a4c200 0x3fe000001ffe700f 0x23fe000001ffe700

def z918 : W := mkw 0x27a78ed1ea7ca51a 0x627a78ed1ea7ca51 0x87878fc1e07e0008 0x087878fc1e07e000

def z919 : W := mkw 0x3d5156b540000000 0x43d5156b54000000 0xf99fffffe000000d 0xdf99fffffe000000

def z920 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x386070381f81fff7 0x7386070381f81fff

def z921 : W := mkw 0x35da80000f69c000 0x035da80000f69c00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z922 : W := mkw 0xbf7556b542880200 0x4bf7556b54288020 0xffffffffe380000f 0xdffffffffe380000

def z923 : W := mkw 0x37ff80020f6de0a0 0x237ff80020f6de0a 0xffff98c7ffffffff 0xeffff98c7fffffff

def z924 : W := mkw 0x258029401a5a0d00 0x0258029401a5a0d0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z925 : W := mkw 0x527e823fa525f0fe 0x1527e823fa525f0f 0x407f803fe001f070 0x8407f803fe001f07

def z926 : W := mkw 0x42272b19d036bc5c 0x442272b19d036bc5 0xc667ef39f07ffc7b 0xfc667ef39f07ffc7

def z927 : W := mkw 0x37ff80020f6de0a0 0x237ff80020f6de0a 0x3fff90061ffff38f 0xa3fff90061ffff38

def z928 : W := mkw 0x37f700000b6ce000 0x237f700000b6ce00 0x3fe600001ffff00f 0xa3fe600001ffff00

def z929 : W := mkw 0x37ff86b54f6de000 0x637ff86b54f6de00 0xffff8ffffffff00f 0xaffff8ffffffff00

def z930 : W := mkw 0x27ae80000e6da000 0x027ae80000e6da00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z931 : W := mkw 0x37ff8002af6de0ba 0x237ff8002af6de0b 0xffff98c7fffff07f 0xeffff98c7fffff07

def z932 : W := mkw 0x37f780000b6ce000 0x237f780000b6ce00 0x3fe7800013fff00b 0xa3fe7800013fff00

def z933 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3e6600001ffff00b 0xa3e6600001ffff00

def z934 : W := mkw 0xb7ff84c00f6de100 0x2b7ff84c00f6de10 0x3fff80c01ffff00f 0xa3fff80c01ffff00

def z935 : W := mkw 0x42262b59b036bd5e 0x042262b59b036bd5 0xc6666ff9f07ffc7b 0xfc6666ff9f07ffc7

def z936 : W := mkw 0x35da80000f6de000 0x235da80000f6de00 0x3ff800001ffff00f 0xa3ff800001ffff00

def z937 : W := mkw 0x88007dc810921f40 0x088007dc810921f4 0xc0007ff800000ff0 0x5c0007ff800000ff

def z938 : W := mkw 0x3f7556b541804200 0x53f7556b54180420 0xffffffffe380000f 0xdffffffffe380000

def z939 : W := mkw 0x37ff80400f6de100 0x237ff80400f6de10 0x3fff90c01ffff38f 0xa3fff90c01ffff38

def z940 : W := mkw 0x1850702c10801a40 0x01850702c10801a4 0x7878703e1f81fff7 0xf7878703e1f81fff

def z941 : W := mkw 0x1058202e15815ae0 0x11058202e15815ae 0x7878003e1f81fff7 0xa7878003e1f81fff

def z942 : W := mkw 0x0000021100000000 0x0000002110000000 0xc19fffffe000000d 0xdc19fffffe000000

def z943 : W := mkw 0x0880794018d20f00 0x00880794018d20f0 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z944 : W := mkw 0x985875ae15835ae0 0x1985875ae15835ae 0x7878773e1f81fff7 0xf7878773e1f81fff

def z945 : W := mkw 0x0808700a14811ae0 0x00808700a14811ae 0x7878703e1f81fff7 0xf7878703e1f81fff

def z946 : W := mkw 0x258000000a480000 0x0258000000a48000 0x3fe000001ffff00f 0xa3fe000001ffff00

def z947 : W := mkw 0x127f8237e525e0ba 0x6127f8237e525e0b 0x407f803fe001f070 0x8407f803fe001f07

def z948 : W := mkw 0x185874ae55815ae0 0x5185874ae55815ae 0x787870fe7f81fff7 0xf787870fe7f81fff

def z949 : W := mkw 0x37f700000a6ca000 0x037f700000a6ca00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z950 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf807fc01ffe038e 0x1bf807fc01ffe038

def z951 : W := mkw 0x1058200a150158e0 0x01058200a150158e 0x7878703e1f81fff7 0xf7878703e1f81fff

def z952 : W := mkw 0x02242b1910121c40 0x002242b1910121c4 0xc6666f39907ffc7b 0xfc6666f39907ffc7

def z953 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xff807fc7fffe0f8f 0x7ff807fc7fffe0f8

def z954 : W := mkw 0x022629081036bc40 0x0022629081036bc4 0xc6666f38107ffc7b 0xfc6666f38107ffc7

def z955 : W := mkw 0x37ff82110f6de000 0x237ff82110f6de00 0xfffffffffffff00f 0xffffffffffffff00

def z956 : W := mkw 0xad8075801aca0a00 0x0ad8075801aca0a0 0x3f8077001ffe0f8f 0x73f8077001ffe0f8

def z957 : W := mkw 0x37ff80422f6de1a2 0x237ff80422f6de1a 0x3fff80001ffff38f 0xa3fff80001ffff38

def z958 : W := mkw 0x185056b540000000 0x4185056b54000000 0xf9ffffffe000000f 0xdf9ffffffe000000

def z959 : W := mkw 0x88007deeb0921ffa 0x188007deeb0921ff 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z960 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0x86606f38107ffc7b 0x786606f38107ffc7

def z961 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xf99f98c7fff18fff 0xef99f98c7fff18ff

def z962 : W := mkw 0x27af80000f6de000 0x227af80000f6de00 0x3f8780001ffff00f 0x23f8780001ffff00

def z963 : W := mkw 0x48007fbfd0921efc 0x548007fbfd0921ef 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z964 : W := mkw 0x3f7556b543084000 0x63f7556b54308400 0xffffffffe380000f 0xdffffffffe380000

def z965 : W := mkw 0xbdd954e64fc943a0 0x5bdd954e64fc943a 0x399990c66f800384 0x0399990c66f80038

def z966 : W := mkw 0xad007d80129a0e00 0x0ad007d80129a0e0 0xbe007f001ffe0f8f 0x7be007f001ffe0f8

def z967 : W := mkw 0x2d0056b540000000 0x42d0056b54000000 0xff9fffffe000000f 0xdff9fffffe000000

def z968 : W := mkw 0xc8007f9990921e5c 0x0c8007f9990921e5 0xc0006f3980000c70 0x5c0006f3980000c7

def z969 : W := mkw 0x127f823f4525f0e0 0x7127f823f4525f0e 0x407f803fe001f070 0x8407f803fe001f07

def z970 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc1fff8ffec718fff 0xfc1fff8ffec718ff

def z971 : W := mkw 0x37770000032ce000 0x237770000032ce00 0x3e66000013fe700a 0x03e66000013fe700

def z972 : W := mkw 0x0800702e10801ae0 0x10800702e10801ae 0x7860703e1f81fff7 0xf7860703e1f81fff

def z973 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc6666f39907ff07a 0x9c6666f39907ff07

def z974 : W := mkw 0x37f780000b6ce000 0x237f780000b6ce00 0x3fe780001ffe700f 0x23fe780001ffe700

def z975 : W := mkw 0x42242b1910163c44 0x042242b1910163c4 0xc6606f38107ffc7b 0xfc6606f38107ffc7

def z976 : W := mkw 0x3dd9d4e66f4941a2 0x63dd9d4e66f4941a 0x399990c66f800384 0x0399990c66f80038

def z977 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc6667ffff07ffc7b 0xfc6667ffff07ffc7

def z978 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0x3f8067001ffe0f8f 0x33f8067001ffe0f8

def z979 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf801fc01ffe0f8c 0x2bf801fc01ffe0f8

def z980 : W := mkw 0x008a8842ae7985ba 0x0008a8842ae7985b 0xc19f98c7ffff8ffd 0xec19f98c7ffff8ff

def z981 : W := mkw 0x2725069140000000 0x4272506914000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z982 : W := mkw 0x37ff82354f6de000 0x637ff82354f6de00 0x3fff80381ffff00f 0xa3fff80381ffff00

def z983 : W := mkw 0x258200000a6ca000 0x0258200000a6ca00 0x3f8000001ffff00f 0x23f8000001ffff00

def z984 : W := mkw 0x8800796e10921fe0 0x18800796e10921fe 0x4000703e00000ff0 0x54000703e00000ff

def z985 : W := mkw 0xc08aa94abeffbffe 0x0c08aa94abeffbff 0x000000001ffffff0 0x2000000001ffffff

def z986 : W := mkw 0x1058000005014000 0x0105800000501400 0x3e7800001ffff00f 0xa3e7800001ffff00

def z987 : W := mkw 0x00020842a03085ba 0x000020842a03085b 0xc19f98c7e0718ffd 0xec19f98c7e0718ff

def z988 : W := mkw 0x35db80000f6de000 0x235db80000f6de00 0x3f9980001ffff00f 0x23f9980001ffff00

def z989 : W := mkw 0x37f500000b4c6000 0x237f500000b4c600 0x3fff80001ffe700f 0xa3fff80001ffe700

def z990 : W := mkw 0xad807dc81ada1f40 0x0ad807dc81ada1f4 0xff807ff81ffe0fff 0x7ff807ff81ffe0ff

def z991 : W := mkw 0x408a8942ac77a5be 0x0408a8942ac77a5b 0xc19f98c7ec7f8ffd 0xec19f98c7ec7f8ff

def z992 : W := mkw 0x408aa94abdf7fffe 0x1408aa94abdf7fff 0x000000001ffffff0 0x2000000001ffffff

def z993 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xc7ffffffe0000008 0xdc7ffffffe000000

def z994 : W := mkw 0x37ff80020f6de0a0 0x237ff80020f6de0a 0x7fff80061ffff07f 0xa7fff80061ffff07

def z995 : W := mkw 0x37ff82110f6de000 0x237ff82110f6de00 0x3fffe7381ffff00f 0xb3fffe7381ffff00

def z996 : W := mkw 0xa5802dc01ada0f00 0x0a5802dc01ada0f0 0xbf800fc01ffe0f8f 0x2bf800fc01ffe0f8

def z997 : W := mkw 0x37ff84804f6de000 0x637ff84804f6de00 0x3fff80c07ffff00f 0xa3fff80c07ffff00

def z998 : W := mkw 0xad807dc0bada0f1a 0x0ad807dc0bada0f1 0xbf807fc1fffe0f8f 0x7bf807fc1fffe0f8

def z999 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0xbfff98c01ffff00f 0xebfff98c01ffff00

def z1000 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x39ff80001ffff004 0xa39ff80001ffff00

def z1001 : W := mkw 0x37ff80422f6de1a2 0x237ff80422f6de1a 0xffff98c7fffff38f 0xeffff98c7fffff38

def z1002 : W := mkw 0xbdd9d4e60fc943a0 0x3bdd9d4e60fc943a 0x399990c60f800384 0x0399990c60f80038

def z1003 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0xfe787f3e1f81ffff 0xffe787f3e1f81fff

def z1004 : W := mkw 0x008a8842ac7185ba 0x0008a8842ac7185b 0xc79f98c7fc7f8fff 0xec79f98c7fc7f8ff

def z1005 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0x3f8077c01ffe0f86 0x33f8077c01ffe0f8

def z1006 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0x3fff90c67ffff00f 0xa3fff90c67ffff00

def z1007 : W := mkw 0xad805dc00ada0700 0x0ad805dc00ada070 0xbf801fc01ffe038f 0x2bf801fc01ffe038

def z1008 : W := mkw 0x4a26721990a4ba5c 0x04a26721990a4ba5 0x786670399f81fff7 0xf786670399f81fff

def z1009 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf807fc00ffe0f8c 0x5bf807fc00ffe0f8

def z1010 : W := mkw 0x12fe80000f6de000 0x212fe80000f6de00 0x3e7e00001ffff00f 0xa3e7e00001ffff00

def z1011 : W := mkw 0x37f780000b6ce000 0x237f780000b6ce00 0x3fff800013fe700f 0x83fff800013fe700

def z1012 : W := mkw 0x1858712e15835ae0 0x11858712e15835ae 0x7e78773e1f8ffff7 0xf7e78773e1f8ffff

def z1013 : W := mkw 0x42262b1990b6be5c 0x042262b1990b6be5 0xc6666f399ffffffb 0xfc6666f399ffffff

def z1014 : W := mkw 0x88007dec10921f40 0x188007dec10921f4 0x80007ff800000f80 0x580007ff800000f8

def z1015 : W := mkw 0x0a2456b540000000 0x40a2456b54000000 0xc7ffffffe000000f 0xdc7ffffffe000000

def z1016 : W := mkw 0x37ff82354f6de000 0x637ff82354f6de00 0xffff98fffffff00f 0xeffff98fffffff00

def z1017 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xfe666f399ffffc7f 0xffe666f399ffffc7

def z1018 : W := mkw 0x258000000b4c6000 0x2258000000b4c600 0x3f8000001ffe700f 0x23f8000001ffe700

def z1019 : W := mkw 0x2f24569100000000 0x02f2456910000000 0xffffffffe000000f 0xdffffffffe000000

def z1020 : W := mkw 0x37ff86914f6de000 0x637ff86914f6de00 0xffffeff9fffff00f 0xfffffeff9fffff00

def z1021 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf806fc01ffe0f8a 0x3bf806fc01ffe0f8

def z1022 : W := mkw 0x808aa94abffbdffa 0x1808aa94abffbdff 0x000000001ffffff0 0x2000000001ffffff

def z1023 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x786060381f81fff3 0xf786060381f81fff

def z1024 : W := mkw 0x37ff80240f6de000 0x237ff80240f6de00 0x7fff803e1ffff00f 0xa7fff803e1ffff00

def z1025 : W := mkw 0x3f7556b541004000 0x43f7556b54100400 0xfffffffff380700f 0xdfffffffff380700

def z1026 : W := mkw 0xad8075c01aca0b00 0x0ad8075c01aca0b0 0x3f8077c01ffe038f 0x33f8077c01ffe038

def z1027 : W := mkw 0x1858f02e35815ae2 0x11858f02e35815ae 0x7879f03e7f81fff7 0xf7879f03e7f81fff

def z1028 : W := mkw 0x37ff80022f6de0a2 0x237ff80022f6de0a 0x3fff80067ffff00f 0xa3fff80067ffff00

def z1029 : W := mkw 0x37770000032ce000 0x237770000032ce00 0x3e60000013fff002 0x23e60000013fff00

def z1030 : W := mkw 0x258a80000f6de000 0x2258a80000f6de00 0x398000001ffff004 0x2398000001ffff00

def z1031 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xbfffffffe000000e 0x1bfffffffe000000

def z1032 : W := mkw 0x3f7556b540042000 0x43f7556b54004200 0xfffffffff00e700f 0xdfffffffff00e700

def z1033 : W := mkw 0x008a8842ad71c5ba 0x0008a8842ad71c5b 0xc19f98c7fff1fffd 0xec19f98c7fff1fff

def z1034 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7878103e1f81fff4 0xa7878103e1f81fff

def z1035 : W := mkw 0xc8007dc890921f5c 0x0c8007dc890921f5 0x80007fc000000ff0 0x580007fc000000ff

def z1036 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0xf87e783f9f81ffff 0xff87e783f9f81fff

def z1037 : W := mkw 0x42262b199036bc5c 0x042262b199036bc5 0xc67fef3ff07ffc7b 0xfc67fef3ff07ffc7

def z1038 : W := mkw 0x258a80000f6de000 0x2258a80000f6de00 0x3f9f80001ffff00f 0xa3f9f80001ffff00

def z1039 : W := mkw 0x37ff86914f6de000 0x637ff86914f6de00 0x3fff87001ffff00f 0xa3fff87001ffff00

def z1040 : W := mkw 0x37ff80402f6de102 0x237ff80402f6de10 0x3fff80c07ffff00f 0xa3fff80c07ffff00

def z1041 : W := mkw 0x2d805cc00a580500 0x02d805cc00a58050 0xbf807fc01ffe0f8f 0x7bf807fc01ffe0f8

def z1042 : W := mkw 0xad807dc01ada0f00 0x0ad807dc01ada0f0 0xbf99ffc67ffe0f8f 0x7bf99ffc67ffe0f8

def z1043 : W := mkw 0x88007fff50921fe0 0x588007fff50921fe 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z1044 : W := mkw 0xff7577bd528e3a44 0x4ff7577bd528e3a4 0x3e606738138e7002 0x13e606738138e700

def z1045 : W := mkw 0xad807dc09ada0f18 0x0ad807dc09ada0f1 0xff807fc19ffe0fff 0x7ff807fc19ffe0ff

def z1046 : W := mkw 0xad805dc00ada0700 0x0ad805dc00ada070 0xbf807fc00ffe038f 0x5bf807fc00ffe038

def z1047 : W := mkw 0x008a80000f6de000 0x2008a80000f6de00 0x380000001ffff007 0x2380000001ffff00

def z1048 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0x7860703e1f81fff2 0x77860703e1f81fff

def z1049 : W := mkw 0x02260a118034a418 0x002260a118034a41 0xc6666f39907ffc7b 0xfc6666f39907ffc7

def z1050 : W := mkw 0x1858702e15815ae0 0x11858702e15815ae 0xf9f878fe1f81ffff 0xff9f878fe1f81fff

def z1051 : W := mkw 0x008a8842ad75e5ba 0x2008a8842ad75e5b 0xc19f98c7ec71fffd 0xec19f98c7ec71fff

def z1052 : W := mkw 0x3f7556b540000000 0x43f7556b54000000 0xffffffffec000f8f 0xfffffffffec000f8

def z1053 : W := mkw 0xbdd8d4e62fc943a2 0x1bdd8d4e62fc943a 0x399990c66f800384 0x0399990c66f80038

def z1054 : W := mkw 0xc8007fd910921f44 0x0c8007fd910921f4 0x80007ff800000f80 0x580007ff800000f8

def z1055 : W := mkw 0x48007b7fb0921ffe 0x148007b7fb0921ff 0xc0007fffe0000ff0 0x5c0007fffe0000ff

def z1056 : W := mkw 0x27260000022ca000 0x027260000022ca00 0x3e66000013fff00b 0xa3e66000013fff00

def z1057 : W := mkw 0x377f00000525e000 0x0377f00000525e00 0x3fff80001ffff00f 0xa3fff80001ffff00

def z1058 : W := mkw 0x37ff80000f6de000 0x237ff80000f6de00 0xbfff88c1fffff00f 0xabfff88c1fffff00

def z1059 : W := mkw 0x377f0000072de000 0x2377f0000072de00 0x3e7e00001ffff00f 0xa3e7e00001ffff00

def z1060 : W := mkw 0x37770000032ce000 0x237770000032ce00 0x3fff800013fff00f 0xa3fff800013fff00

def z1061 : W := mkw 0x408aa94abc739dfe 0x0408aa94abc739df 0x000000000c718ff0 0x2000000000c718ff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z1,z2,z3,z8,z5,z6])],[(0,[z9,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z10,z6])],[(0,[z1,z11,z2,z3,z8,z5,z6]),(0,[z1,z12,z2,z8,z5,z13,z6])],[(0,[z1,z14,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z15]),(0,[z1,z2,z16,z3,z8,z5,z6])],[(0,[z1,z2,z3,z17,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z18,z6]),(0,[z1,z2,z19,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z20,z5,z6])],[(0,[z1,z12,z2,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z13,z6])],[(0,[z1,z2,z22,z3,z8,z5,z6]),(0,[z1,z23,z24,z3,z8,z5,z6]),(0,[z25,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z26,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z27,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z28,z6]),(0,[z1,z29,z2,z3,z8,z5,z6]),(0,[z1,z2,z30,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z31])],[(0,[z32,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z33]),(0,[z1,z2,z34,z3,z8,z5,z6]),(1,[z1,z2,z35,z8,z36,z6]),(0,[z1,z2,z3,z37,z8,z5,z6])],[(0,[z1,z2,z3,z8,z38,z5,z6]),(0,[z39,z1,z2,z3,z8,z5,z6]),(0,[z1,z40,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z41,z5,z42,z6])],[(0,[z1,z2,z3,z8,z5,z43,z6]),(0,[z1,z2,z3,z8,z5,z44,z6]),(0,[z1,z2,z3,z8,z45,z5,z6]),(0,[z46,z1,z2,z3,z8,z5,z6]),(0,[z1,z47,z2,z3,z8,z5,z6])],[(0,[z48,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z49,z50]),(0,[z1,z2,z3,z8,z51,z5,z6])],[(0,[z1,z2,z3,z8,z5,z52,z6]),(0,[z1,z2,z3,z8,z5,z53,z6]),(0,[z1,z2,z3,z54,z8,z5,z6]),(0,[z55,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z36,z5,z6]),(0,[z56,z1,z2,z3,z8,z5,z6]),(0,[z57,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z58,z8,z5,z6,z59]),(1,[z1,z2,z60,z3,z5,z61])],[(0,[z1,z2,z3,z8,z5,z62,z6]),(0,[z1,z2,z3,z8,z5,z63,z6])],[(0,[z64,z1,z65,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z66,z6]),(0,[z1,z2,z3,z8,z67,z5,z6]),(0,[z1,z2,z3,z68,z8,z5,z6]),(0,[z1,z2,z3,z8,z69,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z70])]],
   [[(0,[z1,z71,z2,z3,z8,z5,z6]),(0,[z72,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z73,z5,z6])],[(0,[z74,z1,z75,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z76,z5,z6]),(0,[z1,z23,z77,z3,z8,z5,z6]),(0,[z1,z78,z2,z3,z8,z5,z6]),(0,[z79,z1,z80,z3,z8,z5,z6]),(1,[z1,z2,z8,z5,z81,z6]),(0,[z1,z2,z3,z82,z8,z5,z6]),(0,[z1,z2,z83,z3,z8,z5,z6])],[(0,[z84,z85,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z86,z6]),(0,[z1,z2,z3,z8,z87,z5,z6]),(0,[z1,z2,z3,z8,z5,z88,z6]),(0,[z1,z2,z3,z8,z5,z6,z89]),(0,[z1,z2,z3,z8,z5,z90,z6]),(0,[z1,z2,z3,z8,z5,z91,z6])],[(0,[z92,z1,z2,z93,z8,z5,z6]),(0,[z1,z2,z94,z3,z8,z5,z6])],[(0,[z1,z80,z2,z3,z8,z5,z6]),(0,[z1,z95,z2,z3,z8,z5,z6]),(0,[z79,z1,z96,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z97,z6]),(0,[z1,z2,z3,z8,z98,z5,z6]),(0,[z1,z99,z2,z3,z8,z5,z6])],[(0,[z100,z1,z2,z3,z8,z5,z6]),(0,[z1,z101,z2,z3,z8,z5,z6]),(0,[z1,z102,z2,z3,z8,z50,z6]),(0,[z1,z2,z3,z8,z5,z6,z103]),(0,[z104,z1,z2,z3,z8,z5,z6])],[(1,[z1,z75,z3,z8,z5,z6]),(0,[z1,z2,z105,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z106]),(1,[z84,z2,z3,z8,z5,z107]),(0,[z1,z2,z3,z8,z5,z108,z6]),(0,[z1,z2,z3,z5,z91,z6,z61]),(0,[z109,z1,z2,z3,z8,z5,z6])],[(1,[z110,z2,z3,z8,z111,z6]),(0,[z1,z112,z2,z3,z8,z5,z6]),(1,[z1,z2,z113,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z114,z5,z28,z6]),(0,[z2,z3,z8,z5,z107,z6,z115]),(0,[z1,z116,z2,z3,z8,z5,z6]),(0,[z1,z2,z117,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z118,z5,z6]),(0,[z1,z3,z8,z41,z5,z50,z6]),(0,[z1,z2,z93,z3,z73,z5,z6])],[(0,[z74,z1,z119,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z120,z6]),(0,[z1,z2,z3,z121,z8,z5,z6]),(0,[z1,z122,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z123,z6]),(0,[z1,z2,z124,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z125,z6]),(0,[z1,z2,z3,z8,z126,z5,z6]),(0,[z1,z127,z2,z3,z8,z5,z6]),(1,[z1,z128,z2,z3,z129,z6])],[(0,[z1,z2,z3,z76,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z130,z6]),(0,[z1,z2,z3,z131,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z132]),(0,[z1,z133,z2,z3,z8,z5,z6])],[(0,[z1,z2,z134,z3,z8,z5,z6]),(0,[z1,z2,z135,z3,z8,z5,z6]),(0,[z1,z136,z2,z3,z8,z5,z6]),(0,[z1,z2,z137,z3,z8,z5,z6]),(0,[z1,z138,z2,z3,z8,z5,z6])],[(0,[z64,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z139,z3,z8,z5,z6]),(0,[z1,z140,z2,z3,z8,z5,z6]),(0,[z1,z141,z2,z3,z8,z5,z6]),(0,[z1,z142,z2,z3,z8,z5,z6])],[(1,[z1,z119,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z143,z5,z6])]],
   [[(0,[z1,z23,z2,z24,z8,z5,z6]),(0,[z1,z144,z2,z3,z8,z5,z6]),(1,[z1,z2,z93,z73,z5,z6])],[(0,[z145,z1,z2,z3,z8,z5,z6]),(0,[z1,z146,z2,z3,z8,z5,z6]),(0,[z147,z92,z2,z3,z8,z5,z6]),(0,[z1,z148,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z149])],[(0,[z1,z2,z3,z8,z150,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z151]),(0,[z1,z2,z3,z8,z5,z6,z152]),(0,[z1,z2,z3,z8,z5,z153,z6]),(0,[z1,z2,z3,z8,z154,z5,z6])],[(0,[z155,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z156]),(0,[z157,z1,z2,z3,z8,z5,z6])],[(0,[z158,z159,z2,z3,z8,z5,z6])],[(0,[z160,z1,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z42,z6,z161]),(0,[z1,z2,z3,z8,z5,z6,z162]),(0,[z1,z163,z2,z3,z8,z5,z6])],[(0,[z158,z1,z159,z3,z8,z5,z6]),(1,[z1,z77,z8,z164,z5,z6]),(0,[z165,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z166,z6]),(0,[z1,z2,z3,z8,z5,z167,z6])]],
   [[(0,[z1,z168,z2,z3,z8,z5,z6]),(0,[z1,z169,z2,z3,z8,z5,z6]),(0,[z92,z1,z2,z3,z8,z5,z6]),(0,[z92,z170,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z171]),(0,[z172,z1,z2,z3,z8,z5,z6])],[(0,[z173,z1,z2,z3,z8,z5,z6]),(0,[z110,z1,z2,z174,z8,z5,z6]),(0,[z175,z1,z2,z3,z8,z5,z6]),(0,[z1,z136,z2,z3,z8,z5,z161]),(0,[z1,z2,z176,z3,z8,z5,z6])],[(0,[z1,z2,z3,z177,z8,z5,z6]),(0,[z1,z2,z178,z3,z8,z5,z6]),(0,[z1,z179,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z91,z115]),(0,[z180,z1,z2,z3,z8,z5,z6]),(0,[z1,z181,z2,z3,z8,z5,z6])],[(0,[z1,z2,z182,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z183,z6]),(0,[z1,z2,z184,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z185]),(0,[z1,z2,z3,z8,z5,z6,z186]),(0,[z1,z128,z2,z3,z187,z5,z6])],[(0,[z74,z1,z2,z3,z8,z5,z130]),(0,[z1,z188,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z189,z5,z6]),(0,[z1,z2,z35,z3,z8,z190,z6]),(0,[z1,z128,z2,z3,z8,z5,z6]),(0,[z191,z1,z2,z3,z8,z5,z6])],[(0,[z192,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z193,z3,z8,z5,z6]),(0,[z1,z2,z24,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z194]),(0,[z1,z2,z3,z8,z5,z6,z195]),(0,[z84,z1,z2,z196,z8,z5,z6]),(1,[z1,z80,z3,z87,z5,z6]),(0,[z197,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z198,z8,z5,z6]),(0,[z1,z2,z3,z8,z199,z5,z200])]],
   [[(0,[z74,z201,z2,z3,z8,z5,z6]),(0,[z1,z2,z202,z3,z8,z5,z6]),(0,[z85,z1,z2,z3,z8,z5,z6]),(0,[z1,z203,z2,z3,z8,z5,z6]),(0,[z1,z136,z2,z3,z8,z199,z5]),(0,[z92,z1,z2,z8,z5,z190,z6]),(0,[z1,z204,z2,z3,z8,z5,z6])],[(0,[z1,z23,z2,z8,z164,z5,z6]),(0,[z205,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z206,z8,z5,z6])],[(0,[z1,z207,z2,z3,z8,z5,z6]),(0,[z1,z208,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z130]),(0,[z1,z2,z3,z8,z5,z209,z6]),(0,[z1,z2,z3,z8,z5,z6,z210])],[(1,[z1,z2,z211,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z212,z6]),(0,[z1,z2,z3,z8,z5,z213,z6]),(0,[z157,z1,z136,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z214,z6]),(0,[z1,z2,z3,z8,z5,z6,z215]),(0,[z1,z2,z3,z8,z5,z216,z6])],[(0,[z1,z217,z2,z3,z8,z5,z6]),(0,[z110,z1,z2,z218,z8,z5,z6]),(0,[z79,z1,z2,z96,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z219]),(1,[z1,z3,z8,z5,z6,z220])],[(0,[z1,z2,z3,z8,z5,z221,z6]),(0,[z74,z1,z2,z3,z8,z5,z222]),(0,[z84,z1,z2,z3,z8,z5,z6]),(0,[z1,z223,z2,z3,z8,z5,z6]),(0,[z224,z1,z2,z3,z8,z5,z6]),(0,[z1,z225,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z226,z5,z6])],[(0,[z227,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z228,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z229,z6])],[(0,[z230,z1,z2,z3,z8,z5,z6]),(0,[z231,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z232,z3,z8,z5,z6]),(0,[z1,z233,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z234,z5,z6]),(0,[z1,z2,z3,z8,z235,z5,z6]),(0,[z1,z236,z2,z3,z8,z5,z6]),(0,[z1,z2,z60,z3,z8,z5,z91])]],
   [[(0,[z158,z1,z65,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z237,z6]),(0,[z1,z128,z2,z238,z8,z5,z6])],[(0,[z1,z2,z3,z8,z239,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z240]),(0,[z1,z241,z2,z3,z8,z5,z6]),(1,[z1,z136,z3,z8,z5,z161]),(0,[z1,z2,z3,z8,z5,z242,z6]),(0,[z1,z2,z3,z8,z5,z200,z6])],[(0,[z243,z1,z2,z3,z8,z5,z6]),(1,[z1,z2,z3,z8,z5,z222]),(0,[z1,z2,z218,z3,z8,z5,z6]),(0,[z1,z244,z2,z3,z8,z5,z6])],[(0,[z245,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z65,z3,z8,z5,z6]),(0,[z74,z0,z2,z3,z8,z5,z6]),(0,[z1,z2,z246,z3,z8,z5,z6]),(0,[z92,z1,z247,z2,z3,z5,z6]),(0,[z248,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z249,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z250])],[(0,[z1,z2,z58,z3,z8,z5,z13]),(0,[z1,z142,z2,z3,z5,z91,z6])],[(0,[z1,z2,z3,z8,z5,z251,z6]),(0,[z1,z2,z252,z3,z8,z5,z6]),(0,[z1,z2,z3,z253,z8,z5,z6])],[(0,[z254,z1,z2,z3,z8,z5,z6]),(0,[z1,z159,z3,z8,z87,z5,z6]),(0,[z255,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z256,z3,z8,z5,z6]),(0,[z145,z1,z2,z21,z8,z5,z6]),(0,[z1,z2,z3,z257,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z258]),(0,[z1,z2,z3,z259,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z260,z6]),(0,[z110,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z261,z5,z6])],[(1,[z1,z14,z2,z3,z5,z6]),(0,[z1,z262,z2,z3,z8,z5,z6]),(0,[z1,z263,z2,z3,z8,z5,z6])],[(0,[z1,z2,z264,z3,z8,z5,z6]),(1,[z1,z2,z3,z187,z4,z6])],[(0,[z1,z12,z2,z35,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z265]),(0,[z201,z1,z2,z3,z8,z5,z6]),(0,[z266,z1,z2,z3,z8,z5,z6]),(0,[z267,z1,z2,z3,z8,z111,z6]),(0,[z1,z2,z3,z8,z5,z268,z6]),(0,[z1,z2,z3,z8,z269,z5,z6])],[(0,[z1,z77,z2,z3,z8,z5,z6]),(0,[z1,z96,z3,z8,z87,z5,z6]),(0,[z1,z142,z2,z60,z3,z5,z6])],[(0,[z92,z1,z2,z21,z8,z5,z6]),(0,[z270,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z200,z161]),(0,[z1,z2,z3,z8,z271,z5,z6])],[(0,[z158,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z272,z6]),(0,[z1,z2,z273,z3,z8,z5,z6]),(0,[z1,z2,z3,z274,z8,z5,z6])]],
   [[(0,[z1,z2,z275,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z276]),(0,[z0,z2,z3,z76,z8,z5,z6]),(0,[z1,z2,z196,z3,z8,z5,z6]),(0,[z157,z1,z2,z3,z8,z6,z277])],[(0,[z1,z2,z3,z8,z278,z5,z6]),(0,[z1,z2,z58,z21,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z279]),(0,[z85,z1,z2,z3,z8,z5,z115]),(1,[z280,z2,z3,z8,z5,z6])],[(0,[z64,z158,z2,z3,z8,z5,z6]),(0,[z1,z2,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z281,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z282]),(0,[z1,z283,z2,z3,z8,z5,z6])],[(0,[z2,z3,z76,z8,z284,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z285]),(0,[z1,z286,z2,z3,z8,z5,z6]),(0,[z1,z287,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z288,z5,z6])],[(0,[z1,z2,z3,z8,z5,z289,z6]),(1,[z1,z2,z3,z8,z5,z49])],[(0,[z1,z2,z3,z8,z290,z5,z6]),(0,[z1,z2,z3,z8,z291,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z292])],[(0,[z1,z2,z3,z293,z8,z5,z6]),(0,[z1,z2,z3,z174,z8,z5,z6]),(0,[z84,z1,z2,z3,z8,z5,z115]),(0,[z1,z2,z294,z3,z8,z5,z6])],[(1,[z1,z2,z54,z8,z5,z6]),(0,[z295,z1,z2,z3,z8,z5,z6]),(0,[z1,z296,z2,z3,z8,z5,z6])]],
   [[(1,[z64,z65,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z297]),(0,[z1,z298,z2,z3,z8,z5,z6]),(0,[z1,z2,z299,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z200]),(0,[z1,z2,z3,z8,z5,z6,z300])],[(0,[z1,z2,z3,z8,z5,z301,z6]),(0,[z1,z2,z21,z8,z5,z13,z6]),(0,[z84,z2,z3,z8,z5,z107,z6]),(0,[z1,z77,z3,z8,z164,z5,z6]),(0,[z1,z2,z302,z3,z8,z5,z6])],[(1,[z267,z2,z3,z8,z28,z6]),(0,[z267,z2,z3,z8,z5,z28,z6]),(0,[z1,z2,z303,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z304,z6])],[(0,[z1,z2,z3,z8,z5,z6,z305])],[(0,[z1,z306,z2,z3,z8,z5,z6]),(0,[z1,z307,z2,z3,z8,z5,z6]),(1,[z308,z1,z2,z3,z8,z6]),(0,[z309,z1,z2,z3,z8,z5,z6]),(0,[z1,z310,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z311])],[(0,[z1,z2,z3,z312,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z313]),(0,[z1,z2,z3,z8,z314,z5,z6]),(0,[z85,z1,z2,z3,z8,z5,z107]),(0,[z280,z2,z3,z8,z87,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z315])],[(0,[z2,z3,z293,z76,z8,z5,z6]),(0,[z1,z2,z316,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z164,z5,z6]),(0,[z1,z2,z317,z3,z8,z5,z6]),(0,[z270,z1,z2,z3,z8,z41,z6])],[(0,[z1,z318,z2,z3,z8,z5,z6]),(0,[z319,z1,z2,z3,z8,z5,z6]),(0,[z1,z320,z2,z3,z8,z5,z6]),(0,[z201,z145,z2,z3,z8,z5,z6]),(0,[z74,z2,z3,z293,z8,z5,z6]),(0,[z1,z2,z3,z321,z8,z5,z6]),(0,[z1,z2,z322,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z323,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z324]),(0,[z1,z2,z3,z8,z6,z325,z161]),(0,[z1,z326,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z327,z5,z6]),(0,[z1,z2,z3,z8,z328,z5,z6]),(0,[z329,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z330,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z331,z5,z6])],[(0,[z1,z65,z3,z8,z87,z5,z6]),(0,[z1,z2,z21,z8,z36,z5,z6]),(0,[z1,z2,z3,z8,z41,z5,z6]),(0,[z332,z1,z2,z3,z8,z5,z6])],[(0,[z74,z64,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z222]),(0,[z333,z1,z2,z3,z8,z5,z6]),(0,[z84,z1,z2,z3,z8,z5,z107]),(0,[z1,z2,z3,z8,z5,z6,z334]),(0,[z1,z2,z3,z8,z5,z335,z6]),(0,[z1,z2,z35,z8,z36,z5,z6])],[(0,[z1,z2,z3,z8,z336,z5,z6]),(0,[z1,z2,z3,z8,z5,z337,z6]),(0,[z1,z2,z3,z187,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z338]),(0,[z1,z2,z3,z8,z5,z6,z339]),(0,[z340,z1,z2,z3,z8,z5,z6]),(0,[z341,z1,z2,z3,z8,z5,z6]),(0,[z1,z342,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z343]),(0,[z1,z12,z77,z2,z8,z5,z6])],[(0,[z1,z23,z2,z8,z73,z5,z6]),(0,[z344,z1,z2,z3,z8,z5,z6]),(0,[z1,z345,z2,z3,z8,z5,z6])],[]],
   [[(0,[z1,z77,z2,z8,z5,z13,z6])],[(0,[z1,z346,z2,z3,z8,z5,z6]),(0,[z1,z347,z2,z3,z8,z5,z6])],[(0,[z1,z2,z293,z8,z5,z13,z6]),(0,[z201,z1,z2,z21,z8,z5,z6]),(0,[z1,z2,z3,z348,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z349,z6])],[(0,[z1,z2,z350,z3,z8,z5,z6]),(0,[z1,z2,z232,z8,z5,z6,z161]),(0,[z157,z1,z233,z2,z3,z8,z5]),(0,[z1,z351,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z187,z8,z129,z6])],[(0,[z352,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z353,z8,z5,z6]),(0,[z354,z1,z2,z3,z8,z5,z6])],[(0,[z159,z2,z3,z76,z8,z5,z6]),(0,[z355,z1,z2,z3,z8,z5,z6]),(0,[z92,z1,z247,z2,z8,z5,z6]),(0,[z1,z2,z3,z356,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z357,z6]),(0,[z358,z1,z2,z3,z8,z5,z6])],[(0,[z1,z359,z2,z3,z8,z5,z6]),(0,[z1,z233,z2,z3,z8,z5,z6])]],
   [[(0,[z64,z1,z2,z211,z8,z5,z6]),(0,[z360,z1,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z111,z5,z28,z6]),(0,[z1,z2,z3,z8,z5,z361,z6]),(0,[z1,z12,z2,z3,z8,z36,z6]),(0,[z1,z2,z3,z8,z362,z5,z6]),(0,[z1,z2,z363,z3,z8,z5,z6])],[(0,[z1,z208,z2,z21,z3,z5,z6]),(0,[z1,z2,z3,z8,z28,z129,z6]),(0,[z1,z2,z3,z8,z5,z364,z6]),(1,[z1,z365,z2,z8,z5,z6]),(0,[z1,z2,z366,z3,z8,z5,z6]),(0,[z367,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z113,z3,z8,z5,z6]),(0,[z368,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z199,z200,z6])],[(0,[z1,z2,z293,z8,z36,z5,z6]),(0,[z1,z2,z3,z8,z369,z5,z6]),(0,[z92,z1,z2,z58,z8,z5,z6])],[(0,[z1,z2,z3,z8,z370,z5,z6])],[(0,[z371,z1,z2,z3,z8,z5,z6]),(0,[z372,z1,z2,z3,z8,z5,z6]),(0,[z1,z373,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z374,z8,z5,z6])],[(0,[z1,z375,z2,z3,z8,z5,z6]),(0,[z376,z1,z2,z3,z8,z5,z6])],[(0,[z1,z377,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z107,z61])],[(0,[z1,z2,z378,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z379,z6]),(0,[z1,z2,z3,z8,z5,z380,z6]),(0,[z1,z136,z3,z8,z41,z5,z6]),(0,[z381,z1,z2,z3,z8,z5,z6]),(0,[z382,z1,z2,z3,z8,z5,z6]),(0,[z1,z383,z2,z3,z8,z5,z6]),(0,[z384,z1,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z385,z2,z3,z8,z5,z6])],[(1,[z1,z2,z198,z8,z5,z6]),(0,[z1,z386,z2,z3,z8,z5,z6])],[(0,[z387,z1,z2,z3,z8,z5,z6]),(0,[z270,z157,z1,z2,z3,z8,z6])],[(0,[z1,z2,z3,z8,z4,z5,z6])],[(0,[z1,z2,z3,z8,z5,z388,z6]),(0,[z1,z2,z3,z8,z389,z5,z6]),(0,[z1,z233,z2,z3,z8,z5,z161]),(0,[z1,z2,z8,z5,z81,z6,z161]),(0,[z92,z1,z2,z3,z73,z5,z6]),(0,[z1,z390,z2,z3,z8,z5,z59])],[(0,[z1,z2,z3,z8,z5,z5,z6]),(0,[z267,z1,z2,z3,z8,z28,z6]),(0,[z1,z2,z35,z3,z8,z36,z6]),(0,[z1,z2,z3,z8,z5,z391,z6]),(0,[z1,z2,z60,z3,z5,z6,z61]),(0,[z1,z392,z2,z3,z8,z5,z6]),(1,[z1,z2,z393,z8,z5,z6]),(0,[z1,z2,z394,z3,z8,z5,z6])],[(0,[z1,z159,z2,z3,z8,z5,z6]),(0,[z1,z395,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z396])],[(0,[z1,z397,z2,z3,z8,z5,z6]),(1,[z1,z208,z2,z3,z5,z6]),(0,[z85,z2,z3,z8,z5,z6,z115]),(0,[z1,z2,z398,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z5,z129,z6]),(0,[z1,z2,z3,z8,z5,z399,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z400,z6]),(0,[z1,z2,z3,z8,z199,z5,z277])],[(0,[z401,z1,z2,z3,z8,z5,z6]),(0,[z92,z1,z23,z2,z8,z5,z6]),(0,[z1,z102,z2,z3,z8,z200,z6]),(0,[z1,z2,z402,z3,z8,z5,z6]),(0,[z1,z128,z2,z3,z8,z129,z6]),(0,[z1,z2,z3,z403,z8,z5,z6])],[(0,[z404,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z91,z107]),(1,[z1,z2,z3,z8,z5,z324]),(0,[z1,z233,z2,z3,z8,z199,z5]),(0,[z1,z405,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z406,z5,z6]),(0,[z1,z2,z3,z8,z5,z407,z6]),(0,[z1,z2,z3,z8,z408,z5,z6])],[(0,[z1,z409,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z410,z6]),(0,[z1,z411,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z412,z5,z6]),(0,[z1,z2,z3,z8,z5,z413,z6]),(0,[z1,z2,z414,z3,z8,z5,z6]),(0,[z415,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z416,z6]),(0,[z1,z2,z3,z8,z5,z129,z6])],[(1,[z1,z2,z3,z114,z5,z6]),(0,[z1,z2,z417,z3,z8,z5,z6])],[(0,[z74,z159,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z418,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z6,z419]),(0,[z147,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z61]),(0,[z1,z2,z3,z8,z5,z6,z420]),(0,[z1,z2,z3,z8,z200,z6,z277])],[(0,[z1,z2,z3,z8,z5,z421,z6]),(0,[z0,z1,z2,z3,z284,z5,z6]),(0,[z79,z1,z2,z3,z87,z5,z6]),(0,[z1,z2,z3,z422,z8,z5,z6]),(0,[z270,z1,z2,z3,z8,z5,z156]),(0,[z1,z2,z3,z8,z5,z423,z6]),(0,[z1,z247,z2,z93,z3,z5,z6]),(0,[z1,z424,z2,z3,z8,z5,z6]),(0,[z1,z2,z425,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z426,z5,z6]),(0,[z1,z23,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z323,z87,z5,z6]),(0,[z1,z2,z3,z8,z5,z427,z6])],[(0,[z428,z1,z2,z3,z8,z5,z6]),(0,[z429,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z73,z5,z6]),(0,[z1,z2,z3,z8,z5,z430,z6])],[(0,[z159,z2,z65,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z431,z6]),(0,[z1,z2,z3,z8,z5,z432,z6])],[(0,[z433,z1,z2,z3,z8,z5,z6]),(0,[z1,z434,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z49,z6]),(0,[z1,z2,z435,z3,z8,z5,z6]),(0,[z436,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z437,z6])],[(0,[z79,z1,z159,z3,z8,z5,z6]),(0,[z438,z1,z2,z3,z8,z5,z6]),(0,[z92,z1,z2,z8,z5,z13,z6]),(0,[z1,z2,z3,z8,z5,z439,z6]),(0,[z1,z2,z3,z8,z5,z440,z6])],[(0,[z1,z441,z2,z3,z8,z5,z6]),(0,[z1,z77,z2,z58,z8,z5,z6]),(0,[z442,z1,z2,z3,z8,z5,z6]),(0,[z1,z443,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z444,z3,z8,z5,z6]),(0,[z445,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z156,z6]),(0,[z270,z1,z136,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z325]),(0,[z1,z2,z3,z8,z5,z6,z59])],[(0,[z446,z1,z2,z3,z8,z5,z6]),(0,[z447,z1,z2,z3,z8,z5,z6]),(1,[z270,z1,z3,z8,z50,z6]),(0,[z1,z2,z8,z73,z5,z190,z6]),(0,[z1,z2,z3,z8,z5,z6,z448])],[(0,[z1,z2,z3,z8,z5,z449,z6]),(0,[z1,z2,z3,z450,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z451,z6]),(0,[z1,z2,z452,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z453,z5,z6]),(1,[z1,z102,z3,z8,z41,z6]),(0,[z1,z454,z2,z3,z8,z5,z6])],[(0,[z1,z12,z2,z293,z8,z5,z6]),(0,[z1,z455,z2,z3,z8,z5,z6]),(0,[z308,z1,z2,z3,z8,z5,z6]),(0,[z456,z1,z2,z3,z8,z5,z6])],[(0,[z457,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z458,z3,z8,z5,z6])]],
   [[(1,[z1,z2,z174,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z459,z6])],[(0,[z1,z2,z3,z8,z460,z5,z6]),(0,[z1,z2,z58,z8,z36,z5,z6])],[(0,[z1,z2,z96,z422,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z461,z6]),(0,[z1,z2,z3,z8,z5,z462,z6]),(0,[z1,z2,z463,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z464,z5,z6]),(0,[z465,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z466,z6])],[(0,[z1,z2,z3,z8,z5,z467,z6]),(0,[z1,z2,z3,z8,z468,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z469]),(0,[z1,z2,z3,z8,z5,z470,z6])],[(0,[z1,z471,z2,z3,z8,z5,z6]),(0,[z1,z2,z472,z3,z8,z5,z6]),(0,[z1,z473,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z220])],[(1,[z201,z2,z21,z8,z5,z6]),(0,[z1,z2,z3,z474,z8,z5,z6])],[(0,[z79,z1,z65,z3,z8,z5,z6]),(0,[z1,z475,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z187,z4,z5,z6]),(0,[z157,z1,z2,z3,z8,z199,z6]),(0,[z1,z2,z3,z476,z8,z5,z6])]],
   [[(0,[z1,z1,z2,z3,z8,z5,z6]),(0,[z1,z477,z2,z3,z8,z5,z6]),(0,[z280,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z478,z6]),(0,[z1,z170,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z479,z6])],[(0,[z1,z2,z3,z8,z5,z6,z480]),(0,[z110,z2,z3,z8,z111,z5,z6]),(0,[z1,z2,z3,z8,z481,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z277]),(1,[z1,z390,z2,z8,z5,z13]),(0,[z1,z2,z3,z8,z5,z6,z277])],[(0,[z482,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z483,z5,z6]),(1,[z1,z2,z218,z8,z5,z6]),(0,[z1,z365,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z484,z5,z6]),(0,[z84,z1,z2,z54,z8,z5,z6]),(0,[z1,z2,z485,z3,z8,z5,z6])],[(0,[z1,z2,z486,z3,z8,z5,z6]),(1,[z1,z2,z3,z487,z5,z6]),(0,[z1,z488,z2,z3,z8,z5,z6]),(1,[z79,z1,z96,z3,z5,z6]),(0,[z1,z2,z3,z8,z489,z5,z6]),(0,[z1,z247,z2,z8,z73,z5,z6]),(0,[z1,z2,z3,z8,z5,z490,z6])],[(0,[z1,z2,z491,z3,z8,z5,z6]),(0,[z1,z492,z2,z3,z8,z5,z6]),(0,[z1,z2,z493,z3,z8,z5,z6]),(0,[z1,z2,z494,z3,z8,z5,z6]),(0,[z1,z2,z8,z73,z5,z13,z6]),(0,[z1,z2,z3,z8,z495,z5,z6]),(0,[z496,z1,z2,z3,z8,z5,z6]),(0,[z497,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z498,z3,z8,z5,z6])],[(0,[z201,z2,z21,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z115,z61]),(0,[z499,z1,z2,z3,z8,z5,z6]),(0,[z1,z128,z2,z113,z8,z5,z6])]],
   [[(0,[z1,z500,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z501,z6]),(0,[z1,z2,z502,z3,z8,z5,z6]),(0,[z1,z2,z503,z3,z8,z5,z6])],[(0,[z74,z1,z2,z3,z8,z5,z6]),(0,[z74,z1,z2,z3,z284,z5,z6]),(0,[z1,z2,z504,z3,z8,z5,z6]),(0,[z1,z505,z2,z3,z8,z5,z6]),(0,[z1,z506,z2,z3,z8,z5,z6])],[(0,[z64,z2,z3,z76,z8,z5,z6]),(0,[z1,z2,z507,z3,z8,z5,z6]),(0,[z1,z80,z2,z96,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z508,z6])],[(1,[z145,z2,z293,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z509]),(0,[z1,z2,z60,z3,z8,z5,z61]),(1,[z1,z2,z394,z8,z5,z6]),(1,[z1,z2,z3,z8,z199,z200])],[(0,[z1,z12,z2,z3,z8,z5,z6]),(0,[z1,z2,z510,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z511,z6]),(0,[z1,z2,z3,z8,z512,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z513]),(0,[z1,z2,z3,z8,z199,z5,z6])],[(1,[z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z21,z3,z487,z5,z6]),(0,[z1,z2,z3,z8,z514,z5,z6]),(0,[z79,z1,z2,z3,z8,z5,z6]),(0,[z270,z1,z2,z3,z8,z50,z6]),(0,[z1,z136,z3,z8,z5,z6,z161]),(1,[z170,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z515]),(0,[z1,z2,z60,z3,z8,z5,z6]),(0,[z1,z142,z2,z198,z8,z5,z6])],[(0,[z1,z2,z3,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z516,z5,z6]),(0,[z1,z2,z3,z8,z487,z5,z6]),(0,[z1,z2,z3,z517,z8,z5,z6]),(0,[z1,z518,z2,z3,z8,z5,z6]),(1,[z147,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z36,z5,z190,z6]),(0,[z1,z2,z3,z8,z5,z519,z6]),(0,[z1,z2,z393,z3,z8,z5,z6])]],
   [[(0,[z520,z1,z2,z3,z8,z5,z6]),(0,[z521,z1,z2,z3,z8,z5,z6]),(1,[z2,z3,z8,z323,z5,z6])],[(0,[z74,z1,z2,z3,z8,z314,z6]),(0,[z1,z522,z2,z3,z8,z5,z6]),(0,[z523,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z93,z8,z73,z5,z6])],[(0,[z1,z2,z3,z8,z5,z524,z6]),(0,[z1,z525,z2,z3,z8,z5,z6]),(0,[z1,z142,z2,z393,z8,z5,z6]),(0,[z1,z2,z394,z8,z5,z6,z277])],[(0,[z1,z77,z2,z8,z36,z5,z6]),(0,[z1,z2,z58,z3,z8,z5,z59]),(0,[z1,z2,z526,z3,z8,z5,z6])],[(0,[z527,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z528])],[(0,[z1,z2,z3,z8,z529,z5,z6]),(0,[z74,z1,z2,z3,z8,z421,z6]),(0,[z1,z2,z3,z8,z530,z5,z6])],[(1,[z1,z2,z3,z8,z314,z6]),(0,[z267,z110,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z111,z5,z6]),(0,[z1,z2,z3,z531,z8,z5,z6]),(0,[z157,z1,z2,z3,z8,z5,z200])],[(0,[z1,z2,z3,z8,z5,z190,z6]),(0,[z1,z142,z2,z3,z8,z5,z91]),(1,[z1,z342,z3,z8,z5,z6])]],
   [[(0,[z532,z1,z2,z3,z8,z5,z6]),(0,[z74,z1,z2,z533,z8,z5,z6]),(0,[z1,z2,z3,z8,z534,z5,z6]),(1,[z1,z144,z2,z8,z5,z6]),(1,[z1,z2,z238,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z535,z6]),(0,[z1,z390,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z238,z8,z5,z6])],[(1,[z1,z2,z3,z8,z421,z6]),(0,[z1,z2,z536,z3,z8,z5,z6]),(0,[z1,z537,z2,z3,z8,z5,z6])],[(0,[z538,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z539,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z540,z6]),(0,[z1,z2,z3,z8,z5,z107,z6]),(1,[z1,z142,z2,z3,z5,z91])],[(1,[z1,z2,z533,z8,z5,z6]),(0,[z1,z102,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z533,z8,z5,z6]),(1,[z1,z12,z2,z8,z190,z6]),(0,[z1,z2,z3,z187,z8,z4,z6])],[(0,[z1,z541,z2,z3,z8,z5,z6]),(0,[z1,z542,z2,z3,z8,z5,z6]),(1,[z92,z1,z247,z2,z5,z6])]],
   [[(0,[z1,z2,z24,z293,z8,z5,z6]),(0,[z1,z2,z96,z3,z8,z5,z6]),(0,[z1,z543,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z544,z8,z5,z6])],[(0,[z1,z2,z3,z8,z545,z5,z6]),(0,[z546,z1,z2,z3,z8,z5,z6]),(0,[z1,z547,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z548,z8,z5,z6]),(0,[z1,z2,z3,z8,z549,z5,z6]),(0,[z550,z1,z2,z3,z8,z5,z6])],[(0,[z2,z21,z3,z293,z8,z5,z6]),(0,[z1,z2,z551,z3,z8,z5,z6]),(0,[z1,z2,z8,z36,z5,z13,z6])],[(0,[z1,z2,z3,z552,z8,z5,z6]),(0,[z1,z2,z553,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z554,z6]),(0,[z1,z2,z555,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z556,z5,z6]),(0,[z1,z2,z557,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z558,z6])],[(0,[z559,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z8,z5,z560,z50,z6]),(0,[z1,z561,z2,z3,z8,z5,z6]),(0,[z562,z1,z2,z3,z8,z5,z6]),(0,[z1,z563,z2,z3,z8,z5,z6])],[(0,[z1,z564,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z565,z8,z5,z6]),(0,[z1,z2,z3,z8,z566,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z567])],[(0,[z1,z2,z568,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z569,z6]),(0,[z1,z570,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z571,z6]),(0,[z1,z247,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z572,z5,z6]),(0,[z1,z2,z3,z8,z5,z573,z6])],[(0,[z64,z2,z65,z3,z8,z5,z6]),(0,[z1,z2,z574,z3,z8,z5,z6])],[(0,[z1,z2,z575,z3,z8,z5,z6]),(0,[z1,z2,z576,z3,z8,z5,z6]),(0,[z270,z1,z3,z8,z5,z42,z6]),(0,[z1,z2,z577,z3,z8,z5,z6]),(0,[z1,z390,z2,z3,z8,z5,z13]),(1,[z1,z2,z8,z5,z6,z420])],[(0,[z1,z2,z119,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z4,z28,z6]),(1,[z1,z2,z422,z8,z5,z6]),(0,[z1,z2,z3,z8,z578,z5,z6]),(0,[z1,z2,z579,z3,z8,z5,z6])],[(0,[z580,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z2,z3,z8,z5,z6]),(0,[z1,z23,z2,z58,z8,z5,z6]),(0,[z1,z102,z3,z8,z41,z5,z6]),(0,[z1,z2,z3,z581,z8,z5,z6]),(0,[z1,z2,z58,z8,z73,z5,z6])],[(0,[z1,z582,z2,z3,z8,z5,z6]),(0,[z1,z102,z2,z3,z8,z41,z6]),(0,[z1,z2,z3,z8,z5,z583,z6]),(0,[z1,z584,z2,z3,z8,z5,z6])],[(0,[z585,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z6]),(1,[z1,z127,z2,z3,z8,z5]),(0,[z1,z2,z586,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z42,z6]),(0,[z1,z2,z3,z8,z5,z587,z6])],[(1,[z1,z2,z588,z8,z5,z6]),(0,[z1,z2,z3,z8,z589,z5,z6]),(0,[z270,z1,z2,z3,z8,z200,z6]),(0,[z92,z1,z2,z35,z8,z5,z6])]],
   [[(0,[z590,z1,z2,z3,z8,z5,z6]),(0,[z145,z1,z2,z293,z8,z5,z6]),(0,[z201,z2,z3,z76,z8,z5,z6]),(0,[z1,z365,z2,z8,z5,z50,z6]),(0,[z1,z2,z3,z8,z591,z5,z6]),(0,[z1,z2,z3,z8,z5,z592,z6])],[(0,[z593,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z594,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z595,z6])],[(0,[z74,z1,z128,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z596,z6])],[(0,[z1,z597,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z598,z5,z6]),(0,[z1,z2,z3,z8,z114,z5,z6]),(0,[z1,z390,z2,z8,z5,z13,z6]),(0,[z1,z128,z2,z3,z8,z4,z6])],[(0,[z599,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z93,z3,z8,z5,z6]),(0,[z1,z2,z600,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z601,z6])],[(0,[z1,z75,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z602,z5,z6]),(0,[z1,z2,z24,z3,z8,z5,z6]),(1,[z1,z2,z232,z8,z5,z6]),(0,[z1,z2,z3,z8,z603,z5,z6])],[(0,[z1,z2,z3,z8,z5,z6,z604]),(0,[z92,z1,z2,z293,z8,z5,z6]),(0,[z1,z2,z21,z8,z73,z5,z6]),(0,[z1,z605,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z606,z5,z6]),(0,[z1,z2,z3,z8,z5,z81,z6]),(0,[z1,z2,z3,z8,z607,z5,z6])]],
   [[(1,[z0,z2,z3,z76,z5,z6]),(0,[z1,z2,z35,z8,z73,z5,z6])],[(0,[z1,z608,z2,z3,z8,z5,z6]),(0,[z1,z609,z2,z3,z8,z5,z6]),(0,[z1,z24,z3,z8,z164,z5,z6]),(0,[z610,z1,z2,z3,z8,z5,z6]),(0,[z270,z1,z3,z8,z5,z50,z6])],[(0,[z1,z2,z58,z293,z8,z5,z6]),(0,[z1,z611,z2,z3,z8,z5,z6]),(0,[z1,z612,z2,z3,z8,z5,z6])],[(0,[z110,z1,z2,z3,z8,z28,z6]),(0,[z1,z136,z233,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z161])],[(0,[z1,z613,z2,z3,z8,z5,z6]),(0,[z1,z14,z2,z3,z5,z28,z6]),(0,[z1,z2,z3,z8,z614,z5,z6])],[(0,[z1,z2,z3,z8,z4,z111,z6]),(0,[z1,z2,z3,z8,z5,z50,z6]),(1,[z1,z2,z8,z5,z560,z6]),(0,[z1,z2,z3,z8,z5,z6,z615])],[(0,[z616,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z617]),(0,[z1,z2,z3,z8,z5,z560,z6])],[(0,[z145,z2,z3,z293,z8,z5,z6]),(0,[z618,z1,z2,z3,z8,z5,z6]),(0,[z0,z1,z247,z2,z3,z5,z6]),(0,[z270,z1,z2,z3,z8,z5,z324])]],
   [[(0,[z1,z2,z588,z3,z8,z5,z6]),(0,[z74,z1,z2,z184,z8,z5,z6]),(0,[z1,z144,z2,z96,z8,z5,z6]),(0,[z1,z142,z2,z3,z8,z5,z61])],[(0,[z1,z2,z3,z619,z8,z5,z6])],[(0,[z1,z2,z620,z3,z8,z5,z6]),(0,[z270,z1,z102,z3,z8,z5,z6]),(0,[z1,z621,z2,z3,z8,z5,z6])],[(0,[z622,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z623,z3,z8,z5,z6])],[(0,[z1,z80,z3,z8,z87,z5,z6]),(0,[z624,z1,z2,z3,z8,z5,z6])],[(1,[z1,z2,z184,z8,z5,z6]),(0,[z74,z1,z2,z3,z4,z5,z6])],[(0,[z625,z1,z2,z3,z8,z5,z6]),(0,[z1,z77,z2,z8,z73,z5,z6]),(0,[z1,z12,z2,z3,z8,z190,z6]),(0,[z626,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z627])],[(0,[z1,z2,z3,z8,z628,z5,z6]),(1,[z85,z2,z3,z8,z5,z115]),(0,[z1,z2,z3,z8,z5,z6,z115]),(0,[z1,z2,z8,z5,z13,z6,z59]),(0,[z629,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z630])]],
   [[(0,[z1,z2,z293,z8,z73,z5,z6]),(0,[z1,z23,z2,z8,z5,z13,z6]),(0,[z1,z2,z3,z8,z5,z631,z6])],[(0,[z92,z1,z77,z2,z8,z5,z6]),(0,[z1,z2,z3,z632,z8,z5,z6])],[(0,[z267,z1,z2,z3,z8,z5,z6])],[(1,[z1,z2,z196,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z633]),(0,[z1,z77,z2,z24,z8,z5,z6]),(0,[z1,z233,z3,z8,z5,z42,z6]),(0,[z1,z2,z3,z8,z634,z5,z6])],[(0,[z635,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z636,z6]),(0,[z157,z1,z102,z2,z3,z8,z6]),(0,[z637,z1,z2,z3,z8,z5,z6])],[(0,[z638,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z639,z8,z5,z6]),(0,[z1,z2,z21,z8,z164,z5,z6]),(0,[z110,z1,z2,z3,z8,z111,z6]),(0,[z640,z1,z2,z3,z8,z5,z6]),(0,[z1,z127,z2,z3,z8,z5,z50]),(0,[z1,z2,z3,z8,z641,z5,z6])],[(0,[z1,z12,z2,z58,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z642,z6]),(0,[z1,z2,z3,z8,z643,z5,z6]),(0,[z1,z644,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z645,z5,z6]),(0,[z1,z2,z3,z8,z5,z646,z6])]],
   [[(0,[z1,z2,z3,z8,z647,z5,z6]),(0,[z1,z2,z3,z648,z8,z5,z6]),(0,[z1,z23,z2,z8,z36,z5,z6]),(0,[z1,z2,z58,z3,z8,z5,z6]),(0,[z1,z2,z649,z3,z8,z5,z6]),(1,[z157,z1,z2,z3,z8,z277])],[(0,[z1,z2,z3,z8,z5,z161,z277]),(1,[z1,z233,z3,z8,z5,z42])],[(0,[z1,z2,z3,z8,z650,z5,z6]),(0,[z1,z2,z3,z651,z8,z5,z6]),(0,[z1,z652,z2,z3,z8,z5,z6]),(0,[z1,z653,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z220,z277])],[(0,[z201,z1,z2,z293,z8,z5,z6]),(0,[z1,z2,z654,z3,z8,z5,z6]),(0,[z655,z1,z2,z3,z8,z5,z6]),(0,[z656,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z657]),(0,[z1,z658,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z659,z5,z6]),(0,[z1,z660,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z661,z6]),(0,[z1,z2,z3,z8,z5,z662,z6]),(0,[z1,z2,z3,z8,z5,z6,z663]),(0,[z308,z1,z2,z3,z8,z6,z161]),(0,[z1,z2,z8,z5,z6,z420,z277])],[(0,[z1,z2,z664,z3,z8,z5,z6]),(0,[z74,z1,z2,z3,z73,z5,z6]),(0,[z665,z1,z2,z3,z8,z5,z6]),(0,[z1,z136,z2,z3,z8,z5,z42]),(0,[z1,z2,z3,z8,z5,z666,z6])],[(0,[z74,z1,z2,z3,z76,z5,z6]),(0,[z0,z1,z128,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z667,z5,z6]),(1,[z1,z2,z58,z8,z5,z59]),(0,[z1,z342,z3,z8,z5,z6,z277])],[(0,[z1,z80,z2,z3,z87,z5,z6]),(0,[z1,z2,z668,z3,z8,z5,z6]),(0,[z1,z12,z2,z8,z5,z190,z6]),(0,[z1,z2,z669,z3,z8,z5,z6])]],
   [[(0,[z670,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z671,z6])],[(0,[z1,z2,z3,z211,z8,z5,z6]),(1,[z74,z2,z3,z284,z5,z6]),(1,[z1,z23,z24,z8,z5,z6])],[(0,[z1,z672,z2,z3,z8,z5,z6]),(0,[z1,z673,z2,z3,z8,z5,z6])],[(0,[z1,z2,z21,z3,z8,z5,z6]),(0,[z674,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z675,z5,z6]),(0,[z1,z390,z2,z58,z8,z5,z6])],[(0,[z1,z2,z3,z8,z8,z5,z6]),(0,[z1,z2,z3,z8,z284,z5,z6]),(0,[z1,z77,z2,z8,z164,z5,z6]),(0,[z1,z2,z35,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z676,z6]),(0,[z1,z2,z677,z3,z8,z5,z6]),(0,[z1,z678,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z679,z6])],[(1,[z158,z159,z3,z8,z5,z6]),(0,[z680,z1,z2,z3,z8,z5,z6]),(0,[z1,z12,z23,z2,z8,z5,z6]),(0,[z1,z681,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z682,z6]),(0,[z1,z2,z3,z8,z5,z6,z683])],[(0,[z1,z684,z2,z3,z8,z5,z6]),(0,[z685,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z293,z8,z164,z5,z6]),(0,[z1,z2,z3,z8,z5,z686,z6])],[(0,[z74,z1,z247,z2,z3,z5,z6]),(0,[z1,z687,z2,z3,z8,z5,z6]),(0,[z157,z1,z2,z3,z8,z5,z277])]],
   [[(0,[z688,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z689,z6]),(0,[z690,z1,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z111,z129,z6]),(0,[z1,z2,z3,z8,z5,z6,z691])],[(0,[z1,z2,z3,z692,z8,z5,z6]),(0,[z1,z128,z2,z3,z5,z129,z6])],[(0,[z1,z2,z3,z8,z693,z5,z6])],[(0,[z64,z1,z2,z588,z8,z5,z6]),(0,[z1,z2,z3,z8,z694,z5,z6]),(0,[z1,z2,z3,z8,z5,z695,z6]),(0,[z696,z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z697]),(0,[z1,z2,z3,z8,z5,z698,z6]),(0,[z699,z1,z2,z3,z8,z5,z6])],[(0,[z1,z700,z2,z3,z8,z5,z6]),(0,[z74,z2,z3,z8,z284,z5,z6]),(0,[z1,z2,z3,z8,z701,z5,z6]),(1,[z1,z2,z3,z8,z6,z325]),(0,[z702,z1,z2,z3,z8,z5,z6])],[(0,[z64,z1,z159,z3,z8,z5,z6]),(0,[z1,z703,z2,z3,z8,z5,z6]),(0,[z1,z2,z704,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z705,z5,z6]),(0,[z1,z2,z3,z8,z5,z6,z706])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z8,z707,z6]),(0,[z1,z2,z3,z487,z5,z6]),(0,[z1,z3,z8,z5,z708,z6]),(0,[z1,z2,z3,z8,z709,z6]),(0,[z79,z1,z96,z3,z5,z6]),(0,[z1,z2,z3,z8,z710,z6])],[(0,[z1,z2,z3,z8,z5,z711]),(0,[z1,z2,z8,z5,z712,z6]),(0,[z1,z505,z2,z8,z5,z13]),(0,[z147,z92,z247,z2,z5,z6]),(0,[z1,z2,z3,z713,z5,z6])],[(0,[z1,z2,z714,z8,z5,z6]),(0,[z1,z247,z2,z184,z5,z6]),(0,[z2,z3,z715,z284,z5,z6]),(0,[z1,z2,z3,z8,z5,z716]),(0,[z1,z2,z3,z8,z717,z6]),(0,[z718,z2,z3,z8,z5,z6]),(0,[z1,z719,z3,z8,z5,z6]),(0,[z1,z2,z720,z8,z5,z6]),(0,[z1,z2,z60,z3,z5,z721])],[(0,[z367,z2,z293,z8,z5,z6]),(0,[z1,z128,z2,z3,z421,z6]),(0,[z1,z2,z555,z3,z5,z61]),(0,[z1,z2,z3,z8,z5,z722]),(0,[z1,z390,z2,z8,z5,z723])]],
   [[(0,[z1,z724,z2,z8,z5,z6]),(0,[z1,z2,z184,z8,z5,z6]),(0,[z1,z2,z3,z8,z725,z6]),(0,[z1,z2,z8,z5,z726,z6]),(0,[z1,z2,z93,z73,z5,z6]),(0,[z1,z727,z3,z8,z5,z6])],[(0,[z1,z2,z728,z8,z5,z6]),(0,[z1,z2,z729,z8,z5,z6]),(0,[z147,z2,z184,z8,z5,z6]),(0,[z730,z2,z3,z8,z5,z6]),(1,[z1,z2,z8,z5,z723])],[(0,[z1,z2,z3,z8,z731,z6]),(0,[z1,z2,z3,z8,z5,z732]),(0,[z1,z75,z3,z8,z421,z6]),(0,[z1,z75,z3,z8,z5,z130]),(0,[z1,z2,z3,z8,z733,z6]),(0,[z734,z2,z3,z8,z5,z6])],[(0,[z1,z2,z735,z3,z5,z6]),(0,[z1,z2,z3,z8,z736,z6]),(1,[z2,z3,z715,z5,z6]),(0,[z1,z2,z737,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z738]),(0,[z739,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z156]),(0,[z1,z2,z8,z5,z740,z6]),(0,[z1,z136,z8,z5,z81,z161])],[(0,[z1,z77,z485,z8,z5,z6]),(0,[z741,z2,z3,z8,z5,z6])],[],[(0,[z332,z2,z3,z8,z28,z6]),(0,[z1,z2,z8,z5,z6,z742]),(0,[z1,z2,z3,z8,z5,z743]),(0,[z1,z3,z8,z5,z42,z31])]],
   [[(0,[z1,z2,z744,z8,z5,z6]),(0,[z2,z3,z8,z323,z5,z6]),(0,[z1,z2,z3,z8,z745,z6]),(0,[z74,z2,z184,z284,z5,z6]),(0,[z1,z2,z746,z8,z5,z6]),(0,[z308,z1,z2,z3,z8,z324]),(0,[z1,z127,z102,z2,z3,z8]),(0,[z1,z2,z302,z73,z5,z6])],[(0,[z1,z2,z3,z8,z747,z6]),(0,[z158,z748,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z749]),(0,[z1,z2,z750,z8,z5,z6]),(0,[z267,z2,z3,z114,z28,z6]),(0,[z110,z2,z3,z8,z751,z6]),(0,[z2,z3,z8,z5,z6,z752]),(0,[z1,z753,z2,z8,z5,z6]),(0,[z1,z2,z3,z754,z5,z6]),(0,[z1,z102,z3,z8,z6,z630]),(0,[z1,z2,z16,z73,z5,z6]),(0,[z1,z755,z3,z8,z5,z6]),(0,[z1,z2,z8,z36,z6,z300])],[(0,[z1,z756,z3,z8,z5,z6]),(0,[z757,z2,z3,z8,z5,z6]),(0,[z1,z2,z758,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z759]),(0,[z270,z1,z3,z8,z212,z6]),(0,[z170,z2,z58,z8,z5,z6]),(0,[z157,z1,z2,z3,z8,z277])]],
   [[(0,[z456,z2,z293,z8,z5,z6]),(0,[z1,z760,z3,z8,z5,z6]),(0,[z1,z2,z3,z4,z695,z6]),(0,[z1,z2,z8,z5,z6,z761]),(0,[z1,z233,z3,z8,z5,z42]),(0,[z308,z1,z2,z8,z81,z6]),(0,[z1,z342,z394,z8,z5,z6])],[(0,[z1,z2,z3,z8,z762,z6]),(0,[z74,z119,z3,z284,z5,z6]),(0,[z1,z2,z3,z8,z5,z763]),(0,[z1,z2,z8,z5,z13,z186]),(0,[z764,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z765]),(0,[z1,z766,z3,z8,z5,z6]),(0,[z1,z767,z2,z8,z5,z6])],[(0,[z1,z768,z3,z8,z5,z6]),(0,[z46,z2,z3,z8,z5,z115]),(0,[z769,z2,z3,z8,z5,z6]),(0,[z1,z12,z2,z8,z519,z6])],[(0,[z1,z2,z3,z8,z5,z770]),(0,[z1,z2,z498,z73,z5,z6]),(0,[z201,z2,z184,z8,z5,z6]),(0,[z84,z2,z3,z8,z5,z771]),(1,[z1,z772,z8,z5,z6]),(0,[z1,z342,z3,z8,z5,z6]),(0,[z157,z1,z169,z2,z3,z8]),(0,[z1,z687,z2,z8,z190,z6]),(0,[z1,z2,z8,z5,z6,z773])]],
   [[(0,[z1,z774,z3,z8,z5,z6]),(0,[z74,z1,z2,z238,z5,z6]),(0,[z270,z1,z127,z3,z8,z6]),(0,[z270,z1,z3,z8,z407,z6])],[(0,[z1,z2,z3,z8,z775,z6]),(0,[z1,z2,z3,z8,z776,z6]),(0,[z1,z2,z3,z4,z421,z6]),(0,[z1,z2,z777,z8,z5,z6]),(0,[z1,z3,z8,z41,z6,z657]),(0,[z1,z2,z778,z8,z5,z6]),(0,[z1,z142,z2,z3,z5,z721])],[(0,[z1,z2,z3,z8,z779,z6]),(0,[z1,z2,z3,z8,z5,z780]),(0,[z1,z781,z3,z8,z5,z6])],[(0,[z1,z2,z211,z8,z5,z6]),(0,[z1,z782,z2,z3,z8,z6]),(0,[z783,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z784,z5,z6]),(0,[z74,z2,z3,z284,z5,z6]),(0,[z1,z2,z3,z8,z5,z785]),(0,[z786,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z787]),(0,[z1,z142,z2,z3,z5,z91]),(0,[z1,z2,z3,z8,z5,z721])],[(0,[z1,z2,z788,z8,z5,z6]),(0,[z1,z789,z3,z8,z5,z6]),(0,[z1,z790,z2,z3,z5,z6]),(0,[z1,z2,z791,z8,z5,z6]),(0,[z1,z2,z8,z5,z792,z6]),(0,[z157,z1,z2,z3,z8,z793])],[(0,[z1,z794,z3,z8,z5,z6]),(0,[z1,z2,z3,z715,z5,z6]),(0,[z2,z3,z8,z795,z5,z6]),(0,[z147,z2,z3,z73,z5,z6]),(0,[z1,z12,z2,z8,z190,z6]),(0,[z796,z2,z3,z8,z5,z6]),(0,[z1,z2,z797,z8,z5,z6])],[(0,[z1,z2,z798,z8,z5,z6]),(0,[z1,z2,z3,z8,z799,z6]),(0,[z1,z2,z800,z8,z5,z6])]],
   [[(0,[z1,z801,z2,z8,z5,z6]),(0,[z1,z2,z58,z8,z5,z305]),(0,[z1,z2,z802,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z803]),(0,[z1,z136,z3,z8,z5,z161]),(0,[z308,z1,z233,z2,z3,z8]),(0,[z1,z233,z3,z8,z5,z804]),(0,[z1,z128,z2,z3,z805,z6]),(0,[z1,z2,z3,z8,z199,z793])],[(0,[z1,z748,z3,z8,z5,z6]),(0,[z1,z806,z3,z8,z5,z6]),(0,[z1,z807,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z314,z130]),(0,[z2,z3,z76,z715,z5,z6]),(0,[z1,z2,z3,z5,z721,z61])],[(0,[z1,z608,z8,z164,z5,z6]),(0,[z2,z3,z8,z5,z751,z6]),(0,[z1,z3,z8,z808,z50,z6]),(0,[z1,z809,z2,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z810])]],
   [[(0,[z74,z2,z3,z694,z5,z6]),(0,[z1,z2,z811,z8,z5,z6]),(0,[z1,z2,z812,z3,z8,z5]),(0,[z1,z24,z772,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z813]),(0,[z308,z1,z136,z3,z8,z6]),(0,[z308,z1,z3,z8,z42,z6]),(0,[z1,z342,z3,z8,z5,z161]),(0,[z1,z2,z814,z8,z5,z6])],[(0,[z815,z1,z2,z3,z8,z6]),(0,[z1,z2,z8,z5,z816,z6]),(0,[z2,z3,z8,z5,z771,z115]),(0,[z80,z3,z323,z87,z5,z6]),(1,[z1,z3,z8,z5,z804]),(0,[z157,z1,z2,z8,z420,z277])],[(0,[z2,z211,z76,z8,z5,z6]),(0,[z1,z2,z3,z8,z421,z130]),(0,[z110,z2,z174,z8,z111,z6]),(0,[z1,z2,z3,z8,z200,z324]),(0,[z1,z2,z817,z8,z5,z6])],[(0,[z1,z2,z3,z818,z5,z6]),(0,[z1,z2,z819,z8,z5,z6]),(0,[z2,z3,z8,z5,z820,z6]),(0,[z1,z2,z8,z5,z723,z59])]],
   [[(0,[z1,z2,z3,z8,z5,z821]),(0,[z159,z119,z3,z8,z5,z6]),(0,[z2,z3,z76,z38,z5,z6]),(0,[z1,z2,z822,z3,z5,z6]),(0,[z1,z441,z24,z8,z5,z6]),(0,[z2,z3,z8,z823,z5,z6]),(0,[z147,z247,z2,z3,z5,z6]),(0,[z824,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z825]),(0,[z1,z2,z3,z826,z5,z6]),(0,[z1,z14,z2,z3,z5,z6]),(0,[z1,z2,z3,z114,z5,z6]),(0,[z1,z2,z3,z827,z5,z6]),(0,[z1,z2,z3,z8,z828,z6])],[(0,[z748,z65,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z314,z222]),(0,[z829,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z804,z161]),(0,[z1,z3,z8,z5,z42,z804]),(0,[z1,z2,z8,z5,z6,z420]),(0,[z1,z2,z58,z8,z5,z723]),(0,[z1,z2,z3,z187,z4,z6]),(0,[z1,z342,z3,z8,z199,z5])],[(0,[z92,z1,z208,z2,z5,z6]),(0,[z74,z2,z533,z284,z5,z6]),(0,[z1,z2,z422,z8,z5,z6]),(0,[z830,z2,z3,z8,z5,z6]),(0,[z831,z2,z3,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z832,z5,z6]),(0,[z382,z2,z21,z8,z5,z6]),(0,[z1,z2,z833,z8,z5,z6]),(0,[z1,z834,z3,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z835]),(0,[z1,z2,z3,z8,z5,z836]),(0,[z1,z2,z837,z8,z5,z6]),(0,[z1,z838,z3,z8,z5,z6]),(0,[z1,z394,z8,z5,z6,z220])],[(0,[z1,z2,z3,z8,z421,z222]),(0,[z1,z127,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z793]),(0,[z1,z2,z839,z8,z5,z6])],[(0,[z1,z2,z588,z8,z5,z6]),(0,[z1,z2,z840,z8,z5,z6]),(0,[z1,z2,z841,z8,z5,z6]),(0,[z85,z2,z3,z8,z5,z771]),(0,[z1,z77,z772,z8,z5,z6]),(0,[z270,z1,z127,z2,z3,z8]),(0,[z1,z127,z365,z2,z8,z5]),(0,[z170,z2,z8,z5,z13,z6])]],
   [[(0,[z110,z2,z218,z8,z111,z6]),(0,[z1,z842,z3,z8,z5,z6]),(0,[z1,z2,z843,z8,z5,z6]),(0,[z1,z2,z3,z844,z5,z6]),(0,[z1,z2,z845,z8,z5,z6]),(0,[z1,z846,z2,z8,z5,z6]),(0,[z270,z1,z3,z8,z42,z200]),(0,[z270,z1,z117,z3,z8,z6]),(0,[z1,z847,z3,z8,z5,z6]),(0,[z157,z1,z342,z3,z8,z6])],[(0,[z1,z2,z3,z848,z8,z6]),(0,[z1,z849,z2,z8,z5,z6]),(0,[z308,z1,z136,z3,z8,z161])],[(0,[z74,z644,z2,z3,z5,z6])],[(0,[z1,z2,z3,z850,z5,z6]),(0,[z0,z2,z3,z418,z5,z6]),(1,[z2,z3,z8,z751,z6]),(0,[z1,z77,z692,z8,z5,z6]),(0,[z1,z2,z3,z4,z805,z6])]],
   [[(0,[z1,z2,z3,z8,z851,z6]),(0,[z2,z21,z852,z8,z5,z6]),(0,[z1,z853,z2,z73,z5,z6]),(0,[z1,z2,z3,z8,z6,z854]),(0,[z1,z2,z35,z8,z36,z6])],[(0,[z1,z75,z184,z8,z5,z6]),(0,[z1,z14,z2,z3,z421,z6]),(0,[z1,z2,z3,z8,z855,z6]),(0,[z1,z2,z856,z8,z5,z6]),(0,[z1,z2,z857,z3,z8,z5]),(0,[z1,z2,z858,z8,z5,z6]),(0,[z1,z2,z859,z8,z5,z6]),(0,[z270,z1,z3,z8,z50,z6]),(0,[z1,z2,z8,z36,z792,z6])],[(0,[z1,z860,z3,z8,z5,z6]),(0,[z1,z2,z3,z861,z5,z6]),(0,[z1,z2,z3,z8,z5,z862]),(0,[z1,z3,z8,z5,z6,z863]),(0,[z1,z2,z232,z8,z5,z6]),(0,[z864,z2,z3,z8,z5,z6]),(0,[z308,z1,z2,z232,z8,z6]),(0,[z1,z128,z2,z113,z129,z6]),(0,[z157,z1,z3,z8,z220,z277])],[(0,[z1,z2,z54,z8,z5,z6]),(0,[z1,z2,z3,z8,z865,z6]),(0,[z866,z2,z3,z8,z5,z6])]],
   [[(0,[z207,z2,z3,z76,z5,z6]),(0,[z0,z2,z3,z76,z5,z6]),(0,[z0,z2,z3,z715,z5,z6]),(0,[z1,z772,z8,z164,z5,z6]),(0,[z867,z2,z3,z8,z5,z6]),(1,[z1,z3,z8,z808,z6]),(0,[z270,z1,z127,z3,z8,z5]),(0,[z868,z2,z3,z8,z5,z6]),(0,[z1,z128,z2,z238,z129,z6])],[(0,[z1,z2,z869,z3,z5,z6]),(0,[z870,z2,z3,z8,z5,z6]),(0,[z871,z2,z3,z8,z5,z6]),(0,[z1,z2,z872,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z873]),(0,[z874,z2,z3,z8,z5,z6]),(0,[z2,z3,z8,z5,z875,z6]),(0,[z1,z2,z876,z3,z5,z6]),(0,[z1,z2,z8,z792,z190,z6]),(0,[z1,z2,z3,z5,z91,z721])],[(0,[z1,z2,z877,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z878]),(0,[z92,z1,z2,z620,z5,z6]),(0,[z1,z2,z3,z8,z5,z879]),(0,[z308,z1,z136,z2,z3,z8])]],
   [[(0,[z880,z2,z3,z8,z5,z6]),(0,[z308,z1,z2,z3,z8,z6])],[(0,[z1,z2,z881,z8,z5,z6]),(0,[z2,z3,z8,z715,z5,z6]),(0,[z1,z2,z3,z8,z5,z882]),(0,[z883,z2,z3,z8,z5,z6]),(0,[z1,z884,z2,z8,z5,z6]),(0,[z1,z142,z2,z393,z5,z91])],[(0,[z1,z853,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z885])],[(1,[z2,z3,z8,z5,z771]),(0,[z1,z2,z886,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z887,z6]),(0,[z1,z888,z2,z8,z5,z6]),(0,[z74,z2,z3,z336,z5,z6]),(0,[z1,z2,z3,z8,z5,z889]),(0,[z92,z170,z247,z2,z5,z6]),(0,[z1,z890,z2,z8,z5,z6])],[(0,[z1,z75,z3,z8,z5,z6]),(0,[z1,z2,z3,z891,z5,z6]),(0,[z201,z2,z21,z8,z5,z6]),(0,[z1,z2,z892,z8,z5,z6]),(0,[z1,z2,z893,z8,z5,z6]),(0,[z1,z2,z3,z8,z808,z6]),(0,[z1,z2,z894,z8,z5,z6])],[(0,[z159,z3,z8,z483,z5,z6]),(0,[z550,z2,z293,z8,z5,z6]),(0,[z1,z2,z895,z8,z5,z6]),(0,[z1,z80,z896,z3,z5,z6])],[(0,[z159,z748,z3,z8,z5,z6]),(0,[z1,z2,z897,z8,z5,z6])]],
   [[(0,[z1,z2,z898,z8,z5,z6]),(0,[z308,z1,z136,z3,z8,z5])],[(0,[z64,z65,z211,z8,z5,z6]),(0,[z1,z2,z899,z8,z5,z6]),(0,[z1,z14,z2,z895,z5,z6]),(0,[z1,z2,z900,z3,z8,z5]),(0,[z1,z96,z896,z3,z5,z6]),(0,[z270,z1,z3,z8,z808,z6]),(0,[z1,z2,z8,z5,z901,z6])],[(0,[z1,z2,z902,z8,z5,z6]),(0,[z1,z2,z3,z903,z5,z6]),(1,[z2,z852,z8,z5,z6]),(0,[z165,z2,z21,z8,z5,z6]),(0,[z1,z2,z58,z487,z5,z6]),(0,[z1,z2,z3,z8,z751,z6]),(0,[z1,z772,z3,z8,z5,z6]),(0,[z270,z1,z3,z8,z50,z324]),(0,[z308,z1,z2,z3,z8,z200]),(0,[z1,z2,z8,z5,z13,z723]),(0,[z1,z128,z2,z3,z129,z6])],[(0,[z1,z2,z904,z3,z5,z6]),(0,[z1,z905,z3,z8,z5,z6]),(0,[z1,z2,z906,z8,z5,z6]),(0,[z1,z2,z178,z73,z5,z6]),(0,[z1,z14,z2,z3,z4,z6]),(0,[z1,z2,z907,z8,z5,z6]),(0,[z85,z2,z3,z8,z5,z115]),(0,[z1,z23,z772,z8,z5,z6]),(0,[z79,z1,z96,z422,z5,z6]),(0,[z1,z2,z908,z8,z5,z6]),(0,[z1,z909,z2,z3,z8,z5]),(0,[z1,z2,z3,z8,z5,z910]),(0,[z1,z2,z3,z911,z5,z6]),(0,[z157,z1,z342,z2,z3,z8])]],
   [[(0,[z1,z2,z912,z8,z5,z6]),(0,[z1,z2,z3,z8,z67,z200]),(0,[z1,z2,z913,z8,z5,z6])],[(0,[z1,z75,z3,z8,z314,z6]),(0,[z74,z75,z3,z284,z5,z6]),(0,[z1,z2,z914,z8,z5,z6]),(0,[z2,z3,z8,z5,z771,z6]),(1,[z270,z1,z127,z3,z8]),(0,[z1,z136,z232,z8,z5,z161])],[(0,[z1,z119,z3,z8,z5,z6]),(0,[z1,z915,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z916]),(0,[z1,z2,z3,z474,z4,z6]),(0,[z1,z2,z917,z8,z5,z6]),(0,[z280,z2,z819,z8,z5,z6]),(0,[z1,z2,z232,z8,z6,z325])],[(0,[z1,z2,z196,z8,z5,z6]),(0,[z1,z918,z3,z8,z5,z6]),(0,[z1,z2,z3,z919,z5,z6]),(0,[z1,z920,z3,z8,z5,z6]),(0,[z157,z1,z2,z3,z8,z407])]],
   [[(0,[z1,z2,z921,z8,z5,z6]),(0,[z2,z852,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z6,z922]),(0,[z1,z2,z923,z8,z5,z6])],[(0,[z1,z2,z924,z3,z8,z5]),(0,[z1,z2,z58,z8,z5,z419]),(0,[z1,z2,z184,z8,z314,z6])],[(0,[z1,z2,z3,z8,z5,z925]),(0,[z145,z2,z293,z8,z5,z6]),(0,[z352,z2,z293,z8,z5,z6]),(1,[z1,z896,z3,z5,z6]),(0,[z1,z2,z3,z8,z926,z6]),(0,[z1,z2,z3,z8,z200,z706]),(0,[z1,z2,z394,z8,z5,z6]),(0,[z1,z2,z3,z8,z199,z200])],[(0,[z1,z2,z927,z8,z5,z6]),(0,[z2,z184,z293,z8,z5,z6]),(0,[z74,z2,z3,z516,z5,z6]),(0,[z1,z2,z928,z8,z5,z6]),(0,[z1,z2,z929,z8,z5,z6]),(0,[z1,z2,z3,z8,z792,z6])]],
   [[(0,[z1,z75,z533,z8,z5,z6]),(0,[z1,z2,z930,z8,z5,z6]),(0,[z1,z3,z8,z41,z808,z6]),(0,[z1,z2,z931,z8,z5,z6]),(0,[z157,z1,z342,z3,z8,z5])],[(0,[z1,z2,z3,z8,z5,z6]),(0,[z1,z2,z932,z8,z5,z6]),(0,[z170,z2,z3,z8,z5,z6]),(0,[z1,z2,z184,z8,z421,z6]),(0,[z1,z2,z184,z8,z5,z130]),(0,[z1,z2,z933,z8,z5,z6]),(0,[z1,z365,z2,z8,z5,z6]),(0,[z157,z1,z2,z3,z8,z324]),(0,[z1,z2,z8,z5,z6,z934]),(1,[z1,z2,z3,z8,z793])],[(1,[z748,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z935,z6]),(0,[z147,z2,z3,z8,z5,z6]),(0,[z74,z2,z293,z73,z5,z6]),(0,[z1,z119,z3,z8,z314,z6]),(0,[z1,z2,z3,z8,z5,z771]),(0,[z1,z77,z8,z164,z5,z6]),(0,[z1,z2,z936,z8,z5,z6]),(0,[z1,z2,z8,z5,z937,z324]),(0,[z1,z136,z117,z3,z8,z5]),(0,[z308,z1,z2,z3,z8,z277])],[(0,[z1,z703,z3,z87,z5,z6]),(0,[z1,z2,z3,z938,z5,z6]),(0,[z1,z2,z939,z8,z5,z6]),(0,[z497,z2,z3,z8,z111,z6]),(0,[z1,z223,z2,z3,z5,z91]),(0,[z1,z940,z3,z8,z5,z6])]],
   [[(0,[z2,z748,z3,z8,z5,z6]),(0,[z280,z159,z3,z8,z5,z6]),(0,[z1,z2,z184,z73,z5,z6]),(0,[z1,z2,z8,z36,z86,z6]),(0,[z1,z896,z3,z8,z5,z6]),(0,[z79,z1,z144,z96,z5,z6]),(0,[z1,z941,z3,z8,z5,z6]),(0,[z942,z1,z2,z3,z5,z6])],[(0,[z1,z943,z2,z3,z8,z5]),(0,[z1,z3,z8,z5,z944,z6]),(0,[z1,z208,z2,z73,z5,z6]),(0,[z1,z75,z3,z8,z5,z222]),(0,[z267,z14,z2,z3,z28,z6]),(0,[z1,z945,z3,z8,z5,z6]),(0,[z270,z1,z365,z8,z50,z6]),(0,[z270,z1,z8,z560,z50,z6]),(0,[z1,z127,z3,z8,z41,z5]),(0,[z1,z102,z3,z8,z808,z6])],[(0,[z1,z119,z3,z8,z421,z6]),(0,[z1,z119,z3,z8,z5,z130]),(0,[z1,z2,z946,z8,z5,z324]),(0,[z1,z2,z58,z8,z5,z59]),(1,[z1,z2,z3,z5,z721])],[(0,[z1,z947,z2,z3,z8,z5]),(0,[z1,z2,z896,z3,z5,z6]),(0,[z1,z948,z3,z8,z5,z6]),(0,[z1,z2,z949,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z950]),(0,[z1,z951,z3,z8,z5,z6]),(0,[z191,z2,z3,z8,z5,z107]),(0,[z1,z952,z2,z3,z8,z6]),(0,[z1,z127,z2,z8,z5,z560])],[(0,[z64,z65,z588,z8,z5,z6]),(0,[z344,z159,z3,z8,z5,z6]),(0,[z1,z2,z852,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z953]),(0,[z1,z2,z3,z8,z314,z6]),(0,[z1,z119,z533,z8,z5,z6]),(0,[z1,z2,z184,z8,z5,z222]),(0,[z1,z23,z24,z8,z5,z6]),(0,[z1,z954,z2,z3,z8,z6]),(0,[z1,z2,z198,z8,z5,z6])],[(0,[z457,z2,z293,z8,z5,z6]),(0,[z1,z14,z2,z955,z5,z6]),(0,[z1,z80,z3,z87,z5,z6])],[(0,[z64,z748,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z956]),(0,[z1,z2,z568,z8,z36,z6]),(0,[z699,z2,z21,z8,z5,z6]),(0,[z1,z2,z957,z8,z5,z6]),(0,[z1,z144,z2,z8,z5,z6]),(0,[z1,z2,z238,z8,z5,z6]),(0,[z1,z342,z3,z8,z200,z6])]],
   [[(0,[z1,z958,z2,z3,z5,z6]),(0,[z1,z2,z8,z5,z959,z6]),(0,[z1,z2,z3,z8,z960,z6]),(0,[z2,z3,z8,z111,z751,z6]),(0,[z961,z2,z3,z8,z5,z6]),(0,[z1,z2,z962,z8,z5,z6]),(0,[z1,z2,z3,z8,z793,z277])],[(0,[z158,z159,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z421,z6]),(0,[z1,z2,z3,z8,z5,z130]),(0,[z1,z2,z772,z8,z5,z6]),(0,[z1,z2,z8,z5,z963,z6]),(0,[z1,z233,z3,z8,z5,z437]),(0,[z1,z2,z393,z8,z5,z6])],[(0,[z1,z2,z3,z964,z5,z6]),(0,[z1,z119,z3,z8,z5,z222]),(0,[z1,z2,z3,z8,z6,z965]),(0,[z1,z3,z8,z5,z42,z324])],[(0,[z1,z2,z3,z8,z5,z966]),(0,[z1,z208,z2,z3,z5,z6]),(0,[z1,z2,z967,z3,z5,z6]),(0,[z267,z2,z3,z8,z751,z6]),(0,[z1,z2,z8,z5,z6,z968]),(0,[z1,z969,z2,z3,z8,z5]),(0,[z970,z2,z3,z8,z5,z6]),(0,[z1,z3,z8,z5,z6,z220]),(0,[z1,z247,z853,z2,z5,z6])]],
   [[(0,[z1,z2,z533,z8,z5,z6]),(0,[z1,z2,z971,z8,z5,z6]),(0,[z1,z2,z3,z8,z199,z88]),(0,[z1,z972,z3,z8,z5,z6]),(1,[z157,z1,z342,z3,z8])],[(0,[z1,z2,z3,z8,z973,z6]),(0,[z1,z2,z974,z8,z5,z6]),(0,[z1,z2,z3,z8,z975,z6]),(0,[z1,z2,z3,z976,z8,z6]),(0,[z1,z2,z3,z8,z977,z6]),(0,[z1,z2,z3,z8,z5,z978]),(0,[z74,z2,z3,z284,z314,z6]),(0,[z1,z2,z3,z8,z5,z979]),(0,[z980,z2,z3,z8,z5,z6])],[(0,[z1,z2,z30,z73,z5,z6]),(0,[z1,z2,z3,z8,z5,z324]),(0,[z270,z1,z127,z3,z8,z50]),(0,[z92,z1,z247,z2,z5,z6]),(0,[z1,z12,z2,z8,z792,z6])],[(0,[z1,z2,z981,z3,z5,z6]),(0,[z1,z2,z982,z8,z5,z6]),(0,[z1,z2,z8,z5,z560,z49]),(0,[z92,z1,z2,z503,z5,z6]),(0,[z1,z2,z983,z8,z5,z6]),(0,[z1,z2,z8,z5,z984,z6])]],
   [[(0,[z1,z2,z3,z5,z6,z985]),(0,[z84,z2,z54,z8,z5,z107]),(0,[z1,z2,z8,z5,z723,z6]),(0,[z1,z142,z2,z198,z5,z91])],[(0,[z280,z65,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z222]),(0,[z74,z2,z3,z284,z421,z6]),(0,[z74,z2,z3,z284,z5,z130]),(0,[z1,z2,z3,z8,z6,z325]),(0,[z1,z986,z2,z8,z5,z6])],[(0,[z74,z2,z211,z8,z5,z6]),(0,[z79,z1,z275,z3,z5,z6]),(0,[z2,z3,z8,z751,z28,z6]),(0,[z987,z2,z3,z8,z5,z6]),(0,[z1,z2,z988,z8,z5,z6])],[(0,[z1,z12,z2,z8,z689,z6]),(0,[z1,z2,z989,z8,z5,z6]),(0,[z0,z1,z2,z238,z5,z6]),(0,[z1,z2,z3,z8,z5,z990]),(0,[z2,z3,z8,z991,z5,z6]),(0,[z1,z3,z8,z5,z6,z804]),(0,[z1,z342,z3,z8,z5,z42])]],
   [[(0,[z1,z2,z3,z992,z5,z6]),(0,[z201,z2,z852,z8,z5,z6]),(0,[z1,z2,z533,z8,z314,z6]),(0,[z1,z2,z3,z993,z5,z6]),(0,[z1,z136,z3,z8,z5,z324]),(0,[z1,z853,z2,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z723]),(0,[z1,z2,z3,z5,z721,z6])],[(0,[z1,z2,z994,z8,z5,z6]),(0,[z74,z2,z3,z715,z5,z6]),(0,[z1,z2,z995,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z996]),(0,[z1,z2,z997,z8,z5,z6])],[(0,[z1,z2,z3,z8,z5,z998]),(0,[z1,z2,z999,z8,z5,z6]),(0,[z1,z12,z2,z8,z237,z6]),(0,[z1,z2,z1000,z8,z5,z6]),(0,[z1,z2,z1001,z8,z5,z6])],[(0,[z0,z2,z3,z234,z5,z6]),(0,[z1,z342,z3,z8,z5,z324]),(0,[z1,z2,z3,z8,z5,z804])]],
   [[(0,[z145,z2,z852,z8,z5,z6]),(0,[z1,z2,z533,z8,z421,z6]),(0,[z1,z2,z533,z8,z5,z130]),(0,[z1,z2,z3,z8,z6,z1002]),(0,[z1,z2,z8,z5,z13,z15]),(0,[z270,z1,z3,z8,z49,z50]),(0,[z1,z3,z8,z5,z808,z6]),(0,[z1,z1003,z3,z8,z5,z6])],[(0,[z1,z397,z2,z8,z5,z13]),(0,[z280,z119,z3,z8,z5,z6]),(0,[z74,z2,z3,z284,z5,z222]),(0,[z1004,z2,z3,z8,z5,z6])],[(0,[z201,z208,z2,z3,z5,z6]),(0,[z1,z2,z487,z5,z13,z6]),(0,[z1,z2,z3,z8,z5,z1005]),(0,[z1,z2,z1006,z8,z5,z6]),(0,[z2,z3,z8,z5,z107,z771]),(0,[z1,z77,z83,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1007]),(1,[z308,z1,z136,z3,z8]),(0,[z1,z2,z3,z8,z5,z1008]),(0,[z1,z2,z35,z8,z792,z6]),(1,[z1,z2,z3,z805,z6]),(0,[z1,z2,z3,z805,z129,z6])],[(0,[z1,z2,z3,z8,z5,z1009]),(0,[z1,z23,z8,z5,z337,z6]),(0,[z280,z2,z923,z8,z5,z6]),(0,[z1,z1010,z2,z8,z5,z6]),(0,[z1,z8,z5,z6,z420,z220])]],
   [[(0,[z1,z2,z1011,z8,z5,z6]),(0,[z147,z2,z21,z8,z5,z6]),(0,[z1,z1012,z3,z8,z5,z6]),(0,[z270,z1,z3,z8,z50,z156]),(1,[z1,z2,z8,z792,z6]),(0,[z1,z342,z8,z5,z6,z420])],[(0,[z1,z2,z3,z8,z1013,z6]),(0,[z1,z136,z3,z8,z5,z804]),(0,[z92,z1,z347,z2,z5,z6])],[(0,[z1,z2,z8,z5,z1014,z6]),(0,[z1,z1015,z2,z3,z5,z6]),(0,[z1,z2,z1016,z8,z5,z6]),(0,[z1,z2,z3,z8,z1017,z6]),(0,[z1,z896,z3,z87,z5,z6]),(0,[z1,z853,z2,z93,z5,z6]),(0,[z1,z2,z3,z8,z200,z793])],[(0,[z2,z852,z293,z8,z5,z6]),(0,[z1,z2,z1018,z8,z5,z6]),(0,[z1,z2,z1019,z3,z5,z6]),(0,[z1,z2,z1020,z8,z5,z6])]],
   [[(0,[z1,z2,z3,z8,z5,z1021]),(0,[z280,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z5,z1022,z6]),(0,[z201,z2,z21,z487,z5,z6]),(0,[z1,z2,z533,z8,z5,z222]),(0,[z1,z1023,z3,z8,z5,z6]),(0,[z1,z14,z2,z3,z129,z6]),(0,[z1,z136,z3,z8,z675,z5])],[(0,[z1,z2,z1024,z8,z5,z6]),(0,[z1,z102,z3,z8,z41,z6]),(0,[z1,z2,z3,z187,z805,z6]),(0,[z1,z2,z60,z3,z5,z61])],[(0,[z1,z2,z3,z1025,z5,z6]),(0,[z1,z2,z3,z8,z5,z1026]),(0,[z1,z1027,z3,z8,z5,z6]),(0,[z1,z2,z1028,z8,z5,z6]),(0,[z1,z23,z34,z8,z5,z6]),(0,[z1,z23,z8,z5,z349,z6]),(0,[z1,z2,z1029,z8,z5,z6]),(0,[z1,z2,z1030,z8,z5,z6])],[(0,[z1,z2,z3,z1031,z5,z6]),(0,[z201,z208,z2,z21,z5,z6]),(0,[z1,z2,z3,z1032,z5,z6]),(0,[z1033,z2,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z49]),(0,[z1,z365,z2,z8,z5,z49]),(0,[z92,z1,z853,z2,z5,z6]),(0,[z1,z1034,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z805,z6]),(0,[z1,z2,z8,z5,z6,z1035])]],
   [[(0,[z1,z2,z174,z8,z5,z6]),(0,[z1,z2,z955,z8,z5,z6]),(0,[z84,z2,z196,z8,z5,z107]),(0,[z270,z157,z1,z136,z3,z8]),(0,[z1,z2,z3,z5,z805,z6])],[(0,[z147,z2,z293,z8,z5,z6]),(0,[z1,z1036,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z1037,z6]),(0,[z1,z2,z1038,z8,z5,z6]),(0,[z1,z2,z8,z5,z81,z6]),(0,[z1,z2,z58,z8,z5,z185])],[(0,[z1,z2,z1039,z8,z5,z6]),(0,[z1,z2,z1040,z8,z5,z6]),(0,[z1,z2,z1041,z3,z8,z5])],[(0,[z64,z65,z3,z8,z5,z6]),(0,[z1,z2,z3,z8,z5,z1042]),(0,[z1,z2,z8,z5,z1043,z6]),(0,[z2,z3,z8,z5,z6,z1044])]],
   [[(0,[z1,z2,z3,z8,z5,z1045]),(0,[z74,z543,z2,z3,z5,z6]),(0,[z1,z2,z3,z8,z5,z1046]),(0,[z79,z1,z896,z3,z5,z6]),(0,[z1047,z1,z2,z8,z5,z6])],[(0,[z208,z2,z3,z293,z5,z6]),(0,[z267,z2,z3,z8,z28,z6]),(0,[z280,z80,z3,z87,z5,z6]),(0,[z1,z563,z3,z8,z5,z42])],[(0,[z1,z1048,z3,z8,z5,z6]),(0,[z1,z1049,z2,z3,z8,z6]),(0,[z1,z1050,z3,z8,z5,z6]),(0,[z74,z547,z2,z3,z5,z6]),(0,[z84,z2,z3,z8,z5,z107]),(0,[z1,z2,z8,z5,z937,z6]),(0,[z1051,z2,z3,z8,z5,z6])],[(0,[z1,z2,z3,z1052,z5,z6]),(0,[z1,z2,z3,z8,z6,z1053]),(0,[z110,z2,z3,z8,z111,z6]),(0,[z1,z2,z8,z5,z6,z1054]),(0,[z1,z2,z113,z8,z5,z6]),(0,[z1,z2,z3,z8,z6,z793])]],
   [[(0,[z1,z2,z8,z5,z560,z6]),(1,[z1,z853,z2,z5,z6]),(0,[z1,z2,z58,z8,z5,z215])],[(0,[z1,z2,z8,z5,z1055,z6]),(0,[z1,z208,z2,z184,z5,z6]),(0,[z1,z119,z184,z8,z5,z6]),(0,[z1,z2,z1056,z8,z5,z6]),(0,[z1,z2,z1057,z8,z5,z6]),(0,[z1,z2,z8,z81,z6,z325]),(0,[z1,z2,z35,z8,z495,z6]),(0,[z1,z390,z2,z8,z5,z13])],[(0,[z1,z2,z1058,z8,z5,z6]),(0,[z1,z2,z1059,z8,z5,z6]),(0,[z1,z2,z218,z8,z5,z6]),(0,[z1,z2,z1060,z8,z5,z6]),(0,[z1,z2,z946,z8,z5,z6]),(0,[z1,z136,z3,z8,z325,z161])],[(0,[z64,z119,z3,z8,z5,z6]),(0,[z1,z2,z3,z1061,z5,z6]),(0,[z157,z1,z342,z3,z8,z277]),(0,[z157,z1,z2,z394,z8,z277])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 557) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 557).take 469) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1026)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [557, 469] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_nil pbend))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 90).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 90).take 38).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 128)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [90, 38] = true :=
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

end PEqualNP.Outside.L_meta_41362

theorem PEqualNP.Outside.L_meta_41362 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276809450 * 2 ^ 32 + 4240482432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276809450 * 2 ^ 32 + 4240482432) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_41362.solve